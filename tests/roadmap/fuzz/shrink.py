"""Deterministic delta-debugging shrinkers shared by the Q01 fuzzers.

`ddmin` is Zeller's 1-minimal list reduction. `shrink_json` reduces a JSON tree and
`shrink_bytes` a raw (possibly non-JSON) byte string. Every accepted candidate is strictly
smaller under `json_size`/byte length, so each shrinker terminates. The predicate receives a
candidate and returns True when the failure of interest still reproduces.
"""
import copy
import json
import re


def ddmin(items, still_fails):
    """Return a 1-minimal sublist of `items` (order kept) for which `still_fails` holds.

    Precondition: `still_fails(items)` is True. 1-minimal: removing any single remaining
    element makes the predicate False.
    """
    items = list(items)
    granularity = 2
    while len(items) >= 2:
        chunk = -(-len(items) // granularity)
        subsets = [items[i:i + chunk] for i in range(0, len(items), chunk)]
        reduced = False
        for k in range(len(subsets)):
            complement = [x for j, s in enumerate(subsets) if j != k for x in s]
            if still_fails(complement):
                items = complement
                granularity = max(granularity - 1, 2)
                reduced = True
                break
        if not reduced:
            for subset in subsets:
                if len(subset) < len(items) and still_fails(subset):
                    items, granularity, reduced = subset, 2, True
                    break
        if not reduced:
            if granularity >= len(items):
                break
            granularity = min(len(items), granularity * 2)
    if len(items) == 1 and still_fails([]):
        return []
    return items


def json_size(value):
    """Total order used for strict shrinking: serialized length, then text."""
    text = json.dumps(value, sort_keys=True, ensure_ascii=False)
    return (len(text), text)


def get_path(value, path):
    for key in path:
        value = value[key]
    return value


def with_path(value, path, new):
    """A deep copy of `value` with the node at `path` replaced by `new`."""
    if not path:
        return new
    result = copy.deepcopy(value)
    get_path(result, path[:-1])[path[-1]] = new
    return result


def nodes(value, path=()):
    """Every (path, node) of a JSON-shaped tree, preorder."""
    yield path, value
    if isinstance(value, dict):
        for key, child in value.items():
            yield from nodes(child, path + (key,))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from nodes(child, path + (index,))


def _simpler(node):
    """Replacement candidates for one node, simplest first."""
    out = [None, 0, False, "", [], {}]
    if isinstance(node, (dict, list)):
        children = list(node.values()) if isinstance(node, dict) else list(node)
        out.extend(children)  # hoist a child over its parent
    elif isinstance(node, bool):
        pass
    elif isinstance(node, int):
        out.extend([1, -1, node // 2, node - 1 if node > 0 else node + 1])
    elif isinstance(node, float):
        out.extend([0.0, int(node) if abs(node) < 1e18 else 1])
    elif isinstance(node, str):
        out.extend([node[:len(node) // 2], node[1:], node[:-1]])
    return out


def shrink_json(value, still_fails, budget=20000):
    """Greedy fixpoint over child deletion (ddmin) and node replacement."""
    calls = [0]

    def test(candidate):
        if calls[0] >= budget:
            return False
        calls[0] += 1
        return still_fails(candidate)

    current = value
    changed = True
    while changed:
        changed = False
        for path, _ in list(nodes(current)):
            try:
                node = get_path(current, path)
            except (KeyError, IndexError, TypeError):
                continue
            if isinstance(node, (dict, list)) and len(node) > 0:
                if isinstance(node, dict):
                    keys = list(node)
                    def rebuild(sub, node=node):
                        return {k: node[k] for k in sub}
                else:
                    keys = list(range(len(node)))
                    def rebuild(sub, node=node):
                        return [node[k] for k in sub]
                kept = ddmin(keys, lambda sub: test(with_path(current, path, rebuild(sub))))
                if len(kept) < len(keys):
                    current = with_path(current, path, rebuild(kept))
                    changed = True
                    break
            for candidate in _simpler(node):
                if json_size(candidate) >= json_size(node):
                    continue
                trial = with_path(current, path, candidate)
                if test(trial):
                    current = trial
                    changed = True
                    break
            if changed:
                break
    return current


_TOKEN = re.compile(rb'"(?:[^"\\]|\\.)*"?|-?[0-9][0-9.eE+-]*|[A-Za-z_]+|\s+|.', re.S)


def shrink_bytes(data, still_fails, budget=20000):
    """ddmin over JSON-ish tokens, then over single bytes."""
    calls = [0]

    def test(candidate):
        if calls[0] >= budget:
            return False
        calls[0] += 1
        return still_fails(candidate)

    tokens = _TOKEN.findall(data) or [data]
    tokens = ddmin(tokens, lambda sub: test(b"".join(sub)))
    data = b"".join(tokens)
    chars = [data[i:i + 1] for i in range(len(data))]
    return b"".join(ddmin(chars, lambda sub: test(b"".join(sub))))
