#!/usr/bin/env python3
"""Root/CI driver for a built translator; no compiler, native code or build invoked."""
import argparse
import copy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
CURRENT = json.loads((HERE.parent/'profiles/current.json').read_text())
PREFIX = b'-- air2lean-profile: '


def constant(name, value):
    doc = copy.deepcopy(CURRENT)
    doc['name'] = name
    doc['body'][0]['args'][0]['val'] = str(value)
    return doc


def cases():
    independent = [constant(name, i+1) for i,name in enumerate(
        ('order.a', 'order.a.a', 'order.generic(u8).left', 'order.z'))]
    # The root encounters 9 before 10: they become anon_1 and anon_2. Historical
    # raw filename order is 10 before 9, which emission must preserve after renaming.
    reached = [constant('order.generic__anon_9', 9), constant('order.generic__anon_10', 10)]
    root = constant('order.root', 0)
    root['types'].append(dict(k='other', name='fn () u8'))
    root['body'] = [dict(id=i, tag='call', ty=0,
                         callee=dict(ty=2, func=f'order.generic__anon_{n}', noreturn=False), args=[])
                    for i,n in enumerate((9,10))]
    root['body'].append(dict(id=2, tag='ret', ty=1, args=[dict(inst=1)]))
    reached.append(root)
    unreached = [constant(f'order.unused__anon_{n}', n) for n in (9,10)]
    return dict(independent=independent, reached=reached, unreached=unreached)


def storage_name(doc, index, storage):
    if storage == 'direct':
        return doc['name']+'.json'
    if storage == 'hash':
        return '~air2lean-sha256-'+hashlib.sha256(doc['name'].encode()).hexdigest()+'.json'
    # Constructor order deliberately differs from the historical virtual identity order.
    return f'{index:03d}.json'


def invoke(binary, air, output):
    return subprocess.run([str(binary), str(air), '-o', str(output), '--namespace', 'Order',
                           '--prefix', 'order.', '--profile', 'abi64-le-v1'],
                          capture_output=True, timeout=10, check=False)


def check(binary):
    with tempfile.TemporaryDirectory(prefix='air2lean-order-') as temporary:
        directory = Path(temporary)
        for case,docs in cases().items():
            outputs = []
            for storage in ('direct','hash','numeric'):
                air = directory/f'{case}-{storage}'
                air.mkdir()
                for index,doc in enumerate(docs):
                    (air/storage_name(doc,index,storage)).write_text(json.dumps(doc))
                output = directory/f'{case}-{storage}.lean'
                output.write_bytes(b'KEEP\n')
                result = invoke(binary,air,output)
                assert result.returncode == 0, (case,storage,result.returncode,result.stderr)
                generated = output.read_bytes()
                header,body = generated.split(b'\n',1)
                assert header.startswith(PREFIX), (case,storage,'missing mandatory profile header')
                metadata = json.loads(header[len(PREFIX):])
                assert metadata['profile']['name'] == 'abi64-le-v1'
                assert metadata['correspondence'] == 'model'
                outputs.append(generated)
                if case == 'independent':
                    assert body.index(b'def a_a ') < body.index(b'def a '), 'virtual .json suffix order lost'
                if case == 'reached':
                    assert body.index(b'def generic__anon_2 ') < body.index(b'def generic__anon_1 '), 'raw instance ordering lost'
                    first = body.split(b'def generic__anon_1 ',1)[1].split(b'\n\n',1)[0]
                    second = body.split(b'def generic__anon_2 ',1)[1].split(b'\n\n',1)[0]
                    assert b'pure (.ret (9 : BitVec 8))' in first, 'first reached instance changed identity'
                    assert b'pure (.ret (10 : BitVec 8))' in second, 'second reached instance changed identity'
            assert outputs[0] == outputs[1] == outputs[2], case+' output depends on storage filenames'
        # The first path error remains first even if its JSON identity sorts last.
        air = directory/'reject'
        air.mkdir()
        for filename,name,schema in (('0.json','order.z',13),('1.json','order.a',14)):
            doc = constant(name,1);doc['schema'] = schema
            (air/filename).write_text(json.dumps(doc))
        output = directory/'reject.lean';output.write_bytes(b'KEEP\n')
        result = invoke(binary,air,output)
        assert result.returncode == 1, result.stderr
        assert b'0.json' in result.stderr and b'1.json' not in result.stderr, result.stderr
        assert b'unsupported AIR schema 13' in result.stderr, result.stderr
        assert output.read_bytes() == b'KEEP\n', 'rejection overwrote previous output'
    print('emission order CLI passed: 9 positive invocations, 1 preserved first-error rejection')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('translator', type=Path)
    args = parser.parse_args()
    check(args.translator.resolve(strict=True))


if __name__ == '__main__':
    main()
