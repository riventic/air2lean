import Lean.LabelAttribute

/-- Proved modular contracts that automatic VC extraction may use for a call.
A `Result` contract has the shape `∀ xs, pre → ∃ v, f xs = pure v ∧ post v` (`pre →` may be
omitted); a memory contract has the shape `∀ xs, FTotalTriple pre (f xs) post` (or `FTriple`):
`vc_gen` gives it to the walk of `fsym` as a step rule. -/
register_label_attr vc_contract
