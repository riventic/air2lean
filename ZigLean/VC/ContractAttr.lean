import Lean.LabelAttribute

/-- Proved modular contracts that automatic VC extraction may use for a call.
A `Result` contract has the shape `∀ xs, pre → ∃ v, f xs = pure v ∧ post v` (`pre →` may be
omitted); a memory contract has the shape `∀ xs, Triple pre (f xs) post` or `∀ xs, TotalTriple pre (f xs) post`
(a total one also serves total and result-existence goals). -/
register_label_attr vc_contract
