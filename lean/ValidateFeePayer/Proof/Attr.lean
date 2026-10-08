import Lean

/-- The instruction at each address of the carved code (`DecodeTable.lean`). -/
register_simp_attr decode_table

/-- What a symbolic step unfolds: the machine semantics and the register-file lemmas. -/
register_simp_attr vexec
