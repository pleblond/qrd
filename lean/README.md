# QR

Lean 4 formalization of the closed-form ledger in `paper/`.

The library target is `QR`. `QR/Ledger.lean` records which identities are theorems,
which analytic facts are named interfaces, and which items stay in the manuscript's
open class C4. Postulates are not introduced as extra axioms: each proved statement
is an identity in the algebraic structure the manuscript already uses.

Build with `lake build`.
