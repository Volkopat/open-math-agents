import Mathlib

/-!
# OEIS A316584: T(p,p) = p^2 for every prime p

Source: https://oeis.org/A316584 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Andrew Howroyd, Jul 07 2018), offset 1: Array read by antidiagonals: T(n,k) is the number
of elements x in GL(2,Z_n) with x^k == I mod n where I is the identity matrix.
Formula line: Conjecture: T(p,p) = p^2 for p prime.

Formalization notes:
* GL(2,Z_n) is Mathlib's `GL (Fin 2) (ZMod n)`, the group of invertible 2 x 2 matrices over
  `ZMod n`; x^k == I mod n is the equation x ^ k = 1 in that group. `T n k` counts such x with
  `Nat.card` (the type is finite for n >= 1, which is the range of the array).
* The entry's table gives T(2,2) = 4, T(3,3) = 9, T(5,5) = 25 and T(7,7) = 49, all instances of
  `main`.
-/

namespace OMA.S_oeis_a316584

/-- T(n,k): the number of x in GL(2, Z_n) with x^k = I. -/
noncomputable def T (n k : ℕ) : ℕ := Nat.card {x : GL (Fin 2) (ZMod n) // x ^ k = 1}

/-- Howroyd's conjecture: T(p,p) = p^2 for every prime p. -/
theorem main : ∀ p : ℕ, p.Prime → T p p = p ^ 2 := by
  sorry

end OMA.S_oeis_a316584
