import Mathlib

/-!
# OEIS A006694 (cyclotomic cosets of 2 mod 2n+1): `a((3^n - 1)/2) = n`

Source: https://oeis.org/A006694
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Shevelev, in the entry; noted there as correct): `a((3^n - 1)/2) = n`, where `a(m)`
is the number of cyclotomic cosets of 2 modulo `2m + 1`, minus one (the entry's offset
convention: the coset `{0}` is not counted, so that `a(0) = 0` and `a(1) = 1`).

Encoding: cosets are the orbits of `x ↦ 2x` on `ZMod (2m + 1)`; `a(m)` is the number of orbits
on the nonzero residues. For `2m + 1 = 3ⁿ` the statement is `a = n`, `n ≥ 0`.
-/

namespace OMA.S_oeis_a006694

/-- `x` and `y` lie in the same cyclotomic coset of 2 modulo `N`. -/
def SameCoset (N : ℕ) (x y : ZMod N) : Prop := ∃ k : ℕ, y = 2 ^ k * x

/-- Number of cyclotomic cosets of 2 on the nonzero residues modulo `2m + 1`. -/
noncomputable def a (m : ℕ) : ℕ :=
  Nat.card (Quot (fun x y : {x : ZMod (2 * m + 1) // x ≠ 0} => SameCoset (2 * m + 1) x.1 y.1))

/-- Shevelev's formula. -/
theorem main : ∀ n : ℕ, a ((3 ^ n - 1) / 2) = n := by
  sorry

end OMA.S_oeis_a006694
