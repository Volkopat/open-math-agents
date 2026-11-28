import Mathlib

/-!
# OEIS A005133: index-`n` subgroups of the modular group, parity conjectures

Source: https://oeis.org/A005133
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the number of subgroups of index `n` of the modular group `PSL₂(ℤ)`. Conjectures
(Grady, reported in the entry): (I) if `n` is odd then `a(n)` and `a(2n)` have the same parity;
(II) `a(4n)` is even.

Conventions:
* `PSL₂(ℤ) = SL₂(ℤ) / {±1}`, the quotient of `Matrix.SpecialLinearGroup (Fin 2) ℤ` by its center.
  `PSL₂(ℤ)` is finitely generated, so it has finitely many subgroups of each finite index and
  `Nat.card` below is a genuine count.
* `n ≥ 1` in both parts.
-/

namespace OMA.S_oeis_a005133

/-- The modular group `PSL₂(ℤ)`. -/
abbrev PSL2Z := Matrix.SpecialLinearGroup (Fin 2) ℤ ⧸ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) ℤ)

/-- Number of subgroups of index `n` of `PSL₂(ℤ)`. -/
noncomputable def a (n : ℕ) : ℕ := Nat.card {H : Subgroup PSL2Z // H.index = n}

/-- Grady's conjectures (I) and (II). -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → Odd n → (a n % 2 = a (2 * n) % 2)) ∧
    (∀ n : ℕ, 1 ≤ n → Even (a (4 * n))) := by
  sorry

end OMA.S_oeis_a005133
