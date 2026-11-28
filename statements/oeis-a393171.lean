import Mathlib

/-!
# OEIS A393171

The generating function `A` has constant coefficient zero and satisfies
`A(X) = X + A(C(X))²`, where `C(X) = X + C(X)²` is the shifted Catalan
series. The conjecture specifies the residue of each coefficient above degree
`2` modulo `8`.

Source: https://oeis.org/A393171
Credit: @wtho704
-/

namespace OMA.S_oeis_a393171

open PowerSeries

/-- The Catalan series with constant coefficient zero and linear coefficient one. -/
noncomputable def catalanGF : PowerSeries ℤ :=
  X * map (Nat.castRingHom ℤ) catalanSeries

/-- Indices where the conjecture predicts residue `4`. -/
def specialIndex (n : ℕ) : Prop :=
  ∃ k : ℕ, 1 ≤ k ∧ (n = 2 ^ k ∨ n = 2 ^ k + 1)

theorem main : ∀ A : PowerSeries ℤ, constantCoeff A = 0 →
    A = X + (A.subst catalanGF) ^ 2 → ∀ n : ℕ, 2 < n →
      ((coeff n A ≡ 4 [ZMOD 8]) ↔ specialIndex n) ∧
        (¬ specialIndex n → (8 : ℤ) ∣ coeff n A) := by
  sorry

end OMA.S_oeis_a393171
