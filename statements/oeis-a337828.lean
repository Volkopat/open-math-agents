import Mathlib

/-!
# Base-three divisibility at half of k−1

Source: https://oeis.org/A337828

Max Alekseyev (July 26, 2026) conjectures a characterization of the odd
indices in A337828. Its auxiliary sequence A015949 consists of positive
integers m dividing 3^m+1. The entry starts at k=5.
-/

namespace OMA.S_oeis_a337828

/-- The defining divisibility of the sequence, for odd integers at least three. -/
def IsTerm (k : ℕ) : Prop :=
  3 ≤ k ∧ Odd k ∧ k*((k-1)/2) ∣ 3^((k-1)/2)+1

/-- A015949 membership, with its positive offset. -/
def HalfCondition (k : ℕ) : Prop :=
  0 < (k-1)/2 ∧ (k-1)/2 ∣ 3^((k-1)/2)+1

theorem main : ∀ k : ℕ, IsTerm k ↔ k.Prime ∧ k%3=2 ∧ HalfCondition k := by
  sorry

end OMA.S_oeis_a337828
