import Mathlib

/-!
# A223732: Positive numbers that are the sum of three nonzero squares with no common factor > 1 in exactly one way.

Source: https://oeis.org/A223732
Credit: @EtienneLefranc

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a223732

/-- Ways to write `n` as a sum of three nonzero squares with no common factor > 1,
counted as unordered triples `x ≤ y ≤ z`. -/
def reps (n : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {t | 0 < t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
    t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = n ∧ Nat.gcd t.1 (Nat.gcd t.2.1 t.2.2) = 1}

/-- `n` is a term of A223732: a positive number that is the sum of three nonzero squares
with no common factor > 1 in exactly one way. -/
def IsTerm (n : ℕ) : Prop := 0 < n ∧ (reps n).encard = 1

/-- Conjecture (Alois P. Heinz): 793 = 6^2 + 9^2 + 26^2 is the largest element of this sequence. -/

theorem main : IsTerm 793 ∧ ∀ n : ℕ, IsTerm n → n ≤ 793 := by
  sorry

end OMA.S_oeis_a223732

