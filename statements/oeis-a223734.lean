import Mathlib

/-!
# A223734: Positive numbers that are the sum of three nonzero squares with no common factor > 1 in exactly three ways.

Source: https://oeis.org/A223734
Credit: @EtienneLefranc

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a223734

/-- Ways to write `n` as a sum of three nonzero squares with no common factor > 1,
counted as unordered triples `x ≤ y ≤ z`. -/
def reps (n : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {t | 0 < t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
    t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = n ∧ Nat.gcd t.1 (Nat.gcd t.2.1 t.2.2) = 1}

/-- `n` is a term of A223734: a positive number that is the sum of three nonzero squares
with no common factor > 1 in exactly three ways. -/
def IsTerm (n : ℕ) : Prop := 0 < n ∧ (reps n).encard = 3

/-- Conjecture (Alois P. Heinz): a(185) = 4075 = 31^2 + 33^2 + 45^2 = 23^2 + 39^2 + 45^2 = 5^2 + 9^2 + 63^2 is the largest element
of this sequence. Here `a(185) = 4075` means `4075` is a term and exactly 185 terms are `≤ 4075`. -/

theorem main :
    IsTerm 4075 ∧ {n : ℕ | n ≤ 4075 ∧ IsTerm n}.ncard = 185 ∧
      ∀ n : ℕ, IsTerm n → n ≤ 4075 := by
  sorry

end OMA.S_oeis_a223734

