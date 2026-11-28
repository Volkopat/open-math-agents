import Mathlib

/-!
# A223733: Positive numbers that are the sum of three nonzero squares with no common factor > 1 in exactly two ways.

Source: https://oeis.org/A223733
Credit: @EtienneLefranc

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a223733

/-- Ways to write `n` as a sum of three nonzero squares with no common factor > 1,
counted as unordered triples `x ≤ y ≤ z`. -/
def reps (n : ℕ) : Set (ℕ × ℕ × ℕ) :=
  {t | 0 < t.1 ∧ t.1 ≤ t.2.1 ∧ t.2.1 ≤ t.2.2 ∧
    t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = n ∧ Nat.gcd t.1 (Nat.gcd t.2.1 t.2.2) = 1}

/-- `n` is a term of A223733: a positive number that is the sum of three nonzero squares
with no common factor > 1 in exactly two ways. -/
def IsTerm (n : ℕ) : Prop := 0 < n ∧ (reps n).encard = 2

/-- Conjecture (Alois P. Heinz): a(147) = 1885 = 16^2 + 27^2 + 30^2 = 12^2 + 29^2 + 30^2 is the largest element
of this sequence. Here `a(147) = 1885` means `1885` is a term and exactly 147 terms are `≤ 1885`. -/

theorem main :
    IsTerm 1885 ∧ {n : ℕ | n ≤ 1885 ∧ IsTerm n}.ncard = 147 ∧
      ∀ n : ℕ, IsTerm n → n ≤ 1885 := by
  sorry

end OMA.S_oeis_a223733

