import Mathlib

/-!
# New Mersenne conjecture

Source: https://en.wikipedia.org/wiki/New_Mersenne_conjecture
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: for any odd natural number `p`, if any two of the following three conditions are true,
then the third one is also true:

1. `p = 2 ^ k + 1` or `p = 2 ^ k - 1` or `p = 4 ^ k + 3` or `p = 4 ^ k - 3` for some `k`;
2. `2 ^ p - 1` is prime;
3. `(2 ^ p + 1) / 3` is prime.

So the proposition formalized below is: for every odd `p`, each pair of the three conditions
implies the third, where being of the form `2 ^ k - 1` is written as `p + 1 = 2 ^ k` and being of
the form `4 ^ k - 3` is written as `p + 3 = 4 ^ k` to avoid truncated subtraction.
-/

namespace OMA.S_wp_new_mersenne_conjecture

-- definitions the statement needs (no sorry, no axiom)

/-- The first condition: `p` is of the form `2 ^ k + 1`, `2 ^ k - 1`, `4 ^ k + 3` or `4 ^ k - 3`. -/
def OfMersenneLikeForm (p : ℕ) : Prop :=
  ∃ k : ℕ, p = 2 ^ k + 1 ∨ p + 1 = 2 ^ k ∨ p = 4 ^ k + 3 ∨ p + 3 = 4 ^ k

/-- The second condition: `2 ^ p - 1` is prime. -/
def MersennePrimality (p : ℕ) : Prop :=
  (2 ^ p - 1).Prime

/-- The third condition: `(2 ^ p + 1) / 3` is prime. -/
def FermatQuotientPrimality (p : ℕ) : Prop :=
  ((2 ^ p + 1) / 3).Prime

/-- The new Mersenne conjecture. -/
theorem main : ∀ p : ℕ, Odd p →
    (OfMersenneLikeForm p ∧ MersennePrimality p → FermatQuotientPrimality p) ∧
      (OfMersenneLikeForm p ∧ FermatQuotientPrimality p → MersennePrimality p) ∧
        (MersennePrimality p ∧ FermatQuotientPrimality p → OfMersenneLikeForm p) := by
  sorry

end OMA.S_wp_new_mersenne_conjecture
