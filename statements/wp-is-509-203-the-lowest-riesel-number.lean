import Mathlib

/-!
# Is 509,203 the lowest Riesel number?

Source: https://en.wikipedia.org/wiki/Riesel_number
Credit: @ihateSAS

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: a **Riesel number** is an odd natural number `k` such that `k * 2 ^ n - 1` is composite
for every `n ≥ 1` (that is, the sequence contains no primes).  It is conjectured that `509203` is
the smallest Riesel number; the open question, from "List of unsolved problems in mathematics", is
"Is 509,203 the lowest Riesel number?".

So the proposition formalized below is the conjunction: `509203` is a Riesel number, and no smaller
natural number is one.
-/

namespace OMA.S_wp_is_509_203_the_lowest_riesel_number

-- definitions the statement needs (no sorry, no axiom)

/-- `k` is a **Riesel number**: `k` is odd and `k * 2 ^ n - 1` is not prime for any `n ≥ 1`. -/
def IsRieselNumber (k : ℕ) : Prop :=
  Odd k ∧ ∀ n : ℕ, 1 ≤ n → ¬ (k * 2 ^ n - 1).Prime

/-- Is 509,203 the lowest Riesel number? -/
theorem main : IsRieselNumber 509203 ∧ ∀ k : ℕ, k < 509203 → ¬ IsRieselNumber k := by
  sorry

end OMA.S_wp_is_509_203_the_lowest_riesel_number
