import Mathlib

/-!
# A Fermat test for numbers of the form `3 * 2 ^ k + 1`

Source: https://math.stackexchange.com/questions/4887134
Credit: @jagraj28

The question asks: let `k ≥ 1` be an integer and `N = 3 * 2 ^ k + 1`. Is `N` prime if and only if
`2 ^ (N - 1) ≡ 1 (mod N)`?

The direction "prime implies the congruence" is Fermat's little theorem (`N` is odd, so `2` is a unit
mod `N`). The open direction asks whether no `N` of this form is a base-2 Fermat pseudoprime. The
asker checked `k ≤ 15000`; a comment extends the search to `k = 20909`. The question has no answer.

Conventions.
* `k` ranges over the natural numbers with `1 ≤ k`, as in the question.
* `N - 1` is written as `3 * 2 ^ k` to avoid natural-number subtraction.
* The congruence is `Nat.ModEq` on natural numbers, the same as the congruence of integers here
  because both sides are nonnegative.
-/

namespace OMA.S_mse_4887134

/-- For every `k ≥ 1`, `N = 3 * 2 ^ k + 1` is prime if and only if `2 ^ (N - 1) ≡ 1 (mod N)`. -/
theorem main : ∀ k : ℕ, 1 ≤ k →
    ((3 * 2 ^ k + 1).Prime ↔ 2 ^ (3 * 2 ^ k) ≡ 1 [MOD 3 * 2 ^ k + 1]) := by
  sorry

end OMA.S_mse_4887134
