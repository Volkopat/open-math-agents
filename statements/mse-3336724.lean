import Mathlib

/-!
# Are there any $3$-Fermat-pseudoprimes of the form $k^4+1$?

Source: https://math.stackexchange.com/questions/3336724/are-there-any-3-fermat-pseudoprimes-of-the-form-k41
Credit: @luciusacarr

The source: suppose `k` is a positive integer and `N := k ^ 4 + 1` is composite; can the
congruence `3 ^ (N - 1) ≡ 1 (mod N)` hold? The question is stated as the existence claim; a
negative answer is a proof of its negation.

Here `N - 1 = k ^ 4`, so no truncated subtraction is involved. For `k > 0` we have `N ≥ 2`, so
`N` is composite exactly when it is not prime. The source reports no example for `k ≤ 10 ^ 8`.
-/

namespace OMA.S_mse_3336724

theorem main : ∃ k : ℕ, 0 < k ∧ ¬ (k ^ 4 + 1).Prime ∧ 3 ^ (k ^ 4) ≡ 1 [MOD k ^ 4 + 1] := by
  sorry

end OMA.S_mse_3336724
