import Mathlib

/-!
# Between consecutive squares there are numbers of the forms p, 2p, 3p and 4p

Source: https://math.stackexchange.com/questions/4373284

Conjecture: for all `n > 1`, the open interval `(n², (n + 1)²)` contains, for each of
`j = 1, 2, 3, 4`, at least one integer of the form `j p` with `p` prime. (The case `j = 4` is
equivalent to Oppermann's conjecture.) It has been checked for `n ≤ 10^8`.

Formalization notes:
* `main` states the conjecture as posed (the question asks for a counterexample). The later
  generalization in the question's update, to `n^a < k p < (n + 1)^a` for `1 ≤ k ≤ (3^a - 1)/2`,
  is not formalized here.
-/

namespace OMA.S_mse_4373284

/-- For `n > 1` and `j ∈ {1, 2, 3, 4}` there is a prime `p` with `n² < j p < (n + 1)²`. -/
theorem main : ∀ n : ℕ, 1 < n → ∀ j : ℕ, 1 ≤ j → j ≤ 4 →
    ∃ p : ℕ, p.Prime ∧ n ^ 2 < j * p ∧ j * p < (n + 1) ^ 2 := by
  sorry

end OMA.S_mse_4373284
