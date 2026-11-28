import Mathlib

/-!
# A conjecture by Euler about `8n + 3`

Source: https://mathoverflow.net/questions/135608/a-conjecture-by-euler-about-8n3
Credit: @shc261392

Euler's conjecture. For any positive integer `n`, `8n + 3` can be represented as a sum
`8n + 3 = (2k - 1)^2 + 2p`, where `k` is a positive integer and `p` is a prime.
(Mazur, 2012, describes it as still unsettled.)
-/

namespace OMA.S_mo_135608

theorem main :
    ∀ n : ℕ, 0 < n → ∃ k p : ℕ, 0 < k ∧ p.Prime ∧ 8 * n + 3 = (2 * k - 1) ^ 2 + 2 * p := by
  sorry

end OMA.S_mo_135608
