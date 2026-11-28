import Mathlib

/-!
# Primes p ∈ (n, 2n) with (-n/p) = -1

Source: https://mathoverflow.net/questions/332147 (Zhi-Wei Sun, CC BY-SA 4.0).

Conjecture (Sun, 2012), verified for `n ≤ 5 × 10⁸`:
(i) for any integer `n > 6` there is a prime `p ∈ (n, 2n)` with `(-n/p) = -1`;
(ii) for any integer `n > 5` there is a prime `p ∈ (n, 2n)` with `(2n/p) = 1`.
`(a/p)` is the Legendre symbol; for an odd prime `p` (here `p > n > 5`) it is `jacobiSym a p`.
`main` states both parts, in order, as a conjunction.
-/

namespace OMA.S_mo_332147

theorem main :
    (∀ n : ℕ, 6 < n → ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2 * n ∧ jacobiSym (-(n : ℤ)) p = -1) ∧
    (∀ n : ℕ, 5 < n → ∃ p : ℕ, p.Prime ∧ n < p ∧ p < 2 * n ∧ jacobiSym (2 * (n : ℤ)) p = 1) := by
  sorry

end OMA.S_mo_332147
