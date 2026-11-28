import Mathlib

/-!
# Primes and the factorial

Source: https://mathoverflow.net/questions/243771
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjectures (MathOverflow): (1) for all primes `p > 5` there is a prime `q < p` with
`q ≡ m! (mod p)` for some `m` with `2 < m < p`; (2) for all primes `p` there is a prime
`q < p²` with `q ≡ m! (mod p²)` for some `m` with `2 < m < p²`.

Conventions:
* `main` states both conjectures as stated in the question (the second with the range
  `2 < m < p²`; the stronger range `2 < m < p` mentioned in a comment is not part of it).
* In (2), `p` ranges over all primes; for `p = 2` the range `2 < m < 4` gives `m = 3`.
-/

namespace OMA.S_mo_243771

theorem main :
    (∀ p : ℕ, p.Prime → 5 < p → ∃ q m : ℕ, q.Prime ∧ q < p ∧ 2 < m ∧ m < p ∧
      q ≡ m.factorial [MOD p]) ∧
    (∀ p : ℕ, p.Prime → ∃ q m : ℕ, q.Prime ∧ q < p ^ 2 ∧ 2 < m ∧ m < p ^ 2 ∧
      q ≡ m.factorial [MOD p ^ 2]) := by
  sorry

end OMA.S_mo_243771
