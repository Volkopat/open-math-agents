import Mathlib

/-!
# OEIS A023503: greatest prime divisor of p - 1

Source: https://oeis.org/A023503
`a n` is the greatest prime divisor of `prime(n) - 1` (2, 2, 3, 5, 3, 2, …). The entry
records two conjectures:
1. every prime occurs in the sequence;
2. `liminf a(n) = 3`.
`main` is their conjunction.

Conventions. `IsGpf q m` says that `q` is the greatest prime factor of `m`. Over the primes
`p ≥ 3` (for `p = 2`, `p - 1 = 1`), `liminf a(n) = 3` means: only finitely many primes `p`
have greatest prime factor of `p - 1` equal to `2`, and infinitely many have it equal to `3`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a023503

/-- `q` is the greatest prime factor of `m`. -/
def IsGpf (q m : ℕ) : Prop := q.Prime ∧ q ∣ m ∧ ∀ r : ℕ, r.Prime → r ∣ m → r ≤ q

theorem main :
    (∀ q : ℕ, q.Prime → ∃ p : ℕ, p.Prime ∧ IsGpf q (p - 1)) ∧
    ({p : ℕ | p.Prime ∧ 3 ≤ p ∧ IsGpf 2 (p - 1)}.Finite ∧
      {p : ℕ | p.Prime ∧ IsGpf 3 (p - 1)}.Infinite) := by
  sorry

end OMA.S_oeis_a023503
