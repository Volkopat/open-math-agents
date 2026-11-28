import Mathlib

/-!
# A282539: Greedy sequence where a(n)*a(n-1) - 1 and a(n)*a(n-1) + 1 are twin primes

Source: https://oeis.org/A282539

Conjecture (OEIS A282539):
The greedy sequence starting with `a(1) = 1`, where `a(n)` is the smallest positive
integer not previously occurring such that `a(n) * a(n - 1) - 1` and
`a(n) * a(n - 1) + 1` are twin primes, is defined for all `n ≥ 1`.

Conventions:
- OEIS offset is `1`; here we index from `0` (`a 0 = 1`, `a 1 = 4`, `a 2 = 3`,
  `a 3 = 2`, `a 4 = 6`, `a 5 = 5`, `a 6 = 12`, `a 7 = 9`, `a 8 = 8`, `a 9 = 24`, ...).
- Existence of `a : ℕ → ℕ` satisfying `a 0 = 1` and `IsLeast ... (a (n + 1))` for every
  `n : ℕ` captures both well-definedness at every step and the unique greedy choice.
-/

namespace OMA.S_oeis_a282539

/-- Conjecture: the greedy twin-prime product sequence A282539 extends infinitely
(i.e., `a(n)` exists for every `n`). -/
theorem main :
    ∃ a : ℕ → ℕ, a 0 = 1 ∧
      ∀ n : ℕ, IsLeast
        {k : ℕ | 1 ≤ k ∧ (∀ i ≤ n, a i ≠ k) ∧
          Nat.Prime (k * a n - 1) ∧ Nat.Prime (k * a n + 1)}
        (a (n + 1)) := by
  sorry

end OMA.S_oeis_a282539
