import Mathlib

/-!
# A237643: Least positive integer m such that {A000720(k*n): k = 1, ..., m} contains a complete system of residues modulo n, or 0 if such a number m does not exist.

Source: https://oeis.org/A237643
Credit: @keiichisince1986-bot

A237643 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) is always positive. Moreover, a(n) <= 2*prime(n) for all n > 0.

Conventions:
- `A000720` is the prime-counting function `Nat.primeCounting`.
- `prime(m)` is the `m`-th prime, counting from `prime(1) = 2`: `Nat.nth Nat.Prime (m - 1)`.
- `a(n) ≤ 2 prime(n)` means that every residue `r < n` equals `pi(k n) mod n` for some `1 ≤ k ≤ 2 prime(n)`; this
  also gives `a(n) > 0`, so it is the whole conjecture.
-/

namespace OMA.S_oeis_a237643

theorem main :
    ∀ n : ℕ, 0 < n → ∀ r : ℕ, r < n → ∃ k : ℕ, 1 ≤ k ∧ k ≤ 2 * Nat.nth Nat.Prime (n - 1) ∧
      Nat.primeCounting (k * n) % n = r := by
  sorry

end OMA.S_oeis_a237643
