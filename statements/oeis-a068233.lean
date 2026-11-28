import Mathlib

/-!
# A068233: a(n) is the smallest prime p such that p and the next n-1 primes are all == 7 (mod 12).

Source: https://oeis.org/A068233
Credit: @keiichisince1986-bot

A068233 is the sequence `a(n)` named in the title. The entry states:
Dickson's conjecture implies that a(n) exists for all n. (The statement below is the claim that a(n)
exists for every n >= 1. It also follows from Shiu's theorem on strings of congruent consecutive primes,
D. K. L. Shiu, J. London Math. Soc. 61 (2000).)

Conventions:
- Primes are indexed from `0`: `Nat.nth Nat.Prime i`. `a(n)` exists means that some `n` consecutive primes
  `Nat.nth Nat.Prime i, …, Nat.nth Nat.Prime (i + n - 1)` are all congruent to `7` modulo `12`.
-/

namespace OMA.S_oeis_a068233

theorem main :
    ∀ n : ℕ, 1 ≤ n → ∃ i : ℕ, ∀ j : ℕ, j < n → Nat.nth Nat.Prime (i + j) % 12 = 7 := by
  sorry

end OMA.S_oeis_a068233
