import Mathlib

/-!
# A188666: the largest m with lcm(m..n) = lcm(1..n) is the least prime power above n/2

Source: https://oeis.org/A188666 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry (Reinhard Zumkeller, Apr 25 2011), offset 1:
Largest m <= n such that lcm(m, m+1, ..., n) = lcm(1, 2, ..., n). Data
1, 2, 2, 3, 3, 4, 4, 5, 5, 7, 7, 7, 7, 8, 8, 9, 9, 11, 11, 11, 11, 13, ...

Comment: Conjecture: a(n) = A000015(floor(n/2)+1). - Georg Fischer, Nov 29 2022
Status: known result. A later comment of the entry gives a proof that uses Nagura's theorem
on primes in short intervals.

Formalization notes.
* a(n) is the greatest element of the set of the m with 1 <= m <= n and
  lcm(m, ..., n) = lcm(1, ..., n). `main` is stated for every m that is the greatest element of
  this set (`IsGreatest`), so it needs no separate definition of the sequence.
* A000015(k) is the smallest prime power >= k, where 1 counts as a prime power (A000015(1) = 1).
  In Mathlib `IsPrimePow 1` is false, so the condition is `q = 1 ∨ IsPrimePow q`.
* floor(n/2) is the quotient `n / 2` of natural numbers.
-/

namespace OMA.S_oeis_a188666

/-- Fischer's conjecture: a(n) is the smallest prime power that is at least floor(n/2) + 1. -/
theorem main : ∀ n m : ℕ, 1 ≤ n →
    IsGreatest {k : ℕ | 1 ≤ k ∧ k ≤ n ∧ (Finset.Icc k n).lcm id = (Finset.Icc 1 n).lcm id} m →
    IsLeast {q : ℕ | (q = 1 ∨ IsPrimePow q) ∧ n / 2 + 1 ≤ q} m := by
  sorry

end OMA.S_oeis_a188666
