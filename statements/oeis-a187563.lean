import Mathlib

/-!
# A187563: Least k >=0 and k < prime(n) such that prime(n)*(prime(n)-k)-1 and prime(n)*(prime(n)-k)+1 are twin primes or -1 if no such k exists.

Source: https://oeis.org/A187563
Credit: @darealpandaboi

Conjectures: there are only 11 primes (5, 11, 13, 31, 37, 53, 61, 73, 79, 97, 127) for which k does
not exist; and there is always at least a pair of twin primes between prime(n) and prime(n)^2.

Translation notes.
* k does not exist for the prime p when no k with 0 <= k < p makes p(p - k) - 1 and
  p(p - k) + 1 both prime. The first conjecture says these p are exactly the 11 listed primes.
  This reproduces the listed data, and among primes p < 4000 exactly these 11 have a(n) = -1
  (checked by computer).
* Twin primes between p and p^2: q and q + 2 both prime with p < q and q + 2 < p^2. For p = 2
  no such pair exists (the interval (2, 4) contains only 3), so the second conjecture is stated
  for primes p >= 3; a computer check confirms it for the first 200 primes from 3 on.
-/

namespace OMA.S_oeis_a187563

theorem main :
    {p : ℕ | p.Prime ∧ ¬ ∃ k : ℕ, k < p ∧ (p * (p - k) - 1).Prime ∧ (p * (p - k) + 1).Prime} =
      {5, 11, 13, 31, 37, 53, 61, 73, 79, 97, 127} ∧
    ∀ p : ℕ, p.Prime → 3 ≤ p → ∃ q : ℕ, p < q ∧ q + 2 < p ^ 2 ∧ q.Prime ∧ (q + 2).Prime := by
  sorry

end OMA.S_oeis_a187563
