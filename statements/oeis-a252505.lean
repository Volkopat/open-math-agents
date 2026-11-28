import Mathlib

/-!
OEIS A252505: Number of biquadratefree (4th power free) divisors of n.

Conjecture (Sequence Machine, reported by Antti Karttunen, 2025): a(n) = A000005(A058035(n)),
where A000005 is the number of divisors and A058035(n) is the largest 4th-power-free number
dividing n, i.e. A058035(n) = Product_{p prime, p | n} p^min(v_p(n), 3).
-/

namespace OMA.S_oeis_a252505

/-- A252505: the number of divisors d of n such that no p^4 (p prime) divides d
(it suffices to check primes p dividing d). -/
def a (n : ℕ) : ℕ := (n.divisors.filter (fun d => ∀ p ∈ d.primeFactors, ¬ p ^ 4 ∣ d)).card

/-- A058035: the largest 4th-power-free divisor of n. -/
def a058035 (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p ^ min (n.factorization p) 3

theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = (a058035 n).divisors.card := by
  sorry

end OMA.S_oeis_a252505
