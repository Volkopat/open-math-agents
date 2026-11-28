import Mathlib

/-!
# A330077: a(n) = numerator of Sum_{1 <= i < j <= d(n)} 1/(d_j - d_i), sum over ordered pairs of divisors of n, where d(n) is the number of divisors of n.

Source: https://oeis.org/A330077
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A330077 (Amiram Eldar, Nov 30 2019): (Erdős and
Nicolas) H(n) = a(n)/A330078(n) < d(n) for all n > 5040.

Conventions:
* The sequence has offset 1 (data 0, 1, 1, 11, 1, 197, 1, 67, 19, 727, 1, 24593, ...).
* H(n) = Sum_{1 <= i < j <= d(n)} 1/(d_j - d_i), where d_1 < d_2 < ... are the divisors of n and
  d(n) is their number; it is the helper `H n : ℚ`, the sum of 1/(e - d) over all pairs (d, e) of
  divisors of n with d < e. a(n) and A330078(n) are the numerator and denominator of H(n), so
  a(n)/A330078(n) = H(n).
* d(n) is the cardinality of `Nat.divisors n`, cast to `ℚ`.
-/

namespace OMA.S_oeis_a330077

/-- H(n) = sum of 1/(e - d) over the pairs d < e of divisors of n. -/
def H (n : ℕ) : ℚ :=
  ∑ p ∈ (n.divisors ×ˢ n.divisors).filter (fun p => p.1 < p.2), 1 / ((p.2 : ℚ) - (p.1 : ℚ))

/-- The Erdős-Nicolas conjecture recorded in A330077: H(n) < d(n) for all n > 5040. -/
theorem main : ∀ n : ℕ, 5040 < n → H n < (n.divisors.card : ℚ) := by
  sorry

end OMA.S_oeis_a330077
