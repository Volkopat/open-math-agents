import Mathlib.NumberTheory.Bernoulli

/-!
# Ramanujan's primality claim in OEIS A001067

Source: https://oeis.org/A001067 (OEIS Foundation, CC BY-SA 4.0).
See also A119766 for the statement apart from sign and the known
counterexample. The entry has positive indices. Ramanujan's claim
states that the absolute numerator of B(2n)/(2n) is 1 or prime.
-/

namespace OMA.S_oeis_a001067

def absNumerator (n : ℕ) : ℕ := (bernoulli (2*n) / (2*(n:ℚ))).num.natAbs

theorem main : ∀ n : ℕ, 1 ≤ n → absNumerator n = 1 ∨ (absNumerator n).Prime := by
  sorry

end OMA.S_oeis_a001067
