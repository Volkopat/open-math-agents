import Mathlib

/-!
# A242169: Least prime divisor of Fr(n) which does not divide any Fr(k) with k < n, or 1 if such a primitive prime divisor of Fr(n) does not exist, where Fr(n) denotes the n-th Franel number given by A000172.

Source: https://oeis.org/A242169
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry): a(n) > 1 for all n > 0.

Formalization notes:
* Fr(n) = Sum_{k=0..n} binomial(n,k)^3 (A000172). a(n) > 1 means Fr(n) has a primitive prime
  divisor: a prime dividing Fr(n) and no Fr(k) with k < n.
* Controls (computed): Fr(n) has a primitive prime divisor for every 1 ≤ n < 120.
-/

namespace OMA.S_oeis_a242169

/-- The Franel numbers A000172. -/
def franel (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (n.choose k) ^ 3

/-- Every `Fr(n)`, `n ≥ 1`, has a primitive prime divisor. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ p : ℕ, p.Prime ∧ p ∣ franel n ∧ ∀ k : ℕ, k < n → ¬ p ∣ franel k := by
  sorry

end OMA.S_oeis_a242169
