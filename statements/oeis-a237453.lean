import Mathlib

/-!
# A237453: Number of primes p < n with p*n + pi(p) prime, where pi(.) is given by A000720.

Source: https://oeis.org/A237453
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A237453 (Zhi-Wei Sun, Feb 08 2014), part (i): a(n) > 0
for all n > 4, and a(n) = 1 for no n > 144. Moreover, for any positive integer n, there is a prime
p < sqrt(2*n)*log(5n) with p*n + pi(p) prime.

Conventions:
* The sequence has offset 1 (data 0, 0, 1, 0, 2, 1, 1, 2, 3, 1, 1, 1, ...). `a n` is the number of
  primes p < n with p*n + pi(p) prime, exactly as in the OEIS name.
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* log is the natural logarithm `Real.log`, and the bound p < sqrt(2*n)*log(5n) is stated in `ℝ`
  with p and n cast.
* All three assertions of part (i) are formalized, as a conjunction. Parts (ii)-(iv) are different
  statements and are not formalized.
* The set of such tuples is finite for every n, so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a237453

/-- The condition in the name of A237453 on a tuple, for a given n. -/
def P (n : ℕ) (p : ℕ) : Prop :=
  p.Prime ∧ p < n ∧ (p * n + Nat.primeCounting p).Prime

/-- A237453: the number of representations of n described in the OEIS name. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {t : ℕ | P n t}

/-- The conjecture recorded in A237453. -/
theorem main : (∀ n : ℕ, 4 < n → 0 < a n) ∧ (∀ n : ℕ, 144 < n → a n ≠ 1) ∧
    (∀ n : ℕ, 0 < n → ∃ p : ℕ, p.Prime ∧
    (p : ℝ) < Real.sqrt (2 * n) * Real.log (5 * n) ∧
      (p * n + Nat.primeCounting p).Prime) := by
  sorry

end OMA.S_oeis_a237453
