import Mathlib

/-!
# A256619: Numbers n such that there are no primes in the interval [b(n), b(n+1) - 1], where b(n) = 1 + Sum_{k=1..n} floor(1/2 + sqrt(2*k - 2)).

Source: https://oeis.org/A256619
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A256619 (Arkadiusz Wesolowski, Apr 05 2015): the
sequence is finite and complete.

Conventions:
* The sequence has offset 1 (data 1, 26, 29, 38, 47, 97, 114, 127, 216, 276, 433, 1094, ...).
* b(n) = 1 + Sum_{k=1..n} floor(1/2 + sqrt(2*k - 2)); the summand is computed in `ℝ` (sqrt is
  `Real.sqrt`) and its floor is the natural-number floor `Nat.floor`. The terms are the positive
  integers n such that no prime p satisfies b(n) <= p <= b(n+1) - 1, i.e. b(n) <= p < b(n+1).
* `Finite and complete` is stated as: the set of all terms equals the set of the 13 terms listed
  in the entry.
-/

namespace OMA.S_oeis_a256619

/-- b(n) = 1 + Sum_{k=1..n} floor(1/2 + sqrt(2k - 2)). -/
noncomputable def b (n : ℕ) : ℕ :=
  1 + ∑ k ∈ Finset.Icc 1 n, ⌊(1 / 2 : ℝ) + Real.sqrt (2 * (k : ℝ) - 2)⌋₊

/-- The conjecture recorded in A256619. -/
theorem main : {n : ℕ | 0 < n ∧ ∀ p : ℕ, p.Prime → ¬ (b n ≤ p ∧ p < b (n + 1))} =
    ({1, 26, 29, 38, 47, 97, 114, 127, 216, 276, 433, 1094, 1284} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a256619
