import Mathlib

/-!
# A231548: Numbers n such that 2*n - 1 < sigma(n) - sigma(n-2).

Source: https://oeis.org/A231548
Credit: @agchua

Comment lines of A231548 (the entry is by Jaroslav Krizek, Nov 12 2013), verbatim:
  Also numbers n such that antisigma(n) < antisigma(n-2), where antisigma(n) = A024816(n) = the
  sum of the non-divisors of n that are between 1 and n.
  Conjecture: there are no numbers n such that antisigma(n) < antisigma(n-3).
A024816 (offset 1): Antisigma(n): Sum of the numbers less than n that do not divide n
(data 0, 0, 2, 3, 9, 9, 20, 21, 32, 37, 54, ...).

Formalisation. antisigma n is the sum of the numbers k with 1 <= k < n that do not divide n.
Since A024816 has offset 1, antisigma(n-3) is meant for n >= 4. So the conjecture says: there
is no n >= 4 with antisigma n < antisigma (n - 3).
-/

namespace OMA.S_oeis_a231548

/-- A024816: antisigma(n), the sum of the numbers less than n that do not divide n. -/
def antisigma (n : ℕ) : ℕ := ∑ k ∈ (Finset.Ico 1 n).filter (fun k => ¬ k ∣ n), k

/-- There are no numbers n such that antisigma(n) < antisigma(n-3). -/
theorem main : ¬ ∃ n : ℕ, 4 ≤ n ∧ antisigma n < antisigma (n - 3) := by
  sorry

end OMA.S_oeis_a231548
