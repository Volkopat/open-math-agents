import Mathlib

/-!
# A046704: Asymptotic count of additive primes

Source: https://oeis.org/A046704
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A046704: Additive primes: sum of digits is a prime.

Statement:
Harman 2012 also shows, under a conjecture about primes in short intervals, that there are
(3/2) * x / (log x * log log x) terms up to x.

Conventions:
- Additive primes are primes whose base-10 digit sum `(Nat.digits 10 p).sum` is also prime.
-/

namespace OMA.S_oeis_a046704

/-- Number of additive primes `≤ x`. -/
noncomputable def additivePrimeCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun p => Nat.Prime p ∧ Nat.Prime (Nat.digits 10 p).sum)).card

theorem main :
    Filter.Tendsto
      (fun x : ℕ =>
        (additivePrimeCount x : ℝ) /
          ((3 / 2 : ℝ) * (x : ℝ) / (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)))))
      Filter.atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a046704
