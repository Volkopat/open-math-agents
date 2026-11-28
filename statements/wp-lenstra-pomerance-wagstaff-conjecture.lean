import Mathlib

/-!
# Lenstra–Pomerance–Wagstaff conjecture

Source: https://en.wikipedia.org/wiki/Lenstra%E2%80%93Pomerance%E2%80%93Wagstaff_conjecture
(redirects to https://en.wikipedia.org/wiki/Mersenne_conjectures#Lenstra%E2%80%93Pomerance%E2%80%93Wagstaff_conjecture)
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Source statement: there are infinitely many Mersenne primes and, more precisely, the number of
Mersenne primes less than `x` is asymptotically approximated by `e^γ · log₂ log₂ x`, where `γ`
is the Euler–Mascheroni constant.

Conventions:
* a Mersenne prime is a prime number of the form `2^k - 1` (Mathlib's `mersenne k`); the count
  is over the primes themselves, not over exponents, as in the source ("Mersenne primes less
  than `x`");
* `x` is a real variable tending to `+∞`; "asymptotically approximated by" is read as asymptotic
  equivalence (`Asymptotics.IsEquivalent`, i.e. the ratio tends to 1), the standard meaning;
* `γ` is Mathlib's `Real.eulerMascheroniConstant` and `log₂` is `Real.logb 2`.
The source's restatement in terms of exponents `p < y` (asymptotic `e^γ · log₂ y`) is the same
assertion after the substitution `x = 2^y`; only the first form is stated here.
The "infinitely many" part follows from the asymptotic, so it is not stated separately.
-/

namespace OMA.S_wp_lenstra_pomerance_wagstaff_conjecture

open Asymptotics Filter

/-- The number of Mersenne primes less than `x`. -/
noncomputable def mersennePrimeCount (x : ℝ) : ℕ :=
  {m : ℕ | (m : ℝ) < x ∧ m.Prime ∧ ∃ k : ℕ, m = mersenne k}.ncard

theorem main :
    (fun x : ℝ => (mersennePrimeCount x : ℝ)) ~[atTop]
      (fun x : ℝ => Real.exp Real.eulerMascheroniConstant * Real.logb 2 (Real.logb 2 x)) := by
  sorry

end OMA.S_wp_lenstra_pomerance_wagstaff_conjecture
