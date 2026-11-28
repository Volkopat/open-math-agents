import Mathlib

/-!
# A174905: Numbers with no pair (d,e) of divisors such that d < e < 2*d.

Source: https://oeis.org/A174905
Credit: @esracummings31-blip

Conjecture (OEIS, Omar E. Pol, Feb 16 2026): Numbers m such that A001227(m) equals the number
of 2-dense sublists of divisors of m.

Conventions.
* A001227(m) is the number of odd divisors of `m`.
* The 2-dense sublists of divisors of `m` (as in A384149 / A174973): list the divisors of `m`
  in increasing order and cut between adjacent divisors `d < e` exactly when `e > 2*d`; the
  pieces are the maximal sublists in which adjacent terms differ by a factor `≤ 2`.
* The sequence lists positive integers, so we quantify over `m ≥ 1`.
-/

namespace OMA.S_oeis_a174905

/-- `m` has no pair of divisors `d < e < 2d`. -/
def NoPair (m : ℕ) : Prop := ¬ ∃ d e : ℕ, d ∣ m ∧ e ∣ m ∧ d < e ∧ e < 2 * d

/-- A001227: number of odd divisors. -/
def oddDivisorCount (m : ℕ) : ℕ := (m.divisors.filter Odd).card

/-- Number of 2-dense sublists of the divisors of `m`. -/
def twoDenseCount (m : ℕ) : ℕ :=
  ((m.divisors.sort (· ≤ ·)).splitBy (fun d e => decide (e ≤ 2 * d))).length

theorem main : ∀ m : ℕ, 1 ≤ m → (NoPair m ↔ oddDivisorCount m = twoDenseCount m) := by
  sorry

end OMA.S_oeis_a174905
