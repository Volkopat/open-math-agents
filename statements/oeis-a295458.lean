import Mathlib

/-!
# OEIS A295458: Peter Bala's fractional-index integrality conjecture

Source: https://oeis.org/A295458 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A295458, offset 0: a(n) = (30*n)!*(5*n)!*(4*n)!/((15*n)!*(10*n)!*(8*n)!*(6*n)!).
Data: 1,5545451340,188242272043069768860,7383354803839076831124554790900,307213802011837003346320048243705086348060,13202980048704429908831487095516759161045931997393840,579138708444140353944173816622205024638976091097557185100664900

The conjecture of the entry, as the site states the problem:
Conjecture: for n >= 0, both a(n/2) = (15*n)!*(5*n/2)!*(2*n)! / ((15*n/2)!*(5*n)!*(4*n)!*(3*n)!)
and a(n/3) = (10*n)!*(5*n/3)!*(4*n/3)! / ((5*n)!*(10*n/3)!*(8*n/3)!*(2*n)!) are integers, where
fractional factorials are defined using the Gamma function - for example, (5*n/2)! := Gamma(5*n/2
+ 1). - Peter Bala, Jul 29 2026

Formalization notes:
* The fractional factorial is `ffact x = Real.Gamma (x + 1)`, which is the entry's convention
  x! := Gamma(x + 1); for a natural number m, `ffact m = m!` (`Real.Gamma_nat_eq_factorial`).
* Each conjectured quantity is written exactly as in the comment, with n a natural number cast to
  the reals and the arguments such as 7*n/2 computed in the reals (no rounding). Integrality is
  stated as equality with the cast of some integer z, for every n >= 0.
* The entry states two integrality claims (both are conjectures); `main` is their
  conjunction, in the order of the comment.
* For n divisible by the denominator of the fractional arguments the quantity is the entry's own
  term a(m) = (30*m)!(5*m)!(4*m)!/((15*m)!(10*m)!(8*m)!(6*m)!), so only the remaining residues are new. With
  this reading the sequence a(m) for m = 0, 1, ... reproduces all 7 listed terms (checked with
  exact rational arithmetic), and the conjectured quantities are integers for every n < 200
  (checked the same way: each Gamma value at a non-integer point cancels against one with the
  same fractional part).
-/

namespace OMA.S_oeis_a295458

/-- The fractional factorial x! := Gamma(x + 1). -/
noncomputable def ffact (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- Peter Bala's conjecture for OEIS A295458. -/
theorem main :
    (∀ n : ℕ, ∃ z : ℤ, ffact (15 * (n : ℝ)) * ffact (5 * (n : ℝ) / 2) * ffact (2 * (n : ℝ)) / (ffact (15 * (n : ℝ) / 2) * ffact (5 * (n : ℝ)) * ffact (4 * (n : ℝ)) * ffact (3 * (n : ℝ))) = z) ∧
    (∀ n : ℕ, ∃ z : ℤ, ffact (10 * (n : ℝ)) * ffact (5 * (n : ℝ) / 3) * ffact (4 * (n : ℝ) / 3) / (ffact (5 * (n : ℝ)) * ffact (10 * (n : ℝ) / 3) * ffact (8 * (n : ℝ) / 3) * ffact (2 * (n : ℝ))) = z) := by
  sorry

end OMA.S_oeis_a295458
