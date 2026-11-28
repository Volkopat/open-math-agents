import Mathlib

/-!
# OEIS A295481: Peter Bala's fractional-index integrality conjecture

Source: https://oeis.org/A295481 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A295481, offset 0: a(n) = (24*n)!*(4*n)!*(3*n)!/((12*n)!*(9*n)!*(8*n)!*(2*n)!).
Data: 1,6374082,180669266788650,5882199787281395215344,202857467914154836183288657770,7221430962039777689508936047385667332,262302851034768406033478290202841394160147760,9661245477414039526585354113472313766826824134193600

The conjecture of the entry, as the site states the problem:
Conjecture: for n >= 0, a(n/2) = (12*n)!*(2*n)!*(3*n/2)! / ((6*n)!*(9*n/2)!*(4*n)!*n!) is an
integer, where fractional factorials are defined using the Gamma function - for example, (3*n/2)!
:= Gamma(3*n/2 + 1). - Peter Bala, Jul 31 2026

Formalization notes:
* The fractional factorial is `ffact x = Real.Gamma (x + 1)`, which is the entry's convention
  x! := Gamma(x + 1); for a natural number m, `ffact m = m!` (`Real.Gamma_nat_eq_factorial`).
* Each conjectured quantity is written exactly as in the comment, with n a natural number cast to
  the reals and the arguments such as 7*n/2 computed in the reals (no rounding). Integrality is
  stated as equality with the cast of some integer z, for every n >= 0.
* For n divisible by the denominator of the fractional arguments the quantity is the entry's own term a(m) =
  (24*m)!(4*m)!(3*m)!/((12*m)!(9*m)!(8*m)!(2*m)!), so only the remaining residues are new. With this reading the
  sequence a(m) for m = 0, 1, ... reproduces all 8 listed terms (checked with exact
  rational arithmetic), and the conjectured quantities are integers for every n < 200 (checked
  the same way: each Gamma value at a non-integer point cancels against one with the same
  fractional part).
-/

namespace OMA.S_oeis_a295481

/-- The fractional factorial x! := Gamma(x + 1). -/
noncomputable def ffact (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- Peter Bala's conjecture for OEIS A295481. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, ffact (12 * (n : ℝ)) * ffact (2 * (n : ℝ)) * ffact (3 * (n : ℝ) / 2) / (ffact (6 * (n : ℝ)) * ffact (9 * (n : ℝ) / 2) * ffact (4 * (n : ℝ)) * ffact ((n : ℝ))) = z := by
  sorry

end OMA.S_oeis_a295481
