import Mathlib

/-!
# OEIS A295464: Peter Bala's fractional-index integrality conjecture

Source: https://oeis.org/A295464 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A295464, offset 0: a(n) = (30*n)!*(5*n)!*(3*n)!/((15*n)!*(10*n)!*(7*n)!*(6*n)!).
Data: 1,11090902680,806752594470299009400,67926864195319506846345904076280,6070004571618493758425092821342656541250680,560350006184720363483642231730314219687919996242332680,52801774275140194976895125566622993449415218651496078394967387800

The conjecture of the entry, as the site states the problem:
Conjecture: for n >= 0, a(n/2) = (15*n)!*(5*n/2)!*(3*n/2)!/((15*n/2)!*(5*n)!*(7*n/2)!*(3*n)!) is
an integer, where fractional factorials are defined using the Gamma function - for example,
(5*n/2)! := Gamma(5*n/2 + 1). - Peter Bala, Aug 03 2026

Formalization notes:
* The fractional factorial is `ffact x = Real.Gamma (x + 1)`, which is the entry's convention
  x! := Gamma(x + 1); for a natural number m, `ffact m = m!` (`Real.Gamma_nat_eq_factorial`).
* Each conjectured quantity is written exactly as in the comment, with n a natural number cast to
  the reals and the arguments such as 7*n/2 computed in the reals (no rounding). Integrality is
  stated as equality with the cast of some integer z, for every n >= 0.
* For n divisible by the denominator of the fractional arguments the quantity is the entry's own term a(m) =
  (30*m)!(5*m)!(3*m)!/((15*m)!(10*m)!(7*m)!(6*m)!), so only the remaining residues are new. With this reading the
  sequence a(m) for m = 0, 1, ... reproduces all 7 listed terms (checked with exact
  rational arithmetic), and the conjectured quantities are integers for every n < 200 (checked
  the same way: each Gamma value at a non-integer point cancels against one with the same
  fractional part).
-/

namespace OMA.S_oeis_a295464

/-- The fractional factorial x! := Gamma(x + 1). -/
noncomputable def ffact (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- Peter Bala's conjecture for OEIS A295464. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, ffact (15 * (n : ℝ)) * ffact (5 * (n : ℝ) / 2) * ffact (3 * (n : ℝ) / 2) / (ffact (15 * (n : ℝ) / 2) * ffact (5 * (n : ℝ)) * ffact (7 * (n : ℝ) / 2) * ffact (3 * (n : ℝ))) = z := by
  sorry

end OMA.S_oeis_a295464
