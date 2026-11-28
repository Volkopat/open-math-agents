import Mathlib

/-!
# OEIS A295471: Peter Bala's fractional-index integrality conjecture

Source: https://oeis.org/A295471 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A295471, offset 0: a(n) = (20*n)!*n!/((10*n)!*(8*n)!*(3*n)!).
Data: 1,2771340,44524428808860,835982760936614190900,16702642470437308383606668060,345116202503279265243707597937393840,7282855378270617096441349556073829143864900,155927544469969434644890704895476696960247603510200

The conjecture of the entry, as the site states the problem:
Conjecture: for n >= 0, a(n/2) = (10*n)!*(n/2)! / ((5*n)!*(4*n)!*(3*n/2)!) is an integer, where
fractional factorials are defined using the Gamma function - for example, (3*n/2)! := Gamma(3*n/2
+ 1). - Peter Bala, Jul 30 2026

Formalization notes:
* The fractional factorial is `ffact x = Real.Gamma (x + 1)`, which is the entry's convention
  x! := Gamma(x + 1); for a natural number m, `ffact m = m!` (`Real.Gamma_nat_eq_factorial`).
* Each conjectured quantity is written exactly as in the comment, with n a natural number cast to
  the reals and the arguments such as 7*n/2 computed in the reals (no rounding). Integrality is
  stated as equality with the cast of some integer z, for every n >= 0.
* For n divisible by the denominator of the fractional arguments the quantity is the entry's own term a(m) =
  (20*m)!m!/((10*m)!(8*m)!(3*m)!), so only the remaining residues are new. With this reading the
  sequence a(m) for m = 0, 1, ... reproduces all 8 listed terms (checked with exact
  rational arithmetic), and the conjectured quantities are integers for every n < 200 (checked
  the same way: each Gamma value at a non-integer point cancels against one with the same
  fractional part).
-/

namespace OMA.S_oeis_a295471

/-- The fractional factorial x! := Gamma(x + 1). -/
noncomputable def ffact (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- Peter Bala's conjecture for OEIS A295471. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, ffact (10 * (n : ℝ)) * ffact ((n : ℝ) / 2) / (ffact (5 * (n : ℝ)) * ffact (4 * (n : ℝ)) * ffact (3 * (n : ℝ) / 2)) = z := by
  sorry

end OMA.S_oeis_a295471
