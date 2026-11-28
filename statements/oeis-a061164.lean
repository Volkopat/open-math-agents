import Mathlib

/-!
# OEIS A061164: Peter Bala's fractional-index integrality conjecture

Source: https://oeis.org/A061164 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A061164, offset 0: a(n) = (20*n)!*n!/((10*n)!*(7*n)!*(4*n)!).
Data: 1,5542680,190818980609400,7691041400616850556280,330014847932376708502470210680,14647137653300940580784413641872332680,663999280578266939183818080578580843597787800,30541460340748361003270983719744457382865889296237000

The conjecture of the entry, as the site states the problem:
Conjecture: for n >= 0, a(n/2) = (10*n)!*(n/2)! / ((5*n)!*(7*n/2)!*(2*n)!) is an integer, where
fractional factorials are defined using the Gamma function - for example, (n/2)! := Gamma(n/2 +
1). - Peter Bala, Jul 31 2026

Formalization notes:
* The fractional factorial is `ffact x = Real.Gamma (x + 1)`, which is the entry's convention
  x! := Gamma(x + 1); for a natural number m, `ffact m = m!` (`Real.Gamma_nat_eq_factorial`).
* Each conjectured quantity is written exactly as in the comment, with n a natural number cast to
  the reals and the arguments such as 7*n/2 computed in the reals (no rounding). Integrality is
  stated as equality with the cast of some integer z, for every n >= 0.
* For n divisible by the denominator of the fractional arguments the quantity is the entry's own term a(m) =
  (20*m)!m!/((10*m)!(7*m)!(4*m)!), so only the remaining residues are new. With this reading the
  sequence a(m) for m = 0, 1, ... reproduces all 8 listed terms (checked with exact
  rational arithmetic), and the conjectured quantities are integers for every n < 200 (checked
  the same way: each Gamma value at a non-integer point cancels against one with the same
  fractional part).
-/

namespace OMA.S_oeis_a061164

/-- The fractional factorial x! := Gamma(x + 1). -/
noncomputable def ffact (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- Peter Bala's conjecture for OEIS A061164. -/
theorem main :
    ∀ n : ℕ, ∃ z : ℤ, ffact (10 * (n : ℝ)) * ffact ((n : ℝ) / 2) / (ffact (5 * (n : ℝ)) * ffact (7 * (n : ℝ) / 2) * ffact (2 * (n : ℝ))) = z := by
  sorry

end OMA.S_oeis_a061164
