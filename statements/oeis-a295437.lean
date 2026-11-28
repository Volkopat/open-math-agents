import Mathlib

/-!
# OEIS A295437: Peter Bala's fractional-index integrality conjecture

Source: https://oeis.org/A295437 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A295437, offset 0: a(n) = (18*n)!*n!/((9*n)!*(6*n)!*(4*n)!).
Data: 1,1021020,6016814703900,41477110789150966020,304331361887290342345862940,2309513382640863232775760738593520,17900786683992090777583802478540374204100,140773522690118901080808611014971776285838687000

The conjecture of the entry, as the site states the problem:
Conjectures: for n >= 0, both a(n/2) = (9*n)!*(n/2)! / ((9*n/2)!*(3*n)!*(2*n)!) and a(n/3) =
(6*n)!*(n/3)! / ((3*n)!*(2*n)!*(4*n/3)!) are integers, where fractional factorials are defined
using the Gamma function; for example (n/2)! := Gamma(n/2 + 1). - Peter Bala, Jun 13 2026

Formalization notes:
* The fractional factorial is `ffact x = Real.Gamma (x + 1)`, which is the entry's convention
  x! := Gamma(x + 1); for a natural number m, `ffact m = m!` (`Real.Gamma_nat_eq_factorial`).
* Each conjectured quantity is written exactly as in the comment, with n a natural number cast to
  the reals and the arguments such as 7*n/2 computed in the reals (no rounding). Integrality is
  stated as equality with the cast of some integer z, for every n >= 0.
* The entry states two integrality claims (both are conjectures); `main` is their
  conjunction, in the order of the comment.
* For n divisible by the denominator of the fractional arguments the quantity is the entry's own
  term a(m) = (18*m)!m!/((9*m)!(6*m)!(4*m)!), so only the remaining residues are new. With
  this reading the sequence a(m) for m = 0, 1, ... reproduces all 8 listed terms (checked with
  exact rational arithmetic), and the conjectured quantities are integers for every n < 200
  (checked the same way: each Gamma value at a non-integer point cancels against one with the
  same fractional part).
-/

namespace OMA.S_oeis_a295437

/-- The fractional factorial x! := Gamma(x + 1). -/
noncomputable def ffact (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- Peter Bala's conjecture for OEIS A295437. -/
theorem main :
    (∀ n : ℕ, ∃ z : ℤ, ffact (9 * (n : ℝ)) * ffact ((n : ℝ) / 2) / (ffact (9 * (n : ℝ) / 2) * ffact (3 * (n : ℝ)) * ffact (2 * (n : ℝ))) = z) ∧
    (∀ n : ℕ, ∃ z : ℤ, ffact (6 * (n : ℝ)) * ffact ((n : ℝ) / 3) / (ffact (3 * (n : ℝ)) * ffact (2 * (n : ℝ)) * ffact (4 * (n : ℝ) / 3)) = z) := by
  sorry

end OMA.S_oeis_a295437
