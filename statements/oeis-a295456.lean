import Mathlib

/-!
# OEIS A295456: Peter Bala's fractional-index integrality conjecture

Source: https://oeis.org/A295456 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A295456, offset 0: a(n) = (30*n)!*(5*n)!*(4*n)!/((15*n)!*(12*n)!*(10*n)!*(2*n)!).
Data: 1,168043980,126694219977836700,109504706026534324525391988,100204869963549181630558779565943580,94632263448378916462441320194245442445186480,91178760822805067678742350221792424866578707819103300,89078657321704573467701346299333700225381618490806719145843000

The conjecture of the entry, as the site states the problem:
Conjecture: for n >= 0, both a(n/2) = (15*n)!*(5*n/2)!*(2*n)! / ((15*n/2)!*(6*n)!*(5*n)!*n!) and
a(n/3) = (10*n)!*(5*n/3)!*(4*n/3)! / ((5*n)!*(4*n)!*(10*n/3)!*(2*n/3)!) are integers, where
fractional factorials are defined using the Gamma function; for example (5*n/2)! := Gamma(5*n/2 +
1). - Peter Bala, Jun 13 2026

Formalization notes:
* The fractional factorial is `ffact x = Real.Gamma (x + 1)`, which is the entry's convention
  x! := Gamma(x + 1); for a natural number m, `ffact m = m!` (`Real.Gamma_nat_eq_factorial`).
* Each conjectured quantity is written exactly as in the comment, with n a natural number cast to
  the reals and the arguments such as 7*n/2 computed in the reals (no rounding). Integrality is
  stated as equality with the cast of some integer z, for every n >= 0.
* The entry states two integrality claims (both are conjectures); `main` is their
  conjunction, in the order of the comment.
* For n divisible by the denominator of the fractional arguments the quantity is the entry's own
  term a(m) = (30*m)!(5*m)!(4*m)!/((15*m)!(12*m)!(10*m)!(2*m)!), so only the remaining residues are new. With
  this reading the sequence a(m) for m = 0, 1, ... reproduces all 8 listed terms (checked with
  exact rational arithmetic), and the conjectured quantities are integers for every n < 200
  (checked the same way: each Gamma value at a non-integer point cancels against one with the
  same fractional part).
-/

namespace OMA.S_oeis_a295456

/-- The fractional factorial x! := Gamma(x + 1). -/
noncomputable def ffact (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- Peter Bala's conjecture for OEIS A295456. -/
theorem main :
    (∀ n : ℕ, ∃ z : ℤ, ffact (15 * (n : ℝ)) * ffact (5 * (n : ℝ) / 2) * ffact (2 * (n : ℝ)) / (ffact (15 * (n : ℝ) / 2) * ffact (6 * (n : ℝ)) * ffact (5 * (n : ℝ)) * ffact ((n : ℝ))) = z) ∧
    (∀ n : ℕ, ∃ z : ℤ, ffact (10 * (n : ℝ)) * ffact (5 * (n : ℝ) / 3) * ffact (4 * (n : ℝ) / 3) / (ffact (5 * (n : ℝ)) * ffact (4 * (n : ℝ)) * ffact (10 * (n : ℝ) / 3) * ffact (2 * (n : ℝ) / 3)) = z) := by
  sorry

end OMA.S_oeis_a295456
