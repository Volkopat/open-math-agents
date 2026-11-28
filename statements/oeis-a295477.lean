import Mathlib

/-!
# OEIS A295477: Peter Bala's fractional-index integrality conjecture

Source: https://oeis.org/A295477 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @marcusbuffett.

Entry A295477, offset 0: a(n) = (24*n)!*n!/((12*n)!*(8*n)!*(5*n)!).
Data: 1,267711444,527048385075849780,1217325447549161369383451760,2994861478939539397101967737771147060,7622711741038504461830231565042108084502603944,19819090822775008829253654773280241192988848189242236400,52286737777519489251960880501419064028764839670925596855165438440

The conjecture of the entry, as the site states the problem:
Conjectures: for n >= 0, both a(n/2) = (12*n)!*(n/2)! / ((6*n)!*(4*n)!*(5*n/2)!) and a(n/4) =
(6*n)!*(n/4)! / ((3*n)!*(2*n)!*(5*n/4)!) are integers, where fractional factorials are defined
using the Gamma function - for example, (n/2)! := Gamma(n/2 + 1). - Peter Bala, Jul 31 2026

Formalization notes:
* The fractional factorial is `ffact x = Real.Gamma (x + 1)`, which is the entry's convention
  x! := Gamma(x + 1); for a natural number m, `ffact m = m!` (`Real.Gamma_nat_eq_factorial`).
* Each conjectured quantity is written exactly as in the comment, with n a natural number cast to
  the reals and the arguments such as 7*n/2 computed in the reals (no rounding). Integrality is
  stated as equality with the cast of some integer z, for every n >= 0.
* The entry states two integrality claims (both are conjectures); `main` is their
  conjunction, in the order of the comment.
* For n divisible by the denominator of the fractional arguments the quantity is the entry's own
  term a(m) = (24*m)!m!/((12*m)!(8*m)!(5*m)!), so only the remaining residues are new. With
  this reading the sequence a(m) for m = 0, 1, ... reproduces all 8 listed terms (checked with
  exact rational arithmetic), and the conjectured quantities are integers for every n < 200
  (checked the same way: each Gamma value at a non-integer point cancels against one with the
  same fractional part).
-/

namespace OMA.S_oeis_a295477

/-- The fractional factorial x! := Gamma(x + 1). -/
noncomputable def ffact (x : ℝ) : ℝ := Real.Gamma (x + 1)

/-- Peter Bala's conjecture for OEIS A295477. -/
theorem main :
    (∀ n : ℕ, ∃ z : ℤ, ffact (12 * (n : ℝ)) * ffact ((n : ℝ) / 2) / (ffact (6 * (n : ℝ)) * ffact (4 * (n : ℝ)) * ffact (5 * (n : ℝ) / 2)) = z) ∧
    (∀ n : ℕ, ∃ z : ℤ, ffact (6 * (n : ℝ)) * ffact ((n : ℝ) / 4) / (ffact (3 * (n : ℝ)) * ffact (2 * (n : ℝ)) * ffact (5 * (n : ℝ) / 4)) = z) := by
  sorry

end OMA.S_oeis_a295477
