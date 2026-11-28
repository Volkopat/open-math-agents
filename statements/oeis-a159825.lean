import Mathlib

/-!
# A159825: continued fraction for e^e^e (infinite and aperiodic)

Source: https://oeis.org/A159825 (OEIS Foundation, CC BY-SA 4.0)
Credit: @trador01 (agent: Claude Code, model claude-opus-5-5)

A159825 (offset 0): the continued fraction of e^e^e = e^(e^e) = 3814279.1047... (A073227);
data 3814279, 9, 1, 1, 4, 1, 53, 26, ...

The entry records (Vladimir Reshetnikov, Apr 27 2013):

  It was conjectured (but remains unproved) that this sequence is infinite and aperiodic, but it
  is difficult to determine who first posed this problem.

Reading of the source:
* e^e^e is read as `exp (exp (exp 1))`, matching A073227 and the first term 3814279.
* The continued fraction is Mathlib's regular continued fraction `GenContFract.of x`; its
  integer part is `.h` (the term 3814279) and the later terms are its partial denominators
  `.partDens`, a possibly finite sequence.
* "infinite": the continued fraction does not terminate.
* "aperiodic": the sequence of terms is not eventually periodic: there are no `N` and `p > 0`
  with the `(n + p)`-th partial denominator equal to the `n`-th for every `n ≥ N`. Leaving out the
  integer part does not matter for eventual periodicity. (By Lagrange's theorem this is the same
  as `e^e^e` not being a quadratic irrational; the statement keeps the source's wording instead.)
-/

namespace OMA.S_oeis_a159825

/-- The regular continued fraction of `e^e^e`. -/
noncomputable def cf : GenContFract ℝ := GenContFract.of (Real.exp (Real.exp (Real.exp 1)))

/-- The continued fraction of `e^e^e` is infinite and not eventually periodic. -/
theorem main :
    ¬ cf.Terminates ∧
      ¬ ∃ N p : ℕ, 0 < p ∧ ∀ n, N ≤ n → cf.partDens.get? (n + p) = cf.partDens.get? n := by
  sorry

end OMA.S_oeis_a159825
