import Mathlib

/-!
# A005555: A finite sequence associated with the Lie algebra E_8.

Source: https://oeis.org/A005555
Credit: @agchua

Comment in A005555 (entry by N. J. A. Sloane; keywords nonn, fini, full; offset 0):
  The g.f. (5-6*z+2*z**2)/(z-1)**4 conjectured by Simon Plouffe in his 1992 dissertation is wrong.
The statement below is this comment's assertion: the generating function of A005555 is not
(5-6z+2z^2)/(z-1)^4, the g.f. conjectured by Simon Plouffe (Approximations de series
generatrices et quelques conjectures, Dissertation, UQAM 1992, arXiv:0911.4975).
Definition: A005555 is a finite sequence and the entry lists all of it (keywords fini, full):
its 63 terms, from a(0) = 1 to a(62) = 1240, are the list below. Its generating function is the
polynomial sum of a(n) z^n over n = 0 .. 62, so a(n) is taken to be 0 for n >= 63.
Stated as a non-identity of formal power series over Q:
(sum of a(n) X^n) * (X - 1)^4 is not 5 - 6X + 2X^2,
which says that the g.f. is not (5-6z+2z^2)/(z-1)^4, since (X - 1)^4 is invertible.
-/

namespace OMA.S_oeis_a005555

/-- The 63 terms of the finite sequence A005555, as listed in the entry (offset 0). -/
def terms : List ℕ :=
  [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 20, 21, 22, 24, 25, 28, 29, 30, 31,
    32, 34, 35, 36, 37, 38, 39, 40, 56, 57, 60, 61, 62, 63, 64, 70, 84, 85, 88, 110, 111, 112,
    120, 156, 157, 159, 160, 166, 182, 184, 231, 232, 280, 399, 400, 520, 760, 1240]

/-- A005555(n) for 0 <= n <= 62, and 0 beyond the end of the finite sequence. -/
def a (n : ℕ) : ℕ := terms.getD n 0

/-- The comment of the entry: the g.f. (5-6z+2z^2)/(z-1)^4 conjectured by Plouffe is wrong. -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) * (PowerSeries.X - 1) ^ 4 ≠
    5 - 6 * PowerSeries.X + 2 * PowerSeries.X ^ 2 := by
  sorry

end OMA.S_oeis_a005555
