import Mathlib

/-!
# A136746: G.f.: (z^12+1-z^11-z^10+z^8-z^6+z^5-z^3+z)/((z+1)*(z-1)^2).

Source: https://oeis.org/A136746
Credit: @agchua

Comment line of A136746 (offset 0; entry by N. J. A. Sloane, Apr 07 2008), verbatim:
  _Simon Plouffe_ conjectured in 1992 that this is a g.f. for A003003 - it is not.
A003003 (offset 1): Size of the largest subset of the numbers [1...n] which doesn't contain a
4-term arithmetic progression. (A003003 records the same: the g.f. was conjectured by Simon
Plouffe in his 1992 dissertation, but is wrong.)

This file states the comment's assertion (that the g.f. is NOT a g.f. for A003003) as a
non-identity of formal power series over ℚ:
  (∑_{n ≥ 0} A003003(n+1) z^n) * ((z+1)(z-1)^2) ≠ z^12+1-z^11-z^10+z^8-z^6+z^5-z^3+z.
Since (z+1)(z-1)^2 has constant coefficient 1, it is a unit of ℚ[[z]], so the identity would say
exactly that the g.f. above expands to ∑ A003003(n+1) z^n, i.e. A136746(n) = A003003(n+1) for
all n ≥ 0; the assertion is that this fails. The shift by one is the alignment of the two
entries (both sequences begin 1, 2, 3, 3, 4, 5, 5, ...; A136746 has offset 0, A003003 has
offset 1), under which the series agrees with A003003 for the first 27 terms; it is the reading
under which Plouffe's claim had content (matching z^n with A003003(n) instead, the two differ
already at z^0).
Definition: A003003(n) is the largest card S over the subsets S of {1, ..., n} that contain no
four elements a, a+d, a+2d, a+3d with d > 0.
-/

namespace OMA.S_oeis_a136746

/-- The finite set S contains a 4-term arithmetic progression a, a+d, a+2d, a+3d with d > 0. -/
def HasAP4 (S : Finset ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ a ∈ S ∧ a + d ∈ S ∧ a + 2 * d ∈ S ∧ a + 3 * d ∈ S

open Classical in
/-- A003003(n): the size of the largest subset of {1, ..., n} that contains no 4-term arithmetic
progression. -/
noncomputable def A003003 (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).powerset.filter (fun S => ¬ HasAP4 S)).sup Finset.card

/-- Plouffe conjectured (1992) that (z^12+1-z^11-z^10+z^8-z^6+z^5-z^3+z)/((z+1)(z-1)^2) is a
g.f. for A003003, i.e. that its coefficient of z^n is A003003(n+1) for every n ≥ 0; it is not. -/
theorem main : PowerSeries.mk (fun n => (A003003 (n + 1) : ℚ)) *
      ((PowerSeries.X + 1) * (PowerSeries.X - 1) ^ 2) ≠
    PowerSeries.X ^ 12 + 1 - PowerSeries.X ^ 11 - PowerSeries.X ^ 10 + PowerSeries.X ^ 8 -
      PowerSeries.X ^ 6 + PowerSeries.X ^ 5 - PowerSeries.X ^ 3 + PowerSeries.X := by
  sorry

end OMA.S_oeis_a136746
