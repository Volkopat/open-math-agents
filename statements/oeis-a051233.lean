import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Finset.Prod

/-!
# Half-covered pixels in an inscribed disk

Sources: OEIS A051233 (Sean A. Irvine's conjecture, 2021-09-03) and A124623.
https://oeis.org/A051233 and https://oeis.org/A124623
Credit: @LDJAI

Double all distances and place the disk center at the origin. The disk then has
radius n, and pixel i has center coordinate 2i+1-n. In coordinates local to
each pixel its area is 4, so the half-coverage threshold is 2.
-/

namespace OMA.S_oeis_a051233

open Set MeasureTheory Filter
open scoped Topology

def offset (n i : ℕ) : ℤ := 2 * (i : ℤ) + 1 - n

/-- The portion of the doubled pixel covered by the disk, in local coordinates. -/
def covered (r a b : ℝ) : Set (ℝ × ℝ) :=
  (Icc (-1) 1 ×ˢ Icc (-1) 1) ∩
    {p | (a + p.1) ^ 2 + (b + p.2) ^ 2 ≤ r ^ 2}

noncomputable def halfCount (n : ℕ) : ℕ := by
  classical
  exact (((Finset.range n) ×ˢ (Finset.range n)).filter fun ij =>
    2 ≤ volume (covered n (offset n ij.1) (offset n ij.2))).card

def centerCount (n : ℕ) : ℕ :=
  (((Finset.range n) ×ˢ (Finset.range n)).filter fun ij =>
    (offset n ij.1) ^ 2 + (offset n ij.2) ^ 2 < (n : ℤ) ^ 2).card

/-- Interpret "equality in most cases" as natural density one among positive
grid sizes. The numerator counts exceptions in the interval from 1 to N. -/
theorem main :
    (∀ n : ℕ, 0 < n → halfCount n ≤ centerCount n) ∧
    Tendsto (fun N : ℕ =>
      ((((Finset.range N).filter fun k => halfCount (k+1) ≠ centerCount (k+1)).card : ℝ) / N))
      atTop (𝓝 0) := by
  sorry

end OMA.S_oeis_a051233
