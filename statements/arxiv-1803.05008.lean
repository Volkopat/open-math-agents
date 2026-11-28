import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Explicit tight bounds on the stably recoverable information for the inverse source problem

Source: https://arxiv.org/abs/1803.05008
Credit: @happycamper

Conjecture 1 of Mirza Karamehmedović. The comparison is between the least
index of a strictly decreasing tail of the angular singular values and the
least order whose first positive Bessel Y zero is at least k times the
source radius. The singular values use Lemma 1 and the Lommel integral.
-/

open MeasureTheory

namespace OMA.S_arxiv_1803_05008

/-- The integer-order Bessel function J, using NIST DLMF 10.9.2. -/
noncomputable def besselJ (m : ℕ) (x : ℝ) : ℝ :=
  (∫ θ in (0 : ℝ)..Real.pi, Real.cos (x * Real.sin θ - (m : ℝ) * θ)) / Real.pi

/-- The integer-order Bessel function Y for positive arguments, using NIST DLMF 10.9.7. -/
noncomputable def besselY (m : ℕ) (x : ℝ) : ℝ :=
  ((∫ θ in (0 : ℝ)..Real.pi, Real.sin (x * Real.sin θ - (m : ℝ) * θ)) -
    (∫ t in Set.Ioi (0 : ℝ),
      (Real.exp ((m : ℝ) * t) + (-1 : ℝ) ^ m * Real.exp (-(m : ℝ) * t)) *
        Real.exp (-(x * Real.sinh t)))) / Real.pi

/-- The first positive zero of the integer-order Bessel function Y. -/
noncomputable def firstPositiveYZero (m : ℕ) : ℝ :=
  sInf {x : ℝ | 0 < x ∧ besselY m x = 0}

/-- The angular singular value at order m in Lemma 1. The Lommel integral
rewrites the squared source factor as twice the integral below divided by
the squared dimensionless source radius. -/
noncomputable def angularSingularValue (k sourceRadius measurementRadius : ℝ)
    (m : ℕ) : ℝ :=
  Real.sqrt
    ((4 * measurementRadius * Real.pi ^ 2 / k ^ 2) *
      (besselJ m (k * measurementRadius) ^ 2 + besselY m (k * measurementRadius) ^ 2) *
      (∫ t in (0 : ℝ)..(k * sourceRadius), t * besselJ m t ^ 2))

/-- The candidate starting indices from the bandwidth definition in the paper. -/
def decreasingTailStarts (k sourceRadius measurementRadius : ℝ) : Set ℕ :=
  {m : ℕ | ∀ n : ℕ,
    angularSingularValue k sourceRadius measurementRadius (m + n + 1) <
      angularSingularValue k sourceRadius measurementRadius (m + n)}

/-- Conjecture 1, with real wavenumber and concentric source and measurement radii. -/
theorem main :
    ∀ k sourceRadius measurementRadius : ℝ,
      0 < k → 0 < sourceRadius → sourceRadius ≤ measurementRadius →
      ∃ bandwidth upperBound : ℕ,
        IsLeast (decreasingTailStarts k sourceRadius measurementRadius) bandwidth ∧
          IsLeast {m : ℕ | k * sourceRadius ≤ firstPositiveYZero m} upperBound ∧
            bandwidth ≤ upperBound := by
  sorry

end OMA.S_arxiv_1803_05008
