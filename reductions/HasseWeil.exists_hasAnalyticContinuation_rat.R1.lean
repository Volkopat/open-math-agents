import FormalConjectures.Wikipedia.HasseWeil
import Mathlib.Analysis.Complex.Convex

/-! The identity principle extends agreement from a smaller half-plane. -/

open scoped Topology

namespace OMA.R_HasseWeil_exists_hasAnalyticContinuation_rat_R1

-- Analyticity on the half-plane of absolute convergence.
def H1 : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    AnalyticOnNhd ℂ E.LSeries {s | (3 / 2 : ℝ) < s.re}

-- An entire representative agreeing with the elliptic-curve series on Re s > 2.
def H2 : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic],
    ∃ L : ℂ → ℂ, (∀ z, AnalyticAt ℂ L z) ∧
      ∀ s : ℂ, 2 < s.re → L s = E.LSeries s

theorem main : H1 → H2 → type_of% @HasseWeil.exists_hasAnalyticContinuation_rat := by
  intro analyticSeries continuation E hE
  obtain ⟨L, hL, he⟩ := @continuation E hE
  refine ⟨L, hL, fun s hs => ?_⟩
  have hLn : AnalyticOnNhd ℂ L {z | (3 / 2 : ℝ) < z.re} := fun z _ => hL z
  have hnear : L =ᶠ[𝓝 (3 : ℂ)] E.LSeries := by
    have hmem : (3 : ℂ) ∈ {z : ℂ | (2 : ℝ) < z.re} := by norm_num
    exact ((isOpen_lt continuous_const Complex.continuous_re).eventually_mem hmem).mono
      fun z hz => he z hz
  exact hLn.eqOn_of_preconnected_of_eventuallyEq (@analyticSeries E hE)
    (convex_halfSpace_re_gt (3 / 2 : ℝ)).isPreconnected
    (show (3 : ℂ) ∈ {z : ℂ | (3 / 2 : ℝ) < z.re} by norm_num) hnear hs

end OMA.R_HasseWeil_exists_hasAnalyticContinuation_rat_R1
