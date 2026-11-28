import Mathlib

/-!
# Hausdorff limits of linear sections of a seminorm unit ball

Source: Sean, https://mathoverflow.net/questions/420618 (CC BY-SA).
Credit: @connoranderson. In real ℓ¹ the lower semicontinuous weighted supremum
seminorm has a compact unit ball, so its images in all Banach quotients are
compact as well. The sections by tilted lines tend to a proper subsegment of
the unit-ball section by the closed span of their limit.
-/
namespace OMA.S_mo_420618
open Set Metric Filter
open scoped Topology ENNReal
abbrev E := lp (fun _ : ℕ => ℝ) 1
noncomputable def weight (j : ℕ) : ℝ := (1/2:ℝ)^j
noncomputable def gauge (x : E) : ℝ≥0∞ := ⨆ j : ℕ, ENNReal.ofReal ((2:ℝ)^j*|x j|)
def unitBall : Set E := {x | gauge x ≤ 1}
noncomputable def axis (j : ℕ) : E := lp.single 1 j (1:ℝ)
noncomputable def tilt (n : ℕ) : E := axis 0 + (2*weight (n+1)) • axis (n+1)
noncomputable def line (n : ℕ) : Submodule ℝ E := Submodule.span ℝ {tilt n}
noncomputable def limitSet : Set E := (fun r : ℝ => r • axis 0) '' Icc (-1/2) (1/2)

theorem main :
    (gauge 0=0 ∧ (∀ x y : E, gauge (x+y) ≤ gauge x+gauge y) ∧
      (∀ (r : ℝ) (x : E), gauge (r • x)=ENNReal.ofReal |r| * gauge x)) ∧
    LowerSemicontinuous gauge ∧ Dense {x : E | gauge x < ⊤} ∧
    IsCompact unitBall ∧ Convex ℝ unitBall ∧ Balanced ℝ unitBall ∧
    (∀ n, IsClosed (line n : Set E) ∧
      (Submodule.span ℝ ((line n : Set E) ∩ unitBall)).topologicalClosure=line n) ∧
    IsCompact limitSet ∧ limitSet ⊆ unitBall ∧
    Tendsto (fun n => hausdorffDist ((line n : Set E) ∩ unitBall) limitSet) atTop (𝓝 0) ∧
    axis 0 ∈ unitBall ∩ ((Submodule.span ℝ limitSet).topologicalClosure : Set E) ∧
    axis 0 ∉ limitSet := by
  sorry
end OMA.S_mo_420618
