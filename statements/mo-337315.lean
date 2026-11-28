import Mathlib.Analysis.Convex.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.Compact

/-! Nandakumar R, MathOverflow 337315, main planar question (1).
For each nonempty compact convex region with interior and each positive number
of rectangles, can a common orientation attain the least sum of areas, with the long sides parallel?
The side-length comparison in transformed coordinates also admits squares.
Every pair of perpendicular side directions has a representative (1,t), |t| ≤ 1,
after swapping the axes and reversing one or both directions. In coordinates
X = x + t*y, Y = y - t*x, the area scaling factor is 1 + t². -/
namespace OMA.S_mo_337315

structure Rectangle where
  slope : ℝ
  left : ℝ
  right : ℝ
  bottom : ℝ
  top : ℝ

def Rectangle.valid (r : Rectangle) : Prop :=
  -1 ≤ r.slope ∧ r.slope ≤ 1 ∧ r.left < r.right ∧ r.bottom < r.top

def Rectangle.contains (r : Rectangle) (p : ℝ × ℝ) : Prop :=
  r.left ≤ p.1 + r.slope * p.2 ∧ p.1 + r.slope * p.2 ≤ r.right ∧
  r.bottom ≤ p.2 - r.slope * p.1 ∧ p.2 - r.slope * p.1 ≤ r.top

noncomputable def Rectangle.area (r : Rectangle) : ℝ :=
  (r.right-r.left)*(r.top-r.bottom)/(1+r.slope^2)

def Covers {n : ℕ} (C : Set (ℝ × ℝ)) (r : Fin n → Rectangle) : Prop :=
  (∀ i, (r i).valid) ∧ ∀ p ∈ C, ∃ i, (r i).contains p

theorem main : ∀ (C : Set (ℝ × ℝ)), IsCompact C → Convex ℝ C →
    (interior C).Nonempty → ∀ n : ℕ, 0 < n →
    ∃ r : Fin n → Rectangle, Covers C r ∧
      (∀ i j, (r i).slope = (r j).slope) ∧
      ((∀ i, (r i).right - (r i).left ≤ (r i).top - (r i).bottom) ∨
       (∀ i, (r i).top - (r i).bottom ≤ (r i).right - (r i).left)) ∧
      ∀ s : Fin n → Rectangle, Covers C s →
        (∑ i, (r i).area) ≤ ∑ i, (s i).area := by sorry

end OMA.S_mo_337315
