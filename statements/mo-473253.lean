import Mathlib

/-!
# One- and two-coordinate approximation in weighted Lᵖ

Source: shawn532, [Dependence and L² projections of functions](https://mathoverflow.net/questions/473253)
(2024, CC BY-SA 4.0). Credit: @connoranderson (agent: Codex).

The weight is the probability density 1/2 on [0,1]² × [−1,1] and zero
outside. The power loss is the pth power of the weighted Lᵖ error.
`Admissible` requires a globally Lipschitz, nonnegative function. Such
functions are bounded on the box and belong to all the weighted spaces
under consideration. The product metric on ℝ³ is equivalent to the
Euclidean metric for the Lipschitz condition.

The source compares the first-coordinate and first-two-coordinate
predictor classes. Its last displayed strict inequality repeats the
same class twice; we use the comparison described immediately before
it. The target function genuinely varies with either of the first two
coordinates when the others are fixed in the interior of the box.
Both minima are attained, with an exact value for every real exponent p > 0, including the quasi-norm range.
The final clauses give the same optimal essential-uniform error in
both predictor classes.
-/

open MeasureTheory Set
open scoped NNReal ENNReal Interval
namespace OMA.S_mo_473253

abbrev Pair := ℝ × ℝ
abbrev Point := Pair × ℝ
abbrev I := Icc (0 : ℝ) 1
abbrev J := Icc (-1 : ℝ) 1
abbrev box := (I ×ˢ I) ×ˢ J

def Admissible {E : Type*} [PseudoMetricSpace E] (f : E → ℝ) : Prop :=
  (∃ K : ℝ≥0, LipschitzWith K f) ∧ ∀ x, 0 ≤ f x

noncomputable def loss (p : ℝ) (f : Point → ℝ) (g : Pair → ℝ) :=
  (∫ v in box, |f v - g v.1| ^ p) / 2

def oneLosses (p : ℝ) (f : Point → ℝ) : Set ℝ :=
  {r | ∃ g : ℝ → ℝ, Admissible g ∧ r = loss p f (fun v => g v.1)}

def twoLosses (p : ℝ) (f : Point → ℝ) : Set ℝ :=
  {r | ∃ g : Pair → ℝ, Admissible g ∧ r = loss p f g}

def varies (f : Point → ℝ) : Prop :=
  (∃ x ∈ Ioo (0:ℝ) 1, ∃ x' ∈ Ioo (0:ℝ) 1, ∃ y ∈ Ioo (0:ℝ) 1, ∃ z ∈ Ioo (-1:ℝ) 1,
    f ((x,y),z) ≠ f ((x',y),z)) ∧
  (∃ x ∈ Ioo (0:ℝ) 1, ∃ y ∈ Ioo (0:ℝ) 1, ∃ y' ∈ Ioo (0:ℝ) 1, ∃ z ∈ Ioo (-1:ℝ) 1,
    f ((x,y),z) ≠ f ((x,y'),z))

theorem main :
    ∃ f : Point → ℝ, Admissible f ∧ varies f ∧
    (∀ p : ℝ, 0 < p →
      IsLeast (oneLosses p f) (1/(p+1)^2) ∧ IsLeast (twoLosses p f) (1/(p+1)^2)) ∧
    (∃ h : ℝ → ℝ, Admissible h ∧ ∀ v ∈ box, |f v-h v.1.1| ≤ 1) ∧
    (∀ (g : Pair → ℝ), Admissible g → ∀ r : ℝ,
      (∀ᵐ v ∂(volume : Measure Point).restrict box, |f v-g v.1| ≤ r) → 1 ≤ r) := by
  sorry

end OMA.S_mo_473253
