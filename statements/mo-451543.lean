import Mathlib

/-!
# The forward and reverse Jensen gaps of a martingale coupling

Guy Blanc asks when a martingale coupling satisfies
E[f(X) − f(E[X|Y])] ≤ E[f(Y) − f(X)], and suggests that convexity of
both f and its second derivative might suffice. The finite condition below
uses joint weights, row means x, distinct column values y, and column means z.
The condition is homogeneous in the joint weights, so their common
normalization is immaterial. The characterization covers all continuous
functions, including every convex real function. For square-integrable
variables the last equality identifies the precise gap for a quadratic.

Source: Guy Blanc, https://mathoverflow.net/questions/451543 (CC BY-SA 4.0).
Credit: @connoranderson (agent: Codex)
-/

namespace OMA.S_mo_451543
open MeasureTheory

def FiniteGap (f : ℝ → ℝ) : Prop :=
  ∀ (n m : ℕ) (w : Fin n → Fin m → ℝ) (x : Fin n → ℝ) (y z : Fin m → ℝ),
    (∀ i j, 0 ≤ w i j) → Function.Injective y →
    (∀ i, ∑ j, w i j*(y j-x i)=0) → (∀ j, ∑ i, w i j*(x i-z j)=0) →
    0 ≤ ∑ i, ∑ j, w i j*(f (y j)+f (z j)-2*f (x i))

def quadratic (a b c x : ℝ) := a*x^2+b*x+c

theorem main :
    (∀ f : ℝ → ℝ, Continuous f →
      (FiniteGap f ↔ ∃ a b c : ℝ, 0 ≤ a ∧ ∀ x, f x=quadratic a b c x)) ∧
    (let f := fun x : ℝ => (x-3/8)^4
     ConvexOn ℝ Set.univ f ∧ ConvexOn ℝ Set.univ (deriv (deriv f)) ∧ ¬FiniteGap f) ∧
    (∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X Y : Ω → ℝ) (a b c : ℝ), Measurable X → Measurable Y → MemLp X 2 P → MemLp Y 2 P →
      P[Y | MeasurableSpace.comap X (borel ℝ)] =ᵐ[P] X →
      let z := P[X | MeasurableSpace.comap Y (borel ℝ)]
      (∫ ω, (quadratic a b c (Y ω)+quadratic a b c (z ω)-2*quadratic a b c (X ω)) ∂P)
        = a * ∫ ω, (Y ω-z ω)^2 ∂P) := by
  sorry
end OMA.S_mo_451543
