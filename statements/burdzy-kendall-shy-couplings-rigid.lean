import Mathlib

/-!
# Are shy couplings of reflected Brownian motion necessarily rigid?

K. Burdzy and W. Kendall, Problem 7 in "My favorite open problems".
https://sites.math.washington.edu/~burdzy/open_mathjax.php
Credit: @pmaster

We specify normally reflected Brownian motion by its Neumann resolvent on
the full weak Sobolev space H¹(D). No smoothness of the boundary is assumed.
The test at positive deterministic times avoids choices of a representative
of a Sobolev function at the starting point.
-/

namespace OMA.S_burdzy_kendall_shy_couplings_rigid

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Paths (d : ℕ) := C(ℝ≥0, E d)

noncomputable instance pathMeasurable (d : ℕ) : MeasurableSpace (Paths d) :=
  borel (Paths d)

/-- Weak, square-integrable first derivatives of a real H¹ function on D. -/
def SobolevGrad {d : ℕ} (D : Set (E d)) (v : E d → ℝ)
    (a : Fin d → E d → ℝ) : Prop :=
  MemLp v 2 (volume.restrict D) ∧ ∀ i,
    MemLp (a i) 2 (volume.restrict D) ∧
    ∀ φ : E d → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ D →
      (∫ x in D, v x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        -(∫ x in D, a i x * φ x)

/-- The weak Neumann resolvent equation (λ − Δ/2)u = h. Testing against
all of H¹(D) imposes normal reflection. -/
def Resolvent {d : ℕ} (D : Set (E d)) (lam : ℝ) (h u : E d → ℝ) : Prop :=
  ∃ a : Fin d → E d → ℝ, SobolevGrad D u a ∧
    ∀ (v : E d → ℝ) (b : Fin d → E d → ℝ), SobolevGrad D v b →
      lam * (∫ x in D, u x * v x) +
        (1 / 2 : ℝ) * (∫ x in D, ∑ i, a i x * b i x) = ∫ x in D, h x * v x

abbrev Past (d : ℕ) (s : ℝ≥0) : MeasurableSpace (Paths d) :=
  ⨆ r : Set.Iic s, MeasurableSpace.comap (fun w : Paths d => w r.val) inferInstance

def BoundedReal {α : Type*} (g : α → ℝ) : Prop := ∃ M : ℝ, ∀ x, |g x| ≤ M

/-- Conditional future occupation integrals are the Neumann resolvent of
the current position. The Laplace transforms for all λ > 0 characterize the
Brownian transition semigroup. Each marginal uses its own past. -/
def ReflectedLaw {d : ℕ} (D : Set (E d)) (P : Measure (Paths d)) : Prop :=
  IsProbabilityMeasure P ∧
  (∀ᵐ w ∂P, ∀ t, w t ∈ closure D) ∧
  ∀ s : ℝ≥0, 0 < s →
    Measure.map (fun w : Paths d => w s) P ≪ volume.restrict D ∧
    ∀ (lam : ℝ), 0 < lam → ∀ (h u : E d → ℝ),
      Measurable h → BoundedReal h → Measurable u → BoundedReal u →
      Resolvent D lam h u → ∀ B : Set (Paths d), MeasurableSet[Past d s] B →
        (∫ w in B, (∫ t in Set.Ioi (0 : ℝ),
          Real.exp (-lam * t) * h (w (s + t.toNNReal))) ∂P) =
        ∫ w in B, u (w s) ∂P

/-- The two path marginals are reflected Brownian motions and the pair
remains a positive distance apart forever with positive probability. -/
def Shy {d : ℕ} (D : Set (E d)) (P : Measure (Paths d × Paths d)) : Prop :=
  IsProbabilityMeasure P ∧ ReflectedLaw D (Measure.map Prod.fst P) ∧
    ReflectedLaw D (Measure.map Prod.snd P) ∧ ∃ ε : ℝ, 0 < ε ∧
      0 < P {p | ∀ t : ℝ≥0, ε ≤ dist (p.1 t) (p.2 t)}

theorem main : ∀ (d : ℕ), 2 ≤ d → ∀ D : Set (E d),
    IsOpen D → IsConnected D → Bornology.IsBounded D →
    (∃ P : Measure (Paths d × Paths d), Shy D P) →
    ∃ (P : Measure (Paths d × Paths d)) (f : E d → E d),
      Shy D P ∧ ∀ᵐ p ∂P, ∀ t : ℝ≥0, p.2 t = f (p.1 t) := by
  sorry

end OMA.S_burdzy_kendall_shy_couplings_rigid
