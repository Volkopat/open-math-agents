import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Boundedness of a fixed interior column of the Szegő kernel
Source: https://mathoverflow.net/questions/424812 (Naruto).
Hardy-space convention: Jiří Lebl, Tasty Bits of Several Complex Variables, §5.3.
Credit: @Rob1Ham

Use surface measure on the whole topological boundary. The Hardy space is the
L² closure of the boundary traces of functions holomorphic in the domain and
continuous on its closure. The kernel is specified by point evaluation on
this dense class. A fixed positive rescaling of surface measure only rescales
the kernel and leaves the boundedness question invariant.
-/

namespace OMA.S_mo_424812

open MeasureTheory
open scoped ComplexConjugate ContDiff

abbrev Space (n : ℕ) := EuclideanSpace ℂ (Fin n)

/-- A local real defining function with nonzero differential at each boundary point. -/
def smoothDomain {n : ℕ} (Ω : Set (Space n)) : Prop :=
  IsOpen Ω ∧ IsConnected Ω ∧ Bornology.IsBounded Ω ∧
    ∀ p ∈ frontier Ω, ∃ U : Set (Space n), IsOpen U ∧ p ∈ U ∧
      ∃ ρ : Space n → ℝ, ContDiffOn ℝ ∞ ρ U ∧ ρ p = 0 ∧ fderiv ℝ ρ p ≠ 0 ∧
        ∀ x ∈ U, (x ∈ Ω ↔ ρ x < 0)

noncomputable def surface {n : ℕ} (Ω : Set (Space n)) : Measure (Space n) :=
  (Measure.hausdorffMeasure ((2 * n - 1 : ℕ) : ℝ)).restrict (frontier Ω)

def testFunction {n : ℕ} (Ω : Set (Space n)) (f : Space n → ℂ) : Prop :=
  DifferentiableOn ℂ f Ω ∧ ContinuousOn f (closure Ω)

/-- Boundary values use L²(surface), modulo almost-everywhere equality. -/
noncomputable def hardy {n : ℕ} (Ω : Set (Space n)) : Set (Lp ℂ 2 (surface Ω)) :=
  closure {v | ∃ f : Space n → ℂ, testFunction Ω f ∧
    ∃ hf : MemLp f 2 (surface Ω), v = hf.toLp f}

/-- A Hardy vector representing evaluation at w on the dense test functions. -/
def evaluatesAt {n : ℕ} (Ω : Set (Space n)) (w : Space n)
    (k : Lp ℂ 2 (surface Ω)) : Prop :=
  k ∈ hardy Ω ∧ ∀ f : Space n → ℂ, testFunction Ω f →
    (∫ x, f x * conj (k x) ∂(surface Ω)) = f w

/-- The interior kernel S(z,w) is the pairing of the two evaluation vectors. -/
theorem main :
    ∀ (n : ℕ), 0 < n → ∀ Ω : Set (Space n), smoothDomain Ω →
      ∀ k : Space n → Lp ℂ 2 (surface Ω), (∀ w ∈ Ω, evaluatesAt Ω w (k w)) →
        ∀ w ∈ Ω, ∃ C : ℝ, ∀ z ∈ Ω,
          ‖∫ x, k w x * conj (k z x) ∂(surface Ω)‖ ≤ C := by
  sorry

end OMA.S_mo_424812
