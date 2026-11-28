import FormalConjectures.ErdosProblems.«352»
import Mathlib

/-! Reduction by invariant mass. H1 is the outstanding absolute-volume estimate
for universally mean-null triangle-avoiders with gaps in, or no bounded interval for, their vertical projection. H3 handles full interval projections. The companion proof establishes
H2 for sets of positive mass with no measurability assumption. -/
open Affine EuclideanGeometry
open scoped ProbabilityTheory

namespace OMA.R_Erdos352_erdos_352_R1

def H1 : Prop :=
  ∃ c > (0 : ℝ), ∀ A : Set ℝ², MeasurableSet A →
    ¬ (let bd := fun f : ℝ × ℝ → ℝ => ∃ C : ℝ, ∀ x, |f x| ≤ C
      ∃ m : (ℝ × ℝ → ℝ) → ℝ,
        (∀ a : ℝ, m (fun _ => a) = a) ∧
        (∀ f g, bd f → bd g → m (fun x => f x + g x) = m f + m g) ∧
        (∀ (a : ℝ) f, bd f → m (fun x => a * f x) = a * m f) ∧
        (∀ f g, bd f → bd g → (∀ x, f x ≤ g x) → m f ≤ m g) ∧
        (∀ u v f, bd f → m (fun x => f (x.1 + u, x.2 + v)) = m f) ∧
        0 < m (fun x => A.indicator (fun _ => (1 : ℝ)) (WithLp.toLp 2 ![x.1,x.2]))) →
    ¬ (∃ lo hi : ℝ, lo < hi ∧
      (∀ p ∈ A, p 1 ∈ Set.Icc lo hi) ∧
      ∀ y ∈ Set.Ioo lo hi, ∃ x : ℝ, WithLp.toLp 2 ![x,y] ∈ A) →
    ¬ (∃ t : Affine.Triangle ℝ ℝ², (∀ i : Fin 3, t.points i ∈ A) ∧
        triangle_area (t.points 0) (t.points 1) (t.points 2) = 1) → ℙ A < c.toEReal

def H2 : Prop :=
  ∀ A : Set ℝ², (let bd := fun f : ℝ × ℝ → ℝ => ∃ C : ℝ, ∀ x, |f x| ≤ C
      ∃ m : (ℝ × ℝ → ℝ) → ℝ,
        (∀ a : ℝ, m (fun _ => a) = a) ∧
        (∀ f g, bd f → bd g → m (fun x => f x + g x) = m f + m g) ∧
        (∀ (a : ℝ) f, bd f → m (fun x => a * f x) = a * m f) ∧
        (∀ f g, bd f → bd g → (∀ x, f x ≤ g x) → m f ≤ m g) ∧
        (∀ u v f, bd f → m (fun x => f (x.1 + u, x.2 + v)) = m f) ∧
        0 < m (fun x => A.indicator (fun _ => (1 : ℝ)) (WithLp.toLp 2 ![x.1,x.2]))) →
    ∀ a : ℝ, 0 < a → ∃ t : Affine.Triangle ℝ ℝ², (∀ i : Fin 3, t.points i ∈ A) ∧
        triangle_area (t.points 0) (t.points 1) (t.points 2) = a

def H3 : Prop :=
  ∀ A : Set ℝ², MeasurableSet A → (∃ lo hi : ℝ, lo < hi ∧
      (∀ p ∈ A, p 1 ∈ Set.Icc lo hi) ∧
      ∀ y ∈ Set.Ioo lo hi, ∃ x : ℝ, WithLp.toLp 2 ![x,y] ∈ A) →
    4 < ℙ A → ∃ t : Affine.Triangle ℝ ℝ², (∀ i : Fin 3, t.points i ∈ A) ∧
        triangle_area (t.points 0) (t.points 1) (t.points 2) = 1

theorem main : H1 → H2 → H3 → type_of% @Erdos352.erdos_352 := by
  classical
  intro h1 h2 h3
  obtain ⟨c, hc, bound⟩ := h1
  refine ⟨max c 5, hc.trans_le (le_max_left _ _), ?_⟩
  intro A measurable large
  by_contra avoids
  have lc : (c : EReal) ≤ (ℙ A : EReal) :=
    (EReal.coe_le_coe_iff.mpr (le_max_left c 5)).trans large
  apply (not_lt_of_ge lc)
  apply bound A measurable _ _ avoids
  · intro positive
    exact avoids (h2 A positive 1 zero_lt_one)
  · intro proj
    apply avoids
    apply h3 A measurable proj
    apply EReal.coe_ennreal_lt_coe_ennreal_iff.mp
    have lt : ((4 : ℝ) : EReal) < (ℙ A : EReal) :=
      (EReal.coe_lt_coe_iff.mpr (lt_of_lt_of_le (by norm_num : (4:ℝ)<5) (le_max_right c 5))).trans_le large
    have eq : (4 : ENNReal) = ENNReal.ofReal (4:ℝ) := by norm_num
    rw [eq, EReal.coe_ennreal_ofReal]
    simpa only [max_eq_left (by norm_num : (0 : ℝ) ≤ 4)] using lt

end OMA.R_Erdos352_erdos_352_R1
