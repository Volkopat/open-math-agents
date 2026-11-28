import OMAReductions.R_arxiv_2409_19103_R1_H1_R1
import Mathlib
/- Adapted from OpenAI openai/math, commit 3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0. -/
namespace OMA.R_arxiv_2409_19103_R1_H1_R1_H1_R1
open Set Function Metric Bornology Filter MeasureTheory OMA.S_arxiv_2409_19103
open scoped Topology OnePoint

def H1 : Prop :=
  ∀ (G : Set Sphere) (g : Sphere → Sphere),
    IsCircleDomain G → ∞ ∈ G → IsConformalEquivalence g G (g '' G) → g ∞ = ∞ →
    (fun z : ℂ => finiteCoord (g (z : Sphere)) - z) =O[Bornology.cobounded ℂ] (fun z : ℂ => z⁻¹) →
    IsCircleDomain (g '' G) →
    let L (i : Fin 2) (y x : ℝ) : Sphere := ((if i = 0 then Complex.mk x y else Complex.mk y x : ℂ) : Sphere)
    let S (i : Fin 2) (y : ℝ) : Set ℝ := {x | L i y x ∉ G ∧ connectedComponentIn Gᶜ (L i y x) = {L i y x}}
    let T (i : Fin 2) (y x : ℝ) :=
      let w := finiteCoord (limUnder (𝓝[G] (L i y x)) g)
      if i = 0 then w.re else w.im
    (∀ i, ∀ᵐ y ∂volume, volume (T i y '' S i y) = 0) →
    let D := {z : ℂ | (z : Sphere) ∈ G}
    let f := fun z : ℂ => finiteCoord (g (z : Sphere))
    ∃ (I : Type) (_ : Countable I) (a b : I → ℂ) (r s : I → ℝ) (R : ℝ), 0 < R ∧ IsOpen D ∧ IsPreconnected D ∧ DifferentiableOn ℂ f D ∧ InjOn f D ∧
    (closedBall 0 R)ᶜ ⊆ D ∧ (D ∩ ball 0 R).Nonempty ∧
    (∀ j, 0 ≤ r j) ∧ (∀ j, 0 ≤ s j) ∧
    Pairwise (Disjoint on fun j => ball (a j) (r j)) ∧ (∀ j, Disjoint D (ball (a j) (r j))) ∧
    (∀ j, ball (a j) (r j) ⊆ ball 0 R) ∧ Pairwise (Disjoint on fun j => ball (b j) (s j)) ∧
    (∀ j, Disjoint (f '' D) (ball (b j) (s j))) ∧
    ∀ S : Finset I, 2 * (Real.pi * R^2) ≤ 2 * (∫ z in D ∩ ball 0 R, ‖deriv f z‖) +
      2 * Real.pi * (∑ j ∈ S, r j * s j) + 16 * (∑' j : {j // j ∉ S}, r j * s j)

def H2 : Prop :=
  ∀ (f : ℂ → ℂ) (R : ℝ), 0 < R → DifferentiableOn ℂ f (closedBall 0 R)ᶜ →
    InjOn f (closedBall 0 R)ᶜ → (fun z : ℂ => f z - z) =O[cobounded ℂ] (fun z : ℂ => z⁻¹) →
    volume ((f '' (closedBall (0 : ℂ) R)ᶜ)ᶜ) ≤ ENNReal.ofReal (Real.pi * R^2)

def H3 : Prop :=
  ∀ (I : Type) [Countable I] (a b : I → ℂ) (r s : I → ℝ) (R : ℝ) (D : Set ℂ) (f : ℂ → ℂ),
    0 < R → (fun z : ℂ => f z - z) =O[cobounded ℂ] (fun z : ℂ => z⁻¹) → volume ((f '' (closedBall (0 : ℂ) R)ᶜ)ᶜ) ≤ ENNReal.ofReal (Real.pi * R^2) →
    (IsOpen D ∧ IsPreconnected D ∧ DifferentiableOn ℂ f D ∧ InjOn f D ∧
    (closedBall 0 R)ᶜ ⊆ D ∧ (D ∩ ball 0 R).Nonempty ∧
    (∀ j, 0 ≤ r j) ∧ (∀ j, 0 ≤ s j) ∧
    Pairwise (Disjoint on fun j => ball (a j) (r j)) ∧ (∀ j, Disjoint D (ball (a j) (r j))) ∧
    (∀ j, ball (a j) (r j) ⊆ ball 0 R) ∧ Pairwise (Disjoint on fun j => ball (b j) (s j)) ∧
    (∀ j, Disjoint (f '' D) (ball (b j) (s j))) ∧
    ∀ S : Finset I, 2 * (Real.pi * R^2) ≤ 2 * (∫ z in D ∩ ball 0 R, ‖deriv f z‖) +
      2 * Real.pi * (∑ j ∈ S, r j * s j) + 16 * (∑' j : {j // j ∉ S}, r j * s j)) → ∀ z ∈ D, f z = z

theorem main : H1 → H2 → H3 → OMA.R_arxiv_2409_19103_R1_H1_R1.H1 := by
  intro h₁ h₂ h₃ G g hG hi hg hf hn hW L S T ht
  obtain ⟨I, hI, a,b,r,s,R,hR,h⟩ := h₁ G g hG hi hg hf hn hW ht
  have he := h.2.2.2.2.1
  have ha := h₂ _ R hR (h.2.2.1.mono he) (h.2.2.2.1.mono he) hn
  have hid := h₃ I a b r s R _ _ hR hn ha h
  intro p hp
  cases p using OnePoint.rec with
  | infty => exact hf
  | coe z =>
    have hne : g (z : Sphere) ≠ ∞ := by
      obtain ⟨k, _, _, hk, _⟩ := hg.2.2
      intro hh
      exact OnePoint.coe_ne_infty z ((hk _ hp).symm.trans ((congrArg k (hh.trans hf.symm)).trans (hk _ hi)))
    cases e : g (z : Sphere) using OnePoint.rec with
    | infty => exact (hne e).elim
    | coe w =>
      have hh := hid z hp
      change finiteCoord (g (z : Sphere)) = z at hh
      rw [e] at hh
      exact congrArg _ hh

end OMA.R_arxiv_2409_19103_R1_H1_R1_H1_R1
