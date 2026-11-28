import OMAReductions.R_arxiv_2409_19103_R1_H1_R1
import Mathlib
/- Adapted from OpenAI openai/math, Apache-2.0, commit 3344da59991ed94f9ba711217b29c1d760badfa6. Uses TraceCompression, NullImage, LocalNullImage, TraceIntervalPayment and TraceIntegralNull. -/
namespace OMA.R_arxiv_2409_19103_R1_H1_R1_H2_R1
open Set Function Filter MeasureTheory Metric
open scoped Topology OnePoint
open OMA.S_arxiv_2409_19103

def H1 : Prop :=
  ∀ (G : Set Sphere) (g : Sphere → Sphere),
    IsCircleDomain G → ∞ ∈ G → IsConformalEquivalence g G (g '' G) → g ∞ = ∞ →
    (fun z : ℂ => finiteCoord (g (z : Sphere)) - z) =O[Bornology.cobounded ℂ] (fun z : ℂ => z⁻¹) →
    IsCircleDomain (g '' G) →
    IsConformallyRemovable (frontier G) →
    let L (i : Fin 2) (y x : ℝ) : Sphere := ((if i = 0 then Complex.mk x y else Complex.mk y x : ℂ) : Sphere)
    let S (i : Fin 2) (y : ℝ) : Set ℝ := {x | L i y x ∉ G ∧ connectedComponentIn Gᶜ (L i y x) = {L i y x}}
    let T (i : Fin 2) (y x : ℝ) :=
      let w := finiteCoord (limUnder (𝓝[G] (L i y x)) g)
      if i = 0 then w.re else w.im
    ∀ i, ∀ᵐ y ∂volume, ¬ (S i y).Countable → ∃ (C : Set ℝ) (E : ℕ → Set ℝ), ((S i y) \ C).Countable ∧ volume C = 0 ∧
      (∀ n, MeasurableSet (E n)) ∧ Tendsto (fun n => volume (E n)) atTop (𝓝 0) ∧
      let b := T i y
      let K (n : ℕ) (u : ℝ) := ∫ s in (0:ℝ)..u, (E n)ᶜ.indicator (fun _ => (1:ℝ)) s
      ∀ n x, x ∈ C → ∃ V : Set ℝ, IsOpen V ∧ x ∈ V ∧ ∃ q : ℝ → ℝ,
        Integrable q volume ∧ (∀ᵐ t ∂volume, 0 ≤ q t) ∧
        ∀ u ∈ C ∩ V, ∀ v ∈ C ∩ V, u ≤ v → Icc u v ⊆ V →
          |K n (b v) - K n (b u)| ≤ ∫ t in Icc u v, q t

def H2 : Prop :=
  ∀ (C : Set ℝ) (b : ℝ → ℝ) (E : ℕ → Set ℝ), volume C = 0 →
    (∀ n, MeasurableSet (E n)) → Tendsto (fun n => volume (E n)) atTop (𝓝 0) →
    (let K (n : ℕ) (u : ℝ) := ∫ s in (0:ℝ)..u, (E n)ᶜ.indicator (fun _ => (1:ℝ)) s
      ∀ n x, x ∈ C → ∃ V : Set ℝ, IsOpen V ∧ x ∈ V ∧ ∃ q : ℝ → ℝ,
        Integrable q volume ∧ (∀ᵐ t ∂volume, 0 ≤ q t) ∧
        ∀ u ∈ C ∩ V, ∀ v ∈ C ∩ V, u ≤ v → Icc u v ⊆ V →
          |K n (b v) - K n (b u)| ≤ ∫ t in Icc u v, q t) → volume (b '' C) = 0

theorem main : H1 → H2 → OMA.R_arxiv_2409_19103_R1_H1_R1.H2 := by
  intro hw h G g hG hi hg hf hn hW hr L S T i
  filter_upwards [hw G g hG hi hg hf hn hW hr i] with y hy
  intro hu
  obtain ⟨C,E,hc,hC,hE,ht,hp⟩ := hy hu
  apply measure_mono_null _ (measure_union_null (h C (T i y) E hC hE ht hp) ((hc.image (T i y)).measure_zero volume))
  rintro _ ⟨x,hx,rfl⟩
  by_cases hxc : x ∈ C
  · exact Or.inl ⟨x,hxc,rfl⟩
  · exact Or.inr ⟨x,⟨hx,hxc⟩,rfl⟩
end OMA.R_arxiv_2409_19103_R1_H1_R1_H2_R1
