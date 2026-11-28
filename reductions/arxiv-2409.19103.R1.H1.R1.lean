import OMAReductions.R_arxiv_2409_19103_R1
import Mathlib

/- Adapted from OpenAI openai/math (Apache-2.0), commit
3344da59991ed94f9ba711217b29c1d760badfa6, NormalizedRigidityFromTrace.lean.
The field uses limits from inside G, not arbitrary values of g outside G.
On common singleton ends this is the unique matched target; point-to-disk
exceptions form a countable family, immaterial to scalar image measure. -/
namespace OMA.R_arxiv_2409_19103_R1_H1_R1
open Set Filter MeasureTheory OMA.S_arxiv_2409_19103
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
    (∀ i, ∀ᵐ y ∂volume, volume (T i y '' S i y) = 0) → ∀ p ∈ G, g p = p

def H2 : Prop :=
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
    ∀ i, ∀ᵐ y ∂volume, ¬ (S i y).Countable → volume (T i y '' S i y) = 0

def H3 : Prop :=
  ∀ (G : Set Sphere) (g : Sphere → Sphere),
    let L (i : Fin 2) (y x : ℝ) : Sphere := ((if i = 0 then Complex.mk x y else Complex.mk y x : ℂ) : Sphere)
    let S (i : Fin 2) (y : ℝ) : Set ℝ := {x | L i y x ∉ G ∧ connectedComponentIn Gᶜ (L i y x) = {L i y x}}
    let T (i : Fin 2) (y x : ℝ) :=
      let w := finiteCoord (limUnder (𝓝[G] (L i y x)) g)
      if i = 0 then w.re else w.im
    ∀ i y, (S i y).Countable → volume (T i y '' S i y) = 0

theorem main : H1 → H2 → H3 → OMA.R_arxiv_2409_19103_R1.H1 := by
  intro h₁ h₂ h₃ G g hG hi hg hf hn hW hr
  apply h₁ G g hG hi hg hf hn hW
  intro i
  filter_upwards [h₂ G g hG hi hg hf hn hW hr i] with y hy
  classical
  exact (em _).elim (h₃ G g i y) hy

end OMA.R_arxiv_2409_19103_R1_H1_R1
