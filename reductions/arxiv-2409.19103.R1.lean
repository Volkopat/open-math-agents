import OMAStatements.S_arxiv_2409_19103
import Mathlib

/-!
Reduction of the removability ⇒ rigidity direction of the He–Schramm
conjecture (arXiv 2409.19103) to its normalized form, following the
architecture of OpenAI's openai/math (Apache-2.0, commit
3344da59991ed94f9ba711217b29c1d760badfa6,
OAI/Analysis/CircleDomains/Rigidity/RigidityNormalizationReduction.lean).

H1 is the normalized identity theorem: a conformal map of a circle domain
through infinity onto a circle domain, removable boundary, fixing infinity
with principal expansion z + O(1/z), is the identity.
H2 is the Möbius normalization: any instance of the target can be moved by
Möbius maps A, B (source and target side) into the normalized situation.
-/

namespace OMA.R_arxiv_2409_19103_R1
open Set Filter OMA.S_arxiv_2409_19103
open scoped OnePoint

/-- Normalized rigidity: the principal normalized conformal map is the identity. -/
def H1 : Prop :=
  ∀ (G : Set OMA.S_arxiv_2409_19103.Sphere)
    (g : OMA.S_arxiv_2409_19103.Sphere → OMA.S_arxiv_2409_19103.Sphere),
    OMA.S_arxiv_2409_19103.IsCircleDomain G → ∞ ∈ G →
    OMA.S_arxiv_2409_19103.IsConformalEquivalence g G (g '' G) → g ∞ = ∞ →
    (fun z : ℂ => OMA.S_arxiv_2409_19103.finiteCoord (g (z : OMA.S_arxiv_2409_19103.Sphere)) - z)
      =O[Bornology.cobounded ℂ] (fun z : ℂ => z⁻¹) →
    OMA.S_arxiv_2409_19103.IsCircleDomain (g '' G) →
    OMA.S_arxiv_2409_19103.IsConformallyRemovable (frontier G) →
    ∀ p ∈ G, g p = p

/-- Möbius normalization of a conformal equivalence between circle domains. -/
def H2 : Prop :=
  ∀ (U V : Set OMA.S_arxiv_2409_19103.Sphere)
    (f : OMA.S_arxiv_2409_19103.Sphere → OMA.S_arxiv_2409_19103.Sphere),
    OMA.S_arxiv_2409_19103.IsCircleDomain U → OMA.S_arxiv_2409_19103.IsCircleDomain V →
    OMA.S_arxiv_2409_19103.IsConformallyRemovable (frontier U) →
    OMA.S_arxiv_2409_19103.IsConformalEquivalence f U V →
    ∃ A B : OMA.S_arxiv_2409_19103.Mobius,
      OMA.S_arxiv_2409_19103.IsCircleDomain ((fun p => A • p) '' U) ∧
      ∞ ∈ (fun p => A • p) '' U ∧
      OMA.S_arxiv_2409_19103.IsConformalEquivalence (fun p => B • f (A⁻¹ • p))
        ((fun p => A • p) '' U) ((fun p => B • f (A⁻¹ • p)) '' ((fun p => A • p) '' U)) ∧
      B • f (A⁻¹ • ∞) = ∞ ∧
      (fun z : ℂ => OMA.S_arxiv_2409_19103.finiteCoord
          (B • f (A⁻¹ • (z : OMA.S_arxiv_2409_19103.Sphere))) - z)
        =O[Bornology.cobounded ℂ] (fun z : ℂ => z⁻¹) ∧
      OMA.S_arxiv_2409_19103.IsCircleDomain
        ((fun p => B • f (A⁻¹ • p)) '' ((fun p => A • p) '' U)) ∧
      OMA.S_arxiv_2409_19103.IsConformallyRemovable (frontier ((fun p => A • p) '' U))

theorem main : H1 → H2 → type_of% @OMA.S_arxiv_2409_19103.main := by
  intro h1 h2 U V f hU hV hrem hf
  obtain ⟨A, B, hG, hinf, hg, hfix, hnorm, hW, hremG⟩ := h2 U V f hU hV hrem hf
  have hid := h1 _ _ hG hinf hg hfix hnorm hW hremG
  refine ⟨B⁻¹ * A, fun p hp => ?_⟩
  have h := hid (A • p) ⟨p, hp, rfl⟩
  simp only [inv_smul_smul] at h
  rw [mul_smul, ← h, inv_smul_smul]

end OMA.R_arxiv_2409_19103_R1
