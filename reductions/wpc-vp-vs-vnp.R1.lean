import OMAStatements.S_wpc_vp_vs_vnp
import Mathlib

/-! Directed Hamiltonian cycles, including the one-vertex loop.
Family adapted from OpenAI math, lean/OAI/Computability/VPVNP/Hamiltonian.lean,
3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0). The two obligations
separate Boolean verification from an exact arithmetic circuit lower bound. -/
namespace OMA.R_wpc_vp_vs_vnp_R1
open OMA.S_wpc_vp_vs_vnp
open scoped Classical

def H1 : Prop := ∀ (F : Type) [Field F],
  IsVNP (σ := fun n => Fin n × Fin n) (fun n => (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => 0 < n ∧ π.IsCycleOn Set.univ),
      ∏ i, (MvPolynomial.X (i, π i) : MvPolynomial (Fin n × Fin n) F)))

def H2 : Prop := ∀ (F : Type) [Field F] (A d N : ℕ), ∃ n ≥ N, ∀ s ≤ A * n ^ d,
  ¬ Computes s (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => 0 < n ∧ π.IsCycleOn Set.univ),
      ∏ i, (MvPolynomial.X (i, π i) : MvPolynomial (Fin n × Fin n) F))

theorem main : H1 → H2 → type_of% @OMA.S_wpc_vp_vs_vnp.main := by
  intro h₁ h₂ F instF
  refine ⟨fun n => Fin n × Fin n, fun _ => inferInstance, _, h₁ F, ?_⟩
  rintro ⟨_, s, ⟨A, d, N, bound⟩, computes⟩
  obtain ⟨n, hn, hard⟩ := h₂ F A d N
  exact hard (s n) (bound n hn) (computes n)

end OMA.R_wpc_vp_vs_vnp_R1
