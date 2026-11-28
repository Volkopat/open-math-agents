import OMAReductions.R_wpc_vp_vs_vnp_R1

/-! Section 1 of "VP and VNP differ over every field" (OpenAI math,
3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0): a lower bound for the directed
Hamiltonian-cycle polynomial needs only countable algebraically closed fields, because an
exact circuit over any field can be relabeled, gate for gate, over such a field. -/
namespace OMA.R_wpc_vp_vs_vnp_R1_H2_R1
open OMA.S_wpc_vp_vs_vnp
open scoped Classical

def H1 : Prop := ∀ (F : Type) [Field F], ∃ (K : Type) (_ : Field K), IsAlgClosed K ∧ Countable K ∧
  ∀ n s : ℕ, Computes s (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => 0 < n ∧ π.IsCycleOn Set.univ),
      ∏ i, (MvPolynomial.X (i, π i) : MvPolynomial (Fin n × Fin n) F)) →
    Computes s (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => 0 < n ∧ π.IsCycleOn Set.univ),
      ∏ i, (MvPolynomial.X (i, π i) : MvPolynomial (Fin n × Fin n) K))

def H2 : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] [Countable K] (A d N : ℕ), ∃ n ≥ N, ∀ s ≤ A * n ^ d,
  ¬ Computes s (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin n) => 0 < n ∧ π.IsCycleOn Set.univ),
      ∏ i, (MvPolynomial.X (i, π i) : MvPolynomial (Fin n × Fin n) K))

theorem main : H1 → H2 → OMA.R_wpc_vp_vs_vnp_R1.H2 := by
  intro h₁ h₂ F _ A d N
  obtain ⟨K, _, _, _, transfer⟩ := h₁ F
  obtain ⟨n, hn, hard⟩ := h₂ K A d N
  exact ⟨n, hn, fun s hs computes => hard s hs (transfer n s computes)⟩

end OMA.R_wpc_vp_vs_vnp_R1_H2_R1
