import OMAReductions.R_wpc_vp_vs_vnp_R1_H2_R1
/-! Adapted from OpenAI math@3344da59991ed94f9ba711217b29c1d760badfa6, OAI/Computability/VPVNP/{UniversalMachine,PairedFamily,HamiltonianHardness,Separation}.lean, Apache-2.0. -/
namespace OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1
open OMA.S_wpc_vp_vs_vnp
open scoped Classical
def H1 : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] [Countable K]
    (p : Family K (fun n => Fin n × Bool)), IsVNP p → ∃ e M : ℕ,
    ∀ n ≥ M, ∃ m ≥ n, m ≤ n ^ e ∧ ∀ s, Computes s (∑ π ∈ Finset.univ.filter (fun π : Equiv.Perm (Fin m) => 0 < m ∧ π.IsCycleOn Set.univ),
      ∏ i, (MvPolynomial.X (i, π i) : MvPolynomial (Fin m × Fin m) K)) → Computes s (p n)
def H2 : Prop := ∀ (K : Type) [Field K] [IsAlgClosed K] [Countable K],
  ∃ p : Family K (fun n => Fin n × Bool), IsVNP p ∧ ∀ A d N : ℕ,
  ∃ n ≥ N, ∀ s ≤ A * n ^ d, ¬ Computes s (p n)
theorem main : H1 → H2 → OMA.R_wpc_vp_vs_vnp_R1_H2_R1.H2 := by
  intro transfer hard K _ _ _ A d N
  obtain ⟨p,hp,hpHard⟩ := hard K
  obtain ⟨e,M,trans⟩ := transfer K p hp
  obtain ⟨n,hn,h⟩ := hpHard A (e*d) (max M N)
  obtain ⟨m,hm,hm',t⟩ := trans n ((le_max_left ..).trans hn)
  refine ⟨m, ((le_max_right ..).trans hn).trans hm, fun s hs comp => h s ?_ (t s comp)⟩
  rw [pow_mul]
  exact hs.trans (Nat.mul_le_mul_left A (Nat.pow_le_pow_left hm' d))
end OMA.R_wpc_vp_vs_vnp_R1_H2_R1_H2_R1
