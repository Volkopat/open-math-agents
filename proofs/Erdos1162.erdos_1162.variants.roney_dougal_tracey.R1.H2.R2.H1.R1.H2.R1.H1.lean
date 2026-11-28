import OMAReductions.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1_H2_R1

/-!
Proof of `OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1_H2_R1.H1`.

In a finite nilpotent group every Sylow subgroup is normal, so `P p` is the only Sylow
`p`-subgroup and contains every `p`-subgroup. Suppose `H ∩ P p = K ∩ P p` for every prime `p`.
Every `p`-subgroup of `H` then lies in `H ∩ P p`, hence in `K`. So `H ∩ K` contains a Sylow
`p`-subgroup of `H` for every prime `p`, its order is divisible by `|H|`, and `H ∩ K = H`.
By symmetry `H = K`.
-/

namespace OMAProof.NilpotentSylow

theorem le_of_comap_eq {G : Type} [Group G] [Finite G] [Group.IsNilpotent G]
    (P : (p : (Nat.card G).primeFactors) → Sylow p G) (H K : Subgroup G)
    (h : ∀ p, H.comap (P p).1.subtype = K.comap (P p).1.subtype) : H ≤ K := by
  have key : ∀ p : (Nat.card G).primeFactors, ∀ Q : Subgroup G, Q ≤ H →
      IsPGroup (p : ℕ) Q → Q ≤ K := by
    intro p Q hQH hQ x hx
    have : Fact (p : ℕ).Prime := ⟨Nat.prime_of_mem_primeFactors p.2⟩
    obtain ⟨S, hS⟩ := hQ.exists_le_sylow
    let u := Sylow.unique_of_normal (P p) inferInstance
    have hSP : S = P p := Subsingleton.elim _ _
    have hxP : x ∈ ((P p : Sylow (p : ℕ) G) : Subgroup G) := hSP ▸ hS hx
    have hmem : (⟨x, hxP⟩ : ((P p : Sylow (p : ℕ) G) : Subgroup G)) ∈
        H.comap (P p).1.subtype := hQH hx
    rw [h p] at hmem
    exact hmem
  have hLH : H ⊓ K ≤ H := inf_le_left
  suffices hc : Nat.card H ≤ Nat.card (H ⊓ K : Subgroup G) by
    have heq := Subgroup.eq_of_le_of_card_ge hLH hc
    rw [← heq]
    exact inf_le_right
  apply Nat.le_of_dvd Nat.card_pos
  rw [← Nat.factorization_prime_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne']
  intro q hq
  have : Fact q.Prime := ⟨hq⟩
  by_cases hqd : q ∣ Nat.card H
  · have hqG : q ∈ (Nat.card G).primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hq, hqd.trans (Subgroup.card_subgroup_dvd_card H),
        Nat.card_pos.ne'⟩
    obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow q H))
    have hQ'H : (Q : Subgroup H).map H.subtype ≤ H := by
      rintro _ ⟨y, -, rfl⟩
      exact y.2
    have hQ'p : IsPGroup q ((Q : Subgroup H).map H.subtype) := Q.isPGroup'.map H.subtype
    have hQ'K := key ⟨q, hqG⟩ _ hQ'H hQ'p
    have hle : (Q : Subgroup H).map H.subtype ≤ H ⊓ K := le_inf hQ'H hQ'K
    have hcard : Nat.card ((Q : Subgroup H).map H.subtype) =
        q ^ (Nat.card H).factorization q := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact Q.card_eq_multiplicity
    have hdvd : q ^ (Nat.card H).factorization q ∣ Nat.card (H ⊓ K : Subgroup G) :=
      hcard ▸ Subgroup.card_dvd_of_le hle
    exact (hq.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
  · rw [Nat.factorization_eq_zero_of_not_dvd hqd]
    exact Nat.zero_le _

end OMAProof.NilpotentSylow

open OMAProof.NilpotentSylow in
theorem OMA.solution :
    OMA.R_Erdos1162_erdos_1162_variants_roney_dougal_tracey_R1_H2_R2_H1_R1_H2_R1.H1 := by
  intro G _ _ hG P H K hHK
  exact le_antisymm (le_of_comap_eq P H K fun p => congrFun hHK p)
    (le_of_comap_eq P K H fun p => (congrFun hHK p).symm)
