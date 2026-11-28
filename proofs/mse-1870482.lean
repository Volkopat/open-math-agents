import OMAStatements.S_mse_1870482
import Mathlib

namespace NeonMSE1870482

open Subgroup

lemma card_sup_of_le_normalizer_of_disjoint {G : Type*} [Group G] [Finite G]
    {H K : Subgroup G} (hN : K ≤ Subgroup.normalizer (H : Set G)) (hD : Disjoint H K) :
    Nat.card (H ⊔ K : Subgroup G) = Nat.card H * Nat.card K := by
  let S : Subgroup G :=
    { carrier := {g | ∃ x ∈ H, ∃ y ∈ K, g = x * y}
      one_mem' := ⟨1, H.one_mem, 1, K.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨x₁, hx₁, y₁, hy₁, rfl⟩ ⟨x₂, hx₂, y₂, hy₂, rfl⟩
        have hconj : y₁ * x₂ * y₁⁻¹ ∈ H :=
          (Subgroup.mem_normalizer_iff.mp (hN hy₁) x₂).mp hx₂
        refine ⟨x₁ * (y₁ * x₂ * y₁⁻¹), H.mul_mem hx₁ hconj, y₁ * y₂, K.mul_mem hy₁ hy₂, ?_⟩
        group
      inv_mem' := by
        rintro _ ⟨x, hx, y, hy, rfl⟩
        have hy' : y⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
          (Subgroup.normalizer (H : Set G)).inv_mem (hN hy)
        have hconj : y⁻¹ * x⁻¹ * (y⁻¹)⁻¹ ∈ H :=
          (Subgroup.mem_normalizer_iff.mp hy' x⁻¹).mp (H.inv_mem hx)
        refine ⟨y⁻¹ * x⁻¹ * (y⁻¹)⁻¹, hconj, y⁻¹, K.inv_mem hy, ?_⟩
        group }
  have hS : H ⊔ K = S := by
    apply le_antisymm
    · refine sup_le ?_ ?_
      · intro x hx
        exact ⟨x, hx, 1, K.one_mem, by simp⟩
      · intro y hy
        exact ⟨1, H.one_mem, y, hy, by simp⟩
    · rintro _ ⟨x, hx, y, hy, rfl⟩
      exact Subgroup.mul_mem _ ((le_sup_left : H ≤ H ⊔ K) hx) ((le_sup_right : K ≤ H ⊔ K) hy)
  rw [hS]
  let f : H × K → S := fun p => ⟨p.1.1 * p.2.1, ⟨p.1.1, p.1.2, p.2.1, p.2.2, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨⟨x₁, hx₁⟩, ⟨y₁, hy₁⟩⟩ ⟨⟨x₂, hx₂⟩, ⟨y₂, hy₂⟩⟩ h
    have heq : x₁ * y₁ = x₂ * y₂ := congrArg Subtype.val h
    have h1 : x₂⁻¹ * x₁ = y₂ * y₁⁻¹ := by
      calc x₂⁻¹ * x₁ = x₂⁻¹ * (x₁ * y₁) * y₁⁻¹ := by group
        _ = x₂⁻¹ * (x₂ * y₂) * y₁⁻¹ := by rw [heq]
        _ = y₂ * y₁⁻¹ := by group
    have hmemH : x₂⁻¹ * x₁ ∈ H := H.mul_mem (H.inv_mem hx₂) hx₁
    have hmemK : x₂⁻¹ * x₁ ∈ K := h1 ▸ K.mul_mem hy₂ (K.inv_mem hy₁)
    have hbot : x₂⁻¹ * x₁ = 1 := (Subgroup.disjoint_def.mp hD) hmemH hmemK
    have hx : x₁ = x₂ := by
      calc x₁ = x₂ * (x₂⁻¹ * x₁) := by group
        _ = x₂ * 1 := by rw [hbot]
        _ = x₂ := by simp
    have hy : y₁ = y₂ := by
      rw [hx] at heq
      exact mul_left_cancel heq
    ext <;> simp [hx, hy]
  have hf_surj : Function.Surjective f := by
    rintro ⟨g, x, hx, y, hy, rfl⟩
    exact ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm

lemma sup_eq_top_of_card_eq {G : Type*} [Group G] [Finite G]
    {H K : Subgroup G} (hN : K ≤ Subgroup.normalizer (H : Set G)) (hD : Disjoint H K)
    (hcard : Nat.card H * Nat.card K = Nat.card G) : H ⊔ K = ⊤ := by
  have hc : Nat.card (H ⊔ K : Subgroup G) = Nat.card G := by
    rw [card_sup_of_le_normalizer_of_disjoint hN hD, hcard]
  exact Subgroup.eq_top_of_card_eq _ hc

lemma factor_prime_pow_mul_prime_pow {p q n a b : ℕ} (hp : p.Prime) (hq : q.Prime)
    (h : n ∣ p ^ a * q ^ b) : ∃ i j, i ≤ a ∧ j ≤ b ∧ n = p ^ i * q ^ j := by
  obtain ⟨m₁, m₂, hm₁, hm₂, rfl⟩ := Nat.dvd_mul.mp h
  obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).mp hm₁
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hq).mp hm₂
  exact ⟨i, j, hi, hj, rfl⟩

lemma sylow_card_of_card_eq_mul_pow {G : Type*} [Group G] [Finite G]
    {p q a b : ℕ} [Fact p.Prime] (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hG : Nat.card G = p ^ a * q ^ b) (P : Sylow p G) :
    Nat.card (P : Subgroup G) = p ^ a := by
  have h1 := P.card_eq_multiplicity
  rw [hG] at h1
  have hfac : (p ^ a * q ^ b).factorization p = a := by
    rw [Nat.factorization_mul (pow_ne_zero a hp.ne_zero) (pow_ne_zero b hq.ne_zero)]
    simp [hp.factorization_pow, Nat.Prime.factorization_pow hq, hpq]
  rw [hfac] at h1
  exact h1

lemma card_sylow_dvd_index_aux {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) : Nat.card (Sylow p G) ∣ (P : Subgroup G).index := by
  rw [P.card_eq_card_quotient_normalizer, ← Subgroup.index_eq_card]
  exact Subgroup.index_dvd_of_le Subgroup.le_normalizer

lemma isCoatom_of_index_eq_prime_aux {G : Type*} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime) {H : Subgroup G} (hidx : H.index = p) : IsCoatom H := by
  refine ⟨fun htop => ?_, fun K hHK => ?_⟩
  · rw [htop, Subgroup.index_top] at hidx
    exact hp.ne_one hidx.symm
  · have hdvd : K.index ∣ p := by
      rw [← hidx]
      exact Subgroup.index_dvd_of_le hHK.le
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
    · exact Subgroup.index_eq_one.mp h1
    · exfalso
      have hm1 := Subgroup.card_mul_index H
      have hm2 := Subgroup.card_mul_index K
      rw [hidx] at hm1
      rw [hp'] at hm2
      have hcard_eq : Nat.card H = Nat.card K := by
        have hppos : 0 < p := hp.pos
        nlinarith
      exact hHK.ne (Subgroup.eq_of_le_of_card_ge hHK.le (by omega))

lemma isCyclic_of_nilpotent_card_mul_pow {H : Type*} [Group H] [Finite H]
    [Group.IsNilpotent H] {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hH : Nat.card H = p ^ a * q ^ b)
    (hP : ∀ P : Sylow p H, IsCyclic P) (hQ : ∀ Q : Sylow q H, IsCyclic Q) :
    IsCyclic H := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p H))
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow q H))
  have hPnorm : (P : Subgroup H).Normal := inferInstance
  have hQnorm : (Q : Subgroup H).Normal := inferInstance
  have hPcard : Nat.card (P : Subgroup H) = p ^ a :=
    sylow_card_of_card_eq_mul_pow hp hq hpq hH P
  have hQcard : Nat.card (Q : Subgroup H) = q ^ b := by
    have hH' : Nat.card H = q ^ b * p ^ a := by rw [hH, mul_comm]
    exact sylow_card_of_card_eq_mul_pow hq hp hpq.symm hH' Q
  have hD : Disjoint (P : Subgroup H) (Q : Subgroup H) :=
    IsPGroup.disjoint_of_ne p q hpq (P : Subgroup H) (Q : Subgroup H) P.isPGroup' Q.isPGroup'
  have hcomm : ∀ (x : P) (y : Q), x.1 * y.1 = y.1 * x.1 := by
    intro x y
    have h1 : x.1 * y.1 * x.1⁻¹ * y.1⁻¹ ∈ (P : Subgroup H) := by
      have : y.1 * x.1⁻¹ * y.1⁻¹ ∈ (P : Subgroup H) := hPnorm.conj_mem _ (P.inv_mem x.2) y.1
      simpa [mul_assoc] using P.mul_mem x.2 this
    have h2 : x.1 * y.1 * x.1⁻¹ * y.1⁻¹ ∈ (Q : Subgroup H) := by
      have : x.1 * y.1 * x.1⁻¹ ∈ (Q : Subgroup H) := hQnorm.conj_mem _ y.2 x.1
      exact Q.mul_mem this (Q.inv_mem y.2)
    have hbot : x.1 * y.1 * x.1⁻¹ * y.1⁻¹ = 1 := (Subgroup.disjoint_def.mp hD) h1 h2
    calc x.1 * y.1 = (x.1 * y.1 * x.1⁻¹ * y.1⁻¹) * (y.1 * x.1) := by group
      _ = 1 * (y.1 * x.1) := by rw [hbot]
      _ = y.1 * x.1 := by simp
  let φ : P × Q →* H :=
    { toFun := fun xy => xy.1.1 * xy.2.1
      map_one' := by simp
      map_mul' := by
        rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
        change (x₁.1 * x₂.1) * (y₁.1 * y₂.1) = (x₁.1 * y₁.1) * (x₂.1 * y₂.1)
        calc x₁.1 * x₂.1 * (y₁.1 * y₂.1)
            = x₁.1 * (x₂.1 * y₁.1) * y₂.1 := by group
          _ = x₁.1 * (y₁.1 * x₂.1) * y₂.1 := by rw [hcomm x₂ y₁]
          _ = x₁.1 * y₁.1 * (x₂.1 * y₂.1) := by group }
  have hφ_inj : Function.Injective φ := by
    rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ h
    change x₁.1 * y₁.1 = x₂.1 * y₂.1 at h
    have h1 : x₂.1⁻¹ * x₁.1 = y₂.1 * y₁.1⁻¹ := by
      calc x₂.1⁻¹ * x₁.1 = x₂.1⁻¹ * (x₁.1 * y₁.1) * y₁.1⁻¹ := by group
        _ = x₂.1⁻¹ * (x₂.1 * y₂.1) * y₁.1⁻¹ := by rw [h]
        _ = y₂.1 * y₁.1⁻¹ := by group
    have hmP : x₂.1⁻¹ * x₁.1 ∈ (P : Subgroup H) := P.mul_mem (P.inv_mem x₂.2) x₁.2
    have hmQ : x₂.1⁻¹ * x₁.1 ∈ (Q : Subgroup H) := h1 ▸ Q.mul_mem y₂.2 (Q.inv_mem y₁.2)
    have hbot : x₂.1⁻¹ * x₁.1 = 1 := (Subgroup.disjoint_def.mp hD) hmP hmQ
    have hx : x₁ = x₂ := by
      ext
      calc x₁.1 = x₂.1 * (x₂.1⁻¹ * x₁.1) := by group
        _ = x₂.1 * 1 := by rw [hbot]
        _ = x₂.1 := by simp
    have hy : y₁ = y₂ := by
      ext
      rw [hx] at h
      exact mul_left_cancel h
    exact Prod.ext hx hy
  have hcard_eq : Nat.card (P × Q) = Nat.card H := by
    rw [Nat.card_prod, hPcard, hQcard, hH]
  have hφ_surj : Function.Surjective φ := by
    letI : Fintype (P × Q) := Fintype.ofFinite (P × Q)
    letI : Fintype H := Fintype.ofFinite H
    have hc' : Fintype.card (P × Q) = Fintype.card H := by
      simpa [Nat.card_eq_fintype_card] using hcard_eq
    exact (Finite.injective_iff_surjective_of_equiv (Fintype.equivOfCardEq hc')).mp hφ_inj
  let e : P × Q ≃* H := MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩
  rw [← e.isCyclic]
  rw [Group.isCyclic_prod_iff]
  refine ⟨hP P, hQ Q, ?_⟩
  rw [hPcard, hQcard]
  exact Nat.coprime_pow_primes a b hp hq hpq

lemma sylow_normal_card_twelve {H : Type*} [Group H] [Finite H]
    (hH : Nat.card H = 12) (hcardP : Nat.card (Sylow 3 H) = 4) :
    ∃ Q : Sylow 2 H, (Q : Subgroup H).Normal := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fintype H := Fintype.ofFinite H
  haveI : Fintype (Sylow 3 H) := Fintype.ofFinite (Sylow 3 H)
  obtain ⟨Q0⟩ := (inferInstance : Nonempty (Sylow 2 H))
  have hPc_all : ∀ P : Sylow 3 H, Nat.card (P : Subgroup H) = 3 := by
    intro P
    have hH' : Nat.card H = 3 ^ 1 * 2 ^ 2 := by rw [hH]; norm_num
    simpa using sylow_card_of_card_eq_mul_pow Nat.prime_three Nat.prime_two (by decide) hH' P
  have hQc_all : ∀ Q : Sylow 2 H, Nat.card (Q : Subgroup H) = 4 := by
    intro Q
    have hH' : Nat.card H = 2 ^ 2 * 3 ^ 1 := by rw [hH]; norm_num
    simpa using sylow_card_of_card_eq_mul_pow Nat.prime_two Nat.prime_three (by decide) hH' Q
  let f : Sylow 3 H → Finset H := fun P =>
    (Finset.univ.filter fun x : H => x ∈ (P : Subgroup H) ∧ x ≠ 1)
  have hf_card : ∀ P : Sylow 3 H, (f P).card = 2 := by
    intro P
    have hPc := hPc_all P
    have h1 : (Finset.univ.filter fun x : H => x ∈ (P : Subgroup H)).card = 3 := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact hPc
    have hmem1 : (1 : H) ∈ Finset.univ.filter (fun x : H => x ∈ (P : Subgroup H)) := by
      simp
    have hfeq : f P = (Finset.univ.filter fun x : H => x ∈ (P : Subgroup H)).erase 1 := by
      ext x
      simp [f, and_comm]
    rw [hfeq, Finset.card_erase_of_mem hmem1, h1]
  have hf_disj : Set.PairwiseDisjoint (Set.univ : Set (Sylow 3 H)) f := by
    intro P₁ _ P₂ _ hne
    change Disjoint (f P₁) (f P₂)
    rw [Finset.disjoint_left]
    intro x hx₁ hx₂
    simp only [f, Finset.mem_filter, Finset.mem_univ, true_and] at hx₁ hx₂
    have hmem : x ∈ (P₁ : Subgroup H) ⊓ (P₂ : Subgroup H) := ⟨hx₁.1, hx₂.1⟩
    have hPc₁ := hPc_all P₁
    have hPc₂ := hPc_all P₂
    have hle1 : (P₁ : Subgroup H) ⊓ (P₂ : Subgroup H) ≤ P₁ := inf_le_left
    have hdvd3 : Nat.card ((P₁ : Subgroup H) ⊓ (P₂ : Subgroup H) : Subgroup H) ∣ 3 := by
      have hd := Subgroup.card_dvd_of_le hle1
      rwa [hPc₁] at hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
    · have hbot : (P₁ : Subgroup H) ⊓ (P₂ : Subgroup H) = ⊥ :=
        Subgroup.eq_bot_of_card_eq _ h1
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hx₁.2 hmem
    · have heq1 : (P₁ : Subgroup H) ⊓ (P₂ : Subgroup H) = P₁ :=
        Subgroup.eq_of_le_of_card_ge hle1 (by omega)
      have hle12 : (P₁ : Subgroup H) ≤ P₂ := by
        rw [← heq1]; exact inf_le_right
      have heq12 : (P₁ : Subgroup H) = P₂ :=
        Subgroup.eq_of_le_of_card_ge hle12 (by omega)
      exact hne (Sylow.ext heq12)
  have hS3 : Fintype.card (Sylow 3 H) = 4 := by
    rw [← Nat.card_eq_fintype_card, hcardP]
  let U : Finset H := Finset.univ.biUnion f
  have hUcard : U.card = 8 := by
    rw [Finset.card_biUnion (fun a _ b _ hab => hf_disj trivial trivial hab)]
    simp [hf_card, hS3]
  have hQ_disj : ∀ Q : Sylow 2 H, ∀ x ∈ (Q : Subgroup H), x ∉ U := by
    intro Q x hx hU
    simp only [U, Finset.mem_biUnion, Finset.mem_univ, true_and] at hU
    obtain ⟨P, hxP⟩ := hU
    simp only [f, Finset.mem_filter, Finset.mem_univ, true_and] at hxP
    have hD : Disjoint (Q : Subgroup H) (P : Subgroup H) :=
      IsPGroup.disjoint_of_ne 2 3 (by decide) (Q : Subgroup H) (P : Subgroup H)
        Q.isPGroup' P.isPGroup'
    exact hxP.2 ((Subgroup.disjoint_def.mp hD) hx hxP.1)
  have hQ_eq : ∀ Q : Sylow 2 H, (Finset.univ.filter fun x : H => x ∈ (Q : Subgroup H)) = Uᶜ := by
    intro Q
    have hsub : (Finset.univ.filter fun x : H => x ∈ (Q : Subgroup H)) ⊆ Uᶜ := by
      intro x hx
      simp only [Finset.mem_compl]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact hQ_disj Q x hx
    have hc1 : (Finset.univ.filter fun x : H => x ∈ (Q : Subgroup H)).card = 4 := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact hQc_all Q
    have hc2 : Uᶜ.card = 4 := by
      rw [Finset.card_compl, ← Nat.card_eq_fintype_card, hH, hUcard]
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  have : Subsingleton (Sylow 2 H) := ⟨fun Q₁ Q₂ => by
    apply Sylow.ext
    ext x
    have h12 := (hQ_eq Q₁).trans (hQ_eq Q₂).symm
    have hx := Finset.ext_iff.mp h12 x
    simpa [Finset.mem_filter] using hx⟩
  exact ⟨Q0, Sylow.normal_of_subsingleton Q0⟩

lemma sylow_normal_of_card_pq2 {H : Type*} [Group H] [Finite H]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hH : Nat.card H = p * q ^ 2) :
    (∃ P : Sylow p H, (P : Subgroup H).Normal) ∨ (∃ Q : Sylow q H, (Q : Subgroup H).Normal) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨P0⟩ := (inferInstance : Nonempty (Sylow p H))
  obtain ⟨Q0⟩ := (inferInstance : Nonempty (Sylow q H))
  by_cases hlt : p < q
  · right
    have hQcard : Nat.card (Q0 : Subgroup H) = q ^ 2 := by
      have hH' : Nat.card H = q ^ 2 * p ^ 1 := by rw [hH, pow_one, mul_comm]
      exact sylow_card_of_card_eq_mul_pow hq hp hpq.symm hH' Q0
    have hdvd : Nat.card (Sylow q H) ∣ p := by
      have hidx : (Q0 : Subgroup H).index = p := by
        have hmul := Subgroup.card_mul_index (Q0 : Subgroup H)
        rw [hQcard, hH] at hmul
        have hq2pos : 0 < q ^ 2 := pow_pos hq.pos 2
        nlinarith
      rw [← hidx]
      exact card_sylow_dvd_index_aux Q0
    have hmod : Nat.card (Sylow q H) ≡ 1 [MOD q] := card_sylow_modEq_one q H
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | hp'
    · have : Subsingleton (Sylow q H) := Finite.card_le_one_iff_subsingleton.mp (by omega)
      exact ⟨Q0, Sylow.normal_of_subsingleton Q0⟩
    · rw [hp'] at hmod
      have hq1 : q ∣ p - 1 := (Nat.modEq_iff_dvd' hp.one_le).mp hmod.symm
      have hp1pos : 0 < p - 1 := by have := hp.two_le; omega
      have := Nat.le_of_dvd hp1pos hq1
      omega
  · have hgt : q < p := lt_of_le_of_ne (not_lt.mp hlt) hpq.symm
    have hPcard : Nat.card (P0 : Subgroup H) = p := by
      have hH' : Nat.card H = p ^ 1 * q ^ 2 := by rw [hH, pow_one]
      simpa using sylow_card_of_card_eq_mul_pow hp hq hpq hH' P0
    have hdvd : Nat.card (Sylow p H) ∣ q ^ 2 := by
      have hidx : (P0 : Subgroup H).index = q ^ 2 := by
        have hmul := Subgroup.card_mul_index (P0 : Subgroup H)
        rw [hPcard, hH] at hmul
        have hppos : 0 < p := hp.pos
        nlinarith
      rw [← hidx]
      exact card_sylow_dvd_index_aux P0
    have hmod : Nat.card (Sylow p H) ≡ 1 [MOD p] := card_sylow_modEq_one p H
    obtain ⟨k, hk, hcardP⟩ := (Nat.dvd_prime_pow hq).mp hdvd
    interval_cases k
    · left
      rw [pow_zero] at hcardP
      have : Subsingleton (Sylow p H) := Finite.card_le_one_iff_subsingleton.mp (by omega)
      exact ⟨P0, Sylow.normal_of_subsingleton P0⟩
    · exfalso
      rw [pow_one] at hcardP
      rw [hcardP] at hmod
      have hp1 : p ∣ q - 1 := (Nat.modEq_iff_dvd' hq.one_le).mp hmod.symm
      have hq1pos : 0 < q - 1 := by have := hq.two_le; omega
      have := Nat.le_of_dvd hq1pos hp1
      omega
    · rw [hcardP] at hmod
      have hq2pos : 1 ≤ q ^ 2 := one_le_pow₀ hq.one_le
      have hpdvd : p ∣ q ^ 2 - 1 := (Nat.modEq_iff_dvd' hq2pos).mp hmod.symm
      have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
        have hq1 := hq.one_le
        zify [hq1, hq2pos]
        ring
      rw [hfac] at hpdvd
      rcases hp.dvd_mul.mp hpdvd with h1 | h2
      · exfalso
        have hq1pos : 0 < q - 1 := by have := hq.two_le; omega
        have := Nat.le_of_dvd hq1pos h1
        omega
      · have hle : p ≤ q + 1 := Nat.le_of_dvd (by omega) h2
        have hpq1 : p = q + 1 := by omega
        have hq2 : q = 2 := by
          rcases hq.eq_two_or_odd with rfl | hodd
          · rfl
          · exfalso
            have hp_even : 2 ∣ p := by omega
            have hp2 : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hp_even
            have hq2' := hq.two_le
            omega
        have hp3 : p = 3 := by omega
        subst hq2 hp3
        right
        exact sylow_normal_card_twelve (by omega) (by omega)

lemma isCyclic_of_quotient_frattini_isCyclic {P : Type*} [Group P] [Finite P]
    (h : IsCyclic (P ⧸ frattini P)) : IsCyclic P := by
  obtain ⟨gbar, hgbar⟩ := h.exists_generator
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective gbar
  have hsup : Subgroup.zpowers g ⊔ frattini P = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨k, hk⟩ := hgbar (QuotientGroup.mk x)
    have hk' : (QuotientGroup.mk (g ^ k) : P ⧸ frattini P) = QuotientGroup.mk x := by
      simpa [QuotientGroup.mk_zpow] using hk
    have hmem : (g ^ k)⁻¹ * x ∈ frattini P := (QuotientGroup.eq).mp hk'
    have h1 : g ^ k ∈ Subgroup.zpowers g ⊔ frattini P :=
      (le_sup_left : Subgroup.zpowers g ≤ Subgroup.zpowers g ⊔ frattini P) ⟨k, rfl⟩
    have h2 : (g ^ k)⁻¹ * x ∈ Subgroup.zpowers g ⊔ frattini P :=
      (le_sup_right : frattini P ≤ Subgroup.zpowers g ⊔ frattini P) hmem
    have h3 : g ^ k * ((g ^ k)⁻¹ * x) ∈ Subgroup.zpowers g ⊔ frattini P :=
      Subgroup.mul_mem _ h1 h2
    simpa [mul_assoc] using h3
  have htop : Subgroup.zpowers g = ⊤ := frattini_nongenerating hsup
  refine ⟨⟨g, fun x => ?_⟩⟩
  have : x ∈ Subgroup.zpowers g := htop ▸ Subgroup.mem_top x
  exact this

lemma pgroup_coatom_index_eq_prime {P : Type*} [Group P] [Finite P]
    {p : ℕ} (hp : p.Prime) (hP : IsPGroup p P) {M : Subgroup P} (hM : IsCoatom M) :
    M.Normal ∧ Nat.card (P ⧸ M) = p := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  have hMnorm : M.Normal :=
    (Group.isNilpotent_of_finite_tfae (G := P)).out 0 2 rfl rfl |>.mp inferInstance M hM
  refine ⟨hMnorm, ?_⟩
  have hQ : IsPGroup p (P ⧸ M) := hP.to_quotient M
  have hnt : Nontrivial (P ⧸ M) := by
    have hne : ∃ x : P, x ∉ M := by
      by_contra hall
      push_neg at hall
      exact hM.1 (eq_top_iff.mpr fun x _ => hall x)
    obtain ⟨x, hx⟩ := hne
    refine ⟨⟨QuotientGroup.mk x, 1, fun h1 => ?_⟩⟩
    exact hx ((QuotientGroup.eq_one_iff x).mp h1)
  obtain ⟨k, hkpos, hQcard⟩ := hQ.nontrivial_iff_card.mp hnt
  have hpdvd : p ^ 1 ∣ Nat.card (P ⧸ M) := by
    rw [hQcard, pow_one]
    exact dvd_pow_self p (Nat.ne_of_gt hkpos)
  obtain ⟨K, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime p hpdvd
  let L : Subgroup P := K.comap (QuotientGroup.mk' M)
  have hML : M ≤ L := by
    intro x hx
    change QuotientGroup.mk' M x ∈ K
    have h1 : QuotientGroup.mk' M x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact K.one_mem
  have hMLne : M ≠ L := by
    intro heq
    have hKbot : K = ⊥ := by
      ext q
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M q
      change x ∈ L ↔ QuotientGroup.mk' M x = 1
      rw [← heq]
      exact (QuotientGroup.eq_one_iff x).symm
    rw [hKbot, Subgroup.card_bot, pow_one] at hKcard
    have := hp.one_lt
    omega
  have hLtop : L = ⊤ := hM.2 L (lt_of_le_of_ne hML hMLne)
  have hKtop : K = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M q
    have : x ∈ L := hLtop ▸ Subgroup.mem_top x
    exact this
  rw [hKtop, Subgroup.card_top, pow_one] at hKcard
  exact hKcard

lemma pgroup_quotient_frattini_comm_and_pow {P : Type*} [Group P] [Finite P]
    {p : ℕ} (hp : p.Prime) (hP : IsPGroup p P) :
    (∀ x y : P ⧸ frattini P, x * y = y * x) ∧ (∀ x : P ⧸ frattini P, x ^ p = 1) := by
  have hmem_frattini : ∀ z : P, (∀ M : Subgroup P, IsCoatom M → z ∈ M) → z ∈ frattini P := by
    intro z hz
    change z ∈ Order.radical (Subgroup P)
    rw [Order.radical, Subgroup.mem_iInf]
    intro M
    rw [Subgroup.mem_iInf]
    exact hz M
  constructor
  · intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    change (QuotientGroup.mk (a * b) : P ⧸ frattini P) = QuotientGroup.mk (b * a)
    rw [QuotientGroup.eq]
    apply hmem_frattini
    intro M hM
    obtain ⟨hMnorm, hMcard⟩ := pgroup_coatom_index_eq_prime hp hP hM
    have : Fact p.Prime := ⟨hp⟩
    have : IsCyclic (P ⧸ M) := isCyclic_of_prime_card hMcard
    let _ : CommGroup (P ⧸ M) := IsCyclic.commGroup
    have heq : (QuotientGroup.mk a : P ⧸ M) * QuotientGroup.mk b =
        QuotientGroup.mk b * QuotientGroup.mk a := mul_comm _ _
    exact (QuotientGroup.eq).mp heq
  · intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    change (QuotientGroup.mk (a ^ p) : P ⧸ frattini P) = 1
    rw [QuotientGroup.eq_one_iff]
    apply hmem_frattini
    intro M hM
    obtain ⟨hMnorm, hMcard⟩ := pgroup_coatom_index_eq_prime hp hP hM
    haveI : Fintype (P ⧸ M) := Fintype.ofFinite (P ⧸ M)
    have hMcard' : Fintype.card (P ⧸ M) = p := by rw [← Nat.card_eq_fintype_card, hMcard]
    have hpow : (QuotientGroup.mk a : P ⧸ M) ^ p = 1 := by
      rw [← hMcard']
      exact pow_card_eq_one
    exact (QuotientGroup.eq_one_iff (a ^ p)).mp (by simpa [QuotientGroup.mk_pow] using hpow)

lemma maschke_complement_mod_p {V : Type*} [AddCommGroup V] [Finite V]
    {p : ℕ} [Fact p.Prime] (hpV : ∀ v : V, p • v = 0)
    {Q : Type*} [Group Q] [Fintype Q] (hcop : Nat.Coprime (Fintype.card Q) p)
    (act : Q → (V ≃+ V))
    (hact_one : ∀ v, act 1 v = v)
    (hact_mul : ∀ g h v, act (g * h) v = act g (act h v))
    (U : AddSubgroup V)
    (hU_inv : ∀ g : Q, ∀ u ∈ U, act g u ∈ U)
    (hU_ne_bot : U ≠ ⊥) :
    ∃ W : AddSubgroup V, (∀ g : Q, ∀ w ∈ W, act g w ∈ W) ∧ W ≠ ⊤ ∧ U ⊔ W = ⊤ := by
  letI : Module (ZMod p) V :=
    { smul := fun r v => r.val • v
      one_smul := fun v => by
        show (1 : ZMod p).val • v = v
        rw [ZMod.val_one, one_nsmul]
      mul_smul := fun r s v => by
        show (r * s).val • v = r.val • (s.val • v)
        rw [← mul_nsmul', ZMod.val_mul]
        have hdiv := Nat.div_add_mod (r.val * s.val) p
        have h0 : (p * ((r.val * s.val) / p)) • v = 0 := by
          rw [mul_comm, mul_nsmul', hpV, smul_zero]
        have := congrArg (fun n => n • v) hdiv
        simp only [add_nsmul, h0, zero_add] at this
        exact this
      smul_zero := fun r => nsmul_zero r.val
      smul_add := fun r v w => nsmul_add v w r.val
      add_smul := fun r s v => by
        show (r + s).val • v = r.val • v + s.val • v
        rw [ZMod.val_add]
        have hdiv := Nat.div_add_mod (r.val + s.val) p
        have h0 : (p * ((r.val + s.val) / p)) • v = 0 := by
          rw [mul_comm, mul_nsmul', hpV, smul_zero]
        have := congrArg (fun n => n • v) hdiv
        simp only [add_nsmul, h0, zero_add] at this
        exact this
      zero_smul := fun v => by
        show (0 : ZMod p).val • v = 0
        simp }
  let Usub : Submodule (ZMod p) V :=
    { carrier := U
      add_mem' := fun hx hy => U.add_mem hx hy
      zero_mem' := U.zero_mem
      smul_mem' := fun r x hx => U.nsmul_mem hx r.val }
  obtain ⟨proj, hproj⟩ := Usub.exists_isCompl
  let P0 : V →ₗ[ZMod p] V := Usub.subtype.comp (Submodule.projectionOnto Usub proj hproj)
  have hP0_mem : ∀ v : V, P0 v ∈ U := fun v => (Submodule.projectionOnto Usub proj hproj v).2
  have hP0_id : ∀ u ∈ U, P0 u = u := by
    intro u hu
    change (Submodule.projectionOnto Usub proj hproj u : V) = u
    have := Submodule.projectionOnto_apply_left hproj ⟨u, hu⟩
    exact congrArg Subtype.val this
  have hact_smul : ∀ (g : Q) (r : ZMod p) (v : V), act g (r • v) = r • act g v := by
    intro g r v
    change act g (r.val • v) = r.val • act g v
    exact map_nsmul (act g) r.val v
  let c : ZMod p := ((Fintype.card Q : ZMod p))⁻¹
  have hQne : (Fintype.card Q : ZMod p) ≠ 0 := by
    intro h0
    have hdvd : p ∣ Fintype.card Q := (ZMod.natCast_eq_zero_iff (Fintype.card Q) p).mp h0
    have h1 := Nat.dvd_gcd hdvd (dvd_refl p)
    rw [hcop.gcd_eq_one] at h1
    exact (Fact.out : p.Prime).not_dvd_one h1
  have hcQ : c * (Fintype.card Q : ZMod p) = 1 := inv_mul_cancel₀ hQne
  let Pbar : V →+ V :=
    { toFun := fun v => c • (∑ g : Q, act g (P0 (act g⁻¹ v)))
      map_zero' := by simp
      map_add' := fun v w => by
        simp only [map_add, Finset.sum_add_distrib, smul_add] }
  have hPbar_mem : ∀ v : V, Pbar v ∈ U := by
    intro v
    have hsum : (∑ g : Q, act g (P0 (act g⁻¹ v))) ∈ U := by
      refine U.sum_mem ?_
      intro g _
      exact hU_inv g _ (hP0_mem _)
    exact U.nsmul_mem hsum c.val
  have hPbar_id : ∀ u ∈ U, Pbar u = u := by
    intro u hu
    have hterm : ∀ g : Q, act g (P0 (act g⁻¹ u)) = u := by
      intro g
      have h1 : act g⁻¹ u ∈ U := hU_inv g⁻¹ u hu
      rw [hP0_id _ h1, ← hact_mul, mul_inv_cancel, hact_one]
    change c • (∑ g : Q, act g (P0 (act g⁻¹ u))) = u
    simp only [hterm, Finset.sum_const, Finset.card_univ]
    have hsm : (Fintype.card Q) • u = (Fintype.card Q : ZMod p) • u := by
      change (Fintype.card Q) • u = ((Fintype.card Q : ZMod p).val) • u
      rw [ZMod.val_natCast]
      have hdiv := Nat.div_add_mod (Fintype.card Q) p
      have h0 : (p * (Fintype.card Q / p)) • u = 0 := by
        rw [mul_comm, mul_nsmul', hpV, smul_zero]
      have := congrArg (fun n => n • u) hdiv
      simp only [add_nsmul, h0, zero_add] at this
      exact this.symm
    rw [hsm, ← mul_smul, hcQ, one_smul]
  have hPbar_equiv : ∀ (h : Q) (v : V), Pbar (act h v) = act h (Pbar v) := by
    intro h v
    change c • (∑ g : Q, act g (P0 (act g⁻¹ (act h v)))) =
      act h (c • (∑ g : Q, act g (P0 (act g⁻¹ v))))
    rw [hact_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulLeft h).symm _ _ fun g => ?_
    simp only [Equiv.mulLeft_symm_apply]
    have h1 : act g⁻¹ (act h v) = act (h⁻¹ * g)⁻¹ v := by
      rw [← hact_mul]
      have : g⁻¹ * h = (h⁻¹ * g)⁻¹ := by group
      rw [this]
    have h2 : act h (act (h⁻¹ * g) (P0 (act (h⁻¹ * g)⁻¹ v))) =
        act g (P0 (act (h⁻¹ * g)⁻¹ v)) := by
      rw [← hact_mul]
      have : h * (h⁻¹ * g) = g := by group
      rw [this]
    rw [h1, h2]
  refine ⟨Pbar.ker, ?_, ?_, ?_⟩
  · intro g w hw
    change Pbar (act g w) = 0
    rw [hPbar_equiv, hw, map_zero]
  · intro htop
    have : U = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      have hmem : u ∈ Pbar.ker := htop ▸ AddSubgroup.mem_top u
      have h0 : Pbar u = 0 := hmem
      rw [hPbar_id u hu] at h0
      exact h0
    exact hU_ne_bot this
  · rw [eq_top_iff]
    intro v _
    have h1 : Pbar v ∈ U := hPbar_mem v
    have h2 : v - Pbar v ∈ Pbar.ker := by
      change Pbar (v - Pbar v) = 0
      rw [map_sub, hPbar_id _ h1, sub_self]
    have hv : v = Pbar v + (v - Pbar v) := by abel
    rw [hv]
    exact AddSubgroup.add_mem _ ((le_sup_left : U ≤ U ⊔ Pbar.ker) h1)
      ((le_sup_right : Pbar.ker ≤ U ⊔ Pbar.ker) h2)

lemma comap_card_eq_mul {G : Type*} [Group G] [Finite G]
    (K : Subgroup G) [K.Normal] (S : Subgroup (G ⧸ K)) :
    Nat.card (S.comap (QuotientGroup.mk' K) : Subgroup G) = Nat.card K * Nat.card S := by
  let M : Subgroup G := S.comap (QuotientGroup.mk' K)
  have hKM : K ≤ M := by
    intro x hx
    change QuotientGroup.mk' K x ∈ S
    have h1 : QuotientGroup.mk' K x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact S.one_mem
  let φ : M →* S :=
    { toFun := fun x => ⟨QuotientGroup.mk' K x.1, x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hφ_surj : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    exact ⟨⟨x, hy⟩, rfl⟩
  have hker : Nat.card φ.ker = Nat.card K := by
    let e : K ≃ φ.ker :=
      { toFun := fun x => ⟨⟨x.1, hKM x.2⟩, by
          change (⟨QuotientGroup.mk' K x.1, _⟩ : S) = 1
          ext
          exact (QuotientGroup.eq_one_iff x.1).mpr x.2⟩
        invFun := fun x => ⟨x.1.1, by
          have hx : QuotientGroup.mk' K x.1.1 = 1 := congrArg Subtype.val x.2
          exact (QuotientGroup.eq_one_iff x.1.1).mp hx⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact (Nat.card_congr e).symm
  have h1 := Subgroup.card_mul_index φ.ker
  rw [Subgroup.index_eq_card] at h1
  have hqeq : (M ⧸ φ.ker) ≃* S := QuotientGroup.quotientKerEquivOfSurjective φ hφ_surj
  rw [Nat.card_congr hqeq.toEquiv, hker] at h1
  exact h1.symm

lemma case_normal_sylow_p {G : Type*} [Group G] [Finite G]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hGcard : Nat.card G = p ^ 3 * q ^ 2)
    (K : Subgroup G) (hKF : K ≤ frattini G) (hKnorm : K.Normal)
    (hKcard : Nat.card K = p ^ 2) (hKnotcyc : ¬ IsCyclic K)
    (Pbar : Sylow p (G ⧸ K)) (hPbarNorm : (Pbar : Subgroup (G ⧸ K)).Normal) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have hGKcard : Nat.card (G ⧸ K) = p * q ^ 2 := by
    have hmul := Subgroup.card_mul_index K
    rw [hKcard, hGcard, Subgroup.index_eq_card] at hmul
    have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
    nlinarith
  let P : Subgroup G := (Pbar : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K)
  have hPnorm : P.Normal := Subgroup.Normal.comap hPbarNorm (QuotientGroup.mk' K)
  have hKP_le : K ≤ P := by
    intro x hx
    change QuotientGroup.mk' K x ∈ (Pbar : Subgroup (G ⧸ K))
    have h1 : QuotientGroup.mk' K x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact Pbar.one_mem
  have hPbar_card : Nat.card (Pbar : Subgroup (G ⧸ K)) = p := by
    have h1 : Nat.card (G ⧸ K) = p ^ 1 * q ^ 2 := by rw [hGKcard, pow_one]
    simpa using sylow_card_of_card_eq_mul_pow hp hq hpq h1 Pbar
  have hPcard : Nat.card P = p ^ 3 := by
    have := comap_card_eq_mul K (Pbar : Subgroup (G ⧸ K))
    rw [hKcard, hPbar_card] at this
    nlinarith
  have hPisP : IsPGroup p P := IsPGroup.of_card hPcard
  let Ksub : Subgroup P := K.subgroupOf P
  have hKsub_card : Nat.card Ksub = p ^ 2 := by
    have he : Ksub ≃* K := Subgroup.subgroupOfEquivOfLe hKP_le
    rw [Nat.card_congr he.toEquiv, hKcard]
  have hKsub_idx : Ksub.index = p := by
    have hm := Subgroup.card_mul_index Ksub
    rw [hKsub_card, hPcard] at hm
    have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
    nlinarith
  have hKsub_coatom : IsCoatom Ksub := isCoatom_of_index_eq_prime_aux hp hKsub_idx
  have hPhiP_le_Ksub : frattini P ≤ Ksub := frattini_le_coatom hKsub_coatom
  have hPhiP_lt_Ksub : frattini P < Ksub := by
    refine lt_of_le_of_ne hPhiP_le_Ksub ?_
    intro heq
    have hQcard : Nat.card (P ⧸ frattini P) = p := by
      rw [heq, ← Subgroup.index_eq_card, hKsub_idx]
    have hPcyc : IsCyclic P :=
      isCyclic_of_quotient_frattini_isCyclic (isCyclic_of_prime_card hQcard)
    have hKsub_cyc : IsCyclic Ksub := inferInstance
    have he : Ksub ≃* K := Subgroup.subgroupOfEquivOfLe hKP_le
    exact hKnotcyc (he.isCyclic.mp hKsub_cyc)
  obtain ⟨hcommV, hpowV⟩ := pgroup_quotient_frattini_comm_and_pow hp hPisP
  letI : CommGroup (P ⧸ frattini P) :=
    { (inferInstance : Group (P ⧸ frattini P)) with mul_comm := hcommV }
  let V := Additive (P ⧸ frattini P)
  have hpV : ∀ v : V, p • v = 0 := fun v => hpowV (Additive.toMul v)
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow q G))
  have hQcard : Nat.card (Q : Subgroup G) = q ^ 2 := by
    have hG' : Nat.card G = q ^ 2 * p ^ 3 := by rw [hGcard, mul_comm]
    exact sylow_card_of_card_eq_mul_pow hq hp hpq.symm hG' Q
  haveI : Fintype Q := Fintype.ofFinite Q
  have hQcop : Nat.Coprime (Fintype.card Q) p := by
    rw [← Nat.card_eq_fintype_card, hQcard]
    exact ((Nat.coprime_primes hq hp).mpr hpq.symm).pow_left 2
  let conjP : Q → (P ≃* P) := fun g =>
    { toFun := fun x => ⟨g.1 * x.1 * g.1⁻¹, hPnorm.conj_mem _ x.2 g.1⟩
      invFun := fun x => ⟨g.1⁻¹ * x.1 * g.1, by
        simpa [inv_inv] using hPnorm.conj_mem _ x.2 g.1⁻¹⟩
      left_inv := fun x => by ext; group
      right_inv := fun x => by ext; group
      map_mul' := fun x y => by ext; simp only [Subgroup.coe_mul]; group }
  let conjQ : Q → (P ⧸ frattini P ≃* P ⧸ frattini P) := fun g =>
    QuotientGroup.congr (frattini P) (frattini P) (conjP g)
      (Subgroup.characteristic_iff_map_eq.mp frattini_characteristic (conjP g))
  let act : Q → (V ≃+ V) := fun g => (conjQ g).toAdditive
  have hact_one : ∀ v : V, act 1 v = v := by
    intro v
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have hv : v = Additive.ofMul (QuotientGroup.mk a) := by
      rw [ha]; rfl
    rw [hv]
    change Additive.ofMul (QuotientGroup.mk (conjP 1 a)) = Additive.ofMul (QuotientGroup.mk a)
    congr 2
    ext
    simp [conjP]
  have hact_mul : ∀ (g h : Q) (v : V), act (g * h) v = act g (act h v) := by
    intro g h v
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have hv : v = Additive.ofMul (QuotientGroup.mk a) := by
      rw [ha]; rfl
    rw [hv]
    change Additive.ofMul (QuotientGroup.mk (conjP (g * h) a)) =
      Additive.ofMul (QuotientGroup.mk (conjP g (conjP h a)))
    congr 2
    ext
    simp [conjP, mul_assoc]
  let Ugrp : Subgroup (P ⧸ frattini P) := Ksub.map (QuotientGroup.mk' (frattini P))
  let U : AddSubgroup V :=
    { carrier := {v | Additive.toMul v ∈ Ugrp}
      add_mem' := fun hx hy => Ugrp.mul_mem hx hy
      zero_mem' := Ugrp.one_mem
      neg_mem' := fun hx => Ugrp.inv_mem hx }
  have hU_inv : ∀ g : Q, ∀ u ∈ U, act g u ∈ U := by
    intro g u hu
    rcases hu with ⟨x, hx, hxu⟩
    refine ⟨conjP g x, ?_, ?_⟩
    · change g.1 * x.1 * g.1⁻¹ ∈ K
      exact hKnorm.conj_mem _ hx g.1
    · change QuotientGroup.mk' (frattini P) (conjP g x) = conjQ g (Additive.toMul u)
      rw [← hxu]
      rfl
  have hU_ne_bot : U ≠ ⊥ := by
    intro hbot
    have hle : Ksub ≤ frattini P := by
      intro x hx
      have hmem : Additive.ofMul (QuotientGroup.mk' (frattini P) x) ∈ U := ⟨x, hx, rfl⟩
      rw [hbot, AddSubgroup.mem_bot] at hmem
      have h1 : QuotientGroup.mk' (frattini P) x = 1 := hmem
      exact (QuotientGroup.eq_one_iff x).mp h1
    exact not_le_of_gt hPhiP_lt_Ksub hle
  obtain ⟨W, hW_inv, hW_ne_top, hUW_top⟩ :=
    maschke_complement_mod_p hpV hQcop act hact_one hact_mul U hU_inv hU_ne_bot
  let Wgrp : Subgroup (P ⧸ frattini P) :=
    { carrier := {q | Additive.ofMul q ∈ W}
      mul_mem' := fun hx hy => W.add_mem hx hy
      one_mem' := W.zero_mem
      inv_mem' := fun hx => W.neg_mem hx }
  let P1sub : Subgroup P := Wgrp.comap (QuotientGroup.mk' (frattini P))
  let P1 : Subgroup G := P1sub.map P.subtype
  have hP1_le_P : P1 ≤ P := by
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  have hP1_lt_P : P1 < P := by
    refine lt_of_le_of_ne hP1_le_P ?_
    intro heq
    apply hW_ne_top
    rw [eq_top_iff]
    intro v _
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    have hxP1 : (x : G) ∈ P1 := by
      rw [heq]
      exact x.2
    rcases hxP1 with ⟨y, hy, hyx⟩
    have hxy : x = y := Subtype.ext hyx.symm
    rw [← hxy] at hy
    change Additive.ofMul (QuotientGroup.mk' (frattini P) x) ∈ W at hy
    have hxeq : Additive.ofMul (QuotientGroup.mk' (frattini P) x) = v := by
      change Additive.ofMul (QuotientGroup.mk x) = v
      rw [hx]
      rfl
    rwa [hxeq] at hy
  have hQ_norm_P1 : (Q : Subgroup G) ≤ Subgroup.normalizer (P1 : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨a, ha, rfl⟩
      refine ⟨conjP ⟨g, hg⟩ a, ?_, rfl⟩
      change Additive.ofMul (QuotientGroup.mk' (frattini P) (conjP ⟨g, hg⟩ a)) ∈ W
      have hstep : Additive.ofMul (QuotientGroup.mk' (frattini P) (conjP ⟨g, hg⟩ a)) =
          act ⟨g, hg⟩ (Additive.ofMul (QuotientGroup.mk' (frattini P) a)) := rfl
      rw [hstep]
      exact hW_inv ⟨g, hg⟩ _ ha
    · intro hgx
      rcases hgx with ⟨b, hb, hbeq⟩
      have hbinv : P.subtype ((conjP ⟨g, hg⟩⁻¹) b) = x := by
        have hinv : ((⟨g, hg⟩⁻¹ : Q) : G) = g⁻¹ := rfl
        change ((⟨g, hg⟩⁻¹ : Q) : G) * b.1 * ((⟨g, hg⟩⁻¹ : Q) : G)⁻¹ = x
        rw [hinv, inv_inv]
        change b.1 = g * x * g⁻¹ at hbeq
        rw [hbeq]
        group
      refine ⟨conjP ⟨g, hg⟩⁻¹ b, ?_, hbinv⟩
      change Additive.ofMul (QuotientGroup.mk' (frattini P) (conjP ⟨g, hg⟩⁻¹ b)) ∈ W
      have hstep : Additive.ofMul (QuotientGroup.mk' (frattini P) (conjP ⟨g, hg⟩⁻¹ b)) =
          act ⟨g, hg⟩⁻¹ (Additive.ofMul (QuotientGroup.mk' (frattini P) b)) := rfl
      rw [hstep]
      exact hW_inv ⟨g, hg⟩⁻¹ _ hb
  have hKP1_eq_P : K ⊔ P1 = P := by
    apply le_antisymm (sup_le hKP_le hP1_le_P)
    intro x hx
    let v : V := Additive.ofMul (QuotientGroup.mk' (frattini P) ⟨x, hx⟩)
    have hv : v ∈ U ⊔ W := hUW_top ▸ AddSubgroup.mem_top v
    rw [AddSubgroup.mem_sup] at hv
    obtain ⟨u, hu, w, hw, huvw⟩ := hv
    rcases hu with ⟨a, haK, hau⟩
    obtain ⟨b, hb⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    have hbP1 : b ∈ P1sub := by
      change Additive.ofMul (QuotientGroup.mk' (frattini P) b) ∈ W
      have : Additive.ofMul (QuotientGroup.mk' (frattini P) b) = w := by
        change Additive.ofMul (QuotientGroup.mk b) = w
        rw [hb]; rfl
      rwa [this]
    have hmul_q : (QuotientGroup.mk (a * b) : P ⧸ frattini P) = QuotientGroup.mk (⟨x, hx⟩ : P) := by
      have h1 : (Additive.toMul u) * (Additive.toMul w) = Additive.toMul v := huvw
      rw [← hau, ← hb] at h1
      exact h1
    have hdiff : (a * b)⁻¹ * ⟨x, hx⟩ ∈ frattini P := (QuotientGroup.eq).mp hmul_q
    have hdiff_P1 : (a * b)⁻¹ * ⟨x, hx⟩ ∈ P1sub := by
      change Additive.ofMul (QuotientGroup.mk' (frattini P) ((a * b)⁻¹ * ⟨x, hx⟩)) ∈ W
      have h1 : QuotientGroup.mk' (frattini P) ((a * b)⁻¹ * ⟨x, hx⟩) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr hdiff
      rw [h1]
      exact W.zero_mem
    have hprod_P1 : b * ((a * b)⁻¹ * ⟨x, hx⟩) ∈ P1sub := P1sub.mul_mem hbP1 hdiff_P1
    have hx_eq : x = a.1 * (b * ((a * b)⁻¹ * ⟨x, hx⟩)).1 := by
      have : (⟨x, hx⟩ : P) = a * (b * ((a * b)⁻¹ * ⟨x, hx⟩)) := by group
      exact congrArg Subtype.val this
    rw [hx_eq]
    exact Subgroup.mul_mem _ ((le_sup_left : K ≤ K ⊔ P1) haK)
      ((le_sup_right : P1 ≤ K ⊔ P1) ⟨_, hprod_P1, rfl⟩)
  let H : Subgroup G := P1 ⊔ (Q : Subgroup G)
  have hD_PQ : Disjoint P (Q : Subgroup G) :=
    IsPGroup.disjoint_of_ne p q hpq P (Q : Subgroup G) hPisP Q.isPGroup'
  have hD_P1Q : Disjoint P1 (Q : Subgroup G) := Disjoint.mono_left hP1_le_P hD_PQ
  have hH_lt_top : H < ⊤ := by
    have hHcard : Nat.card H = Nat.card P1 * Nat.card (Q : Subgroup G) :=
      card_sup_of_le_normalizer_of_disjoint hQ_norm_P1 hD_P1Q
    have hP1_lt : Nat.card P1 < Nat.card P := by
      have hle := Subgroup.card_le_of_le hP1_le_P
      refine lt_of_le_of_ne hle ?_
      intro heq
      exact hP1_lt_P.ne (Subgroup.eq_of_le_of_card_ge hP1_le_P (by omega))
    have hH_lt_G : Nat.card H < Nat.card G := by
      rw [hHcard, hQcard, hGcard]
      have hq2pos : 0 < q ^ 2 := pow_pos hq.pos 2
      rw [hPcard] at hP1_lt
      nlinarith
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    rw [htop, Subgroup.card_top] at hH_lt_G
    exact lt_irrefl _ hH_lt_G
  have hPQ_top : P ⊔ (Q : Subgroup G) = ⊤ :=
    sup_eq_top_of_card_eq
      (by rw [Subgroup.normalizer_eq_top_iff.mpr hPnorm]; exact le_top)
      hD_PQ (by rw [hPcard, hQcard, hGcard])
  have hHF_top : H ⊔ frattini G = ⊤ := by
    rw [eq_top_iff, ← hPQ_top, ← hKP1_eq_P]
    refine sup_le (sup_le (hKF.trans le_sup_right) (le_sup_left.trans le_sup_left))
      (le_sup_right.trans le_sup_left)
  exact hH_lt_top.ne (frattini_nongenerating hHF_top)

lemma case_normal_sylow_q {G : Type*} [Group G] [Finite G]
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hGcard : Nat.card G = p ^ 3 * q ^ 2)
    (K : Subgroup G) (hKF : K ≤ frattini G) (hKnorm : K.Normal)
    (hKP : IsPGroup p K) (hKcard : Nat.card K = p ^ 2) (hKnotcyc : ¬ IsCyclic K)
    (Qbar : Sylow q (G ⧸ K)) (hQbarNorm : (Qbar : Subgroup (G ⧸ K)).Normal) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have hGKcard : Nat.card (G ⧸ K) = p * q ^ 2 := by
    have hmul := Subgroup.card_mul_index K
    rw [hKcard, hGcard, Subgroup.index_eq_card] at hmul
    have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
    nlinarith
  let N : Subgroup G := (Qbar : Subgroup (G ⧸ K)).comap (QuotientGroup.mk' K)
  have hNnorm : N.Normal := Subgroup.Normal.comap hQbarNorm (QuotientGroup.mk' K)
  have hKN_le : K ≤ N := by
    intro x hx
    change QuotientGroup.mk' K x ∈ (Qbar : Subgroup (G ⧸ K))
    have h1 : QuotientGroup.mk' K x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    rw [h1]
    exact Qbar.one_mem
  have hQbar_card : Nat.card (Qbar : Subgroup (G ⧸ K)) = q ^ 2 := by
    have h1 : Nat.card (G ⧸ K) = q ^ 2 * p ^ 1 := by rw [hGKcard, pow_one, mul_comm]
    exact sylow_card_of_card_eq_mul_pow hq hp hpq.symm h1 Qbar
  have hNcard : Nat.card N = p ^ 2 * q ^ 2 := by
    have := comap_card_eq_mul K (Qbar : Subgroup (G ⧸ K))
    rw [hKcard, hQbar_card] at this
    exact this
  obtain ⟨Qsub⟩ := (inferInstance : Nonempty (Sylow q N))
  have hQsub_card : Nat.card (Qsub : Subgroup N) = q ^ 2 := by
    have hN' : Nat.card N = q ^ 2 * p ^ 2 := by rw [hNcard, mul_comm]
    exact sylow_card_of_card_eq_mul_pow hq hp hpq.symm hN' Qsub
  let Q : Subgroup G := (Qsub : Subgroup N).map N.subtype
  have hQcard : Nat.card Q = q ^ 2 := by
    have he : (Qsub : Subgroup N) ≃* Q :=
      Subgroup.equivMapOfInjective _ N.subtype Subtype.coe_injective
    rw [← Nat.card_congr he.toEquiv, hQsub_card]
  have hQisP : IsPGroup q Q := Qsub.isPGroup'.map N.subtype
  have hDKQ : Disjoint K Q := IsPGroup.disjoint_of_ne p q hpq K Q hKP hQisP
  have hKQ_eq_N : K ⊔ Q = N := by
    have hle : K ⊔ Q ≤ N := sup_le hKN_le (by rintro _ ⟨x, _, rfl⟩; exact x.2)
    have hc : Nat.card (K ⊔ Q : Subgroup G) = p ^ 2 * q ^ 2 := by
      rw [card_sup_of_le_normalizer_of_disjoint
        (by rw [Subgroup.normalizer_eq_top_iff.mpr hKnorm]; exact le_top) hDKQ, hKcard, hQcard]
    exact Subgroup.eq_of_le_of_card_ge hle (by omega)
  have hFrat : Subgroup.normalizer (Q : Set G) ⊔ N = ⊤ := Sylow.normalizer_sup_eq_top Qsub
  have hQnorm_sup : Subgroup.normalizer (Q : Set G) ⊔ frattini G = ⊤ := by
    rw [eq_top_iff, ← hFrat, ← hKQ_eq_N]
    refine sup_le le_sup_left (sup_le (hKF.trans le_sup_right) ?_)
    exact Subgroup.le_normalizer.trans le_sup_left
  have hQnorm : Q.Normal := Subgroup.normalizer_eq_top_iff.mp (frattini_nongenerating hQnorm_sup)
  have hGQcard : Nat.card (G ⧸ Q) = p ^ 3 := by
    have hm := Subgroup.card_mul_index Q
    rw [hQcard, hGcard, Subgroup.index_eq_card] at hm
    have hq2pos : 0 < q ^ 2 := pow_pos hq.pos 2
    nlinarith
  let Kimg : Subgroup (G ⧸ Q) := K.map (QuotientGroup.mk' Q)
  have hKimg_le : Kimg ≤ frattini (G ⧸ Q) := by
    have h1 := frattini_le_comap_frattini_of_surjective (QuotientGroup.mk'_surjective Q)
    rintro _ ⟨x, hx, rfl⟩
    exact h1 (hKF hx)
  let fK : K →* Kimg :=
    { toFun := fun x => ⟨QuotientGroup.mk' Q x.1, ⟨x.1, x.2, rfl⟩⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp }
  have hfK_inj : Function.Injective fK := by
    intro x y h
    have heq : QuotientGroup.mk' Q x.1 = QuotientGroup.mk' Q y.1 := congrArg Subtype.val h
    have hmemQ : x.1⁻¹ * y.1 ∈ Q := (QuotientGroup.eq).mp heq
    have hmemK : x.1⁻¹ * y.1 ∈ K := K.mul_mem (K.inv_mem x.2) y.2
    have hbot : x.1⁻¹ * y.1 = 1 := (Subgroup.disjoint_def.mp hDKQ) hmemK hmemQ
    ext
    calc x.1 = x.1 * (x.1⁻¹ * y.1) := by rw [hbot]; simp
      _ = y.1 := by group
  have hfK_surj : Function.Surjective fK := by
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hKimg_equiv : K ≃* Kimg := MulEquiv.ofBijective fK ⟨hfK_inj, hfK_surj⟩
  have hKimg_card : Nat.card Kimg = p ^ 2 := by
    rw [← Nat.card_congr hKimg_equiv.toEquiv, hKcard]
  have hPhiGQ_dvd : Nat.card (frattini (G ⧸ Q)) ∣ p ^ 3 := by
    rw [← hGQcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hKimg_dvd : p ^ 2 ∣ Nat.card (frattini (G ⧸ Q)) := by
    rw [← hKimg_card]
    exact Subgroup.card_dvd_of_le hKimg_le
  obtain ⟨r, hr3, hr⟩ := (Nat.dvd_prime_pow hp).mp hPhiGQ_dvd
  have hr2 : 2 ≤ r := by
    rw [hr] at hKimg_dvd
    exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hKimg_dvd
  have hGQ_cyc : IsCyclic (G ⧸ Q) := by
    interval_cases r
    · have hqcard : Nat.card ((G ⧸ Q) ⧸ frattini (G ⧸ Q)) = p := by
        have hm := Subgroup.card_mul_index (frattini (G ⧸ Q))
        rw [hr, hGQcard, Subgroup.index_eq_card] at hm
        have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
        nlinarith
      exact isCyclic_of_quotient_frattini_isCyclic (isCyclic_of_prime_card hqcard)
    · have hqcard : Nat.card ((G ⧸ Q) ⧸ frattini (G ⧸ Q)) = 1 := by
        have hm := Subgroup.card_mul_index (frattini (G ⧸ Q))
        rw [hr, hGQcard, Subgroup.index_eq_card] at hm
        have hp3pos : 0 < p ^ 3 := pow_pos hp.pos 3
        nlinarith
      have : Subsingleton ((G ⧸ Q) ⧸ frattini (G ⧸ Q)) :=
        Finite.card_le_one_iff_subsingleton.mp (by omega)
      exact isCyclic_of_quotient_frattini_isCyclic isCyclic_of_subsingleton
  have hKimg_cyc : IsCyclic Kimg := inferInstance
  exact hKnotcyc (hKimg_equiv.isCyclic.mpr hKimg_cyc)

lemma main_proof (G : Type) [Group G] [Fintype G] (p q : ℕ)
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hcard : Fintype.card G = p ^ 3 * q ^ 2) : IsCyclic (frattini G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact q.Prime := ⟨hq⟩
  have hGcard : Nat.card G = p ^ 3 * q ^ 2 := by rw [Nat.card_eq_fintype_card, hcard]
  have : Group.IsNilpotent (frattini G) := frattini_nilpotent
  have hFdvd : Nat.card (frattini G) ∣ p ^ 3 * q ^ 2 := by
    rw [← hGcard]
    exact Subgroup.card_subgroup_dvd_card (frattini G)
  obtain ⟨a, b, ha, hb, hFcard⟩ := factor_prime_pow_mul_prime_pow hp hq hFdvd
  apply isCyclic_of_nilpotent_card_mul_pow hp hq hpq hFcard
  · intro P0
    have hP0card : Nat.card (P0 : Subgroup (frattini G)) = p ^ a :=
      sylow_card_of_card_eq_mul_pow hp hq hpq hFcard P0
    let K : Subgroup G := (P0 : Subgroup (frattini G)).map (frattini G).subtype
    have hKF : K ≤ frattini G := by
      rintro _ ⟨x, _, rfl⟩
      exact x.2
    have hKcard : Nat.card K = p ^ a := by
      have he : (P0 : Subgroup (frattini G)) ≃* K :=
        Subgroup.equivMapOfInjective _ (frattini G).subtype Subtype.coe_injective
      rw [← Nat.card_congr he.toEquiv, hP0card]
    have hKnorm : K.Normal := by
      have h1 := Sylow.normalizer_sup_eq_top P0
      have h2 := frattini_nongenerating h1
      exact Subgroup.normalizer_eq_top_iff.mp h2
    have hKP : IsPGroup p K := P0.isPGroup'.map (frattini G).subtype
    have ha3 : a ≠ 3 := by
      intro ha3
      subst ha3
      obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow q G))
      have hQcard : Nat.card (Q : Subgroup G) = q ^ 2 := by
        have hG' : Nat.card G = q ^ 2 * p ^ 3 := by rw [hGcard, mul_comm]
        exact sylow_card_of_card_eq_mul_pow hq hp hpq.symm hG' Q
      have hD : Disjoint K (Q : Subgroup G) :=
        IsPGroup.disjoint_of_ne p q hpq K (Q : Subgroup G) hKP Q.isPGroup'
      have hsup : K ⊔ (Q : Subgroup G) = ⊤ :=
        sup_eq_top_of_card_eq
          (by rw [Subgroup.normalizer_eq_top_iff.mpr hKnorm]; exact le_top) hD
          (by rw [hKcard, hQcard, hGcard])
      have hsupF : (Q : Subgroup G) ⊔ frattini G = ⊤ := by
        rw [eq_top_iff, ← hsup]
        exact sup_le (hKF.trans le_sup_right) le_sup_left
      have hQtop : (Q : Subgroup G) = ⊤ := frattini_nongenerating hsupF
      have hQeq : Nat.card (Q : Subgroup G) = Nat.card G := by rw [hQtop, Subgroup.card_top]
      rw [hQcard, hGcard] at hQeq
      have hq2pos : 0 < q ^ 2 := pow_pos hq.pos 2
      have hp3 : 1 < p ^ 3 := one_lt_pow₀ hp.one_lt (by decide)
      nlinarith
    have ha2 : a ≤ 2 := by omega
    interval_cases a
    · rw [pow_zero] at hP0card
      have : Subsingleton P0 := Finite.card_le_one_iff_subsingleton.mp (by omega)
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hP0card
      exact isCyclic_of_prime_card hP0card
    · by_contra hnotcyc
      have hKnotcyc : ¬ IsCyclic K := by
        intro hc
        have he : (P0 : Subgroup (frattini G)) ≃* K :=
          Subgroup.equivMapOfInjective _ (frattini G).subtype Subtype.coe_injective
        exact hnotcyc (he.symm.isCyclic.mp hc)
      have hGKcard : Nat.card (G ⧸ K) = p * q ^ 2 := by
        have hmul := Subgroup.card_mul_index K
        rw [hKcard, hGcard, Subgroup.index_eq_card] at hmul
        have hp2pos : 0 < p ^ 2 := pow_pos hp.pos 2
        nlinarith
      rcases sylow_normal_of_card_pq2 hp hq hpq hGKcard with ⟨Pbar, hPbarNorm⟩ | ⟨Qbar, hQbarNorm⟩
      · exact case_normal_sylow_p hp hq hpq hGcard K hKF hKnorm hKcard hKnotcyc Pbar hPbarNorm
      · exact case_normal_sylow_q hp hq hpq hGcard K hKF hKnorm hKP hKcard hKnotcyc Qbar hQbarNorm
  · intro Q0
    have hQ0card : Nat.card (Q0 : Subgroup (frattini G)) = q ^ b := by
      have hF' : Nat.card (frattini G) = q ^ b * p ^ a := by rw [hFcard, mul_comm]
      exact sylow_card_of_card_eq_mul_pow hq hp hpq.symm hF' Q0
    have hb2 : b ≠ 2 := by
      intro hb2
      subst hb2
      let L : Subgroup G := (Q0 : Subgroup (frattini G)).map (frattini G).subtype
      have hLF : L ≤ frattini G := by
        rintro _ ⟨x, _, rfl⟩
        exact x.2
      have hLcard : Nat.card L = q ^ 2 := by
        have he : (Q0 : Subgroup (frattini G)) ≃* L :=
          Subgroup.equivMapOfInjective _ (frattini G).subtype Subtype.coe_injective
        rw [← Nat.card_congr he.toEquiv, hQ0card]
      have hLnorm : L.Normal := by
        have h1 := Sylow.normalizer_sup_eq_top Q0
        have h2 := frattini_nongenerating h1
        exact Subgroup.normalizer_eq_top_iff.mp h2
      obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow p G))
      have hPcard : Nat.card (P : Subgroup G) = p ^ 3 :=
        sylow_card_of_card_eq_mul_pow hp hq hpq hGcard P
      have hLQ : IsPGroup q L := Q0.isPGroup'.map (frattini G).subtype
      have hD : Disjoint L (P : Subgroup G) :=
        IsPGroup.disjoint_of_ne q p hpq.symm L (P : Subgroup G) hLQ P.isPGroup'
      have hsup : L ⊔ (P : Subgroup G) = ⊤ :=
        sup_eq_top_of_card_eq
          (by rw [Subgroup.normalizer_eq_top_iff.mpr hLnorm]; exact le_top) hD
          (by rw [hLcard, hPcard, hGcard, mul_comm])
      have hsupF : (P : Subgroup G) ⊔ frattini G = ⊤ := by
        rw [eq_top_iff, ← hsup]
        exact sup_le (hLF.trans le_sup_right) le_sup_left
      have hPtop : (P : Subgroup G) = ⊤ := frattini_nongenerating hsupF
      have hPeq : Nat.card (P : Subgroup G) = Nat.card G := by rw [hPtop, Subgroup.card_top]
      rw [hPcard, hGcard] at hPeq
      have hp3pos : 0 < p ^ 3 := pow_pos hp.pos 3
      have hq2 : 1 < q ^ 2 := one_lt_pow₀ hq.one_lt (by decide)
      nlinarith
    have hb1 : b ≤ 1 := by omega
    interval_cases b
    · rw [pow_zero] at hQ0card
      have : Subsingleton Q0 := Finite.card_le_one_iff_subsingleton.mp (by omega)
      exact isCyclic_of_subsingleton
    · rw [pow_one] at hQ0card
      exact isCyclic_of_prime_card hQ0card

end NeonMSE1870482

theorem OMA.solution : type_of% @OMA.S_mse_1870482.main :=
  NeonMSE1870482.main_proof
