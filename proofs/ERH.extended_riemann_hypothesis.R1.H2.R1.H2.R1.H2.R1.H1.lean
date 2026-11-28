import OMAReductions.R_ERH_extended_riemann_hypothesis_R1_H2_R1_H2_R1_H2_R1

namespace OMAH1Help
open Finset NumberField
open scoped NumberField

variable {K : Type} [Field K] [NumberField K]

abbrev P (K : Type) [Field K] [NumberField K] := {I : Ideal (𝓞 K) // I.IsPrime ∧ I ≠ ⊥}

noncomputable def pr (S : Finset (P K)) : Ideal (𝓞 K) := ∏ p ∈ S, p.1

noncomputable def N (S : Finset (P K)) : ℕ := ∏ p ∈ S, Ideal.absNorm p.1

lemma norm_pr (S : Finset (P K)) : Ideal.absNorm (pr S) = N S := by
  simp [pr, N, map_prod]

lemma pr_ne_bot (S : Finset (P K)) : pr S ≠ ⊥ := by
  intro h
  have h0 : (∏ p ∈ S, p.1) = 0 := h
  obtain ⟨p, _, hp⟩ := Finset.prod_eq_zero_iff.mp h0
  exact p.2.2 hp

lemma maximal (p : P K) : p.1.IsMaximal :=
  Ideal.IsPrime.isMaximal_of_ne_bot p.2.1 p.2.2

lemma pr_dvd_iff (S : Finset (P K)) (I : Ideal (𝓞 K)) :
    pr S ∣ I ↔ ∀ p ∈ S, p.1 ∣ I := by
  constructor
  · intro h p hp
    exact (Finset.dvd_prod_of_mem (fun q : P K => q.1) hp).trans h
  · intro h
    apply Finset.prod_dvd_of_coprime _ h
    intro p _ q _ hpq
    have := maximal p
    have := maximal q
    exact Ideal.isCoprime_of_isMaximal (fun e => hpq (Subtype.ext e))

lemma norm_le_of_dvd (p : P K) (I : Ideal (𝓞 K)) (n : ℕ) (hn : n ≠ 0)
    (hI : Ideal.absNorm I = n) (h : p.1 ∣ I) : Ideal.absNorm p.1 ≤ n := by
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero hn)
  rw [← hI]
  exact Ideal.absNorm_dvd_absNorm_of_le (Ideal.le_of_dvd h)

lemma finP (n : ℕ) : {p : P K | Ideal.absNorm p.1 ≤ n}.Finite :=
  (Ideal.finite_setOfPred_absNorm_le n).preimage Subtype.val_injective.injOn

noncomputable def Q (n : ℕ) : Finset (P K) := (finP (K := K) n).toFinset

lemma mem_Q (n : ℕ) (p : P K) : p ∈ Q n ↔ Ideal.absNorm p.1 ≤ n := by
  simp [Q]

noncomputable def IdN (e : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_eq e).toFinset

lemma mem_IdN (e : ℕ) (I : Ideal (𝓞 K)) : I ∈ IdN e ↔ Ideal.absNorm I = e := by
  simp [IdN]

lemma card_IdN (e : ℕ) :
    Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = e} = (IdN (K := K) e).card := by
  rw [IdN, ← Set.ncard_eq_toFinset_card _ (Ideal.finite_setOfPred_absNorm_eq e),
    ← Nat.card_coe_set_eq]
  rfl

lemma subset_Q (S : Finset (P K)) (d n : ℕ) (hd : N S = d) (hd0 : d ≠ 0) (hdn : d ≤ n) :
    S ⊆ Q n := by
  intro p hp
  rw [mem_Q]
  have : Ideal.absNorm p.1 ∣ N S := Finset.dvd_prod_of_mem (fun q : P K => Ideal.absNorm q.1) hp
  rw [hd] at this
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero hd0) this).trans hdn

lemma a_eq (d n : ℕ) (hd0 : d ≠ 0) (hdn : d ≤ n) :
    (∑' S : (N (K := K)) ⁻¹' {d}, (-1 : ℂ)^S.1.card) =
      ∑ S ∈ (Q (K := K) n).powerset.filter (fun S => N S = d), (-1 : ℂ)^S.card := by
  classical
  have hs : (N (K := K)) ⁻¹' {d} = ↑((Q (K := K) n).powerset.filter (fun S => N S = d)) := by
    ext S
    simp only [Set.mem_preimage, Set.mem_singleton_iff, coe_filter, mem_powerset,
      Set.mem_ofPred_eq]
    exact ⟨fun h => ⟨subset_Q S d n h hd0 hdn, h⟩, fun h => h.2⟩
  rw [hs, Finset.tsum_subtype' _ (fun S : Finset (P K) => (-1 : ℂ)^S.card)]


open Classical in
lemma filter_empty_iff (n : ℕ) (hn : n ≠ 0) (I : Ideal (𝓞 K)) (hI : Ideal.absNorm I = n) :
    (Q (K := K) n).filter (fun p => p.1 ∣ I) = ∅ ↔ I = ⊤ := by
  classical
  constructor
  · intro h
    by_contra hne
    obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hne
    have hI0 : I ≠ ⊥ := by
      intro e
      rw [e, Ideal.absNorm_bot] at hI
      exact hn hI.symm
    have hM0 : M ≠ ⊥ := fun e => hI0 (le_bot_iff.mp (e ▸ hIM))
    let p : P K := ⟨M, hM.isPrime, hM0⟩
    have hdvd : p.1 ∣ I := Ideal.dvd_iff_le.mpr hIM
    have hp : p ∈ (Q (K := K) n).filter (fun p => p.1 ∣ I) := by
      rw [mem_filter, mem_Q]
      exact ⟨norm_le_of_dvd p I n hn hI hdvd, hdvd⟩
    rw [h] at hp
    exact absurd hp (Finset.notMem_empty _)
  · intro h
    rw [Finset.filter_eq_empty_iff]
    intro p _ hp
    rw [h] at hp
    exact p.2.1.ne_top (top_le_iff.mp (Ideal.le_of_dvd hp))

lemma conv (n : ℕ) (hn : n ≠ 0) :
    ∑ x ∈ n.divisorsAntidiagonal,
      (∑ S ∈ (Q (K := K) n).powerset.filter (fun S => N S = x.1), (-1 : ℂ)^S.card) *
        ((IdN (K := K) x.2).card : ℂ) = if n = 1 then 1 else 0 := by
  classical
  calc _ = ∑ y ∈ (n.divisorsAntidiagonal).sigma (fun x =>
          ((Q (K := K) n).powerset.filter (fun S => N S = x.1)) ×ˢ IdN (K := K) x.2),
          (-1 : ℂ)^y.2.1.card := by
        rw [Finset.sum_sigma]
        apply sum_congr rfl
        intro x _
        rw [Finset.sum_product, Finset.sum_mul]
        apply sum_congr rfl
        intro S _
        simp [Finset.sum_const, mul_comm]
    _ = ∑ y ∈ (IdN (K := K) n).sigma (fun I => ((Q (K := K) n).filter (fun p => p.1 ∣ I)).powerset),
          (-1 : ℂ)^y.2.card := by
        apply Finset.sum_bij
          (fun y _ => (⟨pr y.2.1 * y.2.2, y.2.1⟩ : Σ _ : Ideal (𝓞 K), Finset (P K)))
        · rintro ⟨x, S, J⟩ hy
          simp only [mem_sigma, mem_product, mem_filter, mem_powerset, Finset.subset_iff, Nat.mem_divisorsAntidiagonal,
            mem_IdN] at hy ⊢
          refine ⟨?_, fun p hp => ⟨hy.2.1.1 hp, ?_⟩⟩
          · rw [map_mul, norm_pr, hy.2.1.2, hy.2.2, hy.1.1]
          · exact (Finset.dvd_prod_of_mem (fun q : P K => q.1) hp).trans (dvd_mul_right _ _)
        · rintro ⟨x, S, J⟩ hy ⟨x', S', J'⟩ hy' e
          simp only [mem_sigma, mem_product, mem_filter, mem_powerset, Finset.subset_iff, Nat.mem_divisorsAntidiagonal,
            mem_IdN] at hy hy'
          simp only [Sigma.mk.injEq, heq_eq_eq] at e
          obtain ⟨e1, rfl⟩ := e
          have hJ : J = J' := mul_left_cancel₀ (pr_ne_bot S) e1
          subst hJ
          have hx : x = x' := Prod.ext (hy.2.1.2.symm.trans hy'.2.1.2) (hy.2.2.symm.trans hy'.2.2)
          subst hx
          rfl
        · rintro ⟨I, S⟩ hy
          simp only [mem_sigma, mem_filter, mem_powerset, Finset.subset_iff, mem_IdN] at hy
          have hd : pr S ∣ I := (pr_dvd_iff S I).mpr (fun p hp => (hy.2 hp).2)
          obtain ⟨J, hJ⟩ := hd
          refine ⟨⟨(N S, Ideal.absNorm J), S, J⟩, ?_, ?_⟩
          · simp only [mem_sigma, mem_product, mem_filter, mem_powerset, Finset.subset_iff,
              Nat.mem_divisorsAntidiagonal, mem_IdN]
            refine ⟨⟨?_, hn⟩, ⟨fun p hp => (hy.2 hp).1, trivial⟩, trivial⟩
            rw [← norm_pr, ← map_mul, ← hJ, hy.1]
          · simp [hJ]
        · intro y _
          rfl
    _ = ∑ I ∈ IdN (K := K) n, if I = ⊤ then (1 : ℂ) else 0 := by
        rw [Finset.sum_sigma]
        apply sum_congr rfl
        intro I hI
        rw [mem_IdN] at hI
        have h := Finset.sum_powerset_neg_one_pow_card (x := (Q (K := K) n).filter (fun p => p.1 ∣ I))
        have hc : (∑ S ∈ ((Q (K := K) n).filter (fun p => p.1 ∣ I)).powerset, (-1 : ℂ)^S.card) =
            ((∑ S ∈ ((Q (K := K) n).filter (fun p => p.1 ∣ I)).powerset, (-1 : ℤ)^S.card : ℤ) : ℂ) := by
          push_cast; rfl
        rw [hc, h]
        have he := filter_empty_iff n hn I hI
        by_cases hT : I = ⊤
        · rw [if_pos (he.mpr hT), if_pos hT]; simp
        · rw [if_neg (fun h' => hT (he.mp h')), if_neg hT]; simp
    _ = if n = 1 then 1 else 0 := by
        rw [Finset.sum_ite_eq']
        simp only [mem_IdN, Ideal.absNorm_top]
        by_cases h : n = 1
        · simp [h]
        · simp [h, Ne.symm h]

end OMAH1Help


open scoped NumberField in
theorem OMA.solution : OMA.R_ERH_extended_riemann_hypothesis_R1_H2_R1_H2_R1_H2_R1.H1 := by
  intro K _ _ P N a f z
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply,
    ← OMAH1Help.conv (K := K) n hn.ne']
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hx1, hx0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
  have h1 : x.1 ≠ 0 := fun e => hx0 (by rw [← hx1, e, zero_mul])
  have h2 : x.2 ≠ 0 := fun e => hx0 (by rw [← hx1, e, mul_zero])
  have hle : x.1 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hx0) ⟨x.2, hx1.symm⟩
  show (if x.1 = 0 then 0 else a x.1) *
    (if x.2 = 0 then 0 else (Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = x.2} : ℂ)) = _
  rw [if_neg h1, if_neg h2, OMAH1Help.card_IdN]
  congr 1
  exact OMAH1Help.a_eq x.1 n h1 hle
