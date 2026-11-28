import OMAReductions.R_Erdos535_erdos_535_R1

-- Step Erdos535.erdos_535.R1.H2: hypothesis H2 of reduction Erdos535.erdos_535.R1
-- Credit: @green-notes

open Erdos535 ArithmeticFunction Finset
open scoped Omega

private lemma cardFactors_finset_prod (T : Finset ℕ) (e : ℕ → ℕ)
    (hT : ∀ p ∈ T, Nat.Prime p) :
    Ω (∏ p ∈ T, p ^ e p) = ∑ p ∈ T, e p := by
  classical
  induction T using Finset.induction with
  | empty => simp
  | @insert p T hpT ih =>
    have hp : Nat.Prime p := hT p (mem_insert_self p T)
    have hT' : ∀ q ∈ T, Nat.Prime q := fun q hq => hT q (mem_insert_of_mem hq)
    have hne1 : p ^ e p ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hne2 : ∏ q ∈ T, q ^ e q ≠ 0 :=
      prod_ne_zero_iff.mpr fun q hq => pow_ne_zero _ (hT' q hq).ne_zero
    rw [prod_insert hpT, sum_insert hpT, cardFactors_mul hne1 hne2,
      cardFactors_apply_prime_pow hp, ih hT']

theorem OMA.solution : OMA.R_Erdos535_erdos_535_R1.H2 := by
  classical
  intro N y L K hy hNL hNK A hAN
  by_cases hAne : A.Nonempty
  · let sPart : ℕ → ℕ := fun a =>
      (a.factorization.filter (fun p => p < y)).prod (fun p e => p ^ e)
    let bPart : ℕ → ℕ := fun a =>
      (a.factorization.filter (fun p => ¬ p < y)).prod (fun p e => p ^ e)
    have hmul : ∀ a ∈ A, sPart a * bPart a = a := by
      intro a ha
      have ha1 : 1 ≤ a := (mem_Icc.mp (hAN ha)).1
      change (a.factorization.filter (fun p => p < y)).prod (fun p e => p ^ e) *
          (a.factorization.filter (fun p => ¬ p < y)).prod (fun p e => p ^ e) = a
      rw [← Finsupp.prod_add_index' (fun p : ℕ => pow_zero p) (fun p a b => pow_add p a b)]
      rw [Finsupp.filter_add_filter_not, Nat.prod_factorization_pow_eq_self (by omega)]
    have hs_pos : ∀ a ∈ A, 0 < sPart a := by
      intro a ha
      have ha1 : 1 ≤ a := (mem_Icc.mp (hAN ha)).1
      have hm := hmul a ha
      by_contra! h
      simp [Nat.eq_zero_of_le_zero h] at hm
      omega
    have hb_pos : ∀ a ∈ A, 0 < bPart a := by
      intro a ha
      have ha1 : 1 ≤ a := (mem_Icc.mp (hAN ha)).1
      have hm := hmul a ha
      by_contra! h
      simp [Nat.eq_zero_of_le_zero h] at hm
      omega
    have hfac_lt : ∀ a ∈ A, ∀ p : ℕ, a.factorization p < L + 1 := by
      intro a ha p
      have ha_range := mem_Icc.mp (hAN ha)
      have ha0 : a ≠ 0 := by omega
      by_cases hp : p ∈ a.primeFactors
      · have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
        have hdvd : p ^ a.factorization p ∣ a :=
          (hp_prime.pow_dvd_iff_le_factorization ha0).mpr le_rfl
        have hpow_le : p ^ a.factorization p ≤ a := Nat.le_of_dvd (by omega) hdvd
        have h2p : 2 ^ a.factorization p ≤ p ^ a.factorization p :=
          Nat.pow_le_pow_left hp_prime.two_le _
        have h2lt : 2 ^ a.factorization p < 2 ^ L := by omega
        have hltL : a.factorization p < L :=
          (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp h2lt
        omega
      · have hzero : a.factorization p = 0 :=
          Finsupp.notMem_support_iff.mp (by simpa only [Nat.support_factorization] using hp)
        omega
    have hΩ_le : ∀ a ∈ A, Ω (bPart a) ≤ K := by
      intro a ha
      have ha_range := mem_Icc.mp (hAN ha)
      have hb0 : 0 < bPart a := hb_pos a ha
      have hm := hmul a ha
      have hb_le : bPart a ≤ a := by
        calc bPart a = 1 * bPart a := (one_mul _).symm
          _ ≤ sPart a * bPart a := Nat.mul_le_mul_right _ (hs_pos a ha)
          _ = a := hm
      let R := a.factorization.filter (fun p => ¬ p < y)
      have hR_le : R ≤ a.factorization := by
        intro p
        dsimp [R]
        rw [Finsupp.filter_apply]
        split <;> omega
      have hR_primes : ∀ p ∈ R.support, Nat.Prime p := by
        intro p hp
        have hpos_R : R p ≠ 0 := Finsupp.mem_support_iff.mp hp
        have hpos_a : a.factorization p ≠ 0 := fun h => hpos_R (Nat.eq_zero_of_le_zero (h ▸ hR_le p))
        exact Nat.prime_of_mem_primeFactors
          (Nat.support_factorization a ▸ Finsupp.mem_support_iff.mpr hpos_a)
      have hb_eq : bPart a = ∏ p ∈ R.support, p ^ R p := rfl
      have hΩ_eq : Ω (bPart a) = ∑ p ∈ R.support, R p := by
        rw [hb_eq]
        exact cardFactors_finset_prod R.support (fun p => R p) hR_primes
      have hy_pow_le : y ^ Ω (bPart a) ≤ bPart a := by
        rw [hΩ_eq, hb_eq, ← prod_pow_eq_pow_sum]
        refine prod_le_prod' fun p hp => ?_
        have hpos_R : R p ≠ 0 := Finsupp.mem_support_iff.mp hp
        have hpy : y ≤ p := by
          dsimp [R] at hpos_R
          rw [Finsupp.filter_apply] at hpos_R
          split at hpos_R
          · omega
          · contradiction
        exact Nat.pow_le_pow_left hpy _
      have hylt : y ^ Ω (bPart a) < y ^ (K + 1) := by omega
      have hlt : Ω (bPart a) < K + 1 :=
        (Nat.pow_lt_pow_iff_right (by omega : 1 < y)).mp hylt
      omega
    let key : ℕ → (Fin y → Fin (L + 1)) × Fin (K + 1) := fun a =>
      if h : a ∈ A then
        (fun i => ⟨a.factorization i.1, hfac_lt a h i.1⟩,
         ⟨Ω (bPart a), Nat.lt_succ_of_le (hΩ_le a h)⟩)
      else (fun _ => 0, 0)
    let Kset := A.image key
    have hfib : A.card ≤ ∑ z ∈ Kset, (A.filter (fun a => key a = z)).card := by
      calc A.card = (Kset.biUnion (fun z => A.filter (fun a => key a = z))).card := by
            congr 1
            ext a
            simp only [Kset, mem_biUnion, mem_image, mem_filter]
            exact ⟨fun ha => ⟨key a, ⟨a, ha, rfl⟩, ha, rfl⟩, fun ⟨_, _, ha, _⟩ => ha⟩
        _ ≤ ∑ z ∈ Kset, (A.filter (fun a => key a = z)).card := card_biUnion_le
    obtain ⟨z₀, hz₀_mem, hz₀_max⟩ :=
      Finset.exists_max_image Kset (fun z => (A.filter (fun a => key a = z)).card)
        (hAne.image key)
    let A₀ := A.filter (fun a => key a = z₀)
    have hsum_le : ∑ z ∈ Kset, (A.filter (fun a => key a = z)).card ≤ Kset.card * A₀.card := by
      calc ∑ z ∈ Kset, (A.filter (fun a => key a = z)).card
          ≤ ∑ _z ∈ Kset, A₀.card := sum_le_sum fun z hz => hz₀_max z hz
        _ = Kset.card * A₀.card := by simp [smul_eq_mul]
    have hKset_card : Kset.card ≤ (L + 1) ^ y * (K + 1) := by
      calc Kset.card ≤ Fintype.card ((Fin y → Fin (L + 1)) × Fin (K + 1)) := card_le_univ Kset
        _ = (L + 1) ^ y * (K + 1) := by
            simp [Fintype.card_prod, Fintype.card_fin]
    obtain ⟨a₀, ha₀_mem, ha₀_key⟩ := mem_image.mp hz₀_mem
    have hs_eq : ∀ a ∈ A₀, sPart a = sPart a₀ := by
      intro a ha
      have haA : a ∈ A := (mem_filter.mp ha).1
      have hkey : key a = key a₀ := (mem_filter.mp ha).2.trans ha₀_key.symm
      have hf1 : ∀ i : Fin y, (key a).1 i = (key a₀).1 i := fun i => congrArg (fun x => x.1 i) hkey
      have hfilt : a.factorization.filter (fun p => p < y) =
          a₀.factorization.filter (fun p => p < y) := by
        ext p
        rw [Finsupp.filter_apply, Finsupp.filter_apply]
        split_ifs with hp
        · have hfi := congrArg Fin.val (hf1 ⟨p, hp⟩)
          dsimp only [key] at hfi
          rw [dif_pos haA, dif_pos ha₀_mem] at hfi
          exact hfi
        · rfl
      exact congrArg (fun F : ℕ →₀ ℕ => F.prod (fun p e => p ^ e)) hfilt
    have hΩ_eq : ∀ a ∈ A₀, Ω (bPart a) = Ω (bPart a₀) := by
      intro a ha
      have haA : a ∈ A := (mem_filter.mp ha).1
      have hkey : key a = key a₀ := (mem_filter.mp ha).2.trans ha₀_key.symm
      have hf2 := congrArg Fin.val (congrArg Prod.snd hkey)
      dsimp only [key] at hf2
      rw [dif_pos haA, dif_pos ha₀_mem] at hf2
      exact hf2
    let B := A₀.image bPart
    have hinj : Set.InjOn bPart (A₀ : Set ℕ) := by
      intro a₁ ha₁ a₂ ha₂ heq
      have ha₁A : a₁ ∈ A := (mem_filter.mp (mem_coe.mp ha₁)).1
      have ha₂A : a₂ ∈ A := (mem_filter.mp (mem_coe.mp ha₂)).1
      calc a₁ = sPart a₁ * bPart a₁ := (hmul a₁ ha₁A).symm
        _ = sPart a₀ * bPart a₁ := by rw [hs_eq a₁ (mem_coe.mp ha₁)]
        _ = sPart a₀ * bPart a₂ := by rw [heq]
        _ = sPart a₂ * bPart a₂ := by rw [hs_eq a₂ (mem_coe.mp ha₂)]
        _ = a₂ := hmul a₂ ha₂A
    have hB_card : B.card = A₀.card := card_image_of_injOn hinj
    refine ⟨sPart a₀, Ω (bPart a₀), B, hs_pos a₀ ha₀_mem, hΩ_le a₀ ha₀_mem, ?_, ?_, ?_⟩
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
      have haA : a ∈ A := (mem_filter.mp ha).1
      exact ⟨hb_pos a haA, hΩ_eq a ha⟩
    · calc A.card ≤ Kset.card * A₀.card := hfib.trans hsum_le
        _ ≤ ((L + 1) ^ y * (K + 1)) * A₀.card := Nat.mul_le_mul_right _ hKset_card
        _ = (L + 1) ^ y * (K + 1) * B.card := by rw [hB_card]
    · intro b hb
      obtain ⟨a, ha, rfl⟩ := mem_image.mp hb
      have haA : a ∈ A := (mem_filter.mp ha).1
      rw [← hs_eq a ha, hmul a haA]
      exact haA
  · rw [not_nonempty_iff_eq_empty] at hAne
    subst hAne
    refine ⟨1, 0, ∅, Nat.one_pos, Nat.zero_le _, ?_, by simp, ?_⟩
    · intro b hb
      simp at hb
    · intro b hb
      simp at hb
