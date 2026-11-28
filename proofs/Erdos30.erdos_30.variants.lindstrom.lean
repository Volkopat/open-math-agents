import FormalConjectures.ErdosProblems.«30»
lemma oma_sum_ge_of_pos (D : Finset ℕ) (hD : ∀ x ∈ D, 1 ≤ x) :
    D.card * (D.card + 1) ≤ 2 * ∑ x ∈ D, x := by
  let e := D.orderIsoOfFin rfl
  have hge (i : ℕ) : (hi : i < D.card) → i + 1 ≤ (e ⟨i, hi⟩ : ℕ) := by
    induction i with
    | zero => exact fun hi => hD _ (e ⟨0, hi⟩).2
    | succ i ih =>
      intro hi
      have hi' : i < D.card := by omega
      have h1 := ih hi'
      have h2 : (e ⟨i, hi'⟩ : ℕ) < (e ⟨i + 1, hi⟩ : ℕ) :=
        e.strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self i))
      omega
  have hsum : ∑ x ∈ D, x = ∑ i : Fin D.card, (e i : ℕ) := by
    rw [← Finset.sum_coe_sort D (fun x => x)]
    exact (Fintype.sum_equiv e.toEquiv (fun i => (e i : ℕ)) (fun x : ↥D => (x : ℕ)) fun _ => rfl).symm
  have hle : ∑ i : Fin D.card, (i.val + 1) ≤ ∑ x ∈ D, x :=
    hsum ▸ Finset.sum_le_sum fun i _ => hge i.val i.isLt
  have hid : 2 * ∑ i : Fin D.card, (i.val + 1) = D.card * (D.card + 1) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => i + 1)]
    induction D.card with
    | zero => simp
    | succ m ih => rw [Finset.sum_range_succ, mul_add, ih]; ring
  omega

lemma oma_sidon_lindstrom (N : ℕ) (A : Finset ℕ) (hA : A ⊆ Finset.Icc 1 N) (hS : IsSidon (A : Set ℕ)) :
    (A.card : ℝ) ≤ (N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1 := by
  by_cases hN0 : N = 0
  · subst hN0; simp [Finset.subset_empty.mp (by simpa using hA)]
  have hNreal : (0 : ℝ) < N := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN0)
  set k := A.card
  set u : ℝ := (N : ℝ) ^ (4⁻¹ : ℝ)
  set r : ℕ := Nat.floor u + 1
  have hu_nn : 0 ≤ u := by positivity
  have hr_gt : u < r := by exact_mod_cast Nat.lt_floor_add_one u
  have hr_le : (r : ℝ) ≤ u + 1 := by have := Nat.floor_le hu_nn; push_cast [r]; linarith
  by_cases hkr : k ≤ r
  · have : (k : ℝ) ≤ r := Nat.cast_le.mpr hkr
    linarith [Real.sqrt_nonneg N]
  have hrk : r < k := by omega
  let e := A.orderIsoOfFin rfl
  let a : Fin k → ℕ := fun i => (e i : ℕ)
  have ha_mono : StrictMono a := fun _ _ h => e.strictMono h
  have ha_mem (i : Fin k) : a i ∈ A := (e i).2
  have ha_le (i : Fin k) : a i ≤ N := (Finset.mem_Icc.mp (hA (ha_mem i))).2
  let row (d : ℕ) := (Finset.range (k - d)).image fun j => (d, j)
  let P : Finset (ℕ × ℕ) := (Finset.Icc 1 r).biUnion row
  have hdisj : (Finset.Icc 1 r : Set ℕ).PairwiseDisjoint row := fun d₁ _ d₂ _ hne =>
    Finset.disjoint_left.mpr fun _ h1 h2 => by
      obtain ⟨_, _, e1⟩ := Finset.mem_image.mp h1
      obtain ⟨_, _, e2⟩ := Finset.mem_image.mp h2
      exact hne (congrArg Prod.fst (e1.trans e2.symm))
  have hP_mem (p : ℕ × ℕ) (hp : p ∈ P) : 1 ≤ p.1 ∧ p.1 ≤ r ∧ p.2 + p.1 < k := by
    rcases p with ⟨d, j⟩
    simp only [P, row, Finset.mem_biUnion, Finset.mem_Icc, Finset.mem_image, Finset.mem_range] at hp
    rcases hp with ⟨d', ⟨hd1, hd2⟩, j', hj', heq⟩
    rcases Prod.ext_iff.mp heq with ⟨rfl, rfl⟩
    exact ⟨hd1, hd2, by omega⟩
  let diffFn (p : ℕ × ℕ) : ℕ := if h : p.2 + p.1 < k then a ⟨p.2 + p.1, h⟩ - a ⟨p.2, by omega⟩ else 0
  have hdiff_inj : Set.InjOn diffFn (P : Set (ℕ × ℕ)) := by
    intro ⟨d₁, j₁⟩ h1 ⟨d₂, j₂⟩ h2 heq
    have hm1 := hP_mem _ (Finset.mem_coe.mp h1)
    have hm2 := hP_mem _ (Finset.mem_coe.mp h2)
    simp only [diffFn, dif_pos hm1.2.2, dif_pos hm2.2.2] at heq
    have hpair := Finset.IsSidon.eq_of_tsub hS
      (ha_mem ⟨j₁ + d₁, hm1.2.2⟩) (ha_mem ⟨j₁, by omega⟩)
      (ha_mem ⟨j₂ + d₂, hm2.2.2⟩) (ha_mem ⟨j₂, by omega⟩)
      (ha_mono (Fin.mk_lt_mk.mpr (by omega))) (ha_mono (Fin.mk_lt_mk.mpr (by omega))) heq
    have hj := congrArg Fin.val (ha_mono.injective hpair.2)
    have hjd := congrArg Fin.val (ha_mono.injective hpair.1)
    simp only at hj hjd; ext <;> omega
  have htri : ∑ d ∈ Finset.Icc 1 r, d = r * (r + 1) / 2 := by
    suffices 2 * ∑ d ∈ Finset.Icc 1 r, d = r * (r + 1) by omega
    induction r with
    | zero => simp
    | succ m ih => rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]; ring
  let D := P.image diffFn
  have hD_pos (x : ℕ) (hx : x ∈ D) : 1 ≤ x := by
    obtain ⟨⟨d, j⟩, hp, rfl⟩ := Finset.mem_image.mp hx
    have hm := hP_mem (d, j) hp
    have := ha_mono (Fin.mk_lt_mk.mpr (by omega) : (⟨j, by omega⟩ : Fin k) < ⟨j + d, hm.2.2⟩)
    simp only [diffFn, dif_pos hm.2.2]; omega
  have hP_card : P.card = r * k - r * (r + 1) / 2 := by
    rw [Finset.card_biUnion hdisj]
    have hterm (d : ℕ) (_ : d ∈ Finset.Icc 1 r) : (row d).card = k - d := by
      rw [Finset.card_image_of_injective _ fun _ _ h => congrArg Prod.snd h, Finset.card_range]
    rw [Finset.sum_congr rfl hterm]
    have h1 : ∑ d ∈ Finset.Icc 1 r, (k - d) + ∑ d ∈ Finset.Icc 1 r, d = r * k := by
      rw [← Finset.sum_add_distrib]
      refine (Finset.sum_congr rfl fun d hd => Nat.sub_add_cancel ?_).trans (by simp [Nat.card_Icc])
      have := (Finset.mem_Icc.mp hd).2; omega
    rw [htri] at h1; exact eq_tsub_of_add_eq h1
  have h_upper : ∑ p ∈ P, diffFn p ≤ (r * (r + 1) / 2) * N := by
    rw [Finset.sum_biUnion hdisj, ← htri, Finset.sum_mul]
    refine Finset.sum_le_sum fun d hd => ?_
    have hdr := (Finset.mem_Icc.mp hd).2
    rw [Finset.sum_image fun _ _ _ _ h => congrArg Prod.snd h]
    let a' (i : ℕ) : ℝ := if h : i < k then (a ⟨i, h⟩ : ℝ) else 0
    have hcast : ((∑ j ∈ Finset.range (k - d), diffFn (d, j) : ℕ) : ℝ) =
        ∑ j ∈ Finset.range (k - d), (a' (j + d) - a' j) := by
      rw [Nat.cast_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mem_range] at hj
      have hjd : j + d < k := by omega
      have hj' : j < k := by omega
      simp only [diffFn, dif_pos hjd, a', dif_pos hj']
      exact Nat.cast_sub (ha_mono.monotone (Fin.mk_le_mk.mpr (by omega)))
    suffices ((∑ j ∈ Finset.range (k - d), diffFn (d, j) : ℕ) : ℝ) ≤ (d : ℝ) * N by exact_mod_cast this
    rw [hcast, Finset.sum_sub_distrib]
    have hshift : ∑ j ∈ Finset.range (k - d), a' (j + d) = ∑ i ∈ Finset.Ico d k, a' i :=
      Finset.sum_bij (fun j _ => j + d)
        (fun j hj => by rw [Finset.mem_range] at hj; rw [Finset.mem_Ico]; omega)
        (fun _ _ _ _ h => by omega)
        (fun i hi => by rw [Finset.mem_Ico] at hi; exact ⟨i - d, Finset.mem_range.mpr (by omega), by omega⟩)
        (fun _ _ => rfl)
    rw [hshift, ← Finset.sum_inter_add_sum_sdiff (Finset.Ico d k) (Finset.range (k - d)),
      ← Finset.sum_inter_add_sum_sdiff (Finset.range (k - d)) (Finset.Ico d k),
      Finset.inter_comm (Finset.range (k - d))]
    have hnn : 0 ≤ ∑ i ∈ Finset.range (k - d) \ Finset.Ico d k, a' i :=
      Finset.sum_nonneg fun i _ => by dsimp [a']; split_ifs <;> positivity
    have hsub : Finset.Ico d k \ Finset.range (k - d) ⊆ Finset.Ico (k - d) k := fun x hx => by
      simp only [Finset.mem_sdiff, Finset.mem_Ico, Finset.mem_range] at hx ⊢; omega
    have hcle : (Finset.Ico d k \ Finset.range (k - d)).card ≤ d := by
      have := Finset.card_le_card hsub; rw [Nat.card_Ico] at this; omega
    have hbnd : ∑ i ∈ Finset.Ico d k \ Finset.range (k - d), a' i ≤
        (Finset.Ico d k \ Finset.range (k - d)).card * (N : ℝ) := by
      refine (Finset.sum_le_sum fun i hi => (?_ : a' i ≤ N)).trans_eq (by simp)
      have hik := (Finset.mem_Ico.mp (Finset.mem_sdiff.mp hi).1).2
      simp only [a', dif_pos hik]; exact_mod_cast ha_le ⟨i, hik⟩
    have : ((Finset.Ico d k \ Finset.range (k - d)).card : ℝ) ≤ d := Nat.cast_le.mpr hcle
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have h_lower := oma_sum_ge_of_pos D hD_pos
  rw [Finset.card_image_of_injOn hdiff_inj, Finset.sum_image fun _ hx _ hy h => hdiff_inj hx hy h] at h_lower
  have heven : 2 ∣ r * (r + 1) := (Nat.even_mul_succ_self r).two_dvd
  have hineq_nat : P.card * (P.card + 1) ≤ r * (r + 1) * N := by
    have : 2 * (r * (r + 1) / 2 * N) = r * (r + 1) * N := by rw [← mul_assoc, Nat.mul_div_cancel' heven]
    linarith
  have hP_real : (P.card : ℝ) = r * (k : ℝ) - r * (r + 1) / 2 := by
    have hle : r * (r + 1) / 2 ≤ r * k := Nat.div_le_of_le_mul (by nlinarith)
    rw [hP_card, Nat.cast_sub hle, Nat.cast_div heven (by norm_num)]; push_cast; ring
  have hineq_real : (P.card : ℝ) ^ 2 ≤ r * (r + 1) * N := by
    have : (P.card : ℝ) * (P.card + 1) ≤ r * (r + 1) * N := by exact_mod_cast hineq_nat
    nlinarith [Nat.cast_nonneg (α := ℝ) P.card]
  by_contra! hgt
  have hu2 : u ^ 2 = (N : ℝ).sqrt := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast u 2, ← Real.rpow_mul hNreal.le]; norm_num
  have hsqN : (N : ℝ).sqrt ^ 2 = N := Real.sq_sqrt hNreal.le
  have hr_pos : (0 : ℝ) < r := Nat.cast_pos.mpr (by omega)
  have hP_gt : (r : ℝ) * ((N : ℝ).sqrt + u / 2) < P.card := by rw [hP_real]; nlinarith
  have h1 : ((r : ℝ) * ((N : ℝ).sqrt + u / 2)) ^ 2 < (P.card : ℝ) ^ 2 := by
    nlinarith [show 0 ≤ (r : ℝ) * ((N : ℝ).sqrt + u / 2) by positivity]
  have hru : (N : ℝ) < r * u * (N : ℝ).sqrt := by
    have hNeq : (N : ℝ) = u * u * (N : ℝ).sqrt := by
      calc (N : ℝ) = ((N : ℝ).sqrt) ^ 2 := hsqN.symm
        _ = (N : ℝ).sqrt * (N : ℝ).sqrt := sq _
        _ = u ^ 2 * (N : ℝ).sqrt := by rw [hu2]
        _ = u * u * (N : ℝ).sqrt := by ring
    nlinarith [Real.rpow_pos_of_pos hNreal (4⁻¹ : ℝ), Real.sqrt_pos.mpr hNreal]
  nlinarith [show ((r : ℝ) * ((N : ℝ).sqrt + u / 2)) ^ 2 = r ^ 2 * (N + u * (N : ℝ).sqrt + u ^ 2 / 4) by
    linear_combination (r : ℝ) ^ 2 * hsqN, show 0 ≤ (r : ℝ) ^ 2 * (u ^ 2 / 4) by positivity]

theorem OMA.solution : type_of% @Erdos30.erdos_30.variants.lindstrom := by
  intro N
  dsimp [Erdos30.h, Finset.maxSidonSubsetCard]
  have hsup : ((Finset.Icc 1 N).powerset.filter fun B : Finset ℕ => IsSidon (B : Set ℕ)).sup
      Finset.card ≤ Nat.floor ((N : ℝ).sqrt + (N : ℝ) ^ (4⁻¹ : ℝ) + 1) :=
    Finset.sup_le fun B hB => by
      rw [Finset.mem_filter, Finset.mem_powerset] at hB
      exact Nat.le_floor (oma_sidon_lindstrom N B hB.1 hB.2)
  exact (Nat.cast_le (α := ℝ).mpr hsup).trans (Nat.floor_le (by positivity))
