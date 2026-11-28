import FormalConjectures.ErdosProblems.«789»

open Erdos789 Filter Finset in
open scoped Asymptotics in
theorem OMA.solution : type_of% @Erdos789.erdos_789.variants.isBigO_sq := by
  refine Asymptotics.isBigO_iff.2 ⟨3, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  simp only [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) _),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  have hatt : IsSubsetSumSeparatingCard n (subsetSumThreshold n) :=
    Nat.sSup_mem (s := {m | IsSubsetSumSeparatingCard n m})
    ⟨0, fun _ _ => ⟨∅, empty_subset _, Nat.zero_le _, fun _ hT _ hS _ _ _ => by
      rw [subset_empty.1 hT, subset_empty.1 hS]⟩⟩
    ⟨n, fun m hm => by
      obtain ⟨A, hA⟩ := Infinite.exists_subset_card_eq ℤ n
      obtain ⟨B, hBA, hc, _⟩ := hm A hA
      exact hc.trans ((card_le_card hBA).trans_eq hA)⟩
  obtain ⟨B, hBA, hm, hB⟩ := hatt (Icc (1 : ℤ) n) (by simp [Int.card_Icc])
  let m := B.card
  refine (show (subsetSumThreshold n : ℝ) ≤ m by exact_mod_cast hm).trans ?_
  by_cases hm0 : m = 0
  · rw [hm0, Nat.cast_zero]; positivity
  have hmp : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero hm0
  let L (C : Finset ℤ) (k : ℕ) := (C.powersetCard k).image fun T => ∑ x ∈ T, x
  have hmono {C D : Finset ℤ} (h : C ⊆ D) (k : ℕ) : L C k ⊆ L D k := fun z hz => by
    obtain ⟨T, hT, rfl⟩ := mem_image.1 hz; obtain ⟨hTC, hk⟩ := mem_powersetCard.1 hT
    exact mem_image.2 ⟨T, mem_powersetCard.2 ⟨hTC.trans h, hk⟩, rfl⟩
  have hlowB : ∀ (C : Finset ℤ) (k : ℕ), k ≤ C.card → k * (C.card - k) + 1 ≤ (L C k).card := by
    intro C; induction C using strongInductionOn with
    | _ C ih =>
      intro k hk
      by_cases heq : k = C.card
      · have hne : (L C k).Nonempty :=
          ⟨∑ x ∈ C, x, mem_image.2 ⟨C, mem_powersetCard.2 ⟨Subset.rfl, heq.symm⟩, rfl⟩⟩
        have := card_pos.2 hne; subst heq; simp; omega
      have hne : C.Nonempty := card_pos.1 (by omega)
      let x := C.max' hne; have hx : x ∈ C := C.max'_mem hne
      let E := C.erase x
      have hc : E ⊆ C := erase_subset _ _
      have hcard : E.card + 1 = C.card := card_erase_add_one hx
      have hk' : k ≤ E.card := by omega
      have hTne : (E.powersetCard k).Nonempty :=
        card_pos.1 (by rw [card_powersetCard]; exact Nat.choose_pos hk')
      obtain ⟨T, hT, hTm⟩ := exists_max_image (E.powersetCard k) (fun U => ∑ z ∈ U, z) hTne
      obtain ⟨hTE, hTk⟩ := mem_powersetCard.1 hT
      let D := T.image fun y => (∑ z ∈ T, z) + x - y
      have hDc : D.card = k := by
        rw [card_image_of_injective _ fun a b h => by linarith, hTk]
      have hDsub : D ⊆ L C k := fun z hz => by
        obtain ⟨y, hy, rfl⟩ := mem_image.1 hz
        have hxT : x ∉ T := fun h => (mem_erase.1 (hTE h)).1 rfl
        have hxU : x ∉ T.erase y := fun h => hxT (mem_of_mem_erase h)
        refine mem_image.2 ⟨insert x (T.erase y), mem_powersetCard.2
          ⟨insert_subset hx ((erase_subset _ _).trans (hTE.trans hc)),
            by rw [card_insert_of_notMem hxU, card_erase_add_one hy, hTk]⟩,
          by rw [sum_insert hxU]; linarith [sum_erase_add T (fun z : ℤ => z) hy]⟩
      have hdis : Disjoint (L E k) D := disjoint_left.2 fun z hz hDz => by
        obtain ⟨U, hU, rfl⟩ := mem_image.1 hz; obtain ⟨y, hy, he⟩ := mem_image.1 hDz
        obtain ⟨hyx, hyC⟩ := mem_erase.1 (hTE hy)
        have := lt_of_le_of_ne (C.le_max' _ hyC) hyx; have := hTm U hU; linarith
      have hsum := card_le_card (union_subset (hmono hc k) hDsub)
      rw [card_union_of_disjoint hdis, hDc] at hsum
      have := ih E (erase_ssubset hx) k hk'
      rw [show C.card - k = E.card - k + 1 by omega, Nat.mul_add, Nat.mul_one]; omega
  have hdisj : ((range m : Finset ℕ) : Set ℕ).PairwiseDisjoint fun k => L B (k + 1) :=
    fun j _ k _ hjk => disjoint_left.2 fun z hzj hzk => by
      obtain ⟨T, hT, hj⟩ := mem_image.1 hzj; obtain ⟨S, hS, hk⟩ := mem_image.1 hzk
      obtain ⟨hTB, hTc⟩ := mem_powersetCard.1 hT; obtain ⟨hSB, hSc⟩ := mem_powersetCard.1 hS
      have := hB T hTB S hSB (card_pos.1 (by omega)) (card_pos.1 (by omega)) (hj.trans hk.symm)
      omega
  have hint : (range m).biUnion (fun k => L B (k + 1)) ⊆ Icc (1 : ℤ) (m * n) := fun z hz => by
    obtain ⟨k, _, hz⟩ := mem_biUnion.1 hz; obtain ⟨T, hT, rfl⟩ := mem_image.1 hz
    obtain ⟨hTB, hTc⟩ := mem_powersetCard.1 hT
    have hlo : (T.card : ℤ) ≤ ∑ x ∈ T, x := by
      simpa using sum_le_sum fun x hx => (mem_Icc.1 (hBA (hTB hx))).1
    have hhi : ∑ x ∈ T, x ≤ T.card * (n : ℤ) := by
      simpa using sum_le_sum fun x hx => (mem_Icc.1 (hBA (hTB hx))).2
    have hTl : (T.card : ℤ) ≤ m := by exact_mod_cast card_le_card hTB
    exact mem_Icc.2 ⟨by omega, hhi.trans (mul_le_mul_of_nonneg_right hTl (by positivity))⟩
  have hcap : (∑ k ∈ range m, ((L B (k + 1)).card : ℝ)) ≤ m * n := by
    have h1 := card_le_card hint; rw [card_biUnion hdisj] at h1
    have h2 : (Icc (1 : ℤ) (m * n)).card = m * n := by
      rw [Int.card_Icc, add_sub_cancel_right, ← Int.natCast_mul, Int.toNat_natCast]
    rw [h2] at h1; exact_mod_cast h1
  have hlow : (∑ k ∈ range m, ((k + 1 : ℕ) : ℝ) * (m - (k + 1 : ℕ))) ≤
      ∑ k ∈ range m, ((L B (k + 1)).card : ℝ) := sum_le_sum fun k hk => by
    have hkm : k + 1 ≤ m := Nat.succ_le_of_lt (mem_range.1 hk)
    have hb := hlowB B (k + 1) hkm
    have hc : (((k + 1) * (m - (k + 1)) : ℕ) : ℝ) ≤ (L B (k + 1)).card := by
      exact_mod_cast (Nat.mul_le_mul_left (k + 1)
        (Nat.sub_le_sub_right (show m ≤ B.card by omega) (k + 1))).trans (by omega)
    rwa [Nat.cast_mul, Nat.cast_sub hkm] at hc
  have htel : (6 : ℝ) * ∑ k ∈ range m, ((k + 1 : ℕ) : ℝ) * (m - (k + 1 : ℕ)) = m * (m ^ 2 - 1) := by
    let F (j : ℕ) : ℝ := j * (j + 1) * (3 * m - 2 * j - 1)
    rw [mul_sum, sum_congr rfl fun k _ => show (6 : ℝ) * (((k + 1 : ℕ) : ℝ) * (m - (k + 1 : ℕ))) =
      F (k + 1) - F k by dsimp [F]; push_cast; ring, sum_range_sub F m]
    dsimp [F]; ring
  have hbig := mul_le_mul_of_nonneg_left (hlow.trans hcap) (by norm_num : (0 : ℝ) ≤ 6)
  rw [htel] at hbig
  have hsm : (m : ℝ) ^ 2 - 1 ≤ 6 * n := (mul_le_mul_iff_left₀ hmp).1 (by linarith)
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  exact (sq_le_sq₀ hmp.le (by positivity)).1
    (by rw [mul_pow, Real.sq_sqrt (by positivity)]; linarith only [hsm, hn'])
