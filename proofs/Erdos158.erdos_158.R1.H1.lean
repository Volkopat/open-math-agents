import OMAReductions.R_Erdos158_erdos_158_R1

/-!
# Proof of `Erdos158.erdos_158.R1.H1`

Proves Erdős's theorem that every infinite Sidon set `A ⊆ ℕ` satisfies
`liminf (fun N : ℕ => (A ∩ .Iio N).ncard * (N : ℝ) ^ (-1 / 2 : ℝ)) atTop = 0`.

Suppose for contradiction that the `liminf` is strictly positive, so there exist `c > 0` and
`N₀ : ℕ` with `|A ∩ [0, N)| ≥ c * √N` for all `N ≥ N₀`.
1. Since `A` is a Sidon set, positive differences `y - x` (`x < y`, `x, y ∈ A`) are pairwise
   distinct. Partitioning `[0, M * D)` into `M` blocks `B_m = [m * D, (m + 1) * D)` of length `D`
   with counts `b_m = |A ∩ B_m|`, every ordered pair `x < y` in `A ∩ B_m` gives a distinct
   difference in `{1, ..., D - 1}`, yielding `∑_{m < M} b_m^2 ≤ 2 * D + |A ∩ [0, M * D)|`.
2. Taking `M = 1` gives `|A ∩ [0, N)|^2 ≤ 2 * N + |A ∩ [0, N)|`, hence `|A ∩ [0, N)| ≤ 2 * √N`
   for all `N ≥ 1`.
3. Choosing `K ≥ 16 / c^2 + 2`, `J > 16 / c^2`, and `D = max (max N₀ 1) (K ^ J)`, the Sidon
   block bound caps `∑_{m < K^J} b_m^2 ≤ 4 * D`. On the other hand, on each of the `J` disjoint
   dyadic-like scales `m ∈ [K^j, K^(j + 1))` (`0 ≤ j < J`), we have
   `∑_{m ∈ [K^j, K^(j + 1))} b_m ≥ c * √(D * K^(j + 1)) - 2 * √(D * K^j) ≥ (c / 2) * √(D * K^(j + 1))`,
   so Cauchy-Schwarz gives `∑_{m ∈ [K^j, K^(j + 1))} b_m^2 ≥ (c^2 / 4) * D`.
   Summing over all `J` scales yields `J * (c^2 / 4) * D ≤ 4 * D`, contradicting `16 < c^2 * J`.
-/

namespace Erdos158R1H1Proof

open Filter Real
open scoped Classical

private noncomputable def prefixFin (A : Set ℕ) (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (· ∈ A)

private noncomputable def blockFin (A : Set ℕ) (D m : ℕ) : Finset ℕ :=
  (Finset.Ico (m * D) ((m + 1) * D)).filter (· ∈ A)

private noncomputable def orderedPairs (S : Finset ℕ) : Finset (ℕ × ℕ) :=
  S.offDiag.filter (fun p => p.1 < p.2)

private lemma ncard_inter_Iio_eq_card_prefixFin (A : Set ℕ) (N : ℕ) :
    (A ∩ Set.Iio N).ncard = (prefixFin A N).card := by
  rw [← Set.ncard_coe_finset (prefixFin A N)]
  congr 1
  ext x
  simp [prefixFin, Set.mem_Iio, and_comm]

private lemma card_sq_eq_two_mul_orderedPairs_add_card (S : Finset ℕ) :
    S.card * S.card = 2 * (orderedPairs S).card + S.card := by
  let ltSet := S.offDiag.filter (fun p => p.1 < p.2)
  let gtSet := S.offDiag.filter (fun p => p.2 < p.1)
  have hunion : S.offDiag = ltSet ∪ gtSet := by
    ext p
    simp only [ltSet, gtSet, Finset.mem_union, Finset.mem_filter, Finset.mem_offDiag]
    constructor
    · rintro ⟨h1, h2, hne⟩
      rcases lt_or_gt_of_ne hne with h | h
      · exact Or.inl ⟨⟨h1, h2, hne⟩, h⟩
      · exact Or.inr ⟨⟨h1, h2, hne⟩, h⟩
    · rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
  have hdisj : Disjoint ltSet gtSet :=
    Finset.disjoint_filter.mpr (fun _ _ h1 h2 => by omega)
  have hswap : ltSet.card = gtSet.card := by
    refine Finset.card_bij (fun p _ => p.swap) ?_ ?_ ?_
    · intro p hp
      simp only [ltSet, gtSet, Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
      exact ⟨⟨hp.1.2.1, hp.1.1, hp.1.2.2.symm⟩, hp.2⟩
    · intro p _ q _ h
      exact Prod.swap_inj.mp h
    · intro p hp
      refine ⟨p.swap, ?_, Prod.swap_swap p⟩
      simp only [ltSet, gtSet, Finset.mem_filter, Finset.mem_offDiag] at hp ⊢
      exact ⟨⟨hp.1.2.1, hp.1.1, hp.1.2.2.symm⟩, hp.2⟩
  have hoff : S.offDiag.card = 2 * (orderedPairs S).card := by
    rw [hunion, Finset.card_union_of_disjoint hdisj, ← hswap]
    change ltSet.card + ltSet.card = 2 * ltSet.card
    omega
  have hcard : S.offDiag.card = S.card * S.card - S.card := Finset.offDiag_card S
  have hle : S.card ≤ S.card * S.card := Nat.le_mul_self S.card
  omega

private lemma blockFin_pairwiseDisjoint (A : Set ℕ) (D : ℕ) :
    Set.PairwiseDisjoint (Set.univ : Set ℕ) (blockFin A D) := by
  intro m₁ _ m₂ _ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  simp only [blockFin, Finset.mem_filter, Finset.mem_Ico] at hx₁ hx₂
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : (m₁ + 1) * D ≤ m₂ * D := Nat.mul_le_mul_right D (by omega)
    omega
  · have hle : (m₂ + 1) * D ≤ m₁ * D := Nat.mul_le_mul_right D (by omega)
    omega

private lemma prefixFin_eq_biUnion_blockFin (A : Set ℕ) {D : ℕ} (hD : 0 < D) (M : ℕ) :
    prefixFin A (M * D) = (Finset.range M).biUnion (blockFin A D) := by
  ext x
  simp only [prefixFin, blockFin, Finset.mem_filter, Finset.mem_range, Finset.mem_biUnion,
    Finset.mem_Ico]
  constructor
  · rintro ⟨hxM, hxA⟩
    refine ⟨x / D, ?_, ?_, hxA⟩
    · have hlt : x < D * M := by linarith
      exact Nat.div_lt_of_lt_mul hlt
    · refine ⟨Nat.div_mul_le_self x D, ?_⟩
      have hdiv := Nat.div_add_mod x D
      have hmod := Nat.mod_lt x hD
      have h1 : (x / D + 1) * D = D * (x / D) + D := by ring
      omega
  · rintro ⟨m, hm, ⟨_, hxu⟩, hxA⟩
    have hle : (m + 1) * D ≤ M * D := Nat.mul_le_mul_right D (by omega)
    exact ⟨lt_of_lt_of_le hxu hle, hxA⟩

private lemma card_prefixFin_eq_sum_blockFin (A : Set ℕ) {D : ℕ} (hD : 0 < D) (M : ℕ) :
    (prefixFin A (M * D)).card = ∑ m ∈ Finset.range M, (blockFin A D m).card := by
  rw [prefixFin_eq_biUnion_blockFin A hD M]
  exact Finset.card_biUnion (fun m₁ _ m₂ _ hne =>
    blockFin_pairwiseDisjoint A D (Set.mem_univ m₁) (Set.mem_univ m₂) hne)

private lemma sidon_sum_sq_blockFin_le {A : Set ℕ} (hAsid : IsSidon A)
    {D : ℕ} (hD : 0 < D) (M : ℕ) :
    ∑ m ∈ Finset.range M, (blockFin A D m).card ^ 2 ≤
      2 * D + (prefixFin A (M * D)).card := by
  let U : Finset (ℕ × ℕ) := (Finset.range M).biUnion (fun m => orderedPairs (blockFin A D m))
  have hdisj_pairs :
      (↑(Finset.range M) : Set ℕ).PairwiseDisjoint (fun m => orderedPairs (blockFin A D m)) := by
    intro m₁ _ m₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p hp₁ hp₂
    simp only [orderedPairs, Finset.mem_filter, Finset.mem_offDiag] at hp₁ hp₂
    exact Finset.disjoint_left.mp
      (blockFin_pairwiseDisjoint A D (Set.mem_univ m₁) (Set.mem_univ m₂) hne)
      hp₁.1.1 hp₂.1.1
  have hU_card : U.card = ∑ m ∈ Finset.range M, (orderedPairs (blockFin A D m)).card :=
    Finset.card_biUnion hdisj_pairs
  have hU_le : U.card ≤ D := by
    have hsub : U.image (fun p => p.2 - p.1) ⊆ Finset.Ico 1 D := by
      intro d hd
      rcases Finset.mem_image.mp hd with ⟨p, hp, rfl⟩
      rcases Finset.mem_biUnion.mp hp with ⟨m, _, hpm⟩
      simp only [orderedPairs, blockFin, Finset.mem_filter, Finset.mem_offDiag, Finset.mem_Ico] at hpm
      simp only [Finset.mem_Ico]
      have h1 : m * D ≤ p.1 := hpm.1.1.1.1
      have h2 : p.2 < (m + 1) * D := hpm.1.2.1.1.2
      have hlt : p.1 < p.2 := hpm.2
      have hexp : (m + 1) * D = m * D + D := by ring
      omega
    have hinj : Set.InjOn (fun p : ℕ × ℕ => p.2 - p.1) (↑U : Set (ℕ × ℕ)) := by
      intro p hp q hq heq
      rcases Finset.mem_biUnion.mp hp with ⟨mp, _, hpm⟩
      rcases Finset.mem_biUnion.mp hq with ⟨mq, _, hqm⟩
      simp only [orderedPairs, blockFin, Finset.mem_filter, Finset.mem_offDiag] at hpm hqm
      have hp1A : p.1 ∈ A := hpm.1.1.2
      have hp2A : p.2 ∈ A := hpm.1.2.1.2
      have hq1A : q.1 ∈ A := hqm.1.1.2
      have hq2A : q.2 ∈ A := hqm.1.2.1.2
      have hplt : p.1 < p.2 := hpm.2
      have hqlt : q.1 < q.2 := hqm.2
      dsimp only at heq
      have hsum : p.2 + q.1 = q.2 + p.1 := by omega
      have hsid := hAsid p.2 hp2A q.2 hq2A q.1 hq1A p.1 hp1A hsum
      rcases hsid with ⟨h1, h2⟩ | ⟨h1, _⟩
      · exact Prod.ext h2.symm h1
      · omega
    have himg_card : (U.image (fun p => p.2 - p.1)).card = U.card :=
      Finset.card_image_of_injOn hinj
    have hle_ico : U.card ≤ (Finset.Ico 1 D).card := by
      rw [← himg_card]
      exact Finset.card_le_card hsub
    simp only [Nat.card_Ico] at hle_ico
    omega
  have hsum_sq :
      ∑ m ∈ Finset.range M, (blockFin A D m).card ^ 2 =
        2 * U.card + (prefixFin A (M * D)).card := by
    rw [hU_card, card_prefixFin_eq_sum_blockFin A hD M, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [sq, card_sq_eq_two_mul_orderedPairs_add_card]
  omega

private lemma sidon_prefixFin_le_two_sqrt {A : Set ℕ} (hAsid : IsSidon A)
    {N : ℕ} (hN : 1 ≤ N) :
    ((prefixFin A N).card : ℝ) ≤ 2 * Real.sqrt N := by
  have h1 := sidon_sum_sq_blockFin_le hAsid (by omega : 0 < N) 1
  simp only [Finset.range_one, Finset.sum_singleton, one_mul] at h1
  have hblk : blockFin A N 0 = prefixFin A N := by
    ext x
    simp [blockFin, prefixFin]
  rw [hblk] at h1
  have hreal : ((prefixFin A N).card : ℝ) ^ 2 ≤ 2 * (N : ℝ) + ((prefixFin A N).card : ℝ) := by
    exact_mod_cast h1
  have hN_pos : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hsq : Real.sqrt (N : ℝ) ^ 2 = (N : ℝ) := Real.sq_sqrt (by linarith)
  have hsqrt_ge1 : 1 ≤ Real.sqrt (N : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hN_pos
  have hsqrt_le : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    nlinarith
  by_contra hgt
  push Not at hgt
  nlinarith

private lemma sum_blockFin_Ico {A : Set ℕ} {D : ℕ} (hD : 0 < D) {M₁ M₂ : ℕ} (hM : M₁ ≤ M₂) :
    (∑ m ∈ Finset.Ico M₁ M₂, ((blockFin A D m).card : ℝ)) =
      ((prefixFin A (M₂ * D)).card : ℝ) - ((prefixFin A (M₁ * D)).card : ℝ) := by
  have hnat :
      ∑ m ∈ Finset.range M₁, (blockFin A D m).card +
        ∑ m ∈ Finset.Ico M₁ M₂, (blockFin A D m).card =
      ∑ m ∈ Finset.range M₂, (blockFin A D m).card :=
    Finset.sum_range_add_sum_Ico (fun m => (blockFin A D m).card) hM
  rw [← card_prefixFin_eq_sum_blockFin A hD M₁, ← card_prefixFin_eq_sum_blockFin A hD M₂] at hnat
  have hreal :
      ((prefixFin A (M₁ * D)).card : ℝ) +
        ∑ m ∈ Finset.Ico M₁ M₂, ((blockFin A D m).card : ℝ) =
      ((prefixFin A (M₂ * D)).card : ℝ) := by
    exact_mod_cast hnat
  linarith

private lemma erdos_158_sidon {A : Set ℕ} (hAsid : IsSidon A) :
    liminf (fun N : ℕ => (A ∩ Set.Iio N).ncard * (N : ℝ) ^ (-1 / 2 : ℝ)) atTop = 0 := by
  by_contra hne
  obtain ⟨c, hc_pos, N₀, hN₀⟩ :
      ∃ c > (0 : ℝ), ∃ N₀ : ℕ, ∀ N ≥ N₀,
        c ≤ ((A ∩ Set.Iio N).ncard : ℝ) * (N : ℝ) ^ (-1 / 2 : ℝ) := by
    suffices
        ∃ a ∈ {a : ℝ | ∃ N₀ : ℕ, ∀ b ≥ N₀, a ≤ ↑(A ∩ Set.Iio b).ncard * (b : ℝ) ^ (-1 / 2 : ℝ)},
          0 < a by
      rcases this with ⟨a, ⟨N₀, hN₀⟩, ha⟩
      exact ⟨a, ha, N₀, hN₀⟩
    by_contra ha
    push Not at ha
    simp only [liminf_eq, eventually_atTop] at hne
    exact hne <| le_antisymm (csSup_le ⟨0, 0, fun n _ => by positivity⟩ ha) <|
      le_csSup ⟨0, ha⟩ ⟨0, fun n _ => by positivity⟩
  have hlower : ∀ N ≥ max N₀ 1, c * Real.sqrt N ≤ ((prefixFin A N).card : ℝ) := by
    intro N hN
    have hN1 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
    have hsqrt_pos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hN1
    have hbound := hN₀ N (le_trans (le_max_left N₀ 1) hN)
    rw [ncard_inter_Iio_eq_card_prefixFin] at hbound
    have hrpow : (N : ℝ) ^ (-1 / 2 : ℝ) = (Real.sqrt (N : ℝ))⁻¹ := by
      rw [neg_div, Real.rpow_neg (le_of_lt hN1), Real.sqrt_eq_rpow]
    rw [hrpow] at hbound
    have hmul := mul_le_mul_of_nonneg_right hbound (le_of_lt hsqrt_pos)
    rwa [mul_assoc, inv_mul_cancel₀ (ne_of_gt hsqrt_pos), mul_one] at hmul
  let K : ℕ := Nat.ceil (16 / c ^ 2) + 2
  let J : ℕ := Nat.ceil (16 / c ^ 2) + 1
  let D : ℕ := max (max N₀ 1) (K ^ J)
  have hK2 : 2 ≤ K := by omega
  have hK1 : 1 ≤ K := by omega
  have hD1 : 1 ≤ D := le_trans (le_max_right N₀ 1) (le_max_left _ _)
  have hD_pos : 0 < D := by omega
  have hD_ge_N0 : max N₀ 1 ≤ D := le_max_left _ _
  have hD_ge_KJ : K ^ J ≤ D := le_max_right _ _
  have hK_real : 16 / c ^ 2 ≤ (K : ℝ) := by
    have hceil : 16 / c ^ 2 ≤ (Nat.ceil (16 / c ^ 2) : ℝ) := Nat.le_ceil _
    have hcast : (K : ℝ) = (Nat.ceil (16 / c ^ 2) : ℝ) + 2 := by
      simp [K]
    linarith
  have hJ_real : 16 / c ^ 2 < (J : ℝ) := by
    have hceil : 16 / c ^ 2 ≤ (Nat.ceil (16 / c ^ 2) : ℝ) := Nat.le_ceil _
    have hcast : (J : ℝ) = (Nat.ceil (16 / c ^ 2) : ℝ) + 1 := by
      simp [J]
    linarith
  have hcK : (4 : ℝ) ≤ c * Real.sqrt K := by
    have hc2_pos : 0 < c ^ 2 := sq_pos_of_pos hc_pos
    have h16 : 16 ≤ c ^ 2 * (K : ℝ) := by
      have := mul_le_mul_of_nonneg_left hK_real (le_of_lt hc2_pos)
      rwa [mul_div_cancel₀ _ (ne_of_gt hc2_pos)] at this
    have hsq : (c * Real.sqrt (K : ℝ)) ^ 2 = c ^ 2 * (K : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg K)]
    have hnn : 0 ≤ c * Real.sqrt (K : ℝ) := mul_nonneg (le_of_lt hc_pos) (Real.sqrt_nonneg _)
    nlinarith
  have hupper_total :
      ∑ m ∈ Finset.range (K ^ J), ((blockFin A D m).card : ℝ) ^ 2 ≤ 4 * (D : ℝ) := by
    have hsid :
        ∑ m ∈ Finset.range (K ^ J), ((blockFin A D m).card : ℝ) ^ 2 ≤
          2 * (D : ℝ) + ((prefixFin A (K ^ J * D)).card : ℝ) := by
      exact_mod_cast sidon_sum_sq_blockFin_le hAsid hD_pos (K ^ J)
    have hKJ_pos : 1 ≤ K ^ J := Nat.one_le_pow J K hK1
    have hprod_ge1 : 1 ≤ K ^ J * D := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hpref_le : ((prefixFin A (K ^ J * D)).card : ℝ) ≤ 2 * Real.sqrt (K ^ J * D : ℕ) :=
      sidon_prefixFin_le_two_sqrt hAsid hprod_ge1
    have hsqrt_le_D : Real.sqrt (K ^ J * D : ℕ) ≤ (D : ℝ) := by
      have hle_D2 : ((K ^ J * D : ℕ) : ℝ) ≤ (D : ℝ) ^ 2 := by
        have hnat : K ^ J * D ≤ D * D := Nat.mul_le_mul_right D hD_ge_KJ
        rw [sq]
        exact_mod_cast hnat
      calc Real.sqrt (K ^ J * D : ℕ)
          ≤ Real.sqrt ((D : ℝ) ^ 2) := Real.sqrt_le_sqrt hle_D2
        _ = (D : ℝ) := Real.sqrt_sq (Nat.cast_nonneg D)
    linarith
  have hscale_lower :
      ∀ j ∈ Finset.range J,
        (c ^ 2 / 4) * (D : ℝ) ≤
          ∑ m ∈ Finset.Ico (K ^ j) (K ^ (j + 1)), ((blockFin A D m).card : ℝ) ^ 2 := by
    intro j hj
    have hj_lt : j < J := Finset.mem_range.mp hj
    have hpow_le : K ^ j ≤ K ^ (j + 1) := Nat.pow_le_pow_right hK1 (Nat.le_succ j)
    have hKj_ge1 : 1 ≤ K ^ j := Nat.one_le_pow j K hK1
    have hKj1_ge1 : 1 ≤ K ^ (j + 1) := Nat.one_le_pow (j + 1) K hK1
    have hN_hi_ge : max N₀ 1 ≤ K ^ (j + 1) * D :=
      le_trans hD_ge_N0 (Nat.le_mul_of_pos_left D (by omega))
    have hlo_count := hlower (K ^ (j + 1) * D) hN_hi_ge
    have hhi_count := sidon_prefixFin_le_two_sqrt hAsid
      (Nat.one_le_iff_ne_zero.mpr (by positivity : K ^ j * D ≠ 0))
    have hsqrt_rel :
        Real.sqrt (K ^ (j + 1) * D : ℕ) = Real.sqrt (K : ℝ) * Real.sqrt (K ^ j * D : ℕ) := by
      have hcast : ((K ^ (j + 1) * D : ℕ) : ℝ) = (K : ℝ) * ((K ^ j * D : ℕ) : ℝ) := by
        push_cast [pow_succ']
        ring
      rw [hcast, Real.sqrt_mul (Nat.cast_nonneg K)]
    have hdiff_ge :
        (c / 2) * Real.sqrt (K ^ (j + 1) * D : ℕ) ≤
          ∑ m ∈ Finset.Ico (K ^ j) (K ^ (j + 1)), ((blockFin A D m).card : ℝ) := by
      rw [sum_blockFin_Ico hD_pos hpow_le]
      have h2_le : 2 * Real.sqrt (K ^ j * D : ℕ) ≤ (c / 2) * Real.sqrt (K ^ (j + 1) * D : ℕ) := by
        rw [hsqrt_rel]
        have hnn : 0 ≤ Real.sqrt (K ^ j * D : ℕ) := Real.sqrt_nonneg _
        nlinarith
      linarith
    have hcs :=
      sq_sum_le_card_mul_sum_sq (s := Finset.Ico (K ^ j) (K ^ (j + 1)))
        (f := fun m => ((blockFin A D m).card : ℝ))
    have hcard_le : ((Finset.Ico (K ^ j) (K ^ (j + 1))).card : ℝ) ≤ (K ^ (j + 1) : ℝ) := by
      have hnat : (Finset.Ico (K ^ j) (K ^ (j + 1))).card ≤ K ^ (j + 1) := by
        simp only [Nat.card_Ico]
        omega
      exact_mod_cast hnat
    have hsum_sq_nonneg :
        0 ≤ ∑ m ∈ Finset.Ico (K ^ j) (K ^ (j + 1)), ((blockFin A D m).card : ℝ) ^ 2 :=
      Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hsq_lhs :
        ((c / 2) * Real.sqrt (K ^ (j + 1) * D : ℕ)) ^ 2 ≤
          (K ^ (j + 1) : ℝ) *
            ∑ m ∈ Finset.Ico (K ^ j) (K ^ (j + 1)), ((blockFin A D m).card : ℝ) ^ 2 := by
      have hnn : 0 ≤ (c / 2) * Real.sqrt (K ^ (j + 1) * D : ℕ) := by positivity
      have h1 : ((c / 2) * Real.sqrt (K ^ (j + 1) * D : ℕ)) ^ 2 ≤
          (∑ m ∈ Finset.Ico (K ^ j) (K ^ (j + 1)), ((blockFin A D m).card : ℝ)) ^ 2 := by
        nlinarith
      have h2 :
          ((Finset.Ico (K ^ j) (K ^ (j + 1))).card : ℝ) *
              ∑ m ∈ Finset.Ico (K ^ j) (K ^ (j + 1)), ((blockFin A D m).card : ℝ) ^ 2 ≤
            (K ^ (j + 1) : ℝ) *
              ∑ m ∈ Finset.Ico (K ^ j) (K ^ (j + 1)), ((blockFin A D m).card : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hcard_le hsum_sq_nonneg
      exact le_trans (le_trans h1 hcs) h2
    have hsimp :
        ((c / 2) * Real.sqrt (K ^ (j + 1) * D : ℕ)) ^ 2 =
          (K ^ (j + 1) : ℝ) * ((c ^ 2 / 4) * (D : ℝ)) := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      push_cast
      ring
    rw [hsimp] at hsq_lhs
    have hKj1_pos : (0 : ℝ) < (K ^ (j + 1) : ℝ) := by
      exact_mod_cast (show 0 < K ^ (j + 1) by omega)
    exact le_of_mul_le_mul_left hsq_lhs hKj1_pos
  have hdisj_scales :
      (↑(Finset.range J) : Set ℕ).PairwiseDisjoint (fun j => Finset.Ico (K ^ j) (K ^ (j + 1))) := by
    intro j₁ _ j₂ _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro m hm₁ hm₂
    simp only [Finset.mem_Ico] at hm₁ hm₂
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : K ^ (j₁ + 1) ≤ K ^ j₂ := Nat.pow_le_pow_right hK1 (by omega)
      omega
    · have hle : K ^ (j₂ + 1) ≤ K ^ j₁ := Nat.pow_le_pow_right hK1 (by omega)
      omega
  have hsub_range :
      (Finset.range J).biUnion (fun j => Finset.Ico (K ^ j) (K ^ (j + 1))) ⊆
        Finset.range (K ^ J) := by
    intro m hm
    rcases Finset.mem_biUnion.mp hm with ⟨j, hj, hmj⟩
    have hj_lt : j < J := Finset.mem_range.mp hj
    have hle : K ^ (j + 1) ≤ K ^ J := Nat.pow_le_pow_right hK1 (by omega)
    simp only [Finset.mem_Ico] at hmj
    exact Finset.mem_range.mpr (lt_of_lt_of_le hmj.2 hle)
  have hlower_total :
      (J : ℝ) * ((c ^ 2 / 4) * (D : ℝ)) ≤
        ∑ m ∈ Finset.range (K ^ J), ((blockFin A D m).card : ℝ) ^ 2 := by
    calc (J : ℝ) * ((c ^ 2 / 4) * (D : ℝ))
        = ∑ _j ∈ Finset.range J, (c ^ 2 / 4) * (D : ℝ) := by simp
      _ ≤ ∑ j ∈ Finset.range J,
            ∑ m ∈ Finset.Ico (K ^ j) (K ^ (j + 1)), ((blockFin A D m).card : ℝ) ^ 2 :=
          Finset.sum_le_sum hscale_lower
      _ = ∑ m ∈ (Finset.range J).biUnion (fun j => Finset.Ico (K ^ j) (K ^ (j + 1))),
            ((blockFin A D m).card : ℝ) ^ 2 :=
          (Finset.sum_biUnion hdisj_scales).symm
      _ ≤ ∑ m ∈ Finset.range (K ^ J), ((blockFin A D m).card : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub_range (fun _ _ _ => sq_nonneg _)
  have hcomb : (J : ℝ) * ((c ^ 2 / 4) * (D : ℝ)) ≤ 4 * (D : ℝ) :=
    le_trans hlower_total hupper_total
  have hD_rpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD_pos
  have hcancel : (J : ℝ) * (c ^ 2 / 4) ≤ 4 := by
    have h1 : ((J : ℝ) * (c ^ 2 / 4)) * (D : ℝ) ≤ 4 * (D : ℝ) := by linarith
    exact le_of_mul_le_mul_right h1 hD_rpos
  have hc2_pos : 0 < c ^ 2 := sq_pos_of_pos hc_pos
  have hJ_gt : 16 < (J : ℝ) * c ^ 2 := by
    have := mul_lt_mul_of_pos_right hJ_real hc2_pos
    rwa [div_mul_cancel₀ _ (ne_of_gt hc2_pos)] at this
  linarith

end Erdos158R1H1Proof

theorem OMA.solution : OMA.R_Erdos158_erdos_158_R1.H1 := by
  intro A _ hAsid
  exact Erdos158R1H1Proof.erdos_158_sidon hAsid
