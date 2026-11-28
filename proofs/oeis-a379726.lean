import OMAStatements.S_oeis_a379726
import Mathlib

namespace OMA.P_oeis_a379726

open OMA.S_oeis_a379726

private lemma kingAdj_symm {n : ℕ} {u v : Fin n × Fin n} (h : kingAdj u v) : kingAdj v u := by
  unfold kingAdj at *; omega

-- General double-counting lower bound:
-- For any set Y of target squares and any subset Z of board squares:
-- If every u ∈ Z is king-adjacent to at most 2 elements of Y, and every u ∉ Z is king-adjacent
-- to at most 1 element of Y, then for any 2-dominating set S:
--   2 * Y.card ≤ S.card + Z.card!
private lemma double_count_bound {n : ℕ} (S Y Z : Finset (Fin n × Fin n))
    (hS : isTwoDominating S)
    (hZ : ∀ u ∈ Z, (Y.filter (fun v => kingAdj u v)).card ≤ 2)
    (hnotZ : ∀ u : Fin n × Fin n, u ∉ Z → (Y.filter (fun v => kingAdj u v)).card ≤ 1) :
    2 * Y.card ≤ S.card + Z.card := by
  have h1 : 2 * Y.card ≤ ∑ v ∈ Y, (S.filter (fun u => kingAdj u v)).card := by
    calc 2 * Y.card = ∑ _v ∈ Y, 2 := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ Y, (S.filter (fun u => kingAdj u v)).card :=
        Finset.sum_le_sum fun v _ => hS v
  have hswap :
      ∑ v ∈ Y, (S.filter (fun u => kingAdj u v)).card =
      ∑ u ∈ S, (Y.filter (fun v => kingAdj u v)).card := by
    simp_rw [Finset.card_filter]
    rw [Finset.sum_comm]
  have h2 : ∑ u ∈ S, (Y.filter (fun v => kingAdj u v)).card ≤ S.card + Z.card := by
    have hsplit : ∑ u ∈ S, (Y.filter (fun v => kingAdj u v)).card =
        ∑ u ∈ S.filter (fun u => u ∈ Z), (Y.filter (fun v => kingAdj u v)).card +
        ∑ u ∈ S.filter (fun u => u ∉ Z), (Y.filter (fun v => kingAdj u v)).card := by
      rw [← Finset.sum_union]
      · congr 1; ext u; simp only [Finset.mem_union, Finset.mem_filter]; tauto
      · rw [Finset.disjoint_left]; intro u h1 h2; simp at h1 h2; exact h2.2 h1.2
    rw [hsplit]
    have ha : ∑ u ∈ S.filter (fun u => u ∈ Z), (Y.filter (fun v => kingAdj u v)).card ≤
        2 * (S.filter (fun u => u ∈ Z)).card := by
      calc ∑ u ∈ S.filter (fun u => u ∈ Z), (Y.filter (fun v => kingAdj u v)).card
          ≤ ∑ _u ∈ S.filter (fun u => u ∈ Z), 2 :=
            Finset.sum_le_sum fun u hu => hZ u (Finset.mem_filter.mp hu).2
        _ = 2 * (S.filter (fun u => u ∈ Z)).card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
    have hb : ∑ u ∈ S.filter (fun u => u ∉ Z), (Y.filter (fun v => kingAdj u v)).card ≤
        (S.filter (fun u => u ∉ Z)).card := by
      calc ∑ u ∈ S.filter (fun u => u ∉ Z), (Y.filter (fun v => kingAdj u v)).card
          ≤ ∑ _u ∈ S.filter (fun u => u ∉ Z), 1 :=
            Finset.sum_le_sum fun u hu => hnotZ u (Finset.mem_filter.mp hu).2
        _ = (S.filter (fun u => u ∉ Z)).card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
    have hcard_sum : (S.filter (fun u => u ∈ Z)).card + (S.filter (fun u => u ∉ Z)).card = S.card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext u; simp only [Finset.mem_union, Finset.mem_filter]; tauto
      · rw [Finset.disjoint_left]; intro u h1 h2; simp at h1 h2; exact h2.2 h1.2
    have hsub : (S.filter (fun u => u ∈ Z)).card ≤ Z.card := by
      apply Finset.card_le_card
      intro u hu; exact (Finset.mem_filter.mp hu).2
    omega
  omega

-- Case 1: n % 3 ≠ 0 (n = 3m + 1 or 3m + 2, n ≥ 2):
-- Lower bound: Y = {(3a, 3b) | a ≤ m, b ≤ m}, Z = ∅!
private lemma lower_not_dvd3 {n : ℕ} (hn : n % 3 ≠ 0) (S : Finset (Fin n × Fin n))
    (hS : isTwoDominating S) :
    2 * (n / 3 + 1) ^ 2 ≤ S.card := by
  let m := n / 3
  have hm : 3 * m < n := by omega
  let Y : Finset (Fin n × Fin n) :=
    (Finset.univ : Finset (Fin (m + 1) × Fin (m + 1))).image
      (fun p => (⟨3 * p.1.1, by have := p.1.isLt; omega⟩, ⟨3 * p.2.1, by have := p.2.isLt; omega⟩))
  have hYcard : Y.card = (m + 1) ^ 2 := by
    rw [Finset.card_image_of_injective]
    · simp [pow_two]
    · intro p1 p2 h
      simp only [Prod.mk.injEq, Fin.mk.injEq] at h
      ext <;> omega
  have hnotZ : ∀ u : Fin n × Fin n, u ∉ (∅ : Finset (Fin n × Fin n)) →
      (Y.filter (fun v => kingAdj u v)).card ≤ 1 := by
    intro u _
    rw [Finset.card_le_one]
    intro v1 hv1 v2 hv2
    simp only [Finset.mem_filter, Y, Finset.mem_image, Finset.mem_univ, true_and] at hv1 hv2
    rcases hv1 with ⟨⟨p1, rfl⟩, hadj1⟩
    rcases hv2 with ⟨⟨p2, rfl⟩, hadj2⟩
    unfold kingAdj at hadj1 hadj2
    dsimp only at hadj1 hadj2
    have h1 : p1.1.1 = p2.1.1 := by omega
    have h2 : p1.2.1 = p2.2.1 := by omega
    ext <;> dsimp only <;> omega
  have hbound := double_count_bound S Y ∅ hS (fun _ h => absurd h (Finset.notMem_empty _)) hnotZ
  rw [hYcard, Finset.card_empty, add_zero] at hbound
  exact hbound

-- Case 2: n = 3m (m ≥ 1):
-- Lower bound: Y = Y1 ∪ Y2 where
--   Y1 = {(3a, 3b+2) | a ≤ b < m}  (size m*(m+1)/2),
--   Y2 = {(3a+2, 3b) | b ≤ a < m}  (size m*(m+1)/2),
--   Z  = {(3a+1, 3a+1) | a < m}    (size m)!
private lemma lower_dvd3 {m : ℕ} (_hm : 1 ≤ m) (S : Finset (Fin (3 * m) × Fin (3 * m)))
    (hS : isTwoDominating S) :
    2 * m ^ 2 + m ≤ S.card := by
  let Y1 : Finset (Fin (3 * m) × Fin (3 * m)) :=
    ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1.1 ≤ p.2.1)).image
      (fun p => (⟨3 * p.1.1, by have := p.1.isLt; omega⟩, ⟨3 * p.2.1 + 2, by have := p.2.isLt; omega⟩))
  let Y2 : Finset (Fin (3 * m) × Fin (3 * m)) :=
    ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.2.1 ≤ p.1.1)).image
      (fun p => (⟨3 * p.1.1 + 2, by have := p.1.isLt; omega⟩, ⟨3 * p.2.1, by have := p.2.isLt; omega⟩))
  let Y := Y1 ∪ Y2
  let Z : Finset (Fin (3 * m) × Fin (3 * m)) :=
    (Finset.univ : Finset (Fin m)).image
      (fun a => (⟨3 * a.1 + 1, by have := a.isLt; omega⟩, ⟨3 * a.1 + 1, by have := a.isLt; omega⟩))
  -- Membership characterization of Y:
  have hmemY : ∀ v : Fin (3 * m) × Fin (3 * m), v ∈ Y ↔
      (v.1.1 % 3 = 0 ∧ v.2.1 % 3 = 2 ∧ v.1.1 / 3 ≤ v.2.1 / 3) ∨
      (v.1.1 % 3 = 2 ∧ v.2.1 % 3 = 0 ∧ v.2.1 / 3 ≤ v.1.1 / 3) := by
    intro v
    simp only [Y, Y1, Y2, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩)
      · left; dsimp only; exact ⟨by omega, by omega, by omega⟩
      · right; dsimp only; exact ⟨by omega, by omega, by omega⟩
    · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
      · left
        refine ⟨(⟨v.1.1 / 3, by have := v.1.isLt; omega⟩, ⟨v.2.1 / 3, by have := v.2.isLt; omega⟩), h3, ?_⟩
        ext <;> dsimp only <;> omega
      · right
        refine ⟨(⟨v.1.1 / 3, by have := v.1.isLt; omega⟩, ⟨v.2.1 / 3, by have := v.2.isLt; omega⟩), h3, ?_⟩
        ext <;> dsimp only <;> omega
  -- Key pairwise-disjointness lemma: if v1, v2 ∈ Y are distinct and both king-adjacent to u,
  -- then u ∈ Z and v1 is either (u.1 - 1, u.2 + 1) or (u.1 + 1, u.2 - 1)!
  have hpair : ∀ u v1 v2 : Fin (3 * m) × Fin (3 * m),
      v1 ∈ Y → v2 ∈ Y → kingAdj u v1 → kingAdj u v2 → v1 ≠ v2 →
      u ∈ Z ∧ (v1.1.1 + 1 = u.1.1 ∧ v1.2.1 = u.2.1 + 1 ∨ v1.1.1 = u.1.1 + 1 ∧ v1.2.1 + 1 = u.2.1) := by
    intro u v1 v2 hv1 hv2 hadj1 hadj2 hne
    rw [hmemY] at hv1 hv2
    unfold kingAdj at hadj1 hadj2
    have hZ_iff : u ∈ Z ↔ u.1.1 % 3 = 1 ∧ u.2.1 % 3 = 1 ∧ u.1.1 / 3 = u.2.1 / 3 := by
      simp only [Z, Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨a, rfl⟩; dsimp only; exact ⟨by omega, by omega, by omega⟩
      · rintro ⟨h1, h2, h3⟩
        refine ⟨⟨u.1.1 / 3, by have := u.1.isLt; omega⟩, ?_⟩
        ext <;> dsimp only <;> omega
    rw [hZ_iff]
    have hne_coord : v1.1.1 ≠ v2.1.1 ∨ v1.2.1 ≠ v2.2.1 := by
      by_contra h; push Not at h
      exact hne (by ext <;> [exact h.1; exact h.2])
    rcases hv1 with ⟨a1, b1, c1⟩ | ⟨a1, b1, c1⟩ <;>
    rcases hv2 with ⟨a2, b2, c2⟩ | ⟨a2, b2, c2⟩ <;>
    omega
  -- Hence for u ∉ Z, |(Y.filter (kingAdj u))| ≤ 1; and for u ∈ Z, |(Y.filter (kingAdj u))| ≤ 2!
  have hnotZ : ∀ u : Fin (3 * m) × Fin (3 * m), u ∉ Z →
      (Y.filter (fun v => kingAdj u v)).card ≤ 1 := by
    intro u hu
    rw [Finset.card_le_one]
    intro v1 hv1 v2 hv2
    by_contra hne
    simp only [Finset.mem_filter] at hv1 hv2
    exact hu (hpair u v1 v2 hv1.1 hv2.1 hv1.2 hv2.2 hne).1
  have hZ : ∀ u ∈ Z, (Y.filter (fun v => kingAdj u v)).card ≤ 2 := by
    intro u hu
    by_cases hle1 : (Y.filter (fun v => kingAdj u v)).card ≤ 1
    · omega
    · have hgt1 : 1 < (Y.filter (fun v => kingAdj u v)).card := by omega
      obtain ⟨v0, hv0, v1, hv1, hvne⟩ := Finset.one_lt_card.mp hgt1
      simp only [Finset.mem_filter] at hv0 hv1
      have hsub : Y.filter (fun v => kingAdj u v) ⊆ {v0, v1} := by
        intro v hv
        simp only [Finset.mem_filter] at hv
        simp only [Finset.mem_insert, Finset.mem_singleton]
        by_cases h0 : v = v0
        · left; exact h0
        · right
          have hp0 := (hpair u v0 v1 hv0.1 hv1.1 hv0.2 hv1.2 hvne).2
          have hp1 := (hpair u v1 v0 hv1.1 hv0.1 hv1.2 hv0.2 (Ne.symm hvne)).2
          have hpv := (hpair u v v0 hv.1 hv0.1 hv.2 hv0.2 h0).2
          have h01 : v0.1.1 ≠ v1.1.1 ∨ v0.2.1 ≠ v1.2.1 := by
            by_contra h; push Not at h; exact hvne (by ext <;> [exact h.1; exact h.2])
          have hv0_ne : v.1.1 ≠ v0.1.1 ∨ v.2.1 ≠ v0.2.1 := by
            by_contra h; push Not at h; exact h0 (by ext <;> [exact h.1; exact h.2])
          have hveq : v.1.1 = v1.1.1 ∧ v.2.1 = v1.2.1 := by
            rcases hp0 with ⟨_, _⟩ | ⟨_, _⟩ <;> rcases hp1 with ⟨_, _⟩ | ⟨_, _⟩ <;>
            rcases hpv with ⟨_, _⟩ | ⟨_, _⟩ <;> omega
          ext <;> [exact hveq.1; exact hveq.2]
      calc (Y.filter (fun v => kingAdj u v)).card ≤ ({v0, v1} : Finset _).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
  -- Compute Y.card = m^2 + m and Z.card = m!
  have hZcard : Z.card = m := by
    rw [Finset.card_image_of_injective]
    · simp
    · intro a1 a2 h; simp only [Prod.mk.injEq, Fin.mk.injEq] at h; ext; omega
  have hYcard : Y.card = m ^ 2 + m := by
    have hd12 : Disjoint Y1 Y2 := by
      rw [Finset.disjoint_left]; intro v h1 h2
      simp only [Y1, Y2, Finset.mem_image] at h1 h2
      rcases h1 with ⟨p1, _, rfl⟩; rcases h2 with ⟨p2, _, h⟩
      simp only [Prod.mk.injEq, Fin.mk.injEq] at h; omega
    have hc1 : Y1.card = ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1.1 ≤ p.2.1)).card := by
      apply Finset.card_image_of_injective
      intro p1 p2 h; simp only [Prod.mk.injEq, Fin.mk.injEq] at h; ext <;> omega
    have hc2 : Y2.card = ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.2.1 ≤ p.1.1)).card := by
      apply Finset.card_image_of_injective
      intro p1 p2 h; simp only [Prod.mk.injEq, Fin.mk.injEq] at h; ext <;> omega
    have hdiag_m : ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1.1 = p.2.1)).card = m := by
      have heq : (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1.1 = p.2.1) =
          (Finset.univ : Finset (Fin m)).image (fun a => (a, a)) := by
        ext p; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro h; exact ⟨p.1, by ext; rfl; exact h⟩
        · rintro ⟨a, rfl⟩; rfl
      rw [heq, Finset.card_image_of_injective]
      · simp
      · intro a1 a2 h; simp at h; exact h
    have hunion : (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1.1 ≤ p.2.1) ∪
        (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.2.1 ≤ p.1.1) = Finset.univ := by
      ext p; simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]; omega
    have hinter : (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1.1 ≤ p.2.1) ∩
        (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.2.1 ≤ p.1.1) =
        (Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1.1 = p.2.1) := by
      ext p; simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hinc := Finset.card_union_add_card_inter
      ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.1.1 ≤ p.2.1))
      ((Finset.univ : Finset (Fin m × Fin m)).filter (fun p => p.2.1 ≤ p.1.1))
    rw [hunion, hinter, hdiag_m] at hinc
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, ← pow_two] at hinc
    rw [Finset.card_union_of_disjoint hd12, hc1, hc2]
    omega
  have hbound := double_count_bound S Y Z hS hZ hnotZ
  rw [hYcard, hZcard] at hbound
  omega

-- Upper bound constructions for all 3 residues mod 3!

-- Case A: n = 3 * m (m ≥ 1): S = {(3a+1, c) | a < m, c = 0 ∨ c % 3 ≠ 0}, |S| = 2m^2 + m!
private lemma upper_dvd3 (m : ℕ) (hm : 1 ≤ m) :
    ∃ S : Finset (Fin (3 * m) × Fin (3 * m)), isTwoDominating S ∧ S.card = 2 * m ^ 2 + m := by
  let rows : Finset (Fin (3 * m)) :=
    (Finset.univ : Finset (Fin m)).image (fun a => ⟨3 * a.1 + 1, by have := a.isLt; omega⟩)
  let cols : Finset (Fin (3 * m)) :=
    (Finset.univ : Finset (Fin (3 * m))).filter (fun c => c.1 = 0 ∨ c.1 % 3 ≠ 0)
  let S := rows ×ˢ cols
  refine ⟨S, ?_, ?_⟩
  · intro v
    let a : Fin m := ⟨v.1.1 / 3, by have := v.1.isLt; omega⟩
    let r0 : Fin (3 * m) := ⟨3 * a.1 + 1, by have := a.isLt; omega⟩
    have hr0_mem : r0 ∈ rows := Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    have hr0_adj : r0.1 ≤ v.1.1 + 1 ∧ v.1.1 ≤ r0.1 + 1 := by
      dsimp only [r0, a]; omega
    -- Find two distinct columns c1, c2 ∈ cols adjacent to v.2!
    have hcols : ∃ c1 c2 : Fin (3 * m), c1 ≠ c2 ∧ c1 ∈ cols ∧ c2 ∈ cols ∧
        (c1.1 ≤ v.2.1 + 1 ∧ v.2.1 ≤ c1.1 + 1) ∧ (c2.1 ≤ v.2.1 + 1 ∧ v.2.1 ≤ c2.1 + 1) := by
      by_cases hv0 : v.2.1 = 0
      · refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, by simp, ?_, ?_, by dsimp; omega, by dsimp; omega⟩
        · simp [cols]
        · simp [cols]
      · by_cases hmod : v.2.1 % 3 = 0
        · refine ⟨⟨v.2.1 - 1, by have := v.2.isLt; omega⟩, ⟨v.2.1 + 1, by have := v.2.isLt; omega⟩,
            by intro h; simp only [Fin.mk.injEq] at h; omega, ?_, ?_, by dsimp; omega, by dsimp; omega⟩
          · simp [cols]; right; omega
          · simp [cols]; omega
        · by_cases hmod1 : v.2.1 % 3 = 1
          · refine ⟨v.2, ⟨v.2.1 + 1, by have := v.2.isLt; omega⟩,
              by intro h; have := congr_arg Fin.val h; dsimp at this; omega, ?_, ?_, by omega, by dsimp; omega⟩
            · simp [cols]; right; omega
            · simp [cols]; omega
          · refine ⟨⟨v.2.1 - 1, by have := v.2.isLt; omega⟩, v.2,
              by intro h; have := congr_arg Fin.val h; dsimp at this; omega, ?_, ?_, by dsimp; omega, by omega⟩
            · simp [cols]; right; omega
            · simp [cols]; right; omega
    obtain ⟨c1, c2, hne, hc1, hc2, ha1, ha2⟩ := hcols
    have hsub : {(r0, c1), (r0, c2)} ⊆ S.filter (fun u => kingAdj u v) := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      simp only [Finset.mem_filter, S, Finset.mem_product]
      rcases hu with rfl | rfl
      · exact ⟨⟨hr0_mem, hc1⟩, ⟨hr0_adj, ha1⟩⟩
      · exact ⟨⟨hr0_mem, hc2⟩, ⟨hr0_adj, ha2⟩⟩
    have hcard2 : ({(r0, c1), (r0, c2)} : Finset (Fin (3 * m) × Fin (3 * m))).card = 2 := by
      rw [Finset.card_pair]
      intro h; exact hne (congr_arg Prod.snd h)
    calc 2 = ({(r0, c1), (r0, c2)} : Finset _).card := hcard2.symm
      _ ≤ (S.filter (fun u => kingAdj u v)).card := Finset.card_le_card hsub
  · rw [Finset.card_product]
    have hrc : rows.card = m := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro a1 a2 h; simp only [Fin.mk.injEq] at h; ext; omega
    have hcc : cols.card = 2 * m + 1 := by
      -- Complement of cols in univ is {3*(a+1) | a : Fin (m - 1)}, size m - 1!
      let bad : Finset (Fin (3 * m)) :=
        (Finset.univ : Finset (Fin (m - 1))).image (fun a => ⟨3 * (a.1 + 1), by have := a.isLt; omega⟩)
      have hbad_card : bad.card = m - 1 := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro a1 a2 h; simp only [Fin.mk.injEq] at h; ext; omega
      have hdisj : Disjoint cols bad := by
        rw [Finset.disjoint_left]; intro c hc hb
        simp only [cols, bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at hc hb
        rcases hb with ⟨a, rfl⟩; dsimp only at hc; omega
      have hunion : cols ∪ bad = Finset.univ := by
        ext c; simp only [Finset.mem_union, cols, bad, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_image, iff_true]
        by_cases h0 : c.1 = 0 ∨ c.1 % 3 ≠ 0
        · left; exact h0
        · right
          refine ⟨⟨c.1 / 3 - 1, by have := c.isLt; omega⟩, ?_⟩
          ext; dsimp only; omega
      have htot := congr_arg Finset.card hunion
      rw [Finset.card_union_of_disjoint hdisj, hbad_card, Finset.card_univ, Fintype.card_fin] at htot
      omega
    rw [hrc, hcc]; ring

-- Case B: n = 3 * m + 2 (m ≥ 0):
-- rows = {3a, 3a+1 | a ≤ m} (size 2*(m+1)), cols = {3b+1 | b ≤ m} (size m+1), |S| = 2*(m+1)^2!
private lemma upper_mod2 (m : ℕ) :
    ∃ S : Finset (Fin (3 * m + 2) × Fin (3 * m + 2)),
      isTwoDominating S ∧ S.card = 2 * (m + 1) ^ 2 := by
  let rows : Finset (Fin (3 * m + 2)) :=
    (Finset.univ : Finset (Fin (3 * m + 2))).filter (fun r => r.1 % 3 ≠ 2)
  let cols : Finset (Fin (3 * m + 2)) :=
    (Finset.univ : Finset (Fin (m + 1))).image (fun b => ⟨3 * b.1 + 1, by have := b.isLt; omega⟩)
  let S := rows ×ˢ cols
  refine ⟨S, ?_, ?_⟩
  · intro v
    -- Pick column c0 = 3*(v.2/3) + 1 ∈ cols (adjacent to v.2!)
    let b : Fin (m + 1) := ⟨v.2.1 / 3, by have := v.2.isLt; omega⟩
    let c0 : Fin (3 * m + 2) := ⟨3 * b.1 + 1, by have := b.isLt; omega⟩
    have hc0_mem : c0 ∈ cols := Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
    have hc0_adj : c0.1 ≤ v.2.1 + 1 ∧ v.2.1 ≤ c0.1 + 1 := by dsimp only [c0, b]; omega
    -- Pick two distinct rows r1, r2 ∈ rows adjacent to v.1!
    have hrows : ∃ r1 r2 : Fin (3 * m + 2), r1 ≠ r2 ∧ r1 ∈ rows ∧ r2 ∈ rows ∧
        (r1.1 ≤ v.1.1 + 1 ∧ v.1.1 ≤ r1.1 + 1) ∧ (r2.1 ≤ v.1.1 + 1 ∧ v.1.1 ≤ r2.1 + 1) := by
      by_cases hm2 : v.1.1 % 3 = 2
      · refine ⟨⟨v.1.1 - 1, by have := v.1.isLt; omega⟩, ⟨v.1.1 + 1, by have := v.1.isLt; omega⟩,
          by intro h; simp only [Fin.mk.injEq] at h; omega, ?_, ?_, by dsimp; omega, by dsimp; omega⟩
        · simp [rows]; omega
        · simp [rows]; omega
      · by_cases hm0 : v.1.1 % 3 = 0
        · refine ⟨v.1, ⟨v.1.1 + 1, by have := v.1.isLt; omega⟩,
            by intro h; have := congr_arg Fin.val h; dsimp at this; omega, ?_, ?_, by omega, by dsimp; omega⟩
          · simp [rows]; omega
          · simp [rows]; omega
        · refine ⟨⟨v.1.1 - 1, by have := v.1.isLt; omega⟩, v.1,
            by intro h; have := congr_arg Fin.val h; dsimp at this; omega, ?_, ?_, by dsimp; omega, by omega⟩
          · simp [rows]; omega
          · simp [rows]; omega
    obtain ⟨r1, r2, hne, hr1, hr2, ha1, ha2⟩ := hrows
    have hsub : {(r1, c0), (r2, c0)} ⊆ S.filter (fun u => kingAdj u v) := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      simp only [Finset.mem_filter, S, Finset.mem_product]
      rcases hu with rfl | rfl
      · exact ⟨⟨hr1, hc0_mem⟩, ⟨ha1, hc0_adj⟩⟩
      · exact ⟨⟨hr2, hc0_mem⟩, ⟨ha2, hc0_adj⟩⟩
    have hcard2 : ({(r1, c0), (r2, c0)} : Finset _).card = 2 := by
      rw [Finset.card_pair]; intro h; exact hne (congr_arg Prod.fst h)
    calc 2 = ({(r1, c0), (r2, c0)} : Finset _).card := hcard2.symm
      _ ≤ (S.filter (fun u => kingAdj u v)).card := Finset.card_le_card hsub
  · rw [Finset.card_product]
    have hcc : cols.card = m + 1 := by
      rw [Finset.card_image_of_injective]
      · simp
      · intro b1 b2 h; simp only [Fin.mk.injEq] at h; ext; omega
    have hrc : rows.card = 2 * (m + 1) := by
      let bad : Finset (Fin (3 * m + 2)) :=
        (Finset.univ : Finset (Fin m)).image (fun a => ⟨3 * a.1 + 2, by have := a.isLt; omega⟩)
      have hbad_card : bad.card = m := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro a1 a2 h; simp only [Fin.mk.injEq] at h; ext; omega
      have hdisj : Disjoint rows bad := by
        rw [Finset.disjoint_left]; intro r hr hb
        simp only [rows, bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at hr hb
        rcases hb with ⟨a, rfl⟩; dsimp only at hr; omega
      have hunion : rows ∪ bad = Finset.univ := by
        ext r; simp only [Finset.mem_union, rows, bad, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_image, iff_true]
        by_cases h2 : r.1 % 3 ≠ 2
        · left; exact h2
        · right
          refine ⟨⟨r.1 / 3, by have := r.isLt; omega⟩, ?_⟩
          ext; dsimp only; omega
      have htot := congr_arg Finset.card hunion
      rw [Finset.card_union_of_disjoint hdisj, hbad_card, Finset.card_univ, Fintype.card_fin] at htot
      omega
    rw [hrc, hcc]; ring

-- Case C: n = 3 * m + 1 (m ≥ 1):
-- rows = {r | r % 3 ≠ 2 ∨ r = 3m - 1} (size 2*(m+1)),
-- cols = {3b+1 | b < m} ∪ {3m - 1} (size m+1), |S| = 2*(m+1)^2!
private lemma upper_mod1 (m : ℕ) (hm : 1 ≤ m) :
    ∃ S : Finset (Fin (3 * m + 1) × Fin (3 * m + 1)),
      isTwoDominating S ∧ S.card = 2 * (m + 1) ^ 2 := by
  let rows : Finset (Fin (3 * m + 1)) :=
    (Finset.univ : Finset (Fin (3 * m + 1))).filter (fun r => r.1 % 3 ≠ 2 ∨ r.1 = 3 * m - 1)
  let cols : Finset (Fin (3 * m + 1)) :=
    insert ⟨3 * m - 1, by omega⟩
      ((Finset.univ : Finset (Fin m)).image (fun b => ⟨3 * b.1 + 1, by have := b.isLt; omega⟩))
  let S := rows ×ˢ cols
  refine ⟨S, ?_, ?_⟩
  · intro v
    -- Pick column c0 ∈ cols adjacent to v.2!
    have hcol : ∃ c0 ∈ cols, c0.1 ≤ v.2.1 + 1 ∧ v.2.1 ≤ c0.1 + 1 := by
      by_cases htop : v.2.1 ≥ 3 * m - 1
      · refine ⟨⟨3 * m - 1, by omega⟩, Finset.mem_insert_self _ _, ?_, ?_⟩ <;>
          (dsimp only; have := v.2.isLt; omega)
      · let b : Fin m := ⟨v.2.1 / 3, by omega⟩
        refine ⟨⟨3 * b.1 + 1, by have := b.isLt; omega⟩,
          Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩), ?_, ?_⟩ <;>
          (dsimp only [b]; omega)
    obtain ⟨c0, hc0_mem, hc0_adj⟩ := hcol
    -- Pick two distinct rows r1, r2 ∈ rows adjacent to v.1!
    have hrows : ∃ r1 r2 : Fin (3 * m + 1), r1 ≠ r2 ∧ r1 ∈ rows ∧ r2 ∈ rows ∧
        (r1.1 ≤ v.1.1 + 1 ∧ v.1.1 ≤ r1.1 + 1) ∧ (r2.1 ≤ v.1.1 + 1 ∧ v.1.1 ≤ r2.1 + 1) := by
      by_cases htop : v.1.1 = 3 * m
      · refine ⟨⟨3 * m - 1, by omega⟩, ⟨3 * m, by omega⟩,
          by intro h; simp only [Fin.mk.injEq] at h; omega, ?_, ?_, by dsimp; omega, by dsimp; omega⟩
        · simp [rows]
        · simp [rows]
      · by_cases hm2 : v.1.1 % 3 = 2
        · refine ⟨⟨v.1.1 - 1, by have := v.1.isLt; omega⟩, ⟨v.1.1 + 1, by have := v.1.isLt; omega⟩,
            by intro h; simp only [Fin.mk.injEq] at h; omega, ?_, ?_, by dsimp; omega, by dsimp; omega⟩
          · simp [rows]; left; omega
          · simp [rows]; left; omega
        · by_cases hm0 : v.1.1 % 3 = 0
          · refine ⟨v.1, ⟨v.1.1 + 1, by have := v.1.isLt; omega⟩,
              by intro h; have := congr_arg Fin.val h; dsimp at this; omega, ?_, ?_, by omega, by dsimp; omega⟩
            · simp [rows]; left; omega
            · simp [rows]; left; omega
          · refine ⟨⟨v.1.1 - 1, by have := v.1.isLt; omega⟩, v.1,
              by intro h; have := congr_arg Fin.val h; dsimp at this; omega, ?_, ?_, by dsimp; omega, by omega⟩
            · simp [rows]; left; omega
            · simp [rows]; left; omega
    obtain ⟨r1, r2, hne, hr1, hr2, ha1, ha2⟩ := hrows
    have hsub : {(r1, c0), (r2, c0)} ⊆ S.filter (fun u => kingAdj u v) := by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      simp only [Finset.mem_filter, S, Finset.mem_product]
      rcases hu with rfl | rfl
      · exact ⟨⟨hr1, hc0_mem⟩, ⟨ha1, hc0_adj⟩⟩
      · exact ⟨⟨hr2, hc0_mem⟩, ⟨ha2, hc0_adj⟩⟩
    have hcard2 : ({(r1, c0), (r2, c0)} : Finset _).card = 2 := by
      rw [Finset.card_pair]; intro h; exact hne (congr_arg Prod.fst h)
    calc 2 = ({(r1, c0), (r2, c0)} : Finset _).card := hcard2.symm
      _ ≤ (S.filter (fun u => kingAdj u v)).card := Finset.card_le_card hsub
  · rw [Finset.card_product]
    have hcc : cols.card = m + 1 := by
      rw [Finset.card_insert_of_notMem]
      · rw [Finset.card_image_of_injective]
        · simp
        · intro b1 b2 h; simp only [Fin.mk.injEq] at h; ext; omega
      · simp only [Finset.mem_image, Finset.mem_univ, true_and, not_exists]
        intro b h; simp only [Fin.mk.injEq] at h; omega
    have hrc : rows.card = 2 * (m + 1) := by
      let bad : Finset (Fin (3 * m + 1)) :=
        (Finset.univ : Finset (Fin (m - 1))).image (fun a => ⟨3 * a.1 + 2, by have := a.isLt; omega⟩)
      have hbad_card : bad.card = m - 1 := by
        rw [Finset.card_image_of_injective]
        · simp
        · intro a1 a2 h; simp only [Fin.mk.injEq] at h; ext; omega
      have hdisj : Disjoint rows bad := by
        rw [Finset.disjoint_left]; intro r hr hb
        simp only [rows, bad, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image] at hr hb
        rcases hb with ⟨a, rfl⟩; have := a.isLt; dsimp only at hr; omega
      have hunion : rows ∪ bad = Finset.univ := by
        ext r; simp only [Finset.mem_union, rows, bad, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_image, iff_true]
        by_cases h2 : r.1 % 3 ≠ 2 ∨ r.1 = 3 * m - 1
        · left; exact h2
        · right
          refine ⟨⟨r.1 / 3, by have := r.isLt; omega⟩, ?_⟩
          ext; dsimp only; omega
      have htot := congr_arg Finset.card hunion
      rw [Finset.card_union_of_disjoint hdisj, hbad_card, Finset.card_univ, Fintype.card_fin] at htot
      omega
    rw [hrc, hcc]; ring

private theorem main_proved :
    ∀ n : ℕ, 2 ≤ n →
      a379726 n =
        if n % 3 = 0 then 2 * (n / 3) ^ 2 + n / 3
        else 2 * (n / 3 + 1) ^ 2 := by
  intro n hn
  unfold a379726
  by_cases h0 : n % 3 = 0
  · simp only [h0, ↓reduceIte]
    obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m := ⟨n / 3, by omega⟩
    have hm : 1 ≤ m := by omega
    have hdiv : 3 * m / 3 = m := by omega
    rw [hdiv]
    apply le_antisymm
    · exact Nat.sInf_le (upper_dvd3 m hm)
    · apply le_csInf
      · obtain ⟨S, hS, hcard⟩ := upper_dvd3 m hm
        exact ⟨_, S, hS, hcard⟩
      · rintro k ⟨S, hS, rfl⟩
        exact lower_dvd3 hm S hS
  · simp only [h0, ↓reduceIte]
    by_cases h1 : n % 3 = 1
    · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m + 1 := ⟨n / 3, by omega⟩
      have hm : 1 ≤ m := by omega
      have hdiv : (3 * m + 1) / 3 = m := by omega
      rw [hdiv]
      apply le_antisymm
      · exact Nat.sInf_le (upper_mod1 m hm)
      · apply le_csInf
        · obtain ⟨S, hS, hcard⟩ := upper_mod1 m hm
          exact ⟨_, S, hS, hcard⟩
        · rintro k ⟨S, hS, rfl⟩
          have hb := lower_not_dvd3 (by omega : (3 * m + 1) % 3 ≠ 0) S hS
          rwa [hdiv] at hb
    · obtain ⟨m, rfl⟩ : ∃ m, n = 3 * m + 2 := ⟨n / 3, by omega⟩
      have hdiv : (3 * m + 2) / 3 = m := by omega
      rw [hdiv]
      apply le_antisymm
      · exact Nat.sInf_le (upper_mod2 m)
      · apply le_csInf
        · obtain ⟨S, hS, hcard⟩ := upper_mod2 m
          exact ⟨_, S, hS, hcard⟩
        · rintro k ⟨S, hS, rfl⟩
          have hb := lower_not_dvd3 (by omega : (3 * m + 2) % 3 ≠ 0) S hS
          rwa [hdiv] at hb

end OMA.P_oeis_a379726

theorem OMA.solution : type_of% @OMA.S_oeis_a379726.main :=
  OMA.P_oeis_a379726.main_proved
