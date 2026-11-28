import OMAStatements.S_oeis_a208402

-- Problem: A208402: Number of n x 2 0..3 arrays with new values 0..3 introduced in row-major order
-- and no element equal to >2 of its immediate leftward, upward, or right-upward antidiagonal neighbors.
-- Credit: @ceejcake
-- Proof: In an n x 2 array every cell has at most 2 such neighbors, so the neighbor constraint holds automatically.
-- Flattening in row-major order gives restricted growth strings of length 2n over Fin 4, counted by a 4-state DP.

namespace ProofA208402

open OMA.S_oeis_a208402
open scoped Classical
noncomputable section

private lemma eqNeighborCount_le_two {n : ℕ} (A : Fin n → Fin 2 → Fin 4) (i : Fin n) (j : Fin 2) :
    eqNeighborCount A i j ≤ 2 := by
  unfold eqNeighborCount
  have hj := j.2
  by_cases h1 : 0 < j.1
  · have h3 : ¬ (0 < i.1 ∧ j.1 + 1 < 2) := by omega
    rw [dif_pos h1, dif_neg h3]
    split_ifs <;> omega
  · rw [dif_neg h1]
    split_ifs <;> omega

-- Restricted growth strings of length L over Fin 4
private def isRGS {L : ℕ} (w : Fin L → Fin 4) : Prop :=
  ∀ (t : Fin L) (v : Fin 4), v < w t → ∃ s : Fin L, s.1 < t.1 ∧ w s = v

private def rgsSet (L : ℕ) : Finset (Fin L → Fin 4) :=
  Finset.univ.filter isRGS

private def rgsMax (L : ℕ) (k : Fin 4) : Finset (Fin L → Fin 4) :=
  (rgsSet L).filter (fun w => (∀ t : Fin L, w t ≤ k) ∧ (∃ t : Fin L, w t = k))

-- Bijection between valid n x 2 arrays and rgsSet (2 * n)
private lemma card_valid_eq_rgs (n : ℕ) :
    (Finset.univ.filter (isValid n)).card = (rgsSet (2 * n)).card := by
  refine Finset.card_bij
    (fun A _ t => A ⟨t.1 / 2, by omega⟩ ⟨t.1 % 2, by omega⟩) ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA
    simp only [rgsSet, Finset.mem_filter, Finset.mem_univ, true_and, isRGS]
    intro t v hv
    rcases hA.1 ⟨t.1 / 2, by omega⟩ ⟨t.1 % 2, by omega⟩ v hv with ⟨i', j', hlt, heq⟩
    dsimp only at hlt
    refine ⟨⟨2 * i'.1 + j'.1, by omega⟩, by dsimp only; omega, ?_⟩
    have hd : (2 * i'.1 + j'.1) / 2 = i'.1 := by omega
    have hm : (2 * i'.1 + j'.1) % 2 = j'.1 := by omega
    simp only [hd, hm]
    exact heq
  · intro A1 _ A2 _ h
    funext i j
    have ht := congr_fun h ⟨2 * i.1 + j.1, by omega⟩
    dsimp only at ht
    have hd : (2 * i.1 + j.1) / 2 = i.1 := by omega
    have hm : (2 * i.1 + j.1) % 2 = j.1 := by omega
    simp only [hd, hm] at ht
    exact ht
  · intro w hw
    simp only [rgsSet, Finset.mem_filter, Finset.mem_univ, true_and, isRGS] at hw
    let A : Fin n → Fin 2 → Fin 4 := fun i j => w ⟨2 * i.1 + j.1, by omega⟩
    refine ⟨A, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, isValid]
      refine ⟨fun i j v hv => ?_, fun i j => eqNeighborCount_le_two A i j⟩
      rcases hw ⟨2 * i.1 + j.1, by omega⟩ v hv with ⟨s, hlt, heq⟩
      dsimp only at hlt
      refine ⟨⟨s.1 / 2, by omega⟩, ⟨s.1 % 2, by omega⟩, by dsimp only; omega, ?_⟩
      dsimp only [A]
      have hs : 2 * (s.1 / 2) + s.1 % 2 = s.1 := by omega
      have hfin : (⟨2 * (s.1 / 2) + s.1 % 2, by omega⟩ : Fin (2 * n)) = s := Fin.ext hs
      rwa [hfin]
    · funext t
      dsimp only [A]
      have ht : 2 * (t.1 / 2) + t.1 % 2 = t.1 := by omega
      exact congr_arg w (Fin.ext ht)

-- Partition rgsSet L (L ≥ 1) by maximum value k : Fin 4
private lemma card_rgs_eq_sum (L : ℕ) (hL : 1 ≤ L) :
    (rgsSet L).card = (rgsMax L 0).card + (rgsMax L 1).card + (rgsMax L 2).card + (rgsMax L 3).card := by
  have hunion : rgsSet L = rgsMax L 0 ∪ rgsMax L 1 ∪ rgsMax L 2 ∪ rgsMax L 3 := by
    ext w
    simp only [Finset.mem_union, rgsMax, Finset.mem_filter]
    constructor
    · intro hw
      have hne : (Finset.univ.image w).Nonempty :=
        ⟨w ⟨0, by omega⟩, Finset.mem_image_of_mem w (Finset.mem_univ _)⟩
      obtain ⟨m, hm_eq⟩ : ∃ m : Fin 4, m = (Finset.univ.image w).max' hne := ⟨_, rfl⟩
      have hm_mem : m ∈ Finset.univ.image w := hm_eq ▸ Finset.max'_mem _ hne
      rcases Finset.mem_image.mp hm_mem with ⟨t0, _, ht0⟩
      have hm_le : ∀ t : Fin L, w t ≤ m := fun t =>
        hm_eq ▸ Finset.le_max' _ _ (Finset.mem_image_of_mem w (Finset.mem_univ t))
      fin_cases m
      · exact Or.inl (Or.inl (Or.inl ⟨hw, hm_le, ⟨t0, ht0⟩⟩))
      · exact Or.inl (Or.inl (Or.inr ⟨hw, hm_le, ⟨t0, ht0⟩⟩))
      · exact Or.inl (Or.inr ⟨hw, hm_le, ⟨t0, ht0⟩⟩)
      · exact Or.inr ⟨hw, hm_le, ⟨t0, ht0⟩⟩
    · rintro (((h | h) | h) | h) <;> exact h.1
  have hdisj : ∀ j k : Fin 4, j ≠ k → Disjoint (rgsMax L j) (rgsMax L k) := by
    intro j k hjk
    rw [Finset.disjoint_left]; intro w hj hk
    simp only [rgsMax, Finset.mem_filter] at hj hk
    rcases hj.2.2 with ⟨t1, ht1⟩; rcases hk.2.2 with ⟨t2, ht2⟩
    have h1 : j ≤ k := ht1 ▸ hk.2.1 t1
    have h2 : k ≤ j := ht2 ▸ hj.2.1 t2
    exact hjk (le_antisymm h1 h2)
  rw [hunion]
  rw [Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_union_left, Finset.disjoint_union_left]
        exact ⟨⟨hdisj 0 3 (by decide), hdisj 1 3 (by decide)⟩, hdisj 2 3 (by decide)⟩)]
  rw [Finset.card_union_of_disjoint (by
        rw [Finset.disjoint_union_left]
        exact ⟨hdisj 0 2 (by decide), hdisj 1 2 (by decide)⟩)]
  rw [Finset.card_union_of_disjoint (hdisj 0 1 (by decide))]

-- Helper: extend a word w : Fin L → Fin 4 by appending a : Fin 4 at Fin.last L
private def snocWord {L : ℕ} (w : Fin L → Fin 4) (a : Fin 4) : Fin (L + 1) → Fin 4 :=
  fun i => if h : i.1 < L then w ⟨i.1, h⟩ else a

private lemma snocWord_castSucc {L : ℕ} (w : Fin L → Fin 4) (a : Fin 4) (i : Fin L) :
    snocWord w a i.castSucc = w i := by
  simp only [snocWord, Fin.val_castSucc, i.2, ↓reduceDIte]

private lemma snocWord_last {L : ℕ} (w : Fin L → Fin 4) (a : Fin 4) :
    snocWord w a (Fin.last L) = a := by
  simp only [snocWord, Fin.val_last, lt_irrefl, ↓reduceDIte]

-- Recurrence step for rgsMax (L + 1) 0
private lemma card_rgsMax_zero (L : ℕ) (hL : 1 ≤ L) :
    (rgsMax L 0).card = 1 := by
  have h : rgsMax L 0 = {fun _ => 0} := by
    ext w
    simp only [rgsMax, rgsSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · rintro ⟨_, hle, _⟩
      funext t
      exact Fin.le_zero_iff.mp (hle t)
    · rintro rfl
      refine ⟨fun _ v hv => by dsimp only at hv; exact absurd hv (by omega), fun _ => le_rfl, ⟨⟨0, by omega⟩, rfl⟩⟩
  rw [h, Finset.card_singleton]

-- Recurrence step for rgsMax (L + 1) k when k.1 > 0
private lemma card_rgsMax_succ_pos (L : ℕ) (k : Fin 4) (hk : 0 < k.1) :
    (rgsMax (L + 1) k).card =
      (k.1 + 1) * (rgsMax L k).card + (rgsMax L ⟨k.1 - 1, by omega⟩).card := by
  let prevK : Fin 4 := ⟨k.1 - 1, by omega⟩
  -- Split rgsMax (L + 1) k into: (1) prefix already hits k, (2) prefix has max k-1 and last = k
  let S1 := (rgsMax (L + 1) k).filter (fun w => ∃ t : Fin L, w t.castSucc = k)
  let S2 := (rgsMax (L + 1) k).filter (fun w => ¬ ∃ t : Fin L, w t.castSucc = k)
  have hsplit : rgsMax (L + 1) k = S1 ∪ S2 := by
    ext w; simp only [S1, S2, Finset.mem_union, Finset.mem_filter]; tauto
  have hdisj : Disjoint S1 S2 := by
    rw [Finset.disjoint_left]; intro w h1 h2
    simp only [S1, S2, Finset.mem_filter] at h1 h2; exact h2.2 h1.2
  rw [hsplit, Finset.card_union_of_disjoint hdisj]
  -- S1 ↔ rgsMax L k × {a : Fin 4 | a ≤ k}
  have hc1 : S1.card = (k.1 + 1) * (rgsMax L k).card := by
    let vals := Finset.univ.filter (fun a : Fin 4 => a ≤ k)
    have hvals : vals.card = k.1 + 1 := by fin_cases k <;> decide
    rw [← hvals, ← Finset.card_product]
    refine Finset.card_bij (fun w _ => (w (Fin.last L), fun i : Fin L => w i.castSucc)) ?_ ?_ ?_
    · intro w hw
      simp only [S1, rgsMax, rgsSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simp only [Finset.mem_product, vals, rgsMax, rgsSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨hw.1.2.1 (Fin.last L), ⟨fun t v hv => ?_, fun t => hw.1.2.1 t.castSucc, hw.2⟩⟩
      rcases hw.1.1 t.castSucc v hv with ⟨s, hlt, heq⟩
      exact ⟨⟨s.1, by simp only [Fin.val_castSucc] at hlt; omega⟩, by simp only [Fin.val_castSucc] at hlt; omega, heq⟩
    · intro w1 _ w2 _ h
      simp only [Prod.mk.injEq] at h
      funext i
      by_cases hi : i.1 < L
      · exact congr_fun h.2 ⟨i.1, hi⟩
      · have hlast : i = Fin.last L := Fin.ext (by simp only [Fin.val_last]; omega)
        rw [hlast, h.1]
    · intro ⟨a, u⟩ hau
      simp only [Finset.mem_product, vals, rgsMax, rgsSet, Finset.mem_filter, Finset.mem_univ, true_and] at hau
      refine ⟨snocWord u a, ?_, ?_⟩
      · simp only [S1, rgsMax, rgsSet, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨⟨fun t v hv => ?_, fun t => ?_, ?_⟩, ?_⟩
        · by_cases ht : t.1 < L
          · simp only [snocWord, ht, ↓reduceDIte] at hv
            rcases hau.2.1 ⟨t.1, ht⟩ v hv with ⟨s, hlt, heq⟩
            exact ⟨s.castSucc, by simp only [Fin.val_castSucc]; omega, by rw [snocWord_castSucc]; exact heq⟩
          · have hlast : t = Fin.last L := Fin.ext (by simp only [Fin.val_last]; omega)
            rw [hlast, snocWord_last] at hv
            rcases hau.2.2.2 with ⟨t0, ht0⟩
            by_cases hvk : v < k
            · have hvt : v < u t0 := ht0.symm ▸ hvk
              rcases hau.2.1 t0 v hvt with ⟨s, _, heq⟩
              exact ⟨s.castSucc, by simp only [Fin.val_castSucc]; omega, by rw [snocWord_castSucc]; exact heq⟩
            · have : v = k := le_antisymm (le_trans (le_of_lt hv) hau.1) (not_lt.mp hvk)
              omega
        · by_cases ht : t.1 < L
          · simp only [snocWord, ht, ↓reduceDIte]; exact hau.2.2.1 ⟨t.1, ht⟩
          · have hlast : t = Fin.last L := Fin.ext (by simp only [Fin.val_last]; omega)
            rw [hlast, snocWord_last]; exact hau.1
        · rcases hau.2.2.2 with ⟨t0, ht0⟩
          exact ⟨t0.castSucc, by rw [snocWord_castSucc]; exact ht0⟩
        · rcases hau.2.2.2 with ⟨t0, ht0⟩
          exact ⟨t0, by rw [snocWord_castSucc]; exact ht0⟩
      · simp only [Prod.mk.injEq, snocWord_last, true_and]
        exact funext (snocWord_castSucc u a)
  -- S2 ↔ rgsMax L prevK
  have hc2 : S2.card = (rgsMax L prevK).card := by
    refine Finset.card_bij (fun w _ i => w i.castSucc) ?_ ?_ ?_
    · intro w hw
      simp only [S2, rgsMax, rgsSet, Finset.mem_filter, Finset.mem_univ, true_and] at hw
      simp only [rgsMax, rgsSet, Finset.mem_filter, Finset.mem_univ, true_and]
      have hlast_eq : w (Fin.last L) = k := by
        rcases hw.1.2.2 with ⟨t0, ht0⟩
        by_cases hlt : t0.1 < L
        · exact absurd ⟨⟨t0.1, hlt⟩, ht0⟩ hw.2
        · have : t0 = Fin.last L := Fin.ext (by simp only [Fin.val_last]; omega)
          rwa [← this]
      have hprev_hit : ∃ t : Fin L, w t.castSucc = prevK := by
        have hv : prevK < w (Fin.last L) := by rw [hlast_eq]; change k.1 - 1 < k.1; omega
        rcases hw.1.1 (Fin.last L) prevK hv with ⟨s, hlt, heq⟩
        exact ⟨⟨s.1, by simp only [Fin.val_last] at hlt; omega⟩, heq⟩
      refine ⟨fun t v hv => ?_, fun t => ?_, hprev_hit⟩
      · rcases hw.1.1 t.castSucc v hv with ⟨s, hlt, heq⟩
        exact ⟨⟨s.1, by simp only [Fin.val_castSucc] at hlt; omega⟩, by simp only [Fin.val_castSucc] at hlt; omega, heq⟩
      · have hle := hw.1.2.1 t.castSucc
        have hne : w t.castSucc ≠ k := fun h => hw.2 ⟨t, h⟩
        have hlt : (w t.castSucc).1 < k.1 := lt_of_le_of_ne hle (fun h => hne (Fin.ext h))
        change (w t.castSucc).1 ≤ k.1 - 1; omega
    · intro w1 hw1 w2 hw2 h
      simp only [S2, rgsMax, Finset.mem_filter] at hw1 hw2
      have hlast1 : w1 (Fin.last L) = k := by
        rcases hw1.1.2.2 with ⟨t0, ht0⟩
        by_cases hlt : t0.1 < L
        · exact absurd ⟨⟨t0.1, hlt⟩, ht0⟩ hw1.2
        · have : t0 = Fin.last L := Fin.ext (by simp only [Fin.val_last]; omega); rwa [← this]
      have hlast2 : w2 (Fin.last L) = k := by
        rcases hw2.1.2.2 with ⟨t0, ht0⟩
        by_cases hlt : t0.1 < L
        · exact absurd ⟨⟨t0.1, hlt⟩, ht0⟩ hw2.2
        · have : t0 = Fin.last L := Fin.ext (by simp only [Fin.val_last]; omega); rwa [← this]
      funext i
      by_cases hi : i.1 < L
      · exact congr_fun h ⟨i.1, hi⟩
      · have hlast : i = Fin.last L := Fin.ext (by simp only [Fin.val_last]; omega)
        rw [hlast, hlast1, hlast2]
    · intro u hu
      simp only [rgsMax, rgsSet, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      refine ⟨snocWord u k, ?_, funext (snocWord_castSucc u k)⟩
      simp only [S2, rgsMax, rgsSet, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨fun t v hv => ?_, fun t => ?_, ⟨Fin.last L, snocWord_last u k⟩⟩, ?_⟩
      · by_cases ht : t.1 < L
        · simp only [snocWord, ht, ↓reduceDIte] at hv
          rcases hu.1 ⟨t.1, ht⟩ v hv with ⟨s, hlt, heq⟩
          exact ⟨s.castSucc, by simp only [Fin.val_castSucc]; omega, by rw [snocWord_castSucc]; exact heq⟩
        · have hlast : t = Fin.last L := Fin.ext (by simp only [Fin.val_last]; omega)
          rw [hlast, snocWord_last] at hv
          rcases hu.2.2 with ⟨t0, ht0⟩
          by_cases hvprev : v = prevK
          · exact ⟨t0.castSucc, by simp only [Fin.val_castSucc]; omega, by rw [snocWord_castSucc, ht0, hvprev]⟩
          · have hlt : v < u t0 := by
              rw [ht0]
              have h1 : v.1 < k.1 := hv
              have h2 : v.1 ≠ k.1 - 1 := fun h => hvprev (Fin.ext h)
              change v.1 < k.1 - 1; omega
            rcases hu.1 t0 v hlt with ⟨s, _, heq⟩
            exact ⟨s.castSucc, by simp only [Fin.val_castSucc]; omega, by rw [snocWord_castSucc]; exact heq⟩
      · by_cases ht : t.1 < L
        · simp only [snocWord, ht, ↓reduceDIte]
          have := hu.2.1 ⟨t.1, ht⟩
          change (u ⟨t.1, ht⟩).1 ≤ k.1
          change (u ⟨t.1, ht⟩).1 ≤ k.1 - 1 at this
          omega
        · have hlast : t = Fin.last L := Fin.ext (by simp only [Fin.val_last]; omega)
          rw [hlast, snocWord_last]
      · rintro ⟨t, ht⟩
        rw [snocWord_castSucc] at ht
        have := hu.2.1 t
        rw [ht] at this
        change k.1 ≤ k.1 - 1 at this
        omega
  rw [hc1, hc2]

-- Closed forms for all 4 states by induction on m (where L = m + 1)
private lemma rgsMax_formulas (m : ℕ) :
    (rgsMax (m + 1) 0).card = 1 ∧
    (rgsMax (m + 1) 1).card + 1 = 2 ^ m ∧
    2 * (rgsMax (m + 1) 2).card + 2 ^ (m + 1) = 3 ^ m + 1 ∧
    6 * (rgsMax (m + 1) 3).card + 3 ^ (m + 1) + 1 = 4 ^ m + 3 * 2 ^ m := by
  induction m with
  | zero =>
    have h0 : (rgsMax 1 0).card = 1 := card_rgsMax_zero 1 (by omega)
    have h1 : (rgsMax 1 1).card = 0 := by
      have : rgsMax 1 1 = ∅ := by
        ext w; simp only [rgsMax, rgsSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false]
        rintro ⟨hrgs, _, ⟨t, ht⟩⟩
        have ht0 : t = 0 := Fin.eq_zero t
        rw [ht0] at ht
        rcases hrgs 0 0 (by rw [ht]; decide) with ⟨s, hs, _⟩
        omega
      rw [this, Finset.card_empty]
    have h2 : (rgsMax 1 2).card = 0 := by
      have : rgsMax 1 2 = ∅ := by
        ext w; simp only [rgsMax, rgsSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false]
        rintro ⟨hrgs, _, ⟨t, ht⟩⟩
        have ht0 : t = 0 := Fin.eq_zero t
        rw [ht0] at ht
        rcases hrgs 0 0 (by rw [ht]; decide) with ⟨s, hs, _⟩
        omega
      rw [this, Finset.card_empty]
    have h3 : (rgsMax 1 3).card = 0 := by
      have : rgsMax 1 3 = ∅ := by
        ext w; simp only [rgsMax, rgsSet, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.notMem_empty, iff_false]
        rintro ⟨hrgs, _, ⟨t, ht⟩⟩
        have ht0 : t = 0 := Fin.eq_zero t
        rw [ht0] at ht
        rcases hrgs 0 0 (by rw [ht]; decide) with ⟨s, hs, _⟩
        omega
      rw [this, Finset.card_empty]
    rw [h0, h1, h2, h3]; norm_num
  | succ m ih =>
    rcases ih with ⟨ih0, ih1, ih2, ih3⟩
    have s0 : (rgsMax (m + 1 + 1) 0).card = 1 := card_rgsMax_zero (m + 1 + 1) (by omega)
    have s1 : (rgsMax (m + 1 + 1) 1).card = 2 * (rgsMax (m + 1) 1).card + (rgsMax (m + 1) 0).card :=
      card_rgsMax_succ_pos (m + 1) 1 (by decide)
    have s2 : (rgsMax (m + 1 + 1) 2).card = 3 * (rgsMax (m + 1) 2).card + (rgsMax (m + 1) 1).card :=
      card_rgsMax_succ_pos (m + 1) 2 (by decide)
    have s3 : (rgsMax (m + 1 + 1) 3).card = 4 * (rgsMax (m + 1) 3).card + (rgsMax (m + 1) 2).card :=
      card_rgsMax_succ_pos (m + 1) 3 (by decide)
    have p2 : 2 ^ (m + 1) = 2 * 2 ^ m := by ring
    have p2' : 2 ^ (m + 1 + 1) = 4 * 2 ^ m := by ring
    have p3 : 3 ^ (m + 1) = 3 * 3 ^ m := by ring
    have p3' : 3 ^ (m + 1 + 1) = 9 * 3 ^ m := by ring
    have p4 : 4 ^ (m + 1) = 4 * 4 ^ m := by ring
    refine ⟨s0, by omega, by omega, by omega⟩

theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = (8 + 3 * 2 ^ (1 + 2 * n) + 16 ^ n) / 24 := by
  intro n hn
  have ha : a n = (Finset.univ.filter (isValid n)).card := by
    unfold a
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [ha, card_valid_eq_rgs n, card_rgs_eq_sum (2 * n) (by omega)]
  have hm : 2 * n = (2 * n - 1) + 1 := by omega
  rcases rgsMax_formulas (2 * n - 1) with ⟨h0, h1, h2, h3⟩
  rw [← hm] at h0 h1 h2 h3
  have hsum6 : 6 * ((rgsMax (2 * n) 0).card + (rgsMax (2 * n) 1).card +
      (rgsMax (2 * n) 2).card + (rgsMax (2 * n) 3).card) =
      2 + 3 * 2 ^ (2 * n - 1) + 4 ^ (2 * n - 1) := by
    have p2 : 2 ^ (2 * n) = 2 * 2 ^ (2 * n - 1) := by rw [← pow_succ', ← hm]
    have p3 : 3 ^ (2 * n) = 3 * 3 ^ (2 * n - 1) := by rw [← pow_succ', ← hm]
    omega
  have hpow2 : 4 * 2 ^ (2 * n - 1) = 2 ^ (1 + 2 * n) := by
    have : 1 + 2 * n = (2 * n - 1) + 2 := by omega
    rw [this]; ring
  have hpow4 : 4 * 4 ^ (2 * n - 1) = 16 ^ n := by
    have h1 : 4 * 4 ^ (2 * n - 1) = 4 ^ (2 * n) := by rw [← pow_succ', ← hm]
    rw [h1, pow_mul]; norm_num
  omega

end
end ProofA208402

theorem OMA.solution : type_of% @OMA.S_oeis_a208402.main :=
  ProofA208402.main
