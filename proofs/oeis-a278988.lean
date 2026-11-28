import OMAStatements.S_oeis_a278988
import Mathlib

/-!
Credit: @ivillar
Proof: a transfer-matrix argument. The state of a word records how often each letter occurs,
capped at 2; appending a letter to a word in standard order keeps it in standard order exactly
when the previous letter already occurs, and updates the state in a fixed way. This gives linear
recurrences for the numbers N(n, s) of standard words with state s; their exponential-polynomial
solutions (valid from n = 4, checked against the 81 words of length 4) are proved by induction,
and a(n) is the sum over the states in which no letter occurs exactly once.
-/

namespace OMAA278988Helpers

open OMA.S_oeis_a278988 Finset

instance decStd {n : ℕ} : DecidablePred (StdOrder (n := n)) := fun w => by
  unfold StdOrder
  infer_instance

/-- Number of occurrences of the letter `c`. -/
def cnt {n : ℕ} (w : Fin n → Fin 3) (c : Fin 3) : ℕ := #(univ.filter fun i => w i = c)

/-- The state of a word: the numbers of occurrences of the three letters, capped at 2. -/
def st {n : ℕ} (w : Fin n → Fin 3) : ℕ × ℕ × ℕ :=
  (min (cnt w 0) 2, min (cnt w 1) 2, min (cnt w 2) 2)

/-- Number of words of length `n` in standard order with state `s`. -/
def N (n : ℕ) (s : ℕ × ℕ × ℕ) : ℕ :=
  #(univ.filter fun w : Fin n → Fin 3 => StdOrder w ∧ st w = s)

/-- Appending the letter `x` is allowed in a standard word of state `s`. -/
def okc (s : ℕ × ℕ × ℕ) (x : ℕ) : Prop :=
  x = 0 ∨ (x = 1 ∧ 1 ≤ s.1) ∨ (x = 2 ∧ 1 ≤ s.2.1)

instance : ∀ s x, Decidable (okc s x) := fun s x => by unfold okc; infer_instance

/-- The state after appending the letter `x`. -/
def step (s : ℕ × ℕ × ℕ) (x : ℕ) : ℕ × ℕ × ℕ :=
  (if x = 0 then min (s.1 + 1) 2 else s.1, if x = 1 then min (s.2.1 + 1) 2 else s.2.1,
    if x = 2 then min (s.2.2 + 1) 2 else s.2.2)

/-- The possible states. -/
def T : Finset (ℕ × ℕ × ℕ) := range 3 ×ˢ range 3 ×ˢ range 3

theorem cnt_snoc {n : ℕ} (v : Fin n → Fin 3) (x c : Fin 3) :
    cnt (Fin.snoc v x : Fin (n + 1) → Fin 3) c = cnt v c + if x = c then 1 else 0 := by
  unfold cnt
  rw [card_filter, card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem cnt_pos {n : ℕ} (v : Fin n → Fin 3) (c : Fin 3) : 0 < cnt v c ↔ ∃ j, v j = c := by
  unfold cnt
  rw [card_pos, filter_nonempty_iff]
  simp

theorem std_snoc {n : ℕ} (v : Fin n → Fin 3) (x : Fin 3) :
    StdOrder (Fin.snoc v x : Fin (n + 1) → Fin 3) ↔
      StdOrder v ∧ (x ≠ 0 → ∃ j, (v j : ℕ) + 1 = x) := by
  unfold StdOrder
  rw [Fin.forall_fin_succ']
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  apply and_congr
  · apply forall_congr'
    intro i
    apply imp_congr_right
    intro _
    rw [Fin.exists_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.castSucc_lt_castSucc_iff]
    constructor
    · rintro (h | ⟨h, -⟩)
      · exact h
      · exact absurd h (not_lt.mpr (Fin.castSucc_lt_last i).le)
    · exact Or.inl
  · apply imp_congr_right
    intro _
    rw [Fin.exists_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.castSucc_lt_last, true_and,
      lt_self_iff_false, false_and, or_false]

theorem ok_iff {n : ℕ} (v : Fin n → Fin 3) (x : Fin 3) :
    (x ≠ 0 → ∃ j, (v j : ℕ) + 1 = x) ↔ okc (st v) (x : ℕ) := by
  have A : (∃ j, (v j : ℕ) + 1 = (x : ℕ)) ↔
      ((x : ℕ) = 1 ∧ 0 < cnt v 0) ∨ ((x : ℕ) = 2 ∧ 0 < cnt v 1) := by
    rw [cnt_pos, cnt_pos]
    constructor
    · rintro ⟨j, hj⟩
      have hx := x.isLt
      by_cases h : (v j : ℕ) = 0
      · exact Or.inl ⟨by omega, j, Fin.ext (by rw [h]; rfl)⟩
      · exact Or.inr ⟨by omega, j, Fin.ext (by have := (v j).isLt; simp only [Fin.val_one]; omega)⟩
    · rintro (⟨hx, j, hj⟩ | ⟨hx, j, hj⟩)
      · exact ⟨j, by rw [hj, hx]; rfl⟩
      · exact ⟨j, by rw [hj, hx]; rfl⟩
  have B : x = 0 ↔ (x : ℕ) = 0 := Fin.ext_iff
  unfold okc st
  simp only [ne_eq, A, B]
  have := x.isLt
  omega

theorem st_snoc {n : ℕ} (v : Fin n → Fin 3) (x : Fin 3) :
    st (Fin.snoc v x : Fin (n + 1) → Fin 3) = step (st v) (x : ℕ) := by
  unfold st step
  rw [cnt_snoc, cnt_snoc, cnt_snoc]
  fin_cases x <;> simp <;> omega

theorem st_mem {n : ℕ} (v : Fin n → Fin 3) : st v ∈ T := by
  unfold st T
  simp only [mem_product, mem_range]
  omega

theorem trans (n : ℕ) (s : ℕ × ℕ × ℕ) :
    N (n + 1) s = ∑ x ∈ range 3, ∑ t ∈ T, if okc t x ∧ step t x = s then N n t else 0 := by
  rw [← Fin.sum_univ_eq_sum_range (fun x => ∑ t ∈ T, if okc t x ∧ step t x = s then N n t else 0)]
  let e : Fin 3 × (Fin n → Fin 3) ≃ (Fin (n + 1) → Fin 3) :=
    { toFun := fun p => Fin.snoc p.2 p.1
      invFun := fun w => (w (Fin.last n), Fin.init w)
      left_inv := fun p => by simp [Fin.init_snoc, Fin.snoc_last]
      right_inv := fun w => Fin.snoc_init_self w }
  unfold N
  rw [card_filter, ← e.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hR : ∀ t, (if okc t (x : ℕ) ∧ step t (x : ℕ) = s then
      #(univ.filter fun v : Fin n → Fin 3 => StdOrder v ∧ st v = t) else 0) =
      ∑ v : Fin n → Fin 3, if (okc t (x : ℕ) ∧ step t (x : ℕ) = s) ∧ (StdOrder v ∧ st v = t)
        then 1 else 0 := by
    intro t
    split_ifs with h
    · rw [card_filter]
      exact Finset.sum_congr rfl fun v _ => by simp [h]
    · simp [h]
  rw [Finset.sum_congr rfl fun t _ => hR t, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hl : (e (x, v)) = (Fin.snoc v x : Fin (n + 1) → Fin 3) := rfl
  rw [hl, Finset.sum_eq_single (st v)]
  · simp only [std_snoc, ok_iff, st_snoc]
    by_cases h1 : StdOrder v <;> by_cases h2 : okc (st v) (x : ℕ) <;>
      by_cases h3 : step (st v) (x : ℕ) = s <;> simp [h1, h2, h3]
  · intro t _ ht
    rw [if_neg]
    rintro ⟨-, -, h⟩
    exact ht h.symm
  · intro h
    exact absurd (st_mem v) h

/-- The states with no letter occurring exactly once. -/
def good (s : ℕ × ℕ × ℕ) : Prop := s.1 ≠ 1 ∧ s.2.1 ≠ 1 ∧ s.2.2 ≠ 1

instance : DecidablePred good := fun s => by unfold good; infer_instance

theorem rep_iff {n : ℕ} (w : Fin n → Fin 3) : Repeated w ↔ good (st w) := by
  have h0 := cnt_pos w 0
  have h1 := cnt_pos w 1
  have h2 := cnt_pos w 2
  unfold Repeated good st
  simp only
  constructor
  · intro h
    have e0 := h 0
    have e1 := h 1
    have e2 := h 2
    rw [← h0] at e0
    rw [← h1] at e1
    rw [← h2] at e2
    unfold cnt at h0 h1 h2
    simp only [cnt] at *
    omega
  · intro h c hc
    fin_cases c
    · have := h0.mpr hc
      unfold cnt at this h
      simp only [Fin.zero_eta, Fin.isValue] at *
      omega
    · have := h1.mpr hc
      unfold cnt at this h
      simp only [Fin.mk_one, Fin.isValue] at *
      omega
    · have := h2.mpr hc
      unfold cnt at this h
      simp only [Fin.reduceFinMk, Fin.isValue] at *
      omega

theorem a_eq (n : ℕ) : a n = ∑ t ∈ T, if good t then N n t else 0 := by
  classical
  unfold a
  rw [Fintype.card_subtype]
  have e : (univ.filter fun w : Fin n → Fin 3 => StdOrder w ∧ Repeated w) =
      univ.filter fun w : Fin n → Fin 3 => StdOrder w ∧ good (st w) :=
    filter_congr fun w _ => by rw [rep_iff]
  rw [e, card_eq_sum_card_fiberwise (f := st) (t := T) (fun w _ => st_mem w)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [filter_filter]
  unfold N
  split_ifs with h
  · congr 1
    apply filter_congr
    intro w _
    constructor
    · rintro ⟨⟨h1, -⟩, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨h1, h2 ▸ h⟩, h2⟩
  · rw [card_eq_zero, filter_eq_empty_iff]
    rintro w - ⟨⟨-, h1⟩, h2⟩
    exact h (h2 ▸ h1)

theorem tr_s000 (n : ℕ) : N (n + 1) (0, 0, 0) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s001 (n : ℕ) : N (n + 1) (0, 0, 1) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s002 (n : ℕ) : N (n + 1) (0, 0, 2) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s010 (n : ℕ) : N (n + 1) (0, 1, 0) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s011 (n : ℕ) : N (n + 1) (0, 1, 1) = N n (0, 1, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s012 (n : ℕ) : N (n + 1) (0, 1, 2) = N n (0, 1, 1) + N n (0, 1, 2) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s020 (n : ℕ) : N (n + 1) (0, 2, 0) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s021 (n : ℕ) : N (n + 1) (0, 2, 1) = N n (0, 2, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s022 (n : ℕ) : N (n + 1) (0, 2, 2) = N n (0, 2, 1) + N n (0, 2, 2) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s100 (n : ℕ) : N (n + 1) (1, 0, 0) = N n (0, 0, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s101 (n : ℕ) : N (n + 1) (1, 0, 1) = N n (0, 0, 1) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s102 (n : ℕ) : N (n + 1) (1, 0, 2) = N n (0, 0, 2) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s110 (n : ℕ) : N (n + 1) (1, 1, 0) = N n (0, 1, 0) + N n (1, 0, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s111 (n : ℕ) : N (n + 1) (1, 1, 1) = N n (0, 1, 1) + N n (1, 0, 1) + N n (1, 1, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s112 (n : ℕ) : N (n + 1) (1, 1, 2) = N n (0, 1, 2) + N n (1, 0, 2) + N n (1, 1, 1) + N n (1, 1, 2) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]; ring

theorem tr_s120 (n : ℕ) : N (n + 1) (1, 2, 0) = N n (0, 2, 0) + N n (1, 1, 0) + N n (1, 2, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]; ring

theorem tr_s121 (n : ℕ) : N (n + 1) (1, 2, 1) = N n (0, 2, 1) + N n (1, 1, 1) + N n (1, 2, 0) + N n (1, 2, 1) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]; ring

theorem tr_s122 (n : ℕ) : N (n + 1) (1, 2, 2) = N n (0, 2, 2) + N n (1, 1, 2) + N n (1, 2, 1) + N n (1, 2, 2) + N n (1, 2, 2) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]; ring

theorem tr_s200 (n : ℕ) : N (n + 1) (2, 0, 0) = N n (1, 0, 0) + N n (2, 0, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s201 (n : ℕ) : N (n + 1) (2, 0, 1) = N n (1, 0, 1) + N n (2, 0, 1) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s202 (n : ℕ) : N (n + 1) (2, 0, 2) = N n (1, 0, 2) + N n (2, 0, 2) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s210 (n : ℕ) : N (n + 1) (2, 1, 0) = N n (1, 1, 0) + N n (2, 0, 0) + N n (2, 1, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]; ring

theorem tr_s211 (n : ℕ) : N (n + 1) (2, 1, 1) = N n (1, 1, 1) + N n (2, 0, 1) + N n (2, 1, 0) + N n (2, 1, 1) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]; ring

theorem tr_s212 (n : ℕ) : N (n + 1) (2, 1, 2) = N n (1, 1, 2) + N n (2, 0, 2) + N n (2, 1, 1) + N n (2, 1, 2) + N n (2, 1, 2) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]; ring

theorem tr_s220 (n : ℕ) : N (n + 1) (2, 2, 0) = N n (1, 2, 0) + N n (2, 1, 0) + N n (2, 2, 0) + N n (2, 2, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]; ring

theorem tr_s221 (n : ℕ) : N (n + 1) (2, 2, 1) = N n (1, 2, 1) + N n (2, 1, 1) + N n (2, 2, 0) + N n (2, 2, 1) + N n (2, 2, 1) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]; ring

theorem tr_s222 (n : ℕ) : N (n + 1) (2, 2, 2) = N n (1, 2, 2) + N n (2, 1, 2) + N n (2, 2, 1) + N n (2, 2, 2) + N n (2, 2, 2) + N n (2, 2, 2) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]; ring

theorem b_s000 : N 4 (0, 0, 0) = 0 := by decide

theorem b_s001 : N 4 (0, 0, 1) = 0 := by decide

theorem b_s002 : N 4 (0, 0, 2) = 0 := by decide

theorem b_s010 : N 4 (0, 1, 0) = 0 := by decide

theorem b_s011 : N 4 (0, 1, 1) = 0 := by decide

theorem b_s012 : N 4 (0, 1, 2) = 0 := by decide

theorem b_s020 : N 4 (0, 2, 0) = 0 := by decide

theorem b_s021 : N 4 (0, 2, 1) = 0 := by decide

theorem b_s022 : N 4 (0, 2, 2) = 0 := by decide

theorem b_s100 : N 4 (1, 0, 0) = 0 := by decide

theorem b_s101 : N 4 (1, 0, 1) = 0 := by decide

theorem b_s102 : N 4 (1, 0, 2) = 0 := by decide

theorem b_s110 : N 4 (1, 1, 0) = 0 := by decide

theorem b_s111 : N 4 (1, 1, 1) = 0 := by decide

theorem b_s112 : N 4 (1, 1, 2) = 1 := by decide

theorem b_s120 : N 4 (1, 2, 0) = 1 := by decide

theorem b_s121 : N 4 (1, 2, 1) = 2 := by decide

theorem b_s122 : N 4 (1, 2, 2) = 0 := by decide

theorem b_s200 : N 4 (2, 0, 0) = 1 := by decide

theorem b_s201 : N 4 (2, 0, 1) = 0 := by decide

theorem b_s202 : N 4 (2, 0, 2) = 0 := by decide

theorem b_s210 : N 4 (2, 1, 0) = 3 := by decide

theorem b_s211 : N 4 (2, 1, 1) = 3 := by decide

theorem b_s212 : N 4 (2, 1, 2) = 0 := by decide

theorem b_s220 : N 4 (2, 2, 0) = 3 := by decide

theorem b_s221 : N 4 (2, 2, 1) = 0 := by decide

theorem b_s222 : N 4 (2, 2, 2) = 0 := by decide

theorem closed_all (n : ℕ) (hn : 4 ≤ n) :
    (N n (0, 0, 0) : ℚ) = 0 ∧
    (N n (0, 0, 1) : ℚ) = 0 ∧
    (N n (0, 0, 2) : ℚ) = 0 ∧
    (N n (0, 1, 0) : ℚ) = 0 ∧
    (N n (0, 1, 1) : ℚ) = 0 ∧
    (N n (0, 1, 2) : ℚ) = 0 ∧
    (N n (0, 2, 0) : ℚ) = 0 ∧
    (N n (0, 2, 1) : ℚ) = 0 ∧
    (N n (0, 2, 2) : ℚ) = 0 ∧
    (N n (1, 0, 0) : ℚ) = 0 ∧
    (N n (1, 0, 1) : ℚ) = 0 ∧
    (N n (1, 0, 2) : ℚ) = 0 ∧
    (N n (1, 1, 0) : ℚ) = 0 ∧
    (N n (1, 1, 1) : ℚ) = 0 ∧
    (N n (1, 1, 2) : ℚ) = (1 : ℚ) * (1) ∧
    (N n (1, 2, 0) : ℚ) = (1 : ℚ) * (1) ∧
    (N n (1, 2, 1) : ℚ) = (-2 : ℚ) * (1) + (1 : ℚ) * ((n : ℚ)) ∧
    (N n (1, 2, 2) : ℚ) = (-1 : ℚ) * ((n : ℚ)) + ((1 : ℚ) / 4) * (2 ^ n) ∧
    (N n (2, 0, 0) : ℚ) = (1 : ℚ) * (1) ∧
    (N n (2, 0, 1) : ℚ) = 0 ∧
    (N n (2, 0, 2) : ℚ) = 0 ∧
    (N n (2, 1, 0) : ℚ) = (-1 : ℚ) * (1) + (1 : ℚ) * ((n : ℚ)) ∧
    (N n (2, 1, 1) : ℚ) = (1 : ℚ) * (1) + ((-3 : ℚ) / 2) * ((n : ℚ)) + ((1 : ℚ) / 2) * ((n : ℚ) ^ 2) ∧
    (N n (2, 1, 2) : ℚ) = (-2 : ℚ) * (1) + ((1 : ℚ) / 2) * ((n : ℚ)) + ((-1 : ℚ) / 2) * ((n : ℚ) ^ 2) + ((1 : ℚ) / 2) * (2 ^ n) ∧
    (N n (2, 2, 0) : ℚ) = (-1 : ℚ) * (1) + (-1 : ℚ) * ((n : ℚ)) + ((1 : ℚ) / 2) * (2 ^ n) ∧
    (N n (2, 2, 1) : ℚ) = (2 : ℚ) * (1) + ((1 : ℚ) / 2) * ((n : ℚ)) + ((-1 : ℚ) / 2) * ((n : ℚ) ^ 2) + ((-3 : ℚ) / 4) * (2 ^ n) + ((1 : ℚ) / 4) * ((n : ℚ) * 2 ^ n) ∧
    (N n (2, 2, 2) : ℚ) = ((1 : ℚ) / 2) * (1) + ((1 : ℚ) / 2) * ((n : ℚ)) + ((1 : ℚ) / 2) * ((n : ℚ) ^ 2) + ((-1 : ℚ) / 2) * (2 ^ n) + ((-1 : ℚ) / 4) * ((n : ℚ) * 2 ^ n) + ((1 : ℚ) / 6) * (3 ^ n) := by
  induction n, hn using Nat.le_induction with
  | base =>
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [b_s000, b_s001, b_s002, b_s010, b_s011, b_s012, b_s020, b_s021, b_s022, b_s100, b_s101, b_s102, b_s110, b_s111, b_s112, b_s120, b_s121, b_s122, b_s200, b_s201, b_s202, b_s210, b_s211, b_s212, b_s220, b_s221, b_s222] <;> norm_num
  | succ n hn ih =>
    obtain ⟨hs000, hs001, hs002, hs010, hs011, hs012, hs020, hs021, hs022, hs100, hs101, hs102, hs110, hs111, hs112, hs120, hs121, hs122, hs200, hs201, hs202, hs210, hs211, hs212, hs220, hs221, hs222⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [tr_s000]
      push_cast
      all_goals simp
    · rw [tr_s001]
      push_cast
      all_goals simp
    · rw [tr_s002]
      push_cast
      all_goals simp
    · rw [tr_s010]
      push_cast
      all_goals simp
    · rw [tr_s011]
      all_goals (rw [hs010])
    · rw [tr_s012]
      push_cast
      all_goals (rw [hs011, hs012]; ring)
    · rw [tr_s020]
      push_cast
      all_goals simp
    · rw [tr_s021]
      all_goals (rw [hs020])
    · rw [tr_s022]
      push_cast
      all_goals (rw [hs021, hs022]; ring)
    · rw [tr_s100]
      all_goals (rw [hs000])
    · rw [tr_s101]
      all_goals (rw [hs001])
    · rw [tr_s102]
      all_goals (rw [hs002])
    · rw [tr_s110]
      push_cast
      all_goals (rw [hs010, hs100]; ring)
    · rw [tr_s111]
      push_cast
      all_goals (rw [hs011, hs101, hs110]; ring)
    · rw [tr_s112]
      push_cast
      all_goals (rw [hs012, hs102, hs111, hs112]; ring)
    · rw [tr_s120]
      push_cast
      all_goals (rw [hs020, hs110, hs120]; ring)
    · rw [tr_s121]
      push_cast
      all_goals (rw [hs021, hs111, hs120, hs121]; ring)
    · rw [tr_s122]
      push_cast
      all_goals (rw [hs022, hs112, hs121, hs122]; ring)
    · rw [tr_s200]
      push_cast
      all_goals (rw [hs100, hs200]; ring)
    · rw [tr_s201]
      push_cast
      all_goals (rw [hs101, hs201]; ring)
    · rw [tr_s202]
      push_cast
      all_goals (rw [hs102, hs202]; ring)
    · rw [tr_s210]
      push_cast
      all_goals (rw [hs110, hs200, hs210]; ring)
    · rw [tr_s211]
      push_cast
      all_goals (rw [hs111, hs201, hs210, hs211]; ring)
    · rw [tr_s212]
      push_cast
      all_goals (rw [hs112, hs202, hs211, hs212]; ring)
    · rw [tr_s220]
      push_cast
      all_goals (rw [hs120, hs210, hs220]; ring)
    · rw [tr_s221]
      push_cast
      all_goals (rw [hs121, hs211, hs220, hs221]; ring)
    · rw [tr_s222]
      push_cast
      all_goals (rw [hs122, hs212, hs221, hs222]; ring)

theorem a_closed (n : ℕ) (hn : 4 ≤ n) : (a n : ℚ) =
    (2 * (3 + 3 ^ n) - 3 * (2 + 2 ^ n) * n + 6 * n ^ 2) / 12 := by
  rw [a_eq]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [good]
  obtain ⟨h000, -, h002, -, -, -, h020, -, h022, -, -, -, -, -, -, -, -, -, h200, -, h202, -, -, -, h220, -, h222⟩ :=
    closed_all n hn
  rw [h000, h002, h020, h022, h200, h202, h220, h222]
  ring

end OMAA278988Helpers

open OMAA278988Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a278988.main := by
  have hz : ∀ n : ℕ, 4 ≤ n → (OMA.S_oeis_a278988.a n : ℤ) * 12 =
      2 * (3 + 3 ^ n) - 3 * (2 + 2 ^ n) * n + 6 * n ^ 2 := by
    intro n hn
    have h := a_closed n hn
    have h' : ((OMA.S_oeis_a278988.a n : ℤ) * 12 : ℚ) =
        ((2 * (3 + 3 ^ n) - 3 * (2 + 2 ^ n) * n + 6 * n ^ 2 : ℤ) : ℚ) := by
      push_cast
      rw [h]
      ring
    exact_mod_cast h'
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rw [← hz n hn, Int.mul_ediv_cancel _ (by norm_num)]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 10 := ⟨n - 10, by omega⟩
    rw [show m + 10 - 1 = m + 9 by omega, show m + 10 - 2 = m + 8 by omega,
      show m + 10 - 3 = m + 7 by omega, show m + 10 - 4 = m + 6 by omega,
      show m + 10 - 5 = m + 5 by omega, show m + 10 - 6 = m + 4 by omega]
    have q0 := hz (m + 10) (by omega)
    have q1 := hz (m + 9) (by omega)
    have q2 := hz (m + 8) (by omega)
    have q3 := hz (m + 7) (by omega)
    have q4 := hz (m + 6) (by omega)
    have q5 := hz (m + 5) (by omega)
    have q6 := hz (m + 4) (by omega)
    push_cast at q0 q1 q2 q3 q4 q5 q6
    have : ((OMA.S_oeis_a278988.a (m + 10) : ℤ) -
        (10 * OMA.S_oeis_a278988.a (m + 9) - 40 * OMA.S_oeis_a278988.a (m + 8) +
          82 * OMA.S_oeis_a278988.a (m + 7) - 91 * OMA.S_oeis_a278988.a (m + 6) +
          52 * OMA.S_oeis_a278988.a (m + 5) - 12 * OMA.S_oeis_a278988.a (m + 4))) * 12 = 0 := by
      linear_combination q0 - 10 * q1 + 40 * q2 - 82 * q3 + 91 * q4 - 52 * q5 + 12 * q6
    have h12 : ((OMA.S_oeis_a278988.a (m + 10) : ℤ) -
        (10 * OMA.S_oeis_a278988.a (m + 9) - 40 * OMA.S_oeis_a278988.a (m + 8) +
          82 * OMA.S_oeis_a278988.a (m + 7) - 91 * OMA.S_oeis_a278988.a (m + 6) +
          52 * OMA.S_oeis_a278988.a (m + 5) - 12 * OMA.S_oeis_a278988.a (m + 4))) = 0 := by
      rcases mul_eq_zero.mp this with h | h
      · exact h
      · norm_num at h
    linarith
