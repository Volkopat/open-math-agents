import OMAStatements.S_oeis_a278989
import Mathlib

/-!
# A278989: proof of Barker's recurrence

Credit: @ivillar (the transfer-matrix method follows the proof of the sibling entry A278988 by
the same account)

A transfer-matrix argument. The state of a word records how often each of the four letters
occurs, capped at 2; appending a letter to a word in standard order keeps it in standard order
exactly when the previous letter already occurs, and updates the state in a fixed way. This gives
linear recurrences for the numbers N(n, s) of standard words with state s (81 states). Their
values at n = 5 are computed from the empty word, and their exponential-polynomial closed forms
(in 1, n, n^2, n^3, 2^n, n 2^n, n^2 2^n, 3^n, n 3^n, 4^n, valid from n = 5) are proved by
induction. a(n) is the sum over the states in which no letter occurs exactly once; its closed form
satisfies the recurrence, which therefore holds for n > 14.
-/

namespace OMAA278989Helpers

open OMA.S_oeis_a278989 Finset

instance decStd {n : ℕ} : DecidablePred (StdOrder (n := n)) := fun w => by
  unfold StdOrder
  infer_instance

/-- Number of occurrences of the letter `c`. -/
def cnt {n : ℕ} (w : Fin n → Fin 4) (c : Fin 4) : ℕ := #(univ.filter fun i => w i = c)

/-- The state of a word: the numbers of occurrences of the four letters, capped at 2. -/
def st {n : ℕ} (w : Fin n → Fin 4) : ℕ × ℕ × ℕ × ℕ :=
  (min (cnt w 0) 2, min (cnt w 1) 2, min (cnt w 2) 2, min (cnt w 3) 2)

/-- Number of words of length `n` in standard order with state `s`. -/
def N (n : ℕ) (s : ℕ × ℕ × ℕ × ℕ) : ℕ :=
  #(univ.filter fun w : Fin n → Fin 4 => StdOrder w ∧ st w = s)

/-- Appending the letter `x` is allowed in a standard word of state `s`. -/
def okc (s : ℕ × ℕ × ℕ × ℕ) (x : ℕ) : Prop :=
  x = 0 ∨ (x = 1 ∧ 1 ≤ s.1) ∨ (x = 2 ∧ 1 ≤ s.2.1) ∨ (x = 3 ∧ 1 ≤ s.2.2.1)

instance : ∀ s x, Decidable (okc s x) := fun s x => by unfold okc; infer_instance

/-- The state after appending the letter `x`. -/
def step (s : ℕ × ℕ × ℕ × ℕ) (x : ℕ) : ℕ × ℕ × ℕ × ℕ :=
  (if x = 0 then min (s.1 + 1) 2 else s.1, if x = 1 then min (s.2.1 + 1) 2 else s.2.1,
    if x = 2 then min (s.2.2.1 + 1) 2 else s.2.2.1,
    if x = 3 then min (s.2.2.2 + 1) 2 else s.2.2.2)

/-- The possible states. -/
def T : Finset (ℕ × ℕ × ℕ × ℕ) := range 3 ×ˢ range 3 ×ˢ range 3 ×ˢ range 3

theorem cnt_snoc {n : ℕ} (v : Fin n → Fin 4) (x c : Fin 4) :
    cnt (Fin.snoc v x : Fin (n + 1) → Fin 4) c = cnt v c + if x = c then 1 else 0 := by
  unfold cnt
  rw [card_filter, card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem cnt_pos {n : ℕ} (v : Fin n → Fin 4) (c : Fin 4) : 0 < cnt v c ↔ ∃ j, v j = c := by
  unfold cnt
  rw [card_pos, filter_nonempty_iff]
  simp

theorem std_snoc {n : ℕ} (v : Fin n → Fin 4) (x : Fin 4) :
    StdOrder (Fin.snoc v x : Fin (n + 1) → Fin 4) ↔
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

theorem ok_iff {n : ℕ} (v : Fin n → Fin 4) (x : Fin 4) :
    (x ≠ 0 → ∃ j, (v j : ℕ) + 1 = x) ↔ okc (st v) (x : ℕ) := by
  have A : (∃ j, (v j : ℕ) + 1 = (x : ℕ)) ↔
      ((x : ℕ) = 1 ∧ 0 < cnt v 0) ∨ ((x : ℕ) = 2 ∧ 0 < cnt v 1) ∨
        ((x : ℕ) = 3 ∧ 0 < cnt v 2) := by
    rw [cnt_pos, cnt_pos, cnt_pos]
    constructor
    · rintro ⟨j, hj⟩
      have hx := x.isLt
      have hv := (v j).isLt
      rcases (show (v j : ℕ) = 0 ∨ (v j : ℕ) = 1 ∨ (v j : ℕ) = 2 by omega) with h | h | h
      · exact Or.inl ⟨by omega, j, Fin.ext (by rw [h]; rfl)⟩
      · exact Or.inr (Or.inl ⟨by omega, j, Fin.ext (by rw [h]; rfl)⟩)
      · exact Or.inr (Or.inr ⟨by omega, j, Fin.ext (by rw [h]; rfl)⟩)
    · rintro (⟨hx, j, hj⟩ | ⟨hx, j, hj⟩ | ⟨hx, j, hj⟩)
      · exact ⟨j, by rw [hj, hx]; rfl⟩
      · exact ⟨j, by rw [hj, hx]; rfl⟩
      · exact ⟨j, by rw [hj, hx]; rfl⟩
  have B : x = 0 ↔ (x : ℕ) = 0 := Fin.ext_iff
  unfold okc st
  simp only [ne_eq, A, B]
  have := x.isLt
  omega

theorem st_snoc {n : ℕ} (v : Fin n → Fin 4) (x : Fin 4) :
    st (Fin.snoc v x : Fin (n + 1) → Fin 4) = step (st v) (x : ℕ) := by
  unfold st step
  rw [cnt_snoc, cnt_snoc, cnt_snoc, cnt_snoc]
  fin_cases x <;> simp <;> omega

theorem st_mem {n : ℕ} (v : Fin n → Fin 4) : st v ∈ T := by
  unfold st T
  simp only [mem_product, mem_range]
  omega

theorem trans (n : ℕ) (s : ℕ × ℕ × ℕ × ℕ) :
    N (n + 1) s = ∑ x ∈ range 4, ∑ t ∈ T, if okc t x ∧ step t x = s then N n t else 0 := by
  rw [← Fin.sum_univ_eq_sum_range (fun x => ∑ t ∈ T, if okc t x ∧ step t x = s then N n t else 0)]
  let e : Fin 4 × (Fin n → Fin 4) ≃ (Fin (n + 1) → Fin 4) :=
    { toFun := fun p => Fin.snoc p.2 p.1
      invFun := fun w => (w (Fin.last n), Fin.init w)
      left_inv := fun p => by simp [Fin.init_snoc, Fin.snoc_last]
      right_inv := fun w => Fin.snoc_init_self w }
  unfold N
  rw [card_filter, ← e.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hR : ∀ t, (if okc t (x : ℕ) ∧ step t (x : ℕ) = s then
      #(univ.filter fun v : Fin n → Fin 4 => StdOrder v ∧ st v = t) else 0) =
      ∑ v : Fin n → Fin 4, if (okc t (x : ℕ) ∧ step t (x : ℕ) = s) ∧ (StdOrder v ∧ st v = t)
        then 1 else 0 := by
    intro t
    split_ifs with h
    · rw [card_filter]
      exact Finset.sum_congr rfl fun v _ => by simp [h]
    · simp [h]
  rw [Finset.sum_congr rfl fun t _ => hR t, Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hl : (e (x, v)) = (Fin.snoc v x : Fin (n + 1) → Fin 4) := rfl
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
def good (s : ℕ × ℕ × ℕ × ℕ) : Prop := s.1 ≠ 1 ∧ s.2.1 ≠ 1 ∧ s.2.2.1 ≠ 1 ∧ s.2.2.2 ≠ 1

instance : DecidablePred good := fun s => by unfold good; infer_instance

theorem rep_iff {n : ℕ} (w : Fin n → Fin 4) : Repeated w ↔ good (st w) := by
  have h0 := cnt_pos w 0
  have h1 := cnt_pos w 1
  have h2 := cnt_pos w 2
  have h3 := cnt_pos w 3
  unfold Repeated good st
  simp only
  constructor
  · intro h
    have e0 := h 0
    have e1 := h 1
    have e2 := h 2
    have e3 := h 3
    rw [← h0] at e0
    rw [← h1] at e1
    rw [← h2] at e2
    rw [← h3] at e3
    unfold cnt at h0 h1 h2 h3
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
    · have := h3.mpr hc
      unfold cnt at this h
      simp only [Fin.reduceFinMk, Fin.isValue] at *
      omega

theorem a_eq (n : ℕ) : a n = ∑ t ∈ T, if good t then N n t else 0 := by
  classical
  unfold a
  rw [Fintype.card_subtype]
  have e : (univ.filter fun w : Fin n → Fin 4 => StdOrder w ∧ Repeated w) =
      univ.filter fun w : Fin n → Fin 4 => StdOrder w ∧ good (st w) :=
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

theorem tr_s0000 (n : ℕ) : N (n + 1) (0, 0, 0, 0) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0001 (n : ℕ) : N (n + 1) (0, 0, 0, 1) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0002 (n : ℕ) : N (n + 1) (0, 0, 0, 2) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0010 (n : ℕ) : N (n + 1) (0, 0, 1, 0) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0011 (n : ℕ) : N (n + 1) (0, 0, 1, 1) = N n (0, 0, 1, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0012 (n : ℕ) : N (n + 1) (0, 0, 1, 2) = (N n (0, 0, 1, 1) + N n (0, 0, 1, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0020 (n : ℕ) : N (n + 1) (0, 0, 2, 0) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0021 (n : ℕ) : N (n + 1) (0, 0, 2, 1) = N n (0, 0, 2, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0022 (n : ℕ) : N (n + 1) (0, 0, 2, 2) = (N n (0, 0, 2, 1) + N n (0, 0, 2, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0100 (n : ℕ) : N (n + 1) (0, 1, 0, 0) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0101 (n : ℕ) : N (n + 1) (0, 1, 0, 1) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0102 (n : ℕ) : N (n + 1) (0, 1, 0, 2) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0110 (n : ℕ) : N (n + 1) (0, 1, 1, 0) = N n (0, 1, 0, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0111 (n : ℕ) : N (n + 1) (0, 1, 1, 1) = N n (0, 1, 0, 1) + N n (0, 1, 1, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0112 (n : ℕ) : N (n + 1) (0, 1, 1, 2) = N n (0, 1, 0, 2) + (N n (0, 1, 1, 1) + N n (0, 1, 1, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0120 (n : ℕ) : N (n + 1) (0, 1, 2, 0) = (N n (0, 1, 1, 0) + N n (0, 1, 2, 0)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0121 (n : ℕ) : N (n + 1) (0, 1, 2, 1) = (N n (0, 1, 1, 1) + N n (0, 1, 2, 1)) + N n (0, 1, 2, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0122 (n : ℕ) : N (n + 1) (0, 1, 2, 2) = (N n (0, 1, 1, 2) + N n (0, 1, 2, 2)) + (N n (0, 1, 2, 1) + N n (0, 1, 2, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0200 (n : ℕ) : N (n + 1) (0, 2, 0, 0) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0201 (n : ℕ) : N (n + 1) (0, 2, 0, 1) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0202 (n : ℕ) : N (n + 1) (0, 2, 0, 2) = 0 := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0210 (n : ℕ) : N (n + 1) (0, 2, 1, 0) = N n (0, 2, 0, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0211 (n : ℕ) : N (n + 1) (0, 2, 1, 1) = N n (0, 2, 0, 1) + N n (0, 2, 1, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0212 (n : ℕ) : N (n + 1) (0, 2, 1, 2) = N n (0, 2, 0, 2) + (N n (0, 2, 1, 1) + N n (0, 2, 1, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0220 (n : ℕ) : N (n + 1) (0, 2, 2, 0) = (N n (0, 2, 1, 0) + N n (0, 2, 2, 0)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0221 (n : ℕ) : N (n + 1) (0, 2, 2, 1) = (N n (0, 2, 1, 1) + N n (0, 2, 2, 1)) + N n (0, 2, 2, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s0222 (n : ℕ) : N (n + 1) (0, 2, 2, 2) = (N n (0, 2, 1, 2) + N n (0, 2, 2, 2)) + (N n (0, 2, 2, 1) + N n (0, 2, 2, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1000 (n : ℕ) : N (n + 1) (1, 0, 0, 0) = N n (0, 0, 0, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1001 (n : ℕ) : N (n + 1) (1, 0, 0, 1) = N n (0, 0, 0, 1) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1002 (n : ℕ) : N (n + 1) (1, 0, 0, 2) = N n (0, 0, 0, 2) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1010 (n : ℕ) : N (n + 1) (1, 0, 1, 0) = N n (0, 0, 1, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1011 (n : ℕ) : N (n + 1) (1, 0, 1, 1) = N n (0, 0, 1, 1) + N n (1, 0, 1, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1012 (n : ℕ) : N (n + 1) (1, 0, 1, 2) = N n (0, 0, 1, 2) + (N n (1, 0, 1, 1) + N n (1, 0, 1, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1020 (n : ℕ) : N (n + 1) (1, 0, 2, 0) = N n (0, 0, 2, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1021 (n : ℕ) : N (n + 1) (1, 0, 2, 1) = N n (0, 0, 2, 1) + N n (1, 0, 2, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1022 (n : ℕ) : N (n + 1) (1, 0, 2, 2) = N n (0, 0, 2, 2) + (N n (1, 0, 2, 1) + N n (1, 0, 2, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1100 (n : ℕ) : N (n + 1) (1, 1, 0, 0) = N n (0, 1, 0, 0) + N n (1, 0, 0, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1101 (n : ℕ) : N (n + 1) (1, 1, 0, 1) = N n (0, 1, 0, 1) + N n (1, 0, 0, 1) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1102 (n : ℕ) : N (n + 1) (1, 1, 0, 2) = N n (0, 1, 0, 2) + N n (1, 0, 0, 2) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1110 (n : ℕ) : N (n + 1) (1, 1, 1, 0) = N n (0, 1, 1, 0) + N n (1, 0, 1, 0) + N n (1, 1, 0, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1111 (n : ℕ) : N (n + 1) (1, 1, 1, 1) = N n (0, 1, 1, 1) + N n (1, 0, 1, 1) + N n (1, 1, 0, 1) + N n (1, 1, 1, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1112 (n : ℕ) : N (n + 1) (1, 1, 1, 2) = N n (0, 1, 1, 2) + N n (1, 0, 1, 2) + N n (1, 1, 0, 2) + (N n (1, 1, 1, 1) + N n (1, 1, 1, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1120 (n : ℕ) : N (n + 1) (1, 1, 2, 0) = N n (0, 1, 2, 0) + N n (1, 0, 2, 0) + (N n (1, 1, 1, 0) + N n (1, 1, 2, 0)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1121 (n : ℕ) : N (n + 1) (1, 1, 2, 1) = N n (0, 1, 2, 1) + N n (1, 0, 2, 1) + (N n (1, 1, 1, 1) + N n (1, 1, 2, 1)) + N n (1, 1, 2, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1122 (n : ℕ) : N (n + 1) (1, 1, 2, 2) = N n (0, 1, 2, 2) + N n (1, 0, 2, 2) + (N n (1, 1, 1, 2) + N n (1, 1, 2, 2)) + (N n (1, 1, 2, 1) + N n (1, 1, 2, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1200 (n : ℕ) : N (n + 1) (1, 2, 0, 0) = N n (0, 2, 0, 0) + (N n (1, 1, 0, 0) + N n (1, 2, 0, 0)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1201 (n : ℕ) : N (n + 1) (1, 2, 0, 1) = N n (0, 2, 0, 1) + (N n (1, 1, 0, 1) + N n (1, 2, 0, 1)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1202 (n : ℕ) : N (n + 1) (1, 2, 0, 2) = N n (0, 2, 0, 2) + (N n (1, 1, 0, 2) + N n (1, 2, 0, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1210 (n : ℕ) : N (n + 1) (1, 2, 1, 0) = N n (0, 2, 1, 0) + (N n (1, 1, 1, 0) + N n (1, 2, 1, 0)) + N n (1, 2, 0, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1211 (n : ℕ) : N (n + 1) (1, 2, 1, 1) = N n (0, 2, 1, 1) + (N n (1, 1, 1, 1) + N n (1, 2, 1, 1)) + N n (1, 2, 0, 1) + N n (1, 2, 1, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1212 (n : ℕ) : N (n + 1) (1, 2, 1, 2) = N n (0, 2, 1, 2) + (N n (1, 1, 1, 2) + N n (1, 2, 1, 2)) + N n (1, 2, 0, 2) + (N n (1, 2, 1, 1) + N n (1, 2, 1, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1220 (n : ℕ) : N (n + 1) (1, 2, 2, 0) = N n (0, 2, 2, 0) + (N n (1, 1, 2, 0) + N n (1, 2, 2, 0)) + (N n (1, 2, 1, 0) + N n (1, 2, 2, 0)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1221 (n : ℕ) : N (n + 1) (1, 2, 2, 1) = N n (0, 2, 2, 1) + (N n (1, 1, 2, 1) + N n (1, 2, 2, 1)) + (N n (1, 2, 1, 1) + N n (1, 2, 2, 1)) + N n (1, 2, 2, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s1222 (n : ℕ) : N (n + 1) (1, 2, 2, 2) = N n (0, 2, 2, 2) + (N n (1, 1, 2, 2) + N n (1, 2, 2, 2)) + (N n (1, 2, 1, 2) + N n (1, 2, 2, 2)) + (N n (1, 2, 2, 1) + N n (1, 2, 2, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2000 (n : ℕ) : N (n + 1) (2, 0, 0, 0) = (N n (1, 0, 0, 0) + N n (2, 0, 0, 0)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2001 (n : ℕ) : N (n + 1) (2, 0, 0, 1) = (N n (1, 0, 0, 1) + N n (2, 0, 0, 1)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2002 (n : ℕ) : N (n + 1) (2, 0, 0, 2) = (N n (1, 0, 0, 2) + N n (2, 0, 0, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2010 (n : ℕ) : N (n + 1) (2, 0, 1, 0) = (N n (1, 0, 1, 0) + N n (2, 0, 1, 0)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2011 (n : ℕ) : N (n + 1) (2, 0, 1, 1) = (N n (1, 0, 1, 1) + N n (2, 0, 1, 1)) + N n (2, 0, 1, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2012 (n : ℕ) : N (n + 1) (2, 0, 1, 2) = (N n (1, 0, 1, 2) + N n (2, 0, 1, 2)) + (N n (2, 0, 1, 1) + N n (2, 0, 1, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2020 (n : ℕ) : N (n + 1) (2, 0, 2, 0) = (N n (1, 0, 2, 0) + N n (2, 0, 2, 0)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2021 (n : ℕ) : N (n + 1) (2, 0, 2, 1) = (N n (1, 0, 2, 1) + N n (2, 0, 2, 1)) + N n (2, 0, 2, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2022 (n : ℕ) : N (n + 1) (2, 0, 2, 2) = (N n (1, 0, 2, 2) + N n (2, 0, 2, 2)) + (N n (2, 0, 2, 1) + N n (2, 0, 2, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2100 (n : ℕ) : N (n + 1) (2, 1, 0, 0) = (N n (1, 1, 0, 0) + N n (2, 1, 0, 0)) + N n (2, 0, 0, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2101 (n : ℕ) : N (n + 1) (2, 1, 0, 1) = (N n (1, 1, 0, 1) + N n (2, 1, 0, 1)) + N n (2, 0, 0, 1) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2102 (n : ℕ) : N (n + 1) (2, 1, 0, 2) = (N n (1, 1, 0, 2) + N n (2, 1, 0, 2)) + N n (2, 0, 0, 2) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2110 (n : ℕ) : N (n + 1) (2, 1, 1, 0) = (N n (1, 1, 1, 0) + N n (2, 1, 1, 0)) + N n (2, 0, 1, 0) + N n (2, 1, 0, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2111 (n : ℕ) : N (n + 1) (2, 1, 1, 1) = (N n (1, 1, 1, 1) + N n (2, 1, 1, 1)) + N n (2, 0, 1, 1) + N n (2, 1, 0, 1) + N n (2, 1, 1, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2112 (n : ℕ) : N (n + 1) (2, 1, 1, 2) = (N n (1, 1, 1, 2) + N n (2, 1, 1, 2)) + N n (2, 0, 1, 2) + N n (2, 1, 0, 2) + (N n (2, 1, 1, 1) + N n (2, 1, 1, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2120 (n : ℕ) : N (n + 1) (2, 1, 2, 0) = (N n (1, 1, 2, 0) + N n (2, 1, 2, 0)) + N n (2, 0, 2, 0) + (N n (2, 1, 1, 0) + N n (2, 1, 2, 0)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2121 (n : ℕ) : N (n + 1) (2, 1, 2, 1) = (N n (1, 1, 2, 1) + N n (2, 1, 2, 1)) + N n (2, 0, 2, 1) + (N n (2, 1, 1, 1) + N n (2, 1, 2, 1)) + N n (2, 1, 2, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2122 (n : ℕ) : N (n + 1) (2, 1, 2, 2) = (N n (1, 1, 2, 2) + N n (2, 1, 2, 2)) + N n (2, 0, 2, 2) + (N n (2, 1, 1, 2) + N n (2, 1, 2, 2)) + (N n (2, 1, 2, 1) + N n (2, 1, 2, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2200 (n : ℕ) : N (n + 1) (2, 2, 0, 0) = (N n (1, 2, 0, 0) + N n (2, 2, 0, 0)) + (N n (2, 1, 0, 0) + N n (2, 2, 0, 0)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2201 (n : ℕ) : N (n + 1) (2, 2, 0, 1) = (N n (1, 2, 0, 1) + N n (2, 2, 0, 1)) + (N n (2, 1, 0, 1) + N n (2, 2, 0, 1)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2202 (n : ℕ) : N (n + 1) (2, 2, 0, 2) = (N n (1, 2, 0, 2) + N n (2, 2, 0, 2)) + (N n (2, 1, 0, 2) + N n (2, 2, 0, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2210 (n : ℕ) : N (n + 1) (2, 2, 1, 0) = (N n (1, 2, 1, 0) + N n (2, 2, 1, 0)) + (N n (2, 1, 1, 0) + N n (2, 2, 1, 0)) + N n (2, 2, 0, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2211 (n : ℕ) : N (n + 1) (2, 2, 1, 1) = (N n (1, 2, 1, 1) + N n (2, 2, 1, 1)) + (N n (2, 1, 1, 1) + N n (2, 2, 1, 1)) + N n (2, 2, 0, 1) + N n (2, 2, 1, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2212 (n : ℕ) : N (n + 1) (2, 2, 1, 2) = (N n (1, 2, 1, 2) + N n (2, 2, 1, 2)) + (N n (2, 1, 1, 2) + N n (2, 2, 1, 2)) + N n (2, 2, 0, 2) + (N n (2, 2, 1, 1) + N n (2, 2, 1, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2220 (n : ℕ) : N (n + 1) (2, 2, 2, 0) = (N n (1, 2, 2, 0) + N n (2, 2, 2, 0)) + (N n (2, 1, 2, 0) + N n (2, 2, 2, 0)) + (N n (2, 2, 1, 0) + N n (2, 2, 2, 0)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2221 (n : ℕ) : N (n + 1) (2, 2, 2, 1) = (N n (1, 2, 2, 1) + N n (2, 2, 2, 1)) + (N n (2, 1, 2, 1) + N n (2, 2, 2, 1)) + (N n (2, 2, 1, 1) + N n (2, 2, 2, 1)) + N n (2, 2, 2, 0) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem tr_s2222 (n : ℕ) : N (n + 1) (2, 2, 2, 2) = (N n (1, 2, 2, 2) + N n (2, 2, 2, 2)) + (N n (2, 1, 2, 2) + N n (2, 2, 2, 2)) + (N n (2, 2, 1, 2) + N n (2, 2, 2, 2)) + (N n (2, 2, 2, 1) + N n (2, 2, 2, 2)) := by
  rw [trans]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [okc, step]

theorem b0_s0000 : N 0 (0, 0, 0, 0) = 1 := by decide

theorem b0_s0001 : N 0 (0, 0, 0, 1) = 0 := by decide

theorem b0_s0002 : N 0 (0, 0, 0, 2) = 0 := by decide

theorem b0_s0010 : N 0 (0, 0, 1, 0) = 0 := by decide

theorem b0_s0011 : N 0 (0, 0, 1, 1) = 0 := by decide

theorem b0_s0012 : N 0 (0, 0, 1, 2) = 0 := by decide

theorem b0_s0020 : N 0 (0, 0, 2, 0) = 0 := by decide

theorem b0_s0021 : N 0 (0, 0, 2, 1) = 0 := by decide

theorem b0_s0022 : N 0 (0, 0, 2, 2) = 0 := by decide

theorem b0_s0100 : N 0 (0, 1, 0, 0) = 0 := by decide

theorem b0_s0101 : N 0 (0, 1, 0, 1) = 0 := by decide

theorem b0_s0102 : N 0 (0, 1, 0, 2) = 0 := by decide

theorem b0_s0110 : N 0 (0, 1, 1, 0) = 0 := by decide

theorem b0_s0111 : N 0 (0, 1, 1, 1) = 0 := by decide

theorem b0_s0112 : N 0 (0, 1, 1, 2) = 0 := by decide

theorem b0_s0120 : N 0 (0, 1, 2, 0) = 0 := by decide

theorem b0_s0121 : N 0 (0, 1, 2, 1) = 0 := by decide

theorem b0_s0122 : N 0 (0, 1, 2, 2) = 0 := by decide

theorem b0_s0200 : N 0 (0, 2, 0, 0) = 0 := by decide

theorem b0_s0201 : N 0 (0, 2, 0, 1) = 0 := by decide

theorem b0_s0202 : N 0 (0, 2, 0, 2) = 0 := by decide

theorem b0_s0210 : N 0 (0, 2, 1, 0) = 0 := by decide

theorem b0_s0211 : N 0 (0, 2, 1, 1) = 0 := by decide

theorem b0_s0212 : N 0 (0, 2, 1, 2) = 0 := by decide

theorem b0_s0220 : N 0 (0, 2, 2, 0) = 0 := by decide

theorem b0_s0221 : N 0 (0, 2, 2, 1) = 0 := by decide

theorem b0_s0222 : N 0 (0, 2, 2, 2) = 0 := by decide

theorem b0_s1000 : N 0 (1, 0, 0, 0) = 0 := by decide

theorem b0_s1001 : N 0 (1, 0, 0, 1) = 0 := by decide

theorem b0_s1002 : N 0 (1, 0, 0, 2) = 0 := by decide

theorem b0_s1010 : N 0 (1, 0, 1, 0) = 0 := by decide

theorem b0_s1011 : N 0 (1, 0, 1, 1) = 0 := by decide

theorem b0_s1012 : N 0 (1, 0, 1, 2) = 0 := by decide

theorem b0_s1020 : N 0 (1, 0, 2, 0) = 0 := by decide

theorem b0_s1021 : N 0 (1, 0, 2, 1) = 0 := by decide

theorem b0_s1022 : N 0 (1, 0, 2, 2) = 0 := by decide

theorem b0_s1100 : N 0 (1, 1, 0, 0) = 0 := by decide

theorem b0_s1101 : N 0 (1, 1, 0, 1) = 0 := by decide

theorem b0_s1102 : N 0 (1, 1, 0, 2) = 0 := by decide

theorem b0_s1110 : N 0 (1, 1, 1, 0) = 0 := by decide

theorem b0_s1111 : N 0 (1, 1, 1, 1) = 0 := by decide

theorem b0_s1112 : N 0 (1, 1, 1, 2) = 0 := by decide

theorem b0_s1120 : N 0 (1, 1, 2, 0) = 0 := by decide

theorem b0_s1121 : N 0 (1, 1, 2, 1) = 0 := by decide

theorem b0_s1122 : N 0 (1, 1, 2, 2) = 0 := by decide

theorem b0_s1200 : N 0 (1, 2, 0, 0) = 0 := by decide

theorem b0_s1201 : N 0 (1, 2, 0, 1) = 0 := by decide

theorem b0_s1202 : N 0 (1, 2, 0, 2) = 0 := by decide

theorem b0_s1210 : N 0 (1, 2, 1, 0) = 0 := by decide

theorem b0_s1211 : N 0 (1, 2, 1, 1) = 0 := by decide

theorem b0_s1212 : N 0 (1, 2, 1, 2) = 0 := by decide

theorem b0_s1220 : N 0 (1, 2, 2, 0) = 0 := by decide

theorem b0_s1221 : N 0 (1, 2, 2, 1) = 0 := by decide

theorem b0_s1222 : N 0 (1, 2, 2, 2) = 0 := by decide

theorem b0_s2000 : N 0 (2, 0, 0, 0) = 0 := by decide

theorem b0_s2001 : N 0 (2, 0, 0, 1) = 0 := by decide

theorem b0_s2002 : N 0 (2, 0, 0, 2) = 0 := by decide

theorem b0_s2010 : N 0 (2, 0, 1, 0) = 0 := by decide

theorem b0_s2011 : N 0 (2, 0, 1, 1) = 0 := by decide

theorem b0_s2012 : N 0 (2, 0, 1, 2) = 0 := by decide

theorem b0_s2020 : N 0 (2, 0, 2, 0) = 0 := by decide

theorem b0_s2021 : N 0 (2, 0, 2, 1) = 0 := by decide

theorem b0_s2022 : N 0 (2, 0, 2, 2) = 0 := by decide

theorem b0_s2100 : N 0 (2, 1, 0, 0) = 0 := by decide

theorem b0_s2101 : N 0 (2, 1, 0, 1) = 0 := by decide

theorem b0_s2102 : N 0 (2, 1, 0, 2) = 0 := by decide

theorem b0_s2110 : N 0 (2, 1, 1, 0) = 0 := by decide

theorem b0_s2111 : N 0 (2, 1, 1, 1) = 0 := by decide

theorem b0_s2112 : N 0 (2, 1, 1, 2) = 0 := by decide

theorem b0_s2120 : N 0 (2, 1, 2, 0) = 0 := by decide

theorem b0_s2121 : N 0 (2, 1, 2, 1) = 0 := by decide

theorem b0_s2122 : N 0 (2, 1, 2, 2) = 0 := by decide

theorem b0_s2200 : N 0 (2, 2, 0, 0) = 0 := by decide

theorem b0_s2201 : N 0 (2, 2, 0, 1) = 0 := by decide

theorem b0_s2202 : N 0 (2, 2, 0, 2) = 0 := by decide

theorem b0_s2210 : N 0 (2, 2, 1, 0) = 0 := by decide

theorem b0_s2211 : N 0 (2, 2, 1, 1) = 0 := by decide

theorem b0_s2212 : N 0 (2, 2, 1, 2) = 0 := by decide

theorem b0_s2220 : N 0 (2, 2, 2, 0) = 0 := by decide

theorem b0_s2221 : N 0 (2, 2, 2, 1) = 0 := by decide

theorem b0_s2222 : N 0 (2, 2, 2, 2) = 0 := by decide

theorem b1_s0000 : N 1 (0, 0, 0, 0) = 0 := tr_s0000 0

theorem b1_s0001 : N 1 (0, 0, 0, 1) = 0 := tr_s0001 0

theorem b1_s0002 : N 1 (0, 0, 0, 2) = 0 := tr_s0002 0

theorem b1_s0010 : N 1 (0, 0, 1, 0) = 0 := tr_s0010 0

theorem b1_s0011 : N 1 (0, 0, 1, 1) = 0 := by
  show N (0 + 1) (0, 0, 1, 1) = 0
  rw [tr_s0011]
  norm_num [b0_s0010]

theorem b1_s0012 : N 1 (0, 0, 1, 2) = 0 := by
  show N (0 + 1) (0, 0, 1, 2) = 0
  rw [tr_s0012]
  norm_num [b0_s0011, b0_s0012]

theorem b1_s0020 : N 1 (0, 0, 2, 0) = 0 := tr_s0020 0

theorem b1_s0021 : N 1 (0, 0, 2, 1) = 0 := by
  show N (0 + 1) (0, 0, 2, 1) = 0
  rw [tr_s0021]
  norm_num [b0_s0020]

theorem b1_s0022 : N 1 (0, 0, 2, 2) = 0 := by
  show N (0 + 1) (0, 0, 2, 2) = 0
  rw [tr_s0022]
  norm_num [b0_s0021, b0_s0022]

theorem b1_s0100 : N 1 (0, 1, 0, 0) = 0 := tr_s0100 0

theorem b1_s0101 : N 1 (0, 1, 0, 1) = 0 := tr_s0101 0

theorem b1_s0102 : N 1 (0, 1, 0, 2) = 0 := tr_s0102 0

theorem b1_s0110 : N 1 (0, 1, 1, 0) = 0 := by
  show N (0 + 1) (0, 1, 1, 0) = 0
  rw [tr_s0110]
  norm_num [b0_s0100]

theorem b1_s0111 : N 1 (0, 1, 1, 1) = 0 := by
  show N (0 + 1) (0, 1, 1, 1) = 0
  rw [tr_s0111]
  norm_num [b0_s0101, b0_s0110]

theorem b1_s0112 : N 1 (0, 1, 1, 2) = 0 := by
  show N (0 + 1) (0, 1, 1, 2) = 0
  rw [tr_s0112]
  norm_num [b0_s0102, b0_s0111, b0_s0112]

theorem b1_s0120 : N 1 (0, 1, 2, 0) = 0 := by
  show N (0 + 1) (0, 1, 2, 0) = 0
  rw [tr_s0120]
  norm_num [b0_s0110, b0_s0120]

theorem b1_s0121 : N 1 (0, 1, 2, 1) = 0 := by
  show N (0 + 1) (0, 1, 2, 1) = 0
  rw [tr_s0121]
  norm_num [b0_s0111, b0_s0120, b0_s0121]

theorem b1_s0122 : N 1 (0, 1, 2, 2) = 0 := by
  show N (0 + 1) (0, 1, 2, 2) = 0
  rw [tr_s0122]
  norm_num [b0_s0112, b0_s0121, b0_s0122]

theorem b1_s0200 : N 1 (0, 2, 0, 0) = 0 := tr_s0200 0

theorem b1_s0201 : N 1 (0, 2, 0, 1) = 0 := tr_s0201 0

theorem b1_s0202 : N 1 (0, 2, 0, 2) = 0 := tr_s0202 0

theorem b1_s0210 : N 1 (0, 2, 1, 0) = 0 := by
  show N (0 + 1) (0, 2, 1, 0) = 0
  rw [tr_s0210]
  norm_num [b0_s0200]

theorem b1_s0211 : N 1 (0, 2, 1, 1) = 0 := by
  show N (0 + 1) (0, 2, 1, 1) = 0
  rw [tr_s0211]
  norm_num [b0_s0201, b0_s0210]

theorem b1_s0212 : N 1 (0, 2, 1, 2) = 0 := by
  show N (0 + 1) (0, 2, 1, 2) = 0
  rw [tr_s0212]
  norm_num [b0_s0202, b0_s0211, b0_s0212]

theorem b1_s0220 : N 1 (0, 2, 2, 0) = 0 := by
  show N (0 + 1) (0, 2, 2, 0) = 0
  rw [tr_s0220]
  norm_num [b0_s0210, b0_s0220]

theorem b1_s0221 : N 1 (0, 2, 2, 1) = 0 := by
  show N (0 + 1) (0, 2, 2, 1) = 0
  rw [tr_s0221]
  norm_num [b0_s0211, b0_s0220, b0_s0221]

theorem b1_s0222 : N 1 (0, 2, 2, 2) = 0 := by
  show N (0 + 1) (0, 2, 2, 2) = 0
  rw [tr_s0222]
  norm_num [b0_s0212, b0_s0221, b0_s0222]

theorem b1_s1000 : N 1 (1, 0, 0, 0) = 1 := by
  show N (0 + 1) (1, 0, 0, 0) = 1
  rw [tr_s1000]
  norm_num [b0_s0000]

theorem b1_s1001 : N 1 (1, 0, 0, 1) = 0 := by
  show N (0 + 1) (1, 0, 0, 1) = 0
  rw [tr_s1001]
  norm_num [b0_s0001]

theorem b1_s1002 : N 1 (1, 0, 0, 2) = 0 := by
  show N (0 + 1) (1, 0, 0, 2) = 0
  rw [tr_s1002]
  norm_num [b0_s0002]

theorem b1_s1010 : N 1 (1, 0, 1, 0) = 0 := by
  show N (0 + 1) (1, 0, 1, 0) = 0
  rw [tr_s1010]
  norm_num [b0_s0010]

theorem b1_s1011 : N 1 (1, 0, 1, 1) = 0 := by
  show N (0 + 1) (1, 0, 1, 1) = 0
  rw [tr_s1011]
  norm_num [b0_s0011, b0_s1010]

theorem b1_s1012 : N 1 (1, 0, 1, 2) = 0 := by
  show N (0 + 1) (1, 0, 1, 2) = 0
  rw [tr_s1012]
  norm_num [b0_s0012, b0_s1011, b0_s1012]

theorem b1_s1020 : N 1 (1, 0, 2, 0) = 0 := by
  show N (0 + 1) (1, 0, 2, 0) = 0
  rw [tr_s1020]
  norm_num [b0_s0020]

theorem b1_s1021 : N 1 (1, 0, 2, 1) = 0 := by
  show N (0 + 1) (1, 0, 2, 1) = 0
  rw [tr_s1021]
  norm_num [b0_s0021, b0_s1020]

theorem b1_s1022 : N 1 (1, 0, 2, 2) = 0 := by
  show N (0 + 1) (1, 0, 2, 2) = 0
  rw [tr_s1022]
  norm_num [b0_s0022, b0_s1021, b0_s1022]

theorem b1_s1100 : N 1 (1, 1, 0, 0) = 0 := by
  show N (0 + 1) (1, 1, 0, 0) = 0
  rw [tr_s1100]
  norm_num [b0_s0100, b0_s1000]

theorem b1_s1101 : N 1 (1, 1, 0, 1) = 0 := by
  show N (0 + 1) (1, 1, 0, 1) = 0
  rw [tr_s1101]
  norm_num [b0_s0101, b0_s1001]

theorem b1_s1102 : N 1 (1, 1, 0, 2) = 0 := by
  show N (0 + 1) (1, 1, 0, 2) = 0
  rw [tr_s1102]
  norm_num [b0_s0102, b0_s1002]

theorem b1_s1110 : N 1 (1, 1, 1, 0) = 0 := by
  show N (0 + 1) (1, 1, 1, 0) = 0
  rw [tr_s1110]
  norm_num [b0_s0110, b0_s1010, b0_s1100]

theorem b1_s1111 : N 1 (1, 1, 1, 1) = 0 := by
  show N (0 + 1) (1, 1, 1, 1) = 0
  rw [tr_s1111]
  norm_num [b0_s0111, b0_s1011, b0_s1101, b0_s1110]

theorem b1_s1112 : N 1 (1, 1, 1, 2) = 0 := by
  show N (0 + 1) (1, 1, 1, 2) = 0
  rw [tr_s1112]
  norm_num [b0_s0112, b0_s1012, b0_s1102, b0_s1111, b0_s1112]

theorem b1_s1120 : N 1 (1, 1, 2, 0) = 0 := by
  show N (0 + 1) (1, 1, 2, 0) = 0
  rw [tr_s1120]
  norm_num [b0_s0120, b0_s1020, b0_s1110, b0_s1120]

theorem b1_s1121 : N 1 (1, 1, 2, 1) = 0 := by
  show N (0 + 1) (1, 1, 2, 1) = 0
  rw [tr_s1121]
  norm_num [b0_s0121, b0_s1021, b0_s1111, b0_s1120, b0_s1121]

theorem b1_s1122 : N 1 (1, 1, 2, 2) = 0 := by
  show N (0 + 1) (1, 1, 2, 2) = 0
  rw [tr_s1122]
  norm_num [b0_s0122, b0_s1022, b0_s1112, b0_s1121, b0_s1122]

theorem b1_s1200 : N 1 (1, 2, 0, 0) = 0 := by
  show N (0 + 1) (1, 2, 0, 0) = 0
  rw [tr_s1200]
  norm_num [b0_s0200, b0_s1100, b0_s1200]

theorem b1_s1201 : N 1 (1, 2, 0, 1) = 0 := by
  show N (0 + 1) (1, 2, 0, 1) = 0
  rw [tr_s1201]
  norm_num [b0_s0201, b0_s1101, b0_s1201]

theorem b1_s1202 : N 1 (1, 2, 0, 2) = 0 := by
  show N (0 + 1) (1, 2, 0, 2) = 0
  rw [tr_s1202]
  norm_num [b0_s0202, b0_s1102, b0_s1202]

theorem b1_s1210 : N 1 (1, 2, 1, 0) = 0 := by
  show N (0 + 1) (1, 2, 1, 0) = 0
  rw [tr_s1210]
  norm_num [b0_s0210, b0_s1110, b0_s1200, b0_s1210]

theorem b1_s1211 : N 1 (1, 2, 1, 1) = 0 := by
  show N (0 + 1) (1, 2, 1, 1) = 0
  rw [tr_s1211]
  norm_num [b0_s0211, b0_s1111, b0_s1201, b0_s1210, b0_s1211]

theorem b1_s1212 : N 1 (1, 2, 1, 2) = 0 := by
  show N (0 + 1) (1, 2, 1, 2) = 0
  rw [tr_s1212]
  norm_num [b0_s0212, b0_s1112, b0_s1202, b0_s1211, b0_s1212]

theorem b1_s1220 : N 1 (1, 2, 2, 0) = 0 := by
  show N (0 + 1) (1, 2, 2, 0) = 0
  rw [tr_s1220]
  norm_num [b0_s0220, b0_s1120, b0_s1210, b0_s1220]

theorem b1_s1221 : N 1 (1, 2, 2, 1) = 0 := by
  show N (0 + 1) (1, 2, 2, 1) = 0
  rw [tr_s1221]
  norm_num [b0_s0221, b0_s1121, b0_s1211, b0_s1220, b0_s1221]

theorem b1_s1222 : N 1 (1, 2, 2, 2) = 0 := by
  show N (0 + 1) (1, 2, 2, 2) = 0
  rw [tr_s1222]
  norm_num [b0_s0222, b0_s1122, b0_s1212, b0_s1221, b0_s1222]

theorem b1_s2000 : N 1 (2, 0, 0, 0) = 0 := by
  show N (0 + 1) (2, 0, 0, 0) = 0
  rw [tr_s2000]
  norm_num [b0_s1000, b0_s2000]

theorem b1_s2001 : N 1 (2, 0, 0, 1) = 0 := by
  show N (0 + 1) (2, 0, 0, 1) = 0
  rw [tr_s2001]
  norm_num [b0_s1001, b0_s2001]

theorem b1_s2002 : N 1 (2, 0, 0, 2) = 0 := by
  show N (0 + 1) (2, 0, 0, 2) = 0
  rw [tr_s2002]
  norm_num [b0_s1002, b0_s2002]

theorem b1_s2010 : N 1 (2, 0, 1, 0) = 0 := by
  show N (0 + 1) (2, 0, 1, 0) = 0
  rw [tr_s2010]
  norm_num [b0_s1010, b0_s2010]

theorem b1_s2011 : N 1 (2, 0, 1, 1) = 0 := by
  show N (0 + 1) (2, 0, 1, 1) = 0
  rw [tr_s2011]
  norm_num [b0_s1011, b0_s2010, b0_s2011]

theorem b1_s2012 : N 1 (2, 0, 1, 2) = 0 := by
  show N (0 + 1) (2, 0, 1, 2) = 0
  rw [tr_s2012]
  norm_num [b0_s1012, b0_s2011, b0_s2012]

theorem b1_s2020 : N 1 (2, 0, 2, 0) = 0 := by
  show N (0 + 1) (2, 0, 2, 0) = 0
  rw [tr_s2020]
  norm_num [b0_s1020, b0_s2020]

theorem b1_s2021 : N 1 (2, 0, 2, 1) = 0 := by
  show N (0 + 1) (2, 0, 2, 1) = 0
  rw [tr_s2021]
  norm_num [b0_s1021, b0_s2020, b0_s2021]

theorem b1_s2022 : N 1 (2, 0, 2, 2) = 0 := by
  show N (0 + 1) (2, 0, 2, 2) = 0
  rw [tr_s2022]
  norm_num [b0_s1022, b0_s2021, b0_s2022]

theorem b1_s2100 : N 1 (2, 1, 0, 0) = 0 := by
  show N (0 + 1) (2, 1, 0, 0) = 0
  rw [tr_s2100]
  norm_num [b0_s1100, b0_s2000, b0_s2100]

theorem b1_s2101 : N 1 (2, 1, 0, 1) = 0 := by
  show N (0 + 1) (2, 1, 0, 1) = 0
  rw [tr_s2101]
  norm_num [b0_s1101, b0_s2001, b0_s2101]

theorem b1_s2102 : N 1 (2, 1, 0, 2) = 0 := by
  show N (0 + 1) (2, 1, 0, 2) = 0
  rw [tr_s2102]
  norm_num [b0_s1102, b0_s2002, b0_s2102]

theorem b1_s2110 : N 1 (2, 1, 1, 0) = 0 := by
  show N (0 + 1) (2, 1, 1, 0) = 0
  rw [tr_s2110]
  norm_num [b0_s1110, b0_s2010, b0_s2100, b0_s2110]

theorem b1_s2111 : N 1 (2, 1, 1, 1) = 0 := by
  show N (0 + 1) (2, 1, 1, 1) = 0
  rw [tr_s2111]
  norm_num [b0_s1111, b0_s2011, b0_s2101, b0_s2110, b0_s2111]

theorem b1_s2112 : N 1 (2, 1, 1, 2) = 0 := by
  show N (0 + 1) (2, 1, 1, 2) = 0
  rw [tr_s2112]
  norm_num [b0_s1112, b0_s2012, b0_s2102, b0_s2111, b0_s2112]

theorem b1_s2120 : N 1 (2, 1, 2, 0) = 0 := by
  show N (0 + 1) (2, 1, 2, 0) = 0
  rw [tr_s2120]
  norm_num [b0_s1120, b0_s2020, b0_s2110, b0_s2120]

theorem b1_s2121 : N 1 (2, 1, 2, 1) = 0 := by
  show N (0 + 1) (2, 1, 2, 1) = 0
  rw [tr_s2121]
  norm_num [b0_s1121, b0_s2021, b0_s2111, b0_s2120, b0_s2121]

theorem b1_s2122 : N 1 (2, 1, 2, 2) = 0 := by
  show N (0 + 1) (2, 1, 2, 2) = 0
  rw [tr_s2122]
  norm_num [b0_s1122, b0_s2022, b0_s2112, b0_s2121, b0_s2122]

theorem b1_s2200 : N 1 (2, 2, 0, 0) = 0 := by
  show N (0 + 1) (2, 2, 0, 0) = 0
  rw [tr_s2200]
  norm_num [b0_s1200, b0_s2100, b0_s2200]

theorem b1_s2201 : N 1 (2, 2, 0, 1) = 0 := by
  show N (0 + 1) (2, 2, 0, 1) = 0
  rw [tr_s2201]
  norm_num [b0_s1201, b0_s2101, b0_s2201]

theorem b1_s2202 : N 1 (2, 2, 0, 2) = 0 := by
  show N (0 + 1) (2, 2, 0, 2) = 0
  rw [tr_s2202]
  norm_num [b0_s1202, b0_s2102, b0_s2202]

theorem b1_s2210 : N 1 (2, 2, 1, 0) = 0 := by
  show N (0 + 1) (2, 2, 1, 0) = 0
  rw [tr_s2210]
  norm_num [b0_s1210, b0_s2110, b0_s2200, b0_s2210]

theorem b1_s2211 : N 1 (2, 2, 1, 1) = 0 := by
  show N (0 + 1) (2, 2, 1, 1) = 0
  rw [tr_s2211]
  norm_num [b0_s1211, b0_s2111, b0_s2201, b0_s2210, b0_s2211]

theorem b1_s2212 : N 1 (2, 2, 1, 2) = 0 := by
  show N (0 + 1) (2, 2, 1, 2) = 0
  rw [tr_s2212]
  norm_num [b0_s1212, b0_s2112, b0_s2202, b0_s2211, b0_s2212]

theorem b1_s2220 : N 1 (2, 2, 2, 0) = 0 := by
  show N (0 + 1) (2, 2, 2, 0) = 0
  rw [tr_s2220]
  norm_num [b0_s1220, b0_s2120, b0_s2210, b0_s2220]

theorem b1_s2221 : N 1 (2, 2, 2, 1) = 0 := by
  show N (0 + 1) (2, 2, 2, 1) = 0
  rw [tr_s2221]
  norm_num [b0_s1221, b0_s2121, b0_s2211, b0_s2220, b0_s2221]

theorem b1_s2222 : N 1 (2, 2, 2, 2) = 0 := by
  show N (0 + 1) (2, 2, 2, 2) = 0
  rw [tr_s2222]
  norm_num [b0_s1222, b0_s2122, b0_s2212, b0_s2221, b0_s2222]

theorem b2_s0000 : N 2 (0, 0, 0, 0) = 0 := tr_s0000 1

theorem b2_s0001 : N 2 (0, 0, 0, 1) = 0 := tr_s0001 1

theorem b2_s0002 : N 2 (0, 0, 0, 2) = 0 := tr_s0002 1

theorem b2_s0010 : N 2 (0, 0, 1, 0) = 0 := tr_s0010 1

theorem b2_s0011 : N 2 (0, 0, 1, 1) = 0 := by
  show N (1 + 1) (0, 0, 1, 1) = 0
  rw [tr_s0011]
  norm_num [b1_s0010]

theorem b2_s0012 : N 2 (0, 0, 1, 2) = 0 := by
  show N (1 + 1) (0, 0, 1, 2) = 0
  rw [tr_s0012]
  norm_num [b1_s0011, b1_s0012]

theorem b2_s0020 : N 2 (0, 0, 2, 0) = 0 := tr_s0020 1

theorem b2_s0021 : N 2 (0, 0, 2, 1) = 0 := by
  show N (1 + 1) (0, 0, 2, 1) = 0
  rw [tr_s0021]
  norm_num [b1_s0020]

theorem b2_s0022 : N 2 (0, 0, 2, 2) = 0 := by
  show N (1 + 1) (0, 0, 2, 2) = 0
  rw [tr_s0022]
  norm_num [b1_s0021, b1_s0022]

theorem b2_s0100 : N 2 (0, 1, 0, 0) = 0 := tr_s0100 1

theorem b2_s0101 : N 2 (0, 1, 0, 1) = 0 := tr_s0101 1

theorem b2_s0102 : N 2 (0, 1, 0, 2) = 0 := tr_s0102 1

theorem b2_s0110 : N 2 (0, 1, 1, 0) = 0 := by
  show N (1 + 1) (0, 1, 1, 0) = 0
  rw [tr_s0110]
  norm_num [b1_s0100]

theorem b2_s0111 : N 2 (0, 1, 1, 1) = 0 := by
  show N (1 + 1) (0, 1, 1, 1) = 0
  rw [tr_s0111]
  norm_num [b1_s0101, b1_s0110]

theorem b2_s0112 : N 2 (0, 1, 1, 2) = 0 := by
  show N (1 + 1) (0, 1, 1, 2) = 0
  rw [tr_s0112]
  norm_num [b1_s0102, b1_s0111, b1_s0112]

theorem b2_s0120 : N 2 (0, 1, 2, 0) = 0 := by
  show N (1 + 1) (0, 1, 2, 0) = 0
  rw [tr_s0120]
  norm_num [b1_s0110, b1_s0120]

theorem b2_s0121 : N 2 (0, 1, 2, 1) = 0 := by
  show N (1 + 1) (0, 1, 2, 1) = 0
  rw [tr_s0121]
  norm_num [b1_s0111, b1_s0120, b1_s0121]

theorem b2_s0122 : N 2 (0, 1, 2, 2) = 0 := by
  show N (1 + 1) (0, 1, 2, 2) = 0
  rw [tr_s0122]
  norm_num [b1_s0112, b1_s0121, b1_s0122]

theorem b2_s0200 : N 2 (0, 2, 0, 0) = 0 := tr_s0200 1

theorem b2_s0201 : N 2 (0, 2, 0, 1) = 0 := tr_s0201 1

theorem b2_s0202 : N 2 (0, 2, 0, 2) = 0 := tr_s0202 1

theorem b2_s0210 : N 2 (0, 2, 1, 0) = 0 := by
  show N (1 + 1) (0, 2, 1, 0) = 0
  rw [tr_s0210]
  norm_num [b1_s0200]

theorem b2_s0211 : N 2 (0, 2, 1, 1) = 0 := by
  show N (1 + 1) (0, 2, 1, 1) = 0
  rw [tr_s0211]
  norm_num [b1_s0201, b1_s0210]

theorem b2_s0212 : N 2 (0, 2, 1, 2) = 0 := by
  show N (1 + 1) (0, 2, 1, 2) = 0
  rw [tr_s0212]
  norm_num [b1_s0202, b1_s0211, b1_s0212]

theorem b2_s0220 : N 2 (0, 2, 2, 0) = 0 := by
  show N (1 + 1) (0, 2, 2, 0) = 0
  rw [tr_s0220]
  norm_num [b1_s0210, b1_s0220]

theorem b2_s0221 : N 2 (0, 2, 2, 1) = 0 := by
  show N (1 + 1) (0, 2, 2, 1) = 0
  rw [tr_s0221]
  norm_num [b1_s0211, b1_s0220, b1_s0221]

theorem b2_s0222 : N 2 (0, 2, 2, 2) = 0 := by
  show N (1 + 1) (0, 2, 2, 2) = 0
  rw [tr_s0222]
  norm_num [b1_s0212, b1_s0221, b1_s0222]

theorem b2_s1000 : N 2 (1, 0, 0, 0) = 0 := by
  show N (1 + 1) (1, 0, 0, 0) = 0
  rw [tr_s1000]
  norm_num [b1_s0000]

theorem b2_s1001 : N 2 (1, 0, 0, 1) = 0 := by
  show N (1 + 1) (1, 0, 0, 1) = 0
  rw [tr_s1001]
  norm_num [b1_s0001]

theorem b2_s1002 : N 2 (1, 0, 0, 2) = 0 := by
  show N (1 + 1) (1, 0, 0, 2) = 0
  rw [tr_s1002]
  norm_num [b1_s0002]

theorem b2_s1010 : N 2 (1, 0, 1, 0) = 0 := by
  show N (1 + 1) (1, 0, 1, 0) = 0
  rw [tr_s1010]
  norm_num [b1_s0010]

theorem b2_s1011 : N 2 (1, 0, 1, 1) = 0 := by
  show N (1 + 1) (1, 0, 1, 1) = 0
  rw [tr_s1011]
  norm_num [b1_s0011, b1_s1010]

theorem b2_s1012 : N 2 (1, 0, 1, 2) = 0 := by
  show N (1 + 1) (1, 0, 1, 2) = 0
  rw [tr_s1012]
  norm_num [b1_s0012, b1_s1011, b1_s1012]

theorem b2_s1020 : N 2 (1, 0, 2, 0) = 0 := by
  show N (1 + 1) (1, 0, 2, 0) = 0
  rw [tr_s1020]
  norm_num [b1_s0020]

theorem b2_s1021 : N 2 (1, 0, 2, 1) = 0 := by
  show N (1 + 1) (1, 0, 2, 1) = 0
  rw [tr_s1021]
  norm_num [b1_s0021, b1_s1020]

theorem b2_s1022 : N 2 (1, 0, 2, 2) = 0 := by
  show N (1 + 1) (1, 0, 2, 2) = 0
  rw [tr_s1022]
  norm_num [b1_s0022, b1_s1021, b1_s1022]

theorem b2_s1100 : N 2 (1, 1, 0, 0) = 1 := by
  show N (1 + 1) (1, 1, 0, 0) = 1
  rw [tr_s1100]
  norm_num [b1_s0100, b1_s1000]

theorem b2_s1101 : N 2 (1, 1, 0, 1) = 0 := by
  show N (1 + 1) (1, 1, 0, 1) = 0
  rw [tr_s1101]
  norm_num [b1_s0101, b1_s1001]

theorem b2_s1102 : N 2 (1, 1, 0, 2) = 0 := by
  show N (1 + 1) (1, 1, 0, 2) = 0
  rw [tr_s1102]
  norm_num [b1_s0102, b1_s1002]

theorem b2_s1110 : N 2 (1, 1, 1, 0) = 0 := by
  show N (1 + 1) (1, 1, 1, 0) = 0
  rw [tr_s1110]
  norm_num [b1_s0110, b1_s1010, b1_s1100]

theorem b2_s1111 : N 2 (1, 1, 1, 1) = 0 := by
  show N (1 + 1) (1, 1, 1, 1) = 0
  rw [tr_s1111]
  norm_num [b1_s0111, b1_s1011, b1_s1101, b1_s1110]

theorem b2_s1112 : N 2 (1, 1, 1, 2) = 0 := by
  show N (1 + 1) (1, 1, 1, 2) = 0
  rw [tr_s1112]
  norm_num [b1_s0112, b1_s1012, b1_s1102, b1_s1111, b1_s1112]

theorem b2_s1120 : N 2 (1, 1, 2, 0) = 0 := by
  show N (1 + 1) (1, 1, 2, 0) = 0
  rw [tr_s1120]
  norm_num [b1_s0120, b1_s1020, b1_s1110, b1_s1120]

theorem b2_s1121 : N 2 (1, 1, 2, 1) = 0 := by
  show N (1 + 1) (1, 1, 2, 1) = 0
  rw [tr_s1121]
  norm_num [b1_s0121, b1_s1021, b1_s1111, b1_s1120, b1_s1121]

theorem b2_s1122 : N 2 (1, 1, 2, 2) = 0 := by
  show N (1 + 1) (1, 1, 2, 2) = 0
  rw [tr_s1122]
  norm_num [b1_s0122, b1_s1022, b1_s1112, b1_s1121, b1_s1122]

theorem b2_s1200 : N 2 (1, 2, 0, 0) = 0 := by
  show N (1 + 1) (1, 2, 0, 0) = 0
  rw [tr_s1200]
  norm_num [b1_s0200, b1_s1100, b1_s1200]

theorem b2_s1201 : N 2 (1, 2, 0, 1) = 0 := by
  show N (1 + 1) (1, 2, 0, 1) = 0
  rw [tr_s1201]
  norm_num [b1_s0201, b1_s1101, b1_s1201]

theorem b2_s1202 : N 2 (1, 2, 0, 2) = 0 := by
  show N (1 + 1) (1, 2, 0, 2) = 0
  rw [tr_s1202]
  norm_num [b1_s0202, b1_s1102, b1_s1202]

theorem b2_s1210 : N 2 (1, 2, 1, 0) = 0 := by
  show N (1 + 1) (1, 2, 1, 0) = 0
  rw [tr_s1210]
  norm_num [b1_s0210, b1_s1110, b1_s1200, b1_s1210]

theorem b2_s1211 : N 2 (1, 2, 1, 1) = 0 := by
  show N (1 + 1) (1, 2, 1, 1) = 0
  rw [tr_s1211]
  norm_num [b1_s0211, b1_s1111, b1_s1201, b1_s1210, b1_s1211]

theorem b2_s1212 : N 2 (1, 2, 1, 2) = 0 := by
  show N (1 + 1) (1, 2, 1, 2) = 0
  rw [tr_s1212]
  norm_num [b1_s0212, b1_s1112, b1_s1202, b1_s1211, b1_s1212]

theorem b2_s1220 : N 2 (1, 2, 2, 0) = 0 := by
  show N (1 + 1) (1, 2, 2, 0) = 0
  rw [tr_s1220]
  norm_num [b1_s0220, b1_s1120, b1_s1210, b1_s1220]

theorem b2_s1221 : N 2 (1, 2, 2, 1) = 0 := by
  show N (1 + 1) (1, 2, 2, 1) = 0
  rw [tr_s1221]
  norm_num [b1_s0221, b1_s1121, b1_s1211, b1_s1220, b1_s1221]

theorem b2_s1222 : N 2 (1, 2, 2, 2) = 0 := by
  show N (1 + 1) (1, 2, 2, 2) = 0
  rw [tr_s1222]
  norm_num [b1_s0222, b1_s1122, b1_s1212, b1_s1221, b1_s1222]

theorem b2_s2000 : N 2 (2, 0, 0, 0) = 1 := by
  show N (1 + 1) (2, 0, 0, 0) = 1
  rw [tr_s2000]
  norm_num [b1_s1000, b1_s2000]

theorem b2_s2001 : N 2 (2, 0, 0, 1) = 0 := by
  show N (1 + 1) (2, 0, 0, 1) = 0
  rw [tr_s2001]
  norm_num [b1_s1001, b1_s2001]

theorem b2_s2002 : N 2 (2, 0, 0, 2) = 0 := by
  show N (1 + 1) (2, 0, 0, 2) = 0
  rw [tr_s2002]
  norm_num [b1_s1002, b1_s2002]

theorem b2_s2010 : N 2 (2, 0, 1, 0) = 0 := by
  show N (1 + 1) (2, 0, 1, 0) = 0
  rw [tr_s2010]
  norm_num [b1_s1010, b1_s2010]

theorem b2_s2011 : N 2 (2, 0, 1, 1) = 0 := by
  show N (1 + 1) (2, 0, 1, 1) = 0
  rw [tr_s2011]
  norm_num [b1_s1011, b1_s2010, b1_s2011]

theorem b2_s2012 : N 2 (2, 0, 1, 2) = 0 := by
  show N (1 + 1) (2, 0, 1, 2) = 0
  rw [tr_s2012]
  norm_num [b1_s1012, b1_s2011, b1_s2012]

theorem b2_s2020 : N 2 (2, 0, 2, 0) = 0 := by
  show N (1 + 1) (2, 0, 2, 0) = 0
  rw [tr_s2020]
  norm_num [b1_s1020, b1_s2020]

theorem b2_s2021 : N 2 (2, 0, 2, 1) = 0 := by
  show N (1 + 1) (2, 0, 2, 1) = 0
  rw [tr_s2021]
  norm_num [b1_s1021, b1_s2020, b1_s2021]

theorem b2_s2022 : N 2 (2, 0, 2, 2) = 0 := by
  show N (1 + 1) (2, 0, 2, 2) = 0
  rw [tr_s2022]
  norm_num [b1_s1022, b1_s2021, b1_s2022]

theorem b2_s2100 : N 2 (2, 1, 0, 0) = 0 := by
  show N (1 + 1) (2, 1, 0, 0) = 0
  rw [tr_s2100]
  norm_num [b1_s1100, b1_s2000, b1_s2100]

theorem b2_s2101 : N 2 (2, 1, 0, 1) = 0 := by
  show N (1 + 1) (2, 1, 0, 1) = 0
  rw [tr_s2101]
  norm_num [b1_s1101, b1_s2001, b1_s2101]

theorem b2_s2102 : N 2 (2, 1, 0, 2) = 0 := by
  show N (1 + 1) (2, 1, 0, 2) = 0
  rw [tr_s2102]
  norm_num [b1_s1102, b1_s2002, b1_s2102]

theorem b2_s2110 : N 2 (2, 1, 1, 0) = 0 := by
  show N (1 + 1) (2, 1, 1, 0) = 0
  rw [tr_s2110]
  norm_num [b1_s1110, b1_s2010, b1_s2100, b1_s2110]

theorem b2_s2111 : N 2 (2, 1, 1, 1) = 0 := by
  show N (1 + 1) (2, 1, 1, 1) = 0
  rw [tr_s2111]
  norm_num [b1_s1111, b1_s2011, b1_s2101, b1_s2110, b1_s2111]

theorem b2_s2112 : N 2 (2, 1, 1, 2) = 0 := by
  show N (1 + 1) (2, 1, 1, 2) = 0
  rw [tr_s2112]
  norm_num [b1_s1112, b1_s2012, b1_s2102, b1_s2111, b1_s2112]

theorem b2_s2120 : N 2 (2, 1, 2, 0) = 0 := by
  show N (1 + 1) (2, 1, 2, 0) = 0
  rw [tr_s2120]
  norm_num [b1_s1120, b1_s2020, b1_s2110, b1_s2120]

theorem b2_s2121 : N 2 (2, 1, 2, 1) = 0 := by
  show N (1 + 1) (2, 1, 2, 1) = 0
  rw [tr_s2121]
  norm_num [b1_s1121, b1_s2021, b1_s2111, b1_s2120, b1_s2121]

theorem b2_s2122 : N 2 (2, 1, 2, 2) = 0 := by
  show N (1 + 1) (2, 1, 2, 2) = 0
  rw [tr_s2122]
  norm_num [b1_s1122, b1_s2022, b1_s2112, b1_s2121, b1_s2122]

theorem b2_s2200 : N 2 (2, 2, 0, 0) = 0 := by
  show N (1 + 1) (2, 2, 0, 0) = 0
  rw [tr_s2200]
  norm_num [b1_s1200, b1_s2100, b1_s2200]

theorem b2_s2201 : N 2 (2, 2, 0, 1) = 0 := by
  show N (1 + 1) (2, 2, 0, 1) = 0
  rw [tr_s2201]
  norm_num [b1_s1201, b1_s2101, b1_s2201]

theorem b2_s2202 : N 2 (2, 2, 0, 2) = 0 := by
  show N (1 + 1) (2, 2, 0, 2) = 0
  rw [tr_s2202]
  norm_num [b1_s1202, b1_s2102, b1_s2202]

theorem b2_s2210 : N 2 (2, 2, 1, 0) = 0 := by
  show N (1 + 1) (2, 2, 1, 0) = 0
  rw [tr_s2210]
  norm_num [b1_s1210, b1_s2110, b1_s2200, b1_s2210]

theorem b2_s2211 : N 2 (2, 2, 1, 1) = 0 := by
  show N (1 + 1) (2, 2, 1, 1) = 0
  rw [tr_s2211]
  norm_num [b1_s1211, b1_s2111, b1_s2201, b1_s2210, b1_s2211]

theorem b2_s2212 : N 2 (2, 2, 1, 2) = 0 := by
  show N (1 + 1) (2, 2, 1, 2) = 0
  rw [tr_s2212]
  norm_num [b1_s1212, b1_s2112, b1_s2202, b1_s2211, b1_s2212]

theorem b2_s2220 : N 2 (2, 2, 2, 0) = 0 := by
  show N (1 + 1) (2, 2, 2, 0) = 0
  rw [tr_s2220]
  norm_num [b1_s1220, b1_s2120, b1_s2210, b1_s2220]

theorem b2_s2221 : N 2 (2, 2, 2, 1) = 0 := by
  show N (1 + 1) (2, 2, 2, 1) = 0
  rw [tr_s2221]
  norm_num [b1_s1221, b1_s2121, b1_s2211, b1_s2220, b1_s2221]

theorem b2_s2222 : N 2 (2, 2, 2, 2) = 0 := by
  show N (1 + 1) (2, 2, 2, 2) = 0
  rw [tr_s2222]
  norm_num [b1_s1222, b1_s2122, b1_s2212, b1_s2221, b1_s2222]

theorem b3_s0000 : N 3 (0, 0, 0, 0) = 0 := tr_s0000 2

theorem b3_s0001 : N 3 (0, 0, 0, 1) = 0 := tr_s0001 2

theorem b3_s0002 : N 3 (0, 0, 0, 2) = 0 := tr_s0002 2

theorem b3_s0010 : N 3 (0, 0, 1, 0) = 0 := tr_s0010 2

theorem b3_s0011 : N 3 (0, 0, 1, 1) = 0 := by
  show N (2 + 1) (0, 0, 1, 1) = 0
  rw [tr_s0011]
  norm_num [b2_s0010]

theorem b3_s0012 : N 3 (0, 0, 1, 2) = 0 := by
  show N (2 + 1) (0, 0, 1, 2) = 0
  rw [tr_s0012]
  norm_num [b2_s0011, b2_s0012]

theorem b3_s0020 : N 3 (0, 0, 2, 0) = 0 := tr_s0020 2

theorem b3_s0021 : N 3 (0, 0, 2, 1) = 0 := by
  show N (2 + 1) (0, 0, 2, 1) = 0
  rw [tr_s0021]
  norm_num [b2_s0020]

theorem b3_s0022 : N 3 (0, 0, 2, 2) = 0 := by
  show N (2 + 1) (0, 0, 2, 2) = 0
  rw [tr_s0022]
  norm_num [b2_s0021, b2_s0022]

theorem b3_s0100 : N 3 (0, 1, 0, 0) = 0 := tr_s0100 2

theorem b3_s0101 : N 3 (0, 1, 0, 1) = 0 := tr_s0101 2

theorem b3_s0102 : N 3 (0, 1, 0, 2) = 0 := tr_s0102 2

theorem b3_s0110 : N 3 (0, 1, 1, 0) = 0 := by
  show N (2 + 1) (0, 1, 1, 0) = 0
  rw [tr_s0110]
  norm_num [b2_s0100]

theorem b3_s0111 : N 3 (0, 1, 1, 1) = 0 := by
  show N (2 + 1) (0, 1, 1, 1) = 0
  rw [tr_s0111]
  norm_num [b2_s0101, b2_s0110]

theorem b3_s0112 : N 3 (0, 1, 1, 2) = 0 := by
  show N (2 + 1) (0, 1, 1, 2) = 0
  rw [tr_s0112]
  norm_num [b2_s0102, b2_s0111, b2_s0112]

theorem b3_s0120 : N 3 (0, 1, 2, 0) = 0 := by
  show N (2 + 1) (0, 1, 2, 0) = 0
  rw [tr_s0120]
  norm_num [b2_s0110, b2_s0120]

theorem b3_s0121 : N 3 (0, 1, 2, 1) = 0 := by
  show N (2 + 1) (0, 1, 2, 1) = 0
  rw [tr_s0121]
  norm_num [b2_s0111, b2_s0120, b2_s0121]

theorem b3_s0122 : N 3 (0, 1, 2, 2) = 0 := by
  show N (2 + 1) (0, 1, 2, 2) = 0
  rw [tr_s0122]
  norm_num [b2_s0112, b2_s0121, b2_s0122]

theorem b3_s0200 : N 3 (0, 2, 0, 0) = 0 := tr_s0200 2

theorem b3_s0201 : N 3 (0, 2, 0, 1) = 0 := tr_s0201 2

theorem b3_s0202 : N 3 (0, 2, 0, 2) = 0 := tr_s0202 2

theorem b3_s0210 : N 3 (0, 2, 1, 0) = 0 := by
  show N (2 + 1) (0, 2, 1, 0) = 0
  rw [tr_s0210]
  norm_num [b2_s0200]

theorem b3_s0211 : N 3 (0, 2, 1, 1) = 0 := by
  show N (2 + 1) (0, 2, 1, 1) = 0
  rw [tr_s0211]
  norm_num [b2_s0201, b2_s0210]

theorem b3_s0212 : N 3 (0, 2, 1, 2) = 0 := by
  show N (2 + 1) (0, 2, 1, 2) = 0
  rw [tr_s0212]
  norm_num [b2_s0202, b2_s0211, b2_s0212]

theorem b3_s0220 : N 3 (0, 2, 2, 0) = 0 := by
  show N (2 + 1) (0, 2, 2, 0) = 0
  rw [tr_s0220]
  norm_num [b2_s0210, b2_s0220]

theorem b3_s0221 : N 3 (0, 2, 2, 1) = 0 := by
  show N (2 + 1) (0, 2, 2, 1) = 0
  rw [tr_s0221]
  norm_num [b2_s0211, b2_s0220, b2_s0221]

theorem b3_s0222 : N 3 (0, 2, 2, 2) = 0 := by
  show N (2 + 1) (0, 2, 2, 2) = 0
  rw [tr_s0222]
  norm_num [b2_s0212, b2_s0221, b2_s0222]

theorem b3_s1000 : N 3 (1, 0, 0, 0) = 0 := by
  show N (2 + 1) (1, 0, 0, 0) = 0
  rw [tr_s1000]
  norm_num [b2_s0000]

theorem b3_s1001 : N 3 (1, 0, 0, 1) = 0 := by
  show N (2 + 1) (1, 0, 0, 1) = 0
  rw [tr_s1001]
  norm_num [b2_s0001]

theorem b3_s1002 : N 3 (1, 0, 0, 2) = 0 := by
  show N (2 + 1) (1, 0, 0, 2) = 0
  rw [tr_s1002]
  norm_num [b2_s0002]

theorem b3_s1010 : N 3 (1, 0, 1, 0) = 0 := by
  show N (2 + 1) (1, 0, 1, 0) = 0
  rw [tr_s1010]
  norm_num [b2_s0010]

theorem b3_s1011 : N 3 (1, 0, 1, 1) = 0 := by
  show N (2 + 1) (1, 0, 1, 1) = 0
  rw [tr_s1011]
  norm_num [b2_s0011, b2_s1010]

theorem b3_s1012 : N 3 (1, 0, 1, 2) = 0 := by
  show N (2 + 1) (1, 0, 1, 2) = 0
  rw [tr_s1012]
  norm_num [b2_s0012, b2_s1011, b2_s1012]

theorem b3_s1020 : N 3 (1, 0, 2, 0) = 0 := by
  show N (2 + 1) (1, 0, 2, 0) = 0
  rw [tr_s1020]
  norm_num [b2_s0020]

theorem b3_s1021 : N 3 (1, 0, 2, 1) = 0 := by
  show N (2 + 1) (1, 0, 2, 1) = 0
  rw [tr_s1021]
  norm_num [b2_s0021, b2_s1020]

theorem b3_s1022 : N 3 (1, 0, 2, 2) = 0 := by
  show N (2 + 1) (1, 0, 2, 2) = 0
  rw [tr_s1022]
  norm_num [b2_s0022, b2_s1021, b2_s1022]

theorem b3_s1100 : N 3 (1, 1, 0, 0) = 0 := by
  show N (2 + 1) (1, 1, 0, 0) = 0
  rw [tr_s1100]
  norm_num [b2_s0100, b2_s1000]

theorem b3_s1101 : N 3 (1, 1, 0, 1) = 0 := by
  show N (2 + 1) (1, 1, 0, 1) = 0
  rw [tr_s1101]
  norm_num [b2_s0101, b2_s1001]

theorem b3_s1102 : N 3 (1, 1, 0, 2) = 0 := by
  show N (2 + 1) (1, 1, 0, 2) = 0
  rw [tr_s1102]
  norm_num [b2_s0102, b2_s1002]

theorem b3_s1110 : N 3 (1, 1, 1, 0) = 1 := by
  show N (2 + 1) (1, 1, 1, 0) = 1
  rw [tr_s1110]
  norm_num [b2_s0110, b2_s1010, b2_s1100]

theorem b3_s1111 : N 3 (1, 1, 1, 1) = 0 := by
  show N (2 + 1) (1, 1, 1, 1) = 0
  rw [tr_s1111]
  norm_num [b2_s0111, b2_s1011, b2_s1101, b2_s1110]

theorem b3_s1112 : N 3 (1, 1, 1, 2) = 0 := by
  show N (2 + 1) (1, 1, 1, 2) = 0
  rw [tr_s1112]
  norm_num [b2_s0112, b2_s1012, b2_s1102, b2_s1111, b2_s1112]

theorem b3_s1120 : N 3 (1, 1, 2, 0) = 0 := by
  show N (2 + 1) (1, 1, 2, 0) = 0
  rw [tr_s1120]
  norm_num [b2_s0120, b2_s1020, b2_s1110, b2_s1120]

theorem b3_s1121 : N 3 (1, 1, 2, 1) = 0 := by
  show N (2 + 1) (1, 1, 2, 1) = 0
  rw [tr_s1121]
  norm_num [b2_s0121, b2_s1021, b2_s1111, b2_s1120, b2_s1121]

theorem b3_s1122 : N 3 (1, 1, 2, 2) = 0 := by
  show N (2 + 1) (1, 1, 2, 2) = 0
  rw [tr_s1122]
  norm_num [b2_s0122, b2_s1022, b2_s1112, b2_s1121, b2_s1122]

theorem b3_s1200 : N 3 (1, 2, 0, 0) = 1 := by
  show N (2 + 1) (1, 2, 0, 0) = 1
  rw [tr_s1200]
  norm_num [b2_s0200, b2_s1100, b2_s1200]

theorem b3_s1201 : N 3 (1, 2, 0, 1) = 0 := by
  show N (2 + 1) (1, 2, 0, 1) = 0
  rw [tr_s1201]
  norm_num [b2_s0201, b2_s1101, b2_s1201]

theorem b3_s1202 : N 3 (1, 2, 0, 2) = 0 := by
  show N (2 + 1) (1, 2, 0, 2) = 0
  rw [tr_s1202]
  norm_num [b2_s0202, b2_s1102, b2_s1202]

theorem b3_s1210 : N 3 (1, 2, 1, 0) = 0 := by
  show N (2 + 1) (1, 2, 1, 0) = 0
  rw [tr_s1210]
  norm_num [b2_s0210, b2_s1110, b2_s1200, b2_s1210]

theorem b3_s1211 : N 3 (1, 2, 1, 1) = 0 := by
  show N (2 + 1) (1, 2, 1, 1) = 0
  rw [tr_s1211]
  norm_num [b2_s0211, b2_s1111, b2_s1201, b2_s1210, b2_s1211]

theorem b3_s1212 : N 3 (1, 2, 1, 2) = 0 := by
  show N (2 + 1) (1, 2, 1, 2) = 0
  rw [tr_s1212]
  norm_num [b2_s0212, b2_s1112, b2_s1202, b2_s1211, b2_s1212]

theorem b3_s1220 : N 3 (1, 2, 2, 0) = 0 := by
  show N (2 + 1) (1, 2, 2, 0) = 0
  rw [tr_s1220]
  norm_num [b2_s0220, b2_s1120, b2_s1210, b2_s1220]

theorem b3_s1221 : N 3 (1, 2, 2, 1) = 0 := by
  show N (2 + 1) (1, 2, 2, 1) = 0
  rw [tr_s1221]
  norm_num [b2_s0221, b2_s1121, b2_s1211, b2_s1220, b2_s1221]

theorem b3_s1222 : N 3 (1, 2, 2, 2) = 0 := by
  show N (2 + 1) (1, 2, 2, 2) = 0
  rw [tr_s1222]
  norm_num [b2_s0222, b2_s1122, b2_s1212, b2_s1221, b2_s1222]

theorem b3_s2000 : N 3 (2, 0, 0, 0) = 1 := by
  show N (2 + 1) (2, 0, 0, 0) = 1
  rw [tr_s2000]
  norm_num [b2_s1000, b2_s2000]

theorem b3_s2001 : N 3 (2, 0, 0, 1) = 0 := by
  show N (2 + 1) (2, 0, 0, 1) = 0
  rw [tr_s2001]
  norm_num [b2_s1001, b2_s2001]

theorem b3_s2002 : N 3 (2, 0, 0, 2) = 0 := by
  show N (2 + 1) (2, 0, 0, 2) = 0
  rw [tr_s2002]
  norm_num [b2_s1002, b2_s2002]

theorem b3_s2010 : N 3 (2, 0, 1, 0) = 0 := by
  show N (2 + 1) (2, 0, 1, 0) = 0
  rw [tr_s2010]
  norm_num [b2_s1010, b2_s2010]

theorem b3_s2011 : N 3 (2, 0, 1, 1) = 0 := by
  show N (2 + 1) (2, 0, 1, 1) = 0
  rw [tr_s2011]
  norm_num [b2_s1011, b2_s2010, b2_s2011]

theorem b3_s2012 : N 3 (2, 0, 1, 2) = 0 := by
  show N (2 + 1) (2, 0, 1, 2) = 0
  rw [tr_s2012]
  norm_num [b2_s1012, b2_s2011, b2_s2012]

theorem b3_s2020 : N 3 (2, 0, 2, 0) = 0 := by
  show N (2 + 1) (2, 0, 2, 0) = 0
  rw [tr_s2020]
  norm_num [b2_s1020, b2_s2020]

theorem b3_s2021 : N 3 (2, 0, 2, 1) = 0 := by
  show N (2 + 1) (2, 0, 2, 1) = 0
  rw [tr_s2021]
  norm_num [b2_s1021, b2_s2020, b2_s2021]

theorem b3_s2022 : N 3 (2, 0, 2, 2) = 0 := by
  show N (2 + 1) (2, 0, 2, 2) = 0
  rw [tr_s2022]
  norm_num [b2_s1022, b2_s2021, b2_s2022]

theorem b3_s2100 : N 3 (2, 1, 0, 0) = 2 := by
  show N (2 + 1) (2, 1, 0, 0) = 2
  rw [tr_s2100]
  norm_num [b2_s1100, b2_s2000, b2_s2100]

theorem b3_s2101 : N 3 (2, 1, 0, 1) = 0 := by
  show N (2 + 1) (2, 1, 0, 1) = 0
  rw [tr_s2101]
  norm_num [b2_s1101, b2_s2001, b2_s2101]

theorem b3_s2102 : N 3 (2, 1, 0, 2) = 0 := by
  show N (2 + 1) (2, 1, 0, 2) = 0
  rw [tr_s2102]
  norm_num [b2_s1102, b2_s2002, b2_s2102]

theorem b3_s2110 : N 3 (2, 1, 1, 0) = 0 := by
  show N (2 + 1) (2, 1, 1, 0) = 0
  rw [tr_s2110]
  norm_num [b2_s1110, b2_s2010, b2_s2100, b2_s2110]

theorem b3_s2111 : N 3 (2, 1, 1, 1) = 0 := by
  show N (2 + 1) (2, 1, 1, 1) = 0
  rw [tr_s2111]
  norm_num [b2_s1111, b2_s2011, b2_s2101, b2_s2110, b2_s2111]

theorem b3_s2112 : N 3 (2, 1, 1, 2) = 0 := by
  show N (2 + 1) (2, 1, 1, 2) = 0
  rw [tr_s2112]
  norm_num [b2_s1112, b2_s2012, b2_s2102, b2_s2111, b2_s2112]

theorem b3_s2120 : N 3 (2, 1, 2, 0) = 0 := by
  show N (2 + 1) (2, 1, 2, 0) = 0
  rw [tr_s2120]
  norm_num [b2_s1120, b2_s2020, b2_s2110, b2_s2120]

theorem b3_s2121 : N 3 (2, 1, 2, 1) = 0 := by
  show N (2 + 1) (2, 1, 2, 1) = 0
  rw [tr_s2121]
  norm_num [b2_s1121, b2_s2021, b2_s2111, b2_s2120, b2_s2121]

theorem b3_s2122 : N 3 (2, 1, 2, 2) = 0 := by
  show N (2 + 1) (2, 1, 2, 2) = 0
  rw [tr_s2122]
  norm_num [b2_s1122, b2_s2022, b2_s2112, b2_s2121, b2_s2122]

theorem b3_s2200 : N 3 (2, 2, 0, 0) = 0 := by
  show N (2 + 1) (2, 2, 0, 0) = 0
  rw [tr_s2200]
  norm_num [b2_s1200, b2_s2100, b2_s2200]

theorem b3_s2201 : N 3 (2, 2, 0, 1) = 0 := by
  show N (2 + 1) (2, 2, 0, 1) = 0
  rw [tr_s2201]
  norm_num [b2_s1201, b2_s2101, b2_s2201]

theorem b3_s2202 : N 3 (2, 2, 0, 2) = 0 := by
  show N (2 + 1) (2, 2, 0, 2) = 0
  rw [tr_s2202]
  norm_num [b2_s1202, b2_s2102, b2_s2202]

theorem b3_s2210 : N 3 (2, 2, 1, 0) = 0 := by
  show N (2 + 1) (2, 2, 1, 0) = 0
  rw [tr_s2210]
  norm_num [b2_s1210, b2_s2110, b2_s2200, b2_s2210]

theorem b3_s2211 : N 3 (2, 2, 1, 1) = 0 := by
  show N (2 + 1) (2, 2, 1, 1) = 0
  rw [tr_s2211]
  norm_num [b2_s1211, b2_s2111, b2_s2201, b2_s2210, b2_s2211]

theorem b3_s2212 : N 3 (2, 2, 1, 2) = 0 := by
  show N (2 + 1) (2, 2, 1, 2) = 0
  rw [tr_s2212]
  norm_num [b2_s1212, b2_s2112, b2_s2202, b2_s2211, b2_s2212]

theorem b3_s2220 : N 3 (2, 2, 2, 0) = 0 := by
  show N (2 + 1) (2, 2, 2, 0) = 0
  rw [tr_s2220]
  norm_num [b2_s1220, b2_s2120, b2_s2210, b2_s2220]

theorem b3_s2221 : N 3 (2, 2, 2, 1) = 0 := by
  show N (2 + 1) (2, 2, 2, 1) = 0
  rw [tr_s2221]
  norm_num [b2_s1221, b2_s2121, b2_s2211, b2_s2220, b2_s2221]

theorem b3_s2222 : N 3 (2, 2, 2, 2) = 0 := by
  show N (2 + 1) (2, 2, 2, 2) = 0
  rw [tr_s2222]
  norm_num [b2_s1222, b2_s2122, b2_s2212, b2_s2221, b2_s2222]

theorem b4_s0000 : N 4 (0, 0, 0, 0) = 0 := tr_s0000 3

theorem b4_s0001 : N 4 (0, 0, 0, 1) = 0 := tr_s0001 3

theorem b4_s0002 : N 4 (0, 0, 0, 2) = 0 := tr_s0002 3

theorem b4_s0010 : N 4 (0, 0, 1, 0) = 0 := tr_s0010 3

theorem b4_s0011 : N 4 (0, 0, 1, 1) = 0 := by
  show N (3 + 1) (0, 0, 1, 1) = 0
  rw [tr_s0011]
  norm_num [b3_s0010]

theorem b4_s0012 : N 4 (0, 0, 1, 2) = 0 := by
  show N (3 + 1) (0, 0, 1, 2) = 0
  rw [tr_s0012]
  norm_num [b3_s0011, b3_s0012]

theorem b4_s0020 : N 4 (0, 0, 2, 0) = 0 := tr_s0020 3

theorem b4_s0021 : N 4 (0, 0, 2, 1) = 0 := by
  show N (3 + 1) (0, 0, 2, 1) = 0
  rw [tr_s0021]
  norm_num [b3_s0020]

theorem b4_s0022 : N 4 (0, 0, 2, 2) = 0 := by
  show N (3 + 1) (0, 0, 2, 2) = 0
  rw [tr_s0022]
  norm_num [b3_s0021, b3_s0022]

theorem b4_s0100 : N 4 (0, 1, 0, 0) = 0 := tr_s0100 3

theorem b4_s0101 : N 4 (0, 1, 0, 1) = 0 := tr_s0101 3

theorem b4_s0102 : N 4 (0, 1, 0, 2) = 0 := tr_s0102 3

theorem b4_s0110 : N 4 (0, 1, 1, 0) = 0 := by
  show N (3 + 1) (0, 1, 1, 0) = 0
  rw [tr_s0110]
  norm_num [b3_s0100]

theorem b4_s0111 : N 4 (0, 1, 1, 1) = 0 := by
  show N (3 + 1) (0, 1, 1, 1) = 0
  rw [tr_s0111]
  norm_num [b3_s0101, b3_s0110]

theorem b4_s0112 : N 4 (0, 1, 1, 2) = 0 := by
  show N (3 + 1) (0, 1, 1, 2) = 0
  rw [tr_s0112]
  norm_num [b3_s0102, b3_s0111, b3_s0112]

theorem b4_s0120 : N 4 (0, 1, 2, 0) = 0 := by
  show N (3 + 1) (0, 1, 2, 0) = 0
  rw [tr_s0120]
  norm_num [b3_s0110, b3_s0120]

theorem b4_s0121 : N 4 (0, 1, 2, 1) = 0 := by
  show N (3 + 1) (0, 1, 2, 1) = 0
  rw [tr_s0121]
  norm_num [b3_s0111, b3_s0120, b3_s0121]

theorem b4_s0122 : N 4 (0, 1, 2, 2) = 0 := by
  show N (3 + 1) (0, 1, 2, 2) = 0
  rw [tr_s0122]
  norm_num [b3_s0112, b3_s0121, b3_s0122]

theorem b4_s0200 : N 4 (0, 2, 0, 0) = 0 := tr_s0200 3

theorem b4_s0201 : N 4 (0, 2, 0, 1) = 0 := tr_s0201 3

theorem b4_s0202 : N 4 (0, 2, 0, 2) = 0 := tr_s0202 3

theorem b4_s0210 : N 4 (0, 2, 1, 0) = 0 := by
  show N (3 + 1) (0, 2, 1, 0) = 0
  rw [tr_s0210]
  norm_num [b3_s0200]

theorem b4_s0211 : N 4 (0, 2, 1, 1) = 0 := by
  show N (3 + 1) (0, 2, 1, 1) = 0
  rw [tr_s0211]
  norm_num [b3_s0201, b3_s0210]

theorem b4_s0212 : N 4 (0, 2, 1, 2) = 0 := by
  show N (3 + 1) (0, 2, 1, 2) = 0
  rw [tr_s0212]
  norm_num [b3_s0202, b3_s0211, b3_s0212]

theorem b4_s0220 : N 4 (0, 2, 2, 0) = 0 := by
  show N (3 + 1) (0, 2, 2, 0) = 0
  rw [tr_s0220]
  norm_num [b3_s0210, b3_s0220]

theorem b4_s0221 : N 4 (0, 2, 2, 1) = 0 := by
  show N (3 + 1) (0, 2, 2, 1) = 0
  rw [tr_s0221]
  norm_num [b3_s0211, b3_s0220, b3_s0221]

theorem b4_s0222 : N 4 (0, 2, 2, 2) = 0 := by
  show N (3 + 1) (0, 2, 2, 2) = 0
  rw [tr_s0222]
  norm_num [b3_s0212, b3_s0221, b3_s0222]

theorem b4_s1000 : N 4 (1, 0, 0, 0) = 0 := by
  show N (3 + 1) (1, 0, 0, 0) = 0
  rw [tr_s1000]
  norm_num [b3_s0000]

theorem b4_s1001 : N 4 (1, 0, 0, 1) = 0 := by
  show N (3 + 1) (1, 0, 0, 1) = 0
  rw [tr_s1001]
  norm_num [b3_s0001]

theorem b4_s1002 : N 4 (1, 0, 0, 2) = 0 := by
  show N (3 + 1) (1, 0, 0, 2) = 0
  rw [tr_s1002]
  norm_num [b3_s0002]

theorem b4_s1010 : N 4 (1, 0, 1, 0) = 0 := by
  show N (3 + 1) (1, 0, 1, 0) = 0
  rw [tr_s1010]
  norm_num [b3_s0010]

theorem b4_s1011 : N 4 (1, 0, 1, 1) = 0 := by
  show N (3 + 1) (1, 0, 1, 1) = 0
  rw [tr_s1011]
  norm_num [b3_s0011, b3_s1010]

theorem b4_s1012 : N 4 (1, 0, 1, 2) = 0 := by
  show N (3 + 1) (1, 0, 1, 2) = 0
  rw [tr_s1012]
  norm_num [b3_s0012, b3_s1011, b3_s1012]

theorem b4_s1020 : N 4 (1, 0, 2, 0) = 0 := by
  show N (3 + 1) (1, 0, 2, 0) = 0
  rw [tr_s1020]
  norm_num [b3_s0020]

theorem b4_s1021 : N 4 (1, 0, 2, 1) = 0 := by
  show N (3 + 1) (1, 0, 2, 1) = 0
  rw [tr_s1021]
  norm_num [b3_s0021, b3_s1020]

theorem b4_s1022 : N 4 (1, 0, 2, 2) = 0 := by
  show N (3 + 1) (1, 0, 2, 2) = 0
  rw [tr_s1022]
  norm_num [b3_s0022, b3_s1021, b3_s1022]

theorem b4_s1100 : N 4 (1, 1, 0, 0) = 0 := by
  show N (3 + 1) (1, 1, 0, 0) = 0
  rw [tr_s1100]
  norm_num [b3_s0100, b3_s1000]

theorem b4_s1101 : N 4 (1, 1, 0, 1) = 0 := by
  show N (3 + 1) (1, 1, 0, 1) = 0
  rw [tr_s1101]
  norm_num [b3_s0101, b3_s1001]

theorem b4_s1102 : N 4 (1, 1, 0, 2) = 0 := by
  show N (3 + 1) (1, 1, 0, 2) = 0
  rw [tr_s1102]
  norm_num [b3_s0102, b3_s1002]

theorem b4_s1110 : N 4 (1, 1, 1, 0) = 0 := by
  show N (3 + 1) (1, 1, 1, 0) = 0
  rw [tr_s1110]
  norm_num [b3_s0110, b3_s1010, b3_s1100]

theorem b4_s1111 : N 4 (1, 1, 1, 1) = 1 := by
  show N (3 + 1) (1, 1, 1, 1) = 1
  rw [tr_s1111]
  norm_num [b3_s0111, b3_s1011, b3_s1101, b3_s1110]

theorem b4_s1112 : N 4 (1, 1, 1, 2) = 0 := by
  show N (3 + 1) (1, 1, 1, 2) = 0
  rw [tr_s1112]
  norm_num [b3_s0112, b3_s1012, b3_s1102, b3_s1111, b3_s1112]

theorem b4_s1120 : N 4 (1, 1, 2, 0) = 1 := by
  show N (3 + 1) (1, 1, 2, 0) = 1
  rw [tr_s1120]
  norm_num [b3_s0120, b3_s1020, b3_s1110, b3_s1120]

theorem b4_s1121 : N 4 (1, 1, 2, 1) = 0 := by
  show N (3 + 1) (1, 1, 2, 1) = 0
  rw [tr_s1121]
  norm_num [b3_s0121, b3_s1021, b3_s1111, b3_s1120, b3_s1121]

theorem b4_s1122 : N 4 (1, 1, 2, 2) = 0 := by
  show N (3 + 1) (1, 1, 2, 2) = 0
  rw [tr_s1122]
  norm_num [b3_s0122, b3_s1022, b3_s1112, b3_s1121, b3_s1122]

theorem b4_s1200 : N 4 (1, 2, 0, 0) = 1 := by
  show N (3 + 1) (1, 2, 0, 0) = 1
  rw [tr_s1200]
  norm_num [b3_s0200, b3_s1100, b3_s1200]

theorem b4_s1201 : N 4 (1, 2, 0, 1) = 0 := by
  show N (3 + 1) (1, 2, 0, 1) = 0
  rw [tr_s1201]
  norm_num [b3_s0201, b3_s1101, b3_s1201]

theorem b4_s1202 : N 4 (1, 2, 0, 2) = 0 := by
  show N (3 + 1) (1, 2, 0, 2) = 0
  rw [tr_s1202]
  norm_num [b3_s0202, b3_s1102, b3_s1202]

theorem b4_s1210 : N 4 (1, 2, 1, 0) = 2 := by
  show N (3 + 1) (1, 2, 1, 0) = 2
  rw [tr_s1210]
  norm_num [b3_s0210, b3_s1110, b3_s1200, b3_s1210]

theorem b4_s1211 : N 4 (1, 2, 1, 1) = 0 := by
  show N (3 + 1) (1, 2, 1, 1) = 0
  rw [tr_s1211]
  norm_num [b3_s0211, b3_s1111, b3_s1201, b3_s1210, b3_s1211]

theorem b4_s1212 : N 4 (1, 2, 1, 2) = 0 := by
  show N (3 + 1) (1, 2, 1, 2) = 0
  rw [tr_s1212]
  norm_num [b3_s0212, b3_s1112, b3_s1202, b3_s1211, b3_s1212]

theorem b4_s1220 : N 4 (1, 2, 2, 0) = 0 := by
  show N (3 + 1) (1, 2, 2, 0) = 0
  rw [tr_s1220]
  norm_num [b3_s0220, b3_s1120, b3_s1210, b3_s1220]

theorem b4_s1221 : N 4 (1, 2, 2, 1) = 0 := by
  show N (3 + 1) (1, 2, 2, 1) = 0
  rw [tr_s1221]
  norm_num [b3_s0221, b3_s1121, b3_s1211, b3_s1220, b3_s1221]

theorem b4_s1222 : N 4 (1, 2, 2, 2) = 0 := by
  show N (3 + 1) (1, 2, 2, 2) = 0
  rw [tr_s1222]
  norm_num [b3_s0222, b3_s1122, b3_s1212, b3_s1221, b3_s1222]

theorem b4_s2000 : N 4 (2, 0, 0, 0) = 1 := by
  show N (3 + 1) (2, 0, 0, 0) = 1
  rw [tr_s2000]
  norm_num [b3_s1000, b3_s2000]

theorem b4_s2001 : N 4 (2, 0, 0, 1) = 0 := by
  show N (3 + 1) (2, 0, 0, 1) = 0
  rw [tr_s2001]
  norm_num [b3_s1001, b3_s2001]

theorem b4_s2002 : N 4 (2, 0, 0, 2) = 0 := by
  show N (3 + 1) (2, 0, 0, 2) = 0
  rw [tr_s2002]
  norm_num [b3_s1002, b3_s2002]

theorem b4_s2010 : N 4 (2, 0, 1, 0) = 0 := by
  show N (3 + 1) (2, 0, 1, 0) = 0
  rw [tr_s2010]
  norm_num [b3_s1010, b3_s2010]

theorem b4_s2011 : N 4 (2, 0, 1, 1) = 0 := by
  show N (3 + 1) (2, 0, 1, 1) = 0
  rw [tr_s2011]
  norm_num [b3_s1011, b3_s2010, b3_s2011]

theorem b4_s2012 : N 4 (2, 0, 1, 2) = 0 := by
  show N (3 + 1) (2, 0, 1, 2) = 0
  rw [tr_s2012]
  norm_num [b3_s1012, b3_s2011, b3_s2012]

theorem b4_s2020 : N 4 (2, 0, 2, 0) = 0 := by
  show N (3 + 1) (2, 0, 2, 0) = 0
  rw [tr_s2020]
  norm_num [b3_s1020, b3_s2020]

theorem b4_s2021 : N 4 (2, 0, 2, 1) = 0 := by
  show N (3 + 1) (2, 0, 2, 1) = 0
  rw [tr_s2021]
  norm_num [b3_s1021, b3_s2020, b3_s2021]

theorem b4_s2022 : N 4 (2, 0, 2, 2) = 0 := by
  show N (3 + 1) (2, 0, 2, 2) = 0
  rw [tr_s2022]
  norm_num [b3_s1022, b3_s2021, b3_s2022]

theorem b4_s2100 : N 4 (2, 1, 0, 0) = 3 := by
  show N (3 + 1) (2, 1, 0, 0) = 3
  rw [tr_s2100]
  norm_num [b3_s1100, b3_s2000, b3_s2100]

theorem b4_s2101 : N 4 (2, 1, 0, 1) = 0 := by
  show N (3 + 1) (2, 1, 0, 1) = 0
  rw [tr_s2101]
  norm_num [b3_s1101, b3_s2001, b3_s2101]

theorem b4_s2102 : N 4 (2, 1, 0, 2) = 0 := by
  show N (3 + 1) (2, 1, 0, 2) = 0
  rw [tr_s2102]
  norm_num [b3_s1102, b3_s2002, b3_s2102]

theorem b4_s2110 : N 4 (2, 1, 1, 0) = 3 := by
  show N (3 + 1) (2, 1, 1, 0) = 3
  rw [tr_s2110]
  norm_num [b3_s1110, b3_s2010, b3_s2100, b3_s2110]

theorem b4_s2111 : N 4 (2, 1, 1, 1) = 0 := by
  show N (3 + 1) (2, 1, 1, 1) = 0
  rw [tr_s2111]
  norm_num [b3_s1111, b3_s2011, b3_s2101, b3_s2110, b3_s2111]

theorem b4_s2112 : N 4 (2, 1, 1, 2) = 0 := by
  show N (3 + 1) (2, 1, 1, 2) = 0
  rw [tr_s2112]
  norm_num [b3_s1112, b3_s2012, b3_s2102, b3_s2111, b3_s2112]

theorem b4_s2120 : N 4 (2, 1, 2, 0) = 0 := by
  show N (3 + 1) (2, 1, 2, 0) = 0
  rw [tr_s2120]
  norm_num [b3_s1120, b3_s2020, b3_s2110, b3_s2120]

theorem b4_s2121 : N 4 (2, 1, 2, 1) = 0 := by
  show N (3 + 1) (2, 1, 2, 1) = 0
  rw [tr_s2121]
  norm_num [b3_s1121, b3_s2021, b3_s2111, b3_s2120, b3_s2121]

theorem b4_s2122 : N 4 (2, 1, 2, 2) = 0 := by
  show N (3 + 1) (2, 1, 2, 2) = 0
  rw [tr_s2122]
  norm_num [b3_s1122, b3_s2022, b3_s2112, b3_s2121, b3_s2122]

theorem b4_s2200 : N 4 (2, 2, 0, 0) = 3 := by
  show N (3 + 1) (2, 2, 0, 0) = 3
  rw [tr_s2200]
  norm_num [b3_s1200, b3_s2100, b3_s2200]

theorem b4_s2201 : N 4 (2, 2, 0, 1) = 0 := by
  show N (3 + 1) (2, 2, 0, 1) = 0
  rw [tr_s2201]
  norm_num [b3_s1201, b3_s2101, b3_s2201]

theorem b4_s2202 : N 4 (2, 2, 0, 2) = 0 := by
  show N (3 + 1) (2, 2, 0, 2) = 0
  rw [tr_s2202]
  norm_num [b3_s1202, b3_s2102, b3_s2202]

theorem b4_s2210 : N 4 (2, 2, 1, 0) = 0 := by
  show N (3 + 1) (2, 2, 1, 0) = 0
  rw [tr_s2210]
  norm_num [b3_s1210, b3_s2110, b3_s2200, b3_s2210]

theorem b4_s2211 : N 4 (2, 2, 1, 1) = 0 := by
  show N (3 + 1) (2, 2, 1, 1) = 0
  rw [tr_s2211]
  norm_num [b3_s1211, b3_s2111, b3_s2201, b3_s2210, b3_s2211]

theorem b4_s2212 : N 4 (2, 2, 1, 2) = 0 := by
  show N (3 + 1) (2, 2, 1, 2) = 0
  rw [tr_s2212]
  norm_num [b3_s1212, b3_s2112, b3_s2202, b3_s2211, b3_s2212]

theorem b4_s2220 : N 4 (2, 2, 2, 0) = 0 := by
  show N (3 + 1) (2, 2, 2, 0) = 0
  rw [tr_s2220]
  norm_num [b3_s1220, b3_s2120, b3_s2210, b3_s2220]

theorem b4_s2221 : N 4 (2, 2, 2, 1) = 0 := by
  show N (3 + 1) (2, 2, 2, 1) = 0
  rw [tr_s2221]
  norm_num [b3_s1221, b3_s2121, b3_s2211, b3_s2220, b3_s2221]

theorem b4_s2222 : N 4 (2, 2, 2, 2) = 0 := by
  show N (3 + 1) (2, 2, 2, 2) = 0
  rw [tr_s2222]
  norm_num [b3_s1222, b3_s2122, b3_s2212, b3_s2221, b3_s2222]

theorem b5_s0000 : N 5 (0, 0, 0, 0) = 0 := tr_s0000 4

theorem b5_s0001 : N 5 (0, 0, 0, 1) = 0 := tr_s0001 4

theorem b5_s0002 : N 5 (0, 0, 0, 2) = 0 := tr_s0002 4

theorem b5_s0010 : N 5 (0, 0, 1, 0) = 0 := tr_s0010 4

theorem b5_s0011 : N 5 (0, 0, 1, 1) = 0 := by
  show N (4 + 1) (0, 0, 1, 1) = 0
  rw [tr_s0011]
  norm_num [b4_s0010]

theorem b5_s0012 : N 5 (0, 0, 1, 2) = 0 := by
  show N (4 + 1) (0, 0, 1, 2) = 0
  rw [tr_s0012]
  norm_num [b4_s0011, b4_s0012]

theorem b5_s0020 : N 5 (0, 0, 2, 0) = 0 := tr_s0020 4

theorem b5_s0021 : N 5 (0, 0, 2, 1) = 0 := by
  show N (4 + 1) (0, 0, 2, 1) = 0
  rw [tr_s0021]
  norm_num [b4_s0020]

theorem b5_s0022 : N 5 (0, 0, 2, 2) = 0 := by
  show N (4 + 1) (0, 0, 2, 2) = 0
  rw [tr_s0022]
  norm_num [b4_s0021, b4_s0022]

theorem b5_s0100 : N 5 (0, 1, 0, 0) = 0 := tr_s0100 4

theorem b5_s0101 : N 5 (0, 1, 0, 1) = 0 := tr_s0101 4

theorem b5_s0102 : N 5 (0, 1, 0, 2) = 0 := tr_s0102 4

theorem b5_s0110 : N 5 (0, 1, 1, 0) = 0 := by
  show N (4 + 1) (0, 1, 1, 0) = 0
  rw [tr_s0110]
  norm_num [b4_s0100]

theorem b5_s0111 : N 5 (0, 1, 1, 1) = 0 := by
  show N (4 + 1) (0, 1, 1, 1) = 0
  rw [tr_s0111]
  norm_num [b4_s0101, b4_s0110]

theorem b5_s0112 : N 5 (0, 1, 1, 2) = 0 := by
  show N (4 + 1) (0, 1, 1, 2) = 0
  rw [tr_s0112]
  norm_num [b4_s0102, b4_s0111, b4_s0112]

theorem b5_s0120 : N 5 (0, 1, 2, 0) = 0 := by
  show N (4 + 1) (0, 1, 2, 0) = 0
  rw [tr_s0120]
  norm_num [b4_s0110, b4_s0120]

theorem b5_s0121 : N 5 (0, 1, 2, 1) = 0 := by
  show N (4 + 1) (0, 1, 2, 1) = 0
  rw [tr_s0121]
  norm_num [b4_s0111, b4_s0120, b4_s0121]

theorem b5_s0122 : N 5 (0, 1, 2, 2) = 0 := by
  show N (4 + 1) (0, 1, 2, 2) = 0
  rw [tr_s0122]
  norm_num [b4_s0112, b4_s0121, b4_s0122]

theorem b5_s0200 : N 5 (0, 2, 0, 0) = 0 := tr_s0200 4

theorem b5_s0201 : N 5 (0, 2, 0, 1) = 0 := tr_s0201 4

theorem b5_s0202 : N 5 (0, 2, 0, 2) = 0 := tr_s0202 4

theorem b5_s0210 : N 5 (0, 2, 1, 0) = 0 := by
  show N (4 + 1) (0, 2, 1, 0) = 0
  rw [tr_s0210]
  norm_num [b4_s0200]

theorem b5_s0211 : N 5 (0, 2, 1, 1) = 0 := by
  show N (4 + 1) (0, 2, 1, 1) = 0
  rw [tr_s0211]
  norm_num [b4_s0201, b4_s0210]

theorem b5_s0212 : N 5 (0, 2, 1, 2) = 0 := by
  show N (4 + 1) (0, 2, 1, 2) = 0
  rw [tr_s0212]
  norm_num [b4_s0202, b4_s0211, b4_s0212]

theorem b5_s0220 : N 5 (0, 2, 2, 0) = 0 := by
  show N (4 + 1) (0, 2, 2, 0) = 0
  rw [tr_s0220]
  norm_num [b4_s0210, b4_s0220]

theorem b5_s0221 : N 5 (0, 2, 2, 1) = 0 := by
  show N (4 + 1) (0, 2, 2, 1) = 0
  rw [tr_s0221]
  norm_num [b4_s0211, b4_s0220, b4_s0221]

theorem b5_s0222 : N 5 (0, 2, 2, 2) = 0 := by
  show N (4 + 1) (0, 2, 2, 2) = 0
  rw [tr_s0222]
  norm_num [b4_s0212, b4_s0221, b4_s0222]

theorem b5_s1000 : N 5 (1, 0, 0, 0) = 0 := by
  show N (4 + 1) (1, 0, 0, 0) = 0
  rw [tr_s1000]
  norm_num [b4_s0000]

theorem b5_s1001 : N 5 (1, 0, 0, 1) = 0 := by
  show N (4 + 1) (1, 0, 0, 1) = 0
  rw [tr_s1001]
  norm_num [b4_s0001]

theorem b5_s1002 : N 5 (1, 0, 0, 2) = 0 := by
  show N (4 + 1) (1, 0, 0, 2) = 0
  rw [tr_s1002]
  norm_num [b4_s0002]

theorem b5_s1010 : N 5 (1, 0, 1, 0) = 0 := by
  show N (4 + 1) (1, 0, 1, 0) = 0
  rw [tr_s1010]
  norm_num [b4_s0010]

theorem b5_s1011 : N 5 (1, 0, 1, 1) = 0 := by
  show N (4 + 1) (1, 0, 1, 1) = 0
  rw [tr_s1011]
  norm_num [b4_s0011, b4_s1010]

theorem b5_s1012 : N 5 (1, 0, 1, 2) = 0 := by
  show N (4 + 1) (1, 0, 1, 2) = 0
  rw [tr_s1012]
  norm_num [b4_s0012, b4_s1011, b4_s1012]

theorem b5_s1020 : N 5 (1, 0, 2, 0) = 0 := by
  show N (4 + 1) (1, 0, 2, 0) = 0
  rw [tr_s1020]
  norm_num [b4_s0020]

theorem b5_s1021 : N 5 (1, 0, 2, 1) = 0 := by
  show N (4 + 1) (1, 0, 2, 1) = 0
  rw [tr_s1021]
  norm_num [b4_s0021, b4_s1020]

theorem b5_s1022 : N 5 (1, 0, 2, 2) = 0 := by
  show N (4 + 1) (1, 0, 2, 2) = 0
  rw [tr_s1022]
  norm_num [b4_s0022, b4_s1021, b4_s1022]

theorem b5_s1100 : N 5 (1, 1, 0, 0) = 0 := by
  show N (4 + 1) (1, 1, 0, 0) = 0
  rw [tr_s1100]
  norm_num [b4_s0100, b4_s1000]

theorem b5_s1101 : N 5 (1, 1, 0, 1) = 0 := by
  show N (4 + 1) (1, 1, 0, 1) = 0
  rw [tr_s1101]
  norm_num [b4_s0101, b4_s1001]

theorem b5_s1102 : N 5 (1, 1, 0, 2) = 0 := by
  show N (4 + 1) (1, 1, 0, 2) = 0
  rw [tr_s1102]
  norm_num [b4_s0102, b4_s1002]

theorem b5_s1110 : N 5 (1, 1, 1, 0) = 0 := by
  show N (4 + 1) (1, 1, 1, 0) = 0
  rw [tr_s1110]
  norm_num [b4_s0110, b4_s1010, b4_s1100]

theorem b5_s1111 : N 5 (1, 1, 1, 1) = 0 := by
  show N (4 + 1) (1, 1, 1, 1) = 0
  rw [tr_s1111]
  norm_num [b4_s0111, b4_s1011, b4_s1101, b4_s1110]

theorem b5_s1112 : N 5 (1, 1, 1, 2) = 1 := by
  show N (4 + 1) (1, 1, 1, 2) = 1
  rw [tr_s1112]
  norm_num [b4_s0112, b4_s1012, b4_s1102, b4_s1111, b4_s1112]

theorem b5_s1120 : N 5 (1, 1, 2, 0) = 1 := by
  show N (4 + 1) (1, 1, 2, 0) = 1
  rw [tr_s1120]
  norm_num [b4_s0120, b4_s1020, b4_s1110, b4_s1120]

theorem b5_s1121 : N 5 (1, 1, 2, 1) = 2 := by
  show N (4 + 1) (1, 1, 2, 1) = 2
  rw [tr_s1121]
  norm_num [b4_s0121, b4_s1021, b4_s1111, b4_s1120, b4_s1121]

theorem b5_s1122 : N 5 (1, 1, 2, 2) = 0 := by
  show N (4 + 1) (1, 1, 2, 2) = 0
  rw [tr_s1122]
  norm_num [b4_s0122, b4_s1022, b4_s1112, b4_s1121, b4_s1122]

theorem b5_s1200 : N 5 (1, 2, 0, 0) = 1 := by
  show N (4 + 1) (1, 2, 0, 0) = 1
  rw [tr_s1200]
  norm_num [b4_s0200, b4_s1100, b4_s1200]

theorem b5_s1201 : N 5 (1, 2, 0, 1) = 0 := by
  show N (4 + 1) (1, 2, 0, 1) = 0
  rw [tr_s1201]
  norm_num [b4_s0201, b4_s1101, b4_s1201]

theorem b5_s1202 : N 5 (1, 2, 0, 2) = 0 := by
  show N (4 + 1) (1, 2, 0, 2) = 0
  rw [tr_s1202]
  norm_num [b4_s0202, b4_s1102, b4_s1202]

theorem b5_s1210 : N 5 (1, 2, 1, 0) = 3 := by
  show N (4 + 1) (1, 2, 1, 0) = 3
  rw [tr_s1210]
  norm_num [b4_s0210, b4_s1110, b4_s1200, b4_s1210]

theorem b5_s1211 : N 5 (1, 2, 1, 1) = 3 := by
  show N (4 + 1) (1, 2, 1, 1) = 3
  rw [tr_s1211]
  norm_num [b4_s0211, b4_s1111, b4_s1201, b4_s1210, b4_s1211]

theorem b5_s1212 : N 5 (1, 2, 1, 2) = 0 := by
  show N (4 + 1) (1, 2, 1, 2) = 0
  rw [tr_s1212]
  norm_num [b4_s0212, b4_s1112, b4_s1202, b4_s1211, b4_s1212]

theorem b5_s1220 : N 5 (1, 2, 2, 0) = 3 := by
  show N (4 + 1) (1, 2, 2, 0) = 3
  rw [tr_s1220]
  norm_num [b4_s0220, b4_s1120, b4_s1210, b4_s1220]

theorem b5_s1221 : N 5 (1, 2, 2, 1) = 0 := by
  show N (4 + 1) (1, 2, 2, 1) = 0
  rw [tr_s1221]
  norm_num [b4_s0221, b4_s1121, b4_s1211, b4_s1220, b4_s1221]

theorem b5_s1222 : N 5 (1, 2, 2, 2) = 0 := by
  show N (4 + 1) (1, 2, 2, 2) = 0
  rw [tr_s1222]
  norm_num [b4_s0222, b4_s1122, b4_s1212, b4_s1221, b4_s1222]

theorem b5_s2000 : N 5 (2, 0, 0, 0) = 1 := by
  show N (4 + 1) (2, 0, 0, 0) = 1
  rw [tr_s2000]
  norm_num [b4_s1000, b4_s2000]

theorem b5_s2001 : N 5 (2, 0, 0, 1) = 0 := by
  show N (4 + 1) (2, 0, 0, 1) = 0
  rw [tr_s2001]
  norm_num [b4_s1001, b4_s2001]

theorem b5_s2002 : N 5 (2, 0, 0, 2) = 0 := by
  show N (4 + 1) (2, 0, 0, 2) = 0
  rw [tr_s2002]
  norm_num [b4_s1002, b4_s2002]

theorem b5_s2010 : N 5 (2, 0, 1, 0) = 0 := by
  show N (4 + 1) (2, 0, 1, 0) = 0
  rw [tr_s2010]
  norm_num [b4_s1010, b4_s2010]

theorem b5_s2011 : N 5 (2, 0, 1, 1) = 0 := by
  show N (4 + 1) (2, 0, 1, 1) = 0
  rw [tr_s2011]
  norm_num [b4_s1011, b4_s2010, b4_s2011]

theorem b5_s2012 : N 5 (2, 0, 1, 2) = 0 := by
  show N (4 + 1) (2, 0, 1, 2) = 0
  rw [tr_s2012]
  norm_num [b4_s1012, b4_s2011, b4_s2012]

theorem b5_s2020 : N 5 (2, 0, 2, 0) = 0 := by
  show N (4 + 1) (2, 0, 2, 0) = 0
  rw [tr_s2020]
  norm_num [b4_s1020, b4_s2020]

theorem b5_s2021 : N 5 (2, 0, 2, 1) = 0 := by
  show N (4 + 1) (2, 0, 2, 1) = 0
  rw [tr_s2021]
  norm_num [b4_s1021, b4_s2020, b4_s2021]

theorem b5_s2022 : N 5 (2, 0, 2, 2) = 0 := by
  show N (4 + 1) (2, 0, 2, 2) = 0
  rw [tr_s2022]
  norm_num [b4_s1022, b4_s2021, b4_s2022]

theorem b5_s2100 : N 5 (2, 1, 0, 0) = 4 := by
  show N (4 + 1) (2, 1, 0, 0) = 4
  rw [tr_s2100]
  norm_num [b4_s1100, b4_s2000, b4_s2100]

theorem b5_s2101 : N 5 (2, 1, 0, 1) = 0 := by
  show N (4 + 1) (2, 1, 0, 1) = 0
  rw [tr_s2101]
  norm_num [b4_s1101, b4_s2001, b4_s2101]

theorem b5_s2102 : N 5 (2, 1, 0, 2) = 0 := by
  show N (4 + 1) (2, 1, 0, 2) = 0
  rw [tr_s2102]
  norm_num [b4_s1102, b4_s2002, b4_s2102]

theorem b5_s2110 : N 5 (2, 1, 1, 0) = 6 := by
  show N (4 + 1) (2, 1, 1, 0) = 6
  rw [tr_s2110]
  norm_num [b4_s1110, b4_s2010, b4_s2100, b4_s2110]

theorem b5_s2111 : N 5 (2, 1, 1, 1) = 4 := by
  show N (4 + 1) (2, 1, 1, 1) = 4
  rw [tr_s2111]
  norm_num [b4_s1111, b4_s2011, b4_s2101, b4_s2110, b4_s2111]

theorem b5_s2112 : N 5 (2, 1, 1, 2) = 0 := by
  show N (4 + 1) (2, 1, 1, 2) = 0
  rw [tr_s2112]
  norm_num [b4_s1112, b4_s2012, b4_s2102, b4_s2111, b4_s2112]

theorem b5_s2120 : N 5 (2, 1, 2, 0) = 4 := by
  show N (4 + 1) (2, 1, 2, 0) = 4
  rw [tr_s2120]
  norm_num [b4_s1120, b4_s2020, b4_s2110, b4_s2120]

theorem b5_s2121 : N 5 (2, 1, 2, 1) = 0 := by
  show N (4 + 1) (2, 1, 2, 1) = 0
  rw [tr_s2121]
  norm_num [b4_s1121, b4_s2021, b4_s2111, b4_s2120, b4_s2121]

theorem b5_s2122 : N 5 (2, 1, 2, 2) = 0 := by
  show N (4 + 1) (2, 1, 2, 2) = 0
  rw [tr_s2122]
  norm_num [b4_s1122, b4_s2022, b4_s2112, b4_s2121, b4_s2122]

theorem b5_s2200 : N 5 (2, 2, 0, 0) = 10 := by
  show N (4 + 1) (2, 2, 0, 0) = 10
  rw [tr_s2200]
  norm_num [b4_s1200, b4_s2100, b4_s2200]

theorem b5_s2201 : N 5 (2, 2, 0, 1) = 0 := by
  show N (4 + 1) (2, 2, 0, 1) = 0
  rw [tr_s2201]
  norm_num [b4_s1201, b4_s2101, b4_s2201]

theorem b5_s2202 : N 5 (2, 2, 0, 2) = 0 := by
  show N (4 + 1) (2, 2, 0, 2) = 0
  rw [tr_s2202]
  norm_num [b4_s1202, b4_s2102, b4_s2202]

theorem b5_s2210 : N 5 (2, 2, 1, 0) = 8 := by
  show N (4 + 1) (2, 2, 1, 0) = 8
  rw [tr_s2210]
  norm_num [b4_s1210, b4_s2110, b4_s2200, b4_s2210]

theorem b5_s2211 : N 5 (2, 2, 1, 1) = 0 := by
  show N (4 + 1) (2, 2, 1, 1) = 0
  rw [tr_s2211]
  norm_num [b4_s1211, b4_s2111, b4_s2201, b4_s2210, b4_s2211]

theorem b5_s2212 : N 5 (2, 2, 1, 2) = 0 := by
  show N (4 + 1) (2, 2, 1, 2) = 0
  rw [tr_s2212]
  norm_num [b4_s1212, b4_s2112, b4_s2202, b4_s2211, b4_s2212]

theorem b5_s2220 : N 5 (2, 2, 2, 0) = 0 := by
  show N (4 + 1) (2, 2, 2, 0) = 0
  rw [tr_s2220]
  norm_num [b4_s1220, b4_s2120, b4_s2210, b4_s2220]

theorem b5_s2221 : N 5 (2, 2, 2, 1) = 0 := by
  show N (4 + 1) (2, 2, 2, 1) = 0
  rw [tr_s2221]
  norm_num [b4_s1221, b4_s2121, b4_s2211, b4_s2220, b4_s2221]

theorem b5_s2222 : N 5 (2, 2, 2, 2) = 0 := by
  show N (4 + 1) (2, 2, 2, 2) = 0
  rw [tr_s2222]
  norm_num [b4_s1222, b4_s2122, b4_s2212, b4_s2221, b4_s2222]

theorem closed_all (n : ℕ) (hn : 5 ≤ n) :
    (N n (0, 0, 0, 0) : ℚ) = 0 ∧
    (N n (0, 0, 0, 1) : ℚ) = 0 ∧
    (N n (0, 0, 0, 2) : ℚ) = 0 ∧
    (N n (0, 0, 1, 0) : ℚ) = 0 ∧
    (N n (0, 0, 1, 1) : ℚ) = 0 ∧
    (N n (0, 0, 1, 2) : ℚ) = 0 ∧
    (N n (0, 0, 2, 0) : ℚ) = 0 ∧
    (N n (0, 0, 2, 1) : ℚ) = 0 ∧
    (N n (0, 0, 2, 2) : ℚ) = 0 ∧
    (N n (0, 1, 0, 0) : ℚ) = 0 ∧
    (N n (0, 1, 0, 1) : ℚ) = 0 ∧
    (N n (0, 1, 0, 2) : ℚ) = 0 ∧
    (N n (0, 1, 1, 0) : ℚ) = 0 ∧
    (N n (0, 1, 1, 1) : ℚ) = 0 ∧
    (N n (0, 1, 1, 2) : ℚ) = 0 ∧
    (N n (0, 1, 2, 0) : ℚ) = 0 ∧
    (N n (0, 1, 2, 1) : ℚ) = 0 ∧
    (N n (0, 1, 2, 2) : ℚ) = 0 ∧
    (N n (0, 2, 0, 0) : ℚ) = 0 ∧
    (N n (0, 2, 0, 1) : ℚ) = 0 ∧
    (N n (0, 2, 0, 2) : ℚ) = 0 ∧
    (N n (0, 2, 1, 0) : ℚ) = 0 ∧
    (N n (0, 2, 1, 1) : ℚ) = 0 ∧
    (N n (0, 2, 1, 2) : ℚ) = 0 ∧
    (N n (0, 2, 2, 0) : ℚ) = 0 ∧
    (N n (0, 2, 2, 1) : ℚ) = 0 ∧
    (N n (0, 2, 2, 2) : ℚ) = 0 ∧
    (N n (1, 0, 0, 0) : ℚ) = 0 ∧
    (N n (1, 0, 0, 1) : ℚ) = 0 ∧
    (N n (1, 0, 0, 2) : ℚ) = 0 ∧
    (N n (1, 0, 1, 0) : ℚ) = 0 ∧
    (N n (1, 0, 1, 1) : ℚ) = 0 ∧
    (N n (1, 0, 1, 2) : ℚ) = 0 ∧
    (N n (1, 0, 2, 0) : ℚ) = 0 ∧
    (N n (1, 0, 2, 1) : ℚ) = 0 ∧
    (N n (1, 0, 2, 2) : ℚ) = 0 ∧
    (N n (1, 1, 0, 0) : ℚ) = 0 ∧
    (N n (1, 1, 0, 1) : ℚ) = 0 ∧
    (N n (1, 1, 0, 2) : ℚ) = 0 ∧
    (N n (1, 1, 1, 0) : ℚ) = 0 ∧
    (N n (1, 1, 1, 1) : ℚ) = 0 ∧
    (N n (1, 1, 1, 2) : ℚ) = (1 : ℚ) * (1) ∧
    (N n (1, 1, 2, 0) : ℚ) = (1 : ℚ) * (1) ∧
    (N n (1, 1, 2, 1) : ℚ) = (-3 : ℚ) * (1) + (1 : ℚ) * ((n : ℚ)) ∧
    (N n (1, 1, 2, 2) : ℚ) = (1 : ℚ) * (1) + (-1 : ℚ) * ((n : ℚ)) + ((1 : ℚ) / 8) * (2 ^ n) ∧
    (N n (1, 2, 0, 0) : ℚ) = (1 : ℚ) * (1) ∧
    (N n (1, 2, 0, 1) : ℚ) = 0 ∧
    (N n (1, 2, 0, 2) : ℚ) = 0 ∧
    (N n (1, 2, 1, 0) : ℚ) = (-2 : ℚ) * (1) + (1 : ℚ) * ((n : ℚ)) ∧
    (N n (1, 2, 1, 1) : ℚ) = (3 : ℚ) * (1) + ((-5 : ℚ) / 2) * ((n : ℚ)) + ((1 : ℚ) / 2) * ((n : ℚ) ^ 2) ∧
    (N n (1, 2, 1, 2) : ℚ) = (-3 : ℚ) * (1) + ((3 : ℚ) / 2) * ((n : ℚ)) + ((-1 : ℚ) / 2) * ((n : ℚ) ^ 2) + ((1 : ℚ) / 4) * (2 ^ n) ∧
    (N n (1, 2, 2, 0) : ℚ) = (-1 : ℚ) * ((n : ℚ)) + ((1 : ℚ) / 4) * (2 ^ n) ∧
    (N n (1, 2, 2, 1) : ℚ) = (1 : ℚ) * (1) + ((3 : ℚ) / 2) * ((n : ℚ)) + ((-1 : ℚ) / 2) * ((n : ℚ) ^ 2) + ((-1 : ℚ) / 2) * (2 ^ n) + ((1 : ℚ) / 8) * ((n : ℚ) * 2 ^ n) ∧
    (N n (1, 2, 2, 2) : ℚ) = ((1 : ℚ) / 2) * (1) + ((-1 : ℚ) / 2) * ((n : ℚ)) + ((1 : ℚ) / 2) * ((n : ℚ) ^ 2) + ((-1 : ℚ) / 8) * (2 ^ n) + ((-1 : ℚ) / 8) * ((n : ℚ) * 2 ^ n) + ((1 : ℚ) / 18) * (3 ^ n) ∧
    (N n (2, 0, 0, 0) : ℚ) = (1 : ℚ) * (1) ∧
    (N n (2, 0, 0, 1) : ℚ) = 0 ∧
    (N n (2, 0, 0, 2) : ℚ) = 0 ∧
    (N n (2, 0, 1, 0) : ℚ) = 0 ∧
    (N n (2, 0, 1, 1) : ℚ) = 0 ∧
    (N n (2, 0, 1, 2) : ℚ) = 0 ∧
    (N n (2, 0, 2, 0) : ℚ) = 0 ∧
    (N n (2, 0, 2, 1) : ℚ) = 0 ∧
    (N n (2, 0, 2, 2) : ℚ) = 0 ∧
    (N n (2, 1, 0, 0) : ℚ) = (-1 : ℚ) * (1) + (1 : ℚ) * ((n : ℚ)) ∧
    (N n (2, 1, 0, 1) : ℚ) = 0 ∧
    (N n (2, 1, 0, 2) : ℚ) = 0 ∧
    (N n (2, 1, 1, 0) : ℚ) = (1 : ℚ) * (1) + ((-3 : ℚ) / 2) * ((n : ℚ)) + ((1 : ℚ) / 2) * ((n : ℚ) ^ 2) ∧
    (N n (2, 1, 1, 1) : ℚ) = (-1 : ℚ) * (1) + ((11 : ℚ) / 6) * ((n : ℚ)) + (-1 : ℚ) * ((n : ℚ) ^ 2) + ((1 : ℚ) / 6) * ((n : ℚ) ^ 3) ∧
    (N n (2, 1, 1, 2) : ℚ) = (-1 : ℚ) * (1) + ((-4 : ℚ) / 3) * ((n : ℚ)) + ((1 : ℚ) / 2) * ((n : ℚ) ^ 2) + ((-1 : ℚ) / 6) * ((n : ℚ) ^ 3) + ((1 : ℚ) / 2) * (2 ^ n) ∧
    (N n (2, 1, 2, 0) : ℚ) = (-2 : ℚ) * (1) + ((1 : ℚ) / 2) * ((n : ℚ)) + ((-1 : ℚ) / 2) * ((n : ℚ) ^ 2) + ((1 : ℚ) / 2) * (2 ^ n) ∧
    (N n (2, 1, 2, 1) : ℚ) = (5 : ℚ) * (1) + ((-11 : ℚ) / 6) * ((n : ℚ)) + (1 : ℚ) * ((n : ℚ) ^ 2) + ((-1 : ℚ) / 6) * ((n : ℚ) ^ 3) + ((-5 : ℚ) / 4) * (2 ^ n) + ((1 : ℚ) / 4) * ((n : ℚ) * 2 ^ n) ∧
    (N n (2, 1, 2, 2) : ℚ) = ((-7 : ℚ) / 4) * (1) + ((11 : ℚ) / 6) * ((n : ℚ)) + ((-1 : ℚ) / 2) * ((n : ℚ) ^ 2) + ((1 : ℚ) / 6) * ((n : ℚ) ^ 3) + ((1 : ℚ) / 8) * (2 ^ n) + ((-1 : ℚ) / 4) * ((n : ℚ) * 2 ^ n) + ((1 : ℚ) / 12) * (3 ^ n) ∧
    (N n (2, 2, 0, 0) : ℚ) = (-1 : ℚ) * (1) + (-1 : ℚ) * ((n : ℚ)) + ((1 : ℚ) / 2) * (2 ^ n) ∧
    (N n (2, 2, 0, 1) : ℚ) = 0 ∧
    (N n (2, 2, 0, 2) : ℚ) = 0 ∧
    (N n (2, 2, 1, 0) : ℚ) = (2 : ℚ) * (1) + ((1 : ℚ) / 2) * ((n : ℚ)) + ((-1 : ℚ) / 2) * ((n : ℚ) ^ 2) + ((-3 : ℚ) / 4) * (2 ^ n) + ((1 : ℚ) / 4) * ((n : ℚ) * 2 ^ n) ∧
    (N n (2, 2, 1, 1) : ℚ) = (-3 : ℚ) * (1) + ((2 : ℚ) / 3) * ((n : ℚ)) + ((1 : ℚ) / 2) * ((n : ℚ) ^ 2) + ((-1 : ℚ) / 6) * ((n : ℚ) ^ 3) + ((7 : ℚ) / 8) * (2 ^ n) + ((-7 : ℚ) / 16) * ((n : ℚ) * 2 ^ n) + ((1 : ℚ) / 16) * ((n : ℚ) ^ 2 * 2 ^ n) ∧
    (N n (2, 2, 1, 2) : ℚ) = ((7 : ℚ) / 2) * (1) + ((-1 : ℚ) / 6) * ((n : ℚ)) + ((1 : ℚ) / 6) * ((n : ℚ) ^ 3) + ((-11 : ℚ) / 8) * (2 ^ n) + ((3 : ℚ) / 16) * ((n : ℚ) * 2 ^ n) + ((-1 : ℚ) / 16) * ((n : ℚ) ^ 2 * 2 ^ n) + ((1 : ℚ) / 6) * (3 ^ n) ∧
    (N n (2, 2, 2, 0) : ℚ) = ((1 : ℚ) / 2) * (1) + ((1 : ℚ) / 2) * ((n : ℚ)) + ((1 : ℚ) / 2) * ((n : ℚ) ^ 2) + ((-1 : ℚ) / 2) * (2 ^ n) + ((-1 : ℚ) / 4) * ((n : ℚ) * 2 ^ n) + ((1 : ℚ) / 6) * (3 ^ n) ∧
    (N n (2, 2, 2, 1) : ℚ) = ((-9 : ℚ) / 4) * (1) + ((-2 : ℚ) / 3) * ((n : ℚ)) + ((-1 : ℚ) / 2) * ((n : ℚ) ^ 2) + ((1 : ℚ) / 6) * ((n : ℚ) ^ 3) + ((11 : ℚ) / 8) * (2 ^ n) + ((1 : ℚ) / 16) * ((n : ℚ) * 2 ^ n) + ((-1 : ℚ) / 16) * ((n : ℚ) ^ 2 * 2 ^ n) + ((-11 : ℚ) / 36) * (3 ^ n) + ((1 : ℚ) / 18) * ((n : ℚ) * 3 ^ n) ∧
    (N n (2, 2, 2, 2) : ℚ) = ((-1 : ℚ) / 6) * (1) + ((-1 : ℚ) / 3) * ((n : ℚ)) + ((-1 : ℚ) / 6) * ((n : ℚ) ^ 3) + ((1 : ℚ) / 4) * (2 ^ n) + ((3 : ℚ) / 16) * ((n : ℚ) * 2 ^ n) + ((1 : ℚ) / 16) * ((n : ℚ) ^ 2 * 2 ^ n) + ((-1 : ℚ) / 6) * (3 ^ n) + ((-1 : ℚ) / 18) * ((n : ℚ) * 3 ^ n) + ((1 : ℚ) / 24) * (4 ^ n) := by
  induction n, hn using Nat.le_induction with
  | base =>
    simp only [b5_s0000, b5_s0001, b5_s0002, b5_s0010, b5_s0011, b5_s0012, b5_s0020, b5_s0021, b5_s0022, b5_s0100, b5_s0101, b5_s0102, b5_s0110, b5_s0111, b5_s0112, b5_s0120, b5_s0121, b5_s0122, b5_s0200, b5_s0201, b5_s0202, b5_s0210, b5_s0211, b5_s0212, b5_s0220, b5_s0221, b5_s0222, b5_s1000, b5_s1001, b5_s1002, b5_s1010, b5_s1011, b5_s1012, b5_s1020, b5_s1021, b5_s1022, b5_s1100, b5_s1101, b5_s1102, b5_s1110, b5_s1111, b5_s1112, b5_s1120, b5_s1121, b5_s1122, b5_s1200, b5_s1201, b5_s1202, b5_s1210, b5_s1211, b5_s1212, b5_s1220, b5_s1221, b5_s1222, b5_s2000, b5_s2001, b5_s2002, b5_s2010, b5_s2011, b5_s2012, b5_s2020, b5_s2021, b5_s2022, b5_s2100, b5_s2101, b5_s2102, b5_s2110, b5_s2111, b5_s2112, b5_s2120, b5_s2121, b5_s2122, b5_s2200, b5_s2201, b5_s2202, b5_s2210, b5_s2211, b5_s2212, b5_s2220, b5_s2221, b5_s2222]
    norm_num
  | succ n hn ih =>
    obtain ⟨hs0000, hs0001, hs0002, hs0010, hs0011, hs0012, hs0020, hs0021, hs0022, hs0100, hs0101, hs0102, hs0110, hs0111, hs0112, hs0120, hs0121, hs0122, hs0200, hs0201, hs0202, hs0210, hs0211, hs0212, hs0220, hs0221, hs0222, hs1000, hs1001, hs1002, hs1010, hs1011, hs1012, hs1020, hs1021, hs1022, hs1100, hs1101, hs1102, hs1110, hs1111, hs1112, hs1120, hs1121, hs1122, hs1200, hs1201, hs1202, hs1210, hs1211, hs1212, hs1220, hs1221, hs1222, hs2000, hs2001, hs2002, hs2010, hs2011, hs2012, hs2020, hs2021, hs2022, hs2100, hs2101, hs2102, hs2110, hs2111, hs2112, hs2120, hs2121, hs2122, hs2200, hs2201, hs2202, hs2210, hs2211, hs2212, hs2220, hs2221, hs2222⟩ := ih
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [tr_s0000]
      simp
    · rw [tr_s0001]
      simp
    · rw [tr_s0002]
      simp
    · rw [tr_s0010]
      simp
    · rw [tr_s0011]
      linear_combination hs0010
    · rw [tr_s0012]
      push_cast
      linear_combination hs0011 + hs0012
    · rw [tr_s0020]
      simp
    · rw [tr_s0021]
      linear_combination hs0020
    · rw [tr_s0022]
      push_cast
      linear_combination hs0021 + hs0022
    · rw [tr_s0100]
      simp
    · rw [tr_s0101]
      simp
    · rw [tr_s0102]
      simp
    · rw [tr_s0110]
      linear_combination hs0100
    · rw [tr_s0111]
      push_cast
      linear_combination hs0101 + hs0110
    · rw [tr_s0112]
      push_cast
      linear_combination hs0102 + hs0111 + hs0112
    · rw [tr_s0120]
      push_cast
      linear_combination hs0110 + hs0120
    · rw [tr_s0121]
      push_cast
      linear_combination hs0111 + hs0120 + hs0121
    · rw [tr_s0122]
      push_cast
      linear_combination hs0112 + hs0121 + 2 * hs0122
    · rw [tr_s0200]
      simp
    · rw [tr_s0201]
      simp
    · rw [tr_s0202]
      simp
    · rw [tr_s0210]
      linear_combination hs0200
    · rw [tr_s0211]
      push_cast
      linear_combination hs0201 + hs0210
    · rw [tr_s0212]
      push_cast
      linear_combination hs0202 + hs0211 + hs0212
    · rw [tr_s0220]
      push_cast
      linear_combination hs0210 + hs0220
    · rw [tr_s0221]
      push_cast
      linear_combination hs0211 + hs0220 + hs0221
    · rw [tr_s0222]
      push_cast
      linear_combination hs0212 + hs0221 + 2 * hs0222
    · rw [tr_s1000]
      linear_combination hs0000
    · rw [tr_s1001]
      linear_combination hs0001
    · rw [tr_s1002]
      linear_combination hs0002
    · rw [tr_s1010]
      linear_combination hs0010
    · rw [tr_s1011]
      push_cast
      linear_combination hs0011 + hs1010
    · rw [tr_s1012]
      push_cast
      linear_combination hs0012 + hs1011 + hs1012
    · rw [tr_s1020]
      linear_combination hs0020
    · rw [tr_s1021]
      push_cast
      linear_combination hs0021 + hs1020
    · rw [tr_s1022]
      push_cast
      linear_combination hs0022 + hs1021 + hs1022
    · rw [tr_s1100]
      push_cast
      linear_combination hs0100 + hs1000
    · rw [tr_s1101]
      push_cast
      linear_combination hs0101 + hs1001
    · rw [tr_s1102]
      push_cast
      linear_combination hs0102 + hs1002
    · rw [tr_s1110]
      push_cast
      linear_combination hs0110 + hs1010 + hs1100
    · rw [tr_s1111]
      push_cast
      linear_combination hs0111 + hs1011 + hs1101 + hs1110
    · rw [tr_s1112]
      push_cast
      linear_combination hs0112 + hs1012 + hs1102 + hs1111 + hs1112
    · rw [tr_s1120]
      push_cast
      linear_combination hs0120 + hs1020 + hs1110 + hs1120
    · rw [tr_s1121]
      push_cast
      linear_combination hs0121 + hs1021 + hs1111 + hs1120 + hs1121
    · rw [tr_s1122]
      push_cast
      linear_combination hs0122 + hs1022 + hs1112 + hs1121 + 2 * hs1122
    · rw [tr_s1200]
      push_cast
      linear_combination hs0200 + hs1100 + hs1200
    · rw [tr_s1201]
      push_cast
      linear_combination hs0201 + hs1101 + hs1201
    · rw [tr_s1202]
      push_cast
      linear_combination hs0202 + hs1102 + hs1202
    · rw [tr_s1210]
      push_cast
      linear_combination hs0210 + hs1110 + hs1200 + hs1210
    · rw [tr_s1211]
      push_cast
      linear_combination hs0211 + hs1111 + hs1201 + hs1210 + hs1211
    · rw [tr_s1212]
      push_cast
      linear_combination hs0212 + hs1112 + hs1202 + hs1211 + 2 * hs1212
    · rw [tr_s1220]
      push_cast
      linear_combination hs0220 + hs1120 + hs1210 + 2 * hs1220
    · rw [tr_s1221]
      push_cast
      linear_combination hs0221 + hs1121 + hs1211 + hs1220 + 2 * hs1221
    · rw [tr_s1222]
      push_cast
      linear_combination hs0222 + hs1122 + hs1212 + hs1221 + 3 * hs1222
    · rw [tr_s2000]
      push_cast
      linear_combination hs1000 + hs2000
    · rw [tr_s2001]
      push_cast
      linear_combination hs1001 + hs2001
    · rw [tr_s2002]
      push_cast
      linear_combination hs1002 + hs2002
    · rw [tr_s2010]
      push_cast
      linear_combination hs1010 + hs2010
    · rw [tr_s2011]
      push_cast
      linear_combination hs1011 + hs2010 + hs2011
    · rw [tr_s2012]
      push_cast
      linear_combination hs1012 + hs2011 + 2 * hs2012
    · rw [tr_s2020]
      push_cast
      linear_combination hs1020 + hs2020
    · rw [tr_s2021]
      push_cast
      linear_combination hs1021 + hs2020 + hs2021
    · rw [tr_s2022]
      push_cast
      linear_combination hs1022 + hs2021 + 2 * hs2022
    · rw [tr_s2100]
      push_cast
      linear_combination hs1100 + hs2000 + hs2100
    · rw [tr_s2101]
      push_cast
      linear_combination hs1101 + hs2001 + hs2101
    · rw [tr_s2102]
      push_cast
      linear_combination hs1102 + hs2002 + hs2102
    · rw [tr_s2110]
      push_cast
      linear_combination hs1110 + hs2010 + hs2100 + hs2110
    · rw [tr_s2111]
      push_cast
      linear_combination hs1111 + hs2011 + hs2101 + hs2110 + hs2111
    · rw [tr_s2112]
      push_cast
      linear_combination hs1112 + hs2012 + hs2102 + hs2111 + 2 * hs2112
    · rw [tr_s2120]
      push_cast
      linear_combination hs1120 + hs2020 + hs2110 + 2 * hs2120
    · rw [tr_s2121]
      push_cast
      linear_combination hs1121 + hs2021 + hs2111 + hs2120 + 2 * hs2121
    · rw [tr_s2122]
      push_cast
      linear_combination hs1122 + hs2022 + hs2112 + hs2121 + 3 * hs2122
    · rw [tr_s2200]
      push_cast
      linear_combination hs1200 + hs2100 + 2 * hs2200
    · rw [tr_s2201]
      push_cast
      linear_combination hs1201 + hs2101 + 2 * hs2201
    · rw [tr_s2202]
      push_cast
      linear_combination hs1202 + hs2102 + 2 * hs2202
    · rw [tr_s2210]
      push_cast
      linear_combination hs1210 + hs2110 + hs2200 + 2 * hs2210
    · rw [tr_s2211]
      push_cast
      linear_combination hs1211 + hs2111 + hs2201 + hs2210 + 2 * hs2211
    · rw [tr_s2212]
      push_cast
      linear_combination hs1212 + hs2112 + hs2202 + hs2211 + 3 * hs2212
    · rw [tr_s2220]
      push_cast
      linear_combination hs1220 + hs2120 + hs2210 + 3 * hs2220
    · rw [tr_s2221]
      push_cast
      linear_combination hs1221 + hs2121 + hs2211 + hs2220 + 3 * hs2221
    · rw [tr_s2222]
      push_cast
      linear_combination hs1222 + hs2122 + hs2212 + hs2221 + 4 * hs2222

theorem a_closed (n : ℕ) (hn : 5 ≤ n) : (a n : ℚ) = ((1 : ℚ) / 3) * (1) + ((-5 : ℚ) / 6) * ((n : ℚ)) + ((1 : ℚ) / 2) * ((n : ℚ) ^ 2) + ((-1 : ℚ) / 6) * ((n : ℚ) ^ 3) + ((1 : ℚ) / 4) * (2 ^ n) + ((-1 : ℚ) / 16) * ((n : ℚ) * 2 ^ n) + ((1 : ℚ) / 16) * ((n : ℚ) ^ 2 * 2 ^ n) + ((-1 : ℚ) / 18) * ((n : ℚ) * 3 ^ n) + ((1 : ℚ) / 24) * (4 ^ n) := by
  rw [a_eq]
  simp only [T, sum_product, sum_range_succ, sum_range_zero]
  norm_num [good]
  obtain ⟨hs0000, -, hs0002, -, -, -, hs0020, -, hs0022, -, -, -, -, -, -, -, -, -, hs0200, -, hs0202, -, -, -, hs0220, -, hs0222, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hs2000, -, hs2002, -, -, -, hs2020, -, hs2022, -, -, -, -, -, -, -, -, -, hs2200, -, hs2202, -, -, -, hs2220, -, hs2222⟩ := closed_all n hn
  linear_combination hs0000 + hs0002 + hs0020 + hs0022 + hs0200 + hs0202 + hs0220 + hs0222 + hs2000 + hs2002 + hs2020 + hs2022 + hs2200 + hs2202 + hs2220 + hs2222


end OMAA278989Helpers

open OMAA278989Helpers OMA.S_oeis_a278989 in
theorem OMA.solution : type_of% @OMA.S_oeis_a278989.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 15 := ⟨n - 15, by omega⟩
  rw [show m + 15 - 1 = m + 14 by omega,
    show m + 15 - 2 = m + 13 by omega,
    show m + 15 - 3 = m + 12 by omega,
    show m + 15 - 4 = m + 11 by omega,
    show m + 15 - 5 = m + 10 by omega,
    show m + 15 - 6 = m + 9 by omega,
    show m + 15 - 7 = m + 8 by omega,
    show m + 15 - 8 = m + 7 by omega,
    show m + 15 - 9 = m + 6 by omega,
    show m + 15 - 10 = m + 5 by omega]
  have q0 := a_closed (m + 15) (by omega)
  have q1 := a_closed (m + 14) (by omega)
  have q2 := a_closed (m + 13) (by omega)
  have q3 := a_closed (m + 12) (by omega)
  have q4 := a_closed (m + 11) (by omega)
  have q5 := a_closed (m + 10) (by omega)
  have q6 := a_closed (m + 9) (by omega)
  have q7 := a_closed (m + 8) (by omega)
  have q8 := a_closed (m + 7) (by omega)
  have q9 := a_closed (m + 6) (by omega)
  have q10 := a_closed (m + 5) (by omega)
  push_cast at q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10
  have h : ((a (m + 15) : ℤ) : ℚ) = ((20 * a (m + 14) - 175 * a (m + 13) + 882 * a (m + 12) - 2835 * a (m + 11) + 6072 * a (m + 10) - 8777 * a (m + 9) + 8458 * a (m + 8) - 5204 * a (m + 7) + 1848 * a (m + 6) - 288 * a (m + 5) : ℤ) : ℚ) := by
    push_cast
    linear_combination q0 - 20 * q1 + 175 * q2 - 882 * q3 + 2835 * q4 - 6072 * q5 + 8777 * q6 - 8458 * q7 + 5204 * q8 - 1848 * q9 + 288 * q10
  exact_mod_cast h
