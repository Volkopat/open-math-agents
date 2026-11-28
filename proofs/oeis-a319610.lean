import OMAStatements.S_oeis_a319610
import Mathlib

open OMA.S_oeis_a319610
open PowerSeries

theorem state_succ (t : ℕ) (i : ℤ) :
    state (t + 1) i = eca 30 (state t (i - 1)) (state t i) (state t (i + 1)) := rfl

theorem outside : ∀ t : ℕ, ∀ i : ℤ, (i < -(t : ℤ) ∨ (t : ℤ) < i) → state t i = false := by
  intro t
  induction t with
  | zero =>
    intro i h
    simp only [state, decide_eq_false_iff_not]
    push_cast at h
    omega
  | succ t ih =>
    intro i h
    rw [state_succ]
    push_cast at h
    rw [ih (i - 1) (by omega), ih i (by omega), ih (i + 1) (by omega)]
    decide

def cell (l : List Bool) (j : ℤ) : Bool := if j < 0 then false else l.getD j.toNat false

def stepF (l : List Bool) : List Bool :=
  (List.range 29).map fun k : ℕ => eca 30 (cell l ((k : ℤ) - 2)) (cell l ((k : ℤ) - 1)) (cell l k)

def v0 : List Bool := (List.range 29).map fun k => decide (k = 0)

def vec (t : ℕ) : List Bool := stepF^[t] v0

theorem get_stepF (l : List Bool) (j : ℤ) (h0 : 0 ≤ j) (h : j < 29) :
    cell (stepF l) j = eca 30 (cell l (j - 2)) (cell l (j - 1)) (cell l j) := by
  have hj : j.toNat < 29 := by omega
  rw [cell, if_neg (show ¬ j < 0 by omega)]
  simp only [stepF, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj,
    Option.map_some, Option.getD_some, Int.toNat_of_nonneg h0]

theorem W_eq : ∀ t : ℕ, ∀ j : ℤ, j < 29 → state t (-(t : ℤ) + j) = cell (vec t) j := by
  intro t
  induction t with
  | zero =>
    intro j hj
    by_cases h0 : j < 0
    · rw [outside 0 _ (by left; push_cast; omega)]; simp [cell, h0]
    · simp only [vec, Function.iterate_zero, id, cell, h0, if_false, v0, state]
      rw [List.getD_eq_getElem _ _ (by simp; omega)]
      simp only [List.getElem_map, List.getElem_range]
      by_cases hz : j = 0
      · subst hz; simp
      · have : j.toNat ≠ 0 := by omega
        simp [hz, this]
  | succ t ih =>
    intro j hj
    by_cases h0 : j < 0
    · rw [outside (t + 1) _ (by left; push_cast; omega)]; simp [cell, h0]
    · rw [vec, Function.iterate_succ_apply', ← vec, get_stepF _ _ (by omega) hj,
        ← ih (j - 2) (by omega), ← ih (j - 1) (by omega), ← ih j hj, state_succ]
      have e1 : -((t + 1 : ℕ) : ℤ) + j - 1 = -(t : ℤ) + (j - 2) := by push_cast; ring
      have e2 : -((t + 1 : ℕ) : ℤ) + j = -(t : ℤ) + (j - 1) := by push_cast; ring
      have e3 : -((t + 1 : ℕ) : ℤ) + j + 1 = -(t : ℤ) + j := by push_cast; ring
      rw [e1, e3, e2]

theorem period : vec 35 = vec 31 := by decide +kernel

theorem vec_red (t : ℕ) (h : 35 ≤ t) : vec t = vec (t - 4) := by
  obtain ⟨m, rfl⟩ : ∃ m, t = m + 35 := ⟨t - 35, by omega⟩
  rw [show m + 35 - 4 = m + 31 by omega, vec, vec, Function.iterate_add_apply,
    Function.iterate_add_apply, ← vec, ← vec, period]

def runList (v : Bool) (l : List Bool) (L : ℕ) : Prop :=
  ∃ j < 29, j + L < 29 ∧ (∀ k < L, cell l ((j : ℤ) + k) = v) ∧
    cell l ((j : ℤ) - 1) = !v ∧ cell l ((j : ℤ) + L) = !v

theorem run_of_list (v : Bool) (t L : ℕ) (hL : 1 ≤ L) (h : runList v (vec t) L) : IsRun v t L := by
  obtain ⟨j, -, hjL, hk, h1, h2⟩ := h
  refine ⟨hL, -(t : ℤ) + j, ?_, ?_, ?_⟩
  · intro k hk'
    rw [show -(t : ℤ) + j + k = -(t : ℤ) + ((j : ℤ) + k) by ring, W_eq t _ (by omega)]
    exact hk k hk'
  · rw [show -(t : ℤ) + j - 1 = -(t : ℤ) + ((j : ℤ) - 1) by ring, W_eq t _ (by omega)]
    exact h1
  · rw [show -(t : ℤ) + j + L = -(t : ℤ) + ((j : ℤ) + L) by ring, W_eq t _ (by omega)]
    exact h2

theorem list_of_run (v : Bool) (t L : ℕ) (ht : t ≤ 13) (h : IsRun v t L) : runList v (vec t) L := by
  obtain ⟨hL, i, hk, h1, h2⟩ := h
  have hlo : -(t : ℤ) ≤ i := by
    by_contra hc
    cases v
    · rw [outside t (i - 1) (by left; omega)] at h1; simp at h1
    · have := hk 0 hL
      rw [outside t (i + ((0 : ℕ) : ℤ)) (by left; push_cast; omega)] at this; simp at this
  have hhi : i + L ≤ t + 1 := by
    by_contra hc
    cases v
    · rw [outside t (i + L) (by right; omega)] at h2; simp at h2
    · have := hk (L - 1) (by omega)
      rw [outside t (i + ((L - 1 : ℕ) : ℤ)) (by right; omega)] at this; simp at this
  have hj : (((i + t).toNat : ℕ) : ℤ) = i + t := Int.toNat_of_nonneg (by omega)
  refine ⟨(i + t).toNat, by omega, by omega, ?_, ?_, ?_⟩
  · intro k hk'
    rw [← W_eq t _ (by omega), hj, show -(t : ℤ) + (i + t + k) = i + k by ring]
    exact hk k hk'
  · rw [← W_eq t _ (by omega), hj, show -(t : ℤ) + (i + t - 1) = i - 1 by ring]
    exact h1
  · rw [← W_eq t _ (by omega), hj, show -(t : ℤ) + (i + t + L) = i + L by ring]
    exact h2

theorem sInf_eq_of (S : Set ℕ) (c : ℕ) (hc : c ∈ S) (hlt : ∀ L < c, L ∉ S) : sInf S = c :=
  le_antisymm (Nat.sInf_le hc) (le_csInf ⟨c, hc⟩ fun L hL => not_lt.1 fun h => hlt L h hL)

theorem big : ∀ t, 10 ≤ t → runList false (vec t) 1 := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht
    by_cases h35 : t < 35
    · have key : ∀ s < 35, 10 ≤ s → runList false (vec s) 1 := by
        unfold runList; decide +kernel
      exact key t h35 ht
    · rw [vec_red t (by omega)]
      exact ih (t - 4) (by omega) (by omega)

theorem a_one (t : ℕ) (h : runList false (vec t) 1) : a t = 1 :=
  sInf_eq_of _ 1 (run_of_list false t 1 le_rfl h) (fun L hL hS => by have := hS.1; omega)

theorem a_two (t : ℕ) (ht : t ≤ 13) (h2 : runList false (vec t) 2) (h1 : ¬ runList false (vec t) 1) :
    a t = 2 := by
  refine sInf_eq_of _ 2 (run_of_list false t 2 (by norm_num) h2) ?_
  intro L hL hS
  have := hS.1
  obtain rfl : L = 1 := by omega
  exact h1 (list_of_run false t 1 ht hS)

theorem a_zero (t : ℕ) (ht : t ≤ 13) (h : ∀ L < 29, 1 ≤ L → ¬ runList false (vec t) L) : a t = 0 := by
  have : {L : ℕ | IsRun false t L} = ∅ := by
    ext L
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    intro hS
    have hl := list_of_run false t L ht hS
    obtain ⟨j, -, hjL, -⟩ := hl
    exact h L (by omega) hS.1 (list_of_run false t L ht hS)
  unfold a
  rw [this, Nat.sInf_empty]

theorem vals : a 0 = 0 ∧ a 1 = 0 ∧ a 2 = 2 ∧ a 3 = 1 ∧ a 4 = 2 ∧ a 5 = 1 ∧ a 6 = 2 ∧ a 7 = 1 ∧
    a 8 = 2 ∧ a 9 = 1 := by
  refine ⟨a_zero 0 (by norm_num) ?_, a_zero 1 (by norm_num) ?_, a_two 2 (by norm_num) ?_ ?_,
    a_one 3 ?_, a_two 4 (by norm_num) ?_ ?_, a_one 5 ?_, a_two 6 (by norm_num) ?_ ?_, a_one 7 ?_,
    a_two 8 (by norm_num) ?_ ?_, a_one 9 ?_⟩ <;> unfold runList <;> decide +kernel

theorem a_big (n : ℕ) (h : 10 ≤ n) : a n = 1 := a_one n (big n h)

theorem gf : mk (fun n => (a n : ℤ)) * (1 - X) = X * ((X + X ^ 3 + X ^ 5 + X ^ 7) * (1 - X) + X) := by
  obtain ⟨v0', v1, v2, v3, v4, v5, v6, v7, v8, v9⟩ := vals
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * (1 - X) = F + (-1 : ℤ) • (F * X ^ 1) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : X * ((X + X ^ 3 + X ^ 5 + X ^ 7) * (1 - X) + X) =
      (2 : ℤ) • (X : PowerSeries ℤ) ^ 2 + (-1 : ℤ) • X ^ 3 + (1 : ℤ) • X ^ 4 + (-1 : ℤ) • X ^ 5 +
        (1 : ℤ) • X ^ 6 + (-1 : ℤ) • X ^ 7 + (1 : ℤ) • X ^ 8 + (-1 : ℤ) • X ^ 9 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 10 < n
  · have h1 := a_big n (by omega)
    have h2 := a_big (n - 1) (by omega)
    simp only [show 1 ≤ n by omega, show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega,
      show n ≠ 5 by omega, show n ≠ 6 by omega, show n ≠ 7 by omega, show n ≠ 8 by omega,
      show n ≠ 9 by omega, if_true, if_false, h1, h2]
    norm_num
  · have h10 := a_big 10 le_rfl
    interval_cases n <;> simp [v0', v1, v2, v3, v4, v5, v6, v7, v8, v9, h10]

theorem OMA.solution : type_of% @OMA.S_oeis_a319610.main := ⟨gf, a_big⟩
