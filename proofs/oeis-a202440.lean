import OMAStatements.S_oeis_a202440
import Mathlib

namespace A202440
open OMA.S_oeis_a202440 in
def L0 : List Int := [1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 1]
open OMA.S_oeis_a202440 in
def L1 : List Int := [1, 2, 2, 0, 0, 2, 3, 6, 2, 1, 0, 0, 0, 2, 3, 2, 2, 3, 1, 0, 0, 3, 2, 3, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 2, 3, 0, 0, 1, 3, 2, 2, 3, 2, 0, 0, 0, 1, 2, 6, 3, 2, 0, 0, 2, 2, 1]
open OMA.S_oeis_a202440 in
def L2 : List Int := [1, 3, 3, 0, 0, 5, 5, 16, 3, 1, 0, 0, 0, 3, 3, 3, 3, 3, 1, 0, 0, 8, 3, 5, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 5, 3, 8, 0, 0, 1, 3, 3, 3, 3, 3, 0, 0, 0, 1, 3, 16, 5, 5, 0, 0, 3, 3, 1]
open OMA.S_oeis_a202440 in
def L3 : List Int := [1, 4, 4, 0, 0, 8, 7, 33, 4, 1, 0, 0, 0, 4, 4, 4, 4, 4, 1, 0, 0, 16, 4, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 4, 16, 0, 0, 1, 4, 4, 4, 4, 4, 0, 0, 0, 1, 4, 33, 7, 8, 0, 0, 4, 4, 1]
open OMA.S_oeis_a202440 in
def L4 : List Int := [1, 5, 5, 0, 0, 13, 9, 57, 5, 1, 0, 0, 0, 5, 5, 5, 5, 5, 1, 0, 0, 29, 5, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 13, 5, 29, 0, 0, 1, 5, 5, 5, 5, 5, 0, 0, 0, 1, 5, 57, 9, 13, 0, 0, 5, 5, 1]
open OMA.S_oeis_a202440 in
def L5 : List Int := [1, 6, 6, 0, 0, 18, 11, 90, 6, 1, 0, 0, 0, 6, 6, 6, 6, 6, 1, 0, 0, 47, 6, 19, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 19, 6, 47, 0, 0, 1, 6, 6, 6, 6, 6, 0, 0, 0, 1, 6, 90, 11, 18, 0, 0, 6, 6, 1]
open OMA.S_oeis_a202440 in
def L6 : List Int := [1, 7, 7, 0, 0, 25, 13, 132, 7, 1, 0, 0, 0, 7, 7, 7, 7, 7, 1, 0, 0, 72, 7, 25, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 25, 7, 72, 0, 0, 1, 7, 7, 7, 7, 7, 0, 0, 0, 1, 7, 132, 13, 25, 0, 0, 7, 7, 1]
open OMA.S_oeis_a202440 in
def L7 : List Int := [1, 8, 8, 0, 0, 32, 15, 185, 8, 1, 0, 0, 0, 8, 8, 8, 8, 8, 1, 0, 0, 104, 8, 33, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 33, 8, 104, 0, 0, 1, 8, 8, 8, 8, 8, 0, 0, 0, 1, 8, 185, 15, 32, 0, 0, 8, 8, 1]

open OMA.S_oeis_a202440 in
def T (l : List Int) (s : Fin 64) : Int := l.getD s.val 0

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma c0 : ∀ s : Fin 64, count 0 s = T L0 s := by decide

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma key1 : ∀ s : Fin 64, step (T L0) s = T L1 s := by decide

open OMA.S_oeis_a202440 in
lemma c1 : ∀ s : Fin 64, count 1 s = T L1 s := by
  intro s
  have h : count 0 = T L0 := funext c0
  show step (count 0) s = _
  rw [h]
  exact key1 s

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma key2 : ∀ s : Fin 64, step (T L1) s = T L2 s := by decide

open OMA.S_oeis_a202440 in
lemma c2 : ∀ s : Fin 64, count 2 s = T L2 s := by
  intro s
  have h : count 1 = T L1 := funext c1
  show step (count 1) s = _
  rw [h]
  exact key2 s

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma key3 : ∀ s : Fin 64, step (T L2) s = T L3 s := by decide

open OMA.S_oeis_a202440 in
lemma c3 : ∀ s : Fin 64, count 3 s = T L3 s := by
  intro s
  have h : count 2 = T L2 := funext c2
  show step (count 2) s = _
  rw [h]
  exact key3 s

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma key4 : ∀ s : Fin 64, step (T L3) s = T L4 s := by decide

open OMA.S_oeis_a202440 in
lemma c4 : ∀ s : Fin 64, count 4 s = T L4 s := by
  intro s
  have h : count 3 = T L3 := funext c3
  show step (count 3) s = _
  rw [h]
  exact key4 s

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma key5 : ∀ s : Fin 64, step (T L4) s = T L5 s := by decide

open OMA.S_oeis_a202440 in
lemma c5 : ∀ s : Fin 64, count 5 s = T L5 s := by
  intro s
  have h : count 4 = T L4 := funext c4
  show step (count 4) s = _
  rw [h]
  exact key5 s

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma key6 : ∀ s : Fin 64, step (T L5) s = T L6 s := by decide

open OMA.S_oeis_a202440 in
lemma c6 : ∀ s : Fin 64, count 6 s = T L6 s := by
  intro s
  have h : count 5 = T L5 := funext c5
  show step (count 5) s = _
  rw [h]
  exact key6 s

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma key7 : ∀ s : Fin 64, step (T L6) s = T L7 s := by decide

open OMA.S_oeis_a202440 in
lemma c7 : ∀ s : Fin 64, count 7 s = T L7 s := by
  intro s
  have h : count 6 = T L6 := funext c6
  show step (count 6) s = _
  rw [h]
  exact key7 s

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma sumT1 : ∑ s : Fin 64, T L1 s = 80 := by decide

open OMA.S_oeis_a202440 in
lemma tot1 : total 1 = 80 := by
  unfold total
  have h : count 1 = T L1 := funext c1
  rw [h]
  exact sumT1

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma sumT2 : ∑ s : Fin 64, T L2 s = 138 := by decide

open OMA.S_oeis_a202440 in
lemma tot2 : total 2 = 138 := by
  unfold total
  have h : count 2 = T L2 := funext c2
  rw [h]
  exact sumT2

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma sumT3 : ∑ s : Fin 64, T L3 s = 224 := by decide

open OMA.S_oeis_a202440 in
lemma tot3 : total 3 = 224 := by
  unfold total
  have h : count 3 = T L3 := funext c3
  rw [h]
  exact sumT3

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma sumT4 : ∑ s : Fin 64, T L4 s = 338 := by decide

open OMA.S_oeis_a202440 in
lemma tot4 : total 4 = 338 := by
  unfold total
  have h : count 4 = T L4 := funext c4
  rw [h]
  exact sumT4

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma sumT5 : ∑ s : Fin 64, T L5 s = 484 := by decide

open OMA.S_oeis_a202440 in
lemma tot5 : total 5 = 484 := by
  unfold total
  have h : count 5 = T L5 := funext c5
  rw [h]
  exact sumT5

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma sumT6 : ∑ s : Fin 64, T L6 s = 666 := by decide

open OMA.S_oeis_a202440 in
lemma tot6 : total 6 = 666 := by
  unfold total
  have h : count 6 = T L6 := funext c6
  rw [h]
  exact sumT6

open OMA.S_oeis_a202440 in
def G (n : Nat) (s : Fin 64) : Int :=
  count (n + 5) s - 3 * count (n + 4) s + 2 * count (n + 3) s + 2 * count (n + 2) s
    - 3 * count (n + 1) s + count n s

open OMA.S_oeis_a202440 in
lemma G_succ (n : Nat) (s : Fin 64) : G (n + 1) s = step (G n) s := by
  show step (count (n + 5)) s - 3 * step (count (n + 4)) s + 2 * step (count (n + 3)) s
      + 2 * step (count (n + 2)) s - 3 * step (count (n + 1)) s + step (count n) s
    = step (fun t => count (n + 5) t - 3 * count (n + 4) t + 2 * count (n + 3) t
      + 2 * count (n + 2) t - 3 * count (n + 1) t + count n t) s
  unfold step
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

open OMA.S_oeis_a202440 in
set_option maxRecDepth 100000 in
lemma G_tab : ∀ s : Fin 64, T L7 s - 3 * T L6 s + 2 * T L5 s + 2 * T L4 s - 3 * T L3 s + T L2 s = 0 := by
  decide

open OMA.S_oeis_a202440 in
lemma G_two (s : Fin 64) : G 2 s = 0 := by
  show count 7 s - 3 * count 6 s + 2 * count 5 s + 2 * count 4 s - 3 * count 3 s + count 2 s = 0
  rw [c7 s, c6 s, c5 s, c4 s, c3 s, c2 s]
  exact G_tab s

open OMA.S_oeis_a202440 in
lemma G_all (n : Nat) : ∀ s : Fin 64, G (n + 2) s = 0 := by
  induction n with
  | zero => exact G_two
  | succ n ih =>
    intro s
    have e : G (n + 1 + 2) s = step (G (n + 2)) s := G_succ (n + 2) s
    have z : G (n + 2) = fun _ => 0 := funext ih
    rw [e, z]
    unfold step
    simp

open OMA.S_oeis_a202440 in
lemma tot_rel (n : Nat) :
    total (n + 2 + 5) - 3 * total (n + 2 + 4) + 2 * total (n + 2 + 3) + 2 * total (n + 2 + 2)
      - 3 * total (n + 2 + 1) + total (n + 2) = 0 := by
  have h : ∑ s : Fin 64, G (n + 2) s = 0 := Finset.sum_eq_zero (fun s _ => G_all n s)
  unfold G at h
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at h
  exact h

open OMA.S_oeis_a202440 in
lemma D_all (n : Nat) :
    total (n + 2 + 4) - 4 * total (n + 2 + 3) + 6 * total (n + 2 + 2) - 4 * total (n + 2 + 1)
      + total (n + 2) = 0 := by
  induction n with
  | zero =>
    show total 6 - 4 * total 5 + 6 * total 4 - 4 * total 3 + total 2 = 0
    rw [tot6, tot5, tot4, tot3, tot2]
    rfl
  | succ n ih =>
    have h := tot_rel n
    have e5 : n + 1 + 2 + 4 = n + 2 + 5 := by omega
    have e4 : n + 1 + 2 + 3 = n + 2 + 4 := by omega
    have e3 : n + 1 + 2 + 2 = n + 2 + 3 := by omega
    have e2 : n + 1 + 2 + 1 = n + 2 + 2 := by omega
    have e1 : n + 1 + 2 = n + 2 + 1 := by omega
    rw [e5, e4, e3, e2, e1]
    linarith

end A202440

theorem OMA.solution : type_of% @OMA.S_oeis_a202440.main := by
  constructor
  · intro n
    have h := A202440.D_all n
    show OMA.S_oeis_a202440.total (n + 6) - 4 * OMA.S_oeis_a202440.total (n + 5)
      + 6 * OMA.S_oeis_a202440.total (n + 4) - 4 * OMA.S_oeis_a202440.total (n + 3)
      + OMA.S_oeis_a202440.total (n + 2) = 0
    exact h
  · intro n
    rcases n with _ | _ | _ | _ | _ | _ | m
    · rfl
    · show OMA.S_oeis_a202440.total 1 - 4 * 0 = 80
      rw [A202440.tot1]
      rfl
    · show OMA.S_oeis_a202440.total 2 - 4 * OMA.S_oeis_a202440.total 1 + 6 * 0 = -182
      rw [A202440.tot1, A202440.tot2]
      rfl
    · show OMA.S_oeis_a202440.total 3 - 4 * OMA.S_oeis_a202440.total 2
        + 6 * OMA.S_oeis_a202440.total 1 - 4 * 0 = 152
      rw [A202440.tot1, A202440.tot2, A202440.tot3]
      rfl
    · show OMA.S_oeis_a202440.total 4 - 4 * OMA.S_oeis_a202440.total 3
        + 6 * OMA.S_oeis_a202440.total 2 - 4 * OMA.S_oeis_a202440.total 1 + 0 = -50
      rw [A202440.tot1, A202440.tot2, A202440.tot3, A202440.tot4]
      rfl
    · show OMA.S_oeis_a202440.total 5 - 4 * OMA.S_oeis_a202440.total 4
        + 6 * OMA.S_oeis_a202440.total 3 - 4 * OMA.S_oeis_a202440.total 2
        + OMA.S_oeis_a202440.total 1 = 4
      rw [A202440.tot1, A202440.tot2, A202440.tot3, A202440.tot4, A202440.tot5]
      rfl
    · have h := A202440.D_all m
      show OMA.S_oeis_a202440.total (m + 6) - 4 * OMA.S_oeis_a202440.total (m + 5)
        + 6 * OMA.S_oeis_a202440.total (m + 4) - 4 * OMA.S_oeis_a202440.total (m + 3)
        + OMA.S_oeis_a202440.total (m + 2) = 0
      exact h
