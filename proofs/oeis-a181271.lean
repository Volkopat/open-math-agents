import OMAStatements.S_oeis_a181271
import Mathlib

open OMA.S_oeis_a181271

namespace P181271

def adv (v : List ℤ) : List ℤ :=
  (List.finRange 82).map (fun s => advance (fun t => v.getD t.val 0) s)

def cv : ℕ → List ℤ
  | 0 => (List.finRange 82).map finalCount
  | n + 1 => adv (cv n)

theorem getD_fr (f : State → ℤ) (s : State) : ((List.finRange 82).map f).getD s.val 0 = f s := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

theorem comp_eq : ∀ n (s : State), completions n s = (cv n).getD s.val 0
  | 0, s => by simp only [cv, getD_fr]; rfl
  | n + 1, s => by
    have ih := comp_eq n
    show advance (completions n) s = _
    rw [show completions n = fun t => (cv n).getD t.val 0 from funext ih]
    simp only [cv, adv, getD_fr]

theorem nv_lin (v1 v2 v3 v4 v5 v6 v7 : State → ℤ) (s : State) (c : Fin 8) :
    nextValue (fun t => 14 * v1 t - 36 * v2 t - 216 * v3 t + 1056 * v4 t - 384 * v5 t
      - 3584 * v6 t + 4096 * v7 t) s c =
    14 * nextValue v1 s c - 36 * nextValue v2 s c - 216 * nextValue v3 s c + 1056 * nextValue v4 s c
      - 384 * nextValue v5 s c - 3584 * nextValue v6 s c + 4096 * nextValue v7 s c := by
  unfold nextValue
  cases step s c <;> simp

theorem adv_lin (v1 v2 v3 v4 v5 v6 v7 : State → ℤ) (s : State) :
    advance (fun t => 14 * v1 t - 36 * v2 t - 216 * v3 t + 1056 * v4 t - 384 * v5 t
      - 3584 * v6 t + 4096 * v7 t) s =
    14 * advance v1 s - 36 * advance v2 s - 216 * advance v3 s + 1056 * advance v4 s
      - 384 * advance v5 s - 3584 * advance v6 s + 4096 * advance v7 s := by
  simp only [advance, nv_lin, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

def baseOK : Bool :=
  let a := cv 10
  let b := cv 9
  let c := cv 8
  let d := cv 7
  let e := cv 6
  let f := cv 5
  let g := cv 4
  let h := cv 3
  (List.range 82).all (fun i => a.getD i 0 == 14 * b.getD i 0 - 36 * c.getD i 0 - 216 * d.getD i 0
    + 1056 * e.getD i 0 - 384 * f.getD i 0 - 3584 * g.getD i 0 + 4096 * h.getD i 0)

set_option maxHeartbeats 400000000 in
theorem base_ok : baseOK = true := by decide +kernel

theorem rec_all : ∀ k (s : State), completions (k + 10) s =
    14 * completions (k + 9) s - 36 * completions (k + 8) s - 216 * completions (k + 7) s
      + 1056 * completions (k + 6) s - 384 * completions (k + 5) s - 3584 * completions (k + 4) s
      + 4096 * completions (k + 3) s := by
  intro k
  induction k with
  | zero =>
    intro s
    have h := List.all_eq_true.mp base_ok s.val (by simp)
    simp only [comp_eq]
    simpa using h
  | succ k ih =>
    intro s
    show advance (completions (k + 10)) s = 14 * advance (completions (k + 9)) s
      - 36 * advance (completions (k + 8)) s - 216 * advance (completions (k + 7)) s
      + 1056 * advance (completions (k + 6)) s - 384 * advance (completions (k + 5)) s
      - 3584 * advance (completions (k + 4)) s + 4096 * advance (completions (k + 3)) s
    rw [show completions (k + 10) = _ from funext ih, adv_lin]

end P181271

set_option maxHeartbeats 400000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a181271.main := by
  refine ⟨fun n => ?_, fun k => P181271.rec_all k 0⟩
  rcases Nat.lt_or_ge n 10 with hn | hn
  · simp only [lag, OMA.S_oeis_a181271.sequence, P181271.comp_eq]
    interval_cases n <;> decide +kernel
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 10 := ⟨n - 10, by omega⟩
    have hr := P181271.rec_all k 0
    have hz : numerator (k + 10) = 0 := by
      unfold numerator
      split_ifs <;> first | omega | rfl
    simp only [lag, show 0 ≤ k + 10 by omega, show 1 ≤ k + 10 by omega, show 2 ≤ k + 10 by omega,
      show 3 ≤ k + 10 by omega, show 4 ≤ k + 10 by omega, show 5 ≤ k + 10 by omega,
      show 6 ≤ k + 10 by omega, show 7 ≤ k + 10 by omega, if_true, Nat.sub_zero,
      show k + 10 - 1 = k + 9 by omega, show k + 10 - 2 = k + 8 by omega,
      show k + 10 - 3 = k + 7 by omega, show k + 10 - 4 = k + 6 by omega,
      show k + 10 - 5 = k + 5 by omega, show k + 10 - 6 = k + 4 by omega,
      show k + 10 - 7 = k + 3 by omega]
    rw [hz]
    simp only [OMA.S_oeis_a181271.sequence]
    linarith
