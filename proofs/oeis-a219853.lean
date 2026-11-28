import OMAStatements.S_oeis_a219853
import Mathlib

open OMA.S_oeis_a219853

namespace P219853

def Tv (k : ℕ) (W : List (States × ℤ)) : ℤ := (W.map (fun p => p.2 * tails k p.1)).sum

def ins (x : States × ℤ) : List (States × ℤ) → List (States × ℤ)
  | [] => [x]
  | y :: L => if y.1 = x.1 then (y.1, y.2 + x.2) :: L else y :: ins x L

def mrg : List (States × ℤ) → List (States × ℤ)
  | [] => []
  | x :: L => ins x (mrg L)

def expand (W : List (States × ℤ)) : List (States × ℤ) :=
  W.flatMap (fun p => (List.finRange 9).map (fun d => (advance p.1 d, p.2)))

def stp (W : List (States × ℤ)) : List (States × ℤ) := mrg (expand W)

theorem Tv_ins (k : ℕ) (x : States × ℤ) (L : List (States × ℤ)) :
    Tv k (ins x L) = x.2 * tails k x.1 + Tv k L := by
  induction L with
  | nil => simp [ins, Tv]
  | cons y L ih =>
    unfold ins
    split_ifs with h
    · simp only [Tv, List.map_cons, List.sum_cons] at *
      rw [← h]; ring
    · simp only [Tv, List.map_cons, List.sum_cons] at *
      rw [ih]; ring

theorem Tv_mrg (k : ℕ) (L : List (States × ℤ)) : Tv k (mrg L) = Tv k L := by
  induction L with
  | nil => rfl
  | cons x L ih =>
    simp only [mrg, Tv_ins, ih]
    simp only [Tv, List.map_cons, List.sum_cons]

theorem Tv_expand (k : ℕ) (W : List (States × ℤ)) : Tv (k + 1) W = Tv k (expand W) := by
  induction W with
  | nil => rfl
  | cons p W ih =>
    simp only [Tv, expand, List.flatMap_cons, List.map_cons, List.sum_cons, List.map_append,
      List.sum_append] at *
    rw [ih]
    congr 1
    simp only [tails, Fin.sum_univ_def, List.map_map, Function.comp_def, ← List.sum_map_mul_left]

theorem Tv_stp (k : ℕ) (W : List (States × ℤ)) : Tv (k + 1) W = Tv k (stp W) := by
  rw [Tv_expand, stp, Tv_mrg]

def F0 (W : List (States × ℤ)) : ℤ := (W.map (fun p => p.2 * finalCount p.1)).sum

theorem Tv_iter (n : ℕ) (W : List (States × ℤ)) : Tv n W = F0 (stp^[n] W) := by
  induction n generalizing W with
  | zero => rfl
  | succ n ih => rw [Tv_stp, ih, Function.iterate_succ_apply]

theorem seq_eq (n : ℕ) : sequence (n + 1) = F0 (stp^[n] [(initial, 1)]) := by
  rw [← Tv_iter]
  simp only [Tv, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero]
  rfl

set_option maxHeartbeats 400000000 in
theorem vals : F0 (stp^[3] [(initial, 1)]) = 33 ∧ F0 (stp^[4] [(initial, 1)]) = 56 ∧
    F0 (stp^[5] [(initial, 1)]) = 86 ∧ F0 (stp^[6] [(initial, 1)]) = 125 := by
  decide +kernel

end P219853

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a219853.main) := by
  intro h
  have h1 := h.2 1
  rw [show 1 + 6 = 6 + 1 by rfl, show 1 + 5 = 5 + 1 by rfl, show 1 + 4 = 4 + 1 by rfl,
    show 1 + 3 = 3 + 1 by rfl, P219853.seq_eq, P219853.seq_eq, P219853.seq_eq, P219853.seq_eq] at h1
  obtain ⟨v3, v4, v5, v6⟩ := P219853.vals
  rw [v3, v4, v5, v6] at h1
  norm_num at h1
