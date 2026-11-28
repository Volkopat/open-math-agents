import OMAStatements.S_oeis_a224013
import Mathlib

-- Proof of the formulas of OEIS A224013 (statement by @ivillar).
-- Idea: the conditions only involve three consecutive lines, so the count is a walk count on pairs of consecutive
-- lines (transfer matrix). The pairs are grouped into 31 classes such that the number of successors in each class
-- depends only on the class (checked by decide); the class counts V n c then satisfy an explicit linear system, from
-- which the recurrence follows by linear algebra, and the g.f. and the closed form follow from the recurrence and
-- initial values.

namespace OMAA224013Helpers

open OMA.S_oeis_a224013

/-- The lines of the array (the states of the transfer matrix are pairs of consecutive lines). -/
abbrev R := Fin 3 → Fin 3

instance (u v w : R) : Decidable (TriOK u v w) := by unfold TriOK; infer_instance

abbrev tri (r s t : R) : Prop := TriOK r s t

instance (u v : R) : Decidable (BlockOK u v) := by unfold BlockOK; infer_instance

abbrev compat (r s : R) : Prop := BlockOK r s

abbrev ok (_r : R) : Prop := True

abbrev ini (_r : R) : Prop := True

abbrev Walk2 {n : ℕ} (x : Fin (n + 2) → R) : Prop :=
  (∀ i, ok (x i)) ∧ (∀ i : Fin (n + 1), compat (x i.castSucc) (x i.succ)) ∧
    ∀ i : Fin n, tri (x i.castSucc.castSucc) (x i.succ.castSucc) (x i.succ.succ)

theorem walk2_cons (n : ℕ) (r : R) (y : Fin (n + 2) → R) :
    Walk2 (Fin.cons r y : Fin (n + 3) → R) ↔ ok r ∧ compat r (y 0) ∧ tri r (y 0) (y 1) ∧ Walk2 y := by
  have e0 : (Fin.cons r y : Fin (n + 3) → R) 0 = r := Fin.cons_zero _ _
  have es : ∀ i : Fin (n + 2), (Fin.cons r y : Fin (n + 3) → R) i.succ = y i :=
    fun i => Fin.cons_succ _ _ i
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_, fun i => ?_, fun i => ?_, fun i => ?_⟩
    · simpa only [e0] using h1 0
    · simpa only [Fin.castSucc_zero, e0, es] using h2 0
    · have a3 := h3 0
      simp only [Fin.castSucc_zero, e0, es, ← Fin.succ_castSucc] at a3
      rw [Fin.succ_zero_eq_one] at a3
      exact a3
    · simpa only [es] using h1 i.succ
    · simpa only [← Fin.succ_castSucc, es] using h2 i.succ
    · simpa only [← Fin.succ_castSucc, es] using h3 i.succ
  · rintro ⟨h1, h2, h3, g1, g2, g3⟩
    refine ⟨fun i => ?_, fun i => ?_, fun i => ?_⟩
    · induction i using Fin.cases with
      | zero => simpa only [e0] using h1
      | succ j => simpa only [es] using g1 j
    · induction i using Fin.cases with
      | zero => simpa only [Fin.castSucc_zero, e0, es] using h2
      | succ j => simpa only [← Fin.succ_castSucc, es] using g2 j
    · induction i using Fin.cases with
      | zero =>
        simp only [Fin.castSucc_zero, e0, es, ← Fin.succ_castSucc]
        rw [Fin.succ_zero_eq_one]
        exact h3
      | succ j => simpa only [← Fin.succ_castSucc, es] using g3 j

theorem walk2_zero (y : Fin 2 → R) : Walk2 y ↔ (ok (y 0) ∧ ok (y 1)) ∧ compat (y 0) (y 1) := by
  constructor
  · rintro ⟨h1, h2, -⟩
    exact ⟨⟨h1 0, h1 1⟩, h2 0⟩
  · rintro ⟨⟨a0, a1⟩, c⟩
    refine ⟨Fin.forall_fin_two.mpr ⟨a0, a1⟩, fun i => ?_, fun i => i.elim0⟩
    have hi : i = 0 := Fin.eq_zero i
    subst hi
    exact c

/-- F2(n, s, t): the number of sequences of n + 2 lines satisfying the conditions, starting with s, t. -/
def F2 (n : ℕ) (s t : R) : ℕ :=
  ∑ y : Fin (n + 2) → R, if Walk2 y ∧ y 0 = s ∧ y 1 = t then 1 else 0

theorem F2_zero (s t : R) : F2 0 s t = if (ok s ∧ ok t) ∧ compat s t then 1 else 0 := by
  unfold F2
  have h : ∀ y : Fin 2 → R, (if Walk2 y ∧ y 0 = s ∧ y 1 = t then 1 else 0) =
      if y = ![s, t] then (if (ok s ∧ ok t) ∧ compat s t then 1 else 0) else 0 := by
    intro y
    by_cases hy : y = ![s, t]
    · have h0 : y 0 = s := by rw [hy]; rfl
      have h1 : y 1 = t := by rw [hy]; rfl
      rw [if_pos hy]
      refine if_congr ⟨fun hh => ?_, fun hh => ⟨?_, h0, h1⟩⟩ rfl rfl
      · have := (walk2_zero y).mp hh.1
        rw [h0, h1] at this
        exact this
      · rw [walk2_zero, h0, h1]
        exact hh
    · rw [if_neg hy, if_neg]
      rintro ⟨-, h0, h1⟩
      apply hy
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [h0]; rfl
      · rw [Subsingleton.elim j 0]
        exact h1
  rw [Finset.sum_congr rfl (fun y _ => h y), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]

theorem F2_succ (n : ℕ) (s t : R) :
    F2 (n + 1) s t = ∑ u : R, if ok s ∧ compat s t ∧ tri s t u then F2 n t u else 0 := by
  have lhs : F2 (n + 1) s t = ∑ y : Fin (n + 2) → R,
      if (ok s ∧ compat s t ∧ tri s t (y 1)) ∧ (Walk2 y ∧ y 0 = t) then 1 else 0 := by
    unfold F2
    rw [← (Fin.consEquiv (fun _ : Fin (n + 3) => R)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have h : ∀ r : R, (if Walk2 ((Fin.consEquiv (fun _ : Fin (n + 3) => R)) (r, y)) ∧
        (Fin.consEquiv (fun _ : Fin (n + 3) => R)) (r, y) 0 = s ∧
        (Fin.consEquiv (fun _ : Fin (n + 3) => R)) (r, y) 1 = t then 1 else 0) =
        if r = s then (if (ok s ∧ compat s t ∧ tri s t (y 1)) ∧ (Walk2 y ∧ y 0 = t) then 1 else 0)
          else 0 := by
      intro r
      have e1 : (Fin.cons r y : Fin (n + 3) → R) 1 = y 0 := by
        rw [← Fin.succ_zero_eq_one, Fin.cons_succ]
      rw [show (Fin.consEquiv (fun _ : Fin (n + 3) => R)) (r, y) = (Fin.cons r y : Fin (n + 3) → R)
        from rfl]
      simp only [walk2_cons, Fin.cons_zero, e1]
      by_cases hr : r = s
      · subst hr
        rw [if_pos rfl]
        refine if_congr ⟨fun hh => ?_, fun hh => ?_⟩ rfl rfl
        · obtain ⟨⟨k1, k2, k3, k4⟩, -, k5⟩ := hh
          rw [k5] at k2 k3
          exact ⟨⟨k1, k2, k3⟩, k4, k5⟩
        · obtain ⟨⟨k1, k2, k3⟩, k4, k5⟩ := hh
          refine ⟨⟨k1, ?_, ?_, k4⟩, rfl, k5⟩
          · rw [k5]; exact k2
          · rw [k5]; exact k3
      · rw [if_neg hr, if_neg (fun hh => hr hh.2.1)]
    rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  rw [lhs]
  unfold F2
  have h2 : ∀ u : R, (if ok s ∧ compat s t ∧ tri s t u then
      ∑ y : Fin (n + 2) → R, (if Walk2 y ∧ y 0 = t ∧ y 1 = u then 1 else 0) else 0) =
      ∑ y : Fin (n + 2) → R, if y 1 = u then
        (if (ok s ∧ compat s t ∧ tri s t (y 1)) ∧ (Walk2 y ∧ y 0 = t) then 1 else 0) else 0 := by
    intro u
    split_ifs with hu
    · apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y 1 = u
      · rw [if_pos hy]
        refine if_congr ⟨fun hh => ⟨?_, hh.1, hh.2.1⟩, fun hh => ⟨hh.2.1, hh.2.2, hy⟩⟩ rfl rfl
        rw [hy]; exact hu
      · rw [if_neg hy, if_neg (fun hh => hy hh.2.2)]
    · symm
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y 1 = u
      · rw [if_pos hy, if_neg]
        intro hh
        apply hu
        rw [← hy]; exact hh.1
      · rw [if_neg hy]
  rw [Finset.sum_congr rfl (fun u _ => h2 u), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

theorem good2_iff (n : ℕ) (x : Fin (n + 2) → R) : Good x ↔ Walk2 x ∧ ini (x 0) := by
  unfold Good
  constructor
  · rintro ⟨h2, h3⟩
    exact ⟨⟨fun _ => trivial, fun i => h2 i.castSucc i.succ (by simp),
      fun i => h3 i.castSucc.castSucc i.succ.castSucc i.succ.succ (by simp) (by simp)⟩, trivial⟩
  · rintro ⟨⟨-, h2, h3⟩, -⟩
    refine ⟨?_, ?_⟩
    · intro i j hij
      have hi : (i : ℕ) < n + 1 := by have := j.isLt; omega
      have e1 : (⟨i, hi⟩ : Fin (n + 1)).castSucc = i := Fin.ext rfl
      have e2 : (⟨i, hi⟩ : Fin (n + 1)).succ = j := Fin.ext (by simp [hij])
      have := h2 ⟨i, hi⟩
      rw [e1, e2] at this
      exact this
    · intro i j l hij hjl
      have hi : (i : ℕ) < n := by have := l.isLt; omega
      have e1 : (⟨i, hi⟩ : Fin n).castSucc.castSucc = i := Fin.ext rfl
      have e2 : (⟨i, hi⟩ : Fin n).succ.castSucc = j := Fin.ext (by simp [hij])
      have e3 : (⟨i, hi⟩ : Fin n).succ.succ = l := Fin.ext (by simp [hjl, hij])
      have := h3 ⟨i, hi⟩
      rw [e1, e2, e3] at this
      exact this

/-- The class table, indexed by the entries of two consecutive lines. -/
def clsT : List (List (List (List (List (List ℕ))))) :=
  [[[[[[0, 1, 2], [3, 4, 5], [6, 7, 8]], [[9, 10, 11], [12, 13, 14], [7, 15, 16]], [[17, 18, 19], [20, 21, 22], [8, 16, 23]]], [[[24, 25, 26], [24, 4, 5], [24, 7, 8]], [[24, 27, 27], [24, 13, 14], [24, 15, 16]], [[24, 27, 27], [24, 21, 22], [24, 16, 23]]], [[[24, 24, 26], [24, 24, 28], [24, 24, 8]], [[24, 24, 27], [24, 24, 29], [24, 24, 16]], [[24, 24, 27], [24, 24, 30], [24, 24, 23]]]], [[[[24, 24, 24], [3, 4, 5], [6, 7, 8]], [[24, 24, 24], [12, 13, 14], [7, 15, 16]], [[24, 24, 24], [20, 21, 22], [8, 16, 23]]], [[[24, 24, 24], [24, 4, 5], [24, 7, 8]], [[24, 24, 24], [24, 13, 14], [24, 15, 16]], [[24, 24, 24], [24, 21, 22], [24, 16, 23]]], [[[24, 24, 24], [24, 24, 28], [24, 24, 8]], [[24, 24, 24], [24, 24, 29], [24, 24, 16]], [[24, 24, 24], [24, 24, 30], [24, 24, 23]]]], [[[[24, 24, 24], [24, 24, 24], [6, 7, 8]], [[24, 24, 24], [24, 24, 24], [7, 15, 16]], [[24, 24, 24], [24, 24, 24], [8, 16, 23]]], [[[24, 24, 24], [24, 24, 24], [24, 7, 8]], [[24, 24, 24], [24, 24, 24], [24, 15, 16]], [[24, 24, 24], [24, 24, 24], [24, 16, 23]]], [[[24, 24, 24], [24, 24, 24], [24, 24, 8]], [[24, 24, 24], [24, 24, 24], [24, 24, 16]], [[24, 24, 24], [24, 24, 24], [24, 24, 23]]]]], [[[[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[9, 10, 11], [12, 13, 14], [7, 15, 16]], [[17, 18, 19], [20, 21, 22], [8, 16, 23]]], [[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 27, 27], [24, 13, 14], [24, 15, 16]], [[24, 27, 27], [24, 21, 22], [24, 16, 23]]], [[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 27], [24, 24, 29], [24, 24, 16]], [[24, 24, 27], [24, 24, 30], [24, 24, 23]]]], [[[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [12, 13, 14], [7, 15, 16]], [[24, 24, 24], [20, 21, 22], [8, 16, 23]]], [[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 13, 14], [24, 15, 16]], [[24, 24, 24], [24, 21, 22], [24, 16, 23]]], [[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 29], [24, 24, 16]], [[24, 24, 24], [24, 24, 30], [24, 24, 23]]]], [[[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [7, 15, 16]], [[24, 24, 24], [24, 24, 24], [8, 16, 23]]], [[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [24, 15, 16]], [[24, 24, 24], [24, 24, 24], [24, 16, 23]]], [[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [24, 24, 16]], [[24, 24, 24], [24, 24, 24], [24, 24, 23]]]]], [[[[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[17, 18, 19], [20, 21, 22], [8, 16, 23]]], [[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 27, 27], [24, 21, 22], [24, 16, 23]]], [[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 27], [24, 24, 30], [24, 24, 23]]]], [[[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [20, 21, 22], [8, 16, 23]]], [[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 21, 22], [24, 16, 23]]], [[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 30], [24, 24, 23]]]], [[[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [8, 16, 23]]], [[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [24, 16, 23]]], [[[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [24, 24, 24]], [[24, 24, 24], [24, 24, 24], [24, 24, 23]]]]]]

/-- The class of a pair of consecutive lines: pairs of the same class have the same number of successors
in each class. -/
def cls2 (s t : R) : ℕ :=
  ((((((clsT).getD (s 0 : ℕ) []).getD (s 1 : ℕ) []).getD (s 2 : ℕ) []).getD (t 0 : ℕ) []).getD (t 1 : ℕ) []).getD (t 2 : ℕ) 0

/-- Mt i j: the number of successors in class j of a pair of class i. -/
def Mt (i j : ℕ) : ℕ :=
  (([[1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 2, 0, 0, 0, 0, 1, 1, 1, 9, 1, 1, 4, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 18, 0, 1, 2, 1, 1, 1],
    [0, 0, 0, 1, 1, 1, 1, 2, 2, 0, 0, 0, 1, 1, 1, 1, 2, 0, 0, 0, 1, 1, 1, 1, 9, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 1, 1, 1, 2, 0, 0, 0, 0, 1, 1, 1, 15, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 21, 0, 0, 0, 1, 1, 1],
    [0, 0, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 18, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 21, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 24, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 0, 0, 0, 1, 1, 1, 15, 0, 0, 4, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 21, 0, 0, 2, 0, 1, 1],
    [0, 0, 0, 0, 0, 0, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 2, 0, 0, 0, 1, 1, 1, 1, 15, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 2, 0, 0, 0, 0, 1, 1, 1, 19, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 23, 0, 0, 0, 0, 1, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 0, 0, 0, 0, 0, 1, 23, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 25, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 1, 18, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 21, 0, 0, 2, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 24, 0, 0, 1, 0, 0, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 1, 1, 1, 21, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 1, 1, 23, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 25, 0, 0, 0, 0, 0, 1],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 26, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 1, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 1, 0, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 9, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 14, 0, 0, 0, 1, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 16, 0, 0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 18, 0, 0, 0, 0, 0, 0]] : List (List ℕ)).getD i []).getD j 0

/-- V n c: the number of walks of n + 2 lines starting with a given pair of lines of class c. -/
def V : ℕ → ℕ → ℕ
  | 0, c => ([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 1, 1, 1, 1, 1, 1] : List ℕ).getD c 0
  | n + 1, 0 => 0 + 1 * V n 0 + 1 * V n 1 + 1 * V n 2 + 1 * V n 3 + 1 * V n 4 + 1 * V n 5 + 1 * V n 6 + 2 * V n 7 + 2 * V n 8 + 1 * V n 9 + 1 * V n 10 + 1 * V n 11 + 1 * V n 12 + 1 * V n 13 + 1 * V n 14 + 1 * V n 15 + 2 * V n 16 + 1 * V n 17 + 1 * V n 18 + 1 * V n 19 + 1 * V n 20 + 1 * V n 21 + 1 * V n 22 + 1 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 1 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 1 * V n 4 + 1 * V n 5 + 0 * V n 6 + 1 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 1 * V n 13 + 1 * V n 14 + 1 * V n 15 + 2 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 1 * V n 21 + 1 * V n 22 + 1 * V n 23 + 9 * V n 24 + 1 * V n 25 + 1 * V n 26 + 4 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 2 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 18 * V n 24 + 0 * V n 25 + 1 * V n 26 + 2 * V n 27 + 1 * V n 28 + 1 * V n 29 + 1 * V n 30
  | n + 1, 3 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 1 * V n 3 + 1 * V n 4 + 1 * V n 5 + 1 * V n 6 + 2 * V n 7 + 2 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 1 * V n 12 + 1 * V n 13 + 1 * V n 14 + 1 * V n 15 + 2 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 1 * V n 20 + 1 * V n 21 + 1 * V n 22 + 1 * V n 23 + 9 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 4 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 1 * V n 4 + 1 * V n 5 + 0 * V n 6 + 1 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 1 * V n 13 + 1 * V n 14 + 1 * V n 15 + 2 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 1 * V n 21 + 1 * V n 22 + 1 * V n 23 + 15 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 5 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 21 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 1 * V n 28 + 1 * V n 29 + 1 * V n 30
  | n + 1, 6 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 1 * V n 6 + 2 * V n 7 + 2 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 1 * V n 15 + 2 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 18 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 7 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 1 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 1 * V n 15 + 2 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 21 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 8 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 24 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 9 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 1 * V n 7 + 1 * V n 8 + 1 * V n 9 + 1 * V n 10 + 1 * V n 11 + 1 * V n 12 + 1 * V n 13 + 1 * V n 14 + 1 * V n 15 + 2 * V n 16 + 1 * V n 17 + 1 * V n 18 + 1 * V n 19 + 1 * V n 20 + 1 * V n 21 + 1 * V n 22 + 1 * V n 23 + 9 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 10 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 1 * V n 13 + 1 * V n 14 + 1 * V n 15 + 2 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 1 * V n 21 + 1 * V n 22 + 1 * V n 23 + 15 * V n 24 + 0 * V n 25 + 0 * V n 26 + 4 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 11 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 21 * V n 24 + 0 * V n 25 + 0 * V n 26 + 2 * V n 27 + 0 * V n 28 + 1 * V n 29 + 1 * V n 30
  | n + 1, 12 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 1 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 1 * V n 12 + 1 * V n 13 + 1 * V n 14 + 1 * V n 15 + 2 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 1 * V n 20 + 1 * V n 21 + 1 * V n 22 + 1 * V n 23 + 15 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 13 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 1 * V n 13 + 1 * V n 14 + 1 * V n 15 + 2 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 1 * V n 21 + 1 * V n 22 + 1 * V n 23 + 19 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 14 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 23 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 1 * V n 29 + 1 * V n 30
  | n + 1, 15 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 1 * V n 15 + 2 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 23 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 16 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 25 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 17 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 1 * V n 17 + 1 * V n 18 + 1 * V n 19 + 1 * V n 20 + 1 * V n 21 + 1 * V n 22 + 1 * V n 23 + 18 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 18 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 1 * V n 21 + 1 * V n 22 + 1 * V n 23 + 21 * V n 24 + 0 * V n 25 + 0 * V n 26 + 2 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 19 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 24 * V n 24 + 0 * V n 25 + 0 * V n 26 + 1 * V n 27 + 0 * V n 28 + 0 * V n 29 + 1 * V n 30
  | n + 1, 20 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 1 * V n 20 + 1 * V n 21 + 1 * V n 22 + 1 * V n 23 + 21 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 21 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 1 * V n 21 + 1 * V n 22 + 1 * V n 23 + 23 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 22 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 25 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 1 * V n 30
  | n + 1, 23 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 1 * V n 23 + 26 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 24 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 0 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 25 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 1 * V n 4 + 1 * V n 5 + 0 * V n 6 + 1 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 3 * V n 24 + 1 * V n 25 + 1 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 26 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 6 * V n 24 + 0 * V n 25 + 1 * V n 26 + 0 * V n 27 + 1 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 27 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 9 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | n + 1, 28 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 1 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 14 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 1 * V n 28 + 1 * V n 29 + 0 * V n 30
  | n + 1, 29 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 1 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 16 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 1 * V n 29 + 0 * V n 30
  | n + 1, 30 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9 + 0 * V n 10 + 0 * V n 11 + 0 * V n 12 + 0 * V n 13 + 0 * V n 14 + 0 * V n 15 + 0 * V n 16 + 0 * V n 17 + 0 * V n 18 + 0 * V n 19 + 0 * V n 20 + 0 * V n 21 + 0 * V n 22 + 0 * V n 23 + 18 * V n 24 + 0 * V n 25 + 0 * V n 26 + 0 * V n 27 + 0 * V n 28 + 0 * V n 29 + 0 * V n 30
  | _ + 1, _ => 0

theorem cls2_lt : ∀ s t : R, cls2 s t < 31 := by decide +kernel

theorem sum_clsf (f : R → ℕ) (hf : ∀ t, f t < 31) (g : ℕ → ℕ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then g (f t) else 0) =
      ∑ c ∈ Finset.range 31, (Finset.univ.filter (fun t : R => f t = c ∧ P t)).card * g c := by
  have h1 : ∀ t : R, (if P t then g (f t) else 0) =
      ∑ c ∈ Finset.range 31, if f t = c ∧ P t then g c else 0 := by
    intro t
    rw [Finset.sum_eq_single (f t)]
    · by_cases hp : P t <;> simp [hp]
    · intro c _ hc
      rw [if_neg]
      exact fun h => hc h.1.symm
    · intro h
      exact absurd (Finset.mem_range.mpr (hf t)) h
  rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  rw [← Finset.sum_filter, Finset.sum_const, smul_eq_mul]

/-- The lines, numbered by their base-3 digits. -/
abbrev E : R ≃ Fin (3 ^ 3) := finFunctionFinEquiv

theorem cntN_0 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 0 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_1 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 1 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_2 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 2 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_3 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 3 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_4 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 4 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_5 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 5 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_6 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 6 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_7 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 7 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_8 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 8 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_9 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 9 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_10 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 10 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_11 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 11 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_12 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 12 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_13 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 13 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_14 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 14 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_15 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 15 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_16 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 16 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_17 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 17 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_18 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 18 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_19 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 19 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cntN_20 : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 = 20 → ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem chunk_lt : ∀ a b : Fin (3 ^ 3), ((a : ℕ) * 27 + (b : ℕ)) / 35 < 21 := by decide +kernel

theorem cntN (a b : Fin (3 ^ 3)) : ∀ c < 31,
    (Finset.univ.filter (fun x : Fin (3 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  have h := chunk_lt a b
  generalize hq : ((a : ℕ) * 27 + (b : ℕ)) / 35 = q at h
  interval_cases q
  · exact cntN_0 a b hq
  · exact cntN_1 a b hq
  · exact cntN_2 a b hq
  · exact cntN_3 a b hq
  · exact cntN_4 a b hq
  · exact cntN_5 a b hq
  · exact cntN_6 a b hq
  · exact cntN_7 a b hq
  · exact cntN_8 a b hq
  · exact cntN_9 a b hq
  · exact cntN_10 a b hq
  · exact cntN_11 a b hq
  · exact cntN_12 a b hq
  · exact cntN_13 a b hq
  · exact cntN_14 a b hq
  · exact cntN_15 a b hq
  · exact cntN_16 a b hq
  · exact cntN_17 a b hq
  · exact cntN_18 a b hq
  · exact cntN_19 a b hq
  · exact cntN_20 a b hq

theorem cnt (s t : R) (c : ℕ) (hc : c < 31) :
    (Finset.univ.filter (fun u : R => cls2 t u = c ∧ (ok s ∧ compat s t ∧ tri s t u))).card =
      Mt (cls2 s t) c := by
  have h := cntN (E s) (E t) c hc
  simp only [Equiv.symm_apply_apply] at h
  rw [← h, Finset.card_filter, Finset.card_filter]
  exact (Equiv.sum_comp E.symm
    (fun u : R => if cls2 t u = c ∧ (ok s ∧ compat s t ∧ tri s t u) then 1 else 0)).symm


theorem cnt0 : ∀ s t : R, (if (ok s ∧ ok t) ∧ compat s t then 1 else 0) = V 0 (cls2 s t) := by
  decide +kernel

theorem tcnt : ∀ c < 31, (∑ s : R, (Finset.univ.filter (fun t : R => cls2 s t = c ∧ ini s)).card) =
    ([1, 1, 1, 2, 4, 4, 3, 12, 18, 2, 2, 2, 4, 8, 8, 12, 36, 3, 3, 3, 6, 12, 12, 27, 513, 1, 2, 15, 2, 4, 6] : List ℕ).getD c 0 := by decide +kernel

theorem step (n : ℕ) : ∀ i < 31, (∑ c ∈ Finset.range 31, Mt i c * V n c) = V (n + 1) i := by
  intro i hi
  interval_cases i <;> (simp only [Finset.sum_range_succ, Finset.sum_range_zero]; rfl)

theorem F2_eq (n : ℕ) : ∀ s t : R, F2 n s t = V n (cls2 s t) := by
  induction n with
  | zero => intro s t; rw [F2_zero]; exact cnt0 s t
  | succ n ih =>
    intro s t
    rw [F2_succ]
    simp only [ih]
    rw [sum_clsf (cls2 t) (cls2_lt t) (V n) (fun u => ok s ∧ compat s t ∧ tri s t u),
      ← step n (cls2 s t) (cls2_lt s t)]
    apply Finset.sum_congr rfl
    intro c hc
    rw [cnt s t c (Finset.mem_range.mp hc)]

/-- U n: the number of arrays with n + 2 lines. -/
def U (n : ℕ) : ℕ := 0 + 1 * V n 0 + 1 * V n 1 + 1 * V n 2 + 2 * V n 3 + 4 * V n 4 + 4 * V n 5 + 3 * V n 6 + 12 * V n 7 + 18 * V n 8 + 2 * V n 9 + 2 * V n 10 + 2 * V n 11 + 4 * V n 12 + 8 * V n 13 + 8 * V n 14 + 12 * V n 15 + 36 * V n 16 + 3 * V n 17 + 3 * V n 18 + 3 * V n 19 + 6 * V n 20 + 12 * V n 21 + 12 * V n 22 + 27 * V n 23 + 513 * V n 24 + 1 * V n 25 + 2 * V n 26 + 15 * V n 27 + 2 * V n 28 + 4 * V n 29 + 6 * V n 30

theorem usum (n : ℕ) : (∑ c ∈ Finset.range 31, ([1, 1, 1, 2, 4, 4, 3, 12, 18, 2, 2, 2, 4, 8, 8, 12, 36, 3, 3, 3, 6, 12, 12, 27, 513, 1, 2, 15, 2, 4, 6] : List ℕ).getD c 0 * V n c) = U n := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  rfl

theorem a_eq (n : ℕ) : a (n + 2) = U n := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight (good2_iff n)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 2) → R, if Walk2 x ∧ ini (x 0) then 1 else 0) =
      ∑ s : R, ∑ t : R, if ini s then F2 n s t else 0 := by
    unfold F2
    have h2 : ∀ s t : R, (if ini s then ∑ y : Fin (n + 2) → R,
        (if Walk2 y ∧ y 0 = s ∧ y 1 = t then 1 else 0) else 0) =
        ∑ y : Fin (n + 2) → R, if y 0 = s ∧ y 1 = t then (if Walk2 y ∧ ini (y 0) then 1 else 0)
          else 0 := by
      intro s t
      split_ifs with hs
      · apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y 0 = s ∧ y 1 = t
        · rw [if_pos hy]
          refine if_congr ⟨fun hh => ⟨hh.1, ?_⟩, fun hh => ⟨hh.1, hy⟩⟩ rfl rfl
          rw [hy.1]; exact hs
        · rw [if_neg hy, if_neg (fun hh => hy hh.2)]
      · symm
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : y 0 = s ∧ y 1 = t
        · rw [if_pos hy, if_neg]
          intro hh
          apply hs
          rw [← hy.1]; exact hh.2
        · rw [if_neg hy]
    have inner : ∀ (y : Fin (n + 2) → R) (c : ℕ) (s : R),
        (∑ t : R, if y 0 = s ∧ y 1 = t then c else 0) = if y 0 = s then c else 0 := by
      intro y c s
      by_cases h : y 0 = s
      · simp [h]
      · simp [h]
    rw [Finset.sum_congr rfl (fun s _ => Finset.sum_congr rfl (fun t _ => h2 s t)),
      Finset.sum_congr rfl (fun s _ => Finset.sum_comm), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_congr rfl (fun s _ => inner y _ s), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [h1]
  simp only [F2_eq]
  rw [Finset.sum_congr rfl (fun s _ => sum_clsf (cls2 s) (cls2_lt s) (V n) (fun _ => ini s)),
    Finset.sum_comm, ← usum n]
  apply Finset.sum_congr rfl
  intro c hc
  rw [← Finset.sum_mul, tcnt c (Finset.mem_range.mp hc)]

theorem good1_iff (x : Fin 1 → R) : Good x ↔ ok (x 0) ∧ ini (x 0) := by
  unfold Good
  constructor
  · rintro ⟨h2, h3⟩
    exact ⟨trivial, trivial⟩
  · rintro ⟨-, -⟩
    exact ⟨fun i j hij => by exfalso; have := i.isLt; have := j.isLt; omega,
      fun i j l hij hjl => by exfalso; have := i.isLt; have := j.isLt; omega⟩

theorem a_v1 : a 1 = 27 := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight good1_iff), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter, ← (Equiv.funUnique (Fin 1) R).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply]
  decide +kernel

theorem up0 (n : ℕ) : U n = V n 0 + V n 1 + V n 2 + 2 * V n 3 + 4 * V n 4 + 4 * V n 5 + 3 * V n 6 + 12 * V n 7 + 18 * V n 8 + 2 * V n 9 + 2 * V n 10 + 2 * V n 11 + 4 * V n 12 + 8 * V n 13 + 8 * V n 14 + 12 * V n 15 + 36 * V n 16 + 3 * V n 17 + 3 * V n 18 + 3 * V n 19 + 6 * V n 20 + 12 * V n 21 + 12 * V n 22 + 27 * V n 23 + 513 * V n 24 + V n 25 + 2 * V n 26 + 15 * V n 27 + 2 * V n 28 + 4 * V n 29 + 6 * V n 30 := by
  unfold U
  ring

theorem up1 (n : ℕ) : U (n + 1) = V n 0 + V n 1 + V n 2 + 3 * V n 3 + 9 * V n 4 + 9 * V n 5 + 6 * V n 6 + 36 * V n 7 + 72 * V n 8 + 3 * V n 9 + 3 * V n 10 + 3 * V n 11 + 9 * V n 12 + 24 * V n 13 + 24 * V n 14 + 51 * V n 15 + 201 * V n 16 + 6 * V n 17 + 6 * V n 18 + 6 * V n 19 + 18 * V n 20 + 48 * V n 21 + 48 * V n 22 + 186 * V n 23 + 4532 * V n 24 + 2 * V n 25 + 5 * V n 26 + 27 * V n 27 + 9 * V n 28 + 21 * V n 29 + 30 * V n 30 := by
  rw [up0 (n + 1)]
  simp only [V]
  ring

theorem up2 (n : ℕ) : U (n + 2) = V n 0 + V n 1 + V n 2 + 4 * V n 3 + 16 * V n 4 + 16 * V n 5 + 10 * V n 6 + 80 * V n 7 + 200 * V n 8 + 4 * V n 9 + 4 * V n 10 + 4 * V n 11 + 16 * V n 12 + 53 * V n 13 + 53 * V n 14 + 146 * V n 15 + 710 * V n 16 + 10 * V n 17 + 10 * V n 18 + 10 * V n 19 + 40 * V n 20 + 131 * V n 21 + 131 * V n 22 + 774 * V n 23 + 19623 * V n 24 + 3 * V n 25 + 9 * V n 26 + 42 * V n 27 + 24 * V n 28 + 67 * V n 29 + 91 * V n 30 := by
  rw [show n + 2 = (n + 1) + 1 from rfl, up1 (n + 1)]
  simp only [V]
  ring

theorem up3 (n : ℕ) : U (n + 3) = V n 0 + V n 1 + V n 2 + 5 * V n 3 + 25 * V n 4 + 25 * V n 5 + 15 * V n 6 + 150 * V n 7 + 450 * V n 8 + 5 * V n 9 + 5 * V n 10 + 5 * V n 11 + 25 * V n 12 + 99 * V n 13 + 99 * V n 14 + 335 * V n 15 + 1936 * V n 16 + 15 * V n 17 + 15 * V n 18 + 15 * V n 19 + 75 * V n 20 + 290 * V n 21 + 290 * V n 22 + 2425 * V n 23 + 62422 * V n 24 + 4 * V n 25 + 14 * V n 26 + 60 * V n 27 + 50 * V n 28 + 165 * V n 29 + 215 * V n 30 := by
  rw [show n + 3 = (n + 1) + 2 from rfl, up2 (n + 1)]
  simp only [V]
  ring

theorem up4 (n : ℕ) : U (n + 4) = V n 0 + V n 1 + V n 2 + 6 * V n 3 + 36 * V n 4 + 36 * V n 5 + 21 * V n 6 + 252 * V n 7 + 882 * V n 8 + 6 * V n 9 + 6 * V n 10 + 6 * V n 11 + 36 * V n 12 + 166 * V n 13 + 166 * V n 14 + 666 * V n 15 + 4458 * V n 16 + 21 * V n 17 + 21 * V n 18 + 21 * V n 19 + 126 * V n 20 + 561 * V n 21 + 561 * V n 22 + 6307 * V n 23 + 163391 * V n 24 + 5 * V n 25 + 20 * V n 26 + 81 * V n 27 + 90 * V n 28 + 345 * V n 29 + 435 * V n 30 := by
  rw [show n + 4 = (n + 1) + 3 from rfl, up3 (n + 1)]
  simp only [V]
  ring

theorem up5 (n : ℕ) : U (n + 5) = V n 0 + V n 1 + V n 2 + 7 * V n 3 + 49 * V n 4 + 49 * V n 5 + 28 * V n 6 + 392 * V n 7 + 1568 * V n 8 + 7 * V n 9 + 7 * V n 10 + 7 * V n 11 + 49 * V n 12 + 258 * V n 13 + 258 * V n 14 + 1197 * V n 15 + 9107 * V n 16 + 28 * V n 17 + 28 * V n 18 + 28 * V n 19 + 196 * V n 20 + 987 * V n 21 + 987 * V n 22 + 14364 * V n 23 + 373118 * V n 24 + 6 * V n 25 + 27 * V n 26 + 105 * V n 27 + 147 * V n 28 + 644 * V n 29 + 791 * V n 30 := by
  rw [show n + 5 = (n + 1) + 4 from rfl, up4 (n + 1)]
  simp only [V]
  ring

theorem up6 (n : ℕ) : U (n + 6) = V n 0 + V n 1 + V n 2 + 8 * V n 3 + 64 * V n 4 + 64 * V n 5 + 36 * V n 6 + 576 * V n 7 + 2592 * V n 8 + 8 * V n 9 + 8 * V n 10 + 8 * V n 11 + 64 * V n 12 + 379 * V n 13 + 379 * V n 14 + 1996 * V n 15 + 17012 * V n 16 + 36 * V n 17 + 36 * V n 18 + 36 * V n 19 + 288 * V n 20 + 1618 * V n 21 + 1618 * V n 22 + 29604 * V n 23 + 769759 * V n 24 + 7 * V n 25 + 35 * V n 26 + 132 * V n 27 + 224 * V n 28 + 1106 * V n 29 + 1330 * V n 30 := by
  rw [show n + 6 = (n + 1) + 5 from rfl, up5 (n + 1)]
  simp only [V]
  ring

theorem up7 (n : ℕ) : U (n + 7) = V n 0 + V n 1 + V n 2 + 9 * V n 3 + 81 * V n 4 + 81 * V n 5 + 45 * V n 6 + 810 * V n 7 + 4050 * V n 8 + 9 * V n 9 + 9 * V n 10 + 9 * V n 11 + 81 * V n 12 + 533 * V n 13 + 533 * V n 14 + 3141 * V n 15 + 29646 * V n 16 + 45 * V n 17 + 45 * V n 18 + 45 * V n 19 + 405 * V n 20 + 2511 * V n 21 + 2511 * V n 22 + 56433 * V n 23 + 1467676 * V n 24 + 8 * V n 25 + 44 * V n 26 + 162 * V n 27 + 324 * V n 28 + 1782 * V n 29 + 2106 * V n 30 := by
  rw [show n + 7 = (n + 1) + 6 from rfl, up6 (n + 1)]
  simp only [V]
  ring

theorem kry (n : ℕ) :
    (54 * (V n 24 : ℚ) = 0) := by
  induction n with
  | zero => simp [V]
  | succ n ih =>
    have h0 := ih
    simp only [V]; push_cast; linear_combination (0 : ℚ) * h0

theorem a_v2 : a 2 = 216 := by
  rw [show a 2 = U 0 from a_eq _]; decide +kernel

theorem a_v3 : a 3 = 868 := by
  rw [show a 3 = U 1 from a_eq _]; decide +kernel

theorem a_v4 : a 4 = 2661 := by
  rw [show a 4 = U 2 from a_eq _]; decide +kernel

theorem a_v5 : a 5 = 6815 := by
  rw [show a 5 = U 3 from a_eq _]; decide +kernel

theorem a_v6 : a 6 = 15340 := by
  rw [show a 6 = U 4 from a_eq _]; decide +kernel

theorem a_v7 : a 7 = 31324 := by
  rw [show a 7 = U 5 from a_eq _]; decide +kernel

theorem a_v8 : a 8 = 59267 := by
  rw [show a 8 = U 6 from a_eq _]; decide +kernel

theorem a_rec : ∀ m : ℕ, 9 ≤ m → (a m : ℤ) = 7 * (a (m - 1) : ℤ) - 21 * (a (m - 2) : ℤ) + 35 * (a (m - 3) : ℤ) - 35 * (a (m - 4) : ℤ) + 21 * (a (m - 5) : ℤ) - 7 * (a (m - 6) : ℤ) + (a (m - 7) : ℤ) := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 9 := ⟨m - 9, by omega⟩
  rw [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega, show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega, show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega, show k + 9 - 7 = k + 2 by omega]
  rw [show a (k + 9) = U (k + 7) from a_eq _, show a (k + 8) = U (k + 6) from a_eq _, show a (k + 7) = U (k + 5) from a_eq _, show a (k + 6) = U (k + 4) from a_eq _, show a (k + 5) = U (k + 3) from a_eq _, show a (k + 4) = U (k + 2) from a_eq _, show a (k + 3) = U (k + 1) from a_eq _, show a (k + 2) = U (k) from a_eq _]
  rw [up7 k, up6 k, up5 k, up4 k, up3 k, up2 k, up1 k, up0 k]
  push_cast
  have h := (kry k)
  have hz : 54 * (V k 24 : ℤ) = 0 := by exact_mod_cast h
  linear_combination hz

theorem gf_eq : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have e1 : F' * ((1 - PowerSeries.X) ^ 7) = F' - PowerSeries.C (7 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (21 : ℚ) * (PowerSeries.X ^ 2 * F') - PowerSeries.C (35 : ℚ) * (PowerSeries.X ^ 3 * F') + PowerSeries.C (35 : ℚ) * (PowerSeries.X ^ 4 * F') - PowerSeries.C (21 : ℚ) * (PowerSeries.X ^ 5 * F') + PowerSeries.C (7 : ℚ) * (PowerSeries.X ^ 6 * F') - PowerSeries.X ^ 7 * F' := by
    simp only [map_ofNat]
    ring
  have e2 : (PowerSeries.X * (27 + 27 * PowerSeries.X - 77 * PowerSeries.X ^ 2 + 176 * PowerSeries.X ^ 3 - 199 * PowerSeries.X ^ 4 + 129 * PowerSeries.X ^ 5 - 43 * PowerSeries.X ^ 6 + 6 * PowerSeries.X ^ 7) : PowerSeries ℚ) = PowerSeries.C (27 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (27 : ℚ) * PowerSeries.X ^ 2 - PowerSeries.C (77 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (176 : ℚ) * PowerSeries.X ^ 4 - PowerSeries.C (199 : ℚ) * PowerSeries.X ^ 5 + PowerSeries.C (129 : ℚ) * PowerSeries.X ^ 6 - PowerSeries.C (43 : ℚ) * PowerSeries.X ^ 7 + PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 8 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 8
  · interval_cases n <;> norm_num [a_v1, a_v2, a_v3, a_v4, a_v5, a_v6, a_v7, a_v8]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 9 := ⟨n - 9, by omega⟩
    have h := a_rec (j + 9) (by omega)
    rw [show j + 9 - 1 = j + 8 by omega, show j + 9 - 2 = j + 7 by omega, show j + 9 - 3 = j + 6 by omega, show j + 9 - 4 = j + 5 by omega, show j + 9 - 5 = j + 4 by omega, show j + 9 - 6 = j + 3 by omega, show j + 9 - 7 = j + 2 by omega] at h
    have q : (a (j + 9) : ℚ) = 7 * (a (j + 8) : ℚ) - 21 * (a (j + 7) : ℚ) + 35 * (a (j + 6) : ℚ) - 35 * (a (j + 5) : ℚ) + 21 * (a (j + 4) : ℚ) - 7 * (a (j + 3) : ℚ) + (a (j + 2) : ℚ) := by exact_mod_cast h
    simp
    linear_combination q

theorem closed0 : ∀ n : ℕ, 2 ≤ n → (a n : ℚ) = (23 / 360) * (n : ℚ) ^ 6 + (27 / 40) * (n : ℚ) ^ 5 + (271 / 72) * (n : ℚ) ^ 4 + (65 / 8) * (n : ℚ) ^ 3 + (2101 / 180) * (n : ℚ) ^ 2 + (97 / 10) * (n : ℚ) - 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 9
    · interval_cases n <;> norm_num [a_v2, a_v3, a_v4, a_v5, a_v6, a_v7, a_v8]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
      have h1 := ih (k + 8) (by omega) (by omega)
      have h2 := ih (k + 7) (by omega) (by omega)
      have h3 := ih (k + 6) (by omega) (by omega)
      have h4 := ih (k + 5) (by omega) (by omega)
      have h5 := ih (k + 4) (by omega) (by omega)
      have h6 := ih (k + 3) (by omega) (by omega)
      have h7 := ih (k + 2) (by omega) (by omega)
      have hr := a_rec (k + 9) (by omega)
      rw [show k + 9 - 1 = k + 8 by omega, show k + 9 - 2 = k + 7 by omega, show k + 9 - 3 = k + 6 by omega, show k + 9 - 4 = k + 5 by omega, show k + 9 - 5 = k + 4 by omega, show k + 9 - 6 = k + 3 by omega, show k + 9 - 7 = k + 2 by omega] at hr
      have q : (a (k + 9) : ℚ) = 7 * (a (k + 8) : ℚ) - 21 * (a (k + 7) : ℚ) + 35 * (a (k + 6) : ℚ) - 35 * (a (k + 5) : ℚ) + 21 * (a (k + 4) : ℚ) - 7 * (a (k + 3) : ℚ) + (a (k + 2) : ℚ) := by exact_mod_cast hr
      rw [q, h1, h2, h3, h4, h5, h6, h7]
      push_cast
      ring

end OMAA224013Helpers

open OMA.S_oeis_a224013 OMAA224013Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a224013.main :=
  ⟨a_rec, gf_eq, closed0⟩
