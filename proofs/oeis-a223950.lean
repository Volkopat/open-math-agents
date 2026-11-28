import OMAStatements.S_oeis_a223950
import Mathlib

-- Proof of the formulas of OEIS A223950 (statement by @ivillar).
-- Idea: the conditions only involve three consecutive lines, so the count is a walk count on pairs of consecutive
-- lines (transfer matrix). The pairs are grouped into classes such that the number of successors in each class
-- depends only on the class (checked by decide); the class counts V n c then satisfy an explicit linear system, from
-- which the recurrence follows by linear algebra, and the g.f. and the closed form follow from the recurrence and
-- initial values.

namespace OMAA223950Helpers

open OMA.S_oeis_a223950

/-- The lines of the array (the states of the transfer matrix are pairs of consecutive lines). -/
abbrev R := Fin 3 → Fin 2

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
  [[[[[[0, 1], [2, 3]], [[1, 4], [3, 5]]], [[[6, 7], [6, 3]], [[6, 8], [6, 5]]]], [[[[6, 6], [2, 3]], [[6, 6], [3, 5]]], [[[6, 6], [6, 3]], [[6, 6], [6, 5]]]]], [[[[[6, 6], [6, 6]], [[7, 8], [3, 5]]], [[[6, 6], [6, 6]], [[6, 9], [6, 5]]]], [[[[6, 6], [6, 6]], [[6, 6], [3, 5]]], [[[6, 6], [6, 6]], [[6, 6], [6, 5]]]]]]

/-- The class of a pair of consecutive lines: pairs of the same class have the same number of successors
in each class. -/
def cls2 (s t : R) : ℕ :=
  ((((((clsT).getD (s 0 : ℕ) []).getD (s 1 : ℕ) []).getD (s 2 : ℕ) []).getD (t 0 : ℕ) []).getD (t 1 : ℕ) []).getD (t 2 : ℕ) 0

/-- Mt i j: the number of successors in class j of a pair of class i. -/
def Mt (i j : ℕ) : ℕ :=
  (([[1, 2, 1, 2, 1, 1, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 1, 4, 1, 1, 0],
    [0, 0, 1, 2, 0, 1, 4, 0, 0, 0],
    [0, 0, 0, 1, 0, 1, 6, 0, 0, 0],
    [0, 0, 0, 0, 0, 1, 6, 0, 0, 1],
    [0, 0, 0, 0, 0, 1, 7, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
    [0, 0, 0, 1, 0, 0, 2, 1, 0, 0],
    [0, 0, 0, 0, 0, 0, 4, 0, 0, 0],
    [0, 0, 0, 0, 0, 0, 2, 0, 0, 0]] : List (List ℕ)).getD i []).getD j 0

/-- V n c: the number of walks of n + 2 lines starting with a given pair of lines of class c. -/
def V : ℕ → ℕ → ℕ
  | 0, c => ([1, 1, 1, 1, 1, 1, 0, 1, 1, 1] : List ℕ).getD c 0
  | n + 1, 0 => 0 + 1 * V n 0 + 2 * V n 1 + 1 * V n 2 + 2 * V n 3 + 1 * V n 4 + 1 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9
  | n + 1, 1 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 1 * V n 3 + 0 * V n 4 + 1 * V n 5 + 4 * V n 6 + 1 * V n 7 + 1 * V n 8 + 0 * V n 9
  | n + 1, 2 => 0 + 0 * V n 0 + 0 * V n 1 + 1 * V n 2 + 2 * V n 3 + 0 * V n 4 + 1 * V n 5 + 4 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9
  | n + 1, 3 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 1 * V n 3 + 0 * V n 4 + 1 * V n 5 + 6 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9
  | n + 1, 4 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 1 * V n 5 + 6 * V n 6 + 0 * V n 7 + 0 * V n 8 + 1 * V n 9
  | n + 1, 5 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 1 * V n 5 + 7 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9
  | n + 1, 6 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 0 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9
  | n + 1, 7 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 1 * V n 3 + 0 * V n 4 + 0 * V n 5 + 2 * V n 6 + 1 * V n 7 + 0 * V n 8 + 0 * V n 9
  | n + 1, 8 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 4 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9
  | n + 1, 9 => 0 + 0 * V n 0 + 0 * V n 1 + 0 * V n 2 + 0 * V n 3 + 0 * V n 4 + 0 * V n 5 + 2 * V n 6 + 0 * V n 7 + 0 * V n 8 + 0 * V n 9
  | _ + 1, _ => 0

theorem cls2_lt : ∀ s t : R, cls2 s t < 10 := by decide +kernel

theorem sum_clsf (f : R → ℕ) (hf : ∀ t, f t < 10) (g : ℕ → ℕ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then g (f t) else 0) =
      ∑ c ∈ Finset.range 10, (Finset.univ.filter (fun t : R => f t = c ∧ P t)).card * g c := by
  have h1 : ∀ t : R, (if P t then g (f t) else 0) =
      ∑ c ∈ Finset.range 10, if f t = c ∧ P t then g c else 0 := by
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

/-- The lines, numbered by their base-2 digits. -/
abbrev E : R ≃ Fin (2 ^ 3) := finFunctionFinEquiv

theorem cntN : ∀ a b : Fin (2 ^ 3), ∀ c < 10,
    (Finset.univ.filter (fun x : Fin (2 ^ 3) => cls2 (E.symm b) (E.symm x) = c ∧
      (ok (E.symm a) ∧ compat (E.symm a) (E.symm b) ∧ tri (E.symm a) (E.symm b) (E.symm x)))).card =
      Mt (cls2 (E.symm a) (E.symm b)) c := by
  decide +kernel

theorem cnt (s t : R) (c : ℕ) (hc : c < 10) :
    (Finset.univ.filter (fun u : R => cls2 t u = c ∧ (ok s ∧ compat s t ∧ tri s t u))).card =
      Mt (cls2 s t) c := by
  have h := cntN (E s) (E t) c hc
  simp only [Equiv.symm_apply_apply] at h
  rw [← h, Finset.card_filter, Finset.card_filter]
  exact (Equiv.sum_comp E.symm
    (fun u : R => if cls2 t u = c ∧ (ok s ∧ compat s t ∧ tri s t u) then 1 else 0)).symm


theorem cnt0 : ∀ s t : R, (if (ok s ∧ ok t) ∧ compat s t then 1 else 0) = V 0 (cls2 s t) := by
  decide +kernel

theorem tcnt : ∀ c < 10, (∑ s : R, (Finset.univ.filter (fun t : R => cls2 s t = c ∧ ini s)).card) =
    ([1, 2, 2, 8, 1, 8, 37, 2, 2, 1] : List ℕ).getD c 0 := by decide +kernel

theorem step (n : ℕ) : ∀ i < 10, (∑ c ∈ Finset.range 10, Mt i c * V n c) = V (n + 1) i := by
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
def U (n : ℕ) : ℕ := 0 + 1 * V n 0 + 2 * V n 1 + 2 * V n 2 + 8 * V n 3 + 1 * V n 4 + 8 * V n 5 + 37 * V n 6 + 2 * V n 7 + 2 * V n 8 + 1 * V n 9

theorem usum (n : ℕ) : (∑ c ∈ Finset.range 10, ([1, 2, 2, 8, 1, 8, 37, 2, 2, 1] : List ℕ).getD c 0 * V n c) = U n := by
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

theorem a_v1 : a 1 = 8 := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight good1_iff), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter, ← (Equiv.funUnique (Fin 1) R).symm.sum_comp]
  simp only [Equiv.funUnique_symm_apply]
  decide +kernel

theorem up0 (n : ℕ) : U n = V n 0 + 2 * V n 1 + 2 * V n 2 + 8 * V n 3 + V n 4 + 8 * V n 5 + 37 * V n 6 + 2 * V n 7 + 2 * V n 8 + V n 9 := by
  unfold U
  ring

theorem up1 (n : ℕ) : U (n + 1) = V n 0 + 2 * V n 1 + 3 * V n 2 + 18 * V n 3 + V n 4 + 22 * V n 5 + 140 * V n 6 + 4 * V n 7 + 2 * V n 8 + V n 9 := by
  rw [up0 (n + 1)]
  simp only [V]
  ring

theorem up2 (n : ℕ) : U (n + 2) = V n 0 + 2 * V n 1 + 4 * V n 2 + 32 * V n 3 + V n 4 + 47 * V n 5 + 306 * V n 6 + 6 * V n 7 + 2 * V n 8 + V n 9 := by
  rw [show n + 2 = (n + 1) + 1 from rfl, up1 (n + 1)]
  simp only [V]
  ring

theorem up3 (n : ℕ) : U (n + 3) = V n 0 + 2 * V n 1 + 5 * V n 2 + 50 * V n 3 + V n 4 + 87 * V n 5 + 573 * V n 6 + 8 * V n 7 + 2 * V n 8 + V n 9 := by
  rw [show n + 3 = (n + 1) + 2 from rfl, up2 (n + 1)]
  simp only [V]
  ring

theorem up4 (n : ℕ) : U (n + 4) = V n 0 + 2 * V n 1 + 6 * V n 2 + 72 * V n 3 + V n 4 + 146 * V n 5 + 969 * V n 6 + 10 * V n 7 + 2 * V n 8 + V n 9 := by
  rw [show n + 4 = (n + 1) + 3 from rfl, up3 (n + 1)]
  simp only [V]
  ring

theorem kry (n : ℕ) :
    (-10 * (V n 6 : ℚ) = 0) := by
  induction n with
  | zero => simp [V]
  | succ n ih =>
    have h0 := ih
    simp only [V]; push_cast; linear_combination (0 : ℚ) * h0

theorem a_v2 : a 2 = 27 := by
  rw [show a 2 = U 0 from a_eq _]; decide +kernel

theorem a_v3 : a 3 = 54 := by
  rw [show a 3 = U 1 from a_eq _]; decide +kernel

theorem a_v4 : a 4 = 96 := by
  rw [show a 4 = U 2 from a_eq _]; decide +kernel

theorem a_v5 : a 5 = 157 := by
  rw [show a 5 = U 3 from a_eq _]; decide +kernel

theorem a_rec : ∀ m : ℕ, 6 ≤ m → (a m : ℤ) = 4 * (a (m - 1) : ℤ) - 6 * (a (m - 2) : ℤ) + 4 * (a (m - 3) : ℤ) - (a (m - 4) : ℤ) := by
  intro m hm
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 6 := ⟨m - 6, by omega⟩
  rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega, show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega]
  rw [show a (k + 6) = U (k + 4) from a_eq _, show a (k + 5) = U (k + 3) from a_eq _, show a (k + 4) = U (k + 2) from a_eq _, show a (k + 3) = U (k + 1) from a_eq _, show a (k + 2) = U (k) from a_eq _]
  rw [up4 k, up3 k, up2 k, up1 k, up0 k]
  push_cast
  have h := (kry k)
  have hz : -10 * (V k 6 : ℤ) = 0 := by exact_mod_cast h
  linear_combination hz

theorem gf_eq : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) = G := by
  rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
  set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
  have e1 : F' * ((1 - PowerSeries.X) ^ 4) = F' - PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 2 * F') - PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 3 * F') + PowerSeries.X ^ 4 * F' := by
    simp only [map_ofNat]
    ring
  have e2 : (PowerSeries.X * (8 - 5 * PowerSeries.X - 6 * PowerSeries.X ^ 2 + 10 * PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 4) : PowerSeries ℚ) = PowerSeries.C (8 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (5 : ℚ) * PowerSeries.X ^ 2 - PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 3 + PowerSeries.C (10 : ℚ) * PowerSeries.X ^ 4 - PowerSeries.C (3 : ℚ) * PowerSeries.X ^ 5 := by
    simp only [map_ofNat]
    ring
  rw [e1, e2]
  ext n
  simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
  by_cases hn : n ≤ 5
  · interval_cases n <;> norm_num [a_v1, a_v2, a_v3, a_v4, a_v5]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 6 := ⟨n - 6, by omega⟩
    have h := a_rec (j + 6) (by omega)
    rw [show j + 6 - 1 = j + 5 by omega, show j + 6 - 2 = j + 4 by omega, show j + 6 - 3 = j + 3 by omega, show j + 6 - 4 = j + 2 by omega] at h
    have q : (a (j + 6) : ℚ) = 4 * (a (j + 5) : ℚ) - 6 * (a (j + 4) : ℚ) + 4 * (a (j + 3) : ℚ) - (a (j + 2) : ℚ) := by exact_mod_cast h
    simp
    linear_combination q

theorem closed0 : ∀ n : ℕ, 2 ≤ n → (a n : ℚ) = (2 / 3) * (n : ℚ) ^ 3 + (3 / 2) * (n : ℚ) ^ 2 + (41 / 6) * (n : ℚ) + 2 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 6
    · interval_cases n <;> norm_num [a_v2, a_v3, a_v4, a_v5]
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      have h1 := ih (k + 5) (by omega) (by omega)
      have h2 := ih (k + 4) (by omega) (by omega)
      have h3 := ih (k + 3) (by omega) (by omega)
      have h4 := ih (k + 2) (by omega) (by omega)
      have hr := a_rec (k + 6) (by omega)
      rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega, show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega] at hr
      have q : (a (k + 6) : ℚ) = 4 * (a (k + 5) : ℚ) - 6 * (a (k + 4) : ℚ) + 4 * (a (k + 3) : ℚ) - (a (k + 2) : ℚ) := by exact_mod_cast hr
      rw [q, h1, h2, h3, h4]
      push_cast
      ring

end OMAA223950Helpers

open OMA.S_oeis_a223950 OMAA223950Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a223950.main :=
  ⟨a_rec, gf_eq, closed0⟩
