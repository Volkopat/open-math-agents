import OMAStatements.S_oeis_a223982
import Mathlib

-- Proof of the conjectures in OEIS A223982 (statement by @ivillar).
-- Idea: the conditions involve only consecutive rows, so the count is a walk count on rows (transfer matrix).
-- For each row s, the number α(n, s) of walks with n steps starting at s is tabulated for n < 10; the tables satisfy
-- the transfer relation (checked by kernel computation) and a linear recurrence of order 10 with the characteristic
-- polynomial of the conjectured recurrence as a factor. Sequences with the same recurrence and initial values agree,
-- which gives the recurrence, the g.f. and the closed form.

namespace OMAA223982Helpers

open OMA.S_oeis_a223982

abbrev R := Fin 3 → Fin 4

instance (r : R) : Decidable (Unimodal r) := by unfold Unimodal; infer_instance


abbrev ok (r : R) : Prop := Unimodal r

abbrev compat (r s : R) : Prop := ∀ j, r j ≤ s j


abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem walk_cons (n : ℕ) (r : R) (y : Fin (n + 1) → R) :
    Walk (Fin.cons r y : Fin (n + 2) → R) ↔ ok r ∧ compat r (y 0) ∧ Walk y := by
  simp only [Walk, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    ← Fin.succ_castSucc]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩
    refine ⟨h1, ?_, h2, h4⟩
    simpa using h3
  · rintro ⟨h1, h3, h2, h4⟩
    refine ⟨⟨h1, h2⟩, ?_, h4⟩
    simpa using h3

def F (n : ℕ) (s : R) : ℕ := ∑ y : Fin (n + 1) → R, if Walk y ∧ y 0 = s then 1 else 0

theorem F_zero (s : R) : F 0 s = if ok s then 1 else 0 := by
  unfold F
  rw [← (Equiv.funUnique (Fin 1) R).symm.sum_comp]
  have h : ∀ r : R, (if Walk ((Equiv.funUnique (Fin 1) R).symm r) ∧
      (Equiv.funUnique (Fin 1) R).symm r 0 = s then 1 else 0) = if r = s then (if ok s then 1 else 0) else 0 := by
    intro r
    simp only [Equiv.funUnique_symm_apply, Walk, IsEmpty.forall_iff, and_true]
    by_cases hr : r = s
    · subst hr; simp
    · simp [hr]
  rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq']
  simp

theorem F_succ (n : ℕ) (s : R) :
    F (n + 1) s = ∑ t : R, if ok s ∧ compat s t then F n t else 0 := by
  have lhs : F (n + 1) s = ∑ y : Fin (n + 1) → R, if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0 := by
    unfold F
    rw [← (Fin.consEquiv (fun _ : Fin (n + 2) => R)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have h : ∀ r : R, (if Walk ((Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y)) ∧
        (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) 0 = s then 1 else 0) =
        if r = s then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
      intro r
      rw [show (Fin.consEquiv (fun _ : Fin (n + 2) => R)) (r, y) = (Fin.cons r y : Fin (n + 2) → R)
        from rfl]
      simp only [walk_cons, Fin.cons_zero]
      by_cases hr : r = s
      · subst hr
        rw [if_pos rfl]
        exact if_congr ⟨fun h => h.1, fun h => ⟨h, rfl⟩⟩ rfl rfl
      · rw [if_neg hr, if_neg (show ¬((ok r ∧ compat r (y 0) ∧ Walk y) ∧ r = s) from fun h => hr h.2)]
    rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq', if_pos (Finset.mem_univ _)]
  rw [lhs]
  unfold F
  have h2 : ∀ t : R, (if ok s ∧ compat s t then
      ∑ y : Fin (n + 1) → R, (if Walk y ∧ y 0 = t then 1 else 0) else 0) =
      ∑ y : Fin (n + 1) → R, if y 0 = t then (if ok s ∧ compat s (y 0) ∧ Walk y then 1 else 0) else 0 := by
    intro t
    split_ifs with ht
    · apply Finset.sum_congr rfl
      intro y _
      by_cases hy : y 0 = t
      · subst hy
        rw [if_pos (rfl : y 0 = y 0)]
        exact if_congr ⟨fun h => ⟨ht.1, ht.2, h.1⟩, fun h => ⟨h.2.2, rfl⟩⟩ rfl rfl
      · rw [if_neg hy, if_neg (show ¬(Walk y ∧ y 0 = t) from fun h => hy h.2)]
    · symm
      apply Finset.sum_eq_zero
      intro y _
      by_cases hy : y 0 = t
      · subst hy; rw [if_pos rfl, if_neg (fun h => ht ⟨h.1, h.2.1⟩)]
      · rw [if_neg hy]
  rw [Finset.sum_congr rfl (fun t _ => h2 t), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

theorem sum_F (n : ℕ) : (∑ x : Fin (n + 1) → R, if Walk x then 1 else 0) = ∑ s : R, F n s := by
  unfold F
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have hh : ∀ s : R, (if Walk y ∧ y 0 = s then 1 else 0) = if y 0 = s then (if Walk y then 1 else 0) else 0 := by
    intro s
    by_cases h : y 0 = s
    · rw [if_pos h]; exact if_congr ⟨fun hh => hh.1, fun hh => ⟨hh, h⟩⟩ rfl rfl
    · rw [if_neg h, if_neg (show ¬(Walk y ∧ y 0 = s) from fun hh => h hh.2)]
  rw [Finset.sum_congr rfl (fun s _ => hh s), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]

theorem forall_vecCons {k : ℕ} {β : Type} (P : (Fin (k + 1) → β) → Prop) :
    (∀ s, P s) ↔ ∀ a t, P (Matrix.vecCons a t) :=
  ⟨fun h a t => h _, fun h s => by rw [← Matrix.cons_head_tail s]; exact h _ _⟩

theorem forall_vecEmpty {β : Type} (P : (Fin 0 → β) → Prop) : (∀ s, P s) ↔ P ![] :=
  ⟨fun h => h _, fun h s => by rw [Subsingleton.elim s ![]]; exact h⟩

theorem sum_vecCons {k : ℕ} {β : Type} [Fintype β] (f : (Fin (k + 1) → β) → ℤ) :
    ∑ s, f s = ∑ a, ∑ t, f (Matrix.vecCons a t) := by
  rw [← (Fin.consEquiv (fun _ : Fin (k + 1) => β)).sum_comp, Fintype.sum_prod_type]
  rfl

theorem sum_vecEmpty {β : Type} [Fintype β] (f : (Fin 0 → β) → ℤ) : ∑ s, f s = f ![] := by
  rw [Fintype.sum_unique]
  congr 1

def look (l : List (List (List (ℤ)))) (s : R) : ℤ := (((l).getD (s 0).val []).getD (s 1).val []).getD (s 2).val 0

def tab0 : List (List (List (ℤ))) := [[[1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]], [[1, 0, 0, 0], [1, 1, 1, 1], [1, 1, 1, 1], [1, 1, 1, 1]], [[1, 0, 0, 0], [1, 1, 0, 0], [1, 1, 1, 1], [1, 1, 1, 1]], [[1, 0, 0, 0], [1, 1, 0, 0], [1, 1, 1, 0], [1, 1, 1, 1]]]

def tab1 : List (List (List (ℤ))) := [[[50, 34, 21, 10], [43, 31, 19, 9], [31, 23, 15, 7], [16, 12, 8, 4]], [[34, 0, 0, 0], [31, 22, 13, 6], [23, 17, 11, 5], [12, 9, 6, 3]], [[21, 0, 0, 0], [19, 13, 0, 0], [15, 11, 7, 3], [8, 6, 4, 2]], [[10, 0, 0, 0], [9, 6, 0, 0], [7, 5, 3, 0], [4, 3, 2, 1]]]

def tab2 : List (List (List (ℤ))) := [[[684, 351, 159, 50], [504, 286, 128, 40], [283, 167, 81, 25], [100, 60, 30, 10]], [[351, 0, 0, 0], [286, 158, 66, 20], [167, 98, 47, 14], [60, 36, 18, 6]], [[159, 0, 0, 0], [128, 66, 0, 0], [81, 47, 22, 6], [30, 18, 9, 3]], [[50, 0, 0, 0], [40, 20, 0, 0], [25, 14, 6, 0], [10, 6, 3, 1]]]

def tab3 : List (List (List (ℤ))) := [[[5029, 2071, 744, 175], [3225, 1511, 535, 125], [1483, 727, 281, 65], [400, 200, 80, 20]], [[2071, 0, 0, 0], [1511, 684, 221, 50], [727, 354, 135, 30], [200, 100, 40, 10]], [[744, 0, 0, 0], [535, 221, 0, 0], [281, 135, 50, 10], [80, 40, 16, 4]], [[175, 0, 0, 0], [125, 50, 0, 0], [65, 30, 10, 0], [20, 10, 4, 1]]]

def tab4 : List (List (List (ℤ))) := [[[25410, 8739, 2606, 490], [14401, 5749, 1687, 315], [5608, 2352, 756, 140], [1225, 525, 175, 35]], [[8739, 0, 0, 0], [5749, 2205, 581, 105], [2352, 979, 310, 55], [525, 225, 75, 15]], [[2606, 0, 0, 0], [1687, 581, 0, 0], [756, 310, 95, 15], [175, 75, 25, 5]], [[490, 0, 0, 0], [315, 105, 0, 0], [140, 55, 15, 0], [35, 15, 5, 1]]]

def tab5 : List (List (List (ℤ))) := [[[99634, 29421, 7506, 1176], [50554, 17586, 4410, 686], [17074, 6258, 1722, 266], [3136, 1176, 336, 56]], [[29421, 0, 0, 0], [17586, 5852, 1302, 196], [6258, 2275, 616, 91], [1176, 441, 126, 21]], [[7506, 0, 0, 0], [4410, 1302, 0, 0], [1722, 616, 161, 21], [336, 126, 36, 6]], [[1176, 0, 0, 0], [686, 196, 0, 0], [266, 91, 21, 0], [56, 21, 6, 1]]]

def tab6 : List (List (List (ℤ))) := [[[325120, 84123, 18762, 2520], [149280, 46020, 10080, 1344], [44514, 14490, 3486, 462], [7056, 2352, 588, 84]], [[84123, 0, 0, 0], [46020, 13524, 2604, 336], [14490, 4676, 1106, 140], [2352, 784, 196, 28]], [[18762, 0, 0, 0], [10080, 2604, 0, 0], [3486, 1106, 252, 28], [588, 196, 49, 7]], [[2520, 0, 0, 0], [1344, 336, 0, 0], [462, 140, 28, 0], [84, 28, 7, 1]]]

def tab7 : List (List (List (ℤ))) := [[[922768, 212487, 42108, 4950], [386838, 107082, 20826, 2430], [103266, 30234, 6462, 750], [14400, 4320, 960, 120]], [[212487, 0, 0, 0], [107082, 28176, 4782, 540], [30234, 8772, 1842, 204], [4320, 1296, 288, 36]], [[42108, 0, 0, 0], [20826, 4782, 0, 0], [6462, 1842, 372, 36], [960, 288, 64, 8]], [[4950, 0, 0, 0], [2430, 540, 0, 0], [750, 204, 36, 0], [120, 36, 8, 1]]]

def tab8 : List (List (List (ℤ))) := [[[2346883, 486882, 86823, 9075], [905025, 227337, 39765, 4125], [218691, 58179, 11187, 1155], [27225, 7425, 1485, 165]], [[486882, 0, 0, 0], [227337, 54153, 8217, 825], [58179, 15333, 2895, 285], [7425, 2025, 405, 45]], [[86823, 0, 0, 0], [39765, 8217, 0, 0], [11187, 2895, 525, 45], [1485, 405, 81, 9]], [[9075, 0, 0, 0], [4125, 825, 0, 0], [1155, 285, 45, 0], [165, 45, 9, 1]]]

def tab9 : List (List (List (ℤ))) := [[[5462600, 1031173, 167167, 15730], [1950157, 448393, 71269, 6655], [430441, 104929, 18337, 1705], [48400, 12100, 2200, 220]], [[1031173, 0, 0, 0], [448393, 97570, 13387, 1210], [104929, 25333, 4345, 385], [12100, 3025, 550, 55]], [[167167, 0, 0, 0], [71269, 13387, 0, 0], [18337, 4345, 715, 55], [2200, 550, 100, 10]], [[15730, 0, 0, 0], [6655, 1210, 0, 0], [1705, 385, 55, 0], [220, 55, 10, 1]]]

def α : ℕ → R → ℤ
  | 0, s => look tab0 s
  | 1, s => look tab1 s
  | 2, s => look tab2 s
  | 3, s => look tab3 s
  | 4, s => look tab4 s
  | 5, s => look tab5 s
  | 6, s => look tab6 s
  | 7, s => look tab7 s
  | 8, s => look tab8 s
  | 9, s => look tab9 s
  | n + 10, s => (-1) * α n s + 10 * α (n + 1) s - 45 * α (n + 2) s + 120 * α (n + 3) s - 210 * α (n + 4) s + 252 * α (n + 5) s - 210 * α (n + 6) s + 120 * α (n + 7) s - 45 * α (n + 8) s + 10 * α (n + 9) s

theorem α_rec (n : ℕ) (s : R) : α (n + 10) s = (-1) * α n s + 10 * α (n + 1) s - 45 * α (n + 2) s + 120 * α (n + 3) s - 210 * α (n + 4) s + 252 * α (n + 5) s - 210 * α (n + 6) s + 120 * α (n + 7) s - 45 * α (n + 8) s + 10 * α (n + 9) s := by
  rw [α]

theorem uniqP {K : Type} [CommRing K] (u v : ℕ → K)
    (hu : ∀ n, u (n + 10) = (-1) * u n + 10 * u (n + 1) - 45 * u (n + 2) + 120 * u (n + 3) - 210 * u (n + 4) + 252 * u (n + 5) - 210 * u (n + 6) + 120 * u (n + 7) - 45 * u (n + 8) + 10 * u (n + 9))
    (hv : ∀ n, v (n + 10) = (-1) * v n + 10 * v (n + 1) - 45 * v (n + 2) + 120 * v (n + 3) - 210 * v (n + 4) + 252 * v (n + 5) - 210 * v (n + 6) + 120 * v (n + 7) - 45 * v (n + 8) + 10 * v (n + 9))
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) (h3 : u 3 = v 3) (h4 : u 4 = v 4) (h5 : u 5 = v 5) (h6 : u 6 = v 6) (h7 : u 7 = v 7) (h8 : u 8 = v 8) (h9 : u 9 = v 9) : ∀ n, u n = v n := by
  have key : ∀ n, u n = v n ∧ u (n + 1) = v (n + 1) ∧ u (n + 2) = v (n + 2) ∧ u (n + 3) = v (n + 3) ∧ u (n + 4) = v (n + 4) ∧ u (n + 5) = v (n + 5) ∧ u (n + 6) = v (n + 6) ∧ u (n + 7) = v (n + 7) ∧ u (n + 8) = v (n + 8) ∧ u (n + 9) = v (n + 9) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    | succ n ih =>
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ih
      refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, ?_⟩
      rw [show n + 1 + 9 = n + 10 from rfl, hu, hv, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  exact fun n => (key n).1

def adjT : List (List (List (List R))) := [[[[![0, 0, 0], ![0, 0, 1], ![0, 0, 2], ![0, 0, 3], ![0, 1, 0], ![0, 1, 1], ![0, 1, 2], ![0, 1, 3], ![0, 2, 0], ![0, 2, 1], ![0, 2, 2], ![0, 2, 3], ![0, 3, 0], ![0, 3, 1], ![0, 3, 2], ![0, 3, 3], ![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 0, 3], ![1, 1, 0], ![1, 1, 1], ![1, 1, 2], ![1, 1, 3], ![1, 2, 0], ![1, 2, 1], ![1, 2, 2], ![1, 2, 3], ![1, 3, 0], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 0, 0], ![2, 0, 1], ![2, 0, 2], ![2, 0, 3], ![2, 1, 0], ![2, 1, 1], ![2, 1, 2], ![2, 1, 3], ![2, 2, 0], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 0], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 0, 0], ![3, 0, 1], ![3, 0, 2], ![3, 0, 3], ![3, 1, 0], ![3, 1, 1], ![3, 1, 2], ![3, 1, 3], ![3, 2, 0], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![0, 0, 1], ![0, 0, 2], ![0, 0, 3], ![0, 1, 1], ![0, 1, 2], ![0, 1, 3], ![0, 2, 1], ![0, 2, 2], ![0, 2, 3], ![0, 3, 1], ![0, 3, 2], ![0, 3, 3], ![1, 0, 1], ![1, 0, 2], ![1, 0, 3], ![1, 1, 1], ![1, 1, 2], ![1, 1, 3], ![1, 2, 1], ![1, 2, 2], ![1, 2, 3], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 0, 1], ![2, 0, 2], ![2, 0, 3], ![2, 1, 1], ![2, 1, 2], ![2, 1, 3], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 0, 1], ![3, 0, 2], ![3, 0, 3], ![3, 1, 1], ![3, 1, 2], ![3, 1, 3], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![0, 0, 2], ![0, 0, 3], ![0, 1, 2], ![0, 1, 3], ![0, 2, 2], ![0, 2, 3], ![0, 3, 2], ![0, 3, 3], ![1, 0, 2], ![1, 0, 3], ![1, 1, 2], ![1, 1, 3], ![1, 2, 2], ![1, 2, 3], ![1, 3, 2], ![1, 3, 3], ![2, 0, 2], ![2, 0, 3], ![2, 1, 2], ![2, 1, 3], ![2, 2, 2], ![2, 2, 3], ![2, 3, 2], ![2, 3, 3], ![3, 0, 2], ![3, 0, 3], ![3, 1, 2], ![3, 1, 3], ![3, 2, 2], ![3, 2, 3], ![3, 3, 2], ![3, 3, 3]], [![0, 0, 3], ![0, 1, 3], ![0, 2, 3], ![0, 3, 3], ![1, 0, 3], ![1, 1, 3], ![1, 2, 3], ![1, 3, 3], ![2, 0, 3], ![2, 1, 3], ![2, 2, 3], ![2, 3, 3], ![3, 0, 3], ![3, 1, 3], ![3, 2, 3], ![3, 3, 3]]], [[![0, 1, 0], ![0, 1, 1], ![0, 1, 2], ![0, 1, 3], ![0, 2, 0], ![0, 2, 1], ![0, 2, 2], ![0, 2, 3], ![0, 3, 0], ![0, 3, 1], ![0, 3, 2], ![0, 3, 3], ![1, 1, 0], ![1, 1, 1], ![1, 1, 2], ![1, 1, 3], ![1, 2, 0], ![1, 2, 1], ![1, 2, 2], ![1, 2, 3], ![1, 3, 0], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 1, 0], ![2, 1, 1], ![2, 1, 2], ![2, 1, 3], ![2, 2, 0], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 0], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 1, 0], ![3, 1, 1], ![3, 1, 2], ![3, 1, 3], ![3, 2, 0], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![0, 1, 1], ![0, 1, 2], ![0, 1, 3], ![0, 2, 1], ![0, 2, 2], ![0, 2, 3], ![0, 3, 1], ![0, 3, 2], ![0, 3, 3], ![1, 1, 1], ![1, 1, 2], ![1, 1, 3], ![1, 2, 1], ![1, 2, 2], ![1, 2, 3], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 1, 1], ![2, 1, 2], ![2, 1, 3], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 1, 1], ![3, 1, 2], ![3, 1, 3], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![0, 1, 2], ![0, 1, 3], ![0, 2, 2], ![0, 2, 3], ![0, 3, 2], ![0, 3, 3], ![1, 1, 2], ![1, 1, 3], ![1, 2, 2], ![1, 2, 3], ![1, 3, 2], ![1, 3, 3], ![2, 1, 2], ![2, 1, 3], ![2, 2, 2], ![2, 2, 3], ![2, 3, 2], ![2, 3, 3], ![3, 1, 2], ![3, 1, 3], ![3, 2, 2], ![3, 2, 3], ![3, 3, 2], ![3, 3, 3]], [![0, 1, 3], ![0, 2, 3], ![0, 3, 3], ![1, 1, 3], ![1, 2, 3], ![1, 3, 3], ![2, 1, 3], ![2, 2, 3], ![2, 3, 3], ![3, 1, 3], ![3, 2, 3], ![3, 3, 3]]], [[![0, 2, 0], ![0, 2, 1], ![0, 2, 2], ![0, 2, 3], ![0, 3, 0], ![0, 3, 1], ![0, 3, 2], ![0, 3, 3], ![1, 2, 0], ![1, 2, 1], ![1, 2, 2], ![1, 2, 3], ![1, 3, 0], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 2, 0], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 0], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 2, 0], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![0, 2, 1], ![0, 2, 2], ![0, 2, 3], ![0, 3, 1], ![0, 3, 2], ![0, 3, 3], ![1, 2, 1], ![1, 2, 2], ![1, 2, 3], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![0, 2, 2], ![0, 2, 3], ![0, 3, 2], ![0, 3, 3], ![1, 2, 2], ![1, 2, 3], ![1, 3, 2], ![1, 3, 3], ![2, 2, 2], ![2, 2, 3], ![2, 3, 2], ![2, 3, 3], ![3, 2, 2], ![3, 2, 3], ![3, 3, 2], ![3, 3, 3]], [![0, 2, 3], ![0, 3, 3], ![1, 2, 3], ![1, 3, 3], ![2, 2, 3], ![2, 3, 3], ![3, 2, 3], ![3, 3, 3]]], [[![0, 3, 0], ![0, 3, 1], ![0, 3, 2], ![0, 3, 3], ![1, 3, 0], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 3, 0], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![0, 3, 1], ![0, 3, 2], ![0, 3, 3], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![0, 3, 2], ![0, 3, 3], ![1, 3, 2], ![1, 3, 3], ![2, 3, 2], ![2, 3, 3], ![3, 3, 2], ![3, 3, 3]], [![0, 3, 3], ![1, 3, 3], ![2, 3, 3], ![3, 3, 3]]]], [[[![1, 0, 0], ![1, 0, 1], ![1, 0, 2], ![1, 0, 3], ![1, 1, 0], ![1, 1, 1], ![1, 1, 2], ![1, 1, 3], ![1, 2, 0], ![1, 2, 1], ![1, 2, 2], ![1, 2, 3], ![1, 3, 0], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 0, 0], ![2, 0, 1], ![2, 0, 2], ![2, 0, 3], ![2, 1, 0], ![2, 1, 1], ![2, 1, 2], ![2, 1, 3], ![2, 2, 0], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 0], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 0, 0], ![3, 0, 1], ![3, 0, 2], ![3, 0, 3], ![3, 1, 0], ![3, 1, 1], ![3, 1, 2], ![3, 1, 3], ![3, 2, 0], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [], [], []], [[![1, 1, 0], ![1, 1, 1], ![1, 1, 2], ![1, 1, 3], ![1, 2, 0], ![1, 2, 1], ![1, 2, 2], ![1, 2, 3], ![1, 3, 0], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 1, 0], ![2, 1, 1], ![2, 1, 2], ![2, 1, 3], ![2, 2, 0], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 0], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 1, 0], ![3, 1, 1], ![3, 1, 2], ![3, 1, 3], ![3, 2, 0], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![1, 1, 1], ![1, 1, 2], ![1, 1, 3], ![1, 2, 1], ![1, 2, 2], ![1, 2, 3], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 1, 1], ![2, 1, 2], ![2, 1, 3], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 1, 1], ![3, 1, 2], ![3, 1, 3], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![1, 1, 2], ![1, 1, 3], ![1, 2, 2], ![1, 2, 3], ![1, 3, 2], ![1, 3, 3], ![2, 1, 2], ![2, 1, 3], ![2, 2, 2], ![2, 2, 3], ![2, 3, 2], ![2, 3, 3], ![3, 1, 2], ![3, 1, 3], ![3, 2, 2], ![3, 2, 3], ![3, 3, 2], ![3, 3, 3]], [![1, 1, 3], ![1, 2, 3], ![1, 3, 3], ![2, 1, 3], ![2, 2, 3], ![2, 3, 3], ![3, 1, 3], ![3, 2, 3], ![3, 3, 3]]], [[![1, 2, 0], ![1, 2, 1], ![1, 2, 2], ![1, 2, 3], ![1, 3, 0], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 2, 0], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 0], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 2, 0], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![1, 2, 1], ![1, 2, 2], ![1, 2, 3], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![1, 2, 2], ![1, 2, 3], ![1, 3, 2], ![1, 3, 3], ![2, 2, 2], ![2, 2, 3], ![2, 3, 2], ![2, 3, 3], ![3, 2, 2], ![3, 2, 3], ![3, 3, 2], ![3, 3, 3]], [![1, 2, 3], ![1, 3, 3], ![2, 2, 3], ![2, 3, 3], ![3, 2, 3], ![3, 3, 3]]], [[![1, 3, 0], ![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 3, 0], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![1, 3, 1], ![1, 3, 2], ![1, 3, 3], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![1, 3, 2], ![1, 3, 3], ![2, 3, 2], ![2, 3, 3], ![3, 3, 2], ![3, 3, 3]], [![1, 3, 3], ![2, 3, 3], ![3, 3, 3]]]], [[[![2, 0, 0], ![2, 0, 1], ![2, 0, 2], ![2, 0, 3], ![2, 1, 0], ![2, 1, 1], ![2, 1, 2], ![2, 1, 3], ![2, 2, 0], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 0], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 0, 0], ![3, 0, 1], ![3, 0, 2], ![3, 0, 3], ![3, 1, 0], ![3, 1, 1], ![3, 1, 2], ![3, 1, 3], ![3, 2, 0], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [], [], []], [[![2, 1, 0], ![2, 1, 1], ![2, 1, 2], ![2, 1, 3], ![2, 2, 0], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 0], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 1, 0], ![3, 1, 1], ![3, 1, 2], ![3, 1, 3], ![3, 2, 0], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![2, 1, 1], ![2, 1, 2], ![2, 1, 3], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 1, 1], ![3, 1, 2], ![3, 1, 3], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [], []], [[![2, 2, 0], ![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 0], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 2, 0], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![2, 2, 1], ![2, 2, 2], ![2, 2, 3], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![2, 2, 2], ![2, 2, 3], ![2, 3, 2], ![2, 3, 3], ![3, 2, 2], ![3, 2, 3], ![3, 3, 2], ![3, 3, 3]], [![2, 2, 3], ![2, 3, 3], ![3, 2, 3], ![3, 3, 3]]], [[![2, 3, 0], ![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![2, 3, 1], ![2, 3, 2], ![2, 3, 3], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![2, 3, 2], ![2, 3, 3], ![3, 3, 2], ![3, 3, 3]], [![2, 3, 3], ![3, 3, 3]]]], [[[![3, 0, 0], ![3, 0, 1], ![3, 0, 2], ![3, 0, 3], ![3, 1, 0], ![3, 1, 1], ![3, 1, 2], ![3, 1, 3], ![3, 2, 0], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [], [], []], [[![3, 1, 0], ![3, 1, 1], ![3, 1, 2], ![3, 1, 3], ![3, 2, 0], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![3, 1, 1], ![3, 1, 2], ![3, 1, 3], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [], []], [[![3, 2, 0], ![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![3, 2, 1], ![3, 2, 2], ![3, 2, 3], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![3, 2, 2], ![3, 2, 3], ![3, 3, 2], ![3, 3, 3]], []], [[![3, 3, 0], ![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![3, 3, 1], ![3, 3, 2], ![3, 3, 3]], [![3, 3, 2], ![3, 3, 3]], [![3, 3, 3]]]]]

def adjL (s : R) : List R := (((adjT).getD (s 0).val []).getD (s 1).val []).getD (s 2).val []

def AP (s : R) : Prop := ∀ t : R, (ok s ∧ compat s t) ↔ t ∈ adjL s

theorem ADJ : ∀ s : R, AP s := by
  simp only [AP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem ND : ∀ s : R, (adjL s).Nodup := by
  simp only [forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem sum_adj (s : R) (f : R → ℤ) :
    (∑ t : R, if ok s ∧ compat s t then f t else 0) = ((adjL s).map f).sum := by
  have h1 : ∀ t, (if ok s ∧ compat s t then f t else 0) = if t ∈ adjL s then f t else 0 :=
    fun t => if_congr (ADJ s t) rfl rfl
  rw [Finset.sum_congr rfl (fun t _ => h1 t), ← Finset.sum_filter, ← List.sum_toFinset f (ND s)]
  congr 1
  ext t
  simp

def TP (j : ℕ) (s : R) : Prop := ((adjL s).map (α j)).sum = α (j + 1) s

theorem TL0 : ∀ s : R, TP 0 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T0 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 0 t else 0) = α 1 s := by
  rw [sum_adj]
  exact TL0 s

theorem TL1 : ∀ s : R, TP 1 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T1 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 1 t else 0) = α 2 s := by
  rw [sum_adj]
  exact TL1 s

theorem TL2 : ∀ s : R, TP 2 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T2 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 2 t else 0) = α 3 s := by
  rw [sum_adj]
  exact TL2 s

theorem TL3 : ∀ s : R, TP 3 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T3 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 3 t else 0) = α 4 s := by
  rw [sum_adj]
  exact TL3 s

theorem TL4 : ∀ s : R, TP 4 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T4 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 4 t else 0) = α 5 s := by
  rw [sum_adj]
  exact TL4 s

theorem TL5 : ∀ s : R, TP 5 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T5 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 5 t else 0) = α 6 s := by
  rw [sum_adj]
  exact TL5 s

theorem TL6 : ∀ s : R, TP 6 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T6 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 6 t else 0) = α 7 s := by
  rw [sum_adj]
  exact TL6 s

theorem TL7 : ∀ s : R, TP 7 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T7 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 7 t else 0) = α 8 s := by
  rw [sum_adj]
  exact TL7 s

theorem TL8 : ∀ s : R, TP 8 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T8 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 8 t else 0) = α 9 s := by
  rw [sum_adj]
  exact TL8 s

theorem TL9 : ∀ s : R, TP 9 s := by
  simp only [TP, forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem T9 (s : R) : (∑ t : R, if ok s ∧ compat s t then α 9 t else 0) = α 10 s := by
  rw [sum_adj]
  exact TL9 s

theorem T (s : R) : ∀ n, (∑ t : R, if ok s ∧ compat s t then α n t else 0) = α (n + 1) s := by
  apply uniqP (fun n => ∑ t : R, if ok s ∧ compat s t then α n t else 0) (fun n => α (n + 1) s)
  · intro n
    simp only [α_rec, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t _
    split_ifs <;> ring
  · intro n
    exact α_rec (n + 1) s
  · exact T0 s
  · exact T1 s
  · exact T2 s
  · exact T3 s
  · exact T4 s
  · exact T5 s
  · exact T6 s
  · exact T7 s
  · exact T8 s
  · exact T9 s

theorem B0 : ∀ s : R, α 0 s = if ok s then 1 else 0 := by
  simp only [forall_vecCons, forall_vecEmpty]
  decide +kernel

theorem F_eq (n : ℕ) : ∀ s : R, (F n s : ℤ) = α n s := by
  induction n with
  | zero =>
    intro s
    rw [F_zero, B0]
    split_ifs <;> simp
  | succ n ih =>
    intro s
    rw [F_succ, ← T s n]
    push_cast
    apply Finset.sum_congr rfl
    intro t _
    split_ifs
    · exact ih t
    · rfl

def A : ℕ → ℤ
  | 0 => 50
  | 1 => 684
  | 2 => 5029
  | 3 => 25410
  | 4 => 99634
  | 5 => 325120
  | 6 => 922768
  | 7 => 2346883
  | 8 => 5462600
  | 9 => 11818092
  | n + 10 => (-1) * A n + 10 * A (n + 1) - 45 * A (n + 2) + 120 * A (n + 3) - 210 * A (n + 4) + 252 * A (n + 5) - 210 * A (n + 6) + 120 * A (n + 7) - 45 * A (n + 8) + 10 * A (n + 9)

theorem A_rec (n : ℕ) : A (n + 10) = (-1) * A n + 10 * A (n + 1) - 45 * A (n + 2) + 120 * A (n + 3) - 210 * A (n + 4) + 252 * A (n + 5) - 210 * A (n + 6) + 120 * A (n + 7) - 45 * A (n + 8) + 10 * A (n + 9) := by
  rw [A]

theorem U0 : (∑ s : R, if True then α 0 s else 0) = A 0 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U1 : (∑ s : R, if True then α 1 s else 0) = A 1 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U2 : (∑ s : R, if True then α 2 s else 0) = A 2 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U3 : (∑ s : R, if True then α 3 s else 0) = A 3 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U4 : (∑ s : R, if True then α 4 s else 0) = A 4 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U5 : (∑ s : R, if True then α 5 s else 0) = A 5 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U6 : (∑ s : R, if True then α 6 s else 0) = A 6 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U7 : (∑ s : R, if True then α 7 s else 0) = A 7 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U8 : (∑ s : R, if True then α 8 s else 0) = A 8 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U9 : (∑ s : R, if True then α 9 s else 0) = A 9 := by
  simp only [sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem U : ∀ n, (∑ s : R, if True then α n s else 0) = A n := by
  apply uniqP (fun n => ∑ s : R, if True then α n s else 0) A
  · intro n
    simp only [α_rec, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _
    split_ifs <;> ring
  · exact A_rec
  · exact U0
  · exact U1
  · exact U2
  · exact U3
  · exact U4
  · exact U5
  · exact U6
  · exact U7
  · exact U8
  · exact U9

theorem N_eq (n : ℕ) : (a (n + 1) : ℤ) = A n := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight
      (p := fun x : Fin (n + 1) → R => (∀ i, Unimodal (x i)) ∧ ∀ j, Monotone (fun i => x i j))
      (q := fun y : Fin (n + 1) → R => Walk y)
      (fun x => and_congr Iff.rfl ⟨fun h i j => Fin.monotone_iff_le_succ.mp (h j) i,
        fun h j => Fin.monotone_iff_le_succ.mpr (fun i => h i j)⟩)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter, sum_F, ← U n]
  push_cast
  apply Finset.sum_congr rfl
  intro s _
  exact F_eq n s

def C : ℕ → ℤ
  | 0 => 50
  | 1 => 684
  | 2 => 5029
  | 3 => 25410
  | 4 => 99634
  | 5 => 325120
  | 6 => 922768
  | 7 => 2346883
  | 8 => 5462600
  | 9 => 11818092
  | n + 10 => (-1) * C n + 10 * C (n + 1) - 45 * C (n + 2) + 120 * C (n + 3) - 210 * C (n + 4) + 252 * C (n + 5) - 210 * C (n + 6) + 120 * C (n + 7) - 45 * C (n + 8) + 10 * C (n + 9)

theorem C_rec (n : ℕ) : C (n + 10) = (-1) * C n + 10 * C (n + 1) - 45 * C (n + 2) + 120 * C (n + 3) - 210 * C (n + 4) + 252 * C (n + 5) - 210 * C (n + 6) + 120 * C (n + 7) - 45 * C (n + 8) + 10 * C (n + 9) := by
  rw [C]

theorem C_P (n : ℕ) : C (n + 10) = (-1) * C n + 10 * C (n + 1) - 45 * C (n + 2) + 120 * C (n + 3) - 210 * C (n + 4) + 252 * C (n + 5) - 210 * C (n + 6) + 120 * C (n + 7) - 45 * C (n + 8) + 10 * C (n + 9) := by
  have h0 : C (n + 10) = (-1) * C n + 10 * C (n + 1) - 45 * C (n + 2) + 120 * C (n + 3) - 210 * C (n + 4) + 252 * C (n + 5) - 210 * C (n + 6) + 120 * C (n + 7) - 45 * C (n + 8) + 10 * C (n + 9) := C_rec (n)
  linear_combination (1) * h0

theorem A_C : ∀ n, A (n + 0) = 1 * C n := by
  apply uniqP (fun n => A (n + 0)) (fun n => 1 * C n)
  · intro n
    exact A_rec (n + 0)
  · intro n
    rw [C_P]
    ring
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem aC (n : ℕ) : (a (n + 1) : ℤ) = C n := by
  rw [show (a (n + 1) : ℤ) = A (n + 0) from N_eq (n + 0), A_C]
  ring

theorem uniqp {K : Type} [CommRing K] (u v : ℕ → K)
    (hu : ∀ n, u (n + 10) = (-1) * u n + 10 * u (n + 1) - 45 * u (n + 2) + 120 * u (n + 3) - 210 * u (n + 4) + 252 * u (n + 5) - 210 * u (n + 6) + 120 * u (n + 7) - 45 * u (n + 8) + 10 * u (n + 9))
    (hv : ∀ n, v (n + 10) = (-1) * v n + 10 * v (n + 1) - 45 * v (n + 2) + 120 * v (n + 3) - 210 * v (n + 4) + 252 * v (n + 5) - 210 * v (n + 6) + 120 * v (n + 7) - 45 * v (n + 8) + 10 * v (n + 9))
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) (h3 : u 3 = v 3) (h4 : u 4 = v 4) (h5 : u 5 = v 5) (h6 : u 6 = v 6) (h7 : u 7 = v 7) (h8 : u 8 = v 8) (h9 : u 9 = v 9) : ∀ n, u n = v n := by
  have key : ∀ n, u n = v n ∧ u (n + 1) = v (n + 1) ∧ u (n + 2) = v (n + 2) ∧ u (n + 3) = v (n + 3) ∧ u (n + 4) = v (n + 4) ∧ u (n + 5) = v (n + 5) ∧ u (n + 6) = v (n + 6) ∧ u (n + 7) = v (n + 7) ∧ u (n + 8) = v (n + 8) ∧ u (n + 9) = v (n + 9) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
    | succ n ih =>
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := ih
      refine ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, ?_⟩
      rw [show n + 1 + 9 = n + 10 from rfl, hu, hv, a0, a1, a2, a3, a4, a5, a6, a7, a8, a9]
  exact fun n => (key n).1

theorem rec_k (k : ℕ) : (a (k + 11) : ℤ) = 10 * (a (k + 10) : ℤ) - 45 * (a (k + 9) : ℤ) + 120 * (a (k + 8) : ℤ) - 210 * (a (k + 7) : ℤ) + 252 * (a (k + 6) : ℤ) - 210 * (a (k + 5) : ℤ) + 120 * (a (k + 4) : ℤ) - 45 * (a (k + 3) : ℤ) + 10 * (a (k + 2) : ℤ) - 1 * (a (k + 1) : ℤ) := by
  have e0 : (a (k + 11) : ℤ) = C (k + 10) := aC (k + 10)
  have e1 : (a (k + 10) : ℤ) = C (k + 9) := aC (k + 9)
  have e2 : (a (k + 9) : ℤ) = C (k + 8) := aC (k + 8)
  have e3 : (a (k + 8) : ℤ) = C (k + 7) := aC (k + 7)
  have e4 : (a (k + 7) : ℤ) = C (k + 6) := aC (k + 6)
  have e5 : (a (k + 6) : ℤ) = C (k + 5) := aC (k + 5)
  have e6 : (a (k + 5) : ℤ) = C (k + 4) := aC (k + 4)
  have e7 : (a (k + 4) : ℤ) = C (k + 3) := aC (k + 3)
  have e8 : (a (k + 3) : ℤ) = C (k + 2) := aC (k + 2)
  have e9 : (a (k + 2) : ℤ) = C (k + 1) := aC (k + 1)
  have e10 : (a (k + 1) : ℤ) = C (k) := aC (k)
  linear_combination e0 - (10) * e1 - (-45) * e2 - (120) * e3 - (-210) * e4 - (252) * e5 - (-210) * e6 - (120) * e7 - (-45) * e8 - (10) * e9 - (-1) * e10 + C_rec k

theorem a_v1 : a 1 = 50 := by
  have h := N_eq 0
  rw [show A 0 = 50 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v2 : a 2 = 684 := by
  have h := N_eq 1
  rw [show A 1 = 684 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v3 : a 3 = 5029 := by
  have h := N_eq 2
  rw [show A 2 = 5029 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v4 : a 4 = 25410 := by
  have h := N_eq 3
  rw [show A 3 = 25410 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v5 : a 5 = 99634 := by
  have h := N_eq 4
  rw [show A 4 = 99634 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v6 : a 6 = 325120 := by
  have h := N_eq 5
  rw [show A 5 = 325120 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v7 : a 7 = 922768 := by
  have h := N_eq 6
  rw [show A 6 = 922768 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v8 : a 8 = 2346883 := by
  have h := N_eq 7
  rw [show A 7 = 2346883 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v9 : a 9 = 5462600 := by
  have h := N_eq 8
  rw [show A 8 = 5462600 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v10 : a 10 = 11818092 := by
  have h := N_eq 9
  rw [show A 9 = 11818092 from by decide +kernel] at h
  exact_mod_cast h

theorem closedC : ∀ m : ℕ, ((C (m + 0) : ℤ) : ℚ) = (1 : ℚ) + (6491/1260 : ℚ) * ((m + 1 : ℕ) : ℚ) + (715/63 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 2 + (159679/11340 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 3 + (1565/144 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 4 + (46793/8640 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 5 + (251/144 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 6 + (10571/30240 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 7 + (5/126 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 8 + (353/181440 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 9 := by
  apply uniqp (fun m : ℕ => ((C (m + 0) : ℤ) : ℚ)) (fun m : ℕ => (1 : ℚ) + (6491/1260 : ℚ) * ((m + 1 : ℕ) : ℚ) + (715/63 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 2 + (159679/11340 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 3 + (1565/144 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 4 + (46793/8640 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 5 + (251/144 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 6 + (10571/30240 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 7 + (5/126 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 8 + (353/181440 : ℚ) * ((m + 1 : ℕ) : ℚ) ^ 9)
  · intro m
    have h := congrArg (Int.cast : ℤ → ℚ) (C_rec (m + 0))
    push_cast at h
    exact h
  · intro m
    push_cast
    ring
  · show ((C (0 + 0) : ℤ) : ℚ) = _
    rw [show C (0 + 0) = 50 from by decide +kernel]
    norm_num
  · show ((C (1 + 0) : ℤ) : ℚ) = _
    rw [show C (1 + 0) = 684 from by decide +kernel]
    norm_num
  · show ((C (2 + 0) : ℤ) : ℚ) = _
    rw [show C (2 + 0) = 5029 from by decide +kernel]
    norm_num
  · show ((C (3 + 0) : ℤ) : ℚ) = _
    rw [show C (3 + 0) = 25410 from by decide +kernel]
    norm_num
  · show ((C (4 + 0) : ℤ) : ℚ) = _
    rw [show C (4 + 0) = 99634 from by decide +kernel]
    norm_num
  · show ((C (5 + 0) : ℤ) : ℚ) = _
    rw [show C (5 + 0) = 325120 from by decide +kernel]
    norm_num
  · show ((C (6 + 0) : ℤ) : ℚ) = _
    rw [show C (6 + 0) = 922768 from by decide +kernel]
    norm_num
  · show ((C (7 + 0) : ℤ) : ℚ) = _
    rw [show C (7 + 0) = 2346883 from by decide +kernel]
    norm_num
  · show ((C (8 + 0) : ℤ) : ℚ) = _
    rw [show C (8 + 0) = 5462600 from by decide +kernel]
    norm_num
  · show ((C (9 + 0) : ℤ) : ℚ) = _
    rw [show C (9 + 0) = 11818092 from by decide +kernel]
    norm_num

end OMAA223982Helpers

open OMA.S_oeis_a223982 OMAA223982Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a223982.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
    rw [show k + 11 - 1 = k + 10 by omega, show k + 11 - 2 = k + 9 by omega, show k + 11 - 3 = k + 8 by omega, show k + 11 - 4 = k + 7 by omega, show k + 11 - 5 = k + 6 by omega, show k + 11 - 6 = k + 5 by omega, show k + 11 - 7 = k + 4 by omega, show k + 11 - 8 = k + 3 by omega, show k + 11 - 9 = k + 2 by omega, show k + 11 - 10 = k + 1 by omega]
    exact rec_k k
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * ((1 - PowerSeries.X) ^ 10) =
        F' - PowerSeries.C (10 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (45 : ℚ) * (PowerSeries.X ^ 2 * F') - PowerSeries.C (120 : ℚ) * (PowerSeries.X ^ 3 * F') + PowerSeries.C (210 : ℚ) * (PowerSeries.X ^ 4 * F') - PowerSeries.C (252 : ℚ) * (PowerSeries.X ^ 5 * F') + PowerSeries.C (210 : ℚ) * (PowerSeries.X ^ 6 * F') - PowerSeries.C (120 : ℚ) * (PowerSeries.X ^ 7 * F') + PowerSeries.C (45 : ℚ) * (PowerSeries.X ^ 8 * F') - PowerSeries.C (10 : ℚ) * (PowerSeries.X ^ 9 * F') + PowerSeries.C (1 : ℚ) * (PowerSeries.X ^ 10 * F') := by
      simp only [map_ofNat, map_one]
      ring
    have e2 : (50 * PowerSeries.X + 184 * PowerSeries.X ^ 2 + 439 * PowerSeries.X ^ 3 - 100 * PowerSeries.X ^ 4 + 259 * PowerSeries.X ^ 5 - 210 * PowerSeries.X ^ 6 + 120 * PowerSeries.X ^ 7 - 45 * PowerSeries.X ^ 8 + 10 * PowerSeries.X ^ 9 - 1 * PowerSeries.X ^ 10 : PowerSeries ℚ) =
        PowerSeries.C (50 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (184 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (439 : ℚ) * PowerSeries.X ^ 3 - PowerSeries.C (100 : ℚ) * PowerSeries.X ^ 4 + PowerSeries.C (259 : ℚ) * PowerSeries.X ^ 5 - PowerSeries.C (210 : ℚ) * PowerSeries.X ^ 6 + PowerSeries.C (120 : ℚ) * PowerSeries.X ^ 7 - PowerSeries.C (45 : ℚ) * PowerSeries.X ^ 8 + PowerSeries.C (10 : ℚ) * PowerSeries.X ^ 9 - PowerSeries.C (1 : ℚ) * PowerSeries.X ^ 10 := by
      simp only [map_ofNat, map_one]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 10
    · interval_cases n <;> norm_num [a_v1, a_v2, a_v3, a_v4, a_v5, a_v6, a_v7, a_v8, a_v9, a_v10]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 11 := ⟨n - 11, by omega⟩
      have h := rec_k (j)
      have q := congrArg (Int.cast : ℤ → ℚ) h
      push_cast at q
      simp
      linear_combination q
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h := congrArg (Int.cast : ℤ → ℚ) (aC (k))
    push_cast at h
    have h2 := closedC k
    rw [show (a (k + 1) : ℚ) = ((C (k) : ℤ) : ℚ) from h]
    exact h2
