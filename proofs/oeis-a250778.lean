import OMAStatements.S_oeis_a250778
import Mathlib

-- Proof of the conjectures in OEIS A250778 (statement by @ivillar).
-- Idea: the conditions involve only consecutive rows, so the count is a walk count on rows (transfer matrix).
-- For each row s, the number α(n, s) of walks with n steps starting at s is tabulated for n < 6; the tables satisfy
-- the transfer relation (checked by kernel computation) and a linear recurrence of order 6 with the characteristic
-- polynomial of the conjectured recurrence as a factor. Sequences with the same recurrence and initial values agree,
-- which gives the recurrence, the g.f. and the closed form.

namespace OMAA250778Helpers

open OMA.S_oeis_a250778

abbrev R := Fin 4 → Fin 2

instance (u v : R) : Decidable (PairOK u v) := by unfold PairOK; infer_instance


abbrev ok (_r : R) : Prop := True

abbrev compat (r s : R) : Prop := PairOK r s


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

def look (l : List (List (List (List (ℤ))))) (s : R) : ℤ := ((((l).getD (s 0).val []).getD (s 1).val []).getD (s 2).val []).getD (s 3).val 0

def tab0 : List (List (List (List (ℤ)))) := [[[[1, 1], [1, 1]], [[1, 1], [1, 1]]], [[[1, 1], [1, 1]], [[1, 1], [1, 1]]]]

def tab1 : List (List (List (List (ℤ)))) := [[[[5, 4], [4, 1]], [[4, 3], [2, 1]]], [[[5, 4], [4, 1]], [[3, 2], [2, 1]]]]

def tab2 : List (List (List (List (ℤ)))) := [[[[12, 12], [10, 1]], [[9, 9], [3, 1]]], [[[12, 12], [10, 1]], [[6, 4], [3, 1]]]]

def tab3 : List (List (List (List (ℤ)))) := [[[[27, 28], [24, 1]], [[20, 22], [4, 1]]], [[[27, 28], [24, 1]], [[11, 7], [4, 1]]]]

def tab4 : List (List (List (List (ℤ)))) := [[[[58, 60], [54, 1]], [[44, 50], [5, 1]]], [[[58, 60], [54, 1]], [[19, 11], [5, 1]]]]

def tab5 : List (List (List (List (ℤ)))) := [[[[121, 124], [116, 1]], [[96, 109], [6, 1]]], [[[121, 124], [116, 1]], [[31, 16], [6, 1]]]]

def α : ℕ → R → ℤ
  | 0, s => look tab0 s
  | 1, s => look tab1 s
  | 2, s => look tab2 s
  | 3, s => look tab3 s
  | 4, s => look tab4 s
  | 5, s => look tab5 s
  | n + 6, s => 2 * α (n + 1) s - 9 * α (n + 2) s + 16 * α (n + 3) s - 14 * α (n + 4) s + 6 * α (n + 5) s

theorem α_rec (n : ℕ) (s : R) : α (n + 6) s = 2 * α (n + 1) s - 9 * α (n + 2) s + 16 * α (n + 3) s - 14 * α (n + 4) s + 6 * α (n + 5) s := by
  rw [α]

theorem uniqP {K : Type} [CommRing K] (u v : ℕ → K)
    (hu : ∀ n, u (n + 6) = 2 * u (n + 1) - 9 * u (n + 2) + 16 * u (n + 3) - 14 * u (n + 4) + 6 * u (n + 5))
    (hv : ∀ n, v (n + 6) = 2 * v (n + 1) - 9 * v (n + 2) + 16 * v (n + 3) - 14 * v (n + 4) + 6 * v (n + 5))
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) (h3 : u 3 = v 3) (h4 : u 4 = v 4) (h5 : u 5 = v 5) : ∀ n, u n = v n := by
  have key : ∀ n, u n = v n ∧ u (n + 1) = v (n + 1) ∧ u (n + 2) = v (n + 2) ∧ u (n + 3) = v (n + 3) ∧ u (n + 4) = v (n + 4) ∧ u (n + 5) = v (n + 5) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1, h2, h3, h4, h5⟩
    | succ n ih =>
      obtain ⟨a0, a1, a2, a3, a4, a5⟩ := ih
      refine ⟨a1, a2, a3, a4, a5, ?_⟩
      rw [show n + 1 + 5 = n + 6 from rfl, hu, hv, a1, a2, a3, a4, a5]
  exact fun n => (key n).1

theorem T0 : ∀ s : R, (∑ t : R, if ok s ∧ compat s t then α 0 t else 0) = α 1 s := by
  simp only [forall_vecCons, forall_vecEmpty, sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem T1 : ∀ s : R, (∑ t : R, if ok s ∧ compat s t then α 1 t else 0) = α 2 s := by
  simp only [forall_vecCons, forall_vecEmpty, sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem T2 : ∀ s : R, (∑ t : R, if ok s ∧ compat s t then α 2 t else 0) = α 3 s := by
  simp only [forall_vecCons, forall_vecEmpty, sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem T3 : ∀ s : R, (∑ t : R, if ok s ∧ compat s t then α 3 t else 0) = α 4 s := by
  simp only [forall_vecCons, forall_vecEmpty, sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem T4 : ∀ s : R, (∑ t : R, if ok s ∧ compat s t then α 4 t else 0) = α 5 s := by
  simp only [forall_vecCons, forall_vecEmpty, sum_vecCons, sum_vecEmpty]
  decide +kernel

theorem T5 : ∀ s : R, (∑ t : R, if ok s ∧ compat s t then α 5 t else 0) = α 6 s := by
  simp only [forall_vecCons, forall_vecEmpty, sum_vecCons, sum_vecEmpty]
  decide +kernel

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
  | 0 => 16
  | 1 => 46
  | 2 => 106
  | 3 => 230
  | 4 => 482
  | 5 => 990
  | n + 6 => 2 * A (n + 1) - 9 * A (n + 2) + 16 * A (n + 3) - 14 * A (n + 4) + 6 * A (n + 5)

theorem A_rec (n : ℕ) : A (n + 6) = 2 * A (n + 1) - 9 * A (n + 2) + 16 * A (n + 3) - 14 * A (n + 4) + 6 * A (n + 5) := by
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

theorem N_eq (n : ℕ) : (a n : ℤ) = A n := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight
      (p := fun x : Fin (n + 1) → R => ∀ i : Fin n, PairOK (x i.castSucc) (x i.succ))
      (q := fun y : Fin (n + 1) → R => Walk y)
      (fun x => ⟨fun h => ⟨fun _ => trivial, h⟩, fun h => h.2⟩)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter, sum_F, ← U n]
  push_cast
  apply Finset.sum_congr rfl
  intro s _
  exact F_eq n s

def C : ℕ → ℤ
  | 0 => 46
  | 1 => 106
  | 2 => 230
  | n + 3 => 2 * C n - 5 * C (n + 1) + 4 * C (n + 2)

theorem C_rec (n : ℕ) : C (n + 3) = 2 * C n - 5 * C (n + 1) + 4 * C (n + 2) := by
  rw [C]

theorem C_P (n : ℕ) : C (n + 6) = 2 * C (n + 1) - 9 * C (n + 2) + 16 * C (n + 3) - 14 * C (n + 4) + 6 * C (n + 5) := by
  have h1 : C (n + 4) = 2 * C (n + 1) - 5 * C (n + 2) + 4 * C (n + 3) := C_rec (n + 1)
  have h2 : C (n + 5) = 2 * C (n + 2) - 5 * C (n + 3) + 4 * C (n + 4) := C_rec (n + 2)
  have h3 : C (n + 6) = 2 * C (n + 3) - 5 * C (n + 4) + 4 * C (n + 5) := C_rec (n + 3)
  linear_combination (1) * h1 + (-2) * h2 + (1) * h3

theorem A_C : ∀ n, A (n + 1) = 1 * C n := by
  apply uniqP (fun n => A (n + 1)) (fun n => 1 * C n)
  · intro n
    exact A_rec (n + 1)
  · intro n
    rw [C_P]
    ring
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem aC (n : ℕ) : (a (n + 1) : ℤ) = C n := by
  rw [N_eq, A_C]
  ring

theorem uniqp {K : Type} [CommRing K] (u v : ℕ → K)
    (hu : ∀ n, u (n + 3) = 2 * u n - 5 * u (n + 1) + 4 * u (n + 2))
    (hv : ∀ n, v (n + 3) = 2 * v n - 5 * v (n + 1) + 4 * v (n + 2))
    (h0 : u 0 = v 0) (h1 : u 1 = v 1) (h2 : u 2 = v 2) : ∀ n, u n = v n := by
  have key : ∀ n, u n = v n ∧ u (n + 1) = v (n + 1) ∧ u (n + 2) = v (n + 2) := by
    intro n
    induction n with
    | zero => exact ⟨h0, h1, h2⟩
    | succ n ih =>
      obtain ⟨a0, a1, a2⟩ := ih
      refine ⟨a1, a2, ?_⟩
      rw [show n + 1 + 2 = n + 3 from rfl, hu, hv, a0, a1, a2]
  exact fun n => (key n).1

theorem rec_k (k : ℕ) : (a (k + 4) : ℤ) = 4 * (a (k + 3) : ℤ) - 5 * (a (k + 2) : ℤ) + 2 * (a (k + 1) : ℤ) := by
  have e0 : (a (k + 4) : ℤ) = C (k + 3) := aC (k + 3)
  have e1 : (a (k + 3) : ℤ) = C (k + 2) := aC (k + 2)
  have e2 : (a (k + 2) : ℤ) = C (k + 1) := aC (k + 1)
  have e3 : (a (k + 1) : ℤ) = C (k) := aC (k)
  linear_combination e0 - (4) * e1 - (-5) * e2 - (2) * e3 + C_rec k

theorem a_v1 : a 1 = 46 := by
  have h := N_eq 1
  rw [show A 1 = 46 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v2 : a 2 = 106 := by
  have h := N_eq 2
  rw [show A 2 = 106 from by decide +kernel] at h
  exact_mod_cast h

theorem a_v3 : a 3 = 230 := by
  have h := N_eq 3
  rw [show A 3 = 230 from by decide +kernel] at h
  exact_mod_cast h

theorem closedC : ∀ m : ℕ, ((C (m + 0) : ℤ) : ℚ) = (2 : ℚ) ^ (5 + (m + 1)) - 4 * ((m + 1 : ℕ) : ℚ) - 14 := by
  apply uniqp (fun m : ℕ => ((C (m + 0) : ℤ) : ℚ)) (fun m : ℕ => (2 : ℚ) ^ (5 + (m + 1)) - 4 * ((m + 1 : ℕ) : ℚ) - 14)
  · intro m
    have h := congrArg (Int.cast : ℤ → ℚ) (C_rec (m + 0))
    push_cast at h
    exact h
  · intro m
    push_cast
    ring
  · show ((C (0 + 0) : ℤ) : ℚ) = _
    rw [show C (0 + 0) = 46 from by decide +kernel]
    norm_num
  · show ((C (1 + 0) : ℤ) : ℚ) = _
    rw [show C (1 + 0) = 106 from by decide +kernel]
    norm_num
  · show ((C (2 + 0) : ℤ) : ℚ) = _
    rw [show C (2 + 0) = 230 from by decide +kernel]
    norm_num

end OMAA250778Helpers

open OMA.S_oeis_a250778 OMAA250778Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a250778.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega]
    exact rec_k k
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * ((1 - PowerSeries.X) ^ 2 * (1 - 2 * PowerSeries.X)) =
        F' - PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 1 * F') + PowerSeries.C (5 : ℚ) * (PowerSeries.X ^ 2 * F') - PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 3 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (46 * PowerSeries.X - 78 * PowerSeries.X ^ 2 + 36 * PowerSeries.X ^ 3 : PowerSeries ℚ) =
        PowerSeries.C (46 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (78 : ℚ) * PowerSeries.X ^ 2 + PowerSeries.C (36 : ℚ) * PowerSeries.X ^ 3 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 3
    · interval_cases n <;> norm_num [a_v1, a_v2, a_v3]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
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
