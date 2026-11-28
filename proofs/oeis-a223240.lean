import OMAStatements.S_oeis_a223240
import Mathlib

-- Proof of the conjectures in OEIS A223240 (statement by @ivillar).
-- Idea: an n X 1 array is a walk of length n-1 in the 3-loop graph (only vertical neighbours exist).
-- Walk counts depend only on whether the start is node 0 (degree 6) or not (degree 2, adjacent to 0 and
-- to its partner): α' = 6β, β' = α + β, a(n+1) = α(n) + 6β(n). The characteristic polynomial
-- t^2 - t - 6 = (t - 3)(t + 2) gives the recurrence, the g.f. and the closed form.

namespace OMAA223240Helpers

open OMA.S_oeis_a223240

instance : DecidableRel edge := fun u v => by unfold edge; infer_instance

abbrev R := Fin 1 → Fin 7

/-- Rows are unconstrained. -/
abbrev ok (_r : R) : Prop := True

/-- Consecutive rows (vertical neighbours) are joined by an edge. -/
abbrev compat (r s : R) : Prop := edge (r 0) (s 0)

abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem walk_cons (n : ℕ) (r : R) (y : Fin (n + 1) → R) :
    Walk (Fin.cons r y : Fin (n + 2) → R) ↔ ok r ∧ compat r (y 0) ∧ Walk y := by
  simp only [Walk, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ, Fin.castSucc_zero,
    Fin.succ_zero_eq_one, ← Fin.succ_castSucc]
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

theorem edge_symm : ∀ u v : Fin 7, edge u v → edge v u := by decide

theorem good_iff (n : ℕ) (x : Fin (n + 1) → R) : Good x ↔ Walk x := by
  constructor
  · intro h
    refine ⟨fun _ => trivial, fun i => ?_⟩
    have := h (i.castSucc, 0) (i.succ, 0)
      (Or.inr ⟨rfl, Or.inr (by simp only [Fin.val_castSucc, Fin.val_succ])⟩)
    exact this
  · rintro ⟨-, hc⟩ p q hpq
    have hp2 : p.2 = 0 := Subsingleton.elim _ _
    have hq2 : q.2 = 0 := Subsingleton.elim _ _
    rcases hpq with ⟨-, h | h⟩ | ⟨-, h | h⟩
    · rw [hp2, hq2] at h; simp at h
    · rw [hp2, hq2] at h; simp at h
    · have hlt : (q.1 : ℕ) < n := by have := p.1.isLt; omega
      have e1 : (⟨q.1, hlt⟩ : Fin n).castSucc = q.1 := Fin.ext rfl
      have e2 : (⟨q.1, hlt⟩ : Fin n).succ = p.1 := Fin.ext (by simp; omega)
      have := hc ⟨q.1, hlt⟩
      simp only [compat, e1, e2] at this
      rw [hp2, hq2]
      exact edge_symm _ _ this
    · have hlt : (p.1 : ℕ) < n := by have := q.1.isLt; omega
      have e1 : (⟨p.1, hlt⟩ : Fin n).castSucc = p.1 := Fin.ext rfl
      have e2 : (⟨p.1, hlt⟩ : Fin n).succ = q.1 := Fin.ext (by simp; omega)
      have := hc ⟨p.1, hlt⟩
      simp only [compat, e1, e2] at this
      rw [hp2, hq2]
      exact this

/-- Walk counts from node 0 (α) and from any other node (β). -/
def α : ℕ → ℕ
  | 0 => 1
  | n + 1 => 6 * β n
where
  β : ℕ → ℕ
  | 0 => 1
  | n + 1 => α n + β n

abbrev Z (t : R) : Prop := t 0 = 0

def V (n : ℕ) (s : R) : ℕ := if Z s then α n else α.β n

theorem cA : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ Z t)).card =
    if Z s then 0 else 1 := by decide

theorem cB : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t)).card =
    if Z s then 6 else 1 := by decide

theorem tA : (Finset.univ.filter (fun t : R => True ∧ Z t)).card = 1 := by decide
theorem tB : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t)).card = 6 := by decide

theorem split_V (n : ℕ) (P : Prop) [Decidable P] (t : R) :
    (if P then V n t else 0) = (if P ∧ Z t then α n else 0) + (if P ∧ ¬ Z t then α.β n else 0) := by
  unfold V
  by_cases h1 : P
  · rw [if_pos h1]
    by_cases h2 : Z t
    · rw [if_pos h2, if_pos (show P ∧ Z t from ⟨h1, h2⟩),
        if_neg (show ¬(P ∧ ¬ Z t) from fun h => h.2 h2)]
      ring
    · rw [if_neg h2, if_neg (show ¬(P ∧ Z t) from fun h => h2 h.2),
        if_pos (show P ∧ ¬ Z t from ⟨h1, h2⟩)]
      ring
  · rw [if_neg h1, if_neg (show ¬(P ∧ Z t) from fun h => h1 h.1),
      if_neg (show ¬(P ∧ ¬ Z t) from fun h => h1 h.1)]

theorem sum_V (n : ℕ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then V n t else 0) =
      (Finset.univ.filter (fun t => P t ∧ Z t)).card * α n +
      (Finset.univ.filter (fun t => P t ∧ ¬ Z t)).card * α.β n := by
  rw [Finset.sum_congr rfl (fun t _ => split_V n (P t) t), Finset.sum_add_distrib,
    Finset.sum_ite, Finset.sum_ite]
  simp only [Finset.sum_const, Finset.sum_const_zero, smul_eq_mul, add_zero, mul_zero]

theorem F_eq (n : ℕ) : ∀ s : R, F n s = V n s := by
  induction n with
  | zero =>
    intro s
    rw [F_zero]
    unfold V
    simp only [ok, if_true]
    split_ifs <;> rfl
  | succ n ih =>
    intro s
    rw [F_succ]
    simp only [ih]
    rw [sum_V n (fun t => ok s ∧ compat s t), cA s, cB s]
    unfold V
    split_ifs <;> simp [α, α.β]

theorem a_succ (n : ℕ) : a (n + 1) = α n + 6 * α.β n := by
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight (good_iff n)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x then 1 else 0) = ∑ s : R, if True then F n s else 0 := by
    unfold F
    simp only [if_true]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    have hh : ∀ s : R, (if Walk y ∧ y 0 = s then 1 else 0) = if y 0 = s then (if Walk y then 1 else 0) else 0 := by
      intro s
      by_cases h : y 0 = s
      · rw [if_pos h]; exact if_congr ⟨fun hh => hh.1, fun hh => ⟨hh, h⟩⟩ rfl rfl
      · rw [if_neg h, if_neg (show ¬(Walk y ∧ y 0 = s) from fun hh => h hh.2)]
    rw [Finset.sum_congr rfl (fun s _ => hh s), Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
  rw [h1]
  simp only [F_eq]
  rw [sum_V n (fun _ => True), tA, tB]
  ring

theorem α_rec (n : ℕ) : α (n + 2) = α (n + 1) + 6 * α n := by
  simp only [α, α.β]; ring

theorem β_rec (n : ℕ) : α.β (n + 2) = α.β (n + 1) + 6 * α.β n := by
  simp only [α, α.β]; ring

theorem a_rec (n : ℕ) : a (n + 3) = a (n + 2) + 6 * a (n + 1) := by
  rw [a_succ, a_succ, a_succ, α_rec, β_rec]
  ring

theorem a_one : a 1 = 7 := by rw [a_succ]; simp [α, α.β]
theorem a_two : a 2 = 18 := by rw [a_succ]; simp [α, α.β]

theorem closed (k : ℕ) : (a (k + 1) : ℚ) = (64 * 3 ^ (k + 1) - 9 * (-2) ^ (k + 1)) / 30 ∧
    (a (k + 2) : ℚ) = (64 * 3 ^ (k + 2) - 9 * (-2) ^ (k + 2)) / 30 := by
  induction k with
  | zero => refine ⟨?_, ?_⟩ <;> norm_num [a_one, a_two]
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h : ((a (k + 3) : ℕ) : ℚ) = ((a (k + 2) + 6 * a (k + 1) : ℕ) : ℚ) := by rw [a_rec]
    push_cast at h
    rw [show k + 1 + 2 = k + 3 from rfl, h, ih.1, ih.2]
    ring

end OMAA223240Helpers

open OMA.S_oeis_a223240 OMAA223240Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a223240.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega]
    exact a_rec k
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * ((1 + 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X)) =
        F' - PowerSeries.X ^ 1 * F' - PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 2 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (PowerSeries.X * (7 + 11 * PowerSeries.X) : PowerSeries ℚ) =
        PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (11 : ℚ) * PowerSeries.X ^ 2 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 2
    · interval_cases n <;> norm_num [a_one, a_two]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
      have h := a_rec j
      have q : ((a (j + 3) : ℕ) : ℚ) = ((a (j + 2) + 6 * a (j + 1) : ℕ) : ℚ) := by rw [h]
      push_cast at q
      simp
      linear_combination q
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    exact (closed k).1
