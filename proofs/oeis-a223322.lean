import OMAStatements.S_oeis_a223322
import Mathlib

-- Proof of the conjectures in OEIS A223322 (statement by @ivillar).
-- Idea: read the array column by column. The constraints link consecutive columns (top-top,
-- bottom-bottom and bottom-to-next-top), so the count is a walk count on columns (transfer matrix).
-- Walk counts depend only on whether a column has equal entries (f), antipodal entries (h; no successor),
-- or other entries (g): f' = 5f + 20g, g' = 2f + 8g, and a(n+1) = f + 10g + h. After the first step
-- 5g = 2f, so a(n+1) = 5f(n) and f(n+1) = 13f(n); this gives the recurrence, the g.f. and
-- a(n) = 125*13^(n-2).

namespace OMAAA223322Helpers

open OMA.S_oeis_a223322

instance (u v : Fin 12) : Decidable (edge u v) := by unfold edge; infer_instance

theorem adjFace_symm : ∀ u v : Fin 12, edge u v → edge v u := by decide +kernel

/-- The antipodal vertex. -/
def anti : Fin 12 → Fin 12 := ![9, 10, 11, 6, 7, 8, 3, 4, 5, 0, 1, 2]

abbrev R := Fin 2 → Fin 12

/-- Columns are unconstrained (vertical neighbours are not adjacent). -/
abbrev ok (_r : R) : Prop := True

/-- Two consecutive columns: no complementary pair between them (all such cells are adjacent). -/
abbrev compat (r s : R) : Prop := edge (r 0) (s 0) ∧ edge (r 1) (s 1) ∧ edge (r 1) (s 0)

/-- The array conditions, row by row. -/
abbrev Walk {n : ℕ} (x : Fin (n + 1) → R) : Prop :=
  (∀ i, ok (x i)) ∧ ∀ i : Fin n, compat (x i.castSucc) (x i.succ)

theorem good_iff (n : ℕ) (x : Fin 2 → Fin (n + 1) → Fin 12) :
    Good x ↔ Walk (fun j i => x i j : Fin (n + 1) → R) ∧ x 0 0 = 0 := by
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨⟨fun i => trivial, fun i => ⟨?_, ?_, ?_⟩⟩, ?_⟩
    · exact h1 (0, i.castSucc) (0, i.succ)
        (Or.inl ⟨rfl, Or.inr (by simp only [Fin.val_castSucc, Fin.val_succ])⟩)
    · exact h1 (1, i.castSucc) (1, i.succ)
        (Or.inl ⟨rfl, Or.inr (by simp only [Fin.val_castSucc, Fin.val_succ])⟩)
    · exact h1 (1, i.castSucc) (0, i.succ)
        (Or.inr ⟨by simp only [Fin.val_castSucc, Fin.val_succ, Fin.val_zero, Fin.val_one]; omega,
          Or.inl (by simp)⟩)
    · exact h2 (Nat.succ_pos n)
  · rintro ⟨⟨-, hc⟩, h0⟩
    refine ⟨fun p q hpq => ?_, fun h => ?_⟩
    · obtain ⟨⟨pi, pj⟩, ⟨qi, qj⟩⟩ := (⟨p, q⟩ : (Fin 2 × Fin (n + 1)) × (Fin 2 × Fin (n + 1)))
      have hpi := p.1.isLt
      have hqi := q.1.isLt
      rcases hpq with ⟨hr, hl | hl⟩ | ⟨hs, hl | hl⟩
      · -- horizontal, p to the right of q
        have hlt : (q.2 : ℕ) < n := by have := p.2.isLt; omega
        have e1 : (⟨q.2, hlt⟩ : Fin n).castSucc = q.2 := Fin.ext rfl
        have e2 : (⟨q.2, hlt⟩ : Fin n).succ = p.2 := Fin.ext (by simp; omega)
        have := hc ⟨q.2, hlt⟩
        simp only [e1, e2] at this
        rcases (show (p.1 : ℕ) = 0 ∨ (p.1 : ℕ) = 1 by omega) with h | h
        · have ep : p.1 = 0 := Fin.ext h
          rw [ep, ← hr, ep]; exact adjFace_symm _ _ this.1
        · have ep : p.1 = 1 := Fin.ext h
          rw [ep, ← hr, ep]; exact adjFace_symm _ _ this.2.1
      · -- horizontal, q to the right of p
        have hlt : (p.2 : ℕ) < n := by have := q.2.isLt; omega
        have e1 : (⟨p.2, hlt⟩ : Fin n).castSucc = p.2 := Fin.ext rfl
        have e2 : (⟨p.2, hlt⟩ : Fin n).succ = q.2 := Fin.ext (by simp; omega)
        have := hc ⟨p.2, hlt⟩
        simp only [e1, e2] at this
        rcases (show (p.1 : ℕ) = 0 ∨ (p.1 : ℕ) = 1 by omega) with h | h
        · have ep : p.1 = 0 := Fin.ext h
          rw [← hr, ep]; exact this.1
        · have ep : p.1 = 1 := Fin.ext h
          rw [← hr, ep]; exact this.2.1
      · -- antidiagonal, p in the lower row: p = (1, j), q = (0, j + 1)
        have ep : p.1 = 1 := Fin.ext (by omega)
        have eq : q.1 = 0 := Fin.ext (by omega)
        have hlt : (p.2 : ℕ) < n := by have := q.2.isLt; rw [ep, eq] at hs; simp at hs; omega
        have e1 : (⟨p.2, hlt⟩ : Fin n).castSucc = p.2 := Fin.ext rfl
        have e2 : (⟨p.2, hlt⟩ : Fin n).succ = q.2 := Fin.ext (by
          rw [ep, eq] at hs; simp at hs; simp; omega)
        have := hc ⟨p.2, hlt⟩
        simp only [e1, e2] at this
        rw [ep, eq]; exact this.2.2
      · -- antidiagonal, q in the lower row: q = (1, j), p = (0, j + 1)
        have eq : q.1 = 1 := Fin.ext (by omega)
        have ep : p.1 = 0 := Fin.ext (by omega)
        have hlt : (q.2 : ℕ) < n := by have := p.2.isLt; rw [ep, eq] at hs; simp at hs; omega
        have e1 : (⟨q.2, hlt⟩ : Fin n).castSucc = q.2 := Fin.ext rfl
        have e2 : (⟨q.2, hlt⟩ : Fin n).succ = p.2 := Fin.ext (by
          rw [ep, eq] at hs; simp at hs; simp; omega)
        have := hc ⟨q.2, hlt⟩
        simp only [e1, e2] at this
        rw [ep, eq]; exact adjFace_symm _ _ this.2.2
    · have e : (⟨0, h⟩ : Fin (n + 1)) = 0 := Fin.ext rfl
      rw [e]
      exact h0

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

/-- F(n, s): the number of row sequences of length n+1 satisfying the conditions, starting at s. -/
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
      · subst hr; simp
      · simp [hr]
    rw [Finset.sum_congr rfl (fun r _ => h r), Finset.sum_ite_eq']
    simp
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
  rw [Finset.sum_ite_eq]
  simp

/-- Walk counts by column type: equal entries (f), other (g), antipodal (h). -/
def f : ℕ → ℕ
  | 0 => 1
  | n + 1 => 5 * f n + 20 * g n
where
  g : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * f n + 8 * g n
  h : ℕ → ℕ
  | 0 => 1
  | _ + 1 => 0

abbrev Z (t : R) : Prop := t 0 = t 1
abbrev O (t : R) : Prop := t 1 ≠ anti (t 0)

def V (n : ℕ) (s : R) : ℕ := if Z s then f n else if O s then f.g n else f.h n

theorem cZ : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ Z t)).card =
    if Z s then 5 else if O s then 2 else 0 := by decide +kernel

theorem cO : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ O t)).card =
    if Z s then 20 else if O s then 8 else 0 := by decide +kernel

theorem cN : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ ¬ O t)).card =
    0 := by decide +kernel

theorem tZ : (Finset.univ.filter (fun t : R => t 0 = 0 ∧ Z t)).card = 1 := by decide +kernel
theorem tO : (Finset.univ.filter (fun t : R => t 0 = 0 ∧ ¬ Z t ∧ O t)).card = 10 := by decide +kernel
theorem tN : (Finset.univ.filter (fun t : R => t 0 = 0 ∧ ¬ Z t ∧ ¬ O t)).card = 1 := by decide +kernel

theorem split_V (n : ℕ) (P : Prop) [Decidable P] (t : R) :
    (if P then V n t else 0) = ((if P ∧ Z t then f n else 0) +
      (if P ∧ ¬ Z t ∧ O t then f.g n else 0)) + (if P ∧ ¬ Z t ∧ ¬ O t then f.h n else 0) := by
  unfold V
  by_cases h1 : P
  · rw [if_pos h1]
    by_cases h2 : Z t
    · rw [if_pos h2, if_pos (show P ∧ Z t from ⟨h1, h2⟩),
        if_neg (show ¬(P ∧ ¬ Z t ∧ O t) from fun h => h.2.1 h2),
        if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ O t) from fun h => h.2.1 h2)]
      ring
    · rw [if_neg h2, if_neg (show ¬(P ∧ Z t) from fun h => h2 h.2)]
      by_cases h3 : O t
      · rw [if_pos h3, if_pos (show P ∧ ¬ Z t ∧ O t from ⟨h1, h2, h3⟩),
          if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ O t) from fun h => h.2.2 h3)]
        ring
      · rw [if_neg h3, if_neg (show ¬(P ∧ ¬ Z t ∧ O t) from fun h => h3 h.2.2),
          if_pos (show P ∧ ¬ Z t ∧ ¬ O t from ⟨h1, h2, h3⟩)]
        ring
  · rw [if_neg h1, if_neg (show ¬(P ∧ Z t) from fun h => h1 h.1),
      if_neg (show ¬(P ∧ ¬ Z t ∧ O t) from fun h => h1 h.1),
      if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ O t) from fun h => h1 h.1)]

theorem sum_V (n : ℕ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then V n t else 0) =
      (Finset.univ.filter (fun t => P t ∧ Z t)).card * f n +
      (Finset.univ.filter (fun t => P t ∧ ¬ Z t ∧ O t)).card * f.g n +
      (Finset.univ.filter (fun t => P t ∧ ¬ Z t ∧ ¬ O t)).card * f.h n := by
  rw [Finset.sum_congr rfl (fun t _ => split_V n (P t) t), Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_ite]
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
    rw [sum_V n (fun t => ok s ∧ compat s t), cZ s, cO s, cN s]
    unfold V
    split_ifs <;> simp [f, f.g, f.h] <;> ring

theorem a_succ (n : ℕ) : a (n + 1) = f n + 10 * f.g n + f.h n := by
  unfold a
  rw [Nat.card_congr ((Equiv.piComm (fun (_ : Fin 2) (_ : Fin (n + 1)) => Fin 12)).subtypeEquiv
      (p := Good) (q := fun y : Fin (n + 1) → R => Walk y ∧ y 0 0 = 0)
      (fun x => good_iff n x)), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter]
  have h1 : (∑ x : Fin (n + 1) → R, if Walk x ∧ x 0 0 = 0 then 1 else 0) =
      ∑ s : R, if s 0 = 0 then F n s else 0 := by
    unfold F
    have h2 : ∀ s : R, (if s 0 = 0 then ∑ y : Fin (n + 1) → R, (if Walk y ∧ y 0 = s then 1 else 0)
        else 0) = ∑ y : Fin (n + 1) → R, if y 0 = s then (if Walk y ∧ y 0 0 = 0 then 1 else 0)
          else 0 := by
      intro s
      split_ifs with hs
      · apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y 0 = s
        · subst hy; simp [hs]
        · simp [hy]
      · symm
        apply Finset.sum_eq_zero
        intro y _
        by_cases hy : y 0 = s
        · subst hy; rw [if_pos rfl, if_neg (fun h => hs h.2)]
        · rw [if_neg hy]
    rw [Finset.sum_congr rfl (fun s _ => h2 s), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    rw [Finset.sum_ite_eq]
    simp
  rw [h1]
  simp only [F_eq]
  rw [sum_V n (fun t => t 0 = 0), tZ, tO, tN]
  ring

theorem a_rec (n : ℕ) : a (n + 3) = 13 * a (n + 2) := by
  rw [a_succ, a_succ]
  simp only [f, f.g, f.h]
  ring

theorem a_two : a 2 = 125 := by rw [a_succ]; simp [f, f.g, f.h]
theorem a_one : a 1 = 12 := by rw [a_succ]; simp [f, f.g, f.h]

theorem closed (k : ℕ) : a (k + 2) = 125 * 13 ^ k := by
  induction k with
  | zero => rw [a_two]; rfl
  | succ k ih => rw [show k + 1 + 2 = k + 3 from rfl, a_rec, ih]; ring

end OMAAA223322Helpers

open OMA.S_oeis_a223322 OMAAA223322Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a223322.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
    rw [show k + 3 - 1 = k + 2 by omega]
    exact a_rec k
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * (1 - 13 * PowerSeries.X) =
        F' - PowerSeries.C (13 : ℚ) * (PowerSeries.X ^ 1 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (PowerSeries.X * (12 - 31 * PowerSeries.X) : PowerSeries ℚ) =
        PowerSeries.C (12 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (31 : ℚ) * PowerSeries.X ^ 2 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 2
    · interval_cases n <;> norm_num [a_one, a_two]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 3 := ⟨n - 3, by omega⟩
      have h := a_rec j
      have q : ((a (j + 3) : ℕ) : ℚ) = ((13 * a (j + 2) : ℕ) : ℚ) := by rw [h]
      push_cast at q
      simp
      linear_combination q
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
    rw [show k + 2 - 2 = k by omega]
    exact closed k
