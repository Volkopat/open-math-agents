import OMAStatements.S_oeis_a204708
import Mathlib

-- Proof of the conjectures in OEIS A204708 (statement by @ivillar).
-- Idea: for n ≥ 1 the common permanent k is 1 or 2 (binary entries), so the count splits as the
-- arrays with all subblock permanents 1 plus those with all permanents 2. Each part is a walk count on
-- rows (transfer matrix). Permanent 2 forces the all-ones array, so that part counts 1. For
-- permanent 1, 8 rows have no successor and the other rows split into two lists LA, LB with g' = 2g + 2h
-- and h' = 2g (checked by decide). So a(n+1) = 4g(n+1) + 4h(n+1) + 1, and a - 1 satisfies
-- b(n+2) = 2b(n+1) + 4b(n) (roots 1 ± sqrt 5); this gives the recurrence, the g.f. and the closed form.

namespace OMAA204708Helpers

open OMA.S_oeis_a204708

instance (k : ℕ) (u v : Fin 4 → Fin 2) : Decidable (BlockP k u v) := by unfold BlockP perm; infer_instance

namespace P1

abbrev R := Fin 4 → Fin 2

/-- Rows are unconstrained. -/
abbrev ok (_r : R) : Prop := True

/-- Consecutive rows r, s: the subblock they form satisfies the condition. -/
abbrev compat (r s : R) : Prop := BlockP 1 r s

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

/-- Walk counts by row type: zero row (f, no successor), a zero entry or constant (g), distinct
nonzero entries (h). -/
def LA : List R := [![0, 1, 0, 1], ![1, 0, 1, 0], ![1, 0, 1, 1], ![1, 1, 0, 1]]
def LB : List R := [![0, 1, 1, 0], ![0, 1, 1, 1], ![1, 1, 1, 0], ![1, 1, 1, 1]]

def f : ℕ → ℕ
  | 0 => 1
  | _ + 1 => 0
where
  g : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * g n + 2 * h n
  h : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * g n + 0 * h n

abbrev Z (t : R) : Prop := ¬ (t ∈ LA ∨ t ∈ LB)
abbrev O (t : R) : Prop := t ∈ LA

def V (n : ℕ) (s : R) : ℕ := if Z s then f n else if O s then f.g n else f.h n

theorem cZ : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ Z t)).card = 0 := by
  decide +kernel

theorem cO : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ O t)).card =
    if Z s then 0 else if O s then 2 else 2 := by decide +kernel

theorem cN : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ ¬ O t)).card =
    if Z s then 0 else if O s then 2 else 0 := by decide +kernel

theorem tZ : (Finset.univ.filter (fun t : R => True ∧ Z t)).card = 8 := by decide +kernel
theorem tO : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t ∧ O t)).card = 4 := by decide +kernel
theorem tN : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t ∧ ¬ O t)).card = 4 := by decide +kernel

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

theorem C_eq (n : ℕ) : Nat.card {x : Fin (n + 1) → R // ∀ i : Fin n, BlockP 1 (x i.castSucc) (x i.succ)} =
    8 * f n + 4 * f.g n + 4 * f.h n := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
      (p := fun x : Fin (n + 1) → R => ∀ i : Fin n, BlockP 1 (x i.castSucc) (x i.succ))
      (q := fun y : Fin (n + 1) → R => Walk y)
      (fun x => ⟨fun h => ⟨fun _ => trivial, h⟩, fun h => h.2⟩)), Nat.card_eq_fintype_card,
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
  rw [sum_V n (fun _ => True), tZ, tO, tN]

end P1

namespace P2

abbrev R := Fin 4 → Fin 2

/-- Rows are unconstrained. -/
abbrev ok (_r : R) : Prop := True

/-- Consecutive rows r, s: the subblock they form satisfies the condition. -/
abbrev compat (r s : R) : Prop := BlockP 2 r s

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

/-- Walk counts by row type: zero row (f, no successor), a zero entry or constant (g), distinct
nonzero entries (h). -/
def f : ℕ → ℕ
  | 0 => 1
  | _ + 1 => 0
where
  g : ℕ → ℕ
  | 0 => 1
  | n + 1 => g n + 0 * h n
  h : ℕ → ℕ
  | 0 => 1
  | n + 1 => 0 * g n + 0 * h n

abbrev Z (t : R) : Prop := ¬ (t 0 = 1 ∧ t 1 = 1 ∧ t 2 = 1 ∧ t 3 = 1)
abbrev O (t : R) : Prop := True

def V (n : ℕ) (s : R) : ℕ := if Z s then f n else if O s then f.g n else f.h n

theorem cZ : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ Z t)).card = 0 := by
  decide +kernel

theorem cO : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ O t)).card =
    if Z s then 0 else if O s then 1 else 0 := by decide +kernel

theorem cN : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ ¬ O t)).card =
    if Z s then 0 else if O s then 0 else 0 := by decide +kernel

theorem tZ : (Finset.univ.filter (fun t : R => True ∧ Z t)).card = 15 := by decide +kernel
theorem tO : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t ∧ O t)).card = 1 := by decide +kernel
theorem tN : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t ∧ ¬ O t)).card = 0 := by decide +kernel

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

theorem C_eq (n : ℕ) : Nat.card {x : Fin (n + 1) → R // ∀ i : Fin n, BlockP 2 (x i.castSucc) (x i.succ)} =
    15 * f n + 1 * f.g n + 0 * f.h n := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight
      (p := fun x : Fin (n + 1) → R => ∀ i : Fin n, BlockP 2 (x i.castSucc) (x i.succ))
      (q := fun y : Fin (n + 1) → R => Walk y)
      (fun x => ⟨fun h => ⟨fun _ => trivial, h⟩, fun h => h.2⟩)), Nat.card_eq_fintype_card,
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
  rw [sum_V n (fun _ => True), tZ, tO, tN]

end P2

theorem perm_le : ∀ p q r s : Fin 2, perm p q r s ≤ 2 := by decide

theorem good_iff (m : ℕ) (x : Fin (m + 2) → Fin 4 → Fin 2) :
    Good x ↔ (∀ i : Fin (m + 1), BlockP 1 (x i.castSucc) (x i.succ)) ∨
      (∀ i : Fin (m + 1), BlockP 2 (x i.castSucc) (x i.succ)) := by
  constructor
  · rintro ⟨k, hk, h⟩
    have h0 := h 0 0
    have hle := perm_le (x (0 : Fin (m + 1)).castSucc (0 : Fin 3).castSucc)
      (x (0 : Fin (m + 1)).castSucc (0 : Fin 3).succ) (x (0 : Fin (m + 1)).succ (0 : Fin 3).castSucc)
      (x (0 : Fin (m + 1)).succ (0 : Fin 3).succ)
    rw [h0] at hle
    rcases (show k = 1 ∨ k = 2 by omega) with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact ⟨1, one_ne_zero, h⟩
    · exact ⟨2, two_ne_zero, h⟩

theorem a_eq (m : ℕ) : a (m + 1) = (8 * P1.f (m + 1) + 4 * P1.f.g (m + 1) + 4 * P1.f.h (m + 1)) +
    (15 * P2.f (m + 1) + 1 * P2.f.g (m + 1) + 0 * P2.f.h (m + 1)) := by
  classical
  unfold a
  rw [Nat.card_congr (Equiv.subtypeEquivRight (good_iff m)), Nat.card_eq_fintype_card,
    Fintype.card_subtype_or_disjoint]
  · rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, P1.C_eq, P2.C_eq]
  · rw [Pi.disjoint_iff]
    intro x
    simp only [Prop.disjoint_iff]
    rintro ⟨h1, h2⟩
    have := (h1 0 0).symm.trans (h2 0 0)
    omega

theorem a_succ (m : ℕ) : a (m + 1) = 4 * P1.f.g (m + 1) + 4 * P1.f.h (m + 1) + 1 := by
  rw [a_eq, show P1.f (m + 1) = 0 from rfl, show P2.f (m + 1) = 0 from rfl,
    show P2.f.h (m + 1) = 0 by simp [P2.f.h]]
  have hg : ∀ n, P2.f.g n = 1 := fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp only [P2.f.g, ih, P2.f.h]; ring
  rw [hg]
  ring

theorem a_rec2 (m : ℕ) : a (m + 3) + 5 = 2 * a (m + 2) + 4 * a (m + 1) := by
  rw [a_succ, a_succ, a_succ]
  simp only [P1.f.g, P1.f.h]
  ring

theorem a_rec (m : ℕ) : a (m + 4) + 4 * a (m + 1) = 3 * a (m + 3) + 2 * a (m + 2) := by
  have h1 : a (m + 3) + 5 = 2 * a (m + 2) + 4 * a (m + 1) := a_rec2 m
  have h2 : a (m + 4) + 5 = 2 * a (m + 3) + 4 * a (m + 2) := a_rec2 (m + 1)
  omega

theorem a1 : a 1 = 25 := by rw [a_succ]; simp [P1.f.g, P1.f.h]
theorem a2 : a 2 = 81 := by rw [a_succ]; simp [P1.f.g, P1.f.h]
theorem a3 : a 3 = 257 := by rw [a_succ]; simp [P1.f.g, P1.f.h]

theorem closedT (k : ℕ) :
    5 * ((a (k + 1) : ℝ) - 1) = (20 - 8 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ (k + 1) +
      4 * (1 + Real.sqrt 5) ^ (k + 1) * (5 + 2 * Real.sqrt 5) ∧
    5 * ((a (k + 2) : ℝ) - 1) = (20 - 8 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ (k + 2) +
      4 * (1 + Real.sqrt 5) ^ (k + 2) * (5 + 2 * Real.sqrt 5) := by
  have hs : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have r1 : (1 + Real.sqrt 5) ^ 2 = 2 * (1 + Real.sqrt 5) + 4 := by linear_combination hs
  have r2 : (1 - Real.sqrt 5) ^ 2 = 2 * (1 - Real.sqrt 5) + 4 := by linear_combination hs
  induction k with
  | zero =>
    refine ⟨?_, ?_⟩
    · rw [a1]; push_cast; linear_combination (-16 : ℝ) * hs
    · rw [a2]; push_cast; linear_combination (-72 : ℝ) * hs
  | succ k ih =>
    refine ⟨ih.2, ?_⟩
    have h : ((a (k + 3) : ℕ) : ℝ) + 5 = 2 * a (k + 2) + 4 * a (k + 1) := by exact_mod_cast a_rec2 k
    have e : (a (k + 1 + 2) : ℝ) = 2 * a (k + 2) + 4 * a (k + 1) - 5 := by
      show (a (k + 3) : ℝ) = _
      linarith
    rw [e]
    obtain ⟨h1, h2⟩ := ih
    linear_combination (2 : ℝ) * h2 + (4 : ℝ) * h1 -
      (20 - 8 * Real.sqrt 5) * (1 - Real.sqrt 5) ^ (k + 1) * r2 -
      4 * (1 + Real.sqrt 5) ^ (k + 1) * (5 + 2 * Real.sqrt 5) * r1

end OMAA204708Helpers

open OMA.S_oeis_a204708 OMAA204708Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a204708.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega]
    have h : ((a (m + 4) : ℕ) : ℤ) + 4 * a (m + 1) = 3 * a (m + 3) + 2 * a (m + 2) := by
      exact_mod_cast a_rec m
    linarith
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X - 4 * PowerSeries.X ^ 2)) =
        F' - PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 1 * F') -
          PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 2 * F') +
          PowerSeries.C (4 : ℚ) * (PowerSeries.X ^ 3 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (PowerSeries.X * (25 + 6 * PowerSeries.X - 36 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C (25 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.C (6 : ℚ) * PowerSeries.X ^ 2 -
          PowerSeries.C (36 : ℚ) * PowerSeries.X ^ 3 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 3
    · interval_cases n <;> norm_num [a1, a2, a3]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
      have q : ((a (j + 4) : ℕ) : ℚ) + 4 * a (j + 1) = 3 * a (j + 3) + 2 * a (j + 2) := by
        exact_mod_cast a_rec j
      simp
      linear_combination q
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have h := (closedT k).1
    linear_combination (1 / 5 : ℝ) * h
