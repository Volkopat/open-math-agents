import OMAStatements.S_oeis_a209722
import Mathlib

-- Proof of the conjectures in OEIS A209722 (statement by @ivillar).
-- Idea: the subblock conditions involve only consecutive rows, so the count is a walk count on rows
-- (transfer matrix). Checking all 81 x 81 row pairs: 67 rows have no successor; 8 rows (list L1)
-- have exactly one successor, in L1; the rows (0,2,0,2), (2,0,2,0) (list L3) each have 2 successors,
-- in the list L2 of the 4 other alternating rows; each row of L2 has 1 successor, in L3. So for
-- n ≥ 1, N(n) = 8 + 2h(n) + 4k(n) with h' = 2k, k' = h, i.e. a(m+1) = 2 + k(m) + k(m+1) with
-- k(m+2) = 2k(m). This gives the recurrence, the g.f. and the parity closed forms.

namespace OMAA209722Helpers

open OMA.S_oeis_a209722

instance (u v : Fin 4 → Fin 3) : Decidable (BlockOK u v) := by
  unfold BlockOK CW; infer_instance

abbrev R := Fin 4 → Fin 3

/-- Rows are unconstrained. -/
abbrev ok (_r : R) : Prop := True

/-- Consecutive rows r, s: the subblock they form satisfies the stress condition. -/
abbrev compat (r s : R) : Prop := BlockOK r s

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

/-- The live rows: walk count 1 (L1), the alternating 0/2 rows (L3) and the other alternating rows (L2). -/
def L1 : List R := [![0, 1, 0, 2], ![0, 2, 0, 1], ![0, 2, 1, 2], ![1, 0, 2, 0], ![1, 2, 0, 2],
  ![2, 0, 1, 0], ![2, 0, 2, 1], ![2, 1, 2, 0]]
def L2 : List R := [![0, 1, 0, 1], ![1, 0, 1, 0], ![1, 2, 1, 2], ![2, 1, 2, 1]]
def L3 : List R := [![0, 2, 0, 2], ![2, 0, 2, 0]]

/-- Walk counts by row type: dead rows (f), L1 (g), L3 (h), L2 (k). -/
def f : ℕ → ℕ
  | 0 => 1
  | _ + 1 => 0
where
  g : ℕ → ℕ
  | 0 => 1
  | n + 1 => g n
  h : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * k n
  k : ℕ → ℕ
  | 0 => 1
  | n + 1 => h n

abbrev Z (t : R) : Prop := ¬ (t ∈ L1 ∨ t ∈ L2 ∨ t ∈ L3)
abbrev P2 (t : R) : Prop := t ∈ L1
abbrev P3 (t : R) : Prop := t ∈ L3

def V (n : ℕ) (s : R) : ℕ :=
  if Z s then f n else if P2 s then f.g n else if P3 s then f.h n else f.k n

theorem cZ : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ Z t)).card = 0 := by
  decide +kernel

theorem c2 : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ P2 t)).card =
    if Z s then 0 else if P2 s then 1 else 0 := by decide +kernel

theorem c3 : ∀ s : R,
    (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ ¬ P2 t ∧ P3 t)).card =
    if Z s then 0 else if P2 s then 0 else if P3 s then 0 else 1 := by decide +kernel

theorem c1 : ∀ s : R,
    (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ ¬ P2 t ∧ ¬ P3 t)).card =
    if Z s then 0 else if P2 s then 0 else if P3 s then 2 else 0 := by decide +kernel

theorem tZ : (Finset.univ.filter (fun t : R => True ∧ Z t)).card = 67 := by decide +kernel
theorem t2 : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t ∧ P2 t)).card = 8 := by decide +kernel
theorem t3 : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t ∧ ¬ P2 t ∧ P3 t)).card = 2 := by
  decide +kernel
theorem t1 : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t ∧ ¬ P2 t ∧ ¬ P3 t)).card = 4 := by
  decide +kernel

theorem split_V (n : ℕ) (P : Prop) [Decidable P] (t : R) :
    (if P then V n t else 0) = (((if P ∧ Z t then f n else 0) +
      (if P ∧ ¬ Z t ∧ P2 t then f.g n else 0)) + (if P ∧ ¬ Z t ∧ ¬ P2 t ∧ P3 t then f.h n else 0)) +
      (if P ∧ ¬ Z t ∧ ¬ P2 t ∧ ¬ P3 t then f.k n else 0) := by
  unfold V
  by_cases h1 : P
  · rw [if_pos h1]
    by_cases h2 : Z t
    · rw [if_pos h2, if_pos (show P ∧ Z t from ⟨h1, h2⟩),
        if_neg (show ¬(P ∧ ¬ Z t ∧ P2 t) from fun h => h.2.1 h2),
        if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ P2 t ∧ P3 t) from fun h => h.2.1 h2),
        if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ P2 t ∧ ¬ P3 t) from fun h => h.2.1 h2)]
      ring
    · rw [if_neg h2, if_neg (show ¬(P ∧ Z t) from fun h => h2 h.2)]
      by_cases h3 : P2 t
      · rw [if_pos h3, if_pos (show P ∧ ¬ Z t ∧ P2 t from ⟨h1, h2, h3⟩),
          if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ P2 t ∧ P3 t) from fun h => h.2.2.1 h3),
          if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ P2 t ∧ ¬ P3 t) from fun h => h.2.2.1 h3)]
        ring
      · rw [if_neg h3, if_neg (show ¬(P ∧ ¬ Z t ∧ P2 t) from fun h => h3 h.2.2)]
        by_cases h4 : P3 t
        · rw [if_pos h4, if_pos (show P ∧ ¬ Z t ∧ ¬ P2 t ∧ P3 t from ⟨h1, h2, h3, h4⟩),
            if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ P2 t ∧ ¬ P3 t) from fun h => h.2.2.2 h4)]
          ring
        · rw [if_neg h4, if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ P2 t ∧ P3 t) from fun h => h4 h.2.2.2),
            if_pos (show P ∧ ¬ Z t ∧ ¬ P2 t ∧ ¬ P3 t from ⟨h1, h2, h3, h4⟩)]
          ring
  · rw [if_neg h1, if_neg (show ¬(P ∧ Z t) from fun h => h1 h.1),
      if_neg (show ¬(P ∧ ¬ Z t ∧ P2 t) from fun h => h1 h.1),
      if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ P2 t ∧ P3 t) from fun h => h1 h.1),
      if_neg (show ¬(P ∧ ¬ Z t ∧ ¬ P2 t ∧ ¬ P3 t) from fun h => h1 h.1)]

theorem sum_V (n : ℕ) (P : R → Prop) [DecidablePred P] :
    (∑ t : R, if P t then V n t else 0) =
      (Finset.univ.filter (fun t => P t ∧ Z t)).card * f n +
      (Finset.univ.filter (fun t => P t ∧ ¬ Z t ∧ P2 t)).card * f.g n +
      (Finset.univ.filter (fun t => P t ∧ ¬ Z t ∧ ¬ P2 t ∧ P3 t)).card * f.h n +
      (Finset.univ.filter (fun t => P t ∧ ¬ Z t ∧ ¬ P2 t ∧ ¬ P3 t)).card * f.k n := by
  rw [Finset.sum_congr rfl (fun t _ => split_V n (P t) t), Finset.sum_add_distrib,
    Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_ite, Finset.sum_ite, Finset.sum_ite,
    Finset.sum_ite]
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
    rw [sum_V n (fun t => ok s ∧ compat s t), cZ s, c2 s, c3 s, c1 s]
    unfold V
    split_ifs <;> simp [f, f.g, f.h, f.k]

theorem N_eq (n : ℕ) : N n = 67 * f n + 8 * f.g n + 2 * f.h n + 4 * f.k n := by
  unfold N
  rw [Nat.card_congr (Equiv.subtypeEquivRight
      (p := fun x : Fin (n + 1) → R => ∀ i : Fin n, BlockOK (x i.castSucc) (x i.succ))
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
  rw [sum_V n (fun _ => True), tZ, t2, t3, t1]

theorem g_one (n : ℕ) : f.g n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [f.g, ih]

theorem a_eq (m : ℕ) : a (m + 1) = 2 + f.k m + f.k (m + 1) := by
  unfold a
  rw [N_eq, show f (m + 1) = 0 from rfl, g_one, show f.h (m + 1) = 2 * f.k m from rfl,
    show f.k (m + 1) = f.h m from rfl,
    show 67 * 0 + 8 * 1 + 2 * (2 * f.k m) + 4 * f.h m = 4 * (2 + f.k m + f.h m) by ring,
    Nat.mul_div_cancel_left _ (by norm_num)]

theorem k_rec (m : ℕ) : f.k (m + 2) = 2 * f.k m := rfl

theorem a_rec (m : ℕ) : a (m + 4) + 2 * a (m + 1) = a (m + 3) + 2 * a (m + 2) := by
  rw [a_eq, a_eq, a_eq, a_eq, show m + 3 + 1 = (m + 2) + 2 from rfl, k_rec (m + 2),
    show m + 2 + 1 = (m + 1) + 2 from rfl, k_rec (m + 1), show m + 1 + 1 = m + 2 from rfl, k_rec m]
  ring

theorem k_closed (j : ℕ) : f.k (2 * j) = 2 ^ j ∧ f.k (2 * j + 1) = 2 ^ j := by
  induction j with
  | zero => exact ⟨rfl, rfl⟩
  | succ j ih =>
    refine ⟨?_, ?_⟩
    · rw [show 2 * (j + 1) = 2 * j + 2 by ring, k_rec, ih.1]; ring
    · rw [show 2 * (j + 1) + 1 = (2 * j + 1) + 2 by ring, k_rec, ih.2]; ring

theorem a1 : a 1 = 4 := by rw [a_eq]; rfl
theorem a2 : a 2 = 5 := by rw [a_eq]; rfl
theorem a3 : a 3 = 6 := by rw [a_eq]; rfl

end OMAA209722Helpers

open OMA.S_oeis_a209722 OMAA209722Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a209722.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn he => ?_, fun n hn ho => ?_⟩
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega]
    have h : ((a (m + 4) : ℕ) : ℤ) + 2 * a (m + 1) = a (m + 3) + 2 * a (m + 2) := by
      exact_mod_cast a_rec m
    linarith
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * ((1 - PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2)) =
        F' - PowerSeries.X ^ 1 * F' - PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 2 * F') +
          PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 3 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (PowerSeries.X * (4 + PowerSeries.X - 7 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C (4 : ℚ) * PowerSeries.X ^ 1 + PowerSeries.X ^ 2 -
          PowerSeries.C (7 : ℚ) * PowerSeries.X ^ 3 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 3
    · interval_cases n <;> norm_num [a1, a2, a3]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
      have q : ((a (j + 4) : ℕ) : ℚ) + 2 * a (j + 1) = a (j + 3) + 2 * a (j + 2) := by
        exact_mod_cast a_rec j
      simp
      linear_combination q
  · obtain ⟨j, rfl⟩ := he
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [show i + 1 + (i + 1) = (2 * i + 1) + 1 by ring, a_eq, (k_closed i).2,
      show 2 * i + 1 + 1 = 2 * (i + 1) by ring, (k_closed (i + 1)).1,
      show 2 * (i + 1) / 2 - 1 = i by omega]
    ring
  · obtain ⟨j, rfl⟩ := ho
    rw [a_eq, (k_closed j).1, (k_closed j).2, show (2 * j + 1 + 1) / 2 = j + 1 by omega]
    ring
