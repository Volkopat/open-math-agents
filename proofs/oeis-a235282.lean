import OMAStatements.S_oeis_a235282
import Mathlib

-- Proof of the conjectures in OEIS A235282 (statement by @ivillar).
-- Idea: the subblock condition involves only consecutive rows, so the count is a walk count on rows
-- (transfer matrix). Checking the 16 x 16 row pairs:
-- * constant rows have no successor;
-- * rows with entries differing by 2 are followed by 2 such rows;
-- * rows differing by 1 are followed by 1 row differing by 3;
-- * rows differing by 3 are followed by 3 rows differing by 1.
-- Hence for n ≥ 1, a(n) = 4*2^n + 2h(n) + 6k(n) with h' = 3k and k' = h, so a(2j+1) = 2^(2j+3) + 12*3^j
-- and a(2j) = 2^(2j+2) + 8*3^j. This gives the recurrence (char. polynomial (t-2)(t^2-3)), the g.f. and
-- the closed form (the half-integer power of 3 for even n combines with sqrt(3)).

namespace OMAA235282Helpers

open OMA.S_oeis_a235282

instance (u v : Fin 2 → Fin 4) : Decidable (BlockOK u v) := by unfold BlockOK; infer_instance

abbrev R := Fin 2 → Fin 4

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

/-- Walk counts by row type: constant (f), entries differing by 2 (g), by 3 (h), by 1 (k). -/
def f : ℕ → ℕ
  | 0 => 1
  | _ + 1 => 0
where
  g : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * g n
  h : ℕ → ℕ
  | 0 => 1
  | n + 1 => 3 * k n
  k : ℕ → ℕ
  | 0 => 1
  | n + 1 => h n

abbrev Z (t : R) : Prop := t 0 = t 1
abbrev P2 (t : R) : Prop := (t 0 : ℕ) + 2 = t 1 ∨ (t 1 : ℕ) + 2 = t 0
abbrev P3 (t : R) : Prop := (t 0 : ℕ) + 3 = t 1 ∨ (t 1 : ℕ) + 3 = t 0

def V (n : ℕ) (s : R) : ℕ :=
  if Z s then f n else if P2 s then f.g n else if P3 s then f.h n else f.k n

theorem cZ : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ Z t)).card = 0 := by
  decide

theorem c2 : ∀ s : R, (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ P2 t)).card =
    if Z s then 0 else if P2 s then 2 else 0 := by decide

theorem c3 : ∀ s : R,
    (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ ¬ P2 t ∧ P3 t)).card =
    if Z s then 0 else if P2 s then 0 else if P3 s then 0 else 1 := by decide

theorem c1 : ∀ s : R,
    (Finset.univ.filter (fun t : R => (ok s ∧ compat s t) ∧ ¬ Z t ∧ ¬ P2 t ∧ ¬ P3 t)).card =
    if Z s then 0 else if P2 s then 0 else if P3 s then 3 else 0 := by decide

theorem tZ : (Finset.univ.filter (fun t : R => True ∧ Z t)).card = 4 := by decide
theorem t2 : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t ∧ P2 t)).card = 4 := by decide
theorem t3 : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t ∧ ¬ P2 t ∧ P3 t)).card = 2 := by decide
theorem t1 : (Finset.univ.filter (fun t : R => True ∧ ¬ Z t ∧ ¬ P2 t ∧ ¬ P3 t)).card = 6 := by decide

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

theorem a_eq (n : ℕ) : a n = 4 * f n + 4 * f.g n + 2 * f.h n + 6 * f.k n := by
  unfold a
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

theorem a_rec (n : ℕ) : a (n + 4) + 6 * a (n + 1) = 2 * a (n + 3) + 3 * a (n + 2) := by
  rw [a_eq, a_eq, a_eq, a_eq]
  simp only [f, f.g, f.h, f.k]
  ring

theorem a1 : a 1 = 20 := by rw [a_eq]; simp [f, f.g, f.h, f.k]
theorem a2 : a 2 = 40 := by rw [a_eq]; simp [f, f.g, f.h, f.k]
theorem a3 : a 3 = 68 := by rw [a_eq]; simp [f, f.g, f.h, f.k]

theorem g_pow (n : ℕ) : f.g n = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [f.g, ih]; ring

theorem hk_closed (j : ℕ) : f.h (2 * j) = 3 ^ j ∧ f.k (2 * j) = 3 ^ j ∧
    f.h (2 * j + 1) = 3 ^ (j + 1) ∧ f.k (2 * j + 1) = 3 ^ j := by
  induction j with
  | zero => simp [f.h, f.k]
  | succ j ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    have e1 : f.h (2 * (j + 1)) = 3 * f.k (2 * j + 1) := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]; simp only [f.h]
    have e2 : f.k (2 * (j + 1)) = f.h (2 * j + 1) := by
      rw [show 2 * (j + 1) = 2 * j + 1 + 1 by ring]; simp only [f.k]
    have e3 : f.h (2 * (j + 1) + 1) = 3 * f.k (2 * (j + 1)) := by simp only [f.h]
    have e4 : f.k (2 * (j + 1) + 1) = f.h (2 * (j + 1)) := by simp only [f.k]
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [e1, h4]; ring
    · rw [e2, h3]
    · rw [e3, e2, h3]; ring
    · rw [e4, e1, h4]; ring

theorem f_succ (n : ℕ) : f (n + 1) = 0 := rfl

end OMAA235282Helpers

open OMA.S_oeis_a235282 OMAA235282Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a235282.main := by
  refine ⟨fun n hn => ?_, ?_, fun n hn => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    rw [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
      show k + 4 - 3 = k + 1 by omega]
    have h := a_rec k
    have h' : ((a (k + 4) : ℕ) : ℤ) + 6 * a (k + 1) = 2 * a (k + 3) + 3 * a (k + 2) := by
      exact_mod_cast h
    linarith
  · rw [G, PowerSeries.eq_mul_inv_iff_mul_eq (by simp)]
    set F' := PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ))
    have e1 : F' * ((1 - 2 * PowerSeries.X) * (1 - 3 * PowerSeries.X ^ 2)) =
        F' - PowerSeries.C (2 : ℚ) * (PowerSeries.X ^ 1 * F') -
          PowerSeries.C (3 : ℚ) * (PowerSeries.X ^ 2 * F') +
          PowerSeries.C (6 : ℚ) * (PowerSeries.X ^ 3 * F') := by
      simp only [map_ofNat]
      ring
    have e2 : (4 * PowerSeries.X * (5 - 18 * PowerSeries.X ^ 2) : PowerSeries ℚ) =
        PowerSeries.C (20 : ℚ) * PowerSeries.X ^ 1 - PowerSeries.C (72 : ℚ) * PowerSeries.X ^ 3 := by
      simp only [map_ofNat]
      ring
    rw [e1, e2]
    ext n
    simp only [F', map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk,
      PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow]
    by_cases hn : n ≤ 3
    · interval_cases n <;> norm_num [a1, a2, a3]
    · obtain ⟨j, rfl⟩ : ∃ j, n = j + 4 := ⟨n - 4, by omega⟩
      have h := a_rec j
      have q : ((a (j + 4) : ℕ) : ℚ) + 6 * a (j + 1) = 2 * a (j + 3) + 3 * a (j + 2) := by
        exact_mod_cast h
      simp
      linear_combination q
  · have h3p : (0 : ℝ) < 3 := by norm_num
    have hs : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
    rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hn2 : n = 2 * (m + 1) := by omega
      subst hn2
      have hf : f (2 * (m + 1)) = 0 := rfl
      rw [a_eq, hf, (hk_closed (m + 1)).1, (hk_closed (m + 1)).2.1, g_pow]
      have er : (3 : ℝ) ^ (((-1 : ℝ) + ((2 * (m + 1) : ℕ) : ℝ)) / 2) = 3 ^ m * Real.sqrt 3 := by
        rw [show ((-1 : ℝ) + ((2 * (m + 1) : ℕ) : ℝ)) / 2 = (m : ℝ) + 1 / 2 by push_cast; ring,
          Real.rpow_add h3p, Real.rpow_natCast, Real.sqrt_eq_rpow]
      rw [er, show ((-1 : ℝ)) ^ (2 * (m + 1)) = 1 by rw [pow_mul]; norm_num]
      push_cast
      rw [show (2 : ℝ) ^ (2 + 2 * (m + 1)) = 4 * 2 ^ (2 * (m + 1)) by rw [pow_add]; norm_num]
      linear_combination (-8 * (3 : ℝ) ^ m) * hs
    · subst hk
      have hf : f (2 * k + 1) = 0 := rfl
      rw [a_eq, hf, (hk_closed k).2.2.1, (hk_closed k).2.2.2, g_pow]
      have er : (3 : ℝ) ^ (((-1 : ℝ) + ((2 * k + 1 : ℕ) : ℝ)) / 2) = 3 ^ k := by
        rw [show ((-1 : ℝ) + ((2 * k + 1 : ℕ) : ℝ)) / 2 = (k : ℝ) by push_cast; ring, Real.rpow_natCast]
      rw [er, show ((-1 : ℝ)) ^ (2 * k + 1) = -1 by rw [pow_succ, pow_mul]; norm_num]
      push_cast
      rw [show (2 : ℝ) ^ (2 + (2 * k + 1)) = 4 * 2 ^ (2 * k + 1) by rw [pow_add]; norm_num]
      ring
