import OMAStatements.S_oeis_a235510
import Mathlib.Tactic

namespace OMA.P_oeis_a235510

open OMA.S_oeis_a235510

private def mmCode (r1 r2 : Bool × Bool) : Fin 3 :=
  match blockMaxMin r1.1 r1.2 r2.1 r2.2 with
  | 0 => 0
  | 1 => 1
  | _ => 2

private lemma mmCode_val (r1 r2 : Bool × Bool) :
    (mmCode r1 r2).1 = blockMaxMin r1.1 r1.2 r2.1 r2.2 := by
  rcases r1 with ⟨a, b⟩; rcases r2 with ⟨c, d⟩
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

private lemma mmCode_le_iff (r1 r2 r3 : Bool × Bool) :
    mmCode r1 r2 ≤ mmCode r2 r3 ↔
      blockMaxMin r1.1 r1.2 r2.1 r2.2 ≤ blockMaxMin r2.1 r2.2 r3.1 r3.2 := by
  rw [Fin.le_iff_val_le_val, mmCode_val, mmCode_val]

private def stepVec (v : (Bool × Bool) × Fin 3 → ℤ) (s : (Bool × Bool) × Fin 3) : ℤ :=
  ∑ r1 : Bool × Bool, ∑ d1 : Fin 3,
    if mmCode r1 s.1 = s.2 ∧ d1 ≤ s.2 then v (r1, d1) else 0

private lemma stepVec_add (u v : (Bool × Bool) × Fin 3 → ℤ) (s : (Bool × Bool) × Fin 3) :
    stepVec (fun x => u x + v x) s = stepVec u s + stepVec v s := by
  unfold stepVec
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun d1 _ => ?_
  split_ifs <;> ring

private lemma stepVec_sub (u v : (Bool × Bool) × Fin 3 → ℤ) (s : (Bool × Bool) × Fin 3) :
    stepVec (fun x => u x - v x) s = stepVec u s - stepVec v s := by
  unfold stepVec
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun d1 _ => ?_
  split_ifs <;> ring

private lemma stepVec_smul (c : ℤ) (v : (Bool × Bool) × Fin 3 → ℤ) (s : (Bool × Bool) × Fin 3) :
    stepVec (fun x => c * v x) s = c * stepVec v s := by
  unfold stepVec
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun d1 _ => ?_
  split_ifs <;> ring

private def isValidArr (k : ℕ) (A : Fin (k + 2) × Fin 2 → Bool) : Prop :=
  ∀ i : Fin k,
    blockMaxMin (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
      (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)) ≤
    blockMaxMin (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1))
      (A (⟨i.1 + 2, by omega⟩, 0)) (A (⟨i.1 + 2, by omega⟩, 1))

private instance (k : ℕ) (A : Fin (k + 2) × Fin 2 → Bool) : Decidable (isValidArr k A) := by
  unfold isValidArr; infer_instance

private def lastState (k : ℕ) (A : Fin (k + 2) × Fin 2 → Bool) : (Bool × Bool) × Fin 3 :=
  ((A (⟨k + 1, by omega⟩, 0), A (⟨k + 1, by omega⟩, 1)),
   mmCode (A (⟨k, by omega⟩, 0), A (⟨k, by omega⟩, 1))
          (A (⟨k + 1, by omega⟩, 0), A (⟨k + 1, by omega⟩, 1)))

private def stateCount (k : ℕ) (s : (Bool × Bool) × Fin 3) : ℤ :=
  ∑ A : Fin (k + 2) × Fin 2 → Bool,
    if isValidArr k A ∧ lastState k A = s then 1 else 0

private lemma A235510_eq_sum_stateCount (k : ℕ) :
    (A235510 (k + 1) : ℤ) = ∑ s : (Bool × Bool) × Fin 3, stateCount k s := by
  unfold A235510 stateCount
  rw [Finset.sum_comm]
  have hcard : ∀ S : Finset (Fin (k + 1 + 1) × Fin 2 → Bool),
      (S.card : ℤ) = ∑ A : Fin (k + 1 + 1) × Fin 2 → Bool, if A ∈ S then (1 : ℤ) else 0 := by
    intro S; simp
  rw [hcard]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hiff_k :
      (∀ i : Fin (k + 1 - 1),
        blockMaxMin (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
          (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)) ≤
        blockMaxMin (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1))
          (A (⟨i.1 + 2, by omega⟩, 0)) (A (⟨i.1 + 2, by omega⟩, 1))) ↔ isValidArr k A :=
    ⟨fun h i => h ⟨i.1, by omega⟩, fun h i => h ⟨i.1, by omega⟩⟩
  by_cases hA : isValidArr k A
  · rw [if_pos (hiff_k.mpr hA)]
    rw [Finset.sum_eq_single (lastState k A)]
    · simp [hA]
    · intro s _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  · rw [if_neg (fun h => hA (hiff_k.mp h))]
    refine (Finset.sum_eq_zero fun s _ => ?_).symm
    simp [hA]

private def initVec (s : (Bool × Bool) × Fin 3) : ℤ :=
  ∑ r1 : Bool × Bool, if mmCode r1 s.1 = s.2 then 1 else 0

private lemma stateCount_zero (s : (Bool × Bool) × Fin 3) :
    stateCount 0 s = initVec s := by
  let e : (Fin 2 × Fin 2 → Bool) ≃ ((Bool × Bool) × (Bool × Bool)) :=
    { toFun := fun A => ((A (0, 0), A (0, 1)), (A (1, 0), A (1, 1)))
      invFun := fun ⟨r0, r1⟩ p =>
        if p.1 = 0 then (if p.2 = 0 then r0.1 else r0.2)
        else (if p.2 = 0 then r1.1 else r1.2)
      left_inv := fun A => by funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> rfl
      right_inv := fun ⟨⟨a, b⟩, ⟨c, d⟩⟩ => rfl }
  unfold stateCount initVec
  rw [Fintype.sum_equiv e _ (fun p => if (p.2, mmCode p.1 p.2) = s then (1 : ℤ) else 0)
      (fun A => by
        have hv : isValidArr 0 A := fun i => Fin.elim0 i
        simp [e, hv, lastState])]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  rw [Finset.sum_eq_single s.1]
  · simp [Prod.ext_iff]
  · intro r2 _ hne; simp [Prod.ext_iff, hne]
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private lemma stateCount_succ (k : ℕ) (s : (Bool × Bool) × Fin 3) :
    stateCount (k + 1) s = stepVec (stateCount k) s := by
  let e : (Fin (k + 3) × Fin 2 → Bool) ≃ ((Fin (k + 2) × Fin 2 → Bool) × (Bool × Bool)) :=
    { toFun := fun A =>
        (fun p => A (⟨p.1.1, by omega⟩, p.2),
         (A (⟨k + 2, Nat.lt_succ_self _⟩, 0), A (⟨k + 2, Nat.lt_succ_self _⟩, 1)))
      invFun := fun ⟨A', r'⟩ p =>
        if h : p.1.1 < k + 2 then A' (⟨p.1.1, h⟩, p.2)
        else if p.2 = 0 then r'.1 else r'.2
      left_inv := fun A => by
        funext ⟨i, j⟩
        by_cases h : i.1 < k + 2
        · simp [h]
        · have hi : i = ⟨k + 2, Nat.lt_succ_self _⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
          subst hi; fin_cases j <;> simp
      right_inv := fun ⟨A', r'⟩ => by
        apply Prod.ext
        · funext ⟨i, j⟩; simp [i.isLt]
        · simp }
  have hiff : ∀ A : Fin (k + 3) × Fin 2 → Bool,
      (isValidArr (k + 1) A ∧ lastState (k + 1) A = s) ↔
      (isValidArr k (e A).1 ∧
       mmCode (lastState k (e A).1).1 (e A).2 = s.2 ∧
       (lastState k (e A).1).2 ≤ s.2 ∧
       (e A).2 = s.1) := by
    intro A
    simp only [e, Equiv.coe_fn_mk, isValidArr, lastState, Prod.ext_iff]
    constructor
    · rintro ⟨hA, hr, hd⟩
      refine ⟨fun i => hA ⟨i.1, by omega⟩, hd, ?_, hr⟩
      rw [← hd, mmCode_le_iff]
      exact hA ⟨k, Nat.lt_succ_self k⟩
    · rintro ⟨hA', hd, hle, hr⟩
      refine ⟨fun i => ?_, hr, hd⟩
      by_cases hi : i.1 < k
      · exact hA' ⟨i.1, hi⟩
      · have hieq : i = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
        subst hieq
        dsimp only
        exact (mmCode_le_iff
          (A (⟨k, by omega⟩, 0), A (⟨k, by omega⟩, 1))
          (A (⟨k + 1, by omega⟩, 0), A (⟨k + 1, by omega⟩, 1))
          (A (⟨k + 2, by omega⟩, 0), A (⟨k + 2, by omega⟩, 1))).mp (by rw [hd]; exact hle)
  unfold stateCount stepVec
  rw [Fintype.sum_equiv e _ (fun p =>
      if isValidArr k p.1 ∧ mmCode (lastState k p.1).1 p.2 = s.2 ∧
         (lastState k p.1).2 ≤ s.2 ∧ p.2 = s.1 then (1 : ℤ) else 0)
      (fun A => by simp only [hiff A])]
  rw [Fintype.sum_prod_type]
  have hr_sum : ∀ A' : Fin (k + 2) × Fin 2 → Bool,
      (∑ r' : Bool × Bool,
        if isValidArr k A' ∧ mmCode (lastState k A').1 r' = s.2 ∧
           (lastState k A').2 ≤ s.2 ∧ r' = s.1 then (1 : ℤ) else 0) =
      if isValidArr k A' ∧ mmCode (lastState k A').1 s.1 = s.2 ∧
         (lastState k A').2 ≤ s.2 then (1 : ℤ) else 0 := by
    intro A'
    rw [Finset.sum_eq_single s.1]
    · simp
    · intro r' _ hne; simp [hne]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  simp_rw [hr_sum]
  symm
  trans ∑ r1 : Bool × Bool, ∑ d1 : Fin 3, ∑ A' : Fin (k + 2) × Fin 2 → Bool,
      if isValidArr k A' ∧ lastState k A' = (r1, d1) ∧
         mmCode r1 s.1 = s.2 ∧ d1 ≤ s.2 then (1 : ℤ) else 0
  · refine Finset.sum_congr rfl fun r1 _ => Finset.sum_congr rfl fun d1 _ => ?_
    by_cases hc : mmCode r1 s.1 = s.2 ∧ d1 ≤ s.2
    · simp [hc]
    · simp [hc]
  · rw [show (∑ r1 : Bool × Bool, ∑ d1 : Fin 3, ∑ A' : Fin (k + 2) × Fin 2 → Bool,
          if isValidArr k A' ∧ lastState k A' = (r1, d1) ∧
             mmCode r1 s.1 = s.2 ∧ d1 ≤ s.2 then (1 : ℤ) else 0) =
        ∑ p : (Bool × Bool) × Fin 3, ∑ A' : Fin (k + 2) × Fin 2 → Bool,
          if isValidArr k A' ∧ lastState k A' = p ∧
             mmCode p.1 s.1 = s.2 ∧ p.2 ≤ s.2 then (1 : ℤ) else 0 by
        symm; exact Fintype.sum_prod_type _]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A' _ => ?_
    rw [Finset.sum_eq_single (lastState k A')]
    · simp
    · intro p _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private def tab0 : (Bool × Bool) × Fin 3 → ℤ
  | ((false, false), 0) => 1
  | ((false, false), 1) => 3
  | ((false, false), 2) => 0
  | ((false, true), 0) => 0
  | ((false, true), 1) => 4
  | ((false, true), 2) => 0
  | ((true, false), 0) => 0
  | ((true, false), 1) => 4
  | ((true, false), 2) => 0
  | ((true, true), 0) => 0
  | ((true, true), 1) => 3
  | ((true, true), 2) => 1

private def tab1 : (Bool × Bool) × Fin 3 → ℤ
  | ((false, false), 0) => 1
  | ((false, false), 1) => 11
  | ((false, false), 2) => 0
  | ((false, true), 0) => 0
  | ((false, true), 1) => 15
  | ((false, true), 2) => 0
  | ((true, false), 0) => 0
  | ((true, false), 1) => 15
  | ((true, false), 2) => 0
  | ((true, true), 0) => 0
  | ((true, true), 1) => 12
  | ((true, true), 2) => 4

private def tab2 : (Bool × Bool) × Fin 3 → ℤ
  | ((false, false), 0) => 1
  | ((false, false), 1) => 42
  | ((false, false), 2) => 0
  | ((false, true), 0) => 0
  | ((false, true), 1) => 54
  | ((false, true), 2) => 0
  | ((true, false), 0) => 0
  | ((true, false), 1) => 54
  | ((true, false), 2) => 0
  | ((true, true), 0) => 0
  | ((true, true), 1) => 42
  | ((true, true), 2) => 16

private def tab3 : (Bool × Bool) × Fin 3 → ℤ
  | ((false, false), 0) => 1
  | ((false, false), 1) => 150
  | ((false, false), 2) => 0
  | ((false, true), 0) => 0
  | ((false, true), 1) => 193
  | ((false, true), 2) => 0
  | ((true, false), 0) => 0
  | ((true, false), 1) => 193
  | ((true, false), 2) => 0
  | ((true, true), 0) => 0
  | ((true, true), 1) => 151
  | ((true, true), 2) => 58

private def tab4 : (Bool × Bool) × Fin 3 → ℤ
  | ((false, false), 0) => 1
  | ((false, false), 1) => 537
  | ((false, false), 2) => 0
  | ((false, true), 0) => 0
  | ((false, true), 1) => 688
  | ((false, true), 2) => 0
  | ((true, false), 0) => 0
  | ((true, false), 1) => 688
  | ((true, false), 2) => 0
  | ((true, true), 0) => 0
  | ((true, true), 1) => 537
  | ((true, true), 2) => 209

private def tab5 : (Bool × Bool) × Fin 3 → ℤ
  | ((false, false), 0) => 1
  | ((false, false), 1) => 1913
  | ((false, false), 2) => 0
  | ((false, true), 0) => 0
  | ((false, true), 1) => 2451
  | ((false, true), 2) => 0
  | ((true, false), 0) => 0
  | ((true, false), 1) => 2451
  | ((true, false), 2) => 0
  | ((true, true), 0) => 0
  | ((true, true), 1) => 1914
  | ((true, true), 2) => 746

private lemma stateCount_0_eq : stateCount 0 = tab0 := by
  funext s; rw [stateCount_zero]; revert s; decide
private lemma stateCount_1_eq : stateCount 1 = tab1 := by
  funext s; rw [stateCount_succ, stateCount_0_eq]; revert s; decide
private lemma stateCount_2_eq : stateCount 2 = tab2 := by
  funext s; rw [stateCount_succ, stateCount_1_eq]; revert s; decide
private lemma stateCount_3_eq : stateCount 3 = tab3 := by
  funext s; rw [stateCount_succ, stateCount_2_eq]; revert s; decide
private lemma stateCount_4_eq : stateCount 4 = tab4 := by
  funext s; rw [stateCount_succ, stateCount_3_eq]; revert s; decide
private lemma stateCount_5_eq : stateCount 5 = tab5 := by
  funext s; rw [stateCount_succ, stateCount_4_eq]; revert s; decide

private lemma stateCount_rec_base :
    stateCount 5 = fun s =>
      4 * stateCount 4 s - 6 * stateCount 2 s + stateCount 1 s + 2 * stateCount 0 s := by
  rw [stateCount_5_eq, stateCount_4_eq, stateCount_2_eq, stateCount_1_eq, stateCount_0_eq]
  funext s; revert s; decide

private lemma stateCount_rec (m : ℕ) :
    stateCount (m + 5) = fun s =>
      4 * stateCount (m + 4) s - 6 * stateCount (m + 2) s +
        stateCount (m + 1) s + 2 * stateCount m s := by
  induction m with
  | zero => exact stateCount_rec_base
  | succ m ih =>
    funext s
    conv_lhs =>
      rw [stateCount_succ (m + 5) s, ih, stepVec_add, stepVec_add, stepVec_sub,
        stepVec_smul, stepVec_smul, stepVec_smul,
        ← stateCount_succ (m + 4) s, ← stateCount_succ (m + 2) s,
        ← stateCount_succ (m + 1) s, ← stateCount_succ m s]

private lemma A235510_rec (m : ℕ) :
    (A235510 (m + 6) : ℤ) =
      4 * A235510 (m + 5) - 6 * A235510 (m + 3) + A235510 (m + 2) + 2 * A235510 (m + 1) := by
  simp only [A235510_eq_sum_stateCount, stateCount_rec, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]

private lemma A235510_small :
    A235510 1 = 16 ∧ A235510 2 = 58 ∧ A235510 3 = 209 ∧
    A235510 4 = 746 ∧ A235510 5 = 2660 := by
  have h1 : (A235510 1 : ℤ) = 16 := by rw [A235510_eq_sum_stateCount 0, stateCount_0_eq]; decide
  have h2 : (A235510 2 : ℤ) = 58 := by rw [A235510_eq_sum_stateCount 1, stateCount_1_eq]; decide
  have h3 : (A235510 3 : ℤ) = 209 := by rw [A235510_eq_sum_stateCount 2, stateCount_2_eq]; decide
  have h4 : (A235510 4 : ℤ) = 746 := by rw [A235510_eq_sum_stateCount 3, stateCount_3_eq]; decide
  have h5 : (A235510 5 : ℤ) = 2660 := by rw [A235510_eq_sum_stateCount 4, stateCount_4_eq]; decide
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3,
    by exact_mod_cast h4, by exact_mod_cast h5⟩

private lemma coeff_X_pow_mul_eq (k : ℕ) (f : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n (PowerSeries.X ^ k * f) =
      if k ≤ n then PowerSeries.coeff (n - k) f else 0 := by
  rw [PowerSeries.coeff_mul]
  split_ifs with hk
  · rw [Finset.sum_eq_single (k, n - k)]
    · rw [PowerSeries.coeff_X_pow, if_pos rfl, one_mul]
    · intro p hp hne
      rw [Finset.mem_antidiagonal] at hp
      have hne1 : p.1 ≠ k := fun h => hne (Prod.ext h (by omega))
      rw [PowerSeries.coeff_X_pow, if_neg hne1, zero_mul]
    · intro hnot; exfalso; apply hnot; rw [Finset.mem_antidiagonal]; omega
  · apply Finset.sum_eq_zero
    intro p hp; rw [Finset.mem_antidiagonal] at hp
    rw [PowerSeries.coeff_X_pow, if_neg (by omega), zero_mul]

private lemma A235510_gf :
    (1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) * (1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235510 n : ℤ)) =
      PowerSeries.X * (16 - 6 * PowerSeries.X - 23 * PowerSeries.X ^ 2 +
        6 * PowerSeries.X ^ 3 + 8 * PowerSeries.X ^ 4) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235510 n : ℤ))
  have hlhs : (1 - PowerSeries.X) ^ 2 * (1 + PowerSeries.X) *
        (1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.C 4 * (PowerSeries.X ^ 1 * F) +
        PowerSeries.C 6 * (PowerSeries.X ^ 3 * F) -
        PowerSeries.X ^ 4 * F - PowerSeries.C 2 * (PowerSeries.X ^ 5 * F) := by
    have h2 : PowerSeries.C (2 : ℤ) = (2 : PowerSeries ℤ) := rfl
    have h4 : PowerSeries.C (4 : ℤ) = (4 : PowerSeries ℤ) := rfl
    have h6 : PowerSeries.C (6 : ℤ) = (6 : PowerSeries ℤ) := rfl
    rw [h2, h4, h6, pow_one]; ring
  have hrhs : (PowerSeries.X : PowerSeries ℤ) *
        (16 - 6 * PowerSeries.X - 23 * PowerSeries.X ^ 2 +
          6 * PowerSeries.X ^ 3 + 8 * PowerSeries.X ^ 4) =
      PowerSeries.C 16 * PowerSeries.X - PowerSeries.C 6 * PowerSeries.X ^ 2 -
      PowerSeries.C 23 * PowerSeries.X ^ 3 + PowerSeries.C 6 * PowerSeries.X ^ 4 +
      PowerSeries.C 8 * PowerSeries.X ^ 5 := by
    have h6 : PowerSeries.C (6 : ℤ) = (6 : PowerSeries ℤ) := rfl
    have h8 : PowerSeries.C (8 : ℤ) = (8 : PowerSeries ℤ) := rfl
    have h16 : PowerSeries.C (16 : ℤ) = (16 : PowerSeries ℤ) := rfl
    have h23 : PowerSeries.C (23 : ℤ) = (23 : PowerSeries ℤ) := rfl
    rw [h6, h8, h16, h23]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2, h3, h4, h5⟩ := A235510_small
  by_cases hn5 : n ≤ 5
  · interval_cases n <;> simp [F, h1, h2, h3, h4, h5]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show n ≠ 5 by omega,
      show 1 ≤ n by omega, show 3 ≤ n by omega, show 4 ≤ n by omega, show 5 ≤ n by omega,
      show n - 1 ≠ 0 by omega, show n - 3 ≠ 0 by omega, show n - 4 ≠ 0 by omega,
      show n - 5 ≠ 0 by omega, ↓reduceIte, mul_zero, sub_zero, add_zero]
    have hrec := A235510_rec (n - 6)
    simp only [show n - 6 + 6 = n by omega, show n - 6 + 5 = n - 1 by omega,
      show n - 6 + 3 = n - 3 by omega, show n - 6 + 2 = n - 4 by omega,
      show n - 6 + 1 = n - 5 by omega] at hrec
    linarith

private lemma A235510_binet (n : ℕ) (hn : 1 ≤ n) :
    (A235510 n : ℝ) =
      (1 / 544 : ℝ) *
        (-221 - 68 * (-1 : ℝ) ^ n +
         (2 : ℝ) ^ (-1 - (n : ℤ)) *
           ((2533 - 611 * Real.sqrt 17) * (3 - Real.sqrt 17) ^ n +
            (3 + Real.sqrt 17) ^ n * (2533 + 611 * Real.sqrt 17)) -
         68 * (1 + (n : ℝ))) := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  suffices h : ∀ k : ℕ,
      544 * (A235510 (k + 1) : ℝ) =
        -221 - 68 * (-1 : ℝ) ^ (k + 1) +
         (2 : ℝ) ^ (-1 - ((k + 1 : ℕ) : ℤ)) *
           ((2533 - 611 * Real.sqrt 17) * (3 - Real.sqrt 17) ^ (k + 1) +
            (3 + Real.sqrt 17) ^ (k + 1) * (2533 + 611 * Real.sqrt 17)) -
         68 * (1 + ((k + 1 : ℕ) : ℝ)) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    linarith [h k]
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h1, h2, h3, h4, h5⟩ := A235510_small
    have hz : ∀ j : ℕ, (2 : ℝ) ^ (-1 - ((j + 1 : ℕ) : ℤ)) = (1 / 2 : ℝ) ^ (j + 2) := by
      intro j
      have : -1 - ((j + 1 : ℕ) : ℤ) = -((j + 2 : ℕ) : ℤ) := by omega
      rw [this, zpow_neg, zpow_natCast, one_div, inv_pow]
    rcases k with _ | _ | _ | _ | _ | m
    · rw [hz 0]; simp only [zero_add, h1, Nat.cast_ofNat, pow_one]
      have : (2533 - 611 * Real.sqrt 17) * (3 - Real.sqrt 17) +
          (3 + Real.sqrt 17) * (2533 + 611 * Real.sqrt 17) =
          15198 + 1222 * Real.sqrt 17 ^ 2 := by ring
      norm_num; linarith [this, hs]
    · rw [hz 1]; simp only [Nat.reduceAdd, h2, Nat.cast_ofNat]
      have hsq1 : (3 - Real.sqrt 17) ^ 2 = 26 - 6 * Real.sqrt 17 := by
        have : (3 - Real.sqrt 17) ^ 2 = 9 - 6 * Real.sqrt 17 + Real.sqrt 17 ^ 2 := by ring
        rw [this, hs]; ring
      have hsq2 : (3 + Real.sqrt 17) ^ 2 = 26 + 6 * Real.sqrt 17 := by
        have : (3 + Real.sqrt 17) ^ 2 = 9 + 6 * Real.sqrt 17 + Real.sqrt 17 ^ 2 := by ring
        rw [this, hs]; ring
      rw [hsq1, hsq2]
      have : (2533 - 611 * Real.sqrt 17) * (26 - 6 * Real.sqrt 17) +
          (26 + 6 * Real.sqrt 17) * (2533 + 611 * Real.sqrt 17) =
          131716 + 7332 * Real.sqrt 17 ^ 2 := by ring
      norm_num; linarith [this, hs]
    · rw [hz 2]; simp only [Nat.reduceAdd, h3, Nat.cast_ofNat]
      have hc1 : (3 - Real.sqrt 17) ^ 3 = 180 - 44 * Real.sqrt 17 := by
        have : (3 - Real.sqrt 17) ^ 3 = 27 - 27 * Real.sqrt 17 + 9 * Real.sqrt 17 ^ 2 - Real.sqrt 17 ^ 2 * Real.sqrt 17 := by ring
        rw [this, hs]; ring
      have hc2 : (3 + Real.sqrt 17) ^ 3 = 180 + 44 * Real.sqrt 17 := by
        have : (3 + Real.sqrt 17) ^ 3 = 27 + 27 * Real.sqrt 17 + 9 * Real.sqrt 17 ^ 2 + Real.sqrt 17 ^ 2 * Real.sqrt 17 := by ring
        rw [this, hs]; ring
      rw [hc1, hc2]
      have : (2533 - 611 * Real.sqrt 17) * (180 - 44 * Real.sqrt 17) +
          (180 + 44 * Real.sqrt 17) * (2533 + 611 * Real.sqrt 17) =
          911880 + 53768 * Real.sqrt 17 ^ 2 := by ring
      norm_num; linarith [this, hs]
    · rw [hz 3]; simp only [Nat.reduceAdd, h4, Nat.cast_ofNat]
      have hq1 : (3 - Real.sqrt 17) ^ 4 = 1288 - 312 * Real.sqrt 17 := by
        have hsq : (3 - Real.sqrt 17) ^ 2 = 26 - 6 * Real.sqrt 17 := by
          have : (3 - Real.sqrt 17) ^ 2 = 9 - 6 * Real.sqrt 17 + Real.sqrt 17 ^ 2 := by ring
          rw [this, hs]; ring
        have : (3 - Real.sqrt 17) ^ 4 = ((3 - Real.sqrt 17) ^ 2) ^ 2 := by ring
        rw [this, hsq]
        have : (26 - 6 * Real.sqrt 17) ^ 2 = 676 - 312 * Real.sqrt 17 + 36 * Real.sqrt 17 ^ 2 := by ring
        rw [this, hs]; ring
      have hq2 : (3 + Real.sqrt 17) ^ 4 = 1288 + 312 * Real.sqrt 17 := by
        have hsq : (3 + Real.sqrt 17) ^ 2 = 26 + 6 * Real.sqrt 17 := by
          have : (3 + Real.sqrt 17) ^ 2 = 9 + 6 * Real.sqrt 17 + Real.sqrt 17 ^ 2 := by ring
          rw [this, hs]; ring
        have : (3 + Real.sqrt 17) ^ 4 = ((3 + Real.sqrt 17) ^ 2) ^ 2 := by ring
        rw [this, hsq]
        have : (26 + 6 * Real.sqrt 17) ^ 2 = 676 + 312 * Real.sqrt 17 + 36 * Real.sqrt 17 ^ 2 := by ring
        rw [this, hs]; ring
      rw [hq1, hq2]
      have : (2533 - 611 * Real.sqrt 17) * (1288 - 312 * Real.sqrt 17) +
          (1288 + 312 * Real.sqrt 17) * (2533 + 611 * Real.sqrt 17) =
          6525008 + 381264 * Real.sqrt 17 ^ 2 := by ring
      norm_num; linarith [this, hs]
    · rw [hz 4]; simp only [Nat.reduceAdd, h5, Nat.cast_ofNat]
      have hf1 : (3 - Real.sqrt 17) ^ 5 = 9168 - 2224 * Real.sqrt 17 := by
        have hq : (3 - Real.sqrt 17) ^ 4 = 1288 - 312 * Real.sqrt 17 := by
          have hsq : (3 - Real.sqrt 17) ^ 2 = 26 - 6 * Real.sqrt 17 := by
            have : (3 - Real.sqrt 17) ^ 2 = 9 - 6 * Real.sqrt 17 + Real.sqrt 17 ^ 2 := by ring
            rw [this, hs]; ring
          have : (3 - Real.sqrt 17) ^ 4 = ((3 - Real.sqrt 17) ^ 2) ^ 2 := by ring
          rw [this, hsq]
          have : (26 - 6 * Real.sqrt 17) ^ 2 = 676 - 312 * Real.sqrt 17 + 36 * Real.sqrt 17 ^ 2 := by ring
          rw [this, hs]; ring
        rw [pow_succ, hq]
        have : (1288 - 312 * Real.sqrt 17) * (3 - Real.sqrt 17) =
            3864 - 2224 * Real.sqrt 17 + 312 * Real.sqrt 17 ^ 2 := by ring
        rw [this, hs]; ring
      have hf2 : (3 + Real.sqrt 17) ^ 5 = 9168 + 2224 * Real.sqrt 17 := by
        have hq : (3 + Real.sqrt 17) ^ 4 = 1288 + 312 * Real.sqrt 17 := by
          have hsq : (3 + Real.sqrt 17) ^ 2 = 26 + 6 * Real.sqrt 17 := by
            have : (3 + Real.sqrt 17) ^ 2 = 9 + 6 * Real.sqrt 17 + Real.sqrt 17 ^ 2 := by ring
            rw [this, hs]; ring
          have : (3 + Real.sqrt 17) ^ 4 = ((3 + Real.sqrt 17) ^ 2) ^ 2 := by ring
          rw [this, hsq]
          have : (26 + 6 * Real.sqrt 17) ^ 2 = 676 + 312 * Real.sqrt 17 + 36 * Real.sqrt 17 ^ 2 := by ring
          rw [this, hs]; ring
        rw [pow_succ, hq]
        have : (1288 + 312 * Real.sqrt 17) * (3 + Real.sqrt 17) =
            3864 + 2224 * Real.sqrt 17 + 312 * Real.sqrt 17 ^ 2 := by ring
        rw [this, hs]; ring
      rw [hf1, hf2]
      have : (2533 - 611 * Real.sqrt 17) * (9168 - 2224 * Real.sqrt 17) +
          (9168 + 2224 * Real.sqrt 17) * (2533 + 611 * Real.sqrt 17) =
          46445088 + 2717728 * Real.sqrt 17 ^ 2 := by ring
      norm_num; linarith [this, hs]
    · have hrec : (A235510 (m + 6) : ℝ) =
          4 * A235510 (m + 5) - 6 * A235510 (m + 3) + A235510 (m + 2) + 2 * A235510 (m + 1) := by
        exact_mod_cast A235510_rec m
      have ih4 := ih (m + 4) (by omega)
      have ih2 := ih (m + 2) (by omega)
      have ih1 := ih (m + 1) (by omega)
      have ih0 := ih m (by omega)
      rw [show m + 5 + 1 = m + 6 by omega, hrec]
      have hcomb : 544 * (4 * (A235510 (m + 5) : ℝ) - 6 * A235510 (m + 3) +
          A235510 (m + 2) + 2 * A235510 (m + 1)) =
          4 * (544 * A235510 (m + 4 + 1)) - 6 * (544 * A235510 (m + 2 + 1)) +
          (544 * A235510 (m + 1 + 1)) + 2 * (544 * A235510 (m + 1)) := by ring
      rw [hcomb, ih4, ih2, ih1, ih0]
      have hr1 : ((3 - Real.sqrt 17) / 2) ^ 2 = 3 * ((3 - Real.sqrt 17) / 2) + 2 := by
        linear_combination (1 / 4 : ℝ) * hs
      have hr2 : ((3 + Real.sqrt 17) / 2) ^ 2 = 3 * ((3 + Real.sqrt 17) / 2) + 2 := by
        linear_combination (1 / 4 : ℝ) * hs
      have hterm : ∀ j : ℕ,
          (2 : ℝ) ^ (-1 - ((j + 1 : ℕ) : ℤ)) *
            ((2533 - 611 * Real.sqrt 17) * (3 - Real.sqrt 17) ^ (j + 1) +
             (3 + Real.sqrt 17) ^ (j + 1) * (2533 + 611 * Real.sqrt 17)) =
          (1 / 2 : ℝ) * (2533 - 611 * Real.sqrt 17) * ((3 - Real.sqrt 17) / 2) ^ (j + 1) +
          (1 / 2 : ℝ) * (2533 + 611 * Real.sqrt 17) * ((3 + Real.sqrt 17) / 2) ^ (j + 1) := by
        intro j
        rw [hz j, div_pow, div_pow, div_pow, one_pow, show j + 2 = 1 + (j + 1) by omega,
          pow_add, pow_one]
        ring
      have hpoly : ∀ u : ℝ, u ^ 2 = 3 * u + 2 →
          u ^ (m + 6) = 4 * u ^ (m + 5) - 6 * u ^ (m + 3) + u ^ (m + 2) + 2 * u ^ (m + 1) := by
        intro u hu
        have hfac : u ^ 5 - 4 * u ^ 4 + 6 * u ^ 2 - u - 2 = (u ^ 3 - u ^ 2 - u + 1) * (u ^ 2 - 3 * u - 2) := by
          ring
        have h0 : u ^ 5 - 4 * u ^ 4 + 6 * u ^ 2 - u - 2 = 0 := by rw [hfac, hu]; ring
        have hmul : u ^ (m + 1) * (u ^ 5 - 4 * u ^ 4 + 6 * u ^ 2 - u - 2) = 0 := by rw [h0, mul_zero]
        have he1 : u ^ (m + 6) = u ^ (m + 1) * u ^ 5 := by rw [← pow_add]
        have he2 : u ^ (m + 5) = u ^ (m + 1) * u ^ 4 := by rw [← pow_add]
        have he3 : u ^ (m + 3) = u ^ (m + 1) * u ^ 2 := by rw [← pow_add]
        have he4 : u ^ (m + 2) = u ^ (m + 1) * u := by rw [pow_succ]
        rw [he1, he2, he3, he4]; linarith
      have hp1 := hpoly ((3 - Real.sqrt 17) / 2) hr1
      have hp2 := hpoly ((3 + Real.sqrt 17) / 2) hr2
      have hneg : ∀ j : ℕ, (-1 : ℝ) ^ (m + j + 1) = (-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ j := by
        intro j; rw [show m + j + 1 = (m + 1) + j by omega, pow_add]
      have hneg5 : (-1 : ℝ) ^ (m + 6) = (-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ 5 := by
        rw [show m + 6 = (m + 1) + 5 by omega, pow_add]
      rw [show m + 6 = m + 5 + 1 by omega]
      rw [hterm (m + 5), hterm (m + 4), hterm (m + 2), hterm (m + 1), hterm m]
      rw [show m + 5 + 1 = m + 6 by omega, show m + 4 + 1 = m + 5 by omega,
        show m + 2 + 1 = m + 3 by omega, show m + 1 + 1 = m + 2 by omega]
      rw [hp1, hp2, hneg5,
        show (-1 : ℝ) ^ (m + 5) = (-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ 4 by exact hneg 4,
        show (-1 : ℝ) ^ (m + 3) = (-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ 2 by exact hneg 2,
        show (-1 : ℝ) ^ (m + 2) = (-1 : ℝ) ^ (m + 1) * (-1 : ℝ) ^ 1 by exact hneg 1]
      push_cast; ring

end OMA.P_oeis_a235510

theorem OMA.solution : type_of% @OMA.S_oeis_a235510.main :=
  ⟨OMA.P_oeis_a235510.A235510_gf, OMA.P_oeis_a235510.A235510_binet⟩
