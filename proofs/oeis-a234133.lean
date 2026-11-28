import OMAStatements.S_oeis_a234133
import Mathlib.Tactic

namespace OMA.P_oeis_a234133

open OMA.S_oeis_a234133

private def adj (r1 r2 : Fin 4 × Fin 4) : Bool :=
  decide (validBlock r1.1 r1.2 r2.1 r2.2)

private def stepVec (v : Fin 4 × Fin 4 → ℤ) (r2 : Fin 4 × Fin 4) : ℤ :=
  ∑ r1 : Fin 4 × Fin 4, if adj r1 r2 then v r1 else 0

private lemma stepVec_add (u v : Fin 4 × Fin 4 → ℤ) (r : Fin 4 × Fin 4) :
    stepVec (fun x => u x + v x) r = stepVec u r + stepVec v r := by
  unfold stepVec
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private lemma stepVec_sub (u v : Fin 4 × Fin 4 → ℤ) (r : Fin 4 × Fin 4) :
    stepVec (fun x => u x - v x) r = stepVec u r - stepVec v r := by
  unfold stepVec
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private lemma stepVec_smul (c : ℤ) (v : Fin 4 × Fin 4 → ℤ) (r : Fin 4 × Fin 4) :
    stepVec (fun x => c * v x) r = c * stepVec v r := by
  unfold stepVec
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private def isValidArr (n : ℕ) (A : Fin (n + 1) × Fin 2 → Fin 4) : Prop :=
  ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
    (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1))

private instance (n : ℕ) (A : Fin (n + 1) × Fin 2 → Fin 4) : Decidable (isValidArr n A) := by
  unfold isValidArr; infer_instance

private def rowCount (n : ℕ) (r : Fin 4 × Fin 4) : ℤ :=
  ∑ A : Fin (n + 1) × Fin 2 → Fin 4,
    if isValidArr n A ∧ (A (⟨n, Nat.lt_succ_self n⟩, 0), A (⟨n, Nat.lt_succ_self n⟩, 1)) = r
    then 1 else 0

private lemma A234133_eq_sum_rowCount (n : ℕ) :
    (A234133 n : ℤ) = ∑ r : Fin 4 × Fin 4, rowCount n r := by
  unfold A234133 rowCount
  rw [Finset.sum_comm]
  have hcard : ∀ S : Finset (Fin (n + 1) × Fin 2 → Fin 4),
      (S.card : ℤ) = ∑ A : Fin (n + 1) × Fin 2 → Fin 4, if A ∈ S then (1 : ℤ) else 0 := by
    intro S; simp
  rw [hcard]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, isValidArr]
  by_cases hA : ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
      (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1))
  · rw [if_pos hA]
    rw [Finset.sum_eq_single (A (⟨n, Nat.lt_succ_self n⟩, 0), A (⟨n, Nat.lt_succ_self n⟩, 1))]
    · simp [hA]
    · intro r _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  · rw [if_neg hA]
    refine (Finset.sum_eq_zero fun r _ => ?_).symm
    simp [hA]

private lemma rowCount_zero (r : Fin 4 × Fin 4) : rowCount 0 r = 1 := by
  unfold rowCount isValidArr
  let A0 : Fin 1 × Fin 2 → Fin 4 := fun p => if p.2 = 0 then r.1 else r.2
  rw [Finset.sum_eq_single A0]
  · simp [A0]
  · intro A _ hne
    rw [if_neg]
    rintro ⟨_, hr⟩
    apply hne
    funext ⟨i, j⟩
    fin_cases i; fin_cases j
    · exact congrArg Prod.fst hr
    · exact congrArg Prod.snd hr
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private lemma rowCount_succ (n : ℕ) (r : Fin 4 × Fin 4) :
    rowCount (n + 1) r = stepVec (rowCount n) r := by
  let e : (Fin (n + 2) × Fin 2 → Fin 4) ≃ ((Fin (n + 1) × Fin 2 → Fin 4) × (Fin 4 × Fin 4)) :=
    { toFun := fun A =>
        (fun p => A (⟨p.1.1, by omega⟩, p.2),
         (A (⟨n + 1, Nat.lt_succ_self _⟩, 0), A (⟨n + 1, Nat.lt_succ_self _⟩, 1)))
      invFun := fun ⟨A', r'⟩ p =>
        if h : p.1.1 < n + 1 then A' (⟨p.1.1, h⟩, p.2)
        else if p.2 = 0 then r'.1 else r'.2
      left_inv := fun A => by
        funext ⟨i, j⟩
        by_cases h : i.1 < n + 1
        · simp [h]
        · have hi : i = ⟨n + 1, Nat.lt_succ_self _⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
          subst hi; fin_cases j <;> simp
      right_inv := fun ⟨A', r'⟩ => by
        apply Prod.ext
        · funext ⟨i, j⟩; simp [i.isLt]
        · simp }
  have hiff : ∀ A : Fin (n + 2) × Fin 2 → Fin 4,
      (isValidArr (n + 1) A ∧
       (A (⟨n + 1, Nat.lt_succ_self _⟩, 0), A (⟨n + 1, Nat.lt_succ_self _⟩, 1)) = r) ↔
      (isValidArr n (e A).1 ∧
       adj ((e A).1 (⟨n, Nat.lt_succ_self n⟩, 0), (e A).1 (⟨n, Nat.lt_succ_self n⟩, 1)) (e A).2 = true ∧
       (e A).2 = r) := by
    intro A
    simp only [e, Equiv.coe_fn_mk, isValidArr, adj, decide_eq_true_eq]
    constructor
    · rintro ⟨hA, hr⟩
      refine ⟨fun i => hA ⟨i.1, by omega⟩, hA ⟨n, Nat.lt_succ_self n⟩, hr⟩
    · rintro ⟨hA', hlast, hr⟩
      refine ⟨fun i => ?_, hr⟩
      by_cases hi : i.1 < n
      · exact hA' ⟨i.1, hi⟩
      · have hieq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
        subst hieq; exact hlast
  unfold rowCount stepVec
  rw [Fintype.sum_equiv e _ (fun p =>
      if isValidArr n p.1 ∧
         adj (p.1 (⟨n, Nat.lt_succ_self n⟩, 0), p.1 (⟨n, Nat.lt_succ_self n⟩, 1)) p.2 = true ∧
         p.2 = r then (1 : ℤ) else 0)
      (fun A => by simp only [hiff A])]
  rw [Fintype.sum_prod_type]
  have hr_sum : ∀ A' : Fin (n + 1) × Fin 2 → Fin 4,
      (∑ r' : Fin 4 × Fin 4,
        if isValidArr n A' ∧
           adj (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1)) r' = true ∧
           r' = r then (1 : ℤ) else 0) =
      if isValidArr n A' ∧
         adj (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1)) r = true
      then (1 : ℤ) else 0 := by
    intro A'
    rw [Finset.sum_eq_single r]
    · simp
    · intro r' _ hne; simp [hne]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  simp_rw [hr_sum]
  symm
  trans ∑ r1 : Fin 4 × Fin 4, ∑ A' : Fin (n + 1) × Fin 2 → Fin 4,
      if isValidArr n A' ∧
         (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1)) = r1 ∧
         adj r1 r = true then (1 : ℤ) else 0
  · refine Finset.sum_congr rfl fun r1 _ => ?_
    by_cases hadj : adj r1 r = true <;> simp [hadj]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A' _ => ?_
    rw [Finset.sum_eq_single (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1))]
    · simp
    · intro r1 _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private lemma rowCount_zero_fun : rowCount 0 = fun _ => 1 := funext rowCount_zero
private lemma rowCount_succ_fun (n : ℕ) : rowCount (n + 1) = stepVec (rowCount n) :=
  funext (rowCount_succ n)

private def tab1 (r : Fin 4 × Fin 4) : ℤ :=
  match r.1.1, r.2.1 with
  | 0, 3 | 3, 0 => 4
  | 1, 2 | 2, 1 => 0
  | _, _ => 2

private def tab2 (r : Fin 4 × Fin 4) : ℤ :=
  match r.1.1, r.2.1 with
  | 0, 0 | 0, 3 | 1, 1 | 2, 2 | 3, 0 | 3, 3 => 8
  | 1, 2 | 2, 1 => 0
  | _, _ => 4

private def tab3 (r : Fin 4 × Fin 4) : ℤ :=
  match r.1.1, r.2.1 with
  | 0, 3 | 3, 0 => 32
  | 0, 0 | 1, 1 | 2, 2 | 3, 3 => 16
  | 1, 2 | 2, 1 => 0
  | _, _ => 8

private lemma rowCount_1_eq : rowCount 1 = tab1 := by
  funext r; rw [rowCount_succ_fun, rowCount_zero_fun]; revert r; decide

private lemma rowCount_2_eq : rowCount 2 = tab2 := by
  funext r; rw [rowCount_succ_fun, rowCount_1_eq]; revert r; decide

private lemma rowCount_3_eq : rowCount 3 = tab3 := by
  funext r; rw [rowCount_succ_fun, rowCount_2_eq]; revert r; decide

private lemma rowCount_rec_base :
    rowCount 4 = fun r => 2 * rowCount 3 r + 8 * rowCount 2 r - 16 * rowCount 1 r := by
  funext r
  rw [rowCount_succ_fun 3, rowCount_3_eq, rowCount_2_eq, rowCount_1_eq]
  revert r; decide

private lemma rowCount_rec (m : ℕ) :
    rowCount (m + 4) = fun r => 2 * rowCount (m + 3) r + 8 * rowCount (m + 2) r - 16 * rowCount (m + 1) r := by
  induction m with
  | zero => exact rowCount_rec_base
  | succ m ih =>
    funext r
    conv_lhs =>
      rw [rowCount_succ (m + 4) r, ih, stepVec_sub, stepVec_add, stepVec_smul, stepVec_smul,
        stepVec_smul, ← rowCount_succ (m + 3) r, ← rowCount_succ (m + 2) r, ← rowCount_succ (m + 1) r]

private lemma A234133_rec (m : ℕ) :
    (A234133 (m + 4) : ℤ) = 2 * A234133 (m + 3) + 8 * A234133 (m + 2) - 16 * A234133 (m + 1) := by
  simp only [A234133_eq_sum_rowCount]
  rw [rowCount_rec m, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    ← Finset.mul_sum, ← Finset.mul_sum]

private lemma A234133_small : A234133 1 = 32 ∧ A234133 2 = 80 ∧ A234133 3 = 192 := by
  have h1 : (A234133 1 : ℤ) = 32 := by
    rw [A234133_eq_sum_rowCount, rowCount_1_eq]; decide
  have h2 : (A234133 2 : ℤ) = 80 := by
    rw [A234133_eq_sum_rowCount, rowCount_2_eq]; decide
  have h3 : (A234133 3 : ℤ) = 192 := by
    rw [A234133_eq_sum_rowCount, rowCount_3_eq]; decide
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3⟩

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

private lemma A234133_gf :
    (1 - 2 * PowerSeries.X) * (1 - 8 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A234133 n : ℤ)) =
      16 * PowerSeries.X * (2 + PowerSeries.X - 14 * PowerSeries.X ^ 2) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A234133 n : ℤ))
  have hlhs : (1 - 2 * PowerSeries.X) * (1 - 8 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.C 2 * (PowerSeries.X ^ 1 * F) -
        PowerSeries.C 8 * (PowerSeries.X ^ 2 * F) + PowerSeries.C 16 * (PowerSeries.X ^ 3 * F) := by
    have h2 : PowerSeries.C (2 : ℤ) = (2 : PowerSeries ℤ) := rfl
    have h8 : PowerSeries.C (8 : ℤ) = (8 : PowerSeries ℤ) := rfl
    have h16 : PowerSeries.C (16 : ℤ) = (16 : PowerSeries ℤ) := rfl
    rw [h2, h8, h16, pow_one]; ring
  have hrhs : 16 * (PowerSeries.X : PowerSeries ℤ) *
        (2 + PowerSeries.X - 14 * PowerSeries.X ^ 2) =
      PowerSeries.C 32 * PowerSeries.X + PowerSeries.C 16 * PowerSeries.X ^ 2 -
      PowerSeries.C 224 * PowerSeries.X ^ 3 := by
    have h32 : PowerSeries.C (32 : ℤ) = (32 : PowerSeries ℤ) := rfl
    have h16 : PowerSeries.C (16 : ℤ) = (16 : PowerSeries ℤ) := rfl
    have h224 : PowerSeries.C (224 : ℤ) = (224 : PowerSeries ℤ) := rfl
    rw [h32, h16, h224]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2, h3⟩ := A234133_small
  by_cases hn3 : n ≤ 3
  · interval_cases n <;> simp [F, h1, h2, h3]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show 3 ≤ n by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, ↓reduceIte, mul_zero, sub_zero, add_zero]
    have hrec := A234133_rec (n - 4)
    simp only [show n - 4 + 4 = n by omega, show n - 4 + 3 = n - 1 by omega,
      show n - 4 + 2 = n - 2 by omega, show n - 4 + 1 = n - 3 by omega] at hrec
    linarith

private lemma A234133_closed_int (n : ℕ) (hn : 1 ≤ n) :
    (A234133 n : ℤ) =
      if Even n then (2 : ℤ) ^ (3 + n) + 6 * (8 : ℤ) ^ (n / 2)
      else (2 : ℤ) ^ (3 + n) + 16 * (8 : ℤ) ^ ((n - 1) / 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  clear hn
  rw [Nat.add_sub_cancel]
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h1, h2, h3⟩ := A234133_small
    rcases k with _ | _ | _ | m
    · simp [h1]
    · simp [h2]
    · have ho3 : ¬ Even 3 := by decide
      simp [h3, ho3]
    · have hrec := A234133_rec m
      have ih2 := ih (m + 2) (by omega)
      have ih1 := ih (m + 1) (by omega)
      have ih0 := ih m (by omega)
      rw [show m + 3 + 1 = m + 4 by omega, hrec]
      by_cases hev : Even (m + 4)
      · have h3o : ¬ Even (m + 3) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2e : Even (m + 2) := by rw [Nat.even_iff] at hev ⊢; omega
        have h1o : ¬ Even (m + 1) := by rw [Nat.even_iff] at hev ⊢; omega
        rw [if_pos hev]
        rw [show m + 2 + 1 = m + 3 by omega, if_neg h3o] at ih2
        rw [show m + 1 + 1 = m + 2 by omega, if_pos h2e] at ih1
        rw [if_neg h1o] at ih0
        have hp3 : (2 : ℤ) ^ (3 + (m + 4)) = 8 * (2 : ℤ) ^ (3 + (m + 1)) := by
          rw [show 3 + (m + 4) = (3 + (m + 1)) + 3 by omega, pow_add]; ring
        have hp2 : (2 : ℤ) ^ (3 + (m + 3)) = 4 * (2 : ℤ) ^ (3 + (m + 1)) := by
          rw [show 3 + (m + 3) = (3 + (m + 1)) + 2 by omega, pow_add]; ring
        have hp1 : (2 : ℤ) ^ (3 + (m + 2)) = 2 * (2 : ℤ) ^ (3 + (m + 1)) := by
          rw [show 3 + (m + 2) = (3 + (m + 1)) + 1 by omega, pow_add]; ring
        have h8_4 : (8 : ℤ) ^ ((m + 4) / 2) = 64 * (8 : ℤ) ^ (m / 2) := by
          rw [show (m + 4) / 2 = m / 2 + 2 by omega, pow_add]; ring
        have h8_2 : (8 : ℤ) ^ ((m + 2) / 2) = 8 * (8 : ℤ) ^ (m / 2) := by
          rw [show (m + 2) / 2 = m / 2 + 1 by omega, pow_succ]; ring
        rw [hp3, h8_4]; rw [hp2, h8_2] at ih2; rw [hp1, h8_2] at ih1
        linarith
      · have h3e : Even (m + 3) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2o : ¬ Even (m + 2) := by rw [Nat.even_iff] at hev ⊢; omega
        have h1e : Even (m + 1) := by rw [Nat.even_iff] at hev ⊢; omega
        rw [if_neg hev]
        rw [show m + 2 + 1 = m + 3 by omega, if_pos h3e] at ih2
        rw [show m + 1 + 1 = m + 2 by omega, if_neg h2o] at ih1
        rw [if_pos h1e] at ih0
        have hp3 : (2 : ℤ) ^ (3 + (m + 4)) = 8 * (2 : ℤ) ^ (3 + (m + 1)) := by
          rw [show 3 + (m + 4) = (3 + (m + 1)) + 3 by omega, pow_add]; ring
        have hp2 : (2 : ℤ) ^ (3 + (m + 3)) = 4 * (2 : ℤ) ^ (3 + (m + 1)) := by
          rw [show 3 + (m + 3) = (3 + (m + 1)) + 2 by omega, pow_add]; ring
        have hp1 : (2 : ℤ) ^ (3 + (m + 2)) = 2 * (2 : ℤ) ^ (3 + (m + 1)) := by
          rw [show 3 + (m + 2) = (3 + (m + 1)) + 1 by omega, pow_add]; ring
        have h8_3 : (8 : ℤ) ^ ((m + 3) / 2) = 8 * (8 : ℤ) ^ ((m + 1) / 2) := by
          rw [show (m + 3) / 2 = (m + 1) / 2 + 1 by omega, pow_succ]; ring
        rw [hp3, h8_3]; rw [hp2, h8_3] at ih2; rw [hp1] at ih1
        linarith

private lemma A234133_closed (n : ℕ) (hn : 1 ≤ n) :
    (A234133 n : ℝ) =
      (2 : ℝ) ^ (3 + n) +
      (2 : ℝ) ^ (-(1 : ℝ) / 2 + (3 * (n : ℝ)) / 2) *
        (4 - 4 * (-1 : ℝ) ^ n + 3 * Real.sqrt 2 + 3 * (-1 : ℝ) ^ n * Real.sqrt 2) := by
  have hint : (A234133 n : ℝ) =
      if Even n then (2 : ℝ) ^ (3 + n) + 6 * (8 : ℝ) ^ (n / 2)
      else (2 : ℝ) ^ (3 + n) + 16 * (8 : ℝ) ^ ((n - 1) / 2) := by
    have h := A234133_closed_int n hn
    split_ifs at h ⊢ <;> exact_mod_cast h
  rw [hint]
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hr2 : (2 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 2 := (Real.sqrt_eq_rpow 2).symm
  by_cases hev : Even n
  · rw [if_pos hev]
    obtain ⟨m, rfl⟩ := hev
    have hdiv : (m + m) / 2 = m := by omega
    have hm1 : (-1 : ℝ) ^ (m + m) = 1 := by
      rw [← two_mul, pow_mul]; norm_num
    have hexp : -(1 : ℝ) / 2 + 3 * ((m + m : ℕ) : ℝ) / 2 = ((3 * m - 1 : ℕ) : ℝ) + (1 : ℝ) / 2 := by
      have hm_pos : 1 ≤ m := by omega
      push_cast [Nat.cast_sub (show 1 ≤ 3 * m by omega)]
      ring
    have hrpow : (2 : ℝ) ^ (-(1 : ℝ) / 2 + 3 * ((m + m : ℕ) : ℝ) / 2) * Real.sqrt 2 =
        (8 : ℝ) ^ m := by
      rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast, hr2, mul_assoc,
        ← sq, hs, ← pow_succ, show 3 * m - 1 + 1 = 3 * m by omega, pow_mul]
      norm_num
    rw [hdiv, hm1]
    have hfac : 4 - 4 * (1 : ℝ) + 3 * Real.sqrt 2 + 3 * (1 : ℝ) * Real.sqrt 2 =
        6 * Real.sqrt 2 := by ring
    rw [hfac, ← mul_assoc, mul_comm ((2 : ℝ) ^ _) 6, mul_assoc, hrpow]
  · rw [if_neg hev]
    obtain ⟨m, rfl⟩ := Nat.not_even_iff_odd.mp hev
    have hdiv : (2 * m + 1 - 1) / 2 = m := by omega
    have hm1 : (-1 : ℝ) ^ (2 * m + 1) = -1 := by
      rw [pow_succ, pow_mul]; norm_num
    have hexp : -(1 : ℝ) / 2 + 3 * ((2 * m + 1 : ℕ) : ℝ) / 2 = ((3 * m + 1 : ℕ) : ℝ) := by
      push_cast; ring
    rw [hdiv, hm1, hexp, Real.rpow_natCast, pow_succ, pow_mul]
    norm_num; ring

end OMA.P_oeis_a234133

theorem OMA.solution : type_of% @OMA.S_oeis_a234133.main :=
  ⟨OMA.P_oeis_a234133.A234133_gf, OMA.P_oeis_a234133.A234133_closed⟩
