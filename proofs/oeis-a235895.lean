import OMAStatements.S_oeis_a235895
import Mathlib.Tactic

namespace OMA.P_oeis_a235895

open OMA.S_oeis_a235895

private def adj (r1 r2 : Fin 3 × Fin 3) : Bool :=
  decide (validBlock r1.1 r1.2 r2.1 r2.2)

private def stepVec (v : Fin 3 × Fin 3 → ℤ) (r2 : Fin 3 × Fin 3) : ℤ :=
  ∑ r1 : Fin 3 × Fin 3, if adj r1 r2 then v r1 else 0

private lemma stepVec_add (u v : Fin 3 × Fin 3 → ℤ) (r : Fin 3 × Fin 3) :
    stepVec (fun x => u x + v x) r = stepVec u r + stepVec v r := by
  unfold stepVec
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private lemma stepVec_sub (u v : Fin 3 × Fin 3 → ℤ) (r : Fin 3 × Fin 3) :
    stepVec (fun x => u x - v x) r = stepVec u r - stepVec v r := by
  unfold stepVec
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private lemma stepVec_smul (c : ℤ) (v : Fin 3 × Fin 3 → ℤ) (r : Fin 3 × Fin 3) :
    stepVec (fun x => c * v x) r = c * stepVec v r := by
  unfold stepVec
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private def isValidArr (n : ℕ) (A : Fin (n + 1) × Fin 2 → Fin 3) : Prop :=
  ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
    (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1))

private instance (n : ℕ) (A : Fin (n + 1) × Fin 2 → Fin 3) : Decidable (isValidArr n A) := by
  unfold isValidArr; infer_instance

private def rowCount (n : ℕ) (r : Fin 3 × Fin 3) : ℤ :=
  ∑ A : Fin (n + 1) × Fin 2 → Fin 3,
    if isValidArr n A ∧ (A (⟨n, Nat.lt_succ_self n⟩, 0), A (⟨n, Nat.lt_succ_self n⟩, 1)) = r
    then 1 else 0

private lemma A235895_eq_sum_rowCount (n : ℕ) :
    (A235895 n : ℤ) = ∑ r : Fin 3 × Fin 3, rowCount n r := by
  unfold A235895 rowCount
  rw [Finset.sum_comm]
  have hcard : ∀ S : Finset (Fin (n + 1) × Fin 2 → Fin 3),
      (S.card : ℤ) = ∑ A : Fin (n + 1) × Fin 2 → Fin 3, if A ∈ S then (1 : ℤ) else 0 := by
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

private lemma rowCount_zero (r : Fin 3 × Fin 3) : rowCount 0 r = 1 := by
  unfold rowCount isValidArr
  let A0 : Fin 1 × Fin 2 → Fin 3 := fun p => if p.2 = 0 then r.1 else r.2
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

private lemma rowCount_succ (n : ℕ) (r : Fin 3 × Fin 3) :
    rowCount (n + 1) r = stepVec (rowCount n) r := by
  let e : (Fin (n + 2) × Fin 2 → Fin 3) ≃ ((Fin (n + 1) × Fin 2 → Fin 3) × (Fin 3 × Fin 3)) :=
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
  have hiff : ∀ A : Fin (n + 2) × Fin 2 → Fin 3,
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
  have hr_sum : ∀ A' : Fin (n + 1) × Fin 2 → Fin 3,
      (∑ r' : Fin 3 × Fin 3,
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
  trans ∑ r1 : Fin 3 × Fin 3, ∑ A' : Fin (n + 1) × Fin 2 → Fin 3,
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

private lemma rowCount_rec_base :
    rowCount 3 = fun r => 7 * rowCount 2 r - 10 * rowCount 1 r - 8 * rowCount 0 r := by
  funext r
  simp only [rowCount_succ_fun, rowCount_zero_fun]
  revert r; decide

private lemma rowCount_rec (m : ℕ) :
    rowCount (m + 3) = fun r => 7 * rowCount (m + 2) r - 10 * rowCount (m + 1) r - 8 * rowCount m r := by
  induction m with
  | zero => exact rowCount_rec_base
  | succ m ih =>
    funext r
    conv_lhs =>
      rw [rowCount_succ (m + 3) r, ih, stepVec_sub, stepVec_sub, stepVec_smul, stepVec_smul,
        stepVec_smul, ← rowCount_succ (m + 2) r, ← rowCount_succ (m + 1) r, ← rowCount_succ m r]

private lemma A235895_rec (m : ℕ) :
    (A235895 (m + 4) : ℤ) = 7 * A235895 (m + 3) - 10 * A235895 (m + 2) - 8 * A235895 (m + 1) := by
  simp only [A235895_eq_sum_rowCount]
  rw [show m + 4 = (m + 1) + 3 by omega, show m + 3 = (m + 1) + 2 by omega,
    show m + 2 = (m + 1) + 1 by omega, rowCount_rec (m + 1),
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]

private lemma A235895_small : A235895 1 = 33 ∧ A235895 2 = 125 ∧ A235895 3 = 473 := by
  have h1 : (A235895 1 : ℤ) = 33 := by
    rw [A235895_eq_sum_rowCount, rowCount_succ_fun, rowCount_zero_fun]; decide
  have h2 : (A235895 2 : ℤ) = 125 := by
    rw [A235895_eq_sum_rowCount, rowCount_succ_fun, rowCount_succ_fun, rowCount_zero_fun]; decide
  have h3 : (A235895 3 : ℤ) = 473 := by
    rw [A235895_eq_sum_rowCount, rowCount_succ_fun, rowCount_succ_fun, rowCount_succ_fun,
      rowCount_zero_fun]; decide
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

private lemma A235895_gf :
    (1 - 4 * PowerSeries.X) * (1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235895 n : ℤ)) =
      PowerSeries.X * (33 - 106 * PowerSeries.X - 72 * PowerSeries.X ^ 2) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235895 n : ℤ))
  have hlhs : (1 - 4 * PowerSeries.X) * (1 - 3 * PowerSeries.X - 2 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.C 7 * (PowerSeries.X ^ 1 * F) +
        PowerSeries.C 10 * (PowerSeries.X ^ 2 * F) + PowerSeries.C 8 * (PowerSeries.X ^ 3 * F) := by
    have h7 : PowerSeries.C (7 : ℤ) = (7 : PowerSeries ℤ) := rfl
    have h10 : PowerSeries.C (10 : ℤ) = (10 : PowerSeries ℤ) := rfl
    have h8 : PowerSeries.C (8 : ℤ) = (8 : PowerSeries ℤ) := rfl
    rw [h7, h10, h8, pow_one]; ring
  have hrhs : (PowerSeries.X : PowerSeries ℤ) *
        (33 - 106 * PowerSeries.X - 72 * PowerSeries.X ^ 2) =
      PowerSeries.C 33 * PowerSeries.X - PowerSeries.C 106 * PowerSeries.X ^ 2 -
      PowerSeries.C 72 * PowerSeries.X ^ 3 := by
    have h33 : PowerSeries.C (33 : ℤ) = (33 : PowerSeries ℤ) := rfl
    have h106 : PowerSeries.C (106 : ℤ) = (106 : PowerSeries ℤ) := rfl
    have h72 : PowerSeries.C (72 : ℤ) = (72 : PowerSeries ℤ) := rfl
    rw [h33, h106, h72]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2, h3⟩ := A235895_small
  by_cases hn3 : n ≤ 3
  · interval_cases n <;> simp [F, h1, h2, h3]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show 3 ≤ n by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, ↓reduceIte, mul_zero, sub_zero]
    have hrec := A235895_rec (n - 4)
    simp only [show n - 4 + 4 = n by omega, show n - 4 + 3 = n - 1 by omega,
      show n - 4 + 2 = n - 2 by omega, show n - 4 + 1 = n - 3 by omega] at hrec
    linarith

private lemma A235895_binet (n : ℕ) (hn : 1 ≤ n) :
    (A235895 n : ℝ) =
      (4 : ℝ) ^ (1 + n) +
      ((2 : ℝ) ^ (-1 - (n : ℤ)) *
        ((3 - Real.sqrt 17) ^ n * (-19 + 5 * Real.sqrt 17) +
         (3 + Real.sqrt 17) ^ n * (19 + 5 * Real.sqrt 17))) / Real.sqrt 17 := by
  have hs_pos : (0 : ℝ) < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 17
  set r1 : ℝ := (3 + s) / 2
  set r2 : ℝ := (3 - s) / 2
  have hbinet_eq : ∀ k : ℕ,
      ((2 : ℝ) ^ (-1 - (k : ℤ)) *
        ((3 - s) ^ k * (-19 + 5 * s) + (3 + s) ^ k * (19 + 5 * s))) / s =
      ((-19 + 5 * s) * r2 ^ k + (19 + 5 * s) * r1 ^ k) / (2 * s) := by
    intro k
    have hpow : (2 : ℝ) ^ (-1 - (k : ℤ)) = ((2 : ℝ) ^ k)⁻¹ / 2 := by
      rw [show (-1 : ℤ) - (k : ℤ) = -(k : ℤ) + (-1) by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
        zpow_neg, zpow_natCast]
      norm_num; ring
    have hr1k : r1 ^ k = (3 + s) ^ k * ((2 : ℝ) ^ k)⁻¹ := by
      simp only [r1, div_eq_mul_inv, mul_pow, inv_pow]
    have hr2k : r2 ^ k = (3 - s) ^ k * ((2 : ℝ) ^ k)⁻¹ := by
      simp only [r2, div_eq_mul_inv, mul_pow, inv_pow]
    rw [hpow, hr1k, hr2k]; ring
  rw [hbinet_eq n]
  suffices h : ∀ k : ℕ,
      ((A235895 (k + 1) : ℝ) - (4 : ℝ) ^ (1 + (k + 1))) * (2 * s) =
        (-19 + 5 * s) * r2 ^ (k + 1) + (19 + 5 * s) * r1 ^ (k + 1) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have hk := h k
    have hne : (2 : ℝ) * s ≠ 0 := by positivity
    rw [← sub_eq_iff_eq_add', eq_div_iff hne]
    exact hk
  have hr1_sq : r1 ^ 2 = 3 * r1 + 2 := by
    have : r1 ^ 2 - (3 * r1 + 2) = (s ^ 2 - 17) / 4 := by simp only [r1]; ring
    linarith [this, hs]
  have hr2_sq : r2 ^ 2 = 3 * r2 + 2 := by
    have : r2 ^ 2 - (3 * r2 + 2) = (s ^ 2 - 17) / 4 := by simp only [r2]; ring
    linarith [this, hs]
  have hr1_cub : r1 ^ 3 = 7 * r1 ^ 2 - 10 * r1 - 8 := by
    calc r1 ^ 3 = r1 * r1 ^ 2 := by ring
      _ = r1 * (3 * r1 + 2) := by rw [hr1_sq]
      _ = 7 * r1 ^ 2 - 4 * r1 ^ 2 + 2 * r1 := by ring
      _ = 7 * r1 ^ 2 - 4 * (3 * r1 + 2) + 2 * r1 := by rw [hr1_sq]
      _ = 7 * r1 ^ 2 - 10 * r1 - 8 := by ring
  have hr2_cub : r2 ^ 3 = 7 * r2 ^ 2 - 10 * r2 - 8 := by
    calc r2 ^ 3 = r2 * r2 ^ 2 := by ring
      _ = r2 * (3 * r2 + 2) := by rw [hr2_sq]
      _ = 7 * r2 ^ 2 - 4 * r2 ^ 2 + 2 * r2 := by ring
      _ = 7 * r2 ^ 2 - 4 * (3 * r2 + 2) + 2 * r2 := by rw [hr2_sq]
      _ = 7 * r2 ^ 2 - 10 * r2 - 8 := by ring
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h1, h2, h3⟩ := A235895_small
    rcases k with _ | _ | _ | m
    · rw [show (0 : ℕ) + 1 = 1 by rfl, h1]
      have : (-19 + 5 * s) * r2 ^ 1 + (19 + 5 * s) * r1 ^ 1 -
          ((33 : ℝ) - (4 : ℝ) ^ (1 + 1)) * (2 * s) = 0 := by
        simp only [r1, r2, pow_one]; norm_num; ring
      norm_num at this ⊢; linarith
    · rw [show (1 : ℕ) + 1 = 2 by rfl, h2]
      have : (-19 + 5 * s) * r2 ^ 2 + (19 + 5 * s) * r1 ^ 2 -
          ((125 : ℝ) - (4 : ℝ) ^ (1 + 2)) * (2 * s) = (5 / 2) * (s ^ 2 - 17) * s := by
        simp only [r1, r2]; norm_num; ring
      have h0 : (5 / 2) * (s ^ 2 - 17) * s = 0 := by rw [hs]; ring
      norm_num at this ⊢; linarith
    · rw [show (2 : ℕ) + 1 = 3 by rfl, h3]
      have hr1_3 : r1 ^ 3 = 11 * r1 + 6 := by
        calc r1 ^ 3 = r1 * r1 ^ 2 := by ring
          _ = r1 * (3 * r1 + 2) := by rw [hr1_sq]
          _ = 3 * r1 ^ 2 + 2 * r1 := by ring
          _ = 3 * (3 * r1 + 2) + 2 * r1 := by rw [hr1_sq]
          _ = 11 * r1 + 6 := by ring
      have hr2_3 : r2 ^ 3 = 11 * r2 + 6 := by
        calc r2 ^ 3 = r2 * r2 ^ 2 := by ring
          _ = r2 * (3 * r2 + 2) := by rw [hr2_sq]
          _ = 3 * r2 ^ 2 + 2 * r2 := by ring
          _ = 3 * (3 * r2 + 2) + 2 * r2 := by rw [hr2_sq]
          _ = 11 * r2 + 6 := by ring
      rw [hr1_3, hr2_3]
      have : (-19 + 5 * s) * (11 * r2 + 6) + (19 + 5 * s) * (11 * r1 + 6) -
          ((473 : ℝ) - (4 : ℝ) ^ (1 + 3)) * (2 * s) = 0 := by
        simp only [r1, r2]; norm_num; ring
      norm_num at this ⊢; linarith
    · have hrec : (A235895 (m + 4) : ℝ) =
          7 * A235895 (m + 3) - 10 * A235895 (m + 2) - 8 * A235895 (m + 1) := by
        exact_mod_cast A235895_rec m
      have ih2 := ih (m + 2) (by omega)
      have ih1 := ih (m + 1) (by omega)
      have ih0 := ih m (by omega)
      have h4rec : (4 : ℝ) ^ (1 + (m + 4)) =
          7 * (4 : ℝ) ^ (1 + (m + 3)) - 10 * (4 : ℝ) ^ (1 + (m + 2)) -
          8 * (4 : ℝ) ^ (1 + (m + 1)) := by
        rw [show 1 + (m + 4) = (1 + (m + 1)) + 3 by omega,
          show 1 + (m + 3) = (1 + (m + 1)) + 2 by omega,
          show 1 + (m + 2) = (1 + (m + 1)) + 1 by omega, pow_add, pow_add, pow_add]
        ring
      have hpow1 : r1 ^ (m + 4) = 7 * r1 ^ (m + 3) - 10 * r1 ^ (m + 2) - 8 * r1 ^ (m + 1) := by
        calc r1 ^ (m + 4) = r1 ^ 3 * r1 ^ (m + 1) := by ring
          _ = (7 * r1 ^ 2 - 10 * r1 - 8) * r1 ^ (m + 1) := by rw [hr1_cub]
          _ = 7 * r1 ^ (m + 3) - 10 * r1 ^ (m + 2) - 8 * r1 ^ (m + 1) := by ring
      have hpow2 : r2 ^ (m + 4) = 7 * r2 ^ (m + 3) - 10 * r2 ^ (m + 2) - 8 * r2 ^ (m + 1) := by
        calc r2 ^ (m + 4) = r2 ^ 3 * r2 ^ (m + 1) := by ring
          _ = (7 * r2 ^ 2 - 10 * r2 - 8) * r2 ^ (m + 1) := by rw [hr2_cub]
          _ = 7 * r2 ^ (m + 3) - 10 * r2 ^ (m + 2) - 8 * r2 ^ (m + 1) := by ring
      rw [show m + 3 + 1 = m + 4 by omega, hrec, h4rec, hpow1, hpow2]
      rw [show m + 2 + 1 = m + 3 by omega] at ih2
      rw [show m + 1 + 1 = m + 2 by omega] at ih1
      linarith

end OMA.P_oeis_a235895

theorem OMA.solution : type_of% @OMA.S_oeis_a235895.main :=
  ⟨OMA.P_oeis_a235895.A235895_gf, OMA.P_oeis_a235895.A235895_binet⟩
