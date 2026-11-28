import OMAStatements.S_oeis_a234789
import Mathlib.Tactic

namespace OMA.P_oeis_a234789

open OMA.S_oeis_a234789

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

private lemma A234789_eq_sum_rowCount (n : ℕ) :
    (A234789 n : ℤ) = ∑ r : Fin 4 × Fin 4, rowCount n r := by
  unfold A234789 rowCount
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
  match (r.2.1 + 4 - r.1.1) % 4 with
  | 0 => 13 | 1 => 16 | 2 => 13 | _ => 9

private def tab2 (r : Fin 4 × Fin 4) : ℤ :=
  match (r.2.1 + 4 - r.1.1) % 4 with
  | 0 => 159 | 1 => 204 | 2 => 159 | _ => 104

private lemma rowCount_1_eq : rowCount 1 = tab1 := by
  funext r; rw [rowCount_succ_fun, rowCount_zero_fun]; revert r; decide

private lemma rowCount_2_eq : rowCount 2 = tab2 := by
  funext r; rw [rowCount_succ_fun, rowCount_1_eq]; revert r; decide

private lemma rowCount_rec_base :
    rowCount 3 = fun r => 15 * rowCount 2 r - 36 * rowCount 1 r + 20 * rowCount 0 r := by
  funext r
  rw [rowCount_succ_fun 2, rowCount_2_eq, rowCount_1_eq, rowCount_zero_fun]
  revert r; decide

private lemma rowCount_rec (m : ℕ) :
    rowCount (m + 3) = fun r => 15 * rowCount (m + 2) r - 36 * rowCount (m + 1) r + 20 * rowCount m r := by
  induction m with
  | zero => exact rowCount_rec_base
  | succ m ih =>
    funext r
    conv_lhs =>
      rw [rowCount_succ (m + 3) r, ih, stepVec_add, stepVec_sub, stepVec_smul, stepVec_smul,
        stepVec_smul, ← rowCount_succ (m + 2) r, ← rowCount_succ (m + 1) r, ← rowCount_succ m r]

private lemma A234789_rec (m : ℕ) :
    (A234789 (m + 4) : ℤ) = 15 * A234789 (m + 3) - 36 * A234789 (m + 2) + 20 * A234789 (m + 1) := by
  simp only [A234789_eq_sum_rowCount]
  rw [show m + 4 = (m + 1) + 3 by omega, show m + 3 = (m + 1) + 2 by omega,
    show m + 2 = (m + 1) + 1 by omega, rowCount_rec (m + 1),
    Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum]

private lemma A234789_small : A234789 1 = 204 ∧ A234789 2 = 2504 ∧ A234789 3 = 30536 := by
  have h1 : (A234789 1 : ℤ) = 204 := by
    rw [A234789_eq_sum_rowCount, rowCount_1_eq]; decide
  have h2 : (A234789 2 : ℤ) = 2504 := by
    rw [A234789_eq_sum_rowCount, rowCount_2_eq]; decide
  have h3 : (A234789 3 : ℤ) = 30536 := by
    rw [A234789_eq_sum_rowCount, rowCount_succ_fun 2, rowCount_2_eq]; decide
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

private lemma A234789_gf :
    (1 - 2 * PowerSeries.X) * (1 - 13 * PowerSeries.X + 10 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A234789 n : ℤ)) =
      4 * PowerSeries.X * (51 - 139 * PowerSeries.X + 80 * PowerSeries.X ^ 2) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A234789 n : ℤ))
  have hlhs : (1 - 2 * PowerSeries.X) * (1 - 13 * PowerSeries.X + 10 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.C 15 * (PowerSeries.X ^ 1 * F) +
        PowerSeries.C 36 * (PowerSeries.X ^ 2 * F) - PowerSeries.C 20 * (PowerSeries.X ^ 3 * F) := by
    have h15 : PowerSeries.C (15 : ℤ) = (15 : PowerSeries ℤ) := rfl
    have h36 : PowerSeries.C (36 : ℤ) = (36 : PowerSeries ℤ) := rfl
    have h20 : PowerSeries.C (20 : ℤ) = (20 : PowerSeries ℤ) := rfl
    rw [h15, h36, h20, pow_one]; ring
  have hrhs : 4 * (PowerSeries.X : PowerSeries ℤ) *
        (51 - 139 * PowerSeries.X + 80 * PowerSeries.X ^ 2) =
      PowerSeries.C 204 * PowerSeries.X - PowerSeries.C 556 * PowerSeries.X ^ 2 +
      PowerSeries.C 320 * PowerSeries.X ^ 3 := by
    have h204 : PowerSeries.C (204 : ℤ) = (204 : PowerSeries ℤ) := rfl
    have h556 : PowerSeries.C (556 : ℤ) = (556 : PowerSeries ℤ) := rfl
    have h320 : PowerSeries.C (320 : ℤ) = (320 : PowerSeries ℤ) := rfl
    rw [h204, h556, h320]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2, h3⟩ := A234789_small
  by_cases hn3 : n ≤ 3
  · interval_cases n <;> simp [F, h1, h2, h3]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show 3 ≤ n by omega, show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega,
      show n - 3 ≠ 0 by omega, ↓reduceIte, mul_zero, sub_zero, add_zero]
    have hrec := A234789_rec (n - 4)
    simp only [show n - 4 + 4 = n by omega, show n - 4 + 3 = n - 1 by omega,
      show n - 4 + 2 = n - 2 by omega, show n - 4 + 1 = n - 3 by omega] at hrec
    linarith

private lemma A234789_binet (n : ℕ) (hn : 1 ≤ n) :
    (A234789 n : ℝ) =
      (1 / 129 : ℝ) * (2 : ℝ) ^ (-1 - (n : ℤ)) *
        (-129 * (2 : ℝ) ^ (1 + 2 * n) +
         (2193 - 191 * Real.sqrt 129) * (13 - Real.sqrt 129) ^ n +
         (13 + Real.sqrt 129) ^ n * (2193 + 191 * Real.sqrt 129)) := by
  have hs : Real.sqrt 129 ^ 2 = 129 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 129
  set r1 : ℝ := (13 + s) / 2
  set r2 : ℝ := (13 - s) / 2
  have hbinet_eq : ∀ k : ℕ,
      (1 / 129 : ℝ) * (2 : ℝ) ^ (-1 - (k : ℤ)) *
        (-129 * (2 : ℝ) ^ (1 + 2 * k) +
         (2193 - 191 * s) * (13 - s) ^ k + (13 + s) ^ k * (2193 + 191 * s)) =
      (-258 * (2 : ℝ) ^ k + (2193 - 191 * s) * r2 ^ k + (2193 + 191 * s) * r1 ^ k) / 258 := by
    intro k
    have hpow : (2 : ℝ) ^ (-1 - (k : ℤ)) = ((2 : ℝ) ^ k)⁻¹ / 2 := by
      rw [show (-1 : ℤ) - (k : ℤ) = -(k : ℤ) + (-1) by ring, zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),
        zpow_neg, zpow_natCast]
      norm_num; ring
    have h2k : (2 : ℝ) ^ (1 + 2 * k) = 2 * ((2 : ℝ) ^ k) * ((2 : ℝ) ^ k) := by
      rw [show 1 + 2 * k = 1 + (k + k) by omega, pow_add, pow_add, pow_one]; ring
    have h2ne : (2 : ℝ) ^ k ≠ 0 := by positivity
    have hcancel : ((2 : ℝ) ^ k)⁻¹ * (2 : ℝ) ^ k = 1 := inv_mul_cancel₀ h2ne
    have hr1k : r1 ^ k = (13 + s) ^ k * ((2 : ℝ) ^ k)⁻¹ := by
      simp only [r1, div_eq_mul_inv, mul_pow, inv_pow]
    have hr2k : r2 ^ k = (13 - s) ^ k * ((2 : ℝ) ^ k)⁻¹ := by
      simp only [r2, div_eq_mul_inv, mul_pow, inv_pow]
    rw [hpow, h2k, hr1k, hr2k]
    field_simp
    ring
  rw [hbinet_eq n]
  suffices h : ∀ k : ℕ,
      (A234789 (k + 1) : ℝ) * 258 =
        -258 * (2 : ℝ) ^ (k + 1) + (2193 - 191 * s) * r2 ^ (k + 1) +
        (2193 + 191 * s) * r1 ^ (k + 1) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [eq_div_iff (by norm_num : (258 : ℝ) ≠ 0)]
    exact h k
  have hr1_sq : r1 ^ 2 = 13 * r1 - 10 := by
    have : r1 ^ 2 - (13 * r1 - 10) = (s ^ 2 - 129) / 4 := by simp only [r1]; ring
    linarith [this, hs]
  have hr2_sq : r2 ^ 2 = 13 * r2 - 10 := by
    have : r2 ^ 2 - (13 * r2 - 10) = (s ^ 2 - 129) / 4 := by simp only [r2]; ring
    linarith [this, hs]
  have hr1_cub : r1 ^ 3 = 15 * r1 ^ 2 - 36 * r1 + 20 := by
    calc r1 ^ 3 = r1 * r1 ^ 2 := by ring
      _ = r1 * (13 * r1 - 10) := by rw [hr1_sq]
      _ = 15 * r1 ^ 2 - 2 * r1 ^ 2 - 10 * r1 := by ring
      _ = 15 * r1 ^ 2 - 2 * (13 * r1 - 10) - 10 * r1 := by rw [hr1_sq]
      _ = 15 * r1 ^ 2 - 36 * r1 + 20 := by ring
  have hr2_cub : r2 ^ 3 = 15 * r2 ^ 2 - 36 * r2 + 20 := by
    calc r2 ^ 3 = r2 * r2 ^ 2 := by ring
      _ = r2 * (13 * r2 - 10) := by rw [hr2_sq]
      _ = 15 * r2 ^ 2 - 2 * r2 ^ 2 - 10 * r2 := by ring
      _ = 15 * r2 ^ 2 - 2 * (13 * r2 - 10) - 10 * r2 := by rw [hr2_sq]
      _ = 15 * r2 ^ 2 - 36 * r2 + 20 := by ring
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h1, h2, h3⟩ := A234789_small
    rcases k with _ | _ | _ | m
    · rw [show (0 : ℕ) + 1 = 1 by rfl, h1]
      have : -258 * (2 : ℝ) ^ 1 + (2193 - 191 * s) * r2 ^ 1 + (2193 + 191 * s) * r1 ^ 1 -
          (204 : ℝ) * 258 = 191 * (s ^ 2 - 129) := by
        simp only [r1, r2, pow_one]; ring
      have h0 : 191 * (s ^ 2 - 129) = 0 := by rw [hs]; ring
      norm_num at this ⊢; linarith
    · rw [show (1 : ℕ) + 1 = 2 by rfl, h2]
      rw [hr1_sq, hr2_sq]
      have : -258 * (2 : ℝ) ^ 2 + (2193 - 191 * s) * (13 * r2 - 10) +
          (2193 + 191 * s) * (13 * r1 - 10) - (2504 : ℝ) * 258 = 2483 * (s ^ 2 - 129) := by
        simp only [r1, r2]; ring
      have h0 : 2483 * (s ^ 2 - 129) = 0 := by rw [hs]; ring
      norm_num at this ⊢; linarith
    · rw [show (2 : ℕ) + 1 = 3 by rfl, h3]
      have hr1_3 : r1 ^ 3 = 159 * r1 - 130 := by
        calc r1 ^ 3 = r1 * r1 ^ 2 := by ring
          _ = r1 * (13 * r1 - 10) := by rw [hr1_sq]
          _ = 13 * r1 ^ 2 - 10 * r1 := by ring
          _ = 13 * (13 * r1 - 10) - 10 * r1 := by rw [hr1_sq]
          _ = 159 * r1 - 130 := by ring
      have hr2_3 : r2 ^ 3 = 159 * r2 - 130 := by
        calc r2 ^ 3 = r2 * r2 ^ 2 := by ring
          _ = r2 * (13 * r2 - 10) := by rw [hr2_sq]
          _ = 13 * r2 ^ 2 - 10 * r2 := by ring
          _ = 13 * (13 * r2 - 10) - 10 * r2 := by rw [hr2_sq]
          _ = 159 * r2 - 130 := by ring
      rw [hr1_3, hr2_3]
      have : -258 * (2 : ℝ) ^ 3 + (2193 - 191 * s) * (159 * r2 - 130) +
          (2193 + 191 * s) * (159 * r1 - 130) - (30536 : ℝ) * 258 = 30369 * (s ^ 2 - 129) := by
        simp only [r1, r2]; ring
      have h0 : 30369 * (s ^ 2 - 129) = 0 := by rw [hs]; ring
      norm_num at this ⊢; linarith
    · have hrec : (A234789 (m + 4) : ℝ) =
          15 * A234789 (m + 3) - 36 * A234789 (m + 2) + 20 * A234789 (m + 1) := by
        exact_mod_cast A234789_rec m
      have ih2 := ih (m + 2) (by omega)
      have ih1 := ih (m + 1) (by omega)
      have ih0 := ih m (by omega)
      have h2rec : (2 : ℝ) ^ (m + 4) =
          15 * (2 : ℝ) ^ (m + 3) - 36 * (2 : ℝ) ^ (m + 2) + 20 * (2 : ℝ) ^ (m + 1) := by
        rw [show m + 4 = (m + 1) + 3 by omega, show m + 3 = (m + 1) + 2 by omega,
          show m + 2 = (m + 1) + 1 by omega, pow_add, pow_add, pow_add]
        ring
      have hpow1 : r1 ^ (m + 4) = 15 * r1 ^ (m + 3) - 36 * r1 ^ (m + 2) + 20 * r1 ^ (m + 1) := by
        calc r1 ^ (m + 4) = r1 ^ 3 * r1 ^ (m + 1) := by ring
          _ = (15 * r1 ^ 2 - 36 * r1 + 20) * r1 ^ (m + 1) := by rw [hr1_cub]
          _ = 15 * r1 ^ (m + 3) - 36 * r1 ^ (m + 2) + 20 * r1 ^ (m + 1) := by ring
      have hpow2 : r2 ^ (m + 4) = 15 * r2 ^ (m + 3) - 36 * r2 ^ (m + 2) + 20 * r2 ^ (m + 1) := by
        calc r2 ^ (m + 4) = r2 ^ 3 * r2 ^ (m + 1) := by ring
          _ = (15 * r2 ^ 2 - 36 * r2 + 20) * r2 ^ (m + 1) := by rw [hr2_cub]
          _ = 15 * r2 ^ (m + 3) - 36 * r2 ^ (m + 2) + 20 * r2 ^ (m + 1) := by ring
      rw [show m + 3 + 1 = m + 4 by omega, hrec, h2rec, hpow1, hpow2]
      rw [show m + 2 + 1 = m + 3 by omega] at ih2
      rw [show m + 1 + 1 = m + 2 by omega] at ih1
      linarith

end OMA.P_oeis_a234789

theorem OMA.solution : type_of% @OMA.S_oeis_a234789.main :=
  ⟨OMA.P_oeis_a234789.A234789_gf, OMA.P_oeis_a234789.A234789_binet⟩
