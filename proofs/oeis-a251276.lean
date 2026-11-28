import OMAStatements.S_oeis_a251276
import Mathlib.Tactic

namespace OMA.P_oeis_a251276

open OMA.S_oeis_a251276

private def adj (r1 r2 : Fin 4 × Fin 4) : Bool :=
  decide (validBlock r1.1 r1.2 r2.1 r2.2)

private def stepVec (v : Fin 4 × Fin 4 → ℤ) (r2 : Fin 4 × Fin 4) : ℤ :=
  ∑ r1 : Fin 4 × Fin 4, if adj r1 r2 then v r1 else 0

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

private lemma A251276_eq_sum_rowCount (n : ℕ) :
    (A251276 n : ℤ) = ∑ r : Fin 4 × Fin 4, rowCount n r := by
  unfold A251276 rowCount
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

private def tab1 : Fin 4 × Fin 4 → ℤ := fun r =>
  match r.1.1, r.2.1 with
  | 0, _ => 16
  | 1, 0 => 13 | 1, _ => 16
  | 2, 0 => 11 | 2, 1 => 12 | 2, _ => 16
  | 3, 0 => 10 | 3, 1 => 11 | 3, 2 => 13 | _, _ => 16

private lemma rowCount_1_eq : rowCount 1 = tab1 := by
  funext r
  rw [rowCount_succ_fun, rowCount_zero_fun]
  revert r; decide

private lemma rowCount_rec_base :
    rowCount 2 = fun r => 16 * rowCount 1 r - 26 * rowCount 0 r := by
  funext r
  rw [rowCount_succ_fun 1, rowCount_1_eq, rowCount_zero_fun]
  revert r; decide

private lemma rowCount_rec (m : ℕ) :
    rowCount (m + 2) = fun r => 16 * rowCount (m + 1) r - 26 * rowCount m r := by
  induction m with
  | zero => exact rowCount_rec_base
  | succ m ih =>
    funext r
    conv_lhs =>
      rw [rowCount_succ (m + 2) r, ih, stepVec_sub, stepVec_smul, stepVec_smul,
        ← rowCount_succ (m + 1) r, ← rowCount_succ m r]

private lemma A251276_rec (m : ℕ) :
    (A251276 (m + 3) : ℤ) = 16 * A251276 (m + 2) - 26 * A251276 (m + 1) := by
  simp only [A251276_eq_sum_rowCount]
  rw [show m + 3 = (m + 1) + 2 by omega, show m + 2 = (m + 1) + 1 by omega,
    rowCount_rec (m + 1), Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private lemma A251276_small : A251276 1 = 230 ∧ A251276 2 = 3264 := by
  have h1 : (A251276 1 : ℤ) = 230 := by
    rw [A251276_eq_sum_rowCount, rowCount_1_eq]; decide
  have h2 : (A251276 2 : ℤ) = 3264 := by
    rw [A251276_eq_sum_rowCount, rowCount_succ_fun 1, rowCount_1_eq]; decide
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

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

private lemma A251276_gf :
    (1 - 16 * PowerSeries.X + 26 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A251276 n : ℤ)) =
      2 * PowerSeries.X * (115 - 208 * PowerSeries.X) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A251276 n : ℤ))
  have hlhs : (1 - 16 * PowerSeries.X + 26 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.C 16 * (PowerSeries.X ^ 1 * F) +
        PowerSeries.C 26 * (PowerSeries.X ^ 2 * F) := by
    have h16 : PowerSeries.C (16 : ℤ) = (16 : PowerSeries ℤ) := rfl
    have h26 : PowerSeries.C (26 : ℤ) = (26 : PowerSeries ℤ) := rfl
    rw [h16, h26, pow_one]; ring
  have hrhs : 2 * (PowerSeries.X : PowerSeries ℤ) * (115 - 208 * PowerSeries.X) =
      PowerSeries.C 230 * PowerSeries.X - PowerSeries.C 416 * PowerSeries.X ^ 2 := by
    have h230 : PowerSeries.C (230 : ℤ) = (230 : PowerSeries ℤ) := rfl
    have h416 : PowerSeries.C (416 : ℤ) = (416 : PowerSeries ℤ) := rfl
    rw [h230, h416]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2⟩ := A251276_small
  by_cases hn2 : n ≤ 2
  · interval_cases n <;> simp [F, h1, h2]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, ↓reduceIte, mul_zero, sub_zero]
    have hrec := A251276_rec (n - 3)
    simp only [show n - 3 + 3 = n by omega, show n - 3 + 2 = n - 1 by omega,
      show n - 3 + 1 = n - 2 by omega] at hrec
    linarith

private lemma A251276_binet (n : ℕ) (hn : 1 ≤ n) :
    (A251276 n : ℝ) =
      ((8 - Real.sqrt 38) ^ n * (-51 + 8 * Real.sqrt 38) +
       (8 + Real.sqrt 38) ^ n * (51 + 8 * Real.sqrt 38)) / Real.sqrt 38 := by
  have hs_pos : (0 : ℝ) < Real.sqrt 38 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt 38 ^ 2 = 38 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 38
  set r1 : ℝ := 8 + s
  set r2 : ℝ := 8 - s
  suffices h : ∀ k : ℕ,
      (A251276 (k + 1) : ℝ) * s =
        r2 ^ (k + 1) * (-51 + 8 * s) + r1 ^ (k + 1) * (51 + 8 * s) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [eq_div_iff (ne_of_gt hs_pos)]
    exact h k
  have hr1_sq : r1 ^ 2 = 16 * r1 - 26 := by
    have : r1 ^ 2 - (16 * r1 - 26) = s ^ 2 - 38 := by simp only [r1]; ring
    linarith [this, hs]
  have hr2_sq : r2 ^ 2 = 16 * r2 - 26 := by
    have : r2 ^ 2 - (16 * r2 - 26) = s ^ 2 - 38 := by simp only [r2]; ring
    linarith [this, hs]
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h1, h2⟩ := A251276_small
    rcases k with _ | _ | m
    · rw [show (0 : ℕ) + 1 = 1 by rfl, h1]
      have : r2 ^ 1 * (-51 + 8 * s) + r1 ^ 1 * (51 + 8 * s) - (230 : ℝ) * s = 0 := by
        simp only [r1, r2, pow_one]; ring
      norm_num; linarith
    · rw [show (1 : ℕ) + 1 = 2 by rfl, h2]
      have : r2 ^ 2 * (-51 + 8 * s) + r1 ^ 2 * (51 + 8 * s) - (3264 : ℝ) * s =
          16 * (s ^ 2 - 38) * s := by
        simp only [r1, r2]; ring
      norm_num
      have h0 : 16 * (s ^ 2 - 38) * s = 0 := by rw [hs]; ring
      linarith
    · have hrec : (A251276 (m + 3) : ℝ) = 16 * A251276 (m + 2) - 26 * A251276 (m + 1) := by
        exact_mod_cast A251276_rec m
      have ih1 := ih (m + 1) (by omega)
      have ih0 := ih m (by omega)
      have hpow1 : r1 ^ (m + 3) = 16 * r1 ^ (m + 2) - 26 * r1 ^ (m + 1) := by
        calc r1 ^ (m + 3) = r1 ^ 2 * r1 ^ (m + 1) := by ring
          _ = (16 * r1 - 26) * r1 ^ (m + 1) := by rw [hr1_sq]
          _ = 16 * r1 ^ (m + 2) - 26 * r1 ^ (m + 1) := by ring
      have hpow2 : r2 ^ (m + 3) = 16 * r2 ^ (m + 2) - 26 * r2 ^ (m + 1) := by
        calc r2 ^ (m + 3) = r2 ^ 2 * r2 ^ (m + 1) := by ring
          _ = (16 * r2 - 26) * r2 ^ (m + 1) := by rw [hr2_sq]
          _ = 16 * r2 ^ (m + 2) - 26 * r2 ^ (m + 1) := by ring
      rw [show m + 2 + 1 = m + 3 by omega, hrec, hpow1, hpow2]
      rw [show m + 1 + 1 = m + 2 by omega] at ih1
      linarith

end OMA.P_oeis_a251276

theorem OMA.solution : type_of% @OMA.S_oeis_a251276.main :=
  ⟨OMA.P_oeis_a251276.A251276_gf, OMA.P_oeis_a251276.A251276_binet⟩
