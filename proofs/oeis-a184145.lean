import OMAStatements.S_oeis_a184145
import Mathlib.Tactic

namespace OMA.P_oeis_a184145

open OMA.S_oeis_a184145

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

private def rawCount (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 2 → Fin 4 => isValidArr n A)).card

private lemma A184145_eq_rawCount_div (n : ℕ) : A184145 n = rawCount n / 4 := rfl

private def rowCount (n : ℕ) (r : Fin 4 × Fin 4) : ℤ :=
  ∑ A : Fin (n + 1) × Fin 2 → Fin 4,
    if isValidArr n A ∧ (A (⟨n, Nat.lt_succ_self n⟩, 0), A (⟨n, Nat.lt_succ_self n⟩, 1)) = r
    then 1 else 0

private lemma rawCount_eq_sum_rowCount (n : ℕ) :
    (rawCount n : ℤ) = ∑ r : Fin 4 × Fin 4, rowCount n r := by
  unfold rawCount rowCount
  rw [Finset.sum_comm]
  have hcard : ∀ S : Finset (Fin (n + 1) × Fin 2 → Fin 4),
      (S.card : ℤ) = ∑ A : Fin (n + 1) × Fin 2 → Fin 4, if A ∈ S then (1 : ℤ) else 0 := by
    intro S; simp
  rw [hcard]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hA : isValidArr n A
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

private def tab1 : Fin 4 × Fin 4 → ℤ := fun r => if r.1 = r.2 then 16 else 9

private lemma rowCount_1_eq : rowCount 1 = tab1 := by
  funext r
  rw [rowCount_succ_fun, rowCount_zero_fun]
  revert r; decide

private lemma rowCount_rec_base :
    rowCount 2 = fun r => 9 * rowCount 1 r + 28 * rowCount 0 r := by
  funext r
  rw [rowCount_succ_fun 1, rowCount_1_eq, rowCount_zero_fun]
  revert r; decide

private lemma rowCount_rec (m : ℕ) :
    rowCount (m + 2) = fun r => 9 * rowCount (m + 1) r + 28 * rowCount m r := by
  induction m with
  | zero => exact rowCount_rec_base
  | succ m ih =>
    funext r
    conv_lhs =>
      rw [rowCount_succ (m + 2) r, ih, stepVec_add, stepVec_smul, stepVec_smul,
        ← rowCount_succ (m + 1) r, ← rowCount_succ m r]

private lemma rawCount_rec (m : ℕ) :
    (rawCount (m + 2) : ℤ) = 9 * rawCount (m + 1) + 28 * rawCount m := by
  simp only [rawCount_eq_sum_rowCount]
  rw [rowCount_rec m, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private lemma rawCount_small : rawCount 1 = 172 ∧ rawCount 2 = 1996 := by
  have h1 : (rawCount 1 : ℤ) = 172 := by
    rw [rawCount_eq_sum_rowCount, rowCount_1_eq]; decide
  have h2 : (rawCount 2 : ℤ) = 1996 := by
    rw [rawCount_eq_sum_rowCount, rowCount_succ_fun 1, rowCount_1_eq]; decide
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

private lemma four_dvd_rawCount (n : ℕ) (hn : 1 ≤ n) : 4 ∣ rawCount n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  clear hn
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h1, h2⟩ := rawCount_small
    rcases k with _ | _ | m
    · rw [h1]; exact ⟨43, rfl⟩
    · rw [h2]; exact ⟨499, rfl⟩
    · have hrec := rawCount_rec (m + 1)
      have hm1 := ih (m + 1) (by omega)
      have hm0 := ih m (by omega)
      obtain ⟨a, ha⟩ := hm1
      obtain ⟨b, hb⟩ := hm0
      refine ⟨9 * a + 28 * b, ?_⟩
      have hrec' : rawCount (m + 3) = 9 * rawCount (m + 2) + 28 * rawCount (m + 1) := by
        exact_mod_cast hrec
      rw [show m + 1 + 1 + 1 = m + 3 by omega, hrec']
      rw [show m + 1 + 1 = m + 2 by omega] at ha
      omega

private lemma four_mul_A184145 (n : ℕ) (hn : 1 ≤ n) :
    4 * (A184145 n : ℤ) = (rawCount n : ℤ) := by
  have hd := four_dvd_rawCount n hn
  have hnat : 4 * A184145 n = rawCount n := by
    rw [A184145_eq_rawCount_div, Nat.mul_div_cancel' hd]
  exact_mod_cast hnat

private lemma A184145_rec (m : ℕ) :
    (A184145 (m + 3) : ℤ) = 9 * A184145 (m + 2) + 28 * A184145 (m + 1) := by
  have h3 := four_mul_A184145 (m + 3) (by omega)
  have h2 := four_mul_A184145 (m + 2) (by omega)
  have h1 := four_mul_A184145 (m + 1) (by omega)
  have hrec := rawCount_rec (m + 1)
  linarith

private lemma A184145_small : A184145 1 = 43 ∧ A184145 2 = 499 := by
  obtain ⟨h1, h2⟩ := rawCount_small
  simp [A184145_eq_rawCount_div, h1, h2]

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

private lemma A184145_gf :
    (1 - 9 * PowerSeries.X - 28 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A184145 n : ℤ)) =
      PowerSeries.X * (43 + 112 * PowerSeries.X) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A184145 n : ℤ))
  have hlhs : (1 - 9 * PowerSeries.X - 28 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.C 9 * (PowerSeries.X ^ 1 * F) -
        PowerSeries.C 28 * (PowerSeries.X ^ 2 * F) := by
    have h9 : PowerSeries.C (9 : ℤ) = (9 : PowerSeries ℤ) := rfl
    have h28 : PowerSeries.C (28 : ℤ) = (28 : PowerSeries ℤ) := rfl
    rw [h9, h28, pow_one]; ring
  have hrhs : (PowerSeries.X : PowerSeries ℤ) * (43 + 112 * PowerSeries.X) =
      PowerSeries.C 43 * PowerSeries.X + PowerSeries.C 112 * PowerSeries.X ^ 2 := by
    have h43 : PowerSeries.C (43 : ℤ) = (43 : PowerSeries ℤ) := rfl
    have h112 : PowerSeries.C (112 : ℤ) = (112 : PowerSeries ℤ) := rfl
    rw [h43, h112]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2⟩ := A184145_small
  by_cases hn2 : n ≤ 2
  · interval_cases n <;> simp [F, h1, h2]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, ↓reduceIte, mul_zero, add_zero]
    have hrec := A184145_rec (n - 3)
    simp only [show n - 3 + 3 = n by omega, show n - 3 + 2 = n - 1 by omega,
      show n - 3 + 1 = n - 2 by omega] at hrec
    linarith

private lemma A184145_binet (n : ℕ) (hn : 1 ≤ n) :
    (A184145 n : ℝ) =
      ((2 : ℝ) ^ (-(n : ℤ)) *
        ((9 - Real.sqrt 193) ^ n * (-25 + 2 * Real.sqrt 193) +
         (9 + Real.sqrt 193) ^ n * (25 + 2 * Real.sqrt 193))) / Real.sqrt 193 := by
  have hs_pos : (0 : ℝ) < Real.sqrt 193 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt 193 ^ 2 = 193 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 193
  set r1 : ℝ := (9 + s) / 2
  set r2 : ℝ := (9 - s) / 2
  have hbinet_eq : ∀ k : ℕ,
      ((2 : ℝ) ^ (-(k : ℤ)) *
        ((9 - s) ^ k * (-25 + 2 * s) + (9 + s) ^ k * (25 + 2 * s))) / s =
      ((-25 + 2 * s) * r2 ^ k + (25 + 2 * s) * r1 ^ k) / s := by
    intro k
    have hpow : (2 : ℝ) ^ (-(k : ℤ)) = ((2 : ℝ) ^ k)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    have hr1k : r1 ^ k = (9 + s) ^ k * ((2 : ℝ) ^ k)⁻¹ := by
      simp only [r1, div_eq_mul_inv, mul_pow, inv_pow]
    have hr2k : r2 ^ k = (9 - s) ^ k * ((2 : ℝ) ^ k)⁻¹ := by
      simp only [r2, div_eq_mul_inv, mul_pow, inv_pow]
    rw [hpow, hr1k, hr2k]; ring
  rw [hbinet_eq n]
  suffices h : ∀ k : ℕ,
      (A184145 (k + 1) : ℝ) * s =
        (-25 + 2 * s) * r2 ^ (k + 1) + (25 + 2 * s) * r1 ^ (k + 1) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [eq_div_iff (ne_of_gt hs_pos)]
    exact h k
  have hr1_sq : r1 ^ 2 = 9 * r1 + 28 := by
    have : r1 ^ 2 - (9 * r1 + 28) = (s ^ 2 - 193) / 4 := by simp only [r1]; ring
    linarith [this, hs]
  have hr2_sq : r2 ^ 2 = 9 * r2 + 28 := by
    have : r2 ^ 2 - (9 * r2 + 28) = (s ^ 2 - 193) / 4 := by simp only [r2]; ring
    linarith [this, hs]
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h1, h2⟩ := A184145_small
    rcases k with _ | _ | m
    · rw [show (0 : ℕ) + 1 = 1 by rfl, h1]
      have : (-25 + 2 * s) * r2 ^ 1 + (25 + 2 * s) * r1 ^ 1 - (43 : ℝ) * s = 0 := by
        simp only [r1, r2, pow_one]; ring
      norm_num; linarith
    · rw [show (1 : ℕ) + 1 = 2 by rfl, h2]
      have : (-25 + 2 * s) * r2 ^ 2 + (25 + 2 * s) * r1 ^ 2 - (499 : ℝ) * s =
          (s ^ 2 - 193) * s := by
        simp only [r1, r2]; ring
      norm_num
      have h0 : (s ^ 2 - 193) * s = 0 := by rw [hs]; ring
      linarith
    · have hrec : (A184145 (m + 3) : ℝ) = 9 * A184145 (m + 2) + 28 * A184145 (m + 1) := by
        exact_mod_cast A184145_rec m
      have ih1 := ih (m + 1) (by omega)
      have ih0 := ih m (by omega)
      have hpow1 : r1 ^ (m + 3) = 9 * r1 ^ (m + 2) + 28 * r1 ^ (m + 1) := by
        calc r1 ^ (m + 3) = r1 ^ 2 * r1 ^ (m + 1) := by ring
          _ = (9 * r1 + 28) * r1 ^ (m + 1) := by rw [hr1_sq]
          _ = 9 * r1 ^ (m + 2) + 28 * r1 ^ (m + 1) := by ring
      have hpow2 : r2 ^ (m + 3) = 9 * r2 ^ (m + 2) + 28 * r2 ^ (m + 1) := by
        calc r2 ^ (m + 3) = r2 ^ 2 * r2 ^ (m + 1) := by ring
          _ = (9 * r2 + 28) * r2 ^ (m + 1) := by rw [hr2_sq]
          _ = 9 * r2 ^ (m + 2) + 28 * r2 ^ (m + 1) := by ring
      rw [show m + 2 + 1 = m + 3 by omega, hrec, hpow1, hpow2]
      rw [show m + 1 + 1 = m + 2 by omega] at ih1
      linarith

end OMA.P_oeis_a184145

theorem OMA.solution : type_of% @OMA.S_oeis_a184145.main :=
  ⟨OMA.P_oeis_a184145.A184145_gf, OMA.P_oeis_a184145.A184145_binet⟩
