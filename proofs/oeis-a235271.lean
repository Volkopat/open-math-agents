import OMAStatements.S_oeis_a235271
import Mathlib.Tactic

namespace OMA.P_oeis_a235271

open OMA.S_oeis_a235271

private def adj (r1 r2 : Fin 5 × Fin 5) : Bool :=
  decide (validBlock r1.1 r1.2 r2.1 r2.2)

private def stepVec (v : Fin 5 × Fin 5 → ℤ) (r2 : Fin 5 × Fin 5) : ℤ :=
  ∑ r1 : Fin 5 × Fin 5, if adj r1 r2 then v r1 else 0

private lemma stepVec_sub (u v : Fin 5 × Fin 5 → ℤ) (r : Fin 5 × Fin 5) :
    stepVec (fun x => u x - v x) r = stepVec u r - stepVec v r := by
  unfold stepVec
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private lemma stepVec_smul (c : ℤ) (v : Fin 5 × Fin 5 → ℤ) (r : Fin 5 × Fin 5) :
    stepVec (fun x => c * v x) r = c * stepVec v r := by
  unfold stepVec
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private def isValidArr (n : ℕ) (A : Fin (n + 1) × Fin 2 → Fin 5) : Prop :=
  ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
    (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1))

private instance (n : ℕ) (A : Fin (n + 1) × Fin 2 → Fin 5) : Decidable (isValidArr n A) := by
  unfold isValidArr; infer_instance

private def rowCount (n : ℕ) (r : Fin 5 × Fin 5) : ℤ :=
  ∑ A : Fin (n + 1) × Fin 2 → Fin 5,
    if isValidArr n A ∧ (A (⟨n, Nat.lt_succ_self n⟩, 0), A (⟨n, Nat.lt_succ_self n⟩, 1)) = r
    then 1 else 0

private lemma A235271_eq_sum_rowCount (n : ℕ) :
    (A235271 n : ℤ) = ∑ r : Fin 5 × Fin 5, rowCount n r := by
  unfold A235271 rowCount
  rw [Finset.sum_comm]
  have hcard : ∀ S : Finset (Fin (n + 1) × Fin 2 → Fin 5),
      (S.card : ℤ) = ∑ A : Fin (n + 1) × Fin 2 → Fin 5, if A ∈ S then (1 : ℤ) else 0 := by
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

private lemma rowCount_zero (r : Fin 5 × Fin 5) : rowCount 0 r = 1 := by
  unfold rowCount isValidArr
  let A0 : Fin 1 × Fin 2 → Fin 5 := fun p => if p.2 = 0 then r.1 else r.2
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

private lemma rowCount_succ (n : ℕ) (r : Fin 5 × Fin 5) :
    rowCount (n + 1) r = stepVec (rowCount n) r := by
  let e : (Fin (n + 2) × Fin 2 → Fin 5) ≃ ((Fin (n + 1) × Fin 2 → Fin 5) × (Fin 5 × Fin 5)) :=
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
  have hiff : ∀ A : Fin (n + 2) × Fin 2 → Fin 5,
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
  have hr_sum : ∀ A' : Fin (n + 1) × Fin 2 → Fin 5,
      (∑ r' : Fin 5 × Fin 5,
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
  trans ∑ r1 : Fin 5 × Fin 5, ∑ A' : Fin (n + 1) × Fin 2 → Fin 5,
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

private def rdiff (r : Fin 5 × Fin 5) : ℕ :=
  if r.1.1 ≤ r.2.1 then r.2.1 - r.1.1 else r.1.1 - r.2.1

private def tab1 (r : Fin 5 × Fin 5) : ℤ := (rdiff r : ℤ)

private def tab2 (r : Fin 5 × Fin 5) : ℤ :=
  match rdiff r with | 0 => 0 | 1 => 4 | 2 => 6 | 3 => 6 | _ => 4

private def tab3 (r : Fin 5 × Fin 5) : ℤ :=
  match rdiff r with | 0 => 0 | 1 => 4 | 2 => 12 | 3 => 18 | _ => 16

private def tab4 (r : Fin 5 × Fin 5) : ℤ :=
  match rdiff r with | 0 => 0 | 1 => 16 | 2 => 36 | 3 => 36 | _ => 16

private lemma rowCount_1_eq : rowCount 1 = tab1 := by
  funext r; rw [rowCount_succ_fun, rowCount_zero_fun]; revert r; decide

private lemma rowCount_2_eq : rowCount 2 = tab2 := by
  funext r; rw [rowCount_succ_fun, rowCount_1_eq]; revert r; decide

private lemma rowCount_3_eq : rowCount 3 = tab3 := by
  funext r; rw [rowCount_succ_fun, rowCount_2_eq]; revert r; decide

private lemma rowCount_4_eq : rowCount 4 = tab4 := by
  funext r; rw [rowCount_succ_fun, rowCount_3_eq]; revert r; decide

private lemma rowCount_rec_base :
    rowCount 5 = fun r => 10 * rowCount 3 r - 24 * rowCount 1 r := by
  funext r
  rw [rowCount_succ_fun 4, rowCount_4_eq, rowCount_3_eq, rowCount_1_eq]
  revert r; decide

private lemma rowCount_rec (m : ℕ) :
    rowCount (m + 5) = fun r => 10 * rowCount (m + 3) r - 24 * rowCount (m + 1) r := by
  induction m with
  | zero => exact rowCount_rec_base
  | succ m ih =>
    funext r
    conv_lhs =>
      rw [rowCount_succ (m + 5) r, ih, stepVec_sub, stepVec_smul, stepVec_smul,
        ← rowCount_succ (m + 3) r, ← rowCount_succ (m + 1) r]

private lemma A235271_rec (m : ℕ) :
    (A235271 (m + 5) : ℤ) = 10 * A235271 (m + 3) - 24 * A235271 (m + 1) := by
  simp only [A235271_eq_sum_rowCount]
  rw [rowCount_rec m, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

private lemma A235271_small :
    A235271 1 = 40 ∧ A235271 2 = 100 ∧ A235271 3 = 208 ∧ A235271 4 = 520 := by
  have h1 : (A235271 1 : ℤ) = 40 := by rw [A235271_eq_sum_rowCount, rowCount_1_eq]; decide
  have h2 : (A235271 2 : ℤ) = 100 := by rw [A235271_eq_sum_rowCount, rowCount_2_eq]; decide
  have h3 : (A235271 3 : ℤ) = 208 := by rw [A235271_eq_sum_rowCount, rowCount_3_eq]; decide
  have h4 : (A235271 4 : ℤ) = 520 := by rw [A235271_eq_sum_rowCount, rowCount_4_eq]; decide
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3, by exact_mod_cast h4⟩

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

private lemma A235271_gf :
    (1 - 2 * PowerSeries.X) * (1 + 2 * PowerSeries.X) * (1 - 6 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235271 n : ℤ)) =
      4 * PowerSeries.X * (2 + 5 * PowerSeries.X) * (5 - 24 * PowerSeries.X ^ 2) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A235271 n : ℤ))
  have hlhs : (1 - 2 * PowerSeries.X) * (1 + 2 * PowerSeries.X) * (1 - 6 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.C 10 * (PowerSeries.X ^ 2 * F) + PowerSeries.C 24 * (PowerSeries.X ^ 4 * F) := by
    have h10 : PowerSeries.C (10 : ℤ) = (10 : PowerSeries ℤ) := rfl
    have h24 : PowerSeries.C (24 : ℤ) = (24 : PowerSeries ℤ) := rfl
    rw [h10, h24]; ring
  have hrhs : 4 * (PowerSeries.X : PowerSeries ℤ) * (2 + 5 * PowerSeries.X) *
        (5 - 24 * PowerSeries.X ^ 2) =
      PowerSeries.C 40 * PowerSeries.X + PowerSeries.C 100 * PowerSeries.X ^ 2 -
      PowerSeries.C 192 * PowerSeries.X ^ 3 - PowerSeries.C 480 * PowerSeries.X ^ 4 := by
    have h40 : PowerSeries.C (40 : ℤ) = (40 : PowerSeries ℤ) := rfl
    have h100 : PowerSeries.C (100 : ℤ) = (100 : PowerSeries ℤ) := rfl
    have h192 : PowerSeries.C (192 : ℤ) = (192 : PowerSeries ℤ) := rfl
    have h480 : PowerSeries.C (480 : ℤ) = (480 : PowerSeries ℤ) := rfl
    rw [h40, h100, h192, h480]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2, h3, h4⟩ := A235271_small
  by_cases hn4 : n ≤ 4
  · interval_cases n <;> simp [F, h1, h2, h3, h4]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show 2 ≤ n by omega,
      show 4 ≤ n by omega, show n - 2 ≠ 0 by omega, show n - 4 ≠ 0 by omega,
      ↓reduceIte, mul_zero, sub_zero, add_zero]
    have hrec := A235271_rec (n - 5)
    simp only [show n - 5 + 5 = n by omega, show n - 5 + 3 = n - 2 by omega,
      show n - 5 + 1 = n - 4 by omega] at hrec
    linarith

private lemma A235271_closed_int (n : ℕ) (hn : 1 ≤ n) :
    (A235271 n : ℤ) =
      if Even n then 10 * (4 : ℤ) ^ (n / 2) + 10 * (6 : ℤ) ^ (n / 2)
      else 16 * (4 : ℤ) ^ ((n - 1) / 2) + 24 * (6 : ℤ) ^ ((n - 1) / 2) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  clear hn
  rw [Nat.add_sub_cancel]
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := A235271_small
    rcases k with _ | _ | _ | _ | m
    · simp [h1]
    · simp [h2]
    · have ho3 : ¬ Even 3 := by decide
      simp [h3, ho3]
    · have he4 : Even 4 := by decide
      simp [h4, he4]
    · have hrec := A235271_rec m
      have ih2 := ih (m + 2) (by omega)
      have ih0 := ih m (by omega)
      rw [show m + 4 + 1 = m + 5 by omega, hrec]
      by_cases hev : Even (m + 5)
      · have h3e : Even (m + 3) := by rw [Nat.even_iff] at hev ⊢; omega
        have h1e : Even (m + 1) := by rw [Nat.even_iff] at hev ⊢; omega
        rw [if_pos hev]
        rw [show m + 2 + 1 = m + 3 by omega, if_pos h3e] at ih2
        rw [if_pos h1e] at ih0
        have h4_5 : (4 : ℤ) ^ ((m + 5) / 2) = 16 * (4 : ℤ) ^ ((m + 1) / 2) := by
          rw [show (m + 5) / 2 = (m + 1) / 2 + 2 by omega, pow_add]; ring
        have h4_3 : (4 : ℤ) ^ ((m + 3) / 2) = 4 * (4 : ℤ) ^ ((m + 1) / 2) := by
          rw [show (m + 3) / 2 = (m + 1) / 2 + 1 by omega, pow_succ]; ring
        have h6_5 : (6 : ℤ) ^ ((m + 5) / 2) = 36 * (6 : ℤ) ^ ((m + 1) / 2) := by
          rw [show (m + 5) / 2 = (m + 1) / 2 + 2 by omega, pow_add]; ring
        have h6_3 : (6 : ℤ) ^ ((m + 3) / 2) = 6 * (6 : ℤ) ^ ((m + 1) / 2) := by
          rw [show (m + 3) / 2 = (m + 1) / 2 + 1 by omega, pow_succ]; ring
        rw [h4_5, h6_5]; rw [h4_3, h6_3] at ih2
        linarith
      · have h3o : ¬ Even (m + 3) := by rw [Nat.even_iff] at hev ⊢; omega
        have h1o : ¬ Even (m + 1) := by rw [Nat.even_iff] at hev ⊢; omega
        rw [if_neg hev]
        rw [show m + 2 + 1 = m + 3 by omega, if_neg h3o] at ih2
        rw [if_neg h1o] at ih0
        have h4_4 : (4 : ℤ) ^ ((m + 4) / 2) = 16 * (4 : ℤ) ^ (m / 2) := by
          rw [show (m + 4) / 2 = m / 2 + 2 by omega, pow_add]; ring
        have h4_2 : (4 : ℤ) ^ ((m + 2) / 2) = 4 * (4 : ℤ) ^ (m / 2) := by
          rw [show (m + 2) / 2 = m / 2 + 1 by omega, pow_succ]; ring
        have h6_4 : (6 : ℤ) ^ ((m + 4) / 2) = 36 * (6 : ℤ) ^ (m / 2) := by
          rw [show (m + 4) / 2 = m / 2 + 2 by omega, pow_add]; ring
        have h6_2 : (6 : ℤ) ^ ((m + 2) / 2) = 6 * (6 : ℤ) ^ (m / 2) := by
          rw [show (m + 2) / 2 = m / 2 + 1 by omega, pow_succ]; ring
        rw [h4_4, h6_4]; rw [h4_2, h6_2] at ih2
        linarith

private lemma A235271_closed (n : ℕ) (hn : 1 ≤ n) :
    (A235271 n : ℝ) =
      (-2 : ℝ) ^ n + 9 * (2 : ℝ) ^ n +
      (6 : ℝ) ^ ((1 / 2 : ℝ) * (-1 + (n : ℝ))) *
        (12 - 12 * (-1 : ℝ) ^ n + 5 * Real.sqrt 6 + 5 * (-1 : ℝ) ^ n * Real.sqrt 6) := by
  have hint : (A235271 n : ℝ) =
      if Even n then 10 * (4 : ℝ) ^ (n / 2) + 10 * (6 : ℝ) ^ (n / 2)
      else 16 * (4 : ℝ) ^ ((n - 1) / 2) + 24 * (6 : ℝ) ^ ((n - 1) / 2) := by
    have h := A235271_closed_int n hn
    split_ifs at h ⊢ <;> exact_mod_cast h
  rw [hint]
  have hs : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hr6 : (6 : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt 6 := (Real.sqrt_eq_rpow 6).symm
  by_cases hev : Even n
  · rw [if_pos hev]
    obtain ⟨m, rfl⟩ := hev
    have hdiv : (m + m) / 2 = m := by omega
    have hm1 : (-1 : ℝ) ^ (m + m) = 1 := by rw [← two_mul, pow_mul]; norm_num
    have h2m : (-2 : ℝ) ^ (m + m) + 9 * (2 : ℝ) ^ (m + m) = 10 * (4 : ℝ) ^ m := by
      rw [← two_mul, pow_mul, pow_mul]; norm_num; ring
    have hexp : (1 / 2 : ℝ) * (-1 + ((m + m : ℕ) : ℝ)) = ((m - 1 : ℕ) : ℝ) + (1 : ℝ) / 2 := by
      have hm_pos : 1 ≤ m := by omega
      push_cast [Nat.cast_sub hm_pos]; ring
    have hrpow : (6 : ℝ) ^ ((1 / 2 : ℝ) * (-1 + ((m + m : ℕ) : ℝ))) * Real.sqrt 6 = (6 : ℝ) ^ m := by
      rw [hexp, Real.rpow_add (by norm_num : (0 : ℝ) < 6), Real.rpow_natCast, hr6, mul_assoc,
        ← sq, hs, ← pow_succ, show m - 1 + 1 = m by omega]
    rw [hdiv, h2m, hm1]
    have hfac : 12 - 12 * (1 : ℝ) + 5 * Real.sqrt 6 + 5 * (1 : ℝ) * Real.sqrt 6 =
        10 * Real.sqrt 6 := by ring
    rw [hfac, ← mul_assoc, mul_comm ((6 : ℝ) ^ _) 10, mul_assoc, hrpow]
  · rw [if_neg hev]
    obtain ⟨m, rfl⟩ := Nat.not_even_iff_odd.mp hev
    have hdiv : (2 * m + 1 - 1) / 2 = m := by omega
    have hm1 : (-1 : ℝ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    have h2m : (-2 : ℝ) ^ (2 * m + 1) + 9 * (2 : ℝ) ^ (2 * m + 1) = 16 * (4 : ℝ) ^ m := by
      rw [pow_succ, pow_succ, pow_mul, pow_mul]; norm_num; ring
    have hexp : (1 / 2 : ℝ) * (-1 + ((2 * m + 1 : ℕ) : ℝ)) = (m : ℝ) := by
      push_cast; ring
    rw [hdiv, h2m, hm1, hexp, Real.rpow_natCast]
    ring

end OMA.P_oeis_a235271

theorem OMA.solution : type_of% @OMA.S_oeis_a235271.main :=
  ⟨OMA.P_oeis_a235271.A235271_gf, OMA.P_oeis_a235271.A235271_closed⟩
