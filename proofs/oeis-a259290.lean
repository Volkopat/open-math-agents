import OMAStatements.S_oeis_a259290
import Mathlib.Tactic

namespace OMA.P_oeis_a259290

open OMA.S_oeis_a259290

private def adj (r1 r2 : Bool × Bool) : Bool :=
  decide (validBlock r1.1 r1.2 r2.2 r2.1)

private def stepVec (v : Bool × Bool → ℤ) (r2 : Bool × Bool) : ℤ :=
  ∑ r1 : Bool × Bool, if adj r1 r2 then v r1 else 0

private def isValidArr (n : ℕ) (A : Fin (n + 1) × Fin 2 → Bool) : Prop :=
  ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
    (A (⟨i.1 + 1, by omega⟩, 1)) (A (⟨i.1 + 1, by omega⟩, 0))

private instance (n : ℕ) (A : Fin (n + 1) × Fin 2 → Bool) : Decidable (isValidArr n A) := by
  unfold isValidArr; infer_instance

private def rowCount (n : ℕ) (r : Bool × Bool) : ℤ :=
  ∑ A : Fin (n + 1) × Fin 2 → Bool,
    if isValidArr n A ∧ (A (⟨n, Nat.lt_succ_self n⟩, 0), A (⟨n, Nat.lt_succ_self n⟩, 1)) = r
    then 1 else 0

private lemma A259290_eq_sum_rowCount (n : ℕ) :
    (A259290 n : ℤ) = ∑ r : Bool × Bool, rowCount n r := by
  unfold A259290 rowCount
  rw [Finset.sum_comm]
  have hcard : ∀ S : Finset (Fin (n + 1) × Fin 2 → Bool),
      (S.card : ℤ) = ∑ A : Fin (n + 1) × Fin 2 → Bool, if A ∈ S then (1 : ℤ) else 0 := by
    intro S; simp
  rw [hcard]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, isValidArr]
  by_cases hA : ∀ i : Fin n, validBlock (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1, by omega⟩, 1))
      (A (⟨i.1 + 1, by omega⟩, 1)) (A (⟨i.1 + 1, by omega⟩, 0))
  · rw [if_pos hA]
    rw [Finset.sum_eq_single (A (⟨n, Nat.lt_succ_self n⟩, 0), A (⟨n, Nat.lt_succ_self n⟩, 1))]
    · simp [hA]
    · intro r _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  · rw [if_neg hA]
    refine (Finset.sum_eq_zero fun r _ => ?_).symm
    simp [hA]

private lemma rowCount_zero (r : Bool × Bool) : rowCount 0 r = 1 := by
  unfold rowCount isValidArr
  let A0 : Fin 1 × Fin 2 → Bool := fun p => if p.2 = 0 then r.1 else r.2
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

private lemma rowCount_succ (n : ℕ) (r : Bool × Bool) :
    rowCount (n + 1) r = stepVec (rowCount n) r := by
  let e : (Fin (n + 2) × Fin 2 → Bool) ≃ ((Fin (n + 1) × Fin 2 → Bool) × (Bool × Bool)) :=
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
  have hiff : ∀ A : Fin (n + 2) × Fin 2 → Bool,
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
  have hr_sum : ∀ A' : Fin (n + 1) × Fin 2 → Bool,
      (∑ r' : Bool × Bool,
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
  trans ∑ r1 : Bool × Bool, ∑ A' : Fin (n + 1) × Fin 2 → Bool,
      if isValidArr n A' ∧
         (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1)) = r1 ∧
         adj r1 r = true then (1 : ℤ) else 0
  · refine Finset.sum_congr rfl fun r1 _ => ?_
    by_cases hadj : adj r1 r = true
    · simp [hadj]
    · simp [hadj]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A' _ => ?_
    rw [Finset.sum_eq_single (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1))]
    · simp
    · intro r1 _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private lemma stepVec_symm (v : Bool × Bool → ℤ) (hsym : v (false, true) = v (true, false)) :
    stepVec v (false, true) = stepVec v (true, false) := by
  unfold stepVec adj
  simp [Fintype.sum_prod_type, validBlock, hsym]; ring

private lemma rowCount_symm (n : ℕ) :
    rowCount n (false, true) = rowCount n (true, false) := by
  induction n with
  | zero => rw [rowCount_zero, rowCount_zero]
  | succ m ih => rw [rowCount_succ, rowCount_succ]; exact stepVec_symm (rowCount m) ih

private lemma stepVec_rec (v : Bool × Bool → ℤ) (hsym : v (false, true) = v (true, false))
    (r : Bool × Bool) :
    stepVec (stepVec (stepVec v)) r =
      stepVec (stepVec v) r + 4 * stepVec v r := by
  unfold stepVec adj
  rcases r with ⟨a, b⟩
  cases a <;> cases b <;> simp [Fintype.sum_prod_type, validBlock, hsym] <;> ring

private lemma rowCount_succ_fun (n : ℕ) : rowCount (n + 1) = stepVec (rowCount n) :=
  funext (rowCount_succ n)

private lemma rowCount_zero_fun : rowCount 0 = fun _ => 1 :=
  funext rowCount_zero

private lemma rowCount_rec (n : ℕ) (r : Bool × Bool) :
    rowCount (n + 3) r = rowCount (n + 2) r + 4 * rowCount (n + 1) r := by
  rw [rowCount_succ_fun (n + 2), rowCount_succ_fun (n + 1), rowCount_succ_fun n]
  exact stepVec_rec (rowCount n) (rowCount_symm n) r

private lemma A259290_rec (n : ℕ) :
    (A259290 (n + 3) : ℤ) = A259290 (n + 2) + 4 * A259290 (n + 1) := by
  simp only [A259290_eq_sum_rowCount, rowCount_rec, Finset.sum_add_distrib, ← Finset.mul_sum]

private lemma A259290_small : A259290 1 = 10 ∧ A259290 2 = 26 := by
  have h1 : (A259290 1 : ℤ) = 10 := by
    rw [A259290_eq_sum_rowCount, rowCount_succ_fun 0, rowCount_zero_fun]; decide
  have h2 : (A259290 2 : ℤ) = 26 := by
    rw [A259290_eq_sum_rowCount, rowCount_succ_fun 1, rowCount_succ_fun 0, rowCount_zero_fun]; decide
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

private lemma A259290_gf :
    (1 - PowerSeries.X - 4 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A259290 n : ℤ)) =
      2 * PowerSeries.X * (5 + 8 * PowerSeries.X) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A259290 n : ℤ))
  have hlhs : (1 - PowerSeries.X - 4 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.X ^ 1 * F - PowerSeries.C 4 * (PowerSeries.X ^ 2 * F) := by
    have h4 : PowerSeries.C (4 : ℤ) = (4 : PowerSeries ℤ) := rfl
    rw [h4, pow_one]; ring
  have hrhs : 2 * (PowerSeries.X : PowerSeries ℤ) * (5 + 8 * PowerSeries.X) =
      PowerSeries.C 10 * PowerSeries.X + PowerSeries.C 16 * PowerSeries.X ^ 2 := by
    have h10 : PowerSeries.C (10 : ℤ) = (10 : PowerSeries ℤ) := rfl
    have h16 : PowerSeries.C (16 : ℤ) = (16 : PowerSeries ℤ) := rfl
    rw [h10, h16]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2⟩ := A259290_small
  by_cases hn2 : n ≤ 2
  · interval_cases n <;> simp [F, h1, h2]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, ↓reduceIte, mul_zero, add_zero]
    have hrec := A259290_rec (n - 3)
    simp only [show n - 3 + 3 = n by omega, show n - 3 + 2 = n - 1 by omega,
      show n - 3 + 1 = n - 2 by omega] at hrec
    linarith

private lemma A259290_binet (n : ℕ) (hn : 1 ≤ n) :
    (A259290 n : ℝ) =
      ((2 : ℝ) ^ (1 - (n : ℤ)) *
        ((1 - Real.sqrt 17) ^ n * (-4 + Real.sqrt 17) +
         (1 + Real.sqrt 17) ^ n * (4 + Real.sqrt 17))) / Real.sqrt 17 := by
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  have hsne : Real.sqrt 17 ≠ 0 := by positivity
  suffices h : ∀ k : ℕ,
      (A259290 (k + 1) : ℝ) * Real.sqrt 17 =
        (2 : ℝ) ^ (1 - ((k + 1 : ℕ) : ℤ)) *
          ((1 - Real.sqrt 17) ^ (k + 1) * (-4 + Real.sqrt 17) +
           (1 + Real.sqrt 17) ^ (k + 1) * (4 + Real.sqrt 17)) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    exact (eq_div_iff hsne).mpr (h k)
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h1, h2⟩ := A259290_small
    rcases k with _ | _ | m
    · simp only [zero_add, h1, Nat.cast_ofNat, pow_one]
      norm_num; ring
    · simp only [Nat.reduceAdd, h2, Nat.cast_ofNat]
      have hz : (2 : ℝ) ^ ((1 : ℤ) - 2) = 1 / 2 := by norm_num
      rw [hz]
      linear_combination (-(1 : ℝ) * Real.sqrt 17) * hs
    · have hrec : (A259290 (m + 3) : ℝ) = A259290 (m + 2) + 4 * A259290 (m + 1) := by
        exact_mod_cast A259290_rec m
      have ih1 := ih (m + 1) (by omega)
      have ih0 := ih m (by omega)
      rw [hrec, add_mul, mul_assoc, ih1, ih0]
      have hp1 : (2 : ℝ) ^ (1 - ((m + 2 : ℕ) : ℤ)) = 2 * (2 : ℝ) ^ (1 - ((m + 3 : ℕ) : ℤ)) := by
        have : 1 - ((m + 2 : ℕ) : ℤ) = 1 + (1 - ((m + 3 : ℕ) : ℤ)) := by omega
        rw [this, zpow_add₀ (by norm_num), zpow_one]
      have hp0 : (2 : ℝ) ^ (1 - ((m + 1 : ℕ) : ℤ)) = 4 * (2 : ℝ) ^ (1 - ((m + 3 : ℕ) : ℤ)) := by
        have : 1 - ((m + 1 : ℕ) : ℤ) = 2 + (1 - ((m + 3 : ℕ) : ℤ)) := by omega
        rw [this, zpow_add₀ (by norm_num)]; norm_num
      rw [hp1, hp0]
      have hr1 : (1 - Real.sqrt 17) ^ 2 = 2 * (1 - Real.sqrt 17) + 16 := by
        linear_combination hs
      have hr2 : (1 + Real.sqrt 17) ^ 2 = 2 * (1 + Real.sqrt 17) + 16 := by
        linear_combination hs
      have hpow1 : (1 - Real.sqrt 17) ^ (m + 3) =
          (1 - Real.sqrt 17) ^ (m + 1) * (1 - Real.sqrt 17) ^ 2 := by rw [← pow_add]
      have hpow2 : (1 + Real.sqrt 17) ^ (m + 3) =
          (1 + Real.sqrt 17) ^ (m + 1) * (1 + Real.sqrt 17) ^ 2 := by rw [← pow_add]
      have hpow1' : (1 - Real.sqrt 17) ^ (m + 2) =
          (1 - Real.sqrt 17) ^ (m + 1) * (1 - Real.sqrt 17) := by rw [pow_succ]
      have hpow2' : (1 + Real.sqrt 17) ^ (m + 2) =
          (1 + Real.sqrt 17) ^ (m + 1) * (1 + Real.sqrt 17) := by rw [pow_succ]
      rw [hpow1, hpow2, hpow1', hpow2', hr1, hr2]
      ring

end OMA.P_oeis_a259290

theorem OMA.solution : type_of% @OMA.S_oeis_a259290.main :=
  ⟨OMA.P_oeis_a259290.A259290_gf, OMA.P_oeis_a259290.A259290_binet⟩
