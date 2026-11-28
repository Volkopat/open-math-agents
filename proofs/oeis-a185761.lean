import OMAStatements.S_oeis_a185761
import Mathlib.Tactic

namespace OMA.P_oeis_a185761

open OMA.S_oeis_a185761

private def bTraceFin (a d : Bool) : Fin 3 :=
  ⟨blockTrace a d, by cases a <;> cases d <;> decide⟩

private def stepVec (v : Bool × Bool × Fin 3 → ℤ) (s2 : Bool × Bool × Fin 3) : ℤ :=
  ∑ s1 : Bool × Bool × Fin 3,
    if bTraceFin s1.1 s2.2.1 = s2.2.2 ∧ s1.2.2 ≠ s2.2.2 then v s1 else 0

private lemma stepVec_add (u v : Bool × Bool × Fin 3 → ℤ) (s : Bool × Bool × Fin 3) :
    stepVec (fun x => u x + v x) s = stepVec u s + stepVec v s := by
  unfold stepVec
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s1 _ => ?_
  split_ifs <;> ring

private lemma stepVec_smul (c : ℤ) (v : Bool × Bool × Fin 3 → ℤ) (s : Bool × Bool × Fin 3) :
    stepVec (fun x => c * v x) s = c * stepVec v s := by
  unfold stepVec
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s1 _ => ?_
  split_ifs <;> ring

private def isValidArr (k : ℕ) (A : Fin (k + 2) × Fin 2 → Bool) : Prop :=
  ∀ i : Fin k,
    blockTrace (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)) ≠
    blockTrace (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 2, by omega⟩, 1))

private instance (k : ℕ) (A : Fin (k + 2) × Fin 2 → Bool) : Decidable (isValidArr k A) := by
  unfold isValidArr; infer_instance

private def stateCount (k : ℕ) (s : Bool × Bool × Fin 3) : ℤ :=
  ∑ A : Fin (k + 2) × Fin 2 → Bool,
    if isValidArr k A ∧
       (A (⟨k + 1, by omega⟩, 0), A (⟨k + 1, by omega⟩, 1),
        bTraceFin (A (⟨k, by omega⟩, 0)) (A (⟨k + 1, by omega⟩, 1))) = s
    then 1 else 0

private lemma A185761_eq_sum_stateCount (k : ℕ) :
    (A185761 (k + 1) : ℤ) = ∑ s : Bool × Bool × Fin 3, stateCount k s := by
  unfold A185761 stateCount
  rw [Finset.sum_comm]
  have hcard : ∀ S : Finset (Fin (k + 2) × Fin 2 → Bool),
      (S.card : ℤ) = ∑ A : Fin (k + 2) × Fin 2 → Bool, if A ∈ S then (1 : ℤ) else 0 := by
    intro S; simp
  rw [hcard]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have hiff_k : (∀ i : Fin (k + 1 - 1),
      blockTrace (A (⟨i.1, by omega⟩, 0)) (A (⟨i.1 + 1, by omega⟩, 1)) ≠
      blockTrace (A (⟨i.1 + 1, by omega⟩, 0)) (A (⟨i.1 + 2, by omega⟩, 1))) ↔ isValidArr k A := by
    constructor
    · intro h i; exact h ⟨i.1, by omega⟩
    · intro h i; exact h ⟨i.1, by omega⟩
  by_cases hA : isValidArr k A
  · rw [if_pos (hiff_k.mpr hA)]
    rw [Finset.sum_eq_single
      (A (⟨k + 1, by omega⟩, 0), A (⟨k + 1, by omega⟩, 1),
       bTraceFin (A (⟨k, by omega⟩, 0)) (A (⟨k + 1, by omega⟩, 1)))]
    · simp [hA]
    · intro s _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  · rw [if_neg (fun h => hA (hiff_k.mp h))]
    refine (Finset.sum_eq_zero fun s _ => ?_).symm
    simp [hA]

private def tab0 (s : Bool × Bool × Fin 3) : ℤ :=
  ∑ a : Bool, ∑ _b : Bool, if bTraceFin a s.2.1 = s.2.2 then 1 else 0

private lemma stateCount_zero (s : Bool × Bool × Fin 3) : stateCount 0 s = tab0 s := by
  rcases s with ⟨s0, s1, st⟩
  unfold stateCount tab0 isValidArr
  let e : (Fin 2 × Fin 2 → Bool) ≃ ((Bool × Bool) × (Bool × Bool)) :=
    { toFun := fun A => ((A (0, 0), A (0, 1)), (A (1, 0), A (1, 1)))
      invFun := fun p q =>
        if q.1 = 0 then (if q.2 = 0 then p.1.1 else p.1.2)
        else (if q.2 = 0 then p.2.1 else p.2.2)
      left_inv := fun A => by funext ⟨i, j⟩; fin_cases i <;> fin_cases j <;> rfl
      right_inv := fun ⟨⟨a, b⟩, ⟨c, d⟩⟩ => rfl }
  rw [Fintype.sum_equiv e _ (fun p =>
      if (p.2.1, p.2.2, bTraceFin p.1.1 p.2.2) = (s0, s1, st) then (1 : ℤ) else 0)
      (fun A => by simp [e])]
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_eq_single (s0, s1)]
  · simp
  · intro p _ hne
    rw [if_neg]
    intro h
    apply hne
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1 h.2.1
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private lemma stateCount_succ (k : ℕ) (s : Bool × Bool × Fin 3) :
    stateCount (k + 1) s = stepVec (stateCount k) s := by
  rcases s with ⟨s0, s1, st⟩
  let e : (Fin (k + 3) × Fin 2 → Bool) ≃ ((Fin (k + 2) × Fin 2 → Bool) × (Bool × Bool)) :=
    { toFun := fun A =>
        (fun p => A (⟨p.1.1, by omega⟩, p.2),
         (A (⟨k + 2, by omega⟩, 0), A (⟨k + 2, by omega⟩, 1)))
      invFun := fun ⟨A', r'⟩ p =>
        if h : p.1.1 < k + 2 then A' (⟨p.1.1, h⟩, p.2)
        else if p.2 = 0 then r'.1 else r'.2
      left_inv := fun A => by
        funext ⟨i, j⟩
        by_cases h : i.1 < k + 2
        · simp [h]
        · have hi : i = ⟨k + 2, by omega⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
          rw [hi]; fin_cases j <;> simp
      right_inv := fun ⟨A', r'⟩ => by
        apply Prod.ext
        · funext ⟨i, j⟩; simp [i.isLt]
        · simp }
  have hiff : ∀ A : Fin (k + 3) × Fin 2 → Bool,
      (isValidArr (k + 1) A ∧
       (A (⟨k + 2, by omega⟩, 0), A (⟨k + 2, by omega⟩, 1),
        bTraceFin (A (⟨k + 1, by omega⟩, 0)) (A (⟨k + 2, by omega⟩, 1))) = (s0, s1, st)) ↔
      (isValidArr k (e A).1 ∧
       bTraceFin ((e A).1 (⟨k, by omega⟩, 0)) ((e A).1 (⟨k + 1, by omega⟩, 1)) ≠ st ∧
       bTraceFin ((e A).1 (⟨k + 1, by omega⟩, 0)) (e A).2.2 = st ∧
       (e A).2 = (s0, s1)) := by
    intro A
    simp only [e, Equiv.coe_fn_mk, isValidArr, Prod.mk.injEq]
    constructor
    · rintro ⟨hA, hs0, hs1, hst⟩
      refine ⟨fun i => hA ⟨i.1, by omega⟩, ?_, hst, hs0, hs1⟩
      intro heq
      have hlast := hA ⟨k, by omega⟩
      dsimp at hlast
      apply hlast
      have h1 := congrArg Fin.val heq
      have h2 := congrArg Fin.val hst
      simp only [bTraceFin] at h1 h2
      omega
    · rintro ⟨hA', hne, hst, hs0, hs1⟩
      refine ⟨fun i => ?_, hs0, hs1, hst⟩
      by_cases hi : i.1 < k
      · exact hA' ⟨i.1, hi⟩
      · have hieq : i = ⟨k, by omega⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
        rw [hieq]
        intro heq
        apply hne
        rw [← hst]
        exact Fin.ext (by simpa [bTraceFin] using heq)
  unfold stateCount stepVec
  rw [Fintype.sum_equiv e _ (fun p =>
      if isValidArr k p.1 ∧
         bTraceFin (p.1 (⟨k, by omega⟩, 0)) (p.1 (⟨k + 1, by omega⟩, 1)) ≠ st ∧
         bTraceFin (p.1 (⟨k + 1, by omega⟩, 0)) p.2.2 = st ∧
         p.2 = (s0, s1) then (1 : ℤ) else 0)
      (fun A => by simp only [hiff A])]
  rw [Fintype.sum_prod_type]
  have hr_sum : ∀ A' : Fin (k + 2) × Fin 2 → Bool,
      (∑ r' : Bool × Bool,
        if isValidArr k A' ∧
           bTraceFin (A' (⟨k, by omega⟩, 0)) (A' (⟨k + 1, by omega⟩, 1)) ≠ st ∧
           bTraceFin (A' (⟨k + 1, by omega⟩, 0)) r'.2 = st ∧
           r' = (s0, s1) then (1 : ℤ) else 0) =
      if isValidArr k A' ∧
         bTraceFin (A' (⟨k, by omega⟩, 0)) (A' (⟨k + 1, by omega⟩, 1)) ≠ st ∧
         bTraceFin (A' (⟨k + 1, by omega⟩, 0)) s1 = st
      then (1 : ℤ) else 0 := by
    intro A'
    rw [Finset.sum_eq_single (s0, s1)]
    · simp
    · intro r' _ hne; simp [hne]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  simp_rw [hr_sum]
  symm
  trans ∑ s1' : Bool × Bool × Fin 3, ∑ A' : Fin (k + 2) × Fin 2 → Bool,
      if isValidArr k A' ∧
         (A' (⟨k + 1, by omega⟩, 0), A' (⟨k + 1, by omega⟩, 1),
          bTraceFin (A' (⟨k, by omega⟩, 0)) (A' (⟨k + 1, by omega⟩, 1))) = s1' ∧
         bTraceFin s1'.1 s1 = st ∧ s1'.2.2 ≠ st then (1 : ℤ) else 0
  · refine Finset.sum_congr rfl fun s1' _ => ?_
    by_cases h : bTraceFin s1'.1 s1 = st ∧ s1'.2.2 ≠ st
    · simp [h]
    · rw [if_neg h]
      refine (Finset.sum_eq_zero fun A' _ => ?_).symm
      split_ifs with hp
      · exact (h ⟨hp.2.2.1, hp.2.2.2⟩).elim
      · rfl
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A' _ => ?_
    rw [Finset.sum_eq_single
      (A' (⟨k + 1, by omega⟩, 0), A' (⟨k + 1, by omega⟩, 1),
       bTraceFin (A' (⟨k, by omega⟩, 0)) (A' (⟨k + 1, by omega⟩, 1)))]
    · simp [and_comm]
    · intro s1' _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private lemma stateCount_zero_fun : stateCount 0 = tab0 := funext stateCount_zero
private lemma stateCount_succ_fun (k : ℕ) : stateCount (k + 1) = stepVec (stateCount k) :=
  funext (stateCount_succ k)

private lemma stateCount_rec_base :
    stateCount 2 = fun s => stateCount 1 s + 4 * stateCount 0 s := by
  funext s
  simp only [stateCount_succ_fun, stateCount_zero_fun]
  revert s; decide

private lemma stateCount_rec (m : ℕ) :
    stateCount (m + 2) = fun s => stateCount (m + 1) s + 4 * stateCount m s := by
  induction m with
  | zero => exact stateCount_rec_base
  | succ m ih =>
    funext s
    conv_lhs =>
      rw [stateCount_succ (m + 2) s, ih, stepVec_add, stepVec_smul,
        ← stateCount_succ (m + 1) s, ← stateCount_succ m s]

private lemma A185761_rec (m : ℕ) :
    (A185761 (m + 3) : ℤ) = A185761 (m + 2) + 4 * A185761 (m + 1) := by
  rw [show m + 3 = (m + 2) + 1 by omega, show m + 2 = (m + 1) + 1 by omega,
    A185761_eq_sum_stateCount (m + 2), A185761_eq_sum_stateCount (m + 1),
    A185761_eq_sum_stateCount m, stateCount_rec m, Finset.sum_add_distrib, ← Finset.mul_sum]

private lemma A185761_small : A185761 1 = 16 ∧ A185761 2 = 40 := by
  have h1 : (A185761 1 : ℤ) = 16 := by
    rw [show (1 : ℕ) = 0 + 1 by rfl, A185761_eq_sum_stateCount 0, stateCount_zero_fun]; decide
  have h2 : (A185761 2 : ℤ) = 40 := by
    rw [show (2 : ℕ) = 1 + 1 by rfl, A185761_eq_sum_stateCount 1, stateCount_succ_fun,
      stateCount_zero_fun]; decide
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

private lemma A185761_gf :
    (1 - PowerSeries.X - 4 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A185761 n : ℤ)) =
      8 * PowerSeries.X * (2 + 3 * PowerSeries.X) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A185761 n : ℤ))
  have hlhs : (1 - PowerSeries.X - 4 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.X ^ 1 * F - PowerSeries.C 4 * (PowerSeries.X ^ 2 * F) := by
    have h4 : PowerSeries.C (4 : ℤ) = (4 : PowerSeries ℤ) := rfl
    rw [h4, pow_one]; ring
  have hrhs : 8 * (PowerSeries.X : PowerSeries ℤ) * (2 + 3 * PowerSeries.X) =
      PowerSeries.C 16 * PowerSeries.X + PowerSeries.C 24 * PowerSeries.X ^ 2 := by
    have h16 : PowerSeries.C (16 : ℤ) = (16 : PowerSeries ℤ) := rfl
    have h24 : PowerSeries.C (24 : ℤ) = (24 : PowerSeries ℤ) := rfl
    rw [h16, h24]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2⟩ := A185761_small
  by_cases hn2 : n ≤ 2
  · interval_cases n <;> simp [F, h1, h2]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show 1 ≤ n by omega, show 2 ≤ n by omega,
      show n - 1 ≠ 0 by omega, show n - 2 ≠ 0 by omega, ↓reduceIte, mul_zero, add_zero]
    have hrec := A185761_rec (n - 3)
    simp only [show n - 3 + 3 = n by omega, show n - 3 + 2 = n - 1 by omega,
      show n - 3 + 1 = n - 2 by omega] at hrec
    linarith

private lemma A185761_binet (n : ℕ) (hn : 1 ≤ n) :
    (A185761 n : ℝ) =
      ((2 : ℝ) ^ (-(n : ℤ)) *
        ((1 - Real.sqrt 17) ^ n * (-13 + 3 * Real.sqrt 17) +
         (1 + Real.sqrt 17) ^ n * (13 + 3 * Real.sqrt 17))) / Real.sqrt 17 := by
  have hs_pos : (0 : ℝ) < Real.sqrt 17 := Real.sqrt_pos.mpr (by norm_num)
  have hs : Real.sqrt 17 ^ 2 = 17 := Real.sq_sqrt (by norm_num)
  set s := Real.sqrt 17
  set r1 : ℝ := (1 + s) / 2
  set r2 : ℝ := (1 - s) / 2
  have hbinet_eq : ∀ k : ℕ,
      ((2 : ℝ) ^ (-(k : ℤ)) *
        ((1 - s) ^ k * (-13 + 3 * s) + (1 + s) ^ k * (13 + 3 * s))) / s =
      ((-13 + 3 * s) * r2 ^ k + (13 + 3 * s) * r1 ^ k) / s := by
    intro k
    have hpow : (2 : ℝ) ^ (-(k : ℤ)) = ((2 : ℝ) ^ k)⁻¹ := by
      rw [zpow_neg, zpow_natCast]
    have hr1k : r1 ^ k = (1 + s) ^ k * ((2 : ℝ) ^ k)⁻¹ := by
      simp only [r1, div_eq_mul_inv, mul_pow, inv_pow]
    have hr2k : r2 ^ k = (1 - s) ^ k * ((2 : ℝ) ^ k)⁻¹ := by
      simp only [r2, div_eq_mul_inv, mul_pow, inv_pow]
    rw [hpow, hr1k, hr2k]; ring
  rw [hbinet_eq n]
  suffices h : ∀ k : ℕ,
      (A185761 (k + 1) : ℝ) * s =
        (-13 + 3 * s) * r2 ^ (k + 1) + (13 + 3 * s) * r1 ^ (k + 1) by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    rw [eq_div_iff (ne_of_gt hs_pos)]
    exact h k
  have hr1_sq : r1 ^ 2 = r1 + 4 := by
    have : r1 ^ 2 - (r1 + 4) = (s ^ 2 - 17) / 4 := by simp only [r1]; ring
    linarith [this, hs]
  have hr2_sq : r2 ^ 2 = r2 + 4 := by
    have : r2 ^ 2 - (r2 + 4) = (s ^ 2 - 17) / 4 := by simp only [r2]; ring
    linarith [this, hs]
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h1, h2⟩ := A185761_small
    rcases k with _ | _ | m
    · rw [show (0 : ℕ) + 1 = 1 by rfl, h1]
      have : (-13 + 3 * s) * r2 ^ 1 + (13 + 3 * s) * r1 ^ 1 - (16 : ℝ) * s = 0 := by
        simp only [r1, r2, pow_one]; ring
      norm_num; linarith
    · rw [show (1 : ℕ) + 1 = 2 by rfl, h2]
      have : (-13 + 3 * s) * r2 ^ 2 + (13 + 3 * s) * r1 ^ 2 - (40 : ℝ) * s =
          (3 / 2) * (s ^ 2 - 17) * s := by
        simp only [r1, r2]; ring
      norm_num
      have h0 : (3 / 2) * (s ^ 2 - 17) * s = 0 := by rw [hs]; ring
      linarith
    · have hrec : (A185761 (m + 3) : ℝ) = A185761 (m + 2) + 4 * A185761 (m + 1) := by
        exact_mod_cast A185761_rec m
      have ih1 := ih (m + 1) (by omega)
      have ih0 := ih m (by omega)
      have hpow1 : r1 ^ (m + 3) = r1 ^ (m + 2) + 4 * r1 ^ (m + 1) := by
        calc r1 ^ (m + 3) = r1 ^ 2 * r1 ^ (m + 1) := by ring
          _ = (r1 + 4) * r1 ^ (m + 1) := by rw [hr1_sq]
          _ = r1 ^ (m + 2) + 4 * r1 ^ (m + 1) := by ring
      have hpow2 : r2 ^ (m + 3) = r2 ^ (m + 2) + 4 * r2 ^ (m + 1) := by
        calc r2 ^ (m + 3) = r2 ^ 2 * r2 ^ (m + 1) := by ring
          _ = (r2 + 4) * r2 ^ (m + 1) := by rw [hr2_sq]
          _ = r2 ^ (m + 2) + 4 * r2 ^ (m + 1) := by ring
      rw [show m + 2 + 1 = m + 3 by omega, hrec, hpow1, hpow2]
      rw [show m + 1 + 1 = m + 2 by omega] at ih1
      linarith

end OMA.P_oeis_a185761

theorem OMA.solution : type_of% @OMA.S_oeis_a185761.main :=
  ⟨OMA.P_oeis_a185761.A185761_gf, OMA.P_oeis_a185761.A185761_binet⟩
