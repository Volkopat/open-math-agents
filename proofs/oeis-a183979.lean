import OMAStatements.S_oeis_a183979
import Mathlib.Tactic

namespace OMA.P_oeis_a183979

open OMA.S_oeis_a183979

private def adj (s : Fin 5) (r1 r2 : Bool × Bool × Bool) : Bool :=
  decide (blockSum r1.1 r1.2.1 r2.1 r2.2.1 = s.1 ∧ blockSum r1.2.1 r1.2.2 r2.2.1 r2.2.2 = s.1)

private def stepVec (s : Fin 5) (v : Bool × Bool × Bool → ℤ) (r2 : Bool × Bool × Bool) : ℤ :=
  ∑ r1 : Bool × Bool × Bool, if adj s r1 r2 then v r1 else 0

private lemma stepVec_add (s : Fin 5) (u v : Bool × Bool × Bool → ℤ) (r : Bool × Bool × Bool) :
    stepVec s (fun x => u x + v x) r = stepVec s u r + stepVec s v r := by
  unfold stepVec
  simp only [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private lemma stepVec_sub (s : Fin 5) (u v : Bool × Bool × Bool → ℤ) (r : Bool × Bool × Bool) :
    stepVec s (fun x => u x - v x) r = stepVec s u r - stepVec s v r := by
  unfold stepVec
  simp only [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private lemma stepVec_smul (s : Fin 5) (c : ℤ) (v : Bool × Bool × Bool → ℤ) (r : Bool × Bool × Bool) :
    stepVec s (fun x => c * v x) r = c * stepVec s v r := by
  unfold stepVec
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun r1 _ => ?_
  split_ifs <;> ring

private def isValidSum (s : Fin 5) (n : ℕ) (A : Fin (n + 1) × Fin 3 → Bool) : Prop :=
  ∀ (i : Fin n) (j : Fin 2),
    blockSum (A (⟨i.1, by omega⟩, ⟨j.1, by omega⟩))
      (A (⟨i.1, by omega⟩, ⟨j.1 + 1, by omega⟩))
      (A (⟨i.1 + 1, by omega⟩, ⟨j.1, by omega⟩))
      (A (⟨i.1 + 1, by omega⟩, ⟨j.1 + 1, by omega⟩)) = s.1

private instance (s : Fin 5) (n : ℕ) (A : Fin (n + 1) × Fin 3 → Bool) :
    Decidable (isValidSum s n A) := by
  unfold isValidSum; infer_instance

private def sumCount (s : Fin 5) (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun A : Fin (n + 1) × Fin 3 → Bool => isValidSum s n A)).card

private def rawCount (n : ℕ) : ℕ := ∑ s : Fin 5, sumCount s n

private lemma blockSum_lt_five (a b c d : Bool) : blockSum a b c d < 5 := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

open scoped Classical in
private lemma A183979_eq_rawCount_div (n : ℕ) (hn : 1 ≤ n) :
    A183979 n = rawCount n / 4 := by
  unfold A183979 rawCount sumCount
  congr 1
  have hdisj : Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 5)))
      (fun s => Finset.univ.filter (fun A : Fin (n + 1) × Fin 3 → Bool => isValidSum s n A)) := by
    intro s1 _ s2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro A h1 h2
    rw [Finset.mem_filter] at h1 h2
    have e1 := h1.2 ⟨0, by omega⟩ ⟨0, by omega⟩
    have e2 := h2.2 ⟨0, by omega⟩ ⟨0, by omega⟩
    exact hne (Fin.ext (by omega))
  rw [← Finset.card_biUnion hdisj]
  congr 1
  ext A
  rw [Finset.mem_filter, Finset.mem_biUnion]
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨s, hA⟩
    have hlt : s < 5 := by
      have h0 := hA ⟨0, by omega⟩ ⟨0, by omega⟩
      rw [← h0]; exact blockSum_lt_five _ _ _ _
    exact ⟨⟨s, hlt⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hA⟩⟩
  · rintro ⟨s, hA⟩
    exact ⟨s.1, (Finset.mem_filter.mp hA).2⟩

private def rowCount (s : Fin 5) (n : ℕ) (r : Bool × Bool × Bool) : ℤ :=
  ∑ A : Fin (n + 1) × Fin 3 → Bool,
    if isValidSum s n A ∧
       (A (⟨n, Nat.lt_succ_self n⟩, 0), A (⟨n, Nat.lt_succ_self n⟩, 1),
        A (⟨n, Nat.lt_succ_self n⟩, 2)) = r
    then 1 else 0

private lemma sumCount_eq_sum_rowCount (s : Fin 5) (n : ℕ) :
    (sumCount s n : ℤ) = ∑ r : Bool × Bool × Bool, rowCount s n r := by
  unfold sumCount rowCount
  rw [Finset.sum_comm]
  have hcard : ∀ S : Finset (Fin (n + 1) × Fin 3 → Bool),
      (S.card : ℤ) = ∑ A : Fin (n + 1) × Fin 3 → Bool, if A ∈ S then (1 : ℤ) else 0 := by
    intro S; simp
  rw [hcard]
  refine Finset.sum_congr rfl fun A _ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hA : isValidSum s n A
  · rw [if_pos hA]
    rw [Finset.sum_eq_single
      (A (⟨n, Nat.lt_succ_self n⟩, 0), A (⟨n, Nat.lt_succ_self n⟩, 1),
       A (⟨n, Nat.lt_succ_self n⟩, 2))]
    · simp [hA]
    · intro r _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  · rw [if_neg hA]
    refine (Finset.sum_eq_zero fun r _ => ?_).symm
    simp [hA]

private lemma rowCount_zero (s : Fin 5) (r : Bool × Bool × Bool) : rowCount s 0 r = 1 := by
  unfold rowCount isValidSum
  let A0 : Fin 1 × Fin 3 → Bool := fun p =>
    if p.2 = 0 then r.1 else if p.2 = 1 then r.2.1 else r.2.2
  rw [Finset.sum_eq_single A0]
  · simp [A0]
  · intro A _ hne
    rw [if_neg]
    rintro ⟨_, hr⟩
    apply hne
    funext ⟨i, j⟩
    fin_cases i; fin_cases j
    · exact congrArg Prod.fst hr
    · exact congrArg (fun x => x.2.1) hr
    · exact congrArg (fun x => x.2.2) hr
  · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private lemma rowCount_succ (s : Fin 5) (n : ℕ) (r : Bool × Bool × Bool) :
    rowCount s (n + 1) r = stepVec s (rowCount s n) r := by
  let e : (Fin (n + 2) × Fin 3 → Bool) ≃
      ((Fin (n + 1) × Fin 3 → Bool) × (Bool × Bool × Bool)) :=
    { toFun := fun A =>
        (fun p => A (⟨p.1.1, by omega⟩, p.2),
         (A (⟨n + 1, Nat.lt_succ_self _⟩, 0), A (⟨n + 1, Nat.lt_succ_self _⟩, 1),
          A (⟨n + 1, Nat.lt_succ_self _⟩, 2)))
      invFun := fun ⟨A', r'⟩ p =>
        if h : p.1.1 < n + 1 then A' (⟨p.1.1, h⟩, p.2)
        else if p.2 = 0 then r'.1 else if p.2 = 1 then r'.2.1 else r'.2.2
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
  have hiff : ∀ A : Fin (n + 2) × Fin 3 → Bool,
      (isValidSum s (n + 1) A ∧
       (A (⟨n + 1, Nat.lt_succ_self _⟩, 0), A (⟨n + 1, Nat.lt_succ_self _⟩, 1),
        A (⟨n + 1, Nat.lt_succ_self _⟩, 2)) = r) ↔
      (isValidSum s n (e A).1 ∧
       adj s ((e A).1 (⟨n, Nat.lt_succ_self n⟩, 0), (e A).1 (⟨n, Nat.lt_succ_self n⟩, 1),
              (e A).1 (⟨n, Nat.lt_succ_self n⟩, 2)) (e A).2 = true ∧
       (e A).2 = r) := by
    intro A
    simp only [e, Equiv.coe_fn_mk, isValidSum, adj, decide_eq_true_eq]
    constructor
    · rintro ⟨hA, hr⟩
      refine ⟨fun i j => hA ⟨i.1, by omega⟩ j,
        ⟨hA ⟨n, Nat.lt_succ_self n⟩ ⟨0, by omega⟩, hA ⟨n, Nat.lt_succ_self n⟩ ⟨1, by omega⟩⟩, hr⟩
    · rintro ⟨hA', ⟨hlast0, hlast1⟩, hr⟩
      refine ⟨fun i j => ?_, hr⟩
      by_cases hi : i.1 < n
      · exact hA' ⟨i.1, hi⟩ j
      · have hieq : i = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by have := i.isLt; dsimp; omega)
        subst hieq
        fin_cases j
        · exact hlast0
        · exact hlast1
  unfold rowCount stepVec
  rw [Fintype.sum_equiv e _ (fun p =>
      if isValidSum s n p.1 ∧
         adj s (p.1 (⟨n, Nat.lt_succ_self n⟩, 0), p.1 (⟨n, Nat.lt_succ_self n⟩, 1),
                p.1 (⟨n, Nat.lt_succ_self n⟩, 2)) p.2 = true ∧
         p.2 = r then (1 : ℤ) else 0)
      (fun A => by simp only [hiff A])]
  rw [Fintype.sum_prod_type]
  have hr_sum : ∀ A' : Fin (n + 1) × Fin 3 → Bool,
      (∑ r' : Bool × Bool × Bool,
        if isValidSum s n A' ∧
           adj s (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1),
                  A' (⟨n, Nat.lt_succ_self n⟩, 2)) r' = true ∧
           r' = r then (1 : ℤ) else 0) =
      if isValidSum s n A' ∧
         adj s (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1),
                A' (⟨n, Nat.lt_succ_self n⟩, 2)) r = true
      then (1 : ℤ) else 0 := by
    intro A'
    rw [Finset.sum_eq_single r]
    · simp
    · intro r' _ hne; simp [hne]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim
  simp_rw [hr_sum]
  symm
  trans ∑ r1 : Bool × Bool × Bool, ∑ A' : Fin (n + 1) × Fin 3 → Bool,
      if isValidSum s n A' ∧
         (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1),
          A' (⟨n, Nat.lt_succ_self n⟩, 2)) = r1 ∧
         adj s r1 r = true then (1 : ℤ) else 0
  · refine Finset.sum_congr rfl fun r1 _ => ?_
    by_cases hadj : adj s r1 r = true <;> simp [hadj]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun A' _ => ?_
    rw [Finset.sum_eq_single
      (A' (⟨n, Nat.lt_succ_self n⟩, 0), A' (⟨n, Nat.lt_succ_self n⟩, 1),
       A' (⟨n, Nat.lt_succ_self n⟩, 2))]
    · simp
    · intro r1 _ hne; simp [hne.symm]
    · intro hnot; exact (hnot (Finset.mem_univ _)).elim

private lemma rowCount_zero_fun (s : Fin 5) : rowCount s 0 = fun _ => 1 := funext (rowCount_zero s)
private lemma rowCount_succ_fun (s : Fin 5) (n : ℕ) :
    rowCount s (n + 1) = stepVec s (rowCount s n) := funext (rowCount_succ s n)

private lemma rowCount_rec_base (s : Fin 5) :
    rowCount s 5 = fun r => 3 * rowCount s 4 r - 6 * rowCount s 2 r + 4 * rowCount s 1 r := by
  funext r
  simp only [rowCount_succ_fun, rowCount_zero_fun]
  revert s r; decide

private lemma rowCount_rec (s : Fin 5) (m : ℕ) :
    rowCount s (m + 5) =
      fun r => 3 * rowCount s (m + 4) r - 6 * rowCount s (m + 2) r + 4 * rowCount s (m + 1) r := by
  induction m with
  | zero => exact rowCount_rec_base s
  | succ m ih =>
    funext r
    conv_lhs =>
      rw [rowCount_succ s (m + 5) r, ih, stepVec_add, stepVec_sub, stepVec_smul, stepVec_smul,
        stepVec_smul, ← rowCount_succ s (m + 4) r, ← rowCount_succ s (m + 2) r,
        ← rowCount_succ s (m + 1) r]

private lemma rawCount_rec (m : ℕ) :
    (rawCount (m + 5) : ℤ) =
      3 * rawCount (m + 4) - 6 * rawCount (m + 2) + 4 * rawCount (m + 1) := by
  unfold rawCount
  push_cast
  simp only [sumCount_eq_sum_rowCount]
  trans ∑ s : Fin 5, ∑ r : Bool × Bool × Bool,
      (3 * rowCount s (m + 4) r - 6 * rowCount s (m + 2) r + 4 * rowCount s (m + 1) r)
  · refine Finset.sum_congr rfl fun s _ => ?_
    rw [rowCount_rec s m]
  · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]

private lemma rawCount_small :
    rawCount 1 = 24 ∧ rawCount 2 = 32 ∧ rawCount 3 = 44 ∧ rawCount 4 = 68 := by
  have h1 : (rawCount 1 : ℤ) = 24 := by
    unfold rawCount; push_cast; simp only [sumCount_eq_sum_rowCount, rowCount_succ_fun, rowCount_zero_fun]; decide
  have h2 : (rawCount 2 : ℤ) = 32 := by
    unfold rawCount; push_cast; simp only [sumCount_eq_sum_rowCount, rowCount_succ_fun, rowCount_zero_fun]; decide
  have h3 : (rawCount 3 : ℤ) = 44 := by
    unfold rawCount; push_cast; simp only [sumCount_eq_sum_rowCount, rowCount_succ_fun, rowCount_zero_fun]; decide
  have h4 : (rawCount 4 : ℤ) = 68 := by
    unfold rawCount; push_cast; simp only [sumCount_eq_sum_rowCount, rowCount_succ_fun, rowCount_zero_fun]; decide
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2, by exact_mod_cast h3, by exact_mod_cast h4⟩

private lemma four_dvd_rawCount (n : ℕ) (hn : 1 ≤ n) : 4 ∣ rawCount n := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
  clear hn
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := rawCount_small
    rcases k with _ | _ | _ | _ | m
    · rw [h1]; exact ⟨6, rfl⟩
    · rw [h2]; exact ⟨8, rfl⟩
    · rw [h3]; exact ⟨11, rfl⟩
    · rw [h4]; exact ⟨17, rfl⟩
    · have hrec := rawCount_rec m
      obtain ⟨a, ha⟩ := ih (m + 3) (by omega)
      obtain ⟨b, hb⟩ := ih (m + 1) (by omega)
      obtain ⟨c, hc⟩ := ih m (by omega)
      rw [show m + 3 + 1 = m + 4 by omega] at ha
      rw [show m + 1 + 1 = m + 2 by omega] at hb
      have hdiv : (4 : ℤ) ∣ (rawCount (m + 5) : ℤ) := by
        refine ⟨3 * (a : ℤ) - 6 * (b : ℤ) + 4 * (c : ℤ), ?_⟩
        have ha' : (rawCount (m + 4) : ℤ) = 4 * a := by exact_mod_cast ha
        have hb' : (rawCount (m + 2) : ℤ) = 4 * b := by exact_mod_cast hb
        have hc' : (rawCount (m + 1) : ℤ) = 4 * c := by exact_mod_cast hc
        linarith
      rw [show m + 4 + 1 = m + 5 by omega]
      exact_mod_cast hdiv

private lemma four_mul_A183979 (n : ℕ) (hn : 1 ≤ n) :
    4 * (A183979 n : ℤ) = (rawCount n : ℤ) := by
  have hd := four_dvd_rawCount n hn
  have hnat : 4 * A183979 n = rawCount n := by
    rw [A183979_eq_rawCount_div n hn, Nat.mul_div_cancel' hd]
  exact_mod_cast hnat

private lemma A183979_rec (m : ℕ) :
    (A183979 (m + 5) : ℤ) =
      3 * A183979 (m + 4) - 6 * A183979 (m + 2) + 4 * A183979 (m + 1) := by
  have h5 := four_mul_A183979 (m + 5) (by omega)
  have h4 := four_mul_A183979 (m + 4) (by omega)
  have h2 := four_mul_A183979 (m + 2) (by omega)
  have h1 := four_mul_A183979 (m + 1) (by omega)
  have hrec := rawCount_rec m
  linarith

private lemma A183979_small :
    A183979 1 = 6 ∧ A183979 2 = 8 ∧ A183979 3 = 11 ∧ A183979 4 = 17 := by
  obtain ⟨h1, h2, h3, h4⟩ := rawCount_small
  rw [A183979_eq_rawCount_div 1 (by omega), A183979_eq_rawCount_div 2 (by omega),
    A183979_eq_rawCount_div 3 (by omega), A183979_eq_rawCount_div 4 (by omega),
    h1, h2, h3, h4]
  exact ⟨rfl, rfl, rfl, rfl⟩

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

private lemma A183979_gf :
    (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2) *
      PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A183979 n : ℤ)) =
      PowerSeries.X * (6 - 10 * PowerSeries.X - 13 * PowerSeries.X ^ 2 + 20 * PowerSeries.X ^ 3) := by
  set F : PowerSeries ℤ := PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else (A183979 n : ℤ))
  have hlhs : (1 - PowerSeries.X) * (1 - 2 * PowerSeries.X) * (1 - 2 * PowerSeries.X ^ 2) * F =
      F - PowerSeries.C 3 * (PowerSeries.X ^ 1 * F) +
        PowerSeries.C 6 * (PowerSeries.X ^ 3 * F) - PowerSeries.C 4 * (PowerSeries.X ^ 4 * F) := by
    have h3 : PowerSeries.C (3 : ℤ) = (3 : PowerSeries ℤ) := rfl
    have h6 : PowerSeries.C (6 : ℤ) = (6 : PowerSeries ℤ) := rfl
    have h4 : PowerSeries.C (4 : ℤ) = (4 : PowerSeries ℤ) := rfl
    rw [h3, h6, h4, pow_one]; ring
  have hrhs : (PowerSeries.X : PowerSeries ℤ) *
        (6 - 10 * PowerSeries.X - 13 * PowerSeries.X ^ 2 + 20 * PowerSeries.X ^ 3) =
      PowerSeries.C 6 * PowerSeries.X - PowerSeries.C 10 * PowerSeries.X ^ 2 -
      PowerSeries.C 13 * PowerSeries.X ^ 3 + PowerSeries.C 20 * PowerSeries.X ^ 4 := by
    have h6 : PowerSeries.C (6 : ℤ) = (6 : PowerSeries ℤ) := rfl
    have h10 : PowerSeries.C (10 : ℤ) = (10 : PowerSeries ℤ) := rfl
    have h13 : PowerSeries.C (13 : ℤ) = (13 : PowerSeries ℤ) := rfl
    have h20 : PowerSeries.C (20 : ℤ) = (20 : PowerSeries ℤ) := rfl
    rw [h6, h10, h13, h20]; ring
  rw [hlhs, hrhs]
  ext n
  simp only [map_add, map_sub, PowerSeries.coeff_C_mul, coeff_X_pow_mul_eq,
    PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
  obtain ⟨h1, h2, h3, h4⟩ := A183979_small
  by_cases hn4 : n ≤ 4
  · interval_cases n <;> simp [F, h1, h2, h3, h4]
  · simp only [F, PowerSeries.coeff_mk, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, show 1 ≤ n by omega,
      show 3 ≤ n by omega, show 4 ≤ n by omega, show n - 1 ≠ 0 by omega, show n - 3 ≠ 0 by omega,
      show n - 4 ≠ 0 by omega, ↓reduceIte, mul_zero, sub_zero, add_zero]
    have hrec := A183979_rec (n - 5)
    simp only [show n - 5 + 5 = n by omega, show n - 5 + 4 = n - 1 by omega,
      show n - 5 + 2 = n - 3 by omega, show n - 5 + 1 = n - 4 by omega] at hrec
    linarith

private lemma A183979_closed (n : ℕ) (hn : 1 ≤ n) :
    if Even n then 2 * A183979 n = 3 * 2 ^ (n / 2) + 2 ^ n + 6
    else A183979 n = 2 ^ (n - 1) + 2 ^ ((n + 1) / 2) + 3 := by
  suffices h : ∀ k : ℕ,
      2 * (A183979 (k + 1) : ℤ) =
        if Even (k + 1) then 3 * (2 : ℤ) ^ ((k + 1) / 2) + (2 : ℤ) ^ (k + 1) + 6
        else (2 : ℤ) ^ (k + 1) + 2 * (2 : ℤ) ^ ((k + 2) / 2) + 6 by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hn
    have hk := h k
    by_cases hev : Even (k + 1)
    · rw [if_pos hev] at hk ⊢; exact_mod_cast hk
    · rw [if_neg hev] at hk ⊢
      rw [Nat.add_sub_cancel]
      have h2k : (2 : ℤ) ^ (k + 1) = 2 * (2 : ℤ) ^ k := by rw [pow_succ]; ring
      rw [h2k] at hk
      have hnat : (A183979 (k + 1) : ℤ) = (2 : ℤ) ^ k + (2 : ℤ) ^ ((k + 2) / 2) + 3 := by linarith
      exact_mod_cast hnat
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    obtain ⟨h1, h2, h3, h4⟩ := A183979_small
    rcases k with _ | _ | _ | _ | m
    · simp [h1]
    · simp [h2]
    · have ho3 : ¬ Even 3 := by decide
      simp [h3, ho3]
    · have he4 : Even 4 := by decide
      simp [h4, he4]
    · have hrec := A183979_rec m
      have ih3 := ih (m + 3) (by omega)
      have ih1 := ih (m + 1) (by omega)
      have ih0 := ih m (by omega)
      rw [show m + 4 + 1 = m + 5 by omega, hrec]
      by_cases hev : Even (m + 5)
      · have h4o : ¬ Even (m + 4) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2o : ¬ Even (m + 2) := by rw [Nat.even_iff] at hev ⊢; omega
        have h1e : Even (m + 1) := by rw [Nat.even_iff] at hev ⊢; omega
        rw [if_pos hev]
        rw [show m + 3 + 1 = m + 4 by omega, if_neg h4o] at ih3
        rw [show m + 1 + 1 = m + 2 by omega, if_neg h2o] at ih1
        rw [if_pos h1e] at ih0
        have hp5 : (2 : ℤ) ^ (m + 5) = 16 * (2 : ℤ) ^ (m + 1) := by
          rw [show m + 5 = (m + 1) + 4 by omega, pow_add]; ring
        have hp4 : (2 : ℤ) ^ (m + 4) = 8 * (2 : ℤ) ^ (m + 1) := by
          rw [show m + 4 = (m + 1) + 3 by omega, pow_add]; ring
        have hp2 : (2 : ℤ) ^ (m + 2) = 2 * (2 : ℤ) ^ (m + 1) := by
          rw [show m + 2 = (m + 1) + 1 by omega, pow_add]; ring
        have hd5 : (2 : ℤ) ^ ((m + 5) / 2) = 4 * (2 : ℤ) ^ ((m + 1) / 2) := by
          rw [show (m + 5) / 2 = (m + 1) / 2 + 2 by omega, pow_add]; ring
        have hd4 : (2 : ℤ) ^ ((m + 3 + 2) / 2) = 4 * (2 : ℤ) ^ ((m + 1) / 2) := by
          rw [show (m + 3 + 2) / 2 = (m + 1) / 2 + 2 by omega, pow_add]; ring
        have hd2 : (2 : ℤ) ^ ((m + 1 + 2) / 2) = 2 * (2 : ℤ) ^ ((m + 1) / 2) := by
          rw [show (m + 1 + 2) / 2 = (m + 1) / 2 + 1 by omega, pow_succ]; ring
        rw [hp5, hd5]; rw [hp4, hd4] at ih3; rw [hp2, hd2] at ih1
        linarith
      · have h4e : Even (m + 4) := by rw [Nat.even_iff] at hev ⊢; omega
        have h2e : Even (m + 2) := by rw [Nat.even_iff] at hev ⊢; omega
        have h1o : ¬ Even (m + 1) := by rw [Nat.even_iff] at hev ⊢; omega
        rw [if_neg hev]
        rw [show m + 3 + 1 = m + 4 by omega, if_pos h4e] at ih3
        rw [show m + 1 + 1 = m + 2 by omega, if_pos h2e] at ih1
        rw [if_neg h1o] at ih0
        have hp5 : (2 : ℤ) ^ (m + 5) = 16 * (2 : ℤ) ^ (m + 1) := by
          rw [show m + 5 = (m + 1) + 4 by omega, pow_add]; ring
        have hp4 : (2 : ℤ) ^ (m + 4) = 8 * (2 : ℤ) ^ (m + 1) := by
          rw [show m + 4 = (m + 1) + 3 by omega, pow_add]; ring
        have hp2 : (2 : ℤ) ^ (m + 2) = 2 * (2 : ℤ) ^ (m + 1) := by
          rw [show m + 2 = (m + 1) + 1 by omega, pow_add]; ring
        have hd5 : (2 : ℤ) ^ ((m + 4 + 2) / 2) = 4 * (2 : ℤ) ^ ((m + 2) / 2) := by
          rw [show (m + 4 + 2) / 2 = (m + 2) / 2 + 2 by omega, pow_add]; ring
        have hd4 : (2 : ℤ) ^ ((m + 4) / 2) = 2 * (2 : ℤ) ^ ((m + 2) / 2) := by
          rw [show (m + 4) / 2 = (m + 2) / 2 + 1 by omega, pow_succ]; ring
        rw [hp5, hd5]; rw [hp4, hd4] at ih3; rw [hp2] at ih1
        linarith

end OMA.P_oeis_a183979

theorem OMA.solution : type_of% @OMA.S_oeis_a183979.main :=
  ⟨OMA.P_oeis_a183979.A183979_gf, OMA.P_oeis_a183979.A183979_closed⟩
