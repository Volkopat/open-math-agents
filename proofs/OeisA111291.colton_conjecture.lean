import FormalConjectures.OEIS.«111291»
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Tactic

/-!
# Proof of Colton's Conjecture (`OeisA111291.colton_conjecture`)

For every natural number `n`, `Nat.primeCounting n ≤ 2 * countRefactorableNat n`.

Overview of the proof:
1. Elementary zero-PNT Chebyshev-Sylvester bounds on `ψ(x)` and `θ(x)` (`D = 2520`) yielding
   `0.9400 * x ≤ θ(x) ≤ 1.0562 * x` for all `x ≥ 10^7`.
2. Width-1 segmented bitset sieve with 4-step SWAR popcount, trial-factorization verifier
   `fastTauTop`, and exact base verification of Colton's conjecture through `n ≤ 4096`.
3. Computable rational log bounds, zero-constant `π(x)` upper/lower bounds for `x ≥ 10^7`,
   `θ(10^7)` integral pinning, and exact finite Abel summation for `∑_{L < p ≤ U} 1/p`.
4. Multi-resolution prime tables up to `14,090,240` verified in `PLift` batches, packed
   20-bit `Nat` lookup tables, Zelinsky's disjoint generator cover on `[4096, 14,090,240]`,
   and zero-calculus lower bounds on `π(x)` over `[101, 10^7]` and `[2000, 10^7]`.
5. Disjoint refactorable families `G1` (`k ≤ 200,000`, 14 buckets) and `G4` (`m ≤ 10,000`,
   5 groups) verified across 430 continuous intervals on `[14,090,240, 10^32]` and a
   constant-cutoff asymptotic tail on `[10^32, ∞)`.
-/


/- ===================== Mod1_Chebyshev.lean ===================== -/

/-
Module 1: Elementary periodic Chebyshev-Sylvester bounds (`D = 2520`) for `ψ` and `θ`.
-/

namespace ColtonChebyshev

open Finset Real Chebyshev ArithmeticFunction

/- ### Part 1: Elementary logarithm bounds (`log 2, log 3, log 5, log 7, log 50`) -/

private lemma log_seven_bounds :
    (1.945910148 : ℝ) < Real.log 7 ∧ Real.log 7 < 1.945910150 := by
  have h1 := Real.abs_log_sub_add_sum_range_le (x := (1 / 8 : ℝ)) (by norm_num) 10
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1
  norm_num at h1
  have hlog7 : Real.log 7 = 3 * Real.log 2 + Real.log (7 / 8) := by
    have hmul : (7 : ℝ) = (2 : ℝ) ^ (3 : ℕ) * (7 / 8) := by norm_num
    rw [hmul, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    norm_num
  rw [abs_le] at h1
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  constructor <;> linarith

private lemma log_le_quarter_rpow {x : ℝ} (hx : 0 < x) :
    Real.log x ≤ (4 / 50 : ℝ) * x ^ ((1 : ℝ) / 4) + 11.65 := by
  have h50 : Real.log 50 < 3.9125 := by
    have hmul : (50 : ℝ) = 2 * 5 ^ (2 : ℕ) := by norm_num
    rw [hmul, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    have := Real.log_two_lt_d9
    have := Real.log_five_lt_d9
    norm_num at *
    linarith
  have hy : 0 < x ^ ((1 : ℝ) / 4) / 50 := by positivity
  have hsub := Real.log_le_sub_one_of_pos hy
  rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hx] at hsub
  linarith

/- ### Part 2: Stirling's elementary bound for `T(x) = ∑_{1 ≤ m ≤ ⌊x⌋} log m` -/

noncomputable def T (x : ℝ) : ℝ := ∑ m ∈ Icc 1 ⌊x⌋₊, Real.log m

private lemma T_nat_bounds {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) * Real.log n - n + 1 ≤ T n ∧
    T n ≤ (n : ℝ) * Real.log n - n + 1 + Real.log n := by
  have hT (k : ℕ) : T k = ∑ m ∈ Icc 1 k, Real.log m := by
    simp [T]
  rw [hT]
  induction n, hn using Nat.le_induction with
  | base =>
    simp
  | succ k hk ih =>
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hk1_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    rw [sum_Icc_succ_top (by omega : 1 ≤ k + 1)]
    push_cast
    constructor
    · have h1 : Real.log (((k : ℝ) + 1) / k) ≤ ((k : ℝ) + 1) / k - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div hk1_pos.ne' hk_pos.ne'] at h1
      have h2 : (k : ℝ) * (Real.log ((k : ℝ) + 1) - Real.log k) ≤ 1 := by
        have hmul := mul_le_mul_of_nonneg_left h1 hk_pos.le
        have : (k : ℝ) * (((k : ℝ) + 1) / k - 1) = 1 := by field_simp; ring
        linarith
      linarith [ih.1]
    · have h1 : Real.log ((k : ℝ) / ((k : ℝ) + 1)) ≤ (k : ℝ) / ((k : ℝ) + 1) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      rw [Real.log_div hk_pos.ne' hk1_pos.ne'] at h1
      have h2 : ((k : ℝ) + 1) * (Real.log k - Real.log ((k : ℝ) + 1)) ≤ -1 := by
        have hmul := mul_le_mul_of_nonneg_left h1 hk1_pos.le
        have : ((k : ℝ) + 1) * ((k : ℝ) / ((k : ℝ) + 1) - 1) = -1 := by field_simp; ring
        linarith
      linarith [ih.2]

private lemma T_stirling {x : ℝ} (hx : 1 ≤ x) :
    |T x - (x * Real.log x - x + 1)| ≤ Real.log x := by
  set n : ℕ := ⌊x⌋₊
  have hn1 : 1 ≤ n := (Nat.one_le_floor_iff x).mpr hx
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hx_pos : (0 : ℝ) < x := by linarith
  have hnx : (n : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxn1 : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hTn : T x = T n := by simp [T, n]
  obtain ⟨hlo, hhi⟩ := T_nat_bounds hn1
  rw [hTn]
  have hlogN_nonneg : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hlogx_nonneg : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlogN_le : Real.log n ≤ Real.log x := Real.log_le_log hn_pos hnx
  -- f(n) ≤ f(x) via log(n/x) ≤ n/x - 1
  have hf_le : (n : ℝ) * Real.log n - n + 1 ≤ x * Real.log x - x + 1 := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < (n : ℝ) / x by positivity)
    rw [Real.log_div hn_pos.ne' hx_pos.ne'] at h1
    have h2 : x * (Real.log n - Real.log x) ≤ (n : ℝ) - x := by
      have hmul := mul_le_mul_of_nonneg_left h1 hx_pos.le
      have : x * ((n : ℝ) / x - 1) = (n : ℝ) - x := by field_simp
      linarith
    have h3 : (x - n) * Real.log n ≥ 0 := mul_nonneg (by linarith) hlogN_nonneg
    nlinarith
  -- f(x) - f(n) ≤ log x via log(x/n) ≤ x/n - 1
  have hf_diff : (x * Real.log x - x + 1) - ((n : ℝ) * Real.log n - n + 1) ≤ Real.log x := by
    have h1 := Real.log_le_sub_one_of_pos (show 0 < x / n by positivity)
    rw [Real.log_div hx_pos.ne' hn_pos.ne'] at h1
    have h2 : (n : ℝ) * (Real.log x - Real.log n) ≤ x - n := by
      have hmul := mul_le_mul_of_nonneg_left h1 hn_pos.le
      have : (n : ℝ) * (x / n - 1) = x - n := by field_simp
      linarith
    have h3 : (x - n) * Real.log x ≤ 1 * Real.log x :=
      mul_le_mul_of_nonneg_right (by linarith) hlogx_nonneg
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/- ### Part 3: The Chebyshev identity `T(x) = ∑_{k=1}^{⌊x⌋} ψ(x/k)` and Abel summation -/

private lemma floor_div_natCast_eq {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    ⌊x / (k : ℝ)⌋₊ = ⌊x⌋₊ / k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hk_pos : 0 < k := Nat.pos_of_ne_zero hk
  have hk_posR : (0 : ℝ) < k := by exact_mod_cast hk_pos
  apply le_antisymm
  · rw [Nat.le_div_iff_mul_le hk_pos]
    have h1 : (⌊x / (k : ℝ)⌋₊ : ℝ) ≤ x / k := Nat.floor_le (by positivity)
    have h2 : ((⌊x / (k : ℝ)⌋₊ * k : ℕ) : ℝ) ≤ x := by
      push_cast
      exact (le_div_iff₀ hk_posR).mp h1
    exact Nat.le_floor h2
  · apply Nat.le_floor
    rw [le_div_iff₀ hk_posR]
    calc ((⌊x⌋₊ / k : ℕ) : ℝ) * k = ((⌊x⌋₊ / k * k : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast Nat.div_mul_le_self ⌊x⌋₊ k
      _ ≤ x := Nat.floor_le hx

private lemma T_eq_sum_psi {x : ℝ} (hx : 0 ≤ x) :
    T x = ∑ k ∈ Icc 1 ⌊x⌋₊, ψ (x / k) := by
  set N := ⌊x⌋₊
  have h1 : T x = ∑ m ∈ Icc 1 N, ∑ d ∈ m.divisors, Λ d := by
    unfold T
    refine sum_congr rfl fun m _ => ?_
    exact vonMangoldt_sum.symm
  have h2 : ∑ m ∈ Icc 1 N, ∑ d ∈ m.divisors, Λ d =
      ∑ k ∈ Icc 1 N, ∑ d ∈ Icc 1 (N / k), Λ d := by
    rw [Finset.sum_sigma' (Icc 1 N) (fun m => m.divisors) (fun _ d => Λ d),
        Finset.sum_sigma' (Icc 1 N) (fun k => Icc 1 (N / k)) (fun _ d => Λ d)]
    refine sum_bij (fun p _ => ⟨p.1 / p.2, p.2⟩) ?_ ?_ ?_ ?_
    · rintro ⟨m, d⟩ hp
      simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at hp ⊢
      obtain ⟨⟨hm1, hmN⟩, hdvd, hm0⟩ := hp
      have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
      have hq_pos : 0 < m / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd_pos
      have hqN : m / d ≤ N := (Nat.div_le_self m d).trans hmN
      have hdq : d ≤ N / (m / d) := by
        rw [Nat.le_div_iff_mul_le hq_pos]
        have : d * (m / d) = m := Nat.mul_div_cancel' hdvd
        omega
      exact ⟨⟨hq_pos, hqN⟩, ⟨hd_pos, hdq⟩⟩
    · rintro ⟨m₁, d₁⟩ hp₁ ⟨m₂, d₂⟩ hp₂ heq
      simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
      obtain ⟨hq, rfl⟩ := heq
      simp only [mem_sigma, mem_Icc, Nat.mem_divisors] at hp₁ hp₂
      have hm1 : m₁ = d₁ * (m₁ / d₁) := (Nat.mul_div_cancel' hp₁.2.1).symm
      have hm2 : m₂ = d₁ * (m₂ / d₁) := (Nat.mul_div_cancel' hp₂.2.1).symm
      have hm : m₁ = m₂ := by rw [hm1, hm2, hq]
      subst hm; rfl
    · rintro ⟨k, d⟩ hp
      simp only [mem_sigma, mem_Icc] at hp
      obtain ⟨⟨hk1, hkN⟩, ⟨hd1, hdk⟩⟩ := hp
      have hkdN : k * d ≤ N := by
        have := (Nat.le_div_iff_mul_le (by omega : 0 < k)).mp hdk
        linarith
      have hkd1 : 1 ≤ k * d := Nat.one_le_iff_ne_zero.mpr (by positivity)
      refine ⟨⟨k * d, d⟩, ?_, ?_⟩
      · simp only [mem_sigma, mem_Icc, Nat.mem_divisors]
        exact ⟨⟨hkd1, hkdN⟩, dvd_mul_left d k, by omega⟩
      · simp [Nat.mul_div_cancel _ (by omega : 0 < d)]
    · rintro ⟨m, d⟩ _
      rfl
  rw [h1, h2]
  refine sum_congr rfl fun k _ => ?_
  rw [psi_eq_sum_Icc, floor_div_natCast_eq hx k]
  have hIcc : Icc 0 (N / k) = insert 0 (Icc 1 (N / k)) := by
    ext n; simp only [mem_Icc, mem_insert]
    have : 0 ≤ N / k := Nat.zero_le _
    omega
  rw [hIcc, Finset.sum_insert (by simp)]
  simp

private lemma T_div_eq_sum_dvd {x : ℝ} (hx : 0 ≤ x) {d : ℕ} (hd : 0 < d) :
    T (x / d) = ∑ k ∈ (Icc 1 ⌊x⌋₊).filter (fun k => d ∣ k), ψ (x / k) := by
  rw [T_eq_sum_psi (by positivity), floor_div_natCast_eq hx d]
  refine sum_bij (fun m _ => d * m) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [mem_Icc, mem_filter] at hm ⊢
    have hdm : d * m ≤ ⌊x⌋₊ := by
      have := (Nat.le_div_iff_mul_le hd).mp hm.2
      linarith
    exact ⟨⟨by nlinarith, hdm⟩, dvd_mul_right d m⟩
  · intro m₁ _ m₂ _ h
    exact Nat.eq_of_mul_eq_mul_left hd h
  · intro k hk
    simp only [mem_filter, mem_Icc] at hk
    obtain ⟨⟨hk1, hkN⟩, m, rfl⟩ := hk
    have hm1 : 1 ≤ m := by
      by_contra h
      have : m = 0 := by omega
      subst this; omega
    have hmN : m ≤ ⌊x⌋₊ / d := (Nat.le_div_iff_mul_le hd).mpr (by linarith)
    exact ⟨m, mem_Icc.mpr ⟨hm1, hmN⟩, rfl⟩
  · intro m _
    push_cast
    rw [div_div]

private lemma abel_sum_Icc (h a : ℕ → ℝ) (N : ℕ) (h0 : h 0 = 0) (ha : a (N + 1) = 0) :
    ∑ k ∈ Icc 1 N, (h k - h (k - 1)) * a k =
      ∑ k ∈ Icc 1 N, h k * (a k - a (k + 1)) := by
  have aux : ∀ M, ∑ k ∈ Icc 1 M, (h k - h (k - 1)) * a k =
      h M * a (M + 1) + ∑ k ∈ Icc 1 M, h k * (a k - a (k + 1)) := by
    intro M
    induction M with
    | zero => simp [h0]
    | succ M ih =>
      rw [sum_Icc_succ_top (by omega : 1 ≤ M + 1),
          sum_Icc_succ_top (by omega : 1 ≤ M + 1), ih]
      simp only [Nat.add_sub_cancel]
      ring
  rw [aux N, ha]
  ring

/- ### Part 4: Periodic `D = 2520` linear combinations -/

private def evalH (L : List (ℕ × ℤ)) (k : ℕ) : ℤ :=
  L.foldl (fun acc p => acc + p.2 * ((k / p.1 : ℕ) : ℤ)) 0

private lemma evalH_cons_aux (L : List (ℕ × ℤ)) (k : ℕ) (init : ℤ) :
    L.foldl (fun acc p => acc + p.2 * ((k / p.1 : ℕ) : ℤ)) init =
      init + L.foldl (fun acc p => acc + p.2 * ((k / p.1 : ℕ) : ℤ)) 0 := by
  induction L generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, zero_add]
    rw [ih (init + x.2 * ((k / x.1 : ℕ) : ℤ)), ih (x.2 * ((k / x.1 : ℕ) : ℤ))]
    ring

private lemma evalH_eq_sum (L : List (ℕ × ℤ)) (k : ℕ) :
    evalH L k = (L.map (fun p => p.2 * ((k / p.1 : ℕ) : ℤ))).sum := by
  unfold evalH
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, zero_add]
    rw [evalH_cons_aux, ih]

private lemma evalH_zero (L : List (ℕ × ℤ)) : evalH L 0 = 0 := by
  rw [evalH_eq_sum]
  induction L with
  | nil => simp
  | cons x xs ih => simp

private lemma evalH_sub_pred (L : List (ℕ × ℤ)) (hpos : ∀ p ∈ L, 0 < p.1)
    {k : ℕ} (hk : 1 ≤ k) :
    evalH L k - evalH L (k - 1) =
      (L.map (fun p => if p.1 ∣ k then p.2 else 0)).sum := by
  rw [evalH_eq_sum, evalH_eq_sum]
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    have hxpos : 0 < x.1 := hpos x (List.mem_cons_self ..)
    have hxs := ih (fun p hp => hpos p (List.mem_cons_of_mem _ hp))
    have hdiv : ((k / x.1 : ℕ) : ℤ) - (((k - 1) / x.1 : ℕ) : ℤ) =
        if x.1 ∣ k then 1 else 0 := by
      split_ifs with hd
      · have hstep : k / x.1 = (k - 1) / x.1 + 1 := by
          obtain ⟨q, rfl⟩ := hd
          cases q with
          | zero => simp at hk
          | succ q' =>
            have h1 : (x.1 * (q' + 1)) / x.1 = q' + 1 := Nat.mul_div_cancel_left (q' + 1) hxpos
            have heq : x.1 * (q' + 1) - 1 = x.1 * q' + (x.1 - 1) := by
              rw [Nat.mul_succ]; omega
            have h2 : (x.1 * (q' + 1) - 1) / x.1 = q' := by
              rw [heq, Nat.mul_add_div hxpos, Nat.div_eq_of_lt (by omega : x.1 - 1 < x.1)]
              omega
            rw [h1, h2]
        omega
      · have hstep : k / x.1 = (k - 1) / x.1 := by
          have hmod : k % x.1 ≠ 0 := fun h => hd (Nat.dvd_of_mod_eq_zero h)
          have hlt : k % x.1 < x.1 := Nat.mod_lt k hxpos
          have h1 : k = x.1 * (k / x.1) + k % x.1 := (Nat.div_add_mod k x.1).symm
          have h2 : k - 1 = x.1 * (k / x.1) + (k % x.1 - 1) := by omega
          rw [h2, Nat.mul_add_div hxpos, Nat.div_eq_of_lt (by omega : k % x.1 - 1 < x.1)]
          omega
        omega
    have hmul : x.2 * ((k / x.1 : ℕ) : ℤ) - x.2 * (((k - 1) / x.1 : ℕ) : ℤ) =
        if x.1 ∣ k then x.2 else 0 := by
      calc x.2 * ((k / x.1 : ℕ) : ℤ) - x.2 * (((k - 1) / x.1 : ℕ) : ℤ)
          = x.2 * (((k / x.1 : ℕ) : ℤ) - (((k - 1) / x.1 : ℕ) : ℤ)) := by ring
        _ = x.2 * (if x.1 ∣ k then 1 else 0) := by rw [hdiv]
        _ = if x.1 ∣ k then x.2 else 0 := by split_ifs <;> ring
    linarith

private lemma evalH_add (L : List (ℕ × ℤ)) (D : ℕ)
    (hdvd : ∀ p ∈ L, 0 < p.1 ∧ p.1 ∣ D) (k : ℕ) :
    evalH L (k + D) = evalH L k + evalH L D := by
  rw [evalH_eq_sum, evalH_eq_sum, evalH_eq_sum]
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    obtain ⟨hxpos, hxd⟩ := hdvd x (List.mem_cons_self ..)
    have hdiv : (k + D) / x.1 = k / x.1 + D / x.1 := by
      obtain ⟨q, rfl⟩ := hxd
      rw [Nat.add_mul_div_left k q hxpos, Nat.mul_div_cancel_left q hxpos]
    have hxs := ih (fun p hp => hdvd p (List.mem_cons_of_mem _ hp))
    rw [hdiv, hxs]
    push_cast
    ring

private lemma evalH_periodic (L : List (ℕ × ℤ)) (D : ℕ)
    (hdvd : ∀ p ∈ L, 0 < p.1 ∧ p.1 ∣ D) (hbal : evalH L D = 0) (k : ℕ) :
    evalH L (k + D) = evalH L k := by
  rw [evalH_add L D hdvd k, hbal, add_zero]

private lemma evalH_mod (L : List (ℕ × ℤ)) (D : ℕ) (_hD : 0 < D)
    (hdvd : ∀ p ∈ L, 0 < p.1 ∧ p.1 ∣ D) (hbal : evalH L D = 0) (k : ℕ) :
    evalH L k = evalH L (k % D) := by
  have h1 : ∀ q, evalH L (k % D + D * q) = evalH L (k % D) := by
    intro q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, evalH_periodic L D hdvd hbal, ih]
  have hdiv : k = k % D + D * (k / D) := by
    have := Nat.div_add_mod k D
    omega
  conv_lhs => rw [hdiv]
  exact h1 (k / D)

private lemma list_sum_T_eq_abel (L : List (ℕ × ℤ)) (hpos : ∀ p ∈ L, 0 < p.1)
    {x : ℝ} (hx : 0 ≤ x) :
    (L.map (fun p => (p.2 : ℝ) * T (x / p.1))).sum =
      ∑ k ∈ Icc 1 ⌊x⌋₊, ((evalH L k : ℝ) * (ψ (x / k) - ψ (x / (k + 1 : ℕ)))) := by
  have hstep : (L.map (fun p => (p.2 : ℝ) * T (x / p.1))).sum =
      ∑ k ∈ Icc 1 ⌊x⌋₊,
        ((L.map (fun p => if p.1 ∣ k then (p.2 : ℝ) else 0)).sum * ψ (x / k)) := by
    induction L with
    | nil => simp
    | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons]
      have hypos : 0 < y.1 := hpos y (List.mem_cons_self ..)
      have hys := ih (fun p hp => hpos p (List.mem_cons_of_mem _ hp))
      rw [hys, T_div_eq_sum_dvd hx hypos, mul_sum, sum_filter]
      rw [← sum_add_distrib]
      refine sum_congr rfl fun k _ => ?_
      split_ifs <;> ring
  rw [hstep]
  have hcast_map : ∀ (L' : List (ℕ × ℤ)) (k : ℕ),
      (((L'.map (fun p => if p.1 ∣ k then p.2 else 0)).sum : ℤ) : ℝ) =
      (L'.map (fun p => if p.1 ∣ k then (p.2 : ℝ) else 0)).sum := by
    intro L' k
    induction L' with
    | nil => simp
    | cons y ys ih =>
      simp only [List.map_cons, List.sum_cons, Int.cast_add, ih]
      split_ifs <;> simp
  have hcongr : ∀ k ∈ Icc 1 ⌊x⌋₊,
      (L.map (fun p => if p.1 ∣ k then (p.2 : ℝ) else 0)).sum * ψ (x / k) =
      ((evalH L k : ℝ) - (evalH L (k - 1) : ℝ)) * ψ (x / k) := by
    intro k hk
    have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
    have hdiff := evalH_sub_pred L hpos hk1
    have hcast : ((evalH L k : ℝ) - (evalH L (k - 1) : ℝ)) =
        (L.map (fun p => if p.1 ∣ k then (p.2 : ℝ) else 0)).sum := by
      rw [← Int.cast_sub, hdiff, hcast_map]
    rw [hcast]
  rw [sum_congr rfl hcongr]
  have h0 : ((evalH L 0 : ℤ) : ℝ) = 0 := by simp [evalH_zero]
  have ha : ψ (x / ((⌊x⌋₊ + 1 : ℕ) : ℝ)) = 0 := by
    apply psi_eq_zero_of_lt_two
    have hlt : x < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by
      push_cast
      exact Nat.lt_floor_add_one x
    have hpos1 : (0 : ℝ) < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by positivity
    have : x / ((⌊x⌋₊ + 1 : ℕ) : ℝ) < 1 := (div_lt_one hpos1).mpr hlt
    linarith
  exact abel_sum_Icc (fun k => (evalH L k : ℝ)) (fun k => ψ (x / k)) ⌊x⌋₊ h0 ha

/- ### Part 5: Stirling linear-combination estimate -/

private def sumC (L : List (ℕ × ℤ)) : ℤ := (L.map (fun p => p.2)).sum

private def l1C (L : List (ℕ × ℤ)) : ℤ := (L.map (fun p => |p.2|)).sum

private lemma list_mul_bal_aux (L : List (ℕ × ℤ)) (D : ℕ)
    (hdvd : ∀ p ∈ L, 0 < p.1 ∧ p.1 ∣ D) :
    (D : ℝ) * (L.map (fun p => (p.2 : ℝ) / p.1)).sum =
      ((L.map (fun p => p.2 * ((D / p.1 : ℕ) : ℤ))).sum : ℝ) := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    obtain ⟨hypos, hyd⟩ := hdvd y (List.mem_cons_self ..)
    have hys := ih (fun p hp => hdvd p (List.mem_cons_of_mem _ hp))
    rw [mul_add, hys]
    congr 1
    have hyposR : (0 : ℝ) < y.1 := by exact_mod_cast hypos
    have hdiv : ((D / y.1 : ℕ) : ℝ) * (y.1 : ℝ) = (D : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hyd
    field_simp
    rw [← hdiv]
    ring

private lemma list_sum_T_stirling (L : List (ℕ × ℤ)) (D : ℕ) (hD : 0 < D)
    (hdvd : ∀ p ∈ L, 0 < p.1 ∧ p.1 ∣ D) (hbal : evalH L D = 0)
    {x : ℝ} (hx : (D : ℝ) ≤ x) :
    |(L.map (fun p => (p.2 : ℝ) * T (x / p.1))).sum -
      ((-(L.map (fun p => ((p.2 : ℝ) / p.1) * Real.log p.1)).sum) * x + (sumC L : ℝ))| ≤
      (l1C L : ℝ) * Real.log x := by
  have hx1 : 1 ≤ x := le_trans (by exact_mod_cast hD) hx
  have hx_pos : 0 < x := by linarith
  have hbal_real : (L.map (fun p => (p.2 : ℝ) / p.1)).sum = 0 := by
    have hbal_eq := evalH_eq_sum L D
    rw [hbal] at hbal_eq
    have hD_pos : (0 : ℝ) < D := by exact_mod_cast hD
    have hmul := list_mul_bal_aux L D hdvd
    rw [← hbal_eq] at hmul
    simp only [Int.cast_zero] at hmul
    exact (mul_eq_zero.mp hmul).resolve_left hD_pos.ne'
  have hmain : (L.map (fun p => (p.2 : ℝ) * ((x / p.1) * Real.log (x / p.1) - x / p.1 + 1))).sum =
      (-(L.map (fun p => ((p.2 : ℝ) / p.1) * Real.log p.1)).sum) * x + (sumC L : ℝ) := by
    have hexpand : ∀ L' : List (ℕ × ℤ), (∀ p ∈ L', 0 < p.1) →
        (L'.map (fun p => (p.2 : ℝ) * ((x / p.1) * Real.log (x / p.1) - x / p.1 + 1))).sum =
        (L'.map (fun p => (p.2 : ℝ) / p.1)).sum * (x * Real.log x - x) -
        (L'.map (fun p => ((p.2 : ℝ) / p.1) * Real.log p.1)).sum * x +
        (sumC L' : ℝ) := by
      intro L' hpos'
      induction L' with
      | nil => simp [sumC]
      | cons y ys ih =>
        have hypos : 0 < y.1 := hpos' y (List.mem_cons_self ..)
        have hyposR : (0 : ℝ) < y.1 := by exact_mod_cast hypos
        have hys := ih (fun p hp => hpos' p (List.mem_cons_of_mem _ hp))
        simp only [List.map_cons, List.sum_cons, sumC, Int.cast_add] at hys ⊢
        rw [hys, Real.log_div hx_pos.ne' hyposR.ne']
        ring
    rw [hexpand L (fun p hp => (hdvd p hp).1), hbal_real]
    ring
  rw [← hmain]
  -- Bound difference term-by-term
  have hdiff : ∀ L' : List (ℕ × ℤ), (∀ p ∈ L', 0 < p.1 ∧ p.1 ≤ D) →
      |(L'.map (fun p => (p.2 : ℝ) * T (x / p.1))).sum -
        (L'.map (fun p => (p.2 : ℝ) * ((x / p.1) * Real.log (x / p.1) - x / p.1 + 1))).sum| ≤
        (l1C L' : ℝ) * Real.log x := by
    intro L' hbd
    induction L' with
    | nil => simp [l1C]
    | cons y ys ih =>
      obtain ⟨hypos, hyD⟩ := hbd y (List.mem_cons_self ..)
      have hys := ih (fun p hp => hbd p (List.mem_cons_of_mem _ hp))
      have hyposR : (0 : ℝ) < y.1 := by exact_mod_cast hypos
      have hy1 : (1 : ℝ) ≤ y.1 := by exact_mod_cast hypos
      have hxy1 : 1 ≤ x / y.1 := by
        rw [one_le_div hyposR]
        exact le_trans (by exact_mod_cast hyD) hx
      have hst := T_stirling hxy1
      have hlog_le : Real.log (x / y.1) ≤ Real.log x := by
        apply Real.log_le_log (by positivity)
        exact div_le_self hx_pos.le hy1
      simp only [List.map_cons, List.sum_cons, l1C, Int.cast_add, Int.cast_abs]
      have hrew : ((y.2 : ℝ) * T (x / y.1) +
            (ys.map (fun p => (p.2 : ℝ) * T (x / p.1))).sum) -
          ((y.2 : ℝ) * ((x / y.1) * Real.log (x / y.1) - x / y.1 + 1) +
            (ys.map (fun p => (p.2 : ℝ) * ((x / p.1) * Real.log (x / p.1) - x / p.1 + 1))).sum) =
          (y.2 : ℝ) * (T (x / y.1) - ((x / y.1) * Real.log (x / y.1) - x / y.1 + 1)) +
          ((ys.map (fun p => (p.2 : ℝ) * T (x / p.1))).sum -
            (ys.map (fun p => (p.2 : ℝ) * ((x / p.1) * Real.log (x / p.1) - x / p.1 + 1))).sum) := by
        ring
      rw [hrew]
      have hterm : |(y.2 : ℝ) * (T (x / y.1) - ((x / y.1) * Real.log (x / y.1) - x / y.1 + 1))| ≤
          |(y.2 : ℝ)| * Real.log x := by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left (hst.trans hlog_le) (abs_nonneg _)
      calc _ ≤ |(y.2 : ℝ) * (T (x / y.1) - ((x / y.1) * Real.log (x / y.1) - x / y.1 + 1))| +
               |(ys.map (fun p => (p.2 : ℝ) * T (x / p.1))).sum -
                 (ys.map (fun p => (p.2 : ℝ) * ((x / p.1) * Real.log (x / p.1) - x / p.1 + 1))).sum| :=
            abs_add_le _ _
        _ ≤ |(y.2 : ℝ)| * Real.log x + (l1C ys : ℝ) * Real.log x := add_le_add hterm hys
        _ = (|(y.2 : ℝ)| + (l1C ys : ℝ)) * Real.log x := by ring
  exact hdiff L (fun p hp => ⟨(hdvd p hp).1, Nat.le_of_dvd hD (hdvd p hp).2⟩)

/- ### Part 6: Concrete `D = 2520` identities for lower and upper `ψ` bounds -/

private def loList : List (ℕ × ℤ) := [
  (1, 2), (2, -2), (3, -2), (5, -2), (6, 2), (7, -2), (12, -2), (14, 2),
  (18, -2), (20, 2), (24, 2), (28, -2), (35, 2), (36, 2), (40, -2), (42, -2),
  (56, 2), (70, -3), (72, -1), (84, 2), (126, 2), (140, 1), (168, -1), (180, -2),
  (210, 4), (252, -4), (280, 2), (360, 2), (420, -3), (504, 2), (630, 1),
  (840, 1), (1260, 3), (2520, 1)
]

private def upList : List (ℕ × ℤ) := [
  (1, 7), (2, -7), (3, -7), (5, -7), (6, 7), (7, -7), (10, 7), (12, -7),
  (14, 2), (15, 5), (18, -7), (20, -2), (21, 2), (28, 5), (30, -12), (36, 7),
  (40, -5), (42, -4), (45, -5), (60, 9), (63, -2), (70, -2), (84, 1), (90, 15),
  (105, -7), (120, 1), (126, 6), (140, 7), (168, -4), (180, -11), (210, 12),
  (252, -10), (280, -4), (315, 8), (420, -6), (504, 7), (630, -8), (840, -3),
  (1260, -7), (2520, -8)
]

private lemma loList_dvd : ∀ p ∈ loList, 0 < p.1 ∧ p.1 ∣ 2520 := by decide +kernel
private lemma loList_bal : evalH loList 2520 = 0 := by decide +kernel
private lemma loList_sumC : sumC loList = 5 := by decide +kernel
private lemma loList_l1C : l1C loList = 69 := by decide +kernel

set_option maxHeartbeats 0 in
private lemma loList_h_le : ∀ k : Fin 2520, evalH loList k.val ≤ 2 := by decide +kernel

private lemma upList_dvd : ∀ p ∈ upList, 0 < p.1 ∧ p.1 ∣ 2520 := by decide +kernel
private lemma upList_bal : evalH upList 2520 = 0 := by decide +kernel
private lemma upList_sumC : sumC upList = -34 := by decide +kernel
private lemma upList_l1C : l1C upList = 250 := by decide +kernel

set_option maxHeartbeats 0 in
private lemma upList_h_nonneg : ∀ k : Fin 2520, 0 ≤ evalH upList k.val := by decide +kernel

set_option maxHeartbeats 0 in
private lemma upList_h_ge_7 : ∀ k : Fin 36, 1 ≤ k.val → 7 ≤ evalH upList k.val := by decide +kernel

-- Helper: computable 2,3,5,7-adic valuations for divisors of 2520
private def vp (p : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n % p = 0 then 1 + vp p fuel (n / p) else 0

private def v2 (n : ℕ) : ℕ := vp 2 10 n
private def v3 (n : ℕ) : ℕ := vp 3 10 n
private def v5 (n : ℕ) : ℕ := vp 5 10 n
private def v7 (n : ℕ) : ℕ := vp 7 10 n

private lemma log_eq_2357 {d : ℕ} (h : d = 2 ^ v2 d * 3 ^ v3 d * 5 ^ v5 d * 7 ^ v7 d) :
    Real.log (d : ℝ) = (v2 d : ℝ) * Real.log 2 + (v3 d : ℝ) * Real.log 3 +
      (v5 d : ℝ) * Real.log 5 + (v7 d : ℝ) * Real.log 7 := by
  have hd : (d : ℝ) = (2 : ℝ) ^ v2 d * (3 : ℝ) ^ v3 d * (5 : ℝ) ^ v5 d * (7 : ℝ) ^ v7 d := by
    exact_mod_cast h
  rw [hd, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow, Real.log_pow]

private lemma coeff_decomp (L : List (ℕ × ℤ))
    (hfac : ∀ p ∈ L, p.1 = 2 ^ v2 p.1 * 3 ^ v3 p.1 * 5 ^ v5 p.1 * 7 ^ v7 p.1) :
    (-(L.map (fun p => ((p.2 : ℝ) / p.1) * Real.log p.1)).sum) =
      (-(L.map (fun p => (p.2 : ℝ) * (v2 p.1 : ℝ) / p.1)).sum) * Real.log 2 +
      (-(L.map (fun p => (p.2 : ℝ) * (v3 p.1 : ℝ) / p.1)).sum) * Real.log 3 +
      (-(L.map (fun p => (p.2 : ℝ) * (v5 p.1 : ℝ) / p.1)).sum) * Real.log 5 +
      (-(L.map (fun p => (p.2 : ℝ) * (v7 p.1 : ℝ) / p.1)).sum) * Real.log 7 := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    have hy := log_eq_2357 (hfac y (List.mem_cons_self ..))
    have hys := ih (fun p hp => hfac p (List.mem_cons_of_mem _ hp))
    simp only [List.map_cons, List.sum_cons] at hys ⊢
    rw [hy]
    have hrew : -((y.2 : ℝ) / y.1 * ((v2 y.1 : ℝ) * Real.log 2 + (v3 y.1 : ℝ) * Real.log 3 +
        (v5 y.1 : ℝ) * Real.log 5 + (v7 y.1 : ℝ) * Real.log 7) +
        (ys.map (fun p => ((p.2 : ℝ) / p.1) * Real.log p.1)).sum) =
      -((y.2 : ℝ) * (v2 y.1 : ℝ) / y.1) * Real.log 2 -
      ((y.2 : ℝ) * (v3 y.1 : ℝ) / y.1) * Real.log 3 -
      ((y.2 : ℝ) * (v5 y.1 : ℝ) / y.1) * Real.log 5 -
      ((y.2 : ℝ) * (v7 y.1 : ℝ) / y.1) * Real.log 7 +
      (-(ys.map (fun p => ((p.2 : ℝ) / p.1) * Real.log p.1)).sum) := by ring
    rw [hrew, hys]
    ring

private lemma loList_fac :
    ∀ p ∈ loList, p.1 = 2 ^ v2 p.1 * 3 ^ v3 p.1 * 5 ^ v5 p.1 * 7 ^ v7 p.1 := by
  decide +kernel

private lemma upList_fac :
    ∀ p ∈ upList, p.1 = 2 ^ v2 p.1 * 3 ^ v3 p.1 * 5 ^ v5 p.1 * 7 ^ v7 p.1 := by
  decide +kernel

private lemma sum_rat_mul_aux (L : List (ℕ × ℤ)) (f : ℕ → ℕ)
    (hdvd : ∀ p ∈ L, 0 < p.1 ∧ p.1 ∣ 2520) :
    (2520 : ℝ) * (L.map (fun p => (p.2 : ℝ) * (f p.1 : ℝ) / p.1)).sum =
      ((L.map (fun p => p.2 * (f p.1 : ℤ) * ((2520 / p.1 : ℕ) : ℤ))).sum : ℝ) := by
  induction L with
  | nil => simp
  | cons y ys ih =>
    obtain ⟨hypos, hyd⟩ := hdvd y (List.mem_cons_self ..)
    have hys := ih (fun p hp => hdvd p (List.mem_cons_of_mem _ hp))
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul, Int.cast_natCast]
    rw [mul_add, hys]
    congr 1
    have hyposR : (0 : ℝ) < y.1 := by exact_mod_cast hypos
    have hdiv : ((2520 / y.1 : ℕ) : ℝ) * (y.1 : ℝ) = 2520 := by
      exact_mod_cast Nat.div_mul_cancel hyd
    field_simp
    rw [← hdiv]
    ring

private lemma sum_rat_eq (L : List (ℕ × ℤ)) (f : ℕ → ℕ)
    (hdvd : ∀ p ∈ L, 0 < p.1 ∧ p.1 ∣ 2520) (val : ℤ)
    (hcheck : (L.map (fun p => p.2 * (f p.1 : ℤ) * ((2520 / p.1 : ℕ) : ℤ))).sum = val) :
    (-(L.map (fun p => (p.2 : ℝ) * (f p.1 : ℝ) / p.1)).sum) = -(val : ℝ) / 2520 := by
  have hmul := sum_rat_mul_aux L f hdvd
  rw [hcheck] at hmul
  linarith

private lemma loList_A_ge :
    (1.88154 : ℝ) ≤ -(loList.map (fun p => ((p.2 : ℝ) / p.1) * Real.log p.1)).sum := by
  rw [coeff_decomp loList loList_fac]
  rw [sum_rat_eq loList v2 loList_dvd (-1646) (by decide +kernel)]
  rw [sum_rat_eq loList v3 loList_dvd (-1428) (by decide +kernel)]
  rw [sum_rat_eq loList v5 loList_dvd (-780) (by decide +kernel)]
  rw [sum_rat_eq loList v7 loList_dvd (-399) (by decide +kernel)]
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  have h5 := Real.log_five_gt_d9
  have h7 := log_seven_bounds.1
  linarith

private lemma upList_A_le :
    -(upList.map (fun p => ((p.2 : ℝ) / p.1) * Real.log p.1)).sum ≤ (7.18550 : ℝ) := by
  rw [coeff_decomp upList upList_fac]
  rw [sum_rat_eq upList v2 upList_dvd (-7624) (by decide +kernel)]
  rw [sum_rat_eq upList v3 upList_dvd (-5316) (by decide +kernel)]
  rw [sum_rat_eq upList v5 upList_dvd (-2155) (by decide +kernel)]
  rw [sum_rat_eq upList v7 upList_dvd (-1806) (by decide +kernel)]
  have h2 := Real.log_two_lt_d9
  have h3 := Real.log_three_lt_d9
  have h5 := Real.log_five_lt_d9
  have h7 := log_seven_bounds.2
  linarith

/- ### Part 7: Main `ψ` and `θ` bounds -/

private lemma psi_div_diff_nonneg {x : ℝ} (hx : 0 ≤ x) (k : ℕ) (hk : 1 ≤ k) :
    0 ≤ ψ (x / k) - ψ (x / (k + 1 : ℕ)) := by
  apply sub_nonneg.mpr
  apply psi_mono
  have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  exact div_le_div_of_nonneg_left hx hk_pos (by exact_mod_cast (show k ≤ k + 1 by omega))

private lemma sum_psi_diff_telescope (x : ℝ) (M : ℕ) :
    ∑ k ∈ Icc 1 M, (ψ (x / k) - ψ (x / (k + 1 : ℕ))) = ψ x - ψ (x / (M + 1 : ℕ)) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_Icc_succ_top (by omega : 1 ≤ M + 1), ih]
    ring

theorem psi_lower {x : ℝ} (hx : 2520 ≤ x) :
    0.94077 * x - 35 * Real.log x ≤ ψ x := by
  have hx0 : 0 ≤ x := by linarith
  have hst := list_sum_T_stirling loList 2520 (by decide) loList_dvd loList_bal hx
  rw [abs_le, loList_sumC, loList_l1C] at hst
  have hlo_A := loList_A_ge
  have hsum_ge : 1.88154 * x - 69 * Real.log x ≤
      (loList.map (fun p => (p.2 : ℝ) * T (x / p.1))).sum := by
    have h1 : 1.88154 * x ≤ (-(loList.map (fun p => ((p.2 : ℝ) / p.1) * Real.log p.1)).sum) * x :=
      mul_le_mul_of_nonneg_right hlo_A hx0
    push_cast at hst
    linarith [hst.1]
  rw [list_sum_T_eq_abel loList (fun p hp => (loList_dvd p hp).1) hx0] at hsum_ge
  have hsum_le : ∑ k ∈ Icc 1 ⌊x⌋₊, ((evalH loList k : ℝ) * (ψ (x / k) - ψ (x / (k + 1 : ℕ)))) ≤
      2 * ψ x := by
    have h1 : ∑ k ∈ Icc 1 ⌊x⌋₊, ((evalH loList k : ℝ) * (ψ (x / k) - ψ (x / (k + 1 : ℕ)))) ≤
        ∑ k ∈ Icc 1 ⌊x⌋₊, (2 : ℝ) * (ψ (x / k) - ψ (x / (k + 1 : ℕ))) := by
      refine sum_le_sum fun k hk => ?_
      have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
      have hdiff := psi_div_diff_nonneg hx0 k hk1
      have hhk : evalH loList k ≤ 2 := by
        rw [evalH_mod loList 2520 (by decide) loList_dvd loList_bal k]
        exact loList_h_le ⟨k % 2520, Nat.mod_lt k (by decide)⟩
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hhk) hdiff
    rw [← mul_sum, sum_psi_diff_telescope] at h1
    have hzero : ψ (x / ((⌊x⌋₊ + 1 : ℕ) : ℝ)) = 0 := by
      apply psi_eq_zero_of_lt_two
      have hlt : x < ((⌊x⌋₊ + 1 : ℕ) : ℝ) := by push_cast; exact Nat.lt_floor_add_one x
      have : x / ((⌊x⌋₊ + 1 : ℕ) : ℝ) < 1 := (div_lt_one (by positivity)).mpr hlt
      linarith
    rw [hzero, sub_zero] at h1
    exact h1
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  linarith

private lemma psi_step_upper {x : ℝ} (hx : 2520 ≤ x) :
    ψ x - ψ (x / 36) ≤ 1.02650 * x + 36 * Real.log x := by
  have hx0 : 0 ≤ x := by linarith
  have hst := list_sum_T_stirling upList 2520 (by decide) upList_dvd upList_bal hx
  rw [abs_le, upList_sumC, upList_l1C] at hst
  have hup_A := upList_A_le
  have hsum_le : (upList.map (fun p => (p.2 : ℝ) * T (x / p.1))).sum ≤
      7.18550 * x + 250 * Real.log x := by
    have h1 : (-(upList.map (fun p => ((p.2 : ℝ) / p.1) * Real.log p.1)).sum) * x ≤ 7.18550 * x :=
      mul_le_mul_of_nonneg_right hup_A hx0
    push_cast at hst
    linarith [hst.2]
  rw [list_sum_T_eq_abel upList (fun p hp => (upList_dvd p hp).1) hx0] at hsum_le
  have hN35 : 35 ≤ ⌊x⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hsum_ge : 7 * (ψ x - ψ (x / 36)) ≤
      ∑ k ∈ Icc 1 ⌊x⌋₊, ((evalH upList k : ℝ) * (ψ (x / k) - ψ (x / (k + 1 : ℕ)))) := by
    have hsub : Icc 1 35 ⊆ Icc 1 ⌊x⌋₊ := Icc_subset_Icc_right hN35
    have hnonneg : ∀ k ∈ Icc 1 ⌊x⌋₊,
        0 ≤ (evalH upList k : ℝ) * (ψ (x / k) - ψ (x / (k + 1 : ℕ))) := by
      intro k hk
      have hk1 : 1 ≤ k := (mem_Icc.mp hk).1
      have hhk : 0 ≤ evalH upList k := by
        rw [evalH_mod upList 2520 (by decide) upList_dvd upList_bal k]
        exact upList_h_nonneg ⟨k % 2520, Nat.mod_lt k (by decide)⟩
      exact mul_nonneg (by exact_mod_cast hhk) (psi_div_diff_nonneg hx0 k hk1)
    calc 7 * (ψ x - ψ (x / 36))
        = 7 * ∑ k ∈ (Icc 1 35 : Finset ℕ), (ψ (x / k) - ψ (x / (k + 1 : ℕ))) := by
          rw [sum_psi_diff_telescope]; norm_num
      _ = ∑ k ∈ (Icc 1 35 : Finset ℕ), (7 : ℝ) * (ψ (x / k) - ψ (x / (k + 1 : ℕ))) := by
          rw [mul_sum]
      _ ≤ ∑ k ∈ (Icc 1 35 : Finset ℕ), ((evalH upList k : ℝ) * (ψ (x / k) - ψ (x / (k + 1 : ℕ)))) := by
          refine sum_le_sum fun k hk => ?_
          obtain ⟨hk1, hk35⟩ := mem_Icc.mp hk
          have hhk : 7 ≤ evalH upList k := upList_h_ge_7 ⟨k, by omega⟩ hk1
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hhk) (psi_div_diff_nonneg hx0 k hk1)
      _ ≤ ∑ k ∈ Icc 1 ⌊x⌋₊, ((evalH upList k : ℝ) * (ψ (x / k) - ψ (x / (k + 1 : ℕ)))) :=
          sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => hnonneg k hk
  have hlog_nonneg : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  linarith

theorem psi_upper {x : ℝ} (hx : 1 ≤ x) :
    ψ x ≤ 1.05583 * x + 7 * (Real.log x) ^ 2 + 1700 := by
  -- Strong induction on ⌊x⌋₊
  suffices h : ∀ N : ℕ, ∀ y : ℝ, 1 ≤ y → ⌊y⌋₊ ≤ N →
      ψ y ≤ 1.05583 * y + 7 * (Real.log y) ^ 2 + 1700 from
    h ⌊x⌋₊ x hx le_rfl
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
    intro y hy1 hyN
    by_cases hy2520 : y < 2520
    · -- Base case: 1 ≤ y < 2520 via Chebyshev.psi_le
      have hpsi := Chebyshev.psi_le hy1
      have hlog4 : Real.log 4 < 1.3863 := by
        rw [Real.log_four_eq]
        linarith [Real.log_two_lt_d9]
      have hsqrt : Real.sqrt y ≤ 51 := by
        have : y ≤ 51 ^ 2 := by linarith
        exact (Real.sqrt_le_sqrt this).trans (by norm_num)
      have hlog2520 : Real.log y ≤ 7.84 := by
        have h1 : Real.log y ≤ Real.log 2520 := Real.log_le_log (by linarith) hy2520.le
        have h2 : (2520 : ℝ) = 2 ^ 3 * 3 ^ 2 * 5 * 7 := by norm_num
        have h3 : Real.log 2520 = 3 * Real.log 2 + 2 * Real.log 3 + Real.log 5 + Real.log 7 := by
          rw [h2, Real.log_mul (by positivity) (by norm_num),
              Real.log_mul (by positivity) (by norm_num),
              Real.log_mul (by positivity) (by positivity),
              Real.log_pow, Real.log_pow]
          push_cast; ring
        have := Real.log_two_lt_d9
        have := Real.log_three_lt_d9
        have := Real.log_five_lt_d9
        have := log_seven_bounds.2
        linarith
      have hsqrt_nonneg : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
      have hlog_nonneg : 0 ≤ Real.log y := Real.log_nonneg hy1
      have hterm1 : (Real.log 4 - 1.05583) * y ≤ (1.3863 - 1.05583) * 2520 := by
        nlinarith
      have hterm2 : 2 * Real.sqrt y * Real.log y ≤ 2 * 51 * 7.84 := by
        nlinarith
      have hsq_nonneg : 0 ≤ 7 * (Real.log y) ^ 2 := by positivity
      linarith
    · -- Inductive step: y ≥ 2520
      push Not at hy2520
      have hstep := psi_step_upper hy2520
      have hy36_ge : 1 ≤ y / 36 := by linarith
      have hfloor_lt : ⌊y / 36⌋₊ < N := by
        have h1 : (⌊y / 36⌋₊ : ℝ) ≤ y / 36 := Nat.floor_le (by linarith)
        have h2 : (⌊y⌋₊ : ℝ) > y - 1 := Nat.sub_one_lt_floor y
        have h3 : (⌊y / 36⌋₊ : ℝ) < (⌊y⌋₊ : ℝ) := by linarith
        have h4 : ⌊y / 36⌋₊ < ⌊y⌋₊ := by exact_mod_cast h3
        omega
      have hih := ih ⌊y / 36⌋₊ hfloor_lt (y / 36) hy36_ge le_rfl
      rw [Real.log_div (by linarith) (by norm_num)] at hih
      have hlog36_lo : (3.5835 : ℝ) < Real.log 36 := by
        have h36 : (36 : ℝ) = 2 ^ 2 * 3 ^ 2 := by norm_num
        rw [h36, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
        push_cast
        linarith [Real.log_two_gt_d9, Real.log_three_gt_d9]
      have hlog36_hi : Real.log 36 < (3.5836 : ℝ) := by
        have h36 : (36 : ℝ) = 2 ^ 2 * 3 ^ 2 := by norm_num
        rw [h36, Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
        push_cast
        linarith [Real.log_two_lt_d9, Real.log_three_lt_d9]
      have hlogy_ge : (7.83 : ℝ) < Real.log y := by
        have h1 : Real.log 2520 ≤ Real.log y := Real.log_le_log (by norm_num) hy2520
        have h2 : (2520 : ℝ) = 2 ^ 3 * 3 ^ 2 * 5 * 7 := by norm_num
        have h3 : Real.log 2520 = 3 * Real.log 2 + 2 * Real.log 3 + Real.log 5 + Real.log 7 := by
          rw [h2, Real.log_mul (by positivity) (by norm_num),
              Real.log_mul (by positivity) (by norm_num),
              Real.log_mul (by positivity) (by positivity),
              Real.log_pow, Real.log_pow]
          push_cast; ring
        have := Real.log_two_gt_d9
        have := Real.log_three_gt_d9
        have := Real.log_five_gt_d9
        have := log_seven_bounds.1
        linarith
      -- 7 * (log y - log 36)^2 + 36 * log y ≤ 7 * (log y)^2
      have hlog_ineq : 7 * (Real.log y - Real.log 36) ^ 2 + 36 * Real.log y ≤
          7 * (Real.log y) ^ 2 := by
        nlinarith
      linarith

private lemma rpow_le_div_const {x c : ℝ} {a : ℝ} (hx : 0 < x) (hc : 0 < c)
    (h : c ≤ x ^ (1 - a)) : x ^ a ≤ x / c := by
  rw [le_div_iff₀ hc]
  calc x ^ a * c ≤ x ^ a * x ^ (1 - a) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = x ^ (a + (1 - a)) := (Real.rpow_add hx a (1 - a)).symm
    _ = x := by norm_num

private lemma rpow_bounds_10M {x : ℝ} (hx : (10 ^ 7 : ℝ) ≤ x) :
    x ^ ((1 : ℝ) / 2) ≤ x / 3162 ∧
    x ^ ((1 : ℝ) / 3) ≤ x / 46415 ∧
    x ^ ((1 : ℝ) / 4) ≤ x / 177827 ∧
    x ^ ((1 : ℝ) / 5) ≤ x / 398107 := by
  have hx0 : 0 < x := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply rpow_le_div_const hx0 (by norm_num)
    have h1 : (3162 : ℝ) ^ (2 : ℝ) ≤ x := by norm_num; linarith
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 2)
    rw [← Real.rpow_mul (by norm_num)] at h2
    norm_num at h2 ⊢; linarith
  · apply rpow_le_div_const hx0 (by norm_num)
    have h1 : (46415 : ℝ) ^ (3 : ℝ) ≤ x ^ (2 : ℝ) := by
      have hsq : ((10 ^ 7 : ℝ)) ^ (2 : ℝ) ≤ x ^ (2 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hx (by norm_num)
      have hnum : (46415 : ℝ) ^ (3 : ℝ) ≤ ((10 ^ 7 : ℝ)) ^ (2 : ℝ) := by norm_num
      linarith
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 3)
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul hx0.le] at h2
    norm_num at h2 ⊢; linarith
  · apply rpow_le_div_const hx0 (by norm_num)
    have h1 : (177827 : ℝ) ^ (4 : ℝ) ≤ x ^ (3 : ℝ) := by
      have hcb : ((10 ^ 7 : ℝ)) ^ (3 : ℝ) ≤ x ^ (3 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hx (by norm_num)
      have hnum : (177827 : ℝ) ^ (4 : ℝ) ≤ ((10 ^ 7 : ℝ)) ^ (3 : ℝ) := by norm_num
      linarith
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 4)
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul hx0.le] at h2
    norm_num at h2 ⊢; linarith
  · apply rpow_le_div_const hx0 (by norm_num)
    have h1 : (398107 : ℝ) ^ (5 : ℝ) ≤ x ^ (4 : ℝ) := by
      have h4 : ((10 ^ 7 : ℝ)) ^ (4 : ℝ) ≤ x ^ (4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hx (by norm_num)
      have hnum : (398107 : ℝ) ^ (5 : ℝ) ≤ ((10 ^ 7 : ℝ)) ^ (4 : ℝ) := by norm_num
      linarith
    have h2 := Real.rpow_le_rpow (by positivity) h1 (by norm_num : (0 : ℝ) ≤ 1 / 5)
    rw [← Real.rpow_mul (by norm_num), ← Real.rpow_mul hx0.le] at h2
    norm_num at h2 ⊢; linarith

theorem theta_upper_10M {x : ℝ} (hx : (10 ^ 7 : ℝ) ≤ x) :
    θ x ≤ 1.0562 * x := by
  have hx0 : 0 < x := by linarith
  have h1 := (theta_le_psi x).trans (psi_upper (by linarith))
  have hlog := log_le_quarter_rpow hx0
  have hlog_nn : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hsq : (Real.log x) ^ 2 ≤ ((4 / 50 : ℝ) * x ^ ((1 : ℝ) / 4) + 11.65) ^ 2 :=
    pow_le_pow_left₀ hlog_nn hlog 2
  have hqsq : (x ^ ((1 : ℝ) / 4)) ^ 2 = x ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  obtain ⟨hr2, _, hr4, _⟩ := rpow_bounds_10M hx
  have hsq_exp : ((4 / 50 : ℝ) * x ^ ((1 : ℝ) / 4) + 11.65) ^ 2 =
      (16 / 2500 : ℝ) * x ^ ((1 : ℝ) / 2) + (93.2 / 50 : ℝ) * x ^ ((1 : ℝ) / 4) + 135.7225 := by
    calc _ = (16 / 2500 : ℝ) * (x ^ ((1 : ℝ) / 4)) ^ 2 +
              (93.2 / 50 : ℝ) * x ^ ((1 : ℝ) / 4) + 135.7225 := by ring
      _ = _ := by rw [hqsq]
  linarith

theorem theta_lower_10M {x : ℝ} (hx : (10 ^ 7 : ℝ) ≤ x) :
    0.9400 * x ≤ θ x := by
  have hx0 : 0 < x := by linarith
  have hpsi := psi_lower (by linarith : 2520 ≤ x)
  have hdiff := Chebyshev.psi_sub_theta_le_psi_add_psi_add_psi x
  have hlog4 : Real.log 4 < 1.387 := by
    rw [Real.log_four_eq]; linarith [Real.log_two_lt_d9]
  -- Bound ψ(x^(1/2)) via Chebyshev.psi_le
  have hx2_ge1 : 1 ≤ x ^ ((1 : ℝ) / 2) := Real.one_le_rpow (by linarith) (by norm_num)
  have hpsi2 := Chebyshev.psi_le hx2_ge1
  have hsqrt2 : Real.sqrt (x ^ ((1 : ℝ) / 2)) = x ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hx0.le]; norm_num
  have hlog2 : Real.log (x ^ ((1 : ℝ) / 2)) = (1 / 2 : ℝ) * Real.log x := by
    rw [Real.log_rpow hx0]
  rw [hsqrt2, hlog2] at hpsi2
  have hlog_bound := log_le_quarter_rpow hx0
  have hq_nn : 0 ≤ x ^ ((1 : ℝ) / 4) := by positivity
  have hq_mul_log : x ^ ((1 : ℝ) / 4) * Real.log x ≤
      (4 / 50 : ℝ) * x ^ ((1 : ℝ) / 2) + 11.65 * x ^ ((1 : ℝ) / 4) := by
    have hqsq : x ^ ((1 : ℝ) / 4) * x ^ ((1 : ℝ) / 4) = x ^ ((1 : ℝ) / 2) := by
      rw [← Real.rpow_add hx0]; norm_num
    have hmul := mul_le_mul_of_nonneg_left hlog_bound hq_nn
    linarith
  have hpsi2' : ψ (x ^ ((1 : ℝ) / 2)) ≤
      (1.387 + 4 / 50) * x ^ ((1 : ℝ) / 2) + 11.65 * x ^ ((1 : ℝ) / 4) := by
    have h1 : Real.log 4 * x ^ ((1 : ℝ) / 2) ≤ 1.387 * x ^ ((1 : ℝ) / 2) :=
      mul_le_mul_of_nonneg_right hlog4.le (by positivity)
    linarith
  -- Bound ψ(x^(1/3)) and ψ(x^(1/5)) via Chebyshev.psi_le_const_mul_self
  have hpsi3 : ψ (x ^ ((1 : ℝ) / 3)) ≤ 5.39 * x ^ ((1 : ℝ) / 3) := by
    have h := Chebyshev.psi_le_const_mul_self (x := x ^ ((1 : ℝ) / 3)) (by positivity)
    have : (Real.log 4 + 4) * x ^ ((1 : ℝ) / 3) ≤ 5.39 * x ^ ((1 : ℝ) / 3) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  have hpsi5 : ψ (x ^ ((1 : ℝ) / 5)) ≤ 5.39 * x ^ ((1 : ℝ) / 5) := by
    have h := Chebyshev.psi_le_const_mul_self (x := x ^ ((1 : ℝ) / 5)) (by positivity)
    have : (Real.log 4 + 4) * x ^ ((1 : ℝ) / 5) ≤ 5.39 * x ^ ((1 : ℝ) / 5) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    linarith
  obtain ⟨hr2, hr3, hr4, hr5⟩ := rpow_bounds_10M hx
  have hdiff' : ψ x - θ x ≤
      (1.387 + 4 / 50) * x ^ ((1 : ℝ) / 2) + 11.65 * x ^ ((1 : ℝ) / 4) +
      5.39 * x ^ ((1 : ℝ) / 3) + 5.39 * x ^ ((1 : ℝ) / 5) := by
    have h2 : x ^ ((2 : ℝ)⁻¹) = x ^ ((1 : ℝ) / 2) := by norm_num
    have h3 : x ^ ((3 : ℝ)⁻¹) = x ^ ((1 : ℝ) / 3) := by norm_num
    have h5 : x ^ ((5 : ℝ)⁻¹) = x ^ ((1 : ℝ) / 5) := by norm_num
    rw [h2, h3, h5] at hdiff
    linarith
  linarith

end ColtonChebyshev


/- ===================== Mod2A_SieveCore.lean ===================== -/

/-
Module 2A: Kernel-reducible width-1 segmented bitset sieve, SWAR popcount,
exact small prime counter up to 8192, fast trial-factorization (`fastTauTop`),
and base verification of Colton's conjecture through 4096.
-/

namespace ColtonSieve

open Finset

def pulses (step len : Nat) : Nat :=
  ((2 ^ step) ^ len - 1) / (2 ^ step - 1)

lemma pulses_succ {step : Nat} (hs : 0 < step) (len : Nat) :
    pulses step (len + 1) = (pulses step len <<< step) ||| 1 := by
  have hbase : 2 ≤ (2 : Nat) ^ step := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (show 1 ≤ step by omega)
  unfold pulses
  rw [← Nat.geomSum_eq hbase, ← Nat.geomSum_eq hbase, geom_sum_succ]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (show 1 < (2 : Nat) ^ step by omega)]
  rw [Nat.shiftLeft_eq, Nat.mul_comm]

theorem pulses_bit {step : Nat} (hs : 0 < step) (len i : Nat) :
    (pulses step len).testBit i = true ↔ ∃ j < len, i = step * j := by
  induction len generalizing i with
  | zero => simp [pulses]
  | succ len ih =>
    rw [pulses_succ hs, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true,
      Bool.and_eq_true, decide_eq_true_eq, ih, Nat.testBit_one_eq_true_iff_self_eq_zero]
    constructor
    · rintro (⟨hi, j, hj, h⟩ | rfl)
      · refine ⟨j + 1, by omega, ?_⟩
        rw [Nat.mul_succ]; omega
      · exact ⟨0, by omega, by simp⟩
    · rintro ⟨j, hj, h⟩
      cases j with
      | zero => exact Or.inr (by simpa using h)
      | succ j =>
        rw [Nat.mul_succ] at h
        exact Or.inl ⟨by omega, j, by omega, by omega⟩

lemma pulses_lt (step len : Nat) : pulses step len < 2 ^ (step * len) := by
  unfold pulses
  rw [Nat.pow_mul]
  have hp : 0 < (2 ^ step : Nat) ^ len := by positivity
  exact (Nat.div_le_self _ _).trans_lt (by omega)

def phase (lo p : Nat) : Nat := p * ((lo + p - 1) / p) - lo

lemma phase_bounds {p : Nat} (hp : 0 < p) (lo : Nat) :
    phase lo p < p ∧ p ∣ lo + phase lo p := by
  have hmod := Nat.mod_lt (lo + p - 1) hp
  have hdiv := Nat.mod_add_div (lo + p - 1) p
  unfold phase
  constructor
  · omega
  · refine ⟨(lo + p - 1) / p, ?_⟩; omega

lemma divides_phase {p : Nat} (hp : 0 < p) (lo i : Nat) :
    p ∣ lo + i ↔ ∃ j, i = phase lo p + p * j := by
  have ⟨hbound, q, hq⟩ := phase_bounds hp lo
  constructor
  · rintro ⟨r, hr⟩
    have hqr : q ≤ r := by
      by_contra h
      push Not at h
      have hm := Nat.mul_le_mul_left p (show r + 1 ≤ q by omega)
      rw [Nat.mul_succ] at hm; omega
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hqr
    rw [Nat.mul_add] at hr
    exact ⟨j, by omega⟩
  · rintro ⟨j, rfl⟩
    refine ⟨q + j, ?_⟩
    rw [Nat.mul_add]; omega

def progressionMask (lo len p : Nat) : Nat :=
  pulses p (len / p + 1) <<< phase lo p

lemma progression_bit {p : Nat} (hp : 0 < p) (lo len i : Nat) (hi : i < len) :
    (progressionMask lo len p).testBit i = true ↔ p ∣ lo + i := by
  rw [progressionMask, Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq,
    pulses_bit hp, divides_phase hp]
  constructor
  · rintro ⟨hle, j, _, he⟩
    exact ⟨j, by omega⟩
  · rintro ⟨j, rfl⟩
    have hj : j < len / p + 1 := by
      have h : p * j ≤ len := by omega
      exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hp).mpr (by simpa [Nat.mul_comm] using h))
    exact ⟨Nat.le_add_right _ _, j, hj, by omega⟩

def primesLe64 : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61]

private def eligible3760 : List Nat :=
  (List.range 3761).filter (fun p => decide (2 ≤ p ∧ (p ∈ primesLe64 ∨ Nat.Coprime p (Nat.factorial 64))))

def primes3760 : List Nat := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
  67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
  157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
  257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359,
  367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463,
  467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593,
  599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701,
  709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827,
  829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953,
  967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069,
  1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213,
  1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321,
  1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481,
  1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579, 1583, 1597, 1601,
  1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693, 1697, 1699, 1709, 1721, 1723, 1733,
  1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801, 1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877,
  1879, 1889, 1901, 1907, 1913, 1931, 1933, 1949, 1951, 1973, 1979, 1987, 1993, 1997, 1999, 2003, 2011, 2017,
  2027, 2029, 2039, 2053, 2063, 2069, 2081, 2083, 2087, 2089, 2099, 2111, 2113, 2129, 2131, 2137, 2141, 2143,
  2153, 2161, 2179, 2203, 2207, 2213, 2221, 2237, 2239, 2243, 2251, 2267, 2269, 2273, 2281, 2287, 2293, 2297,
  2309, 2311, 2333, 2339, 2341, 2347, 2351, 2357, 2371, 2377, 2381, 2383, 2389, 2393, 2399, 2411, 2417, 2423,
  2437, 2441, 2447, 2459, 2467, 2473, 2477, 2503, 2521, 2531, 2539, 2543, 2549, 2551, 2557, 2579, 2591, 2593,
  2609, 2617, 2621, 2633, 2647, 2657, 2659, 2663, 2671, 2677, 2683, 2687, 2689, 2693, 2699, 2707, 2711, 2713,
  2719, 2729, 2731, 2741, 2749, 2753, 2767, 2777, 2789, 2791, 2797, 2801, 2803, 2819, 2833, 2837, 2843, 2851,
  2857, 2861, 2879, 2887, 2897, 2903, 2909, 2917, 2927, 2939, 2953, 2957, 2963, 2969, 2971, 2999, 3001, 3011,
  3019, 3023, 3037, 3041, 3049, 3061, 3067, 3079, 3083, 3089, 3109, 3119, 3121, 3137, 3163, 3167, 3169, 3181,
  3187, 3191, 3203, 3209, 3217, 3221, 3229, 3251, 3253, 3257, 3259, 3271, 3299, 3301, 3307, 3313, 3319, 3323,
  3329, 3331, 3343, 3347, 3359, 3361, 3371, 3373, 3389, 3391, 3407, 3413, 3433, 3449, 3457, 3461, 3463, 3467,
  3469, 3491, 3499, 3511, 3517, 3527, 3529, 3533, 3539, 3541, 3547, 3557, 3559, 3571, 3581, 3583, 3593, 3607,
  3613, 3617, 3623, 3631, 3637, 3643, 3659, 3671, 3673, 3677, 3691, 3697, 3701, 3709, 3719, 3727, 3733, 3739
]

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private theorem primes3760_eq : primes3760 = eligible3760 := by decide +kernel

private lemma mem_primesLe64_of_prime {p : Nat} (hp : p.Prime) (h : p ≤ 64) : p ∈ primesLe64 := by
  have : ∀ k : Fin 65, k.val.Prime → k.val ∈ primesLe64 := by decide +kernel
  exact this ⟨p, by omega⟩ hp

private lemma mem_primes3760 {p : Nat} :
    p ∈ primes3760 ↔ p < 3761 ∧ 2 ≤ p ∧ (p ∈ primesLe64 ∨ Nat.Coprime p (Nat.factorial 64)) := by
  rw [primes3760_eq, eligible3760, List.mem_filter, List.mem_range, decide_eq_true_eq]

private lemma prime_mem_primes3760 {p : Nat} (hp : p.Prime) (hb : p < 3761) :
    p ∈ primes3760 := by
  refine mem_primes3760.mpr ⟨hb, hp.two_le, ?_⟩
  by_cases h : p ≤ 64
  · exact Or.inl (mem_primesLe64_of_prime hp h)
  · exact Or.inr (hp.coprime_factorial_of_lt (by omega))

def properMask (lo len p : Nat) : Nat :=
  progressionMask lo len p ^^^
    (if lo ≤ p ∧ p < lo + len then (1 : Nat) <<< (p - lo) else 0)

private lemma properMask_bit {lo len p i : Nat} (hp : 0 < p) (hi : i < len) :
    (properMask lo len p).testBit i = true ↔ p ∣ lo + i ∧ p ≠ lo + i := by
  have singleton :
      (if lo ≤ p ∧ p < lo + len then (1 : Nat) <<< (p - lo) else 0).testBit i = true ↔ p = lo + i := by
    split
    · next h =>
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq,
        Nat.testBit_one_eq_true_iff_self_eq_zero]
      omega
    · next h =>
      simp only [Nat.zero_testBit, Bool.false_eq_true, false_iff]
      omega
  unfold properMask
  rw [Nat.testBit_xor]
  by_cases h : p = lo + i
  · have hm := (progression_bit hp lo len i hi).mpr (h ▸ (dvd_rfl : p ∣ p))
    rw [hm, singleton.mpr h]
    simp [h]
  · have hs : (if lo ≤ p ∧ p < lo + len then (1 : Nat) <<< (p - lo) else 0).testBit i = false :=
      Bool.eq_false_iff.mpr (h ∘ singleton.mp)
    rw [hs, Bool.xor_false, progression_bit hp lo len i hi]
    simp [h]

def rejectMask (lo len : Nat) : List Nat → Nat
  | [] => 0
  | p :: ps => (properMask lo len p) ||| rejectMask lo len ps

private lemma rejectMask_bit {lo len i : Nat} (hi : i < len)
    (ps : List Nat) (hps : ∀ p ∈ ps, 0 < p) :
    (rejectMask lo len ps).testBit i = true ↔ ∃ p ∈ ps, p ∣ lo + i ∧ p ≠ lo + i := by
  induction ps with
  | nil => simp [rejectMask]
  | cons p ps ih =>
    rw [rejectMask, Nat.testBit_or, Bool.or_eq_true, properMask_bit (hps p (by simp)) hi,
      ih (fun q hq => hps q (List.mem_cons_of_mem _ hq))]
    simp only [List.mem_cons]
    constructor
    · rintro (hp | ⟨q, hq, hd⟩)
      · exact ⟨p, Or.inl rfl, hp⟩
      · exact ⟨q, Or.inr hq, hd⟩
    · rintro ⟨q, rfl | hq, hd⟩
      · exact Or.inl hd
      · exact Or.inr ⟨q, hq, hd⟩

def intervalDivisors (limit : Nat) : List Nat :=
  primes3760.filter (fun p => decide (p * p < limit))

private lemma mem_intervalDivisors {limit p : Nat} :
    p ∈ intervalDivisors limit ↔ p ∈ primes3760 ∧ p * p < limit := by
  rw [intervalDivisors, List.mem_filter, decide_eq_true_eq]

private lemma no_small_factor {n limit : Nat} (hlo : 2 ≤ n) (hn : n < limit)
    (hhi : limit ≤ 14137600) :
    (¬ ∃ p ∈ intervalDivisors limit, p ∣ n ∧ p ≠ n) ↔ n.Prime := by
  constructor
  · intro h
    by_contra hnot
    have hp : n.minFac.Prime := Nat.minFac_prime (by omega)
    have hs : n.minFac * n.minFac ≤ n := by
      simpa [sq] using Nat.minFac_sq_le_self (by omega : 0 < n) hnot
    have hmin : n.minFac < 3761 := by
      by_contra hbig
      push Not at hbig
      have : 3761 * 3761 ≤ n.minFac * n.minFac := Nat.mul_le_mul hbig hbig
      omega
    exact h ⟨n.minFac, mem_intervalDivisors.mpr ⟨prime_mem_primes3760 hp hmin, hs.trans_lt hn⟩,
      n.minFac_dvd, ne_of_lt ((Nat.not_prime_iff_minFac_lt hlo).mp hnot)⟩
  · intro h ⟨p, hp, hd, hne⟩
    obtain ⟨_, hp2, _⟩ := mem_primes3760.mp (mem_intervalDivisors.mp hp).1
    exact hne ((Nat.dvd_prime_two_le h hp2).mp hd)

def primeMask (lo len : Nat) : Nat :=
  let box := pulses 1 len
  box ^^^ (box &&& rejectMask lo len (intervalDivisors (lo + len)))

theorem primeMask_lt (lo len : Nat) : primeMask lo len < 2 ^ len := by
  by_contra hge
  push Not at hge
  have hsub : ∀ i, (primeMask lo len).testBit i = true → (pulses 1 len).testBit i = true := by
    intro i hi
    unfold primeMask at hi
    rw [Nat.testBit_xor, Nat.testBit_and] at hi
    cases h : (pulses 1 len).testBit i <;> simp [h] at hi ⊢
  have hne : primeMask lo len >>> len ≠ 0 := by
    rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_pos hge (by positivity)).ne'
  obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero hne
  have hbit : (primeMask lo len).testBit (len + j) = true := by
    simpa [Nat.testBit_shiftRight, Nat.add_comm] using hj
  obtain ⟨k, hk, heq⟩ := (pulses_bit (by decide : 0 < 1) len (len + j)).mp (hsub _ hbit)
  omega

theorem primeMask_bit {lo len i : Nat} (hlo : 2 ≤ lo) (hhi : lo + len ≤ 14137600)
    (hi : i < len) : (primeMask lo len).testBit i = true ↔ (lo + i).Prime := by
  unfold primeMask
  rw [Nat.testBit_xor, Nat.testBit_and]
  have hbox : (pulses 1 len).testBit i = true :=
    (pulses_bit (by decide : 0 < 1) len i).mpr ⟨i, hi, by omega⟩
  rw [hbox, Bool.true_and, Bool.true_xor]
  have hit := rejectMask_bit (lo := lo) hi (intervalDivisors (lo + len))
      (fun p hp => by have := (mem_primes3760.mp (mem_intervalDivisors.mp hp).1).2.1; omega)
  have hbool : ∀ b : Bool, ((!b) = true) ↔ b = false := fun b => by cases b <;> decide
  rw [hbool, ← Bool.not_eq_true, hit, no_small_factor (by omega) (by omega) hhi]

theorem primeCounting'_add_range (lo len : Nat) :
    Nat.primeCounting' (lo + len) = Nat.primeCounting' lo +
      ∑ i ∈ range len, (decide ((lo + i).Prime)).toNat := by
  induction len with
  | zero => simp
  | succ len ih =>
    rw [← Nat.add_assoc, Nat.primeCounting', Nat.count_succ, ← Nat.primeCounting', ih,
      sum_range_succ, Nat.add_assoc]
    congr 1
    by_cases hp : (lo + len).Prime <;> simp [hp]

end ColtonSieve

/- ### SWAR Popcount for Width-1 Bitmasks -/

namespace ColtonSWAR

open Finset ColtonSieve

def laneSum (w len : Nat) (f : Nat → Nat) : Nat :=
  ∑ i ∈ range len, f i * 2 ^ (w * i)

private lemma laneSum_lt {w len : Nat} {f : Nat → Nat} (hf : ∀ i < len, f i < 2 ^ w) :
    laneSum w len f < 2 ^ (w * len) := by
  induction len with
  | zero => simp [laneSum]
  | succ len ih =>
    unfold laneSum at ih ⊢
    rw [sum_range_succ]
    have h1 := ih (fun i hi => hf i (by omega))
    have h2 : f len ≤ 2 ^ w - 1 := by have := hf len (by omega); omega
    have h3 : f len * 2 ^ (w * len) ≤ (2 ^ w - 1) * 2 ^ (w * len) := Nat.mul_le_mul_right _ h2
    have h4 : 2 ^ (w * (len + 1)) = 2 ^ w * 2 ^ (w * len) := by
      rw [Nat.mul_succ, Nat.pow_add, Nat.mul_comm]
    have hpos : 0 < 2 ^ w := by positivity
    have h5 : (2 ^ w - 1) * 2 ^ (w * len) + 2 ^ (w * len) = 2 ^ w * 2 ^ (w * len) := by
      have : (2 ^ w - 1) * 2 ^ (w * len) + 2 ^ (w * len) = (2 ^ w - 1 + 1) * 2 ^ (w * len) := by ring
      rw [this, Nat.sub_add_cancel hpos]
    omega

private lemma laneSum_testBit {w len : Nat} {f : Nat → Nat} (hw : 0 < w)
    (hf : ∀ i < len, f i < 2 ^ w) (k : Nat) :
    (laneSum w len f).testBit k = (if k / w < len then (f (k / w)).testBit (k % w) else false) := by
  induction len with
  | zero => simp [laneSum]
  | succ len ih =>
    have hsplit : laneSum w (len + 1) f = (f len <<< (w * len)) ||| laneSum w len f := by
      rw [← Nat.shiftLeft_add_eq_or_of_lt (laneSum_lt (fun i hi => hf i (by omega)))]
      unfold laneSum
      rw [sum_range_succ, Nat.shiftLeft_eq, Nat.add_comm]
    rw [hsplit, Nat.testBit_or, Nat.testBit_shiftLeft, ih (fun i hi => hf i (by omega))]
    by_cases hk : k < w * len
    · have hdiv : k / w < len := (Nat.div_lt_iff_lt_mul hw).mpr (by rw [Nat.mul_comm]; exact hk)
      have hnot : ¬ (w * len ≤ k) := by omega
      simp [hnot, hdiv, show k / w < len + 1 by omega]
    · by_cases hk2 : k < w * (len + 1)
      · have hdiv : k / w = len := by
          have h1 : len ≤ k / w := (Nat.le_div_iff_mul_le hw).mpr (by rw [Nat.mul_comm]; omega)
          have h2 : k / w < len + 1 := (Nat.div_lt_iff_lt_mul hw).mpr (by rw [Nat.mul_comm]; exact hk2)
          omega
        have hrem : k - w * len = k % w := by
          have := Nat.div_add_mod k w
          rw [hdiv] at this; omega
        have hge : w * len ≤ k := by omega
        have hlt1 : k / w < len + 1 := by omega
        have hnotl : ¬ (k / w < len) := by omega
        simp [hge, hdiv, hrem]
      · have hdiv : ¬ (k / w < len + 1) := by
          intro h
          have := (Nat.div_lt_iff_lt_mul hw).mp h
          rw [Nat.mul_comm] at this; omega
        have hnotl : ¬ (k / w < len) := by omega
        have hbig : w ≤ k - w * len := by rw [Nat.mul_succ] at hk2; omega
        have hzero : (f len).testBit (k - w * len) = false :=
          Nat.testBit_lt_two_pow ((hf len (by omega)).trans_le (Nat.pow_le_pow_right (by decide) hbig))
        simp [hnotl, hdiv, hzero]

private lemma laneMask_testBit {w len : Nat} (hw : 0 < w) (k : Nat) :
    ((2 ^ w - 1) * pulses (2 * w) len).testBit k = decide (k / (2 * w) < len ∧ k % (2 * w) < w) := by
  have heq : (2 ^ w - 1) * pulses (2 * w) len = laneSum (2 * w) len (fun _ => 2 ^ w - 1) := by
    have hbase : 2 ≤ (2 : Nat) ^ (2 * w) := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < (2 : Nat)) (show 1 ≤ 2 * w by omega)
    unfold pulses laneSum
    rw [← Nat.geomSum_eq hbase, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [← Nat.pow_mul]
  rw [heq, laneSum_testBit (by omega) (fun _ _ => by
    have : 2 ^ w ≤ 2 ^ (2 * w) := Nat.pow_le_pow_right (by decide) (by omega)
    have : 0 < 2 ^ w := by positivity
    omega)]
  by_cases h1 : k / (2 * w) < len
  · simp only [h1, ite_true, true_and]
    simp [Nat.testBit_two_pow_sub_one]
  · simp [h1]

private lemma swarStep {w len : Nat} (hw : 0 < w) {f : Nat → Nat}
    (hf : ∀ i < 2 * len, f i < 2 ^ w) :
    let x := laneSum w (2 * len) f
    let m := (2 ^ w - 1) * pulses (2 * w) len
    (x &&& m) + ((x >>> w) &&& m) = laneSum (2 * w) len (fun j => f (2 * j) + f (2 * j + 1)) := by
  intro x m
  have h1 : x &&& m = laneSum (2 * w) len (fun j => f (2 * j)) := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, laneSum_testBit hw hf, laneMask_testBit hw,
      laneSum_testBit (by omega) (fun j hj => (hf (2 * j) (by omega)).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega)))]
    by_cases hlen : k / (2 * w) < len
    · by_cases hrem : k % (2 * w) < w
      · have hmul2 : 2 * w * (k / (2 * w)) = w * (2 * (k / (2 * w))) := by ring
        have hq : k = w * (2 * (k / (2 * w))) + k % (2 * w) := by
          have := Nat.div_add_mod k (2 * w); omega
        have hd : k / w = 2 * (k / (2 * w)) := by
          conv_lhs => rw [hq]
          rw [Nat.mul_add_div hw, Nat.div_eq_of_lt hrem, add_zero]
        have hr : k % w = k % (2 * w) := by
          conv_lhs => rw [hq]
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrem]
        simp [hlen, hrem, hd, hr, show 2 * (k / (2 * w)) < 2 * len by omega]
      · have hbig : (f (2 * (k / (2 * w)))).testBit (k % (2 * w)) = false :=
          Nat.testBit_lt_two_pow ((hf (2 * (k / (2 * w))) (by omega)).trans_le
            (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [hlen, hrem, hbig]
    · simp [hlen]
  have h2 : (x >>> w) &&& m = laneSum (2 * w) len (fun j => f (2 * j + 1)) := by
    apply Nat.eq_of_testBit_eq
    intro k
    rw [Nat.testBit_and, Nat.testBit_shiftRight, laneSum_testBit hw hf, laneMask_testBit hw,
      laneSum_testBit (by omega) (fun j hj => (hf (2 * j + 1) (by omega)).trans_le
        (Nat.pow_le_pow_right (by decide) (by omega)))]
    by_cases hlen : k / (2 * w) < len
    · by_cases hrem : k % (2 * w) < w
      · have hmul2 : 2 * w * (k / (2 * w)) = w * (2 * (k / (2 * w))) := by ring
        have hq : w + k = w * (2 * (k / (2 * w)) + 1) + k % (2 * w) := by
          have := Nat.div_add_mod k (2 * w)
          rw [Nat.mul_add, Nat.mul_one]; omega
        have hd : (w + k) / w = 2 * (k / (2 * w)) + 1 := by
          conv_lhs => rw [hq]
          rw [Nat.mul_add_div hw, Nat.div_eq_of_lt hrem, add_zero]
        have hr : (w + k) % w = k % (2 * w) := by
          conv_lhs => rw [hq]
          rw [Nat.mul_add_mod, Nat.mod_eq_of_lt hrem]
        simp [hlen, hrem, hd, hr, show 2 * (k / (2 * w)) + 1 < 2 * len by omega]
      · have hbig : (f (2 * (k / (2 * w)) + 1)).testBit (k % (2 * w)) = false :=
          Nat.testBit_lt_two_pow ((hf (2 * (k / (2 * w)) + 1) (by omega)).trans_le
            (Nat.pow_le_pow_right (by decide) (by omega)))
        simp [hlen, hrem, hbig]
    · simp [hlen]
  rw [h1, h2]
  unfold laneSum
  rw [← sum_add_distrib]
  refine sum_congr rfl fun j _ => by ring

private lemma laneSum_mod_eq (len : Nat) (f : Nat → Nat) :
    laneSum 16 len f ≡ ∑ i ∈ range len, f i [MOD 65535] := by
  have hm : (2 ^ 16 : Nat) ≡ 1 [MOD 65535] := by decide
  induction len with
  | zero => simp [laneSum, Nat.ModEq]
  | succ len ih =>
    unfold laneSum at ih ⊢
    rw [sum_range_succ, sum_range_succ]
    apply ih.add
    rw [Nat.pow_mul]
    simpa using (Nat.ModEq.refl (f len)).mul (hm.pow len)

private lemma laneSum_mod {len : Nat} {f : Nat → Nat}
    (hsum : ∑ i ∈ range len, f i < 65535) :
    laneSum 16 len f % 65535 = ∑ i ∈ range len, f i := by
  have hrel := laneSum_mod_eq len f
  unfold Nat.ModEq at hrel
  exact hrel.trans (Nat.mod_eq_of_lt hsum)

private lemma eq_laneSum_one {len word : Nat} (hword : word < 2 ^ len) :
    word = laneSum 1 len (fun i => (word.testBit i).toNat) := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [laneSum_testBit (by decide : 0 < 1) (fun i _ => by cases word.testBit i <;> decide)]
  simp only [Nat.div_one, Nat.mod_one]
  by_cases hk : k < len
  · simp only [hk, ite_true]
    cases h : word.testBit k <;> decide
  · simp only [hk, ite_false]
    exact Nat.testBit_lt_two_pow (hword.trans_le (Nat.pow_le_pow_right (by decide) (by omega)))

/-- SWAR popcount of a `(16 * m)`-bit mask (`16 * m < 65535`). -/
def swarPop (m w : Nat) : Nat :=
  let m1 := pulses 2 (8 * m)
  let m2 := 3 * pulses 4 (4 * m)
  let m4 := 15 * pulses 8 (2 * m)
  let m8 := 255 * pulses 16 m
  let w1 := (w &&& m1) + ((w >>> 1) &&& m1)
  let w2 := (w1 &&& m2) + ((w1 >>> 2) &&& m2)
  let w3 := (w2 &&& m4) + ((w2 >>> 4) &&& m4)
  let w4 := (w3 &&& m8) + ((w3 >>> 8) &&& m8)
  w4 % 65535

theorem swarPop_eq {m w : Nat} (hm : 16 * m < 65535) (hw : w < 2 ^ (16 * m)) :
    swarPop m w = ∑ i ∈ range (16 * m), (w.testBit i).toNat := by
  unfold swarPop
  let f0 : Nat → Nat := fun i => (w.testBit i).toNat
  let f1 : Nat → Nat := fun j => f0 (2 * j) + f0 (2 * j + 1)
  let f2 : Nat → Nat := fun j => f1 (2 * j) + f1 (2 * j + 1)
  let f3 : Nat → Nat := fun j => f2 (2 * j) + f2 (2 * j + 1)
  let f4 : Nat → Nat := fun j => f3 (2 * j) + f3 (2 * j + 1)
  have hf0 : ∀ i < 2 * (8 * m), f0 i < 2 ^ 1 := fun i _ => by
    dsimp [f0]; cases w.testBit i <;> decide
  have hf1 : ∀ i < 2 * (4 * m), f1 i < 2 ^ 2 := fun i hi => by
    dsimp [f1]; have := hf0 (2 * i) (by omega); have := hf0 (2 * i + 1) (by omega); omega
  have hf2 : ∀ i < 2 * (2 * m), f2 i < 2 ^ 4 := fun i hi => by
    dsimp [f2]; have := hf1 (2 * i) (by omega); have := hf1 (2 * i + 1) (by omega); omega
  have hf3 : ∀ i < 2 * m, f3 i < 2 ^ 8 := fun i hi => by
    dsimp [f3]; have := hf2 (2 * i) (by omega); have := hf2 (2 * i + 1) (by omega); omega
  have hw0 : w = laneSum 1 (2 * (8 * m)) f0 := by
    simpa [show 2 * (8 * m) = 16 * m by omega] using eq_laneSum_one hw
  have hs1 := swarStep (w := 1) (len := 8 * m) (by decide) hf0
  have hs2 := swarStep (w := 2) (len := 4 * m) (by decide) hf1
  have hs3 := swarStep (w := 4) (len := 2 * m) (by decide) hf2
  have hs4 := swarStep (w := 8) (len := m) (by decide) hf3
  dsimp only at hs1 hs2 hs3 hs4
  have hsum_pair : ∀ (g : Nat → Nat) (n : Nat),
      ∑ j ∈ range n, (g (2 * j) + g (2 * j + 1)) = ∑ i ∈ range (2 * n), g i := by
    intro g n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [sum_range_succ, ih, show 2 * (n + 1) = 2 * n + 1 + 1 by omega,
        sum_range_succ, sum_range_succ, Nat.add_assoc]
  have hsum_eq : ∑ j ∈ range m, f4 j = ∑ i ∈ range (16 * m), f0 i := by
    calc ∑ j ∈ range m, f4 j
        = ∑ j ∈ range (2 * m), f3 j := hsum_pair f3 m
      _ = ∑ j ∈ range (2 * (2 * m)), f2 j := hsum_pair f2 (2 * m)
      _ = ∑ j ∈ range (2 * (4 * m)), f1 j := by
          simpa [show 2 * (2 * m) = 4 * m by omega] using hsum_pair f1 (4 * m)
      _ = ∑ i ∈ range (16 * m), f0 i := by
          simpa [show 2 * (4 * m) = 8 * m by omega, show 2 * (8 * m) = 16 * m by omega]
            using hsum_pair f0 (8 * m)
  have hsum_lt : ∑ j ∈ range m, f4 j < 65535 := by
    rw [hsum_eq]
    have hle : ∑ i ∈ range (16 * m), f0 i ≤ 16 * m := by
      calc _ ≤ ∑ _i ∈ range (16 * m), 1 := sum_le_sum fun i _ => by
            dsimp [f0]; cases w.testBit i <;> decide
        _ = 16 * m := by simp
    omega
  conv_lhs => rw [hw0]
  have hm1 : pulses 2 (8 * m) = (2 ^ 1 - 1) * pulses (2 * 1) (8 * m) := by simp
  have hm2 : 3 * pulses 4 (4 * m) = (2 ^ 2 - 1) * pulses (2 * 2) (4 * m) := by norm_num
  have hm4 : 15 * pulses 8 (2 * m) = (2 ^ 4 - 1) * pulses (2 * 4) (2 * m) := by norm_num
  have hm8 : 255 * pulses 16 m = (2 ^ 8 - 1) * pulses (2 * 8) m := by norm_num
  dsimp only
  rw [hm1, hs1]
  have h2eq : laneSum (2 * 1) (8 * m) f1 = laneSum 2 (2 * (4 * m)) f1 := by
    simp [show 8 * m = 2 * (4 * m) by omega]
  rw [h2eq, hm2, hs2]
  have h4eq : laneSum (2 * 2) (4 * m) f2 = laneSum 4 (2 * (2 * m)) f2 := by
    simp [show 4 * m = 2 * (2 * m) by omega]
  rw [h4eq, hm4, hs3]
  have h8eq : laneSum (2 * 4) (2 * m) f3 = laneSum 8 (2 * m) f3 := by simp
  rw [h8eq, hm8, hs4]
  have h16eq : laneSum (2 * 8) m f4 = laneSum 16 m f4 := by simp
  rw [h16eq, laneSum_mod hsum_lt, hsum_eq]

/-- Precomputed SWAR masks for `m = 1024` (`len = 16384`), avoiding repeated mask synthesis. -/
def m1_16k : Nat := pulses 2 (8 * 1024)
def m2_16k : Nat := 3 * pulses 4 (4 * 1024)
def m4_16k : Nat := 15 * pulses 8 (2 * 1024)
def m8_16k : Nat := 255 * pulses 16 1024

def pop16k (w : Nat) : Nat :=
  let w1 := (w &&& m1_16k) + ((w >>> 1) &&& m1_16k)
  let w2 := (w1 &&& m2_16k) + ((w1 >>> 2) &&& m2_16k)
  let w3 := (w2 &&& m4_16k) + ((w2 >>> 4) &&& m4_16k)
  let w4 := (w3 &&& m8_16k) + ((w3 >>> 8) &&& m8_16k)
  w4 % 65535

lemma pop16k_eq (w : Nat) : pop16k w = swarPop 1024 w := rfl

/-- Exact prime count on `[lo, lo + 16 * m)`. -/
def countBlock (m lo : Nat) : Nat := swarPop m (primeMask lo (16 * m))

theorem countBlock_correct {m lo : Nat} (hm : 16 * m < 65535)
    (hlo : 2 ≤ lo) (hhi : lo + 16 * m ≤ 14137600) :
    Nat.primeCounting' (lo + 16 * m) = Nat.primeCounting' lo + countBlock m lo := by
  rw [countBlock, swarPop_eq hm (primeMask_lt lo (16 * m)), primeCounting'_add_range]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hilt := mem_range.mp hi
  have hbit := primeMask_bit hlo hhi hilt
  by_cases hp : (lo + i).Prime
  · rw [hbit.mpr hp]; simp [hp]
  · have hf : (primeMask lo (16 * m)).testBit i = false := Bool.eq_false_iff.mpr (hp ∘ hbit.mp)
    rw [hf]; simp [hp]

def count16k (lo : Nat) : Nat := pop16k (primeMask lo 16384)

theorem count16k_correct {lo : Nat} (hlo : 2 ≤ lo) (hhi : lo + 16384 ≤ 14137600) :
    Nat.primeCounting' (lo + 16384) = Nat.primeCounting' lo + count16k lo := by
  simpa [count16k, pop16k_eq, countBlock] using countBlock_correct (m := 1024) (by decide) hlo hhi

/-- Extract a sub-block of width `16 * m` at offset `off` from a precomputed primeMask `word`. -/
def slicePop (m word off : Nat) : Nat :=
  swarPop m ((word >>> off) % (1 <<< (16 * m)))

theorem slicePop_correct {lo len m off : Nat} (hm : 16 * m < 65535)
    (hlo : 2 ≤ lo) (hhi : lo + len ≤ 14137600) (hsub : off + 16 * m ≤ len) :
    Nat.primeCounting' (lo + off + 16 * m) =
      Nat.primeCounting' (lo + off) + slicePop m (primeMask lo len) off := by
  have hpow : (1 <<< (16 * m)) = 2 ^ (16 * m) := by simp [Nat.shiftLeft_eq]
  unfold slicePop
  rw [hpow, swarPop_eq hm (Nat.mod_lt _ (by positivity)), primeCounting'_add_range]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hilt := mem_range.mp hi
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, decide_eq_true hilt, Bool.true_and]
  have hbit := primeMask_bit hlo hhi (show off + i < len by omega)
  rw [show lo + (off + i) = lo + off + i by omega] at hbit
  by_cases hp : (lo + off + i).Prime
  · rw [hbit.mpr hp]; simp [hp]
  · have hf : (primeMask lo len).testBit (off + i) = false := Bool.eq_false_iff.mpr (hp ∘ hbit.mp)
    rw [hf]; simp [hp]

end ColtonSWAR

/- ### Exact Small Prime Counter up to 8192 -/

namespace ColtonSmall

open Finset ColtonSieve

def popByte (word : Nat) : Nat :=
  (0x8776766576656554766565546554544376656554655454436554544354434332766565546554544365545443544343326554544354434332544343324332322176656554655454436554544354434332655454435443433254434332433232216554544354434332544343324332322154434332433232214332322132212110 >>> (4 * (word % 256))) % 16

private lemma popByte_checked : ∀ b : Fin 256,
    popByte b.val = ∑ i ∈ range 8, (b.val.testBit i).toNat := by
  decide +kernel

private lemma popByte_eq (word : Nat) :
    popByte word = ∑ i ∈ range 8, (word.testBit i).toNat := by
  have h := popByte_checked ⟨word % 256, Nat.mod_lt _ (by decide)⟩
  have hp : popByte (word % 256) = popByte word := by simp [popByte]
  change popByte (word % 256) = ∑ i ∈ range 8, ((word % 256).testBit i).toNat at h
  rw [hp] at h
  rw [h]
  refine sum_congr rfl fun i hi => ?_
  have hlt := mem_range.mp hi
  rw [show (256 : Nat) = 2 ^ 8 by decide, Nat.testBit_mod_two_pow]
  simp [hlt]

def popBytes : Nat → Nat → Nat
  | 0, _ => 0
  | len + 1, word => popByte word + popBytes len (word >>> 8)

private lemma popBytes_eq (len word : Nat) :
    popBytes len word = ∑ i ∈ range (8 * len), (word.testBit i).toNat := by
  induction len generalizing word with
  | zero => simp [popBytes]
  | succ len ih =>
    rw [popBytes, popByte_eq, ih, show 8 * (len + 1) = 8 + 8 * len by omega, sum_range_add]
    simp [Nat.testBit_shiftRight, Nat.add_comm]

def popPrefix (word len : Nat) : Nat :=
  popBytes (len / 8) word + popByte ((word >>> (8 * (len / 8))) % (2 ^ (len % 8)))

theorem popPrefix_eq (word len : Nat) :
    popPrefix word len = ∑ i ∈ range len, (word.testBit i).toNat := by
  unfold popPrefix
  rw [popBytes_eq, popByte_eq]
  let base := 8 * (len / 8)
  let tail := len % 8
  have hsum : base + tail = len := by dsimp [base, tail]; omega
  conv_rhs => rw [← hsum, sum_range_add]
  apply congrArg (fun x : Nat => (∑ i ∈ range base, (word.testBit i).toNat) + x)
  rw [← sum_filter_add_sum_filter_not (s := range 8) (p := fun i => i < tail)]
  rw [show (range 8).filter (fun i => i < tail) = range tail by
    ext i; rw [mem_filter, mem_range, mem_range]; dsimp [tail]; omega]
  have hz : (∑ i ∈ (range 8).filter (fun i => ¬ i < tail),
      (((word >>> base) % (2 ^ tail)).testBit i).toNat) = 0 := by
    apply sum_eq_zero
    intro i hi
    have hi' := (mem_filter.mp hi).2
    simp [Nat.testBit_mod_two_pow, hi']
  rw [hz, add_zero]
  refine sum_congr rfl fun i hi => ?_
  have h : i < len % 8 := mem_range.mp hi
  simp [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, h, base, Nat.add_comm]

def smallMask : Nat :=
  0x20020220800200000208200808a08008020800200000828000800000020028008820200208000228820008008008208000008800000028800800220800220220808800008220000800220028208800a00a08808208020200a08800028200008000820000800000800028000a00800a00800200000008220808020a20008200800020200000a08008200000200800800220020208008820208220a00a00000008220200020028208000808a20000200a00a00028000008800200828028020800a08000800020020200008828200a20000808000000200808800028000020800000808020820a08020808208200a00200828208020000808820228000008020020200a00808008028020820008220808000220000208000000800200220000208000a00a08828220020808208020220000000828800008200808820008028a20a00020000000200808820800000220a00228000228200000828820028820208208000000220008020008208000a08008000008a20000800808020220008200000020820a00208800020200200028028220820008a00820208a00200820008008200800000020008800a08a20000020200008828000200200208020828228000800020820200020800a00000228820008028000208220800028008008200008020808028020000000808200a00a08028028028200800000800028800208a00020020a00208000828000020a08228008000020000220028228220000808800200a20008028000208800200a08000020820200808820008a00200020820208820008028020028020a08a00820020200000a28808000800008200028000a00a00220028220820a00000020028a00000808808200220800a20000008000a00800008220020800808800220200a00000028208800200200808208020200008820208800200028828008020008808028020a20208a20820228020008008808000a00200000828220200800020000008820200208800208200208828820008220a08000028008820808a00020228000808220000020000808028828000a00200a28008200800200a00820228820208000028000a00008208008028a20800200020200200800a20800020820808028008028800000a20800008020a08a08800220220208820020200200208a28020020a20208a20008020000808208000000020a00228828228000200800828208800808208020200a00000820808208a20000828028020a00a08800820208220008208808020220000228800228800200a28028008020008808820220820200808020208800a08228020028820a08200828208020800028008220220200228808220a00a00808808220820208a00820008a20008028828208200a08a20020028a00a08220828028220008a28808220a20a08228828228a2b

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
theorem smallMask_eq : smallMask = primeMask 2 8192 := by decide +kernel

def smallPref : Array Nat :=
  #[0, 55, 97, 136, 172, 207, 242, 278, 309, 342, 375, 409, 439, 469, 502, 532, 564,
    594, 623, 651, 685, 708, 739, 775, 801, 834, 857, 889, 916, 941, 974, 1003, 1028]

private def smallWindow (row len : Nat) : Nat :=
  popPrefix (smallMask >>> (256 * row)) len

set_option maxHeartbeats 0 in
private lemma smallPref_step : ∀ row : Fin 32,
    smallPref[row.val + 1]! = smallPref[row.val]! + smallWindow row.val 256 := by decide +kernel

private lemma smallWindow_correct {row len : Nat} (hrow : row < 32) (hlen : len ≤ 256) :
    Nat.primeCounting' ((2 + 256 * row) + len) =
      Nat.primeCounting' (2 + 256 * row) + smallWindow row len := by
  rw [primeCounting'_add_range, smallWindow, popPrefix_eq]
  congr 1
  refine sum_congr rfl fun i hi => ?_
  have hilt := mem_range.mp hi
  rw [smallMask_eq, Nat.testBit_shiftRight]
  have hbit := primeMask_bit (lo := 2) (len := 8192) (i := 256 * row + i)
    (by omega) (by omega) (by omega)
  rw [show 2 + (256 * row + i) = (2 + 256 * row) + i by omega] at hbit
  by_cases hp : ((2 + 256 * row) + i).Prime
  · rw [hbit.mpr hp]; simp [hp]
  · have hf : (primeMask 2 8192).testBit (256 * row + i) = false :=
      Bool.eq_false_iff.mpr (hp ∘ hbit.mp)
    rw [hf]; simp [hp]

def exactPiSmall (n : Nat) : Nat :=
  if n < 2 then 0
  else smallPref[(n - 1) / 256]! + smallWindow ((n - 1) / 256) ((n - 1) % 256)

theorem exactPiSmall_correct {n : Nat} (hn : n ≤ 8192) :
    exactPiSmall n = n.primeCounting := by
  have hpref : ∀ row ≤ 32, smallPref[row]! = Nat.primeCounting' (2 + 256 * row) := by
    intro row
    induction row with
    | zero => intro _; decide
    | succ row ih =>
      intro hr
      have hstep := smallPref_step ⟨row, by omega⟩
      rw [hstep, ih (by omega), show 2 + 256 * (row + 1) = (2 + 256 * row) + 256 by omega,
        smallWindow_correct (by omega) (by omega)]
  unfold exactPiSmall
  split
  · next h =>
    have : n = 0 ∨ n = 1 := by omega
    rcases this with rfl | rfl <;> decide
  · next h =>
    let row := (n - 1) / 256
    let len := (n - 1) % 256
    have hrow : row < 32 := by dsimp [row]; omega
    have hlen : len ≤ 256 := by dsimp [len]; omega
    have he : (2 + 256 * row) + len = n + 1 := by dsimp [row, len]; omega
    change smallPref[row]! + smallWindow row len = Nat.primeCounting' (n + 1)
    rw [hpref row (by omega), ← smallWindow_correct hrow hlen, he]

end ColtonSmall

/- ### Generic Fast Trial Factorization (`fastTauTop`) and Base 4096 Certificate -/

namespace ColtonFactor

open Finset

def stripPrime (p : Nat) : Nat → Nat → Nat × Nat
  | 0, n => (n, 0)
  | fuel + 1, n =>
    if n % p = 0 then
      let r := stripPrime p fuel (n / p)
      (r.1, r.2 + 1)
    else (n, 0)

private lemma stripPrime_spec {p : Nat} (hp : 2 ≤ p) :
    ∀ (fuel n : Nat), 0 < n → n < 2 ^ fuel →
      let r := stripPrime p fuel n
      n = r.1 * p ^ r.2 ∧ 0 < r.1 ∧ ¬ (p ∣ r.1) := by
  intro fuel
  induction fuel with
  | zero => intro n hn hlt; omega
  | succ fuel ih =>
    intro n hn hlt
    unfold stripPrime
    split
    · next hmod =>
      have hd : p ∣ n := Nat.dvd_of_mod_eq_zero hmod
      have hpos : 0 < n / p := Nat.div_pos (Nat.le_of_dvd hn hd) (by omega)
      have hdiv_lt : n / p < 2 ^ fuel := by
        have h2 : n / p ≤ n / 2 := Nat.div_le_div_left hp (by decide : 0 < 2)
        have hpow : 2 ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [Nat.pow_succ, Nat.mul_comm]
        omega
      have hr := ih (n / p) hpos hdiv_lt
      dsimp only at hr ⊢
      refine ⟨?_, hr.2.1, hr.2.2⟩
      have hmul : p * (n / p) = n := Nat.mul_div_cancel' hd
      calc n = p * (n / p) := hmul.symm
        _ = p * ((stripPrime p fuel (n / p)).1 * p ^ (stripPrime p fuel (n / p)).2) :=
            congrArg (p * ·) hr.1
        _ = (stripPrime p fuel (n / p)).1 * p ^ ((stripPrime p fuel (n / p)).2 + 1) := by
            rw [Nat.pow_succ]; ring
    · next hmod =>
      refine ⟨by simp, hn, fun hd => hmod (Nat.mod_eq_zero_of_dvd hd)⟩

def trialLoop (fuel : Nat) : List Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | [], rem, tau, top => (rem, tau, top)
  | p :: ps, rem, tau, top =>
    if rem % p = 0 then
      let r := stripPrime p fuel rem
      trialLoop fuel ps r.1 (tau * (r.2 + 1)) (max top p)
    else
      trialLoop fuel ps rem tau top

private lemma prime_pow_divisors_card {p e : Nat} (hp : p.Prime) :
    (p ^ e).divisors.card = e + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

private lemma prime_pow_top {p e : Nat} (hp : p.Prime) (he : 1 ≤ e) :
    (p ^ e).primeFactors.sup id = p := by
  rw [Nat.primeFactors_pow p (by omega), hp.primeFactors]
  simp

private lemma trialLoop_spec (fuel : Nat) (ps : List Nat)
    (hps : ∀ p ∈ ps, p.Prime) (hnodup : ps.Nodup) :
    ∀ (rem used : Nat),
      0 < rem → rem < 2 ^ fuel → 0 < used →
      (∀ p ∈ ps, ¬ (p ∣ used)) →
      Nat.Coprime rem used →
      let out := trialLoop fuel ps rem used.divisors.card (used.primeFactors.sup id)
      ∃ used', rem * used = out.1 * used' ∧ 0 < out.1 ∧ 0 < used' ∧
        Nat.Coprime out.1 used' ∧
        (∀ p ∈ ps, ¬ (p ∣ out.1)) ∧
        (∀ q, q.Prime → q ∣ out.1 → q ∣ rem) ∧
        out.2.1 = used'.divisors.card ∧
        out.2.2 = used'.primeFactors.sup id := by
  induction ps with
  | nil =>
    intro rem used hrem _ hused _ hcop
    refine ⟨used, rfl, hrem, hused, hcop, by simp, fun _ _ h => h, rfl, rfl⟩
  | cons p ps ih =>
    intro rem used hrem hlt hused hnotd hcop
    obtain ⟨hp_notin, hnodup'⟩ := List.nodup_cons.mp hnodup
    have hp : p.Prime := hps p (by simp)
    have hps' : ∀ q ∈ ps, q.Prime := fun q hq => hps q (List.mem_cons_of_mem _ hq)
    unfold trialLoop
    split
    · next hmod =>
      have hd : p ∣ rem := Nat.dvd_of_mod_eq_zero hmod
      have hsp := stripPrime_spec hp.two_le fuel rem hrem hlt
      dsimp only at hsp
      set rem' := (stripPrime p fuel rem).1
      set e := (stripPrime p fuel rem).2
      have he1 : 1 ≤ e := by
        by_contra h0
        have he0 : e = 0 := by omega
        rw [he0, pow_zero, mul_one] at hsp
        exact hsp.2.2 (hsp.1 ▸ hd)
      have hrem'_le : rem' ≤ rem := by
        have : 1 ≤ p ^ e := Nat.one_le_pow _ _ hp.pos
        nlinarith [hsp.1]
      have hpe_cop_used : Nat.Coprime (p ^ e) used :=
        (hp.coprime_iff_not_dvd.mpr (hnotd p (by simp))).pow_left e
      have hrem'_cop_pe : Nat.Coprime rem' (p ^ e) :=
        (hp.coprime_iff_not_dvd.mpr hsp.2.2).symm.pow_right e
      have hrem'_cop_used : Nat.Coprime rem' used :=
        Nat.Coprime.coprime_dvd_left ⟨p ^ e, hsp.1⟩ hcop
      have hused1_pos : 0 < used * p ^ e := Nat.mul_pos hused (pow_pos hp.pos e)
      have hused1_card : (used * p ^ e).divisors.card = used.divisors.card * (e + 1) := by
        rw [Nat.Coprime.card_divisors_mul hpe_cop_used.symm, prime_pow_divisors_card hp]
      have hused1_top : (used * p ^ e).primeFactors.sup id = max (used.primeFactors.sup id) p := by
        rw [Nat.primeFactors_mul hused.ne' (pow_pos hp.pos e).ne', Finset.sup_union,
          prime_pow_top hp he1]
      have hnotd' : ∀ q ∈ ps, ¬ (q ∣ used * p ^ e) := by
        intro q hq hqd
        have hqp := hps' q hq
        rcases hqp.dvd_mul.mp hqd with hqu | hqpe
        · exact hnotd q (List.mem_cons_of_mem _ hq) hqu
        · have hqp_eq : q = p := (Nat.prime_dvd_prime_iff_eq hqp hp).mp (hqp.dvd_of_dvd_pow hqpe)
          subst hqp_eq
          exact hp_notin hq
      have hrec := ih hps' hnodup' rem' (used * p ^ e) hsp.2.1 (lt_of_le_of_lt hrem'_le hlt)
        hused1_pos hnotd' (hrem'_cop_used.mul_right hrem'_cop_pe)
      rw [hused1_card, hused1_top] at hrec
      obtain ⟨used', hprod, ho1, hu', hcop', hnotp', hsub', hcard', htop'⟩ := hrec
      refine ⟨used', ?_, ho1, hu', hcop', ?_, ?_, hcard', htop'⟩
      · calc rem * used = (rem' * p ^ e) * used := by rw [← hsp.1]
          _ = rem' * (used * p ^ e) := by ring
          _ = _ := hprod
      · intro q hq
        rcases List.mem_cons.mp hq with hqp | hq'
        · subst hqp
          intro hdp
          exact hsp.2.2 (hsub' q hp hdp)
        · exact hnotp' q hq'
      · intro q hqp hqd
        exact dvd_trans (hsub' q hqp hqd) ⟨p ^ e, hsp.1⟩
    · next hmod =>
      have hnotp : ¬ (p ∣ rem) := fun hd => hmod (Nat.mod_eq_zero_of_dvd hd)
      have hrec := ih hps' hnodup' rem used hrem hlt hused
        (fun q hq => hnotd q (List.mem_cons_of_mem _ hq)) hcop
      obtain ⟨used', hprod, ho1, hu', hcop', hnotp', hsub', hcard', htop'⟩ := hrec
      refine ⟨used', hprod, ho1, hu', hcop', ?_, hsub', hcard', htop'⟩
      intro q hq
      rcases List.mem_cons.mp hq with hqp | hq'
      · subst hqp
        intro hdp
        exact hnotp (hsub' q hp hdp)
      · exact hnotp' q hq'

def fastTauTop (fuel : Nat) (ps : List Nat) (n : Nat) : Nat × Nat :=
  let out := trialLoop fuel ps n 1 0
  if out.1 = 1 then (out.2.1, out.2.2) else (2 * out.2.1, max out.2.2 out.1)

theorem fastTauTop_spec {fuel B : Nat} {ps : List Nat}
    (hps : ∀ p ∈ ps, p.Prime) (hnodup : ps.Nodup)
    (hcov : ∀ p, p.Prime → p < B → p ∈ ps)
    {n : Nat} (hn : 0 < n) (hlt : n < 2 ^ fuel) (hsq : n < B * B) :
    (fastTauTop fuel ps n).1 = n.divisors.card ∧
    (fastTauTop fuel ps n).2 = n.primeFactors.sup id := by
  have h1_card : (1 : Nat).divisors.card = 1 := by decide
  have h1_top : (1 : Nat).primeFactors.sup id = 0 := by simp
  have hspec := trialLoop_spec fuel ps hps hnodup n 1 hn hlt (by decide)
    (fun p hp hd => (hps p hp).ne_one (Nat.dvd_one.mp hd)) (Nat.coprime_one_right n)
  rw [h1_card, h1_top, mul_one] at hspec
  set out := trialLoop fuel ps n 1 0
  obtain ⟨used', hprod, ho1, hu', hcop', hnotp', _, hcard', htop'⟩ := hspec
  unfold fastTauTop
  change (if out.1 = 1 then (out.2.1, out.2.2) else (2 * out.2.1, max out.2.2 out.1)).1 = _ ∧
    (if out.1 = 1 then (out.2.1, out.2.2) else (2 * out.2.1, max out.2.2 out.1)).2 = _
  split
  · next h1 =>
    rw [h1, one_mul] at hprod
    rw [hprod]
    exact ⟨hcard', htop'⟩
  · next hne1 =>
    have hrem_le : out.1 ≤ n := by
      have : 1 ≤ used' := hu'
      nlinarith [hprod]
    have hrem_prime : out.1.Prime := by
      by_contra hnot
      have hmf_prime : out.1.minFac.Prime := Nat.minFac_prime hne1
      have hmf_sq : out.1.minFac * out.1.minFac ≤ out.1 := by
        simpa [sq] using Nat.minFac_sq_le_self ho1 hnot
      have hmf_lt : out.1.minFac < B := by
        by_contra hbig
        push Not at hbig
        have : B * B ≤ out.1.minFac * out.1.minFac := Nat.mul_le_mul hbig hbig
        omega
      exact hnotp' _ (hcov _ hmf_prime hmf_lt) (Nat.minFac_dvd _)
    rw [hprod]
    constructor
    · rw [Nat.Coprime.card_divisors_mul hcop', Nat.Prime.divisors hrem_prime,
        Finset.card_pair hrem_prime.ne_one.symm, hcard']
    · rw [Nat.primeFactors_mul ho1.ne' hu'.ne', Finset.sup_union,
        hrem_prime.primeFactors, Finset.sup_singleton, id_eq, htop', max_comm]

end ColtonFactor

/- ### Base Certificate up to 4096 -/

namespace ColtonBase4096

open Finset OeisA111291 ColtonSieve ColtonSmall ColtonFactor

private lemma primesLe64_prime : ∀ p ∈ primesLe64, p.Prime := by decide +kernel
private lemma primesLe64_nodup : primesLe64.Nodup := by decide +kernel
private lemma primesLe64_cov : ∀ p, p.Prime → p < 65 → p ∈ primesLe64 := by
  intro p hp hlt
  have : ∀ k : Fin 65, k.val.Prime → k.val ∈ primesLe64 := by decide +kernel
  exact this ⟨p, hlt⟩ hp

def isRefac4096 (n : Nat) : Bool :=
  if n = 0 then false
  else decide (n % (fastTauTop 13 primesLe64 n).1 = 0)

theorem isRefac4096_iff {n : Nat} (hn : n ≤ 4096) :
    isRefac4096 n = true ↔ n.IsRefactorable := by
  unfold isRefac4096
  by_cases h0 : n = 0
  · subst h0
    simp [Nat.IsRefactorable]
  · simp only [h0, ite_false, decide_eq_true_eq]
    have hpos : 0 < n := Nat.pos_of_ne_zero h0
    have hspec := fastTauTop_spec primesLe64_prime primesLe64_nodup primesLe64_cov
      hpos (by omega : n < 2 ^ 13) (by omega : n < 65 * 65)
    rw [hspec.1, ← Nat.dvd_iff_mod_eq_zero]
    exact ⟨fun hd => ⟨hpos, hd⟩, fun hr => hr.2⟩

private def check4096Aux : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | k + 1, cur, rcnt =>
    let rcnt' := if isRefac4096 cur then rcnt + 1 else rcnt
    decide (exactPiSmall cur ≤ 2 * rcnt') && check4096Aux k (cur + 1) rcnt'

private def countRefac4096Aux : Nat → Nat → Nat → Nat
  | 0, _, rcnt => rcnt
  | k + 1, cur, rcnt =>
    let rcnt' := if isRefac4096 cur then rcnt + 1 else rcnt
    countRefac4096Aux k (cur + 1) rcnt'

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private theorem check4096_ok : check4096Aux 4097 0 0 = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private theorem countRefac4096_eq : countRefac4096Aux 4097 0 0 = 307 := by decide +kernel

private lemma countRefac_succ (n : Nat) :
    countRefactorableNat (n + 1) =
      countRefactorableNat n + if (n + 1).IsRefactorable then 1 else 0 := by
  have he : Icc 1 (n + 1) = insert (n + 1) (Icc 1 n) := by ext i; simp; omega
  have hnot : n + 1 ∉ (Icc 1 n).filter Nat.IsRefactorable := by simp
  by_cases h : (n + 1).IsRefactorable <;>
    simp [countRefactorableNat, he, h, hnot, Finset.filter_insert]

private lemma check4096Aux_sound :
    ∀ (k cur rcnt : Nat), cur + k ≤ 4097 →
      (if cur = 0 then rcnt = 0 else rcnt = countRefactorableNat (cur - 1)) →
      check4096Aux k cur rcnt = true →
      ∀ m, cur ≤ m → m < cur + k → m.primeCounting ≤ 2 * countRefactorableNat m := by
  intro k
  induction k with
  | zero => intro cur rcnt _ _ _ m h1 h2; omega
  | succ k ih =>
    intro cur rcnt hbd hrc hok m hm1 hm2
    unfold check4096Aux at hok
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
    have hcur_le : cur ≤ 4096 := by omega
    have hrc_cur : (if isRefac4096 cur then rcnt + 1 else rcnt) = countRefactorableNat cur := by
      cases cur with
      | zero =>
        simp [isRefac4096, countRefactorableNat] at hrc ⊢
        exact hrc
      | succ c =>
        simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel] at hrc
        rw [hrc, countRefac_succ]
        by_cases hr : (c + 1).IsRefactorable
        · rw [(isRefac4096_iff hcur_le).mpr hr]; simp [hr]
        · have hf : isRefac4096 (c + 1) = false :=
            Bool.eq_false_iff.mpr (fun ht => hr ((isRefac4096_iff hcur_le).mp ht))
          rw [hf]; simp [hr]
    by_cases heq : m = cur
    · subst heq
      rw [← exactPiSmall_correct (by omega : m ≤ 8192), ← hrc_cur]
      exact hok.1
    · exact ih (cur + 1) (if isRefac4096 cur then rcnt + 1 else rcnt) (by omega)
        (by simp [hrc_cur]) hok.2 m (by omega) (by omega)

private lemma countRefac4096Aux_eq :
    ∀ (k cur rcnt : Nat), cur + k ≤ 4097 →
      (if cur = 0 then rcnt = 0 else rcnt = countRefactorableNat (cur - 1)) →
      countRefac4096Aux k cur rcnt = countRefactorableNat (cur + k - 1) := by
  intro k
  induction k with
  | zero =>
    intro cur rcnt _ hrc
    unfold countRefac4096Aux
    cases cur with
    | zero => simp [countRefactorableNat] at hrc ⊢; exact hrc
    | succ c => simp at hrc ⊢; exact hrc
  | succ k ih =>
    intro cur rcnt hbd hrc
    unfold countRefac4096Aux
    have hcur_le : cur ≤ 4096 := by omega
    have hrc_cur : (if isRefac4096 cur then rcnt + 1 else rcnt) = countRefactorableNat cur := by
      cases cur with
      | zero => simp [isRefac4096, countRefactorableNat] at hrc ⊢; exact hrc
      | succ c =>
        simp only [Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel] at hrc
        rw [hrc, countRefac_succ]
        by_cases hr : (c + 1).IsRefactorable
        · rw [(isRefac4096_iff hcur_le).mpr hr]; simp [hr]
        · have hf : isRefac4096 (c + 1) = false :=
            Bool.eq_false_iff.mpr (fun ht => hr ((isRefac4096_iff hcur_le).mp ht))
          rw [hf]; simp [hr]
    have hrec := ih (cur + 1) (if isRefac4096 cur then rcnt + 1 else rcnt) (by omega) (by simp [hrc_cur])
    simpa [show cur + 1 + k - 1 = cur + (k + 1) - 1 by omega] using hrec

theorem colton_le_4096 : ∀ n ≤ 4096, n.primeCounting ≤ 2 * countRefactorableNat n := by
  intro n hn
  exact check4096Aux_sound 4097 0 0 (by omega) (by simp) check4096_ok n (by omega) (by omega)

theorem countRefactorableNat_4096 : countRefactorableNat 4096 = 307 := by
  have h := countRefac4096Aux_eq 4097 0 0 (by omega) (by simp)
  rw [countRefac4096_eq] at h
  exact h.symm

end ColtonBase4096


/- ===================== Mod3_PiAndAbel.lean ===================== -/

/-
Module 3: Computable rational log bounds (12 anchors, scale `10^9`),
zero-constant `π(x)` lower and upper bounds from Chebyshev `θ`,
`θ(10^7)` integral pinning helper, and exact Abel summation for `∑_{L < p ≤ U} 1/p`.
-/

namespace ColtonPiAbel

open Finset Real Chebyshev MeasureTheory

/- ### Part 1: Elementary `log (1 + d)` bounds and 12-anchor computable rational log -/

private lemma log_seven_bounds_aux :
    (1.945910148 : ℝ) < Real.log 7 ∧ Real.log 7 < 1.945910150 := by
  have h1 := Real.abs_log_sub_add_sum_range_le (x := (1 / 8 : ℝ)) (by norm_num) 10
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h1
  norm_num at h1
  have hlog7 : Real.log 7 = 3 * Real.log 2 + Real.log (7 / 8) := by
    have hmul : (7 : ℝ) = (2 : ℝ) ^ (3 : ℕ) * (7 / 8) := by norm_num
    rw [hmul, Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    norm_num
  rw [abs_le] at h1
  have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9
  constructor <;> linarith

theorem two_mul_div_add_le_log_one_add {d : ℝ} (hd : 0 ≤ d) :
    2 * d / (2 + d) ≤ Real.log (1 + d) := by
  let f : ℝ → ℝ := fun t => Real.log (1 + t) - 2 * t / (2 + t)
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt f (t ^ 2 / ((1 + t) * (2 + t) ^ 2)) t := by
    intro t ht
    have ht0 : 0 ≤ t := ht
    have h1 : 1 + t ≠ 0 := by linarith
    have h2 : 2 + t ≠ 0 := by linarith
    have hd1 : HasDerivAt (fun x => Real.log (1 + x)) (1 / (1 + t)) t := by
      have := ((hasDerivAt_id t).const_add 1).log h1
      simpa using this
    have hd2 : HasDerivAt (fun x => 2 * x / (2 + x)) (4 / (2 + t) ^ 2) t := by
      have ha : HasDerivAt (fun x => 2 * x) 2 t := by simpa using (hasDerivAt_id t).const_mul 2
      have hb : HasDerivAt (fun x => 2 + x) 1 t := by simpa using (hasDerivAt_id t).const_add 2
      have hdiv := ha.div hb h2
      have heq : (2 * (2 + t) - 2 * t * 1) / (2 + t) ^ 2 = 4 / (2 + t) ^ 2 := by ring
      rwa [heq] at hdiv
    have hsub := hd1.sub hd2
    have heq : 1 / (1 + t) - 4 / (2 + t) ^ 2 = t ^ 2 / ((1 + t) * (2 + t) ^ 2) := by
      field_simp; ring
    rwa [heq] at hsub
  have hmono : MonotoneOn f (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      rw [(hderiv t ht0).deriv]
      positivity
  have h0 : f 0 ≤ f d := hmono (Set.mem_Ici.mpr le_rfl) hd hd
  simp only [f, add_zero, Real.log_one, mul_zero, zero_div, sub_zero] at h0
  linarith

theorem log_one_add_le_mul_div {d : ℝ} (hd : 0 ≤ d) :
    Real.log (1 + d) ≤ d * (2 + d) / (2 * (1 + d)) := by
  let g : ℝ → ℝ := fun t => t * (2 + t) / (2 * (1 + t)) - Real.log (1 + t)
  have hderiv : ∀ t ∈ Set.Ici (0 : ℝ),
      HasDerivAt g (t ^ 2 / (2 * (1 + t) ^ 2)) t := by
    intro t ht
    have ht0 : 0 ≤ t := ht
    have h1 : 1 + t ≠ 0 := by linarith
    have h2 : 2 * (1 + t) ≠ 0 := by linarith
    have hd1 : HasDerivAt (fun x => x * (2 + x) / (2 * (1 + x)))
        (((1 + t) ^ 2 + 1) / (2 * (1 + t) ^ 2)) t := by
      have ha : HasDerivAt (fun x => x * (2 + x)) (2 + 2 * t) t := by
        have hmul := (hasDerivAt_id t).fun_mul ((hasDerivAt_id t).const_add 2)
        have heq : 1 * (2 + t) + t * 1 = 2 + 2 * t := by ring
        simpa only [id_eq, heq] using hmul
      have hb : HasDerivAt (fun x => 2 * (1 + x)) 2 t := by
        have := ((hasDerivAt_id t).const_add 1).const_mul 2
        simpa using this
      have hdiv := ha.div hb h2
      have heq : ((2 + 2 * t) * (2 * (1 + t)) - t * (2 + t) * 2) / (2 * (1 + t)) ^ 2 =
          ((1 + t) ^ 2 + 1) / (2 * (1 + t) ^ 2) := by
        field_simp; ring
      rwa [heq] at hdiv
    have hd2 : HasDerivAt (fun x => Real.log (1 + x)) (1 / (1 + t)) t := by
      have := ((hasDerivAt_id t).const_add 1).log h1
      simpa using this
    have hsub := hd1.sub hd2
    have heq : ((1 + t) ^ 2 + 1) / (2 * (1 + t) ^ 2) - 1 / (1 + t) =
        t ^ 2 / (2 * (1 + t) ^ 2) := by
      field_simp; ring
    rwa [heq] at hsub
  have hmono : MonotoneOn g (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht0 : 0 ≤ t := interior_subset ht
      rw [(hderiv t ht0).deriv]
      positivity
  have h0 : g 0 ≤ g d := hmono (Set.mem_Ici.mpr le_rfl) hd hd
  simp only [g, zero_mul, zero_div, add_zero, Real.log_one, sub_zero] at h0
  linarith

def logScale : Nat := 1000000000

def logAnchors : List (Nat × Nat × Nat × Nat) := [
  (1, 1, 0, 0),
  (16, 15, 64538518, 64538524),
  (9, 8, 117783033, 117783038),
  (7, 6, 154150678, 154150682),
  (5, 4, 223143550, 223143553),
  (4, 3, 287682071, 287682074),
  (7, 5, 336472235, 336472238),
  (3, 2, 405465107, 405465109),
  (8, 5, 470003627, 470003631),
  (5, 3, 510825623, 510825625),
  (7, 4, 559615786, 559615790),
  (15, 8, 628608657, 628608662)
]

private lemma logAnchors_valid :
    ∀ x ∈ logAnchors, 0 < x.1 ∧ 0 < x.2.1 ∧
      (x.2.2.1 : ℝ) / logScale ≤ Real.log ((x.1 : ℝ) / x.2.1) ∧
      Real.log ((x.1 : ℝ) / x.2.1) ≤ (x.2.2.2 : ℝ) / logScale := by
  have h2lo := Real.log_two_gt_d9
  have h2hi := Real.log_two_lt_d9
  have h3lo := Real.log_three_gt_d9
  have h3hi := Real.log_three_lt_d9
  have h5lo := Real.log_five_gt_d9
  have h5hi := Real.log_five_lt_d9
  have h7lo := log_seven_bounds_aux.1
  have h7hi := log_seven_bounds_aux.2
  intro x hx
  simp only [logAnchors, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    dsimp only <;> push_cast
  · norm_num [logScale]
  · refine ⟨by decide, by decide, ?_, ?_⟩
    · have h : Real.log ((16 : ℝ) / 15) = 4 * Real.log 2 - Real.log 3 - Real.log 5 := by
        rw [Real.log_div (by norm_num) (by norm_num),
            show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow,
            show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        push_cast; ring
      rw [h]; norm_num [logScale]; linarith
    · have h : Real.log ((16 : ℝ) / 15) = 4 * Real.log 2 - Real.log 3 - Real.log 5 := by
        rw [Real.log_div (by norm_num) (by norm_num),
            show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow,
            show (15 : ℝ) = 3 * 5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        push_cast; ring
      rw [h]; norm_num [logScale]; linarith
  · refine ⟨by decide, by decide, ?_, ?_⟩
    · have h : Real.log ((9 : ℝ) / 8) = 2 * Real.log 3 - 3 * Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num),
            show (9 : ℝ) = 3 ^ 2 by norm_num, show (8 : ℝ) = 2 ^ 3 by norm_num,
            Real.log_pow, Real.log_pow]
        push_cast; ring
      rw [h]; norm_num [logScale]; linarith
    · have h : Real.log ((9 : ℝ) / 8) = 2 * Real.log 3 - 3 * Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num),
            show (9 : ℝ) = 3 ^ 2 by norm_num, show (8 : ℝ) = 2 ^ 3 by norm_num,
            Real.log_pow, Real.log_pow]
        push_cast; ring
      rw [h]; norm_num [logScale]; linarith
  · refine ⟨by decide, by decide, ?_, ?_⟩
    · have h : Real.log ((7 : ℝ) / 6) = Real.log 7 - Real.log 2 - Real.log 3 := by
        rw [Real.log_div (by norm_num) (by norm_num),
            show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        ring
      rw [h]; norm_num [logScale]; linarith
    · have h : Real.log ((7 : ℝ) / 6) = Real.log 7 - Real.log 2 - Real.log 3 := by
        rw [Real.log_div (by norm_num) (by norm_num),
            show (6 : ℝ) = 2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
        ring
      rw [h]; norm_num [logScale]; linarith
  · refine ⟨by decide, by decide, ?_, ?_⟩
    · have h : Real.log ((5 : ℝ) / 4) = Real.log 5 - 2 * Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_four_eq]
      rw [h]; norm_num [logScale]; linarith
    · have h : Real.log ((5 : ℝ) / 4) = Real.log 5 - 2 * Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_four_eq]
      rw [h]; norm_num [logScale]; linarith
  · refine ⟨by decide, by decide, ?_, ?_⟩
    · have h : Real.log ((4 : ℝ) / 3) = 2 * Real.log 2 - Real.log 3 := by
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_four_eq]
      rw [h]; norm_num [logScale]; linarith
    · have h : Real.log ((4 : ℝ) / 3) = 2 * Real.log 2 - Real.log 3 := by
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_four_eq]
      rw [h]; norm_num [logScale]; linarith
  · refine ⟨by decide, by decide, ?_, ?_⟩
    · rw [Real.log_div (by norm_num) (by norm_num)]; norm_num [logScale]; linarith
    · rw [Real.log_div (by norm_num) (by norm_num)]; norm_num [logScale]; linarith
  · refine ⟨by decide, by decide, ?_, ?_⟩
    · rw [Real.log_div (by norm_num) (by norm_num)]; norm_num [logScale]; linarith
    · rw [Real.log_div (by norm_num) (by norm_num)]; norm_num [logScale]; linarith
  · refine ⟨by decide, by decide, ?_, ?_⟩
    · have h : Real.log ((8 : ℝ) / 5) = 3 * Real.log 2 - Real.log 5 := by
        rw [Real.log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        push_cast; ring
      rw [h]; norm_num [logScale]; linarith
    · have h : Real.log ((8 : ℝ) / 5) = 3 * Real.log 2 - Real.log 5 := by
        rw [Real.log_div (by norm_num) (by norm_num), show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
        push_cast; ring
      rw [h]; norm_num [logScale]; linarith
  · refine ⟨by decide, by decide, ?_, ?_⟩
    · rw [Real.log_div (by norm_num) (by norm_num)]; norm_num [logScale]; linarith
    · rw [Real.log_div (by norm_num) (by norm_num)]; norm_num [logScale]; linarith
  · refine ⟨by decide, by decide, ?_, ?_⟩
    · have h : Real.log ((7 : ℝ) / 4) = Real.log 7 - 2 * Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_four_eq]
      rw [h]; norm_num [logScale]; linarith
    · have h : Real.log ((7 : ℝ) / 4) = Real.log 7 - 2 * Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num), Real.log_four_eq]
      rw [h]; norm_num [logScale]; linarith
  · refine ⟨by decide, by decide, ?_, ?_⟩
    · have h : Real.log ((15 : ℝ) / 8) = Real.log 3 + Real.log 5 - 3 * Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num),
            show (15 : ℝ) = 3 * 5 by norm_num, show (8 : ℝ) = 2 ^ 3 by norm_num,
            Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
        push_cast; ring
      rw [h]; norm_num [logScale]; linarith
    · have h : Real.log ((15 : ℝ) / 8) = Real.log 3 + Real.log 5 - 3 * Real.log 2 := by
        rw [Real.log_div (by norm_num) (by norm_num),
            show (15 : ℝ) = 3 * 5 by norm_num, show (8 : ℝ) = 2 ^ 3 by norm_num,
            Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
        push_cast; ring
      rw [h]; norm_num [logScale]; linarith

private def pickAnchorAux (a bp2 : Nat) (cur : Nat × Nat × Nat × Nat) :
    List (Nat × Nat × Nat × Nat) → Nat × Nat × Nat × Nat
  | [] => cur
  | x :: xs =>
    if x.1 * bp2 ≤ a * x.2.1 then pickAnchorAux a bp2 x xs
    else pickAnchorAux a bp2 cur xs

private lemma pickAnchorAux_spec (a bp2 : Nat) (cur : Nat × Nat × Nat × Nat)
    (L : List (Nat × Nat × Nat × Nat))
    (hcur_mem : cur ∈ logAnchors) (hcur_le : cur.1 * bp2 ≤ a * cur.2.1)
    (hL : ∀ x ∈ L, x ∈ logAnchors) :
    let res := pickAnchorAux a bp2 cur L
    res ∈ logAnchors ∧ res.1 * bp2 ≤ a * res.2.1 := by
  induction L generalizing cur with
  | nil => exact ⟨hcur_mem, hcur_le⟩
  | cons x xs ih =>
    unfold pickAnchorAux
    split
    · next hle =>
      exact ih x (hL x (by simp)) hle (fun y hy => hL y (List.mem_cons_of_mem _ hy))
    · next _ =>
      exact ih cur hcur_mem hcur_le (fun y hy => hL y (List.mem_cons_of_mem _ hy))

/-- Computable scaled `[lo, hi]` bounds for `Real.log (a / b)` (`1 ≤ b ≤ a`), scaled by `10^9`. -/
def logRatBounds (a b : Nat) : Nat × Nat :=
  let k := (a / b).log2
  let bp2 := b * (1 <<< k)
  let anch := pickAnchorAux a bp2 (1, 1, 0, 0) logAnchors
  let num := anch.1
  let den := anch.2.1
  let alo := anch.2.2.1
  let ahi := anch.2.2.2
  let P := a * den - num * bp2
  let Q := num * bp2
  let dlo := (2 * P * logScale) / (2 * Q + P)
  let dhi := (P * (2 * Q + P) * logScale + 2 * Q * (Q + P) - 1) / (2 * Q * (Q + P))
  (k * 693147180 + alo + dlo, k * 693147181 + ahi + dhi)

def logRatLo (a b : Nat) : Nat := (logRatBounds a b).1
def logRatHi (a b : Nat) : Nat := (logRatBounds a b).2
def logNatLo (n : Nat) : Nat := logRatLo n 1
def logNatHi (n : Nat) : Nat := logRatHi n 1

theorem logRatBounds_correct {a b : Nat} (hb : 1 ≤ b) (hab : b ≤ a) :
    ((logRatLo a b : ℝ) / logScale) ≤ Real.log ((a : ℝ) / b) ∧
    Real.log ((a : ℝ) / b) ≤ ((logRatHi a b : ℝ) / logScale) := by
  unfold logRatLo logRatHi logRatBounds
  set k := (a / b).log2
  set bp2 := b * (1 <<< k)
  have hq_pos : 0 < a / b := Nat.div_pos hab hb
  have h2k_le : 2 ^ k ≤ a / b := Nat.log2_self_le hq_pos.ne'
  have hbp2_le : bp2 ≤ a := by
    have h1 : 1 <<< k = 2 ^ k := by simp [Nat.shiftLeft_eq]
    rw [show bp2 = b * (1 <<< k) from rfl, h1]
    have := (Nat.le_div_iff_mul_le hb).mp h2k_le
    nlinarith
  have hpick := pickAnchorAux_spec a bp2 (1, 1, 0, 0) logAnchors (by simp [logAnchors])
    (by simpa using hbp2_le) (fun x hx => hx)
  set anch := pickAnchorAux a bp2 (1, 1, 0, 0) logAnchors
  obtain ⟨hnum_pos, hden_pos, halo_le, hahi_ge⟩ := logAnchors_valid anch hpick.1
  have hQ_pos : 0 < anch.1 * bp2 := by
    have : 0 < bp2 := by
      have : 1 <<< k = 2 ^ k := by simp [Nat.shiftLeft_eq]
      rw [show bp2 = b * (1 <<< k) from rfl, this]; positivity
    exact Nat.mul_pos hnum_pos this
  set P := a * anch.2.1 - anch.1 * bp2
  set Q := anch.1 * bp2
  have hPQ : a * anch.2.1 = Q + P := by
    have := hpick.2; omega
  have hbp2_real : (bp2 : ℝ) = (b : ℝ) * (2 : ℝ) ^ k := by
    have : 1 <<< k = 2 ^ k := by simp [Nat.shiftLeft_eq]
    rw [show bp2 = b * (1 <<< k) from rfl, this]; push_cast; rfl
  have ha_pos : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb_pos : (0 : ℝ) < b := by exact_mod_cast hb
  have hnum_posR : (0 : ℝ) < anch.1 := by exact_mod_cast hnum_pos
  have hden_posR : (0 : ℝ) < anch.2.1 := by exact_mod_cast hden_pos
  have hQ_posR : (0 : ℝ) < Q := by exact_mod_cast hQ_pos
  have hP_nnR : (0 : ℝ) ≤ P := Nat.cast_nonneg P
  have hfac : (a : ℝ) / b = (2 : ℝ) ^ k * ((anch.1 : ℝ) / anch.2.1) * (1 + (P : ℝ) / Q) := by
    have hPQ_R : (a : ℝ) * anch.2.1 = (Q : ℝ) + P := by exact_mod_cast hPQ
    have hQ_R : (Q : ℝ) = (anch.1 : ℝ) * (b : ℝ) * (2 : ℝ) ^ k := by
      calc (Q : ℝ) = (anch.1 : ℝ) * bp2 := by exact_mod_cast (rfl : Q = anch.1 * bp2)
        _ = (anch.1 : ℝ) * ((b : ℝ) * (2 : ℝ) ^ k) := by rw [hbp2_real]
        _ = _ := by ring
    field_simp
    nlinarith
  have hlog_eq : Real.log ((a : ℝ) / b) =
      (k : ℝ) * Real.log 2 + Real.log ((anch.1 : ℝ) / anch.2.1) + Real.log (1 + (P : ℝ) / Q) := by
    rw [hfac, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hd_lo := two_mul_div_add_le_log_one_add (show (0 : ℝ) ≤ (P : ℝ) / Q by positivity)
  have hd_hi := log_one_add_le_mul_div (show (0 : ℝ) ≤ (P : ℝ) / Q by positivity)
  have hlog2_lo : (693147180 : ℝ) / logScale ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num [logScale]; linarith
  have hlog2_hi : Real.log 2 ≤ (693147181 : ℝ) / logScale := by
    have := Real.log_two_lt_d9; norm_num [logScale]; linarith
  have hS_pos : (0 : ℝ) < logScale := by norm_num [logScale]
  dsimp only
  constructor
  · have hdlo_le : (((2 * P * logScale) / (2 * Q + P) : Nat) : ℝ) / logScale ≤
        2 * ((P : ℝ) / Q) / (2 + (P : ℝ) / Q) := by
      have hden_pos' : 0 < 2 * Q + P := by omega
      have hdiv_le : (((2 * P * logScale) / (2 * Q + P) : Nat) : ℝ) * (2 * Q + P) ≤
          2 * P * logScale := by
        exact_mod_cast Nat.div_mul_le_self (2 * P * logScale) (2 * Q + P)
      have h1 : (((2 * P * logScale) / (2 * Q + P) : Nat) : ℝ) / logScale ≤
          (2 * (P : ℝ)) / (2 * Q + P) := by
        rw [div_le_div_iff₀ hS_pos (by positivity)]
        linarith
      have h2 : (2 * (P : ℝ)) / (2 * Q + P) = 2 * ((P : ℝ) / Q) / (2 + (P : ℝ) / Q) := by
        field_simp
      linarith
    have hk_le : (k : ℝ) * (693147180 : ℝ) / logScale ≤ (k : ℝ) * Real.log 2 := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hlog2_lo (Nat.cast_nonneg k)
    rw [hlog_eq]
    push_cast
    rw [add_div, add_div]
    linarith
  · have hdhi_ge : ((P : ℝ) / Q) * (2 + (P : ℝ) / Q) / (2 * (1 + (P : ℝ) / Q)) ≤
        (((P * (2 * Q + P) * logScale + 2 * Q * (Q + P) - 1) / (2 * Q * (Q + P)) : Nat) : ℝ) /
          logScale := by
      have hden_pos' : 0 < 2 * Q * (Q + P) := by positivity
      have hceil : P * (2 * Q + P) * logScale ≤
          ((P * (2 * Q + P) * logScale + 2 * Q * (Q + P) - 1) / (2 * Q * (Q + P))) *
            (2 * Q * (Q + P)) := by
        have hmod := Nat.div_add_mod (P * (2 * Q + P) * logScale + 2 * Q * (Q + P) - 1) (2 * Q * (Q + P))
        have hlt := Nat.mod_lt (P * (2 * Q + P) * logScale + 2 * Q * (Q + P) - 1) hden_pos'
        rw [Nat.mul_comm] at hmod
        omega
      have hceilR : (P : ℝ) * (2 * Q + P) * logScale ≤
          (((P * (2 * Q + P) * logScale + 2 * Q * (Q + P) - 1) / (2 * Q * (Q + P)) : Nat) : ℝ) *
            (2 * Q * (Q + P)) := by exact_mod_cast hceil
      have h1 : (P : ℝ) * (2 * Q + P) / (2 * Q * (Q + P)) ≤
          (((P * (2 * Q + P) * logScale + 2 * Q * (Q + P) - 1) / (2 * Q * (Q + P)) : Nat) : ℝ) /
            logScale := by
        rw [div_le_div_iff₀ (by positivity) hS_pos]
        linarith
      have h2 : ((P : ℝ) / Q) * (2 + (P : ℝ) / Q) / (2 * (1 + (P : ℝ) / Q)) =
          (P : ℝ) * (2 * Q + P) / (2 * Q * (Q + P)) := by
        field_simp
      linarith
    have hk_ge : (k : ℝ) * Real.log 2 ≤ (k : ℝ) * (693147181 : ℝ) / logScale := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hlog2_hi (Nat.cast_nonneg k)
    rw [hlog_eq]
    push_cast
    rw [add_div, add_div]
    linarith

/- ### Part 2: FTC antiderivatives and zero-constant `π(x)` bounds for `x ≥ 10^7` -/

private lemma integral_one_div_log_sq_lower {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    b / (Real.log b) ^ 2 - a / (Real.log a) ^ 2 ≤ ∫ t in a..b, 1 / (Real.log t) ^ 2 := by
  let F : ℝ → ℝ := fun t => t / (Real.log t) ^ 2
  let F' : ℝ → ℝ := fun t => (Real.log t - 2) / (Real.log t) ^ 3
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt F (F' t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have hlog_ne : Real.log t ≠ 0 := hlog_pos.ne'
    have hd_sq : HasDerivAt (fun x => (Real.log x) ^ 2) (2 * Real.log t / t) t := by
      have hp := (Real.hasDerivAt_log ht0).pow 2
      have heq : (2 : ℝ) * (Real.log t) ^ (2 - 1) * t⁻¹ = 2 * Real.log t / t := by
        simp [div_eq_mul_inv]
      simpa only [Nat.cast_ofNat] using heq ▸ hp
    have hdiv := (hasDerivAt_id t).fun_div hd_sq (pow_ne_zero 2 hlog_ne)
    have heq : (1 * (Real.log t) ^ 2 - t * (2 * Real.log t / t)) / ((Real.log t) ^ 2) ^ 2 = F' t := by
      dsimp only [F']; field_simp
    simpa only [id_eq, heq] using hdiv
  have hcont : ContinuousOn F' (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog_ne : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have h3 : (Real.log t) ^ 3 ≠ 0 := pow_ne_zero 3 hlog_ne
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [← hftc]
  apply intervalIntegral.integral_mono_on hab hcont.intervalIntegrable
    (Chebyshev.intervalIntegrable_one_div_log_sq (by linarith) (by linarith))
  intro t ht
  have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
  dsimp only [F']
  rw [div_le_div_iff₀ (pow_pos hlog_pos 3) (pow_pos hlog_pos 2)]
  nlinarith

private lemma integral_one_div_log_sq_upper {a b : ℝ} (ha : (10 ^ 7 : ℝ) ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / (Real.log t) ^ 2 ≤
      (b / (Real.log b) ^ 2 + 3 * b / (Real.log b) ^ 3) -
      (a / (Real.log a) ^ 2 + 3 * a / (Real.log a) ^ 3) := by
  let G : ℝ → ℝ := fun t => t / (Real.log t) ^ 2 + 3 * t / (Real.log t) ^ 3
  let G' : ℝ → ℝ := fun t => 1 / (Real.log t) ^ 2 + (Real.log t - 9) / (Real.log t) ^ 4
  have hlog_ge9 : ∀ t : ℝ, (10 ^ 7 : ℝ) ≤ t → 9 ≤ Real.log t := by
    intro t ht
    have h1 : Real.log (10 ^ 7 : ℝ) ≤ Real.log t := Real.log_le_log (by positivity) ht
    have h2 : Real.log (10 ^ 7 : ℝ) = 7 * (Real.log 2 + Real.log 5) := by
      rw [Real.log_pow, Real.log_ten_eq]; push_cast; ring
    have := Real.log_two_gt_d9
    have := Real.log_five_gt_d9
    linarith
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt G (G' t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog_pos : 0 < Real.log t := by linarith [hlog_ge9 t (by linarith [ht.1])]
    have hlog_ne : Real.log t ≠ 0 := hlog_pos.ne'
    have hd2 : HasDerivAt (fun x => x / (Real.log x) ^ 2)
        ((Real.log t - 2) / (Real.log t) ^ 3) t := by
      have hd_sq : HasDerivAt (fun x => (Real.log x) ^ 2) (2 * Real.log t / t) t := by
        have hp := (Real.hasDerivAt_log ht0).pow 2
        have heq : (2 : ℝ) * (Real.log t) ^ (2 - 1) * t⁻¹ = 2 * Real.log t / t := by
          simp [div_eq_mul_inv]
        simpa only [Nat.cast_ofNat] using heq ▸ hp
      have hdiv := (hasDerivAt_id t).fun_div hd_sq (pow_ne_zero 2 hlog_ne)
      have heq : (1 * (Real.log t) ^ 2 - t * (2 * Real.log t / t)) / ((Real.log t) ^ 2) ^ 2 =
          (Real.log t - 2) / (Real.log t) ^ 3 := by field_simp
      simpa only [id_eq, heq] using hdiv
    have hd3 : HasDerivAt (fun x => 3 * x / (Real.log x) ^ 3)
        (3 * (Real.log t - 3) / (Real.log t) ^ 4) t := by
      have hnum : HasDerivAt (fun x => 3 * x) 3 t := by simpa using (hasDerivAt_id t).const_mul 3
      have hd_cb : HasDerivAt (fun x => (Real.log x) ^ 3) (3 * (Real.log t) ^ 2 / t) t := by
        have hp := (Real.hasDerivAt_log ht0).pow 3
        have heq : (3 : ℝ) * (Real.log t) ^ (3 - 1) * t⁻¹ = 3 * (Real.log t) ^ 2 / t := by
          simp [div_eq_mul_inv]
        simpa only [Nat.cast_ofNat] using heq ▸ hp
      have hdiv := hnum.fun_div hd_cb (pow_ne_zero 3 hlog_ne)
      have heq : (3 * (Real.log t) ^ 3 - 3 * t * (3 * (Real.log t) ^ 2 / t)) / ((Real.log t) ^ 3) ^ 2 =
          3 * (Real.log t - 3) / (Real.log t) ^ 4 := by field_simp
      simpa only [heq] using hdiv
    have hadd := hd2.fun_add hd3
    have heq : (Real.log t - 2) / (Real.log t) ^ 3 + 3 * (Real.log t - 3) / (Real.log t) ^ 4 = G' t := by
      dsimp only [G']; field_simp; ring
    simpa only [heq] using hadd
  have hcont : ContinuousOn G' (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog_ne : Real.log t ≠ 0 := (by linarith [hlog_ge9 t (by linarith [ht.1])] : 0 < Real.log t).ne'
    have h2 : (Real.log t) ^ 2 ≠ 0 := pow_ne_zero 2 hlog_ne
    have h4 : (Real.log t) ^ 4 ≠ 0 := pow_ne_zero 4 hlog_ne
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable
  rw [← hftc]
  apply intervalIntegral.integral_mono_on hab
    (Chebyshev.intervalIntegrable_one_div_log_sq (by linarith) (by linarith))
    hcont.intervalIntegrable
  intro t ht
  have h9 : 9 ≤ Real.log t := hlog_ge9 t (by linarith [ht.1])
  have hlog_pos : 0 < Real.log t := by linarith
  dsimp only [G']
  have hnn : 0 ≤ (Real.log t - 9) / (Real.log t) ^ 4 := div_nonneg (by linarith) (by positivity)
  linarith

private lemma log_10M_bounds :
    (16.1180956 : ℝ) < Real.log (10 ^ 7 : ℝ) ∧ Real.log (10 ^ 7 : ℝ) < 16.1180957 := by
  have h : Real.log (10 ^ 7 : ℝ) = 7 * (Real.log 2 + Real.log 5) := by
    rw [Real.log_pow, Real.log_ten_eq]; push_cast; ring
  have := Real.log_two_gt_d9
  have := Real.log_two_lt_d9
  have := Real.log_five_gt_d9
  have := Real.log_five_lt_d9
  rw [h]
  constructor <;> linarith

private lemma intervalIntegrable_theta_div {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t => θ t / (t * (Real.log t) ^ 2)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact (Chebyshev.integrableOn_theta_div_id_mul_log_sq b).mono_set
    (Set.Icc_subset_Icc_left ha)

theorem pi_lower_10M
    (htheta_lo : ∀ t : ℝ, (10 ^ 7 : ℝ) ≤ t → 0.9400 * t ≤ θ t)
    (hI_lo : (36183 : ℝ) ≤ ∫ t in (2 : ℝ)..(10 ^ 7 : ℝ), θ t / (t * (Real.log t) ^ 2))
    {x : ℝ} (hx : (10 ^ 7 : ℝ) ≤ x) :
    0.9400 * (x / Real.log x + x / (Real.log x) ^ 2) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hx2 : 2 ≤ x := by linarith
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2]
  have hsplit : ∫ t in (2 : ℝ)..x, θ t / (t * (Real.log t) ^ 2) =
      (∫ t in (2 : ℝ)..(10 ^ 7 : ℝ), θ t / (t * (Real.log t) ^ 2)) +
      (∫ t in (10 ^ 7 : ℝ)..x, θ t / (t * (Real.log t) ^ 2)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_theta_div le_rfl (by norm_num))
      (intervalIntegrable_theta_div (by norm_num) hx)).symm
  rw [hsplit]
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hmain : 0.9400 * (x / Real.log x) ≤ θ x / Real.log x := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (htheta_lo x hx) hlogx_pos.le
  have hint : 0.9400 * (x / (Real.log x) ^ 2 - (10 ^ 7 : ℝ) / (Real.log (10 ^ 7 : ℝ)) ^ 2) ≤
      ∫ t in (10 ^ 7 : ℝ)..x, θ t / (t * (Real.log t) ^ 2) := by
    calc 0.9400 * (x / (Real.log x) ^ 2 - (10 ^ 7 : ℝ) / (Real.log (10 ^ 7 : ℝ)) ^ 2)
        ≤ 0.9400 * ∫ t in (10 ^ 7 : ℝ)..x, 1 / (Real.log t) ^ 2 :=
          mul_le_mul_of_nonneg_left (integral_one_div_log_sq_lower (by norm_num) hx) (by norm_num)
      _ = ∫ t in (10 ^ 7 : ℝ)..x, 0.9400 * (1 / (Real.log t) ^ 2) :=
          (intervalIntegral.integral_const_mul _ _).symm
      _ ≤ ∫ t in (10 ^ 7 : ℝ)..x, θ t / (t * (Real.log t) ^ 2) := by
          apply intervalIntegral.integral_mono_on hx
            ((Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)).const_mul _)
            (intervalIntegrable_theta_div (by norm_num) hx)
          intro t ht
          have ht0 : 0 < t := by linarith [ht.1]
          have hlogt_pos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
          have hth := htheta_lo t ht.1
          have h1 : 0.9400 * (1 / (Real.log t) ^ 2) = (0.9400 * t) / (t * (Real.log t) ^ 2) := by
            field_simp
          rw [h1]
          exact div_le_div_of_nonneg_right hth (by positivity)
  have hconst : 0.9400 * ((10 ^ 7 : ℝ) / (Real.log (10 ^ 7 : ℝ)) ^ 2) ≤ 36183 := by
    have hlog := log_10M_bounds.1
    have hsq : (16.1180956 : ℝ) ^ 2 ≤ (Real.log (10 ^ 7 : ℝ)) ^ 2 :=
      pow_le_pow_left₀ (by norm_num) hlog.le 2
    rw [mul_div_assoc', div_le_iff₀ (by positivity)]
    nlinarith
  linarith

theorem pi_upper_10M
    (htheta_hi : ∀ t : ℝ, (10 ^ 7 : ℝ) ≤ t → θ t ≤ 1.0562 * t)
    (hI_hi : ∫ t in (2 : ℝ)..(10 ^ 7 : ℝ), θ t / (t * (Real.log t) ^ 2) ≤ 48222)
    {x : ℝ} (hx : (10 ^ 7 : ℝ) ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      1.0562 * (x / Real.log x + x / (Real.log x) ^ 2 + 3 * x / (Real.log x) ^ 3) := by
  have hx2 : 2 ≤ x := by linarith
  rw [Chebyshev.primeCounting_eq_theta_div_log_add_integral hx2]
  have hsplit : ∫ t in (2 : ℝ)..x, θ t / (t * (Real.log t) ^ 2) =
      (∫ t in (2 : ℝ)..(10 ^ 7 : ℝ), θ t / (t * (Real.log t) ^ 2)) +
      (∫ t in (10 ^ 7 : ℝ)..x, θ t / (t * (Real.log t) ^ 2)) :=
    (intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_theta_div le_rfl (by norm_num))
      (intervalIntegrable_theta_div (by norm_num) hx)).symm
  rw [hsplit]
  have hlogx_pos : 0 < Real.log x := Real.log_pos (by linarith)
  have hmain : θ x / Real.log x ≤ 1.0562 * (x / Real.log x) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (htheta_hi x hx) hlogx_pos.le
  have hint : ∫ t in (10 ^ 7 : ℝ)..x, θ t / (t * (Real.log t) ^ 2) ≤
      1.0562 * ((x / (Real.log x) ^ 2 + 3 * x / (Real.log x) ^ 3) -
        ((10 ^ 7 : ℝ) / (Real.log (10 ^ 7 : ℝ)) ^ 2 +
          3 * (10 ^ 7 : ℝ) / (Real.log (10 ^ 7 : ℝ)) ^ 3)) := by
    calc ∫ t in (10 ^ 7 : ℝ)..x, θ t / (t * (Real.log t) ^ 2)
        ≤ ∫ t in (10 ^ 7 : ℝ)..x, 1.0562 * (1 / (Real.log t) ^ 2) := by
          apply intervalIntegral.integral_mono_on hx
            (intervalIntegrable_theta_div (by norm_num) hx)
            ((Chebyshev.intervalIntegrable_one_div_log_sq (by norm_num) (by linarith)).const_mul _)
          intro t ht
          have ht0 : 0 < t := by linarith [ht.1]
          have hlogt_pos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
          have hth := htheta_hi t ht.1
          have h1 : 1.0562 * (1 / (Real.log t) ^ 2) = (1.0562 * t) / (t * (Real.log t) ^ 2) := by
            field_simp
          rw [h1]
          exact div_le_div_of_nonneg_right hth (by positivity)
      _ = 1.0562 * ∫ t in (10 ^ 7 : ℝ)..x, 1 / (Real.log t) ^ 2 :=
          intervalIntegral.integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (integral_one_div_log_sq_upper le_rfl hx) (by norm_num)
  have hconst : 48222 ≤ 1.0562 * ((10 ^ 7 : ℝ) / (Real.log (10 ^ 7 : ℝ)) ^ 2 +
      3 * (10 ^ 7 : ℝ) / (Real.log (10 ^ 7 : ℝ)) ^ 3) := by
    have hlog := log_10M_bounds.2
    have hlog_pos : 0 < Real.log (10 ^ 7 : ℝ) := Real.log_pos (by norm_num)
    have hsq : (Real.log (10 ^ 7 : ℝ)) ^ 2 ≤ (16.1180957 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hlog_pos.le hlog.le 2
    have hcb : (Real.log (10 ^ 7 : ℝ)) ^ 3 ≤ (16.1180957 : ℝ) ^ 3 :=
      pow_le_pow_left₀ hlog_pos.le hlog.le 3
    have h1 : (10 ^ 7 : ℝ) / (16.1180957 : ℝ) ^ 2 ≤ (10 ^ 7 : ℝ) / (Real.log (10 ^ 7 : ℝ)) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
    have h2 : 3 * (10 ^ 7 : ℝ) / (16.1180957 : ℝ) ^ 3 ≤
        3 * (10 ^ 7 : ℝ) / (Real.log (10 ^ 7 : ℝ)) ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hcb
    norm_num at h1 h2
    linarith
  linarith

/- ### Part 3: Helper to pin `∫_2^{10^7} θ(t)/(t log^2 t) dt` from breakpoint `π` table -/

private lemma integrableOn_pi_div_id {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Nat.primeCounting ⌊t⌋₊ : ℝ) / t) volume a b := by
  have h1 : MonotoneOn (fun t : ℝ => (Nat.primeCounting ⌊t⌋₊ : ℝ)) (Set.uIcc a b) := by
    intro x _ y _ hxy
    dsimp only
    exact_mod_cast Nat.monotone_primeCounting (Nat.floor_mono hxy)
  have h2 : ContinuousOn (fun t : ℝ => (t : ℝ)⁻¹) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    exact (continuousAt_inv₀ (by linarith [ht.1])).continuousWithinAt
  have hint : IntervalIntegrable (fun t : ℝ => (Nat.primeCounting ⌊t⌋₊ : ℝ) * t⁻¹) volume a b :=
    (h1.intervalIntegrable (μ := volume)).mul_continuousOn h2
  convert hint using 1
  ext t; rw [div_eq_mul_inv]

private lemma integral_pi_div_segment {a b : ℕ} (ha : 2 ≤ a) (hab : a ≤ b) :
    (a.primeCounting : ℝ) * Real.log ((b : ℝ) / a) ≤
      ∫ t in (a : ℝ)..(b : ℝ), (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ∧
    ∫ t in (a : ℝ)..(b : ℝ), (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ≤
      (b.primeCounting : ℝ) * Real.log ((b : ℝ) / a) := by
  have haR : (2 : ℝ) ≤ a := by exact_mod_cast ha
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  have ha0 : (0 : ℝ) < a := by linarith
  have hb0 : (0 : ℝ) < b := by linarith
  have hlog : ∫ t in (a : ℝ)..(b : ℝ), (1 : ℝ) / t = Real.log ((b : ℝ) / a) := by
    rw [integral_one_div_of_pos ha0 hb0]
  have hint_inv : IntervalIntegrable (fun t : ℝ => (1 : ℝ) / t) volume (a : ℝ) (b : ℝ) := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le habR]
    intro t ht
    exact ContinuousAt.continuousWithinAt (by fun_prop (disch := linarith [ht.1]))
  constructor
  · calc (a.primeCounting : ℝ) * Real.log ((b : ℝ) / a)
        = ∫ t in (a : ℝ)..(b : ℝ), (a.primeCounting : ℝ) * (1 / t) := by
          rw [intervalIntegral.integral_const_mul, hlog]
      _ ≤ ∫ t in (a : ℝ)..(b : ℝ), (Nat.primeCounting ⌊t⌋₊ : ℝ) / t := by
          apply intervalIntegral.integral_mono_on habR (hint_inv.const_mul _)
            (integrableOn_pi_div_id haR habR)
          intro t ht
          have hfl : a ≤ ⌊t⌋₊ := Nat.le_floor ht.1
          have hpi : (a.primeCounting : ℝ) ≤ (Nat.primeCounting ⌊t⌋₊ : ℝ) := by
            exact_mod_cast Nat.monotone_primeCounting hfl
          have ht0 : 0 < t := by linarith [ht.1]
          rw [mul_one_div]
          exact div_le_div_of_nonneg_right hpi ht0.le
  · calc ∫ t in (a : ℝ)..(b : ℝ), (Nat.primeCounting ⌊t⌋₊ : ℝ) / t
        ≤ ∫ t in (a : ℝ)..(b : ℝ), (b.primeCounting : ℝ) * (1 / t) := by
          apply intervalIntegral.integral_mono_on habR
            (integrableOn_pi_div_id haR habR) (hint_inv.const_mul _)
          intro t ht
          have hfl : ⌊t⌋₊ ≤ b := Nat.floor_le_of_le ht.2
          have hpi : (Nat.primeCounting ⌊t⌋₊ : ℝ) ≤ (b.primeCounting : ℝ) := by
            exact_mod_cast Nat.monotone_primeCounting hfl
          have ht0 : 0 < t := by linarith [ht.1]
          rw [mul_one_div]
          exact div_le_div_of_nonneg_right hpi ht0.le
      _ = (b.primeCounting : ℝ) * Real.log ((b : ℝ) / a) := by
          rw [intervalIntegral.integral_const_mul, hlog]

def piIntLoSum : List (Nat × Nat) → Nat
  | [] => 0
  | [_] => 0
  | (a, pa) :: (b, pb) :: rest => pa * logRatLo b a + piIntLoSum ((b, pb) :: rest)

def piIntHiSum : List (Nat × Nat) → Nat
  | [] => 0
  | [_] => 0
  | (a, _pa) :: (b, pb) :: rest => pb * logRatHi b a + piIntHiSum ((b, pb) :: rest)

theorem piInt_chain_bounds :
    ∀ (pts : List (Nat × Nat)) (a _pa b pb : Nat),
      pts.head? = some (a, _pa) → pts.getLast? = some (b, pb) →
      2 ≤ a →
      (∀ p ∈ pts, p.2 = p.1.primeCounting) →
      pts.IsChain (fun p q => p.1 ≤ q.1) →
      ((piIntLoSum pts : ℝ) / logScale) ≤
        ∫ t in (a : ℝ)..(b : ℝ), (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ∧
      ∫ t in (a : ℝ)..(b : ℝ), (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ≤
        ((piIntHiSum pts : ℝ) / logScale) := by
  intro pts
  induction pts with
  | nil => intro _ _ _ _ h; simp at h
  | cons p rest ih =>
    rcases rest with _ | ⟨q, rest'⟩
    · intro a _pa b pb h1 h2 _ _ _
      simp only [List.head?_cons, Option.some.injEq] at h1
      simp only [List.getLast?_singleton, Option.some.injEq] at h2
      rcases h1 with rfl
      injection h2 with h2'; rcases h2' with rfl
      simp [piIntLoSum, piIntHiSum]
    · intro a _pa b pb hhead hlast ha2 hpi hchain
      simp only [List.head?_cons, Option.some.injEq] at hhead
      have hp1 : p.1 = a := congrArg Prod.fst hhead
      have hlast' : (q :: rest').getLast? = some (b, pb) := by
        simpa [List.getLast?_cons_cons] using hlast
      have hpq : p.1 ≤ q.1 := (List.isChain_cons_cons.mp hchain).1
      have hchain' : (q :: rest').IsChain (fun x y => x.1 ≤ y.1) :=
        (List.isChain_cons_cons.mp hchain).2
      have hpi' : ∀ x ∈ q :: rest', x.2 = x.1.primeCounting :=
        fun x hx => hpi x (List.mem_cons_of_mem _ hx)
      have hrec := ih q.1 q.2 b pb rfl hlast' (by omega) hpi' hchain'
      have hqb : q.1 ≤ b := by
        have hmem : ∀ (L : List (Nat × Nat)) (u v : Nat × Nat),
            L.head? = some u → L.getLast? = some v → L.IsChain (fun x y => x.1 ≤ y.1) → u.1 ≤ v.1 := by
          intro L
          induction L with
          | nil => intro _ _ h; simp at h
          | cons x xs ihL =>
            rcases xs with _ | ⟨y, ys⟩
            · intro u v hu hv _
              simp at hu hv; subst hu; subst hv; exact le_rfl
            · intro u v hu hv hc
              simp at hu; subst hu
              have hxy := (List.isChain_cons_cons.mp hc).1
              have hy := ihL y v rfl (by simpa [List.getLast?_cons_cons] using hv)
                (List.isChain_cons_cons.mp hc).2
              omega
        exact hmem (q :: rest') q (b, pb) rfl hlast' hchain'
      rw [← hp1]
      have hsplit : ∫ t in (p.1 : ℝ)..(b : ℝ), (Nat.primeCounting ⌊t⌋₊ : ℝ) / t =
          (∫ t in (p.1 : ℝ)..(q.1 : ℝ), (Nat.primeCounting ⌊t⌋₊ : ℝ) / t) +
          (∫ t in (q.1 : ℝ)..(b : ℝ), (Nat.primeCounting ⌊t⌋₊ : ℝ) / t) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (integrableOn_pi_div_id (by exact_mod_cast (show 2 ≤ p.1 by omega)) (by exact_mod_cast hpq))
          (integrableOn_pi_div_id (by exact_mod_cast (show 2 ≤ q.1 by omega))
            (by exact_mod_cast hqb))).symm
      obtain ⟨hseg_lo, hseg_hi⟩ := integral_pi_div_segment (by omega : 2 ≤ p.1) hpq
      obtain ⟨hlog_lo, hlog_hi⟩ := logRatBounds_correct (by omega : 1 ≤ p.1) hpq
      have hp_eq : p.2 = p.1.primeCounting := hpi p (by simp)
      have hq_eq : q.2 = q.1.primeCounting := hpi q (by simp)
      rw [hsplit]
      unfold piIntLoSum piIntHiSum
      push_cast
      rw [add_div, add_div]
      constructor
      · have hmul : (p.2 : ℝ) * (logRatLo q.1 p.1 : ℝ) / logScale ≤
            (p.1.primeCounting : ℝ) * Real.log ((q.1 : ℝ) / p.1) := by
          rw [hp_eq, mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hlog_lo (Nat.cast_nonneg _)
        linarith [hrec.1]
      · have hmul : (q.1.primeCounting : ℝ) * Real.log ((q.1 : ℝ) / p.1) ≤
            (q.2 : ℝ) * (logRatHi q.1 p.1 : ℝ) / logScale := by
          rw [hq_eq, mul_div_assoc]
          exact mul_le_mul_of_nonneg_left hlog_hi (Nat.cast_nonneg _)
        linarith [hrec.2]

theorem theta_10M_integral_from_table
    (pts : List (Nat × Nat))
    (hhead : pts.head? = some (2, 1))
    (hlast : pts.getLast? = some (10000000, 664579))
    (hpi : ∀ p ∈ pts, p.2 = p.1.primeCounting)
    (hchain : pts.IsChain (fun p q => p.1 ≤ q.1))
    (hlo_chk : (664579 : ℝ) * 16.1180956 - (piIntHiSum pts : ℝ) / logScale ≥ 9940000)
    (hhi_chk : (664579 : ℝ) * 16.1180957 - (piIntLoSum pts : ℝ) / logScale ≤ 10080000) :
    (36183 : ℝ) ≤ ∫ t in (2 : ℝ)..(10 ^ 7 : ℝ), θ t / (t * (Real.log t) ^ 2) ∧
    ∫ t in (2 : ℝ)..(10 ^ 7 : ℝ), θ t / (t * (Real.log t) ^ 2) ≤ 48222 := by
  have h10M : ((10000000 : ℕ) : ℝ) = (10 ^ 7 : ℝ) := by norm_num
  have hpi10M : Nat.primeCounting 10000000 = 664579 := by
    have hmem : (10000000, 664579) ∈ pts := List.mem_of_getLast? hlast
    exact (hpi _ hmem).symm
  have hfl : ⌊(10 ^ 7 : ℝ)⌋₊ = 10000000 := by
    rw [← h10M]; exact Nat.floor_natCast 10000000
  have hI_eq : ∫ t in (2 : ℝ)..(10 ^ 7 : ℝ), θ t / (t * (Real.log t) ^ 2) =
      (664579 : ℝ) - θ (10 ^ 7 : ℝ) / Real.log (10 ^ 7 : ℝ) := by
    have h := Chebyshev.primeCounting_eq_theta_div_log_add_integral (x := (10 ^ 7 : ℝ)) (by norm_num)
    rw [hfl, hpi10M] at h
    push_cast at h
    linarith
  have hth_eq : θ (10 ^ 7 : ℝ) =
      (664579 : ℝ) * Real.log (10 ^ 7 : ℝ) -
        ∫ t in (2 : ℝ)..(10 ^ 7 : ℝ), (Nat.primeCounting ⌊t⌋₊ : ℝ) / t := by
    have h := Chebyshev.theta_eq_primeCounting_mul_log_sub_integral (x := (10 ^ 7 : ℝ)) (by norm_num)
    rw [hfl, hpi10M] at h
    push_cast at h
    exact h
  obtain ⟨hint_lo, hint_hi⟩ := piInt_chain_bounds pts 2 1 10000000 664579 hhead hlast (by decide) hpi hchain
  rw [h10M] at hint_lo hint_hi
  simp only [Nat.cast_ofNat] at hint_lo hint_hi
  obtain ⟨hlog_lo, hlog_hi⟩ := log_10M_bounds
  have hlog_pos : 0 < Real.log (10 ^ 7 : ℝ) := Real.log_pos (by norm_num)
  have hth_lo : (9940000 : ℝ) ≤ θ (10 ^ 7 : ℝ) := by
    rw [hth_eq]
    have h1 : (664579 : ℝ) * 16.1180956 ≤ (664579 : ℝ) * Real.log (10 ^ 7 : ℝ) := by linarith
    have h2 : ∫ t in (2 : ℝ)..(10 ^ 7 : ℝ), (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ≤
        (piIntHiSum pts : ℝ) / logScale := by convert hint_hi using 1
    linarith [hlo_chk]
  have hth_hi : θ (10 ^ 7 : ℝ) ≤ 10080000 := by
    rw [hth_eq]
    have h1 : (664579 : ℝ) * Real.log (10 ^ 7 : ℝ) ≤ (664579 : ℝ) * 16.1180957 := by linarith
    have h2 : (piIntLoSum pts : ℝ) / logScale ≤
        ∫ t in (2 : ℝ)..(10 ^ 7 : ℝ), (Nat.primeCounting ⌊t⌋₊ : ℝ) / t := by convert hint_lo using 1
    linarith [hhi_chk]
  rw [hI_eq]
  constructor
  · have hdiv : θ (10 ^ 7 : ℝ) / Real.log (10 ^ 7 : ℝ) ≤ 10080000 / 16.1180956 := by
      calc θ (10 ^ 7 : ℝ) / Real.log (10 ^ 7 : ℝ)
          ≤ 10080000 / Real.log (10 ^ 7 : ℝ) := div_le_div_of_nonneg_right hth_hi hlog_pos.le
        _ ≤ 10080000 / 16.1180956 :=
            div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlog_lo.le
    have hnum : (10080000 : ℝ) / 16.1180956 ≤ 664579 - 36183 := by norm_num
    linarith
  · have hdiv : 9940000 / 16.1180957 ≤ θ (10 ^ 7 : ℝ) / Real.log (10 ^ 7 : ℝ) := by
      calc 9940000 / 16.1180957
          ≤ 9940000 / Real.log (10 ^ 7 : ℝ) :=
            div_le_div_of_nonneg_left (by norm_num) hlog_pos hlog_hi.le
        _ ≤ θ (10 ^ 7 : ℝ) / Real.log (10 ^ 7 : ℝ) :=
            div_le_div_of_nonneg_right hth_lo hlog_pos.le
    have hnum : (664579 : ℝ) - 48222 ≤ 9940000 / 16.1180957 := by norm_num
    linarith

/- ### Part 4: Exact finite Abel summation lower bound for `∑_{L < p ≤ U} 1/p` -/

private lemma abel_sum_Ioc_inv (pi_fn : ℕ → ℝ) {L U : ℕ} (_hL : 1 ≤ L) (hLU : L < U) :
    ∑ k ∈ Ioc L U, (pi_fn k - pi_fn (k - 1)) / (k : ℝ) =
      pi_fn U / (U : ℝ) - pi_fn L / ((L + 1 : ℕ) : ℝ) +
      ∑ k ∈ Icc (L + 1) (U - 1), pi_fn k * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
  obtain ⟨d, rfl⟩ : ∃ d, U = L + 1 + d := ⟨U - (L + 1), by omega⟩
  clear hLU
  induction d with
  | zero =>
    have hIoc : Ioc L (L + 1 + 0) = {L + 1} := by ext x; simp only [mem_Ioc, mem_singleton]; omega
    have hIcc : Icc (L + 1) (L + 1 + 0 - 1) = ∅ := by ext x; simp only [mem_Icc, notMem_empty, iff_false]; omega
    rw [hIoc, hIcc, sum_singleton, sum_empty]
    simp only [add_zero, Nat.add_sub_cancel]
    ring
  | succ d ih =>
    have hIoc : Ioc L (L + 1 + (d + 1)) = insert (L + 1 + (d + 1)) (Ioc L (L + 1 + d)) := by
      ext x; simp only [mem_Ioc, mem_insert]; omega
    have hnot : (L + 1 + (d + 1)) ∉ Ioc L (L + 1 + d) := by simp
    rw [hIoc, sum_insert hnot, ih]
    have hIcc : Icc (L + 1) (L + 1 + (d + 1) - 1) =
        insert (L + 1 + d) (Icc (L + 1) (L + 1 + d - 1)) := by
      ext x; simp only [mem_Icc, mem_insert]; omega
    have hnot2 : (L + 1 + d) ∉ Icc (L + 1) (L + 1 + d - 1) := by simp only [mem_Icc]; omega
    rw [hIcc, sum_insert hnot2]
    have hpred : L + 1 + (d + 1) - 1 = L + 1 + d := by omega
    rw [hpred]
    have hsucc : L + 1 + d + 1 = L + 1 + (d + 1) := by omega
    rw [hsucc]
    ring

private lemma primeCounting_sub_pred (k : ℕ) (hk : 1 ≤ k) :
    (k.primeCounting : ℝ) - ((k - 1).primeCounting : ℝ) = if k.Prime then 1 else 0 := by
  have h1 : k = (k - 1) + 1 := by omega
  conv_lhs => rw [h1]
  simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_succ]
  rw [← h1]
  by_cases hp : k.Prime <;> simp [hp]

private lemma integral_one_div_t_log_t {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, 1 / (t * Real.log t) = Real.log (Real.log b / Real.log a) := by
  have hderiv : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun x => Real.log (Real.log x)) (1 / (t * Real.log t)) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog_pos : 0 < Real.log t := Real.log_pos (by linarith [ht.1])
    have := (Real.hasDerivAt_log ht0).log hlog_pos.ne'
    convert this using 1
    field_simp
  have hcont : ContinuousOn (fun t : ℝ => 1 / (t * Real.log t)) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have hlog_ne : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1])).ne'
    have hmul : t * Real.log t ≠ 0 := mul_ne_zero ht0 hlog_ne
    exact ContinuousAt.continuousWithinAt (by fun_prop)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont.intervalIntegrable,
    Real.log_div (Real.log_pos (by linarith)).ne' (Real.log_pos (by linarith)).ne']

theorem sum_inv_primes_lower
    (hpi_lo : ∀ m : ℕ, 101 ≤ m →
      0.9400 * ((m : ℝ) / Real.log m + (m : ℝ) / (Real.log m) ^ 2) ≤ (m.primeCounting : ℝ))
    {L U : ℕ} (hL : 100 ≤ L) (hLU : L < U) :
    (U.primeCounting : ℝ) / U - (L.primeCounting : ℝ) / L +
      0.9400 * Real.log (Real.log U / Real.log (L + 1 : ℕ)) ≤
      ∑ p ∈ (Ioc L U).filter Nat.Prime, (1 : ℝ) / p := by
  have hsum_eq : ∑ p ∈ (Ioc L U).filter Nat.Prime, (1 : ℝ) / p =
      ∑ k ∈ Ioc L U, ((k.primeCounting : ℝ) - ((k - 1).primeCounting : ℝ)) / k := by
    rw [sum_filter]
    refine sum_congr rfl fun k hk => ?_
    have hk1 : 1 ≤ k := by have := (mem_Ioc.mp hk).1; omega
    rw [primeCounting_sub_pred k hk1]
    split_ifs <;> simp
  rw [hsum_eq, abel_sum_Ioc_inv (fun k => (k.primeCounting : ℝ)) (by omega) hLU]
  have hL_bound : (L.primeCounting : ℝ) / ((L + 1 : ℕ) : ℝ) ≤ (L.primeCounting : ℝ) / L := by
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by exact_mod_cast (show 0 < L by omega))
    exact_mod_cast (show L ≤ L + 1 by omega)
  have hterm : ∀ k ∈ Icc (L + 1) (U - 1),
      0.9400 * ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), 1 / (t * Real.log t) ≤
        (k.primeCounting : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
    intro k hk
    have hk101 : 101 ≤ k := by have := (mem_Icc.mp hk).1; omega
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
    have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    have hlogk_pos : 0 < Real.log k := Real.log_pos (by exact_mod_cast (show 1 < k by omega))
    have hint_le : ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), 1 / (t * Real.log t) ≤
        1 / ((k : ℝ) * Real.log k) := by
      have hab : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (show k ≤ k + 1 by omega)
      have hcont : ContinuousOn (fun t : ℝ => 1 / (t * Real.log t)) (Set.uIcc (k : ℝ) ((k + 1 : ℕ) : ℝ)) := by
        rw [Set.uIcc_of_le hab]
        intro t ht
        have ht0 : t ≠ 0 := by linarith [ht.1]
        have hlt_ne : Real.log t ≠ 0 := (Real.log_pos (by linarith [ht.1, (show (2 : ℝ) ≤ k by exact_mod_cast (show 2 ≤ k by omega))])).ne'
        have hmul : t * Real.log t ≠ 0 := mul_ne_zero ht0 hlt_ne
        exact ContinuousAt.continuousWithinAt (by fun_prop)
      calc ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), 1 / (t * Real.log t)
          ≤ ∫ _t in (k : ℝ)..((k + 1 : ℕ) : ℝ), 1 / ((k : ℝ) * Real.log k) := by
            apply intervalIntegral.integral_mono_on hab hcont.intervalIntegrable
              intervalIntegrable_const
            intro t ht
            apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
            exact mul_le_mul ht.1 (Real.log_le_log hk_pos ht.1) hlogk_pos.le (by linarith [ht.1])
        _ = 1 / ((k : ℝ) * Real.log k) := by
            rw [intervalIntegral.integral_const]
            push_cast
            simp
    have hdiff_eq : (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) = 1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)) := by
      push_cast; field_simp; ring
    have hlog_le_k : Real.log k ≤ (k : ℝ) := by
      have := Real.log_le_sub_one_of_pos hk_pos; linarith
    have halg : 1 / ((k : ℝ) * Real.log k) ≤
        ((k : ℝ) / Real.log k + (k : ℝ) / (Real.log k) ^ 2) * (1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ))) := by
      push_cast
      rw [show (k : ℝ) / Real.log k + (k : ℝ) / (Real.log k) ^ 2 =
          (k : ℝ) * (Real.log k + 1) / (Real.log k) ^ 2 by field_simp]
      rw [div_mul_div_comm, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
      have hprod := mul_le_mul_of_nonneg_left hlog_le_k (mul_pos hk_pos hlogk_pos).le
      linarith
    calc 0.9400 * ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), 1 / (t * Real.log t)
        ≤ 0.9400 * (1 / ((k : ℝ) * Real.log k)) :=
          mul_le_mul_of_nonneg_left hint_le (by norm_num)
      _ ≤ 0.9400 * (((k : ℝ) / Real.log k + (k : ℝ) / (Real.log k) ^ 2) *
            (1 / ((k : ℝ) * ((k + 1 : ℕ) : ℝ)))) :=
          mul_le_mul_of_nonneg_left halg (by norm_num)
      _ = (0.9400 * ((k : ℝ) / Real.log k + (k : ℝ) / (Real.log k) ^ 2)) *
            (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by rw [← hdiff_eq]; ring
      _ ≤ (k.primeCounting : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
          apply mul_le_mul_of_nonneg_right (hpi_lo k hk101)
          rw [hdiff_eq]; positivity
  have hsum_int : ∑ k ∈ Icc (L + 1) (U - 1),
      ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), 1 / (t * Real.log t) =
      Real.log (Real.log U / Real.log (L + 1 : ℕ)) := by
    have htele : ∀ d : ℕ, ∑ k ∈ Icc (L + 1) (L + d),
        ∫ t in (k : ℝ)..((k + 1 : ℕ) : ℝ), 1 / (t * Real.log t) =
        Real.log (Real.log ((L + 1 + d : ℕ) : ℝ) / Real.log (L + 1 : ℕ)) := by
      intro d
      induction d with
      | zero =>
        have : Icc (L + 1) (L + 0) = ∅ := by ext x; simp only [mem_Icc, notMem_empty, iff_false]; omega
        rw [this, sum_empty]
        simp
      | succ d ih =>
        have hIcc : Icc (L + 1) (L + (d + 1)) = insert (L + 1 + d) (Icc (L + 1) (L + d)) := by
          ext x; simp only [mem_Icc, mem_insert]; omega
        have hnot : (L + 1 + d) ∉ Icc (L + 1) (L + d) := by simp only [mem_Icc]; omega
        rw [hIcc, sum_insert hnot, ih,
          integral_one_div_t_log_t (by exact_mod_cast (show 2 ≤ L + 1 + d by omega))
            (by exact_mod_cast (show L + 1 + d ≤ L + 1 + d + 1 by omega))]
        have hlog1 : 0 < Real.log (L + 1 : ℕ) :=
          Real.log_pos (by exact_mod_cast (show 1 < L + 1 by omega))
        have hlog2 : 0 < Real.log ((L + 1 + d : ℕ) : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < L + 1 + d by omega))
        have hlog3 : 0 < Real.log ((L + 1 + d + 1 : ℕ) : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < L + 1 + d + 1 by omega))
        rw [← Real.log_mul (div_pos hlog3 hlog2).ne' (div_pos hlog2 hlog1).ne']
        congr 1
        have heq : L + 1 + (d + 1) = L + 1 + d + 1 := by omega
        rw [heq]; field_simp
    have hU : U - 1 = L + (U - (L + 1)) := by omega
    have hU2 : L + 1 + (U - (L + 1)) = U := by omega
    rw [hU, htele (U - (L + 1)), hU2]
  have hsum_le : 0.9400 * Real.log (Real.log U / Real.log (L + 1 : ℕ)) ≤
      ∑ k ∈ Icc (L + 1) (U - 1), (k.primeCounting : ℝ) * (1 / (k : ℝ) - 1 / ((k + 1 : ℕ) : ℝ)) := by
    rw [← hsum_int, mul_sum]
    exact sum_le_sum hterm
  linarith

end ColtonPiAbel


/- ===================== Mod2B_Tables.lean ===================== -/

/-
Module 2B: Multi-resolution prime tables up to 14,090,240 verified in PLift batches
via width-1 SWAR segmented sieve, Colton verification through 14,090,240,
zero-calculus lower bounds on `π(x)` for `[101, 10^7]` and `[2000, 10^7]`,
and `θ(10^7)` integral pinning.
-/

namespace ColtonTables

open Finset Real Chebyshev OeisA111291 ColtonSieve ColtonSWAR ColtonSmall ColtonFactor ColtonBase4096

def P1 : Array Nat := #[
  1028, 1035, 1044, 1049, 1057, 1060, 1068, 1075, 1084, 1093, 1100, 1108, 1113, 1121, 1127, 1134,
  1142, 1148, 1157, 1163, 1173, 1180, 1184, 1193, 1199, 1208, 1215, 1222, 1229, 1233, 1242, 1249,
  1254, 1264, 1271, 1276, 1283, 1289, 1295, 1303, 1310, 1315, 1322, 1329, 1336, 1342, 1349, 1356,
  1362, 1369, 1374, 1381, 1389, 1393, 1399, 1405, 1409, 1421, 1426, 1434, 1440, 1446, 1455, 1460,
  1469, 1475, 1482, 1489, 1498, 1505, 1514, 1519, 1526, 1532, 1540, 1547, 1555, 1560, 1569, 1574,
  1580, 1586, 1592, 1600, 1605, 1611, 1619, 1628, 1633, 1641, 1648, 1654, 1659, 1664, 1671, 1675,
  1681, 1686, 1696, 1700, 1709, 1716, 1722, 1733, 1739, 1746, 1753, 1757, 1764, 1771, 1777, 1786,
  1794, 1801, 1808, 1814, 1820, 1830, 1836, 1844, 1848, 1857, 1862, 1868, 1877, 1882, 1889, 1893,
  1900
]

def P2 : Array Nat := #[
  1900, 1912, 1924, 1938, 1948, 1962, 1975, 1986, 2002, 2016, 2029, 2042, 2053, 2068, 2082, 2097,
  2110, 2125, 2133, 2146, 2154, 2165, 2176, 2190, 2205, 2222, 2231, 2243, 2257, 2271, 2286, 2298,
  2312, 2323, 2334, 2346, 2360, 2373, 2388, 2397, 2413, 2429, 2441, 2455, 2466, 2482, 2493, 2507,
  2517, 2531, 2546, 2557, 2571, 2585, 2597, 2608, 2618, 2635, 2647, 2663, 2676, 2692, 2701, 2714,
  2725, 2735, 2745, 2757, 2769, 2781, 2795, 2810, 2818, 2832, 2845, 2858, 2870, 2883, 2896, 2909,
  2918, 2936, 2948, 2961, 2975, 2984, 2993, 3005, 3016, 3031, 3045, 3059, 3070, 3080, 3092, 3104,
  3124, 3136, 3149, 3159, 3172, 3185, 3199, 3208, 3221, 3230, 3242, 3251, 3267, 3279, 3288, 3301,
  3314, 3325, 3338, 3350, 3365, 3380, 3388, 3401, 3414, 3423, 3432, 3447, 3459, 3476, 3489, 3503,
  3512, 3525, 3540, 3553, 3562, 3577, 3590, 3607, 3619, 3631, 3642, 3652, 3666, 3678, 3692, 3705,
  3716, 3728, 3738, 3751, 3764, 3776, 3788, 3795, 3808, 3819, 3833, 3844, 3857, 3868, 3882, 3894,
  3908, 3922, 3934, 3945, 3958, 3969, 3985, 3995, 4006, 4018, 4025, 4038, 4052, 4059, 4072, 4087,
  4098, 4109, 4124, 4136, 4150, 4161, 4172, 4183, 4197, 4209, 4222, 4231, 4240, 4252, 4263, 4275,
  4288, 4300, 4314, 4326, 4337, 4349, 4363, 4375, 4391, 4403, 4417, 4428, 4446, 4455, 4471, 4483,
  4495, 4506, 4515, 4523, 4535, 4547, 4557, 4568, 4583, 4596, 4611, 4618, 4631, 4643, 4656, 4668,
  4678, 4690, 4700, 4714, 4723, 4735, 4746, 4756, 4767, 4780, 4791, 4802, 4815, 4827, 4840, 4849,
  4858, 4870, 4883, 4893, 4908, 4923, 4934, 4946, 4956, 4966, 4977, 4990, 5002, 5014, 5029, 5038,
  5051, 5065, 5075, 5089, 5100, 5113, 5124, 5137, 5152, 5162, 5175, 5186, 5196, 5204, 5216, 5229,
  5239, 5249, 5265, 5279, 5291, 5304, 5315, 5327, 5339, 5349, 5358, 5371, 5384, 5394, 5407, 5420,
  5432, 5442, 5453, 5466, 5477, 5489, 5503, 5512, 5520, 5532, 5548, 5562, 5573, 5582, 5593, 5605,
  5616, 5627, 5637, 5650, 5662, 5679, 5688, 5700, 5711, 5722, 5737, 5749, 5763, 5777, 5788, 5802,
  5814, 5825, 5835, 5848, 5862, 5872, 5885, 5900, 5908, 5922, 5932, 5943, 5949, 5963, 5979, 5993,
  6003, 6018, 6028, 6042, 6050, 6060, 6073, 6083, 6094, 6104, 6116, 6129, 6141, 6151, 6160, 6168,
  6179, 6194, 6208, 6217, 6226, 6240, 6253, 6263, 6270, 6283, 6294, 6304, 6316, 6328, 6336, 6348,
  6363, 6377, 6393, 6406, 6413, 6424, 6434, 6444, 6453, 6465, 6474, 6485, 6495, 6510, 6521, 6532,
  6542
]

def P3 : Array Nat := #[
  6542, 6595, 6636, 6682, 6734, 6780, 6820, 6864, 6906, 6951, 6999, 7047, 7095, 7145, 7190, 7234,
  7281, 7325, 7371, 7416, 7465, 7508, 7550, 7595, 7649, 7691, 7733, 7777, 7824, 7870, 7915, 7965,
  8009, 8057, 8103, 8148, 8187, 8235, 8277, 8321, 8363, 8413, 8453, 8499, 8548, 8580, 8630, 8677,
  8727, 8771, 8812, 8859, 8899, 8951, 9000, 9043, 9087, 9132, 9180, 9228, 9271, 9315, 9357, 9399,
  9439, 9485, 9533, 9580, 9618, 9663, 9708, 9756, 9805, 9847, 9886, 9924, 9971, 10021, 10062, 10105,
  10151, 10198, 10236, 10278, 10324, 10369, 10416, 10460, 10499, 10543, 10585, 10630, 10674, 10721, 10761, 10804,
  10846, 10888, 10930, 10981, 11021, 11066, 11110, 11156, 11196, 11240, 11282, 11328, 11371, 11419, 11462, 11510,
  11554, 11593, 11641, 11684, 11729, 11772, 11816, 11859, 11900, 11939, 11987, 12033, 12079, 12125, 12163, 12211,
  12251, 12291, 12333, 12376, 12425, 12466, 12507, 12549, 12589, 12641, 12680, 12732, 12777, 12819, 12861, 12907,
  12941, 12990, 13032, 13080, 13125, 13169, 13212, 13252, 13289, 13333, 13372, 13414, 13452, 13499, 13546, 13586,
  13631, 13672, 13712, 13756, 13807, 13850, 13894, 13937, 13982, 14030, 14072, 14117, 14159, 14200, 14242, 14282,
  14327, 14372, 14407, 14450, 14497, 14535, 14577, 14618, 14662, 14707, 14750, 14790, 14835, 14873, 14915, 14959,
  14999, 15045, 15086, 15121, 15167, 15204, 15247, 15294, 15334, 15368, 15408, 15450, 15495, 15541, 15585, 15624,
  15670, 15713, 15758, 15795, 15843, 15882, 15925, 15955, 16003, 16056, 16097, 16132, 16173, 16219, 16264, 16313,
  16357, 16399, 16433, 16472, 16519, 16563, 16601, 16647, 16690, 16731, 16775, 16822, 16869, 16910, 16954, 16993,
  17032, 17075, 17119, 17164, 17200, 17243, 17282, 17326, 17369, 17418, 17457, 17502, 17536, 17580, 17623, 17666,
  17704, 17745, 17789, 17833, 17877, 17917, 17957, 18001, 18038, 18079, 18118, 18166, 18205, 18243, 18285, 18322,
  18367, 18407, 18450, 18496, 18535, 18577, 18624, 18667, 18710, 18755, 18798, 18848, 18889, 18930, 18974, 19010,
  19045, 19089, 19130, 19173, 19213, 19254, 19290, 19328, 19370, 19415, 19453, 19493, 19541, 19580, 19628, 19666,
  19709, 19751, 19797, 19833, 19876, 19918, 19960, 20002, 20043, 20088, 20126, 20168, 20206, 20251, 20288, 20335,
  20379, 20428, 20476, 20513, 20552, 20595, 20632, 20672, 20709, 20745, 20787, 20835, 20870, 20908, 20946, 20986,
  21022, 21062, 21109, 21149, 21191, 21234, 21272, 21314, 21359, 21405, 21446, 21483, 21527, 21563, 21613, 21649,
  21695, 21735, 21776, 21815, 21859, 21906, 21950, 21990, 22031, 22069, 22106, 22151, 22196, 22236, 22276, 22310,
  22358, 22396, 22435, 22481, 22525, 22564, 22599, 22641, 22678, 22722, 22765, 22803, 22845, 22883, 22925, 22962,
  23000, 23042, 23079, 23125, 23168, 23202, 23247, 23287, 23332, 23371, 23413, 23469, 23509, 23543, 23589, 23631,
  23672, 23716, 23755, 23795, 23841, 23876, 23918, 23951, 23992, 24033, 24075, 24117, 24162, 24204, 24240, 24278,
  24318, 24363, 24397, 24438, 24477, 24525, 24564, 24615, 24651, 24694, 24729, 24768, 24812, 24858, 24897, 24933,
  24973, 25009, 25045, 25080, 25120, 25168, 25208, 25248, 25293, 25333, 25373, 25411, 25454, 25490, 25524, 25570,
  25607, 25647, 25684, 25723, 25768, 25805, 25844, 25884, 25919, 25961, 26000, 26039, 26086, 26125, 26167, 26202,
  26248, 26291, 26334, 26376, 26424, 26466, 26503, 26543, 26588, 26630, 26661, 26701, 26741, 26784, 26820, 26862,
  26899, 26938, 26979, 27019, 27063, 27103, 27150, 27188, 27223, 27267, 27307, 27352, 27393, 27434, 27480, 27521,
  27566, 27608, 27651, 27689, 27730, 27772, 27813, 27852, 27891, 27925, 27970, 28017, 28057, 28102, 28137, 28175,
  28223
]

def P4 : Array Nat := #[
  28223, 28546, 28865, 29181, 29504, 29828, 30152, 30480, 30789, 31107, 31431, 31725, 32055, 32366, 32683, 32995,
  33335, 33647, 33961, 34262, 34579, 34891, 35213, 35531, 35851, 36168, 36493, 36809, 37126, 37450, 37757, 38057,
  38368, 38666, 38980, 39311, 39627, 39949, 40264, 40558, 40883, 41202, 41519, 41817, 42132, 42445, 42745, 43073,
  43390, 43703, 44011, 44319, 44622, 44930, 45235, 45544, 45858, 46170, 46463, 46769, 47088, 47401, 47711, 48018,
  48340, 48640, 48954, 49258, 49569, 49878, 50185, 50505, 50805, 51101, 51392, 51709, 51999, 52297, 52609, 52915,
  53228, 53520, 53828, 54141, 54439, 54748, 55056, 55362, 55672, 55969, 56277, 56576, 56884, 57205, 57510, 57808,
  58096, 58417, 58720, 59019, 59323, 59627, 59906, 60209, 60509, 60807, 61124, 61432, 61737, 62044, 62336, 62648,
  62946, 63247, 63560, 63864, 64162, 64459, 64761, 65057, 65348, 65668, 65978, 66270, 66570, 66867, 67166, 67463,
  67763, 68052, 68356, 68662, 68970, 69274, 69571, 69872, 70169, 70474, 70767, 71065, 71357, 71654, 71971, 72262,
  72547, 72848, 73166, 73460, 73747, 74046, 74349, 74640, 74928, 75224, 75507, 75810, 76114, 76401, 76708, 76999,
  77279, 77584, 77869, 78155, 78460, 78769, 79063, 79368, 79667, 79968, 80265, 80563, 80844, 81150, 81432, 81737,
  82025, 82314, 82604, 82894, 83184, 83478, 83772, 84073, 84379, 84665, 84953, 85251, 85557, 85846, 86152, 86452,
  86756, 87054, 87337, 87616, 87917, 88221, 88507, 88795, 89082, 89378, 89667, 89975, 90288, 90580, 90871, 91155,
  91465, 91767, 92066, 92361, 92654, 92943, 93230, 93503, 93794, 94092, 94388, 94671, 94964, 95255, 95521, 95821,
  96113, 96416, 96693, 96996, 97291, 97588, 97887, 98187, 98460, 98751, 99045, 99349, 99627, 99915, 100205, 100493,
  100786, 101066, 101361, 101663, 101953, 102222, 102512, 102808, 103109, 103388, 103670, 103960, 104248, 104543, 104826, 105118,
  105407, 105715, 105991, 106286, 106565, 106870, 107179, 107454, 107738, 108040, 108293, 108580, 108870, 109162, 109464, 109764,
  110056, 110337, 110630, 110918, 111213, 111505, 111800, 112075, 112363, 112648, 112944, 113231, 113528, 113827, 114100, 114390,
  114700, 114992, 115273, 115562, 115842, 116124, 116400, 116684, 116973, 117251, 117542, 117826, 118120, 118415, 118688, 118973,
  119268, 119553, 119833, 120114, 120390, 120669, 120955, 121241, 121550, 121827, 122106, 122387, 122682, 122968, 123265, 123563,
  123841, 124107, 124403, 124690, 124972, 125261, 125545, 125825, 126129, 126411, 126711, 126986, 127265, 127546, 127829, 128130,
  128413, 128697, 128981, 129262, 129549, 129816, 130109, 130386, 130666, 130960, 131235, 131526, 131836, 132109, 132369, 132647,
  132937, 133210, 133500, 133800, 134085, 134354, 134650, 134930, 135227, 135510, 135805, 136082, 136361, 136639, 136942, 137232,
  137524, 137778, 138069, 138350, 138630, 138931, 139223, 139508, 139802, 140085, 140360, 140644, 140930, 141218, 141504, 141794,
  142071, 142341, 142626, 142919, 143210, 143489, 143764, 144066, 144348, 144622, 144917, 145200, 145481, 145760, 146045, 146330,
  146605, 146867, 147139, 147415, 147705, 147989, 148272, 148557, 148858, 149135, 149417, 149712, 150005, 150284, 150571, 150843,
  151128, 151423, 151693, 151982, 152252, 152526, 152798, 153099, 153384, 153659, 153947, 154214, 154499, 154765, 155064, 155341,
  155611
]

def P5 : Array Nat := #[
  155611, 156742, 157880, 159005, 160144, 161261, 162373, 163488, 164598, 165704, 166849, 167986, 169084, 170208, 171292, 172410,
  173514, 174621, 175761, 176861, 177974, 179082, 180197, 181311, 182420, 183536, 184634, 185766, 186866, 187974, 189111, 190210,
  191308, 192426, 193540, 194642, 195746, 196861, 198007, 199062, 200167, 201277, 202376, 203470, 204613, 205731, 206843, 207937,
  209014, 210106, 211205, 212305, 213390, 214492, 215594, 216703, 217807, 218882, 219973, 221051, 222165, 223284, 224358, 225464,
  226549, 227641, 228754, 229861, 230984, 232077, 233182, 234274, 235370, 236466, 237544, 238636, 239725, 240777, 241873, 242977,
  244069, 245167, 246282, 247365, 248429, 249467, 250562, 251628, 252687, 253764, 254867, 255943, 257024, 258142, 259244, 260285,
  261378, 262479, 263582, 264661, 265772, 266856, 267908, 268984, 270055, 271158, 272244, 273336, 274394, 275467, 276570, 277639,
  278737, 279821, 280882, 281955, 282992, 284073, 285162, 286283, 287346, 288429, 289511, 290594, 291640, 292690, 293777, 294847,
  295947, 297032, 298101, 299161, 300236, 301298, 302351, 303421, 304473, 305562, 306607, 307697, 308758, 309807, 310902, 312001,
  313085, 314161, 315260, 316324, 317368, 318408, 319493, 320569, 321634, 322699, 323777, 324836, 325892, 326952, 328041, 329116,
  330177, 331257, 332309, 333368, 334421, 335471, 336536, 337600, 338677, 339741, 340814, 341911, 342978, 344032, 345106, 346174,
  347259, 348326, 349373, 350444, 351487, 352552, 353610, 354678, 355720, 356781, 357854, 358907, 359952, 360995, 362075, 363140,
  364195, 365268, 366338, 367390, 368456, 369492, 370564, 371617, 372663, 373745, 374778, 375840, 376903, 377957, 379014, 380061,
  381113, 382158, 383218, 384250, 385311, 386360, 387408, 388460, 389513, 390544, 391581, 392626, 393710, 394772, 395817, 396868,
  397906, 398949, 399988, 401052, 402094, 403146, 404178, 405238, 406315, 407392, 408459, 409507, 410554, 411589, 412629, 413695,
  414771, 415781, 416825, 417873, 418899, 419976, 421016, 422062, 423119, 424172, 425185, 426258, 427276, 428335, 429386, 430437,
  431502, 432589, 433628, 434669, 435711, 436730, 437744, 438800, 439839, 440862, 441921, 442963, 443987, 445061, 446095, 447139,
  448182, 449226, 450297, 451338, 452412, 453415, 454451, 455486, 456517, 457564, 458636, 459679, 460717, 461774, 462805, 463830,
  464881, 465925, 466969, 468044, 469089, 470142, 471172, 472203, 473247, 474316, 475356, 476388, 477415, 478480, 479543, 480585,
  481615, 482659, 483715, 484731, 485755, 486794, 487820, 488857, 489887, 490926, 491960, 493002, 494051, 495089, 496118, 497156,
  498177, 499213, 500242, 501294, 502304, 503346, 504378, 505433, 506439, 507493, 508496, 509527, 510553, 511619, 512631, 513645,
  514705, 515749, 516787, 517818, 518854, 519884, 520939, 521964, 522988, 524007, 525034, 526068, 527072, 528136, 529148, 530217,
  531252, 532286, 533328, 534348, 535375, 536417, 537431, 538473, 539493, 540516, 541542, 542558, 543605, 544630, 545637, 546646,
  547712, 548711, 549752, 550772, 551814, 552858, 553883, 554925, 555941, 556957, 557991, 559035, 560059, 561070, 562129, 563125,
  564163, 565183, 566214, 567228, 568234, 569251, 570304, 571334, 572365, 573414, 574442, 575460, 576520, 577541, 578580, 579591,
  580619, 581656, 582667, 583706, 584751, 585791, 586799, 587845, 588867, 589896, 590909, 591933, 592937, 593958, 594980, 596002,
  597016, 598071, 599086, 600100, 601108, 602155, 603142, 604155, 605170, 606182, 607198, 608243, 609268, 610262, 611306, 612312,
  613334, 614374, 615393, 616438, 617464, 618492, 619511, 620525, 621559, 622560, 623600, 624624, 625656, 626659, 627670, 628688,
  629686, 630704, 631720, 632732, 633754, 634771, 635804, 636804, 637820, 638886, 639915, 640927, 641939, 642973, 643991, 645020,
  646005, 647025, 648052, 649084, 650082, 651087, 652114, 653129, 654170, 655160, 656180, 657175, 658197, 659197, 660196, 661227,
  662226, 663239, 664228, 665236, 666269, 667292, 668323, 669331, 670352, 671367, 672389, 673402, 674425, 675424, 676427, 677426,
  678426, 679461, 680470, 681498, 682513, 683511, 684518, 685553, 686547, 687583, 688588, 689632, 690646, 691663, 692668, 693707,
  694716, 695742, 696756, 697748, 698782, 699810, 700802, 701815, 702826, 703836, 704869, 705868, 706919, 707937, 708964, 709967,
  710976, 711975, 712974, 713971, 714998, 715981, 717019, 718038, 719035, 720039, 721070, 722087, 723104, 724117, 725124, 726127,
  727128, 728126, 729131, 730170, 731186, 732205, 733217, 734214, 735203, 736235, 737255, 738275, 739284, 740277, 741275, 742309,
  743287, 744299, 745299, 746316, 747323, 748329, 749316, 750331, 751333, 752342, 753327, 754335, 755375, 756375, 757391, 758371,
  759401, 760435, 761445, 762447, 763448, 764503, 765518, 766491, 767514, 768489, 769517, 770519, 771517, 772530, 773528, 774522,
  775549, 776559, 777578, 778539, 779563, 780581, 781575, 782592, 783618, 784612, 785647, 786640, 787643, 788622, 789635, 790634,
  791652, 792661, 793650, 794640, 795652, 796654, 797672, 798664, 799658, 800645, 801664, 802685, 803671, 804683, 805680, 806702,
  807738, 808716, 809705, 810773, 811762, 812763, 813783, 814786, 815780, 816777, 817804, 818756, 819768, 820783, 821758, 822738,
  823749, 824752, 825769, 826788, 827785, 828770, 829785, 830774, 831786, 832799, 833832, 834840, 835855, 836832, 837842, 838845,
  839845, 840867, 841864, 842861, 843828, 844809, 845800, 846798, 847799, 848777, 849802, 850804, 851788, 852777, 853752, 854735,
  855732, 856716, 857730, 858720, 859709, 860730, 861740, 862738, 863735, 864739, 865712, 866728, 867718, 868736, 869725, 870712,
  871735, 872717, 873728, 874707, 875703, 876692, 877667, 878665, 879662, 880642, 881639, 882625, 883619, 884622, 885626, 886658,
  887642, 888640, 889642, 890670, 891663, 892651, 893652, 894632, 895638, 896615, 897665, 898651, 899638, 900646, 901652, 902654,
  903648, 904679, 905678, 906669, 907634, 908609, 909582, 910568, 911572, 912579, 913538, 914551, 915556
]

/- ### Tier verification via width-1 SWAR segmented sieve -/

def checkSeg (arr : Array Nat) (base m perSeg segLen segIdx : Nat) : Bool :=
  let mask := primeMask (base + 1 + segLen * segIdx) segLen
  (List.range perSeg).all (fun r =>
    let j := perSeg * segIdx + r
    decide (arr[j + 1]! = arr[j]! + slicePop m mask (16 * m * r)))

def checkSegRange (arr : Array Nat) (base m perSeg segLen lo cnt : Nat) : Bool :=
  (List.range cnt).all (fun i => checkSeg arr base m perSeg segLen (lo + i))

private lemma checkSegRange_at {arr : Array Nat} {base m perSeg segLen lo cnt s : Nat}
    (h : checkSegRange arr base m perSeg segLen lo cnt = true) (h1 : lo ≤ s) (h2 : s < lo + cnt) :
    checkSeg arr base m perSeg segLen s = true := by
  unfold checkSegRange at h
  rw [List.all_eq_true] at h
  have hmem : s - lo ∈ List.range cnt := List.mem_range.mpr (by omega)
  have hres := h (s - lo) hmem
  rwa [show lo + (s - lo) = s by omega] at hres

private lemma checkSeg_at {arr : Array Nat} {base m perSeg segLen segIdx r : Nat}
    (h : checkSeg arr base m perSeg segLen segIdx = true) (hr : r < perSeg) :
    arr[perSeg * segIdx + r + 1]! =
      arr[perSeg * segIdx + r]! + slicePop m (primeMask (base + 1 + segLen * segIdx) segLen) (16 * m * r) := by
  unfold checkSeg at h
  dsimp only at h
  rw [List.all_eq_true] at h
  have hres := h r (List.mem_range.mpr hr)
  exact decide_eq_true_eq.mp hres

private theorem tier_correct {arr : Array Nat} {base m perSeg segLen numSegs : Nat}
    (hm : 16 * m < 65535) (hper : 0 < perSeg) (hseg : perSeg * (16 * m) = segLen)
    (hlo : 1 ≤ base) (hhi : base + 1 + segLen * numSegs ≤ 14137600)
    (h0 : arr[0]! = Nat.primeCounting base)
    (hall : ∀ s < numSegs, checkSeg arr base m perSeg segLen s = true) :
    ∀ j ≤ perSeg * numSegs, arr[j]! = Nat.primeCounting (base + 16 * m * j) := by
  intro j
  induction j with
  | zero => intro _; simpa using h0
  | succ j ih =>
    intro hj
    have hjlt : j < perSeg * numSegs := by omega
    let s := j / perSeg
    let r := j % perSeg
    have hs : s < numSegs := (Nat.div_lt_iff_lt_mul hper).mpr (by rw [Nat.mul_comm]; exact hjlt)
    have hr : r < perSeg := Nat.mod_lt j hper
    have hj_eq : perSeg * s + r = j := Nat.div_add_mod j perSeg
    have hstep := checkSeg_at (hall s hs) hr
    rw [hj_eq] at hstep
    rw [hstep, ih (by omega)]
    have hsub : 16 * m * r + 16 * m ≤ segLen := by
      have : 16 * m * (r + 1) ≤ 16 * m * perSeg := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_comm] at hseg
      rw [Nat.mul_succ] at this
      omega
    have hseg_hi : base + 1 + segLen * s + segLen ≤ 14137600 := by
      have : segLen * (s + 1) ≤ segLen * numSegs := Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_succ] at this
      omega
    have hcor := slicePop_correct (lo := base + 1 + segLen * s) (len := segLen)
      (m := m) (off := 16 * m * r) hm (by omega) hseg_hi hsub
    have hidx : base + 1 + segLen * s + 16 * m * r = base + 16 * m * j + 1 := by
      have hmul : segLen * s = 16 * m * (perSeg * s) := by
        rw [← hseg]; ring
      have hmul2 : 16 * m * j = 16 * m * (perSeg * s) + 16 * m * r := by
        rw [← hj_eq, Nat.mul_add]
      omega
    have hidx2 : base + 16 * m * j + 1 + 16 * m = base + 16 * m * (j + 1) + 1 := by
      rw [Nat.mul_succ]; omega
    rw [hidx, hidx2] at hcor
    simpa only [Nat.primeCounting] using hcor.symm

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p1Check : PLift (checkSegRange P1 8192 4 128 8192 0 1 = true) := ⟨by decide +kernel⟩

theorem P1_correct : ∀ j ≤ 128, P1[j]! = Nat.primeCounting (8192 + 64 * j) := by
  have h0 : P1[0]! = Nat.primeCounting 8192 := by
    rw [← exactPiSmall_correct (by decide : 8192 ≤ 8192)]; decide +kernel
  exact tier_correct (m := 4) (perSeg := 128) (segLen := 8192) (numSegs := 1)
    (by decide) (by decide) (by decide) (by decide) (by decide) h0
    (fun s hs => checkSegRange_at p1Check.down (by omega) (by omega))

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p2Check : PLift (checkSegRange P2 16384 8 128 16384 0 3 = true) := ⟨by decide +kernel⟩

theorem P2_correct : ∀ j ≤ 384, P2[j]! = Nat.primeCounting (16384 + 128 * j) := by
  have h0 : P2[0]! = Nat.primeCounting 16384 := by
    have h1 := P1_correct 128 le_rfl
    have h2 : P2[0]! = P1[128]! := by decide +kernel
    simpa using h2.trans h1
  exact tier_correct (m := 8) (perSeg := 128) (segLen := 16384) (numSegs := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) h0
    (fun s hs => checkSegRange_at p2Check.down (by omega) (by omega))

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p3Check : PLift (checkSegRange P3 65536 32 32 16384 0 16 = true) := ⟨by decide +kernel⟩

theorem P3_correct : ∀ j ≤ 512, P3[j]! = Nat.primeCounting (65536 + 512 * j) := by
  have h0 : P3[0]! = Nat.primeCounting 65536 := by
    have h1 := P2_correct 384 le_rfl
    have h2 : P3[0]! = P2[384]! := by decide +kernel
    simpa using h2.trans h1
  exact tier_correct (m := 32) (perSeg := 32) (segLen := 16384) (numSegs := 16)
    (by decide) (by decide) (by decide) (by decide) (by decide) h0
    (fun s hs => checkSegRange_at p3Check.down (by omega) (by omega))

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p4Batch0 : PLift (checkSegRange P4 327680 256 4 16384 0 18 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p4Batch1 : PLift (checkSegRange P4 327680 256 4 16384 18 18 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p4Batch2 : PLift (checkSegRange P4 327680 256 4 16384 36 18 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p4Batch3 : PLift (checkSegRange P4 327680 256 4 16384 54 18 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p4Batch4 : PLift (checkSegRange P4 327680 256 4 16384 72 18 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p4Batch5 : PLift (checkSegRange P4 327680 256 4 16384 90 18 = true) := ⟨by decide +kernel⟩


theorem P4_correct : ∀ j ≤ 432, P4[j]! = Nat.primeCounting (327680 + 4096 * j) := by
  have h0 : P4[0]! = Nat.primeCounting 327680 := by
    have h1 := P3_correct 512 le_rfl
    have h2 : P4[0]! = P3[512]! := by decide +kernel
    simpa using h2.trans h1
  refine tier_correct (m := 256) (perSeg := 4) (segLen := 16384) (numSegs := 108)
    (by decide) (by decide) (by decide) (by decide) (by decide) h0 (fun s hs => ?_)
  have hcases : (0 ≤ s ∧ s < 18) ∨ (18 ≤ s ∧ s < 36) ∨ (36 ≤ s ∧ s < 54) ∨ (54 ≤ s ∧ s < 72) ∨ (72 ≤ s ∧ s < 90) ∨ (90 ≤ s ∧ s < 108) := by omega
  rcases hcases with h | h | h | h | h | h
  · exact checkSegRange_at p4Batch0.down (by omega) (by omega)
  · exact checkSegRange_at p4Batch1.down (by omega) (by omega)
  · exact checkSegRange_at p4Batch2.down (by omega) (by omega)
  · exact checkSegRange_at p4Batch3.down (by omega) (by omega)
  · exact checkSegRange_at p4Batch4.down (by omega) (by omega)
  · exact checkSegRange_at p4Batch5.down (by omega) (by omega)

def checkP5Batch (lo cnt : Nat) : Bool :=
  (List.range cnt).all (fun i =>
    let j := lo + i
    decide (P5[j + 1]! = P5[j]! + count16k (2097153 + 16384 * j)))

private lemma checkP5Batch_at {lo cnt j : Nat}
    (h : checkP5Batch lo cnt = true) (h1 : lo ≤ j) (h2 : j < lo + cnt) :
    P5[j + 1]! = P5[j]! + count16k (2097153 + 16384 * j) := by
  unfold checkP5Batch at h
  rw [List.all_eq_true] at h
  have hres := h (j - lo) (List.mem_range.mpr (by omega))
  dsimp only at hres
  rw [show lo + (j - lo) = j by omega] at hres
  exact decide_eq_true_eq.mp hres

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch0 : PLift (checkP5Batch 0 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch1 : PLift (checkP5Batch 25 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch2 : PLift (checkP5Batch 50 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch3 : PLift (checkP5Batch 75 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch4 : PLift (checkP5Batch 100 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch5 : PLift (checkP5Batch 125 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch6 : PLift (checkP5Batch 150 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch7 : PLift (checkP5Batch 175 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch8 : PLift (checkP5Batch 200 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch9 : PLift (checkP5Batch 225 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch10 : PLift (checkP5Batch 250 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch11 : PLift (checkP5Batch 275 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch12 : PLift (checkP5Batch 300 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch13 : PLift (checkP5Batch 325 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch14 : PLift (checkP5Batch 350 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch15 : PLift (checkP5Batch 375 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch16 : PLift (checkP5Batch 400 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch17 : PLift (checkP5Batch 425 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch18 : PLift (checkP5Batch 450 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch19 : PLift (checkP5Batch 475 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch20 : PLift (checkP5Batch 500 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch21 : PLift (checkP5Batch 525 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch22 : PLift (checkP5Batch 550 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch23 : PLift (checkP5Batch 575 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch24 : PLift (checkP5Batch 600 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch25 : PLift (checkP5Batch 625 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch26 : PLift (checkP5Batch 650 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch27 : PLift (checkP5Batch 675 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch28 : PLift (checkP5Batch 700 25 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def p5Batch29 : PLift (checkP5Batch 725 7 = true) := ⟨by decide +kernel⟩


private lemma P5_step : ∀ j < 732, P5[j + 1]! = P5[j]! + count16k (2097153 + 16384 * j) := by
  intro j hj
  have hcases : (0 ≤ j ∧ j < 25) ∨ (25 ≤ j ∧ j < 50) ∨ (50 ≤ j ∧ j < 75) ∨ (75 ≤ j ∧ j < 100) ∨ (100 ≤ j ∧ j < 125) ∨ (125 ≤ j ∧ j < 150) ∨ (150 ≤ j ∧ j < 175) ∨ (175 ≤ j ∧ j < 200) ∨ (200 ≤ j ∧ j < 225) ∨ (225 ≤ j ∧ j < 250) ∨ (250 ≤ j ∧ j < 275) ∨ (275 ≤ j ∧ j < 300) ∨ (300 ≤ j ∧ j < 325) ∨ (325 ≤ j ∧ j < 350) ∨ (350 ≤ j ∧ j < 375) ∨ (375 ≤ j ∧ j < 400) ∨ (400 ≤ j ∧ j < 425) ∨ (425 ≤ j ∧ j < 450) ∨ (450 ≤ j ∧ j < 475) ∨ (475 ≤ j ∧ j < 500) ∨ (500 ≤ j ∧ j < 525) ∨ (525 ≤ j ∧ j < 550) ∨ (550 ≤ j ∧ j < 575) ∨ (575 ≤ j ∧ j < 600) ∨ (600 ≤ j ∧ j < 625) ∨ (625 ≤ j ∧ j < 650) ∨ (650 ≤ j ∧ j < 675) ∨ (675 ≤ j ∧ j < 700) ∨ (700 ≤ j ∧ j < 725) ∨ (725 ≤ j ∧ j < 732) := by omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact checkP5Batch_at p5Batch0.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch1.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch2.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch3.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch4.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch5.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch6.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch7.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch8.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch9.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch10.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch11.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch12.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch13.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch14.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch15.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch16.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch17.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch18.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch19.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch20.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch21.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch22.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch23.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch24.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch25.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch26.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch27.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch28.down (by omega) (by omega)
  · exact checkP5Batch_at p5Batch29.down (by omega) (by omega)

theorem P5_correct : ∀ j ≤ 732, P5[j]! = Nat.primeCounting (2097152 + 16384 * j) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h1 := P4_correct 432 le_rfl
    have h2 : P5[0]! = P4[432]! := by decide +kernel
    simpa using h2.trans h1
  | succ j ih =>
    intro hj
    rw [P5_step j (by omega), ih (by omega)]
    have hcor := count16k_correct (lo := 2097153 + 16384 * j) (by omega) (by omega)
    rw [show 2097153 + 16384 * j + 16384 = 2097152 + 16384 * (j + 1) + 1 by omega] at hcor
    have hlo : (2097153 + 16384 * j).primeCounting' = (2097152 + 16384 * j).primeCounting := by
      rw [Nat.primeCounting, show 2097153 + 16384 * j = 2097152 + 16384 * j + 1 by omega]
    rw [hlo] at hcor
    exact hcor.symm

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def pi10MCheck : PLift (P5[482]! + countBlock 360 9994241 = 664579) := ⟨by decide +kernel⟩

theorem pi_10M_eq : Nat.primeCounting 10000000 = 664579 := by
  have h1 := P5_correct 482 (by decide)
  have h2 := countBlock_correct (m := 360) (lo := 9994241) (by decide) (by decide) (by decide)
  have h3 := pi10MCheck.down
  have hidx1 : 2097152 + 16384 * 482 = 9994240 := by decide
  rw [hidx1] at h1
  have h4 : Nat.primeCounting' 10000001 = Nat.primeCounting' 9994241 + countBlock 360 9994241 := h2
  change Nat.primeCounting' 10000001 = 664579
  rw [h4]
  change P5[482]! = Nat.primeCounting' 9994241 at h1
  omega

/- ### Lookup functions `piLoTbl` and `piHiTbl` on `[0, 14090240]` -/

def piLoTbl (n : Nat) : Nat :=
  if n ≤ 8192 then exactPiSmall n
  else if n ≤ 16384 then P1[(n - 8192) / 64]!
  else if n ≤ 65536 then P2[(n - 16384) / 128]!
  else if n ≤ 327680 then P3[(n - 65536) / 512]!
  else if n ≤ 2097152 then P4[(n - 327680) / 4096]!
  else P5[(n - 2097152) / 16384]!

def piHiTbl (n : Nat) : Nat :=
  if n ≤ 8192 then exactPiSmall n
  else if n ≤ 16384 then P1[(n - 8192 + 63) / 64]!
  else if n ≤ 65536 then P2[(n - 16384 + 127) / 128]!
  else if n ≤ 327680 then P3[(n - 65536 + 511) / 512]!
  else if n ≤ 2097152 then P4[(n - 327680 + 4095) / 4096]!
  else P5[(n - 2097152 + 16383) / 16384]!

theorem piLoTbl_le {n : Nat} (hn : n ≤ 14090240) : piLoTbl n ≤ n.primeCounting := by
  unfold piLoTbl
  split_ifs with h1 h2 h3 h4 h5
  · rw [exactPiSmall_correct h1]
  · rw [P1_correct ((n - 8192) / 64) (by omega)]
    exact Nat.monotone_primeCounting (by omega)
  · rw [P2_correct ((n - 16384) / 128) (by omega)]
    exact Nat.monotone_primeCounting (by omega)
  · rw [P3_correct ((n - 65536) / 512) (by omega)]
    exact Nat.monotone_primeCounting (by omega)
  · rw [P4_correct ((n - 327680) / 4096) (by omega)]
    exact Nat.monotone_primeCounting (by omega)
  · rw [P5_correct ((n - 2097152) / 16384) (by omega)]
    exact Nat.monotone_primeCounting (by omega)

theorem le_piHiTbl {n : Nat} (hn : n ≤ 14090240) : n.primeCounting ≤ piHiTbl n := by
  unfold piHiTbl
  split_ifs with h1 h2 h3 h4 h5
  · rw [exactPiSmall_correct h1]
  · rw [P1_correct ((n - 8192 + 63) / 64) (by omega)]
    exact Nat.monotone_primeCounting (by omega)
  · rw [P2_correct ((n - 16384 + 127) / 128) (by omega)]
    exact Nat.monotone_primeCounting (by omega)
  · rw [P3_correct ((n - 65536 + 511) / 512) (by omega)]
    exact Nat.monotone_primeCounting (by omega)
  · rw [P4_correct ((n - 327680 + 4095) / 4096) (by omega)]
    exact Nat.monotone_primeCounting (by omega)
  · rw [P5_correct ((n - 2097152 + 16383) / 16384) (by omega)]
    exact Nat.monotone_primeCounting (by omega)


end ColtonTables


/- ===================== Mod2C_Checks.lean ===================== -/

/-
Module 2C: Bit-packed O(1) prime-table lookups, Zelinsky disjoint generator check for
Colton's conjecture through 14,090,240, zero-calculus lower bounds on `π(x)` for
`[101, 10^7]` and `[2000, 10^7]`, and `θ(10^7)` integral pinning.
-/

namespace ColtonTables

open Finset Real Chebyshev OeisA111291 ColtonSieve ColtonSWAR ColtonSmall ColtonFactor ColtonBase4096 ColtonPiAbel

/- ### Bit-packed O(1) kernel lookup tables (`20 bits` per entry) -/

def pack20 : List Nat → Nat
  | [] => 0
  | x :: xs => x + (pack20 xs <<< 20)

def get20 (tbl i : Nat) : Nat := (tbl >>> (20 * i)) % 1048576

private lemma get20_pack20 : ∀ (xs : List Nat) (i : Nat),
    (∀ x ∈ xs, x < 1048576) → i < xs.length → get20 (pack20 xs) i = xs[i]! := by
  intro xs
  induction xs with
  | nil => intro i _ hi; simp at hi
  | cons x xs ih =>
    intro i hlt hi
    have hx : x < 1048576 := hlt x (by simp)
    have hxs : ∀ y ∈ xs, y < 1048576 := fun y hy => hlt y (List.mem_cons_of_mem _ hy)
    cases i with
    | zero =>
      unfold get20 pack20
      simp only [Nat.mul_zero, Nat.shiftRight_zero, Nat.shiftLeft_eq]
      rw [show (2 : Nat) ^ 20 = 1048576 by decide, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx]
      rfl
    | succ j =>
      have hsh : (x + (pack20 xs <<< 20)) >>> 20 = pack20 xs := by
        rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
          show (2 : Nat) ^ 20 = 1048576 by decide,
          Nat.add_mul_div_right _ _ (by decide : 0 < 1048576), Nat.div_eq_of_lt hx, Nat.zero_add]
      have hget : get20 (pack20 (x :: xs)) (j + 1) = get20 (pack20 xs) j := by
        change ((x + (pack20 xs <<< 20)) >>> (20 * (j + 1))) % 1048576 = (pack20 xs >>> (20 * j)) % 1048576
        rw [show 20 * (j + 1) = 20 + 20 * j by omega, Nat.shiftRight_add, hsh]
      rw [hget, ih j hxs (by simpa using hi)]
      rfl

def P0p : Nat := pack20 ((List.range 513).map (fun j => exactPiSmall (16 * j)))
def P1p : Nat := pack20 P1.toList
def P2p : Nat := pack20 P2.toList
def P3p : Nat := pack20 P3.toList
def P4p : Nat := pack20 P4.toList
def P5p : Nat := pack20 P5.toList

set_option maxHeartbeats 0 in
private def packedBoundsCheck : PLift (
    P1.toList.length = 129 ∧ P1.toList.all (fun x => decide (x < 1048576)) = true ∧
    P2.toList.length = 385 ∧ P2.toList.all (fun x => decide (x < 1048576)) = true ∧
    P3.toList.length = 513 ∧ P3.toList.all (fun x => decide (x < 1048576)) = true ∧
    P4.toList.length = 433 ∧ P4.toList.all (fun x => decide (x < 1048576)) = true ∧
    P5.toList.length = 733 ∧ P5.toList.all (fun x => decide (x < 1048576)) = true) := ⟨by decide +kernel⟩

private lemma get20_array_eq (arr : Array Nat) (n : Nat)
    (hlen : arr.toList.length = n) (hlt : arr.toList.all (fun x => decide (x < 1048576)) = true)
    {j : Nat} (hj : j < n) : get20 (pack20 arr.toList) j = arr[j]! := by
  have h1 := get20_pack20 arr.toList j
    (fun x hx => decide_eq_true_eq.mp (List.all_eq_true.mp hlt x hx)) (hlen ▸ hj)
  rw [h1]
  have hlt_a : j < arr.size := by rw [← Array.length_toList, hlen]; exact hj
  have hlt_l : j < arr.toList.length := hlen ▸ hj
  rw [getElem!_pos arr j hlt_a, getElem!_pos arr.toList j hlt_l]
  rfl

private lemma get20_pack20_map (f : Nat → Nat) (n : Nat) (hf : ∀ i < n, f i < 1048576)
    {j : Nat} (hj : j < n) :
    get20 (pack20 ((List.range n).map f)) j = f j := by
  have hlt : ∀ x ∈ (List.range n).map f, x < 1048576 := by
    intro x hx; obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx; exact hf i (List.mem_range.mp hi)
  have hpos : j < ((List.range n).map f).length := by simp [hj]
  rw [get20_pack20 ((List.range n).map f) j hlt hpos, getElem!_pos ((List.range n).map f) j hpos]
  simp [List.getElem_map, List.getElem_range]

lemma P0p_correct {j : Nat} (hj : j ≤ 512) : get20 P0p j = Nat.primeCounting (16 * j) := by
  unfold P0p
  have hf : ∀ i < 513, exactPiSmall (16 * i) < 1048576 := by
    intro i hi
    rw [exactPiSmall_correct (by omega : 16 * i ≤ 8192)]
    have hle := Nat.monotone_primeCounting (show 16 * i ≤ 8192 by omega)
    have h8k : Nat.primeCounting 8192 = 1028 := by
      rw [← exactPiSmall_correct (by decide : 8192 ≤ 8192)]; decide +kernel
    omega
  rw [get20_pack20_map (fun i => exactPiSmall (16 * i)) 513 hf (by omega)]
  exact exactPiSmall_correct (by omega : 16 * j ≤ 8192)

lemma P1p_correct {j : Nat} (hj : j ≤ 128) : get20 P1p j = Nat.primeCounting (8192 + 64 * j) := by
  obtain ⟨h1l, h1b, _⟩ := packedBoundsCheck.down
  rw [P1p, get20_array_eq P1 129 h1l h1b (by omega), P1_correct j hj]

lemma P2p_correct {j : Nat} (hj : j ≤ 384) : get20 P2p j = Nat.primeCounting (16384 + 128 * j) := by
  obtain ⟨_, _, h2l, h2b, _⟩ := packedBoundsCheck.down
  rw [P2p, get20_array_eq P2 385 h2l h2b (by omega), P2_correct j hj]

lemma P3p_correct {j : Nat} (hj : j ≤ 512) : get20 P3p j = Nat.primeCounting (65536 + 512 * j) := by
  obtain ⟨_, _, _, _, h3l, h3b, _⟩ := packedBoundsCheck.down
  rw [P3p, get20_array_eq P3 513 h3l h3b (by omega), P3_correct j hj]

lemma P4p_correct {j : Nat} (hj : j ≤ 432) : get20 P4p j = Nat.primeCounting (327680 + 4096 * j) := by
  obtain ⟨_, _, _, _, _, _, h4l, h4b, _⟩ := packedBoundsCheck.down
  rw [P4p, get20_array_eq P4 433 h4l h4b (by omega), P4_correct j hj]

lemma P5p_correct {j : Nat} (hj : j ≤ 732) : get20 P5p j = Nat.primeCounting (2097152 + 16384 * j) := by
  obtain ⟨_, _, _, _, _, _, _, _, h5l, h5b⟩ := packedBoundsCheck.down
  rw [P5p, get20_array_eq P5 733 h5l h5b (by omega), P5_correct j hj]

def piLoFast (n : Nat) : Nat :=
  if n ≤ 256 then exactPiSmall n
  else if n ≤ 8192 then get20 P0p (n / 16)
  else if n ≤ 16384 then get20 P1p ((n - 8192) / 64)
  else if n ≤ 65536 then get20 P2p ((n - 16384) / 128)
  else if n ≤ 327680 then get20 P3p ((n - 65536) / 512)
  else if n ≤ 2097152 then get20 P4p ((n - 327680) / 4096)
  else get20 P5p ((n - 2097152) / 16384)

def piHiFast (n : Nat) : Nat :=
  if n ≤ 256 then exactPiSmall n
  else if n ≤ 8192 then get20 P0p ((n + 15) / 16)
  else if n ≤ 16384 then get20 P1p ((n - 8192 + 63) / 64)
  else if n ≤ 65536 then get20 P2p ((n - 16384 + 127) / 128)
  else if n ≤ 327680 then get20 P3p ((n - 65536 + 511) / 512)
  else if n ≤ 2097152 then get20 P4p ((n - 327680 + 4095) / 4096)
  else get20 P5p ((n - 2097152 + 16383) / 16384)

theorem piLoFast_le {n : Nat} (hn : n ≤ 14090240) : piLoFast n ≤ n.primeCounting := by
  unfold piLoFast
  split_ifs with h0 h1 h2 h3 h4 h5
  · rw [exactPiSmall_correct (by omega)]
  · rw [P0p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)
  · rw [P1p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)
  · rw [P2p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)
  · rw [P3p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)
  · rw [P4p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)
  · rw [P5p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)

theorem le_piHiFast {n : Nat} (hn : n ≤ 14090240) : n.primeCounting ≤ piHiFast n := by
  unfold piHiFast
  split_ifs with h0 h1 h2 h3 h4 h5
  · rw [exactPiSmall_correct (by omega)]
  · rw [P0p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)
  · rw [P1p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)
  · rw [P2p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)
  · rw [P3p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)
  · rw [P4p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)
  · rw [P5p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)

def piHiTblFast (n : Nat) : Nat :=
  if n ≤ 8192 then exactPiSmall n
  else if n ≤ 16384 then get20 P1p ((n - 8192 + 63) / 64)
  else if n ≤ 65536 then get20 P2p ((n - 16384 + 127) / 128)
  else if n ≤ 327680 then get20 P3p ((n - 65536 + 511) / 512)
  else if n ≤ 2097152 then get20 P4p ((n - 327680 + 4095) / 4096)
  else get20 P5p ((n - 2097152 + 16383) / 16384)

theorem le_piHiTblFast {n : Nat} (hn : n ≤ 14090240) : n.primeCounting ≤ piHiTblFast n := by
  unfold piHiTblFast
  split_ifs with h1 h2 h3 h4 h5
  · rw [exactPiSmall_correct h1]
  · rw [P1p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)
  · rw [P2p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)
  · rw [P3p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)
  · rw [P4p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)
  · rw [P5p_correct (by omega)]; exact Nat.monotone_primeCounting (by omega)

/- ### Zelinsky disjoint generator count + Colton verification on `[0, 14090240]` -/

theorem prime_le_top {p k : Nat} (hp : p.Prime) (hd : p ∣ k) (hk : k ≠ 0) :
    p ≤ k.primeFactors.sup id :=
  Finset.le_sup (f := id) (hp.mem_primeFactors hd hk)

theorem product_good {k p : Nat} (hk : 0 < k ∧ 2 * k.divisors.card ∣ k) (hp : p.Prime)
    (hlt : k.primeFactors.sup id < p) : (k * p).IsRefactorable := by
  have hnd : ¬ p ∣ k := fun h => hlt.not_ge (prime_le_top hp h hk.1.ne')
  have hc : k.Coprime p := (hp.coprime_iff_not_dvd.mpr hnd).symm
  refine ⟨Nat.mul_pos hk.1 hp.pos, ?_⟩
  rw [Nat.Coprime.card_divisors_mul hc, hp.divisors, Finset.card_pair hp.ne_one.symm]
  simpa [Nat.mul_comm] using dvd_mul_of_dvd_left hk.2 p

theorem maxPrime_inj {k p l q : Nat} (hk : 0 < k) (hl : 0 < l)
    (hp : p.Prime) (hq : q.Prime) (hkp : k.primeFactors.sup id < p) (hlq : l.primeFactors.sup id < q)
    (h : k * p = l * q) : k = l ∧ p = q := by
  have step {u v r s : Nat} (hu : 0 < u) (hr : r.Prime) (hs : s.Prime)
      (hus : u.primeFactors.sup id < s) (heq : v * r = u * s) : r ≤ s := by
    have hd : r ∣ u * s := heq ▸ dvd_mul_left r v
    rcases hr.dvd_mul.mp hd with hdu | hds
    · exact (prime_le_top hr hdu hu.ne').trans hus.le
    · exact Nat.le_of_dvd hs.pos hds
  have he := le_antisymm (step hl hp hq hlq h) (step hk hq hp hkp h.symm)
  subst q
  exact ⟨Nat.eq_of_mul_eq_mul_right hp.pos h, rfl⟩

theorem seed_add_generated {B n : Nat} (hBn : B ≤ n) (G : Finset Nat)
    (hG : ∀ k ∈ G, 0 < k ∧ 2 * k.divisors.card ∣ k) :
    countRefactorableNat B +
      ∑ k ∈ G, ((n / k).primeCounting - (max (k.primeFactors.sup id) (B / k)).primeCounting) ≤
      countRefactorableNat n := by
  classical
  let seed := (Icc 1 B).filter Nat.IsRefactorable
  let choices (k : Nat) := Nat.primesLE (n / k) \ Nat.primesLE (max (k.primeFactors.sup id) (B / k))
  have specs {k p : Nat} (hp : p ∈ choices k) :
      p.Prime ∧ max (k.primeFactors.sup id) (B / k) < p ∧ p ≤ n / k := by
    obtain ⟨hp1, hp2⟩ := mem_sdiff.mp hp
    obtain ⟨hp3, hp4⟩ := Nat.mem_primesLE.mp hp1
    exact ⟨hp4, lt_of_not_ge (fun h => hp2 (Nat.mem_primesLE.mpr ⟨h, hp4⟩)), hp3⟩
  have hs (k : Nat) :
      (n / k).primeCounting - (max (k.primeFactors.sup id) (B / k)).primeCounting ≤ (choices k).card := by
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
      show (choices k).card = _ from Finset.card_sdiff ..]
    exact Nat.sub_le_sub_left (Finset.card_le_card Finset.inter_subset_left) _
  let products := G.sigma choices
  have hpgt {k p : Nat} (hk : 0 < k) (hp : max (k.primeFactors.sup id) (B / k) < p) : B < k * p := by
    have h := (Nat.div_lt_iff_lt_mul hk).mp ((le_max_right _ _).trans_lt hp)
    simpa [Nat.mul_comm] using h
  let f : Nat ⊕ (Σ _k : Nat, Nat) → Nat := Sum.elim id (fun t => t.1 * t.2)
  calc
    _ ≤ seed.card + products.card := by
      dsimp only [products]
      rw [Finset.card_sigma]
      exact Nat.add_le_add_left (Finset.sum_le_sum (fun k _ => hs k)) _
    _ = (seed.disjSum products).card := (Finset.card_disjSum _ _).symm
    _ ≤ _ := by
      unfold countRefactorableNat
      apply Finset.card_le_card_of_injOn f
      · rintro (a | ⟨k, p⟩) h
        · have ha := Finset.mem_filter.mp (Finset.inl_mem_disjSum.mp h)
          exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp ha.1).1, (mem_Icc.mp ha.1).2.trans hBn⟩, ha.2⟩
        · obtain ⟨hk, hp⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp h)
          obtain ⟨hpp, hpl, hpu⟩ := specs hp
          have hgen := hG k hk
          have hgood := product_good hgen hpp ((le_max_left _ _).trans_lt hpl)
          refine mem_filter.mpr ⟨mem_Icc.mpr ⟨hgood.1, ?_⟩, hgood⟩
          change k * p ≤ n
          simpa only [Nat.mul_comm p k] using (Nat.le_div_iff_mul_le hgen.1).mp hpu
      · rintro (a | ⟨k, p⟩) ha (b | ⟨l, q⟩) hb heq
        · exact congrArg Sum.inl heq
        · have ha' := (mem_Icc.mp (mem_filter.mp (Finset.inl_mem_disjSum.mp ha)).1).2
          obtain ⟨hl, hq⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp hb)
          have hgt : B < l * q := hpgt (hG l hl).1 (specs hq).2.1
          change a = l * q at heq
          omega
        · have hb' := (mem_Icc.mp (mem_filter.mp (Finset.inl_mem_disjSum.mp hb)).1).2
          obtain ⟨hk, hp⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp ha)
          have hgt : B < k * p := hpgt (hG k hk).1 (specs hp).2.1
          change k * p = b at heq
          omega
        · obtain ⟨hk, hp⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp ha)
          obtain ⟨hl, hq⟩ := Finset.mem_sigma.mp (Finset.inr_mem_disjSum.mp hb)
          obtain ⟨rfl, rfl⟩ := maxPrime_inj (hG k hk).1 (hG l hl).1 (specs hp).1 (specs hq).1
            ((le_max_left _ _).trans_lt (specs hp).2.1) ((le_max_left _ _).trans_lt (specs hq).2.1) heq
          rfl

def primesLe100 : List Nat :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

private lemma primesLe100_prime : ∀ p ∈ primesLe100, p.Prime := by decide +kernel
private lemma primesLe100_nodup : primesLe100.Nodup := by decide +kernel
private lemma primesLe100_cov : ∀ p, p.Prime → p < 101 → p ∈ primesLe100 := by
  intro p hp hlt
  have : ∀ k : Fin 101, k.val.Prime → k.val ∈ primesLe100 := by decide +kernel
  exact this ⟨p, hlt⟩ hp

/-- Precomputed `(k, max(P+(k), 4096/k), piHiFast(max(P+(k), 4096/k)))` for 221 generators ≤ 10,000. -/
def gens10kInfo : List (Nat × Nat × Nat) := [
  (8, 512, 97), (12, 341, 70), (36, 113, 30), (72, 56, 16), (80, 51, 15), (96, 42, 13), (128, 32, 11), (180, 22, 8),
  (240, 17, 7), (252, 16, 6), (288, 14, 6), (384, 10, 4), (396, 11, 5), (448, 9, 4), (468, 13, 6), (480, 8, 4),
  (560, 7, 4), (612, 17, 7), (640, 6, 3), (672, 7, 4), (684, 19, 8), (720, 5, 3), (828, 23, 9), (864, 4, 2),
  (880, 11, 5), (896, 7, 4), (972, 4, 2), (1040, 13, 6), (1044, 29, 10), (1056, 11, 5), (1116, 31, 11), (1152, 3, 2),
  (1200, 5, 3), (1248, 13, 6), (1332, 37, 12), (1344, 7, 4), (1360, 17, 7), (1408, 11, 5), (1440, 5, 3), (1476, 41, 13),
  (1520, 19, 8), (1548, 43, 14), (1620, 5, 3), (1632, 17, 7), (1664, 13, 6), (1680, 7, 4), (1692, 47, 15), (1800, 5, 3),
  (1824, 19, 8), (1840, 23, 9), (1908, 53, 16), (1920, 5, 3), (2000, 5, 3), (2016, 7, 4), (2124, 59, 17), (2160, 5, 3),
  (2176, 17, 7), (2196, 61, 18), (2208, 23, 9), (2240, 7, 4), (2320, 29, 10), (2412, 67, 19), (2432, 19, 8), (2480, 31, 11),
  (2556, 71, 20), (2560, 5, 3), (2628, 73, 21), (2640, 11, 5), (2688, 7, 4), (2784, 29, 10), (2844, 79, 22), (2944, 23, 9),
  (2960, 37, 12), (2976, 31, 11), (2988, 83, 23), (3120, 13, 6), (3168, 11, 5), (3204, 89, 24), (3280, 41, 13), (3360, 7, 4),
  (3440, 43, 14), (3456, 3, 2), (3492, 97, 25), (3528, 7, 4), (3552, 37, 12), (3600, 5, 3), (3636, 101, 26), (3708, 103, 27),
  (3712, 29, 10), (3744, 13, 6), (3760, 47, 15), (3852, 107, 28), (3924, 109, 29), (3936, 41, 13), (3968, 31, 11), (4032, 7, 4),
  (4068, 113, 30), (4080, 17, 7), (4128, 43, 14), (4224, 11, 5), (4240, 53, 16), (4320, 5, 3), (4480, 7, 4), (4512, 47, 15),
  (4560, 19, 8), (4572, 127, 31), (4716, 131, 32), (4720, 59, 17), (4736, 37, 12), (4880, 61, 18), (4896, 17, 7), (4928, 11, 5),
  (4932, 137, 33), (4992, 13, 6), (5000, 5, 3), (5004, 139, 34), (5040, 7, 4), (5088, 53, 16), (5248, 41, 13), (5280, 11, 5),
  (5360, 67, 19), (5364, 149, 35), (5436, 151, 36), (5472, 19, 8), (5504, 43, 14), (5520, 23, 9), (5652, 157, 37), (5664, 59, 17),
  (5680, 71, 20), (5760, 5, 3), (5824, 13, 6), (5840, 73, 21), (5856, 61, 18), (5868, 163, 38), (6000, 5, 3), (6012, 167, 39),
  (6016, 47, 15), (6048, 7, 4), (6144, 3, 2), (6160, 11, 5), (6228, 173, 40), (6240, 13, 6), (6320, 79, 22), (6432, 67, 19),
  (6444, 179, 41), (6516, 181, 42), (6528, 17, 7), (6624, 23, 9), (6640, 83, 23), (6720, 7, 4), (6784, 53, 16), (6816, 71, 20),
  (6876, 191, 43), (6912, 3, 2), (6948, 193, 44), (6960, 29, 10), (7008, 73, 21), (7040, 11, 5), (7092, 197, 45), (7120, 89, 24),
  (7164, 199, 46), (7280, 13, 6), (7296, 19, 8), (7392, 11, 5), (7440, 31, 11), (7500, 5, 3), (7552, 59, 17), (7584, 79, 22),
  (7596, 211, 47), (7616, 17, 7), (7680, 5, 3), (7760, 97, 25), (7776, 3, 2), (7808, 61, 18), (7920, 11, 5), (7968, 83, 23),
  (8028, 223, 48), (8064, 7, 4), (8080, 101, 26), (8100, 5, 3), (8160, 17, 7), (8172, 227, 49), (8240, 103, 27), (8244, 229, 50),
  (8320, 13, 6), (8352, 29, 10), (8388, 233, 51), (8400, 7, 4), (8512, 19, 8), (8544, 89, 24), (8560, 107, 28), (8576, 67, 19),
  (8604, 239, 52), (8676, 241, 53), (8712, 11, 5), (8720, 109, 29), (8736, 13, 6), (8832, 23, 9), (8880, 37, 12), (8928, 31, 11),
  (9036, 251, 54), (9040, 113, 30), (9088, 71, 20), (9120, 19, 8), (9252, 257, 58), (9312, 97, 25), (9344, 73, 21), (9360, 13, 6),
  (9408, 7, 4), (9468, 263, 58), (9504, 11, 5), (9520, 17, 7), (9600, 5, 3), (9684, 269, 58), (9696, 101, 26), (9756, 271, 58),
  (9840, 41, 13), (9856, 11, 5), (9888, 103, 27), (9972, 277, 61), (10000, 5, 3)
]

def grid14M : List Nat := [
  4096, 4512, 4848, 5104, 5440, 5824, 6256, 6640, 6944, 7296, 7696, 8080, 8512, 8960,
  9408, 9792, 10112, 10432, 10816, 11200, 11520, 12032, 12416, 12800, 13248, 13760, 14272, 14720,
  15232, 15680, 16064, 16512, 17024, 17408, 17920, 18432, 19200, 19968, 20736, 21504, 22272, 22912,
  23680, 24320, 25088, 25728, 26624, 27520, 28416, 29440, 30720, 32000, 33024, 34304, 35712, 37248,
  38784, 40448, 42112, 43904, 45952, 48128, 50304, 52864, 55552, 58112, 60928, 64000, 67072, 70656,
  74752, 78848, 83456, 88064, 93184, 98816, 104448, 111104, 118272, 126464, 135168, 144384, 154112, 164864,
  176640, 189440, 204288, 219648, 237056, 255488, 274944, 297472, 321536, 348160, 376832, 405504, 438272, 475136,
  516096, 561152, 606208, 655360, 708608, 770048, 835584, 905216, 983040, 1069056, 1159168, 1257472, 1359872, 1470464,
  1593344, 1724416, 1863680, 2015232, 2162688, 2326528, 2506752, 2686976, 2883584, 3096576, 3309568, 3538944, 3784704, 4046848,
  4308992, 4587520, 4882432, 5193728, 5505024, 5849088, 6193152, 6569984, 6946816, 7340032, 7749632, 8159232, 8601600, 9043968,
  9502720, 9977856, 10452992, 10944512, 11452416, 11960320, 12484608, 13008896, 13549568, 14090240
]

set_option maxHeartbeats 0 in
private lemma gens10kInfo_valid :
    (gens10kInfo.map Prod.fst).IsChain (· < ·) ∧
    gens10kInfo.all (fun t =>
      let ft := fastTauTop 14 primesLe100 t.1
      let cut := max ft.2 (4096 / t.1)
      decide (0 < t.1 ∧ t.1 ≤ 10000 ∧ t.1 % (2 * ft.1) = 0 ∧ t.2.1 = cut ∧ t.2.2 = piHiFast cut)) = true := by
  decide +kernel

private lemma nodup_of_isChain_lt {L : List Nat} (h : L.IsChain (· < ·)) : L.Nodup :=
  List.Pairwise.nodup (List.isChain_iff_pairwise.mp h)

private def checkGridStep (a b : Nat) : Bool :=
  let lb := 307 + (gens10kInfo.map (fun t =>
    let q := a / t.1
    if q ≤ t.2.1 then 0 else piLoFast q - t.2.2)).sum
  decide (piHiFast b ≤ 2 * lb)

private def checkGridList : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => checkGridStep a b && checkGridList (b :: rest)

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def grid14MCheck : PLift (
    2 ≤ grid14M.length ∧
    grid14M.head? = some 4096 ∧
    grid14M.getLast? = some 14090240 ∧
    grid14M.IsChain (· ≤ ·) ∧
    checkGridList grid14M = true) := ⟨by decide +kernel⟩

private lemma info_sum_le_finset_sum {L : List (Nat × Nat × Nat)}
    (hnd : (L.map Prod.fst).Nodup) (f : Nat × Nat × Nat → Nat) (g : Nat → Nat)
    (hfg : ∀ t ∈ L, f t ≤ g t.1) :
    (L.map f).sum ≤ ∑ k ∈ (L.map Prod.fst).toFinset, g k := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons] at hnd ⊢
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    simp only [List.sum_cons, List.toFinset_cons]
    rw [Finset.sum_insert (by simp [hx])]
    exact Nat.add_le_add (hfg x (by simp)) (ih hnd' (fun t ht => hfg t (List.mem_cons_of_mem _ ht)))

private lemma grid_step_sound {a b : Nat} (ha : 4096 ≤ a) (_hab : a ≤ b) (hb : b ≤ 14090240)
    (hchk : checkGridStep a b = true) :
    ∀ n, a ≤ n → n ≤ b → n.primeCounting ≤ 2 * countRefactorableNat n := by
  intro n han hnb
  have hnd : (gens10kInfo.map Prod.fst).Nodup := nodup_of_isChain_lt gens10kInfo_valid.1
  have hgen : ∀ k ∈ (gens10kInfo.map Prod.fst).toFinset, 0 < k ∧ 2 * k.divisors.card ∣ k := by
    intro k hk
    obtain ⟨t, htL, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    have hall := List.all_eq_true.mp gens10kInfo_valid.2 t htL
    obtain ⟨hk0, hk10k, hmod, _, _⟩ := decide_eq_true_eq.mp hall
    have hspec := fastTauTop_spec primesLe100_prime primesLe100_nodup primesLe100_cov
      hk0 (by omega : t.1 < 2 ^ 14) (by omega : t.1 < 101 * 101)
    rw [hspec.1] at hmod
    exact ⟨hk0, Nat.dvd_of_mod_eq_zero hmod⟩
  have hseed := seed_add_generated (B := 4096) (n := a) ha (gens10kInfo.map Prod.fst).toFinset hgen
  rw [countRefactorableNat_4096] at hseed
  have hsum : (gens10kInfo.map (fun t =>
      let q := a / t.1
      if q ≤ t.2.1 then 0 else piLoFast q - t.2.2)).sum ≤
      ∑ k ∈ (gens10kInfo.map Prod.fst).toFinset,
        ((a / k).primeCounting - (max (k.primeFactors.sup id) (4096 / k)).primeCounting) := by
    refine info_sum_le_finset_sum hnd _ _ fun t htL => ?_
    dsimp only
    split_ifs with hq
    · exact Nat.zero_le _
    · have hall := List.all_eq_true.mp gens10kInfo_valid.2 t htL
      obtain ⟨hk0, hk10k, _, hcut, hpiCut⟩ := decide_eq_true_eq.mp hall
      have hspec := fastTauTop_spec primesLe100_prime primesLe100_nodup primesLe100_cov
        hk0 (by omega : t.1 < 2 ^ 14) (by omega : t.1 < 101 * 101)
      have htop_le : t.1.primeFactors.sup id ≤ t.1 := by
        apply Finset.sup_le; intro p hp
        exact Nat.le_of_dvd hk0 (Nat.dvd_of_mem_primeFactors hp)
      rw [hpiCut, hspec.2]
      exact tsub_le_tsub (piLoFast_le (by have := Nat.div_le_self a t.1; omega))
        (le_piHiFast (by have := Nat.div_le_self 4096 t.1; omega))
  unfold checkGridStep at hchk
  have hchk' := decide_eq_true_eq.mp hchk
  have hpi : n.primeCounting ≤ piHiFast b :=
    (Nat.monotone_primeCounting hnb).trans (le_piHiFast hb)
  have href : countRefactorableNat a ≤ countRefactorableNat n := by
    unfold countRefactorableNat
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right han))
  omega

private lemma grid_chain_sound :
    ∀ (L : List Nat) (a b : Nat),
      2 ≤ L.length →
      L.head? = some a → L.getLast? = some b → 4096 ≤ a → b ≤ 14090240 →
      L.IsChain (· ≤ ·) → checkGridList L = true →
      ∀ n, a ≤ n → n ≤ b → n.primeCounting ≤ 2 * countRefactorableNat n := by
  intro L
  induction L with
  | nil => intro _ _ hlen; simp at hlen
  | cons x rest ih =>
    rcases rest with _ | ⟨y, rest'⟩
    · intro _ _ hlen; simp at hlen
    · intro a b _ h1 h2 ha hb hch hok n hn1 hn2
      simp only [List.head?_cons, Option.some.injEq] at h1
      subst h1
      obtain ⟨hxy, hch'⟩ := List.isChain_cons_cons.mp hch
      unfold checkGridList at hok
      obtain ⟨hstep, hok'⟩ := Bool.and_eq_true _ _ |>.mp hok
      have hlast' : (y :: rest').getLast? = some b := by simpa [List.getLast?_cons_cons] using h2
      have hyb : y ≤ b := by
        have hmem : ∀ (M : List Nat) (u v : Nat),
            M.head? = some u → M.getLast? = some v → M.IsChain (· ≤ ·) → u ≤ v := by
          intro M
          induction M with
          | nil => intro _ _ h; simp at h
          | cons u0 ms ihM =>
            rcases ms with _ | ⟨u1, ms'⟩
            · intro u v hu hv _; simp at hu hv; subst hu; subst hv; exact le_rfl
            · intro u v hu hv hc
              simp at hu; subst hu
              have h01 := (List.isChain_cons_cons.mp hc).1
              have h1v := ihM u1 v rfl (by simpa [List.getLast?_cons_cons] using hv)
                (List.isChain_cons_cons.mp hc).2
              omega
        exact hmem (y :: rest') y b rfl hlast' hch'
      by_cases hny : n ≤ y
      · exact grid_step_sound ha hxy (hyb.trans hb) hstep n hn1 hny
      · rcases rest' with _ | ⟨z, rest''⟩
        · simp only [List.getLast?_singleton, Option.some.injEq] at hlast'
          subst hlast'; omega
        · exact ih y b (by simp) rfl hlast' (by omega) hb hch' hok' n (by omega) hn2

theorem colton_le_14M : ∀ n ≤ 14090240, n.primeCounting ≤ 2 * countRefactorableNat n := by
  intro n hn
  by_cases h4096 : n ≤ 4096
  · exact colton_le_4096 n h4096
  · obtain ⟨hlen, hhead, hlast, hch, hok⟩ := grid14MCheck.down
    exact grid_chain_sound grid14M 4096 14090240 hlen hhead hlast le_rfl le_rfl hch hok n (by omega) hn

/- ### Zero-calculus `π(x)` lower bounds on `[101, 10^7]` and `[2000, 10^7]` -/

private lemma f1_interval_sound {a b : Nat} {x : ℝ} (ha : 101 ≤ a) (hax : (a : ℝ) ≤ x) (hxb : x ≤ b)
    (hchk : 9400 * b * logScale * (logNatLo a + logScale) ≤ 10000 * a.primeCounting * (logNatLo a) ^ 2) :
    0.9400 * (x / Real.log x + x / (Real.log x) ^ 2) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have ha1 : 1 ≤ a := by omega
  have hlog_lo := (logRatBounds_correct (a := a) (b := 1) le_rfl ha1).1
  simp only [Nat.cast_one, div_one] at hlog_lo
  have hL_pos : 0 < logNatLo a := by
    by_contra h0
    have hL0 : logNatLo a = 0 := by omega
    rw [hL0] at hchk
    have : 9400 * b * logScale * (0 + logScale) = 0 := by omega
    have hbpos : 0 < b := by
      have : (101 : ℝ) ≤ b := by linarith [show (101 : ℝ) ≤ a by exact_mod_cast ha]
      exact_mod_cast (by linarith : (0 : ℝ) < b)
    have : 0 < 9400 * b * logScale * (0 + logScale) := by
      unfold logScale; positivity
    omega
  have hS_pos : (0 : ℝ) < logScale := by norm_num [logScale]
  have hLR_pos : (0 : ℝ) < (logNatLo a : ℝ) / logScale := by positivity
  have hlogx_ge : (logNatLo a : ℝ) / logScale ≤ Real.log x :=
    hlog_lo.trans (Real.log_le_log (by exact_mod_cast (show 0 < a by omega)) hax)
  have hlogx_pos : 0 < Real.log x := lt_of_lt_of_le hLR_pos hlogx_ge
  have h1 : x / Real.log x ≤ (b : ℝ) / ((logNatLo a : ℝ) / logScale) := by
    calc x / Real.log x ≤ (b : ℝ) / Real.log x := div_le_div_of_nonneg_right hxb hlogx_pos.le
      _ ≤ (b : ℝ) / ((logNatLo a : ℝ) / logScale) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg b) hLR_pos hlogx_ge
  have h2 : x / (Real.log x) ^ 2 ≤ (b : ℝ) / ((logNatLo a : ℝ) / logScale) ^ 2 := by
    have hsq : ((logNatLo a : ℝ) / logScale) ^ 2 ≤ (Real.log x) ^ 2 :=
      pow_le_pow_left₀ hLR_pos.le hlogx_ge 2
    calc x / (Real.log x) ^ 2 ≤ (b : ℝ) / (Real.log x) ^ 2 :=
          div_le_div_of_nonneg_right hxb (by positivity)
      _ ≤ (b : ℝ) / ((logNatLo a : ℝ) / logScale) ^ 2 :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg b) (by positivity) hsq
  have hchkR : (9400 : ℝ) * b * logScale * ((logNatLo a : ℝ) + logScale) ≤
      10000 * (a.primeCounting : ℝ) * (logNatLo a : ℝ) ^ 2 := by exact_mod_cast hchk
  have h3 : 0.9400 * ((b : ℝ) / ((logNatLo a : ℝ) / logScale) +
      (b : ℝ) / ((logNatLo a : ℝ) / logScale) ^ 2) ≤ (a.primeCounting : ℝ) := by
    have hLne : (logNatLo a : ℝ) ≠ 0 := (by exact_mod_cast hL_pos : (0 : ℝ) < logNatLo a).ne'
    have hSne : (logScale : ℝ) ≠ 0 := hS_pos.ne'
    have heq : 0.9400 * ((b : ℝ) / ((logNatLo a : ℝ) / logScale) +
        (b : ℝ) / ((logNatLo a : ℝ) / logScale) ^ 2) =
        ((9400 : ℝ) * b * logScale * ((logNatLo a : ℝ) + logScale)) /
          (10000 * (logNatLo a : ℝ) ^ 2) := by
      field_simp; ring
    rw [heq, div_le_iff₀ (by positivity)]
    linarith
  have hpi : (a.primeCounting : ℝ) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    exact_mod_cast Nat.monotone_primeCounting (Nat.le_floor hax)
  linarith

private lemma f2_interval_sound {a b : Nat} {x : ℝ} (ha : 2000 ≤ a) (hax : (a : ℝ) ≤ x) (hxb : x ≤ b)
    (hgt : logScale < logNatLo a)
    (hchk : 990 * b * logScale ≤ 1000 * a.primeCounting * (logNatLo a - logScale)) :
    0.990 * (x / (Real.log x - 1)) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have ha1 : 1 ≤ a := by omega
  have hlog_lo := (logRatBounds_correct (a := a) (b := 1) le_rfl ha1).1
  simp only [Nat.cast_one, div_one] at hlog_lo
  have hS_pos : (0 : ℝ) < logScale := by norm_num [logScale]
  have hd_pos : (0 : ℝ) < ((logNatLo a - logScale : Nat) : ℝ) :=
    Nat.cast_pos.mpr (by omega)
  have hL_sub_pos : (0 : ℝ) < ((logNatLo a - logScale : Nat) : ℝ) / logScale :=
    div_pos hd_pos hS_pos
  have hlogx_ge : ((logNatLo a - logScale : Nat) : ℝ) / logScale ≤ Real.log x - 1 := by
    have h1 : (logNatLo a : ℝ) / logScale ≤ Real.log x :=
      hlog_lo.trans (Real.log_le_log (by exact_mod_cast (show 0 < a by omega)) hax)
    have hcast : ((logNatLo a - logScale : Nat) : ℝ) = (logNatLo a : ℝ) - logScale := by
      rw [Nat.cast_sub (by omega)]
    rw [hcast, sub_div, div_self hS_pos.ne']
    linarith
  have hlogx1_pos : 0 < Real.log x - 1 := lt_of_lt_of_le hL_sub_pos hlogx_ge
  have h1 : x / (Real.log x - 1) ≤ (b : ℝ) / (((logNatLo a - logScale : Nat) : ℝ) / logScale) := by
    calc x / (Real.log x - 1) ≤ (b : ℝ) / (Real.log x - 1) :=
          div_le_div_of_nonneg_right hxb hlogx1_pos.le
      _ ≤ (b : ℝ) / (((logNatLo a - logScale : Nat) : ℝ) / logScale) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg b) hL_sub_pos hlogx_ge
  have hchkR : (990 : ℝ) * b * logScale ≤
      1000 * (a.primeCounting : ℝ) * ((logNatLo a - logScale : Nat) : ℝ) := by exact_mod_cast hchk
  have h2 : 0.990 * ((b : ℝ) / (((logNatLo a - logScale : Nat) : ℝ) / logScale)) ≤ (a.primeCounting : ℝ) := by
    have heq : 0.990 * ((b : ℝ) / (((logNatLo a - logScale : Nat) : ℝ) / logScale)) =
        ((990 : ℝ) * b * logScale) / (1000 * ((logNatLo a - logScale : Nat) : ℝ)) := by
      field_simp; ring
    rw [heq, div_le_iff₀ (mul_pos (by norm_num) hd_pos)]
    linarith
  have hpi : (a.primeCounting : ℝ) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
    exact_mod_cast Nat.monotone_primeCounting (Nat.le_floor hax)
  linarith

private def checkF1Step (lo step cnt : Nat) : Bool :=
  (List.range cnt).all (fun i =>
    let a := lo + step * i
    let b := a + step
    let L := logNatLo a
    decide (9400 * b * logScale * (L + logScale) ≤ 10000 * exactPiSmall a * L * L))

private def checkF2Step (lo step cnt : Nat) : Bool :=
  (List.range cnt).all (fun i =>
    let a := lo + step * i
    let b := a + step
    let L := logNatLo a
    decide (logScale < L ∧ 990 * b * logScale ≤ 1000 * exactPiSmall a * (L - logScale)))

private def checkF1Packed (tbl base step cnt : Nat) : Bool :=
  (List.range cnt).all (fun j =>
    let a := base + step * j
    let b := a + step
    let L := logNatLo a
    decide (9400 * b * logScale * (L + logScale) ≤ 10000 * get20 tbl j * L * L))

private def checkF2Packed (tbl base step cnt : Nat) : Bool :=
  (List.range cnt).all (fun j =>
    let a := base + step * j
    let b := a + step
    let L := logNatLo a
    decide (logScale < L ∧ 990 * b * logScale ≤ 1000 * get20 tbl j * (L - logScale)))

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def f1SmallCheck : PLift (
    checkF1Step 101 1 155 = true ∧
    checkF1Step 256 4 192 = true ∧
    checkF1Step 1024 32 224 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def f1TiersCheck : PLift (
    checkF1Packed P1p 8192 64 128 = true ∧
    checkF1Packed P2p 16384 128 384 = true ∧
    checkF1Packed P3p 65536 512 512 = true ∧
    checkF1Packed P4p 327680 4096 432 = true ∧
    checkF1Packed P5p 2097152 16384 482 = true ∧
    9400 * 10000000 * logScale * (logNatLo 9994240 + logScale) ≤
      10000 * get20 P5p 482 * (logNatLo 9994240) ^ 2) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def f2SmallCheck : PLift (
    checkF2Step 2000 4 204 = true ∧
    checkF2Step 2816 16 144 = true ∧
    checkF2Step 5120 32 96 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def f2TiersCheck : PLift (
    checkF2Packed P1p 8192 64 128 = true ∧
    checkF2Packed P2p 16384 128 384 = true ∧
    checkF2Packed P3p 65536 512 512 = true ∧
    checkF2Packed P4p 327680 4096 432 = true ∧
    checkF2Packed P5p 2097152 16384 482 = true ∧
    logScale < logNatLo 9994240 ∧
    990 * 10000000 * logScale ≤ 1000 * get20 P5p 482 * (logNatLo 9994240 - logScale)) := ⟨by decide +kernel⟩

private lemma checkF1Step_at {lo step cnt j : Nat}
    (h : checkF1Step lo step cnt = true) (hj : j < cnt) :
    9400 * (lo + step * j + step) * logScale * (logNatLo (lo + step * j) + logScale) ≤
      10000 * exactPiSmall (lo + step * j) * (logNatLo (lo + step * j)) ^ 2 := by
  unfold checkF1Step at h
  rw [List.all_eq_true] at h
  have hres := decide_eq_true_eq.mp (h j (List.mem_range.mpr hj))
  simpa [sq, mul_assoc] using hres

private lemma checkF2Step_at {lo step cnt j : Nat}
    (h : checkF2Step lo step cnt = true) (hj : j < cnt) :
    logScale < logNatLo (lo + step * j) ∧
    990 * (lo + step * j + step) * logScale ≤
      1000 * exactPiSmall (lo + step * j) * (logNatLo (lo + step * j) - logScale) := by
  unfold checkF2Step at h
  rw [List.all_eq_true] at h
  exact decide_eq_true_eq.mp (h j (List.mem_range.mpr hj))

private lemma checkF1Packed_at {tbl base step cnt j : Nat}
    (h : checkF1Packed tbl base step cnt = true) (hj : j < cnt) :
    9400 * (base + step * j + step) * logScale * (logNatLo (base + step * j) + logScale) ≤
      10000 * get20 tbl j * (logNatLo (base + step * j)) ^ 2 := by
  unfold checkF1Packed at h
  rw [List.all_eq_true] at h
  have hres := decide_eq_true_eq.mp (h j (List.mem_range.mpr hj))
  simpa [sq, mul_assoc] using hres

private lemma checkF2Packed_at {tbl base step cnt j : Nat}
    (h : checkF2Packed tbl base step cnt = true) (hj : j < cnt) :
    logScale < logNatLo (base + step * j) ∧
    990 * (base + step * j + step) * logScale ≤ 1000 * get20 tbl j * (logNatLo (base + step * j) - logScale) := by
  unfold checkF2Packed at h
  rw [List.all_eq_true] at h
  exact decide_eq_true_eq.mp (h j (List.mem_range.mpr hj))

private lemma f1_floor_step {a b : Nat} {x : ℝ} (ha : 101 ≤ a) (hx0 : 0 ≤ x)
    (ham : a ≤ ⌊x⌋₊) (hmb : ⌊x⌋₊ + 1 ≤ b)
    (hchk : 9400 * b * logScale * (logNatLo a + logScale) ≤ 10000 * a.primeCounting * (logNatLo a) ^ 2) :
    0.9400 * (x / Real.log x + x / (Real.log x) ^ 2) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hax : (a : ℝ) ≤ x := le_trans (by exact_mod_cast ham) (Nat.floor_le hx0)
  have hxb : x ≤ (b : ℝ) := by
    have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hmb
    linarith
  exact f1_interval_sound ha hax hxb hchk

private lemma f2_floor_step {a b : Nat} {x : ℝ} (ha : 2000 ≤ a) (hx0 : 0 ≤ x)
    (ham : a ≤ ⌊x⌋₊) (hmb : ⌊x⌋₊ + 1 ≤ b)
    (hgt : logScale < logNatLo a)
    (hchk : 990 * b * logScale ≤ 1000 * a.primeCounting * (logNatLo a - logScale)) :
    0.990 * (x / (Real.log x - 1)) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  have hax : (a : ℝ) ≤ x := le_trans (by exact_mod_cast ham) (Nat.floor_le hx0)
  have hxb : x ≤ (b : ℝ) := by
    have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have h2 : (⌊x⌋₊ : ℝ) + 1 ≤ (b : ℝ) := by exact_mod_cast hmb
    linarith
  exact f2_interval_sound ha hax hxb hgt hchk

theorem pi_lower_101_10M {x : ℝ} (hx1 : 101 ≤ x) (hx2 : x ≤ (10 ^ 7 : ℝ)) :
    0.9400 * (x / Real.log x + x / (Real.log x) ^ 2) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  obtain ⟨hs0, hs1, hs2⟩ := f1SmallCheck.down
  obtain ⟨h1, h2, h3, h4, h5, htail⟩ := f1TiersCheck.down
  have hx0 : 0 ≤ x := by linarith
  set m := ⌊x⌋₊
  have hm101 : 101 ≤ m := Nat.le_floor (by norm_num; linarith)
  have hm10M : m ≤ 10000000 := Nat.floor_le_of_le (by norm_num; linarith)
  by_cases c00 : m < 256
  · let j := m - 101
    have hchk := checkF1Step_at hs0 (show j < 155 by dsimp [j]; omega)
    rw [exactPiSmall_correct (by dsimp [j]; omega)] at hchk
    exact f1_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk
  · by_cases c01 : m < 1024
    · let j := (m - 256) / 4
      have hchk := checkF1Step_at hs1 (show j < 192 by dsimp [j]; omega)
      rw [exactPiSmall_correct (by dsimp [j]; omega)] at hchk
      exact f1_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk
    · by_cases c02 : m < 8192
      · let j := (m - 1024) / 32
        have hchk := checkF1Step_at hs2 (show j < 224 by dsimp [j]; omega)
        rw [exactPiSmall_correct (by dsimp [j]; omega)] at hchk
        exact f1_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk
      · by_cases c1 : m < 16384
        · let j := (m - 8192) / 64
          have hchk := checkF1Packed_at h1 (show j < 128 by dsimp [j]; omega)
          rw [P1p_correct (by dsimp [j]; omega)] at hchk
          exact f1_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk
        · by_cases c2 : m < 65536
          · let j := (m - 16384) / 128
            have hchk := checkF1Packed_at h2 (show j < 384 by dsimp [j]; omega)
            rw [P2p_correct (by dsimp [j]; omega)] at hchk
            exact f1_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk
          · by_cases c3 : m < 327680
            · let j := (m - 65536) / 512
              have hchk := checkF1Packed_at h3 (show j < 512 by dsimp [j]; omega)
              rw [P3p_correct (by dsimp [j]; omega)] at hchk
              exact f1_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk
            · by_cases c4 : m < 2097152
              · let j := (m - 327680) / 4096
                have hchk := checkF1Packed_at h4 (show j < 432 by dsimp [j]; omega)
                rw [P4p_correct (by dsimp [j]; omega)] at hchk
                exact f1_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk
              · by_cases c5 : m < 9994240
                · let j := (m - 2097152) / 16384
                  have hchk := checkF1Packed_at h5 (show j < 482 by dsimp [j]; omega)
                  rw [P5p_correct (by dsimp [j]; omega)] at hchk
                  exact f1_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk
                · have hp := P5p_correct (j := 482) (by decide)
                  have hidx : 2097152 + 16384 * 482 = 9994240 := by decide
                  rw [hidx] at hp
                  rw [hp] at htail
                  have hax : (9994240 : ℝ) ≤ x :=
                    le_trans (by exact_mod_cast (show 9994240 ≤ m by omega)) (Nat.floor_le hx0)
                  exact f1_interval_sound (a := 9994240) (b := 10000000) (by decide) hax (by norm_num at hx2 ⊢; linarith) htail

theorem pi_lower_sieve_2000_10M {x : ℝ} (hx1 : 2000 ≤ x) (hx2 : x ≤ (10 ^ 7 : ℝ)) :
    0.990 * (x / (Real.log x - 1)) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  obtain ⟨hs0, hs1, hs2⟩ := f2SmallCheck.down
  obtain ⟨h1, h2, h3, h4, h5, hgt_t, htail⟩ := f2TiersCheck.down
  have hx0 : 0 ≤ x := by linarith
  set m := ⌊x⌋₊
  have hm2000 : 2000 ≤ m := Nat.le_floor (by norm_num; linarith)
  have hm10M : m ≤ 10000000 := Nat.floor_le_of_le (by norm_num; linarith)
  by_cases c00 : m < 2816
  · let j := (m - 2000) / 4
    have hchk := checkF2Step_at hs0 (show j < 204 by dsimp [j]; omega)
    rw [exactPiSmall_correct (by dsimp [j]; omega)] at hchk
    exact f2_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk.1 hchk.2
  · by_cases c01 : m < 5120
    · let j := (m - 2816) / 16
      have hchk := checkF2Step_at hs1 (show j < 144 by dsimp [j]; omega)
      rw [exactPiSmall_correct (by dsimp [j]; omega)] at hchk
      exact f2_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk.1 hchk.2
    · by_cases c02 : m < 8192
      · let j := (m - 5120) / 32
        have hchk := checkF2Step_at hs2 (show j < 96 by dsimp [j]; omega)
        rw [exactPiSmall_correct (by dsimp [j]; omega)] at hchk
        exact f2_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk.1 hchk.2
      · by_cases c1 : m < 16384
        · let j := (m - 8192) / 64
          have hchk := checkF2Packed_at h1 (show j < 128 by dsimp [j]; omega)
          rw [P1p_correct (by dsimp [j]; omega)] at hchk
          exact f2_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk.1 hchk.2
        · by_cases c2 : m < 65536
          · let j := (m - 16384) / 128
            have hchk := checkF2Packed_at h2 (show j < 384 by dsimp [j]; omega)
            rw [P2p_correct (by dsimp [j]; omega)] at hchk
            exact f2_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk.1 hchk.2
          · by_cases c3 : m < 327680
            · let j := (m - 65536) / 512
              have hchk := checkF2Packed_at h3 (show j < 512 by dsimp [j]; omega)
              rw [P3p_correct (by dsimp [j]; omega)] at hchk
              exact f2_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk.1 hchk.2
            · by_cases c4 : m < 2097152
              · let j := (m - 327680) / 4096
                have hchk := checkF2Packed_at h4 (show j < 432 by dsimp [j]; omega)
                rw [P4p_correct (by dsimp [j]; omega)] at hchk
                exact f2_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk.1 hchk.2
              · by_cases c5 : m < 9994240
                · let j := (m - 2097152) / 16384
                  have hchk := checkF2Packed_at h5 (show j < 482 by dsimp [j]; omega)
                  rw [P5p_correct (by dsimp [j]; omega)] at hchk
                  exact f2_floor_step (by dsimp [j]; omega) hx0 (by dsimp [j]; omega) (by dsimp [j]; omega) hchk.1 hchk.2
                · have hp := P5p_correct (j := 482) (by decide)
                  have hidx : 2097152 + 16384 * 482 = 9994240 := by decide
                  rw [hidx] at hp
                  rw [hp] at htail
                  have hax : (9994240 : ℝ) ≤ x :=
                    le_trans (by exact_mod_cast (show 9994240 ≤ m by omega)) (Nat.floor_le hx0)
                  exact f2_interval_sound (a := 9994240) (b := 10000000) (by decide) hax (by norm_num at hx2 ⊢; linarith) hgt_t htail

/- ### `θ(10^7)` integral pinning from our verified breakpoint table -/

def bpts10M : List (Nat × Nat) := [
  (2, 1), (3, 2), (5, 3), (10, 4), (20, 8), (40, 12), (80, 22), (160, 37),
  (320, 66), (640, 115), (1280, 207), (2560, 375), (4096, 564), (6144, 801), (8192, 1028), (9408, 1163),
  (10816, 1315), (12416, 1482), (14272, 1675), (16384, 1900), (18816, 2146), (21632, 2429), (24832, 2745), (28544, 3104),
  (32768, 3512), (37632, 3985), (43264, 4515), (49664, 5100), (57088, 5788), (65536, 6542), (75264, 7416), (86528, 8413),
  (99328, 9533), (114176, 10804), (131072, 12251), (150528, 13894), (173056, 15758), (198656, 17877), (228352, 20288), (262144, 23000),
  (301056, 26086), (344064, 29504), (393216, 33335), (450560, 37757), (516096, 42745), (589824, 48340), (675840, 54748), (774144, 62044),
  (888832, 70474), (1019904, 79968), (1171456, 90871), (1343488, 103109), (1544192, 117251), (1773568, 133210), (2035712, 151423), (2326528, 171292),
  (2670592, 194642), (3063808, 221051), (3522560, 251628), (4046848, 286283), (4653056, 325892), (5341184, 370564), (6127616, 421016), (7045120, 479543),
  (8093696, 545637), (9306112, 621559), (10000000, 664579)
]

private lemma bpts10M_pi : ∀ p ∈ bpts10M, p.2 = p.1.primeCounting := by
  intro p hp
  have hchk : bpts10M.all (fun q =>
      decide ((q.1 = 10000000 ∧ q.2 = 664579) ∨ (q.1 ≤ 14090240 ∧ piLoFast q.1 = q.2 ∧ piHiFast q.1 = q.2))) = true := by
    decide +kernel
  have h := decide_eq_true_eq.mp (List.all_eq_true.mp hchk p hp)
  rcases h with ⟨h1, h2⟩ | ⟨hle, hlo, hhi⟩
  · rw [h1, h2, pi_10M_eq]
  · have h1 := piLoFast_le hle
    have h2 := le_piHiFast hle
    omega

set_option maxHeartbeats 0 in
private lemma bpts10M_sums :
    bpts10M.head? = some (2, 1) ∧
    bpts10M.getLast? = some (10000000, 664579) ∧
    bpts10M.IsChain (fun p q => p.1 ≤ q.1) ∧
    piIntHiSum bpts10M ≤ 770000000000000 ∧
    650000000000000 ≤ piIntLoSum bpts10M := by
  decide +kernel

theorem theta_10M_integral_bounds :
    (36183 : ℝ) ≤ ∫ t in (2 : ℝ)..(10 ^ 7 : ℝ), θ t / (t * (Real.log t) ^ 2) ∧
    ∫ t in (2 : ℝ)..(10 ^ 7 : ℝ), θ t / (t * (Real.log t) ^ 2) ≤ 48222 := by
  obtain ⟨hhead, hlast, hch, hhi, hlo⟩ := bpts10M_sums
  refine theta_10M_integral_from_table bpts10M hhead hlast bpts10M_pi hch ?_ ?_
  · have hhiR : (piIntHiSum bpts10M : ℝ) ≤ 770000000000000 := by exact_mod_cast hhi
    norm_num [logScale]; linarith
  · have hloR : (650000000000000 : ℝ) ≤ (piIntLoSum bpts10M : ℝ) := by exact_mod_cast hlo
    norm_num [logScale]; linarith

end ColtonTables


/- ===================== Mod4_ColtonTail.lean ===================== -/

/-
Module 4: Disjoint refactorable families `G1` (`k ≤ 200,000`, 14 buckets) and `G4`
(`m ≤ 10,000`, 5 groups), continuous interval coverage `[14,090,240, 10^32]`,
constant-`U0` tail `[10^32, ∞)`, and the complete proof of Colton's conjecture.
-/

namespace ColtonTail

open Finset Real Chebyshev OeisA111291 ColtonChebyshev ColtonSieve ColtonSmall ColtonFactor ColtonPiAbel ColtonTables

/- ### Part 1: Combined `pi_lower_all` (`x ≥ 101`) and `pi_upper_10M_full` (`x ≥ 10^7`) -/

theorem pi_lower_all {x : ℝ} (hx : 101 ≤ x) :
    0.9400 * (x / Real.log x + x / (Real.log x) ^ 2) ≤ (Nat.primeCounting ⌊x⌋₊ : ℝ) := by
  by_cases h10M : x ≤ (10 ^ 7 : ℝ)
  · exact pi_lower_101_10M hx h10M
  · push Not at h10M
    exact pi_lower_10M (fun _ ht => theta_lower_10M ht) theta_10M_integral_bounds.1 h10M.le

theorem pi_lower_nat {m : Nat} (hm : 101 ≤ m) :
    0.9400 * ((m : ℝ) / Real.log m + (m : ℝ) / (Real.log m) ^ 2) ≤ (m.primeCounting : ℝ) := by
  have h := pi_lower_all (x := (m : ℝ)) (by exact_mod_cast hm)
  rwa [Nat.floor_natCast] at h

theorem pi_upper_10M_full {x : ℝ} (hx : (10 ^ 7 : ℝ) ≤ x) :
    (Nat.primeCounting ⌊x⌋₊ : ℝ) ≤
      1.0562 * (x / Real.log x + x / (Real.log x) ^ 2 + 3 * x / (Real.log x) ^ 3) :=
  pi_upper_10M (fun _ ht => theta_upper_10M ht) theta_10M_integral_bounds.2 hx

/- ### Part 2: Verified `G1` (14 buckets, `k ≤ 200,000`) and `G4` (5 groups, `m ≤ 10,000`) -/

def primesLe448 : List Nat := [
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61,
  67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151,
  157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251,
  257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359,
  367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443
]

private lemma primesLe448_prime : ∀ p ∈ primesLe448, p.Prime := by decide +kernel
private lemma primesLe448_nodup : primesLe448.Nodup := by decide +kernel
private lemma primesLe448_cov : ∀ p, p.Prime → p < 448 → p ∈ primesLe448 := by
  intro p hp hlt
  have : ∀ k : Fin 448, k.val.Prime → k.val ∈ primesLe448 := by decide +kernel
  exact this ⟨p, hlt⟩ hp

private lemma primesLe100_prime' : ∀ p ∈ primesLe100, p.Prime := by decide +kernel
private lemma primesLe100_nodup' : primesLe100.Nodup := by decide +kernel
private lemma primesLe100_cov' : ∀ p, p.Prime → p < 101 → p ∈ primesLe100 := by
  intro p hp hlt
  have : ∀ k : Fin 101, k.val.Prime → k.val ∈ primesLe100 := by decide +kernel
  exact this ⟨p, hlt⟩ hp

def harmScale : Nat := 1000000000000
def ratioScale : Nat := 1000000000

def g1List0 : List Nat := [
  8
]

def g1List1 : List Nat := [
  12
]

def g1List2 : List Nat := [
  36
]

def g1List3 : List Nat := [
  72
]

def g1List4 : List Nat := [
  80, 96, 128
]

def g1List5 : List Nat := [
  180, 240, 252, 288
]

def g1List6 : List Nat := [
  384, 396, 448, 468, 480, 560, 612, 640, 672, 684, 720
]

def g1List7 : List Nat := [
  828, 864, 880, 896, 972, 1040, 1044, 1056, 1116, 1152, 1200, 1248, 1332, 1344, 1360, 1408, 1440, 1476,
  1520, 1548, 1620, 1632, 1664, 1680, 1692, 1800
]

def g1List8 : List Nat := [
  1824, 1840, 1908, 1920, 2000, 2016, 2124, 2160, 2176, 2196, 2208, 2240, 2320, 2412, 2432, 2480, 2556, 2560,
  2628, 2640, 2688, 2784, 2844, 2944, 2960, 2976, 2988, 3120, 3168, 3204, 3280, 3360, 3440, 3456, 3492, 3528,
  3552, 3600, 3636, 3708, 3712, 3744, 3760, 3852, 3924, 3936, 3968
]

def g1List9 : List Nat := [
  4032, 4068, 4080, 4128, 4224, 4240, 4320, 4480, 4512, 4560, 4572, 4716, 4720, 4736, 4880, 4896, 4928, 4932,
  4992, 5000, 5004, 5040, 5088, 5248, 5280, 5360, 5364, 5436, 5472, 5504, 5520, 5652, 5664, 5680, 5760, 5824,
  5840, 5856, 5868, 6000, 6012, 6016, 6048, 6144, 6160, 6228, 6240, 6320, 6432, 6444, 6516, 6528, 6624, 6640,
  6720, 6784, 6816, 6876, 6912, 6948, 6960, 7008, 7040, 7092, 7120, 7164, 7280, 7296, 7392, 7440, 7500, 7552,
  7584, 7596, 7616, 7680, 7760, 7776, 7808, 7920, 7968, 8028, 8064, 8080, 8100, 8160, 8172, 8240, 8244, 8320,
  8352, 8388, 8400, 8512, 8544, 8560, 8576, 8604, 8676, 8712, 8720, 8736, 8832, 8880, 8928
]

def g1List10 : List Nat := [
  9036, 9040, 9088, 9120, 9252, 9312, 9344, 9360, 9408, 9468, 9504, 9520, 9600, 9684, 9696, 9756, 9840, 9856,
  9888, 9972, 10000, 10080, 10112, 10116, 10160, 10188, 10272, 10304, 10320, 10464, 10480, 10548, 10624, 10640, 10656, 10800,
  10848, 10880, 10960, 11040, 11052, 11120, 11136, 11196, 11232, 11264, 11268, 11280, 11392, 11412, 11424, 11440, 11648, 11760,
  11808, 11904, 11916, 11920, 12000, 12080, 12096, 12132, 12160, 12168, 12192, 12240, 12384, 12416, 12492, 12560, 12564, 12576,
  12672, 12708, 12720, 12768, 12880, 12924, 12928, 12960, 12992, 13040, 13152, 13184, 13200, 13212, 13344, 13360, 13428, 13440,
  13536, 13644, 13680, 13696, 13728, 13788, 13840, 13888, 13920, 13952, 14000, 14004, 14160, 14208, 14292, 14304, 14320, 14436,
  14464, 14480, 14496, 14640, 14688, 14720, 14724, 14784, 14880, 14960, 14976, 15072, 15084, 15156, 15232, 15264, 15280, 15440,
  15456, 15516, 15588, 15600, 15648, 15744, 15760, 15804, 15840, 15920, 15948, 16000, 16032, 16080, 16164, 16200, 16240, 16256,
  16416, 16452, 16512, 16560, 16576, 16596, 16608, 16668, 16720, 16768, 16812, 16880, 16992, 17024, 17040, 17184, 17244, 17280,
  17360, 17376, 17472, 17520, 17532, 17536, 17568, 17676, 17680, 17760, 17792, 17840, 17920, 17952, 17964, 18000, 18048, 18108,
  18160, 18304, 18320, 18324, 18336, 18368, 18432, 18528, 18560, 18640, 18720, 18756, 18816, 18828, 18912, 18960, 19072, 19104,
  19120, 19264, 19280, 19296, 19328, 19440, 19476, 19488, 19584, 19680, 19692, 19760, 19840, 19872, 19920
]

def g1List11 : List Nat := [
  20052, 20064, 20080, 20096, 20160, 20240, 20256, 20268, 20352, 20400, 20412, 20448, 20484, 20556, 20560, 20608, 20640, 20720,
  20772, 20808, 20832, 20864, 20880, 21024, 21040, 21056, 21120, 21132, 21216, 21348, 21360, 21376, 21408, 21520, 21564, 21600,
  21636, 21680, 21792, 21852, 21888, 21952, 21984, 22000, 22068, 22144, 22160, 22176, 22212, 22284, 22320, 22368, 22480, 22500,
  22560, 22640, 22656, 22716, 22752, 22800, 22848, 22912, 22944, 22960, 23040, 23076, 23136, 23148, 23168, 23280, 23292, 23424,
  23440, 23508, 23680, 23712, 23724, 23744, 23796, 23904, 23920, 23936, 24080, 24096, 24192, 24228, 24240, 24288, 24300, 24372,
  24448, 24480, 24560, 24588, 24640, 24672, 24704, 24720, 24864, 24876, 24880, 24960, 25040, 25056, 25200, 25216, 25236, 25248,
  25360, 25440, 25472, 25520, 25524, 25536, 25632, 25680, 25728, 25824, 25840, 25884, 25984, 25992, 26000, 26016, 26160, 26172,
  26208, 26240, 26244, 26320, 26388, 26432, 26480, 26496, 26592, 26604, 26640, 26748, 26752, 26784, 26960, 26976, 27008, 27036,
  27120, 27168, 27252, 27264, 27280, 27328, 27360, 27396, 27440, 27520, 27552, 27600, 27684, 27760, 27776, 27828, 27920, 27936,
  28032, 28128, 28160, 28224, 28240, 28288, 28320, 28332, 28544, 28692, 28704, 28720, 28800, 28896, 29040, 29056, 29088, 29120,
  29124, 29196, 29280, 29312, 29360, 29472, 29520, 29556, 29568, 29628, 29664, 29680, 29772, 29824, 29840, 29844, 29856, 30000,
  30016, 30048, 30080, 30160, 30204, 30320, 30336, 30432, 30480, 30592, 30624, 30640, 30708, 30720, 30816, 30848, 30852, 30912,
  30924, 30960, 31008, 31068, 31104, 31120, 31280, 31392, 31440, 31572, 31584, 31616, 31716, 31760, 31776, 31788, 31808, 31872,
  31932, 31968, 32080, 32128, 32160, 32240, 32352, 32384, 32400, 32544, 32560, 32640, 32652, 32704, 32720, 32736, 32768, 32796,
  32880, 32896, 32928, 33040, 33084, 33120, 33152, 33280, 33312, 33360, 33408, 33444, 33504, 33520, 33600, 33664, 33680, 33732,
  33792, 33840, 33876, 33888, 33920, 34000, 34080, 34092, 34160, 34176, 34272, 34308, 34432, 34464, 34480, 34560, 34640, 34688,
  34800, 34812, 34944, 34956, 34960, 35040, 35120, 35172, 35232, 35280, 35388, 35392, 35424, 35440, 35456, 35616, 35676, 35712,
  35760, 35808, 35892, 35920, 35968, 36000, 36080, 36192, 36224, 36240, 36324, 36384, 36468, 36480, 36560, 36576, 36684, 36736,
  36756, 36768, 36880, 37040, 37116, 37152, 37184, 37188, 37200, 37248, 37344, 37360, 37404, 37504, 37520, 37536, 37680, 37728,
  37760, 37764, 37836, 37840, 37920, 38000, 38016, 38080, 38088, 38112, 38160, 38196, 38268, 38272, 38304, 38320, 38400, 38480,
  38484, 38496, 38528, 38688, 38784, 38880, 38960, 38976, 39040, 39072, 39120, 39132, 39264, 39276, 39280, 39296, 39348, 39440,
  39456, 39492, 39552, 39600, 39648, 39708, 39760, 39808, 39840, 39872, 39920, 39924, 40032, 40064, 40080, 40212, 40224, 40240,
  40320, 40416, 40428, 40560, 40576, 40608, 40644, 40720, 40832, 40880, 40992, 41088, 41184, 41344, 41360, 41376, 41436, 41508,
  41520, 41568, 41664, 41680, 41760, 41840, 41856, 41868, 41952, 42112, 42144, 42156, 42160, 42336, 42368, 42480, 42516, 42528,
  42560, 42624, 42640, 42720, 42732, 42880, 42912, 42948, 42960, 43008, 43104, 43136, 43236, 43280, 43296, 43392, 43440, 43456,
  43488, 43520, 43648, 43668, 43760, 43812, 43872, 43904, 43920, 44028, 44080, 44160, 44240, 44244, 44256, 44316, 44352, 44400,
  44416, 44448, 44532, 44560, 44640, 44672, 44720, 44832, 44928, 44964, 45000
]

def g1List12 : List Nat := [
  45024, 45040, 45184, 45216, 45248, 45324, 45408, 45440, 45520, 45680, 45696, 45792, 45840, 45952, 45972, 45984, 46000, 46044,
  46144, 46160, 46176, 46188, 46320, 46368, 46404, 46464, 46476, 46480, 46560, 46640, 46692, 46720, 46752, 46800, 46836, 46908,
  46944, 46960, 46976, 47040, 47052, 47120, 47136, 47232, 47280, 47328, 47440, 47484, 47488, 47556, 47628, 47712, 47744, 47760,
  47772, 47904, 47920, 47936, 48000, 48080, 48096, 48240, 48256, 48288, 48384, 48480, 48512, 48560, 48640, 48768, 48832, 48864,
  48880, 48996, 49024, 49040, 49056, 49200, 49212, 49280, 49360, 49428, 49440, 49520, 49536, 49632, 49716, 49728, 49792, 49824,
  49840, 50016, 50048, 50208, 50304, 50320, 50364, 50480, 50560, 50592, 50624, 50640, 50724, 50816, 50976, 51072, 51120, 51168,
  51228, 51280, 51328, 51360, 51372, 51440, 51444, 51520, 51552, 51584, 51588, 51600, 51760, 51804, 51840, 51920, 51936, 52092,
  52096, 52128, 52236, 52240, 52308, 52320, 52352, 52416, 52488, 52512, 52524, 52560, 52608, 52704, 52720, 52864, 52880, 52896,
  52956, 53088, 53120, 53248, 53280, 53316, 53360, 53376, 53388, 53472, 53520, 53532, 53604, 53632, 53664, 53680, 53748, 53760,
  53840, 53856, 53888, 53964, 54048, 54144, 54160, 54240, 54320, 54396, 54432, 54480, 54624, 54640, 54656, 54816, 54828, 54912,
  54960, 55008, 55104, 55116, 55120, 55168, 55280, 55296, 55392, 55424, 55440, 55548, 55584, 55680, 55760, 55764, 55776, 55908,
  55920, 55936, 55968, 56000, 56080, 56124, 56192, 56240, 56320, 56352, 56400, 56412, 56448, 56544, 56556, 56560, 56700, 56704,
  56720, 56736, 56844, 56880, 56896, 56928, 56960, 56988, 57040, 57216, 57312, 57344, 57360, 57472, 57492, 57504, 57520, 57636,
  57680, 57696, 57728, 57792, 57840, 57852, 57888, 57924, 57984, 58000, 58068, 58160, 58240, 58272, 58284, 58356, 58464, 58480,
  58496, 58572, 58640, 58656, 58688, 58752, 58848, 58880, 58932, 58960, 59008, 59040, 59120, 59232, 59264, 59424, 59440, 59520,
  59652, 59760, 59776, 59808, 59868, 59920, 60000, 60012, 60032, 60080, 60084, 60192, 60240, 60288, 60384, 60480, 60544, 60552,
  60560, 60576, 60768, 60880, 60948, 60960, 61040, 61056, 61092, 61164, 61200, 61312, 61344, 61360, 61376, 61520, 61524, 61536,
  61568, 61680, 61728, 61824, 61840, 61920, 61956, 62000, 62028, 62080, 62112, 62208, 62272, 62304, 62320, 62336, 62388, 62480,
  62496, 62592, 62676, 62688, 62848, 62880, 62892, 62960, 63072, 63104, 63108, 63120, 63168, 63264, 63280, 63324, 63360, 63440,
  63456, 63600, 63616, 63648, 63760, 63872, 63920, 63972, 64000, 64032, 64064, 64080, 64128, 64188, 64224, 64240, 64332, 64384,
  64404, 64416, 64560, 64608, 64640, 64720, 64800, 64836, 64880, 64896, 64960, 64992, 65040, 65152, 65184, 65196, 65360, 65376,
  65408, 65520, 65568, 65628, 65664, 65680, 65760, 65840, 65856, 65916, 65920, 65952, 66144, 66160, 66176, 66320, 66336, 66432,
  66480, 66492, 66688, 66720, 66752, 66912, 66944, 66996, 67104, 67120, 67200, 67212, 67296, 67356, 67428, 67440, 67456, 67488,
  67572, 67584, 67644, 67648, 67680, 67872, 67920, 67968, 68004, 68064, 68080, 68224, 68240, 68256, 68400, 68436, 68448, 68480,
  68544, 68560, 68652, 68720, 68736, 68832, 68868, 69024, 69040, 69120, 69192, 69216, 69248, 69360, 69408, 69440, 69504, 69516,
  69520, 69588, 69680, 69760, 69792, 69840, 69984, 70000, 70016, 70160, 70164, 70176, 70236, 70272, 70320, 70336, 70368, 70480,
  70528, 70640, 70752, 70784, 70800, 70944, 70960, 71028, 71040, 71120, 71136, 71232, 71244, 71296, 71328, 71440, 71520, 71532,
  71552, 71712, 71748, 71808, 71892, 71904, 71920, 71964, 72064, 72080, 72096, 72108, 72288, 72320, 72396, 72480, 72560, 72612,
  72672, 72720, 72832, 72864, 72880, 72972, 73024, 73040, 73044, 73056, 73088, 73200, 73248, 73344, 73360, 73404, 73520, 73632,
  73680, 73824, 73840, 73856, 73908, 73920, 74000, 74016, 74112, 74160, 74208, 74240, 74268, 74320, 74368, 74484, 74592, 74624,
  74640, 74784, 74816, 74880, 74916, 74960, 74976, 74988, 75120, 75132, 75136, 75204, 75280, 75360, 75392, 75440, 75552, 75564,
  75600, 75648, 75744, 75760, 75904, 75920, 75936, 75996, 76032, 76068, 76080, 76128, 76160, 76240, 76320, 76416, 76512, 76608,
  76644, 76672, 76704, 76716, 76720, 76896, 76928, 76932, 77040, 77076, 77088, 77148, 77184, 77360, 77472, 77504, 77508, 77664,
  77680, 77696, 77796, 77840, 77856, 77952, 78048, 78160, 78208, 78240, 78320, 78432, 78444, 78464, 78480, 78640, 78720, 78816,
  78848, 78976, 79008, 79120, 79232, 79280, 79296, 79308, 79360, 79380, 79392, 79440, 79452, 79488, 79584, 79668, 79744, 79760,
  79776, 79872, 79956, 80000, 80160, 80192, 80240, 80256, 80400, 80512, 80532, 80544, 80560, 80604, 80720, 80748, 80768, 80880,
  80928, 81024, 81036, 81040, 81088, 81280, 81360, 81504, 81520, 81612, 81680, 81684, 81696, 81792, 81828, 81888, 81984, 82000,
  82048, 82116, 82160, 82272, 82304, 82332, 82464, 82480, 82548, 82560, 82640, 82656, 82692, 82800, 82816, 82848, 82880, 82960,
  83040, 83072, 83120, 83124, 83196, 83280, 83328, 83424, 83440, 83584, 83616, 83760, 83776, 83808, 83840, 83920, 83988, 84080,
  84096, 84192, 84204, 84276, 84352, 84384, 84480, 84492, 84560, 84576, 84608, 84636, 84672, 84720, 84768, 84852, 84864, 84880,
  84960, 85040, 85120, 85152, 85200, 85344, 85356, 85360, 85376, 85520, 85536, 85568, 85572, 85632, 85680, 85716, 85728, 85788,
  85840, 85888, 85920, 86000, 86004, 86112, 86144, 86148, 86160, 86304, 86320, 86364, 86400, 86464, 86480, 86496, 86640, 86656,
  86688, 86796, 86880, 86912, 86960, 87012, 87072, 87120, 87168, 87228, 87264, 87280, 87360, 87424, 87440, 87456, 87600, 87648,
  87680, 87732, 87760, 87840, 87876, 87920, 87936, 88032, 88080, 88092, 88192, 88224, 88240, 88256, 88416, 88448, 88524, 88608,
  88704, 88720, 88812, 88880, 88960, 88992, 89028, 89100, 89152, 89172, 89184, 89216, 89360, 89472, 89520, 89568, 89680, 89728,
  89840, 89856, 89952, 89984, 90000, 90048, 90108, 90144, 90240, 90320, 90336, 90496, 90528, 90640, 90720, 90752, 90756, 90912,
  90960, 91008, 91104, 91116, 91120, 91264, 91280, 91296, 91404, 91440, 91488, 91520, 91548, 91680, 91760, 91764, 91776, 91836,
  91840, 91872, 91920, 92032, 92052, 92064, 92080, 92160, 92240, 92288, 92400, 92448, 92544, 92560, 92640, 92720, 92736, 92832,
  92844, 93024, 93040, 93056, 93216, 93276, 93348, 93360, 93408, 93520, 93568, 93632, 93680, 93792, 93824, 93924, 93984, 94000,
  94080, 94160, 94176, 94212, 94320, 94336, 94356, 94368, 94480, 94528, 94560, 94592, 94720, 94752, 94788, 94800, 94848, 94944,
  94960, 95104, 95120, 95136, 95280, 95292, 95328, 95360, 95424, 95440, 95520, 95616, 95652, 95712, 95724, 95760, 95868, 95872,
  95920, 96080, 96128, 96156, 96240, 96288, 96320, 96372, 96384, 96480, 96560, 96588, 96640, 96672, 96732, 96804, 96864, 96880,
  96896, 96948, 97040, 97056, 97152, 97164, 97200, 97248, 97360, 97408, 97452, 97520, 97596, 97632, 97664, 97668, 97824, 97840,
  97884, 97920, 98016, 98112, 98160, 98176, 98208, 98244, 98304, 98316, 98320, 98432, 98480, 98568, 98592, 98640, 98676, 98688,
  98784, 98944, 98960, 98964, 98976, 99008, 99108, 99168, 99280, 99440, 99456, 99552, 99600, 99612, 99712, 99744, 99760, 99840,
  99904, 99920, 99936, 99968, 99972
]

def g1List13 : List Nat := [
  100080, 100128, 100224, 100240, 100404, 100476, 100480, 100512, 100560, 100692, 100704, 100720, 100736, 100800, 100836, 100880, 100896, 100908,
  100992, 101040, 101088, 101248, 101280, 101360, 101376, 101472, 101484, 101504, 101664, 101680, 101696, 101760, 101840, 101856, 101988, 102016,
  102048, 102132, 102160, 102240, 102272, 102320, 102348, 102432, 102528, 102592, 102624, 102636, 102640, 102784, 102852, 102960, 102996, 103008,
  103040, 103120, 103280, 103296, 103392, 103440, 103488, 103552, 103584, 103644, 103680, 103760, 103776, 103808, 103920, 103932, 104064, 104080,
  104240, 104292, 104320, 104352, 104384, 104400, 104448, 104508, 104544, 104560, 104576, 104724, 104736, 104832, 104928, 104960, 105012, 105040,
  105088, 105120, 105280, 105300, 105312, 105344, 105360, 105372, 105504, 105520, 105600, 105680, 105696, 105804, 105840, 105856, 105888, 106000,
  106112, 106160, 106176, 106308, 106320, 106368, 106452, 106464, 106480, 106640, 106656, 106668, 106800, 106848, 106880, 106884, 106956, 106960,
  107040, 107072, 107120, 107136, 107232, 107280, 107392, 107424, 107440, 107616, 107760, 107808, 107904, 107920, 107964, 107968, 108036, 108080,
  108384, 108396, 108560, 108576, 108672, 108684, 108720, 108768, 108828, 108864, 108880, 108928, 108960, 109040, 109152, 109184, 109200, 109332,
  109344, 109360, 109440, 109476, 109536, 109680, 109696, 109728, 109760, 109764, 109840, 109920, 109952, 110000, 110080, 110112, 110196, 110208,
  110304, 110320, 110412, 110464, 110480, 110496, 110640, 110656, 110688, 110720, 110844, 110880, 110960, 110976, 110988, 111072, 111120, 111204,
  111232, 111264, 111280, 111440, 111488, 111552, 111600, 111648, 111744, 111760, 111840, 111920, 111924, 112000, 112032, 112080, 112224, 112240,
  112256, 112284, 112356, 112416, 112448, 112512, 112608, 112720, 112768, 112880, 112932, 112992, 113024, 113040, 113184, 113280, 113344, 113360,
  113376, 113536, 113760, 113792, 113840, 113868, 113952, 114012, 114084, 114144, 114160, 114240, 114304, 114320, 114336, 114516, 114528, 114560,
  114640, 114720, 114732, 114816, 114876, 114960, 115072, 115104, 115120, 115136, 115200, 115280, 115296, 115308, 115328, 115488, 115524, 115584,
  115680, 115760, 115812, 115840, 115872, 115920, 115956, 116064, 116080, 116096, 116240, 116244, 116256, 116352, 116400, 116448, 116560, 116608,
  116720, 116736, 116832, 116864, 116880, 116928, 117024, 117036, 117108, 117120, 117216, 117252, 117324, 117360, 117376, 117408, 117504, 117520,
  117612, 117632, 117680, 117756, 117792, 117824, 117840, 117888, 117984, 118000, 118144, 118160, 118176, 118368, 118480, 118640, 118656, 118720,
  118752, 118764, 118800, 118836, 118912, 118944, 118960, 119052, 119120, 119136, 119268, 119328, 119424, 119440, 119484, 119520, 119616, 119628,
  119680, 119712, 119760, 119844, 119904, 119916, 119920, 119936, 120080, 120096, 120192, 120240, 120288, 120320, 120348, 120448, 120480, 120492,
  120512, 120560, 120672, 120704, 120720, 120864, 120880, 120924, 120996, 121032, 121040, 121056, 121200, 121216, 121248, 121356, 121360, 121408,
  121428, 121472, 121632, 121680, 121728, 121840, 121984, 122000, 122004, 122016, 122076, 122160, 122208, 122240, 122304, 122320, 122480, 122496,
  122592, 122652, 122752, 122784, 122868, 122960, 122976, 123168, 123264, 123280, 123360, 123440, 123520, 123588, 123600, 123744, 123776, 123920,
  123936, 124032, 124096, 124128, 124164, 124240, 124288, 124452, 124512, 124544, 124560, 124596, 124668, 124704, 124720, 124800, 124812, 124880,
  124884, 124896, 124992, 125040, 125056, 125088, 125312, 125360, 125472, 125520, 125568, 125676, 125680, 125824, 125856, 125888, 125964, 126000,
  126048, 126080, 126160, 126240, 126320, 126336, 126396, 126432, 126592, 126612, 126624, 126640, 126784, 126816, 126848, 126960, 126972, 127044,
  127104, 127120, 127188, 127280, 127360, 127392, 127404, 127476, 127584, 127616, 127680, 127692, 127760, 127776, 127872, 127968, 128052, 128080,
  128124, 128128, 128160, 128240, 128352, 128384, 128400, 128544, 128556, 128560, 128640, 128720, 128736, 128880, 128896, 128916, 128928, 128988,
  129024, 129040, 129120, 129152, 129312, 129348, 129360, 129408, 129504, 129520, 129664, 129680, 129696, 129840, 129852, 129888, 129920, 130000,
  130068, 130080, 130160, 130176, 130212, 130272, 130320, 130368, 130428, 130432, 130464, 130480, 130560, 130640, 130656, 130688, 130716, 130800,
  130848, 130932, 130944, 130960, 131040, 131120, 131148, 131220, 131232, 131264, 131280, 131328, 131440, 131456, 131616, 131712, 131724, 131808,
  131920, 131968, 132080, 132156, 132160, 132192, 132224, 132228, 132372, 132384, 132480, 132560, 132576, 132736, 132768, 132876, 132880, 132960,
  132992, 133040, 133056, 133092, 133128, 133152, 133200, 133236, 133248, 133344, 133360, 133504, 133520, 133524, 133536, 133680, 133728, 133760,
  133840, 133884, 133952, 134000, 134016, 134112, 134172, 134272, 134304, 134320, 134388, 134496, 134528, 134604, 134640, 134688, 134880, 134960,
  135040, 135072, 135120, 135264, 135280, 135296, 135396, 135440, 135456, 135552, 135600, 135612, 135648, 135680, 135684, 135744, 135760, 135808,
  135840, 135920, 136032, 136044, 136064, 136080, 136224, 136240, 136320, 136548, 136560, 136576, 136608, 136640, 136692, 136720, 136832, 136880,
  136908, 136992, 137040, 137088, 137184, 137344, 137360, 137520, 137536, 137556, 137568, 137628, 137680, 137700, 137840, 137856, 137952, 137988,
  138112, 138144, 138160, 138336, 138368, 138432, 138480, 138492, 138528, 138624, 138636, 138640, 138708, 138880, 138912, 138960, 139068, 139120,
  139136, 139280, 139296, 139328, 139392, 139488, 139572, 139648, 139680, 139716, 139760, 139872, 139904, 140004, 140064, 140080, 140160, 140224,
  140240, 140256, 140400, 140416, 140560, 140640, 140652, 140672, 140720, 140796, 140832, 140880, 140928, 141012, 141024, 141040, 141084, 141120,
  141184, 141216, 141228, 141312, 141408, 141440, 141444, 141516, 141520, 141696, 141792, 141840, 141948, 141952, 141984, 142000, 142016, 142092,
  142160, 142176, 142208, 142320, 142368, 142464, 142480, 142560, 142640, 142720, 142752, 142800, 142812, 142884, 142912, 142944, 142960, 142976,
  143120, 143136, 143232, 143280, 143328, 143440, 143488, 143604, 143712, 143744, 143760, 143808, 143904, 143920, 144000, 144036, 144080, 144096,
  144108, 144240, 144252, 144288, 144468, 144512, 144560, 144672, 144684, 144704, 144756, 144768, 144864, 144880, 144972, 145024, 145056, 145248,
  145280, 145360, 145440, 145520, 145536, 145632, 145680, 145764, 145792, 145836, 145840, 145920, 146000, 146016, 146048, 146052, 146160, 146208,
  146304, 146320, 146432, 146480, 146496, 146560, 146592, 146628, 146784, 146816, 146844, 146960, 146976, 147072, 147120, 147168, 147276, 147280,
  147328, 147348, 147360, 147440, 147552, 147564, 147584, 147600, 147744, 147760, 147936, 147996, 148080, 148096, 148128, 148240, 148288, 148320,
  148352, 148560, 148572, 148608, 148644, 148704, 148788, 148864, 148880, 148896, 149004, 149088, 149120, 149184, 149280, 149360, 149376, 149472,
  149508, 149632, 149652, 149664, 149680, 149724, 149840, 149856, 149888, 150000, 150048, 150080, 150144, 150160, 150240, 150320, 150372, 150432,
  150480, 150624, 150640, 150656, 150816, 150912, 150976, 151040, 151120, 151168, 151200, 151236, 151280, 151392, 151440, 151584, 151596, 151680,
  151760, 151776, 151812, 151872, 151884, 151920, 151936, 151968, 152080, 152160, 152192, 152240, 152244, 152316, 152400, 152448, 152544, 152560,
  152676, 152704, 152720, 152736, 152748, 152768, 152880, 152960, 153040, 153108, 153216, 153312, 153324, 153396, 153472, 153504, 153520, 153680,
  153696, 153728, 153756, 153828, 153840, 153888, 153900, 153984, 154080, 154160, 154188, 154240, 154272, 154320, 154404, 154464, 154480, 154496,
  154560, 154640, 154656, 154692, 154752, 154800, 154848, 154960, 155008, 155120, 155264, 155280, 155424, 155440, 155456, 155520, 155616, 155772,
  155776, 155808, 155920, 156032, 156080, 156132, 156160, 156192, 156204, 156240, 156288, 156352, 156384, 156544, 156560, 156564, 156576, 156720,
  156768, 156852, 156880, 156960, 157040, 157056, 157068, 157152, 157200, 157248, 157312, 157344, 157360, 157428, 157500, 157520, 157536, 157568,
  157728, 157824, 157840, 158000, 158076, 158080, 158144, 158160, 158292, 158304, 158320, 158336, 158480, 158496, 158592, 158640, 158688, 158724,
  158848, 158880, 158960, 158976, 159040, 159048, 159072, 159104, 159120, 159156, 159228, 159264, 159280, 159360, 159440, 159456, 159600, 159616,
  159648, 159744, 159760, 159872, 159876, 159920, 159936, 160032, 160092, 160128, 160224, 160236, 160240, 160384, 160416, 160452, 160560, 160608,
  160640, 160668, 160832, 160880, 160896, 160992, 161152, 161184, 161280, 161316, 161360, 161388, 161408, 161520, 161664, 161680, 161748, 161760,
  161920, 161952, 162000, 162144, 162160, 162176, 162252, 162320, 162336, 162432, 162468, 162480, 162528, 162612, 162624, 162640, 162684, 162688,
  162720, 162828, 162912, 162944, 163104, 163120, 163200, 163280, 163296, 163440, 163456, 163488, 163520, 163692, 163712, 163760, 163764, 163840,
  163872, 163920, 163968, 164064, 164080, 164196, 164224, 164240, 164256, 164268, 164400, 164412, 164416, 164448, 164480, 164720, 164736, 164832,
  164880, 164988, 164992, 165024, 165040, 165216, 165248, 165276, 165312, 165408, 165492, 165504, 165520, 165680, 165708, 165760, 165792, 165840,
  166000, 166016, 166160, 166176, 166272, 166356, 166368, 166480, 166528, 166560, 166640, 166752, 166784, 166800, 166932, 166944, 166960, 167004,
  167040, 167104, 167120, 167136, 167148, 167296, 167328, 167364, 167436, 167520, 167552, 167652, 167712, 167760, 167808, 167868, 167904, 167920,
  168000, 168064, 168080, 168096, 168228, 168240, 168288, 168320, 168444, 168480, 168576, 168672, 168832, 168864, 168876, 168880, 168896, 168960,
  169040, 169056, 169088, 169200, 169248, 169308, 169344, 169360, 169440, 169520, 169632, 169792, 169824, 169840, 169856, 169956, 170000, 170028,
  170112, 170160, 170208, 170244, 170320, 170368, 170388, 170480, 170592, 170624, 170688, 170784, 170880, 170960, 170976, 171036, 171136, 171168,
  171280, 171324, 171360, 171392, 171440, 171520, 171552, 171584, 171600, 171648, 171744, 171760, 171904, 171920, 171936, 172032, 172080, 172128,
  172160, 172188, 172240, 172320, 172332, 172404, 172416, 172512, 172548, 172560, 172672, 172704, 172720, 172764, 172800, 172836, 172880, 172896,
  172928, 173088, 173184, 173268, 173360, 173376, 173412, 173440, 173472, 173520, 173680, 173696, 173840, 173856, 173916, 173952, 174160, 174208,
  174272, 174320, 174432, 174464, 174480, 174624, 174640, 174816, 174976, 174996, 175008, 175120, 175168, 175280, 175356, 175488, 175572, 175584,
  175744, 175760, 175776, 175920, 175968, 176000, 176004, 176064, 176080, 176160, 176240, 176352, 176508, 176512, 176544, 176560, 176640, 176724,
  176736, 176768, 176928, 176960, 177024, 177040, 177084, 177280, 177312, 177360, 177516, 177520, 177536, 177588, 177680, 177696, 177732, 177792,
  177840, 177856, 177888, 177948, 178000, 178048, 178160, 178176, 178236, 178272, 178304, 178320, 178452, 178480, 178560, 178656, 178752, 178800,
  178812, 178816, 178848, 178884, 178960, 179028, 179040, 179072, 179120, 179232, 179328, 179424, 179440, 179532, 179584, 179616, 179648, 179748,
  179808, 179840, 179920, 179964, 180000, 180080, 180096, 180108, 180192, 180240, 180324, 180352, 180384, 180396, 180544, 180560, 180608, 180720,
  180756, 180768, 180828, 180864, 181040, 181120, 181152, 181200, 181344, 181360, 181376, 181404, 181440, 181520, 181536, 181632, 181680, 181728,
  181760, 181836, 181840, 181920, 182112, 182124, 182144, 182160, 182304, 182320, 182336, 182400, 182480, 182496, 182640, 182656, 182688, 182772,
  182880, 182912, 182916, 182960, 183072, 183132, 183168, 183232, 183264, 183280, 183424, 183440, 183564, 183600, 183636, 183648, 183680, 183708,
  183760, 183840, 183852, 183936, 184068, 184128, 184192, 184224, 184284, 184416, 184448, 184560, 184608, 184704, 184720, 184880, 184992, 185040,
  185184, 185216, 185292, 185360, 185376, 185472, 185508, 185520, 185568, 185680, 185728, 185840, 185920, 185952, 185984, 186012, 186144, 186156,
  186160, 186240, 186300, 186320, 186336, 186444, 186480, 186496, 186528, 186640, 186720, 186752, 186804, 186816, 186880, 186912, 187008, 187092,
  187104, 187120, 187264, 187280, 187296, 187520, 187524, 187712, 187760, 187776, 187872, 188032, 188064, 188080, 188172, 188240, 188256, 188288,
  188316, 188388, 188400, 188448, 188532, 188544, 188560, 188608, 188640, 188720, 188832, 188880, 189024, 189040, 189056, 189312, 189360, 189396,
  189408, 189504, 189520, 189568, 189680, 189792, 189824, 189828, 189984, 190000, 190044, 190116, 190160, 190176, 190336, 190368, 190464, 190480,
  190560, 190592, 190640, 190692, 190752, 190800, 190848, 190908, 191104, 191120, 191124, 191136, 191280, 191328, 191360, 191440, 191488, 191520,
  191616, 191628, 191712, 191872, 191904, 191920, 191988, 192000, 192096, 192128, 192192, 192288, 192384, 192480, 192492, 192560, 192636, 192640,
  192672, 192880, 192896, 193040, 193056, 193088, 193152, 193200, 193248, 193360, 193408, 193520, 193632, 193664, 193680, 193716, 193824, 193840,
  193920, 193932, 193984, 194000, 194016, 194148, 194160, 194176, 194320, 194364, 194400, 194592, 194640, 194652, 194688, 194784, 194868, 194880,
  194944, 194960, 194976, 195012, 195084, 195120, 195168, 195280, 195440, 195456, 195516, 195552, 195600, 195712, 195732, 195744, 195760, 195776,
  195876, 195920, 195936, 195948, 195968, 196020, 196128, 196164, 196224, 196240, 196320, 196480, 196512, 196672, 196704, 196720, 196736, 196880,
  196896, 196956, 197040, 197088, 197120, 197172, 197244, 197248, 197280, 197360, 197388, 197504, 197520, 197568, 197664, 197680, 197760, 197840,
  197856, 198000, 198016, 198036, 198048, 198108, 198160, 198252, 198272, 198320, 198432, 198464, 198480, 198528, 198624, 198640, 198684, 198756,
  198784, 198816, 198960, 198972, 199008, 199040, 199116, 199120, 199280, 199296, 199360, 199392, 199440, 199552, 199760, 199776, 199808, 199920,
  199968
]


def g1Meta : List (Nat × Nat × Nat × Nat) := [
  (8, 8, 125000000000, 1),
  (12, 12, 83333333333, 2),
  (36, 36, 27777777777, 2),
  (72, 72, 13888888888, 2),
  (80, 128, 30729166666, 6),
  (180, 288, 17162698411, 12),
  (384, 720, 20902821160, 49),
  (828, 1800, 21100430701, 169),
  (1824, 3968, 17140618854, 566),
  (4032, 8928, 16811866985, 1923),
  (9036, 19920, 15566213433, 6898),
  (20052, 45000, 15681556783, 28021),
  (45024, 99972, 14473839709, 107781),
  (100080, 199968, 12011071856, 327284)
]

def g1Buckets : List (Nat × Nat × Nat × Nat × List Nat) := [
  (8, 8, 125000000000, 1, g1List0),
  (12, 12, 83333333333, 2, g1List1),
  (36, 36, 27777777777, 2, g1List2),
  (72, 72, 13888888888, 2, g1List3),
  (80, 128, 30729166666, 6, g1List4),
  (180, 288, 17162698411, 12, g1List5),
  (384, 720, 20902821160, 49, g1List6),
  (828, 1800, 21100430701, 169, g1List7),
  (1824, 3968, 17140618854, 566, g1List8),
  (4032, 8928, 16811866985, 1923, g1List9),
  (9036, 19920, 15566213433, 6898, g1List10),
  (20052, 45000, 15681556783, 28021, g1List11),
  (45024, 99972, 14473839709, 107781, g1List12),
  (100080, 199968, 12011071856, 327284, g1List13)
]

def g4List0 : List Nat := [
  36
]

def g4List1 : List Nat := [
  80, 96, 128
]

def g4List2 : List Nat := [
  240, 288, 384, 448, 480
]

def g4List3 : List Nat := [
  560, 640, 672, 720, 864, 880, 896, 1040, 1056, 1152, 1200, 1248, 1344, 1360, 1408, 1440, 1520, 1632,
  1664, 1824, 1840, 1920, 2000
]

def g4List4 : List Nat := [
  2016, 2176, 2208, 2240, 2320, 2432, 2480, 2560, 2688, 2784, 2944, 2960, 2976, 3168, 3280, 3440, 3456, 3552,
  3600, 3712, 3744, 3760, 3936, 3968, 4032, 4128, 4224, 4240, 4480, 4512, 4720, 4736, 4880, 4896, 4928, 4992,
  5040, 5088, 5248, 5360, 5472, 5504, 5664, 5680, 5760, 5824, 5840, 5856, 6016, 6144, 6320, 6432, 6528, 6624,
  6640, 6720, 6784, 6816, 6912, 7008, 7040, 7120, 7296, 7552, 7584, 7616, 7680, 7760, 7776, 7808, 7920, 7968,
  8064, 8080, 8100, 8240, 8320, 8352, 8400, 8512, 8544, 8560, 8576, 8720, 8832, 8928, 9040, 9088, 9312, 9344,
  9360, 9408, 9600, 9696, 9856, 9888, 10000
]


def g4Meta : List (Nat × Nat × Nat × Nat × Nat × Nat) := [
  (36, 36, 1, 27777777777, 5555, 732),
  (80, 128, 3, 30729166666, 2500, 367),
  (240, 480, 5, 14558531744, 833, 145),
  (560, 2000, 23, 20914392009, 357, 71),
  (2016, 10000, 97, 19351601191, 113, 30)
]

def g4Groups : List (Nat × Nat × Nat × Nat × Nat × Nat × List Nat) := [
  (36, 36, 1, 27777777777, 5555, 732, g4List0),
  (80, 128, 3, 30729166666, 2500, 367, g4List1),
  (240, 480, 5, 14558531744, 833, 145, g4List2),
  (560, 2000, 23, 20914392009, 357, 71, g4List3),
  (2016, 10000, 97, 19351601191, 113, 30, g4List4)
]

private def isStrictSorted : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a < b) && isStrictSorted (b :: rest)

private lemma isStrictSorted_isChain : ∀ L : List Nat, isStrictSorted L = true → L.IsChain (· < ·) := by
  intro L
  induction L with
  | nil => intro _; exact List.isChain_nil
  | cons a rest ih =>
    cases rest with
    | nil => intro _; exact List.isChain_singleton a
    | cons b rest' =>
      intro h
      unfold isStrictSorted at h
      obtain ⟨hab, hrest⟩ := Bool.and_eq_true _ _ |>.mp h
      exact List.isChain_cons_cons.mpr ⟨decide_eq_true_eq.mp hab, ih hrest⟩

private lemma nodup_of_isStrictSorted {L : List Nat} (h : isStrictSorted L = true) : L.Nodup :=
  List.Pairwise.nodup (List.isChain_iff_pairwise.mp (isStrictSorted_isChain L h))

private def checkG1Bucket (klo khi S_i E_i : Nat) (ks : List Nat) : Bool :=
  decide (0 < klo ∧ khi ≤ 200000) &&
  isStrictSorted ks &&
  ks.all (fun k =>
    let ft := fastTauTop 18 primesLe448 k
    decide (klo ≤ k ∧ k ≤ khi ∧ k % (2 * ft.1) = 0)) &&
  decide ((ks.map (fun k => harmScale / k)).sum = S_i) &&
  decide ((ks.map (fun k => piHiTblFast (fastTauTop 18 primesLe448 k).2)).sum = E_i)

private def checkG4Group (mlo mhi cnt S4 L piL : Nat) (ms : List Nat) : Bool :=
  decide (0 < mlo ∧ mhi ≤ 10000 ∧ 100 ≤ L ∧ L ≤ 8192 ∧ piL = exactPiSmall L ∧ ms.length = cnt) &&
  isStrictSorted ms &&
  ms.all (fun m =>
    let ft := fastTauTop 14 primesLe100 m
    decide (mlo ≤ m ∧ m ≤ mhi ∧ m % (4 * ft.1) = 0 ∧ ft.2 ≤ L ∧ 200000 / m ≤ L)) &&
  decide ((ms.map (fun m => harmScale / m)).sum = S4)

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def g1CheckA : PLift (
    checkG1Bucket 8 8 125000000000 1 g1List0 = true ∧
    checkG1Bucket 12 12 83333333333 2 g1List1 = true ∧
    checkG1Bucket 36 36 27777777777 2 g1List2 = true ∧
    checkG1Bucket 72 72 13888888888 2 g1List3 = true ∧
    checkG1Bucket 80 128 30729166666 6 g1List4 = true ∧
    checkG1Bucket 180 288 17162698411 12 g1List5 = true ∧
    checkG1Bucket 384 720 20902821160 49 g1List6 = true ∧
    checkG1Bucket 828 1800 21100430701 169 g1List7 = true ∧
    checkG1Bucket 1824 3968 17140618854 566 g1List8 = true ∧
    checkG1Bucket 4032 8928 16811866985 1923 g1List9 = true ∧
    checkG1Bucket 9036 19920 15566213433 6898 g1List10 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def g1CheckB : PLift (checkG1Bucket 20052 45000 15681556783 28021 g1List11 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def g1CheckC : PLift (checkG1Bucket 45024 99972 14473839709 107781 g1List12 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def g1CheckD : PLift (checkG1Bucket 100080 199968 12011071856 327284 g1List13 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def g4CheckAll : PLift (
    checkG4Group 36 36 1 27777777777 5555 732 g4List0 = true ∧
    checkG4Group 80 128 3 30729166666 2500 367 g4List1 = true ∧
    checkG4Group 240 480 5 14558531744 833 145 g4List2 = true ∧
    checkG4Group 560 2000 23 20914392009 357 71 g4List3 = true ∧
    checkG4Group 2016 10000 97 19351601191 113 30 g4List4 = true) := ⟨by decide +kernel⟩

private lemma list_harmonic_le {L : List Nat} (hnd : L.Nodup) (hpos : ∀ k ∈ L, 0 < k) :
    (((L.map (fun k => harmScale / k)).sum : Nat) : ℝ) / harmScale ≤
      ∑ k ∈ L.toFinset, (1 : ℝ) / k := by
  have hS : (0 : ℝ) < harmScale := by norm_num [harmScale]
  induction L with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    have hxpos : 0 < x := hpos x (by simp)
    have hxs := ih hnd' (fun k hk => hpos k (List.mem_cons_of_mem _ hk))
    simp only [List.map_cons, List.sum_cons, List.toFinset_cons]
    rw [Finset.sum_insert (by simp [hx]), Nat.cast_add, add_div]
    have h1 : ((harmScale / x : Nat) : ℝ) / harmScale ≤ (1 : ℝ) / x := by
      have hxR : (0 : ℝ) < x := by exact_mod_cast hxpos
      have hdiv : ((harmScale / x : Nat) : ℝ) * x ≤ harmScale := by
        exact_mod_cast Nat.div_mul_le_self harmScale x
      rw [div_le_div_iff₀ hS hxR]
      linarith
    linarith

/- ### Part 3: Disjoint Family 1 (`k * q`) and Family 2 (`m * p * q`) lower bound -/

private lemma top_mul_prime {a q : Nat} (ha : 0 < a) (hq : q.Prime) (hlt : a.primeFactors.sup id < q) :
    (a * q).primeFactors.sup id = q := by
  have haq : a * q ≠ 0 := (Nat.mul_pos ha hq.pos).ne'
  apply le_antisymm
  · apply Finset.sup_le
    intro r hr
    obtain ⟨hrp, hrd, _⟩ := Nat.mem_primeFactors.mp hr
    rcases hrp.dvd_mul.mp hrd with hra | hrq
    · exact (prime_le_top hrp hra ha.ne').trans hlt.le
    · exact Nat.le_of_dvd hq.pos hrq
  · exact prime_le_top hq (dvd_mul_left q a) haq

private lemma triple_good {m p q : Nat} (hm : 0 < m ∧ 4 * m.divisors.card ∣ m)
    (hp : p.Prime) (hq : q.Prime) (hmp : m.primeFactors.sup id < p) (hpq : p < q) :
    (m * p * q).IsRefactorable := by
  have hndp : ¬ p ∣ m := fun h => hmp.not_ge (prime_le_top hp h hm.1.ne')
  have hcm_p : m.Coprime p := (hp.coprime_iff_not_dvd.mpr hndp).symm
  have htop_mp : (m * p).primeFactors.sup id = p := top_mul_prime hm.1 hp hmp
  have hndq : ¬ q ∣ m * p := fun h => hpq.not_ge (htop_mp ▸ prime_le_top hq h (Nat.mul_pos hm.1 hp.pos).ne')
  have hcmp_q : (m * p).Coprime q := (hq.coprime_iff_not_dvd.mpr hndq).symm
  refine ⟨Nat.mul_pos (Nat.mul_pos hm.1 hp.pos) hq.pos, ?_⟩
  rw [Nat.Coprime.card_divisors_mul hcmp_q, Nat.Coprime.card_divisors_mul hcm_p,
    hp.divisors, hq.divisors, Finset.card_pair hp.ne_one.symm, Finset.card_pair hq.ne_one.symm]
  have hd : m.divisors.card * 2 * 2 = 4 * m.divisors.card := by ring
  rw [hd]
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hm.2 p) q

private lemma triple_inj {m1 p1 q1 m2 p2 q2 : Nat}
    (hm1 : 0 < m1) (hm2 : 0 < m2) (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hq1 : q1.Prime) (hq2 : q2.Prime)
    (hmp1 : m1.primeFactors.sup id < p1) (hmp2 : m2.primeFactors.sup id < p2)
    (hpq1 : p1 < q1) (hpq2 : p2 < q2)
    (heq : m1 * p1 * q1 = m2 * p2 * q2) : m1 = m2 ∧ p1 = p2 ∧ q1 = q2 := by
  have htop1 : (m1 * p1 * q1).primeFactors.sup id = q1 :=
    top_mul_prime (Nat.mul_pos hm1 hp1.pos) hq1 (by rw [top_mul_prime hm1 hp1 hmp1]; exact hpq1)
  have htop2 : (m2 * p2 * q2).primeFactors.sup id = q2 :=
    top_mul_prime (Nat.mul_pos hm2 hp2.pos) hq2 (by rw [top_mul_prime hm2 hp2 hmp2]; exact hpq2)
  have hq : q1 = q2 := by rw [← htop1, heq, htop2]
  subst hq
  have hmp_eq : m1 * p1 = m2 * p2 := Nat.eq_of_mul_eq_mul_right hq1.pos heq
  obtain ⟨rfl, rfl⟩ := maxPrime_inj hm1 hm2 hp1 hp2 hmp1 hmp2 hmp_eq
  exact ⟨rfl, rfl, rfl⟩

private def f1Count (n : Nat) (B : Finset Nat) : Nat :=
  ∑ k ∈ B, ((n / k).primeCounting - (k.primeFactors.sup id).primeCounting)

private def f2Count (n : Nat) (D : Finset Nat) (L U : Nat) : Nat :=
  ∑ m ∈ D, ∑ p ∈ (Ioc L U).filter Nat.Prime, ((n / (m * p)).primeCounting - p.primeCounting)

private theorem disjoint_F1_F2_count (n : Nat)
    (Bsets : List (Finset Nat))
    (hB_disj : Bsets.Pairwise Disjoint)
    (hB_good : ∀ B ∈ Bsets, ∀ k ∈ B, 0 < k ∧ k ≤ 200000 ∧ 2 * k.divisors.card ∣ k)
    (Dgroups : List (Finset Nat × Nat × Nat))
    (hD_disj : (Dgroups.map Prod.fst).Pairwise Disjoint)
    (hD_good : ∀ g ∈ Dgroups, ∀ m ∈ g.1,
      0 < m ∧ 4 * m.divisors.card ∣ m ∧ m.primeFactors.sup id ≤ g.2.1 ∧ 200000 / m ≤ g.2.1) :
    (Bsets.map (f1Count n)).sum + (Dgroups.map (fun g => f2Count n g.1 g.2.1 g.2.2)).sum ≤
      countRefactorableNat n := by
  classical
  let choices1 (k : Nat) := Nat.primesLE (n / k) \ Nat.primesLE (k.primeFactors.sup id)
  let F1 (B : Finset Nat) : Finset Nat := (B.sigma choices1).image (fun t => t.1 * t.2)
  have hF1_card : ∀ B ∈ Bsets, f1Count n B ≤ (F1 B).card := by
    intro B hB
    have hinj : Set.InjOn (fun t : Σ _k : Nat, Nat => t.1 * t.2) ↑(B.sigma choices1) := by
      rintro ⟨k1, q1⟩ h1 ⟨k2, q2⟩ h2 heq
      obtain ⟨hk1, hq1⟩ := Finset.mem_sigma.mp h1
      obtain ⟨hk2, hq2⟩ := Finset.mem_sigma.mp h2
      obtain ⟨hq1a, hq1b⟩ := Finset.mem_sdiff.mp hq1
      obtain ⟨hq2a, hq2b⟩ := Finset.mem_sdiff.mp hq2
      obtain ⟨_, hp1⟩ := Nat.mem_primesLE.mp hq1a
      obtain ⟨_, hp2⟩ := Nat.mem_primesLE.mp hq2a
      have hlt1 : k1.primeFactors.sup id < q1 := lt_of_not_ge (fun h => hq1b (Nat.mem_primesLE.mpr ⟨h, hp1⟩))
      have hlt2 : k2.primeFactors.sup id < q2 := lt_of_not_ge (fun h => hq2b (Nat.mem_primesLE.mpr ⟨h, hp2⟩))
      obtain ⟨rfl, rfl⟩ := maxPrime_inj (hB_good B hB k1 hk1).1 (hB_good B hB k2 hk2).1 hp1 hp2 hlt1 hlt2 heq
      rfl
    rw [Finset.card_image_of_injOn hinj, Finset.card_sigma]
    refine Finset.sum_le_sum fun k _ => ?_
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
      show (choices1 k).card = _ from Finset.card_sdiff ..]
    exact Nat.sub_le_sub_left (Finset.card_le_card Finset.inter_subset_left) _
  have hF1_mem : ∀ B ∈ Bsets, ∀ x ∈ F1 B,
      1 ≤ x ∧ x ≤ n ∧ x.IsRefactorable ∧ x / x.primeFactors.sup id ∈ B ∧ x / x.primeFactors.sup id ≤ 200000 := by
    intro B hB x hx
    obtain ⟨⟨k, q⟩, hkq, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hk, hq⟩ := Finset.mem_sigma.mp hkq
    obtain ⟨hqa, hqb⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqu, hqp⟩ := Nat.mem_primesLE.mp hqa
    have hlt : k.primeFactors.sup id < q := lt_of_not_ge (fun h => hqb (Nat.mem_primesLE.mpr ⟨h, hqp⟩))
    obtain ⟨hk0, hk200, hkd⟩ := hB_good B hB k hk
    have hgood := product_good ⟨hk0, hkd⟩ hqp hlt
    have hle : k * q ≤ n := by
      simpa only [Nat.mul_comm q k] using (Nat.le_div_iff_mul_le hk0).mp hqu
    have htop : (k * q).primeFactors.sup id = q := top_mul_prime hk0 hqp hlt
    have hdiv : (k * q) / (k * q).primeFactors.sup id = k := by
      rw [htop, Nat.mul_div_cancel _ hqp.pos]
    refine ⟨hgood.1, hle, hgood, ?_, ?_⟩
    · rwa [hdiv]
    · rwa [hdiv]
  let choices2 (m p : Nat) := Nat.primesLE (n / (m * p)) \ Nat.primesLE p
  let F2 (g : Finset Nat × Nat × Nat) : Finset Nat :=
    ((g.1.sigma (fun _ => (Ioc g.2.1 g.2.2).filter Nat.Prime)).sigma (fun mp => choices2 mp.1 mp.2)).image
      (fun t => t.1.1 * t.1.2 * t.2)
  have hF2_card : ∀ g ∈ Dgroups, f2Count n g.1 g.2.1 g.2.2 ≤ (F2 g).card := by
    intro g hg
    have hinj : Set.InjOn (fun t : Σ mp : (Σ _m : Nat, Nat), Nat => t.1.1 * t.1.2 * t.2)
        ↑((g.1.sigma (fun _ => (Ioc g.2.1 g.2.2).filter Nat.Prime)).sigma (fun mp => choices2 mp.1 mp.2)) := by
      rintro ⟨⟨m1, p1⟩, q1⟩ h1 ⟨⟨m2, p2⟩, q2⟩ h2 heq
      obtain ⟨hmp1, hq1⟩ := Finset.mem_sigma.mp h1
      obtain ⟨hmp2, hq2⟩ := Finset.mem_sigma.mp h2
      obtain ⟨hm1, hp1m⟩ := Finset.mem_sigma.mp hmp1
      obtain ⟨hm2, hp2m⟩ := Finset.mem_sigma.mp hmp2
      obtain ⟨hp1I, hp1p⟩ := Finset.mem_filter.mp hp1m
      obtain ⟨hp2I, hp2p⟩ := Finset.mem_filter.mp hp2m
      obtain ⟨hq1a, hq1b⟩ := Finset.mem_sdiff.mp hq1
      obtain ⟨hq2a, hq2b⟩ := Finset.mem_sdiff.mp hq2
      obtain ⟨_, hq1p⟩ := Nat.mem_primesLE.mp hq1a
      obtain ⟨_, hq2p⟩ := Nat.mem_primesLE.mp hq2a
      have hpq1 : p1 < q1 := lt_of_not_ge (fun h => hq1b (Nat.mem_primesLE.mpr ⟨h, hq1p⟩))
      have hpq2 : p2 < q2 := lt_of_not_ge (fun h => hq2b (Nat.mem_primesLE.mpr ⟨h, hq2p⟩))
      have hm1g := hD_good g hg m1 hm1
      have hm2g := hD_good g hg m2 hm2
      have hlt1 : m1.primeFactors.sup id < p1 := lt_of_le_of_lt hm1g.2.2.1 (Finset.mem_Ioc.mp hp1I).1
      have hlt2 : m2.primeFactors.sup id < p2 := lt_of_le_of_lt hm2g.2.2.1 (Finset.mem_Ioc.mp hp2I).1
      obtain ⟨rfl, rfl, rfl⟩ := triple_inj hm1g.1 hm2g.1 hp1p hp2p hq1p hq2p hlt1 hlt2 hpq1 hpq2 heq
      rfl
    rw [Finset.card_image_of_injOn hinj, Finset.card_sigma, Finset.sum_sigma]
    refine Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun p _ => ?_
    rw [← Nat.primesLE_card_eq_primeCounting, ← Nat.primesLE_card_eq_primeCounting,
      show (choices2 m p).card = _ from Finset.card_sdiff ..]
    exact Nat.sub_le_sub_left (Finset.card_le_card Finset.inter_subset_left) _
  have hF2_mem : ∀ g ∈ Dgroups, ∀ y ∈ F2 g,
      1 ≤ y ∧ y ≤ n ∧ y.IsRefactorable ∧ 200000 < y / y.primeFactors.sup id ∧
      (y / y.primeFactors.sup id) / (y / y.primeFactors.sup id).primeFactors.sup id ∈ g.1 := by
    intro g hg y hy
    obtain ⟨⟨⟨m, p⟩, q⟩, hmpq, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hmp, hq⟩ := Finset.mem_sigma.mp hmpq
    obtain ⟨hm, hpm⟩ := Finset.mem_sigma.mp hmp
    obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hpm
    obtain ⟨hqa, hqb⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqu, hqp⟩ := Nat.mem_primesLE.mp hqa
    have hpq : p < q := lt_of_not_ge (fun h => hqb (Nat.mem_primesLE.mpr ⟨h, hqp⟩))
    obtain ⟨hm0, hm4, hmtop, hm200⟩ := hD_good g hg m hm
    have hlt_mp : m.primeFactors.sup id < p := lt_of_le_of_lt hmtop (Finset.mem_Ioc.mp hpI).1
    have hgood := triple_good ⟨hm0, hm4⟩ hpp hqp hlt_mp hpq
    have hle : m * p * q ≤ n := by
      simpa only [Nat.mul_comm q (m * p)] using (Nat.le_div_iff_mul_le (Nat.mul_pos hm0 hpp.pos)).mp hqu
    have htop_mp : (m * p).primeFactors.sup id = p := top_mul_prime hm0 hpp hlt_mp
    have htop_mpq : (m * p * q).primeFactors.sup id = q :=
      top_mul_prime (Nat.mul_pos hm0 hpp.pos) hqp (by rw [htop_mp]; exact hpq)
    have hdiv1 : (m * p * q) / (m * p * q).primeFactors.sup id = m * p := by
      rw [htop_mpq, Nat.mul_div_cancel _ hqp.pos]
    have hdiv2 : (m * p) / (m * p).primeFactors.sup id = m := by
      rw [htop_mp, Nat.mul_div_cancel _ hpp.pos]
    have hgt200 : 200000 < m * p := by
      have hp_gt : 200000 / m < p := lt_of_le_of_lt hm200 (Finset.mem_Ioc.mp hpI).1
      simpa only [Nat.mul_comm p m] using (Nat.div_lt_iff_lt_mul hm0).mp hp_gt
    refine ⟨hgood.1, hle, hgood, ?_, ?_⟩
    · rwa [hdiv1]
    · rw [hdiv1, hdiv2]; exact hm
  -- Combine pairwise-disjoint Finsets in a single list union!
  let allSets : List (Finset Nat) := Bsets.map F1 ++ Dgroups.map F2
  have hsum_card : ∀ (L : List (Finset Nat)), L.Pairwise Disjoint →
      (∀ S ∈ L, S ⊆ (Icc 1 n).filter Nat.IsRefactorable) →
      (L.map Finset.card).sum ≤ ((Icc 1 n).filter Nat.IsRefactorable).card := by
    intro L hpw hsub
    have hU : ∀ (M : List (Finset Nat)), M.Pairwise Disjoint →
        (M.map Finset.card).sum = (M.foldr (· ∪ ·) ∅).card ∧
        (∀ x ∈ M.foldr (· ∪ ·) ∅, ∃ S ∈ M, x ∈ S) := by
      intro M
      induction M with
      | nil => intro _; simp
      | cons S Ms ih =>
        intro hpw'
        obtain ⟨hS_disj, hMs_pw⟩ := List.pairwise_cons.mp hpw'
        obtain ⟨hcard', hmem'⟩ := ih hMs_pw
        have hdisj : Disjoint S (Ms.foldr (· ∪ ·) ∅) := by
          rw [Finset.disjoint_left]
          intro x hxS hxU
          obtain ⟨T, hT, hxT⟩ := hmem' x hxU
          exact Finset.disjoint_left.mp (hS_disj T hT) hxS hxT
        refine ⟨?_, ?_⟩
        · simp only [List.map_cons, List.sum_cons, List.foldr_cons]
          rw [Finset.card_union_of_disjoint hdisj, hcard']
        · intro x hx
          simp only [List.foldr_cons, Finset.mem_union] at hx
          rcases hx with hxS | hxU
          · exact ⟨S, by simp, hxS⟩
          · obtain ⟨T, hT, hxT⟩ := hmem' x hxU
            exact ⟨T, List.mem_cons_of_mem _ hT, hxT⟩
    obtain ⟨heq, hmem⟩ := hU L hpw
    rw [heq]
    apply Finset.card_le_card
    intro x hx
    obtain ⟨S, hS, hxS⟩ := hmem x hx
    exact hsub S hS hxS
  have hall_pw : allSets.Pairwise Disjoint := by
    rw [List.pairwise_append]
    refine ⟨?_, ?_, ?_⟩
    · rw [List.pairwise_map]
      refine hB_disj.imp_of_mem fun {B1 B2} hB1 hB2 hdisj => ?_
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have h1 := (hF1_mem B1 hB1 x hx1).2.2.2.1
      have h2 := (hF1_mem B2 hB2 x hx2).2.2.2.1
      exact Finset.disjoint_left.mp hdisj h1 h2
    · rw [List.pairwise_map]
      rw [List.pairwise_map] at hD_disj
      refine hD_disj.imp_of_mem fun {g1 g2} hg1 hg2 hdisj => ?_
      rw [Finset.disjoint_left]
      intro y hy1 hy2
      have h1 := (hF2_mem g1 hg1 y hy1).2.2.2.2
      have h2 := (hF2_mem g2 hg2 y hy2).2.2.2.2
      exact Finset.disjoint_left.mp hdisj h1 h2
    · intro S1 hS1 S2 hS2
      obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hS1
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hS2
      rw [Finset.disjoint_left]
      intro x hx1 hx2
      have hle := (hF1_mem B hB x hx1).2.2.2.2
      have hgt := (hF2_mem g hg x hx2).2.2.2.1
      omega
  have hall_sub : ∀ S ∈ allSets, S ⊆ (Icc 1 n).filter Nat.IsRefactorable := by
    intro S hS
    rcases List.mem_append.mp hS with h1 | h2
    · obtain ⟨B, hB, rfl⟩ := List.mem_map.mp h1
      intro x hx
      obtain ⟨h1, h2, h3, _, _⟩ := hF1_mem B hB x hx
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, h3⟩
    · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp h2
      intro y hy
      obtain ⟨h1, h2, h3, _, _⟩ := hF2_mem g hg y hy
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h1, h2⟩, h3⟩
  have h1 : (Bsets.map (f1Count n)).sum ≤ ((Bsets.map F1).map Finset.card).sum := by
    rw [List.map_map]
    clear hall_pw hall_sub hsum_card hF2_mem hF2_card hF1_mem hD_good hD_disj hB_good hB_disj
    induction Bsets with
    | nil => simp
    | cons B Bs ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply]
      exact Nat.add_le_add (hF1_card B (by simp)) (ih (fun B' hB' => hF1_card B' (List.mem_cons_of_mem _ hB')))
  have h2 : (Dgroups.map (fun g => f2Count n g.1 g.2.1 g.2.2)).sum ≤ ((Dgroups.map F2).map Finset.card).sum := by
    rw [List.map_map]
    clear hall_pw hall_sub hsum_card hF1_mem hF1_card hF2_mem hD_good hD_disj hB_good hB_disj h1
    induction Dgroups with
    | nil => simp
    | cons g gs ih =>
      simp only [List.map_cons, List.sum_cons, Function.comp_apply]
      exact Nat.add_le_add (hF2_card g (by simp)) (ih (fun g' hg' => hF2_card g' (List.mem_cons_of_mem _ hg')))
  have htot := hsum_card allSets hall_pw hall_sub
  rw [show (allSets.map Finset.card).sum =
      ((Bsets.map F1).map Finset.card).sum + ((Dgroups.map F2).map Finset.card).sum by
    simp [allSets, List.map_append, List.sum_append]] at htot
  exact (Nat.add_le_add h1 h2).trans htot

/- ### Part 4: Elementary monotonicity helpers and integer evaluators -/

private lemma log_div_log_div_antitone {c a b : ℝ} (hc : 1 ≤ c) (hca : c < a) (hab : a ≤ b) :
    Real.log b / Real.log (b / c) ≤ Real.log a / Real.log (a / c) := by
  have hc0 : 0 < c := by linarith
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hloga : 0 < Real.log (a / c) := Real.log_pos ((one_lt_div hc0).mpr hca)
  have hlogb : 0 < Real.log (b / c) := Real.log_pos ((one_lt_div hc0).mpr (lt_of_lt_of_le hca hab))
  rw [div_le_div_iff₀ hlogb hloga, Real.log_div ha0.ne' hc0.ne', Real.log_div hb0.ne' hc0.ne']
  have hlog_le : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  nlinarith

private lemma log_div_log_div_sub_one_antitone {c a b : ℝ} (hc : 1 ≤ c) (ha0 : 0 < a)
    (hca : 1 < Real.log (a / c)) (hab : a ≤ b) :
    Real.log b / (Real.log (b / c) - 1) ≤ Real.log a / (Real.log (a / c) - 1) := by
  have hc0 : 0 < c := by linarith
  have hb0 : 0 < b := by linarith
  have hlogc : 0 ≤ Real.log c := Real.log_nonneg hc
  have hlogb_gt : 1 < Real.log (b / c) :=
    lt_of_lt_of_le hca (Real.log_le_log (div_pos ha0 hc0) (div_le_div_of_nonneg_right hab hc0.le))
  rw [div_le_div_iff₀ (by linarith) (by linarith),
    Real.log_div ha0.ne' hc0.ne', Real.log_div hb0.ne' hc0.ne']
  have hlog_le : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  nlinarith

private lemma log_div_self_antitone {a b : ℝ} (ha : 3 ≤ a) (hab : a ≤ b) :
    Real.log b / b ≤ Real.log a / a := by
  let f : ℝ → ℝ := fun t => -(Real.log t / t)
  have hderiv : ∀ t ∈ Set.Ici (3 : ℝ), HasDerivAt f ((Real.log t - 1) / t ^ 2) t := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [Set.mem_Ici.mp ht]
    have hdiv := (Real.hasDerivAt_log ht0).fun_div (hasDerivAt_id t) ht0
    have hneg := hdiv.fun_neg
    have heq : -((t⁻¹ * t - Real.log t * 1) / t ^ 2) = (Real.log t - 1) / t ^ 2 := by
      field_simp; ring
    simpa only [id_eq, heq] using hneg
  have hmono : MonotoneOn f (Set.Ici 3) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 3)
    · exact fun t ht => (hderiv t ht).continuousAt.continuousWithinAt
    · exact fun t ht => (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have ht3 : 3 ≤ t := interior_subset ht
      rw [(hderiv t ht3).deriv]
      have hlog3 : 1 < Real.log t := by
        have := Real.log_three_gt_d9
        have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) ht3
        linarith
      exact div_nonneg (by linarith) (by positivity)
  have hle := hmono (Set.mem_Ici.mpr ha) (Set.mem_Ici.mpr (ha.trans hab)) hab
  dsimp only [f] at hle
  linarith

def ceilDiv (a b : Nat) : Nat := (a + b - 1) / b

def lhsHi (Na : Nat) : Nat :=
  let la := logNatLo Na
  ceilDiv (10562 * ratioScale * (la * la + la * logScale + 3 * logScale * logScale))
    (10000 * la * la)

def g1BucketTerm (Na Nb klo khi S_i E_i : Nat) : Nat :=
  if Na < 101 * khi then 0
  else
    let lb_lo := logNatLo Nb
    let la_hi := logNatHi Na
    let l_nk_hi := logRatHi Nb klo
    let main :=
      if 2000 * khi ≤ Na ∧ Nb ≤ 10000000 * klo then
        (2 * 990 * ratioScale * S_i * lb_lo) / (1000 * harmScale * (l_nk_hi - logScale))
      else
        (2 * 9400 * ratioScale * S_i * lb_lo * (l_nk_hi + logScale)) /
          (10000 * harmScale * l_nk_hi * l_nk_hi)
    let err := ceilDiv (2 * ratioScale * E_i * la_hi) (logScale * Na)
    main - err

def g4PiUHi (U : Nat) : Nat :=
  if U ≤ 14090240 then piHiTblFast U
  else
    let lu_lo := logNatLo U
    ceilDiv (10562 * U * logScale * (lu_lo * lu_lo + lu_lo * logScale + 3 * logScale * logScale))
      (10000 * lu_lo * lu_lo * lu_lo)

def g4HpLo (L piL U : Nat) : Nat :=
  let lu_lo := logNatLo U
  let lu_hi := logNatHi U
  let lL1_hi := logNatHi (L + 1)
  if lu_lo ≤ lL1_hi then 0
  else
    let llog_lo := logRatLo lu_lo lL1_hi
    let term_u := (9400 * ratioScale * logScale * (lu_hi + logScale)) / (10000 * lu_hi * lu_hi)
    let term_ll := (9400 * ratioScale * llog_lo) / (10000 * logScale)
    let term_L := ceilDiv (ratioScale * piL) L
    term_u + term_ll - term_L

def g4GroupTerm (Na Nb mlo mhi cnt S4 L piL : Nat) : Nat :=
  let U := Nat.sqrt (Na / (20 * mhi))
  if U ≤ L ∨ Na < 101 * mhi * U then 0
  else
    let Hp := g4HpLo L piL U
    if Hp = 0 then 0
    else
      let lb_lo := logNatLo Nb
      let la_hi := logNatHi Na
      let l_nmp_hi := logRatHi Nb (mlo * L)
      let main2 := (2 * 9400 * S4 * Hp * lb_lo * (l_nmp_hi + logScale)) /
        (10000 * harmScale * l_nmp_hi * l_nmp_hi)
      let piU := g4PiUHi U
      let err2 := ceilDiv (2 * ratioScale * cnt * piU * piU * la_hi) (logScale * Na)
      main2 - err2

def rhs1Int (Na Nb : Nat) : Nat :=
  (g1Meta.map (fun b => g1BucketTerm Na Nb b.1 b.2.1 b.2.2.1 b.2.2.2)).sum

def rhs2Int (Na Nb : Nat) : Nat :=
  (g4Meta.map (fun g => g4GroupTerm Na Nb g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2)).sum

def intervals430 : Array Nat := #[
  14090240, 14935654, 15831793, 16781700,
  17788602, 18855918, 19987273, 21186509,
  22457699, 23805160, 25233469, 26747477,
  28352325, 30053464, 31856671, 33768071,
  35794155, 37941804, 40218312, 42631410,
  45189294, 47900651, 50774690, 53821171,
  57050441, 60473467, 64101875, 67947987,
  72024866, 76346357, 80927138, 85782766,
  90929731, 96385514, 102168644, 117493940,
  135118031, 155385735, 178693595, 205497634,
  236322279, 271770620, 312536213, 359416644,
  413329140, 475328510, 546627786, 628621953,
  722915245, 831352531, 956055410, 1099463721,
  1264383279, 1454040770, 1672146885, 1922968917,
  2211414254, 2543126392, 2924595350, 3363284652,
  3867777349, 4447943951, 5115135543, 5882405874,
  6764766755, 7779481768, 8946404033, 10288364637,
  11831619332, 13606362231, 15647316565, 17994414049,
  20693576156, 23797612579, 27367254465, 31472342634,
  36193194029, 41622173133, 47865499102, 55045323967,
  63302122562, 72797440946, 83717057087, 96274615650,
  110715807997, 127323179196, 146421656075, 168384904486,
  193642640158, 222689036181, 256092391608, 294506250349,
  338682187901, 389484516086, 447907193498, 515093272522,
  592357263400, 681210852910, 783392480846, 900901352972,
  1036036555917, 1191442039304, 1370158345199, 1575682096978,
  1812034411524, 2083839573252, 2396415509239, 2755877835624,
  3169259510967, 3644648437612, 4191345703253, 4820047558740,
  5543054692551, 6374512896433, 7330689830897, 8430293305531,
  9694837301360, 11149062896564, 12821422331048, 14744635680705,
  16956331032810, 19499780687731, 22424747790890, 25788459959523,
  29656728953451, 34105238296468, 39221024040938, 45104177647078,
  51869804294139, 59650274938259, 68597816178997, 78887488605846,
  90720611896722, 104328703681230, 119978009233414, 137974710618426,
  158670917211189, 182471554792867, 209842288011797, 241318631213566,
  277516425895600, 319143889779940, 367015473246931, 422067794233970,
  485377963369065, 558184657874424, 641912356555587, 738199210038925,
  848929091544763, 976268455276477, 1122708723567948, 1291115032103140,
  1484782286918611, 1707499629956402, 1963624574449862, 2258168260617341,
  2596893499709942, 2986427524666433, 3434391653366397, 3949550401371356,
  4541982961577059, 5223280405813617, 6006772466685659, 6907788336688507,
  7943956587191782, 9135550075270548, 10505882586561130, 12081764974545298,
  13894029720727092, 15978134178836154, 18374854305661576, 21131082451510812,
  24300744819237432, 27945856542123044, 32137735023441500, 36958395276957720,
  42502154568501376, 48877477753776576, 56209099416843056, 64640464329369512,
  74336533978774928, 85487014075591168, 98310066186929840, 113056576114969312,
  130015062532214704, 149517321912046912, 171944920198853920, 197736658228681984,
  227397156962984256, 261506730507431872, 300732740083546624, 345842651096078592,
  397719048760490368, 457376906074563904, 525983441985748480, 604880958283610752,
  695613102026152320, 799955067330075136, 919948327429586304, 1057940576544024192,
  1216631663025627648, 1399126412479471616, 1608995374351392256, 1850344680504100864,
  2127896382579715840, 2447080839966672896, 2814142965961673728, 3236264410855924736,
  3721704072484313088, 4279959683356959744, 4921953635860503552, 5660246681239578624,
  6509283683425514496, 7485676235939341312, 8608527671330241536, 9899806822029776896,
  11384777845334243328, 13092494522134378496, 15056368700454533120, 17314824005522712576,
  19912047606351118336, 22898854747303784448, 26333682959399350272, 30283735403309248512,
  34826295713805631488, 40050240070876471296, 46057776081507942400, 52966442493734133760,
  60911408867794247680, 70048120197963382784, 80555338227657883648, 92638638961806557184,
  106534434806077538304, 122514600026989166592, 140891790031037530112, 162025558535693139968,
  186329392316047097856, 214278801163454152704, 246420621337972244480, 283383714538668064768,
  325891271719468269568, 374774962477388464128, 430991206848996704256, 495639887876346150912,
  569985871057798037504, 655483751716467638272, 753806314473937698816, 866877261645028261888,
  996908850891782488064, 1146445178525549723648, 1318411955304382070784, 1516173748600039276544,
  1743599810890045063168, 2005139782523551744000, 2305910749902084243456, 2651797362387396853760,
  3049566966745506250752, 3507002011757331873792, 4033052313520931602432, 4638010160549070897152,
  5333711684631430955008, 6133768437326145388544, 7053833702925066567680, 8111908758363826028544,
  9328695072118398779392, 10727999332936157495296, 12337199232876579651584, 14187779117808065970176,
  16315945985479274397696, 18763337883301164613632, 21577838565796337418240, 24814514350665788030976,
  28536691503265654767616, 32817195228755501514752, 37739774513068824854528, 43400740690029145227264,
  49910851793533511139328, 57397479562563530260480, 66007101496948053508096, 75908166721490261114880,
  87294391729713796087808, 100388550489170862145536, 115446833062546484756480, 132763858021928444887040,
  152678436725217711620096, 175580202234000344875008, 201917232569100368084992, 232204817454465418264576,
  267035540072635207516160, 307090871083530497032192, 353154501746060024610816, 406127677007969021591552,
  467046828559164344631296, 537103852843038939283456, 617669430769494706356224, 710319845384918851911680,
  816867822192656612589568, 939397995521555017236480, 1080307694849788236267520, 1242353849077256337489920,
  1428706926438844788113408, 1643012965404671452643328, 1889464910215372049743872, 2172884646747677709565952,
  2498817343759829352579072, 2873639945323803406499840, 3304685937122373783257088, 3800388827690729662840832,
  4370447151844339031736320, 5026014224620989618061312, 5779916358314137309151232, 6646903812061257422340096,
  7643939383870445659881472, 8790530291451011757244416, 10109109835168662071279616, 11625476310443961274597376,
  13369297757010554821541888, 15374692420562136112037888, 17680896283646454596108288, 20333030726193419242176512,
  23382985335122430840012800, 26890433135390793318531072, 30923998105699411027820544, 35562597821554319031271424,
  40896987494787462161498112, 47031535619005575902265344, 54086265961856409710624768, 62199205856134866013257728,
  71529086734555092908769280, 82258449744738358992568320, 94597217206449104251518976, 108786799787416468171259904,
  125104819755528922935066624, 143870542718858245913444352, 165451124126686979364487168, 190268792745690021115199488,
  218809111657543493358714880, 251630478406174983002783744, 289375050167101223581253632, 332781307692166386502598656,
  382698503845991299810328576, 440103279422889950114217984, 506118771336323401399664640, 582036587036771860070006784,
  669342075092287546309214208, 769743386356130595792224256, 885204894309550123313528832, 1017985628455982518115500032,
  1170683472724379772137766912, 1346285993633036614263373824, 1548228892677991996451717120, 1780463226579690589761044480,
  2047532710566643972066770944, 2354662617151640251767193600, 2707862009724385945934888960, 3114041311183043425508261888,
  3581147507860499856871129088, 4118319634039574752938426368, 4736067579145510745976864768, 5446477716017336725654208512,
  6263449373419937179526758400, 7202966779432926656944144384, 8283411796347864720900882432, 9525923565800043824304619520,
  10954812100670049298438684672, 12598033915770554714083557376, 14487739003136137481391439872, 16660899853606557773746667520,
  19160034831647539240785412096, 22034040056394668587586945024, 25339146064853867116506382336, 29140017974581946744177688576,
  33511020670769236116976435200, 38537673771384618235988017152, 44318324837092304594218778624, 50966073562656144126086479872,
  58610984597054564865390149632, 67402632286612742118519603200, 77513027129604644640204521472, 89139981199045327262486364160,
  102510978378902113157719785472, 117887625135737429251768451072, 135570768906098038361877905408, 155906384242012731801629360128,
  179292341878314620461250510848, 206186193160061810012000878592, 237114122134071058643959152640, 272681240454181708644460003328,
  313583426522308935034412728320, 360620940500655257697388593152, 414714081575753497093875957760, 476921193812116468881399218176,
  548459372883933896992362594304, 630728278816523918209347223552, 725337520639002403906070249472, 834138148734852715233859862528,
  959258871045080566223943499776, 1103147701701842503383172251648, 1268619856957118857780024836096, 1458912835500686503488293699584,
  1677749760825789450864040083456, 1929412224949657685534911234048, 2218824058692106141332664221696, 2551647667495921879573828993024,
  2934394817620309851887428960256, 3374554040263356217080552620032, 3880737146302859565200142499840, 4462847718248288359242675519488,
  5132274875985530853146639728640, 5902116107383359636693705555968, 6787433523490863525902766047232, 7805548552014492829608199585792,
  8976380834816665684444518023168, 10322837960039164917866246963200, 11871263654045037966696323743744, 13651953202151793211340809568256,
  15699746182474561517501986897920, 18054708109845744056277424668672, 20762914326322603187739243315200, 23877351475270992540000222969856,
  27458954196561640745460312309760, 31577797326045882353679731785728, 36314466924952763806011766079488, 41761636963695674098493884989440,
  48025882508250022961468154052608, 55229764884487525504968451686400, 63514229617160645323514464698368, 73041364059734734465922267873280,
  83997568668694940132210980683776, 96597203968999174847003149467648, 100000000000000000000000000000000
]

def checkIntRange (lo cnt : Nat) : Bool :=
  (List.range cnt).all (fun i =>
    let j := lo + i
    let Na := intervals430[j]!
    let Nb := intervals430[j + 1]!
    decide (Na ≤ Nb ∧ lhsHi Na ≤ rhs1Int Na Nb + rhs2Int Na Nb))

private lemma checkIntRange_at {lo cnt j : Nat}
    (h : checkIntRange lo cnt = true) (h1 : lo ≤ j) (h2 : j < lo + cnt) :
    intervals430[j]! ≤ intervals430[j + 1]! ∧
    lhsHi intervals430[j]! ≤ rhs1Int intervals430[j]! intervals430[j + 1]! +
      rhs2Int intervals430[j]! intervals430[j + 1]! := by
  unfold checkIntRange at h
  rw [List.all_eq_true] at h
  have hres := decide_eq_true_eq.mp (h (j - lo) (List.mem_range.mpr (by omega)))
  rwa [show lo + (j - lo) = j by omega] at hres

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def intBatch0 : PLift (checkIntRange 0 72 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def intBatch1 : PLift (checkIntRange 72 72 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def intBatch2 : PLift (checkIntRange 144 72 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def intBatch3 : PLift (checkIntRange 216 72 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def intBatch4 : PLift (checkIntRange 288 72 = true) := ⟨by decide +kernel⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 40000 in
private def intBatch5 : PLift (checkIntRange 360 70 = true) := ⟨by decide +kernel⟩


-- Tail [10^32, ∞) check
def Ntail : Nat := 100000000000000000000000000000000

def g1TailSum : Nat :=
  let S_tot := (g1Meta.map (fun b => b.2.2.1)).sum
  let E_tot := (g1Meta.map (fun b => b.2.2.2)).sum
  (2 * 9400 * ratioScale * S_tot) / (10000 * harmScale) -
    ceilDiv (2 * ratioScale * E_tot * logNatHi Ntail) (logScale * Ntail)

def g4TailTerm (mhi cnt S4 L piL : Nat) : Nat :=
  let U0 := Nat.sqrt (Ntail / (20 * mhi))
  let Hp := g4HpLo L piL U0
  let piU := g4PiUHi U0
  (2 * 9400 * S4 * Hp) / (10000 * harmScale) -
    ceilDiv (2 * ratioScale * cnt * piU * piU * logNatHi Ntail) (logScale * Ntail)

def g4TailSum : Nat :=
  (g4Meta.map (fun g => g4TailTerm g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2)).sum

set_option maxHeartbeats 0 in
private def tailCheck : PLift (lhsHi Ntail ≤ g1TailSum + g4TailSum) := ⟨by decide +kernel⟩

/- ### Part 5: Analytic soundness connecting integer checks to real bounds -/

private lemma nat_div_cast_le {a b : Nat} (hb : 0 < b) :
    ((a / b : Nat) : ℝ) ≤ (a : ℝ) / b := by
  rw [le_div_iff₀ (by exact_mod_cast hb)]
  exact_mod_cast Nat.div_mul_le_self a b

private lemma ceilDiv_cast_ge {a b : Nat} (hb : 0 < b) :
    (a : ℝ) / b ≤ ((ceilDiv a b : Nat) : ℝ) := by
  rw [div_le_iff₀ (by exact_mod_cast hb)]
  unfold ceilDiv
  have h : a ≤ ((a + b - 1) / b) * b := by
    have hmod := Nat.div_add_mod (a + b - 1) b
    have hlt := Nat.mod_lt (a + b - 1) hb
    rw [Nat.mul_comm] at hmod
    omega
  exact_mod_cast h

private lemma nat_sub_cast_ge (a b : Nat) : (a : ℝ) - b ≤ ((a - b : Nat) : ℝ) := by
  by_cases h : b ≤ a
  · rw [Nat.cast_sub h]
  · push Not at h
    have : a - b = 0 := Nat.sub_eq_zero_of_le h.le
    rw [this, Nat.cast_zero]
    have : (a : ℝ) ≤ b := by exact_mod_cast h.le
    linarith

private lemma nat_sub_cast_le_of_le {a b : Nat} {X : ℝ} (h0 : 0 ≤ X) (h : (a : ℝ) - b ≤ X) :
    ((a - b : Nat) : ℝ) ≤ X := by
  by_cases hle : b ≤ a
  · rwa [Nat.cast_sub hle]
  · push Not at hle
    have : a - b = 0 := Nat.sub_eq_zero_of_le hle.le
    rw [this, Nat.cast_zero]
    exact h0

private lemma floor_nat_div_eq (n k : Nat) : ⌊(n : ℝ) / (k : ℝ)⌋₊ = n / k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  have hk0 : 0 < k := Nat.pos_of_ne_zero hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  apply le_antisymm
  · rw [Nat.le_div_iff_mul_le hk0]
    have h1 : (⌊(n : ℝ) / k⌋₊ : ℝ) * k ≤ n := (le_div_iff₀ hkR).mp (Nat.floor_le (by positivity))
    exact_mod_cast h1
  · apply Nat.le_floor
    rw [le_div_iff₀ hkR]
    exact_mod_cast Nat.div_mul_le_self n k

private lemma logNatLo_pos {m : Nat} (hm : 10 ≤ m) : 0 < logNatLo m := by
  have h1 : 3 ≤ m.log2 := by
    have h8 : 2 ^ 3 ≤ m := by omega
    exact (Nat.le_log2 (by omega : m ≠ 0)).mpr h8
  unfold logNatLo logRatLo logRatBounds
  dsimp only
  rw [Nat.div_one]
  exact Nat.add_pos_left (Nat.add_pos_left (by omega) _) _

private lemma lhsHi_sound {Na n : Nat} (hNa : 10000000 ≤ Na) (hn : Na ≤ n) :
    (n.primeCounting : ℝ) / ((n : ℝ) / Real.log n) ≤ (lhsHi Na : ℝ) / ratioScale := by
  have hn10M : (10 ^ 7 : ℝ) ≤ n := by
    have : (10000000 : ℝ) ≤ n := by exact_mod_cast (hNa.trans hn)
    norm_num; linarith
  have hpi := pi_upper_10M_full hn10M
  rw [Nat.floor_natCast] at hpi
  have hn_pos : (0 : ℝ) < n := by linarith
  have hlogn_pos : 0 < Real.log n := Real.log_pos (by linarith)
  have hlogNa_lo := (logRatBounds_correct (a := Na) (b := 1) le_rfl (by omega)).1
  simp only [Nat.cast_one, div_one] at hlogNa_lo
  have hla_pos : 0 < logNatLo Na := logNatLo_pos (by omega)
  have hS_pos : (0 : ℝ) < logScale := by norm_num [logScale]
  have hlaR_pos : (0 : ℝ) < (logNatLo Na : ℝ) / logScale := by positivity
  have hlogn_ge : (logNatLo Na : ℝ) / logScale ≤ Real.log n :=
    hlogNa_lo.trans (Real.log_le_log (by exact_mod_cast (show 0 < Na by omega)) (by exact_mod_cast hn))
  have hdiv : (n.primeCounting : ℝ) / ((n : ℝ) / Real.log n) ≤
      1.0562 * (1 + 1 / Real.log n + 3 / (Real.log n) ^ 2) := by
    rw [div_le_iff₀ (div_pos hn_pos hlogn_pos)]
    have heq : 1.0562 * (1 + 1 / Real.log n + 3 / (Real.log n) ^ 2) * ((n : ℝ) / Real.log n) =
        1.0562 * ((n : ℝ) / Real.log n + (n : ℝ) / (Real.log n) ^ 2 + 3 * (n : ℝ) / (Real.log n) ^ 3) := by
      field_simp
    rw [heq]; exact hpi
  have hinv1 : 1 / Real.log n ≤ 1 / ((logNatLo Na : ℝ) / logScale) :=
    div_le_div_of_nonneg_left (by norm_num) hlaR_pos hlogn_ge
  have hinv2 : 3 / (Real.log n) ^ 2 ≤ 3 / ((logNatLo Na : ℝ) / logScale) ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (pow_le_pow_left₀ hlaR_pos.le hlogn_ge 2)
  have hW_pos : (0 : ℝ) < ratioScale := by norm_num [ratioScale]
  have hceil := ceilDiv_cast_ge (a := 10562 * ratioScale * (logNatLo Na * logNatLo Na + logNatLo Na * logScale + 3 * logScale * logScale))
    (b := 10000 * logNatLo Na * logNatLo Na) (by positivity)
  have hceil' : (10562 * (ratioScale : ℝ) * ((logNatLo Na : ℝ) * logNatLo Na + logNatLo Na * logScale + 3 * logScale * logScale)) /
      (10000 * (logNatLo Na : ℝ) * logNatLo Na) / ratioScale ≤ (lhsHi Na : ℝ) / ratioScale := by
    apply div_le_div_of_nonneg_right _ hW_pos.le
    have hcast : (((10562 * ratioScale * (logNatLo Na * logNatLo Na + logNatLo Na * logScale + 3 * logScale * logScale) : Nat) : ℝ) /
        ((10000 * logNatLo Na * logNatLo Na : Nat) : ℝ)) =
        (10562 * (ratioScale : ℝ) * ((logNatLo Na : ℝ) * logNatLo Na + logNatLo Na * logScale + 3 * logScale * logScale)) /
          (10000 * (logNatLo Na : ℝ) * logNatLo Na) := by push_cast; ring
    rw [← hcast]
    exact hceil
  have halg : 1.0562 * (1 + 1 / ((logNatLo Na : ℝ) / logScale) + 3 / ((logNatLo Na : ℝ) / logScale) ^ 2) =
      (10562 * (ratioScale : ℝ) * ((logNatLo Na : ℝ) * logNatLo Na + logNatLo Na * logScale + 3 * logScale * logScale)) /
        (10000 * (logNatLo Na : ℝ) * logNatLo Na) / ratioScale := by
    have hla_ne : (logNatLo Na : ℝ) ≠ 0 := (by exact_mod_cast hla_pos : (0 : ℝ) < logNatLo Na).ne'
    have hS_ne : (logScale : ℝ) ≠ 0 := hS_pos.ne'
    have hW_ne : (ratioScale : ℝ) ≠ 0 := hW_pos.ne'
    field_simp; ring
  linarith

private lemma g1Bucket_valid_props {klo khi S_i E_i : Nat} {ks : List Nat}
    (hchk : checkG1Bucket klo khi S_i E_i ks = true) :
    0 < klo ∧ khi ≤ 200000 ∧ ks.Nodup ∧
    (∀ k ∈ ks, klo ≤ k ∧ k ≤ khi ∧ 0 < k ∧ k ≤ 200000 ∧ 2 * k.divisors.card ∣ k) ∧
    (S_i : ℝ) / harmScale ≤ ∑ k ∈ ks.toFinset, (1 : ℝ) / k ∧
    ∑ k ∈ ks.toFinset, ((k.primeFactors.sup id).primeCounting : ℝ) ≤ (E_i : ℝ) := by
  unfold checkG1Bucket at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨⟨hklo, hkhi⟩, hch⟩, hall⟩, hS⟩, hE⟩ := hchk
  have hnd : ks.Nodup := nodup_of_isStrictSorted hch
  have hmem : ∀ k ∈ ks, klo ≤ k ∧ k ≤ khi ∧ 0 < k ∧ k ≤ 200000 ∧ 2 * k.divisors.card ∣ k ∧
      (fastTauTop 18 primesLe448 k).2 = k.primeFactors.sup id := by
    intro k hk
    have h1 := decide_eq_true_eq.mp (List.all_eq_true.mp hall k hk)
    have hk0 : 0 < k := by omega
    have hspec := fastTauTop_spec primesLe448_prime primesLe448_nodup primesLe448_cov
      hk0 (by omega : k < 2 ^ 18) (by omega : k < 448 * 448)
    rw [hspec.1] at h1
    exact ⟨h1.1, h1.2.1, hk0, by omega, Nat.dvd_of_mod_eq_zero h1.2.2, hspec.2⟩
  refine ⟨hklo, hkhi, hnd, fun k hk => ⟨(hmem k hk).1, (hmem k hk).2.1, (hmem k hk).2.2.1,
    (hmem k hk).2.2.2.1, (hmem k hk).2.2.2.2.1⟩, ?_, ?_⟩
  · rw [← hS]
    exact list_harmonic_le hnd (fun k hk => (hmem k hk).2.2.1)
  · rw [← hE]
    have hsum_nat : ∑ k ∈ ks.toFinset, (k.primeFactors.sup id).primeCounting ≤
        (ks.map (fun k => piHiTblFast (fastTauTop 18 primesLe448 k).2)).sum := by
      have haux : ∀ (L : List Nat), L.Nodup →
          (∀ k ∈ L, 0 < k ∧ k ≤ 200000 ∧ (fastTauTop 18 primesLe448 k).2 = k.primeFactors.sup id) →
          ∑ k ∈ L.toFinset, (k.primeFactors.sup id).primeCounting ≤
            (L.map (fun k => piHiTblFast (fastTauTop 18 primesLe448 k).2)).sum := by
        intro L
        induction L with
        | nil => intros; simp
        | cons x xs ih =>
          intro hnd' hp'
          obtain ⟨hx, hnd''⟩ := List.nodup_cons.mp hnd'
          obtain ⟨hx0, hx200, hxtop⟩ := hp' x (by simp)
          simp only [List.toFinset_cons, List.map_cons, List.sum_cons]
          rw [Finset.sum_insert (by simp [hx])]
          have htop_le : x.primeFactors.sup id ≤ 14090240 := by
            have : x.primeFactors.sup id ≤ x := by
              apply Finset.sup_le; intro p hp
              exact Nat.le_of_dvd hx0 (Nat.dvd_of_mem_primeFactors hp)
            omega
          have h1 : (x.primeFactors.sup id).primeCounting ≤ piHiTblFast (fastTauTop 18 primesLe448 x).2 := by
            rw [hxtop]; exact le_piHiTblFast htop_le
          exact Nat.add_le_add h1 (ih hnd'' (fun k hk => hp' k (List.mem_cons_of_mem _ hk)))
      exact haux ks hnd (fun k hk => ⟨(hmem k hk).2.2.1, (hmem k hk).2.2.2.1, (hmem k hk).2.2.2.2.2⟩)
    exact_mod_cast hsum_nat

private lemma g1BucketTerm_sound {Na Nb n klo khi S_i E_i : Nat} {ks : List Nat}
    (hchk : checkG1Bucket klo khi S_i E_i ks = true)
    (hNa : 10000000 ≤ Na) (hn1 : Na ≤ n) (hn2 : n ≤ Nb) :
    (g1BucketTerm Na Nb klo khi S_i E_i : ℝ) / ratioScale ≤
      2 * (f1Count n ks.toFinset : ℝ) / ((n : ℝ) / Real.log n) := by
  have hW_pos : (0 : ℝ) < ratioScale := by norm_num [ratioScale]
  have hS_pos : (0 : ℝ) < logScale := by norm_num [logScale]
  have hH_pos : (0 : ℝ) < harmScale := by norm_num [harmScale]
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hdenom_pos : 0 < (n : ℝ) / Real.log n := div_pos hn_pos hlogn_pos
  have hrhs_nn : 0 ≤ 2 * (f1Count n ks.toFinset : ℝ) / ((n : ℝ) / Real.log n) := by positivity
  unfold g1BucketTerm
  dsimp only
  split_ifs with hlt hsieve
  · simp; exact hrhs_nn
  · -- Sieve mode: 2000 * khi ≤ Na ∧ Nb ≤ 10000000 * klo
    obtain ⟨hklo, hkhi, _, hmem, hharm, hE⟩ := g1Bucket_valid_props hchk
    obtain ⟨hs1, hs2⟩ := hsieve
    by_cases hke : ks = []
    · subst hke
      have hS0 : S_i = 0 := by
        unfold checkG1Bucket at hchk
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.map_nil, List.sum_nil] at hchk
        exact hchk.1.2.symm
      simp [hS0]; exact hrhs_nn
    obtain ⟨k0, hk0⟩ := List.exists_mem_of_ne_nil ks hke
    have hklo_le_khi : klo ≤ khi := (hmem k0 hk0).1.trans (hmem k0 hk0).2.1
    have hnb_klo : 2000 ≤ Nb / klo := by
      have : 2000 * klo ≤ Nb := by nlinarith
      exact (Nat.le_div_iff_mul_le hklo).mpr (by linarith)
    have hlb_lo := (logRatBounds_correct (a := Nb) (b := 1) le_rfl (by omega)).1
    simp only [Nat.cast_one, div_one] at hlb_lo
    have hla_hi := (logRatBounds_correct (a := Na) (b := 1) le_rfl (by omega)).2
    simp only [Nat.cast_one, div_one] at hla_hi
    have hlnk_hi := (logRatBounds_correct (a := Nb) (b := klo) hklo (by nlinarith)).2
    have hlog_ge2 : (2 : ℝ) < Real.log ((Nb : ℝ) / klo) := by
      have h2000 : (8 : ℝ) ≤ (Nb : ℝ) / klo := by
        rw [le_div_iff₀ (by exact_mod_cast hklo)]
        have : 8 * klo ≤ Nb := by
          have : klo ≤ Nb / 2000 := by
            have := Nat.div_le_div_right (show 2000 * klo ≤ Nb by
              by_cases hke : ks = []
              · omega
              · obtain ⟨k0, hk0⟩ := List.exists_mem_of_ne_nil ks hke
                have := hmem k0 hk0; nlinarith) (c := 2000)
            omega
          omega
        exact_mod_cast this
      have hlog8 : Real.log 8 = 3 * Real.log 2 := by
        rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; push_cast; ring
      have := Real.log_two_gt_d9
      have := Real.log_le_log (by norm_num : (0 : ℝ) < 8) h2000
      linarith
    have hlnk_gt_S : logScale < logRatHi Nb klo := by
      have h1 : (2 : ℝ) < (logRatHi Nb klo : ℝ) / logScale := lt_of_lt_of_le hlog_ge2 hlnk_hi
      have h2 : (2 : ℝ) * logScale < logRatHi Nb klo := (lt_div_iff₀ hS_pos).mp h1
      have h3 : 2 * logScale < logRatHi Nb klo := by exact_mod_cast h2
      omega
    have hlb_lo' : (logNatLo Nb : ℝ) / logScale ≤ Real.log Nb := hlb_lo
    have hla_hi' : Real.log Na ≤ (logNatHi Na : ℝ) / logScale := hla_hi
    clear hlb_lo hla_hi
    generalize hlb_eq : logNatLo Nb = lb at hlb_lo' ⊢
    generalize hla_eq : logNatHi Na = la at hla_hi' ⊢
    generalize hlnk_eq : logRatHi Nb klo = lnk at hlnk_hi hlnk_gt_S ⊢
    clear hlb_eq hla_eq hlnk_eq
    generalize hldiff_eq : lnk - logScale = ldiff
    have hldiff_pos : 0 < ldiff := by omega
    have hldiffR_pos : (0 : ℝ) < ldiff := Nat.cast_pos.mpr hldiff_pos
    have hsub_cast : (ldiff : ℝ) / logScale = (lnk : ℝ) / logScale - 1 := by
      rw [← hldiff_eq, Nat.cast_sub (by omega), sub_div, div_self hS_pos.ne']
    clear hldiff_eq
    have hratio_nn : (0 : ℝ) ≤ (lb : ℝ) / (ldiff : ℝ) := div_nonneg (Nat.cast_nonneg _) hldiffR_pos.le
    -- Step 1: lower bound f1Count
    have hf1_ge : ∑ k ∈ ks.toFinset, (((n / k).primeCounting : ℝ) - ((k.primeFactors.sup id).primeCounting : ℝ)) ≤
        (f1Count n ks.toFinset : ℝ) := by
      unfold f1Count
      push_cast
      exact Finset.sum_le_sum fun k _ => nat_sub_cast_ge _ _
    rw [Finset.sum_sub_distrib] at hf1_ge
    -- Step 2: lower bound each (n/k).primeCounting using pi_lower_sieve_2000_10M
    have hsum_pi : 0.990 * ((n : ℝ) / Real.log n) * ((lb : ℝ) / (ldiff : ℝ)) *
        ((S_i : ℝ) / harmScale) ≤ ∑ k ∈ ks.toFinset, ((n / k).primeCounting : ℝ) := by
      have hterm : ∀ k ∈ ks.toFinset,
          0.990 * ((n : ℝ) / Real.log n) * ((lb : ℝ) / (ldiff : ℝ)) *
            ((1 : ℝ) / k) ≤ ((n / k).primeCounting : ℝ) := by
        intro k hk
        obtain ⟨hk1, hk2, hk0, _, _⟩ := hmem k (List.mem_toFinset.mp hk)
        have hkR_pos : (0 : ℝ) < k := by exact_mod_cast hk0
        have hxk_lo : (2000 : ℝ) ≤ (n : ℝ) / k := by
          rw [le_div_iff₀ hkR_pos]
          exact_mod_cast (show 2000 * k ≤ n by
            exact (Nat.mul_le_mul_left 2000 hk2).trans (hs1.trans hn1))
        have hxk_hi : (n : ℝ) / k ≤ (10 ^ 7 : ℝ) := by
          rw [div_le_iff₀ hkR_pos]
          have : n ≤ 10000000 * k := hn2.trans (hs2.trans (Nat.mul_le_mul_left 10000000 hk1))
          have hR : (n : ℝ) ≤ 10000000 * (k : ℝ) := by exact_mod_cast this
          norm_num; linarith
        have hpi := pi_lower_sieve_2000_10M hxk_lo hxk_hi
        rw [floor_nat_div_eq] at hpi
        have hlog_nk_gt1 : 1 < Real.log ((n : ℝ) / k) := by
          have : Real.log 2000 ≤ Real.log ((n : ℝ) / k) := Real.log_le_log (by norm_num) hxk_lo
          have h3 : (3 : ℝ) ≤ 2000 := by norm_num
          have := Real.log_three_gt_d9
          have := Real.log_le_log (by norm_num : (0 : ℝ) < 3) h3
          linarith
        have hkloR_pos : (0 : ℝ) < klo := Nat.cast_pos.mpr hklo
        have hk1R : (klo : ℝ) ≤ k := Nat.cast_le.mpr hk1
        have hnk_pos : (0 : ℝ) < (n : ℝ) / k := div_pos hn_pos hkR_pos
        have hlog_nklo_gt1 : 1 < Real.log ((n : ℝ) / klo) :=
          lt_of_lt_of_le hlog_nk_gt1 (Real.log_le_log hnk_pos
            (div_le_div_of_nonneg_left hn_pos.le hkloR_pos hk1R))
        have hanti := log_div_log_div_sub_one_antitone (c := (klo : ℝ)) (a := (n : ℝ)) (b := (Nb : ℝ))
          (by exact_mod_cast hklo) hn_pos hlog_nklo_gt1 (by exact_mod_cast hn2)
        have hmono_k : Real.log n / (Real.log ((n : ℝ) / klo) - 1) ≤ Real.log n / (Real.log ((n : ℝ) / k) - 1) := by
          apply div_le_div_of_nonneg_left hlogn_pos.le (by linarith)
          linarith [Real.log_le_log hnk_pos
            (div_le_div_of_nonneg_left hn_pos.le hkloR_pos hk1R)]
        have hratio_ge : (lb : ℝ) / (ldiff : ℝ) ≤
            Real.log Nb / (Real.log ((Nb : ℝ) / klo) - 1) := by
          have hden_le : Real.log ((Nb : ℝ) / klo) - 1 ≤ (ldiff : ℝ) / logScale := by linarith
          have h1 : (lb : ℝ) / (ldiff : ℝ) = ((lb : ℝ) / logScale) / ((ldiff : ℝ) / logScale) := by
            have hSne := hS_pos.ne'
            have hne := hldiffR_pos.ne'
            field_simp
          rw [h1]
          calc ((lb : ℝ) / logScale) / ((ldiff : ℝ) / logScale)
              ≤ Real.log Nb / ((ldiff : ℝ) / logScale) :=
                div_le_div_of_nonneg_right hlb_lo' (div_pos hldiffR_pos hS_pos).le
            _ ≤ Real.log Nb / (Real.log ((Nb : ℝ) / klo) - 1) :=
                div_le_div_of_nonneg_left (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Nb by omega)))
                  (by linarith) hden_le
        have hcomb : (lb : ℝ) / (ldiff : ℝ) ≤ Real.log n / (Real.log ((n : ℝ) / k) - 1) :=
          hratio_ge.trans (hanti.trans hmono_k)
        have hrew : 0.990 * ((n : ℝ) / Real.log n) * (Real.log n / (Real.log ((n : ℝ) / k) - 1)) * ((1 : ℝ) / k) =
            0.990 * (((n : ℝ) / k) / (Real.log ((n : ℝ) / k) - 1)) := by
          have hne1 := hlogn_pos.ne'
          have hne2 : Real.log ((n : ℝ) / k) - 1 ≠ 0 := by linarith
          have hne3 := hkR_pos.ne'
          field_simp
        calc 0.990 * ((n : ℝ) / Real.log n) * ((lb : ℝ) / (ldiff : ℝ)) * ((1 : ℝ) / k)
            ≤ 0.990 * ((n : ℝ) / Real.log n) * (Real.log n / (Real.log ((n : ℝ) / k) - 1)) * ((1 : ℝ) / k) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hcomb (mul_nonneg (by norm_num) hdenom_pos.le))
                (div_nonneg (by norm_num) hkR_pos.le)
          _ = 0.990 * (((n : ℝ) / k) / (Real.log ((n : ℝ) / k) - 1)) := hrew
          _ ≤ ((n / k).primeCounting : ℝ) := hpi
      calc _ ≤ 0.990 * ((n : ℝ) / Real.log n) * ((lb : ℝ) / (ldiff : ℝ)) *
              ∑ k ∈ ks.toFinset, (1 : ℝ) / k := by
            exact mul_le_mul_of_nonneg_left hharm (mul_nonneg (mul_nonneg (by norm_num) hdenom_pos.le) hratio_nn)
        _ = ∑ k ∈ ks.toFinset, (0.990 * ((n : ℝ) / Real.log n) *
              ((lb : ℝ) / (ldiff : ℝ)) * ((1 : ℝ) / k)) := by
            rw [Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum hterm
    -- Step 3: combine main and err bounds!
    apply (div_le_iff₀ hW_pos).mpr
    apply nat_sub_cast_le_of_le (mul_nonneg hrhs_nn hW_pos.le)
    have hmain_le : (((2 * 990 * ratioScale * S_i * lb) / (1000 * harmScale * ldiff) : Nat) : ℝ) ≤
        2 * 0.990 * ((lb : ℝ) / (ldiff : ℝ)) * ((S_i : ℝ) / harmScale) * ratioScale := by
      have hdiv := nat_div_cast_le (a := 2 * 990 * ratioScale * S_i * lb)
        (b := 1000 * harmScale * ldiff) (Nat.mul_pos (by decide) hldiff_pos)
      have heq : ((2 * 990 * ratioScale * S_i * lb : Nat) : ℝ) /
          ((1000 * harmScale * ldiff : Nat) : ℝ) =
          2 * 0.990 * ((lb : ℝ) / (ldiff : ℝ)) * ((S_i : ℝ) / harmScale) * ratioScale := by
        have hne1 := hH_pos.ne'
        have hne2 := hldiffR_pos.ne'
        push_cast; field_simp; ring
      linarith
    have herr_ge : 2 * (E_i : ℝ) / ((n : ℝ) / Real.log n) * ratioScale ≤
        ((ceilDiv (2 * ratioScale * E_i * la) (logScale * Na) : Nat) : ℝ) := by
      have hceil := ceilDiv_cast_ge (a := 2 * ratioScale * E_i * la)
        (b := logScale * Na) (Nat.mul_pos (by decide) (by omega))
      have hanti := log_div_self_antitone (a := (Na : ℝ)) (b := (n : ℝ))
        (by exact_mod_cast (show 3 ≤ Na by omega)) (by exact_mod_cast hn1)
      have h1 : 2 * (E_i : ℝ) / ((n : ℝ) / Real.log n) * ratioScale =
          2 * (ratioScale : ℝ) * E_i * (Real.log n / n) := by field_simp
      have h2 : 2 * (ratioScale : ℝ) * E_i * (Real.log n / n) ≤
          2 * (ratioScale : ℝ) * E_i * ((la : ℝ) / logScale / Na) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (by norm_num) hW_pos.le) (Nat.cast_nonneg _))
        exact hanti.trans (div_le_div_of_nonneg_right hla_hi' (Nat.cast_nonneg _))
      have h3 : 2 * (ratioScale : ℝ) * E_i * ((la : ℝ) / logScale / Na) =
          ((2 * ratioScale * E_i * la : Nat) : ℝ) / ((logScale * Na : Nat) : ℝ) := by
        have hne1 := hS_pos.ne'
        have hne2 : (Na : ℝ) ≠ 0 := (by exact_mod_cast (show 0 < Na by omega) : (0 : ℝ) < Na).ne'
        push_cast; field_simp
      linarith
    have hdiv_all : 2 * 0.990 * ((lb : ℝ) / (ldiff : ℝ)) * ((S_i : ℝ) / harmScale) -
        2 * (E_i : ℝ) / ((n : ℝ) / Real.log n) ≤
        2 * (f1Count n ks.toFinset : ℝ) / ((n : ℝ) / Real.log n) := by
      have h1 : 2 * (0.990 * ((n : ℝ) / Real.log n) * ((lb : ℝ) / (ldiff : ℝ)) *
          ((S_i : ℝ) / harmScale) - E_i) ≤ 2 * (f1Count n ks.toFinset : ℝ) := by linarith
      have h2 := div_le_div_of_nonneg_right h1 hdenom_pos.le
      have heq : 2 * (0.990 * ((n : ℝ) / Real.log n) * ((lb : ℝ) / (ldiff : ℝ)) *
          ((S_i : ℝ) / harmScale) - E_i) / ((n : ℝ) / Real.log n) =
          2 * 0.990 * ((lb : ℝ) / (ldiff : ℝ)) * ((S_i : ℝ) / harmScale) -
            2 * (E_i : ℝ) / ((n : ℝ) / Real.log n) := by
        have hne1 := hn_pos.ne'
        have hne2 := hlogn_pos.ne'
        field_simp
      linarith
    have hmul_all := mul_le_mul_of_nonneg_right hdiv_all hW_pos.le
    rw [sub_mul] at hmul_all
    linarith
  · -- Standard mode: 101 * khi ≤ Na
    obtain ⟨hklo, hkhi, _, hmem, hharm, hE⟩ := g1Bucket_valid_props hchk
    by_cases hke : ks = []
    · subst hke
      have hS0 : S_i = 0 := by
        unfold checkG1Bucket at hchk
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.map_nil, List.sum_nil] at hchk
        exact hchk.1.2.symm
      simp [hS0]; exact hrhs_nn
    obtain ⟨k0, hk0⟩ := List.exists_mem_of_ne_nil ks hke
    have hklo_le_khi : klo ≤ khi := (hmem k0 hk0).1.trans (hmem k0 hk0).2.1
    have hlb_lo := (logRatBounds_correct (a := Nb) (b := 1) le_rfl (by omega)).1
    simp only [Nat.cast_one, div_one] at hlb_lo
    have hla_hi := (logRatBounds_correct (a := Na) (b := 1) le_rfl (by omega)).2
    simp only [Nat.cast_one, div_one] at hla_hi
    have hlnk_hi := (logRatBounds_correct (a := Nb) (b := klo) hklo (by nlinarith)).2
    have hlnk_pos : 0 < logRatHi Nb klo := by
      have h1 : (0 : ℝ) < Real.log ((Nb : ℝ) / klo) :=
        Real.log_pos ((one_lt_div (by exact_mod_cast hklo)).mpr (by exact_mod_cast (show klo < Nb by nlinarith)))
      have h2 : (0 : ℝ) < (logRatHi Nb klo : ℝ) / logScale := lt_of_lt_of_le h1 hlnk_hi
      have h3 : (0 : ℝ) < logRatHi Nb klo := (div_pos_iff_of_pos_right hS_pos).mp h2
      exact_mod_cast h3
    have hlb_lo' : (logNatLo Nb : ℝ) / logScale ≤ Real.log Nb := hlb_lo
    have hla_hi' : Real.log Na ≤ (logNatHi Na : ℝ) / logScale := hla_hi
    clear hlb_lo hla_hi
    generalize hlb_eq : logNatLo Nb = lb at hlb_lo' ⊢
    generalize hla_eq : logNatHi Na = la at hla_hi' ⊢
    generalize hlnk_eq : logRatHi Nb klo = lnk at hlnk_hi hlnk_pos ⊢
    clear hlb_eq hla_eq hlnk_eq
    have hlnkR_pos : (0 : ℝ) < lnk := Nat.cast_pos.mpr hlnk_pos
    have hfac_nn : (0 : ℝ) ≤ (lb : ℝ) * ((lnk : ℝ) + logScale) / ((lnk : ℝ) ^ 2) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hlnkR_pos.le hS_pos.le)) (sq_nonneg _)
    have hf1_ge : ∑ k ∈ ks.toFinset, (((n / k).primeCounting : ℝ) - ((k.primeFactors.sup id).primeCounting : ℝ)) ≤
        (f1Count n ks.toFinset : ℝ) := by
      unfold f1Count; push_cast
      exact Finset.sum_le_sum fun k _ => nat_sub_cast_ge _ _
    rw [Finset.sum_sub_distrib] at hf1_ge
    have hsum_pi : 0.9400 * ((n : ℝ) / Real.log n) *
        ((lb : ℝ) * ((lnk : ℝ) + logScale) / ((lnk : ℝ) ^ 2)) *
        ((S_i : ℝ) / harmScale) ≤ ∑ k ∈ ks.toFinset, ((n / k).primeCounting : ℝ) := by
      have hterm : ∀ k ∈ ks.toFinset,
          0.9400 * ((n : ℝ) / Real.log n) *
            ((lb : ℝ) * ((lnk : ℝ) + logScale) / ((lnk : ℝ) ^ 2)) *
            ((1 : ℝ) / k) ≤ ((n / k).primeCounting : ℝ) := by
        intro k hk
        obtain ⟨hk1, hk2, hk0, _, _⟩ := hmem k (List.mem_toFinset.mp hk)
        have hkR_pos : (0 : ℝ) < k := by exact_mod_cast hk0
        have hxk_lo : (101 : ℝ) ≤ (n : ℝ) / k := by
          rw [le_div_iff₀ hkR_pos]
          exact_mod_cast (show 101 * k ≤ n by
            exact (Nat.mul_le_mul_left 101 hk2).trans ((show 101 * khi ≤ Na by omega).trans hn1))
        have hpi := pi_lower_all hxk_lo
        rw [floor_nat_div_eq] at hpi
        have hnk_pos : (0 : ℝ) < (n : ℝ) / k := div_pos hn_pos hkR_pos
        have hlog_nk_pos : 0 < Real.log ((n : ℝ) / k) := Real.log_pos (by linarith)
        have hlog_nk_le : Real.log ((n : ℝ) / k) ≤ Real.log ((Nb : ℝ) / klo) := by
          apply Real.log_le_log hnk_pos
          exact div_le_div₀ (Nat.cast_nonneg _) (by exact_mod_cast hn2) (by exact_mod_cast hklo) (by exact_mod_cast hk1)
        have hanti := log_div_log_div_antitone (c := (klo : ℝ)) (a := (n : ℝ)) (b := (Nb : ℝ))
          (by exact_mod_cast hklo) (by exact_mod_cast (show klo < n by nlinarith)) (by exact_mod_cast hn2)
        have hmono_k : Real.log n / Real.log ((n : ℝ) / klo) ≤ Real.log n / Real.log ((n : ℝ) / k) := by
          apply div_le_div_of_nonneg_left hlogn_pos.le hlog_nk_pos
          exact Real.log_le_log hnk_pos
            (div_le_div_of_nonneg_left hn_pos.le (by exact_mod_cast hklo) (by exact_mod_cast hk1))
        have hlog_nbklo_pos : 0 < Real.log ((Nb : ℝ) / klo) := lt_of_lt_of_le hlog_nk_pos hlog_nk_le
        have hrat1 : (lb : ℝ) / (lnk : ℝ) ≤ Real.log n / Real.log ((n : ℝ) / k) := by
          have h1 : (lb : ℝ) / (lnk : ℝ) = ((lb : ℝ) / logScale) / ((lnk : ℝ) / logScale) := by
            have hne1 := hS_pos.ne'; have hne2 := hlnkR_pos.ne'; field_simp
          have h2 : ((lb : ℝ) / logScale) / ((lnk : ℝ) / logScale) ≤
              Real.log Nb / Real.log ((Nb : ℝ) / klo) := by
            calc _ ≤ Real.log Nb / ((lnk : ℝ) / logScale) :=
                  div_le_div_of_nonneg_right hlb_lo' (div_pos hlnkR_pos hS_pos).le
              _ ≤ Real.log Nb / Real.log ((Nb : ℝ) / klo) :=
                  div_le_div_of_nonneg_left (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Nb by omega)))
                    hlog_nbklo_pos hlnk_hi
          exact h1.le.trans (h2.trans (hanti.trans hmono_k))
        have hrat2 : ((lnk : ℝ) + logScale) / (lnk : ℝ) ≤ 1 + 1 / Real.log ((n : ℝ) / k) := by
          have h1 : ((lnk : ℝ) + logScale) / (lnk : ℝ) = 1 + 1 / ((lnk : ℝ) / logScale) := by
            have hne1 := hlnkR_pos.ne'; have hne2 := hS_pos.ne'; field_simp
          rw [h1]
          exact add_le_add le_rfl (div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num) hlog_nk_pos (hlog_nk_le.trans hlnk_hi))
        have hmul_rat : (lb : ℝ) * ((lnk : ℝ) + logScale) / ((lnk : ℝ) ^ 2) ≤
            (Real.log n / Real.log ((n : ℝ) / k)) * (1 + 1 / Real.log ((n : ℝ) / k)) := by
          have heq : (lb : ℝ) * ((lnk : ℝ) + logScale) / ((lnk : ℝ) ^ 2) =
              ((lb : ℝ) / (lnk : ℝ)) * (((lnk : ℝ) + logScale) / (lnk : ℝ)) := by ring
          rw [heq]
          exact mul_le_mul hrat1 hrat2
            (div_nonneg (add_nonneg hlnkR_pos.le hS_pos.le) hlnkR_pos.le)
            (div_nonneg hlogn_pos.le hlog_nk_pos.le)
        have hrew : 0.9400 * ((n : ℝ) / Real.log n) *
            ((Real.log n / Real.log ((n : ℝ) / k)) * (1 + 1 / Real.log ((n : ℝ) / k))) * ((1 : ℝ) / k) =
            0.9400 * (((n : ℝ) / k) / Real.log ((n : ℝ) / k) + ((n : ℝ) / k) / (Real.log ((n : ℝ) / k)) ^ 2) := by
          have hne1 := hlogn_pos.ne'; have hne2 := hlog_nk_pos.ne'; have hne3 := hkR_pos.ne'
          field_simp
        calc _ ≤ 0.9400 * ((n : ℝ) / Real.log n) *
              ((Real.log n / Real.log ((n : ℝ) / k)) * (1 + 1 / Real.log ((n : ℝ) / k))) * ((1 : ℝ) / k) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left hmul_rat (mul_nonneg (by norm_num) hdenom_pos.le))
                (div_nonneg (by norm_num) hkR_pos.le)
          _ = _ := hrew
          _ ≤ ((n / k).primeCounting : ℝ) := hpi
      calc _ ≤ 0.9400 * ((n : ℝ) / Real.log n) *
              ((lb : ℝ) * ((lnk : ℝ) + logScale) / ((lnk : ℝ) ^ 2)) *
              ∑ k ∈ ks.toFinset, (1 : ℝ) / k := by
            exact mul_le_mul_of_nonneg_left hharm (mul_nonneg (mul_nonneg (by norm_num) hdenom_pos.le) hfac_nn)
        _ = ∑ k ∈ ks.toFinset, (0.9400 * ((n : ℝ) / Real.log n) *
              ((lb : ℝ) * ((lnk : ℝ) + logScale) / ((lnk : ℝ) ^ 2)) *
              ((1 : ℝ) / k)) := by rw [Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum hterm
    apply (div_le_iff₀ hW_pos).mpr
    apply nat_sub_cast_le_of_le (mul_nonneg hrhs_nn hW_pos.le)
    have hmain_le : (((2 * 9400 * ratioScale * S_i * lb * (lnk + logScale)) /
          (10000 * harmScale * lnk * lnk) : Nat) : ℝ) ≤
        2 * 0.9400 * ((lb : ℝ) * ((lnk : ℝ) + logScale) / ((lnk : ℝ) ^ 2)) *
          ((S_i : ℝ) / harmScale) * ratioScale := by
      have hdiv := nat_div_cast_le (a := 2 * 9400 * ratioScale * S_i * lb * (lnk + logScale))
        (b := 10000 * harmScale * lnk * lnk)
        (Nat.mul_pos (Nat.mul_pos (by decide) hlnk_pos) hlnk_pos)
      have heq : ((2 * 9400 * ratioScale * S_i * lb * (lnk + logScale) : Nat) : ℝ) /
          ((10000 * harmScale * lnk * lnk : Nat) : ℝ) =
          2 * 0.9400 * ((lb : ℝ) * ((lnk : ℝ) + logScale) / ((lnk : ℝ) ^ 2)) *
            ((S_i : ℝ) / harmScale) * ratioScale := by
        have hne1 := hH_pos.ne'; have hne2 := hlnkR_pos.ne'
        push_cast; field_simp; ring
      linarith
    have herr_ge : 2 * (E_i : ℝ) / ((n : ℝ) / Real.log n) * ratioScale ≤
        ((ceilDiv (2 * ratioScale * E_i * la) (logScale * Na) : Nat) : ℝ) := by
      have hceil := ceilDiv_cast_ge (a := 2 * ratioScale * E_i * la)
        (b := logScale * Na) (Nat.mul_pos (by decide) (by omega))
      have hanti := log_div_self_antitone (a := (Na : ℝ)) (b := (n : ℝ))
        (by exact_mod_cast (show 3 ≤ Na by omega)) (by exact_mod_cast hn1)
      have h1 : 2 * (E_i : ℝ) / ((n : ℝ) / Real.log n) * ratioScale =
          2 * (ratioScale : ℝ) * E_i * (Real.log n / n) := by field_simp
      have h2 : 2 * (ratioScale : ℝ) * E_i * (Real.log n / n) ≤
          2 * (ratioScale : ℝ) * E_i * ((la : ℝ) / logScale / Na) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (by norm_num) hW_pos.le) (Nat.cast_nonneg _))
        exact hanti.trans (div_le_div_of_nonneg_right hla_hi' (Nat.cast_nonneg _))
      have h3 : 2 * (ratioScale : ℝ) * E_i * ((la : ℝ) / logScale / Na) =
          ((2 * ratioScale * E_i * la : Nat) : ℝ) / ((logScale * Na : Nat) : ℝ) := by
        have hne1 := hS_pos.ne'
        have hne2 : (Na : ℝ) ≠ 0 := (by exact_mod_cast (show 0 < Na by omega) : (0 : ℝ) < Na).ne'
        push_cast; field_simp
      linarith
    have hdiv_all : 2 * 0.9400 * ((lb : ℝ) * ((lnk : ℝ) + logScale) / ((lnk : ℝ) ^ 2)) *
        ((S_i : ℝ) / harmScale) - 2 * (E_i : ℝ) / ((n : ℝ) / Real.log n) ≤
        2 * (f1Count n ks.toFinset : ℝ) / ((n : ℝ) / Real.log n) := by
      have h1 : 2 * (0.9400 * ((n : ℝ) / Real.log n) *
          ((lb : ℝ) * ((lnk : ℝ) + logScale) / ((lnk : ℝ) ^ 2)) *
          ((S_i : ℝ) / harmScale) - E_i) ≤ 2 * (f1Count n ks.toFinset : ℝ) := by linarith
      have h2 := div_le_div_of_nonneg_right h1 hdenom_pos.le
      have heq : 2 * (0.9400 * ((n : ℝ) / Real.log n) *
          ((lb : ℝ) * ((lnk : ℝ) + logScale) / ((lnk : ℝ) ^ 2)) *
          ((S_i : ℝ) / harmScale) - E_i) / ((n : ℝ) / Real.log n) =
          2 * 0.9400 * ((lb : ℝ) * ((lnk : ℝ) + logScale) / ((lnk : ℝ) ^ 2)) *
            ((S_i : ℝ) / harmScale) - 2 * (E_i : ℝ) / ((n : ℝ) / Real.log n) := by
        have hne1 := hn_pos.ne'; have hne2 := hlogn_pos.ne'
        field_simp
      linarith
    have hmul_all := mul_le_mul_of_nonneg_right hdiv_all hW_pos.le
    rw [sub_mul] at hmul_all
    linarith

private lemma g4PiUHi_sound {U : Nat} (hU : 1 ≤ U) : (U.primeCounting : ℝ) ≤ (g4PiUHi U : ℝ) := by
  unfold g4PiUHi
  split_ifs with hle
  · exact_mod_cast le_piHiTblFast hle
  · push Not at hle
    have h10M : (10 ^ 7 : ℝ) ≤ U := by
      have : (10000000 : ℝ) ≤ U := by exact_mod_cast (show 10000000 ≤ U by omega)
      norm_num; linarith
    have hpi := pi_upper_10M_full h10M
    rw [Nat.floor_natCast] at hpi
    have hlu_lo := (logRatBounds_correct (a := U) (b := 1) le_rfl hU).1
    simp only [Nat.cast_one, div_one] at hlu_lo
    have hlu_pos : 0 < logNatLo U := logNatLo_pos (by omega)
    have hS_pos : (0 : ℝ) < logScale := by norm_num [logScale]
    have hluR_pos : (0 : ℝ) < (logNatLo U : ℝ) / logScale := by positivity
    have h1 : (U : ℝ) / Real.log U ≤ (U : ℝ) / ((logNatLo U : ℝ) / logScale) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg U) hluR_pos hlu_lo
    have h2 : (U : ℝ) / (Real.log U) ^ 2 ≤ (U : ℝ) / ((logNatLo U : ℝ) / logScale) ^ 2 :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg U) (by positivity) (pow_le_pow_left₀ hluR_pos.le hlu_lo 2)
    have h3 : 3 * (U : ℝ) / (Real.log U) ^ 3 ≤ 3 * (U : ℝ) / ((logNatLo U : ℝ) / logScale) ^ 3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hluR_pos.le hlu_lo 3)
    have hceil := ceilDiv_cast_ge
      (a := 10562 * U * logScale * (logNatLo U * logNatLo U + logNatLo U * logScale + 3 * logScale * logScale))
      (b := 10000 * logNatLo U * logNatLo U * logNatLo U) (by positivity)
    have halg : 1.0562 * ((U : ℝ) / ((logNatLo U : ℝ) / logScale) +
        (U : ℝ) / ((logNatLo U : ℝ) / logScale) ^ 2 + 3 * (U : ℝ) / ((logNatLo U : ℝ) / logScale) ^ 3) =
        ((10562 * U * logScale * (logNatLo U * logNatLo U + logNatLo U * logScale + 3 * logScale * logScale) : Nat) : ℝ) /
          ((10000 * logNatLo U * logNatLo U * logNatLo U : Nat) : ℝ) := by
      have hne1 : (logNatLo U : ℝ) ≠ 0 := (by exact_mod_cast hlu_pos : (0 : ℝ) < logNatLo U).ne'
      have hne2 : (logScale : ℝ) ≠ 0 := hS_pos.ne'
      push_cast; field_simp; ring
    linarith

private lemma g4HpLo_sound {L piL U : Nat} (hL : 100 ≤ L) (hLU : L < U) (hpiL : piL = L.primeCounting) :
    (g4HpLo L piL U : ℝ) / ratioScale ≤ ∑ p ∈ (Ioc L U).filter Nat.Prime, (1 : ℝ) / p := by
  have hW_pos : (0 : ℝ) < ratioScale := by norm_num [ratioScale]
  have hS_pos : (0 : ℝ) < logScale := by norm_num [logScale]
  have hsum_nn : 0 ≤ ∑ p ∈ (Ioc L U).filter Nat.Prime, (1 : ℝ) / p := Finset.sum_nonneg fun _ _ => by positivity
  unfold g4HpLo
  dsimp only
  split_ifs with hle
  · rw [Nat.cast_zero, zero_div]; exact hsum_nn
  · push Not at hle
    have habel := sum_inv_primes_lower (fun m hm => pi_lower_nat hm) hL hLU
    have hpiU := pi_lower_nat (by omega : 101 ≤ U)
    have hU_pos : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
    have hpiU_div : 0.9400 * (1 / Real.log U + 1 / (Real.log U) ^ 2) ≤ (U.primeCounting : ℝ) / U := by
      have h1 := div_le_div_of_nonneg_right hpiU hU_pos.le
      have heq : 0.9400 * ((U : ℝ) / Real.log U + (U : ℝ) / (Real.log U) ^ 2) / U =
          0.9400 * (1 / Real.log U + 1 / (Real.log U) ^ 2) := by field_simp
      linarith
    obtain ⟨hlu_lo, hlu_hi⟩ := logRatBounds_correct (a := U) (b := 1) le_rfl (by omega)
    simp only [Nat.cast_one, div_one] at hlu_lo hlu_hi
    have hlL1_hi := (logRatBounds_correct (a := L + 1) (b := 1) le_rfl (by omega)).2
    simp only [Nat.cast_one, div_one] at hlL1_hi
    have hlu_pos : 0 < logNatLo U := logNatLo_pos (by omega)
    have hlu_hi_pos : 0 < logNatHi U := by
      have h1 : (0 : ℝ) < Real.log U := Real.log_pos (by exact_mod_cast (show 1 < U by omega))
      have h2 : (0 : ℝ) < (logNatHi U : ℝ) / logScale := lt_of_lt_of_le h1 hlu_hi
      exact_mod_cast ((div_pos_iff_of_pos_right hS_pos).mp h2)
    have hlL1_pos : 0 < logNatHi (L + 1) := by
      have h1 : (0 : ℝ) < Real.log ((L + 1 : Nat) : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < L + 1 by omega))
      have h2 : (0 : ℝ) < (logNatHi (L + 1) : ℝ) / logScale := lt_of_lt_of_le h1 hlL1_hi
      exact_mod_cast ((div_pos_iff_of_pos_right hS_pos).mp h2)
    have hll_lo := (logRatBounds_correct (a := logNatLo U) (b := logNatHi (L + 1)) hlL1_pos (by omega)).1
    have hlu_lo' : (logNatLo U : ℝ) / logScale ≤ Real.log U := hlu_lo
    have hlu_hi' : Real.log U ≤ (logNatHi U : ℝ) / logScale := hlu_hi
    have hlL1_hi' : Real.log ((L + 1 : Nat) : ℝ) ≤ (logNatHi (L + 1) : ℝ) / logScale := hlL1_hi
    clear hlu_lo hlu_hi hlL1_hi
    generalize h1eq : logNatLo U = lu_lo at hlu_lo' hlu_pos hll_lo hle ⊢
    generalize h2eq : logNatHi U = lu_hi at hlu_hi' hlu_hi_pos ⊢
    generalize h3eq : logNatHi (L + 1) = lL1_hi at hlL1_hi' hlL1_pos hll_lo hle ⊢
    generalize h4eq : logRatLo lu_lo lL1_hi = llog_lo at hll_lo ⊢
    clear h1eq h2eq h3eq h4eq
    have hluR_pos : (0 : ℝ) < lu_lo := Nat.cast_pos.mpr hlu_pos
    have hluHiR_pos : (0 : ℝ) < lu_hi := Nat.cast_pos.mpr hlu_hi_pos
    have hlL1R_pos : (0 : ℝ) < lL1_hi := Nat.cast_pos.mpr hlL1_pos
    have hlog_log_ge : (llog_lo : ℝ) / logScale ≤
        Real.log (Real.log U / Real.log ((L + 1 : Nat) : ℝ)) := by
      have hratio : (lu_lo : ℝ) / (lL1_hi : ℝ) ≤ Real.log U / Real.log ((L + 1 : Nat) : ℝ) := by
        have h1 : (lu_lo : ℝ) / (lL1_hi : ℝ) =
            ((lu_lo : ℝ) / logScale) / ((lL1_hi : ℝ) / logScale) := by
          have hne1 := hS_pos.ne'; have hne2 := hlL1R_pos.ne'; field_simp
        rw [h1]
        calc _ ≤ Real.log U / ((lL1_hi : ℝ) / logScale) :=
              div_le_div_of_nonneg_right hlu_lo' (div_pos hlL1R_pos hS_pos).le
          _ ≤ Real.log U / Real.log ((L + 1 : Nat) : ℝ) :=
              div_le_div_of_nonneg_left (Real.log_nonneg (by exact_mod_cast (show 1 ≤ U by omega)))
                (Real.log_pos (by exact_mod_cast (show 1 < L + 1 by omega))) hlL1_hi'
      exact hll_lo.trans (Real.log_le_log (div_pos hluR_pos hlL1R_pos) hratio)
    have htu : (((9400 * ratioScale * logScale * (lu_hi + logScale)) /
          (10000 * lu_hi * lu_hi) : Nat) : ℝ) / ratioScale ≤
        0.9400 * (1 / Real.log U + 1 / (Real.log U) ^ 2) := by
      have hdiv := nat_div_cast_le (a := 9400 * ratioScale * logScale * (lu_hi + logScale))
        (b := 10000 * lu_hi * lu_hi) (Nat.mul_pos (Nat.mul_pos (by decide) hlu_hi_pos) hlu_hi_pos)
      have h1 : (((9400 * ratioScale * logScale * (lu_hi + logScale) : Nat) : ℝ) /
          ((10000 * lu_hi * lu_hi : Nat) : ℝ)) / ratioScale =
          0.9400 * (1 / ((lu_hi : ℝ) / logScale) + 1 / ((lu_hi : ℝ) / logScale) ^ 2) := by
        have hne1 := hluHiR_pos.ne'
        have hne2 := hS_pos.ne'
        have hne3 := hW_pos.ne'
        push_cast; field_simp; ring
      have hlogU_pos : 0 < Real.log U := Real.log_pos (by exact_mod_cast (show 1 < U by omega))
      have h2 : 1 / ((lu_hi : ℝ) / logScale) ≤ 1 / Real.log U :=
        div_le_div_of_nonneg_left (by norm_num) hlogU_pos hlu_hi'
      have h3 : 1 / ((lu_hi : ℝ) / logScale) ^ 2 ≤ 1 / (Real.log U) ^ 2 :=
        div_le_div_of_nonneg_left (by norm_num) (sq_pos_of_pos hlogU_pos) (pow_le_pow_left₀ hlogU_pos.le hlu_hi' 2)
      have hdiv' := div_le_div_of_nonneg_right hdiv hW_pos.le
      linarith
    have htll : (((9400 * ratioScale * llog_lo) /
          (10000 * logScale) : Nat) : ℝ) / ratioScale ≤
        0.9400 * Real.log (Real.log U / Real.log ((L + 1 : Nat) : ℝ)) := by
      have hdiv := nat_div_cast_le (a := 9400 * ratioScale * llog_lo)
        (b := 10000 * logScale) (by decide)
      have h1 : (((9400 * ratioScale * llog_lo : Nat) : ℝ) /
          ((10000 * logScale : Nat) : ℝ)) / ratioScale =
          0.9400 * ((llog_lo : ℝ) / logScale) := by
        have hne2 := hS_pos.ne'
        have hne3 := hW_pos.ne'
        push_cast; field_simp; ring
      have hdiv' := div_le_div_of_nonneg_right hdiv hW_pos.le
      linarith
    have htL : (L.primeCounting : ℝ) / L ≤ ((ceilDiv (ratioScale * piL) L : Nat) : ℝ) / ratioScale := by
      rw [← hpiL]
      have hceil := ceilDiv_cast_ge (a := ratioScale * piL) (b := L) (by omega)
      have h1 : (piL : ℝ) / L = ((ratioScale * piL : Nat) : ℝ) / L / ratioScale := by
        have hne3 := hW_pos.ne'
        push_cast; field_simp
      rw [h1]
      exact div_le_div_of_nonneg_right hceil hW_pos.le
    apply (div_le_iff₀ hW_pos).mpr
    apply nat_sub_cast_le_of_le (mul_nonneg hsum_nn hW_pos.le)
    push_cast
    have hsum' : ((9400 * ratioScale * logScale * (lu_hi + logScale)) / (10000 * lu_hi * lu_hi) : Nat) +
        ((9400 * ratioScale * llog_lo) / (10000 * logScale) : Nat) -
        ((ceilDiv (ratioScale * piL) L : Nat) : ℝ) ≤
        (∑ p ∈ (Ioc L U).filter Nat.Prime, (1 : ℝ) / p) * ratioScale := by
      have hcomb : ((9400 * ratioScale * logScale * (lu_hi + logScale)) / (10000 * lu_hi * lu_hi) : Nat) / (ratioScale : ℝ) +
          ((9400 * ratioScale * llog_lo) / (10000 * logScale) : Nat) / (ratioScale : ℝ) -
          ((ceilDiv (ratioScale * piL) L : Nat) : ℝ) / ratioScale ≤
          ∑ p ∈ (Ioc L U).filter Nat.Prime, (1 : ℝ) / p := by linarith
      have hmul := mul_le_mul_of_nonneg_right hcomb hW_pos.le
      have heq : (((9400 * ratioScale * logScale * (lu_hi + logScale)) / (10000 * lu_hi * lu_hi) : Nat) / (ratioScale : ℝ) +
          ((9400 * ratioScale * llog_lo) / (10000 * logScale) : Nat) / (ratioScale : ℝ) -
          ((ceilDiv (ratioScale * piL) L : Nat) : ℝ) / ratioScale) * ratioScale =
          ((9400 * ratioScale * logScale * (lu_hi + logScale)) / (10000 * lu_hi * lu_hi) : Nat) +
          ((9400 * ratioScale * llog_lo) / (10000 * logScale) : Nat) -
          ((ceilDiv (ratioScale * piL) L : Nat) : ℝ) := by
        have hne3 := hW_pos.ne'
        field_simp
      linarith
    exact hsum'

private lemma g4Group_valid_props {mlo mhi cnt S4 L piL : Nat} {ms : List Nat}
    (hchk : checkG4Group mlo mhi cnt S4 L piL ms = true) :
    0 < mlo ∧ mhi ≤ 10000 ∧ 100 ≤ L ∧ L ≤ 8192 ∧ piL = L.primeCounting ∧ ms.Nodup ∧
    ms.toFinset.card = cnt ∧
    (∀ m ∈ ms, mlo ≤ m ∧ m ≤ mhi ∧ 0 < m ∧ 4 * m.divisors.card ∣ m ∧
      m.primeFactors.sup id ≤ L ∧ 200000 / m ≤ L) ∧
    (S4 : ℝ) / harmScale ≤ ∑ m ∈ ms.toFinset, (1 : ℝ) / m := by
  unfold checkG4Group at hchk
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨⟨⟨⟨hmlo, hmhi, hL100, hL8k, hpiL, hlen⟩, hch⟩, hall⟩, hS4⟩ := hchk
  have hnd : ms.Nodup := nodup_of_isStrictSorted hch
  have hpiL' : piL = L.primeCounting := by rw [hpiL, exactPiSmall_correct hL8k]
  have hcard : ms.toFinset.card = cnt := by rw [List.toFinset_card_of_nodup hnd, hlen]
  have hmem : ∀ m ∈ ms, mlo ≤ m ∧ m ≤ mhi ∧ 0 < m ∧ 4 * m.divisors.card ∣ m ∧
      m.primeFactors.sup id ≤ L ∧ 200000 / m ≤ L := by
    intro m hm
    have h1 := decide_eq_true_eq.mp (List.all_eq_true.mp hall m hm)
    have hm0 : 0 < m := by omega
    have hspec := fastTauTop_spec primesLe100_prime' primesLe100_nodup' primesLe100_cov'
      hm0 (by omega : m < 2 ^ 14) (by omega : m < 101 * 101)
    rw [hspec.1, hspec.2] at h1
    exact ⟨h1.1, h1.2.1, hm0, Nat.dvd_of_mod_eq_zero h1.2.2.1, h1.2.2.2.1, h1.2.2.2.2⟩
  refine ⟨hmlo, hmhi, hL100, hL8k, hpiL', hnd, hcard, hmem, ?_⟩
  rw [← hS4]
  exact list_harmonic_le hnd (fun m hm => (hmem m hm).2.2.1)

private lemma sum_pi_primes_le_sq (L U : Nat) :
    ∑ p ∈ (Ioc L U).filter Nat.Prime, (p.primeCounting : ℝ) ≤ (U.primeCounting : ℝ) ^ 2 := by
  have hsub : (Ioc L U).filter Nat.Prime ⊆ Nat.primesLE U := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesLE.mpr ⟨(Finset.mem_Ioc.mp hpI).2, hpp⟩
  have hcard : ((Ioc L U).filter Nat.Prime).card ≤ U.primeCounting := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    exact Finset.card_le_card hsub
  calc ∑ p ∈ (Ioc L U).filter Nat.Prime, (p.primeCounting : ℝ)
      ≤ ∑ _p ∈ (Ioc L U).filter Nat.Prime, (U.primeCounting : ℝ) := by
        refine Finset.sum_le_sum fun p hp => ?_
        exact_mod_cast Nat.monotone_primeCounting (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2
    _ = (((Ioc L U).filter Nat.Prime).card : ℝ) * (U.primeCounting : ℝ) := by simp
    _ ≤ (U.primeCounting : ℝ) * (U.primeCounting : ℝ) := by
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Nat.cast_nonneg _)
    _ = (U.primeCounting : ℝ) ^ 2 := by ring

private lemma g4GroupTerm_sound {Na Nb n mlo mhi cnt S4 L piL : Nat} {ms : List Nat}
    (hchk : checkG4Group mlo mhi cnt S4 L piL ms = true)
    (hNa : 10000000 ≤ Na) (hn1 : Na ≤ n) (hn2 : n ≤ Nb) :
    (g4GroupTerm Na Nb mlo mhi cnt S4 L piL : ℝ) / ratioScale ≤
      2 * (f2Count n ms.toFinset L (Nat.sqrt (Na / (20 * mhi))) : ℝ) / ((n : ℝ) / Real.log n) := by
  have hW_pos : (0 : ℝ) < ratioScale := by norm_num [ratioScale]
  have hS_pos : (0 : ℝ) < logScale := by norm_num [logScale]
  have hH_pos : (0 : ℝ) < harmScale := by norm_num [harmScale]
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hdenom_pos : 0 < (n : ℝ) / Real.log n := div_pos hn_pos hlogn_pos
  have hrhs_nn : 0 ≤ 2 * (f2Count n ms.toFinset L (Nat.sqrt (Na / (20 * mhi))) : ℝ) / ((n : ℝ) / Real.log n) := by
    positivity
  unfold g4GroupTerm
  dsimp only
  set U := Nat.sqrt (Na / (20 * mhi))
  split_ifs with hskip hHp0
  · simp; exact hrhs_nn
  · simp; exact hrhs_nn
  · push Not at hskip
    obtain ⟨hLU, h101U⟩ := hskip
    obtain ⟨hmlo, hmhi, hL100, _, hpiL, _, hcard, hmem, hharm⟩ := g4Group_valid_props hchk
    by_cases hme : ms = []
    · subst hme
      have : S4 = 0 := by
        unfold checkG4Group at hchk
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.map_nil, List.sum_nil] at hchk
        exact hchk.2.symm
      simp [this]; exact hrhs_nn
    obtain ⟨m0, hm0⟩ := List.exists_mem_of_ne_nil ms hme
    have hmlo_le_mhi : mlo ≤ mhi := (hmem m0 hm0).1.trans (hmem m0 hm0).2.1
    have hlb_lo := (logRatBounds_correct (a := Nb) (b := 1) le_rfl (by omega)).1
    simp only [Nat.cast_one, div_one] at hlb_lo
    have hla_hi := (logRatBounds_correct (a := Na) (b := 1) le_rfl (by omega)).2
    simp only [Nat.cast_one, div_one] at hla_hi
    have hmloL_pos : 1 ≤ mlo * L := by nlinarith
    have hmloL_lt_Nb : mlo * L < Nb := by nlinarith
    have hlnmp_hi := (logRatBounds_correct (a := Nb) (b := mlo * L) hmloL_pos hmloL_lt_Nb.le).2
    have hlnmp_pos : 0 < logRatHi Nb (mlo * L) := by
      have h1 : (0 : ℝ) < Real.log ((Nb : ℝ) / ((mlo * L : Nat) : ℝ)) :=
        Real.log_pos ((one_lt_div (by exact_mod_cast hmloL_pos)).mpr (by exact_mod_cast hmloL_lt_Nb))
      have h2 : (0 : ℝ) < (logRatHi Nb (mlo * L) : ℝ) / logScale := lt_of_lt_of_le h1 hlnmp_hi
      exact_mod_cast ((div_pos_iff_of_pos_right hS_pos).mp h2)
    have hHp := g4HpLo_sound hL100 hLU hpiL
    have hpiU_le := g4PiUHi_sound (by omega : 1 ≤ U)
    have hlb_lo' : (logNatLo Nb : ℝ) / logScale ≤ Real.log Nb := hlb_lo
    have hla_hi' : Real.log Na ≤ (logNatHi Na : ℝ) / logScale := hla_hi
    clear hlb_lo hla_hi
    generalize hlb_eq : logNatLo Nb = lb at hlb_lo' ⊢
    generalize hla_eq : logNatHi Na = la at hla_hi' ⊢
    generalize hlnmp_eq : logRatHi Nb (mlo * L) = lnmp at hlnmp_hi hlnmp_pos ⊢
    generalize hHp_eq : g4HpLo L piL U = Hp at hHp hHp0 ⊢
    generalize hpiU_eq : g4PiUHi U = piU at hpiU_le ⊢
    clear hlb_eq hla_eq hlnmp_eq hHp_eq hpiU_eq
    have hlnmpR_pos : (0 : ℝ) < lnmp := Nat.cast_pos.mpr hlnmp_pos
    have hfac_nn : (0 : ℝ) ≤ (lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (add_nonneg hlnmpR_pos.le hS_pos.le)) (sq_nonneg _)
    -- Lower bound f2Count
    have hf2_ge : (∑ m ∈ ms.toFinset, ∑ p ∈ (Ioc L U).filter Nat.Prime, ((n / (m * p)).primeCounting : ℝ)) -
        (cnt : ℝ) * (piU : ℝ) ^ 2 ≤ (f2Count n ms.toFinset L U : ℝ) := by
      have h1 : ∑ m ∈ ms.toFinset, ∑ p ∈ (Ioc L U).filter Nat.Prime,
          (((n / (m * p)).primeCounting : ℝ) - (p.primeCounting : ℝ)) ≤ (f2Count n ms.toFinset L U : ℝ) := by
        unfold f2Count; push_cast
        exact Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun p _ => nat_sub_cast_ge _ _
      simp_rw [Finset.sum_sub_distrib] at h1
      have hsub : ∑ m ∈ ms.toFinset, ∑ p ∈ (Ioc L U).filter Nat.Prime, (p.primeCounting : ℝ) ≤
          (cnt : ℝ) * (piU : ℝ) ^ 2 := by
        calc ∑ m ∈ ms.toFinset, ∑ p ∈ (Ioc L U).filter Nat.Prime, (p.primeCounting : ℝ)
            ≤ ∑ _m ∈ ms.toFinset, (piU : ℝ) ^ 2 := by
              refine Finset.sum_le_sum fun _ _ => ?_
              exact (sum_pi_primes_le_sq L U).trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hpiU_le 2)
          _ = (ms.toFinset.card : ℝ) * (piU : ℝ) ^ 2 := by simp
          _ = (cnt : ℝ) * (piU : ℝ) ^ 2 := by rw [hcard]
      linarith
    -- Lower bound the double sum of π(n/(mp))
    have hdouble : 0.9400 * ((n : ℝ) / Real.log n) *
        ((lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2)) *
        ((S4 : ℝ) / harmScale) * ((Hp : ℝ) / ratioScale) ≤
        ∑ m ∈ ms.toFinset, ∑ p ∈ (Ioc L U).filter Nat.Prime, ((n / (m * p)).primeCounting : ℝ) := by
      have hterm : ∀ m ∈ ms.toFinset, ∀ p ∈ (Ioc L U).filter Nat.Prime,
          0.9400 * ((n : ℝ) / Real.log n) *
            ((lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2)) *
            ((1 : ℝ) / m) * ((1 : ℝ) / p) ≤ ((n / (m * p)).primeCounting : ℝ) := by
        intro m hm p hp
        obtain ⟨hm1, hm2, hmpos, _, _, _⟩ := hmem m (List.mem_toFinset.mp hm)
        obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
        obtain ⟨hpL, hpU⟩ := Finset.mem_Ioc.mp hpI
        have hmp_pos : 0 < m * p := Nat.mul_pos hmpos hpp.pos
        have hmp_le : m * p ≤ mhi * U := Nat.mul_le_mul hm2 hpU
        have hmp_ge : mlo * L ≤ m * p := Nat.mul_le_mul hm1 hpL.le
        have hmpR_pos : (0 : ℝ) < ((m * p : Nat) : ℝ) := Nat.cast_pos.mpr hmp_pos
        have hxmp : (101 : ℝ) ≤ (n : ℝ) / ((m * p : Nat) : ℝ) := by
          rw [le_div_iff₀ hmpR_pos]
          exact_mod_cast (show 101 * (m * p) ≤ n by
            have h1 : 101 * (m * p) ≤ 101 * (mhi * U) := Nat.mul_le_mul_left 101 hmp_le
            have h2 : 101 * (mhi * U) = 101 * mhi * U := by ring
            omega)
        have hpi := pi_lower_all hxmp
        rw [floor_nat_div_eq] at hpi
        have hnmp_pos : (0 : ℝ) < (n : ℝ) / ((m * p : Nat) : ℝ) := div_pos hn_pos hmpR_pos
        have hlog_nmp_pos : 0 < Real.log ((n : ℝ) / ((m * p : Nat) : ℝ)) := Real.log_pos (by linarith)
        have hlog_le : Real.log ((n : ℝ) / ((m * p : Nat) : ℝ)) ≤ Real.log ((Nb : ℝ) / ((mlo * L : Nat) : ℝ)) := by
          apply Real.log_le_log hnmp_pos
          exact div_le_div₀ (Nat.cast_nonneg _) (by exact_mod_cast hn2) (by exact_mod_cast hmloL_pos) (by exact_mod_cast hmp_ge)
        have hanti := log_div_log_div_antitone (c := ((mlo * L : Nat) : ℝ)) (a := (n : ℝ)) (b := (Nb : ℝ))
          (by exact_mod_cast hmloL_pos) (by exact_mod_cast (show mlo * L < n by
            have hlt1 : mlo * L < mhi * U := Nat.mul_lt_mul_of_le_of_lt hmlo_le_mhi hLU (by omega)
            have hle2 : mhi * U ≤ 101 * mhi * U := Nat.mul_le_mul_right U (Nat.le_mul_of_pos_left mhi (by decide))
            exact lt_of_lt_of_le hlt1 (hle2.trans (h101U.trans hn1)))) (by exact_mod_cast hn2)
        have hmono_mp : Real.log n / Real.log ((n : ℝ) / ((mlo * L : Nat) : ℝ)) ≤
            Real.log n / Real.log ((n : ℝ) / ((m * p : Nat) : ℝ)) := by
          apply div_le_div_of_nonneg_left hlogn_pos.le hlog_nmp_pos
          exact Real.log_le_log hnmp_pos
            (div_le_div_of_nonneg_left hn_pos.le (by exact_mod_cast hmloL_pos) (by exact_mod_cast hmp_ge))
        have hlog_nb_pos : 0 < Real.log ((Nb : ℝ) / ((mlo * L : Nat) : ℝ)) := lt_of_lt_of_le hlog_nmp_pos hlog_le
        have hrat1 : (lb : ℝ) / (lnmp : ℝ) ≤ Real.log n / Real.log ((n : ℝ) / ((m * p : Nat) : ℝ)) := by
          have h1 : (lb : ℝ) / (lnmp : ℝ) = ((lb : ℝ) / logScale) / ((lnmp : ℝ) / logScale) := by
            have hne1 := hS_pos.ne'; have hne2 := hlnmpR_pos.ne'; field_simp
          have h2 : ((lb : ℝ) / logScale) / ((lnmp : ℝ) / logScale) ≤
              Real.log Nb / Real.log ((Nb : ℝ) / ((mlo * L : Nat) : ℝ)) := by
            calc _ ≤ Real.log Nb / ((lnmp : ℝ) / logScale) :=
                  div_le_div_of_nonneg_right hlb_lo' (div_pos hlnmpR_pos hS_pos).le
              _ ≤ _ := div_le_div_of_nonneg_left (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Nb by omega)))
                  hlog_nb_pos hlnmp_hi
          exact h1.le.trans (h2.trans (hanti.trans hmono_mp))
        have hrat2 : ((lnmp : ℝ) + logScale) / (lnmp : ℝ) ≤ 1 + 1 / Real.log ((n : ℝ) / ((m * p : Nat) : ℝ)) := by
          have h1 : ((lnmp : ℝ) + logScale) / (lnmp : ℝ) = 1 + 1 / ((lnmp : ℝ) / logScale) := by
            have hne1 := hlnmpR_pos.ne'; have hne2 := hS_pos.ne'; field_simp
          rw [h1]
          exact add_le_add le_rfl (div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num) hlog_nmp_pos (hlog_le.trans hlnmp_hi))
        have hmul_rat : (lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2) ≤
            (Real.log n / Real.log ((n : ℝ) / ((m * p : Nat) : ℝ))) * (1 + 1 / Real.log ((n : ℝ) / ((m * p : Nat) : ℝ))) := by
          have heq : (lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2) =
              ((lb : ℝ) / (lnmp : ℝ)) * (((lnmp : ℝ) + logScale) / (lnmp : ℝ)) := by ring
          rw [heq]
          exact mul_le_mul hrat1 hrat2
            (div_nonneg (add_nonneg hlnmpR_pos.le hS_pos.le) hlnmpR_pos.le)
            (div_nonneg hlogn_pos.le hlog_nmp_pos.le)
        have hrew : 0.9400 * ((n : ℝ) / Real.log n) *
            ((Real.log n / Real.log ((n : ℝ) / ((m * p : Nat) : ℝ))) *
              (1 + 1 / Real.log ((n : ℝ) / ((m * p : Nat) : ℝ)))) * ((1 : ℝ) / m) * ((1 : ℝ) / p) =
            0.9400 * (((n : ℝ) / ((m * p : Nat) : ℝ)) / Real.log ((n : ℝ) / ((m * p : Nat) : ℝ)) +
              ((n : ℝ) / ((m * p : Nat) : ℝ)) / (Real.log ((n : ℝ) / ((m * p : Nat) : ℝ))) ^ 2) := by
          have hmR : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hmpos).ne'
          have hpR : (p : ℝ) ≠ 0 := (Nat.cast_pos.mpr hpp.pos).ne'
          have hln : Real.log n ≠ 0 := hlogn_pos.ne'
          have hlmp : Real.log ((n : ℝ) / ((m * p : Nat) : ℝ)) ≠ 0 := hlog_nmp_pos.ne'
          rw [Nat.cast_mul] at hlmp ⊢
          field_simp
        have hmR_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hmpos
        have hpR_pos : (0 : ℝ) < p := Nat.cast_pos.mpr hpp.pos
        calc _ ≤ 0.9400 * ((n : ℝ) / Real.log n) *
              ((Real.log n / Real.log ((n : ℝ) / ((m * p : Nat) : ℝ))) *
                (1 + 1 / Real.log ((n : ℝ) / ((m * p : Nat) : ℝ)))) * ((1 : ℝ) / m) * ((1 : ℝ) / p) := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hmul_rat (mul_nonneg (by norm_num) hdenom_pos.le))
                  (div_nonneg (by norm_num) hmR_pos.le))
                (div_nonneg (by norm_num) hpR_pos.le)
          _ = _ := hrew
          _ ≤ ((n / (m * p)).primeCounting : ℝ) := hpi
      have hC_nn : 0 ≤ 0.9400 * ((n : ℝ) / Real.log n) *
          ((lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2)) :=
        mul_nonneg (mul_nonneg (by norm_num) hdenom_pos.le) hfac_nn
      calc _ ≤ 0.9400 * ((n : ℝ) / Real.log n) *
              ((lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2)) *
              (∑ m ∈ ms.toFinset, (1 : ℝ) / m) * (∑ p ∈ (Ioc L U).filter Nat.Prime, (1 : ℝ) / p) := by
            have h1 := mul_le_mul hharm hHp (div_nonneg (Nat.cast_nonneg _) hW_pos.le)
              (Finset.sum_nonneg fun _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
            have h2 := mul_le_mul_of_nonneg_left h1 hC_nn
            simpa only [mul_assoc] using h2
        _ = ∑ m ∈ ms.toFinset, ∑ p ∈ (Ioc L U).filter Nat.Prime,
              (0.9400 * ((n : ℝ) / Real.log n) *
                ((lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2)) *
                ((1 : ℝ) / m) * ((1 : ℝ) / p)) := by
            rw [show 0.9400 * ((n : ℝ) / Real.log n) *
                  ((lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2)) *
                  (∑ m ∈ ms.toFinset, (1 : ℝ) / m) =
                ∑ m ∈ ms.toFinset, (0.9400 * ((n : ℝ) / Real.log n) *
                  ((lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2)) * ((1 : ℝ) / m)) by
              rw [Finset.mul_sum]]
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun p hp => hterm m hm p hp
    -- Combine main2 and err2
    apply (div_le_iff₀ hW_pos).mpr
    apply nat_sub_cast_le_of_le (mul_nonneg hrhs_nn hW_pos.le)
    have hmain2 : (((2 * 9400 * S4 * Hp * lb * (lnmp + logScale)) /
          (10000 * harmScale * lnmp * lnmp) : Nat) : ℝ) ≤
        2 * 0.9400 * ((lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2)) *
          ((S4 : ℝ) / harmScale) * ((Hp : ℝ) / ratioScale) * ratioScale := by
      have hdiv := nat_div_cast_le
        (a := 2 * 9400 * S4 * Hp * lb * (lnmp + logScale))
        (b := 10000 * harmScale * lnmp * lnmp)
        (Nat.mul_pos (Nat.mul_pos (by decide) hlnmp_pos) hlnmp_pos)
      have heq : ((2 * 9400 * S4 * Hp * lb * (lnmp + logScale) : Nat) : ℝ) /
          ((10000 * harmScale * lnmp * lnmp : Nat) : ℝ) =
          2 * 0.9400 * ((lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2)) *
            ((S4 : ℝ) / harmScale) * ((Hp : ℝ) / ratioScale) * ratioScale := by
        have hneW := hW_pos.ne'; have hneH := hH_pos.ne'; have hneL := hlnmpR_pos.ne'
        push_cast; field_simp; ring
      linarith
    have herr2 : 2 * ((cnt : ℝ) * (piU : ℝ) ^ 2) / ((n : ℝ) / Real.log n) * ratioScale ≤
        ((ceilDiv (2 * ratioScale * cnt * piU * piU * la) (logScale * Na) : Nat) : ℝ) := by
      have hceil := ceilDiv_cast_ge (a := 2 * ratioScale * cnt * piU * piU * la)
        (b := logScale * Na) (Nat.mul_pos (by decide) (by omega))
      have hanti := log_div_self_antitone (a := (Na : ℝ)) (b := (n : ℝ))
        (by exact_mod_cast (show 3 ≤ Na by omega)) (by exact_mod_cast hn1)
      have h1 : 2 * ((cnt : ℝ) * (piU : ℝ) ^ 2) / ((n : ℝ) / Real.log n) * ratioScale =
          2 * (ratioScale : ℝ) * cnt * (piU : ℝ) ^ 2 * (Real.log n / n) := by
        have hne1 := hn_pos.ne'; have hne2 := hlogn_pos.ne'
        field_simp
      have h2 : 2 * (ratioScale : ℝ) * cnt * (piU : ℝ) ^ 2 * (Real.log n / n) ≤
          2 * (ratioScale : ℝ) * cnt * (piU : ℝ) ^ 2 * ((la : ℝ) / logScale / Na) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hW_pos.le) (Nat.cast_nonneg _)) (sq_nonneg _))
        exact hanti.trans (div_le_div_of_nonneg_right hla_hi' (Nat.cast_nonneg _))
      have h3 : 2 * (ratioScale : ℝ) * cnt * (piU : ℝ) ^ 2 * ((la : ℝ) / logScale / Na) =
          ((2 * ratioScale * cnt * piU * piU * la : Nat) : ℝ) /
            ((logScale * Na : Nat) : ℝ) := by
        have hne1 := hS_pos.ne'
        have hne2 : (Na : ℝ) ≠ 0 := (by exact_mod_cast (show 0 < Na by omega) : (0 : ℝ) < Na).ne'
        push_cast; field_simp
      linarith
    have hdiv_all : 2 * 0.9400 * ((lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2)) *
        ((S4 : ℝ) / harmScale) * ((Hp : ℝ) / ratioScale) -
        2 * ((cnt : ℝ) * (piU : ℝ) ^ 2) / ((n : ℝ) / Real.log n) ≤
        2 * (f2Count n ms.toFinset L U : ℝ) / ((n : ℝ) / Real.log n) := by
      have h1 : 2 * (0.9400 * ((n : ℝ) / Real.log n) *
          ((lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2)) *
          ((S4 : ℝ) / harmScale) * ((Hp : ℝ) / ratioScale) - (cnt : ℝ) * (piU : ℝ) ^ 2) ≤
          2 * (f2Count n ms.toFinset L U : ℝ) := by linarith
      have h2 := div_le_div_of_nonneg_right h1 hdenom_pos.le
      have heq : 2 * (0.9400 * ((n : ℝ) / Real.log n) *
          ((lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2)) *
          ((S4 : ℝ) / harmScale) * ((Hp : ℝ) / ratioScale) - (cnt : ℝ) * (piU : ℝ) ^ 2) /
          ((n : ℝ) / Real.log n) =
          2 * 0.9400 * ((lb : ℝ) * ((lnmp : ℝ) + logScale) / ((lnmp : ℝ) ^ 2)) *
            ((S4 : ℝ) / harmScale) * ((Hp : ℝ) / ratioScale) -
          2 * ((cnt : ℝ) * (piU : ℝ) ^ 2) / ((n : ℝ) / Real.log n) := by
        have hne1 := hn_pos.ne'; have hne2 := hlogn_pos.ne'
        field_simp
      linarith
    have hmul_all := mul_le_mul_of_nonneg_right hdiv_all hW_pos.le
    rw [sub_mul] at hmul_all
    linarith

/- ### Part 6: Disjointness of our 14 G1 buckets and 5 G4 groups, interval coverage, and 10^32 tail -/

private lemma disjoint_of_range {A B : Finset Nat} {a_hi b_lo : Nat}
    (hA : ∀ x ∈ A, x ≤ a_hi) (hB : ∀ y ∈ B, b_lo ≤ y) (hlt : a_hi < b_lo) :
    Disjoint A B := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  have := hA x hxA
  have := hB x hxB
  omega

private def g1Finsets : List (Finset Nat) :=
  g1Buckets.map (fun b => b.2.2.2.2.toFinset)

private lemma g1Buckets_all_ok :
    ∀ b ∈ g1Buckets, checkG1Bucket b.1 b.2.1 b.2.2.1 b.2.2.2.1 b.2.2.2.2 = true := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := g1CheckA.down
  have h11 := g1CheckB.down
  have h12 := g1CheckC.down
  have h13 := g1CheckD.down
  intro b hb
  simp only [g1Buckets, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4
  · exact h5
  · exact h6
  · exact h7
  · exact h8
  · exact h9
  · exact h10
  · exact h11
  · exact h12
  · exact h13

private lemma g4Groups_all_ok :
    ∀ g ∈ g4Groups, checkG4Group g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2.1 g.2.2.2.2.2.2 = true := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := g4CheckAll.down
  intro g hg
  simp only [g4Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
  · exact h3
  · exact h4

private lemma g1Finsets_disjoint : g1Finsets.Pairwise Disjoint := by
  have hmem := fun b hb => (g1Bucket_valid_props (g1Buckets_all_ok b hb)).2.2.2.1
  have hrange : ∀ b ∈ g1Buckets, ∀ x ∈ b.2.2.2.2.toFinset, b.1 ≤ x ∧ x ≤ b.2.1 := fun b hb x hx =>
    ⟨(hmem b hb x (List.mem_toFinset.mp hx)).1, (hmem b hb x (List.mem_toFinset.mp hx)).2.1⟩
  have hpw_hi : g1Buckets.Pairwise (fun b1 b2 => b1.2.1 < b2.1) := by
    have hpw_meta : g1Meta.Pairwise (fun b1 b2 => b1.2.1 < b2.1) := by decide +kernel
    have hmap : g1Buckets.map (fun b => (b.1, b.2.1, b.2.2.1, b.2.2.2.1)) = g1Meta := rfl
    rw [← hmap, List.pairwise_map] at hpw_meta
    exact hpw_meta
  unfold g1Finsets
  rw [List.pairwise_map]
  exact hpw_hi.imp_of_mem fun {b1 b2} hb1 hb2 hlt =>
    disjoint_of_range (fun x hx => (hrange b1 hb1 x hx).2) (fun y hy => (hrange b2 hb2 y hy).1) hlt

private lemma g1Finsets_good : ∀ B ∈ g1Finsets, ∀ k ∈ B, 0 < k ∧ k ≤ 200000 ∧ 2 * k.divisors.card ∣ k := by
  intro B hB k hk
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hB
  have h := (g1Bucket_valid_props (g1Buckets_all_ok b hb)).2.2.2.1 k (List.mem_toFinset.mp hk)
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

private lemma g4Finsets_disjoint (Na : Nat) :
    ((g4Groups.map (fun g => (g.2.2.2.2.2.2.toFinset, g.2.2.2.2.1, Nat.sqrt (Na / (20 * g.2.1))))).map Prod.fst).Pairwise Disjoint := by
  rw [List.map_map]
  have hmem := fun g hg => (g4Group_valid_props (g4Groups_all_ok g hg)).2.2.2.2.2.2.2.1
  have hrange : ∀ g ∈ g4Groups, ∀ x ∈ g.2.2.2.2.2.2.toFinset, g.1 ≤ x ∧ x ≤ g.2.1 := fun g hg x hx =>
    ⟨(hmem g hg x (List.mem_toFinset.mp hx)).1, (hmem g hg x (List.mem_toFinset.mp hx)).2.1⟩
  have hpw_hi : g4Groups.Pairwise (fun g1 g2 => g1.2.1 < g2.1) := by
    simp only [g4Groups, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
      List.Pairwise.nil, forall_eq_or_imp, forall_eq, false_imp_iff, forall_const, and_true]
    decide
  rw [List.pairwise_map]
  exact hpw_hi.imp_of_mem fun {g1 g2} hg1 hg2 hlt =>
    disjoint_of_range (fun x hx => (hrange g1 hg1 x hx).2) (fun y hy => (hrange g2 hg2 y hy).1) hlt

private lemma g4Finsets_good (Na : Nat) :
    ∀ d ∈ g4Groups.map (fun g => (g.2.2.2.2.2.2.toFinset, g.2.2.2.2.1, Nat.sqrt (Na / (20 * g.2.1)))),
      ∀ m ∈ d.1, 0 < m ∧ 4 * m.divisors.card ∣ m ∧ m.primeFactors.sup id ≤ d.2.1 ∧ 200000 / m ≤ d.2.1 := by
  intro d hd m hm
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hd
  have h := (g4Group_valid_props (g4Groups_all_ok g hg)).2.2.2.2.2.2.2.1 m (List.mem_toFinset.mp hm)
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

private lemma list_sum_div (L : List ℝ) (c : ℝ) : L.sum / c = (L.map (· / c)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih => simp [add_div, ih]

private lemma list_mul_sum (c : ℝ) (L : List ℝ) : c * L.sum = (L.map (c * ·)).sum := by
  induction L with
  | nil => simp
  | cons x xs ih => simp [mul_add, ih]

private lemma list_sum_real_le {α : Type*} (L : List α) (f g : α → ℝ)
    (h : ∀ x ∈ L, f x ≤ g x) : (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h x (by simp)) (ih (fun y hy => h y (List.mem_cons_of_mem _ hy)))

private lemma interval_colton_sound {Na Nb : Nat} (hNa : 10000000 ≤ Na)
    (hchk : lhsHi Na ≤ rhs1Int Na Nb + rhs2Int Na Nb) :
    ∀ n, Na ≤ n → n ≤ Nb → n.primeCounting ≤ 2 * countRefactorableNat n := by
  intro n hn1 hn2
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hdenom_pos : 0 < (n : ℝ) / Real.log n := div_pos hn_pos hlogn_pos
  have hW_pos : (0 : ℝ) < ratioScale := by norm_num [ratioScale]
  let Dgroups := g4Groups.map (fun g => (g.2.2.2.2.2.2.toFinset, g.2.2.2.2.1, Nat.sqrt (Na / (20 * g.2.1))))
  have hdisj := disjoint_F1_F2_count n g1Finsets g1Finsets_disjoint g1Finsets_good
    Dgroups (g4Finsets_disjoint Na) (g4Finsets_good Na)
  have hlhs := lhsHi_sound hNa hn1
  have hr1 : (rhs1Int Na Nb : ℝ) / ratioScale ≤
      2 * ((g1Finsets.map (f1Count n)).sum : ℝ) / ((n : ℝ) / Real.log n) := by
    have hmeta_eq : rhs1Int Na Nb =
        (g1Buckets.map (fun b => g1BucketTerm Na Nb b.1 b.2.1 b.2.2.1 b.2.2.2.1)).sum := rfl
    rw [hmeta_eq, Nat.cast_list_sum, list_sum_div, List.map_map, List.map_map]
    have hsum2 : 2 * ((g1Finsets.map (f1Count n)).sum : ℝ) / ((n : ℝ) / Real.log n) =
        (g1Buckets.map (fun b => 2 * (f1Count n b.2.2.2.2.toFinset : ℝ) / ((n : ℝ) / Real.log n))).sum := by
      unfold g1Finsets
      rw [List.map_map, Nat.cast_list_sum, list_mul_sum, list_sum_div, List.map_map, List.map_map, List.map_map]
      rfl
    rw [hsum2]
    refine list_sum_real_le g1Buckets _ _ fun b hb => ?_
    dsimp only [Function.comp_apply]
    exact g1BucketTerm_sound (g1Buckets_all_ok b hb) hNa hn1 hn2
  have hr2 : (rhs2Int Na Nb : ℝ) / ratioScale ≤
      2 * ((Dgroups.map (fun g => f2Count n g.1 g.2.1 g.2.2)).sum : ℝ) / ((n : ℝ) / Real.log n) := by
    have hmeta_eq : rhs2Int Na Nb =
        (g4Groups.map (fun g => g4GroupTerm Na Nb g.1 g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2.1)).sum := rfl
    rw [hmeta_eq, Nat.cast_list_sum, list_sum_div, List.map_map, List.map_map]
    have hsum2 : 2 * ((Dgroups.map (fun g => f2Count n g.1 g.2.1 g.2.2)).sum : ℝ) / ((n : ℝ) / Real.log n) =
        (g4Groups.map (fun g => 2 * (f2Count n g.2.2.2.2.2.2.toFinset g.2.2.2.2.1 (Nat.sqrt (Na / (20 * g.2.1))) : ℝ) /
          ((n : ℝ) / Real.log n))).sum := by
      dsimp only [Dgroups]
      rw [List.map_map, Nat.cast_list_sum, list_mul_sum, list_sum_div, List.map_map, List.map_map, List.map_map]
      rfl
    rw [hsum2]
    refine list_sum_real_le g4Groups _ _ fun g hg => ?_
    dsimp only [Function.comp_apply]
    exact g4GroupTerm_sound (g4Groups_all_ok g hg) hNa hn1 hn2
  have hchkR : (lhsHi Na : ℝ) / ratioScale ≤ (rhs1Int Na Nb : ℝ) / ratioScale + (rhs2Int Na Nb : ℝ) / ratioScale := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hchk) hW_pos.le
  have htot : (n.primeCounting : ℝ) / ((n : ℝ) / Real.log n) ≤
      2 * ((countRefactorableNat n : Nat) : ℝ) / ((n : ℝ) / Real.log n) := by
    have hdisjR : ((g1Finsets.map (f1Count n)).sum : ℝ) +
        ((Dgroups.map (fun g => f2Count n g.1 g.2.1 g.2.2)).sum : ℝ) ≤ (countRefactorableNat n : ℝ) := by
      exact_mod_cast hdisj
    have hdiv_disj : 2 * ((g1Finsets.map (f1Count n)).sum : ℝ) / ((n : ℝ) / Real.log n) +
        2 * ((Dgroups.map (fun g => f2Count n g.1 g.2.1 g.2.2)).sum : ℝ) / ((n : ℝ) / Real.log n) ≤
        2 * (countRefactorableNat n : ℝ) / ((n : ℝ) / Real.log n) := by
      rw [← add_div, ← mul_add]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdisjR (by norm_num)) hdenom_pos.le
    linarith
  have hfinal : (n.primeCounting : ℝ) ≤ 2 * (countRefactorableNat n : ℝ) :=
    (div_le_div_iff_of_pos_right hdenom_pos).mp htot
  exact_mod_cast hfinal

private lemma intervals430_all :
    ∀ j < 430,
      intervals430[j]! ≤ intervals430[j + 1]! ∧
      lhsHi intervals430[j]! ≤ rhs1Int intervals430[j]! intervals430[j + 1]! +
        rhs2Int intervals430[j]! intervals430[j + 1]! := by
  intro j hj
  have hcases : (0 ≤ j ∧ j < 72) ∨ (72 ≤ j ∧ j < 144) ∨ (144 ≤ j ∧ j < 216) ∨ (216 ≤ j ∧ j < 288) ∨ (288 ≤ j ∧ j < 360) ∨ (360 ≤ j ∧ j < 430) := by omega
  rcases hcases with h | h | h | h | h | h
  · exact checkIntRange_at intBatch0.down (by omega) (by omega)
  · exact checkIntRange_at intBatch1.down (by omega) (by omega)
  · exact checkIntRange_at intBatch2.down (by omega) (by omega)
  · exact checkIntRange_at intBatch3.down (by omega) (by omega)
  · exact checkIntRange_at intBatch4.down (by omega) (by omega)
  · exact checkIntRange_at intBatch5.down (by omega) (by omega)

private lemma intervals430_mono : ∀ i j, i ≤ j → j ≤ 430 → intervals430[i]! ≤ intervals430[j]! := by
  intro i j hij hj
  obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
  clear hij
  induction d with
  | zero => simp
  | succ d ih =>
    have h1 := ih (by omega)
    have h2 := (intervals430_all (i + d) (by omega)).1
    exact h1.trans (by simpa [Nat.add_assoc] using h2)

theorem colton_mid_14M_1e32 : ∀ n, 14090240 ≤ n → n ≤ Ntail →
    n.primeCounting ≤ 2 * countRefactorableNat n := by
  have hstart : intervals430[0]! = 14090240 := by decide +kernel
  have hend : intervals430[430]! = Ntail := by decide +kernel
  suffices h : ∀ k ≤ 430, ∀ n, 14090240 ≤ n → n ≤ intervals430[k]! →
      n.primeCounting ≤ 2 * countRefactorableNat n by
    intro n hn1 hn2
    exact h 430 le_rfl n hn1 (hend ▸ hn2)
  intro k
  induction k with
  | zero =>
    intro _ n hn1 hn2
    rw [hstart] at hn2
    have : n = 14090240 := by omega
    subst this
    exact colton_le_14M 14090240 le_rfl
  | succ k ih =>
    intro hk n hn1 hn2
    by_cases hle : n ≤ intervals430[k]!
    · exact ih (by omega) n hn1 hle
    · push Not at hle
      have hge14M : 14090240 ≤ intervals430[k]! := by
        rw [← hstart]; exact intervals430_mono 0 k (Nat.zero_le k) (by omega)
      exact interval_colton_sound (by omega : 10000000 ≤ intervals430[k]!)
        (intervals430_all k (by omega)).2 n hle.le hn2

/- ### Constant-`U0` tail `[10^32, ∞)` -/

theorem colton_ge_1e32 : ∀ n, Ntail ≤ n → n.primeCounting ≤ 2 * countRefactorableNat n := by
  intro n hn
  have hn_pos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by unfold Ntail at hn; omega)
  have hlogn_pos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by unfold Ntail at hn; omega))
  have hdenom_pos : 0 < (n : ℝ) / Real.log n := div_pos hn_pos hlogn_pos
  have hW_pos : (0 : ℝ) < ratioScale := by norm_num [ratioScale]
  have hS_pos : (0 : ℝ) < logScale := by norm_num [logScale]
  have hH_pos : (0 : ℝ) < harmScale := by norm_num [harmScale]
  have hNt10M : 10000000 ≤ Ntail := by decide
  have hlhs := lhsHi_sound hNt10M hn
  have hlt_hi := (logRatBounds_correct (a := Ntail) (b := 1) le_rfl (by decide)).2
  simp only [Nat.cast_one, div_one] at hlt_hi
  have hanti_t := log_div_self_antitone (a := (Ntail : ℝ)) (b := (n : ℝ))
    (by exact_mod_cast (show 3 ≤ Ntail by decide)) (by exact_mod_cast hn)
  let Dgroups := g4Groups.map (fun g => (g.2.2.2.2.2.2.toFinset, g.2.2.2.2.1, Nat.sqrt (Ntail / (20 * g.2.1))))
  have hdisj := disjoint_F1_F2_count n g1Finsets g1Finsets_disjoint g1Finsets_good
    Dgroups (g4Finsets_disjoint Ntail) (g4Finsets_good Ntail)
  -- Family 1 tail lower bound: drop all log(n)/log(n/k) ≥ 1 and 1/log(n/k) ≥ 0
  have hr1 : (g1TailSum : ℝ) / ratioScale ≤
      2 * ((g1Finsets.map (f1Count n)).sum : ℝ) / ((n : ℝ) / Real.log n) := by
    have hbucket : ∀ b ∈ g1Buckets,
        0.9400 * ((n : ℝ) / Real.log n) * ((b.2.2.1 : ℝ) / harmScale) - (b.2.2.2.1 : ℝ) ≤
          (f1Count n b.2.2.2.2.toFinset : ℝ) := by
      intro b hb
      obtain ⟨hklo, hkhi, _, hmem, hharm, hE⟩ := g1Bucket_valid_props (g1Buckets_all_ok b hb)
      have hf1_ge : (∑ k ∈ b.2.2.2.2.toFinset, ((n / k).primeCounting : ℝ)) -
          (∑ k ∈ b.2.2.2.2.toFinset, ((k.primeFactors.sup id).primeCounting : ℝ)) ≤
          (f1Count n b.2.2.2.2.toFinset : ℝ) := by
        unfold f1Count; push_cast
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_le_sum fun k _ => nat_sub_cast_ge _ _
      have hsum_pi : 0.9400 * ((n : ℝ) / Real.log n) * ((b.2.2.1 : ℝ) / harmScale) ≤
          ∑ k ∈ b.2.2.2.2.toFinset, ((n / k).primeCounting : ℝ) := by
        have hterm : ∀ k ∈ b.2.2.2.2.toFinset,
            0.9400 * ((n : ℝ) / Real.log n) * ((1 : ℝ) / k) ≤ ((n / k).primeCounting : ℝ) := by
          intro k hk
          obtain ⟨_, _, hk0, hk200, _⟩ := hmem k (List.mem_toFinset.mp hk)
          have hkR_pos : (0 : ℝ) < k := by exact_mod_cast hk0
          have hxk : (101 : ℝ) ≤ (n : ℝ) / k := by
            rw [le_div_iff₀ hkR_pos]
            have : 101 * k ≤ n := by unfold Ntail at hn; omega
            exact_mod_cast this
          have hpi := pi_lower_all hxk
          rw [floor_nat_div_eq] at hpi
          have hlog_nk_pos : 0 < Real.log ((n : ℝ) / k) := Real.log_pos (by linarith)
          have hlog_le : Real.log ((n : ℝ) / k) ≤ Real.log n :=
            Real.log_le_log (by positivity) (div_le_self hn_pos.le (by exact_mod_cast hk0))
          have h1 : ((n : ℝ) / k) / Real.log n ≤ ((n : ℝ) / k) / Real.log ((n : ℝ) / k) :=
            div_le_div_of_nonneg_left (by positivity) hlog_nk_pos hlog_le
          have h2 : 0 ≤ ((n : ℝ) / k) / (Real.log ((n : ℝ) / k)) ^ 2 := by positivity
          have heq : 0.9400 * ((n : ℝ) / Real.log n) * ((1 : ℝ) / k) = 0.9400 * (((n : ℝ) / k) / Real.log n) := by
            field_simp
          linarith
        calc _ ≤ 0.9400 * ((n : ℝ) / Real.log n) * ∑ k ∈ b.2.2.2.2.toFinset, (1 : ℝ) / k :=
              mul_le_mul_of_nonneg_left hharm (by positivity)
          _ = ∑ k ∈ b.2.2.2.2.toFinset, (0.9400 * ((n : ℝ) / Real.log n) * ((1 : ℝ) / k)) := by
              rw [Finset.mul_sum]
          _ ≤ _ := Finset.sum_le_sum hterm
      linarith
    have hsum_b := list_sum_real_le g1Buckets
      (fun b => 0.9400 * ((n : ℝ) / Real.log n) * ((b.2.2.1 : ℝ) / harmScale) - (b.2.2.2.1 : ℝ))
      (fun b => (f1Count n b.2.2.2.2.toFinset : ℝ)) hbucket
    have hsum_lhs : (g1Buckets.map (fun b =>
        0.9400 * ((n : ℝ) / Real.log n) * ((b.2.2.1 : ℝ) / harmScale) - (b.2.2.2.1 : ℝ))).sum =
        0.9400 * ((n : ℝ) / Real.log n) * (((g1Meta.map (fun b => b.2.2.1)).sum : Nat) : ℝ) / harmScale -
          (((g1Meta.map (fun b => b.2.2.2)).sum : Nat) : ℝ) := by
      have h1 : (g1Buckets.map (fun b => b.2.2.1)).sum = (g1Meta.map (fun b => b.2.2.1)).sum := rfl
      have h2 : (g1Buckets.map (fun b => b.2.2.2.1)).sum = (g1Meta.map (fun b => b.2.2.2)).sum := rfl
      rw [← h1, ← h2]
      clear h1 h2 hsum_b hbucket
      induction g1Buckets with
      | nil => simp
      | cons b bs ih =>
        simp only [List.map_cons, List.sum_cons, Nat.cast_add]
        rw [ih]; ring
    have hsum_rhs : (g1Buckets.map (fun b => (f1Count n b.2.2.2.2.toFinset : ℝ))).sum =
        ((g1Finsets.map (f1Count n)).sum : ℝ) := by
      unfold g1Finsets; rw [List.map_map, Nat.cast_list_sum, List.map_map]; rfl
    rw [hsum_lhs, hsum_rhs] at hsum_b
    unfold g1TailSum
    apply (div_le_iff₀ hW_pos).mpr
    apply nat_sub_cast_le_of_le (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hdenom_pos.le) hW_pos.le)
    set S_tot := (g1Meta.map (fun b => b.2.2.1)).sum
    set E_tot := (g1Meta.map (fun b => b.2.2.2)).sum
    set lt := logNatHi Ntail
    have hNt_posR : (0 : ℝ) < Ntail := by exact_mod_cast (by decide : 0 < Ntail)
    have hmain : (((2 * 9400 * ratioScale * S_tot) / (10000 * harmScale) : Nat) : ℝ) ≤
        2 * 0.9400 * ((S_tot : ℝ) / harmScale) * ratioScale := by
      have hdiv := nat_div_cast_le (a := 2 * 9400 * ratioScale * S_tot) (b := 10000 * harmScale)
        (by decide)
      have heq : ((2 * 9400 * ratioScale * S_tot : Nat) : ℝ) / ((10000 * harmScale : Nat) : ℝ) =
          2 * 0.9400 * ((S_tot : ℝ) / harmScale) * ratioScale := by
        have hneH := hH_pos.ne'
        push_cast; field_simp; ring
      linarith
    have herr : 2 * (E_tot : ℝ) / ((n : ℝ) / Real.log n) * ratioScale ≤
        ((ceilDiv (2 * ratioScale * E_tot * lt) (logScale * Ntail) : Nat) : ℝ) := by
      have hceil := ceilDiv_cast_ge (a := 2 * ratioScale * E_tot * lt)
        (b := logScale * Ntail) (by decide)
      have h1 : 2 * (E_tot : ℝ) / ((n : ℝ) / Real.log n) * ratioScale =
          2 * (ratioScale : ℝ) * E_tot * (Real.log n / n) := by field_simp
      have h2 : 2 * (ratioScale : ℝ) * E_tot * (Real.log n / n) ≤
          2 * (ratioScale : ℝ) * E_tot * ((lt : ℝ) / logScale / Ntail) := by
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (mul_nonneg (by norm_num) hW_pos.le) (Nat.cast_nonneg _))
        exact hanti_t.trans (div_le_div_of_nonneg_right hlt_hi hNt_posR.le)
      have h3 : 2 * (ratioScale : ℝ) * E_tot * ((lt : ℝ) / logScale / Ntail) =
          ((2 * ratioScale * E_tot * lt : Nat) : ℝ) / ((logScale * Ntail : Nat) : ℝ) := by
        have hneS := hS_pos.ne'; have hneNt := hNt_posR.ne'
        push_cast; field_simp
      linarith
    have hdiv_b : 2 * 0.9400 * ((S_tot : ℝ) / harmScale) - 2 * (E_tot : ℝ) / ((n : ℝ) / Real.log n) ≤
        2 * ((g1Finsets.map (f1Count n)).sum : ℝ) / ((n : ℝ) / Real.log n) := by
      have h1 : 2 * (0.9400 * ((n : ℝ) / Real.log n) * (S_tot : ℝ) / harmScale - E_tot) ≤
          2 * ((g1Finsets.map (f1Count n)).sum : ℝ) := by linarith
      have h2 := div_le_div_of_nonneg_right h1 hdenom_pos.le
      have heq : 2 * (0.9400 * ((n : ℝ) / Real.log n) * (S_tot : ℝ) / harmScale - E_tot) / ((n : ℝ) / Real.log n) =
          2 * 0.9400 * ((S_tot : ℝ) / harmScale) - 2 * (E_tot : ℝ) / ((n : ℝ) / Real.log n) := by
        have hne1 := hn_pos.ne'; have hne2 := hlogn_pos.ne'
        field_simp
      linarith
    have hmul_b := mul_le_mul_of_nonneg_right hdiv_b hW_pos.le
    rw [sub_mul] at hmul_b
    linarith
  -- Family 2 tail lower bound: fixed U0_g = sqrt(Ntail / (20 * mhi))
  have hr2 : (g4TailSum : ℝ) / ratioScale ≤
      2 * ((Dgroups.map (fun g => f2Count n g.1 g.2.1 g.2.2)).sum : ℝ) / ((n : ℝ) / Real.log n) := by
    have hmeta_eq : g4TailSum =
        (g4Groups.map (fun g => g4TailTerm g.2.1 g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2.1)).sum := rfl
    rw [hmeta_eq, Nat.cast_list_sum, list_sum_div, List.map_map, List.map_map]
    have hsum2 : 2 * ((Dgroups.map (fun g => f2Count n g.1 g.2.1 g.2.2)).sum : ℝ) / ((n : ℝ) / Real.log n) =
        (g4Groups.map (fun g => 2 * (f2Count n g.2.2.2.2.2.2.toFinset g.2.2.2.2.1 (Nat.sqrt (Ntail / (20 * g.2.1))) : ℝ) /
          ((n : ℝ) / Real.log n))).sum := by
      dsimp only [Dgroups]
      rw [List.map_map, Nat.cast_list_sum, list_mul_sum, list_sum_div, List.map_map, List.map_map, List.map_map]
      rfl
    rw [hsum2]
    refine list_sum_real_le g4Groups _ _ fun g hg => ?_
    dsimp only [Function.comp_apply]
    obtain ⟨hmlo, hmhi, hL100, hL8k, hpiL, _, hcard, hmem, hharm⟩ := g4Group_valid_props (g4Groups_all_ok g hg)
    have hmhi_pos : 0 < g.2.1 := by
      simp only [g4Groups, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with h | h | h | h | h <;> (rw [h]; decide)
    have hU0_sq_le : Nat.sqrt (Ntail / (20 * g.2.1)) * Nat.sqrt (Ntail / (20 * g.2.1)) ≤ Ntail / (20 * g.2.1) :=
      Nat.sqrt_le (Ntail / (20 * g.2.1))
    have hU0_gt_L : g.2.2.2.2.1 < Nat.sqrt (Ntail / (20 * g.2.1)) := by
      have h1 : (8193 : Nat) * 8193 ≤ Ntail / (20 * 10000) := by decide
      have h2 : Ntail / (20 * 10000) ≤ Ntail / (20 * g.2.1) :=
        Nat.div_le_div_left (by omega) (by omega)
      have h3 : 8193 ≤ Nat.sqrt (Ntail / (20 * g.2.1)) := Nat.le_sqrt.mpr (h1.trans h2)
      omega
    have h101_U0 : 101 * g.2.1 * Nat.sqrt (Ntail / (20 * g.2.1)) ≤ Ntail := by
      have h1 : Nat.sqrt (Ntail / (20 * g.2.1)) ≤ 10 ^ 16 := by
        have hdiv_le : Ntail / (20 * g.2.1) ≤ 10 ^ 32 :=
          (Nat.div_le_self Ntail (20 * g.2.1)).trans (by decide : Ntail ≤ 10 ^ 32)
        have hsq : Nat.sqrt (Ntail / (20 * g.2.1)) * Nat.sqrt (Ntail / (20 * g.2.1)) ≤ 10 ^ 16 * 10 ^ 16 :=
          hU0_sq_le.trans (hdiv_le.trans (by decide : 10 ^ 32 ≤ 10 ^ 16 * 10 ^ 16))
        by_contra hbig; push Not at hbig
        have : 10 ^ 16 * 10 ^ 16 < Nat.sqrt (Ntail / (20 * g.2.1)) * Nat.sqrt (Ntail / (20 * g.2.1)) :=
          Nat.mul_lt_mul'' hbig hbig
        omega
      have hnt_big : 101 * 10000 * 10 ^ 16 ≤ Ntail := by decide
      exact (Nat.mul_le_mul (Nat.mul_le_mul_left 101 hmhi) h1).trans hnt_big
    have hHp := g4HpLo_sound hL100 hU0_gt_L hpiL
    have hpiU_le := g4PiUHi_sound (by omega : 1 ≤ Nat.sqrt (Ntail / (20 * g.2.1)))
    have hNt_posR : (0 : ℝ) < Ntail := by exact_mod_cast (by decide : 0 < Ntail)
    have hlt_hi' : Real.log (Ntail : ℝ) ≤ (logNatHi Ntail : ℝ) / logScale := hlt_hi
    unfold g4TailTerm
    dsimp only
    generalize hU0_eq : Nat.sqrt (Ntail / (20 * g.2.1)) = U0 at hU0_gt_L h101_U0 hHp hpiU_le ⊢
    generalize hHp_eq : g4HpLo g.2.2.2.2.1 g.2.2.2.2.2.1 U0 = Hp at hHp ⊢
    generalize hpiU_eq : g4PiUHi U0 = piU at hpiU_le ⊢
    generalize hlt_eq : logNatHi Ntail = lt at hlt_hi' ⊢
    clear hU0_eq hHp_eq hpiU_eq hlt_eq hU0_sq_le
    have hf2_ge : (∑ m ∈ g.2.2.2.2.2.2.toFinset, ∑ p ∈ (Ioc g.2.2.2.2.1 U0).filter Nat.Prime,
        ((n / (m * p)).primeCounting : ℝ)) - (g.2.2.1 : ℝ) * (piU : ℝ) ^ 2 ≤
        (f2Count n g.2.2.2.2.2.2.toFinset g.2.2.2.2.1 U0 : ℝ) := by
      have h1 : ∑ m ∈ g.2.2.2.2.2.2.toFinset, ∑ p ∈ (Ioc g.2.2.2.2.1 U0).filter Nat.Prime,
          (((n / (m * p)).primeCounting : ℝ) - (p.primeCounting : ℝ)) ≤
          (f2Count n g.2.2.2.2.2.2.toFinset g.2.2.2.2.1 U0 : ℝ) := by
        unfold f2Count; push_cast
        exact Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun p _ => nat_sub_cast_ge _ _
      simp_rw [Finset.sum_sub_distrib] at h1
      have hsub : ∑ m ∈ g.2.2.2.2.2.2.toFinset, ∑ p ∈ (Ioc g.2.2.2.2.1 U0).filter Nat.Prime, (p.primeCounting : ℝ) ≤
          (g.2.2.1 : ℝ) * (piU : ℝ) ^ 2 := by
        calc _ ≤ ∑ _m ∈ g.2.2.2.2.2.2.toFinset, (piU : ℝ) ^ 2 :=
              Finset.sum_le_sum fun _ _ => (sum_pi_primes_le_sq _ _).trans (pow_le_pow_left₀ (Nat.cast_nonneg _) hpiU_le 2)
          _ = (g.2.2.2.2.2.2.toFinset.card : ℝ) * (piU : ℝ) ^ 2 := by simp
          _ = (g.2.2.1 : ℝ) * (piU : ℝ) ^ 2 := by rw [hcard]
      linarith
    have hdouble : 0.9400 * ((n : ℝ) / Real.log n) * ((g.2.2.2.1 : ℝ) / harmScale) *
        ((Hp : ℝ) / ratioScale) ≤
        ∑ m ∈ g.2.2.2.2.2.2.toFinset, ∑ p ∈ (Ioc g.2.2.2.2.1 U0).filter Nat.Prime, ((n / (m * p)).primeCounting : ℝ) := by
      have hterm : ∀ m ∈ g.2.2.2.2.2.2.toFinset, ∀ p ∈ (Ioc g.2.2.2.2.1 U0).filter Nat.Prime,
          0.9400 * ((n : ℝ) / Real.log n) * ((1 : ℝ) / m) * ((1 : ℝ) / p) ≤ ((n / (m * p)).primeCounting : ℝ) := by
        intro m hm p hp
        obtain ⟨_, hm2, hmpos, _, _, _⟩ := hmem m (List.mem_toFinset.mp hm)
        obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
        obtain ⟨_, hpU⟩ := Finset.mem_Ioc.mp hpI
        have hmp_pos : 0 < m * p := Nat.mul_pos hmpos hpp.pos
        have hmpR_pos : (0 : ℝ) < ((m * p : Nat) : ℝ) := Nat.cast_pos.mpr hmp_pos
        have hxmp : (101 : ℝ) ≤ (n : ℝ) / ((m * p : Nat) : ℝ) := by
          rw [le_div_iff₀ hmpR_pos]
          have h1 : m * p ≤ g.2.1 * U0 := Nat.mul_le_mul hm2 hpU
          have h2 : 101 * (m * p) ≤ 101 * g.2.1 * U0 := by
            rw [Nat.mul_assoc]
            exact Nat.mul_le_mul_left 101 h1
          exact_mod_cast (h2.trans (h101_U0.trans hn))
        have hpi := pi_lower_all hxmp
        rw [floor_nat_div_eq] at hpi
        have hnmp_pos : (0 : ℝ) < (n : ℝ) / ((m * p : Nat) : ℝ) := div_pos hn_pos hmpR_pos
        have hlog_nmp_pos : 0 < Real.log ((n : ℝ) / ((m * p : Nat) : ℝ)) := Real.log_pos (by linarith)
        have hlog_le : Real.log ((n : ℝ) / ((m * p : Nat) : ℝ)) ≤ Real.log n :=
          Real.log_le_log hnmp_pos (div_le_self hn_pos.le (by exact_mod_cast hmp_pos))
        have h1 : ((n : ℝ) / ((m * p : Nat) : ℝ)) / Real.log n ≤
            ((n : ℝ) / ((m * p : Nat) : ℝ)) / Real.log ((n : ℝ) / ((m * p : Nat) : ℝ)) :=
          div_le_div_of_nonneg_left hnmp_pos.le hlog_nmp_pos hlog_le
        have h2 : 0 ≤ ((n : ℝ) / ((m * p : Nat) : ℝ)) / (Real.log ((n : ℝ) / ((m * p : Nat) : ℝ))) ^ 2 :=
          div_nonneg hnmp_pos.le (sq_nonneg _)
        have heq : 0.9400 * ((n : ℝ) / Real.log n) * ((1 : ℝ) / m) * ((1 : ℝ) / p) =
            0.9400 * (((n : ℝ) / ((m * p : Nat) : ℝ)) / Real.log n) := by
          have hmR : (m : ℝ) ≠ 0 := (Nat.cast_pos.mpr hmpos).ne'
          have hpR : (p : ℝ) ≠ 0 := (Nat.cast_pos.mpr hpp.pos).ne'
          have hln : Real.log n ≠ 0 := hlogn_pos.ne'
          rw [Nat.cast_mul]; field_simp
        linarith
      calc _ ≤ 0.9400 * ((n : ℝ) / Real.log n) * (∑ m ∈ g.2.2.2.2.2.2.toFinset, (1 : ℝ) / m) *
              (∑ p ∈ (Ioc g.2.2.2.2.1 U0).filter Nat.Prime, (1 : ℝ) / p) := by
            have h1 := mul_le_mul hharm hHp (div_nonneg (Nat.cast_nonneg _) hW_pos.le)
              (Finset.sum_nonneg fun _ _ => div_nonneg (by norm_num) (Nat.cast_nonneg _))
            have h2 := mul_le_mul_of_nonneg_left h1 (mul_nonneg (show (0 : ℝ) ≤ 0.9400 by norm_num) hdenom_pos.le)
            simpa only [mul_assoc] using h2
        _ = ∑ m ∈ g.2.2.2.2.2.2.toFinset, ∑ p ∈ (Ioc g.2.2.2.2.1 U0).filter Nat.Prime,
              (0.9400 * ((n : ℝ) / Real.log n) * ((1 : ℝ) / m) * ((1 : ℝ) / p)) := by
            rw [show 0.9400 * ((n : ℝ) / Real.log n) * (∑ m ∈ g.2.2.2.2.2.2.toFinset, (1 : ℝ) / m) =
                ∑ m ∈ g.2.2.2.2.2.2.toFinset, (0.9400 * ((n : ℝ) / Real.log n) * ((1 : ℝ) / m)) by
              rw [Finset.mul_sum]]
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum fun m hm => Finset.sum_le_sum fun p hp => hterm m hm p hp
    apply (div_le_iff₀ hW_pos).mpr
    apply nat_sub_cast_le_of_le (mul_nonneg (div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) hdenom_pos.le) hW_pos.le)
    have hmain : (((2 * 9400 * g.2.2.2.1 * Hp) / (10000 * harmScale) : Nat) : ℝ) ≤
        2 * 0.9400 * ((g.2.2.2.1 : ℝ) / harmScale) * ((Hp : ℝ) / ratioScale) * ratioScale := by
      have hdiv := nat_div_cast_le (a := 2 * 9400 * g.2.2.2.1 * Hp)
        (b := 10000 * harmScale) (by decide)
      have heq : ((2 * 9400 * g.2.2.2.1 * Hp : Nat) : ℝ) / ((10000 * harmScale : Nat) : ℝ) =
          2 * 0.9400 * ((g.2.2.2.1 : ℝ) / harmScale) * ((Hp : ℝ) / ratioScale) * ratioScale := by
        have hneW := hW_pos.ne'; have hneH := hH_pos.ne'
        push_cast; field_simp; ring
      linarith
    have herr : 2 * ((g.2.2.1 : ℝ) * (piU : ℝ) ^ 2) / ((n : ℝ) / Real.log n) * ratioScale ≤
        ((ceilDiv (2 * ratioScale * g.2.2.1 * piU * piU * lt) (logScale * Ntail) : Nat) : ℝ) := by
      have hceil := ceilDiv_cast_ge (a := 2 * ratioScale * g.2.2.1 * piU * piU * lt)
        (b := logScale * Ntail) (by decide)
      have h1 : 2 * ((g.2.2.1 : ℝ) * (piU : ℝ) ^ 2) / ((n : ℝ) / Real.log n) * ratioScale =
          2 * (ratioScale : ℝ) * g.2.2.1 * (piU : ℝ) ^ 2 * (Real.log n / n) := by
        have hne1 := hn_pos.ne'; have hne2 := hlogn_pos.ne'
        field_simp
      have h2 : 2 * (ratioScale : ℝ) * g.2.2.1 * (piU : ℝ) ^ 2 * (Real.log n / n) ≤
          2 * (ratioScale : ℝ) * g.2.2.1 * (piU : ℝ) ^ 2 * ((lt : ℝ) / logScale / Ntail) := by
        apply mul_le_mul_of_nonneg_left _
          (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hW_pos.le) (Nat.cast_nonneg _)) (sq_nonneg _))
        exact hanti_t.trans (div_le_div_of_nonneg_right hlt_hi' hNt_posR.le)
      have h3 : 2 * (ratioScale : ℝ) * g.2.2.1 * (piU : ℝ) ^ 2 * ((lt : ℝ) / logScale / Ntail) =
          ((2 * ratioScale * g.2.2.1 * piU * piU * lt : Nat) : ℝ) /
            ((logScale * Ntail : Nat) : ℝ) := by
        have hneS := hS_pos.ne'; have hneNt := hNt_posR.ne'
        push_cast; field_simp
      linarith
    have hdiv_g : 2 * 0.9400 * ((g.2.2.2.1 : ℝ) / harmScale) * ((Hp : ℝ) / ratioScale) -
        2 * ((g.2.2.1 : ℝ) * (piU : ℝ) ^ 2) / ((n : ℝ) / Real.log n) ≤
        2 * (f2Count n g.2.2.2.2.2.2.toFinset g.2.2.2.2.1 U0 : ℝ) / ((n : ℝ) / Real.log n) := by
      have h1 : 2 * (0.9400 * ((n : ℝ) / Real.log n) * ((g.2.2.2.1 : ℝ) / harmScale) *
          ((Hp : ℝ) / ratioScale) - (g.2.2.1 : ℝ) * (piU : ℝ) ^ 2) ≤
          2 * (f2Count n g.2.2.2.2.2.2.toFinset g.2.2.2.2.1 U0 : ℝ) := by linarith
      have h2 := div_le_div_of_nonneg_right h1 hdenom_pos.le
      have heq : 2 * (0.9400 * ((n : ℝ) / Real.log n) * ((g.2.2.2.1 : ℝ) / harmScale) *
          ((Hp : ℝ) / ratioScale) - (g.2.2.1 : ℝ) * (piU : ℝ) ^ 2) /
          ((n : ℝ) / Real.log n) =
          2 * 0.9400 * ((g.2.2.2.1 : ℝ) / harmScale) * ((Hp : ℝ) / ratioScale) -
          2 * ((g.2.2.1 : ℝ) * (piU : ℝ) ^ 2) / ((n : ℝ) / Real.log n) := by
        have hne1 := hn_pos.ne'; have hne2 := hlogn_pos.ne'
        field_simp
      linarith
    have hmul_g := mul_le_mul_of_nonneg_right hdiv_g hW_pos.le
    rw [sub_mul] at hmul_g
    linarith
  have hchkR : (lhsHi Ntail : ℝ) / ratioScale ≤ (g1TailSum : ℝ) / ratioScale + (g4TailSum : ℝ) / ratioScale := by
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast tailCheck.down) hW_pos.le
  have htot : (n.primeCounting : ℝ) / ((n : ℝ) / Real.log n) ≤
      2 * ((countRefactorableNat n : Nat) : ℝ) / ((n : ℝ) / Real.log n) := by
    have hdisjR : ((g1Finsets.map (f1Count n)).sum : ℝ) +
        ((Dgroups.map (fun g => f2Count n g.1 g.2.1 g.2.2)).sum : ℝ) ≤ (countRefactorableNat n : ℝ) := by
      exact_mod_cast hdisj
    have hdiv_disj : 2 * ((g1Finsets.map (f1Count n)).sum : ℝ) / ((n : ℝ) / Real.log n) +
        2 * ((Dgroups.map (fun g => f2Count n g.1 g.2.1 g.2.2)).sum : ℝ) / ((n : ℝ) / Real.log n) ≤
        2 * (countRefactorableNat n : ℝ) / ((n : ℝ) / Real.log n) := by
      rw [← add_div, ← mul_add]
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hdisjR (by norm_num)) hdenom_pos.le
    linarith
  have hfinal : (n.primeCounting : ℝ) ≤ 2 * (countRefactorableNat n : ℝ) :=
    (div_le_div_iff_of_pos_right hdenom_pos).mp htot
  exact_mod_cast hfinal

theorem colton_all : ∀ n : Nat, n.primeCounting ≤ 2 * countRefactorableNat n := by
  intro n
  by_cases h1 : n ≤ 14090240
  · exact colton_le_14M n h1
  · by_cases h2 : n ≤ Ntail
    · exact colton_mid_14M_1e32 n (by omega) h2
    · exact colton_ge_1e32 n (by omega)

end ColtonTail


theorem OMA.solution : type_of% @OeisA111291.colton_conjecture := by
  intro n
  exact ColtonTail.colton_all n
