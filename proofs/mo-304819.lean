import OMAStatements.S_mo_304819
import Mathlib

/-!
# Proof of MathOverflow 304819

For `n ≥ 2`, `1 ≤ α ≤ 2`, and `n` points `B : Fin n → ℂ` on the unit circle,
`∑_{i < j} ‖B i - B j‖ ^ α ≤ ∑_{i < j} ‖ζ i - ζ j‖ ^ α`,
where `ζ i = exp(2πi * i / n)` is the regular `n`-gon.

## Proof structure
1. **Case `α = 2`**: `∑_{i, j} ‖B i - B j‖ ^ 2 = 2 * n ^ 2 - 2 * ‖∑ i, B i‖ ^ 2 ≤ 2 * n ^ 2`,
   with equality for `ζ`.
2. **Case `1 ≤ α < 2`** (in fact all `0 < α < 2`):
   - Set `s = α / 2 ∈ (0, 1)`. Using `u`-substitution `λ = x * u`, for every `x ≥ 0`:
     `∫ λ ∈ Ioi 0, (x / (x + λ)) * λ ^ (s - 1) = x ^ s * C_s` with `C_s > 0`.
   - Since `‖z - w‖ ^ 2 + λ = 2 * ((1 + λ / 2) - (z * conj w).re)`, it suffices to prove for
     every fixed `a > 1`:
     `∑_{i ≠ j} 1 / (a - (B i * conj (B j)).re) ≥ ∑_{i ≠ j} 1 / (a - (ζ i * conj (ζ j)).re)`.
   - Define the Fejer kernel `Q n t = n + 2 * ∑_{k=1}^{n-1} (n - k) * T k t`.
     It satisfies `(1 - t) * Q n t = 1 - T n t`, hence `Q n t ≥ 0` on `[-1, 1]`,
     `Q n (cos(2πk/n)) = 0` for `1 ≤ k < n`, and `Q n a > 0` for `a > 1`.
   - The polynomial `P_a t = (Q n a - Q n t) / (Q n a * (a - t))` satisfies `P_a t ≤ 1 / (a - t)`
     on `[-1, 1]` with equality at `cos(2πk/n)` (`1 ≤ k < n`).
   - By the identity `T k a - T k t = (a - t) * (U (k-1) a + 2 * ∑_{j=1}^{k-1} U (k-1-j) a * T j t)`
     with `U m a > 0` for `a > 1`, every Chebyshev coefficient of `P_a` for `1 ≤ j ≤ n - 2`
     is positive, and `∑_{i, l} T j (B i * conj (B l)).re = ‖∑ i, B i ^ j‖ ^ 2 ≥ 0` vanishes
     at the regular `n`-gon `ζ` for `1 ≤ j < n`.
-/

namespace OMA.MO304819

open Finset BigOperators MeasureTheory

/-! ### Section 1: Chebyshev functions `T` and `U` -/

private def T : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => x
  | k + 2, x => 2 * x * T (k + 1) x - T k x

private def U : ℕ → ℝ → ℝ
  | 0, _ => 1
  | 1, x => 2 * x
  | k + 2, x => 2 * x * U (k + 1) x - U k x

private lemma T_one (k : ℕ) : T k 1 = 1 := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => rfl
    | 1 => rfl
    | k + 2 =>
      simp only [T]
      rw [ih (k + 1) (by omega), ih k (by omega)]
      ring

private lemma T_cos (k : ℕ) (θ : ℝ) : T k (Real.cos θ) = Real.cos (k * θ) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => simp [T]
    | 1 => simp [T]
    | k + 2 =>
      simp only [T]
      rw [ih (k + 1) (by omega), ih k (by omega)]
      have h1 : ((k + 2 : ℕ) : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ + θ := by push_cast; ring
      have h2 : (k : ℝ) * θ = ((k + 1 : ℕ) : ℝ) * θ - θ := by push_cast; ring
      rw [h1, h2, Real.cos_add, Real.cos_sub]
      ring

private lemma T_le_one {t : ℝ} (ht1 : -1 ≤ t) (ht2 : t ≤ 1) (k : ℕ) : T k t ≤ 1 := by
  have hcos : Real.cos (Real.arccos t) = t := Real.cos_arccos ht1 ht2
  rw [← hcos, T_cos]
  exact Real.cos_le_one _

private lemma T_ge_one_of_one_lt {a : ℝ} (ha : 1 < a) :
    ∀ k : ℕ, 1 ≤ T k a ∧ T k a ≤ T (k + 1) a
  | 0 => by simp only [T]; exact ⟨le_rfl, ha.le⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := T_ge_one_of_one_lt ha k
    have hstep : T (k + 1) a ≤ T (k + 2) a := by
      simp only [T]
      nlinarith
    exact ⟨h1.trans h2, hstep⟩

private lemma U_ge_one_of_one_lt {a : ℝ} (ha : 1 < a) :
    ∀ k : ℕ, 1 ≤ U k a ∧ U k a ≤ U (k + 1) a
  | 0 => by simp only [U]; constructor <;> linarith
  | k + 1 => by
    obtain ⟨h1, h2⟩ := U_ge_one_of_one_lt ha k
    have hstep : U (k + 1) a ≤ U (k + 2) a := by
      simp only [U]
      nlinarith
    exact ⟨h1.trans h2, hstep⟩

private lemma U_pos_of_one_lt {a : ℝ} (ha : 1 < a) (k : ℕ) : 0 < U k a :=
  lt_of_lt_of_le zero_lt_one (U_ge_one_of_one_lt ha k).1

private lemma T_re_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) (k : ℕ) :
    T k u.re = (u ^ k).re := by
  have hnorm2 : u.re * u.re + u.im * u.im = 1 := by
    have h := congrArg (fun x : ℝ => x ^ 2) hu
    rw [Complex.sq_norm, Complex.normSq_apply] at h
    simpa using h
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => simp [T]
    | 1 => simp [T]
    | k + 2 =>
      simp only [T]
      rw [ih (k + 1) (by omega), ih k (by omega)]
      have h1 : (u ^ (k + 2)).re = (u ^ (k + 1)).re * u.re - (u ^ (k + 1)).im * u.im := by
        rw [pow_succ, Complex.mul_re]
      have h2 : (u ^ k).re = (u ^ (k + 1)).re * u.re + (u ^ (k + 1)).im * u.im := by
        rw [pow_succ, Complex.mul_re, Complex.mul_im]
        linear_combination -(u ^ k).re * hnorm2
      linarith

private lemma T_re_mul_conj {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) (k : ℕ) :
    T k (z * starRingEnd ℂ w).re = (z ^ k * starRingEnd ℂ (w ^ k)).re := by
  have hnorm : ‖z * starRingEnd ℂ w‖ = 1 := by
    rw [norm_mul, Complex.norm_conj, hz, hw, mul_one]
  rw [T_re_of_norm_eq_one hnorm k, mul_pow, ← map_pow]

/-! ### Section 2: Divided-difference identity for `T` and Fejer kernel `Q` -/

private def W (k : ℕ) (a t : ℝ) : ℝ :=
  if k = 0 then 0
  else U (k - 1) a + 2 * ∑ j ∈ Ico 1 k, U (k - 1 - j) a * T j t

private lemma W_one (a t : ℝ) : W 1 a t = 1 := by
  simp [W, U]

private lemma W_two (a t : ℝ) : W 2 a t = 2 * a + 2 * t := by
  have h12 : Ico 1 2 = {1} := by decide
  simp [W, h12, U, T]

private lemma W_rec (k : ℕ) (hk : 1 ≤ k) (a t : ℝ) :
    W (k + 2) a t - 2 * a * W (k + 1) a t + W k a t = 2 * T (k + 1) t := by
  have hk0 : k ≠ 0 := by omega
  have h1 : Ico 1 (k + 2) = insert (k + 1) (insert k (Ico 1 k)) := by
    ext j; simp only [mem_Ico, mem_insert]; omega
  have h2 : Ico 1 (k + 1) = insert k (Ico 1 k) := by
    ext j; simp only [mem_Ico, mem_insert]; omega
  have hnot1 : k + 1 ∉ insert k (Ico 1 k) := by simp
  have hnot2 : k ∉ Ico 1 k := by simp
  simp only [W, hk0, Nat.add_eq_zero_iff, one_ne_zero, and_false, false_and, ↓reduceIte,
    Nat.add_sub_cancel]
  rw [h1, sum_insert hnot1, sum_insert hnot2, h2, sum_insert hnot2]
  have hsub0 : k + 2 - 1 = k + 1 := by omega
  have hsub1 : k + 1 - (k + 1) = 0 := by omega
  have hsub2 : k + 1 - k = 1 := by omega
  have hsub3 : k - k = 0 := by omega
  rw [hsub0, hsub1, hsub2, hsub3]
  have hU_head : U (k + 1) a - 2 * a * U k a + U (k - 1) a = 0 := by
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    simp only [Nat.add_sub_cancel, U]; ring
  have hsum :
      ∑ j ∈ Ico 1 k, U (k + 1 - j) a * T j t -
        2 * a * ∑ j ∈ Ico 1 k, U (k - j) a * T j t +
        ∑ j ∈ Ico 1 k, U (k - 1 - j) a * T j t = 0 := by
    rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_eq_zero fun j hj => ?_
    have hj1 : 1 ≤ j := (mem_Ico.mp hj).1
    have hjk : j < k := (mem_Ico.mp hj).2
    obtain ⟨m, hm⟩ : ∃ m, k - 1 - j = m := ⟨k - 1 - j, rfl⟩
    have hm1 : k - j = m + 1 := by omega
    have hm2 : k + 1 - j = m + 2 := by omega
    rw [hm, hm1, hm2, U]
    ring
  simp only [U] at hU_head ⊢
  linarith

private lemma T_sub_eq_mul_W (k : ℕ) (a t : ℝ) :
    T k a - T k t = (a - t) * W k a t := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    match k with
    | 0 => simp [T, W]
    | 1 => simp [T, W_one]
    | 2 => simp [T, W_two]; ring
    | k + 3 =>
      have hrec := W_rec (k + 1) (by omega) a t
      have ih1 := ih (k + 2) (by omega)
      have ih2 := ih (k + 1) (by omega)
      have hW : W (k + 3) a t = 2 * a * W (k + 2) a t - W (k + 1) a t + 2 * T (k + 2) t := by
        linarith
      have hTa : T (k + 3) a = 2 * a * T (k + 2) a - T (k + 1) a := rfl
      have hTt : T (k + 3) t = 2 * t * T (k + 2) t - T (k + 1) t := rfl
      rw [hTa, hTt, hW]
      linear_combination 2 * a * ih1 - ih2

private def Q (n : ℕ) (t : ℝ) : ℝ :=
  (n : ℝ) + 2 * ∑ k ∈ Ico 1 n, ((n - k : ℕ) : ℝ) * T k t

private lemma Q_succ_sub (n : ℕ) (t : ℝ) :
    Q (n + 1) t - Q n t = 1 + 2 * ∑ k ∈ Ico 1 (n + 1), T k t := by
  unfold Q
  rcases n with _ | n
  · simp
  · have hsplit : Ico 1 (n + 2) = insert (n + 1) (Ico 1 (n + 1)) := by
      ext k; simp only [mem_Ico, mem_insert]; omega
    have hnot : n + 1 ∉ Ico 1 (n + 1) := by simp
    rw [hsplit, sum_insert hnot, sum_insert hnot]
    have hcast : ∀ k ∈ Ico 1 (n + 1),
        (((n + 2 - k : ℕ) : ℝ) * T k t) = (((n + 1 - k : ℕ) : ℝ) * T k t + T k t) := by
      intro k hk
      have hkle : k ≤ n + 1 := (mem_Ico.mp hk).2.le
      have hnat : n + 2 - k = (n + 1 - k) + 1 := by omega
      rw [hnat]; push_cast; ring
    rw [sum_congr rfl hcast, sum_add_distrib]
    have h1 : ((n + 2 - (n + 1) : ℕ) : ℝ) = 1 := by norm_num
    rw [h1]; push_cast; ring

private lemma one_sub_mul_sum_T (n : ℕ) (t : ℝ) :
    (1 - t) * (1 + 2 * ∑ k ∈ Ico 1 (n + 1), T k t) = T n t - T (n + 1) t := by
  induction n with
  | zero => simp [T]
  | succ n ih =>
    have hsplit : Ico 1 (n + 2) = insert (n + 1) (Ico 1 (n + 1)) := by
      ext k; simp only [mem_Ico, mem_insert]; omega
    have hnot : n + 1 ∉ Ico 1 (n + 1) := by simp
    rw [hsplit, sum_insert hnot]
    have hrec : T (n + 2) t = 2 * t * T (n + 1) t - T n t := rfl
    linear_combination ih + hrec

private lemma one_sub_mul_Q (n : ℕ) (hn : 1 ≤ n) (t : ℝ) :
    (1 - t) * Q n t = 1 - T n t := by
  induction n, hn using Nat.le_induction with
  | base => simp [Q, T]
  | succ n hn ih =>
    have hdiff := Q_succ_sub n t
    have hstep := one_sub_mul_sum_T n t
    have hQ : Q (n + 1) t = Q n t + (1 + 2 * ∑ k ∈ Ico 1 (n + 1), T k t) := by linarith
    rw [hQ, mul_add, ih, hstep]
    ring

private lemma Q_nonneg_of_mem_Icc {n : ℕ} (hn : 1 ≤ n) {t : ℝ} (ht1 : -1 ≤ t) (ht2 : t ≤ 1) :
    0 ≤ Q n t := by
  rcases eq_or_lt_of_le ht2 with rfl | hlt
  · unfold Q
    have hsum : 0 ≤ ∑ k ∈ Ico 1 n, ((n - k : ℕ) : ℝ) * T k 1 := by
      refine sum_nonneg fun k _ => ?_
      rw [T_one]; positivity
    positivity
  · have hpos : 0 < 1 - t := by linarith
    have hprod : 0 ≤ (1 - t) * Q n t := by
      rw [one_sub_mul_Q n hn t]
      linarith [T_le_one ht1 ht2 n]
    exact nonneg_of_mul_nonneg_right hprod hpos

private lemma Q_pos_of_one_lt {n : ℕ} (hn : 1 ≤ n) {a : ℝ} (ha : 1 < a) : 0 < Q n a := by
  unfold Q
  have hsum : 0 ≤ ∑ k ∈ Ico 1 n, ((n - k : ℕ) : ℝ) * T k a := by
    refine sum_nonneg fun k _ => ?_
    have hT : 0 ≤ T k a := le_trans zero_le_one (T_ge_one_of_one_lt ha k).1
    positivity
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
  linarith

private lemma Q_cos_root {n : ℕ} (hn : 2 ≤ n) {k : ℕ} (hk1 : 1 ≤ k) (hk2 : k < n) :
    Q n (Real.cos (2 * Real.pi * k / n)) = 0 := by
  have hangle_pos : 0 < 2 * Real.pi * k / n := by
    have : (0 : ℝ) < k := Nat.cast_pos.mpr (by omega)
    have : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    positivity
  have hangle_lt : 2 * Real.pi * k / n < 2 * Real.pi := by
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
    have hkn : (k : ℝ) < n := Nat.cast_lt.mpr hk2
    rw [div_lt_iff₀ hn0]
    nlinarith [Real.pi_pos]
  have hcos_lt : Real.cos (2 * Real.pi * k / n) < 1 := by
    rcases lt_or_ge (2 * Real.pi * k / n) Real.pi with h | h
    · have := Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le)
        ⟨hangle_pos.le, h.le⟩ hangle_pos
      simpa [Real.cos_zero] using this
    · have h2 : 2 * Real.pi - 2 * Real.pi * k / n ∈ Set.Icc 0 Real.pi := by
        constructor <;> linarith
      have hpos2 : 0 < 2 * Real.pi - 2 * Real.pi * k / n := by linarith
      have := Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le) h2 hpos2
      rw [Real.cos_two_pi_sub, Real.cos_zero] at this
      exact this
  have hprod := one_sub_mul_Q n (by omega) (Real.cos (2 * Real.pi * k / n))
  rw [T_cos] at hprod
  have harg : (n : ℝ) * (2 * Real.pi * k / n) = (k : ℕ) * (2 * Real.pi) := by
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    field_simp
  rw [harg, Real.cos_nat_mul_two_pi, sub_self] at hprod
  exact (mul_eq_zero.mp hprod).resolve_left (by linarith)

/-! ### Section 3: Fixed-`a` potential inequality via `Q` and `W` -/

private noncomputable def regPt (n : ℕ) (i : Fin n) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (i : ℕ) / (n : ℕ))

private lemma norm_regPt (n : ℕ) (i : Fin n) : ‖regPt n i‖ = 1 := by
  unfold regPt
  have h : (2 * Real.pi * Complex.I * (i : ℕ) / (n : ℕ) : ℂ) =
      (((2 * Real.pi * (i : ℕ) / (n : ℕ) : ℝ) : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

private lemma sum_regPt_pow_eq_zero {n j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n) :
    ∑ i : Fin n, regPt n i ^ j = 0 := by
  let ω : ℂ := Complex.exp (2 * Real.pi * Complex.I * (j : ℕ) / (n : ℕ))
  have hpow : ∀ i : Fin n, regPt n i ^ j = ω ^ (i : ℕ) := by
    intro i
    unfold regPt
    rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul]
    congr 1; ring
  simp_rw [hpow]
  rw [Fin.sum_univ_eq_sum_range (fun k => ω ^ k) n]
  have hω_ne : ω ≠ 1 := by
    intro heq
    have hre := congrArg Complex.re heq
    have harg : (2 * Real.pi * Complex.I * (j : ℕ) / (n : ℕ) : ℂ) =
        (((2 * Real.pi * (j : ℕ) / (n : ℕ) : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    have hcos : Real.cos (2 * Real.pi * j / n) = 1 := by
      have hωeq : ω = Complex.exp (((2 * Real.pi * (j : ℕ) / (n : ℕ) : ℝ) : ℂ) * Complex.I) := by
        dsimp only [ω]; rw [harg]
      rw [hωeq, Complex.exp_ofReal_mul_I_re] at hre
      exact hre
    have hpos : 0 < 2 * Real.pi * j / n := by
      have : (0 : ℝ) < j := Nat.cast_pos.mpr (by omega)
      have : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      positivity
    have hlt : 2 * Real.pi * j / n < 2 * Real.pi := by
      have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (by omega)
      have hjn' : (j : ℝ) < n := Nat.cast_lt.mpr hjn
      rw [div_lt_iff₀ hn0]
      nlinarith [Real.pi_pos]
    rcases lt_or_ge (2 * Real.pi * j / n) Real.pi with h | h
    · have := Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le) ⟨hpos.le, h.le⟩ hpos
      rw [Real.cos_zero] at this; linarith
    · have h2 : 2 * Real.pi - 2 * Real.pi * j / n ∈ Set.Icc 0 Real.pi := by
        constructor <;> linarith
      have := Real.strictAntiOn_cos (Set.left_mem_Icc.mpr Real.pi_pos.le) h2 (by linarith)
      rw [Real.cos_two_pi_sub, Real.cos_zero] at this; linarith
  have hωn : ω ^ n = 1 := by
    dsimp only [ω]
    rw [← Complex.exp_nat_mul]
    have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hmul : (n : ℂ) * (2 * ↑Real.pi * Complex.I * ↑j / ↑n) = ↑j * (2 * ↑Real.pi * Complex.I) := by
      field_simp
    rw [hmul, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
  have hgeom := mul_geom_sum ω n
  rw [hωn, sub_self] at hgeom
  exact (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr hω_ne)

private lemma sum_T_re_nonneg {n : ℕ} (B : Fin n → ℂ) (hB : ∀ i, ‖B i‖ = 1) (j : ℕ) :
    ∑ i : Fin n, ∑ l : Fin n, T j (B i * starRingEnd ℂ (B l)).re =
      ‖∑ i : Fin n, B i ^ j‖ ^ 2 := by
  have hterm : ∀ i l : Fin n,
      T j (B i * starRingEnd ℂ (B l)).re = (B i ^ j * starRingEnd ℂ (B l ^ j)).re :=
    fun i l => T_re_mul_conj (hB i) (hB l) j
  simp_rw [hterm]
  rw [Complex.sq_norm]
  have hre : ((starRingEnd ℂ (∑ i : Fin n, B i ^ j)) * (∑ i : Fin n, B i ^ j)).re =
      (∑ i : Fin n, ∑ l : Fin n, B i ^ j * starRingEnd ℂ (B l ^ j)).re := by
    rw [mul_comm, map_sum, sum_mul]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [mul_sum]
  have hreal : Complex.re (starRingEnd ℂ (∑ i : Fin n, B i ^ j) * ∑ i : Fin n, B i ^ j) =
      Complex.normSq (∑ i : Fin n, B i ^ j) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
  rw [← hreal, hre]
  simp only [Complex.re_sum]

private lemma regPt_mul_conj_re {n : ℕ} (_hn : 2 ≤ n) (i l : Fin n) (hil : i ≠ l) :
    ∃ k : ℕ, 1 ≤ k ∧ k < n ∧
      (regPt n i * starRingEnd ℂ (regPt n l)).re = Real.cos (2 * Real.pi * k / n) := by
  have h1 : regPt n i * starRingEnd ℂ (regPt n l) =
      Complex.exp (((2 * Real.pi * ((i : ℤ) - (l : ℤ)) / (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    unfold regPt
    have hconj : starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I * (l : ℕ) / (n : ℕ))) =
        Complex.exp (-(2 * Real.pi * Complex.I * (l : ℕ) / (n : ℕ))) := by
      rw [← Complex.exp_conj]
      congr 1
      simp [map_div₀, map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [hconj, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [h1, Complex.exp_ofReal_mul_I_re]
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hil) with hlt | hgt
  · refine ⟨(l : ℕ) - (i : ℕ), by omega, by omega, ?_⟩
    rw [← Real.cos_neg]
    congr 1
    have hcast : ((l : ℕ) - (i : ℕ) : ℕ) = ((l : ℤ) - (i : ℤ)) := by omega
    have hcastR : (((l : ℕ) - (i : ℕ) : ℕ) : ℝ) = ((l : ℕ) : ℝ) - ((i : ℕ) : ℝ) := by
      exact Nat.cast_sub hlt.le
    rw [hcastR]; push_cast; ring
  · refine ⟨(i : ℕ) - (l : ℕ), by omega, by omega, ?_⟩
    congr 1
    have hcastR : (((i : ℕ) - (l : ℕ) : ℕ) : ℝ) = ((i : ℕ) : ℝ) - ((l : ℕ) : ℝ) := by
      exact Nat.cast_sub hgt.le
    rw [hcastR]; push_cast; ring

private lemma re_mul_conj_mem_Icc {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    -1 ≤ (z * starRingEnd ℂ w).re ∧ (z * starRingEnd ℂ w).re ≤ 1 := by
  have habs : |(z * starRingEnd ℂ w).re| ≤ 1 := by
    calc |(z * starRingEnd ℂ w).re|
        ≤ ‖z * starRingEnd ℂ w‖ := Complex.abs_re_le_norm _
      _ = 1 := by rw [norm_mul, Complex.norm_conj, hz, hw, mul_one]
  exact abs_le.mp habs

private lemma inv_sub_re_sum_ge {n : ℕ} (hn : 2 ≤ n) {a : ℝ} (ha : 1 < a)
    (B : Fin n → ℂ) (hB : ∀ i, ‖B i‖ = 1) :
    ∑ i : Fin n, ∑ l : Fin n, (if i ≠ l then (a - (regPt n i * starRingEnd ℂ (regPt n l)).re)⁻¹ else 0) ≤
    ∑ i : Fin n, ∑ l : Fin n, (if i ≠ l then (a - (B i * starRingEnd ℂ (B l)).re)⁻¹ else 0) := by
  have hQa : 0 < Q n a := Q_pos_of_one_lt (by omega) ha
  let P : ℝ → ℝ := fun t =>
    (2 / Q n a) * ∑ k ∈ Ico 1 n, ((n - k : ℕ) : ℝ) * W k a t
  have hP_eq : ∀ t : ℝ, (a - t) * P t = 1 - Q n t / Q n a := by
    intro t
    have hQdiff : Q n a - Q n t =
        2 * (a - t) * ∑ k ∈ Ico 1 n, ((n - k : ℕ) : ℝ) * W k a t := by
      unfold Q
      have : (n : ℝ) + 2 * ∑ k ∈ Ico 1 n, ((n - k : ℕ) : ℝ) * T k a -
          ((n : ℝ) + 2 * ∑ k ∈ Ico 1 n, ((n - k : ℕ) : ℝ) * T k t) =
          ∑ k ∈ Ico 1 n, 2 * ((n - k : ℕ) : ℝ) * (T k a - T k t) := by
        rw [← sub_sub, add_sub_cancel_left, ← mul_sub, ← sum_sub_distrib, mul_sum]
        refine sum_congr rfl fun k _ => by ring
      rw [this, mul_sum]
      refine sum_congr rfl fun k _ => by rw [T_sub_eq_mul_W]; ring
    dsimp only [P]
    have hQa0 : Q n a ≠ 0 := hQa.ne'
    calc (a - t) * ((2 / Q n a) * ∑ k ∈ Ico 1 n, ((n - k : ℕ) : ℝ) * W k a t)
        = (2 * (a - t) * ∑ k ∈ Ico 1 n, ((n - k : ℕ) : ℝ) * W k a t) / Q n a := by ring
      _ = (Q n a - Q n t) / Q n a := by rw [← hQdiff]
      _ = 1 - Q n t / Q n a := by rw [sub_div, div_self hQa0]
  have hP_le : ∀ t : ℝ, -1 ≤ t → t ≤ 1 → P t ≤ (a - t)⁻¹ := by
    intro t ht1 ht2
    have hpos : 0 < a - t := by linarith
    have hmul : (a - t) * P t ≤ 1 := by
      rw [hP_eq]
      have hQt : 0 ≤ Q n t := Q_nonneg_of_mem_Icc (by omega) ht1 ht2
      have : 0 ≤ Q n t / Q n a := div_nonneg hQt hQa.le
      linarith
    have hmul' : (a - t) * P t ≤ (a - t) * (a - t)⁻¹ := by
      rwa [mul_inv_cancel₀ hpos.ne']
    exact le_of_mul_le_mul_left hmul' hpos
  have hP_reg : ∀ i l : Fin n, i ≠ l →
      P (regPt n i * starRingEnd ℂ (regPt n l)).re =
        (a - (regPt n i * starRingEnd ℂ (regPt n l)).re)⁻¹ := by
    intro i l hil
    obtain ⟨k, hk1, hk2, hcos⟩ := regPt_mul_conj_re hn i l hil
    have hQt : Q n (regPt n i * starRingEnd ℂ (regPt n l)).re = 0 := by
      rw [hcos]; exact Q_cos_root hn hk1 hk2
    have hmem := re_mul_conj_mem_Icc (norm_regPt n i) (norm_regPt n l)
    have hpos : 0 < a - (regPt n i * starRingEnd ℂ (regPt n l)).re := by linarith [hmem.2]
    have hmul := hP_eq (regPt n i * starRingEnd ℂ (regPt n l)).re
    rw [hQt, zero_div, sub_zero] at hmul
    exact (eq_inv_of_mul_eq_one_right hmul)
  have hsum_P : ∀ (X : Fin n → ℂ), (∀ i, ‖X i‖ = 1) →
      ∑ i : Fin n, ∑ l : Fin n, P (X i * starRingEnd ℂ (X l)).re =
      (2 / Q n a) * ∑ k ∈ Ico 1 n, ((n - k : ℕ) : ℝ) *
        ((n : ℝ) ^ 2 * U (k - 1) a +
          2 * ∑ j ∈ Ico 1 k, U (k - 1 - j) a * ‖∑ i : Fin n, X i ^ j‖ ^ 2) := by
    intro X hX
    dsimp only [P]
    simp_rw [← mul_sum]
    congr 1
    trans ∑ k ∈ Ico 1 n, ∑ i : Fin n, ∑ l : Fin n,
        ((n - k : ℕ) : ℝ) * W k a (X i * starRingEnd ℂ (X l)).re
    · trans ∑ i : Fin n, ∑ k ∈ Ico 1 n, ∑ l : Fin n,
          ((n - k : ℕ) : ℝ) * W k a (X i * starRingEnd ℂ (X l)).re
      · refine sum_congr rfl fun i _ => sum_comm
      · exact sum_comm
    refine sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := by have := (mem_Ico.mp hk).1; omega
    simp_rw [← mul_sum]
    congr 1
    simp only [W, hk0, ↓reduceIte]
    simp_rw [sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    congr 1
    · ring
    · simp_rw [← mul_sum]
      congr 1
      trans ∑ j ∈ Ico 1 k, ∑ i : Fin n, ∑ l : Fin n,
          U (k - 1 - j) a * T j (X i * starRingEnd ℂ (X l)).re
      · trans ∑ i : Fin n, ∑ j ∈ Ico 1 k, ∑ l : Fin n,
            U (k - 1 - j) a * T j (X i * starRingEnd ℂ (X l)).re
        · refine sum_congr rfl fun i _ => sum_comm
        · exact sum_comm
      refine sum_congr rfl fun j _ => ?_
      simp_rw [← mul_sum]
      rw [sum_T_re_nonneg X hX j]
  have hP_total :
      ∑ i : Fin n, ∑ l : Fin n, P (regPt n i * starRingEnd ℂ (regPt n l)).re ≤
      ∑ i : Fin n, ∑ l : Fin n, P (B i * starRingEnd ℂ (B l)).re := by
    rw [hsum_P (regPt n) (norm_regPt n), hsum_P B hB]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine sum_le_sum fun k hk => ?_
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine add_le_add le_rfl ?_
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine sum_le_sum fun j hj => ?_
    have hj1 : 1 ≤ j := (mem_Ico.mp hj).1
    have hjk : j < k := (mem_Ico.mp hj).2
    have hkn : k < n := (mem_Ico.mp hk).2
    rw [sum_regPt_pow_eq_zero hj1 (lt_trans hjk hkn), norm_zero, sq, mul_zero, mul_zero]
    exact mul_nonneg (U_pos_of_one_lt ha _).le (sq_nonneg _)
  have hdiag : ∀ (X : Fin n → ℂ), (∀ i, ‖X i‖ = 1) →
      ∑ i : Fin n, ∑ l : Fin n, P (X i * starRingEnd ℂ (X l)).re =
      (∑ i : Fin n, ∑ l : Fin n, (if i ≠ l then P (X i * starRingEnd ℂ (X l)).re else 0)) +
        (n : ℝ) * P 1 := by
    intro X hX
    have hsplit : ∀ i : Fin n,
        ∑ l : Fin n, P (X i * starRingEnd ℂ (X l)).re =
        (∑ l : Fin n, if i ≠ l then P (X i * starRingEnd ℂ (X l)).re else 0) + P 1 := by
      intro i
      rw [← add_sum_erase _ _ (mem_univ i)]
      have hself : (X i * starRingEnd ℂ (X i)).re = 1 := by
        rw [mul_comm, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re, ← Complex.sq_norm, hX i]
        norm_num
      rw [hself, add_comm]
      congr 1
      rw [← add_sum_erase _ _ (mem_univ i)]
      simp only [ne_eq, not_true_eq_false, ↓reduceIte, zero_add]
      refine sum_congr rfl fun l hl => ?_
      have hil : i ≠ l := (mem_erase.mp hl).1.symm
      simp [hil]
    simp_rw [hsplit, sum_add_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hP_offdiag :
      ∑ i : Fin n, ∑ l : Fin n, (if i ≠ l then P (regPt n i * starRingEnd ℂ (regPt n l)).re else 0) ≤
      ∑ i : Fin n, ∑ l : Fin n, (if i ≠ l then P (B i * starRingEnd ℂ (B l)).re else 0) := by
    rw [hdiag (regPt n) (norm_regPt n), hdiag B hB] at hP_total
    linarith
  calc ∑ i : Fin n, ∑ l : Fin n, (if i ≠ l then (a - (regPt n i * starRingEnd ℂ (regPt n l)).re)⁻¹ else 0)
      = ∑ i : Fin n, ∑ l : Fin n, (if i ≠ l then P (regPt n i * starRingEnd ℂ (regPt n l)).re else 0) := by
        refine sum_congr rfl fun i _ => sum_congr rfl fun l _ => ?_
        split_ifs with h
        · exact (hP_reg i l h).symm
        · rfl
    _ ≤ ∑ i : Fin n, ∑ l : Fin n, (if i ≠ l then P (B i * starRingEnd ℂ (B l)).re else 0) := hP_offdiag
    _ ≤ ∑ i : Fin n, ∑ l : Fin n, (if i ≠ l then (a - (B i * starRingEnd ℂ (B l)).re)⁻¹ else 0) := by
        refine sum_le_sum fun i _ => sum_le_sum fun l _ => ?_
        split_ifs with h
        · have hmem := re_mul_conj_mem_Icc (hB i) (hB l)
          exact hP_le _ hmem.1 hmem.2
        · exact le_rfl

/-! ### Section 4: Integral representation for `x ^ s` (`0 < s < 1`) -/

private lemma integrableOn_kernel {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    IntegrableOn (fun u : ℝ => (1 + u)⁻¹ * u ^ (s - 1)) (Set.Ioi 0) := by
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · have hdom : IntegrableOn (fun u : ℝ => u ^ (s - 1)) (Set.Ioc 0 1) := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
      exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
    refine hdom.mono' ?_ ?_
    · exact ((continuousOn_const.add continuousOn_id).inv₀ (fun u hu => by
          have hu0 : 0 < u := hu.1; dsimp; linarith)).aestronglyMeasurable
        measurableSet_Ioc |>.mul
        ((ContinuousOn.rpow_const continuousOn_id (fun u hu => Or.inl hu.1.ne')).aestronglyMeasurable
          measurableSet_Ioc)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      have hu0 : 0 < u := hu.1
      have h1 : 0 < 1 + u := by linarith
      have hrp : 0 ≤ u ^ (s - 1) := Real.rpow_nonneg hu0.le _
      rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr h1.le) hrp)]
      have hinv : (1 + u)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
      nlinarith
  · have hdom : IntegrableOn (fun u : ℝ => u ^ (s - 2)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine hdom.mono' ?_ ?_
    · exact ((continuousOn_const.add continuousOn_id).inv₀ (fun u hu => by
          have hu1 : 1 < u := hu; dsimp; linarith)).aestronglyMeasurable
        measurableSet_Ioi |>.mul
        ((ContinuousOn.rpow_const continuousOn_id (fun u hu => Or.inl (lt_trans zero_lt_one hu).ne')).aestronglyMeasurable
          measurableSet_Ioi)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu1 : 1 < u := hu
      have hu0 : 0 < u := lt_trans zero_lt_one hu1
      have h1 : 0 < 1 + u := by linarith
      have hrp : 0 ≤ u ^ (s - 1) := Real.rpow_nonneg hu0.le _
      rw [Real.norm_of_nonneg (mul_nonneg (inv_nonneg.mpr h1.le) hrp)]
      have hinv : (1 + u)⁻¹ ≤ u⁻¹ := inv_anti₀ hu0 (by linarith)
      have hpow : u⁻¹ * u ^ (s - 1) = u ^ (s - 2) := by
        rw [← Real.rpow_neg_one, ← Real.rpow_add hu0]
        congr 1; ring
      calc (1 + u)⁻¹ * u ^ (s - 1) ≤ u⁻¹ * u ^ (s - 1) :=
            mul_le_mul_of_nonneg_right hinv hrp
        _ = u ^ (s - 2) := hpow

private lemma integral_kernel_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    0 < ∫ u in Set.Ioi (0 : ℝ), (1 + u)⁻¹ * u ^ (s - 1) := by
  have hint := integrableOn_kernel hs0 hs1
  have hsub : Set.Icc (1 : ℝ) 2 ⊆ Set.Ioi 0 := fun u hu => lt_of_lt_of_le zero_lt_one hu.1
  have hnonneg : ∀ u ∈ Set.Ioi (0 : ℝ), 0 ≤ (1 + u)⁻¹ * u ^ (s - 1) := fun u hu => by
    have hu0 : 0 < u := hu
    exact mul_nonneg (inv_nonneg.mpr (by linarith)) (Real.rpow_nonneg hu0.le _)
  have hge : ∫ u in Set.Icc (1 : ℝ) 2, (1 + u)⁻¹ * u ^ (s - 1) ≤
      ∫ u in Set.Ioi (0 : ℝ), (1 + u)⁻¹ * u ^ (s - 1) :=
    setIntegral_mono_set hint
      (ae_restrict_of_forall_mem measurableSet_Ioi hnonneg)
      (LE.le.eventuallyLE hsub)
  have hlb : ∀ u ∈ Set.Icc (1 : ℝ) 2, (3 : ℝ)⁻¹ * (2 : ℝ) ^ (s - 1) ≤ (1 + u)⁻¹ * u ^ (s - 1) := by
    intro u hu
    have h1 : (3 : ℝ)⁻¹ ≤ (1 + u)⁻¹ := inv_anti₀ (by linarith [hu.1]) (by linarith [hu.2])
    have h2 : (2 : ℝ) ^ (s - 1) ≤ u ^ (s - 1) :=
      Real.rpow_le_rpow_of_nonpos (lt_of_lt_of_le zero_lt_one hu.1) hu.2 (by linarith)
    exact mul_le_mul h1 h2 (Real.rpow_nonneg (by norm_num) _) (inv_nonneg.mpr (by linarith [hu.1]))
  have hint_sub : IntegrableOn (fun u : ℝ => (1 + u)⁻¹ * u ^ (s - 1)) (Set.Icc 1 2) :=
    hint.mono_set hsub
  have hconst_int : IntegrableOn (fun _ : ℝ => (3 : ℝ)⁻¹ * (2 : ℝ) ^ (s - 1)) (Set.Icc 1 2) :=
    integrableOn_const (by simp)
  have hmono := setIntegral_mono_on hconst_int hint_sub measurableSet_Icc hlb
  have hval : ∫ _ in Set.Icc (1 : ℝ) 2, (3 : ℝ)⁻¹ * (2 : ℝ) ^ (s - 1) =
      (3 : ℝ)⁻¹ * (2 : ℝ) ^ (s - 1) := by
    rw [setIntegral_const, Measure.real_def, Real.volume_Icc]
    norm_num
  rw [hval] at hmono
  have hpos : 0 < (3 : ℝ)⁻¹ * (2 : ℝ) ^ (s - 1) := by positivity
  linarith

private lemma integrableOn_scaled {x s : ℝ} (hx : 0 ≤ x) (hs0 : 0 < s) (hs1 : s < 1) :
    IntegrableOn (fun lam : ℝ => (x / (x + lam)) * lam ^ (s - 1)) (Set.Ioi 0) := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp only [zero_div, zero_mul]
    exact integrableOn_zero
  · have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := (Set.Ioc_union_Ioi_eq_Ioi zero_le_one).symm
    rw [hsplit]
    refine IntegrableOn.union ?_ ?_
    · have hdom : IntegrableOn (fun lam : ℝ => lam ^ (s - 1)) (Set.Ioc 0 1) := by
        rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
        exact intervalIntegral.intervalIntegrable_rpow' (by linarith)
      refine hdom.mono' ?_ ?_
      · exact (continuousOn_const.div (continuousOn_const.add continuousOn_id)
            (fun lam hlam => by have h0 : 0 < lam := hlam.1; dsimp; linarith)).aestronglyMeasurable
          measurableSet_Ioc |>.mul
          ((ContinuousOn.rpow_const continuousOn_id
            (fun lam hlam => Or.inl hlam.1.ne')).aestronglyMeasurable measurableSet_Ioc)
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with lam hlam
        have hlam0 : 0 < lam := hlam.1
        have hden : 0 < x + lam := by linarith
        have hrp : 0 ≤ lam ^ (s - 1) := Real.rpow_nonneg hlam0.le _
        rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg hxpos.le hden.le) hrp)]
        have hle1 : x / (x + lam) ≤ 1 := (div_le_one hden).mpr (by linarith)
        nlinarith
    · have hdom : IntegrableOn (fun lam : ℝ => x * lam ^ (s - 2)) (Set.Ioi 1) :=
        (integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one).const_mul x
      refine hdom.mono' ?_ ?_
      · exact (continuousOn_const.div (continuousOn_const.add continuousOn_id)
            (fun lam hlam => by have h1 : 1 < lam := hlam; dsimp; linarith)).aestronglyMeasurable
          measurableSet_Ioi |>.mul
          ((ContinuousOn.rpow_const continuousOn_id
            (fun lam hlam => Or.inl (lt_trans zero_lt_one hlam).ne')).aestronglyMeasurable
            measurableSet_Ioi)
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with lam hlam
        have hlam1 : 1 < lam := hlam
        have hlam0 : 0 < lam := lt_trans zero_lt_one hlam1
        have hden : 0 < x + lam := by linarith
        have hrp : 0 ≤ lam ^ (s - 1) := Real.rpow_nonneg hlam0.le _
        rw [Real.norm_of_nonneg (mul_nonneg (div_nonneg hxpos.le hden.le) hrp)]
        have hinv : x / (x + lam) ≤ x * lam⁻¹ := by
          rw [div_eq_mul_inv]
          exact mul_le_mul_of_nonneg_left (inv_anti₀ hlam0 (by linarith)) hxpos.le
        have hpow : lam⁻¹ * lam ^ (s - 1) = lam ^ (s - 2) := by
          rw [← Real.rpow_neg_one, ← Real.rpow_add hlam0]
          congr 1; ring
        calc (x / (x + lam)) * lam ^ (s - 1)
            ≤ (x * lam⁻¹) * lam ^ (s - 1) := mul_le_mul_of_nonneg_right hinv hrp
          _ = x * (lam⁻¹ * lam ^ (s - 1)) := by ring
          _ = x * lam ^ (s - 2) := by rw [hpow]

private lemma integral_scaled_eq {x s : ℝ} (hx : 0 ≤ x) (hs0 : 0 < s) (hs1 : s < 1) :
    ∫ lam in Set.Ioi (0 : ℝ), (x / (x + lam)) * lam ^ (s - 1) =
      x ^ s * ∫ u in Set.Ioi (0 : ℝ), (1 + u)⁻¹ * u ^ (s - 1) := by
  rcases eq_or_lt_of_le hx with rfl | hxpos
  · simp [Real.zero_rpow hs0.ne']
  · have hsub := integral_comp_mul_left_Ioi'
      (fun lam : ℝ => (x / (x + lam)) * lam ^ (s - 1)) (0 : ℝ) hxpos
    rw [mul_zero, smul_eq_mul] at hsub
    have hxs : ∫ u in Set.Ioi (0 : ℝ), (x / (x + x * u)) * (x * u) ^ (s - 1) =
        x ^ (s - 1) * ∫ u in Set.Ioi (0 : ℝ), (1 + u)⁻¹ * u ^ (s - 1) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
      have hu0 : 0 < u := hu
      have hfrac : x / (x + x * u) = (1 + u)⁻¹ := by
        have hxne : x ≠ 0 := hxpos.ne'
        have h1u : 1 + u ≠ 0 := by linarith
        field_simp
      rw [hfrac, Real.mul_rpow hxpos.le hu0.le]
      ring
    rw [← hsub, hxs, ← mul_assoc]
    have hpow : x * x ^ (s - 1) = x ^ s := by
      have h1 : x ^ (1 : ℝ) * x ^ (s - 1) = x ^ s := by
        rw [← Real.rpow_add hxpos]
        congr 1; ring
      rwa [Real.rpow_one] at h1
    rw [hpow]

/-! ### Section 5: Main Theorem -/

private lemma norm_sub_sq_eq {z w : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ = 1) :
    ‖z - w‖ ^ 2 = 2 - 2 * (z * starRingEnd ℂ w).re := by
  rw [Complex.sq_norm, Complex.normSq_sub]
  have hz2 : Complex.normSq z = 1 := by rw [← Complex.sq_norm, hz]; norm_num
  have hw2 : Complex.normSq w = 1 := by rw [← Complex.sq_norm, hw]; norm_num
  rw [hz2, hw2]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

private lemma sum_offdiag_eq_two_mul_sum_lt {n : ℕ} (f : Fin n → Fin n → ℝ)
    (hsym : ∀ i j, f i j = f j i) :
    ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then f i j else 0) =
      2 * ∑ i : Fin n, ∑ j : Fin n, (if i < j then f i j else 0) := by
  have h1 : ∀ i j : Fin n,
      (if i ≠ j then f i j else 0) =
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    intro i j
    rcases lt_trichotomy i j with h | rfl | h
    · simp [ne_of_lt h, h, not_lt_of_gt h]
    · simp
    · simp [ne_of_gt h, h, not_lt_of_gt h]
  simp_rw [h1, sum_add_distrib]
  have hswap :
      ∑ i : Fin n, ∑ j : Fin n, (if j < i then f i j else 0) =
      ∑ i : Fin n, ∑ j : Fin n, (if i < j then f i j else 0) := by
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
    rw [hsym]
  rw [hswap]; ring

private lemma main_alpha_two {n : ℕ} (hn : 2 ≤ n) (B : Fin n → ℂ) (hB : ∀ i, ‖B i‖ = 1) :
    ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then ‖B i - B j‖ ^ (2 : ℝ) else 0) ≤
    ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then ‖regPt n i - regPt n j‖ ^ (2 : ℝ) else 0) := by
  have hsum_sq : ∀ (X : Fin n → ℂ), (∀ i, ‖X i‖ = 1) →
      ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then ‖X i - X j‖ ^ (2 : ℝ) else 0) =
      2 * (n : ℝ) ^ 2 - 2 * ‖∑ i : Fin n, X i‖ ^ 2 := by
    intro X hX
    have hdiag0 : ∀ i j : Fin n,
        (if i ≠ j then ‖X i - X j‖ ^ (2 : ℝ) else 0) = ‖X i - X j‖ ^ (2 : ℕ) := by
      intro i j
      split_ifs with h
      · exact Real.rpow_two _
      · rw [not_ne_iff] at h; subst h; simp
    have hsq : ∀ i j : Fin n, ‖X i - X j‖ ^ (2 : ℕ) = 2 - 2 * (X i * starRingEnd ℂ (X j)).re :=
      fun i j => norm_sub_sq_eq (hX i) (hX j)
    simp_rw [hdiag0, hsq]
    simp_rw [sum_sub_distrib, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_sum]
    have h1 : ∑ i : Fin n, ∑ j : Fin n, (X i * starRingEnd ℂ (X j)).re = ‖∑ i : Fin n, X i‖ ^ 2 := by
      simpa only [T, pow_one] using sum_T_re_nonneg X hX 1
    rw [h1]
    ring
  rw [hsum_sq B hB, hsum_sq (regPt n) (norm_regPt n)]
  have hreg0 : ∑ i : Fin n, regPt n i = 0 := by
    have := sum_regPt_pow_eq_zero (n := n) (j := 1) le_rfl (by omega)
    simpa using this
  rw [hreg0, norm_zero]
  nlinarith [sq_nonneg ‖∑ i : Fin n, B i‖]

private lemma main_alpha_lt_two {n : ℕ} (hn : 2 ≤ n) {α : ℝ} (hα1 : 1 ≤ α) (hα2 : α < 2)
    (B : Fin n → ℂ) (hB : ∀ i, ‖B i‖ = 1) :
    ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then ‖B i - B j‖ ^ α else 0) ≤
    ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then ‖regPt n i - regPt n j‖ ^ α else 0) := by
  let s : ℝ := α / 2
  have hs0 : 0 < s := by dsimp only [s]; linarith
  have hs1 : s < 1 := by dsimp only [s]; linarith
  let C : ℝ := ∫ u in Set.Ioi (0 : ℝ), (1 + u)⁻¹ * u ^ (s - 1)
  have hCpos : 0 < C := integral_kernel_pos hs0 hs1
  suffices hmul :
      (∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then ‖B i - B j‖ ^ α else 0)) * C ≤
      (∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then ‖regPt n i - regPt n j‖ ^ α else 0)) * C by
    exact le_of_mul_le_mul_right hmul hCpos
  have hrewrite' : ∀ (X : Fin n → ℂ),
      (∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then ‖X i - X j‖ ^ α else 0)) * C =
      ∫ lam in Set.Ioi (0 : ℝ),
        (∑ i : Fin n, ∑ j : Fin n,
          (if i ≠ j then ‖X i - X j‖ ^ 2 / (‖X i - X j‖ ^ 2 + lam) else 0)) * lam ^ (s - 1) := by
    intro X
    have hint : ∀ i j : Fin n,
        IntegrableOn (fun lam : ℝ =>
          (if i ≠ j then ‖X i - X j‖ ^ 2 / (‖X i - X j‖ ^ 2 + lam) else 0) * lam ^ (s - 1)) (Set.Ioi 0) := by
      intro i j
      split_ifs with h
      · exact integrableOn_scaled (sq_nonneg _) hs0 hs1
      · simp only [zero_mul]; exact integrableOn_zero
    have hterm : ∀ i j : Fin n,
        (if i ≠ j then ‖X i - X j‖ ^ α else 0) * C =
        ∫ lam in Set.Ioi (0 : ℝ),
          (if i ≠ j then ‖X i - X j‖ ^ 2 / (‖X i - X j‖ ^ 2 + lam) else 0) * lam ^ (s - 1) := by
      intro i j
      split_ifs with h
      · have hrpow : ‖X i - X j‖ ^ α = (‖X i - X j‖ ^ 2) ^ s := by
          rw [← Real.rpow_natCast ‖X i - X j‖ 2, ← Real.rpow_mul (norm_nonneg _)]
          congr 1; dsimp only [s]; push_cast; ring
        rw [hrpow]
        exact (integral_scaled_eq (sq_nonneg _) hs0 hs1).symm
      · simp
    calc (∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then ‖X i - X j‖ ^ α else 0)) * C
        = ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then ‖X i - X j‖ ^ α else 0) * C := by
          simp_rw [sum_mul]
      _ = ∑ i : Fin n, ∑ j : Fin n,
            ∫ lam in Set.Ioi (0 : ℝ),
              (if i ≠ j then ‖X i - X j‖ ^ 2 / (‖X i - X j‖ ^ 2 + lam) else 0) * lam ^ (s - 1) := by
          simp_rw [hterm]
      _ = ∑ i : Fin n, ∫ lam in Set.Ioi (0 : ℝ),
            ∑ j : Fin n,
              (if i ≠ j then ‖X i - X j‖ ^ 2 / (‖X i - X j‖ ^ 2 + lam) else 0) * lam ^ (s - 1) := by
          refine sum_congr rfl fun i _ => (integral_finsetSum _ (fun j _ => hint i j)).symm
      _ = ∫ lam in Set.Ioi (0 : ℝ),
            ∑ i : Fin n, ∑ j : Fin n,
              (if i ≠ j then ‖X i - X j‖ ^ 2 / (‖X i - X j‖ ^ 2 + lam) else 0) * lam ^ (s - 1) := by
          exact (integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))).symm
      _ = ∫ lam in Set.Ioi (0 : ℝ),
            (∑ i : Fin n, ∑ j : Fin n,
              (if i ≠ j then ‖X i - X j‖ ^ 2 / (‖X i - X j‖ ^ 2 + lam) else 0)) * lam ^ (s - 1) := by
          refine setIntegral_congr_fun measurableSet_Ioi fun lam _ => ?_
          simp_rw [sum_mul]
  rw [hrewrite' B, hrewrite' (regPt n)]
  have hintF : ∀ (X : Fin n → ℂ),
      IntegrableOn (fun lam : ℝ =>
        (∑ i : Fin n, ∑ j : Fin n,
          (if i ≠ j then ‖X i - X j‖ ^ 2 / (‖X i - X j‖ ^ 2 + lam) else 0)) * lam ^ (s - 1)) (Set.Ioi 0) := by
    intro X
    have h1 : IntegrableOn (fun lam : ℝ =>
        ∑ i : Fin n, ∑ j : Fin n,
          (if i ≠ j then ‖X i - X j‖ ^ 2 / (‖X i - X j‖ ^ 2 + lam) else 0) * lam ^ (s - 1)) (Set.Ioi 0) := by
      refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
      split_ifs with h
      · exact integrableOn_scaled (sq_nonneg _) hs0 hs1
      · simp only [zero_mul]; exact integrableOn_zero
    exact h1.congr_fun (fun lam _ => by simp_rw [sum_mul]) measurableSet_Ioi
  refine setIntegral_mono_on (hintF B) (hintF (regPt n)) measurableSet_Ioi fun lam hlam => ?_
  have hlam0 : 0 < lam := hlam
  refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hlam0.le _)
  let a : ℝ := 1 + lam / 2
  have ha : 1 < a := by dsimp only [a]; linarith
  have hfrac_id : ∀ (X : Fin n → ℂ), (∀ i, ‖X i‖ = 1) →
      ∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then ‖X i - X j‖ ^ 2 / (‖X i - X j‖ ^ 2 + lam) else 0) =
      (∑ i : Fin n, ∑ j : Fin n, (if i ≠ j then (1 : ℝ) else 0)) -
      (lam / 2) * ∑ i : Fin n, ∑ j : Fin n,
        (if i ≠ j then (a - (X i * starRingEnd ℂ (X j)).re)⁻¹ else 0) := by
    intro X hX
    have hterm : ∀ i j : Fin n,
        (if i ≠ j then ‖X i - X j‖ ^ 2 / (‖X i - X j‖ ^ 2 + lam) else 0) =
        (if i ≠ j then (1 : ℝ) else 0) -
        (lam / 2) * (if i ≠ j then (a - (X i * starRingEnd ℂ (X j)).re)⁻¹ else 0) := by
      intro i j
      split_ifs with h
      · rw [norm_sub_sq_eq (hX i) (hX j)]
        set t := (X i * starRingEnd ℂ (X j)).re
        have hmem := re_mul_conj_mem_Icc (hX i) (hX j)
        have hd1 : 2 - 2 * t + lam ≠ 0 := by linarith [hmem.2]
        have hd2 : a - t ≠ 0 := by dsimp only [a]; linarith [hmem.2]
        rw [div_eq_iff hd1]
        have ha2 : 2 * (a - t) = 2 - 2 * t + lam := by dsimp only [a]; ring
        calc 2 - 2 * t
            = (2 - 2 * t + lam) - lam := by ring
          _ = (2 - 2 * t + lam) - (lam / 2) * (2 * (a - t)) * (a - t)⁻¹ := by
                have hcancel : (lam / 2) * (2 * (a - t)) * (a - t)⁻¹ = lam := by
                  calc (lam / 2) * (2 * (a - t)) * (a - t)⁻¹
                      = lam * ((a - t) * (a - t)⁻¹) := by ring
                    _ = lam := by rw [mul_inv_cancel₀ hd2, mul_one]
                rw [hcancel]
          _ = (1 - lam / 2 * (a - t)⁻¹) * (2 - 2 * t + lam) := by rw [ha2]; ring
      · ring
    simp_rw [hterm, sum_sub_distrib, ← mul_sum]
  rw [hfrac_id B hB, hfrac_id (regPt n) (norm_regPt n)]
  have hineq := inv_sub_re_sum_ge hn ha B hB
  nlinarith

end OMA.MO304819

theorem OMA.solution : type_of% @OMA.S_mo_304819.main := by
  intro n α hn hα1 hα2 B hB
  have hsymB : ∀ i j : Fin n, ‖B i - B j‖ ^ α = ‖B j - B i‖ ^ α := fun i j => by
    rw [norm_sub_rev]
  have hsymR : ∀ i j : Fin n,
      ‖OMA.MO304819.regPt n i - OMA.MO304819.regPt n j‖ ^ α =
      ‖OMA.MO304819.regPt n j - OMA.MO304819.regPt n i‖ ^ α := fun i j => by
    rw [norm_sub_rev]
  have hreg_eq : ∀ i j : Fin n,
      ‖Complex.exp (2 * Real.pi * Complex.I * i / n) -
        Complex.exp (2 * Real.pi * Complex.I * j / n)‖ ^ α =
      ‖OMA.MO304819.regPt n i - OMA.MO304819.regPt n j‖ ^ α := fun _ _ => rfl
  simp_rw [hreg_eq]
  have h2B := OMA.MO304819.sum_offdiag_eq_two_mul_sum_lt (fun i j => ‖B i - B j‖ ^ α) hsymB
  have h2R := OMA.MO304819.sum_offdiag_eq_two_mul_sum_lt
    (fun i j => ‖OMA.MO304819.regPt n i - OMA.MO304819.regPt n j‖ ^ α) hsymR
  rcases eq_or_lt_of_le hα2 with rfl | hlt
  · have h := OMA.MO304819.main_alpha_two hn B hB
    linarith
  · have h := OMA.MO304819.main_alpha_lt_two hn hα1 hlt B hB
    linarith
