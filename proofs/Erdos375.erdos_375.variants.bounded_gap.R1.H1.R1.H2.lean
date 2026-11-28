import OMAReductions.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1
import Mathlib
/- The van der Corput estimate is by Sky (@ChironTheCentaur), adapted from the merged proof by @senamakel. Source commit 467faf0ee95603cd28ff806134bd3e0de330747d, Apache-2.0. The Bernoulli smoothing, bilinear estimate, and prime interval application are supplied here.
NOTICE of the original package, retained as Apache-2.0 requires:

  PowerfulNumbers (standalone package)
  Copyright 2026 Sky (GitHub: ChironTheCentaur)

  The original work in this package (PowerfulFC/, LeanClassics/, PowerfulNumbers.lean, check.py, AxiomAudit.lean,
  PlantedSorry.lean, controls/) is licensed under the Apache License, Version 2.0 (see LICENSE).

  The statements of asymptotic_erdos_szekeres, asymptotic_bateman_grosswald and the conclusion of
  error_term_improvement, and the definitions Q, A, B and Nat.Full / Nat.Powerful are copied verbatim from
  google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/PowerfulNumbersDensity.lean and
  FormalConjecturesForMathlib/Data/Nat/Full.lean, commit ea8e3e19), Copyright The Formal Conjectures Authors,
  licensed under the Apache License, Version 2.0.

  Zeta23/ is a subset of zeta-23-lean, Copyright 2026 Anthropic, PBC, licensed under the Apache License,
  Version 2.0 (LICENSE.zeta23, NOTICE.zeta23), as ported to Lean v4.35.0 / Mathlib 56a005855ea1.

The LeanClassics.DHEMZeta* modules below carry their own notice (ported from DrMurphyIsIn/Arda, Apache-2.0).
-/
section
/-!
# Van der Corput estimates, rung V1: the Kusmin–Landau first-derivative test

`e x = exp(2πix)`.

`kusmin_landau_discrete`: let `x : ℕ → ℝ` have differences `δₙ = x(n+1) − x(n)` that are nondecreasing
and lie in `[k + λ, k + 1 − λ]` for one integer `k` and `0 < λ ≤ 1/2`, for every `n + 1 < N`. Then
`‖∑_{n<N} e(x n)‖ ≤ cot(πλ/2)`.

`kusmin_landau`: let `f` be differentiable with derivative `f'` on `[m, m + N − 1]` (`m : ℤ`), `f'` monotone
(nondecreasing or nonincreasing) there and `k + λ ≤ f' ≤ k + 1 − λ` there. Then
`‖∑_{n<N} e(f(m + n))‖ ≤ cot(πλ/2)`, and `kusmin_landau_inv` gives `≤ 1/λ`.

This is Graham–Kolesnik, *Van der Corput's method of exponential sums*, Theorem 2.1 (there `‖f'‖ ≥ λ` with
`f'` monotone; for a derivative that never reaches a near-integer value the two hypotheses are the same, since
`f'` has the intermediate value property), with Kusmin's and Landau's constant `cot(πλ/2)`. Only the integers
of the closed interval on which the hypotheses hold are summed.

Proof (Kusmin–Landau). Subtract `k n` from `x n` (it does not change `e(x n)`), so `λ ≤ δₙ ≤ 1 − λ`. With
`zₙ = e(xₙ)` and `cₙ = −1/2 − (i/2) cot(πδₙ)` one has `cₙ (e(δₙ) − 1) = 1`, so `zₙ = cₙ (zₙ₊₁ − zₙ)`.
Abel summation gives `∑_{n ≤ L+1} zₙ = (1 + c_L) z_{L+1} − c₀ z₀ + ∑_{n<L} (cₙ − cₙ₊₁) zₙ₊₁`. Here
`‖c₀‖, ‖1 + c_L‖ ≤ 1/(2 sin πλ)`, and `cₙ − cₙ₊₁ = (i/2)(cot πδₙ₊₁ − cot πδₙ)` telescopes because `cot` is
decreasing on `(0, π)`, to at most `cot πλ`. The total is `1/sin πλ + cot πλ = cot(πλ/2)`.
-/

namespace LeanClassics.VanDerCorput

open Real Finset

/-- `e(x) = exp(2πix)`. -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (((2 * π * x : ℝ) : ℂ) * Complex.I)

theorem e_add (x y : ℝ) : e (x + y) = e x * e y := by
  unfold e
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_e (x : ℝ) : ‖e x‖ = 1 := by
  unfold e
  exact Complex.norm_exp_ofReal_mul_I _

theorem e_eq (x : ℝ) : e x = (Real.cos (2 * π * x) : ℂ) + (Real.sin (2 * π * x) : ℂ) * Complex.I := by
  unfold e
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem e_intCast_mul (k : ℤ) (n : ℕ) : e ((k : ℝ) * n) = 1 := by
  unfold e
  have : (((2 * π * ((k : ℝ) * n) : ℝ) : ℂ) * Complex.I) = ((k * n : ℤ) : ℂ) * (2 * π * Complex.I) := by
    push_cast
    ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

theorem e_neg (x : ℝ) : e (-x) = (starRingEnd ℂ) (e x) := by
  unfold e
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- `cot` is nonincreasing on `(0, π)`: for `0 < πa ≤ πb < π`, `cot πb ≤ cot πa` (as `cos/sin`). -/
theorem cot_anti {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    Real.cos (π * b) / Real.sin (π * b) ≤ Real.cos (π * a) / Real.sin (π * a) := by
  have hsa : 0 < Real.sin (π * a) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hsb : 0 < Real.sin (π * b) :=
    Real.sin_pos_of_pos_of_lt_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  rw [div_le_div_iff₀ hsb hsa]
  have h := Real.sin_sub (π * b) (π * a)
  have hnn : 0 ≤ Real.sin (π * b - π * a) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  linarith

/-- On `[λ, 1 − λ]`, `sin(πδ) ≥ sin(πλ)`. -/
theorem sin_ge {lam δ : ℝ} (h1 : lam ≤ δ) (h2 : δ ≤ 1 - lam) (hlam : 0 < lam) :
    Real.sin (π * lam) ≤ Real.sin (π * δ) := by
  rcases le_total δ (1 / 2) with hd | hd
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])
  · have : Real.sin (π * δ) = Real.sin (π * (1 - δ)) := by
      rw [show π * (1 - δ) = π - π * δ by ring, Real.sin_pi_sub]
    rw [this]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by nlinarith [Real.pi_pos])
      (by nlinarith [Real.pi_pos]) (by nlinarith [Real.pi_pos])

/-- The Kusmin–Landau coefficient `c(δ) = −1/2 − (i/2) cot(πδ)`. -/
noncomputable def cKL (δ : ℝ) : ℂ :=
  -1 / 2 - Complex.I / 2 * ((Real.cos (π * δ) / Real.sin (π * δ) : ℝ) : ℂ)

theorem cKL_mul (δ : ℝ) (h : Real.sin (π * δ) ≠ 0) : cKL δ * (e δ - 1) = 1 := by
  have h2 : 2 * π * δ = 2 * (π * δ) := by ring
  rw [e_eq, h2, Real.cos_two_mul, Real.sin_two_mul]
  unfold cKL
  have hpy := Real.sin_sq_add_cos_sq (π * δ)
  have hgs : Real.cos (π * δ) / Real.sin (π * δ) * Real.sin (π * δ) = Real.cos (π * δ) := by
    field_simp
  generalize Real.cos (π * δ) / Real.sin (π * δ) = g at *
  generalize hq : Real.cos (π * δ) ^ 2 = q at *
  generalize Real.sin (π * δ) = s at *
  generalize Real.cos (π * δ) = co at *
  apply Complex.ext
  · simp
    linear_combination co * hgs + hq
  · simp
    linear_combination s * hgs - g * hpy

theorem norm_cKL_aux (s co g : ℝ) (hs : 0 < s) (hpy : s ^ 2 + co ^ 2 = 1) (hg : g = co / s) :
    ‖(-1 / 2 - Complex.I / 2 * (g : ℂ) : ℂ)‖ = 1 / (2 * s) ∧
      ‖(1 + (-1 / 2 - Complex.I / 2 * (g : ℂ)) : ℂ)‖ = 1 / (2 * s) := by
  have hr : 0 ≤ 1 / (2 * s) := by positivity
  constructor
  · rw [← sq_eq_sq₀ (norm_nonneg _) hr, Complex.sq_norm, Complex.normSq_apply]
    simp
    rw [hg]
    field_simp
    linear_combination hpy
  · rw [← sq_eq_sq₀ (norm_nonneg _) hr, Complex.sq_norm, Complex.normSq_apply]
    simp
    rw [hg]
    field_simp
    linear_combination hpy

theorem norm_cKL (δ : ℝ) (h : 0 < Real.sin (π * δ)) : ‖cKL δ‖ = 1 / (2 * Real.sin (π * δ)) :=
  (norm_cKL_aux _ (Real.cos (π * δ)) _ h (Real.sin_sq_add_cos_sq _) rfl).1

theorem norm_one_add_cKL (δ : ℝ) (h : 0 < Real.sin (π * δ)) :
    ‖1 + cKL δ‖ = 1 / (2 * Real.sin (π * δ)) :=
  (norm_cKL_aux _ (Real.cos (π * δ)) _ h (Real.sin_sq_add_cos_sq _) rfl).2

theorem norm_cKL_sub (a b : ℝ) :
    ‖cKL a - cKL b‖ =
      |Real.cos (π * b) / Real.sin (π * b) - Real.cos (π * a) / Real.sin (π * a)| / 2 := by
  unfold cKL
  have : (-1 / 2 - Complex.I / 2 * ((Real.cos (π * a) / Real.sin (π * a) : ℝ) : ℂ)) -
      (-1 / 2 - Complex.I / 2 * ((Real.cos (π * b) / Real.sin (π * b) : ℝ) : ℂ)) =
      ((((Real.cos (π * b) / Real.sin (π * b) - Real.cos (π * a) / Real.sin (π * a)) / 2 : ℝ) : ℂ)) *
        Complex.I := by
    push_cast
    ring
  rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
    abs_two]

/-- Abel summation for `zₙ = cₙ (zₙ₊₁ − zₙ)`, `n < L + 1`. -/
theorem abel (z c : ℕ → ℂ) (L : ℕ) (hz : ∀ n, n < L + 1 → z n = c n * (z (n + 1) - z n)) :
    ∑ n ∈ range (L + 2), z n =
      (1 + c L) * z (L + 1) - c 0 * z 0 + ∑ n ∈ range L, (c n - c (n + 1)) * z (n + 1) := by
  have key : ∀ m, m < L + 1 → ∑ n ∈ range (m + 1), z n =
      c m * z (m + 1) - c 0 * z 0 + ∑ n ∈ range m, (c n - c (n + 1)) * z (n + 1) := by
    intro m
    induction m with
    | zero =>
      intro h
      simp only [zero_add, range_one, sum_singleton, range_zero, sum_empty, add_zero]
      have := hz 0 h
      linear_combination this
    | succ m ih =>
      intro h
      rw [sum_range_succ, ih (by omega), sum_range_succ]
      have := hz (m + 1) h
      linear_combination this
  rw [sum_range_succ, key L (by omega)]
  ring

/-- The constant: `(1 + cos πλ)/sin πλ = cot(πλ/2)`. -/
theorem cot_half (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1 / 2) :
    Real.cot (π * lam / 2) = (1 + Real.cos (π * lam)) / Real.sin (π * lam) := by
  have hu : π * lam = 2 * (π * lam / 2) := by ring
  have hs : 0 < Real.sin (π * lam / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hc : 0 < Real.cos (π * lam / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  rw [Real.cot_eq_cos_div_sin, hu, Real.cos_two_mul, Real.sin_two_mul]
  field_simp
  ring

/-- **Kusmin–Landau, discrete form.** Nondecreasing differences in `[k + λ, k + 1 − λ]` give
`‖∑_{n<N} e(xₙ)‖ ≤ cot(πλ/2)`. -/
theorem kusmin_landau_discrete (x : ℕ → ℝ) (N : ℕ) (k : ℤ) (lam : ℝ) (hlam : 0 < lam)
    (hlam' : lam ≤ 1 / 2)
    (hδ : ∀ n, n + 1 < N → (k : ℝ) + lam ≤ x (n + 1) - x n ∧ x (n + 1) - x n ≤ k + 1 - lam)
    (hmono : ∀ n, n + 2 < N → x (n + 1) - x n ≤ x (n + 2) - x (n + 1)) :
    ‖∑ n ∈ range N, e (x n)‖ ≤ Real.cot (π * lam / 2) := by
  rw [cot_half lam hlam hlam']
  have hsl : 0 < Real.sin (π * lam) :=
    Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [Real.pi_pos])
  have hcl : 0 ≤ Real.cos (π * lam) :=
    Real.cos_nonneg_of_mem_Icc ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  -- shift by `k n`
  set y : ℕ → ℝ := fun n => x n - k * n with hy
  have hey : ∀ n, e (x n) = e (y n) := by
    intro n
    have : x n = y n + k * n := by simp [hy]
    rw [this, e_add, e_intCast_mul, mul_one]
  simp_rw [hey]
  set d : ℕ → ℝ := fun n => y (n + 1) - y n with hd
  have hd' : ∀ n, d n = x (n + 1) - x n - k := by
    intro n; simp only [hd, hy]; push_cast; ring
  match N with
  | 0 => simp; positivity
  | 1 =>
    simp only [range_one, sum_singleton, norm_e]
    rw [le_div_iff₀ hsl]
    nlinarith [Real.sin_le_one (π * lam)]
  | L + 2 =>
    have hdI : ∀ n, n < L + 1 → lam ≤ d n ∧ d n ≤ 1 - lam := by
      intro n hn
      obtain ⟨h1, h2⟩ := hδ n (by omega)
      rw [hd' n]; constructor <;> linarith
    have hsin : ∀ n, n < L + 1 → Real.sin (π * lam) ≤ Real.sin (π * d n) := by
      intro n hn
      exact sin_ge (hdI n hn).1 (hdI n hn).2 hlam
    set g : ℕ → ℝ := fun n => Real.cos (π * d n) / Real.sin (π * d n) with hg
    have hgG : ∀ n, n < L + 1 → g n ≤ Real.cos (π * lam) / Real.sin (π * lam) ∧
        -(Real.cos (π * lam) / Real.sin (π * lam)) ≤ g n := by
      intro n hn
      obtain ⟨h1, h2⟩ := hdI n hn
      constructor
      · exact cot_anti hlam h1 (by linarith)
      · have := cot_anti (a := d n) (b := 1 - lam) (by linarith) h2 (by linarith)
        have e1 : Real.cos (π * (1 - lam)) = -Real.cos (π * lam) := by
          rw [show π * (1 - lam) = π - π * lam by ring, Real.cos_pi_sub]
        have e2 : Real.sin (π * (1 - lam)) = Real.sin (π * lam) := by
          rw [show π * (1 - lam) = π - π * lam by ring, Real.sin_pi_sub]
        rw [e1, e2, neg_div] at this
        exact this
    have hganti : ∀ n, n < L → g (n + 1) ≤ g n := by
      intro n hn
      have hm := hmono n (by omega)
      have h1 := hdI n (by omega)
      have h2 := hdI (n + 1) (by omega)
      have : d n ≤ d (n + 1) := by
        rw [hd' n, hd' (n + 1)]; linarith
      exact cot_anti (by linarith [h1.1]) this (by linarith [h2.2])
    set c : ℕ → ℂ := fun n => cKL (d n) with hc
    have hz : ∀ n, n < L + 1 → e (y n) = c n * (e (y (n + 1)) - e (y n)) := by
      intro n hn
      have hyn : y (n + 1) = y n + d n := by simp only [hd]; ring
      rw [hyn, e_add]
      have := cKL_mul (d n) (ne_of_gt (lt_of_lt_of_le hsl (hsin n hn)))
      simp only [hc]
      linear_combination (-(e (y n))) * this
    rw [abel (fun n => e (y n)) c L hz]
    have hc0 : ‖c 0‖ ≤ 1 / (2 * Real.sin (π * lam)) := by
      simp only [hc]
      rw [norm_cKL _ (lt_of_lt_of_le hsl (hsin 0 (by omega)))]
      gcongr
      exact hsin 0 (by omega)
    have hcL : ‖1 + c L‖ ≤ 1 / (2 * Real.sin (π * lam)) := by
      simp only [hc]
      rw [norm_one_add_cKL _ (lt_of_lt_of_le hsl (hsin L (by omega)))]
      gcongr
      exact hsin L (by omega)
    have hmid : ∑ n ∈ range L, ‖(c n - c (n + 1)) * e (y (n + 1))‖ = (g 0 - g L) / 2 := by
      have : ∀ n ∈ range L, ‖(c n - c (n + 1)) * e (y (n + 1))‖ = (g n - g (n + 1)) / 2 := by
        intro n hn
        rw [mem_range] at hn
        rw [norm_mul, norm_e, mul_one]
        simp only [hc]
        rw [norm_cKL_sub]
        have := hganti n hn
        simp only [hg] at this
        rw [abs_of_nonpos (by linarith)]
        simp only [hg]
        ring
      rw [sum_congr rfl this, ← sum_div, sum_range_sub' g L]
    have hg0 := (hgG 0 (by omega)).1
    have hgL := (hgG L (by omega)).2
    calc ‖(1 + c L) * e (y (L + 1)) - c 0 * e (y 0) +
          ∑ n ∈ range L, (c n - c (n + 1)) * e (y (n + 1))‖
        ≤ ‖(1 + c L) * e (y (L + 1))‖ + ‖c 0 * e (y 0)‖ +
          ∑ n ∈ range L, ‖(c n - c (n + 1)) * e (y (n + 1))‖ := by
          refine (norm_add_le _ _).trans ?_
          gcongr
          · exact norm_sub_le _ _
          · exact norm_sum_le _ _
      _ = ‖1 + c L‖ + ‖c 0‖ + (g 0 - g L) / 2 := by
          rw [hmid, norm_mul, norm_mul, norm_e, norm_e, mul_one, mul_one]
      _ ≤ 1 / (2 * Real.sin (π * lam)) + 1 / (2 * Real.sin (π * lam)) +
          Real.cos (π * lam) / Real.sin (π * lam) := by
          linarith
      _ = (1 + Real.cos (π * lam)) / Real.sin (π * lam) := by
          field_simp
          ring

/-- **Kusmin–Landau, nondecreasing `f'`.** -/
theorem kusmin_landau_mono (f f' : ℝ → ℝ) (m : ℤ) (N : ℕ) (k : ℤ) (lam : ℝ) (hlam : 0 < lam)
    (hlam' : lam ≤ 1 / 2)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hmono : MonotoneOn f' (Set.Icc (m : ℝ) (m + N - 1)))
    (hk : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), (k : ℝ) + lam ≤ f' t ∧ f' t ≤ k + 1 - lam) :
    ‖∑ n ∈ range N, e (f (m + n))‖ ≤ Real.cot (π * lam / 2) := by
  -- the mean value theorem on `[m + n, m + n + 1]`
  have mvt : ∀ n : ℕ, n + 1 < N → ∃ ξ ∈ Set.Icc ((m : ℝ) + n) (m + n + 1),
      ξ ∈ Set.Icc (m : ℝ) (m + N - 1) ∧ f (m + (n + 1 : ℕ)) - f (m + n) = f' ξ := by
    intro n hn
    have hN : ((n : ℝ) + 1 + 1) ≤ N := by exact_mod_cast hn
    have hsub : Set.Icc ((m : ℝ) + n) (m + n + 1) ⊆ Set.Icc (m : ℝ) (m + N - 1) := by
      intro t ht
      exact ⟨by linarith [ht.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)], by linarith [ht.2]⟩
    obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope f f' (show (m : ℝ) + n < m + n + 1 by linarith)
      (fun t ht => (hf t (hsub ht)).continuousAt.continuousWithinAt)
      (fun t ht => hf t (hsub (Set.Ioo_subset_Icc_self ht)))
    refine ⟨ξ, Set.Ioo_subset_Icc_self hξ, hsub (Set.Ioo_subset_Icc_self hξ), ?_⟩
    rw [hξe]
    push_cast
    ring_nf
  apply kusmin_landau_discrete (fun n => f (m + n)) N k lam hlam hlam'
  · intro n hn
    obtain ⟨ξ, -, hξ, he⟩ := mvt n hn
    rw [he]
    exact hk ξ hξ
  · intro n hn
    obtain ⟨ξ₁, hξ₁, hξ₁', he₁⟩ := mvt n (by omega)
    obtain ⟨ξ₂, hξ₂, hξ₂', he₂⟩ := mvt (n + 1) hn
    rw [he₁, show n + 2 = (n + 1) + 1 by ring, he₂]
    apply hmono hξ₁' hξ₂'
    have := hξ₁.2
    have := hξ₂.1
    push_cast at *
    linarith

/-- **Kusmin–Landau** (Graham–Kolesnik Theorem 2.1, with the constant `cot(πλ/2)`). If `f' = f′` on
`[m, m + N − 1]`, `f'` is monotone there and `k + λ ≤ f' ≤ k + 1 − λ` there (`k ∈ ℤ`, `0 < λ ≤ 1/2`), then
`‖∑_{n<N} e(f(m + n))‖ ≤ cot(πλ/2)`. -/
theorem kusmin_landau (f f' : ℝ → ℝ) (m : ℤ) (N : ℕ) (k : ℤ) (lam : ℝ) (hlam : 0 < lam)
    (hlam' : lam ≤ 1 / 2)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hmono : MonotoneOn f' (Set.Icc (m : ℝ) (m + N - 1)) ∨
      AntitoneOn f' (Set.Icc (m : ℝ) (m + N - 1)))
    (hk : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), (k : ℝ) + lam ≤ f' t ∧ f' t ≤ k + 1 - lam) :
    ‖∑ n ∈ range N, e (f (m + n))‖ ≤ Real.cot (π * lam / 2) := by
  rcases hmono with hmono | hanti
  · exact kusmin_landau_mono f f' m N k lam hlam hlam' hf hmono hk
  · have h := kusmin_landau_mono (fun t => -f t) (fun t => -f' t) m N (-k - 1) lam hlam hlam'
      (fun t ht => (hf t ht).neg) (fun a ha b hb hab => neg_le_neg (hanti ha hb hab))
      (fun t ht => by
        obtain ⟨h1, h2⟩ := hk t ht
        push_cast
        constructor <;> linarith)
    simp_rw [e_neg, ← map_sum, Complex.norm_conj] at h
    exact h

/-- **Kusmin–Landau, `≪ 1/λ` form**: under the hypotheses of `kusmin_landau`,
`‖∑_{n<N} e(f(m + n))‖ ≤ 1/λ`. -/
theorem kusmin_landau_inv (f f' : ℝ → ℝ) (m : ℤ) (N : ℕ) (k : ℤ) (lam : ℝ) (hlam : 0 < lam)
    (hlam' : lam ≤ 1 / 2)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hmono : MonotoneOn f' (Set.Icc (m : ℝ) (m + N - 1)) ∨
      AntitoneOn f' (Set.Icc (m : ℝ) (m + N - 1)))
    (hk : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), (k : ℝ) + lam ≤ f' t ∧ f' t ≤ k + 1 - lam) :
    ‖∑ n ∈ range N, e (f (m + n))‖ ≤ 1 / lam := by
  refine (kusmin_landau f f' m N k lam hlam hlam' hf hmono hk).trans ?_
  rw [cot_half lam hlam hlam']
  have hsl : 2 * lam ≤ Real.sin (π * lam) := by
    have := Real.mul_le_sin (x := π * lam) (by positivity) (by nlinarith [Real.pi_pos])
    rw [show 2 / π * (π * lam) = 2 * lam by field_simp] at this
    exact this
  have hc : Real.cos (π * lam) ≤ 1 := Real.cos_le_one _
  rw [div_le_div_iff₀ (by linarith) hlam]
  nlinarith

end LeanClassics.VanDerCorput
end

-- ===== LeanClassics.VanDerCorputSecond =====
section
/-!
# Van der Corput estimates, rung V2: the second-derivative test

`van_der_corput_second`: let `f` have derivative `f'` and `f'` have derivative `f''` on `[m, m + N − 1]`
(`m : ℤ`), with `λ ≤ f'' ≤ αλ` there and `λ > 0`. Then
`‖∑_{n<N} e(f(m + n))‖ ≤ 4 α N √λ + 7/√λ`.

`van_der_corput_second_delta` is the form with a free cut-off `0 < δ ≤ 1/2`: for `N ≥ 1`,
`‖∑_{n<N} e(f(m + n))‖ ≤ (αλ(N − 1) + 2) · (2δ/λ + 1 + 1/δ)`.

This is Graham–Kolesnik, *Van der Corput's method of exponential sums*, Theorem 2.2
(`∑ e(f(n)) ≪ α (b − a) λ^{1/2} + λ^{−1/2}`), with explicit constants.

Proof. Put `w = f' + δ` and cut `[m, m + N − 1]` into maximal blocks of integers on which `⌊w⌋` is a
constant `j`; there are at most `⌊w(end)⌋ − ⌊w(m)⌋ + 1 ≤ αλ(N − 1) + 2` of them. Inside a block `f'` rises
through `[j − δ, j + 1 − δ)`. Its first part, where `f' < j + δ`, has fewer than `2δ/λ + 1` points (`f'` grows
by at least `λ` per step and the part spans less than `2δ`), and is bounded trivially. On the rest
`j + δ ≤ f' ≤ j + 1 − δ` on the whole real interval (since `f'` is monotone), so Kusmin–Landau
(`kusmin_landau_inv`) bounds it by `1/δ`. Taking `δ = √λ` (when `λ ≤ 1/4`; otherwise the trivial bound `N`
already suffices, as `α ≥ 1`) gives the stated form.
-/

namespace LeanClassics.VanDerCorput

open Real Finset

/-- The trivial bound `‖∑_{n<N} e(xₙ)‖ ≤ N`. -/
theorem norm_sum_e_le (x : ℕ → ℝ) (N : ℕ) : ‖∑ n ∈ range N, e (x n)‖ ≤ N := by
  refine (norm_sum_le _ _).trans ?_
  simp [norm_e]

/-- Splitting `∑_{n<N} g(m + n)` at `r ≤ N`. -/
theorem sum_split (g : ℝ → ℂ) (m : ℤ) (N r : ℕ) (hr : r ≤ N) :
    ∑ n ∈ range N, g (m + n) =
      ∑ n ∈ range r, g (m + n) + ∑ n ∈ range (N - r), g (((m + r : ℤ) : ℝ) + n) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hr
  rw [Nat.add_sub_cancel_left, sum_range_add]
  congr 1
  refine sum_congr rfl fun n _ => ?_
  congr 1
  push_cast
  ring

/-- A sub-block `[m + s, m + s + q − 1]` of `[m, m + N − 1]` when `s + q ≤ N`. -/
theorem Icc_sub (m : ℤ) (N s q : ℕ) (h : s + q ≤ N) :
    Set.Icc ((m + s : ℤ) : ℝ) ((m + s : ℤ) + (q : ℝ) - 1) ⊆ Set.Icc (m : ℝ) (m + N - 1) := by
  intro t ⟨h1, h2⟩
  have hsq : (s : ℝ) + q ≤ N := by exact_mod_cast h
  have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg s
  push_cast at h1 h2
  exact ⟨by linarith, by linarith⟩

/-- The mean value theorem for `f'`: `a ≤ f'' ≤ b` on `I = [m, m + N − 1]` gives
`a (t − s) ≤ f' t − f' s ≤ b (t − s)` for `s ≤ t` in `I`. -/
theorem mvt_bounds (f' f'' : ℝ → ℝ) (lo hi : ℝ) (a b : ℝ)
    (hf' : ∀ t ∈ Set.Icc lo hi, HasDerivAt f' (f'' t) t)
    (ha : ∀ t ∈ Set.Icc lo hi, a ≤ f'' t) (hb : ∀ t ∈ Set.Icc lo hi, f'' t ≤ b)
    (s t : ℝ) (hs : s ∈ Set.Icc lo hi) (ht : t ∈ Set.Icc lo hi) (hst : s ≤ t) :
    a * (t - s) ≤ f' t - f' s ∧ f' t - f' s ≤ b * (t - s) := by
  rcases hst.eq_or_lt with h | h
  · subst h; simp
  have hsub : Set.Icc s t ⊆ Set.Icc lo hi := Set.Icc_subset_Icc hs.1 ht.2
  obtain ⟨ξ, hξ, hξe⟩ := exists_hasDerivAt_eq_slope f' f'' h
    (fun x hx => (hf' x (hsub hx)).continuousAt.continuousWithinAt)
    (fun x hx => hf' x (hsub (Set.Ioo_subset_Icc_self hx)))
  have hξI := hsub (Set.Ioo_subset_Icc_self hξ)
  have hpos : 0 < t - s := by linarith
  have key : f' t - f' s = f'' ξ * (t - s) := by
    rw [hξe]; field_simp
  rw [key]
  exact ⟨mul_le_mul_of_nonneg_right (ha ξ hξI) hpos.le,
    mul_le_mul_of_nonneg_right (hb ξ hξI) hpos.le⟩

/-- One block. With `j = ⌊f'(m) + δ⌋` there is `1 ≤ r ≤ N` such that the first `r` terms have
`‖∑_{n<r} e(f(m + n))‖ ≤ 2δ/λ + 1 + 1/δ`, and if `r < N` then `f'(m + r) + δ ≥ j + 1`. -/
theorem block (f f' : ℝ → ℝ) (lam δ : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (m : ℤ) (N : ℕ) (hN : 1 ≤ N)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hg : ∀ s ∈ Set.Icc (m : ℝ) (m + N - 1), ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), s ≤ t →
      lam * (t - s) ≤ f' t - f' s) :
    ∃ r : ℕ, 1 ≤ r ∧ r ≤ N ∧
      (r < N → (⌊f' m + δ⌋ : ℝ) + 1 ≤ f' (m + r) + δ) ∧
      ‖∑ n ∈ range r, e (f (m + n))‖ ≤ 2 * δ / lam + 1 + 1 / δ := by
  classical
  set j : ℤ := ⌊f' m + δ⌋ with hj
  have hj1 : (j : ℝ) ≤ f' m + δ := Int.floor_le _
  have hj2 : f' m + δ < j + 1 := Int.lt_floor_add_one _
  have hmem : ∀ n : ℕ, n < N → ((m : ℝ) + n) ∈ Set.Icc (m : ℝ) (m + N - 1) := by
    intro n hn
    have : (n : ℝ) + 1 ≤ N := by exact_mod_cast hn
    exact ⟨by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)], by linarith⟩
  have hmono : ∀ s ∈ Set.Icc (m : ℝ) (m + N - 1), ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), s ≤ t →
      f' s ≤ f' t := by
    intro s hs t ht hst
    have := hg s hs t ht hst
    nlinarith
  -- the block end `r`
  obtain ⟨r, hrN, hrspec, hrmin⟩ : ∃ r : ℕ, r ≤ N ∧ (r = N ∨ (j : ℝ) + 1 ≤ f' (m + r) + δ) ∧
      ∀ n < r, f' (m + n) + δ < j + 1 := by
    have hex : ∃ n : ℕ, n = N ∨ (j : ℝ) + 1 ≤ f' (m + n) + δ := ⟨N, Or.inl rfl⟩
    refine ⟨Nat.find hex, Nat.find_min' hex (Or.inl rfl), Nat.find_spec hex, fun n hn => ?_⟩
    have := Nat.find_min hex hn
    push Not at this
    exact this.2
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · subst h
      rcases hrspec with h | h
      · omega
      · simp at h; linarith
    · exact h
  -- the end `s` of the near-integer part
  obtain ⟨s, hsr, hsspec, hsmin⟩ : ∃ s : ℕ, s ≤ r ∧ (s = r ∨ (j : ℝ) + δ ≤ f' (m + s)) ∧
      ∀ n < s, f' (m + n) < j + δ := by
    have hex : ∃ n : ℕ, n = r ∨ (j : ℝ) + δ ≤ f' (m + n) := ⟨r, Or.inl rfl⟩
    refine ⟨Nat.find hex, Nat.find_min' hex (Or.inl rfl), Nat.find_spec hex, fun n hn => ?_⟩
    have := Nat.find_min hex hn
    push Not at this
    exact this.2
  refine ⟨r, hr1, hrN, fun h => (hrspec.resolve_left (by omega)), ?_⟩
  rw [sum_split (fun x => e (f x)) m r s hsr]
  refine (norm_add_le _ _).trans ?_
  have hpart1 : ‖∑ n ∈ range s, e (f (m + n))‖ ≤ 2 * δ / lam + 1 := by
    refine (norm_sum_e_le (fun n => f (m + n)) s).trans ?_
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h; simp; positivity
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have h1 := hsmin s' (by omega)
    have h2 := hg m (by simpa using hmem 0 (by omega)) (m + s') (hmem s' (by omega))
      (by linarith [(Nat.cast_nonneg s' : (0 : ℝ) ≤ s')])
    have hlt : lam * s' < 2 * δ := by
      have : (m : ℝ) + s' - m = s' := by ring
      rw [this] at h2
      linarith
    have : (s' : ℝ) ≤ 2 * δ / lam := by
      rw [le_div_iff₀ hlam]; linarith
    push_cast
    linarith
  have hpart2 : ‖∑ n ∈ range (r - s), e (f (((m + s : ℤ) : ℝ) + n))‖ ≤ 1 / δ := by
    rcases hsr.eq_or_lt with h | h
    · rw [h, Nat.sub_self]; simp; positivity
    have hsub := Icc_sub m N s (r - s) (by omega)
    have hcast : ((m + s : ℤ) : ℝ) + ((r - s : ℕ) : ℝ) - 1 = m + ((r - 1 : ℕ) : ℝ) := by
      push_cast [Nat.cast_sub hsr, Nat.cast_sub hr1]
      ring
    have hlast := hrmin (r - 1) (by omega)
    have hfirst : (j : ℝ) + δ ≤ f' (m + s) := hsspec.resolve_left (by omega)
    refine kusmin_landau_inv f f' (m + s) (r - s) j δ hδ hδ' (fun t ht => hf t (hsub ht))
      (Or.inl fun a ha b hb hab => hmono a (hsub ha) b (hsub hb) hab) ?_
    intro t ht
    have htI := hsub ht
    constructor
    · have hsI := hmem s (by omega)
      have := hmono (m + s) hsI t htI (by have := ht.1; push_cast at this; linarith)
      linarith
    · have hlI := hmem (r - 1) (by omega)
      have := hmono t htI (m + ((r - 1 : ℕ) : ℝ)) hlI (by rw [← hcast]; exact ht.2)
      linarith
  linarith

/-- The block decomposition, by induction on the number `K` of integers crossed by `f' + δ`. -/
theorem blocks (f f' : ℝ → ℝ) (lam δ : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (K : ℕ) :
    ∀ (m : ℤ) (N : ℕ), 1 ≤ N →
      (∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t) →
      (∀ s ∈ Set.Icc (m : ℝ) (m + N - 1), ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), s ≤ t →
        lam * (t - s) ≤ f' t - f' s) →
      ⌊f' (m + N - 1) + δ⌋ ≤ ⌊f' m + δ⌋ + K →
      ‖∑ n ∈ range N, e (f (m + n))‖ ≤ (K + 1) * (2 * δ / lam + 1 + 1 / δ) := by
  have hC : 0 ≤ 2 * δ / lam + 1 + 1 / δ := by positivity
  induction K with
  | zero =>
    intro m N hN hf hg hK
    obtain ⟨r, hr1, hrN, hrnext, hr⟩ := block f f' lam δ hlam hδ hδ' m N hN hf hg
    rcases hrN.eq_or_lt with h | h
    · subst h; simpa using hr
    · exfalso
      have h1 := hrnext h
      have hrI : ((m : ℝ) + r) ∈ Set.Icc (m : ℝ) (m + N - 1) := by
        have : (r : ℝ) + 1 ≤ N := by exact_mod_cast h
        exact ⟨by linarith [(Nat.cast_nonneg r : (0 : ℝ) ≤ r)], by linarith⟩
      have hNI : ((m : ℝ) + N - 1) ∈ Set.Icc (m : ℝ) (m + N - 1) := ⟨hrI.1.trans hrI.2, le_rfl⟩
      have h2 := hg _ hrI _ hNI hrI.2
      have h2' : 0 ≤ lam * ((m : ℝ) + N - 1 - (m + r)) := mul_nonneg hlam.le (by linarith [hrI.2])
      have h3 : (⌊f' m + δ⌋ : ℝ) + 1 ≤ f' (m + N - 1) + δ := by linarith
      have h4 : ⌊f' m + δ⌋ + 1 ≤ ⌊f' (m + N - 1) + δ⌋ := by
        rw [Int.le_floor]; push_cast; exact h3
      push_cast at hK
      omega
  | succ K ih =>
    intro m N hN hf hg hK
    obtain ⟨r, hr1, hrN, hrnext, hr⟩ := block f f' lam δ hlam hδ hδ' m N hN hf hg
    rcases hrN.eq_or_lt with h | h
    · subst h
      refine hr.trans ?_
      have : (1 : ℝ) ≤ ((K + 1 : ℕ) : ℝ) + 1 := by push_cast; linarith [(Nat.cast_nonneg K : (0 : ℝ) ≤ K)]
      nlinarith
    rw [sum_split (fun x => e (f x)) m N r hrN]
    refine (norm_add_le _ _).trans ?_
    have hsub := Icc_sub m N r (N - r) (by omega)
    have hend : ((m + r : ℤ) : ℝ) + ((N - r : ℕ) : ℝ) - 1 = m + N - 1 := by
      push_cast [Nat.cast_sub hrN]
      ring
    have hstart : ((m + r : ℤ) : ℝ) = m + r := by push_cast; ring
    have h1 := hrnext h
    have hfl : ⌊f' m + δ⌋ + 1 ≤ ⌊f' ((m + r : ℤ) : ℝ) + δ⌋ := by
      rw [Int.le_floor, hstart]; push_cast; exact h1
    have hrest := ih (m + r) (N - r) (by omega) (fun t ht => hf t (hsub ht))
      (fun s hs t ht hst => hg s (hsub hs) t (hsub ht) hst)
      (by rw [hend]; push_cast at hK; omega)
    have hrest' : ‖∑ n ∈ range (N - r), e (f (((m + r : ℤ) : ℝ) + n))‖ ≤
        (K + 1) * (2 * δ / lam + 1 + 1 / δ) := hrest
    have hc : ((K + 1 : ℕ) : ℝ) + 1 = (K + 1) + 1 := by push_cast; ring
    rw [hc]
    linarith

/-- **Van der Corput's second-derivative test, with a free cut-off `δ`.** If `f' = f′` and `f'' = f′′` on
`[m, m + N − 1]`, `N ≥ 1`, and `λ ≤ f'' ≤ αλ` there (`λ > 0`), then for every `0 < δ ≤ 1/2`,
`‖∑_{n<N} e(f(m + n))‖ ≤ (αλ(N − 1) + 2)(2δ/λ + 1 + 1/δ)`. -/
theorem van_der_corput_second_delta (f f' f'' : ℝ → ℝ) (m : ℤ) (N : ℕ) (hN : 1 ≤ N)
    (lam alpha δ : ℝ) (hlam : 0 < lam) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f' (f'' t) t)
    (hlo : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), lam ≤ f'' t)
    (hhi : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), f'' t ≤ alpha * lam) :
    ‖∑ n ∈ range N, e (f (m + n))‖ ≤ (alpha * lam * (N - 1) + 2) * (2 * δ / lam + 1 + 1 / δ) := by
  have hg : ∀ s ∈ Set.Icc (m : ℝ) (m + N - 1), ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), s ≤ t →
      lam * (t - s) ≤ f' t - f' s :=
    fun s hs t ht hst => (mvt_bounds f' f'' _ _ lam (alpha * lam) hf' hlo hhi s t hs ht hst).1
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmI : (m : ℝ) ∈ Set.Icc (m : ℝ) (m + N - 1) := ⟨le_rfl, by linarith⟩
  have heI : ((m : ℝ) + N - 1) ∈ Set.Icc (m : ℝ) (m + N - 1) := ⟨by linarith, le_rfl⟩
  have hS := (mvt_bounds f' f'' _ _ lam (alpha * lam) hf' hlo hhi _ _ hmI heI (by linarith)).2
  have hS0 := hg _ hmI _ heI (by linarith)
  set D : ℤ := ⌊f' (m + N - 1) + δ⌋ - ⌊f' m + δ⌋ with hD
  have hD0 : 0 ≤ D := by
    rw [hD, sub_nonneg]
    exact Int.floor_mono (by nlinarith)
  have hDr : (D : ℝ) ≤ f' (m + N - 1) - f' m + 1 := by
    rw [hD]; push_cast
    have := Int.floor_le (f' (m + N - 1) + δ)
    have := Int.sub_one_lt_floor (f' m + δ)
    linarith
  have hK := blocks f f' lam δ hlam hδ hδ' D.toNat m N hN hf hg
    (by have := Int.self_le_toNat D; omega)
  have hKr : ((D.toNat : ℕ) : ℝ) = D := by
    have := Int.toNat_of_nonneg hD0
    exact_mod_cast this
  rw [hKr] at hK
  refine hK.trans ?_
  have hC : 0 ≤ 2 * δ / lam + 1 + 1 / δ := by positivity
  apply mul_le_mul_of_nonneg_right _ hC
  have : (m : ℝ) + N - 1 - m = N - 1 := by ring
  rw [this] at hS
  linarith

/-- **Van der Corput's second-derivative test** (Graham–Kolesnik Theorem 2.2, explicit). If `f' = f′` and
`f'' = f′′` on `[m, m + N − 1]` and `λ ≤ f'' ≤ αλ` there (`λ > 0`), then
`‖∑_{n<N} e(f(m + n))‖ ≤ 4 α N √λ + 7/√λ`. -/
theorem van_der_corput_second (f f' f'' : ℝ → ℝ) (m : ℤ) (N : ℕ) (lam alpha : ℝ) (hlam : 0 < lam)
    (hf : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f (f' t) t)
    (hf' : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), HasDerivAt f' (f'' t) t)
    (hlo : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), lam ≤ f'' t)
    (hhi : ∀ t ∈ Set.Icc (m : ℝ) (m + N - 1), f'' t ≤ alpha * lam) :
    ‖∑ n ∈ range N, e (f (m + n))‖ ≤ 4 * alpha * N * √lam + 7 / √lam := by
  have hsq : 0 < √lam := Real.sqrt_pos.mpr hlam
  rcases Nat.eq_zero_or_pos N with hN0 | hN
  · subst hN0; simp; positivity
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmI : (m : ℝ) ∈ Set.Icc (m : ℝ) (m + N - 1) := ⟨le_rfl, by linarith⟩
  have halpha : 1 ≤ alpha := by
    have := (hlo m hmI).trans (hhi m hmI)
    nlinarith
  rcases le_or_gt lam (1 / 4) with hl | hl
  · set δ := √lam with hδdef
    have hδsq : δ ^ 2 = lam := Real.sq_sqrt hlam.le
    have hδ' : δ ≤ 1 / 2 := by nlinarith
    have h := van_der_corput_second_delta f f' f'' m N hN lam alpha δ hlam hsq hδ' hf hf' hlo hhi
    refine h.trans ?_
    rw [← hδsq]
    have hP : 0 ≤ alpha * δ ^ 2 * (N - 1) := by
      have : (0 : ℝ) ≤ N - 1 := by linarith
      positivity
    have e1 : (alpha * δ ^ 2 * (N - 1) + 2) * (2 * δ / δ ^ 2 + 1 + 1 / δ) =
        (alpha * δ ^ 2 * (N - 1) + 2) * (3 + δ) / δ := by
      field_simp
      ring
    have e2 : 4 * alpha * N * δ + 7 / δ = (4 * alpha * N * δ ^ 2 + 7) / δ := by
      field_simp
    rw [e1, e2]
    apply div_le_div_of_nonneg_right _ hsq.le
    have hPd : alpha * δ ^ 2 * (N - 1) * δ ≤ alpha * δ ^ 2 * (N - 1) * (1 / 2) :=
      mul_le_mul_of_nonneg_left hδ' hP
    have hN' : alpha * δ ^ 2 * (N - 1) ≤ alpha * δ ^ 2 * N := by
      have : 0 ≤ alpha * δ ^ 2 := by positivity
      nlinarith
    nlinarith
  · refine (norm_sum_e_le (fun n => f (m + n)) N).trans ?_
    have hs : 1 / 2 < √lam := by
      rw [show (1 : ℝ) / 2 = √((1 / 2) ^ 2) by rw [Real.sqrt_sq]; norm_num]
      exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
    have h7 : 0 ≤ 7 / √lam := by positivity
    have : (N : ℝ) ≤ 4 * alpha * N * √lam := by
      have : 2 ≤ 4 * alpha * √lam := by nlinarith
      nlinarith
    linarith

end LeanClassics.VanDerCorput
end


open Filter Finset Real
open scoped BigOperators

private lemma bracket (x d : ℝ) (hd : 0 < d) (hd1 : d < 1) :
    let B := fun u : ℝ => bernoulliFun 2 (Int.fract u)
    B (x-d)-B x-d^2 ≤ 2*d*(1/2-Int.fract x) ∧
    2*d*(1/2-Int.fract x) ≤ B x-B (x+d)+d^2 := by
  intro B
  let y := Int.fract x
  have hy : 0 ≤ y := Int.fract_nonneg _
  have hy1 : y < 1 := Int.fract_lt_one _
  have hxy : x - y = (⌊x⌋ : ℝ) := by
    have hyeq : y = x - (⌊x⌋ : ℝ) := by
      dsimp only [y]
      rw [Int.fract]
    rw [hyeq]
    ring
  change B (x-d)-B x-d^2 ≤ 2*d*(1/2-y) ∧ 2*d*(1/2-y) ≤ B x-B (x+d)+d^2
  dsimp only [B]
  repeat rw [bernoulliFun_two]
  change _ ≤ 2*d*(1/2-y) ∧ 2*d*(1/2-y) ≤ y^2-y+6⁻¹-(_^2-_+6⁻¹)+d^2
  constructor
  · by_cases h : d ≤ y
    · have he : Int.fract (x-d) = y-d := Int.fract_eq_iff.mpr
        ⟨by linarith,by linarith,⌊x⌋,by linarith⟩
      rw [he]
      change _ - (y^2-y+6⁻¹) - d^2 ≤ _
      nlinarith
    · have he : Int.fract (x-d) = y-d+1 := Int.fract_eq_iff.mpr
        ⟨by linarith,by linarith,⌊x⌋-1,by push_cast; linarith⟩
      rw [he]
      change _ - (y^2-y+6⁻¹) - d^2 ≤ _
      nlinarith
  · by_cases h : y+d < 1
    · have he : Int.fract (x+d) = y+d := Int.fract_eq_iff.mpr
        ⟨by linarith,h,⌊x⌋,by linarith⟩
      rw [he]
      nlinarith
    · have he : Int.fract (x+d) = y+d-1 := Int.fract_eq_iff.mpr
        ⟨by linarith,by linarith,⌊x⌋+1,by push_cast; linarith⟩
      rw [he]
      nlinarith

private lemma sum_bracket {ι : Type*} (S : Finset ι) (f : ι → ℝ) (d E : ℝ)
    (hd : 0 < d) (hd1 : d < 1) (h : ∀ u : ℝ,
      |∑ i ∈ S, bernoulliFun 2 (Int.fract (f i+u))| ≤ E) :
    |∑ i ∈ S, (1/2-Int.fract (f i))| ≤ S.card*d/2+E/d := by
  let B := fun u : ℝ => ∑ i ∈ S, bernoulliFun 2 (Int.fract (f i+u))
  have h0 := abs_le.mp (h 0)
  simp only [add_zero] at h0
  have hp := abs_le.mp (h d)
  have hm := abs_le.mp (h (-d))
  have h1 := sum_le_sum (s:=S) (fun i _ => (bracket (f i) d hd hd1).1)
  have h2 := sum_le_sum (s:=S) (fun i _ => (bracket (f i) d hd hd1).2)
  simp only [sum_sub_distrib,sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum,sub_eq_add_neg (f _) d] at h1 h2
  set Δ : ℝ := (S.card : ℝ) - 2 * ∑ x ∈ S, Int.fract (f x)
  have hsumeq : ∑ i ∈ S, (1 / 2 - Int.fract (f i)) = Δ / 2 := by
    simp only [Δ, sum_sub_distrib, sum_const, nsmul_eq_mul]
    ring
  have hup : d * Δ ≤ 2 * E + d ^ 2 * (S.card : ℝ) := by
    have hB0 : ∑ x ∈ S, bernoulliFun 2 (Int.fract (f x)) ≤ E := h0.2
    have hBp : -E ≤ ∑ x ∈ S, bernoulliFun 2 (Int.fract (f x + d)) := hp.1
    linarith
  have hlo : -(2 * E + d ^ 2 * (S.card : ℝ)) ≤ d * Δ := by
    have hBm : -E ≤ ∑ x ∈ S, bernoulliFun 2 (Int.fract (f x + -d)) := hm.1
    have hB0 : ∑ x ∈ S, bernoulliFun 2 (Int.fract (f x)) ≤ E := h0.2
    linarith
  rw [hsumeq, abs_le]
  refine ⟨?_, ?_⟩
  · have hden : 0 < 2 * d := by positivity
    rw [← mul_le_mul_iff_of_pos_left hden]
    have hL : 2 * d * -(S.card * d / 2 + E / d) = -(2 * E + d ^ 2 * (S.card : ℝ)) := by
      field_simp [hd.ne']
      ring
    have hR : 2 * d * (Δ / 2) = d * Δ := by field_simp
    linarith
  · have hden : 0 < 2 * d := by positivity
    rw [← mul_le_mul_iff_of_pos_left hden]
    have hL : 2 * d * (Δ / 2) = d * Δ := by field_simp
    have hR : 2 * d * (S.card * d / 2 + E / d) = 2 * E + d ^ 2 * (S.card : ℝ) := by
      field_simp [hd.ne']
      ring
    linarith

private lemma cos_series (x : ℝ) :
    HasSum (fun h : ℕ => (1/(h:ℝ)^2)*cos (2*π*h*x))
      (π^2*bernoulliFun 2 (Int.fract x)) := by
  have eqf (h : ℕ) : cos (2*π*h*Int.fract x) = cos (2*π*h*x) := by
    have e : 2*π*h*Int.fract x =
        2*π*h*x-(((h:ℤ)*⌊x⌋:ℤ):ℝ)*(2*π) := by
      simp only [Int.fract,Int.cast_mul,Int.cast_natCast]
      ring
    rw [e,cos_sub_int_mul_two_pi]
  have hh := hasSum_one_div_nat_pow_mul_cos (k:=1) (by decide)
    (show Int.fract x ∈ Set.Icc (0:ℝ) 1 from ⟨Int.fract_nonneg _,(Int.fract_lt_one _).le⟩)
  simp only [Nat.mul_one,Nat.reduceAdd,Nat.factorial_two,Nat.cast_ofNat,neg_one_sq,one_mul,eqf] at hh
  convert hh using 1
  change π^2*bernoulliFun 2 (Int.fract x)=(2*π)^2/2/2*bernoulliFun 2 (Int.fract x)
  ring

private lemma tail_square {a : ℕ} (ha : 0 < a) (k : ℕ) :
    ∑ j ∈ range k, 1/((a+j+1:ℕ):ℝ)^2 ≤ 1/(a:ℝ)-1/((a+k:ℕ):ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ]
    have hp : 0 < ((a+k:ℕ):ℝ) := by positivity
    have hq : 0 < ((a+k+1:ℕ):ℝ) := by positivity
    have step : 1/((a+k+1:ℕ):ℝ)^2 ≤ 1/((a+k:ℕ):ℝ)-1/((a+k+1:ℕ):ℝ) := by
      push_cast
      field_simp
      nlinarith
    change _ ≤ 1/(a:ℝ)-1/((a+k+1:ℕ):ℝ)
    linarith

private lemma spectral_cut (a : ℕ → ℝ) {L C M : ℝ} {H : ℕ} (hH : 0 < H)
    (hC : 0 ≤ C) (hM : 0 ≤ M) (hs : HasSum (fun h : ℕ => (1 / ((h : ℕ) : ℝ) ^ 2) * a h) L)
    (head : ∀ h : ℕ, 0 < h → h ≤ H → |a h| ≤ C) (allh : ∀ h, |a h| ≤ M) :
    |L| ≤ (∑' h : ℕ, 1/(h:ℝ)^2)*C + M/H := by
  let g := fun h : ℕ => (1 / ((h : ℕ) : ℝ) ^ 2) * a h
  have sm := (Real.summable_one_div_nat_pow (p:=2)).mpr (by decide)
  have hd : |∑ h ∈ range (H+1),g h| ≤ (∑' h : ℕ,1/(h:ℝ)^2)*C := by
    calc _ ≤ ∑ h ∈ range (H+1),|g h| := abs_sum_le_sum_abs _ _
         _ ≤ ∑ h ∈ range (H+1),(1/(h:ℝ)^2)*C := by
           apply sum_le_sum
           intro h hh
           by_cases hz : h=0
           · simp [g,hz]
           · simp only [g,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/(h:ℝ)^2)]
             exact mul_le_mul_of_nonneg_left (head h (by omega) (by have := mem_range.mp hh; omega)) (by positivity)
         _ ≤ _ := by
           rw [←sum_mul]
           exact mul_le_mul_of_nonneg_right (sm.sum_le_tsum _ (fun j _ => by positivity)) hC
  have ht (k : ℕ) : |∑ j ∈ range k,g ((H+1)+j)| ≤ M/H := by
    calc _ ≤ ∑ j ∈ range k,|g ((H+1)+j)| := abs_sum_le_sum_abs _ _
         _ ≤ ∑ j ∈ range k,(1/((H+j+1:ℕ):ℝ)^2)*M := by
           apply sum_le_sum
           intro j _
           rw [show H+1+j=H+j+1 by omega]
           simp only [g,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/((H+j+1:ℕ):ℝ)^2)]
           exact mul_le_mul_of_nonneg_left (allh _) (by positivity)
         _ ≤ (1/H-1/((H+k:ℕ):ℝ))*M := by
           rw [←sum_mul]
           exact mul_le_mul_of_nonneg_right (tail_square hH k) hM
         _ ≤ _ := by
           rw [sub_mul]
           have hnonneg : 0 ≤ 1 / ((H + k : ℕ) : ℝ) * M := by positivity
           have hdiv : (1 / (H : ℝ)) * M = M / H := by ring
           linarith
  have hidx : Tendsto (fun k : ℕ => (H + 1) + k) atTop atTop :=
    (tendsto_add_atTop_nat (H + 1)).congr' (Filter.Eventually.of_forall fun k => Nat.add_comm k (H + 1))
  have conv : Tendsto (fun k : ℕ => |∑ j ∈ range ((H+1)+k),g j|) atTop (nhds |L|) :=
    (hs.tendsto_sum_nat.comp hidx).abs
  apply le_of_tendsto conv
  filter_upwards with k
  rw [sum_range_add]
  exact (abs_add_le ..).trans (add_le_add hd (ht k))



private lemma sum_cos_series {ι : Type*} (S : Finset ι) (x : ι → ℝ) :
    HasSum (fun h:ℕ => (1/(h:ℝ)^2)*(∑ i∈S, cos (2*π*h*x i)))
      (π^2*(∑ i∈S,bernoulliFun 2 (Int.fract (x i)))) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simpa only [sum_insert hi,mul_add] using (cos_series (x i)).add ih

private lemma smooth_discrepancy :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} (S : Finset ι) (x : ι → ℝ) (d B : ℝ) (H : ℕ),
      0 < d → d < 1 → 0 ≤ B → 0 < H →
      (∀ u : ℝ, ∀ h:ℕ, 0<h → h≤H → |∑ i∈S, cos (2*π*h*(x i+u))| ≤ B) →
      |∑ i∈S, (1/2-Int.fract (x i))| ≤ S.card*d/2+C*(B+S.card/(H:ℝ))/d := by
  let K := ∑' h : ℕ,1/(h:ℝ)^2
  have kn : 0 ≤ K := tsum_nonneg (fun _ => by positivity)
  refine ⟨(K+1)/π^2,by positivity,?_⟩
  intro ι S x d B H hd hd1 hb hh freq
  apply sum_bracket S x d _ hd hd1
  intro u
  let a := fun h:ℕ => ∑ i∈S,cos (2*π*h*(x i+u))
  have big (h : ℕ) : |a h| ≤ (S.card:ℝ) := by
    calc _ ≤ ∑ i∈S, |cos (2*π*h*(x i+u))| := abs_sum_le_sum_abs _ _
         _ ≤ ∑ _i∈S, (1:ℝ) := sum_le_sum fun _ _ => abs_cos_le_one _
         _ = _ := by simp
  have h := spectral_cut a hh hb (Nat.cast_nonneg S.card)
    (sum_cos_series S (fun i => x i+u)) (freq u) big
  rw [abs_mul,abs_of_pos (sq_pos_of_pos pi_pos)] at h
  change π^2*_ ≤ K*B+_ at h
  have hratio : 0 ≤ (S.card:ℝ)/H := by positivity
  have hpp := sq_pos_of_pos pi_pos
  apply le_of_mul_le_mul_left (a:=π^2) _ hpp
  calc π^2*_ ≤ K*B+S.card/(H:ℝ) := h
       _ ≤ (K+1)*(B+S.card/(H:ℝ)) := by nlinarith only [mul_nonneg kn hratio,hb]
       _ = _ := by
         have hpi : π ≠ 0 := pi_ne_zero
         field_simp [hpi]



open Finset Complex
open scoped ComplexConjugate

private lemma expand_square {α : Type*} (Q : Finset α) (f : α → ℂ) :
    ‖∑ q ∈ Q, f q‖^2 = ∑ q ∈ Q, ∑ v ∈ Q, (f q*conj (f v)).re := by
  calc _ = ((∑ q ∈ Q,f q)*conj (∑ q ∈ Q,f q)).re := by
          rw [Complex.mul_conj,Complex.ofReal_re,Complex.sq_norm]
       _ = _ := by
         simp only [map_sum, sum_mul, mul_sum, Complex.re_sum]
         exact sum_comm

private lemma block_energy {α β : Type*} (I : Finset α) (Q : Finset β)
    (f : α → β → ℂ) {E : ℝ} (hE : 0 ≤ E) (unit : ∀ i∈I, ∀ q∈Q, ‖f i q‖ ≤ 1)
    (corr : ∀ q∈Q,∀ v∈Q,q≠v → ‖∑ i∈I, f i q*conj (f i v)‖ ≤ E) :
    (∑ i∈I, ‖∑ q∈Q, f i q‖^2) ≤ (Q.card:ℝ)*(I.card+Q.card*E) := by
  classical
  simp_rw [expand_square]
  rw [sum_comm]
  calc _ ≤ ∑ q∈Q, ((I.card:ℝ)+Q.card*E) := by
         apply sum_le_sum
         intro q hq
         rw [sum_comm]
         calc _ ≤ ∑ v∈Q,(if v=q then (I.card:ℝ) else 0) + ∑ _v∈Q,E := by
                rw [←sum_add_distrib]
                apply sum_le_sum
                intro v hv
                rw [←Complex.re_sum]
                by_cases eq : v=q
                · subst v
                  simp only [if_true]
                  apply le_trans _ (le_add_of_nonneg_right hE)
                  rw [Complex.re_sum]
                  calc _ ≤ ∑ _i∈I,(1:ℝ) := by
                         apply sum_le_sum
                         intro i hi
                         rw [Complex.mul_conj,Complex.ofReal_re,←Complex.sq_norm]
                         nlinarith [unit i hi q hq,norm_nonneg (f i q),
                           mul_self_le_mul_self (norm_nonneg (f i q)) (unit i hi q hq)]
                       _ = _ := by simp
                · simp only [if_neg eq,zero_add]
                  exact (Complex.re_le_norm _).trans (corr q hq v hv (Ne.symm eq))
              _ = _ := by simp [hq]
       _ = _ := by simp; ring

private lemma block_cauchy {α β γ : Type*} (P I : Finset α) (B : Finset β)
    (Q : β → Finset γ) (f : α → γ → ℂ) (sub : P ⊆ I) {E R : ℝ}
    (hE : 0 ≤ E) (bound : ∀ b∈B, ((Q b).card:ℝ) ≤ R)
    (unit : ∀ b∈B,∀ i∈I,∀ q∈Q b, ‖f i q‖ ≤ 1)
    (corr : ∀ b∈B,∀ q∈Q b,∀ v∈Q b,q≠v → ‖∑ i∈I, f i q*conj (f i v)‖ ≤ E) :
    ‖∑ b∈B,∑ i∈P,∑ q∈Q b,f i q‖^2 ≤
      (B.card:ℝ)*P.card*(∑ b∈B,((Q b).card:ℝ))*(I.card+R*E) := by
  classical
  let F (b : β) (i : α) := ∑ q∈Q b,f i q
  have one (b:β) (hb:b∈B) : ∑ i∈P, ‖F b i‖^2 ≤ ((Q b).card:ℝ)*(I.card+R*E) := by
    calc _ ≤ ∑ i∈I,‖F b i‖^2 := sum_le_sum_of_subset_of_nonneg sub (fun _ _ _ => sq_nonneg _)
         _ ≤ _ := (block_energy I (Q b) f hE (unit b hb) (corr b hb)).trans (by gcongr; exact bound b hb)
  let D := B ×ˢ P
  let g (u : β×α) := F u.1 u.2
  have hh := norm_sum_le D g
  have cs := (sq_sum_le_card_mul_sum_sq (s:=D) (f:=fun u => ‖g u‖))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hh 2
  have htot : ∑ u∈D,‖g u‖^2 ≤ (∑ b∈B,((Q b).card:ℝ))*(I.card+R*E) := by
    rw [sum_mul]
    simpa only [D,g,sum_product] using sum_le_sum one
  have h := hsq.trans (cs.trans (mul_le_mul_of_nonneg_left htot (Nat.cast_nonneg _)))
  simpa only [D,g,F,sum_product,card_product,Nat.cast_mul,mul_assoc] using h


open Finset Real LeanClassics.VanDerCorput
open scoped ComplexConjugate

private theorem frac_block (N h t q v:ℕ) (hN:2≤N) (hh:0<h) (hi:h≤N^20)
    (lt:N^1000≤t) (ut:t≤N^1001) (lq:N^251<q) (lqv:q<v) (uv:v≤N^252)
    (near:v-q≤N^40) :
    ‖∑ p∈Ioc (N^251) (N^252), e ((h:ℝ)*(t:ℝ)/((p:ℝ)*q)) *
      conj (e ((h:ℝ)*(t:ℝ)/((p:ℝ)*v)))‖ ≤ 15*(N:ℝ)^188 := by
  let X : ℝ := N
  have xp : 1≤X := by dsimp [X]; exact_mod_cast (by omega : 1≤N)
  have xp0 := lt_of_lt_of_le zero_lt_one xp
  have qp : 0<(q:ℝ) := by exact_mod_cast (by omega : 0<q)
  have vp : 0<(v:ℝ) := by exact_mod_cast (by omega : 0<v)
  have h1 : 1≤(h:ℝ) := by exact_mod_cast (by omega : 1≤h)
  have gu : (h:ℝ)≤X^20 := by dsimp [X]; exact_mod_cast hi
  have tl : X^1000≤(t:ℝ) := by dsimp [X]; exact_mod_cast lt
  have tu : (t:ℝ)≤X^1001 := by dsimp [X]; exact_mod_cast ut
  have ql : X^251≤(q:ℝ) := by dsimp [X]; exact_mod_cast lq.le
  have vl : X^251≤(v:ℝ) := by dsimp [X]; exact_mod_cast (by omega : N^251≤v)
  have qu : (q:ℝ)≤X^252 := by dsimp [X]; exact_mod_cast (by omega : q≤N^252)
  have vu : (v:ℝ)≤X^252 := by dsimp [X]; exact_mod_cast uv
  have gap : 1 ≤ (v : ℝ) - (q : ℝ) := by
    have hqv : q + 1 ≤ v := lqv
    have : ((q + 1 : ℕ) : ℝ) ≤ (v : ℝ) := by exact_mod_cast hqv
    push_cast at this
    linarith
  have gapu : (v:ℝ)-q≤X^40 := by
    have z : ((v-q:ℕ):ℝ)≤X^40 := by dsimp [X]; exact_mod_cast near
    rwa [Nat.cast_sub lqv.le] at z
  let A := (h:ℝ)*t*((v:ℝ)-q)/(q*v)
  have al : X^496≤A := by
    apply (le_div_iff₀ (mul_pos qp vp)).mpr
    calc X^496*(q*v) ≤ X^496*(X^252*X^252) := by gcongr
         _ = X^1000 := by ring
         _ ≤ (h:ℝ)*t*((v:ℝ)-q) := by
             calc _ ≤ (1:ℝ)*t*1 := by simpa using tl
                  _ ≤ _ := by gcongr
  have au : A≤X^559 := by
    apply (div_le_iff₀ (mul_pos qp vp)).mpr
    calc (h:ℝ)*t*((v:ℝ)-q) ≤ X^20*X^1001*X^40 := by gcongr
         _ = X^559*(X^251*X^251) := by ring
         _ ≤ _ := by gcongr
  let m := N^251+1
  let M := N^252-N^251
  have base : N^251≤N^252 := Nat.pow_le_pow_right (by omega) (by decide)
  have sub : ((M:ℕ):ℝ) = X^252-X^251 := by dsimp [M,X]; rw [Nat.cast_sub base]; push_cast; rfl
  have mm : (m:ℝ)=X^251+1 := by simp [m,X]
  let f := fun x:ℝ => A/x
  let f' := fun x:ℝ => -A/x^2
  let f'' := fun x:ℝ => 2*A/x^3
  have bounds (x:ℝ) (hx:x∈Set.Icc (((m:ℕ):ℤ):ℝ) (((m:ℕ):ℤ)+M-1)) :
      X^251≤x ∧ x≤X^252 := by
    simp only [Int.cast_natCast] at hx
    rw [mm,sub] at hx
    exact ⟨by linarith [hx.1],by linarith [hx.2]⟩
  let lam := (X^260)⁻¹
  let alpha := 2*X^66
  have vd := van_der_corput_second f f' f'' (m:ℤ) M lam alpha (by dsimp [lam]; positivity)
    (by intro x hx; obtain ⟨xl,_⟩ := bounds x hx
        have xpos := lt_of_lt_of_le (pow_pos xp0 251) xl
        refine HasDerivAt.congr_deriv
          ((hasDerivAt_const x A).fun_div (hasDerivAt_id x) xpos.ne') ?_
        change (0 * x - A * 1) / x ^ 2 = -A / x ^ 2
        field_simp [xpos.ne']
        ring)
    (by intro x hx; obtain ⟨xl,_⟩ := bounds x hx
        have xpos : 0 < x := lt_of_lt_of_le (pow_pos xp0 251) xl
        have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 xpos.ne'
        refine HasDerivAt.congr_deriv
          ((hasDerivAt_const x (-A)).fun_div ((hasDerivAt_id x).fun_pow 2) hx2) ?_
        change (0 * x ^ 2 - (-A) * ((2 : ℕ) * x ^ (2 - 1) * (1 : ℝ))) / (x ^ 2) ^ 2
          = 2 * A / x ^ 3
        field_simp [xpos.ne']
        ring)
    (by intro x hx; obtain ⟨xl,xu⟩ := bounds x hx
        have xpos := lt_of_lt_of_le (pow_pos xp0 251) xl
        change (X^260)⁻¹≤2*A/x^3
        rw [le_div_iff₀ (pow_pos xpos _),inv_mul_eq_div,div_le_iff₀ (pow_pos xp0 _)]
        calc x^3 ≤ (X^252)^3 := by gcongr
             _ = X^496*X^260 := by ring
             _ ≤ _ := by gcongr; linarith [pow_pos xp0 496])
    (by intro x hx; obtain ⟨xl,xu⟩ := bounds x hx
        have xpos := lt_of_lt_of_le (pow_pos xp0 251) xl
        change 2*A/x^3 ≤ 2*X^66*(X^260)⁻¹
        rw [←div_eq_mul_inv,div_le_div_iff₀ (pow_pos xpos _) (pow_pos xp0 _)]
        calc 2*A*X^260 ≤ 2*X^559*X^260 := by gcongr
             _ = 2*X^66*(X^251)^3 := by ring
             _ ≤ _ := by gcongr)
  have sq : √lam=(X^130)⁻¹ := by
    dsimp [lam]
    rw [Real.sqrt_inv,show X^260=(X^130)^2 by ring,Real.sqrt_sq (by positivity)]
  have um : (M:ℝ)≤X^252 := by rw [sub]; linarith [pow_pos xp0 251]
  have total : 4*alpha*M*√lam+7/√lam≤15*X^188 := by
    rw [sq]
    dsimp only [alpha]
    have xz : X^130≠0 := ne_of_gt (pow_pos xp0 _)
    calc _ ≤ 4*(2*X^66)*X^252*(X^130)⁻¹+7/(X^130)⁻¹ := by gcongr
         _ = 8*X^188+7*X^130 := by field_simp; ring
         _ ≤ _ := by nlinarith only [pow_le_pow_right₀ xp (show 130≤188 by decide)]
  apply le_trans (le_of_eq ?_) (vd.trans total)
  congr 1
  rw [←Ico_add_one_add_one_eq_Ioc,sum_Ico_eq_sum_range]
  change (∑ j∈range (N^252+1-(N^251+1)),_) = _
  rw [show N^252+1-(N^251+1)=M by dsimp [M]; omega]
  apply sum_congr rfl
  intro j hj
  rw [←e_neg,←e_add]
  congr 1
  simp only [Int.cast_natCast,Nat.cast_add,Nat.cast_one,Nat.cast_pow]
  dsimp only [f,A,m]
  push_cast
  field_simp
  ring


private theorem pair_phase (N h t:ℕ) (hN:2≤N) (hh:0<h) (hi:h≤N^20)
    (lt:N^1000≤t) (ut:t≤N^1001) :
    let P := (Ioc (N^251) (N^252)).filter Nat.Prime
    ‖∑ w∈P ×ˢ P, e ((h:ℝ)*(t:ℝ)/((w.1:ℝ)*w.2))‖ ≤ 6*(N:ℝ)^484 := by
  classical
  intro P
  let I := Ioc (N^251) (N^252)
  let R := N^40
  let B := range (N^212+1)
  let Q (b:ℕ) := P.filter (fun q => q/R=b)
  let f (p q:ℕ) := e ((h:ℝ)*(t:ℝ)/((p:ℝ)*q))
  have sub : P⊆I := filter_subset _ _
  have rpos : 0<R := by dsimp [R]; positivity
  have maps (q:ℕ) (hq:q∈P) : q/R∈B := by
    change q/R∈range (N^212+1)
    rw [mem_range,Nat.div_lt_iff_lt_mul rpos]
    have high := (mem_Ioc.mp (sub hq)).2
    have fact : N^252=N^212*R := by dsimp [R]; ring
    rw [fact] at high
    nlinarith
  have box {b q:ℕ} (hq:q∈Q b) : q∈Ico (b*R) ((b+1)*R) := by
    obtain ⟨_,he⟩ := mem_filter.mp hq
    change q/R=b at he
    apply mem_Ico.mpr
    rw [←he]
    exact ⟨Nat.div_mul_le_self _ _,(Nat.div_lt_iff_lt_mul rpos).mp (Nat.lt_succ_self _)⟩
  have cards (b:ℕ) : (Q b).card≤R := by
    calc _ ≤ (Ico (b*R) ((b+1)*R)).card := card_le_card (fun _ hq => box hq)
         _ = _ := by simp [Nat.add_mul]
  have corr (b:ℕ) (_:b∈B) (q:ℕ) (hq:q∈Q b) (v:ℕ) (hv:v∈Q b) (hne:q≠v) :
      ‖∑ i∈I,f i q*conj (f i v)‖≤15*(N:ℝ)^188 := by
    have aux {x y:ℕ} (hx:x∈Q b) (hy:y∈Q b) (xy:x<y) :
        ‖∑ i∈I,f i x*conj (f i y)‖≤15*(N:ℝ)^188 := by
      have xx := mem_Ioc.mp (sub (mem_filter.mp hx).1)
      have yy := mem_Ioc.mp (sub (mem_filter.mp hy).1)
      have xb := mem_Ico.mp (box hx)
      have yb := mem_Ico.mp (box hy)
      have gap : y-x≤R := by rw [Nat.add_mul,Nat.one_mul] at yb; omega
      exact frac_block N h t x y hN hh hi lt ut xx.1 xy yy.2 gap
    rcases lt_or_gt_of_ne hne with a|a
    · exact aux hq hv a
    · have h := aux hv hq a
      rw [←Complex.norm_conj (∑ i∈I,f i q*conj (f i v)),map_sum]
      simpa only [map_mul,starRingEnd_self_apply,mul_comm] using h
  have hc := block_cauchy P I B Q f sub (by positivity : 0≤15*(N:ℝ)^188)
    (R:=(R:ℝ)) (fun b _ => by exact_mod_cast cards b)
    (fun _ _ _ _ _ _ => (norm_e _).le) corr
  have grouping : ∑ w∈P ×ˢ P, f w.1 w.2 = ∑ b∈B,∑ i∈P,∑ q∈Q b,f i q := by
    rw [sum_product,sum_comm (s:=B)]
    apply sum_congr rfl
    intro i _
    symm
    exact sum_fiberwise_of_maps_to maps (f i)
  have qc : ∑ b∈B,((Q b).card:ℝ) = P.card := by
    exact_mod_cast (card_eq_sum_card_fiberwise maps).symm
  have ic : I.card≤N^252 := by simp [I]
  have pc : (P.card:ℝ)≤(N:ℝ)^252 := by exact_mod_cast (card_le_card sub).trans ic
  have ic' : (I.card:ℝ)≤(N:ℝ)^252 := by exact_mod_cast ic
  have xp : 1≤(N:ℝ) := by exact_mod_cast (by omega : 1≤N)
  have bc : (B.card:ℝ)≤2*(N:ℝ)^212 := by
    simp [B]
    linarith [one_le_pow₀ xp (n:=212)]
  have exp : (N:ℝ)^40*(N:ℝ)^188≤(N:ℝ)^252 := by
    rw [←pow_add]; exact pow_le_pow_right₀ xp (by decide)
  have rb : (I.card:ℝ)+(R:ℝ)*(15*(N:ℝ)^188)≤16*(N:ℝ)^252 := by
    dsimp only [R]
    push_cast
    nlinarith only [exp,ic']
  rw [qc] at hc
  have cap : (B.card:ℝ)*(P.card:ℝ)*(P.card:ℝ)*((I.card:ℝ)+(R:ℝ)*(15*(N:ℝ)^188)) ≤ 32*(N:ℝ)^968 := by
    have nP : 0 ≤ (P.card : ℝ) := Nat.cast_nonneg _
    have nI : 0 ≤ (I.card : ℝ) := Nat.cast_nonneg _
    have nR : 0 ≤ (R : ℝ) := Nat.cast_nonneg _
    have nN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
    have n15 : 0 ≤ (15 : ℝ) * (N : ℝ) ^ 188 := mul_nonneg (by norm_num) (pow_nonneg nN _)
    have nTail : 0 ≤ (I.card : ℝ) + (R : ℝ) * ((15 : ℝ) * (N : ℝ) ^ 188) :=
      add_nonneg nI (mul_nonneg nR n15)
    have n2 : 0 ≤ (2 : ℝ) * (N : ℝ) ^ 212 := mul_nonneg (by norm_num) (pow_nonneg nN _)
    have n252 : 0 ≤ (N : ℝ) ^ 252 := pow_nonneg nN _
    have s1 : (B.card : ℝ) * (P.card : ℝ) ≤ (2 * (N : ℝ) ^ 212) * (P.card : ℝ) :=
      mul_le_mul_of_nonneg_right bc nP
    have s2 : (B.card : ℝ) * (P.card : ℝ) * (P.card : ℝ) ≤
        (2 * (N : ℝ) ^ 212) * (P.card : ℝ) * (P.card : ℝ) :=
      mul_le_mul_of_nonneg_right s1 nP
    have s3 : (2 * (N : ℝ) ^ 212) * (P.card : ℝ) ≤ (2 * (N : ℝ) ^ 212) * (N : ℝ) ^ 252 :=
      mul_le_mul_of_nonneg_left pc n2
    have s4 : (2 * (N : ℝ) ^ 212) * (P.card : ℝ) * (P.card : ℝ) ≤
        (2 * (N : ℝ) ^ 212) * (N : ℝ) ^ 252 * (P.card : ℝ) :=
      mul_le_mul_of_nonneg_right s3 nP
    have s5 : (2 * (N : ℝ) ^ 212) * (N : ℝ) ^ 252 * (P.card : ℝ) ≤
        (2 * (N : ℝ) ^ 212) * (N : ℝ) ^ 252 * (N : ℝ) ^ 252 :=
      mul_le_mul_of_nonneg_left pc (mul_nonneg n2 n252)
    have s6 := s2.trans (s4.trans s5)
    have s7 : (B.card : ℝ) * (P.card : ℝ) * (P.card : ℝ) *
        ((I.card : ℝ) + (R : ℝ) * (15 * (N : ℝ) ^ 188)) ≤
        (2 * (N : ℝ) ^ 212) * (N : ℝ) ^ 252 * (N : ℝ) ^ 252 *
          ((I.card : ℝ) + (R : ℝ) * (15 * (N : ℝ) ^ 188)) :=
      mul_le_mul_of_nonneg_right s6 nTail
    have s8 : (2 * (N : ℝ) ^ 212) * (N : ℝ) ^ 252 * (N : ℝ) ^ 252 *
        ((I.card : ℝ) + (R : ℝ) * (15 * (N : ℝ) ^ 188)) ≤
        (2 * (N : ℝ) ^ 212) * (N : ℝ) ^ 252 * (N : ℝ) ^ 252 * (16 * (N : ℝ) ^ 252) :=
      mul_le_mul_of_nonneg_left rb (mul_nonneg (mul_nonneg n2 n252) n252)
    refine (s7.trans s8).trans ?_
    exact le_of_eq (by ring)
  have powb := hc.trans cap
  change ‖∑ w∈P ×ˢ P, f w.1 w.2‖ ≤ _
  rw [grouping]
  have sq : (6*(N:ℝ)^484)^2 = 36*(N:ℝ)^968 := by ring
  have hpow : 0 ≤ (N : ℝ) ^ 968 := by positivity
  have h6 : 0 ≤ 6 * (N : ℝ) ^ 484 := by positivity
  nlinarith only [powb, sq, hpow, h6]



private lemma real_phase (z:ℝ) : (e z).re = Real.cos (2*π*z) := by
  rw [e_eq, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

private theorem smooth_prime_floor :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ t : ℕ, N^1000 ≤ t → t ≤ N^1001 →
    let P := (Ioc (N^251) (N^252)).filter Nat.Prime
    |∑ w ∈ P ×ˢ P, ((((t/(w.1*w.2):ℕ):ℝ)-(t:ℝ)/((w.1*w.2:ℕ):ℝ))+1/2)| ≤
      ε*(N:ℝ)^499 := by
  intro ε ep
  obtain ⟨C,cp,sm⟩ := smooth_discrepancy
  obtain ⟨z,hz⟩ := exists_nat_gt ((1+7*C)/ε)
  filter_upwards [eventually_ge_atTop (max 2 z)] with N hN
  intro t lt ut P
  have ge : 2≤N := (le_max_left _ _).trans hN
  let X : ℝ := N
  have xp : 1<X := by dsimp [X]; exact_mod_cast ge
  have xp0 := zero_lt_one.trans xp
  have small : 1+7*C≤ε*X := by
    have zn : (z:ℝ)≤X := by
      dsimp [X]
      exact_mod_cast (le_max_right 2 z).trans hN
    nlinarith only [(div_lt_iff₀ ep).mp hz,mul_le_mul_of_nonneg_left zn ep.le]
  let S := P ×ˢ P
  let x (w:ℕ×ℕ) := (t:ℝ)/((w.1*w.2:ℕ):ℝ)
  have sc : (S.card:ℝ)≤X^504 := by
    have pc : P.card≤N^252 := (card_le_card (filter_subset _ _)).trans (by simp)
    have pcr : (P.card:ℝ)≤X^252 := by
      dsimp [X]
      exact_mod_cast pc
    dsimp only [S]; rw [card_product,Nat.cast_mul]
    calc _ ≤ X^252*X^252 := by gcongr
         _ = _ := by ring
  have freq (u:ℝ) (h:ℕ) (hh:0<h) (hi:h≤N^20) :
      |∑ w∈S, Real.cos (2*π*h*(x w+u))| ≤ 6*X^484 := by
    let g (w:ℕ×ℕ) := e ((h:ℝ)*t/((w.1:ℝ)*w.2))
    have fc : ∑ w∈S, Real.cos (2*π*h*(x w+u)) = (e (h*u)*∑ w∈S,g w).re := by
      rw [mul_sum,Complex.re_sum]
      apply sum_congr rfl
      intro w _
      dsimp only [g]; rw [←e_add,real_phase]
      congr 1
      dsimp [x]; push_cast; ring
    rw [fc]
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul,norm_e,one_mul]
    exact pair_phase N h t ge hh hi lt ut
  have hs := sm S x (1/X^6) (6*X^484) (N^20) (by positivity)
    (by rw [div_lt_one (by positivity)]; exact one_lt_pow₀ xp (by decide))
    (by positivity) (by positivity) freq
  have fe (w:ℕ×ℕ) : (((t/(w.1*w.2):ℕ):ℝ)-(t:ℝ)/((w.1*w.2:ℕ):ℝ))+1/2 = 1/2-Int.fract (x w) := by
    set n : ℕ := w.1 * w.2
    dsimp only [x]
    rw [Int.fract]
    by_cases hn : n = 0
    · have hprod : w.1 * w.2 = 0 := hn
      rw [hn, hprod]
      simp only [Nat.div_zero, Nat.cast_zero, div_zero, Int.floor_zero, Int.cast_zero,
        sub_self, sub_zero, zero_add]
    · have hpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnn : 0 ≤ (t : ℝ) / (n : ℝ) := div_nonneg (Nat.cast_nonneg _) hpos.le
      have hfl : ⌊(t : ℝ) / (n : ℝ)⌋ = ((t / n : ℕ) : ℤ) := by
        rw [← Int.natCast_floor_eq_floor hnn, Nat.floor_div_eq_div]
      rw [hfl, Int.cast_natCast]
      ring
  have hsum : ∑ w ∈ S, ((((t / (w.1 * w.2) : ℕ) : ℝ) - (t : ℝ) / ((w.1 * w.2 : ℕ) : ℝ)) + 1 / 2)
      = ∑ w ∈ S, (1 / 2 - Int.fract (x w)) := by
    refine sum_congr rfl ?_
    intro w _
    exact fe w
  rw [hsum]
  apply hs.trans
  change _ ≤ ε*X^499
  have xz : X≠0 := xp0.ne'
  have cap : (S.card:ℝ)*(1/X^6)/2 + C*(6*X^484+S.card/((N^20:ℕ):ℝ))/(1/X^6) ≤
      X^498/2+C*(7*X^490) := by
    rw [Nat.cast_pow]; change _+ C*(6*X^484+(S.card:ℝ)/X^20)/(1/X^6) ≤ _
    calc _ ≤ X^504*(1/X^6)/2+C*(6*X^484+X^504/X^20)/(1/X^6) := by gcongr
         _ = _ := by field_simp; ring
  refine cap.trans ?_
  calc X^498/2+C*(7*X^490) ≤ (1+7*C)*X^498 := by
         have := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ xp.le (show 490≤498 by decide)) cp.le
         nlinarith only [this,pow_nonneg xp0.le 498]
       _ ≤ (ε*X)*X^498 := mul_le_mul_of_nonneg_right small (pow_nonneg xp0.le _)
       _ = _ := by ring


theorem OMA.solution : OMA.R_Erdos375_erdos_375_variants_bounded_gap_R1_H1_R1.H2 := smooth_prime_floor
