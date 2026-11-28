import OMAStatements.S_wp_exponent_pair_conjecture
import Mathlib

/-!
# Exponent pair conjecture: the formalized statement is false

In the formal statement the constant `C` is fixed before `s`, `T`, `N`, and the derivative
condition only forces `f' ~ s T x^(-s)`. Take `eps = 1/2`, `sigma = 2`, `T = 1`: the bound is `C`.
For a large natural `m` put `s = m + 1` and `f x = -((m+1)/m) x^(-m)`. Its `(r+1)`-st derivative is
`(-1)^r s (s (s+1) ... (s+r-1)) x^(-s-r)`, which differs from the required main term by the factor
`s/(s+r)`, within `delta` once `R <= delta m`. But `|f| <= 2/N` on `[N, 2N]`, so every term
`e (f n)` has real part at least `1/2`, and the sum of `N + 1` terms has norm at least `(N+1)/2 > C`.
-/

namespace OMA.ExponentPairDisproof

open Finset

theorem prod_aux (m : ℕ) (r : ℕ) :
    ∏ i ∈ Finset.range (r + 1), (((-(m : ℤ) : ℤ) : ℝ) - i) =
      (-1) ^ (r + 1) * m * ∏ i ∈ Finset.range r, ((m : ℝ) + 1 + i) := by
  induction r with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ, ih, Finset.prod_range_succ (n := k)]
    push_cast
    ring

theorem key_deriv (m : ℕ) (hm : 1 ≤ m) (x : ℝ) (hx : 0 < x) (r : ℕ) :
    iteratedDeriv (r + 1) (fun y : ℝ => (-(((m : ℝ) + 1) / m)) * y ^ (-(m : ℤ))) x =
      (-1) ^ r * ((m : ℝ) + 1) * (∏ i ∈ Finset.range r, ((m : ℝ) + 1 + i)) *
        x ^ (-((m : ℝ) + 1) - (r : ℝ)) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_eq_iterate, iter_deriv_zpow, prod_aux]
  have hexp : (-((m : ℝ) + 1) - (r : ℝ)) = ((-(m : ℤ) - ((r + 1 : ℕ) : ℤ) : ℤ) : ℝ) := by
    push_cast; ring
  rw [hexp, Real.rpow_intCast]
  field_simp
  ring

theorem disproof_aux :
    ¬ (∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      OMA.S_wp_exponent_pair_conjecture.IsExponentPair ε (1 / 2 + ε)) := by
  intro h
  obtain ⟨-, -, -, -, H⟩ := h (1 / 2) (by norm_num) le_rfl
  obtain ⟨δ, hδ, R, C, hC, H⟩ := H 2 (by norm_num)
  set m : ℕ := ⌈(R : ℝ) / δ⌉₊ + 1 with hmdef
  set N : ℕ := ⌈2 * C⌉₊ + 13 with hNdef
  have hm1 : 1 ≤ m := by omega
  have hmR : (R : ℝ) ≤ δ * m := by
    have h1 : (R : ℝ) / δ ≤ m := by
      have := Nat.le_ceil ((R : ℝ) / δ)
      have h2 : ((⌈(R : ℝ) / δ⌉₊ : ℕ) : ℝ) ≤ (m : ℝ) := by
        rw [hmdef]; push_cast; linarith
      linarith
    rw [div_le_iff₀ hδ] at h1
    linarith
  have hN13 : (13 : ℝ) ≤ N := by rw [hNdef]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈2 * C⌉₊]
  have hNC : 2 * C ≤ N := by
    have := Nat.le_ceil (2 * C)
    rw [hNdef]; push_cast; linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  set c : ℝ := -(((m : ℝ) + 1) / m) with hc
  set f : ℝ → ℝ := fun y : ℝ => c * y ^ (-(m : ℤ)) with hf
  have hadm : OMA.S_wp_exponent_pair_conjecture.Admissible R ((m : ℝ) + 1) 1 δ N f := by
    refine ⟨?_, ?_⟩
    · have hcd : ContDiffOn ℝ R (fun y : ℝ => c * (y ^ m)⁻¹) (Set.Icc (N : ℝ) (2 * N)) := by
        apply ContDiffOn.mul contDiffOn_const
        apply ContDiffOn.inv (contDiffOn_id.pow m)
        intro y hy
        have : (0 : ℝ) < y := by linarith [hy.1]
        positivity
      refine hcd.congr ?_
      intro y _
      simp [hf, zpow_neg]
    · intro x hx r hr
      have hx0 : (0 : ℝ) < x := by linarith [hx.1]
      rw [hf, hc, key_deriv m hm1 x hx0 r]
      unfold OMA.S_wp_exponent_pair_conjecture.rising
      rw [Finset.prod_range_succ]
      set P : ℝ := ∏ i ∈ Finset.range r, ((m : ℝ) + 1 + i) with hP
      set y : ℝ := x ^ (-((m : ℝ) + 1) - (r : ℝ)) with hy
      have hP0 : 0 ≤ P := Finset.prod_nonneg (fun i _ => by positivity)
      have hy0 : 0 ≤ y := Real.rpow_nonneg hx0.le _
      have heq : (-1 : ℝ) ^ r * ((m : ℝ) + 1) * P * y -
          (-1 : ℝ) ^ r * (P * ((m : ℝ) + 1 + r)) * 1 * y = (-1 : ℝ) ^ r * (-(P * y * r)) := by
        ring
      rw [heq, norm_mul, norm_pow, norm_neg, norm_neg, norm_one, one_pow, one_mul,
        Real.norm_of_nonneg (by positivity)]
      have hrR : (r : ℝ) ≤ R := by exact_mod_cast hr.le
      have hr1 : (r : ℝ) ≤ δ * ((m : ℝ) + 1 + r) := by nlinarith
      calc P * y * r = (P * y) * r := by ring
        _ ≤ (P * y) * (δ * ((m : ℝ) + 1 + r)) :=
          mul_le_mul_of_nonneg_left hr1 (mul_nonneg hP0 hy0)
        _ = δ * (P * ((m : ℝ) + 1 + r)) * 1 * y := by ring
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hb := H N 1 ((m : ℝ) + 1) (N : ℤ) (2 * (N : ℤ)) f hN1 le_rfl (by positivity)
    (by simp) (by push_cast; exact le_rfl) (by omega) hadm
  have hrhs : C * (1 / (N : ℝ) ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) * (N : ℝ) ^ ((1 : ℝ) / 2 + 1 / 2) = C := by
    have h2 : ((1 : ℝ) / 2 + 1 / 2) = 1 := by norm_num
    rw [h2, Real.rpow_one, Real.rpow_two, ← Real.sqrt_eq_rpow]
    have h3 : (1 / (N : ℝ) ^ 2) = ((N : ℝ)⁻¹) ^ 2 := by field_simp
    rw [h3, Real.sqrt_sq (by positivity)]
    field_simp
  rw [hrhs] at hb
  have hterm : ∀ n ∈ Finset.Icc (N : ℤ) (2 * (N : ℤ)),
      (1 : ℝ) / 2 ≤ (OMA.S_wp_exponent_pair_conjecture.e (f n)).re := by
    intro n hn
    have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by linarith
    have hpow : (N : ℝ) ≤ (n : ℝ) ^ m := le_trans hnN (le_self_pow₀ hn1 (by omega))
    have hinv : ((n : ℝ) ^ m)⁻¹ ≤ 1 / 13 := by
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    have hinv0 : 0 ≤ ((n : ℝ) ^ m)⁻¹ := by positivity
    have hcabs : |c| ≤ 2 := by
      rw [hc, abs_neg, abs_of_nonneg (by positivity), div_le_iff₀ hm0]
      linarith
    have hfn : |f n| ≤ 2 / 13 := by
      have : f n = c * ((n : ℝ) ^ m)⁻¹ := by simp [hf, zpow_neg]
      rw [this, abs_mul, abs_of_nonneg hinv0]
      calc |c| * ((n : ℝ) ^ m)⁻¹ ≤ 2 * (1 / 13) :=
            mul_le_mul hcabs hinv hinv0 (by norm_num)
        _ = 2 / 13 := by norm_num
    have hre : (OMA.S_wp_exponent_pair_conjecture.e (f n)).re = Real.cos (2 * Real.pi * f n) := by
      unfold OMA.S_wp_exponent_pair_conjecture.e
      rw [← Complex.exp_ofReal_mul_I_re]
      congr 2
      push_cast
      ring
    rw [hre]
    have hpi : Real.pi ≤ 3.15 := Real.pi_lt_d2.le
    have hpi0 : 0 < Real.pi := Real.pi_pos
    have hy : |2 * Real.pi * f n| ≤ 1 := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      have := abs_nonneg (f n)
      nlinarith
    have hy2 : (2 * Real.pi * f n) ^ 2 ≤ 1 := by
      rw [sq_le_one_iff_abs_le_one]; exact hy
    have := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * f n)
    linarith
  have hcard : ((Finset.Icc (N : ℤ) (2 * (N : ℤ))).card : ℝ) = (N : ℝ) + 1 := by
    rw [Int.card_Icc]
    have : (2 * (N : ℤ) + 1 - (N : ℤ)).toNat = N + 1 := by omega
    rw [this]; push_cast; ring
  have hsum : ((N : ℝ) + 1) * (1 / 2) ≤
      (∑ n ∈ Finset.Icc (N : ℤ) (2 * (N : ℤ)),
        OMA.S_wp_exponent_pair_conjecture.e (f n)).re := by
    rw [Complex.re_sum, ← hcard, ← nsmul_eq_mul]
    exact Finset.card_nsmul_le_sum _ _ _ hterm
  have hnorm := Complex.re_le_norm (∑ n ∈ Finset.Icc (N : ℤ) (2 * (N : ℤ)),
        OMA.S_wp_exponent_pair_conjecture.e (f n))
  have hb' : ‖∑ n ∈ Finset.Icc (N : ℤ) (2 * (N : ℤ)),
        OMA.S_wp_exponent_pair_conjecture.e (f n)‖ ≤ C := by
    convert hb using 3
  linarith

end OMA.ExponentPairDisproof

theorem OMA.disproof : ¬ (type_of% @OMA.S_wp_exponent_pair_conjecture.main) :=
  OMA.ExponentPairDisproof.disproof_aux
