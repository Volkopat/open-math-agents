import OMAStatements.S_mo_434426
import Mathlib

-- Problem: mo-434426, the double series of 1 / (s_m (s_m + s_n)) with s_m = a^m / m, a > 1,
-- equals a^2 / (2 (a - 1)^4).
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- With T(m, n) = 1 / (s_m (s_m + s_n)) one has T(m, n) + T(n, m) = (1 / s_m) (1 / s_n), and all
-- terms are positive, so twice the double sum is the square of the sum of m / a^m, which is
-- a / (a - 1)^2.

open OMA.S_mo_434426 in
theorem OMA.solution : type_of% @OMA.S_mo_434426.main := by
  intro a ha
  have ha0 : 0 < a := by linarith
  have ha1 : a - 1 ≠ 0 := by
    intro h
    linarith
  have hr : ‖a⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha0)]
    exact inv_lt_one_of_one_lt₀ ha
  have hu0 := hasSum_coe_mul_geometric_of_norm_lt_one hr
  have hu1 : HasSum (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * a⁻¹ ^ (n + 1))
      (a⁻¹ / (1 - a⁻¹) ^ 2) := by
    have h := (hasSum_nat_add_iff' 1).mpr hu0
    simpa using h
  have hs : ∀ m : ℕ, scale a m = a ^ (m + 1) / ((m + 1 : ℕ) : ℝ) := fun m => rfl
  have hspos : ∀ m : ℕ, 0 < scale a m := by
    intro m
    rw [hs]
    positivity
  have hu : ∀ m : ℕ, 1 / scale a m = ((m + 1 : ℕ) : ℝ) * a⁻¹ ^ (m + 1) := by
    intro m
    rw [hs, one_div, inv_div, div_eq_mul_inv, ← inv_pow]
  have hU : HasSum (fun m : ℕ => 1 / scale a m) (a⁻¹ / (1 - a⁻¹) ^ 2) := by
    simp only [hu]
    exact hu1
  have hTnonneg : ∀ m n : ℕ, 0 ≤ term a m n := by
    intro m n
    unfold term
    have h1 := hspos m
    have h2 := hspos n
    positivity
  have hTle : ∀ m n : ℕ, term a m n ≤ 1 / scale a m * (1 / scale a n) := by
    intro m n
    unfold term
    have h1 := hspos m
    have h2 := hspos n
    rw [div_mul_div_comm, one_mul]
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith
  have hsym : ∀ m n : ℕ, term a m n + term a n m = 1 / scale a m * (1 / scale a n) := by
    intro m n
    unfold term
    have h1 := (hspos m).ne'
    have h2 := (hspos n).ne'
    have h3 : scale a m + scale a n ≠ 0 := (add_pos (hspos m) (hspos n)).ne'
    have h4 : scale a n + scale a m ≠ 0 := (add_pos (hspos n) (hspos m)).ne'
    field_simp
    ring
  have hprodsum : Summable (fun p : ℕ × ℕ => 1 / scale a p.1 * (1 / scale a p.2)) :=
    Summable.mul_of_nonneg hU.summable hU.summable
      (fun m => (one_div_pos.mpr (hspos m)).le) (fun m => (one_div_pos.mpr (hspos m)).le)
  have hTsum : Summable (fun p : ℕ × ℕ => term a p.1 p.2) :=
    Summable.of_nonneg_of_le (fun p => hTnonneg p.1 p.2) (fun p => hTle p.1 p.2) hprodsum
  have hprodsum' : Summable (fun p : ℕ × ℕ => 1 / scale a p.2 * (1 / scale a p.1)) :=
    hprodsum.congr (fun p => mul_comm _ _)
  have hTsum' : Summable (fun p : ℕ × ℕ => term a p.2 p.1) :=
    Summable.of_nonneg_of_le (fun p => hTnonneg p.2 p.1) (fun p => hTle p.2 p.1) hprodsum'
  have hA : ∑' p : ℕ × ℕ, term a p.1 p.2 = ∑' m : ℕ, ∑' n : ℕ, term a m n :=
    hTsum.tsum_prod' (fun m => hTsum.prod_factor m)
  have hswap : ∑' p : ℕ × ℕ, term a p.2 p.1 = ∑' p : ℕ × ℕ, term a p.1 p.2 := by
    have h := (Equiv.prodComm ℕ ℕ).tsum_eq (fun p : ℕ × ℕ => term a p.1 p.2)
    simpa using h
  have hadd : ∑' p : ℕ × ℕ, (term a p.1 p.2 + term a p.2 p.1) =
      ∑' p : ℕ × ℕ, term a p.1 p.2 + ∑' p : ℕ × ℕ, term a p.2 p.1 :=
    hTsum.tsum_add hTsum'
  have hcongr : ∑' p : ℕ × ℕ, (term a p.1 p.2 + term a p.2 p.1) =
      ∑' p : ℕ × ℕ, 1 / scale a p.1 * (1 / scale a p.2) :=
    tsum_congr (fun p => hsym p.1 p.2)
  have hmul : (∑' m : ℕ, 1 / scale a m) * (∑' n : ℕ, 1 / scale a n) =
      ∑' p : ℕ × ℕ, 1 / scale a p.1 * (1 / scale a p.2) :=
    hU.summable.tsum_mul_tsum hU.summable hprodsum
  rw [hU.tsum_eq] at hmul
  have hA2 : ∑' p : ℕ × ℕ, term a p.1 p.2 =
      a⁻¹ / (1 - a⁻¹) ^ 2 * (a⁻¹ / (1 - a⁻¹) ^ 2) / 2 := by
    linarith
  have hinv : 1 - a⁻¹ = (a - 1) / a := by
    field_simp
  rw [← hA, hA2, hinv]
  field_simp
