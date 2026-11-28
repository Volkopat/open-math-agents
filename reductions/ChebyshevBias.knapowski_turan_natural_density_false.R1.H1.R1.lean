import OMAReductions.R_ChebyshevBias_knapowski_turan_natural_density_false_R1

/-!
Reduction of `OMA.R_ChebyshevBias_knapowski_turan_natural_density_false_R1.H1` (Cramér 1922 /
Rubinstein-Sarnak 1994 / Kaczorowski 1995 `L^2` mean-square bound under GRH for `L(s, chi_4)`).

Inside this file we prove completely from scratch in Lean 4:
1. Exact character-sum identity expressing `pi(j; 4, 1) - pi(j; 4, 3)` via `ZMod.chi_4`.
2. Discrete Abel summation expressing `pi(j; 4, 1) - pi(j; 4, 3)` in terms of the weighted prime
   sum `theta_4(k) = sum_{p <= k, prime} chi_4(p) log p`.
3. Cauchy-Schwarz, exact telescoping of `sum (1/log k - 1/log(k+1)) <= 2`, and an explicit
   antiderivative `h(x) = ((log x)^2 + 2 log x + 2) / x` with mean-value theorem bounding the
   tail `sum_{j=k+1}^N (log j)^2 / j^2 <= 52 (log k)^2 / k`, yielding the unconditional pure
   constant-factor reduction
     `sum_{j=2}^N (1/j) ((log j / sqrt j) (pi(j;4,1) - pi(j;4,3)))^2 <= 210 sum_{j=2}^N (1/j) (theta_4(j) / sqrt j)^2`.
4. Chebyshev prime-power comparison `|psi_4(j) - theta_4(j)| <= C_0 sqrt j` (via Mathlib's
   `Chebyshev.psi_sub_theta_le_mul_sqrt`) and the harmonic bound `sum_{j=2}^N 1/j <= log N`,
   reducing further to `sum_{j=2}^N (1/j) (psi_4(j) / sqrt j)^2`.
5. Discrete-to-continuous step-function integral comparison at `sigma = 1/2 + 1 / log(N + 1)`
   showing `sum_{j=2}^N psi_4(j)^2 / j^2 <= (9 e^2 / 4) * integral_1^{N+1} psi_4(floor x)^2 x^{-(2 sigma + 1)} dx`.

The reduction isolates two decoupled, unconditionally true analytic number theory theorems:
- `H1`: Mellin-Plancherel `L^2` bound for `psi_4(floor x)` on vertical lines `Re(s) = sigma > 1/2`
  under GRH for `L(s, chi_4)` (Cramér 1922).
- `H2`: Vertical-line `L^2` mean-square bound for `L'(s, chi_4) / (s L(s, chi_4))` on
  `1/2 < sigma <= 1` under GRH (Hadamard partial fraction + Riemann-von Mangoldt zero density).
-/

namespace OMA.R_ChebyshevBias_knapowski_turan_natural_density_false_R1_H1_R1

open MeasureTheory intervalIntegral

/-- Mellin-Plancherel `L^2` inequality for the Chebyshev character sum `psi_4(floor x)` on
vertical lines `Re(s) = sigma > 1/2` under GRH for `L(s, chi_4)` (Cramér 1922). -/
def H1 : Prop :=
  (∀ s : ℂ, 0 < s.re → s.re < 1 →
      DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) s = 0 →
      s.re = 1 / 2) →
    ∀ (σ X : ℝ), (1 : ℝ) / 2 < σ → 1 ≤ X →
      (∫ x in (1 : ℝ)..X,
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ArithmeticFunction.vonMangoldt n * (ZMod.χ₄ (n : ZMod 4) : ℝ)) ^ 2 *
          x ^ (-(2 * σ + 1))) ≤
      (1 / (2 * Real.pi)) *
        ∫ t : ℝ,
          ‖deriv (DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)))
              ((σ : ℂ) + (t : ℂ) * Complex.I) /
            (((σ : ℂ) + (t : ℂ) * Complex.I) *
              DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
                ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2

/-- GRH vertical-line `L^2` mean-square bound for `L'(s, chi_4) / (s L(s, chi_4))` on
`1/2 < sigma <= 1` (Hadamard partial fraction + Riemann-von Mangoldt zero density). -/
def H2 : Prop :=
  (∀ s : ℂ, 0 < s.re → s.re < 1 →
      DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) s = 0 →
      s.re = 1 / 2) →
    ∃ C : ℝ, 0 < C ∧ ∀ σ : ℝ, (1 : ℝ) / 2 < σ → σ ≤ 1 →
      MeasureTheory.Integrable (fun t : ℝ =>
        ‖deriv (DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)))
            ((σ : ℂ) + (t : ℂ) * Complex.I) /
          (((σ : ℂ) + (t : ℂ) * Complex.I) *
            DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
              ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2) ∧
      (∫ t : ℝ,
        ‖deriv (DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)))
            ((σ : ℂ) + (t : ℂ) * Complex.I) /
          (((σ : ℂ) + (t : ℂ) * Complex.I) *
            DirichletCharacter.LFunction (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))
              ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ^ 2) ≤
        C / (σ - 1 / 2)

/- === Section 1: Character Evaluation and Prime-Counting Identity === -/

lemma chi4_eq_of_mod_zero {n : ℕ} (h : n % 4 = 0) : (ZMod.χ₄ (n : ZMod 4) : ℝ) = 0 := by
  have hcast : (n : ZMod 4) = 0 := by
    rw [← ZMod.natCast_mod n 4, h]
    rfl
  rw [hcast]
  have hz : ZMod.χ₄ 0 = 0 := by decide
  rw [hz]
  norm_num

lemma chi4_eq_of_mod_one {n : ℕ} (h : n % 4 = 1) : (ZMod.χ₄ (n : ZMod 4) : ℝ) = 1 := by
  have hcast : (n : ZMod 4) = 1 := by
    rw [← ZMod.natCast_mod n 4, h]
    rfl
  rw [hcast]
  have hz : ZMod.χ₄ 1 = 1 := by decide
  rw [hz]
  norm_num

lemma chi4_eq_of_mod_two {n : ℕ} (h : n % 4 = 2) : (ZMod.χ₄ (n : ZMod 4) : ℝ) = 0 := by
  have hcast : (n : ZMod 4) = 2 := by
    rw [← ZMod.natCast_mod n 4, h]
    rfl
  rw [hcast]
  have hz : ZMod.χ₄ 2 = 0 := by decide
  rw [hz]
  norm_num

lemma chi4_eq_of_mod_three {n : ℕ} (h : n % 4 = 3) : (ZMod.χ₄ (n : ZMod 4) : ℝ) = -1 := by
  have hcast : (n : ZMod 4) = 3 := by
    rw [← ZMod.natCast_mod n 4, h]
    rfl
  rw [hcast]
  have hz : ZMod.χ₄ 3 = -1 := by decide
  rw [hz]
  norm_num

lemma abs_chi4_le_one (n : ℕ) : |(ZMod.χ₄ (n : ZMod 4) : ℝ)| ≤ 1 := by
  have hmod : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hmod with h | h | h | h
  · rw [chi4_eq_of_mod_zero h]; norm_num
  · rw [chi4_eq_of_mod_one h]; norm_num
  · rw [chi4_eq_of_mod_two h]; norm_num
  · rw [chi4_eq_of_mod_three h]; norm_num

lemma primeCountingMod_diff_eq_sum_chi4 (j : ℕ) :
    (j.primeCountingMod 4 1 : ℝ) - (j.primeCountingMod 4 3 : ℝ) =
      ∑ p ∈ Finset.Icc 1 j, if p.Prime then (ZMod.χ₄ (p : ZMod 4) : ℝ) else 0 := by
  have h1 : (j.primeCountingMod 4 1 : ℝ) =
      ∑ p ∈ Finset.Icc 1 j, if p.Prime ∧ p % 4 = 1 then (1 : ℝ) else 0 := by
    have hc := Nat.primeCountingMod_natCast_eq_card_filter_mod j 4 1
    simp only [Nat.cast_one] at hc
    rw [hc]
    simp only [Finset.sum_boole]
  have h3 : (j.primeCountingMod 4 3 : ℝ) =
      ∑ p ∈ Finset.Icc 1 j, if p.Prime ∧ p % 4 = 3 then (1 : ℝ) else 0 := by
    have hc := Nat.primeCountingMod_natCast_eq_card_filter_mod j 4 3
    simp only [Nat.cast_ofNat] at hc
    rw [hc]
    simp only [Finset.sum_boole]
  rw [h1, h3, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases hp : p.Prime
  · have hmod : p % 4 = 0 ∨ p % 4 = 1 ∨ p % 4 = 2 ∨ p % 4 = 3 := by omega
    rcases hmod with hm | hm | hm | hm
    · rw [chi4_eq_of_mod_zero hm]; simp [hp, hm]
    · rw [chi4_eq_of_mod_one hm]; simp [hp, hm]
    · rw [chi4_eq_of_mod_two hm]; simp [hp, hm]
    · rw [chi4_eq_of_mod_three hm]; simp [hp, hm]
  · simp [hp]

/- === Section 2: Discrete Abel Summation, Cauchy-Schwarz, and Tail Sum === -/

lemma pi4_eq_abel_sum (j : ℕ) (hj : 2 ≤ j) :
    (j.primeCountingMod 4 1 : ℝ) - (j.primeCountingMod 4 3 : ℝ) =
      (∑ p ∈ Finset.Icc 1 j, if p.Prime then (ZMod.χ₄ (p : ZMod 4) : ℝ) * Real.log p else 0) /
        Real.log j +
      ∑ k ∈ Finset.Icc 2 (j - 1),
        (∑ p ∈ Finset.Icc 1 k, if p.Prime then (ZMod.χ₄ (p : ZMod 4) : ℝ) * Real.log p else 0) *
          (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) := by
  rw [primeCountingMod_diff_eq_sum_chi4]
  induction j, hj using Nat.le_induction with
  | base =>
    have hIcc : Finset.Icc 1 2 = {1, 2} := by decide
    have hEmpty : Finset.Icc 2 (2 - 1) = ∅ := by decide
    rw [hIcc, hEmpty, Finset.sum_empty, add_zero]
    simp only [Finset.sum_pair (by decide : (1 : ℕ) ≠ 2), Nat.not_prime_one, ↓reduceIte,
      Nat.prime_two, chi4_eq_of_mod_two (by decide : 2 % 4 = 2), zero_mul, zero_add, zero_div]
  | succ m hm ih =>
    have hm1 : 1 ≤ m + 1 := by omega
    have hlog_pos : 0 < Real.log ((m + 1 : ℕ) : ℝ) := by
      refine Real.log_pos ?_
      exact_mod_cast (by omega : 1 < m + 1)
    have hlog_ne : Real.log ((m + 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hlog_pos
    have hL :
        (∑ p ∈ Finset.Icc 1 (m + 1), if p.Prime then (ZMod.χ₄ (p : ZMod 4) : ℝ) else 0) =
          (∑ p ∈ Finset.Icc 1 m, if p.Prime then (ZMod.χ₄ (p : ZMod 4) : ℝ) else 0) +
            (if (m + 1).Prime then (ZMod.χ₄ ((m + 1 : ℕ) : ZMod 4) : ℝ) else 0) := by
      rw [Finset.sum_Icc_succ_top hm1]
    have hT :
        (∑ p ∈ Finset.Icc 1 (m + 1),
            if p.Prime then (ZMod.χ₄ (p : ZMod 4) : ℝ) * Real.log p else 0) =
          (∑ p ∈ Finset.Icc 1 m,
            if p.Prime then (ZMod.χ₄ (p : ZMod 4) : ℝ) * Real.log p else 0) +
          (if (m + 1).Prime then
            (ZMod.χ₄ ((m + 1 : ℕ) : ZMod 4) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ) else 0) := by
      rw [Finset.sum_Icc_succ_top hm1]
    have hS :
        (∑ k ∈ Finset.Icc 2 (m + 1 - 1),
            (∑ p ∈ Finset.Icc 1 k, if p.Prime then (ZMod.χ₄ (p : ZMod 4) : ℝ) * Real.log p else 0) *
              (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ))) =
          (∑ k ∈ Finset.Icc 2 (m - 1),
            (∑ p ∈ Finset.Icc 1 k, if p.Prime then (ZMod.χ₄ (p : ZMod 4) : ℝ) * Real.log p else 0) *
              (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ))) +
          (∑ p ∈ Finset.Icc 1 m, if p.Prime then (ZMod.χ₄ (p : ZMod 4) : ℝ) * Real.log p else 0) *
            (1 / Real.log m - 1 / Real.log ((m + 1 : ℕ) : ℝ)) := by
      have heq : m + 1 - 1 = (m - 1) + 1 := by omega
      rw [heq, Finset.sum_Icc_succ_top (by omega : 2 ≤ m - 1 + 1)]
      have hm_eq : m - 1 + 1 = m := by omega
      rw [hm_eq]
    have hterm :
        (if (m + 1).Prime then
          (ZMod.χ₄ ((m + 1 : ℕ) : ZMod 4) : ℝ) * Real.log ((m + 1 : ℕ) : ℝ) else 0) /
          Real.log ((m + 1 : ℕ) : ℝ) =
        if (m + 1).Prime then (ZMod.χ₄ ((m + 1 : ℕ) : ZMod 4) : ℝ) else 0 := by
      by_cases hp : (m + 1).Prime
      · simp only [hp, ↓reduceIte, mul_div_cancel_right₀ _ hlog_ne]
      · simp only [hp, ↓reduceIte, zero_div]
    rw [hL, ih, hT, hS, add_div, hterm]
    ring

lemma half_lt_log_two : (1 : ℝ) / 2 < Real.log 2 := by
  have hexp : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hlog : Real.log (Real.exp 1) < Real.log 4 := Real.log_lt_log (Real.exp_pos 1) hexp
  rw [Real.log_exp] at hlog
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    have h22 : (4 : ℝ) = 2 ^ (2 : ℕ) := by norm_num
    rw [h22, Real.log_pow]
    norm_num
  linarith

lemma inv_log_sub_bounds (k : ℕ) (hk : 2 ≤ k) :
    0 ≤ 1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ) ∧
    1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ) ≤ 1 / ((k : ℝ) * (Real.log k) ^ 2) := by
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hk1_pos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k + 1)
  have hlogk_pos : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hlogk_le : Real.log k ≤ Real.log ((k + 1 : ℕ) : ℝ) :=
    Real.log_le_log hk_pos (by exact_mod_cast (by omega : k ≤ k + 1))
  have hlogk1_pos : 0 < Real.log ((k + 1 : ℕ) : ℝ) := lt_of_lt_of_le hlogk_pos hlogk_le
  have hdiff_eq :
      1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ) =
        (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) / (Real.log k * Real.log ((k + 1 : ℕ) : ℝ)) := by
    field_simp [hlogk_pos.ne', hlogk1_pos.ne']
  constructor
  · rw [hdiff_eq]
    exact div_nonneg (sub_nonneg.mpr hlogk_le) (mul_nonneg hlogk_pos.le hlogk1_pos.le)
  · rw [hdiff_eq]
    have hlog_sub : Real.log ((k + 1 : ℕ) : ℝ) - Real.log k ≤ 1 / (k : ℝ) := by
      rw [← Real.log_div hk1_pos.ne' hk_pos.ne']
      have h1 := Real.log_le_sub_one_of_pos (div_pos hk1_pos hk_pos)
      have h2 : ((k + 1 : ℕ) : ℝ) / (k : ℝ) - 1 = 1 / (k : ℝ) := by
        push_cast
        field_simp [hk_pos.ne']
        ring
      linarith
    have hden_le : (Real.log k) ^ 2 ≤ Real.log k * Real.log ((k + 1 : ℕ) : ℝ) := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left hlogk_le hlogk_pos.le
    calc
      (Real.log ((k + 1 : ℕ) : ℝ) - Real.log k) / (Real.log k * Real.log ((k + 1 : ℕ) : ℝ))
          ≤ (1 / (k : ℝ)) / (Real.log k * Real.log ((k + 1 : ℕ) : ℝ)) :=
            div_le_div_of_nonneg_right hlog_sub (mul_nonneg hlogk_pos.le hlogk1_pos.le)
      _ ≤ (1 / (k : ℝ)) / (Real.log k) ^ 2 :=
            div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hlogk_pos) hden_le
      _ = 1 / ((k : ℝ) * (Real.log k) ^ 2) := by
            rw [div_div]

lemma sum_inv_log_diff_le_two (j : ℕ) :
    ∑ k ∈ Finset.Icc 2 (j - 1), (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) ≤ 2 := by
  by_cases hj : 2 ≤ j
  · have htelesc : ∀ m : ℕ, 2 ≤ m →
        ∑ k ∈ Finset.Icc 2 (m - 1), (1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)) =
          1 / Real.log 2 - 1 / Real.log m := by
      intro m hm
      induction m, hm using Nat.le_induction with
      | base =>
        have hEmpty : Finset.Icc 2 (2 - 1) = ∅ := by decide
        rw [hEmpty, Finset.sum_empty]
        norm_num
      | succ r hr ihr =>
        have heq : r + 1 - 1 = (r - 1) + 1 := by omega
        rw [heq, Finset.sum_Icc_succ_top (by omega : 2 ≤ r - 1 + 1)]
        have hr_eq : r - 1 + 1 = r := by omega
        rw [hr_eq, ihr]
        ring
    rw [htelesc j hj]
    have hlog2 : (1 : ℝ) / 2 < Real.log 2 := half_lt_log_two
    have hlog2_pos : 0 < Real.log 2 := lt_trans (by norm_num) hlog2
    have hlogj_pos : 0 < Real.log j := Real.log_pos (by exact_mod_cast (by omega : 1 < j))
    have hinv2 : 1 / Real.log 2 ≤ 2 := by
      rw [div_le_iff₀ hlog2_pos]
      linarith
    have hinvj : 0 ≤ 1 / Real.log j := by positivity
    linarith
  · have hEmpty : Finset.Icc 2 (j - 1) = ∅ := by
      rw [Finset.Icc_eq_empty_iff]
      omega
    rw [hEmpty, Finset.sum_empty]
    norm_num

lemma hasDerivAt_aux_tail (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun t : ℝ => ((Real.log t) ^ 2 + 2 * Real.log t + 2) / t)
      (-((Real.log x) ^ 2) / x ^ 2) x := by
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hsq : HasDerivAt (fun t : ℝ => (Real.log t) ^ 2) (2 * Real.log x * x⁻¹) x := by
    refine (hlog.pow 2).congr_deriv ?_
    norm_num
  have h2log : HasDerivAt (fun t : ℝ => 2 * Real.log t) (2 * x⁻¹) x := hlog.const_mul 2
  have hnum : HasDerivAt (fun t : ℝ => (Real.log t) ^ 2 + 2 * Real.log t + 2)
      (2 * Real.log x * x⁻¹ + 2 * x⁻¹) x := by
    refine ((hsq.add h2log).add (hasDerivAt_const x (2 : ℝ))).congr_deriv ?_
    ring
  have hdiv : HasDerivAt (fun t : ℝ => ((Real.log t) ^ 2 + 2 * Real.log t + 2) / t)
      (((2 * Real.log x * x⁻¹ + 2 * x⁻¹) * x - ((Real.log x) ^ 2 + 2 * Real.log x + 2) * 1) /
        x ^ 2) x :=
    hnum.div (hasDerivAt_id x) hx.ne'
  refine hdiv.congr_deriv ?_
  field_simp [hx.ne']
  ring

lemma log_sq_div_sq_le_four_diff (j : ℕ) (hj : 3 ≤ j) :
    (Real.log j) ^ 2 / (j : ℝ) ^ 2 ≤
      4 * ((((Real.log ((j - 1 : ℕ) : ℝ)) ^ 2 + 2 * Real.log ((j - 1 : ℕ) : ℝ) + 2) /
            ((j - 1 : ℕ) : ℝ)) -
           (((Real.log j) ^ 2 + 2 * Real.log j + 2) / (j : ℝ))) := by
  let a : ℝ := ((j - 1 : ℕ) : ℝ)
  let b : ℝ := (j : ℝ)
  have ha_pos : 0 < a := by
    dsimp only [a]
    exact_mod_cast (by omega : 0 < j - 1)
  have hab : a < b := by
    dsimp only [a, b]
    exact_mod_cast (by omega : j - 1 < j)
  have hba : b - a = 1 := by
    dsimp only [a, b]
    have hsub : (j - 1 : ℕ) + 1 = j := by omega
    have hcast : ((j - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by exact_mod_cast hsub
    linarith
  let h : ℝ → ℝ := fun t => ((Real.log t) ^ 2 + 2 * Real.log t + 2) / t
  have hcont : ContinuousOn h (Set.Icc a b) := by
    intro t ht
    have ht_pos : 0 < t := lt_of_lt_of_le ha_pos ht.1
    exact (hasDerivAt_aux_tail t ht_pos).continuousAt.continuousWithinAt
  have hderiv : ∀ t ∈ Set.Ioo a b, HasDerivAt h (-((Real.log t) ^ 2) / t ^ 2) t := by
    intro t ht
    exact hasDerivAt_aux_tail t (lt_trans ha_pos ht.1)
  obtain ⟨c, hc, hc_eq⟩ := exists_hasDerivAt_eq_slope h (fun t => -((Real.log t) ^ 2) / t ^ 2)
    hab hcont hderiv
  rw [hba, div_one, neg_div] at hc_eq
  have hdiff : h a - h b = (Real.log c) ^ 2 / c ^ 2 := by
    linarith
  have hc_pos : 0 < c := lt_trans ha_pos hc.1
  have ha_sq_ge : b ≤ a ^ 2 := by
    dsimp only [a, b]
    have hj3 : (3 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have ha_eq : ((j - 1 : ℕ) : ℝ) = (j : ℝ) - 1 := by linarith [hba]
    rw [ha_eq]
    nlinarith
  have hlogb_le : Real.log b ≤ 2 * Real.log c := by
    have h1 : Real.log b ≤ Real.log (a ^ 2) := Real.log_le_log (lt_trans ha_pos hab) ha_sq_ge
    have h2 : Real.log (a ^ 2) = 2 * Real.log a := by
      rw [Real.log_pow]
      norm_num
    have h3 : Real.log a ≤ Real.log c := Real.log_le_log ha_pos hc.1.le
    linarith
  have hlogb_nn : 0 ≤ Real.log b := by
    dsimp only [b]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ j))
  have hlog_sq : (Real.log b) ^ 2 ≤ 4 * (Real.log c) ^ 2 := by
    nlinarith
  have hcsq_le : c ^ 2 ≤ b ^ 2 := by
    nlinarith [hc.2]
  have hbound : (Real.log b) ^ 2 / b ^ 2 ≤ 4 * ((Real.log c) ^ 2 / c ^ 2) := by
    calc
      (Real.log b) ^ 2 / b ^ 2 ≤ (4 * (Real.log c) ^ 2) / b ^ 2 :=
        div_le_div_of_nonneg_right hlog_sq (sq_nonneg b)
      _ ≤ (4 * (Real.log c) ^ 2) / c ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hc_pos) hcsq_le
      _ = 4 * ((Real.log c) ^ 2 / c ^ 2) := by ring
  simpa only [h, a, b, hdiff] using hbound

lemma sum_log_sq_div_sq_tail_le (k N : ℕ) (hk : 2 ≤ k) :
    ∑ j ∈ Finset.Icc (k + 1) N, (Real.log j) ^ 2 / (j : ℝ) ^ 2 ≤
      52 * ((Real.log k) ^ 2 / (k : ℝ)) := by
  let h : ℕ → ℝ := fun m => ((Real.log m) ^ 2 + 2 * Real.log m + 2) / (m : ℝ)
  have hh_nn : ∀ m : ℕ, 1 ≤ m → 0 ≤ h m := by
    intro m hm
    dsimp only [h]
    have hlog_nn : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm)
    have hm_nn : (0 : ℝ) ≤ (m : ℝ) := by positivity
    positivity
  have hstep :
      ∑ j ∈ Finset.Icc (k + 1) N, (Real.log j) ^ 2 / (j : ℝ) ^ 2 ≤ 4 * h k := by
    calc
      ∑ j ∈ Finset.Icc (k + 1) N, (Real.log j) ^ 2 / (j : ℝ) ^ 2
          ≤ ∑ j ∈ Finset.Icc (k + 1) N, 4 * (h (j - 1) - h j) := by
            refine Finset.sum_le_sum fun j hj => ?_
            have hj3 : 3 ≤ j := by
              rw [Finset.mem_Icc] at hj
              omega
            exact log_sq_div_sq_le_four_diff j hj3
      _ = 4 * ∑ j ∈ Finset.Icc (k + 1) N, (h (j - 1) - h j) := by
            rw [← Finset.mul_sum]
      _ ≤ 4 * h k := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            by_cases hN : k + 1 ≤ N
            · have htelesc : ∀ M : ℕ, k + 1 ≤ M →
                  ∑ j ∈ Finset.Icc (k + 1) M, (h (j - 1) - h j) = h k - h M := by
                intro M hM
                induction M, hM using Nat.le_induction with
                | base =>
                  rw [Finset.Icc_self, Finset.sum_singleton]
                  have hk1 : k + 1 - 1 = k := by omega
                  rw [hk1]
                | succ r hr ihr =>
                  rw [Finset.sum_Icc_succ_top (by omega : k + 1 ≤ r + 1), ihr]
                  have hr1 : r + 1 - 1 = r := by omega
                  rw [hr1]
                  ring
              rw [htelesc N hN]
              linarith [hh_nn N (by omega)]
            · have hEmpty : Finset.Icc (k + 1) N = ∅ := by
                rw [Finset.Icc_eq_empty_iff]
                omega
              rw [hEmpty, Finset.sum_empty]
              exact hh_nn k (by omega)
  have hlogk : (1 : ℝ) / 2 < Real.log k := by
    refine lt_of_lt_of_le half_lt_log_two ?_
    exact Real.log_le_log (by norm_num) (by exact_mod_cast hk)
  have hhk_le : 4 * h k ≤ 52 * ((Real.log k) ^ 2 / (k : ℝ)) := by
    dsimp only [h]
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hpoly : (Real.log k) ^ 2 + 2 * Real.log k + 2 ≤ 13 * (Real.log k) ^ 2 := by
      nlinarith
    have hdiv := div_le_div_of_nonneg_right hpoly hk_pos.le
    rw [mul_div_assoc] at hdiv
    linarith
  exact le_trans hstep hhk_le

lemma sum_pi4_le_sum_theta4 (N : ℕ) :
    ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) *
      (((Real.log j / Real.sqrt j) * ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) ^ 2) ≤
    210 * ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) *
      ((∑ p ∈ Finset.Icc 1 j, if p.Prime then (ZMod.χ₄ (p : ZMod 4) : ℝ) * Real.log p else 0) /
        Real.sqrt j) ^ 2 := by
  let θ₄ : ℕ → ℝ := fun m =>
    ∑ p ∈ Finset.Icc 1 m, if p.Prime then (ZMod.χ₄ (p : ZMod 4) : ℝ) * Real.log p else 0
  let Δ : ℕ → ℝ := fun k => 1 / Real.log k - 1 / Real.log ((k + 1 : ℕ) : ℝ)
  have hpoint : ∀ j ∈ Finset.Icc 2 N,
      (1 / (j : ℝ)) *
        (((Real.log j / Real.sqrt j) * ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) ^ 2) ≤
      2 * ((1 / (j : ℝ)) * (θ₄ j / Real.sqrt j) ^ 2) +
      4 * ((Real.log j) ^ 2 / (j : ℝ) ^ 2) *
        ∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2) := by
    intro j hj
    have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hlogj_pos : 0 < Real.log j := Real.log_pos (by exact_mod_cast (by omega : 1 < j))
    have hsqrt_sq : (Real.sqrt j) ^ 2 = (j : ℝ) := Real.sq_sqrt hj_pos.le
    have habel := pi4_eq_abel_sum j hj2
    have hprod :
        (Real.log j / Real.sqrt j) * ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3) =
          θ₄ j / Real.sqrt j + (Real.log j / Real.sqrt j) * ∑ k ∈ Finset.Icc 2 (j - 1), θ₄ k * Δ k := by
      rw [habel]
      dsimp only [θ₄, Δ]
      have h1 : (Real.log j / Real.sqrt j) * (θ₄ j / Real.log j) = θ₄ j / Real.sqrt j := by
        field_simp [hlogj_pos.ne', (Real.sqrt_pos.mpr hj_pos).ne']
      rw [mul_add, h1]
    have hsq_split :
        ((Real.log j / Real.sqrt j) * ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) ^ 2 ≤
          2 * (θ₄ j / Real.sqrt j) ^ 2 +
          2 * ((Real.log j) ^ 2 / (j : ℝ)) * (∑ k ∈ Finset.Icc 2 (j - 1), θ₄ k * Δ k) ^ 2 := by
      rw [hprod]
      have h2uv : ∀ u v : ℝ, (u + v) ^ 2 ≤ 2 * u ^ 2 + 2 * v ^ 2 := fun u v => by
        nlinarith [sq_nonneg (u - v)]
      have hfactor :
          ((Real.log j / Real.sqrt j) * ∑ k ∈ Finset.Icc 2 (j - 1), θ₄ k * Δ k) ^ 2 =
            ((Real.log j) ^ 2 / (j : ℝ)) * (∑ k ∈ Finset.Icc 2 (j - 1), θ₄ k * Δ k) ^ 2 := by
        rw [mul_pow, div_pow, hsqrt_sq]
      linarith [h2uv (θ₄ j / Real.sqrt j)
        ((Real.log j / Real.sqrt j) * ∑ k ∈ Finset.Icc 2 (j - 1), θ₄ k * Δ k)]
    have hcs :
        (∑ k ∈ Finset.Icc 2 (j - 1), θ₄ k * Δ k) ^ 2 ≤
          2 * ∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2) := by
      have hrew :
          ∑ k ∈ Finset.Icc 2 (j - 1), θ₄ k * Δ k =
            ∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k * Real.sqrt (Δ k)) * Real.sqrt (Δ k) := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
        have hΔnn : 0 ≤ Δ k := (inv_log_sub_bounds k hk2).1
        rw [mul_assoc, Real.mul_self_sqrt hΔnn]
      rw [hrew]
      have hcs0 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 2 (j - 1))
        (fun k => θ₄ k * Real.sqrt (Δ k)) (fun k => Real.sqrt (Δ k))
      have hsum1 :
          ∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k * Real.sqrt (Δ k)) ^ 2 ≤
            ∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2) := by
        refine Finset.sum_le_sum fun k hk => ?_
        have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
        have hΔb := inv_log_sub_bounds k hk2
        rw [mul_pow, Real.sq_sqrt hΔb.1]
        calc
          (θ₄ k) ^ 2 * Δ k ≤ (θ₄ k) ^ 2 * (1 / ((k : ℝ) * (Real.log k) ^ 2)) :=
            mul_le_mul_of_nonneg_left hΔb.2 (sq_nonneg _)
          _ = (θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2) := by ring
      have hsum2 : ∑ k ∈ Finset.Icc 2 (j - 1), (Real.sqrt (Δ k)) ^ 2 ≤ 2 := by
        calc
          ∑ k ∈ Finset.Icc 2 (j - 1), (Real.sqrt (Δ k)) ^ 2 =
              ∑ k ∈ Finset.Icc 2 (j - 1), Δ k := by
            refine Finset.sum_congr rfl fun k hk => ?_
            exact Real.sq_sqrt (inv_log_sub_bounds k (Finset.mem_Icc.mp hk).1).1
          _ ≤ 2 := sum_inv_log_diff_le_two j
      have hsum1_nn : 0 ≤ ∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k * Real.sqrt (Δ k)) ^ 2 :=
        Finset.sum_nonneg fun _ _ => sq_nonneg _
      calc
        (∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k * Real.sqrt (Δ k)) * Real.sqrt (Δ k)) ^ 2
            ≤ (∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k * Real.sqrt (Δ k)) ^ 2) *
                (∑ k ∈ Finset.Icc 2 (j - 1), (Real.sqrt (Δ k)) ^ 2) := hcs0
        _ ≤ (∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2)) * 2 :=
              mul_le_mul hsum1 hsum2 (Finset.sum_nonneg fun _ _ => sq_nonneg _)
                (Finset.sum_nonneg fun k _ => by positivity)
        _ = 2 * ∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2) := by ring
    have hmul := mul_le_mul_of_nonneg_left hsq_split (by positivity : (0 : ℝ) ≤ 1 / (j : ℝ))
    have htail_mul := mul_le_mul_of_nonneg_left hcs
      (by positivity : (0 : ℝ) ≤ (1 / (j : ℝ)) * (2 * ((Real.log j) ^ 2 / (j : ℝ))))
    calc
      (1 / (j : ℝ)) *
          (((Real.log j / Real.sqrt j) * ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) ^ 2)
          ≤ (1 / (j : ℝ)) * (2 * (θ₄ j / Real.sqrt j) ^ 2 +
              2 * ((Real.log j) ^ 2 / (j : ℝ)) * (∑ k ∈ Finset.Icc 2 (j - 1), θ₄ k * Δ k) ^ 2) := hmul
      _ = 2 * ((1 / (j : ℝ)) * (θ₄ j / Real.sqrt j) ^ 2) +
            ((1 / (j : ℝ)) * (2 * ((Real.log j) ^ 2 / (j : ℝ)))) *
              (∑ k ∈ Finset.Icc 2 (j - 1), θ₄ k * Δ k) ^ 2 := by ring
      _ ≤ 2 * ((1 / (j : ℝ)) * (θ₄ j / Real.sqrt j) ^ 2) +
            ((1 / (j : ℝ)) * (2 * ((Real.log j) ^ 2 / (j : ℝ)))) *
              (2 * ∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2)) :=
            add_le_add le_rfl htail_mul
      _ = 2 * ((1 / (j : ℝ)) * (θ₄ j / Real.sqrt j) ^ 2) +
            4 * ((Real.log j) ^ 2 / (j : ℝ) ^ 2) *
              ∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2) := by
            field_simp [hj_pos.ne']
            ring
  have hsum_step :
      ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) *
        (((Real.log j / Real.sqrt j) * ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) ^ 2) ≤
      2 * (∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * (θ₄ j / Real.sqrt j) ^ 2) +
      4 * ∑ j ∈ Finset.Icc 2 N, ((Real.log j) ^ 2 / (j : ℝ) ^ 2) *
        ∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2) := by
    calc
      ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) *
          (((Real.log j / Real.sqrt j) * ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) ^ 2)
          ≤ ∑ j ∈ Finset.Icc 2 N,
              (2 * ((1 / (j : ℝ)) * (θ₄ j / Real.sqrt j) ^ 2) +
               4 * ((Real.log j) ^ 2 / (j : ℝ) ^ 2) *
                 ∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2)) :=
            Finset.sum_le_sum hpoint
      _ = 2 * (∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * (θ₄ j / Real.sqrt j) ^ 2) +
          4 * ∑ j ∈ Finset.Icc 2 N, ((Real.log j) ^ 2 / (j : ℝ) ^ 2) *
            ∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum]
            congr 1
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun _ _ => ?_
            ring
  have hswap :
      ∑ j ∈ Finset.Icc 2 N, ((Real.log j) ^ 2 / (j : ℝ) ^ 2) *
          ∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2) =
        ∑ k ∈ Finset.Icc 2 N, ((θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2)) *
          ∑ j ∈ Finset.Icc (k + 1) N, (Real.log j) ^ 2 / (j : ℝ) ^ 2 := by
    have hL :
        ∑ j ∈ Finset.Icc 2 N, ((Real.log j) ^ 2 / (j : ℝ) ^ 2) *
            ∑ k ∈ Finset.Icc 2 (j - 1), (θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2) =
          ∑ j ∈ Finset.Icc 2 N, ∑ k ∈ Finset.Icc 2 N,
            if k < j then
              ((Real.log j) ^ 2 / (j : ℝ) ^ 2) * ((θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2))
            else 0 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Finset.mul_sum, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext k
      simp only [Finset.mem_Icc, Finset.mem_filter]
      have hjN : j ≤ N := (Finset.mem_Icc.mp hj).2
      omega
    have hR :
        ∑ k ∈ Finset.Icc 2 N, ((θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2)) *
            ∑ j ∈ Finset.Icc (k + 1) N, (Real.log j) ^ 2 / (j : ℝ) ^ 2 =
          ∑ k ∈ Finset.Icc 2 N, ∑ j ∈ Finset.Icc 2 N,
            if k < j then
              ((Real.log j) ^ 2 / (j : ℝ) ^ 2) * ((θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2))
            else 0 := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mul_sum, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => mul_comm _ _
      ext j
      simp only [Finset.mem_Icc, Finset.mem_filter]
      have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
      omega
    rw [hL, hR, Finset.sum_comm]
  have hdouble_le :
      ∑ k ∈ Finset.Icc 2 N, ((θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2)) *
          ∑ j ∈ Finset.Icc (k + 1) N, (Real.log j) ^ 2 / (j : ℝ) ^ 2 ≤
        52 * ∑ k ∈ Finset.Icc 2 N, (1 / (k : ℝ)) * (θ₄ k / Real.sqrt k) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k hk => ?_
    have hk2 : 2 ≤ k := (Finset.mem_Icc.mp hk).1
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hlogk_pos : 0 < Real.log k := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    have htail := sum_log_sq_div_sq_tail_le k N hk2
    have hcoeff_nn : 0 ≤ (θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2) := by positivity
    calc
      ((θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2)) *
          ∑ j ∈ Finset.Icc (k + 1) N, (Real.log j) ^ 2 / (j : ℝ) ^ 2
          ≤ ((θ₄ k) ^ 2 / ((k : ℝ) * (Real.log k) ^ 2)) * (52 * ((Real.log k) ^ 2 / (k : ℝ))) :=
            mul_le_mul_of_nonneg_left htail hcoeff_nn
      _ = 52 * ((1 / (k : ℝ)) * (θ₄ k / Real.sqrt k) ^ 2) := by
            rw [div_pow, Real.sq_sqrt hk_pos.le]
            field_simp [hk_pos.ne', hlogk_pos.ne']
  rw [hswap] at hsum_step
  linarith

/- === Section 3: Chebyshev Prime-Power Reduction and Harmonic Bound === -/

lemma abs_psi4_sub_theta4_le :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ j : ℕ,
      |(∑ n ∈ Finset.Icc 1 j, ArithmeticFunction.vonMangoldt n * (ZMod.χ₄ (n : ZMod 4) : ℝ)) -
       (∑ p ∈ Finset.Icc 1 j, if p.Prime then (ZMod.χ₄ (p : ZMod 4) : ℝ) * Real.log p else 0)| ≤
        C₀ * Real.sqrt j := by
  obtain ⟨C, hC⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨max C 0, le_max_right C 0, fun j => ?_⟩
  rw [← Finset.sum_sub_distrib]
  have hIoc : Finset.Ioc 0 ⌊(j : ℝ)⌋₊ = Finset.Icc 1 j := by
    rw [Nat.floor_natCast]
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have hpsi : Chebyshev.psi (j : ℝ) = ∑ n ∈ Finset.Icc 1 j, ArithmeticFunction.vonMangoldt n := by
    rw [Chebyshev.psi, hIoc]
  have htheta :
      Chebyshev.theta (j : ℝ) =
        ∑ n ∈ Finset.Icc 1 j, if n.Prime then Real.log n else 0 := by
    rw [Chebyshev.theta, hIoc, Finset.sum_filter]
  have hterm : ∀ n ∈ Finset.Icc 1 j,
      |ArithmeticFunction.vonMangoldt n * (ZMod.χ₄ (n : ZMod 4) : ℝ) -
        (if n.Prime then (ZMod.χ₄ (n : ZMod 4) : ℝ) * Real.log n else 0)| ≤
      ArithmeticFunction.vonMangoldt n - (if n.Prime then Real.log n else 0) := by
    intro n _
    by_cases hp : n.Prime
    · simp only [hp, ↓reduceIte, ArithmeticFunction.vonMangoldt_apply_prime hp]
      rw [mul_comm, sub_self, abs_zero, sub_self]
    · simp only [hp, ↓reduceIte, sub_zero, abs_mul]
      have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      rw [abs_of_nonneg hΛ]
      calc
        ArithmeticFunction.vonMangoldt n * |(ZMod.χ₄ (n : ZMod 4) : ℝ)|
            ≤ ArithmeticFunction.vonMangoldt n * 1 :=
              mul_le_mul_of_nonneg_left (abs_chi4_le_one n) hΛ
        _ = ArithmeticFunction.vonMangoldt n := mul_one _
  calc
    |∑ n ∈ Finset.Icc 1 j,
        (ArithmeticFunction.vonMangoldt n * (ZMod.χ₄ (n : ZMod 4) : ℝ) -
          if n.Prime then (ZMod.χ₄ (n : ZMod 4) : ℝ) * Real.log n else 0)|
        ≤ ∑ n ∈ Finset.Icc 1 j,
            |ArithmeticFunction.vonMangoldt n * (ZMod.χ₄ (n : ZMod 4) : ℝ) -
              if n.Prime then (ZMod.χ₄ (n : ZMod 4) : ℝ) * Real.log n else 0| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 j,
          (ArithmeticFunction.vonMangoldt n - if n.Prime then Real.log n else 0) :=
          Finset.sum_le_sum hterm
    _ = Chebyshev.psi (j : ℝ) - Chebyshev.theta (j : ℝ) := by
          rw [Finset.sum_sub_distrib, hpsi, htheta]
    _ ≤ C * Real.sqrt j := hC (j : ℝ)
    _ ≤ max C 0 * Real.sqrt j :=
          mul_le_mul_of_nonneg_right (le_max_left C 0) (Real.sqrt_nonneg _)

lemma sum_inv_le_log (N : ℕ) :
    ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) ≤ Real.log N := by
  by_cases hN : 1 ≤ N
  · induction N, hN using Nat.le_induction with
    | base =>
      have hEmpty : Finset.Icc 2 1 = ∅ := by decide
      rw [hEmpty, Finset.sum_empty, Nat.cast_one, Real.log_one]
    | succ m hm ih =>
      rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ m + 1)]
      have hm_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
      have hm1_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < m + 1)
      have hstep : 1 / ((m + 1 : ℕ) : ℝ) ≤ Real.log ((m + 1 : ℕ) : ℝ) - Real.log m := by
        have h1 := Real.log_le_sub_one_of_pos (div_pos hm_pos hm1_pos)
        rw [Real.log_div hm_pos.ne' hm1_pos.ne'] at h1
        have h2 : (m : ℝ) / ((m + 1 : ℕ) : ℝ) - 1 = -(1 / ((m + 1 : ℕ) : ℝ)) := by
          push_cast
          field_simp [hm1_pos.ne']
          ring
        linarith
      linarith
  · have hN0 : N = 0 := by omega
    subst hN0
    have hEmpty : Finset.Icc 2 0 = ∅ := by decide
    rw [hEmpty, Finset.sum_empty, Nat.cast_zero, Real.log_zero]

/- === Section 4: Step-Function Integral Comparison === -/

lemma sum_psi4_le_integral (N : ℕ) (hN : 8 ≤ N) :
    let σ : ℝ := (1 : ℝ) / 2 + 1 / Real.log ((N + 1 : ℕ) : ℝ)
    ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) *
      ((∑ n ∈ Finset.Icc 1 j,
          ArithmeticFunction.vonMangoldt n * (ZMod.χ₄ (n : ZMod 4) : ℝ)) / Real.sqrt j) ^ 2 ≤
    (9 * Real.exp 2 / 4) *
      ∫ x in (1 : ℝ)..((N + 1 : ℕ) : ℝ),
        (∑ n ∈ Finset.Icc 1 ⌊x⌋₊,
          ArithmeticFunction.vonMangoldt n * (ZMod.χ₄ (n : ZMod 4) : ℝ)) ^ 2 *
          x ^ (-(2 * σ + 1)) := by
  intro σ
  let ψ₄ : ℕ → ℝ := fun m =>
    ∑ n ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt n * (ZMod.χ₄ (n : ZMod 4) : ℝ)
  let f : ℝ → ℝ := fun x => (ψ₄ ⌊x⌋₊) ^ 2 * x ^ (-(2 * σ + 1))
  have hlogN1_pos : 0 < Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N + 1))
  have hpiece : ∀ k : ℕ, 1 ≤ k →
      IntervalIntegrable f volume (k : ℝ) ((k + 1 : ℕ) : ℝ) ∧
      ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), f x =
        ∫ x in (k : ℝ)..((k + 1 : ℕ) : ℝ), (ψ₄ k) ^ 2 * x ^ (-(2 * σ + 1)) := by
    intro k hk
    let g : ℝ → ℝ := fun x => (ψ₄ k) ^ 2 * x ^ (-(2 * σ + 1))
    have hk_le : (k : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : k ≤ k + 1)
    have hcont : ContinuousOn g (Set.Icc (k : ℝ) ((k + 1 : ℕ) : ℝ)) := by
      refine ContinuousOn.mul continuousOn_const ?_
      intro x hx
      have hx_pos : 0 < x := lt_of_lt_of_le (by exact_mod_cast (by omega : 0 < k)) hx.1
      exact (Real.continuousAt_rpow_const x _ (Or.inl hx_pos.ne')).continuousWithinAt
    have hg_int : IntervalIntegrable g volume (k : ℝ) ((k + 1 : ℕ) : ℝ) :=
      hcont.intervalIntegrable_of_Icc hk_le
    have hae : ∀ᵐ x ∂volume, x ∈ Set.uIoc (k : ℝ) ((k + 1 : ℕ) : ℝ) → f x = g x := by
      have hne : ∀ᵐ x ∂volume, x ≠ ((k + 1 : ℕ) : ℝ) := by
        rw [ae_iff]
        simp
      filter_upwards [hne] with x hxne hxmem
      rw [Set.uIoc_of_le hk_le] at hxmem
      have hx_lt : x < ((k + 1 : ℕ) : ℝ) := lt_of_le_of_ne hxmem.2 hxne
      have hfl : ⌊x⌋₊ = k := by
        rw [Nat.floor_eq_iff (le_trans (by positivity) hxmem.1.le)]
        refine ⟨hxmem.1.le, ?_⟩
        simpa only [Nat.cast_add, Nat.cast_one] using hx_lt
      dsimp only [f, g]
      rw [hfl]
    have hae_res : g =ᵐ[volume.restrict (Set.uIoc (k : ℝ) ((k + 1 : ℕ) : ℝ))] f := by
      rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
      filter_upwards [hae] with x hx hmem
      exact (hx hmem).symm
    exact ⟨hg_int.congr_ae hae_res, intervalIntegral.integral_congr_ae hae⟩
  have hsplit :
      ∫ x in (1 : ℝ)..((N + 1 : ℕ) : ℝ), f x =
        ∑ k ∈ Finset.range N, ∫ x in ((k + 1 : ℕ) : ℝ)..((k + 2 : ℕ) : ℝ), f x := by
    have h := intervalIntegral.sum_integral_adjacent_intervals
      (f := f) (μ := volume) (a := fun m : ℕ => ((m + 1 : ℕ) : ℝ)) (n := N)
      (fun k _ => (hpiece (k + 1) (by omega)).1)
    simpa only [Nat.cast_one, zero_add] using h.symm
  have h1_nn : 0 ≤ ∫ x in ((0 + 1 : ℕ) : ℝ)..((0 + 2 : ℕ) : ℝ), f x := by
    refine intervalIntegral.integral_nonneg (by norm_num) fun x hx => ?_
    dsimp only [f]
    have hx_nn : 0 ≤ x := le_trans (by norm_num) hx.1
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx_nn _)
  have hpiece_lb : ∀ j ∈ Finset.Icc 2 N,
      (4 / (9 * Real.exp 2)) * ((1 / (j : ℝ)) * (ψ₄ j / Real.sqrt j) ^ 2) ≤
        ∫ x in (j : ℝ)..((j + 1 : ℕ) : ℝ), f x := by
    intro j hj
    have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
    have hjN : j ≤ N := (Finset.mem_Icc.mp hj).2
    have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
    have hj_le : (j : ℝ) ≤ ((j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : j ≤ j + 1)
    rw [(hpiece j (by omega)).2]
    let g : ℝ → ℝ := fun x => (ψ₄ j) ^ 2 * x ^ (-(2 * σ + 1))
    let c : ℝ := (4 / (9 * Real.exp 2)) * ((1 / (j : ℝ)) * (ψ₄ j / Real.sqrt j) ^ 2)
    have hcont : ContinuousOn g (Set.Icc (j : ℝ) ((j + 1 : ℕ) : ℝ)) := by
      refine ContinuousOn.mul continuousOn_const ?_
      intro x hx
      have hx_pos : 0 < x := lt_of_lt_of_le hj_pos hx.1
      exact (Real.continuousAt_rpow_const x _ (Or.inl hx_pos.ne')).continuousWithinAt
    have hg_int : IntervalIntegrable g volume (j : ℝ) ((j + 1 : ℕ) : ℝ) :=
      hcont.intervalIntegrable_of_Icc hj_le
    have hc_int : IntervalIntegrable (fun _ : ℝ => c) volume (j : ℝ) ((j + 1 : ℕ) : ℝ) :=
      intervalIntegrable_const
    have hmono : ∀ x ∈ Set.Icc (j : ℝ) ((j + 1 : ℕ) : ℝ), c ≤ g x := by
      intro x hx
      have hx_pos : 0 < x := lt_of_lt_of_le hj_pos hx.1
      have hx_le_32 : x ≤ (3 : ℝ) / 2 * (j : ℝ) := by
        have h1 : ((j + 1 : ℕ) : ℝ) ≤ (3 : ℝ) / 2 * (j : ℝ) := by
          have hj2r : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj2
          push_cast
          linarith
        exact le_trans hx.2 h1
      have hx_le_N1 : x ≤ ((N + 1 : ℕ) : ℝ) := by
        exact le_trans hx.2 (by exact_mod_cast (by omega : j + 1 ≤ N + 1))
      have hexp_eq : -(2 * σ + 1) = (-2 : ℝ) + -(2 / Real.log ((N + 1 : ℕ) : ℝ)) := by
        dsimp only [σ]
        ring
      have hrpow_split :
          x ^ (-(2 * σ + 1)) = (x ^ (2 : ℕ))⁻¹ * (x ^ (2 / Real.log ((N + 1 : ℕ) : ℝ)))⁻¹ := by
        rw [hexp_eq, Real.rpow_add hx_pos, Real.rpow_neg hx_pos.le, Real.rpow_neg hx_pos.le]
        norm_cast
      have h1 : 4 / (9 * (j : ℝ) ^ 2) ≤ (x ^ (2 : ℕ))⁻¹ := by
        have hxsq : x ^ (2 : ℕ) ≤ (9 / 4) * (j : ℝ) ^ 2 := by
          nlinarith [hx_pos]
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 9 * (j : ℝ) ^ 2)]
        have hxsq_pos : 0 < x ^ (2 : ℕ) := sq_pos_of_pos hx_pos
        rw [mul_comm, ← div_eq_mul_inv, le_div_iff₀ hxsq_pos]
        linarith
      have h2 : (Real.exp 2)⁻¹ ≤ (x ^ (2 / Real.log ((N + 1 : ℕ) : ℝ)))⁻¹ := by
        have hbase_le :
            x ^ (2 / Real.log ((N + 1 : ℕ) : ℝ)) ≤
              ((N + 1 : ℕ) : ℝ) ^ (2 / Real.log ((N + 1 : ℕ) : ℝ)) :=
          Real.rpow_le_rpow hx_pos.le hx_le_N1 (by positivity)
        have hN1_pow :
            ((N + 1 : ℕ) : ℝ) ^ (2 / Real.log ((N + 1 : ℕ) : ℝ)) = Real.exp 2 := by
          have hN1_pos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < N + 1)
          rw [Real.rpow_def_of_pos hN1_pos]
          congr 1
          field_simp [hlogN1_pos.ne']
        rw [hN1_pow] at hbase_le
        exact inv_anti₀ (Real.rpow_pos_of_pos hx_pos _) hbase_le
      have hrpow_lb : 4 / (9 * Real.exp 2) * (1 / (j : ℝ) ^ 2) ≤ x ^ (-(2 * σ + 1)) := by
        rw [hrpow_split]
        calc
          4 / (9 * Real.exp 2) * (1 / (j : ℝ) ^ 2)
              = (4 / (9 * (j : ℝ) ^ 2)) * (Real.exp 2)⁻¹ := by ring
          _ ≤ (x ^ (2 : ℕ))⁻¹ * (x ^ (2 / Real.log ((N + 1 : ℕ) : ℝ)))⁻¹ :=
                mul_le_mul h1 h2 (by positivity) (by positivity)
      dsimp only [c, g]
      rw [div_pow, Real.sq_sqrt hj_pos.le]
      calc
        4 / (9 * Real.exp 2) * (1 / (j : ℝ) * ((ψ₄ j) ^ 2 / (j : ℝ)))
            = (ψ₄ j) ^ 2 * (4 / (9 * Real.exp 2) * (1 / (j : ℝ) ^ 2)) := by ring
        _ ≤ (ψ₄ j) ^ 2 * x ^ (-(2 * σ + 1)) :=
              mul_le_mul_of_nonneg_left hrpow_lb (sq_nonneg _)
    have hint := intervalIntegral.integral_mono_on hj_le hc_int hg_int hmono
    rw [intervalIntegral.integral_const] at hint
    have hlen : ((j + 1 : ℕ) : ℝ) - (j : ℝ) = 1 := by
      push_cast
      ring
    rw [hlen, one_smul] at hint
    exact hint
  have hsum_range :
      ∑ k ∈ Finset.range N, ∫ x in ((k + 1 : ℕ) : ℝ)..((k + 2 : ℕ) : ℝ), f x =
        (∫ x in ((0 + 1 : ℕ) : ℝ)..((0 + 2 : ℕ) : ℝ), f x) +
        ∑ j ∈ Finset.Icc 2 N, ∫ x in (j : ℝ)..((j + 1 : ℕ) : ℝ), f x := by
    have hN_pos : 0 < N := by omega
    have hsplit0 :
        ∑ k ∈ Finset.range N, ∫ x in ((k + 1 : ℕ) : ℝ)..((k + 2 : ℕ) : ℝ), f x =
          (∫ x in ((0 + 1 : ℕ) : ℝ)..((0 + 2 : ℕ) : ℝ), f x) +
          ∑ k ∈ (Finset.range N).erase 0, ∫ x in ((k + 1 : ℕ) : ℝ)..((k + 2 : ℕ) : ℝ), f x := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_range.mpr hN_pos)]
    rw [hsplit0]
    congr 1
    refine Finset.sum_nbij (fun k => k + 1) ?_ ?_ ?_ ?_
    · intro k hk
      rw [Finset.mem_erase, Finset.mem_range] at hk
      rw [Finset.mem_Icc]
      omega
    · intro k₁ _ k₂ _ heq
      dsimp only at heq
      omega
    · intro j hj
      rw [Finset.mem_coe, Finset.mem_Icc] at hj
      refine ⟨j - 1, ?_, by dsimp only; omega⟩
      rw [Finset.mem_coe, Finset.mem_erase, Finset.mem_range]
      omega
    · intro _ _
      rfl
  have htot :
      (4 / (9 * Real.exp 2)) *
        ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * (ψ₄ j / Real.sqrt j) ^ 2 ≤
      ∫ x in (1 : ℝ)..((N + 1 : ℕ) : ℝ), f x := by
    rw [hsplit, hsum_range, Finset.mul_sum]
    have h2 :
        ∑ j ∈ Finset.Icc 2 N, (4 / (9 * Real.exp 2)) * ((1 / (j : ℝ)) * (ψ₄ j / Real.sqrt j) ^ 2) ≤
          ∑ j ∈ Finset.Icc 2 N, ∫ x in (j : ℝ)..((j + 1 : ℕ) : ℝ), f x :=
      Finset.sum_le_sum hpiece_lb
    exact le_trans h2 (le_add_of_nonneg_left h1_nn)
  have hmul := mul_le_mul_of_nonneg_left htot (by positivity : (0 : ℝ) ≤ 9 * Real.exp 2 / 4)
  have hcancel : (9 * Real.exp 2 / 4) * (4 / (9 * Real.exp 2)) = 1 := by
    field_simp [(Real.exp_pos 2).ne']
  rw [← mul_assoc, hcancel, one_mul] at hmul
  exact hmul

/- === Section 5: Main Reduction Theorem === -/

theorem main : H1 → H2 → OMA.R_ChebyshevBias_knapowski_turan_natural_density_false_R1.H1 := by
  intro h1 h2 hGRH
  obtain ⟨C, hC_pos, hC⟩ := h2 hGRH
  obtain ⟨C₀, hC₀_nn, hC₀⟩ := abs_psi4_sub_theta4_le
  let B : ℝ := 420 * (9 * Real.exp 2 / 4) * (C / Real.pi) + 420 * C₀ ^ 2 + 1
  have hB_pos : 0 < B := by
    dsimp only [B]
    positivity
  refine ⟨B, hB_pos, Filter.eventually_atTop.mpr ⟨8, fun N hN => ?_⟩⟩
  let θ₄ : ℕ → ℝ := fun m =>
    ∑ p ∈ Finset.Icc 1 m, if p.Prime then (ZMod.χ₄ (p : ZMod 4) : ℝ) * Real.log p else 0
  let ψ₄ : ℕ → ℝ := fun m =>
    ∑ n ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt n * (ZMod.χ₄ (n : ZMod 4) : ℝ)
  have hpi_theta := sum_pi4_le_sum_theta4 N
  have htheta_psi :
      ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * (θ₄ j / Real.sqrt j) ^ 2 ≤
        2 * (∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * (ψ₄ j / Real.sqrt j) ^ 2) +
        2 * C₀ ^ 2 * Real.log N := by
    have hpt : ∀ j ∈ Finset.Icc 2 N,
        (1 / (j : ℝ)) * (θ₄ j / Real.sqrt j) ^ 2 ≤
          2 * ((1 / (j : ℝ)) * (ψ₄ j / Real.sqrt j) ^ 2) + 2 * C₀ ^ 2 * (1 / (j : ℝ)) := by
      intro j hj
      have hj2 : 2 ≤ j := (Finset.mem_Icc.mp hj).1
      have hj_pos : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
      have hsqrt_pos : 0 < Real.sqrt j := Real.sqrt_pos.mpr hj_pos
      have hdiff_abs : |θ₄ j - ψ₄ j| ≤ C₀ * Real.sqrt j := by
        rw [abs_sub_comm]
        exact hC₀ j
      have hdiff_div : |θ₄ j / Real.sqrt j - ψ₄ j / Real.sqrt j| ≤ C₀ := by
        rw [← sub_div, abs_div, abs_of_pos hsqrt_pos, div_le_iff₀ hsqrt_pos]
        exact hdiff_abs
      have hdiff_sq : (θ₄ j / Real.sqrt j - ψ₄ j / Real.sqrt j) ^ 2 ≤ C₀ ^ 2 := by
        nlinarith [abs_le.mp hdiff_div]
      have hsq : (θ₄ j / Real.sqrt j) ^ 2 ≤ 2 * (ψ₄ j / Real.sqrt j) ^ 2 + 2 * C₀ ^ 2 := by
        nlinarith [sq_nonneg (θ₄ j / Real.sqrt j - 2 * (ψ₄ j / Real.sqrt j) + ψ₄ j / Real.sqrt j),
          sq_nonneg (ψ₄ j / Real.sqrt j - (θ₄ j / Real.sqrt j - ψ₄ j / Real.sqrt j))]
      have hmul := mul_le_mul_of_nonneg_left hsq (by positivity : (0 : ℝ) ≤ 1 / (j : ℝ))
      linarith
    calc
      ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * (θ₄ j / Real.sqrt j) ^ 2
          ≤ ∑ j ∈ Finset.Icc 2 N,
              (2 * ((1 / (j : ℝ)) * (ψ₄ j / Real.sqrt j) ^ 2) + 2 * C₀ ^ 2 * (1 / (j : ℝ))) :=
            Finset.sum_le_sum hpt
      _ = 2 * (∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * (ψ₄ j / Real.sqrt j) ^ 2) +
          2 * C₀ ^ 2 * ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ 2 * (∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * (ψ₄ j / Real.sqrt j) ^ 2) +
          2 * C₀ ^ 2 * Real.log N := by
            refine add_le_add le_rfl ?_
            exact mul_le_mul_of_nonneg_left (sum_inv_le_log N) (by positivity)
  let σ : ℝ := (1 : ℝ) / 2 + 1 / Real.log ((N + 1 : ℕ) : ℝ)
  have hlogN_pos : 0 < Real.log N := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hlogN1_gt_two : (2 : ℝ) < Real.log ((N + 1 : ℕ) : ℝ) := by
    have hexp2 : Real.exp 2 < 9 := by
      have h1 : Real.exp 1 < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
      have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
        rw [← Real.exp_add]
        norm_num
      nlinarith [Real.exp_pos 1]
    have h9 : (9 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 9 ≤ N + 1)
    have hlt := Real.log_lt_log (Real.exp_pos 2) (lt_of_lt_of_le hexp2 h9)
    rwa [Real.log_exp] at hlt
  have hlogN1_pos : 0 < Real.log ((N + 1 : ℕ) : ℝ) := lt_trans (by norm_num) hlogN1_gt_two
  have hσ_gt : (1 : ℝ) / 2 < σ := by
    dsimp only [σ]
    have hinv : 0 < 1 / Real.log ((N + 1 : ℕ) : ℝ) := by positivity
    linarith
  have hσ_le : σ ≤ 1 := by
    dsimp only [σ]
    have hinv : 1 / Real.log ((N + 1 : ℕ) : ℝ) ≤ (1 : ℝ) / 2 := by
      rw [div_le_div_iff₀ hlogN1_pos (by norm_num)]
      linarith
    linarith
  have hlogN1_le : Real.log ((N + 1 : ℕ) : ℝ) ≤ 2 * Real.log N := by
    have hle : ((N + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (2 : ℕ) := by
      have hN8 : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      push_cast
      nlinarith
    have h := Real.log_le_log (by exact_mod_cast (by omega : 0 < N + 1)) hle
    rw [Real.log_pow] at h
    simpa only [Nat.cast_ofNat] using h
  have hstep_int := sum_psi4_le_integral N hN
  have hplanch := h1 hGRH σ ((N + 1 : ℕ) : ℝ) hσ_gt (by exact_mod_cast (by omega : 1 ≤ N + 1))
  have hl2 := (hC σ hσ_gt hσ_le).2
  have hσ_sub : σ - 1 / 2 = 1 / Real.log ((N + 1 : ℕ) : ℝ) := by
    dsimp only [σ]
    ring
  rw [hσ_sub, div_div_eq_mul_div, div_one] at hl2
  have hpsi_bound :
      ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * (ψ₄ j / Real.sqrt j) ^ 2 ≤
        (9 * Real.exp 2 / 4) * (C / Real.pi) * Real.log N := by
    have h12 :
        ∫ x in (1 : ℝ)..((N + 1 : ℕ) : ℝ),
          (ψ₄ ⌊x⌋₊) ^ 2 * x ^ (-(2 * σ + 1)) ≤
        (1 / (2 * Real.pi)) * (C * Real.log ((N + 1 : ℕ) : ℝ)) := by
      refine le_trans hplanch ?_
      exact mul_le_mul_of_nonneg_left hl2 (by positivity)
    have h13 :
        (1 / (2 * Real.pi)) * (C * Real.log ((N + 1 : ℕ) : ℝ)) ≤
          (C / Real.pi) * Real.log N := by
      have hmul := mul_le_mul_of_nonneg_left hlogN1_le (by positivity : (0 : ℝ) ≤ (1 / (2 * Real.pi)) * C)
      calc
        (1 / (2 * Real.pi)) * (C * Real.log ((N + 1 : ℕ) : ℝ))
            = (1 / (2 * Real.pi)) * C * Real.log ((N + 1 : ℕ) : ℝ) := by ring
        _ ≤ (1 / (2 * Real.pi)) * C * (2 * Real.log N) := hmul
        _ = (C / Real.pi) * Real.log N := by
              field_simp [Real.pi_pos.ne']
    exact le_trans hstep_int
      (by
        have h := mul_le_mul_of_nonneg_left (le_trans h12 h13)
          (by positivity : (0 : ℝ) ≤ 9 * Real.exp 2 / 4)
        linarith)
  have hstep1 :
      ∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) *
        (((Real.log j / Real.sqrt j) * ((j.primeCountingMod 4 1 : ℝ) - j.primeCountingMod 4 3)) ^ 2) ≤
      210 * (2 * (∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * (ψ₄ j / Real.sqrt j) ^ 2) +
        2 * C₀ ^ 2 * Real.log N) :=
    le_trans hpi_theta (mul_le_mul_of_nonneg_left htheta_psi (by norm_num))
  have hstep2 :
      210 * (2 * (∑ j ∈ Finset.Icc 2 N, (1 / (j : ℝ)) * (ψ₄ j / Real.sqrt j) ^ 2) +
        2 * C₀ ^ 2 * Real.log N) ≤
      210 * (2 * ((9 * Real.exp 2 / 4) * (C / Real.pi) * Real.log N) +
        2 * C₀ ^ 2 * Real.log N) := by
    refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hpsi_bound (by norm_num)) le_rfl) (by norm_num)
  have hfinal := le_trans hstep1 hstep2
  dsimp only [B]
  linarith

end OMA.R_ChebyshevBias_knapowski_turan_natural_density_false_R1_H1_R1
