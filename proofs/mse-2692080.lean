import OMAStatements.S_mse_2692080

namespace OMA.P_mse_2692080

open OMA.S_mse_2692080

private noncomputable def term (k : ℕ) : ℝ :=
  Real.exp (-((k + 1 : ℕ) : ℝ)) /
    (((k + 1 : ℕ) : ℝ) ^ (k + 1) * Real.sqrt ((k + 1 : ℕ) : ℝ))

private lemma exp_one_div_16_bounds :
    (1064494458917859429563 / 1000000000000000000000 : ℝ) ≤ Real.exp (1 / 16 : ℝ) ∧ Real.exp (1 / 16 : ℝ) ≤ (266123614729464857391 / 250000000000000000000 : ℝ) := by
  have hbd := Real.exp_bound (x := (1 / 16 : ℝ)) (n := 16) (by norm_num) (by norm_num)
  rw [abs_le] at hbd
  have hsum : (∑ m ∈ Finset.range 16, (1 / 16 : ℝ) ^ m / (m.factorial : ℝ)) = (1604880706443526238206603522801 / 1507645899890367707813511168000 : ℝ) := by
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  rw [hsum, show (16 : ℕ).succ = (17 : ℕ) from rfl] at hbd
  have herr2 : |(1 / 16 : ℝ)| ^ 16 * (((17 : ℕ) : ℝ) / ((Nat.factorial 16 : ℝ) * (16 : ℕ))) = (17 / 6175317605950946131204141744128000 : ℝ) := by
    norm_num [Nat.factorial]
  rw [herr2] at hbd
  constructor <;> linarith

private lemma exp1_ge : (135914091422952261767 / 50000000000000000000 : ℝ) ≤ Real.exp 1 := by
  have h16 := exp_one_div_16_bounds.1
  have hpow : ((1064494458917859429563 / 1000000000000000000000 : ℝ)) ^ 16 ≤ (Real.exp (1 / 16 : ℝ)) ^ 16 :=
    pow_le_pow_left₀ (by norm_num) h16 16
  have hexp : (Real.exp (1 / 16 : ℝ)) ^ 16 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hexp] at hpow
  have hnum : (135914091422952261767 / 50000000000000000000 : ℝ) ≤ ((1064494458917859429563 / 1000000000000000000000 : ℝ)) ^ 16 := by norm_num
  linarith

private lemma exp1_le : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := by
  have h16 := exp_one_div_16_bounds.2
  have hpow : (Real.exp (1 / 16 : ℝ)) ^ 16 ≤ ((266123614729464857391 / 250000000000000000000 : ℝ)) ^ 16 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) h16 16
  have hexp : (Real.exp (1 / 16 : ℝ)) ^ 16 = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [hexp] at hpow
  have hnum : ((266123614729464857391 / 250000000000000000000 : ℝ)) ^ 16 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := by norm_num
  linarith

private lemma term_nonneg (k : ℕ) : 0 ≤ term k := by
  unfold term
  positivity

private lemma term_summable : Summable term := by
  refine Summable.of_nonneg_of_le term_nonneg (fun k => ?_)
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1))
  unfold term
  have hexp : Real.exp (-((k + 1 : ℕ) : ℝ)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith [Nat.cast_nonneg (α := ℝ) (k + 1)]
  have hsqrt : (1 : ℝ) ≤ Real.sqrt ((k + 1 : ℕ) : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    have : (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
    linarith
  have hpow : (2 : ℝ) ^ k ≤ ((k + 1 : ℕ) : ℝ) ^ (k + 1) := by
    cases k with
    | zero => norm_num
    | succ m =>
      have h2 : (2 : ℝ) ≤ ((m + 2 : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ m + 2 by omega)
      calc (2 : ℝ) ^ (m + 1) ≤ (2 : ℝ) ^ (m + 2) :=
            pow_le_pow_right₀ (by norm_num) (by omega)
        _ ≤ ((m + 2 : ℕ) : ℝ) ^ (m + 2) := pow_le_pow_left₀ (by norm_num) h2 (m + 2)
  have hden : (2 : ℝ) ^ k ≤ ((k + 1 : ℕ) : ℝ) ^ (k + 1) * Real.sqrt ((k + 1 : ℕ) : ℝ) := by
    nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k]
  calc Real.exp (-((k + 1 : ℕ) : ℝ)) / (((k + 1 : ℕ) : ℝ) ^ (k + 1) * Real.sqrt ((k + 1 : ℕ) : ℝ))
      ≤ 1 / (((k + 1 : ℕ) : ℝ) ^ (k + 1) * Real.sqrt ((k + 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right hexp (by positivity)
    _ ≤ 1 / (2 : ℝ) ^ k := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
    _ = (1 / 2 : ℝ) ^ k := by rw [one_div_pow]

private lemma term_lb_1 : (36787944117144232159 / 100000000000000000000 : ℝ) ≤ term 0 := by
  unfold term
  have he : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := exp1_le
  have h1 : (1 : ℝ) ^ 1 * Real.sqrt (1 : ℝ) ≤ (1 : ℝ) ^ 1 * (1 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hexp : Real.exp (-(1 : ℝ)) = ((Real.exp 1) ^ 1)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hpow : (Real.exp 1) ^ 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 1 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he 1
  have hden : (Real.exp 1) ^ 1 * ((1 : ℝ) ^ 1 * Real.sqrt (1 : ℝ)) ≤
      (271828182845904523539 / 100000000000000000000 : ℝ) ^ 1 * ((1 : ℝ) ^ 1 * (1 : ℝ)) :=
    mul_le_mul hpow h1 (by positivity) (by positivity)
  have hpos : 0 < (Real.exp 1) ^ 1 * ((1 : ℝ) ^ 1 * Real.sqrt (1 : ℝ)) := by positivity
  have hinv : ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 1 * ((1 : ℝ) ^ 1 * (1 : ℝ)))⁻¹ ≤
      ((Real.exp 1) ^ 1 * ((1 : ℝ) ^ 1 * Real.sqrt (1 : ℝ)))⁻¹ :=
    inv_anti₀ hpos hden
  have hrew : Real.exp (-(((0 + 1 : ℕ) : ℝ))) /
      (((0 + 1 : ℕ) : ℝ) ^ (0 + 1) * Real.sqrt (((0 + 1 : ℕ) : ℝ))) =
      ((Real.exp 1) ^ 1 * ((1 : ℝ) ^ 1 * Real.sqrt (1 : ℝ)))⁻¹ := by
    rw [show ((0 + 1 : ℕ) : ℝ) = (1 : ℝ) by norm_num,
        show (0 + 1 : ℕ) = 1 from rfl, hexp, div_eq_mul_inv]
    simp only [mul_inv]
  rw [hrew]
  have hnum : (36787944117144232159 / 100000000000000000000 : ℝ) ≤ ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 1 * ((1 : ℝ) ^ 1 * (1 : ℝ)))⁻¹ := by norm_num
  exact le_trans hnum hinv

private lemma term_lb_2 : (1196206206380136549 / 50000000000000000000 : ℝ) ≤ term 1 := by
  unfold term
  have he : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := exp1_le
  have h1 : (2 : ℝ) ^ 2 * Real.sqrt (2 : ℝ) ≤ (2 : ℝ) ^ 2 * (141421356237309504881 / 100000000000000000000 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hexp : Real.exp (-(2 : ℝ)) = ((Real.exp 1) ^ 2)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hpow : (Real.exp 1) ^ 2 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he 2
  have hden : (Real.exp 1) ^ 2 * ((2 : ℝ) ^ 2 * Real.sqrt (2 : ℝ)) ≤
      (271828182845904523539 / 100000000000000000000 : ℝ) ^ 2 * ((2 : ℝ) ^ 2 * (141421356237309504881 / 100000000000000000000 : ℝ)) :=
    mul_le_mul hpow h1 (by positivity) (by positivity)
  have hpos : 0 < (Real.exp 1) ^ 2 * ((2 : ℝ) ^ 2 * Real.sqrt (2 : ℝ)) := by positivity
  have hinv : ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 2 * ((2 : ℝ) ^ 2 * (141421356237309504881 / 100000000000000000000 : ℝ)))⁻¹ ≤
      ((Real.exp 1) ^ 2 * ((2 : ℝ) ^ 2 * Real.sqrt (2 : ℝ)))⁻¹ :=
    inv_anti₀ hpos hden
  have hrew : Real.exp (-(((1 + 1 : ℕ) : ℝ))) /
      (((1 + 1 : ℕ) : ℝ) ^ (1 + 1) * Real.sqrt (((1 + 1 : ℕ) : ℝ))) =
      ((Real.exp 1) ^ 2 * ((2 : ℝ) ^ 2 * Real.sqrt (2 : ℝ)))⁻¹ := by
    rw [show ((1 + 1 : ℕ) : ℝ) = (2 : ℝ) by norm_num,
        show (1 + 1 : ℕ) = 2 from rfl, hexp, div_eq_mul_inv]
    simp only [mul_inv]
  rw [hrew]
  have hnum : (1196206206380136549 / 50000000000000000000 : ℝ) ≤ ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 2 * ((2 : ℝ) ^ 2 * (141421356237309504881 / 100000000000000000000 : ℝ)))⁻¹ := by norm_num
  exact le_trans hnum hinv

private lemma term_lb_3 : (106461397497587219 / 100000000000000000000 : ℝ) ≤ term 2 := by
  unfold term
  have he : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := exp1_le
  have h1 : (3 : ℝ) ^ 3 * Real.sqrt (3 : ℝ) ≤ (3 : ℝ) ^ 3 * (173205080756887729353 / 100000000000000000000 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hexp : Real.exp (-(3 : ℝ)) = ((Real.exp 1) ^ 3)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hpow : (Real.exp 1) ^ 3 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 3 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he 3
  have hden : (Real.exp 1) ^ 3 * ((3 : ℝ) ^ 3 * Real.sqrt (3 : ℝ)) ≤
      (271828182845904523539 / 100000000000000000000 : ℝ) ^ 3 * ((3 : ℝ) ^ 3 * (173205080756887729353 / 100000000000000000000 : ℝ)) :=
    mul_le_mul hpow h1 (by positivity) (by positivity)
  have hpos : 0 < (Real.exp 1) ^ 3 * ((3 : ℝ) ^ 3 * Real.sqrt (3 : ℝ)) := by positivity
  have hinv : ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 3 * ((3 : ℝ) ^ 3 * (173205080756887729353 / 100000000000000000000 : ℝ)))⁻¹ ≤
      ((Real.exp 1) ^ 3 * ((3 : ℝ) ^ 3 * Real.sqrt (3 : ℝ)))⁻¹ :=
    inv_anti₀ hpos hden
  have hrew : Real.exp (-(((2 + 1 : ℕ) : ℝ))) /
      (((2 + 1 : ℕ) : ℝ) ^ (2 + 1) * Real.sqrt (((2 + 1 : ℕ) : ℝ))) =
      ((Real.exp 1) ^ 3 * ((3 : ℝ) ^ 3 * Real.sqrt (3 : ℝ)))⁻¹ := by
    rw [show ((2 + 1 : ℕ) : ℝ) = (3 : ℝ) by norm_num,
        show (2 + 1 : ℕ) = 3 from rfl, hexp, div_eq_mul_inv]
    simp only [mul_inv]
  rw [hrew]
  have hnum : (106461397497587219 / 100000000000000000000 : ℝ) ≤ ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 3 * ((3 : ℝ) ^ 3 * (173205080756887729353 / 100000000000000000000 : ℝ)))⁻¹ := by norm_num
  exact le_trans hnum hinv

private lemma term_lb_4 : (1788636610227947 / 50000000000000000000 : ℝ) ≤ term 3 := by
  unfold term
  have he : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := exp1_le
  have h1 : (4 : ℝ) ^ 4 * Real.sqrt (4 : ℝ) ≤ (4 : ℝ) ^ 4 * (2 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hexp : Real.exp (-(4 : ℝ)) = ((Real.exp 1) ^ 4)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hpow : (Real.exp 1) ^ 4 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 4 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he 4
  have hden : (Real.exp 1) ^ 4 * ((4 : ℝ) ^ 4 * Real.sqrt (4 : ℝ)) ≤
      (271828182845904523539 / 100000000000000000000 : ℝ) ^ 4 * ((4 : ℝ) ^ 4 * (2 : ℝ)) :=
    mul_le_mul hpow h1 (by positivity) (by positivity)
  have hpos : 0 < (Real.exp 1) ^ 4 * ((4 : ℝ) ^ 4 * Real.sqrt (4 : ℝ)) := by positivity
  have hinv : ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 4 * ((4 : ℝ) ^ 4 * (2 : ℝ)))⁻¹ ≤
      ((Real.exp 1) ^ 4 * ((4 : ℝ) ^ 4 * Real.sqrt (4 : ℝ)))⁻¹ :=
    inv_anti₀ hpos hden
  have hrew : Real.exp (-(((3 + 1 : ℕ) : ℝ))) /
      (((3 + 1 : ℕ) : ℝ) ^ (3 + 1) * Real.sqrt (((3 + 1 : ℕ) : ℝ))) =
      ((Real.exp 1) ^ 4 * ((4 : ℝ) ^ 4 * Real.sqrt (4 : ℝ)))⁻¹ := by
    rw [show ((3 + 1 : ℕ) : ℝ) = (4 : ℝ) by norm_num,
        show (3 + 1 : ℕ) = 4 from rfl, hexp, div_eq_mul_inv]
    simp only [mul_inv]
  rw [hrew]
  have hnum : (1788636610227947 / 50000000000000000000 : ℝ) ≤ ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 4 * ((4 : ℝ) ^ 4 * (2 : ℝ)))⁻¹ := by norm_num
  exact le_trans hnum hinv

private lemma term_lb_5 : (96425648119973 / 100000000000000000000 : ℝ) ≤ term 4 := by
  unfold term
  have he : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := exp1_le
  have h1 : (5 : ℝ) ^ 5 * Real.sqrt (5 : ℝ) ≤ (5 : ℝ) ^ 5 * (223606797749978969641 / 100000000000000000000 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hexp : Real.exp (-(5 : ℝ)) = ((Real.exp 1) ^ 5)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hpow : (Real.exp 1) ^ 5 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 5 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he 5
  have hden : (Real.exp 1) ^ 5 * ((5 : ℝ) ^ 5 * Real.sqrt (5 : ℝ)) ≤
      (271828182845904523539 / 100000000000000000000 : ℝ) ^ 5 * ((5 : ℝ) ^ 5 * (223606797749978969641 / 100000000000000000000 : ℝ)) :=
    mul_le_mul hpow h1 (by positivity) (by positivity)
  have hpos : 0 < (Real.exp 1) ^ 5 * ((5 : ℝ) ^ 5 * Real.sqrt (5 : ℝ)) := by positivity
  have hinv : ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 5 * ((5 : ℝ) ^ 5 * (223606797749978969641 / 100000000000000000000 : ℝ)))⁻¹ ≤
      ((Real.exp 1) ^ 5 * ((5 : ℝ) ^ 5 * Real.sqrt (5 : ℝ)))⁻¹ :=
    inv_anti₀ hpos hden
  have hrew : Real.exp (-(((4 + 1 : ℕ) : ℝ))) /
      (((4 + 1 : ℕ) : ℝ) ^ (4 + 1) * Real.sqrt (((4 + 1 : ℕ) : ℝ))) =
      ((Real.exp 1) ^ 5 * ((5 : ℝ) ^ 5 * Real.sqrt (5 : ℝ)))⁻¹ := by
    rw [show ((4 + 1 : ℕ) : ℝ) = (5 : ℝ) by norm_num,
        show (4 + 1 : ℕ) = 5 from rfl, hexp, div_eq_mul_inv]
    simp only [mul_inv]
  rw [hrew]
  have hnum : (96425648119973 / 100000000000000000000 : ℝ) ≤ ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 5 * ((5 : ℝ) ^ 5 * (223606797749978969641 / 100000000000000000000 : ℝ)))⁻¹ := by norm_num
  exact le_trans hnum hinv

private lemma term_lb_6 : (271119025047 / 12500000000000000000 : ℝ) ≤ term 5 := by
  unfold term
  have he : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := exp1_le
  have h1 : (6 : ℝ) ^ 6 * Real.sqrt (6 : ℝ) ≤ (6 : ℝ) ^ 6 * (12247448713915890491 / 5000000000000000000 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hexp : Real.exp (-(6 : ℝ)) = ((Real.exp 1) ^ 6)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hpow : (Real.exp 1) ^ 6 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 6 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he 6
  have hden : (Real.exp 1) ^ 6 * ((6 : ℝ) ^ 6 * Real.sqrt (6 : ℝ)) ≤
      (271828182845904523539 / 100000000000000000000 : ℝ) ^ 6 * ((6 : ℝ) ^ 6 * (12247448713915890491 / 5000000000000000000 : ℝ)) :=
    mul_le_mul hpow h1 (by positivity) (by positivity)
  have hpos : 0 < (Real.exp 1) ^ 6 * ((6 : ℝ) ^ 6 * Real.sqrt (6 : ℝ)) := by positivity
  have hinv : ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 6 * ((6 : ℝ) ^ 6 * (12247448713915890491 / 5000000000000000000 : ℝ)))⁻¹ ≤
      ((Real.exp 1) ^ 6 * ((6 : ℝ) ^ 6 * Real.sqrt (6 : ℝ)))⁻¹ :=
    inv_anti₀ hpos hden
  have hrew : Real.exp (-(((5 + 1 : ℕ) : ℝ))) /
      (((5 + 1 : ℕ) : ℝ) ^ (5 + 1) * Real.sqrt (((5 + 1 : ℕ) : ℝ))) =
      ((Real.exp 1) ^ 6 * ((6 : ℝ) ^ 6 * Real.sqrt (6 : ℝ)))⁻¹ := by
    rw [show ((5 + 1 : ℕ) : ℝ) = (6 : ℝ) by norm_num,
        show (5 + 1 : ℕ) = 6 from rfl, hexp, div_eq_mul_inv]
    simp only [mul_inv]
  rw [hrew]
  have hnum : (271119025047 / 12500000000000000000 : ℝ) ≤ ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 6 * ((6 : ℝ) ^ 6 * (12247448713915890491 / 5000000000000000000 : ℝ)))⁻¹ := by norm_num
  exact le_trans hnum hinv

private lemma term_lb_7 : (4185075783 / 10000000000000000000 : ℝ) ≤ term 6 := by
  unfold term
  have he : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := exp1_le
  have h1 : (7 : ℝ) ^ 7 * Real.sqrt (7 : ℝ) ≤ (7 : ℝ) ^ 7 * (529150262213 / 200000000000 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hexp : Real.exp (-(7 : ℝ)) = ((Real.exp 1) ^ 7)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hpow : (Real.exp 1) ^ 7 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 7 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he 7
  have hden : (Real.exp 1) ^ 7 * ((7 : ℝ) ^ 7 * Real.sqrt (7 : ℝ)) ≤
      (271828182845904523539 / 100000000000000000000 : ℝ) ^ 7 * ((7 : ℝ) ^ 7 * (529150262213 / 200000000000 : ℝ)) :=
    mul_le_mul hpow h1 (by positivity) (by positivity)
  have hpos : 0 < (Real.exp 1) ^ 7 * ((7 : ℝ) ^ 7 * Real.sqrt (7 : ℝ)) := by positivity
  have hinv : ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 7 * ((7 : ℝ) ^ 7 * (529150262213 / 200000000000 : ℝ)))⁻¹ ≤
      ((Real.exp 1) ^ 7 * ((7 : ℝ) ^ 7 * Real.sqrt (7 : ℝ)))⁻¹ :=
    inv_anti₀ hpos hden
  have hrew : Real.exp (-(((6 + 1 : ℕ) : ℝ))) /
      (((6 + 1 : ℕ) : ℝ) ^ (6 + 1) * Real.sqrt (((6 + 1 : ℕ) : ℝ))) =
      ((Real.exp 1) ^ 7 * ((7 : ℝ) ^ 7 * Real.sqrt (7 : ℝ)))⁻¹ := by
    rw [show ((6 + 1 : ℕ) : ℝ) = (7 : ℝ) by norm_num,
        show (6 + 1 : ℕ) = 7 from rfl, hexp, div_eq_mul_inv]
    simp only [mul_inv]
  rw [hrew]
  have hnum : (4185075783 / 10000000000000000000 : ℝ) ≤ ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 7 * ((7 : ℝ) ^ 7 * (529150262213 / 200000000000 : ℝ)))⁻¹ := by norm_num
  exact le_trans hnum hinv

private lemma term_lb_8 : (706934627 / 100000000000000000000 : ℝ) ≤ term 7 := by
  unfold term
  have he : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := exp1_le
  have h1 : (8 : ℝ) ^ 8 * Real.sqrt (8 : ℝ) ≤ (8 : ℝ) ^ 8 * (2828427124747 / 1000000000000 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hexp : Real.exp (-(8 : ℝ)) = ((Real.exp 1) ^ 8)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hpow : (Real.exp 1) ^ 8 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 8 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he 8
  have hden : (Real.exp 1) ^ 8 * ((8 : ℝ) ^ 8 * Real.sqrt (8 : ℝ)) ≤
      (271828182845904523539 / 100000000000000000000 : ℝ) ^ 8 * ((8 : ℝ) ^ 8 * (2828427124747 / 1000000000000 : ℝ)) :=
    mul_le_mul hpow h1 (by positivity) (by positivity)
  have hpos : 0 < (Real.exp 1) ^ 8 * ((8 : ℝ) ^ 8 * Real.sqrt (8 : ℝ)) := by positivity
  have hinv : ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 8 * ((8 : ℝ) ^ 8 * (2828427124747 / 1000000000000 : ℝ)))⁻¹ ≤
      ((Real.exp 1) ^ 8 * ((8 : ℝ) ^ 8 * Real.sqrt (8 : ℝ)))⁻¹ :=
    inv_anti₀ hpos hden
  have hrew : Real.exp (-(((7 + 1 : ℕ) : ℝ))) /
      (((7 + 1 : ℕ) : ℝ) ^ (7 + 1) * Real.sqrt (((7 + 1 : ℕ) : ℝ))) =
      ((Real.exp 1) ^ 8 * ((8 : ℝ) ^ 8 * Real.sqrt (8 : ℝ)))⁻¹ := by
    rw [show ((7 + 1 : ℕ) : ℝ) = (8 : ℝ) by norm_num,
        show (7 + 1 : ℕ) = 8 from rfl, hexp, div_eq_mul_inv]
    simp only [mul_inv]
  rw [hrew]
  have hnum : (706934627 / 100000000000000000000 : ℝ) ≤ ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 8 * ((8 : ℝ) ^ 8 * (2828427124747 / 1000000000000 : ℝ)))⁻¹ := by norm_num
  exact le_trans hnum hinv

private lemma term_lb_9 : (424723 / 4000000000000000000 : ℝ) ≤ term 8 := by
  unfold term
  have he : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := exp1_le
  have h1 : (9 : ℝ) ^ 9 * Real.sqrt (9 : ℝ) ≤ (9 : ℝ) ^ 9 * (3 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hexp : Real.exp (-(9 : ℝ)) = ((Real.exp 1) ^ 9)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hpow : (Real.exp 1) ^ 9 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 9 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he 9
  have hden : (Real.exp 1) ^ 9 * ((9 : ℝ) ^ 9 * Real.sqrt (9 : ℝ)) ≤
      (271828182845904523539 / 100000000000000000000 : ℝ) ^ 9 * ((9 : ℝ) ^ 9 * (3 : ℝ)) :=
    mul_le_mul hpow h1 (by positivity) (by positivity)
  have hpos : 0 < (Real.exp 1) ^ 9 * ((9 : ℝ) ^ 9 * Real.sqrt (9 : ℝ)) := by positivity
  have hinv : ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 9 * ((9 : ℝ) ^ 9 * (3 : ℝ)))⁻¹ ≤
      ((Real.exp 1) ^ 9 * ((9 : ℝ) ^ 9 * Real.sqrt (9 : ℝ)))⁻¹ :=
    inv_anti₀ hpos hden
  have hrew : Real.exp (-(((8 + 1 : ℕ) : ℝ))) /
      (((8 + 1 : ℕ) : ℝ) ^ (8 + 1) * Real.sqrt (((8 + 1 : ℕ) : ℝ))) =
      ((Real.exp 1) ^ 9 * ((9 : ℝ) ^ 9 * Real.sqrt (9 : ℝ)))⁻¹ := by
    rw [show ((8 + 1 : ℕ) : ℝ) = (9 : ℝ) by norm_num,
        show (8 + 1 : ℕ) = 9 from rfl, hexp, div_eq_mul_inv]
    simp only [mul_inv]
  rw [hrew]
  have hnum : (424723 / 4000000000000000000 : ℝ) ≤ ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 9 * ((9 : ℝ) ^ 9 * (3 : ℝ)))⁻¹ := by norm_num
  exact le_trans hnum hinv

private lemma term_lb_10 : (143567 / 100000000000000000000 : ℝ) ≤ term 9 := by
  unfold term
  have he : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := exp1_le
  have h1 : (10 : ℝ) ^ 10 * Real.sqrt (10 : ℝ) ≤ (10 : ℝ) ^ 10 * (3162277660169 / 1000000000000 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hexp : Real.exp (-(10 : ℝ)) = ((Real.exp 1) ^ 10)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hpow : (Real.exp 1) ^ 10 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 10 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he 10
  have hden : (Real.exp 1) ^ 10 * ((10 : ℝ) ^ 10 * Real.sqrt (10 : ℝ)) ≤
      (271828182845904523539 / 100000000000000000000 : ℝ) ^ 10 * ((10 : ℝ) ^ 10 * (3162277660169 / 1000000000000 : ℝ)) :=
    mul_le_mul hpow h1 (by positivity) (by positivity)
  have hpos : 0 < (Real.exp 1) ^ 10 * ((10 : ℝ) ^ 10 * Real.sqrt (10 : ℝ)) := by positivity
  have hinv : ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 10 * ((10 : ℝ) ^ 10 * (3162277660169 / 1000000000000 : ℝ)))⁻¹ ≤
      ((Real.exp 1) ^ 10 * ((10 : ℝ) ^ 10 * Real.sqrt (10 : ℝ)))⁻¹ :=
    inv_anti₀ hpos hden
  have hrew : Real.exp (-(((9 + 1 : ℕ) : ℝ))) /
      (((9 + 1 : ℕ) : ℝ) ^ (9 + 1) * Real.sqrt (((9 + 1 : ℕ) : ℝ))) =
      ((Real.exp 1) ^ 10 * ((10 : ℝ) ^ 10 * Real.sqrt (10 : ℝ)))⁻¹ := by
    rw [show ((9 + 1 : ℕ) : ℝ) = (10 : ℝ) by norm_num,
        show (9 + 1 : ℕ) = 10 from rfl, hexp, div_eq_mul_inv]
    simp only [mul_inv]
  rw [hrew]
  have hnum : (143567 / 100000000000000000000 : ℝ) ≤ ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 10 * ((10 : ℝ) ^ 10 * (3162277660169 / 1000000000000 : ℝ)))⁻¹ := by norm_num
  exact le_trans hnum hinv

private lemma term_lb_11 : (353 / 20000000000000000000 : ℝ) ≤ term 10 := by
  unfold term
  have he : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := exp1_le
  have h1 : (11 : ℝ) ^ 11 * Real.sqrt (11 : ℝ) ≤ (11 : ℝ) ^ 11 * (26533 / 8000 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hexp : Real.exp (-(11 : ℝ)) = ((Real.exp 1) ^ 11)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hpow : (Real.exp 1) ^ 11 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 11 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he 11
  have hden : (Real.exp 1) ^ 11 * ((11 : ℝ) ^ 11 * Real.sqrt (11 : ℝ)) ≤
      (271828182845904523539 / 100000000000000000000 : ℝ) ^ 11 * ((11 : ℝ) ^ 11 * (26533 / 8000 : ℝ)) :=
    mul_le_mul hpow h1 (by positivity) (by positivity)
  have hpos : 0 < (Real.exp 1) ^ 11 * ((11 : ℝ) ^ 11 * Real.sqrt (11 : ℝ)) := by positivity
  have hinv : ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 11 * ((11 : ℝ) ^ 11 * (26533 / 8000 : ℝ)))⁻¹ ≤
      ((Real.exp 1) ^ 11 * ((11 : ℝ) ^ 11 * Real.sqrt (11 : ℝ)))⁻¹ :=
    inv_anti₀ hpos hden
  have hrew : Real.exp (-(((10 + 1 : ℕ) : ℝ))) /
      (((10 + 1 : ℕ) : ℝ) ^ (10 + 1) * Real.sqrt (((10 + 1 : ℕ) : ℝ))) =
      ((Real.exp 1) ^ 11 * ((11 : ℝ) ^ 11 * Real.sqrt (11 : ℝ)))⁻¹ := by
    rw [show ((10 + 1 : ℕ) : ℝ) = (11 : ℝ) by norm_num,
        show (10 + 1 : ℕ) = 11 from rfl, hexp, div_eq_mul_inv]
    simp only [mul_inv]
  rw [hrew]
  have hnum : (353 / 20000000000000000000 : ℝ) ≤ ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 11 * ((11 : ℝ) ^ 11 * (26533 / 8000 : ℝ)))⁻¹ := by norm_num
  exact le_trans hnum hinv

private lemma term_lb_12 : (19 / 100000000000000000000 : ℝ) ≤ term 11 := by
  unfold term
  have he : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := exp1_le
  have h1 : (12 : ℝ) ^ 12 * Real.sqrt (12 : ℝ) ≤ (12 : ℝ) ^ 12 * (1732051 / 500000 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hexp : Real.exp (-(12 : ℝ)) = ((Real.exp 1) ^ 12)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hpow : (Real.exp 1) ^ 12 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 12 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he 12
  have hden : (Real.exp 1) ^ 12 * ((12 : ℝ) ^ 12 * Real.sqrt (12 : ℝ)) ≤
      (271828182845904523539 / 100000000000000000000 : ℝ) ^ 12 * ((12 : ℝ) ^ 12 * (1732051 / 500000 : ℝ)) :=
    mul_le_mul hpow h1 (by positivity) (by positivity)
  have hpos : 0 < (Real.exp 1) ^ 12 * ((12 : ℝ) ^ 12 * Real.sqrt (12 : ℝ)) := by positivity
  have hinv : ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 12 * ((12 : ℝ) ^ 12 * (1732051 / 500000 : ℝ)))⁻¹ ≤
      ((Real.exp 1) ^ 12 * ((12 : ℝ) ^ 12 * Real.sqrt (12 : ℝ)))⁻¹ :=
    inv_anti₀ hpos hden
  have hrew : Real.exp (-(((11 + 1 : ℕ) : ℝ))) /
      (((11 + 1 : ℕ) : ℝ) ^ (11 + 1) * Real.sqrt (((11 + 1 : ℕ) : ℝ))) =
      ((Real.exp 1) ^ 12 * ((12 : ℝ) ^ 12 * Real.sqrt (12 : ℝ)))⁻¹ := by
    rw [show ((11 + 1 : ℕ) : ℝ) = (12 : ℝ) by norm_num,
        show (11 + 1 : ℕ) = 12 from rfl, hexp, div_eq_mul_inv]
    simp only [mul_inv]
  rw [hrew]
  have hnum : (19 / 100000000000000000000 : ℝ) ≤ ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 12 * ((12 : ℝ) ^ 12 * (1732051 / 500000 : ℝ)))⁻¹ := by norm_num
  exact le_trans hnum hinv

private lemma term_lb_13 : (0 : ℝ) ≤ term 12 := by
  unfold term
  have he : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := exp1_le
  have h1 : (13 : ℝ) ^ 13 * Real.sqrt (13 : ℝ) ≤ (13 : ℝ) ^ 13 * (225347 / 62500 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hexp : Real.exp (-(13 : ℝ)) = ((Real.exp 1) ^ 13)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hpow : (Real.exp 1) ^ 13 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 13 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he 13
  have hden : (Real.exp 1) ^ 13 * ((13 : ℝ) ^ 13 * Real.sqrt (13 : ℝ)) ≤
      (271828182845904523539 / 100000000000000000000 : ℝ) ^ 13 * ((13 : ℝ) ^ 13 * (225347 / 62500 : ℝ)) :=
    mul_le_mul hpow h1 (by positivity) (by positivity)
  have hpos : 0 < (Real.exp 1) ^ 13 * ((13 : ℝ) ^ 13 * Real.sqrt (13 : ℝ)) := by positivity
  have hinv : ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 13 * ((13 : ℝ) ^ 13 * (225347 / 62500 : ℝ)))⁻¹ ≤
      ((Real.exp 1) ^ 13 * ((13 : ℝ) ^ 13 * Real.sqrt (13 : ℝ)))⁻¹ :=
    inv_anti₀ hpos hden
  have hrew : Real.exp (-(((12 + 1 : ℕ) : ℝ))) /
      (((12 + 1 : ℕ) : ℝ) ^ (12 + 1) * Real.sqrt (((12 + 1 : ℕ) : ℝ))) =
      ((Real.exp 1) ^ 13 * ((13 : ℝ) ^ 13 * Real.sqrt (13 : ℝ)))⁻¹ := by
    rw [show ((12 + 1 : ℕ) : ℝ) = (13 : ℝ) by norm_num,
        show (12 + 1 : ℕ) = 13 from rfl, hexp, div_eq_mul_inv]
    simp only [mul_inv]
  rw [hrew]
  have hnum : (0 : ℝ) ≤ ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 13 * ((13 : ℝ) ^ 13 * (225347 / 62500 : ℝ)))⁻¹ := by norm_num
  exact le_trans hnum hinv

private lemma term_lb_14 : (0 : ℝ) ≤ term 13 := by
  unfold term
  have he : Real.exp 1 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) := exp1_le
  have h1 : (14 : ℝ) ^ 14 * Real.sqrt (14 : ℝ) ≤ (14 : ℝ) ^ 14 * (1870829 / 500000 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hexp : Real.exp (-(14 : ℝ)) = ((Real.exp 1) ^ 14)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]; norm_num
  have hpow : (Real.exp 1) ^ 14 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 14 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) he 14
  have hden : (Real.exp 1) ^ 14 * ((14 : ℝ) ^ 14 * Real.sqrt (14 : ℝ)) ≤
      (271828182845904523539 / 100000000000000000000 : ℝ) ^ 14 * ((14 : ℝ) ^ 14 * (1870829 / 500000 : ℝ)) :=
    mul_le_mul hpow h1 (by positivity) (by positivity)
  have hpos : 0 < (Real.exp 1) ^ 14 * ((14 : ℝ) ^ 14 * Real.sqrt (14 : ℝ)) := by positivity
  have hinv : ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 14 * ((14 : ℝ) ^ 14 * (1870829 / 500000 : ℝ)))⁻¹ ≤
      ((Real.exp 1) ^ 14 * ((14 : ℝ) ^ 14 * Real.sqrt (14 : ℝ)))⁻¹ :=
    inv_anti₀ hpos hden
  have hrew : Real.exp (-(((13 + 1 : ℕ) : ℝ))) /
      (((13 + 1 : ℕ) : ℝ) ^ (13 + 1) * Real.sqrt (((13 + 1 : ℕ) : ℝ))) =
      ((Real.exp 1) ^ 14 * ((14 : ℝ) ^ 14 * Real.sqrt (14 : ℝ)))⁻¹ := by
    rw [show ((13 + 1 : ℕ) : ℝ) = (14 : ℝ) by norm_num,
        show (13 + 1 : ℕ) = 14 from rfl, hexp, div_eq_mul_inv]
    simp only [mul_inv]
  rw [hrew]
  have hnum : (0 : ℝ) ≤ ((271828182845904523539 / 100000000000000000000 : ℝ) ^ 14 * ((14 : ℝ) ^ 14 * (1870829 / 500000 : ℝ)))⁻¹ := by norm_num
  exact le_trans hnum hinv

private lemma rhs_upper :
    (-92 - 95 * Real.exp 1 + 86 * (Real.exp 1) ^ 2) /
      (2 * (130 - 4 * Real.exp 1 + 33 * (Real.exp 1) ^ 2)) ≤ (1426110254022133110992043451008932018634403 / 3629657239508752765534043999272357475022148 : ℝ) := by
  have hlo := exp1_ge
  have hhi := exp1_le
  have hsq_lo : (135914091422952261767 / 50000000000000000000 : ℝ) ^ 2 ≤ (Real.exp 1) ^ 2 :=
    pow_le_pow_left₀ (by norm_num) hlo 2
  have hsq_hi : (Real.exp 1) ^ 2 ≤ (271828182845904523539 / 100000000000000000000 : ℝ) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) hhi 2
  have hnum_le : -92 - 95 * Real.exp 1 + 86 * (Real.exp 1) ^ 2 ≤ (1426110254022133110992043451008932018634403 / 5000000000000000000000000000000000000000 : ℝ) := by
    linarith
  have hden_ge : (907414309877188191383510999818089368755537 / 1250000000000000000000000000000000000000 : ℝ) ≤ 2 * (130 - 4 * Real.exp 1 + 33 * (Real.exp 1) ^ 2) := by
    linarith
  have hnum_pos : 0 ≤ (1426110254022133110992043451008932018634403 / 5000000000000000000000000000000000000000 : ℝ) := by norm_num
  have hden_pos : 0 < (907414309877188191383510999818089368755537 / 1250000000000000000000000000000000000000 : ℝ) := by norm_num
  have hdiv : (-92 - 95 * Real.exp 1 + 86 * (Real.exp 1) ^ 2) /
        (2 * (130 - 4 * Real.exp 1 + 33 * (Real.exp 1) ^ 2)) ≤
      (1426110254022133110992043451008932018634403 / 5000000000000000000000000000000000000000 : ℝ) / (907414309877188191383510999818089368755537 / 1250000000000000000000000000000000000000 : ℝ) :=
    div_le_div₀ hnum_pos hnum_le hden_pos hden_ge
  have heq : (1426110254022133110992043451008932018634403 / 5000000000000000000000000000000000000000 : ℝ) / (907414309877188191383510999818089368755537 / 1250000000000000000000000000000000000000 : ℝ) = (1426110254022133110992043451008932018634403 / 3629657239508752765534043999272357475022148 : ℝ) := by norm_num
  linarith

private theorem main_disproof : ¬ (type_of% @OMA.S_mse_2692080.main) := by
  intro hmain
  have hsum_le : (∑ k ∈ Finset.range 14, term k) ≤ ∑' k : ℕ, term k :=
    term_summable.sum_le_tsum (Finset.range 14) (fun k _ => term_nonneg k)
  have h14 : (19645246918895662301 / 50000000000000000000 : ℝ) ≤ ∑ k ∈ Finset.range 14, term k := by
    rw [show Finset.range 14 = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13} from by decide]
    simp only [Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton, Finset.sum_singleton,
      OfNat.zero_ne_ofNat, OfNat.one_ne_ofNat, Nat.reduceEqDiff, or_self, not_false_eq_true]
    have h1 := term_lb_1; have h2 := term_lb_2; have h3 := term_lb_3; have h4 := term_lb_4
    have h5 := term_lb_5; have h6 := term_lb_6; have h7 := term_lb_7; have h8 := term_lb_8
    have h9 := term_lb_9; have h10 := term_lb_10; have h11 := term_lb_11; have h12 := term_lb_12
    have h13 := term_lb_13; have h14' := term_lb_14
    linarith
  have hrhs := rhs_upper
  have hgt : (1426110254022133110992043451008932018634403 / 3629657239508752765534043999272357475022148 : ℝ) < (19645246918895662301 / 50000000000000000000 : ℝ) := by norm_num
  change (∑' k : ℕ, term k) = _ at hmain
  linarith

end OMA.P_mse_2692080

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_2692080.main) :=
  OMA.P_mse_2692080.main_disproof
