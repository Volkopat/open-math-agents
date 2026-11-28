import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_61
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.PSeries

/-!
# Koksma's metric theorem for a fixed real base `α > 1`

For a fixed real `α > 1` the sequence `(ξ * α ^ (n + 1))` is uniformly distributed modulo one
for Lebesgue-almost every real `ξ`.  This is the "almost every" variant of Problem 10.61 of
Bugeaud's collection, and it is exactly Koksma's metric theorem [Kok35].

The proof is the textbook three step argument.

* Weyl's criterion: a sequence is equidistributed modulo one as soon as every nonzero
  exponential sum `(1/N) ∑_{n<N} exp (2 π i h s n)` tends to `0`.
* An `L²` bound on a fixed interval `[-T, T]`, obtained by expanding the square of the
  exponential sum and estimating the off-diagonal terms with
  `|α ^ (j+1) - α ^ (i+1)| ≥ ((α - 1) / α) α ^ (j+1)`.
* Borel–Cantelli along the lacunary sequence `N = (k+1) ^ 2`, followed by an interpolation
  from the squares to all `N`.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace OMA

noncomputable abbrev p := Real.pi
noncomputable abbrev w := 2 * p
noncomputable abbrev g (α : ℝ) := (α - 1) / α
noncomputable abbrev f (α : ℝ) := α / (α - 1)

/-- The angle `2 * π * h * ξ * α ^ (n + 1)`. -/
noncomputable def ang (α : ℝ) (h : ℤ) (ξ : ℝ) (n : ℕ) : ℝ :=
  w * (h : ℝ) * (ξ * α ^ (n + 1))

/-- The exponential `exp (2 π i h ξ α ^ (n + 1))`. -/
noncomputable def ez (α : ℝ) (h : ℤ) (ξ : ℝ) (n : ℕ) : ℂ :=
  Complex.exp (((ang α h ξ n : ℝ) : ℂ) * Complex.I)

/-- The unnormalised exponential sum `∑_{n < N} exp (2 π i h ξ α ^ (n + 1))`. -/
noncomputable def psum (α : ℝ) (h : ℤ) (ξ : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N, ez α h ξ n

/-- The normalised exponential sum `N⁻¹ ∑_{n < N} exp (2 π i h ξ α ^ (n + 1))`. -/
noncomputable def nsum (α : ℝ) (h : ℤ) (ξ : ℝ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * psum α h ξ N

lemma ang_sub (α : ℝ) (h : ℤ) (ξ : ℝ) (i j : ℕ) :
    ang α h ξ i - ang α h ξ j
      = (w * (h : ℝ) * (α ^ (i + 1) - α ^ (j + 1))) * ξ := by
  simp only [ang]; ring

lemma norm_ez (α : ℝ) (h : ℤ) (ξ : ℝ) (n : ℕ) : ‖ez α h ξ n‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

lemma conj_ez (α : ℝ) (h : ℤ) (ξ : ℝ) (j : ℕ) :
    (starRingEnd ℂ) (ez α h ξ j)
      = Complex.exp (((-(ang α h ξ j) : ℝ) : ℂ) * Complex.I) := by
  rw [ez, (Complex.exp_conj (((ang α h ξ j : ℝ) : ℂ) * Complex.I)).symm]
  congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

lemma ez_mul_conj (α : ℝ) (h : ℤ) (ξ : ℝ) (i j : ℕ) :
    ez α h ξ i * (starRingEnd ℂ) (ez α h ξ j)
      = Complex.exp ((((ang α h ξ i - ang α h ξ j) : ℝ) : ℂ) * Complex.I) := by
  rw [conj_ez, ez, ← Complex.exp_add]
  congr 1
  rw [Complex.ofReal_sub]
  push_cast
  ring

/-- Decomposing the squared modulus of the exponential sum into a double sum of cosines. -/
lemma normSq_psum (α : ℝ) (h : ℤ) (ξ : ℝ) (N : ℕ) :
    ‖psum α h ξ N‖ ^ 2
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          Real.cos (ang α h ξ i - ang α h ξ j) := by
  have hconj : (starRingEnd ℂ) (psum α h ξ N)
      = ∑ j ∈ Finset.range N, (starRingEnd ℂ) (ez α h ξ j) := by
    rw [psum]
    exact map_sum (starRingEnd ℂ) (fun n => ez α h ξ n) (Finset.range N)
  have hmul : psum α h ξ N * (starRingEnd ℂ) (psum α h ξ N)
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          ez α h ξ i * (starRingEnd ℂ) (ez α h ξ j) := by
    rw [hconj, psum, Finset.sum_mul_sum]
  calc ‖psum α h ξ N‖ ^ 2
      = Complex.normSq (psum α h ξ N) := (Complex.normSq_eq_norm_sq _).symm
    _ = (psum α h ξ N * (starRingEnd ℂ) (psum α h ξ N)).re := by
        rw [Complex.mul_conj, Complex.ofReal_re]
    _ = (∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          ez α h ξ i * (starRingEnd ℂ) (ez α h ξ j)).re := by rw [hmul]
    _ = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          Real.cos (ang α h ξ i - ang α h ξ j) := by
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Complex.re_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [ez_mul_conj, Complex.exp_ofReal_mul_I_re]

lemma intervalIntegrable_cos_ang (α : ℝ) (h : ℤ) (i j : ℕ) (a b : ℝ) :
    IntervalIntegrable (fun ξ : ℝ => Real.cos (ang α h ξ i - ang α h ξ j)) volume a b := by
  apply Continuous.intervalIntegrable
  simp only [ang]
  fun_prop

/-- Interchanging the finite double sum with the integral. -/
lemma integral_normSq_psum (α : ℝ) (h : ℤ) (T : ℝ) (N : ℕ) :
    ∫ ξ in (-T)..T, ‖psum α h ξ N‖ ^ 2
      = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
          ∫ ξ in (-T)..T, Real.cos (ang α h ξ i - ang α h ξ j) := by
  rw [show (fun ξ : ℝ => ‖psum α h ξ N‖ ^ 2)
        = (fun ξ : ℝ => ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            Real.cos (ang α h ξ i - ang α h ξ j)) from funext (fun ξ => normSq_psum α h ξ N)]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    exact fun j _ => intervalIntegrable_cos_ang α h i j (-T) T
  · exact fun i _ => by
      apply Continuous.intervalIntegrable
      simp only [ang]
      fun_prop

/-- `∫ x in a..b, cos (c * x) = (sin (c * b) - sin (c * a)) / c` for `c ≠ 0`. -/
lemma integral_cos_mul (c a b : ℝ) (hc : c ≠ 0) :
    ∫ x in a..b, Real.cos (c * x) = (Real.sin (c * b) - Real.sin (c * a)) / c := by
  rw [intervalIntegral.integral_comp_mul_left (f := Real.cos) hc,
    integral_cos]
  simp only [smul_eq_mul]
  field_simp

/-- `|∫ x in (-T)..T, cos (c * x)| ≤ 2 / |c|` for `c ≠ 0` and `0 ≤ T`. -/
lemma abs_integral_cos_mul_le (c T : ℝ) (hc : c ≠ 0) :
    |∫ x in (-T)..T, Real.cos (c * x)| ≤ 2 / |c| := by
  have hsin : Real.sin (c * T) - Real.sin (c * -T) = 2 * Real.sin (c * T) := by
    rw [mul_neg, Real.sin_neg]; ring
  rw [integral_cos_mul c (-T) T hc, hsin, div_eq_mul_inv, div_eq_mul_inv,
    abs_mul, abs_mul, abs_inv]
  have h2 : |(2:ℝ)| = 2 := by norm_num
  rw [h2]
  have hb : |Real.sin (c * T)| ≤ 1 := Real.abs_sin_le_one _
  have hnn : (0:ℝ) ≤ |c|⁻¹ := by positivity
  have hm := mul_le_mul_of_nonneg_right hb hnn
  calc 2 * |Real.sin (c * T)| * |c|⁻¹ = 2 * (|Real.sin (c * T)| * |c|⁻¹) := by ring
    _ ≤ 2 * (1 * |c|⁻¹) := by linarith
    _ = 2 * |c|⁻¹ := by ring

/-- `α ^ j - α ^ i ≥ ((α - 1) / α) * α ^ j` for `i < j` and `α > 1`. -/
lemma pow_sub_pow_ge {α : ℝ} (hα : 1 < α) {i j : ℕ} (hij : i < j) :
    g α * α ^ j ≤ α ^ j - α ^ i := by
  have hi : i ≤ j - 1 := by omega
  have hp : α ^ i ≤ α ^ (j - 1) := pow_le_pow_right₀ (le_of_lt hα) hi
  have hj : α ^ j = α ^ (j - 1) * α := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ j)]
  rw [hj]
  field_simp
  nlinarith

noncomputable abbrev r (α : ℝ) := Real.sqrt α⁻¹

/-- `α⁻¹ ^ max i j ≤ (√α⁻¹) ^ i * (√α⁻¹) ^ j`. -/
lemma pow_inv_max_le {α : ℝ} (hα : 1 < α) (i j : ℕ) :
    α⁻¹ ^ max i j ≤ (r α) ^ i * (r α) ^ j := by
  have hinv0 : (0:ℝ) < α⁻¹ := by positivity
  have hinv1 : α⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα
  set s := r α with hs
  have hs0 : (0:ℝ) ≤ s := Real.sqrt_nonneg _
  have hs2 : s * s = α⁻¹ := Real.mul_self_sqrt hinv0.le
  have hs1 : s < 1 := by nlinarith
  have hm : α⁻¹ ^ max i j = s ^ (max i j) * s ^ (max i j) := by
    rw [← hs2, mul_pow]
  rw [hm, ← pow_add, ← pow_add]
  exact pow_le_pow_of_le_one hs0 hs1.le (by omega)

/-- `1 / |α ^ (i+1) - α ^ (j+1)|` is summable with the geometric-like weight `(√α⁻¹) ^ (i+j)`. -/
lemma one_div_abs_sub_pow_le {α : ℝ} (hα : 1 < α) (i j : ℕ) :
    (1 : ℝ) / |α ^ (i + 1) - α ^ (j + 1)|
      ≤ f α * α⁻¹ * ((r α) ^ i * (r α) ^ j) := by
  have hα0 : (0:ℝ) < α := by linarith
  have hcpos : (0:ℝ) < g α := div_pos (by linarith) hα0
  by_cases hij : i = j
  · subst j
    rw [sub_self, abs_zero, div_zero]
    positivity
  have hlt : min i j < max i j := by omega
  have hgap : g α * α ^ (max i j + 1)
      ≤ α ^ (max i j + 1) - α ^ (min i j + 1) :=
    pow_sub_pow_ge hα (Nat.succ_lt_succ hlt)
  have hdiff : 0 < α ^ (max i j + 1) - α ^ (min i j + 1) :=
    lt_of_lt_of_le (mul_pos hcpos (pow_pos hα0 _)) hgap
  have habs : |α ^ (i + 1) - α ^ (j + 1)|
      = α ^ (max i j + 1) - α ^ (min i j + 1) := by
    rcases le_total i j with hij | hji
    · rw [max_eq_right hij, min_eq_left hij, abs_of_nonpos]
      · ring
      · exact sub_nonpos.mpr (pow_le_pow_right₀ (le_of_lt hα) (by omega))
    · rw [max_eq_left hji, min_eq_right hji, abs_of_nonneg]
      · exact sub_nonneg.mpr (pow_le_pow_right₀ (le_of_lt hα) (by omega))
  rw [habs]
  have hrecip := one_div_le_one_div_of_le (mul_pos hcpos (pow_pos hα0 _)) hgap
  have hfactor : 1 / (g α * α ^ (max i j + 1))
      = f α * α⁻¹ ^ (max i j + 1) := by
    rw [inv_pow]
    field_simp
  have hroot := pow_inv_max_le hα i j
  have hbound : α⁻¹ ^ (max i j + 1)
      ≤ α⁻¹ * ((r α) ^ i * (r α) ^ j) := by
    calc
      α⁻¹ ^ (max i j + 1) = α⁻¹ * α⁻¹ ^ max i j := by rw [pow_succ']
      _ ≤ α⁻¹ * ((r α) ^ i * (r α) ^ j) :=
        mul_le_mul_of_nonneg_left hroot (by positivity)
  calc
    1 / (α ^ (max i j + 1) - α ^ (min i j + 1))
        ≤ 1 / (g α * α ^ (max i j + 1)) := hrecip
    _ = f α * α⁻¹ ^ (max i j + 1) := hfactor
    _ ≤ f α * (α⁻¹ * ((r α) ^ i * (r α) ^ j)) :=
      mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = f α * α⁻¹ * ((r α) ^ i * (r α) ^ j) := by ring

/-- The `∩²`-type constant `1 / (π |h| |α ^ (i+1) - α ^ (j+1)|)` has the bound below. -/
lemma two_div_abs_le_pi (h : ℤ) (hh : h ≠ 0) (d : ℝ) :
    (2 : ℝ) / |w * ((h:ℝ)) * d| ≤ (1 / p) * (1 / |d|) := by
  have hpi : (0:ℝ) < p := Real.pi_pos
  have hcast : ((h:ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hh
  have hh1 : (1:ℝ) ≤ |(h:ℝ)| := by
    have h1 : (1:ℤ) ≤ |h| := Int.one_le_abs hh
    calc (1:ℝ) ≤ ((|h| : ℤ) : ℝ) := by exact_mod_cast h1
      _ = |(h:ℝ)| := by push_cast; ring
  rcases eq_or_ne d 0 with hd | hd
  · rw [hd, mul_zero, abs_zero, div_zero, div_zero, mul_zero]
  · have hd' : |d| ≠ 0 := abs_ne_zero.mpr hd
    have hha : |(h:ℝ)| ≠ 0 := abs_ne_zero.mpr hcast
    have hpi' : p ≠ 0 := Real.pi_ne_zero
    have hw : (0:ℝ) < w := by positivity
    have habs : |w * ((h:ℝ)) * d| = w * |(h:ℝ)| * |d| := by
      rw [abs_mul, abs_mul, abs_of_pos hw]
    rw [habs]
    have heq : (2:ℝ) / (w * |(h:ℝ)| * |d|) = 1 / (p * |(h:ℝ)| * |d|) := by
      field_simp
    rw [heq]
    have hmono : p * 1 * |d| ≤ p * |(h:ℝ)| * |d| :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hh1 hpi.le) (abs_nonneg d)
    have hle : (1:ℝ) / (p * |(h:ℝ)| * |d|) ≤ 1 / (p * 1 * |d|) :=
      one_div_le_one_div_of_le (by positivity) hmono
    refine le_trans hle (le_of_eq ?_)
    field_simp

/-- One cosine term of the squared exponential sum, written with the angle collapsed. -/
noncomputable def cosTerm (α : ℝ) (h : ℤ) (T : ℝ) (i j : ℕ) : ℝ :=
  ∫ ξ in (-T)..T, Real.cos ((w * (h : ℝ) * (α ^ (i + 1) - α ^ (j + 1))) * ξ)

/-- The geometric constant of the pairwise estimate. -/
noncomputable def pairC (α : ℝ) : ℝ :=
  f α * α⁻¹ * (1 - r α)⁻¹ ^ 2

/-- The constant of the `L²` bound. -/
noncomputable def l2const (α : ℝ) : ℝ := (1 / p) * pairC α

lemma l2const_nonneg {α : ℝ} (hα : 1 < α) : 0 ≤ l2const α := by
  have hinv0 : (0:ℝ) < α⁻¹ := by positivity
  have hs2 : r α * r α = α⁻¹ := Real.mul_self_sqrt hinv0.le
  have hinv1 : α⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα
  have hs1 : r α < 1 := by nlinarith [Real.sqrt_nonneg α⁻¹]
  have hspos : (0:ℝ) < 1 - r α := by linarith
  rw [l2const, pairC]
  positivity

/-- The `L²` bound: on any symmetric interval the second moment of the exponential sum grows at
most linearly in `N`. -/
lemma integral_normSq_le {α : ℝ} (hα : 1 < α) (h : ℤ) (hh : h ≠ 0) (T : ℝ) (N : ℕ) :
    ∫ ξ in (-T)..T, ‖psum α h ξ N‖ ^ 2 ≤ 2 * T * N + l2const α := by
  have hα0 : (0:ℝ) < α := by linarith
  have hcpos : (0:ℝ) < g α := div_pos (by linarith) hα0
  have hcast : ((h:ℝ)) ≠ 0 := Int.cast_ne_zero.mpr hh
  have hs0 : (0:ℝ) ≤ r α := Real.sqrt_nonneg _
  have hinv0 : (0:ℝ) < α⁻¹ := by positivity
  have hs2 : r α * r α = α⁻¹ := Real.mul_self_sqrt hinv0.le
  have hinv1 : α⁻¹ < 1 := inv_lt_one_of_one_lt₀ hα
  have hs1 : r α < 1 := by nlinarith [Real.sqrt_nonneg α⁻¹]
  rw [integral_normSq_psum]
  have hstep : ∀ i j : ℕ,
      ∫ ξ in (-T)..T, Real.cos (ang α h ξ i - ang α h ξ j) = cosTerm α h T i j := by
    intro i j
    have hh2 : ∫ ξ in (-T)..T, Real.cos (ang α h ξ i - ang α h ξ j)
        = ∫ ξ in (-T)..T,
            Real.cos ((w * (h:ℝ) * (α ^ (i+1) - α ^ (j+1))) * ξ) := by
      apply intervalIntegral.integral_congr
      intro x _
      simp only [ang_sub]
    exact hh2
  simp only [hstep]
  have hdiag : ∀ i : ℕ, cosTerm α h T i i = 2 * T := by
    intro i
    unfold cosTerm
    simp only [sub_self, mul_zero, zero_mul, Real.cos_zero]
    rw [intervalIntegral.integral_const]
    simp
    ring
  have hoff : ∀ i j : ℕ, i ≠ j → cosTerm α h T i j
      ≤ 2 / |w * (h:ℝ) * (α ^ (i+1) - α ^ (j+1))| := by
    intro i j hij
    have hne : (w * (h:ℝ) * (α ^ (i+1) - α ^ (j+1))) ≠ 0 := by
      have hdne : α ^ (i+1) - α ^ (j+1) ≠ 0 := by
        apply sub_ne_zero.mpr
        rcases lt_or_gt_of_ne hij with hlt | hgt
        · exact ne_of_lt (pow_lt_pow_right₀ hα (Nat.succ_lt_succ hlt))
        · exact ne_of_gt (pow_lt_pow_right₀ hα (Nat.succ_lt_succ hgt))
      exact mul_ne_zero (mul_ne_zero (by positivity) hcast) hdne
    unfold cosTerm
    exact le_trans (le_abs_self _) (abs_integral_cos_mul_le _ T hne)
  have hsumdiag : ∑ i ∈ Finset.range N, (2 * T) = 2 * T * N := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    ring
  have hsumoff : ∑ i ∈ Finset.range N, ∑ j ∈ (Finset.range N).erase i, cosTerm α h T i j
      ≤ l2const α := by
    have hA : ∀ i j : ℕ, i ≠ j → cosTerm α h T i j
        ≤ (1 / p) * (f α * α⁻¹ * ((r α) ^ i * (r α) ^ j)) := by
      intro i j hij
      refine le_trans (hoff i j hij) ?_
      refine le_trans (two_div_abs_le_pi h hh _) ?_
      exact mul_le_mul_of_nonneg_left (one_div_abs_sub_pow_le hα i j) (by positivity)
    have hstepA : ∑ i ∈ Finset.range N, ∑ j ∈ (Finset.range N).erase i, cosTerm α h T i j
        ≤ ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            (1 / p) * (f α * α⁻¹ * ((r α) ^ i * (r α) ^ j)) := by
      apply Finset.sum_le_sum; intro i hi
      refine le_trans (Finset.sum_le_sum fun j hj => hA i j (Ne.symm (Finset.ne_of_mem_erase hj))) ?_
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) (fun j _ _ => by positivity)
    have hfac : (1 / p) * (f α * α⁻¹) *
            ((∑ i ∈ Finset.range N, (r α) ^ i) *
              (∑ j ∈ Finset.range N, (r α) ^ j))
        = ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N,
            (1 / p) * (f α * α⁻¹ * ((r α) ^ i * (r α) ^ j)) := by
      rw [Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hgeom : ∑ i ∈ Finset.range N, (r α) ^ i ≤ (1 - r α)⁻¹ := by
      have hs : Summable (fun i : ℕ => (r α) ^ i) :=
        summable_geometric_of_lt_one hs0 hs1
      have hle := hs.sum_le_tsum (Finset.range N) (fun i _ => pow_nonneg hs0 i)
      rwa [tsum_geometric_of_lt_one hs0 hs1] at hle
    have hgeom0 : (0:ℝ) ≤ ∑ i ∈ Finset.range N, (r α) ^ i :=
      Finset.sum_nonneg fun i _ => pow_nonneg hs0 i
    have hspos : (0:ℝ) < 1 - r α := by linarith
    have hinvnn : (0:ℝ) ≤ (1 - r α)⁻¹ := by positivity
    have hmul := mul_le_mul hgeom hgeom hgeom0 hinvnn
    have hC : (0:ℝ) ≤ (1 / p) * (f α * α⁻¹) := by positivity
    refine le_trans hstepA ?_
    rw [← hfac, l2const, pairC]
    refine le_trans (mul_le_mul_of_nonneg_left hmul hC) (le_of_eq ?_)
    ring
  calc ∑ i ∈ Finset.range N, ∑ j ∈ Finset.range N, cosTerm α h T i j
      = ∑ i ∈ Finset.range N, (2 * T + ∑ j ∈ (Finset.range N).erase i, cosTerm α h T i j) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [(Finset.add_sum_erase (Finset.range N) (fun j => cosTerm α h T i j) hi).symm, hdiag i]
    _ = ∑ i ∈ Finset.range N, (2 * T)
          + ∑ i ∈ Finset.range N, ∑ j ∈ (Finset.range N).erase i, cosTerm α h T i j :=
        Finset.sum_add_distrib
    _ ≤ 2 * T * N + l2const α := by rw [hsumdiag]; linarith

lemma norm_nsum (α : ℝ) (h : ℤ) (ξ : ℝ) (N : ℕ) :
    ‖nsum α h ξ N‖ = (N : ℝ)⁻¹ * ‖psum α h ξ N‖ := by
  rw [nsum, norm_mul, norm_inv]
  congr 1
  simp

noncomputable abbrev q (k : ℕ) := ((k + 1 : ℝ))⁻¹

/-- The second moment of the normalised sum along `N = (k+1) ^ 2`. -/
lemma continuous_nsum (α : ℝ) (h : ℤ) (N : ℕ) : Continuous (fun ξ : ℝ => nsum α h ξ N) := by
  unfold nsum psum ez ang
  fun_prop

lemma integral_normSq_nsum_sq_le {α : ℝ} (hα : 1 < α) (h : ℤ) (hh : h ≠ 0) {T : ℝ} (hT : 0 ≤ T)
    (k : ℕ) :
    ∫ ξ in Set.Ioc (-T) T, ‖nsum α h ξ ((k+1)^2)‖ ^ 2
      ≤ (2 * T + l2const α) * q k ^ 2 := by
  have hu0 : (0:ℝ) < ((k+1 : ℝ)) := by positivity
  have hconv : ∫ ξ in Set.Ioc (-T) T, ‖psum α h ξ ((k+1)^2)‖ ^ 2
      ≤ 2 * T * ((k+1 : ℝ)) ^ 2 + l2const α := by
    have hh2 := integral_normSq_le hα h hh T ((k+1)^2)
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T)] at hh2
    refine le_trans hh2 (le_of_eq ?_)
    push_cast
    ring
  have hcoef : ((((k+1)^2 : ℕ) : ℝ)⁻¹) ^ 2 = q k ^ 4 := by
    push_cast
    rw [← inv_pow]
    ring
  have hc : (0:ℝ) ≤ ((((k+1)^2 : ℕ) : ℝ)⁻¹) ^ 2 := by positivity
  have hpt : ∀ ξ : ℝ, ‖nsum α h ξ ((k+1)^2)‖ ^ 2
      = ((((k+1)^2 : ℕ) : ℝ)⁻¹) ^ 2 * ‖psum α h ξ ((k+1)^2)‖ ^ 2 := by
    intro ξ; rw [norm_nsum, mul_pow]
  simp only [hpt]
  rw [integral_const_mul]
  refine le_trans (mul_le_mul_of_nonneg_left hconv hc) ?_
  rw [hcoef]
  have hinv1 : q k ≤ 1 := by
    rw [inv_le_one₀ hu0]
    push_cast
    linarith
  have hinv0 : (0:ℝ) ≤ q k := by positivity
  have h4 : q k ^ 4 ≤ q k ^ 2 :=
    pow_le_pow_of_le_one hinv0 hinv1 (by norm_num)
  have hC : (0:ℝ) ≤ l2const α := l2const_nonneg hα
  have hstep : q k ^ 4 * (2 * T * ((k+1 : ℝ)) ^ 2 + l2const α)
      = 2 * T * q k ^ 2 + l2const α * q k ^ 4 := by
    simp_rw [inv_pow]
    field_simp
  rw [hstep]
  have hm : l2const α * q k ^ 4 ≤ l2const α * q k ^ 2 :=
    mul_le_mul_of_nonneg_left h4 hC
  linarith [hm]

/-- Borel–Cantelli along the squares: the exponential sum normalised by `(k+1) ^ 2` tends to zero
almost everywhere on any symmetric interval. -/
lemma ae_tendsto_squares {α : ℝ} (hα : 1 < α) (h : ℤ) (hh : h ≠ 0) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ξ ∂(volume.restrict (Set.Ioc (-T) T)),
      Tendsto (fun k : ℕ => nsum α h ξ ((k+1)^2)) atTop (𝓝 0) := by
  have hsummable : Summable (fun k : ℕ => q k ^ 2) := by
    have h0 : Summable (fun n : ℕ => ((n : ℝ))⁻¹ ^ 2) := by
      simpa using
        Real.summable_one_div_nat_pow.mpr (by omega : 1 < 2)
    have h1 : Summable (fun k : ℕ => (((k + 1 : ℕ) : ℝ))⁻¹ ^ 2) :=
      (summable_nat_add_iff (f := fun n : ℕ => ((n : ℝ))⁻¹ ^ 2) (k := 1)).mpr h0
    refine h1.congr fun k => ?_
    push_cast
    ring_nf
  let C : ℝ := 2 * T + l2const α
  have htot : Summable (fun k : ℕ => C * q k ^ 2) :=
    (hsummable.mul_left C).congr fun k => by
      push_cast
      ring
  have hnonneg : ∀ k : ℕ, (0:ℝ) ≤ C * q k ^ 2 := fun k =>
    mul_nonneg (by linarith [l2const_nonneg hα, hT]) (by positivity)
  have hfin : (∑' k : ℕ, ENNReal.ofReal (C * q k ^ 2)) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg htot]
    exact ENNReal.ofReal_ne_top
  let S (x : ℝ) (k : ℕ) := nsum α h x ((k+1)^2)
  let p (j : ℕ) : ℝ := ((j : ℝ) + 1) ^ 2
  have hmain : ∀ j : ℕ, ∀ᵐ ξ ∂(volume.restrict (Set.Ioc (-T) T)),
      ∀ᶠ k in atTop, ‖S ξ k‖ < q j := by
    intro j
    have hjne : ENNReal.ofReal (q j ^ 2) ≠ 0 := by
      rw [ENNReal.ofReal_ne_zero_iff]
      positivity
    have hjtop : ENNReal.ofReal (q j ^ 2) ≠ ∞ := ENNReal.ofReal_ne_top
    have hcheb : ∀ k : ℕ,
        (volume.restrict (Set.Ioc (-T) T))
            {ξ : ℝ | ENNReal.ofReal (q j ^ 2)
              ≤ ENNReal.ofReal (‖S ξ k‖ ^ 2)}
          ≤ ENNReal.ofReal (p j) * ENNReal.ofReal (C * q k ^ 2) := by
      intro k
      have hcont : Continuous (fun ξ : ℝ => ‖S ξ k‖ ^ 2) :=
        (continuous_nsum α h _).norm.pow 2
      have hmarkov := meas_ge_le_lintegral_div (μ := volume.restrict (Set.Ioc (-T) T))
        hcont.measurable.ennreal_ofReal.aemeasurable hjne hjtop
      have hlint : (∫⁻ ξ in Set.Ioc (-T) T,
            ENNReal.ofReal (‖S ξ k‖ ^ 2))
          = ENNReal.ofReal (∫ ξ in Set.Ioc (-T) T,
              ‖S ξ k‖ ^ 2) :=
        (ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Ioc
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)).symm
      rw [hlint] at hmarkov
      have hInt : ENNReal.ofReal (∫ ξ in Set.Ioc (-T) T,
            ‖S ξ k‖ ^ 2)
          ≤ ENNReal.ofReal (C * q k ^ 2) :=
        ENNReal.ofReal_le_ofReal (integral_normSq_nsum_sq_le hα h hh hT k)
      refine le_trans hmarkov (le_trans (ENNReal.div_le_div_right hInt _) (le_of_eq ?_))
      rw [ENNReal.div_eq_inv_mul]
      have hinv : (ENNReal.ofReal (q j ^ 2))⁻¹ = ENNReal.ofReal (p j) := by
        rw [← ENNReal.ofReal_inv_of_pos (show (0:ℝ) < q j ^ 2 from by positivity)]
        congr 1
        field_simp
        rfl
      rw [hinv]
    have hne : (∑' k : ℕ, ENNReal.ofReal (p j) *
        ENNReal.ofReal (C * q k ^ 2)) ≠ ∞ := by
      rw [ENNReal.tsum_mul_left]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
    have hbc := ae_eventually_notMem
      (s := fun k : ℕ => {ξ : ℝ | ENNReal.ofReal (q j ^ 2)
        ≤ ENNReal.ofReal (‖S ξ k‖ ^ 2)})
      (ne_top_of_le_ne_top hne (ENNReal.tsum_le_tsum hcheb))
    refine hbc.mono fun ξ hξ => hξ.mono fun k hk => ?_
    have hlt : ENNReal.ofReal (‖S ξ k‖ ^ 2)
        < ENNReal.ofReal (q j ^ 2) := not_le.mp hk
    have h2 : ‖S ξ k‖ ^ 2 < q j ^ 2 :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp hlt
    have hnn := norm_nonneg (S ξ k)
    have hj0 : (0:ℝ) < q j := by positivity
    nlinarith
  have hall : ∀ᵐ ξ ∂(volume.restrict (Set.Ioc (-T) T)),
      ∀ j : ℕ, ∀ᶠ k in atTop, ‖S ξ k‖ < q j :=
    ae_all_iff.mpr hmain
  refine hall.mono ?_
  intro ξ hξ
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨j, hj⟩ : ∃ j : ℕ, q j < ε := by
    obtain ⟨m, hm⟩ := exists_nat_gt (max 1 ε⁻¹)
    refine ⟨m, ?_⟩
    have hm2 : ε⁻¹ < (m : ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
    rw [inv_lt_comm₀ (by positivity : (0:ℝ) < (m : ℝ) + 1) hε]
    linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hξ j)
  exact ⟨N, fun k hk => by rw [dist_zero_right]; exact lt_trans (hN k hk) hj⟩

/-- Interpolation from the lacunary sequence `N = k ^ 2` to all `N`: if the normalised sums along
the squares tend to zero then so do all of them. -/
lemma tendsto_nsum_of_squares (α : ℝ) (h : ℤ) (ξ : ℝ)
    (hsq : Tendsto (fun k : ℕ => nsum α h ξ ((k+1)^2)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => nsum α h ξ N) atTop (𝓝 0) := by
  let S (n : ℕ) := nsum α h ξ n
  let P (n : ℕ) := psum α h ξ n
  have hu : Tendsto (fun k : ℕ => S (k^2)) atTop (𝓝 0) :=
    (tendsto_add_atTop_iff_nat 1).mp hsq
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  have hε2 : (0:ℝ) < ε / 2 := by linarith
  obtain ⟨K₀, hK₀⟩ := Metric.tendsto_atTop.mp hu (ε/2) hε2
  obtain ⟨K₁, hK₁a, hK₁b⟩ : ∃ K₁ : ℕ, 1 ≤ K₁ ∧ 2 * ((K₁:ℝ))⁻¹ < ε / 2 := by
    obtain ⟨m, hm⟩ := exists_nat_gt (max 1 (4/ε))
    have hm1 : (1:ℝ) ≤ (m:ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hm)
    have hm2 : 4/ε < (m:ℝ) := lt_of_le_of_lt (le_max_right _ _) hm
    refine ⟨m, ?_, ?_⟩
    · exact_mod_cast hm1
    · have hm0 : (0:ℝ) < (m:ℝ) := by linarith
      have hprod : 4 < ε * (m:ℝ) := by
        simpa [mul_comm] using (div_lt_iff₀ hε).mp hm2
      change 2 / (m:ℝ) < ε / 2
      rw [div_lt_iff₀ hm0]
      nlinarith
  refine ⟨max (K₀^2) (K₁^2), fun N hN => ?_⟩
  have hN₀ : K₀^2 ≤ N := le_trans (le_max_left _ _) hN
  have hN₁ : K₁^2 ≤ N := le_trans (le_max_right _ _) hN
  set K := Nat.sqrt N with hKdef
  have hM : K^2 ≤ N := Nat.sqrt_le' N
  have hNK : N < (K+1)^2 := by
    have := Nat.lt_succ_sqrt' N
    simpa [Nat.succ_eq_add_one] using this
  have hK₀K : K₀ ≤ K := Nat.le_sqrt'.mpr hN₀
  have hK₁K : K₁ ≤ K := Nat.le_sqrt'.mpr hN₁
  have hK1 : 1 ≤ K := le_trans hK₁a hK₁K
  have hKpos : 0 < (K:ℝ) := by exact_mod_cast hK1
  have hK1pos : (0:ℝ) < (K₁:ℝ) := by exact_mod_cast hK₁a
  have hNpos : 0 < (N:ℝ) := by
    have h1 : 0 < N := lt_of_lt_of_le (by positivity : 0 < K₁^2) hN₁
    exact_mod_cast h1
  have hbig : ‖S (K^2)‖ < ε/2 := by simpa using hK₀ K hK₀K
  -- the difference of the two normalised sums
  have hsub : Finset.range (K^2) ⊆ Finset.range N := Finset.range_subset_range.mpr hM
  have hsplit : P N
      = P (K^2) + ∑ n ∈ (Finset.range N \ Finset.range (K^2)), ez α h ξ n := by
    change psum α h ξ N
      = psum α h ξ (K^2) + ∑ n ∈ (Finset.range N \ Finset.range (K^2)), ez α h ξ n
    unfold psum
    rw [← Finset.sum_sdiff hsub, add_comm]
  have hde : ‖∑ n ∈ (Finset.range N \ Finset.range (K^2)), ez α h ξ n‖
      ≤ (N:ℝ) - ((K:ℝ))^2 := by
    calc
      _ ≤ ((Finset.range N \ Finset.range (K^2)).card : ℝ) := by
        simpa [norm_ez] using
          (norm_sum_le (Finset.range N \ Finset.range (K^2))
            (fun n : ℕ => ez α h ξ n))
      _ = _ := by
        rw [Finset.card_sdiff, (Finset.inter_eq_left).mpr hsub, Finset.card_range,
          Finset.card_range, Nat.cast_sub hM]
        push_cast
        ring
  have hps : ‖P N‖ ≤ ‖P (K^2)‖ + ((N:ℝ) - ((K:ℝ))^2) := by
    rw [hsplit]
    have := norm_add_le (P (K^2)) (∑ n ∈ (Finset.range N \ Finset.range (K^2)), ez α h ξ n)
    linarith
  have hpsM : ‖P (K^2)‖ = ((K:ℝ))^2 * ‖S (K^2)‖ := by
    have h' := norm_nsum α h ξ (K^2)
    have hK2 : ((((K^2 : ℕ)) : ℝ)) = ((K:ℝ))^2 := by push_cast; ring
    rw [hK2] at h'
    field_simp at h'
    linarith
  have hstep : ‖S N‖
      ≤ ((K:ℝ))^2 / (N:ℝ) * ‖S (K^2)‖ + ((N:ℝ) - ((K:ℝ))^2) / (N:ℝ) := by
    calc
      ‖S N‖ = (N:ℝ)⁻¹ * ‖P N‖ := norm_nsum α h ξ N
      _ ≤ (N:ℝ)⁻¹ * (‖P (K^2)‖ + ((N:ℝ) - ((K:ℝ))^2)) :=
        mul_le_mul_of_nonneg_left hps (by positivity)
      _ = _ := by rw [hpsM]; field_simp
  have hMK : ((K:ℝ))^2 ≤ (N:ℝ) := by
    have h' : ((K^2 : ℕ) : ℝ) ≤ (N:ℝ) := by exact_mod_cast hM
    simpa [Nat.cast_pow] using h'
  have herr : ((N:ℝ) - ((K:ℝ))^2) / (N:ℝ) ≤ 2 * ((K:ℝ))⁻¹ := by
    have hNm : ((N:ℝ) - ((K:ℝ))^2) ≤ 2 * (K:ℝ) := by
      have hnat : N ≤ K^2 + 2*K := by
        have hs : (K + 1)^2 = K^2 + (2*K + 1) := by ring
        omega
      have hcast : (N:ℝ) ≤ (K:ℝ)^2 + 2*(K:ℝ) := by exact_mod_cast hnat
      linarith
    rw [div_le_iff₀ hNpos]
    exact le_trans hNm (by
      calc
        2 * (K:ℝ) ≤ 2 * (N:ℝ) / (K:ℝ) := by
          rw [le_div_iff₀ hKpos]
          nlinarith [hMK]
        _ = 2 * (K:ℝ)⁻¹ * (N:ℝ) := by rw [div_eq_mul_inv]; ring)
  -- assembly
  rw [dist_zero_right]
  have ha0 : (0:ℝ) ≤ ((K:ℝ))^2 / (N:ℝ) := by positivity
  have ha1 : ((K:ℝ))^2 / (N:ℝ) ≤ 1 := by
    rw [div_le_one hNpos]
    exact_mod_cast hM
  have hA : 0 ≤ ‖S (K^2)‖ := norm_nonneg _
  have hle : ((K:ℝ))^2 / (N:ℝ) * ‖S (K^2)‖ ≤ ‖S (K^2)‖ := by
    nlinarith
  have herr2 : 2 * ((K:ℝ))⁻¹ ≤ 2 * ((K₁:ℝ))⁻¹ := by
    have : ((K:ℝ))⁻¹ ≤ ((K₁:ℝ))⁻¹ := inv_anti₀ hK1pos (by exact_mod_cast hK₁K)
    linarith
  linarith


noncomputable section

open Classical

/-! # Weyl's criterion -/

/-- The circle `ℝ / ℤ`. -/
abbrev Torus := AddCircle (1 : ℝ)

/-- The `N`-th average of a continuous function on the circle along a sequence `s`. -/
def favg (s : ℕ → ℝ) (k : ℤ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, fourier k ((s n : ℝ) : Torus)

/-- The `N`-th average of an arbitrary function on the circle along a sequence `s`. -/
def avgC (s : ℕ → ℝ) (P : Torus → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.range N, P ((s n : ℝ) : Torus)

/-- The `N`-th average of a real function on the circle along a sequence `s`. -/
def avgR (s : ℕ → ℝ) (P : Torus → ℝ) (N : ℕ) : ℝ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.range N, P ((s n : ℝ) : Torus)

/-- The Weyl hypothesis: every nonzero exponential sum tends to zero. -/
def WeylHyp (s : ℕ → ℝ) : Prop :=
  ∀ k : ℤ, k ≠ 0 → Tendsto (fun N : ℕ => favg s k N) atTop (𝓝 0)

/-! ## Integrals of the Fourier characters -/

lemma volume_univ_torus : (volume : Measure Torus).real Set.univ = 1 := by
  rw [Measure.real, AddCircle.measure_univ, ENNReal.toReal_ofReal (by norm_num)]

lemma integral_fourier_zero : (∫ x : Torus, fourier (0 : ℤ) x) = 1 := by
  simp only [fourier_zero]
  rw [integral_const, volume_univ_torus, one_smul]

lemma integral_fourier_ne (k : ℤ) (hk : k ≠ 0) : (∫ x : Torus, fourier k x) = 0 := by
  have hbridge := AddCircle.intervalIntegral_preimage (T := 1) (E := ℂ) 0
    (fun x : Torus => fourier k x)
  rw [← hbridge]
  simp only [zero_add]
  have hcongr : (∫ a in (0 : ℝ)..1, fourier k (a : Torus))
      = ∫ a in (0 : ℝ)..1, Complex.exp ((2 * Real.pi * Complex.I * (k : ℂ)) * a) := by
    refine intervalIntegral.integral_congr fun a _ => ?_
    rw [fourier_coe_apply]
    push_cast
    ring_nf
  rw [hcongr]
  have hc : (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ)) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero)
      (by exact_mod_cast hk)
    exact_mod_cast Real.pi_ne_zero
  rw [integral_exp_mul_complex hc]
  have hexp : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((1:ℝ) : ℂ)) = 1 := by
    refine Complex.exp_eq_one_iff.mpr ⟨k, ?_⟩
    push_cast
    ring
  have h0 : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) * ((0:ℝ) : ℂ)) = 1 := by simp
  rw [hexp, h0, sub_self, zero_div]

/-! ## The average of a single character -/

lemma tendsto_favg (s : ℕ → ℝ) (H : WeylHyp s) (k : ℤ) :
    Tendsto (fun N : ℕ => favg s k N) atTop (𝓝 (∫ x : Torus, fourier k x)) := by
  by_cases hk : k = 0
  · subst hk
    rw [integral_fourier_zero]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hsum : (∑ n ∈ Finset.range N, fourier (0 : ℤ) ((s n : ℝ) : Torus)) = (N : ℂ) := by
      simp
    have hN0 : (N : ℂ) ≠ 0 := by
      exact_mod_cast (by omega : N ≠ 0)
    simp only [favg, hsum]
    field_simp
  · rw [integral_fourier_ne k hk]
    exact H k hk

/-! ## Trigonometric polynomials -/

/-- Trig polynomials: the span of the Fourier characters in `C(𝕋, ℂ)`. -/
abbrev trigSpan : Submodule ℂ C(Torus, ℂ) :=
  Submodule.span ℂ (Set.range (fourier : ℤ → C(Torus, ℂ)))

lemma integrable_of_continuous (P : C(Torus, ℂ)) : Integrable (P : Torus → ℂ) :=
  MeasureTheory.Integrable.of_bound P.continuous.aestronglyMeasurable ‖P‖
    (Filter.Eventually.of_forall fun x => P.norm_coe_le_norm x)

lemma span_avg (s : ℕ → ℝ) (H : WeylHyp s) :
    ∀ P ∈ trigSpan,
      Tendsto (fun N : ℕ => avgC s (P : Torus → ℂ) N) atTop
        (𝓝 (∫ x : Torus, (P : Torus → ℂ) x)) := by
  intro P hP
  induction hP using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨k, rfl⟩ := hp
    exact tendsto_favg s H k
  | zero =>
    simp [avgC]
  | add P Q _ _ ihP ihQ =>
    convert ihP.add ihQ using 1
    · ext N
      simp only [avgC, ContinuousMap.add_apply, Finset.sum_add_distrib, mul_add]
    · congr 1
      exact integral_add (integrable_of_continuous P) (integrable_of_continuous Q)
  | smul c P _ ih =>
    convert ih.const_mul c using 1
    · ext N
      simp only [avgC, ContinuousMap.smul_apply, smul_eq_mul]
      rw [← Finset.mul_sum]
      ring
    · congr 1
      simpa only [ContinuousMap.smul_apply, smul_eq_mul] using integral_const_mul c _

/-! ## Approximation by trigonometric polynomials -/

lemma exists_trig_approx (F : C(Torus, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ P ∈ trigSpan, ∀ x : Torus, ‖F x - P x‖ ≤ ε := by
  have htop : ((trigSpan.topologicalClosure : Submodule ℂ C(Torus, ℂ)) : Set C(Torus, ℂ)) = ⊤ := by
    rw [span_fourier_closure_eq_top (T := 1)]
    rfl
  have hmem : (F : C(Torus, ℂ)) ∈ (trigSpan.topologicalClosure : Set C(Torus, ℂ)) := by
    rw [htop]
    exact Set.mem_univ F
  rw [Submodule.topologicalClosure_coe, Metric.mem_closure_iff] at hmem
  obtain ⟨P, hPspan, hFP⟩ := hmem ε hε
  refine ⟨P, hPspan, fun x => ?_⟩
  have hdist : dist (F x) (P x) ≤ dist F P := ContinuousMap.dist_apply_le_dist x
  have h2 : dist F P = ‖F - P‖ := dist_eq_norm F P
  have h3 : ‖F - P‖ ≤ ε := by
    rw [dist_eq_norm] at hFP
    exact le_of_lt hFP
  calc ‖F x - P x‖ = dist (F x) (P x) := (dist_eq_norm _ _).symm
    _ ≤ dist F P := hdist
    _ = ‖F - P‖ := h2
    _ ≤ ε := h3

/-! ## The continuous case -/

lemma avgC_sub_le (s : ℕ → ℝ) (F P : C(Torus, ℂ)) {ε : ℝ}
    (hFP : ∀ x : Torus, ‖F x - P x‖ ≤ ε) {N : ℕ} (hN : 1 ≤ N) :
    ‖avgC s (F : Torus → ℂ) N - avgC s (P : Torus → ℂ) N‖ ≤ ε := by
  have hN0 : (0:ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  simp only [avgC]
  rw [← mul_sub, ← Finset.sum_sub_distrib, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ n ∈ Finset.range N,
      (F ((s n : ℝ) : Torus) - P ((s n : ℝ) : Torus))‖ ≤ (N:ℝ) * ε := by
    calc
      _ ≤ ∑ n ∈ Finset.range N, ‖F ((s n : ℝ) : Torus) - P ((s n : ℝ) : Torus)‖ :=
        norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.range N, ε := Finset.sum_le_sum fun n _ => hFP _
      _ = (N:ℝ) * ε := by simp
  calc
    (N:ℝ)⁻¹ * ‖∑ n ∈ Finset.range N,
        (F ((s n : ℝ) : Torus) - P ((s n : ℝ) : Torus))‖ ≤ (N:ℝ)⁻¹ * ((N:ℝ) * ε) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ε := by field_simp

lemma integral_sub_le (F P : C(Torus, ℂ)) {ε : ℝ}
    (hFP : ∀ x : Torus, ‖F x - P x‖ ≤ ε) :
    ‖(∫ x : Torus, (F : Torus → ℂ) x) - ∫ x : Torus, (P : Torus → ℂ) x‖ ≤ ε := by
  have h1 := integrable_of_continuous F
  have h2 := integrable_of_continuous P
  have heq : (∫ x : Torus, (F : Torus → ℂ) x) - ∫ x : Torus, (P : Torus → ℂ) x
      = ∫ x : Torus, (F x - P x) := (integral_sub h1 h2).symm
  rw [heq]
  have h3 : ‖∫ x : Torus, (F x - P x)‖ ≤ ε * (volume : Measure Torus).real Set.univ :=
    norm_integral_le_of_norm_le_const (Filter.Eventually.of_forall hFP)
  rwa [volume_univ_torus, mul_one] at h3

lemma continuous_avg_tendsto (s : ℕ → ℝ) (H : WeylHyp s) (F : C(Torus, ℂ)) :
    Tendsto (fun N : ℕ => avgC s (F : Torus → ℂ) N) atTop
      (𝓝 (∫ x : Torus, (F : Torus → ℂ) x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨P, hPspan, hFP⟩ := exists_trig_approx F (show 0 < ε/3 by linarith)
  obtain ⟨N₀, hN₀⟩ := Metric.tendsto_atTop.mp (span_avg s H P hPspan) (ε/3) (by linarith)
  refine ⟨max N₀ 1, fun N hN => ?_⟩
  have hN₁ : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN₀' : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hA : dist (avgC s (F : Torus → ℂ) N) (avgC s (P : Torus → ℂ) N) ≤ ε/3 := by
    rw [dist_eq_norm]
    exact avgC_sub_le s F P hFP hN₁
  have hB : dist (avgC s (P : Torus → ℂ) N) (∫ x : Torus, (P : Torus → ℂ) x) < ε/3 :=
    hN₀ N hN₀'
  have hC : dist (∫ x : Torus, (P : Torus → ℂ) x) (∫ x : Torus, (F : Torus → ℂ) x)
      ≤ ε/3 := by
    rw [dist_eq_norm, norm_sub_rev]
    exact integral_sub_le F P hFP
  calc
    dist (avgC s (F : Torus → ℂ) N) (∫ x : Torus, (F : Torus → ℂ) x)
        ≤ dist (avgC s (F : Torus → ℂ) N) (avgC s (P : Torus → ℂ) N)
          + dist (avgC s (P : Torus → ℂ) N) (∫ x : Torus, (F : Torus → ℂ) x) :=
          dist_triangle _ _ _
    _ ≤ ε/3 + (dist (avgC s (P : Torus → ℂ) N) (∫ x : Torus, (P : Torus → ℂ) x)
          + dist (∫ x : Torus, (P : Torus → ℂ) x) (∫ x : Torus, (F : Torus → ℂ) x)) :=
        add_le_add hA (dist_triangle _ _ _)
    _ < ε := by linarith

/-! ## The real case -/

lemma continuous_avgR_tendsto (s : ℕ → ℝ) (H : WeylHyp s) (G : C(Torus, ℝ)) :
    Tendsto (fun N : ℕ => avgR s (G : Torus → ℝ) N) atTop
      (𝓝 (∫ x : Torus, (G : Torus → ℝ) x)) := by
  let Gc : C(Torus, ℂ) :=
    ⟨fun x => (G x : ℂ), Complex.continuous_ofReal.comp G.continuous⟩
  convert (Complex.continuous_re.tendsto _).comp (continuous_avg_tendsto s H Gc) using 1
  · ext N
    simp [avgC, avgR, Gc]
  · have heq : (∫ x : Torus, (Gc : Torus → ℂ) x)
        = ((∫ x : Torus, (G : Torus → ℝ) x : ℝ) : ℂ) := by
      exact integral_ofReal
    rw [heq, Complex.ofReal_re]

/-! ## Periodic functions on the line -/

lemma liftIco_val {g : ℝ → ℝ} (x : ℝ) :
    AddCircle.liftIco 1 0 g ((x : ℝ) : Torus) = g (Int.fract x) := by
  rw [← AddCircle.coe_fract x]
  exact AddCircle.liftIco_coe_apply ⟨Int.fract_nonneg x, by simpa using Int.fract_lt_one x⟩

lemma liftIco_integral {g : ℝ → ℝ} (hg : g 0 = g 1) (hgcont : Continuous g) :
    (∫ x : Torus, AddCircle.liftIco 1 0 g x) = ∫ t in (0:ℝ)..1, g t := by
  have hb := AddCircle.intervalIntegral_preimage (T := 1) (E := ℝ) 0
    (fun x : Torus => AddCircle.liftIco 1 0 g x)
  rw [← hb]
  simp only [zero_add]
  refine intervalIntegral.integral_congr fun a ha => ?_
  rw [Set.uIcc_of_le zero_le_one] at ha
  rcases lt_or_eq_of_le ha.2 with hlt | heq
  · exact AddCircle.liftIco_coe_apply ⟨ha.1, by simpa using hlt⟩
  · subst heq
    have hone : ((1:ℝ) : Torus) = 0 := by
      rw [← AddCircle.coe_fract (1:ℝ)]
      norm_num
    rw [hone]
    change AddCircle.liftIco 1 0 g ((0:ℝ) : Torus) = g 1
    rw [AddCircle.liftIco_coe_apply ⟨le_refl 0, by simpa using zero_lt_one⟩]
    exact hg

/-! ## Averaging profiles on the fundamental domain -/

/-- Averaging along `s` a profile `g` evaluated at the fractional parts. -/
lemma tendsto_avg_fract (s : ℕ → ℝ) (H : WeylHyp s) {g : ℝ → ℝ}
    (hgcont : Continuous g) (h0 : g 0 = g 1) :
    Tendsto (fun N : ℕ => (N:ℝ)⁻¹ * ∑ n ∈ Finset.range N, g (Int.fract (s n))) atTop
      (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
  set G : C(Torus, ℝ) := ⟨AddCircle.liftIco 1 0 g,
    AddCircle.liftIco_zero_continuous h0 hgcont.continuousOn⟩ with hG
  have hGval : ∀ x : ℝ, (G : Torus → ℝ) ((x : ℝ) : Torus) = g (Int.fract x) :=
    fun x => liftIco_val x
  have hint : (∫ x : Torus, (G : Torus → ℝ) x) = ∫ t in (0:ℝ)..1, g t :=
    liftIco_integral h0 hgcont
  have hmain : Tendsto (fun N : ℕ => avgR s (G : Torus → ℝ) N) atTop (𝓝 (∫ t in (0:ℝ)..1, g t)) := by
    have h := continuous_avgR_tendsto s H G
    rwa [hint] at h
  refine hmain.congr' ?_
  filter_upwards with N
  simp only [avgR, hGval]

/-! ## Tent profiles -/

/-- The inner tent profile: `1` on `[a + δ, b - δ]`, sloping linearly to `0` at `a` and `b`. -/
def tentLo (a b δ : ℝ) (t : ℝ) : ℝ :=
  max 0 (min 1 (min ((t - a) / δ) ((b - t) / δ)))

lemma continuous_tentLo (a b δ : ℝ) : Continuous (tentLo a b δ) := by
  unfold tentLo
  fun_prop

lemma tentLo_nonneg (a b δ t : ℝ) : 0 ≤ tentLo a b δ t := le_max_left _ _

lemma tentLo_le_one (a b δ t : ℝ) : tentLo a b δ t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

lemma tentLo_one (a b δ t : ℝ) (hδ : 0 < δ) (h1 : a + δ ≤ t) (h2 : t ≤ b - δ) :
    tentLo a b δ t = 1 := by
  have hx : 1 ≤ (t - a) / δ := by rw [le_div_iff₀ hδ]; linarith
  have hy : 1 ≤ (b - t) / δ := by rw [le_div_iff₀ hδ]; linarith
  simp only [tentLo]
  rw [min_eq_left (le_min hx hy)]
  simp

lemma tentLo_zero_of_lt (a b δ t : ℝ) (hδ : 0 < δ) (h : t < a) : tentLo a b δ t = 0 := by
  have hx : (t - a) / δ < 0 := div_neg_of_neg_of_pos (by linarith) hδ
  simp only [tentLo]
  exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_left _ _) hx.le))

lemma tentLo_zero_of_gt (a b δ t : ℝ) (hδ : 0 < δ) (h : b < t) : tentLo a b δ t = 0 := by
  have hy : (b - t) / δ < 0 := div_neg_of_neg_of_pos (by linarith) hδ
  simp only [tentLo]
  exact max_eq_left (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) hy.le))

lemma tentLo_le_indicator (a b δ : ℝ) (hδ : 0 < δ) (t : ℝ) :
    tentLo a b δ t ≤ (Set.Icc a b).indicator (fun _ => (1:ℝ)) t := by
  rw [Set.indicator_apply]
  by_cases h : t ∈ Set.Icc a b
  · rw [if_pos h]
    exact tentLo_le_one a b δ t
  · rw [if_neg h]
    have hle : tentLo a b δ t ≤ 0 := by
      simp only [Set.mem_Icc, not_and_or, not_le] at h
      rcases h with h | h
      · exact (tentLo_zero_of_lt a b δ t hδ h).le
      · exact (tentLo_zero_of_gt a b δ t hδ h).le
    exact hle

lemma tentLo_zero_zero {a b δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) (hδb : δ < 1 - b) :
    tentLo a b δ 0 = tentLo a b δ 1 := by
  rw [tentLo_zero_of_lt a b δ 0 hδ (by linarith), tentLo_zero_of_gt a b δ 1 hδ (by linarith)]

lemma integral_tentLo_ge {a b δ : ℝ} (hδ : 0 < δ) (hδa : δ < a) (hδb : δ < 1 - b)
    (hab : a + δ ≤ b - δ) :
    b - a - 2 * δ ≤ ∫ t in (0:ℝ)..1, tentLo a b δ t := by
  have hcont : Continuous (tentLo a b δ) := continuous_tentLo a b δ
  have hint : ∀ x y : ℝ, IntervalIntegrable (tentLo a b δ) volume x y :=
    fun x y => hcont.intervalIntegrable x y
  have hnn : ∀ t, 0 ≤ tentLo a b δ t := tentLo_nonneg a b δ
  have hA : 0 ≤ ∫ t in (0:ℝ)..(a+δ), tentLo a b δ t :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => hnn t)
  have hC : 0 ≤ ∫ t in (b-δ)..1, tentLo a b δ t :=
    intervalIntegral.integral_nonneg (by linarith) (fun t _ => hnn t)
  have hB : ∫ t in (a+δ)..(b-δ), tentLo a b δ t = (b - δ) - (a + δ) := by
    have hcongr : ∫ t in (a+δ)..(b-δ), tentLo a b δ t = ∫ t in (a+δ)..(b-δ), (1:ℝ) := by
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hab] at ht
      exact tentLo_one a b δ t hδ ht.1 ht.2
    rw [hcongr, intervalIntegral.integral_const]
    simp
  have hs1 := intervalIntegral.integral_add_adjacent_intervals (hint 0 (a+δ)) (hint (a+δ) 1)
  have hs2 := intervalIntegral.integral_add_adjacent_intervals (hint (a+δ) (b-δ)) (hint (b-δ) 1)
  linarith

/-! ## Counting functions and their limits -/

/-- Number of `n < N` with `u n ∈ A`, regarded as a real number. -/
def cnt (u : ℕ → ℝ) (A : Set ℝ) (N : ℕ) : ℝ :=
  (((Finset.range N).filter (fun n => u n ∈ A)).card : ℝ)

def oneInd (A : Set ℝ) (t : ℝ) : ℝ := A.indicator (fun _ => (1:ℝ)) t

/-- The counting function written as a sum of indicator functions. -/
lemma cnt_eq_sum (u : ℕ → ℝ) (A : Set ℝ) (N : ℕ) :
    cnt u A N = ∑ n ∈ Finset.range N, oneInd A (u n) := by
  rw [cnt, Finset.card_filter, Nat.cast_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [oneInd, Set.indicator_apply]
  by_cases h : u n ∈ A <;> simp [h]

/-- Hypothesis that averages of continuous periodic profiles along `u` converge to integrals. -/
def AvgHyp (u : ℕ → ℝ) : Prop :=
  ∀ (g : ℝ → ℝ), Continuous g → g 0 = g 1 →
    Tendsto (fun N : ℕ => (N:ℝ)⁻¹ * ∑ n ∈ Finset.range N, g (u n)) atTop
      (𝓝 (∫ t in (0:ℝ)..1, g t))

lemma avgHyp_fract (s : ℕ → ℝ) (H : WeylHyp s) : AvgHyp (fun n => Int.fract (s n)) :=
  fun g hc h0 => tendsto_avg_fract s H hc h0

lemma indicator_subset {c d δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    oneInd (Set.Icc (c + δ) (d - δ)) t ≤ oneInd (Set.Icc c d) t := by
  unfold oneInd
  rw [Set.indicator_apply, Set.indicator_apply]
  by_cases h : t ∈ Set.Icc (c + δ) (d - δ)
  · rw [if_pos h, if_pos ⟨by linarith [h.1], by linarith [h.2]⟩]
  · rw [if_neg h]
    split_ifs <;> simp

lemma indicator_disjoint_le {c d δ : ℝ} (hδ : 0 < δ) (hcd : c ≤ d) (t : ℝ) :
    oneInd (Set.Icc c d) t + oneInd (Set.Icc δ (c - δ)) t
      + oneInd (Set.Icc (d + δ) (1 - δ)) t ≤ 1 := by
  unfold oneInd
  simp only [Set.indicator_apply]
  split_ifs <;> norm_num at * <;> linarith

/-- Comparison of a sum of profile values with the counting function. -/
lemma sum_le_cnt {u : ℕ → ℝ} {A : Set ℝ} {g : ℝ → ℝ}
    (h : ∀ t, g t ≤ oneInd A t) (N : ℕ) :
    ∑ n ∈ Finset.range N, g (u n) ≤ cnt u A N := by
  rw [cnt_eq_sum]
  exact Finset.sum_le_sum fun n _ => h _

lemma cnt_subset {u : ℕ → ℝ} {A B : Set ℝ}
    (h : ∀ t, oneInd A t ≤ oneInd B t) (N : ℕ) :
    cnt u A N ≤ cnt u B N := by
  rw [cnt_eq_sum, cnt_eq_sum]
  exact Finset.sum_le_sum fun n _ => h _

lemma cnt_add_le {u : ℕ → ℝ} {A B C : Set ℝ}
    (h : ∀ t, oneInd A t + oneInd B t + oneInd C t ≤ 1) (N : ℕ) :
    cnt u A N + cnt u B N + cnt u C N ≤ (N : ℝ) := by
  rw [cnt_eq_sum, cnt_eq_sum, cnt_eq_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  calc
    _ ≤ ∑ _n ∈ Finset.range N, (1:ℝ) := Finset.sum_le_sum fun n _ => h _
    _ = _ := by simp

lemma cnt_nonneg (u : ℕ → ℝ) (A : Set ℝ) (N : ℕ) : 0 ≤ cnt u A N := by
  rw [cnt_eq_sum]
  exact Finset.sum_nonneg fun n _ =>
    (Set.indicator_nonneg (fun _ _ => zero_le_one) (u n))

/-- One-sided lower bound for the counting function, valid for any interior interval. -/
lemma cnt_lower_eventually (u : ℕ → ℝ) (Hu : AvgHyp u) {a b δ η : ℝ} (hab : a ≤ b)
    (hδ : 0 < δ) (hδa : δ < a) (hδb : δ < 1 - b) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, (b - a) - 2 * δ - η ≤ cnt u (Set.Icc a b) N / (N : ℝ) := by
  by_cases hcase : a + δ ≤ b - δ
  · have hlo := Hu (tentLo a b δ) (continuous_tentLo a b δ) (tentLo_zero_zero hδ hδa hδb)
    have hIntLo := integral_tentLo_ge hδ hδa hδb hcase
    filter_upwards [eventually_atTop.mpr (Metric.tendsto_atTop.mp hlo η hη)] with N hN
    rw [Real.dist_eq] at hN
    have hcmp : ((N : ℝ))⁻¹ * (∑ n ∈ Finset.range N, tentLo a b δ (u n))
        ≤ cnt u (Set.Icc a b) N / (N : ℝ) := by
      have hle := sum_le_cnt (u := u) (fun t => tentLo_le_indicator a b δ hδ t) N
      rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    linarith [(abs_lt.mp hN).1]
  · filter_upwards with N
    have h1 : (0:ℝ) ≤ cnt u (Set.Icc a b) N / (N : ℝ) :=
      div_nonneg (cnt_nonneg u (Set.Icc a b) N) (by positivity)
    linarith

/-- One-sided upper bound for the counting function, valid for any interval inside `[0, 1]`. -/
lemma cnt_upper_eventually (u : ℕ → ℝ) (Hu : AvgHyp u) {a b δ η : ℝ} (ha0 : 0 ≤ a)
    (hab : a ≤ b) (hb1 : b ≤ 1) (hδ : 0 < δ) (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, cnt u (Set.Icc a b) N / (N : ℝ) ≤ (b - a + 4 * δ) + η := by
  set δs : ℝ := min (δ/2) (η/16) with hδsdef
  have hδs : 0 < δs := lt_min (by linarith) (by linarith)
  have hδsδ : δs < δ := by
    have h1 : δs ≤ δ/2 := min_le_left _ _
    linarith
  have hδsη : 8 * δs ≤ η/2 := by
    have h1 : δs ≤ η/16 := min_le_right _ _
    linarith
  have hB_ev : ∀ᶠ N : ℕ in atTop, (a - 2 * δ) - η/2 ≤ cnt u (Set.Icc δ (a - δ)) N / (N : ℝ) := by
    by_cases hcase : δ ≤ a - δ
    · filter_upwards [cnt_lower_eventually u Hu (a := δ) (b := a - δ) (δ := δs)
        (η := η/4) hcase hδs (by linarith) (by linarith) (by linarith)] with N hN
      linarith [hδsη]
    · have hempty : Set.Icc δ (a - δ) = ∅ := Set.Icc_eq_empty hcase
      filter_upwards with N
      have hzero : cnt u (Set.Icc δ (a - δ)) N = 0 := by
        rw [cnt_eq_sum]
        simp [oneInd, hempty]
      rw [hzero, zero_div]
      linarith
  have hC_ev : ∀ᶠ N : ℕ in atTop,
      (1 - b - 2 * δ) - η/2 ≤ cnt u (Set.Icc (b + δ) (1 - δ)) N / (N : ℝ) := by
    by_cases hcase : (b + δ) ≤ (1 - δ)
    · filter_upwards [cnt_lower_eventually u Hu (a := b + δ) (b := 1 - δ) (δ := δs)
        (η := η/4) hcase hδs (by linarith) (by linarith) (by linarith)] with N hN
      linarith [hδsη]
    · have hempty : Set.Icc (b + δ) (1 - δ) = ∅ := Set.Icc_eq_empty hcase
      filter_upwards with N
      have hzero : cnt u (Set.Icc (b + δ) (1 - δ)) N = 0 := by
        rw [cnt_eq_sum]
        simp [oneInd, hempty]
      rw [hzero, zero_div]
      linarith
  filter_upwards [hB_ev, hC_ev, eventually_ge_atTop (1 : ℕ)] with N hB hC hN
  have hsplit := cnt_add_le (u := u) (A := Set.Icc a b) (B := Set.Icc δ (a - δ))
    (C := Set.Icc (b + δ) (1 - δ)) (fun t => indicator_disjoint_le hδ hab t) N
  have hNpos : (0:ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hdiv : cnt u (Set.Icc a b) N / (N : ℝ) + (cnt u (Set.Icc δ (a - δ)) N / (N : ℝ)
      + cnt u (Set.Icc (b + δ) (1 - δ)) N / (N : ℝ)) ≤ 1 := by
    rw [← add_div, ← add_div, div_le_one hNpos]
    linarith
  linarith

/-- The counting limit for an arbitrary closed interval inside `[0, 1]`. -/
lemma tendsto_cnt (u : ℕ → ℝ) (Hu : AvgHyp u) {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d)
    (hd : d ≤ 1) :
    Tendsto (fun N : ℕ => cnt u (Set.Icc c d) N / (N : ℝ)) atTop (𝓝 (d - c)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hη4 : (0:ℝ) < ε/4 := by linarith
  set δ : ℝ := min (ε/16) (1/2) with hδdef
  have hδ : 0 < δ := lt_min (by linarith) (by norm_num)
  have hδe : 4 * δ ≤ ε/4 := by
    have h1 : δ ≤ ε/16 := min_le_left _ _
    linarith
  have hlow : ∀ᶠ N : ℕ in atTop, (d - c) - ε/2 ≤ cnt u (Set.Icc c d) N / (N:ℝ) := by
    by_cases hcase : c + δ ≤ d - δ
    · have hδ2 : 0 < δ / 2 := by positivity
      have hδc : δ / 2 < c + δ := by linarith
      have hδd : δ / 2 < 1 - (d - δ) := by linarith
      have hinner := cnt_lower_eventually u Hu (a := c + δ) (b := d - δ) (δ := δ/2)
        (η := ε/4) hcase hδ2 hδc hδd hη4
      filter_upwards [hinner] with N hN
      have hmono : cnt u (Set.Icc (c + δ) (d - δ)) N ≤ cnt u (Set.Icc c d) N :=
        cnt_subset (fun t => indicator_subset hδ t) N
      have h2 : cnt u (Set.Icc (c + δ) (d - δ)) N / (N:ℝ) ≤ cnt u (Set.Icc c d) N / (N:ℝ) := by
        rw [div_eq_inv_mul, div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left hmono (by positivity)
      linarith
    · filter_upwards with N
      have h1 : (0:ℝ) ≤ cnt u (Set.Icc c d) N / (N:ℝ) :=
        div_nonneg (cnt_nonneg u _ N) (by positivity)
      linarith
  have hup : ∀ᶠ N : ℕ in atTop, cnt u (Set.Icc c d) N / (N:ℝ) ≤ (d - c) + ε/2 := by
    have h := cnt_upper_eventually u Hu hc hcd hd hδ hη4
    filter_upwards [h] with N hN
    linarith
  refine eventually_atTop.mp ?_
  filter_upwards [hlow, hup] with N h1 h2
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **Weyl's criterion**: if every nonzero exponential sum of a sequence tends to zero, the
sequence is equidistributed modulo one. -/
theorem weyl_criterion (s : ℕ → ℝ) (H : WeylHyp s) :
    IsEquidistributedModuloOne s := by
  intro c d hcd hsub
  have hc : 0 ≤ c := (hsub ⟨le_rfl, hcd⟩).1
  have hd : d ≤ 1 := (hsub ⟨hcd, le_rfl⟩).2
  have hlim := tendsto_cnt (fun n => Int.fract (s n)) (avgHyp_fract s H) hc hcd hd
  rw [show (d - c) / (1 - 0) = d - c from by norm_num]
  convert hlim using 2
  simp only [cnt]


end

/-- The Fourier average of the sequence `ξ * α ^ (n + 1)` is the exponential sum `nsum`. -/
lemma favg_eq_nsum (α : ℝ) (h : ℤ) (ξ : ℝ) (N : ℕ) :
    favg (fun n : ℕ => ξ * α ^ (n + 1)) h N = nsum α h ξ N := by
  unfold favg nsum psum ez ang
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

/-! ## From the `L²` estimate to almost every `ξ` -/

/-- On any `(-T, T)`, almost every `ξ` satisfies Weyl's hypothesis for `ξ * α ^ (n + 1)`. -/
lemma weylHyp_ae {α : ℝ} (hα : 1 < α) {T : ℝ} (hT : 0 ≤ T) :
    ∀ᵐ ξ ∂(volume.restrict (Set.Ioc (-T) T)),
      WeylHyp (fun n : ℕ => ξ * α ^ (n + 1)) := by
  refine ae_all_iff.mpr fun h => ?_
  by_cases hh : h = 0
  · subst hh
    filter_upwards with ξ hne
    exact absurd rfl hne
  · filter_upwards [ae_tendsto_squares hα h hh hT] with ξ hξ hne
    have h2 : Tendsto (fun N : ℕ => nsum α h ξ N) atTop (𝓝 0) :=
      tendsto_nsum_of_squares α h ξ hξ
    have h3 : (fun N : ℕ => favg (fun n : ℕ => ξ * α ^ (n + 1)) h N)
        = fun N : ℕ => nsum α h ξ N := funext fun N => favg_eq_nsum α h ξ N
    rw [h3]
    exact h2

/-- A property that holds almost everywhere on every `(-M, M)` holds almost everywhere. -/
lemma ae_of_ae_Ioc_all {p : ℝ → Prop}
    (hp : ∀ M : ℕ, ∀ᵐ ξ ∂(volume.restrict (Set.Ioc (-(M:ℝ)) M)), p ξ) :
    ∀ᵐ ξ ∂(volume : Measure ℝ), p ξ := by
  rw [ae_iff]
  have hcover : {ξ : ℝ | ¬ p ξ}
      = ⋃ M : ℕ, {ξ : ℝ | ξ ∈ Set.Ioc (-(M:ℝ)) M ∧ ¬ p ξ} := by
    ext ξ
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro hξ
      refine ⟨⌈|ξ|⌉₊ + 1, ?_, hξ⟩
      obtain ⟨h2, h3⟩ := abs_le.mp (Nat.le_ceil |ξ|)
      refine ⟨by push_cast; linarith, by push_cast; linarith⟩
    · rintro ⟨M, -, hξ⟩
      exact hξ
  rw [hcover]
  refine measure_iUnion_null fun M => ?_
  have h := ae_iff.mp (hp M)
  rw [Measure.restrict_apply' measurableSet_Ioc, Set.inter_comm] at h
  have hset : {ξ : ℝ | ξ ∈ Set.Ioc (-(M:ℝ)) M ∧ ¬ p ξ}
      = Set.Ioc (-(M:ℝ)) M ∩ {ξ : ℝ | ¬ p ξ} := rfl
  rw [hset]
  exact h

end OMA

theorem OMA.solution : type_of% @Bugeaud61.problem_10_61.variants.almost_every := by
  intro α hα
  refine OMA.ae_of_ae_Ioc_all fun M => ?_
  filter_upwards [OMA.weylHyp_ae (α := α) hα (T := (M:ℝ)) (Nat.cast_nonneg M)] with ξ hξ
  exact OMA.weyl_criterion (fun n : ℕ => ξ * α ^ (n + 1)) hξ
