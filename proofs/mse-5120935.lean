import OMAStatements.S_mse_5120935

-- Problem: mse-5120935, Behavior of polynomial roots when removing a single term.
-- Credit: @Andyi955
--
-- Disproof of OMA.S_mse_5120935.main using an explicit counterexample family in P_n(1).
-- Fix r = 1/4 and the Blaschke factor B(z) = (z - 1/4) / (1 - z/4) = sum c_1(k) z^k.
-- For n >= 2400 and m = n / 16, let B(z)^m = sum c(m, k) z^k and let sigma(m, k) be the
-- (k+1)-th Cesaro mean of the partial sums of c(m, .). Set C_m = sum_{k>=1} sigma(m, k-1) r^k,
-- and define P^(n)(z) = z^n - C_m + sum_{k=1}^{n-1} sigma(m, k-1) z^k.
-- Then:
--   1. |sigma(m, k)| <= 1 (by Fejer averaging over N-th roots of unity) and |C_m| <= 1/3,
--      so P^(n) is monic of degree n with all lower coefficients bounded by 1.
--   2. On the open unit disk, H_m(z) := -C_m + sum_{k>=1} sigma(m, k-1) z^k satisfies
--      H_m(z) = (5/3) * sum_{j>=0} ((j+1)/(m+j+1)) * B(z)^(m+j+1), giving tight upper and
--      lower bounds via (1 - v)^2 J_m(v).
--   3. Every root w of P^(n) lies either inside |w - 1/4| < 10^(-5) or outside |w| > 0.95.
--   4. For every k in [4m, 5m), sigma(m, k-1) >= 1/2, so P_k = P^(n) - a_k z^k has no roots
--      in |z - 1/4| <= 4 * 10^(-4). Thus no root of P_k is within eps = 2 * 10^(-4) of any
--      inner root of P^(n), so every non-far root of P_k has |B(zeta)| >= 9/10.
--   5. The algebraic identity prod_{zeta in Z(P_k)} |B(zeta)| = |P_k(1/4)| / |(1/4)^n P_k(4)|
--      <= 6 * (1/4)^k forces at least n / 50 far roots for each k in [4m, 5m), yielding
--      farProportion (P^(n)) (1/5000) >= 1/2000 for all n >= 2400.

namespace OMA.P_mse_5120935

open Polynomial Filter Topology Complex
open scoped BigOperators

noncomputable section

-- ============================================================================
-- Section 1: Blaschke factor, Cauchy-product coefficients, and weighted l1 bound
-- ============================================================================

def B (z : ℂ) : ℂ :=
  (z - (1 / 4 : ℂ)) / (1 - (1 / 4 : ℂ) * z)

def c1 : ℕ → ℝ
  | 0 => -(1 / 4 : ℝ)
  | k + 1 => (15 / 16 : ℝ) * (1 / 4 : ℝ) ^ k

def c : ℕ → ℕ → ℝ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | m + 1, k => ∑ j ∈ Finset.range (k + 1), c m j * c1 (k - j)

def sigma (m k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), (1 - (i : ℝ) / ((k : ℝ) + 1)) * c m i

def Cm (m : ℕ) : ℝ :=
  ∑' k : ℕ, sigma m k * (1 / 4 : ℝ) ^ (k + 1)

def aCoeff (m : ℕ) : ℕ → ℝ
  | 0 => -Cm m
  | k + 1 => sigma m k

def polyP (n : ℕ) : ℂ[X] :=
  if n < 2400 then X ^ n
  else X ^ n + ∑ j ∈ Finset.range n, C (aCoeff (n / 16) j : ℂ) * X ^ j

lemma denom_ne_zero_of_norm_lt_four {z : ℂ} (hz : ‖z‖ < 4) :
    (1 : ℂ) - (1 / 4 : ℂ) * z ≠ 0 := by
  intro h
  have h1 : (1 / 4 : ℂ) * z = 1 := (sub_eq_zero.mp h).symm
  have h2 : ‖(1 / 4 : ℂ) * z‖ = 1 := by rw [h1, norm_one]
  rw [norm_mul, show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num] at h2
  linarith

lemma normSq_denom_sub_num (z : ℂ) :
    Complex.normSq ((1 : ℂ) - (1 / 4 : ℂ) * z) - Complex.normSq (z - (1 / 4 : ℂ)) =
      (15 / 16 : ℝ) * (1 - Complex.normSq z) := by
  simp only [Complex.normSq_apply, sub_re, sub_im, mul_re, mul_im, one_re, one_im,
    div_ofNat_re, div_ofNat_im]
  ring

lemma norm_B_eq_one_of_norm_eq_one {z : ℂ} (hz : ‖z‖ = 1) : ‖B z‖ = 1 := by
  have hd : (1 : ℂ) - (1 / 4 : ℂ) * z ≠ 0 := denom_ne_zero_of_norm_lt_four (by linarith)
  rw [B, norm_div, div_eq_one_iff_eq (norm_ne_zero_iff.mpr hd)]
  have hns : Complex.normSq z = 1 := by rw [← Complex.sq_norm, hz]; norm_num
  have hdiff := normSq_denom_sub_num z
  rw [hns] at hdiff
  have hsq : ‖z - (1 / 4 : ℂ)‖ ^ 2 = ‖(1 : ℂ) - (1 / 4 : ℂ) * z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    linarith
  nlinarith [norm_nonneg (z - (1 / 4 : ℂ)), norm_nonneg ((1 : ℂ) - (1 / 4 : ℂ) * z)]

lemma norm_B_lt_one_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) : ‖B z‖ < 1 := by
  have hd : (1 : ℂ) - (1 / 4 : ℂ) * z ≠ 0 := denom_ne_zero_of_norm_lt_four (by linarith)
  rw [B, norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  have hns : Complex.normSq z < 1 := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  have hdiff := normSq_denom_sub_num z
  have hsq : ‖z - (1 / 4 : ℂ)‖ ^ 2 < ‖(1 : ℂ) - (1 / 4 : ℂ) * z‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    linarith
  nlinarith [norm_nonneg (z - (1 / 4 : ℂ)), norm_nonneg ((1 : ℂ) - (1 / 4 : ℂ) * z)]

lemma one_le_norm_B_of_one_le_norm {z : ℂ} (hz : 1 ≤ ‖z‖) (hz4 : z ≠ 4) : 1 ≤ ‖B z‖ := by
  have hd : (1 : ℂ) - (1 / 4 : ℂ) * z ≠ 0 := by
    intro h
    apply hz4
    linear_combination -4 * h
  rw [B, norm_div, one_le_div (norm_pos_iff.mpr hd)]
  have hns : 1 ≤ Complex.normSq z := by
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg z]
  have hdiff := normSq_denom_sub_num z
  have hsq : ‖(1 : ℂ) - (1 / 4 : ℂ) * z‖ ^ 2 ≤ ‖z - (1 / 4 : ℂ)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm]
    linarith
  nlinarith [norm_nonneg (z - (1 / 4 : ℂ)), norm_nonneg ((1 : ℂ) - (1 / 4 : ℂ) * z)]

lemma norm_B_ge_of_norm_lt_one {z : ℂ} (hz1 : ‖z‖ < 1) (hzr : 1 / 4 ≤ ‖z‖) :
    (‖z‖ - 1 / 4) / (1 - ‖z‖ / 4) ≤ ‖B z‖ := by
  have hd : (1 : ℂ) - (1 / 4 : ℂ) * z ≠ 0 := denom_ne_zero_of_norm_lt_four (by linarith)
  have hd_pos : (0 : ℝ) < 1 - ‖z‖ / 4 := by linarith
  rw [B, norm_div, div_le_div_iff₀ hd_pos (norm_pos_iff.mpr hd)]
  have hre : z.re ≤ ‖z‖ := Complex.re_le_norm z
  have hsq_z : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply] at this
    linarith
  have hns1 : ‖z - (1 / 4 : ℂ)‖ ^ 2 = ‖z‖ ^ 2 - z.re / 2 + 1 / 16 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, sub_im, div_ofNat_re, div_ofNat_im, one_re, one_im]
    nlinarith
  have hns2 : ‖(1 : ℂ) - (1 / 4 : ℂ) * z‖ ^ 2 = 1 - z.re / 2 + ‖z‖ ^ 2 / 16 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, sub_im, mul_re, mul_im, one_re, one_im, div_ofNat_re, div_ofNat_im]
    nlinarith
  have hdiff : (1 - ‖z‖ / 4) ^ 2 * ‖z - (1 / 4 : ℂ)‖ ^ 2 -
      (‖z‖ - 1 / 4) ^ 2 * ‖(1 : ℂ) - (1 / 4 : ℂ) * z‖ ^ 2 =
      (15 / 32 : ℝ) * (1 - ‖z‖ ^ 2) * (‖z‖ - z.re) := by
    rw [hns1, hns2]; ring
  have hnonneg : 0 ≤ (15 / 32 : ℝ) * (1 - ‖z‖ ^ 2) * (‖z‖ - z.re) := by
    have h1 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have h2 : 0 ≤ ‖z‖ - z.re := by linarith
    positivity
  have hsq : ((‖z‖ - 1 / 4) * ‖(1 : ℂ) - (1 / 4 : ℂ) * z‖) ^ 2 ≤
      (‖z - (1 / 4 : ℂ)‖ * (1 - ‖z‖ / 4)) ^ 2 := by
    nlinarith
  have hL : 0 ≤ (‖z‖ - 1 / 4) * ‖(1 : ℂ) - (1 / 4 : ℂ) * z‖ :=
    mul_nonneg (by linarith) (norm_nonneg _)
  have hR : 0 ≤ ‖z - (1 / 4 : ℂ)‖ * (1 - ‖z‖ / 4) :=
    mul_nonneg (norm_nonneg _) (le_of_lt hd_pos)
  nlinarith

lemma norm_B_le_of_norm_le {z : ℂ} {R : ℝ} (hR : R < 1) (hz : ‖z‖ ≤ R) :
    ‖B z‖ ≤ (R + 1 / 4) / (1 + R / 4) := by
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz hR
  have hd : (1 : ℂ) - (1 / 4 : ℂ) * z ≠ 0 := denom_ne_zero_of_norm_lt_four (by linarith)
  have hR0 : 0 ≤ R := le_trans (norm_nonneg z) hz
  have hdR : (0 : ℝ) < 1 + R / 4 := by linarith
  rw [B, norm_div, div_le_div_iff₀ (norm_pos_iff.mpr hd) hdR]
  have hre : -‖z‖ ≤ z.re := neg_le_of_abs_le (Complex.abs_re_le_norm z)
  have hsq_z : z.re ^ 2 + z.im ^ 2 = ‖z‖ ^ 2 := by
    have := Complex.sq_norm z
    rw [Complex.normSq_apply] at this
    linarith
  have hns1 : ‖z - (1 / 4 : ℂ)‖ ^ 2 = ‖z‖ ^ 2 - z.re / 2 + 1 / 16 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, sub_im, div_ofNat_re, div_ofNat_im, one_re, one_im]
    nlinarith
  have hns2 : ‖(1 : ℂ) - (1 / 4 : ℂ) * z‖ ^ 2 = 1 - z.re / 2 + ‖z‖ ^ 2 / 16 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [sub_re, sub_im, mul_re, mul_im, one_re, one_im, div_ofNat_re, div_ofNat_im]
    nlinarith
  have hdiff1 : (‖z‖ + 1 / 4) ^ 2 * ‖(1 : ℂ) - (1 / 4 : ℂ) * z‖ ^ 2 -
      (1 + ‖z‖ / 4) ^ 2 * ‖z - (1 / 4 : ℂ)‖ ^ 2 =
      (15 / 32 : ℝ) * (1 - ‖z‖ ^ 2) * (‖z‖ + z.re) := by
    rw [hns1, hns2]; ring
  have hnonneg1 : 0 ≤ (15 / 32 : ℝ) * (1 - ‖z‖ ^ 2) * (‖z‖ + z.re) := by
    have h1 : 0 ≤ 1 - ‖z‖ ^ 2 := by nlinarith [norm_nonneg z]
    have h2 : 0 ≤ ‖z‖ + z.re := by linarith
    positivity
  have hle1 : ‖z - (1 / 4 : ℂ)‖ * (1 + ‖z‖ / 4) ≤ (‖z‖ + 1 / 4) * ‖(1 : ℂ) - (1 / 4 : ℂ) * z‖ := by
    have hL : 0 ≤ ‖z - (1 / 4 : ℂ)‖ * (1 + ‖z‖ / 4) :=
      mul_nonneg (norm_nonneg _) (by linarith [norm_nonneg z])
    have hR' : 0 ≤ (‖z‖ + 1 / 4) * ‖(1 : ℂ) - (1 / 4 : ℂ) * z‖ :=
      mul_nonneg (by linarith [norm_nonneg z]) (norm_nonneg _)
    nlinarith
  have hmon : (‖z‖ + 1 / 4) / (1 + ‖z‖ / 4) ≤ (R + 1 / 4) / (1 + R / 4) := by
    rw [div_le_div_iff₀ (by linarith [norm_nonneg z]) hdR]
    nlinarith
  have hdiv1 : ‖z - (1 / 4 : ℂ)‖ / ‖(1 : ℂ) - (1 / 4 : ℂ) * z‖ ≤ (‖z‖ + 1 / 4) / (1 + ‖z‖ / 4) := by
    rw [div_le_div_iff₀ (norm_pos_iff.mpr hd) (by linarith [norm_nonneg z])]
    exact hle1
  have hfin := le_trans hdiv1 hmon
  rw [div_le_div_iff₀ (norm_pos_iff.mpr hd) hdR] at hfin
  exact hfin

-- Weighted l1 bound for c1 and c m at rho = 2

lemma hasSum_c1_abs_two_pow : HasSum (fun k : ℕ => |c1 k| * (2 : ℝ) ^ k) 4 := by
  have hgeom0 : HasSum (fun k : ℕ => (15 / 8 : ℝ) * (1 / 2 : ℝ) ^ k)
      ((15 / 8 : ℝ) * (1 - (1 / 2 : ℝ))⁻¹) :=
    (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left (15 / 8 : ℝ)
  have hval0 : (15 / 8 : ℝ) * (1 - (1 / 2 : ℝ))⁻¹ = 15 / 4 := by norm_num
  rw [hval0] at hgeom0
  have hshift : HasSum (fun k : ℕ => |c1 (k + 1)| * (2 : ℝ) ^ (k + 1)) (15 / 4 : ℝ) := by
    refine hgeom0.congr_fun (fun k => ?_)
    have hpos : (0 : ℝ) ≤ (15 / 16 : ℝ) * (1 / 4 : ℝ) ^ k := by positivity
    simp only [c1, abs_of_nonneg hpos]
    have hpow : (1 / 4 : ℝ) ^ k * (2 : ℝ) ^ k = (1 / 2 : ℝ) ^ k := by
      rw [← mul_pow]; norm_num
    rw [pow_succ, show (15 / 16 : ℝ) * (1 / 4 : ℝ) ^ k * ((2 : ℝ) ^ k * 2) =
      (15 / 8 : ℝ) * ((1 / 4 : ℝ) ^ k * (2 : ℝ) ^ k) by ring, hpow]
  rw [← hasSum_nat_add_iff' 1]
  rw [Finset.sum_range_one]
  have hsub : (4 : ℝ) - |c1 0| * (2 : ℝ) ^ 0 = 15 / 4 := by simp [c1]; norm_num
  rw [hsub]
  exact hshift

lemma summable_cauchy_nonneg {f g : ℕ → ℝ} (hf0 : ∀ k, 0 ≤ f k) (hg0 : ∀ k, 0 ≤ g k)
    (hf : Summable f) (hg : Summable g) :
    Summable (fun n => ∑ j ∈ Finset.range (n + 1), f j * g (n - j)) ∧
      ∑' n, (∑ j ∈ Finset.range (n + 1), f j * g (n - j)) ≤ (∑' j, f j) * (∑' i, g i) := by
  have hbound : ∀ s : Finset ℕ,
      ∑ n ∈ s, (∑ j ∈ Finset.range (n + 1), f j * g (n - j)) ≤ (∑' j, f j) * (∑' i, g i) := by
    intro s
    set N := s.sup id + 1
    have hs : s ⊆ Finset.range N := by
      intro n hn
      rw [Finset.mem_range]
      exact Nat.lt_succ_of_le (Finset.le_sup (f := id) hn)
    have h1 : ∑ n ∈ s, (∑ j ∈ Finset.range (n + 1), f j * g (n - j)) ≤
        ∑ n ∈ Finset.range N, (∑ j ∈ Finset.range (n + 1), f j * g (n - j)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun n _ _ =>
        Finset.sum_nonneg (fun j _ => mul_nonneg (hf0 j) (hg0 _)))
    have h2 : ∑ n ∈ Finset.range N, (∑ j ∈ Finset.range (n + 1), f j * g (n - j)) ≤
        (∑ j ∈ Finset.range N, f j) * (∑ i ∈ Finset.range N, g i) := by
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      have hcard : ∀ n ∈ Finset.range N,
          ∑ j ∈ Finset.range (n + 1), f j * g (n - j) =
            ∑ p ∈ (Finset.range N ×ˢ Finset.range N).filter (fun p => p.1 + p.2 = n),
              f p.1 * g p.2 := by
        intro n hn
        rw [Finset.mem_range] at hn
        refine Finset.sum_nbij (fun j => (j, n - j)) ?_ ?_ ?_ ?_
        · intro j hj
          rw [Finset.mem_range] at hj
          rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
          exact ⟨⟨by omega, by omega⟩, by omega⟩
        · intro j1 _ j2 _ h
          exact (Prod.mk.inj h).1
        · intro p hp
          rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hp
          refine ⟨p.1, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), ?_⟩
          ext
          · dsimp
          · dsimp; omega
        · intro j _; rfl
      rw [Finset.sum_congr rfl hcard, ← Finset.sum_biUnion]
      · refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun (p : ℕ × ℕ) _ _ => mul_nonneg (hf0 p.1) (hg0 p.2))
        intro p hp
        rw [Finset.mem_biUnion] at hp
        rcases hp with ⟨_, _, hp'⟩
        exact (Finset.mem_filter.mp hp').1
      · intro n1 _ n2 _ hne
        simp only [Function.onFun, Finset.disjoint_left]
        intro p hp1 hp2
        have e1 := (Finset.mem_filter.mp hp1).2
        have e2 := (Finset.mem_filter.mp hp2).2
        exact hne (e1.symm.trans e2)
    have h3 : (∑ j ∈ Finset.range N, f j) * (∑ i ∈ Finset.range N, g i) ≤
        (∑' j, f j) * (∑' i, g i) := by
      refine mul_le_mul (hf.sum_le_tsum (Finset.range N) (fun j _ => hf0 j))
        (hg.sum_le_tsum (Finset.range N) (fun i _ => hg0 i))
        (Finset.sum_nonneg (fun i _ => hg0 i))
        (tsum_nonneg hf0)
    linarith
  have hsum : Summable (fun n => ∑ j ∈ Finset.range (n + 1), f j * g (n - j)) :=
    summable_of_sum_le (fun n => Finset.sum_nonneg (fun j _ => mul_nonneg (hf0 j) (hg0 _))) hbound
  exact ⟨hsum, hsum.tsum_le_of_sum_le hbound⟩

lemma c_weighted_l1 (m : ℕ) :
    Summable (fun k => |c m k| * (2 : ℝ) ^ k) ∧
      ∑' k, |c m k| * (2 : ℝ) ^ k ≤ (4 : ℝ) ^ m := by
  induction m with
  | zero =>
    have h0 : ∀ k, |c 0 k| * (2 : ℝ) ^ k = if k = 0 then 1 else 0 := by
      intro k
      cases k with
      | zero => simp [c]
      | succ k => simp [c]
    simp_rw [h0]
    exact ⟨summable_of_ne_finset_zero (s := {0}) (fun k hk => by simp_all),
      by rw [tsum_ite_eq]; norm_num⟩
  | succ m ih =>
    have hc1 := hasSum_c1_abs_two_pow
    obtain ⟨hsum_prod, hle_prod⟩ := summable_cauchy_nonneg
      (fun k => mul_nonneg (abs_nonneg _) (by positivity))
      (fun k => mul_nonneg (abs_nonneg _) (by positivity))
      ih.1 hc1.summable
    have hdom : ∀ k, |c (m + 1) k| * (2 : ℝ) ^ k ≤
        ∑ j ∈ Finset.range (k + 1), (|c m j| * (2 : ℝ) ^ j) * (|c1 (k - j)| * (2 : ℝ) ^ (k - j)) := by
      intro k
      calc |c (m + 1) k| * (2 : ℝ) ^ k
          = |∑ j ∈ Finset.range (k + 1), c m j * c1 (k - j)| * (2 : ℝ) ^ k := rfl
        _ ≤ (∑ j ∈ Finset.range (k + 1), |c m j * c1 (k - j)|) * (2 : ℝ) ^ k :=
            mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) (by positivity)
        _ = ∑ j ∈ Finset.range (k + 1), |c m j * c1 (k - j)| * (2 : ℝ) ^ k := Finset.sum_mul ..
        _ = ∑ j ∈ Finset.range (k + 1), (|c m j| * (2 : ℝ) ^ j) * (|c1 (k - j)| * (2 : ℝ) ^ (k - j)) := by
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [Finset.mem_range] at hj
            rw [abs_mul]
            have hpow : (2 : ℝ) ^ j * (2 : ℝ) ^ (k - j) = (2 : ℝ) ^ k := by
              rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp hj)]
            rw [← hpow]; ring
    have hsum : Summable (fun k => |c (m + 1) k| * (2 : ℝ) ^ k) :=
      Summable.of_nonneg_of_le (fun k => mul_nonneg (abs_nonneg _) (by positivity)) hdom hsum_prod
    have hle : ∑' k, |c (m + 1) k| * (2 : ℝ) ^ k ≤ (4 : ℝ) ^ (m + 1) := by
      calc ∑' k, |c (m + 1) k| * (2 : ℝ) ^ k
          ≤ ∑' k, ∑ j ∈ Finset.range (k + 1), (|c m j| * (2 : ℝ) ^ j) * (|c1 (k - j)| * (2 : ℝ) ^ (k - j)) :=
            hsum.tsum_le_tsum hdom hsum_prod
        _ ≤ (∑' j, |c m j| * (2 : ℝ) ^ j) * (∑' i, |c1 i| * (2 : ℝ) ^ i) := hle_prod
        _ = (∑' j, |c m j| * (2 : ℝ) ^ j) * 4 := by rw [hc1.tsum_eq]
        _ ≤ (4 : ℝ) ^ m * 4 := by linarith [ih.2]
        _ = (4 : ℝ) ^ (m + 1) := by rw [pow_succ]
    exact ⟨hsum, hle⟩

lemma abs_c_le (m k : ℕ) : |c m k| ≤ (4 : ℝ) ^ m / (2 : ℝ) ^ k := by
  have h1 := (c_weighted_l1 m).1
  have h2 := (c_weighted_l1 m).2
  have hle : |c m k| * (2 : ℝ) ^ k ≤ ∑' j, |c m j| * (2 : ℝ) ^ j :=
    h1.le_tsum k (fun j _ => mul_nonneg (abs_nonneg _) (by positivity))
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ k)]
  exact le_trans hle h2

lemma summable_norm_c_mul_pow (m : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 2) :
    Summable (fun k => ‖(c m k : ℂ) * z ^ k‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) (c_weighted_l1 m).1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz k) (abs_nonneg _)

lemma hasSum_c1_pow {z : ℂ} (hz : ‖z‖ ≤ 2) :
    HasSum (fun k : ℕ => (c1 k : ℂ) * z ^ k) (B z) := by
  have hzr : ‖(1 / 4 : ℂ) * z‖ < 1 := by
    rw [norm_mul, show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num]
    linarith
  have hgeom := hasSum_geometric_of_norm_lt_one hzr
  have hscaled := hgeom.mul_left ((15 / 16 : ℂ) * z)
  have hshift : HasSum (fun k : ℕ => (c1 (k + 1) : ℂ) * z ^ (k + 1))
      ((15 / 16 : ℂ) * z * ((1 : ℂ) - (1 / 4 : ℂ) * z)⁻¹) := by
    refine hscaled.congr_fun (fun k => ?_)
    simp only [c1, ofReal_mul, ofReal_pow, ofReal_div, ofReal_ofNat, ofReal_one]
    rw [mul_pow, pow_succ]
    ring
  have hval : (15 / 16 : ℂ) * z * ((1 : ℂ) - (1 / 4 : ℂ) * z)⁻¹ + (c1 0 : ℂ) * z ^ 0 = B z := by
    have hd : (1 : ℂ) - (1 / 4 : ℂ) * z ≠ 0 := denom_ne_zero_of_norm_lt_four (by linarith)
    have h4z : (4 : ℂ) - z ≠ 0 := by
      intro h; apply hd; linear_combination h / 4
    simp only [c1, pow_zero, mul_one, ofReal_neg, ofReal_div, ofReal_one, ofReal_ofNat, B]
    field_simp [hd, h4z]
    ring
  have hfull2 : HasSum (fun k => (c1 k : ℂ) * z ^ k)
      ((15 / 16 : ℂ) * z * ((1 : ℂ) - (1 / 4 : ℂ) * z)⁻¹ + (c1 0 : ℂ) * z ^ 0) := by
    rw [← hasSum_nat_add_iff' 1]
    rw [Finset.sum_range_one, add_sub_cancel_right]
    exact hshift
  rw [hval] at hfull2
  exact hfull2

lemma tsum_c_pow (m : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 2) :
    ∑' k : ℕ, (c m k : ℂ) * z ^ k = B z ^ m := by
  induction m with
  | zero =>
    have h0 : ∀ k, (c 0 k : ℂ) * z ^ k = if k = 0 then 1 else 0 := by
      intro k
      cases k with
      | zero => simp [c]
      | succ k => simp [c]
    simp_rw [h0]
    rw [tsum_ite_eq, pow_zero]
  | succ m ih =>
    have h1 : Summable (fun k => ‖(c m k : ℂ) * z ^ k‖) := summable_norm_c_mul_pow m hz
    have h2 : Summable (fun k => ‖(c1 k : ℂ) * z ^ k‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_)
        hasSum_c1_abs_two_pow.summable
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg z) hz k) (abs_nonneg _)
    have hmul := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm h1 h2
    rw [ih, (hasSum_c1_pow hz).tsum_eq, ← pow_succ] at hmul
    rw [hmul]
    congr 1
    ext k
    simp only [c, ofReal_sum, ofReal_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    rw [Finset.mem_range] at hj
    have hpow : z ^ j * z ^ (k - j) = z ^ k := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp hj)]
    calc (c m j : ℂ) * (c1 (k - j) : ℂ) * z ^ k
        = (c m j : ℂ) * (c1 (k - j) : ℂ) * (z ^ j * z ^ (k - j)) := by rw [hpow]
      _ = (c m j : ℂ) * z ^ j * ((c1 (k - j) : ℂ) * z ^ (k - j)) := by ring

lemma tsum_c_eq_one (m : ℕ) : ∑' k : ℕ, c m k = 1 := by
  have h := tsum_c_pow m (z := 1) (by norm_num)
  have hB1 : B 1 = 1 := by simp [B]; norm_num
  rw [hB1, one_pow] at h
  simp only [one_pow, mul_one] at h
  rw [← Complex.ofReal_tsum] at h
  exact Complex.ofReal_injective h

lemma summable_c (m : ℕ) : Summable (fun k => c m k) := by
  have h := summable_norm_c_mul_pow m (z := 1) (by norm_num)
  simp only [one_pow, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  exact h.of_abs

lemma summable_nat_mul_abs_c (m : ℕ) : Summable (fun k : ℕ => (k : ℝ) * |c m k|) := by
  have hdom : ∀ k : ℕ, (k : ℝ) * |c m k| ≤ |c m k| * (2 : ℝ) ^ k := by
    intro k
    have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by
      have : k ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
      exact_mod_cast this
    nlinarith [abs_nonneg (c m k)]
  exact Summable.of_nonneg_of_le (fun k => mul_nonneg (Nat.cast_nonneg k) (abs_nonneg _))
    hdom (c_weighted_l1 m).1

lemma summable_nat_mul_c (m : ℕ) : Summable (fun k : ℕ => (k : ℝ) * c m k) := by
  refine (summable_nat_mul_abs_c m).of_norm_bounded (fun k => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]

lemma tsum_nat_mul_c1 : ∑' k : ℕ, (k : ℝ) * c1 k = 5 / 3 := by
  have ha := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 4 : ℝ)) (by norm_num)
  have hb := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)
  have hc := ha.add hb
  have hval1 : (1 / 4 : ℝ) / (1 - (1 / 4 : ℝ)) ^ 2 + (1 - (1 / 4 : ℝ))⁻¹ = 16 / 9 := by norm_num
  rw [hval1] at hc
  have h1 : HasSum (fun k : ℕ => ((k : ℝ) + 1) * (1 / 4 : ℝ) ^ k) (16 / 9 : ℝ) :=
    hc.congr_fun (fun k => by ring)
  have h2 := h1.mul_left (15 / 16 : ℝ)
  have hval2 : (15 / 16 : ℝ) * (16 / 9 : ℝ) = 5 / 3 := by norm_num
  rw [hval2] at h2
  have h3 : HasSum (fun k : ℕ => ((k + 1 : ℕ) : ℝ) * c1 (k + 1)) (5 / 3 : ℝ) :=
    h2.congr_fun (fun k => by simp only [c1, Nat.cast_add, Nat.cast_one]; ring)
  have h4 : HasSum (fun k : ℕ => (k : ℝ) * c1 k) (5 / 3 : ℝ) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, Nat.cast_zero, zero_mul, sub_zero]
    exact h3
  exact h4.tsum_eq

lemma tsum_c1_eq_one : ∑' k : ℕ, c1 k = 1 := by
  have h := (hasSum_c1_pow (z := 1) (by norm_num)).tsum_eq
  have hB1 : B 1 = 1 := by simp [B]; norm_num
  rw [hB1] at h
  simp only [one_pow, mul_one] at h
  rw [← Complex.ofReal_tsum] at h
  exact Complex.ofReal_injective h

lemma summable_abs_c1 : Summable (fun k : ℕ => |c1 k|) := by
  refine Summable.of_nonneg_of_le (fun _ => abs_nonneg _) (fun k => ?_)
    hasSum_c1_abs_two_pow.summable
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  nlinarith [abs_nonneg (c1 k)]

lemma summable_nat_mul_abs_c1 : Summable (fun k : ℕ => (k : ℝ) * |c1 k|) := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Nat.cast_nonneg k) (abs_nonneg _))
    (fun k => ?_) hasSum_c1_abs_two_pow.summable
  have hk : (k : ℝ) ≤ (2 : ℝ) ^ k := by
    have : k ≤ 2 ^ k := Nat.le_of_lt Nat.lt_two_pow_self
    exact_mod_cast this
  nlinarith [abs_nonneg (c1 k)]

lemma tsum_nat_mul_c (m : ℕ) : ∑' k : ℕ, (k : ℝ) * c m k = (5 / 3 : ℝ) * m := by
  induction m with
  | zero =>
    have h0 : ∀ k : ℕ, (k : ℝ) * c 0 k = 0 := by
      intro k; cases k <;> simp [c]
    simp_rw [h0]; simp
  | succ m ih =>
    have h1 : Summable (fun k : ℕ => ‖(k : ℝ) * c m k‖) := by
      refine (summable_nat_mul_abs_c m).congr (fun k => ?_)
      rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    have h2 : Summable (fun k : ℕ => ‖c1 k‖) := by
      simpa [Real.norm_eq_abs] using summable_abs_c1
    have h3 : Summable (fun k : ℕ => ‖c m k‖) := by
      have := summable_norm_c_mul_pow m (z := 1) (by norm_num)
      simpa [Real.norm_eq_abs, Complex.norm_real] using this
    have h4 : Summable (fun k : ℕ => ‖(k : ℝ) * c1 k‖) := by
      refine (summable_nat_mul_abs_c1).congr (fun k => ?_)
      rw [Real.norm_eq_abs, abs_mul, Nat.abs_cast]
    have hA := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm h1 h2
    have hB := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm h3 h4
    have hsumA : Summable (fun n => ∑ j ∈ Finset.range (n + 1), ((j : ℝ) * c m j) * c1 (n - j)) := by
      have := (summable_cauchy_nonneg
        (fun k : ℕ => mul_nonneg (Nat.cast_nonneg k) (abs_nonneg (c m k)))
        (fun k : ℕ => abs_nonneg (c1 k))
        (summable_nat_mul_abs_c m) summable_abs_c1).1
      refine this.of_norm_bounded (fun n => ?_)
      calc ‖∑ j ∈ Finset.range (n + 1), ((j : ℝ) * c m j) * c1 (n - j)‖
          ≤ ∑ j ∈ Finset.range (n + 1), ‖((j : ℝ) * c m j) * c1 (n - j)‖ := norm_sum_le _ _
        _ = ∑ j ∈ Finset.range (n + 1), (j : ℝ) * |c m j| * |c1 (n - j)| := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Real.norm_eq_abs, abs_mul, abs_mul, Nat.abs_cast]
    have hsumB : Summable (fun n => ∑ j ∈ Finset.range (n + 1), c m j * (((n - j : ℕ) : ℝ) * c1 (n - j))) := by
      have := (summable_cauchy_nonneg
        (fun k : ℕ => abs_nonneg (c m k))
        (fun k : ℕ => mul_nonneg (Nat.cast_nonneg k) (abs_nonneg (c1 k)))
        (by simpa [Real.norm_eq_abs] using h3) summable_nat_mul_abs_c1).1
      refine this.of_norm_bounded (fun n => ?_)
      calc ‖∑ j ∈ Finset.range (n + 1), c m j * (((n - j : ℕ) : ℝ) * c1 (n - j))‖
          ≤ ∑ j ∈ Finset.range (n + 1), ‖c m j * (((n - j : ℕ) : ℝ) * c1 (n - j))‖ := norm_sum_le _ _
        _ = ∑ j ∈ Finset.range (n + 1), |c m j| * ((n - j : ℕ) * |c1 (n - j)|) := by
            refine Finset.sum_congr rfl (fun j _ => ?_)
            rw [Real.norm_eq_abs, abs_mul, abs_mul, Nat.abs_cast]
    have hEq : (fun k : ℕ => (k : ℝ) * c (m + 1) k) =
        fun k => (∑ j ∈ Finset.range (k + 1), ((j : ℝ) * c m j) * c1 (k - j)) +
          (∑ j ∈ Finset.range (k + 1), c m j * (((k - j : ℕ) : ℝ) * c1 (k - j))) := by
      ext k
      rw [c, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j hj => ?_)
      rw [Finset.mem_range] at hj
      have hjk : (j : ℝ) + ((k - j : ℕ) : ℝ) = (k : ℝ) := by
        exact_mod_cast Nat.add_sub_of_le (Nat.lt_succ_iff.mp hj)
      linear_combination -(c m j * c1 (k - j)) * hjk
    rw [hEq, hsumA.tsum_add hsumB, ← hA, ← hB, ih, tsum_c1_eq_one, tsum_c_eq_one, tsum_nat_mul_c1]
    push_cast
    ring

-- ============================================================================
-- Section 2: Fejer bound |sigma m k| <= 1, |Cm m| <= 1/3, and sigma m k >= 1/2
-- ============================================================================

lemma sum_root_of_unity (N : ℕ) (hN : 0 < N) (d : ℤ) :
    ∑ t ∈ Finset.range N, (Complex.exp (2 * Real.pi * Complex.I / (N : ℂ)) ^ t) ^ d =
      if (N : ℤ) ∣ d then (N : ℂ) else 0 := by
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN)
  have hterm : ∀ t : ℕ, (ω ^ t) ^ d = (ω ^ d) ^ t := by
    intro t
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
  simp_rw [hterm]
  have hωd : ω ^ d = Complex.exp (2 * Real.pi * Complex.I * (d : ℂ) / (N : ℂ)) := by
    rw [← Complex.exp_int_mul]
    congr 1; ring
  split_ifs with hd
  · obtain ⟨q, rfl⟩ := hd
    have h1 : ω ^ ((N : ℤ) * q) = 1 := by
      rw [hωd]
      have heq : 2 * ↑Real.pi * I * ↑((N : ℤ) * q) / ↑N = (q : ℂ) * (2 * ↑Real.pi * I) := by
        push_cast; field_simp [hN0]
      rw [heq, Complex.exp_int_mul_two_pi_mul_I]
    simp [h1]
  · have hne : ω ^ d ≠ 1 := by
      intro h1
      rw [hωd, Complex.exp_eq_one_iff] at h1
      obtain ⟨q, hq⟩ := h1
      have h2pi : (2 * ↑Real.pi * I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hq' : (d : ℂ) = (N : ℂ) * (q : ℂ) := by
        have hmul : (2 * ↑Real.pi * I : ℂ) * (d : ℂ) = (2 * ↑Real.pi * I : ℂ) * ((N : ℂ) * (q : ℂ)) := by
          have := congr_arg (· * (N : ℂ)) hq
          rw [div_mul_cancel₀ _ hN0] at this
          linear_combination this
        exact mul_left_cancel₀ h2pi hmul
      have hdz : d = (N : ℤ) * q := by exact_mod_cast hq'
      exact hd ⟨q, hdz⟩
    have hgeom : (ω ^ d - 1) * ∑ t ∈ Finset.range N, (ω ^ d) ^ t = (ω ^ d) ^ N - 1 := by
      rw [mul_comm]
      exact geom_sum_mul (ω ^ d) N
    have hωN : ω ^ N = 1 := by
      rw [← Complex.exp_nat_mul]
      have heq2 : (N : ℂ) * (2 * ↑Real.pi * I / ↑N) = 2 * ↑Real.pi * I := by
        field_simp [hN0]
      rw [heq2, Complex.exp_two_pi_mul_I]
    have hpowN : (ω ^ d) ^ N = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hωN, one_zpow]
    rw [hpowN, sub_self] at hgeom
    exact (mul_eq_zero.mp hgeom).resolve_left (sub_ne_zero.mpr hne)

lemma abs_sigma_le_one (m k : ℕ) : |sigma m k| ≤ 1 := by
  suffices hlim : ∀ ε : ℝ, 0 < ε → |sigma m k| ≤ 1 + ε by
    by_contra h
    push Not at h
    have hε : 0 < (|sigma m k| - 1) / 2 := by linarith
    have := hlim _ hε
    linarith
  intro ε hε
  have htend : Tendsto (fun N : ℕ => ((k : ℝ) + 1) * (4 : ℝ) ^ m * 2 * (1 / 2 : ℝ) ^ (N - k))
      atTop (𝓝 0) := by
    have h0 : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ N) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have h1 : Tendsto (fun N : ℕ => (1 / 2 : ℝ) ^ (N - k)) atTop (𝓝 0) := by
      rw [← tendsto_add_atTop_iff_nat k]
      simpa [Nat.add_sub_cancel] using h0
    simpa using h1.const_mul (((k : ℝ) + 1) * (4 : ℝ) ^ m * 2)
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N0, hN0⟩ := htend ε hε
  set N := max N0 (2 * (k + 1) + 1)
  have hN_gt : 2 * (k + 1) < N := lt_of_lt_of_le (by omega) (le_max_right _ _)
  have hN_pos : 0 < N := by omega
  have hN_tail : ((k : ℝ) + 1) * (4 : ℝ) ^ m * 2 * (1 / 2 : ℝ) ^ (N - k) < ε := by
    have h := hN0 N (le_max_left _ _)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at h
    exact h
  set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I / (N : ℂ))
  have hω_norm : ‖ω‖ = 1 := by
    have harg : (2 * ↑Real.pi * I / (N : ℂ)) = ((2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [show ω = Complex.exp (((2 * Real.pi / (N : ℝ) : ℝ) : ℂ) * I) by rw [← harg]]
    exact Complex.norm_exp_ofReal_mul_I _
  have hωt_norm : ∀ t : ℕ, ‖ω ^ t‖ = 1 := fun t => by rw [norm_pow, hω_norm, one_pow]
  have hωt_inv : ∀ t : ℕ, (ω ^ t)⁻¹ = starRingEnd ℂ (ω ^ t) := by
    intro t
    have h := Complex.mul_conj (ω ^ t)
    rw [Complex.normSq_eq_norm_sq, hωt_norm t, one_pow, ofReal_one] at h
    exact inv_eq_of_mul_eq_one_right h
  let K : ℕ → ℂ := fun t =>
    (∑ u ∈ Finset.range (k + 1), (ω ^ t) ^ u) *
      (∑ v ∈ Finset.range (k + 1), (ω ^ t)⁻¹ ^ v)
  let SN : ℂ := (1 / ((N : ℂ) * ((k : ℂ) + 1))) *
    ∑ t ∈ Finset.range N, B (ω ^ t) ^ m * K t
  have hK_real : ∀ t : ℕ, K t = ((‖∑ u ∈ Finset.range (k + 1), (ω ^ t) ^ u‖ ^ 2 : ℝ) : ℂ) := by
    intro t
    dsimp [K]
    have hconj : ∑ v ∈ Finset.range (k + 1), (ω ^ t)⁻¹ ^ v =
        starRingEnd ℂ (∑ u ∈ Finset.range (k + 1), (ω ^ t) ^ u) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [map_pow, ← hωt_inv t]
    rw [hconj, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hK_sum : ∑ t ∈ Finset.range N, K t = (N : ℂ) * ((k : ℂ) + 1) := by
    have hexp : ∀ t : ℕ, K t = ∑ u ∈ Finset.range (k + 1), ∑ v ∈ Finset.range (k + 1),
        (ω ^ t) ^ ((u : ℤ) - (v : ℤ)) := by
      intro t
      dsimp [K]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      have hne : ω ^ t ≠ 0 := pow_ne_zero t (Complex.exp_ne_zero _)
      rw [inv_pow, ← zpow_natCast (ω ^ t) u, ← zpow_natCast (ω ^ t) v, ← div_eq_mul_inv,
        ← zpow_sub₀ hne]
    rw [Finset.sum_congr rfl (fun t _ => hexp t)]
    rw [Finset.sum_comm]
    have hswap : ∑ u ∈ Finset.range (k + 1), ∑ t ∈ Finset.range N,
        ∑ v ∈ Finset.range (k + 1), (ω ^ t) ^ ((u : ℤ) - (v : ℤ)) =
        ∑ u ∈ Finset.range (k + 1), ∑ v ∈ Finset.range (k + 1),
        ∑ t ∈ Finset.range N, (ω ^ t) ^ ((u : ℤ) - (v : ℤ)) :=
      Finset.sum_congr rfl (fun u _ => Finset.sum_comm)
    rw [hswap]
    have hinner : ∀ u ∈ Finset.range (k + 1),
        ∑ v ∈ Finset.range (k + 1), ∑ t ∈ Finset.range N, (ω ^ t) ^ ((u : ℤ) - (v : ℤ)) = (N : ℂ) := by
      intro u hu
      rw [Finset.mem_range] at hu
      have hterm : ∀ v ∈ Finset.range (k + 1),
          ∑ t ∈ Finset.range N, (ω ^ t) ^ ((u : ℤ) - (v : ℤ)) = if v = u then (N : ℂ) else 0 := by
        intro v hv
        rw [Finset.mem_range] at hv
        rw [sum_root_of_unity N hN_pos]
        congr 1
        refine propext ⟨fun hd => ?_, fun hvu => by subst hvu; simp⟩
        obtain ⟨q, hq⟩ := hd
        have hlt : |(u : ℤ) - (v : ℤ)| < (N : ℤ) := by
          rw [abs_lt]; constructor <;> omega
        have hq0 : q = 0 := by
          by_contra hqne
          have h1 : (1 : ℤ) ≤ |q| := Int.one_le_abs hqne
          have h2 : (N : ℤ) ≤ |(u : ℤ) - (v : ℤ)| := by
            rw [hq, abs_mul, abs_of_nonneg (Int.natCast_nonneg N)]
            nlinarith
          linarith
        rw [hq0, mul_zero] at hq
        omega
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range (k + 1)) u]
      simp [Finset.mem_range.mpr hu]
    rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast; ring
  have hSN_le_one : ‖SN‖ ≤ 1 := by
    dsimp [SN]
    rw [norm_mul, norm_div, norm_one, norm_mul, Complex.norm_natCast,
      show ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 by
        rw [show ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
    have htri : ‖∑ t ∈ Finset.range N, B (ω ^ t) ^ m * K t‖ ≤
        ∑ t ∈ Finset.range N, ‖∑ u ∈ Finset.range (k + 1), (ω ^ t) ^ u‖ ^ 2 := by
      calc ‖∑ t ∈ Finset.range N, B (ω ^ t) ^ m * K t‖
          ≤ ∑ t ∈ Finset.range N, ‖B (ω ^ t) ^ m * K t‖ := norm_sum_le _ _
        _ = ∑ t ∈ Finset.range N, ‖∑ u ∈ Finset.range (k + 1), (ω ^ t) ^ u‖ ^ 2 := by
            refine Finset.sum_congr rfl (fun t _ => ?_)
            rw [norm_mul, norm_pow, norm_B_eq_one_of_norm_eq_one (hωt_norm t), one_pow, one_mul,
              hK_real t, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hsum_real : ∑ t ∈ Finset.range N, ‖∑ u ∈ Finset.range (k + 1), (ω ^ t) ^ u‖ ^ 2 =
        (N : ℝ) * ((k : ℝ) + 1) := by
      have h := hK_sum
      simp_rw [hK_real] at h
      rw [← ofReal_sum] at h
      have hR : ((N : ℂ) * ((k : ℂ) + 1)) = (((N : ℝ) * ((k : ℝ) + 1) : ℝ) : ℂ) := by push_cast; rfl
      rw [hR] at h
      exact Complex.ofReal_injective h
    have hden_pos : (0 : ℝ) < (N : ℝ) * ((k : ℝ) + 1) := by positivity
    calc 1 / ((N : ℝ) * ((k : ℝ) + 1)) * ‖∑ t ∈ Finset.range N, B (ω ^ t) ^ m * K t‖
        ≤ 1 / ((N : ℝ) * ((k : ℝ) + 1)) * ((N : ℝ) * ((k : ℝ) + 1)) := by
          rw [← hsum_real]
          exact mul_le_mul_of_nonneg_left htri (by positivity)
      _ = 1 := by field_simp [ne_of_gt hden_pos]
  have hSN_diff : ‖SN - (sigma m k : ℂ)‖ ≤ ε := by
    have hterm_sum : ∀ t : ℕ, B (ω ^ t) ^ m * K t =
        ∑' i : ℕ, (c m i : ℂ) * ((ω ^ t) ^ i * K t) := by
      intro t
      rw [← tsum_c_pow m (z := ω ^ t) (by rw [hωt_norm t]; norm_num), ← tsum_mul_right]
      congr 1; ext i; ring
    have hsumm : ∀ t : ℕ, Summable (fun i : ℕ => (c m i : ℂ) * ((ω ^ t) ^ i * K t)) := by
      intro t
      have h1 := (summable_norm_c_mul_pow m (z := ω ^ t) (by rw [hωt_norm t]; norm_num)).of_norm
      exact (h1.mul_right (K t)).congr (fun i => by ring)
    have hSN_tsum : SN = ∑' i : ℕ, (c m i : ℂ) *
        ((1 / ((N : ℂ) * ((k : ℂ) + 1))) * ∑ t ∈ Finset.range N, (ω ^ t) ^ i * K t) := by
      dsimp [SN]
      rw [Finset.sum_congr rfl (fun t _ => hterm_sum t), ← Summable.tsum_finsetSum (fun t _ => hsumm t),
        ← tsum_mul_left]
      congr 1; ext i
      rw [← Finset.mul_sum]; ring
    let M : ℕ → ℂ := fun i =>
      (1 / ((N : ℂ) * ((k : ℂ) + 1))) * ∑ t ∈ Finset.range N, (ω ^ t) ^ i * K t
    have hM_eval : ∀ i : ℕ, M i = (1 / ((N : ℂ) * ((k : ℂ) + 1))) *
        ∑ u ∈ Finset.range (k + 1), ∑ v ∈ Finset.range (k + 1),
          if (N : ℤ) ∣ ((i : ℤ) + (u : ℤ) - (v : ℤ)) then (N : ℂ) else 0 := by
      intro i
      dsimp [M, K]
      congr 1
      have h1 : ∀ t : ℕ, (ω ^ t) ^ i * ((∑ u ∈ Finset.range (k + 1), (ω ^ t) ^ u) *
          (∑ v ∈ Finset.range (k + 1), (ω ^ t)⁻¹ ^ v)) =
          ∑ u ∈ Finset.range (k + 1), ∑ v ∈ Finset.range (k + 1),
            (ω ^ t) ^ ((i : ℤ) + (u : ℤ) - (v : ℤ)) := by
        intro t
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun u _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun v _ => ?_)
        have hne : ω ^ t ≠ 0 := pow_ne_zero t (Complex.exp_ne_zero _)
        rw [inv_pow, ← zpow_natCast (ω ^ t) i, ← zpow_natCast (ω ^ t) u, ← zpow_natCast (ω ^ t) v,
          ← mul_assoc, ← zpow_add₀ hne, ← div_eq_mul_inv, ← zpow_sub₀ hne]
      rw [Finset.sum_congr rfl (fun t _ => h1 t), Finset.sum_comm]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun v _ => sum_root_of_unity N hN_pos _)
    have hM_small : ∀ i ∈ Finset.range (k + 1), M i = (1 - (i : ℂ) / ((k : ℂ) + 1)) := by
      intro i hi
      rw [Finset.mem_range] at hi
      rw [hM_eval i]
      have hcond : ∀ u ∈ Finset.range (k + 1), ∀ v ∈ Finset.range (k + 1),
          (if (N : ℤ) ∣ ((i : ℤ) + (u : ℤ) - (v : ℤ)) then (N : ℂ) else 0) =
            if v = i + u then (N : ℂ) else 0 := by
        intro u hu v hv
        rw [Finset.mem_range] at hu hv
        congr 1
        refine propext ⟨fun hd => ?_, fun hvu => by subst hvu; simp⟩
        obtain ⟨q, hq⟩ := hd
        have hlt : |(i : ℤ) + (u : ℤ) - (v : ℤ)| < (N : ℤ) := by
          rw [abs_lt]; constructor <;> omega
        have hq0 : q = 0 := by
          by_contra hqne
          have h1 : (1 : ℤ) ≤ |q| := Int.one_le_abs hqne
          have h2 : (N : ℤ) ≤ |(i : ℤ) + (u : ℤ) - (v : ℤ)| := by
            rw [hq, abs_mul, abs_of_nonneg (Int.natCast_nonneg N)]
            nlinarith
          linarith
        rw [hq0, mul_zero] at hq
        omega
      have hsum_uv : ∑ u ∈ Finset.range (k + 1), ∑ v ∈ Finset.range (k + 1),
          (if (N : ℤ) ∣ ((i : ℤ) + (u : ℤ) - (v : ℤ)) then (N : ℂ) else 0) =
          (((k + 1 - i : ℕ) : ℂ)) * (N : ℂ) := by
        have h2 : ∀ u ∈ Finset.range (k + 1),
            ∑ v ∈ Finset.range (k + 1),
              (if (N : ℤ) ∣ ((i : ℤ) + (u : ℤ) - (v : ℤ)) then (N : ℂ) else 0) =
              if u < k + 1 - i then (N : ℂ) else 0 := by
          intro u hu
          rw [Finset.sum_congr rfl (fun v hv => hcond u hu v hv),
            Finset.sum_ite_eq' (Finset.range (k + 1)) (i + u)]
          simp only [Finset.mem_range]
          congr 1; exact propext (by omega)
        rw [Finset.sum_congr rfl h2, Finset.sum_ite, Finset.sum_const_zero, add_zero,
          Finset.sum_const, nsmul_eq_mul]
        congr 1
        have hfilt : (Finset.range (k + 1)).filter (fun u => u < k + 1 - i) =
            Finset.range (k + 1 - i) := by
          ext u; simp only [Finset.mem_filter, Finset.mem_range]; omega
        rw [hfilt, Finset.card_range]
      rw [hsum_uv]
      have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hN_pos)
      have hk0 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
      have hsub : ((k + 1 - i : ℕ) : ℂ) = (k : ℂ) + 1 - (i : ℂ) := by
        rw [Nat.cast_sub (Nat.le_of_lt hi)]
        push_cast; ring
      rw [hsub]
      field_simp [hN0, hk0]
    have hM_mid : ∀ i : ℕ, k + 1 ≤ i → i < N - k → M i = 0 := by
      intro i hi1 hi2
      rw [hM_eval i]
      have hzero : ∀ u ∈ Finset.range (k + 1), ∀ v ∈ Finset.range (k + 1),
          (if (N : ℤ) ∣ ((i : ℤ) + (u : ℤ) - (v : ℤ)) then (N : ℂ) else 0) = 0 := by
        intro u hu v hv
        rw [Finset.mem_range] at hu hv
        rw [if_neg]
        intro hd
        obtain ⟨q, hq⟩ := hd
        have hpos : 0 < (i : ℤ) + (u : ℤ) - (v : ℤ) := by omega
        have hlt : (i : ℤ) + (u : ℤ) - (v : ℤ) < (N : ℤ) := by omega
        have hq1 : 1 ≤ q := by nlinarith
        nlinarith
      simp [Finset.sum_congr rfl (fun u hu => Finset.sum_congr rfl (fun v hv => hzero u hu v hv))]
    have hM_bound : ∀ i : ℕ, ‖M i‖ ≤ (k : ℝ) + 1 := by
      intro i
      dsimp [M]
      rw [norm_mul, norm_div, norm_one, norm_mul, Complex.norm_natCast,
        show ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 by
          rw [show ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
      have hK_le : ∀ t : ℕ, ‖K t‖ ≤ ((k : ℝ) + 1) ^ 2 := by
        intro t
        rw [hK_real t, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        have h1 : ‖∑ u ∈ Finset.range (k + 1), (ω ^ t) ^ u‖ ≤ (k : ℝ) + 1 := by
          calc ‖∑ u ∈ Finset.range (k + 1), (ω ^ t) ^ u‖
              ≤ ∑ u ∈ Finset.range (k + 1), ‖(ω ^ t) ^ u‖ := norm_sum_le _ _
            _ = ∑ _u ∈ Finset.range (k + 1), (1 : ℝ) :=
                Finset.sum_congr rfl (fun u _ => by rw [norm_pow, hωt_norm t, one_pow])
            _ = (k : ℝ) + 1 := by simp
        nlinarith [norm_nonneg (∑ u ∈ Finset.range (k + 1), (ω ^ t) ^ u)]
      have hsum_le : ‖∑ t ∈ Finset.range N, (ω ^ t) ^ i * K t‖ ≤ (N : ℝ) * ((k : ℝ) + 1) ^ 2 := by
        calc ‖∑ t ∈ Finset.range N, (ω ^ t) ^ i * K t‖
            ≤ ∑ t ∈ Finset.range N, ‖(ω ^ t) ^ i * K t‖ := norm_sum_le _ _
          _ ≤ ∑ _t ∈ Finset.range N, ((k : ℝ) + 1) ^ 2 := by
              refine Finset.sum_le_sum (fun t _ => ?_)
              rw [norm_mul, norm_pow, hωt_norm t, one_pow, one_mul]
              exact hK_le t
          _ = (N : ℝ) * ((k : ℝ) + 1) ^ 2 := by simp
      have hden : (0 : ℝ) < (N : ℝ) * ((k : ℝ) + 1) := by positivity
      calc 1 / ((N : ℝ) * ((k : ℝ) + 1)) * ‖∑ t ∈ Finset.range N, (ω ^ t) ^ i * K t‖
          ≤ 1 / ((N : ℝ) * ((k : ℝ) + 1)) * ((N : ℝ) * ((k : ℝ) + 1) ^ 2) :=
            mul_le_mul_of_nonneg_left hsum_le (by positivity)
        _ = (k : ℝ) + 1 := by field_simp [ne_of_gt hden]
    have hsumm_cM : Summable (fun i : ℕ => (c m i : ℂ) * M i) := by
      have h1 : Summable (fun i : ℕ => ‖(c m i : ℂ) * M i‖) := by
        refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => ?_)
          ((c_weighted_l1 m).1.mul_right ((k : ℝ) + 1))
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ i := one_le_pow₀ (by norm_num)
        exact mul_le_mul (le_mul_of_one_le_right (abs_nonneg _) hpow) (hM_bound i)
          (norm_nonneg _) (mul_nonneg (abs_nonneg _) (by positivity))
      exact h1.of_norm
    have hsplit := hsumm_cM.sum_add_tsum_nat_add (N - k)
    have hhead : ∑ i ∈ Finset.range (N - k), (c m i : ℂ) * M i = (sigma m k : ℂ) := by
      have hsub : Finset.range (k + 1) ⊆ Finset.range (N - k) :=
        Finset.range_mono (by omega)
      rw [← Finset.sum_subset hsub]
      · simp only [sigma, ofReal_sum, ofReal_mul, ofReal_sub, ofReal_one, ofReal_div,
          ofReal_add, ofReal_natCast]
        refine Finset.sum_congr rfl (fun i hi => ?_)
        rw [hM_small i hi, mul_comm]
      · intro i hi1 hi2
        rw [Finset.mem_range] at hi1 hi2
        rw [hM_mid i (by omega) hi1, mul_zero]
    rw [hSN_tsum, ← hsplit, hhead, add_sub_cancel_left]
    have htail_dom : ∀ j : ℕ, ‖(c m (j + (N - k)) : ℂ) * M (j + (N - k))‖ ≤
        ((k : ℝ) + 1) * (4 : ℝ) ^ m * (1 / 2 : ℝ) ^ (N - k) * (1 / 2 : ℝ) ^ j := by
      intro j
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hc := abs_c_le m (j + (N - k))
      have hM := hM_bound (j + (N - k))
      have h1 : |c m (j + (N - k))| * ‖M (j + (N - k))‖ ≤
          ((4 : ℝ) ^ m / (2 : ℝ) ^ (j + (N - k))) * ((k : ℝ) + 1) :=
        mul_le_mul hc hM (norm_nonneg _) (by positivity)
      have hpow : (1 : ℝ) / (2 : ℝ) ^ (j + (N - k)) = (1 / 2 : ℝ) ^ (N - k) * (1 / 2 : ℝ) ^ j := by
        rw [one_div_pow, one_div_pow, pow_add]; ring
      calc |c m (j + (N - k))| * ‖M (j + (N - k))‖
          ≤ ((4 : ℝ) ^ m / (2 : ℝ) ^ (j + (N - k))) * ((k : ℝ) + 1) := h1
        _ = ((k : ℝ) + 1) * (4 : ℝ) ^ m * ((1 : ℝ) / (2 : ℝ) ^ (j + (N - k))) := by ring
        _ = ((k : ℝ) + 1) * (4 : ℝ) ^ m * (1 / 2 : ℝ) ^ (N - k) * (1 / 2 : ℝ) ^ j := by
            rw [hpow]; ring
    have hgeom0 := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)).mul_left
      (((k : ℝ) + 1) * (4 : ℝ) ^ m * (1 / 2 : ℝ) ^ (N - k))
    have hval0 : ((k : ℝ) + 1) * (4 : ℝ) ^ m * (1 / 2 : ℝ) ^ (N - k) * (1 - (1 / 2 : ℝ))⁻¹ =
        ((k : ℝ) + 1) * (4 : ℝ) ^ m * 2 * (1 / 2 : ℝ) ^ (N - k) := by ring
    rw [hval0] at hgeom0
    have hnorm_sum : Summable (fun j : ℕ => ‖(c m (j + (N - k)) : ℂ) * M (j + (N - k))‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) htail_dom hgeom0.summable
    calc ‖∑' j : ℕ, (c m (j + (N - k)) : ℂ) * M (j + (N - k))‖
        ≤ ∑' j : ℕ, ‖(c m (j + (N - k)) : ℂ) * M (j + (N - k))‖ := norm_tsum_le_tsum_norm hnorm_sum
      _ ≤ ∑' j : ℕ, ((k : ℝ) + 1) * (4 : ℝ) ^ m * (1 / 2 : ℝ) ^ (N - k) * (1 / 2 : ℝ) ^ j :=
          hnorm_sum.tsum_le_tsum htail_dom hgeom0.summable
      _ = ((k : ℝ) + 1) * (4 : ℝ) ^ m * 2 * (1 / 2 : ℝ) ^ (N - k) := hgeom0.tsum_eq
      _ ≤ ε := le_of_lt hN_tail
  have htri : ‖(sigma m k : ℂ)‖ ≤ ‖SN‖ + ‖SN - (sigma m k : ℂ)‖ := by
    have := norm_sub_le SN (SN - (sigma m k : ℂ))
    simpa [sub_sub_cancel] using this
  rw [Complex.norm_real, Real.norm_eq_abs] at htri
  linarith

lemma hasSum_quarter_succ : HasSum (fun k : ℕ => (1 / 4 : ℝ) ^ (k + 1)) (1 / 3 : ℝ) := by
  have h := (hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 4) (by norm_num)).mul_left (1 / 4 : ℝ)
  have hv : (1 / 4 : ℝ) * (1 - (1 / 4 : ℝ))⁻¹ = 1 / 3 := by norm_num
  rw [hv] at h
  exact h.congr_fun (fun k => pow_succ' (1 / 4 : ℝ) k)

lemma abs_Cm_le (m : ℕ) : |Cm m| ≤ 1 / 3 := by
  have hgeom := hasSum_quarter_succ
  have hdom : ∀ k : ℕ, ‖sigma m k * (1 / 4 : ℝ) ^ (k + 1)‖ ≤ (1 / 4 : ℝ) ^ (k + 1) := by
    intro k
    have hq0 : (0 : ℝ) ≤ (1 / 4 : ℝ) ^ (k + 1) := pow_nonneg (by norm_num) (k + 1)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hq0]
    exact mul_le_of_le_one_left hq0 (abs_sigma_le_one m k)
  have hsumm : Summable (fun k : ℕ => ‖sigma m k * (1 / 4 : ℝ) ^ (k + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom hgeom.summable
  calc |Cm m| = ‖∑' k : ℕ, sigma m k * (1 / 4 : ℝ) ^ (k + 1)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' k : ℕ, ‖sigma m k * (1 / 4 : ℝ) ^ (k + 1)‖ := norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' k : ℕ, (1 / 4 : ℝ) ^ (k + 1) := hsumm.tsum_le_tsum hdom hgeom.summable
    _ = 1 / 3 := hgeom.tsum_eq

lemma abs_aCoeff_le_one (m j : ℕ) : |aCoeff m j| ≤ 1 := by
  cases j with
  | zero =>
    simp only [aCoeff, abs_neg]
    linarith [abs_Cm_le m]
  | succ k =>
    exact abs_sigma_le_one m k

lemma sigma_eq_main_add_tail (m k : ℕ) :
    sigma m k = 1 - (1 / ((k : ℝ) + 1)) * ((5 / 3 : ℝ) * m) +
      ∑' j : ℕ, ((j : ℝ) / ((k : ℝ) + 1)) * c m (j + (k + 1)) := by
  have hk0 : ((k : ℝ) + 1) ≠ 0 := by positivity
  let g : ℕ → ℝ := fun i => (1 - (i : ℝ) / ((k : ℝ) + 1)) * c m i
  have hg_hasSum : HasSum g (1 - (1 / ((k : ℝ) + 1)) * ((5 / 3 : ℝ) * m)) := by
    have h1 : HasSum (fun i : ℕ => c m i) 1 := by
      simpa [tsum_c_eq_one m] using (summable_c m).hasSum
    have h2 : HasSum (fun i : ℕ => (1 / ((k : ℝ) + 1)) * ((i : ℝ) * c m i))
        ((1 / ((k : ℝ) + 1)) * ((5 / 3 : ℝ) * m)) := by
      have h := (summable_nat_mul_c m).hasSum.mul_left (1 / ((k : ℝ) + 1))
      rwa [tsum_nat_mul_c m] at h
    exact (h1.sub h2).congr_fun (fun i => by dsimp [g]; ring)
  have hsplit := hg_hasSum.summable.sum_add_tsum_nat_add (k + 1)
  rw [hg_hasSum.tsum_eq] at hsplit
  have htail : ∑' j : ℕ, g (j + (k + 1)) =
      -(∑' j : ℕ, ((j : ℝ) / ((k : ℝ) + 1)) * c m (j + (k + 1))) := by
    rw [← tsum_neg]
    congr 1; ext j
    dsimp [g]
    have hcast : ((j + (k + 1) : ℕ) : ℝ) = (j : ℝ) + ((k : ℝ) + 1) := by push_cast; ring
    rw [hcast, add_div, div_self hk0]
    ring
  rw [htail] at hsplit
  exact eq_add_of_sub_eq (by simpa [sigma, g, sub_eq_add_neg] using hsplit)

lemma sigma_ge_half (m k : ℕ) (hm : 4 ≤ m) (hk : 4 * m ≤ k + 1) :
    (1 / 2 : ℝ) ≤ sigma m k := by
  rw [sigma_eq_main_add_tail m k]
  have hkpos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hmain : (7 / 12 : ℝ) ≤ 1 - 1 / ((k : ℝ) + 1) * ((5 / 3 : ℝ) * m) := by
    have hk' : (4 * m : ℝ) ≤ (k : ℝ) + 1 := by exact_mod_cast hk
    have hdiv : (5 / 3 : ℝ) * m / ((k : ℝ) + 1) ≤ 5 / 12 := by
      rw [div_le_iff₀ hkpos]; linarith
    have heq : 1 / ((k : ℝ) + 1) * ((5 / 3 : ℝ) * m) = (5 / 3 : ℝ) * m / ((k : ℝ) + 1) := by ring
    linarith
  have htail_dom : ∀ j : ℕ, ‖((j : ℝ) / ((k : ℝ) + 1)) * c m (j + (k + 1))‖ ≤
      (1 / 4 : ℝ) ^ m * ((j : ℝ) * (1 / 2 : ℝ) ^ j) := by
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_nonneg (Nat.cast_nonneg j) (le_of_lt hkpos))]
    have hjk : (j : ℝ) / ((k : ℝ) + 1) ≤ (j : ℝ) := div_le_self (Nat.cast_nonneg j) (by linarith)
    have hc : |c m (j + (k + 1))| ≤ (4 : ℝ) ^ m / (2 : ℝ) ^ (j + (k + 1)) := abs_c_le m _
    have hpow : (2 : ℝ) ^ (j + 4 * m) ≤ (2 : ℝ) ^ (j + (k + 1)) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    have hdiv : (4 : ℝ) ^ m / (2 : ℝ) ^ (j + (k + 1)) ≤ (1 / 4 : ℝ) ^ m * (1 / 2 : ℝ) ^ j := by
      have hstep1 : (4 : ℝ) ^ m / (2 : ℝ) ^ (j + (k + 1)) ≤ (4 : ℝ) ^ m / (2 : ℝ) ^ (j + 4 * m) :=
        div_le_div_of_nonneg_left (pow_nonneg (by norm_num) m) (pow_pos (by norm_num) _) hpow
      have hstep2 : (4 : ℝ) ^ m / (2 : ℝ) ^ (j + 4 * m) = (1 / 4 : ℝ) ^ m * (1 / 2 : ℝ) ^ j := by
        rw [pow_add, pow_mul, show (2 : ℝ) ^ 4 = 16 by norm_num,
          show (16 : ℝ) ^ m = (4 : ℝ) ^ m * (4 : ℝ) ^ m by rw [← mul_pow]; norm_num,
          one_div_pow, one_div_pow]
        have h4ne : (4 : ℝ) ^ m ≠ 0 := pow_ne_zero m (by norm_num)
        have h2ne : (2 : ℝ) ^ j ≠ 0 := pow_ne_zero j (by norm_num)
        field_simp [h4ne, h2ne]
      linarith
    have hmul := mul_le_mul hjk (le_trans hc hdiv) (abs_nonneg _) (Nat.cast_nonneg j)
    linarith
  have hgeom0 := (hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num)).mul_left
    ((1 / 4 : ℝ) ^ m)
  have hval0 : (1 / 4 : ℝ) ^ m * ((1 / 2 : ℝ) / (1 - (1 / 2 : ℝ)) ^ 2) = (1 / 4 : ℝ) ^ m * 2 := by ring
  rw [hval0] at hgeom0
  have hsumm_norm : Summable (fun j : ℕ => ‖((j : ℝ) / ((k : ℝ) + 1)) * c m (j + (k + 1))‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) htail_dom hgeom0.summable
  have hT_le : |∑' j : ℕ, ((j : ℝ) / ((k : ℝ) + 1)) * c m (j + (k + 1))| ≤ 1 / 12 := by
    have hT1 : |∑' j : ℕ, ((j : ℝ) / ((k : ℝ) + 1)) * c m (j + (k + 1))| ≤ (1 / 4 : ℝ) ^ m * 2 := by
      calc |∑' j : ℕ, ((j : ℝ) / ((k : ℝ) + 1)) * c m (j + (k + 1))|
          = ‖∑' j : ℕ, ((j : ℝ) / ((k : ℝ) + 1)) * c m (j + (k + 1))‖ := (Real.norm_eq_abs _).symm
        _ ≤ ∑' j : ℕ, ‖((j : ℝ) / ((k : ℝ) + 1)) * c m (j + (k + 1))‖ := norm_tsum_le_tsum_norm hsumm_norm
        _ ≤ ∑' j : ℕ, (1 / 4 : ℝ) ^ m * ((j : ℝ) * (1 / 2 : ℝ) ^ j) :=
            hsumm_norm.tsum_le_tsum htail_dom hgeom0.summable
        _ = (1 / 4 : ℝ) ^ m * 2 := hgeom0.tsum_eq
    have h2 : (1 / 4 : ℝ) ^ m ≤ (1 / 4 : ℝ) ^ 4 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
    linarith [show (1 / 4 : ℝ) ^ 4 * 2 ≤ 1 / 12 by norm_num]
  linarith [neg_abs_le (∑' j : ℕ, ((j : ℝ) / ((k : ℝ) + 1)) * c m (j + (k + 1)))]

-- ============================================================================
-- Section 3: Exact identity H m z = (5/3) * J m (B z) and upper/lower bounds
-- ============================================================================

def H (m : ℕ) (z : ℂ) : ℂ :=
  -(Cm m : ℂ) + ∑' k : ℕ, (sigma m k : ℂ) * z ^ (k + 1)

def J (m : ℕ) (v : ℂ) : ℂ :=
  ∑' j : ℕ, (((j : ℂ) + 1) / ((m : ℂ) + (j : ℂ) + 1)) * v ^ (m + j + 1)

lemma tsum_succ_mul_pow {z : ℂ} (hz : ‖z‖ < 1) :
    ∑' j : ℕ, (((j : ℂ) + 1) * z ^ j) = 1 / (1 - z) ^ 2 := by
  have h1 := hasSum_coe_mul_geometric_of_norm_lt_one hz
  have h2 := hasSum_geometric_of_norm_lt_one hz
  have h3 := h1.add h2
  have hne : (1 : ℂ) - z ≠ 0 := by
    intro h
    have hz1 : z = 1 := (sub_eq_zero.mp h).symm
    rw [hz1, norm_one] at hz
    exact lt_irrefl 1 hz
  have heq : z / (1 - z) ^ 2 + (1 - z)⁻¹ = 1 / (1 - z) ^ 2 := by
    field_simp [hne]; ring
  rw [heq] at h3
  exact (h3.congr_fun (fun j => by ring)).tsum_eq

lemma hasDerivAt_H (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (H m) (B z ^ m / (1 - z) ^ 2) z := by
  let ρ : ℝ := (‖z‖ + 1) / 2
  have hρ_lt : ρ < 1 := by dsimp [ρ]; linarith
  have hz_lt : ‖z‖ < ρ := by dsimp [ρ]; linarith
  have hρ_pos : 0 < ρ := by dsimp [ρ]; linarith [norm_nonneg z]
  have hu : Summable (fun k : ℕ => ((k : ℝ) + 1) * ρ ^ k) := by
    have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one (r := ρ) (by
      rw [Real.norm_eq_abs, abs_of_pos hρ_pos]; exact hρ_lt)).summable
    have h2 := (hasSum_geometric_of_lt_one (le_of_lt hρ_pos) hρ_lt).summable
    exact (h1.add h2).congr (fun k => by ring)
  have hderiv_tsum : HasDerivAt (fun w : ℂ => ∑' k : ℕ, (sigma m k : ℂ) * w ^ (k + 1))
      (∑' k : ℕ, (sigma m k : ℂ) * (((k : ℂ) + 1) * z ^ k)) z := by
    refine hasDerivAt_tsum_of_isPreconnected
      (g := fun (k : ℕ) (w : ℂ) => (sigma m k : ℂ) * w ^ (k + 1))
      (g' := fun (k : ℕ) (w : ℂ) => (sigma m k : ℂ) * (((k : ℂ) + 1) * w ^ k))
      (t := Metric.ball (0 : ℂ) ρ) (y₀ := 0) hu
      Metric.isOpen_ball (convex_ball 0 ρ).isPreconnected ?_ ?_
      (Metric.mem_ball_self hρ_pos) ?_ (by simpa [Metric.mem_ball, dist_zero_right] using hz_lt)
    · intro k y _
      have hd := (hasDerivAt_pow (k + 1) y).const_mul (sigma m k : ℂ)
      simpa [Nat.cast_add, Nat.cast_one] using hd
    · intro k y hy
      rw [Metric.mem_ball, dist_zero_right] at hy
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow,
        show ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 by
          rw [show ((k : ℂ) + 1) = (((k : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
      calc |sigma m k| * (((k : ℝ) + 1) * ‖y‖ ^ k)
          ≤ 1 * (((k : ℝ) + 1) * ρ ^ k) :=
            mul_le_mul (abs_sigma_le_one m k)
              (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y) (le_of_lt hy) k) (by positivity))
              (by positivity) (by norm_num)
        _ = ((k : ℝ) + 1) * ρ ^ k := one_mul _
    · simp [zero_pow (Nat.succ_ne_zero _)]
  have hsum_eq : ∑' k : ℕ, (sigma m k : ℂ) * (((k : ℂ) + 1) * z ^ k) = B z ^ m / (1 - z) ^ 2 := by
    have h1 : Summable (fun i : ℕ => ‖(c m i : ℂ) * z ^ i‖) :=
      summable_norm_c_mul_pow m (by linarith)
    have h2 : Summable (fun j : ℕ => ‖(((j : ℂ) + 1) * z ^ j)‖) := by
      have ha := (hasSum_coe_mul_geometric_of_norm_lt_one (r := ‖z‖) (by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z)]; exact hz)).summable
      have hb := (hasSum_geometric_of_lt_one (norm_nonneg z) hz).summable
      refine (ha.add hb).congr (fun j => ?_)
      rw [norm_mul, norm_pow,
        show ‖((j : ℂ) + 1)‖ = (j : ℝ) + 1 by
          rw [show ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
      ring
    have hmul := tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm h1 h2
    rw [tsum_c_pow m (by linarith), tsum_succ_mul_pow hz] at hmul
    rw [show B z ^ m / (1 - z) ^ 2 = B z ^ m * (1 / (1 - z) ^ 2) by ring, hmul]
    congr 1; ext k
    simp only [sigma, ofReal_sum, ofReal_mul, ofReal_sub, ofReal_one, ofReal_div,
      ofReal_add, ofReal_natCast, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    have hk0 : ((k : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
    have hpow : z ^ i * z ^ (k - i) = z ^ k := by
      rw [← pow_add, Nat.add_sub_of_le (Nat.lt_succ_iff.mp hi)]
    have hsub : ((k - i : ℕ) : ℂ) + 1 = (k : ℂ) + 1 - (i : ℂ) := by
      rw [Nat.cast_sub (Nat.lt_succ_iff.mp hi)]; ring
    rw [hsub]
    calc (1 - (i : ℂ) / ((k : ℂ) + 1)) * (c m i : ℂ) * (((k : ℂ) + 1) * z ^ k)
        = (c m i : ℂ) * (((k : ℂ) + 1 - (i : ℂ)) * (z ^ i * z ^ (k - i))) := by
          rw [hpow]; field_simp [hk0]
      _ = (c m i : ℂ) * z ^ i * (((k : ℂ) + 1 - (i : ℂ)) * z ^ (k - i)) := by ring
  rw [hsum_eq] at hderiv_tsum
  change HasDerivAt (fun w : ℂ => -(Cm m : ℂ) + ∑' k : ℕ, (sigma m k : ℂ) * w ^ (k + 1)) _ z
  exact hderiv_tsum.const_add (-(Cm m : ℂ))

lemma hasDerivAt_J (m : ℕ) {v : ℂ} (hv : ‖v‖ < 1) :
    HasDerivAt (J m) (v ^ m / (1 - v) ^ 2) v := by
  let ρ : ℝ := (‖v‖ + 1) / 2
  have hρ_lt : ρ < 1 := by dsimp [ρ]; linarith
  have hv_lt : ‖v‖ < ρ := by dsimp [ρ]; linarith
  have hρ_pos : 0 < ρ := by dsimp [ρ]; linarith [norm_nonneg v]
  have hu : Summable (fun j : ℕ => ((j : ℝ) + 1) * ρ ^ (m + j)) := by
    have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one (r := ρ) (by
      rw [Real.norm_eq_abs, abs_of_pos hρ_pos]; exact hρ_lt)).summable
    have h2 := (hasSum_geometric_of_lt_one (le_of_lt hρ_pos) hρ_lt).summable
    exact ((h1.add h2).mul_left (ρ ^ m)).congr (fun j => by rw [pow_add]; ring)
  have hderiv_tsum : HasDerivAt (J m)
      (∑' j : ℕ, (((j : ℂ) + 1) / ((m : ℂ) + (j : ℂ) + 1)) *
        ((((m + j + 1 : ℕ) : ℂ)) * v ^ (m + j))) v := by
    change HasDerivAt (fun w : ℂ => ∑' j : ℕ, (((j : ℂ) + 1) / ((m : ℂ) + (j : ℂ) + 1)) * w ^ (m + j + 1)) _ v
    refine hasDerivAt_tsum_of_isPreconnected
      (g := fun (j : ℕ) (w : ℂ) => (((j : ℂ) + 1) / ((m : ℂ) + (j : ℂ) + 1)) * w ^ (m + j + 1))
      (g' := fun (j : ℕ) (w : ℂ) => (((j : ℂ) + 1) / ((m : ℂ) + (j : ℂ) + 1)) * ((((m + j + 1 : ℕ) : ℂ)) * w ^ (m + j)))
      (t := Metric.ball (0 : ℂ) ρ) (y₀ := 0) hu
      Metric.isOpen_ball (convex_ball 0 ρ).isPreconnected ?_ ?_
      (Metric.mem_ball_self hρ_pos) ?_ (by simpa [Metric.mem_ball, dist_zero_right] using hv_lt)
    · intro j y _
      exact (hasDerivAt_pow (m + j + 1) y).const_mul _
    · intro j y hy
      rw [Metric.mem_ball, dist_zero_right] at hy
      have hne : ((m : ℂ) + (j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + j)
      have hsimp : (((j : ℂ) + 1) / ((m : ℂ) + (j : ℂ) + 1)) *
          ((((m + j + 1 : ℕ) : ℂ)) * y ^ (m + j)) = ((j : ℂ) + 1) * y ^ (m + j) := by
        push_cast; field_simp [hne]
      rw [hsimp, norm_mul, norm_pow,
        show ‖((j : ℂ) + 1)‖ = (j : ℝ) + 1 by
          rw [show ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg y) (le_of_lt hy) _) (by positivity)
    · simp [zero_pow (Nat.succ_ne_zero _)]
  have hsum_eq : (∑' j : ℕ, (((j : ℂ) + 1) / ((m : ℂ) + (j : ℂ) + 1)) *
      ((((m + j + 1 : ℕ) : ℂ)) * v ^ (m + j))) = v ^ m / (1 - v) ^ 2 := by
    have hsimp : ∀ j : ℕ, (((j : ℂ) + 1) / ((m : ℂ) + (j : ℂ) + 1)) *
        ((((m + j + 1 : ℕ) : ℂ)) * v ^ (m + j)) = v ^ m * (((j : ℂ) + 1) * v ^ j) := by
      intro j
      have hne : ((m : ℂ) + (j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + j)
      rw [pow_add]
      push_cast; field_simp [hne]
    simp_rw [hsimp]
    rw [tsum_mul_left, tsum_succ_mul_pow hv]
    ring
  rw [hsum_eq] at hderiv_tsum
  exact hderiv_tsum

lemma hasDerivAt_B {z : ℂ} (hz : ‖z‖ < 4) :
    HasDerivAt B ((15 / 16 : ℂ) / (1 - (1 / 4 : ℂ) * z) ^ 2) z := by
  have hd : (1 : ℂ) - (1 / 4 : ℂ) * z ≠ 0 := denom_ne_zero_of_norm_lt_four hz
  have hnum : HasDerivAt (fun w : ℂ => w - (1 / 4 : ℂ)) 1 z :=
    (hasDerivAt_id z).sub_const _
  have hden : HasDerivAt (fun w : ℂ => (1 : ℂ) - (1 / 4 : ℂ) * w) (-(1 / 4 : ℂ)) z := by
    simpa using (hasDerivAt_id z).const_mul (1 / 4 : ℂ) |>.const_sub (1 : ℂ)
  have hdiv := hnum.div hden hd
  have hval : (1 * ((1 : ℂ) - (1 / 4 : ℂ) * z) - (z - (1 / 4 : ℂ)) * -(1 / 4 : ℂ)) /
      ((1 : ℂ) - (1 / 4 : ℂ) * z) ^ 2 = (15 / 16 : ℂ) / (1 - (1 / 4 : ℂ) * z) ^ 2 := by
    ring
  rw [hval] at hdiv
  exact hdiv

lemma H_eq_J_B (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    H m z = (5 / 3 : ℂ) * J m (B z) := by
  let f : ℂ → ℂ := fun w => H m w - (5 / 3 : ℂ) * J m (B w)
  have hderiv : ∀ w ∈ Metric.ball (0 : ℂ) 1, HasDerivAt f 0 w := by
    intro w hw
    rw [Metric.mem_ball, dist_zero_right] at hw
    have hH := hasDerivAt_H m hw
    have hBw : ‖B w‖ < 1 := norm_B_lt_one_of_norm_lt_one hw
    have hJ := (hasDerivAt_J m hBw).comp w (hasDerivAt_B (by linarith))
    have hmul := hJ.const_mul (5 / 3 : ℂ)
    have hsub := hH.sub hmul
    have hzero : B w ^ m / (1 - w) ^ 2 -
        5 / 3 * (B w ^ m / (1 - B w) ^ 2 * (15 / 16 / (1 - 1 / 4 * w) ^ 2)) = 0 := by
      have hd : (1 : ℂ) - (1 / 4 : ℂ) * w ≠ 0 := denom_ne_zero_of_norm_lt_four (by linarith)
      have h4w : (4 : ℂ) - w ≠ 0 := by intro h; apply hd; linear_combination h / 4
      have h1w : (1 : ℂ) - w ≠ 0 := by
        intro h; have : w = 1 := (sub_eq_zero.mp h).symm; rw [this, norm_one] at hw; exact lt_irrefl 1 hw
      have h1B : (1 : ℂ) - B w = (5 / 4 : ℂ) * (1 - w) / (1 - (1 / 4 : ℂ) * w) := by
        simp only [B]; field_simp [hd, h4w]; ring
      rw [h1B]
      field_simp [hd, h1w]
      ring
    rw [hzero] at hsub
    exact hsub
  have hdiffOn : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) 1) :=
    fun w hw => (hderiv w hw).differentiableAt.differentiableWithinAt
  have hfderiv : ∀ w ∈ Metric.ball (0 : ℂ) 1, fderivWithin ℂ f (Metric.ball (0 : ℂ) 1) w = 0 := by
    intro w hw
    rw [fderivWithin_of_isOpen Metric.isOpen_ball hw, (hderiv w hw).hasFDerivAt.fderiv]
    simp
  have hconst := Convex.is_const_of_fderivWithin_eq_zero (convex_ball (0 : ℂ) 1) hdiffOn hfderiv
    (by simpa [Metric.mem_ball, dist_zero_right] using hz)
    (by simp [Metric.mem_ball, dist_zero_right]; norm_num : (1 / 4 : ℂ) ∈ Metric.ball (0 : ℂ) 1)
  have hf_r : f (1 / 4 : ℂ) = 0 := by
    dsimp [f]
    have hBr : B (1 / 4 : ℂ) = 0 := by simp [B]
    have hJ0 : J m 0 = 0 := by simp [J, zero_pow (Nat.succ_ne_zero _)]
    have hHr : H m (1 / 4 : ℂ) = 0 := by
      dsimp [H, Cm]
      rw [Complex.ofReal_tsum]
      have hterm : ∀ k : ℕ, ((sigma m k * (1 / 4 : ℝ) ^ (k + 1) : ℝ) : ℂ) =
          (sigma m k : ℂ) * (1 / 4 : ℂ) ^ (k + 1) := by
        intro k; push_cast; rfl
      simp_rw [hterm]
      ring
    rw [hBr, hJ0, hHr]; ring
  rw [hf_r] at hconst
  exact sub_eq_zero.mp hconst

lemma norm_J_le (m : ℕ) {v : ℂ} (hv : ‖v‖ < 1) :
    ‖J m v‖ ≤ ‖v‖ ^ (m + 1) / (1 - ‖v‖) := by
  have hgeom0 := (hasSum_geometric_of_lt_one (norm_nonneg v) hv).mul_left (‖v‖ ^ (m + 1))
  have hv0 : ‖v‖ ^ (m + 1) * (1 - ‖v‖)⁻¹ = ‖v‖ ^ (m + 1) / (1 - ‖v‖) := by rw [div_eq_mul_inv]
  rw [hv0] at hgeom0
  have hdom : ∀ j : ℕ, ‖(((j : ℂ) + 1) / ((m : ℂ) + (j : ℂ) + 1)) * v ^ (m + j + 1)‖ ≤
      ‖v‖ ^ (m + 1) * ‖v‖ ^ j := by
    intro j
    rw [norm_mul, norm_div, norm_pow,
      show ‖((j : ℂ) + 1)‖ = (j : ℝ) + 1 by
        rw [show ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)],
      show ‖((m : ℂ) + (j : ℂ) + 1)‖ = (m : ℝ) + (j : ℝ) + 1 by
        rw [show ((m : ℂ) + (j : ℂ) + 1) = (((m : ℝ) + (j : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
    have hfrac : ((j : ℝ) + 1) / ((m : ℝ) + (j : ℝ) + 1) ≤ 1 :=
      (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
    have hpow : ‖v‖ ^ (m + j + 1) = ‖v‖ ^ (m + 1) * ‖v‖ ^ j := by
      rw [← pow_add]; congr 1; omega
    rw [hpow]
    exact mul_le_of_le_one_left (by positivity) hfrac
  have hsumm : Summable (fun j : ℕ => ‖(((j : ℂ) + 1) / ((m : ℂ) + (j : ℂ) + 1)) * v ^ (m + j + 1)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom hgeom0.summable
  calc ‖J m v‖ ≤ ∑' j : ℕ, ‖(((j : ℂ) + 1) / ((m : ℂ) + (j : ℂ) + 1)) * v ^ (m + j + 1)‖ :=
        norm_tsum_le_tsum_norm hsumm
    _ ≤ ∑' j : ℕ, ‖v‖ ^ (m + 1) * ‖v‖ ^ j := hsumm.tsum_le_tsum hdom hgeom0.summable
    _ = ‖v‖ ^ (m + 1) / (1 - ‖v‖) := hgeom0.tsum_eq

lemma norm_H_le (m : ℕ) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖H m z‖ ≤ (5 / 3 : ℝ) * (‖B z‖ ^ (m + 1) / (1 - ‖B z‖)) := by
  rw [H_eq_J_B m hz, norm_mul, show ‖(5 / 3 : ℂ)‖ = (5 / 3 : ℝ) by norm_num]
  exact mul_le_mul_of_nonneg_left (norm_J_le m (norm_B_lt_one_of_norm_lt_one hz)) (by norm_num)

lemma norm_J_ge (m : ℕ) (hm : 1 ≤ m) {v : ℂ} (hv1 : ‖v‖ < 1)
    (hv2 : ‖v‖ ≤ 1 - 4 / ((m : ℝ) + 2)) :
    ‖v‖ ^ (m + 1) / (8 * ((m : ℝ) + 1)) ≤ ‖J m v‖ := by
  let a : ℕ → ℂ := fun j => (((j : ℂ) + 1) / ((m : ℂ) + (j : ℂ) + 1)) * v ^ (m + j + 1)
  have hsumm_a : Summable a := by
    have hgeom : Summable (fun j : ℕ => ‖v‖ ^ (m + 1) * ‖v‖ ^ j) :=
      (hasSum_geometric_of_lt_one (norm_nonneg v) hv1).summable.mul_left _
    have hnorm_a : Summable (fun j : ℕ => ‖a j‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_) hgeom
      dsimp [a]
      rw [norm_mul, norm_div, norm_pow,
        show ‖((j : ℂ) + 1)‖ = (j : ℝ) + 1 by
          rw [show ((j : ℂ) + 1) = (((j : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)],
        show ‖((m : ℂ) + (j : ℂ) + 1)‖ = (m : ℝ) + (j : ℝ) + 1 by
          rw [show ((m : ℂ) + (j : ℂ) + 1) = (((m : ℝ) + (j : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
      have hfrac : ((j : ℝ) + 1) / ((m : ℝ) + (j : ℝ) + 1) ≤ 1 :=
        (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α := ℝ) m])
      have hpow : ‖v‖ ^ (m + j + 1) = ‖v‖ ^ (m + 1) * ‖v‖ ^ j := by rw [← pow_add]; congr 1; omega
      rw [hpow]
      exact mul_le_of_le_one_left (by positivity) hfrac
    exact hnorm_a.of_norm
  let b : ℕ → ℂ := fun j =>
    ((m : ℂ) / (((m : ℂ) + (j : ℂ) + 1) * ((m : ℂ) + (j : ℂ) + 2))) * v ^ (m + j + 2)
  have hshift1 : (1 - v) * J m v = (1 / ((m : ℂ) + 1)) * v ^ (m + 1) + ∑' j : ℕ, b j := by
    have hsplit := hsumm_a.tsum_eq_zero_add
    have h1 : (1 - v) * J m v = J m v - v * J m v := by ring
    have hJeq : J m v = ∑' j : ℕ, a j := rfl
    rw [h1, hJeq]
    conv_lhs => arg 1; rw [hsplit]
    rw [← tsum_mul_left]
    have hsumm_s1 : Summable (fun j => a (j + 1)) := (summable_nat_add_iff 1).mpr hsumm_a
    have hsumm_va : Summable (fun j => v * a j) := hsumm_a.mul_left v
    rw [add_sub_assoc, ← hsumm_s1.tsum_sub hsumm_va]
    congr 1
    · dsimp [a]; simp
    · congr 1; ext j
      dsimp [a, b]
      have hne1 : ((m : ℂ) + (j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + j)
      have hne2 : ((m : ℂ) + (j : ℂ) + 2) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + j + 1)
      have hpow1 : v ^ (m + (j + 1) + 1) = v ^ (m + j + 2) := by ring
      have hpow2 : v * v ^ (m + j + 1) = v ^ (m + j + 2) := (pow_succ' v (m + j + 1)).symm
      have hcast1 : ((j + 1 : ℕ) : ℂ) + 1 = (j : ℂ) + 2 := by push_cast; ring
      have hcast2 : (m : ℂ) + ((j + 1 : ℕ) : ℂ) + 1 = (m : ℂ) + (j : ℂ) + 2 := by push_cast; ring
      rw [hcast1, hcast2, hpow1,
        show v * (((j : ℂ) + 1) / ((m : ℂ) + (j : ℂ) + 1) * v ^ (m + j + 1)) =
          (((j : ℂ) + 1) / ((m : ℂ) + (j : ℂ) + 1)) * (v * v ^ (m + j + 1)) by ring, hpow2]
      field_simp [hne1, hne2]
      ring
  have hsumm_b : Summable b := by
    have hgeom : Summable (fun j : ℕ => ‖v‖ ^ (m + 2) * ‖v‖ ^ j) :=
      (hasSum_geometric_of_lt_one (norm_nonneg v) hv1).summable.mul_left _
    have hnorm_b : Summable (fun j : ℕ => ‖b j‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun j => ?_) hgeom
      dsimp [b]
      rw [norm_mul, norm_div, norm_mul, Complex.norm_natCast, norm_pow,
        show ‖((m : ℂ) + (j : ℂ) + 1)‖ = (m : ℝ) + (j : ℝ) + 1 by
          rw [show ((m : ℂ) + (j : ℂ) + 1) = (((m : ℝ) + (j : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)],
        show ‖((m : ℂ) + (j : ℂ) + 2)‖ = (m : ℝ) + (j : ℝ) + 2 by
          rw [show ((m : ℂ) + (j : ℂ) + 2) = (((m : ℝ) + (j : ℝ) + 2 : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
      have hfrac : (m : ℝ) / (((m : ℝ) + (j : ℝ) + 1) * ((m : ℝ) + (j : ℝ) + 2)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [Nat.cast_nonneg (α := ℝ) m, Nat.cast_nonneg (α := ℝ) j]
      have hpow : ‖v‖ ^ (m + j + 2) = ‖v‖ ^ (m + 2) * ‖v‖ ^ j := by rw [← pow_add]; congr 1; omega
      rw [hpow]
      exact mul_le_of_le_one_left (by positivity) hfrac
    exact hnorm_b.of_norm
  let tailTerm : ℕ → ℂ := fun j =>
    ((2 * (m : ℂ)) /
      (((m : ℂ) + (j : ℂ) + 1) * ((m : ℂ) + (j : ℂ) + 2) * ((m : ℂ) + (j : ℂ) + 3))) *
        v ^ (m + j + 3)
  have hshift2 : (1 - v) ^ 2 * J m v =
      (1 / ((m : ℂ) + 1)) * v ^ (m + 1) -
        (((2 : ℂ) / (((m : ℂ) + 1) * ((m : ℂ) + 2))) * v ^ (m + 2) + ∑' j : ℕ, tailTerm j) := by
    have h1 : (1 - v) ^ 2 * J m v = (1 - v) * ((1 - v) * J m v) := by ring
    rw [h1, hshift1, mul_add]
    have h2 : (1 - v) * ∑' j : ℕ, b j = b 0 - ∑' j : ℕ, (v * b j - b (j + 1)) := by
      have hsumm_sb : Summable (fun j => b (j + 1)) := (summable_nat_add_iff 1).mpr hsumm_b
      have hsumm_vb : Summable (fun j => v * b j) := hsumm_b.mul_left v
      have hsub := hsumm_vb.tsum_sub hsumm_sb
      have hsplit := hsumm_b.tsum_eq_zero_add
      rw [sub_mul, one_mul, ← tsum_mul_left]
      set S0 := ∑' j, b (j + 1)
      set Sv := ∑' j, v * b j
      rw [hsplit]
      have : Sv - S0 = ∑' j, (v * b j - b (j + 1)) := hsub.symm
      linear_combination -this
    rw [h2]
    have hhead : (1 - v) * (1 / ((m : ℂ) + 1) * v ^ (m + 1)) + b 0 =
        1 / ((m : ℂ) + 1) * v ^ (m + 1) - 2 / (((m : ℂ) + 1) * ((m : ℂ) + 2)) * v ^ (m + 2) := by
      dsimp [b]
      have hne1 : ((m : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
      have hne2 : ((m : ℂ) + 2) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + 1)
      have hpow : v * v ^ (m + 1) = v ^ (m + 2) := (pow_succ' v (m + 1)).symm
      simp only [Nat.cast_zero, add_zero]
      have hv1 : (1 - v) * (1 / ((m : ℂ) + 1) * v ^ (m + 1)) =
          1 / ((m : ℂ) + 1) * v ^ (m + 1) - 1 / ((m : ℂ) + 1) * (v * v ^ (m + 1)) := by ring
      rw [hv1, hpow]
      field_simp [hne1, hne2]
      ring
    have htail_eq : ∑' j : ℕ, (v * b j - b (j + 1)) = ∑' j : ℕ, tailTerm j := by
      congr 1; ext j
      dsimp [b, tailTerm]
      have hne1 : ((m : ℂ) + (j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + j)
      have hne2 : ((m : ℂ) + (j : ℂ) + 2) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + j + 1)
      have hne3 : ((m : ℂ) + (j : ℂ) + 3) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero (m + j + 2)
      have hpow1 : v * v ^ (m + j + 2) = v ^ (m + j + 3) := (pow_succ' v (m + j + 2)).symm
      have hpow2 : v ^ (m + (j + 1) + 2) = v ^ (m + j + 3) := by ring
      have hcast1 : (m : ℂ) + ((j + 1 : ℕ) : ℂ) + 1 = (m : ℂ) + (j : ℂ) + 2 := by push_cast; ring
      have hcast2 : (m : ℂ) + ((j + 1 : ℕ) : ℂ) + 2 = (m : ℂ) + (j : ℂ) + 3 := by push_cast; ring
      rw [hcast1, hcast2,
        show v * ((m : ℂ) / (((m : ℂ) + (j : ℂ) + 1) * ((m : ℂ) + (j : ℂ) + 2)) * v ^ (m + j + 2)) =
          (m : ℂ) / (((m : ℂ) + (j : ℂ) + 1) * ((m : ℂ) + (j : ℂ) + 2)) * (v * v ^ (m + j + 2)) by ring,
        hpow1, hpow2]
      field_simp [hne1, hne2, hne3]
      ring
    rw [htail_eq]
    set Tsum := ∑' j : ℕ, tailTerm j
    linear_combination hhead
  have htail_dom : ∀ j : ℕ, ‖tailTerm j‖ ≤
      (2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) * ‖v‖ ^ (m + 3) * ‖v‖ ^ j := by
    intro j
    dsimp [tailTerm]
    rw [norm_mul, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_natCast, norm_pow,
      show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num,
      show ‖((m : ℂ) + (j : ℂ) + 1)‖ = (m : ℝ) + (j : ℝ) + 1 by
        rw [show ((m : ℂ) + (j : ℂ) + 1) = (((m : ℝ) + (j : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)],
      show ‖((m : ℂ) + (j : ℂ) + 2)‖ = (m : ℝ) + (j : ℝ) + 2 by
        rw [show ((m : ℂ) + (j : ℂ) + 2) = (((m : ℝ) + (j : ℝ) + 2 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)],
      show ‖((m : ℂ) + (j : ℂ) + 3)‖ = (m : ℝ) + (j : ℝ) + 3 by
        rw [show ((m : ℂ) + (j : ℂ) + 3) = (((m : ℝ) + (j : ℝ) + 3 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
    have hfrac : 2 * (m : ℝ) / (((m : ℝ) + (j : ℝ) + 1) * ((m : ℝ) + (j : ℝ) + 2) * ((m : ℝ) + (j : ℝ) + 3)) ≤
        2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      have h12 : ((m : ℝ) + 1) * ((m : ℝ) + 2) ≤ ((m : ℝ) + (j : ℝ) + 1) * ((m : ℝ) + (j : ℝ) + 2) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
      have h3 : (m : ℝ) ≤ (m : ℝ) + (j : ℝ) + 3 := by linarith
      have h123 : (m : ℝ) * (((m : ℝ) + 1) * ((m : ℝ) + 2)) ≤
          ((m : ℝ) + (j : ℝ) + 1) * ((m : ℝ) + (j : ℝ) + 2) * ((m : ℝ) + (j : ℝ) + 3) := by
        calc (m : ℝ) * (((m : ℝ) + 1) * ((m : ℝ) + 2))
            = (((m : ℝ) + 1) * ((m : ℝ) + 2)) * (m : ℝ) := by ring
          _ ≤ (((m : ℝ) + (j : ℝ) + 1) * ((m : ℝ) + (j : ℝ) + 2)) * ((m : ℝ) + (j : ℝ) + 3) :=
              mul_le_mul h12 h3 hm0 (by positivity)
      linarith
    have hpow : ‖v‖ ^ (m + j + 3) = ‖v‖ ^ (m + 3) * ‖v‖ ^ j := by rw [← pow_add]; congr 1; omega
    rw [hpow, mul_assoc (2 / (((m : ℝ) + 1) * ((m : ℝ) + 2)))]
    exact mul_le_mul_of_nonneg_right hfrac (mul_nonneg (pow_nonneg (norm_nonneg v) (m + 3)) (pow_nonneg (norm_nonneg v) j))
  have hgeom0 := (hasSum_geometric_of_lt_one (norm_nonneg v) hv1).mul_left
    ((2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) * ‖v‖ ^ (m + 3))
  have hval0 : (2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) * ‖v‖ ^ (m + 3) * (1 - ‖v‖)⁻¹ =
      (2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) * ‖v‖ ^ (m + 3) / (1 - ‖v‖) :=
    (div_eq_mul_inv _ _).symm
  rw [hval0] at hgeom0
  have hsumm_tail : Summable (fun j => ‖tailTerm j‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) htail_dom hgeom0.summable
  have htail_le : ‖∑' j, tailTerm j‖ ≤ (2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) * ‖v‖ ^ (m + 3) / (1 - ‖v‖) := by
    calc ‖∑' j, tailTerm j‖ ≤ ∑' j, ‖tailTerm j‖ := norm_tsum_le_tsum_norm hsumm_tail
      _ ≤ ∑' j, (2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) * ‖v‖ ^ (m + 3) * ‖v‖ ^ j :=
          hsumm_tail.tsum_le_tsum htail_dom hgeom0.summable
      _ = _ := hgeom0.tsum_eq
  have hrem : ‖((2 : ℂ) / (((m : ℂ) + 1) * ((m : ℂ) + 2))) * v ^ (m + 2) + ∑' j, tailTerm j‖ ≤
      (2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) * ‖v‖ ^ (m + 2) / (1 - ‖v‖) := by
    have hterm2 : ‖((2 : ℂ) / (((m : ℂ) + 1) * ((m : ℂ) + 2))) * v ^ (m + 2)‖ =
        (2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) * ‖v‖ ^ (m + 2) := by
      rw [norm_mul, norm_div, norm_mul, norm_pow,
        show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num,
        show ‖((m : ℂ) + 1)‖ = (m : ℝ) + 1 by
          rw [show ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)],
        show ‖((m : ℂ) + 2)‖ = (m : ℝ) + 2 by
          rw [show ((m : ℂ) + 2) = (((m : ℝ) + 2 : ℝ) : ℂ) by push_cast; rfl,
            Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
    calc ‖((2 : ℂ) / (((m : ℂ) + 1) * ((m : ℂ) + 2))) * v ^ (m + 2) + ∑' j, tailTerm j‖
        ≤ ‖((2 : ℂ) / (((m : ℂ) + 1) * ((m : ℂ) + 2))) * v ^ (m + 2)‖ + ‖∑' j, tailTerm j‖ := norm_add_le _ _
      _ ≤ (2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) * ‖v‖ ^ (m + 2) +
            (2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) * ‖v‖ ^ (m + 3) / (1 - ‖v‖) := by
          rw [hterm2]; linarith
      _ = (2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) * ‖v‖ ^ (m + 2) / (1 - ‖v‖) := by
          have h1v : (1 : ℝ) - ‖v‖ ≠ 0 := by linarith
          have hpow : ‖v‖ ^ (m + 3) = ‖v‖ ^ (m + 2) * ‖v‖ := pow_succ _ _
          rw [hpow]; field_simp [h1v]; ring
  have hrem_half : (2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) * ‖v‖ ^ (m + 2) / (1 - ‖v‖) ≤
      (1 / 2 : ℝ) * (‖v‖ ^ (m + 1) / ((m : ℝ) + 1)) := by
    have h1v : (0 : ℝ) < 1 - ‖v‖ := by linarith
    have hm2 : (0 : ℝ) < (m : ℝ) + 2 := by positivity
    have hcond : 4 / ((m : ℝ) + 2) ≤ 1 - ‖v‖ := by linarith
    have hrat : 2 * ‖v‖ / (((m : ℝ) + 2) * (1 - ‖v‖)) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have : 4 ≤ ((m : ℝ) + 2) * (1 - ‖v‖) := by linarith [(div_le_iff₀ hm2).mp hcond]
      nlinarith [norm_nonneg v]
    have hpow : ‖v‖ ^ (m + 2) = ‖v‖ ^ (m + 1) * ‖v‖ := pow_succ _ _
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [hpow]
    calc (2 / (((m : ℝ) + 1) * ((m : ℝ) + 2))) * (‖v‖ ^ (m + 1) * ‖v‖) / (1 - ‖v‖)
        = (2 * ‖v‖ / (((m : ℝ) + 2) * (1 - ‖v‖))) * (‖v‖ ^ (m + 1) / ((m : ℝ) + 1)) := by
            field_simp [ne_of_gt hm1, ne_of_gt hm2, ne_of_gt h1v]
      _ ≤ (1 / 2 : ℝ) * (‖v‖ ^ (m + 1) / ((m : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hrat (by positivity)
  have hmain : ‖(1 / ((m : ℂ) + 1)) * v ^ (m + 1)‖ = ‖v‖ ^ (m + 1) / ((m : ℝ) + 1) := by
    rw [norm_mul, norm_div, norm_one, norm_pow,
      show ‖((m : ℂ) + 1)‖ = (m : ℝ) + 1 by
        rw [show ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]]
    ring
  have hlow : (1 / 2 : ℝ) * (‖v‖ ^ (m + 1) / ((m : ℝ) + 1)) ≤ ‖(1 - v) ^ 2 * J m v‖ := by
    rw [hshift2]
    have hrev := norm_sub_norm_le ((1 / ((m : ℂ) + 1)) * v ^ (m + 1))
      (((2 : ℂ) / (((m : ℂ) + 1) * ((m : ℂ) + 2))) * v ^ (m + 2) + ∑' j, tailTerm j)
    rw [hmain] at hrev
    linarith
  have h1v2 : ‖(1 - v) ^ 2‖ ≤ 4 := by
    rw [norm_pow]
    have h1 : ‖(1 : ℂ) - v‖ ≤ 2 := by
      calc ‖(1 : ℂ) - v‖ ≤ ‖(1 : ℂ)‖ + ‖v‖ := norm_sub_le _ _
        _ ≤ 1 + 1 := by rw [norm_one]; linarith
        _ = 2 := by norm_num
    nlinarith [norm_nonneg ((1 : ℂ) - v)]
  rw [norm_mul] at hlow
  have h4J : ‖(1 - v) ^ 2‖ * ‖J m v‖ ≤ 4 * ‖J m v‖ :=
    mul_le_mul_of_nonneg_right h1v2 (norm_nonneg _)
  have hdiv8 : ‖v‖ ^ (m + 1) / (8 * ((m : ℝ) + 1)) = (1 / 4 : ℝ) * ((1 / 2 : ℝ) * (‖v‖ ^ (m + 1) / ((m : ℝ) + 1))) := by
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    field_simp [ne_of_gt hm1]; ring
  linarith

lemma norm_H_ge (m : ℕ) (hm : 1 ≤ m) {z : ℂ} (hz : ‖z‖ < 1)
    (hB : ‖B z‖ ≤ 1 - 4 / ((m : ℝ) + 2)) :
    ‖B z‖ ^ (m + 1) / (5 * ((m : ℝ) + 1)) ≤ ‖H m z‖ := by
  rw [H_eq_J_B m hz, norm_mul, show ‖(5 / 3 : ℂ)‖ = (5 / 3 : ℝ) by norm_num]
  have hJ := norm_J_ge m hm (norm_B_lt_one_of_norm_lt_one hz) hB
  have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hpos : (0 : ℝ) ≤ ‖B z‖ ^ (m + 1) / ((m : ℝ) + 1) := by positivity
  have heq1 : ‖B z‖ ^ (m + 1) / (5 * ((m : ℝ) + 1)) = (1 / 5 : ℝ) * (‖B z‖ ^ (m + 1) / ((m : ℝ) + 1)) := by
    field_simp [ne_of_gt hm1]
  have heq2 : (5 / 24 : ℝ) * (‖B z‖ ^ (m + 1) / ((m : ℝ) + 1)) =
      (5 / 3 : ℝ) * (‖B z‖ ^ (m + 1) / (8 * ((m : ℝ) + 1))) := by
    field_simp [ne_of_gt hm1]; ring
  calc ‖B z‖ ^ (m + 1) / (5 * ((m : ℝ) + 1))
      = (1 / 5 : ℝ) * (‖B z‖ ^ (m + 1) / ((m : ℝ) + 1)) := heq1
    _ ≤ (5 / 24 : ℝ) * (‖B z‖ ^ (m + 1) / ((m : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hpos
    _ = (5 / 3 : ℝ) * (‖B z‖ ^ (m + 1) / (8 * ((m : ℝ) + 1))) := heq2
    _ ≤ (5 / 3 : ℝ) * ‖J m (B z)‖ := mul_le_mul_of_nonneg_left hJ (by norm_num)

-- ============================================================================
-- Section 4: Polynomial properties, root localization, and algebraic disproof
-- ============================================================================

lemma polyP_boundedMonic (n : ℕ) : OMA.S_mse_5120935.BoundedMonic n 1 (polyP n) := by
  dsimp [OMA.S_mse_5120935.BoundedMonic, polyP]
  split_ifs with hlt
  · refine ⟨monic_X_pow n, natDegree_X_pow n, fun j hj => ?_⟩
    rw [coeff_X_pow, if_neg (ne_of_lt hj), norm_zero]; norm_num
  · set m := n / 16
    set S : ℂ[X] := ∑ j ∈ Finset.range n, C (aCoeff m j : ℂ) * X ^ j
    have hcoeff_S : ∀ j : ℕ, S.coeff j = if j < n then (aCoeff m j : ℂ) else 0 := by
      intro j
      dsimp [S]
      rw [finsetSum_coeff]
      simp_rw [coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq (Finset.range n) j]
      simp [Finset.mem_range]
    have hdeg_S : S.degree < (X ^ n : ℂ[X]).degree := by
      rw [degree_X_pow]
      by_cases hS : S = 0
      · rw [hS, degree_zero]; exact WithBot.bot_lt_coe n
      · rw [Polynomial.degree_lt_iff_coeff_zero]
        intro k hk
        rw [hcoeff_S k, if_neg (not_lt.mpr hk)]
    have hmonic : (X ^ n + S).Monic := (monic_X_pow n).add_of_left hdeg_S
    have hdeg : (X ^ n + S).natDegree = n := by
      rw [natDegree_add_eq_left_of_degree_lt hdeg_S, natDegree_X_pow]
    refine ⟨hmonic, hdeg, fun j hj => ?_⟩
    rw [coeff_add, coeff_X_pow, if_neg (ne_of_lt hj), zero_add, hcoeff_S j, if_pos hj,
      Complex.norm_real, Real.norm_eq_abs]
    exact abs_aCoeff_le_one m j

lemma polyP_coeff_eq {n : ℕ} (hn : 2400 ≤ n) {j : ℕ} (hj : j < n) :
    (polyP n).coeff j = (aCoeff (n / 16) j : ℂ) := by
  dsimp [polyP]
  rw [if_neg (not_lt.mpr hn), coeff_add, coeff_X_pow, if_neg (ne_of_lt hj), zero_add,
    finsetSum_coeff]
  simp_rw [coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq (Finset.range n) j, if_pos (Finset.mem_range.mpr hj)]

lemma polyP_eval_sub_H {n : ℕ} (hn : 2400 ≤ n) {z : ℂ} (hz : ‖z‖ < 1) :
    ‖(polyP n).eval z - H (n / 16) z‖ ≤ 2 * ‖z‖ ^ n / (1 - ‖z‖) := by
  set m := n / 16
  have hsplit_n : n = (n - 1) + 1 := by omega
  have hsum_split : ∑ j ∈ Finset.range n, (aCoeff m j : ℂ) * z ^ j =
      -(Cm m : ℂ) + ∑ k ∈ Finset.range (n - 1), (sigma m k : ℂ) * z ^ (k + 1) := by
    conv_lhs => rw [hsplit_n, Finset.sum_range_succ']
    simp only [pow_zero, mul_one, aCoeff, ofReal_neg]
    ring
  have heval : (polyP n).eval z =
      z ^ n - (Cm m : ℂ) + ∑ k ∈ Finset.range (n - 1), (sigma m k : ℂ) * z ^ (k + 1) := by
    dsimp [polyP]
    rw [if_neg (not_lt.mpr hn), eval_add, eval_pow, eval_X, eval_finsetSum]
    have hterms : ∑ j ∈ Finset.range n, eval z (C (aCoeff m j : ℂ) * X ^ j) =
        ∑ j ∈ Finset.range n, (aCoeff m j : ℂ) * z ^ j :=
      Finset.sum_congr rfl (fun j _ => by simp)
    rw [hterms, hsum_split]
    ring
  have hsumm_sig : Summable (fun k : ℕ => (sigma m k : ℂ) * z ^ (k + 1)) := by
    have hgeom : Summable (fun k : ℕ => ‖z‖ * ‖z‖ ^ k) :=
      (hasSum_geometric_of_lt_one (norm_nonneg z) hz).summable.mul_left ‖z‖
    have hnorm_sig : Summable (fun k : ℕ => ‖(sigma m k : ℂ) * z ^ (k + 1)‖) := by
      refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hgeom
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, pow_succ']
      exact mul_le_of_le_one_left (mul_nonneg (norm_nonneg z) (pow_nonneg (norm_nonneg z) k)) (abs_sigma_le_one m k)
    exact hnorm_sig.of_norm
  have hsplit_H := hsumm_sig.sum_add_tsum_nat_add (n - 1)
  have htail_idx : (∑' j : ℕ, (sigma m (j + (n - 1)) : ℂ) * z ^ (j + (n - 1) + 1)) =
      ∑' j : ℕ, (sigma m (j + (n - 1)) : ℂ) * z ^ (j + n) := by
    congr 1; ext j; congr 2; omega
  have hdiff : (polyP n).eval z - H m z =
      z ^ n - ∑' j : ℕ, (sigma m (j + (n - 1)) : ℂ) * z ^ (j + n) := by
    have hHdef : H m z = -(Cm m : ℂ) + ∑' k : ℕ, (sigma m k : ℂ) * z ^ (k + 1) := rfl
    rw [heval, hHdef, ← hsplit_H, htail_idx]
    set Sfin := ∑ k ∈ Finset.range (n - 1), (sigma m k : ℂ) * z ^ (k + 1)
    set Stail := ∑' j : ℕ, (sigma m (j + (n - 1)) : ℂ) * z ^ (j + n)
    ring
  rw [hdiff]
  have hgeom0 := (hasSum_geometric_of_lt_one (norm_nonneg z) hz).mul_left (‖z‖ ^ n)
  have hv0 : ‖z‖ ^ n * (1 - ‖z‖)⁻¹ = ‖z‖ ^ n / (1 - ‖z‖) := by rw [div_eq_mul_inv]
  rw [hv0] at hgeom0
  have hdom : ∀ j : ℕ, ‖(sigma m (j + (n - 1)) : ℂ) * z ^ (j + n)‖ ≤ ‖z‖ ^ n * ‖z‖ ^ j := by
    intro j
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_pow, pow_add, mul_comm (‖z‖ ^ j)]
    exact mul_le_of_le_one_left (by positivity) (abs_sigma_le_one m _)
  have hsumm_norm : Summable (fun j : ℕ => ‖(sigma m (j + (n - 1)) : ℂ) * z ^ (j + n)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hdom hgeom0.summable
  have htail_le : ‖∑' j : ℕ, (sigma m (j + (n - 1)) : ℂ) * z ^ (j + n)‖ ≤ ‖z‖ ^ n / (1 - ‖z‖) := by
    calc ‖∑' j : ℕ, (sigma m (j + (n - 1)) : ℂ) * z ^ (j + n)‖
        ≤ ∑' j : ℕ, ‖(sigma m (j + (n - 1)) : ℂ) * z ^ (j + n)‖ := norm_tsum_le_tsum_norm hsumm_norm
      _ ≤ ∑' j : ℕ, ‖z‖ ^ n * ‖z‖ ^ j := hsumm_norm.tsum_le_tsum hdom hgeom0.summable
      _ = ‖z‖ ^ n / (1 - ‖z‖) := hgeom0.tsum_eq
  have hzn : ‖z‖ ^ n ≤ ‖z‖ ^ n / (1 - ‖z‖) :=
    le_div_self (by positivity) (by linarith) (by linarith [norm_nonneg z])
  calc ‖z ^ n - ∑' j : ℕ, (sigma m (j + (n - 1)) : ℂ) * z ^ (j + n)‖
      ≤ ‖z ^ n‖ + ‖∑' j : ℕ, (sigma m (j + (n - 1)) : ℂ) * z ^ (j + n)‖ := norm_sub_le _ _
    _ = ‖z‖ ^ n + ‖∑' j : ℕ, (sigma m (j + (n - 1)) : ℂ) * z ^ (j + n)‖ := by rw [norm_pow]
    _ ≤ ‖z‖ ^ n / (1 - ‖z‖) + ‖z‖ ^ n / (1 - ‖z‖) := by linarith
    _ = 2 * ‖z‖ ^ n / (1 - ‖z‖) := by ring

lemma three_halves_pow_gt (m : ℕ) (hm : 150 ≤ m) :
    (100000000 : ℝ) * ((m : ℝ) + 1) < (3 / 2 : ℝ) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [pow_succ]
    push_cast
    have hk' : (150 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    nlinarith

lemma polyP_root_loc {n : ℕ} (hn : 2400 ≤ n) {w : ℂ} (hw : w ∈ (polyP n).roots) :
    ‖w - (1 / 4 : ℂ)‖ < 1 / 100000 ∨ (95 / 100 : ℝ) < ‖w‖ := by
  by_contra h
  push Not at h
  rcases h with ⟨hfar, hle95⟩
  set m := n / 16
  have hm : 150 ≤ m := by omega
  have h16m : 16 * m ≤ n := Nat.mul_div_le n 16
  have hw1 : ‖w‖ < 1 := by linarith
  have hB_lower : (3 / 2 : ℝ) * ‖w‖ ^ 16 ≤ ‖B w‖ ∧ (6 / 1000000 : ℝ) ≤ ‖B w‖ := by
    by_cases h1 : ‖w‖ ≤ 30 / 100
    · have hd_le : ‖(1 : ℂ) - (1 / 4 : ℂ) * w‖ ≤ 3 / 2 := by
        calc ‖(1 : ℂ) - (1 / 4 : ℂ) * w‖ ≤ ‖(1 : ℂ)‖ + ‖(1 / 4 : ℂ) * w‖ := norm_sub_le _ _
          _ = 1 + (1 / 4 : ℝ) * ‖w‖ := by rw [norm_one, norm_mul]; norm_num
          _ ≤ 3 / 2 := by linarith
      have hd_pos : 0 < ‖(1 : ℂ) - (1 / 4 : ℂ) * w‖ :=
        norm_pos_iff.mpr (denom_ne_zero_of_norm_lt_four (by linarith))
      have hB6 : (6 / 1000000 : ℝ) ≤ ‖B w‖ := by
        rw [B, norm_div, le_div_iff₀ hd_pos]
        nlinarith
      have hw16 : (3 / 2 : ℝ) * ‖w‖ ^ 16 ≤ 6 / 1000000 := by
        have := pow_le_pow_left₀ (norm_nonneg w) h1 16
        linarith [show (3 / 2 : ℝ) * (30 / 100 : ℝ) ^ 16 ≤ 6 / 1000000 by norm_num]
      exact ⟨le_trans hw16 hB6, hB6⟩
    · push Not at h1
      have hB_mon : (‖w‖ - 1 / 4) / (1 - ‖w‖ / 4) ≤ ‖B w‖ :=
        norm_B_ge_of_norm_lt_one hw1 (by linarith)
      by_cases h2 : ‖w‖ ≤ 80 / 100
      · have hB_val : (54 / 1000 : ℝ) ≤ ‖B w‖ := by
          have : (54 / 1000 : ℝ) ≤ (‖w‖ - 1 / 4) / (1 - ‖w‖ / 4) := by
            rw [le_div_iff₀ (by linarith)]; linarith
          exact le_trans this hB_mon
        have hw16 : (3 / 2 : ℝ) * ‖w‖ ^ 16 ≤ 54 / 1000 := by
          have := pow_le_pow_left₀ (norm_nonneg w) h2 16
          linarith [show (3 / 2 : ℝ) * (80 / 100 : ℝ) ^ 16 ≤ 54 / 1000 by norm_num]
        exact ⟨le_trans hw16 hB_val, by linarith⟩
      · push Not at h2
        have hB_val : (68 / 100 : ℝ) ≤ ‖B w‖ := by
          have : (68 / 100 : ℝ) ≤ (‖w‖ - 1 / 4) / (1 - ‖w‖ / 4) := by
            rw [le_div_iff₀ (by linarith)]; linarith
          exact le_trans this hB_mon
        have hw16 : (3 / 2 : ℝ) * ‖w‖ ^ 16 ≤ 68 / 100 := by
          have := pow_le_pow_left₀ (norm_nonneg w) hle95 16
          linarith [show (3 / 2 : ℝ) * (95 / 100 : ℝ) ^ 16 ≤ 68 / 100 by norm_num]
        exact ⟨le_trans hw16 hB_val, by linarith⟩
  have hB_up : ‖B w‖ ≤ 1 - 4 / ((m : ℝ) + 2) := by
    have h1 := norm_B_le_of_norm_le (R := 95 / 100) (by norm_num) hle95
    have h2 : (95 / 100 + 1 / 4 : ℝ) / (1 + (95 / 100) / 4) = 32 / 33 := by norm_num
    rw [h2] at h1
    have h3 : 4 / ((m : ℝ) + 2) ≤ 1 / 33 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have hm' : (150 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
      linarith
    linarith
  have hH_ge := norm_H_ge m (by omega) hw1 hB_up
  have htrunc := polyP_eval_sub_H hn hw1
  have heval0 : (polyP n).eval w = 0 := (mem_roots (polyP_boundedMonic n).1.ne_zero).mp hw
  rw [heval0, zero_sub, norm_neg] at htrunc
  have hzn_le : ‖w‖ ^ n ≤ ‖w‖ ^ (16 * m) :=
    pow_le_pow_of_le_one (norm_nonneg w) (le_of_lt hw1) h16m
  have htrunc40 : ‖H m w‖ ≤ 40 * ‖w‖ ^ (16 * m) := by
    have h1 : 2 * ‖w‖ ^ n / (1 - ‖w‖) ≤ 40 * ‖w‖ ^ (16 * m) := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [pow_nonneg (norm_nonneg w) (16 * m)]
    exact le_trans htrunc h1
  have hB_pow : (6 / 1000000 : ℝ) * ((3 / 2 : ℝ) ^ m * ‖w‖ ^ (16 * m)) ≤ ‖B w‖ ^ (m + 1) := by
    rw [pow_succ', pow_mul]
    have hpow := pow_le_pow_left₀ (by positivity) hB_lower.1 m
    rw [mul_pow] at hpow
    exact mul_le_mul hB_lower.2 hpow (by positivity) (by norm_num)
  have hbig := three_halves_pow_gt m hm
  have hstrict : 40 * ‖w‖ ^ (16 * m) < ‖B w‖ ^ (m + 1) / (5 * ((m : ℝ) + 1)) := by
    rw [lt_div_iff₀ (by positivity)]
    by_cases hw0 : ‖w‖ = 0
    · rw [hw0, zero_pow (by omega : 16 * m ≠ 0), mul_zero, zero_mul]
      have hBpos : 0 < ‖B w‖ := by linarith [hB_lower.2]
      positivity
    · have hw16_pos : 0 < ‖w‖ ^ (16 * m) := pow_pos (lt_of_le_of_ne (norm_nonneg w) (Ne.symm hw0)) _
      have hcoef : 40 * (5 * ((m : ℝ) + 1)) < (6 / 1000000 : ℝ) * (3 / 2 : ℝ) ^ m := by linarith
      have hmul := mul_lt_mul_of_pos_right hcoef hw16_pos
      linarith
  linarith

lemma polyPk_no_root_near {n k : ℕ} (hn : 2400 ≤ n) (hk1 : 4 * (n / 16) ≤ k)
    (hk2 : k < 5 * (n / 16)) {ζ : ℂ}
    (hζ : ζ ∈ (polyP n - C ((polyP n).coeff k) * X ^ k).roots) :
    (1 / 2500 : ℝ) < ‖ζ - (1 / 4 : ℂ)‖ := by
  by_contra h
  push Not at h
  set m := n / 16
  have hm : 150 ≤ m := by omega
  have hkn : k < n := by omega
  have h16m : 16 * m ≤ n := Nat.mul_div_le n 16
  have hζ_up : ‖ζ‖ ≤ 2504 / 10000 := by
    have htri : ‖ζ‖ ≤ ‖ζ - (1 / 4 : ℂ)‖ + ‖(1 / 4 : ℂ)‖ := by
      simpa using norm_add_le (ζ - (1 / 4 : ℂ)) (1 / 4 : ℂ)
    rw [show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num] at htri
    linarith
  have hζ_low : (2496 / 10000 : ℝ) ≤ ‖ζ‖ := by
    have htri : ‖(1 / 4 : ℂ)‖ - ‖ζ‖ ≤ ‖ζ - (1 / 4 : ℂ)‖ := by
      have := norm_sub_norm_le (1 / 4 : ℂ) ζ
      rwa [norm_sub_rev] at this
    rw [show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num] at htri
    linarith
  have hζ1 : ‖ζ‖ < 1 := by linarith
  have hak_ge : (1 / 2 : ℝ) ≤ ‖(polyP n).coeff k‖ := by
    rw [polyP_coeff_eq hn hkn]
    have hk_eq : k = (k - 1) + 1 := by omega
    rw [hk_eq, aCoeff, Complex.norm_real, Real.norm_eq_abs]
    have hsig := sigma_ge_half m (k - 1) (by omega) (by omega)
    exact le_trans hsig (le_abs_self _)
  have hterm_ge : (1 / 2 : ℝ) * (96 / 100000 : ℝ) ^ m ≤ ‖(polyP n).coeff k * ζ ^ k‖ := by
    rw [norm_mul, norm_pow]
    have hpow1 : (2496 / 10000 : ℝ) ^ (5 * m) ≤ ‖ζ‖ ^ k := by
      calc (2496 / 10000 : ℝ) ^ (5 * m)
          ≤ (2496 / 10000 : ℝ) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_of_lt hk2)
        _ ≤ ‖ζ‖ ^ k := pow_le_pow_left₀ (by norm_num) hζ_low k
    have hpow2 : (96 / 100000 : ℝ) ^ m ≤ (2496 / 10000 : ℝ) ^ (5 * m) := by
      rw [pow_mul]
      exact pow_le_pow_left₀ (by norm_num) (by norm_num) m
    exact mul_le_mul hak_ge (le_trans hpow2 hpow1) (by positivity) (norm_nonneg _)
  have hB_le : ‖B ζ‖ ≤ 45 / 100000 := by
    have hd_ge : (93 / 100 : ℝ) ≤ ‖(1 : ℂ) - (1 / 4 : ℂ) * ζ‖ := by
      have hrev := norm_sub_norm_le (1 : ℂ) ((1 / 4 : ℂ) * ζ)
      rw [norm_one, norm_mul, show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num] at hrev
      linarith
    rw [B, norm_div, div_le_iff₀ (by linarith)]
    linarith
  have hH_le : ‖H m ζ‖ ≤ 2 * (45 / 100000 : ℝ) ^ m := by
    have h1 := norm_H_le m hζ1
    have h2 : ‖B ζ‖ ^ (m + 1) ≤ (45 / 100000 : ℝ) ^ m := by
      rw [pow_succ']
      calc ‖B ζ‖ * ‖B ζ‖ ^ m ≤ 1 * (45 / 100000 : ℝ) ^ m :=
            mul_le_mul (by linarith) (pow_le_pow_left₀ (norm_nonneg _) hB_le m) (by positivity) (by norm_num)
        _ = (45 / 100000 : ℝ) ^ m := one_mul _
    have h3 : (5 / 3 : ℝ) / (1 - ‖B ζ‖) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    calc ‖H m ζ‖ ≤ (5 / 3 : ℝ) * (‖B ζ‖ ^ (m + 1) / (1 - ‖B ζ‖)) := h1
      _ = ((5 / 3 : ℝ) / (1 - ‖B ζ‖)) * ‖B ζ‖ ^ (m + 1) := by ring
      _ ≤ 2 * (45 / 100000 : ℝ) ^ m := mul_le_mul h3 h2 (by positivity) (by norm_num)
  have htrunc_le : ‖(polyP n).eval ζ - H m ζ‖ ≤ 3 * (45 / 100000 : ℝ) ^ m := by
    have h1 := polyP_eval_sub_H hn hζ1
    have hpow : ‖ζ‖ ^ n ≤ (45 / 100000 : ℝ) ^ m := by
      calc ‖ζ‖ ^ n ≤ ‖ζ‖ ^ (16 * m) := pow_le_pow_of_le_one (norm_nonneg _) (le_of_lt hζ1) h16m
        _ ≤ (2504 / 10000 : ℝ) ^ (16 * m) := pow_le_pow_left₀ (norm_nonneg _) hζ_up _
        _ = ((2504 / 10000 : ℝ) ^ 16) ^ m := pow_mul _ _ _
        _ ≤ (45 / 100000 : ℝ) ^ m := pow_le_pow_left₀ (by positivity) (by norm_num) m
    have hdiv : 2 / (1 - ‖ζ‖) ≤ 3 := by rw [div_le_iff₀ (by linarith)]; linarith
    calc ‖(polyP n).eval ζ - H m ζ‖ ≤ (2 / (1 - ‖ζ‖)) * ‖ζ‖ ^ n := by
          convert h1 using 1; ring
      _ ≤ 3 * (45 / 100000 : ℝ) ^ m := mul_le_mul hdiv hpow (by positivity) (by norm_num)
  have hP_le : ‖(polyP n).eval ζ‖ ≤ 5 * (45 / 100000 : ℝ) ^ m := by
    have htri : ‖(polyP n).eval ζ‖ ≤ ‖H m ζ‖ + ‖(polyP n).eval ζ - H m ζ‖ := by
      have := norm_add_le (H m ζ) ((polyP n).eval ζ - H m ζ)
      simpa using this
    linarith
  have hQ_monic : (polyP n - C ((polyP n).coeff k) * X ^ k).Monic := by
    have hdeg_lt : (C ((polyP n).coeff k) * X ^ k).degree < (polyP n).degree := by
      rw [Polynomial.degree_eq_natDegree (polyP_boundedMonic n).1.ne_zero, (polyP_boundedMonic n).2.1]
      exact lt_of_le_of_lt (degree_C_mul_X_pow_le k ((polyP n).coeff k)) (WithBot.coe_lt_coe.mpr hkn)
    exact (polyP_boundedMonic n).1.sub_of_left hdeg_lt
  have heval0 : (polyP n - C ((polyP n).coeff k) * X ^ k).eval ζ = 0 :=
    (mem_roots hQ_monic.ne_zero).mp hζ
  simp only [eval_sub, eval_mul, eval_C, eval_pow, eval_X] at heval0
  have heq : (polyP n).eval ζ = (polyP n).coeff k * ζ ^ k := sub_eq_zero.mp heval0
  rw [heq] at hP_le
  have hratio : (10 : ℝ) < (96 / 45 : ℝ) ^ m := by
    have h1 : (96 / 45 : ℝ) ^ 4 ≤ (96 / 45 : ℝ) ^ m :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    linarith [show (10 : ℝ) < (96 / 45 : ℝ) ^ 4 by norm_num]
  have hstrict : 5 * (45 / 100000 : ℝ) ^ m < (1 / 2 : ℝ) * (96 / 100000 : ℝ) ^ m := by
    have hmul := mul_lt_mul_of_pos_right hratio (by positivity : (0 : ℝ) < (45 / 100000 : ℝ) ^ m)
    have hpow : (96 / 45 : ℝ) ^ m * (45 / 100000 : ℝ) ^ m = (96 / 100000 : ℝ) ^ m := by
      rw [← mul_pow]; norm_num
    rw [hpow] at hmul
    linarith
  linarith

lemma norm_multiset_prod_eq (s : Multiset ℂ) :
    ‖s.prod‖ = (s.map (fun z => ‖z‖)).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih => simp [ih]

lemma multiset_pow_card_le_prod {s : Multiset ℝ} {b : ℝ} (hb : 0 ≤ b)
    (h : ∀ x ∈ s, b ≤ x) : b ^ s.card ≤ s.prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    rw [Multiset.card_cons, pow_succ', Multiset.prod_cons]
    have ha : b ≤ a := h a (Multiset.mem_cons_self a t)
    have ht : b ^ t.card ≤ t.prod := ih (fun x hx => h x (Multiset.mem_cons_of_mem hx))
    exact mul_le_mul ha ht (pow_nonneg hb t.card) (le_trans hb ha)

open Classical in
lemma polyPk_far_roots_ge {n k : ℕ} (hn : 2400 ≤ n) (hk1 : 4 * (n / 16) ≤ k)
    (hk2 : k < 5 * (n / 16)) :
    n ≤ 50 * ((polyP n - C ((polyP n).coeff k) * X ^ k).roots.filter
      (OMA.S_mse_5120935.IsFar (polyP n) (1 / 5000))).card := by
  set m := n / 16
  set Q : ℂ[X] := polyP n - C ((polyP n).coeff k) * X ^ k
  let ε : ℝ := 1 / 5000
  have hkn : k < n := by omega
  have hdeg_lt : (C ((polyP n).coeff k) * X ^ k).degree < (polyP n).degree := by
    rw [Polynomial.degree_eq_natDegree (polyP_boundedMonic n).1.ne_zero, (polyP_boundedMonic n).2.1]
    exact lt_of_le_of_lt (degree_C_mul_X_pow_le k ((polyP n).coeff k)) (WithBot.coe_lt_coe.mpr hkn)
  have hQ_monic : Q.Monic := (polyP_boundedMonic n).1.sub_of_left hdeg_lt
  have hQ_deg : Q.natDegree = n := by
    have hsub : Q = polyP n + -(C ((polyP n).coeff k) * X ^ k) := sub_eq_add_neg _ _
    rw [hsub, natDegree_add_eq_left_of_degree_lt (by simpa [degree_neg] using hdeg_lt),
      (polyP_boundedMonic n).2.1]
  have hQ_card : Q.roots.card = n := by
    rw [← hQ_deg, ← (IsAlgClosed.splits Q).natDegree_eq_card_roots]
  have hQ_prod : (Q.roots.map (fun ζ => X - C ζ)).prod = Q :=
    Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQ_monic (by rw [hQ_card, hQ_deg])
  have hQ_r_le : ‖Q.eval (1 / 4 : ℂ)‖ ≤ 4 * (1 / 4 : ℝ) ^ k := by
    have hev : Q.eval (1 / 4 : ℂ) = (polyP n).eval (1 / 4 : ℂ) - (polyP n).coeff k * (1 / 4 : ℂ) ^ k := by
      simp [Q]
    rw [hev]
    have hHr : H m (1 / 4 : ℂ) = 0 := by
      rw [H_eq_J_B m (by norm_num)]
      simp [B, J, zero_pow (Nat.succ_ne_zero _)]
    have hP_r : ‖(polyP n).eval (1 / 4 : ℂ)‖ ≤ 3 * (1 / 4 : ℝ) ^ n := by
      have h := polyP_eval_sub_H hn (z := (1 / 4 : ℂ)) (by norm_num)
      rw [hHr, sub_zero, show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num] at h
      have h83 : 2 * (1 / 4 : ℝ) ^ n / (1 - (1 / 4 : ℝ)) = (8 / 3 : ℝ) * (1 / 4 : ℝ) ^ n := by ring
      rw [h83] at h
      nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) n]
    have hcoeff_le : ‖(polyP n).coeff k‖ ≤ 1 := (polyP_boundedMonic n).2.2 k hkn
    have hpow_le : (1 / 4 : ℝ) ^ n ≤ (1 / 4 : ℝ) ^ k :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (le_of_lt hkn)
    calc ‖(polyP n).eval (1 / 4 : ℂ) - (polyP n).coeff k * (1 / 4 : ℂ) ^ k‖
        ≤ ‖(polyP n).eval (1 / 4 : ℂ)‖ + ‖(polyP n).coeff k * (1 / 4 : ℂ) ^ k‖ := norm_sub_le _ _
      _ ≤ 3 * (1 / 4 : ℝ) ^ n + 1 * (1 / 4 : ℝ) ^ k := by
          rw [norm_mul, norm_pow, show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num]
          nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) k]
      _ ≤ 4 * (1 / 4 : ℝ) ^ k := by linarith
  have hQ_4_ge : (2 / 3 : ℝ) ≤ ‖(1 / 4 : ℂ) ^ n * Q.eval 4‖ := by
    have hQ_sum : Q = X ^ n + ∑ j ∈ Finset.range n, C (Q.coeff j) * X ^ j := by
      ext j
      rw [coeff_add, coeff_X_pow, finsetSum_coeff]
      simp_rw [coeff_C_mul_X_pow]
      rw [Finset.sum_ite_eq (Finset.range n) j]
      by_cases hj : j < n
      · rw [if_neg (ne_of_lt hj), zero_add, if_pos (Finset.mem_range.mpr hj)]
      · by_cases hjn : j = n
        · rw [hjn, if_pos rfl, if_neg (by simp), add_zero]
          have := hQ_monic.leadingCoeff
          rw [Polynomial.leadingCoeff, hQ_deg] at this
          exact this
        · rw [if_neg hjn, if_neg (by simp; omega), add_zero]
          exact coeff_eq_zero_of_natDegree_lt (p := Q) (n := j) (by rw [hQ_deg]; omega)
    have hev4 : (1 / 4 : ℂ) ^ n * Q.eval 4 =
        1 + ∑ j ∈ Finset.range n, Q.coeff j * (1 / 4 : ℂ) ^ (n - j) := by
      conv_lhs => rw [hQ_sum]
      rw [eval_add, eval_pow, eval_X, eval_finsetSum, mul_add, Finset.mul_sum]
      congr 1
      · rw [← mul_pow]; norm_num
      · refine Finset.sum_congr rfl (fun j hj => ?_)
        rw [Finset.mem_range] at hj
        simp only [eval_mul, eval_C, eval_pow, eval_X]
        have hpow : (1 / 4 : ℂ) ^ n * (4 : ℂ) ^ j = (1 / 4 : ℂ) ^ (n - j) := by
          have hnj : n = (n - j) + j := (Nat.sub_add_cancel (le_of_lt hj)).symm
          conv_lhs => rw [hnj, pow_add]
          rw [mul_assoc, ← mul_pow]; norm_num
        calc (1 / 4 : ℂ) ^ n * (Q.coeff j * (4 : ℂ) ^ j)
            = Q.coeff j * ((1 / 4 : ℂ) ^ n * (4 : ℂ) ^ j) := by ring
          _ = Q.coeff j * (1 / 4 : ℂ) ^ (n - j) := by rw [hpow]
    have hcoeff_Q : ∀ j ∈ Finset.range n, ‖Q.coeff j‖ ≤ 1 := by
      intro j hj
      rw [Finset.mem_range] at hj
      dsimp [Q]
      rw [coeff_sub, coeff_C_mul_X_pow]
      split_ifs with hjk
      · subst hjk; simp
      · rw [sub_zero]; exact (polyP_boundedMonic n).2.2 j hj
    have hsum_le : ‖∑ j ∈ Finset.range n, Q.coeff j * (1 / 4 : ℂ) ^ (n - j)‖ ≤ 1 / 3 := by
      calc ‖∑ j ∈ Finset.range n, Q.coeff j * (1 / 4 : ℂ) ^ (n - j)‖
          ≤ ∑ j ∈ Finset.range n, ‖Q.coeff j * (1 / 4 : ℂ) ^ (n - j)‖ := norm_sum_le _ _
        _ ≤ ∑ j ∈ Finset.range n, (1 / 4 : ℝ) ^ (n - j) := by
            refine Finset.sum_le_sum (fun j hj => ?_)
            rw [norm_mul, norm_pow, show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num]
            exact mul_le_of_le_one_left (by positivity) (hcoeff_Q j hj)
        _ = ∑ t ∈ Finset.range n, (1 / 4 : ℝ) ^ (t + 1) := by
            refine Finset.sum_nbij (fun j => n - 1 - j) ?_ ?_ ?_ ?_
            · intro j hj; rw [Finset.mem_range] at hj ⊢; omega
            · intro j1 hj1 j2 hj2 h
              rw [Finset.mem_coe, Finset.mem_range] at hj1 hj2
              dsimp at h; omega
            · intro t ht
              rw [Finset.mem_coe, Finset.mem_range] at ht
              exact ⟨n - 1 - t, Finset.mem_coe.mpr (Finset.mem_range.mpr (by omega)), by dsimp; omega⟩
            · intro j hj; rw [Finset.mem_range] at hj; congr 1; omega
        _ ≤ 1 / 3 :=
            hasSum_quarter_succ.summable.sum_le_tsum (Finset.range n) (fun _ _ => by positivity)
              |>.trans_eq hasSum_quarter_succ.tsum_eq
    rw [hev4]
    have hrev := norm_sub_norm_le (1 : ℂ) (-(∑ j ∈ Finset.range n, Q.coeff j * (1 / 4 : ℂ) ^ (n - j)))
    rw [sub_neg_eq_add, norm_one, norm_neg] at hrev
    linarith
  have hprod_num : (Q.roots.map (fun ζ => ‖ζ - (1 / 4 : ℂ)‖)).prod = ‖Q.eval (1 / 4 : ℂ)‖ := by
    have h := congr_arg (fun p => ‖p.eval (1 / 4 : ℂ)‖) hQ_prod
    rw [eval_multiset_prod, norm_multiset_prod_eq, Multiset.map_map, Multiset.map_map] at h
    rw [← h]
    congr 1; refine Multiset.map_congr rfl (fun ζ _ => ?_)
    simp [norm_sub_rev]
  have hprod_den : (Q.roots.map (fun ζ => ‖(1 : ℂ) - (1 / 4 : ℂ) * ζ‖)).prod =
      ‖(1 / 4 : ℂ) ^ n * Q.eval 4‖ := by
    have h := congr_arg (fun p => ‖(1 / 4 : ℂ) ^ n * p.eval 4‖) hQ_prod
    rw [eval_multiset_prod, norm_mul, norm_pow, show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num,
      norm_multiset_prod_eq, Multiset.map_map, Multiset.map_map] at h
    rw [← h, ← hQ_card]
    have hmul : (1 / 4 : ℝ) ^ Q.roots.card * (Q.roots.map (fun ζ => ‖(4 : ℂ) - ζ‖)).prod =
        (Q.roots.map (fun ζ => (1 / 4 : ℝ) * ‖(4 : ℂ) - ζ‖)).prod := by
      clear h hQ_prod hQ_card
      induction Q.roots using Multiset.induction_on with
      | empty => simp
      | cons a s ih =>
        rw [Multiset.card_cons, pow_succ', Multiset.map_cons, Multiset.prod_cons,
          Multiset.map_cons, Multiset.prod_cons]
        linear_combination (1 / 4 : ℝ) * ‖(4 : ℂ) - a‖ * ih
    have hstep : (Q.roots.map (((fun z => ‖z‖) ∘ eval 4) ∘ fun ζ => X - C ζ)).prod =
        (Q.roots.map (fun ζ => ‖(4 : ℂ) - ζ‖)).prod := by
      congr 1; refine Multiset.map_congr rfl (fun ζ _ => ?_); simp
    rw [hstep, hmul]
    congr 1; refine Multiset.map_congr rfl (fun ζ _ => ?_)
    have heq : (1 : ℂ) - (1 / 4 : ℂ) * ζ = (1 / 4 : ℂ) * ((4 : ℂ) - ζ) := by ring
    rw [heq, norm_mul, show ‖(1 / 4 : ℂ)‖ = (1 / 4 : ℝ) by norm_num]
  have hprod_B : (Q.roots.map (fun ζ => ‖B ζ‖)).prod =
      ‖Q.eval (1 / 4 : ℂ)‖ / ‖(1 / 4 : ℂ) ^ n * Q.eval 4‖ := by
    rw [← hprod_num, ← hprod_den]
    have hdiv : ∀ s : Multiset ℂ,
        (s.map (fun ζ => ‖B ζ‖)).prod =
          (s.map (fun ζ => ‖ζ - (1 / 4 : ℂ)‖)).prod /
            (s.map (fun ζ => ‖(1 : ℂ) - (1 / 4 : ℂ) * ζ‖)).prod := by
      intro s
      induction s using Multiset.induction_on with
      | empty => simp
      | cons a s ih =>
        rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons,
          Multiset.map_cons, Multiset.prod_cons, ih, B, norm_div, div_mul_div_comm]
    exact hdiv Q.roots
  have hRHS_le : (Q.roots.map (fun ζ => ‖B ζ‖)).prod ≤ 6 * (1 / 4 : ℝ) ^ (4 * m) := by
    rw [hprod_B]
    have h1 : ‖Q.eval (1 / 4 : ℂ)‖ / ‖(1 / 4 : ℂ) ^ n * Q.eval 4‖ ≤
        (4 * (1 / 4 : ℝ) ^ k) / (2 / 3 : ℝ) :=
      div_le_div₀ (by positivity) hQ_r_le (by norm_num) hQ_4_ge
    have h2 : (1 / 4 : ℝ) ^ k ≤ (1 / 4 : ℝ) ^ (4 * m) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hk1
    linarith
  have hB_any : ∀ ζ ∈ Q.roots, (1 / 10000 : ℝ) ≤ ‖B ζ‖ := by
    intro ζ hζ
    have hne4 : ζ ≠ 4 := by
      intro h4
      have h0 : Q.eval 4 = 0 := by rw [← h4]; exact (mem_roots hQ_monic.ne_zero).mp hζ
      rw [h0, mul_zero, norm_zero] at hQ_4_ge
      linarith
    by_cases h1 : 1 ≤ ‖ζ‖
    · exact le_trans (by norm_num) (one_le_norm_B_of_one_le_norm h1 hne4)
    · push Not at h1
      have hnear := polyPk_no_root_near hn hk1 hk2 hζ
      have hd_le : ‖(1 : ℂ) - (1 / 4 : ℂ) * ζ‖ ≤ 5 / 4 := by
        calc ‖(1 : ℂ) - (1 / 4 : ℂ) * ζ‖ ≤ ‖(1 : ℂ)‖ + ‖(1 / 4 : ℂ) * ζ‖ := norm_sub_le _ _
          _ = 1 + (1 / 4 : ℝ) * ‖ζ‖ := by rw [norm_one, norm_mul]; norm_num
          _ ≤ 5 / 4 := by linarith
      have hd_pos : 0 < ‖(1 : ℂ) - (1 / 4 : ℂ) * ζ‖ :=
        norm_pos_iff.mpr (denom_ne_zero_of_norm_lt_four (by linarith))
      rw [B, norm_div, le_div_iff₀ hd_pos]
      nlinarith
  have hB_near : ∀ ζ ∈ Q.roots, ¬ OMA.S_mse_5120935.IsFar (polyP n) ε ζ → (9 / 10 : ℝ) ≤ ‖B ζ‖ := by
    intro ζ hζ hnf
    dsimp [OMA.S_mse_5120935.IsFar] at hnf
    push Not at hnf
    obtain ⟨w, hw, hdist⟩ := hnf
    have hdist' : ‖ζ - w‖ ≤ 1 / 5000 := hdist
    have hw_loc := polyP_root_loc hn hw
    have hw_out : (95 / 100 : ℝ) < ‖w‖ := by
      rcases hw_loc with h_in | h_out
      · exfalso
        have hnear := polyPk_no_root_near hn hk1 hk2 hζ
        have htri : ‖ζ - (1 / 4 : ℂ)‖ ≤ ‖ζ - w‖ + ‖w - (1 / 4 : ℂ)‖ := by
          simpa using norm_add_le (ζ - w) (w - (1 / 4 : ℂ))
        linarith
      · exact h_out
    have hζ_norm : (9498 / 10000 : ℝ) < ‖ζ‖ := by
      have hrev := norm_sub_norm_le w ζ
      rw [norm_sub_rev] at hrev
      linarith
    have hne4 : ζ ≠ 4 := by
      intro h4
      have h0 : Q.eval 4 = 0 := by rw [← h4]; exact (mem_roots hQ_monic.ne_zero).mp hζ
      rw [h0, mul_zero, norm_zero] at hQ_4_ge
      linarith
    by_cases h1 : 1 ≤ ‖ζ‖
    · exact le_trans (by norm_num) (one_le_norm_B_of_one_le_norm h1 hne4)
    · push Not at h1
      have hmon := norm_B_ge_of_norm_lt_one h1 (by linarith)
      have hnum : (9 / 10 : ℝ) ≤ (‖ζ‖ - 1 / 4) / (1 - ‖ζ‖ / 4) := by
        rw [le_div_iff₀ (by linarith)]; linarith
      exact le_trans hnum hmon
  set farM := Q.roots.filter (OMA.S_mse_5120935.IsFar (polyP n) ε)
  set nearM := Q.roots.filter (fun ζ => ¬ OMA.S_mse_5120935.IsFar (polyP n) ε ζ)
  set F := farM.card
  have hsplit : farM + nearM = Q.roots := Multiset.filter_add_not _ Q.roots
  have hcards : F + nearM.card = n := by
    rw [← Multiset.card_add, hsplit, hQ_card]
  have hprod_split : (Q.roots.map (fun ζ => ‖B ζ‖)).prod =
      (farM.map (fun ζ => ‖B ζ‖)).prod * (nearM.map (fun ζ => ‖B ζ‖)).prod := by
    rw [← hsplit, Multiset.map_add, Multiset.prod_add]
  have hfar_prod : (1 / 10000 : ℝ) ^ F ≤ (farM.map (fun ζ => ‖B ζ‖)).prod := by
    have h := multiset_pow_card_le_prod (s := farM.map (fun ζ => ‖B ζ‖)) (b := (1 / 10000 : ℝ))
      (by norm_num) (by
        intro x hx
        rcases Multiset.mem_map.mp hx with ⟨ζ, hζ, rfl⟩
        exact hB_any ζ (Multiset.mem_of_mem_filter hζ))
    simpa [F] using h
  have hnear_prod : (9 / 10 : ℝ) ^ nearM.card ≤ (nearM.map (fun ζ => ‖B ζ‖)).prod := by
    have h := multiset_pow_card_le_prod (s := nearM.map (fun ζ => ‖B ζ‖)) (b := (9 / 10 : ℝ))
      (by norm_num) (by
        intro x hx
        rcases Multiset.mem_map.mp hx with ⟨ζ, hζ, rfl⟩
        exact hB_near ζ (Multiset.mem_of_mem_filter hζ) (Multiset.mem_filter.mp hζ).2)
    simpa using h
  have hcomb : (1 / 10000 : ℝ) ^ F * (9 / 10 : ℝ) ^ nearM.card ≤ 6 * (1 / 4 : ℝ) ^ (4 * m) := by
    rw [hprod_split] at hRHS_le
    have hprod_nonneg : 0 ≤ (farM.map (fun ζ => ‖B ζ‖)).prod :=
      le_trans (pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 10000) F) hfar_prod
    exact le_trans (mul_le_mul hfar_prod hnear_prod (pow_nonneg (by norm_num : (0 : ℝ) ≤ 9 / 10) _) hprod_nonneg) hRHS_le
  by_contra hlt
  push Not at hlt
  have hineq1 : (9 / 10 : ℝ) ^ n ≤ 6 * (1 / 4 : ℝ) ^ (4 * m) * (9000 : ℝ) ^ F := by
    have hmul := mul_le_mul_of_nonneg_right hcomb (by positivity : (0 : ℝ) ≤ (9000 : ℝ) ^ F)
    have hL : (1 / 10000 : ℝ) ^ F * (9 / 10 : ℝ) ^ nearM.card * (9000 : ℝ) ^ F = (9 / 10 : ℝ) ^ n := by
      rw [← hcards, pow_add]
      have hF : (1 / 10000 : ℝ) ^ F * (9000 : ℝ) ^ F = (9 / 10 : ℝ) ^ F := by
        rw [← mul_pow]; norm_num
      calc (1 / 10000 : ℝ) ^ F * (9 / 10 : ℝ) ^ nearM.card * (9000 : ℝ) ^ F
          = ((1 / 10000 : ℝ) ^ F * (9000 : ℝ) ^ F) * (9 / 10 : ℝ) ^ nearM.card := by ring
        _ = (9 / 10 : ℝ) ^ F * (9 / 10 : ℝ) ^ nearM.card := by rw [hF]
    linarith
  have h16m_ge : n ≤ 16 * m + 15 := by omega
  have hpow4 : (9 / 10 : ℝ) ^ (4 * n) ≤ 6 ^ 4 * (4 ^ 15 * (1 / 4 : ℝ) ^ n) * (9000 : ℝ) ^ (4 * F) := by
    have h1 := pow_le_pow_left₀ (by positivity) hineq1 4
    rw [← pow_mul, mul_comm n 4, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm F 4] at h1
    have h16 : (1 / 4 : ℝ) ^ (4 * m * 4) ≤ 4 ^ 15 * (1 / 4 : ℝ) ^ n := by
      have hle : (1 / 4 : ℝ) ^ (16 * m + 15) ≤ (1 / 4 : ℝ) ^ n :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) h16m_ge
      have heq : (1 / 4 : ℝ) ^ (4 * m * 4) = 4 ^ 15 * (1 / 4 : ℝ) ^ (16 * m + 15) := by
        rw [show 4 * m * 4 = 16 * m by ring, pow_add]
        have : (4 : ℝ) ^ 15 * (1 / 4 : ℝ) ^ 15 = 1 := by rw [← mul_pow]; norm_num
        linear_combination -((1 / 4 : ℝ) ^ (16 * m)) * this
      rw [heq]
      exact mul_le_mul_of_nonneg_left hle (by positivity)
    exact le_trans h1 (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h16 (by positivity)) (by positivity))
  have hpow4' : (26244 / 10000 : ℝ) ^ n ≤ (6 : ℝ) ^ 4 * (4 : ℝ) ^ 15 * (9000 : ℝ) ^ (4 * F) := by
    have hmul := mul_le_mul_of_nonneg_right hpow4 (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ n)
    have hL : (9 / 10 : ℝ) ^ (4 * n) * (4 : ℝ) ^ n = (26244 / 10000 : ℝ) ^ n := by
      rw [pow_mul, ← mul_pow]; norm_num
    have hR : 6 ^ 4 * (4 ^ 15 * (1 / 4 : ℝ) ^ n) * (9000 : ℝ) ^ (4 * F) * (4 : ℝ) ^ n =
        (6 : ℝ) ^ 4 * (4 : ℝ) ^ 15 * (9000 : ℝ) ^ (4 * F) := by
      have h4 : (1 / 4 : ℝ) ^ n * (4 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
      linear_combination (6 : ℝ) ^ 4 * (4 : ℝ) ^ 15 * (9000 : ℝ) ^ (4 * F) * h4
    linarith
  have hsplit_n : 40 * F + 480 ≤ n := by omega
  have hbase1 : (9000 : ℝ) ^ 4 ≤ (26244 / 10000 : ℝ) ^ 40 := by norm_num
  have hbase2 : (6 : ℝ) ^ 4 * (4 : ℝ) ^ 15 < (26244 / 10000 : ℝ) ^ 480 := by
    have h1 : (6 : ℝ) ^ 4 * (4 : ℝ) ^ 15 < (26244 / 10000 : ℝ) ^ 40 := by norm_num
    have h2 : (26244 / 10000 : ℝ) ^ 40 ≤ (26244 / 10000 : ℝ) ^ 480 :=
      pow_le_pow_right₀ (by norm_num) (by norm_num)
    exact lt_of_lt_of_le h1 h2
  have hstrict : (6 : ℝ) ^ 4 * (4 : ℝ) ^ 15 * (9000 : ℝ) ^ (4 * F) < (26244 / 10000 : ℝ) ^ n := by
    calc (6 : ℝ) ^ 4 * (4 : ℝ) ^ 15 * (9000 : ℝ) ^ (4 * F)
        = ((6 : ℝ) ^ 4 * (4 : ℝ) ^ 15) * ((9000 : ℝ) ^ 4) ^ F := by rw [pow_mul]
      _ < (26244 / 10000 : ℝ) ^ 480 * ((26244 / 10000 : ℝ) ^ 40) ^ F := by
          have hFpow : ((9000 : ℝ) ^ 4) ^ F ≤ ((26244 / 10000 : ℝ) ^ 40) ^ F :=
            pow_le_pow_left₀ (by positivity) hbase1 F
          calc ((6 : ℝ) ^ 4 * (4 : ℝ) ^ 15) * ((9000 : ℝ) ^ 4) ^ F
              ≤ ((6 : ℝ) ^ 4 * (4 : ℝ) ^ 15) * ((26244 / 10000 : ℝ) ^ 40) ^ F :=
                mul_le_mul_of_nonneg_left hFpow (by positivity)
            _ < (26244 / 10000 : ℝ) ^ 480 * ((26244 / 10000 : ℝ) ^ 40) ^ F :=
                mul_lt_mul_of_pos_right hbase2 (by positivity)
      _ = (26244 / 10000 : ℝ) ^ (40 * F + 480) := by rw [← pow_mul, ← pow_add, add_comm]
      _ ≤ (26244 / 10000 : ℝ) ^ n := pow_le_pow_right₀ (by norm_num) hsplit_n
  linarith

lemma farProportion_ge {n : ℕ} (hn : 2400 ≤ n) :
    (1 / 2000 : ℝ) ≤ OMA.S_mse_5120935.farProportion (polyP n) (1 / 5000) := by
  classical
  set P := polyP n
  set m := n / 16
  let ε : ℝ := 1 / 5000
  have hdeg : P.natDegree = n := (polyP_boundedMonic n).2.1
  have hden_le : ((OMA.S_mse_5120935.modRoots P).card : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
    have hcard : (OMA.S_mse_5120935.modRoots P).card ≤ (n + 1) * n := by
      dsimp [OMA.S_mse_5120935.modRoots]
      rw [hdeg, Multiset.card_sum]
      calc ∑ k ∈ Finset.range (n + 1), (P - C (P.coeff k) * X ^ k).roots.card
          ≤ ∑ _k ∈ Finset.range (n + 1), n := by
            refine Finset.sum_le_sum (fun k hk => ?_)
            rw [Finset.mem_range] at hk
            refine le_trans (Polynomial.card_roots' _) ?_
            have h1 : (P - C (P.coeff k) * X ^ k).natDegree ≤ max P.natDegree (C (P.coeff k) * X ^ k).natDegree :=
              natDegree_sub_le _ _
            have h2 : (C (P.coeff k) * X ^ k).natDegree ≤ k := natDegree_C_mul_X_pow_le _ _
            rw [hdeg] at h1
            exact le_trans h1 (max_le le_rfl (le_trans h2 (by omega)))
        _ = (n + 1) * n := by simp
    have hnat : ((n + 1) * n : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
      have hn' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      nlinarith
    exact le_trans (by exact_mod_cast hcard) hnat
  have hden_pos : (0 : ℝ) < ((OMA.S_mse_5120935.modRoots P).card : ℝ) := by
    have h0 : 0 < (OMA.S_mse_5120935.modRoots P).card := by
      dsimp [OMA.S_mse_5120935.modRoots]
      rw [hdeg, Multiset.card_sum]
      have h0mem : 0 ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
      have hge := Finset.single_le_sum (f := fun k => (P - C (P.coeff k) * X ^ k).roots.card)
        (fun _ _ => Nat.zero_le _) h0mem
      have hdeg0 : (C (P.coeff 0) * X ^ 0).degree < P.degree := by
        rw [Polynomial.degree_eq_natDegree (polyP_boundedMonic n).1.ne_zero, hdeg]
        exact lt_of_le_of_lt (degree_C_mul_X_pow_le 0 (P.coeff 0)) (WithBot.coe_lt_coe.mpr (by omega : 0 < n))
      have hQ0_deg : (P - C (P.coeff 0) * X ^ 0).natDegree = n := by
        have hsub : P - C (P.coeff 0) * X ^ 0 = P + -(C (P.coeff 0) * X ^ 0) := sub_eq_add_neg _ _
        rw [hsub, natDegree_add_eq_left_of_degree_lt (by simpa [degree_neg] using hdeg0), hdeg]
      have hQ0_card : (P - C (P.coeff 0) * X ^ 0).roots.card = n := by
        rw [← hQ0_deg, ← (IsAlgClosed.splits _).natDegree_eq_card_roots]
      omega
    exact_mod_cast h0
  have hnum_ge : (n : ℝ) ^ 2 / 1000 ≤
      (((OMA.S_mse_5120935.modRoots P).filter (OMA.S_mse_5120935.IsFar P ε)).card : ℝ) := by
    have hsub : Finset.Ico (4 * m) (5 * m) ⊆ Finset.range (n + 1) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      rw [Finset.mem_range]; omega
    have hcard_ge : ∑ k ∈ Finset.Ico (4 * m) (5 * m),
        ((P - C (P.coeff k) * X ^ k).roots.filter (OMA.S_mse_5120935.IsFar P ε)).card ≤
        ((OMA.S_mse_5120935.modRoots P).filter (OMA.S_mse_5120935.IsFar P ε)).card := by
      dsimp [OMA.S_mse_5120935.modRoots]
      rw [hdeg]
      have hfilt_sum : ∀ (s : Finset ℕ) (f : ℕ → Multiset ℂ),
          ((∑ k ∈ s, f k).filter (OMA.S_mse_5120935.IsFar P ε)).card =
            ∑ k ∈ s, ((f k).filter (OMA.S_mse_5120935.IsFar P ε)).card := by
        intro s f
        induction s using Finset.cons_induction with
        | empty => simp
        | cons a s ha ih =>
          rw [Finset.sum_cons, Multiset.filter_add, Multiset.card_add, ih, Finset.sum_cons]
      rw [hfilt_sum]
      exact Finset.sum_le_sum_of_subset hsub
    have h50 : m * n ≤ 50 * ((OMA.S_mse_5120935.modRoots P).filter (OMA.S_mse_5120935.IsFar P ε)).card := by
      calc m * n = ∑ _k ∈ Finset.Ico (4 * m) (5 * m), n := by
            rw [Finset.sum_const, Nat.card_Ico, show 5 * m - 4 * m = m by omega, smul_eq_mul]
        _ ≤ ∑ k ∈ Finset.Ico (4 * m) (5 * m),
              50 * ((P - C (P.coeff k) * X ^ k).roots.filter (OMA.S_mse_5120935.IsFar P ε)).card := by
            refine Finset.sum_le_sum (fun k hk => ?_)
            rw [Finset.mem_Ico] at hk
            exact polyPk_far_roots_ge hn hk.1 hk.2
        _ = 50 * ∑ k ∈ Finset.Ico (4 * m) (5 * m),
              ((P - C (P.coeff k) * X ^ k).roots.filter (OMA.S_mse_5120935.IsFar P ε)).card :=
            (Finset.mul_sum ..).symm
        _ ≤ 50 * ((OMA.S_mse_5120935.modRoots P).filter (OMA.S_mse_5120935.IsFar P ε)).card :=
            Nat.mul_le_mul_left 50 hcard_ge
    have hmn : n * n ≤ 20 * (m * n) := by
      have hm_ge : n ≤ 20 * m := by omega
      nlinarith
    have hcomb : n * n ≤ 1000 * ((OMA.S_mse_5120935.modRoots P).filter (OMA.S_mse_5120935.IsFar P ε)).card := by
      linarith
    have hcombR : (n : ℝ) ^ 2 ≤ 1000 *
        (((OMA.S_mse_5120935.modRoots P).filter (OMA.S_mse_5120935.IsFar P ε)).card : ℝ) := by
      rw [sq]; exact_mod_cast hcomb
    linarith
  dsimp [OMA.S_mse_5120935.farProportion]
  rw [le_div_iff₀ hden_pos]
  nlinarith

end

end OMA.P_mse_5120935

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_5120935.main) := by
  intro hmain
  have htend := hmain 1 (by norm_num) (1 / 5000) (by norm_num)
    OMA.P_mse_5120935.polyP OMA.P_mse_5120935.polyP_boundedMonic
  rw [Metric.tendsto_atTop] at htend
  obtain ⟨N, hN⟩ := htend (1 / 2000) (by norm_num)
  have h1 := hN (max N 2400) (le_max_left _ _)
  rw [Real.dist_eq, sub_zero] at h1
  have h2 := OMA.P_mse_5120935.farProportion_ge (le_max_right N 2400)
  have h3 : (1 / 2000 : ℝ) ≤ |OMA.S_mse_5120935.farProportion (OMA.P_mse_5120935.polyP (max N 2400)) (1 / 5000)| :=
    le_trans h2 (le_abs_self _)
  linarith
