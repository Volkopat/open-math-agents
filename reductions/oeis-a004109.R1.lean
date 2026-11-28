import OMAStatements.S_oeis_a004109
import Mathlib

/-!
# Asymptotic enumeration of connected labeled cubic graphs

The fixed-degree regular graph formula of Bender and Canfield
(J. Combin. Theory Ser. A 24 (1978), 296–307, DOI 10.1016/0097-3165(78)90059-6)
gives the limiting ratio to the pairing count divided by the half-edge
labeling multiplicity. The limiting factor at degree 3 is `exp (-2)`.

The contribution from disconnected graphs is bounded by splitting into
two unions of components, one with at most half the vertices. The
normalized convolution is bounded using Vandermonde's identity.
Stirling's formula then gives Kotesovec's expression in A004109.
-/

namespace OMA.A004109

open Filter Asymptotics Finset Finset.Nat
open scoped Topology BigOperators

private theorem stirling_ratio_identity (n : ℕ) (hn : 0 < n) :
    (Real.sqrt (2 * ((6*n : ℕ) : ℝ) * Real.pi) *
        (((6*n : ℕ) : ℝ) / Real.exp 1)^(6*n)) /
      (Real.sqrt (2 * ((3*n : ℕ) : ℝ) * Real.pi) *
        (((3*n : ℕ) : ℝ) / Real.exp 1)^(3*n) * (2 : ℝ)^(3*n) * 6^(2*n)) =
    Real.sqrt 2 * (2 : ℝ)^n * 3^n * ((n : ℝ) / Real.exp 1)^(3*n) := by
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  let v := (n : ℝ) / Real.exp 1
  let A := Real.sqrt (2 * (3 * (n : ℝ)) * Real.pi)
  have hv : 0 < v := by dsimp [v]; positivity
  have ha : 0 < A := by dsimp [A]; positivity
  have hroot : Real.sqrt (2 * (6 * (n : ℝ)) * Real.pi) = Real.sqrt 2 * A := by
    unfold A
    rw [← Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    ring
  have h3 : 3 * (n : ℝ) / Real.exp 1 = 3 * v := by simp [v, mul_div_assoc]
  have h6 : 6 * (n : ℝ) / Real.exp 1 = 2 * (3 * v) := by simp [v]; ring
  rw [hroot, h3, h6]
  change Real.sqrt 2 * A * (2 * (3 * v))^(6*n) /
      (A * (3 * v)^(3*n) * (2 : ℝ)^(3*n) * 6^(2*n)) = _
  apply (div_eq_iff (by positivity)).mpr
  have h2p : (2 : ℝ)^(6*n) = 2^n * (2^(3*n) * 2^(2*n)) := by
    rw [← pow_add, ← pow_add, show 6*n = n+(3*n+2*n) by omega]
  have h3p : (3 : ℝ)^(3*n) = 3^n * 3^(2*n) := by
    rw [← pow_add, show 3*n = n+2*n by omega]
  have h6p : (6 : ℝ)^(2*n) = (2 : ℝ)^(2*n) * (3 : ℝ)^(2*n) := by
    rw [← mul_pow]
    norm_num
  have hpow : (3*v)^(6*n) = (3*v)^(3*n) * ((3 : ℝ)^(3*n) * v^(3*n)) := by
    rw [← mul_pow, ← pow_add, show 3*n+3*n=6*n by omega]
  rw [mul_pow, h2p, hpow, h3p, h6p]
  change _ = Real.sqrt 2 * 2^n * 3^n * v^(3*n) * _
  ring

section PairingScale

variable (pairingScale : ℕ → ℝ)
variable (hScale : ∀ n, pairingScale n =
  (6*n).factorial / ((3*n).factorial * (2 : ℝ)^(3*n) * 6^(2*n)))

include hScale in
theorem pairingScale_isEquivalent :
    pairingScale ~[atTop]
      (fun n : ℕ => Real.sqrt 2 * (2 : ℝ)^n * 3^n *
        ((n : ℝ) / Real.exp 1)^(3*n)) := by
  rw [funext hScale]
  have h6 := Stirling.factorial_isEquivalent_stirling.comp_tendsto
    (tendsto_atTop_mono (fun n : ℕ => show n ≤ 6*n by omega) tendsto_id)
  have h3 := Stirling.factorial_isEquivalent_stirling.comp_tendsto
    (tendsto_atTop_mono (fun n : ℕ => show n ≤ 3*n by omega) tendsto_id)
  have h2pow : (fun n : ℕ => (2 : ℝ)^(3*n)) ~[atTop]
      (fun n : ℕ => (2 : ℝ)^(3*n)) := IsEquivalent.refl
  have h6pow : (fun n : ℕ => (6 : ℝ)^(2*n)) ~[atTop]
      (fun n : ℕ => (6 : ℝ)^(2*n)) := IsEquivalent.refl
  have h := h6.div ((h3.mul h2pow).mul h6pow)
  refine h.trans_eventuallyEq ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  exact stirling_ratio_identity n hn

include hScale in
theorem scaled_pairingScale_isEquivalent :
    (fun n : ℕ => Real.exp (-2) * pairingScale n) ~[atTop]
      (fun n : ℕ => (2 : ℝ)^((n : ℝ) + 1/2) * 3^n * (n : ℝ)^(3*n) /
        Real.exp (3*(n : ℝ)+2)) := by
  have hconst : (fun _ : ℕ => Real.exp (-2)) ~[atTop]
      (fun _ : ℕ => Real.exp (-2)) := IsEquivalent.refl
  refine (hconst.mul (pairingScale_isEquivalent pairingScale hScale)).trans_eventuallyEq ?_
  filter_upwards [] with n
  simp only [Pi.mul_apply, div_pow]
  have he : (Real.exp 1)^(3*n) = Real.exp (3*(n : ℝ)) := by
    rw [← Real.exp_nat_mul]
    push_cast
    ring_nf
  have h2 : (2 : ℝ)^((n : ℝ) + 1/2) = 2^n * Real.sqrt 2 := by
    rw [Real.rpow_add (by norm_num), Real.rpow_natCast, Real.sqrt_eq_rpow]
  rw [he, h2, Real.exp_add, Real.exp_neg]
  ring

include hScale in
private theorem pairingScale_pos (n : ℕ) : 0 < pairingScale n := by
  rw [hScale]
  positivity

private theorem choose_mul_choose_le (a b i j : ℕ) :
    a.choose i * b.choose j ≤ (a+b).choose (i+j) := by
  rw [Nat.add_choose_eq]
  exact Finset.single_le_sum (f := fun p : ℕ × ℕ => a.choose p.1 * b.choose p.2)
    (fun _ _ => Nat.zero_le _)
    (mem_antidiagonal.mpr rfl : (i,j) ∈ antidiagonal (i+j))

private theorem choose_three_mul_le (n i : ℕ) :
    (2*n).choose (2*i) * (3*n).choose (3*i) * n.choose i ≤ (6*n).choose (6*i) := by
  calc
    _ ≤ (2*n+3*n).choose (2*i+3*i) * n.choose i :=
      Nat.mul_le_mul_right _ (choose_mul_choose_le (2*n) (3*n) (2*i) (3*i))
    _ ≤ (2*n+3*n+n).choose (2*i+3*i+i) := choose_mul_choose_le _ _ _ _
    _ = _ := by
      rw [show 2*n+3*n+n=6*n by omega, show 2*i+3*i+i=6*i by omega]

include hScale in
private theorem pairingScale_choose_ratio (n i : ℕ) (hi : i ≤ n) :
    pairingScale i * pairingScale (n-i) / pairingScale n =
      ((3*n).choose (3*i) : ℝ) / (6*n).choose (6*i) := by
  have hs (c : ℕ) : c*n - c*i = c*(n-i) := (Nat.mul_sub_left_distrib c n i).symm
  have hm (c : ℕ) : c*i ≤ c*n := Nat.mul_le_mul_left c hi
  have hp (a : ℝ) (c : ℕ) : a^(c*n) = a^(c*i) * a^(c*(n-i)) := by
    rw [← pow_add, ← Nat.mul_add, Nat.add_sub_of_le hi]
  rw [Nat.cast_choose ℝ (hm 3), Nat.cast_choose ℝ (hm 6), hs 3, hs 6]
  simp only [hScale]
  rw [hp 2 3, hp 6 2]
  have hfac (k : ℕ) : ((k.factorial : ℕ) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp [hfac]

include hScale in
private theorem pairingScale_term_le (n i : ℕ) (hi : i ≤ n) :
    ((2*n).choose (2*i) : ℝ) * pairingScale i * pairingScale (n-i) / pairingScale n ≤
      (1 : ℝ) / n.choose i := by
  have h6 : (0 : ℝ) < (6*n).choose (6*i) :=
    Nat.cast_pos.mpr (Nat.choose_pos (Nat.mul_le_mul_left 6 hi))
  have hni : (0:ℝ) < n.choose i := Nat.cast_pos.mpr (Nat.choose_pos hi)
  rw [mul_assoc, mul_div_assoc, pairingScale_choose_ratio pairingScale hScale n i hi, ← mul_div_assoc]
  rw [div_le_div_iff₀ h6 hni, one_mul]
  exact_mod_cast choose_three_mul_le n i

private theorem choose_two_le_of_mem {n i : ℕ} (hi : 2 ≤ i) (hin : i ≤ n/2) :
    n.choose 2 ≤ n.choose i := by
  induction i, hi using Nat.le_induction with
  | base => exact le_rfl
  | succ i hi ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem sum_inverse_choose_le (n : ℕ) (hn : 2 ≤ n) :
    (∑ i ∈ Icc 1 (n/2), (1 : ℝ) / n.choose i) ≤ 5 / (n : ℝ) := by
  have hn₀ : (0 : ℝ) < n := by exact_mod_cast (show 0<n by omega)
  have hn₂ : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hbound (i : ℕ) (hi : i ∈ Icc 1 (n/2)) :
      (1 : ℝ) / n.choose i ≤ (if i = 1 then 1/(n:ℝ) else 0) + 4/(n:ℝ)^2 := by
    split_ifs with h
    · subst i
      rw [Nat.choose_one_right]
      exact le_add_of_nonneg_right (by positivity)
    · have h₂ := choose_two_le_of_mem (by have := (mem_Icc.mp hi).1; omega) (mem_Icc.mp hi).2
      have h₂' : (n.choose 2 : ℝ) ≤ n.choose i := by exact_mod_cast h₂
      rw [Nat.cast_choose_two] at h₂'
      simp only [zero_add]
      have hnle : (n : ℝ)^2 / 4 ≤ n.choose i := by
        nlinarith only [h₂', mul_nonneg hn₀.le (show 0 ≤ (n:ℝ)-2 by linarith)]
      simpa only [one_div_div, one_mul] using
        (one_div_le_one_div_of_le (show 0 < (n:ℝ)^2/4 by positivity) hnle)
  calc
    _ ≤ ∑ i ∈ Icc 1 (n/2), ((if i = 1 then 1/(n:ℝ) else 0) + 4/(n:ℝ)^2) :=
      sum_le_sum hbound
    _ = 1/(n:ℝ) + (n/2 : ℕ) * (4/(n:ℝ)^2) := by
      have h1 : 1 ∈ Icc 1 (n/2) := mem_Icc.mpr ⟨le_rfl, by omega⟩
      simp [Finset.sum_add_distrib, Nat.card_Icc, h1, nsmul_eq_mul]
    _ ≤ _ := by
      have hle : ((n/2 : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.div_le_self n 2)
      calc
        _ ≤ 1/(n:ℝ) + (n:ℝ) * (4/(n:ℝ)^2) := by gcongr
        _ = _ := by field_simp; ring

include hScale in
/-- The disconnected-component convolution is negligible at the cubic pairing
scale. Only a global constant upper bound on total counts is needed. -/
theorem component_error_tendsto_zero
    (g a : ℕ → ℕ) (hle : ∀ n, a n ≤ g n) (C : ℝ) (hC : 0 ≤ C)
    (hg : ∀ n, (g n : ℝ) ≤ C * pairingScale n)
    (hconv : ∀ n, 0 < n → g n - a n ≤
      ∑ i ∈ Icc 1 (n/2), (2*n).choose (2*i) * g i * g (n-i)) :
    Tendsto (fun n : ℕ => ((g n : ℝ) - (a n : ℝ))/pairingScale n) atTop (𝓝 0) := by
  have hbound (n : ℕ) (hn : 2 ≤ n) :
      ((g n : ℝ) - (a n : ℝ))/pairingScale n ≤ C^2 * (5/(n:ℝ)) := by
    have hcast : (g n : ℝ) - (a n : ℝ) ≤
        ∑ i ∈ Icc 1 (n/2), ((2*n).choose (2*i) : ℝ) * (g i : ℝ) * g (n-i) := by
      have h := hconv n (by omega)
      rw [← Nat.cast_sub (hle n)]
      exact_mod_cast h
    calc
      _ ≤ (∑ i ∈ Icc 1 (n/2), ((2*n).choose (2*i) : ℝ) * (g i : ℝ) * g (n-i)) /
          pairingScale n := div_le_div_of_nonneg_right hcast (pairingScale_pos pairingScale hScale n).le
      _ ≤ ∑ i ∈ Icc 1 (n/2), C^2 * ((1:ℝ)/n.choose i) := by
        rw [sum_div]
        apply sum_le_sum
        intro i hi
        have hin : i ≤ n := by have := (mem_Icc.mp hi).2; omega
        have hupper := mul_le_mul (hg i) (hg (n-i)) (by positivity)
          (mul_nonneg hC (pairingScale_pos pairingScale hScale i).le)
        have hbin : 0 ≤ ((2*n).choose (2*i) : ℝ) := Nat.cast_nonneg _
        calc
          _ ≤ ((2*n).choose (2*i) : ℝ) *
                ((C * pairingScale i) * (C * pairingScale (n-i))) / pairingScale n := by
            rw [mul_assoc]
            exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hupper hbin)
              (pairingScale_pos pairingScale hScale n).le
          _ = C^2 * (((2*n).choose (2*i) : ℝ) * pairingScale i *
                pairingScale (n-i) / pairingScale n) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (pairingScale_term_le pairingScale hScale n i hin) (sq_nonneg C)
      _ ≤ _ := by
        rw [← mul_sum]
        exact mul_le_mul_of_nonneg_left (sum_inverse_choose_le n hn) (sq_nonneg C)
  have ht : Tendsto (fun n : ℕ => C^2 * (5/(n:ℝ))) atTop (𝓝 0) := by
    convert ((tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop).const_mul (C^2*5)) using 1
    · funext n
      simp only [Function.comp_apply, div_eq_mul_inv, mul_assoc]
    · simp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht ?_ ?_
  · exact Eventually.of_forall fun n => div_nonneg
      (sub_nonneg.mpr (by exact_mod_cast hle n)) (pairingScale_pos pairingScale hScale n).le
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact hbound n hn

include hScale in
/-- A count with the cubic pairing asymptotic retains it after removing
disconnected graphs under the component convolution bound. -/
theorem connected_isEquivalent_of_component_sum
    (g a : ℕ → ℕ) (hle : ∀ n, a n ≤ g n)
    (hg : Tendsto (fun n : ℕ => (g n : ℝ)/pairingScale n) atTop (𝓝 (Real.exp (-2))))
    (hconv : ∀ n, 0 < n → g n - a n ≤
      ∑ i ∈ Icc 1 (n/2), (2*n).choose (2*i) * g i * g (n-i)) :
    (fun n : ℕ => (a n : ℝ)) ~[atTop]
      fun n : ℕ => Real.exp (-2) * pairingScale n := by
  obtain ⟨C, hC⟩ := (Metric.isBounded_iff_subset_ball (0:ℝ)).mp
    (Metric.isBounded_range_of_tendsto (fun n : ℕ => (g n : ℝ)/pairingScale n) hg)
  let K : ℝ := max C 0
  have hK : 0 ≤ K := le_max_right _ _
  have hgK (n : ℕ) : (g n : ℝ) ≤ K * pairingScale n := by
    apply (div_le_iff₀ (pairingScale_pos pairingScale hScale n)).mp
    have hc : |(g n : ℝ)/pairingScale n| < C := by
      simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hC ⟨n, rfl⟩
    exact (le_abs_self _).trans (hc.le.trans (le_max_left _ _))
  have hzero := component_error_tendsto_zero pairingScale hScale g a hle K hK hgK hconv
  have ha : Tendsto (fun n : ℕ => (a n : ℝ)/pairingScale n) atTop (𝓝 (Real.exp (-2))) := by
    convert hg.sub hzero using 1
    · funext n
      rw [sub_div]
      ring
    · simp
  have he : Real.exp (-2) ≠ 0 := Real.exp_ne_zero _
  apply isEquivalent_of_tendsto_one
  convert ha.div_const (Real.exp (-2)) using 1
  · funext n
    simp only [Pi.div_apply, div_div, mul_comm]
  · rw [div_self he]

end PairingScale

end OMA.A004109

namespace OMA.R_oeis_a004109_R1

open Filter Asymptotics Finset
open scoped Topology BigOperators
open OMA.A004109

/-- Bender–Canfield enumeration at constant degree three on (2n) labels. -/
def H1 : Prop :=
  open Classical in
  let g (n : ℕ) := (univ.filter fun G : SimpleGraph (Fin (2*n)) =>
    ∀ v, (G.neighborFinset v).card = 3).card
  Tendsto (fun n : ℕ => (g n : ℝ) /
    ((6*n).factorial / ((3*n).factorial * (2 : ℝ)^(3*n) * 6^(2*n)))) atTop (𝓝 (Real.exp (-2)))

/-- A disconnected cubic graph admits a nonempty closed even vertex
subset of at most half the vertices. Counting the two induced cubic
graphs gives the finite convolution bound. -/
def H2 : Prop :=
  open Classical in
  let g (n : ℕ) := (univ.filter fun G : SimpleGraph (Fin (2*n)) =>
    ∀ v, (G.neighborFinset v).card = 3).card
  (∀ n, S_oeis_a004109.a n ≤ g n) ∧
    ∀ n, 0 < n → g n - S_oeis_a004109.a n ≤
      ∑ i ∈ Icc 1 (n/2), (2*n).choose (2*i) * g i * g (n-i)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a004109.main := by
  intro h1 h2
  obtain ⟨hle, hcomp⟩ := h2
  let M (n : ℕ) : ℝ := (6*n).factorial / ((3*n).factorial * (2 : ℝ)^(3*n) * 6^(2*n))
  have hM (n : ℕ) : M n = (6*n).factorial / ((3*n).factorial * (2 : ℝ)^(3*n) * 6^(2*n)) := rfl
  exact (connected_isEquivalent_of_component_sum M hM _ _ hle h1 hcomp).trans
    (scaled_pairingScale_isEquivalent M hM)

end OMA.R_oeis_a004109_R1
