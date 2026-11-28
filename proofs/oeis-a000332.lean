import OMAStatements.S_oeis_a000332
import Mathlib.Tactic

open PowerSeries
/-!
Proof of OEIS A000332: telescoping the base-b digit factors gives
(1 - X) * F N = 1 - X ^ (b ^ N), so X * (F N)^5 = X * (invOneSubPow ℤ 5).val * (1 - X^(b^N))^5.
Since X^(b^N) converges to 0 coefficientwise in WithPiTopology, the product
converges to X * (invOneSubPow ℤ 5).val.
-/

open Filter
open scoped BigOperators Topology WithPiTopology

private lemma one_sub_mul_sum_pow (y : PowerSeries ℤ) (b : ℕ) :
    (1 - y) * ∑ j ∈ Finset.range b, y ^ j = 1 - y ^ b := by
  induction b with
  | zero => simp
  | succ b ih =>
    rw [Finset.sum_range_succ, mul_add, ih, pow_succ]
    ring

theorem OMA.solution : type_of% @OMA.S_oeis_a000332.main := by
  intro b hb
  let F : ℕ → PowerSeries ℤ := fun N =>
    ∏ i ∈ Finset.range N, ∑ j ∈ Finset.range b, (X : PowerSeries ℤ) ^ (j * b ^ i)
  have hF : ∀ N : ℕ, (1 - X) * F N = 1 - X ^ (b ^ N) := by
    intro N
    induction N with
    | zero =>
      dsimp [F]
      simp
    | succ N ih =>
      have hstep : F (N + 1) = F N *
          ∑ j ∈ Finset.range b, (X : PowerSeries ℤ) ^ (j * b ^ N) :=
        Finset.prod_range_succ _ N
      rw [hstep, ← mul_assoc, ih]
      have hpow : (∑ j ∈ Finset.range b, (X : PowerSeries ℤ) ^ (j * b ^ N)) =
          ∑ j ∈ Finset.range b, ((X : PowerSeries ℤ) ^ (b ^ N)) ^ j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm j (b ^ N), pow_mul]
      rw [hpow, one_sub_mul_sum_pow, ← pow_mul, ← pow_succ]
  have hunit : (invOneSubPow ℤ 5).val * (1 - X) ^ 5 = 1 := by
    rw [← invOneSubPow_inv_eq_one_sub_pow ℤ 5]
    exact (invOneSubPow ℤ 5).val_inv
  have hprod : ∀ N : ℕ,
      (X : PowerSeries ℤ) *
        ∏ i ∈ Finset.range N,
          (∑ j ∈ Finset.range b, (X : PowerSeries ℤ) ^ (j * b ^ i)) ^ 5 =
      X * (invOneSubPow ℤ 5).val *
        (1 - X ^ (b ^ N)) ^ 5 := by
    intro N
    have hpow5 : (∏ i ∈ Finset.range N,
          (∑ j ∈ Finset.range b, (X : PowerSeries ℤ) ^ (j * b ^ i)) ^ 5) =
        F N ^ 5 := by
      dsimp [F]
      rw [← Finset.prod_pow]
    rw [hpow5]
    have hF5 : (1 - X) ^ 5 * F N ^ 5 = (1 - X ^ (b ^ N)) ^ 5 := by
      rw [← mul_pow, hF N]
    calc
      X * F N ^ 5
          = X * ((invOneSubPow ℤ 5).val * (1 - X) ^ 5) *
              F N ^ 5 := by rw [hunit, mul_one]
      _ = X * (invOneSubPow ℤ 5).val *
            ((1 - X) ^ 5 * F N ^ 5) := by ring
      _ = X * (invOneSubPow ℤ 5).val *
            (1 - X ^ (b ^ N)) ^ 5 := by rw [hF5]
  simp_rw [hprod]
  have hlim0 : Tendsto (fun N : ℕ => (X : PowerSeries ℤ) ^ (b ^ N)) atTop (𝓝 0) := by
    rw [WithPiTopology.tendsto_iff_coeff_tendsto]
    intro d
    refine tendsto_atTop_of_eventually_const fun N (hdN : d + 1 ≤ N) => ?_
    have hlt : d < b ^ N := by
      have h2N : N < 2 ^ N := Nat.lt_two_pow_self
      have hpow : 2 ^ N ≤ b ^ N := Nat.pow_le_pow_left hb N
      omega
    rw [coeff_X_pow,
      show (if d = b ^ N then (1 : ℤ) else 0) = 0 by
        by_cases h : d = b ^ N
        · exfalso; omega
        · simp [h],
      map_zero]
  have hlim1 : Tendsto (fun N : ℕ =>
      X * (invOneSubPow ℤ 5).val *
        (1 - (X : PowerSeries ℤ) ^ (b ^ N)) ^ 5) atTop
      (𝓝 (X * (invOneSubPow ℤ 5).val * (1 - 0) ^ 5)) := by
    exact ((tendsto_const_nhds.sub hlim0).pow 5).const_mul _
  simpa using hlim1
