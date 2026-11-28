import OMAStatements.S_oeis_a002376
import Mathlib.Tactic

/-! Volkopat's original disproof in #24922 uses the discrepancy at 27.
Multiplication by two finite geometric sums isolates that single coefficient. -/

open OMA.S_oeis_a002376 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a002376.main) := by
  intro h
  let F := PowerSeries.mk fun k => (A002376 (k + 1) : ℤ)
  let x : PowerSeries ℤ := X
  let P := (1+x)*(1+x^2)*(1+x^4)*(1+x^8)^2*(1+x^16)^2
  change ((x+1)*(x^2+1)*(x^4+1)*(x-1)^2)*F =
    -(-1-x-x^2-x^3-x^4-x^5-x^6+C (6:ℤ)*x^7) at h
  have key : F - 2*(F*x^32) + F*x^64 =
      P * (1+x+x^2+x^3+x^4+x^5+x^6-6*x^7) := by
    simp only [map_ofNat] at h
    dsimp [P]
    linear_combination ((1+x)*(1+x^2)*(1+x^4)*(1+x^8)^2*(1+x^16)^2) * h
  have hc := congrArg (coeff 26) key
  dsimp only [P, x] at hc
  ring_nf at hc
  have numCoeff (n k : ℕ) [k.AtLeastTwo] :
      coeff n (OfNat.ofNat k : PowerSeries ℤ) = if n=0 then (OfNat.ofNat k : ℤ) else 0 := by
    calc
      _ = coeff n (C (OfNat.ofNat k : ℤ)) := congrArg _ (map_ofNat (C : ℤ →+* PowerSeries ℤ) k).symm
      _ = _ := by rw [coeff_C]
  norm_num [mul_two, map_add, map_sub, map_neg, coeff_mul_X_pow', coeff_X_pow_mul',
    coeff_X_pow, coeff_X, numCoeff, F] at hc
  have hle : A002376 27 ≤ 1 := by
    apply Nat.sInf_le
    exact ⟨fun _ => 3, fun _ => by norm_num, by norm_num⟩
  omega
