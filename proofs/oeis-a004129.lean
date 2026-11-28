import OMAStatements.S_oeis_a004129
import Mathlib.Tactic

/-! The earlier Lean disproof by @Volkopat (#24935) uses the sharp unordered-pair bound at 26.
The proposed coefficient at 39 already exceeds the number of ordered pairs. -/

namespace OMA.A004129

open Finset S_oeis_a004129 PowerSeries

private theorem ordered_bound (n : ℕ) : A004129 n ≤ n*n := by
  have hz : CoversDistinctTwoSum n 0 := ⟨range n, card_range n, fun k hk hk' => by omega⟩
  refine csSup_le ⟨0, hz⟩ fun m ⟨S, hS, hcover⟩ => ?_
  have hsub : Icc 1 m ⊆ (S ×ˢ S).image (fun p : ℕ × ℕ => p.1 + p.2) := by
    intro k hk
    obtain ⟨a, ha, b, hb, _, hab⟩ := hcover k (mem_Icc.mp hk).1 (mem_Icc.mp hk).2
    exact mem_image.mpr ⟨(a,b), mem_product.mpr ⟨ha,hb⟩, hab⟩
  simpa [card_product, hS] using (card_le_card hsub).trans card_image_le

end OMA.A004129

set_option maxRecDepth 4096 in
open OMA.S_oeis_a004129 OMA.A004129 PowerSeries in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a004129.main) := by
  intro h
  let F := PowerSeries.mk fun k => (A004129 (k+2) : ℤ)
  let x : PowerSeries ℤ := X
  let q := x^2 + x^3 - x^6
  let P := (1+q)*(1+q^2)*(1+q^4)*(1+q^8)*(1+q^16)
  let N := (x^4+x^3+2*x^2+2*x+1)*(x^2+x+1)
  have h0 : (1-q)*F = N := by
    change ((x-1)*(x^5+x^4+x^3-x-1))*F = _ at h
    rw [show 1-q = (x-1)*(x^5+x^4+x^3-x-1) by dsimp [q]; ring]
    simpa only [map_ofNat] using h
  have he : F - F*q^32 = P*N := by rw [←h0]; dsimp [P]; ring
  have high : coeff 37 (F * q ^ 32) = 0 := by
    rw [show q = (1+x-x^4)*x^2 by dsimp [q]; ring, mul_pow, ← pow_mul, ← mul_assoc]
    simp [x, coeff_mul_X_pow']
  have value : coeff 37 (P*N) = 1572 := by
    dsimp only [P, q, N, x]
    ring_nf
    simp only [← map_ofNat (C : ℤ →+* PowerSeries ℤ), map_add, map_sub,
      coeff_mul_C, coeff_X_pow, coeff_X, coeff_one]
    norm_num
  have hc := congrArg (coeff 37) he
  rw [map_sub, high, sub_zero, value] at hc
  simp only [F, coeff_mk] at hc
  have hbound := ordered_bound 39
  change (A004129 39 : ℤ) = 1572 at hc
  omega
