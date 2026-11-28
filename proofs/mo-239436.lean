import OMAStatements.S_mo_239436
import Mathlib

/-! Cubic Wronskians satisfy a coefficient inequality that excludes X + X³.
The coefficient and derivative APIs compute it without an auxiliary quartic expansion. -/
open Polynomial OMA.S_mo_239436

set_option maxHeartbeats 2000000 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_239436.main) := by
  intro h
  obtain ⟨⟨a, b⟩, hab⟩ := h 3 (by decide) (fun i => if i.val = 1 ∨ i.val = 3 then 1 else 0)
  let w := wronskianMap 3 (a, b)
  have hn : 0 ≤ w 2 ^ 2 - 3 * w 1 * w 3 + 12 * w 0 * w 4 := by
    norm_num [w, wronskianMap, polynomialOfCoeffs, coeff_mul, coeff_derivative,
      coeff_monomial, Fin.succ, Fin.sum_univ_succ,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ]
    nlinarith only [sq_nonneg (3 * (a 0 * b ⟨3, by decide⟩ - a ⟨3, by decide⟩ * b 0) - (a 1 * b ⟨2, by decide⟩ - a ⟨2, by decide⟩ * b 1))]
  norm_num [w, hab] at hn
