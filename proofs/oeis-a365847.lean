import OMAStatements.S_oeis_a365847
import Mathlib

/-!
# A365847: `A = B⁴` for `B = 1 + x B⁴ + x B⁵`

Cancelling `X`, the hypothesis on `A` reads `F(A) = 0` with
`F(T) = T (1 - X T)⁴ - (1 + X T)⁴`.  The series `B⁴` satisfies the same equation, because
`B (1 - X B⁴) = 1 + X B⁴` is a rearrangement of the equation for `B`.  Finally
`F(A) - F(C) = (A - C) · H` where `H` has constant term `1`; as `ℚ⟦X⟧` is a domain, `F(A) = F(C)`
forces `A = C`.
-/

namespace OMA.S_oeis_a365847

open PowerSeries

/-- The equation `T (1 - X T)⁴ = (1 + X T)⁴` has at most one solution. -/
lemma uniq (A C : PowerSeries ℚ) (hA : A * (1 - X * A) ^ 4 = (1 + X * A) ^ 4)
    (hC : C * (1 - X * C) ^ 4 = (1 + X * C) ^ 4) : A = C := by
  have h : (A - C) * (1 - 4 * X * (A + C) + 6 * X ^ 2 * (A ^ 2 + A * C + C ^ 2)
      - 4 * X ^ 3 * (A ^ 3 + A ^ 2 * C + A * C ^ 2 + C ^ 3)
      + X ^ 4 * (A ^ 4 + A ^ 3 * C + A ^ 2 * C ^ 2 + A * C ^ 3 + C ^ 4)
      - 4 * X - 6 * X ^ 2 * (A + C) - 4 * X ^ 3 * (A ^ 2 + A * C + C ^ 2)
      - X ^ 4 * (A ^ 3 + A ^ 2 * C + A * C ^ 2 + C ^ 3)) = 0 := by
    linear_combination hA - hC
  have hH : (1 - 4 * X * (A + C) + 6 * X ^ 2 * (A ^ 2 + A * C + C ^ 2)
      - 4 * X ^ 3 * (A ^ 3 + A ^ 2 * C + A * C ^ 2 + C ^ 3)
      + X ^ 4 * (A ^ 4 + A ^ 3 * C + A ^ 2 * C ^ 2 + A * C ^ 3 + C ^ 4)
      - 4 * X - 6 * X ^ 2 * (A + C) - 4 * X ^ 3 * (A ^ 2 + A * C + C ^ 2)
      - X ^ 4 * (A ^ 3 + A ^ 2 * C + A * C ^ 2 + C ^ 3) : PowerSeries ℚ) ≠ 0 := by
    intro h0
    have h' := congrArg constantCoeff h0
    simp at h'
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_right hH)

end OMA.S_oeis_a365847

open OMA.S_oeis_a365847 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a365847.main := by
  intro A B hA hB
  -- cancel the factor `X`
  have hA' : A * (1 - X * A) ^ 4 = (1 + X * A) ^ 4 :=
    mul_left_cancel₀ (X_ne_zero (R := ℚ)) (by rw [← mul_assoc]; exact hA)
  -- `B⁴` satisfies the same equation
  have hB' : B * (1 - X * B ^ 4) = 1 + X * B ^ 4 := by linear_combination hB
  have hC : B ^ 4 * (1 - X * B ^ 4) ^ 4 = (1 + X * B ^ 4) ^ 4 := by
    calc B ^ 4 * (1 - X * B ^ 4) ^ 4 = (B * (1 - X * B ^ 4)) ^ 4 := by ring
      _ = (1 + X * B ^ 4) ^ 4 := by rw [hB']
  exact uniq A (B ^ 4) hA' hC
