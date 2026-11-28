import OMAStatements.S_oeis_a378840
import Mathlib

/-!
# A378840: the cube of the series `B = 1 + x B⁴ + x B⁵`

Put `D = 1 + X C⁴ (1 + C)`.  From `C³ = A = D³` we get `(C - D)(C² + C D + D²) = 0`; the second
factor has constant term `3`, so it is non-zero, and `ℚ⟦X⟧` is a domain, hence `C = D`, i.e.
`C = 1 + X C⁴ + X C⁵`.  So `B` and `C` satisfy the same functional equation, and

  `(B - C) (1 - X G) = 0`,  `G = B³ + B²C + BC² + C³ + B⁴ + B³C + B²C² + BC³ + C⁴`.

The factor `1 - X G` has constant term `1`, so `B = C` and `A = C³ = B³`.
-/

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a378840.main := by
  intro A C B hA hC0 hA' hB
  have hC : constantCoeff C = 1 := by simpa using hC0
  -- step 1: `C = 1 + X C⁴ (1 + C)`
  have h1 : (C - (1 + X * C ^ 4 * (1 + C))) *
      (C ^ 2 + C * (1 + X * C ^ 4 * (1 + C)) + (1 + X * C ^ 4 * (1 + C)) ^ 2) = 0 := by
    have h : C ^ 3 = (1 + X * C ^ 4 * (1 + C)) ^ 3 := hA.symm.trans hA'
    linear_combination h
  have h2 : C ^ 2 + C * (1 + X * C ^ 4 * (1 + C)) + (1 + X * C ^ 4 * (1 + C)) ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [hC] at h'
    norm_num at h'
  have hCeq : C = 1 + X * C ^ 4 * (1 + C) :=
    sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right h2)
  -- step 2: uniqueness of the solution of the functional equation
  have h3 : (B - C) * (1 - X * (B ^ 3 + B ^ 2 * C + B * C ^ 2 + C ^ 3 + B ^ 4 + B ^ 3 * C +
      B ^ 2 * C ^ 2 + B * C ^ 3 + C ^ 4)) = 0 := by
    linear_combination hB - hCeq
  have h4 : 1 - X * (B ^ 3 + B ^ 2 * C + B * C ^ 2 + C ^ 3 + B ^ 4 + B ^ 3 * C +
      B ^ 2 * C ^ 2 + B * C ^ 3 + C ^ 4) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp at h'
  have hBC : B = C := sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right h4)
  rw [hBC, hA]
