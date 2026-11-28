import OMAReductions.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R2

/-!
Multiplying the twist index by a square rescales the coordinates by the
second and third powers of its square root. The chord and tangent slopes
scale by the first power, so this bijection preserves addition.
-/

open WeierstrassCurve EllipticCurveRank

private def shortModel (A B : ℚ) : Affine ℚ := ⟨0, 0, 0, A, B⟩

private theorem nonsingular_scale {A B C D u x y : ℚ} (hu : u ≠ 0)
    (hC : C = u ^ 4 * A) (hD : D = u ^ 6 * B) (h : (shortModel A B).Nonsingular x y) :
    (shortModel C D).Nonsingular (u ^ 2 * x) (u ^ 3 * y) := by
  rw [Affine.nonsingular_iff', Affine.equation_iff] at h ⊢
  simp only [shortModel, zero_mul, add_zero, zero_sub] at h ⊢
  rw [hC, hD]
  constructor
  · linear_combination (u ^ 6) * h.1
  · rcases h.2 with h | h
    · left
      have hne := mul_ne_zero (pow_ne_zero 4 hu) h
      convert hne using 1
      ring
    · right
      have hne := mul_ne_zero (pow_ne_zero 3 hu) h
      convert hne using 1
      ring

private def scalePoint {A B C D u : ℚ} (hu : u ≠ 0)
    (hC : C = u ^ 4 * A) (hD : D = u ^ 6 * B) :
    (shortModel A B).Point → (shortModel C D).Point
  | .zero => .zero
  | .some x y h => .some (u ^ 2 * x) (u ^ 3 * y) (nonsingular_scale hu hC hD h)

private theorem scale_x_eq {u x₁ x₂ : ℚ} (hu : u ≠ 0) :
    u ^ 2 * x₁ = u ^ 2 * x₂ ↔ x₁ = x₂ :=
  ⟨mul_left_cancel₀ (pow_ne_zero 2 hu), congrArg (fun x => u ^ 2 * x)⟩

private theorem scale_y_eq {A B C D u x₂ y₁ y₂ : ℚ} (hu : u ≠ 0) :
    u ^ 3 * y₁ = (shortModel C D).negY (u ^ 2 * x₂) (u ^ 3 * y₂) ↔
      y₁ = (shortModel A B).negY x₂ y₂ := by
  simp only [Affine.negY, shortModel, zero_mul, sub_zero, ← mul_neg]
  exact ⟨mul_left_cancel₀ (pow_ne_zero 3 hu), congrArg (fun y => u ^ 3 * y)⟩

private theorem scale_ratio (u s t : ℚ) (k : ℕ) (hu : u ≠ 0) :
    (u ^ (k + 1) * s) / (u ^ k * t) = u * (s / t) := by
  rw [pow_succ, mul_assoc, mul_div_mul_left _ _ (pow_ne_zero k hu), mul_div_assoc]

private theorem scale_slope {A B C D u x₁ x₂ y₁ y₂ : ℚ} (hu : u ≠ 0)
    (hC : C = u ^ 4 * A) :
    (shortModel C D).slope (u ^ 2 * x₁) (u ^ 2 * x₂) (u ^ 3 * y₁) (u ^ 3 * y₂) =
      u * (shortModel A B).slope x₁ x₂ y₁ y₂ := by
  simp only [Affine.slope, scale_x_eq hu, scale_y_eq (A := A) (B := B) hu]
  split_ifs
  · ring
  · simp only [shortModel, Affine.negY, mul_zero, zero_mul, add_zero, sub_zero, hC]
    have hn : 3 * (u ^ 2 * x₁) ^ 2 + u ^ 4 * A = u ^ 4 * (3 * x₁ ^ 2 + A) := by ring
    have hd : u ^ 3 * y₁ - -(u ^ 3 * y₁) = u ^ 3 * (y₁ - -y₁) := by ring
    rw [hn, hd]
    exact scale_ratio u _ _ 3 hu
  · rw [← mul_sub, ← mul_sub]
    exact scale_ratio u _ _ 2 hu

private theorem scale_add {A B C D u : ℚ} (hu : u ≠ 0)
    (hC : C = u ^ 4 * A) (hD : D = u ^ 6 * B)
    (P Q : (shortModel A B).Point) :
    scalePoint hu hC hD (P + Q) = scalePoint hu hC hD P + scalePoint hu hC hD Q := by
  cases P with
  | zero => rfl
  | some x₁ y₁ h₁ =>
    cases Q with
    | zero => rfl
    | some x₂ y₂ h₂ =>
      have hex :
          (u ^ 2 * x₁ = u ^ 2 * x₂ ∧
            u ^ 3 * y₁ = (shortModel C D).negY (u ^ 2 * x₂) (u ^ 3 * y₂)) ↔
          (x₁ = x₂ ∧ y₁ = (shortModel A B).negY x₂ y₂) :=
        and_congr (scale_x_eq hu) (scale_y_eq hu)
      by_cases hv : x₁ = x₂ ∧ y₁ = (shortModel A B).negY x₂ y₂
      · obtain ⟨hx, hy⟩ := hex.mpr hv
        simp only [Affine.Point.add_of_Y_eq hv.1 hv.2, scalePoint,
          Affine.Point.add_of_Y_eq hx hy]
        rfl
      · have hv' := fun h => hv (hex.mp h)
        simp only [Affine.Point.add_some hv, scalePoint, Affine.Point.add_some hv',
          Affine.Point.some.injEq]
        constructor <;> simp only [Affine.addX, Affine.addY, Affine.negAddY, Affine.negY] <;>
          rw [scale_slope (B := B) (D := D) hu hC] <;>
          simp only [shortModel, zero_mul, add_zero, sub_zero] <;> ring

private def scaleEquiv {A B C D u : ℚ} (hu : u ≠ 0)
    (hC : C = u ^ 4 * A) (hD : D = u ^ 6 * B) :
    (shortModel A B).Point ≃+ (shortModel C D).Point := by
  have hA : A = u⁻¹ ^ 4 * C := by rw [hC]; field_simp [hu]
  have hB : B = u⁻¹ ^ 6 * D := by rw [hD]; field_simp [hu]
  exact
    { toFun := scalePoint hu hC hD
      invFun := scalePoint (inv_ne_zero hu) hA hB
      left_inv := by
        intro P
        cases P with
        | zero => rfl
        | some x y h =>
          simp only [scalePoint, Affine.Point.some.injEq]
          constructor <;> field_simp [hu]
      right_inv := by
        intro P
        cases P with
        | zero => rfl
        | some x y h =>
          simp only [scalePoint, Affine.Point.some.injEq]
          constructor <;> field_simp [hu]
      map_add' := scale_add hu hC hD }

theorem OMA.solution :
    OMA.R_EllipticCurveRank_RatEllipticCurve_goldfeld_conjecture_variants_two_le_R2.H2 := by
  intro E a b _ hb
  have hu : (b : ℚ) ≠ 0 := by exact_mod_cast hb.ne'
  unfold RatEllipticCurve.twistRank RatEllipticCurve.quadraticTwist
  exact (scaleEquiv (u := (b : ℚ)) hu (by push_cast; ring)
    (by push_cast; ring)).toIntLinearEquiv.finrank_eq.symm
