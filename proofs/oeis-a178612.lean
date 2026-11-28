import OMAStatements.S_oeis_a178612

/-!
# No squares in OEIS A178612

An integer square in the given form produces an affine rational point on
the minimal 35.a2 model. The degree-three isogeny sends it to the model
(y^2+y=x^3+x^2+9x+1). The three-isogeny descent below establishes finiteness
of the latter rational point group. An explicit doubling height estimate
then gives a finite computation, certified in Lean, showing that its only
affine abscissa is 1. Pulling back that abscissa gives a cubic with no
rational root.

The 35.a3 descent reuses the Apache-2.0 MazurTheorem development at revision
9327963d4ec14fba49c7b14b004fd00707ffc2e9:
https://github.com/Vilin97/MazurTheorem/tree/9327963d4ec14fba49c7b14b004fd00707ffc2e9
The original authors and file paths are indicated in the source. The local
adaptation removes the good-reduction torsion dependency, replaces the
rank-zero kernel identity by a lower bound from the visible order-three
point, and supplies the doubling height estimate and the application
to the OEIS statement. The upstream license is reproduced at the end.
-/





open Polynomial

private theorem noRationalCubicRootModThree (A B Cc : ℤ)
    (hmod : ∀ v : ZMod 3, v^3 + (A : ZMod 3)*v^2 + (B : ZMod 3)*v + (Cc : ZMod 3) ≠ 0)
    {t : ℚ} (h : t^3 + (A : ℚ)*t^2 + (B : ℚ)*t + (Cc : ℚ) = 0) : False := by
  let P : ℤ[X] := X^3 + (C A * X^2 + C B * X + C Cc)
  have hm : P.Monic := by
    apply monic_X_pow_add
    compute_degree!
  have hv : aeval t P = 0 := by
    simp only [P, map_add, map_mul, map_pow, aeval_X, aeval_C]
    change t^3 + ((A : ℚ)*t^2 + (B : ℚ)*t + (Cc : ℚ)) = 0
    linear_combination h
  obtain ⟨z, hz, _⟩ := exists_integer_of_is_root_of_monic hm hv
  change t = (z : ℚ) at hz
  rw [hz] at h
  have hz' : z^3 + A*z^2 + B*z + Cc = 0 := by exact_mod_cast h
  have hzmod := congrArg (fun z : ℤ => (z : ZMod 3)) hz'
  push_cast at hzmod
  exact hmod _ hzmod

private theorem normalized35_completedOrdinate_ne_zero {x y : ℚ}
    (h : y^2 + 4*x*y + 7*y = x^3 - 140*x - 791) : 2*y+4*x+7 ≠ 0 := by
  intro h0
  have hy : y = -2*x - 7/2 := by linarith
  rw [hy] at h
  have heq : (4*x)^3 + 16*(4*x)^2 - 2016*(4*x) - 49840 = 0 := by
    linear_combination -64*h
  exact noRationalCubicRootModThree 16 (-2016) (-49840) (by decide) (t := 4*x) (by push_cast; linarith only [heq])

private theorem optimal35_completedOrdinate_ne_zero {x y : ℚ}
    (h : y^2+y = x^3+x^2+9*x+1) : 2*y+1 ≠ 0 := by
  intro h0
  have hy : y = -1/2 := by linarith
  rw [hy] at h
  have heq : (4*x)^3 + 4*(4*x)^2 + 144*(4*x) + 80 = 0 := by
    linear_combination -64*h
  exact noRationalCubicRootModThree 4 144 80 (by decide) (t := 4*x) heq

private theorem source35_completedOrdinate_ne_zero {x y : ℚ}
    (h : y^2+4*x*y+7*y = x^3) : 2*y+4*x+7 ≠ 0 := by
  intro h0
  have hy : y = -2*x - 7/2 := by linarith
  rw [hy] at h
  have heq : (4*x)^3 + 16*(4*x)^2 + 224*(4*x) + 784 = 0 := by
    linear_combination -64*h
  exact noRationalCubicRootModThree 16 224 784 (by decide) (t := 4*x) heq


/- Source: MazurTorsion/Foundations/NaiveHeightDescent.lean -/

section

/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Vasily Ilin
-/


/-!
# Naïve-height descent for rational elliptic curves

This file is a narrow port of the height part of Michael Stoll's
`EllipticCurves/MordellWeil.lean`, commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

It proves the approximate parallelogram law for the naïve logarithmic
height on affine Weierstrass points. Combined with Northcott and finite
index of multiplication by two or three, this gives finite generation by
the descent theorems in `Mathlib.GroupTheory.Descent`.

The much larger weak Mordell--Weil and Selmer-group layers are deliberately
not imported: callers may establish the required finite index by a
curve-specific descent.
-/

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R]
  {W' : WeierstrassCurve R}

open MvPolynomial Nat

lemma den_duplication_eq {x y : R} (h : W'.toAffine.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ =
      (2 * y + W'.a₁ * x + W'.a₃) ^ 2 := by
  have heq := (W'.toAffine.equation_iff x y).mp h
  simp only [b₂, b₄, b₆]
  linear_combination -4 * heq

lemma den_duplication_eq_zero_iff [IsReduced R] {x y : R}
    (h : W'.toAffine.Equation x y) :
    4 * x ^ 3 + W'.b₂ * x ^ 2 + 2 * W'.b₄ * x + W'.b₆ = 0 ↔
      y = W'.toAffine.negY x y := by
  rw [den_duplication_eq h, sq_eq_zero_iff,
    WeierstrassCurve.Affine.negY]
  grind only

variable {F : Type*} [Field F]
  {W : WeierstrassCurve F}

lemma den_duplication_ne_zero_or_num_duplication_ne_zero
    {x y : F} (h : W.toAffine.Nonsingular x y) :
    4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ ≠ 0 ∨
      x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈ ≠ 0 := by
  have ⟨h₁, h₂⟩ := (W.toAffine.nonsingular_iff x y).mp h
  rw [W.toAffine.equation_iff x y] at h₁
  by_cases hzero : 2 * y + W.a₁ * x + W.a₃ = 0
  · right
    replace h₂ : W.a₁ * y ≠ 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
      grind
    contrapose! h₂
    rw [b₄, b₆, b₈] at h₂
    grobner
  · left
    clear h₂
    contrapose! hzero
    rw [b₂, b₄, b₆] at hzero
    grobner

section Decidable

variable [DecidableEq F]

lemma addX_self_of_Y_ne {x y : F} (h : W.toAffine.Equation x y)
    (hn : y ≠ W.toAffine.negY x y) :
    W.toAffine.addX x x (W.toAffine.slope x x y y) =
      (x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
        (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆) := by
  have aux {a b c : F} (ha : a ≠ 0) :
      a ^ 2 * (b * (c / a)) = a * b * c := by
    field
  have hn' := (den_duplication_eq_zero_iff h).not.mpr hn
  refine mul_left_cancel₀ hn' ?_
  have hn'' : 2 * y + W.a₁ * x + W.a₃ ≠ 0 := by
    rw [den_duplication_eq h] at hn'
    grind
  rw [mul_div_cancel₀ _ hn', WeierstrassCurve.Affine.addX,
    sub_sub, sub_sub, mul_sub, mul_add]
  simp only [WeierstrassCurve.Affine.slope, ↓reduceIte, hn]
  rw [WeierstrassCurve.Affine.negY,
    show y - (-y - W.a₁ * x - W.a₃) = 2 * y + W.a₁ * x + W.a₃ by ring,
    div_pow]
  nth_rewrite 1 2 [den_duplication_eq h]
  rw [mul_div_cancel₀ _ <| pow_ne_zero 2 hn'', aux hn'', b₂, b₄, b₆, b₈]
  linear_combination -W.a₁ ^ 2 * (W.toAffine.equation_iff x y).mp h

lemma addX_of_X_ne {xP yP xQ yQ : F} (hn : xP ≠ xQ) :
    W.toAffine.addX xP xQ (W.toAffine.slope xP xQ yP yQ) =
      ((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) -
          (W.a₂ + xP + xQ) * (xP - xQ) ^ 2) /
        (xP - xQ) ^ 2 := by
  have hxPQ : xP - xQ ≠ 0 := by
    grind only
  simp [WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.slope, hn, div_pow]
  field

lemma Point.xRep_add_self_of_Y_ne {x y : F}
    (h : W.toAffine.Nonsingular x y)
    (hn : y ≠ W.toAffine.negY x y) :
    (some x y h + some x y h).xRep =
      ![(x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈) /
          (4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆), 1] := by
  simp only [add_self_of_Y_ne hn, ← addX_self_of_Y_ne h.1 hn, xRep_some]

lemma Point.xRep_add_self_of_Y_eq {x y : F}
    (h : W.toAffine.Nonsingular x y)
    (hn : y = W.toAffine.negY x y) :
    (some x y h + some x y h).xRep = ![1, 0] := by
  simp only [add_self_of_Y_eq hn, xRep_zero]

lemma Point.xRep_add_of_X_ne {xP yP xQ yQ : F}
    (hP : W.toAffine.Nonsingular xP yP)
    (hQ : W.toAffine.Nonsingular xQ yQ)
    (hn : xP ≠ xQ) :
    (some xP yP hP + some xQ yQ hQ).xRep =
      ![((yP - yQ) ^ 2 + W.a₁ * (yP - yQ) * (xP - xQ) -
            (W.a₂ + xP + xQ) * (xP - xQ) ^ 2) /
          (xP - xQ) ^ 2, 1] := by
  simp only [add_of_X_ne (h₁ := hP) (h₂ := hQ) hn, xRep_some,
    addX_of_X_ne hn]

lemma Point.xRep_sub_of_X_ne {xP yP xQ yQ : F}
    (hP : W.toAffine.Nonsingular xP yP)
    (hQ : W.toAffine.Nonsingular xQ yQ)
    (hn : xP ≠ xQ) :
    (some xP yP hP - some xQ yQ hQ).xRep =
      ![((yP + yQ + W.a₁ * xQ + W.a₃) ^ 2 +
            W.a₁ * (yP + yQ + W.a₁ * xQ + W.a₃) * (xP - xQ) -
            (W.a₂ + xP + xQ) * (xP - xQ) ^ 2) /
          (xP - xQ) ^ 2, 1] := by
  simp only [sub_eq_add_neg (some ..), neg_some hQ,
    add_of_X_ne (h₁ := hP) (h₂ := (nonsingular_neg ..).mpr hQ) hn,
    xRep_some, addX_of_X_ne hn]
  grind only [negY]

end Decidable

lemma finite_preimage_xRep (x : F) :
    {P : W.toAffine.Point | P.xRep = ![x, 1]}.Finite := by
  rcases Set.eq_empty_or_nonempty
      {P : W.toAffine.Point | P.xRep = ![x, 1]} with h | h
  · exact h ▸ Set.finite_empty
  choose Q hQ using h
  simp only [Set.mem_setOf_eq] at hQ
  rw [show {P | P.xRep = ![x, 1]} = {Q, -Q} by
    ext
    simp [← hQ, Point.xRep_eq_xRep_iff]]
  simp

lemma finite_preimage_xRep0 (x : F) :
    {P : W.toAffine.Point | P.xRep 0 = x}.Finite := by
  have hsubset :
      {P : W.toAffine.Point | P.xRep 0 = x} ⊆
        {P | P.xRep = ![x, 1]} ∪ {0} := by
    intro P hP
    match P with
    | 0 => simp
    | .some x' y h => simp_all [Point.xRep_some]
  exact (finite_preimage_xRep x).union (Set.finite_singleton 0) |>.subset hsubset

lemma Point.sym2x_eq (P Q : W.toAffine.Point) :
    P.sym2x Q =
      ![P.xRep 0 * Q.xRep 0,
        P.xRep 0 * Q.xRep 1 + P.xRep 1 * Q.xRep 0,
        P.xRep 1 * Q.xRep 1] :=
  rfl

private lemma Point.sym2x_P_P_eq_addSubMap (P : W.toAffine.Point) :
    Point.sym2x P P =
      fun i ↦ (addSubMap W i).eval <| P.sym2x 0 := by
  match P with
  | 0 =>
    simp only [Point.sym2x_zero_zero, succ_eq_add_one, reduceAdd,
      addSubMap, Fin.isValue]
    ext i
    fin_cases i <;> simp
  | some .. =>
    simp only [Point.sym2x_some_some, succ_eq_add_one, reduceAdd,
      Point.sym2x_some_zero, addSubMap, Fin.isValue]
    ext i
    fin_cases i <;> simp [pow_two, two_mul]

section Decidable

variable [DecidableEq F]

private lemma Point.sym2x_P_add_P_zero (P : W.toAffine.Point) :
    ∃ t : F, t ≠ 0 ∧
      t • Point.sym2x (P + P) 0 =
        fun i ↦ (addSubMap W i).eval <| P.sym2x P := by
  match P with
  | 0 =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [add_zero, Point.sym2x_zero_zero, one_smul, addSubMap]
    ext i
    fin_cases i <;> simp
  | some x y h =>
    have heq := (W.toAffine.equation_iff x y).mp h.1
    have hrs :
        (fun i ↦ (addSubMap W i).eval <|
          (some x y h).sym2x (some x y h)) =
          ![x ^ 4 - W.b₄ * x ^ 2 - 2 * W.b₆ * x - W.b₈,
            4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆, 0] := by
      ext i
      fin_cases i <;> simp [addSubMap] <;> ring
    rw [hrs]
    by_cases hvertical : y = W.toAffine.negY x y
    · have hden := (den_duplication_eq_zero_iff h.1).mpr hvertical
      rw [hden, add_self_of_Y_eq hvertical, Point.sym2x_zero_zero]
      refine ⟨_,
        den_duplication_ne_zero_or_num_duplication_ne_zero h
          |>.neg_resolve_left hden, ?_⟩
      simp
    · have hden := (den_duplication_eq_zero_iff h.1).not.mpr hvertical
      refine ⟨_, hden, ?_⟩
      simp [Point.sym2x_eq, Point.xRep_add_self_of_Y_ne h hvertical,
        mul_div_cancel₀ _ hden]

theorem Point.sym2x_add_sub_eq_addSubMap_sym2x
    (P Q : W.toAffine.Point) :
    ∃ t : F, t ≠ 0 ∧
      t • Point.sym2x (P + Q) (P - Q) =
        fun i ↦ (addSubMap W i).eval <| Point.sym2x P Q := by
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using P.sym2x_P_add_P_zero
  rcases eq_or_ne Q (-P) with rfl | hPQ'
  · simpa [Point.sym2x_neg_right, Point.sym2x_comm 0] using
      P.sym2x_P_add_P_zero
  match P, Q with
  | P, 0 =>
    exact ⟨1, one_ne_zero, by simpa using P.sym2x_P_P_eq_addSubMap⟩
  | 0, Q =>
    refine ⟨1, one_ne_zero, ?_⟩
    simpa [Point.sym2x_neg_right, Point.sym2x_comm _ Q] using
      Q.sym2x_P_P_eq_addSubMap
  | some xP yP hP, some xQ yQ hQ =>
    have hxPQ : xP ≠ xQ := fun heq ↦ by
      grind only [X_eq_iff.mp heq]
    have hrs :
        (fun i ↦ (addSubMap W i).eval <|
          (some xP yP hP).sym2x (some xQ yQ hQ)) =
          ![(xP * xQ) ^ 2 - W.b₄ * (xP * xQ) -
              W.b₆ * (xP + xQ) - W.b₈,
            2 * (xP + xQ) * (xP * xQ) +
              W.b₂ * (xP * xQ) + W.b₄ * (xP + xQ) + W.b₆,
            (xP - xQ) ^ 2] := by
      ext i
      fin_cases i <;> simp [addSubMap]
      ring
    have hsub : xP - xQ ≠ 0 := sub_ne_zero_of_ne hxPQ
    refine ⟨(xP - xQ) ^ 2, pow_ne_zero 2 hsub, ?_⟩
    have heqP := (W.toAffine.equation_iff xP yP).mp hP.1
    have heqQ := (W.toAffine.equation_iff xQ yQ).mp hQ.1
    rw [hrs, Point.sym2x_eq, Point.xRep_add_of_X_ne hP hQ hxPQ,
      Point.xRep_sub_of_X_ne hP hQ hxPQ, b₂, b₄, b₆, b₈]
    ext i
    fin_cases i <;> simp [field] <;> grobner

end Decidable

section Height

open Height

variable [AdmissibleAbsValues F]

/-- The logarithmic projective height of an affine point's `x`-coordinates. -/
noncomputable def Point.naiveHeight (P : W.toAffine.Point) : ℝ :=
  logHeight P.xRep

lemma Point.naiveHeight_eq_logHeight (P : W.toAffine.Point) :
    P.naiveHeight = logHeight P.xRep :=
  rfl

lemma Point.naiveHeight_eq_logHeight₁ {P : W.toAffine.Point} :
    P.naiveHeight = logHeight₁ (P.xRep 0) := by
  match P with
  | 0 => simp [naiveHeight, xRep]
  | some .. =>
    simpa [naiveHeight] using (logHeight₁_eq_logHeight _).symm

variable (W)

lemma abs_logHeight_sym2x_sub_le :
    ∃ C, ∀ P Q : W.toAffine.Point,
      |logHeight (P.sym2x Q) - (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C, hC⟩ := abs_logHeight_sym2_sub_le F
  refine ⟨C, fun P Q ↦ ?_⟩
  rw [P.naiveHeight_eq_logHeight, Q.naiveHeight_eq_logHeight,
    Point.sym2x_eq]
  have hmul := logHeight_fun_mul_eq P.xRep_ne_zero Q.xRep_ne_zero
  have hvec (v : Fin 2 → F) : ![v 0, v 1] = v := by
    ext i
    fin_cases i <;> simp
  have hzero (P : W.toAffine.Point) : ![P.xRep 0, P.xRep 1] ≠ 0 :=
    hvec P.xRep ▸ P.xRep_ne_zero
  specialize hC (hzero P) (hzero Q)
  rw [hvec P.xRep, hvec Q.xRep] at *
  grind only [= abs.eq_1, = max_def]

variable [W.toAffine.IsElliptic]

theorem approx_parallelogram_law [DecidableEq F] :
    ∃ C, ∀ P Q : W.toAffine.Point,
      |(P + Q).naiveHeight + (P - Q).naiveHeight -
          2 * (P.naiveHeight + Q.naiveHeight)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := abs_logHeight_sym2x_sub_le W
  obtain ⟨C₂, hC₂⟩ :=
    WeierstrassCurve.abs_logHeight_addSubMap_sub_two_mul_logHeight_le W
  refine ⟨3 * C₁ + C₂, fun P Q ↦ ?_⟩
  obtain ⟨t, ht₀, ht⟩ :=
    Point.sym2x_add_sub_eq_addSubMap_sym2x P Q
  replace ht := congrArg logHeight ht
  rw [Height.logHeight_smul_eq_logHeight _ ht₀] at ht
  have hPQ := hC₁ P Q
  have haddsub := hC₁ (P + Q) (P - Q)
  have hC := ht ▸ hC₂ (P.sym2x Q)
  generalize (P + Q).naiveHeight + (P - Q).naiveHeight = A at haddsub ⊢
  generalize logHeight ((P + Q).sym2x (P - Q)) = B at hC haddsub
  generalize logHeight (P.sym2x Q) = B' at hPQ hC
  generalize P.naiveHeight + Q.naiveHeight = A' at hPQ ⊢
  grind only [= abs.eq_1, = max_def]

instance [Northcott (logHeight₁ (K := F))] :
    Northcott (Point.naiveHeight (F := F) (W := W)) := by
  eta_expand
  simp only [Point.naiveHeight_eq_logHeight₁]
  rw [← Function.comp_def]
  letI : Filter.TendstoCofinite (fun P : W.toAffine.Point ↦ P.xRep 0) :=
    (Filter.tendstoCofinite_iff_finite_preimage_singleton _).2 fun x ↦ by
      simpa only [Set.preimage, Set.mem_singleton_iff] using
        (finite_preimage_xRep0 (W := W) x)
  exact Northcott.comp_of_finite_fibers
    (h := fun P : W.toAffine.Point ↦ P.xRep 0)
    (h' := logHeight₁)

variable [Northcott (logHeight₁ (K := F))]
variable [DecidableEq F]

theorem fg_point_of_finiteIndex_two
    (hindex :
      (nsmulAddMonoidHom (α := W.toAffine.Point) 2).range.FiniteIndex) :
    AddGroup.FG W.toAffine.Point := by
  have hnonneg (P : W.toAffine.Point) : 0 ≤ P.naiveHeight := by
    rw [Point.naiveHeight_eq_logHeight P]
    positivity
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  exact AddCommGroup.fg_of_descent' hindex hnonneg hC

/-- The approximate parallelogram law runs naïve-height descent with
multiplication by three. -/
theorem fg_point_of_finiteIndex_three
    (hindex :
      (nsmulAddMonoidHom (α := W.toAffine.Point) 3).range.FiniteIndex) :
    AddGroup.FG W.toAffine.Point := by
  let h : W.toAffine.Point → ℝ := Point.naiveHeight
  have hnonneg (P : W.toAffine.Point) : 0 ≤ h P := by
    change 0 ≤ P.naiveHeight
    rw [Point.naiveHeight_eq_logHeight P]
    positivity
  obtain ⟨C, hC⟩ := approx_parallelogram_law W
  have htranslate (G P : W.toAffine.Point) :
      h P ≤ 2 * h (G + P) + (2 * h (-G) + C) := by
    have hpar := hC (G + P) (-G)
    have hrest : 0 ≤ h ((G + P) - (-G)) := hnonneg _
    have hsum : (G + P) + (-G) = P := by abel
    rw [hsum] at hpar
    grind
  have hgrowth (P : W.toAffine.Point) :
      9 * h P - (2 * h 0 + 3 * C) ≤ h ((3 : ℕ) • P) := by
    have htwoPar := hC P P
    have htwo :
        4 * h P - (h 0 + C) ≤ h ((2 : ℕ) • P) := by
      have hsum : P + P = (2 : ℕ) • P := by abel
      have hdiff : P - P = 0 := sub_self P
      rw [hsum, hdiff] at htwoPar
      grind
    have hthreePar := hC ((2 : ℕ) • P) P
    have hsum : (2 : ℕ) • P + P = (3 : ℕ) • P := by abel
    have hdiff : (2 : ℕ) • P - P = P := by abel
    rw [hsum, hdiff] at hthreePar
    grind
  letI : Northcott h := by
    dsimp only [h]
    infer_instance
  exact
    AddCommGroup.fg_of_descent
      (n := 3) (h := h) (a := 2) (b := 9)
      (c₀ := 2 * h 0 + 3 * C)
      (c := fun G ↦ 2 * h (-G) + C)
      (by norm_num) (by norm_num) hindex
      htranslate hgrowth

end Height

end WeierstrassCurve.Affine

end

/- Source: MazurTorsion/GroupTheory/IndexNSmulFG.lean -/

section

/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
# The index of multiplication on a finitely generated abelian group

This file is a narrow port of the finitely-generated-abelian-group part of
Michael Stoll's `EllipticCurves/Mathlib/SelmerGroup.lean`, commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

It extends `AddSubgroup.index_range_nsmul`, which treats a finite free
`ℤ`-module, to a finitely generated commutative group with torsion.  The
result will let a curve-specific two-descent turn a bound on
`E(ℚ) / 2 E(ℚ)` into a bound on the Mordell--Weil rank.
-/

/-- First-isomorphism counting: the cardinality of an additive group is the
cardinality of the kernel times the cardinality of the range of a homomorphism. -/
theorem AddMonoidHom.card_ker_mul_card_range {G H : Type*}
    [AddGroup G] [AddGroup H] (φ : G →+ H) :
    Nat.card φ.ker * Nat.card φ.range = Nat.card G := by
  rw [Nat.card_congr
      (QuotientAddGroup.quotientKerEquivRange φ).toEquiv.symm,
    mul_comm]
  exact
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker).symm

/-- On a finite additive group, the index of the range of an endomorphism
equals the cardinality of its kernel. -/
theorem AddMonoidHom.index_range_eq_card_ker {G : Type*}
    [AddGroup G] [Finite G] (φ : G →+ G) :
    φ.range.index = Nat.card φ.ker := by
  have h1 : φ.range.index * Nat.card φ.range = Nat.card G :=
    φ.range.index_mul_card
  exact
    Nat.eq_of_mul_eq_mul_right Nat.card_pos
      (h1.trans φ.card_ker_mul_card_range.symm)

/-- An additive equivalence maps the kernel of multiplication by `n` onto
the corresponding kernel. -/
lemma AddEquiv.map_ker_nsmulAddMonoidHom {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) (n : ℕ) :
    ((nsmulAddMonoidHom (α := M) n).ker).map e.toAddMonoidHom =
      (nsmulAddMonoidHom (α := N) n).ker := by
  ext x
  rw [AddSubgroup.mem_map_equiv]
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
  rw [← map_nsmul, EmbeddingLike.map_eq_zero_iff]

/-- Multiplication by `n` on a product has the product of the two ranges as
its range. -/
lemma nsmulAddMonoidHom_range_prod (A B : Type*)
    [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    (nsmulAddMonoidHom (α := A × B) n).range =
      ((nsmulAddMonoidHom (α := A) n).range).prod
        (nsmulAddMonoidHom (α := B) n).range := by
  ext x
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply,
    AddSubgroup.mem_prod]
  exact
    ⟨fun ⟨y, hy⟩ ↦
        ⟨⟨y.1, congrArg Prod.fst hy⟩, ⟨y.2, congrArg Prod.snd hy⟩⟩,
      fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ⟨(a, b), Prod.ext ha hb⟩⟩

/-- Multiplication by `n` on a product has the product of the two kernels as
its kernel. -/
lemma nsmulAddMonoidHom_ker_prod (A B : Type*)
    [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    (nsmulAddMonoidHom (α := A × B) n).ker =
      ((nsmulAddMonoidHom (α := A) n).ker).prod
        (nsmulAddMonoidHom (α := B) n).ker := by
  ext x
  simp [AddMonoidHom.mem_ker, AddSubgroup.mem_prod, Prod.ext_iff]

/-- A finite module over a characteristic-zero ring has rank zero. -/
lemma Module.rank_eq_zero_of_finite (R M : Type*) [Ring R] [CharZero R]
    [AddCommGroup M] [Module R M] [Finite M] :
    Module.rank R M = 0 :=
  rank_eq_zero_iff.mpr fun x ↦
    ⟨addOrderOf x, Nat.cast_ne_zero.mpr (addOrderOf_pos x).ne',
      by
        rw [Nat.cast_smul_eq_nsmul]
        exact addOrderOf_nsmul_eq_zero x⟩

open scoped DirectSum in
open Module in
/-- The index of `nG` in a finitely generated commutative group `G` is
`n ^ rank(G)` times the cardinality of its `n`-torsion subgroup. -/
theorem AddSubgroup.index_range_nsmul_of_fg
    (G : Type*) [AddCommGroup G] [AddGroup.FG G]
    {n : ℕ} (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := G) n).range.index =
      n ^ finrank ℤ G *
        Nat.card (nsmulAddMonoidHom (α := G) n).ker := by
  obtain ⟨r, ι, fι, p, hp, e, ⟨eqv⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod G
  have hne (i : ι) : NeZero (p i ^ e i) :=
    ⟨pow_ne_zero _ (hp i).pos.ne'⟩
  have hTfin : Finite (⨁ i, ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have hidx :
      (nsmulAddMonoidHom (α := G) n).range.index =
        (nsmulAddMonoidHom
          (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).range.index := by
    simpa [AddEquiv.map_range_nsmulAddMonoidHom]
      using
        (AddSubgroup.index_map_equiv
          (nsmulAddMonoidHom (α := G) n).range eqv).symm
  have hker :
      Nat.card (nsmulAddMonoidHom (α := G) n).ker =
        Nat.card
          (nsmulAddMonoidHom
            (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).ker := by
    rw [← eqv.map_ker_nsmulAddMonoidHom n]
    exact
      Nat.card_congr
        (AddSubgroup.equivMapOfInjective _
          eqv.toAddMonoidHom eqv.injective).toEquiv
  have hrk : finrank ℤ G = r := by
    have h1 :
        Module.rank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      set π :=
        LinearMap.fst ℤ (Fin r →₀ ℤ) (⨁ i, ZMod (p i ^ e i))
        with hπ
      have h0 : Module.rank ℤ (LinearMap.ker π) = 0 := by
        have e2 :
            LinearMap.ker π ≃ₗ[ℤ] ⨁ i, ZMod (p i ^ e i) :=
          { toFun := fun x ↦ x.1.2
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl
            invFun := fun t ↦ ⟨(0, t), rfl⟩
            left_inv := fun x ↦
              Subtype.ext (Prod.ext (x.2 : x.1.1 = 0).symm rfl)
            right_inv := fun _ ↦ rfl }
        rw [e2.rank_eq]
        exact Module.rank_eq_zero_of_finite ℤ _
      rw [← π.rank_range_add_rank_ker,
        LinearMap.range_eq_top.mpr Prod.fst_surjective, rank_top,
        rank_finsupp_self', Cardinal.mk_fin, h0, add_zero]
    have h2 :
        finrank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      simp [Module.finrank, h1]
    rw [eqv.toIntLinearEquiv.finrank_eq]
    convert h2 using 2
  have hkerF : (nsmulAddMonoidHom (α := Fin r →₀ ℤ) n).ker = ⊥ :=
    (AddMonoidHom.ker_eq_bot_iff _).mpr
      (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hn)
  rw [hidx, hker, hrk, nsmulAddMonoidHom_range_prod,
    AddSubgroup.index_prod, AddSubgroup.index_range_nsmul,
    AddMonoidHom.index_range_eq_card_ker,
    nsmulAddMonoidHom_ker_prod,
    Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv,
    Nat.card_prod, hkerF]
  simp

end

/- Source: MazurTorsion/Foundations/ThreeTorsion.lean -/

section

/-
Copyright (c) 2026 Victor Aguiar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Victor Aguiar
-/


/-!
# The full rational three-torsion obstruction

This file proves that the rational points of a Weierstrass curve over `ℚ`
cannot contain a subgroup isomorphic to `ZMod 3 × ZMod 3`. The proof derives
the three-division polynomial from the tangent formulas and uses its four
hypothetical rational roots to contradict the Weierstrass coefficient
relation.
-/

namespace MazurTorsion.ThreeTorsion

open WeierstrassCurve

lemma tangent_forces_three_division
    {a₁ a₂ a₃ a₄ a₆ x y slope : ℚ}
    (hcurve :
      y ^ 2 + a₁ * x * y + a₃ * y =
        x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hslope :
      slope * (2 * y + a₁ * x + a₃) =
        3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y)
    (hx : slope ^ 2 + a₁ * slope - a₂ - 3 * x = 0) :
    3 * x ^ 4 + (a₁ ^ 2 + 4 * a₂) * x ^ 3 +
      3 * (a₁ * a₃ + 2 * a₄) * x ^ 2 +
      3 * (a₃ ^ 2 + 4 * a₆) * x +
      (a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ +
        a₂ * a₃ ^ 2 - a₄ ^ 2) = 0 := by
  linear_combination
    -(2 * y + a₁ * x + a₃) ^ 2 * hx +
    ((3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) +
      slope * (2 * y + a₁ * x + a₃) +
      a₁ * (2 * y + a₁ * x + a₃)) * hslope -
    (a₁ ^ 2 + 4 * a₂ + 12 * x) * hcurve

/-- The exact algebraic identity behind the three-division polynomial:
on the curve, the value of `Ψ₃` is the negative square of the tangent
denominator times the difference between the doubled and original
x-coordinates. -/
lemma three_division_tangent_identity
    {a₁ a₂ a₃ a₄ a₆ x y slope : ℚ}
    (hcurve :
      y ^ 2 + a₁ * x * y + a₃ * y =
        x ^ 3 + a₂ * x ^ 2 + a₄ * x + a₆)
    (hslope :
      slope * (2 * y + a₁ * x + a₃) =
        3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) :
    3 * x ^ 4 + (a₁ ^ 2 + 4 * a₂) * x ^ 3 +
        3 * (a₁ * a₃ + 2 * a₄) * x ^ 2 +
        3 * (a₃ ^ 2 + 4 * a₆) * x +
        (a₁ ^ 2 * a₆ + 4 * a₂ * a₆ - a₁ * a₃ * a₄ +
          a₂ * a₃ ^ 2 - a₄ ^ 2) =
      -(2 * y + a₁ * x + a₃) ^ 2 *
        (slope ^ 2 + a₁ * slope - a₂ - 3 * x) := by
  linear_combination
    ((3 * x ^ 2 + 2 * a₂ * x + a₄ - a₁ * y) +
      slope * (2 * y + a₁ * x + a₃) +
      a₁ * (2 * y + a₁ * x + a₃)) * hslope -
    (a₁ ^ 2 + 4 * a₂ + 12 * x) * hcurve

open scoped WeierstrassCurve.Affine

lemma nonzero_three_torsion_abscissa
    (W : WeierstrassCurve.Affine ℚ) (P : W.Point)
    (hthree : (3 : ℕ) • P = 0) (hne : P ≠ 0) :
    ∃ x y, ∃ hP : W.Nonsingular x y,
      P = .some x y hP ∧ Polynomial.eval x W.Ψ₃ = 0 := by
  cases P with
  | zero => exact (hne rfl).elim
  | some x y hP =>
      have hthree' :
          (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP +
            WeierstrassCurve.Affine.Point.some x y hP = 0 := by
        simpa [three_nsmul, two_nsmul, add_assoc] using hthree
      have hdouble :
          (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP =
            -WeierstrassCurve.Affine.Point.some x y hP := by
        rw [← add_eq_zero_iff_eq_neg]
        exact hthree'
      have hy : y ≠ W.negY x y := by
        intro hy
        have htwo :
            (2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 := by
          rw [two_nsmul, WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy]
        have : WeierstrassCurve.Affine.Point.some x y hP = 0 := by
          rw [htwo, zero_add] at hthree'
          exact hthree'
        exact hne this
      let slope := W.slope x x y y
      have hadd :=
        WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hP) hy
      have hxcoord : W.addX x x slope = x := by
        have hsum :
            WeierstrassCurve.Affine.Point.some x y hP +
                WeierstrassCurve.Affine.Point.some x y hP =
              -WeierstrassCurve.Affine.Point.some x y hP := by
          simpa [two_nsmul] using hdouble
        have hsome := hadd.symm.trans hsum
        exact (WeierstrassCurve.Affine.Point.some.inj hsome).1
      have hslope :
          slope * (2 * y + W.a₁ * x + W.a₃) =
            3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y := by
        have hden : y - W.negY x y = 2 * y + W.a₁ * x + W.a₃ := by
          simp only [WeierstrassCurve.Affine.negY]
          ring
        dsimp [slope]
        rw [← hden, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
          div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
      have hx : slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x = 0 := by
        have := hxcoord
        simp only [WeierstrassCurve.Affine.addX] at this
        linarith
      have hcurve := hP.1
      rw [WeierstrassCurve.Affine.equation_iff] at hcurve
      have hψ := tangent_forces_three_division hcurve hslope hx
      refine ⟨x, y, hP, rfl, ?_⟩
      simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
      ring_nf at hψ ⊢
      exact hψ

/-- For a nonsingular affine point over `ℚ`, vanishing of the
three-division polynomial is equivalent to the point being killed by `3`. -/
theorem three_nsmul_some_eq_zero_iff
    (W : WeierstrassCurve.Affine ℚ) {x y : ℚ}
    (hP : W.Nonsingular x y) :
    (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP = 0 ↔
      Polynomial.eval x W.Ψ₃ = 0 := by
  constructor
  · intro hthree
    obtain ⟨x', y', hP', heq, hψ⟩ :=
      nonzero_three_torsion_abscissa W
        (WeierstrassCurve.Affine.Point.some x y hP) hthree
        (WeierstrassCurve.Affine.Point.some_ne_zero hP)
    have hcoords := WeierstrassCurve.Affine.Point.some.inj heq
    simpa [hcoords.1] using hψ
  · intro hψ
    have hcurve := hP.1
    rw [WeierstrassCurve.Affine.equation_iff] at hcurve
    simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_ofNat, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈] at hψ
    let D := 2 * y + W.a₁ * x + W.a₃
    let N := 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y
    have hD : D ≠ 0 := by
      intro hD0
      have hN2 : N ^ 2 = 0 := by
        dsimp [D, N] at hD0 ⊢
        linear_combination
          -hψ - (W.a₁ ^ 2 + 4 * W.a₂ + 12 * x) * hcurve -
          (W.a₁ * (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ - W.a₁ * y) -
            (W.a₂ + 3 * x) * (2 * y + W.a₁ * x + W.a₃)) * hD0
      have hN : N = 0 := sq_eq_zero_iff.mp hN2
      rw [WeierstrassCurve.Affine.nonsingular_iff'] at hP
      rcases hP.2 with hX | hY
      · apply hX
        dsimp [N] at hN
        linarith
      · exact hY (by simpa [D] using hD0)
    let slope := W.slope x x y y
    have hy : y ≠ W.negY x y := by
      intro hy
      apply hD
      dsimp [D]
      simp only [WeierstrassCurve.Affine.negY] at hy
      linarith
    have hslope :
        slope * D = N := by
      have hden : y - W.negY x y = D := by
        dsimp [D]
        ring
      dsimp [slope]
      rw [← hden, WeierstrassCurve.Affine.slope_of_Y_ne rfl hy,
        div_mul_cancel₀ _ (sub_ne_zero.mpr hy)]
    have hidentity :=
      three_division_tangent_identity hcurve hslope
    have hx : slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x = 0 := by
      have hmul : D ^ 2 *
          (slope ^ 2 + W.a₁ * slope - W.a₂ - 3 * x) = 0 := by
        dsimp [D, N] at hidentity ⊢
        linear_combination hidentity - hψ
      exact (mul_eq_zero.mp hmul).resolve_left (pow_ne_zero 2 hD)
    have hadd :=
      WeierstrassCurve.Affine.Point.add_self_of_Y_ne (h₁ := hP) hy
    have hxcoord : W.addX x x slope = x := by
      simp only [WeierstrassCurve.Affine.addX]
      linarith
    change W.addX x x (W.slope x x y y) = x at hxcoord
    have hxrep :
        ((2 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP).xRep =
          (WeierstrassCurve.Affine.Point.some x y hP).xRep := by
      rw [two_nsmul, hadd]
      simp only [WeierstrassCurve.Affine.Point.xRep_some, hxcoord]
    rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep
      with hdouble | hdouble
    · have hzero : WeierstrassCurve.Affine.Point.some x y hP = 0 := by
        have hsum :
            WeierstrassCurve.Affine.Point.some x y hP +
                WeierstrassCurve.Affine.Point.some x y hP =
              WeierstrassCurve.Affine.Point.some x y hP + 0 := by
          rw [add_zero]
          rw [two_nsmul] at hdouble
          exact hdouble
        exact add_left_cancel hsum
      exact (WeierstrassCurve.Affine.Point.some_ne_zero hP hzero).elim
    · rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul,
        hdouble, neg_add_cancel]

private noncomputable def threeTorsionRootMap
    (W : WeierstrassCurve.Affine ℚ) :
    {P : W.Point // (3 : ℕ) • P = 0} →
      Option (W.Ψ₃.rootSet ℚ × Bool)
  | ⟨0, _⟩ => none
  | ⟨WeierstrassCurve.Affine.Point.some x y hP, hthree⟩ =>
      some (⟨x, by
        rw [Polynomial.mem_rootSet_of_ne (W.Ψ₃_ne_zero (by norm_num))]
        exact (three_nsmul_some_eq_zero_iff W hP).mp hthree⟩,
        decide (y ≤ W.negY x y))

private theorem threeTorsionRootMap_injective
    (W : WeierstrassCurve.Affine ℚ) :
    Function.Injective (threeTorsionRootMap W) := by
  rintro ⟨P, hP⟩ ⟨Q, hQ⟩ hmap
  apply Subtype.ext
  cases P with
  | zero =>
      cases Q with
      | zero => rfl
      | some x y hxy => simp [threeTorsionRootMap] at hmap
  | some x y hxy =>
      cases Q with
      | zero => simp [threeTorsionRootMap] at hmap
      | some x' y' hxy' =>
          have hpair :
              ((⟨x, by
                rw [Polynomial.mem_rootSet_of_ne (W.Ψ₃_ne_zero (by norm_num))]
                exact (three_nsmul_some_eq_zero_iff W hxy).mp hP⟩,
                decide (y ≤ W.negY x y)) : W.Ψ₃.rootSet ℚ × Bool) =
              ((⟨x', by
                rw [Polynomial.mem_rootSet_of_ne (W.Ψ₃_ne_zero (by norm_num))]
                exact (three_nsmul_some_eq_zero_iff W hxy').mp hQ⟩,
                decide (y' ≤ W.negY x' y')) : W.Ψ₃.rootSet ℚ × Bool) := by
            simpa only [threeTorsionRootMap, Option.some.injEq] using hmap
          have hx : x = x' :=
            congrArg (fun z : W.Ψ₃.rootSet ℚ × Bool ↦ z.1.1) hpair
          have hbool :
              decide (y ≤ W.negY x y) =
                decide (y' ≤ W.negY x' y') :=
            congrArg (fun z : W.Ψ₃.rootSet ℚ × Bool ↦ z.2) hpair
          subst x'
          have hxrep :
              (WeierstrassCurve.Affine.Point.some x y hxy).xRep =
                (WeierstrassCurve.Affine.Point.some x y' hxy').xRep := by
            simp
          rcases
              WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep
            with heq | heq
          · exact heq
          · have hy : y = W.negY x y' :=
              (WeierstrassCurve.Affine.Point.some.inj heq).2
            have hy' : y' = W.negY x y := by
              rw [hy, WeierstrassCurve.Affine.negY_negY]
            have hbool' : (y ≤ y') ↔ (y' ≤ y) := by
              rw [hy'.symm, hy.symm] at hbool
              exact decide_eq_decide.mp hbool
            have hyy : y = y' := by
              by_contra hne
              rcases lt_or_gt_of_ne hne with hlt | hgt
              · exact (not_le_of_gt hlt) (hbool'.mp (le_of_lt hlt))
              · exact (not_le_of_gt hgt) (hbool'.mpr (le_of_lt hgt))
            simp only [WeierstrassCurve.Affine.Point.some.injEq]
            exact ⟨trivial, hyy⟩

/-- The rational three-torsion of a Weierstrass curve has at most nine
points. -/
theorem ncard_three_torsion_le_nine
    (W : WeierstrassCurve.Affine ℚ) :
    Set.ncard {P : W.Point | (3 : ℕ) • P = 0} ≤ 9 := by
  rw [← Nat.card_coe_set_eq]
  calc
    Nat.card {P : W.Point // (3 : ℕ) • P = 0}
        ≤ Nat.card (Option (W.Ψ₃.rootSet ℚ × Bool)) :=
      Nat.card_le_card_of_injective (threeTorsionRootMap W)
        (threeTorsionRootMap_injective W)
    _ = Nat.card (W.Ψ₃.rootSet ℚ) * Nat.card Bool + 1 := by
      rw [Finite.card_option, Nat.card_prod]
    _ ≤ 4 * 2 + 1 := by
      gcongr
      · rw [Nat.card_coe_set_eq]
        exact (W.Ψ₃.ncard_rootSet_le ℚ).trans_eq
          (W.natDegree_Ψ₃ (by norm_num))
      · norm_num
    _ = 9 := by norm_num

lemma quartic_coefficients_of_four_distinct_roots
    {b₂ b₄ b₆ b₈ r₁ r₂ r₃ r₄ : ℚ}
    (hne₁₂ : r₁ ≠ r₂) (hne₁₃ : r₁ ≠ r₃) (hne₁₄ : r₁ ≠ r₄)
    (hne₂₃ : r₂ ≠ r₃) (hne₂₄ : r₂ ≠ r₄) (hne₃₄ : r₃ ≠ r₄)
    (h₁ : 3 * r₁ ^ 4 + b₂ * r₁ ^ 3 + 3 * b₄ * r₁ ^ 2 +
      3 * b₆ * r₁ + b₈ = 0)
    (h₂ : 3 * r₂ ^ 4 + b₂ * r₂ ^ 3 + 3 * b₄ * r₂ ^ 2 +
      3 * b₆ * r₂ + b₈ = 0)
    (h₃ : 3 * r₃ ^ 4 + b₂ * r₃ ^ 3 + 3 * b₄ * r₃ ^ 2 +
      3 * b₆ * r₃ + b₈ = 0)
    (h₄ : 3 * r₄ ^ 4 + b₂ * r₄ ^ 3 + 3 * b₄ * r₄ ^ 2 +
      3 * b₆ * r₄ + b₈ = 0) :
    b₂ = -3 * (r₁ + r₂ + r₃ + r₄) ∧
      b₄ = r₁ * r₂ + r₁ * r₃ + r₁ * r₄ +
        r₂ * r₃ + r₂ * r₄ + r₃ * r₄ ∧
      b₆ = -(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ +
        r₁ * r₃ * r₄ + r₂ * r₃ * r₄) ∧
      b₈ = 3 * (r₁ * r₂ * r₃ * r₄) := by
  have g₁₂ :
      3 * (r₁ ^ 3 + r₁ ^ 2 * r₂ + r₁ * r₂ ^ 2 + r₂ ^ 3) +
        b₂ * (r₁ ^ 2 + r₁ * r₂ + r₂ ^ 2) +
        3 * b₄ * (r₁ + r₂) + 3 * b₆ = 0 := by
    have hfactor : (r₁ - r₂) * (
        3 * (r₁ ^ 3 + r₁ ^ 2 * r₂ + r₁ * r₂ ^ 2 + r₂ ^ 3) +
          b₂ * (r₁ ^ 2 + r₁ * r₂ + r₂ ^ 2) +
          3 * b₄ * (r₁ + r₂) + 3 * b₆) = 0 := by
      linear_combination h₁ - h₂
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₁₂)
  have g₁₃ :
      3 * (r₁ ^ 3 + r₁ ^ 2 * r₃ + r₁ * r₃ ^ 2 + r₃ ^ 3) +
        b₂ * (r₁ ^ 2 + r₁ * r₃ + r₃ ^ 2) +
        3 * b₄ * (r₁ + r₃) + 3 * b₆ = 0 := by
    have hfactor : (r₁ - r₃) * (
        3 * (r₁ ^ 3 + r₁ ^ 2 * r₃ + r₁ * r₃ ^ 2 + r₃ ^ 3) +
          b₂ * (r₁ ^ 2 + r₁ * r₃ + r₃ ^ 2) +
          3 * b₄ * (r₁ + r₃) + 3 * b₆) = 0 := by
      linear_combination h₁ - h₃
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₁₃)
  have g₁₄ :
      3 * (r₁ ^ 3 + r₁ ^ 2 * r₄ + r₁ * r₄ ^ 2 + r₄ ^ 3) +
        b₂ * (r₁ ^ 2 + r₁ * r₄ + r₄ ^ 2) +
        3 * b₄ * (r₁ + r₄) + 3 * b₆ = 0 := by
    have hfactor : (r₁ - r₄) * (
        3 * (r₁ ^ 3 + r₁ ^ 2 * r₄ + r₁ * r₄ ^ 2 + r₄ ^ 3) +
          b₂ * (r₁ ^ 2 + r₁ * r₄ + r₄ ^ 2) +
          3 * b₄ * (r₁ + r₄) + 3 * b₆) = 0 := by
      linear_combination h₁ - h₄
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₁₄)
  have q₁₂₃ :
      3 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₃ +
        r₂ ^ 2 + r₂ * r₃ + r₃ ^ 2) +
        b₂ * (r₁ + r₂ + r₃) + 3 * b₄ = 0 := by
    have hfactor : (r₂ - r₃) * (
        3 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₃ +
          r₂ ^ 2 + r₂ * r₃ + r₃ ^ 2) +
          b₂ * (r₁ + r₂ + r₃) + 3 * b₄) = 0 := by
      linear_combination g₁₂ - g₁₃
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₂₃)
  have q₁₂₄ :
      3 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₄ +
        r₂ ^ 2 + r₂ * r₄ + r₄ ^ 2) +
        b₂ * (r₁ + r₂ + r₄) + 3 * b₄ = 0 := by
    have hfactor : (r₂ - r₄) * (
        3 * (r₁ ^ 2 + r₁ * r₂ + r₁ * r₄ +
          r₂ ^ 2 + r₂ * r₄ + r₄ ^ 2) +
          b₂ * (r₁ + r₂ + r₄) + 3 * b₄) = 0 := by
      linear_combination g₁₂ - g₁₄
    exact (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₂₄)
  have hb₂ : b₂ = -3 * (r₁ + r₂ + r₃ + r₄) := by
    have hfactor : (r₃ - r₄) *
        (3 * (r₁ + r₂ + r₃ + r₄) + b₂) = 0 := by
      linear_combination q₁₂₃ - q₁₂₄
    have := (mul_eq_zero.mp hfactor).resolve_left (sub_ne_zero.mpr hne₃₄)
    linarith
  have hb₄ : b₄ = r₁ * r₂ + r₁ * r₃ + r₁ * r₄ +
      r₂ * r₃ + r₂ * r₄ + r₃ * r₄ := by
    have h := q₁₂₃
    rw [hb₂] at h
    linear_combination (1 : ℚ) / 3 * h
  have hb₆ : b₆ = -(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ +
      r₁ * r₃ * r₄ + r₂ * r₃ * r₄) := by
    have h := g₁₂
    rw [hb₂, hb₄] at h
    linear_combination (1 : ℚ) / 3 * h
  have hb₈ : b₈ = 3 * (r₁ * r₂ * r₃ * r₄) := by
    have h := h₁
    rw [hb₂, hb₄, hb₆] at h
    linear_combination h
  exact ⟨hb₂, hb₄, hb₆, hb₈⟩

lemma four_distinct_roots_invariant_impossible
    {b₂ b₄ b₆ b₈ r₁ r₂ r₃ r₄ : ℚ}
    (hne₁₂ : r₁ ≠ r₂) (hne₃₄ : r₃ ≠ r₄)
    (hb₂ : b₂ = -3 * (r₁ + r₂ + r₃ + r₄))
    (hb₄ : b₄ =
      r₁ * r₂ + r₁ * r₃ + r₁ * r₄ + r₂ * r₃ + r₂ * r₄ + r₃ * r₄)
    (hb₆ : b₆ = -(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ +
      r₁ * r₃ * r₄ + r₂ * r₃ * r₄))
    (hb₈ : b₈ = 3 * (r₁ * r₂ * r₃ * r₄))
    (hrel : 4 * b₈ = b₂ * b₆ - b₄ ^ 2) :
    False := by
  subst b₂
  subst b₄
  subst b₆
  subst b₈
  have hid :
      2 * (12 * (r₁ * r₂ * r₃ * r₄) -
          (-3 * (r₁ + r₂ + r₃ + r₄)) *
            (-(r₁ * r₂ * r₃ + r₁ * r₂ * r₄ +
              r₁ * r₃ * r₄ + r₂ * r₃ * r₄)) +
          (r₁ * r₂ + r₁ * r₃ + r₁ * r₄ +
            r₂ * r₃ + r₂ * r₄ + r₃ * r₄) ^ 2) =
        ((r₁ - r₂) * (r₃ - r₄)) ^ 2 +
          ((r₁ - r₃) * (r₂ - r₄)) ^ 2 +
          ((r₁ - r₄) * (r₂ - r₃)) ^ 2 := by
    ring
  have hpair : (r₁ - r₂) * (r₃ - r₄) ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hne₁₂) (sub_ne_zero.mpr hne₃₄)
  have hpos : 0 < ((r₁ - r₂) * (r₃ - r₄)) ^ 2 :=
    sq_pos_of_ne_zero hpair
  have hnonneg₁ : 0 ≤ ((r₁ - r₃) * (r₂ - r₄)) ^ 2 := sq_nonneg _
  have hnonneg₂ : 0 ≤ ((r₁ - r₄) * (r₂ - r₃)) ^ 2 := sq_nonneg _
  nlinarith

private lemma abscissa_ne_of_independent_images
    (W : WeierstrassCurve.Affine ℚ)
    (φ : (ZMod 3 × ZMod 3) →+ W.Point) (hφ : Function.Injective φ)
    {z w : ZMod 3 × ZMod 3} (hzw : z ≠ w) (hznegw : z ≠ -w)
    {xz yz xw yw : ℚ}
    {hz : W.Nonsingular xz yz} {hw : W.Nonsingular xw yw}
    (hPz : φ z = .some xz yz hz) (hPw : φ w = .some xw yw hw) :
    xz ≠ xw := by
  intro hx
  have hxrep :
      (WeierstrassCurve.Affine.Point.some xz yz hz).xRep =
        (WeierstrassCurve.Affine.Point.some xw yw hw).xRep := by
    simp [hx]
  rcases WeierstrassCurve.Affine.Point.eq_or_eq_neg_of_xRep_eq_xRep hxrep
    with heq | heq
  · apply hzw
    exact hφ (hPz.trans (heq.trans hPw.symm))
  · apply hznegw
    apply hφ
    calc
      φ z = WeierstrassCurve.Affine.Point.some xz yz hz := hPz
      _ = -WeierstrassCurve.Affine.Point.some xw yw hw := heq
      _ = -φ w := congrArg Neg.neg hPw.symm
      _ = φ (-w) := (map_neg φ w).symm

/-- There is no full rational three-torsion subgroup on a Weierstrass curve
over `ℚ`. -/
theorem not_injective_zmod_three_square
    (E : WeierstrassCurve ℚ)
    (φ : (ZMod 3 × ZMod 3) →+ (E⁄ℚ).Point) :
    ¬ Function.Injective φ := by
  intro hφ
  let z₁ : ZMod 3 × ZMod 3 := (1, 0)
  let z₂ : ZMod 3 × ZMod 3 := (0, 1)
  let z₃ : ZMod 3 × ZMod 3 := (1, 1)
  let z₄ : ZMod 3 × ZMod 3 := (1, 2)
  let P₁ : (E⁄ℚ).Point := φ z₁
  let P₂ : (E⁄ℚ).Point := φ z₂
  let P₃ : (E⁄ℚ).Point := φ z₃
  let P₄ : (E⁄ℚ).Point := φ z₄
  have hthree (z : ZMod 3 × ZMod 3) : (3 : ℕ) • φ z = 0 := by
    have hz : (3 : ℕ) • z = 0 := by
      rcases z with ⟨a, b⟩
      apply Prod.ext
      · change (3 : ℕ) • a = 0
        rw [nsmul_eq_mul]
        rw [show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul]
      · change (3 : ℕ) • b = 0
        rw [nsmul_eq_mul]
        rw [show ((3 : ℕ) : ZMod 3) = 0 by decide, zero_mul]
    rw [← map_nsmul, hz, map_zero]
  have hn₁ : P₁ ≠ 0 := by
    intro h
    exact (by decide : z₁ ≠ 0) (hφ (by simpa [P₁] using h))
  have hn₂ : P₂ ≠ 0 := by
    intro h
    exact (by decide : z₂ ≠ 0) (hφ (by simpa [P₂] using h))
  have hn₃ : P₃ ≠ 0 := by
    intro h
    exact (by decide : z₃ ≠ 0) (hφ (by simpa [P₃] using h))
  have hn₄ : P₄ ≠ 0 := by
    intro h
    exact (by decide : z₄ ≠ 0) (hφ (by simpa [P₄] using h))
  obtain ⟨r₁, y₁, hP₁, hP₁eq, hr₁⟩ :=
    nonzero_three_torsion_abscissa (E⁄ℚ) P₁ (hthree z₁) hn₁
  obtain ⟨r₂, y₂, hP₂, hP₂eq, hr₂⟩ :=
    nonzero_three_torsion_abscissa (E⁄ℚ) P₂ (hthree z₂) hn₂
  obtain ⟨r₃, y₃, hP₃, hP₃eq, hr₃⟩ :=
    nonzero_three_torsion_abscissa (E⁄ℚ) P₃ (hthree z₃) hn₃
  obtain ⟨r₄, y₄, hP₄, hP₄eq, hr₄⟩ :=
    nonzero_three_torsion_abscissa (E⁄ℚ) P₄ (hthree z₄) hn₄
  have hrepr₁ : φ z₁ = .some r₁ y₁ hP₁ := by simpa [P₁] using hP₁eq
  have hrepr₂ : φ z₂ = .some r₂ y₂ hP₂ := by simpa [P₂] using hP₂eq
  have hrepr₃ : φ z₃ = .some r₃ y₃ hP₃ := by simpa [P₃] using hP₃eq
  have hrepr₄ : φ z₄ = .some r₄ y₄ hP₄ := by simpa [P₄] using hP₄eq
  have hr₁₂ : r₁ ≠ r₂ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₁ hrepr₂
  have hr₁₃ : r₁ ≠ r₃ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₁ hrepr₃
  have hr₁₄ : r₁ ≠ r₄ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₁ hrepr₄
  have hr₂₃ : r₂ ≠ r₃ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₂ hrepr₃
  have hr₂₄ : r₂ ≠ r₄ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₂ hrepr₄
  have hr₃₄ : r₃ ≠ r₄ :=
    abscissa_ne_of_independent_images (E⁄ℚ) φ hφ
      (by decide) (by decide) hrepr₃ hrepr₄
  simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat] at hr₁ hr₂ hr₃ hr₄
  obtain ⟨hb₂, hb₄, hb₆, hb₈⟩ :=
    quartic_coefficients_of_four_distinct_roots
      hr₁₂ hr₁₃ hr₁₄ hr₂₃ hr₂₄ hr₃₄ hr₁ hr₂ hr₃ hr₄
  exact four_distinct_roots_invariant_impossible hr₁₂ hr₃₄
    hb₂ hb₄ hb₆ hb₈ (E⁄ℚ).b_relation

end MazurTorsion.ThreeTorsion

end

/- Source: MazurTorsion/EllipticCurve/VariableChange.lean -/

section

/-
Copyright (c) 2026 Kevin Buzzard, Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude, Vasily Ilin
-/


/-!
# Isomorphism of point groups induced by a change of variables

This file is ported from Michael Stoll's Apache-2.0 `EllipticCurves` project at commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

The derivative-transport and singular-cubic nonsingular-locus equivalence are local extensions.
They generalize the ported point equivalence beyond elliptic equations while retaining the
original admissible change-of-variables formulas and attribution.

Mathlib's affine `Point` API provides the group homomorphism induced by a change of the base
field for a fixed Weierstrass curve, but not the isomorphism of Mordell--Weil groups induced by
an admissible change of variables between two different curves. For
`C : WeierstrassCurve.VariableChange F`, the admissible change

`(x, y) ↦ (u²x + r, u³y + u²sx + t)`

gives the group isomorphism
`WeierstrassCurve.Affine.Point.equivVariableChange : (C • W).Point ≃+ W.Point`.
Its inverse is the explicit change of variables `C⁻¹`.
-/

section

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-! ### Transformation of the group-law formulae under a change of variables -/

lemma variableChange_negY (x y : F) :
    W.toAffine.negY ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) ^ 3 * (C • W).toAffine.negY x y + (C.u : F) ^ 2 * C.s * x + C.t := by
  simp [negY, variableChange_a₁, variableChange_a₃]
  field

/-- The image of a pair of points under the change of variables satisfies the `y₁ = -y₂`
degeneracy condition only if the original pair does. -/
lemma variableChange_negY_ne {x₁ x₂ y₁ y₂ : F}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    ¬((C.u : F) ^ 2 * x₁ + C.r = (C.u : F) ^ 2 * x₂ + C.r ∧
      (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t = W.toAffine.negY
        ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  intro ⟨hX, hY⟩
  have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
  subst hx
  rw [variableChange_negY] at hY
  exact hxy ⟨rfl, mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY)⟩

lemma variableChange_addX (x₁ x₂ ℓ : F) :
    W.toAffine.addX ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  simp [addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_negAddY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.negAddY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.negAddY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp [negAddY, addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_addY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.addY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [addY, variableChange_negAddY, variableChange_addX, variableChange_negY]

lemma variableChange_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rcases eq_or_ne x₁ x₂ with rfl | hx
  · have hy : y₁ ≠ (C • W).toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    obtain rfl := Y_eq_of_Y_ne h₁ h₂ rfl hy
    have hΦy : (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t
        ≠ W.toAffine.negY ((C.u : F) ^ 2 * x₁ + C.r)
            ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) := by
      rw [variableChange_negY]
      exact fun h ↦ hy (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination h))
    rw [W.toAffine.slope_of_Y_ne rfl hΦy, (C • W).toAffine.slope_of_Y_ne rfl hy,
      ← mul_div_assoc, div_add' _ _ _ (sub_ne_zero.mpr hy),
      div_eq_div_iff (sub_ne_zero.mpr hΦy) (sub_ne_zero.mpr hy)]
    simp [negY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
    field
  · have hΦx : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r := by
      simpa [mul_right_inj' (pow_ne_zero 2 hu)] using hx
    rw [W.toAffine.slope_of_X_ne hΦx, (C • W).toAffine.slope_of_X_ne hx]
    have h1 := sub_ne_zero.mpr hΦx
    have h2 := sub_ne_zero.mpr hx
    field

/-- A point `(x, y)` lies on `C • W` if and only if `(u²x + r, u³y + u²sx + t)` lies on `W`. -/
lemma variableChange_equation (x y : F) :
    W.toAffine.Equation ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Equation x y := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [equation_iff', variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val, field]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> linear_combination h

/-- The `Y`-derivative of a Weierstrass equation under an admissible change of variables.
This formula does not require either equation to be elliptic. -/
lemma variableChange_polynomialY (x y : F) :
    W.toAffine.polynomialY.evalEval ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) =
      (C.u : F) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y := by
  simp only [Affine.evalEval_polynomialY, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field

/-- The `X`-derivative of a Weierstrass equation under an admissible change of variables.
The correction term is the chain-rule contribution from the `sx` term in the new `Y` coordinate.
This formula does not require either equation to be elliptic. -/
lemma variableChange_polynomialX (x y : F) :
    W.toAffine.polynomialX.evalEval ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) =
      (C.u : F) ^ 4 * (C • W).toAffine.polynomialX.evalEval x y -
        C.s * ((C.u : F) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y) := by
  simp only [Affine.evalEval_polynomialX, Affine.evalEval_polynomialY, variableChange_a₁,
    variableChange_a₂, variableChange_a₃, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field

/-- An admissible change of variables identifies the nonsingular loci even when the common
Weierstrass cubic is singular. -/
lemma variableChange_nonsingular (x y : F) :
    W.toAffine.Nonsingular ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) ↔
      (C • W).toAffine.Nonsingular x y := by
  rw [Affine.Nonsingular, Affine.Nonsingular, variableChange_equation W C,
    variableChange_polynomialX W C, variableChange_polynomialY W C]
  apply and_congr_right
  intro _
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  constructor
  · rintro (hx | hy)
    · by_cases hY : (C • W).toAffine.polynomialY.evalEval x y = 0
      · left
        intro hX
        apply hx
        rw [hY, mul_zero, mul_zero, sub_zero, hX, mul_zero]
      · exact Or.inr hY
    · exact Or.inr fun hY ↦ hy (mul_eq_zero.mpr <| Or.inr hY)
  · rintro (hx | hy)
    · by_cases hY : (C • W).toAffine.polynomialY.evalEval x y = 0
      · left
        rw [hY, mul_zero, mul_zero, sub_zero]
        exact mul_ne_zero (pow_ne_zero 4 hu) hx
      · exact Or.inr (mul_ne_zero (pow_ne_zero 3 hu) hY)
    · exact Or.inr (mul_ne_zero (pow_ne_zero 3 hu) hy)

/-! ### The induced isomorphism of point groups -/

namespace Point

/-- The underlying point map of the change of variables, sending `0` to `0`. -/
def mapVariableChangeFun : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some ((C.u : F) ^ 2 * x + C.r)
      ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ((variableChange_nonsingular W C x y).mpr h)

@[simp] lemma mapVariableChangeFun_zero : mapVariableChangeFun W C 0 = 0 := rfl

lemma mapVariableChangeFun_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    mapVariableChangeFun W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) := rfl

lemma some_eq_some (W : WeierstrassCurve F) {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂} :
    (some x₁ y₁ h₁ : W.toAffine.Point) = some x₂ y₂ h₂ := by
  subst hx hy
  rfl

lemma mapVariableChangeFun_injective :
    Function.Injective (mapVariableChangeFun W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [mapVariableChangeFun] at h
  · simp [mapVariableChangeFun] at h
  · rw [mapVariableChangeFun_some, mapVariableChangeFun_some] at h
    injection h with hX hY
    have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
    exact some_eq_some (C • W) hx
      (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx))

variable [DecidableEq F]

/-- Transport of the affine point group along an equality of Weierstrass curves. -/
def equivOfEq {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.Point ≃+ V'.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

@[simp] lemma equivOfEq_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    equivOfEq h (some x y hns) = some x y (h ▸ hns) := by
  subst h
  rfl

/-- The group homomorphism induced by the admissible change of variables. -/
def mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := mapVariableChangeFun W C
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [mapVariableChangeFun_some]
    have e₁ : (C • W).toAffine.Equation x₁ y₁ := h₁.left
    have e₂ : (C • W).toAffine.Equation x₂ y₂ := h₂.left
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2, mapVariableChangeFun_zero]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, mapVariableChangeFun_some, add_some (variableChange_negY_ne W C hxy)]
      simp only [variableChange_slope W C e₁ e₂ hxy, variableChange_addX, variableChange_addY]

/-- The point-group isomorphism induced by the admissible change of variables. -/
def equivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  have hright : ∀ P, mapVariableChangeFun W C
      (mapVariableChangeFun (C • W) C⁻¹ (equivOfEq (inv_smul_smul C W).symm P)) = P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨X, Y, h⟩)
    · simp [← zero_def]
    · rw [equivOfEq_some, mapVariableChangeFun_some, mapVariableChangeFun_some]
      refine some_eq_some W ?_ ?_ <;>
        (simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]; field)
  { toFun := mapVariableChangeFun W C
    invFun := fun P ↦ mapVariableChangeFun (C • W) C⁻¹ (equivOfEq (inv_smul_smul C W).symm P)
    left_inv := Function.RightInverse.leftInverse_of_injective hright
      (mapVariableChangeFun_injective W C)
    right_inv := hright
    map_add' := (mapVariableChange W C).map_add' }

lemma equivVariableChange_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    equivVariableChange W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) := rfl

end Point

end WeierstrassCurve.Affine

end

end

/- Source: MazurTorsion/NumberTheory/OrderThirtyFiveQuotient.lean -/

section

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# The fixed elliptic model expected at level 35

The literature identifies the elliptic quotient `X₀(35)/w₅` with the model

`X₀(35)/w₅ : y² + y = x³ + x² + 9x + 1`.

This file only fixes that Weierstrass equation and checks its elementary
arithmetic data.  It does **not** construct the modular curve, the quotient
map by `w₅`, or an isomorphism from that quotient to this model; those remain
separate obligations on the order-35 critical path.  The
translation

`x = X + 1`, `y = Y + 2X + 3`

identifies it with the rational-three-torsion normal form

`Y² + 4XY + 7Y = X³`.

The marked point `(X,Y) = (0,0)`, hence `(x,y) = (1,3)` on the fixed model,
has exact order three.  This is arithmetic input for a prospective
curve-specific three-isogeny descent; it also explains why the existing
two-isogeny descent files are not the right API for this model.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

/-- The fixed rational Weierstrass model expected for `X₀(35)/w₅`.

No modular interpretation is part of this definition. -/
def optimalQuotientModel : WeierstrassCurve ℚ :=
  ⟨0, 1, 1, 9, 1⟩

/-- The integral model underlying `optimalQuotientModel`. -/
def optimalQuotientModelIntegral : WeierstrassCurve ℤ :=
  ⟨0, 1, 1, 9, 1⟩

/-- The discriminant of the selected integral model is `-5³7³`. -/
theorem optimalQuotientModelIntegral_discriminant :
    optimalQuotientModelIntegral.Δ = -42875 := by
  norm_num [optimalQuotientModelIntegral, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The integral and rational definitions are literally compatible. -/
theorem map_optimalQuotientModelIntegral :
    (optimalQuotientModelIntegral.map (algebraMap ℤ ℚ)).toAffine =
      optimalQuotientModel.toAffine := by
  ext <;> simp [optimalQuotientModelIntegral, optimalQuotientModel]

instance optimalQuotientModel_isElliptic : optimalQuotientModel.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [optimalQuotientModel, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The order-three Tate normal form of the fixed model. -/
def threeTorsionCurve : WeierstrassCurve ℚ :=
  ⟨4, 0, 7, 0, 0⟩

instance threeTorsionCurve_isElliptic : threeTorsionCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [threeTorsionCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The admissible change `x = X+1`, `y = Y+2X+3`. -/
def threeTorsionChange : WeierstrassCurve.VariableChange ℚ :=
  WeierstrassCurve.VariableChange.mk 1 1 2 3

/-- Applying the explicit change to the model gives its order-three
normal form. -/
theorem threeTorsionChange_smul :
    threeTorsionChange • optimalQuotientModel = threeTorsionCurve := by
  ext <;>
    norm_num [WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆,
      threeTorsionChange, optimalQuotientModel, threeTorsionCurve]

/-- The point-group equivalence furnished by the explicit normalization. -/
noncomputable def threeTorsionEquiv :
    threeTorsionCurve.toAffine.Point ≃+
      optimalQuotientModel.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.equivOfEq
      threeTorsionChange_smul.symm).trans
    (WeierstrassCurve.Affine.Point.equivVariableChange
      optimalQuotientModel threeTorsionChange)

private theorem threeTorsionOrigin_nonsingular :
    threeTorsionCurve.toAffine.Nonsingular 0 0 := by
  apply threeTorsionCurve.toAffine.equation_iff_nonsingular.mp
  norm_num [WeierstrassCurve.Affine.equation_iff,
    threeTorsionCurve]

/-- The marked origin on the order-three normal form. -/
def threeTorsionOrigin : threeTorsionCurve.toAffine.Point :=
  .some 0 0 threeTorsionOrigin_nonsingular

private theorem double_threeTorsionOrigin :
    (2 : ℕ) • threeTorsionOrigin = -threeTorsionOrigin := by
  simp only [two_nsmul, threeTorsionOrigin]
  rw [WeierstrassCurve.Affine.Point.add_self_of_Y_ne]
  · rw [WeierstrassCurve.Affine.Point.neg_some]
    simp only [WeierstrassCurve.Affine.Point.some.injEq]
    constructor
    · norm_num [WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.slope,
        WeierstrassCurve.Affine.negY, threeTorsionCurve]
    · norm_num [WeierstrassCurve.Affine.addY,
        WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.slope,
        WeierstrassCurve.Affine.negY, threeTorsionCurve]
  · norm_num [WeierstrassCurve.Affine.negY, threeTorsionCurve]

private theorem three_nsmul_threeTorsionOrigin :
    (3 : ℕ) • threeTorsionOrigin = 0 := by
  calc
    (3 : ℕ) • threeTorsionOrigin =
        threeTorsionOrigin + (2 : ℕ) • threeTorsionOrigin := by abel
    _ = threeTorsionOrigin + -threeTorsionOrigin := by
      rw [double_threeTorsionOrigin]
    _ = 0 := add_neg_cancel _

/-- The marked origin has exact additive order three. -/
theorem addOrderOf_threeTorsionOrigin :
    addOrderOf threeTorsionOrigin = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by decide⟩
  apply addOrderOf_eq_prime three_nsmul_threeTorsionOrigin
  exact WeierstrassCurve.Affine.Point.some_ne_zero _

/-- The visible rational point `(1,3)` on the fixed model. -/
def modelThreeTorsion : optimalQuotientModel.toAffine.Point :=
  .some 1 3 (by
    apply optimalQuotientModel.toAffine.equation_iff_nonsingular.mp
    norm_num [WeierstrassCurve.Affine.equation_iff,
      optimalQuotientModel])

/-- The normalization sends `(0,0)` to the literal point `(1,3)`. -/
theorem threeTorsionEquiv_origin :
    threeTorsionEquiv threeTorsionOrigin = modelThreeTorsion := by
  rw [threeTorsionEquiv]
  simp only [AddEquiv.trans_apply]
  rw [threeTorsionOrigin]
  rw [WeierstrassCurve.Affine.Point.equivOfEq_some]
  rw [WeierstrassCurve.Affine.Point.equivVariableChange_some]
  apply WeierstrassCurve.Affine.Point.some_eq_some optimalQuotientModel
  · norm_num [threeTorsionChange]
  · norm_num [threeTorsionChange]

/-- The visible point `(1,3)` has exact rational order three. -/
theorem addOrderOf_modelThreeTorsion :
    addOrderOf modelThreeTorsion = 3 := by
  rw [← threeTorsionEquiv_origin,
    AddEquiv.addOrderOf_eq threeTorsionEquiv]
  exact addOrderOf_threeTorsionOrigin

private theorem eq_zero_of_two_nsmul_eq_zero (P : optimalQuotientModel.toAffine.Point)
    (hP : (2 : ℕ) • P = 0) : P = 0 := by
  cases P with
  | zero => rfl
  | some x y h =>
    have hxy : y^2+y = x^3+x^2+9*x+1 := by
      simpa [WeierstrassCurve.Affine.equation_iff, optimalQuotientModel] using h.1
    have hs : WeierstrassCurve.Affine.Point.some x y h = -(.some x y h) := by
      apply (add_eq_zero_iff_eq_neg).mp
      simpa only [two_nsmul] using hP
    rw [WeierstrassCurve.Affine.Point.neg_some] at hs
    have hxy' : x = x ∧ y = optimalQuotientModel.toAffine.negY x y := by
      simpa only [WeierstrassCurve.Affine.Point.some.injEq] using hs
    have hy := hxy'.2
    change y = -y-0*x-1 at hy
    exact (optimal35_completedOrdinate_ne_zero hxy (by linarith)).elim

end MazurTorsion.OrderThirtyFive

end

/- Source: MazurTorsion/NumberTheory/OrderThirtyFiveThreeIsogeny.lean -/

section

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# An equation-checked Vélu three-isogeny candidate

On the normalized curve

`E : y² + 4xy + 7y = x³`,

the points `(0,0)` and `(0,-7)` form the nonidentity part of a rational
order-three subgroup.  Vélu's coordinate sums suggest the target model

`E' : Y² + 4XY + 7Y = X³ - 140X - 791`

and, away from that subgroup, the coordinate formulas

```
X = (x³ + 28x + 49) / x²,
Y = (x³y - 28xy - 98y - 112x² - 392x - 343) / x³.
```

This file checks that the denominator-safe point function lands on `E'`
and computes its zero fibre.  It does **not** yet prove that the function is
additive, construct a bundled isogeny, determine its degree, construct its
dual, or prove a multiplication-by-three composition.  Accordingly all
declarations below use candidate and zero-fibre language.

The file also proves that `E'` has
trivial rational torsion: reduction modulo three bounds torsion by three,
while an explicit factorization of the third division polynomial rules out
nonidentity rational three-torsion.  These are fixed-curve arithmetic inputs
for a prospective three-isogeny Selmer calculation, not such a calculation.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve.Affine

/-- The candidate target obtained from the Vélu coordinate formulas for the
visible order-three subgroup. -/
def veluThreeCandidateTarget : WeierstrassCurve ℚ :=
  ⟨4, 0, 7, -140, -791⟩

/-- The integral model of the candidate target. -/
def veluThreeCandidateTargetIntegral : WeierstrassCurve ℤ :=
  ⟨4, 0, 7, -140, -791⟩

/-- The candidate target discriminant is `-5⁹7`. -/
theorem veluThreeCandidateTargetIntegral_discriminant :
    veluThreeCandidateTargetIntegral.Δ = -13671875 := by
  norm_num [veluThreeCandidateTargetIntegral,
    WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

theorem map_veluThreeCandidateTargetIntegral :
    (veluThreeCandidateTargetIntegral.map
      (algebraMap ℤ ℚ)).toAffine =
        veluThreeCandidateTarget.toAffine := by
  ext <;> simp [veluThreeCandidateTargetIntegral,
    veluThreeCandidateTarget]

instance veluThreeCandidateTarget_isElliptic :
    veluThreeCandidateTarget.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff]
  norm_num [veluThreeCandidateTarget, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- The candidate abscissa formula away from the visible subgroup. -/
def veluThreeCandidateX (x : ℚ) : ℚ :=
  (x ^ 3 + 28 * x + 49) / x ^ 2

/-- The candidate ordinate formula away from the visible subgroup. -/
def veluThreeCandidateY (x y : ℚ) : ℚ :=
  (x ^ 3 * y - 28 * x * y - 98 * y - 112 * x ^ 2 -
      392 * x - 343) / x ^ 3

private theorem threeTorsionCurve_equation
    {x y : ℚ}
    (h : threeTorsionCurve.toAffine.Nonsingular x y) :
    y ^ 2 + 4 * x * y + 7 * y = x ^ 3 := by
  have heq := h.1
  rw [WeierstrassCurve.Affine.equation_iff] at heq
  norm_num [threeTorsionCurve] at heq
  exact heq

/-- Direct substitution verifies the Vélu formulas. -/
theorem veluThreeCandidate_equation
    {x y : ℚ} (hx : x ≠ 0)
    (hcurve : y ^ 2 + 4 * x * y + 7 * y = x ^ 3) :
    veluThreeCandidateY x y ^ 2 +
        4 * veluThreeCandidateX x * veluThreeCandidateY x y +
        7 * veluThreeCandidateY x y =
      veluThreeCandidateX x ^ 3 - 140 * veluThreeCandidateX x - 791 := by
  simp only [veluThreeCandidateX, veluThreeCandidateY]
  field_simp [hx]
  linear_combination
    (x ^ 3 - 28 * x - 98) ^ 2 * hcurve

private theorem veluThreeCandidate_nonsingular
    {x y : ℚ}
    (h : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    veluThreeCandidateTarget.toAffine.Nonsingular
      (veluThreeCandidateX x) (veluThreeCandidateY x y) := by
  apply veluThreeCandidateTarget.toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [veluThreeCandidateTarget]
  simpa only [sub_eq_add_neg] using
    veluThreeCandidate_equation hx (threeTorsionCurve_equation h)

/-- The denominator-safe point-function candidate.  No additivity theorem is
asserted here. -/
noncomputable def veluThreeCandidatePointFun :
    threeTorsionCurve.toAffine.Point →
      veluThreeCandidateTarget.toAffine.Point
  | .zero => .zero
  | .some x y h =>
      if hx : x = 0 then .zero
      else .some (veluThreeCandidateX x) (veluThreeCandidateY x y)
        (veluThreeCandidate_nonsingular h hx)

@[simp] theorem veluThreeCandidatePointFun_zero :
    veluThreeCandidatePointFun 0 = 0 :=
  rfl

@[simp] theorem veluThreeCandidatePointFun_threeTorsionOrigin :
    veluThreeCandidatePointFun threeTorsionOrigin = 0 := by
  simp [veluThreeCandidatePointFun, threeTorsionOrigin]
  rfl

@[simp] theorem veluThreeCandidatePointFun_neg_threeTorsionOrigin :
    veluThreeCandidatePointFun (-threeTorsionOrigin) = 0 := by
  rw [threeTorsionOrigin,
    WeierstrassCurve.Affine.Point.neg_some]
  simp [veluThreeCandidatePointFun]
  rfl

/-- The zero fibre of the explicit point function is exactly the visible
three-element set.  This is not a group-kernel theorem until additivity is
proved. -/
theorem veluThreeCandidatePointFun_eq_zero_iff
    (P : threeTorsionCurve.toAffine.Point) :
    veluThreeCandidatePointFun P = 0 ↔
      P = 0 ∨ P = threeTorsionOrigin ∨
        P = -threeTorsionOrigin := by
  cases P with
  | zero =>
      constructor
      · intro
        exact Or.inl rfl
      · intro
        exact veluThreeCandidatePointFun_zero
  | some x y h =>
      by_cases hx : x = 0
      · subst x
        have hcurve := threeTorsionCurve_equation h
        norm_num at hcurve
        have hfactor : y * (y + 7) = 0 := by
          nlinarith
        rcases mul_eq_zero.mp hfactor with hy | hy
        · subst y
          have hP :
              (WeierstrassCurve.Affine.Point.some 0 0 h :
                threeTorsionCurve.toAffine.Point) =
                threeTorsionOrigin := by
            apply WeierstrassCurve.Affine.Point.some_eq_some
              threeTorsionCurve <;> rfl
          rw [hP]
          simp
        · have hy' : y = -7 := by linarith
          subst y
          have hP :
              (WeierstrassCurve.Affine.Point.some 0 (-7) h :
                threeTorsionCurve.toAffine.Point) =
                -threeTorsionOrigin := by
            rw [threeTorsionOrigin,
              WeierstrassCurve.Affine.Point.neg_some]
            apply WeierstrassCurve.Affine.Point.some_eq_some
              threeTorsionCurve
            · rfl
            · norm_num [WeierstrassCurve.Affine.negY,
                threeTorsionCurve]
          rw [hP]
          simp
      · simp [veluThreeCandidatePointFun, hx,
          threeTorsionOrigin,
          WeierstrassCurve.Affine.Point.neg_some]

/-! ## The candidate target has no rational three-torsion -/

/-- Evaluation of the third division polynomial on the candidate target. -/
theorem eval_veluThreeCandidateTarget_Psi_three (x : ℚ) :
    Polynomial.eval x veluThreeCandidateTarget.Ψ₃ =
      (3 * x + 16) * (x ^ 3 - 252 * x - 1771) := by
  simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat,
    veluThreeCandidateTarget, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  ring

private theorem cubic_threeKernel_ne_zero (x : ℚ) :
    x ^ 3 - 252 * x - 1771 ≠ 0 := by
  intro hx
  let p : Polynomial ℤ :=
    Polynomial.X ^ 3 - Polynomial.C 252 * Polynomial.X -
      Polynomial.C 1771
  have hroot : Polynomial.aeval x p = 0 := by
    simpa [p, map_ofNat] using hx
  have hdeg : p.natDegree = 3 := by
    dsimp only [p]
    compute_degree <;> norm_num
  have hlc : p.leadingCoeff = 1 := by
    rw [Polynomial.leadingCoeff, hdeg]
    norm_num [p, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_one]
  have hd : ((IsFractionRing.den ℤ x : ℤ)) ∣ 1 := by
    simpa only [hlc] using den_dvd_of_is_root hroot
  have hdAbs :
      ((IsFractionRing.den ℤ x : ℤ)).natAbs = 1 := by
    simpa using (Int.natAbs_dvd_natAbs.mpr hd)
  have hdCases :
      (IsFractionRing.den ℤ x : ℤ) = 1 ∨
        (IsFractionRing.den ℤ x : ℤ) = -1 := by
    rcases Int.natAbs_eq
      (IsFractionRing.den ℤ x : ℤ) with h | h
    · left
      rw [hdAbs] at h
      norm_num at h ⊢
      exact h
    · right
      rw [hdAbs] at h
      norm_num at h ⊢
      exact h
  have hnoRoot :
      ∀ z : ZMod 13,
        z ^ 3 - 252 * z - 1771 ≠ 0 := by
    decide
  have noIntRoot (m : ℤ) :
      m ^ 3 - 252 * m - 1771 ≠ 0 := by
    intro hm
    have hmMod :=
      congrArg (fun z : ℤ ↦ (z : ZMod 13)) hm
    push_cast at hmMod
    exact hnoRoot _ hmMod
  have hrepr := IsFractionRing.mk'_num_den' ℤ x
  rcases hdCases with hdOne | hdNeg
  · rw [hdOne] at hrepr
    norm_num at hrepr
    apply noIntRoot (IsFractionRing.num ℤ x)
    rw [← hrepr] at hx
    exact_mod_cast hx
  · rw [hdNeg] at hrepr
    norm_num at hrepr
    apply noIntRoot (-IsFractionRing.num ℤ x)
    rw [← hrepr] at hx
    have hdiv :
        (IsFractionRing.num ℤ x : ℚ) / (-1 : ℚ) =
          -(IsFractionRing.num ℤ x : ℚ) := by
      ring
    rw [hdiv] at hx
    exact_mod_cast hx

private theorem linear_threeKernel_impossible
    {x y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular x y)
    (hx : 3 * x + 16 = 0) : False := by
  have hx' : x = -16 / 3 := by linarith
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [veluThreeCandidateTarget, hx'] at hcurve
  nlinarith [sq_nonneg (6 * y - 43)]

/-- The candidate target has no nonidentity rational point killed by three. -/
theorem veluThreeCandidateTarget_eq_zero_of_three_nsmul_eq_zero
    (P : veluThreeCandidateTarget.toAffine.Point)
    (hP : (3 : ℕ) • P = 0) :
    P = 0 := by
  cases P with
  | zero => rfl
  | some x y hxy =>
      exfalso
      have hroot :=
        (MazurTorsion.ThreeTorsion.three_nsmul_some_eq_zero_iff
          veluThreeCandidateTarget hxy).mp hP
      rw [eval_veluThreeCandidateTarget_Psi_three] at hroot
      rcases mul_eq_zero.mp hroot with hlinear | hcubic
      · exact linear_threeKernel_impossible hxy hlinear
      · exact cubic_threeKernel_ne_zero x hcubic

end MazurTorsion.OrderThirtyFive

end

/- Source: MazurTorsion/NumberTheory/OrderThirtyFiveThreeIsogenyDual.lean -/

section

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# The equation-checked dual three-isogeny candidate at level 35

This file constructs the rational point function in the direction opposite to
`OrderThirtyFive.veluThreeCandidatePointFun`.  In completed-square
coordinates, the two fixed curves are

```
z² = 4x³ + 16x² + 56x + 49,
Z² = 4X³ + 16X² - 504X - 3115.
```

The dual kernel has linear abscissa factor `3X + 16`; it has no rational
affine point on the target curve.  Consequently the dual formulas define a
total rational point function.  We also check that its composite with the
first candidate is multiplication by three on the actual affine point group.

The declarations remain point-function candidates: the exact Mathlib pin has
no bundled elliptic-curve morphism API, and this file does not assert
additivity of either point function in isolation.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve.Affine

/-- The rational linear factor cutting out the geometric dual kernel. -/
def veluThreeDualCandidateKernel (X : ℚ) : ℚ :=
  3 * X + 16

/-- The candidate dual abscissa. -/
def veluThreeDualCandidateX (X : ℚ) : ℚ :=
  (X ^ 3 - 252 * X - 1771) /
    veluThreeDualCandidateKernel X ^ 2

/-- The completed-ordinate multiplier for the candidate dual map. -/
def veluThreeDualCandidateDifferential (X : ℚ) : ℚ :=
  (X ^ 3 + 16 * X ^ 2 + 252 * X + 2198) /
    veluThreeDualCandidateKernel X ^ 3

/-- The candidate dual ordinate. -/
def veluThreeDualCandidateY (X Y : ℚ) : ℚ :=
  ((2 * Y + 4 * X + 7) *
      veluThreeDualCandidateDifferential X -
    4 * veluThreeDualCandidateX X - 7) / 2

/-- The completed-square polynomial of the source curve. -/
private def sourceCompletedPolynomial (x : ℚ) : ℚ :=
  4 * x ^ 3 + 16 * x ^ 2 + 56 * x + 49

/-- The completed-square polynomial of the candidate target. -/
private def targetCompletedPolynomial (X : ℚ) : ℚ :=
  4 * X ^ 3 + 16 * X ^ 2 - 504 * X - 3115

/-- The dual formulas carry the target completed-square equation to the
source completed-square equation. -/
private theorem veluThreeDualCandidate_completedSquare (X : ℚ)
    (hkernel : veluThreeDualCandidateKernel X ≠ 0) :
    veluThreeDualCandidateDifferential X ^ 2 *
        targetCompletedPolynomial X =
      sourceCompletedPolynomial (veluThreeDualCandidateX X) := by
  let K : ℚ := 3 * X + 16
  let A : ℚ := X ^ 3 - 252 * X - 1771
  let B : ℚ := X ^ 3 + 16 * X ^ 2 + 252 * X + 2198
  let T : ℚ := 4 * X ^ 3 + 16 * X ^ 2 - 504 * X - 3115
  have hK : K ≠ 0 := by
    simpa only [K, veluThreeDualCandidateKernel] using hkernel
  change (B / K ^ 3) ^ 2 * T =
    4 * (A / K ^ 2) ^ 3 + 16 * (A / K ^ 2) ^ 2 +
      56 * (A / K ^ 2) + 49
  field_simp [hK]
  dsimp only [A, B, K, T]
  ring

/-- No rational affine target point lies on the denominator of the dual
candidate. -/
theorem veluThreeDualCandidateKernel_ne_zero
    {X Y : ℚ}
    (hP : (veluThreeCandidateTarget.toAffine).Nonsingular X Y) :
    veluThreeDualCandidateKernel X ≠ 0 := by
  intro hkernel
  have hX : X = -16 / 3 := by
    dsimp only [veluThreeDualCandidateKernel] at hkernel
    linarith
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [veluThreeCandidateTarget, hX] at hcurve
  nlinarith [sq_nonneg (6 * Y - 43)]

/-- Direct substitution verifies that the dual formulas land on the source
curve. -/
theorem veluThreeDualCandidate_equation {X Y : ℚ}
    (hkernel : veluThreeDualCandidateKernel X ≠ 0)
    (hcurve : Y ^ 2 + 4 * X * Y + 7 * Y =
      X ^ 3 - 140 * X - 791) :
    threeTorsionCurve.toAffine.Equation
      (veluThreeDualCandidateX X)
      (veluThreeDualCandidateY X Y) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [threeTorsionCurve]
  have hsource :
      (2 * Y + 4 * X + 7) ^ 2 =
        targetCompletedPolynomial X := by
    dsimp only [targetCompletedPolynomial]
    nlinarith
  have htarget :
      (2 * veluThreeDualCandidateY X Y +
          4 * veluThreeDualCandidateX X + 7) ^ 2 =
        sourceCompletedPolynomial (veluThreeDualCandidateX X) := by
    rw [← veluThreeDualCandidate_completedSquare X hkernel, ← hsource]
    simp only [veluThreeDualCandidateY]
    ring
  dsimp only [sourceCompletedPolynomial] at htarget
  nlinarith

/-- The affine value of the dual candidate. -/
noncomputable def veluThreeDualCandidatePoint
    {X Y : ℚ}
    (hP : (veluThreeCandidateTarget.toAffine).Nonsingular X Y) :
    threeTorsionCurve.toAffine.Point :=
  .some (veluThreeDualCandidateX X)
    (veluThreeDualCandidateY X Y)
    (threeTorsionCurve.toAffine.equation_iff_nonsingular.mp
      (veluThreeDualCandidate_equation
        (veluThreeDualCandidateKernel_ne_zero hP) (by
        have heq := hP.1
        rw [WeierstrassCurve.Affine.equation_iff] at heq
        norm_num [veluThreeCandidateTarget] at heq ⊢
        simpa only [sub_eq_add_neg] using heq)))

/-- The total dual candidate on rational points.  The rational dual kernel is
trivial, so every nonzero rational point uses the affine formula. -/
noncomputable def veluThreeDualCandidatePointFun :
    (veluThreeCandidateTarget.toAffine).Point →
      threeTorsionCurve.toAffine.Point
  | .zero => .zero
  | .some _ _ hP => veluThreeDualCandidatePoint hP

@[simp] theorem veluThreeDualCandidatePointFun_zero :
    veluThreeDualCandidatePointFun 0 = 0 :=
  rfl

/-! ## The composite rational functions -/

/-- The completed-ordinate multiplier of the first candidate. -/
private def veluThreeCandidateDifferential (x : ℚ) : ℚ :=
  (x ^ 3 - 28 * x - 98) / x ^ 3

/-- The non-visible factor in the source third-division polynomial. -/
private def sourceThreeDivisionCofactor (x : ℚ) : ℚ :=
  (3 * x + 7) * (x ^ 2 + 3 * x + 21)

/-- The source third-division polynomial, in its fixed-model
factorization. -/
private def sourceThreeDivisionPolynomial (x : ℚ) : ℚ :=
  x * sourceThreeDivisionCofactor x

/-- The numerator of the multiplication-by-three abscissa. -/
private def tripleAbscissaNumerator (x : ℚ) : ℚ :=
  x ^ 9 - 168 * x ^ 7 - 1624 * x ^ 6 - 4704 * x ^ 5 -
    4116 * x ^ 4 + 29155 * x ^ 3 + 115248 * x ^ 2 +
    201684 * x + 117649

/-- The multiplication-by-three abscissa rational function. -/
private def tripleAbscissa (x : ℚ) : ℚ :=
  tripleAbscissaNumerator x / sourceThreeDivisionPolynomial x ^ 2

/-- The degree-six factor in the multiplication-by-three completed
ordinate. -/
private def tripleDifferentialCofactor (x : ℚ) : ℚ :=
  x ^ 6 + 9 * x ^ 5 + 280 * x ^ 4 + 1295 * x ^ 3 +
    3430 * x ^ 2 + 4459 * x + 2401

/-- The numerator of the multiplication-by-three completed-ordinate
multiplier. -/
private def tripleDifferentialNumerator (x : ℚ) : ℚ :=
  (x ^ 3 - 28 * x - 98) *
    (x ^ 3 + 7 * x ^ 2 - 7 * x + 49) *
      tripleDifferentialCofactor x

/-- The multiplication-by-three completed-ordinate multiplier. -/
private def tripleDifferential (x : ℚ) : ℚ :=
  tripleDifferentialNumerator x / sourceThreeDivisionPolynomial x ^ 3

/-- The first candidate acts diagonally on the completed ordinate. -/
private theorem veluThreeCandidate_completed {x y : ℚ}
    (hx : x ≠ 0) :
    2 * veluThreeCandidateY x y +
        4 * veluThreeCandidateX x + 7 =
      (2 * y + 4 * x + 7) * veluThreeCandidateDifferential x := by
  simp only [veluThreeCandidateY, veluThreeCandidateX,
    veluThreeCandidateDifferential]
  field_simp [hx]
  ring

/-- Pulling back the dual denominator gives the non-visible source
third-division factor. -/
private theorem veluThreeDualCandidateKernel_candidateX {x : ℚ}
    (hx : x ≠ 0) :
    veluThreeDualCandidateKernel (veluThreeCandidateX x) =
      sourceThreeDivisionCofactor x / x ^ 2 := by
  simp only [veluThreeDualCandidateKernel, veluThreeCandidateX,
    sourceThreeDivisionCofactor]
  field_simp [hx]
  ring

/-- Pulling back the dual abscissa gives the standard tripling rational
function. -/
private theorem veluThreeDualCandidateX_candidateX {x : ℚ}
    (hx : x ≠ 0)
    (hcofactor : sourceThreeDivisionCofactor x ≠ 0) :
    veluThreeDualCandidateX (veluThreeCandidateX x) =
      tripleAbscissa x := by
  simp only [veluThreeDualCandidateX, tripleAbscissa]
  rw [veluThreeDualCandidateKernel_candidateX hx]
  simp only [veluThreeCandidateX, sourceThreeDivisionPolynomial]
  field_simp [hx, hcofactor]
  simp only [tripleAbscissaNumerator]
  ring

/-- Pulling back the dual completed-ordinate multiplier gives the remaining
factor in the tripling multiplier. -/
private theorem veluThreeDualCandidateDifferential_candidateX {x : ℚ}
    (hx : x ≠ 0)
    (hcofactor : sourceThreeDivisionCofactor x ≠ 0) :
    veluThreeDualCandidateDifferential (veluThreeCandidateX x) =
      (x ^ 3 + 7 * x ^ 2 - 7 * x + 49) *
          tripleDifferentialCofactor x /
        sourceThreeDivisionCofactor x ^ 3 := by
  simp only [veluThreeDualCandidateDifferential]
  rw [veluThreeDualCandidateKernel_candidateX hx]
  simp only [veluThreeCandidateX]
  field_simp [hx, hcofactor]
  simp only [tripleDifferentialCofactor]
  ring

/-- The completed ordinate of the two candidate maps composes to the
tripling rational function. -/
private theorem veluThreeDualCandidateY_candidate_completed {x y : ℚ}
    (hx : x ≠ 0)
    (hcofactor : sourceThreeDivisionCofactor x ≠ 0) :
    2 * veluThreeDualCandidateY
          (veluThreeCandidateX x) (veluThreeCandidateY x y) +
        4 * veluThreeDualCandidateX (veluThreeCandidateX x) + 7 =
      (2 * y + 4 * x + 7) * tripleDifferential x := by
  calc
    2 * veluThreeDualCandidateY
          (veluThreeCandidateX x) (veluThreeCandidateY x y) +
        4 * veluThreeDualCandidateX (veluThreeCandidateX x) + 7 =
      (2 * veluThreeCandidateY x y +
          4 * veluThreeCandidateX x + 7) *
        veluThreeDualCandidateDifferential (veluThreeCandidateX x) := by
          simp only [veluThreeDualCandidateY]
          ring
    _ = (2 * y + 4 * x + 7) * tripleDifferential x := by
      rw [veluThreeCandidate_completed hx,
        veluThreeDualCandidateDifferential_candidateX hx hcofactor]
      simp only [veluThreeCandidateDifferential,
        tripleDifferential, tripleDifferentialNumerator,
        sourceThreeDivisionPolynomial]
      field_simp [hx, hcofactor]

/-! ## Identification with multiplication by three -/

/-- The abscissa of the double of a source point. -/
private def doubleAbscissa (x : ℚ) : ℚ :=
  x * (x ^ 3 - 28 * x - 98) / sourceCompletedPolynomial x

/-- The completed-ordinate multiplier of doubling on the source. -/
private def doubleDifferential (x : ℚ) : ℚ :=
  (2 * x ^ 6 + 16 * x ^ 5 + 140 * x ^ 4 + 490 * x ^ 3 -
      1372 * x - 2401) /
    sourceCompletedPolynomial x ^ 2

/-- The normalized completed slope of the secant from a point to its
double. -/
private def tripleSecantSlopeFactor (x : ℚ) : ℚ :=
  2 * (7 * x ^ 6 + 56 * x ^ 5 + 282 * x ^ 4 + 847 * x ^ 3 +
      2352 * x ^ 2 + 3430 * x + 2401) /
    (sourceThreeDivisionPolynomial x * sourceCompletedPolynomial x)

private theorem source_completed_equation {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y) :
    (2 * y + 4 * x + 7) ^ 2 = sourceCompletedPolynomial x := by
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve, sourceCompletedPolynomial] at hcurve ⊢
  nlinarith

private theorem source_eq_zero_of_two_nsmul_eq_zero
    (P : threeTorsionCurve.toAffine.Point)
    (hP : (2 : ℕ) • P = 0) :
    P = 0 := by
  apply threeTorsionEquiv.injective
  rw [map_zero]
  apply eq_zero_of_two_nsmul_eq_zero
  rw [← map_nsmul, hP, map_zero]

private theorem sourceThreeDivisionCofactor_ne_zero
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y) :
    sourceThreeDivisionCofactor x ≠ 0 := by
  apply mul_ne_zero
  · intro hlinear
    have hx : x = -7 / 3 := by linarith
    have hcompleted := source_completed_equation hP
    norm_num [sourceCompletedPolynomial, hx] at hcompleted
    nlinarith [sq_nonneg (2 * y + 4 * x + 7)]
  · have hpositive : 0 < x ^ 2 + 3 * x + 21 := by
      nlinarith [sq_nonneg (2 * x + 3)]
    exact ne_of_gt hpositive

private theorem sourceThreeDivisionPolynomial_ne_zero
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    sourceThreeDivisionPolynomial x ≠ 0 :=
  mul_ne_zero hx (sourceThreeDivisionCofactor_ne_zero hP)

private theorem eval_source_Psi_three (x : ℚ) :
    Polynomial.eval x threeTorsionCurve.Ψ₃ =
      sourceThreeDivisionPolynomial x := by
  simp only [WeierstrassCurve.Ψ₃, Polynomial.eval_add,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat, threeTorsionCurve,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈,
    sourceThreeDivisionPolynomial, sourceThreeDivisionCofactor]
  ring

private theorem source_three_nsmul_some_ne_zero
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP ≠ 0 := by
  intro hthree
  have hroot :=
    (MazurTorsion.ThreeTorsion.three_nsmul_some_eq_zero_iff
      threeTorsionCurve hP).mp hthree
  apply sourceThreeDivisionPolynomial_ne_zero hP hx
  rwa [eval_source_Psi_three] at hroot

private theorem addX_eq_completed
    (x₁ x₂ ℓ : ℚ) :
    threeTorsionCurve.toAffine.addX x₁ x₂ ℓ =
      (2 * ℓ + 4) ^ 2 / 4 - 4 - x₁ - x₂ := by
  simp only [WeierstrassCurve.Affine.addX, threeTorsionCurve]
  ring

private theorem addY_completed
    (x₁ x₂ y₁ ℓ : ℚ) :
    2 * threeTorsionCurve.toAffine.addY x₁ x₂ y₁ ℓ +
        4 * threeTorsionCurve.toAffine.addX x₁ x₂ ℓ + 7 =
      -(2 * y₁ + 4 * x₁ + 7) -
        (2 * ℓ + 4) *
          (threeTorsionCurve.toAffine.addX x₁ x₂ ℓ - x₁) := by
  simp only [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.negY,
    WeierstrassCurve.Affine.addX, threeTorsionCurve]
  ring

private theorem tangent_completed_slope {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hy : y ≠ threeTorsionCurve.toAffine.negY x y) :
    2 * threeTorsionCurve.toAffine.slope x x y y + 4 =
      (2 * y + 4 * x + 7) *
        (6 * x ^ 2 + 16 * x + 28) /
          sourceCompletedPolynomial x := by
  let z : ℚ := 2 * y + 4 * x + 7
  let A : ℚ := 6 * x ^ 2 + 16 * x + 28
  have hz : z ≠ 0 := by
    intro hz
    apply hy
    simp only [threeTorsionCurve, WeierstrassCurve.Affine.negY]
    dsimp only [z] at hz
    linarith
  have hcompleted := source_completed_equation hP
  have hD : sourceCompletedPolynomial x ≠ 0 := by
    rw [← hcompleted]
    exact pow_ne_zero 2 hz
  have hden : y - threeTorsionCurve.toAffine.negY x y = z := by
    simp only [threeTorsionCurve, WeierstrassCurve.Affine.negY]
    dsimp only [z]
    ring
  rw [threeTorsionCurve.toAffine.slope_of_Y_ne rfl hy, hden]
  norm_num [threeTorsionCurve]
  change 2 * ((3 * x ^ 2 - 4 * y) / z) + 4 = z * A /
    sourceCompletedPolynomial x
  field_simp [hz, hD]
  dsimp only [z, A, sourceCompletedPolynomial] at hcompleted ⊢
  linear_combination
    -(6 * x ^ 2 + 16 * x + 28) * hcompleted

private theorem double_abscissa_identity {x z : ℚ}
    (hcompleted : z ^ 2 = sourceCompletedPolynomial x)
    (hD : sourceCompletedPolynomial x ≠ 0) :
    (z * ((6 * x ^ 2 + 16 * x + 28) /
        sourceCompletedPolynomial x)) ^ 2 / 4 - 4 - x - x =
      doubleAbscissa x := by
  simp only [doubleAbscissa]
  field_simp [hD]
  dsimp only [sourceCompletedPolynomial] at hcompleted ⊢
  linear_combination
    (6 * x ^ 2 + 16 * x + 28) ^ 2 *
      hcompleted

private theorem double_completed_identity (x : ℚ)
    (hD : sourceCompletedPolynomial x ≠ 0) :
    -1 - (6 * x ^ 2 + 16 * x + 28) /
        sourceCompletedPolynomial x * (doubleAbscissa x - x) =
      doubleDifferential x := by
  simp only [doubleAbscissa, doubleDifferential]
  field_simp [hD]
  simp only [sourceCompletedPolynomial]
  ring

private theorem double_abscissa_difference (x : ℚ)
    (hD : sourceCompletedPolynomial x ≠ 0) :
    x - doubleAbscissa x =
      sourceThreeDivisionPolynomial x / sourceCompletedPolynomial x := by
  simp only [doubleAbscissa]
  field_simp [hD]
  simp only [sourceCompletedPolynomial,
    sourceThreeDivisionPolynomial, sourceThreeDivisionCofactor]
  ring

private theorem double_differential_difference (x : ℚ)
    (hD : sourceCompletedPolynomial x ≠ 0) :
    1 - doubleDifferential x =
      2 * (7 * x ^ 6 + 56 * x ^ 5 + 282 * x ^ 4 + 847 * x ^ 3 +
        2352 * x ^ 2 + 3430 * x + 2401) /
          sourceCompletedPolynomial x ^ 2 := by
  simp only [doubleDifferential]
  field_simp [hD]
  simp only [sourceCompletedPolynomial]
  ring

private theorem secant_completed_slope_identity (x : ℚ)
    (hD : sourceCompletedPolynomial x ≠ 0)
    (hψ : sourceThreeDivisionPolynomial x ≠ 0) :
    (1 - doubleDifferential x) /
        (x - doubleAbscissa x) =
      tripleSecantSlopeFactor x := by
  rw [double_differential_difference x hD,
    double_abscissa_difference x hD]
  simp only [tripleSecantSlopeFactor]
  field_simp [hD, hψ]

private theorem triple_abscissa_identity {x z : ℚ}
    (hcompleted : z ^ 2 = sourceCompletedPolynomial x)
    (hD : sourceCompletedPolynomial x ≠ 0)
    (hψ : sourceThreeDivisionPolynomial x ≠ 0) :
    (z * tripleSecantSlopeFactor x) ^ 2 / 4 - 4 - x -
        doubleAbscissa x = tripleAbscissa x := by
  simp only [tripleSecantSlopeFactor, doubleAbscissa, tripleAbscissa]
  field_simp [hD, hψ]
  dsimp only [sourceCompletedPolynomial,
    sourceThreeDivisionPolynomial, sourceThreeDivisionCofactor,
    tripleAbscissaNumerator] at hcompleted ⊢
  linear_combination
    4 * (7 * x ^ 6 + 56 * x ^ 5 + 282 * x ^ 4 + 847 * x ^ 3 +
      2352 * x ^ 2 + 3430 * x + 2401) ^ 2 *
        hcompleted

private theorem triple_completed_identity (x z : ℚ)
    (hD : sourceCompletedPolynomial x ≠ 0)
    (hψ : sourceThreeDivisionPolynomial x ≠ 0) :
    -z - z * tripleSecantSlopeFactor x * (tripleAbscissa x - x) =
      z * tripleDifferential x := by
  simp only [tripleSecantSlopeFactor, tripleAbscissa,
    tripleDifferential]
  field_simp [hD, hψ]
  simp only [sourceCompletedPolynomial,
    sourceThreeDivisionPolynomial, sourceThreeDivisionCofactor,
    tripleAbscissaNumerator, tripleDifferentialNumerator,
    tripleDifferentialCofactor]
  ring

/-- Away from the visible three-element fibre, the two equation-checked
candidate point functions compose to actual multiplication by three in
Mathlib's affine point group. -/
theorem veluThreeDualCandidatePointFun_candidate_some
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    veluThreeDualCandidatePointFun
        (veluThreeCandidatePointFun
          (WeierstrassCurve.Affine.Point.some x y hP)) =
      (3 : ℕ) • WeierstrassCurve.Affine.Point.some x y hP := by
  let P : threeTorsionCurve.toAffine.Point :=
    WeierstrassCurve.Affine.Point.some x y hP
  let z : ℚ := 2 * y + 4 * x + 7
  let ℓ₂ : ℚ := threeTorsionCurve.toAffine.slope x x y y
  let x₂ : ℚ := threeTorsionCurve.toAffine.addX x x ℓ₂
  let y₂ : ℚ := threeTorsionCurve.toAffine.addY x x y ℓ₂
  have hP_ne : P ≠ 0 :=
    WeierstrassCurve.Affine.Point.some_ne_zero hP
  have htwo_ne : (2 : ℕ) • P ≠ 0 := by
    intro htwo
    exact hP_ne (source_eq_zero_of_two_nsmul_eq_zero P htwo)
  have hy : y ≠ threeTorsionCurve.toAffine.negY x y := by
    intro hy
    apply htwo_ne
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy
  have hP₂ : threeTorsionCurve.toAffine.Nonsingular x₂ y₂ :=
    nonsingular_add hP hP (fun hxy => hy hxy.2)
  have hdouble :
      (2 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
    rw [two_nsmul]
    exact WeierstrassCurve.Affine.Point.add_self_of_Y_ne hy
  have hcompleted : z ^ 2 = sourceCompletedPolynomial x := by
    simpa only [z] using source_completed_equation hP
  have hz : z ≠ 0 := by
    intro hz
    apply hy
    simp only [threeTorsionCurve, WeierstrassCurve.Affine.negY]
    dsimp only [z] at hz
    linarith
  have hD : sourceCompletedPolynomial x ≠ 0 := by
    rw [← hcompleted]
    exact pow_ne_zero 2 hz
  have htangent :
      2 * ℓ₂ + 4 =
        z * ((6 * x ^ 2 + 16 * x + 28) /
          sourceCompletedPolynomial x) := by
    simpa only [ℓ₂, z, mul_div_assoc] using
      tangent_completed_slope hP hy
  have hx₂ : x₂ = doubleAbscissa x := by
    calc
      x₂ = (2 * ℓ₂ + 4) ^ 2 / 4 - 4 - x - x :=
        addX_eq_completed x x ℓ₂
      _ = (z * ((6 * x ^ 2 + 16 * x + 28) /
          sourceCompletedPolynomial x)) ^ 2 / 4 - 4 - x - x := by
            rw [htangent]
      _ = doubleAbscissa x :=
        double_abscissa_identity hcompleted hD
  have hz₂ : 2 * y₂ + 4 * x₂ + 7 = z * doubleDifferential x := by
    calc
      2 * y₂ + 4 * x₂ + 7 =
          -z - (2 * ℓ₂ + 4) * (x₂ - x) := by
        simpa only [x₂, y₂, z, ℓ₂] using
          addY_completed x x y ℓ₂
      _ = -z -
          (z * ((6 * x ^ 2 + 16 * x + 28) /
            sourceCompletedPolynomial x)) * (doubleAbscissa x - x) := by
        rw [htangent, hx₂]
      _ = z * (-1 - (6 * x ^ 2 + 16 * x + 28) /
          sourceCompletedPolynomial x * (doubleAbscissa x - x)) := by
        ring
      _ = z * doubleDifferential x := by
        rw [double_completed_identity x hD]
  have hψ : sourceThreeDivisionPolynomial x ≠ 0 :=
    sourceThreeDivisionPolynomial_ne_zero hP hx
  have hthree_ne : (3 : ℕ) • P ≠ 0 := by
    simpa only [P] using source_three_nsmul_some_ne_zero hP hx
  have hsec : x ≠ x₂ := by
    intro hxx₂
    rcases (WeierstrassCurve.Affine.Point.X_eq_iff).mp hxx₂ with
      heq | heq
    · have htwo_eq : (2 : ℕ) • P = P :=
        hdouble.trans heq.symm
      apply hP_ne
      calc
        P = (2 : ℕ) • P - P := by abel
        _ = P - P := by rw [htwo_eq]
        _ = 0 := sub_self P
    · apply hthree_ne
      calc
        (3 : ℕ) • P = P + (2 : ℕ) • P := by abel
        _ = P + WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
          rw [hdouble]
        _ = 0 := (add_eq_zero_iff_eq_neg).2 heq
  let ℓ₃ : ℚ := threeTorsionCurve.toAffine.slope x x₂ y y₂
  have hsecant :
      2 * ℓ₃ + 4 = z * tripleSecantSlopeFactor x := by
    have hcoordinateDifference :
        2 * (y - y₂) + 4 * (x - x₂) =
          z - (2 * y₂ + 4 * x₂ + 7) := by
      dsimp only [z]
      ring
    dsimp only [ℓ₃]
    rw [threeTorsionCurve.toAffine.slope_of_X_ne hsec]
    calc
      2 * ((y - y₂) / (x - x₂)) + 4 =
          (2 * (y - y₂) + 4 * (x - x₂)) / (x - x₂) := by
        field_simp [sub_ne_zero.mpr hsec]
      _ = (z - (2 * y₂ + 4 * x₂ + 7)) / (x - x₂) := by
        rw [hcoordinateDifference]
      _ = (z - z * doubleDifferential x) /
          (x - doubleAbscissa x) := by rw [hz₂, hx₂]
      _ = z * ((1 - doubleDifferential x) /
          (x - doubleAbscissa x)) := by ring
      _ = z * tripleSecantSlopeFactor x := by
        rw [secant_completed_slope_identity x hD hψ]
  have hx₃ :
      threeTorsionCurve.toAffine.addX x x₂ ℓ₃ =
        tripleAbscissa x := by
    calc
      threeTorsionCurve.toAffine.addX x x₂ ℓ₃ =
          (2 * ℓ₃ + 4) ^ 2 / 4 - 4 - x - x₂ :=
        addX_eq_completed x x₂ ℓ₃
      _ = (z * tripleSecantSlopeFactor x) ^ 2 / 4 - 4 - x -
          doubleAbscissa x := by rw [hsecant, hx₂]
      _ = tripleAbscissa x :=
        triple_abscissa_identity hcompleted hD hψ
  have hz₃ :
      2 * threeTorsionCurve.toAffine.addY x x₂ y ℓ₃ +
          4 * threeTorsionCurve.toAffine.addX x x₂ ℓ₃ + 7 =
        z * tripleDifferential x := by
    calc
      2 * threeTorsionCurve.toAffine.addY x x₂ y ℓ₃ +
          4 * threeTorsionCurve.toAffine.addX x x₂ ℓ₃ + 7 =
        -z - (2 * ℓ₃ + 4) *
          (threeTorsionCurve.toAffine.addX x x₂ ℓ₃ - x) := by
            simpa only [z] using addY_completed x x₂ y ℓ₃
      _ = -z - z * tripleSecantSlopeFactor x *
          (tripleAbscissa x - x) := by rw [hsecant, hx₃]
      _ = z * tripleDifferential x :=
        triple_completed_identity x z hD hψ
  have htriple :
      (3 : ℕ) • P =
        WeierstrassCurve.Affine.Point.some
          (threeTorsionCurve.toAffine.addX x x₂ ℓ₃)
          (threeTorsionCurve.toAffine.addY x x₂ y ℓ₃)
          (nonsingular_add hP hP₂ (fun hxy => hsec hxy.1)) := by
    calc
      (3 : ℕ) • P = P + (2 : ℕ) • P := by abel
      _ = P + WeierstrassCurve.Affine.Point.some x₂ y₂ hP₂ := by
        rw [hdouble]
      _ = WeierstrassCurve.Affine.Point.some _ _ _ :=
        WeierstrassCurve.Affine.Point.add_of_X_ne hsec
  rw [htriple]
  simp only [veluThreeCandidatePointFun]
  rw [dif_neg hx]
  simp only [veluThreeDualCandidatePointFun,
    veluThreeDualCandidatePoint,
    WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · exact (veluThreeDualCandidateX_candidateX hx
      (sourceThreeDivisionCofactor_ne_zero hP)).trans hx₃.symm
  · have hdual := veluThreeDualCandidateY_candidate_completed
      (y := y) hx (sourceThreeDivisionCofactor_ne_zero hP)
    rw [← hz₃] at hdual
    have hxdual := veluThreeDualCandidateX_candidateX hx
      (sourceThreeDivisionCofactor_ne_zero hP)
    linarith

private theorem three_nsmul_eq_zero_of_candidate_eq_zero
    (P : threeTorsionCurve.toAffine.Point)
    (hP : veluThreeCandidatePointFun P = 0) :
    (3 : ℕ) • P = 0 := by
  rcases (veluThreeCandidatePointFun_eq_zero_iff P).mp hP with
    rfl | rfl | rfl
  · simp
  · rw [← addOrderOf_threeTorsionOrigin]
    exact addOrderOf_nsmul_eq_zero threeTorsionOrigin
  · have hT : (3 : ℕ) • threeTorsionOrigin = 0 := by
      rw [← addOrderOf_threeTorsionOrigin]
      exact addOrderOf_nsmul_eq_zero threeTorsionOrigin
    simp [hT]

/-- The two equation-checked point functions compose to multiplication by
three on every rational source point.  This is a statement about the
composite only; it does not assert that either function is additive. -/
theorem veluThreeDualCandidatePointFun_candidate
    (P : threeTorsionCurve.toAffine.Point) :
    veluThreeDualCandidatePointFun (veluThreeCandidatePointFun P) =
      (3 : ℕ) • P := by
  cases P with
  | zero => rfl
  | some x y hP =>
      by_cases hx : x = 0
      · have hcandidate :
            veluThreeCandidatePointFun
              (WeierstrassCurve.Affine.Point.some x y hP) = 0 := by
          simp [veluThreeCandidatePointFun, hx]
          rfl
        rw [hcandidate, veluThreeDualCandidatePointFun_zero,
          three_nsmul_eq_zero_of_candidate_eq_zero _ hcandidate]
      · exact veluThreeDualCandidatePointFun_candidate_some hP hx

end MazurTorsion.OrderThirtyFive

end

/- Source: MazurTorsion/NumberTheory/RatNorthcott.lean -/

section

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Northcott's property for the rational logarithmic height

The logarithmic height of a rational number is the logarithm of the maximum of the absolute
value of its normalized numerator and its positive denominator. Consequently, a height bound
places the numerator and denominator in finite integer intervals. This file records that elementary
rational specialization of Northcott's theorem.
-/

section

namespace MazurTorsion

open Height

/-- The rational numbers of logarithmic height at most `B` form a finite set. -/
theorem finite_rat_logHeight₁_le (B : ℝ) :
    {q : ℚ | logHeight₁ q ≤ B}.Finite := by
  let N := Nat.ceil (Real.exp B)
  let encode : ℚ → ℤ × ℕ := fun q => (q.num, q.den)
  let box : Set (ℤ × ℕ) :=
    Set.Icc (-(N : ℤ)) (N : ℤ) ×ˢ Set.Icc 0 N
  have hbox : box.Finite := by
    exact (Set.finite_Icc (-(N : ℤ)) (N : ℤ)).prod (Set.finite_Icc 0 N)
  have himage : encode '' {q : ℚ | logHeight₁ q ≤ B} ⊆ box := by
    rintro p ⟨q, hq, rfl⟩
    have hmax_real : (max q.num.natAbs q.den : ℝ) ≤ Real.exp B := by
      apply Real.le_exp_of_log_le
      simpa only [Set.mem_setOf_eq, Rat.logHeight₁_eq_log_max, Nat.cast_max] using hq
    have hmax_cast : (max q.num.natAbs q.den : ℝ) ≤ (N : ℝ) :=
      hmax_real.trans (Nat.le_ceil (Real.exp B))
    have hmax : max q.num.natAbs q.den ≤ N := by
      exact_mod_cast hmax_cast
    have hnum : q.num.natAbs ≤ N := le_trans (le_max_left _ _) hmax
    have hden : q.den ≤ N := le_trans (le_max_right _ _) hmax
    have hnum_upper : q.num ≤ (N : ℤ) := by
      exact Int.le_natAbs.trans (Int.ofNat_le.mpr hnum)
    have hnum_lower : -(N : ℤ) ≤ q.num := by
      have hneg : -q.num ≤ (N : ℤ) :=
        Int.le_natAbs.trans (by simpa only [Int.natAbs_neg] using Int.ofNat_le.mpr hnum)
      omega
    exact ⟨⟨hnum_lower, hnum_upper⟩, ⟨Nat.zero_le _, hden⟩⟩
  refine Set.Finite.of_finite_image (hbox.subset himage) ?_
  intro q _ r _ h
  exact Rat.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

/-- The usual logarithmic height on `ℚ` has Northcott's property. -/
instance rationalLogHeightNorthcott : Northcott (logHeight₁ (K := ℚ)) where
  finite_le := finite_rat_logHeight₁_le

end MazurTorsion

end

/- Source: MazurTorsion/NumberTheory/OrderThirtyFiveRankBoundary.lean -/

section

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# The exact order-35 three-descent boundary

The explicit candidate maps are most convenient on the normalized model

`Y² + 4XY + 7Y = X³`.

This file isolates the remaining arithmetic output at precisely the strength
needed downstream: every rational point is represented, modulo three times
the point group, by one of `0`, `(0,0)`, and `(0,-7)`.  From that three-coset
certificate we prove finite generation, Mordell--Weil rank zero, and
finiteness for the fixed model expected to be `X₀(35)/w₅`.

No three-coset certificate is asserted here.  Its proof is the outstanding
fixed-number-field three-isogeny Selmer calculation; all consequences below
are checked consumers of the exact proposition it must establish.
-/

open WeierstrassCurve

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve.Affine

/-- Multiplication by three on the normalized source model. -/
def normalizedThreeRange : AddSubgroup threeTorsionCurve.toAffine.Point :=
  (nsmulAddMonoidHom
    (α := threeTorsionCurve.toAffine.Point) 3).range

/-- Membership in three times the normalized point group is equivalently
membership in the image of the checked dual-after-candidate composite.  This
is the bridge from the explicit point functions to the Selmer coset
boundary; it uses only the proved composite identity, not unproved
additivity of either factor. -/
theorem mem_normalizedThreeRange_iff_exists_candidateComposite
    (P : threeTorsionCurve.toAffine.Point) :
    P ∈ normalizedThreeRange ↔
      ∃ Q : threeTorsionCurve.toAffine.Point,
        P = veluThreeDualCandidatePointFun
          (veluThreeCandidatePointFun Q) := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    rw [veluThreeDualCandidatePointFun_candidate]
    exact hQ.symm
  · rintro ⟨Q, rfl⟩
    refine ⟨Q, ?_⟩
    exact (veluThreeDualCandidatePointFun_candidate Q).symm

/-- The three visible representatives on the normalized source model. -/
def normalizedThreeRepresentative (i : Fin 3) :
    threeTorsionCurve.toAffine.Point :=
  i.val • threeTorsionOrigin

/-- The exact arithmetic output required from the order-35 three-isogeny
descent: the visible rational subgroup exhausts the quotient by three times
the rational point group. -/
def ThreeCosetBound : Prop :=
  ∀ P : threeTorsionCurve.toAffine.Point,
    ∃ i : Fin 3, ∃ Q : threeTorsionCurve.toAffine.Point,
      P = normalizedThreeRepresentative i + (3 : ℕ) • Q

/-- Multiplication by three on the fixed quotient model. -/
def optimalQuotientModelThreeRange :
    AddSubgroup optimalQuotientModel.toAffine.Point :=
  (nsmulAddMonoidHom
    (α := optimalQuotientModel.toAffine.Point) 3).range

/-- The corresponding visible representatives on the selected fixed
model. -/
def optimalQuotientModelThreeRepresentative (i : Fin 3) :
    optimalQuotientModel.toAffine.Point :=
  i.val • modelThreeTorsion

private theorem optimalQuotientModel_cosets_of_normalized
    (hcosets : ThreeCosetBound) :
    ∀ P : optimalQuotientModel.toAffine.Point,
      ∃ i : Fin 3, ∃ Q : optimalQuotientModel.toAffine.Point,
        P = optimalQuotientModelThreeRepresentative i + (3 : ℕ) • Q := by
  intro P
  obtain ⟨i, Q, hQ⟩ := hcosets (threeTorsionEquiv.symm P)
  refine ⟨i, threeTorsionEquiv Q, ?_⟩
  calc
    P = threeTorsionEquiv (threeTorsionEquiv.symm P) := by
      rw [threeTorsionEquiv.apply_symm_apply]
    _ = threeTorsionEquiv
          (normalizedThreeRepresentative i + (3 : ℕ) • Q) := by
      rw [hQ]
    _ = optimalQuotientModelThreeRepresentative i +
          (3 : ℕ) • threeTorsionEquiv Q := by
      simp only [map_add, map_nsmul, normalizedThreeRepresentative,
        optimalQuotientModelThreeRepresentative,
        threeTorsionEquiv_origin]

/-- A normalized three-coset certificate surjects onto the quotient of the
fixed model by multiplication by three. -/
theorem optimalQuotientModel_three_quotient_surjective
    (hcosets : ThreeCosetBound) :
    Function.Surjective
      (fun i : Fin 3 ↦
        QuotientAddGroup.mk' optimalQuotientModelThreeRange
          (optimalQuotientModelThreeRepresentative i)) := by
  intro c
  obtain ⟨P, rfl⟩ :=
    QuotientAddGroup.mk'_surjective optimalQuotientModelThreeRange c
  obtain ⟨i, Q, hP⟩ :=
    optimalQuotientModel_cosets_of_normalized hcosets P
  refine ⟨i, (QuotientAddGroup.mk'_eq_mk'
    optimalQuotientModelThreeRange).mpr ?_⟩
  refine ⟨(3 : ℕ) • Q, ⟨Q, rfl⟩, ?_⟩
  exact hP.symm

/-- A normalized three-coset certificate makes tripling have finite index
on the selected fixed model. -/
theorem optimalQuotientModel_three_finiteIndex_of_cosetBound
    (hcosets : ThreeCosetBound) :
    optimalQuotientModelThreeRange.FiniteIndex := by
  letI : Finite
      (optimalQuotientModel.toAffine.Point ⧸
        optimalQuotientModelThreeRange) :=
    Finite.of_surjective _
      (optimalQuotientModel_three_quotient_surjective hcosets)
  exact AddSubgroup.finiteIndex_of_finite_quotient

/-- The explicit three-fold height descent consumes the normalized Selmer
certificate and proves finite generation of the fixed model. -/
theorem optimalQuotientModel_point_fg_of_cosetBound
    (hcosets : ThreeCosetBound) :
    AddGroup.FG optimalQuotientModel.toAffine.Point :=
  WeierstrassCurve.Affine.fg_point_of_finiteIndex_three
    optimalQuotientModel
    (optimalQuotientModel_three_finiteIndex_of_cosetBound hcosets)

/-- The same certificate gives the sharp index bound three. -/
theorem optimalQuotientModel_three_index_le_three_of_cosetBound
    (hcosets : ThreeCosetBound) :
    optimalQuotientModelThreeRange.index ≤ 3 := by
  letI : Finite
      (optimalQuotientModel.toAffine.Point ⧸
        optimalQuotientModelThreeRange) :=
    Finite.of_surjective _
      (optimalQuotientModel_three_quotient_surjective hcosets)
  rw [AddSubgroup.index_eq_card]
  exact
    (Nat.card_le_card_of_surjective _
      (optimalQuotientModel_three_quotient_surjective hcosets)).trans_eq
        (by simp)

theorem optimalQuotientModel_point_rank_zero_of_cosetBound
    (hcosets : ThreeCosetBound) :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 := by
  letI : AddGroup.FG optimalQuotientModel.toAffine.Point :=
    optimalQuotientModel_point_fg_of_cosetBound hcosets
  let f := nsmulAddMonoidHom (α := optimalQuotientModel.toAffine.Point) 3
  have hformula := AddSubgroup.index_range_nsmul_of_fg
    optimalQuotientModel.toAffine.Point (by norm_num : (3 : ℕ) ≠ 0)
  change optimalQuotientModelThreeRange.index =
    3 ^ Module.finrank ℤ optimalQuotientModel.toAffine.Point * Nat.card f.ker at hformula
  have hmem : modelThreeTorsion ∈ f.ker := by
    change (3 : ℕ) • modelThreeTorsion = 0
    rw [← addOrderOf_modelThreeTorsion]
    exact addOrderOf_nsmul_eq_zero modelThreeTorsion
  have hdvd : 3 ∣ Nat.card f.ker := by
    have hd := f.ker.addOrderOf_dvd_natCard hmem
    simpa only [addOrderOf_modelThreeTorsion] using hd
  have hpos : 0 < Nat.card f.ker := by
    have hne := (optimalQuotientModel_three_finiteIndex_of_cosetBound hcosets).index_ne_zero
    rw [hformula] at hne
    exact Nat.pos_of_ne_zero (right_ne_zero_of_mul hne)
  have hge := Nat.le_of_dvd hpos hdvd
  have hle := optimalQuotientModel_three_index_le_three_of_cosetBound hcosets
  rw [hformula] at hle
  have hbound := (Nat.mul_le_mul_left _ hge).trans hle
  have hone : 3 ^ Module.finrank ℤ optimalQuotientModel.toAffine.Point = 1 := by
    have h1 := Nat.one_le_pow (Module.finrank ℤ optimalQuotientModel.toAffine.Point)
      3 (by decide)
    omega
  simpa using hone

/-- Once the exact three cosets are certified, the rational point group of
the selected fixed model is finite. -/
theorem optimalQuotientModel_point_finite_of_cosetBound
    (hcosets : ThreeCosetBound) :
    Finite optimalQuotientModel.toAffine.Point := by
  letI : AddGroup.FG optimalQuotientModel.toAffine.Point :=
    optimalQuotientModel_point_fg_of_cosetBound hcosets
  letI : Module.Finite ℤ optimalQuotientModel.toAffine.Point :=
    Module.Finite.iff_addGroup_fg.mpr
      (optimalQuotientModel_point_fg_of_cosetBound hcosets)
  have hmoduleTorsion :
      Module.IsTorsion ℤ optimalQuotientModel.toAffine.Point :=
    (Module.finrank_eq_zero_iff_isTorsion (R := ℤ)).mp
      (optimalQuotientModel_point_rank_zero_of_cosetBound hcosets)
  exact
    AddCommGroup.finite_of_fg_torsion
      optimalQuotientModel.toAffine.Point
      (AddMonoid.isTorsion_iff_isTorsion_int.mpr hmoduleTorsion)

end MazurTorsion.OrderThirtyFive

end

/- Source: MazurTorsion/NumberTheory/OrderThirtyFiveThreeDescent.lean -/

section

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# The rational three-cover attached to the order-35 dual candidate

For the normalized source curve

`y² + 4xy + 7y = x³`,

the fixed three-descent function is the source ordinate `y`.  Pulling this
function back along the checked dual candidate gives the literal cube

`((Y - 28) / (3X + 16))³`.

Conversely, if a nonzero source ordinate is a rational cube `t³`, writing
`x = tu` produces the plane cubic

`u³ = t³ + 4tu + 7`.

This cubic has an explicit map to the candidate target, and the dual
candidate sends the resulting point back to `(x,y)`.  Thus this file proves
the affine, nonexceptional part of the key descent equivalence

`y(P) is a cube ⇔ P lies in the image of the dual candidate`.

The exceptional points with `y = 0` encode the two nontrivial visible cosets
and are deliberately not folded into a multiplicative quotient by an ad hoc
zero convention.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Affine
open Polynomial

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve.Affine

/-- Pullback of the source ordinate along the dual candidate is a literal
rational cube. -/
theorem veluThreeDualCandidateY_eq_cube
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    veluThreeDualCandidateY X Y =
      ((Y - 28) / veluThreeDualCandidateKernel X) ^ 3 := by
  let K : ℚ := 3 * X + 16
  let A : ℚ := X ^ 3 - 252 * X - 1771
  let B : ℚ := X ^ 3 + 16 * X ^ 2 + 252 * X + 2198
  let Z : ℚ := 2 * Y + 4 * X + 7
  have hkernel := veluThreeDualCandidateKernel_ne_zero hP
  have hK : K ≠ 0 := by
    simpa only [K, veluThreeDualCandidateKernel] using hkernel
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [veluThreeCandidateTarget] at hcurve
  change ((Z * (B / K ^ 3) - 4 * (A / K ^ 2) - 7) / 2) =
    ((Y - 28) / K) ^ 3
  field_simp [hK]
  dsimp only [A, B, K, Z]
  linear_combination 2 * (4 * X - Y + 91) * hcurve

/-- The abscissa on the rational three-cover. -/
def threeCoverTargetX (t u : ℚ) : ℚ :=
  3 * t ^ 2 + 3 * t * u - 4 * t + 3 * u ^ 2 + 4 * u

/-- The ordinate on the rational three-cover. -/
def threeCoverTargetY (t u : ℚ) : ℚ :=
  28 + t * (3 * threeCoverTargetX t u + 16)

/-- The covering cubic maps to the candidate target equation. -/
theorem threeCoverTarget_equation
    {t u : ℚ}
    (hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7) :
    veluThreeCandidateTarget.toAffine.Equation
      (threeCoverTargetX t u) (threeCoverTargetY t u) := by
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [veluThreeCandidateTarget]
  dsimp only [threeCoverTargetX, threeCoverTargetY]
  linear_combination
    -(54 * t ^ 3 + 81 * t ^ 2 * u + 81 * t * u ^ 2 +
      108 * t * u + 27 * u ^ 3 + 108 * u ^ 2 + 144 * u + 253) *
        hcover

/-- The rational point on the candidate target supplied by the covering
cubic. -/
noncomputable def threeCoverTargetPoint
    {t u : ℚ}
    (hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7) :
    veluThreeCandidateTarget.toAffine.Point :=
  .some (threeCoverTargetX t u) (threeCoverTargetY t u)
    (veluThreeCandidateTarget.toAffine.equation_iff_nonsingular.mp
      (threeCoverTarget_equation hcover))

/-- The dual abscissa of a covering point is `tu`. -/
theorem veluThreeDualCandidateX_threeCoverTargetX
    {t u : ℚ}
    (hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7) :
    veluThreeDualCandidateX (threeCoverTargetX t u) = t * u := by
  let X : ℚ := threeCoverTargetX t u
  let K : ℚ := 3 * X + 16
  let A : ℚ := X ^ 3 - 252 * X - 1771
  let htarget : veluThreeCandidateTarget.toAffine.Nonsingular
      (threeCoverTargetX t u) (threeCoverTargetY t u) :=
    veluThreeCandidateTarget.toAffine.equation_iff_nonsingular.mp
      (threeCoverTarget_equation hcover)
  have hkernel := veluThreeDualCandidateKernel_ne_zero htarget
  have hK : K ≠ 0 := by
    simpa only [K, X, veluThreeDualCandidateKernel] using hkernel
  change A / K ^ 2 = t * u
  field_simp [hK]
  dsimp only [A, K, X, threeCoverTargetX] at hcover ⊢
  linear_combination
    -(27 * t ^ 3 - 108 * t ^ 2 + 144 * t - 27 * u ^ 3 -
      108 * u ^ 2 - 144 * u - 253) * hcover

/-- The dual ordinate of a covering point is `t³`. -/
theorem veluThreeDualCandidateY_threeCoverTarget
    {t u : ℚ}
    (hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7) :
    veluThreeDualCandidateY
        (threeCoverTargetX t u) (threeCoverTargetY t u) = t ^ 3 := by
  let htarget : veluThreeCandidateTarget.toAffine.Nonsingular
      (threeCoverTargetX t u) (threeCoverTargetY t u) :=
    veluThreeCandidateTarget.toAffine.equation_iff_nonsingular.mp
      (threeCoverTarget_equation hcover)
  rw [veluThreeDualCandidateY_eq_cube htarget]
  have hkernel := veluThreeDualCandidateKernel_ne_zero htarget
  have hkernel' :
      3 * threeCoverTargetX t u + 16 ≠ 0 := by
    simpa only [veluThreeDualCandidateKernel] using hkernel
  have ht :
      (threeCoverTargetY t u - 28) /
          veluThreeDualCandidateKernel (threeCoverTargetX t u) = t := by
    simp only [threeCoverTargetY, veluThreeDualCandidateKernel]
    field_simp [hkernel']
    ring
  rw [ht]

/-- A nonzero cube source ordinate gives an explicit rational preimage under
the dual candidate. -/
theorem exists_dualCandidate_preimage_of_Y_eq_cube
    {x y t : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (ht : t ≠ 0)
    (hy : y = t ^ 3) :
    ∃ Q : veluThreeCandidateTarget.toAffine.Point,
      veluThreeDualCandidatePointFun Q =
        WeierstrassCurve.Affine.Point.some x y hP := by
  let u : ℚ := x / t
  have hxu : x = t * u := by
    dsimp only [u]
    field_simp [ht]
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  have hfactor :
      t ^ 3 * (t ^ 3 + 4 * t * u + 7) = t ^ 3 * u ^ 3 := by
    calc
      t ^ 3 * (t ^ 3 + 4 * t * u + 7) =
          y ^ 2 + 4 * x * y + 7 * y := by rw [hy, hxu]; ring
      _ = x ^ 3 := hcurve
      _ = t ^ 3 * u ^ 3 := by rw [hxu]; ring
  have hcover : u ^ 3 = t ^ 3 + 4 * t * u + 7 := by
    exact (mul_left_cancel₀ (pow_ne_zero 3 ht) hfactor).symm
  refine ⟨threeCoverTargetPoint hcover, ?_⟩
  simp only [threeCoverTargetPoint, veluThreeDualCandidatePointFun,
    veluThreeDualCandidatePoint,
    WeierstrassCurve.Affine.Point.some.injEq]
  constructor
  · rw [veluThreeDualCandidateX_threeCoverTargetX hcover]
    exact hxu.symm
  · rw [veluThreeDualCandidateY_threeCoverTarget hcover]
    exact hy.symm

/-! ## Translation by the visible kernel -/

/-- Translating by `(0,0)` multiplies the source descent class by `49`:
the new ordinate is `-49y/x³`. -/
theorem addY_threeTorsionOrigin
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    threeTorsionCurve.toAffine.addY x 0 y
        (threeTorsionCurve.toAffine.slope x 0 y 0) =
      -49 * y / x ^ 3 := by
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  rw [threeTorsionCurve.toAffine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY, threeTorsionCurve]
  field_simp [hx]
  linear_combination -x ^ 3 * (4 * x + y - 7) * hcurve

/-- Translating by `(0,-7) = -(0,0)` gives the symmetric raw ordinate
formula. -/
theorem addY_neg_threeTorsionOrigin
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) :
    threeTorsionCurve.toAffine.addY x 0 y
        (threeTorsionCurve.toAffine.slope x 0 y (-7)) =
      -7 * (y + 4 * x + 7) ^ 2 / x ^ 3 := by
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  rw [threeTorsionCurve.toAffine.slope_of_X_ne hx]
  simp only [WeierstrassCurve.Affine.addY,
    WeierstrassCurve.Affine.negAddY,
    WeierstrassCurve.Affine.addX,
    WeierstrassCurve.Affine.negY, threeTorsionCurve]
  field_simp [hx]
  linear_combination -x ^ 3 * (4 * x + y + 7) * hcurve

/-- Away from the exceptional ordinate zero, translation by `(0,-7)`
multiplies the descent class by `7`, up to the displayed rational cube. -/
theorem addY_neg_threeTorsionOrigin_cubeClass
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (hx : x ≠ 0) (hy : y ≠ 0) :
    threeTorsionCurve.toAffine.addY x 0 y
        (threeTorsionCurve.toAffine.slope x 0 y (-7)) =
      -7 * y * (x / y) ^ 3 := by
  rw [addY_neg_threeTorsionOrigin hP hx]
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  field_simp [hx, hy]
  linear_combination
    -(x ^ 3 + 4 * x * y + y ^ 2 + 7 * y) * hcurve

/-! ## Exact arithmetic inputs and assembly of the three cosets -/

/-- A nonzero factor of a cube whose gcd with the cofactor divides `7` has
one of the three cube classes supported at `7`. -/
private theorem cubeclass_of_gcd_dvd_seven
    {A B C : ℤ}
    (hA : A ≠ 0) (hprod : A * B = C ^ 3)
    (hgcd : GCDMonoid.gcd A B ∣ (7 : ℤ)) :
    ∃ d : ℤ, A = d ^ 3 ∨ A = 7 * d ^ 3 ∨ A = 49 * d ^ 3 := by
  let g : ℤ := GCDMonoid.gcd A B
  have hgA : g ∣ A := GCDMonoid.gcd_dvd_left A B
  have hgB : g ∣ B := GCDMonoid.gcd_dvd_right A B
  have hg0 : g ≠ 0 := by
    intro hz
    rw [hz] at hgA
    exact hA (zero_dvd_iff.mp hgA)
  have hgpos : 0 < g :=
    lt_of_le_of_ne (Int.gcd_nonneg A B) (Ne.symm hg0)
  have hdivNat : g.natAbs ∣ 7 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hgcd
  have hgleNat : g.natAbs ≤ 7 := Nat.le_of_dvd (by norm_num) hdivNat
  have hgle : g ≤ 7 := by
    have : (g.natAbs : ℤ) ≤ 7 := by exact_mod_cast hgleNat
    simpa [Int.natCast_natAbs, abs_of_pos hgpos] using this
  have hgval : g = 1 ∨ g = 7 := by
    interval_cases g <;> norm_num at hdivNat
    all_goals simp
  rcases hgval with hg | hg
  · have hab : IsCoprime A B := by
      apply (gcd_isUnit_iff A B).mp
      rw [← show g = GCDMonoid.gcd A B from rfl, hg]
      exact isUnit_one
    obtain ⟨d, hd⟩ :=
      Int.eq_pow_of_mul_eq_pow_odd_left (k := 3) hab (by norm_num) hprod
    exact ⟨d, Or.inl hd⟩
  · have hsevenA : (7 : ℤ) ∣ A := by simpa [hg] using hgA
    have hsevenB : (7 : ℤ) ∣ B := by simpa [hg] using hgB
    have hsevenC : (7 : ℤ) ∣ C := by
      have hsevenC3 : (7 : ℤ) ∣ C ^ 3 := by
        rw [← hprod]
        exact dvd_mul_of_dvd_left hsevenA B
      have hprime7 : Prime (7 : ℤ) :=
        Int.prime_iff_natAbs_prime.mpr (by norm_num)
      exact hprime7.dvd_of_dvd_pow hsevenC3
    let a : ℤ := A / 7
    let b : ℤ := B / 7
    let c : ℤ := C / 7
    have hga : 7 * a = A := by
      exact EuclideanDomain.mul_div_cancel' (by norm_num) hsevenA
    have hgb : 7 * b = B := by
      exact EuclideanDomain.mul_div_cancel' (by norm_num) hsevenB
    have hgc : 7 * c = C := by
      exact EuclideanDomain.mul_div_cancel' (by norm_num) hsevenC
    have hab : a * b = 7 * c ^ 3 := by
      apply mul_left_cancel₀ (show (49 : ℤ) ≠ 0 by norm_num)
      calc
        49 * (a * b) = A * B := by rw [← hga, ← hgb]; ring
        _ = C ^ 3 := hprod
        _ = 49 * (7 * c ^ 3) := by rw [← hgc]; ring
    have habcop : IsCoprime a b := by
      simpa [g, hg] using
        (isCoprime_div_gcd_div_gcd_of_gcd_ne_zero hg0 :
          IsCoprime (A / g) (B / g))
    have hsevenab : (7 : ℤ) ∣ a * b := by
      rw [hab]
      exact dvd_mul_right 7 (c ^ 3)
    have hprime7 : Prime (7 : ℤ) :=
      Int.prime_iff_natAbs_prime.mpr (by norm_num)
    rcases hprime7.dvd_mul.mp hsevenab with hsevena | hsevenb
    · obtain ⟨a', ha'⟩ := hsevena
      have ha'div : a' ∣ a := ⟨7, by rw [ha']; ring⟩
      have ha'bcube : a' * b = c ^ 3 := by
        apply mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num)
        calc
          7 * (a' * b) = a * b := by rw [ha']; ring
          _ = 7 * c ^ 3 := hab
      have ha'b : IsCoprime a' b :=
        habcop.of_isCoprime_of_dvd_left ha'div
      obtain ⟨d, hd⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd_left (k := 3) ha'b (by norm_num) ha'bcube
      refine ⟨d, Or.inr (Or.inr ?_)⟩
      rw [← hga, ha', hd]
      ring
    · obtain ⟨b', hb'⟩ := hsevenb
      have hb'div : b' ∣ b := ⟨7, by rw [hb']; ring⟩
      have hab'cube : a * b' = c ^ 3 := by
        apply mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num)
        calc
          7 * (a * b') = a * b := by rw [hb']; ring
          _ = 7 * c ^ 3 := hab
      have hab' : IsCoprime a b' :=
        habcop.of_isCoprime_of_dvd_right hb'div
      obtain ⟨d, hd⟩ :=
        Int.eq_pow_of_mul_eq_pow_odd_left (k := 3) hab' (by norm_num) hab'cube
      refine ⟨d, Or.inr (Or.inl ?_)⟩
      rw [← hga, hd]

/-- Scaling the abscissa by the reduced denominator of the ordinate gives
an integer.  This is the integral-root step behind the weighted integral
coordinates used in the source descent. -/
private theorem integral_scaled_abscissa
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y) :
    ∃ U : ℤ, (y.den : ℚ) * x = U := by
  let r : ℤ := y.num
  let s : ℤ := y.den
  let u : ℚ := (s : ℚ) * x
  let p : ℤ[X] :=
    Polynomial.X ^ 3 -
      (Polynomial.C (4 * r * s) * Polynomial.X +
        Polynomial.C (r ^ 2 * s + 7 * r * s ^ 2))
  have hs : (s : ℚ) ≠ 0 := by
    dsimp [s]
    exact_mod_cast y.den_ne_zero
  have hy : y = (r : ℚ) / (s : ℚ) := by
    simpa [r, s] using y.num_div_den.symm
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  have hu :
      u ^ 3 - (4 * r * s : ℤ) * u -
          (r ^ 2 * s + 7 * r * s ^ 2 : ℤ) = 0 := by
    rw [hy] at hcurve
    dsimp only [u]
    push_cast
    field_simp [hs] at hcurve
    linear_combination -(s : ℚ) * hcurve
  have hp : p.Monic := by
    dsimp only [p]
    apply Polynomial.monic_X_pow_sub
    compute_degree
    norm_num
  have hroot : Polynomial.aeval u p = 0 := by
    dsimp only [p]
    simp only [map_sub, map_add, map_mul, Polynomial.aeval_X,
      Polynomial.aeval_C, map_pow]
    norm_num at hu ⊢
    linear_combination hu
  obtain ⟨U, hU, -⟩ := exists_integer_of_is_root_of_monic hp hroot
  exact ⟨U, by simpa [u, s] using hU⟩

/-- In the reduced integral source equation, any common divisor of the two
descent factors divides `7`.  The exponent-one assertion at `7` is the only
non-radical part of the calculation. -/
private theorem common_divisor_source_dvd_seven
    {r s U T d : ℤ}
    (hrs : IsCoprime r s)
    (hT : T = r + 4 * U + 7 * s)
    (hcurve : r * s * T = U ^ 3)
    (hdr : d ∣ r) (hdT : d ∣ T) :
    d ∣ (7 : ℤ) := by
  have hds : IsCoprime d s :=
    hrs.of_isCoprime_of_dvd_left hdr
  have hdU3 : d ∣ U ^ 3 := by
    rw [← hcurve]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hdr s) T
  have hdlin : d ∣ 4 * U + 7 * s := by
    have hsub : d ∣ T - r := hdT.sub hdr
    convert hsub using 1
    rw [hT]
    ring
  have hd343s3 : d ∣ 343 * s ^ 3 := by
    have hid :
        (4 * U + 7 * s) *
            (16 * U ^ 2 - 28 * U * s + 49 * s ^ 2) =
          64 * U ^ 3 + 343 * s ^ 3 := by ring
    have hdsum : d ∣ 64 * U ^ 3 + 343 * s ^ 3 := by
      rw [← hid]
      exact dvd_mul_of_dvd_left hdlin _
    obtain ⟨a, ha⟩ := hdsum
    obtain ⟨b, hb⟩ : d ∣ 64 * U ^ 3 := by
      simpa [mul_comm] using dvd_mul_of_dvd_right hdU3 64
    refine ⟨a - b, ?_⟩
    linear_combination ha - hb
  have hd343 : d ∣ (343 : ℤ) :=
    hds.pow_right.dvd_of_dvd_mul_right hd343s3
  by_cases hd0 : d = 0
  · subst d
    norm_num at hd343
  have hdabs : d.natAbs ∣ 343 := by
    simpa using Int.natAbs_dvd_natAbs.mpr hd343
  have hdabs' : d.natAbs ∣ 7 ^ 3 := by
    norm_num at hdabs ⊢
    exact hdabs
  obtain ⟨k, hk, hkval⟩ :=
    (Nat.dvd_prime_pow Nat.prime_seven).mp hdabs'
  have hnot49 : ¬ (49 : ℤ) ∣ d := by
    intro h49d
    have h49r : (49 : ℤ) ∣ r := h49d.trans hdr
    have h49T : (49 : ℤ) ∣ T := h49d.trans hdT
    have h2401U3 : (2401 : ℤ) ∣ U ^ 3 := by
      obtain ⟨r', hr'⟩ := h49r
      obtain ⟨T', hT'⟩ := h49T
      refine ⟨r' * s * T', ?_⟩
      rw [← hcurve, hr', hT']
      ring
    have h7U : (7 : ℤ) ∣ U := by
      apply Int.Prime.dvd_pow' Nat.prime_seven
      exact (show (7 : ℤ) ∣ 2401 by norm_num).trans h2401U3
    obtain ⟨u, hu⟩ := h7U
    obtain ⟨q, hq⟩ := h2401U3
    have huCube : u ^ 3 = 7 * q := by
      apply mul_left_cancel₀ (show (343 : ℤ) ≠ 0 by norm_num)
      calc
        343 * u ^ 3 = U ^ 3 := by rw [hu]; ring
        _ = 2401 * q := hq
        _ = 343 * (7 * q) := by ring
    have h7u : (7 : ℤ) ∣ u := by
      apply Int.Prime.dvd_pow' Nat.prime_seven
      exact ⟨q, huCube⟩
    obtain ⟨u', hu'⟩ := h7u
    have h49U : (49 : ℤ) ∣ U := by
      refine ⟨u', ?_⟩
      rw [hu, hu']
      ring
    have h49lin : (49 : ℤ) ∣ 4 * U + 7 * s := by
      have hsub : (49 : ℤ) ∣ T - r := h49T.sub h49r
      convert hsub using 1
      rw [hT]
      ring
    have h49sevenS : (49 : ℤ) ∣ 7 * s := by
      obtain ⟨a, ha⟩ := h49lin
      obtain ⟨b, hb⟩ : (49 : ℤ) ∣ 4 * U := by
        simpa [mul_comm] using dvd_mul_of_dvd_right h49U 4
      refine ⟨a - b, ?_⟩
      linear_combination ha - hb
    obtain ⟨q, hq⟩ := h49sevenS
    have h7s : (7 : ℤ) ∣ s := by
      refine ⟨q, ?_⟩
      apply mul_left_cancel₀ (show (7 : ℤ) ≠ 0 by norm_num)
      calc
        7 * s = 49 * q := hq
        _ = 7 * (7 * q) := by ring
    have h7r : (7 : ℤ) ∣ r :=
      (show (7 : ℤ) ∣ 49 by norm_num).trans h49r
    have hunit : IsUnit (7 : ℤ) :=
      hrs.isUnit_of_dvd' h7r h7s
    rcases Int.isUnit_iff.mp hunit with h | h <;> norm_num at h
  have hklt : k < 2 := by
    by_contra hknot
    have hk2 : 2 ≤ k := by omega
    have h49abs : 49 ∣ d.natAbs := by
      rw [hkval]
      simpa using (pow_dvd_pow (7 : ℕ) hk2)
    apply hnot49
    have h49cast : (49 : ℤ) ∣ (d.natAbs : ℤ) := by
      exact_mod_cast h49abs
    simpa [Int.natCast_natAbs] using h49cast
  have hkcases : k = 0 ∨ k = 1 := by omega
  rcases hkcases with rfl | rfl
  · have hdabs1 : d.natAbs = 1 := by simpa using hkval
    have hdunit : IsUnit d := by
      exact Int.isUnit_iff.mpr (Int.natAbs_eq_iff.mp hdabs1)
    exact hdunit.dvd
  · have hdseven : d.natAbs = 7 := by simpa using hkval
    have hdval : d = 7 ∨ d = -7 := by
      simpa using (Int.natAbs_eq_iff.mp hdseven)
    rcases hdval with rfl | rfl
    · exact dvd_rfl
    · norm_num

/-- The second reduced source factor is coprime to the denominator. -/
private theorem source_factor_coprime_denominator
    {r s U T : ℤ}
    (hrs : IsCoprime r s) (hs0 : s ≠ 0)
    (hT : T = r + 4 * U + 7 * s)
    (hcurve : r * s * T = U ^ 3) :
    IsCoprime T s := by
  apply isCoprime_of_prime_dvd
  · exact fun h ↦ hs0 h.2
  · intro p hp hpT hps
    have hpU3 : p ∣ U ^ 3 := by
      rw [← hcurve]
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right hps r) T
    have hpU : p ∣ U := hp.dvd_of_dvd_pow hpU3
    have hp4U : p ∣ 4 * U := by
      simpa [mul_comm] using dvd_mul_of_dvd_right hpU 4
    have hp7s : p ∣ 7 * s :=
      dvd_mul_of_dvd_right hps 7
    have hpr : p ∣ r := by
      obtain ⟨a, ha⟩ := hpT
      obtain ⟨b, hb⟩ := hp4U
      obtain ⟨c, hc⟩ := hp7s
      refine ⟨a - b - c, ?_⟩
      calc
        r = T - 4 * U - 7 * s := by rw [hT]; ring
        _ = p * (a - b - c) := by rw [ha, hb, hc]; ring
    exact hp.not_unit (hrs.isUnit_of_dvd' hpr hps)

/-- The source equation in the reduced integral coordinates
`r = num(y)`, `s = den(y)`, and `U = sx`. -/
private theorem scaled_source_equation
    {x y : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    {U : ℤ} (hU : (y.den : ℚ) * x = U) :
    y.num * (y.den : ℤ) *
        (y.num + 4 * U + 7 * (y.den : ℤ)) = U ^ 3 := by
  let r : ℤ := y.num
  let s : ℤ := y.den
  have hs : (s : ℚ) ≠ 0 := by
    dsimp [s]
    exact_mod_cast y.den_ne_zero
  have hy : y = (r : ℚ) / (s : ℚ) := by
    simpa [r, s] using y.num_div_den.symm
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [threeTorsionCurve] at hcurve
  have hQ :
      ((r * s * (r + 4 * U + 7 * s) : ℤ) : ℚ) =
        ((U ^ 3 : ℤ) : ℚ) := by
    rw [hy] at hcurve
    have hU' : (s : ℚ) * x = (U : ℚ) := by
      simpa [s] using hU
    push_cast
    field_simp [hs] at hcurve
    rw [← hU']
    linear_combination (s : ℚ) * hcurve
  exact_mod_cast hQ

/-- The source local calculation needed from the fixed three-descent: every
nonexceptional ordinate has one of the three supported cube classes
`1`, `7`, or `49`. -/
def SourceThreeCubeClassBound : Prop :=
  ∀ {x y : ℚ},
    threeTorsionCurve.toAffine.Nonsingular x y → x ≠ 0 →
      ∃ t : ℚ, t ≠ 0 ∧
        (y = t ^ 3 ∨ y = 7 * t ^ 3 ∨ y = 49 * t ^ 3)

/-- The fixed source local calculation: the ordinate of every
nonexceptional rational point has cube class `1`, `7`, or `49`.

The proof uses reduced numerator-denominator coordinates for the ordinate.
The integral-root theorem first shows that `den(y) * x` is integral.  The
resulting two integral descent factors are coprime away from `7`, while a
short exponent calculation rules out a common factor `49`. -/
theorem sourceThreeCubeClassBound : SourceThreeCubeClassBound := by
  intro x y hP hx
  have hy0 : y ≠ 0 := by
    intro hy
    have hcurve := hP.1
    rw [WeierstrassCurve.Affine.equation_iff] at hcurve
    norm_num [threeTorsionCurve, hy] at hcurve
    exact hx (eq_zero_of_pow_eq_zero hcurve.symm)
  obtain ⟨U, hU⟩ := integral_scaled_abscissa hP
  let r : ℤ := y.num
  let s : ℤ := y.den
  let T : ℤ := r + 4 * U + 7 * s
  have hr0 : r ≠ 0 := by
    dsimp only [r]
    exact Rat.num_ne_zero.mpr hy0
  have hs0 : s ≠ 0 := by
    dsimp only [s]
    exact_mod_cast y.den_ne_zero
  have hrs : IsCoprime r s := by
    simpa [r, s] using Rat.isCoprime_num_den y
  have hT : T = r + 4 * U + 7 * s := rfl
  have hcurve : r * s * T = U ^ 3 := by
    simpa [r, s, T] using scaled_source_equation hP hU
  have hTs : IsCoprime T s :=
    source_factor_coprime_denominator hrs hs0 hT hcurve
  have hRTs : IsCoprime (r * T) s := hrs.mul_left hTs
  have hprod : (r * T) * s = U ^ 3 := by
    calc
      (r * T) * s = r * s * T := by ring
      _ = U ^ 3 := hcurve
  obtain ⟨e, he⟩ := Int.eq_pow_of_mul_eq_pow_odd_left (k := 3) hRTs.symm
    (by norm_num) (by simpa [mul_comm] using hprod)
  obtain ⟨w, hw⟩ :=
    Int.eq_pow_of_mul_eq_pow_odd_left (k := 3) hRTs (by norm_num) hprod
  have hgcd : GCDMonoid.gcd r T ∣ (7 : ℤ) :=
    common_divisor_source_dvd_seven hrs hT hcurve
      (GCDMonoid.gcd_dvd_left r T)
      (GCDMonoid.gcd_dvd_right r T)
  have he0 : e ≠ 0 := by
    intro hezero
    rw [hezero] at he
    norm_num at he
    exact hs0 he
  have hy : y = (r : ℚ) / (s : ℚ) := by
    simpa [r, s] using y.num_div_den.symm
  obtain ⟨d, hd | hd | hd⟩ :=
    cubeclass_of_gcd_dvd_seven hr0 hw hgcd
  · have hd0 : d ≠ 0 := by
      intro hdzero
      rw [hdzero] at hd
      norm_num at hd
      exact hr0 hd
    refine ⟨(d : ℚ) / (e : ℚ), div_ne_zero (by exact_mod_cast hd0)
      (by exact_mod_cast he0), Or.inl ?_⟩
    rw [hy, hd, he]
    push_cast
    field_simp [he0]
  · have hd0 : d ≠ 0 := by
      intro hdzero
      rw [hdzero] at hd
      norm_num at hd
      exact hr0 hd
    refine ⟨(d : ℚ) / (e : ℚ), div_ne_zero (by exact_mod_cast hd0)
      (by exact_mod_cast he0), Or.inr (Or.inl ?_)⟩
    rw [hy, hd, he]
    push_cast
    field_simp [he0]
  · have hd0 : d ≠ 0 := by
      intro hdzero
      rw [hdzero] at hd
      norm_num at hd
      exact hr0 hd
    refine ⟨(d : ℚ) / (e : ℚ), div_ne_zero (by exact_mod_cast hd0)
      (by exact_mod_cast he0), Or.inr (Or.inr ?_)⟩
    rw [hy, hd, he]
    push_cast
    field_simp [he0]

/-- The target local calculation needed from the fixed three-descent: every
rational target point is in the image of the first candidate point
function.  No additivity is included in this proposition. -/
def TargetThreeCandidateSurjective : Prop :=
  Function.Surjective veluThreeCandidatePointFun

/-- Under target surjectivity, a nonzero cube source ordinate makes the
source point an actual triple. -/
theorem exists_eq_three_nsmul_of_Y_eq_cube
    (htarget : TargetThreeCandidateSurjective)
    {x y t : ℚ}
    (hP : threeTorsionCurve.toAffine.Nonsingular x y)
    (ht : t ≠ 0) (hy : y = t ^ 3) :
    ∃ R : threeTorsionCurve.toAffine.Point,
      WeierstrassCurve.Affine.Point.some x y hP = (3 : ℕ) • R := by
  obtain ⟨Q, hQ⟩ := exists_dualCandidate_preimage_of_Y_eq_cube hP ht hy
  obtain ⟨R, hR⟩ := htarget Q
  refine ⟨R, ?_⟩
  calc
    WeierstrassCurve.Affine.Point.some x y hP =
        veluThreeDualCandidatePointFun Q := hQ.symm
    _ = veluThreeDualCandidatePointFun
          (veluThreeCandidatePointFun R) := by rw [hR]
    _ = (3 : ℕ) • R :=
      veluThreeDualCandidatePointFun_candidate R

private theorem two_nsmul_threeTorsionOrigin_eq_neg :
    (2 : ℕ) • threeTorsionOrigin = -threeTorsionOrigin := by
  have hthree : (3 : ℕ) • threeTorsionOrigin = 0 := by
    rw [← addOrderOf_threeTorsionOrigin]
    exact addOrderOf_nsmul_eq_zero threeTorsionOrigin
  calc
    (2 : ℕ) • threeTorsionOrigin =
        (3 : ℕ) • threeTorsionOrigin - threeTorsionOrigin := by abel
    _ = -threeTorsionOrigin := by rw [hthree]; simp

/-- The two fixed arithmetic outputs assemble to the exact three-coset
certificate consumed by the rank-zero boundary. -/
theorem threeCosetBound_of_descent_inputs
    (hsource : SourceThreeCubeClassBound)
    (htarget : TargetThreeCandidateSurjective) :
    ThreeCosetBound := by
  intro P
  cases P with
  | zero =>
      refine ⟨⟨0, by norm_num⟩, 0, ?_⟩
      simp [normalizedThreeRepresentative]
      rfl
  | some x y hP =>
      by_cases hx : x = 0
      · have hcandidate :
            veluThreeCandidatePointFun
              (WeierstrassCurve.Affine.Point.some x y hP) = 0 := by
          simp [veluThreeCandidatePointFun, hx]
          rfl
        rcases
            (veluThreeCandidatePointFun_eq_zero_iff
              (WeierstrassCurve.Affine.Point.some x y hP)).mp hcandidate with
          hzero | horigin | hnegOrigin
        · exact (WeierstrassCurve.Affine.Point.some_ne_zero hP hzero).elim
        · refine ⟨⟨1, by norm_num⟩, 0, ?_⟩
          simpa [normalizedThreeRepresentative] using horigin
        · refine ⟨⟨2, by norm_num⟩, 0, ?_⟩
          rw [hnegOrigin, normalizedThreeRepresentative]
          norm_num
          exact two_nsmul_threeTorsionOrigin_eq_neg.symm
      · obtain ⟨t, ht, hy | hy | hy⟩ := hsource hP hx
        · obtain ⟨R, hR⟩ :=
            exists_eq_three_nsmul_of_Y_eq_cube htarget hP ht hy
          refine ⟨⟨0, by norm_num⟩, R, ?_⟩
          simpa [normalizedThreeRepresentative] using hR
        · have hT : threeTorsionCurve.toAffine.Nonsingular 0 0 := by
            apply threeTorsionCurve.toAffine.equation_iff_nonsingular.mp
            norm_num [WeierstrassCurve.Affine.equation_iff,
              threeTorsionCurve]
          let x' : ℚ := threeTorsionCurve.toAffine.addX x 0
            (threeTorsionCurve.toAffine.slope x 0 y 0)
          let y' : ℚ := threeTorsionCurve.toAffine.addY x 0 y
            (threeTorsionCurve.toAffine.slope x 0 y 0)
          have hP' : threeTorsionCurve.toAffine.Nonsingular x' y' :=
            nonsingular_add hP hT (fun hxy => hx hxy.1)
          let t' : ℚ := -7 * t / x
          have ht' : t' ≠ 0 := by
            dsimp only [t']
            exact div_ne_zero (mul_ne_zero (by norm_num) ht) hx
          have hy' : y' = t' ^ 3 := by
            dsimp only [y', t']
            rw [addY_threeTorsionOrigin hP hx, hy]
            field_simp [hx]
            ring
          obtain ⟨R, hR⟩ :=
            exists_eq_three_nsmul_of_Y_eq_cube htarget hP' ht' hy'
          have hsum :
              WeierstrassCurve.Affine.Point.some x y hP +
                  threeTorsionOrigin = (3 : ℕ) • R := by
            calc
              WeierstrassCurve.Affine.Point.some x y hP +
                    threeTorsionOrigin =
                  WeierstrassCurve.Affine.Point.some x' y' hP' := by
                rw [threeTorsionOrigin]
                exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
              _ = (3 : ℕ) • R := hR
          refine ⟨⟨2, by norm_num⟩, R, ?_⟩
          rw [normalizedThreeRepresentative]
          norm_num
          rw [two_nsmul_threeTorsionOrigin_eq_neg]
          calc
            WeierstrassCurve.Affine.Point.some x y hP =
                -threeTorsionOrigin +
                  (WeierstrassCurve.Affine.Point.some x y hP +
                    threeTorsionOrigin) := by abel
            _ = -threeTorsionOrigin + (3 : ℕ) • R := by rw [hsum]
        · have hnegT : threeTorsionCurve.toAffine.Nonsingular 0 (-7) := by
            apply threeTorsionCurve.toAffine.equation_iff_nonsingular.mp
            norm_num [WeierstrassCurve.Affine.equation_iff,
              threeTorsionCurve]
          let x' : ℚ := threeTorsionCurve.toAffine.addX x 0
            (threeTorsionCurve.toAffine.slope x 0 y (-7))
          let y' : ℚ := threeTorsionCurve.toAffine.addY x 0 y
            (threeTorsionCurve.toAffine.slope x 0 y (-7))
          have hP' : threeTorsionCurve.toAffine.Nonsingular x' y' :=
            nonsingular_add hP hnegT (fun hxy => hx hxy.1)
          have hy0 : y ≠ 0 := by rw [hy]; positivity
          let t' : ℚ := -7 * t * x / y
          have ht' : t' ≠ 0 := by
            dsimp only [t']
            exact div_ne_zero
              (mul_ne_zero (mul_ne_zero (by norm_num) ht) hx) hy0
          have hy' : y' = t' ^ 3 := by
            dsimp only [y', t']
            rw [addY_neg_threeTorsionOrigin_cubeClass hP hx hy0, hy]
            field_simp [hy0]
            ring
          obtain ⟨R, hR⟩ :=
            exists_eq_three_nsmul_of_Y_eq_cube htarget hP' ht' hy'
          have hsum :
              WeierstrassCurve.Affine.Point.some x y hP +
                  -threeTorsionOrigin = (3 : ℕ) • R := by
            calc
              WeierstrassCurve.Affine.Point.some x y hP +
                    -threeTorsionOrigin =
                  WeierstrassCurve.Affine.Point.some x' y' hP' := by
                rw [threeTorsionOrigin,
                  WeierstrassCurve.Affine.Point.neg_some]
                norm_num [WeierstrassCurve.Affine.negY,
                  threeTorsionCurve]
                exact WeierstrassCurve.Affine.Point.add_of_X_ne hx
              _ = (3 : ℕ) • R := hR
          refine ⟨⟨1, by norm_num⟩, R, ?_⟩
          rw [normalizedThreeRepresentative]
          norm_num
          calc
            WeierstrassCurve.Affine.Point.some x y hP =
                threeTorsionOrigin +
                  (WeierstrassCurve.Affine.Point.some x y hP +
                    -threeTorsionOrigin) := by abel
            _ = threeTorsionOrigin + (3 : ℕ) • R := by rw [hsum]

/-- Once target surjectivity is supplied, the checked source cube-class
calculation discharges the complete three-coset certificate. -/
theorem threeCosetBound_of_targetCandidateSurjective
    (htarget : TargetThreeCandidateSurjective) :
    ThreeCosetBound :=
  threeCosetBound_of_descent_inputs sourceThreeCubeClassBound htarget

/-- End-to-end rank-zero consumer of the two isolated fixed descent
calculations. -/
theorem optimalQuotientModel_rank_zero_of_three_descent_inputs
    (hsource : SourceThreeCubeClassBound)
    (htarget : TargetThreeCandidateSurjective) :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 :=
  optimalQuotientModel_point_rank_zero_of_cosetBound
    (threeCosetBound_of_descent_inputs hsource htarget)

/-- End-to-end finiteness consumer of the two isolated fixed descent
calculations. -/
theorem optimalQuotientModel_finite_of_three_descent_inputs
    (hsource : SourceThreeCubeClassBound)
    (htarget : TargetThreeCandidateSurjective) :
    Finite optimalQuotientModel.toAffine.Point :=
  optimalQuotientModel_point_finite_of_cosetBound
    (threeCosetBound_of_descent_inputs hsource htarget)

/-- Rank-zero consumer with the source local calculation fully discharged. -/
theorem optimalQuotientModel_rank_zero_of_targetCandidateSurjective
    (htarget : TargetThreeCandidateSurjective) :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 :=
  optimalQuotientModel_point_rank_zero_of_cosetBound
    (threeCosetBound_of_targetCandidateSurjective htarget)

/-- Finiteness consumer with the source local calculation fully discharged. -/
theorem optimalQuotientModel_finite_of_targetCandidateSurjective
    (htarget : TargetThreeCandidateSurjective) :
    Finite optimalQuotientModel.toAffine.Point :=
  optimalQuotientModel_point_finite_of_cosetBound
    (threeCosetBound_of_targetCandidateSurjective htarget)

end MazurTorsion.OrderThirtyFive

end

/- Source: MazurTorsion/NumberTheory/OrderThirtyFiveTargetCubic.lean -/

section

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# The cyclic cubic fibre of the order-35 three-isogeny candidate

For a point `(X,Y)` on the candidate target, a source abscissa above it has
to be a root of

`t^3 - X*t^2 + 28*t + 49`.

This file makes that fibre calculation into a checked interface.  Its
discriminant is `49` times the completed-square equation of the target, so
at a rational target point it is the square `(7*(2Y+4X+7))^2`.  Conversely,
any rational root of the fibre gives an explicit source point mapping to
`(X,Y)`.  Thus the remaining target descent can be stated exactly as a
rational-root problem for this fixed family of cyclic cubics; no additivity
claim about the coordinate candidate is used.
-/

open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

open WeierstrassCurve.Affine

/-- The cubic whose rational roots are source abscissae above target
abscissa `X`. -/
def targetCubicFibre (X t : ℚ) : ℚ :=
  t ^ 3 - X * t ^ 2 + 28 * t + 49

/-- The standard coefficient discriminant of a cubic
`a*t^3+b*t^2+c*t+d`. -/
def targetCubicDiscriminant (a b c d : ℚ) : ℚ :=
  b ^ 2 * c ^ 2 - 4 * a * c ^ 3 - 4 * b ^ 3 * d -
    27 * a ^ 2 * d ^ 2 + 18 * a * b * c * d

/-- The fibre discriminant is `49` times the target completed-square
polynomial. -/
theorem targetCubicFibre_discriminant (X : ℚ) :
    targetCubicDiscriminant 1 (-X) 28 49 =
      49 * (4 * X ^ 3 + 16 * X ^ 2 - 504 * X - 3115) := by
  simp only [targetCubicDiscriminant]
  ring

/-- The target equation in completed-ordinate coordinates. -/
theorem veluThreeCandidateTarget_completedEquation
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    (2 * Y + 4 * X + 7) ^ 2 =
      4 * X ^ 3 + 16 * X ^ 2 - 504 * X - 3115 := by
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [veluThreeCandidateTarget] at hcurve
  linear_combination 4 * hcurve

/-- At a target point the fibre discriminant has the displayed rational
square root. -/
theorem targetCubicFibre_discriminant_eq_square
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    targetCubicDiscriminant 1 (-X) 28 49 =
      (7 * (2 * Y + 4 * X + 7)) ^ 2 := by
  rw [targetCubicFibre_discriminant,
    ← veluThreeCandidateTarget_completedEquation hP]
  ring

/-- The completed ordinate of an affine target point is nonzero.  A zero
would make the point rational two-torsion, whereas the checked target
torsion subgroup is trivial. -/
theorem veluThreeCandidateTarget_completedOrdinate_ne_zero
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    2 * Y + 4 * X + 7 ≠ 0 := by
  have hxy : Y^2 + 4*X*Y + 7*Y = X^3 - 140*X - 791 := by
    simpa [WeierstrassCurve.Affine.equation_iff, veluThreeCandidateTarget,
      add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using hP.1
  exact normalized35_completedOrdinate_ne_zero hxy

/-- The fibre discriminant at an affine target point is nonzero. -/
theorem targetCubicFibre_discriminant_ne_zero
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    targetCubicDiscriminant 1 (-X) 28 49 ≠ 0 := by
  rw [targetCubicFibre_discriminant_eq_square hP]
  exact pow_ne_zero 2 (mul_ne_zero (by norm_num)
    (veluThreeCandidateTarget_completedOrdinate_ne_zero hP))

/-- A root of the fibre is nonzero, since its constant term is `49`. -/
theorem targetCubicFibre_root_ne_zero
    {X t : ℚ} (hroot : targetCubicFibre X t = 0) : t ≠ 0 := by
  intro ht
  subst t
  norm_num [targetCubicFibre] at hroot

/-- A fibre root recovers the target abscissa through the first candidate
formula. -/
theorem veluThreeCandidateX_eq_of_targetCubicFibre_root
    {X t : ℚ} (hroot : targetCubicFibre X t = 0) :
    veluThreeCandidateX t = X := by
  have ht := targetCubicFibre_root_ne_zero hroot
  simp only [targetCubicFibre, veluThreeCandidateX] at hroot ⊢
  field_simp [ht]
  linear_combination hroot

/-- The formal derivative of the fibre, written as a rational function at
a root.  This identity exhibits directly why the inverse ordinate
denominator is the nonvanishing derivative factor. -/
theorem targetCubicFibre_derivative_at_root
    {X t : ℚ} (hroot : targetCubicFibre X t = 0) :
    3 * t ^ 2 - 2 * X * t + 28 =
      (t ^ 3 - 28 * t - 98) / t := by
  have ht := targetCubicFibre_root_ne_zero hroot
  simp only [targetCubicFibre] at hroot
  field_simp [ht]
  linear_combination 2 * hroot

/-- The completed-square polynomial transforms by the square of the
completed-ordinate multiplier of the first candidate. -/
theorem targetCompletedPolynomial_candidateX
    {t : ℚ} (ht : t ≠ 0) :
    4 * veluThreeCandidateX t ^ 3 +
          16 * veluThreeCandidateX t ^ 2 -
          504 * veluThreeCandidateX t - 3115 =
      (4 * t ^ 3 + 16 * t ^ 2 + 56 * t + 49) *
        ((t ^ 3 - 28 * t - 98) / t ^ 3) ^ 2 := by
  simp only [veluThreeCandidateX]
  field_simp [ht]
  ring

/-- The ordinate multiplier cannot vanish above an affine target point. -/
theorem targetCubicFibre_multiplier_ne_zero
    {X Y t : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y)
    (hroot : targetCubicFibre X t = 0) :
    t ^ 3 - 28 * t - 98 ≠ 0 := by
  intro hmult
  have ht := targetCubicFibre_root_ne_zero hroot
  have hX := veluThreeCandidateX_eq_of_targetCubicFibre_root hroot
  have htarget := veluThreeCandidateTarget_completedEquation hP
  have htransform := targetCompletedPolynomial_candidateX ht
  rw [hX] at htransform
  rw [← htarget] at htransform
  have hzero : (2 * Y + 4 * X + 7) ^ 2 = 0 := by
    rw [htransform, hmult]
    norm_num
  exact veluThreeCandidateTarget_completedOrdinate_ne_zero hP
    (sq_eq_zero_iff.mp hzero)

/-- The explicit source ordinate associated to a target point and one
rational fibre root. -/
def targetCubicPreimageY (Y t : ℚ) : ℚ :=
  (Y * t ^ 3 + 112 * t ^ 2 + 392 * t + 343) /
    (t ^ 3 - 28 * t - 98)

/-- The explicit inverse ordinate evaluates under the first candidate to
the prescribed target ordinate. -/
theorem veluThreeCandidateY_targetCubicPreimageY
    {X Y t : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y)
    (hroot : targetCubicFibre X t = 0) :
    veluThreeCandidateY t (targetCubicPreimageY Y t) = Y := by
  have ht := targetCubicFibre_root_ne_zero hroot
  have hmult := targetCubicFibre_multiplier_ne_zero hP hroot
  simp only [veluThreeCandidateY]
  rw [div_eq_iff (pow_ne_zero 3 ht)]
  rw [show
      t ^ 3 * targetCubicPreimageY Y t -
            28 * t * targetCubicPreimageY Y t -
            98 * targetCubicPreimageY Y t =
        (t ^ 3 - 28 * t - 98) * targetCubicPreimageY Y t by
      ring]
  simp only [targetCubicPreimageY]
  rw [mul_div_cancel₀ _ hmult]
  ring

/-- The residual of the target equation at the candidate coordinates is
the source residual times the square of the ordinate multiplier. -/
theorem veluThreeCandidate_equation_residual
    {t y : ℚ} (ht : t ≠ 0) :
    veluThreeCandidateY t y ^ 2 +
          4 * veluThreeCandidateX t * veluThreeCandidateY t y +
          7 * veluThreeCandidateY t y -
          (veluThreeCandidateX t ^ 3 -
            140 * veluThreeCandidateX t - 791) =
      ((t ^ 3 - 28 * t - 98) / t ^ 3) ^ 2 *
        (y ^ 2 + 4 * t * y + 7 * y - t ^ 3) := by
  simp only [veluThreeCandidateX, veluThreeCandidateY]
  field_simp [ht]
  ring

/-- The point reconstructed from a rational fibre root lies on the source
curve. -/
theorem targetCubicPreimage_nonsingular
    {X Y t : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y)
    (hroot : targetCubicFibre X t = 0) :
    threeTorsionCurve.toAffine.Nonsingular t
      (targetCubicPreimageY Y t) := by
  apply threeTorsionCurve.toAffine.equation_iff_nonsingular.mp
  rw [WeierstrassCurve.Affine.equation_iff]
  norm_num [threeTorsionCurve]
  have ht := targetCubicFibre_root_ne_zero hroot
  have hmult := targetCubicFibre_multiplier_ne_zero hP hroot
  have hX := veluThreeCandidateX_eq_of_targetCubicFibre_root hroot
  have hY := veluThreeCandidateY_targetCubicPreimageY hP hroot
  have hcurve := hP.1
  rw [WeierstrassCurve.Affine.equation_iff] at hcurve
  norm_num [veluThreeCandidateTarget] at hcurve
  have hresidual := veluThreeCandidate_equation_residual
    (y := targetCubicPreimageY Y t) ht
  rw [hX, hY] at hresidual
  have hfactor :
      ((t ^ 3 - 28 * t - 98) / t ^ 3) ^ 2 ≠ 0 := by
    exact pow_ne_zero 2 (div_ne_zero hmult (pow_ne_zero 3 ht))
  apply sub_eq_zero.mp
  apply mul_left_cancel₀ hfactor
  rw [← hresidual]
  linear_combination hcurve

/-- A rational root of the cubic fibre gives an explicit source point
mapping to the prescribed affine target point. -/
theorem exists_veluThreeCandidate_preimage_of_targetCubicFibre_root
    {X Y t : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y)
    (hroot : targetCubicFibre X t = 0) :
    ∃ Q : threeTorsionCurve.toAffine.Point,
      veluThreeCandidatePointFun Q =
        WeierstrassCurve.Affine.Point.some X Y hP := by
  have ht := targetCubicFibre_root_ne_zero hroot
  let hsource := targetCubicPreimage_nonsingular hP hroot
  refine ⟨WeierstrassCurve.Affine.Point.some t
    (targetCubicPreimageY Y t) hsource, ?_⟩
  simp only [veluThreeCandidatePointFun, ht]
  apply WeierstrassCurve.Affine.Point.some_eq_some
    veluThreeCandidateTarget
  · exact veluThreeCandidateX_eq_of_targetCubicFibre_root hroot
  · exact veluThreeCandidateY_targetCubicPreimageY hP hroot

/-- The exact rational-root input remaining in the target descent. -/
def TargetCubicFibreRoots : Prop :=
  ∀ {X Y : ℚ},
    veluThreeCandidateTarget.toAffine.Nonsingular X Y →
      ∃ t : ℚ, targetCubicFibre X t = 0

/-- Solving every affine cubic fibre proves surjectivity of the fixed point
function, including the point at infinity. -/
theorem targetThreeCandidateSurjective_of_cubicFibreRoots
    (hroots : TargetCubicFibreRoots) :
    TargetThreeCandidateSurjective := by
  intro P
  cases P with
  | zero =>
      exact ⟨0, veluThreeCandidatePointFun_zero⟩
  | some X Y hP =>
      obtain ⟨t, ht⟩ := hroots hP
      exact exists_veluThreeCandidate_preimage_of_targetCubicFibre_root
        hP ht

/-- Conversely, any candidate preimage exposes a rational root of the
cubic fibre. -/
theorem exists_targetCubicFibre_root_of_candidate_preimage
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y)
    (hpreimage : ∃ Q : threeTorsionCurve.toAffine.Point,
      veluThreeCandidatePointFun Q =
        WeierstrassCurve.Affine.Point.some X Y hP) :
    ∃ t : ℚ, targetCubicFibre X t = 0 := by
  obtain ⟨Q, hQ⟩ := hpreimage
  cases Q with
  | zero =>
      simp only [veluThreeCandidatePointFun] at hQ
      exact (WeierstrassCurve.Affine.Point.some_ne_zero hP hQ.symm).elim
  | some t y htPoint =>
      by_cases ht : t = 0
      · simp only [veluThreeCandidatePointFun, ht] at hQ
        exact (WeierstrassCurve.Affine.Point.some_ne_zero hP hQ.symm).elim
      · have hX : veluThreeCandidateX t = X := by
          simp only [veluThreeCandidatePointFun, ht] at hQ
          exact (WeierstrassCurve.Affine.Point.some.inj hQ).1
        refine ⟨t, ?_⟩
        simp only [targetCubicFibre, veluThreeCandidateX] at hX ⊢
        field_simp [ht] at hX
        linear_combination hX

/-- The cubic rational-root condition is exactly the target-surjectivity
condition already consumed by the order-35 rank boundary. -/
theorem targetCubicFibreRoots_iff_targetThreeCandidateSurjective :
    TargetCubicFibreRoots ↔ TargetThreeCandidateSurjective := by
  constructor
  · exact targetThreeCandidateSurjective_of_cubicFibreRoots
  · intro hsurj X Y hP
    exact exists_targetCubicFibre_root_of_candidate_preimage hP
      (hsurj (WeierstrassCurve.Affine.Point.some X Y hP))

/-! ## The nontrivial Eisenstein-unit cover

Putting the candidate target in Cohen--Pazuki form gives

`v² = u³ - 3(12u+1500)²`.

For either nontrivial unit cube-class in `ℤ[ζ₃]`, their homogeneous
three-descent cubic is, up to conjugating `Y`, the form below.  Modulo seven
it has only the zero solution, hence an integral solution would be divisible
by arbitrarily high powers of seven.  The minimal-size argument below
packages that infinite descent without any unproved unique-factorization
step.
-/

/-- The abscissa change from the checked candidate target to the integral
dual three-descent model. -/
def targetThreeDescentU (X : ℚ) : ℚ :=
  36 * X + 192

/-- The ordinate change to the integral dual three-descent model. -/
def targetThreeDescentV (X Y : ℚ) : ℚ :=
  108 * (2 * Y + 4 * X + 7)

/-- The candidate target is explicitly the dual three-descent model
`v² = u³ - 3(12u+1500)²`, with parameters
`D=-3`, `a=12`, and `b=1500`. -/
theorem targetThreeDescent_equation
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    targetThreeDescentV X Y ^ 2 =
      targetThreeDescentU X ^ 3 -
        3 * (12 * targetThreeDescentU X + 1500) ^ 2 := by
  simp only [targetThreeDescentV, targetThreeDescentU]
  linear_combination
    11664 * veluThreeCandidateTarget_completedEquation hP

/-- The fixed homogeneous cubic for a nontrivial Eisenstein-unit class in
the target three-descent. -/
def targetEisensteinUnitCover (X Y Z : ℤ) : ℤ :=
  X ^ 3 - 3 * Y ^ 3 + 3000 * Z ^ 3 + 3 * X ^ 2 * Y -
    9 * X * Y ^ 2 + 24 * X ^ 2 * Z + 72 * Y ^ 2 * Z

/-- The unit-cover cubic is homogeneous of degree three. -/
theorem targetEisensteinUnitCover_scale (r X Y Z : ℤ) :
    targetEisensteinUnitCover (r * X) (r * Y) (r * Z) =
      r ^ 3 * targetEisensteinUnitCover X Y Z := by
  simp only [targetEisensteinUnitCover]
  ring

private theorem targetEisensteinUnitCover_modSeven_only_zero :
    ∀ X Y Z : ZMod 7,
      X ^ 3 - 3 * Y ^ 3 + 3000 * Z ^ 3 + 3 * X ^ 2 * Y -
          9 * X * Y ^ 2 + 24 * X ^ 2 * Z + 72 * Y ^ 2 * Z = 0 →
        X = 0 ∧ Y = 0 ∧ Z = 0 := by
  decide

/-- Every integral zero of the nontrivial-unit cover is coordinatewise
divisible by seven. -/
theorem seven_dvd_targetEisensteinUnitCover_zero
    {X Y Z : ℤ}
    (hcover : targetEisensteinUnitCover X Y Z = 0) :
    (7 : ℤ) ∣ X ∧ (7 : ℤ) ∣ Y ∧ (7 : ℤ) ∣ Z := by
  have hcast := congrArg (fun n : ℤ ↦ (n : ZMod 7)) hcover
  have hmod :
      (X : ZMod 7) ^ 3 - 3 * (Y : ZMod 7) ^ 3 +
            3000 * (Z : ZMod 7) ^ 3 +
            3 * (X : ZMod 7) ^ 2 * (Y : ZMod 7) -
          9 * (X : ZMod 7) * (Y : ZMod 7) ^ 2 +
        24 * (X : ZMod 7) ^ 2 * (Z : ZMod 7) +
      72 * (Y : ZMod 7) ^ 2 * (Z : ZMod 7) = 0 := by
    simpa [targetEisensteinUnitCover] using hcast
  obtain ⟨hX, hY, hZ⟩ :=
    targetEisensteinUnitCover_modSeven_only_zero
      (X : ZMod 7) (Y : ZMod 7) (Z : ZMod 7) hmod
  exact ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd X 7).mp hX,
    (ZMod.intCast_zmod_eq_zero_iff_dvd Y 7).mp hY,
    (ZMod.intCast_zmod_eq_zero_iff_dvd Z 7).mp hZ⟩

/-- The nontrivial Eisenstein-unit cover has no nonzero integral point. -/
theorem targetEisensteinUnitCover_no_nonzero_integer_solution
    (X Y Z : ℤ)
    (hcover : targetEisensteinUnitCover X Y Z = 0) :
    X = 0 ∧ Y = 0 ∧ Z = 0 := by
  classical
  by_contra hnonzero
  let sizes : Set ℕ :=
    {n | ∃ x y z : ℤ,
      targetEisensteinUnitCover x y z = 0 ∧
        ¬(x = 0 ∧ y = 0 ∧ z = 0) ∧
        x.natAbs + y.natAbs + z.natAbs = n}
  have hsizes : sizes.Nonempty := by
    refine ⟨X.natAbs + Y.natAbs + Z.natAbs, X, Y, Z,
      hcover, hnonzero, rfl⟩
  let n : ℕ := Nat.find hsizes
  obtain ⟨x, y, z, hxyz, hxyz0, hsize⟩ := Nat.find_spec hsizes
  obtain ⟨⟨x', hx⟩, ⟨y', hy⟩, ⟨z', hz⟩⟩ :=
    seven_dvd_targetEisensteinUnitCover_zero hxyz
  have hscaled : targetEisensteinUnitCover x' y' z' = 0 := by
    have hhom := targetEisensteinUnitCover_scale (7 : ℤ) x' y' z'
    rw [← hx, ← hy, ← hz, hxyz] at hhom
    norm_num at hhom
    exact hhom
  have hscaled0 : ¬(x' = 0 ∧ y' = 0 ∧ z' = 0) := by
    rintro ⟨rfl, rfl, rfl⟩
    have hx0 : x = 0 := by simpa using hx
    have hy0 : y = 0 := by simpa using hy
    have hz0 : z = 0 := by simpa using hz
    exact hxyz0 ⟨hx0, hy0, hz0⟩
  have hnew : x'.natAbs + y'.natAbs + z'.natAbs ∈ sizes :=
    ⟨x', y', z', hscaled, hscaled0, rfl⟩
  have hpositive : 0 < x'.natAbs + y'.natAbs + z'.natAbs := by
    omega
  have hfactor :
      x.natAbs + y.natAbs + z.natAbs =
        7 * (x'.natAbs + y'.natAbs + z'.natAbs) := by
    rw [hx, hy, hz]
    simp only [Int.natAbs_mul]
    norm_num
    omega
  have hless : x'.natAbs + y'.natAbs + z'.natAbs < n := by
    change x'.natAbs + y'.natAbs + z'.natAbs < Nat.find hsizes
    rw [← hsize, hfactor]
    omega
  exact (Nat.not_lt_of_ge (Nat.find_min' hsizes hnew)) hless

/-- The homogeneous cubic for the conjugate nontrivial unit class. -/
def targetEisensteinConjugateUnitCover (X Y Z : ℤ) : ℤ :=
  -X ^ 3 - 3 * Y ^ 3 + 3000 * Z ^ 3 + 3 * X ^ 2 * Y +
    9 * X * Y ^ 2 + 24 * X ^ 2 * Z + 72 * Y ^ 2 * Z

/-- Conjugating the Eisenstein unit class changes the second and third
homogeneous coordinates by sign. -/
theorem targetEisensteinConjugateUnitCover_eq
    (X Y Z : ℤ) :
    targetEisensteinConjugateUnitCover X Y Z =
      -targetEisensteinUnitCover X (-Y) (-Z) := by
  simp only [targetEisensteinConjugateUnitCover,
    targetEisensteinUnitCover]
  ring

/-- The conjugate nontrivial unit cover also has no nonzero integral
point. -/
theorem targetEisensteinConjugateUnitCover_no_nonzero_integer_solution
    (X Y Z : ℤ)
    (hcover : targetEisensteinConjugateUnitCover X Y Z = 0) :
    X = 0 ∧ Y = 0 ∧ Z = 0 := by
  have hunit : targetEisensteinUnitCover X (-Y) (-Z) = 0 := by
    rw [targetEisensteinConjugateUnitCover_eq] at hcover
    linarith
  obtain ⟨hX, hY, hZ⟩ :=
    targetEisensteinUnitCover_no_nonzero_integer_solution
      X (-Y) (-Z) hunit
  exact ⟨hX, neg_eq_zero.mp hY, neg_eq_zero.mp hZ⟩

/-- The exact global-algebra output still required from the dual
three-descent.  It says that a target point either has a rational fibre
root (the trivial Eisenstein unit class), or supplies a nonzero integral
point on one of the two nontrivial unit covers.  The class-number-one and
prime-support argument over `ℤ[ζ₃]` is precisely the missing proof of this
proposition; the two local-obstruction branches are checked above. -/
def TargetEisensteinDescentReduction : Prop :=
  ∀ {X Y : ℚ},
    veluThreeCandidateTarget.toAffine.Nonsingular X Y →
      (∃ t : ℚ, targetCubicFibre X t = 0) ∨
      (∃ A B C : ℤ,
        targetEisensteinUnitCover A B C = 0 ∧
          ¬(A = 0 ∧ B = 0 ∧ C = 0)) ∨
      ∃ A B C : ℤ,
        targetEisensteinConjugateUnitCover A B C = 0 ∧
          ¬(A = 0 ∧ B = 0 ∧ C = 0)

/-- Once the global Eisenstein descent has reduced the target points to
the three unit classes, the two mod-seven infinite descents force every
target fibre to have a rational root. -/
theorem targetCubicFibreRoots_of_eisensteinDescentReduction
    (hdescent : TargetEisensteinDescentReduction) :
    TargetCubicFibreRoots := by
  intro X Y hP
  rcases hdescent hP with hroot | hunit | hconjugate
  · exact hroot
  · obtain ⟨A, B, C, hcover, hnonzero⟩ := hunit
    exact (hnonzero
      (targetEisensteinUnitCover_no_nonzero_integer_solution
        A B C hcover)).elim
  · obtain ⟨A, B, C, hcover, hnonzero⟩ := hconjugate
    exact (hnonzero
      (targetEisensteinConjugateUnitCover_no_nonzero_integer_solution
        A B C hcover)).elim

/-- The exact global Eisenstein reduction has a checked end-to-end
rank-zero consumer. -/
theorem optimalQuotientModel_rank_zero_of_eisensteinDescentReduction
    (hdescent : TargetEisensteinDescentReduction) :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 :=
  optimalQuotientModel_rank_zero_of_targetCandidateSurjective
    (targetThreeCandidateSurjective_of_cubicFibreRoots
      (targetCubicFibreRoots_of_eisensteinDescentReduction hdescent))

/-- The cubic-fibre input has a checked end-to-end rank-zero consumer. -/
theorem optimalQuotientModel_rank_zero_of_targetCubicFibreRoots
    (hroots : TargetCubicFibreRoots) :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 :=
  optimalQuotientModel_rank_zero_of_targetCandidateSurjective
    (targetThreeCandidateSurjective_of_cubicFibreRoots hroots)

/-- The cubic-fibre input has a checked end-to-end finiteness consumer. -/
theorem optimalQuotientModel_finite_of_targetCubicFibreRoots
    (hroots : TargetCubicFibreRoots) :
    Finite optimalQuotientModel.toAffine.Point :=
  optimalQuotientModel_finite_of_targetCandidateSurjective
    (targetThreeCandidateSurjective_of_cubicFibreRoots hroots)

end MazurTorsion.OrderThirtyFive

end

/- Source: MazurTorsion/NumberTheory/OrderThirtyFiveEisensteinDescent.lean -/

section

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Eisenstein factor arithmetic for the order-35 target descent

This file clears denominators on the fixed target model

`v² = u³ - 3(12u + 1500)²`

and factors the resulting norm equation in the ring of integers of a third
cyclotomic field.  If the negative factor is associated to a cube, Mathlib's
classification of the six Eisenstein units gives exactly three cases.  The
trivial unit has the explicit rational cubic-fibre root

`t = -42d / (c + 8d)`,

while the other two conjugate pairs produce the homogeneous cubics already
excluded by the checked mod-seven infinite descents.  Consequently the exact
associated-cube statement has a compiled consumer proving target-candidate
surjectivity and rank zero.

The global input is deliberately isolated as
`TargetEisensteinAssociatedCube`: it is the ideal-support calculation from
Cohen--Pazuki, Theorem 4.1 and Corollary 4.3.  It is proved from the primitive
denominator data in `OrderThirtyFiveEisensteinIdealSupport`, rather than being
inferred from class number one alone.
-/

open NumberField
open Polynomial
open WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

/-- Integral data obtained by clearing a target point's denominators.  Its
last equation is the Eisenstein norm factorization to be descended. -/
structure TargetEisensteinIntegralData (U V : ℚ) where
  d : ℤ
  m : ℤ
  n : ℤ
  b : ℤ
  d_ne_zero : d ≠ 0
  U_eq : U = (m : ℚ) / (d : ℚ) ^ 2
  V_eq : V = (n : ℚ) / (d : ℚ) ^ 3
  b_eq : b = d * (12 * m + 1500 * d ^ 2)
  norm_eq : n ^ 2 + 3 * b ^ 2 = m ^ 3

/-- The denominator presentation used by the ideal-support argument.  The
positive `d` is the square denominator of `U`; both numerators are primitive
with respect to it. -/
structure TargetEisensteinNormalizedIntegralData (U V : ℚ)
    extends TargetEisensteinIntegralData U V where
  d_pos : 0 < d
  m_coprime_d : IsCoprime m d
  n_coprime_d : IsCoprime n d

private theorem targetEisensteinNormalizedIntegralData_of_equation
    {U V : ℚ}
    (hcurve : V ^ 2 = U ^ 3 - 3 * (12 * U + 1500) ^ 2) :
    Nonempty (TargetEisensteinNormalizedIntegralData U V) := by
  let m : ℤ := U.num
  let q : ℕ := U.den
  let A : ℤ := m ^ 3 - 3 * (q : ℤ) * (12 * m + 1500 * q) ^ 2
  have hqpos : 0 < q := by
    dsimp only [q]
    exact U.den_pos
  have hq0Q : (q : ℚ) ≠ 0 := by positivity
  have hU : U = (m : ℚ) / (q : ℚ) := by
    simpa [m, q] using U.num_div_den.symm
  have hcurve' : V ^ 2 = (A : ℚ) / (q : ℚ) ^ 3 := by
    rw [hU] at hcurve
    dsimp only [A]
    push_cast
    field_simp [hq0Q] at hcurve ⊢
    linear_combination hcurve
  have hmq : IsCoprime m (q : ℤ) := by
    simpa [m, q] using Rat.isCoprime_num_den U
  have hAq : IsCoprime A ((q : ℤ) ^ 3) := by
    have hbase : IsCoprime A (q : ℤ) := by
      have hpow : IsCoprime (m ^ 3) (q : ℤ) := hmq.pow_left
      have h := hpow.add_mul_left_left
        (-3 * (12 * m + 1500 * (q : ℤ)) ^ 2)
      have heq : m ^ 3 + (q : ℤ) *
          (-3 * (12 * m + 1500 * (q : ℤ)) ^ 2) = A := by
        dsimp only [A]
        ring
      rw [← heq]
      exact h
    exact hbase.pow_right
  have hdenCast : (((V ^ 2).den : ℤ)) = (q : ℤ) ^ 3 := by
    rw [hcurve']
    exact Rat.den_div_eq_of_coprime (by positivity)
      (Int.isCoprime_iff_nat_coprime.mp hAq)
  have hden : V.den ^ 2 = q ^ 3 := by
    rw [Rat.den_pow] at hdenCast
    exact_mod_cast hdenCast
  have hq_dvd_vden : q ∣ V.den := by
    apply (UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd
      (R := ℕ) (n := 2) (by norm_num)).mp
    rw [hden]
    exact ⟨q, by ring⟩
  obtain ⟨d, hd⟩ := hq_dvd_vden
  have hq_sq : q = d ^ 2 := by
    have hmul : q ^ 2 * q = q ^ 2 * d ^ 2 := by
      calc
        q ^ 2 * q = q ^ 3 := by ring
        _ = V.den ^ 2 := hden.symm
        _ = q ^ 2 * d ^ 2 := by rw [hd]; ring
    exact Nat.eq_of_mul_eq_mul_left (by positivity) hmul
  have hdpos : 0 < d := by
    by_contra hd0
    simp only [not_lt, nonpos_iff_eq_zero] at hd0
    subst d
    norm_num at hq_sq
    exact hqpos.ne' hq_sq
  have hd0Z : (d : ℤ) ≠ 0 := by positivity
  have hd0Q : (d : ℚ) ≠ 0 := by positivity
  have hU' : U = (m : ℚ) / (d : ℚ) ^ 2 := by
    rw [hU, hq_sq]
    norm_cast
  let W : ℚ := V * (d : ℚ) ^ 3
  let B : ℤ := m ^ 3 - 3 * (d : ℤ) ^ 2 *
    (12 * m + 1500 * (d : ℤ) ^ 2) ^ 2
  have hWsq : W ^ 2 = (B : ℚ) := by
    dsimp only [W, B]
    rw [hU'] at hcurve
    field_simp [hd0Q] at hcurve
    push_cast
    linear_combination hcurve
  let p : ℤ[X] := Polynomial.X ^ 2 - Polynomial.C B
  have hp : p.Monic := by
    dsimp only [p]
    exact Polynomial.monic_X_pow_sub_C B (by norm_num)
  have hroot : Polynomial.aeval W p = 0 := by
    dsimp only [p]
    simp only [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    exact sub_eq_zero.mpr hWsq
  obtain ⟨n, hn, -⟩ := exists_integer_of_is_root_of_monic hp hroot
  have hV' : V = (n : ℚ) / (d : ℚ) ^ 3 := by
    dsimp only [W] at hn
    field_simp [hd0Q]
    exact hn
  let b : ℤ := (d : ℤ) * (12 * m + 1500 * (d : ℤ) ^ 2)
  have hnorm : n ^ 2 + 3 * b ^ 2 = m ^ 3 := by
    have hWsq' := hWsq
    rw [hn] at hWsq'
    have hnBcast : ((n ^ 2 : ℤ) : ℚ) = (B : ℚ) := by
      simpa using hWsq'
    have hnB : n ^ 2 = B := by exact_mod_cast hnBcast
    dsimp only [B, b] at hnB ⊢
    linear_combination hnB
  have hmd : IsCoprime m (d : ℤ) := by
    have hm_dsq : IsCoprime m ((d : ℤ) ^ 2) := by
      simpa [hq_sq] using hmq
    exact hm_dsq.of_isCoprime_of_dvd_right ⟨d, by ring⟩
  have hnd : IsCoprime n (d : ℤ) := by
    apply isCoprime_of_prime_dvd
    · rintro ⟨-, hdzero⟩
      exact hd0Z hdzero
    · intro p hp hpn hpd
      have hpb : p ∣ b := by
        exact hpd.trans ⟨12 * m + 1500 * (d : ℤ) ^ 2, rfl⟩
      have hpm3 : p ∣ m ^ 3 := by
        rw [← hnorm]
        have hpn2 : p ∣ n ^ 2 := by
          simpa [pow_two] using hpn.mul_right n
        have hpb2 : p ∣ b ^ 2 := by
          simpa [pow_two] using hpb.mul_right b
        exact dvd_add hpn2 (hpb2.mul_left 3)
      have hpm : p ∣ m := hp.dvd_of_dvd_pow hpm3
      exact hp.not_unit (hmd.isUnit_of_dvd' hpm hpd)
  refine ⟨
    { d := d
      m := m
      n := n
      b := b
      d_ne_zero := hd0Z
      U_eq := hU'
      V_eq := hV'
      b_eq := rfl
      norm_eq := hnorm
      d_pos := by exact_mod_cast hdpos
      m_coprime_d := hmd
      n_coprime_d := hnd }⟩

/-- Every affine target point has a positive primitive denominator
presentation. -/
theorem targetEisensteinNormalizedIntegralData
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    Nonempty (TargetEisensteinNormalizedIntegralData
      (targetThreeDescentU X) (targetThreeDescentV X Y)) := by
  apply targetEisensteinNormalizedIntegralData_of_equation
  exact targetThreeDescent_equation hP

/-- Forgetting primitivity recovers the original denominator-cleared
interface. -/
theorem targetEisensteinIntegralData
    {X Y : ℚ}
    (hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y) :
    Nonempty (TargetEisensteinIntegralData (targetThreeDescentU X)
      (targetThreeDescentV X Y)) := by
  obtain ⟨D⟩ := targetEisensteinNormalizedIntegralData hP
  exact ⟨D.toTargetEisensteinIntegralData⟩

end MazurTorsion.OrderThirtyFive

namespace MazurTorsion.OrderThirtyFive

open IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3)

/-- The element `2ζ₃+1`, whose square is `-3`, in the ring of integers. -/
def eisensteinSqrtNegThree : 𝓞 K :=
  2 * hζ.toInteger + 1

private theorem eisensteinSqrtNegThree_sq :
    eisensteinSqrtNegThree hζ ^ 2 = -3 := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  simp only [eisensteinSqrtNegThree]
  linear_combination 4 * hroot

private theorem eisensteinNormFactor (m n : ℤ) :
    ((m : 𝓞 K) - n * eisensteinSqrtNegThree hζ) *
        ((m : 𝓞 K) + n * eisensteinSqrtNegThree hζ) =
      ((m ^ 2 + 3 * n ^ 2 : ℤ) : 𝓞 K) := by
  calc
    _ = (m : 𝓞 K) ^ 2 - (n : 𝓞 K) ^ 2 *
        eisensteinSqrtNegThree hζ ^ 2 := by ring
    _ = ((m ^ 2 + 3 * n ^ 2 : ℤ) : 𝓞 K) := by
      rw [eisensteinSqrtNegThree_sq]
      push_cast
      ring

private theorem eisensteinEtaCoords_zero_field [CharZero K]
    (hζ : IsPrimitiveRoot ζ 3) {a b : ℤ}
    (h : (a : K) + b * ζ = 0) :
    a = 0 ∧ b = 0 := by
  have hroot := hζ.isRoot_cyclotomic (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  have hnormK : ((a ^ 2 - a * b + b ^ 2 : ℤ) : K) = 0 := by
    calc
      ((a ^ 2 - a * b + b ^ 2 : ℤ) : K) =
          ((a : K) + b * ζ) * ((a - b : ℤ) - b * ζ) := by
            push_cast
            linear_combination (b : K) ^ 2 * hroot
      _ = 0 := by rw [h]; simp
  have hnormZ : a ^ 2 - a * b + b ^ 2 = 0 := by
    exact_mod_cast hnormK
  have hb : b = 0 := by
    nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
  subst b
  norm_num at hnormZ
  exact ⟨hnormZ, rfl⟩

private theorem eisensteinEtaCoords_zero [CharZero K] {a b : ℤ}
    (h : (a : 𝓞 K) + b * hζ.toInteger = 0) :
    a = 0 ∧ b = 0 := by
  have hK := congrArg (fun z : 𝓞 K ↦ (z : K)) h
  change (a : K) + b * ζ = 0 at hK
  exact eisensteinEtaCoords_zero_field hζ hK

/-- Equality in the integral basis `(1, ζ₃)` is coordinatewise. -/
theorem eisensteinEtaCoords_injective [CharZero K] {a b c d : ℤ}
    (h : (a : 𝓞 K) + b * hζ.toInteger =
      (c : 𝓞 K) + d * hζ.toInteger) :
    a = c ∧ b = d := by
  have hK := congrArg (fun z : 𝓞 K ↦ (z : K)) h
  change (a : K) + b * ζ = (c : K) + d * ζ at hK
  have hzero' : ((a - c : ℤ) : K) +
      ((b - d : ℤ) : K) * ζ = 0 := by
    push_cast
    linear_combination hK
  obtain ⟨hac, hbd⟩ :=
    eisensteinEtaCoords_zero_field (a := a - c) (b := b - d) hζ hzero'
  exact ⟨sub_eq_zero.mp hac, sub_eq_zero.mp hbd⟩

private def plusUnitReal (a b : ℤ) : ℤ :=
  a ^ 3 - 3 * a ^ 2 * b + b ^ 3

private def plusUnitEta (a b : ℤ) : ℤ :=
  a ^ 3 - 3 * a * b ^ 2 + b ^ 3

private def minusUnitReal (a b : ℤ) : ℤ :=
  3 * a ^ 2 * b - 3 * a * b ^ 2

private def minusUnitEta (a b : ℤ) : ℤ :=
  -a ^ 3 + 3 * a ^ 2 * b - b ^ 3

private theorem plusUnitNorm (a b : ℤ) :
    plusUnitReal a b ^ 2 -
        plusUnitReal a b * plusUnitEta a b +
      plusUnitEta a b ^ 2 = (a ^ 2 - a * b + b ^ 2) ^ 3 := by
  simp only [plusUnitReal, plusUnitEta]
  ring

private theorem minusUnitNorm (a b : ℤ) :
    minusUnitReal a b ^ 2 -
        minusUnitReal a b * minusUnitEta a b +
      minusUnitEta a b ^ 2 = (a ^ 2 - a * b + b ^ 2) ^ 3 := by
  simp only [minusUnitReal, minusUnitEta]
  ring

private theorem TargetEisensteinIntegralData.unitCover_solution_of_plus_coords
    {U V : ℚ} (D : TargetEisensteinIntegralData U V) (a b : ℤ)
    (hreal : D.n - D.b = plusUnitReal a b)
    (heta : -2 * D.b = plusUnitEta a b) :
    targetEisensteinUnitCover (2 * a - b) b (2 * D.d) = 0 ∧
      ¬(2 * a - b = 0 ∧ b = 0 ∧ 2 * D.d = 0) := by
  let q : ℤ := a ^ 2 - a * b + b ^ 2
  have hcubes : D.m ^ 3 = q ^ 3 := by
    calc
      D.m ^ 3 = D.n ^ 2 + 3 * D.b ^ 2 := D.norm_eq.symm
      _ = (D.n - D.b) ^ 2 -
          (D.n - D.b) * (-2 * D.b) + (-2 * D.b) ^ 2 := by ring
      _ = plusUnitReal a b ^ 2 -
          plusUnitReal a b * plusUnitEta a b +
            plusUnitEta a b ^ 2 := by rw [hreal, heta]
      _ = q ^ 3 := plusUnitNorm a b
  have hm : D.m = q :=
    (show Odd 3 by decide).pow_injective hcubes
  have heta' := heta
  rw [D.b_eq, hm] at heta'
  simp only [plusUnitEta] at heta'
  constructor
  · simp only [targetEisensteinUnitCover]
    dsimp only [q] at heta'
    linear_combination -8 * heta'
  · rintro ⟨-, -, hd⟩
    apply D.d_ne_zero
    linarith

private theorem TargetEisensteinIntegralData.conjugateUnitCover_solution_of_minus_coords
    {U V : ℚ} (D : TargetEisensteinIntegralData U V) (a b : ℤ)
    (hreal : D.n - D.b = minusUnitReal a b)
    (heta : -2 * D.b = minusUnitEta a b) :
    targetEisensteinConjugateUnitCover (2 * a - b) b (2 * D.d) = 0 ∧
      ¬(2 * a - b = 0 ∧ b = 0 ∧ 2 * D.d = 0) := by
  let q : ℤ := a ^ 2 - a * b + b ^ 2
  have hcubes : D.m ^ 3 = q ^ 3 := by
    calc
      D.m ^ 3 = D.n ^ 2 + 3 * D.b ^ 2 := D.norm_eq.symm
      _ = (D.n - D.b) ^ 2 -
          (D.n - D.b) * (-2 * D.b) + (-2 * D.b) ^ 2 := by ring
      _ = minusUnitReal a b ^ 2 -
          minusUnitReal a b * minusUnitEta a b +
            minusUnitEta a b ^ 2 := by rw [hreal, heta]
      _ = q ^ 3 := minusUnitNorm a b
  have hm : D.m = q :=
    (show Odd 3 by decide).pow_injective hcubes
  have heta' := heta
  rw [D.b_eq, hm] at heta'
  simp only [minusUnitEta] at heta'
  constructor
  · simp only [targetEisensteinConjugateUnitCover]
    dsimp only [q] at heta'
    linear_combination -8 * heta'
  · rintro ⟨-, -, hd⟩
    apply D.d_ne_zero
    linarith

private theorem oneAddEta_cube (a b : ℤ) :
    (1 + hζ.toInteger) *
        ((a : 𝓞 K) + b * hζ.toInteger) ^ 3 =
      (plusUnitReal a b : 𝓞 K) +
        plusUnitEta a b * hζ.toInteger := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  have hcube := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hsq : hζ.toInteger ^ 2 = -hζ.toInteger - 1 := by
    linear_combination hroot
  have hfour : hζ.toInteger ^ 4 = hζ.toInteger := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hcube,
      one_mul]
  simp only [plusUnitReal, plusUnitEta]
  push_cast
  ring_nf
  rw [hfour, hcube, hsq]
  ring

private theorem negEta_cube (a b : ℤ) :
    -hζ.toInteger *
        ((a : 𝓞 K) + b * hζ.toInteger) ^ 3 =
      (minusUnitReal a b : 𝓞 K) +
        minusUnitEta a b * hζ.toInteger := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  have hcube := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hsq : hζ.toInteger ^ 2 = -hζ.toInteger - 1 := by
    linear_combination hroot
  have hfour : hζ.toInteger ^ 4 = hζ.toInteger := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hcube,
      one_mul]
  simp only [minusUnitReal, minusUnitEta]
  push_cast
  ring_nf
  rw [hfour, hcube, hsq]
  ring

private def cubeReal (a b : ℤ) : ℤ :=
  a ^ 3 - 3 * a * b ^ 2 + b ^ 3

private def cubeEta (a b : ℤ) : ℤ :=
  3 * a ^ 2 * b - 3 * a * b ^ 2

private theorem eisensteinCube (a b : ℤ) :
    ((a : 𝓞 K) + b * hζ.toInteger) ^ 3 =
      (cubeReal a b : 𝓞 K) +
        cubeEta a b * hζ.toInteger := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  have hcube := hζ.toInteger_isPrimitiveRoot.pow_eq_one
  have hsq : hζ.toInteger ^ 2 = -hζ.toInteger - 1 := by
    linear_combination hroot
  simp only [cubeReal, cubeEta]
  push_cast
  ring_nf
  rw [hcube, hsq]
  ring

/-- The negative Eisenstein factor `n-b√-3` of the cleared norm equation. -/
def TargetEisensteinIntegralData.minusFactor {U V : ℚ}
    (D : TargetEisensteinIntegralData U V) : 𝓞 K :=
  (D.n : 𝓞 K) - D.b * eisensteinSqrtNegThree hζ

/-- The conjugate factor `n+b√-3` of the cleared norm equation. -/
def TargetEisensteinIntegralData.plusFactor {U V : ℚ}
    (D : TargetEisensteinIntegralData U V) : 𝓞 K :=
  (D.n : 𝓞 K) + D.b * eisensteinSqrtNegThree hζ

/-- Coordinates of the negative factor in the integral basis `(1,ζ₃)`. -/
theorem TargetEisensteinIntegralData.minusFactor_coords {U V : ℚ}
    (D : TargetEisensteinIntegralData U V) :
    D.minusFactor hζ =
      ((D.n - D.b : ℤ) : 𝓞 K) +
        (-2 * D.b : ℤ) * hζ.toInteger := by
  simp only [TargetEisensteinIntegralData.minusFactor, eisensteinSqrtNegThree]
  push_cast
  ring

/-- Coordinates of the positive factor in the integral basis `(1,ζ₃)`. -/
theorem TargetEisensteinIntegralData.plusFactor_coords {U V : ℚ}
    (D : TargetEisensteinIntegralData U V) :
    D.plusFactor hζ =
      ((D.n + D.b : ℤ) : 𝓞 K) -
        (-2 * D.b : ℤ) * hζ.toInteger := by
  simp only [TargetEisensteinIntegralData.plusFactor, eisensteinSqrtNegThree]
  push_cast
  ring

/-- The two conjugate Eisenstein factors multiply to the cube `m³`. -/
theorem TargetEisensteinIntegralData.factors_mul {U V : ℚ}
    (D : TargetEisensteinIntegralData U V) :
    D.minusFactor hζ * D.plusFactor hζ = (D.m : 𝓞 K) ^ 3 := by
  rw [TargetEisensteinIntegralData.minusFactor, TargetEisensteinIntegralData.plusFactor,
    eisensteinNormFactor]
  rw [D.norm_eq]
  push_cast
  ring

/-- If the conjugate factors are coprime, unique factorization in the
class-number-one third cyclotomic ring makes the negative factor an
associated cube.  The remaining global support argument must handle the
nonsplit common-prime case as well. -/
theorem TargetEisensteinIntegralData.exists_associated_cube_of_isCoprime
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {U V : ℚ} (D : TargetEisensteinIntegralData U V)
    (hcoprime : IsCoprime (D.minusFactor hζ) (D.plusFactor hζ)) :
    ∃ z : 𝓞 K, Associated (z ^ 3) (D.minusFactor hζ) := by
  letI : IsPrincipalIdealRing (𝓞 K) :=
    IsCyclotomicExtension.Rat.three_pid K
  exact exists_associated_pow_of_mul_eq_pow' hcoprime (D.factors_mul hζ)

/-- Every Eisenstein integer has coordinates in the integral basis
`(1, ζ₃)`. -/
theorem exists_eisenstein_integer_coords
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    (z : 𝓞 K) :
    ∃ a b : ℤ, z = a + b * hζ.toInteger := by
  let pb := hζ.integralPowerBasis
  have hdim : pb.dim = 2 := by
    dsimp only [pb]
    rw [hζ.integralPowerBasis_dim]
    decide
  obtain ⟨f, hfdeg, hz⟩ := pb.exists_eq_aeval z
  have hfdeg' : f.natDegree < 2 := by simpa [hdim] using hfdeg
  let a : ℤ := f.coeff 0
  let b : ℤ := f.coeff 1
  have hf : f = Polynomial.C a +
      Polynomial.C b * Polynomial.X := by
    have hsum := f.as_sum_range' 2 hfdeg'
    norm_num [Finset.sum_range_succ] at hsum
    calc
      f = Polynomial.C (f.coeff 0) +
          Polynomial.monomial 1 (f.coeff 1) := hsum
      _ = Polynomial.C a + Polynomial.C b * Polynomial.X := by
        rw [Polynomial.C_mul_X_eq_monomial]
  refine ⟨a, b, ?_⟩
  calc
    z = Polynomial.aeval pb.gen f := hz
    _ = a + b * hζ.toInteger := by
      rw [hf]
      simp only [map_add, map_mul, Polynomial.aeval_C,
        Polynomial.aeval_X]
      rw [show pb.gen = hζ.toInteger by
        exact hζ.integralPowerBasis_gen]
      have ha : (algebraMap ℤ (𝓞 K)) a = (a : 𝓞 K) := by
        simp
      have hb : (algebraMap ℤ (𝓞 K)) b = (b : 𝓞 K) := by
        simp
      rw [ha, hb]

private theorem TargetEisensteinIntegralData.exists_unitCover_solution_of_plus_cube
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {U V : ℚ} (D : TargetEisensteinIntegralData U V) (z : 𝓞 K)
    (hfactor : D.minusFactor hζ =
      (1 + hζ.toInteger) * z ^ 3) :
    ∃ A B C : ℤ,
      targetEisensteinUnitCover A B C = 0 ∧
        ¬(A = 0 ∧ B = 0 ∧ C = 0) := by
  obtain ⟨a, b, hz⟩ := exists_eisenstein_integer_coords hζ z
  have hcoords :
      ((D.n - D.b : ℤ) : 𝓞 K) +
          (-2 * D.b : ℤ) * hζ.toInteger =
        (plusUnitReal a b : 𝓞 K) +
          plusUnitEta a b * hζ.toInteger := by
    calc
      _ = D.minusFactor hζ := (D.minusFactor_coords hζ).symm
      _ = (1 + hζ.toInteger) * z ^ 3 := hfactor
      _ = (1 + hζ.toInteger) *
          ((a : 𝓞 K) + b * hζ.toInteger) ^ 3 := by rw [hz]
      _ = _ := oneAddEta_cube hζ a b
  obtain ⟨hreal, heta⟩ := eisensteinEtaCoords_injective hζ hcoords
  refine ⟨2 * a - b, b, 2 * D.d, ?_⟩
  exact D.unitCover_solution_of_plus_coords a b hreal heta

private theorem TargetEisensteinIntegralData.exists_conjugateUnitCover_solution_of_minus_cube
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {U V : ℚ} (D : TargetEisensteinIntegralData U V) (z : 𝓞 K)
    (hfactor : D.minusFactor hζ =
      -hζ.toInteger * z ^ 3) :
    ∃ A B C : ℤ,
      targetEisensteinConjugateUnitCover A B C = 0 ∧
        ¬(A = 0 ∧ B = 0 ∧ C = 0) := by
  obtain ⟨a, b, hz⟩ := exists_eisenstein_integer_coords hζ z
  have hcoords :
      ((D.n - D.b : ℤ) : 𝓞 K) +
          (-2 * D.b : ℤ) * hζ.toInteger =
        (minusUnitReal a b : 𝓞 K) +
          minusUnitEta a b * hζ.toInteger := by
    calc
      _ = D.minusFactor hζ := (D.minusFactor_coords hζ).symm
      _ = -hζ.toInteger * z ^ 3 := hfactor
      _ = -hζ.toInteger *
          ((a : 𝓞 K) + b * hζ.toInteger) ^ 3 := by rw [hz]
      _ = _ := negEta_cube hζ a b
  obtain ⟨hreal, heta⟩ := eisensteinEtaCoords_injective hζ hcoords
  refine ⟨2 * a - b, b, 2 * D.d, ?_⟩
  exact D.conjugateUnitCover_solution_of_minus_coords a b hreal heta

/-- A literal cube in the trivial unit class gives the explicit fibre root
`-42d/(c+8d)`. -/
theorem TargetEisensteinIntegralData.exists_targetCubicFibre_root_of_cube
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {X V : ℚ} (D : TargetEisensteinIntegralData (targetThreeDescentU X) V)
    (z : 𝓞 K) (hfactor : D.minusFactor hζ = z ^ 3) :
    ∃ t : ℚ, targetCubicFibre X t = 0 := by
  obtain ⟨a, c, hz⟩ := exists_eisenstein_integer_coords hζ z
  have hcoords :
      ((D.n - D.b : ℤ) : 𝓞 K) +
          (-2 * D.b : ℤ) * hζ.toInteger =
        (cubeReal a c : 𝓞 K) +
          cubeEta a c * hζ.toInteger := by
    calc
      _ = D.minusFactor hζ := (D.minusFactor_coords hζ).symm
      _ = z ^ 3 := hfactor
      _ = ((a : 𝓞 K) + c * hζ.toInteger) ^ 3 := by rw [hz]
      _ = _ := eisensteinCube hζ a c
  obtain ⟨hreal, heta⟩ := eisensteinEtaCoords_injective hζ hcoords
  let q : ℤ := a ^ 2 - a * c + c ^ 2
  have hcubeNorm : D.m ^ 3 = q ^ 3 := by
    calc
      D.m ^ 3 = D.n ^ 2 + 3 * D.b ^ 2 := D.norm_eq.symm
      _ = (D.n - D.b) ^ 2 -
          (D.n - D.b) * (-2 * D.b) + (-2 * D.b) ^ 2 := by ring
      _ = cubeReal a c ^ 2 -
          cubeReal a c * cubeEta a c +
            cubeEta a c ^ 2 := by rw [hreal, heta]
      _ = q ^ 3 := by
        simp only [cubeReal, cubeEta]
        dsimp only [q]
        ring
  have hm : D.m = q :=
    (show Odd 3 by decide).pow_injective hcubeNorm
  have heta' := heta
  rw [D.b_eq, hm] at heta'
  simp only [cubeEta] at heta'
  have hden : c + 8 * D.d ≠ 0 := by
    intro hzero
    have hc : c = -8 * D.d := by linarith
    dsimp only [q] at heta'
    rw [hc] at heta'
    have hdCube : D.d ^ 3 = 0 := by nlinarith [heta']
    exact (pow_ne_zero 3 D.d_ne_zero) hdCube
  have hdQ : (D.d : ℚ) ≠ 0 := by exact_mod_cast D.d_ne_zero
  have hX :
      36 * (D.d : ℚ) ^ 2 * X - D.m +
          192 * (D.d : ℚ) ^ 2 = 0 := by
    have hU := D.U_eq
    simp only [targetThreeDescentU] at hU
    field_simp [hdQ] at hU
    calc
      _ = (36 * X + 192) * (D.d : ℚ) ^ 2 - D.m := by ring
      _ = 0 := sub_eq_zero.mpr hU
  refine ⟨-42 * (D.d : ℚ) / (c + 8 * D.d : ℤ), ?_⟩
  simp only [targetCubicFibre]
  simp only [Int.cast_add, Int.cast_mul, Int.cast_ofNat]
  change
    (-42 * (D.d : ℚ) / ((c : ℚ) + 8 * D.d)) ^ 3 -
        X * (-42 * (D.d : ℚ) / ((c : ℚ) + 8 * D.d)) ^ 2 +
      28 * (-42 * (D.d : ℚ) / ((c : ℚ) + 8 * D.d)) + 49 = 0
  have hdenQ' : (c : ℚ) + 8 * D.d ≠ 0 := by
    exact_mod_cast hden
  have hdenCube :
      (D.d : ℚ) * c ^ 2 * 24 + (D.d : ℚ) ^ 2 * c * 192 +
          (D.d : ℚ) ^ 3 * 512 + (c : ℚ) ^ 3 ≠ 0 := by
    intro hzero
    exact (pow_ne_zero 3 hdenQ') (by
      calc
        ((c : ℚ) + 8 * D.d) ^ 3 =
            (D.d : ℚ) * c ^ 2 * 24 + (D.d : ℚ) ^ 2 * c * 192 +
              (D.d : ℚ) ^ 3 * 512 + (c : ℚ) ^ 3 := by ring
        _ = 0 := hzero)
  rw [hm] at hX
  have hetaQ := congrArg (fun z : ℤ ↦ (z : ℚ)) heta'
  push_cast at hetaQ hX
  dsimp only [q] at hetaQ hX
  push_cast at hetaQ hX
  simp only [div_pow]
  field_simp [hdenQ', hdenCube]
  have hdenQ'' : (c : ℚ) + (D.d : ℚ) * 8 ≠ 0 := by
    intro hzero
    apply hdenQ'
    linarith
  rw [add_eq_zero_iff_eq_neg]
  rw [div_eq_iff (pow_ne_zero 3 hdenQ'')]
  linear_combination
    (-49 * ((c : ℚ) + 8 * D.d)) * hX +
      (49 / 3 : ℚ) * hetaQ

/-- An associated cube factor gives either a rational fibre root or a
nonzero integral point on one of the two nontrivial unit covers. -/
theorem TargetEisensteinIntegralData.descent_alternatives_of_associated
    [NumberField K] [IsCyclotomicExtension {3} ℚ K]
    {X V : ℚ} (D : TargetEisensteinIntegralData (targetThreeDescentU X) V)
    {z : 𝓞 K} (hassociated : Associated (z ^ 3) (D.minusFactor hζ)) :
    (∃ t : ℚ, targetCubicFibre X t = 0) ∨
      (∃ A B C : ℤ,
        targetEisensteinUnitCover A B C = 0 ∧
          ¬(A = 0 ∧ B = 0 ∧ C = 0)) ∨
      ∃ A B C : ℤ,
        targetEisensteinConjugateUnitCover A B C = 0 ∧
          ¬(A = 0 ∧ B = 0 ∧ C = 0) := by
  obtain ⟨u, hu⟩ := hassociated
  have hfactor : D.minusFactor hζ = (u : 𝓞 K) * z ^ 3 := by
    rw [← hu]
    ring
  let η : (𝓞 K)ˣ :=
    (IsPrimitiveRoot.isUnit hζ.toInteger_isPrimitiveRoot (by decide)).unit
  have hmem := IsCyclotomicExtension.Rat.Three.Units.mem hζ u
  change u ∈ [1, -1, η, -η, η ^ 2, -η ^ 2] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h <;> subst u
  all_goals
    simp only [η, Units.val_one, Units.val_neg,
      Units.val_pow_eq_pow_val,
      IsCyclotomicExtension.Rat.Three.coe_eta] at hfactor
  · left
    exact D.exists_targetCubicFibre_root_of_cube hζ z (by
      simpa only [Units.val_one, one_mul] using hfactor)
  · left
    exact D.exists_targetCubicFibre_root_of_cube hζ (-z) (by
      simpa only [Units.val_neg, Units.val_one, neg_one_mul,
        Odd.neg_pow (by decide : Odd 3)] using hfactor)
  · right; right
    exact D.exists_conjugateUnitCover_solution_of_minus_cube hζ (-z) (by
      calc
        D.minusFactor hζ = hζ.toInteger * z ^ 3 := hfactor
        _ = -hζ.toInteger * (-z) ^ 3 := by
          rw [Odd.neg_pow (by decide : Odd 3)]
          ring)
  · right; right
    exact D.exists_conjugateUnitCover_solution_of_minus_cube hζ z (by
      exact hfactor)
  · right; left
    exact D.exists_unitCover_solution_of_plus_cube hζ (-z) (by
      rw [Odd.neg_pow (by decide : Odd 3)]
      calc
        D.minusFactor hζ = hζ.toInteger ^ 2 * z ^ 3 := by
          exact hfactor
        _ = (1 + hζ.toInteger) * -z ^ 3 := by
          have hetaSq : hζ.toInteger ^ 2 =
              -hζ.toInteger - 1 := by
            simpa only [IsCyclotomicExtension.Rat.Three.coe_eta] using
              IsCyclotomicExtension.Rat.Three.eta_sq hζ
          rw [hetaSq]
          ring)
  · right; left
    exact D.exists_unitCover_solution_of_plus_cube hζ z (by
      calc
        D.minusFactor hζ = -(hζ.toInteger ^ 2) * z ^ 3 := by
          exact hfactor
        _ = (1 + hζ.toInteger) * z ^ 3 := by
          have hetaSq : hζ.toInteger ^ 2 =
              -hζ.toInteger - 1 := by
            simpa only [IsCyclotomicExtension.Rat.Three.coe_eta] using
              IsCyclotomicExtension.Rat.Three.eta_sq hζ
          rw [hetaSq]
          ring)

/-- The exact ideal-support interface: every target point admits
a positive primitive integral presentation whose negative factor is
associated to a cube in `ℤ[ζ₃]`.  The existential presentation is essential:
the rank-zero consumer does not require a claim about every possible common
rescaling of the denominator data. -/
def TargetEisensteinAssociatedCube : Prop :=
  ∀ (K : Type) [Field K] [NumberField K]
      [IsCyclotomicExtension {3} ℚ K]
      {ζ : K} (hζ : IsPrimitiveRoot ζ 3)
      {X Y : ℚ}
      (_hP : veluThreeCandidateTarget.toAffine.Nonsingular X Y),
    ∃ (D : TargetEisensteinNormalizedIntegralData
        (targetThreeDescentU X) (targetThreeDescentV X Y)) (z : 𝓞 K),
      Associated (z ^ 3)
        (D.toTargetEisensteinIntegralData.minusFactor hζ)

/-- The associated-cube input discharges the complete three-class descent
reduction consumed by the checked local obstructions. -/
theorem targetEisensteinDescentReduction_of_associatedCube
    (hfactor : TargetEisensteinAssociatedCube) :
    TargetEisensteinDescentReduction := by
  intro X Y hP
  let K := CyclotomicField 3 ℚ
  letI : IsCyclotomicExtension {3} ℚ K :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  have : NumberField K :=
    IsCyclotomicExtension.numberField {3} ℚ K
  obtain ⟨D, z, hz⟩ := hfactor K hζ hP
  exact D.toTargetEisensteinIntegralData.descent_alternatives_of_associated
    hζ hz

/-- The associated-cube input forces a rational root in every target cubic
fibre. -/
theorem targetCubicFibreRoots_of_associatedCube
    (hfactor : TargetEisensteinAssociatedCube) :
    TargetCubicFibreRoots :=
  targetCubicFibreRoots_of_eisensteinDescentReduction
    (targetEisensteinDescentReduction_of_associatedCube hfactor)

/-- End-to-end rank-zero consumer of the exact remaining ideal-support
statement. -/
theorem optimalQuotientModel_rank_zero_of_associatedCube
    (hfactor : TargetEisensteinAssociatedCube) :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 :=
  optimalQuotientModel_rank_zero_of_targetCubicFibreRoots
    (targetCubicFibreRoots_of_associatedCube hfactor)

/-- End-to-end finiteness consumer of the associated-cube ideal-support
statement. -/
theorem optimalQuotientModel_finite_of_associatedCube
    (hfactor : TargetEisensteinAssociatedCube) :
    Finite optimalQuotientModel.toAffine.Point :=
  optimalQuotientModel_finite_of_targetCubicFibreRoots
    (targetCubicFibreRoots_of_associatedCube hfactor)

end MazurTorsion.OrderThirtyFive

end

/- Source: MazurTorsion/NumberTheory/OrderThirtyFiveEisensteinIdealSupport.lean -/

section

/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Ideal support for the order-35 Eisenstein descent

This file proves the remaining ideal-support step for the normalized equation

`n² + 3b² = m³`.

A common prime of the two Eisenstein factors is shown to lie over `2`, `3`,
or `5`. The primes `2` and `5` are inert, while `√-3` is the ramified
prime over `3`. Coordinate conjugation identifies the valuations of both
factors at all three exceptional primes. Comparing valuations in
`(n-b√-3)(n+b√-3)=m³` then makes every valuation of the negative factor a
multiple of three. Unique factorization produces an associated cube and
closes the checked order-35 rank-zero descent.
-/

open NumberField Polynomial WeierstrassCurve UniqueFactorizationMonoid
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.OrderThirtyFive

open IsCyclotomicExtension.Rat.Three

variable {K : Type*} [Field K] [NumberField K]
variable [IsCyclotomicExtension {3} ℚ K]
variable {ζ : K} (hζ : IsPrimitiveRoot ζ 3)


private def eisensteinCoordinateNorm (a b : ℤ) : ℤ := a ^ 2 - a * b + b ^ 2

private lemma eisensteinCoordinateNorm_mul (a b c d : ℤ) :
    eisensteinCoordinateNorm (a * c - b * d) (a * d + b * c - b * d) =
      eisensteinCoordinateNorm a b * eisensteinCoordinateNorm c d := by
  simp only [eisensteinCoordinateNorm]
  ring

private lemma eisensteinCoordinateNorm_pos {a b : ℤ} (h : ¬(a = 0 ∧ b = 0)) :
    0 < eisensteinCoordinateNorm a b := by
  simp only [eisensteinCoordinateNorm]
  by_contra hnpos
  have hid : 4 * (a ^ 2 - a * b + b ^ 2) =
      (2 * a - b) ^ 2 + 3 * b ^ 2 := by ring
  have hb2 : b ^ 2 = 0 := by
    nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
  have hb : b = 0 := sq_eq_zero_iff.mp hb2
  have ha : a = 0 := by
    rw [hb] at hnpos
    norm_num at hnpos
    exact hnpos
  exact h ⟨ha, hb⟩

private lemma eisensteinCoordinateNorm_ne_two_or_five (a b : ℤ) :
    eisensteinCoordinateNorm a b ≠ 2 ∧ eisensteinCoordinateNorm a b ≠ 5 := by
  have hpow := ZMod.pow_card ((a + b : ℤ) : ZMod 3)
  constructor <;> intro hnorm
  · have hmod := congrArg (fun z : ℤ ↦ (z : ZMod 3)) hnorm
    simp only [eisensteinCoordinateNorm] at hmod
    push_cast at hmod
    have hsq : (((a + b : ℤ) : ZMod 3) ^ 2) = 2 := by
      calc
        _ = (a : ZMod 3) ^ 2 - (a : ZMod 3) * b + (b : ZMod 3) ^ 2 := by
          push_cast
          have hthree : (3 : ZMod 3) = 0 := by decide
          rw [← sub_eq_iff_eq_add]
          linear_combination hthree * ((a : ZMod 3) * b)
        _ = 2 := hmod
    have hx0 : ((a + b : ℤ) : ZMod 3) = 0 := by
      rw [show ((a + b : ℤ) : ZMod 3) ^ 3 =
          ((a + b : ℤ) : ZMod 3) ^ 2 * ((a + b : ℤ) : ZMod 3) by ring,
        hsq] at hpow
      linear_combination hpow
    rw [hx0] at hsq
    exact (by decide : (0 : ZMod 3) ≠ 2) hsq
  · have hmod := congrArg (fun z : ℤ ↦ (z : ZMod 3)) hnorm
    simp only [eisensteinCoordinateNorm] at hmod
    push_cast at hmod
    have hsq : (((a + b : ℤ) : ZMod 3) ^ 2) = 2 := by
      calc
        _ = (a : ZMod 3) ^ 2 - (a : ZMod 3) * b + (b : ZMod 3) ^ 2 := by
          push_cast
          have hthree : (3 : ZMod 3) = 0 := by decide
          rw [← sub_eq_iff_eq_add]
          linear_combination hthree * ((a : ZMod 3) * b)
        _ = (5 : ZMod 3) := hmod
        _ = 2 := by decide
    have hx0 : ((a + b : ℤ) : ZMod 3) = 0 := by
      rw [show ((a + b : ℤ) : ZMod 3) ^ 3 =
          ((a + b : ℤ) : ZMod 3) ^ 2 * ((a + b : ℤ) : ZMod 3) by ring,
        hsq] at hpow
      linear_combination hpow
    rw [hx0] at hsq
    exact (by decide : (0 : ZMod 3) ≠ 2) hsq

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma eisenstein_mul_coords (a b c d : ℤ) :
    ((a : 𝓞 K) + b * hζ.toInteger) *
        ((c : 𝓞 K) + d * hζ.toInteger) =
      ((a * c - b * d : ℤ) : 𝓞 K) +
        (a * d + b * c - b * d) * hζ.toInteger := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  push_cast
  linear_combination b * d * hroot

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma isUnit_of_eisensteinCoordinateNorm_eq_one {a b : ℤ}
    (h : eisensteinCoordinateNorm a b = 1) :
    IsUnit ((a : 𝓞 K) + b * hζ.toInteger) := by
  rw [isUnit_iff_exists_inv]
  refine ⟨((a - b : ℤ) : 𝓞 K) - b * hζ.toInteger, ?_⟩
  rw [show ((a - b : ℤ) : 𝓞 K) - b * hζ.toInteger =
      ((a - b : ℤ) : 𝓞 K) + (-b : ℤ) * hζ.toInteger by push_cast; ring]
  rw [eisenstein_mul_coords hζ]
  simp only [eisensteinCoordinateNorm] at h
  push_cast
  have hreal : a * (a - b) - b * -b = 1 := by
    linear_combination h
  have heta : a * -b + b * (a - b) - b * -b = 0 := by ring
  have hrealO := congrArg (fun z : ℤ ↦ (z : 𝓞 K)) hreal
  have hetaO := congrArg (fun z : ℤ ↦ (z : 𝓞 K)) heta
  push_cast at hrealO hetaO
  rw [hrealO, hetaO]
  ring

private lemma eisenstein_prime_two_or_five (hζ : IsPrimitiveRoot ζ 3)
    (r : ℤ) (hr : r = 2 ∨ r = 5) :
    Prime (r : 𝓞 K) := by
  letI : IsPrincipalIdealRing (𝓞 K) :=
    IsCyclotomicExtension.Rat.three_pid K
  apply Irreducible.prime
  rw [irreducible_iff]
  constructor
  · intro hunit
    obtain ⟨y, hy⟩ := isUnit_iff_exists_inv.mp hunit
    obtain ⟨c, d, hycoords⟩ := exists_eisenstein_integer_coords hζ y
    have hprod : (r : 𝓞 K) *
        ((c : 𝓞 K) + d * hζ.toInteger) = 1 := by
      rw [← hycoords]
      exact hy
    have hprod' :
        ((r : 𝓞 K) + (0 : ℤ) * hζ.toInteger) *
            ((c : 𝓞 K) + d * hζ.toInteger) =
          ((1 : ℤ) : 𝓞 K) + (0 : ℤ) * hζ.toInteger := by
      simpa using hprod
    rw [eisenstein_mul_coords hζ] at hprod'
    have hcoords := eisensteinEtaCoords_injective
      (a := r * c - 0 * d) (b := r * d + 0 * c - 0 * d)
      (c := 1) (d := 0) hζ (by
        simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul,
          Int.cast_zero, Int.cast_one] using hprod')
    rcases hr with rfl | rfl <;> omega
  · intro x y hxy
    obtain ⟨a, b, hx⟩ := exists_eisenstein_integer_coords hζ x
    obtain ⟨c, d, hy⟩ := exists_eisenstein_integer_coords hζ y
    have hxy' :
        ((a : 𝓞 K) + b * hζ.toInteger) *
            ((c : 𝓞 K) + d * hζ.toInteger) = (r : 𝓞 K) := by
      rw [← hx, ← hy, ← hxy]
    rw [eisenstein_mul_coords hζ] at hxy'
    have hxy'' :
        ((a * c - b * d : ℤ) : 𝓞 K) +
            (a * d + b * c - b * d) * hζ.toInteger =
          (r : 𝓞 K) + (0 : ℤ) * hζ.toInteger := by
      simpa using hxy'
    have hcoords := eisensteinEtaCoords_injective
      (a := a * c - b * d) (b := a * d + b * c - b * d)
      (c := r) (d := 0) hζ (by
        simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul,
          Int.cast_zero] using hxy'')
    have hnormprod : eisensteinCoordinateNorm a b * eisensteinCoordinateNorm c d = r ^ 2 := by
      rw [← eisensteinCoordinateNorm_mul]
      simp only [hcoords.1, hcoords.2, eisensteinCoordinateNorm]
      ring
    by_contra hnonunits
    simp only [not_or] at hnonunits
    have hab0 : ¬(a = 0 ∧ b = 0) := by
      rintro ⟨rfl, rfl⟩
      have hx0 : x = 0 := by
        simpa only [Int.cast_zero, zero_mul, add_zero] using hx
      rw [hx0, zero_mul] at hxy
      rcases hr with rfl | rfl <;> norm_num at hxy
    have hcd0 : ¬(c = 0 ∧ d = 0) := by
      rintro ⟨rfl, rfl⟩
      have hy0 : y = 0 := by
        simpa only [Int.cast_zero, zero_mul, add_zero] using hy
      rw [hy0, mul_zero] at hxy
      rcases hr with rfl | rfl <;> norm_num at hxy
    have hNabpos := eisensteinCoordinateNorm_pos hab0
    have hNcdpos := eisensteinCoordinateNorm_pos hcd0
    have hNabne1 : eisensteinCoordinateNorm a b ≠ 1 := fun h ↦
      hnonunits.1 (hx.symm ▸ isUnit_of_eisensteinCoordinateNorm_eq_one hζ h)
    have hNcdne1 : eisensteinCoordinateNorm c d ≠ 1 := fun h ↦
      hnonunits.2 (hy.symm ▸ isUnit_of_eisensteinCoordinateNorm_eq_one hζ h)
    have hNab2 : 2 ≤ eisensteinCoordinateNorm a b := by omega
    have hNcd2 : 2 ≤ eisensteinCoordinateNorm c d := by omega
    have hNabBound : eisensteinCoordinateNorm a b ≤ 12 := by
      rcases hr with rfl | rfl
      · nlinarith
      · nlinarith
    rcases hr with rfl | rfl
    · have hNab : eisensteinCoordinateNorm a b = 2 := by nlinarith
      exact (eisensteinCoordinateNorm_ne_two_or_five a b).1 hNab
    · have hNab : eisensteinCoordinateNorm a b = 5 := by
        interval_cases hN : eisensteinCoordinateNorm a b <;> omega
      exact (eisensteinCoordinateNorm_ne_two_or_five a b).2 hNab

/-- The rational prime `2` remains prime in the Eisenstein integers. -/
theorem eisenstein_two_prime (hζ : IsPrimitiveRoot ζ 3) :
    Prime (2 : 𝓞 K) := by
  simpa only [Int.cast_ofNat] using
    eisenstein_prime_two_or_five hζ (2 : ℤ) (Or.inl rfl)

/-- The rational prime `5` remains prime in the Eisenstein integers. -/
theorem eisenstein_five_prime (hζ : IsPrimitiveRoot ζ 3) :
    Prime (5 : 𝓞 K) := by
  simpa only [Int.cast_ofNat] using
    eisenstein_prime_two_or_five hζ (5 : ℤ) (Or.inr rfl)

/-- The element `√-3` generates the ramified prime over `3`. -/
theorem eisensteinSqrtNegThree_prime : Prime (eisensteinSqrtNegThree hζ) := by
  have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
    (by norm_num)
  rw [Polynomial.cyclotomic_three] at hroot
  norm_num [Polynomial.IsRoot] at hroot
  have hfactor : eisensteinSqrtNegThree hζ =
      (-hζ.toInteger) * (hζ.toInteger - 1) := by
    simp only [eisensteinSqrtNegThree]
    linear_combination hroot
  rw [hfactor]
  exact (prime_isUnit_mul
    (hζ.toInteger_isPrimitiveRoot.isUnit (by decide)).neg).mpr
      hζ.zeta_sub_one_prime'

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
/-- A prime common to the conjugate norm factors divides `2`, `√-3`, or
the constant `1500`. -/
theorem common_prime_support
    {U V : ℚ} (D : TargetEisensteinNormalizedIntegralData U V)
    (p : 𝓞 K) (hp : Prime p)
    (hminus : p ∣ D.toTargetEisensteinIntegralData.minusFactor hζ)
    (hplus : p ∣ D.toTargetEisensteinIntegralData.plusFactor hζ) :
    p ∣ (2 : 𝓞 K) ∨ p ∣ eisensteinSqrtNegThree hζ ∨
      p ∣ (1500 : 𝓞 K) := by
  have hsum : p ∣ (2 : 𝓞 K) * D.n := by
    have h := dvd_add hminus hplus
    change p ∣ ((D.n : 𝓞 K) - D.b * eisensteinSqrtNegThree hζ) +
      ((D.n : 𝓞 K) + D.b * eisensteinSqrtNegThree hζ) at h
    convert h using 1
    ring
  rcases hp.dvd_mul.mp hsum with hp2 | hpn
  · exact Or.inl hp2
  have hdifference : p ∣ (2 : 𝓞 K) * D.b * eisensteinSqrtNegThree hζ := by
    have h := dvd_sub hplus hminus
    change p ∣ ((D.n : 𝓞 K) + D.b * eisensteinSqrtNegThree hζ) -
      ((D.n : 𝓞 K) - D.b * eisensteinSqrtNegThree hζ) at h
    convert h using 1
    ring
  rcases hp.dvd_mul.mp hdifference with hptwoB | hpsqrt
  · rcases hp.dvd_mul.mp hptwoB with hp2 | hpb
    · exact Or.inl hp2
    · have hcop0 := D.n_coprime_d.map (Int.castRingHom (𝓞 K))
      change IsCoprime (D.n : 𝓞 K) (D.d : 𝓞 K) at hcop0
      have hcop : IsCoprime (D.n : 𝓞 K) (D.d : 𝓞 K) := hcop0
      rw [D.b_eq] at hpb
      push_cast at hpb
      rcases hp.dvd_mul.mp hpb with hpd | hpc
      · exact False.elim (hp.not_unit (hcop.isUnit_of_dvd' hpn hpd))
      · have hpm3 : p ∣ (D.m : 𝓞 K) ^ 3 := by
          rw [← D.toTargetEisensteinIntegralData.factors_mul hζ]
          exact hminus.mul_right _
        have hpm : p ∣ (D.m : 𝓞 K) := hp.dvd_of_dvd_pow hpm3
        have h1500d : p ∣ (1500 : 𝓞 K) * (D.d : 𝓞 K) ^ 2 := by
          have h12m : p ∣ (12 : 𝓞 K) * D.m := hpm.mul_left 12
          have h := dvd_sub hpc h12m
          convert h using 1
          ring
        rcases hp.dvd_mul.mp h1500d with h1500 | hd2
        · exact Or.inr (Or.inr h1500)
        · have hpd : p ∣ (D.d : 𝓞 K) := hp.dvd_of_dvd_pow hd2
          exact False.elim (hp.not_unit (hcop.isUnit_of_dvd' hpn hpd))
  · exact Or.inr (Or.inl hpsqrt)

/-- Every prime common to the conjugate factors is associated to one of the
three exceptional prime elements `2`, `√-3`, and `5`. -/
theorem common_prime_associated
    {U V : ℚ} (D : TargetEisensteinNormalizedIntegralData U V)
    (p : 𝓞 K) (hp : Prime p)
    (hminus : p ∣ D.toTargetEisensteinIntegralData.minusFactor hζ)
    (hplus : p ∣ D.toTargetEisensteinIntegralData.plusFactor hζ) :
    Associated p (2 : 𝓞 K) ∨
      Associated p (eisensteinSqrtNegThree hζ) ∨
      Associated p (5 : 𝓞 K) := by
  have hp2 : Prime (2 : 𝓞 K) := eisenstein_two_prime hζ
  have hp5 : Prime (5 : 𝓞 K) := eisenstein_five_prime hζ
  have hps : Prime (eisensteinSqrtNegThree hζ) := eisensteinSqrtNegThree_prime hζ
  rcases common_prime_support hζ D p hp hminus hplus with
    h2 | hs | h1500
  · exact Or.inl (hp.irreducible.associated_of_dvd hp2.irreducible h2)
  · exact Or.inr (Or.inl
      (hp.irreducible.associated_of_dvd hps.irreducible hs))
  · have hfactor : (1500 : 𝓞 K) =
        (2 : 𝓞 K) ^ 2 * (3 : 𝓞 K) * (5 : 𝓞 K) ^ 3 := by norm_num
    rw [hfactor] at h1500
    rcases hp.dvd_mul.mp h1500 with htwoThree | hfive
    · rcases hp.dvd_mul.mp htwoThree with htwo | hthree
      · have h2 : p ∣ (2 : 𝓞 K) := hp.dvd_of_dvd_pow htwo
        exact Or.inl (hp.irreducible.associated_of_dvd hp2.irreducible h2)
      · have hthree' : p ∣ eisensteinSqrtNegThree hζ ^ 2 := by
          have hsquare : eisensteinSqrtNegThree hζ ^ 2 = (-3 : 𝓞 K) := by
            have hroot := hζ.toInteger_isPrimitiveRoot.isRoot_cyclotomic
              (by norm_num)
            rw [Polynomial.cyclotomic_three] at hroot
            norm_num [Polynomial.IsRoot] at hroot
            simp only [eisensteinSqrtNegThree]
            linear_combination 4 * hroot
          rw [hsquare]
          exact hthree.neg_right
        have hs : p ∣ eisensteinSqrtNegThree hζ :=
          hp.dvd_of_dvd_pow hthree'
        exact Or.inr (Or.inl
          (hp.irreducible.associated_of_dvd hps.irreducible hs))
    · have h5 : p ∣ (5 : 𝓞 K) := hp.dvd_of_dvd_pow hfive
      exact Or.inr (Or.inr
        (hp.irreducible.associated_of_dvd hp5.irreducible h5))

private def EisensteinConjugate (x y : 𝓞 K) : Prop :=
  ∃ a b : ℤ,
    x = (a : 𝓞 K) + b * hζ.toInteger ∧
    y = ((a - b : ℤ) : 𝓞 K) + (-b : ℤ) * hζ.toInteger

omit [IsCyclotomicExtension {3} ℚ K] in
private lemma EisensteinConjugate.right_unique {x y z : 𝓞 K}
    (hxy : EisensteinConjugate hζ x y) (hxz : EisensteinConjugate hζ x z) :
    y = z := by
  obtain ⟨a, b, hxab, hyab⟩ := hxy
  obtain ⟨c, d, hxcd, hzcd⟩ := hxz
  have hcoords := eisensteinEtaCoords_injective hζ (hxab.symm.trans hxcd)
  rcases hcoords with ⟨rfl, rfl⟩
  rw [hyab, hzcd]

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma EisensteinConjugate.symm {x y : 𝓞 K}
    (hxy : EisensteinConjugate hζ x y) :
    EisensteinConjugate hζ y x := by
  obtain ⟨a, b, rfl, rfl⟩ := hxy
  refine ⟨a - b, -b, ?_, ?_⟩
  · rfl
  · push_cast
    ring

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma EisensteinConjugate.mul {x₁ y₁ x₂ y₂ : 𝓞 K}
    (h₁ : EisensteinConjugate hζ x₁ y₁) (h₂ : EisensteinConjugate hζ x₂ y₂) :
    EisensteinConjugate hζ (x₁ * x₂) (y₁ * y₂) := by
  obtain ⟨a, b, rfl, rfl⟩ := h₁
  obtain ⟨c, d, rfl, rfl⟩ := h₂
  refine ⟨a * c - b * d, a * d + b * c - b * d, ?_, ?_⟩
  · simpa only [Int.cast_add, Int.cast_sub, Int.cast_mul] using
      eisenstein_mul_coords hζ a b c d
  · rw [eisenstein_mul_coords hζ]
    push_cast
    ring

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma EisensteinConjugate.one :
    EisensteinConjugate hζ (1 : 𝓞 K) 1 := by
  refine ⟨1, 0, ?_, ?_⟩ <;> push_cast <;> ring

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma EisensteinConjugate.pow {x y : 𝓞 K}
    (hxy : EisensteinConjugate hζ x y)
    (k : ℕ) : EisensteinConjugate hζ (x ^ k) (y ^ k) := by
  induction k with
  | zero => simpa using EisensteinConjugate.one hζ
  | succ k ih => simpa [pow_succ] using ih.mul hζ hxy

private lemma exists_eisensteinConjugate (x : 𝓞 K) :
    ∃ y, EisensteinConjugate hζ x y := by
  obtain ⟨a, b, rfl⟩ := exists_eisenstein_integer_coords hζ x
  exact ⟨_, a, b, rfl, rfl⟩

private lemma EisensteinConjugate.pow_dvd_iff {q q' x y : 𝓞 K}
    (hq : EisensteinConjugate hζ q q') (hxy : EisensteinConjugate hζ x y) (k : ℕ) :
    q ^ k ∣ x ↔ q' ^ k ∣ y := by
  constructor
  · rintro ⟨z, hz⟩
    obtain ⟨z', hzz'⟩ := exists_eisensteinConjugate hζ z
    have hprod := (hq.pow hζ k).mul hζ hzz'
    refine ⟨z', ?_⟩
    apply hxy.right_unique hζ
    rw [hz]
    exact hprod
  · rintro ⟨z, hz⟩
    obtain ⟨z', hzz'⟩ := exists_eisensteinConjugate hζ z
    have hprod := ((hq.symm hζ).pow hζ k).mul hζ hzz'
    refine ⟨z', ?_⟩
    apply (hxy.symm hζ).right_unique hζ
    rw [hz]
    exact hprod

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma eisensteinConjugate_intCast (r : ℤ) :
    EisensteinConjugate hζ (r : 𝓞 K) (r : 𝓞 K) := by
  refine ⟨r, 0, ?_, ?_⟩ <;> push_cast <;> ring

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma eisensteinSqrtNegThree_conjugate :
    EisensteinConjugate hζ (eisensteinSqrtNegThree hζ)
      (-eisensteinSqrtNegThree hζ) := by
  refine ⟨1, 2, ?_, ?_⟩ <;>
    simp only [eisensteinSqrtNegThree] <;> push_cast <;> ring

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma factors_conjugate {U V : ℚ}
    (D : TargetEisensteinIntegralData U V) :
    EisensteinConjugate hζ (D.minusFactor hζ) (D.plusFactor hζ) := by
  refine ⟨D.n - D.b, -2 * D.b, D.minusFactor_coords hζ, ?_⟩
  rw [D.plusFactor_coords hζ]
  push_cast
  ring

omit [NumberField K] [IsCyclotomicExtension {3} ℚ K] in
private lemma exists_associated_cube_of_factor_counts
    [NormalizationMonoid (𝓞 K)] [UniqueFactorizationMonoid (𝓞 K)]
    [DecidableEq (𝓞 K)]
    {x : 𝓞 K} (hx : x ≠ 0)
    (hcount : ∀ p : 𝓞 K, 3 ∣ (normalizedFactors x).count p) :
    ∃ z : 𝓞 K, Associated (z ^ 3) x := by
  classical
  let f : 𝓞 K → 𝓞 K := fun p ↦
    p ^ ((normalizedFactors x).count p / 3)
  have hf : f.HasFiniteMulSupport := by
    apply (normalizedFactors x).toFinset.finite_toSet.subset
    intro p hp
    have hcount0 : (normalizedFactors x).count p ≠ 0 := by
      intro hzero
      apply hp
      change p ^ ((normalizedFactors x).count p / 3) = 1
      rw [hzero]
      norm_num
    exact Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (Nat.pos_of_ne_zero hcount0))
  refine ⟨∏ᶠ p, f p, ?_⟩
  have hcube : (∏ᶠ p, f p) ^ 3 =
      ∏ᶠ p : 𝓞 K, p ^ (normalizedFactors x).count p := by
    rw [finprod_pow hf]
    apply finprod_congr
    intro p
    simp only [f, ← pow_mul]
    rw [Nat.div_mul_cancel (hcount p)]
  rw [hcube]
  exact associated_finprod_pow_count hx

private lemma TargetEisensteinNormalizedIntegralData.m_ne_zero
    {U V : ℚ} (D : TargetEisensteinNormalizedIntegralData U V) :
    D.m ≠ 0 := by
  intro hm
  have hb : D.b ≠ 0 := by
    rw [D.b_eq, hm]
    norm_num
    exact D.d_ne_zero
  have hnorm := D.norm_eq
  rw [hm] at hnorm
  nlinarith [sq_nonneg D.n, sq_pos_of_ne_zero hb]

/-- Every normalized irreducible factor of the negative Eisenstein factor has
multiplicity divisible by three. -/
theorem minusFactor_count_dvd_three
    [NormalizationMonoid (𝓞 K)] [UniqueFactorizationMonoid (𝓞 K)]
    [DecidableEq (𝓞 K)]
    {U V : ℚ} (D : TargetEisensteinNormalizedIntegralData U V)
    (p : 𝓞 K) :
    3 ∣ (normalizedFactors
      (D.toTargetEisensteinIntegralData.minusFactor hζ)).count p := by
  classical
  let x := D.toTargetEisensteinIntegralData.minusFactor hζ
  let y := D.toTargetEisensteinIntegralData.plusFactor hζ
  let M : 𝓞 K := (D.m : 𝓞 K)
  have hmZ : D.m ≠ 0 := D.m_ne_zero
  have hm : M ≠ 0 := by
    dsimp only [M]
    exact_mod_cast hmZ
  have hmul : x * y = M ^ 3 := by
    simpa only [x, y, M] using
      D.toTargetEisensteinIntegralData.factors_mul hζ
  have hx : x ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hmul
    exact (pow_ne_zero 3 hm) hmul.symm
  have hy : y ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    exact (pow_ne_zero 3 hm) hmul.symm
  have hfac : factorization x + factorization y =
      3 • factorization M := by
    rw [← factorization_mul hx hy, hmul, factorization_pow]
  have hcountEq := DFunLike.congr_fun hfac p
  simp only [Finsupp.add_apply, factorization_eq_count,
    Finsupp.smul_apply, smul_eq_mul] at hcountEq
  by_cases hpx : p ∈ normalizedFactors x
  · have hp : Prime p := prime_of_normalized_factor p hpx
    have hpdivx : p ∣ x := dvd_of_mem_normalizedFactors hpx
    by_cases hpdivy : p ∣ y
    · have hassoc := common_prime_associated hζ D p hp hpdivx hpdivy
      have hxyconj : EisensteinConjugate hζ x y := by
        simpa only [x, y] using
          factors_conjugate hζ D.toTargetEisensteinIntegralData
      have hcountSame : (normalizedFactors x).count p =
          (normalizedFactors y).count p := by
        have hnorm : normalize p = p := normalize_normalized_factor p hpx
        have hemp : emultiplicity p x = emultiplicity p y := by
          rcases hassoc with hp2 | hps | hp5
          · calc
              emultiplicity p x = emultiplicity (2 : 𝓞 K) x :=
                (emultiplicity_eq_of_associated_left hp2).symm
              _ = emultiplicity (2 : 𝓞 K) y :=
                emultiplicity_eq_emultiplicity_iff.mpr fun k ↦
                  (by simpa only [Int.cast_ofNat] using
                    (eisensteinConjugate_intCast hζ 2).pow_dvd_iff hζ hxyconj k)
              _ = emultiplicity p y :=
                emultiplicity_eq_of_associated_left hp2
          · calc
              emultiplicity p x =
                  emultiplicity (eisensteinSqrtNegThree hζ) x :=
                (emultiplicity_eq_of_associated_left hps).symm
              _ = emultiplicity (-eisensteinSqrtNegThree hζ) y :=
                emultiplicity_eq_emultiplicity_iff.mpr fun k ↦
                  (eisensteinSqrtNegThree_conjugate hζ).pow_dvd_iff hζ hxyconj k
              _ = emultiplicity (eisensteinSqrtNegThree hζ) y :=
                emultiplicity_eq_of_associated_left Associated.rfl.neg_right
              _ = emultiplicity p y :=
                emultiplicity_eq_of_associated_left hps
          · calc
              emultiplicity p x = emultiplicity (5 : 𝓞 K) x :=
                (emultiplicity_eq_of_associated_left hp5).symm
              _ = emultiplicity (5 : 𝓞 K) y :=
                emultiplicity_eq_emultiplicity_iff.mpr fun k ↦
                  (by simpa only [Int.cast_ofNat] using
                    (eisensteinConjugate_intCast hζ 5).pow_dvd_iff hζ hxyconj k)
              _ = emultiplicity p y :=
                emultiplicity_eq_of_associated_left hp5
        have hmult : multiplicity p x = multiplicity p y :=
          multiplicity_eq_of_emultiplicity_eq hemp
        have hmx' := multiplicity_eq_count_normalizedFactors hp.irreducible hx
        have hmy' := multiplicity_eq_count_normalizedFactors hp.irreducible hy
        calc
          (normalizedFactors x).count p = multiplicity p x := by
            rw [hmx', hnorm]
          _ = multiplicity p y := hmult
          _ = (normalizedFactors y).count p := by rw [hmy', hnorm]
      rw [hcountSame] at hcountEq
      have hthree : 3 ∣ 2 * (normalizedFactors x).count p := by
        refine ⟨(normalizedFactors M).count p, ?_⟩
        omega
      exact Nat.Coprime.dvd_of_dvd_mul_left (by decide) hthree
    · have hpynmem : p ∉ normalizedFactors y := fun hpy ↦
        hpdivy (dvd_of_mem_normalizedFactors hpy)
      have hcounty : (normalizedFactors y).count p = 0 :=
        Multiset.count_eq_zero.mpr hpynmem
      rw [hcounty, add_zero] at hcountEq
      exact ⟨(normalizedFactors M).count p, hcountEq⟩
  · rw [Multiset.count_eq_zero.mpr hpx]
    exact dvd_zero 3

/-- The negative Eisenstein norm factor of normalized target data is
associated to a cube. -/
theorem exists_associated_cube
    {U V : ℚ} (D : TargetEisensteinNormalizedIntegralData U V) :
    ∃ z : 𝓞 K, Associated (z ^ 3)
      (D.toTargetEisensteinIntegralData.minusFactor hζ) := by
  classical
  letI : IsPrincipalIdealRing (𝓞 K) :=
    IsCyclotomicExtension.Rat.three_pid K
  letI : StrongNormalizationMonoid (𝓞 K) :=
    UniqueFactorizationMonoid.strongNormalizationMonoid
  let x := D.toTargetEisensteinIntegralData.minusFactor hζ
  have hmZ : D.m ≠ 0 := D.m_ne_zero
  have hm : (D.m : 𝓞 K) ≠ 0 := by exact_mod_cast hmZ
  have hx : x ≠ 0 := by
    intro hzero
    have hmul := D.toTargetEisensteinIntegralData.factors_mul hζ
    change x * D.toTargetEisensteinIntegralData.plusFactor hζ =
      (D.m : 𝓞 K) ^ 3 at hmul
    rw [hzero, zero_mul] at hmul
    exact (pow_ne_zero 3 hm) hmul.symm
  apply exists_associated_cube_of_factor_counts hx
  intro p
  simpa only [x] using minusFactor_count_dvd_three hζ D p

/-- The ideal-support contract required by the order-35 Eisenstein descent. -/
theorem targetEisensteinAssociatedCube : TargetEisensteinAssociatedCube := by
  intro K _ _ _ ζ hζ X Y hP
  obtain ⟨D⟩ := targetEisensteinNormalizedIntegralData hP
  obtain ⟨z, hz⟩ := exists_associated_cube hζ D
  exact ⟨D, z, hz⟩

/-- The explicit optimal quotient used at level `35` has Mordell--Weil rank
zero, with no remaining arithmetic hypothesis. -/
theorem optimalQuotientModel_rank_zero :
    Module.finrank ℤ optimalQuotientModel.toAffine.Point = 0 :=
  optimalQuotientModel_rank_zero_of_associatedCube targetEisensteinAssociatedCube

/-- The rational point group of the fixed explicit level-`35` model is finite,
with no remaining arithmetic hypothesis.  Identifying this model with the
required modular quotient is a separate geometric step. -/
theorem optimalQuotientModel_finite :
    Finite optimalQuotientModel.toAffine.Point :=
  optimalQuotientModel_finite_of_associatedCube targetEisensteinAssociatedCube

end MazurTorsion.OrderThirtyFive

end


private def dupNum (x : ℚ) : ℚ := x^4 - 18*x^2 - 10*x + 76

private def dupDen (x : ℚ) : ℚ := 4*x^3 + 4*x^2 + 36*x + 5

private theorem dupBezout (x : ℚ) :
    (560 + 32*x + 48*x^2) * dupNum x +
      (63 + 180*x + 4*x^2 - 12*x^3) * dupDen x = 42875 := by
  unfold dupNum dupDen
  ring

private theorem dupHeightReal (x : ℚ) :
    (max |x| 1)^4 / 5 ≤ max |dupNum x| |dupDen x| := by
  let t := |x|
  have ht : 0 ≤ t := abs_nonneg x
  have hsq : x^2 = t^2 := (sq_abs x).symm
  have hfour : x^4 = t^4 := by
    calc
      x^4 = (x^2)^2 := by ring
      _ = (t^2)^2 := by rw [hsq]
      _ = t^4 := by ring
  have hxle : x ≤ t := le_abs_self x
  change (max t 1)^4 / 5 ≤ _
  by_cases h_small : t ≤ 1
  · rw [max_eq_right h_small]
    apply le_trans _ (le_max_left _ _)
    apply le_trans _ (le_abs_self _)
    unfold dupNum
    have hsq1 : t^2 ≤ 1 := (pow_le_pow_left₀ ht h_small 2).trans_eq (by norm_num)
    nlinarith [sq_nonneg (x^2)]
  · have h1 : 1 ≤ t := (lt_of_not_ge h_small).le
    rw [max_eq_left h1]
    by_cases h_medium : t ≤ 5
    · apply le_trans _ (le_max_right _ _)
      have hquartic : t^4 ≤ 5*t^3 := by
        calc
          _ = t * t^3 := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right h_medium (pow_nonneg ht 3)
      have h_lower : t^3 ≤ |dupDen x| := by
        by_cases hx : 0 ≤ x
        · have htx : t = x := abs_of_nonneg hx
          rw [htx]
          exact le_trans (by unfold dupDen; nlinarith [pow_nonneg hx 3, sq_nonneg x]) (le_abs_self _)
        · have htx : x = -t := by
            dsimp only [t]
            rw [abs_of_nonpos (le_of_not_ge hx), neg_neg]
          calc
            t^3 ≤ -dupDen x := by
              rw [htx]
              unfold dupDen
              nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sq_nonneg t),
                mul_nonneg ht (sub_nonneg.mpr h_medium)]
            _ ≤ |dupDen x| := neg_le_abs _
      linarith
    · apply le_trans _ (le_max_left _ _)
      apply le_trans _ (le_abs_self _)
      unfold dupNum
      rw [hsq, hfour]
      let s := t - 5
      have hs : 0 ≤ s := sub_nonneg.mpr (lt_of_not_ge h_medium).le
      have hshape : t^4 - 18*t^2 - 10*t + 76 - t^4/5 =
          (4/5)*s^4 + 16*s^3 + 102*s^2 + 210*s + 76 := by
        dsimp only [s]
        ring
      have hn : 0 ≤ (4/5:ℚ)*s^4 + 16*s^3 + 102*s^2 + 210*s + 76 := by positivity
      linarith


private def height35 (x : ℚ) : ℚ := max |(x.num : ℚ)| (x.den : ℚ)

private theorem height35_scale (x : ℚ) :
    height35 x = max |x| 1 * (x.den : ℚ) := by
  have hd : 0 < (x.den : ℚ) := by exact_mod_cast x.den_pos
  have he := (div_eq_iff hd.ne').mp x.num_div_den
  have habs : |x| * (x.den : ℚ) = |(x.num : ℚ)| := by
    calc
      _ = |x * (x.den : ℚ)| := by rw [abs_mul, abs_of_nonneg hd.le]
      _ = _ := by rw [← he]
  rw [height35, max_mul_of_nonneg _ _ hd.le, one_mul, habs]


private theorem height35_dup (x : ℚ) (hg : dupDen x ≠ 0) :
    height35 x ^ 4 ≤ 214375 * height35 (dupNum x / dupDen x) := by
  let a := x.num
  let b : ℤ := x.den
  let F := a^4 - 18*a^2*b^2 - 10*a*b^3 + 76*b^4
  let G := b*(4*a^3 + 4*a^2*b + 36*a*b^2 + 5*b^3)
  have hb0 : 0 < (b : ℚ) := by
    change 0 < ((x.den : ℤ) : ℚ)
    exact_mod_cast x.den_pos
  have hx : x = (a : ℚ) / (b : ℚ) := by
    simpa [a, b] using x.num_div_den.symm
  have hb4 : 0 < (b : ℚ)^4 := pow_pos hb0 _
  have hF : (F : ℚ) = dupNum x * (b : ℚ)^4 := by
    dsimp only [F]
    push_cast
    rw [hx]
    unfold dupNum
    field_simp [hb0.ne'] <;> ring
  have hG : (G : ℚ) = dupDen x * (b : ℚ)^4 := by
    dsimp only [G]
    push_cast
    rw [hx]
    unfold dupDen
    field_simp [hb0.ne'] <;> ring
  have hGn : G ≠ 0 := by
    have hne : (G : ℚ) ≠ 0 := hG ▸ mul_ne_zero hg hb4.ne'
    exact_mod_cast hne
  let z := dupNum x / dupDen x
  have hz : z = Rat.divInt F G := by
    rw [Rat.divInt_eq_div, hF, hG, mul_div_mul_right _ _ hb4.ne']
  obtain ⟨c, hcF, hcG⟩ := Rat.num_den_mk hGn hz
  have hcf : c ∣ F := ⟨z.num, hcF⟩
  have hcg : c ∣ G := ⟨z.den, hcG⟩
  have hbBezout :
      F*(b*(560*b^2+32*a*b+48*a^2)) + G*(63*b^3+180*a*b^2+4*a^2*b-12*a^3) =
        42875*b^7 := by
    dsimp [F,G]
    ring
  have hcbpower : c ∣ 42875*b^7 :=
    hbBezout ▸ dvd_add (dvd_mul_of_dvd_left hcf _) (dvd_mul_of_dvd_left hcg _)
  have hcb : Int.gcd c b = 1 := by
    have hf : (Int.gcd c b : ℤ) ∣ F := (Int.gcd_dvd_left c b).trans hcf
    have hb : (Int.gcd c b : ℤ) ∣ b := Int.gcd_dvd_right c b
    have hg := dvd_add hf (dvd_mul_of_dvd_left hb (18*a^2*b + 10*a*b^2 - 76*b^3))
    have he : F + b*(18*a^2*b+10*a*b^2-76*b^3) = a^4 := by dsimp [F]; ring
    rw [he] at hg
    have hgn : Int.gcd c b ∣ a.natAbs^4 := by
      simpa only [Int.natAbs_natCast, Int.natAbs_pow] using (Int.natAbs_dvd_natAbs.mpr hg)
    have hbn : Int.gcd c b ∣ x.den := by
      simpa [b] using Int.gcd_dvd_natAbs_right c b
    exact Nat.eq_one_of_dvd_coprimes (x.reduced.pow_left 4) hgn hbn
  have hcgcd : Int.gcd c (b^7) = 1 := by
    change Nat.Coprime c.natAbs b.natAbs at hcb
    simpa only [Int.gcd_eq_natAbs_gcd_natAbs, Int.natAbs_pow] using hcb.pow_right 7
  have hcbd : c ∣ (42875 : ℤ) := Int.dvd_of_dvd_mul_left_of_gcd_one hcbpower hcgcd
  have hcbound : |(c : ℚ)| ≤ 42875 := by
    have h := Int.natAbs_le_of_dvd_ne_zero hcbd (by decide)
    norm_num at h
    rw [← Int.cast_abs, ← Nat.cast_natAbs]
    exact_mod_cast h
  have hcF' : (F : ℚ) = (c : ℚ)*(z.num : ℚ) := by exact_mod_cast hcF
  have hcG' : (G : ℚ) = (c : ℚ)*(z.den : ℚ) := by exact_mod_cast hcG
  have hmax : max |(F : ℚ)| |(G : ℚ)| = |(c : ℚ)| * height35 z := by
    rw [hcF', hcG', abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (z.den : ℚ)),
      height35, mul_max_of_nonneg _ _ (abs_nonneg _)]
  have hmax' : max |(F : ℚ)| |(G : ℚ)| = (max |dupNum x| |dupDen x|)*(b : ℚ)^4 := by
    rw [hF, hG, abs_mul, abs_mul, abs_of_nonneg hb4.le, max_mul_of_nonneg _ _ hb4.le]
  have hheight : height35 x ^ 4 / 5 ≤ max |(F : ℚ)| |(G : ℚ)| := by
    rw [height35_scale, mul_pow, hmax']
    have h := mul_le_mul_of_nonneg_right (dupHeightReal x) hb4.le
    push_cast [b] at h ⊢
    simpa [div_mul_eq_mul_div, b] using h
  rw [hmax] at hheight
  have hnz : 0 ≤ height35 z := (abs_nonneg _).trans (le_max_left _ _)
  have hcap := mul_le_mul_of_nonneg_right hcbound hnz
  change height35 x ^ 4 ≤ 214375 * height35 z
  linarith



open WeierstrassCurve.Affine in
private def pointHeight35 : MazurTorsion.OrderThirtyFive.optimalQuotientModel.toAffine.Point → ℕ
  | .zero => 0
  | .some x _ _ => max x.num.natAbs x.den

private theorem height35_nat (x : ℚ) : (↑(max x.num.natAbs x.den) : ℚ) = height35 x := by
  rw [Nat.cast_max, height35, Nat.cast_natAbs, Int.cast_abs]

open WeierstrassCurve.Affine MazurTorsion.OrderThirtyFive in
private theorem pointHeight35_dup (P : optimalQuotientModel.toAffine.Point) :
    pointHeight35 P ^ 4 ≤ 214375 * pointHeight35 ((2 : ℕ) • P) := by
  cases P with
  | zero => simp [pointHeight35]
  | some x y h =>
    have hxy : y^2 + y = x^3+x^2+9*x+1 := by
      simpa [WeierstrassCurve.Affine.equation_iff, optimalQuotientModel] using h.1
    have hden : y - (-y-1) ≠ 0 := by
      intro h0
      exact optimal35_completedOrdinate_ne_zero hxy (by linarith)
    have hyne : y ≠ optimalQuotientModel.toAffine.negY x y := by
      change y ≠ -y-0*x-1
      intro h0
      exact hden (by linarith)
    have hG : (y - (-y-1))^2 = dupDen x := by unfold dupDen; linear_combination 4*hxy
    have hX :
        optimalQuotientModel.toAffine.addX x x (optimalQuotientModel.toAffine.slope x x y y) =
          dupNum x / dupDen x := by
      rw [slope_of_Y_ne rfl hyne]
      change ((3*x^2+2*1*x+9-0*y)/(y-(-y-0*x-1)))^2 +
        0*((3*x^2+2*1*x+9-0*y)/(y-(-y-0*x-1))) - 1 - x - x = _
      simp only [zero_mul, sub_zero, add_zero, mul_one]
      rw [← hG]
      field_simp [hden]
      unfold dupNum dupDen at *
      linear_combination -(1+2*x)*hG
    rw [two_nsmul, Point.add_some (fun hh => hyne hh.2)]
    change max x.num.natAbs x.den ^ 4 ≤ 214375 * _
    have hstep := height35_dup x (hG ▸ pow_ne_zero 2 hden)
    rw [← hX, ← height35_nat, ← height35_nat] at hstep
    exact_mod_cast hstep

open WeierstrassCurve.Affine MazurTorsion.OrderThirtyFive in
private theorem pointHeight35_le_59 (hfin : Finite optimalQuotientModel.toAffine.Point)
    (P : optimalQuotientModel.toAffine.Point) : pointHeight35 P ≤ 59 := by
  classical
  letI : Fintype optimalQuotientModel.toAffine.Point := Fintype.ofFinite _
  obtain ⟨Q, _, hQ⟩ := Finset.exists_max_image Finset.univ pointHeight35 Finset.univ_nonempty
  have hPQ := hQ P (Finset.mem_univ P)
  have hD := hQ ((2 : ℕ) • Q) (Finset.mem_univ ((2 : ℕ) • Q))
  have hbound := (pointHeight35_dup Q).trans (Nat.mul_le_mul_left _ hD)
  by_contra! hp
  have h60 : 60 ≤ pointHeight35 Q := hp.trans_le hPQ
  have h3 : 216000 ≤ pointHeight35 Q ^ 3 :=
    by simpa only [show (60 : ℕ)^3 = 216000 by decide] using Nat.pow_le_pow_left h60 3
  have h4 : pointHeight35 Q * 216000 ≤ pointHeight35 Q ^ 4 := by
    rw [pow_succ']
    exact Nat.mul_le_mul_left _ h3
  have hN := h4.trans hbound
  omega



private def completedNumerator (a b : ℤ) : ℤ :=
  b * (4*a^3 + 4*a^2*b + 36*a*b^2 + 5*b^3)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
private theorem smallSquareCertificate :
    ∀ i : Fin 119, ∀ j : Fin 59,
      IsSquare ((completedNumerator ((i.val : ℤ) - 59) ((j.val : ℤ) + 1) : ℤ) : ℚ) →
      (i.val : ℤ) - 59 = (j.val : ℤ) + 1 := by
  decide +kernel

private theorem squareAtSmallHeight {a : ℤ} {b : ℕ}
    (ha : a.natAbs ≤ 59) (hb : 0 < b) (hb' : b ≤ 59)
    (hs : IsSquare ((completedNumerator a b : ℤ) : ℚ)) : a = (b : ℤ) := by
  have halo : -59 ≤ a := by omega
  have hahi : a ≤ 59 := by omega
  let i : Fin 119 := ⟨(a+59).toNat, by omega⟩
  let j : Fin 59 := ⟨b-1, by omega⟩
  have hi : (i.val : ℤ) - 59 = a := by dsimp [i]; omega
  have hj : (j.val : ℤ) + 1 = (b : ℤ) := by dsimp [j]; omega
  have H := smallSquareCertificate i j
  rw [hi, hj] at H
  exact H hs

private theorem optimal35_smallHeight {a : ℤ} {b : ℕ} {x y : ℚ} (hb : 0 < b)
    (hx : x = (a : ℚ) / (b : ℚ)) (hy : y^2+y=x^3+x^2+9*x+1)
    (ha : a.natAbs ≤ 59) (hb' : b ≤ 59) : x = 1 := by
  have hbq : (b : ℚ) ≠ 0 := by positivity
  have hs : IsSquare ((completedNumerator a b : ℤ) : ℚ) := by
    refine ⟨(2*y+1)*(b:ℚ)^2, ?_⟩
    rw [hx] at hy
    field_simp [hbq] at hy
    unfold completedNumerator
    push_cast
    linear_combination -4*(b:ℚ)*hy
  rw [hx, squareAtSmallHeight ha hb hb' hs]
  push_cast
  exact div_self hbq


open Polynomial

private theorem a178612_bridge
    (rationalPoints35 : ∀ x y : ℚ, y ^ 2 + y = x ^ 3 + x ^ 2 + 9*x + 1 → x = 1) :
    ∀ p q : ℤ, p ≠ 0 → q ≠ 0 →
      0 < p ^ 6 - 4 * p ^ 4 * q + 4 * p ^ 2 * q ^ 2 + 4 * q ^ 3 →
      ¬ IsSquare (p ^ 6 - 4 * p ^ 4 * q + 4 * p ^ 2 * q ^ 2 + 4 * q ^ 3) := by
  intro p q hp hq _ hsq
  obtain ⟨s, hs⟩ := hsq
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  have hq' : (q : ℚ) ≠ 0 := by exact_mod_cast hq
  have hs' : (p : ℚ)^6 - 4*(p : ℚ)^4*q + 4*(p : ℚ)^2*(q : ℚ)^2 + 4*(q : ℚ)^3 =
      (s : ℚ)*(s : ℚ) := by exact_mod_cast hs
  let x : ℚ := (q : ℚ) / (p : ℚ)^2
  let y : ℚ := ((s : ℚ) / (p : ℚ)^3 - 1) / 2
  have hx : x ≠ 0 := div_ne_zero hq' (pow_ne_zero _ hp')
  have hy : (y + 1/2)^2 = x^3+x^2-x+1/4 := by
    dsimp only [x, y]
    field_simp [hp']
    linear_combination -4 * hs'
  let X' : ℚ := x - 2/x + 1/x^2
  let D : ℚ := 1 + 2/x^2 - 2/x^3
  let Y' : ℚ := (y+1/2)*D - 1/2
  have hIso : Y'^2+Y' = X'^3+X'^2+9*X'+1 := by
    calc
      _ = (y+1/2)^2*D^2 - 1/4 := by dsimp only [Y']; ring
      _ = _ := by
        rw [hy]
        dsimp only [D, X']
        field_simp [hx]
        ring
  have hX' := rationalPoints35 X' Y' hIso
  have hcubic : x^3 - x^2 - 2*x + 1 = 0 := by
    dsimp only [X'] at hX'
    field_simp [hx] at hX'
    linear_combination hX'
  let Q : ℤ[X] := X^3 + (-(X^2) - C 2 * X + C 1)
  have hMonic : Q.Monic := by
    apply monic_X_pow_add
    compute_degree!
  have hRoot : aeval x Q = 0 := by
    simp only [Q, map_add, map_sub, map_mul, map_neg, map_pow, aeval_X, aeval_C]
    change x^3 + (-x^2 - 2*x + 1) = 0
    linear_combination hcubic
  obtain ⟨z, hxz, hz⟩ := exists_integer_of_is_root_of_monic hMonic hRoot
  have hz1 : z ∣ (1 : ℤ) := by
    simpa [Q, Polynomial.coeff_X_pow, coeff_mul_X] using hz
  rw [hxz] at hcubic
  obtain ⟨c, hc⟩ := hz1
  obtain rfl | rfl := Int.eq_one_or_neg_one_of_mul_eq_one hc.symm <;> norm_num at hcubic


open WeierstrassCurve.Affine MazurTorsion.OrderThirtyFive in
private theorem rationalPoints35 (x y : ℚ) (h : y^2+y = x^3+x^2+9*x+1) : x = 1 := by
  have hN : optimalQuotientModel.toAffine.Nonsingular x y :=
    optimalQuotientModel.toAffine.equation_iff_nonsingular.mp (by
      simpa [WeierstrassCurve.Affine.equation_iff, optimalQuotientModel] using h)
  let P := WeierstrassCurve.Affine.Point.some x y hN
  have hB := pointHeight35_le_59 optimalQuotientModel_finite P
  change max x.num.natAbs x.den ≤ 59 at hB
  exact optimal35_smallHeight x.den_pos x.num_div_den.symm h
    ((le_max_left _ _).trans hB) ((le_max_right _ _).trans hB)

theorem OMA.solution : type_of% @OMA.S_oeis_a178612.main :=
  a178612_bridge rationalPoints35


/-
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
-/
