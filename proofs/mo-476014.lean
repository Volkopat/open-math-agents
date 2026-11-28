import OMAStatements.S_mo_476014

/-!
Retains @Solfanbtc's counterexample from PR #26602 and uses the square-root
inequality method in @etaubman's earlier companion to statement PR #21258,
commit ebbf5ffd2085a61270d18e1a587164ed121ba7f8. The same positive functions,
half-convexity, sandwich bounds and nonconvexity witness are preserved.
-/

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_476014.main) := by
  intro h
  let f : ℝ → ℝ := fun x => 1 + x + Real.sqrt x
  let g : ℝ → ℝ := fun x => 1 + x
  have hconv : ConvexOn ℝ (Set.Ioi 0) f := by
    apply h (1 / 2) f g 1 2 (by norm_num) (by norm_num)
    · intro x hx
      dsimp [f]
      linarith [Real.sqrt_nonneg x]
    · intro x hx y hy u hu0 hu1
      dsimp [f]
      rw [← Real.sqrt_eq_rpow u, ← Real.sqrt_eq_rpow (1 - u)]
      have hsu : u ≤ Real.sqrt u := Real.le_sqrt_self_iff.mpr hu1.le
      have hs1u : 1 - u ≤ Real.sqrt (1 - u) :=
        Real.le_sqrt_self_iff.mpr (by linarith)
      have hsqrt_add :
          Real.sqrt (u * x + (1 - u) * y) ≤
            Real.sqrt u * Real.sqrt x + Real.sqrt (1 - u) * Real.sqrt y := by
        rw [← Real.sqrt_mul hu0.le, ← Real.sqrt_mul (sub_nonneg.mpr hu1.le)]
        apply Real.sqrt_le_iff.mpr
        refine ⟨by positivity, ?_⟩
        nlinarith [Real.sq_sqrt (mul_nonneg hu0.le hx.le),
          Real.sq_sqrt (mul_nonneg (sub_nonneg.mpr hu1.le) hy.le),
          mul_nonneg (Real.sqrt_nonneg (u * x)) (Real.sqrt_nonneg ((1 - u) * y))]
      nlinarith
    · intro x hx
      dsimp [g]
      linarith
    · refine ⟨convex_Ioi 0, ?_⟩
      intro x hx y hy a b ha hb hab
      change 1 + (a * x + b * y) ≤ a * (1 + x) + b * (1 + y)
      nlinarith
    · norm_num
    · norm_num
    · intro x hx
      dsimp [f, g]
      have hnn : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
      have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hx)
      constructor <;> nlinarith
  have hineq := hconv.2 (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (9 : ℝ) ∈ Set.Ioi 0 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (by norm_num)
  change 1 + ((1 / 2 : ℝ) * 1 + (1 / 2 : ℝ) * 9) +
      Real.sqrt ((1 / 2 : ℝ) * 1 + (1 / 2 : ℝ) * 9) ≤
    (1 / 2 : ℝ) * (1 + 1 + Real.sqrt 1) + (1 / 2 : ℝ) * (1 + 9 + Real.sqrt 9) at hineq
  have h9 : Real.sqrt 9 = 3 :=
    (Real.sqrt_eq_iff_mul_self_eq (by norm_num) (by norm_num)).mpr (by norm_num)
  norm_num [h9] at hineq
  have hs5 : 2 < Real.sqrt 5 := Real.lt_sqrt_of_sq_lt (by norm_num)
  linarith
