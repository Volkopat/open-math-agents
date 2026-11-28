import OMAStatements.S_mo_225439

open Set Matrix OMA.S_mo_225439
open scoped BigOperators

private abbrev V := Fin 3 → ℝ

private noncomputable def apex : V := fun i => if i = 0 then 2/3 else if i = 1 then 1/3 else 0
private def axis (j : Fin 3) : V := Pi.single j 1

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_225439.main) := by
  classical
  intro claim
  have f01 : (0 : Fin 3) ≠ 1 := by decide
  have f02 : (0 : Fin 3) ≠ 2 := by decide
  have f10 : (1 : Fin 3) ≠ 0 := by decide
  have f12 : (1 : Fin 3) ≠ 2 := by decide
  have f20 : (2 : Fin 3) ≠ 0 := by decide
  have f21 : (2 : Fin 3) ≠ 1 := by decide
  let S : Finset V := {apex, axis 0, axis 2}
  let H := convexHull ℝ (S : Set V)
  have hs : (S : Set V) ⊆ stdSimplex ℝ (Fin 3) := by
    intro z hz
    have hz' : z = apex ∨ z = axis 0 ∨ z = axis 2 := by simpa [S] using hz
    rcases hz' with rfl | rfl | rfl
    · change (∀ i, 0 ≤ apex i) ∧ (∑ i, apex i) = 1
      constructor
      · intro i
        by_cases h0 : i = 0 <;> by_cases h1 : i = 1 <;> norm_num [apex, h0, h1]
      · norm_num [apex, Fin.sum_univ_three, f10, f20, f21]
    · exact single_mem_stdSimplex ℝ 0
    · exact single_mem_stdSimplex ℝ 2
  have hsimplex : H ⊆ stdSimplex ℝ (Fin 3) :=
    convexHull_min hs (convex_stdSimplex ℝ (Fin 3))
  let K : Set V := {z | z 1 ≤ 1/3 ∧ 2 * z 1 ≤ z 0}
  have hK : H ⊆ K := by
    apply convexHull_min
    · intro z hz
      have hz' : z = apex ∨ z = axis 0 ∨ z = axis 2 := by simpa [S] using hz
      rcases hz' with rfl | rfl | rfl <;>
        norm_num [K, apex, axis, Pi.single_apply, f01, f02, f10, f12, f20, f21]
    · intro x hx y hy a b ha hb hab
      change x 1 ≤ 1/3 ∧ 2 * x 1 ≤ x 0 at hx
      change y 1 ≤ 1/3 ∧ 2 * y 1 ≤ y 0 at hy
      change a * x 1 + b * y 1 ≤ 1/3 ∧
          2 * (a * x 1 + b * y 1) ≤ a * x 0 + b * y 0
      constructor
      · nlinarith [mul_le_mul_of_nonneg_left hx.1 ha, mul_le_mul_of_nonneg_left hy.1 hb]
      · nlinarith [mul_le_mul_of_nonneg_left hx.2 ha, mul_le_mul_of_nonneg_left hy.2 hb]
  have unique (x : V) (hx : x ∈ H) (h₁ : x 1 = 1/3) : x = apex := by
    have hk : 2 * x 1 ≤ x 0 := (hK hx).2
    have hS : (∀ i, 0 ≤ x i) ∧ (∑ i, x i) = 1 := hsimplex hx
    rw [Fin.sum_univ_three] at hS
    have h₀ : x 0 = 2/3 := by linarith [hS.1 2, hS.2]
    have h₂ : x 2 = 0 := by linarith [hS.1 2, hS.2]
    funext i
    fin_cases i
    · exact h₀
    · exact h₁
    · exact h₂
  have hapex : apex ∈ H.extremePoints ℝ := by
    apply mem_extremePoints.mpr
    refine ⟨subset_convexHull ℝ _ (by simp [S]), fun x hx y hy hseg => ?_⟩
    obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
    have hz := congrFun heq (1 : Fin 3)
    change a * x 1 + b * y 1 = apex 1 at hz
    have hp1 : apex 1 = 1/3 := by norm_num [apex, f10]
    rw [hp1] at hz
    have hxle : x 1 ≤ 1/3 := (hK hx).1
    have hyle : y 1 ≤ 1/3 := (hK hy).1
    refine ⟨unique x hx ?_, unique y hy ?_⟩
    · by_contra hne
      have hlt : x 1 < 1/3 := lt_of_le_of_ne hxle hne
      nlinarith [mul_lt_mul_of_pos_left hlt ha, mul_le_mul_of_nonneg_left hyle hb.le]
    · by_contra hne
      have hlt : y 1 < 1/3 := lt_of_le_of_ne hyle hne
      nlinarith [mul_le_mul_of_nonneg_left hxle ha.le, mul_lt_mul_of_pos_left hlt hb]
  rcases claim 3 S hsimplex apex hapex with hleft | hright
  · have h := hleft (axis 0) (subset_convexHull ℝ _ (by simp [S]))
    norm_num [dotProduct, apex, axis, Pi.single_apply, Fin.sum_univ_three,
      f01, f02, f10, f12, f20, f21] at h
  · have h := hright (axis 2) (subset_convexHull ℝ _ (by simp [S]))
    norm_num [dotProduct, apex, axis, Pi.single_apply, Fin.sum_univ_three,
      f01, f02, f10, f12, f20, f21] at h