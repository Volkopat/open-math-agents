import OMAReductions.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R2

-- Step TotalColoringConjecture.total_coloring_conjecture.variants.maxDegree_le_five.R1.H2.R1.H3.R2.H1: hypothesis H1 of reduction TotalColoringConjecture.total_coloring_conjecture.variants.maxDegree_le_five.R1.H2.R1.H3.R2
-- Credit: @luciusacarr
-- H1 := ∀ (W : Type) [Fintype W] [DecidableEq W] (m : W → W → ℕ),     (∀ x y, m x y = m y x) → (∀ x, m x x = 0) → ∀ (c : W → Bool) (v : W),     let score (a : W → Bool) : ℤ := ∑ x, ∑ y, if a x = a y then 0 else (m x y : ℤ)     let side (v : W) : ℤ := ∑ y, if c v = c y then (m v y : ℤ) else 0     score (fun x => if x = v then !(c v) else c x) - score c =       2 * (2 * side v - ∑ y, (m v y : ℤ))

/-! Flipping the colour of `v` only changes the terms of the double sum with `x = v` or `y = v`.
Pointwise, the change of the `(x, y)` term is `[x = v] e y + [y = v] e x`, where
`e y = m v y` if `c v = c y` and `-m v y` otherwise (using `m x y = m y x` and `m v v = 0`).
Summing gives `2 Σ_y e y = 2 (2 side v - Σ_y m v y)`. -/

theorem OMA.solution :
    OMA.R_TotalColoringConjecture_total_coloring_conjecture_variants_maxDegree_le_five_R1_H2_R1_H3_R2.H1 := by
  intro W _ _ m hsym hdiag c v
  simp only
  set e : W → ℤ := fun y => if c v = c y then (m v y : ℤ) else -(m v y : ℤ) with he
  have key : ∀ x y : W,
      ((if (if x = v then !(c v) else c x) = (if y = v then !(c v) else c y) then 0 else (m x y : ℤ))
        - (if c x = c y then 0 else (m x y : ℤ)))
      = (if x = v then e y else 0) + (if y = v then e x else 0) := by
    intro x y
    by_cases hx : x = v <;> by_cases hy : y = v
    · subst hx; subst hy; simp [he, hdiag]
    · subst hx
      simp only [if_pos rfl, if_neg hy, he]
      cases h1 : c x <;> cases h2 : c y <;> simp
    · subst hy
      simp only [if_neg hx, if_pos rfl, he, hsym x y]
      cases h1 : c x <;> cases h2 : c y <;> simp
    · simp [hx, hy]
  rw [← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib, key, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  have hsum : ∑ x : W, (∑ y : W, if x = v then e y else 0) = ∑ y, e y := by
    rw [Finset.sum_comm]; simp
  rw [hsum]
  have he2 : ∀ y, e y = 2 * (if c v = c y then (m v y : ℤ) else 0) - (m v y : ℤ) := by
    intro y; simp only [he]; split_ifs <;> ring
  simp_rw [he2, Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring
