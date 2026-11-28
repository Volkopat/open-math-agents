import OMAReductions.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1_H2_R1_H2_R1

namespace OMA.P_Erdos313_H2_H2_H2_H1

/-- Four equal coordinates slightly above `4R/c` and a large fifth coordinate solving the
linear equation in it. -/
theorem realPoints : ∀ R c p : ℕ, 4 < R → 3 < p → c*p = R+1 →
    ∀ B : ℝ, ∃ x : Fin 5 → ℝ, (∀ i, (p:ℝ) < x i) ∧ B < x 4 ∧
      (c:ℝ) * (∏ i, x i) = (R:ℝ) * (∑ i : Fin 5, ∏ j ∈ Finset.univ.erase i, x j) + 1 := by
  intro R c p hR hp hc B
  have hcR : ((c:ℝ)) * p = R + 1 := by exact_mod_cast hc
  have hpR : (3:ℝ) < p := by exact_mod_cast hp
  have hRR : (4:ℝ) < R := by exact_mod_cast hR
  have cpos : (0:ℝ) < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; simp at hc
    · exact_mod_cast h
  set δ : ℝ := 1 / (|B| + 1) with hδ
  have δpos : 0 < δ := by positivity
  have δle : δ ≤ 1 := by
    rw [hδ, div_le_one (by positivity)]; linarith [abs_nonneg B]
  set t : ℝ := 4 * R / c + δ with ht
  have t0 : (p:ℝ) < 4 * R / c := by
    rw [lt_div_iff₀ cpos]; nlinarith
  have tp : (p:ℝ) < t := by linarith
  have tpos : 0 < t := by linarith
  have den : c * t ^ 4 - 4 * R * t ^ 3 = t ^ 3 * (c * δ) := by
    rw [ht]; field_simp; ring
  have denpos : 0 < t ^ 3 * (c * δ) := by positivity
  set y : ℝ := (R * t ^ 4 + 1) / (t ^ 3 * (c * δ)) with hy
  have Rc : (c:ℝ) ≤ R := by nlinarith
  have ylow : t / δ ≤ y := by
    rw [hy, div_le_div_iff₀ δpos denpos]
    nlinarith [pow_pos tpos 4, mul_le_mul_of_nonneg_left Rc (le_of_lt (pow_pos tpos 4))]
  have tδ : t ≤ t / δ := by
    rw [le_div_iff₀ δpos]; nlinarith
  have Bt : B < t / δ := by
    rw [hδ, div_div_eq_mul_div, div_one]
    have : (1:ℝ) < t := by linarith
    nlinarith [abs_nonneg B, le_abs_self B]
  refine ⟨![t, t, t, t, y], ?_, by simpa using lt_of_lt_of_le Bt ylow, ?_⟩
  · intro i
    fin_cases i <;> simp <;> linarith
  · have e0 : (Finset.univ.erase (0:Fin 5)) = {1,2,3,4} := by decide
    have e1 : (Finset.univ.erase (1:Fin 5)) = {0,2,3,4} := by decide
    have e2 : (Finset.univ.erase (2:Fin 5)) = {0,1,3,4} := by decide
    have e3 : (Finset.univ.erase (3:Fin 5)) = {0,1,2,4} := by decide
    have e4 : (Finset.univ.erase (4:Fin 5)) = {0,1,2,3} := by decide
    simp only [Fin.prod_univ_five, Fin.sum_univ_five, e0, e1, e2, e3, e4]
    simp
    have key : y * (c * t ^ 4 - 4 * R * t ^ 3) = R * t ^ 4 + 1 := by
      rw [den, hy]; field_simp
    linear_combination key

end OMA.P_Erdos313_H2_H2_H2_H1

theorem OMA.solution :
    OMA.R_Erdos313_erdos_313_variants_primary_pseudoperfect_are_infinite_R1_H2_R1_H2_R1_H2_R1.H1 := by
  intro R c p hR hp hc B
  exact OMA.P_Erdos313_H2_H2_H2_H1.realPoints R c p hR hp hc B
