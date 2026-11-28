import OMAStatements.S_oeis_a175769
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

namespace OMA.P_oeis_a175769

open OMA.S_oeis_a175769

private noncomputable def s5 : ℝ := Real.sqrt 5
private noncomputable def a5 : ℝ := (s5 - 1) / 4
private noncomputable def b5 : ℝ := -(s5 + 1) / 4
private noncomputable def u5 : ℝ := Real.sqrt (10 + 2 * s5) / 4
private noncomputable def v5 : ℝ := Real.sqrt (10 - 2 * s5) / 4

/-- L. M. Kelly's 8-point isosceles set in `ℝ^3`: the 5 vertices of a regular pentagon on
the unit circle in `z = 0`, its center `(0, 0, 0)`, and the two poles `(0, 0, ±1)`. -/
private noncomputable def kellyPt : Fin 8 → ℝ × ℝ × ℝ
  | ⟨0, _⟩ => (1, 0, 0)
  | ⟨1, _⟩ => (a5, u5, 0)
  | ⟨2, _⟩ => (b5, v5, 0)
  | ⟨3, _⟩ => (b5, -v5, 0)
  | ⟨4, _⟩ => (a5, -u5, 0)
  | ⟨5, _⟩ => (0, 0, 0)
  | ⟨6, _⟩ => (0, 0, 1)
  | ⟨7, _⟩ => (0, 0, -1)

private lemma s5_sq : s5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

private lemma s5_pos : 0 < s5 := Real.sqrt_pos.mpr (by norm_num)

private lemma s5_lt_3 : s5 < 3 := by
  have h1 : s5 ^ 2 < 3 ^ 2 := by rw [s5_sq]; norm_num
  nlinarith [s5_pos]

private lemma s5_gt_2 : 2 < s5 := by
  have h1 : 2 ^ 2 < s5 ^ 2 := by rw [s5_sq]; norm_num
  nlinarith [s5_pos]

private lemma u5_sq : u5 ^ 2 = (10 + 2 * s5) / 16 := by
  unfold u5
  rw [div_pow, Real.sq_sqrt (by linarith [s5_pos])]
  norm_num

private lemma v5_sq : v5 ^ 2 = (10 - 2 * s5) / 16 := by
  unfold v5
  rw [div_pow, Real.sq_sqrt (by linarith [s5_lt_3])]
  norm_num

private lemma u5_pos : 0 < u5 := by
  unfold u5
  exact div_pos (Real.sqrt_pos.mpr (by linarith [s5_pos])) (by norm_num)

private lemma v5_pos : 0 < v5 := by
  unfold v5
  exact div_pos (Real.sqrt_pos.mpr (by linarith [s5_lt_3])) (by norm_num)

private lemma u5_mul_v5 : u5 * v5 = s5 / 4 := by
  have hsq : (u5 * v5) ^ 2 = (s5 / 4) ^ 2 := by
    rw [mul_pow, u5_sq, v5_sq, div_pow]
    have h := s5_sq
    nlinarith
  have hnn1 : 0 ≤ u5 * v5 := (mul_pos u5_pos v5_pos).le
  have hnn2 : 0 ≤ s5 / 4 := (div_pos s5_pos (by norm_num)).le
  nlinarith

/-- Exact distance tag among `{0, 1, 2, 4, (5 - √5)/2, (5 + √5)/2}` for Kelly's 8 points. -/
private def dTag (i j : Fin 8) : ℕ :=
  if i = j then 0
  else if i.1 < 5 ∧ j.1 < 5 then
    let d := (i.1 + 5 - j.1) % 5
    if d = 1 ∨ d = 4 then 4 else 5
  else if (i.1 < 5 ∧ j.1 = 5) ∨ (j.1 < 5 ∧ i.1 = 5) then 1
  else if (i.1 < 5 ∧ 6 ≤ j.1) ∨ (j.1 < 5 ∧ 6 ≤ i.1) then 2
  else if (i.1 = 5 ∧ 6 ≤ j.1) ∨ (j.1 = 5 ∧ 6 ≤ i.1) then 1
  else 3

private noncomputable def tagVal : ℕ → ℝ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 4
  | 4 => (5 - s5) / 2
  | _ => (5 + s5) / 2

private lemma distSq3_kellyPt (i j : Fin 8) : distSq3 (kellyPt i) (kellyPt j) = tagVal (dTag i j) := by
  have hs := s5_sq
  have hu := u5_sq
  have hv := v5_sq
  have huv := u5_mul_v5
  fin_cases i <;> fin_cases j <;>
    simp only [kellyPt, distSq3, dTag, tagVal, a5, b5, Fin.mk_eq_mk] <;>
    norm_num <;>
    nlinarith

private lemma dTag_isosceles :
    ∀ i j k : Fin 8, i ≠ j → i ≠ k → j ≠ k →
      dTag i j = dTag i k ∨ dTag i j = dTag j k ∨ dTag i k = dTag j k := by
  decide

private lemma kellyPt_inj : Function.Injective kellyPt := by
  intro i j hij
  have h0 : distSq3 (kellyPt i) (kellyPt j) = 0 := by
    rw [hij]; unfold distSq3; ring
  rw [distSq3_kellyPt] at h0
  by_contra hne
  have hpos : 0 < tagVal (dTag i j) := by
    have hs3 := s5_lt_3
    have hs0 := s5_pos
    fin_cases i <;> fin_cases j <;> simp_all [dTag, tagVal] <;> linarith
  linarith

private theorem prove_disproof : ¬ (type_of% @OMA.S_oeis_a175769.main) := by
  intro hmain
  let S : Finset (ℝ × ℝ × ℝ) := Finset.univ.image kellyPt
  have hiso : IsIsoscelesSet3 S := by
    intro p hp q hq r hr hpq hpr hqr
    simp only [S, Finset.mem_image, Finset.mem_univ, true_and] at hp hq hr
    rcases hp with ⟨i, rfl⟩
    rcases hq with ⟨j, rfl⟩
    rcases hr with ⟨k, rfl⟩
    have hij : i ≠ j := fun h => hpq (congrArg kellyPt h)
    have hik : i ≠ k := fun h => hpr (congrArg kellyPt h)
    have hjk : j ≠ k := fun h => hqr (congrArg kellyPt h)
    rw [distSq3_kellyPt, distSq3_kellyPt, distSq3_kellyPt]
    rcases dTag_isosceles i j k hij hik hjk with h1 | h2 | h3
    · exact Or.inl (congrArg tagVal h1)
    · exact Or.inr (Or.inl (congrArg tagVal h2))
    · exact Or.inr (Or.inr (congrArg tagVal h3))
  have hcard : S.card = 8 := by
    rw [Finset.card_image_of_injective _ kellyPt_inj, Finset.card_univ, Fintype.card_fin]
  have hle := hmain S hiso
  omega

end OMA.P_oeis_a175769

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a175769.main) :=
  OMA.P_oeis_a175769.prove_disproof
