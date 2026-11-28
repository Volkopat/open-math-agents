import OMAStatements.S_mo_403038
import Mathlib

-- Problem: mo-403038, is there a member of the family
--   x^2 + (x^2 + 1)(a x^8 + b x^6 + c x^5 + d x^4 + e x^3 + f x^2 + g),  a < 0 < g,
-- with ten distinct real roots?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- Yes: a = -1/25000, b = 1/64, c = e = -4/25, d = 1/2, f = -65/64, g = 1/25000.
-- (Found from ten roots u_j, -1/u_j with u_j = cot(t_j / 2), sum t_j = 3 pi / 2 and
-- sum cot t_j = 0, then rounded; only the sign pattern below is used.)
-- The polynomial F has alternating signs at -100, -1, -3/10, -1/5, -1/10, 0, 1, 33/10, 5, 10,
-- 100, so the intermediate value theorem gives ten roots in ten disjoint intervals. Since F has
-- degree at most 10 and is not zero, these are all its roots.

namespace MO403038

open Polynomial

noncomputable def F (x : ℝ) : ℝ :=
  x ^ 2 + (x ^ 2 + 1) * ((-1 / 25000) * x ^ 8 + (1 / 64) * x ^ 6 + (-4 / 25) * x ^ 5 +
    (1 / 2) * x ^ 4 + (-4 / 25) * x ^ 3 + (-65 / 64) * x ^ 2 + 1 / 25000)

theorem F_cont : Continuous F := by
  unfold F
  fun_prop

theorem ivt (u v : ℝ) (huv : u < v) (h : F u * F v < 0) : ∃ x, u < x ∧ x < v ∧ F x = 0 := by
  have hu0 : F u ≠ 0 := fun h0 => by
    rw [h0, zero_mul] at h
    exact lt_irrefl _ h
  rcases lt_or_gt_of_ne hu0 with hu | hu
  · have hv : 0 < F v := by
      by_contra hneg
      have h1 : F v ≤ 0 := not_lt.mp hneg
      have h2 := mul_nonneg_of_nonpos_of_nonpos hu.le h1
      linarith
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo huv.le F_cont.continuousOn ⟨hu, hv⟩
    exact ⟨x, hx.1, hx.2, hfx⟩
  · have hv : F v < 0 := by
      by_contra hneg
      have h1 : 0 ≤ F v := not_lt.mp hneg
      have h2 := mul_nonneg hu.le h1
      linarith
    obtain ⟨x, hx, hfx⟩ := intermediate_value_Ioo' huv.le F_cont.continuousOn ⟨hv, hu⟩
    exact ⟨x, hx.1, hx.2, hfx⟩

noncomputable def p : ℝ[X] :=
  X ^ 2 + (X ^ 2 + 1) * (C (-1 / 25000) * X ^ 8 + C (1 / 64) * X ^ 6 + C (-4 / 25) * X ^ 5 +
    C (1 / 2) * X ^ 4 + C (-4 / 25) * X ^ 3 + C (-65 / 64) * X ^ 2 + C (1 / 25000))

theorem p_eval (x : ℝ) : p.eval x = F x := by
  simp [p, F]

theorem p_deg : p.natDegree ≤ 10 := by
  unfold p
  compute_degree

theorem p_ne : p ≠ 0 := by
  intro h
  have h0 := p_eval 0
  rw [h] at h0
  simp [F] at h0

theorem key : ∃ r : Fin 10 → ℝ, Function.Injective r ∧ ∀ x : ℝ, F x = 0 ↔ ∃ j, r j = x := by
  obtain ⟨x0, l0, u0, h0⟩ := ivt (-100) (-1) (by norm_num) (by unfold F; norm_num)
  obtain ⟨x1, l1, u1, h1⟩ := ivt (-1) (-3 / 10) (by norm_num) (by unfold F; norm_num)
  obtain ⟨x2, l2, u2, h2⟩ := ivt (-3 / 10) (-1 / 5) (by norm_num) (by unfold F; norm_num)
  obtain ⟨x3, l3, u3, h3⟩ := ivt (-1 / 5) (-1 / 10) (by norm_num) (by unfold F; norm_num)
  obtain ⟨x4, l4, u4, h4⟩ := ivt (-1 / 10) 0 (by norm_num) (by unfold F; norm_num)
  obtain ⟨x5, l5, u5, h5⟩ := ivt 0 1 (by norm_num) (by unfold F; norm_num)
  obtain ⟨x6, l6, u6, h6⟩ := ivt 1 (33 / 10) (by norm_num) (by unfold F; norm_num)
  obtain ⟨x7, l7, u7, h7⟩ := ivt (33 / 10) 5 (by norm_num) (by unfold F; norm_num)
  obtain ⟨x8, l8, u8, h8⟩ := ivt 5 10 (by norm_num) (by unfold F; norm_num)
  obtain ⟨x9, l9, u9, h9⟩ := ivt 10 100 (by norm_num) (by unfold F; norm_num)
  obtain ⟨r, hr⟩ : ∃ r : Fin 10 → ℝ, r = ![x0, x1, x2, x3, x4, x5, x6, x7, x8, x9] := ⟨_, rfl⟩
  have hmono : StrictMono r := by
    intro i j hij
    rw [hr]
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> linarith
  have hinj : Function.Injective r := hmono.injective
  have hroot : ∀ j, F (r j) = 0 := by
    intro j
    rw [hr]
    fin_cases j
    exacts [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  have hmem : ∀ j, r j ∈ p.roots := by
    intro j
    rw [Polynomial.mem_roots p_ne, Polynomial.IsRoot, p_eval]
    exact hroot j
  have hcard : (Finset.univ.image r).card = 10 := by
    rw [Finset.card_image_of_injective _ hinj]
    simp
  have hsub : Finset.univ.image r ⊆ p.roots.toFinset := by
    intro x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hx
    exact Multiset.mem_toFinset.mpr (hmem j)
  have hle : p.roots.toFinset.card ≤ 10 :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' p).trans p_deg)
  have heq : Finset.univ.image r = p.roots.toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; exact hle)
  refine ⟨r, hinj, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · have hx' : x ∈ p.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots p_ne, Polynomial.IsRoot, p_eval]
      exact hx
    rw [← heq] at hx'
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hx'
    exact ⟨j, hj⟩
  · rintro ⟨j, rfl⟩
    exact hroot j

end MO403038

theorem OMA.solution : type_of% @OMA.S_mo_403038.main := by
  refine ⟨-1 / 25000, 1 / 64, -4 / 25, 1 / 2, -4 / 25, -65 / 64, 1 / 25000, by norm_num,
    by norm_num, ?_⟩
  exact MO403038.key
