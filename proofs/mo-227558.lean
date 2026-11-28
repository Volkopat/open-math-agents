import OMAStatements.S_mo_227558
import Mathlib

open OMA.S_mo_227558
open Real

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_227558.main) := by
  intro h
  set a := Real.arccos (1 / Real.sqrt 3) with ha
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have h3gt : 1 < Real.sqrt 3 := by nlinarith
  have hx1 : 1 / Real.sqrt 3 < 1 := by rw [div_lt_one h3pos]; exact h3gt
  have hx0 : 0 < 1 / Real.sqrt 3 := by positivity
  have hc : cos a = 1 / Real.sqrt 3 := Real.cos_arccos (by linarith) hx1.le
  have hc2 : cos a ^ 2 = 1 / 3 := by rw [hc, div_pow, h3]; norm_num
  have hcpos : 0 < cos a := by rw [hc]; exact hx0
  have hapos : 0 < a := Real.arccos_pos.2 hx1
  have halt : a < Real.pi := Real.arccos_lt_pi.2 (by linarith)
  have hs : 0 < sin a := Real.sin_pos_of_pos_of_lt_pi hapos halt
  have t1 : cos (2 * Real.pi / 3) = -1 / 2 := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.cos_pi_sub, Real.cos_pi_div_three]; norm_num
  have t2 : sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    have : 2 * Real.pi / 3 = Real.pi - Real.pi / 3 := by ring
    rw [this, Real.sin_pi_sub, Real.sin_pi_div_three]
  have p1 : cos (Real.pi - a) = - cos a := Real.cos_pi_sub a
  have p2 : sin (Real.pi - a) = sin a := Real.sin_pi_sub a
  let θ : Fin 6 → ℝ := ![0, 2 * Real.pi / 3, -(2 * Real.pi / 3), 0, 2 * Real.pi / 3,
    -(2 * Real.pi / 3)]
  let φ : Fin 6 → ℝ := ![a, a, a, Real.pi - a, Real.pi - a, Real.pi - a]
  have heqs := (h θ φ).1
  have hoct := heqs (by
    simp only [Fin.sum_univ_six, θ, φ]
    simp [Real.cos_two_mul, Real.sin_two_mul, t1, t2, p1, p2]
    constructorm* _ ∧ _
    all_goals nlinarith [hc2])
  obtain ⟨u, -, hu⟩ := hoct
  have h0 : sphPoint (θ 0) (φ 0) ∈ Set.range (fun k => sphPoint (θ k) (φ k)) := ⟨0, rfl⟩
  rw [hu] at h0
  have hneg : -sphPoint (θ 0) (φ 0) ∈ ({u 0, -u 0, u 1, -u 1, u 2, -u 2} :
      Set (EuclideanSpace ℝ (Fin 3))) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h0 ⊢
    rcases h0 with h0 | h0 | h0 | h0 | h0 | h0 <;> rw [h0] <;> simp
  rw [← hu] at hneg
  obtain ⟨k, hk⟩ := hneg
  have hx := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w 0) hk
  have hz := congrArg (fun w : EuclideanSpace ℝ (Fin 3) => w 2) hk
  fin_cases k <;>
    simp [sphPoint, θ, φ, t1, p1, p2] at hx hz <;> nlinarith
