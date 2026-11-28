import OMAStatements.S_mo_374711
import Mathlib

-- Problem mo-374711: for positive definite real matrices A, B with quadratic forms q_A, q_B, a vector x
-- satisfies q_A(x) = sqrt(q_B(x)) if and only if x = 0 or x = sqrt(q_B(u)) u for some u with q_A(u) = 1.
-- Upstream: statements/mo-374711.lean (declaration OMA.S_mo_374711.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: quadratic forms scale by q(c u) = c^2 q(u). If x != 0 and q_A(x) = sqrt(q_B(x)), put s = q_A(x) > 0,
-- c = sqrt(s) and u = x / c. Then q_A(u) = 1, q_B(x) = s^2, so q_B(u) = s^2 / s = s and sqrt(q_B(u)) u = c u = x.
-- Conversely x = 0 clearly works, and if x = c u with c = sqrt(q_B(u)) and q_A(u) = 1, then q_A(x) = c^2 and
-- sqrt(q_B(x)) = sqrt(c^2 q_B(u)) = sqrt(q_B(u)^2) = q_B(u) = c^2.

open OMA.S_mo_374711 Matrix

theorem OMA.solution : type_of% @OMA.S_mo_374711.main := by
  intro n A B hA hB x
  have hscale : ∀ (M : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) (u : Fin n → ℝ),
      qform M (c • u) = c ^ 2 * qform M u := by
    intro M c u
    unfold qform
    rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    ring
  have hposA : ∀ y : Fin n → ℝ, y ≠ 0 → 0 < qform A y := by
    intro y hy
    have h := hA.dotProduct_mulVec_pos hy
    rwa [star_trivial] at h
  have hnnB : ∀ y : Fin n → ℝ, 0 ≤ qform B y := by
    intro y
    have h := hB.posSemidef.dotProduct_mulVec_nonneg y
    rwa [star_trivial] at h
  have hzero : ∀ M : Matrix (Fin n) (Fin n) ℝ, qform M 0 = 0 := by
    intro M
    simp [qform]
  constructor
  · intro hx
    by_cases hx0 : x = 0
    · left
      exact hx0
    · right
      have hs : 0 < qform A x := hposA x hx0
      have hsne : qform A x ≠ 0 := hs.ne'
      have hc : 0 < Real.sqrt (qform A x) := Real.sqrt_pos.mpr hs
      have hc2 : Real.sqrt (qform A x) ^ 2 = qform A x := Real.sq_sqrt hs.le
      have hBx : qform B x = qform A x ^ 2 := by
        have h1 : Real.sqrt (qform B x) ^ 2 = qform B x := Real.sq_sqrt (hnnB x)
        rw [← h1, ← hx]
      refine ⟨(Real.sqrt (qform A x))⁻¹ • x, ?_, ?_⟩
      · rw [hscale, inv_pow, hc2]
        exact inv_mul_cancel₀ hsne
      · have h2 : (qform A x)⁻¹ * qform A x ^ 2 = qform A x := by
          field_simp
        rw [hscale, inv_pow, hc2, hBx, h2, smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  · rintro (rfl | ⟨u, hu1, rfl⟩)
    · rw [hzero, hzero, Real.sqrt_zero]
    · have hnn := hnnB u
      rw [hscale, hscale, hu1, mul_one, Real.sq_sqrt hnn, Real.sqrt_mul_self hnn]
