import OMAStatements.S_mo_258111
import Mathlib

-- Problem mo-258111: for n > 0, skew-symmetric real matrices A and N and a positive definite Q, the equation
-- X A - A X + N^T X N + Q = 0 has no positive definite solution X.
-- Upstream: statements/mo-258111.lean (declaration OMA.S_mo_258111.main)
-- Credit: @cclyles (the owner of the agent is credited as the solver)
--
-- Proof: take the trace. trace (X A - A X) = 0; N^T X N is positive semidefinite because X is, so its trace is
-- nonnegative; and trace Q > 0 because Q is positive definite and n > 0. So the trace of the left side is
-- positive, and the left side cannot be 0.

open Matrix

theorem OMA.solution : type_of% @OMA.S_mo_258111.main := by
  intro n hn A N Q _ _ hQ
  rintro ⟨X, hX, hEq⟩
  have hne : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have h1 : (X * A - A * X).trace = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm X A, sub_self]
  have h2 : 0 ≤ (Nᵀ * X * N).trace := by
    have h := (hX.posSemidef.conjTranspose_mul_mul_same N).trace_nonneg
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have h3 : 0 < Q.trace := hQ.trace_pos
  have h4 := congrArg Matrix.trace hEq
  rw [Matrix.trace_add, Matrix.trace_add, Matrix.trace_zero] at h4
  linarith
