import FormalConjectures.Arxiv.«2607.05739».TanArctanSum

/-!
# The rational tangent recurrence

Write the Gaussian product as A_n + i B_n. Multiplication by 1 + (n+1)i
provides the two component recurrences. To divide by A_n, prove over ZMod 3
that A_n is nonzero and B_n = n(2-n)A_n. A finite-field step and induction
establish this for every n, without a bound on the index.

This simplifies the modular argument in the original proof by @rorcores.
-/

open Arxiv.«2607.05739»

namespace OMAAux

lemma gaussProd_succ (n : ℕ) :
    gaussProd (n + 1) = gaussProd n * (⟨1, ((n + 1 : ℕ) : ℤ)⟩ : GaussianInt) := by
  unfold gaussProd
  rw [Finset.prod_Icc_succ_top (by omega)]

lemma A_succ (n : ℕ) : A (n + 1) = A n - ((n : ℤ) + 1) * B n := by
  simp only [A, B, gaussProd_succ, Zsqrtd.re_mul]
  push_cast
  ring

lemma B_succ (n : ℕ) : B (n + 1) = B n + ((n : ℤ) + 1) * A n := by
  simp only [A, B, gaussProd_succ, Zsqrtd.im_mul]
  push_cast
  ring

/-- A polynomial invariant replaces the case distinction between the three
residue classes. The finite-field implication is checked by the kernel. -/
lemma step_mod_three : ∀ a b c : ZMod 3,
    (a ≠ 0 ∧ b = c * (2 - c) * a) →
      (a - (c + 1) * b ≠ 0 ∧
        b + (c + 1) * a = (c + 1) * (2 - (c + 1)) * (a - (c + 1) * b)) := by
  decide

lemma inv_mod_three (n : ℕ) :
    (A n : ZMod 3) ≠ 0 ∧
      (B n : ZMod 3) = (n : ZMod 3) * (2 - (n : ZMod 3)) * (A n : ZMod 3) := by
  induction n with
  | zero => norm_num [A, B, gaussProd]
  | succ n ih =>
    have h := step_mod_three _ _ _ ih
    rw [A_succ, B_succ]
    push_cast
    exact h

/-- The real part of the Gaussian product never vanishes. -/
lemma A_ne_zero (n : ℕ) : A n ≠ 0 := by
  intro h
  have h3 := (inv_mod_three n).1
  rw [h] at h3
  exact h3 Int.cast_zero

end OMAAux

theorem OMA.solution : type_of% @Arxiv.«2607.05739».x_succ := by
  intro n _
  have hA : (A n : ℚ) ≠ 0 := by exact_mod_cast OMAAux.A_ne_zero n
  unfold x
  rw [OMAAux.A_succ, OMAAux.B_succ]
  push_cast
  -- Rewrite over the common denominator A n before cancelling it.
  rw [← mul_div_assoc, one_sub_div hA, div_add' _ _ _ hA, div_div_div_cancel_right₀ hA]
