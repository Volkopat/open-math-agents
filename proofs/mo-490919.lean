import OMAStatements.S_mo_490919
import Mathlib

/-!
MathOverflow 490919, inequality (2). For a probability distribution `μ` on a finite abelian group
`G`, with `S = ‖μ̂‖₁`: `|μ̂ ψ| ≤ 1 = μ̂ 0` gives `H(Y) ≥ log S`, and Fourier inversion gives
`|G| μ(x) ≤ S`, hence `H(X) ≥ log |G| - log S`. Adding the two bounds proves (2).
-/

open Finset Real OMA.S_mo_490919

namespace OMA.P490919

variable {G : Type*} [AddCommGroup G] [Fintype G]

/-- `‖μ̂‖₁`. -/
noncomputable def l1 (μ : G → ℝ) : ℝ := ∑ ψ : AddChar G ℂ, ‖fourierHat μ ψ‖

lemma norm_fourierHat_le (μ : G → ℝ) (h0 : ∀ x, 0 ≤ μ x) (h1 : ∑ x, μ x = 1) (ψ : AddChar G ℂ) :
    ‖fourierHat μ ψ‖ ≤ 1 := by
  unfold fourierHat
  calc ‖∑ x, (μ x : ℂ) * ψ x‖ ≤ ∑ x, ‖(μ x : ℂ) * ψ x‖ := norm_sum_le _ _
    _ = ∑ x, μ x := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [norm_mul, AddChar.norm_apply, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (h0 x)]
    _ = 1 := h1

lemma fourierHat_zero (μ : G → ℝ) (h1 : ∑ x, μ x = 1) : fourierHat μ 0 = 1 := by
  unfold fourierHat
  simp only [AddChar.zero_apply, mul_one]
  exact_mod_cast h1

lemma one_le_l1 (μ : G → ℝ) (h1 : ∑ x, μ x = 1) : 1 ≤ l1 μ := by
  unfold l1
  have := Finset.single_le_sum (f := fun ψ : AddChar G ℂ => ‖fourierHat μ ψ‖)
    (fun ψ _ => norm_nonneg _) (Finset.mem_univ (0 : AddChar G ℂ))
  simpa [fourierHat_zero μ h1] using this

/-- Fourier inversion: `n μ x = ∑ ψ, μ̂ ψ * ψ (-x)`. -/
lemma inversion [DecidableEq G] (μ : G → ℝ) (x : G) :
    ((Fintype.card G : ℂ) * μ x) = ∑ ψ : AddChar G ℂ, fourierHat μ ψ * ψ (-x) := by
  unfold fourierHat
  simp_rw [Finset.sum_mul, mul_assoc, ← AddChar.map_add_eq_mul]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, AddChar.sum_apply_eq_ite]
  rw [Finset.sum_eq_single x]
  · simp [mul_comm]
  · intro y _ hy
    have : y + -x ≠ 0 := by
      intro h; apply hy; exact (add_neg_eq_zero.mp h)
    simp [this]
  · simp

lemma card_mul_le_l1 (μ : G → ℝ) (h0 : ∀ x, 0 ≤ μ x) (x : G) :
    (Fintype.card G : ℝ) * μ x ≤ l1 μ := by
  classical
  have h := congrArg (fun z : ℂ => ‖z‖) (inversion μ x)
  have hl : ‖(Fintype.card G : ℂ) * (μ x : ℂ)‖ = (Fintype.card G : ℝ) * μ x := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 x)]
    simp
  rw [← hl, h]
  unfold l1
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [norm_mul, AddChar.norm_apply, mul_one]

/-- `H(X) ≥ log n - log S`. -/
lemma entropy_mu_ge (μ : G → ℝ) (h0 : ∀ x, 0 ≤ μ x) (h1 : ∑ x, μ x = 1) :
    Real.log (Fintype.card G) - Real.log (l1 μ) ≤ entropy μ := by
  have hS : 0 < l1 μ := lt_of_lt_of_le one_pos (one_le_l1 μ h1)
  have hn : (0 : ℝ) < Fintype.card G := by
    have : Nonempty G := ⟨0⟩
    exact_mod_cast Fintype.card_pos
  unfold entropy
  calc Real.log (Fintype.card G) - Real.log (l1 μ)
      = ∑ x, μ x * (Real.log (Fintype.card G) - Real.log (l1 μ)) := by
        rw [← Finset.sum_mul, h1, one_mul]
    _ ≤ ∑ x, Real.negMulLog (μ x) := by
        refine Finset.sum_le_sum fun x _ => ?_
        rcases (h0 x).eq_or_lt with hx | hx
        · rw [← hx]; simp
        · rw [Real.negMulLog, neg_mul, ← mul_neg]
          refine mul_le_mul_of_nonneg_left ?_ hx.le
          have hle : (Fintype.card G : ℝ) * μ x ≤ l1 μ := card_mul_le_l1 μ h0 x
          have := Real.log_le_log (mul_pos hn hx) hle
          rw [Real.log_mul hn.ne' hx.ne'] at this
          linarith

/-- `H(Y) ≥ log S`. -/
lemma entropy_hat_ge (μ : G → ℝ) (h0 : ∀ x, 0 ≤ μ x) (h1 : ∑ x, μ x = 1) :
    Real.log (l1 μ) ≤ entropy (fun ψ : AddChar G ℂ => ‖fourierHat μ ψ‖ / l1 μ) := by
  have hS : 0 < l1 μ := lt_of_lt_of_le one_pos (one_le_l1 μ h1)
  unfold entropy
  calc Real.log (l1 μ) = ∑ ψ : AddChar G ℂ, (‖fourierHat μ ψ‖ / l1 μ) * Real.log (l1 μ) := by
        rw [← Finset.sum_mul, ← Finset.sum_div]
        change Real.log (l1 μ) = (l1 μ / l1 μ) * Real.log (l1 μ)
        rw [div_self hS.ne', one_mul]
    _ ≤ ∑ ψ : AddChar G ℂ, Real.negMulLog (‖fourierHat μ ψ‖ / l1 μ) := by
        refine Finset.sum_le_sum fun ψ _ => ?_
        have ha := norm_fourierHat_le μ h0 h1 ψ
        rcases (norm_nonneg (fourierHat μ ψ)).eq_or_lt with h | h
        · rw [← h]; simp
        · have hq : 0 < ‖fourierHat μ ψ‖ / l1 μ := div_pos h hS
          rw [Real.negMulLog, neg_mul, ← mul_neg]
          refine mul_le_mul_of_nonneg_left ?_ hq.le
          rw [Real.log_div h.ne' hS.ne']
          have : Real.log ‖fourierHat μ ψ‖ ≤ 0 := Real.log_nonpos (norm_nonneg _) ha
          linarith

theorem ineq2 (μ : G → ℝ) (h0 : ∀ x, 0 ≤ μ x) (h1 : ∑ x, μ x = 1) :
    Real.log (Fintype.card G) ≤
      entropy μ +
        entropy (fun ψ : AddChar G ℂ =>
          ‖fourierHat μ ψ‖ / ∑ χ : AddChar G ℂ, ‖fourierHat μ χ‖) := by
  have a := entropy_mu_ge μ h0 h1
  have b := entropy_hat_ge μ h0 h1
  unfold l1 at a b
  linarith

end OMA.P490919

theorem OMA.solution : type_of% @OMA.S_mo_490919.main := by
  intro G _ _ μ h0 h1
  exact OMA.P490919.ineq2 μ h0 h1
