import OMAStatements.S_mse_2363374
import Mathlib

-- Problem: mse-2363374, does a_n (a_1 = a, a_2 = b, a_n = a_{n-1} + a_{n-2}^2) always have
-- exactly F_n terms?
-- Credit: @ivillar (the owner of the agent is credited as the solver)
--
-- No: the conjecture fails first at n = 7. Expanding,
--   a_7 = b + 4b^2 + 6b^3 + 5b^4 + a^2 + 6a^2b + 10a^2b^2 + 8a^2b^3 + 3a^4 + 6a^4b + 8a^4b^2
--         + 2a^6 + 4a^6b + a^8,
-- which has 14 terms, while F_7 = 13. To count terms inside Lean we substitute a = X, b = X^9
-- (a monomial substitution cannot increase the number of terms, and here it separates all 14
-- monomials) and read off 14 nonzero coefficients of the resulting one-variable polynomial.

namespace MSE2363374

open Polynomial

noncomputable def w : Fin 2 → ℤ[X] := ![X, X ^ 9]

theorem card_le (p : MvPolynomial (Fin 2) ℤ) :
    (p.eval₂ (C : ℤ →+* ℤ[X]) w).support.card ≤ p.support.card := by
  rw [MvPolynomial.eval₂_eq']
  have key : ∀ d : Fin 2 →₀ ℕ, ∏ i, w i ^ d i = X ^ (d 0 + 9 * d 1) := by
    intro d
    simp [w, Fin.prod_univ_two, ← pow_mul, ← pow_add]
  have hsub : (∑ d ∈ p.support, C (p.coeff d) * ∏ i, w i ^ d i).support ⊆
      p.support.image (fun d => d 0 + 9 * d 1) := by
    intro k hk
    rw [Polynomial.mem_support_iff, Polynomial.finset_sum_coeff] at hk
    obtain ⟨d, hd, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hk
    rw [key, Polynomial.coeff_C_mul_X_pow] at hne
    rw [Finset.mem_image]
    refine ⟨d, hd, ?_⟩
    by_contra h
    exact hne (if_neg (fun h' => h h'.symm))
  exact (Finset.card_le_card hsub).trans Finset.card_image_le

noncomputable def Q : ℤ[X] :=
  X ^ 2 + 3 * X ^ 4 + 2 * X ^ 6 + X ^ 8 + X ^ 9 + 6 * X ^ 11 + 6 * X ^ 13 + 4 * X ^ 15 +
    4 * X ^ 18 + 10 * X ^ 20 + 8 * X ^ 22 + 6 * X ^ 27 + 8 * X ^ 29 + 5 * X ^ 36

theorem seq7 : (OMA.S_mse_2363374.seq 7).eval₂ (C : ℤ →+* ℤ[X]) w = Q := by
  have h3 : OMA.S_mse_2363374.seq 3 =
      OMA.S_mse_2363374.seq 2 + OMA.S_mse_2363374.seq 1 ^ 2 := rfl
  have h4 : OMA.S_mse_2363374.seq 4 =
      OMA.S_mse_2363374.seq 3 + OMA.S_mse_2363374.seq 2 ^ 2 := rfl
  have h5 : OMA.S_mse_2363374.seq 5 =
      OMA.S_mse_2363374.seq 4 + OMA.S_mse_2363374.seq 3 ^ 2 := rfl
  have h6 : OMA.S_mse_2363374.seq 6 =
      OMA.S_mse_2363374.seq 5 + OMA.S_mse_2363374.seq 4 ^ 2 := rfl
  have h7 : OMA.S_mse_2363374.seq 7 =
      OMA.S_mse_2363374.seq 6 + OMA.S_mse_2363374.seq 5 ^ 2 := rfl
  have s1 : (OMA.S_mse_2363374.seq 1).eval₂ (C : ℤ →+* ℤ[X]) w = X := by
    show (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℤ).eval₂ (C : ℤ →+* ℤ[X]) w = X
    rw [MvPolynomial.eval₂_X]
    rfl
  have s2 : (OMA.S_mse_2363374.seq 2).eval₂ (C : ℤ →+* ℤ[X]) w = X ^ 9 := by
    show (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℤ).eval₂ (C : ℤ →+* ℤ[X]) w = X ^ 9
    rw [MvPolynomial.eval₂_X]
    rfl
  rw [h7, h6, h5, h4, h3]
  simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_pow, s1, s2]
  unfold Q
  ring

theorem card_Q : 14 ≤ Q.support.card := by
  have hsub : ({2, 4, 6, 8, 9, 11, 13, 15, 18, 20, 22, 27, 29, 36} : Finset ℕ) ⊆ Q.support := by
    intro k hk
    rw [Polynomial.mem_support_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Q, Polynomial.coeff_X_pow]
  have hc := Finset.card_le_card hsub
  have h14 : ({2, 4, 6, 8, 9, 11, 13, 15, 18, 20, 22, 27, 29, 36} : Finset ℕ).card = 14 := by
    decide
  omega

end MSE2363374

theorem OMA.disproof : ¬ (type_of% @OMA.S_mse_2363374.main) := by
  intro h
  have h7 := h 7 (by norm_num)
  have hfib : Nat.fib 7 = 13 := by decide
  have hle := MSE2363374.card_le (OMA.S_mse_2363374.seq 7)
  rw [h7, hfib, MSE2363374.seq7] at hle
  have := MSE2363374.card_Q
  omega
