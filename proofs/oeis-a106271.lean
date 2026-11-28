import OMAStatements.S_oeis_a106271
import Mathlib

namespace OMA.S_oeis_a106271

open PowerSeries

lemma cat_rec (m : ℕ) : ((m : ℚ) + 2) * (catalan (m + 1) : ℚ) = 2 * (2 * (m : ℚ) + 1) * (catalan m : ℚ) := by
  have h1 := Nat.succ_mul_centralBinom_succ m
  have h2 := succ_mul_catalan_eq_centralBinom (m + 1)
  have h3 := succ_mul_catalan_eq_centralBinom m
  have h4 : (m + 1) * ((m + 1 + 1) * catalan (m + 1)) = (m + 1) * (2 * (2 * m + 1) * catalan m) := by
    rw [h2, h1, ← h3]; ring
  have h5 : (m + 1 + 1) * catalan (m + 1) = 2 * (2 * m + 1) * catalan m :=
    Nat.eq_of_mul_eq_mul_left (Nat.succ_pos m) h4
  exact_mod_cast h5

end OMA.S_oeis_a106271

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a106271.main := by
  intro S c G hS hS0 hc hG n hn
  have hSc : S = 1 - 2 * X * c := by rw [hc]; ring
  have hcc : X * (X * c ^ 2 - c + 1) = 0 := by
    have : (4 : ℚ⟦X⟧) * (X * (X * c ^ 2 - c + 1)) = 0 := by
      have e : S ^ 2 = 1 - 4 * X := hS
      rw [hSc] at e
      linear_combination e
    have h4 : (4 : ℚ⟦X⟧) ≠ 0 := by
      have e4 : (4 : ℚ⟦X⟧) = C (4 : ℚ) := (map_ofNat C 4).symm
      rw [e4]; simp
    exact (mul_eq_zero.mp this).resolve_left h4
  have hc2 : X * c ^ 2 - c + 1 = 0 :=
    (mul_eq_zero.mp hcc).resolve_left PowerSeries.X_ne_zero
  have hcoef : ∀ k, PowerSeries.coeff k c = (catalan k : ℚ) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      cases k with
      | zero =>
        have := congrArg (coeff 0) hc2
        simp at this
        simp [catalan_zero]
        linarith
      | succ k =>
        have e : c = X * c ^ 2 + 1 := by linear_combination -hc2
        have := congrArg (coeff (k + 1)) e
        simp only [map_add, coeff_one, coeff_succ_X_mul] at this
        rw [this, catalan_succ']
        simp only [sq, coeff_mul]
        push_cast
        simp only [add_zero]
        refine Finset.sum_congr rfl ?_
        intro p hp
        have hp' := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
        rw [ih p.1 (by omega), ih p.2 (by omega)]
  have hGe : G * (1 - X) = 2 - c := by
    rw [hG, hSc]; linear_combination (-2 : ℚ⟦X⟧) * hc2
  have hg : ∀ m, coeff (m + 1) G = coeff m G - (catalan (m + 1) : ℚ) := by
    intro m
    have := congrArg (coeff (m + 1)) hGe
    rw [mul_sub, mul_one, map_sub, coeff_succ_mul_X] at this
    have e2 : coeff (m + 1) (2 - c) = - (catalan (m + 1) : ℚ) := by
      rw [map_sub, hcoef]
      have : coeff (m + 1) (2 : ℚ⟦X⟧) = 0 := by
        have : (2 : ℚ⟦X⟧) = C (2 : ℚ) := (map_ofNat C 2).symm
        rw [this, coeff_C]; simp
      rw [this]; ring
    rw [e2] at this
    linarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have e1 : m + 2 - 1 = m + 1 := by omega
  have e2 : m + 2 - 2 = m := by omega
  rw [e1, e2, hg (m + 1), hg m]
  have := OMA.S_oeis_a106271.cat_rec m
  have h' := OMA.S_oeis_a106271.cat_rec (m + 1)
  push_cast at *
  have : (((m : ℚ) + 1 + 2) * (catalan (m + 1 + 1) : ℚ)) = 2 * (2 * ((m : ℚ) + 1) + 1) * (catalan (m + 1) : ℚ) := by
    exact_mod_cast h'
  nlinarith [this]

