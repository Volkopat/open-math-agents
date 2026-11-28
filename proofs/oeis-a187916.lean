import OMAStatements.S_oeis_a187916
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A187916 (statement by @ivillar).
-- Idea: (k+2)*C(k+1) = (4k+2)*C(k); for each parity of n express the Catalan numbers occurring in
-- the recurrence through the two lowest ones, C(n-4) and C(floor(n/2)-2) (or C(floor(n/2)-1)),
-- after which the recurrence is an identity of rational functions.

namespace OMAA187916Helpers

open OMA.S_oeis_a187916

theorem cat_rec (j : ℕ) : ((j : ℚ) + 2) * catalan (j + 1) = (4 * j + 2) * catalan j := by
  have h1 := succ_mul_catalan_eq_centralBinom (j + 1)
  have h2 := succ_mul_catalan_eq_centralBinom j
  have h3 := Nat.succ_mul_centralBinom_succ j
  have h1' : ((j + 1 + 1 : ℕ) : ℚ) * catalan (j + 1) = (Nat.centralBinom (j + 1) : ℚ) := by exact_mod_cast h1
  have h2' : ((j + 1 : ℕ) : ℚ) * catalan j = (Nat.centralBinom j : ℚ) := by exact_mod_cast h2
  have h3' : ((j + 1 : ℕ) : ℚ) * Nat.centralBinom (j + 1) = 2 * (2 * j + 1) * Nat.centralBinom j := by
    exact_mod_cast h3
  push_cast at h1' h2' h3'
  have hj : (j : ℚ) + 1 ≠ 0 := by positivity
  apply mul_left_cancel₀ hj
  linear_combination ((j : ℚ) + 1) * h1' + h3' - 2 * (2 * (j : ℚ) + 1) * h2'

theorem cat_step (j : ℕ) : (catalan (j + 1) : ℚ) = (4 * j + 2) / ((j : ℚ) + 2) * catalan j := by
  have h := cat_rec j
  have hj : (j : ℚ) + 2 ≠ 0 := by positivity
  field_simp
  linarith

end OMAA187916Helpers

open OMA.S_oeis_a187916 OMAA187916Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a187916.main := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · -- n = 2m, m ≥ 3
    obtain ⟨p, rfl⟩ : ∃ p, m = p + 3 := ⟨m - 3, by omega⟩
    subst hm
    have e1 : p + 3 + (p + 3) - 1 = 2 * p + 5 := by omega
    have e2 : p + 3 + (p + 3) - 2 = 2 * p + 4 := by omega
    have e3 : p + 3 + (p + 3) - 3 = 2 * p + 3 := by omega
    have e4 : p + 3 + (p + 3) - 4 = 2 * p + 2 := by omega
    rw [e1, e2, e3, e4, show p + 3 + (p + 3) = 2 * p + 6 by ring]
    unfold a
    rw [if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega),
      show (2 * p + 6) / 2 = p + 3 by omega, show (2 * p + 4) / 2 = p + 2 by omega,
      show (2 * p + 2) / 2 = p + 1 by omega]
    have q : ∀ x : ℤ, ((x : ℚ) = 0) → x = 0 := fun x h => by exact_mod_cast h
    apply q
    push_cast
    rw [cat_step (2 * p + 5), cat_step (2 * p + 4), cat_step (2 * p + 3), cat_step (2 * p + 2),
      cat_step (p + 2), cat_step (p + 1)]
    push_cast
    field_simp
    ring
  · -- n = 2m + 1, m ≥ 2
    obtain ⟨p, rfl⟩ : ∃ p, m = p + 2 := ⟨m - 2, by omega⟩
    subst hm
    rw [show 2 * (p + 2) + 1 - 1 = 2 * p + 4 by omega, show 2 * (p + 2) + 1 - 2 = 2 * p + 3 by omega,
      show 2 * (p + 2) + 1 - 3 = 2 * p + 2 by omega, show 2 * (p + 2) + 1 - 4 = 2 * p + 1 by omega,
      show 2 * (p + 2) + 1 = 2 * p + 5 by ring]
    unfold a
    rw [if_pos (by omega), if_neg (by omega), if_pos (by omega), if_neg (by omega), if_pos (by omega),
      show (2 * p + 4) / 2 = p + 2 by omega, show (2 * p + 2) / 2 = p + 1 by omega]
    have q : ∀ x : ℤ, ((x : ℚ) = 0) → x = 0 := fun x h => by exact_mod_cast h
    apply q
    push_cast
    rw [cat_step (2 * p + 4), cat_step (2 * p + 3), cat_step (2 * p + 2), cat_step (2 * p + 1),
      cat_step (p + 1)]
    push_cast
    field_simp
    ring
