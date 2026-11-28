import OMAStatements.S_oeis_a242172
import Mathlib

-- Proof of R. J. Mathar's conjecture in OEIS A242172 (statement by @ivillar).
-- Idea: with g(j) = binomial(j + 1/2, 1/2), a(2j) = 4^j g(j) and a(2j+1) = 2*4^j g(j+1), and
-- Γ(s+1) = sΓ(s) gives g(j+1) = (j + 3/2)/(j + 1) * g(j); the recurrence is then an identity of
-- rational functions in j for each parity of n.

namespace OMAA242172Helpers

open OMA.S_oeis_a242172

noncomputable def g (j : ℕ) : ℝ := gbinom ((j : ℝ) + 1 / 2) (1 / 2)

theorem a_even (j : ℕ) : a (2 * j) = 4 ^ j * g j := by
  unfold a g
  rw [show (2 * j) % 2 = 0 by omega, pow_mul]
  norm_num
  congr 2
  ring

theorem a_odd (j : ℕ) : a (2 * j + 1) = 2 * 4 ^ j * g (j + 1) := by
  unfold a g
  rw [show (2 * j + 1) % 2 = 1 by omega, pow_succ, pow_mul]
  norm_num
  rw [show ((2 : ℝ) * j + 1 + 1 + 1) / 2 = (j : ℝ) + 1 + 1 / 2 by ring]
  ring

theorem g_succ (j : ℕ) : g (j + 1) = ((j : ℝ) + 3 / 2) / ((j : ℝ) + 1) * g j := by
  unfold g gbinom
  have h1 : ((j + 1 : ℕ) : ℝ) + 1 / 2 + 1 = ((j : ℝ) + 1 / 2 + 1) + 1 := by push_cast; ring
  have h2 : ((j + 1 : ℕ) : ℝ) + 1 / 2 - 1 / 2 + 1 = ((j : ℝ) + 1) + 1 := by push_cast; ring
  have h3 : (j : ℝ) + 1 / 2 - 1 / 2 + 1 = (j : ℝ) + 1 := by ring
  rw [h1, h2, h3, Real.Gamma_add_one (s := (j : ℝ) + 1 / 2 + 1) (by positivity),
    Real.Gamma_add_one (s := (j : ℝ) + 1) (by positivity)]
  have g1 : Real.Gamma ((j : ℝ) + 1 / 2 + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have g2 : Real.Gamma ((j : ℝ) + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have g3 : Real.Gamma ((1 : ℝ) / 2 + 1) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hj : (j : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

end OMAA242172Helpers

open OMA.S_oeis_a242172 OMAA242172Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a242172.main := by
  intro n hn
  rcases Nat.even_or_odd n with ⟨j, hj⟩ | ⟨j, hj⟩
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    subst hj
    rw [show i + 1 + (i + 1) = 2 * (i + 1) by ring, show 2 * (i + 1) - 1 = 2 * i + 1 by omega,
      show 2 * (i + 1) - 2 = 2 * i by omega, a_even, a_odd, a_even, g_succ]
    have hi : (i : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    subst hj
    rw [show 2 * (i + 1) + 1 - 1 = 2 * (i + 1) by omega, show 2 * (i + 1) + 1 - 2 = 2 * i + 1 by omega,
      a_odd, a_even, a_odd, g_succ (i + 1)]
    have hi : ((i + 1 : ℕ) : ℝ) + 1 ≠ 0 := by positivity
    push_cast at hi ⊢
    field_simp
    ring
