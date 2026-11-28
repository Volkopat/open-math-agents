import FormalConjectures.Wikipedia.RiemannZetaValues

-- Reduction RiemannZetaValues.irrational_odd.R1 of Particular values of the Riemann zeta function — irrational odd
-- Credit: @sntntHb
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Sketch: the target asks that zeta(2n+1) be irrational for every n >= 1. Different values of n
-- are independent statements (none implies another), so we split by n:
--   H1: n = 1, zeta(3) is irrational. This is Apery's theorem (1979), a solved companion in the
--       same upstream file (RiemannZetaValues.irrational_three).
--   H2: n = 2, zeta(5) is irrational (open; the companion irrational_five).
--   H3: every n >= 3 (open; Zudilin and Rivoal only give partial results here).
-- main is a case split n = 1 / n = 2 / n >= 3 with a numeral normalisation of 2n+1.

namespace OMA.R_RiemannZetaValues_irrational_odd_R1

/-- The case `n = 1`: `ζ(3)` is irrational (Apéry 1979). -/
def H1 : Prop := ∃ x, Irrational x ∧ riemannZeta 3 = x

/-- The case `n = 2`: `ζ(5)` is irrational. -/
def H2 : Prop := ∃ x, Irrational x ∧ riemannZeta 5 = x

/-- The remaining cases `n ≥ 3`: `ζ(2n+1)` is irrational. -/
def H3 : Prop := ∀ n : ℕ, 3 ≤ n → ∃ x, Irrational x ∧ riemannZeta (2 * n + 1) = x

theorem main : H1 → H2 → H3 → type_of% @RiemannZetaValues.irrational_odd := by
  intro h1 h2 h3 n hn
  rcases (by omega : n = 1 ∨ n = 2 ∨ 3 ≤ n) with rfl | rfl | h
  · obtain ⟨x, hx, hz⟩ := h1
    refine ⟨x, hx, ?_⟩
    rw [← hz]
    norm_num
  · obtain ⟨x, hx, hz⟩ := h2
    refine ⟨x, hx, ?_⟩
    rw [← hz]
    norm_num
  · exact h3 n h

end OMA.R_RiemannZetaValues_irrational_odd_R1
