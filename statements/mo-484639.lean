import Mathlib

/-!
# Conjectured closed form of a summation over an integer lattice

Source: https://mathoverflow.net/questions/484639
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

For a full-rank integer lattice `Λ = {∑ aⱼ vⱼ | aⱼ ∈ ℤ} ⊆ ℤⁿ` with `d(Λ) = |det V|`, conjecture
(asker): there is `P ∈ ℤ[x]` with
`S(Λ) = ∑_{k ∈ Λ} ∏_{j=1}^{n} 1/(1 + kⱼ²) = π^n / (sinh^n(π) d(Λ)) · P(cosh(π / d(Λ)))`.

Conventions:
* `V` is an `n × n` integer matrix with `det V ≠ 0` (columns `vⱼ`), `n ≥ 1`. The lattice points
  are `V a` for `a ∈ ℤⁿ`, each listed once since `V` is injective; the series converges
  absolutely and is a `tsum` over `a`.
-/

namespace OMA.S_mo_484639

open Polynomial

/-- `S(Λ)` for the lattice spanned by the columns of `V`. -/
noncomputable def S {n : ℕ} (V : Matrix (Fin n) (Fin n) ℤ) : ℝ :=
  ∑' a : Fin n → ℤ, ∏ j, 1 / (1 + ((V.mulVec a j : ℤ) : ℝ) ^ 2)

/-- The conjectured closed form. -/
theorem main : ∀ (n : ℕ) (V : Matrix (Fin n) (Fin n) ℤ), 1 ≤ n → V.det ≠ 0 →
    ∃ P : ℤ[X], S V = Real.pi ^ n / (Real.sinh Real.pi ^ n * |(V.det : ℝ)|) *
      (P.map (Int.castRingHom ℝ)).eval (Real.cosh (Real.pi / |(V.det : ℝ)|)) := by
  sorry

end OMA.S_mo_484639
