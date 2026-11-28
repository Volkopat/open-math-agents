import Mathlib

/-!
# OEIS A000522: Total number of arrangements of subsets of an n-element set

Source: https://oeis.org/A000522
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

`a(n) = ∑_{k=0}^n n! / k!`.

Conjecture: The ordinary generating function of `a(n)` is `T(0) / (1 - 2x)`, where
`T(k) = 1 - x^2 (k+1)^2 / (x^2 (k+1)^2 - (1 - 2x(k+1))(1 - 2x(k+2)) / T(k+1))`
as a formal continued fraction in `ℚ[[x]]`.
-/

namespace OMA.S_oeis_a000522

def a (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), n.factorial / k.factorial

noncomputable def cfT (k : ℕ) : ℕ → PowerSeries ℚ
  | 0 => 1
  | m + 1 =>
    let x := (PowerSeries.X : PowerSeries ℚ)
    let c1 := PowerSeries.C (((k + 1 : ℕ) : ℚ) ^ 2) * x ^ 2
    let lin1 := 1 - PowerSeries.C (2 * ((k + 1 : ℕ) : ℚ)) * x
    let lin2 := 1 - PowerSeries.C (2 * ((k + 2 : ℕ) : ℚ)) * x
    1 - c1 * Ring.inverse (c1 - lin1 * lin2 * Ring.inverse (cfT (k + 1) m))

theorem main :
    ∀ n : ℕ, ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      PowerSeries.coeff n
        (cfT 0 m * Ring.inverse (1 - PowerSeries.C 2 * PowerSeries.X)) = (a n : ℚ) := by
  sorry

end OMA.S_oeis_a000522
