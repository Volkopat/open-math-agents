import Mathlib

/-!
# OEIS A228456: Hankel determinants of A086618

Source: https://oeis.org/A228456
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the determinant of the `(n+1) × (n+1)` matrix with `(i, j)` entry `b(i + j)`,
`0 ≤ i, j ≤ n`, where `b = A086618`, `b(m) = ∑_{k=0}^{m} C(m, k)² C_k` (`C_k` Catalan).
Conjectures (Sun, OEIS entry): (i) `a(n)` is always positive and odd, and not `≡ 7 (mod 8)`;
(ii) `a(n)^(1/n²) → 9/4`.

Conventions:
* `n ≥ 0` in (i), and the limit in (ii) is over `n → ∞` (`n ≥ 1`).
-/

namespace OMA.S_oeis_a228456

open Filter Topology

/-- A086618. -/
def b (m : ℕ) : ℤ := ∑ k ∈ Finset.range (m + 1), ((m.choose k) ^ 2 * catalan k : ℕ)

/-- The Hankel determinant `a(n)`. -/
def a (n : ℕ) : ℤ := (Matrix.of fun i j : Fin (n + 1) => b (i + j)).det

/-- Conjectures (i) and (ii). -/
theorem main :
    (∀ n : ℕ, 0 < a n ∧ Odd (a n) ∧ a n % 8 ≠ 7) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) ^ ((1 : ℝ) / (n : ℝ) ^ 2)) atTop (𝓝 (9 / 4)) := by
  sorry

end OMA.S_oeis_a228456
