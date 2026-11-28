import Mathlib

/-!
# OEIS A127710: the inverse triangle is integral, with the ruler function as row sums

Source: https://oeis.org/A127710 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Paul Barry, Jan 24 2007), offset 0: Inverse of the triangle
A(n,k)=if(k<=n,if(n<=2k,1/(n+1),0),0).
Comment: It is conjectured that all elements of this triangle are integers. It appears that the
row sums are the ruler function A001511.

Formalization notes:
* The triangle is lower triangular with nonzero diagonal 1/(n+1), so its inverse is the lower
  triangular matrix whose (N+1) x (N+1) truncation is the inverse of the truncation of A, for
  every N. `tri N` is that truncation, with rows and columns indexed by `Fin (N + 1)`, and
  `(tri N)⁻¹` is Mathlib's matrix inverse; `main` quantifies over every N, so it covers every
  entry and every row of the inverse triangle.
* The triangle has offset 0 and A001511 has offset 1: row n is matched with A001511(n+1), which
  is what the entry's rows show (row sums 1, 2, 1, 3, 1, 2, 1, 4, ...).
* A001511(m) is the 2-adic valuation of 2m (its definition in the entry), `ruler m`.
* Control proved in the proof file: row 3 of the inverse is 0, 2, -3, 4, as in the entry.
-/

namespace OMA.S_oeis_a127710

open Matrix Finset

/-- The (N+1) x (N+1) truncation of the triangle A(n,k) = 1/(n+1) for k <= n <= 2k, else 0. -/
def tri (N : ℕ) : Matrix (Fin (N + 1)) (Fin (N + 1)) ℚ :=
  fun n k => if (k : ℕ) ≤ n ∧ (n : ℕ) ≤ 2 * k then 1 / ((n : ℚ) + 1) else 0

/-- The ruler function A001511(m): the 2-adic valuation of 2m. -/
def ruler (m : ℕ) : ℕ := padicValNat 2 (2 * m)

/-- Barry's conjectures: every entry of the inverse triangle is an integer, and row n of the
inverse triangle sums to A001511(n+1). -/
theorem main : ∀ N : ℕ, (∀ n k : Fin (N + 1), ∃ z : ℤ, (tri N)⁻¹ n k = z) ∧
    (∀ n : Fin (N + 1), ∑ k, (tri N)⁻¹ n k = ((ruler ((n : ℕ) + 1) : ℕ) : ℚ)) := by
  sorry

end OMA.S_oeis_a127710
