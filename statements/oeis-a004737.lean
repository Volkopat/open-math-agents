import Mathlib

/-!
# A004737: Concatenation of sequences (1,2,...,n-1,n,n-1,...,1) for n >= 1.

Source: https://oeis.org/A004737
Credit: @tczyzycki

Formalizes L. Edson Jeffery's conjecture (Jan 13, 2012) on the matrix `M_N = (1/q) * E_N^T * E_N`,
where `N = 2 * q`, `x_k = cos((2 * k - 1) * pi / N)` for `k = 1, ..., q`, and the `k`-th column
of `E_N` evaluates the Chebyshev polynomial of the second kind `U_k` (in 1-based indexing:
`U_1(t) = 1`, `U_2(t) = 2 * t`, `U_r(t) = 2 * t * U_{r-1}(t) - U_{r-2}(t)`, which equals Mathlib's
0-based `Polynomial.Chebyshev.U ℝ (k - 1)`) at `x_1, ..., x_q`.

Conventions and reading of the source:
- The source comment writes "E_N and M_N are always integral and symmetric, with M_N having
  diagonal entries {1, 2, ...} beginning at entries (1, j) (j odd) in the first row and (i, 1)
  (i odd) in the first column and with zeros elsewhere." Literally claiming `E_N` itself is
  integral and symmetric is a slip in the source (already for `q = 2`, `N = 4`, `E_4` has
  entries `1, sqrt 2; 1, -sqrt 2`). Following the standard reading and the explicit example `M_18`
  in the source, `main` states the exact entrywise formula for `M_N`: in 0-based `Fin q` indexing,
  `M q i j = min i j + 1` when `i + j` is even, and `0` when `i + j` is odd.
- This single entrywise formula implies integrality, symmetry, the diagonal structure, and that
  the antidiagonals `i + j = 2 * v` reproduce the rows of A004737.
- Including `q = 1` matches the source's trivial case `M_2 = [1]` (since `x_1 = cos(pi / 2) = 0`
  and `U_1(0) = 1` gives `M 1 0 0 = 1`).
-/

namespace OMA.S_oeis_a004737

/-- Chebyshev nodes `x_r = cos((2 * r + 1) * pi / (2 * q))` (0-based `r : Fin q`). -/
noncomputable def x (q : ℕ) (r : Fin q) : ℝ :=
  Real.cos ((2 * (r.val : ℝ) + 1) * Real.pi / (2 * (q : ℝ)))

/-- The `q × q` matrix `E_{2q}` whose `(r, k)` entry is `U_k(x_r)` (0-based Mathlib Chebyshev
polynomial of the second kind, corresponding to Jeffery's 1-based `U_{k+1}`). -/
noncomputable def E (q : ℕ) : Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun r k => (Polynomial.Chebyshev.U ℝ k.val).eval (x q r)

/-- The scaled Gram matrix `M_{2q} = (1 / q) * E_{2q}^T * E_{2q}`. -/
noncomputable def M (q : ℕ) : Matrix (Fin q) (Fin q) ℝ :=
  ((q : ℝ)⁻¹) • ((E q).transpose * E q)

theorem main :
    ∀ q : ℕ, 1 ≤ q → ∀ i j : Fin q,
      M q i j = if Even (i.val + j.val) then ((min i.val j.val + 1 : ℕ) : ℝ) else 0 := by
  sorry

end OMA.S_oeis_a004737
