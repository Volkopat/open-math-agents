import Mathlib

/-!
# A103910: Triangle T read by rows: inverse of fibonomial triangle (A010048).

Source: https://oeis.org/A103910
Credit: @luciusacarr

The entry records two claims labelled as conjectures:
* (comment) all rows except the first add to zero;
* (formula) `T(n+k, n) = A010048(n+k-1, k)*T(k, 1)`, `n > 1`.

Reading of the source:
* A010048 is the triangle of Fibonomial coefficients (offset 0):
  `A010048(n, k) = F(n)*F(n-1)*...*F(n-k+1) / (F(k)*F(k-1)*...*F(1))` for `0 ≤ k ≤ n`, with `F` the
  Fibonacci numbers (`Nat.fib`); we take it as a rational number (it is an integer). It is lower
  triangular with unit diagonal.
* A103910 has offset 1: row `n ≥ 1` has the `n` entries `T(n, 1), ..., T(n, n)` (data
  `1; -1, 1; 0, -1, 1; 1, 0, -2, 1; ...`). `T` is the matrix inverse of the Fibonomial
  triangle: `T(n, k)` is the entry in row `n - 1`, column `k - 1` (0-based) of the inverse of the
  `n × n` matrix `(A010048(i, j))_{0 ≤ i, j < n}`. (For lower triangular matrices the leading
  `n × n` block of the inverse is the inverse of the leading block, so this does not depend on
  the truncation size.) Outside `1 ≤ k ≤ n` we set `T(n, k) = 0`; the claims below only use
  entries inside the triangle.
* Claim 1: for every row `n ≥ 2`, `Sum_{k=1..n} T(n, k) = 0`.
* Claim 2: for every `n > 1` and every `k ≥ 1` (so that `T(k, 1)` is an entry of the triangle),
  `T(n+k, n) = A010048(n+k-1, k) * T(k, 1)`.
* The statement is the conjunction of the two claims.
-/

namespace OMA.S_oeis_a103910

/-- A010048: the Fibonomial coefficient `F(n)...F(n-k+1)/(F(k)...F(1))`, and `0` for `k > n`. -/
noncomputable def fibonomial (n k : ℕ) : ℚ :=
  if k ≤ n then
    (∏ i ∈ Finset.range k, (Nat.fib (n - i) : ℚ)) / ∏ i ∈ Finset.range k, (Nat.fib (i + 1) : ℚ)
  else 0

/-- The leading `n × n` block of the Fibonomial triangle (0-based indices). -/
noncomputable def fibMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  fun i j => fibonomial i.val j.val

/-- A103910 (offset 1): `T(n, k)` for `1 ≤ k ≤ n` is entry `(n-1, k-1)` of the inverse of the
leading `n × n` block of the Fibonomial triangle. -/
noncomputable def T (n k : ℕ) : ℚ :=
  if h : 1 ≤ k ∧ k ≤ n then
    (fibMatrix n)⁻¹ ⟨n - 1, by omega⟩ ⟨k - 1, by omega⟩
  else 0

theorem main :
    (∀ n : ℕ, 2 ≤ n → ∑ k ∈ Finset.Icc 1 n, T n k = 0) ∧
    (∀ n k : ℕ, 1 < n → 1 ≤ k → T (n + k) n = fibonomial (n + k - 1) k * T k 1) := by
  sorry

end OMA.S_oeis_a103910
