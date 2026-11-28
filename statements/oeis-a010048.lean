import Mathlib

/-!
# A010048: Triangle of Fibonomial coefficients, read by rows

Source: https://oeis.org/A010048
Credit: @sntntHb

Conjecture (in the comments of A010048): polynomials with (positive) Fibonomial coefficients
are reducible iff n odd > 1.

Conventions:
* The Fibonomial coefficient is `C_F(n, k) = (F(n) F(n-1) ... F(n-k+1)) / (F(1) F(2) ... F(k))`,
  with `F = Nat.fib` (`F 0 = 0`, `F 1 = 1`). The quotient is exact; it is written with natural
  number division.
* The polynomial of row `n` is `P_n(x) = Sum_{k=0..n} C_F(n, k) x^k`, taken in `ℚ[X]` (it has
  leading coefficient `1`, so reducibility over `ℚ` and over `ℤ` agree).
* The statement is for `n ≥ 1` (for `n = 0` the polynomial is the constant `1`, which is neither
  irreducible nor reducible). For `n = 1` the polynomial `1 + x` is irreducible, as the
  conjecture says (`1` is odd but not `> 1`).
* For odd `n > 1` reducibility is easy (`x = -1` is a root by the symmetry
  `C_F(n, k) = C_F(n, n - k)`); the open part is irreducibility for even `n`.
-/

namespace OMA.S_oeis_a010048

open Polynomial

/-- The Fibonomial coefficient `C_F(n, k)`. -/
def fibonomial (n k : ℕ) : ℕ :=
  (∏ i ∈ Finset.range k, Nat.fib (n - i)) / ∏ i ∈ Finset.range k, Nat.fib (i + 1)

/-- The polynomial `Sum_{k=0..n} C_F(n, k) x^k` of row `n` of the triangle. -/
noncomputable def fibPoly (n : ℕ) : ℚ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((fibonomial n k : ℕ) : ℚ) * X ^ k

/-- For `n ≥ 1`, the row-`n` Fibonomial polynomial is reducible exactly when `n` is odd and
`n > 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (¬ Irreducible (fibPoly n) ↔ (Odd n ∧ 1 < n)) := by
  sorry

end OMA.S_oeis_a010048
