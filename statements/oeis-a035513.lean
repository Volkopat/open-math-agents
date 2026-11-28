import Mathlib

/-!
# A035513: Wythoff array read by falling antidiagonals.

Source: https://oeis.org/A035513 (Clark Kimberling, comment of Jun 04 2025, last line)
Credit: @Aijy0264561

Conjecture: if `m ≥ 2`, then `{(T(n,1), T(n,2)) mod m}` has cardinality `m^2`.

Conventions:
* `T n k` is the Wythoff array entry in row `n ≥ 1`, column `k`, by the entry's formula
  `T(n,k) = Fib(k+1) * floor(n*tau) + Fib(k) * (n-1)` with `tau = (1 + sqrt 5)/2`
  (Bottomley; Kimberling 1994, p. 314), `Fib` = `Nat.fib`. So `T n 1 = floor(n*tau) + n - 1` and
  `T n 2 = 2 floor(n*tau) + n - 1`; rows 1, 2, 3, 4 start `(1, 2)`, `(4, 7)`, `(6, 10)`, `(9, 15)`,
  matching the antidiagonals `1; 2, 4; 3, 7, 6; …` of the data and the classes in Kimberling's
  comment (`(T(n,1), T(n,2)) mod 2` is `(0,0)` for `n = 3, 5, 9, …`, `(0,1)` for `n = 2, 6, 12, …`,
  `(1,0)` for `n = 1, 7, 11, …`, `(1,1)` for `n = 4, 8, 10, …`; mod 3 it is `(0,0)` at `n = 4, 13`).
* `{(T(n,1), T(n,2)) mod m}` is the set of pairs of residues `(T n 1 % m, T n 2 % m)` over all rows
  `n ≥ 1`; the conjecture says it has `m^2` elements, i.e. every pair of residues occurs.
-/

namespace OMA.S_oeis_a035513

/-- The Wythoff array `T(n, k)` (rows `n ≥ 1`). -/
noncomputable def T (n k : ℕ) : ℕ :=
  Nat.fib (k + 1) * ⌊(n : ℝ) * Real.goldenRatio⌋₊ + Nat.fib k * (n - 1)

theorem main : ∀ m : ℕ, 2 ≤ m →
    {p : ℕ × ℕ | ∃ n : ℕ, 1 ≤ n ∧ p = (T n 1 % m, T n 2 % m)}.ncard = m ^ 2 := by
  sorry

end OMA.S_oeis_a035513
