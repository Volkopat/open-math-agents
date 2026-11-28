import Mathlib

/-!
# A204558: Row sums of the triangle A045975

Source: https://oeis.org/A204558 and https://oeis.org/A045975 (OEIS Foundation, CC BY-SA 4.0).
Credit: @mbilenko03

A045975: take the first odd integer and multiple of 1, the next 2 even integers and multiples of 2,
the next 3 odd integers and multiples of 3, the next 4 even integers and multiples of 4, ...
Row `n` (for `n ≥ 1`) of the triangle is those `n` numbers: the `n` smallest integers greater than
the last entry of row `n - 1` (`0` before the first row) that are multiples of `n` and have the
parity of `n`. Rows: `1 | 2, 4 | 9, 15, 21 | 24, 28, 32, 36 | ...`.

A204558 (offset 1) is the sequence of row sums: `1, 6, 45, 120, 325, 630, ...`.

Conjectures (Colin Barker, Apr 02 2013), both stated:
1. `a(n) = (n^2*(-(-1)^n+n^2))/2` for `n ≥ 1`.
2. G.f.: `-x*(x^6 +4*x^5 +31*x^4 +24*x^3 +31*x^2 +4*x +1) / ((x -1)^5*(x +1)^3)`, stated over `ℤ`
   with the denominator cleared; the series is `∑_{n ≥ 1} a(n) x^n` (here `a 0 = 0`, the empty row,
   so the series is `∑_{n ≥ 0} a(n) x^n`).
-/

namespace OMA.S_oeis_a204558

/-- `x` may be an entry of row `m` when the previous row ended at `L`: `L < x`, `m ∣ x`, and `x`
has the parity of `m`. -/
def P (m L x : ℕ) : Prop := L < x ∧ m ∣ x ∧ x % 2 = m % 2

/-- The last entry of row `m` (`last 0 = 0`): the `m`-th smallest admissible number. -/
noncomputable def last : ℕ → ℕ
  | 0 => 0
  | m + 1 => Nat.nth (P (m + 1) (last m)) m

/-- Entry `T(n, k)` of A045975, `1 ≤ k ≤ n`: the `k`-th smallest admissible number for row `n`. -/
noncomputable def T (n k : ℕ) : ℕ := Nat.nth (P n (last (n - 1))) (k - 1)

/-- A204558: the sum of row `n` of A045975. -/
noncomputable def a (n : ℕ) : ℕ := ∑ k ∈ Finset.Icc 1 n, T n k

open PowerSeries in
/-- Both conjectures of Colin Barker: the closed form and the rational generating function. -/
theorem main :
    (∀ n : ℕ, 1 ≤ n → (a n : ℚ) = ((n : ℚ) ^ 2 * (-(-1 : ℚ) ^ n + (n : ℚ) ^ 2)) / 2) ∧
    (PowerSeries.mk (fun n => (a n : ℤ)) * ((X - 1) ^ 5 * (X + 1) ^ 3) =
      -X * (X ^ 6 + 4 * X ^ 5 + 31 * X ^ 4 + 24 * X ^ 3 + 31 * X ^ 2 + 4 * X + 1)) := by
  sorry

end OMA.S_oeis_a204558
