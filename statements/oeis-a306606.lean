import Mathlib

/-!
# A306606: n = w^2 + T(x)^2 + Pen(y)^2 + 2*Pen(z)^2

Source: https://oeis.org/A306606

A306606 (offset 1): `a(n)` is the number of ways to write `n` as
`w^2 + T(x)^2 + Pen(y)^2 + 2*Pen(z)^2`, where `w, x, y, z` are integers with `w > 0` and `x ≥ 0`,
and `T(m) = m*(m+1)/2` and `Pen(m) = m*(3m-1)/2`: 1, 2, 2, 3, 4, 3, 3, 3, 3, 6, …  For example
`a(23) = 1` with `23 = 4^2 + T(1)^2 + Pen(-1)^2 + 2*Pen(1)^2`.

Conjecture (Zhi-Wei Sun, Feb 28 2019): `a(n) > 0` for all `n > 0`. In other words, any positive
integer `n` can be written as `s^2 + t^2 + u^2 + 2*v^2`, where `s` is a positive integer, `t` is
a triangular number, `u` and `v` are generalized pentagonal numbers. The entry notes that this
has been verified for all `n = 1..5*10^6`.

Since `a(n)` counts the quadruples `(w, x, y, z)` with `w > 0`, `x ≥ 0`, `y, z` integers and
`w^2 + T(x)^2 + Pen(y)^2 + 2*Pen(z)^2 = n`, `a(n) > 0` says exactly that such a quadruple exists,
and the conjecture is stated in that form.

Conventions:
- `w` and `x` range over `ℕ` (with `w > 0`), and `y`, `z` over `ℤ`, as in the sequence
  definition; the equation is stated in `ℤ`.
- `T(m) = m*(m+1)/2` and `Pen(m) = m*(3m-1)/2` use integer division by 2, which is exact because
  `m*(m+1)` and `m*(3m-1)` are even for every integer `m`.
-/

namespace OMA.S_oeis_a306606

/-- The triangular number `T(m) = m*(m+1)/2`. -/
def T (m : ℤ) : ℤ := m * (m + 1) / 2

/-- The (generalized) pentagonal number `Pen(m) = m*(3m-1)/2`, for any integer `m`. -/
def Pen (m : ℤ) : ℤ := m * (3 * m - 1) / 2

theorem main :
    ∀ n : ℕ, 0 < n →
      ∃ w x : ℕ, ∃ y z : ℤ, 0 < w ∧
        (w : ℤ) ^ 2 + T (x : ℤ) ^ 2 + Pen y ^ 2 + 2 * Pen z ^ 2 = (n : ℤ) := by
  sorry

end OMA.S_oeis_a306606
