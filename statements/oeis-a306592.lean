import Mathlib

/-!
# A306592: the 1-2-3-4-5 conjecture on generalized pentagonal numbers

Source: https://oeis.org/A306592

A306592 (offset 0): `a(n)` is the number of ways to write `n` as
`u^2 + 2*v^2 + 3*x^2 + 4*y^2 + 5*z^2`, where `u, v, x, y, z` are generalized pentagonal numbers
(A001318): 1, 1, 1, 2, 3, 3, 4, 4, 5, 6, …

Conjecture (Zhi-Wei Sun, Feb 26 2019, called the 1-2-3-4-5 conjecture in the entry):
`a(n) > 0` for any nonnegative integer `n`. The entry notes that this has been verified for all
`n = 0..4*10^5`.

Since `a(n)` counts the quintuples of generalized pentagonal numbers `(u, v, x, y, z)` with
`u^2 + 2*v^2 + 3*x^2 + 4*y^2 + 5*z^2 = n`, `a(n) > 0` says exactly that such a quintuple exists,
and the conjecture is stated in that form.

Conventions: the generalized pentagonal numbers (A001318) are the numbers `k*(3*k-1)/2` with `k`
any integer: 0, 1, 2, 5, 7, 12, 15, 22, 26, …  A natural number `m` is one of them when
`2*m = k*(3*k-1)` for some integer `k`.
-/

namespace OMA.S_oeis_a306592

/-- `m` is a generalized pentagonal number (A001318): `m = k*(3k-1)/2` for some integer `k`. -/
def IsGenPentagonal (m : ℕ) : Prop := ∃ k : ℤ, 2 * (m : ℤ) = k * (3 * k - 1)

theorem main :
    ∀ n : ℕ, ∃ u v x y z : ℕ, IsGenPentagonal u ∧ IsGenPentagonal v ∧ IsGenPentagonal x ∧
      IsGenPentagonal y ∧ IsGenPentagonal z ∧
      u ^ 2 + 2 * v ^ 2 + 3 * x ^ 2 + 4 * y ^ 2 + 5 * z ^ 2 = n := by
  sorry

end OMA.S_oeis_a306592
