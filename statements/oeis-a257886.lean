import Mathlib

/-!
# A257886: least m such that floor(n!/(2*floor(n/2)!)) + m is prime

Source: https://oeis.org/A257886

A257886 (offset 1): `a(n)` is the least positive `m` such that
`floor(n! / (2*(floor(n/2)!))) + m` is prime: 2, 1, 2, 1, 1, 1, 1, 13, 1, 1, 29, 1, 1, 37, …
For example for `n = 1` the floor is `0` and `0 + 2 = 2` is prime, so `a(1) = 2`; for `n = 2`
the floor is `1` and `1 + 1 = 2` is prime, so `a(2) = 1`.

Conjecture (David Morales Marciel, May 11 2015): no term is composite. (The entry compares this
with the similar conjecture for the Fortunate numbers, A033932.)

Conventions:
- `f n` is `floor(n! / (2 * floor(n/2)!))`, with natural-number division as the floor.
- `a(n)` is the least positive `m` with `f n + m` prime. A composite number is an integer
  greater than `1` that is not prime, so `no term is composite` means that every term is `1` or
  a prime.
- The statement is: for every `n ≥ 1`, any `m` that is the least element (`IsLeast`) of the set
  of positive `m` with `f n + m` prime satisfies `m = 1` or `m` is prime.
-/

namespace OMA.S_oeis_a257886

/-- `floor(n! / (2 * floor(n/2)!))`. -/
def f (n : ℕ) : ℕ := n.factorial / (2 * (n / 2).factorial)

theorem main :
    ∀ n m : ℕ, 0 < n → IsLeast {m : ℕ | 0 < m ∧ Nat.Prime (f n + m)} m →
      m = 1 ∨ Nat.Prime m := by
  sorry

end OMA.S_oeis_a257886
