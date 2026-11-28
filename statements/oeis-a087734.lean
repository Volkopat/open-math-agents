import Mathlib

/-!
# A087734: a(n) = f(f(n)), where f() = A035327().

Source: https://oeis.org/A087734
Credit: @cj-55m (agent: Claude Code, model claude-opus-5-5)

The entry (offset 0, data 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 2, 3, 0, 1, 0, 0, 0, 1, 2, 3, ...)
records in its FORMULA section:

  From Mikhail Kurkov, Sep 29 2019: Some conjectures: ...
  a(n) = 2*a(floor(n/2)) + n mod 2 - A036987(n) for n>1 with a(0)=a(1)=0.

Conventions:
* `f n` is A035327(n): write `n` in binary, interchange 0's and 1's, convert back to decimal.
  With `k = Nat.size n` the number of binary digits of `n`, this is `2^k - 1 - n` (the entry
  A035327 gives `a(n) = 2^k - n - 1` for `2^(k-1) ≤ n < 2^k`).
* For `n = 0` this gives `f 0 = 0` (the binary representation of zero taken to be the empty
  string), whereas A035327 lists `A035327(0) = 1`. The value `f 0 = 0` is the one that
  reproduces the DATA of A087734: with `f 0 = 1` one would get `a(1) = f(f(1)) = f(0) = 1`,
  but the entry has `a(1) = 0` (and `a(3) = a(7) = 0`). With `f 0 = 0`, `a n = f (f n)` agrees
  with all listed terms.
* `a n = f (f n)`, indexed from `0` (offset 0).
* `fr n` is A036987(n) (Fredholm-Rueppel sequence, offset 0): `1` if `n + 1` is a power of
  `2`, i.e. `n = 2^k - 1` for some `k`, and `0` otherwise. Such a `k` satisfies `k ≤ n + 1`, so
  the search is bounded to keep the definition computable.
* The conjecture is stated over `ℤ` (because of the subtraction), together with the initial
  values `a 0 = 0` and `a 1 = 0`.
-/

namespace OMA.S_oeis_a087734

/-- A035327 with the empty-string convention at `0`: complement the binary digits of `n`. -/
def f (n : ℕ) : ℕ := 2 ^ Nat.size n - 1 - n

/-- A087734: `a(n) = f(f(n))`. -/
def a (n : ℕ) : ℕ := f (f n)

/-- A036987: `1` if `n = 2^k - 1` for some `k`, else `0`. -/
def fr (n : ℕ) : ℕ := if ∃ k < n + 2, n + 1 = 2 ^ k then 1 else 0

/-- The conjecture of A087734 (Mikhail Kurkov): `a(0) = a(1) = 0` and
`a(n) = 2*a(floor(n/2)) + n mod 2 - A036987(n)` for `n > 1`. -/
theorem main : a 0 = 0 ∧ a 1 = 0 ∧
    ∀ n : ℕ, 1 < n →
      (a n : ℤ) = 2 * (a (n / 2) : ℤ) + ((n % 2 : ℕ) : ℤ) - (fr n : ℤ) := by
  sorry

end OMA.S_oeis_a087734
