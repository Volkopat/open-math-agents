import Mathlib

/-!
# A378277: Denominators in a harmonic triangle, based on products of Fibonacci numbers

Source: https://oeis.org/A378277
Credit: @jagong-cmu

Formalizes the OEIS A378277 conjecture (offset 1):
Alt. row sums of the harmonic triangle are Fibonacci(n-2) / Fibonacci(n+1), where
Fibonacci(-1) = 1.

Conventions:
* The name of A378277 does not give the entries explicitly. The statement uses the explicit
  OEIS formula: `T(n, k) = Fibonacci(n) * Fibonacci(n+1)` if `k = n`, and
  `T(n, k) = Fibonacci(k) * Fibonacci(k+2)` if `1 <= k < n`. It agrees with the OEIS data.
  `Nat.fib` is the Fibonacci sequence with `fib 0 = 0` and `fib 1 = 1`.
* The harmonic triangle has the entries `1 / T(n, k)` (numerators 1), for `1 <= k <= n`,
  computed in `ℚ`.
* The alternating row sum of row `n` is `Sum_{k=1..n} (-1)^(k+1) / T(n, k)`, with a plus sign
  on the first entry `k = 1`. This sign convention is the one that gives the positive values
  of the conjecture (the other convention, `(-1)^(n-k)`, gives the opposite sign for even `n`).
* `Fibonacci(n-2)` is `fib (n - 2)` for `n >= 2`, and `Fibonacci(-1) = 1` for `n = 1`, as the
  conjecture says. The claim is stated for every row `n >= 1`.
-/

namespace OMA.S_oeis_a378277

open Nat

/-- `T(n, k) = F(n)*F(n+1)` if `k = n`, and `F(k)*F(k+2)` if `1 <= k < n`. -/
def T (n k : ℕ) : ℕ :=
  if k = n then fib n * fib (n + 1) else fib k * fib (k + 2)

/-- `Fibonacci(n-2)` for `n >= 1`, with `Fibonacci(-1) = 1`. -/
def fibSub2 (n : ℕ) : ℕ := if n = 1 then 1 else fib (n - 2)

/-- For every `n >= 1`: `Sum_{k=1..n} (-1)^(k+1) / T(n,k) = Fibonacci(n-2) / Fibonacci(n+1)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    ∑ k ∈ Finset.Icc 1 n, (-1 : ℚ) ^ (k + 1) / (T n k : ℚ) =
      (fibSub2 n : ℚ) / (fib (n + 1) : ℚ) := by
  sorry

end OMA.S_oeis_a378277
