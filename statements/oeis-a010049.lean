import Mathlib

/-!
# A010049: Second-order Fibonacci numbers.

Source: https://oeis.org/A010049
Credit: @<your GitHub handle>

The entry records the conjecture (Peter Bala, Oct 24 2007):
"The polynomials F_2(n,-x) = Sum_{k=0..n} C(n,k)*a(n-k)*(-x)^k appear to satisfy a Riemann
hypothesis; their zeros appear to lie on the vertical line Re x = 1/2 in the complex plane."

* `a(n)` is A010049 (offset 0: `0, 1, 1, 3, 5, 10, 18, 33, 59, ...`). We use the recurrence
  recorded in the entry (Benoit Cloitre): `a(0) = 0`, `a(1) = 1`, `a(2) = 1`,
  `a(n+2) = a(n+1) + a(n) + F(n)`, with `F = Nat.fib` the Fibonacci numbers (A000045);
  it agrees with the g.f. `x(1-x)/(1-x-x^2)^2` given there.
* `F2neg n` is the polynomial `F_2(n,-x) = Sum_{k=0..n} C(n,k) a(n-k) (-x)^k` over `ℂ`.
* The conjecture is stated for `n ≥ 1`: for `n = 0` the polynomial is `a(0) = 0`, the zero
  polynomial, every complex number is a root, and the claim is meaningless. (For `n = 1` the
  polynomial is the constant `1`, and the statement holds vacuously.)
-/

namespace OMA.S_oeis_a010049

open Polynomial

/-- A010049, second-order Fibonacci numbers: `a(0) = 0`, `a(1) = 1`, `a(2) = 1`,
`a(n+3) = a(n+2) + a(n+1) + F(n+1)`. -/
def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n + 3 => a (n + 2) + a (n + 1) + Nat.fib (n + 1)

/-- Bala's polynomial `F_2(n,-x) = Sum_{k=0..n} C(n,k) a(n-k) (-x)^k`, over `ℂ`. -/
noncomputable def F2neg (n : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1), C ((Nat.choose n k : ℂ) * (a (n - k) : ℂ)) * (-X) ^ k

/-- Bala's "Riemann hypothesis" for A010049: for `n ≥ 1`, every complex zero of `F_2(n,-x)`
has real part `1/2`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∀ z : ℂ, (F2neg n).eval z = 0 → z.re = 1 / 2 := by
  sorry

end OMA.S_oeis_a010049
