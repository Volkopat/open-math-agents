import Mathlib

/-!
# A366362: Triangle read by rows: T(n,k) = Sum_{y=1..n} Sum_{x=1..n} [GCD(f(x,y), n) = k], where f(x,y) = x^3 - x^2 - y^2 - y.

Source: https://oeis.org/A366362
Credit: @agchua

Formula line of A366362 (unsigned):
  Conjecture: T(n,n) = A060457(n).
A366362 has offset 1 (rows n ≥ 1, 1 ≤ k ≤ n), so the claim is stated for n ≥ 1.
GCD(f(x,y), n) is the nonnegative gcd of the integer f(x,y) and n: Mathlib's `Int.gcd`.
[P] is 1 if P holds and 0 otherwise.

The referenced sequence, by its own entry's definition:
* A060457 (offset 1) is the number of solutions to y^2 + y = x^3 - x^2 modulo n, that is, the
  number of residue pairs (x, y) with 0 ≤ x, y < n and n ∣ y^2 + y - (x^3 - x^2), as in the
  entry's first PARI program.
-/

namespace OMA.S_oeis_a366362

/-- f(x,y) = x^3 - x^2 - y^2 - y. -/
def f (x y : ℤ) : ℤ := x ^ 3 - x ^ 2 - y ^ 2 - y

/-- A366362: T(n,k) = Sum_{y=1..n} Sum_{x=1..n} [GCD(f(x,y), n) = k]. -/
def T (n k : ℕ) : ℕ :=
  ∑ y ∈ Finset.Icc 1 n, ∑ x ∈ Finset.Icc 1 n,
    if Int.gcd (f (x : ℤ) (y : ℤ)) (n : ℤ) = k then 1 else 0

/-- A060457(n): the number of solutions to y^2 + y = x^3 - x^2 modulo n. -/
def a060457 (n : ℕ) : ℕ :=
  ∑ x ∈ Finset.range n, ∑ y ∈ Finset.range n,
    if (n : ℤ) ∣ ((y : ℤ) ^ 2 + (y : ℤ) - ((x : ℤ) ^ 3 - (x : ℤ) ^ 2)) then 1 else 0

/-- The conjecture: T(n,n) = A060457(n) for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → T n n = a060457 n := by
  sorry

end OMA.S_oeis_a366362
