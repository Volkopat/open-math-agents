import Mathlib

/-!
# A244973: a(n) = Sum_{k=0..n} (-1)^k*C(n, k)^2*C(2*k, k).

Source: https://oeis.org/A244973
Credit: @luciusacarr

The entry records two conjectures. Only the binomial-transform conjecture (Peter Bala,
Jul 19 2024) is formalized here: a(n) = Sum_{k = 0..n} binomial(n, k)*b(k), where
b(n) = Sum_{k = 0..n} (-1)^k*binomial(n, k)^2*binomial(2*k, n). The other conjecture (for any
prime p > 5 and positive integer n, (a(p*n) - a(n))/(p*n)^3 is a p-adic integer) is not
formalized in this file.

Reading of the source:
* `a` and `b` are integer-valued (the signs make some terms negative), with `C(n, k)` the usual
  binomial coefficient, so they are defined over `ℤ` with `Nat.choose` cast in.
* The conjecture is the identity `a(n) = Sum_{k=0..n} C(n, k) * b(k)` for every `n ≥ 0`.
-/

namespace OMA.S_oeis_a244973

/-- `a(n) = Sum_{k=0..n} (-1)^k C(n,k)^2 C(2k,k)`. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2 * ((2 * k).choose k : ℤ)

/-- `b(n) = Sum_{k=0..n} (-1)^k C(n,k)^2 C(2k,n)`. -/
def b (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (-1 : ℤ) ^ k * (n.choose k : ℤ) ^ 2 * ((2 * k).choose n : ℤ)

theorem main : ∀ n : ℕ, a n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * b k := by
  sorry

end OMA.S_oeis_a244973
