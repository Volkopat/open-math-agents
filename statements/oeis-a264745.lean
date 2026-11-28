import Mathlib

/-!
# A264745: Rectangular array A read by upward antidiagonals in which the entry in row n and column k is defined by A(n,k) = Fibonacci(2^(n-1)*(2*k-1) + 1), n,k >= 1.

Source: https://oeis.org/A264745
Credit: @agchua

In the formula section of A264745 (the line has no author or date; the entry is by
L. Edson Jeffery, Nov 23 2015):
  Conjectured g.f. for row n: x*(A000045(2^(n-1)+1) - A000045(2^(n-1)-1)*x)/(1 - A001566(n)*x + x^2), n >= 1.
A000045 is the Fibonacci sequence, `Nat.fib` (F(0) = 0, F(1) = 1). A001566 is the sequence with
offset 0 given by a(0) = 3, a(n) = a(n-1)^2 - 2 (3, 7, 47, 2207, ...), as in its own entry.
The g.f. of row n is the power series of the row, ∑_{k >= 1} A(n,k) x^k, written here as
X * ∑_{j >= 0} A(n,j+1) X^j. The conjecture is stated literally, for every n >= 1, as an identity of
formal power series over ℚ after multiplication by the denominator 1 - A001566(n) X + X^2
(whose constant term is 1):
  (X * ∑_j A(n,j+1) X^j) * (1 - A001566(n) X + X^2) = X * (F(2^(n-1)+1) - F(2^(n-1)-1) X).
-/

namespace OMA.S_oeis_a264745

/-- The array: A(n,k) = Fibonacci(2^(n-1)*(2*k-1) + 1). -/
def A (n k : ℕ) : ℕ := Nat.fib (2 ^ (n - 1) * (2 * k - 1) + 1)

/-- A001566: a(0) = 3, a(n) = a(n-1)^2 - 2. -/
def A001566 : ℕ → ℤ
  | 0 => 3
  | (n + 1) => A001566 n ^ 2 - 2

/-- The conjectured g.f. of row n of A264745, for every n >= 1, as printed in the entry. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    PowerSeries.X * PowerSeries.mk (fun j => (A n (j + 1) : ℚ)) *
        (1 - (PowerSeries.C : ℚ →+* PowerSeries ℚ) (A001566 n : ℚ) * PowerSeries.X +
          PowerSeries.X ^ 2) =
      PowerSeries.X * ((PowerSeries.C : ℚ →+* PowerSeries ℚ) (Nat.fib (2 ^ (n - 1) + 1) : ℚ) -
        (PowerSeries.C : ℚ →+* PowerSeries ℚ) (Nat.fib (2 ^ (n - 1) - 1) : ℚ) *
          PowerSeries.X) := by
  sorry

end OMA.S_oeis_a264745
