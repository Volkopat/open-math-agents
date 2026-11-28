import Mathlib

/-!
# A068073: Period 4 sequence [ 1, 2, 3, 2, ...].

Source: https://oeis.org/A068073
Credit: @agchua

Formula line of A068073, by Paul Barry, Jan 14 2005:
  Conjecture: a(n) = Sum_{k=0..n} e^(i*Pi*(A000120(A001045(n)) - A001045(A000120(n)))), i=sqrt(-1).
A068073 has offset 0, so the claim is stated for every n ≥ 0: a(n) = 1, 2, 3, 2 for n ≡ 0, 1, 2, 3
(mod 4). The conjecture is stated literally, as printed: the summand
e^(i*Pi*(A000120(A001045(n)) - A001045(A000120(n)))) does not depend on the summation index k
(written _k below), so the sum is n+1 times that summand, which is a sign. The identity is stated in
the complex numbers, with Complex.exp, Complex.I and Real.pi. (As printed it fails at n = 3: the
sum is -4 while a(3) = 2. With k in place of n in the summand the identity holds for n < 400, but
that is not what is stated.)

The referenced sequences, by their own entries' definitions:
* A000120 (offset 0): the number of 1's in the binary expansion of n.
* A001045 (offset 0), the Jacobsthal numbers: a(0) = 0, a(1) = 1, a(n) = a(n-1) + 2*a(n-2).
-/

namespace OMA.S_oeis_a068073

/-- A068073(n): the period 4 sequence 1, 2, 3, 2, 1, 2, 3, 2, ... (offset 0). -/
def a (n : ℕ) : ℕ := if n % 4 = 0 then 1 else if n % 4 = 2 then 3 else 2

/-- A000120(n): the number of 1's in the binary expansion of n. -/
def a000120 (n : ℕ) : ℕ := (Nat.digits 2 n).count 1

/-- A001045: the Jacobsthal numbers, a(0) = 0, a(1) = 1, a(n) = a(n-1) + 2*a(n-2). -/
def a001045 : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | (n + 2) => a001045 (n + 1) + 2 * a001045 n

/-- The conjecture as printed:
a(n) = Sum_{k=0..n} e^(i*Pi*(A000120(A001045(n)) - A001045(A000120(n)))). -/
theorem main : ∀ n : ℕ, (a n : ℂ) = ∑ _k ∈ Finset.range (n + 1),
    Complex.exp (Complex.I * Real.pi *
      ((a000120 (a001045 n) : ℂ) - (a001045 (a000120 n) : ℂ))) := by
  sorry

end OMA.S_oeis_a068073
