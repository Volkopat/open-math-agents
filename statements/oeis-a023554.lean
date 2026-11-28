import Mathlib

/-!
# A023554: Convolution of natural numbers >= 3 and (Fib(2), Fib(3), Fib(4), ...).

Source: https://oeis.org/A023554
Credit: @JeremyDevs

Formalizes the conjecture recorded in the FORMULA section of OEIS A023554 (Creighton Dement,
Feb 02 2005): 2*(n+5) = A022308(n+4) - a(n+1) (conjectured). Note offset of A022308 is 0.

Conventions:
* A023554 has offset 1 and is the convolution of the sequence 3, 4, 5, ... (natural numbers >= 3)
  with the sequence Fib(2), Fib(3), Fib(4), ...; that is,
  a(n) = Sum_{k=0..n-1} (k+3)*Fib(n-1-k+2) = Sum_{k=0..n-1} (k+3)*Fib(n-k+1) for n >= 1,
  with data 3, 10, 22, 43, 78, 136, ... `a n` is this sum for every natural number n (the value
  `a 0 = 0`, an empty sum, is never used). In the sum k < n, so the natural-number subtraction
  n - k is exact. Fib is `Nat.fib` (Fib(0) = 0, Fib(1) = 1).
* A022308 has offset 0 and is defined by its name: a(n) = a(n-1) + a(n-2) + 1 for n > 1,
  a(0) = 0, a(1) = 3; data 0, 3, 4, 8, 13, 22, 36, 59, ...
* The source gives no range for n. Since A023554 has offset 1, the term a(n+1) is defined for
  every n >= 0, and the identity is asserted for every n >= 0 (for n = 0 it reads
  10 = 13 - 3). Values are integers, so the subtraction is the integer one.
-/

namespace OMA.S_oeis_a023554

/-- A023554 (offset 1): a(n) = Sum_{k=0..n-1} (k+3)*Fib(n-k+1). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range n, ((k : ℤ) + 3) * (Nat.fib (n - k + 1) : ℤ)

/-- A022308 (offset 0): a(0) = 0, a(1) = 3, a(n) = a(n-1) + a(n-2) + 1. -/
def A022308 : ℕ → ℤ
  | 0 => 0
  | 1 => 3
  | n + 2 => A022308 (n + 1) + A022308 n + 1

/-- For every n >= 0, 2*(n+5) = A022308(n+4) - a(n+1). -/
theorem main : ∀ n : ℕ, 2 * ((n : ℤ) + 5) = A022308 (n + 4) - a (n + 1) := by
  sorry

end OMA.S_oeis_a023554
