import Mathlib

/-!
# A105802: Smallest m such that the m-th Fibonacci number has exactly n divisors that are also Fibonacci numbers.

Source: https://oeis.org/A105802
Credit: @agchua

Alexander Adamchuk (Sep 15 2006), in the formula section of A105802:
  Conjecture: a(2k+1) = 3*2^(Prime[k-1]-1) for k>3. It appears that a(2k+1) = 3*2^k for
  k = {1,2,3,4,6,10,12,16,18,...} = A068499[n] Numbers n such that n! reduced modulo (n+1) is
  not zero.

Prime[j] is the j-th prime in Mathematica's numbering (Prime[1] = 2), which is
`Nat.nth Nat.Prime (j - 1)`; so Prime[k-1] is `Nat.nth Nat.Prime (k - 2)` for k > 3.
A068499 is the set of k with k! mod (k+1) not zero.
Definition (offset 1): `c m` is the number of divisors of F(m) = `Nat.fib m` that are Fibonacci
numbers (this is A076984(m) for m >= 1), and `a n` is the least m >= 1 with `c m = n`. The index
m = 0 is left out because every Fibonacci number divides F(0) = 0. The statement is the
conjecture and the observation literally: the first for every k > 3, the second for every k in
A068499.
-/

namespace OMA.S_oeis_a105802

/-- The number of divisors of the m-th Fibonacci number that are Fibonacci numbers. -/
noncomputable def c (m : ℕ) : ℕ := Set.ncard {d : ℕ | d ∣ Nat.fib m ∧ ∃ j, Nat.fib j = d}

/-- A105802(n): the smallest m >= 1 such that F(m) has exactly n divisors that are Fibonacci
numbers. -/
noncomputable def a (n : ℕ) : ℕ := sInf {m : ℕ | 1 ≤ m ∧ c m = n}

/-- Adamchuk: a(2k+1) = 3*2^(Prime[k-1]-1) for k > 3, and a(2k+1) = 3*2^k for k in A068499. -/
theorem main : (∀ k : ℕ, 3 < k → a (2 * k + 1) = 3 * 2 ^ (Nat.nth Nat.Prime (k - 2) - 1)) ∧
    (∀ k : ℕ, Nat.factorial k % (k + 1) ≠ 0 → a (2 * k + 1) = 3 * 2 ^ k) := by
  sorry

end OMA.S_oeis_a105802
