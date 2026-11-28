import Mathlib

/-!
# A086534: Smallest prime p sandwiched between two numbers that are divisible by n-th powers.

Source: https://oeis.org/A086534
Credit: @avivorly

a(n) is the smallest prime p such that p - 1 and p + 1 are both divisible by n-th powers, that is, by
b ^ n for some b ≥ 2 (example in the entry: a(3) = 271, with 270 = 3^3 * 10 and 272 = 2^3 * 34).
The data in the entry are 2, 17, 271, 1249, 13121, 13121, 153089, ... (a(5) = a(6) = 13121: the
condition for n implies the condition for every smaller n). Under the reading b ≥ 2 used here,
a(1) = 3 rather than 2 (the entry's Mathematica program treats 1 as having a prime exponent 1);
a(n) agrees with the data for 2 ≤ n ≤ 8, and a single term does not affect finiteness.

Conjecture in the entry (Amarnath Murthy, 2003): the sequence is finite, i.e. a(n) exists for only
finitely many n.
-/

namespace OMA.S_oeis_a086534

/-- `m` is divisible by an `n`-th power `b ^ n` with `b ≥ 2`. -/
def DivisibleByPow (n m : ℕ) : Prop :=
  ∃ b : ℕ, 2 ≤ b ∧ b ^ n ∣ m

/-- `p` is a prime sandwiched between two numbers that are divisible by `n`-th powers. -/
def Sandwiched (n p : ℕ) : Prop :=
  p.Prime ∧ DivisibleByPow n (p - 1) ∧ DivisibleByPow n (p + 1)

/-- The sequence is finite: only finitely many `n ≥ 1` have a term a(n). -/
theorem main : Set.Finite {n : ℕ | 1 ≤ n ∧ ∃ p : ℕ, Sandwiched n p} := by
  sorry

end OMA.S_oeis_a086534
