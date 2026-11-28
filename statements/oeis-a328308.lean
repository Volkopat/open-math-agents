import Mathlib

/-!
# A328308: a(n) = 1 if k-th arithmetic derivative of n is zero for some k, otherwise 0.

Source: https://oeis.org/A328308
Credit: @agchua

Formula line of A328308 (Antti Karttunen, Jan 06 2023):
  a(0) = 1; and for n > 0, a(n) = A359550(n) * a(A003415(n)). [Provided that Conjecture 3 given on
  page 5 of Ufnarovski and Åhlander 2003 paper holds, i.e., that map x -> x' never forms nontrivial
  loops]
Offset 0. The statement below asserts the formula for all n, without the proviso (so it is the
stronger, unconditional claim).
Definitions: A003415(n) = n' is the arithmetic derivative, written by its formula
n' = sum of e * n / p over the prime powers p^e exactly dividing n (so 0' = 1' = 0, p' = 1 for a
prime p, and (mn)' = m n' + n m'); a(n) = 1 if some iterate D^k(n), k >= 0, is 0, and 0 otherwise;
A359550(0) = 0, and for n >= 1, A359550(n) is the product of [e < p] over the prime powers p^e
exactly dividing n (multiplicative with a(p^e) = [e < p], as in the entry A359550).
-/

namespace OMA.S_oeis_a328308

/-- A003415: the arithmetic derivative, the sum of e * n / p over the prime powers p^e exactly
dividing n. -/
noncomputable def D (n : ℕ) : ℕ := ∑ p ∈ n.primeFactors, n.factorization p * (n / p)

open Classical in
/-- A328308: 1 if some iterated arithmetic derivative of n is 0, and 0 otherwise. -/
noncomputable def a (n : ℕ) : ℕ := if ∃ k : ℕ, D^[k] n = 0 then 1 else 0

/-- A359550: 0 at n = 0; for n ≥ 1 the product of [e < p] over the prime powers p^e exactly
dividing n. -/
noncomputable def A359550 (n : ℕ) : ℕ :=
  if n = 0 then 0 else ∏ p ∈ n.primeFactors, (if n.factorization p < p then 1 else 0)

/-- a(0) = 1, and a(n) = A359550(n) * a(A003415(n)) for n > 0. -/
theorem main : a 0 = 1 ∧ ∀ n : ℕ, 0 < n → a n = A359550 n * a (D n) := by
  sorry

end OMA.S_oeis_a328308
