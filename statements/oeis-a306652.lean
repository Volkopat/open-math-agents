import Mathlib

/-!
# A306652: a(n) = Sum_{m=1..n} Sum_{k=1..n} [k divides n]*[n/k divides m]*[k divides m + 4].

Source: https://oeis.org/A306652
Credit: @luciusacarr

The entry's comment: "In an analogy of Dirichlet convolutions A147848 corresponds to the twin
primes while this sequence corresponds to the cousin primes, and it appears that this sequence
differs from A147848 at multiples of 16." Known terms (offset 1): 1, 2, 2, 4, 2, 4, 2, 6, ...;
A147848 begins 1, 2, 2, 4, 2, 4, 2, 6, ..., the first difference being a(16) = 10 versus
A147848(16) = 6.

Reading of the source:
* `[P]` is the Iverson bracket (1 if `P` holds, else 0), so a(n) counts the pairs `(m, k)` with
  `1 ≤ m, k ≤ n`, `k ∣ n`, `(n/k) ∣ m` and `k ∣ m + 4`.
* A147848 ("number of groups of order 2n that have Z/nZ as a subgroup") is taken through the
  formula recorded in its entry (Mats Granvik, Mar 03 2019), which is exactly the analogy the
  comment refers to: A147848(n) = Sum_{m=1..n} Sum_{k=1..n} [k divides n]*[n/k divides m]*
  [k divides m + 2]. (It agrees with that entry's multiplicative formula a(2) = 2, a(4) = 4,
  a(2^k) = 6 for k >= 3, a(p^k) = 2 for odd primes p.) The group-theoretic definition itself is
  not formalized.
* "Differs from A147848 at multiples of 16" is read as: for every `n ≥ 1`,
  A306652(n) ≠ A147848(n) if and only if `16 ∣ n`.
-/

namespace OMA.S_oeis_a306652

/-- `Sum_{m=1..n} Sum_{k=1..n} [k ∣ n] [(n/k) ∣ m] [k ∣ m + c]`. -/
def S (c n : ℕ) : ℕ :=
  ∑ m ∈ Finset.Icc 1 n, ∑ k ∈ Finset.Icc 1 n, if k ∣ n ∧ n / k ∣ m ∧ k ∣ m + c then 1 else 0

/-- A306652: the case `c = 4` ("cousin primes"). -/
def a306652 (n : ℕ) : ℕ := S 4 n

/-- A147848, via the formula of its entry: the case `c = 2` ("twin primes"). -/
def a147848 (n : ℕ) : ℕ := S 2 n

theorem main : ∀ n : ℕ, 1 ≤ n → (a306652 n ≠ a147848 n ↔ 16 ∣ n) := by
  sorry

end OMA.S_oeis_a306652
