import Mathlib

/-!
# A016957: a(n) = 6*n + 4.

Source: https://oeis.org/A016957
Credit: @prasledi

Conjecture (John Tyler Rascoe, Jul 09 2022, in the COMMENTS of A016957): "this sequence contains
some but not all, even numbers with odd abundance A088827. They appear in this sequence at indices
A186424(n) - 1."

Formalization notes:
* `a n = 6 * n + 4`, offset 0, as in the OEIS entry.
* A088827 ("Even numbers with odd abundance") is stated by its definition: `m` is even and the
  abundance `σ(m) - 2m` (computed in `ℤ`, since it can be negative) is odd. For `m = 0` the
  abundance is `0`, so `0` is not a term, matching the OEIS data (which starts 2, 4, 8, ...).
* A186424 is "Odd terms in A186423", where A186423 is "Partial sums of A186421" and A186421 is
  "Even numbers interleaved with repeated odd numbers": `A186421 n = n` for even `n` and
  `2 * ⌊n / 4⌋ + 1` for odd `n` (offset 0: 0, 1, 2, 1, 4, 3, 6, 3, 8, ...). The partial sums
  start at index 0 (`A186423 0 = A186421 0 = 0`).
* "They appear at indices A186424(n) - 1" is stated as: the indices `k` with `a k` in A088827 are
  exactly the numbers `t - 1` with `t` a term of A186424, i.e. an odd value of A186423. (A186423 is
  increasing, so its odd terms listed in order are just its odd values in increasing order; the
  statement only needs them as a set.)
* "Some but not all" is: some term of A088827 is a value of `a`, and some term of A088827 is not.
-/

namespace OMA.S_oeis_a016957

/-- A016957: `a(n) = 6 * n + 4`. -/
def a (n : ℕ) : ℕ := 6 * n + 4

/-- A088827: `m` is an even number with odd abundance `σ(m) - 2m`. -/
def A088827 (m : ℕ) : Prop :=
  Even m ∧ Odd ((ArithmeticFunction.sigma 1 m : ℤ) - 2 * m)

/-- A186421: even numbers interleaved with repeated odd numbers. -/
def A186421 (n : ℕ) : ℕ := if Even n then n else 2 * (n / 4) + 1

/-- A186423: partial sums of A186421. -/
def A186423 (n : ℕ) : ℕ := ∑ i ∈ Finset.range (n + 1), A186421 i

/-- The terms of A186424: the odd terms of A186423. -/
def A186424 : Set ℕ := {t | Odd t ∧ ∃ i, A186423 i = t}

/-- Rascoe's conjecture on A016957. -/
theorem main :
    (∃ n, A088827 (a n)) ∧ (∃ m, A088827 m ∧ ∀ n, a n ≠ m) ∧
      (∀ k, A088827 (a k) ↔ ∃ t ∈ A186424, k = t - 1) := by
  sorry

end OMA.S_oeis_a016957
