import Mathlib

/-!
# A375852: Numbers congruent to {0, 1, 3, 6, 7, 9, 12, 15} mod 18.

Source: https://oeis.org/A375852
Credit: @agchua

Comment of A375852 (unsigned, verbatim):
  Appears to be the union of A061641 (pure numbers in the Collatz (3x+1) iteration, also
  called pure hailstone numbers) and A309180 (unsuspected numbers to check in the Collatz
  conjecture).

A375852 has offset 1 and begins with a(1) = 0; as a set it is the set of all n whose
remainder mod 18 lies in S = {0, 1, 3, 6, 7, 9, 12, 15}.

A061641 (offset 1, a(1) = 0): with f(0, N) = N and f(k+1, N) = f(k, N)/2 for f(k, N) even,
3 f(k, N) + 1 for f(k, N) odd, its comment says that a(n) is not a value in any sequence f(k, N)
with N < a(n); these are the pure numbers, here `isPure` (0 is pure, as in the data).

A309180 (offset 1): the coloring of the entry, as its C# program computes it. Going through
i = 1, 2, 3, ..., a number i that has not been colored red is blue, and then the iterates
T(i), T(T(i)), ... are colored red as long as they are larger than i (the walk stops at the
first iterate that is at most i). A309180 lists the n at least 1 that do not fit the expected
pattern: n is red although n mod 18 lies in S, or n is blue although n mod 18 lies in
{2, 4, 5, 8, 10, 11, 13, 14, 16, 17}, the complement of S. `IsColoring` is the defining
recursion of the coloring (blue n depends only on blue i for i < n, so at most one predicate
satisfies it); the statement says that such a coloring exists and that, for it, the union of
A061641 and A309180 is the set of terms of A375852.
-/

namespace OMA.S_oeis_a375852

/-- The Collatz (3x+1) map. -/
def T (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- The residues mod 18 of the terms of A375852. -/
def S : Finset ℕ := {0, 1, 3, 6, 7, 9, 12, 15}

/-- A061641: n is pure, i.e. n is not a value of the 3x+1 sequence of any start N < n. -/
def isPure (n : ℕ) : Prop := ∀ N < n, ∀ k : ℕ, T^[k] N ≠ n

/-- The coloring of A309180: n is blue iff n ≥ 1 and no blue i < n colors n red, where i colors
n red iff n = T^[j] i with j ≥ 1 and all of T^[1] i, ..., T^[j] i larger than i. -/
def IsColoring (blue : ℕ → Prop) : Prop :=
  ∀ n, blue n ↔ (1 ≤ n ∧ ¬ ∃ i < n, blue i ∧
    ∃ j, 1 ≤ j ∧ T^[j] i = n ∧ ∀ l, 1 ≤ l → l ≤ j → i < T^[l] i)

/-- A309180 for the coloring blue: n ≥ 1 is red with residue in S, or blue with residue not
in S. -/
def A309180 (blue : ℕ → Prop) (n : ℕ) : Prop :=
  1 ≤ n ∧ ((n % 18 ∈ S ∧ ¬ blue n) ∨ (n % 18 ∉ S ∧ blue n))

/-- The comment's claim: the terms of A375852 form the union of A061641 and A309180. -/
theorem main : (∃ blue : ℕ → Prop, IsColoring blue) ∧
    ∀ blue : ℕ → Prop, IsColoring blue →
      {n : ℕ | n % 18 ∈ S} = {n : ℕ | isPure n} ∪ {n : ℕ | A309180 blue n} := by
  sorry

end OMA.S_oeis_a375852
