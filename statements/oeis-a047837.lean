import Mathlib

/-!
# A047837: Honaker's triangle problem.

Source: https://oeis.org/A047837
Credit: @thatoneguy006

Name: form a triangle with base of length n, all entries different, all row sums equal;
a(n) gives the minimal row sum. Offset 1.

The conjecture stated here, from the entry:

  Agrees with A047873 at least for n < 365, conjectured to always agree.

where A047873(n) = max_{r=1..n-1} ceiling(t(t(n)-t(r-1))/(n-r+1)), t the triangular numbers
A000217. A047873 calls this a lower bound for the problem, conjectured to be exact.

Reading.
* A triangle with base of length n has rows of lengths 1, 2, ..., n. Its entries are positive
  integers (the examples of the entry use 1, 2, 3, ...; and a(1) = 1, which rules out 0), pairwise
  different over the whole triangle, and every row has the same sum. A047837(n) is the least such
  common row sum (`sInf`). With this reading a brute force search gives 1, 3, 8, 15, 27 for
  n = 1..5, the data of the entry.
* For n = 1 the range r = 1..n-1 in A047873 is empty; the data of A047873 gives a(1) = 1, which
  is used here.
-/

namespace OMA.S_oeis_a047837

/-- `s` is the common row sum of a Honaker triangle with base `n`: rows `i = 0, ..., n-1` of
length `i + 1`, with pairwise different positive entries and all row sums equal to `s`. -/
def IsHonakerSum (n s : ℕ) : Prop :=
  ∃ e : (i : Fin n) → Fin (i.val + 1) → ℕ,
    (∀ i j, 0 < e i j) ∧
    Function.Injective (fun x : (Σ i : Fin n, Fin (i.val + 1)) => e x.1 x.2) ∧
    ∀ i : Fin n, ∑ j, e i j = s

/-- A047837(n): the minimal row sum of a Honaker triangle with base `n`. -/
noncomputable def a (n : ℕ) : ℕ := sInf {s : ℕ | IsHonakerSum n s}

/-- The triangular numbers A000217. -/
def t (m : ℕ) : ℕ := m * (m + 1) / 2

/-- A047873(n) = max_{r=1..n-1} ceiling(t(t(n)-t(r-1))/(n-r+1)), and A047873(1) = 1. -/
noncomputable def A047873 (n : ℕ) : ℕ :=
  if n = 1 then 1 else
    (Finset.Icc 1 (n - 1)).sup fun r =>
      ⌈((t (t n - t (r - 1)) : ℕ) : ℚ) / ((n - r + 1 : ℕ) : ℚ)⌉₊

/-- The conjecture: A047837 and A047873 agree for every n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → a n = A047873 n := by
  sorry

end OMA.S_oeis_a047837
