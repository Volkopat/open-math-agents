import Mathlib

/-!
# A306562: a(n) = 1 + 2 - 3 - 4 + 5 + 6 + 7 - 8 - 9 - 10 - 11 + 12 + ...

Source: https://oeis.org/A306562 (conjecture by Jean-François Alcover, Jun 01 2019)

Entry (offset 0): a(n) = 1 + 2 - 3 - 4 + 5 + 6 + 7 - 8 - 9 - 10 - 11 + 12 + 13 + 14 + 15 + ...,
where, after the 1st summand there is one plus, two minuses, three plusses, etc.
Conjecture: F(n) = ((-1)^(n+1)(2n+1)(2n^2+2n+5)+21)/16 gives local extrema
3, -4, 14, -24, 46, -71, 111, -157, ...

Conventions:
* After the first summand 1, the k-th summand (k >= 1) is k + 1, and the signs come in blocks
  of lengths 1, 2, 3, ..., alternately plus and minus starting with plus. The block containing
  the k-th summand is `blk k`, the least j with k <= j(j+1)/2 (A002024), and its sign is plus
  exactly when `blk k` is odd. a(n) is the sum of the first n + 1 summands, so a(0) = 1,
  a(1) = 3, a(2) = 0, a(3) = -4 as in the data (this is the formula of Jinyuan Wang in the
  entry: a(n) = 1 + Sum_{k=1..n} (-1)^(A002024(k)+1)*(k+1)).
* The local extrema of a are the indices m >= 1 where a(m) is strictly above or strictly below
  both neighbours, i.e. (a(m-1) - a(m)) * (a(m+1) - a(m)) > 0 (the index 0 is an endpoint).
* The conjecture is read as: the local extrema occur exactly at the ends of the blocks, i.e. at
  the indices m = n(n+1)/2 with n >= 1, and the extremum at the end of the n-th block is F(n);
  the value is stated after multiplying by 16, in the integers.
-/

namespace OMA.S_oeis_a306562

/-- The block (of the blocks of lengths 1, 2, 3, ...) containing the k-th summand (A002024). -/
noncomputable def blk (k : ℕ) : ℕ := sInf {j : ℕ | k ≤ j * (j + 1) / 2}

/-- A306562(n). -/
noncomputable def a (n : ℕ) : ℤ :=
  1 + ∑ k ∈ Finset.Icc 1 n, (if blk k % 2 = 1 then ((k : ℤ) + 1) else -((k : ℤ) + 1))

theorem main :
    (∀ n : ℕ, 1 ≤ n →
      16 * a (n * (n + 1) / 2) = (-1) ^ (n + 1) * (2 * n + 1) * (2 * n ^ 2 + 2 * n + 5) + 21) ∧
    ∀ m : ℕ, 1 ≤ m →
      (0 < (a (m - 1) - a m) * (a (m + 1) - a m) ↔ ∃ n : ℕ, 1 ≤ n ∧ m = n * (n + 1) / 2) := by
  sorry

end OMA.S_oeis_a306562
