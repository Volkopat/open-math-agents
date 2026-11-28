import Mathlib

/-!
# A361337: numbers that reach 0 after a series of split-and-multiply operations

Source: https://oeis.org/A361337
Credit: @avivorly

A361337 lists the numbers that reach 0 after a suitable series of split-and-multiply operations.
The entry explains: we always split the integer `N` into two integers, then multiply them (and iterate).
For example, 2023 can be split into 20 and 23 (producing 20*23 = 460), or split into 202 and 3 (producing
202*3 = 606). The split 2 and 023 is forbidden, as 023 is not an integer (but 460 can be split into 46 and 0
as 0 is an integer). The sequence lists numbers which reach 0 after a suitable sequence of splits and
multiplications. Its data begin 0, 10, 20, 25, 30, 40, 45, 50, 52, 54, 55, 56, 58, 59, 60, ... (offset 1).

Conjecture (M. F. Hasler, Apr 05 2023, in the entry): `a(2894 + k) = 3112 + k for all k >= 0 (conjectured).`

Conventions:
- A number is read as its decimal digit string (no leading zero; the number 0 is the string `0`).
  A split cuts the digit string of `N` into a nonempty prefix and a nonempty suffix, and each part must itself be
  the decimal string of an integer: no leading zero, unless the part is the single digit `0`.
- In arithmetic form: let `j` be the length of the suffix, so `1 ≤ j` and `j` is less than the number of digits
  of `N`, which is `10 ^ j ≤ N`. The prefix is the decimal string of `N / 10 ^ j`. It starts with the leading
  digit of `N`, which is nonzero, so it is always a legal part. The suffix is the string of `N % 10 ^ j` padded
  with zeros on the left to exactly `j` digits. It is a legal part iff `j = 1` (a single digit, `0` included)
  or its first digit is nonzero, which is `10 ^ (j - 1) ≤ N % 10 ^ j`. The product of the split is
  `N / 10 ^ j * (N % 10 ^ j)`. This is `SplitProd`. The entry's examples: `2023` gives `20 * 23 = 460`
  (`j = 2`) and `202 * 3 = 606` (`j = 1`), the cut `2 | 023` (`j = 3`, `N % 1000 = 23 < 100`) is excluded,
  and `460` gives `46 * 0 = 0` (`j = 1`).
- A one-digit number has no split, since `10 ^ j ≤ N` fails for `j ≥ 1` and `N ≤ 9`.
- `Reaches0 N`: a finite, possibly empty, chain of splits leads from `N` to `0` (`Relation.ReflTransGen`).
  So `0` is a term with zero steps, as the entry's data `a(1) = 0` say, and `1, ..., 9` are not terms.
- Other readings of the leading-zero rule give the same set of terms. Allowing an all-zero suffix such as
  `00`, or any leading zeros (the entry's Python programs read the parts with `int`, which accepts them), changes
  nothing: under each reading, every number `N ≥ 10` with a digit `0` is a term (cut right after its last `0`
  digit: if that digit is the last one the product is `0`; otherwise the suffix starts with a nonzero digit
  and the prefix ends in `0`, so the product is a positive multiple of `10`, and cutting off its last digit `0`
  gives `0`). A number with no digit `0` has no cut with a leading zero under any reading. By induction on `N`
  (every product is less than `N`), all readings, and the programs' shortcut that a number with a digit `0`
  is a term, define the same set.
- Offset 1 (the entry's `%O 1,2`): `a n = Nat.nth Reaches0 (n - 1)`, so `a 1 = 0` and `a 2 = 10`;
  `a 0` is a junk value and is not used.
-/

namespace OMA.S_oeis_a361337

/-- `P` is the product of the two parts of a legal split of `N`: the suffix has `j ≥ 1` digits, the prefix
is nonempty (`10 ^ j ≤ N`), and the suffix has no leading zero unless it is the single digit `0`
(`j = 1` or `10 ^ (j - 1) ≤ N % 10 ^ j`); then `P = (N / 10 ^ j) * (N % 10 ^ j)`. -/
def SplitProd (N P : ℕ) : Prop :=
  ∃ j : ℕ, 1 ≤ j ∧ 10 ^ j ≤ N ∧ (j = 1 ∨ 10 ^ (j - 1) ≤ N % 10 ^ j) ∧
    P = N / 10 ^ j * (N % 10 ^ j)

/-- `N` reaches `0` after a finite (possibly empty) series of split-and-multiply operations. -/
def Reaches0 (N : ℕ) : Prop :=
  Relation.ReflTransGen SplitProd N 0

/-- The `n`-th term of A361337 (offset 1): `a 1 = 0`, `a 2 = 10`, `a 3 = 20`, ... -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth Reaches0 (n - 1)

/-- Hasler's conjecture: `a(2894 + k) = 3112 + k` for all `k ≥ 0`. -/
theorem main : ∀ k : ℕ, a (2894 + k) = 3112 + k := by
  sorry

end OMA.S_oeis_a361337
