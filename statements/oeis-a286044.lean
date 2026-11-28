import Mathlib

/-!
# A286044: {011->0}-transform of the Thue-Morse word A010060.

Source: https://oeis.org/A286044
Credit: @rickmanelius

Conjecture (Velin Yanev, Feb 16 2026): a(n) = b(b(n - 2)) - b(b(n - 3)) for n > 3, where b is
A003160.

Formalization notes:
* The Thue-Morse word A010060 has letters t(0), t(1), t(2), ... with t(i) the binary digit sum of
  i taken mod 2 (the formula a(n) = A000120(n) mod 2 of A010060), here `tm i` with Mathlib's
  `Nat.digits 2`. `tmWord L` is the list of its first L letters t(0), ..., t(L-1). It begins
  0110100110010110100101100..., as in the example of the entry.
* The {011->0}-transform replaces each occurrence of 011 by 0, scanning from left to right as the
  StringReplace of the entry program does (`rep011`). Two occurrences of 011 never overlap.
  Whether a letter starts an occurrence depends only on the two letters after it, so on the first
  L letters of the Thue-Morse word every output letter except possibly the last one is a letter of
  the transform of the whole word (the only possible difference is a final letter 1 of the window
  that, in the whole word, belongs to an occurrence of 011). Each output letter uses at most three
  input letters, so the transform of the first 3n+3 letters has at least n+1 letters, and `a n`
  reads letter n of the transform there (counting from 1, offset 1). The values a(1), a(2), ... are
  0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 1, ..., matching the data.
* A003160 (`b`, offset 1) is given by b(1) = b(2) = 1 and b(n) = n - b(b(n-1)) - b(b(n-2)) for
  n ≥ 3. Every term satisfies b(m) ≤ m (b(1) = b(2) = 1, and for m ≥ 3 the recursion subtracts
  from m), so the definition below writes b(min (b m) m) for b(b(m)): the min changes no value and
  only makes the recursion visibly decreasing. The subtraction is the one of the natural numbers;
  it never truncates, since every term of A003160 is positive (the recursion gives
  n - b(b(n-1)) - b(b(n-2)) ≥ 1, checked for n ≤ 40000). The value of `b 0` is a placeholder that
  the conjecture never reads (for n > 3 it reads b only at positive arguments). The values b(1),
  b(2), ... are 1, 1, 1, 2, 3, 4, 4, 4, 5, 5, 5, 6, 6, 6, 7, 8, 9, ..., matching the data of
  A003160.
* The conjecture is stated for n > 3, as in the entry, with the difference b(b(n-2)) - b(b(n-3))
  computed in the integers.
-/

namespace OMA.S_oeis_a286044

/-- The Thue-Morse word A010060: t(i) = binary digit sum of i, mod 2. -/
def tm (i : ℕ) : ℕ := (Nat.digits 2 i).sum % 2

/-- The first L letters t(0), ..., t(L-1) of the Thue-Morse word. -/
def tmWord (L : ℕ) : List ℕ := (List.range L).map tm

/-- Replace each 011 by 0, scanning from left to right. -/
def rep011 : List ℕ → List ℕ
  | 0 :: 1 :: 1 :: w => 0 :: rep011 w
  | c :: w => c :: rep011 w
  | [] => []

/-- A286044(n) for n ≥ 1: letter n, counting from 1, of the {011->0}-transform of the Thue-Morse
word, read from the transform of its first 3n+3 letters. -/
def a (n : ℕ) : ℕ := (rep011 (tmWord (3 * n + 3))).getD (n - 1) 0

/-- A003160: b(1) = b(2) = 1, b(n) = n - b(b(n-1)) - b(b(n-2)) for n ≥ 3 (b(m) ≤ m, so the min
changes no value). -/
def b (n : ℕ) : ℕ :=
  if n ≤ 2 then 1
  else n - b (min (b (n - 1)) (n - 1)) - b (min (b (n - 2)) (n - 2))
termination_by n
decreasing_by all_goals omega

/-- Yanev's conjecture: a(n) = b(b(n-2)) - b(b(n-3)) for n > 3. -/
theorem main : ∀ n : ℕ, 3 < n → (a n : ℤ) = (b (b (n - 2)) : ℤ) - (b (b (n - 3)) : ℤ) := by
  sorry

end OMA.S_oeis_a286044
