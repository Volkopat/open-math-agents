import Mathlib

/-!
# A264596: position of `n` among `0, ..., n` sorted by their reversed binary words

Source: https://oeis.org/A264596
Credit: @avivorly

A264596 (offset 0): Let `S_n` be the list of the first `n` nonnegative numbers written in binary, with least
significant bits on the left, and sorted into lexicographic order; `a(n)` = position of `n` in `S_n`, starting
indexing at 0.

A293290 (offset 0): `a(n) = Product_{1 <= j <= k <= n} (k^2 + j^2)`.
A007814: the 2-adic valuation of `n` (the exponent of the highest power of 2 dividing `n`).

Conjecture (Velin Yanev, Sep 12 2017, in the entry): `a(n) = n*(n + 3)/2 - A007814(A293290(n))` for `n > 0`.

Conventions:
- `binLSB n` is the binary word of `n` with the least significant bit on the left, as a list of digits `0`, `1`:
  `Nat.digits 2 n` (little-endian) for `n ≥ 1`, and `0` is the one-digit word `[0]`, as in the entry's examples
  (`S_1 = [0, 1]`) and its Python program. (Writing `0` as the empty word `[]` gives the same `a`: for `n ≥ 1` both
  `[]` and `[0]` are below the word of `n`, and for `n = 0` no word is below.)
- Lexicographic order is `List.Lex (· < ·)`: words are compared at the first position where they differ, and a
  proper prefix is smaller; so `0 < 001 < 01 < 011 < 1 < 101 < 11 < 111`, as in the example `S_7`.
- `S_n` is read as the list of the numbers `0, 1, ..., n`: `n` must be in `S_n`, the examples list `S_0 = [0]`,
  `S_1 = [0, 1]`, ..., the data has `a(2^k) = 1` and `a(2^k - 1) = 2^k - 1`, and the Python program sorts
  `range(n+1)`.
- Distinct numbers have distinct words, so the position (from 0) of `n` in the sorted list `S_n` is the number of
  `m ≤ n` whose word is lexicographically smaller than the word of `n`; `A264596 n` is defined as that count.
- A293290 is the product over `1 ≤ k ≤ n` and `1 ≤ j ≤ k` (the empty product `1` at `n = 0`); A007814 is
  `padicValNat 2`.
- The identity is read in `ℤ`, so there is no truncated subtraction; `n * (n + 3)` is even, so `/ 2` is exact.
-/

namespace OMA.S_oeis_a264596

/-- The binary word of `n` with the least significant bit first, as a list of digits; `0` is written `[0]`. -/
def binLSB (n : ℕ) : List ℕ := if n = 0 then [0] else Nat.digits 2 n

/-- `A264596 n`: the position (from 0) of `n` in the list `S_n` of `0, 1, ..., n` sorted lexicographically by their
words `binLSB`, that is, the number of `m ≤ n` whose word is lexicographically smaller than the word of `n`. -/
def A264596 (n : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter (fun m => List.Lex (· < ·) (binLSB m) (binLSB n))).card

/-- `A293290 n = ∏_{1 ≤ j ≤ k ≤ n} (k ^ 2 + j ^ 2)`. -/
def A293290 (n : ℕ) : ℕ :=
  ∏ k ∈ Finset.Icc 1 n, ∏ j ∈ Finset.Icc 1 k, (k ^ 2 + j ^ 2)

/-- `A007814 n`: the 2-adic valuation of `n`. -/
def A007814 (n : ℕ) : ℕ := padicValNat 2 n

theorem main :
    ∀ n : ℕ, 0 < n →
      (A264596 n : ℤ) = (n : ℤ) * ((n : ℤ) + 3) / 2 - (A007814 (A293290 n) : ℤ) := by
  sorry

end OMA.S_oeis_a264596
