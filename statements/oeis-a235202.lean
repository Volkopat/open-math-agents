import Mathlib

/-!
# A235202: numbers in an alternating binary-then-quaternary base, read in base 4

Source: https://oeis.org/A235202
Credit: @avivorly

A235202: Numbers written in an alternating binary-then-quaternary base.

A126001: A106486-encodings of nonnegative combinatorial games, i.e., games whose value is >= 0.

Conjecture (comment in A235202): This sequence interpreted as quaternary (base 4) numbers gives A126001 (hence a
simplified scheme for computing that sequence).

Conventions:
- A235202 has offset 1. Its comments describe a mixed-radix representation with digit bounds `(1, 3, 1, 3, ...)`
  (A010684), the places reading from the right having values `(1, 2, 8, 16, 64, 128, ...)`: the radices of the places,
  from the right, are `2, 4, 2, 4, ...`. Its term `a(n)` is `n` in this mixed radix with the digits shown as a decimal
  numeral (`a(15) = 131` since `15 = 1*1 + 3*2 + 1*8`; the entry's BASIC counter prints the representations of
  `1, 2, 3, ...`). `digits24 n` is that digit list of `n`, least significant first, with no leading zero digit, and
  `A235202 n` is its decimal numeral.
- `quat n` is `A235202 n` interpreted as a quaternary numeral. Every decimal digit of `A235202 n` is a mixed-radix
  digit, hence in `0..3`, so the decimal digits of `A235202 n` are exactly `digits24 n` and their base-4 value is
  `Nat.ofDigits 4 (digits24 n)`.
- A126001 has offset 1 and is taken as defined by its PARI program (the program that wrote its b-file):
  `A320006(n) = 1` iff `A320007(r) = 1` for every `r` such that bit `2*r+1` of `n` is set (so `A320006(0) = 1`), and
  `A320007(n) = 1` iff `A320006(s) = 1` for some `s` such that bit `2*s` of `n` is set (so `A320007(0) = 0`): the PARI
  loop in `A320006` walks through the bits `1, 3, 5, ...` of `n` (`m = n >> 1`, then `m >>= 2`) with `r` counting them,
  and the loop in `A320007` through the bits `0, 2, 4, ...` with `s` counting them. A126001 lists the `n` with
  `A320006(n) = 1` in increasing order. `geZero n` is `A320006(n) = 1` and `zeroLf n` is `A320007(n) = 1` (in game
  terms: the encoded game is `≥ 0`, resp. Left wins it moving first). Both are defined by well-founded recursion on `n`:
  a set bit `2*r+1` or `2*s` of `n` gives `2^(2*r+1) ≤ n` or `2^(2*s) ≤ n`, hence `r < n` or `s < n`, so letting `r`
  and `s` range over `Fin n` loses nothing, and the two definitions are the two PARI loops read as a universal and an
  existential statement over the set bits.
- Both sequences increase: `quat` is strictly increasing (mixed-radix numerals with no leading zero order by length,
  then lexicographically, and so do their base-4 readings, the digits being `< 4`), with `quat 1 = 1`, and A126001 is
  listed in increasing order, starting with `A126001(1) = 0`. So the conjecture, read as `A126001(1) = 0` and
  `A126001(n + 1) = quat n` for `n ≥ 1` (as the data show: `quat 1 = 1`, `quat 2 = 4`, `quat 3 = 5`, ...), is
  equivalent to the equality of sets `{m | geZero m} = {0} ∪ {quat n | n ≥ 1}`, which is `main`.
-/

namespace OMA.S_oeis_a235202

mutual

/-- `digits24 n`: the digits of `n`, least significant first and with no leading zero digit, in the mixed radix
whose places, from the right, have the radices `2, 4, 2, 4, ...` (a binary place first). -/
def digits24 (n : ℕ) : List ℕ :=
  if n = 0 then [] else n % 2 :: digits42 (n / 2)
termination_by n
decreasing_by all_goals omega

/-- `digits42 n`: the same with the radices `4, 2, 4, 2, ...` (a quaternary place first). -/
def digits42 (n : ℕ) : List ℕ :=
  if n = 0 then [] else n % 4 :: digits24 (n / 4)
termination_by n
decreasing_by all_goals omega

end

/-- `A235202 n`: `n` written in the alternating binary-then-quaternary base, its digits read as a decimal numeral. -/
def A235202 (n : ℕ) : ℕ := Nat.ofDigits 10 (digits24 n)

/-- `quat n`: `A235202 n` interpreted as a quaternary (base 4) numeral. -/
def quat (n : ℕ) : ℕ := Nat.ofDigits 4 (digits24 n)

mutual

/-- `geZero n` (`A320006(n) = 1`): `zeroLf r` holds for every `r` such that bit `2*r+1` of `n` is set. -/
def geZero (n : ℕ) : Prop :=
  ∀ r : Fin n, n.testBit (2 * (r : ℕ) + 1) = true → zeroLf (r : ℕ)
termination_by n
decreasing_by all_goals exact Fin.isLt _

/-- `zeroLf n` (`A320007(n) = 1`): `geZero s` holds for some `s` such that bit `2*s` of `n` is set. -/
def zeroLf (n : ℕ) : Prop :=
  ∃ s : Fin n, n.testBit (2 * (s : ℕ)) = true ∧ geZero (s : ℕ)
termination_by n
decreasing_by all_goals exact Fin.isLt _

end

theorem main : ∀ m : ℕ, geZero m ↔ (m = 0 ∨ ∃ n : ℕ, 1 ≤ n ∧ quat n = m) := by
  sorry

end OMA.S_oeis_a235202
