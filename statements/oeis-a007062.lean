import Mathlib

/-!
# A007062: limit of iterated block reversals, compared with A057030

Source: https://oeis.org/A007062
Credit: @avivorly

A007062: Let P(n) of a sequence s(1),s(2),s(3),... be obtained by leaving s(1),...,s(n) fixed and reversing every n
consecutive terms thereafter; apply P(2) to 1,2,3,... to get PS(2), then apply P(3) to PS(2) to get PS(3), then apply
P(4) to PS(3), etc. This sequence is the limit of PS(n).

A057030: Let P(n) of a sequence s(1),s(2),s(3),... be obtained by leaving s(1),...,s(n-1) fixed and reversing every n
consecutive terms thereafter; apply P(2) to 1,2,3,... to get PS(2), then apply P(3) to PS(2) to get PS(3), then apply
P(4) to PS(3), etc. The limit of PS(n) is A057030.

Conjecture (Mikhail Kurkov, in A007062): a(n) = A057030(n-1) + 1 for n > 1 with a(1) = 1.
(The same conjecture is stated in A057030 as: a(n) = A007062(n+1) - 1 for n > 0.)

Conventions:
- A sequence `s(1), s(2), ...` is a function `s : ℕ → ℕ`, 1-indexed as in the entries; index `0` is unused (both maps
  below fix it, and it stays `0`).
- `PA n s` is P(n) of A007062: positions `1, ..., n` are fixed; the positions after them are cut into the consecutive
  blocks `n + q*n + 1, ..., n + q*n + n` (`q = 0, 1, 2, ...`), and each block is reversed: position `n + q*n + 1 + r`
  (`0 ≤ r < n`) takes the term at position `n + q*n + (n - r)`.
- `PB n s` is P(n) of A057030: positions `1, ..., n - 1` are fixed; the blocks are `n - 1 + q*n + 1, ..., n - 1 + q*n + n`,
  each reversed: position `n + q*n + r` (`0 ≤ r < n`) takes the term at position `n - 1 + q*n + (n - r)`.
- `PSA m` is PS(m) of A007062: `PSA 1` is `1, 2, 3, ...` (the identity) and `PSA m = PA m (PSA (m - 1))` for `m ≥ 2`
  (`PSA 0` is also the identity and is not used); `PSB` is the same for A057030 with `PB`.
- The limit: P(m) of A007062 fixes positions `1, ..., m`, so `PSA m j = PSA j j` for all `m ≥ j`; P(m) of A057030 fixes
  positions `1, ..., m - 1`, so `PSB m j = PSB j j` for all `m ≥ j`. So the limit of PS(m) at position `j ≥ 1` is
  `a007062 j := PSA j j`, and likewise `a057030 j := PSB j j` (offset 1 for both, as in their %O lines).
-/

namespace OMA.S_oeis_a007062

/-- P(n) of A007062: keep positions `1..n`, then reverse each consecutive block of `n` positions. -/
def PA (n : ℕ) (s : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i ≤ n then s i else s (n + n * ((i - n - 1) / n) + (n - (i - n - 1) % n))

/-- P(n) of A057030: keep positions `1..n-1`, then reverse each consecutive block of `n` positions. -/
def PB (n : ℕ) (s : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < n then s i else s (n - 1 + n * ((i - n) / n) + (n - (i - n) % n))

/-- PS(m) of A007062: `PSA 1 = 1, 2, 3, ...` and `PSA m = PA m (PSA (m - 1))` for `m ≥ 2`. -/
def PSA : ℕ → ℕ → ℕ
  | 0 => fun i => i
  | 1 => fun i => i
  | m + 2 => PA (m + 2) (PSA (m + 1))

/-- PS(m) of A057030: `PSB 1 = 1, 2, 3, ...` and `PSB m = PB m (PSB (m - 1))` for `m ≥ 2`. -/
def PSB : ℕ → ℕ → ℕ
  | 0 => fun i => i
  | 1 => fun i => i
  | m + 2 => PB (m + 2) (PSB (m + 1))

/-- A007062(n), the limit of PS(m) at position `n` (reached from `m = n` on). -/
def a007062 (n : ℕ) : ℕ := PSA n n

/-- A057030(n), the limit of PS(m) at position `n` (reached from `m = n` on). -/
def a057030 (n : ℕ) : ℕ := PSB n n

theorem main : a007062 1 = 1 ∧ ∀ n : ℕ, 2 ≤ n → a007062 n = a057030 (n - 1) + 1 := by
  sorry

end OMA.S_oeis_a007062
