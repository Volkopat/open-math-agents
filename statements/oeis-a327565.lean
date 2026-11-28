import Mathlib

/-!
# A327565: transfers of marbles between two sets until the first repetition

Source: https://oeis.org/A327565
Credit: @avivorly

A327565 is the number of transfers of marbles between two sets until the first repetition. The entry says: there are
initially `n` marbles in both sets. In the first turn, half of the marbles of set A are transferred to set B, rounding
to the upper integer when halving. In the second turn, half of the marbles of set B are transferred back to set A,
following the same rule. The game goes on back and forth until we reach a distribution already encountered. `a(n)` is
then the number of steps until the first repetition occurs. (Offset 1; data `2, 3, 4, 3, 5, 4, 4, 5, 6, 4, ...`;
example: for `n = 3` the distributions are `(3;3), (1;5), (4;2), (2;4), (4;2)`, so `a(3) = 4`.)

Conjecture (in the entry): for `m > 2`, the first occurrence of `a(n) = m` is for `n = 2^(m-3) + 1`.

Conventions:
- A distribution is the pair `(A, B)` of the numbers of marbles in sets A and B. `transfer k` is the move made when
  `k` transfers have already been made: if `k` is even (an odd-numbered turn) A gives `⌈A/2⌉ = (A + 1) / 2` marbles to
  B, and if `k` is odd (an even-numbered turn) B gives `⌈B/2⌉ = (B + 1) / 2` marbles to A.
- `state n k` is the distribution after `k` transfers, starting from `state n 0 = (n, n)`; the initial distribution
  counts as encountered (as in the entry's example for `n = 3`, and in its PARI program).
- `a n` is the least `k ≥ 1` such that `state n k = state n j` for some `j < k`. As `A + B = 2n` throughout, there are
  at most `2n + 1` distributions, so a repetition occurs within `2n + 1` transfers and the set below is nonempty for
  every `n`; Lean's convention `sInf ∅ = 0` never applies.
- The first occurrence of `a(n) = m` is `N` when `a N = m` and `a n ≠ m` for every `n` with `1 ≤ n < N` (the entry's
  offset is 1). `m - 3` is exact since `m > 2`.
- The entry's formula line says: For m > 1, first occurrence of a(n) = m is for n = A094373(m-1) (conjectured).
  A094373 has offset 0 and terms `1, 2, 3, 5, 9, 17, 33, ...`, i.e. `A094373(0) = 1` and `A094373(k) = 2^(k-1) + 1`
  for `k ≥ 1`. The entry's own comment lists the first occurrences of `a(n) = m > 1` as `1, 2, 3, 5, 9, 17, 33, ...`,
  which is `A094373(m-2)`; read literally with `m-1` the line would claim that the first `2` is at `n = 2`, while
  `a(1) = 2`. The formula line is therefore an index slip for `A094373(m-2)`, which for `m > 2` is the same claim as
  the conjecture above (and for `m = 2` is the fact `a(1) = 2`); the conjecture is stated in that form.
-/

namespace OMA.S_oeis_a327565

/-- One transfer, when `k` transfers have already been made, applied to the distribution `s = (A, B)`: for even `k`
set A gives half of its marbles, rounded up, to set B; for odd `k` set B gives half of its marbles, rounded up, to
set A. -/
def transfer (k : ℕ) (s : ℕ × ℕ) : ℕ × ℕ :=
  if k % 2 = 0 then (s.1 - (s.1 + 1) / 2, s.2 + (s.1 + 1) / 2)
  else (s.1 + (s.2 + 1) / 2, s.2 - (s.2 + 1) / 2)

/-- The distribution `(A, B)` after `k` transfers, starting from `n` marbles in both sets. -/
def state (n : ℕ) : ℕ → ℕ × ℕ
  | 0 => (n, n)
  | k + 1 => transfer k (state n k)

/-- `a n` (A327565): the number of transfers until the first repetition, i.e. the least `k ≥ 1` such that the
distribution after `k` transfers was already encountered after some `j < k` transfers. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ ∃ j < k, state n k = state n j}

theorem main :
    ∀ m : ℕ, 2 < m →
      a (2 ^ (m - 3) + 1) = m ∧ ∀ n : ℕ, 1 ≤ n → n < 2 ^ (m - 3) + 1 → a n ≠ m := by
  sorry

end OMA.S_oeis_a327565
