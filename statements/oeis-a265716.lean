import Mathlib

/-!
# A265716: n IMPL 2n and McEachen's bitwise-or formula

Source: https://oeis.org/A265716
Credit: @ivillar

A265716(n) = n IMPL (2n), where IMPL is the bitwise logical implication (Reinhard Zumkeller).
The Mathematica program in the entry defines `IMPL(n, k) = 0` for `n = 0` and otherwise
`BitOr(2^L - 1 - n, k)`, where `L` is the number of binary digits of `k`. Bill McEachen
conjectured (Dec 13 2021) that a(n) = bitor(A003817(n) - n, 2n).

Formalization notes:
* For `k ≥ 1` the number of binary digits of `k` is `Nat.size k`; only `k = 2n ≥ 2` is used.
* A003817 (a(0) = 0, a(n) = a(n-1) OR n) is used in its closed form from that entry:
  a(n) = 2^k - 1 when 2^(k-1) ≤ n < 2^k, i.e. `2 ^ Nat.size n - 1` (also 0 at n = 0).
* Bitwise OR on natural numbers is `|||`.
-/

namespace OMA.S_oeis_a265716

/-- Bitwise implication `n IMPL k`, following the Mathematica program of A265716. -/
def impl (n k : ℕ) : ℕ := if n = 0 then 0 else (2 ^ Nat.size k - 1 - n) ||| k

/-- A265716: `a(n) = n IMPL (2n)`. -/
def a (n : ℕ) : ℕ := impl n (2 * n)

/-- A003817 in closed form: `2^k - 1` for `2^(k-1) ≤ n < 2^k`, and `0` at `n = 0`. -/
def A003817 (n : ℕ) : ℕ := 2 ^ Nat.size n - 1

/-- McEachen's conjecture: `a(n) = bitor(A003817(n) - n, 2n)` for all `n ≥ 0`. -/
theorem main : ∀ n : ℕ, a n = (A003817 n - n) ||| (2 * n) := by
  sorry

end OMA.S_oeis_a265716
