import Mathlib

/-!
# A396081: Primes p such that A381466(2p) < 2p

Source: https://oeis.org/A396081 (see also https://oeis.org/A381466)
Credit: @gblacher2

A381466: a(0) = 4; for n > 0, a(n) = a(n-1) + n if g = 1, otherwise a(n) = n/g,
where g = gcd(a(n-1), n).
A396081 (Sam Chapman): primes p such that A381466(2p) < 2p.
Data: 2, 7, 19, 29, 31, 47, 59, 73, 79, 107, 127, 167, 191, 227, ...
Conjecture (in the entry): "We conjecture that this is an infinite sequence."

Checks: with the definition below, A381466(0..25) = 4, 5, 7, 10, 2, 7, 13, 20, 2, 11, 21, 32,
3, 16, 7, 22, 8, 25, 43, 62, 10, 31, 53, 76, 6, 31 (as in A381466), and the primes p < 1200 with
A381466(2p) < 2p are exactly the 53 listed terms of A396081 (checked numerically).
-/

namespace OMA.S_oeis_a396081

/-- A381466: `a 0 = 4`; for `n > 0`, `a n = a (n-1) + n` if `gcd (a (n-1)) n = 1`,
otherwise `a n = n / gcd (a (n-1)) n`. -/
def a381466 : ℕ → ℕ
  | 0 => 4
  | n + 1 =>
    let g := Nat.gcd (a381466 n) (n + 1)
    if g = 1 then a381466 n + (n + 1) else (n + 1) / g

/-- There are infinitely many primes `p` with `A381466(2p) < 2p`. -/
theorem main : {p : ℕ | p.Prime ∧ a381466 (2 * p) < 2 * p}.Infinite := by
  sorry

end OMA.S_oeis_a396081
