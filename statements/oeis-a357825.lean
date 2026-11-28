import Mathlib

/-!
# A357825: Total number of n-tuples of semi-Dyck paths from (0,0) to (n,n-2*j) for j = 0..floor(n/2)

Source: https://oeis.org/A357825

A semi-Dyck path is a lattice path with steps `(1,1)` and `(1,-1)` that starts at `(0,0)` and never
goes below the x-axis. Write `b(x,y)` for the number of such paths that end at `(x,y)`. The entry
(Alois P. Heinz, Oct 14 2022, offset 0) defines

  `a(n) = Sum_{j = 0..floor(n/2)} b(n, n-2*j)^n`,

with the Maple program

  `b:= proc(x, y) option remember; if y<0 or y>x then 0 elif x=0 then 1 else add(b(x-1, y+j), j=[-1, 1]) fi end:`
  `a:= n-> add(b(n, n-2*j)^n, j=0..n/2):`

The first terms are `1, 1, 2, 9, 98, 4150, 562692, 211106945, 404883552194, ...`.

The entry makes one conjectural statement, stated here:

  Conjecture: the supercongruence `a(2*p-1) == 1 (mod p^3)` holds for all primes `p >= 5`
  (checked up to `p = 101`). - Peter Bala, Mar 20 2023

The other formula lines (`a(n) = A357824(n,n)`, `a(n) = Sum_{j} A008315(n,j)^n`, the parity
criterion, Kotesovec's asymptotics) are given without the word conjecture and are not part of the
target.

Formalized: `b x y` is the recursion of the Maple program, literally, with `x : ℕ` and `y : ℤ` (the
program calls `b(x-1, -1)`, which is `0`): `b 0 y` is `1` for `y = 0` and `0` otherwise; `b (x+1) y`
is `0` when `y < 0` or `y > x + 1`, and `b x (y-1) + b x (y+1)` otherwise. `a n` is an integer, the
sum over `j` in `Finset.range (n / 2 + 1)`, that is `0 <= j <= floor(n/2)` (natural-number division,
which is the floor), of `b n (n - 2*j)` to the power `n`, where `n - 2*j` is computed in `ℤ` (and is
nonnegative in that range). No closed formula is used in the definition; by the reflection principle
`b(n, n-2*j) = binomial(n,j) - binomial(n,j-1)`, the formula line with A008315. The index `2*p - 1`
is a natural-number subtraction, harmless because `p >= 5`. The congruence
`a(2*p-1) == 1 (mod p^3)` is written as divisibility of `a (2*p-1) - 1` by `p^3` in the integers.
The range is every prime `p` with `5 <= p`. (For `p = 3` the congruence fails: `a(5) - 1 = 4149 =
3^2 * 461`.)
-/

namespace OMA.S_oeis_a357825

/-- `b x y`: the number of semi-Dyck paths (steps `(1,1)` and `(1,-1)`, never below the x-axis)
from `(0,0)` to `(x,y)`, by the recursion of the Maple program of the entry. -/
def b : ℕ → ℤ → ℕ
  | 0, y => if y = 0 then 1 else 0
  | x + 1, y => if y < 0 ∨ ((x : ℤ) + 1) < y then 0 else b x (y - 1) + b x (y + 1)

/-- A357825: `a(n) = Sum_{j=0..floor(n/2)} b(n, n-2*j)^n`. -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n / 2 + 1), ((b n ((n : ℤ) - 2 * (j : ℤ)) : ℕ) : ℤ) ^ n

/-- Bala's conjectured supercongruence: `a(2*p-1) == 1 (mod p^3)` for every prime `p >= 5`. -/
theorem main : ∀ p : ℕ, p.Prime → 5 ≤ p → ((p : ℤ) ^ 3) ∣ (a (2 * p - 1) - 1) := by
  sorry

end OMA.S_oeis_a357825
