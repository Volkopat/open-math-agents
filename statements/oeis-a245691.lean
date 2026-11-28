import Mathlib

/-!
# A245691: Irregular triangle of Collatz like iteration, x -> 3x, then repeat (x -> ceiling(x/2) if divisible by 3, otherwise x -> 3x) while x != 6.

Source: https://oeis.org/A245691

Comment in the entry (K. Spage, Aug 07 2014):

  It is conjectured that the number of steps for the trajectory to arrive at 6 is equal to the
  number of steps for the Collatz trajectory to arrive at 1 for the same starting value n (n>1),
  suggesting the length of the n-th row of the irregular array is given by A008908(n).

Translation notes (please check):
* Row n of the triangle (offset 1) is T(n,0) = n, T(n,1) = 3n (the entry says: starting with x
  the first step in this sequence is always to multiply by 3), and afterwards
  T(n,k+1) = step(T(n,k)), where step(x) = ceiling(x/2) if 3 divides x and 3x otherwise; the row
  stops the first time 6 is reached at a position k >= 1 (row 6 is 6, 18, 9, 5, 15, 8, 24, 12, 6,
  so the starting value itself does not count as an arrival). `T n k` below is the unrestricted
  trajectory; the row is its initial segment up to that first 6.
* ceiling(x/2) is written (x + 1) / 2 with natural-number division.
* The number of steps to arrive at 6 is the least k >= 1 with T(n,k) = 6; the number of steps of
  the Collatz trajectory to arrive at 1 is the least k with collatz^[k] n = 1 (for n > 1 this k
  is automatically >= 1). Since it is not known that either trajectory always arrives, the
  equality of the two step counts is stated as: for every k, k is the first arrival time of one
  trajectory if and only if it is the first arrival time of the other (in particular one
  trajectory arrives if and only if the other does).
* `collatz` is the usual map A006370: x/2 for even x, 3x+1 for odd x.
-/

namespace OMA.S_oeis_a245691

/-- The Collatz map A006370. -/
def collatz (x : ℕ) : ℕ := if x % 2 = 0 then x / 2 else 3 * x + 1

/-- The map of A245691: x -> ceiling(x/2) if x is divisible by 3, otherwise x -> 3x. -/
def step (x : ℕ) : ℕ := if x % 3 = 0 then (x + 1) / 2 else 3 * x

/-- The trajectory of A245691 started at n: n, 3n, step(3n), step(step(3n)), ... -/
def T (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => step^[k] (3 * n)

theorem main : ∀ n : ℕ, 1 < n → ∀ k : ℕ,
    (IsLeast {j : ℕ | 1 ≤ j ∧ T n j = 6} k ↔ IsLeast {j : ℕ | collatz^[j] n = 1} k) := by
  sorry

end OMA.S_oeis_a245691
