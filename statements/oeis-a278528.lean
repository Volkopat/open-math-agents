import Mathlib

/-!
# A278528: a(n) = number of the round in which n is removed in the Flavius sieve, 0 if it is never removed (when n is one of the terms of A000960).

Source: https://oeis.org/A278528
Credit: @esracummings31-blip

Conjecture (OEIS, Mikhail Kurkov): a(n) = [C > 0] * C where we start with A := n,
B := n - 1, C, m := 0 and until A = B consecutively apply m := m + 1, C := A - B,
A := abs(A - m - (A mod m)), B := abs(B - m - (B mod m)).

Conventions.
* Flavius sieve (A000960): start with 1, 2, 3, ...; in round `m` (m = 1, 2, ...) delete every
  `(m+1)`-st term of the remaining sequence (the terms at positions m+1, 2(m+1), ...).
  Whether `n` survives a round depends only on the surviving terms `≤ n` (positions are counted
  from the left), so we run the sieve on the initial segment `[1, ..., n]`.
  `survivors n j` is the list of surviving terms `≤ n` after `j` rounds.
* `a n` is the round `m ≥ 1` with `n` present before round `m` and absent after it,
  and `0` if there is no such round.
* `alg x m` is the value of the variable (A or B) after `m` passes of the loop started from
  `x`; `mod` is the usual nonnegative remainder. The loop stops at the first `M` with
  `A = B` (note `A ≠ B` at the start), and then `C = A - B` computed at the start of pass `M`,
  i.e. `C = alg n (M-1) - alg (n-1) (M-1)`. The conjecture includes that the loop stops.
-/

namespace OMA.S_oeis_a278528

/-- Delete the elements at positions `c, c+1, ...` (counted from the current counter `c`)
that are multiples of `k`. With `c = 1` this deletes every `k`-th element. -/
def dropEvery (k : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | c, x :: xs => if c % k = 0 then dropEvery k (c + 1) xs else x :: dropEvery k (c + 1) xs

/-- Terms `≤ n` remaining after `j` rounds of the Flavius sieve. -/
def survivors (n : ℕ) : ℕ → List ℕ
  | 0 => List.range' 1 n
  | j + 1 => dropEvery (j + 2) 1 (survivors n j)

/-- `n` is removed in round `m`. -/
def RemovedIn (n m : ℕ) : Prop := 1 ≤ m ∧ n ∈ survivors n (m - 1) ∧ n ∉ survivors n m

open Classical in
/-- A278528. -/
noncomputable def a (n : ℕ) : ℕ := if h : ∃ m, RemovedIn n m then Nat.find h else 0

/-- The loop variable after `m` passes, starting from `x`. -/
def alg (x : ℤ) : ℕ → ℤ
  | 0 => x
  | m + 1 => |alg x m - (m + 1) - alg x m % (m + 1)|

theorem main : ∀ n : ℕ, 1 ≤ n →
    ∃ M : ℕ, 1 ≤ M ∧ alg n M = alg ((n : ℤ) - 1) M ∧
      (∀ m < M, alg n m ≠ alg ((n : ℤ) - 1) m) ∧
      (a n : ℤ) = max (alg n (M - 1) - alg ((n : ℤ) - 1) (M - 1)) 0 := by
  sorry

end OMA.S_oeis_a278528
