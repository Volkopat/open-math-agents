import Mathlib

/-!
# A217319: Numbers with binary representation ending in 4*k+2 or 4*k+3 zeros

Source: https://oeis.org/A217319 (see also https://oeis.org/A171949)
Credit: @ivillar

Status: open conjecture in the OEIS entry (Vladimir Shevelev, Mar 18 2013):
  Conjecture. For n>=1, a(n) = A171949(n+1).
The same conjecture is recorded in A171949. A171949 links A. S. Fraenkel's paper on the games
Mark-t (The vile, dopey, evil and odious game players, Discrete Math. 312 (2012) 42-46).

A217319 (offset 1): 4, 8, 12, 20, 24, 28, 36, 40, 44, 52, 56, 60, 64, ..., the positive integers
whose binary representation ends in 4k+2 or 4k+3 zeros, i.e. whose exponent of 2 is 2 or 3
modulo 4.
A171949 (offset 1): 0, 4, 8, 12, 20, 24, 28, 36, ..., the P-positions of the game Mark-4. From
a position n, a move goes to n - 1, n - 2 or n - 3 (not below 0) or to floor(n/4) (when this is
smaller than n); the player who cannot move loses. A P-position is one from which every move
leads to an N-position, so 0, which has no move, is a P-position.

Formalization notes.
* The number of trailing zeros of the binary representation of n > 0 is the exponent of 2 in n,
  `n.factorization 2`.
* `IsP` is defined by well-founded recursion on the position. With these definitions the first
  400 terms of both sequences agree with the data of the two entries.
* Both sequences are increasing enumerations, written with `Nat.nth` (0-based): A217319(n) is
  `Nat.nth InA217319 (n - 1)` and A171949(n + 1) is `Nat.nth IsP n`.
-/

namespace OMA.S_oeis_a217319

/-- Positive integers whose binary representation ends in 4k+2 or 4k+3 zeros. -/
def InA217319 (n : ℕ) : Prop :=
  0 < n ∧ (n.factorization 2 % 4 = 2 ∨ n.factorization 2 % 4 = 3)

/-- The P-positions of Mark-4: every move (to n - 1, n - 2, n - 3, or to floor(n/4) when this is
smaller than n) leads to a position that is not a P-position. -/
def IsP (n : ℕ) : Prop :=
  ∀ m : ℕ, (h : m < n) → (n ≤ m + 3 ∨ m = n / 4) → ¬ IsP m
termination_by n

/-- Shevelev's conjecture: for n ≥ 1, A217319(n) = A171949(n+1). -/
theorem main : ∀ n : ℕ, 1 ≤ n → Nat.nth InA217319 (n - 1) = Nat.nth IsP n := by
  sorry

end OMA.S_oeis_a217319
