import Mathlib

/-!
# A394621: Numbers k of the form k = p1 + p2 = x^2 + y^2 + p1^2, where p1 and p2 are primes, x, y are integers.

Source: https://oeis.org/A394621
Credit: @agchua

Comments of A394621 (the entry is by Bill McEachen, Mar 26 2026):
  Conjecture: odd a(n)-2 belong to A079739.
  Conjecture: odd a(n)-4 belong to A001481.
  Conjecture: even a(n) belong to A145979.
Offset 1, data 4, 5, 9, 10, 13, 14, 21, 22, 26, ... The terms are the natural numbers k with
k = p1 + p2 and k = x^2 + y^2 + p1^2 for some primes p1, p2 and some integers x, y; the three
conjectures are stated for every such k (an odd term is at least 5, so k - 2 and k - 4 are the
true differences). The other sequences, from their name lines:
  A079739: Primes of the form x^2 + y^2 + 2 (x,y nonnegative).
  A001481: Numbers that are the sum of 2 squares (0 included; squares of natural numbers).
  A145979: a(n) = (2*n + 4)/gcd(n,4), offset 0; belonging to it means being one of its values.
-/

namespace OMA.S_oeis_a394621

/-- k is a term of A394621: k = p1 + p2 = x^2 + y^2 + p1^2 with p1, p2 prime and x, y integers. -/
def IsTerm (k : ℕ) : Prop :=
  ∃ p1 p2 : ℕ, p1.Prime ∧ p2.Prime ∧ k = p1 + p2 ∧
    ∃ x y : ℤ, (k : ℤ) = x ^ 2 + y ^ 2 + (p1 : ℤ) ^ 2

/-- m is a term of A079739: a prime of the form x^2 + y^2 + 2 with x, y nonnegative. -/
def InA079739 (m : ℕ) : Prop := m.Prime ∧ ∃ x y : ℕ, m = x ^ 2 + y ^ 2 + 2

/-- m is a term of A001481: a sum of two squares. -/
def InA001481 (m : ℕ) : Prop := ∃ x y : ℕ, m = x ^ 2 + y ^ 2

/-- A145979(n) = (2n + 4)/gcd(n, 4), offset 0. -/
def A145979 (n : ℕ) : ℕ := (2 * n + 4) / Nat.gcd n 4

/-- The three conjectures: for every term k, if k is odd then k - 2 is in A079739 and k - 4 is
in A001481, and if k is even then k is a value of A145979. -/
theorem main :
    (∀ k : ℕ, IsTerm k → Odd k → InA079739 (k - 2)) ∧
    (∀ k : ℕ, IsTerm k → Odd k → InA001481 (k - 4)) ∧
    (∀ k : ℕ, IsTerm k → Even k → ∃ n : ℕ, A145979 n = k) := by
  sorry

end OMA.S_oeis_a394621
