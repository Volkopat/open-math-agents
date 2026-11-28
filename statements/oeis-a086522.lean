import Mathlib

/-!
# A086522: Primes arising as the arithmetic mean of a pair of successive terms of A086519.

Source: https://oeis.org/A086522
Credit: @agchua

Comment of A086522 (the entry is by Amarnath Murthy, Jul 30 2003, corrected and extended by
David Wasserman, Mar 11 2005):
  Conjecture: every prime of the type 6k+1 is a member. Comment from Vim Wenders, May 27 2008:
  The conjecture is worng. For example 19 is missing..
A086519 (offset 1): a(1) = 3, and a(n) is the least prime not already used such that
(a(n)+a(n-1))/2 is prime; its terms begin 3, 7, 19, 43, 31, 103. The formula line of A086522
(David Wasserman, Mar 11 2005) gives A086522(n) = (A086519(n)+A086519(n+1))/2, offset 1. It is
not known that a next term of A086519 always exists; where none exists, the definition below gives
0 (sInf of the empty set), and the statement covers that case too.
The statement is the comment of Vim Wenders as printed: 19 is not a member, and so the conjecture
(every prime of the form 6k+1 is a member) is false.
-/

namespace OMA.S_oeis_a086522

/-- next l t: the least prime q, not in the list l, such that (q + t)/2 is a prime
(0 if there is none). -/
noncomputable def next (l : List ℕ) (t : ℕ) : ℕ :=
  sInf {q : ℕ | q.Prime ∧ q ∉ l ∧ ∃ r : ℕ, r.Prime ∧ q + t = 2 * r}

/-- pre n: the terms A086519(n+1), A086519(n), ..., A086519(1), the most recent first. -/
noncomputable def pre : ℕ → List ℕ
  | 0 => [3]
  | n + 1 => next (pre n) ((pre n).headD 0) :: pre n

/-- A086519(n) for n >= 1. -/
noncomputable def A086519 (n : ℕ) : ℕ := (pre (n - 1)).headD 0

/-- p is a member of A086522: a prime that is the arithmetic mean of two successive terms
A086519(n), A086519(n+1) with n >= 1. -/
def IsTerm (p : ℕ) : Prop := p.Prime ∧ ∃ n : ℕ, 1 ≤ n ∧ A086519 n + A086519 (n + 1) = 2 * p

/-- The comment: 19 is missing, so the conjecture that every prime of the form 6k+1 is a member
is wrong. -/
theorem main : ¬ IsTerm 19 ∧ ¬ (∀ p : ℕ, p.Prime → p % 6 = 1 → IsTerm p) := by
  sorry

end OMA.S_oeis_a086522
