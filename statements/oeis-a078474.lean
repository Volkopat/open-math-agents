import Mathlib

/-!
# OEIS A078474: a(n) = A284680(1) + ... + A284680(n)

Source: https://oeis.org/A078474 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Reinhard Zumkeller, Jan 02 2003), offset 1: a(1)=a(2)=a(3)=1,
a(n)=n-a(a(n-1))-a(a(n-2))-a(a(n-3)).
Conjecture: partial sums of A284680 (verified for n <= 100000). - Sean A. Irvine, Jul 16 2022
Data: 1, 1, 1, 1, 2, 3, 4, 5, 5, 5, 5, 6, ...
A284680 (Clark Kimberling, Apr 11 2017), offset 1: Fixed point of the morphism 0->1, 1->1000.
Data: 1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1, ...

Formalization notes:
* `IsSolution a` states the definition of the entry: a(1) = a(2) = a(3) = 1 and, for n >= 4, the
  recursion as an equation of integers. These conditions determine a(n) for n >= 1 term by term
  (by induction 1 <= a(k) <= k, so the nested arguments are earlier indices), so `main` is
  stated for every function satisfying them; a(0) is not a term of the entry and is left free.
* `mu` applies the morphism 0 -> 1, 1 -> 1000 letter by letter, and `muIter k` is its k-th power
  applied to 1, the first letter of A284680. As 1000 begins with 1, `muIter k` is a prefix of
  `muIter (k + 1)`, and it has more than k letters, so `x k`, letter k - 1 of `muIter k`, is
  A284680(k), counted from 1 as in that entry.
* The partial sums of A284680 are the sums x 1 + ... + x n, so `main` says a(n) = x(1) + ... + x(n)
  for every n >= 1.
-/

namespace OMA.S_oeis_a078474

/-- The definition of A078474: a(1) = a(2) = a(3) = 1 and a(n) = n - a(a(n-1)) - a(a(n-2)) - a(a(n-3))
for n >= 4. -/
def IsSolution (a : ℕ → ℕ) : Prop :=
  a 1 = 1 ∧ a 2 = 1 ∧ a 3 = 1 ∧
    ∀ n : ℕ, 4 ≤ n → (a n : ℤ) = n - a (a (n - 1)) - a (a (n - 2)) - a (a (n - 3))

/-- The morphism 0 -> 1, 1 -> 1000, applied letter by letter (other letters are copied). -/
def mu : List ℕ → List ℕ
  | 0 :: l => 1 :: mu l
  | 1 :: l => 1 :: 0 :: 0 :: 0 :: mu l
  | y :: l => y :: mu l
  | [] => []

/-- The images of 1 under the powers of the morphism: 1, 1000, 1000111, ... -/
def muIter : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => mu (muIter n)

/-- A284680(k), counted from 1: letter k - 1 of the k-th image of 1. -/
def x (k : ℕ) : ℕ := (muIter k).getD (k - 1) 0

/-- Irvine's conjecture: A078474 is the sequence of partial sums of A284680. -/
theorem main : ∀ a : ℕ → ℕ, IsSolution a → ∀ n : ℕ, 1 ≤ n → a n = ∑ k ∈ Finset.Icc 1 n, x k := by
  sorry

end OMA.S_oeis_a078474
