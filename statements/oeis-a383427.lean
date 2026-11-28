import Mathlib

/-!
# A383427: Indices k such that A003849(k) = A383422(k).

Source: https://oeis.org/A383427
Credit: @agchua

Comment of A383427 (the entry is by Clark Kimberling, Apr 27 2025), verbatim:
  Conjecture: {a(n) - a(n-1), n>=2} = {1, 2, 3, 5, 6}.
A003849 (offset 0) is the infinite Fibonacci word, obtained by starting with 0 and repeatedly
applying the morphism 0 -> 01, 1 -> 0; the n-th iterate fibIter n has length Fib(n + 2) >= n + 1
and is a prefix of fibIter (n + 1), so A003849(k) is the k-th entry of fibIter (k + 1).
A383422 (offset 0) is the infinite Lucas word, the limit of s(0) = 0, s(1) = 011,
s(n) = s(n - 1) s(n - 2); each lucasIter n has length L(n + 1) >= n + 1 and is a prefix of
lucasIter (n + 1), so A383422(k) is the k-th entry of lucasIter k.
A383427 has offset 1 (a(1) = 0, a(2) = 1, a(3) = 3, ...), listing in increasing order the indices k >= 0 with A003849 k = A383422 k.
Since Nat.nth indexes from 0, a(n) = Nat.nth P (n - 1) for n >= 1, and the conjecture asserts
that the set of consecutive differences a(n) - a(n - 1) for n >= 2 is {1, 2, 3, 5, 6}.
-/

namespace OMA.S_oeis_a383427

/-- One step of the Fibonacci morphism 0 -> 01, 1 -> 0. -/
def fibStep : List ℕ → List ℕ
  | [] => []
  | 0 :: rest => 0 :: 1 :: fibStep rest
  | _ :: rest => 0 :: fibStep rest

/-- The n-th iterate of the Fibonacci morphism starting from [0]. -/
def fibIter : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => fibStep (fibIter n)

/-- A003849: the k-th letter (0-indexed) of the infinite Fibonacci word. -/
def A003849 (k : ℕ) : ℕ := (fibIter (k + 1)).getD k 0

/-- The finite Lucas words s(0) = 0, s(1) = 011, s(n) = s(n - 1) ++ s(n - 2). -/
def lucasIter : ℕ → List ℕ
  | 0 => [0]
  | 1 => [0, 1, 1]
  | n + 2 => lucasIter (n + 1) ++ lucasIter n

/-- A383422: the k-th letter (0-indexed) of the infinite Lucas word. -/
def A383422 (k : ℕ) : ℕ := (lucasIter k).getD k 0

/-- A383427 (offset 1): the n-th index k >= 0 such that A003849 k = A383422 k. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth (fun k : ℕ => A003849 k = A383422 k) (n - 1)

/-- The conjecture: {a(n) - a(n - 1) | n >= 2} = {1, 2, 3, 5, 6}. -/
theorem main :
    {d : ℕ | ∃ n : ℕ, 2 ≤ n ∧ a n - a (n - 1) = d} = ({1, 2, 3, 5, 6} : Set ℕ) := by
  sorry

end OMA.S_oeis_a383427
