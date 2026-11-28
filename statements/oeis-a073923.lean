import Mathlib

/-!
# A073923: a(n) = A059661(n) - A059661(n-1) fails at n = 2

Source: https://oeis.org/A073923
Credit: @ivillar

A073923: a(1) = 1, a(n) is the smallest power of 2 not included earlier such that
Sum_{k=1..n} a(k) is prime (offset 1; data 1, 2, 4, 16, 8, 4096, 32, 16384, ...). R. J. Mathar
conjectured (May 07 2007) a(n) = A059661(n) - A059661(n-1), where A059661 (offset 1; data 2, 3, 7,
23, 31, 4127, ...) is "like A059459, but each term must be greater than the previous ones", and
A059459 has a(1) = 2, a(n+1) being obtained by writing a(n) in binary and trying to complement
just one bit, starting with the least significant bit, until a new prime is reached.

Status: false as stated (counterexample n = 2: A073923(2) = 2, while
A059661(2) - A059661(1) = 3 - 2 = 1); kept as the target of a disproof. The data agree for
3 <= n <= 12 (the partial sums of A073923 are 1, 3, 7, 23, ..., and A059661 starts at 2, not 1).

Formalization notes:
* `terms n` is the list of the first n terms of A073923; when no admissible power of 2 exists
  the next term is set to 0 (the entry gives no value then; this does not affect n = 2).
* `b` is A059661: from b(n) = x, the next term complements the bit k of x for the least k such
  that x XOR 2^k is a prime greater than x (it is then greater than all earlier terms, which are
  smaller than x, hence new); again 0 if there is no such k.
* The identity is stated over ℤ for every n >= 2 (both sides are defined from n = 2 on).
-/

namespace OMA.S_oeis_a073923

/-- The term following the earlier terms `l`: the smallest power of 2 not in `l` such that the sum
of `l` and this power is prime (0 if there is none). -/
noncomputable def next (l : List ℕ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, 2 ^ k ∉ l ∧ (l.sum + 2 ^ k).Prime then 2 ^ Nat.find h else 0

/-- The first `n` terms of A073923. -/
noncomputable def terms : ℕ → List ℕ
  | 0 => []
  | 1 => [1]
  | n + 2 => terms (n + 1) ++ [next (terms (n + 1))]

/-- A073923(n), for n ≥ 1. -/
noncomputable def a (n : ℕ) : ℕ := (terms n).getD (n - 1) 0

/-- One step of A059661: complement the least significant possible bit of `x` so as to reach a
prime greater than `x` (0 if there is none). -/
noncomputable def flipStep (x : ℕ) : ℕ := by
  classical
  exact if h : ∃ k : ℕ, x < x ^^^ 2 ^ k ∧ (x ^^^ 2 ^ k).Prime then x ^^^ 2 ^ Nat.find h else 0

/-- A059661(n), for n ≥ 1: b(1) = 2 and b(n+1) = flipStep(b(n)). -/
noncomputable def b : ℕ → ℕ
  | 0 => 0
  | 1 => 2
  | n + 2 => flipStep (b (n + 1))

/-- Mathar's conjecture as recorded in A073923: a(n) = A059661(n) - A059661(n-1). -/
theorem main : ∀ n : ℕ, 2 ≤ n → (a n : ℤ) = b n - b (n - 1) := by
  sorry

end OMA.S_oeis_a073923
