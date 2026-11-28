import Mathlib

/-!
# OEIS A233417: q(k)·q(n−k) ± 1 prime, with q the strict partition function

Source: https://oeis.org/A233417 (Zhi-Wei Sun), conjecture (i) in COMMENTS
Credit: @LEGZM

q(n) = A000009(n) is the number of partitions of n into distinct parts, and
a(n) = |{0 < k ≤ n/2 : q(k)·q(n−k) + 1 is prime}|. Conjecture (i): a(n) > 0 for all n > 1.
Similarly, for any integer n > 5, there is a positive integer k < n with q(k)·q(n−k) − 1 prime.
-/

namespace OMA.S_oeis_a233417

/-- q(n): the number of partitions of n into distinct parts (A000009). -/
def q (n : ℕ) : ℕ := (Nat.Partition.distincts n).card

/-- A233417(n): the number of 0 < k ≤ n/2 with q(k)·q(n−k) + 1 prime. -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 1 (n / 2)).filter (fun k => (q k * q (n - k) + 1).Prime)).card

theorem main : (∀ n : ℕ, 1 < n → 0 < a n) ∧
    (∀ n : ℕ, 5 < n → ∃ k : ℕ, 0 < k ∧ k < n ∧ (q k * q (n - k) - 1).Prime) := by
  sorry

end OMA.S_oeis_a233417
