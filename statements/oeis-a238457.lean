import Mathlib

/-!
# A238457: a(n) = |{0 < k <= n: p(n) + k is prime}|, where p(.) is the partition function (A000041).

Source: https://oeis.org/A238457
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry):
(i) a(n) > 0 for all n > 0, and a(n) = 1 only for n = 1, 2, 3, 4, 5, 30, 109. Also, for each
n > 2 there is a positive integer k <= n+3 such that p(n) - k is prime.
(ii) For the strict partition function q(.) given by A000009, we have
|{0 < k <= n: q(n) + k is prime}| > 0 for all n > 0 and |{0 < k <= n: q(n) - k is prime}| > 0
for all n > 4.

Formalization notes:
* p(n) = `Fintype.card (Nat.Partition n)` (the partition function A000041); q(n), the number of
  partitions of n into distinct parts (A000009), is the number of `Nat.Partition n` whose parts
  have no repetition.
* "a(n) = 1 only for n in S" is stated as: for n ≥ 1, a(n) = 1 iff n ∈ S. p(n) - k and q(n) - k are
  in ℕ; a truncated value 0 is not prime, as negative numbers are not prime.
* Controls (computed): a(1..25) = 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 4, 3, 3, 3, 3, 3, 4, 4, 3, 4, 2,
  3, 2, as in the entry; all claims hold for n < 130.
-/

namespace OMA.S_oeis_a238457

/-- The partition function `p(n)`. -/
noncomputable def p (n : ℕ) : ℕ := Fintype.card (Nat.Partition n)

/-- The number of partitions of `n` into distinct parts. -/
noncomputable def q (n : ℕ) : ℕ :=
  Fintype.card {π : Nat.Partition n // π.parts.Nodup}

/-- A238457(n). -/
noncomputable def a (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter fun k => (p n + k).Prime).card

/-- The conjecture of the entry (the parts listed above). -/
theorem main :
    (∀ n : ℕ, 0 < n → 0 < a n) ∧
      (∀ n : ℕ, 0 < n → (a n = 1 ↔ n ∈ ({1, 2, 3, 4, 5, 30, 109} : Finset ℕ))) ∧
      (∀ n : ℕ, 2 < n → ∃ k, 0 < k ∧ k ≤ n + 3 ∧ (p n - k).Prime) ∧
      (∀ n : ℕ, 0 < n → ∃ k, 0 < k ∧ k ≤ n ∧ (q n + k).Prime) ∧
      ∀ n : ℕ, 4 < n → ∃ k, 0 < k ∧ k ≤ n ∧ (q n - k).Prime := by
  sorry

end OMA.S_oeis_a238457
