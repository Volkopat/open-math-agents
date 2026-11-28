import Mathlib

/-!
# A156870: Number of nondecreasing sequences of 2n positive integers with reciprocals adding up
to n (1 <= n).

Source: https://oeis.org/A156870
Credit: @esracummings31-blip

Conjecture (Jens Voß, 2009): A156869(2n + m, n + m) = a(n) if and only if m >= 0.
Here A156869(n, k) is the number of nondecreasing sequences of n positive integers with reciprocals
adding up to k.

Conventions.
* A nondecreasing sequence of positive integers is the same as a multiset of positive integers.
* n >= 1 (offset 1), and m ranges over the integers for which A156869(2n+m, n+m) is an entry
  of the triangle, i.e. n + m >= 1. The equivalence is stated as its two halves: equality for every
  m >= 0, and inequality for every m = -r with 1 <= r <= n - 1.
-/

namespace OMA.S_oeis_a156870

/-- The nondecreasing sequences (multisets) of n positive integers with reciprocals adding up to k. -/
def seqs (n k : ℕ) : Set (Multiset ℕ) :=
  {s | Multiset.card s = n ∧ (∀ x ∈ s, 0 < x) ∧ (s.map (fun x : ℕ => (1 : ℚ) / x)).sum = k}

/-- A156869(n, k). -/
noncomputable def A156869 (n k : ℕ) : ℕ := Set.ncard (seqs n k)

/-- A156870. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard (seqs (2 * n) n)

theorem main : ∀ n : ℕ, 1 ≤ n →
    (∀ m : ℕ, A156869 (2 * n + m) (n + m) = a n) ∧
    (∀ r : ℕ, 1 ≤ r → r < n → A156869 (2 * n - r) (n - r) ≠ a n) := by
  sorry

end OMA.S_oeis_a156870
