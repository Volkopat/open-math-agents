import Mathlib

/-!
# A156869: Triangle read by rows: T(n,k) = number of nondecreasing sequences of n positive
integers with reciprocals adding up to k (1 <= k <= n).

Source: https://oeis.org/A156869
Credit: @esracummings31-blip

Conjecture (Jens Voß, 2009): T(2n + m, n + m) = T(2n, n) (= A156870(n)) if and only if m >= 0.

Conventions.
* A nondecreasing sequence of positive integers is the same as a multiset of positive integers.
* n >= 1 (A156870 has offset 1), and m ranges over the integers for which T(2n+m, n+m) is an entry
  of the triangle, i.e. n + m >= 1. The equivalence is stated as its two halves: equality for every
  m >= 0, and inequality for every m = -r with 1 <= r <= n - 1.
-/

namespace OMA.S_oeis_a156869

/-- The nondecreasing sequences (multisets) of n positive integers with reciprocals adding up to k. -/
def seqs (n k : ℕ) : Set (Multiset ℕ) :=
  {s | Multiset.card s = n ∧ (∀ x ∈ s, 0 < x) ∧ (s.map (fun x : ℕ => (1 : ℚ) / x)).sum = k}

/-- A156869: T(n, k). -/
noncomputable def T (n k : ℕ) : ℕ := Set.ncard (seqs n k)

theorem main : ∀ n : ℕ, 1 ≤ n →
    (∀ m : ℕ, T (2 * n + m) (n + m) = T (2 * n) n) ∧
    (∀ r : ℕ, 1 ≤ r → r < n → T (2 * n - r) (n - r) ≠ T (2 * n) n) := by
  sorry

end OMA.S_oeis_a156869
