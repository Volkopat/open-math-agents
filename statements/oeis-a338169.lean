import Mathlib

/-!
# A338169: A list of all finite sequences of distinct positive integers sorted by their maximum value, then lexicographically.

Source: https://oeis.org/A338169
Credit: @agchua

Comment line of A338169 (unsigned; the entry is by Peter Kagey, Oct 14 2020), verbatim:
  Conjecture: the sum of the sum of all sequences with a maximum value of n is given by A281912(n).
A sequence with a maximum value of n (n >= 1) is a finite sequence of distinct positive integers
whose largest entry is n: a list l of natural numbers without repetitions, all of whose entries
lie in 1..n, and which contains n (IsSeq n l below; for n = 2 these are [1,2], [2], [2,1], with
sums 3 + 2 + 3 = 8). There are finitely many such lists. The statement says that some Finset
contains exactly these lists, and that for every such Finset the sum, over its lists l, of the
sum of the entries of l equals A281912(n).
A281912 (offset 1, data 1, 8, 57, 424, 3425, ...) is defined by its first formula line,
  a(n) = n! * Sum_{k=2..n+1} binomial(k,2)/(n+1-k)!,
computed in the rationals.
-/

namespace OMA.S_oeis_a338169

/-- A281912 by its formula: a(n) = n! * Sum_{k=2..n+1} binomial(k,2)/(n+1-k)!. -/
noncomputable def A281912 (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * ∑ k ∈ Finset.Icc 2 (n + 1), (k.choose 2 : ℚ) / ((n + 1 - k).factorial : ℚ)

/-- l is a finite sequence of distinct positive integers with maximum value n. -/
def IsSeq (n : ℕ) (l : List ℕ) : Prop := l.Nodup ∧ (∀ x ∈ l, 1 ≤ x ∧ x ≤ n) ∧ n ∈ l

/-- For n >= 1 the sequences with maximum value n form a finite set, and the sum of their sums
is A281912(n). -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (∃ F : Finset (List ℕ), ∀ l : List ℕ, l ∈ F ↔ IsSeq n l) ∧
    ∀ F : Finset (List ℕ), (∀ l : List ℕ, l ∈ F ↔ IsSeq n l) →
      ∑ l ∈ F, (l.sum : ℚ) = A281912 n := by
  sorry

end OMA.S_oeis_a338169