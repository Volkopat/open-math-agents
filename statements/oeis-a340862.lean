import Mathlib

/-!
# A340862: Number of times the number n turns up in pseudo-Fibonacci sequences starting with [k, 1] (with k >= 1), excluding the starting terms.

Source: https://oeis.org/A340862
Credit: @agchua

Comment of A340862 (unsigned; the entry is by Robby Goetschalckx, Jan 24 2021):
  Conjecture: for n > 2, a(n) appears to be equal to 1 + A067148(n).
The sequence has offset 1. The pseudo-Fibonacci sequence starting with [k, 1] is S k 0 = k,
S k 1 = 1, S k (j+2) = S k j + S k (j+1); a(n) counts the pairs (k, j) with k >= 1 and j >= 2
(the starting terms excluded) such that S k j = n, as in the entry's examples.
A067148(n) (offset 1) is the number of pairs of integers (n, i), 0 < i < n, such that i and n
are consecutive terms i = b(j-1), n = b(j), for some j > 2, of a sequence b with b(1) = 1,
b(2) > 0 and b(k) = b(k-1) + b(k-2) for all k > 2; here B c is that sequence with b(2) = c
(B c 0 = 0 is a placeholder that is never used). For fixed n this is the number of such i.
Both counts are of finite sets; Set.ncard counts them.
-/

namespace OMA.S_oeis_a340862

/-- The pseudo-Fibonacci sequence starting with [k, 1]. -/
def S (k : ℕ) : ℕ → ℕ
  | 0 => k
  | 1 => 1
  | j + 2 => S k j + S k (j + 1)

/-- A340862(n): the number of pairs (k, j), k >= 1, j >= 2, with S k j = n. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ × ℕ | 1 ≤ p.1 ∧ 2 ≤ p.2 ∧ S p.1 p.2 = n}

/-- The sequence b of A067148 with b(1) = 1 and b(2) = c (indices from 1; B c 0 is unused). -/
def B (c : ℕ) : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => c
  | j + 3 => B c (j + 1) + B c (j + 2)

/-- A067148(n): the number of i with 0 < i < n such that i = b(j-1) and n = b(j) for some
j > 2 and some sequence b = B c with c > 0. -/
noncomputable def A067148 (n : ℕ) : ℕ :=
  Set.ncard {i : ℕ | 0 < i ∧ i < n ∧ ∃ c j : ℕ, 0 < c ∧ 2 < j ∧ B c (j - 1) = i ∧ B c j = n}

/-- The conjecture: a(n) = 1 + A067148(n) for n > 2. -/
theorem main : ∀ n : ℕ, 2 < n → a n = 1 + A067148 n := by
  sorry

end OMA.S_oeis_a340862
