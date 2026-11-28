import Mathlib

/-!
# A267794: a(n) = n-2-i, where i (0 <= i < n-2) is the largest number such that [a(n-2)-a(i); a(n-1)-a(i+1)] = [0; 0], or a(n) = 0 if no such i exists.

Source: https://oeis.org/A267794

Conjecture in the entry (Ctibor O. Zizka, Jan 20 2016):
Maximal number of successive zeros in A181391 is 1, in this sequence 2. Conjecture: maximal
number of successive zeros is k: a(0); ...; a(j)>0; a(j+1)=0; ...; a(j+k)=0; a(j+k+1)>0; ...

Formalization notes:
* The parameter k is the one of the generalization a) listed in the entry: the block
  [a(n-2); a(n-1)] is replaced by the block [a(n-k); ...; a(n-1)]. The entry says that this
  sequence has k = 2 and that A181391 has k = 1. So `s k` is the sequence with offset 0 given
  by s(n) = 0 for n < k, and for n >= k, s(n) = n-k-i, where i (0 <= i < n-k) is the largest
  number such that s(i+t) = s(n-k+t) for every t < k, or s(n) = 0 if no such i exists.
  For k = 2 this is word for word the name of A267794 (the two starting terms a(0) = a(1) = 0
  are the ones of the program in the entry), and `a` below is `s 2`; its first terms agree
  with the data 0, 0, 0, 1, 0, 0, 3, 0, 0, 3, 3, 0, 4, 0, 0, 6, ... For k = 1, s(n) is Van
  Eck's sequence A181391 with the index shifted by one (A181391 has offset 1).
* The sequence is built term by term: `terms k n` is the list s(0), ..., s(n-1) and `next k l`
  computes the following term from the list l of the terms before it. The largest i is taken
  with `Nat.findGreatest`, inside the branch where some i < n-k satisfies the condition, so
  the natural-number subtraction n-k-i is exact there.
* Successive zeros are counted as in the pattern of the conjecture: a run of zeros that starts
  right after a positive term a(j). The run of k+1 zeros at the start, s(0), ..., s(k), is not
  preceded by any term, so the pattern does not count it.
* Maximal number of successive zeros is k is read as two claims: some positive term is
  followed by exactly k zeros and then a positive term, and no positive term is followed by
  k+1 zeros. The claim is stated for every k >= 1, the range of the generalization.
-/

namespace OMA.S_oeis_a267794

/-- The term that follows the list `l` of earlier terms, for the block length `k`. -/
def next (k : ℕ) (l : List ℕ) : ℕ :=
  if l.length < k then 0
  else
    if ∃ i, i < l.length - k ∧ ∀ t, t < k → l.getD (i + t) 0 = l.getD (l.length - k + t) 0 then
      l.length - k - Nat.findGreatest
        (fun i => i < l.length - k ∧
          ∀ t, t < k → l.getD (i + t) 0 = l.getD (l.length - k + t) 0)
        (l.length - k)
    else 0

/-- `terms k n` is the list of the first n terms s(0), ..., s(n-1). -/
def terms (k : ℕ) : ℕ → List ℕ
  | 0 => []
  | n + 1 => terms k n ++ [next k (terms k n)]

/-- The generalized sequence with blocks of length k. -/
def s (k n : ℕ) : ℕ := (terms k (n + 1)).getD n 0

/-- A267794: the case k = 2. -/
def a (n : ℕ) : ℕ := s 2 n

/-- Zizka's conjecture on A267794: for every k >= 1, the maximal number of successive zeros
after a positive term is k. -/
theorem main :
    ∀ k : ℕ, 1 ≤ k →
      (∃ j : ℕ, 0 < s k j ∧ (∀ t : ℕ, 1 ≤ t → t ≤ k → s k (j + t) = 0) ∧
          0 < s k (j + k + 1)) ∧
      (∀ j : ℕ, 0 < s k j → ∃ t : ℕ, 1 ≤ t ∧ t ≤ k + 1 ∧ s k (j + t) ≠ 0) := by
  sorry

end OMA.S_oeis_a267794
