import Mathlib

/-!
# A117549: Values of n for which there exist d(1),...,d(n), each in {0,1,...,4} and an r in {1,...,4} such that Sum[d(i)d(i+k),i=1,n-k]=r (mod 5) for all k=0,...,n-1. (Such a sequence is called a very(5,r) sequence. See the link.).

Source: https://oeis.org/A117549
Credit: @agchua

Comment of A117549 (the entry is by John W. Layman, Apr 21 2006), verbatim:
  Conjecture. Let A be a very(5,1) (respectively very(5,4)) sequence of length n and let Z be a
  sequence of n-1 0's.. Then AZ(3A)ZA is a very(5,1) (respectively very(5,4)) sequence of
  length 5n-2. (Here 3A denotes the result of multiplying each term of A by 3, then reducing
  modulo 5; and juxtaposition of symbols denotes concatenation of sequences.)
Offset 1; data 1, 3, 6, 10, 13, 16.

Formalisation. The sequence d(1), ..., d(n) is the list [d(1), ..., d(n)] of natural numbers,
so d(i) is d.getD (i - 1) 0. corr d k is Sum_{i=1}^{n-k} d(i) d(i+k). very5 r d says that
every term of d is in {0, ..., 4} and that corr d k = r (mod 5) for k = 0, ..., n - 1.
glue A is AZ(3A)ZA. The theorem states the conjecture for r = 1 and for r = 4, including the
length 5n - 2. (For the empty list, n = 0, the claim holds trivially in this form.)
-/

namespace OMA.S_oeis_a117549

/-- corr d k = Sum_{i=1}^{n-k} d(i) d(i+k) for the sequence d = [d(1), ..., d(n)]. -/
def corr (d : List ℕ) (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d.length - k), d.getD i 0 * d.getD (i + k) 0

/-- d is a very(5,r) sequence: every term is in {0, ..., 4}, and corr d k = r (mod 5) for
k = 0, ..., n - 1, where n is the length of d. -/
def very5 (r : ℕ) (d : List ℕ) : Prop :=
  (∀ x ∈ d, x ≤ 4) ∧ ∀ k : ℕ, k < d.length → corr d k ≡ r [MOD 5]

/-- AZ(3A)ZA: Z is the list of n - 1 zeros, and 3A is A with each term x replaced by
3x reduced modulo 5. -/
def glue (A : List ℕ) : List ℕ :=
  A ++ List.replicate (A.length - 1) 0 ++ A.map (fun x => 3 * x % 5) ++
    List.replicate (A.length - 1) 0 ++ A

/-- The conjecture, for r = 1 and for r = 4: if A is a very(5,r) sequence of length n, then
AZ(3A)ZA is a very(5,r) sequence of length 5n - 2. -/
theorem main : ∀ r : ℕ, (r = 1 ∨ r = 4) → ∀ A : List ℕ, very5 r A →
    very5 r (glue A) ∧ (glue A).length = 5 * A.length - 2 := by
  sorry

end OMA.S_oeis_a117549
