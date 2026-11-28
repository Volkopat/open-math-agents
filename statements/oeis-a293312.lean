import Mathlib

/-!
# OEIS A293312: traces of powers of M_n count the magic labelings of LOOP X C_k

Source: https://oeis.org/A293312 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (L. Edson Jeffery, Oct 10 2017): Rectangular array read by antidiagonals:
A(n,k) = tr((M_n)^k), k >= 0, where M_n is the n X n matrix M_1 = {{1}},
M_n = {{0,...,0,1},{0,...,0,1,1},...,{0,1,...,1},{1,...,1}}, n > 1, and tr(.) is the trace.
Conjecture: For all n >= 1, for all k >= 2, A(n, k) = A293311(k, n); i.e., A(n, k) = number of
magic labelings of the graph LOOP X C_k with magic sum n - 1.

Formalization notes:
* `M n` is the matrix M_n with rows and columns indexed from 0. Row r of M_n has ones exactly in
  its last r + 1 columns, so the entry in row r and column c is 1 iff r + c ≥ n - 1; for n = 1
  this is the matrix {{1}}.
* LOOP X C_k is the cycle C_k with a loop attached to every vertex (A293311). A magic labeling
  with magic sum s assigns a nonnegative integer to every edge so that the labels of the edges at
  each vertex add up to s, a loop counted once, as in the Mathematica program of A293311.
* Vertex j of the cycle (j taken mod k) lies on the cycle edges labeled `e j` and `e (j + 1)`,
  where the edge labeled `e (j + 1)` joins vertex j to vertex j + 1, and carries the loop labeled
  `l j`; `finRotate k j` is j + 1 mod k. For k = 2 the cycle has two parallel edges, as in
  A293311 (whose row for C_2 is (s + 1)(s + 2)/2).
* A magic labeling is the pair `(e, l)`, and `main` counts the set of these pairs with
  `Set.ncard`; the set is finite since every label is at most the magic sum.
-/

namespace OMA.S_oeis_a293312

/-- The n X n matrix M_n, rows and columns indexed from 0: the entry in row r and column c is 1
iff r + c ≥ n - 1. -/
def M (n : ℕ) : Matrix (Fin n) (Fin n) ℕ := fun r c => if n - 1 ≤ (r : ℕ) + c then 1 else 0

/-- A(n, k) = tr((M_n)^k). -/
def A (n k : ℕ) : ℕ := Matrix.trace (M n ^ k)

/-- `(e, l)` is a magic labeling of LOOP X C_k with magic sum s: at vertex j the cycle edges
labeled `e j` and `e (j + 1)` and the loop labeled `l j` add up to s. -/
def IsMagicLabeling (k s : ℕ) (e l : Fin k → ℕ) : Prop :=
  ∀ j : Fin k, e j + l j + e (finRotate k j) = s

/-- For all n ≥ 1 and k ≥ 2, A(n, k) is the number of magic labelings of LOOP X C_k with magic
sum n - 1. -/
theorem main : ∀ n k : ℕ, 1 ≤ n → 2 ≤ k →
    A n k = Set.ncard {p : (Fin k → ℕ) × (Fin k → ℕ) | IsMagicLabeling k (n - 1) p.1 p.2} := by
  sorry

end OMA.S_oeis_a293312
