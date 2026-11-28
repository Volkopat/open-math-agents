import Mathlib

/-!
# A192023: The Wiener index of the comb-shaped graph |_|_|...|_| with 2n (n>=1) nodes.

Source: https://oeis.org/A192023
Credit: @agchua

Comment of A192023 (the entry is by Emeric Deutsch, Jun 24 2011):
  Conjecture: for n>2, A192023(n-2) is the number of 2 X 2 matrices with all terms in
  {1,2,...,n} and determinant 2n. - Clark Kimberling, Mar 31 2012
The comb with 2n nodes has a spine of n nodes (i, 0), i < n, forming a path, and a tooth node
(i, 1) attached to each spine node; its Wiener index is the sum of the graph distances over all
unordered pairs of nodes, that is half the sum over all ordered pairs. (This agrees with the
entry's formula a(n) = n*(2*n^2 + 6*n - 5)/3 and its data.) A 2 X 2 matrix [[a, b], [c, d]]
with entries in {1, ..., n} is a quadruple (a, b, c, d); its determinant a*d - b*c equals 2n
exactly when a*d = b*c + 2n. The claim is stated for n > 2 as in the comment.
-/

namespace OMA.S_oeis_a192023

/-- The comb graph with 2n nodes: (i, 0) is joined to (i, 1) and to (i + 1, 0). -/
def comb (n : ℕ) : SimpleGraph (Fin n × Fin 2) :=
  SimpleGraph.fromRel fun x y =>
    (x.1 = y.1 ∧ x.2 = 0 ∧ y.2 = 1) ∨ (x.1.val + 1 = y.1.val ∧ x.2 = 0 ∧ y.2 = 0)

/-- A192023(n): the Wiener index of the comb graph with 2n nodes. -/
noncomputable def wiener (n : ℕ) : ℕ :=
  (∑ x : Fin n × Fin 2, ∑ y : Fin n × Fin 2, (comb n).dist x y) / 2

/-- The number of 2 X 2 matrices [[a, b], [c, d]] with entries in {1, ..., n} and
determinant a*d - b*c = 2n. -/
def count (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n ×ˢ Finset.Icc 1 n).filter
    (fun t : ℕ × ℕ × ℕ × ℕ => t.1 * t.2.2.2 = t.2.1 * t.2.2.1 + 2 * n)).card

/-- The comment's conjecture: for n > 2, the number of such matrices is A192023(n-2). -/
theorem main : ∀ n : ℕ, 2 < n → count n = wiener (n - 2) := by
  sorry

end OMA.S_oeis_a192023
