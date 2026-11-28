import Mathlib

/-!
# A340234: the number of harmonious graphs with n edges and at most n vertices, with loops

Source: https://oeis.org/A340234 (OEIS Foundation, CC BY-SA 4.0).
Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)

Entry A340234, offset 1: Number of harmonious graphs with n edges and at most n vertices,
allowing self-loops. Data
1, 2, 8, 36, 243, 1728, 16384, 160000, 1953125, 24300000, 362797056, 5489031744, ...
Comment: A graph G = (V,E) is harmonious if there exists an injective function
f_V : V -> {0,1,...,n-1} such that a bijection occurs in the function f_E : E -> {0,...,n-1}
after the harmoniously induced edge labels, f_E(v_i v_j) = (f_V(v_i) + f_V(v_j)) (mod n), are
applied.

Formula section: For n odd, a(n) = ceiling(n/2)^n; for n even,
a(n) = ((n^2/4) + (n/2))^(n/2) (conjectured).

Formalization notes.
* The sequence counts the graphs together with their vertex labels: a graph is a set E of n
  edges {i, j} with i <= j (i = j is a loop) on the labels 0..n-1, and it is counted when the
  edge labels (i + j) mod n are pairwise different (n different labels in 0..n-1 are a
  bijection). The count of these sets is 1, 2, 8, 36, 243, 1728 for n = 1..6, which agrees with
  the data (the number of graphs up to isomorphism is smaller, for example 6 for n = 3).
* An edge is a pair (i, j) of natural numbers with i <= j < n.
* ceiling(n/2) is (n + 1) / 2 for odd n; n^2/4 and n/2 are exact divisions for even n.
-/

namespace OMA.S_oeis_a340234

open Finset

/-- A340234(n): the number of sets E of n edges {i, j} (i ≤ j, loops allowed) on the vertex labels
0..n-1 such that the edge labels (i + j) mod n are pairwise different (so they are a bijection
onto 0..n-1). -/
def a (n : ℕ) : ℕ :=
  (((range n ×ˢ range n).powerset).filter (fun E : Finset (ℕ × ℕ) =>
    (∀ e ∈ E, e.1 ≤ e.2) ∧ E.card = n ∧
    ∀ e ∈ E, ∀ e' ∈ E, (e.1 + e.2) % n = (e'.1 + e'.2) % n → e = e')).card

/-- The conjecture: a(n) = ceiling(n/2)^n for odd n, and a(n) = (n^2/4 + n/2)^(n/2) for even n. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (n % 2 = 1 → a n = ((n + 1) / 2) ^ n) ∧
    (n % 2 = 0 → a n = (n ^ 2 / 4 + n / 2) ^ (n / 2)) := by
  sorry

end OMA.S_oeis_a340234
