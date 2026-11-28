import Mathlib

/-!
# A005840: Expansion of (1-x)*e^x/(2-e^x).

Source: https://oeis.org/A005840
Credit: @thatoneguy006

A005840(n) is the number of labeled threshold graphs on n vertices (Svante Janson, in the
entry). The conjecture stated here is the one the entry records:

  Conjecture: A285868 (with offset 1) shows the associated connected threshold graphs.
  - R. J. Mathar, Apr 29 2019

that is, for n ≥ 1 the number of connected labeled threshold graphs on n vertices is
A285868(n - 1). The entry adds (David Galvin, Oct 18 2021) that this number is A317057, which
agrees with A285868 (offset 1) for n ≤ 3 but gives 23 against 20 at n = 4. The statement is
recorded as conjectured; it is expected to be refutable.

Definitions.
* A graph on `Fin n` is threshold if its vertices can be listed so that each vertex is adjacent
  either to all or to none of the vertices listed before it (built from the empty graph by
  repeatedly adding an isolated or a dominating vertex). This is the standard definition; it is
  equivalent to having no induced 2K₂, P₄ or C₄ (Chvátal and Hammer). With it, the numbers of
  threshold graphs on `Fin n` are 1, 1, 2, 8, 46, 332, the terms of A005840.
* Connectedness is Mathlib's `SimpleGraph.Connected`.
* A285868(n) is the row sum of the triangle A285867,
  T(n, k) = S2(n, k) k! + S2(n, k - 1) (k - 1)!, 0 ≤ k ≤ n, with S2 the Stirling numbers of
  the second kind (A048993) and the second term absent for k = 0, as in A285867.
-/

namespace OMA.S_oeis_a005840

/-- A labeled threshold graph: some ordering of the vertices adds each vertex as an isolated or a
dominating vertex with respect to the earlier ones. -/
def IsThreshold {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ σ : Fin n ≃ Fin n, ∀ i : Fin n,
    (∀ j : Fin n, j < i → G.Adj (σ i) (σ j)) ∨ (∀ j : Fin n, j < i → ¬ G.Adj (σ i) (σ j))

/-- The triangle A285867: `T(n, k) = S2(n, k) k! + S2(n, k - 1) (k - 1)!`. -/
def T (n k : ℕ) : ℕ :=
  Nat.stirlingSecond n k * k.factorial +
    (if k = 0 then 0 else Nat.stirlingSecond n (k - 1) * (k - 1).factorial)

/-- A285868: the row sums of A285867. -/
def A285868 (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), T n k

/-- Mathar's conjecture: for n ≥ 1 there are A285868(n - 1) connected labeled threshold graphs
on n vertices. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    Nat.card {G : SimpleGraph (Fin n) // IsThreshold G ∧ G.Connected} = A285868 (n - 1) := by
  sorry

end OMA.S_oeis_a005840
