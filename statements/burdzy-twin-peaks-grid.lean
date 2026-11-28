import Mathlib

/-!
# Do the two peaks of a random labeling of the square grid repel each other?

Source: https://sites.math.washington.edu/~burdzy/open_mathjax.php (problem 9)
Credit: @SulkBash

## The problem, as the source states it

A labeling of a graph with `n` vertices is a one-to-one function mapping the vertices to
`1, 2, …, n`. A vertex is a peak if all adjacent vertices have lower labels. The random labeling
is a labeling chosen uniformly from all labelings.

Problem (Burdzy). Condition the random labeling of an `n` by `n` discrete square on having
exactly two peaks. Let `ρ_n` be the (random) graph distance between the two peaks. Does `ρ_n / n`
converge in distribution to `0` when `n → ∞`?

See Billey, Burdzy and Sagan, Permutations with given peak set, J. Integer Seq. 16 (2013), for
related one-dimensional results, and Burdzy and Pal, Twin peaks, Random Structures Algorithms 56
(2020), 432–460. The latter conjecture that on the two-dimensional discrete torus with `N`
vertices the distance between the two peaks divided by `√N` does not tend to `0`; the title of
the source problem (do peaks repel each other?) points the same way.

## Formalization notes

* The `n` by `n` discrete square is the grid graph `pathGraph n □ pathGraph n` on
  `Fin n × Fin n`: two cells are adjacent when they agree in one coordinate and differ by one in
  the other. It is the square with its boundary, not the torus. The graph distance is Mathlib's
  `SimpleGraph.dist` (the length of a shortest walk; the grid is connected).
* A labeling is a bijection `Fin n × Fin n ≃ Fin (n * n)`, so the labels are `0, …, n² - 1`
  rather than `1, …, n²`. Adding one to every label is a bijection between the two kinds of
  labelings that preserves the order of labels, hence the peaks and `ρ_n`, so the conditioned
  law of `ρ_n` is the same.
* The uniform labeling conditioned on exactly two peaks is the uniform law on the finite set of
  labelings with exactly two peaks. The probability of an event is therefore the number of
  two-peak labelings in it divided by the number of two-peak labelings (`probFar`). For
  `n ≤ 1` there is no two-peak labeling (the largest label is always a peak, and `n = 1` has a
  single vertex), so the quotient is `0 / 0 = 0` in Lean. For every `n ≥ 2` there is one: take two
  opposite corners as peaks and label the other cells in decreasing order of their distance to
  the nearer corner, so every other cell has a neighbour with a larger label. The conditioned
  law is thus defined for all `n ≥ 2`, which is all that a limit as `n → ∞` uses.
* With exactly two peaks `p ≠ q`, `ρ_n = dist p q`, and the event `ρ_n / n > ε` is stated as:
  some two distinct peaks `p, q` satisfy `ε < dist p q / n`.
* The limit is the constant `0`, and for a constant limit convergence in distribution is
  equivalent to convergence in probability. Since `ρ_n / n ≥ 0`, this means: for every `ε > 0`,
  `P(ρ_n / n > ε) → 0` as `n → ∞`. This is the form stated in `main`.
* `main` is the affirmative answer to the question. Its negation, which a disproof would
  establish, is exactly the negative answer: for some `ε > 0`, `P(ρ_n / n > ε)` does not tend
  to `0`, so `ρ_n / n` does not converge in distribution to `0`.
-/

namespace OMA.S_burdzy_twin_peaks_grid

open Filter
open scoped Topology

/-- The `n` by `n` discrete square: the grid graph on `Fin n × Fin n`. -/
def grid (n : ℕ) : SimpleGraph (Fin n × Fin n) :=
  SimpleGraph.boxProd (SimpleGraph.pathGraph n) (SimpleGraph.pathGraph n)

/-- A labeling of the `n` by `n` square: a bijection from its `n * n` vertices onto the labels
`0, 1, …, n * n - 1`. -/
abbrev Labeling (n : ℕ) : Type := Fin n × Fin n ≃ Fin (n * n)

/-- The peaks of a labeling: the vertices all of whose neighbours have lower labels. -/
def peaks {n : ℕ} (f : Labeling n) : Set (Fin n × Fin n) :=
  {v | ∀ w, (grid n).Adj v w → f w < f v}

/-- The labeling has exactly two peaks. -/
def HasTwoPeaks {n : ℕ} (f : Labeling n) : Prop :=
  (peaks f).ncard = 2

/-- The event `ρ_n / n > ε`: two distinct peaks at graph distance greater than `ε * n`. -/
def PeaksApart {n : ℕ} (ε : ℝ) (f : Labeling n) : Prop :=
  ∃ p ∈ peaks f, ∃ q ∈ peaks f, p ≠ q ∧ ε < ((grid n).dist p q : ℝ) / n

/-- `P(ρ_n / n > ε)` for the uniform labeling of the `n` by `n` square conditioned on having
exactly two peaks. -/
noncomputable def probFar (n : ℕ) (ε : ℝ) : ℝ :=
  (Nat.card {f : Labeling n // HasTwoPeaks f ∧ PeaksApart ε f} : ℝ) /
    (Nat.card {f : Labeling n // HasTwoPeaks f} : ℝ)

/-- `ρ_n / n` converges in distribution to `0`: for every `ε > 0`,
`P(ρ_n / n > ε) → 0` as `n → ∞`. -/
theorem main : ∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => probFar n ε) atTop (𝓝 0) := by
  sorry

end OMA.S_burdzy_twin_peaks_grid
