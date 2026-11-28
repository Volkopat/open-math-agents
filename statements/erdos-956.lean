import Mathlib

/-!
# Erdős Problem 956

Source: https://www.erdosproblems.com/956
Credit: @mgv27

If $C,D\subseteq \mathbb{R}^2$ then the distance between $C$ and $D$ is defined by
\[\delta(C,D)=\inf_{\substack{c\in C\\ d\in D}}\| c-d\|.\]
Let $h(n)$ be the maximal number of unit distances between disjoint convex translates. That is,
the maximal $m$ such that there is a compact convex set $C\subset \mathbb{R}^2$ and a set $X$ of
size $n$ such that all $(C+x)_{x\in X}$ are disjoint and there are $m$ pairs $x_1,x_2\in X$ such
that \[\delta(C+x_1,C+x_2)=1.\]
Determine $h(n)$ - in particular, prove that there exists a constant $c>0$ such that
$h(n)>n^{1+c}$ for all large $n$.

Formalization notes:
* `main` states the precise sub-question. Rather than define `h(n)` as a supremum, it says
  directly: there are `c > 0` and `N` such that for every `n ≥ N` some configuration of `n`
  disjoint translates has more than `n^{1+c}` unit-distance pairs (equivalent to `h(n) > n^{1+c}`).
* `C` is a nonempty compact convex subset of `ℝ²` (Euclidean plane); the empty set is excluded
  (it would give no unit distances anyway). "Disjoint" means pairwise disjoint translates for
  distinct `x ∈ X`.
* `δ` is the infimum of `‖c - d‖` over `c ∈ C + x₁`, `d ∈ C + x₂`.
* Pairs are unordered pairs of distinct points; we count ordered pairs `(x₁, x₂)` with
  `x₁ ≠ x₂` and halve.
* The source records `h(n) ≪ n^{4/3}` (Erdős–Pach) and `h(n) ≥ f(n)`, the unit distance function.
-/

namespace OMA.S_erdos_956

/-- The Euclidean plane. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/-- The translate `C + x`. -/
def translate (C : Set Plane) (x : Plane) : Set Plane := (fun p => p + x) '' C

/-- `δ(C, D) = inf_{c ∈ C, d ∈ D} ‖c - d‖`. -/
noncomputable def delta (C D : Set Plane) : ℝ :=
  sInf {r : ℝ | ∃ c ∈ C, ∃ d ∈ D, r = ‖c - d‖}

/-- The number of unordered pairs `{x₁, x₂}` of distinct points of `X` with
`δ(C + x₁, C + x₂) = 1`. -/
noncomputable def unitPairs (C : Set Plane) (X : Finset Plane) : ℝ :=
  ((X.offDiag.filter (fun p => delta (translate C p.1) (translate C p.2) = 1)).card : ℝ) / 2

/-- Erdős Problem 956: there is `c > 0` with `h(n) > n^{1+c}` for all large `n`. -/
theorem main : ∃ c > (0 : ℝ), ∃ N : ℕ, ∀ n ≥ N, ∃ C : Set Plane, C.Nonempty ∧ IsCompact C ∧
    Convex ℝ C ∧ ∃ X : Finset Plane, X.card = n ∧
      (∀ x ∈ X, ∀ y ∈ X, x ≠ y → Disjoint (translate C x) (translate C y)) ∧
      (n : ℝ) ^ (1 + c) < unitPairs C X := by
  sorry

end OMA.S_erdos_956
