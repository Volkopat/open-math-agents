import Mathlib

/-!
# Erdős Problem 1155

Source: https://www.erdosproblems.com/1155
Credit: @mgv27

Construct a random graph on $n$ vertices in the following way: begin with the complete graph
$K_n$. At each stage, choose uniformly a random triangle in the graph and delete all the edges of
this triangle. Repeat until the graph is triangle-free.

Describe the typical parameters and structure of such a graph. In particular, if $f(n)$ is the
number of edges remaining, then is it true that
\[\mathbb{E}f(n)\asymp n^{3/2}\]
and that $f(n) \ll n^{3/2}$ almost surely?

Formalization notes:
* "Describe the typical parameters and structure" is vague. `main` states the first precise
  question, `𝔼 f(n) ≍ n^{3/2}`. The second (`f(n) ≪ n^{3/2}` almost surely) is not stated.
* A graph on `Fin n` is a finset `E` of non-diagonal unordered pairs. A triangle of `E` is a
  3-element vertex set all of whose pairs are edges of `E`. Deleting the triangle `t` removes its
  three edges: `E \ t.sym2` (the diagonal pairs in `t.sym2` are never in `E`).
* The expectation is computed exactly by the recursion: a triangle-free `E` gives `|E|`, and
  otherwise the expectation is the average, over the (uniformly chosen) triangles `t` of `E`, of
  the expectation starting from `E \ t.sym2`. This avoids building a probability space.
* The recursion carries a fuel parameter so that it is structural. Each step deletes 3 edges, so
  the process stops after at most `n(n-1)/6 ≤ n²` steps. With fuel `n²` the fuel never runs out,
  so the fallback value at fuel `0` never matters.
* A quick independent Python check of the process (exact rationals) gives `𝔼 f(n) = 0, 1, 0, 3, 4,
  18/5` for `n = 1, …, 6`. For example, `K_4` always ends with a 3-edge star.
* `≍` is spelled out as: there are constants `c > 0`, `C > 0` and `N₀` with
  `c n^{3/2} ≤ 𝔼 f(n) ≤ C n^{3/2}` for all `n ≥ N₀`.
* Known: Grable proved `ℙ(f(n) > n^{7/4+ε}) → 0`. Bohman, Frieze and Lubetzky proved
  `f(n) = n^{3/2+o(1)}` almost surely.
-/

namespace OMA.S_erdos_1155

open Filter

/-- The edges of the complete graph `K_n`: all non-diagonal unordered pairs. -/
def completeEdges (n : ℕ) : Finset (Sym2 (Fin n)) :=
  (Finset.univ : Finset (Fin n)).sym2.filter fun e => ¬ e.IsDiag

/-- The triangles of the graph with edge set `E`: 3-element vertex sets whose pairs all lie
in `E`. -/
def triangles {n : ℕ} (E : Finset (Sym2 (Fin n))) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard 3).filter fun t => ∀ x ∈ t, ∀ y ∈ t, x ≠ y → s(x, y) ∈ E

/-- The expected number of edges left when the random triangle-removal process is started from
`E`, with `m` steps of fuel. -/
noncomputable def expRemaining {n : ℕ} : ℕ → Finset (Sym2 (Fin n)) → ℚ
  | 0, E => E.card
  | m + 1, E =>
    if triangles E = ∅ then E.card
    else (∑ t ∈ triangles E, expRemaining m (E \ t.sym2)) / (triangles E).card

/-- `𝔼 f(n)`: the expected number of edges remaining when the process starts from `K_n`. -/
noncomputable def expectedF (n : ℕ) : ℚ :=
  expRemaining (n ^ 2) (completeEdges n)

/-- Erdős Problem 1155: is `𝔼 f(n) ≍ n^{3/2}`? -/
theorem main : ∃ c > (0 : ℝ), ∃ C > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    c * (n : ℝ) ^ ((3 : ℝ) / 2) ≤ (expectedF n : ℝ) ∧
      (expectedF n : ℝ) ≤ C * (n : ℝ) ^ ((3 : ℝ) / 2) := by
  sorry

end OMA.S_erdos_1155
