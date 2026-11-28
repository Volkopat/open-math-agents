import Mathlib

/-!
# Erdős Problem 836

Source: https://www.erdosproblems.com/836
Credit: @mgv27

Let $r\geq 2$ and $G$ be a $r$-uniform hypergraph with chromatic number $3$ (that is, there is a
$3$-colouring of the vertices of $G$ such that no edge is monochromatic). Suppose any two edges
of $G$ have a non-empty intersection. Must $G$ contain $O(r^2)$ many vertices? Must there be two
edges which meet in $\gg r$ many vertices?

Formalization notes:
* `main` states the second question. The first has a negative answer (Alon's example on the
  source page has `≍ 4^r / √r` vertices), so it is not stated here.
* Hypergraphs are finite: a finite set `E` of edges, each an `r`-element set of natural numbers.
* Chromatic number `3` means: some colouring with 3 colours leaves no edge monochromatic, and no
  colouring with 2 colours does. (The page's parenthesis only gives the first half, but
  "chromatic number 3" needs both; without the second half a single edge would be an example
  with no two edges at all.)
* "Two edges which meet in `≫ r` many vertices" is: there is a constant `c > 0`, independent of
  `r` and `G`, such that two distinct edges share at least `c r` vertices.
* Erdős and Lovász proved the weaker bound `≫ r / log r`; the Fano plane (`r = 3`) is an
  example where no two edges meet in `r - 1` vertices.
-/

namespace OMA.S_erdos_836

/-- No edge of `E` is monochromatic under the colouring `f`. -/
def Proper {α : Type} (E : Finset (Finset ℕ)) (f : ℕ → α) : Prop :=
  ∀ e ∈ E, ∃ x ∈ e, ∃ y ∈ e, f x ≠ f y

/-- Erdős Problem 836: must an intersecting `r`-uniform hypergraph of chromatic number 3 have two
edges which meet in `≫ r` vertices? -/
theorem main : ∃ c > (0 : ℝ), ∀ r ≥ 2, ∀ E : Finset (Finset ℕ),
    (∀ e ∈ E, e.card = r) →
    (∀ e ∈ E, ∀ e' ∈ E, (e ∩ e').Nonempty) →
    (∃ f : ℕ → Fin 3, Proper E f) →
    (¬ ∃ f : ℕ → Fin 2, Proper E f) →
    ∃ e ∈ E, ∃ e' ∈ E, e ≠ e' ∧ c * r ≤ (e ∩ e').card := by
  sorry

end OMA.S_erdos_836
