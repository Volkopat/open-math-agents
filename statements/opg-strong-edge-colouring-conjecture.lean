import Mathlib

/-!
# Strong edge colouring conjecture

Source: https://www.openproblemgarden.org/op/strong_edge_colouring_conjecture
Credit: @lzvxck

The source (Erdős–Nešetřil): a strong edge-colouring of a graph `G` is an edge-colouring in
which every colour class is an induced matching; that is, any two vertices belonging to
distinct edges with the same colour are not adjacent. The strong chromatic index `sχ'(G)` is
the minimum number of colours in a strong edge-colouring of `G`. Conjecture:
`sχ'(G) ≤ 5Δ²/4` if `Δ` is even, and `sχ'(G) ≤ (5Δ² - 2Δ + 1)/4` if `Δ` is odd.

Graphs are finite and simple; `Δ` is `G.maxDegree`. In a colour class that is an induced
matching, two distinct edges of the same colour share no vertex and no edge joins them, so the
condition is: for distinct edges `e, f` of the same colour and any `x ∈ e`, `y ∈ f`, `x ≠ y`
and `x, y` are not adjacent. Since `sχ'(G)` is an integer, `sχ'(G) ≤ B` is equivalent to the
existence of a strong edge-colouring with `m` colours where `4 m` is at most the numerator.
-/

namespace OMA.S_opg_strong_edge_colouring_conjecture

/-- `c` is a strong edge-colouring of `G`: every colour class is an induced matching. -/
def IsStrongEdgeColouring {V : Type*} (G : SimpleGraph V) {m : ℕ} (c : G.edgeSet → Fin m) :
    Prop :=
  ∀ e f : G.edgeSet, e ≠ f → c e = c f →
    ∀ x ∈ (e : Sym2 V), ∀ y ∈ (f : Sym2 V), x ≠ y ∧ ¬ G.Adj x y

/-- **Strong edge colouring conjecture.** A finite graph with maximum degree `Δ` has a strong
edge-colouring with at most `5Δ²/4` colours if `Δ` is even and at most `(5Δ² - 2Δ + 1)/4`
colours if `Δ` is odd. -/
theorem main : ∀ (V : Type) [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj],
    ∃ (m : ℕ) (c : G.edgeSet → Fin m), IsStrongEdgeColouring G c ∧
      (Even G.maxDegree → 4 * m ≤ 5 * G.maxDegree ^ 2) ∧
      (Odd G.maxDegree → 4 * m + 2 * G.maxDegree ≤ 5 * G.maxDegree ^ 2 + 1) := by
  sorry

end OMA.S_opg_strong_edge_colouring_conjecture
