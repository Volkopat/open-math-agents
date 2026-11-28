import Mathlib

/-!
# Representation number of word-representable graphs

Source: https://en.wikipedia.org/wiki/Word-representable_graph
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Open problem (Wikipedia): are there any graphs on `n` vertices whose representation requires more
than `⌊n/2⌋` copies of each letter?

Conventions:
* Graphs are finite simple graphs on `Fin n`. Letters `x ≠ y` alternate in a word `w` if, after
  deleting all other letters, no two consecutive letters are equal. A word `w` over the vertex
  set represents `G` if every vertex occurs in `w` and, for `x ≠ y`, `x` and `y` are adjacent iff
  they alternate in `w`. `G` is `k`-representable if some representing word contains each letter
  exactly `k` times; a graph is word-representable iff it is `k`-representable for some `k`, and
  its representation number is the least such `k`.
* "Requires more than `⌊n/2⌋` copies": `G` is word-representable but not `k`-representable for
  any `k ≤ ⌊n/2⌋`.
* The source asks a yes/no question; `main` states the answer yes, and a disproof would answer
  no.
-/

namespace OMA.S_wp_representation

/-- `x` and `y` alternate in `w`. -/
def Alternate {n : ℕ} (w : List (Fin n)) (x y : Fin n) : Prop :=
  (w.filter (fun z => z = x ∨ z = y)).Chain' (· ≠ ·)

/-- `w` represents `G` with exactly `k` copies of each letter. -/
def KRepresents {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) (w : List (Fin n)) : Prop :=
  (∀ v, w.count v = k) ∧ ∀ x y, x ≠ y → (G.Adj x y ↔ Alternate w x y)

theorem main :
    ∃ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∃ k ≥ 1, ∃ w, KRepresents G k w) ∧ ∀ k ≤ n / 2, ∀ w, ¬ KRepresents G k w := by
  sorry

end OMA.S_wp_representation
