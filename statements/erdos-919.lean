import Mathlib

/-!
# Erdős Problem 919

Source: https://www.erdosproblems.com/919
Credit: @mgv27

Is there a graph $G$ with vertex set $\omega_2^2$ and chromatic number $\aleph_2$ such that every
subgraph whose vertices have a lesser type has chromatic number $\leq \aleph_0$? What if instead
we ask for $G$ to have chromatic number $\aleph_1$?

Formalization notes:
* `main` states the first question. The second (chromatic number `ℵ₁`) is not stated.
* The vertex set `ω₂²` is the set of ordinals below `ω₂ · ω₂` (ordinal product, which equals the
  ordinal power `ω₂^2`), with `ω₂ = (ℵ₂).ord`, ordered as ordinals.
* "Subgraph whose vertices have a lesser type" is the induced subgraph on a vertex set `S` whose
  order type (with the induced ordinal order) is strictly less than `ω₂²`. Taking induced
  subgraphs loses nothing, since chromatic number is monotone under passing to subgraphs.
* Chromatic number `≤ ℵ₀` means a proper colouring with colours in `ℕ`.
* Chromatic number `ℵ₂`: since the vertex set has cardinality `ℵ₂`, colouring by the identity
  shows it is at most `ℵ₂`; so it equals `ℵ₂` iff there is no proper colouring with `ℵ₁`
  colours, i.e. with colours in the ordinals below `ω₁ = (ℵ₁).ord`.
* The source records an Erdős–Hajnal construction on `ω₂²` with chromatic number `ℵ₂` where every
  smaller subgraph has chromatic number `≤ ℵ₁` (rather than `≤ ℵ₀`).
-/

namespace OMA.S_erdos_919

/-- The ordinal `ω₂²`. -/
noncomputable def omega2sq : Ordinal.{0} := (Cardinal.aleph 2).ord * (Cardinal.aleph 2).ord

/-- The vertex set: ordinals below `ω₂²`. -/
abbrev V := Set.Iio omega2sq

/-- Erdős Problem 919: is there a graph on `ω₂²` with chromatic number `ℵ₂` all of whose
subgraphs on vertex sets of smaller order type have chromatic number `≤ ℵ₀`? -/
theorem main : ∃ G : SimpleGraph V,
    (¬ Nonempty (G.Coloring (Set.Iio (Cardinal.aleph.{0} 1).ord))) ∧
    ∀ S : Set V, Ordinal.type ((· < ·) : S → S → Prop) < Ordinal.lift.{1} omega2sq →
      Nonempty ((G.induce S).Coloring ℕ) := by
  sorry

end OMA.S_erdos_919
