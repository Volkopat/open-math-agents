import Mathlib

/-!
# Vertex-cover integrality gap

Source: https://www.openproblemgarden.org/op/vertex_cover_integrality_gap
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Atserias–Dawar): for every `ε > 0` there is `δ > 0` such that for every large `n`
there are `n`-vertex graphs `G, H` with `G ≡^C_{δn} H` and `vc(G) ≥ (2 - ε) vc(H)`.

Conventions.
* `≡^C_k` is indistinguishability in `k`-variable first-order logic with counting
  quantifiers. We use Hella's characterisation by the bijective `k`-pebble game: `G ≡^C_k H`
  iff Duplicator has a winning strategy, i.e. there is a set `W` of positions containing the
  empty one, each a partial isomorphism, closed under Spoiler's moves (for every position and
  pebble `i`, Duplicator picks a bijection `f` and every placement `(v, f v)` of pebble pair
  `i` stays in `W`).
* `k = ⌊δ n⌋`. "For every large `n`": there is `N` with the property for all `n ≥ N`.
* `vc(G)`: minimum size of a vertex cover.
-/

namespace OMA.S_opg_vertex_cover_integrality_gap

open SimpleGraph

variable {n : ℕ}

/-- A position: for each pebble pair, either unplaced or placed on `(a, b)`. -/
abbrev Position (n k : ℕ) := Fin k → Option (Fin n × Fin n)

/-- The pebbled pairs form a partial isomorphism from `G` to `H`. -/
def PartialIso (G H : SimpleGraph (Fin n)) {k : ℕ} (p : Position n k) : Prop :=
  ∀ i j a b a' b', p i = some (a, b) → p j = some (a', b') →
    (a = a' ↔ b = b') ∧ (G.Adj a a' ↔ H.Adj b b')

/-- `G ≡^C_k H`, via the bijective `k`-pebble game. -/
def CountingEquiv (k : ℕ) (G H : SimpleGraph (Fin n)) : Prop :=
  ∃ W : Set (Position n k), (fun _ => none) ∈ W ∧
    (∀ p ∈ W, PartialIso G H p) ∧
    ∀ p ∈ W, ∀ i : Fin k, ∃ f : Fin n ≃ Fin n,
      ∀ v : Fin n, Function.update p i (some (v, f v)) ∈ W

/-- Minimum vertex cover size. -/
noncomputable def vc (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {c | ∃ C : Finset (Fin n), C.card = c ∧ ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C}

/-- Atserias–Dawar conjecture. -/
theorem main :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ N : ℕ, ∀ n ≥ N,
      ∃ G H : SimpleGraph (Fin n), CountingEquiv ⌊δ * n⌋₊ G H ∧
        (2 - ε) * (vc H : ℝ) ≤ vc G := by
  sorry

end OMA.S_opg_vertex_cover_integrality_gap
