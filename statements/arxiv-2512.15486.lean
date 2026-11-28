import Mathlib

/-!
# Panchromatic and bipanchromatic numbers of hypergraphs

Source: https://arxiv.org/abs/2512.15486 (Mohammed Lalou, Nader Mbarek, Abdallah Skender and
Olivier Togni, Completely independent spanning trees in split graphs: structural properties and
complexity), Conjecture 1 (Section 5, Concluding remarks), with the definitions of Section 2.
Credit: @JamesSlash

Definitions of the source (Section 2), for a hypergraph `H` with finite vertex set `V` and set of
hyperedges `E`:
* a panchromatic `k`-colouring assigns to every vertex one of `k` colours so that each hyperedge
  contains at least one vertex of each colour;
* a colour is unique if it appears on exactly one vertex;
* a panchromatic `k`-colouring is bipanchromatic if each of the `k` colours appears at least twice
  (it has no unique colour);
* the panchromatic number `χ_p(H)` (resp. the bipanchromatic number `χ²_p(H)`) is the maximum `k`
  such that `H` admits a panchromatic (resp. bipanchromatic) `k`-colouring;
* `α_k(H)` is the minimum number of unique colours (equivalently, of vertices of unique colour)
  among all panchromatic `k`-colourings of `H`.

Conjecture 1: every hypergraph `H` satisfies `χ²_p(H) = χ_p(H) - ⌈α_{χ_p(H)}(H) / 2⌉`.

Formalization notes:
* Colours are the elements of `Fin k`. The vertex set is a finite type `V` and the hyperedges form
  a finite set `E` of finite subsets of `V`.
* The three quantities are maxima and a minimum, which exist only for some hypergraphs (with no
  hyperedge at all, every colouring is panchromatic and `χ_p` is not defined). The statement says
  that the equality holds whenever they exist: `p`, `a`, `b` are the values of `χ_p(H)`,
  `α_{χ_p(H)}(H)` and `χ²_p(H)`, given by `IsGreatest` / `IsLeast`. The ceiling is taken in `ℚ`
  and the equality is read in `ℤ`.
-/

namespace OMA.S_arxiv_2512_15486

variable {V : Type} [Fintype V]

/-- The number of vertices with colour `c` under `φ`. -/
def colorCount {k : ℕ} (φ : V → Fin k) (c : Fin k) : ℕ :=
  (Finset.univ.filter fun v => φ v = c).card

/-- `φ` is a panchromatic colouring: every hyperedge contains a vertex of every colour. -/
def IsPanchromatic (E : Finset (Finset V)) {k : ℕ} (φ : V → Fin k) : Prop :=
  ∀ e ∈ E, ∀ c : Fin k, ∃ v ∈ e, φ v = c

/-- `φ` is a bipanchromatic colouring: panchromatic, and every colour appears at least twice. -/
def IsBipanchromatic (E : Finset (Finset V)) {k : ℕ} (φ : V → Fin k) : Prop :=
  IsPanchromatic E φ ∧ ∀ c : Fin k, 2 ≤ colorCount φ c

/-- The number of unique colours of `φ`: colours that appear on exactly one vertex. -/
def numUnique {k : ℕ} (φ : V → Fin k) : ℕ :=
  (Finset.univ.filter fun c : Fin k => colorCount φ c = 1).card

theorem main : ∀ (V : Type) [Fintype V] (E : Finset (Finset V)) (p a b : ℕ),
    IsGreatest {k : ℕ | ∃ φ : V → Fin k, IsPanchromatic E φ} p →
    IsLeast {u : ℕ | ∃ φ : V → Fin p, IsPanchromatic E φ ∧ numUnique φ = u} a →
    IsGreatest {k : ℕ | ∃ φ : V → Fin k, IsBipanchromatic E φ} b →
    (b : ℤ) = p - ⌈(a : ℚ) / 2⌉ := by
  sorry

end OMA.S_arxiv_2512_15486
