import Mathlib

/-!
# Cores of Cayley graphs (cube-like case)

Source: https://www.openproblemgarden.org/op/cores_of_cayley_graphs
Credit: @shc261392

Problem (Šámal): let `M` be an abelian group. Is the core of a Cayley graph on some power of `M`
a Cayley graph on some power of `M`? The source notes that even the case `M = ℤ₂` is open;
Cayley graphs on powers of `ℤ₂` are the cube-like graphs.

A comment on the source page reports that the question has a negative answer for `M = ℤ₁₅`
(a Cayley graph on `ℤ₁₅` with a 5-cycle as its core), so this file states the case `M = ℤ₂`,
in the affirmative: the core of every cube-like graph is cube-like. This is the open conjecture
of Nešetřil and Šámal, stated as open in *Cores of cubelike graphs* (arXiv:1808.02051).

Reading used here:
* The cube-like graph `cay k S` has vertex set `Fin k → ZMod 2`, with `x` adjacent to `y` when
  `x ≠ y` and `x - y ∈ S` (in characteristic two this relation is symmetric).
* A core of a finite graph `G` is a finite graph `H` that is homomorphically equivalent to `G`
  (there are homomorphisms both ways) and all of whose endomorphisms are bijective. Every finite
  graph has a core, unique up to isomorphism.
-/

namespace OMA.S_opg_cores_of_cayley_graphs

/-- The cube-like graph (Cayley graph on `(ZMod 2)^k`) with connection set `S`. -/
def cay (k : ℕ) (S : Set (Fin k → ZMod 2)) : SimpleGraph (Fin k → ZMod 2) :=
  SimpleGraph.fromRel fun x y => x - y ∈ S

theorem main :
    ∀ (k : ℕ) (S : Set (Fin k → ZMod 2)) (W : Type) [Fintype W] (H : SimpleGraph W),
      Nonempty (cay k S →g H) → Nonempty (H →g cay k S) →
      (∀ f : H →g H, Function.Bijective f) →
        ∃ (j : ℕ) (T : Set (Fin j → ZMod 2)), Nonempty (H ≃g cay j T) := by
  sorry

end OMA.S_opg_cores_of_cayley_graphs
