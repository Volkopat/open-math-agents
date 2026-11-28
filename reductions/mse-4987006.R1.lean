import OMAStatements.S_mse_4987006
import Mathlib

/-!
# Reduction of MSE 4987006: are cages Hamiltonian?

Classical slice, not progress on the question. A simple graph has girth at least `3`, so a cage
of girth `g ≤ 2` does not exist, and the `(r, 3)`-cages are exactly the complete graphs
`K_(r+1)`: an `r`-regular graph has at least `r + 1` vertices, `K_(r+1)` is `r`-regular of
girth `3`, and an `r`-regular graph on `r + 1` vertices is complete. A complete graph on at
least `3` vertices is Hamiltonian. This is `H1`.

`H2` is the open core: every `(r, g)`-cage with `r ≥ 3`, `g ≥ 4`, other than the Petersen graph,
is Hamiltonian.
-/

namespace OMA.R_mse_4987006_R1

open SimpleGraph

def H1 : Prop :=
  ∀ r g n : ℕ, 3 ≤ r → g ≤ 3 → ∀ G : SimpleGraph (Fin n),
    OMA.S_mse_4987006.IsCage r g n G → G.IsHamiltonian

def H2 : Prop :=
  ∀ r g n : ℕ, 3 ≤ r → 4 ≤ g → ∀ G : SimpleGraph (Fin n),
    OMA.S_mse_4987006.IsCage r g n G → IsEmpty (G ≃g OMA.S_mse_4987006.petersenGraph) →
      G.IsHamiltonian

theorem main : H1 → H2 → type_of% @OMA.S_mse_4987006.main := by
  intro h1 h2 r g n hr G hG hP
  by_cases hg : g ≤ 3
  · exact h1 r g n hr hg G hG
  · exact h2 r g n hr (by omega) G hG hP

end OMA.R_mse_4987006_R1
