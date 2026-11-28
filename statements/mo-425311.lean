import Mathlib

/-!
# A common figure tiled by each of finitely many lattice dominoes

The dominoes are arbitrary two-point subsets of the integer plane. The figure
is finite and nonempty, with a separate tiling by translates of each domino.

[MathOverflow question](https://mathoverflow.net/questions/425311/does-any-set-of-dominoes-tile-some-common-figure)
[Keevash and Lim](https://arxiv.org/abs/2611.33154)
-/

namespace OMA.S_mo_425311

abbrev Lattice := ℤ × ℤ

def TilesByTranslation (D B : Finset Lattice) : Prop :=
  let placement (t : Lattice) : Set Lattice :=
    (fun x => t + x) '' (D : Set Lattice)
  ∃ shifts : Finset Lattice,
    (shifts : Set Lattice).PairwiseDisjoint placement ∧
      (B : Set Lattice) = ⋃ t ∈ (shifts : Set Lattice), placement t

theorem main :
    ∀ (n : ℕ) (D : Fin n → Finset Lattice),
      (∀ i, (D i).card = 2) →
        ∃ B : Finset Lattice, B.Nonempty ∧ ∀ i, TilesByTranslation (D i) B := by
  sorry

end OMA.S_mo_425311
