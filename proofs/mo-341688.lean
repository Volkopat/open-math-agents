import OMAStatements.S_mo_341688
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith

/-! # Five four-cycles distinguish graph decompositions from square tilings
Research and Lean verification by @LDJAI with OpenAI Codex. -/
namespace OMA.S_mo_341688

abbrev Tile := Fin 5 ⊕ Fin 5

def side : Tile → ℕ := Sum.elim (fun _ => 2) (fun _ => 1)

private def rows : Tile → Finset (Fin 5)
  | .inl i => {i, i+1}
  | .inr i => {i}

private def cols : Tile → Finset (Fin 5)
  | .inl i => {2*i, 2*i+1}
  | .inr i => {2*i+2}

theorem graph_realization : HasBicliqueDecomposition 5 side := by
  refine ⟨rows, cols, ?_, ?_⟩
  · decide +kernel
  · change ∀ a b : Fin 5, ∃ i : Tile, (a ∈ rows i ∧ b ∈ cols i) ∧
      ∀ j : Tile, (a ∈ rows j ∧ b ∈ cols j) → j = i
    decide +kernel

private noncomputable def half (u : ℝ) : Bool := decide (u < 3/2)

private lemma same_half {a b : ℝ} (_ha : 0 ≤ a) (ha' : a + 2 ≤ 5)
    (hb : 0 ≤ b) (_hb' : b + 2 ≤ 5) (h : half a = half b) : a < b + 2 := by
  by_cases h₁ : a < 3/2
  · linarith
  · have h₂ : ¬ b < 3/2 := by
      intro h₂
      simp [half, h₁, h₂] at h
    linarith

theorem no_square_tiling : ¬ HasSquareTiling 5 side := by
  rintro ⟨x, y, inside, disjoint, _⟩
  let zone (i : Fin 5) := (half (x (.inl i)), half (y (.inl i)))
  obtain ⟨i,j,ne,eq⟩ := Fintype.exists_ne_map_eq_of_card_lt zone (by decide)
  have hx : half (x (.inl i)) = half (x (.inl j)) := congrArg Prod.fst eq
  have hy : half (y (.inl i)) = half (y (.inl j)) := congrArg Prod.snd eq
  obtain ⟨ix, iX, iy, iY⟩ := inside (.inl i)
  obtain ⟨jx, jX, jy, jY⟩ := inside (.inl j)
  have hd := disjoint (.inl i) (.inl j) (fun h => ne (Sum.inl.inj h))
  simp only [side, Sum.elim_inl, Nat.cast_ofNat] at iX iY jX jY hd
  exact hd.elim (not_le.mpr (same_half jx jX ix iX hx.symm)) (fun rest =>
    rest.elim (not_le.mpr (same_half ix iX jx jX hx)) (fun rest' =>
      rest'.elim (not_le.mpr (same_half jy jY iy iY hy.symm))
        (not_le.mpr (same_half iy iY jy jY hy))))

/-- The graph-realizable multisets of side lengths need not be geometrically
realizable. This refutes the universal converse using five twos and five ones. -/
theorem counterexample : HasBicliqueDecomposition 5 side ∧ ¬ HasSquareTiling 5 side :=
  ⟨graph_realization, no_square_tiling⟩

end OMA.S_mo_341688

open OMA.S_mo_341688

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_341688.main) := by
  intro h
  exact no_square_tiling (h 5 Tile side (by decide) (by decide +kernel)
    (by decide +kernel) graph_realization)
