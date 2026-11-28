import Mathlib

/-!
# Changing one Laplacian eigenvalue

Source: jkjium, https://mathoverflow.net/questions/47858 (CC BY-SA 2.5).
Credit: @connoranderson. Aaron Meyerowitz noted the finiteness of the
unweighted problem; Tracy Hall distinguished weighted Laplacians in a comment.
The weighted realization follows the nested complete-graph construction
of Forrow, Woodhouse and Dunkel, Phys. Rev. X 8 (2018), 041043.

The common monic factor records the unchanged eigenvalues with multiplicity.
For simple graphs every nonzero displacement is an even integer, and both
changed eigenvalues must themselves be integers. The three-vertex path and
triangle attain displacement two at the smallest positive eigenvalue.
For complete graphs with positive real weights, every positive list is
realizable; the characteristic polynomial records its multiplicities.
-/
namespace OMA.S_mo_47858
open Matrix Polynomial

noncomputable def characteristic {n : ℕ} (G : SimpleGraph (Fin n)) : ℝ[X] := by
  classical exact (G.lapMatrix ℝ).charpoly

theorem main :
    (∀ (n : ℕ) (G H : SimpleGraph (Fin n)) (a b : ℝ) (R : ℝ[X]),
      R.Monic → characteristic G = (X-C a)*R → characteristic H = (X-C b)*R →
      (∃ k : ℤ, b-a=2*(k:ℝ)) ∧ (a≠b → ∃ u v : ℤ, a=(u:ℝ) ∧ b=(v:ℝ))) ∧
    (∃ G H : SimpleGraph (Fin 3), G.Connected ∧ H.Connected ∧
      characteristic G = X*(X-1)*(X-3) ∧ characteristic H = X*(X-3)^2) ∧
    (∀ (n : ℕ) (v : Fin n → ℝ), Antitone v → (∀ i, 0 < v i) →
      ∃ L : Matrix (Fin (n+1)) (Fin (n+1)) ℝ, L.IsSymm ∧
        (∀ i j, i ≠ j → L i j < 0) ∧ (∀ i, ∑ j, L i j = 0) ∧
        L.charpoly = X * ∏ i, (X-C (v i))) := by
  sorry

end OMA.S_mo_47858
