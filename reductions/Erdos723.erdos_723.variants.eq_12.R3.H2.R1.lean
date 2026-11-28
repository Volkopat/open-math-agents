import OMAReductions.R_Erdos723_erdos_723_variants_eq_12_R3

/-!
# Splitting R3.H2 at the gap

The author of the merged reduction R3 states the intended proof of its hypothesis H2 as: append to each of
the 103 ten-cell certificate sets the three labels it omits (each `B i` is injective in row, column and
symbol with 10 cells, so it misses exactly one value in each coordinate), add the 36 lines determined by the
triangle, obtain 139 thirteen-point lines meeting pairwise in exactly one point, and then "the extension
completes them to 157".

This reduction separates those two halves, so that the second one is no longer hidden inside a word:
* `H1` is the construction: the certificate yields 139 such lines on 157 points.
* `H2` is the completion: any 139 such lines extend to all 157 lines.
`main` is then only the composition of the two.

Why the split matters: completion of 139 lines is *not* covered by any known theorem. Metsch's bound for a
partial plane of order `n` with no disjoint lines is `n^2 - n/6 = 142` at `n = 12`, and embedding is forced
only above 142 lines (that statement is R1.H2, already proved, and it does not apply at 139). So `H2` is the
honest name of the remaining mathematical work, and `H1` is the part the author reports as verified.
-/

namespace OMA.R_Erdos723_erdos_723_variants_eq_12_R3_H2_R1

/-- The certificate produces 139 thirteen-point lines that meet pairwise in exactly one point. -/
def H1 : Prop :=
  ∀ (s : (Fin 11 × Fin 11) → Fin 11) (B : Fin 103 → Finset (Fin 11 × Fin 11)),
    let c : Fin 3 → (Fin 11 × Fin 11) → Fin 11 := ![Prod.fst, Prod.snd, s]
    (∀ r : Fin 11, Function.Injective (fun k : Fin 11 => s (r,k))) →
    (∀ k : Fin 11, Function.Injective (fun r : Fin 11 => s (r,k))) →
    (∀ i, (B i).card = 10 ∧ ∀ d, Set.InjOn (c d) (B i : Set (Fin 11 × Fin 11))) →
    (∀ i j, i ≠ j →
      (B i ∩ B j).card + (Finset.univ.filter (fun d : Fin 3 =>
        ∃ a : Fin 11, a ∉ (B i).image (c d) ∧ a ∉ (B j).image (c d))).card = 1) →
    ∃ M : Fin 139 → Finset (Fin 157), (∀ i, (M i).card = 13) ∧
      ∀ i j, i ≠ j → ∃! p, p ∈ M i ∧ p ∈ M j

/-- 139 pairwise-intersecting thirteen-point lines on 157 points extend to all 157 lines of a plane. -/
def H2 : Prop :=
  ∀ M : Fin 139 → Finset (Fin 157), (∀ i, (M i).card = 13) ∧
    (∀ i j, i ≠ j → ∃! p, p ∈ M i ∧ p ∈ M j) →
  ∃ L : Fin 157 → Finset (Fin 157), (∀ i, (L i).card = 13) ∧
    ∀ i j, i ≠ j → ∃! p, p ∈ L i ∧ p ∈ L j

theorem main : H1 → H2 → OMA.R_Erdos723_erdos_723_variants_eq_12_R3.H2 := by
  intro h1 h2 s B
  dsimp only
  intro rows cols sz meet
  obtain ⟨M, hM⟩ := h1 s B rows cols sz meet
  exact h2 M hM

end OMA.R_Erdos723_erdos_723_variants_eq_12_R3_H2_R1
