import OMAStatements.S_opg_universal_highly_arc_transitive_digraphs

/-!
An elementary finite witness for the exact written statement: the bidirected
triangle. The extra nonbacktracking condition in IsSArc makes every arc
determined by its first two vertices.

Scope: this does not formalize the intended infinite digraph construction.
The directed-arc definition in DeVos, Mohar and Samal, Highly arc-transitive
digraphs—structure and counterexamples, arXiv:1110.2945v2, Section1, has no
nonbacktracking restriction (non-refereed arXiv version,
https://doi.org/10.48550/arXiv.1110.2945).

Credit: @lzvxck, statement PR7084. Problem source: Cameron, Praeger and
Wormald, Universal highly arc transitive digraphs, Open Problem Garden
(2007, non-refereed),
https://www.openproblemgarden.org/op/universal_highly_arc_transitive_digraphs .
All proof code here is independent.
-/

namespace OMA.UniversalHAT

open OMA.S_opg_universal_highly_arc_transitive_digraphs

def triangle : Digraph (Fin 3) := ⟨fun a b => a ≠ b⟩

instance : DecidableRel triangle.Adj := fun a b => inferInstanceAs (Decidable (a ≠ b))

lemma third_unique : ∀ a b c d : Fin 3,
    a ≠ b → c ≠ a → c ≠ b → d ≠ a → d ≠ b → c = d := by decide +kernel

lemma ordered_pairs : ∀ a b c d : Fin 3, a ≠ b → c ≠ d →
    ∃ σ : Fin 3 ≃ Fin 3, σ a = c ∧ σ b = d := by decide +kernel

lemma high : IsHighlyArcTransitive triangle := by
  intro s x y hx hy
  cases s with
  | zero =>
    refine ⟨Equiv.swap (x 0) (y 0), ?_, ?_⟩
    · intro a b
      exact (Equiv.swap (x 0) (y 0)).injective.ne_iff
    · intro i
      have hi : i = 0 := Fin.eq_zero i
      subst i
      exact Equiv.swap_apply_left _ _
  | succ t =>
    have hx01 : x 0 ≠ x 1 := hx.1 ⟨0, by omega⟩
    have hy01 : y 0 ≠ y 1 := hy.1 ⟨0, by omega⟩
    obtain ⟨σ, h0, h1⟩ := ordered_pairs _ _ _ _ hx01 hy01
    refine ⟨σ, fun _ _ => σ.injective.ne_iff, ?_⟩
    have maps (i : ℕ) : ∀ hi : i < t + 2, σ (x ⟨i, hi⟩) = y ⟨i, hi⟩ := by
      induction i using Nat.twoStepInduction with
      | zero => intro hi; exact h0
      | one => intro hi; exact h1
      | more i ih0 ih1 =>
        intro hi
        have hi0 : i < t+2 := by omega
        have hi1 : i+1 < t+2 := by omega
        have hxa : x ⟨i+2, hi⟩ ≠ x ⟨i, hi0⟩ := (hx.2 i hi).symm
        have hxb : x ⟨i+2, hi⟩ ≠ x ⟨i+1, hi1⟩ := (hx.1 ⟨i+1, by omega⟩).symm
        have hya : y ⟨i+2, hi⟩ ≠ y ⟨i, hi0⟩ := (hy.2 i hi).symm
        have hyb : y ⟨i+2, hi⟩ ≠ y ⟨i+1, hi1⟩ := (hy.1 ⟨i+1, by omega⟩).symm
        apply third_unique (y ⟨i, hi0⟩) (y ⟨i+1, hi1⟩)
        · exact hy.1 ⟨i, by omega⟩
        · rw [← ih0 hi0]
          exact σ.injective.ne hxa
        · rw [← ih1 hi1]
          exact σ.injective.ne hxb
        · exact hya
        · exact hyb
    intro i
    exact maps i.val i.isLt

def tour (i : Fin 7) : Fin 3 := ⟨i.val % 3, Nat.mod_lt _ (by decide)⟩

lemma tour_edges : ∀ i : Fin 6,
    triangle.Adj (altEdge tour true i).1 (altEdge tour true i).2 := by decide +kernel

lemma tour_covers : ∀ a b : Fin 3, a ≠ b →
    ∃ i : Fin 6, altEdge tour true i = (a,b) := by decide +kernel

lemma universal : IsUniversal triangle := by
  intro a b c d hab hcd
  exact ⟨6, tour, true, tour_edges, tour_covers a b hab, tour_covers c d hcd⟩

end OMA.UniversalHAT

theorem OMA.solution : type_of% @OMA.S_opg_universal_highly_arc_transitive_digraphs.main := by
  refine ⟨Fin 3, OMA.UniversalHAT.triangle, ?_, ?_, ?_,
    OMA.UniversalHAT.high, OMA.UniversalHAT.universal⟩
  · intro v h
    exact h rfl
  · exact ⟨0, 1, by decide⟩
  · intro v
    exact ⟨Set.toFinite _, Set.toFinite _⟩
