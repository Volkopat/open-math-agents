import OMAReductions.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R1
import Mathlib

-- Step PoincareConjecture.poincare_conjecture.variants.dimension_ge_five.R1.H4.R1.H3: hypothesis H3 of reduction PoincareConjecture.poincare_conjecture.variants.dimension_ge_five.R1.H4.R1
-- Credit: @ivillar
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

open Set Topology

/-! Choose a cell around each compact set. Feed each cell's compact closure, together with the next
set of the compact exhaustion, back into the choice; the resulting cells are nested and cover. -/

theorem OMA.solution : OMA.R_PoincareConjecture_poincare_conjecture_variants_dimension_ge_five_R1_H4_R1.H3 := by
  intro n N _ _ hyp
  choose! V hKV hVo hVc hVe using hyp
  let L : ℕ → Set N := fun j => Nat.rec (compactCovering N 0)
    (fun j W => closure (V W) ∪ compactCovering N (j+1)) j
  have compact (j : ℕ) : IsCompact (L j) := by
    induction j with
    | zero => exact isCompact_compactCovering N 0
    | succ j ih => exact (hVc _ ih).union (isCompact_compactCovering N _)
  have cover (j : ℕ) : compactCovering N j ⊆ L j := by
    cases j with
    | zero => exact fun _ hx => hx
    | succ j => exact subset_union_right
  refine ⟨fun j => V (L j), fun j => ⟨hVo _ (compact j), hVe _ (compact j)⟩, ?_, ?_⟩
  · intro j
    exact subset_union_left.trans (hKV _ (compact (j+1)))
  · apply eq_univ_of_univ_subset
    rw [← iUnion_compactCovering N]
    exact iUnion_mono fun j => (cover j).trans (hKV _ (compact j))
