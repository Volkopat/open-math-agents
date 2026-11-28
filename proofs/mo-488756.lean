import OMAStatements.S_mo_488756
import Mathlib

/-!
# MathOverflow 488756: unfragmented sets stay unfragmented when an element is added

Being fragmented is hereditary: if `t` is fragmented and `s ⊆ t`, then `s` is fragmented.
Indeed, follow the deletion sequence of `t`.  When it deletes `v`:

* if `v ∉ s`, then `s ⊆ t.erase v` and we continue;
* if `v ∈ s`, the deletion condition for `v` in `t` quantifies over `t.erase v ⊇ s.erase v`,
  so `v` can also be deleted from `s`, and `s.erase v ⊆ t.erase v`.

Applying this to `s ⊆ insert a s` gives the claim.
-/

namespace OMA.S_mo_488756

/-- Subsets of fragmented sets are fragmented. -/
lemma hereditary {α β : Type*} [DecidableEq α] [LE β] (w : α → α → β) {t : Finset α}
    (ht : Fragmented w t) : ∀ s ⊆ t, Fragmented w s := by
  induction ht with
  | empty =>
    intro s hs
    rw [Finset.subset_empty.mp hs]
    exact Fragmented.empty
  | @delete t v hcan _ ih =>
    intro s hs
    by_cases hv : v ∈ s
    · have hsub : s.erase v ⊆ t.erase v := Finset.erase_subset_erase v hs
      exact Fragmented.delete
        ⟨hv, fun x hx a ha b hb hab => hcan.2 x (hsub hx) a (hsub ha) b (hsub hb) hab⟩
        (ih _ hsub)
    · exact ih s (fun x hx => Finset.mem_erase.mpr ⟨fun h => hv (h ▸ hx), hs hx⟩)

end OMA.S_mo_488756

open OMA.S_mo_488756 in
theorem OMA.solution : type_of% @OMA.S_mo_488756.main := by
  intro α β _ _ w _ s a hs hins
  exact hs (hereditary w hins s (Finset.subset_insert a s))
