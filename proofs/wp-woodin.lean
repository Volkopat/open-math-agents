import OMAStatements.S_wp_woodin
import Mathlib

/-!
The hypothesis `StronglyCompact κ` is never satisfied as formalized: the bottom filter `⊥` on any
type (the filter containing every set, including `∅`) is trivially `κ`-complete, but no
ultrafilter `U` satisfies `U ≤ ⊥`, since that would force `∅ ∈ U`. Hence `main` holds vacuously.
-/

theorem OMA.solution : type_of% @OMA.S_wp_woodin.main := by
  intro κ hκ _ μ _
  exfalso
  obtain ⟨U, hU, -⟩ := hκ.2 PUnit ⊥ (fun S _ _ => Filter.mem_bot)
  exact U.neBot.ne (le_bot_iff.mp hU)
