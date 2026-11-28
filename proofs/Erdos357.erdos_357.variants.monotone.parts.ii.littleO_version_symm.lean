import FormalConjectures.ErdosProblems.«357»

-- Credit: @tjgksruf9801 (shorter proof; same answer n * log n, from h n ≤ n: one-term blocks
-- have distinct sums, so the terms are distinct integers of [1, n])

open Asymptotics

noncomputable def OMA.answer : ℕ → ℝ := fun n ↦ n * Real.log n

theorem OMA.solution :
    Erdos357.erdos_357.variants.monotone.parts.ii.littleO_version_symm.answer = OMA.answer →
    type_of% @Erdos357.erdos_357.variants.monotone.parts.ii.littleO_version_symm := by
  intro h
  rw [h]
  refine (isBigO_of_le _ fun n => ?_).trans_isLittleO ((isBigO_refl _ _).mul_isLittleO
    ((Real.isLittleO_const_log_atTop (c := 1)).comp_tendsto tendsto_natCast_atTop_atTop))
  simpa using (show Erdos357.h n ≤ n from csSup_le' fun k ⟨a, hr, _, hs⟩ => by
    simpa using Finset.card_le_card_of_injOn (s := .univ) (t := .Icc (1 : ℤ) n) a (fun i _ => by simpa using hr ⟨i, rfl⟩)
      fun i _ j _ e => Finset.singleton_injective (hs (by simp [Set.ordConnected_singleton])
        (by simp [Set.ordConnected_singleton]) (by simpa using e)))
