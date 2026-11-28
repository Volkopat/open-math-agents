import OMAStatements.S_mo_273966
import Mathlib

open Finset

open OMA.S_mo_273966

private theorem chooseTop {n s : ℕ} (hs : s ≤ n) (w : Fin n → ℝ) :
    ∃ S : Finset (Fin n), S.card = s ∧
      (∀ i ∈ S, ∀ j ∉ S, w j ≤ w i) ∧
      ∀ T : Finset (Fin n), T.card = s → (∑ i ∈ T, w i) ≤ ∑ i ∈ S, w i := by
  classical
  let candidates := (univ : Finset (Fin n)).powersetCard s
  have hne : candidates.Nonempty := powersetCard_nonempty.mpr (by simpa using hs)
  obtain ⟨S, hS, hmax⟩ := candidates.exists_max_image (fun I => ∑ i ∈ I, w i) hne
  have hcard : S.card = s := (mem_powersetCard.mp hS).2
  have hopt (T : Finset (Fin n)) (hT : T.card = s) :
      (∑ i ∈ T, w i) ≤ ∑ i ∈ S, w i :=
    hmax T (mem_powersetCard.mpr ⟨subset_univ T, hT⟩)
  refine ⟨S, hcard, ?_, hopt⟩
  intro i hi j hj
  let T := insert j (S.erase i)
  have hj' : j ∉ S.erase i := fun h => hj (erase_subset _ _ h)
  have hpos : 0 < S.card := card_pos.mpr ⟨i, hi⟩
  have hT : T.card = s := by
    change (insert j (S.erase i)).card = s
    rw [card_insert_of_notMem hj', card_erase_of_mem hi]
    omega
  have hsumT : (∑ x ∈ T, w x) = w j + ∑ x ∈ S.erase i, w x := sum_insert hj'
  have hsumS := sum_erase_add (s := S) w hi
  have h := hopt T hT
  linarith

private theorem value_eq {n : ℕ} (v w : Fin n → ℝ) (S : Finset (Fin n)) :
    inheritanceValue v w S = (∑ i, w i) + ∑ i ∈ S, (v i - w i) := by
  have h := sum_sdiff (subset_univ S) (f := w)
  unfold inheritanceValue
  rw [sum_sub_distrib]
  linarith

theorem OMA.solution : type_of% @OMA.S_mo_273966.main := by
  intro n k hk v w
  obtain ⟨S, hS, hTop, hMax⟩ := chooseTop hk (fun i => v i - w i)
  refine ⟨S, hS, hTop, fun T hT => ?_⟩
  rw [value_eq, value_eq]
  exact add_le_add_right (hMax T hT) _
