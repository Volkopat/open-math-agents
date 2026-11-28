import OMAStatements.S_mo_407245
import Mathlib

/-! Orthogonal equipartitions and the minimum length forcing repeated meetings.
Retains the case analysis from @danielchin's pending PR #20562, while counting
meetings by a direct injection into the interval of quotients modulo four. -/

open Finset OMA.S_mo_407245

theorem OMA.solution : type_of% @OMA.S_mo_407245.main := by
  intro k n _ _
  have hmt {r} (h : hasOrthogonal k n r = false) (P : Family k n r) (hP : valid P) :
      ∃ x y, x ≠ y ∧ 2 ≤ (meetings P x y).card := by
    by_contra hc
    exact of_decide_eq_false h ⟨P, hP, fun x y hxy => by by_contra hlt; exact hc ⟨x, y, hxy, by omega⟩⟩
  by_cases h3 : hasOrthogonal k n 3 = true
  · by_cases h4 : hasOrthogonal k n 4 = true
    · simp only [threshold, h3, h4, ↓reduceIte]
      intro r hr hf
      obtain ⟨P, hP, horth⟩ := of_decide_eq_true h4
      obtain ⟨x, y, hxy, hle⟩ := hf (fun i => P ⟨i.1 % 4, Nat.mod_lt _ (by decide)⟩) fun i b => hP _ b
      obtain ⟨j, hj⟩ := card_le_one_iff_subset_singleton.1 (horth x y hxy)
      have hres {i : Fin r} (hi : i ∈ meetings
          (fun i : Fin r => P ⟨i.1 % 4, Nat.mod_lt _ (by decide)⟩) x y) : i.1 % 4 = j.1 := by
        exact congrArg Fin.val (mem_singleton.1 (hj (by simpa [meetings] using hi)))
      have hc := card_le_card_of_injOn (fun i : Fin r => i.1 / 4)
        (t := range ((r + 3) / 4))
        (fun i _ => mem_range.2 (by dsimp; have := i.2; omega))
        (fun a ha b hb hab => Fin.ext (by have := hres ha; have := hres hb; dsimp at hab; omega))
      rw [card_range] at hc
      omega
    · simp only [threshold, h3, h4, ↓reduceIte]
      refine ⟨⟨by decide, fun P hP => let ⟨x, y, hxy, hc⟩ := hmt (Bool.eq_false_iff.2 h4) P hP; ⟨x, y, hxy, by omega⟩⟩, ?_⟩
      rintro r ⟨hr, hf⟩
      by_contra hlt
      have r3 : r = 3 := by omega
      subst r3
      obtain ⟨P, hP, horth⟩ := of_decide_eq_true h3
      obtain ⟨x, y, hxy, hle⟩ := hf P hP
      have := horth x y hxy; omega
  · simp only [threshold, h3, ↓reduceIte]
    exact ⟨⟨le_rfl, fun P hP => let ⟨x, y, hxy, hc⟩ := hmt (Bool.eq_false_iff.2 h3) P hP; ⟨x, y, hxy, by omega⟩⟩, fun _ h => h.1⟩
