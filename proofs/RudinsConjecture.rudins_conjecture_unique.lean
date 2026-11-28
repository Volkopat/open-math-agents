import FormalConjectures.Wikipedia.RudinsConjecture

/-! Shorter disproof of `RudinsConjecture.rudins_conjecture_unique` via (120, 49). -/

open RudinsConjecture Finset

theorem OMA.disproof : ¬ (type_of% @RudinsConjecture.rudins_conjecture_unique) := by
  intro hu
  classical
  have hQf (N q a : ℕ) : Q N q a = ((range N).filter fun n => IsSquare (q * n + a)).card := by
    change Set.ncard _ = _; rw [← Set.ncard_coe_finset]; congr 1; ext; simp
  have h120 : IsNontrivial 120 49 := by unfold IsNontrivial; decide +kernel
  have hcnt : Q 6 120 49 = 4 := by rw [hQf]; decide +kernel
  let S : Set ℕ := {m | ∃ q a, IsNontrivial q a ∧ Q 6 q a = m}
  have hb : BddAbove S := ⟨6, by
    rintro _ ⟨q, a, -, rfl⟩; rw [hQf]; exact (card_filter_le ..).trans_eq (card_range 6)⟩
  obtain ⟨q, a, hqa, hmax⟩ := Nat.sSup_mem (⟨4, 120, 49, h120, hcnt⟩ : S.Nonempty) hb
  have hmax' : Q 6 q a = Qmax 6 := hmax
  have hq : q = 24 := hu 6 (by decide) q a hqa hmax'
  have hle : Q 6 24 a ≤ 4 := by
    rw [hQf]
    by_cases ha : a < 144
    · interval_cases a <;> decide +kernel
    · have nadj (b : ℕ) (hb : 144 ≤ b) : ¬(IsSquare b ∧ IsSquare (b + 24)) := by
        rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
        have : 12 ≤ x := by nlinarith
        have : x + 1 ≤ y := by nlinarith
        nlinarith [sq_nonneg ((y : ℤ) - x - 1)]
      obtain ⟨i, hi, hni⟩ : ∃ i < 2, ¬IsSquare (24 * i + a) := by
        by_cases h0 : IsSquare a
        · exact ⟨1, by omega, fun h1 => nadj a (by omega) ⟨h0, by simpa [add_comm] using h1⟩⟩
        · exact ⟨0, by omega, by simpa using h0⟩
      obtain ⟨j, hj, hnj⟩ : ∃ j, (2 ≤ j ∧ j < 4) ∧ ¬IsSquare (24 * j + a) := by
        by_cases h2 : IsSquare (a + 48)
        · exact ⟨3, by omega, fun h3 =>
            nadj (a + 48) (by omega) ⟨h2, by rwa [show a + 48 + 24 = 24 * 3 + a by omega]⟩⟩
        · exact ⟨2, by omega, by simpa [add_comm] using h2⟩
      refine (card_le_card (t := ((range 6).erase i).erase j) fun n hn => ?_).trans ?_
      · simp only [mem_filter, mem_range] at hn
        simp only [mem_erase, mem_range]
        exact ⟨fun e => hnj (e ▸ hn.2), fun e => hni (e ▸ hn.2), hn.1⟩
      · rw [card_erase_of_mem (by simp; omega), card_erase_of_mem (mem_range.mpr (by omega))]; decide
  have hlo : 4 ≤ Qmax 6 := le_csSup hb (show 4 ∈ S from ⟨120, 49, h120, hcnt⟩)
  have hbad := hu 6 (by decide) 120 49 h120 (by rw [← hmax', hq] at hlo ⊢; omega)
  omega
