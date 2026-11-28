import OMAStatements.S_oeis_a159619

-- Problem: A159619: Slowest increasing sequence beginning with 4 such that n and a(n) are either both evil or both odious.
-- Upstream: formal-conjectures statements/oeis-a159619.lean:0 (declaration OMA.S_oeis_a159619.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 1 is a counterexample. a(1) = 4 by definition. A001285 begins 1, 2, 2, 1, 2, 1, 1, 2,
-- so A026491(1) = 4 (A001285(1) = A001285(2) = 2 differ from A001285(0) = 1 = A001285(3)),
-- A026491(2) = 5 (A001285(4) = 2 = A001285(1)) and A026491(3) = 8 (A001285(5) = A001285(6) = 1
-- differ from A001285(2) = 2 = A001285(7)). Hence A026491(2+1) - 1 = 7, not 4.

open OMA.S_oeis_a159619 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a159619.main) := by
  intro H
  have key : ∀ (S : Set ℕ) (v : ℕ), v ∈ S → (∀ m < v, m ∉ S) → sInf S = v := by
    intro S v hv hlt
    apply le_antisymm (Nat.sInf_le hv)
    apply le_csInf ⟨v, hv⟩
    intro m hm
    by_contra h
    exact hlt m (by omega) hm
  have hb0 : a026491 0 = 1 := rfl
  have hb1 : a026491 1 = 4 := by
    show sInf {k : ℕ | a026491 0 < k ∧ a001285 (k - 1) = a001285 0} = 4
    apply key
    · show a026491 0 < 4 ∧ a001285 (4 - 1) = a001285 0
      exact ⟨by rw [hb0]; norm_num, by decide⟩
    · rintro m hm ⟨h1, h2⟩
      rw [hb0] at h1
      interval_cases m
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
  have hb2 : a026491 2 = 5 := by
    show sInf {k : ℕ | a026491 1 < k ∧ a001285 (k - 1) = a001285 1} = 5
    apply key
    · show a026491 1 < 5 ∧ a001285 (5 - 1) = a001285 1
      exact ⟨by rw [hb1]; norm_num, by decide⟩
    · rintro m hm ⟨h1, _⟩
      rw [hb1] at h1
      omega
  have hb3 : a026491 3 = 8 := by
    show sInf {k : ℕ | a026491 2 < k ∧ a001285 (k - 1) = a001285 2} = 8
    apply key
    · show a026491 2 < 8 ∧ a001285 (8 - 1) = a001285 2
      exact ⟨by rw [hb2]; norm_num, by decide⟩
    · rintro m hm ⟨h1, h2⟩
      rw [hb2] at h1
      interval_cases m
      · exact absurd h2 (by decide)
      · exact absurd h2 (by decide)
  have h1 := H 1 le_rfl
  have ha : a 1 = 4 := rfl
  rw [ha, show (2 : ℕ) + 1 = 3 from rfl, hb3] at h1
  norm_num at h1
