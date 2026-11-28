import OMAStatements.S_oeis_a151512

-- Problem: A151512: The triangle in A151359 read by rows upwards.
-- Upstream: formal-conjectures statements/oeis-a151512.lean:0 (declaration OMA.S_oeis_a151512.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Disproof idea: the conjecture at j = 8, i = 7 says A151359(1, 7) = eqRel 7 1. A partition of
-- Fin 7 into one block has the block Finset.univ of size 7 > 6, so A151359(1, 7) = 0, while the
-- indiscrete partition shows eqRel 7 1 > 0. The example sentence of the comment is not used.

open OMA.S_oeis_a151512 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a151512.main) := by
  intro h
  have h1 := h.1 8 7 (by norm_num) (by norm_num)
  rw [show (8 : ℕ) - 1 = 7 from rfl, show (7 : ℕ) - 1 = 6 from rfl,
    show (8 : ℕ) - 7 = 1 from rfl] at h1
  have h2 : A151512 7 6 = 0 := by
    unfold A151512 A151359
    rw [show (7 : ℕ) - 6 = 1 from rfl, Finset.card_eq_zero]
    apply Finset.filter_false_of_mem
    intro P _ hP
    obtain ⟨hc, h6⟩ := hP
    obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hc
    have hs := P.sup_parts
    rw [hb, Finset.sup_singleton] at hs
    have hb6 := (h6 b (by rw [hb]; exact Finset.mem_singleton_self b)).2
    have hbu : b = Finset.univ := hs
    rw [hbu, Finset.card_univ, Fintype.card_fin] at hb6
    omega
  have h3 : 0 < eqRel 7 1 := by
    unfold eqRel
    have ha : (Finset.univ : Finset (Fin 7)) ≠ ⊥ := by
      rw [Finset.bot_eq_empty]
      exact Finset.univ_nonempty.ne_empty
    apply Finset.card_pos.mpr
    exact ⟨Finpartition.indiscrete ha,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, Finset.card_singleton _⟩⟩
  rw [h2] at h1
  rw [← h1] at h3
  exact lt_irrefl 0 h3
