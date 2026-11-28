import OMAReductions.R_CernyConjecture_cerny_conjecture_R1

namespace OMA.Proof_CernyConjecture_cerny_conjecture_R1_H2

private lemma exists_noninj_letter {α σ : Type} (M : DFA α σ)
    {x y : σ} (hne : x ≠ y) {w : List α} (hm : M.evalFrom x w = M.evalFrom y w) :
    ∃ (a : α) (u v : σ), u ≠ v ∧ M.step u a = M.step v a := by
  induction w generalizing x y with
  | nil =>
    exact absurd hm hne
  | cons a t ih =>
    simp only [DFA.evalFrom_cons] at hm
    by_cases hstep : M.step x a = M.step y a
    · exact ⟨a, x, y, hne, hstep⟩
    · exact ih hstep hm

private lemma card_image_lt_of_collision {σ : Type} [DecidableEq σ]
    (S : Finset σ) (f : σ → σ) {x y : σ} (hx : x ∈ S) (hy : y ∈ S)
    (hne : x ≠ y) (heq : f x = f y) :
    (S.image f).card ≤ S.card - 1 := by
  have hsub : S.image f ⊆ (S.erase y).image f := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hz
    by_cases hwy : w = y
    · subst hwy
      exact Finset.mem_image.mpr ⟨x, Finset.mem_erase.mpr ⟨hne, hx⟩, heq⟩
    · exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hwy, hw⟩, rfl⟩
  calc
    (S.image f).card ≤ ((S.erase y).image f).card := Finset.card_le_card hsub
    _ ≤ (S.erase y).card := Finset.card_image_le
    _ = S.card - 1 := Finset.card_erase_of_mem hy

private lemma collapse_finset {α σ : Type} [Fintype σ] [DecidableEq σ] (M : DFA α σ)
    (hpairs : ∀ x y : σ, ∃ w : List α, M.evalFrom x w = M.evalFrom y w ∧ w.length ≤ Fintype.card σ)
    (k : ℕ) :
    ∀ S : Finset σ, S.Nonempty → S.card ≤ k + 1 →
      ∃ v : List α, (S.image (fun q => M.evalFrom q v)).card ≤ 1 ∧
        v.length ≤ k * Fintype.card σ := by
  induction k with
  | zero =>
    intro S _ hSc
    refine ⟨[], ?_, by simp⟩
    have himg : S.image (fun q => M.evalFrom q ([] : List α)) = S := by
      ext q
      simp
    rw [himg]
    exact hSc
  | succ k ih =>
    intro S hSne hSc
    by_cases h1 : S.card ≤ 1
    · refine ⟨[], ?_, by simp⟩
      have himg : S.image (fun q => M.evalFrom q ([] : List α)) = S := by
        ext q
        simp
      rw [himg]
      exact h1
    · have hgt : 1 < S.card := by omega
      obtain ⟨x, hx, y, hy, hne⟩ := Finset.one_lt_card.mp hgt
      obtain ⟨u, hmerge, hulen⟩ := hpairs x y
      let S' : Finset σ := S.image (fun q => M.evalFrom q u)
      have hS'ne : S'.Nonempty := hSne.image _
      have hS'card : S'.card ≤ S.card - 1 :=
        card_image_lt_of_collision S (fun q => M.evalFrom q u) hx hy hne hmerge
      obtain ⟨v', hv'card, hv'len⟩ := ih S' hS'ne (by omega)
      refine ⟨u ++ v', ?_, ?_⟩
      · have himg : S.image (fun q => M.evalFrom q (u ++ v')) =
            S'.image (fun q => M.evalFrom q v') := by
          ext z
          simp only [S', Finset.mem_image]
          constructor
          · rintro ⟨q, hq, rfl⟩
            exact ⟨M.evalFrom q u, ⟨q, hq, rfl⟩, (DFA.evalFrom_of_append M q u v').symm⟩
          · rintro ⟨r, ⟨q, hq, rfl⟩, rfl⟩
            exact ⟨q, hq, DFA.evalFrom_of_append M q u v'⟩
        rw [himg]
        exact hv'card
      · rw [List.length_append, Nat.succ_mul]
        omega

end OMA.Proof_CernyConjecture_cerny_conjecture_R1_H2

theorem OMA.solution : OMA.R_CernyConjecture_cerny_conjecture_R1.H2 := by
  intro α σ inst M hpairs
  classical
  set n := Fintype.card σ with hn_def
  have hn_pos : 1 ≤ n := Fintype.card_pos_iff.mpr ⟨M.start⟩
  by_cases hn1 : n ≤ 1
  · refine ⟨[], ⟨M.start, fun q => ?_⟩, by simp⟩
    exact Fintype.card_le_one_iff.mp hn1 q M.start
  · have hn2 : 2 ≤ n := by omega
    have hgt : 1 < (Finset.univ : Finset σ).card := by
      simpa [hn_def] using (show 1 < n by omega)
    obtain ⟨x0, _, y0, _, hne0⟩ := Finset.one_lt_card.mp hgt
    obtain ⟨w0, hm0, _⟩ := hpairs x0 y0
    obtain ⟨a, u, v, huv, hstep⟩ :=
      OMA.Proof_CernyConjecture_cerny_conjecture_R1_H2.exists_noninj_letter M hne0 hm0
    let S1 : Finset σ := (Finset.univ : Finset σ).image (fun q => M.evalFrom q [a])
    have hS1ne : S1.Nonempty := ⟨M.evalFrom M.start [a], Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
    have hS1card : S1.card ≤ n - 1 := by
      have hcoll := OMA.Proof_CernyConjecture_cerny_conjecture_R1_H2.card_image_lt_of_collision
        (Finset.univ : Finset σ) (fun q => M.evalFrom q [a])
        (Finset.mem_univ u) (Finset.mem_univ v) huv (by simpa [DFA.evalFrom_singleton] using hstep)
      simpa [S1, hn_def] using hcoll
    obtain ⟨t, htcard, htlen⟩ :=
      OMA.Proof_CernyConjecture_cerny_conjecture_R1_H2.collapse_finset M hpairs (n - 2) S1 hS1ne
        (by omega)
    refine ⟨[a] ++ t, ⟨M.evalFrom M.start ([a] ++ t), fun q => ?_⟩, ?_⟩
    · let T : Finset σ := S1.image (fun r => M.evalFrom r t)
      have hqT : M.evalFrom q ([a] ++ t) ∈ T := by
        rw [DFA.evalFrom_of_append]
        exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ q))
      have hsT : M.evalFrom M.start ([a] ++ t) ∈ T := by
        rw [DFA.evalFrom_of_append]
        exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_univ M.start))
      exact Finset.card_le_one.mp htcard _ hqT _ hsT
    · rw [List.length_append]
      simp only [List.length_singleton]
      rw [← hn_def] at htlen
      have hsq : 1 + (n - 2) * n = (n - 1) ^ 2 := by
        obtain ⟨m, hm⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
        rw [hm]
        simp only [Nat.add_sub_cancel, show m + 2 - 1 = m + 1 by omega]
        ring
      omega
