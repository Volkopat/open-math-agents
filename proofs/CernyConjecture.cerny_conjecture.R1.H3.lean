import OMAReductions.R_CernyConjecture_cerny_conjecture_R1

namespace OMA.Proof_CernyConjecture_cerny_conjecture_R1_H3

private lemma short_pair_merge {α σ : Type} [Fintype σ] [DecidableEq σ] (M : DFA α σ)
    (hsync : M.IsSynchronizing) (x y : σ) :
    ∃ v : List α, M.evalFrom x v = M.evalFrom y v ∧ v.length ≤ (Fintype.card σ).choose 2 := by
  classical
  obtain ⟨r, z, hreset⟩ := hsync
  let P (k : ℕ) : Prop := ∃ v : List α, v.length = k ∧ M.evalFrom x v = M.evalFrom y v
  have hex : ∃ k, P k := ⟨r.length, r, rfl, (hreset x).trans (hreset y).symm⟩
  obtain ⟨v, hvlen, hmerge⟩ := Nat.find_spec hex
  have hmin : ∀ u : List α, M.evalFrom x u = M.evalFrom y u → v.length ≤ u.length := by
    intro u hu
    rw [hvlen]
    exact Nat.find_min' hex ⟨u, rfl, hu⟩
  let pair (i : ℕ) : Finset σ := {M.evalFrom x (v.take i), M.evalFrom y (v.take i)}
  have hne : ∀ i < v.length, M.evalFrom x (v.take i) ≠ M.evalFrom y (v.take i) := by
    intro i hi heq
    have hl := hmin (v.take i) heq
    simp only [List.length_take, Nat.min_eq_left hi.le] at hl
    omega
  have hmem : ∀ i ∈ Finset.range v.length,
      pair i ∈ (Finset.univ : Finset σ).powersetCard 2 := by
    intro i hi
    have hlt : i < v.length := Finset.mem_range.mp hi
    rw [Finset.mem_powersetCard]
    exact ⟨Finset.subset_univ _, Finset.card_pair (hne i hlt)⟩
  have hdist : ∀ i j : ℕ, i < j → j < v.length → pair i ≠ pair j := by
    intro i j hij hj heq
    have hxi : M.evalFrom x (v.take i) ∈ pair j := by
      rw [← heq]
      simp [pair]
    have hyi : M.evalFrom y (v.take i) ∈ pair j := by
      rw [← heq]
      simp [pair]
    simp only [pair, Finset.mem_insert, Finset.mem_singleton] at hxi hyi
    let u : List α := v.take i ++ v.drop j
    have hulen : u.length < v.length := by
      simp only [u, List.length_append, List.length_take, List.length_drop,
        Nat.min_eq_left (hij.trans hj).le]
      omega
    have hxu_eq_hyu : M.evalFrom x u = M.evalFrom y u := by
      have h1 : M.evalFrom (M.evalFrom x (v.take j)) (v.drop j) =
          M.evalFrom (M.evalFrom y (v.take j)) (v.drop j) := by
        rw [← DFA.evalFrom_of_append, ← DFA.evalFrom_of_append, List.take_append_drop]
        exact hmerge
      simp only [u, DFA.evalFrom_of_append]
      rcases hxi with hxx | hxy <;> rcases hyi with hyx | hyy
      · exact absurd (hxx.trans hyx.symm) (hne i (hij.trans hj))
      · rw [hxx, hyy]; exact h1
      · rw [hxy, hyx]; exact h1.symm
      · exact absurd (hxy.trans hyy.symm) (hne i (hij.trans hj))
    have hl := hmin u hxu_eq_hyu
    omega
  have hinj : Set.InjOn pair ↑(Finset.range v.length) := by
    intro i hi j hj heq
    have hi' : i < v.length := Finset.mem_range.mp hi
    have hj' : j < v.length := Finset.mem_range.mp hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd heq (hdist i j h hj')
    · exact h
    · exact absurd heq.symm (hdist j i h hi')
  have hcard := Finset.card_le_card_of_injOn pair hmem hinj
  rw [Finset.card_range, Finset.card_powersetCard, Finset.card_univ] at hcard
  exact ⟨v, hmerge, hcard⟩

end OMA.Proof_CernyConjecture_cerny_conjecture_R1_H3

theorem OMA.solution : OMA.R_CernyConjecture_cerny_conjecture_R1.H3 := by
  intro α σ inst M hsync hrank
  classical
  set n := Fintype.card σ with hn_def
  have hn_pos : 1 ≤ n := Fintype.card_pos_iff.mpr ⟨M.start⟩
  by_cases hn1 : n ≤ 1
  · refine ⟨[], ⟨M.start, fun q => ?_⟩, by simp⟩
    exact Fintype.card_le_one_iff.mp hn1 q M.start
  · by_cases hn2 : n = 2
    · have hcard2 : (Finset.univ : Finset σ).card = 2 := by simpa [hn_def] using hn2
      obtain ⟨u0, u1, _, huniv⟩ := Finset.card_eq_two.mp hcard2
      obtain ⟨v, hmerge, hvlen⟩ :=
        OMA.Proof_CernyConjecture_cerny_conjecture_R1_H3.short_pair_merge M hsync u0 u1
      refine ⟨v, ⟨M.evalFrom u0 v, fun q => ?_⟩, ?_⟩
      · have hq : q ∈ ({u0, u1} : Finset σ) := by rw [← huniv]; exact Finset.mem_univ q
        rcases Finset.mem_insert.mp hq with rfl | hq1
        · rfl
        · rw [Finset.mem_singleton.mp hq1]
          exact hmerge.symm
      · rw [← hn_def] at hvlen
        rw [hn2] at hvlen ⊢
        exact hvlen
    · have hn3 : 3 ≤ n := by omega
      obtain ⟨a, x, y, ha⟩ := hrank
      obtain ⟨v, hmerge, hvlen⟩ :=
        OMA.Proof_CernyConjecture_cerny_conjecture_R1_H3.short_pair_merge M hsync x y
      refine ⟨a :: v, ⟨M.evalFrom x v, fun q => ?_⟩, ?_⟩
      · rw [DFA.evalFrom_cons]
        rcases ha q with hqx | hqy
        · rw [hqx]
        · rw [hqy, hmerge.symm]
      · simp only [List.length_cons]
        rw [← hn_def] at hvlen
        have hch : n.choose 2 = n * (n - 1) / 2 := Nat.choose_two_right n
        rw [hch] at hvlen
        have hmul : 2 * (n * (n - 1) / 2) ≤ n * (n - 1) := Nat.mul_div_le (n * (n - 1)) 2
        have hquad : 2 + n * (n - 1) ≤ 2 * (n - 1) ^ 2 := by
          obtain ⟨m, hm⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
          rw [hm]
          simp only [show m + 3 - 1 = m + 2 by omega]
          nlinarith
        omega
