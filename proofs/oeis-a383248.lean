import OMAStatements.S_oeis_a383248

open OMA.S_oeis_a383248

theorem OMA.solution : type_of% @OMA.S_oeis_a383248.main := by
  have hbr : ∀ t, ∃ b, t < b ∧ admissible b ∧
      (∀ m, admissible m → follows m b) ∧ ∀ m, admissible m → follows b m := fun t => by
    let b := Nat.ofDigits 10 (List.replicate (t + 1) 8)
    have hgr : ∀ k, k ≤ Nat.ofDigits 10 (List.replicate k 8) := fun k => by
      induction k with
      | zero => simp
      | succ k ih => rw [List.replicate_succ, Nat.ofDigits_cons]; omega
    have hd : Nat.digits 10 b = List.replicate (t + 1) 8 :=
      Nat.digits_ofDigits 10 (by decide) _ (by simp) (by simp)
    have hf : firstDigit b = 8 := by
      rw [firstDigit, hd, List.reverse_replicate, List.replicate_succ]; rfl
    have hl : lastDigit b = 8 := by simp [lastDigit, hd, List.replicate_succ]
    refine ⟨b, hgr (t + 1), ⟨by simp [hd], by
      rw [hd, List.reverse_replicate]
      exact List.isChain_replicate_of_rel _ (by simp [digitStep])⟩,
      fun m hm => ?_, fun _ _ => by simp [follows, hl, digitStep]⟩
    simp only [follows, hf, digitStep]
    intro hodd
    cases hdig : Nat.digits 10 m with
    | nil => simp [lastDigit, hdig] at hodd
    | cons d ds =>
      have : d ≠ 9 := fun he => hm.1 (by simp [hdig, he])
      have : d < 10 := Nat.digits_lt_base (m := m) (by decide) (by simp [hdig])
      simp [lastDigit, hdig] at hodd ⊢; omega
  have hused : ∀ n, (state n).1 = (Finset.range n).image a := fun n => by
    induction n with
    | zero => simp [state]
    | succ n ih => change insert (a n) (state n).1 = _; simp [Finset.range_add_one, ih]
  have hpick : ∀ n, admissible (state n).2 →
      admissible (a n) ∧ a n ∉ (state n).1 ∧ follows (state n).2 (a n) := fun n h => by
    obtain ⟨b, hb, hadm, hin, _⟩ := hbr ((state n).1.sup id)
    exact Nat.sInf_mem (s := {m | admissible m ∧ m ∉ (state n).1 ∧ follows (state n).2 m})
      ⟨b, hadm, fun H => (not_lt_of_ge (Finset.le_sup (f := id) H)) hb, hin _ h⟩
  have hprev : ∀ n, admissible (state n).2 := fun n => by
    induction n with
    | zero => simp [state, admissible]
    | succ n ih => exact (hpick n ih).1
  have hch (n : ℕ) := hpick n (hprev n)
  have hinj : Function.Injective a := fun i j eq => by
    have hne : ∀ {x y}, x < y → a x ≠ a y := fun h e =>
      (hch _).2.1 (by rw [hused]; exact Finset.mem_image.2 ⟨_, Finset.mem_range.2 h, e⟩)
    rcases lt_trichotomy i j with h | h | h
    · exact (hne h eq).elim
    · exact h
    · exact (hne h eq.symm).elim
  have hfree : ∀ {m}, (¬ ∃ n, a n = m) → ∀ n, m ∉ (state n).1 := fun hm n h => by
    rw [hused] at h; obtain ⟨i, _, hi⟩ := Finset.mem_image.1 h; exact hm ⟨i, hi⟩
  refine ⟨hinj, fun m => ⟨fun ⟨n, h⟩ => h ▸ (hch n).1, fun hm => ?_⟩⟩
  by_contra h
  obtain ⟨N, hN⟩ := ((Set.finite_Iic m).preimage hinj.injOn).bddAbove
  obtain ⟨b, hb, hadm, hin, hout⟩ := hbr ((state (N + 1)).1.sup id)
  have hbo : ∃ j, a j = b := by
    by_contra hb'
    exact (Set.infinite_range_of_injective hinj) ((Set.finite_le_nat b).subset
      (Set.range_subset_iff.2 fun n => Nat.sInf_le ⟨hadm, hfree hb' n, hin _ (hprev n)⟩))
  obtain ⟨j, hj⟩ := hbo
  have hlg : N < j := by
    by_contra! hjN
    exact (not_lt_of_ge (Finset.le_sup (f := id) (by
      rw [hused]; exact Finset.mem_image.2 ⟨j, Finset.mem_range.2 (by omega), hj⟩))) hb
  have hsm : a (j + 1) ≤ m :=
    Nat.sInf_le ⟨hm, hfree h (j + 1), by change follows (a j) m; rw [hj]; exact hout m hm⟩
  have := hN hsm
  omega
