import OMAStatements.S_oeis_a243106

/-!
R. J. Cano's signed-powers conjecture (OEIS A243106) has earlier proofs in
AlphaProof Nexus (Tsoukalas et al., arXiv:2605.22763) and Adamczewski's
*OEIS Open* (arXiv:2608.11941, Appendix A). Here the induction controls both
the absolute value and its predecessor in order to handle borrowing.
-/

open OMA.S_oeis_a243106

private def good (b m : ℕ) : Prop :=
  ∀ d ∈ Nat.digits b m, AllowedDigit b d

private theorem good_zero (b : ℕ) : good b 0 := by simp [good]

private theorem prepend {b r m : ℕ} (hb : 5 ≤ b) (hr : r < b)
    (ha : AllowedDigit b r) (hm : good b m) : good b (r + b * m) := by
  by_cases h : r = 0 ∧ m = 0
  · simpa [h.1, h.2] using good_zero b
  · intro d hd
    rw [Nat.digits_add b (by omega) r m hr (by omega)] at hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ha
    · exact hm d hd

private def represent (b : ℕ) (z : ℤ) : Prop :=
  ∃ m : ℕ, (z = (m : ℤ) ∨ z = -(m : ℤ)) ∧ good b m ∧ good b (m - 1)

private theorem extend_word {b : ℕ} {z e : ℤ} (hb : 5 ≤ b) (hz : represent b z)
    (he : e = -1 ∨ e = 1) : represent b (e + b * z) := by
  obtain ⟨m, hzm, gm, gp⟩ := hz
  have plus : good b (1 + b * m) ∧ good b ((1 + b * m) - 1) := by
    constructor
    · exact prepend hb (by omega) (Or.inr (Or.inl rfl)) gm
    · simpa using prepend hb (r := 0) (by omega) (Or.inl rfl) gm
  cases m with
  | zero =>
    refine ⟨1, ?_, by simpa using plus⟩
    rcases hzm with h | h <;> rcases he with h' | h' <;> simp [h, h']
  | succ k =>
    have hb1 : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
    have hm : ((b - 1 + b * k : ℕ) : ℤ) = (b : ℤ) * (k + 1) - 1 := by
      push_cast
      rw [hb1]
      ring
    have minus : good b (b - 1 + b * k) ∧ good b ((b - 1 + b * k) - 1) := by
      have gk : good b k := by simpa using gp
      constructor
      · exact prepend hb (by omega) (Or.inr (Or.inr (Or.inr rfl))) gk
      · rw [show (b - 1 + b * k) - 1 = (b - 2) + b * k by omega]
        exact prepend hb (by omega) (Or.inr (Or.inr (Or.inl rfl))) gk
    rcases hzm with h | h <;> rcases he with h' | h'
    · exact ⟨_, Or.inl (by rw [h, h', hm]; push_cast; ring), minus⟩
    · exact ⟨_, Or.inl (by rw [h, h']; push_cast; ring), plus⟩
    · exact ⟨_, Or.inr (by rw [h, h']; push_cast; ring), plus⟩
    · exact ⟨_, Or.inr (by rw [h, h', hm]; push_cast; ring), minus⟩

private def word (b n : ℕ) (s : ℕ → ℤ) : ℤ :=
  ∑ i ∈ Finset.range n, s i * (b : ℤ) ^ i

private theorem represent_word {b : ℕ} (hb : 5 ≤ b) (n : ℕ) (s : ℕ → ℤ)
    (hs : ∀ i < n, s i = -1 ∨ s i = 1) : represent b (word b n s) := by
  induction n generalizing s with
  | zero => exact ⟨0, Or.inl (by simp [word]), good_zero b, good_zero b⟩
  | succ n ih =>
    have hword : word b (n + 1) s = s 0 + (b : ℤ) * word b n (fun i => s (i + 1)) := by
      simp only [word, Finset.sum_range_succ', pow_zero, mul_one, Finset.mul_sum]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [pow_succ]
      ring
    rw [hword]
    exact extend_word hb (ih _ (fun i hi => hs _ (by omega))) (hs 0 (by omega))

theorem OMA.solution : type_of% @OMA.S_oeis_a243106.main := by
  intro b n hb s hs
  have h : signedSum b n s = (b : ℤ) * word b n s := by
    simp only [signedSum, word, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [pow_succ]
    ring
  obtain ⟨m, hm, gm, _⟩ := represent_word hb n s hs
  have g : good b (b * m) := by
    simpa using prepend hb (r := 0) (by omega) (Or.inl rfl) gm
  rw [h, Int.natAbs_mul]
  rcases hm with hm | hm <;> simpa [hm, good] using g
