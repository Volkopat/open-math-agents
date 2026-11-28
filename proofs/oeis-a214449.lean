import OMAStatements.S_oeis_a214449

-- Problem: A214449: Least m>0 such that n! <= m^m.
-- Upstream: formal-conjectures statements/oeis-a214449.lean:0 (declaration OMA.S_oeis_a214449.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: n = 188 is a counterexample. From 158^158 < 188! <= 159^159 and the monotonicity of
-- m^m, A214449(188) = 159. But 158^158 < 189! < 159^159 and 2 * 189! < 158^158 + 159^159,
-- so |158^158 - 189!| < |159^159 - 189!|: 159 is not a minimiser for 189!, hence the least
-- minimiser A118168(189) is not 159.

open OMA.S_oeis_a214449 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a214449.main) := by
  intro H
  have mono : ∀ m : ℕ, 0 < m → m ≤ 158 → m ^ m ≤ 158 ^ 158 := fun m hm h =>
    (Nat.pow_le_pow_right hm h).trans (Nat.pow_le_pow_left h 158)
  have key : ∀ N x y : ℕ, y ^ y < N → N < x ^ x → 2 * N < y ^ y + x ^ x →
      |(y : ℤ) ^ y - (N : ℤ)| < |(x : ℤ) ^ x - (N : ℤ)| := by
    intro N x y h1 h2 h3
    have h1' : (y : ℤ) ^ y < (N : ℤ) := by exact_mod_cast h1
    have h2' : (N : ℤ) < (x : ℤ) ^ x := by exact_mod_cast h2
    have h3' : 2 * (N : ℤ) < (y : ℤ) ^ y + (x : ℤ) ^ x := by exact_mod_cast h3
    have hA : |(y : ℤ) ^ y - (N : ℤ)| = (N : ℤ) - (y : ℤ) ^ y := by
      rw [abs_of_neg (by linarith : (y : ℤ) ^ y - (N : ℤ) < 0), neg_sub]
    have hB : |(x : ℤ) ^ x - (N : ℤ)| = (x : ℤ) ^ x - (N : ℤ) := abs_of_pos (by linarith)
    rw [hA, hB]
    linarith
  have gen : ∀ (S : Set ℕ) (m : ℕ), 0 < m → m ∉ S → sInf S ≠ m := by
    intro S m hm hS h
    rcases Set.eq_empty_or_nonempty S with he | hne
    · rw [he, Nat.sInf_empty] at h
      exact hm.ne h
    · apply hS
      rw [← h]
      exact Nat.sInf_mem hne
  have e1 : Nat.factorial 188 ≤ 159 ^ 159 := by norm_num
  have e2 : 158 ^ 158 < Nat.factorial 188 := by norm_num
  have f1 : 158 ^ 158 < Nat.factorial 189 := by norm_num
  have f2 : Nat.factorial 189 < 159 ^ 159 := by norm_num
  have f3 : 2 * Nat.factorial 189 < 158 ^ 158 + 159 ^ 159 := by norm_num
  have ha : a 188 = 159 := by
    unfold a
    apply le_antisymm
    · apply Nat.sInf_le
      exact ⟨by norm_num, e1⟩
    · apply le_csInf
      · exact ⟨159, by norm_num, e1⟩
      · rintro m ⟨hm0, hm⟩
        refine le_of_not_gt fun hlt => ?_
        exact lt_irrefl _ ((hm.trans (mono m hm0 (Nat.le_of_lt_succ hlt))).trans_lt e2)
  have hb : b 189 ≠ 159 := by
    unfold b
    apply gen _ 159 (by norm_num)
    rintro ⟨_, hall⟩
    exact lt_irrefl _
      ((hall 158 (by norm_num)).trans_lt (key (Nat.factorial 189) 159 158 f1 f2 f3))
  exact hb ((H 188 (by norm_num)).symm.trans ha)
