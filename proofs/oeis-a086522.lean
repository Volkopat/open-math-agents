import OMAStatements.S_oeis_a086522

-- Problem: A086522: Primes arising as the arithmetic mean of a pair of successive terms of A086519.
-- Upstream: formal-conjectures statements/oeis-a086522.lean:0 (declaration OMA.S_oeis_a086522.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: A086519 begins 3, 7, 19. If two successive terms t, q had mean 19, then t + q = 38.
-- Neither is 0 (38 is not prime), so both are primes and q is new (not equal to any earlier term,
-- t included). Two primes with sum 38 are 7 + 31, 19 + 19 or 31 + 7. The pair 19, 19 repeats a
-- term; 31, 7 repeats the term 7 = A086519(2); and 7, 31 is impossible because 7 occurs only as
-- A086519(2), whose successor is 19 (a later 7 would repeat A086519(2)), and A086519(1) = 3.

namespace OMA.A086522Proof

open OMA.S_oeis_a086522

theorem next_spec (l : List ℕ) (t : ℕ) :
    next l t = 0 ∨ ((next l t).Prime ∧ next l t ∉ l ∧ ∃ r : ℕ, r.Prime ∧ next l t + t = 2 * r) := by
  rcases Nat.eq_zero_or_pos (next l t) with h | h
  · exact Or.inl h
  · right
    have hne := Nat.nonempty_of_pos_sInf h
    exact Nat.sInf_mem hne

theorem eq_of_least {S : Set ℕ} {k : ℕ} (hk : k ∈ S) (hlow : ∀ q : ℕ, q < k → q ∉ S) :
    sInf S = k := by
  apply le_antisymm (Nat.sInf_le hk)
  by_contra h
  have hmem : sInf S ∈ S := Nat.sInf_mem ⟨k, hk⟩
  exact hlow (sInf S) (by omega) hmem

theorem next1 : next [3] 3 = 7 := by
  apply eq_of_least
  · show Nat.Prime 7 ∧ 7 ∉ [3] ∧ ∃ r : ℕ, r.Prime ∧ 7 + 3 = 2 * r
    exact ⟨by norm_num, by simp, 5, by norm_num, by norm_num⟩
  · intro q hq hmem
    obtain ⟨hqp, hql, r, hr, hqr⟩ := hmem
    obtain rfl : r = (q + 3) / 2 := by omega
    revert hqp hql hr hqr
    interval_cases q <;> norm_num

theorem next2 : next [7, 3] 7 = 19 := by
  apply eq_of_least
  · show Nat.Prime 19 ∧ 19 ∉ [7, 3] ∧ ∃ r : ℕ, r.Prime ∧ 19 + 7 = 2 * r
    exact ⟨by norm_num, by simp, 13, by norm_num, by norm_num⟩
  · intro q hq hmem
    obtain ⟨hqp, hql, r, hr, hqr⟩ := hmem
    obtain rfl : r = (q + 7) / 2 := by omega
    revert hqp hql hr hqr
    interval_cases q <;> norm_num

theorem pre1 : pre 1 = [7, 3] := by
  show next [3] 3 :: [3] = [7, 3]
  rw [next1]

theorem mem7 : ∀ k : ℕ, 7 ∈ pre (k + 1) := by
  intro k
  induction k with
  | zero =>
    change 7 ∈ pre 1
    rw [pre1]
    simp
  | succ k ih =>
    change 7 ∈ next (pre (k + 1)) ((pre (k + 1)).headD 0) :: pre (k + 1)
    exact List.mem_cons.mpr (Or.inr ih)

theorem pair (t q : ℕ) (ht : t.Prime) (hq : q.Prime) (h : t + q = 2 * 19) :
    (t = 7 ∧ q = 31) ∨ (t = 19 ∧ q = 19) ∨ (t = 31 ∧ q = 7) := by
  obtain rfl : q = 38 - t := by omega
  have hle : t ≤ 38 := by omega
  revert ht hq
  interval_cases t <;> norm_num

end OMA.A086522Proof

open OMA.S_oeis_a086522 in
theorem OMA.solution : type_of% @OMA.S_oeis_a086522.main := by
  have h19 : ¬ IsTerm 19 := by
    rintro ⟨-, n, hn, hsum⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have e1 : A086519 (m + 1) = (pre m).headD 0 := by
      unfold A086519
      rw [Nat.add_sub_cancel]
    have e2 : A086519 (m + 1 + 1) = next (pre m) ((pre m).headD 0) := by
      unfold A086519
      rw [Nat.add_sub_cancel]
      rfl
    rw [e1, e2] at hsum
    rcases m with _ | k
    · change 3 + next [3] 3 = 2 * 19 at hsum
      rw [OMA.A086522Proof.next1] at hsum
      omega
    · obtain ⟨T, hT⟩ : ∃ T, T = next (pre k) ((pre k).headD 0) := ⟨_, rfl⟩
      have ht : (pre (k + 1)).headD 0 = T := by
        subst hT
        rfl
      have hpre : pre (k + 1) = T :: pre k := by
        subst hT
        rfl
      obtain ⟨Q, hQ⟩ : ∃ Q, Q = next (pre (k + 1)) T := ⟨_, rfl⟩
      rw [ht, ← hQ] at hsum
      have hTs := OMA.A086522Proof.next_spec (pre k) ((pre k).headD 0)
      rw [← hT] at hTs
      have hQs := OMA.A086522Proof.next_spec (pre (k + 1)) T
      rw [← hQ] at hQs
      rcases hTs with hT0 | ⟨hTp, hTn, -⟩
      · rcases hQs with hQ0 | ⟨hQp, -, -⟩
        · omega
        · have h38 : Q = 38 := by omega
          rw [h38] at hQp
          norm_num at hQp
      · rcases hQs with hQ0 | ⟨hQp, hQn, -⟩
        · have h38 : T = 38 := by omega
          rw [h38] at hTp
          norm_num at hTp
        · rcases OMA.A086522Proof.pair T Q hTp hQp hsum with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · rcases k with _ | j
            · change 31 = next (pre 1) 7 at hQ
              rw [OMA.A086522Proof.pre1, OMA.A086522Proof.next2] at hQ
              omega
            · exact hTn (OMA.A086522Proof.mem7 j)
          · apply hQn
            rw [hpre]
            simp
          · exact hQn (OMA.A086522Proof.mem7 k)
  exact ⟨h19, fun h => h19 (h 19 (by norm_num) (by norm_num))⟩
