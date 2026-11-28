import OMAStatements.S_oeis_a297469
import Mathlib

-- Problem: OEIS A297469, conjecture of Sloane for the sequence bb of Kimberling's system
-- aa(n) = least new, bb(n) = aa(n) + cc(n-1), cc(n) = least new (aa(0), bb(0), cc(0) = 1, 2, 3):
-- bb(2t) = 10t + 1 + [the exponent of 2 in t is odd] for t >= 1, and bb(2t+1) = 10t + 7.
-- Statement: statements/oeis-a297469.lean (declaration OMA.S_oeis_a297469.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let e(j) = 1 if j = 0 or the exponent of 2 in j is even, else 0, and
-- BB(j) = 5j + 1 + e(j). Then e(2t+1) = 1 and e(2t) + e(t) = 1 for t >= 1. Invariant: after
-- step n the set of placed numbers is {1, ..., cc(n)} together with the numbers BB(j), j <= n;
-- bb(n) = BB(n); cc(2t) = 5t + 3 and cc(2t+1) = 5t + 5. The numbers BB(j) are 1 or 2 modulo 5.
-- Step 2t+1: the least new number is 5t + 4, so bb = 10t + 7 = BB(2t+1), and then the least
-- new number is 5t + 5. Step 2t+2: exactly one of 5t + 6, 5t + 7 is BB(t+1), which is already
-- placed; the other one is aa, namely 5(t+1) + 2 - e(t+1). So
-- bb = 10(t+1) + 2 - e(t+1) = BB(2t+2), and then the least new number is 5t + 8.

namespace OMA.A297469

open OMA.S_oeis_a297469

lemma mex_eq (s : Finset ℕ) (m : ℕ) (hm : 0 < m) (hns : m ∉ s)
    (hall : ∀ k, 0 < k → k < m → k ∈ s) : leastNew s = m := by
  unfold leastNew
  apply le_antisymm
  · exact Nat.sInf_le ⟨hm, hns⟩
  · refine le_csInf ⟨m, hm, hns⟩ ?_
    rintro k ⟨hk, hks⟩
    by_contra hlt
    exact hks (hall k hk (by omega))

/-- The correction term: bb(j) = 5 j + 1 + e(j). -/
def e (j : ℕ) : ℕ := if j = 0 ∨ Even (padicValNat 2 j) then 1 else 0

lemma e_le (j : ℕ) : e j ≤ 1 := by
  unfold e; split_ifs <;> omega

lemma e_odd (t : ℕ) : e (2 * t + 1) = 1 := by
  unfold e
  rw [if_pos]
  right
  rw [padicValNat.eq_zero_of_not_dvd (by omega)]
  exact ⟨0, rfl⟩

lemma e_even (t : ℕ) (ht : 1 ≤ t) : e (2 * t) + e t = 1 := by
  have hv : padicValNat 2 (2 * t) = padicValNat 2 t + 1 := by
    rw [padicValNat.mul (by norm_num) (by omega), padicValNat_self, add_comm]
  unfold e
  rw [hv]
  by_cases h : Even (padicValNat 2 t)
  · rw [if_neg, if_pos (Or.inr h)]
    rintro (h0 | h1)
    · omega
    · rw [Nat.even_add_one] at h1; exact h1 h
  · rw [if_pos, if_neg]
    · rintro (h0 | h1)
      · omega
      · exact h h1
    · right; rw [Nat.even_add_one]; exact h

/-- The closed form of bb. -/
def BB (n : ℕ) : ℕ := 5 * n + 1 + e n

lemma step_even (t : ℕ) (U : Finset ℕ)
    (hU : ∀ k, k ∈ U ↔ (1 ≤ k ∧ k ≤ 5 * t + 3) ∨ ∃ j, j ≤ 2 * t ∧ k = BB j) :
    leastNew U = 5 * t + 4 ∧
    leastNew (insert (5 * t + 4 + (5 * t + 3)) (insert (5 * t + 4) U)) = 5 * t + 5 ∧
    ∀ k, k ∈ insert (5 * t + 5) (insert (5 * t + 4 + (5 * t + 3)) (insert (5 * t + 4) U)) ↔
      (1 ≤ k ∧ k ≤ 5 * t + 5) ∨ ∃ j, j ≤ 2 * t + 1 ∧ k = BB j := by
  have hBB : BB (2 * t + 1) = 5 * t + 4 + (5 * t + 3) := by
    unfold BB; rw [e_odd]; ring
  have notBB : ∀ k, (k = 5 * t + 4 ∨ k = 5 * t + 5) → ¬ ∃ j, j ≤ 2 * t ∧ k = BB j := by
    rintro k hk ⟨j, -, hj⟩
    have := e_le j
    unfold BB at hj
    omega
  refine ⟨?_, ?_, ?_⟩
  · apply mex_eq _ _ (by omega)
    · rw [hU]
      rintro (h | h)
      · omega
      · exact notBB _ (Or.inl rfl) h
    · intro k hk hlt
      rw [hU]; left; omega
  · apply mex_eq _ _ (by omega)
    · rw [Finset.mem_insert, Finset.mem_insert, hU]
      rintro (h | h | h | h)
      · omega
      · omega
      · omega
      · exact notBB _ (Or.inr rfl) h
    · intro k hk hlt
      rw [Finset.mem_insert, Finset.mem_insert, hU]
      rcases Nat.lt_or_ge k (5 * t + 4) with h | h
      · right; right; left; omega
      · right; left; omega
  · intro k
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, hU]
    constructor
    · rintro (h | h | h | h | ⟨j, hj, hk⟩)
      · left; omega
      · right; exact ⟨2 * t + 1, le_rfl, by rw [hBB, h]⟩
      · left; omega
      · left; omega
      · right; exact ⟨j, by omega, hk⟩
    · rintro (⟨h1, h2⟩ | ⟨j, hj, hk⟩)
      · rcases Nat.lt_or_ge k (5 * t + 4) with h | h
        · right; right; right; left; omega
        · rcases Nat.lt_or_ge k (5 * t + 5) with h' | h'
          · right; right; left; omega
          · left; omega
      · rcases Nat.lt_or_ge j (2 * t + 1) with h | h
        · right; right; right; right; exact ⟨j, by omega, hk⟩
        · right; left
          rw [hk, show j = 2 * t + 1 by omega, hBB]

lemma step_odd (t : ℕ) (U : Finset ℕ)
    (hU : ∀ k, k ∈ U ↔ (1 ≤ k ∧ k ≤ 5 * t + 5) ∨ ∃ j, j ≤ 2 * t + 1 ∧ k = BB j) :
    leastNew U = 5 * (t + 1) + 2 - e (t + 1) ∧
    leastNew (insert (5 * (t + 1) + 2 - e (t + 1) + (5 * t + 5))
      (insert (5 * (t + 1) + 2 - e (t + 1)) U)) = 5 * (t + 1) + 3 ∧
    ∀ k, k ∈ insert (5 * (t + 1) + 3) (insert (5 * (t + 1) + 2 - e (t + 1) + (5 * t + 5))
      (insert (5 * (t + 1) + 2 - e (t + 1)) U)) ↔
      (1 ≤ k ∧ k ≤ 5 * (t + 1) + 3) ∨ ∃ j, j ≤ 2 * (t + 1) ∧ k = BB j := by
  have he := e_le (t + 1)
  have hee := e_even (t + 1) (by omega)
  have hBB : BB (2 * (t + 1)) = 5 * (t + 1) + 2 - e (t + 1) + (5 * t + 5) := by
    unfold BB; omega
  have hBt : BB (t + 1) = 5 * (t + 1) + 1 + e (t + 1) := rfl
  have hBtmem : BB (t + 1) ∈ U := by
    rw [hU]; right; exact ⟨t + 1, by omega, rfl⟩
  -- a number BB j that is equal to 5 t + 6 or 5 t + 7 is BB (t + 1)
  have onlyBB : ∀ j, (BB j = 5 * t + 6 ∨ BB j = 5 * t + 7) → j = t + 1 := by
    intro j hj
    have := e_le j
    unfold BB at hj
    omega
  have notBB8 : ¬ ∃ j, j ≤ 2 * t + 1 ∧ 5 * (t + 1) + 3 = BB j := by
    rintro ⟨j, -, hj⟩
    have := e_le j
    unfold BB at hj
    omega
  set A := 5 * (t + 1) + 2 - e (t + 1) with hA
  have hAne : A ≠ BB (t + 1) := by rw [hBt, hA]; omega
  have hA67 : A = 5 * t + 6 ∨ A = 5 * t + 7 := by rw [hA]; omega
  have hB67 : BB (t + 1) = 5 * t + 6 ∨ BB (t + 1) = 5 * t + 7 := by rw [hBt]; omega
  have hAU : A ∉ U := by
    rw [hU]
    rintro (h | ⟨j, hj, hk⟩)
    · omega
    · have hjt : j = t + 1 := onlyBB j (by rw [← hk]; exact hA67)
      rw [hjt] at hk
      exact hAne hk
  -- each number 5 t + 6, 5 t + 7 is A or BB (t + 1)
  have cover : ∀ k, (k = 5 * t + 6 ∨ k = 5 * t + 7) → k = A ∨ k = BB (t + 1) := by
    intro k hk; omega
  refine ⟨?_, ?_, ?_⟩
  · apply mex_eq _ _ (by omega) hAU
    intro k hk hlt
    rcases Nat.lt_or_ge k (5 * t + 6) with h | h
    · rw [hU]; left; omega
    · rcases cover k (by omega) with h' | h'
      · omega
      · rw [h']; exact hBtmem
  · apply mex_eq _ _ (by omega)
    · rw [Finset.mem_insert, Finset.mem_insert, hU]
      rintro (h | h | h | h)
      · omega
      · omega
      · omega
      · exact notBB8 h
    · intro k hk hlt
      rw [Finset.mem_insert, Finset.mem_insert]
      rcases Nat.lt_or_ge k (5 * t + 6) with h | h
      · right; right; rw [hU]; left; omega
      · rcases cover k (by omega) with h' | h'
        · right; left; exact h'
        · right; right; rw [h']; exact hBtmem
  · intro k
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, hU]
    constructor
    · rintro (h | h | h | h | ⟨j, hj, hk⟩)
      · left; omega
      · right; exact ⟨2 * (t + 1), le_rfl, by rw [hBB, h]⟩
      · left; omega
      · left; omega
      · right; exact ⟨j, by omega, hk⟩
    · rintro (⟨h1, h2⟩ | ⟨j, hj, hk⟩)
      · rcases Nat.lt_or_ge k (5 * t + 6) with h | h
        · right; right; right; left; omega
        · rcases Nat.lt_or_ge k (5 * t + 8) with h' | h'
          · rcases cover k (by omega) with h'' | h''
            · right; right; left; exact h''
            · right; right; right; right; exact ⟨t + 1, by omega, h''⟩
          · left; omega
      · rcases Nat.lt_or_ge j (2 * t + 2) with h | h
        · right; right; right; right; exact ⟨j, by omega, hk⟩
        · right; left
          rw [hk, show j = 2 * (t + 1) by omega, hBB]

lemma state_succ (n : ℕ) (a b c : ℕ) (U : Finset ℕ) (h : state n = (a, b, c, U)) :
    state (n + 1) = (leastNew U, leastNew U + c,
      leastNew (insert (leastNew U + c) (insert (leastNew U) U)),
      insert (leastNew (insert (leastNew U + c) (insert (leastNew U) U)))
        (insert (leastNew U + c) (insert (leastNew U) U))) := by
  rw [state, h]

/-- The invariant, for even and odd indices together. -/
lemma inv (t : ℕ) :
    (∃ a U, state (2 * t) = (a, BB (2 * t), 5 * t + 3, U) ∧
      ∀ k, k ∈ U ↔ (1 ≤ k ∧ k ≤ 5 * t + 3) ∨ ∃ j, j ≤ 2 * t ∧ k = BB j) ∧
    (∃ a U, state (2 * t + 1) = (a, BB (2 * t + 1), 5 * t + 5, U) ∧
      ∀ k, k ∈ U ↔ (1 ≤ k ∧ k ≤ 5 * t + 5) ∨ ∃ j, j ≤ 2 * t + 1 ∧ k = BB j) := by
  have odd_of_even : ∀ t, (∃ a U, state (2 * t) = (a, BB (2 * t), 5 * t + 3, U) ∧
      ∀ k, k ∈ U ↔ (1 ≤ k ∧ k ≤ 5 * t + 3) ∨ ∃ j, j ≤ 2 * t ∧ k = BB j) →
      (∃ a U, state (2 * t + 1) = (a, BB (2 * t + 1), 5 * t + 5, U) ∧
      ∀ k, k ∈ U ↔ (1 ≤ k ∧ k ≤ 5 * t + 5) ∨ ∃ j, j ≤ 2 * t + 1 ∧ k = BB j) := by
    rintro t ⟨a, U, hst, hU⟩
    obtain ⟨s1, s2, s3⟩ := step_even t U hU
    have h := state_succ (2 * t) _ _ _ _ hst
    rw [s1, s2] at h
    refine ⟨5 * t + 4, _, ?_, s3⟩
    rw [h]
    have : BB (2 * t + 1) = 5 * t + 4 + (5 * t + 3) := by unfold BB; rw [e_odd]; ring
    rw [this]
  induction t with
  | zero =>
    have h0 : (∃ a U, state (2 * 0) = (a, BB (2 * 0), 5 * 0 + 3, U) ∧
        ∀ k, k ∈ U ↔ (1 ≤ k ∧ k ≤ 5 * 0 + 3) ∨ ∃ j, j ≤ 2 * 0 ∧ k = BB j) := by
      refine ⟨1, {1, 2, 3}, ?_, ?_⟩
      · have : BB 0 = 2 := by unfold BB e; simp
        simp only [Nat.mul_zero, Nat.zero_add]
        rw [state, this]
      · intro k
        have : BB 0 = 2 := by unfold BB e; simp
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · intro h; left; omega
        · rintro (h | ⟨j, hj, hk⟩)
          · omega
          · rw [show j = 0 by omega, this] at hk; omega
    exact ⟨h0, odd_of_even 0 h0⟩
  | succ t ih =>
    obtain ⟨a, U, hst, hU⟩ := ih.2
    obtain ⟨s1, s2, s3⟩ := step_odd t U hU
    have h := state_succ (2 * t + 1) _ _ _ _ hst
    rw [s1, s2] at h
    have hev : (∃ a U, state (2 * (t + 1)) = (a, BB (2 * (t + 1)), 5 * (t + 1) + 3, U) ∧
        ∀ k, k ∈ U ↔ (1 ≤ k ∧ k ≤ 5 * (t + 1) + 3) ∨ ∃ j, j ≤ 2 * (t + 1) ∧ k = BB j) := by
      refine ⟨5 * (t + 1) + 2 - e (t + 1), _, ?_, s3⟩
      rw [show 2 * (t + 1) = 2 * t + 1 + 1 by ring, h]
      have he := e_le (t + 1)
      have hee := e_even (t + 1) (by omega)
      have : BB (2 * t + 1 + 1) = 5 * (t + 1) + 2 - e (t + 1) + (5 * t + 5) := by
        rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring]
        unfold BB; omega
      rw [this]
    exact ⟨hev, odd_of_even (t + 1) hev⟩

theorem main' :
    (∀ t : ℕ, 1 ≤ t → bb (2 * t) = 10 * t + 1 + if Odd (padicValNat 2 t) then 1 else 0) ∧
    (∀ t : ℕ, bb (2 * t + 1) = 10 * t + 7) := by
  constructor
  · intro t ht
    obtain ⟨a, U, hst, -⟩ := (inv t).1
    unfold bb
    rw [hst]
    show BB (2 * t) = _
    have hee := e_even t ht
    have het : e t = if Odd (padicValNat 2 t) then 0 else 1 := by
      unfold e
      by_cases h : Even (padicValNat 2 t)
      · rw [if_pos (Or.inr h), if_neg (Nat.not_odd_iff_even.mpr h)]
      · rw [if_neg (by rintro (h0 | h1); omega; exact h h1), if_pos (Nat.not_even_iff_odd.mp h)]
    unfold BB
    by_cases h : Odd (padicValNat 2 t)
    · rw [if_pos h] at het ⊢; omega
    · rw [if_neg h] at het ⊢; omega
  · intro t
    obtain ⟨a, U, hst, -⟩ := (inv t).2
    unfold bb
    rw [hst]
    show BB (2 * t + 1) = _
    unfold BB
    rw [e_odd]; ring

end OMA.A297469

theorem OMA.solution : type_of% @OMA.S_oeis_a297469.main :=
  OMA.A297469.main'
