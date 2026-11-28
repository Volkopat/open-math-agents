import OMAStatements.S_oeis_a297465
import Mathlib

-- Problem: OEIS A297465, conjecture of Kimberling for the system a(n), b(n), c(n) = least new,
-- d(n) = a(n) + b(n) + c(n): with the terms counted from 1, 0 <= 10n - 6 - 3a <= 2,
-- 0 <= 10n - 2 - 3b <= 3, 0 <= 10n + 1 - 3c <= 3, 0 <= 10n - 3 - d <= 2.
-- Statement: statements/oeis-a297465.lean (declaration OMA.S_oeis_a297465.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof (indices from 0). Let del(3j) = 1, del(3j+1) = 2 - del(j), del(3j+2) = 0 and
-- D(n) = 10n + 7 - del(n). Then d(n) = D(n), and D(n) is 5, 6 or 7 modulo 10. Invariant: after
-- step n the placed numbers are {1, ..., M} and the D(i) with i <= n, where M = 10j + 3,
-- 10j + 7, 10j + 10 for n = 3j, 3j + 1, 3j + 2. In the block of the numbers 10j + 1, ...,
-- 10j + 10 the only number D(i) is D(j), which is 10j + 7 - del(j) and is placed before step
-- 3j + 1. So step 3j places 10j + 1, 10j + 2, 10j + 3 (sum 30j + 6 = D(3j)); step 3j + 1
-- places the three numbers of 10j + 4, ..., 10j + 7 that are not D(j) (sum
-- 30j + 15 + del(j) = D(3j + 1)); step 3j + 2 places 10j + 8, 10j + 9, 10j + 10 (sum
-- 30j + 27 = D(3j + 2)). The four inequalities follow in each case.

namespace OMA.A297465

open OMA.S_oeis_a297465

lemma mex_eq (s : Finset ℕ) (m : ℕ) (hm : 0 < m) (hns : m ∉ s)
    (hall : ∀ k, 0 < k → k < m → k ∈ s) : leastNew s = m := by
  unfold leastNew
  apply le_antisymm
  · exact Nat.sInf_le ⟨hm, hns⟩
  · refine le_csInf ⟨m, hm, hns⟩ ?_
    rintro k ⟨hk, hks⟩
    by_contra hlt
    exact hks (hall k hk (by omega))

/-- Three least new numbers in a row. -/
lemma three_mex (U : Finset ℕ) (x y z : ℕ) (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hxU : x ∉ U) (hyU : y ∉ U) (hzU : z ∉ U)
    (h1 : ∀ k, 0 < k → k < x → k ∈ U) (h2 : ∀ k, x < k → k < y → k ∈ U)
    (h3 : ∀ k, y < k → k < z → k ∈ U) :
    leastNew U = x ∧ leastNew (insert x U) = y ∧ leastNew (insert y (insert x U)) = z := by
  refine ⟨mex_eq U x hx hxU h1, ?_, ?_⟩
  · apply mex_eq _ _ (by omega)
    · rw [Finset.mem_insert]; rintro (h | h)
      · omega
      · exact hyU h
    · intro k hk hlt
      rw [Finset.mem_insert]
      rcases Nat.lt_trichotomy k x with h | h | h
      · right; exact h1 k hk h
      · left; exact h
      · right; exact h2 k h hlt
  · apply mex_eq _ _ (by omega)
    · rw [Finset.mem_insert, Finset.mem_insert]; rintro (h | h | h)
      · omega
      · omega
      · exact hzU h
    · intro k hk hlt
      rw [Finset.mem_insert, Finset.mem_insert]
      rcases Nat.lt_trichotomy k x with h | h | h
      · right; right; exact h1 k hk h
      · right; left; exact h
      · rcases Nat.lt_trichotomy k y with h' | h' | h'
        · right; right; exact h2 k h h'
        · left; exact h'
        · right; right; exact h3 k h' hlt

/-- The correction term of d: d(n) = 10 n + 7 - del(n). -/
def del : ℕ → ℕ
  | n => if h : n % 3 = 0 then 1 else if h' : n % 3 = 2 then 0 else 2 - del (n / 3)
decreasing_by omega

lemma del_le (n : ℕ) : del n ≤ 2 := by
  rw [del]; split_ifs <;> omega

lemma del0 (j : ℕ) : del (3 * j) = 1 := by
  rw [del, dif_pos (by omega)]

lemma del1 (j : ℕ) : del (3 * j + 1) = 2 - del j := by
  rw [del, dif_neg (by omega), dif_neg (by omega), show (3 * j + 1) / 3 = j by omega]

lemma del2 (j : ℕ) : del (3 * j + 2) = 0 := by
  rw [del, dif_neg (by omega), dif_pos (by omega)]

/-- The closed form of d. -/
def D (n : ℕ) : ℕ := 10 * n + 7 - del n

lemma D_mod (i : ℕ) : D i % 10 = 5 ∨ D i % 10 = 6 ∨ D i % 10 = 7 := by
  have := del_le i
  unfold D; omega

lemma state_succ (n : ℕ) (a0 b0 c0 d0 : ℕ) (U : Finset ℕ) (h : state n = (a0, b0, c0, d0, U)) :
    state (n + 1) = (leastNew U, leastNew (insert (leastNew U) U),
      leastNew (insert (leastNew (insert (leastNew U) U)) (insert (leastNew U) U)),
      leastNew U + leastNew (insert (leastNew U) U)
        + leastNew (insert (leastNew (insert (leastNew U) U)) (insert (leastNew U) U)),
      insert (leastNew U + leastNew (insert (leastNew U) U)
        + leastNew (insert (leastNew (insert (leastNew U) U)) (insert (leastNew U) U)))
        (insert (leastNew (insert (leastNew (insert (leastNew U) U)) (insert (leastNew U) U)))
          (insert (leastNew (insert (leastNew U) U)) (insert (leastNew U) U)))) := by
  rw [state, h]

/-- The used set after a step, described by a bound M and the numbers D i with i <= n. -/
def Good (U : Finset ℕ) (M n : ℕ) : Prop :=
  ∀ k, k ∈ U ↔ (1 ≤ k ∧ k ≤ M) ∨ ∃ i, i ≤ n ∧ k = D i

/-- A general step: from a good set to the next state, if the three least new numbers are
known. -/
lemma gen_step (n M M' x y z : ℕ) (a0 b0 c0 d0 : ℕ) (U : Finset ℕ)
    (hst : state n = (a0, b0, c0, d0, U)) (hU : Good U M n)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hxU : x ∉ U) (hyU : y ∉ U) (hzU : z ∉ U)
    (h1 : ∀ k, 0 < k → k < x → k ∈ U) (h2 : ∀ k, x < k → k < y → k ∈ U)
    (h3 : ∀ k, y < k → k < z → k ∈ U)
    (hD : D (n + 1) = x + y + z) (hM : M ≤ M') (hzM : z ≤ M')
    (hfill : ∀ k, M < k → k ≤ M' → k = x ∨ k = y ∨ k = z ∨ k ∈ U) :
    ∃ U', state (n + 1) = (x, y, z, x + y + z, U') ∧ Good U' M' (n + 1) := by
  obtain ⟨m1, m2, m3⟩ := three_mex U x y z hx hxy hyz hxU hyU hzU h1 h2 h3
  have h := state_succ n _ _ _ _ _ hst
  rw [m1, m2, m3] at h
  refine ⟨_, h, ?_⟩
  intro k
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, hU]
  constructor
  · rintro (h | h | h | h | ⟨h, h'⟩ | ⟨i, hi, hk⟩)
    · right; exact ⟨n + 1, le_rfl, by rw [hD, h]⟩
    · left; omega
    · left; omega
    · left; omega
    · left; omega
    · right; exact ⟨i, by omega, hk⟩
  · rintro (⟨hk1, hk2⟩ | ⟨i, hi, hk⟩)
    · rcases Nat.lt_or_ge M k with hlt | hge
      · rcases hfill k hlt hk2 with h | h | h | h
        · right; right; right; left; exact h
        · right; right; left; exact h
        · right; left; exact h
        · right; right; right; right; exact (hU k).mp h
      · right; right; right; right; left; exact ⟨hk1, hge⟩
    · rcases Nat.lt_or_ge i (n + 1) with hlt | hge
      · right; right; right; right; right; exact ⟨i, by omega, hk⟩
      · left; rw [hk, show i = n + 1 by omega, hD]

/-- Membership of the numbers of a block, above the bound. -/
lemma not_mem_of_mod (U : Finset ℕ) (M n k : ℕ) (hU : Good U M n) (hk : M < k)
    (hmod : k % 10 ≠ 5 ∧ k % 10 ≠ 6 ∧ k % 10 ≠ 7) : k ∉ U := by
  rw [hU]
  rintro (h | ⟨i, -, hi⟩)
  · omega
  · have := D_mod i
    rw [← hi] at this
    omega

lemma inv (j : ℕ) :
    (∃ U, state (3 * j) = (10 * j + 1, 10 * j + 2, 10 * j + 3, 30 * j + 6, U) ∧
      Good U (10 * j + 3) (3 * j)) ∧
    (∃ y z U, state (3 * j + 1) = (10 * j + 4, y, z, 30 * j + 15 + del j, U) ∧
      (y = 10 * j + 5 ∨ y = 10 * j + 6) ∧ (z = 10 * j + 6 ∨ z = 10 * j + 7) ∧
      Good U (10 * j + 7) (3 * j + 1)) ∧
    (∃ U, state (3 * j + 2) = (10 * j + 8, 10 * j + 9, 10 * j + 10, 30 * j + 27, U) ∧
      Good U (10 * j + 10) (3 * j + 2)) := by
  -- step B: from 3 j to 3 j + 1
  have stepB : ∀ j, (∃ U, state (3 * j) = (10 * j + 1, 10 * j + 2, 10 * j + 3, 30 * j + 6, U) ∧
      Good U (10 * j + 3) (3 * j)) →
      (∃ y z U, state (3 * j + 1) = (10 * j + 4, y, z, 30 * j + 15 + del j, U) ∧
      (y = 10 * j + 5 ∨ y = 10 * j + 6) ∧ (z = 10 * j + 6 ∨ z = 10 * j + 7) ∧
      Good U (10 * j + 7) (3 * j + 1)) := by
    rintro j ⟨U, hst, hU⟩
    have hdl := del_le j
    have hDj : D j = 10 * j + 7 - del j := rfl
    have hDmem : D j ∈ U := (hU _).mpr (Or.inr ⟨j, by omega, rfl⟩)
    -- a number 10 j + p (p = 5, 6, 7) that is in U is D j
    have only : ∀ k, 10 * j + 3 < k → k ≤ 10 * j + 7 → k ∈ U → k = D j := by
      intro k hk1 hk2 hk
      rcases (hU k).mp hk with h | ⟨i, hi, hki⟩
      · omega
      · have := del_le i
        have hij : i = j := by unfold D at hki; omega
        rw [hki, hij]
    have h4 : 10 * j + 4 ∉ U := not_mem_of_mod U _ _ _ hU (by omega) (by omega)
    have low : ∀ k, 0 < k → k < 10 * j + 4 → k ∈ U := by
      intro k hk hlt; exact (hU k).mpr (Or.inl ⟨hk, by omega⟩)
    have hD1 : D (3 * j + 1) = 30 * j + 15 + del j := by
      unfold D; rw [del1]; omega
    have hdcases : del j = 0 ∨ del j = 1 ∨ del j = 2 := by omega
    rcases hdcases with h0 | h0 | h0
    · -- D j = 10 j + 7: the new numbers are 10 j + 4, 5, 6
      obtain ⟨U', hst', hU'⟩ := gen_step (3 * j) (10 * j + 3) (10 * j + 7)
        (10 * j + 4) (10 * j + 5) (10 * j + 6) _ _ _ _ U hst hU (by omega) (by omega) (by omega)
        h4 (fun h => by have := only _ (by omega) (by omega) h; omega)
        (fun h => by have := only _ (by omega) (by omega) h; omega)
        low (fun k h1 h2 => by omega) (fun k h1 h2 => by omega)
        (by rw [hD1]; omega) (by omega) (by omega)
        (fun k h1 h2 => by
          rcases Nat.lt_or_ge k (10 * j + 7) with h | h
          · omega
          · right; right; right
            rw [show k = D j by omega]; exact hDmem)
      refine ⟨_, _, U', ?_, Or.inl rfl, Or.inl rfl, hU'⟩
      rw [hst']; congr 4; omega
    · -- D j = 10 j + 6: the new numbers are 10 j + 4, 5, 7
      obtain ⟨U', hst', hU'⟩ := gen_step (3 * j) (10 * j + 3) (10 * j + 7)
        (10 * j + 4) (10 * j + 5) (10 * j + 7) _ _ _ _ U hst hU (by omega) (by omega) (by omega)
        h4 (fun h => by have := only _ (by omega) (by omega) h; omega)
        (fun h => by have := only _ (by omega) (by omega) h; omega)
        low (fun k h1 h2 => by omega)
        (fun k h1 h2 => by rw [show k = D j by omega]; exact hDmem)
        (by rw [hD1]; omega) (by omega) (by omega)
        (fun k h1 h2 => by
          rcases Nat.lt_trichotomy k (10 * j + 6) with h | h | h
          · omega
          · right; right; right
            rw [show k = D j by omega]; exact hDmem
          · omega)
      refine ⟨_, _, U', ?_, Or.inl rfl, Or.inr rfl, hU'⟩
      rw [hst']; congr 4; omega
    · -- D j = 10 j + 5: the new numbers are 10 j + 4, 6, 7
      obtain ⟨U', hst', hU'⟩ := gen_step (3 * j) (10 * j + 3) (10 * j + 7)
        (10 * j + 4) (10 * j + 6) (10 * j + 7) _ _ _ _ U hst hU (by omega) (by omega) (by omega)
        h4 (fun h => by have := only _ (by omega) (by omega) h; omega)
        (fun h => by have := only _ (by omega) (by omega) h; omega)
        low (fun k h1 h2 => by rw [show k = D j by omega]; exact hDmem)
        (fun k h1 h2 => by omega)
        (by rw [hD1]; omega) (by omega) (by omega)
        (fun k h1 h2 => by
          rcases Nat.lt_trichotomy k (10 * j + 5) with h | h | h
          · omega
          · right; right; right
            rw [show k = D j by omega]; exact hDmem
          · omega)
      refine ⟨_, _, U', ?_, Or.inr rfl, Or.inr rfl, hU'⟩
      rw [hst']; congr 4; omega
  -- step C: from 3 j + 1 to 3 j + 2
  have stepC : ∀ j, (∃ y z U, state (3 * j + 1) = (10 * j + 4, y, z, 30 * j + 15 + del j, U) ∧
      (y = 10 * j + 5 ∨ y = 10 * j + 6) ∧ (z = 10 * j + 6 ∨ z = 10 * j + 7) ∧
      Good U (10 * j + 7) (3 * j + 1)) →
      (∃ U, state (3 * j + 2) = (10 * j + 8, 10 * j + 9, 10 * j + 10, 30 * j + 27, U) ∧
      Good U (10 * j + 10) (3 * j + 2)) := by
    rintro j ⟨y, z, U, hst, -, -, hU⟩
    have low : ∀ k, 0 < k → k < 10 * j + 8 → k ∈ U := by
      intro k hk hlt; exact (hU k).mpr (Or.inl ⟨hk, by omega⟩)
    obtain ⟨U', hst', hU'⟩ := gen_step (3 * j + 1) (10 * j + 7) (10 * j + 10)
      (10 * j + 8) (10 * j + 9) (10 * j + 10) _ _ _ _ U hst hU (by omega) (by omega) (by omega)
      (not_mem_of_mod U _ _ _ hU (by omega) (by omega))
      (not_mem_of_mod U _ _ _ hU (by omega) (by omega))
      (not_mem_of_mod U _ _ _ hU (by omega) (by omega))
      low (fun k h1 h2 => by omega) (fun k h1 h2 => by omega)
      (by unfold D; rw [show 3 * j + 1 + 1 = 3 * j + 2 by ring, del2]; omega) (by omega) (by omega)
      (fun k h1 h2 => by omega)
    refine ⟨U', ?_, hU'⟩
    rw [show 3 * j + 2 = 3 * j + 1 + 1 by ring, hst']; congr 4; omega
  induction j with
  | zero =>
    have h0 : ∃ U, state (3 * 0) = (10 * 0 + 1, 10 * 0 + 2, 10 * 0 + 3, 30 * 0 + 6, U) ∧
        Good U (10 * 0 + 3) (3 * 0) := by
      refine ⟨{1, 2, 3, 6}, by rw [state], ?_⟩
      intro k
      have hD0 : D 0 = 6 := by unfold D; rw [show (0 : ℕ) = 3 * 0 by ring, del0]
      simp only [Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro (h | h | h | h)
        · left; omega
        · left; omega
        · left; omega
        · right; exact ⟨0, le_rfl, by rw [hD0, h]⟩
      · rintro (h | ⟨i, hi, hk⟩)
        · omega
        · rw [show i = 0 by omega, hD0] at hk; omega
    exact ⟨h0, stepB 0 h0, stepC 0 (stepB 0 h0)⟩
  | succ j ih =>
    obtain ⟨U, hst, hU⟩ := ih.2.2
    have low : ∀ k, 0 < k → k < 10 * j + 11 → k ∈ U := by
      intro k hk hlt; exact (hU k).mpr (Or.inl ⟨hk, by omega⟩)
    obtain ⟨U', hst', hU'⟩ := gen_step (3 * j + 2) (10 * j + 10) (10 * j + 13)
      (10 * j + 11) (10 * j + 12) (10 * j + 13) _ _ _ _ U hst hU (by omega) (by omega) (by omega)
      (not_mem_of_mod U _ _ _ hU (by omega) (by omega))
      (not_mem_of_mod U _ _ _ hU (by omega) (by omega))
      (not_mem_of_mod U _ _ _ hU (by omega) (by omega))
      low (fun k h1 h2 => by omega) (fun k h1 h2 => by omega)
      (by unfold D; rw [show 3 * j + 2 + 1 = 3 * (j + 1) by ring, del0]; omega) (by omega) (by omega)
      (fun k h1 h2 => by omega)
    have hA : ∃ U, state (3 * (j + 1)) = (10 * (j + 1) + 1, 10 * (j + 1) + 2, 10 * (j + 1) + 3,
        30 * (j + 1) + 6, U) ∧ Good U (10 * (j + 1) + 3) (3 * (j + 1)) := by
      refine ⟨U', ?_, ?_⟩
      · rw [show 3 * (j + 1) = 3 * j + 2 + 1 by ring, hst',
          show 10 * (j + 1) + 1 = 10 * j + 11 by ring, show 10 * (j + 1) + 2 = 10 * j + 12 by ring,
          show 10 * (j + 1) + 3 = 10 * j + 13 by ring,
          show 30 * (j + 1) + 6 = 10 * j + 11 + (10 * j + 12) + (10 * j + 13) by ring]
      · rw [show 3 * (j + 1) = 3 * j + 2 + 1 by ring, show 10 * (j + 1) + 3 = 10 * j + 13 by ring]
        exact hU'
    exact ⟨hA, stepB (j + 1) hA, stepC (j + 1) (stepB (j + 1) hA)⟩

theorem main' : ∀ n : ℕ,
    (0 ≤ 10 * ((n : ℤ) + 1) - 6 - 3 * (a n : ℤ) ∧ 10 * ((n : ℤ) + 1) - 6 - 3 * (a n : ℤ) ≤ 2) ∧
    (0 ≤ 10 * ((n : ℤ) + 1) - 2 - 3 * (b n : ℤ) ∧ 10 * ((n : ℤ) + 1) - 2 - 3 * (b n : ℤ) ≤ 3) ∧
    (0 ≤ 10 * ((n : ℤ) + 1) + 1 - 3 * (c n : ℤ) ∧ 10 * ((n : ℤ) + 1) + 1 - 3 * (c n : ℤ) ≤ 3) ∧
    (0 ≤ 10 * ((n : ℤ) + 1) - 3 - (d n : ℤ) ∧ 10 * ((n : ℤ) + 1) - 3 - (d n : ℤ) ≤ 2) := by
  intro n
  obtain ⟨j, hj⟩ : ∃ j, n = 3 * j ∨ n = 3 * j + 1 ∨ n = 3 * j + 2 := ⟨n / 3, by omega⟩
  obtain ⟨⟨U0, h0, -⟩, ⟨y, z, U1, h1, hy, hz, -⟩, ⟨U2, h2, -⟩⟩ := inv j
  have hdl := del_le j
  unfold a b c d
  rcases hj with rfl | rfl | rfl
  · rw [h0]; push_cast; refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega
  · rw [h1]
    push_cast
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega
  · rw [h2]; push_cast; refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> omega

end OMA.A297465

theorem OMA.solution : type_of% @OMA.S_oeis_a297465.main :=
  OMA.A297465.main'
