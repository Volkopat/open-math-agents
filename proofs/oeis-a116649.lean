import OMAStatements.S_oeis_a116649
import Mathlib

-- Problem: OEIS A116649, conjecture of Karttunen: each position i where the least missing
-- positive integer A116648 of the XOR sequence A116626 increases is odd.
-- Statement: statements/oeis-a116649.lean (declaration OMA.S_oeis_a116649.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. The least missing number increases at index i only if a(i) is equal to the old least
-- missing number m. Let i be even and c = a(i-1). The admissible set (numbers t > 1 with t and
-- t XOR c not present) is not empty, because a large power of two is admissible. Let t be its
-- least element, so a(i) = t XOR c. All terms are positive: an even-index term t XOR c is not
-- zero because t is not present but c is, and an odd-index term is the number t chosen one
-- step before. Assume a(i) = m. Then m XOR c = t is not present, m is not present and m > 1
-- (1 = a(1) is present), so m is admissible and t <= m. But t is positive and not present, so
-- m <= t. Thus t = m and m XOR c = m, so c = 0, a contradiction.

namespace OMA.A116649

open OMA.S_oeis_a116649

/-- The set of admissible numbers at the even index n + 2. -/
def P (n : ℕ) : Set ℕ :=
  {i : ℕ | 1 < i ∧ ∀ j : ℕ, 1 ≤ j → j < n + 2 → a j ≠ i ∧ a j ≠ i ^^^ a (n + 1)}

lemma xcr (x y : ℕ) : x ^^^ y ^^^ y = x := by
  rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]

lemma a_one : a 1 = 1 := by rw [a]

lemma a_even (n : ℕ) (hn : Even n) : a (n + 2) = sInf (P n) ^^^ a (n + 1) := by
  rw [a, if_pos hn]; rfl

lemma a_odd (n : ℕ) (hn : ¬ Even n) : a (n + 2) = a (n + 1) ^^^ a n := by
  rw [a, if_neg hn]

/-- The admissible set is not empty: a large power of two is admissible. -/
lemma P_nonempty (n : ℕ) : (P n).Nonempty := by
  let B := ∑ j ∈ Finset.range (n + 2), a j
  have hB : ∀ j, j < n + 2 → a j < 2 ^ (B + 1) := by
    intro j hj
    have h1 : a j ≤ B :=
      Finset.single_le_sum (f := a) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hj)
    have h2 : B + 1 < 2 ^ (B + 1) := Nat.lt_two_pow_self
    omega
  refine ⟨2 ^ (B + 1), ?_, ?_⟩
  · calc 1 < 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (B + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · intro j _ hj
    have hc := hB (n + 1) (by omega)
    have hge : 2 ^ (B + 1) ≤ 2 ^ (B + 1) ^^^ a (n + 1) := by
      apply Nat.ge_two_pow_of_testBit
      rw [Nat.testBit_xor, Nat.testBit_two_pow_self, Nat.testBit_lt_two_pow hc]
      rfl
    have := hB j hj
    constructor <;> omega

lemma sInf_P_mem (n : ℕ) : sInf (P n) ∈ P n := Nat.sInf_mem (P_nonempty n)

/-- At an odd index n + 3 (n even) the term is the admissible number chosen at index n + 2. -/
lemma a_odd' (n : ℕ) (hn : Even n) : a (n + 3) = sInf (P n) := by
  rw [show n + 3 = (n + 1) + 2 by ring, a_odd (n + 1) (by simpa [Nat.even_add_one] using hn),
    a_even n hn, xcr]

lemma a_pos : ∀ n : ℕ, 1 ≤ n → 0 < a n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · interval_cases n
      · rw [a_one]; norm_num
      · rw [a_even 0 (by decide)]
        have h := (sInf_P_mem 0).2 1 (by norm_num) (by norm_num)
        rw [Nat.pos_iff_ne_zero]
        intro h0
        exact h.1 (Nat.xor_eq_zero_iff.mp h0).symm
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
      rcases Nat.even_or_odd m with hm | hm
      · rw [a_odd' m hm]
        have := (sInf_P_mem m).1
        omega
      · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by obtain ⟨t, ht⟩ := hm; omega⟩
        have hk : Even (k + 2) := by
          have : ¬ Even (k + 1) := Nat.not_even_iff_odd.mpr hm
          rw [Nat.even_add_one] at this
          rw [Nat.even_add]; simp [not_not.mp this]
        rw [show k + 1 + 3 = (k + 2) + 2 by ring, a_even (k + 2) hk]
        have h := (sInf_P_mem (k + 2)).2 (k + 2 + 1) (by omega) (by omega)
        rw [Nat.pos_iff_ne_zero]
        intro h0
        exact h.1 (Nat.xor_eq_zero_iff.mp h0).symm

/-- The set whose infimum is `mex n`. -/
def M (n : ℕ) : Set ℕ := {m : ℕ | 0 < m ∧ ∀ j : ℕ, 1 ≤ j → j ≤ n → a j ≠ m}

lemma mex_eq (n : ℕ) : mex n = sInf (M n) := rfl

theorem main' : ∀ i : ℕ, 1 ≤ i → mex (i - 1) < mex i → Odd i := by
  intro i hi hlt
  by_contra hodd
  have hev : Even i := Nat.not_odd_iff_even.mp hodd
  obtain ⟨n, rfl⟩ : ∃ n, i = n + 2 := by
    obtain ⟨t, ht⟩ := hev
    exact ⟨i - 2, by omega⟩
  have hn : Even n := by
    rw [Nat.even_add] at hev; simpa using hev
  rw [show n + 2 - 1 = n + 1 by omega, mex_eq, mex_eq] at hlt
  set m := sInf (M (n + 1)) with hm
  -- the old least missing number is in its set
  have hmem : m ∈ M (n + 1) := by
    apply Nat.sInf_mem
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hsub : M (n + 2) ⊆ M (n + 1) := fun x hx => ⟨hx.1, fun j h1 h2 => hx.2 j h1 (by omega)⟩
    have : M (n + 2) = ∅ := Set.subset_empty_iff.mp (hemp ▸ hsub)
    rw [this, Nat.sInf_empty] at hlt
    omega
  -- it is not in the new set, so the new term is equal to it
  have hnot : m ∉ M (n + 2) := Nat.notMem_of_lt_sInf hlt
  have ham : a (n + 2) = m := by
    by_contra hne
    apply hnot
    refine ⟨hmem.1, fun j h1 h2 => ?_⟩
    rcases Nat.lt_or_ge j (n + 2) with h | h
    · exact hmem.2 j h1 (by omega)
    · rw [show j = n + 2 by omega]; exact hne
  have hi0 := sInf_P_mem n
  set i0 := sInf (P n) with hi0def
  rw [a_even n hn, ← hi0def] at ham
  have hmi : m ^^^ a (n + 1) = i0 := by rw [← ham, xcr]
  have hmP : m ∈ P n := by
    refine ⟨?_, fun j h1 h2 => ⟨hmem.2 j h1 (by omega), ?_⟩⟩
    · have h1 := hmem.1
      have h2 := hmem.2 1 (by norm_num) (by omega)
      rw [a_one] at h2
      omega
    · rw [hmi]; exact (hi0.2 j h1 h2).1
  have h1 : i0 ≤ m := Nat.sInf_le hmP
  have h2 : m ≤ i0 := Nat.sInf_le ⟨by have := hi0.1; omega, fun j h1 h2 => (hi0.2 j h1 (by omega)).1⟩
  have h3 : i0 = m := le_antisymm h1 h2
  rw [h3] at ham
  have h4 : a (n + 1) = 0 := by
    have : m ^^^ a (n + 1) ^^^ m = m ^^^ m := by rw [ham]
    rw [Nat.xor_comm m (a (n + 1)), xcr, Nat.xor_self] at this
    exact this
  have := a_pos (n + 1) (by omega)
  omega

end OMA.A116649

theorem OMA.solution : type_of% @OMA.S_oeis_a116649.main :=
  OMA.A116649.main'
