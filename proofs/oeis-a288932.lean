import OMAStatements.S_oeis_a288932

-- Problem: A288932: Fixed point of the mapping 00->1000, 10->10101, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a288932.lean:0 (declaration OMA.S_oeis_a288932.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write words as blocks A = 10 and B = 1 followed by the final letters 00
-- (blkFlat; true is A, false is B). If the block list ends with A (so that every B is followed
-- by a letter 1), the mapping acts blockwise: A -> A A B (10 -> 10101), B -> B (the letter 1 before
-- a 1 is kept) and the final 00 -> A 00 (blkMu). Starting from 00 (no blocks), the k-th image has
-- 2^k - 1 blocks A and 2^k - 1 - k blocks B, hence 2 + 2 (2^k - 1) + 2^k - 1 - k letters, which is
-- A123720(k+1) = 2^(k+1) + 2^k - (k+1).

namespace P1A288932

open OMA.S_oeis_a288932

/-- Blocks to letters: true is the block 10, false is the block 1; the word ends with 00. -/
def blkFlat : List Bool → List Bool
  | [] => [false, false]
  | true :: bs => true :: false :: blkFlat bs
  | false :: bs => true :: blkFlat bs

/-- The mapping on blocks: 10 -> 10 10 1, 1 -> 1, and the final 00 -> 10 00. -/
def blkMu : List Bool → List Bool
  | [] => [true]
  | true :: bs => true :: true :: false :: blkMu bs
  | false :: bs => false :: blkMu bs

/-- The number of blocks 10. -/
def cntA : List Bool → ℕ
  | [] => 0
  | true :: bs => cntA bs + 1
  | false :: bs => cntA bs

/-- The number of blocks 1. -/
def cntB : List Bool → ℕ
  | [] => 0
  | true :: bs => cntB bs
  | false :: bs => cntB bs + 1

theorem flat_head (bs : List Bool) : ∃ z, blkFlat (bs ++ [true]) = true :: z := by
  cases bs with
  | nil => exact ⟨_, rfl⟩
  | cons b bs =>
    cases b with
    | true => exact ⟨_, rfl⟩
    | false => exact ⟨_, rfl⟩

theorem mu_end (cs : List Bool) : ∃ bs, blkMu cs = bs ++ [true] := by
  induction cs with
  | nil => exact ⟨[], rfl⟩
  | cons c cs ih =>
    obtain ⟨bs, hbs⟩ := ih
    cases c with
    | true =>
      refine ⟨true :: true :: false :: bs, ?_⟩
      show true :: true :: false :: blkMu cs = true :: true :: false :: (bs ++ [true])
      rw [hbs]
    | false =>
      refine ⟨false :: bs, ?_⟩
      show false :: blkMu cs = false :: (bs ++ [true])
      rw [hbs]

theorem key (bs : List Bool) :
    step (blkFlat (bs ++ [true])) = blkFlat (blkMu (bs ++ [true])) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | true =>
      show step (true :: false :: blkFlat (bs ++ [true])) =
        blkFlat (true :: true :: false :: blkMu (bs ++ [true]))
      rw [show step (true :: false :: blkFlat (bs ++ [true])) =
        true :: false :: true :: false :: true :: step (blkFlat (bs ++ [true])) from rfl, ih]
      rfl
    | false =>
      obtain ⟨z, hz⟩ := flat_head bs
      show step (true :: blkFlat (bs ++ [true])) = blkFlat (false :: blkMu (bs ++ [true]))
      rw [hz, show step (true :: true :: z) = true :: step (true :: z) from rfl, ← hz, ih]
      rfl

theorem iter_flat (k : ℕ) : step^[k] [false, false] = blkFlat (blkMu^[k] []) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    rcases k with _ | k
    · rfl
    · rw [Function.iterate_succ_apply']
      obtain ⟨bs, hbs⟩ := mu_end (blkMu^[k] [])
      rw [hbs, key]

theorem len_flat (bs : List Bool) : (blkFlat bs).length = 2 + 2 * cntA bs + cntB bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | true =>
      show (true :: false :: blkFlat bs).length = 2 + 2 * (cntA bs + 1) + cntB bs
      rw [List.length_cons, List.length_cons]
      omega
    | false =>
      show (true :: blkFlat bs).length = 2 + 2 * cntA bs + (cntB bs + 1)
      rw [List.length_cons]
      omega

theorem cntA_mu (bs : List Bool) : cntA (blkMu bs) = 2 * cntA bs + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | true =>
      show cntA (blkMu bs) + 1 + 1 = 2 * (cntA bs + 1) + 1
      omega
    | false =>
      show cntA (blkMu bs) = 2 * cntA bs + 1
      exact ih

theorem cntB_mu (bs : List Bool) : cntB (blkMu bs) = cntB bs + cntA bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | true =>
      show cntB (blkMu bs) + 1 = cntB bs + (cntA bs + 1)
      omega
    | false =>
      show cntB (blkMu bs) + 1 = cntB bs + 1 + cntA bs
      omega

theorem counts (k : ℕ) :
    cntA (blkMu^[k] []) + 1 = 2 ^ k ∧ cntB (blkMu^[k] []) + k + 1 = 2 ^ k := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Function.iterate_succ_apply', cntA_mu, cntB_mu, pow_succ]
    refine ⟨?_, ?_⟩
    · omega
    · omega

end P1A288932

open OMA.S_oeis_a288932 P1A288932 in
theorem OMA.solution : type_of% @OMA.S_oeis_a288932.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hit : iter (k + 1) = blkFlat (blkMu^[k] []) := by
    show step^[k + 1 - 1] [false, false] = blkFlat (blkMu^[k] [])
    rw [show k + 1 - 1 = k by omega]
    exact iter_flat k
  obtain ⟨h1, h2⟩ := counts k
  have h1' : (cntA (blkMu^[k] []) : ℤ) + 1 = 2 ^ k := by exact_mod_cast h1
  have h2' : (cntB (blkMu^[k] []) : ℤ) + k + 1 = 2 ^ k := by exact_mod_cast h2
  rw [hit, len_flat]
  show (((2 + 2 * cntA (blkMu^[k] []) + cntB (blkMu^[k] []) : ℕ)) : ℤ) =
    2 ^ (k + 1) + 2 ^ (k + 1 - 1) - ((k + 1 : ℕ) : ℤ)
  rw [show k + 1 - 1 = k by omega]
  push_cast
  linear_combination 2 * h1' + h2'
