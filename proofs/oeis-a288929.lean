import OMAStatements.S_oeis_a288929

-- Problem: A288929: Fixed point of the mapping 00->1000, 10->10011, starting with 00.
-- Upstream: formal-conjectures statements/oeis-a288929.lean:0 (declaration OMA.S_oeis_a288929.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: write words as blocks P = 100, Q = 10 and O = 1 followed by the final letters 00
-- (bflat). If the block list ends with Q (so that every P and every O is followed by a letter 1),
-- the mapping acts blockwise: P -> P O Q (100 -> 10011 0), Q -> P O O (10 -> 10011),
-- O -> O, and the final 00 -> Q 00 (bmu). With p, q, o the block counts, one step gives
-- p' = p + q, q' = p + 1, o' = o + p + 2q, and 3p + q = o + k after k steps. The length is
-- 2 + 3p + 2q + o, so L(k+2) = L(k+1) + L(k) + k + 3, the recurrence of A192967(k+2), with the
-- same first values 2 and 4.

namespace P1A288929

open OMA.S_oeis_a288929

/-- The blocks: P is 100, Q is 10, O is 1. -/
inductive Blk
  | P
  | Q
  | O

/-- Blocks to letters; the word ends with 00. -/
def bflat : List Blk → List Bool
  | [] => [false, false]
  | Blk.P :: bs => true :: false :: false :: bflat bs
  | Blk.Q :: bs => true :: false :: bflat bs
  | Blk.O :: bs => true :: bflat bs

/-- The mapping on blocks: P -> P O Q, Q -> P O O, O -> O, and the final 00 -> Q 00. -/
def bmu : List Blk → List Blk
  | [] => [Blk.Q]
  | Blk.P :: bs => Blk.P :: Blk.O :: Blk.Q :: bmu bs
  | Blk.Q :: bs => Blk.P :: Blk.O :: Blk.O :: bmu bs
  | Blk.O :: bs => Blk.O :: bmu bs

def cntP : List Blk → ℕ
  | [] => 0
  | Blk.P :: bs => cntP bs + 1
  | Blk.Q :: bs => cntP bs
  | Blk.O :: bs => cntP bs

def cntQ : List Blk → ℕ
  | [] => 0
  | Blk.P :: bs => cntQ bs
  | Blk.Q :: bs => cntQ bs + 1
  | Blk.O :: bs => cntQ bs

def cntO : List Blk → ℕ
  | [] => 0
  | Blk.P :: bs => cntO bs
  | Blk.Q :: bs => cntO bs
  | Blk.O :: bs => cntO bs + 1

theorem flat_head (bs : List Blk) : ∃ z, bflat (bs ++ [Blk.Q]) = true :: z := by
  cases bs with
  | nil => exact ⟨_, rfl⟩
  | cons b bs =>
    cases b with
    | P => exact ⟨_, rfl⟩
    | Q => exact ⟨_, rfl⟩
    | O => exact ⟨_, rfl⟩

theorem mu_end (cs : List Blk) : ∃ bs, bmu cs = bs ++ [Blk.Q] := by
  induction cs with
  | nil => exact ⟨[], rfl⟩
  | cons c cs ih =>
    obtain ⟨bs, hbs⟩ := ih
    cases c with
    | P =>
      refine ⟨Blk.P :: Blk.O :: Blk.Q :: bs, ?_⟩
      show Blk.P :: Blk.O :: Blk.Q :: bmu cs = Blk.P :: Blk.O :: Blk.Q :: (bs ++ [Blk.Q])
      rw [hbs]
    | Q =>
      refine ⟨Blk.P :: Blk.O :: Blk.O :: bs, ?_⟩
      show Blk.P :: Blk.O :: Blk.O :: bmu cs = Blk.P :: Blk.O :: Blk.O :: (bs ++ [Blk.Q])
      rw [hbs]
    | O =>
      refine ⟨Blk.O :: bs, ?_⟩
      show Blk.O :: bmu cs = Blk.O :: (bs ++ [Blk.Q])
      rw [hbs]

theorem key (bs : List Blk) :
    step (bflat (bs ++ [Blk.Q])) = bflat (bmu (bs ++ [Blk.Q])) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | P =>
      obtain ⟨z, hz⟩ := flat_head bs
      show step (true :: false :: false :: bflat (bs ++ [Blk.Q])) =
        bflat (Blk.P :: Blk.O :: Blk.Q :: bmu (bs ++ [Blk.Q]))
      rw [show step (true :: false :: false :: bflat (bs ++ [Blk.Q])) =
        true :: false :: false :: true :: true :: step (false :: bflat (bs ++ [Blk.Q])) from rfl,
        hz, show step (false :: true :: z) = false :: step (true :: z) from rfl, ← hz, ih]
      rfl
    | Q =>
      show step (true :: false :: bflat (bs ++ [Blk.Q])) =
        bflat (Blk.P :: Blk.O :: Blk.O :: bmu (bs ++ [Blk.Q]))
      rw [show step (true :: false :: bflat (bs ++ [Blk.Q])) =
        true :: false :: false :: true :: true :: step (bflat (bs ++ [Blk.Q])) from rfl, ih]
      rfl
    | O =>
      obtain ⟨z, hz⟩ := flat_head bs
      show step (true :: bflat (bs ++ [Blk.Q])) = bflat (Blk.O :: bmu (bs ++ [Blk.Q]))
      rw [hz, show step (true :: true :: z) = true :: step (true :: z) from rfl, ← hz, ih]
      rfl

theorem iter_flat (k : ℕ) : w k = bflat (bmu^[k] []) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show step (w k) = bflat (bmu^[k + 1] [])
    rw [ih, Function.iterate_succ_apply']
    rcases k with _ | k
    · rfl
    · rw [Function.iterate_succ_apply']
      obtain ⟨bs, hbs⟩ := mu_end (bmu^[k] [])
      rw [hbs, key]

theorem len_flat (bs : List Blk) :
    (bflat bs).length = 2 + 3 * cntP bs + 2 * cntQ bs + cntO bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | P =>
      show (true :: false :: false :: bflat bs).length =
        2 + 3 * (cntP bs + 1) + 2 * cntQ bs + cntO bs
      rw [List.length_cons, List.length_cons, List.length_cons]
      omega
    | Q =>
      show (true :: false :: bflat bs).length = 2 + 3 * cntP bs + 2 * (cntQ bs + 1) + cntO bs
      rw [List.length_cons, List.length_cons]
      omega
    | O =>
      show (true :: bflat bs).length = 2 + 3 * cntP bs + 2 * cntQ bs + (cntO bs + 1)
      rw [List.length_cons]
      omega

theorem cntP_mu (bs : List Blk) : cntP (bmu bs) = cntP bs + cntQ bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | P =>
      show cntP (bmu bs) + 1 = cntP bs + 1 + cntQ bs
      omega
    | Q =>
      show cntP (bmu bs) + 1 = cntP bs + (cntQ bs + 1)
      omega
    | O =>
      show cntP (bmu bs) = cntP bs + cntQ bs
      exact ih

theorem cntQ_mu (bs : List Blk) : cntQ (bmu bs) = cntP bs + 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | P =>
      show cntQ (bmu bs) + 1 = cntP bs + 1 + 1
      omega
    | Q =>
      show cntQ (bmu bs) = cntP bs + 1
      exact ih
    | O =>
      show cntQ (bmu bs) = cntP bs + 1
      exact ih

theorem cntO_mu (bs : List Blk) : cntO (bmu bs) = cntO bs + cntP bs + 2 * cntQ bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b with
    | P =>
      show cntO (bmu bs) + 1 = cntO bs + (cntP bs + 1) + 2 * cntQ bs
      omega
    | Q =>
      show cntO (bmu bs) + 1 + 1 = cntO bs + cntP bs + 2 * (cntQ bs + 1)
      omega
    | O =>
      show cntO (bmu bs) + 1 = cntO bs + 1 + cntP bs + 2 * cntQ bs
      omega

theorem cnt_inv (k : ℕ) : 3 * cntP (bmu^[k] []) + cntQ (bmu^[k] []) = cntO (bmu^[k] []) + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', cntP_mu, cntQ_mu, cntO_mu]
    omega

theorem A_rec (m : ℕ) : A192967 (m + 2) = A192967 (m + 1) + A192967 m + (m + 1) := rfl

theorem main_aux : ∀ k : ℕ,
    (w k).length = A192967 (k + 2) ∧ (w (k + 1)).length = A192967 (k + 3)
  | 0 => ⟨by decide, by decide⟩
  | k + 1 => by
    obtain ⟨h0, h1⟩ := main_aux k
    refine ⟨h1, ?_⟩
    have l0 := len_flat (bmu^[k] [])
    rw [← iter_flat k] at l0
    have i1 := iter_flat (k + 1)
    rw [Function.iterate_succ_apply'] at i1
    have i2 := iter_flat (k + 1 + 1)
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply'] at i2
    have l1 := len_flat (bmu (bmu^[k] []))
    have l2 := len_flat (bmu (bmu (bmu^[k] [])))
    simp only [cntP_mu, cntQ_mu, cntO_mu] at l1 l2
    rw [← i1] at l1
    rw [← i2] at l2
    have iv := cnt_inv k
    have e := A_rec (k + 2)
    rw [show k + 2 + 2 = k + 1 + 3 by omega, show k + 2 + 1 = k + 3 by omega] at e
    omega

end P1A288929

open OMA.S_oeis_a288929 P1A288929 in
theorem OMA.solution : type_of% @OMA.S_oeis_a288929.main := by
  intro n
  exact (main_aux n).1
