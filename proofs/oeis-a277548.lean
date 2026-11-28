import OMAStatements.S_oeis_a277548
import Mathlib.Tactic

open OMA.S_oeis_a277548

namespace BaseFiveRanks

private lemma digit_mul (q : ℕ) : lastDigit (5*q) = lastDigit q := by
  by_cases h : q = 0
  · simp [h]
  · rw [lastDigit]
    simp [h]

private lemma digit_nonzero (q r : ℕ) (hr : 0 < r) (hr' : r < 5) :
    lastDigit (5*q+r) = r := by
  rw [lastDigit]
  simp [show (5*q+r)%5 = r by omega, Nat.ne_of_gt hr]

private def upto (m : ℕ) : ℕ := Nat.count lastFour (m+1)

private lemma upto_zero : upto 0 = 0 := by
  have h : ¬ lastFour 0 := by unfold lastFour; rw [lastDigit]; decide
  simp [upto, Nat.count_succ, h]

private lemma step (m : ℕ) :
    upto (m+1) = upto m + if lastDigit (m+1) = 4 then 1 else 0 :=
  Nat.count_succ _ _

private lemma partial_block (q r : ℕ) (hr : r ≤ 4) :
    upto (5*q+r) = upto (5*q) + if r = 4 then 1 else 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hr' : r ≠ 4 := by omega
    rw [show 5*q+(r+1) = (5*q+r)+1 by omega, step, ih (by omega), if_neg hr', add_zero]
    rw [show 5*q+r+1 = 5*q+(r+1) by omega, digit_nonzero q (r+1) (by omega) (by omega)]

private lemma full_block (q : ℕ) : upto (5*q) = q + upto q := by
  induction q with
  | zero => simp
  | succ q ih =>
    have h := step (5*q+4)
    rw [show 5*q+4+1 = 5*(q+1) by omega, digit_mul, partial_block q 4 (by decide),
      if_pos rfl, ih] at h
    rw [step q]
    omega

private lemma characterize (m : ℕ) :
    4*upto m ≤ m ∧ (4*upto m = m → Digits01 (upto m)) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hz : m = 0
    · simp [hz, upto_zero, Digits01.zero]
    let q := m/5
    let r := m%5
    have parts : m = 5*q+r := by dsimp [q,r]; omega
    have remainder : r < 5 := Nat.mod_lt _ (by decide)
    have ⟨bound, digits⟩ := ih q (Nat.div_lt_self (Nat.pos_of_ne_zero hz) (by decide))
    have recn : upto m = q + upto q + if r = 4 then 1 else 0 := calc
      upto m = upto (5*q+r) := congrArg upto parts
      _ = _ := by rw [partial_block q r (by omega), full_block]
    by_cases four : r = 4
    · rw [if_pos four] at recn
      refine ⟨by omega, fun eqn => ?_⟩
      have d := Digits01.append1 (digits (by omega))
      convert d using 1
      omega
    · rw [if_neg four] at recn
      refine ⟨by omega, fun eqn => ?_⟩
      have d := Digits01.append0 (digits (by omega))
      convert d using 1
      omega

private lemma digits_rank {s : ℕ} (h : Digits01 s) :
    upto (4*s) = s ∧ (0 < s → lastDigit (4*s) = 4) := by
  induction h with
  | zero => simp [upto_zero]
  | @append0 s _ ih =>
    obtain ⟨hc,hg⟩ := ih
    rw [show 4*(5*s) = 5*(4*s) by omega, full_block, hc, digit_mul]
    exact ⟨by omega, fun hs => hg (by omega)⟩
  | @append1 s _ ih =>
    obtain ⟨hc,_⟩ := ih
    rw [show 4*(5*s+1) = 5*(4*s)+4 by omega, partial_block _ 4 (by decide),
      if_pos rfl, full_block, hc, digit_nonzero _ 4 (by decide) (by decide)]
    exact ⟨by omega, fun _ => rfl⟩

private lemma many : (Set.ofPred lastFour).Infinite := by
  let f : ℕ → ℕ := fun q => 5*q+4
  have mono : StrictMono f := fun _ _ h => by dsimp [f]; omega
  refine (Set.infinite_range_of_injective mono.injective).mono ?_
  rintro _ ⟨q, rfl⟩
  exact digit_nonzero q 4 (by decide) (by decide)

theorem result (n : ℕ) (hn : 0 < n) : Nat.nth lastFour (n-1) = 4*n ↔ Digits01 n := by
  constructor
  · intro he
    have rank := Nat.count_nth_succ_of_infinite many (n-1)
    rw [he] at rank
    have hc : upto (4*n) = n := by unfold upto; omega
    have sm := (characterize (4*n)).2 (by omega)
    rwa [hc] at sm
  · intro hs
    obtain ⟨rank,member⟩ := digits_rank hs
    have hm : lastFour (4*n) := member hn
    unfold upto at rank
    rw [Nat.count_succ, if_pos hm] at rank
    rw [show n-1 = Nat.count lastFour (4*n) by omega]
    exact Nat.nth_count hm

end BaseFiveRanks

theorem OMA.solution : type_of% @OMA.S_oeis_a277548.main := BaseFiveRanks.result
