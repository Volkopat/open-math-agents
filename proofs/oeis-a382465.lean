import OMAStatements.S_oeis_a382465
import Mathlib

/-!
# Repunits connect every two terms

A string of ones is always eligible and can precede every admissible
number. There are infinitely many such strings, so each greedy step is
defined and chooses a fresh number. Each repunit must occur, since
omitting it would bound the entire injective sequence. If any admissible
number were omitted, a sufficiently late repunit would force another
choice at most that number, contradicting finiteness of those choices.
-/

namespace OMA.A382465

open OMA.S_oeis_a382465

/-- A repunit of length k + 1. -/
private def repunit (k : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate (k + 1) 1)

/-- The decimal digit list of a repunit is precisely its string of ones. -/
private lemma repunit_digits (k : ℕ) :
    Nat.digits 10 (repunit k) = List.replicate (k + 1) 1 := by
  apply Nat.digits_ofDigits 10 (by decide)
  · intro x hx
    have hx' : x = 1 := (List.mem_replicate.mp hx).2
    omega
  · intro h
    simp

/-- Repunits with different lengths are distinct. -/
private lemma infinite_repunits : (Set.range repunit).Infinite := by
  apply Set.infinite_range_of_injective
  intro i j hij
  have h := congrArg (fun x => (Nat.digits 10 x).length) hij
  simp only [repunit_digits, List.length_replicate] at h
  omega

/-- All digits of a repunit are odd, so its internal steps are allowed. -/
private lemma repunit_admissible (k : ℕ) : admissible (repunit k) := by
  constructor
  · apply Nat.pos_of_ne_zero
    apply (Nat.digits_ne_nil_iff_ne_zero (b := 10)).mp
    rw [repunit_digits, List.replicate_succ]
    simp
  · rw [repunit_digits, List.reverse_replicate]
    exact List.isChain_replicate_of_rel _ (by norm_num [digitStep] : digitStep 1 1)

/-- A repunit may follow any previous term. -/
private lemma before_repunit (previous k : ℕ) : follows previous (repunit k) := by
  rw [follows, firstDigit, repunit_digits, List.reverse_replicate,
    List.replicate_succ, List.headD_cons]
  norm_num [digitStep]

/-- A positive number has a nonzero leading decimal digit. -/
private lemma firstDigit_pos {m : ℕ} (hm : 0 < m) : 0 < firstDigit m := by
  have hd := (Nat.digits_ne_nil_iff_ne_zero (b := 10)).mpr hm.ne'
  rw [firstDigit, List.headD_eq_head?_getD, List.head?_reverse,
    List.getLast?_eq_some_getLast hd, Option.getD_some]
  exact Nat.pos_of_ne_zero (Nat.getLast_digit_ne_zero 10 hm.ne')

/-- A repunit ends in one, below every positive even leading digit. -/
private lemma after_repunit (k : ℕ) {m : ℕ} (hm : admissible m) : follows (repunit k) m := by
  have hp := firstDigit_pos hm.1
  simp only [follows, lastDigit, repunit_digits, List.replicate_succ, List.headD_cons, digitStep]
  omega

/-- Every greedy step has a candidate, by choosing a fresh repunit. -/
private lemma step_spec (n : ℕ) :
    admissible (a n) ∧ a n ∉ (state n).1 ∧ follows (state n).2 (a n) := by
  obtain ⟨_, ⟨k, rfl⟩, hfresh⟩ := infinite_repunits.exists_notMem_finset (state n).1
  exact Nat.sInf_mem (s := {v | admissible v ∧ v ∉ (state n).1 ∧ follows (state n).2 v})
    ⟨repunit k, repunit_admissible k, hfresh, before_repunit _ k⟩

/-- A candidate bounds the least choice from above. -/
private lemma step_le (n m : ℕ) (hm : admissible m) (hfresh : m ∉ (state n).1)
    (hfollow : follows (state n).2 m) : a n ≤ m := by
  exact Nat.sInf_le (s := {v | admissible v ∧ v ∉ (state n).1 ∧ follows (state n).2 v})
    ⟨hm, hfresh, hfollow⟩

/-- The state records the new choice and inserts it among the used values. -/
private lemma state_step (n : ℕ) : state (n + 1) = (insert (a n) (state n).1, a n) := rfl

/-- Every entry persists in all later states. -/
private lemma used_mono : Monotone (fun n => (state n).1) := by
  apply monotone_nat_of_le_succ
  intro n m hm
  rw [state_step]
  exact Finset.mem_insert_of_mem hm

/-- A just-chosen value is in the next state. -/
private lemma used_next (n : ℕ) : a n ∈ (state (n + 1)).1 := by
  simp [state_step]

/-- Any used value is an output of the sequence. -/
private lemma used_occurs {m : ℕ} (n : ℕ) (hm : m ∈ (state n).1) : ∃ i, a i = m := by
  induction n with
  | zero => simp [state] at hm
  | succ n ih =>
    rw [state_step, Finset.mem_insert] at hm
    rcases hm with h | h
    · exact ⟨n, h.symm⟩
    · exact ih h

/-- A later choice cannot equal an earlier one. -/
private lemma injective_a : Function.Injective a := by
  have distinct (i j : ℕ) (hij : i < j) : a i ≠ a j := by
    intro h
    exact (step_spec j).2.1 (h ▸ used_mono (Nat.succ_le_of_lt hij) (used_next i))
  intro i j h
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (distinct i j hij h)
  · exact hij
  · exact False.elim (distinct j i hij h.symm)

/-- Skipping an always-eligible repunit would bound every output. -/
private lemma repunit_occurs (k : ℕ) : ∃ i, a i = repunit k := by
  by_contra h
  have hbound : Set.range a ⊆ Set.Iic (repunit k) := by
    rintro _ ⟨n, rfl⟩
    exact step_le n _ (repunit_admissible k) (fun hf => h (used_occurs n hf)) (before_repunit _ k)
  exact (Set.infinite_range_of_injective injective_a) ((Set.finite_Iic _).subset hbound)

/-- A late repunit forces a choice no larger than an omitted admissible value. -/
private lemma admissible_occurs (m : ℕ) (hm : admissible m) : ∃ i, a i = m := by
  by_contra h
  have hfinite : {i | a i ≤ m}.Finite :=
    (Set.finite_Iic m).preimage injective_a.injOn
  obtain ⟨N, hN⟩ := hfinite.bddAbove
  obtain ⟨_, ⟨k, rfl⟩, hfresh⟩ := infinite_repunits.exists_notMem_finset (state (N + 1)).1
  obtain ⟨i, hi⟩ := repunit_occurs k
  have hiN : N < i := by
    by_contra! hle
    apply hfresh
    rw [← hi]
    exact used_mono (Nat.succ_le_succ hle) (used_next i)
  have hlast : (state (i + 1)).2 = repunit k := by rw [state_step]; exact hi
  have hle : a (i + 1) ≤ m :=
    step_le (i + 1) m hm (fun hf => h (used_occurs (i + 1) hf)) (hlast.symm ▸ after_repunit k hm)
  have hindex : i + 1 ≤ N := hN hle
  omega

end OMA.A382465

theorem OMA.solution : type_of% @OMA.S_oeis_a382465.main := by
  refine ⟨A382465.injective_a, fun m => ⟨?_, A382465.admissible_occurs m⟩⟩
  rintro ⟨n, rfl⟩
  exact (A382465.step_spec n).1
