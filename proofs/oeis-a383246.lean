import OMAStatements.S_oeis_a383246
import Mathlib

/-!
# Repunits connect every two terms

A repunit starts with one, so it may follow every term with a
nonzero last digit. It ends with one, so it can precede every
admissible term. Fresh repunits keep the recursion defined, and
omitting any repunit would bound the injective sequence. A repunit
chosen sufficiently late then forces any omitted admissible value to
bound a later choice, contradicting finiteness of the smaller choices.
-/

namespace OMA.A383246

open OMA.S_oeis_a383246

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
  refine ⟨?_, ?_, ?_⟩
  · apply Nat.pos_of_ne_zero
    apply (Nat.digits_ne_nil_iff_ne_zero (b := 10)).mp
    rw [repunit_digits, List.replicate_succ]
    simp
  · simp [repunit_digits]
  · rw [repunit_digits, List.reverse_replicate]
    exact List.isChain_replicate_of_rel _ (by norm_num [digitStep] : digitStep 1 1)

/-- An admissible value has a nonzero last digit. -/
private lemma lastDigit_ne_zero {m : ℕ} (hm : admissible m) : lastDigit m ≠ 0 := by
  cases h : Nat.digits 10 m with
  | nil => exact (((Nat.digits_ne_nil_iff_ne_zero (b := 10)).mpr hm.1.ne') h).elim
  | cons d ds =>
    have hd : d ≠ 0 := fun hz => hm.2.1 (by simp [h, hz])
    simpa [lastDigit, h] using hd

/-- A repunit may follow any number with a nonzero last digit. -/
private lemma before_repunit (previous k : ℕ) (hp : lastDigit previous ≠ 0) :
    follows previous (repunit k) := by
  rw [follows, firstDigit, repunit_digits, List.reverse_replicate,
    List.replicate_succ, List.headD_cons]
  unfold digitStep
  omega

/-- A repunit ends in one, so it may precede any number. -/
private lemma after_repunit (k m : ℕ) : follows (repunit k) m := by
  simp only [follows, lastDigit, repunit_digits, List.replicate_succ, List.headD_cons, digitStep]
  norm_num

/-- The state records the new choice and inserts it among the used values. -/
private lemma state_step (n : ℕ) : state (n + 1) = (insert (a n) (state n).1, a n) := rfl

/-- A fresh repunit is a candidate whenever the previous digit is nonzero. -/
private lemma next_spec (used : Finset ℕ) (previous : ℕ) (hp : lastDigit previous ≠ 0) :
    admissible (next used previous) ∧ next used previous ∉ used ∧
      follows previous (next used previous) := by
  obtain ⟨_, ⟨k, rfl⟩, hfresh⟩ := infinite_repunits.exists_notMem_finset used
  exact Nat.sInf_mem (s := {v | admissible v ∧ v ∉ used ∧ follows previous v})
    ⟨repunit k, repunit_admissible k, hfresh, before_repunit _ k hp⟩

/-- The seed ends in one and all subsequent last digits come from admissible values. -/
private lemma state_last_ne_zero (n : ℕ) : lastDigit (state n).2 ≠ 0 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [state_step]
    exact lastDigit_ne_zero (next_spec _ _ ih).1

/-- Each step produces an admissible fresh value satisfying the boundary rule. -/
private lemma step_spec (n : ℕ) :
    admissible (a n) ∧ a n ∉ (state n).1 ∧ follows (state n).2 (a n) :=
  next_spec _ _ (state_last_ne_zero n)

/-- A candidate bounds the least choice from above. -/
private lemma step_le (n m : ℕ) (hm : admissible m) (hfresh : m ∉ (state n).1)
    (hfollow : follows (state n).2 m) : a n ≤ m := by
  exact Nat.sInf_le (s := {v | admissible v ∧ v ∉ (state n).1 ∧ follows (state n).2 v})
    ⟨hm, hfresh, hfollow⟩

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
    exact step_le n _ (repunit_admissible k) (fun hf => h (used_occurs n hf)) (before_repunit _ k (state_last_ne_zero n))
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
    step_le (i + 1) m hm (fun hf => h (used_occurs (i + 1) hf)) (hlast.symm ▸ after_repunit k m)
  have hindex : i + 1 ≤ N := hN hle
  omega

end OMA.A383246

theorem OMA.solution : type_of% @OMA.S_oeis_a383246.main := by
  refine ⟨A383246.injective_a, fun m => ⟨?_, A383246.admissible_occurs m⟩⟩
  rintro ⟨n, rfl⟩
  exact (A383246.step_spec n).1
