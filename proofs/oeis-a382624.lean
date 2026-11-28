import OMAStatements.S_oeis_a382624
import Mathlib

/-!
There are infinitely many numbers consisting entirely of nines. Each
is admissible and can follow any predecessor, so the greedy step always
has a choice. No term repeats, hence eventually every term exceeds any
fixed bound. This forces the algorithm to use each admissible number
with odd leading digit. After any sufficiently late all-nine term,
an unused admissible number can follow it and would bound the next term
from above. Thus every admissible number is used.
-/

namespace OMA.A382624

open S_oeis_a382624

/-- A number with one initial nine and one additional nine per recursion step. -/
def nines : ℕ → ℕ
  | 0 => 9
  | n + 1 => 10 * nines n + 9

/-- The decimal digit list of the repeated-nine number. -/
lemma digits_nines (n : ℕ) : Nat.digits 10 (nines n) = List.replicate (n + 1) 9 := by
  induction n with
  | zero => decide
  | succ n ih =>
    rw [nines, Nat.digits_def' (by decide : 1 < 10) (by omega)]
    rw [show (10 * nines n + 9) % 10 = 9 by omega,
      show (10 * nines n + 9) / 10 = nines n by omega, ih]
    exact (List.replicate_succ (n := n + 1)).symm

/-- Every repeated-nine number is admissible and starts and ends with a nine. -/
lemma nines_props (n : ℕ) :
    admissible (nines n) ∧ firstDigit (nines n) = 9 ∧ lastDigit (nines n) = 9 := by
  have hpos : 0 < nines n := by cases n <;> simp [nines]
  refine ⟨⟨hpos, ?_⟩, ?_, ?_⟩
  · rw [digits_nines, List.reverse_replicate]
    exact List.isChain_replicate_of_rel _ (by norm_num [digitStep] : digitStep 9 9)
  · rw [firstDigit, digits_nines, List.reverse_replicate, List.replicate_succ]
    rfl
  · simp [lastDigit, digits_nines, List.replicate_succ]

/-- The lengths of the digit lists distinguish the repeated-nine numbers. -/
lemma nines_injective : Function.Injective nines := by
  intro i j hij
  have h := congrArg (fun n => (Nat.digits 10 n).length) hij
  simpa [digits_nines] using h

/-- Repeated-nine numbers give infinitely many choices after any predecessor. -/
lemma available (used : Finset ℕ) (previous : ℕ) :
    {m : ℕ | admissible m ∧ m ∉ used ∧ follows previous m}.Nonempty := by
  obtain ⟨m, ⟨n, rfl⟩, hm⟩ :=
    (Set.infinite_range_of_injective nines_injective).exists_notMem_finset used
  obtain ⟨ha, hfirst, _⟩ := nines_props n
  exact ⟨nines n, ha, hm, by simp [follows, hfirst, digitStep]⟩

/-- The greedy term is an admissible, unused choice. -/
lemma chosen (n : ℕ) : admissible (a n) ∧ (a n) ∉ (state n).1 ∧
    follows (state n).2 (a n) :=
  csInf_mem (available (state n).1 (state n).2)

/-- A candidate in the current step bounds the chosen term from above. -/
lemma greedy_le (n m : ℕ) (hm : admissible m) (hu : m ∉ (state n).1)
    (hf : follows (state n).2 m) : a n ≤ m :=
  csInf_le (OrderBot.bddBelow _) (show m ∈ {k : ℕ | admissible k ∧
    k ∉ (state n).1 ∧ follows (state n).2 k} from ⟨hm, hu, hf⟩)

/-- The used set at a step consists exactly of the terms at earlier indices. -/
lemma used_iff (m n : ℕ) : m ∈ (state n).1 ↔ ∃ i < n, a i = m := by
  induction n with
  | zero => simp [state]
  | succ n ih =>
    change m ∈ insert (a n) (state n).1 ↔ ∃ i < n + 1, a i = m
    rw [Finset.mem_insert, ih]
    constructor
    · rintro (h | ⟨i, hi, rfl⟩)
      · exact ⟨n, by omega, h.symm⟩
      · exact ⟨i, by omega, rfl⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with hi | rfl
      · exact Or.inr ⟨i, hi, h⟩
      · exact Or.inl h.symm

/-- No later step selects an already used term. -/
lemma injective : Function.Injective a := by
  have unequal (i j : ℕ) (h : i < j) : a i ≠ a j := by
    intro he
    exact (chosen j).2.1 ((used_iff _ _).2 ⟨i, h, he⟩)
  intro i j h
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact False.elim (unequal i j hij h)
  · rfl
  · exact False.elim (unequal j i hji h.symm)

/-- Only finitely many indices can map into the finite interval ending at m. -/
lemma eventually_gt (m : ℕ) : ∃ N, ∀ i ≥ N, m < a i := by
  have hfin : (a ⁻¹' Set.Iic m).Finite :=
    (Set.finite_Iic m).preimage injective.injOn
  obtain ⟨b, hb⟩ := hfin.bddAbove
  refine ⟨b + 1, fun i hi => lt_of_not_ge fun hm => ?_⟩
  have hib : i ≤ b := hb (show i ∈ a ⁻¹' Set.Iic m from hm)
  omega

/-- A candidate that can follow any predecessor must eventually be selected. -/
lemma always_selected (m : ℕ) (hm : admissible m) (hf : ∀ p, follows p m) :
    ∃ i, a i = m := by
  by_contra h
  obtain ⟨N, hN⟩ := eventually_gt m
  have hu : m ∉ (state N).1 := fun hu =>
    h (let ⟨i, _, hi⟩ := (used_iff m N).mp hu; ⟨i, hi⟩)
  exact (not_le_of_gt (hN N le_rfl)) (greedy_le N m hm hu (hf _))

/-- The leading digit is bounded by nine, including the empty-list default. -/
lemma firstDigit_lt (m : ℕ) : firstDigit m < 10 := by
  unfold firstDigit
  generalize hd : (Nat.digits 10 m).reverse = ds
  cases ds with
  | nil => decide
  | cons d ds =>
    change d < 10
    exact Nat.digits_lt_base (by decide) (by
      have h : d ∈ (Nat.digits 10 m).reverse := by rw [hd]; simp
      simpa using h)

/-- A late step following a repeated-nine number forces any remaining small candidate. -/
lemma all_selected (m : ℕ) (hm : admissible m) : ∃ i, a i = m := by
  by_contra h
  obtain ⟨N, hN⟩ := eventually_gt m
  obtain ⟨q, ⟨k, rfl⟩, hk⟩ :=
    (Set.infinite_range_of_injective nines_injective).exists_notMem_finset (state N).1
  obtain ⟨ha, hf, hl⟩ := nines_props k
  obtain ⟨i, hi⟩ := always_selected (nines k) ha (fun p => by simp [follows, hf, digitStep])
  have hNi : N ≤ i := by
    by_contra hlt
    exact hk ((used_iff _ _).mpr ⟨i, by omega, hi⟩)
  have hu : m ∉ (state (i + 1)).1 := fun hu =>
    h (let ⟨j, _, hj⟩ := (used_iff m (i + 1)).mp hu; ⟨j, hj⟩)
  have hfollows : follows (state (i + 1)).2 m := by
    change digitStep (lastDigit (a i)) (firstDigit m)
    rw [hi, hl]
    intro he
    have hlt := firstDigit_lt m
    omega
  exact (not_le_of_gt (hN (i + 1) (by omega))) (greedy_le _ _ hm hu hfollows)

end OMA.A382624

theorem OMA.solution : type_of% @OMA.S_oeis_a382624.main := by
  refine ⟨OMA.A382624.injective, fun m => ⟨?_, OMA.A382624.all_selected m⟩⟩
  rintro ⟨i, rfl⟩
  exact (OMA.A382624.chosen i).1
