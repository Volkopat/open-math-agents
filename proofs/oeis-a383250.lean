import OMAStatements.S_oeis_a383250

/-!
# Repdigits 22...2 connect every two terms

Adapted from the accepted proof of the sibling entry A383246. A repdigit of twos starts with
2, so it may follow every term whose last digit is not 1. It ends with 2, so it can precede
every number. Fresh repdigits keep the recursion defined, and omitting one forever would
bound the injective sequence. A repdigit chosen sufficiently late then forces any omitted
admissible value to bound a later choice, contradicting finiteness of the smaller choices.
-/

namespace OMA.A383250

open OMA.S_oeis_a383250

/-- A repdigit of twos of length k + 1. -/
private def conn (k : ℕ) : ℕ := Nat.ofDigits 10 (List.replicate (k + 1) 2)

private lemma conn_digits (k : ℕ) :
    Nat.digits 10 (conn k) = List.replicate (k + 1) 2 := by
  apply Nat.digits_ofDigits 10 (by decide)
  · intro x hx
    have hx' : x = 2 := (List.mem_replicate.mp hx).2
    omega
  · intro h
    simp

private lemma infinite_conn : (Set.range conn).Infinite := by
  apply Set.infinite_range_of_injective
  intro i j hij
  have h := congrArg (fun x => (Nat.digits 10 x).length) hij
  simp only [conn_digits, List.length_replicate] at h
  omega

private lemma lastDigit_eq (n : ℕ) : lastDigit n = n % 10 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rfl
  · rw [lastDigit, Nat.digits_def' (by norm_num) hn, List.headD_cons]

private lemma conn_pos (k : ℕ) : 0 < conn k := by
  apply Nat.pos_of_ne_zero
  apply (Nat.digits_ne_nil_iff_ne_zero (b := 10)).mp
  rw [conn_digits, List.replicate_succ]
  simp

private lemma conn_admissible (k : ℕ) : admissible (conn k) := by
  refine ⟨?_, ?_⟩
  · rw [← lastDigit_eq, lastDigit, conn_digits, List.replicate_succ, List.headD_cons]
    norm_num
  · rw [conn_digits, List.reverse_replicate]
    exact List.isChain_replicate_of_rel _ (by norm_num [digitStep] : digitStep 2 2)

private lemma before_conn (previous k : ℕ) (hp : lastDigit previous ≠ 1) :
    follows previous (conn k) := by
  rw [follows, firstDigit, conn_digits, List.reverse_replicate,
    List.replicate_succ, List.headD_cons]
  unfold digitStep
  omega

private lemma after_conn (k m : ℕ) : follows (conn k) m := by
  simp only [follows, lastDigit, conn_digits, List.replicate_succ, List.headD_cons, digitStep]
  norm_num

private lemma state_step (n : ℕ) :
    state (n + 1) = (insert (a (n + 1)) (state n).1, a (n + 1)) := rfl

private lemma a_succ (n : ℕ) : a (n + 1) = next (state n).1 (a n) := rfl

private lemma next_spec (used : Finset ℕ) (previous : ℕ) (hp : lastDigit previous ≠ 1) :
    0 < next used previous ∧ admissible (next used previous) ∧ next used previous ∉ used ∧
      follows previous (next used previous) := by
  obtain ⟨_, ⟨k, rfl⟩, hfresh⟩ := infinite_conn.exists_notMem_finset used
  exact Nat.sInf_mem (s := {v | 0 < v ∧ admissible v ∧ v ∉ used ∧ follows previous v})
    ⟨conn k, conn_pos k, conn_admissible k, hfresh, before_conn _ k hp⟩

private lemma a_zero : a 0 = 0 := rfl

private lemma admissible_zero : admissible 0 := by
  refine ⟨by norm_num, ?_⟩
  simp

private lemma a_admissible (n : ℕ) : admissible (a n) ∧ lastDigit (a n) ≠ 1 := by
  induction n with
  | zero => exact ⟨admissible_zero, by decide⟩
  | succ n ih =>
    rw [a_succ]
    have h := (next_spec (state n).1 (a n) ih.2).2.1
    exact ⟨h, by rw [lastDigit_eq]; exact h.1⟩

private lemma step_spec (n : ℕ) :
    a (n + 1) ∉ (state n).1 ∧ follows (a n) (a (n + 1)) := by
  have h := next_spec (state n).1 (a n) (a_admissible n).2
  exact ⟨h.2.2.1, h.2.2.2⟩

private lemma step_le (n m : ℕ) (hm0 : 0 < m) (hm : admissible m) (hfresh : m ∉ (state n).1)
    (hfollow : follows (a n) m) : a (n + 1) ≤ m := by
  exact Nat.sInf_le (s := {v | 0 < v ∧ admissible v ∧ v ∉ (state n).1 ∧ follows (a n) v})
    ⟨hm0, hm, hfresh, hfollow⟩

private lemma used_mono : Monotone (fun n => (state n).1) := by
  apply monotone_nat_of_le_succ
  intro n m hm
  rw [state_step]
  exact Finset.mem_insert_of_mem hm

private lemma used_self (n : ℕ) : a n ∈ (state n).1 := by
  cases n with
  | zero => simp [a, state]
  | succ n => rw [state_step]; exact Finset.mem_insert_self _ _

private lemma used_occurs {m : ℕ} (n : ℕ) (hm : m ∈ (state n).1) : ∃ i, a i = m := by
  induction n with
  | zero =>
    simp only [state, Finset.mem_singleton] at hm
    exact ⟨0, hm.symm⟩
  | succ n ih =>
    rw [state_step, Finset.mem_insert] at hm
    rcases hm with h | h
    · exact ⟨n + 1, h.symm⟩
    · exact ih h

private lemma injective_a : Function.Injective a := by
  have distinct (i j : ℕ) (hij : i < j) : a i ≠ a j := by
    intro h
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact (step_spec j').1 (h ▸ used_mono (by omega : i ≤ j') (used_self i))
  intro i j h
  rcases lt_trichotomy i j with hij | hij | hij
  · exact False.elim (distinct i j hij h)
  · exact hij
  · exact False.elim (distinct j i hij h.symm)

private lemma conn_occurs (k : ℕ) : ∃ i, a i = conn k := by
  by_contra h
  have hbound : Set.range a ⊆ Set.Iic (conn k) := by
    rintro _ ⟨n, rfl⟩
    cases n with
    | zero => rw [a_zero]; exact Nat.zero_le _
    | succ n =>
      exact step_le n _ (conn_pos k) (conn_admissible k) (fun hf => h (used_occurs n hf))
        (before_conn _ k (a_admissible n).2)
  exact (Set.infinite_range_of_injective injective_a) ((Set.finite_Iic _).subset hbound)

private lemma admissible_occurs (m : ℕ) (hm : admissible m) : ∃ i, a i = m := by
  by_contra h
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · exact absurd ⟨0, a_zero⟩ h
    · exact hpos
  have hfinite : {i | a i ≤ m}.Finite :=
    (Set.finite_Iic m).preimage injective_a.injOn
  obtain ⟨N, hN⟩ := hfinite.bddAbove
  obtain ⟨_, ⟨k, rfl⟩, hfresh⟩ := infinite_conn.exists_notMem_finset (state N).1
  obtain ⟨i, hi⟩ := conn_occurs k
  have hiN : N < i := by
    by_contra! hle
    apply hfresh
    rw [← hi]
    exact used_mono hle (used_self i)
  have hle : a (i + 1) ≤ m :=
    step_le i m hm0 hm (fun hf => h (used_occurs i hf)) (hi ▸ after_conn k m)
  have hindex : i + 1 ≤ N := hN hle
  omega

end OMA.A383250

theorem OMA.solution : type_of% @OMA.S_oeis_a383250.main := by
  refine ⟨A383250.injective_a, fun m => ⟨?_, A383250.admissible_occurs m⟩⟩
  rintro ⟨n, rfl⟩
  exact (A383250.a_admissible n).1
