import OMAStatements.S_oeis_a383062
import Mathlib.Tactic

open OMA.S_oeis_a383062

namespace GreedyDigits

private def Bridge (b : ℕ) : Prop :=
  admissible b ∧ (∀ m, follows m b) ∧ ∀ m, admissible m → follows b m

private lemma bridges (t : ℕ) : ∃ b, t < b ∧ Bridge b := by
  let ds := List.replicate (t+1) 0 ++ [2]
  let b := Nat.ofDigits 10 ds
  have grows (k : ℕ) : k+1 ≤ Nat.ofDigits 10 (List.replicate k 0 ++ [2]) := by
    induction k with
    | zero => decide
    | succ k ih =>
      rw [List.replicate_succ, List.cons_append, Nat.ofDigits_cons]
      omega
  have hb : t < b := by
    have h := grows (t+1)
    change t < Nat.ofDigits 10 (List.replicate (t+1) 0 ++ [2])
    omega
  have hd : Nat.digits 10 b = ds :=
    Nat.digits_ofDigits 10 (by decide) _ (by
      intro x hx
      simp [ds] at hx
      omega) (by intro h; simp [ds])
  have revDigits : ds.reverse = 2 :: List.replicate (t+1) 0 := by simp [ds]
  have hfirst : firstDigit b = 2 := by rw [firstDigit, hd, revDigits]; rfl
  have hlast : lastDigit b = 0 := by
    rw [lastDigit, hd]; simp [ds, List.replicate_succ]
  refine ⟨b, hb, ?_, ?_, ?_⟩
  · rw [admissible, hd, revDigits, List.replicate_succ, List.isChain_cons_cons]
    refine ⟨by simp [digitStep], ?_⟩
    simpa only [← List.replicate_succ] using
      List.isChain_replicate_of_rel (t+1) (by simp [digitStep] : digitStep 0 0)
  · intro m
    simp [follows, hfirst, digitStep]
  · intro m _
    simp only [follows, hlast, digitStep]
    omega

private lemma state_step (n : ℕ) : state (n+1) = (insert (a n) (state n).1, a n) := rfl

private lemma used (n : ℕ) : (state n).1 = (Finset.range n).image a := by
  induction n with
  | zero => simp [state]
  | succ n ih => simp [state_step, Finset.range_add_one, ih]

private lemma chosen (n : ℕ) :
    admissible (a n) ∧ a n ∉ (state n).1 ∧ follows (state n).2 (a n) := by
  obtain ⟨b, hb, hadm, hin, _⟩ := bridges ((state n).1.sup id)
  have hu : b ∉ (state n).1 := fun H => (not_lt_of_ge (Finset.le_sup (f:=id) H)) hb
  change sInf {m : ℕ | admissible m ∧ m ∉ (state n).1 ∧ follows (state n).2 m} ∈
    {m : ℕ | admissible m ∧ m ∉ (state n).1 ∧ follows (state n).2 m}
  apply Nat.sInf_mem
  exact ⟨b, hadm, hu, hin _⟩

private lemma least (n m : ℕ) (hm : admissible m) (hu : m ∉ (state n).1)
    (hf : follows (state n).2 m) : a n ≤ m := Nat.sInf_le ⟨hm, hu, hf⟩

private lemma injective : Function.Injective a := by
  have distinct {i j : ℕ} (hij : i < j) : a i ≠ a j := by
    intro eq
    have hi : a j ∈ (state j).1 := by
      rw [used]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hij, eq⟩
    exact (chosen j).2.1 hi
  intro i j eq
  rcases lt_trichotomy i j with h | h | h
  · exact (distinct h eq).elim
  · exact h
  · exact (distinct h eq.symm).elim

private lemma stays_unused (m : ℕ) (hm : ¬ ∃ n, a n=m) (n : ℕ) : m ∉ (state n).1 := by
  rw [used]
  rintro h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  exact hm ⟨i, hi⟩

-- Any number allowed after every possible boundary digit must eventually be
-- selected. Until that happens every greedy choice is at most that number.
private lemma bridge_occurs (b : ℕ) (hb : Bridge b) : ∃ n, a n=b := by
  by_contra h
  have bound (n : ℕ) := least n b hb.1 (stays_unused b h n) (hb.2.1 _)
  exact (Set.infinite_range_of_injective injective)
    ((Set.finite_le_nat b).subset (Set.range_subset_iff.mpr bound))

-- A bridge selected after the last small term makes the target eligible next.
private lemma covers {m : ℕ} (hm : admissible m) : ∃ n, a n=m := by
  by_contra h
  have finite : (a ⁻¹' Set.Iic m).Finite := (Set.finite_Iic m).preimage injective.injOn
  obtain ⟨N, hN⟩ := finite.bddAbove
  obtain ⟨b, hb, hbridge⟩ := bridges ((state (N+1)).1.sup id)
  obtain ⟨j, hj⟩ := bridge_occurs b hbridge
  have hlarge : N < j := by
    by_contra! hjN
    have hmem : b ∈ (state (N+1)).1 := by
      rw [used]
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), hj⟩
    exact (not_lt_of_ge (Finset.le_sup (f:=id) hmem)) hb
  have hf : follows (state (j+1)).2 m := by
    rw [state_step]
    simpa only [hj] using hbridge.2.2 m hm
  have small := least (j+1) m hm (stays_unused m h _) hf
  have := hN (show j+1 ∈ a ⁻¹' Set.Iic m from small)
  omega

end GreedyDigits

theorem OMA.solution : type_of% @OMA.S_oeis_a383062.main := by
  refine ⟨GreedyDigits.injective, fun m => ⟨?_, GreedyDigits.covers⟩⟩
  rintro ⟨n, rfl⟩
  exact (GreedyDigits.chosen n).1
