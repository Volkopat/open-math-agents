import OMAStatements.S_oeis_a292510

namespace OMA.S_oeis_a292510




/-- The split of the entry's formula line works for every n. -/
lemma splits_seven (n : ℕ) : Splits n 7 := by
  refine ⟨{1, 2, 4, 7}, by decide, ?_⟩
  rw [show Finset.Icc 1 7 \ {1, 2, 4, 7} = ({3, 5, 6} : Finset ℕ) from by decide]
  simp [p, Nat.choose]
  ring

/-- The decidable criterion that excludes an integer root t >= 4 of t * c + d = 0. -/
def Crit (c d : ℤ) : Prop :=
  (c = 0 ∧ d ≠ 0) ∨ (c ≠ 0 ∧ (0 ≤ c * d ∨ |d| < 4 * |c| ∨ d % c ≠ 0))

instance (c d : ℤ) : Decidable (Crit c d) := by unfold Crit; infer_instance

lemma crit_works (c d t : ℤ) (ht : 4 ≤ t) (h : Crit c d) : t * c + d ≠ 0 := by
  intro h0
  have hd : d = -(t * c) := by linarith
  rcases h with ⟨hc, hd0⟩ | ⟨hc, h1 | h1 | h1⟩
  · subst hc; simp at hd; exact hd0 hd
  · rw [hd] at h1
    have : 0 < c * c := mul_self_pos.mpr hc
    nlinarith
  · rw [hd, abs_neg, abs_mul, abs_of_pos (by linarith : (0 : ℤ) < t)] at h1
    have : 0 ≤ |c| := abs_nonneg c
    nlinarith
  · apply h1
    rw [hd]
    simp

/-- Differences of the two sums over a split of {1..k}. -/
def dC (k : ℕ) (A : Finset ℕ) : ℤ :=
  ∑ m ∈ A, (Nat.choose m 2 : ℤ) - ∑ m ∈ Finset.Icc 1 k \ A, (Nat.choose m 2 : ℤ)

def dM (k : ℕ) (A : Finset ℕ) : ℤ :=
  ∑ m ∈ A, (m : ℤ) - ∑ m ∈ Finset.Icc 1 k \ A, (m : ℤ)

/-- The finite check over all splits of {1..k}, k <= 6. -/
lemma crit_all : ∀ k ∈ Finset.Icc 1 6, ∀ A ∈ (Finset.Icc 1 k).powerset, Crit (dC k A) (dM k A) := by
  decide

lemma sum_p_int (n : ℕ) (hn : 2 ≤ n) (B : Finset ℕ) :
    ((∑ m ∈ B, p n m : ℕ) : ℤ) =
      ((n : ℤ) - 2) * ∑ m ∈ B, (Nat.choose m 2 : ℤ) + ∑ m ∈ B, (m : ℤ) := by
  push_cast [p, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Nat.cast_sub hn]
  push_cast
  ring

lemma not_splits (n k : ℕ) (hn : 5 < n) (hk1 : 1 ≤ k) (hk : k ≤ 6) : ¬ Splits n k := by
  rintro ⟨A, hA, hsum⟩
  have hc := crit_all k (Finset.mem_Icc.mpr ⟨hk1, hk⟩) A (Finset.mem_powerset.mpr hA)
  apply crit_works (dC k A) (dM k A) ((n : ℤ) - 2) (by omega) hc
  have h := congrArg (fun x : ℕ => (x : ℤ)) hsum
  rw [sum_p_int n (by omega), sum_p_int n (by omega)] at h
  unfold dC dM
  linarith

/-- The conjecture: a(n) = 7 for every n > 5. -/
theorem conjecture (n : ℕ) (hn : 5 < n) : a n = 7 := by
  have h7 : 7 ∈ {k : ℕ | 1 ≤ k ∧ Splits n k} := ⟨by norm_num, splits_seven n⟩
  apply le_antisymm (Nat.sInf_le h7)
  apply le_csInf ⟨7, h7⟩
  rintro k ⟨hk1, hk⟩
  by_contra hlt
  exact not_splits n k hn hk1 (by omega) hk

end OMA.S_oeis_a292510

theorem OMA.solution : type_of% @OMA.S_oeis_a292510.main :=
  fun n hn => OMA.S_oeis_a292510.conjecture n hn
