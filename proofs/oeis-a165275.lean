import OMAStatements.S_oeis_a165275

namespace OMA.A165275Proof

open OMA.S_oeis_a165275

private def minOdd : ℕ → ℕ
  | 0 => 0
  | r + 1 => 4 * minOdd r + 2

private lemma oddBitCount_eq_filter_of_le (m N : ℕ) (hN : Nat.log2 m < N) :
    oddBitCount m = ((Finset.range N).filter (fun j => j % 2 = 1 ∧ m.testBit j)).card := by
  unfold oddBitCount
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hj, h1, h2⟩; exact ⟨by omega, h1, h2⟩
  · rintro ⟨hj, h1, h2⟩
    refine ⟨?_, h1, h2⟩
    by_contra hge
    have hpow : m < 2 ^ j := by
      have hlt : m < 2 ^ (Nat.log2 m + 1) := Nat.lt_log2_self
      exact lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by decide) (by omega))
    rw [Nat.testBit_eq_false_of_lt hpow] at h2
    exact Bool.false_ne_true h2

private lemma testBit_add_two (m j : ℕ) : m.testBit (j + 2) = (m / 4).testBit j := by
  rw [Nat.testBit_succ, Nat.testBit_succ, Nat.div_div_eq_div_mul]

private lemma oddBitCount_step (m : ℕ) :
    oddBitCount m = oddBitCount (m / 4) + (if m.testBit 1 then 1 else 0) := by
  let N := max (Nat.log2 m + 1) (Nat.log2 (m / 4) + 1)
  have h1 : oddBitCount m = ((Finset.range (N + 2)).filter (fun j => j % 2 = 1 ∧ m.testBit j)).card :=
    oddBitCount_eq_filter_of_le m (N + 2) (by omega)
  have h2 : oddBitCount (m / 4) = ((Finset.range N).filter (fun j => j % 2 = 1 ∧ (m / 4).testBit j)).card :=
    oddBitCount_eq_filter_of_le (m / 4) N (by omega)
  rw [h1, h2]
  have hsplit : (Finset.range (N + 2)).filter (fun j => j % 2 = 1 ∧ m.testBit j) =
      (((Finset.range N).filter (fun j => j % 2 = 1 ∧ (m / 4).testBit j)).image (· + 2)) ∪
        (if m.testBit 1 then {1} else ∅) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
    constructor
    · rintro ⟨hj, hodd, hbit⟩
      by_cases hj1 : j = 1
      · subst hj1; right; simp [hbit]
      · left
        refine ⟨j - 2, ⟨by omega, by omega, ?_⟩, by omega⟩
        have hsub : j - 2 + 2 = j := by omega
        rw [← testBit_add_two, hsub]; exact hbit
    · rintro (⟨k, ⟨hk, hodd, hbit⟩, rfl⟩ | hright)
      · refine ⟨by omega, by omega, ?_⟩
        rw [testBit_add_two]; exact hbit
      · split_ifs at hright with hb
        · rw [Finset.mem_singleton] at hright; subst hright
          exact ⟨by omega, by decide, hb⟩
        · simp at hright
  rw [hsplit, Finset.card_union_of_disjoint, Finset.card_image_of_injective _ (fun _ _ h => by omega)]
  · split_ifs <;> simp
  · rw [Finset.disjoint_left]
    intro x hx
    simp only [Finset.mem_image] at hx
    rcases hx with ⟨k, _, rfl⟩
    split_ifs <;> simp

private lemma oddBitCount_minOdd (r : ℕ) : oddBitCount (minOdd r) = r := by
  induction r with
  | zero => decide
  | succ r ih =>
    rw [minOdd, oddBitCount_step]
    have hdiv : (4 * minOdd r + 2) / 4 = minOdd r := by omega
    have hbit : (4 * minOdd r + 2).testBit 1 = true := by
      rw [Nat.testBit_succ, show (4 * minOdd r + 2) / 2 = 2 * minOdd r + 1 by omega]
      simp [Nat.testBit_zero]
    rw [hdiv, hbit, ih]
    simp

private lemma minOdd_le_of_oddBitCount : ∀ m, minOdd (oddBitCount m) ≤ m := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [oddBitCount, minOdd]
    · rw [oddBitCount_step m]
      have hdiv_lt : m / 4 < m := Nat.div_lt_self hm (by decide)
      have hih := ih (m / 4) hdiv_lt
      by_cases hb : m.testBit 1 = true
      · rw [hb, if_pos rfl, minOdd]
        have hrem : 2 ≤ m % 4 := by
          rw [Nat.testBit_succ, Nat.testBit_zero] at hb
          have hmod : (m / 2) % 2 = 1 := by simpa using hb
          omega
        omega
      · simp only [hb, Bool.false_eq_true, ↓reduceIte, add_zero]
        omega

private lemma minOdd_pos (r : ℕ) (hr : 1 ≤ r) : 0 < minOdd r := by
  rcases r with _ | r
  · omega
  · simp [minOdd]

private lemma T_one_eq_minOdd (n : ℕ) (hn : 2 ≤ n) : T n 1 = minOdd (n - 1) := by
  unfold T
  simp only [Nat.sub_self, Nat.nth_zero]
  have hmem : 0 < minOdd (n - 1) ∧ oddBitCount (minOdd (n - 1)) = n - 1 :=
    ⟨minOdd_pos (n - 1) (by omega), oddBitCount_minOdd (n - 1)⟩
  apply le_antisymm
  · exact Nat.sInf_le hmem
  · exact le_csInf ⟨minOdd (n - 1), hmem⟩ fun m hm => by
      rw [← hm.2]
      exact minOdd_le_of_oddBitCount m

private lemma tri_lt_tri {x y : ℕ} (h : x < y) : tri x < tri y := by
  unfold tri
  have h1 : x * (x + 1) + 2 ≤ y * (y + 1) := by nlinarith
  omega

private lemma diagOf_tri (n : ℕ) (hn : 1 ≤ n) : diagOf (tri n) = n := by
  unfold diagOf
  apply le_antisymm
  · apply Finset.min'_le
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, le_rfl⟩
    unfold tri
    have h : 2 * n ≤ n * (n + 1) := by nlinarith
    omega
  · apply Finset.le_min'
    intro d hd
    simp only [Finset.mem_filter, Finset.mem_range] at hd
    by_contra hlt
    have := tri_lt_tri (show d < n by omega)
    omega

private lemma tri_sub_prev (n : ℕ) (hn : 1 ≤ n) : tri n - tri (n - 1) = n := by
  rcases n with _ | m
  · omega
  · unfold tri
    have h1 : (m + 1) * (m + 1 + 1) = m * (m + 1) + 2 * (m + 1) := by linarith
    simp only [Nat.add_sub_cancel]
    omega

private lemma a_tri (n : ℕ) (hn : 1 ≤ n) : a (tri n) = T n 1 := by
  unfold a
  have hpos : 1 ≤ tri n := by
    unfold tri
    have : 2 ≤ n * (n + 1) := by nlinarith
    omega
  rw [if_pos hpos, diagOf_tri n hn]
  dsimp only
  rw [tri_sub_prev n hn, Nat.add_sub_cancel_left]

end OMA.A165275Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a165275.main := by
  intro n hn
  rw [OMA.A165275Proof.a_tri n (by omega), OMA.A165275Proof.a_tri (n - 1) (by omega),
    OMA.A165275Proof.T_one_eq_minOdd n (by omega),
    OMA.A165275Proof.T_one_eq_minOdd (n - 1) (by omega)]
  have hsub : n - 1 = (n - 2) + 1 := by omega
  rw [hsub, Nat.add_sub_cancel, OMA.A165275Proof.minOdd]
