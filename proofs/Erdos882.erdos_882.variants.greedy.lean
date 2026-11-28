import FormalConjectures.ErdosProblems.«882»

/-!
Shorter proof of `Erdos882.erdos_882.variants.greedy` via Sándor's subset-sum antichain
`{2^i + k * 2^k : i < k}` and binary-parity recursion for popcount subadditivity.
-/

open Finset Nat

@[simp] private def pc (n : ℕ) := n.bitIndices.length

private lemma pc_add (x y : ℕ) : pc (x + y) ≤ pc x + pc y := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · obtain ⟨a, rfl | rfl⟩ := even_or_odd' x <;>
    obtain ⟨b, rfl | rfl⟩ := even_or_odd' y <;>
    have := pc_add a b
    · rw [← mul_add]; simp at *; omega
    · rw [← add_assoc, ← mul_add]; simp at *; omega
    · rw [add_right_comm, ← mul_add]; simp at *; omega
    · have := pc_add (a + b) 1
      rw [show 2 * a + 1 + (2 * b + 1) = 2 * (a + b + 1) by omega]; simp at *; omega
termination_by x + y

private lemma pc_lt (q : ℕ) (hq : 2 ≤ q) : pc q < q := by
  by_cases h4 : q < 4
  · interval_cases q <;> decide
  · obtain ⟨m, rfl | rfl⟩ := even_or_odd' q <;>
      have := pc_lt m (by omega) <;> simp at * <;> omega

private lemma pc_mul (q : ℕ) (s : Finset ℕ) : pc (q * ∑ i ∈ s, 2 ^ i) ≤ pc q * #s := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, mul_add, mul_comm q (2 ^ a), card_insert_of_notMem ha, mul_add_one]
    have := pc_add (2 ^ a * q) (q * ∑ i ∈ s, 2 ^ i)
    simp at *; omega

theorem OMA.solution : type_of% @Erdos882.erdos_882.variants.greedy :=
  Filter.eventually_atTop.mpr ⟨81, fun n hn => by
    set k := log 3 n
    have hk4 : 4 ≤ k := le_log_of_pow_le (by norm_num) (by omega)
    have hpow (m : ℕ) (hm : 4 ≤ m) : (m + 1) * 2 ^ m ≤ 3 ^ m :=
      le_induction (by decide) (fun m _ ih => by rw [pow_succ, pow_succ]; nlinarith [Nat.two_pow_pos m]) m hm
    set T := k * 2 ^ k
    let f : ℕ → ℕ := (2 ^ · + T)
    have hf : Function.Injective f := fun _ _ h => Nat.pow_right_injective le_rfl (by simpa [f] using h)
    have hlog : Real.logb 3 n < k + 1 := by
      rw [Real.logb_lt_iff_lt_rpow (by norm_num) (cast_pos.mpr (by omega)),
        ← cast_add_one, Real.rpow_natCast]
      exact_mod_cast lt_pow_succ_log_self (by norm_num) n
    have hle : (k : ℝ) ≤ Erdos882.maxAntichainCard n := by
      refine cast_le.mpr <|
        le_csSup ⟨n, by rintro _ ⟨B, hB, -, rfl⟩; simpa using card_le_card hB⟩
          ⟨(range k).image f, ?_, ?_, by rw [card_image_of_injective _ hf, card_range]⟩
      · refine image_subset_iff.mpr fun i hi => mem_Icc.mpr ⟨le_add_right_of_le Nat.one_le_two_pow, ?_⟩
        dsimp [f, T]
        nlinarith [Nat.pow_le_pow_right (by omega : 0 < 2) (mem_range.mp hi).le,
          pow_log_le_self 3 (by omega : n ≠ 0), hpow k hk4]
      · intro S1 hS1 S2 hS2 hn1 hn2 hne
        obtain ⟨I1, hI1, rfl⟩ := subset_image_iff.mp hS1
        obtain ⟨I2, hI2, rfl⟩ := subset_image_iff.mp hS2
        simp only [sum_image hf.injOn, f, sum_add_distrib, sum_const, smul_eq_mul]
        set E1 := ∑ i ∈ I1, 2 ^ i
        set E2 := ∑ i ∈ I2, 2 ^ i
        have hsum : ∑ i ∈ range k, 2 ^ i < 2 ^ k := by
          rw [geomSum_eq le_rfl k]; have := Nat.two_pow_pos k; omega
        have : E1 < 2 ^ k := (sum_le_sum_of_subset hI1).trans_lt hsum
        have : E2 < 2 ^ k := (sum_le_sum_of_subset hI2).trans_lt hsum
        have hj1 : 0 < #I1 := card_pos.mpr (image_nonempty.mp hn1)
        have : 0 < #I2 := card_pos.mpr (image_nonempty.mp hn2)
        have : #I2 ≤ k := by simpa using card_le_card hI2
        rintro ⟨q, hq⟩
        set m := q * #I1
        have hq' : E2 + #I2 * T = q * E1 + m * T := by rw [hq]; dsimp [m]; ring
        have hqe : m = #I2 := by
          rcases lt_trichotomy m #I2 with h | h | h
          · have : q ≤ k := (Nat.le_mul_of_pos_right q hj1).trans (by omega)
            have : q * E1 < T := by dsimp [T]; nlinarith
            nlinarith
          · exact h
          · nlinarith [show 2 ^ k ≤ T by dsimp [T]; nlinarith]
        have hE : E2 = q * E1 := by rw [hqe] at hq'; omega
        by_cases hq2 : 2 ≤ q
        · have : pc (q * E1) = #I2 := by
            rw [← hE, pc, ← List.toFinset_card_of_nodup bitIndices_nodup,
              toFinset_bitIndices_sum_two_pow]
          have : pc (q * E1) ≤ pc q * #I1 := pc_mul q I1
          dsimp [m] at hqe; nlinarith [pc_lt q hq2]
        · have hq1 : q = 1 := by dsimp [m] at hqe; nlinarith
          apply hne; congr 1
          simpa [E1, E2, hq1] using congr_arg (·.bitIndices.toFinset) hE.symm
    linarith⟩
