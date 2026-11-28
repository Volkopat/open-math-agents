import OMAStatements.S_oeis_a011558
import Mathlib

-- The weight is (one) + 2 (two) + 5 m, where m is the number whose binary digits are the exponents.
theorem oeis_a011558_weight (p : OMA.S_oeis_a011558.Selection) :
    OMA.S_oeis_a011558.weight 5 p =
      p.one.toNat + 2 * p.two.toNat + 5 * ∑ j ∈ p.exponents, 2 ^ j := by
  unfold OMA.S_oeis_a011558.weight
  rw [Finset.mul_sum]

-- A selection is determined by its weight: the residue modulo 5 fixes the two flags and
-- the quotient fixes the set of exponents (uniqueness of binary expansion).
theorem oeis_a011558_inj (p q : OMA.S_oeis_a011558.Selection)
    (h : OMA.S_oeis_a011558.weight 5 p = OMA.S_oeis_a011558.weight 5 q) : p = q := by
  rw [oeis_a011558_weight, oeis_a011558_weight] at h
  obtain ⟨o1, t1, e1⟩ := p
  obtain ⟨o2, t2, e2⟩ := q
  simp only at h
  have ho1 : o1.toNat ≤ 1 := Bool.toNat_le o1
  have ht1 : t1.toNat ≤ 1 := Bool.toNat_le t1
  have ho2 : o2.toNat ≤ 1 := Bool.toNat_le o2
  have ht2 : t2.toNat ≤ 1 := Bool.toNat_le t2
  have hM : (∑ j ∈ e1, 2 ^ j) = ∑ j ∈ e2, 2 ^ j := by omega
  have ho' : o1.toNat = o2.toNat := by omega
  have ht' : t1.toNat = t2.toNat := by omega
  have he : e1 = e2 := Finset.geomSum_injective (le_refl 2) hM
  have ho : o1 = o2 := by
    revert ho'
    cases o1 <;> cases o2 <;> simp
  have ht : t1 = t2 := by
    revert ht'
    cases t1 <;> cases t2 <;> simp
  rw [ho, ht, he]

-- A selection of weight n, when n is not 4 modulo 5.
theorem oeis_a011558_ex (n : ℕ) (h : n % 5 ≠ 4) :
    OMA.S_oeis_a011558.weight 5
      ⟨decide (n % 5 % 2 = 1), decide (2 ≤ n % 5), (n / 5).bitIndices.toFinset⟩ = n := by
  rw [oeis_a011558_weight]
  simp only
  rw [Finset.twoPowSum_toFinset_bitIndices]
  have hr : n % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have h1 : (decide (n % 5 % 2 = 1)).toNat + 2 * (decide (2 ≤ n % 5)).toNat = n % 5 := by
    have h4 : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 := by omega
    rcases h4 with h0 | h0 | h0 | h0 <;> rw [h0] <;> decide
  omega

-- No selection has weight 4 modulo 5.
theorem oeis_a011558_none (n : ℕ) (h : n % 5 = 4) (p : OMA.S_oeis_a011558.Selection) :
    OMA.S_oeis_a011558.weight 5 p ≠ n := by
  rw [oeis_a011558_weight]
  have ho := Bool.toNat_le p.one
  have ht := Bool.toNat_le p.two
  have h1 : p.one.toNat = 0 ∨ p.one.toNat = 1 := by omega
  have h2 : p.two.toNat = 0 ∨ p.two.toNat = 1 := by omega
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega

theorem OMA.solution : type_of% @OMA.S_oeis_a011558.main := by
  intro n
  unfold OMA.S_oeis_a011558.a
  by_cases h : n % 5 = 4
  · have hs : ({p : OMA.S_oeis_a011558.Selection | OMA.S_oeis_a011558.weight 5 p = n} :
        Set OMA.S_oeis_a011558.Selection) = ∅ := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact oeis_a011558_none n h p
    rw [hs, Set.ncard_empty, if_pos (by omega)]
  · have hs : ({p : OMA.S_oeis_a011558.Selection | OMA.S_oeis_a011558.weight 5 p = n} :
        Set OMA.S_oeis_a011558.Selection) =
        {⟨decide (n % 5 % 2 = 1), decide (2 ≤ n % 5), (n / 5).bitIndices.toFinset⟩} := by
      ext p
      simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
      constructor
      · intro hp
        exact oeis_a011558_inj _ _ (hp.trans (oeis_a011558_ex n h).symm)
      · intro hp
        rw [hp]
        exact oeis_a011558_ex n h
    rw [hs, Set.ncard_singleton, if_neg (by omega)]
