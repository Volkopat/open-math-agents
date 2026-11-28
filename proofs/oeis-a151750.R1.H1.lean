import OMAReductions.R_oeis_a151750_R1

/-! By Kummer's theorem in the form `padicValNat_choose'`, the p-adic valuation of C(2n, n) counts
the i ≥ 1 with p^i ≤ 2 (n mod p^i). By induction on the base-p digits (n mod p^(j+1) =
n mod p + p · ((n / p) mod p^j)), the condition 2 (n mod p^i) < p^i for all i ≥ 1 is equivalent to
2 d < p for every digit d of n. -/

namespace OMA.A151750

theorem digits_iff (p : ℕ) (hp : 2 ≤ p) : ∀ n : ℕ,
    (∀ d ∈ Nat.digits p n, 2 * d < p) ↔ ∀ i, 1 ≤ i → 2 * (n % p ^ i) < p ^ i := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [Nat.digits_zero, List.not_mem_nil, false_imp_iff, imp_true_iff, true_iff,
        Nat.zero_mod, mul_zero]
      intro i _
      positivity
    · rw [Nat.digits_def' (by omega) hn]
      simp only [List.mem_cons, forall_eq_or_imp]
      rw [ih (n / p) (Nat.div_lt_self hn (by omega))]
      constructor
      · rintro ⟨h0, h1⟩ i hi
        obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
        rw [pow_succ', Nat.mod_mul]
        rcases Nat.eq_zero_or_pos j with rfl | hj
        · simp only [pow_zero, Nat.mod_one, mul_zero, add_zero, mul_one]
          exact h0
        · have h2 := h1 j hj
          have h3 : p * (2 * (n / p % p ^ j) + 1) ≤ p * p ^ j := Nat.mul_le_mul_left p h2
          nlinarith
      · intro h
        refine ⟨?_, fun j hj => ?_⟩
        · have h1 := h 1 le_rfl
          simpa using h1
        · have h1 := h (j + 1) (by omega)
          rw [pow_succ', Nat.mod_mul] at h1
          by_contra hc
          push Not at hc
          have h3 : p * p ^ j ≤ p * (2 * (n / p % p ^ j)) := Nat.mul_le_mul_left p hc
          have h4 : p * (2 * (n / p % p ^ j)) = 2 * (p * (n / p % p ^ j)) := by ring
          have h5 : 0 ≤ n % p := Nat.zero_le _
          omega

end OMA.A151750

theorem OMA.solution : OMA.R_oeis_a151750_R1.H1 := by
  intro p n hp
  have := Fact.mk hp
  have hp2 := hp.two_le
  rw [OMA.A151750.digits_iff p hp2 n, show 2 * n = n + n by ring]
  have hv := padicValNat_choose' (p := p) (n := n) (k := n) (Nat.lt_succ_self (Nat.log p (n + n)))
  have hne : Nat.choose (n + n) n ≠ 0 := Nat.choose_ne_zero (by omega)
  constructor
  · intro hnd i hi
    by_contra hc
    push Not at hc
    have hmod : n % p ^ i ≤ n := Nat.mod_le _ _
    have hi' : i < Nat.log p (n + n) + 1 :=
      Nat.lt_succ_of_le (Nat.le_log_of_pow_le (by omega) (by omega))
    have hpos : 0 < padicValNat p (Nat.choose (n + n) n) := by
      rw [hv]
      apply Finset.card_pos.2
      exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨hi, hi'⟩, by omega⟩⟩
    exact hnd (dvd_of_one_le_padicValNat hpos)
  · intro h hdvd
    have hv0 : padicValNat p (Nat.choose (n + n) n) = 0 := by
      rw [hv, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i hi
      have := h i (Finset.mem_Ico.1 hi).1
      omega
    have := one_le_padicValNat_of_dvd hne hdvd
    omega
