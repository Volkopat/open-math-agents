import OMAStatements.S_oeis_a076614

/-! Use monotonicity and congruences to restrict collisions of prime power sums. -/

namespace OMA.R_oeis_a076614_R1

open OMA.S_oeis_a076614

/-- With two even exponents, the lengths must agree modulo four. -/
def H1 : Prop :=
  ∀ k n l m : ℕ, 1 ≤ k → 1 ≤ m → k < l → m < n →
    Even k → Even l → n ≡ m [MOD 4] → S k n = S l m → S k n = 160

/-- With an odd exponent, the lengths must still have the same parity. -/
def H2 : Prop :=
  ∀ k n l m : ℕ, 1 ≤ k → 1 ≤ m → k < l → m < n →
    ¬ (Even k ∧ Even l) → n ≡ m [MOD 2] → S k n = S l m → S k n = 160

lemma sum_strict_length (k : ℕ) : StrictMono (S k) := by
  apply strictMono_nat_of_lt_succ
  intro n
  rw [S, S, Finset.sum_range_succ]
  exact Nat.lt_add_of_pos_right (Nat.pow_pos (Nat.prime_nth_prime n).pos)

lemma sum_strict_exponent {n : ℕ} (hn : 1 ≤ n) : StrictMono (fun k => S k n) := by
  intro k l hkl
  change S k n < S l n
  unfold S
  apply Finset.sum_lt_sum
  · intro i _
    exact Nat.pow_le_pow_right (Nat.prime_nth_prime i).pos hkl.le
  · exact ⟨0, Finset.mem_range.mpr hn, Nat.pow_lt_pow_right (Nat.prime_nth_prime 0).one_lt hkl⟩

lemma odd_nth_prime {i : ℕ} (hi : 0 < i) : Nat.nth Nat.Prime i % 2 = 1 := by
  have hp := Nat.add_two_le_nth_prime i
  exact (Nat.prime_nth_prime i).eq_two_or_odd.resolve_left (by omega)

lemma sum_mod_of_terms {d k : ℕ}
    (h0 : (Nat.nth Nat.Prime 0) ^ k ≡ 0 [MOD d])
    (h1 : ∀ i : ℕ, 0 < i → (Nat.nth Nat.Prime i) ^ k ≡ 1 [MOD d]) (n : ℕ) :
    S k (n + 1) ≡ n [MOD d] := by
  induction n with
  | zero => simpa [S] using h0
  | succ n ih =>
    rw [S, Finset.sum_range_succ]
    exact ih.add (h1 (n + 1) (by omega))

lemma sum_mod_two {k n : ℕ} (hk : 1 ≤ k) : S k (n + 1) ≡ n [MOD 2] := by
  apply sum_mod_of_terms
  · rw [Nat.nth_prime_zero_eq_two, Nat.modEq_zero_iff_dvd]
    simpa using Nat.pow_dvd_pow 2 hk
  · intro i hi
    have hp : Nat.nth Nat.Prime i ≡ 1 [MOD 2] := odd_nth_prime hi
    simpa only [one_pow] using hp.pow k

lemma sum_mod_four {k n : ℕ} (hk : 1 ≤ k) (he : Even k) : S k (n + 1) ≡ n [MOD 4] := by
  obtain ⟨j, hj⟩ := he
  have hkj : k = 2 * j := by omega
  apply sum_mod_of_terms
  · rw [Nat.nth_prime_zero_eq_two, Nat.modEq_zero_iff_dvd]
    change 2 ^ 2 ∣ 2 ^ k
    exact Nat.pow_dvd_pow 2 (by omega)
  · intro i hi
    have hp := odd_nth_prime hi
    have hr : Nat.nth Nat.Prime i % 4 = 1 ∨ Nat.nth Nat.Prime i % 4 = 3 := by omega
    have hs : (Nat.nth Nat.Prime i) ^ 2 ≡ 1 [MOD 4] := by
      rcases hr with h | h <;> norm_num [Nat.ModEq, Nat.pow_mod, h]
    rw [hkj, pow_mul]
    simpa only [one_pow] using hs.pow j

lemma ordered_collision (hEven : H1) (hOther : H2) {k n l m : ℕ}
    (hk : 1 ≤ k) (hn : 1 ≤ n) (hm : 1 ≤ m) (hkl : k < l)
    (hEq : S k n = S l m) : S k n = 160 := by
  have hmn : m < n := by
    by_contra! hnm
    exact (ne_of_lt (((sum_strict_length k).monotone hnm).trans_lt
      (sum_strict_exponent hm hkl))) hEq
  have hl : 1 ≤ l := by omega
  obtain ⟨a, rfl⟩ : ∃ a : ℕ, n = a + 1 := ⟨n - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b : ℕ, m = b + 1 := ⟨m - 1, by omega⟩
  by_cases h : Even k ∧ Even l
  · have hA : S k (a + 1) ≡ a [MOD 4] := sum_mod_four hk h.1
    have hB : S l (b + 1) ≡ b [MOD 4] := sum_mod_four hl h.2
    rw [hEq] at hA
    exact hEven _ _ _ _ hk hm hkl hmn h.1 h.2 ((hA.symm.trans hB).add_right 1) hEq
  · have hA : S k (a + 1) ≡ a [MOD 2] := sum_mod_two hk
    have hB : S l (b + 1) ≡ b [MOD 2] := sum_mod_two hl
    rw [hEq] at hA
    exact hOther _ _ _ _ hk hm hkl hmn h ((hA.symm.trans hB).add_right 1) hEq

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a076614.main := by
  intro hEven hOther k n l m hk hn hl hm hDistinct hEq
  rcases lt_trichotomy k l with h | rfl | h
  · exact ordered_collision hEven hOther hk hn hm h hEq
  · have hnm := (sum_strict_length k).injective hEq
    subst m
    exact (hDistinct rfl).elim
  · exact hEq.trans (ordered_collision hEven hOther hl hm hn h hEq.symm)

end OMA.R_oeis_a076614_R1
