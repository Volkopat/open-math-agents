import OMAStatements.S_oeis_a277273

namespace OMA.P_oeis_a277273

lemma sigma_prime {q : ℕ} (hq : q.Prime) : ArithmeticFunction.sigma 1 q = q + 1 := by
  rw [ArithmeticFunction.sigma_one_apply, Nat.Prime.sum_divisors hq]

lemma sigma_mul_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hne : q ≠ r) :
    ArithmeticFunction.sigma 1 (q * r) = (q + 1) * (r + 1) := by
  rw [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime
    ((Nat.coprime_primes hq hr).mpr hne), sigma_prime hq, sigma_prime hr]

lemma card_mul_primes {q r : ℕ} (hq : q.Prime) (hr : r.Prime) (hne : q ≠ r) :
    (q * r).divisors.card = 4 := by
  rw [Nat.Coprime.card_divisors_mul ((Nat.coprime_primes hq hr).mpr hne),
    Nat.Prime.divisors hq, Nat.Prime.divisors hr]
  rw [Finset.card_pair hq.one_lt.ne, Finset.card_pair hr.one_lt.ne]

/-- `k = (p+2)(3p+2)` has `d(k) = 4`, `k - 4 = p(3p+8)`, and both sigmas equal `3(p+1)(p+3)`. -/
lemma good_mem (p : ℕ) (h : OMA.S_oeis_a277273.Good p) :
    OMA.S_oeis_a277273.InSeq ((p + 2) * (3 * p + 2)) := by
  obtain ⟨hp, hp2, hp3, hp4⟩ := h
  have hp0 := hp.pos
  refine ⟨by positivity, ?_⟩
  rw [card_mul_primes hp2 hp3 (by omega)]
  have : (p + 2) * (3 * p + 2) - 4 = p * (3 * p + 8) := by
    have : (p + 2) * (3 * p + 2) = p * (3 * p + 8) + 4 := by ring
    omega
  rw [this, sigma_mul_primes hp2 hp3 (by omega), sigma_mul_primes hp hp4 (by omega)]
  ring

end OMA.P_oeis_a277273

theorem OMA.solution : type_of% @OMA.S_oeis_a277273.main := by
  refine ⟨OMA.P_oeis_a277273.good_mem, ?_⟩
  have key : ∀ p : ℕ, OMA.S_oeis_a277273.Good p → ∀ k, k = (p + 2) * (3 * p + 2) →
      OMA.S_oeis_a277273.InSeq k ∧ ∃ p : ℕ, OMA.S_oeis_a277273.Good p ∧ k = (p + 2) * (3 * p + 2) :=
    fun p hp k hk => ⟨hk ▸ OMA.P_oeis_a277273.good_mem p hp, p, hp, hk⟩
  intro k hk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact key 3 (by unfold OMA.S_oeis_a277273.Good; norm_num) _ (by norm_num)
  · exact key 5 (by unfold OMA.S_oeis_a277273.Good; norm_num) _ (by norm_num)
  · exact key 17 (by unfold OMA.S_oeis_a277273.Good; norm_num) _ (by norm_num)
  · exact key 197 (by unfold OMA.S_oeis_a277273.Good; norm_num) _ (by norm_num)
  · exact key 1427 (by unfold OMA.S_oeis_a277273.Good; norm_num) _ (by norm_num)
  · exact key 1667 (by unfold OMA.S_oeis_a277273.Good; norm_num) _ (by norm_num)
  · exact key 2087 (by unfold OMA.S_oeis_a277273.Good; norm_num) _ (by norm_num)
  · exact key 4157 (by unfold OMA.S_oeis_a277273.Good; norm_num) _ (by norm_num)
