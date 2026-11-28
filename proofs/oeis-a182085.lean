import OMAStatements.S_oeis_a182085
theorem OMA.solution : type_of% @OMA.S_oeis_a182085.main := by
  intro k hp hq hr
  have K (d t a : ℕ) (hl : (d + 1).Prime) (e : (30 * k + 7) * (60 * k + 13) * (150 * k + 31) = d * t + 1) :
      a ^ ((30 * k + 7) * (60 * k + 13) * (150 * k + 31)) ≡ a [MOD d + 1] := by
    have := Fact.mk hl
    rw [e, ← ZMod.natCast_eq_natCast_iff]
    push_cast
    by_cases h : (a : ZMod (d + 1)) = 0
    · simp [h]
    · have := ZMod.pow_card_sub_one_eq_one h
      simp at this
      rw [pow_succ, pow_mul, this, one_pow, one_mul]
  refine ⟨by have := Nat.mul_le_mul (Nat.mul_le_mul hp.two_le hq.two_le) hr.two_le; omega, Nat.not_prime_mul (by nlinarith) (by omega), fun a => ?_⟩
  exact (Nat.modEq_and_modEq_iff_modEq_mul (((Nat.coprime_primes hp hr).2 (by omega)).mul ((Nat.coprime_primes hq hr).2 (by omega)))).1
    ⟨(Nat.modEq_and_modEq_iff_modEq_mul ((Nat.coprime_primes hp hq).2 (by omega))).1
      ⟨K _ (9000 * k ^ 2 + 4110 * k + 470) a hp (by ring), K _ (4500 * k ^ 2 + 2055 * k + 235) a hq (by ring)⟩,
     K _ (1800 * k ^ 2 + 822 * k + 94) a hr (by ring)⟩
