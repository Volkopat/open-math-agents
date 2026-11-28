import OMAStatements.S_oeis_a182133
theorem OMA.solution : type_of% @OMA.S_oeis_a182133.main := by
  intro n hp hq hr
  have K (d t a : ℕ) (hl : (d + 1).Prime) (e : (30 * n + 13) * (90 * n + 37) * (150 * n + 61) = d * t + 1) :
      a ^ ((30 * n + 13) * (90 * n + 37) * (150 * n + 61)) ≡ a [MOD d + 1] := by
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
      ⟨K _ (13500 * n ^ 2 + 11490 * n + 2445) a hp (by ring), K _ (4500 * n ^ 2 + 3830 * n + 815) a hq (by ring)⟩,
     K _ (2700 * n ^ 2 + 2298 * n + 489) a hr (by ring)⟩
