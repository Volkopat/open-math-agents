import OMAStatements.S_oeis_a135953

theorem OMA.solution : type_of% @OMA.S_oeis_a135953.main := by
  rintro m ⟨p, hp, rfl, -, hΩ⟩
  -- p is odd, since fib 2 = 1 has no prime factors
  rcases hp.eq_two_or_odd' with h2 | ⟨k, hk⟩
  · subst h2
    simp at hΩ
  -- -1 is a square modulo fib p
  have hsq : IsSquare (-1 : ZMod (Nat.fib p)) := by
    rw [hk, Nat.fib_two_mul_add_one]
    exact ZMod.isSquare_neg_one_of_eq_sq_add_sq_of_coprime rfl
      (Nat.fib_coprime_fib_succ k).symm
  have hdiv : ∀ q, q ∣ Nat.fib p → ∃ a b : ℕ, q = a ^ 2 + b ^ 2 := fun q hq =>
    Nat.eq_sq_add_sq_of_isSquare_mod_neg_one (ZMod.isSquare_neg_one_of_dvd hq hsq)
  set n := Nat.fib p with hn
  have hn1 : 1 < n := ArithmeticFunction.cardFactors_pos_iff_one_lt.mp (by omega)
  set q := n.minFac with hq
  have hqp : q.Prime := Nat.minFac_prime (by omega)
  obtain ⟨r, hr⟩ := Nat.minFac_dvd n
  have hr0 : r ≠ 0 := by rintro rfl; simp at hr; omega
  have hΩr : ArithmeticFunction.cardFactors r = 1 := by
    rw [hr, ArithmeticFunction.cardFactors_mul hqp.ne_zero hr0,
      ArithmeticFunction.cardFactors_apply_prime hqp] at hΩ
    omega
  have hrp : r.Prime := ArithmeticFunction.cardFactors_eq_one_iff_prime.mp hΩr
  obtain ⟨a, b, hab⟩ := hdiv q (Nat.minFac_dvd n)
  obtain ⟨c, d, hcd⟩ := hdiv r (Dvd.intro_left _ hr.symm)
  refine ⟨a, b, c, d, ?_, ?_, ?_⟩
  · rw [← hab, ← hcd]; exact hr
  · rw [← hab]; exact hqp.one_lt
  · rw [← hcd]; exact hrp.one_lt
