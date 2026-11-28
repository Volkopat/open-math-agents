import OMAStatements.S_oeis_a000680
open OMA.S_oeis_a000680
theorem OMA.solution : type_of% @OMA.S_oeis_a000680.main := by
  intro n hn
  have d : ∀ n, 2 ^ n ∣ (2 * n).factorial := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ, Nat.factorial_succ, pow_succ']
      exact mul_dvd_mul ⟨n + 1, by ring⟩ (dvd_mul_of_dvd_right ih _)
  have e : 2 ^ n * (a n + 2 ^ n) = (2 * n).factorial + 2 ^ (2 * n) := by
    rw [mul_add, a, Nat.mul_div_cancel' (d n), ← pow_add, two_mul]
  constructor
  · intro h
    by_contra hp
    have q := Nat.minFac_prime (show 2 * n + 1 ≠ 1 by omega)
    have m := Nat.minFac_dvd (2 * n + 1)
    have : (2 * n + 1).minFac ≠ 2 * n + 1 := fun c => hp (c ▸ q)
    have := Nat.le_of_dvd (by omega) m
    have := (Nat.dvd_add_right (Nat.dvd_factorial q.pos (by omega))).1
      (e ▸ dvd_mul_of_dvd_right (m.trans h) _)
    rw [(Nat.prime_dvd_prime_iff_eq q Nat.prime_two).1 (q.dvd_of_dvd_pow this)] at m
    omega
  · intro hp
    have := Fact.mk hp
    refine (Nat.Coprime.dvd_mul_left (Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 (by omega)))).1 ?_
    rw [e, ← ZMod.natCast_eq_zero_iff]
    have w := ZMod.wilsons_lemma (p := 2 * n + 1)
    have f := ZMod.pow_card_sub_one_eq_one (p := 2 * n + 1) (a := 2) (fun c => by
      have := Nat.le_of_dvd two_pos ((ZMod.natCast_eq_zero_iff 2 (2 * n + 1)).1 (by exact_mod_cast c))
      omega)
    simp only [Nat.add_sub_cancel] at w f
    push_cast
    rw [w, f]
    ring
