import OMAStatements.S_oeis_a228541

-- Problem: A228541: Numbers having at least one prime factor of the form 30*k + 1.
-- Upstream: formal-conjectures statements/oeis-a228541.lean:0 (declaration OMA.S_oeis_a228541.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Disprove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: m = 6061 = 11 * 19 * 29 is a counterexample. Its prime factors are 11, 19, 29, none of
-- them 1 mod 30. With z = exp(pi i / 15) we have (-1)^(k/15) = z^k and z^30 = 1, and S(6061) is
-- the sum of mu(d) z^d over the eight divisors d of 6061. Modulo 30 the divisors
-- 1, 11, 19, 29, 209, 319, 551, 6061 are 1, 11, 19, 29, 29, 19, 11, 1 with Moebius values
-- 1, -1, -1, -1, 1, 1, 1, -1, so the terms cancel in pairs and S(6061) = 0.

namespace W3A228541

open OMA.S_oeis_a228541

theorem cpow_eq (k : ℕ) :
    (-1 : ℂ) ^ ((k : ℂ) / 15) = Complex.exp ((Real.pi : ℂ) * Complex.I / 15) ^ k := by
  rw [Complex.cpow_def_of_ne_zero (show (-1 : ℂ) ≠ 0 by norm_num), Complex.log_neg_one,
    ← Complex.exp_nat_mul]
  congr 1
  ring

theorem z30 : Complex.exp ((Real.pi : ℂ) * Complex.I / 15) ^ 30 = 1 := by
  rw [← Complex.exp_nat_mul]
  have e : ((30 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I / 15) = 2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e]
  exact Complex.exp_two_pi_mul_I

theorem S_eq (m : ℕ) (hm : 1 ≤ m) :
    S m = ∑ d ∈ m.divisors, ((ArithmeticFunction.moebius d : ℤ) : ℂ) *
        Complex.exp ((Real.pi : ℂ) * Complex.I / 15) ^ d := by
  unfold OMA.S_oeis_a228541.S
  have hdiv : m.divisors = (Finset.Icc 1 m).filter (fun k => k ∣ m) := by
    ext d
    simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hd, _⟩
      have h1 : 0 < d := Nat.pos_of_dvd_of_pos hd (by omega)
      have h2 : d ≤ m := Nat.le_of_dvd (by omega) hd
      exact ⟨⟨by omega, h2⟩, hd⟩
    · rintro ⟨_, hd⟩
      exact ⟨hd, by omega⟩
  rw [hdiv, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro k _
  show (if k ∣ m then (1 : ℂ) else 0) * ((ArithmeticFunction.moebius k : ℤ) : ℂ) *
      (-1 : ℂ) ^ ((k : ℂ) / 15) =
    if k ∣ m then ((ArithmeticFunction.moebius k : ℤ) : ℂ) *
      Complex.exp ((Real.pi : ℂ) * Complex.I / 15) ^ k else 0
  rw [cpow_eq]
  split_ifs <;> simp

theorem p11 : Nat.Prime 11 := by norm_num

theorem p19 : Nat.Prime 19 := by norm_num

theorem p29 : Nat.Prime 29 := by norm_num

theorem divs : Nat.divisors 6061 = {1, 11, 19, 29, 209, 319, 551, 6061} := by
  have e : Nat.divisors 6061 = Nat.divisors (11 * 19 * 29) := by norm_num
  rw [e, Nat.divisors_mul, Nat.divisors_mul, Nat.Prime.divisors p11, Nat.Prime.divisors p19,
    Nat.Prime.divisors p29]
  decide

theorem mu_p (p : ℕ) (hp : p.Prime) : ArithmeticFunction.moebius p = -1 :=
  ArithmeticFunction.moebius_apply_prime hp

theorem mu_pq (p q n : ℕ) (hn : p * q = n) (hp : p.Prime) (hq : q.Prime) (hc : Nat.Coprime p q) :
    ArithmeticFunction.moebius n = 1 := by
  have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc
  rw [mu_p p hp, mu_p q hq, hn] at h
  linarith

theorem m209 : ArithmeticFunction.moebius 209 = 1 :=
  mu_pq 11 19 209 (by norm_num) p11 p19 (by decide)

theorem m319 : ArithmeticFunction.moebius 319 = 1 :=
  mu_pq 11 29 319 (by norm_num) p11 p29 (by decide)

theorem m551 : ArithmeticFunction.moebius 551 = 1 :=
  mu_pq 19 29 551 (by norm_num) p19 p29 (by decide)

theorem m6061 : ArithmeticFunction.moebius 6061 = -1 := by
  have h1 : ArithmeticFunction.moebius (209 * 29) =
      ArithmeticFunction.moebius 209 * ArithmeticFunction.moebius 29 :=
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by decide)
  rw [m209, mu_p 29 p29, show (209 : ℕ) * 29 = 6061 by norm_num] at h1
  linarith

theorem zero6061 : MZero 6061 := by
  unfold MZero
  rw [norm_eq_zero, S_eq 6061 (by norm_num), divs]
  generalize hz : Complex.exp ((Real.pi : ℂ) * Complex.I / 15) = z
  have h30 : z ^ 30 = 1 := by
    rw [← hz]
    exact z30
  have e209 : z ^ 209 = z ^ 29 := by
    rw [show (209 : ℕ) = 30 * 6 + 29 by norm_num, pow_add, pow_mul, h30, one_pow, one_mul]
  have e319 : z ^ 319 = z ^ 19 := by
    rw [show (319 : ℕ) = 30 * 10 + 19 by norm_num, pow_add, pow_mul, h30, one_pow, one_mul]
  have e551 : z ^ 551 = z ^ 11 := by
    rw [show (551 : ℕ) = 30 * 18 + 11 by norm_num, pow_add, pow_mul, h30, one_pow, one_mul]
  have e6061 : z ^ 6061 = z ^ 1 := by
    rw [show (6061 : ℕ) = 30 * 202 + 1 by norm_num, pow_add, pow_mul, h30, one_pow, one_mul]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [ArithmeticFunction.moebius_apply_one, mu_p 11 p11, mu_p 19 p19, mu_p 29 p29, m209, m319,
    m551, m6061, e209, e319, e551, e6061]
  push_cast
  ring

theorem no_factor (p : ℕ) (hp : p.Prime) (hpd : p ∣ 6061) (h30 : p % 30 = 1) : False := by
  have e : (6061 : ℕ) = 11 * (19 * 29) := by norm_num
  rw [e] at hpd
  rcases (Nat.Prime.dvd_mul hp).mp hpd with h | h
  · have h' := (Nat.prime_dvd_prime_iff_eq hp p11).mp h
    omega
  · rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h2
    · have h' := (Nat.prime_dvd_prime_iff_eq hp p19).mp h2
      omega
    · have h' := (Nat.prime_dvd_prime_iff_eq hp p29).mp h2
      omega

end W3A228541

open OMA.S_oeis_a228541 in
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a228541.main) := by
  intro H
  obtain ⟨p, hp, hpd, hp30⟩ := (H 6061 (by norm_num)).mpr W3A228541.zero6061
  exact W3A228541.no_factor p hp hpd hp30
