import OMAReductions.R_oeis_a228947_R1
import Mathlib

namespace OMA.P228947H1

open ArithmeticFunction

/-- `B ^ 2 < (B + A) A` as soon as `35 A ≥ 24 B > 0`. -/
lemma sq_lt_of_ratio (A B : ℤ) (hB : 0 < B) (h : 24 * B ≤ 35 * A) : B ^ 2 < (B + A) * A := by
  nlinarith

/-- The arithmetic core. `P, Q` are the primes, `x = P ^ (2 a - 1)`, `y = Q ^ (2 b - 1)`,
`s = σ (P ^ (2 a))`, `t = σ (Q ^ (2 b))`. -/
lemma core (P Q x y s t : ℤ) (hP : 3 ≤ P) (hPQ : P < Q) (hPodd : P % 2 = 1) (hQodd : Q % 2 = 1)
    (hx3 : P ≤ x) (hy : Q ≤ y) (hx : P = 3 → (x = 3 ∨ x = 27 ∨ 243 ≤ x))
    (hs : s * (P - 1) + 1 = P * P * x) (ht : t * (Q - 1) + 1 = Q * Q * y)
    (heq : s * t = P * x * (Q * y) + x * (P - 1) * (y * (Q - 1))) : False := by
  have key : (P * Q + (P - 1) * (Q - 1)) * ((P - 1) * (Q - 1)) * (x * y) + P * P * x + Q * Q * y
      = (P * Q) ^ 2 * (x * y) + 1 := by
    linear_combination (t * (Q - 1)) * hs + (P * P * x - 1) * ht - ((P - 1) * (Q - 1)) * heq
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hX : 0 < x * y := mul_pos hx0 hy0
  have hP0 : 0 < P := by linarith
  have hQ0 : 0 < Q := by linarith
  have hPx : 0 < P * P * x := mul_pos (mul_pos hP0 hP0) hx0
  have hQy : 0 < Q * Q * y := mul_pos (mul_pos hQ0 hQ0) hy0
  have hfin : (P * Q) ^ 2 < (P * Q + (P - 1) * (Q - 1)) * ((P - 1) * (Q - 1)) → False := by
    intro hD
    have := mul_lt_mul_of_pos_right hD hX
    linarith
  rcases (by omega : P = 3 ∨ 5 ≤ P) with rfl | hP5
  · have hQ13 : Q ≤ 13 := by
      by_contra hQ
      apply hfin
      nlinarith
    have hxy1 : 3 * y ≤ x * y := mul_le_mul_of_nonneg_right hx3 hy0.le
    have hxy2 : x * Q ≤ x * y := mul_le_mul_of_nonneg_left hy hx0.le
    rcases hx rfl with rfl | rfl | h243
    · interval_cases Q <;> omega
    · interval_cases Q <;> omega
    · have hxy3 : 243 * y ≤ x * y := mul_le_mul_of_nonneg_right h243 hy0.le
      interval_cases Q <;> omega
  · have hQ7 : 7 ≤ Q := by omega
    apply hfin
    apply sq_lt_of_ratio
    · positivity
    · nlinarith

/-- `σ (p ^ k) (p - 1) + 1 = p ^ (k + 1)`. -/
lemma sigma_pp (p k : ℕ) (hp : p.Prime) : sigma 1 (p ^ k) * (p - 1) + 1 = p ^ (k + 1) := by
  rw [sigma_one_apply_prime_pow hp]
  have h := geom_sum_mul_add (p - 1) (k + 1)
  rwa [Nat.sub_add_cancel hp.one_le] at h

/-- The case `m = p ^ a q ^ b` with odd primes `p < q`. -/
lemma two_primes {p q a b : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2)
    (hpq : p < q) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    sigma 1 ((p ^ a * q ^ b) ^ 2) ≠ (p ^ a * q ^ b) ^ 2 + Nat.totient ((p ^ a * q ^ b) ^ 2) := by
  intro h
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, b = d + 1 := ⟨b - 1, by omega⟩
  have e1 : (p ^ (c + 1) * q ^ (d + 1)) ^ 2 = p ^ (2 * c + 2) * q ^ (2 * d + 2) := by ring
  rw [e1] at h
  have hcop : Nat.Coprime (p ^ (2 * c + 2)) (q ^ (2 * d + 2)) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq).mpr hpq.ne)
  have hs := sigma_pp p (2 * c + 2) hp
  have ht := sigma_pp q (2 * d + 2) hq
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, Nat.totient_mul hcop,
    Nat.totient_prime_pow hp (by omega), Nat.totient_prime_pow hq (by omega)] at h
  generalize sigma 1 (p ^ (2 * c + 2)) = s at h hs
  generalize sigma 1 (q ^ (2 * d + 2)) = t at h ht
  have ex1 : 2 * c + 2 - 1 = 2 * c + 1 := by omega
  have ex2 : 2 * d + 2 - 1 = 2 * d + 1 := by omega
  rw [ex1, ex2] at h
  have hpow1 : p ^ (2 * c + 2) = p * p ^ (2 * c + 1) := by ring
  have hpow2 : p ^ (2 * c + 2 + 1) = p * p * p ^ (2 * c + 1) := by ring
  have hqow1 : q ^ (2 * d + 2) = q * q ^ (2 * d + 1) := by ring
  have hqow2 : q ^ (2 * d + 2 + 1) = q * q * q ^ (2 * d + 1) := by ring
  rw [hpow1, hqow1] at h
  rw [hpow2] at hs
  rw [hqow2] at ht
  have hx3 : p ≤ p ^ (2 * c + 1) := Nat.le_self_pow (by omega) p
  have hy3 : q ≤ q ^ (2 * d + 1) := Nat.le_self_pow (by omega) q
  have hx : p = 3 → (p ^ (2 * c + 1) = 3 ∨ p ^ (2 * c + 1) = 27 ∨ 243 ≤ p ^ (2 * c + 1)) := by
    rintro rfl
    rcases c with _ | _ | c
    · left; norm_num
    · right; left; norm_num
    · right; right
      calc 243 = 3 ^ 5 := by norm_num
        _ ≤ 3 ^ (2 * (c + 2) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize p ^ (2 * c + 1) = x at h hs hx3 hx
  generalize q ^ (2 * d + 1) = y at h ht hy3
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq3 : 3 ≤ q := by have := hq.two_le; omega
  have hpo := Nat.odd_iff.mp (hp.odd_of_ne_two hp2)
  have hqo := Nat.odd_iff.mp (hq.odd_of_ne_two hq2)
  zify [hp.one_le, hq.one_le] at h hs ht
  apply core (p : ℤ) (q : ℤ) (x : ℤ) (y : ℤ) (s : ℤ) (t : ℤ)
  · exact_mod_cast hp3
  · exact_mod_cast hpq
  · omega
  · omega
  · exact_mod_cast hx3
  · exact_mod_cast hy3
  · intro h3
    have h3' : p = 3 := by exact_mod_cast h3
    rcases hx h3' with h1 | h1 | h1
    · left; exact_mod_cast h1
    · right; left; exact_mod_cast h1
    · right; right; exact_mod_cast h1
  · exact hs
  · exact ht
  · exact h

theorem sol : OMA.R_oeis_a228947_R1.H1 := by
  intro m hm hcard
  have hm0 : m ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hm
    omega
  obtain ⟨p, q, hpq, hpqs⟩ := Finset.card_eq_two.mp hcard
  have hpm : p ∈ m.primeFactors := by rw [hpqs]; simp
  have hqm : q ∈ m.primeFactors := by rw [hpqs]; simp
  have hp := Nat.prime_of_mem_primeFactors hpm
  have hq := Nat.prime_of_mem_primeFactors hqm
  have hpd := Nat.dvd_of_mem_primeFactors hpm
  have hqd := Nat.dvd_of_mem_primeFactors hqm
  have hp2 : p ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hpd
    obtain ⟨j, hj⟩ := hm
    omega
  have hq2 : q ≠ 2 := by
    rintro rfl
    obtain ⟨k, hk⟩ := hqd
    obtain ⟨j, hj⟩ := hm
    omega
  have ha := hp.factorization_pos_of_dvd hm0 hpd
  have hb := hq.factorization_pos_of_dvd hm0 hqd
  have hfac := Nat.prod_factorization_pow_eq_self hm0
  rw [Finsupp.prod, Nat.support_factorization, hpqs, Finset.prod_pair hpq] at hfac
  generalize m.factorization p = a at hfac ha
  generalize m.factorization q = b at hfac hb
  subst hfac
  rcases lt_or_gt_of_ne hpq with h | h
  · exact two_primes hp hq hp2 hq2 h ha hb
  · rw [mul_comm]
    exact two_primes hq hp hq2 hp2 h hb ha

end OMA.P228947H1

theorem OMA.solution : OMA.R_oeis_a228947_R1.H1 := OMA.P228947H1.sol

