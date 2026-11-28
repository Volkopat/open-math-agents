import OMAStatements.S_oeis_a299406
import Mathlib

open OMA.S_oeis_a299406
open ArithmeticFunction PowerSeries
open scoped ArithmeticFunction.zeta ArithmeticFunction.Moebius

private lemma powInd_apply (k n : ℕ) : powInd k n = if n ≠ 0 ∧ ∃ m : ℕ, m ^ k = n then 1 else 0 := rfl

private lemma powInd_mult (k : ℕ) (hk : 0 < k) : IsMultiplicative (powInd k) := by
  refine ⟨?_, ?_⟩
  · rw [powInd_apply, if_pos ⟨one_ne_zero, 1, one_pow k⟩]
  · intro m n hmn
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [powInd_apply]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [powInd_apply]
    simp only [powInd_apply, ne_eq, mul_eq_zero, hm.ne', hn.ne', or_self, not_false_eq_true,
      true_and]
    have hu : IsUnit (gcd m n) := by
      rw [Nat.isUnit_iff]; exact hmn
    have hu' : IsUnit (gcd n m) := by
      rw [Nat.isUnit_iff]; exact hmn.symm
    by_cases h : ∃ x : ℕ, x ^ k = m * n
    · obtain ⟨x, hx⟩ := h
      obtain ⟨y, hy⟩ := exists_eq_pow_of_mul_eq_pow hu hx.symm
      obtain ⟨z, hz⟩ := exists_eq_pow_of_mul_eq_pow hu' (by rw [mul_comm]; exact hx.symm)
      rw [if_pos ⟨x, hx⟩, if_pos ⟨y, hy.symm⟩, if_pos ⟨z, hz.symm⟩, mul_one]
    · rw [if_neg h]
      by_cases h1 : ∃ y : ℕ, y ^ k = m
      · by_cases h2 : ∃ z : ℕ, z ^ k = n
        · exfalso; obtain ⟨y, rfl⟩ := h1; obtain ⟨z, rfl⟩ := h2
          exact h ⟨y * z, mul_pow y z k⟩
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]

private lemma powInd_pp (k : ℕ) (hk : 0 < k) (p : ℕ) (hp : p.Prime) (e : ℕ) :
    powInd k (p ^ e) = if k ∣ e then 1 else 0 := by
  rw [powInd_apply]
  have hpe : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  by_cases hd : k ∣ e
  · obtain ⟨j, rfl⟩ := hd
    rw [if_pos ⟨hpe, p ^ j, by rw [← pow_mul, mul_comm]⟩, if_pos (dvd_mul_right k j)]
  · rw [if_neg hd, if_neg]
    rintro ⟨-, m, hm⟩
    have hmd : m ∣ p ^ e := ⟨m ^ (k - 1), by rw [← hm, ← pow_succ', Nat.sub_add_cancel hk]⟩
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hmd
    rw [← pow_mul] at hm
    exact hd ⟨j, by rw [mul_comm]; exact (Nat.pow_right_injective hp.two_le hm).symm⟩

private def Phi (p : ℕ) (f : ArithmeticFunction ℤ) : PowerSeries ℤ := PowerSeries.mk fun e => f (p ^ e)

private lemma Phi_mul (p : ℕ) (hp : p.Prime) (f g : ArithmeticFunction ℤ) :
    Phi p (f * g) = Phi p f * Phi p g := by
  ext e
  rw [Phi, coeff_mk, coeff_mul, mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => f x * g y),
    Nat.divisors_prime_pow hp, Finset.sum_map, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i j => coeff i (Phi p f) * coeff j (Phi p g))]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  simp only [Function.Embedding.coeFn_mk, Phi, coeff_mk]
  rw [Nat.pow_div (by omega) hp.pos]

private lemma Phi_ind (k : ℕ) (hk : 0 < k) (p : ℕ) (hp : p.Prime) :
    Phi p (powInd k) * (1 - X ^ k) = 1 := by
  ext e
  rw [mul_sub, mul_one, map_sub, coeff_mul_X_pow', coeff_one, Phi, coeff_mk, coeff_mk,
    powInd_pp k hk p hp]
  by_cases he : k ≤ e
  · rw [if_pos he, powInd_pp k hk p hp]
    have : k ∣ e ↔ k ∣ e - k := by
      conv_lhs => rw [show e = e - k + k by omega]
      exact Nat.dvd_add_self_right
    by_cases h : k ∣ e
    · rw [if_pos h, if_pos (this.1 h), if_neg (by omega)]; simp
    · rw [if_neg h, if_neg (fun h' => h (this.2 h')), if_neg (by omega)]; simp
  · rw [if_neg he]
    rcases Nat.eq_zero_or_pos e with rfl | hpos
    · simp
    · rw [if_neg (fun h => by have := Nat.le_of_dvd hpos h; omega), if_neg (by omega)]; simp

private lemma Phi_zeta (p : ℕ) (hp : p.Prime) : Phi p (ζ : ArithmeticFunction ℤ) * (1 - X) = 1 := by
  have h := Phi_ind 1 one_pos p hp
  rw [pow_one] at h
  have e : Phi p (ζ : ArithmeticFunction ℤ) = Phi p (powInd 1) := by
    ext e
    simp only [Phi, coeff_mk, powInd_pp 1 one_pos p hp, one_dvd, if_true]
    rw [natCoe_apply, zeta_apply, if_neg (pow_ne_zero _ hp.ne_zero)]
    simp
  rw [e, h]

private lemma b_pp (b : ArithmeticFunction ℤ) (hb : b * (ζ : ArithmeticFunction ℤ) = powInd 3)
    (p : ℕ) (hp : p.Prime) (e : ℕ) :
    b (p ^ e) = if e % 3 = 0 then 1 else if e % 3 = 1 then -1 else 0 := by
  have hs : ∀ e, ∑ i ∈ Finset.range (e + 1), b (p ^ i) = if 3 ∣ e then 1 else 0 := by
    intro e
    rw [← powInd_pp 3 (by norm_num) p hp, ← hb, coe_mul_zeta_apply, Nat.divisors_prime_pow hp,
      Finset.sum_map]
    rfl
  rcases e with _ | e
  · have := hs 0; simp at this; simp [this]
  · have h1 := hs (e + 1)
    have h0 := hs e
    rw [Finset.sum_range_succ, h0] at h1
    split_ifs at h1 ⊢ <;> omega

private lemma negpow (e : ℕ) : ((-1 : ℤ) ^ e) = if e % 2 = 0 then 1 else -1 := by
  rcases Nat.even_or_odd' e with ⟨k, rfl | rfl⟩
  · rw [pow_mul]; simp
  · rw [pow_succ, pow_mul]; simp

theorem OMA.solution : type_of% @OMA.S_oeis_a299406.main := by
  intro a b ha hb n hn
  have hbm : IsMultiplicative b := by
    have : b = powInd 3 * μ := by
      rw [← hb, mul_assoc, coe_zeta_mul_moebius, mul_one]
    rw [this]
    exact (powInd_mult 3 (by norm_num)).mul isMultiplicative_moebius
  set c := pmul liouville b with hc
  have hcm : IsMultiplicative c := isMultiplicative_liouville.pmul hbm
  have c_pp : ∀ p, p.Prime → ∀ e, c (p ^ e) =
      if e % 6 = 0 ∨ e % 6 = 1 then 1 else if e % 6 = 3 ∨ e % 6 = 4 then -1 else 0 := by
    intro p hp e
    rw [hc, pmul_apply, liouville_apply (pow_ne_zero _ hp.ne_zero), cardFactors_apply_prime_pow hp,
      b_pp b hb p hp, negpow]
    split_ifs <;> omega
  have key : c * powInd 2 * powInd 3 = (ζ : ArithmeticFunction ℤ) * powInd 6 := by
    have m1 : IsMultiplicative (c * powInd 2 * powInd 3) :=
      (hcm.mul (powInd_mult 2 (by norm_num))).mul (powInd_mult 3 (by norm_num))
    have m2 : IsMultiplicative ((ζ : ArithmeticFunction ℤ) * powInd 6) :=
      isMultiplicative_zeta.natCast.mul (powInd_mult 6 (by norm_num))
    rw [IsMultiplicative.eq_iff_eq_on_prime_powers _ m1 _ m2]
    intro p e hp
    have hPhi : Phi p (c * powInd 2 * powInd 3) = Phi p ((ζ : ArithmeticFunction ℤ) * powInd 6) := by
      rw [Phi_mul p hp, Phi_mul p hp, Phi_mul p hp]
      have hcX : Phi p c * (1 + X ^ 3) = 1 + X := by
        ext e
        rw [mul_add, mul_one, map_add, coeff_mul_X_pow', map_add, coeff_one, coeff_X, Phi, coeff_mk,
          coeff_mk, c_pp p hp]
        by_cases he : 3 ≤ e
        · rw [if_pos he, c_pp p hp]; split_ifs <;> omega
        · rw [if_neg he]; split_ifs <;> omega
      have hK : ((1 - X ^ 2) * (1 - X ^ 6) : PowerSeries ℤ) ≠ 0 := by
        intro h
        have := congrArg (constantCoeff) h
        simp at this
      apply mul_right_cancel₀ hK
      have e2 := Phi_ind 2 (by norm_num) p hp
      have e3 := Phi_ind 3 (by norm_num) p hp
      have e6 := Phi_ind 6 (by norm_num) p hp
      have ez := Phi_zeta p hp
      calc Phi p c * Phi p (powInd 2) * Phi p (powInd 3) * ((1 - X ^ 2) * (1 - X ^ 6))
          = (Phi p c * (1 + X ^ 3)) * (Phi p (powInd 2) * (1 - X ^ 2)) *
              (Phi p (powInd 3) * (1 - X ^ 3)) := by ring
        _ = 1 + X := by rw [hcX, e2, e3]; ring
        _ = (Phi p (ζ : ArithmeticFunction ℤ) * (1 - X)) * (Phi p (powInd 6) * (1 - X ^ 6)) * (1 + X) := by
            rw [ez, e6]; ring
        _ = Phi p (ζ : ArithmeticFunction ℤ) * Phi p (powInd 6) * ((1 - X ^ 2) * (1 - X ^ 6)) := by ring
    have := congrArg (coeff e) hPhi
    simpa [Phi] using this
  have hunit : IsUnit (powInd 2 * powInd 3) := by
    rw [isUnit_iff_isUnit_apply_one, mul_apply, Nat.divisorsAntidiagonal_one]
    simp [powInd_apply]
  have hac : a = c := by
    apply hunit.mul_right_cancel
    rw [← mul_assoc, ← mul_assoc, ha, key]
  rw [hac, hc, pmul_apply, liouville_apply hn.ne']
