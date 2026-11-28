import OMAStatements.S_oeis_a246048
import Mathlib

-- Problem: A246048, no prime power n satisfies n!^n (2n)! | (n^2)!.
-- Upstream: formal-conjectures statements/oeis-a246048.lean (declaration OMA.S_oeis_a246048.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Proof: by Legendre's formula (p-1) v_p(m!) = m - s_p(m). For n = p^(k+1) the digit sums of
-- n and n^2 are 1 and that of 2n is at most 2, so (p-1) v_p(n!^n (2n)!) >= n^2 + n - 2, which
-- exceeds (p-1) v_p((n^2)!) = n^2 - 1.

namespace OMA.P_oeis_a246048

open OMA.S_oeis_a246048 Nat

theorem digsum_pow_mul (p j c : ℕ) (hp : 1 < p) (hc : 0 < c) :
    (Nat.digits p (p ^ j * c)).sum = (Nat.digits p c).sum := by
  rw [Nat.digits_base_pow_mul hp hc]
  simp

theorem main' : ∀ p k : ℕ, p.Prime → ¬ isTerm (p ^ (k + 1)) := by
  intro p k hp h
  have := Fact.mk hp
  unfold isTerm at h
  set n := p ^ (k + 1) with hn
  have hp1 : 1 < p := hp.one_lt
  have hn2 : 2 ≤ n := by
    have : p ≤ p ^ (k + 1) := Nat.le_self_pow (by omega) p
    omega
  -- valuations
  have hA : n.factorial ^ n * (2 * n).factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _)
  have hB : (n ^ 2).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hv : padicValNat p (n.factorial ^ n * (2 * n).factorial) ≤
      padicValNat p ((n ^ 2).factorial) := by
    have h1 : p ^ padicValNat p (n.factorial ^ n * (2 * n).factorial) ∣ (n ^ 2).factorial :=
      dvd_trans pow_padicValNat_dvd h
    exact (padicValNat_dvd_iff_le hB).mp h1
  rw [padicValNat.mul (pow_ne_zero _ (Nat.factorial_ne_zero _)) (Nat.factorial_ne_zero _),
    padicValNat.pow] at hv
  have e1 := sub_one_mul_padicValNat_factorial (p := p) n
  have e2 := sub_one_mul_padicValNat_factorial (p := p) (2 * n)
  have e3 := sub_one_mul_padicValNat_factorial (p := p) (n ^ 2)
  have s1 : (Nat.digits p n).sum = 1 := by
    rw [hn, show p ^ (k + 1) = p ^ (k + 1) * 1 by ring, digsum_pow_mul p _ 1 hp1 (by norm_num),
      Nat.digits_of_lt p 1 (by norm_num) hp1]
    simp
  have s3 : (Nat.digits p (n ^ 2)).sum = 1 := by
    rw [hn, show (p ^ (k + 1)) ^ 2 = p ^ (2 * k + 2) * 1 by ring,
      digsum_pow_mul p _ 1 hp1 (by norm_num), Nat.digits_of_lt p 1 (by norm_num) hp1]
    simp
  have s2 : (Nat.digits p (2 * n)).sum ≤ 2 := by
    rw [hn, show 2 * p ^ (k + 1) = p ^ (k + 1) * 2 by ring, digsum_pow_mul p _ 2 hp1 (by norm_num)]
    exact Nat.digit_sum_le p 2
  rw [s1] at e1
  rw [s3] at e3
  set X := (p - 1) * padicValNat p n.factorial
  set Y := (p - 1) * padicValNat p (2 * n).factorial
  set Z := (p - 1) * padicValNat p (n ^ 2).factorial
  have hn2' : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hX : X + 1 = n := by omega
  have hY : Y + (Nat.digits p (2 * n)).sum = 2 * n := by
    have := Nat.digit_sum_le p (2 * n)
    omega
  have hZ : Z + 1 = n ^ 2 := by omega
  have hmul : n * X + Y ≤ Z := by
    have := Nat.mul_le_mul_left (p - 1) hv
    simp only [X, Y, Z]
    calc n * ((p - 1) * padicValNat p n.factorial) + (p - 1) * padicValNat p (2 * n).factorial
        = (p - 1) * (n * padicValNat p n.factorial + padicValNat p (2 * n).factorial) := by ring
      _ ≤ (p - 1) * padicValNat p (n ^ 2).factorial := this
  have hnX : n * X + n = n ^ 2 := by rw [← hX]; ring
  nlinarith

end OMA.P_oeis_a246048

theorem OMA.solution : type_of% @OMA.S_oeis_a246048.main := OMA.P_oeis_a246048.main'
