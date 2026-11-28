import OMAStatements.S_oeis_a066488

/-! The order of two modulo the sixth cyclotomic polynomial at a power of two. -/
-- Credit: @STARDUSTLC666

namespace JacobsthalCongruence

open OMA.S_oeis_a066488

private abbrev mersenneNumber := OMA.S_oeis_a066488.mersenne

private def modulus (k : ℕ) := mersenneNumber k ^ 2 + mersenneNumber k + 1

private lemma two_power (k : ℕ) : 2 ^ k = mersenneNumber k + 1 := by
  unfold mersenneNumber OMA.S_oeis_a066488.mersenne
  have := Nat.two_pow_pos k
  omega

private lemma large_mersenne {k : ℕ} (hk : 2 ≤ k) : 3 ≤ mersenneNumber k := by
  have h := Nat.pow_le_pow_right (by decide : 0 < 2) hk
  rw [two_power k] at h
  norm_num at h
  omega

private lemma power_cast (k : ℕ) :
    (2 : ZMod (modulus k)) ^ k = (mersenneNumber k : ZMod (modulus k)) + 1 := by
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_add, Nat.cast_one] using
    congrArg (fun a : ℕ => (a : ZMod (modulus k))) (two_power k)

private lemma relation (k : ℕ) :
    (mersenneNumber k : ZMod (modulus k)) ^ 2 + mersenneNumber k + 1 = 0 := by
  have hz := ZMod.natCast_self (modulus k)
  change ((mersenneNumber k ^ 2 + mersenneNumber k + 1 : ℕ) : ZMod (modulus k)) = 0 at hz
  push_cast at hz
  exact hz

private lemma square_residue (k : ℕ) :
    (2 : ZMod (modulus k)) ^ (2*k) = mersenneNumber k := by
  rw [Nat.mul_comm 2 k, pow_mul, power_cast]
  linear_combination relation k

private lemma half_period (k : ℕ) : (2 : ZMod (modulus k)) ^ (3*k) = -1 := by
  rw [show 3*k = 2*k+k by omega, pow_add, square_residue, power_cast]
  linear_combination relation k

private lemma not_one {a m : ℕ} (ha : 1 < a) (hm : a < m) : (a : ZMod m) ≠ 1 := by
  intro eq
  have h := (ZMod.natCast_eq_natCast_iff' a 1 m).mp (by simpa only [Nat.cast_one] using eq)
  rw [Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt (by omega : 1 < m)] at h
  omega

-- A proper order dividing 6k is below 2k, or is one of 2k and 3k.
private lemma exact_order (k : ℕ) (hk : 2 ≤ k) :
    orderOf (2 : ZMod (modulus k)) = 6*k := by
  let d := orderOf (2 : ZMod (modulus k))
  change d = 6*k
  have large := large_mersenne hk
  have dm : mersenneNumber k < modulus k := by unfold modulus; nlinarith
  have half := half_period k
  have period : (2 : ZMod (modulus k)) ^ (6*k) = 1 := by
    rw [show 6*k = (3*k)*2 by omega, pow_mul, half]
    norm_num
  have divides : d ∣ 6*k := orderOf_dvd_of_pow_eq_one period
  have positive : 0 < d := Nat.pos_of_dvd_of_pos divides (by omega)
  have unit : (2 : ZMod (modulus k)) ^ d = 1 := pow_orderOf_eq_one _
  have bound : 2*k ≤ d := by
    by_contra! short
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show d+1 ≤ 2*k by omega)
    rw [pow_succ, Nat.mul_comm 2 k, pow_mul, two_power k] at h
    have small : 2^d < modulus k := by unfold modulus; nlinarith
    have big : 1 < 2^d := lt_of_lt_of_le (by decide : 1 < 2^1)
      (Nat.pow_le_pow_right (by decide) positive)
    apply not_one big small
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using unit
  obtain ⟨q,hq⟩ := divides
  have qle : q ≤ 3 := by
    by_contra! h
    have hmul := Nat.mul_le_mul_left d (show 4 ≤ q by omega)
    omega
  interval_cases q
  · omega
  · omega
  · have eq : d = 3*k := by omega
    rw [eq, half] at unit
    have z : (2 : ZMod (modulus k)) = 0 := by linear_combination -unit
    have dvd : modulus k ∣ 2 := (ZMod.natCast_eq_zero_iff 2 _).mp (by simpa using z)
    have := Nat.le_of_dvd (by decide : 0 < 2) dvd
    omega
  · have eq : d = 2*k := by omega
    rw [eq, square_residue] at unit
    exact (not_one (by omega : 1 < mersenneNumber k) dm unit).elim

private lemma negative_power_iff (k e : ℕ) (hk : 2 ≤ k) (odd : e%2 = 1) :
    modulus k ∣ 2^e+1 ↔ 3*k ∣ e := by
  have wrap : modulus k ∣ 2^e+1 ↔ (2 : ZMod (modulus k))^e = -1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    constructor <;> intro h <;> linear_combination h
  rw [wrap]
  constructor
  · intro h
    have twice : (2 : ZMod (modulus k))^(2*e) = 1 := by
      rw [Nat.mul_comm 2 e, pow_mul, h]
      norm_num
    have dvd := orderOf_dvd_of_pow_eq_one twice
    rw [exact_order k hk, show 6*k = 2*(3*k) by omega] at dvd
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 2)).mp dvd
  · rintro ⟨q,he⟩
    have oddq : q%2 = 1 := by
      by_contra h
      have dq : 2 ∣ q := Nat.dvd_of_mod_eq_zero (by omega)
      have de : 2 ∣ e := he ▸ dvd_mul_of_dvd_right dq _
      omega
    rw [he, pow_mul, half_period, neg_one_pow_eq_pow_mod_two, oddq, pow_one]

private lemma jac_closed (n : ℕ) :
    3*(jacobsthal n : ℤ) = (2 : ℤ)^n - (-1 : ℤ)^n := by
  induction n using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more n h₀ h₁ =>
    rw [jacobsthal]
    push_cast
    simp only [pow_succ] at h₁ ⊢
    linear_combination 2*h₀ + h₁

private lemma jac_parity (n : ℕ) : jacobsthal (n+1)%2 = 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
    change (jacobsthal (n+1) + 2*jacobsthal n)%2 = 1
    omega

private lemma mersenne_parity {n : ℕ} (hn : 0 < n) : mersenneNumber n % 2 = 1 := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have h := two_power j.succ
  rw [pow_succ] at h
  omega

private lemma jac_iff (k : ℕ) (hk : 2 ≤ k) :
    k ∣ jacobsthal (k-1) ↔ 3*k ∣ mersenneNumber (k-1) := by
  by_cases even : k%2 = 0
  · have hk2 := Nat.dvd_of_mod_eq_zero even
    have j := jac_parity (k-2)
    rw [show k-2+1 = k-1 by omega] at j
    have m := mersenne_parity (show 0 < k-1 by omega)
    constructor
    · intro h
      have := hk2.trans h
      omega
    · intro h
      have := hk2.trans ((dvd_mul_left k 3).trans h)
      omega
  · have j := jac_closed (k-1)
    have sign : (-1 : ℤ)^(k-1) = 1 := by
      rw [neg_one_pow_eq_pow_mod_two, show (k-1)%2 = 0 by omega, pow_zero]
    have eq : (2 : ℤ)^(k-1) = (mersenneNumber (k-1) : ℤ)+1 := by exact_mod_cast two_power (k-1)
    rw [sign, eq] at j
    have triple : 3*jacobsthal (k-1) = mersenneNumber (k-1) := by omega
    rw [← triple]
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0 < 3)).symm

end JacobsthalCongruence

open JacobsthalCongruence OMA.S_oeis_a066488

theorem OMA.solution : type_of% @OMA.S_oeis_a066488.main := by
  intro k hk _
  exact (jac_iff k hk).trans
    (negative_power_iff k _ hk (mersenne_parity (show 0 < k-1 by omega))).symm
