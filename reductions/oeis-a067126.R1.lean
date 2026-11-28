import OMAStatements.S_oeis_a067126
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open OMA.S_oeis_a067126

namespace OMA.R_oeis_a067126_R1

/-- After the even case is removed, odd composite prime powers may be treated separately. -/
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → Odd n → IsPrimePow n → ¬ n.Prime → IsTerm n → n = 9

/-- The remaining odd composites have at least two distinct prime factors. -/
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → Odd n → ¬ IsPrimePow n → ¬ n.Prime → IsTerm n → False

/-- A power of two above 4 has a prime strictly above its midpoint plus one. -/
theorem prime_above_power_two_midpoint (r : ℕ) (h : 2 < (2 : ℕ) ^ r) :
    ∃ p : ℕ, p.Prime ∧ 2 ^ r + 1 < p ∧ p < 2 * 2 ^ r := by
  let m := (2 : ℕ) ^ r
  have hm : 2 < m := h
  have hEven : ¬ (2 * m).Prime :=
    Nat.not_prime_of_dvd_of_lt (dvd_mul_right 2 m) (by decide) (by omega)
  by_cases hr : Odd r
  · obtain ⟨p, hp, hmp, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
    have hdiv : 3 ∣ m + 1 := by
      simpa [m] using hr.nat_add_dvd_pow_add_pow 2 1
    have hComp : ¬ (m + 1).Prime :=
      Nat.not_prime_of_dvd_of_lt hdiv (by decide) (by omega)
    have hp₁ : p ≠ m + 1 := fun hEq => hComp (hEq ▸ hp)
    have hp₂ : p ≠ 2 * m := fun hEq => hEven (hEq ▸ hp)
    exact ⟨p, hp, by change m + 1 < p; omega, by change p < 2 * m; omega⟩
  have hs : Odd (r + 1) := Nat.odd_add_one.mpr hr
  obtain ⟨p, hp, hmp, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul (m + 1) (by omega)
  have hdiv : 3 ∣ 2 * m + 1 := by
    simpa [m, pow_succ, mul_comm] using hs.nat_add_dvd_pow_add_pow 2 1
  have hComp : ¬ (2 * m + 1).Prime :=
    Nat.not_prime_of_dvd_of_lt hdiv (by decide) (by omega)
  have hEven' : ¬ (2 * (m + 1)).Prime :=
    Nat.not_prime_of_dvd_of_lt (dvd_mul_right 2 (m + 1)) (by decide) (by omega)
  have hp₀ : p ≠ 2 * m := fun hEq => hEven (hEq ▸ hp)
  have hp₁ : p ≠ 2 * m + 1 := fun hEq => hComp (hEq ▸ hp)
  have hp₂ : p ≠ 2 * (m + 1) := fun hEq => hEven' (hEq ▸ hp)
  exact ⟨p, hp, hmp, by change p < 2 * m; omega⟩

/-- Every even record for Euler's totient is at most 4. -/
theorem even_totient_record_le_four (n : ℕ) (he : Even n) (hrecord : IsTerm n) :
    n ≤ 4 := by
  by_contra! h₄
  obtain ⟨k, w, hw, hnEq⟩ := Nat.exists_eq_two_pow_mul_odd (show n ≠ 0 by omega)
  have hk : 0 < k := by
    by_contra! hk'
    have hk0 : k = 0 := by omega
    rw [hk0, pow_zero, one_mul] at hnEq
    exact (Nat.not_even_iff_odd.mpr hw) (hnEq ▸ he)
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  let m := 2 ^ r * w
  have hnEven : n = 2 * m := by
    rw [hnEq, Nat.succ_eq_add_one, pow_succ]
    dsimp [m]
    ring
  have hm : 2 < m := by omega
  have hcop : Nat.Coprime 2 w := Nat.prime_two.coprime_iff_not_dvd.mpr hw.not_two_dvd_nat
  have htot : n.totient = 2 ^ r * w.totient := by
    rw [hnEq, Nat.totient_mul (hcop.pow_left (r + 1)), Nat.totient_prime_pow_succ Nat.prime_two]
    norm_num
  have hprime : ¬ n.Prime := by
    rw [hnEven]
    exact Nat.not_prime_of_dvd_of_lt (dvd_mul_right 2 m) (by decide) (by omega)
  by_cases hw1 : w = 1
  · have hmEq : m = 2 ^ r := by simp [m, hw1]
    have hphiEq : n.totient = m := by rw [htot, hw1, Nat.totient_one, mul_one, hmEq]
    obtain ⟨p, hp, hmp, hpn⟩ := prime_above_power_two_midpoint r (hmEq ▸ hm)
    have hpLt : p < n := by rw [hnEven, hmEq]; exact hpn
    have hlimit := hrecord p hp.pos hpLt
    rw [Nat.totient_prime hp, hphiEq, hmEq] at hlimit
    omega
  have hwgt : 1 < w := by
    have hw0 : w ≠ 0 := fun hzero => (Nat.not_odd_zero (hzero ▸ hw))
    omega
  have hphiLt : n.totient < m := by
    rw [htot]
    exact Nat.mul_lt_mul_of_pos_left (Nat.totient_lt w hwgt) (pow_pos (by decide) _)
  obtain ⟨p, hp, hmp, hpn⟩ := Nat.exists_prime_lt_and_le_two_mul m (by omega)
  have hpne : p ≠ n := fun hEq => hprime (hEq ▸ hp)
  have hpLt : p < n := by omega
  have hlimit := hrecord p hp.pos hpLt
  rw [Nat.totient_prime hp] at hlimit
  omega

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a067126.main := by
  intro hPowers hOther n hrecord hn hcomp
  by_cases he : Even n
  · have hle := even_totient_record_le_four n he hrecord
    have hmod := Nat.dvd_iff_mod_eq_zero.mp he.two_dvd
    have hcases : n = 2 ∨ n = 4 := by omega
    rcases hcases with htwo | hfour
    · exact (hcomp (htwo.symm ▸ Nat.prime_two)).elim
    · exact Or.inl hfour
  have ho := Nat.not_even_iff_odd.mp he
  by_cases hpow : IsPrimePow n
  · exact Or.inr (hPowers n hn ho hpow hcomp hrecord)
  · exact (hOther n hn ho hpow hcomp hrecord).elim

end OMA.R_oeis_a067126_R1
