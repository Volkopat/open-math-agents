import OMAStatements.S_oeis_a062208
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Tactic

open Finset
namespace OMA.S_oeis_a062208
/-- The function `m ↦ C(m,3)^n` on `ℕ`. -/
def g (n : ℕ) (m : ℕ) : ℤ := (m.choose 3 : ℤ) ^ n

/-- `coefficient n j` is the iterated forward difference `Δ^j (g n)` at `0`. -/
lemma coefficient_eq_fwdDiff (n j : ℕ) : coefficient n j = (fwdDiff 1)^[j] (g n) 0 := by
  rw [fwdDiff_iter_eq_sum_shift]
  simp [coefficient, g]

/-- Higher differences vanish: `coefficient n j = 0` for `3 n < j`. -/
lemma coefficient_eq_zero {n j : ℕ} (hj : 3 * n < j) : coefficient n j = 0 := by
  have hdeg : ((descPochhammer ℤ 3) ^ n).natDegree < j := by
    have h1 := Polynomial.natDegree_pow_le (p := descPochhammer ℤ 3) (n := n)
    rw [descPochhammer_natDegree] at h1
    omega
  have hzero := congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hdeg) 0
  rw [fwdDiff_iter_eq_sum_shift, Pi.zero_apply] at hzero
  have hval : ∀ i : ℕ, ((descPochhammer ℤ 3) ^ n).eval ((0:ℤ) + (i : ℕ) • (1:ℤ)) =
      6 ^ n * (i.choose 3 : ℤ) ^ n := by
    intro i
    rw [Polynomial.eval_pow]
    simp only [nsmul_eq_mul, mul_one, zero_add]
    rw [descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    rw [mul_pow]
    norm_num [Nat.factorial]
  simp only [hval] at hzero
  have h6 : (6 : ℤ) ^ n * coefficient n j = 0 := by
    rw [coefficient, mul_sum, ← hzero]
    refine sum_congr rfl fun i _ => ?_
    rw [smul_eq_mul]
    ring
  rcases mul_eq_zero.mp h6 with h | h
  · exact absurd h (pow_ne_zero _ (by norm_num))
  · exact h

/-- Truncation independence: summing `coefficient n j` beyond `j = 3 n` adds nothing. -/
lemma sum_coefficient_eq_sequence {n J : ℕ} (hJ : 3 * n ≤ J) :
    ∑ j ∈ range (J + 1), coefficient n j = sequence n := by
  symm
  apply sum_subset
  · intro j hj
    simp only [mem_range] at hj ⊢
    omega
  · intro j _ hj
    simp only [mem_range, not_lt] at hj
    exact coefficient_eq_zero (by omega)

/-- A uniform congruence between powers descends to the finite row sums. -/
lemma sequence_dvd_sub_of_pow {k n P : ℕ} (hpow : ∀ x : ℤ, (k : ℤ) ∣ x ^ (n + P) - x ^ n) :
    (k : ℤ) ∣ sequence (n + P) - sequence n := by
  rw [← sum_coefficient_eq_sequence (n := n) (J := 3 * (n + P)) (by omega), sequence, ← sum_sub_distrib]
  refine dvd_sum fun j _ => ?_
  rw [coefficient, coefficient, ← sum_sub_distrib]
  refine dvd_sum fun i _ => ?_
  rw [← mul_sub]
  exact Dvd.dvd.mul_left (hpow _) _

/-- Euler-type power congruence: for `n` at least every prime exponent of `k`,
`x^(n + φ k) ≡ x^n (mod k)`. -/
lemma dvd_pow_add_totient_sub {k n : ℕ} (hk : 0 < k) (hn : ∀ p : ℕ, k.factorization p ≤ n)
    (x : ℤ) : (k : ℤ) ∣ x ^ (n + k.totient) - x ^ n := by
  rw [← Int.dvd_natAbs, Int.natCast_dvd_natCast, Nat.dvd_iff_prime_pow_dvd_dvd]
  intro p j hp hpj
  rw [← Int.natCast_dvd_natCast, Int.dvd_natAbs]
  have hjle : j ≤ n := by
    have := (hp.pow_dvd_iff_le_factorization hk.ne').mp hpj
    exact this.trans (hn p)
  rw [pow_add, ← mul_sub_one]
  push_cast
  by_cases hpx : (p : ℤ) ∣ x
  · refine Dvd.dvd.mul_right ?_ _
    exact (pow_dvd_pow_of_dvd hpx j).trans (pow_dvd_pow x hjle)
  · refine Dvd.dvd.mul_left ?_ _
    have hpr : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    have hcop : IsCoprime x (((p ^ j : ℕ) : ℤ)) := by
      have h1 : IsCoprime (p : ℤ) x := (hpr.irreducible.coprime_iff_not_dvd).mpr hpx
      push_cast
      exact (h1.symm.pow_right)
    obtain ⟨c, hc⟩ := Nat.totient_dvd_of_dvd hpj
    have hu := ZMod.pow_totient (ZMod.unitOfIsCoprime x hcop)
    have hx : ((x ^ k.totient - 1 : ℤ) : ZMod (p ^ j)) = 0 := by
      have hx1 : ((x : ZMod (p ^ j))) ^ (p ^ j).totient = 1 := by
        have h2 := congrArg (fun u : (ZMod (p ^ j))ˣ => (u : ZMod (p ^ j))) hu
        simp only [Units.val_pow_eq_pow_val, ZMod.coe_unitOfIsCoprime, Units.val_one] at h2
        exact h2
      push_cast
      rw [hc, pow_mul, hx1, one_pow, sub_self]
    have hne : NeZero (p ^ j) := ⟨pow_ne_zero _ hp.ne_zero⟩
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx
    exact_mod_cast this


theorem checked (k : ℕ) (hk : 0 < k) : ∃ N : ℕ, ∀ n ≥ N, sequence (n + Nat.totient k) ≡ sequence n [ZMOD (k : ℤ)] := by
  refine ⟨k, fun n hn => ?_⟩
  exact (Int.modEq_iff_dvd.mpr (sequence_dvd_sub_of_pow (dvd_pow_add_totient_sub hk fun p => ((Nat.factorization_lt p hk.ne').le).trans hn))).symm

end OMA.S_oeis_a062208

theorem OMA.solution : type_of% @OMA.S_oeis_a062208.main :=
  OMA.S_oeis_a062208.checked
