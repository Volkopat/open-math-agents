import OMAReductions.R_oeis_a284760_R1_H4_R1

/-!
# Odd power sums at primes

Reflection over the interval from 1 to p − 1 gives the second-order
binomial congruence. The term of order p² contains an odd power sum,
which itself vanishes modulo p by reflection.
-/

namespace OMA.Oeis284760Prime

open Finset

private def powerSum (p e : ℕ) : ℤ :=
  ∑ i ∈ Ico 1 p, (i : ℤ) ^ e

private theorem powerSum_eq_cast (p e : ℕ) :
    powerSum p e = ((∑ i ∈ Ico 1 p, i ^ e : ℕ) : ℤ) := by
  simp only [powerSum, Nat.cast_sum, Nat.cast_pow]

private theorem reflected_sum (p e : ℕ) :
    (∑ i ∈ Ico 1 p, ((p - i : ℕ) : ℤ) ^ e) = powerSum p e := by
  unfold powerSum
  have closed (i : ℕ) (hi : i ∈ Ico 1 p) : p - i ∈ Ico 1 p := by
    rw [mem_Ico] at hi ⊢
    omega
  have invol (i : ℕ) (hi : i ∈ Ico 1 p) : p - (p - i) = i := by
    rw [mem_Ico] at hi
    omega
  exact sum_nbij' (p - ·) (p - ·) closed closed invol invol (fun _ _ => rfl)

private theorem binomial_mod_cube (p x : ℤ) (e : ℕ) (he : 2 ≤ e) :
    p ^ 3 ∣ (p + x) ^ e - (x ^ e + (e : ℤ) * p * x ^ (e - 1) +
      (e.choose 2 : ℤ) * p ^ 2 * x ^ (e - 2)) := by
  rw [add_pow, show e + 1 = 3 + (e - 2) by omega, sum_range_add]
  have hfirst : (∑ j ∈ range 3, p ^ j * x ^ (e - j) * (e.choose j : ℤ)) =
      x ^ e + (e : ℤ) * p * x ^ (e - 1) + (e.choose 2 : ℤ) * p ^ 2 * x ^ (e - 2) := by
    norm_num [sum_range_succ, Nat.choose_one_right]
    ring
  rw [hfirst, add_sub_cancel_left]
  apply dvd_sum
  intro j _
  rw [pow_add, mul_assoc, mul_assoc]
  exact dvd_mul_right _ _

private theorem odd_sum_dvd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {e : ℕ}
    (he : Odd e) : (p : ℤ) ∣ powerSum p e := by
  have term (i : ℕ) (hi : i ∈ Ico 1 p) :
      (p : ℤ) ∣ ((p - i : ℕ) : ℤ) ^ e + (i : ℤ) ^ e := by
    have hip := (mem_Ico.mp hi).2.le
    have h := sub_dvd_pow_sub_pow ((p : ℤ) - i) (-(i : ℤ)) e
    rw [show (p : ℤ) - i - (- ↑i) = p by ring, he.neg_pow, sub_neg_eq_add] at h
    simpa only [Nat.cast_sub hip] using h
  have h := dvd_sum term
  rw [sum_add_distrib, reflected_sum] at h
  change (p : ℤ) ∣ powerSum p e + powerSum p e at h
  rw [← two_mul, powerSum_eq_cast] at h
  have hnat : p ∣ 2 * ∑ i ∈ Ico 1 p, i ^ e := by exact_mod_cast h
  have hc : p.Coprime 2 := hp.coprime_iff_not_dvd.mpr fun hd =>
    hp2 (le_antisymm (Nat.le_of_dvd (by decide) hd) hp.two_le)
  rw [powerSum_eq_cast]
  exact_mod_cast hc.dvd_of_dvd_mul_left hnat

private theorem reflected_congruence {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {e : ℕ} (he : 3 ≤ e) (ho : Odd e) :
    (p : ℤ) ^ 3 ∣ 2 * powerSum p e - (e : ℤ) * p * powerSum p (e - 1) := by
  have heven : Even (e - 1) := by
    obtain ⟨k, hk⟩ := ho
    exact ⟨k, by omega⟩
  have hodd : Odd (e - 2) := by
    obtain ⟨k, hk⟩ := ho
    exact ⟨k - 1, by omega⟩
  have term (i : ℕ) (hi : i ∈ Ico 1 p) :
      (p : ℤ) ^ 3 ∣ ((p - i : ℕ) : ℤ) ^ e + (i : ℤ) ^ e -
        (e : ℤ) * p * (i : ℤ) ^ (e - 1) +
        (e.choose 2 : ℤ) * (p : ℤ) ^ 2 * (i : ℤ) ^ (e - 2) := by
    have h := binomial_mod_cube (p : ℤ) (-(i : ℤ)) e (by omega)
    rw [ho.neg_pow, heven.neg_pow, hodd.neg_pow, ← sub_eq_add_neg,
      ← Nat.cast_sub (mem_Ico.mp hi).2.le] at h
    convert h using 1
    ring
  have h := dvd_sum term
  simp only [sum_add_distrib, sum_sub_distrib, reflected_sum, ← mul_sum] at h
  change (p : ℤ) ^ 3 ∣ powerSum p e + powerSum p e -
    (e : ℤ) * p * powerSum p (e - 1) +
    (e.choose 2 : ℤ) * (p : ℤ) ^ 2 * powerSum p (e - 2) at h
  obtain ⟨k, hk⟩ := odd_sum_dvd hp hp2 hodd
  have htail : (p : ℤ) ^ 3 ∣ (e.choose 2 : ℤ) * (p : ℤ) ^ 2 * powerSum p (e - 2) := by
    refine ⟨(e.choose 2 : ℤ) * k, ?_⟩
    rw [hk]
    ring
  have hdiff := dvd_sub h htail
  rwa [add_sub_cancel_right, ← two_mul] at hdiff

private theorem not_dvd_power_sum {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : ¬ p ^ 2 ∣ ∑ i ∈ Ico 1 p, i ^ (p - 3)) :
    ¬ p ^ 3 ∣ ∑ i ∈ Ico 1 p, i ^ (p - 2) := by
  intro hsum
  have hp2 : p ≠ 2 := by omega
  have hodd : Odd (p - 2) := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    exact ⟨k - 1, by omega⟩
  have htotal : (p : ℤ) ^ 3 ∣ 2 * powerSum p (p - 2) := by
    apply dvd_mul_of_dvd_right
    rw [powerSum_eq_cast]
    exact_mod_cast hsum
  have hcon := reflected_congruence hp hp2 (by omega) hodd
  rw [show p - 2 - 1 = p - 3 by omega] at hcon
  have htarget : (p : ℤ) ^ 3 ∣ ((p - 2 : ℕ) : ℤ) * p * powerSum p (p - 3) := by
    have hdiff := dvd_sub htotal hcon
    rwa [sub_sub_cancel] at hdiff
  rw [powerSum_eq_cast] at htarget
  have hnatural : p ^ 3 ∣ (p - 2) * p * ∑ i ∈ Ico 1 p, i ^ (p - 3) := by
    exact_mod_cast htarget
  have hcancel : p ^ 2 ∣ (p - 2) * ∑ i ∈ Ico 1 p, i ^ (p - 3) := by
    apply Nat.dvd_of_mul_dvd_mul_left hp.pos
    simpa only [← pow_succ', ← mul_assoc, mul_comm p (p - 2)] using hnatural
  have hcop : p.Coprime (p - 2) := hp.coprime_iff_not_dvd.mpr fun hd =>
    (not_le_of_gt (show p - 2 < p by omega)) (Nat.le_of_dvd (by omega) hd)
  exact h ((hcop.pow_left 2).dvd_of_dvd_mul_left hcancel)

end OMA.Oeis284760Prime

theorem OMA.solution : OMA.R_oeis_a284760_R1_H4_R1.H1 := by
  intro p hp hp5 h hmod
  exact OMA.Oeis284760Prime.not_dvd_power_sum hp hp5 h
    ((pow_dvd_pow p (by decide : 3 ≤ 4)).trans (Nat.dvd_of_mod_eq_zero hmod))
