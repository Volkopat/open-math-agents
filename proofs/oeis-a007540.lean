import OMAStatements.S_oeis_a007540
import Mathlib

namespace A007540Proof

private def powerSum (p : ℕ) : ℤ := ∑ k ∈ Finset.Icc 1 (p - 1), (k : ℤ) ^ (p - 1)

/-- A product of factors `1 + P * q k` is `1 + P * (sum of the q k)` modulo `P^2`. -/
private lemma prod_one_add_mul (P : ℤ) (q : ℕ → ℤ) (s : Finset ℕ) :
    P ^ 2 ∣ (∏ k ∈ s, (1 + P * q k)) - (1 + P * ∑ k ∈ s, q k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    obtain ⟨c, hc⟩ := ih
    refine ⟨(1 + P * q a) * c + q a * ∑ k ∈ s, q k, ?_⟩
    have h : ∏ k ∈ s, (1 + P * q k) = (1 + P * ∑ k ∈ s, q k) + P ^ 2 * c := by linarith
    rw [h]
    ring

/-- `(u - 1)^n = (-1)^n * (1 - n*u)` modulo `u^2`. -/
private lemma sub_one_pow_modsq (u : ℤ) (n : ℕ) :
    u ^ 2 ∣ (u - 1) ^ n - (-1) ^ n * (1 - (n : ℤ) * u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, hc⟩ := ih
    refine ⟨c * (u - 1) - (-1) ^ n * (n : ℤ), ?_⟩
    have h : (u - 1) ^ n = (-1) ^ n * (1 - (n : ℤ) * u) + u ^ 2 * c := by linarith
    rw [pow_succ, h, pow_succ]
    push_cast
    ring

/-- Fermat: `p ∣ k^(p-1) - 1` for `1 ≤ k < p`. -/
private lemma fermat_dvd {p k : ℕ} (hp : p.Prime) (hk1 : 1 ≤ k) (hkp : k < p) :
    (p : ℤ) ∣ (k : ℤ) ^ (p - 1) - 1 := by
  have hc : IsCoprime (k : ℤ) (p : ℤ) := by
    rw [Nat.isCoprime_iff_coprime]
    exact (Nat.coprime_of_lt_prime (by omega) hkp hp).symm
  have h := Int.ModEq.pow_card_sub_one_eq_one hp hc
  exact Int.modEq_iff_dvd.mp h.symm

/-- Wilson: `p ∣ (p-1)! + 1`. -/
private lemma wilson_dvd {p : ℕ} (hp : p.Prime) :
    (p : ℤ) ∣ ((p - 1).factorial : ℤ) + 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have h : ((((p - 1).factorial : ℤ) + 1 : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [ZMod.wilsons_lemma]
    ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h

/-- `1 * 2 * ... * n = n!` in the integers. -/
private lemma prod_Icc_cast_factorial (n : ℕ) :
    ∏ k ∈ Finset.Icc 1 n, (k : ℤ) = (n.factorial : ℤ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega), ih, Nat.factorial_succ]
    push_cast
    ring

/-- Lerch's congruence in the form needed here: for an odd prime `p`,
`1^(p-1) + ... + (p-1)^(p-1) - (p-1) = (p-1)! + 1` modulo `p^2`. -/
private lemma key {p : ℕ} (hp : p.Prime) (hodd : Odd p) :
    ((p : ℤ) ^ 2) ∣ (powerSum p - ((p : ℤ) - 1)) - (((p - 1).factorial : ℤ) + 1) := by
  set W : ℤ := ((p - 1).factorial : ℤ) with hW
  have hq : ∀ k ∈ Finset.Icc 1 (p - 1),
      (k : ℤ) ^ (p - 1) = 1 + (p : ℤ) * (((k : ℤ) ^ (p - 1) - 1) / (p : ℤ)) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hd := fermat_dvd hp hk.1 (by have := hp.pos; omega)
    have h := Int.mul_ediv_cancel' hd
    linarith
  have hcast : ((p - 1 : ℕ) : ℤ) = (p : ℤ) - 1 := Nat.cast_pred hp.pos
  have hsum : powerSum p = ((p : ℤ) - 1) +
      (p : ℤ) * ∑ k ∈ Finset.Icc 1 (p - 1), (((k : ℤ) ^ (p - 1) - 1) / (p : ℤ)) := by
    unfold powerSum
    rw [Finset.sum_congr rfl hq, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const,
      Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul, hcast, mul_one]
  have hprod : ∏ k ∈ Finset.Icc 1 (p - 1),
      (1 + (p : ℤ) * (((k : ℤ) ^ (p - 1) - 1) / (p : ℤ))) = W ^ (p - 1) := by
    rw [← Finset.prod_congr rfl hq, Finset.prod_pow, prod_Icc_cast_factorial]
  have h1 : (p : ℤ) ^ 2 ∣
      (∏ k ∈ Finset.Icc 1 (p - 1), (1 + (p : ℤ) * (((k : ℤ) ^ (p - 1) - 1) / (p : ℤ)))) -
        (1 + (p : ℤ) * ∑ k ∈ Finset.Icc 1 (p - 1), (((k : ℤ) ^ (p - 1) - 1) / (p : ℤ))) :=
    prod_one_add_mul (p : ℤ) (fun k => ((k : ℤ) ^ (p - 1) - 1) / (p : ℤ))
      (Finset.Icc 1 (p - 1))
  rw [hprod] at h1
  have hw : (p : ℤ) ∣ W + 1 := wilson_dvd hp
  have h5 := sub_one_pow_modsq (W + 1) (p - 1)
  have heven : Even (p - 1) := by
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m, by omega⟩
  rw [heven.neg_one_pow, add_sub_cancel_right, one_mul, hcast] at h5
  have h5' : (p : ℤ) ^ 2 ∣ W ^ (p - 1) - (1 - ((p : ℤ) - 1) * (W + 1)) :=
    (pow_dvd_pow_of_dvd hw 2).trans h5
  obtain ⟨c, hc⟩ := hw
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h5'
  refine ⟨b - a - c, ?_⟩
  rw [hsum]
  linear_combination -ha + hb - (p : ℤ) * hc

private lemma Ico_eq {p : ℕ} (hp : p.Prime) :
    (∑ k ∈ Finset.Ico 1 p, (k : ℤ) ^ (p - 1)) = powerSum p := by
  unfold powerSum
  have h : Finset.Ico 1 p = Finset.Icc 1 (p - 1) := by
    ext k
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    have := hp.pos
    omega
  rw [h]

end A007540Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a007540.main := by
  intro p hp h2
  have hodd : Odd p := hp.odd_of_ne_two h2
  have hk := A007540Proof.key hp hodd
  rw [A007540Proof.Ico_eq hp, Int.modEq_comm, Int.modEq_iff_dvd, Int.modEq_comm,
    Int.modEq_iff_dvd]
  have e1 : (((p - 1).factorial : ℤ) - -1) = ((p - 1).factorial : ℤ) + 1 := by ring
  rw [e1]
  exact (dvd_iff_dvd_of_dvd_sub hk).symm
