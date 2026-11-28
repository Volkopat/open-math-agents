import OMAReductions.R_mse_1838931_R1

namespace OMA.Proof_mse_1838931_R1_H1

private lemma factorial_split (q m : ℕ) :
    (q + m).factorial = q.factorial * ∏ j ∈ Finset.Icc 1 m, (q + j) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show q + (m + 1) = (q + m) + 1 by omega, Nat.factorial_succ, ih]
    rw [show Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
    rw [Finset.prod_insert (by simp)]
    ring

private lemma factorial_eq_prod_Icc (m : ℕ) :
    m.factorial = ∏ j ∈ Finset.Icc 1 m, j := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.factorial_succ, ih]
    rw [show Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) by
      ext x; simp only [Finset.mem_Icc, Finset.mem_insert]; omega]
    rw [Finset.prod_insert (by simp)]

private lemma part1 (N : ℕ) :
    ∃ p q : ℕ, N < q ∧ q < p ∧ p.Prime ∧ q.Prime ∧ p ∣ q.factorial + 1 := by
  obtain ⟨q, hqge, hqp⟩ := Nat.exists_infinite_primes (N + 1)
  have hge2 : q.factorial + 1 ≠ 1 := by have := Nat.factorial_pos q; omega
  obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd hge2
  have hqp_lt : q < p := by
    by_contra hle
    have hd1 : p ∣ q.factorial := hpp.dvd_factorial.mpr (by omega)
    have hd2 : p ∣ (q.factorial + 1) - q.factorial := Nat.dvd_sub hpdvd hd1
    rw [Nat.add_sub_cancel_left] at hd2
    exact hpp.not_dvd_one hd2
  exact ⟨p, q, by omega, hqp_lt, hpp, hqp, hpdvd⟩

private lemma part2 (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hq2 : 2 < q)
    (hdvd : p ∣ q.factorial + 1) :
    q < p ∧ 2 < p - q ∧ q ≡ (p - q).factorial [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  have hqp : q < p := by
    by_contra hle
    have hd1 : p ∣ q.factorial := hp.dvd_factorial.mpr (by omega)
    have hd2 : p ∣ (q.factorial + 1) - q.factorial := Nat.dvd_sub hdvd hd1
    rw [Nat.add_sub_cancel_left] at hd2
    exact hp.not_dvd_one hd2
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
  have hpodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  have hqfac_z : (q.factorial : ZMod p) = -1 := by
    have h0 : ((q.factorial + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).mpr hdvd
    push_cast at h0
    linear_combination h0
  have hwilson : ((p - 1).factorial : ZMod p) = -1 := ZMod.wilsons_lemma p
  have hgap : 2 < p - q := by
    by_contra hle
    have heq2 : p - q = 2 := by omega
    have hq_eq : q = p - 2 := by omega
    have hfac : (p - 1).factorial = (p - 1) * q.factorial := by
      have : p - 1 = q + 1 := by omega
      rw [this, Nat.factorial_succ]
    have hz := congrArg (fun x : ℕ => (x : ZMod p)) hfac
    rw [Nat.cast_mul, hwilson, hqfac_z] at hz
    have hp1z : ((p - 1 : ℕ) : ZMod p) = -1 := by
      rw [Nat.cast_sub hp.one_le, ZMod.natCast_self, Nat.cast_one, zero_sub]
    rw [hp1z] at hz
    have h20 : (2 : ZMod p) = 0 := by linear_combination -hz
    have hd2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h20
    exact absurd (Nat.le_of_dvd (by decide) hd2) (by omega)
  refine ⟨hqp, hgap, ?_⟩
  rw [← ZMod.natCast_eq_natCast_iff]
  let m : ℕ := p - 1 - q
  have hpm : p - 1 = q + m := by omega
  have hmodd : Odd m := by rw [Nat.odd_iff]; omega
  have hsplit := factorial_split q m
  rw [← hpm] at hsplit
  have hz : ((p - 1).factorial : ZMod p) =
      (q.factorial : ZMod p) * ∏ j ∈ Finset.Icc 1 m, ((q + j : ℕ) : ZMod p) := by
    rw [hsplit, Nat.cast_mul, Nat.cast_prod]
  have hprod_rev :
      (∏ j ∈ Finset.Icc 1 m, ((q + j : ℕ) : ZMod p)) =
        ∏ t ∈ Finset.Icc 1 m, ((p - t : ℕ) : ZMod p) := by
    refine Finset.prod_bij (fun j _ => p - (q + j)) ?_ ?_ ?_ ?_
    · intro j hj; rw [Finset.mem_Icc] at hj ⊢; omega
    · intro j1 hj1 j2 hj2 heq; rw [Finset.mem_Icc] at hj1 hj2; omega
    · intro t ht
      rw [Finset.mem_Icc] at ht
      exact ⟨p - q - t, Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    · intro j hj
      rw [Finset.mem_Icc] at hj
      congr 1
      omega
  have hprod_neg :
      (∏ t ∈ Finset.Icc 1 m, ((p - t : ℕ) : ZMod p)) =
        (-1 : ZMod p) ^ m * (m.factorial : ZMod p) := by
    have hterm : ∀ t ∈ Finset.Icc 1 m, ((p - t : ℕ) : ZMod p) = (-1 : ZMod p) * (t : ZMod p) := by
      intro t ht
      rw [Finset.mem_Icc] at ht
      rw [Nat.cast_sub (by omega), ZMod.natCast_self, zero_sub, neg_one_mul]
    rw [Finset.prod_congr rfl hterm, Finset.prod_mul_distrib, Finset.prod_const,
      Nat.card_Icc, show m + 1 - 1 = m by omega, ← Nat.cast_prod, ← factorial_eq_prod_Icc]
  rw [hwilson, hqfac_z, hprod_rev, hprod_neg, hmodd.neg_one_pow] at hz
  have hmfac : (m.factorial : ZMod p) = -1 := by linear_combination -hz
  have hpq_fac : (p - q).factorial = (p - q) * m.factorial := by
    have : p - q = m + 1 := by omega
    rw [this, Nat.factorial_succ]
  rw [hpq_fac, Nat.cast_mul, hmfac, Nat.cast_sub hqp.le, ZMod.natCast_self, zero_sub]
  ring

end OMA.Proof_mse_1838931_R1_H1

theorem OMA.solution : OMA.R_mse_1838931_R1.H1 :=
  ⟨OMA.Proof_mse_1838931_R1_H1.part1, OMA.Proof_mse_1838931_R1_H1.part2⟩
