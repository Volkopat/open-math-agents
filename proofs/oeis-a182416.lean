import OMAStatements.S_oeis_a182416
import Mathlib

/-! Following @justusklocke-cloud (#12940), retain the Fermat and Chinese-remainder
argument and the k = 2 witness. Split coprimality with each product using the
standard product-coprimality equivalence. -/

namespace A182416Proof
open OMA.S_oeis_a182416

lemma fermat (π a M : ℕ) (hπ : π.Prime) (ha : a.Coprime π) (hdiv : (π - 1) ∣ M) :
    a ^ M ≡ 1 [MOD π] := by
  obtain ⟨c, rfl⟩ := hdiv
  simpa [pow_mul] using (Nat.ModEq.pow_card_sub_one_eq_one hπ ha).pow c

lemma first (k : ℕ) (hk : AllPrime k) : Carmichael (N k) := by
  obtain ⟨hp, hq, hr⟩ := hk
  have hN : N k = p k * q k * r k := rfl
  have hp13 : 13 ≤ p k := by unfold p; omega
  have hq37 : 37 ≤ q k := by unfold q; omega
  have hr61 : 61 ≤ r k := by unfold r; omega
  have hp1 : p k - 1 = 60*k+12 := by unfold p; omega
  have hq1 : q k - 1 = 180*k+36 := by unfold q; omega
  have hr1 : r k - 1 = 300*k+60 := by unfold r; omega
  have eN : N k = 180*(5*k+1)*(3600*k^2+1532*k+163) + 1 := by unfold N p q r; ring
  have hNm : N k - 1 = 180*(5*k+1)*(3600*k^2+1532*k+163) := by
    rw [eN, Nat.add_sub_cancel]
  have dp : (p k - 1) ∣ (N k - 1) := by
    rw [hp1, hNm]; exact ⟨15*(3600*k^2+1532*k+163), by ring⟩
  have dq : (q k - 1) ∣ (N k - 1) := by
    rw [hq1, hNm]; exact ⟨5*(3600*k^2+1532*k+163), by ring⟩
  have dr : (r k - 1) ∣ (N k - 1) := by
    rw [hr1, hNm]; exact ⟨3*(3600*k^2+1532*k+163), by ring⟩
  have cpq : (p k).Coprime (q k) := (Nat.coprime_primes hp hq).mpr (by unfold p q; omega)
  have cpr : (p k).Coprime (r k) := (Nat.coprime_primes hp hr).mpr (by unfold p r; omega)
  have cqr : (q k).Coprime (r k) := (Nat.coprime_primes hq hr).mpr (by unfold q r; omega)
  have hpq : 13 * 37 ≤ p k * q k := Nat.mul_le_mul hp13 hq37
  refine ⟨?_, ?_, ?_⟩
  · have h3 : 13 * 37 * 61 ≤ p k * q k * r k := Nat.mul_le_mul hpq hr61
    rw [hN]
    omega
  · rw [hN]
    exact Nat.not_prime_mul (by omega) (by omega)
  · intro a ha
    rw [hN] at ha
    simp only [Nat.coprime_mul_iff_right] at ha
    rcases ha with ⟨⟨hap, haq⟩, har⟩
    have e1 := fermat (p k) a (N k - 1) hp hap dp
    have e2 := fermat (q k) a (N k - 1) hq haq dq
    have e3 := fermat (r k) a (N k - 1) hr har dr
    have e12 := (Nat.modEq_and_modEq_iff_modEq_mul cpq).mp ⟨e1, e2⟩
    have c12r : (p k * q k).Coprime (r k) := Nat.Coprime.mul_left cpr cqr
    have e123 := (Nat.modEq_and_modEq_iff_modEq_mul c12r).mp ⟨e12, e3⟩
    rw [hN]
    exact e123

lemma N_two : N 2 = 7 * 19 * 397 * 661 := by norm_num [N, p, q, r]

lemma second : Carmichael (N 2) := by
  have hN := N_two
  have h7 : Nat.Prime 7 := by norm_num
  have h19 : Nat.Prime 19 := by norm_num
  have h397 : Nat.Prime 397 := by norm_num
  have h661 : Nat.Prime 661 := by norm_num
  have hNm : N 2 - 1 = 34901460 := by rw [hN]
  refine ⟨?_, ?_, ?_⟩
  · rw [hN]; norm_num
  · rw [hN]
    exact Nat.not_prime_mul (by norm_num) (by norm_num)
  · intro a ha
    rw [hN] at ha
    simp only [Nat.coprime_mul_iff_right] at ha
    rcases ha with ⟨⟨⟨ha7, ha19⟩, ha397⟩, ha661⟩
    rw [hNm]
    have e1 := fermat 7 a 34901460 h7 ha7 (by norm_num)
    have e2 := fermat 19 a 34901460 h19 ha19 (by norm_num)
    have e3 := fermat 397 a 34901460 h397 ha397 (by norm_num)
    have e4 := fermat 661 a 34901460 h661 ha661 (by norm_num)
    have c1 : Nat.Coprime 7 19 := by norm_num
    have c2 : Nat.Coprime (7 * 19) 397 := by norm_num
    have c3 : Nat.Coprime (7 * 19 * 397) 661 := by norm_num
    have e12 := (Nat.modEq_and_modEq_iff_modEq_mul c1).mp ⟨e1, e2⟩
    have e123 := (Nat.modEq_and_modEq_iff_modEq_mul c2).mp ⟨e12, e3⟩
    have e1234 := (Nat.modEq_and_modEq_iff_modEq_mul c3).mp ⟨e123, e4⟩
    rw [hN]
    exact e1234

end A182416Proof

open OMA.S_oeis_a182416 A182416Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a182416.main := by
  refine ⟨first, 2, second, ?_⟩
  rintro ⟨h, -, -⟩
  have h133 : p 2 = 7 * 19 := by norm_num [p]
  rw [h133] at h
  exact Nat.not_prime_mul (by norm_num) (by norm_num) h
