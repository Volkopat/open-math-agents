import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1

-- Reduction Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1.H3.R1
-- Credit: @adammcarter
-- Splits step H3 of Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H3.R1 (3 divides n exactly once, a even,
-- exactly one odd prime q = 2 mod 3 has odd exponent; at least two repeated odd primes, S not
-- admissible) by whether q is simple, with new proved conditions built in.  Proving H1 and H2
-- proves the step.
--
-- Notation: n unitary perfect, a = padicValNat 2 n, e(p) = n.factorization p, S = the repeated odd
-- primes, q the unique odd prime = 2 mod 3 with odd exponent (the only source of 3 in the balance
-- product of the factors 1 + p^e(p), which equals 2n).
--
-- PROVED BELOW (any S):
--   (1) fermat_src: every prime c = 2 mod 3 dividing 2^a + 1 is q or a repeated prime; such a c
--       exists (2^a + 1 = 2 mod 3); 17 (a = 4 mod 8) and 65537 (a = 16 mod 32) are 8 mod 9, so
--       they are never q and are repeated.
--   (2) div_src: every prime d = 2 mod 3 dividing e(q) gives a repeated r = 2 mod 3, r != q, with
--       r | 1 + q^d  ((1 + q^d)/(q + 1) is d mod 3).  This extends the parent clause for
--       e(q) = 5 mod 6 to e.g. e(q) = 25, 55, 85.
--   (3) parity: n has an even number of distinct prime factors exactly when 1 + q^e(q) = 3 mod 9
--       (cancel the single 3 in the balance equation and reduce mod 3).
--   (4) source_of_repeated: every repeated odd prime z has z^2 | 2^a + 1 or a source 1 + p^e(p)
--       with p odd, p != z.
--
-- H1 (OPEN): q is simple (e(q) = 1), with (1), (3), (4).  This is the case of 60, 87360 and
--    Wall's number, which have only one repeated odd prime and so are not in the family.
-- H2 (OPEN): q is repeated (e(q) >= 5, odd, not divisible by 3), with (1) to (4).
-- No closure contradiction is reachable without fixing S: every forced prime = 2 mod 3 other
-- than q can be repeated, and every forced prime = 1 mod 3 can be simple or repeated.

namespace OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H3_R1

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (prod_eq_two_mul prod_primeFactors_pow_self
  two_dvd_of_isUnitaryPerfect exists_quot_mod one_add_pow_dvd_of_odd_mul)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1 (exists_prime_mod3)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1 (fact2_eq fact_pos cop2 dvd_of_dvd_two_mul
  dvd_two_mul_of_src le_fact_of_sq pmod_two_even pmod_two_odd pmod_one)

-- H1: q simple.
def H1 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    n.factorization 3 = 1 → padicValNat 2 n % 2 = 0 →
    (∃ q ∈ n.primeFactors, q % 3 = 2 ∧ q % 9 ≠ 8 ∧ n.factorization q = 1 ∧
      (∀ q' ∈ n.primeFactors, q' % 3 = 2 → n.factorization q' % 2 = 1 → q' = q) ∧
      (∃ c, c.Prime ∧ c % 3 = 2 ∧ c ∣ 2 ^ padicValNat 2 n + 1 ∧ (c = q ∨ c ∈ S)) ∧
      (∀ c, c.Prime → c % 3 = 2 → c ∣ 2 ^ padicValNat 2 n + 1 → c = q ∨ c ∈ S) ∧
      (padicValNat 2 n % 8 = 4 → 17 ∈ S) ∧ (padicValNat 2 n % 32 = 16 → 65537 ∈ S) ∧
      (n.primeFactors.card % 2 = 0 ↔ (1 + q ^ n.factorization q) % 9 = 3)) →
    (∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ p ∈ n.primeFactors, p ≠ 2 ∧ p ≠ z ∧ z ∣ 1 + p ^ n.factorization p) →
    padicValNat 2 n ≤ A

-- H2: q repeated, e(q) >= 5.
def H2 : Prop :=
  ∃ A : ℕ, ∀ n : ℕ, Erdos1052.IsUnitaryPerfect n →
    ∀ S : Finset ℕ, (∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) → 2 ≤ S.card →
    ¬ ((∀ z ∈ S, 128 ≤ z ∧ S.card + 3 ≤ z) ∧
      ∏ z ∈ S, (((z : ℚ) + 1) / ((z : ℚ) - 2 - (S.card : ℚ))) ≤ 2101 / 2097) →
    n.factorization 3 = 1 → padicValNat 2 n % 2 = 0 →
    (∃ q ∈ n.primeFactors, q % 3 = 2 ∧ n.factorization q % 2 = 1 ∧ q % 9 ≠ 8 ∧
      n.factorization q % 3 ≠ 0 ∧ 5 ≤ n.factorization q ∧
      (n.factorization q % 6 = 5 → ∃ r ∈ S, r ≠ q ∧ r % 3 = 2 ∧ r ∣ 1 + q ^ n.factorization q) ∧
      (∀ d : ℕ, d.Prime → d ∣ n.factorization q → d % 3 = 2 →
        ∃ r ∈ S, r ≠ q ∧ r % 3 = 2 ∧ r ∣ 1 + q ^ d) ∧
      (∀ q' ∈ n.primeFactors, q' % 3 = 2 → n.factorization q' % 2 = 1 → q' = q) ∧
      (∃ c, c.Prime ∧ c % 3 = 2 ∧ c ∣ 2 ^ padicValNat 2 n + 1 ∧ (c = q ∨ c ∈ S)) ∧
      (∀ c, c.Prime → c % 3 = 2 → c ∣ 2 ^ padicValNat 2 n + 1 → c = q ∨ c ∈ S) ∧
      (padicValNat 2 n % 8 = 4 → 17 ∈ S) ∧ (padicValNat 2 n % 32 = 16 → 65537 ∈ S) ∧
      (n.primeFactors.card % 2 = 0 ↔ (1 + q ^ n.factorization q) % 9 = 3)) →
    (∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ p ∈ n.primeFactors, p ≠ 2 ∧ p ≠ z ∧ z ∣ 1 + p ^ n.factorization p) →
    padicValNat 2 n ≤ A

-- Section 1. Repeated primes from the factor 1 + 2^a.

theorem mem_S_of {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) {q c : ℕ}
    (huniq : ∀ q' ∈ n.primeFactors, q' % 3 = 2 → n.factorization q' % 2 = 1 → q' = q)
    (hc : c.Prime) (hc2 : c ≠ 2) (hc3 : c % 3 = 2) (hcq : c ≠ q) (hcn : c ∣ n) : c ∈ S := by
  have hn : n ≠ 0 := h.2.ne'
  have hcpf : c ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hc, hcn, hn⟩
  have h1 := fact_pos hcpf
  have hev : n.factorization c % 2 = 0 := by
    by_contra ho
    exact hcq (huniq c hcpf hc3 (by omega))
  exact (hS c).mpr ⟨hc, hc2, (hc.pow_dvd_iff_le_factorization hn).mpr (by omega)⟩

theorem fermat_src {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) {q : ℕ}
    (huniq : ∀ q' ∈ n.primeFactors, q' % 3 = 2 → n.factorization q' % 2 = 1 → q' = q)
    {c : ℕ} (hc : c.Prime) (hc3 : c % 3 = 2) (hcd : c ∣ 2 ^ padicValNat 2 n + 1) :
    c = q ∨ c ∈ S := by
  have hn : n ≠ 0 := h.2.ne'
  have h2pf : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, two_dvd_of_isUnitaryPerfect h, hn⟩
  have ha1 := fact_pos h2pf
  rw [← fact2_eq n] at hcd
  have hc2 : c ≠ 2 := by
    rintro rfl
    have h2d : 2 ∣ 2 ^ n.factorization 2 := dvd_pow_self 2 (by omega)
    have : 2 ∣ 1 := (Nat.dvd_add_right h2d).mp hcd
    omega
  have hcn : c ∣ n := dvd_of_dvd_two_mul (cop2 hc hc2)
    (dvd_two_mul_of_src h h2pf (by rw [add_comm]; exact hcd))
  by_cases hcq : c = q
  · exact Or.inl hcq
  · exact Or.inr (mem_S_of h hS huniq hc hc2 hc3 hcq hcn)

theorem fermat_exists {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (ha : padicValNat 2 n % 2 = 0) :
    ∃ c, c.Prime ∧ c % 3 = 2 ∧ c ∣ 2 ^ padicValNat 2 n + 1 := by
  have h2m : (2 ^ padicValNat 2 n + 1) % 3 = 2 := by
    have := pmod_two_even (q := 2) (e := padicValNat 2 n) (by norm_num) ha
    omega
  obtain ⟨c, hc, hcd, hc3⟩ := exists_prime_mod3 _ h2m
  exact ⟨c, hc, hc3, hcd⟩

-- Section 2. Prime divisors of e(q).

theorem q_ne_two {n q : ℕ} (ha : padicValNat 2 n % 2 = 0) (hqo : n.factorization q % 2 = 1) :
    q ≠ 2 := by
  rintro rfl
  rw [fact2_eq n] at hqo
  omega

theorem div_src {n : ℕ} {S : Finset ℕ} (h : Erdos1052.IsUnitaryPerfect n)
    (hS : ∀ p, p ∈ S ↔ p.Prime ∧ p ≠ 2 ∧ p ^ 2 ∣ n) (ha : padicValNat 2 n % 2 = 0)
    {q : ℕ} (hq : q ∈ n.primeFactors) (hq3 : q % 3 = 2) (hqo : n.factorization q % 2 = 1)
    (huniq : ∀ q' ∈ n.primeFactors, q' % 3 = 2 → n.factorization q' % 2 = 1 → q' = q)
    {d : ℕ} (hd : d.Prime) (hdm : d ∣ n.factorization q) (hd3 : d % 3 = 2) :
    ∃ r ∈ S, r ≠ q ∧ r % 3 = 2 ∧ r ∣ 1 + q ^ d := by
  have hn : n ≠ 0 := h.2.ne'
  have hqp := Nat.prime_of_mem_primeFactors hq
  have hq2 := q_ne_two ha hqo
  have hqodd : q % 2 = 1 := Nat.odd_iff.mp (hqp.eq_two_or_odd'.resolve_left hq2)
  obtain ⟨k, hk⟩ := hdm
  have hkodd : k % 2 = 1 := by
    have : Odd (d * k) := hk ▸ Nat.odd_iff.mpr hqo
    exact Nat.odd_iff.mp (Nat.odd_mul.mp this).2
  have hdodd : d % 2 = 1 := by
    have : Odd (d * k) := hk ▸ Nat.odd_iff.mpr hqo
    exact Nat.odd_iff.mp (Nat.odd_mul.mp this).1
  have hmod : n.factorization q % (2 * d) = d := by
    obtain ⟨j, rfl⟩ : ∃ j, k = 2 * j + 1 := ⟨k / 2, by omega⟩
    have hd1 := hd.two_le
    rw [hk, show d * (2 * j + 1) = d + 2 * d * j by ring, Nat.add_mul_mod_self_left,
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨Q, hQ, hQm⟩ := exists_quot_mod (z := q) (e := d) (Nat.odd_iff.mpr hdodd)
  have hQ3 : Q % 3 = 2 := by
    have := Nat.ModEq.of_dvd (by omega : 3 ∣ q + 1) hQm
    unfold Nat.ModEq at this
    omega
  have hQ2 : Q % 2 = 1 := by
    have := Nat.ModEq.of_dvd (by omega : 2 ∣ q + 1) hQm
    unfold Nat.ModEq at this
    omega
  obtain ⟨r, hr, hrQ, hr3⟩ := exists_prime_mod3 Q hQ3
  have hrd : r ∣ 1 + q ^ d := by
    rw [hQ]
    exact Dvd.dvd.mul_left hrQ _
  have hr2 : r ≠ 2 := by
    rintro rfl
    omega
  have hrq : r ≠ q := by
    intro hrq
    have h1 : q ∣ q ^ d := dvd_pow_self q hd.ne_zero
    have h1' : q ∣ 1 + q ^ d := hrq ▸ hrd
    have : q ∣ 1 := (Nat.dvd_add_right h1).mp (by rw [add_comm]; exact h1')
    exact hqp.one_lt.ne' (Nat.dvd_one.mp this)
  have hrn : r ∣ n := dvd_of_dvd_two_mul (cop2 hr hr2)
    (dvd_two_mul_of_src h hq (hrd.trans (one_add_pow_dvd_of_odd_mul hmod)))
  exact ⟨r, mem_S_of h hS huniq hr hr2 hr3 hrq hrn, hrq, hr3, hrd⟩

-- Section 3. Parity of the number of prime factors.

theorem parity {n : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (h3 : n.factorization 3 = 1)
    (ha : padicValNat 2 n % 2 = 0) {q : ℕ} (hq : q ∈ n.primeFactors) (hq3 : q % 3 = 2)
    (hqo : n.factorization q % 2 = 1)
    (huniq : ∀ q' ∈ n.primeFactors, q' % 3 = 2 → n.factorization q' % 2 = 1 → q' = q) :
    (n.primeFactors.card % 2 = 0 ↔ (1 + q ^ n.factorization q) % 9 = 3) := by
  have hn : n ≠ 0 := h.2.ne'
  have h2pf : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, two_dvd_of_isUnitaryPerfect h, hn⟩
  have h3pf : 3 ∈ n.primeFactors := by
    rw [← Nat.support_factorization]
    exact Finsupp.mem_support_iff.mpr (by omega)
  have hq2 := q_ne_two ha hqo
  have hqne3 : q ≠ 3 := by
    rintro rfl
    norm_num at hq3
  have h3e : 3 ∈ n.primeFactors.erase 2 := Finset.mem_erase.mpr ⟨by norm_num, h3pf⟩
  have hqe : q ∈ (n.primeFactors.erase 2).erase 3 :=
    Finset.mem_erase.mpr ⟨hqne3, Finset.mem_erase.mpr ⟨hq2, hq⟩⟩
  set R := ((n.primeFactors.erase 2).erase 3).erase q with hR
  have hRmem : ∀ r ∈ R, r ∈ n.primeFactors ∧ r ≠ 2 ∧ r ≠ 3 ∧ r ≠ q := by
    intro r hr
    have h1 := Finset.mem_erase.mp hr
    have h2 := Finset.mem_erase.mp h1.2
    have h3' := Finset.mem_erase.mp h2.2
    exact ⟨h3'.2, h3'.1, h2.1, h1.1⟩
  have hpow : ∀ r ∈ R, r ^ n.factorization r % 3 = 1 := by
    intro r hr
    obtain ⟨hrpf, _, hr3, hrq⟩ := hRmem r hr
    have hrp := Nat.prime_of_mem_primeFactors hrpf
    have h0 : r % 3 ≠ 0 := fun h0 =>
      hr3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hrp).mp (Nat.dvd_of_mod_eq_zero h0)).symm
    rcases (by omega : r % 3 = 1 ∨ r % 3 = 2) with h1 | h2
    · exact pmod_one h1
    · have : n.factorization r % 2 = 0 := by
        by_contra ho
        exact hrq (huniq r hrpf h2 (by omega))
      exact pmod_two_even h2 this
  have hE := prod_eq_two_mul h
  have hN := prod_primeFactors_pow_self hn
  rw [← Finset.mul_prod_erase _ _ h2pf, ← Finset.mul_prod_erase _ _ h3e,
    ← Finset.mul_prod_erase _ _ hqe] at hE hN
  rw [← hR] at hE hN
  rw [h3, fact2_eq n] at hE hN
  have hq3d : 3 ∣ 1 + q ^ n.factorization q := by
    have := pmod_two_odd (e := n.factorization q) hq3 hqo
    omega
  obtain ⟨Q, hQ⟩ := hq3d
  have key : (1 + 2 ^ padicValNat 2 n) * 4 * Q * ∏ r ∈ R, (1 + r ^ n.factorization r) =
      2 * 2 ^ padicValNat 2 n * q ^ n.factorization q * ∏ r ∈ R, r ^ n.factorization r := by
    apply Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3)
    calc 3 * ((1 + 2 ^ padicValNat 2 n) * 4 * Q * ∏ r ∈ R, (1 + r ^ n.factorization r))
        = (1 + 2 ^ padicValNat 2 n) * ((1 + 3 ^ 1) * ((1 + q ^ n.factorization q) *
            ∏ r ∈ R, (1 + r ^ n.factorization r))) := by rw [hQ]; ring
      _ = 2 * n := hE
      _ = 2 * (2 ^ padicValNat 2 n * (3 ^ 1 * (q ^ n.factorization q * ∏ r ∈ R, r ^ n.factorization r))) := by
          rw [hN]
      _ = 3 * (2 * 2 ^ padicValNat 2 n * q ^ n.factorization q * ∏ r ∈ R, r ^ n.factorization r) := by
          ring
  have hY : (∏ r ∈ R, (1 + r ^ n.factorization r)) % 3 = 2 ^ R.card % 3 := by
    rw [Finset.prod_nat_mod, Finset.prod_congr rfl (fun r hr => by
      have := hpow r hr
      show (1 + r ^ n.factorization r) % 3 = 2
      omega), Finset.prod_const]
  have hZ : (∏ r ∈ R, r ^ n.factorization r) % 3 = 1 := by
    rw [Finset.prod_nat_mod, Finset.prod_congr rfl (fun r hr => hpow r hr), Finset.prod_const_one]
    norm_num
  have hA : (1 + 2 ^ padicValNat 2 n) % 3 = 2 := by
    have := pmod_two_even (q := 2) (e := padicValNat 2 n) (by norm_num) ha
    omega
  have hB : 2 ^ padicValNat 2 n % 3 = 1 := pmod_two_even (q := 2) (by norm_num) ha
  have hC : q ^ n.factorization q % 3 = 2 := pmod_two_odd hq3 hqo
  have e1 : (1 + 2 ^ padicValNat 2 n) * 4 * Q * ∏ r ∈ R, (1 + r ^ n.factorization r) ≡
      2 * 1 * Q * 2 ^ R.card [MOD 3] :=
    (((show (1 + 2 ^ padicValNat 2 n) ≡ 2 [MOD 3] from hA).mul
      (show 4 ≡ 1 [MOD 3] from rfl)).mul (Nat.ModEq.refl Q)).mul hY
  have e2 : 2 * 2 ^ padicValNat 2 n * q ^ n.factorization q * ∏ r ∈ R, r ^ n.factorization r ≡
      2 * 1 * 2 * 1 [MOD 3] :=
    (((Nat.ModEq.refl 2).mul (show 2 ^ padicValNat 2 n ≡ 1 [MOD 3] from hB)).mul
      (show q ^ n.factorization q ≡ 2 [MOD 3] from hC)).mul (show _ ≡ 1 [MOD 3] from hZ)
  have hm : 2 * 1 * Q * 2 ^ R.card ≡ 2 * 1 * 2 * 1 [MOD 3] := e1.symm.trans (by rw [key]; exact e2)
  unfold Nat.ModEq at hm
  rw [Nat.mul_mod (2 * 1 * Q), Nat.mul_mod (2 * 1) Q] at hm
  have hQ0 : Q % 3 ≠ 0 := by
    intro h0
    have h9 : 3 * 3 ∣ 1 + q ^ n.factorization q := by
      rw [hQ]
      exact mul_dvd_mul_left 3 (Nat.dvd_of_mod_eq_zero h0)
    have := le_fact_of_sq hn Nat.prime_three (by norm_num) (dvd_two_mul_of_src h hq h9)
    omega
  have hcard : n.primeFactors.card = R.card + 3 := by
    rw [hR, Finset.card_erase_of_mem hqe, Finset.card_erase_of_mem h3e,
      Finset.card_erase_of_mem h2pf]
    have h1 : 0 < ((n.primeFactors.erase 2).erase 3).card := Finset.card_pos.mpr ⟨q, hqe⟩
    have h2 : 0 < (n.primeFactors.erase 2).card := Finset.card_pos.mpr ⟨3, h3e⟩
    have h3' : 0 < n.primeFactors.card := Finset.card_pos.mpr ⟨2, h2pf⟩
    rw [Finset.card_erase_of_mem h3e, Finset.card_erase_of_mem h2pf] at h1
    rw [Finset.card_erase_of_mem h2pf] at h2
    omega
  have hT : (R.card % 2 = 0 ∧ 2 ^ R.card % 3 = 1) ∨ (R.card % 2 = 1 ∧ 2 ^ R.card % 3 = 2) := by
    rcases Nat.mod_two_eq_zero_or_one R.card with e | e
    · exact Or.inl ⟨e, pmod_two_even (q := 2) (by norm_num) e⟩
    · exact Or.inr ⟨e, pmod_two_odd (q := 2) (by norm_num) e⟩
  have h9 : (1 + q ^ n.factorization q) % 9 = 3 ↔ Q % 3 = 1 := by
    rw [hQ]
    omega
  rw [h9, hcard]
  rcases (by omega : Q % 3 = 1 ∨ Q % 3 = 2) with hq1 | hq1 <;>
    rcases hT with ⟨hc, ht⟩ | ⟨hc, ht⟩ <;> rw [hq1, ht] at hm <;> norm_num at hm <;> omega

-- Section 4. Every repeated odd prime has a source.

theorem source_of_repeated {n z : ℕ} (h : Erdos1052.IsUnitaryPerfect n) (hz : z.Prime) (hz2 : z ≠ 2)
    (hzz : z ^ 2 ∣ n) :
    z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ q ∈ n.primeFactors, q ≠ 2 ∧ q ≠ z ∧ z ∣ 1 + q ^ n.factorization q := by
  have hn : n ≠ 0 := h.2.ne'
  have h2pf : 2 ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, two_dvd_of_isUnitaryPerfect h, hn⟩
  have E := prod_eq_two_mul h
  rw [← Finset.mul_prod_erase _ _ h2pf] at E
  by_cases hex : ∃ q ∈ n.primeFactors, q ≠ 2 ∧ q ≠ z ∧ z ∣ 1 + q ^ n.factorization q
  · exact Or.inr hex
  · left
    have hR : ¬ z ∣ ∏ q ∈ n.primeFactors.erase 2, (1 + q ^ n.factorization q) := by
      intro hd
      obtain ⟨q, hq, hzq⟩ := (Prime.dvd_finsetProd_iff hz.prime _).mp hd
      have hq1 := Finset.mem_of_mem_erase hq
      by_cases hqz : q = z
      · subst hqz
        have he := fact_pos hq1
        have h1 : q ∣ q ^ n.factorization q := dvd_pow_self q (by omega)
        have : q ∣ 1 := (Nat.dvd_add_right h1).mp (by rw [add_comm]; exact hzq)
        exact hz.one_lt.ne' (Nat.dvd_one.mp this)
      · exact hex ⟨q, hq1, Finset.ne_of_mem_erase hq, hqz, hzq⟩
    have hcop : Nat.Coprime (z ^ 2) (∏ q ∈ n.primeFactors.erase 2, (1 + q ^ n.factorization q)) :=
      Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hz).mpr hR)
    have hd : z ^ 2 ∣ (1 + 2 ^ n.factorization 2) *
        ∏ q ∈ n.primeFactors.erase 2, (1 + q ^ n.factorization q) := by
      rw [E]
      exact Dvd.dvd.mul_left hzz 2
    have := hcop.dvd_of_dvd_mul_right hd
    rwa [add_comm, fact2_eq n] at this

-- Section 5. The step.

theorem main : H1 → H2 → OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1.H3 := by
  rintro ⟨A1, h1⟩ ⟨A2, h2⟩
  refine ⟨A1 + A2, fun n h S hS hc hna hf3 ha hex => ?_⟩
  obtain ⟨q, hq, hq3, hqo, hq9, hqe3, hq5, huniq⟩ := hex
  have hcase : n.factorization q = 1 ∨ 5 ≤ n.factorization q := by omega
  have hsrc : ∀ z ∈ S, z ^ 2 ∣ 2 ^ padicValNat 2 n + 1 ∨
      ∃ p ∈ n.primeFactors, p ≠ 2 ∧ p ≠ z ∧ z ∣ 1 + p ^ n.factorization p := fun z hz => by
    obtain ⟨hzp, hz2, hzz⟩ := (hS z).mp hz
    exact source_of_repeated h hzp hz2 hzz
  obtain ⟨c, hc1, hc3, hcd⟩ := fermat_exists h ha
  have hF := fun c (hc : c.Prime) (hc3 : c % 3 = 2) (hcd : c ∣ 2 ^ padicValNat 2 n + 1) =>
    fermat_src h hS huniq hc hc3 hcd
  have h17 : padicValNat 2 n % 8 = 4 → 17 ∈ S := fun h4 => by
    rcases hF 17 (by norm_num) (by norm_num) (by
      rw [add_comm]
      exact (calc 17 = 1 + 2 ^ 4 := by norm_num
        _ ∣ 1 + 2 ^ padicValNat 2 n := one_add_pow_dvd_of_odd_mul (by omega))) with e | e
    · rw [← e] at hq9
      norm_num at hq9
    · exact e
  have h65537 : padicValNat 2 n % 32 = 16 → 65537 ∈ S := fun h4 => by
    rcases hF 65537 (by norm_num) (by norm_num) (by
      rw [add_comm]
      exact (calc 65537 = 1 + 2 ^ 16 := by norm_num
        _ ∣ 1 + 2 ^ padicValNat 2 n := one_add_pow_dvd_of_odd_mul (by omega))) with e | e
    · rw [← e] at hq9
      norm_num at hq9
    · exact e
  have hpar := parity h hf3 ha hq hq3 hqo huniq
  have hcex : ∃ c, c.Prime ∧ c % 3 = 2 ∧ c ∣ 2 ^ padicValNat 2 n + 1 ∧ (c = q ∨ c ∈ S) :=
    ⟨c, hc1, hc3, hcd, hF c hc1 hc3 hcd⟩
  rcases hcase with e1 | e5
  · have := h1 n h S hS hc hna hf3 ha
      ⟨q, hq, hq3, hq9, e1, huniq, hcex, hF, h17, h65537, hpar⟩ hsrc
    omega
  · have := h2 n h S hS hc hna hf3 ha
      ⟨q, hq, hq3, hqo, hq9, hqe3, e5, hq5, fun d hd hdm hd3 => div_src h hS ha hq hq3 hqo huniq hd hdm hd3,
        huniq, hcex, hF, h17, h65537, hpar⟩ hsrc
    omega

end OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H3_R1_H3_R1
