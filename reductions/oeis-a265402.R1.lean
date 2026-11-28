import OMAStatements.S_oeis_a265402

-- Reduction oeis-a265402.R1 of A265402: gcd_{k=1..n-1} C(2n,2k) = n iff n is prime and 2n-1 is not a prime power.
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.
--
-- Proved here: for 2n-1 = q^e the prime q divides every C(2n,2k), so the gcd is not n; for a prime n with
-- 2n-1 not a prime power the gcd is exactly n (Lucas: C(q^a r, q^a) = r mod q). What is left is the composite
-- case. By Kummer/Lucas, n dividing every C(2n,2k) forces 2n = p + p^s for each prime p dividing n (H2), and the
-- remaining exponential Diophantine question (H1) has, below 2n = 10^20, only the solution n = 15 (2n-1 = 29).

namespace OMA.R_oeis_a265402_R1

-- Diophantine core: a composite n with 2n = p + p^s (s >= 2) for every prime p dividing n has 2n-1 a prime power.
def H1 : Prop :=
  ∀ n : ℕ, 1 < n → ¬ n.Prime →
    (∀ p : ℕ, p.Prime → p ∣ n → ∃ s : ℕ, 2 ≤ s ∧ 2 * n = p + p ^ s) → IsPrimePow (2 * n - 1)

-- Kummer step: if a composite n divides every C(2n,2k) (1 <= k <= n-1), then 2n = p + p^s (s >= 2) for each prime p | n.
def H2 : Prop :=
  ∀ n : ℕ, 1 < n → ¬ n.Prime →
    (∀ k ∈ Finset.Icc 1 (n - 1), n ∣ (2 * n).choose (2 * k)) →
      ∀ p : ℕ, p.Prime → p ∣ n → ∃ s : ℕ, 2 ≤ s ∧ 2 * n = p + p ^ s

lemma gcd_dvd_two (n : ℕ) (hn : 2 ≤ n) :
    (Finset.Icc 1 (n - 1)).gcd (fun k => (2 * n).choose (2 * k)) ∣ n * (2 * n - 1) := by
  have h1 : (1 : ℕ) ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨le_refl 1, by omega⟩
  have h := Finset.gcd_dvd (f := fun k => (2 * n).choose (2 * k)) h1
  have hc : (2 * n).choose (2 * 1) = n * (2 * n - 1) := by
    rw [Nat.choose_two_right]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have : 2 * (m + 1) * (2 * (m + 1) - 1) = 2 * ((m + 1) * (2 * (m + 1) - 1)) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
  simpa [hc] using h

-- If 2n-1 = q^e then q divides every C(2n,2k), 1 <= k <= n-1.
lemma prime_dvd_choose_of_pow (n q e k : ℕ) (hq : q.Prime) (he : q ^ e = 2 * n - 1)
    (hk1 : 1 ≤ k) (hkn : k ≤ n - 1) : q ∣ (2 * n).choose (2 * k) := by
  have hn2 : 2 * n = q ^ e + 1 := by omega
  have hk : 2 * k = (2 * k - 1) + 1 := by omega
  rw [hn2, hk, Nat.choose_succ_succ]
  apply dvd_add
  · exact hq.dvd_choose_pow (by omega) (by omega)
  · apply hq.dvd_choose_pow (by omega)
    intro h
    -- q^e = 2n-1 is odd while 2k is even
    omega

lemma not_isPrimePow_of_gcd_eq (n : ℕ) (hn : 2 ≤ n)
    (hG : (Finset.Icc 1 (n - 1)).gcd (fun k => (2 * n).choose (2 * k)) = n) :
    ¬ IsPrimePow (2 * n - 1) := by
  rw [isPrimePow_nat_iff]
  rintro ⟨q, e, hq, he0, he⟩
  have hqG : q ∣ (Finset.Icc 1 (n - 1)).gcd (fun k => (2 * n).choose (2 * k)) := by
    apply Finset.dvd_gcd
    intro k hk
    rw [Finset.mem_Icc] at hk
    exact prime_dvd_choose_of_pow n q e k hq he hk.1 hk.2
  rw [hG] at hqG
  have hqm : q ∣ 2 * n - 1 := by rw [← he]; exact dvd_pow_self q (by omega)
  have h2n : q ∣ 2 * n := Dvd.dvd.mul_left hqG 2
  have : q ∣ 2 * n - (2 * n - 1) := Nat.dvd_sub h2n hqm
  rw [show 2 * n - (2 * n - 1) = 1 by omega] at this
  exact hq.one_lt.ne' (Nat.dvd_one.mp this)

-- The identity 2n * C(2n-1, j-1) = C(2n, j) * j.
lemma choose_identity (n j : ℕ) (hn : 1 ≤ n) (hj : 1 ≤ j) :
    2 * n * (2 * n - 1).choose (j - 1) = (2 * n).choose j * j := by
  have := Nat.add_one_mul_choose_eq (2 * n - 1) (j - 1)
  rwa [show 2 * n - 1 + 1 = 2 * n by omega, show j - 1 + 1 = j by omega] at this

-- Lucas: C(q^a r, q^a) = r (mod q).
lemma choose_pow_mul_modEq (q : ℕ) (hq : q.Prime) (r : ℕ) :
    ∀ a : ℕ, (q ^ a * r).choose (q ^ a) ≡ r [MOD q] := by
  haveI := Fact.mk hq
  intro a
  induction a with
  | zero => simpa using Nat.ModEq.refl r
  | succ a ih =>
    have hl := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := q ^ (a + 1) * r)
      (k := q ^ (a + 1)) (p := q)
    have h1 : q ^ (a + 1) * r % q = 0 := by
      rw [pow_succ]; exact Nat.mod_eq_zero_of_dvd ⟨q ^ a * r, by ring⟩
    have h2 : q ^ (a + 1) % q = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self q (by omega))
    have h3 : q ^ (a + 1) * r / q = q ^ a * r := by
      rw [pow_succ, show q ^ a * q * r = q * (q ^ a * r) by ring]
      exact Nat.mul_div_cancel_left _ hq.pos
    have h4 : q ^ (a + 1) / q = q ^ a := by
      rw [pow_succ]; exact Nat.mul_div_cancel _ hq.pos
    rw [h1, h2, h3, h4, Nat.choose_zero_right, one_mul] at hl
    exact hl.trans ih

lemma gcd_coprime (n : ℕ) (hn : 2 ≤ n) (hnp : ¬ IsPrimePow (2 * n - 1)) :
    Nat.Coprime ((Finset.Icc 1 (n - 1)).gcd (fun k => (2 * n).choose (2 * k))) (2 * n - 1) := by
  apply Nat.Coprime.symm
  apply Nat.coprime_of_dvd
  intro q hq hqm hqG
  set m := 2 * n - 1 with hm
  have hm0 : m ≠ 0 := by omega
  set a := m.factorization q with ha
  have ha1 : 1 ≤ a := (hq.dvd_iff_one_le_factorization hm0).mp hqm
  set Q := q ^ a with hQ
  have hQm : Q ∣ m := Nat.ordProj_dvd m q
  obtain ⟨r, hr⟩ := hQm
  have hcop : Nat.Coprime q (m / Q) := Nat.coprime_ordCompl hq hm0
  have hrQ : m / Q = r := by
    rw [hr]; exact Nat.mul_div_cancel_left r (by rw [hQ]; exact pow_pos hq.pos a)
  rw [hrQ] at hcop
  have hQne : Q ≠ m := by
    intro h
    apply hnp
    rw [isPrimePow_nat_iff]
    exact ⟨q, a, hq, by omega, h⟩
  have hr2 : 2 ≤ r := by
    rcases Nat.lt_or_ge r 2 with h | h
    · interval_cases r
      · omega
      · exact absurd (by rw [hr, mul_one]) hQne
    · exact h
  have hQ1 : 1 ≤ Q := Nat.one_le_pow _ _ hq.pos
  have hQodd : Q % 2 = 1 := by
    rcases Nat.even_or_odd Q with h | h
    · exfalso
      have : 2 ∣ m := hr ▸ Dvd.dvd.mul_right (even_iff_two_dvd.mp h) r
      omega
    · exact Nat.odd_iff.mp h
  have hQle : 2 * Q ≤ m := by rw [hr]; nlinarith
  set k := (Q + 1) / 2 with hk
  have hk2 : 2 * k = Q + 1 := by omega
  have hkmem : k ∈ Finset.Icc 1 (n - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hqC : q ∣ (2 * n).choose (2 * k) := hqG.trans (Finset.gcd_dvd hkmem)
  have hid := choose_identity n (2 * k) (by omega) (by omega)
  rw [show 2 * k - 1 = Q by omega] at hid
  have hq2 : q ∣ 2 * n * (2 * n - 1).choose Q := by
    rw [hid]; exact Dvd.dvd.mul_right hqC _
  have hqn : ¬ q ∣ 2 * n := by
    intro h
    have : q ∣ 2 * n - (2 * n - 1) := Nat.dvd_sub h hqm
    rw [show 2 * n - (2 * n - 1) = 1 by omega] at this
    exact hq.one_lt.ne' (Nat.dvd_one.mp this)
  have hqc : q ∣ m.choose Q := (hq.dvd_mul.mp hq2).resolve_left hqn
  have hmod := choose_pow_mul_modEq q hq r a
  rw [← hQ, ← hr] at hmod
  have : q ∣ r := (Nat.modEq_zero_iff_dvd.mp ((hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hqc))))
  exact absurd (Nat.Coprime.coprime_dvd_right this hcop |>.symm) (by
    rw [Nat.coprime_self]; exact hq.one_lt.ne')

lemma gcd_eq_of_prime (p : ℕ) (hp : p.Prime) (hnp : ¬ IsPrimePow (2 * p - 1)) :
    (Finset.Icc 1 (p - 1)).gcd (fun k => (2 * p).choose (2 * k)) = p := by
  have hp2 : 2 ≤ p := hp.two_le
  have hp3 : p ≠ 2 := by
    rintro rfl; exact hnp (Nat.prime_three.isPrimePow : IsPrimePow 3)
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp3
    · exact h
  have hpG : p ∣ (Finset.Icc 1 (p - 1)).gcd (fun k => (2 * p).choose (2 * k)) := by
    apply Finset.dvd_gcd
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hid := choose_identity p (2 * k) (by omega) (by omega)
    have h1 : p ∣ (2 * p).choose (2 * k) * (2 * k) := by
      rw [← hid]; exact Dvd.dvd.mul_right (dvd_mul_left p 2) _
    rcases hp.dvd_mul.mp h1 with h | h
    · exact h
    · exfalso
      rcases hp.dvd_mul.mp h with h' | h'
      · have := Nat.le_of_dvd (by norm_num) h'; omega
      · have := Nat.le_of_dvd (by omega) h'; omega
  have hGd := gcd_dvd_two p hp2
  have hcop := gcd_coprime p hp2 hnp
  have : (Finset.Icc 1 (p - 1)).gcd (fun k => (2 * p).choose (2 * k)) ∣ p :=
    hcop.dvd_of_dvd_mul_right hGd
  exact Nat.dvd_antisymm this hpG

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a265402.main := by
  intro h1 h2 n hn
  constructor
  · intro hG
    have hn2 : 2 ≤ n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · have : n = 1 := by omega
        subst this
        simp at hG
      · exact h
    have hnpp := not_isPrimePow_of_gcd_eq n hn2 hG
    refine ⟨?_, hnpp⟩
    by_contra hnp
    apply hnpp
    apply h1 n (by omega) hnp
    apply h2 n (by omega) hnp
    intro k hk
    have hd := Finset.gcd_dvd (f := fun k => (2 * n).choose (2 * k)) hk
    rw [hG] at hd
    exact hd
  · rintro ⟨hp, hnp⟩
    exact gcd_eq_of_prime n hp hnp

end OMA.R_oeis_a265402_R1
