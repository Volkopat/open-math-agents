import OMAStatements.S_oeis_a182132

open OMA.S_oeis_a182132

/-- Fermat for one prime factor `p` of `C` with `p - 1 ∣ C - 1`. -/
lemma fermat_part (N p b : ℕ) (hp : p.Prime) (hpN : p ∣ N) (hd : p - 1 ∣ N - 1)
    (hb : b.Coprime N) : b ^ (N - 1) ≡ 1 [MOD p] := by
  obtain ⟨t, ht⟩ := hd
  have hbp : b.Coprime p := Nat.Coprime.coprime_dvd_right hpN hb
  have h := Nat.ModEq.pow_totient hbp
  rw [Nat.totient_prime hp] at h
  rw [ht, pow_mul]
  simpa using h.pow t

lemma combine (x p q : ℕ) (hpq : p.Coprime q) (hp : x ≡ 1 [MOD p]) (hq : x ≡ 1 [MOD q]) :
    x ≡ 1 [MOD p * q] :=
  (Nat.modEq_and_modEq_iff_modEq_mul hpq).1 ⟨hp, hq⟩

lemma cop (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (h : p ≠ q) : p.Coprime q :=
  (Nat.coprime_primes hp hq).2 h

/-- Korselt-type criterion for a product of three distinct primes. -/
lemma carm3 (p q r : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (dp : p - 1 ∣ p * q * r - 1) (dq : q - 1 ∣ p * q * r - 1) (dr : r - 1 ∣ p * q * r - 1) :
    IsCarmichael (p * q * r) := by
  have h2p := hp.two_le
  have h2q := hq.two_le
  have h2r := hr.two_le
  refine ⟨?_, ?_, ?_⟩
  · have : 1 < p * q := by nlinarith
    nlinarith
  · exact Nat.not_prime_mul (by nlinarith) (by omega)
  · intro b hb
    have ep := fermat_part _ p b hp (Dvd.intro (q * r) (by ring)) dp hb
    have eq := fermat_part _ q b hq (Dvd.intro (p * r) (by ring)) dq hb
    have er := fermat_part _ r b hr (Dvd.intro_left _ rfl) dr hb
    have epq := combine _ _ _ (cop p q hp hq hpq) ep eq
    exact combine _ _ _ (Nat.Coprime.mul_left (cop p r hp hr hpr) (cop q r hq hr hqr)) epq er

/-- Korselt-type criterion for a product of four distinct primes. -/
lemma carm4 (p q r s : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hps : p ≠ s) (hqs : q ≠ s) (hrs : r ≠ s)
    (dp : p - 1 ∣ p * q * r * s - 1) (dq : q - 1 ∣ p * q * r * s - 1)
    (dr : r - 1 ∣ p * q * r * s - 1) (ds : s - 1 ∣ p * q * r * s - 1) :
    IsCarmichael (p * q * r * s) := by
  have h2p := hp.two_le
  have h2q := hq.two_le
  have h2r := hr.two_le
  have h2s := hs.two_le
  have h1 : 1 < p * q := by nlinarith
  have h1' : 1 < p * q * r := by nlinarith
  refine ⟨?_, ?_, ?_⟩
  · nlinarith
  · exact Nat.not_prime_mul (by omega) (by omega)
  · intro b hb
    have ep := fermat_part _ p b hp (Dvd.intro (q * r * s) (by ring)) dp hb
    have eq := fermat_part _ q b hq (Dvd.intro (p * r * s) (by ring)) dq hb
    have er := fermat_part _ r b hr (Dvd.intro (p * q * s) (by ring)) dr hb
    have es := fermat_part _ s b hs (Dvd.intro_left _ rfl) ds hb
    have epq := combine _ _ _ (cop p q hp hq hpq) ep eq
    have epqr := combine _ _ _ (Nat.Coprime.mul_left (cop p r hp hr hpr) (cop q r hq hr hqr))
      epq er
    exact combine _ _ _ (Nat.Coprime.mul_left (Nat.Coprime.mul_left (cop p s hp hs hps)
      (cop q s hq hs hqs)) (cop r s hr hs hrs)) epqr es

theorem OMA.solution : type_of% @OMA.S_oeis_a182132.main := by
  refine ⟨?_, ?_⟩
  · intro n hn h1 h2 h3
    obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have e1 : 30 * (j + 1) - 7 = 30 * j + 23 := by omega
    have e2 : 90 * (j + 1) - 23 = 90 * j + 67 := by omega
    have e3 : 300 * (j + 1) - 79 = 300 * j + 221 := by omega
    unfold C
    rw [e1] at h1
    rw [e2] at h2
    rw [e3] at h3
    rw [e1, e2, e3]
    have key : (30 * j + 23) * (90 * j + 67) * (300 * j + 221) - 1
        = 60 * (15 * j + 11) * (900 * j ^ 2 + 1363 * j + 516) := by
      have : (30 * j + 23) * (90 * j + 67) * (300 * j + 221)
          = 60 * (15 * j + 11) * (900 * j ^ 2 + 1363 * j + 516) + 1 := by ring
      omega
    apply carm3 _ _ _ h1 h2 h3 (by omega) (by omega) (by omega)
    · rw [key, show 30 * j + 23 - 1 = 2 * (15 * j + 11) by omega]
      exact Dvd.intro (30 * (900 * j ^ 2 + 1363 * j + 516)) (by ring)
    · rw [key, show 90 * j + 67 - 1 = 6 * (15 * j + 11) by omega]
      exact Dvd.intro (10 * (900 * j ^ 2 + 1363 * j + 516)) (by ring)
    · rw [key, show 300 * j + 221 - 1 = 20 * (15 * j + 11) by omega]
      exact Dvd.intro (3 * (900 * j ^ 2 + 1363 * j + 516)) (by ring)
  · refine ⟨1, le_refl 1, ?_, ?_⟩
    · have hC : C 1 = 13 * 17 * 23 * 67 := by norm_num [C]
      rw [hC]
      exact carm4 13 17 23 67 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · norm_num
