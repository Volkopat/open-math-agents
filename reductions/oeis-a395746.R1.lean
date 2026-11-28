import OMAStatements.S_oeis_a395746

-- Reduction oeis-a395746.R1 of A395746: Numbers m such that A265388(m) = A007947(m*(2*m-1)).
-- Credit: @lettucrisp
--
-- We prove in full:
-- 1. Exact Kummer characterization of `evenBinomialGcd n`: it is always squarefree,
--    `2 ∣ evenBinomialGcd n ↔ ∃ a ≥ 1, n = 2^a`, and for odd prime `p`,
--    `p ∣ evenBinomialGcd n ↔ (∃ a ≥ 1, n = p^a) ∨ (∃ a < b, 2*n = p^a + p^b)`.
-- 2. Chai Wah Wu's two theorems:
--    - If `n > 1` and both `n` and `2*n - 1` are prime powers, then `n` is a term.
--    - If `n > 1` is a term, then `2*n - 1` is a prime power, and if `n` is even then `n` is a
--      power of 2.
-- 3. For odd composite `n = p^a * q^c` (`p < q`) with `p^r + 1 = 2*q^c` and `q^s + 1 = 2*p^a`:
--    by LTE, `r` and `s` are powers of 2 (so `r = 2^k` with `k ≥ 1`, and `s = 1` or `s = 2^ℓ`
--    with `ℓ ≥ 1`), and the case `s = 1` uniquely forces `n = 15`.
--
-- This leaves two purely exponential-Diophantine subgoals:
-- * H1: the two-prime even-exponent system `p^(2^k) + 1 = 2*q^c`, `q^(2^ℓ) + 1 = 2*p^a` with
--       `2*p^a*q^c - 1` a prime power.
-- * H2: odd `n` with at least three distinct prime factors where every `p ∣ n` satisfies
--       `p^(v_p(n)) * (p^r + 1) = 2*n` and `2*n - 1` is a prime power.

namespace OMA.R_oeis_a395746_R1

open OMA.S_oeis_a395746

/-- Two-prime even-exponent Diophantine core. -/
def H1 : Prop :=
  ∀ p q a c k ℓ : ℕ, p.Prime → q.Prime → 2 < p → p < q →
    1 ≤ a → 1 ≤ c → 1 ≤ k → 1 ≤ ℓ →
    p ^ (2 ^ k) + 1 = 2 * q ^ c →
    q ^ (2 ^ ℓ) + 1 = 2 * p ^ a →
    IsPrimePow (2 * p ^ a * q ^ c - 1) → False

/-- Three-or-more-prime Diophantine core. -/
def H2 : Prop :=
  ∀ n : ℕ, Odd n → 3 ≤ n.primeFactors.card → IsPrimePow (2 * n - 1) →
    (∀ p ∈ n.primeFactors, ∃ r : ℕ, 1 ≤ r ∧ p ^ (n.factorization p) * (p ^ r + 1) = 2 * n) →
    False

section Helpers

private lemma carry_iff_mod_lt {N M q : ℕ} (hMN : M ≤ N) (hq : 0 < q) :
    q ≤ M % q + (N - M) % q ↔ N % q < M % q := by
  have hmod : (M % q + (N - M) % q) % q = N % q := by
    rw [Nat.add_mod_mod, Nat.mod_add_mod, Nat.add_sub_of_le hMN]
  have hM : M % q < q := Nat.mod_lt M hq
  have hNM : (N - M) % q < q := Nat.mod_lt (N - M) hq
  constructor
  · intro hge
    have hlt2 : M % q + (N - M) % q < q + q := Nat.add_lt_add hM hNM
    have hsub : (M % q + (N - M) % q) % q = M % q + (N - M) % q - q := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [hmod] at hsub
    omega
  · intro hlt
    by_contra hnot
    push Not at hnot
    have heq : (M % q + (N - M) % q) % q = M % q + (N - M) % q := Nat.mod_eq_of_lt hnot
    rw [hmod] at heq
    omega

private lemma padicValNat_choose_eq_card_mod_lt {p N M b : ℕ} [hp : Fact p.Prime]
    (hMN : M ≤ N) (hb : Nat.log p N < b) :
    padicValNat p (N.choose M) =
      ((Finset.Ico 1 b).filter fun i => N % p ^ i < M % p ^ i).card := by
  rw [padicValNat_choose hMN hb]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · rintro ⟨hi, hcarry⟩
    exact ⟨hi, (carry_iff_mod_lt hMN (pow_pos hp.out.pos i)).mp hcarry⟩
  · rintro ⟨hi, hlt⟩
    exact ⟨hi, (carry_iff_mod_lt hMN (pow_pos hp.out.pos i)).mpr hlt⟩

private lemma prime_dvd_choose_iff_exists_mod_lt {p N M : ℕ} [hp : Fact p.Prime]
    (hMN : M ≤ N) :
    p ∣ N.choose M ↔ ∃ i : ℕ, 1 ≤ i ∧ N % p ^ i < M % p ^ i := by
  have hne : N.choose M ≠ 0 := Nat.choose_ne_zero hMN
  have hiff : p ∣ N.choose M ↔ 0 < padicValNat p (N.choose M) := by
    have h1 : p ∣ N.choose M ↔ 1 ≤ padicValNat p (N.choose M) := by
      rw [← Nat.factorization_def _ hp.out, ← hp.out.pow_dvd_iff_le_factorization hne, pow_one]
    rw [h1]
    exact ⟨fun h => by omega, fun h => by omega⟩
  rw [hiff]
  let b := Nat.log p N + 1
  rw [padicValNat_choose_eq_card_mod_lt hMN (Nat.lt_succ_self _), Finset.card_pos]
  constructor
  · rintro ⟨i, hi⟩
    simp only [Finset.mem_filter, Finset.mem_Ico] at hi
    exact ⟨i, hi.1.1, hi.2⟩
  · rintro ⟨i, hi1, hlt⟩
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hi1, ?_⟩, hlt⟩⟩
    by_contra hge
    push Not at hge
    have hNlt : N < p ^ i := by
      have h1 : N < p ^ b := Nat.lt_pow_succ_log_self hp.out.one_lt N
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right hp.out.pos hge)
    have hMlt : M < p ^ i := lt_of_le_of_lt hMN hNlt
    rw [Nat.mod_eq_of_lt hNlt, Nat.mod_eq_of_lt hMlt] at hlt
    omega

private lemma evenBinomialGcd_pos {n : ℕ} (hn : 1 < n) : 0 < evenBinomialGcd n := by
  apply Nat.pos_of_ne_zero
  intro h0
  have hdvd : evenBinomialGcd n ∣ (2 * n).choose (2 * 1) :=
    Finset.gcd_dvd (Finset.mem_Ico.mpr ⟨le_rfl, hn⟩)
  rw [h0, zero_dvd_iff] at hdvd
  exact Nat.choose_ne_zero (by omega) hdvd

private lemma dvd_evenBinomialGcd_iff {n d : ℕ} :
    d ∣ evenBinomialGcd n ↔ ∀ k : ℕ, 1 ≤ k → k < n → d ∣ (2 * n).choose (2 * k) := by
  unfold evenBinomialGcd
  rw [Finset.dvd_gcd_iff]
  simp [Finset.mem_Ico]

private lemma not_sq_dvd_choose_of_unique_carry {p N M i₀ : ℕ} [hp : Fact p.Prime]
    (hMN : M ≤ N) (hhi : ∀ i : ℕ, 1 ≤ i → N % p ^ i < M % p ^ i → i = i₀) :
    ¬ p ^ 2 ∣ N.choose M := by
  have hne : N.choose M ≠ 0 := Nat.choose_ne_zero hMN
  rw [hp.out.pow_dvd_iff_le_factorization hne, Nat.factorization_def _ hp.out]
  let b := Nat.log p N + 1
  rw [padicValNat_choose_eq_card_mod_lt (b := b) hMN (Nat.lt_succ_self _)]
  have hsub : ((Finset.Ico 1 b).filter fun i => N % p ^ i < M % p ^ i) ⊆ {i₀} := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton] at hi ⊢
    exact hhi i hi.1.1 hi.2
  have hle : ((Finset.Ico 1 b).filter fun i => N % p ^ i < M % p ^ i).card ≤ 1 :=
    (Finset.card_le_card hsub).trans (by simp)
  omega

private lemma two_dvd_evenBinomialGcd_iff {n : ℕ} (hn : 1 < n) :
    2 ∣ evenBinomialGcd n ↔ ∃ a : ℕ, 1 ≤ a ∧ n = 2 ^ a := by
  have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h2
    let a := Nat.log 2 n
    have ha1 : 1 ≤ a := by
      have : 1 ≤ Nat.log 2 2 := by decide
      exact this.trans (Nat.log_mono_right hn)
    have hle : 2 ^ a ≤ n := Nat.pow_log_le_self 2 (by omega)
    have hlt : n < 2 ^ (a + 1) := Nat.lt_pow_succ_log_self (by decide) n
    refine ⟨a, ha1, ?_⟩
    by_contra hne
    have hlt_a : 2 ^ a < n := lt_of_le_of_ne hle (Ne.symm hne)
    have hdvd : 2 ∣ (2 * n).choose (2 * 2 ^ a) :=
      dvd_evenBinomialGcd_iff.mp h2 (2 ^ a) (Nat.one_le_pow _ _ (by decide)) hlt_a
    obtain ⟨i, hi1, hmod⟩ := (prime_dvd_choose_iff_exists_mod_lt (by omega)).mp hdvd
    have h2a : 2 * 2 ^ a = 2 ^ (a + 1) := by ring
    rw [h2a] at hmod
    by_cases hi : i ≤ a + 1
    · have h0 : 2 ^ (a + 1) % 2 ^ i = 0 :=
        Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 hi)
      omega
    · have hge : a + 2 ≤ i := by omega
      have h2n_lt : 2 * n < 2 ^ i := by
        calc 2 * n < 2 * 2 ^ (a + 1) := by omega
          _ = 2 ^ (a + 2) := by ring
          _ ≤ 2 ^ i := Nat.pow_le_pow_right (by decide) hge
      have h2a_lt : 2 ^ (a + 1) < 2 ^ i := lt_of_le_of_lt (by omega) h2n_lt
      rw [Nat.mod_eq_of_lt h2n_lt, Nat.mod_eq_of_lt h2a_lt] at hmod
      omega
  · rintro ⟨a, ha1, rfl⟩
    rw [dvd_evenBinomialGcd_iff]
    intro k hk1 hkn
    rw [prime_dvd_choose_iff_exists_mod_lt (by omega)]
    refine ⟨a + 1, by omega, ?_⟩
    have hpow : 2 * 2 ^ a = 2 ^ (a + 1) := by ring
    rw [hpow, Nat.mod_self, Nat.mod_eq_of_lt (by omega)]
    omega

private lemma odd_prime_dvd_evenBinomialGcd_iff {p n : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hn : 1 < n) :
    p ∣ evenBinomialGcd n ↔
      (∃ a : ℕ, 1 ≤ a ∧ n = p ^ a) ∨ (∃ a b : ℕ, a < b ∧ 2 * n = p ^ a + p ^ b) := by
  have _ : Fact p.Prime := ⟨hp⟩
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  constructor
  · intro hdvd_all
    let b := Nat.log p (2 * n)
    have hpb_le : p ^ b ≤ 2 * n := Nat.pow_log_le_self p (by omega)
    have h2n_lt : 2 * n < p ^ (b + 1) := Nat.lt_pow_succ_log_self hp.one_lt (2 * n)
    by_cases h2pb : 2 * p ^ b ≤ 2 * n
    · left
      have hb1 : 1 ≤ b := by
        by_contra hb0
        have hb0' : b = 0 := by omega
        simp only [hb0', pow_zero, zero_add, pow_one] at h2n_lt hpb_le
        -- Wait: if b = 0 then 2*n < p, impossible when p | choose (2*n) 2!
        have hc2 : p ∣ (2 * n).choose (2 * 1) :=
          dvd_evenBinomialGcd_iff.mp hdvd_all 1 le_rfl hn
        obtain ⟨i, hi1, hmod⟩ := (prime_dvd_choose_iff_exists_mod_lt (by omega)).mp hc2
        have hlti : 2 * n < p ^ i :=
          lt_of_lt_of_le h2n_lt (by simpa [pow_one] using Nat.pow_le_pow_right hp.pos hi1)
        have h2lt : 2 * 1 < p ^ i := by omega
        rw [Nat.mod_eq_of_lt hlti, Nat.mod_eq_of_lt h2lt] at hmod
        omega
      refine ⟨b, hb1, ?_⟩
      by_contra hne
      have hlt_pb : p ^ b < n := by omega
      have hdvd : p ∣ (2 * n).choose (2 * p ^ b) :=
        dvd_evenBinomialGcd_iff.mp hdvd_all (p ^ b) (Nat.one_le_pow _ _ hp.pos) hlt_pb
      obtain ⟨i, hi1, hmod⟩ := (prime_dvd_choose_iff_exists_mod_lt (by omega)).mp hdvd
      by_cases hi : i ≤ b
      · have h0 : (2 * p ^ b) % p ^ i = 0 :=
          Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right (pow_dvd_pow p hi) 2)
        rw [h0] at hmod
        exact (Nat.not_lt_zero _ hmod).elim
      · have hge : b + 1 ≤ i := by omega
        have hlti : 2 * n < p ^ i :=
          lt_of_lt_of_le h2n_lt (Nat.pow_le_pow_right hp.pos hge)
        have hMlt : 2 * p ^ b < p ^ i := lt_of_le_of_lt h2pb hlti
        rw [Nat.mod_eq_of_lt hlti, Nat.mod_eq_of_lt hMlt] at hmod
        omega
    · right
      let r := 2 * n - p ^ b
      have hr_eq : 2 * n = p ^ b + r := (Nat.add_sub_of_le hpb_le).symm
      have hr_lt : r < p ^ b := by omega
      have hr_pos : 0 < r := by
        by_contra hr0
        have : 2 * n = p ^ b := by omega
        have heven : Even (p ^ b) := ⟨n, by omega⟩
        have hodd : Odd (p ^ b) := hp_odd.pow
        exact (Nat.not_even_iff_odd.mpr hodd) heven
      let a := Nat.log p r
      have hpa_le : p ^ a ≤ r := Nat.pow_log_le_self p (by omega)
      have hr_lt_a : r < p ^ (a + 1) := Nat.lt_pow_succ_log_self hp.one_lt r
      have hab : a < b := by
        by_contra hge
        have : p ^ b ≤ p ^ a := Nat.pow_le_pow_right hp.pos (by omega)
        omega
      have hsum_even : Even (p ^ a + p ^ b) := (hp_odd.pow).add_odd (hp_odd.pow)
      obtain ⟨k, hk_eq⟩ := hsum_even
      have h2k : 2 * k = p ^ a + p ^ b := by omega
      have hk1 : 1 ≤ k := by
        have : 1 ≤ p ^ a := Nat.one_le_pow _ _ hp.pos
        have : 1 ≤ p ^ b := Nat.one_le_pow _ _ hp.pos
        omega
      refine ⟨a, b, hab, ?_⟩
      by_contra hne
      have hkn : k < n := by omega
      have hdvd : p ∣ (2 * n).choose (2 * k) :=
        dvd_evenBinomialGcd_iff.mp hdvd_all k hk1 hkn
      obtain ⟨i, hi1, hmod⟩ := (prime_dvd_choose_iff_exists_mod_lt (by omega)).mp hdvd
      rw [h2k] at hmod
      by_cases hi1' : i ≤ a
      · have h0 : (p ^ a + p ^ b) % p ^ i = 0 :=
          Nat.mod_eq_zero_of_dvd (dvd_add (pow_dvd_pow p hi1') (pow_dvd_pow p (le_trans hi1' hab.le)))
        rw [h0] at hmod
        exact (Nat.not_lt_zero _ hmod).elim
      · by_cases hi2' : i ≤ b
        · have ha1 : a + 1 ≤ i := by omega
          have hpi_le : p ^ (a + 1) ≤ p ^ i := Nat.pow_le_pow_right hp.pos ha1
          have hr_lt_pi : r < p ^ i := lt_of_lt_of_le hr_lt_a hpi_le
          have hpa_lt_pi : p ^ a < p ^ i := lt_of_le_of_lt hpa_le hr_lt_pi
          have hmod_n : (2 * n) % p ^ i = r := by
            rw [hr_eq, Nat.add_mod, Nat.mod_eq_zero_of_dvd (pow_dvd_pow p hi2'),
              zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hr_lt_pi]
          have hmod_m : (p ^ a + p ^ b) % p ^ i = p ^ a := by
            rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (pow_dvd_pow p hi2'),
              add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hpa_lt_pi]
          rw [hmod_n, hmod_m] at hmod
          omega
        · have hb1 : b + 1 ≤ i := by omega
          have hlti : 2 * n < p ^ i := lt_of_lt_of_le h2n_lt (Nat.pow_le_pow_right hp.pos hb1)
          have hMlt : p ^ a + p ^ b < p ^ i := by omega
          rw [Nat.mod_eq_of_lt hlti, Nat.mod_eq_of_lt hMlt] at hmod
          omega
  · intro hcases
    rw [dvd_evenBinomialGcd_iff]
    intro k hk1 hkn
    rw [prime_dvd_choose_iff_exists_mod_lt (by omega)]
    rcases hcases with ⟨a, ha1, rfl⟩ | ⟨a, b, hab, h2n⟩
    · refine ⟨a, ha1, ?_⟩
      have h0 : (2 * p ^ a) % p ^ a = 0 := Nat.mod_eq_zero_of_dvd (dvd_mul_left _ _)
      rw [h0]
      apply Nat.pos_of_ne_zero
      intro hdiv
      have hdvd : p ^ a ∣ 2 * k := Nat.dvd_of_mod_eq_zero hdiv
      have hcop : Nat.Coprime (p ^ a) 2 := ((Nat.coprime_primes hp Nat.prime_two).mpr (by omega)).pow_left a
      have hdvd_k : p ^ a ∣ k := hcop.dvd_of_dvd_mul_left hdvd
      have hle : p ^ a ≤ k := Nat.le_of_dvd (by omega) hdvd_k
      omega
    · by_cases hdiv_a : p ^ a ∣ 2 * k
      · refine ⟨b, by omega, ?_⟩
        have hpa_lt_pb : p ^ a < p ^ b := Nat.pow_lt_pow_right hp.one_lt hab
        have hmod_n : (2 * n) % p ^ b = p ^ a := by
          rw [h2n, Nat.add_mod, Nat.mod_self, add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hpa_lt_pb]
        rw [hmod_n]
        obtain ⟨m, hm⟩ := hdiv_a
        have hm_even : Even m := by
          have h2 : 2 ∣ p ^ a * m := ⟨k, by omega⟩
          have hcop : Nat.Coprime 2 (p ^ a) :=
            ((Nat.coprime_primes Nat.prime_two hp).mpr (by omega)).pow_right a
          exact even_iff_two_dvd.mpr (hcop.dvd_of_dvd_mul_left h2)
        have hm_ge2 : 2 ≤ m := by
          rcases hm_even with ⟨t, ht⟩
          have : m ≠ 0 := by rintro rfl; omega
          omega
        by_cases hlt_pb : 2 * k < p ^ b
        · rw [Nat.mod_eq_of_lt hlt_pb, hm]
          have : p ^ a * 1 < p ^ a * m := Nat.mul_lt_mul_of_pos_left (by omega) (pow_pos hp.pos a)
          simpa using this
        · exfalso
          have hge_pb : p ^ b ≤ 2 * k := by omega
          have hdiff_lt : 2 * k - p ^ b < p ^ a := by omega
          have hdiff_dvd : p ^ a ∣ 2 * k - p ^ b :=
            Nat.dvd_sub ⟨m, hm⟩ (pow_dvd_pow p hab.le)
          have hdiff0 : 2 * k - p ^ b = 0 := by
            by_contra hne0
            have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne0) hdiff_dvd
            omega
          have heq : 2 * k = p ^ b := by omega
          have hodd : Odd (p ^ b) := hp_odd.pow
          exact (Nat.not_even_iff_odd.mpr hodd) ⟨k, by omega⟩
      · have ha1 : 1 ≤ a := by
          by_contra ha0
          have ha0' : a = 0 := by omega
          rw [ha0', pow_zero] at hdiv_a
          exact hdiv_a (one_dvd _)
        refine ⟨a, ha1, ?_⟩
        have h0 : (2 * n) % p ^ a = 0 := by
          rw [h2n]
          exact Nat.mod_eq_zero_of_dvd (dvd_add dvd_rfl (pow_dvd_pow p hab.le))
        rw [h0]
        exact Nat.pos_of_ne_zero (fun h => hdiv_a (Nat.dvd_of_mod_eq_zero h))

private lemma not_sq_dvd_evenBinomialGcd {p n : ℕ} (hp : p.Prime) (hn : 1 < n) :
    ¬ p ^ 2 ∣ evenBinomialGcd n := by
  have _ : Fact p.Prime := ⟨hp⟩
  by_cases hdvd : p ∣ evenBinomialGcd n
  · rcases hp.eq_two_or_odd with rfl | hpodd
    · obtain ⟨a, ha1, rfl⟩ := (two_dvd_evenBinomialGcd_iff hn).mp hdvd
      intro hsq
      have hc : 2 ^ 2 ∣ (2 * 2 ^ a).choose (2 * 2 ^ (a - 1)) :=
        hsq.trans (dvd_evenBinomialGcd_iff.mp dvd_rfl (2 ^ (a - 1))
          (Nat.one_le_pow _ _ (by decide)) (Nat.pow_lt_pow_right (by decide) (by omega)))
      have h2m : 2 * 2 ^ (a - 1) = 2 ^ a := by
        conv_rhs => rw [← Nat.sub_add_cancel ha1, pow_succ']
      have h2n : 2 * 2 ^ a = 2 ^ (a + 1) := by ring
      rw [h2m, h2n] at hc
      refine not_sq_dvd_choose_of_unique_carry (i₀ := a + 1)
        (Nat.pow_le_pow_right (by decide) (by omega)) ?_ hc
      intro i hi1 hlt
      by_cases hi : i ≤ a
      · rw [Nat.mod_eq_zero_of_dvd (pow_dvd_pow 2 hi)] at hlt
        omega
      · by_cases hi' : i = a + 1
        · exact hi'
        · have hge : a + 2 ≤ i := by omega
          have h1 : 2 ^ (a + 1) < 2 ^ i := Nat.pow_lt_pow_right (by decide) (by omega)
          have h2 : 2 ^ a < 2 ^ i := Nat.pow_lt_pow_right (by decide) (by omega)
          rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hlt
          have : 2 ^ a ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by decide) (by omega)
          omega
    · have hp2 : 2 < p := by have := hp.two_le; omega
      rcases (odd_prime_dvd_evenBinomialGcd_iff hp hp2 hn).mp hdvd with
        ⟨a, ha1, rfl⟩ | ⟨a, b, hab, h2n⟩
      · intro hsq
        have hc : p ^ 2 ∣ (2 * p ^ a).choose (2 * p ^ (a - 1)) :=
          hsq.trans (dvd_evenBinomialGcd_iff.mp dvd_rfl (p ^ (a - 1))
            (Nat.one_le_pow _ _ hp.pos) (Nat.pow_lt_pow_right hp.one_lt (by omega)))
        refine not_sq_dvd_choose_of_unique_carry (i₀ := a) (by
          have := Nat.pow_le_pow_right hp.pos (Nat.sub_le a 1); omega) ?_ hc
        intro i hi1 hlt
        by_cases hi : i ≤ a - 1
        · rw [Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right (pow_dvd_pow p hi) 2)] at hlt
          exact (Nat.not_lt_zero _ hlt).elim
        · by_cases hia : i = a
          · exact hia
          · have hge : a + 1 ≤ i := by omega
            have h2pa_lt : 2 * p ^ a < p ^ i := by
              calc 2 * p ^ a < p * p ^ a := Nat.mul_lt_mul_of_pos_right hp2 (pow_pos hp.pos a)
                _ = p ^ (a + 1) := (pow_succ' p a).symm
                _ ≤ p ^ i := Nat.pow_le_pow_right hp.pos hge
            have h2pam_lt : 2 * p ^ (a - 1) < p ^ i := by
              have := Nat.pow_le_pow_right hp.pos (Nat.sub_le a 1); omega
            rw [Nat.mod_eq_of_lt h2pa_lt, Nat.mod_eq_of_lt h2pam_lt] at hlt
            have := Nat.pow_le_pow_right hp.pos (Nat.sub_le a 1)
            omega
      · intro hsq
        rcases Nat.eq_zero_or_pos a with rfl | ha1
        · simp only [pow_zero] at h2n
          by_cases hb1 : b = 1
          · subst hb1
            have hc : p ^ 2 ∣ (2 * n).choose (2 * 1) :=
              hsq.trans (dvd_evenBinomialGcd_iff.mp dvd_rfl 1 le_rfl hn)
            refine not_sq_dvd_choose_of_unique_carry (i₀ := 1) (by omega) ?_ hc
            intro i hi1 hlt
            by_cases hi : i = 1
            · exact hi
            · have hge : 2 ≤ i := by omega
              have h1 : 2 * n < p ^ i := by
                have h2 : p + 1 < p ^ 2 := by nlinarith
                have h3 : p ^ 2 ≤ p ^ i := Nat.pow_le_pow_right hp.pos hge
                rw [h2n, pow_one]; omega
              have h2 : 2 * 1 < p ^ i := by omega
              rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hlt
              omega
          · have hb2 : 2 ≤ b := by omega
            have heven : Even (1 + p ^ (b - 1)) := by
              have : Odd (p ^ (b - 1)) := (hp.odd_of_ne_two (by omega)).pow
              exact (odd_one).add_odd this
            obtain ⟨k, hk⟩ := heven
            have h2k : 2 * k = 1 + p ^ (b - 1) := by omega
            have hpb_gt : p ^ (b - 1) < p ^ b := Nat.pow_lt_pow_right hp.one_lt (by omega)
            have hk1 : 1 ≤ k := by have := Nat.one_le_pow (b - 1) p hp.pos; omega
            have hkn : k < n := by omega
            have hc : p ^ 2 ∣ (2 * n).choose (2 * k) :=
              hsq.trans (dvd_evenBinomialGcd_iff.mp dvd_rfl k hk1 hkn)
            refine not_sq_dvd_choose_of_unique_carry (i₀ := b) (by omega) ?_ hc
            intro i hi1 hlt
            by_cases hi : i ≤ b - 1
            · have hpi_gt1 : 1 < p ^ i := one_lt_pow₀ hp.one_lt (by omega)
              have hmn : (2 * n) % p ^ i = 1 := by
                rw [h2n, Nat.add_mod, Nat.mod_eq_zero_of_dvd (pow_dvd_pow p (by omega)),
                  add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hpi_gt1]
              have hmm : (2 * k) % p ^ i = 1 := by
                rw [h2k, Nat.add_mod, Nat.mod_eq_zero_of_dvd (pow_dvd_pow p hi),
                  add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hpi_gt1]
              rw [hmn, hmm] at hlt
              omega
            · by_cases hib : i = b
              · exact hib
              · have hge : b + 1 ≤ i := by omega
                have h1 : 2 * n < p ^ i := by
                  have hlt_pb1 : 1 + p ^ b < p ^ (b + 1) := by
                    rw [pow_succ']; nlinarith [Nat.one_le_pow b p hp.pos]
                  have hle_pi : p ^ (b + 1) ≤ p ^ i := Nat.pow_le_pow_right hp.pos hge
                  omega
                have h2 : 2 * k < p ^ i := by omega
                rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hlt
                omega
        · -- 1 ≤ a < b, witness 2k = 2 * p^(a - 1)
          have hlt_n : p ^ (a - 1) < n := by
            have h1 : p ^ (a - 1) ≤ p ^ a := Nat.pow_le_pow_right hp.pos (Nat.sub_le a 1)
            have h2 : p ^ a < p ^ b := Nat.pow_lt_pow_right hp.one_lt hab
            omega
          have hc : p ^ 2 ∣ (2 * n).choose (2 * p ^ (a - 1)) :=
            hsq.trans (dvd_evenBinomialGcd_iff.mp dvd_rfl (p ^ (a - 1))
              (Nat.one_le_pow _ _ hp.pos) hlt_n)
          refine not_sq_dvd_choose_of_unique_carry (i₀ := a) (by omega) ?_ hc
          intro i hi1 hlt
          by_cases hi : i ≤ a - 1
          · rw [Nat.mod_eq_zero_of_dvd (dvd_mul_of_dvd_right (pow_dvd_pow p hi) 2)] at hlt
            exact (Nat.not_lt_zero _ hlt).elim
          · by_cases hia : i = a
            · exact hia
            · by_cases hib : i ≤ b
              · have hpa_lt_pi : p ^ a < p ^ i := Nat.pow_lt_pow_right hp.one_lt (by omega)
                have h2pam_lt_pa : 2 * p ^ (a - 1) < p ^ a := by
                  calc 2 * p ^ (a - 1) < p * p ^ (a - 1) :=
                        Nat.mul_lt_mul_of_pos_right hp2 (pow_pos hp.pos _)
                    _ = p ^ a := by rw [← pow_succ', Nat.sub_add_cancel ha1]
                have hmn : (2 * n) % p ^ i = p ^ a := by
                  rw [h2n, Nat.add_mod, Nat.mod_eq_zero_of_dvd (pow_dvd_pow p hib),
                    add_zero, Nat.mod_mod, Nat.mod_eq_of_lt hpa_lt_pi]
                have hmm : (2 * p ^ (a - 1)) % p ^ i = 2 * p ^ (a - 1) :=
                  Nat.mod_eq_of_lt (lt_trans h2pam_lt_pa hpa_lt_pi)
                rw [hmn, hmm] at hlt
                omega
              · have hge : b + 1 ≤ i := by omega
                have h1 : 2 * n < p ^ i := by
                  have hpa_lt : p ^ a < p ^ b := Nat.pow_lt_pow_right hp.one_lt hab
                  have hlt_pb1 : p ^ a + p ^ b < p ^ (b + 1) := by
                    rw [pow_succ']; nlinarith [Nat.one_le_pow b p hp.pos]
                  have hle_pi : p ^ (b + 1) ≤ p ^ i := Nat.pow_le_pow_right hp.pos hge
                  omega
                have h2 : 2 * p ^ (a - 1) < p ^ i := by omega
                rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hlt
                omega
  · intro hsq
    exact hdvd (dvd_trans (dvd_pow_self p (by decide)) hsq)

private lemma eq_of_squarefree_same_prime_dvd {A B : ℕ} (hA0 : A ≠ 0) (hB0 : B ≠ 0)
    (hAsq : ∀ p : ℕ, p.Prime → ¬ p ^ 2 ∣ A)
    (hBsq : ∀ p : ℕ, p.Prime → ¬ p ^ 2 ∣ B)
    (hsame : ∀ p : ℕ, p.Prime → (p ∣ A ↔ p ∣ B)) : A = B := by
  apply Nat.eq_of_factorization_eq hA0 hB0
  intro p
  by_cases hp : p.Prime
  · have hA1 : A.factorization p ≤ 1 := by
      by_contra hgt
      have hge2 : 2 ≤ A.factorization p := by omega
      exact hAsq p hp ((hp.pow_dvd_iff_le_factorization hA0).mpr hge2)
    have hB1 : B.factorization p ≤ 1 := by
      by_contra hgt
      have hge2 : 2 ≤ B.factorization p := by omega
      exact hBsq p hp ((hp.pow_dvd_iff_le_factorization hB0).mpr hge2)
    have hA_pos : 1 ≤ A.factorization p ↔ p ∣ A := by
      rw [← hp.pow_dvd_iff_le_factorization hA0, pow_one]
    have hB_pos : 1 ≤ B.factorization p ↔ p ∣ B := by
      rw [← hp.pow_dvd_iff_le_factorization hB0, pow_one]
    by_cases hpa : p ∣ A
    · have h1 := hA_pos.mpr hpa
      have h2 := hB_pos.mpr ((hsame p hp).mp hpa)
      omega
    · have h1 : A.factorization p = 0 := by
        by_contra hne; exact hpa (hA_pos.mp (Nat.pos_of_ne_zero hne))
      have h2 : B.factorization p = 0 := by
        by_contra hne; exact hpa ((hsame p hp).mpr (hB_pos.mp (Nat.pos_of_ne_zero hne)))
      omega
  · rw [Nat.factorization_eq_zero_of_not_prime A hp, Nat.factorization_eq_zero_of_not_prime B hp]

private lemma prime_dvd_radical_iff {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    p ∣ UniqueFactorizationMonoid.radical m ↔ p ∣ m :=
  UniqueFactorizationMonoid.dvd_radical_iff_of_irreducible hp.prime.irreducible hm

private lemma not_sq_dvd_radical {p m : ℕ} (hp : p.Prime) :
    ¬ p ^ 2 ∣ UniqueFactorizationMonoid.radical m := by
  intro hsq
  have hsf : Squarefree (UniqueFactorizationMonoid.radical m) :=
    UniqueFactorizationMonoid.squarefree_radical
  have hunit : IsUnit p := hsf p (by simpa [pow_two] using hsq)
  exact hp.ne_one (Nat.isUnit_iff.mp hunit)

private lemma odd_geom_sum_dvd {Q d : ℕ} (hd : Odd d) :
    Q + 1 ∣ Q ^ d + 1 := by
  simpa using hd.nat_add_dvd_pow_add_pow Q 1

private lemma odd_pow_add_one_quot_not_dvd {p Q d : ℕ} (_hp : p.Prime) (hd : Odd d)
    (hQ : p ∣ Q + 1) (hpd : ¬ p ∣ d) :
    ¬ p ∣ (Q ^ d + 1) / (Q + 1) := by
  intro hdvd
  have hQ1 : Q + 1 ≠ 0 := by omega
  have hdiv : Q + 1 ∣ Q ^ d + 1 := odd_geom_sum_dvd hd
  have hsum : (∑ j ∈ Finset.range d, (-1 : ℤ) ^ j * (Q : ℤ) ^ j) * ((Q : ℤ) + 1) =
      (Q : ℤ) ^ d + 1 := by
    have h1 := geom_sum_mul (-(Q : ℤ)) d
    have hneg : (-(Q : ℤ)) ^ d = -((Q : ℤ) ^ d) := hd.neg_pow (Q : ℤ)
    have hterm : ∀ j ∈ Finset.range d, (-(Q : ℤ)) ^ j = (-1 : ℤ) ^ j * (Q : ℤ) ^ j := by
      intro j _; rw [neg_eq_neg_one_mul, mul_pow]
    rw [Finset.sum_congr rfl hterm] at h1
    linarith
  have hq_eq : (((Q ^ d + 1) / (Q + 1) : ℕ) : ℤ) =
      ∑ j ∈ Finset.range d, (-1 : ℤ) ^ j * (Q : ℤ) ^ j := by
    have hmul : (((Q ^ d + 1) / (Q + 1) : ℕ) : ℤ) * ((Q : ℤ) + 1) = (Q : ℤ) ^ d + 1 := by
      exact_mod_cast Nat.div_mul_cancel hdiv
    have hne : (Q : ℤ) + 1 ≠ 0 := by positivity
    exact mul_right_cancel₀ hne (hmul.trans hsum.symm)
  have hpZ : (p : ℤ) ∣ ∑ j ∈ Finset.range d, (-1 : ℤ) ^ j * (Q : ℤ) ^ j := by
    rw [← hq_eq]; exact_mod_cast hdvd
  have hmod : (∑ j ∈ Finset.range d, (-1 : ℤ) ^ j * (Q : ℤ) ^ j : ZMod p) = (d : ZMod p) := by
    have hQmod : (Q : ZMod p) = -1 := by
      have : ((Q + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hQ
      push_cast at this
      exact eq_neg_of_add_eq_zero_left this
    push_cast
    simp only [hQmod, ← mul_pow, neg_mul, one_mul, neg_neg, one_pow, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul, mul_one]
  have hsum0 : ((∑ j ∈ Finset.range d, (-1 : ℤ) ^ j * (Q : ℤ) ^ j : ℤ) : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hpZ
  have hd0 : (d : ZMod p) = 0 := by
    rw [← hmod]
    simpa using hsum0
  exact hpd ((ZMod.natCast_eq_zero_iff d p).mp hd0)

private lemma odd_prime_lte_step {p R : ℕ} (hp : p.Prime) (hp2 : 2 < p) (hR : p ∣ R + 1) :
    ¬ p ^ 2 ∣ (R ^ p + 1) / (R + 1) := by
  intro hsq
  have hp_odd : Odd p := hp.odd_of_ne_two (by omega)
  have hdiv : R + 1 ∣ R ^ p + 1 := odd_geom_sum_dvd hp_odd
  have hsum : (∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (R : ℤ) ^ j) * ((R : ℤ) + 1) =
      (R : ℤ) ^ p + 1 := by
    have h1 := geom_sum_mul (-(R : ℤ)) p
    have hneg : (-(R : ℤ)) ^ p = -((R : ℤ) ^ p) := hp_odd.neg_pow (R : ℤ)
    have hterm : ∀ j ∈ Finset.range p, (-(R : ℤ)) ^ j = (-1 : ℤ) ^ j * (R : ℤ) ^ j := by
      intro j _; rw [neg_eq_neg_one_mul, mul_pow]
    rw [Finset.sum_congr rfl hterm] at h1
    linarith
  have hq_eq : (((R ^ p + 1) / (R + 1) : ℕ) : ℤ) =
      ∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (R : ℤ) ^ j := by
    have hmul : (((R ^ p + 1) / (R + 1) : ℕ) : ℤ) * ((R : ℤ) + 1) = (R : ℤ) ^ p + 1 := by
      exact_mod_cast Nat.div_mul_cancel hdiv
    have hne : (R : ℤ) + 1 ≠ 0 := by positivity
    exact mul_right_cancel₀ hne (hmul.trans hsum.symm)
  obtain ⟨t, ht⟩ := hR
  have hR_eq : (R : ℤ) = (p : ℤ) * (t : ℤ) - 1 := by omega
  have hterm_mod : ∀ j : ℕ, (-1 : ℤ) ^ j * (R : ℤ) ^ j ≡ 1 - (j : ℤ) * (p : ℤ) * (t : ℤ) [ZMOD (p : ℤ) ^ 2] := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have hstep : (-1 : ℤ) ^ (j + 1) * (R : ℤ) ^ (j + 1) =
          ((-1 : ℤ) ^ j * (R : ℤ) ^ j) * (1 - (p : ℤ) * (t : ℤ)) := by
        rw [pow_succ, pow_succ, hR_eq]; ring
      rw [hstep]
      have hmul := ih.mul_right (1 - (p : ℤ) * (t : ℤ))
      refine hmul.trans ?_
      rw [Int.modEq_iff_dvd]
      refine ⟨-(j : ℤ) * (t : ℤ) ^ 2, ?_⟩
      push_cast
      ring
  have hsum_mod : (∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (R : ℤ) ^ j) ≡
      ∑ j ∈ Finset.range p, (1 - (j : ℤ) * (p : ℤ) * (t : ℤ)) [ZMOD (p : ℤ) ^ 2] :=
    Int.ModEq.sum fun j _ => hterm_mod j
  have hsum_eval : (∑ j ∈ Finset.range p, (1 - (j : ℤ) * (p : ℤ) * (t : ℤ))) ≡
      (p : ℤ) [ZMOD (p : ℤ) ^ 2] := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    have h2 : ∑ j ∈ Finset.range p, (j : ℤ) * (p : ℤ) * (t : ℤ) =
        (∑ j ∈ Finset.range p, (j : ℤ)) * ((p : ℤ) * (t : ℤ)) := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => by ring
    rw [h2]
    have hdiv2 : (p : ℤ) ∣ ∑ j ∈ Finset.range p, (j : ℤ) := by
      rcases hp_odd with ⟨m, hm⟩
      have hnat : ∑ i ∈ Finset.range p, i = p * m := by
        have h1 := Finset.sum_range_id p
        have h2 : p * (p - 1) = 2 * (p * m) := by
          have : p - 1 = 2 * m := by omega
          rw [this]; ring
        rw [h1, h2, Nat.mul_div_cancel_left _ (by decide)]
      refine ⟨(m : ℤ), ?_⟩
      calc (∑ j ∈ Finset.range p, (j : ℤ)) = ((∑ j ∈ Finset.range p, j : ℕ) : ℤ) := by push_cast; rfl
        _ = ((p * m : ℕ) : ℤ) := by rw [hnat]
        _ = (p : ℤ) * (m : ℤ) := by push_cast; rfl
    obtain ⟨w, hw⟩ := hdiv2
    rw [hw, Int.modEq_iff_dvd]
    exact ⟨w * (t : ℤ), by ring⟩
  have htot := hsum_mod.trans hsum_eval
  have hsqZ : (p : ℤ) ^ 2 ∣ ∑ j ∈ Finset.range p, (-1 : ℤ) ^ j * (R : ℤ) ^ j := by
    rw [← hq_eq]; exact_mod_cast hsq
  have hp_dvd : (p : ℤ) ^ 2 ∣ (p : ℤ) := (Int.ModEq.dvd_iff htot).mp hsqZ
  have hnat_dvd : p ^ 2 ∣ p := by exact_mod_cast hp_dvd
  have hle : p ^ 2 ≤ p := Nat.le_of_dvd hp.pos hnat_dvd
  nlinarith

private lemma padicValNat_odd_pow_add_one {p Q : ℕ} (hp : p.Prime) (hp2 : 2 < p)
    (hQ : p ∣ Q + 1) :
    ∀ d : ℕ, Odd d →
      padicValNat p (Q ^ d + 1) ≤ padicValNat p (Q + 1) + padicValNat p d := by
  have _ : Fact p.Prime := ⟨hp⟩
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    have hdiv : Q + 1 ∣ Q ^ d + 1 := odd_geom_sum_dvd hd
    have hpos1 : Q + 1 ≠ 0 := by omega
    have hpos2 : (Q ^ d + 1) / (Q + 1) ≠ 0 := by
      intro h0
      have hmul := Nat.div_mul_cancel hdiv
      rw [h0, zero_mul] at hmul
      omega
    have hsplit : padicValNat p (Q ^ d + 1) =
        padicValNat p (Q + 1) + padicValNat p ((Q ^ d + 1) / (Q + 1)) := by
      conv_lhs => rw [← Nat.mul_div_cancel' hdiv]
      exact padicValNat.mul hpos1 hpos2
    by_cases hpd : p ∣ d
    · obtain ⟨d', rfl⟩ := hpd
      have hd'_pos : 0 < d' := by
        rcases Nat.eq_zero_or_pos d' with rfl | h
        · simp at hd
        · exact h
      have hd'_odd : Odd d' := by
        rcases Nat.even_or_odd d' with ⟨t, ht⟩ | ho
        · exfalso
          exact (Nat.not_even_iff_odd.mpr hd) ⟨p * t, by rw [ht]; ring⟩
        · exact ho
      have hd'_lt : d' < p * d' := lt_mul_of_one_lt_left hd'_pos hp.one_lt
      have ih' := ih d' hd'_lt hd'_odd
      have hQ'_dvd : p ∣ Q ^ d' + 1 := hQ.trans (odd_geom_sum_dvd hd'_odd)
      have hstep_div : Q ^ d' + 1 ∣ (Q ^ d') ^ p + 1 :=
        odd_geom_sum_dvd (hp.odd_of_ne_two (by omega))
      have hpow_eq : Q ^ (p * d') + 1 = (Q ^ d') ^ p + 1 := by rw [mul_comm, pow_mul]
      have hqpos : ((Q ^ d') ^ p + 1) / (Q ^ d' + 1) ≠ 0 := by
        intro h0
        have hmul := Nat.div_mul_cancel hstep_div
        rw [h0, zero_mul] at hmul
        omega
      have hval_step : padicValNat p (Q ^ (p * d') + 1) =
          padicValNat p (Q ^ d' + 1) + padicValNat p (((Q ^ d') ^ p + 1) / (Q ^ d' + 1)) := by
        rw [hpow_eq]
        conv_lhs => rw [← Nat.mul_div_cancel' hstep_div]
        exact padicValNat.mul (by omega) hqpos
      have hle1 : padicValNat p (((Q ^ d') ^ p + 1) / (Q ^ d' + 1)) ≤ 1 := by
        by_contra hgt
        have hge2 : 2 ≤ padicValNat p (((Q ^ d') ^ p + 1) / (Q ^ d' + 1)) := by omega
        exact odd_prime_lte_step hp hp2 hQ'_dvd
          ((hp.pow_dvd_iff_le_factorization hqpos).mpr (by rw [Nat.factorization_def _ hp]; exact hge2))
      have hd_val : padicValNat p (p * d') = 1 + padicValNat p d' := by
        rw [padicValNat.mul hp.ne_zero (by omega), padicValNat.self hp.one_lt]
      omega
    · have hndvd := odd_pow_add_one_quot_not_dvd hp hd hQ hpd
      have h0 : padicValNat p ((Q ^ d + 1) / (Q + 1)) = 0 :=
        padicValNat.eq_zero_of_not_dvd hndvd
      omega

private lemma pow_add_one_gt_mul {Q d : ℕ} (hQ : 3 ≤ Q) (hd : 3 ≤ d) :
    d * (Q + 1) < Q ^ d + 1 := by
  induction d, hd using Nat.le_induction with
  | base =>
    have : Q ^ 3 = Q * Q * Q := by ring
    nlinarith
  | succ m hm ih =>
    rw [pow_succ']
    nlinarith [Nat.one_le_pow m Q (by omega)]

private lemma exponent_is_pow_two {p q r c : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2 < p) (hq2 : 2 < q) (hr : 1 ≤ r) (heq : p ^ r + 1 = 2 * q ^ c) :
    ∃ k : ℕ, r = 2 ^ k := by
  have _ : Fact q.Prime := ⟨hq⟩
  let k := padicValNat 2 r
  let d := r / 2 ^ k
  have h2k_dvd : 2 ^ k ∣ r := pow_padicValNat_dvd
  have hr_eq : r = 2 ^ k * d := (Nat.mul_div_cancel' h2k_dvd).symm
  have hd_pos : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h0 | hpos
    · rw [h0, mul_zero] at hr_eq; omega
    · exact hpos
  have hd_odd : Odd d := by
    by_contra hnot
    have hev : Even d := Nat.not_odd_iff_even.mp hnot
    obtain ⟨t, ht⟩ := hev
    have h2k1 : 2 ^ (k + 1) ∣ r := by
      refine ⟨t, ?_⟩
      rw [hr_eq, pow_succ, ht]; ring
    have _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hle : k + 1 ≤ padicValNat 2 r := by
      rw [← Nat.factorization_def _ Nat.prime_two]
      exact (Nat.prime_two.pow_dvd_iff_le_factorization (by omega)).mp h2k1
    omega
  refine ⟨k, ?_⟩
  suffices hd1 : d = 1 by rw [hr_eq, hd1, mul_one]
  by_contra hne1
  have hd3 : 3 ≤ d := by rcases hd_odd with ⟨m, hm⟩; omega
  let Q := p ^ (2 ^ k)
  have hQ3 : 3 ≤ Q := by
    have : p ≤ p ^ (2 ^ k) := by
      simpa [pow_one] using Nat.pow_le_pow_right hp.pos (Nat.one_le_pow k 2 (by decide))
    omega
  have hQ_odd : Odd Q := (hp.odd_of_ne_two (by omega)).pow
  have hQd : Q ^ d + 1 = 2 * q ^ c := by
    simpa [Q, ← pow_mul, ← hr_eq] using heq
  have hdiv : Q + 1 ∣ 2 * q ^ c := hQd ▸ odd_geom_sum_dvd hd_odd
  have hQ1_even : 2 ∣ Q + 1 := by rcases hQ_odd with ⟨t, ht⟩; exact ⟨t + 1, by omega⟩
  obtain ⟨m, hm⟩ := hQ1_even
  have hm_dvd : m ∣ q ^ c := by
    have : 2 * m ∣ 2 * q ^ c := hm ▸ hdiv
    exact (mul_dvd_mul_iff_left (by decide : 2 ≠ 0)).mp this
  obtain ⟨u, huc, rfl⟩ := (Nat.dvd_prime_pow hq).mp hm_dvd
  have hu1 : 1 ≤ u := by
    by_contra hu0
    have : u = 0 := by omega
    subst this
    simp only [pow_zero, mul_one] at hm
    omega
  have hq_dvd_Q1 : q ∣ Q + 1 := by
    rw [hm]
    exact dvd_mul_of_dvd_right (dvd_pow_self q (by omega)) 2
  have hlte := padicValNat_odd_pow_add_one hq hq2 hq_dvd_Q1 d hd_odd
  have hval_Qd : padicValNat q (Q ^ d + 1) = c := by
    rw [hQd, padicValNat.mul (by decide) (pow_ne_zero c hq.ne_zero),
      padicValNat.eq_zero_of_not_dvd (by
        intro h; have := Nat.le_of_dvd (by decide) h; omega),
      zero_add, padicValNat.prime_pow]
  have hval_Q1 : padicValNat q (Q + 1) = u := by
    rw [hm, padicValNat.mul (by decide) (pow_ne_zero u hq.ne_zero),
      padicValNat.eq_zero_of_not_dvd (by
        intro h; have := Nat.le_of_dvd (by decide) h; omega),
      zero_add, padicValNat.prime_pow]
  have hle_diff : c - u ≤ padicValNat q d := by omega
  have hpow_le : q ^ (c - u) ≤ d := by
    calc q ^ (c - u) ≤ q ^ padicValNat q d := Nat.pow_le_pow_right hq.pos hle_diff
      _ ≤ d := Nat.le_of_dvd hd_pos pow_padicValNat_dvd
  have hquot : Q ^ d + 1 = (Q + 1) * q ^ (c - u) := by
    rw [hQd, hm]
    have : q ^ u * q ^ (c - u) = q ^ c := by rw [← pow_add, Nat.add_sub_of_le huc]
    calc 2 * q ^ c = 2 * (q ^ u * q ^ (c - u)) := by rw [this]
      _ = 2 * q ^ u * q ^ (c - u) := by ring
  have hbig := pow_add_one_gt_mul hQ3 hd3
  have hsmall : (Q + 1) * q ^ (c - u) ≤ d * (Q + 1) := by
    rw [mul_comm]
    exact Nat.mul_le_mul_right (Q + 1) hpow_le
  omega

private lemma two_prime_s_eq_one_forces_fifteen {p q a c k : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hp2 : 2 < p) (ha : 1 ≤ a) (hc : 1 ≤ c) (hk : 1 ≤ k)
    (h1 : p ^ (2 ^ k) + 1 = 2 * q ^ c) (h2 : q + 1 = 2 * p ^ a) :
    p ^ a * q ^ c = 15 := by
  have hmodp : ((p ^ (2 ^ k) + 1 : ℕ) : ZMod p) = ((2 * q ^ c : ℕ) : ZMod p) := by
    rw [h1]
  have hp2k : (p : ZMod p) ^ (2 ^ k) = 0 := by
    rw [ZMod.natCast_self, zero_pow (pow_ne_zero k (by decide))]
  have hqmod : (q : ZMod p) = -1 := by
    have : ((q + 1 : ℕ) : ZMod p) = 0 := by
      rw [h2]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_mul_of_dvd_right (dvd_pow_self p (by omega)) 2)
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  push_cast at hmodp
  rw [hp2k, zero_add, hqmod] at hmodp
  have hc_odd : Odd c := by
    by_contra hnot
    have hev : Even c := Nat.not_odd_iff_even.mp hnot
    rw [hev.neg_one_pow, mul_one] at hmodp
    have h10 : (1 : ZMod p) = 0 := by linear_combination -hmodp
    have _ : Fact p.Prime := ⟨hp⟩
    exact one_ne_zero h10
  rw [hc_odd.neg_one_pow] at hmodp
  have h30 : (3 : ZMod p) = 0 := by
    have : (1 : ZMod p) + 2 = 0 := by linear_combination hmodp
    simpa [show (1 : ZMod p) + 2 = 3 by norm_num] using this
  have hp3 : p = 3 := by
    have hdvd : p ∣ 3 := (ZMod.natCast_eq_zero_iff 3 p).mp h30
    have hle : p ≤ 3 := Nat.le_of_dvd (by decide) hdvd
    omega
  subst hp3
  -- Reduce mod 9 to force a = 1
  have h2k_ge2 : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by ring
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk
  have ha1 : a = 1 := by
    by_contra hne1
    have ha2 : 2 ≤ a := by omega
    have hmod9 : ((3 ^ (2 ^ k) + 1 : ℕ) : ZMod 9) = ((2 * q ^ c : ℕ) : ZMod 9) := by rw [h1]
    have h3_9 : ((3 ^ (2 ^ k) : ℕ) : ZMod 9) = 0 := by
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (by
        have : 3 ^ 2 ∣ 3 ^ (2 ^ k) := pow_dvd_pow 3 h2k_ge2
        simpa using this)
    have hq9 : (q : ZMod 9) = -1 := by
      have h9dvd : 9 ∣ q + 1 := by
        rw [h2]
        have : 3 ^ 2 ∣ 3 ^ a := pow_dvd_pow 3 ha2
        exact dvd_mul_of_dvd_right (by simpa using this) 2
      have : ((q + 1 : ℕ) : ZMod 9) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr h9dvd
      push_cast at this
      exact eq_neg_of_add_eq_zero_left this
    push_cast at hmod9
    have h3_9' : (3 : ZMod 9) ^ (2 ^ k) = 0 := by simpa using h3_9
    rw [h3_9', zero_add, hq9, hc_odd.neg_one_pow] at hmod9
    have : (1 : ZMod 9) = -2 := by simpa using hmod9
    exact (by decide : (1 : ZMod 9) ≠ -2) this
  subst ha1
  have hq5 : q = 5 := by omega
  subst hq5
  -- Now 3^(2^k) + 1 = 2 * 5^c; check mod 5 for k ≥ 2
  have hk1 : k = 1 := by
    by_contra hne1
    have hk2 : 2 ≤ k := by omega
    have hdiv4 : 4 ∣ 2 ^ k := by
      have : 2 ^ 2 ∣ 2 ^ k := pow_dvd_pow 2 hk2
      simpa using this
    obtain ⟨m, hm⟩ := hdiv4
    have hmod5 : ((3 ^ (2 ^ k) + 1 : ℕ) : ZMod 5) = 0 := by
      rw [h1]
      exact (ZMod.natCast_eq_zero_iff _ _).mpr (dvd_mul_of_dvd_right (dvd_pow_self 5 (by omega)) 2)
    have h34 : ((3 ^ (2 ^ k) : ℕ) : ZMod 5) = 1 := by
      rw [hm, pow_mul]
      push_cast
      have : (81 : ZMod 5) = 1 := by decide
      rw [this, one_pow]
    push_cast at hmod5
    have h34' : (3 : ZMod 5) ^ (2 ^ k) = 1 := by simpa using h34
    rw [h34'] at hmod5
    exact (by decide : (1 : ZMod 5) + 1 ≠ 0) hmod5
  subst hk1
  have hc1 : c = 1 := by
    have : 5 ^ c = 5 := by omega
    by_contra hne
    have : 5 ^ 2 ≤ 5 ^ c := Nat.pow_le_pow_right (by decide) (by omega)
    omega
  subst hc1
  norm_num

end Helpers

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a395746.main := by
  intro hH1 hH2 n hn hne15
  have h2n1_ge3 : 3 ≤ 2 * n - 1 := by omega
  have hprod_ne0 : n * (2 * n - 1) ≠ 0 := by positivity
  have hg_ne0 : evenBinomialGcd n ≠ 0 := (evenBinomialGcd_pos hn).ne'
  have hrad_ne0 : UniqueFactorizationMonoid.radical (n * (2 * n - 1)) ≠ 0 :=
    UniqueFactorizationMonoid.radical_ne_zero
  constructor
  · -- Forward direction: evenBinomialGcd n = radical (n * (2n - 1)) → IsPrimePow n ∧ IsPrimePow (2n - 1)
    intro heq
    -- Step 1: 2n - 1 is a prime power
    have h2n1_pp : IsPrimePow (2 * n - 1) := by
      obtain ⟨w, hw, hwdvd⟩ := Nat.exists_prime_and_dvd (show 2 * n - 1 ≠ 1 by omega)
      have hw_odd : 2 < w := by
        have h2 := hw.two_le
        have hne2 : w ≠ 2 := by
          rintro rfl
          obtain ⟨t, ht⟩ := hwdvd
          omega
        omega
      have hw_rad : w ∣ UniqueFactorizationMonoid.radical (n * (2 * n - 1)) :=
        (prime_dvd_radical_iff hw hprod_ne0).mpr (dvd_mul_of_dvd_right hwdvd n)
      rw [← heq] at hw_rad
      rcases (odd_prime_dvd_evenBinomialGcd_iff hw hw_odd hn).mp hw_rad with
        ⟨a, ha1, hn_eq⟩ | ⟨a, b, hab, h2n_eq⟩
      · exfalso
        have hwn : w ∣ n := by rw [hn_eq]; exact dvd_pow_self w (by omega)
        have hw1 : w ∣ 1 := by
          have h1 : w ∣ 2 * n := dvd_mul_of_dvd_right hwn 2
          have h2 := Nat.dvd_sub h1 hwdvd
          have : 2 * n - (2 * n - 1) = 1 := by omega
          rwa [this] at h2
        exact hw.not_dvd_one hw1
      · rcases Nat.eq_zero_or_pos a with rfl | ha1
        · have h2n1_eq : 2 * n - 1 = w ^ b := by rw [pow_zero] at h2n_eq; omega
          rw [h2n1_eq]
          exact hw.prime.isPrimePow.pow (by omega)
        · exfalso
          have hw2n : w ∣ 2 * n := by
            rw [h2n_eq]
            exact dvd_add (dvd_pow_self w (by omega)) (dvd_pow_self w (by omega))
          have hw1 : w ∣ 1 := by
            have h2 := Nat.dvd_sub hw2n hwdvd
            have : 2 * n - (2 * n - 1) = 1 := by omega
            rwa [this] at h2
          exact hw.not_dvd_one hw1
    refine ⟨?_, h2n1_pp⟩
    -- Step 2: n is a prime power
    by_contra hnot_pp
    -- n cannot be even (else 2 | g(n) ⇒ n = 2^a, prime power)
    have hn_odd : Odd n := by
      rcases Nat.even_or_odd n with hev | hodd
      · exfalso
        have h2n : 2 ∣ n := even_iff_two_dvd.mp hev
        have h2rad : 2 ∣ UniqueFactorizationMonoid.radical (n * (2 * n - 1)) :=
          (prime_dvd_radical_iff Nat.prime_two hprod_ne0).mpr (dvd_mul_of_dvd_left h2n _)
        rw [← heq] at h2rad
        obtain ⟨a, ha1, rfl⟩ := (two_dvd_evenBinomialGcd_iff hn).mp h2rad
        exact hnot_pp (Nat.prime_two.prime.isPrimePow.pow (by omega))
      · exact hodd
    -- Every prime p ∈ n.primeFactors satisfies p^(v_p(n)) * (p^r + 1) = 2 * n for some r ≥ 1
    have hrep : ∀ p ∈ n.primeFactors,
        ∃ r : ℕ, 1 ≤ r ∧ p ^ (n.factorization p) * (p ^ r + 1) = 2 * n := by
      intro p hp_mem
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hp_mem
      have hp2 : 2 < p := by
        have := hp.two_le
        have hne2 : p ≠ 2 := by
          rintro rfl
          exact (Nat.not_even_iff_odd.mpr hn_odd) (even_iff_two_dvd.mpr hpn)
        omega
      have hp_rad : p ∣ UniqueFactorizationMonoid.radical (n * (2 * n - 1)) :=
        (prime_dvd_radical_iff hp hprod_ne0).mpr (dvd_mul_of_dvd_left hpn _)
      rw [← heq] at hp_rad
      rcases (odd_prime_dvd_evenBinomialGcd_iff hp hp2 hn).mp hp_rad with
        ⟨a, ha1, hn_eq⟩ | ⟨a, b, hab, h2n_eq⟩
      · exfalso
        exact hnot_pp (hn_eq ▸ hp.prime.isPrimePow.pow (by omega))
      · have ha_eq : a = n.factorization p := by
          have _ : Fact p.Prime := ⟨hp⟩
          have h1 : 2 * n = p ^ a * (1 + p ^ (b - a)) := by
            rw [h2n_eq, mul_add, mul_one, ← pow_add, Nat.add_sub_of_le hab.le]
          have hndvd : ¬ p ∣ 1 + p ^ (b - a) := by
            intro h
            have : p ∣ 1 := (Nat.dvd_add_left (dvd_pow_self p (by omega))).mp h
            exact hp.not_dvd_one this
          have hval2n : (2 * n).factorization p = n.factorization p := by
            rw [Nat.factorization_mul (by decide) (by omega), Finsupp.add_apply,
              Nat.factorization_eq_zero_of_not_dvd (by
                intro h; have := Nat.le_of_dvd (by decide) h; omega), zero_add]
          rw [← hval2n, h1, Nat.factorization_mul (pow_ne_zero a hp.ne_zero) (by omega),
            Finsupp.add_apply, hp.factorization_pow, Finsupp.single_eq_same,
            Nat.factorization_eq_zero_of_not_dvd hndvd, add_zero]
        refine ⟨b - a, by omega, ?_⟩
        rw [← ha_eq, mul_add, mul_one, ← pow_add, Nat.add_sub_of_le hab.le, add_comm, h2n_eq]
    -- Count distinct prime factors of n: must be ≥ 2
    have hcard_ge2 : 2 ≤ n.primeFactors.card := by
      by_contra hlt2
      have hcard_le1 : n.primeFactors.card ≤ 1 := by omega
      rcases Nat.eq_zero_or_pos n.primeFactors.card with h0 | hpos
      · have : n = 1 := by
          obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
          have hmem : p ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpn, by omega⟩
          have : 0 < n.primeFactors.card := Finset.card_pos.mpr ⟨p, hmem⟩
          omega
        omega
      · have hcard1 : n.primeFactors.card = 1 := by omega
        obtain ⟨p, hp_eq⟩ := Finset.card_eq_one.mp hcard1
        have hp_mem : p ∈ n.primeFactors := by rw [hp_eq]; exact Finset.mem_singleton_self p
        have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
        have hfac_eq : n = p ^ (n.factorization p) := by
          conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (by omega : n ≠ 0)]
          rw [Finsupp.prod, Nat.support_factorization, hp_eq, Finset.prod_singleton]
        have hvp_pos : 1 ≤ n.factorization p := by
          rw [← hp.pow_dvd_iff_le_factorization (by omega), pow_one]
          exact Nat.dvd_of_mem_primeFactors hp_mem
        exact hnot_pp (hfac_eq ▸ hp.prime.isPrimePow.pow (by omega))
    -- Split: card ≥ 3 → H2; card = 2 → H1 + uniqueness of 15
    by_cases hcard3 : 3 ≤ n.primeFactors.card
    · exact hH2 n hn_odd hcard3 h2n1_pp hrep
    · have hcard2 : n.primeFactors.card = 2 := by omega
      obtain ⟨p₀, q₀, hpq_ne, hpf_eq⟩ := Finset.card_eq_two.mp hcard2
      -- Order p < q
      let p := min p₀ q₀
      let q := max p₀ q₀
      have hpq_lt : p < q := by
        dsimp [p, q]
        rcases lt_or_gt_of_ne hpq_ne with h | h
        · rw [min_eq_left h.le, max_eq_right h.le]; exact h
        · rw [min_eq_right h.le, max_eq_left h.le]; exact h
      have hpf_pq : n.primeFactors = {p, q} := by
        rw [hpf_eq]; dsimp [p, q]
        rcases lt_or_gt_of_ne hpq_ne with h | h
        · rw [min_eq_left h.le, max_eq_right h.le]
        · rw [min_eq_right h.le, max_eq_left h.le, Finset.pair_comm]
      have hp_mem : p ∈ n.primeFactors := by rw [hpf_pq]; simp
      have hq_mem : q ∈ n.primeFactors := by rw [hpf_pq]; simp
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hq : q.Prime := Nat.prime_of_mem_primeFactors hq_mem
      have hp2 : 2 < p := by
        have := hp.two_le
        have hne2 : p ≠ 2 := by
          intro hp_eq
          have h2n : 2 ∣ n := hp_eq ▸ Nat.dvd_of_mem_primeFactors hp_mem
          exact (Nat.not_even_iff_odd.mpr hn_odd) (even_iff_two_dvd.mpr h2n)
        omega
      have hq2 : 2 < q := by omega
      let a := n.factorization p
      let c := n.factorization q
      have ha1 : 1 ≤ a := by
        rw [← hp.pow_dvd_iff_le_factorization (by omega), pow_one]
        exact Nat.dvd_of_mem_primeFactors hp_mem
      have hc1 : 1 ≤ c := by
        rw [← hq.pow_dvd_iff_le_factorization (by omega), pow_one]
        exact Nat.dvd_of_mem_primeFactors hq_mem
      have hn_fac : n = p ^ a * q ^ c := by
        conv_lhs => rw [← Nat.prod_factorization_pow_eq_self (by omega : n ≠ 0)]
        rw [Finsupp.prod, Nat.support_factorization, hpf_pq, Finset.prod_pair hpq_lt.ne]
      obtain ⟨r, hr1, hr_eq⟩ := hrep p hp_mem
      obtain ⟨s, hs1, hs_eq⟩ := hrep q hq_mem
      have hpr : p ^ r + 1 = 2 * q ^ c := by
        have hmul : p ^ a * (p ^ r + 1) = p ^ a * (2 * q ^ c) := by
          rw [hr_eq, hn_fac]; ring
        exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos a) hmul
      have hqs : q ^ s + 1 = 2 * p ^ a := by
        have hmul : q ^ c * (q ^ s + 1) = q ^ c * (2 * p ^ a) := by
          rw [hs_eq, hn_fac]; ring
        exact Nat.eq_of_mul_eq_mul_left (pow_pos hq.pos c) hmul
      obtain ⟨k, rfl⟩ := exponent_is_pow_two hp hq hp2 hq2 hr1 hpr
      obtain ⟨ℓ, rfl⟩ := exponent_is_pow_two hq hp hq2 hp2 hs1 hqs
      have hk1 : 1 ≤ k := by
        by_contra hk0
        have : k = 0 := by omega
        subst this
        simp only [pow_zero, pow_one] at hpr
        have hqc : q ≤ q ^ c := le_self_pow₀ hq.one_lt.le (by omega)
        omega
      rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ1
      · simp only [pow_zero, pow_one] at hqs
        have h15 := two_prime_s_eq_one_forces_fifteen hp hq hp2 ha1 hc1 hk1 hpr hqs
        exact hne15 (hn_fac.trans h15)
      · exact hH1 p q a c k ℓ hp hq hp2 hpq_lt ha1 hc1 hk1 hℓ1 hpr hqs
          (by rw [mul_assoc, ← hn_fac]; exact h2n1_pp)
  · -- Backward direction: IsPrimePow n ∧ IsPrimePow (2n - 1) → evenBinomialGcd n = radical (n*(2n-1))
    rintro ⟨hn_pp, h2n1_pp⟩
    obtain ⟨p₀, a₀, hp₀_prime, ha₀_pos, hn_eq⟩ := (isPrimePow_nat_iff n).mp hn_pp
    obtain ⟨q₀, b₀, hq₀_prime, hb₀_pos, h2n1_eq⟩ := (isPrimePow_nat_iff (2 * n - 1)).mp h2n1_pp
    have hq₀_odd : 2 < q₀ := by
      have := hq₀_prime.two_le
      have hne2 : q₀ ≠ 2 := by
        rintro rfl
        have : 2 ∣ 2 * n - 1 := by rw [← h2n1_eq]; exact dvd_pow_self 2 (by omega)
        obtain ⟨t, ht⟩ := this
        omega
      omega
    apply eq_of_squarefree_same_prime_dvd hg_ne0 hrad_ne0
    · intro p hp; exact not_sq_dvd_evenBinomialGcd hp hn
    · intro p hp; exact not_sq_dvd_radical hp
    · intro p hp
      rw [prime_dvd_radical_iff hp hprod_ne0, hp.dvd_mul]
      constructor
      · intro hdvd
        rcases hp.eq_two_or_odd with rfl | _
        · obtain ⟨a, ha1, rfl⟩ := (two_dvd_evenBinomialGcd_iff hn).mp hdvd
          left; exact dvd_pow_self 2 (by omega)
        · have hp2 : 2 < p := by have := hp.two_le; omega
          rcases (odd_prime_dvd_evenBinomialGcd_iff hp hp2 hn).mp hdvd with
            ⟨a, ha1, rfl⟩ | ⟨a, b, hab, h2n_eq⟩
          · left; exact dvd_pow_self p (by omega)
          · rcases Nat.eq_zero_or_pos a with rfl | ha1
            · right
              have : 2 * n - 1 = p ^ b := by rw [pow_zero] at h2n_eq; omega
              rw [this]; exact dvd_pow_self p (by omega)
            · left
              have h2n_dvd : p ∣ 2 * n := by
                rw [h2n_eq]; exact dvd_add (dvd_pow_self p (by omega)) (dvd_pow_self p (by omega))
              have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
              exact hcop.dvd_of_dvd_mul_left h2n_dvd
      · rintro (hpn | hp2n1)
        · have hp_eq : p = p₀ := by
            have : p ∣ p₀ ^ a₀ := hn_eq.symm ▸ hpn
            exact (Nat.prime_dvd_prime_iff_eq hp hp₀_prime).mp (hp.dvd_of_dvd_pow this)
          subst hp_eq
          rcases hp.eq_two_or_odd with rfl | _
          · exact (two_dvd_evenBinomialGcd_iff hn).mpr ⟨a₀, ha₀_pos, hn_eq.symm⟩
          · have hp2 : 2 < p := by have := hp.two_le; omega
            exact (odd_prime_dvd_evenBinomialGcd_iff hp hp2 hn).mpr (Or.inl ⟨a₀, ha₀_pos, hn_eq.symm⟩)
        · have hp_eq : p = q₀ := by
            have : p ∣ q₀ ^ b₀ := h2n1_eq.symm ▸ hp2n1
            exact (Nat.prime_dvd_prime_iff_eq hp hq₀_prime).mp (hp.dvd_of_dvd_pow this)
          subst hp_eq
          refine (odd_prime_dvd_evenBinomialGcd_iff hp hq₀_odd hn).mpr (Or.inr ⟨0, b₀, hb₀_pos, ?_⟩)
          rw [pow_zero]; omega

end OMA.R_oeis_a395746_R1
