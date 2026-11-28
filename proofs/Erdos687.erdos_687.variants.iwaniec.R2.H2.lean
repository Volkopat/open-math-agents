import OMAReductions.R_Erdos687_erdos_687_variants_iwaniec_R2
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Log

-- Step Erdos687.erdos_687.variants.iwaniec.R2.H2: hypothesis H2 of reduction Erdos687.erdos_687.variants.iwaniec.R2
-- Credit: @KevinBigham

/-!
# Proof of `Erdos687.erdos_687.variants.iwaniec.R2.H2`

We prove the summed progression upper sieve over the prime band `(x/2, x]` via:
1. An elementary Chebyshev upper bound on `|x.primesLE \ (x/2).primesLE|` using
   `∏_{x - x/2 < p ≤ x} p ∣ x.choose (x/2) ≤ 2^x`.
2. Selberg's `Λ²` upper bound sieve of level `D = 2^(x.log2 / 3)` on each
   arithmetic progression `n ≡ a p (mod p)` in `[1, x^2]`.
3. An elementary harmonic lower bound on the Selberg denominator
   `G(D) = ∑_{d ≤ D, sqfree} 1/φ(d) ≥ ∑_{j=1}^D 1/j ≥ 1 + (x.log2 / 3) / 2`.
-/

namespace Erdos687IwaniecR2H2

open Finset Filter
open scoped BigOperators

/- ## Section 1: Elementary Chebyshev prime count on `(x / 2, x]` -/

private lemma choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n := by
  by_cases hk : k ≤ n
  · calc
      n.choose k ≤ ∑ i ∈ Finset.range (n + 1), n.choose i :=
        Finset.single_le_sum (f := fun i => n.choose i) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
      _ = 2 ^ n := Nat.sum_range_choose n
  · rw [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hk)]
    exact Nat.zero_le _

private lemma prime_dvd_choose_half {x p : ℕ} (hp : p.Prime)
    (hgt : x - x / 2 < p) (hle : p ≤ x) : p ∣ x.choose (x / 2) := by
  have hhalf : x / 2 ≤ x := Nat.div_le_self x 2
  have hmul : x.choose (x / 2) * (x / 2).factorial * (x - x / 2).factorial = x.factorial :=
    Nat.choose_mul_factorial_mul_factorial hhalf
  have hdvdf : p ∣ x.factorial := hp.dvd_factorial.mpr hle
  rw [← hmul] at hdvdf
  have hnd1 : ¬ p ∣ (x - x / 2).factorial := by
    rw [hp.dvd_factorial]
    omega
  have hnd2 : ¬ p ∣ (x / 2).factorial := by
    rw [hp.dvd_factorial]
    omega
  have h1 : p ∣ x.choose (x / 2) * (x / 2).factorial :=
    (hp.dvd_mul.mp hdvdf).resolve_right hnd1
  exact (hp.dvd_mul.mp h1).resolve_right hnd2

private lemma prod_band_primes_le (x : ℕ) :
    (∏ p ∈ (x.primesLE \ (x / 2).primesLE).filter (fun p => x - x / 2 < p), p) ≤ 2 ^ x := by
  let B := (x.primesLE \ (x / 2).primesLE).filter (fun p => x - x / 2 < p)
  have hdvd : (∏ p ∈ B, p) ∣ x.choose (x / 2) := by
    have haux : ∀ T : Finset ℕ, (∀ p ∈ T, p.Prime ∧ p ∣ x.choose (x / 2)) →
        (∏ p ∈ T, p) ∣ x.choose (x / 2) := by
      intro T
      induction T using Finset.induction with
      | empty => intro _; simp
      | insert a T ha ih =>
        intro hT
        rw [Finset.prod_insert ha]
        have ha' := hT a (Finset.mem_insert_self a T)
        have hT' : ∀ p ∈ T, p.Prime ∧ p ∣ x.choose (x / 2) :=
          fun p hp => hT p (Finset.mem_insert_of_mem hp)
        have hcop : a.Coprime (∏ p ∈ T, p) :=
          Nat.Coprime.prod_right fun p hp =>
            (Nat.coprime_primes ha'.1 (hT' p hp).1).mpr (fun h => ha (h ▸ hp))
        exact hcop.mul_dvd_of_dvd_of_dvd ha'.2 (ih hT')
    apply haux
    intro p hp
    have hmem := Finset.mem_filter.mp hp
    have hpx := Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hmem.1).1
    exact ⟨hpx.2, prime_dvd_choose_half hpx.2 hmem.2 hpx.1⟩
  have hpos : 0 < x.choose (x / 2) := Nat.choose_pos (Nat.div_le_self x 2)
  exact (Nat.le_of_dvd hpos hdvd).trans (choose_le_two_pow x (x / 2))

private lemma two_pow_log2_le {x : ℕ} (hx : 1 ≤ x) : 2 ^ x.log2 ≤ x := by
  rw [Nat.log2_eq_log_two]
  exact Nat.pow_log_le_self 2 (by omega)

private lemma log2_ge_of_pow_le {x c : ℕ} (hx : 2 ^ c ≤ x) : c ≤ x.log2 := by
  rw [Nat.log2_eq_log_two]
  exact Nat.le_log_of_pow_le (by norm_num) hx

private lemma linear_le_pow_two : ∀ m : ℕ, 6 ≤ m → 3 * m + 3 ≤ 2 ^ m := by
  intro m hm
  induction m with
  | zero => omega
  | succ m ih =>
    by_cases h6 : 6 ≤ m
    · have := ih h6
      have h3 : 3 ≤ 2 ^ m := by
        have : 2 ^ 6 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) h6
        omega
      rw [Nat.pow_succ]
      omega
    · have hm5 : m = 5 := by omega
      subst hm5
      norm_num

private lemma card_primes_band_le {x : ℕ} (hx : 2 ^ 18 ≤ x) :
    ((x.primesLE \ (x / 2).primesLE).card : ℝ) ≤ 3 * (x : ℝ) / ((x.log2 + 1 : ℕ) : ℝ) := by
  set band := x.primesLE \ (x / 2).primesLE
  set B := band.filter (fun p => x - x / 2 < p)
  have hk18 : 18 ≤ x.log2 := log2_ge_of_pow_le hx
  have h2k : 2 ^ x.log2 ≤ x := two_pow_log2_le (by omega)
  have hcard_le : band.card ≤ B.card + 1 := by
    have hsub : band ⊆ insert (x / 2 + 1) B := by
      intro p hp
      have hmem := Finset.mem_sdiff.mp hp
      have hpx := Nat.mem_primesLE.mp hmem.1
      have hgt : x / 2 < p := by
        by_contra hle
        exact hmem.2 (Nat.mem_primesLE.mpr ⟨by omega, hpx.2⟩)
      by_cases hbig : x - x / 2 < p
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hp, hbig⟩)
      · exact Finset.mem_insert.mpr (Or.inl (by omega))
    exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hpow_le : 2 ^ ((x.log2 - 1) * B.card) ≤ 2 ^ x := by
    have hbase : ∀ p ∈ B, 2 ^ (x.log2 - 1) ≤ p := by
      intro p hp
      have hmem := Finset.mem_sdiff.mp (Finset.mem_filter.mp hp).1
      have hpx := Nat.mem_primesLE.mp hmem.1
      have hgt : x / 2 < p := by
        by_contra hle
        exact hmem.2 (Nat.mem_primesLE.mpr ⟨by omega, hpx.2⟩)
      have h2half : 2 ^ (x.log2 - 1) ≤ x / 2 := by
        have h1 : 2 ^ (x.log2 - 1) * 2 = 2 ^ x.log2 := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega)]
        omega
      omega
    calc
      2 ^ ((x.log2 - 1) * B.card) = (2 ^ (x.log2 - 1)) ^ B.card := by rw [Nat.pow_mul]
      _ = ∏ _p ∈ B, 2 ^ (x.log2 - 1) := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ B, p := Finset.prod_le_prod' hbase
      _ ≤ 2 ^ x := prod_band_primes_le x
  have hBmul : (x.log2 - 1) * B.card ≤ x :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hpow_le
  have hk_le_x : x.log2 + 1 ≤ x := by
    have hm : 6 ≤ x.log2 / 3 := by omega
    have hlin := linear_le_pow_two (x.log2 / 3) hm
    have hpow3 : 2 ^ (x.log2 / 3) ≤ 2 ^ x.log2 :=
      Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)
    omega
  have hnat : (x.log2 + 1) * band.card ≤ 3 * x := by
    have h1 : (x.log2 + 1) * band.card ≤ (x.log2 + 1) * (B.card + 1) :=
      Nat.mul_le_mul_left _ hcard_le
    have h2 : (x.log2 + 1) * B.card ≤ 2 * ((x.log2 - 1) * B.card) := by
      have hk2 : x.log2 + 1 ≤ 2 * (x.log2 - 1) := by omega
      calc
        (x.log2 + 1) * B.card ≤ (2 * (x.log2 - 1)) * B.card := Nat.mul_le_mul_right _ hk2
        _ = 2 * ((x.log2 - 1) * B.card) := by ring
    nlinarith
  have hpos : (0 : ℝ) < ((x.log2 + 1 : ℕ) : ℝ) := by positivity
  rw [le_div_iff₀ hpos]
  have hreal : ((band.card : ℝ)) * ((x.log2 + 1 : ℕ) : ℝ) ≤ 3 * (x : ℝ) := by
    have hcast : ((x.log2 + 1 : ℕ) : ℝ) * (band.card : ℝ) ≤ 3 * (x : ℝ) := by
      exact_mod_cast hnat
    linarith
  exact hreal

/- ## Section 2: Squarefree CRT and arithmetic progression count -/

private def congSys (a : ℕ → ℕ) (d n : ℕ) : Prop :=
  ∀ q ∈ d.primeFactors, n % q = a q % q

private instance (a : ℕ → ℕ) (d n : ℕ) : Decidable (congSys a d n) :=
  inferInstanceAs (Decidable (∀ q ∈ d.primeFactors, n % q = a q % q))

private lemma congSys_one (a : ℕ → ℕ) (n : ℕ) : congSys a 1 n := by
  intro q hq
  simp at hq

private lemma congSys_mul_iff (a : ℕ → ℕ) {d₁ d₂ : ℕ} (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (n : ℕ) :
    congSys a (d₁ * d₂) n ↔ congSys a d₁ n ∧ congSys a d₂ n := by
  unfold congSys
  rw [Nat.primeFactors_mul hd₁ hd₂]
  simp only [Finset.mem_union]
  constructor
  · intro h
    exact ⟨fun q hq => h q (Or.inl hq), fun q hq => h q (Or.inr hq)⟩
  · rintro ⟨h1, h2⟩ q (hq | hq)
    · exact h1 q hq
    · exact h2 q hq

private lemma congSys_prime_iff (a : ℕ → ℕ) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    congSys a p n ↔ n % p = a p % p := by
  unfold congSys
  rw [hp.primeFactors]
  simp

private lemma congSys_lcm_iff (a : ℕ → ℕ) {d₁ d₂ : ℕ} (hd₁ : d₁ ≠ 0) (hd₂ : d₂ ≠ 0) (n : ℕ) :
    congSys a (Nat.lcm d₁ d₂) n ↔ congSys a d₁ n ∧ congSys a d₂ n := by
  have hlcm0 : Nat.lcm d₁ d₂ ≠ 0 := Nat.lcm_ne_zero hd₁ hd₂
  unfold congSys
  constructor
  · intro h
    refine ⟨fun q hq => h q ?_, fun q hq => h q ?_⟩
    · rw [Nat.mem_primeFactors] at hq ⊢
      exact ⟨hq.1, hq.2.1.trans (Nat.dvd_lcm_left d₁ d₂), hlcm0⟩
    · rw [Nat.mem_primeFactors] at hq ⊢
      exact ⟨hq.1, hq.2.1.trans (Nat.dvd_lcm_right d₁ d₂), hlcm0⟩
  · rintro ⟨h1, h2⟩ q hq
    rw [Nat.mem_primeFactors] at hq
    have hdvd_mul : q ∣ d₁ * d₂ := hq.2.1.trans (Nat.lcm_dvd (dvd_mul_right d₁ d₂) (dvd_mul_left d₂ d₁))
    rcases hq.1.dvd_mul.mp hdvd_mul with hq1 | hq2
    · exact h1 q (Nat.mem_primeFactors.mpr ⟨hq.1, hq1, hd₁⟩)
    · exact h2 q (Nat.mem_primeFactors.mpr ⟨hq.1, hq2, hd₂⟩)

private lemma squarefree_coprime_div {m q : ℕ} (hm : Squarefree m) (hq : q.Prime) (hqm : q ∣ m) :
    q.Coprime (m / q) := by
  rcases hqm with ⟨k, rfl⟩
  rw [Nat.mul_div_cancel_left k hq.pos]
  rw [hq.coprime_iff_not_dvd]
  intro hqk
  rcases hqk with ⟨t, rfl⟩
  have hunit : IsUnit q := hm q ⟨t, by ring⟩
  exact hq.ne_one (Nat.isUnit_iff.mp hunit)

private lemma exists_crt_residue (a : ℕ → ℕ) :
    ∀ m : ℕ, Squarefree m → ∃ r : ℕ, ∀ n : ℕ, congSys a m n ↔ n % m = r % m := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hm
    have hm0 : m ≠ 0 := hm.ne_zero
    by_cases hm1 : m = 1
    · subst hm1
      exact ⟨0, fun n => by simp [congSys_one, Nat.mod_one]⟩
    · have hgt1 : 1 < m := by omega
      set q := m.minFac
      have hqp : q.Prime := Nat.minFac_prime (by omega)
      have hqm : q ∣ m := Nat.minFac_dvd m
      set m' := m / q
      have hm_eq : q * m' = m := Nat.mul_div_cancel' hqm
      have hm'0 : m' ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at hm_eq
        exact hm0 hm_eq.symm
      have hm'_lt : m' < m := Nat.div_lt_self (by omega) hqp.one_lt
      have hm'_sqf : Squarefree m' := hm.squarefree_of_dvd ⟨q, by rw [mul_comm, hm_eq]⟩
      have hcop : q.Coprime m' := squarefree_coprime_div hm hqp hqm
      obtain ⟨r', hr'⟩ := ih m' hm'_lt hm'_sqf
      let crt := Nat.chineseRemainder hcop (a q) r'
      refine ⟨crt.val, fun n => ?_⟩
      rw [← hm_eq, congSys_mul_iff a hqp.ne_zero hm'0 n, congSys_prime_iff a hqp n, hr' n]
      have hmod := Nat.modEq_and_modEq_iff_modEq_mul hcop (a := n) (b := crt.val)
      have h1 : n % q = a q % q ↔ n ≡ crt.val [MOD q] := by
        change n % q = a q % q ↔ n % q = crt.val % q
        have hcrt1 : crt.val % q = a q % q := crt.property.1
        rw [hcrt1]
      have h2 : n % m' = r' % m' ↔ n ≡ crt.val [MOD m'] := by
        change n % m' = r' % m' ↔ n % m' = crt.val % m'
        have hcrt2 : crt.val % m' = r' % m' := crt.property.2
        rw [hcrt2]
      rw [h1, h2, hmod]
      rfl

private lemma card_Icc_mod_bounds (N m r : ℕ) (hm : 0 < m) :
    N / m ≤ ((Finset.Icc 1 N).filter (fun n => n % m = r % m)).card ∧
    ((Finset.Icc 1 N).filter (fun n => n % m = r % m)).card ≤ N / m + 1 := by
  let r₀ := r % m
  have hr₀_lt : r₀ < m := Nat.mod_lt r hm
  let a₀ := if r₀ = 0 then m else r₀
  have ha₀_pos : 1 ≤ a₀ := by
    dsimp only [a₀]
    split_ifs with h <;> omega
  have ha₀_le : a₀ ≤ m := by
    dsimp only [a₀]
    split_ifs with h <;> omega
  have ha₀_mod : a₀ % m = r % m := by
    dsimp only [a₀, r₀]
    split_ifs with h
    · rw [Nat.mod_self, h]
    · exact Nat.mod_eq_of_lt hr₀_lt
  let K := if N < a₀ then 0 else (N - a₀) / m + 1
  have hcard : ((Finset.Icc 1 N).filter (fun n => n % m = r % m)).card = K := by
    rw [← Finset.card_range K]
    apply Finset.card_bij (fun n _ => (n - a₀) / m)
    · intro n hn
      obtain ⟨hI, hmod⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hI
      have hna₀ : a₀ ≤ n := by
        have h1 : n % m = a₀ % m := hmod.trans ha₀_mod.symm
        dsimp only [a₀, r₀] at h1 ⊢
        split_ifs at h1 ⊢ with h
        · have hdvd : m ∣ n := Nat.dvd_of_mod_eq_zero (by simpa [Nat.mod_self] using h1)
          exact Nat.le_of_dvd (by omega) hdvd
        · have hle : n % m ≤ n := Nat.mod_le n m
          rw [hmod] at hle
          exact hle
      have hnotlt : ¬ N < a₀ := by omega
      rw [Finset.mem_range]
      dsimp only [K]
      rw [if_neg hnotlt]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega))
    · intro n₁ hn₁ n₂ hn₂ heq
      obtain ⟨hI₁, hmod₁⟩ := Finset.mem_filter.mp hn₁
      obtain ⟨hI₂, hmod₂⟩ := Finset.mem_filter.mp hn₂
      obtain ⟨h1_1, _⟩ := Finset.mem_Icc.mp hI₁
      obtain ⟨h2_1, _⟩ := Finset.mem_Icc.mp hI₂
      have hge1 : a₀ ≤ n₁ := by
        dsimp only [a₀, r₀]
        split_ifs with h
        · exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero (by omega))
        · have := Nat.mod_le n₁ m; omega
      have hge2 : a₀ ≤ n₂ := by
        dsimp only [a₀, r₀]
        split_ifs with h
        · exact Nat.le_of_dvd (by omega) (Nat.dvd_of_mod_eq_zero (by omega))
        · have := Nat.mod_le n₂ m; omega
      have hdvd1 : m ∣ n₁ - a₀ := by
        have h1 : (n₁ - a₀) % m = 0 := by
          have := Nat.mod_eq_of_lt (show 0 < m by omega)
          have hsub : n₁ = (n₁ - a₀) + a₀ := (Nat.sub_add_cancel hge1).symm
          have hm1 : (n₁ - a₀) % m + a₀ % m = m * (((n₁ - a₀) % m + a₀ % m) / m) +
              ((n₁ - a₀) % m + a₀ % m) % m := (Nat.div_add_mod _ _).symm
          have hmod_add : ((n₁ - a₀) + a₀) % m = ((n₁ - a₀) % m + a₀ % m) % m := Nat.add_mod _ _ _
          rw [← hsub, hmod₁, ← ha₀_mod] at hmod_add
          have ha_lt : a₀ % m < m := Nat.mod_lt _ hm
          have hb_lt : (n₁ - a₀) % m < m := Nat.mod_lt _ hm
          by_cases hsum : (n₁ - a₀) % m + a₀ % m < m
          · rw [Nat.mod_eq_of_lt hsum] at hmod_add; omega
          · have hlt2 : (n₁ - a₀) % m + a₀ % m - m < m := by omega
            have hmod2' : ((n₁ - a₀) % m + a₀ % m) % m = (n₁ - a₀) % m + a₀ % m - m := by
              rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2]
            rw [hmod2'] at hmod_add; omega
        exact Nat.dvd_of_mod_eq_zero h1
      have hdvd2 : m ∣ n₂ - a₀ := by
        have h1 : (n₂ - a₀) % m = 0 := by
          have hsub : n₂ = (n₂ - a₀) + a₀ := (Nat.sub_add_cancel hge2).symm
          have hmod_add : ((n₂ - a₀) + a₀) % m = ((n₂ - a₀) % m + a₀ % m) % m := Nat.add_mod _ _ _
          rw [← hsub, hmod₂, ← ha₀_mod] at hmod_add
          have ha_lt : a₀ % m < m := Nat.mod_lt _ hm
          have hb_lt : (n₂ - a₀) % m < m := Nat.mod_lt _ hm
          by_cases hsum : (n₂ - a₀) % m + a₀ % m < m
          · rw [Nat.mod_eq_of_lt hsum] at hmod_add; omega
          · have hlt2 : (n₂ - a₀) % m + a₀ % m - m < m := by omega
            have hmod2' : ((n₂ - a₀) % m + a₀ % m) % m = (n₂ - a₀) % m + a₀ % m - m := by
              rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt hlt2]
            rw [hmod2'] at hmod_add; omega
        exact Nat.dvd_of_mod_eq_zero h1
      have heq1 : n₁ - a₀ = m * ((n₁ - a₀) / m) := (Nat.mul_div_cancel' hdvd1).symm
      have heq2 : n₂ - a₀ = m * ((n₂ - a₀) / m) := (Nat.mul_div_cancel' hdvd2).symm
      rw [heq] at heq1
      omega
    · intro j hj
      rw [Finset.mem_range] at hj
      have hnotlt : ¬ N < a₀ := by
        intro hlt
        dsimp only [K] at hj
        rw [if_pos hlt] at hj
        omega
      dsimp only [K] at hj
      rw [if_neg hnotlt] at hj
      refine ⟨a₀ + m * j, ?_, ?_⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, ?_⟩, ?_⟩
        · have hjle : j ≤ (N - a₀) / m := Nat.lt_succ_iff.mp hj
          have hmul : m * j ≤ N - a₀ :=
            (Nat.mul_le_mul_left m hjle).trans (Nat.mul_div_le (N - a₀) m)
          omega
        · rw [Nat.add_mul_mod_self_left, ha₀_mod]
      · rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left j hm]
  rw [hcard]
  dsimp only [K]
  split_ifs with hlt
  · have hdiv0 : N / m = 0 := Nat.div_eq_of_lt (by omega)
    omega
  · constructor
    · have hle : N ≤ (N - a₀) + m := by omega
      calc
        N / m ≤ ((N - a₀) + m) / m := Nat.div_le_div_right hle
        _ = (N - a₀) / m + 1 := Nat.add_div_right (N - a₀) hm
    · exact Nat.add_le_add_right (Nat.div_le_div_right (Nat.sub_le N a₀)) 1

private lemma card_Icc_mod_abs_sub_le (N m r : ℕ) (hm : 0 < m) :
    |(((Finset.Icc 1 N).filter (fun n => n % m = r % m)).card : ℝ) - (N : ℝ) / (m : ℝ)| ≤ 1 := by
  obtain ⟨hlo, hhi⟩ := card_Icc_mod_bounds N m r hm
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hdiv_lo : ((N / m : ℕ) : ℝ) ≤ (N : ℝ) / (m : ℝ) := by
    rw [le_div_iff₀ hmR]
    exact_mod_cast (show (N / m) * m ≤ N by rw [mul_comm]; exact Nat.mul_div_le N m)
  have hdiv_hi : (N : ℝ) / (m : ℝ) < ((N / m : ℕ) : ℝ) + 1 := by
    rw [div_lt_iff₀ hmR]
    have hnat : N < (N / m + 1) * m := by
      have h1 := Nat.div_add_mod N m
      have h2 := Nat.mod_lt N hm
      nlinarith
    have hcast : (N : ℝ) < (((N / m + 1) * m : ℕ) : ℝ) := by exact_mod_cast hnat
    push_cast at hcast
    exact hcast
  have hloR : ((N / m : ℕ) : ℝ) ≤ (((Finset.Icc 1 N).filter (fun n => n % m = r % m)).card : ℝ) := by
    exact_mod_cast hlo
  have hhiR : (((Finset.Icc 1 N).filter (fun n => n % m = r % m)).card : ℝ) ≤ ((N / m : ℕ) : ℝ) + 1 := by
    exact_mod_cast hhi
  rw [abs_le]
  constructor <;> linarith

/- ## Section 3: Selberg's `Λ²` upper bound sieve -/

private def sqfD (D : ℕ) : Finset ℕ :=
  (Finset.Icc 1 D).filter Squarefree

private lemma mem_sqfD {D d : ℕ} : d ∈ sqfD D ↔ 1 ≤ d ∧ d ≤ D ∧ Squarefree d := by
  simp [sqfD, Finset.mem_filter, Finset.mem_Icc, and_assoc]

private lemma one_mem_sqfD {D : ℕ} (hD : 1 ≤ D) : 1 ∈ sqfD D :=
  mem_sqfD.mpr ⟨le_rfl, hD, squarefree_one⟩

private lemma dvd_mem_sqfD {D m d : ℕ} (hm : m ∈ sqfD D) (hdm : d ∣ m) : d ∈ sqfD D := by
  obtain ⟨hm1, hmD, hmsqf⟩ := mem_sqfD.mp hm
  have hd0 : d ≠ 0 := fun h0 => by
    rw [h0, zero_dvd_iff] at hdm
    omega
  have hdle : d ≤ m := Nat.le_of_dvd (by omega) hdm
  exact mem_sqfD.mpr ⟨by omega, hdle.trans hmD, hmsqf.squarefree_of_dvd hdm⟩

private noncomputable def selG (D : ℕ) : ℝ :=
  ∑ r ∈ sqfD D, (1 : ℝ) / (r.totient : ℝ)

private lemma one_le_selG {D : ℕ} (hD : 1 ≤ D) : 1 ≤ selG D := by
  calc
    (1 : ℝ) = (1 : ℝ) / ((1 : ℕ).totient : ℝ) := by simp
    _ ≤ ∑ r ∈ sqfD D, (1 : ℝ) / (r.totient : ℝ) :=
      Finset.single_le_sum (f := fun r : ℕ => (1 : ℝ) / (r.totient : ℝ))
        (fun r _ => by positivity) (one_mem_sqfD hD)

private lemma selG_pos {D : ℕ} (hD : 1 ≤ D) : 0 < selG D :=
  lt_of_lt_of_le zero_lt_one (one_le_selG hD)

private lemma moebius_sq_of_squarefree {m : ℕ} (hm : Squarefree m) :
    ((ArithmeticFunction.moebius m : ℤ) : ℝ) * ((ArithmeticFunction.moebius m : ℤ) : ℝ) = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hm]
  push_cast
  rw [← sq, ← pow_mul, mul_comm, pow_mul]
  norm_num

private lemma abs_moebius_of_squarefree {m : ℕ} (hm : Squarefree m) :
    |((ArithmeticFunction.moebius m : ℤ) : ℝ)| = 1 := by
  rw [ArithmeticFunction.moebius_apply_of_squarefree hm]
  push_cast
  rw [abs_pow, abs_neg, abs_one, one_pow]

private noncomputable def selY (D r : ℕ) : ℝ :=
  if r ∈ sqfD D then
    ((ArithmeticFunction.moebius r : ℤ) : ℝ) / (selG D * (r.totient : ℝ))
  else 0

private noncomputable def selLam (D d : ℕ) : ℝ :=
  (d : ℝ) * ∑ m ∈ (sqfD D).filter (fun m => d ∣ m),
    ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * selY D m

private lemma sum_moebius_divisors (k : ℕ) (hk : 1 ≤ k) :
    ∑ t ∈ k.divisors, ((ArithmeticFunction.moebius t : ℤ) : ℝ) = if k = 1 then 1 else 0 := by
  have h1 : (ArithmeticFunction.moebius * (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) k =
      (1 : ArithmeticFunction ℤ) k := by
    rw [ArithmeticFunction.moebius_mul_coe_zeta]
  rw [ArithmeticFunction.mul_apply] at h1
  have hlhs : ∑ x ∈ k.divisorsAntidiagonal,
      ArithmeticFunction.moebius x.1 * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) x.2 =
      ∑ t ∈ k.divisors, ArithmeticFunction.moebius t := by
    rw [Nat.sum_divisorsAntidiagonal (f := fun a b =>
      ArithmeticFunction.moebius a * (ArithmeticFunction.zeta : ArithmeticFunction ℤ) b)]
    apply Finset.sum_congr rfl
    intro t ht
    have hkt0 : k / t ≠ 0 := by
      have ht_le : t ≤ k := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors ht)
      have ht_pos : 0 < t := Nat.pos_of_mem_divisors ht
      exact Nat.div_ne_zero_iff.mpr ⟨ht_pos.ne', ht_le⟩
    simp [ArithmeticFunction.zeta_apply, hkt0]
  rw [hlhs, ArithmeticFunction.one_apply] at h1
  have hcast : ((∑ t ∈ k.divisors, ArithmeticFunction.moebius t : ℤ) : ℝ) =
      ((if k = 1 then (1 : ℤ) else 0 : ℤ) : ℝ) := by exact_mod_cast h1
  rw [Int.cast_sum] at hcast
  split_ifs at hcast ⊢ <;> simpa using hcast

private lemma sum_selLam_div_eq_selY {D r : ℕ} (hr : r ∈ sqfD D) :
    ∑ d ∈ (sqfD D).filter (fun d => r ∣ d), selLam D d / (d : ℝ) = selY D r := by
  have hr1 : 1 ≤ r := (mem_sqfD.mp hr).1
  have hterm : ∀ d ∈ (sqfD D).filter (fun d => r ∣ d),
      selLam D d / (d : ℝ) =
        ∑ m ∈ (sqfD D).filter (fun m => d ∣ m),
          ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * selY D m := by
    intro d hd
    have hd1 : 1 ≤ d := (mem_sqfD.mp (Finset.mem_filter.mp hd).1).1
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
    unfold selLam
    rw [mul_div_cancel_left₀ _ hdR]
  rw [Finset.sum_congr rfl hterm]
  have hswap :
      (∑ d ∈ (sqfD D).filter (fun d => r ∣ d),
        ∑ m ∈ (sqfD D).filter (fun m => d ∣ m),
          ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * selY D m) =
      ∑ m ∈ (sqfD D).filter (fun m => r ∣ m),
        (∑ d ∈ m.divisors.filter (fun d => r ∣ d),
          ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ)) * selY D m := by
    calc
      (∑ d ∈ (sqfD D).filter (fun d => r ∣ d),
        ∑ m ∈ (sqfD D).filter (fun m => d ∣ m),
          ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * selY D m)
        = ∑ d ∈ (sqfD D).filter (fun d => r ∣ d),
            ∑ m ∈ (sqfD D).filter (fun m => r ∣ m),
              if d ∣ m then ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * selY D m else 0 := by
          apply Finset.sum_congr rfl
          intro d hd
          have hrd : r ∣ d := (Finset.mem_filter.mp hd).2
          rw [← Finset.sum_filter]
          congr 1
          ext m
          simp only [Finset.mem_filter]
          exact ⟨fun ⟨hm, hdm⟩ => ⟨⟨hm, hrd.trans hdm⟩, hdm⟩, fun ⟨⟨hm, _⟩, hdm⟩ => ⟨hm, hdm⟩⟩
      _ = ∑ m ∈ (sqfD D).filter (fun m => r ∣ m),
            ∑ d ∈ (sqfD D).filter (fun d => r ∣ d),
              if d ∣ m then ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) * selY D m else 0 :=
          Finset.sum_comm
      _ = ∑ m ∈ (sqfD D).filter (fun m => r ∣ m),
            (∑ d ∈ m.divisors.filter (fun d => r ∣ d),
              ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ)) * selY D m := by
          apply Finset.sum_congr rfl
          intro m hm
          obtain ⟨hmsqf, hrm⟩ := Finset.mem_filter.mp hm
          have hm1 : 1 ≤ m := (mem_sqfD.mp hmsqf).1
          rw [← Finset.sum_filter, Finset.sum_mul]
          congr 1
          ext d
          simp only [Finset.mem_filter, Nat.mem_divisors]
          constructor
          · rintro ⟨⟨_, hrd⟩, hdm⟩
            exact ⟨⟨hdm, by omega⟩, hrd⟩
          · rintro ⟨⟨hdm, _⟩, hrd⟩
            exact ⟨⟨dvd_mem_sqfD hmsqf hdm, hrd⟩, hdm⟩
  rw [hswap]
  have hinner : ∀ m ∈ (sqfD D).filter (fun m => r ∣ m),
      (∑ d ∈ m.divisors.filter (fun d => r ∣ d),
        ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ)) * selY D m =
      if m = r then selY D r else 0 := by
    intro m hm
    obtain ⟨hmsqf, hrm⟩ := Finset.mem_filter.mp hm
    have hm1 : 1 ≤ m := (mem_sqfD.mp hmsqf).1
    have hbij :
        (∑ d ∈ m.divisors.filter (fun d => r ∣ d),
          ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ)) =
        ∑ t ∈ (m / r).divisors, ((ArithmeticFunction.moebius t : ℤ) : ℝ) := by
      apply Finset.sum_bij (fun d _ => m / d)
      · intro d hd
        obtain ⟨hdm, hrd⟩ := Finset.mem_filter.mp hd
        have hd_dvd : d ∣ m := Nat.dvd_of_mem_divisors hdm
        have hd_pos : 0 < d := Nat.pos_of_mem_divisors hdm
        rw [Nat.mem_divisors]
        refine ⟨?_, ?_⟩
        · rcases hrd with ⟨c, rfl⟩
          have hcm : c ∣ m / r := by
            rcases hd_dvd with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            have : r * (m / r) = r * (c * t) := by
              rw [Nat.mul_div_cancel' hrm, ht, mul_assoc]
            exact Nat.eq_of_mul_eq_mul_left (by omega) this
          have hmd : m / (r * c) = (m / r) / c := Nat.div_div_eq_div_mul m r c |>.symm
          rw [hmd]
          exact Nat.div_dvd_of_dvd hcm
        · have hle : r ≤ m := Nat.le_of_dvd (by omega) hrm
          exact (Nat.div_pos hle (by omega)).ne'
      · intro d₁ hd₁ d₂ hd₂ heq
        have hd1 := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd₁).1
        have hd2 := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd₂).1
        have hmd1_pos : 0 < m / d₁ :=
          Nat.div_pos (Nat.le_of_dvd (by omega) hd1) (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hd₁).1)
        have h1 : d₁ * (m / d₁) = m := Nat.mul_div_cancel' hd1
        have h2 : d₂ * (m / d₂) = m := Nat.mul_div_cancel' hd2
        rw [heq] at h1
        have hmd2_pos : 0 < m / d₂ := heq ▸ hmd1_pos
        exact Nat.eq_of_mul_eq_mul_right hmd2_pos (h1.trans h2.symm)
      · intro t ht
        have ht_dvd : t ∣ m / r := Nat.dvd_of_mem_divisors ht
        have ht_pos : 0 < t := Nat.pos_of_mem_divisors ht
        refine ⟨m / t, ?_, ?_⟩
        · have htm : t ∣ m := ht_dvd.trans (Nat.div_dvd_of_dvd hrm)
          refine Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd htm, by omega⟩, ?_⟩
          rcases ht_dvd with ⟨c, hc⟩
          refine ⟨c, ?_⟩
          have h1 : m = r * (t * c) := by
            calc m = r * (m / r) := (Nat.mul_div_cancel' hrm).symm
              _ = r * (t * c) := by rw [hc]
          have h2 : m / t = r * c := by
            rw [h1, show r * (t * c) = t * (r * c) by ring, Nat.mul_div_cancel_left _ ht_pos]
          exact h2
        · have htm : t ∣ m := ht_dvd.trans (Nat.div_dvd_of_dvd hrm)
          have hmt_pos : 0 < m / t := Nat.div_pos (Nat.le_of_dvd (by omega) htm) ht_pos
          exact Nat.div_eq_of_eq_mul_left hmt_pos (Nat.mul_div_cancel' htm).symm
      · intro _ _; rfl
    rw [hbij, sum_moebius_divisors (m / r) (Nat.div_pos (Nat.le_of_dvd (by omega) hrm) (by omega))]
    have hiff : m / r = 1 ↔ m = r := by
      constructor
      · intro h
        have := Nat.mul_div_cancel' hrm
        rw [h, mul_one] at this
        exact this.symm
      · rintro rfl
        exact Nat.div_self (by omega)
    simp only [hiff]
    split_ifs with h
    · rw [h, one_mul]
    · rw [zero_mul]
  rw [Finset.sum_congr rfl hinner, Finset.sum_ite_eq']
  simp [hr]

private lemma selLam_one {D : ℕ} (hD : 1 ≤ D) : selLam D 1 = 1 := by
  unfold selLam selY
  have hG : selG D ≠ 0 := (selG_pos hD).ne'
  have hfilt : (sqfD D).filter (fun m => 1 ∣ m) = sqfD D := by
    ext m; simp
  rw [hfilt]
  simp only [Nat.cast_one, one_mul, Nat.div_one]
  calc
    (∑ m ∈ sqfD D, ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
        if m ∈ sqfD D then ((ArithmeticFunction.moebius m : ℤ) : ℝ) / (selG D * (m.totient : ℝ)) else 0)
      = ∑ m ∈ sqfD D, (1 / selG D) * ((1 : ℝ) / (m.totient : ℝ)) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [if_pos hm]
        have hsq := moebius_sq_of_squarefree (mem_sqfD.mp hm).2.2
        have h1 : ((ArithmeticFunction.moebius m : ℤ) : ℝ) *
            (((ArithmeticFunction.moebius m : ℤ) : ℝ) / (selG D * (m.totient : ℝ))) =
            (((ArithmeticFunction.moebius m : ℤ) : ℝ) * ((ArithmeticFunction.moebius m : ℤ) : ℝ)) /
            (selG D * (m.totient : ℝ)) := by ring
        rw [h1, hsq]
        ring
    _ = (1 / selG D) * selG D := by rw [← Finset.mul_sum]; rfl
    _ = 1 := by field_simp [hG]

private lemma selberg_quad_form {D : ℕ} (hD : 1 ≤ D) :
    (∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D,
      selLam D d₁ * selLam D d₂ / ((Nat.lcm d₁ d₂ : ℕ) : ℝ)) = 1 / selG D := by
  have hG : selG D ≠ 0 := (selG_pos hD).ne'
  have hstep1 :
      (∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D,
        selLam D d₁ * selLam D d₂ / ((Nat.lcm d₁ d₂ : ℕ) : ℝ)) =
      ∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D,
        ∑ r ∈ sqfD D,
          if r ∣ d₁ ∧ r ∣ d₂ then
            (r.totient : ℝ) * (selLam D d₁ / (d₁ : ℝ)) * (selLam D d₂ / (d₂ : ℝ))
          else 0 := by
    apply Finset.sum_congr rfl
    intro d₁ hd₁
    apply Finset.sum_congr rfl
    intro d₂ hd₂
    have hd1_pos : 0 < d₁ := (mem_sqfD.mp hd₁).1
    have hd2_pos : 0 < d₂ := (mem_sqfD.mp hd₂).1
    have hlcm_pos : 0 < Nat.lcm d₁ d₂ := Nat.pos_of_ne_zero (Nat.lcm_ne_zero hd1_pos.ne' hd2_pos.ne')
    have hgcd_lcm : ((Nat.gcd d₁ d₂ : ℕ) : ℝ) * ((Nat.lcm d₁ d₂ : ℕ) : ℝ) = (d₁ : ℝ) * (d₂ : ℝ) := by
      exact_mod_cast Nat.gcd_mul_lcm d₁ d₂
    have hd1R : (d₁ : ℝ) ≠ 0 := by exact_mod_cast hd1_pos.ne'
    have hd2R : (d₂ : ℝ) ≠ 0 := by exact_mod_cast hd2_pos.ne'
    have hlcmR : ((Nat.lcm d₁ d₂ : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hlcm_pos.ne'
    have hfrac : selLam D d₁ * selLam D d₂ / ((Nat.lcm d₁ d₂ : ℕ) : ℝ) =
        ((Nat.gcd d₁ d₂ : ℕ) : ℝ) * (selLam D d₁ / (d₁ : ℝ)) * (selLam D d₂ / (d₂ : ℝ)) := by
      have hdiv : (1 : ℝ) / ((Nat.lcm d₁ d₂ : ℕ) : ℝ) =
          ((Nat.gcd d₁ d₂ : ℕ) : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ)) := by
        rw [div_eq_div_iff hlcmR (mul_ne_zero hd1R hd2R), one_mul, hgcd_lcm]
      calc
        selLam D d₁ * selLam D d₂ / ((Nat.lcm d₁ d₂ : ℕ) : ℝ)
          = selLam D d₁ * selLam D d₂ * (1 / ((Nat.lcm d₁ d₂ : ℕ) : ℝ)) := by ring
        _ = selLam D d₁ * selLam D d₂ * (((Nat.gcd d₁ d₂ : ℕ) : ℝ) / ((d₁ : ℝ) * (d₂ : ℝ))) := by
            rw [hdiv]
        _ = ((Nat.gcd d₁ d₂ : ℕ) : ℝ) * (selLam D d₁ / (d₁ : ℝ)) * (selLam D d₂ / (d₂ : ℝ)) := by
            ring
    rw [hfrac]
    have htot : ((Nat.gcd d₁ d₂ : ℕ) : ℝ) = ∑ r ∈ (Nat.gcd d₁ d₂).divisors, (r.totient : ℝ) := by
      have := Nat.sum_totient (Nat.gcd d₁ d₂)
      exact_mod_cast this.symm
    rw [htot, Finset.sum_mul, Finset.sum_mul, ← Finset.sum_filter]
    congr 1
    ext r
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hrd, hgcd0⟩
      have hrd1 : r ∣ d₁ := hrd.trans (Nat.gcd_dvd_left d₁ d₂)
      have hrd2 : r ∣ d₂ := hrd.trans (Nat.gcd_dvd_right d₁ d₂)
      exact ⟨dvd_mem_sqfD hd₁ hrd1, hrd1, hrd2⟩
    · rintro ⟨_, hrd1, hrd2⟩
      exact ⟨Nat.dvd_gcd hrd1 hrd2, (Nat.gcd_pos_of_pos_left d₂ hd1_pos).ne'⟩
  rw [hstep1]
  calc
    (∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D, ∑ r ∈ sqfD D,
        if r ∣ d₁ ∧ r ∣ d₂ then
          (r.totient : ℝ) * (selLam D d₁ / (d₁ : ℝ)) * (selLam D d₂ / (d₂ : ℝ))
        else 0)
      = ∑ d₁ ∈ sqfD D, ∑ r ∈ sqfD D, ∑ d₂ ∈ sqfD D,
          if r ∣ d₁ ∧ r ∣ d₂ then
            (r.totient : ℝ) * (selLam D d₁ / (d₁ : ℝ)) * (selLam D d₂ / (d₂ : ℝ))
          else 0 := by
        apply Finset.sum_congr rfl
        intro d₁ _
        exact Finset.sum_comm
    _ = ∑ r ∈ sqfD D, ∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D,
          if r ∣ d₁ ∧ r ∣ d₂ then
            (r.totient : ℝ) * (selLam D d₁ / (d₁ : ℝ)) * (selLam D d₂ / (d₂ : ℝ))
          else 0 := Finset.sum_comm
    _ = ∑ r ∈ sqfD D, (r.totient : ℝ) * (selY D r) ^ 2 := by
        apply Finset.sum_congr rfl
        intro r hr
        have hsplit :
            (∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D,
              if r ∣ d₁ ∧ r ∣ d₂ then
                (r.totient : ℝ) * (selLam D d₁ / (d₁ : ℝ)) * (selLam D d₂ / (d₂ : ℝ))
              else 0) =
            (r.totient : ℝ) *
              (∑ d₁ ∈ (sqfD D).filter (fun d => r ∣ d), selLam D d₁ / (d₁ : ℝ)) *
              (∑ d₂ ∈ (sqfD D).filter (fun d => r ∣ d), selLam D d₂ / (d₂ : ℝ)) := by
          have hinner_eq : ∀ d₁ ∈ sqfD D,
              (∑ d₂ ∈ sqfD D, if r ∣ d₁ ∧ r ∣ d₂ then
                (r.totient : ℝ) * (selLam D d₁ / (d₁ : ℝ)) * (selLam D d₂ / (d₂ : ℝ)) else 0) =
              if r ∣ d₁ then
                (r.totient : ℝ) * (selLam D d₁ / (d₁ : ℝ)) *
                  ∑ d₂ ∈ (sqfD D).filter (fun d => r ∣ d), selLam D d₂ / (d₂ : ℝ)
              else 0 := by
            intro d₁ _
            by_cases h1 : r ∣ d₁
            · simp only [h1, true_and, if_true]
              rw [← Finset.sum_filter, Finset.mul_sum]
            · simp [h1]
          rw [Finset.sum_congr rfl hinner_eq, ← Finset.sum_filter, ← Finset.sum_mul, ← Finset.mul_sum]
        rw [hsplit, sum_selLam_div_eq_selY hr]
        ring
    _ = (1 / (selG D) ^ 2) * selG D := by
        unfold selG
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        have htot_pos : (0 : ℝ) < (r.totient : ℝ) := by
          exact_mod_cast Nat.totient_pos.mpr (mem_sqfD.mp hr).1
        have htot_ne : (r.totient : ℝ) ≠ 0 := htot_pos.ne'
        have hsq := moebius_sq_of_squarefree (mem_sqfD.mp hr).2.2
        unfold selY
        rw [if_pos hr]
        have hcalc : (r.totient : ℝ) *
            (((ArithmeticFunction.moebius r : ℤ) : ℝ) / (selG D * (r.totient : ℝ))) ^ 2 =
            (((ArithmeticFunction.moebius r : ℤ) : ℝ) * ((ArithmeticFunction.moebius r : ℤ) : ℝ)) *
              (r.totient : ℝ) / ((selG D) ^ 2 * (r.totient : ℝ) ^ 2) := by ring
        rw [hcalc, hsq]
        change 1 * (r.totient : ℝ) / ((selG D) ^ 2 * (r.totient : ℝ) ^ 2) =
          1 / (selG D) ^ 2 * (1 / (r.totient : ℝ))
        field_simp [hG, htot_ne]
    _ = 1 / selG D := by field_simp [hG]

private lemma div_totient_eq_sum_inv_totient :
    ∀ d : ℕ, Squarefree d →
      (d : ℝ) / (d.totient : ℝ) = ∑ t ∈ d.divisors, (1 : ℝ) / (t.totient : ℝ) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    have hd0 : d ≠ 0 := hd.ne_zero
    by_cases hd1 : d = 1
    · subst hd1; simp
    · set q := d.minFac
      have hqp : q.Prime := Nat.minFac_prime (by omega)
      have hqd : q ∣ d := Nat.minFac_dvd d
      set d' := d / q
      have hd_eq : q * d' = d := Nat.mul_div_cancel' hqd
      have hd'_lt : d' < d := Nat.div_lt_self (by omega) hqp.one_lt
      have hd'_sqf : Squarefree d' := hd.squarefree_of_dvd ⟨q, by rw [mul_comm, hd_eq]⟩
      have hcop : q.Coprime d' := squarefree_coprime_div hd hqp hqd
      have hih := ih d' hd'_lt hd'_sqf
      have hdiv_eq : d.divisors = d'.divisors ∪ d'.divisors.image (fun t => q * t) := by
        ext x
        simp only [Nat.mem_divisors, Finset.mem_union, Finset.mem_image]
        constructor
        · rintro ⟨hxd, _⟩
          by_cases hqx : q ∣ x
          · right
            rcases hqx with ⟨t, rfl⟩
            refine ⟨t, ⟨?_, hd'_sqf.ne_zero⟩, rfl⟩
            rw [← hd_eq] at hxd
            exact (mul_dvd_mul_iff_left hqp.ne_zero).mp hxd
          · left
            have hcopx : x.Coprime q := ((hqp.coprime_iff_not_dvd).mpr hqx).symm
            rw [← hd_eq] at hxd
            exact ⟨hcopx.dvd_of_dvd_mul_left hxd, hd'_sqf.ne_zero⟩
        · rintro (⟨hxd', _⟩ | ⟨t, ⟨htd', _⟩, rfl⟩)
          · exact ⟨hxd'.trans ⟨q, by rw [mul_comm, hd_eq]⟩, hd0⟩
          · exact ⟨by rw [← hd_eq]; exact mul_dvd_mul_left q htd', hd0⟩
      have hdisj : Disjoint d'.divisors (d'.divisors.image (fun t => q * t)) := by
        rw [Finset.disjoint_left]
        intro x hx1 hx2
        obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hx2
        have hqt_d' : q * t ∣ d' := Nat.dvd_of_mem_divisors hx1
        have hqd' : q ∣ d' := (dvd_mul_right q t).trans hqt_d'
        exact (hqp.coprime_iff_not_dvd.mp hcop) hqd'
      have hsum_img :
          ∑ x ∈ d'.divisors.image (fun t => q * t), (1 : ℝ) / (x.totient : ℝ) =
          (1 / ((q.totient : ℕ) : ℝ)) * ∑ t ∈ d'.divisors, (1 : ℝ) / (t.totient : ℝ) := by
        rw [Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hqp.pos h), Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro t ht
        have htd' : t ∣ d' := Nat.dvd_of_mem_divisors ht
        have hcopt : q.Coprime t := hcop.coprime_dvd_right htd'
        rw [Nat.totient_mul hcopt]
        push_cast
        ring
      rw [hdiv_eq, Finset.sum_union hdisj, hsum_img, ← hih]
      have htot_d : d.totient = q.totient * d'.totient := by
        rw [← hd_eq, Nat.totient_mul hcop]
      have htot_q : q.totient = q - 1 := Nat.totient_prime hqp
      have hq1 : 1 ≤ q := hqp.one_lt.le
      have hqR : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by rw [Nat.cast_sub hq1, Nat.cast_one]
      have hqtot_ne : (q.totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr hqp.pos).ne'
      have hd'tot_ne : (d'.totient : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd'_sqf.ne_zero)).ne'
      rw [htot_d, ← hd_eq]
      push_cast
      have hqfrac : (q : ℝ) / (q.totient : ℝ) = 1 + 1 / (q.totient : ℝ) := by
        rw [htot_q, hqR]
        have hqm1 : (q : ℝ) - 1 ≠ 0 := by
          have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hqp.two_le
          linarith
        field_simp [hqm1]
        ring
      calc
        (q : ℝ) * (d' : ℝ) / ((q.totient : ℝ) * (d'.totient : ℝ))
          = ((q : ℝ) / (q.totient : ℝ)) * ((d' : ℝ) / (d'.totient : ℝ)) := by ring
        _ = (1 + 1 / (q.totient : ℝ)) * ((d' : ℝ) / (d'.totient : ℝ)) := by rw [hqfrac]
        _ = (d' : ℝ) / (d'.totient : ℝ) +
              1 / (q.totient : ℝ) * ((d' : ℝ) / (d'.totient : ℝ)) := by ring

private lemma abs_selLam_le_one {D d : ℕ} (hD : 1 ≤ D) (hd : d ∈ sqfD D) :
    |selLam D d| ≤ 1 := by
  have hd1 : 1 ≤ d := (mem_sqfD.mp hd).1
  have hdD : d ≤ D := (mem_sqfD.mp hd).2.1
  have hdsqf : Squarefree d := (mem_sqfD.mp hd).2.2
  have hGpos : 0 < selG D := selG_pos hD
  let Kd := (sqfD D).filter (fun k => k ≤ D / d ∧ d.Coprime k)
  have hlam_eq :
      selLam D d =
        (((ArithmeticFunction.moebius d : ℤ) : ℝ) / selG D) *
          ((d : ℝ) / (d.totient : ℝ)) *
          ∑ k ∈ Kd, (1 : ℝ) / (k.totient : ℝ) := by
    unfold selLam selY
    have hbij :
        (∑ m ∈ (sqfD D).filter (fun m => d ∣ m),
          ((ArithmeticFunction.moebius (m / d) : ℤ) : ℝ) *
            if m ∈ sqfD D then
              ((ArithmeticFunction.moebius m : ℤ) : ℝ) / (selG D * (m.totient : ℝ))
            else 0) =
        ∑ k ∈ Kd,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
            (selG D * (d.totient : ℝ) * (k.totient : ℝ)) := by
      apply Finset.sum_bij (fun m _ => m / d)
      · intro m hm
        obtain ⟨hmsqf, hdm⟩ := Finset.mem_filter.mp hm
        obtain ⟨hm1, hmD, hmsq⟩ := mem_sqfD.mp hmsqf
        have hkm : m / d ∣ m := Nat.div_dvd_of_dvd hdm
        have hk_sqf : m / d ∈ sqfD D := dvd_mem_sqfD hmsqf hkm
        have hk_le : m / d ≤ D / d := Nat.div_le_div_right hmD
        have hcop : d.Coprime (m / d) := by
          have hprod : d * (m / d) = m := Nat.mul_div_cancel' hdm
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          set g := Nat.gcd d (m / d)
          have hg1 : 1 < g := by
            have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
            omega
          have hgd : g ∣ d := Nat.gcd_dvd_left d (m / d)
          have hgk : g ∣ m / d := Nat.gcd_dvd_right d (m / d)
          have hgg : g * g ∣ m := by
            rw [← hprod]
            exact mul_dvd_mul hgd hgk
          exact (Nat.isUnit_iff.mp (hmsq g hgg)) ▸ (show g ≠ 1 by omega) <| rfl
        exact Finset.mem_filter.mpr ⟨hk_sqf, hk_le, hcop⟩
      · intro m₁ hm₁ m₂ hm₂ heq
        have h1 := Nat.mul_div_cancel' (Finset.mem_filter.mp hm₁).2
        have h2 := Nat.mul_div_cancel' (Finset.mem_filter.mp hm₂).2
        rw [← h1, ← h2, heq]
      · intro k hk
        obtain ⟨hksqf, hkle, hcop⟩ := Finset.mem_filter.mp hk
        obtain ⟨hk1, _, hksq⟩ := mem_sqfD.mp hksqf
        refine ⟨d * k, ?_, Nat.mul_div_cancel_left k (by omega)⟩
        have hdk_le : d * k ≤ D := (Nat.mul_le_mul_left d hkle).trans (Nat.mul_div_le D d)
        have hdk_sq : Squarefree (d * k) := (Nat.squarefree_mul hcop).mpr ⟨hdsqf, hksq⟩
        exact Finset.mem_filter.mpr ⟨mem_sqfD.mpr ⟨by nlinarith, hdk_le, hdk_sq⟩, dvd_mul_right d k⟩
      · intro m hm
        obtain ⟨hmsqf, hdm⟩ := Finset.mem_filter.mp hm
        rw [if_pos hmsqf]
        set k := m / d
        have hm_eq : d * k = m := Nat.mul_div_cancel' hdm
        have hksq : Squarefree k := (mem_sqfD.mp hmsqf).2.2.squarefree_of_dvd (Nat.div_dvd_of_dvd hdm)
        have hcop : d.Coprime k := by
          rw [Nat.coprime_iff_gcd_eq_one]
          by_contra hne
          set g := Nat.gcd d k
          have hgpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
          have hgg : g * g ∣ m := by
            rw [← hm_eq]
            exact mul_dvd_mul (Nat.gcd_dvd_left d k) (Nat.gcd_dvd_right d k)
          have hgu : g = 1 := Nat.isUnit_iff.mp ((mem_sqfD.mp hmsqf).2.2 g hgg)
          exact hne hgu
        have hmu : ArithmeticFunction.moebius m =
            ArithmeticFunction.moebius d * ArithmeticFunction.moebius k := by
          rw [← hm_eq]
          exact ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
        have hphi : m.totient = d.totient * k.totient := by
          rw [← hm_eq, Nat.totient_mul hcop]
        have hmusq := moebius_sq_of_squarefree hksq
        rw [hmu, hphi]
        push_cast
        have h1 : ((ArithmeticFunction.moebius k : ℤ) : ℝ) *
            (((ArithmeticFunction.moebius d : ℤ) : ℝ) * ((ArithmeticFunction.moebius k : ℤ) : ℝ) /
              (selG D * ((d.totient : ℝ) * (k.totient : ℝ)))) =
            (((ArithmeticFunction.moebius k : ℤ) : ℝ) * ((ArithmeticFunction.moebius k : ℤ) : ℝ)) *
              ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
              (selG D * (d.totient : ℝ) * (k.totient : ℝ)) := by ring
        rw [h1, hmusq, one_mul]
    rw [hbij, Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hlam_eq, div_totient_eq_sum_inv_totient d hdsqf]
  have hprod_sum :
      (∑ t ∈ d.divisors, (1 : ℝ) / (t.totient : ℝ)) * (∑ k ∈ Kd, (1 : ℝ) / (k.totient : ℝ)) =
      ∑ p ∈ d.divisors ×ˢ Kd, (1 : ℝ) / ((p.1 * p.2).totient : ℝ) := by
    rw [Finset.sum_mul_sum, Finset.sum_product]
    apply Finset.sum_congr rfl
    intro t ht
    apply Finset.sum_congr rfl
    intro k hk
    have hcop_dk : d.Coprime k := (Finset.mem_filter.mp hk).2.2
    have hcop_tk : t.Coprime k := hcop_dk.coprime_dvd_left (Nat.dvd_of_mem_divisors ht)
    rw [Nat.totient_mul hcop_tk]
    push_cast
    ring
  have hsum_le_G : (∑ p ∈ d.divisors ×ˢ Kd, (1 : ℝ) / ((p.1 * p.2).totient : ℝ)) ≤ selG D := by
    have hinj : ∀ p₁ ∈ d.divisors ×ˢ Kd, ∀ p₂ ∈ d.divisors ×ˢ Kd,
        p₁.1 * p₁.2 = p₂.1 * p₂.2 → p₁ = p₂ := by
      intro p₁ hp₁ p₂ hp₂ heq
      obtain ⟨ht₁, hk₁⟩ := Finset.mem_product.mp hp₁
      obtain ⟨ht₂, hk₂⟩ := Finset.mem_product.mp hp₂
      have htd₁ : p₁.1 ∣ d := Nat.dvd_of_mem_divisors ht₁
      have htd₂ : p₂.1 ∣ d := Nat.dvd_of_mem_divisors ht₂
      have hcop₁ : d.Coprime p₁.2 := (Finset.mem_filter.mp hk₁).2.2
      have hcop₂ : d.Coprime p₂.2 := (Finset.mem_filter.mp hk₂).2.2
      have ht_eq : p₁.1 = p₂.1 := by
        have hg1 : Nat.gcd (p₁.1 * p₁.2) d = p₁.1 := by
          rw [hcop₁.symm.gcd_mul_right_cancel p₁.1, Nat.gcd_eq_left htd₁]
        have hg2 : Nat.gcd (p₂.1 * p₂.2) d = p₂.1 := by
          rw [hcop₂.symm.gcd_mul_right_cancel p₂.1, Nat.gcd_eq_left htd₂]
        rw [← hg1, ← hg2, heq]
      have hp1_pos : 0 < p₁.1 := Nat.pos_of_mem_divisors ht₁
      have hk_eq : p₁.2 = p₂.2 := by
        rw [ht_eq] at heq
        exact Nat.eq_of_mul_eq_mul_left (ht_eq ▸ hp1_pos) heq
      exact Prod.ext ht_eq hk_eq
    have hmaps : (d.divisors ×ˢ Kd).image (fun p : ℕ × ℕ => p.1 * p.2) ⊆ sqfD D := by
      intro r hr
      obtain ⟨⟨t, k⟩, htk, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨ht, hk⟩ := Finset.mem_product.mp htk
      have htd : t ∣ d := Nat.dvd_of_mem_divisors ht
      have ht1 : 1 ≤ t := Nat.pos_of_mem_divisors ht
      have htle : t ≤ d := Nat.le_of_dvd (by omega) htd
      obtain ⟨hksqf, hkle, hcop_dk⟩ := Finset.mem_filter.mp hk
      obtain ⟨hk1, _, hksq⟩ := mem_sqfD.mp hksqf
      have htsq : Squarefree t := hdsqf.squarefree_of_dvd htd
      have hcop_tk : t.Coprime k := hcop_dk.coprime_dvd_left htd
      have hleD : t * k ≤ D :=
        (Nat.mul_le_mul htle hkle).trans (Nat.mul_div_le D d)
      exact mem_sqfD.mpr ⟨by nlinarith, hleD, (Nat.squarefree_mul hcop_tk).mpr ⟨htsq, hksq⟩⟩
    calc
      (∑ p ∈ d.divisors ×ˢ Kd, (1 : ℝ) / ((p.1 * p.2).totient : ℝ))
        = ∑ r ∈ (d.divisors ×ˢ Kd).image (fun p : ℕ × ℕ => p.1 * p.2),
            (1 : ℝ) / (r.totient : ℝ) := by
          rw [Finset.sum_image (fun a ha b hb h => hinj a (Finset.mem_coe.mp ha) b (Finset.mem_coe.mp hb) h)]
      _ ≤ ∑ r ∈ sqfD D, (1 : ℝ) / (r.totient : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hmaps (fun _ _ _ => by positivity)
      _ = selG D := rfl
  have hsum_nonneg : 0 ≤ ∑ p ∈ d.divisors ×ˢ Kd, (1 : ℝ) / ((p.1 * p.2).totient : ℝ) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  rw [mul_assoc, hprod_sum, abs_mul, abs_div, abs_moebius_of_squarefree hdsqf,
    abs_of_pos hGpos, abs_of_nonneg hsum_nonneg]
  calc
    (1 / selG D) * (∑ p ∈ d.divisors ×ˢ Kd, (1 : ℝ) / ((p.1 * p.2).totient : ℝ))
      ≤ (1 / selG D) * selG D :=
        mul_le_mul_of_nonneg_left hsum_le_G (by positivity)
    _ = 1 := by field_simp [hGpos.ne']

private lemma selberg_upper_bound {x p D : ℕ} (a : ℕ → ℕ)
    (hD1 : 1 ≤ D) (hp : p.Prime) (hDp : D < p) (hDx : D ≤ x / 2) :
    let small := (x / 2).primesLE
    let S := (Finset.Icc 1 (x ^ 2)).filter fun n => ∀ q ∈ small, n % q ≠ a q % q
    ((S.filter fun n => n % p = a p % p).card : ℝ) ≤
      ((x ^ 2 : ℕ) : ℝ) / ((p : ℝ) * selG D) + (D : ℝ) ^ 2 := by
  intro small S
  set Sp := S.filter fun n => n % p = a p % p
  set Ip := (Finset.Icc 1 (x ^ 2)).filter fun n => n % p = a p % p
  have hSp_sub : Sp ⊆ Ip := by
    intro n hn
    obtain ⟨hnS, hnp⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hnS).1, hnp⟩
  have hSp_weight : ∀ n ∈ Sp,
      (∑ d ∈ sqfD D, if congSys a d n then selLam D d else 0) = 1 := by
    intro n hn
    obtain ⟨hnS, _⟩ := Finset.mem_filter.mp hn
    have hnsmall := (Finset.mem_filter.mp hnS).2
    have hterm : ∀ d ∈ sqfD D,
        (if congSys a d n then selLam D d else 0) = if d = 1 then selLam D 1 else 0 := by
      intro d hd
      by_cases hd1 : d = 1
      · subst hd1
        simp [congSys_one]
      · rw [if_neg hd1]
        have hd_gt1 : 1 < d := by have := (mem_sqfD.mp hd).1; omega
        have hnot : ¬ congSys a d n := by
          intro hcong
          set q := d.minFac
          have hqp : q.Prime := Nat.minFac_prime (by omega)
          have hqd : q ∣ d := Nat.minFac_dvd d
          have hqle : q ≤ d := Nat.le_of_dvd (by omega) hqd
          have hqsmall : q ∈ small := Nat.mem_primesLE.mpr ⟨hqle.trans ((mem_sqfD.mp hd).2.1.trans hDx), hqp⟩
          have hqpf : q ∈ d.primeFactors := Nat.mem_primeFactors.mpr ⟨hqp, hqd, by omega⟩
          exact hnsmall q hqsmall (hcong q hqpf)
        rw [if_neg hnot]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq', if_pos (one_mem_sqfD hD1), selLam_one hD1]
  have hstep1 :
      (Sp.card : ℝ) ≤
      ∑ n ∈ Ip, (∑ d ∈ sqfD D, if congSys a d n then selLam D d else 0) ^ 2 := by
    calc
      (Sp.card : ℝ) = ∑ _n ∈ Sp, (1 : ℝ) := by simp
      _ = ∑ n ∈ Sp, (∑ d ∈ sqfD D, if congSys a d n then selLam D d else 0) ^ 2 := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [hSp_weight n hn, one_pow]
      _ ≤ ∑ n ∈ Ip, (∑ d ∈ sqfD D, if congSys a d n then selLam D d else 0) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hSp_sub (fun _ _ _ => sq_nonneg _)
  have hexpand :
      (∑ n ∈ Ip, (∑ d ∈ sqfD D, if congSys a d n then selLam D d else 0) ^ 2) =
      ∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D,
        selLam D d₁ * selLam D d₂ *
          (((Finset.Icc 1 (x ^ 2)).filter fun n =>
            n % p = a p % p ∧ congSys a d₁ n ∧ congSys a d₂ n).card : ℝ) := by
    have h1 : ∀ n ∈ Ip,
        (∑ d ∈ sqfD D, if congSys a d n then selLam D d else 0) ^ 2 =
        ∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D,
          if congSys a d₁ n ∧ congSys a d₂ n then selLam D d₁ * selLam D d₂ else 0 := by
      intro n _
      rw [sq, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d₁ _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d₂ _
      split_ifs <;> simp_all
    rw [Finset.sum_congr rfl h1]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d₁ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d₂ _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
    congr 1
    norm_cast
    congr 1
    ext n
    simp only [Ip, Finset.mem_filter]
    tauto
  have hterm_bound : ∀ d₁ ∈ sqfD D, ∀ d₂ ∈ sqfD D,
      selLam D d₁ * selLam D d₂ *
        (((Finset.Icc 1 (x ^ 2)).filter fun n =>
          n % p = a p % p ∧ congSys a d₁ n ∧ congSys a d₂ n).card : ℝ) ≤
      selLam D d₁ * selLam D d₂ * (((x ^ 2 : ℕ) : ℝ) / ((p : ℝ) * ((Nat.lcm d₁ d₂ : ℕ) : ℝ))) +
        |selLam D d₁| * |selLam D d₂| := by
    intro d₁ hd₁ d₂ hd₂
    obtain ⟨hd1_1, hd1_D, hd1_sq⟩ := mem_sqfD.mp hd₁
    obtain ⟨hd2_1, hd2_D, hd2_sq⟩ := mem_sqfD.mp hd₂
    set L := Nat.lcm d₁ d₂
    have hL0 : L ≠ 0 := Nat.lcm_ne_zero (by omega) (by omega)
    have hL_sq : Squarefree L := by
      rw [Nat.squarefree_iff_prime_squarefree]
      intro q hq hqq
      have hq1_not : ¬ (q * q ∣ d₁) := fun h => hq.ne_one (Nat.isUnit_iff.mp (hd1_sq q h))
      have hq2_not : ¬ (q * q ∣ d₂) := fun h => hq.ne_one (Nat.isUnit_iff.mp (hd2_sq q h))
      set g := Nat.gcd d₁ d₂
      have hg_pos : 0 < g := Nat.gcd_pos_of_pos_left d₂ (by omega)
      have hg_dvd2 : g ∣ d₂ := Nat.gcd_dvd_right d₁ d₂
      have hL_eq : L = d₁ * (d₂ / g) := by
        have h1 : g * L = d₁ * d₂ := Nat.gcd_mul_lcm d₁ d₂
        have h2 : g * L = g * (d₁ * (d₂ / g)) := by
          rw [h1, show g * (d₁ * (d₂ / g)) = d₁ * (g * (d₂ / g)) by ring, Nat.mul_div_cancel' hg_dvd2]
        exact Nat.eq_of_mul_eq_mul_left hg_pos h2
      by_cases hq2 : q ∣ d₂
      · by_cases hq1 : q ∣ d₁
        · have hqg : q ∣ g := Nat.dvd_gcd hq1 hq2
          have hq_ndvd_q2 : ¬ q ∣ d₂ / g := by
            intro h
            apply hq2_not
            rw [← Nat.mul_div_cancel' hg_dvd2]
            exact mul_dvd_mul hqg h
          have hcop : (q * q).Coprime (d₂ / g) :=
            (hq.coprime_iff_not_dvd.mpr hq_ndvd_q2).mul_left (hq.coprime_iff_not_dvd.mpr hq_ndvd_q2)
          rw [hL_eq] at hqq
          exact hq1_not (hcop.dvd_of_dvd_mul_right hqq)
        · have hcop : (q * q).Coprime d₁ :=
            (hq.coprime_iff_not_dvd.mpr hq1).mul_left (hq.coprime_iff_not_dvd.mpr hq1)
          have hqq_mul : q * q ∣ d₁ * d₂ := hqq.trans (Nat.lcm_dvd (dvd_mul_right d₁ d₂) (dvd_mul_left d₂ d₁))
          exact hq2_not (hcop.dvd_of_dvd_mul_left hqq_mul)
      · have hcop : (q * q).Coprime d₂ :=
          (hq.coprime_iff_not_dvd.mpr hq2).mul_left (hq.coprime_iff_not_dvd.mpr hq2)
        have hqq_mul : q * q ∣ d₁ * d₂ := hqq.trans (Nat.lcm_dvd (dvd_mul_right d₁ d₂) (dvd_mul_left d₂ d₁))
        exact hq1_not (hcop.dvd_of_dvd_mul_right hqq_mul)
    have hpL_cop : p.Coprime L := by
      rw [hp.coprime_iff_not_dvd]
      intro hpL
      have hpmul : p ∣ d₁ * d₂ := hpL.trans (Nat.lcm_dvd (dvd_mul_right d₁ d₂) (dvd_mul_left d₂ d₁))
      rcases hp.dvd_mul.mp hpmul with hp1 | hp2
      · have := Nat.le_of_dvd (by omega) hp1; omega
      · have := Nat.le_of_dvd (by omega) hp2; omega
    have hpL_sq : Squarefree (p * L) := (Nat.squarefree_mul hpL_cop).mpr ⟨hp.squarefree, hL_sq⟩
    obtain ⟨r, hr⟩ := exists_crt_residue a (p * L) hpL_sq
    have hfilt_eq :
        ((Finset.Icc 1 (x ^ 2)).filter fun n =>
          n % p = a p % p ∧ congSys a d₁ n ∧ congSys a d₂ n) =
        ((Finset.Icc 1 (x ^ 2)).filter fun n => n % (p * L) = r % (p * L)) := by
      ext n
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hI, hnp, h1, h2⟩
        refine ⟨hI, (hr n).mp ?_⟩
        rw [congSys_mul_iff a hp.ne_zero hL0, congSys_prime_iff a hp, congSys_lcm_iff a (by omega) (by omega)]
        exact ⟨hnp, h1, h2⟩
      · rintro ⟨hI, hmod⟩
        have hsys := (hr n).mpr hmod
        rw [congSys_mul_iff a hp.ne_zero hL0, congSys_prime_iff a hp, congSys_lcm_iff a (by omega) (by omega)] at hsys
        exact ⟨hI, hsys.1, hsys.2.1, hsys.2.2⟩
    rw [hfilt_eq]
    have habs := card_Icc_mod_abs_sub_le (x ^ 2) (p * L) r (Nat.mul_pos hp.pos (Nat.pos_of_ne_zero hL0))
    rw [Nat.cast_mul] at habs
    set C := (((Finset.Icc 1 (x ^ 2)).filter fun n => n % (p * L) = r % (p * L)).card : ℝ)
    set M := ((x ^ 2 : ℕ) : ℝ) / ((p : ℝ) * (L : ℝ))
    have hdiff : |selLam D d₁ * selLam D d₂ * (C - M)| ≤ |selLam D d₁| * |selLam D d₂| := by
      rw [abs_mul, abs_mul]
      calc
        |selLam D d₁| * |selLam D d₂| * |C - M|
          ≤ |selLam D d₁| * |selLam D d₂| * 1 :=
            mul_le_mul_of_nonneg_left habs (mul_nonneg (abs_nonneg _) (abs_nonneg _))
        _ = |selLam D d₁| * |selLam D d₂| := mul_one _
    have hle := (abs_le.mp hdiff).2
    linarith
  have hmain :
      (∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D,
        selLam D d₁ * selLam D d₂ * (((x ^ 2 : ℕ) : ℝ) / ((p : ℝ) * ((Nat.lcm d₁ d₂ : ℕ) : ℝ)))) =
      ((x ^ 2 : ℕ) : ℝ) / ((p : ℝ) * selG D) := by
    calc
      (∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D,
        selLam D d₁ * selLam D d₂ * (((x ^ 2 : ℕ) : ℝ) / ((p : ℝ) * ((Nat.lcm d₁ d₂ : ℕ) : ℝ))))
        = (((x ^ 2 : ℕ) : ℝ) / (p : ℝ)) *
            (∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D,
              selLam D d₁ * selLam D d₂ / ((Nat.lcm d₁ d₂ : ℕ) : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d₁ _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro d₂ _
          ring
      _ = (((x ^ 2 : ℕ) : ℝ) / (p : ℝ)) * (1 / selG D) := by rw [selberg_quad_form hD1]
      _ = ((x ^ 2 : ℕ) : ℝ) / ((p : ℝ) * selG D) := by ring
  have herr :
      (∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D, |selLam D d₁| * |selLam D d₂|) ≤ (D : ℝ) ^ 2 := by
    have hcard : ((sqfD D).card : ℝ) ≤ (D : ℝ) := by
      have h1 : (sqfD D).card ≤ (Finset.Icc 1 D).card := Finset.card_filter_le _ _
      rw [Nat.card_Icc] at h1
      have h2 : (sqfD D).card ≤ D := by omega
      exact_mod_cast h2
    calc
      (∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D, |selLam D d₁| * |selLam D d₂|)
        ≤ ∑ _d₁ ∈ sqfD D, ∑ _d₂ ∈ sqfD D, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro d₁ hd₁
          apply Finset.sum_le_sum
          intro d₂ hd₂
          have h1 := abs_selLam_le_one hD1 hd₁
          have h2 := abs_selLam_le_one hD1 hd₂
          nlinarith [abs_nonneg (selLam D d₁), abs_nonneg (selLam D d₂)]
      _ = ((sqfD D).card : ℝ) ^ 2 := by simp [sq]
      _ ≤ (D : ℝ) ^ 2 := pow_le_pow_left₀ (by positivity) hcard 2
  calc
    (Sp.card : ℝ) ≤ ∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D,
        selLam D d₁ * selLam D d₂ *
          (((Finset.Icc 1 (x ^ 2)).filter fun n =>
            n % p = a p % p ∧ congSys a d₁ n ∧ congSys a d₂ n).card : ℝ) := by
      rw [← hexpand]; exact hstep1
    _ ≤ ∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D,
        (selLam D d₁ * selLam D d₂ * (((x ^ 2 : ℕ) : ℝ) / ((p : ℝ) * ((Nat.lcm d₁ d₂ : ℕ) : ℝ))) +
          |selLam D d₁| * |selLam D d₂|) :=
      Finset.sum_le_sum fun d₁ hd₁ => Finset.sum_le_sum fun d₂ hd₂ => hterm_bound d₁ hd₁ d₂ hd₂
    _ = (∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D,
          selLam D d₁ * selLam D d₂ * (((x ^ 2 : ℕ) : ℝ) / ((p : ℝ) * ((Nat.lcm d₁ d₂ : ℕ) : ℝ)))) +
        (∑ d₁ ∈ sqfD D, ∑ d₂ ∈ sqfD D, |selLam D d₁| * |selLam D d₂|) := by
      simp only [Finset.sum_add_distrib]
    _ ≤ ((x ^ 2 : ℕ) : ℝ) / ((p : ℝ) * selG D) + (D : ℝ) ^ 2 := by
      rw [hmain]; linarith

/- ## Section 4: Harmonic lower bound for `selG D` -/

private lemma harmonic_pow_two :
    ∀ m : ℕ, (1 : ℝ) + (m : ℝ) / 2 ≤ ∑ j ∈ Finset.Icc (1 : ℕ) (2 ^ m), (1 : ℝ) / (j : ℝ) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    have hsplit : Finset.Icc 1 (2 ^ (m + 1)) =
        Finset.Icc 1 (2 ^ m) ∪ Finset.Icc (2 ^ m + 1) (2 ^ (m + 1)) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_union]
      have hpos : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      rw [Nat.pow_succ]
      omega
    have hdisj : Disjoint (Finset.Icc 1 (2 ^ m)) (Finset.Icc (2 ^ m + 1) (2 ^ (m + 1))) := by
      rw [Finset.disjoint_left]
      intro j h1 h2
      have := (Finset.mem_Icc.mp h1).2
      have := (Finset.mem_Icc.mp h2).1
      omega
    rw [hsplit, Finset.sum_union hdisj]
    have htail : (1 : ℝ) / 2 ≤ ∑ j ∈ Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1) : ℕ), (1 : ℝ) / (j : ℝ) := by
      have hcard : (Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1) : ℕ)).card = 2 ^ m := by
        rw [Nat.card_Icc, Nat.pow_succ]
        omega
      calc
        (1 : ℝ) / 2 = ((2 ^ m : ℕ) : ℝ) * ((1 : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ)) := by
          push_cast [pow_succ]
          have h2m : (2 : ℝ) ^ m ≠ 0 := by positivity
          field_simp [h2m]
        _ = ∑ _j ∈ Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1) : ℕ), (1 : ℝ) / ((2 ^ (m + 1) : ℕ) : ℝ) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
        _ ≤ ∑ j ∈ Finset.Icc (2 ^ m + 1 : ℕ) (2 ^ (m + 1) : ℕ), (1 : ℝ) / (j : ℝ) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj1 : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (show 0 < j by have := (Finset.mem_Icc.mp hj).1; omega)
          have hj2 : (j : ℝ) ≤ ((2 ^ (m + 1) : ℕ) : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).2
          exact one_div_le_one_div_of_le hj1 hj2
    push_cast
    linarith

private lemma sum_geom_prime_le {q : ℕ} (hq : q.Prime) (M : ℕ) :
    (∑ e ∈ Finset.Icc 1 M, (1 : ℝ) / ((q ^ e : ℕ) : ℝ)) ≤ 1 / ((q.totient : ℕ) : ℝ) := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq.two_le
  have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
  have hqm1 : (0 : ℝ) < (q : ℝ) - 1 := by linarith
  have htot : ((q.totient : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.totient_prime hq, Nat.cast_sub hq.one_lt.le]
    norm_num
  rw [htot, le_div_iff₀ hqm1]
  have htele :
      (∑ e ∈ Finset.Icc 1 M, (1 : ℝ) / ((q ^ e : ℕ) : ℝ)) * ((q : ℝ) - 1) =
      1 - (1 : ℝ) / (q : ℝ) ^ M := by
    induction M with
    | zero => simp
    | succ M ih =>
      have hsplit : Finset.Icc 1 (M + 1) = insert (M + 1) (Finset.Icc 1 M) := by
        ext e
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      have hnotmem : M + 1 ∉ Finset.Icc 1 M := by
        simp only [Finset.mem_Icc]; omega
      rw [hsplit, Finset.sum_insert hnotmem, add_mul, ih]
      push_cast [pow_succ]
      have hqM : (q : ℝ) ^ M ≠ 0 := by positivity
      field_simp [hqM, hqpos.ne']
      ring
  rw [htele]
  have hnonneg : (0 : ℝ) ≤ (1 : ℝ) / (q : ℝ) ^ M := by positivity
  linarith

private def rad (j : ℕ) : ℕ := ∏ q ∈ j.primeFactors, q

private lemma rad_pos {j : ℕ} : 0 < rad j := by
  unfold rad
  exact Finset.prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos

private lemma rad_le {j : ℕ} (hj : 1 ≤ j) : rad j ≤ j := by
  unfold rad
  exact Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd j)

private lemma rad_squarefree (j : ℕ) : Squarefree (rad j) := by
  unfold rad
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hdiv : ∀ S : Finset ℕ, (∀ q ∈ S, q.Prime) → ¬ (p * p ∣ ∏ q ∈ S, q) := by
    intro S
    induction S using Finset.induction with
    | empty =>
      intro _ h
      rw [Finset.prod_empty] at h
      have := Nat.le_of_dvd Nat.one_pos h
      have := hp.two_le
      nlinarith
    | insert a S ha ih =>
      intro hpr hdiv
      rw [Finset.prod_insert ha] at hdiv
      have hap : a.Prime := hpr a (Finset.mem_insert_self a S)
      have hSpr : ∀ q ∈ S, q.Prime := fun q hq => hpr q (Finset.mem_insert_of_mem hq)
      by_cases hpa : p = a
      · subst hpa
        have hpS : p ∣ ∏ q ∈ S, q := (mul_dvd_mul_iff_left hp.ne_zero).mp hdiv
        obtain ⟨q, hqS, hpq⟩ := hp.prime.exists_mem_finset_dvd hpS
        have hqp : q.Prime := hSpr q hqS
        have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq
        exact ha (heq ▸ hqS)
      · have hcop : (p * p).Coprime a :=
          ((Nat.coprime_primes hp hap).mpr hpa).mul_left ((Nat.coprime_primes hp hap).mpr hpa)
        exact ih hSpr (hcop.dvd_of_dvd_mul_left hdiv)
  exact hdiv j.primeFactors (fun q hq => Nat.prime_of_mem_primeFactors hq) hpp

private lemma primeFactors_rad (j : ℕ) : (rad j).primeFactors = j.primeFactors := by
  unfold rad
  ext p
  simp only [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hdvd, _⟩
    obtain ⟨q, hq, hpq⟩ := hp.prime.exists_mem_finset_dvd hdvd
    have hqp := Nat.prime_of_mem_primeFactors hq
    have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp hqp).mp hpq
    rw [heq]
    exact Nat.mem_primeFactors.mp hq
  · intro hp
    have hmem : p ∈ j.primeFactors := Nat.mem_primeFactors.mpr hp
    refine ⟨hp.1, Finset.dvd_prod_of_mem _ hmem, ?_⟩
    exact (Finset.prod_pos fun q hq => (Nat.prime_of_mem_primeFactors hq).pos).ne'

private lemma rad_mul_of_coprime {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hcop : a.Coprime b) :
    rad (a * b) = rad a * rad b := by
  unfold rad
  rw [Nat.primeFactors_mul ha hb]
  apply Finset.prod_union
  rw [Finset.disjoint_left]
  intro q hqa hqb
  have hqp := Nat.prime_of_mem_primeFactors hqa
  have h1 := Nat.dvd_of_mem_primeFactors hqa
  have h2 := Nat.dvd_of_mem_primeFactors hqb
  exact hqp.ne_one (Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2))

private lemma rad_prime_pow {q e : ℕ} (hq : q.Prime) (he : 1 ≤ e) : rad (q ^ e) = q := by
  unfold rad
  rw [Nat.primeFactors_pow q (by omega), hq.primeFactors, Finset.prod_singleton]

private lemma sum_rad_eq_le_inv_totient (M : ℕ) :
    ∀ d : ℕ, Squarefree d →
      (∑ j ∈ (Finset.Icc 1 M).filter (fun j => rad j = d), (1 : ℝ) / (j : ℝ)) ≤
        1 / (d.totient : ℝ) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd
    have hd0 : d ≠ 0 := hd.ne_zero
    by_cases hd1 : d = 1
    · subst hd1
      have hsub : (Finset.Icc 1 M).filter (fun j => rad j = 1) ⊆ {1} := by
        intro j hj
        obtain ⟨hI, hrad⟩ := Finset.mem_filter.mp hj
        have hj1 : 1 ≤ j := (Finset.mem_Icc.mp hI).1
        rw [Finset.mem_singleton]
        by_contra hne
        set q := j.minFac
        have hqp : q.Prime := Nat.minFac_prime (by omega)
        have hqj : q ∣ j := Nat.minFac_dvd j
        have hqrad : q ∣ rad j := Finset.dvd_prod_of_mem _ (Nat.mem_primeFactors.mpr ⟨hqp, hqj, by omega⟩)
        rw [hrad] at hqrad
        exact hqp.ne_one (Nat.eq_one_of_dvd_one hqrad)
      calc
        (∑ j ∈ (Finset.Icc 1 M).filter (fun j => rad j = 1), (1 : ℝ) / (j : ℝ))
          ≤ ∑ j ∈ ({1} : Finset ℕ), (1 : ℝ) / (j : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ = 1 / ((1 : ℕ).totient : ℝ) := by simp
    · set q := d.minFac
      have hqp : q.Prime := Nat.minFac_prime (by omega)
      have hqd : q ∣ d := Nat.minFac_dvd d
      set d' := d / q
      have hd_eq : q * d' = d := Nat.mul_div_cancel' hqd
      have hd'_lt : d' < d := Nat.div_lt_self (by omega) hqp.one_lt
      have hd'_sqf : Squarefree d' := hd.squarefree_of_dvd ⟨q, by rw [mul_comm, hd_eq]⟩
      have hcop : q.Coprime d' := squarefree_coprime_div hd hqp hqd
      have : Fact q.Prime := ⟨hqp⟩
      let S := (Finset.Icc 1 M).filter (fun j => rad j = d)
      let S' := (Finset.Icc 1 M).filter (fun j => rad j = d')
      let E := Finset.Icc 1 M
      have hsub : S ⊆ (E ×ˢ S').image (fun p : ℕ × ℕ => q ^ p.1 * p.2) := by
        intro j hj
        obtain ⟨hI, hrad⟩ := Finset.mem_filter.mp hj
        obtain ⟨hj1, hjM⟩ := Finset.mem_Icc.mp hI
        set e := padicValNat q j
        have hqj : q ∣ j := by
          have hqpf : q ∈ (rad j).primeFactors := by
            rw [hrad]
            exact Nat.mem_primeFactors.mpr ⟨hqp, hqd, hd0⟩
          rw [primeFactors_rad] at hqpf
          exact Nat.dvd_of_mem_primeFactors hqpf
        have he1 : 1 ≤ e := one_le_padicValNat_of_dvd (by omega) hqj
        have hqe_dvd : q ^ e ∣ j := pow_padicValNat_dvd
        set j' := j / q ^ e
        have hj_eq : q ^ e * j' = j := Nat.mul_div_cancel' hqe_dvd
        have hj'_pos : 1 ≤ j' := by
          have hj'_ne : j' ≠ 0 := by
            intro h0
            rw [h0, mul_zero] at hj_eq
            omega
          exact Nat.pos_of_ne_zero hj'_ne
        have hj'_le : j' ≤ M := (Nat.div_le_self j (q ^ e)).trans hjM
        have he_le : e ≤ M := by
          have h1 : e < 2 ^ e := Nat.lt_two_pow_self
          have h2 : 2 ^ e ≤ q ^ e := Nat.pow_le_pow_left hqp.two_le e
          have h3 : q ^ e ≤ j := Nat.le_of_dvd (by omega) hqe_dvd
          omega
        have hq_ndvd_j' : ¬ q ∣ j' := by
          intro hqj'
          have hqe1 : q ^ (e + 1) ∣ j := by
            rcases hqj' with ⟨t, ht⟩
            refine ⟨t, ?_⟩
            rw [← hj_eq, ht, pow_succ]
            ring
          have := (padicValNat_dvd_iff_le (show j ≠ 0 by omega)).mp hqe1
          omega
        have hcop_qj' : (q ^ e).Coprime j' := (hqp.coprime_iff_not_dvd.mpr hq_ndvd_j').pow_left e
        have hrad_j' : rad j' = d' := by
          have h1 : rad j = q * rad j' := by
            rw [← hj_eq, rad_mul_of_coprime (pow_ne_zero e hqp.ne_zero) (by omega) hcop_qj',
              rad_prime_pow hqp he1]
          rw [hrad, ← hd_eq] at h1
          exact (Nat.eq_of_mul_eq_mul_left hqp.pos h1).symm
        exact Finset.mem_image.mpr
          ⟨(e, j'), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨he1, he_le⟩,
            Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hj'_pos, hj'_le⟩, hrad_j'⟩⟩, hj_eq⟩
      calc
        (∑ j ∈ S, (1 : ℝ) / (j : ℝ))
          ≤ ∑ j ∈ (E ×ˢ S').image (fun p : ℕ × ℕ => q ^ p.1 * p.2), (1 : ℝ) / (j : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
        _ ≤ ∑ p ∈ E ×ˢ S', (1 : ℝ) / ((q ^ p.1 * p.2 : ℕ) : ℝ) :=
            Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)
        _ = (∑ e ∈ E, (1 : ℝ) / ((q ^ e : ℕ) : ℝ)) * (∑ j' ∈ S', (1 : ℝ) / (j' : ℝ)) := by
            rw [Finset.sum_product, Finset.sum_mul_sum]
            apply Finset.sum_congr rfl
            intro e _
            apply Finset.sum_congr rfl
            intro j' _
            push_cast
            ring
        _ ≤ (1 / ((q.totient : ℕ) : ℝ)) * (1 / (d'.totient : ℝ)) :=
            mul_le_mul (sum_geom_prime_le hqp M) (ih d' hd'_lt hd'_sqf)
              (Finset.sum_nonneg (fun _ _ => by positivity)) (by positivity)
        _ = 1 / (d.totient : ℝ) := by
            rw [← hd_eq, Nat.totient_mul hcop]
            push_cast
            ring

private lemma harmonic_le_selG (D : ℕ) :
    (∑ j ∈ Finset.Icc 1 D, (1 : ℝ) / (j : ℝ)) ≤ selG D := by
  have hfib :
      (∑ j ∈ Finset.Icc 1 D, (1 : ℝ) / (j : ℝ)) =
      ∑ d ∈ sqfD D, ∑ j ∈ (Finset.Icc 1 D).filter (fun j => rad j = d), (1 : ℝ) / (j : ℝ) := by
    symm
    apply Finset.sum_fiberwise_of_maps_to
    intro j hj
    obtain ⟨hj1, hjD⟩ := Finset.mem_Icc.mp hj
    exact mem_sqfD.mpr ⟨rad_pos, (rad_le hj1).trans hjD, rad_squarefree j⟩
  rw [hfib]
  apply Finset.sum_le_sum
  intro d hd
  exact sum_rad_eq_le_inv_totient D d (mem_sqfD.mp hd).2.2

end Erdos687IwaniecR2H2

theorem OMA.solution : OMA.R_Erdos687_erdos_687_variants_iwaniec_R2.H2 := by
  open Erdos687IwaniecR2H2 in
  refine Filter.eventually_atTop.mpr ⟨2 ^ 18, fun x hx a => ?_⟩
  set k := x.log2
  set m := k / 3
  set D := 2 ^ m
  have hk18 : 18 ≤ k := log2_ge_of_pow_le hx
  have hm6 : 6 ≤ m := by omega
  have h2k : 2 ^ k ≤ x := two_pow_log2_le (by omega)
  have hD1 : 1 ≤ D := Nat.one_le_two_pow
  have hD_half : D ≤ x / 2 := by
    have h1 : 2 ^ m * 2 ≤ 2 ^ k := by
      rw [← Nat.pow_succ]
      exact Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hG_lb : ((k + 1 : ℕ) : ℝ) / 8 ≤ selG D := by
    have h1 : (1 : ℝ) + (m : ℝ) / 2 ≤ selG D :=
      (harmonic_pow_two m).trans (harmonic_le_selG D)
    have h2 : ((k + 1 : ℕ) : ℝ) ≤ 4 * (m : ℝ) + 8 := by
      have hnat : k + 1 ≤ 4 * m + 8 := by omega
      exact_mod_cast hnat
    linarith
  have hG_pos : 0 < selG D := selG_pos hD1
  have hDsq_le : (D : ℝ) ^ 2 ≤ (x : ℝ) / ((k + 1 : ℕ) : ℝ) := by
    have hlin : k + 1 ≤ 2 ^ m := by
      have := linear_le_pow_two m hm6
      omega
    have hnat : D ^ 2 * (k + 1) ≤ x := by
      calc
        D ^ 2 * (k + 1) ≤ (2 ^ m) ^ 2 * 2 ^ m := Nat.mul_le_mul_left _ hlin
        _ = 2 ^ (3 * m) := by rw [← Nat.pow_mul, ← Nat.pow_add]; congr 1; omega
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ ≤ x := h2k
    have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    rw [le_div_iff₀ hkpos]
    exact_mod_cast hnat
  set small := (x / 2).primesLE
  set S := (Finset.Icc 1 (x ^ 2)).filter fun n => ∀ q ∈ small, n % q ≠ a q % q
  set band := x.primesLE \ small
  have hper_p : ∀ p ∈ band,
      ((S.filter fun n => n % p = a p % p).card : ℝ) ≤
        17 * (x : ℝ) / ((k + 1 : ℕ) : ℝ) := by
    intro p hp
    have hmem := Finset.mem_sdiff.mp hp
    have hpx := Nat.mem_primesLE.mp hmem.1
    have hp_gt : x / 2 < p := by
      by_contra hle
      exact hmem.2 (Nat.mem_primesLE.mpr ⟨by omega, hpx.2⟩)
    have hDp : D < p := lt_of_le_of_lt hD_half hp_gt
    have hsel := selberg_upper_bound a hD1 hpx.2 hDp hD_half
    have h2p : (x : ℝ) ≤ 2 * (p : ℝ) := by
      have hnat : x ≤ 2 * p := by omega
      exact_mod_cast hnat
    have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpx.2.pos
    have hmain_p : ((x ^ 2 : ℕ) : ℝ) / ((p : ℝ) * selG D) ≤
        16 * (x : ℝ) / ((k + 1 : ℕ) : ℝ) := by
      have h1 : ((x ^ 2 : ℕ) : ℝ) / (p : ℝ) ≤ 2 * (x : ℝ) := by
        rw [div_le_iff₀ hp_pos]
        push_cast
        nlinarith
      have h2 : (1 : ℝ) / selG D ≤ 8 / ((k + 1 : ℕ) : ℝ) := by
        have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
        rw [div_le_div_iff₀ hG_pos hkpos]
        linarith
      calc
        ((x ^ 2 : ℕ) : ℝ) / ((p : ℝ) * selG D)
          = (((x ^ 2 : ℕ) : ℝ) / (p : ℝ)) * (1 / selG D) := by ring
        _ ≤ (2 * (x : ℝ)) * (8 / ((k + 1 : ℕ) : ℝ)) :=
            mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = 16 * (x : ℝ) / ((k + 1 : ℕ) : ℝ) := by ring
    change ((S.filter fun n => n % p = a p % p).card : ℝ) ≤
      ((x ^ 2 : ℕ) : ℝ) / ((p : ℝ) * selG D) + (D : ℝ) ^ 2 at hsel
    have hadd : 16 * (x : ℝ) / ((k + 1 : ℕ) : ℝ) + (x : ℝ) / ((k + 1 : ℕ) : ℝ) =
        17 * (x : ℝ) / ((k + 1 : ℕ) : ℝ) := by ring
    linarith
  have hsum_R :
      ((∑ p ∈ band, (S.filter fun n => n % p = a p % p).card : ℕ) : ℝ) ≤
      51 * ((x : ℝ) / ((k + 1 : ℕ) : ℝ)) ^ 2 := by
    rw [Nat.cast_sum]
    calc
      (∑ p ∈ band, ((S.filter fun n => n % p = a p % p).card : ℝ))
        ≤ ∑ _p ∈ band, (17 * (x : ℝ) / ((k + 1 : ℕ) : ℝ)) := Finset.sum_le_sum hper_p
      _ = (band.card : ℝ) * (17 * (x : ℝ) / ((k + 1 : ℕ) : ℝ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (3 * (x : ℝ) / ((k + 1 : ℕ) : ℝ)) * (17 * (x : ℝ) / ((k + 1 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_right (card_primes_band_le hx) (by positivity)
      _ = 51 * ((x : ℝ) / ((k + 1 : ℕ) : ℝ)) ^ 2 := by ring
  set q := x / (k + 1)
  have hq_pos : 1 ≤ q := by
    have hlin : k + 1 ≤ 2 ^ m := by
      have := linear_le_pow_two m hm6
      omega
    have hpow : 2 ^ m ≤ x := (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_self _ _)).trans h2k
    exact Nat.div_pos (hlin.trans hpow) (by omega)
  have hratio_le : (x : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by
    have hkpos : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_iff₀ hkpos]
    have hnat : x ≤ 2 * q * (k + 1) := by
      have h1 : x < (q + 1) * (k + 1) := by
        have hdm : (k + 1) * q + x % (k + 1) = x := Nat.div_add_mod x (k + 1)
        have hlt := Nat.mod_lt x (show 0 < k + 1 by omega)
        nlinarith
      nlinarith
    exact_mod_cast hnat
  have hfinal_R :
      ((∑ p ∈ band, (S.filter fun n => n % p = a p % p).card : ℕ) : ℝ) ≤
      ((1000 * q ^ 2 : ℕ) : ℝ) := by
    calc
      ((∑ p ∈ band, (S.filter fun n => n % p = a p % p).card : ℕ) : ℝ)
        ≤ 51 * ((x : ℝ) / ((k + 1 : ℕ) : ℝ)) ^ 2 := hsum_R
      _ ≤ 51 * (2 * (q : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hratio_le 2) (by norm_num)
      _ = 204 * (q : ℝ) ^ 2 := by ring
      _ ≤ 1000 * (q : ℝ) ^ 2 := by nlinarith [sq_nonneg (q : ℝ)]
      _ = ((1000 * q ^ 2 : ℕ) : ℝ) := by push_cast; ring
  exact_mod_cast hfinal_R
