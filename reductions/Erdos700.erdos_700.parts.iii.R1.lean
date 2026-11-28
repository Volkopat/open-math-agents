import FormalConjectures.ErdosProblems.«700»
import Mathlib

-- Reduction Erdos700.erdos_700.parts.iii.R1 of Erdős Problem 700 — iii
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Erdős 700 (iii): the largest prime-power divisor settles all but the flat numbers

Let `f(n) = min_{1 < k ≤ n/2} gcd(n, C(n, k))` and let `Q(n)` be the largest prime-power divisor
`p ^ v_p(n)` of `n`. Proved below, with no hypothesis:

* `choose_prime_pow_modEq` (Lucas, iterated): if `p ^ a ∣ n` then `C(n, p ^ a) ≡ n / p ^ a (mod p)`.
* `gcd_choose_component`: for a prime `p ∣ n` with `v = v_p(n)`, `gcd(n, C(n, p ^ v)) = n / p ^ v`.
  Indeed `C(n, p ^ v) = (n / p ^ v) C(n - 1, p ^ v - 1)`, and `p` does not divide `C(n, p ^ v)`.
* `f_le_div_component`: hence `f(n) ≤ n / p ^ v` whenever `n ≠ p ^ v`; in particular
  `f(n) ≤ n / Q(n)` for every `n` that is not a prime power.
* `prime_pow_case`: for `n = p ^ a` with `a ≥ 2`, `f(n) = p ≤ √n`, and `(log n) ^ A ≤ (2 A) ^ A √n`
  (`log_rpow_le_sqrt`), so `f(n) ≤ (2 A) ^ A n / (log n) ^ A`.
* `nonflat_bound`: so `f(n) ≤ max(1, (2 A) ^ A) n / (log n) ^ A` for every composite `n` with
  `Q(n) ≥ (log n) ^ A`.
* `le_four_pow_mul`: `n ≤ 4 ^ Q(n) * Q(n) ^ (√Q(n) + 1)`, since the primes of `n` contribute at
  most the primorial of `Q(n)` (at most `4 ^ Q(n)`) and only primes `p ≤ √Q(n)` occur squared.
* `log_le_six_Q`: hence `log n ≤ 6 Q(n)` for every `n > 1`.
* `es_bound`: so `f(n) ≤ n / Q(n) ≤ 6 n / log n` for every composite `n` that is not a prime
  power, and also for prime powers: the Erdős–Szekeres bound `f(n) ≪ n / log n`, with constant
  `6` in place of their `1 + o(1)`.

So `main` proves the target outright for every `0 < A ≤ 1`, and for `A > 1` on every composite
`n` with `Q(n) ≥ (log n) ^ A`. What remains, exactly the open range `A > 1`, are the flat
composite `n`, whose prime-power divisors all lie below `(log n) ^ A`. The two hypotheses are the
target on these numbers, split by squarefreeness; each is a special case of the target.

* `H1`: for `A > 1`, the bound for squarefree flat composite `n` (all prime factors below
  `(log n) ^ A`).
* `H2`: for `A > 1`, the bound for flat composite `n` that are not squarefree.
-/

namespace OMA.R_Erdos700_erdos_700_parts_iii_R1

open Erdos700

/-- For `A > 1`: the bound `f(n) ≤ C n / (log n) ^ A` for squarefree composite `n` all of whose
prime factors (equivalently its largest prime-power divisor `Q n`) lie below `(log n) ^ A`. -/
def H1 : Prop :=
  ∀ A : ℝ, 1 < A → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ¬ n.Prime → 1 < n → Squarefree n →
    (Q n : ℝ) < Real.log n ^ A → (f n : ℝ) ≤ C * (n : ℝ) / Real.log n ^ A

/-- For `A > 1`: the bound `f(n) ≤ C n / (log n) ^ A` for composite `n` that are not squarefree
and whose largest prime-power divisor `Q n` lies below `(log n) ^ A`. -/
def H2 : Prop :=
  ∀ A : ℝ, 1 < A → ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ¬ n.Prime → 1 < n → ¬ Squarefree n →
    (Q n : ℝ) < Real.log n ^ A → (f n : ℝ) ≤ C * (n : ℝ) / Real.log n ^ A

/-- Lucas' theorem, iterated: if `p ^ a ∣ n` then `C(n, p ^ a) ≡ n / p ^ a (mod p)`. -/
lemma choose_prime_pow_modEq {p : ℕ} (hp : p.Prime) :
    ∀ (a n : ℕ), p ^ a ∣ n → n.choose (p ^ a) ≡ n / p ^ a [MOD p] := by
  have : Fact p.Prime := ⟨hp⟩
  intro a
  induction a with
  | zero =>
    intro n _
    rw [pow_zero, Nat.choose_one_right, Nat.div_one]
  | succ a ih =>
    intro n hn
    have hpn : p ∣ n := (dvd_pow_self p (Nat.succ_ne_zero a)).trans hn
    have hlucas : n.choose (p ^ (a + 1)) ≡
        (n % p).choose (p ^ (a + 1) % p) * (n / p).choose (p ^ (a + 1) / p) [MOD p] :=
      Choose.choose_modEq_choose_mod_mul_choose_div_nat
    have h1 : n % p = 0 := Nat.mod_eq_zero_of_dvd hpn
    have h2 : p ^ (a + 1) % p = 0 := Nat.mod_eq_zero_of_dvd (dvd_pow_self p (Nat.succ_ne_zero a))
    have h3 : p ^ (a + 1) / p = p ^ a := by
      rw [pow_succ]
      exact Nat.mul_div_cancel _ hp.pos
    rw [h1, h2, h3, Nat.choose_zero_right, one_mul] at hlucas
    have hdiv : p ^ a ∣ n / p := Nat.dvd_div_of_mul_dvd (by rw [← pow_succ']; exact hn)
    have hih := ih (n / p) hdiv
    rw [Nat.div_div_eq_div_mul, ← pow_succ'] at hih
    exact hlucas.trans hih

/-- For a prime `p ∣ n` with `v = v_p(n)`: `gcd(n, C(n, p ^ v)) = n / p ^ v`. -/
lemma gcd_choose_component {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    Nat.gcd n (n.choose (p ^ n.factorization p)) = n / p ^ n.factorization p := by
  set v := n.factorization p with hv
  set m := n / p ^ v with hm
  have hpv : p ^ v ∣ n := Nat.ordProj_dvd n p
  have hnm : n = p ^ v * m := (Nat.mul_div_cancel' hpv).symm
  have hpm : ¬ p ∣ m := Nat.not_dvd_ordCompl hp hn
  have hpv0 : 0 < p ^ v := pow_pos hp.pos v
  have hmC : m ∣ n.choose (p ^ v) := by
    have key := Nat.add_one_mul_choose_eq (n - 1) (p ^ v - 1)
    have h1 : n - 1 + 1 = n := Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero hn)
    have h2 : p ^ v - 1 + 1 = p ^ v := Nat.succ_pred_eq_of_pos hpv0
    rw [h1, h2] at key
    refine ⟨(n - 1).choose (p ^ v - 1), ?_⟩
    have hh : p ^ v * (m * (n - 1).choose (p ^ v - 1)) = p ^ v * n.choose (p ^ v) := by
      rw [← mul_assoc, ← hnm, key, mul_comm]
    exact (Nat.eq_of_mul_eq_mul_left hpv0 hh).symm
  have hpC : ¬ p ∣ n.choose (p ^ v) := by
    intro h
    have hmod : n.choose (p ^ v) % p = m % p := choose_prime_pow_modEq hp v n hpv
    have h0 : n.choose (p ^ v) % p = 0 := Nat.mod_eq_zero_of_dvd h
    rw [hmod] at h0
    exact hpm (Nat.dvd_of_mod_eq_zero h0)
  have hcop : Nat.Coprime (p ^ v) (n.choose (p ^ v)) :=
    Nat.Coprime.pow_left v ((Nat.Prime.coprime_iff_not_dvd hp).2 hpC)
  calc Nat.gcd n (n.choose (p ^ v)) = Nat.gcd (p ^ v * m) (n.choose (p ^ v)) := by
        rw [← hnm]
    _ = Nat.gcd m (n.choose (p ^ v)) := Nat.Coprime.gcd_mul_left_cancel m hcop
    _ = m := Nat.gcd_eq_left hmC

/-- `f(n) ≤ n / p ^ v` for a prime `p ∣ n`, `v = v_p(n)`, when `n` is not the power `p ^ v`. -/
lemma f_le_div_component {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hpn : p ∣ n)
    (hne : n ≠ p ^ n.factorization p) : f n ≤ n / p ^ n.factorization p := by
  have hpv : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
  have hv1 : 1 ≤ n.factorization p := (hp.dvd_iff_one_le_factorization hn).1 hpn
  have h1 : 1 < p ^ n.factorization p := Nat.one_lt_pow (by omega) hp.one_lt
  obtain ⟨m, hm⟩ := hpv
  have hm2 : 2 ≤ m := by
    by_contra hlt
    rcases (show m = 0 ∨ m = 1 by omega) with h0 | h0
    · rw [h0, mul_zero] at hm
      exact hn hm
    · rw [h0, mul_one] at hm
      exact hne hm
  have h2 : p ^ n.factorization p ≤ n / 2 := by
    rw [Nat.le_div_iff_mul_le (by norm_num)]
    calc p ^ n.factorization p * 2 ≤ p ^ n.factorization p * m := Nat.mul_le_mul_left _ hm2
      _ = n := hm.symm
  have hf := f_le n (p ^ n.factorization p) h1 h2
  rwa [gcd_choose_component hp hn] at hf

/-- `(log x) ^ A ≤ (2 A) ^ A √x` for `x ≥ 1` and `A > 0`. -/
lemma log_rpow_le_sqrt {A x : ℝ} (hA : 0 < A) (hx : 1 ≤ x) :
    Real.log x ^ A ≤ (2 * A) ^ A * Real.sqrt x := by
  have hA0 : A ≠ 0 := hA.ne'
  have hε : 0 < 1 / (2 * A) := by positivity
  have hx0 : 0 ≤ x := by linarith
  have hlog := Real.log_le_rpow_div hx0 hε
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hxe : 0 ≤ x ^ (1 / (2 * A)) := Real.rpow_nonneg hx0 _
  calc Real.log x ^ A ≤ (x ^ (1 / (2 * A)) / (1 / (2 * A))) ^ A :=
        Real.rpow_le_rpow hlog0 hlog hA.le
    _ = ((2 * A) * x ^ (1 / (2 * A))) ^ A := by
        congr 1
        field_simp
    _ = (2 * A) ^ A * (x ^ (1 / (2 * A))) ^ A := Real.mul_rpow (by positivity) hxe
    _ = (2 * A) ^ A * x ^ (1 / (2 * A) * A) := by rw [← Real.rpow_mul hx0]
    _ = (2 * A) ^ A * Real.sqrt x := by
        rw [Real.sqrt_eq_rpow]
        congr 2
        field_simp

/-- The prime powers: `f(p ^ a) = p ≤ (2 A) ^ A p ^ a / (log p ^ a) ^ A` for `a ≥ 2`. -/
lemma prime_pow_case {p a : ℕ} (hp : p.Prime) (ha : 2 ≤ a) {A : ℝ} (hA : 0 < A) :
    (f (p ^ a) : ℝ) ≤ (2 * A) ^ A * ((p ^ a : ℕ) : ℝ) / Real.log ((p ^ a : ℕ) : ℝ) ^ A := by
  rw [erdos_700.variants.prime_pow p a hp ha]
  have hpa : p ^ 2 ≤ p ^ a := Nat.pow_le_pow_right hp.pos ha
  have hp2 : 2 ≤ p := hp.two_le
  have hn1 : (1 : ℝ) < ((p ^ a : ℕ) : ℝ) := by
    have : 4 ≤ p ^ a := le_trans (by nlinarith) hpa
    exact_mod_cast (show 1 < p ^ a by omega)
  have hL : 0 < Real.log ((p ^ a : ℕ) : ℝ) ^ A := Real.rpow_pos_of_pos (Real.log_pos hn1) A
  rw [le_div_iff₀ hL]
  have hsq : (p : ℝ) ≤ Real.sqrt ((p ^ a : ℕ) : ℝ) := by
    rw [show (p : ℝ) = Real.sqrt ((p : ℝ) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    exact_mod_cast hpa
  have hb := log_rpow_le_sqrt hA hn1.le
  calc (p : ℝ) * Real.log ((p ^ a : ℕ) : ℝ) ^ A
        ≤ Real.sqrt ((p ^ a : ℕ) : ℝ) * ((2 * A) ^ A * Real.sqrt ((p ^ a : ℕ) : ℝ)) :=
        mul_le_mul hsq hb (by positivity) (Real.sqrt_nonneg _)
    _ = (2 * A) ^ A * ((p ^ a : ℕ) : ℝ) := by
        rw [mul_comm, mul_assoc, Real.mul_self_sqrt (by positivity)]

/-- `Q n` is attained: it is `p ^ v_p(n)` for some prime factor `p` of `n`. -/
lemma Q_spec {n : ℕ} (hn1 : 1 < n) :
    ∃ p ∈ n.primeFactors, Q n = p ^ n.factorization p := by
  have hne : n.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 hn1
  obtain ⟨p, hpmem, hpQ⟩ :=
    Finset.exists_mem_eq_sup n.primeFactors hne (fun p => p ^ n.factorization p)
  refine ⟨p, hpmem, ?_⟩
  unfold Q
  exact hpQ

/-- Every prime-power component `p ^ v_p(n)` is at most `Q n`. -/
lemma component_le_Q {n p : ℕ} (hp : p ∈ n.primeFactors) : p ^ n.factorization p ≤ Q n := by
  unfold Q
  exact Finset.le_sup (f := fun p => p ^ n.factorization p) hp

/-- A prime factor `p` of `n` is at most its component `p ^ v_p(n)`. -/
lemma prime_le_component {n p : ℕ} (hp : p ∈ n.primeFactors) : p ≤ p ^ n.factorization p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hn0 : n ≠ 0 := (Nat.mem_primeFactors.1 hp).2.2
  have hv : 1 ≤ n.factorization p :=
    (hpp.dvd_iff_one_le_factorization hn0).1 (Nat.dvd_of_mem_primeFactors hp)
  calc p = p ^ 1 := (pow_one p).symm
    _ ≤ p ^ n.factorization p := Nat.pow_le_pow_right hpp.pos hv

/-- `Q n ≥ 2` for `n > 1`. -/
lemma two_le_Q {n : ℕ} (hn1 : 1 < n) : 2 ≤ Q n := by
  obtain ⟨p, hpmem, hpQ⟩ := Q_spec hn1
  rw [hpQ]
  exact (Nat.prime_of_mem_primeFactors hpmem).two_le.trans (prime_le_component hpmem)

/-- `n ≤ 4 ^ Q(n) * Q(n) ^ (⌊√Q(n)⌋ + 1)`. Write `p ^ v = p * p ^ (v - 1)`: the primes contribute
at most the primorial of `Q(n)`, and only primes `p` with `p * p ≤ Q(n)` occur to a power above
`1`. -/
lemma le_four_pow_mul {n : ℕ} (hn1 : 1 < n) :
    n ≤ 4 ^ Q n * Q n ^ (Nat.sqrt (Q n) + 1) := by
  have hn0 : n ≠ 0 := by omega
  have hq0 : 0 < Q n := by have := two_le_Q hn1; omega
  have hfac : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    have h := Nat.prod_factorization_pow_eq_self hn0
    rw [Finsupp.prod, Nat.support_factorization] at h
    exact h.symm
  have hsplit : ∏ p ∈ n.primeFactors, p ^ n.factorization p =
      (∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hv : 1 ≤ n.factorization p :=
      (hpp.dvd_iff_one_le_factorization hn0).1 (Nat.dvd_of_mem_primeFactors hp)
    rw [← pow_succ']
    congr 1
    omega
  have h1 : ∏ p ∈ n.primeFactors, p ≤ 4 ^ Q n := by
    calc ∏ p ∈ n.primeFactors, p ≤ primorial (Q n) := by
          unfold primorial
          apply Finset.prod_le_prod_of_subset_of_one_le'
          · intro p hp
            rw [Finset.mem_filter, Finset.mem_range]
            exact ⟨Nat.lt_succ_of_le ((prime_le_component hp).trans (component_le_Q hp)),
              Nat.prime_of_mem_primeFactors hp⟩
          · intro p hp _
            exact (Finset.mem_filter.1 hp).2.one_lt.le
      _ ≤ 4 ^ Q n := primorial_le_four_pow (Q n)
  have hfilt : ∏ p ∈ n.primeFactors with 2 ≤ n.factorization p, p ^ (n.factorization p - 1) =
      ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) := by
    apply Finset.prod_filter_of_ne
    intro p _ hne
    by_contra hv
    apply hne
    have h0 : n.factorization p - 1 = 0 := by omega
    rw [h0, pow_zero]
  have hcard : (n.primeFactors.filter (fun p => 2 ≤ n.factorization p)).card ≤
      Nat.sqrt (Q n) + 1 := by
    calc (n.primeFactors.filter (fun p => 2 ≤ n.factorization p)).card
        ≤ (Finset.range (Nat.sqrt (Q n) + 1)).card := by
          apply Finset.card_le_card
          intro p hp
          obtain ⟨hp', hv⟩ := Finset.mem_filter.1 hp
          rw [Finset.mem_range, Nat.lt_succ_iff, Nat.le_sqrt]
          calc p * p = p ^ 2 := (sq p).symm
            _ ≤ p ^ n.factorization p :=
                Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp').pos hv
            _ ≤ Q n := component_le_Q hp'
      _ = Nat.sqrt (Q n) + 1 := Finset.card_range _
  have h2 : ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) ≤
      Q n ^ (Nat.sqrt (Q n) + 1) := by
    rw [← hfilt]
    calc ∏ p ∈ n.primeFactors with 2 ≤ n.factorization p, p ^ (n.factorization p - 1)
        ≤ ∏ p ∈ n.primeFactors with 2 ≤ n.factorization p, Q n := by
          apply Finset.prod_le_prod'
          intro p hp
          have hp' := (Finset.mem_filter.1 hp).1
          calc p ^ (n.factorization p - 1) ≤ p ^ n.factorization p :=
                Nat.pow_le_pow_right (Nat.prime_of_mem_primeFactors hp').pos (by omega)
            _ ≤ Q n := component_le_Q hp'
      _ = Q n ^ (n.primeFactors.filter (fun p => 2 ≤ n.factorization p)).card :=
          Finset.prod_const _
      _ ≤ Q n ^ (Nat.sqrt (Q n) + 1) := Nat.pow_le_pow_right hq0 hcard
  calc n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := hfac
    _ = (∏ p ∈ n.primeFactors, p) * ∏ p ∈ n.primeFactors, p ^ (n.factorization p - 1) := hsplit
    _ ≤ 4 ^ Q n * Q n ^ (Nat.sqrt (Q n) + 1) := Nat.mul_le_mul h1 h2

/-- `log n ≤ 6 Q(n)` for `n > 1`: from `le_four_pow_mul`, `log 4 < 2` and `log q ≤ 2 √q`. -/
lemma log_le_six_Q {n : ℕ} (hn1 : 1 < n) : Real.log n ≤ 6 * Q n := by
  have hq2 : (2 : ℝ) ≤ Q n := by exact_mod_cast two_le_Q hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hle : (n : ℝ) ≤ (4 : ℝ) ^ Q n * (Q n : ℝ) ^ (Nat.sqrt (Q n) + 1) := by
    exact_mod_cast le_four_pow_mul hn1
  have hqpos : (0 : ℝ) < Q n := by linarith
  have hlog : Real.log n ≤
      (Q n : ℝ) * Real.log 4 + ((Nat.sqrt (Q n) : ℝ) + 1) * Real.log (Q n) := by
    calc Real.log n ≤ Real.log ((4 : ℝ) ^ Q n * (Q n : ℝ) ^ (Nat.sqrt (Q n) + 1)) :=
          Real.log_le_log hnpos hle
      _ = (Q n : ℝ) * Real.log 4 + ((Nat.sqrt (Q n) : ℝ) + 1) * Real.log (Q n) := by
          rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow]
          push_cast
          ring
  have hl4 : Real.log 4 < 2 := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      push_cast
      ring
    have h2 := Real.log_two_lt_d9
    rw [h4]
    linarith
  have hs : (Nat.sqrt (Q n) : ℝ) ≤ Real.sqrt (Q n) := Real.nat_sqrt_le_real_sqrt
  have hr0 : 0 ≤ Real.sqrt (Q n) := Real.sqrt_nonneg _
  have hrr : Real.sqrt (Q n) ^ 2 = Q n := Real.sq_sqrt hqpos.le
  have hr1 : 1 ≤ Real.sqrt (Q n) := by
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ Real.sqrt (Q n) := Real.sqrt_le_sqrt (by linarith)
  have hrq : Real.sqrt (Q n) ≤ Q n := by nlinarith
  have hlq : Real.log (Q n) ≤ 2 * Real.sqrt (Q n) := by
    have h := Real.log_le_rpow_div hqpos.le (by norm_num : (0 : ℝ) < 1 / 2)
    rw [← Real.sqrt_eq_rpow] at h
    linarith
  have hlq0 : 0 ≤ Real.log (Q n) := Real.log_nonneg (by linarith)
  have ha : ((Nat.sqrt (Q n) : ℝ) + 1) * Real.log (Q n) ≤
      (Real.sqrt (Q n) + 1) * (2 * Real.sqrt (Q n)) :=
    mul_le_mul (by linarith) hlq hlq0 (by linarith)
  have hb : (Real.sqrt (Q n) + 1) * (2 * Real.sqrt (Q n)) =
      2 * Real.sqrt (Q n) ^ 2 + 2 * Real.sqrt (Q n) := by ring
  rw [hrr] at hb
  have hql4 : (Q n : ℝ) * Real.log 4 ≤ 2 * Q n := by nlinarith
  linarith

/-- The Erdős–Szekeres bound, with constant `6`: `f(n) ≤ 6 n / log n` for every composite `n`. -/
lemma es_bound {n : ℕ} (hnp : ¬ n.Prime) (hn1 : 1 < n) :
    (f n : ℝ) ≤ 6 * n / Real.log n := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn1
  have hL : 0 < Real.log n := Real.log_pos hnR
  obtain ⟨p, hpmem, hQeq⟩ := Q_spec hn1
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
  have hn0 : n ≠ 0 := by omega
  by_cases hpow : n = p ^ n.factorization p
  · have ha2 : 2 ≤ n.factorization p := by
      by_contra h
      rcases (show n.factorization p = 1 ∨ n.factorization p = 0 by omega) with h' | h'
      · rw [h', pow_one] at hpow
        exact hnp (by rw [hpow]; exact hp)
      · rw [h', pow_zero] at hpow
        omega
    have hpp := prime_pow_case hp ha2 one_pos
    rw [← hpow] at hpp
    simp only [mul_one, Real.rpow_one] at hpp
    refine hpp.trans ?_
    apply div_le_div_of_nonneg_right _ hL.le
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  · have hfle := f_le_div_component hp hn0 hpn hpow
    have hdvd : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
    have hQpos : (0 : ℝ) < ((p ^ n.factorization p : ℕ) : ℝ) := by
      have : 0 < p ^ n.factorization p := pow_pos hp.pos _
      exact_mod_cast this
    have hcast : ((n / p ^ n.factorization p : ℕ) : ℝ) =
        (n : ℝ) / ((p ^ n.factorization p : ℕ) : ℝ) := Nat.cast_div hdvd hQpos.ne'
    have hsix : Real.log n ≤ 6 * ((p ^ n.factorization p : ℕ) : ℝ) := by
      have h6 := log_le_six_Q hn1
      rw [hQeq] at h6
      exact h6
    calc (f n : ℝ) ≤ ((n / p ^ n.factorization p : ℕ) : ℝ) := by exact_mod_cast hfle
      _ = (n : ℝ) / ((p ^ n.factorization p : ℕ) : ℝ) := hcast
      _ ≤ 6 * n / Real.log n := by
          rw [div_le_div_iff₀ hQpos hL]
          nlinarith [Nat.cast_nonneg (α := ℝ) n]

/-- Enlarging the constant. -/
lemma mono_C {x C' C n L : ℝ} (hL : 0 < L) (hn : 0 ≤ n) (hC : C' ≤ C) (h : x ≤ C' * n / L) :
    x ≤ C * n / L :=
  h.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hC hn) hL.le)

/-- The non-flat case: `f(n) ≤ max(1, (2 A) ^ A) n / (log n) ^ A` when `Q(n) ≥ (log n) ^ A`. -/
lemma nonflat_bound {A : ℝ} (hA : 0 < A) {n : ℕ} (hnp : ¬ n.Prime) (hn1 : 1 < n)
    (hQ' : Real.log n ^ A ≤ (Q n : ℝ)) :
    (f n : ℝ) ≤ max 1 ((2 * A) ^ A) * n / Real.log n ^ A := by
  have hnR : (1 : ℝ) < n := by exact_mod_cast hn1
  have hL : 0 < Real.log n ^ A := Real.rpow_pos_of_pos (Real.log_pos hnR) A
  obtain ⟨p, hpmem, hQeq⟩ := Q_spec hn1
  have hp : p.Prime := Nat.prime_of_mem_primeFactors hpmem
  have hpn : p ∣ n := Nat.dvd_of_mem_primeFactors hpmem
  have hn0 : n ≠ 0 := by omega
  by_cases hpow : n = p ^ n.factorization p
  · have ha2 : 2 ≤ n.factorization p := by
      by_contra h
      rcases (show n.factorization p = 1 ∨ n.factorization p = 0 by omega) with h' | h'
      · rw [h', pow_one] at hpow
        exact hnp (by rw [hpow]; exact hp)
      · rw [h', pow_zero] at hpow
        omega
    have hpp := prime_pow_case hp ha2 hA
    rw [← hpow] at hpp
    exact mono_C hL (Nat.cast_nonneg n) (le_max_right _ _) hpp
  · have hfle := f_le_div_component hp hn0 hpn hpow
    have hdvd : p ^ n.factorization p ∣ n := Nat.ordProj_dvd n p
    have hQpos : (0 : ℝ) < ((p ^ n.factorization p : ℕ) : ℝ) := by
      have : 0 < p ^ n.factorization p := pow_pos hp.pos _
      exact_mod_cast this
    have hcast : ((n / p ^ n.factorization p : ℕ) : ℝ) =
        (n : ℝ) / ((p ^ n.factorization p : ℕ) : ℝ) := Nat.cast_div hdvd hQpos.ne'
    have hQ'' : Real.log n ^ A ≤ ((p ^ n.factorization p : ℕ) : ℝ) := by
      rw [← hQeq]
      exact hQ'
    have step : (f n : ℝ) ≤ 1 * n / Real.log n ^ A := by
      calc (f n : ℝ) ≤ ((n / p ^ n.factorization p : ℕ) : ℝ) := by exact_mod_cast hfle
        _ = (n : ℝ) / ((p ^ n.factorization p : ℕ) : ℝ) := hcast
        _ ≤ (n : ℝ) / Real.log n ^ A := div_le_div_of_nonneg_left (by positivity) hL hQ''
        _ = 1 * n / Real.log n ^ A := by ring
    exact mono_C hL (Nat.cast_nonneg n) (le_max_left _ _) step

theorem main : H1 → H2 → type_of% @Erdos700.erdos_700.parts.iii := by
  intro h1 h2 A hA
  by_cases hA1 : 1 < A
  · obtain ⟨C1, hC1, hb1⟩ := h1 A hA1
    obtain ⟨C2, hC2, hb2⟩ := h2 A hA1
    have hCpos : 0 < max (max C1 C2) (max 1 ((2 * A) ^ A)) :=
      lt_of_lt_of_le one_pos (le_trans (le_max_left _ _) (le_max_right _ _))
    refine ⟨max (max C1 C2) (max 1 ((2 * A) ^ A)), hCpos, ?_⟩
    intro n hnp hn1
    have hnR : (1 : ℝ) < n := by exact_mod_cast hn1
    have hL : 0 < Real.log n ^ A := Real.rpow_pos_of_pos (Real.log_pos hnR) A
    by_cases hQ : (Q n : ℝ) < Real.log n ^ A
    · by_cases hsq : Squarefree n
      · exact mono_C hL (Nat.cast_nonneg n) (le_trans (le_max_left _ _) (le_max_left _ _))
          (hb1 n hnp hn1 hsq hQ)
      · exact mono_C hL (Nat.cast_nonneg n) (le_trans (le_max_right _ _) (le_max_left _ _))
          (hb2 n hnp hn1 hsq hQ)
    · exact mono_C hL (Nat.cast_nonneg n) (le_max_right _ _)
        (nonflat_bound hA hnp hn1 (not_lt.mp hQ))
  · have hA1' : A ≤ 1 := not_lt.mp hA1
    refine ⟨6, by norm_num, ?_⟩
    intro n hnp hn1
    have h4 : 4 ≤ n := by
      by_contra h
      interval_cases n <;> norm_num at hnp
    have hlog1 : 1 ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le (by positivity)]
      have he := Real.exp_one_lt_d9
      have hn4 : (4 : ℝ) ≤ n := by exact_mod_cast h4
      linarith
    have hLA : 0 < Real.log n ^ A := Real.rpow_pos_of_pos (by linarith) A
    have hrpow : Real.log n ^ A ≤ Real.log n := by
      calc Real.log n ^ A ≤ Real.log n ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hlog1 hA1'
        _ = Real.log n := Real.rpow_one _
    calc (f n : ℝ) ≤ 6 * n / Real.log n := es_bound hnp hn1
      _ ≤ 6 * n / Real.log n ^ A := div_le_div_of_nonneg_left (by positivity) hLA hrpow

end OMA.R_Erdos700_erdos_700_parts_iii_R1
