import OMAReductions.R_OeisA215926_conjecture_1_R1
import Mathlib

-- Reduction OeisA215926.conjecture_1.R1.H1.R1 of step OeisA215926.conjecture_1.R1.H1
-- Credit: @chinwas

/-!
# Odd almost perfect numbers: squares with at least four prime factors

The parent step says that every odd `k` with `σ(k) = 2k - 1` (an odd *almost perfect* number)
is `k = 1`. This reduction proves, unconditionally:

1. `isSquare_of_odd_sigma`: if `k` is odd and `σ(k)` is odd then `k` is a perfect square.
   (`σ(k) = ∏ σ(p^e)`, and for odd `p` the sum `1 + p + ⋯ + p^e` is odd iff `e` is even.)
   Since `σ(k) = 2k - 1` is odd, every odd almost perfect number is a square.
2. `not_card_le_two`: no odd almost perfect number `k > 1` has at most two prime factors.
   * One prime: `σ(p^e)(p - 1) = p^(e+1) - 1` with `σ(p^e) = 2p^e - 1` gives `(p-2)(p^e-1) = 0`.
   * Two primes `p ≠ q`: `(p-1)(q-1)σ(k) < pq·k` contradicts `σ(k) = 2k - 1`, as `(p-2)(q-2) ≥ 3`.
3. `not_card_three`: no odd almost perfect square has exactly three prime factors.
   Write `k = p^(2a) q^(2b) r^(2c)` with `p < q < r`.
   * Abundancy: `(p-1)(q-1)(r-1)σ(k) < pqr·k` gives `k·D < (p-1)(q-1)(r-1)` with
     `D = 2(p-1)(q-1)(r-1) - pqr`, and `D ≥ 1` unless `p = 3`, `q = 5`, `r ≤ 13` (`D_pos`).
     So the primes are `3, 5, r` with `r ∈ {7, 11, 13}`.
   * Congruences: `σ(k) = 2k - 1 ≡ -1` modulo every prime factor of `k`, while the factors
     `σ(x^(2e))` are periodic in `e`: modulo `5` (for `r = 7`) the residues are
     `{1, 3}·1·{1, 2}`; modulo `3` (for `r = 11`) they are `1·1·1`; modulo `13` (for `r = 13`)
     they are `{0, 1, 4}·{1, 5}·1`. None of these products is `-1`.

So any odd almost perfect number other than `1` is an odd square with at least four distinct prime
factors. What remains:
- `H1`: odd squares with exactly four distinct prime factors;
- `H2`: odd squares with at least five distinct prime factors.
-/

namespace OMA.R_OeisA215926_conjecture_1_R1_H1_R1

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- No odd square with exactly four distinct prime factors is almost perfect. -/
def H1 : Prop :=
  ∀ k : ℕ, Odd k → IsSquare k → k.primeFactors.card = 4 → 1 + σ 1 k = 2 * k → False

/-- No odd square with at least five distinct prime factors is almost perfect. -/
def H2 : Prop :=
  ∀ k : ℕ, Odd k → IsSquare k → 5 ≤ k.primeFactors.card → 1 + σ 1 k = 2 * k → False

section Proof

/-- `σ(p^e)·(p - 1) = p^(e+1) - 1`, in `ℤ`. -/
theorem sigma_prime_pow_mul (p e : ℕ) (hp : p.Prime) :
    (σ 1 (p ^ e) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) ^ (e + 1) - 1 := by
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  exact geom_sum_mul _ _

/-- For odd `p`, `1 + p + ⋯ + p^(n-1)` has the parity of `n`. -/
theorem geom_sum_mod_two (p : ℕ) (hp : Odd p) (n : ℕ) :
    (∑ i ∈ Finset.range n, p ^ i) % 2 = n % 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Nat.add_mod, ih, Nat.odd_iff.1 hp.pow]
    omega

/-- If `k` is odd and `σ(k)` is odd, then `k` is a perfect square. -/
theorem isSquare_of_odd_sigma {k : ℕ} (hk : Odd k) (hs : Odd (σ 1 k)) : IsSquare k := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hev : ∀ p ∈ k.primeFactors, Even (k.factorization p) := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hpodd : Odd p := hk.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
    have hdvd : σ 1 (p ^ k.factorization p) ∣ σ 1 k := by
      rw [IsMultiplicative.multiplicative_factorization (σ 1) isMultiplicative_sigma hk0]
      unfold Finsupp.prod
      exact Finset.dvd_prod_of_mem (fun q => σ 1 (q ^ k.factorization q))
        (by simpa using hp)
    have hodd : Odd (σ 1 (p ^ k.factorization p)) := hs.of_dvd_nat hdvd
    rw [sigma_one_apply_prime_pow hpp, Nat.odd_iff, geom_sum_mod_two p hpodd] at hodd
    rw [Nat.even_iff]
    omega
  refine ⟨∏ p ∈ k.primeFactors, p ^ (k.factorization p / 2), ?_⟩
  rw [← Finset.prod_mul_distrib]
  conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hk0]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← pow_add]
  congr 1
  obtain ⟨r, hr⟩ := hev p hp
  omega

/-- `(p - 2)(q - 2) ≥ 3` for distinct odd primes. -/
theorem prod_sub_two_ge {p q : ℕ} (hp : 3 ≤ p) (hq : 3 ≤ q) (hpo : Odd p) (hqo : Odd q)
    (hpq : p ≠ q) : (3 : ℤ) ≤ ((p : ℤ) - 2) * ((q : ℤ) - 2) := by
  rcases Nat.odd_iff.1 hpo with hp2
  rcases Nat.odd_iff.1 hqo with hq2
  rcases (by omega : p = 3 ∨ 5 ≤ p) with rfl | hp5
  · have : 5 ≤ q := by omega
    have : (5 : ℤ) ≤ q := by exact_mod_cast this
    push_cast; nlinarith
  · have hp5' : (5 : ℤ) ≤ p := by exact_mod_cast hp5
    have hq' : (3 : ℤ) ≤ q := by exact_mod_cast hq
    nlinarith

/-- No odd almost perfect number `k > 1` has at most two distinct prime factors. -/
theorem not_card_le_two {k : ℕ} (hk : Odd k) (hk1 : k ≠ 1) (hc : k.primeFactors.card ≤ 2)
    (h : 1 + σ 1 k = 2 * k) : False := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hdecomp := Nat.prod_primeFactors_pow_factorization hk0
  have hodd_of_mem : ∀ p ∈ k.primeFactors, Odd p :=
    fun p hp => hk.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)
  have hpos_of_mem : ∀ p ∈ k.primeFactors, 0 < k.factorization p :=
    fun p hp => (Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hk0
      (Nat.dvd_of_mem_primeFactors hp)
  rcases (by omega : k.primeFactors.card = 0 ∨ k.primeFactors.card = 1 ∨
      k.primeFactors.card = 2) with h0 | h1 | h2
  · -- no prime factors: `k = 1`
    rcases Nat.primeFactors_eq_empty.1 (Finset.card_eq_zero.1 h0) with h' | h' <;> omega
  · -- one prime factor: `k = p^e`
    obtain ⟨p, hp⟩ := Finset.card_eq_one.1 h1
    have hmem : p ∈ k.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
    have hpp := Nat.prime_of_mem_primeFactors hmem
    have hpodd := hodd_of_mem p hmem
    have he := hpos_of_mem p hmem
    set e := k.factorization p
    rw [hp, Finset.prod_singleton] at hdecomp
    have hp3 : 3 ≤ p := by
      rcases Nat.odd_iff.1 hpodd with h'; have := hpp.two_le; omega
    have hS := sigma_prime_pow_mul p e hpp
    rw [← hdecomp] at hS
    have hX : (p : ℤ) ≤ (p : ℤ) ^ e := by
      exact_mod_cast Nat.le_self_pow (by omega) p
    have hσ : (σ 1 k : ℤ) = 2 * (p : ℤ) ^ e - 1 := by
      have : ((1 + σ 1 k : ℕ) : ℤ) = ((2 * k : ℕ) : ℤ) := by rw [h]
      push_cast at this
      rw [hdecomp] at this
      push_cast at this
      linarith
    rw [hσ, pow_succ] at hS
    have hp3' : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    have key : ((p : ℤ) - 2) * ((p : ℤ) ^ e - 1) = 0 := by linear_combination hS
    rcases mul_eq_zero.1 key with h' | h' <;> nlinarith
  · -- two prime factors: `k = p^a q^b`
    obtain ⟨p, q, hpq, hpqs⟩ := Finset.card_eq_two.1 h2
    have hpm : p ∈ k.primeFactors := by rw [hpqs]; simp
    have hqm : q ∈ k.primeFactors := by rw [hpqs]; simp
    have hpp := Nat.prime_of_mem_primeFactors hpm
    have hqp := Nat.prime_of_mem_primeFactors hqm
    have hpodd := hodd_of_mem p hpm
    have hqodd := hodd_of_mem q hqm
    have ha := hpos_of_mem p hpm
    have hb := hpos_of_mem q hqm
    set a := k.factorization p
    set b := k.factorization q
    rw [hpqs, Finset.prod_pair hpq] at hdecomp
    have hp3 : 3 ≤ p := by
      rcases Nat.odd_iff.1 hpodd with h'; have := hpp.two_le; omega
    have hq3 : 3 ≤ q := by
      rcases Nat.odd_iff.1 hqodd with h'; have := hqp.two_le; omega
    have hcop : Nat.Coprime (p ^ a) (q ^ b) :=
      Nat.Coprime.pow a b ((Nat.coprime_primes hpp hqp).2 hpq)
    have hσk : σ 1 k = σ 1 (p ^ a) * σ 1 (q ^ b) := by
      rw [hdecomp]; exact isMultiplicative_sigma.map_mul_of_coprime hcop
    have h1' := sigma_prime_pow_mul p a hpp
    have h2' := sigma_prime_pow_mul q b hqp
    set S1 : ℤ := (σ 1 (p ^ a) : ℤ)
    set S2 : ℤ := (σ 1 (q ^ b) : ℤ)
    set A : ℤ := (p : ℤ) ^ a with hA
    set B : ℤ := (q : ℤ) ^ b with hB
    rw [pow_succ] at h1' h2'
    have h3 : 1 + S1 * S2 = 2 * A * B := by
      have : ((1 + σ 1 k : ℕ) : ℤ) = ((2 * k : ℕ) : ℤ) := by rw [h]
      rw [hσk, hdecomp] at this
      push_cast at this
      linarith
    have hAp : (p : ℤ) ≤ A := by
      rw [hA]; exact_mod_cast Nat.le_self_pow (show a ≠ 0 by omega) p
    have hBq : (q : ℤ) ≤ B := by
      rw [hB]; exact_mod_cast Nat.le_self_pow (show b ≠ 0 by omega) q
    have hp3' : (3 : ℤ) ≤ p := by exact_mod_cast hp3
    have hq3' : (3 : ℤ) ≤ q := by exact_mod_cast hq3
    have hD := prod_sub_two_ge hp3 hq3 hpodd hqodd hpq
    have E : ((p : ℤ) - 1) * ((q : ℤ) - 1) + ((p : ℤ) * A - 1) * ((q : ℤ) * B - 1) =
        2 * A * B * ((p : ℤ) - 1) * ((q : ℤ) - 1) := by
      linear_combination ((p : ℤ) - 1) * ((q : ℤ) - 1) * h3 - (S2 * ((q : ℤ) - 1)) * h1' -
        ((p : ℤ) * A - 1) * h2'
    have hAB : (p : ℤ) * q ≤ A * B := mul_le_mul hAp hBq (by linarith) (by linarith)
    have hABpos : 0 ≤ A * B := by nlinarith
    have h5 : A * B ≤ A * B * (((p : ℤ) - 2) * ((q : ℤ) - 2) - 2) := by nlinarith
    have hpA : 0 ≤ (p : ℤ) * A := by nlinarith
    have hqB : 0 ≤ (q : ℤ) * B := by nlinarith
    nlinarith


/-- Geometric sums are periodic modulo `m` once a full period sums to a multiple of `m`. -/
theorem geom_mod_period (x m T : ℕ) (hT : 0 < T) (hdvd : m ∣ ∑ i ∈ range T, x ^ i) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) ≡ (∑ i ∈ range (n % T), x ^ i) [MOD m] := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < T
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨t, rfl⟩ : ∃ t, n = t + T := ⟨n - T, by omega⟩
      obtain ⟨j, hj⟩ := hdvd
      have hsplit : ∑ i ∈ range (t + T), x ^ i =
          ∑ i ∈ range t, x ^ i + m * (x ^ t * j) := by
        rw [Finset.sum_range_add]
        congr 1
        rw [show m * (x ^ t * j) = x ^ t * (m * j) by ring, ← hj, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_add]
      unfold Nat.ModEq
      rw [hsplit, Nat.add_mul_mod_self_left, Nat.add_mod_right]
      exact ih t (by omega)

/-- `1 + x + ⋯ + x^n ≡ 1 (mod x)`. -/
theorem geom_mod_self (x n : ℕ) : (∑ i ∈ range (n + 1), x ^ i) ≡ 1 [MOD x] := by
  rw [Finset.sum_range_succ', pow_zero]
  have : ∑ i ∈ range n, x ^ (i + 1) = x * ∑ i ∈ range n, x ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [this]
  unfold Nat.ModEq
  simp [Nat.add_mod]

/-- Combine residues of the three factors. -/
theorem residue_contra (m s1 s2 s3 c1 c2 c3 : ℕ) (h0 : (1 + s1 * s2 * s3) % m = 0)
    (h1 : s1 ≡ c1 [MOD m]) (h2 : s2 ≡ c2 [MOD m]) (h3 : s3 ≡ c3 [MOD m]) :
    (1 + c1 * c2 * c3) % m = 0 := by
  have e := Nat.ModEq.add_left 1 ((h1.mul h2).mul h3)
  unfold Nat.ModEq at e
  rw [← e]
  exact h0

/-- `σ(p^e) (p - 1) = p · p^e - 1`, in `ℤ`. -/
theorem sigma_pp_mul (p e : ℕ) (hp : p.Prime) :
    (σ 1 (p ^ e) : ℤ) * ((p : ℤ) - 1) = (p : ℤ) * (p : ℤ) ^ e - 1 := by
  rw [sigma_one_apply_prime_pow hp]
  push_cast
  rw [geom_sum_mul, pow_succ, mul_comm]

theorem cubic_lt (x y z : ℤ) (hx : 1 ≤ x) (hy : 1 ≤ y) (hz : 1 ≤ z) :
    (x - 1) * (y - 1) * (z - 1) < x * y * z := by
  nlinarith [mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hy), mul_nonneg (sub_nonneg.2 hy)
    (sub_nonneg.2 hz), mul_nonneg (sub_nonneg.2 hx) (sub_nonneg.2 hz)]

/-- `D = 2(p-1)(q-1)(r-1) - pqr ≥ 1` outside the three exceptional triples. -/
theorem D_pos (p q r : ℕ) (hr : r.Prime) (hp3 : 3 ≤ p) (hpq : p < q) (hqr : q < r)
    (hpo : Odd p) (hqo : Odd q) (hro : Odd r) (hns : ¬ (p = 3 ∧ q = 5 ∧ r ≤ 13)) :
    (1 : ℤ) ≤ 2 * ((p : ℤ) - 1) * ((q : ℤ) - 1) * ((r : ℤ) - 1) - (p : ℤ) * q * r := by
  have hp2 := Nat.odd_iff.1 hpo
  have hq2 := Nat.odd_iff.1 hqo
  have hr2 := Nat.odd_iff.1 hro
  rcases (by omega : 5 ≤ p ∨ p = 3) with hp5 | rfl
  · have u : (0 : ℤ) ≤ (p : ℤ) - 5 := by
      have : (5 : ℤ) ≤ p := by exact_mod_cast hp5
      linarith
    have v : (0 : ℤ) ≤ (q : ℤ) - 7 := by
      have : (7 : ℤ) ≤ q := by exact_mod_cast (show 7 ≤ q by omega)
      linarith
    have w : (0 : ℤ) ≤ (r : ℤ) - 9 := by
      have : (9 : ℤ) ≤ r := by exact_mod_cast (show 9 ≤ r by omega)
      linarith
    nlinarith [mul_nonneg u v, mul_nonneg u w, mul_nonneg v w, mul_nonneg (mul_nonneg u v) w]
  · rcases (by omega : 7 ≤ q ∨ q = 5) with hq7 | rfl
    · have v : (0 : ℤ) ≤ (q : ℤ) - 7 := by
        have : (7 : ℤ) ≤ q := by exact_mod_cast hq7
        linarith
      have w : (0 : ℤ) ≤ (r : ℤ) - 9 := by
        have : (9 : ℤ) ≤ r := by exact_mod_cast (show 9 ≤ r by omega)
        linarith
      push_cast
      nlinarith [mul_nonneg v w]
    · have h13 : 13 < r := by
        by_contra h'
        exact hns ⟨rfl, rfl, by omega⟩
      have hr17 : 17 ≤ r := by
        rcases (by omega : r = 15 ∨ 17 ≤ r) with h15 | h17
        · rw [h15] at hr; norm_num at hr
        · exact h17
      have w : (17 : ℤ) ≤ r := by exact_mod_cast hr17
      push_cast
      nlinarith

/-- The abundancy bound: `(p-1)(q-1)(r-1)σ(k) < pqr k` forces `p = 3`, `q = 5`, `r ≤ 13`. -/
theorem small (p q r a b c : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp3 : 3 ≤ p) (hpq : p < q) (hqr : q < r) (hpo : Odd p) (hqo : Odd q) (hro : Odd r)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : 1 + σ 1 (p ^ (2 * a)) * σ 1 (q ^ (2 * b)) * σ 1 (r ^ (2 * c)) =
      2 * (p ^ (2 * a) * q ^ (2 * b) * r ^ (2 * c))) : p = 3 ∧ q = 5 ∧ r ≤ 13 := by
  by_contra hns
  have hD := D_pos p q r hr hp3 hpq hqr hpo hqo hro hns
  have e1 := sigma_pp_mul p (2 * a) hp
  have e2 := sigma_pp_mul q (2 * b) hq
  have e3 := sigma_pp_mul r (2 * c) hr
  have h3 := congrArg (fun t : ℕ => (t : ℤ)) h
  push_cast at h3
  generalize (σ 1 (p ^ (2 * a)) : ℤ) = S1 at e1 h3
  generalize (σ 1 (q ^ (2 * b)) : ℤ) = S2 at e2 h3
  generalize (σ 1 (r ^ (2 * c)) : ℤ) = S3 at e3 h3
  have hAp : (p : ℤ) ≤ (p : ℤ) ^ (2 * a) := by exact_mod_cast Nat.le_self_pow (by omega) p
  have hBq : (q : ℤ) ≤ (q : ℤ) ^ (2 * b) := by exact_mod_cast Nat.le_self_pow (by omega) q
  have hCr : (r : ℤ) ≤ (r : ℤ) ^ (2 * c) := by exact_mod_cast Nat.le_self_pow (by omega) r
  generalize (p : ℤ) ^ (2 * a) = A at hAp e1 h3
  generalize (q : ℤ) ^ (2 * b) = B at hBq e2 h3
  generalize (r : ℤ) ^ (2 * c) = C at hCr e3 h3
  have hP : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  have hQ : (3 : ℤ) ≤ q := by exact_mod_cast (show 3 ≤ q by omega)
  have hR : (3 : ℤ) ≤ r := by exact_mod_cast (show 3 ≤ r by omega)
  generalize (p : ℤ) = P at *
  generalize (q : ℤ) = Q at *
  generalize (r : ℤ) = R at *
  have E : (P - 1) * (Q - 1) * (R - 1) * (2 * (A * B * C) - 1) =
      (P * A - 1) * (Q * B - 1) * (R * C - 1) := by
    linear_combination (-((P - 1) * (Q - 1) * (R - 1))) * h3 +
      (S2 * (Q - 1) * (S3 * (R - 1))) * e1 + ((P * A - 1) * (S3 * (R - 1))) * e2 +
      ((P * A - 1) * (Q * B - 1)) * e3
  have hx : (1 : ℤ) ≤ P * A := by nlinarith
  have hy : (1 : ℤ) ≤ Q * B := by nlinarith
  have hz : (1 : ℤ) ≤ R * C := by nlinarith
  have hlt := cubic_lt (P * A) (Q * B) (R * C) hx hy hz
  have hA0 : (0 : ℤ) ≤ A := by linarith
  have hB0 : (0 : ℤ) ≤ B := by linarith
  have hC0 : (0 : ℤ) ≤ C := by linarith
  have hABC0 : (0 : ℤ) ≤ A * B * C := mul_nonneg (mul_nonneg hA0 hB0) hC0
  have hAB : P * Q ≤ A * B := mul_le_mul hAp hBq (by linarith) hA0
  have hABC : P * Q * R ≤ A * B * C := mul_le_mul hAB hCr (by linarith) (mul_nonneg hA0 hB0)
  have hPQR : (P - 1) * (Q - 1) * (R - 1) < P * Q * R := cubic_lt P Q R (by linarith)
    (by linarith) (by linarith)
  have k1 : A * B * C * (2 * (P - 1) * (Q - 1) * (R - 1) - P * Q * R) <
      (P - 1) * (Q - 1) * (R - 1) := by
    have : (P * A) * (Q * B) * (R * C) = P * Q * R * (A * B * C) := by ring
    linarith [E, hlt, this]
  have k2 : A * B * C ≤ A * B * C * (2 * (P - 1) * (Q - 1) * (R - 1) - P * Q * R) := by
    exact le_mul_of_one_le_right hABC0 hD
  linarith

theorem case7 (a b c : ℕ) (h0 : (1 + (∑ i ∈ range (2 * a + 1), 3 ^ i) *
    (∑ i ∈ range (2 * b + 1), 5 ^ i) * (∑ i ∈ range (2 * c + 1), 7 ^ i)) % 5 = 0) : False := by
  have s1 := geom_mod_period 3 5 4 (by norm_num) (by norm_num [Finset.sum_range_succ]) (2 * a + 1)
  have s2 := geom_mod_self 5 (2 * b)
  have s3 := geom_mod_period 7 5 4 (by norm_num) (by norm_num [Finset.sum_range_succ]) (2 * c + 1)
  rcases (by omega : (2 * a + 1) % 4 = 1 ∨ (2 * a + 1) % 4 = 3) with ha | ha <;>
    rcases (by omega : (2 * c + 1) % 4 = 1 ∨ (2 * c + 1) % 4 = 3) with hc | hc <;>
    rw [ha] at s1 <;> rw [hc] at s3 <;>
    · have := residue_contra 5 _ _ _ _ _ _ h0 s1 s2 s3
      norm_num [Finset.sum_range_succ] at this

theorem case11 (a b c : ℕ) (h0 : (1 + (∑ i ∈ range (2 * a + 1), 3 ^ i) *
    (∑ i ∈ range (2 * b + 1), 5 ^ i) * (∑ i ∈ range (2 * c + 1), 11 ^ i)) % 3 = 0) : False := by
  have s1 := geom_mod_self 3 (2 * a)
  have s2 := geom_mod_period 5 3 2 (by norm_num) (by norm_num [Finset.sum_range_succ]) (2 * b + 1)
  have s3 := geom_mod_period 11 3 2 (by norm_num) (by norm_num [Finset.sum_range_succ]) (2 * c + 1)
  rw [show (2 * b + 1) % 2 = 1 by omega] at s2
  rw [show (2 * c + 1) % 2 = 1 by omega] at s3
  have := residue_contra 3 _ _ _ _ _ _ h0 s1 s2 s3
  norm_num [Finset.sum_range_succ] at this

theorem case13 (a b c : ℕ) (h0 : (1 + (∑ i ∈ range (2 * a + 1), 3 ^ i) *
    (∑ i ∈ range (2 * b + 1), 5 ^ i) * (∑ i ∈ range (2 * c + 1), 13 ^ i)) % 13 = 0) : False := by
  have s1 := geom_mod_period 3 13 3 (by norm_num) (by norm_num [Finset.sum_range_succ]) (2 * a + 1)
  have s2 := geom_mod_period 5 13 4 (by norm_num) (by norm_num [Finset.sum_range_succ]) (2 * b + 1)
  have s3 := geom_mod_self 13 (2 * c)
  rcases (by omega : (2 * a + 1) % 3 = 0 ∨ (2 * a + 1) % 3 = 1 ∨ (2 * a + 1) % 3 = 2)
    with ha | ha | ha <;>
    rcases (by omega : (2 * b + 1) % 4 = 1 ∨ (2 * b + 1) % 4 = 3) with hb | hb <;>
    rw [ha] at s1 <;> rw [hb] at s2 <;>
    · have := residue_contra 13 _ _ _ _ _ _ h0 s1 s2 s3
      norm_num [Finset.sum_range_succ] at this

/-- The core statement, for sorted primes. -/
theorem core (p q r a b c : ℕ) (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hp3 : 3 ≤ p) (hpq : p < q) (hqr : q < r) (hpo : Odd p) (hqo : Odd q) (hro : Odd r)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : 1 + σ 1 (p ^ (2 * a)) * σ 1 (q ^ (2 * b)) * σ 1 (r ^ (2 * c)) =
      2 * (p ^ (2 * a) * q ^ (2 * b) * r ^ (2 * c))) : False := by
  obtain ⟨rfl, rfl, hr13⟩ := small p q r a b c hp hq hr hp3 hpq hqr hpo hqo hro ha hb hc h
  have hmod : ∀ d, d ∣ 3 ^ (2 * a) * 5 ^ (2 * b) * r ^ (2 * c) →
      (1 + σ 1 (3 ^ (2 * a)) * σ 1 (5 ^ (2 * b)) * σ 1 (r ^ (2 * c))) % d = 0 := by
    intro d hd
    rw [h]
    exact Nat.mod_eq_zero_of_dvd (hd.mul_left 2)
  rw [sigma_one_apply_prime_pow Nat.prime_three,
    sigma_one_apply_prime_pow (by norm_num : Nat.Prime 5), sigma_one_apply_prime_pow hr] at hmod
  have d3 : 3 ∣ 3 ^ (2 * a) * 5 ^ (2 * b) * r ^ (2 * c) :=
    ((dvd_pow_self 3 (by omega)).mul_right _).mul_right _
  have d5 : 5 ∣ 3 ^ (2 * a) * 5 ^ (2 * b) * r ^ (2 * c) :=
    ((dvd_pow_self 5 (by omega)).mul_left _).mul_right _
  have dr : r ∣ 3 ^ (2 * a) * 5 ^ (2 * b) * r ^ (2 * c) :=
    (dvd_pow_self r (by omega)).mul_left _
  interval_cases r <;>
    first
    | exact case7 a b c (hmod 5 d5)
    | exact case11 a b c (hmod 3 d3)
    | exact case13 a b c (hmod 13 dr)
    | exact absurd hr (by norm_num)

/-- No odd almost perfect square has exactly three distinct prime factors. -/
theorem not_card_three : ∀ k : ℕ, Odd k → IsSquare k → k.primeFactors.card = 3 →
    1 + σ 1 k = 2 * k → False := by
  intro k hk hsq hc h
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  obtain ⟨m, rfl⟩ := hsq
  have hm0 : m ≠ 0 := by rintro rfl; simp at hk0
  have hpf : (m * m).primeFactors = m.primeFactors := by
    rw [Nat.primeFactors_mul hm0 hm0, Finset.union_self]
  obtain ⟨x, y, z, hxy, hxz, hyz, hs⟩ := Finset.card_eq_three.1 hc
  have hfac : ∀ p, (m * m).factorization p = 2 * m.factorization p := by
    intro p; rw [Nat.factorization_mul hm0 hm0]; simp [two_mul]
  have hdecomp := Nat.prod_primeFactors_pow_factorization hk0
  rw [hs, Finset.prod_insert (by simp [hxy, hxz]), Finset.prod_insert (by simp [hyz]),
    Finset.prod_singleton, hfac x, hfac y, hfac z, ← mul_assoc] at hdecomp
  have mem : ∀ p ∈ ({x, y, z} : Finset ℕ), p.Prime ∧ Odd p ∧ 1 ≤ m.factorization p := by
    intro p hp
    rw [← hs] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    refine ⟨hpp, hk.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp), ?_⟩
    rw [hpf] at hp
    exact hpp.factorization_pos_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨hxp, hxo, hxa⟩ := mem x (by simp)
  obtain ⟨hyp, hyo, hya⟩ := mem y (by simp)
  obtain ⟨hzp, hzo, hza⟩ := mem z (by simp)
  set a := m.factorization x
  set b := m.factorization y
  set c := m.factorization z
  have hcop : ∀ {u v : ℕ} (e f : ℕ), u.Prime → v.Prime → u ≠ v → Nat.Coprime (u ^ e) (v ^ f) :=
    fun e f hu hv huv => Nat.Coprime.pow e f ((Nat.coprime_primes hu hv).2 huv)
  have hσ : σ 1 (m * m) = σ 1 (x ^ (2 * a)) * σ 1 (y ^ (2 * b)) * σ 1 (z ^ (2 * c)) := by
    rw [hdecomp, isMultiplicative_sigma.map_mul_of_coprime
      (Nat.Coprime.mul_left (hcop _ _ hxp hzp hxz) (hcop _ _ hyp hzp hyz)),
      isMultiplicative_sigma.map_mul_of_coprime (hcop _ _ hxp hyp hxy)]
  have hE : 1 + σ 1 (x ^ (2 * a)) * σ 1 (y ^ (2 * b)) * σ 1 (z ^ (2 * c)) =
      2 * (x ^ (2 * a) * y ^ (2 * b) * z ^ (2 * c)) := by
    rw [← hσ, ← hdecomp]; exact h
  have t3 : ∀ {p : ℕ}, p.Prime → Odd p → 3 ≤ p := fun hp hpo => by
    have := Nat.odd_iff.1 hpo; have := hp.two_le; omega
  rcases (by omega : (x < y ∧ y < z) ∨ (x < z ∧ z < y) ∨ (y < x ∧ x < z) ∨ (y < z ∧ z < x) ∨
      (z < x ∧ x < y) ∨ (z < y ∧ y < x)) with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
      ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact core x y z a b c hxp hyp hzp (t3 hxp hxo) h1 h2 hxo hyo hzo hxa hya hza hE
  · exact core x z y a c b hxp hzp hyp (t3 hxp hxo) h1 h2 hxo hzo hyo hxa hza hya (by linarith [hE])
  · exact core y x z b a c hyp hxp hzp (t3 hyp hyo) h1 h2 hyo hxo hzo hya hxa hza (by linarith [hE])
  · exact core y z x b c a hyp hzp hxp (t3 hyp hyo) h1 h2 hyo hzo hxo hya hza hxa (by linarith [hE])
  · exact core z x y c a b hzp hxp hyp (t3 hzp hzo) h1 h2 hzo hxo hyo hza hxa hya (by linarith [hE])
  · exact core z y x c b a hzp hyp hxp (t3 hzp hzo) h1 h2 hzo hyo hxo hza hya hxa (by linarith [hE])

theorem main : H1 → H2 → OMA.R_OeisA215926_conjecture_1_R1.H1 := by
  intro h1 h2 k hk h
  by_contra hk1
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hσodd : Odd (σ 1 k) := ⟨k - 1, by omega⟩
  have hsq := isSquare_of_odd_sigma hk hσodd
  rcases (by omega : k.primeFactors.card ≤ 2 ∨ k.primeFactors.card = 3 ∨
      k.primeFactors.card = 4 ∨ 5 ≤ k.primeFactors.card) with hc | hc | hc | hc
  · exact not_card_le_two hk hk1 hc h
  · exact not_card_three k hk hsq hc h
  · exact h1 k hk hsq hc h
  · exact h2 k hk hsq hc h

end Proof

end OMA.R_OeisA215926_conjecture_1_R1_H1_R1
