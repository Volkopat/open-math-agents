import OMAReductions.R_OeisA215926_conjecture_1_R1
import Mathlib

-- Reduction OeisA215926.conjecture_1.R1.H2.R1 of step OeisA215926.conjecture_1.R1.H2
-- Credit: @chinwas

/-!
# Even almost perfect numbers

The parent step asks that every even `k` with `σ(k) = 2k - 1` be a power of two. Write
`k = 2^a m` with `m` odd and `a ≥ 1`, and put `A = 2^(a+1)`. Then `σ(k) = (A - 1) σ(m)` and the
equation reads `1 + (A - 1) σ(m) = A m`. This reduction proves, unconditionally:

1. `σ(m)` is odd, so `m` is a perfect square (`isSquare_of_odd_sigma`).
2. Every prime factor `p` of `m` satisfies `A < p` (`prime_gt`): the divisors `1, m/p, m` give
   `(A - 1)(1 + m/p) + 1 ≤ m`.
3. `m` is not a prime power (`not_card_one`): with `(p - 1) σ(p^e) = p^(e+1) - 1` the equation
   becomes `(p - A)(m - 1) = 0`.
4. If `m = p^(2e) q^(2f)` with primes `p < q`, then `e = f = 1` (`exp_x`, `exp_y`). With
   `B = A - 1`, `X = p^(2e)`, `Y = q^(2f)` and `C = B(p + q - 1) - (p - 1)(q - 1)` one has
   `X Y C = B(pX + qY - 1) - (p - 1)(q - 1)` (`two_identity`). The right side is positive, so
   `C ≥ 1`, which gives `q ≤ B p`; size estimates then force `X = p²` and `Y = q²`.

So an even almost perfect number that is not a power of two is `2^a m²` with `m` odd, every
prime factor of `m` above `2^(a+1)`, and at least two prime factors. What remains:
- `H1`: two prime factors, i.e. the Diophantine equation
  `1 + (A - 1)(p² + p + 1)(q² + q + 1) = A p² q²` for `A = 2^(a+1)` and primes `A < p < q`.
  (A computer search finds no integer solutions at all, prime or not, with `A + 1 < p < q` for
  any `A - 1 < 3000`.)
- `H2`: at least three prime factors.
-/

namespace OMA.R_OeisA215926_conjecture_1_R1_H2_R1

open ArithmeticFunction Finset
open scoped ArithmeticFunction.sigma

/-- Two prime factors: the remaining Diophantine equation for `m = p² q²`. -/
def H1 : Prop :=
  ∀ a p q : ℕ, 1 ≤ a → p.Prime → q.Prime → 2 ^ (a + 1) < p → p < q →
    1 + (2 ^ (a + 1) - 1) * ((p ^ 2 + p + 1) * (q ^ 2 + q + 1)) = 2 ^ (a + 1) * (p ^ 2 * q ^ 2) →
    False

/-- At least three prime factors. -/
def H2 : Prop :=
  ∀ a m : ℕ, 1 ≤ a → Odd m → IsSquare m → 3 ≤ m.primeFactors.card →
    (∀ p ∈ m.primeFactors, 2 ^ (a + 1) < p) →
    1 + (2 ^ (a + 1) - 1) * σ 1 m = 2 ^ (a + 1) * m → False

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
  conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hk0]
  rw [Finsupp.prod, Nat.support_factorization]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← pow_add]
  congr 1
  obtain ⟨r, hr⟩ := hev p hp
  omega

/-- `σ(2^a m) = (2^(a+1) - 1) σ(m)` for odd `m`. -/
theorem sigma_two_pow_mul (a m : ℕ) (hm : Odd m) :
    σ 1 (2 ^ a * m) = (2 ^ (a + 1) - 1) * σ 1 m := by
  have hcop : Nat.Coprime (2 ^ a) m := hm.coprime_two_left.pow_left a
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop, sigma_one_apply_prime_pow Nat.prime_two,
    Nat.geomSum_eq (m := 2) (by decide)]
  simp

/-- Every prime factor of `m` exceeds `A = 2^(a+1)`. -/
theorem prime_gt (A m p : ℕ) (hA : 2 ≤ A) (hAe : Even A) (hsq : IsSquare m) (hmo : Odd m)
    (hp : p ∈ m.primeFactors) (h : 1 + (A - 1) * σ 1 m = A * m) : A < p := by
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpd := Nat.dvd_of_mem_primeFactors hp
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmo
  have hpo : Odd p := hmo.of_dvd_nat hpd
  obtain ⟨r, rfl⟩ := hsq
  have hpr : p ∣ r := (Nat.Prime.dvd_mul hpp).1 hpd |>.elim id id
  obtain ⟨u, rfl⟩ := hpr
  have hu0 : u ≠ 0 := by rintro rfl; simp at hm0
  set s := u * (p * u) with hs
  have hm : p * u * (p * u) = p * s := by rw [hs]; ring
  have hp2 := hpp.two_le
  have hs1 : p ≤ s := by
    calc p = p * 1 := by ring
      _ ≤ p * (u * u) := Nat.mul_le_mul_left p (Nat.one_le_iff_ne_zero.2 (mul_ne_zero hu0 hu0))
      _ = s := by rw [hs]; ring
  have hsub : ({1, s, p * s} : Finset ℕ) ⊆ (p * u * (p * u)).divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rw [hm]
    have hps0 : p * s ≠ 0 := by rw [← hm]; exact hm0
    rcases hd with rfl | rfl | rfl
    · exact Nat.one_mem_divisors.2 hps0
    · exact Nat.mem_divisors.2 ⟨Dvd.intro_left p rfl, hps0⟩
    · exact Nat.mem_divisors_self _ hps0
  have hsum : ∑ d ∈ ({1, s, p * s} : Finset ℕ), d = 1 + s + p * s := by
    rw [Finset.sum_insert (by simp; constructor <;> nlinarith),
      Finset.sum_pair (by nlinarith)]
    ring
  have hσ : 1 + s + p * s ≤ σ 1 (p * u * (p * u)) := by
    rw [sigma_one_apply, ← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  rw [hm] at h hσ
  obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  have hle : B + 1 ≤ p := by
    by_contra hc
    push Not at hc
    have h1 : B * (1 + s + p * s) ≤ B * σ 1 (p * s) := Nat.mul_le_mul_left B hσ
    have h2 : p * s ≤ B * s := Nat.mul_le_mul_right s (by omega)
    nlinarith
  rcases hAe with ⟨c, hc⟩
  rcases hpo with ⟨d, hd⟩
  omega

/-- `m` is not a prime power. -/
theorem not_card_one (A m : ℕ) (hA : 2 ≤ A) (hmo : Odd m) (hc : m.primeFactors.card = 1)
    (hgt : ∀ p ∈ m.primeFactors, A < p) (h : 1 + (A - 1) * σ 1 m = A * m) : False := by
  obtain ⟨p, hp⟩ := Finset.card_eq_one.1 hc
  have hmem : p ∈ m.primeFactors := by rw [hp]; exact Finset.mem_singleton_self p
  have hpp := Nat.prime_of_mem_primeFactors hmem
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmo
  have hdec : m = p ^ m.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hm0]
    rw [Finsupp.prod, Nat.support_factorization, hp, Finset.prod_singleton]
  have hS := sigma_prime_pow_mul p (m.factorization p) hpp
  have hmc : (m : ℤ) = (p : ℤ) ^ m.factorization p := by
    conv_lhs => rw [hdec]
    push_cast
    ring
  rw [← hdec] at hS
  rw [pow_succ, ← hmc] at hS
  have hZ : 1 + ((A : ℤ) - 1) * (σ 1 m : ℤ) = (A : ℤ) * m := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast [Nat.cast_sub (by omega : 1 ≤ A)] at this
    exact this
  have key : ((p : ℤ) - A) * ((m : ℤ) - 1) = 0 := by
    linear_combination (1 - (p : ℤ)) * hZ + ((A : ℤ) - 1) * hS
  have hAp : (A : ℤ) < p := by exact_mod_cast hgt p hmem
  rcases mul_eq_zero.1 key with h1 | h1
  · linarith
  · have hm1 : m = 1 := by omega
    rw [hm1] at hmem
    simp at hmem

/-- The identity behind the two-prime case. -/
theorem two_identity (B p q X Y SX SY : ℤ) (eX : (p - 1) * SX + 1 = p * X)
    (eY : (q - 1) * SY + 1 = q * Y) (h : 1 + B * (SX * SY) = (B + 1) * (X * Y)) :
    X * Y * (B * (p + q - 1) - (p - 1) * (q - 1)) =
      B * (p * X + q * Y - 1) - (p - 1) * (q - 1) := by
  linear_combination (p - 1) * (q - 1) * h - B * (q - 1) * SY * eX - B * (p * X - 1) * eY

/-- Consequences of the identity: `C ≥ 1`, `q ≤ B p` and `X Y < B (p X + q Y)`. -/
theorem two_bounds (B p q X Y : ℤ) (hB : 1 ≤ B) (hp : B + 2 ≤ p) (hpq : p + 2 ≤ q)
    (hX : p ^ 2 ≤ X) (hY : q ^ 2 ≤ Y)
    (key : X * Y * (B * (p + q - 1) - (p - 1) * (q - 1)) =
      B * (p * X + q * Y - 1) - (p - 1) * (q - 1)) :
    1 ≤ B * (p + q - 1) - (p - 1) * (q - 1) ∧ q ≤ B * p ∧ X * Y < B * (p * X + q * Y) := by
  have hX0 : 0 < X := by nlinarith
  have hY0 : 0 < Y := by nlinarith
  have hXY : 0 < X * Y := mul_pos hX0 hY0
  have a1 : q * q ^ 2 ≤ q * Y := mul_le_mul_of_nonneg_left hY (by linarith)
  have a2 : 0 ≤ (B - 1) * (p * X + q * Y - 1) := mul_nonneg (by linarith) (by nlinarith)
  have a3 : (p - 1) * (q - 1) < q * q ^ 2 := by nlinarith
  have hR : 0 < B * (p * X + q * Y - 1) - (p - 1) * (q - 1) := by nlinarith
  have hC : 1 ≤ B * (p + q - 1) - (p - 1) * (q - 1) := by
    by_contra hc
    push Not at hc
    have : X * Y * (B * (p + q - 1) - (p - 1) * (q - 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hXY.le (by linarith)
    linarith
  refine ⟨hC, ?_, ?_⟩
  · nlinarith [mul_nonneg (show (0 : ℤ) ≤ p - 2 - B by linarith) (show (0 : ℤ) ≤ q - 1 by linarith)]
  · have := mul_le_mul_of_nonneg_left hC hXY.le
    nlinarith

/-- In the two-prime case the smaller prime appears squared. -/
theorem exp_x (B p q X Y SX SY : ℤ) (hB : 1 ≤ B) (hp : B + 2 ≤ p) (hpq : p + 2 ≤ q)
    (eX : (p - 1) * SX + 1 = p * X) (eY : (q - 1) * SY + 1 = q * Y)
    (hX : p ^ 2 ≤ X) (hY : q ^ 2 ≤ Y) (h : 1 + B * (SX * SY) = (B + 1) * (X * Y)) :
    X < p ^ 4 := by
  obtain ⟨-, hqB, hlt⟩ := two_bounds B p q X Y hB hp hpq hX hY
    (two_identity B p q X Y SX SY eX eY h)
  have hp3 : 3 ≤ p := by linarith
  have hX0 : 0 < X := by nlinarith
  have hY0 : 0 < Y := by nlinarith
  by_contra hX4
  push Not at hX4
  have b1 : B * q ≤ B * (B * p) := mul_le_mul_of_nonneg_left hqB (by linarith)
  have b2 : B * (B * p) ≤ (p - 2) * ((p - 2) * p) :=
    mul_le_mul (by linarith) (mul_le_mul_of_nonneg_right (by linarith) (by linarith))
      (by nlinarith) (by linarith)
  have b3 : (p - 2) * ((p - 2) * p) ≤ p ^ 3 - p ^ 2 := by nlinarith
  have s1 : Y * (X - B * q) < B * p * X := by nlinarith
  have s2 : Y * (X - (p ^ 3 - p ^ 2)) ≤ Y * (X - B * q) :=
    mul_le_mul_of_nonneg_left (by linarith) hY0.le
  have s3 : (p - 1) * X < p * (X - (p ^ 3 - p ^ 2)) := by nlinarith
  have s4 : Y * ((p - 1) * X) < Y * (p * (X - (p ^ 3 - p ^ 2))) := mul_lt_mul_of_pos_left s3 hY0
  have s5 : p * (Y * (X - B * q)) < p * (B * p * X) := mul_lt_mul_of_pos_left s1 (by linarith)
  have s6 : B * p * X ≤ (p - 2) * p * X := by
    have := mul_le_mul_of_nonneg_right (show B ≤ p - 2 by linarith) (show 0 ≤ p * X by positivity)
    nlinarith
  have s2' : p * (Y * (X - (p ^ 3 - p ^ 2))) ≤ p * (Y * (X - B * q)) :=
    mul_le_mul_of_nonneg_left s2 (by linarith)
  have s7 : (p - 1) * Y * X < p * ((p - 2) * p) * X := by nlinarith
  have s8 : (p - 1) * Y < p * ((p - 2) * p) := by
    by_contra hh
    push Not at hh
    nlinarith [mul_le_mul_of_nonneg_right hh hX0.le]
  have s9 : (p + 2) ^ 2 ≤ Y := le_trans (by nlinarith) hY
  nlinarith

/-- With `X = p²`, the larger prime appears squared too. -/
theorem exp_y (B p q X Y SX SY : ℤ) (hB : 1 ≤ B) (hp : B + 2 ≤ p) (hpq : p + 2 ≤ q)
    (hX2 : X = p ^ 2) (eX : (p - 1) * SX + 1 = p * X) (eY : (q - 1) * SY + 1 = q * Y)
    (hY : q ^ 2 ≤ Y) (h : 1 + B * (SX * SY) = (B + 1) * (X * Y)) : Y < q ^ 4 := by
  have key := two_identity B p q X Y SX SY eX eY h
  obtain ⟨-, hqB, -⟩ := two_bounds B p q X Y hB hp hpq (le_of_eq hX2.symm) hY key
  subst hX2
  have hp3 : 3 ≤ p := by linarith
  have hY0 : 0 < Y := by nlinarith
  set C := B * (p + q - 1) - (p - 1) * (q - 1) with hC
  have key2 : Y * (p ^ 2 * C - B * q) = B * (p ^ 3 - 1) - (p - 1) * (q - 1) := by
    linear_combination key
  have c1 : (p - 1) * (q - 1) ≤ (p - 1) * (B * p - 1) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have c2 : 0 ≤ B * (p ^ 3 - p ^ 2 + p - 1) := mul_nonneg (by linarith) (by nlinarith)
  have hR : 0 < B * (p ^ 3 - 1) - (p - 1) * (q - 1) := by nlinarith
  have hD : 1 ≤ p ^ 2 * C - B * q := by
    by_contra hc
    push Not at hc
    have : Y * (p ^ 2 * C - B * q) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hY0.le (by linarith)
    linarith
  have hYle : Y ≤ B * (p ^ 3 - 1) - (p - 1) * (q - 1) := by
    have := mul_le_mul_of_nonneg_left hD hY0.le
    linarith
  have d1 : B * (p ^ 3 - 1) - (p - 1) * (q - 1) < p ^ 4 := by
    have : B * p ^ 3 ≤ (p - 2) * p ^ 3 :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ p - 1 by linarith) (show (0 : ℤ) ≤ q - 1 by linarith)]
  have d2 : p ^ 4 < q ^ 4 := by
    have h0 : (0 : ℤ) ≤ p := by linarith
    exact pow_lt_pow_left₀ (by linarith) h0 (by norm_num)
  linarith

/-- `σ(p²) = p² + p + 1`. -/
theorem sigma_sq {p : ℕ} (hp : p.Prime) : σ 1 (p ^ 2) = p ^ 2 + p + 1 := by
  rw [sigma_one_apply_prime_pow hp]
  simp [Finset.sum_range_succ]
  ring

/-- Two sorted primes: the exponents are both `2`, which is `H1`. -/
theorem two_sorted (h1 : H1) (a p q e f : ℕ) (ha : 1 ≤ a) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hAp : 2 ^ (a + 1) < p) (he : 1 ≤ e) (hf : 1 ≤ f)
    (h : 1 + (2 ^ (a + 1) - 1) * (σ 1 (p ^ (2 * e)) * σ 1 (q ^ (2 * f))) =
      2 ^ (a + 1) * (p ^ (2 * e) * q ^ (2 * f))) : False := by
  have hA4 : 4 ≤ 2 ^ (a + 1) := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpo : p % 2 = 1 := Nat.odd_iff.1 (hp.odd_of_ne_two (by omega))
  have hqo : q % 2 = 1 := Nat.odd_iff.1 (hq.odd_of_ne_two (by omega))
  have hp1 : 1 < p := hp.one_lt
  have hq1 : 1 < q := hq.one_lt
  -- integer form
  set B : ℤ := ((2 ^ (a + 1) : ℕ) : ℤ) - 1 with hBdef
  have hZ : ∀ e f : ℕ, 1 + (2 ^ (a + 1) - 1) * (σ 1 (p ^ (2 * e)) * σ 1 (q ^ (2 * f))) =
      2 ^ (a + 1) * (p ^ (2 * e) * q ^ (2 * f)) →
      1 + B * ((σ 1 (p ^ (2 * e)) : ℤ) * (σ 1 (q ^ (2 * f)) : ℤ)) =
        (B + 1) * ((p : ℤ) ^ (2 * e) * (q : ℤ) ^ (2 * f)) := by
    intro e f h'
    have := congrArg (fun n : ℕ => (n : ℤ)) h'
    push_cast [Nat.cast_sub (by omega : 1 ≤ 2 ^ (a + 1))] at this
    rw [hBdef]
    push_cast
    linear_combination this
  have hB : (1 : ℤ) ≤ B := by
    rw [hBdef]
    have : (4 : ℤ) ≤ ((2 ^ (a + 1) : ℕ) : ℤ) := by exact_mod_cast hA4
    linarith
  have hBp : B + 2 ≤ (p : ℤ) := by
    rw [hBdef]
    have : ((2 ^ (a + 1) : ℕ) : ℤ) + 1 ≤ (p : ℤ) := by exact_mod_cast hAp
    linarith
  have hpq2 : (p : ℤ) + 2 ≤ q := by
    have : p + 2 ≤ q := by omega
    exact_mod_cast this
  have eX : ∀ e : ℕ, ((p : ℤ) - 1) * (σ 1 (p ^ (2 * e)) : ℤ) + 1 = p * (p : ℤ) ^ (2 * e) := by
    intro e
    have := sigma_prime_pow_mul p (2 * e) hp
    rw [pow_succ] at this
    linarith
  have eY : ∀ f : ℕ, ((q : ℤ) - 1) * (σ 1 (q ^ (2 * f)) : ℤ) + 1 = q * (q : ℤ) ^ (2 * f) := by
    intro f
    have := sigma_prime_pow_mul q (2 * f) hq
    rw [pow_succ] at this
    linarith
  have hXp : ∀ e : ℕ, 1 ≤ e → (p : ℤ) ^ 2 ≤ (p : ℤ) ^ (2 * e) := fun e he => by
    exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)
  have hYq : ∀ f : ℕ, 1 ≤ f → (q : ℤ) ^ 2 ≤ (q : ℤ) ^ (2 * f) := fun f hf => by
    exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)
  -- `e = 1`
  have hx := exp_x B p q _ _ _ _ hB hBp hpq2 (eX e) (eY f) (hXp e he) (hYq f hf) (hZ e f h)
  have he1 : e = 1 := by
    have : p ^ (2 * e) < p ^ 4 := by exact_mod_cast hx
    have := (Nat.pow_lt_pow_iff_right (by omega : 1 < p)).1 this
    omega
  subst he1
  -- `f = 1`
  have hy := exp_y B p q _ _ _ _ hB hBp hpq2 (by norm_num) (eX 1) (eY f) (hYq f hf) (hZ 1 f h)
  have hf1 : f = 1 := by
    have : q ^ (2 * f) < q ^ 4 := by exact_mod_cast hy
    have := (Nat.pow_lt_pow_iff_right (by omega : 1 < q)).1 this
    omega
  subst hf1
  simp only [mul_one] at h
  rw [sigma_sq hp, sigma_sq hq] at h
  exact h1 a p q ha hp hq hAp hpq h

/-- Two prime factors. -/
theorem card_two (h1 : H1) (a m : ℕ) (ha : 1 ≤ a) (hmo : Odd m) (hsq : IsSquare m)
    (hc : m.primeFactors.card = 2) (hgt : ∀ p ∈ m.primeFactors, 2 ^ (a + 1) < p)
    (h : 1 + (2 ^ (a + 1) - 1) * σ 1 m = 2 ^ (a + 1) * m) : False := by
  obtain ⟨r, rfl⟩ := hsq
  have hr0 : r ≠ 0 := by rintro rfl; simp at hmo
  have hrr0 : r * r ≠ 0 := mul_ne_zero hr0 hr0
  have hpf : (r * r).primeFactors = r.primeFactors := by
    rw [Nat.primeFactors_mul hr0 hr0, Finset.union_self]
  obtain ⟨x, y, hxy, hs⟩ := Finset.card_eq_two.1 hc
  have hfac : ∀ p, (r * r).factorization p = 2 * r.factorization p := by
    intro p; rw [Nat.factorization_mul hr0 hr0]; simp [two_mul]
  have hdecomp : r * r = x ^ (2 * r.factorization x) * y ^ (2 * r.factorization y) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hrr0]
    rw [Finsupp.prod, Nat.support_factorization, hs, Finset.prod_pair hxy, hfac x, hfac y]
  have mem : ∀ p ∈ ({x, y} : Finset ℕ), p.Prime ∧ 1 ≤ r.factorization p := by
    intro p hp
    rw [← hs] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    refine ⟨hpp, ?_⟩
    rw [hpf] at hp
    exact hpp.factorization_pos_of_dvd hr0 (Nat.dvd_of_mem_primeFactors hp)
  obtain ⟨hxp, hxa⟩ := mem x (by simp)
  obtain ⟨hyp, hya⟩ := mem y (by simp)
  have hσ : σ 1 (r * r) =
      σ 1 (x ^ (2 * r.factorization x)) * σ 1 (y ^ (2 * r.factorization y)) := by
    rw [hdecomp, isMultiplicative_sigma.map_mul_of_coprime
      (Nat.Coprime.pow _ _ ((Nat.coprime_primes hxp hyp).2 hxy))]
  have hgx := hgt x (by rw [hs]; simp)
  have hgy := hgt y (by rw [hs]; simp)
  rw [hσ] at h
  conv_rhs at h => rw [hdecomp]
  rcases lt_or_gt_of_ne hxy with hlt | hlt
  · exact two_sorted h1 a x y _ _ ha hxp hyp hlt hgx hxa hya h
  · refine two_sorted h1 a y x _ _ ha hyp hxp hlt hgy hya hxa ?_
    rw [mul_comm (σ 1 (y ^ (2 * r.factorization y))), mul_comm (y ^ (2 * r.factorization y))]
    exact h

theorem main : H1 → H2 → OMA.R_OeisA215926_conjecture_1_R1.H2 := by
  intro h1 h2 k hk h
  have hk0 : k ≠ 0 := by rintro rfl; simp at h
  obtain ⟨a, m, hmo, rfl⟩ := Nat.exists_eq_two_pow_mul_odd hk0
  have ha : 1 ≤ a := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp only [pow_zero, one_mul] at hk
      exact absurd hk (Nat.not_even_iff_odd.2 hmo)
    · exact ha
  rw [sigma_two_pow_mul a m hmo] at h
  have h' : 1 + (2 ^ (a + 1) - 1) * σ 1 m = 2 ^ (a + 1) * m := by
    rw [h, pow_succ]
    ring
  have hA2 : 2 ≤ 2 ^ (a + 1) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hAe : Even (2 ^ (a + 1)) := (Nat.even_pow.2 ⟨even_two, by omega⟩)
  have hσo : Odd (σ 1 m) := by
    have he : Even (2 ^ (a + 1) * m) := hAe.mul_right m
    rw [← h'] at he
    have hodd : Odd ((2 ^ (a + 1) - 1) * σ 1 m) := by
      rcases he with ⟨r, hr⟩
      exact ⟨r - 1, by omega⟩
    exact (Nat.odd_mul.1 hodd).2
  have hsq := isSquare_of_odd_sigma hmo hσo
  have hgt : ∀ p ∈ m.primeFactors, 2 ^ (a + 1) < p := fun p hp =>
    prime_gt _ m p hA2 hAe hsq hmo hp h'
  have hm0 : m ≠ 0 := by rintro rfl; simp at hmo
  rcases (by omega : m.primeFactors.card = 0 ∨ m.primeFactors.card = 1 ∨
      m.primeFactors.card = 2 ∨ 3 ≤ m.primeFactors.card) with hc | hc | hc | hc
  · have hm1 : m = 1 := by
      rcases Nat.primeFactors_eq_empty.1 (Finset.card_eq_zero.1 hc) with h0 | h0
      · exact absurd h0 hm0
      · exact h0
    subst hm1
    exact ⟨a, by ring⟩
  · exact (not_card_one _ m hA2 hmo hc hgt h').elim
  · exact (card_two h1 a m ha hmo hsq hc hgt h').elim
  · exact (h2 a m ha hmo hsq hc hgt h').elim

end Proof

end OMA.R_OeisA215926_conjecture_1_R1_H2_R1
