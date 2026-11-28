import OMAReductions.R_RiemannZetaMoments_moment_isEquiv_83_R1
import Mathlib

/-!
# Proof of `RiemannZetaMoments.moment_isEquiv-83.R1.H3`

We prove the Ramanujan-Wilson-Ingham divisor-squared harmonic asymptotic:
`∑_{1 ≤ n ≤ ⌊X⌋₊} d(n)² / n ~ (1 / (4 * π²)) * (log X)⁴` as `X → ∞`.

Proof outline:
1. Multiplicative convolution identity `d(n)² = ∑_{k² * m = n} μ(k) * d₄(m)`, verified on
   prime powers via `Nat.recOnPosPrimePosCoprime` where `d₄ = (σ₀) * (σ₀) = ζ * ζ * ζ * ζ`.
2. Exact Dirichlet-hyperbola recursion for harmonic partial sums `H_f(Y) = ∑_{1 ≤ n ≤ ⌊Y⌋₊} f(n)/n`:
   `H_{ζ * f}(Y) = ∑_{1 ≤ a ≤ ⌊Y⌋₊} (1 / a) * H_f(Y / a)`, together with integral comparison on
   the decreasing function `t ↦ (log Y - log t)^r / t` over `[1, Y]`, yielding by induction for
   all `Y ≥ 1` and `r = 1, 2, 3, 4`:
   `|H_4(Y) - (log Y)⁴ / 24| ≤ 4 * (log Y + 1)³`.
3. Möbius reciprocal-square limit `∑_{1 ≤ k ≤ K} μ(k) / k² → 6 / π²` derived from Mathlib's
   `hasSum_zeta_two` and `moebius_mul_coe_zeta`.
4. Combining (1)-(3) with the convergent majorant `∑ (log k) / k² ≤ ∑ 2 / k^(3/2) < ∞` yields
   the exact asymptotic `(1 / (4 * π²)) * (log X)⁴`.
-/

namespace ZetaMomentsH3Proof

open Filter Finset Real ArithmeticFunction MeasureTheory
open scoped BigOperators Topology ArithmeticFunction.Moebius ArithmeticFunction.zeta

/- ### Section 1: Ramanujan's Convolution Identity `d(n)^2 = (muSq * d4)(n)` -/

private def d2 : ArithmeticFunction ℕ := ArithmeticFunction.sigma 0
private def d3 : ArithmeticFunction ℕ := ArithmeticFunction.zeta * d2
private def d4 : ArithmeticFunction ℕ := ArithmeticFunction.zeta * d3

private lemma d2_eq_zeta_mul_zeta : d2 = ArithmeticFunction.zeta * ArithmeticFunction.zeta := by
  ext n
  by_cases hn : n = 0
  · simp [d2, hn]
  · rw [d2, ArithmeticFunction.sigma_apply, ArithmeticFunction.zeta_mul_apply]
    refine Finset.sum_congr rfl fun d hd => ?_
    have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
    simp [ArithmeticFunction.zeta_apply, hd0]

private lemma d4_eq_d2_mul_d2 : d4 = d2 * d2 := by
  rw [d4, d3, ← mul_assoc, ← d2_eq_zeta_mul_zeta]

private lemma d2_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) : d2 (p ^ a) = a + 1 := by
  simp [d2, ArithmeticFunction.sigma_apply, Nat.divisors_prime_pow hp]

private lemma d4_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) :
    6 * d4 (p ^ a) = (a + 1) * (a + 2) * (a + 3) := by
  rw [d4_eq_d2_mul_d2, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (n := p ^ a) (f := fun x y => d2 x * d2 y)]
  rw [Nat.sum_divisors_prime_pow hp]
  have hterm : ∀ j ∈ Finset.range (a + 1),
      d2 (p ^ j) * d2 (p ^ a / p ^ j) = (j + 1) * (a - j + 1) := by
    intro j hj
    have hja : j ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.pow_div hja hp.pos, d2_prime_pow hp j, d2_prime_pow hp (a - j)]
  rw [Finset.sum_congr rfl hterm]
  clear hp hterm p
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ]
    have hsplit : ∑ x ∈ Finset.range (a + 1), (x + 1) * (a + 1 - x + 1) =
        (∑ x ∈ Finset.range (a + 1), (x + 1) * (a - x + 1)) +
          ∑ x ∈ Finset.range (a + 1), (x + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x hx => ?_
      have hxa : x ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hx)
      have hsub : a + 1 - x = a - x + 1 := by omega
      rw [hsub]; ring
    have hlin_all : ∀ m : ℕ, 2 * ∑ x ∈ Finset.range (m + 1), (x + 1) = (m + 1) * (m + 2) := by
      intro m
      induction m with
      | zero => simp
      | succ k ihk =>
        rw [Finset.sum_range_succ, mul_add, ihk]; ring
    have hlin := hlin_all a
    rw [hsplit]
    have hlast : a + 1 - (a + 1) + 1 = 1 := by omega
    rw [hlast]
    nlinarith

private def d2SqInt : ArithmeticFunction ℤ where
  toFun n := ((d2 n : ℕ) : ℤ) ^ 2
  map_zero' := by simp [d2]

private def d4Int : ArithmeticFunction ℤ where
  toFun n := (d4 n : ℤ)
  map_zero' := by simp [d4]

private def muSq : ArithmeticFunction ℤ where
  toFun n := if (Nat.sqrt n) ^ 2 = n then (μ (Nat.sqrt n) : ℤ) else 0
  map_zero' := by simp

private lemma d2SqInt_isMultiplicative : d2SqInt.IsMultiplicative := by
  constructor
  · simp [d2SqInt, d2]
  · intro m n hmn
    simp only [d2SqInt, coe_mk]
    have hm := ArithmeticFunction.isMultiplicative_sigma (k := 0) |>.map_mul_of_coprime hmn
    change (((d2 (m * n) : ℕ) : ℤ)) ^ 2 = _
    rw [show d2 (m * n) = d2 m * d2 n from hm]
    push_cast; ring

private lemma d4Int_isMultiplicative : d4Int.IsMultiplicative := by
  have hd4m : d4.IsMultiplicative := by
    rw [d4_eq_d2_mul_d2]
    exact (ArithmeticFunction.isMultiplicative_sigma (k := 0)).mul
      (ArithmeticFunction.isMultiplicative_sigma (k := 0))
  constructor
  · simp [d4Int, hd4m.map_one]
  · intro m n hmn
    simp only [d4Int, coe_mk]
    rw [hd4m.map_mul_of_coprime hmn, Nat.cast_mul]

private lemma coprime_sq_mul_iff {a b : ℕ} (hab : Nat.Coprime a b) :
    (Nat.sqrt (a * b)) ^ 2 = a * b ↔ (Nat.sqrt a) ^ 2 = a ∧ (Nat.sqrt b) ^ 2 = b := by
  constructor
  · intro hsq
    set k := Nat.sqrt (a * b)
    set g₁ := Nat.gcd a k
    set g₂ := Nat.gcd b k
    have hg1_dvd : g₁ ∣ a := Nat.gcd_dvd_left a k
    have hg2_dvd : g₂ ∣ b := Nat.gcd_dvd_left b k
    have hcop_g : Nat.Coprime g₁ g₂ := hab.coprime_dvd_left hg1_dvd |>.coprime_dvd_right hg2_dvd
    have hmul_g : g₁ * g₂ = k := by
      have h1 : k.gcd (a * b) = k.gcd a * k.gcd b := hab.gcd_mul k
      rw [Nat.gcd_comm k (a * b), Nat.gcd_comm k a, Nat.gcd_comm k b] at h1
      have h2 : Nat.gcd (k * k) k = k := by simp
      rw [← hsq, sq] at h1
      rw [h2] at h1
      exact h1.symm
    have hg1_sq : g₁ ^ 2 ∣ a := by
      have hdvd : g₁ ^ 2 ∣ a * b := by
        rw [← hsq, ← hmul_g, mul_pow]; exact dvd_mul_right _ _
      exact (hab.coprime_dvd_left hg1_dvd |>.pow_left 2).dvd_of_dvd_mul_right hdvd
    have hg2_sq : g₂ ^ 2 ∣ b := by
      have hdvd : g₂ ^ 2 ∣ a * b := by
        rw [← hsq, ← hmul_g, mul_pow]; exact dvd_mul_left _ _
      exact (hab.symm.coprime_dvd_left hg2_dvd |>.pow_left 2).dvd_of_dvd_mul_left hdvd
    obtain ⟨u, hu⟩ := hg1_sq
    obtain ⟨v, hv⟩ := hg2_sq
    have huv : g₁ ^ 2 * g₂ ^ 2 * (u * v) = g₁ ^ 2 * g₂ ^ 2 * 1 := by
      calc g₁ ^ 2 * g₂ ^ 2 * (u * v) = (g₁ ^ 2 * u) * (g₂ ^ 2 * v) := by ring
        _ = a * b := by rw [← hu, ← hv]
        _ = k ^ 2 := hsq.symm
        _ = (g₁ * g₂) ^ 2 := by rw [hmul_g]
        _ = g₁ ^ 2 * g₂ ^ 2 * 1 := by ring
    by_cases h0 : a * b = 0
    · rcases mul_eq_zero.mp h0 with rfl | rfl
      · have hb1 : b = 1 := by simpa [Nat.Coprime] using hab
        subst hb1; simp
      · have ha1 : a = 1 := by simpa [Nat.Coprime] using hab
        subst ha1; simp
    · have hk0 : g₁ ^ 2 * g₂ ^ 2 ≠ 0 := by
        intro hz
        apply h0
        rw [← hsq, ← hmul_g, mul_pow, hz]
      have huv1 : u * v = 1 := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk0) huv
      have hu1 : u = 1 := (mul_eq_one.mp huv1).1
      have hv1 : v = 1 := (mul_eq_one.mp huv1).2
      rw [hu1, mul_one] at hu
      rw [hv1, mul_one] at hv
      rw [hu, hv, Nat.sqrt_eq', Nat.sqrt_eq']
      exact ⟨rfl, rfl⟩
  · rintro ⟨ha, hb⟩
    have hmul : (Nat.sqrt a * Nat.sqrt b) ^ 2 = a * b := by
      rw [mul_pow, ha, hb]
    rw [← hmul, Nat.sqrt_eq']

private lemma muSq_isMultiplicative : muSq.IsMultiplicative := by
  constructor
  · simp [muSq]
  · intro m n hmn
    simp only [muSq, coe_mk]
    by_cases hm : (Nat.sqrt m) ^ 2 = m
    · by_cases hn : (Nat.sqrt n) ^ 2 = n
      · have hprod : (Nat.sqrt (m * n)) ^ 2 = m * n := (coprime_sq_mul_iff hmn).mpr ⟨hm, hn⟩
        have hsqrt : Nat.sqrt (m * n) = Nat.sqrt m * Nat.sqrt n := by
          have : (Nat.sqrt m * Nat.sqrt n) ^ 2 = m * n := by rw [mul_pow, hm, hn]
          rw [← this, Nat.sqrt_eq']
        have hcop_s : Nat.Coprime (Nat.sqrt m) (Nat.sqrt n) := by
          have hd1 : Nat.sqrt m ∣ m := ⟨Nat.sqrt m, by rw [← sq]; exact hm.symm⟩
          have hd2 : Nat.sqrt n ∣ n := ⟨Nat.sqrt n, by rw [← sq]; exact hn.symm⟩
          exact (hmn.coprime_dvd_left hd1).coprime_dvd_right hd2
        rw [if_pos hprod, if_pos hm, if_pos hn, hsqrt,
          ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop_s]
      · have hprod : ¬ (Nat.sqrt (m * n)) ^ 2 = m * n := fun h =>
          hn ((coprime_sq_mul_iff hmn).mp h).2
        simp [hprod, hm, hn]
    · have hprod : ¬ (Nat.sqrt (m * n)) ^ 2 = m * n := fun h =>
        hm ((coprime_sq_mul_iff hmn).mp h).1
      simp [hprod, hm]

private lemma muSq_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    muSq (p ^ j) = if j = 0 then 1 else if j = 2 then -1 else 0 := by
  simp only [muSq, coe_mk]
  by_cases hj0 : j = 0
  · subst hj0; simp
  · by_cases hj2 : j = 2
    · subst hj2
      rw [Nat.sqrt_eq']
      simp [ArithmeticFunction.moebius_apply_prime hp]
    · simp only [hj0, hj2, ↓reduceIte]
      split_ifs with hsq
      · have hprime_dvd : p ∣ Nat.sqrt (p ^ j) := by
          have h1 : p ∣ (Nat.sqrt (p ^ j)) ^ 2 := by
            rw [hsq]; exact dvd_pow_self p hj0
          exact hp.dvd_of_dvd_pow h1
        by_cases hj1 : j = 1
        · subst hj1
          have hsq1 : (Nat.sqrt p) ^ 2 = p := by simpa using hsq
          have hdvd1 : p ∣ Nat.sqrt p := by simpa using hprime_dvd
          have hle1 : p ≤ Nat.sqrt p := Nat.le_of_dvd (Nat.pos_of_ne_zero (by
            intro h0; rw [h0] at hsq1; simp at hsq1; exact hp.ne_zero hsq1.symm)) hdvd1
          have hle : p ^ 2 ≤ p := by
            calc p ^ 2 ≤ (Nat.sqrt p) ^ 2 := Nat.pow_le_pow_left hle1 2
              _ = p := hsq1
          have := hp.two_le
          nlinarith
        · have hj3 : 3 ≤ j := by omega
          have heven : Even j := by
            have hfac : (Nat.sqrt (p ^ j)) ^ 2 = p ^ j := hsq
            have hv := congrArg (padicValNat p) hfac
            have : Fact p.Prime := ⟨hp⟩
            have hne : Nat.sqrt (p ^ j) ≠ 0 := by
              intro h0; rw [h0, zero_pow (by norm_num)] at hsq
              exact pow_ne_zero j hp.ne_zero hsq.symm
            rw [sq, padicValNat.mul hne hne, padicValNat.prime_pow] at hv
            exact ⟨padicValNat p (Nat.sqrt (p ^ j)), by omega⟩
          obtain ⟨m, rfl⟩ := heven
          have hm2 : 2 ≤ m := by omega
          have hsq_eq : Nat.sqrt (p ^ (m + m)) = p ^ m := by
            have : (p ^ m) ^ 2 = p ^ (m + m) := by rw [← pow_mul, mul_two]
            rw [← this, Nat.sqrt_eq']
          rw [hsq_eq, ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
          simp [show m ≠ 1 by omega]
      · rfl

private lemma d2SqInt_eq_muSq_mul_d4Int : d2SqInt = muSq * d4Int := by
  ext n
  induction n using Nat.recOnPosPrimePosCoprime with
  | zero => simp
  | one =>
    rw [ArithmeticFunction.mul_apply]
    simp [d2SqInt, muSq, d4Int, d2, d4, d3]
  | prime_pow p a hp ha =>
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (n := p ^ a) (f := fun x y => muSq x * d4Int y),
      Nat.sum_divisors_prime_pow hp]
    have hterm : ∀ j ∈ Finset.range (a + 1),
        muSq (p ^ j) * d4Int (p ^ a / p ^ j) =
          (if j = 0 then (1 : ℤ) else if j = 2 then -1 else 0) * (d4 (p ^ (a - j)) : ℤ) := by
      intro j hj
      have hja : j ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [muSq_prime_pow hp j, Nat.pow_div hja hp.pos]
      rfl
    rw [Finset.sum_congr rfl hterm]
    have hlhs : d2SqInt (p ^ a) = ((a + 1 : ℕ) : ℤ) ^ 2 := by
      simp [d2SqInt, d2_prime_pow hp a]
    rw [hlhs]
    by_cases ha1 : a = 1
    · subst ha1
      rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
      have hd1 : d4 p = 4 := by
        have := d4_prime_pow hp 1
        simp only [pow_one] at this
        omega
      simp only [zero_add, Nat.sub_zero, pow_one, ↓reduceIte, one_mul, Nat.one_ne_zero,
        OfNat.one_ne_ofNat, zero_mul, add_zero]
      rw [hd1]
      norm_num
    · have ha2 : 2 ≤ a := by omega
      have hsum : ∑ j ∈ Finset.range (a + 1),
          (if j = 0 then (1 : ℤ) else if j = 2 then -1 else 0) * (d4 (p ^ (a - j)) : ℤ) =
          (d4 (p ^ a) : ℤ) - (d4 (p ^ (a - 2)) : ℤ) := by
        have hsub : ({0, 2} : Finset ℕ) ⊆ Finset.range (a + 1) := by
          intro x hx
          simp only [Finset.mem_insert, Finset.mem_singleton] at hx
          rw [Finset.mem_range]
          omega
        rw [← Finset.sum_subset hsub]
        · rw [Finset.sum_pair (by decide : (0 : ℕ) ≠ 2)]
          simp [sub_eq_add_neg]
        · intro x _ hxnot
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hxnot
          simp [hxnot.1, hxnot.2]
      rw [hsum]
      have hda := d4_prime_pow hp a
      have hda2 := d4_prime_pow hp (a - 2)
      have hda_z : (6 : ℤ) * (d4 (p ^ a) : ℤ) = ((a : ℤ) + 1) * ((a : ℤ) + 2) * ((a : ℤ) + 3) := by
        exact_mod_cast hda
      have hda2_z : (6 : ℤ) * (d4 (p ^ (a - 2)) : ℤ) = ((a : ℤ) - 1) * (a : ℤ) * ((a : ℤ) + 1) := by
        have hcast : ((a - 2 : ℕ) : ℤ) = (a : ℤ) - 2 := Nat.cast_sub ha2
        have hz : (6 : ℤ) * (d4 (p ^ (a - 2)) : ℤ) =
            (((a - 2 : ℕ) : ℤ) + 1) * (((a - 2 : ℕ) : ℤ) + 2) * (((a - 2 : ℕ) : ℤ) + 3) := by
          exact_mod_cast hda2
        rw [hcast] at hz
        linarith
      have h6 : (6 : ℤ) * ((d4 (p ^ a) : ℤ) - (d4 (p ^ (a - 2)) : ℤ)) =
          (6 : ℤ) * ((a + 1 : ℕ) : ℤ) ^ 2 := by
        rw [mul_sub, hda_z, hda2_z]
        push_cast
        ring
      linarith
  | coprime a b _ha _hb hab iha ihb =>
    rw [d2SqInt_isMultiplicative.map_mul_of_coprime hab,
      (muSq_isMultiplicative.mul d4Int_isMultiplicative).map_mul_of_coprime hab, iha, ihb]

private lemma d2_sq_eq_sum_moebius_d4 (n : ℕ) :
    ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 =
      ∑ d ∈ n.divisors, (if (Nat.sqrt d) ^ 2 = d then (μ (Nat.sqrt d) : ℝ) else 0) *
        (d4 (n / d) : ℝ) := by
  have hz := congrArg (fun f : ArithmeticFunction ℤ => (f n : ℝ)) d2SqInt_eq_muSq_mul_d4Int
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (n := n) (f := fun x y => muSq x * d4Int y)] at hz
  simp only [d2SqInt, muSq, d4Int, coe_mk, d2, Int.cast_pow, Int.cast_natCast,
    Int.cast_sum, Int.cast_mul] at hz
  rw [hz]
  refine Finset.sum_congr rfl fun d _ => ?_
  split_ifs <;> simp

/- ### Section 2: Inductive Harmonic Sums of `1, d2, d3, d4` via Integral Comparison -/

private noncomputable def harmSum (f : ℕ → ℝ) (Y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, f n / (n : ℝ)

private lemma harmSum_one_eq_harmonic (Y : ℝ) :
    harmSum (fun _ => (1 : ℝ)) Y = (harmonic ⌊Y⌋₊ : ℝ) := by
  unfold harmSum
  generalize ⌊Y⌋₊ = N
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ N + 1), ih, harmonic_succ]
    push_cast
    rw [one_div]

private lemma harmSum_one_bound {Y : ℝ} (hY : 1 ≤ Y) :
    |harmSum (fun _ => (1 : ℝ)) Y - Real.log Y| ≤ 1 := by
  rw [harmSum_one_eq_harmonic]
  have hlow : Real.log Y ≤ (harmonic ⌊Y⌋₊ : ℝ) := log_le_harmonic_floor Y (by linarith)
  have hfl_pos : (0 : ℝ) < (⌊Y⌋₊ : ℝ) := by
    have : 1 ≤ ⌊Y⌋₊ := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hY)
    exact_mod_cast (by omega : 0 < ⌊Y⌋₊)
  have hup : (harmonic ⌊Y⌋₊ : ℝ) ≤ 1 + Real.log Y := by
    calc (harmonic ⌊Y⌋₊ : ℝ) ≤ 1 + Real.log (⌊Y⌋₊ : ℝ) := harmonic_le_one_add_log ⌊Y⌋₊
      _ ≤ 1 + Real.log Y := by
          gcongr
          exact Nat.floor_le (by linarith)
  rw [abs_le]
  constructor <;> linarith

private lemma harmSum_zeta_mul (f : ArithmeticFunction ℕ) {Y : ℝ} (hY : 0 ≤ Y) :
    harmSum (fun n => ((ArithmeticFunction.zeta * f) n : ℝ)) Y =
      ∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (1 / (a : ℝ)) * harmSum (fun b => (f b : ℝ)) (Y / a) := by
  unfold harmSum
  have hinner : ∀ n ∈ Finset.Icc 1 ⌊Y⌋₊,
      ((ArithmeticFunction.zeta * f) n : ℝ) / (n : ℝ) =
        ∑ d ∈ n.divisors, (f d : ℝ) / (n : ℝ) := by
    intro n _
    rw [ArithmeticFunction.zeta_mul_apply, Nat.cast_sum, Finset.sum_div]
  rw [Finset.sum_congr rfl hinner]
  simp_rw [Finset.mul_sum]
  let S := (Finset.Icc 1 ⌊Y⌋₊).sigma (fun n => n.divisors)
  let T := (Finset.Icc 1 ⌊Y⌋₊).sigma (fun a => Finset.Icc 1 ⌊Y / a⌋₊)
  have hL : (∑ n ∈ Finset.Icc 1 ⌊Y⌋₊, ∑ d ∈ n.divisors, (f d : ℝ) / (n : ℝ)) =
      ∑ p ∈ S, (f p.2 : ℝ) / (p.1 : ℝ) :=
    (Finset.sum_sigma (Finset.Icc 1 ⌊Y⌋₊) (fun n => n.divisors) (fun p => (f p.2 : ℝ) / (p.1 : ℝ))).symm
  have hR : (∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, ∑ b ∈ Finset.Icc 1 ⌊Y / a⌋₊, (1 / (a : ℝ)) * ((f b : ℝ) / (b : ℝ))) =
      ∑ p ∈ T, (1 / (p.1 : ℝ)) * ((f p.2 : ℝ) / (p.2 : ℝ)) :=
    (Finset.sum_sigma (Finset.Icc 1 ⌊Y⌋₊) (fun a => Finset.Icc 1 ⌊Y / a⌋₊)
      (fun p => (1 / (p.1 : ℝ)) * ((f p.2 : ℝ) / (p.2 : ℝ)))).symm
  rw [hL, hR]
  refine Finset.sum_bij (fun p _ => ⟨p.1 / p.2, p.2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨n, b⟩ hp
    simp only [S, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp
    obtain ⟨⟨hn1, hnY⟩, hbn, hn0⟩ := hp
    have hb_pos : 0 < b := Nat.pos_of_dvd_of_pos hbn (by omega)
    have ha_pos : 0 < n / b := Nat.div_pos (Nat.le_of_dvd (by omega) hbn) hb_pos
    have hab_eq : (n / b) * b = n := Nat.div_mul_cancel hbn
    have haY : n / b ≤ ⌊Y⌋₊ := le_trans (Nat.div_le_self n b) hnY
    have haR_pos : (0 : ℝ) < ((n / b : ℕ) : ℝ) := by exact_mod_cast ha_pos
    have hbYa : b ≤ ⌊Y / ((n / b : ℕ) : ℝ)⌋₊ := by
      rw [Nat.le_floor_iff (div_nonneg hY haR_pos.le), le_div_iff₀ haR_pos]
      have hmul : (b : ℝ) * ((n / b : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast (mul_comm b (n / b)).trans hab_eq
      rw [hmul]
      exact (Nat.le_floor_iff hY).mp hnY
    simp only [T, Finset.mem_sigma, Finset.mem_Icc]
    exact ⟨⟨ha_pos, haY⟩, ⟨hb_pos, hbYa⟩⟩
  · rintro ⟨n₁, b₁⟩ hp₁ ⟨n₂, b₂⟩ hp₂ h
    simp only [S, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp₁ hp₂
    have hq : n₁ / b₁ = n₂ / b₂ := congrArg Sigma.fst h
    have hb : b₁ = b₂ := by
      have := congrArg Sigma.snd h
      simpa using this
    subst hb
    have hn : n₁ = n₂ := by
      rw [← Nat.div_mul_cancel hp₁.2.1, ← Nat.div_mul_cancel hp₂.2.1, hq]
    subst hn; rfl
  · rintro ⟨a, b⟩ hp
    simp only [T, Finset.mem_sigma, Finset.mem_Icc] at hp
    obtain ⟨⟨ha1, haY⟩, ⟨hb1, hbYa⟩⟩ := hp
    have haR_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
    have habY : a * b ≤ ⌊Y⌋₊ := by
      rw [Nat.le_floor_iff hY]
      have h1 : (b : ℝ) ≤ Y / (a : ℝ) := (Nat.le_floor_iff (div_nonneg hY haR_pos.le)).mp hbYa
      have h2 := (le_div_iff₀ haR_pos).mp h1
      push_cast; linarith
    refine ⟨⟨a * b, b⟩, ?_, ?_⟩
    · simp only [S, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
      refine ⟨⟨by nlinarith, habY⟩, dvd_mul_left b a, by nlinarith⟩
    · have hdiv : a * b / b = a := Nat.mul_div_cancel a (by omega)
      simp [hdiv]
  · rintro ⟨n, b⟩ hp
    simp only [S, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp
    have hab : ((n / b : ℕ) : ℝ) * (b : ℝ) = (n : ℝ) := by
      exact_mod_cast Nat.div_mul_cancel hp.2.1
    rw [← hab]
    ring

private lemma integral_log_sub_pow_div (r : ℕ) {Y : ℝ} (hY : 1 ≤ Y) :
    ∫ t in (1 : ℝ)..Y, (Real.log Y - Real.log t) ^ r / t =
      (Real.log Y) ^ (r + 1) / ((r + 1 : ℕ) : ℝ) := by
  have hderiv : ∀ t ∈ Set.uIcc (1 : ℝ) Y,
      HasDerivAt (fun x : ℝ => -(Real.log Y - Real.log x) ^ (r + 1) / ((r + 1 : ℕ) : ℝ))
        ((Real.log Y - Real.log t) ^ r / t) t := by
    intro t ht
    rw [Set.uIcc_of_le hY] at ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    have h1 : HasDerivAt (fun x : ℝ => Real.log Y - Real.log x) (-t⁻¹) t :=
      (Real.hasDerivAt_log ht0).const_sub (Real.log Y)
    have h2 : HasDerivAt (fun x : ℝ => (Real.log Y - Real.log x) ^ (r + 1))
        (((r + 1 : ℕ) : ℝ) * (Real.log Y - Real.log t) ^ r * (-t⁻¹)) t := by
      have hp := h1.fun_pow (r + 1)
      simpa [Nat.add_sub_cancel] using hp
    have h3 := (h2.neg).div_const ((r + 1 : ℕ) : ℝ)
    have hval : -(((r + 1 : ℕ) : ℝ) * (Real.log Y - Real.log t) ^ r * (-t⁻¹)) / ((r + 1 : ℕ) : ℝ) =
        (Real.log Y - Real.log t) ^ r / t := by
      have hr : ((r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hr, ht0]
    exact hval ▸ h3
  have hcont : ContinuousOn (fun t : ℝ => (Real.log Y - Real.log t) ^ r / t) (Set.uIcc 1 Y) := by
    rw [Set.uIcc_of_le hY]
    refine ContinuousOn.div ?_ continuousOn_id (fun t ht => by linarith [ht.1])
    exact (continuousOn_const.sub (Real.continuousOn_log.mono (fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]))).pow r
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable)]
  simp; ring

private lemma sum_log_sub_pow_div_approx (r : ℕ) {Y : ℝ} (hY : 1 ≤ Y) :
    |(∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (Real.log (Y / a)) ^ r / (a : ℝ)) -
      (Real.log Y) ^ (r + 1) / ((r + 1 : ℕ) : ℝ)| ≤ (Real.log Y) ^ r := by
  let f : ℝ → ℝ := fun t => (Real.log Y - Real.log t) ^ r / t
  have hrew : ∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (Real.log (Y / a)) ^ r / (a : ℝ) =
      ∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, f (a : ℝ) := by
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha0 : (a : ℝ) ≠ 0 := by
      have := (Finset.mem_Icc.mp ha).1
      exact_mod_cast (by omega : a ≠ 0)
    simp only [f, Real.log_div (by linarith : Y ≠ 0) ha0]
  rw [hrew, ← integral_log_sub_pow_div r hY]
  have hf_nonneg : ∀ t ∈ Set.Icc (1 : ℝ) Y, 0 ≤ f t := by
    intro t ht
    have hlog : Real.log t ≤ Real.log Y := Real.log_le_log (by linarith [ht.1]) ht.2
    exact div_nonneg (pow_nonneg (sub_nonneg.mpr hlog) r) (by linarith [ht.1])
  have hf_anti : AntitoneOn f (Set.Icc 1 Y) := by
    intro x hx y hy hxy
    have hxpos : 0 < x := by linarith [hx.1]
    have hypos : 0 < y := by linarith [hy.1]
    have h1 : 0 ≤ Real.log Y - Real.log y := sub_nonneg.mpr (Real.log_le_log hypos hy.2)
    have h2 : Real.log Y - Real.log y ≤ Real.log Y - Real.log x := by
      linarith [Real.log_le_log hxpos hxy]
    have hpow : (Real.log Y - Real.log y) ^ r ≤ (Real.log Y - Real.log x) ^ r :=
      pow_le_pow_left₀ h1 h2 r
    exact div_le_div₀ (pow_nonneg (le_trans h1 h2) r) hpow hxpos hxy
  have hf_cont : ContinuousOn f (Set.Icc 1 Y) := by
    refine ContinuousOn.div ?_ continuousOn_id (fun t ht => by linarith [ht.1])
    exact (continuousOn_const.sub (Real.continuousOn_log.mono (fun t ht => by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]))).pow r
  have hf_int : ∀ u v : ℝ, 1 ≤ u → u ≤ v → v ≤ Y → IntervalIntegrable f volume u v := by
    intro u v hu huv hv
    refine (hf_cont.mono ?_).intervalIntegrable
    rw [Set.uIcc_of_le huv]
    exact fun t ht => ⟨le_trans hu ht.1, le_trans ht.2 hv⟩
  set N := ⌊Y⌋₊ with hN_def
  have hN1 : 1 ≤ N := (Nat.le_floor_iff (by linarith)).mpr (by simpa using hY)
  have hNY : (N : ℝ) ≤ Y := Nat.floor_le (by linarith)
  have hYlt : Y < (N : ℝ) + 1 := Nat.lt_floor_add_one Y
  -- Split integral from 1 to N into unit steps
  have hint_steps : ∀ k : ℕ, 1 ≤ k → k ≤ N →
      ∫ t in (1 : ℝ)..(k : ℝ), f t = ∑ a ∈ Finset.Icc 1 (k - 1), ∫ t in (a : ℝ)..((a : ℝ) + 1), f t := by
    intro k hk1 hkN
    induction k with
    | zero => omega
    | succ m ih =>
      by_cases hm0 : m = 0
      · subst hm0; simp
      · have hm1 : 1 ≤ m := by omega
        have hmN : m ≤ N := by omega
        have hsplit := intervalIntegral.integral_add_adjacent_intervals
          (hf_int 1 m (by exact_mod_cast hm1 |> fun _ => le_rfl) (by exact_mod_cast hm1)
            (le_trans (by exact_mod_cast hmN) hNY))
          (hf_int m (m + 1) (by exact_mod_cast hm1) (by linarith)
            (le_trans (by exact_mod_cast hkN) hNY))
        have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
        rw [hcast, ← hsplit, ih hm1 hmN]
        have hsub : m + 1 - 1 = (m - 1) + 1 := by omega
        rw [hsub, Finset.sum_Icc_succ_top (by omega : 1 ≤ (m - 1) + 1)]
        have hmeq : m - 1 + 1 = m := by omega
        rw [hmeq]
  have hsplit_all : ∫ t in (1 : ℝ)..Y, f t =
      (∫ t in (1 : ℝ)..(N : ℝ), f t) + ∫ t in (N : ℝ)..Y, f t :=
    (intervalIntegral.integral_add_adjacent_intervals
      (hf_int 1 N le_rfl (by exact_mod_cast hN1) hNY)
      (hf_int N Y (by exact_mod_cast hN1) hNY le_rfl)).symm
  -- Unit interval bounds
  have hunit_le : ∀ a ∈ Finset.Icc 1 (N - 1),
      f ((a : ℝ) + 1) ≤ ∫ t in (a : ℝ)..((a : ℝ) + 1), f t ∧
      ∫ t in (a : ℝ)..((a : ℝ) + 1), f t ≤ f (a : ℝ) := by
    intro a ha
    have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
    have haN : a + 1 ≤ N := by have := (Finset.mem_Icc.mp ha).2; omega
    have haR1 : (1 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha1
    have ha1Y : (a : ℝ) + 1 ≤ Y := le_trans (by exact_mod_cast haN) hNY
    have hint_a := hf_int a (a + 1) haR1 (by linarith) ha1Y
    constructor
    · have hconst : ∫ _ in (a : ℝ)..((a : ℝ) + 1), f ((a : ℝ) + 1) = f ((a : ℝ) + 1) := by
        simp
      rw [← hconst]
      refine intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const hint_a ?_
      intro t ht
      exact hf_anti ⟨le_trans haR1 ht.1, le_trans ht.2 ha1Y⟩ ⟨by linarith, ha1Y⟩ ht.2
    · have hconst : ∫ _ in (a : ℝ)..((a : ℝ) + 1), f (a : ℝ) = f (a : ℝ) := by
        simp
      rw [← hconst]
      refine intervalIntegral.integral_mono_on (by linarith) hint_a intervalIntegrable_const ?_
      intro t ht
      exact hf_anti ⟨haR1, by linarith⟩ ⟨le_trans haR1 ht.1, le_trans ht.2 ha1Y⟩ ht.1
  have htail_nn : 0 ≤ ∫ t in (N : ℝ)..Y, f t := by
    refine intervalIntegral.integral_nonneg hNY fun t ht => ?_
    exact hf_nonneg t ⟨le_trans (by exact_mod_cast hN1) ht.1, ht.2⟩
  have htail_le : ∫ t in (N : ℝ)..Y, f t ≤ f (N : ℝ) := by
    have hconst : ∫ _ in (N : ℝ)..Y, f (N : ℝ) = (Y - (N : ℝ)) * f (N : ℝ) := by
      simp [smul_eq_mul]
    have h1 : ∫ t in (N : ℝ)..Y, f t ≤ ∫ _ in (N : ℝ)..Y, f (N : ℝ) := by
      refine intervalIntegral.integral_mono_on hNY (hf_int N Y (by exact_mod_cast hN1) hNY le_rfl)
        intervalIntegrable_const fun t ht => ?_
      exact hf_anti ⟨by exact_mod_cast hN1, hNY⟩ ⟨le_trans (by exact_mod_cast hN1) ht.1, ht.2⟩ ht.1
    rw [hconst] at h1
    have hfn_nn : 0 ≤ f (N : ℝ) := hf_nonneg N ⟨by exact_mod_cast hN1, hNY⟩
    nlinarith
  have hlow : ∫ t in (1 : ℝ)..Y, f t ≤ ∑ a ∈ Finset.Icc 1 N, f (a : ℝ) := by
    rw [hsplit_all, hint_steps N hN1 le_rfl]
    have hsum_N : ∑ a ∈ Finset.Icc 1 N, f (a : ℝ) =
        (∑ a ∈ Finset.Icc 1 (N - 1), f (a : ℝ)) + f (N : ℝ) := by
      have hNeq : N = (N - 1) + 1 := by omega
      conv_lhs => rw [hNeq, Finset.sum_Icc_succ_top (by omega : 1 ≤ (N - 1) + 1)]
      rw [← hNeq]
    rw [hsum_N]
    exact add_le_add (Finset.sum_le_sum fun a ha => (hunit_le a ha).2) htail_le
  have hup : ∑ a ∈ Finset.Icc 1 N, f (a : ℝ) ≤ f 1 + ∫ t in (1 : ℝ)..Y, f t := by
    have hsum_shift : ∀ M : ℕ, 1 ≤ M → ∑ a ∈ Finset.Icc 1 M, f (a : ℝ) =
        f 1 + ∑ a ∈ Finset.Icc 1 (M - 1), f ((a : ℝ) + 1) := by
      intro M
      induction M with
      | zero => intro h; omega
      | succ m ih =>
        intro _
        by_cases hm0 : m = 0
        · subst hm0; simp
        · have hm1 : 1 ≤ m := by omega
          rw [Finset.sum_Icc_succ_top (by omega : 1 ≤ m + 1), ih hm1]
          have hsub : m + 1 - 1 = (m - 1) + 1 := by omega
          rw [hsub, Finset.sum_Icc_succ_top (by omega : 1 ≤ (m - 1) + 1)]
          have hmeq : m - 1 + 1 = m := by omega
          rw [hmeq]
          push_cast; ring
    rw [hsum_shift N hN1, hsplit_all, hint_steps N hN1 le_rfl]
    have hsum_le : ∑ a ∈ Finset.Icc 1 (N - 1), f ((a : ℝ) + 1) ≤
        ∑ a ∈ Finset.Icc 1 (N - 1), ∫ t in (a : ℝ)..((a : ℝ) + 1), f t :=
      Finset.sum_le_sum fun a ha => (hunit_le a ha).1
    linarith
  have hf1 : f 1 = (Real.log Y) ^ r := by simp [f]
  rw [hf1] at hup
  rw [abs_le]
  constructor <;> linarith

private lemma harmSum_step {f : ArithmeticFunction ℕ} {r : ℕ} {C : ℝ}
    (hr : 1 ≤ r) (hC : 0 ≤ C)
    (hf : ∀ Y : ℝ, 1 ≤ Y →
      |harmSum (fun n => (f n : ℝ)) Y - (Real.log Y) ^ r / (Nat.factorial r : ℝ)| ≤
        C * (Real.log Y + 1) ^ (r - 1)) :
    ∀ Y : ℝ, 1 ≤ Y →
      |harmSum (fun n => ((ArithmeticFunction.zeta * f) n : ℝ)) Y -
        (Real.log Y) ^ (r + 1) / (Nat.factorial (r + 1) : ℝ)| ≤
        (C + 1) * (Real.log Y + 1) ^ r := by
  intro Y hY
  rw [harmSum_zeta_mul f (by linarith)]
  have hlog_nn : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hfac : ((Nat.factorial (r + 1) : ℕ) : ℝ) = ((r + 1 : ℕ) : ℝ) * (Nat.factorial r : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hmain_split :
      (∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (1 / (a : ℝ)) * harmSum (fun b => (f b : ℝ)) (Y / a)) -
        (Real.log Y) ^ (r + 1) / (Nat.factorial (r + 1) : ℝ) =
      (∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (1 / (a : ℝ)) *
          (harmSum (fun b => (f b : ℝ)) (Y / a) - (Real.log (Y / a)) ^ r / (Nat.factorial r : ℝ))) +
      (1 / (Nat.factorial r : ℝ)) *
        ((∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (Real.log (Y / a)) ^ r / (a : ℝ)) -
          (Real.log Y) ^ (r + 1) / ((r + 1 : ℕ) : ℝ)) := by
    rw [hfac, mul_sub, Finset.mul_sum]
    simp_rw [mul_sub, Finset.sum_sub_distrib]
    have hsum_eq : ∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (1 / (a : ℝ)) * ((Real.log (Y / a)) ^ r / (Nat.factorial r : ℝ)) =
        ∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (1 / (Nat.factorial r : ℝ)) * ((Real.log (Y / a)) ^ r / (a : ℝ)) := by
      refine Finset.sum_congr rfl fun a _ => by ring
    rw [hsum_eq]
    have hconst : (1 / (Nat.factorial r : ℝ)) * ((Real.log Y) ^ (r + 1) / ((r + 1 : ℕ) : ℝ)) =
        (Real.log Y) ^ (r + 1) / (((r + 1 : ℕ) : ℝ) * (Nat.factorial r : ℝ)) := by ring
    rw [hconst]
    ring
  rw [hmain_split]
  have herr1 : |∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (1 / (a : ℝ)) *
      (harmSum (fun b => (f b : ℝ)) (Y / a) - (Real.log (Y / a)) ^ r / (Nat.factorial r : ℝ))| ≤
      C * (Real.log Y + 1) ^ r := by
    calc |∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (1 / (a : ℝ)) *
            (harmSum (fun b => (f b : ℝ)) (Y / a) - (Real.log (Y / a)) ^ r / (Nat.factorial r : ℝ))|
        ≤ ∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, |(1 / (a : ℝ)) *
            (harmSum (fun b => (f b : ℝ)) (Y / a) - (Real.log (Y / a)) ^ r / (Nat.factorial r : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (1 / (a : ℝ)) * (C * (Real.log Y + 1) ^ (r - 1)) := by
          refine Finset.sum_le_sum fun a ha => ?_
          have ha1 : 1 ≤ a := (Finset.mem_Icc.mp ha).1
          have haY : a ≤ ⌊Y⌋₊ := (Finset.mem_Icc.mp ha).2
          have ha_pos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast (by omega : 0 < a)
          have hYa : 1 ≤ Y / (a : ℝ) := by
            rw [one_le_div ha_pos]
            exact le_trans (by exact_mod_cast haY) (Nat.floor_le (by linarith))
          have hlog_le : Real.log (Y / a) ≤ Real.log Y := by
            apply Real.log_le_log (by linarith)
            exact div_le_self (by linarith) (by exact_mod_cast ha1)
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (a : ℝ))]
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          calc |harmSum (fun b => (f b : ℝ)) (Y / a) - (Real.log (Y / a)) ^ r / (Nat.factorial r : ℝ)|
              ≤ C * (Real.log (Y / a) + 1) ^ (r - 1) := hf (Y / a) hYa
            _ ≤ C * (Real.log Y + 1) ^ (r - 1) := by
                refine mul_le_mul_of_nonneg_left ?_ hC
                exact pow_le_pow_left₀ (by linarith [Real.log_nonneg hYa]) (by linarith) _
      _ = (C * (Real.log Y + 1) ^ (r - 1)) * harmSum (fun _ => (1 : ℝ)) Y := by
          rw [← Finset.sum_mul, mul_comm]; rfl
      _ ≤ (C * (Real.log Y + 1) ^ (r - 1)) * (Real.log Y + 1) := by
          have h1 := (abs_le.mp (harmSum_one_bound hY)).2
          exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = C * (Real.log Y + 1) ^ r := by
          cases r with
          | zero => omega
          | succ k => simp [pow_succ]; ring
  have herr2 : |(1 / (Nat.factorial r : ℝ)) *
      ((∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (Real.log (Y / a)) ^ r / (a : ℝ)) -
        (Real.log Y) ^ (r + 1) / ((r + 1 : ℕ) : ℝ))| ≤ (Real.log Y + 1) ^ r := by
    have hfac_ge1 : (1 : ℝ) ≤ (Nat.factorial r : ℝ) := by
      exact_mod_cast Nat.factorial_pos r
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 / (Nat.factorial r : ℝ))]
    calc (1 / (Nat.factorial r : ℝ)) *
            |(∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (Real.log (Y / a)) ^ r / (a : ℝ)) -
              (Real.log Y) ^ (r + 1) / ((r + 1 : ℕ) : ℝ)|
        ≤ 1 * (Real.log Y) ^ r := by
          refine mul_le_mul ?_ (sum_log_sub_pow_div_approx r hY) (abs_nonneg _) zero_le_one
          exact div_le_one_of_le₀ hfac_ge1 (by positivity)
      _ = (Real.log Y) ^ r := one_mul _
      _ ≤ (Real.log Y + 1) ^ r := pow_le_pow_left₀ hlog_nn (by linarith) r
  calc _ ≤ |∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (1 / (a : ℝ)) *
              (harmSum (fun b => (f b : ℝ)) (Y / a) - (Real.log (Y / a)) ^ r / (Nat.factorial r : ℝ))| +
            |(1 / (Nat.factorial r : ℝ)) *
              ((∑ a ∈ Finset.Icc 1 ⌊Y⌋₊, (Real.log (Y / a)) ^ r / (a : ℝ)) -
                (Real.log Y) ^ (r + 1) / ((r + 1 : ℕ) : ℝ))| := abs_add_le _ _
    _ ≤ C * (Real.log Y + 1) ^ r + (Real.log Y + 1) ^ r := add_le_add herr1 herr2
    _ = (C + 1) * (Real.log Y + 1) ^ r := by ring

private lemma harmSum_d4_bound {Y : ℝ} (hY : 1 ≤ Y) :
    |harmSum (fun n => (d4 n : ℝ)) Y - (Real.log Y) ^ 4 / 24| ≤ 4 * (Real.log Y + 1) ^ 3 := by
  have h1 : ∀ y : ℝ, 1 ≤ y →
      |harmSum (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) n : ℝ)) y -
        (Real.log y) ^ 1 / (Nat.factorial 1 : ℝ)| ≤ 1 * (Real.log y + 1) ^ (1 - 1) := by
    intro y hy
    have heq : harmSum (fun n => ((ArithmeticFunction.zeta : ArithmeticFunction ℕ) n : ℝ)) y =
        harmSum (fun _ => (1 : ℝ)) y := by
      refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := by have := (Finset.mem_Icc.mp hn).1; omega
      simp [ArithmeticFunction.zeta_apply, hn0]
    rw [heq]
    simpa using harmSum_one_bound hy
  have h2 : ∀ y : ℝ, 1 ≤ y →
      |harmSum (fun n => (d2 n : ℝ)) y - (Real.log y) ^ 2 / (Nat.factorial 2 : ℝ)| ≤
        (1 + 1) * (Real.log y + 1) ^ (2 - 1) := by
    rw [d2_eq_zeta_mul_zeta]
    exact harmSum_step (r := 1) (by omega) (by norm_num) h1
  have h3 : ∀ y : ℝ, 1 ≤ y →
      |harmSum (fun n => (d3 n : ℝ)) y - (Real.log y) ^ 3 / (Nat.factorial 3 : ℝ)| ≤
        ((1 + 1) + 1) * (Real.log y + 1) ^ (3 - 1) :=
    harmSum_step (r := 2) (by omega) (by norm_num) h2
  have h4 := harmSum_step (r := 3) (by omega) (by norm_num) h3 Y hY
  have hfac4 : (Nat.factorial 4 : ℝ) = 24 := by norm_num [Nat.factorial]
  rw [hfac4] at h4
  have hC : ((1 + 1 : ℝ) + 1) + 1 = 4 := by norm_num
  rw [hC] at h4
  exact h4

/- ### Section 3: Möbius Reciprocal-Square Limit `∑ μ(k)/k² → 6/π²` -/

private lemma summable_one_div_sq : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
  hasSum_zeta_two.summable

private lemma tendsto_sum_one_div_sq :
    Tendsto (fun K : ℕ => ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) ^ 2) atTop (𝓝 (Real.pi ^ 2 / 6)) := by
  have h := hasSum_zeta_two.tendsto_sum_nat
  have heq : ∀ K : ℕ, ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) ^ 2 =
      ∑ m ∈ Finset.range (K + 1), (1 : ℝ) / (m : ℝ) ^ 2 := by
    intro K
    rw [Finset.sum_range_eq_add_Ico _ (by omega : 0 < K + 1)]
    have hset : Finset.Icc 1 K = Finset.Ico 1 (K + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    rw [hset]
    simp
  simp_rw [heq]
  exact h.comp (tendsto_add_atTop_nat 1)

private lemma tendsto_sum_moebius_div_sq :
    Tendsto (fun K : ℕ => ∑ k ∈ Finset.Icc 1 K, (μ k : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 (6 / Real.pi ^ 2)) := by
  let M : ℕ → ℝ := fun K => ∑ k ∈ Finset.Icc 1 K, (μ k : ℝ) / (k : ℝ) ^ 2
  let Z : ℕ → ℝ := fun K => ∑ m ∈ Finset.Icc 1 K, (1 : ℝ) / (m : ℝ) ^ 2
  have hZ_lim : Tendsto Z atTop (𝓝 (Real.pi ^ 2 / 6)) := tendsto_sum_one_div_sq
  have hpi2 : Real.pi ^ 2 / 6 ≠ 0 := by positivity
  -- Show M K * Z K -> 1
  have hprod_lim : Tendsto (fun K : ℕ => M K * Z K) atTop (𝓝 1) := by
    have hdiff_bound : ∀ K : ℕ, 1 ≤ K →
        |M K * Z K - 1| ≤
          2 * (Real.pi ^ 2 / 6) *
            ∑ k ∈ Finset.Icc (Nat.sqrt K + 1) K, (1 : ℝ) / (k : ℝ) ^ 2 := by
      intro K hK
      have hprod_eq : M K * Z K =
          ∑ p ∈ Finset.Icc 1 K ×ˢ Finset.Icc 1 K, (μ p.1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2) := by
        dsimp only [M, Z]
        rw [Finset.sum_mul]
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_product']
        refine Finset.sum_congr rfl fun p _ => by ring
      rw [hprod_eq]
      let P := Finset.Icc 1 K ×ˢ Finset.Icc 1 K
      let Ple := P.filter (fun p => p.1 * p.2 ≤ K)
      let Pgt := P.filter (fun p => ¬ p.1 * p.2 ≤ K)
      rw [← Finset.sum_filter_add_sum_filter_not P (fun p => p.1 * p.2 ≤ K)]
      have hPle_eq : ∑ p ∈ Ple, (μ p.1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2) = 1 := by
        have hbij : ∑ p ∈ Ple, (μ p.1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2) =
            ∑ n ∈ Finset.Icc 1 K, (1 / (n : ℝ) ^ 2) * ∑ d ∈ n.divisors, (μ d : ℝ) := by
          simp_rw [Finset.mul_sum]
          have hsig : (∑ n ∈ Finset.Icc 1 K, ∑ d ∈ n.divisors, (1 / (n : ℝ) ^ 2) * (μ d : ℝ)) =
              ∑ p ∈ (Finset.Icc 1 K).sigma (fun n => n.divisors), (1 / (p.1 : ℝ) ^ 2) * (μ p.2 : ℝ) :=
            (Finset.sum_sigma (Finset.Icc 1 K) (fun n => n.divisors)
              (fun p => (1 / (p.1 : ℝ) ^ 2) * (μ p.2 : ℝ))).symm
          rw [hsig]
          refine Finset.sum_bij (fun p _ => ⟨p.1 * p.2, p.1⟩) ?_ ?_ ?_ ?_
          · rintro ⟨a, b⟩ hp
            simp only [Ple, P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp
            simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
            refine ⟨⟨by nlinarith, hp.2⟩, dvd_mul_right a b, by nlinarith⟩
          · rintro ⟨a₁, b₁⟩ hp₁ ⟨a₂, b₂⟩ hp₂ h
            simp only [Ple, P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc] at hp₁ hp₂
            have hmul : a₁ * b₁ = a₂ * b₂ := congrArg Sigma.fst h
            have ha : a₁ = a₂ := by simpa using congrArg Sigma.snd h
            subst ha
            have hb : b₁ = b₂ := Nat.eq_of_mul_eq_mul_left (by omega : 0 < a₁) hmul
            subst hb; rfl
          · rintro ⟨n, d⟩ hp
            simp only [Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp
            obtain ⟨⟨hn1, hnK⟩, hdn, hn0⟩ := hp
            have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
            have hq_pos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdn) hd_pos
            refine ⟨(d, n / d), ?_, ?_⟩
            · simp only [Ple, P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
              exact ⟨⟨⟨hd_pos, le_trans (Nat.le_of_dvd (by omega) hdn) hnK⟩,
                ⟨hq_pos, le_trans (Nat.div_le_self n d) hnK⟩⟩, by rw [Nat.mul_div_cancel' hdn]; exact hnK⟩
            · simp [Nat.mul_div_cancel' hdn]
          · rintro ⟨a, b⟩ _
            push_cast; ring
        rw [hbij, Finset.sum_eq_single 1]
        · simp
        · intro n hn hn1
          have hmu0 : (∑ d ∈ n.divisors, (μ d : ℝ)) = 0 := by
            have hz := congrArg (fun f : ArithmeticFunction ℤ => (f n : ℝ))
              ArithmeticFunction.moebius_mul_coe_zeta
            rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply, if_neg hn1] at hz
            simpa using hz
          rw [hmu0, mul_zero]
        · intro h; exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hK⟩) h
      rw [hPle_eq, add_sub_cancel_left]
      have hmu_le : ∀ k : ℕ, |(μ k : ℝ)| ≤ 1 := by
        intro k
        have h1 : |μ k| ≤ 1 := by
          by_cases hsf : Squarefree k
          · rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]; simp
          · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; simp
        exact_mod_cast h1
      have hPgt_sub : Pgt ⊆ (Finset.Icc (Nat.sqrt K + 1) K ×ˢ Finset.Icc 1 K) ∪
          (Finset.Icc 1 K ×ˢ Finset.Icc (Nat.sqrt K + 1) K) := by
        intro p hp
        simp only [Pgt, P, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, not_le] at hp
        simp only [Finset.mem_union, Finset.mem_product, Finset.mem_Icc]
        by_cases h1 : Nat.sqrt K + 1 ≤ p.1
        · exact Or.inl ⟨⟨h1, hp.1.1.2⟩, hp.1.2⟩
        · refine Or.inr ⟨hp.1.1, ⟨?_, hp.1.2.2⟩⟩
          by_contra h2
          have hle1 : p.1 ≤ Nat.sqrt K := by omega
          have hle2 : p.2 ≤ Nat.sqrt K := by omega
          have hmul : p.1 * p.2 ≤ Nat.sqrt K * Nat.sqrt K := Nat.mul_le_mul hle1 hle2
          have hsq : Nat.sqrt K * Nat.sqrt K ≤ K := Nat.sqrt_le K
          omega
      have hZ_le : Z K ≤ Real.pi ^ 2 / 6 := by
        rw [← hasSum_zeta_two.tsum_eq]
        exact Summable.sum_le_tsum (Finset.Icc 1 K) (fun _ _ => by positivity) summable_one_div_sq
      calc |∑ p ∈ Pgt, (μ p.1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2)|
          ≤ ∑ p ∈ Pgt, |(μ p.1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2)| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p ∈ Pgt, (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2) := by
            refine Finset.sum_le_sum fun p _ => ?_
            rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2)]
            exact div_le_div_of_nonneg_right (hmu_le p.1) (by positivity)
        _ ≤ ∑ p ∈ (Finset.Icc (Nat.sqrt K + 1) K ×ˢ Finset.Icc 1 K) ∪
              (Finset.Icc 1 K ×ˢ Finset.Icc (Nat.sqrt K + 1) K),
              (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2) :=
            Finset.sum_le_sum_of_subset_of_nonneg hPgt_sub (fun _ _ _ => by positivity)
        _ ≤ (∑ p ∈ Finset.Icc (Nat.sqrt K + 1) K ×ˢ Finset.Icc 1 K,
              (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2)) +
            (∑ p ∈ Finset.Icc 1 K ×ˢ Finset.Icc (Nat.sqrt K + 1) K,
              (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2)) := by
            have hu := Finset.sum_union_inter
              (s₁ := Finset.Icc (Nat.sqrt K + 1) K ×ˢ Finset.Icc 1 K)
              (s₂ := Finset.Icc 1 K ×ˢ Finset.Icc (Nat.sqrt K + 1) K)
              (f := fun p : ℕ × ℕ => (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2))
            have hinter_nn : 0 ≤ ∑ p ∈ (Finset.Icc (Nat.sqrt K + 1) K ×ˢ Finset.Icc 1 K) ∩
                (Finset.Icc 1 K ×ˢ Finset.Icc (Nat.sqrt K + 1) K),
                (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2) :=
              Finset.sum_nonneg fun _ _ => by positivity
            linarith
        _ = 2 * Z K * ∑ k ∈ Finset.Icc (Nat.sqrt K + 1) K, (1 : ℝ) / (k : ℝ) ^ 2 := by
            have h1 : ∑ p ∈ Finset.Icc (Nat.sqrt K + 1) K ×ˢ Finset.Icc 1 K,
                (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2) =
                (∑ k ∈ Finset.Icc (Nat.sqrt K + 1) K, (1 : ℝ) / (k : ℝ) ^ 2) * Z K := by
              rw [Finset.sum_product, Finset.sum_mul]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun m _ => by ring
            have h2 : ∑ p ∈ Finset.Icc 1 K ×ˢ Finset.Icc (Nat.sqrt K + 1) K,
                (1 : ℝ) / ((p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 2) =
                Z K * (∑ k ∈ Finset.Icc (Nat.sqrt K + 1) K, (1 : ℝ) / (k : ℝ) ^ 2) := by
              rw [Finset.sum_product, Finset.sum_mul]
              refine Finset.sum_congr rfl fun m _ => ?_
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => by ring
            rw [h1, h2]; ring
        _ ≤ 2 * (Real.pi ^ 2 / 6) * ∑ k ∈ Finset.Icc (Nat.sqrt K + 1) K, (1 : ℝ) / (k : ℝ) ^ 2 := by
            have hnn : 0 ≤ ∑ k ∈ Finset.Icc (Nat.sqrt K + 1) K, (1 : ℝ) / (k : ℝ) ^ 2 :=
              Finset.sum_nonneg fun _ _ => by positivity
            nlinarith
    have htail_lim : Tendsto (fun K : ℕ =>
        ∑ k ∈ Finset.Icc (Nat.sqrt K + 1) K, (1 : ℝ) / (k : ℝ) ^ 2) atTop (𝓝 0) := by
      have hdiff : ∀ K : ℕ,
          ∑ k ∈ Finset.Icc (Nat.sqrt K + 1) K, (1 : ℝ) / (k : ℝ) ^ 2 = Z K - Z (Nat.sqrt K) := by
        intro K
        have hle : Nat.sqrt K ≤ K := Nat.sqrt_le_self K
        have hsplit : Z K = Z (Nat.sqrt K) + ∑ k ∈ Finset.Icc (Nat.sqrt K + 1) K, (1 : ℝ) / (k : ℝ) ^ 2 := by
          dsimp only [Z]
          rw [← Finset.sum_union]
          · congr 1
            ext k
            simp only [Finset.mem_Icc, Finset.mem_union]
            omega
          · rw [Finset.disjoint_left]
            intro k hk1 hk2
            simp only [Finset.mem_Icc] at hk1 hk2
            omega
        linarith
      simp_rw [hdiff]
      have hsqrt_top : Tendsto Nat.sqrt atTop atTop := by
        rw [Filter.tendsto_atTop_atTop]
        intro b
        refine ⟨b ^ 2, fun n hn => ?_⟩
        rw [Nat.le_sqrt, ← sq]
        exact hn
      have hsub := hZ_lim.sub (hZ_lim.comp hsqrt_top)
      simpa using hsub
    have hbound_lim : Tendsto (fun K : ℕ =>
        2 * (Real.pi ^ 2 / 6) * ∑ k ∈ Finset.Icc (Nat.sqrt K + 1) K, (1 : ℝ) / (k : ℝ) ^ 2)
        atTop (𝓝 0) := by
      simpa using htail_lim.const_mul (2 * (Real.pi ^ 2 / 6))
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨N₁, hN₁⟩ := Metric.tendsto_atTop.mp hbound_lim ε hε
    refine ⟨max N₁ 1, fun K hK => ?_⟩
    rw [Real.dist_eq]
    have h1 := hdiff_bound K (le_trans (le_max_right _ _) hK)
    have h2 := hN₁ K (le_trans (le_max_left _ _) hK)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
      refine mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => by positivity))] at h2
    exact lt_of_le_of_lt h1 h2
  have hdiv := hprod_lim.div hZ_lim hpi2
  have hlim_val : (1 : ℝ) / (Real.pi ^ 2 / 6) = 6 / Real.pi ^ 2 := by field_simp [Real.pi_ne_zero]
  rw [hlim_val] at hdiv
  refine hdiv.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with K hK
  have hZpos : 0 < Z K := by
    have h1mem : (1 : ℕ) ∈ Finset.Icc 1 K := Finset.mem_Icc.mpr ⟨le_rfl, hK⟩
    have hle : (1 : ℝ) / ((1 : ℕ) : ℝ) ^ 2 ≤ Z K :=
      Finset.single_le_sum (f := fun m : ℕ => (1 : ℝ) / (m : ℝ) ^ 2)
        (fun _ _ => by positivity) h1mem
    norm_num at hle
    linarith
  exact mul_div_cancel_right₀ (M K) hZpos.ne'

/- ### Section 4: Assembly of `RiemannZetaMoments.moment_isEquiv-83.R1.H3` -/

private lemma sum_d2sq_eq_sum_moebius_harmSum_d4 {X : ℝ} (hX : 0 ≤ X) :
    (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 / (n : ℝ)) =
      ∑ k ∈ Finset.Icc 1 (Nat.sqrt ⌊X⌋₊),
        ((μ k : ℝ) / (k : ℝ) ^ 2) * harmSum (fun m => (d4 m : ℝ)) (X / (k : ℝ) ^ 2) := by
  have hstep : ∀ n ∈ Finset.Icc 1 ⌊X⌋₊,
      ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 / (n : ℝ) =
        ∑ d ∈ n.divisors,
          (if (Nat.sqrt d) ^ 2 = d then (μ (Nat.sqrt d) : ℝ) else 0) * (d4 (n / d) : ℝ) / (n : ℝ) := by
    intro n _
    rw [d2_sq_eq_sum_moebius_d4 n, Finset.sum_div]
  rw [Finset.sum_congr rfl hstep]
  unfold harmSum
  simp_rw [Finset.mul_sum]
  let S := ((Finset.Icc 1 ⌊X⌋₊).sigma (fun n => n.divisors)).filter (fun p => (Nat.sqrt p.2) ^ 2 = p.2)
  let T := (Finset.Icc 1 (Nat.sqrt ⌊X⌋₊)).sigma (fun k => Finset.Icc 1 ⌊X / (k : ℝ) ^ 2⌋₊)
  have hL : (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ∑ d ∈ n.divisors,
        (if (Nat.sqrt d) ^ 2 = d then (μ (Nat.sqrt d) : ℝ) else 0) * (d4 (n / d) : ℝ) / (n : ℝ)) =
      ∑ p ∈ (Finset.Icc 1 ⌊X⌋₊).sigma (fun n => n.divisors),
        (if (Nat.sqrt p.2) ^ 2 = p.2 then (μ (Nat.sqrt p.2) : ℝ) else 0) * (d4 (p.1 / p.2) : ℝ) / (p.1 : ℝ) :=
    (Finset.sum_sigma (Finset.Icc 1 ⌊X⌋₊) (fun n => n.divisors)
      (fun p => (if (Nat.sqrt p.2) ^ 2 = p.2 then (μ (Nat.sqrt p.2) : ℝ) else 0) * (d4 (p.1 / p.2) : ℝ) / (p.1 : ℝ))).symm
  have hR : (∑ k ∈ Finset.Icc 1 (Nat.sqrt ⌊X⌋₊), ∑ m ∈ Finset.Icc 1 ⌊X / (k : ℝ) ^ 2⌋₊,
        ((μ k : ℝ) / (k : ℝ) ^ 2) * ((d4 m : ℝ) / (m : ℝ))) =
      ∑ p ∈ T, ((μ p.1 : ℝ) / (p.1 : ℝ) ^ 2) * ((d4 p.2 : ℝ) / (p.2 : ℝ)) :=
    (Finset.sum_sigma (Finset.Icc 1 (Nat.sqrt ⌊X⌋₊)) (fun k => Finset.Icc 1 ⌊X / (k : ℝ) ^ 2⌋₊)
      (fun p => ((μ p.1 : ℝ) / (p.1 : ℝ) ^ 2) * ((d4 p.2 : ℝ) / (p.2 : ℝ)))).symm
  rw [hL, hR]
  have hfilter : ∑ p ∈ (Finset.Icc 1 ⌊X⌋₊).sigma (fun n => n.divisors),
      (if (Nat.sqrt p.2) ^ 2 = p.2 then (μ (Nat.sqrt p.2) : ℝ) else 0) * (d4 (p.1 / p.2) : ℝ) / (p.1 : ℝ) =
      ∑ p ∈ S, (μ (Nat.sqrt p.2) : ℝ) * (d4 (p.1 / p.2) : ℝ) / (p.1 : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ => ?_
    split_ifs <;> simp
  rw [hfilter]
  refine Finset.sum_bij (fun p _ => ⟨Nat.sqrt p.2, p.1 / p.2⟩) ?_ ?_ ?_ ?_
  · rintro ⟨n, d⟩ hp
    simp only [S, Finset.mem_filter, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp
    obtain ⟨⟨⟨hn1, hnX⟩, hdn, hn0⟩, hsq⟩ := hp
    set k := Nat.sqrt d
    have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
    have hk_pos : 0 < k := by
      by_contra h0; push Not at h0
      have hk0 : k = 0 := by omega
      rw [hk0, zero_pow (by norm_num)] at hsq; omega
    have hk_le : k ≤ Nat.sqrt ⌊X⌋₊ := by
      rw [Nat.le_sqrt, ← sq, hsq]
      exact le_trans (Nat.le_of_dvd (by omega) hdn) hnX
    have hm_pos : 0 < n / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdn) hd_pos
    have hk2_pos : (0 : ℝ) < (k : ℝ) ^ 2 := by exact_mod_cast (by positivity : 0 < k ^ 2)
    have hm_le : n / d ≤ ⌊X / (k : ℝ) ^ 2⌋₊ := by
      rw [Nat.le_floor_iff (div_nonneg hX hk2_pos.le), le_div_iff₀ hk2_pos]
      have hmul : ((n / d : ℕ) : ℝ) * (k : ℝ) ^ 2 = (n : ℝ) := by
        have hnat : (n / d) * k ^ 2 = n := by rw [hsq]; exact Nat.div_mul_cancel hdn
        exact_mod_cast hnat
      rw [hmul]
      exact (Nat.le_floor_iff hX).mp hnX
    simp only [T, Finset.mem_sigma, Finset.mem_Icc]
    exact ⟨⟨hk_pos, hk_le⟩, ⟨hm_pos, hm_le⟩⟩
  · rintro ⟨n₁, d₁⟩ hp₁ ⟨n₂, d₂⟩ hp₂ h
    simp only [S, Finset.mem_filter, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp₁ hp₂
    have hk : Nat.sqrt d₁ = Nat.sqrt d₂ := congrArg Sigma.fst h
    have hd : d₁ = d₂ := by rw [← hp₁.2, ← hp₂.2, hk]
    subst hd
    have hm : n₁ / d₁ = n₂ / d₁ := by simpa using congrArg Sigma.snd h
    have hn : n₁ = n₂ := by
      rw [← Nat.div_mul_cancel hp₁.1.2.1, ← Nat.div_mul_cancel hp₂.1.2.1, hm]
    subst hn; rfl
  · rintro ⟨k, m⟩ hp
    simp only [T, Finset.mem_sigma, Finset.mem_Icc] at hp
    obtain ⟨⟨hk1, hkX⟩, ⟨hm1, hmX⟩⟩ := hp
    have hk2_pos : (0 : ℝ) < (k : ℝ) ^ 2 := by exact_mod_cast (by positivity : 0 < k ^ 2)
    have hprodX : k ^ 2 * m ≤ ⌊X⌋₊ := by
      rw [Nat.le_floor_iff hX]
      have h1 : (m : ℝ) ≤ X / (k : ℝ) ^ 2 := (Nat.le_floor_iff (div_nonneg hX hk2_pos.le)).mp hmX
      have h2 := (le_div_iff₀ hk2_pos).mp h1
      push_cast; linarith
    refine ⟨⟨k ^ 2 * m, k ^ 2⟩, ?_, ?_⟩
    · simp only [S, Finset.mem_filter, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors]
      refine ⟨⟨⟨by nlinarith, hprodX⟩, dvd_mul_right (k ^ 2) m, by nlinarith⟩, by rw [Nat.sqrt_eq']⟩
    · have hdiv : k ^ 2 * m / k ^ 2 = m := Nat.mul_div_cancel_left m (by positivity)
      simp [Nat.sqrt_eq', hdiv]
  · rintro ⟨n, d⟩ hp
    simp only [S, Finset.mem_filter, Finset.mem_sigma, Finset.mem_Icc, Nat.mem_divisors] at hp
    have hnat : (Nat.sqrt d) ^ 2 * (n / d) = n := by
      rw [hp.2]; exact Nat.mul_div_cancel' hp.1.2.1
    have hreal : ((Nat.sqrt d : ℕ) : ℝ) ^ 2 * ((n / d : ℕ) : ℝ) = (n : ℝ) := by
      exact_mod_cast hnat
    rw [← hreal]
    ring

private lemma summable_log_div_sq : Summable (fun k : ℕ => Real.log (k : ℝ) / (k : ℝ) ^ 2) := by
  have hsum32 : Summable (fun k : ℕ => (2 : ℝ) * (1 / (k : ℝ) ^ ((3 : ℝ) / 2))) :=
    (Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 2
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hsum32
  · cases k with
    | zero => simp
    | succ m => exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m + 1))) (by positivity)
  · cases k with
    | zero => simp
    | succ m =>
      have hkpos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hlog : Real.log ((m + 1 : ℕ) : ℝ) ≤ 2 * ((m + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := by
        have hsqrt_pos : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hkpos _
        have h1 := Real.log_le_sub_one_of_pos hsqrt_pos
        rw [Real.log_rpow hkpos] at h1
        linarith
      have hrpow : ((m + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) * ((m + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) =
          ((m + 1 : ℕ) : ℝ) ^ 2 := by
        rw [← Real.rpow_add hkpos]
        norm_num
      calc Real.log ((m + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) ^ 2
          ≤ (2 * ((m + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2)) / ((m + 1 : ℕ) : ℝ) ^ 2 :=
            div_le_div_of_nonneg_right hlog (by positivity)
        _ = 2 * (1 / ((m + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2)) := by
            rw [← hrpow]
            have h1 : ((m + 1 : ℕ) : ℝ) ^ ((1 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hkpos _).ne'
            have h2 : ((m + 1 : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≠ 0 := (Real.rpow_pos_of_pos hkpos _).ne'
            field_simp [h1, h2]

private theorem main_H3 : OMA.R_RiemannZetaMoments_moment_isEquiv_83_R1.H3 := by
  rw [OMA.R_RiemannZetaMoments_moment_isEquiv_83_R1.H3, Asymptotics.isEquivalent_iff_tendsto_one]
  · let C_log : ℝ := ∑' k : ℕ, Real.log (k : ℝ) / (k : ℝ) ^ 2
    let C_sq : ℝ := Real.pi ^ 2 / 6
    let M : ℕ → ℝ := fun K => ∑ k ∈ Finset.Icc 1 K, (μ k : ℝ) / (k : ℝ) ^ 2
    have hM_lim : Tendsto (fun X : ℝ => M (Nat.sqrt ⌊X⌋₊)) atTop (𝓝 (6 / Real.pi ^ 2)) := by
      have hfloor : Tendsto (fun X : ℝ => ⌊X⌋₊) atTop atTop := by
        rw [Filter.tendsto_atTop_atTop]
        intro b
        exact ⟨(b : ℝ), fun X hX => (Nat.le_floor_iff (le_trans (Nat.cast_nonneg b) hX)).mpr hX⟩
      have hsqrt : Tendsto Nat.sqrt atTop atTop := by
        rw [Filter.tendsto_atTop_atTop]
        intro b
        refine ⟨b ^ 2, fun n hn => by rw [Nat.le_sqrt, ← sq]; exact hn⟩
      exact tendsto_sum_moebius_div_sq.comp (hsqrt.comp hfloor)
    have herr_lim : Tendsto (fun X : ℝ =>
        (4 * C_sq + C_log) * (Real.log X + 1) ^ 3 / (Real.log X) ^ 4) atTop (𝓝 0) := by
      have hinv : Tendsto (fun X : ℝ => 1 / Real.log X) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
      have h1 : Tendsto (fun X : ℝ => (1 + 1 / Real.log X) ^ 3) atTop (𝓝 1) := by
        have := ((tendsto_const_nhds (x := (1 : ℝ))).add hinv).pow 3
        simpa using this
      have h2 : Tendsto (fun X : ℝ => (4 * C_sq + C_log) * (1 + 1 / Real.log X) ^ 3 * (1 / Real.log X))
          atTop (𝓝 0) := by
        have := ((h1.const_mul (4 * C_sq + C_log)).mul hinv)
        simpa using this
      refine h2.congr' ?_
      filter_upwards [eventually_gt_atTop (Real.exp 1)] with X hX
      have hlog_pos : 0 < Real.log X := by
        have := Real.log_lt_log (Real.exp_pos 1) hX
        rw [Real.log_exp] at this; linarith
      field_simp [hlog_pos.ne']
    have hmain_lim : Tendsto (fun X : ℝ => (M (Nat.sqrt ⌊X⌋₊) / 24) / (1 / (4 * Real.pi ^ 2)))
        atTop (𝓝 1) := by
      have h1 := (hM_lim.div_const 24).div_const (1 / (4 * Real.pi ^ 2))
      have hval : (6 / Real.pi ^ 2 / 24) / (1 / (4 * Real.pi ^ 2)) = 1 := by
        field_simp [Real.pi_ne_zero]; norm_num
      rwa [hval] at h1
    have herr_scaled : Tendsto (fun X : ℝ =>
        ((4 * C_sq + C_log) * (Real.log X + 1) ^ 3 / (Real.log X) ^ 4) / (1 / (4 * Real.pi ^ 2)))
        atTop (𝓝 0) := by
      have h0 : (0 : ℝ) / (1 / (4 * Real.pi ^ 2)) = 0 := zero_div _
      rw [← h0]
      exact herr_lim.div_const (1 / (4 * Real.pi ^ 2))
    rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨X₁, hX₁⟩ := Metric.tendsto_atTop.mp hmain_lim (ε / 2) (by linarith)
    obtain ⟨X₂, hX₂⟩ := Metric.tendsto_atTop.mp herr_scaled (ε / 2) (by linarith)
    refine ⟨max (max X₁ X₂) (Real.exp 1), fun X hX => ?_⟩
    have hXe : Real.exp 1 ≤ X := le_trans (le_max_right _ _) hX
    have hX1 : 1 ≤ X := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hXe
    have hlog1 : 1 ≤ Real.log X := by
      have := Real.log_le_log (Real.exp_pos 1) hXe
      rwa [Real.log_exp] at this
    have hlog_pos : 0 < Real.log X := by linarith
    have hden_pos : 0 < (1 / (4 * Real.pi ^ 2)) * Real.log X ^ 4 := by positivity
    -- Bound |∑ d(n)^2/n - (M K / 24) * (log X)^4|
    set K := Nat.sqrt ⌊X⌋₊
    have hdiff : |(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 / (n : ℝ)) -
        (M K / 24) * Real.log X ^ 4| ≤ (4 * C_sq + C_log) * (Real.log X + 1) ^ 3 := by
      rw [sum_d2sq_eq_sum_moebius_harmSum_d4 (by linarith)]
      have hrew : (M K / 24) * Real.log X ^ 4 =
          ∑ k ∈ Finset.Icc 1 K, ((μ k : ℝ) / (k : ℝ) ^ 2) * (Real.log X ^ 4 / 24) := by
        dsimp only [M]
        rw [Finset.sum_div, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => by ring
      rw [hrew, ← Finset.sum_sub_distrib]
      have hmu_le : ∀ k : ℕ, |(μ k : ℝ)| ≤ 1 := by
        intro k
        have h1 : |μ k| ≤ 1 := by
          by_cases hsf : Squarefree k
          · rw [ArithmeticFunction.moebius_apply_of_squarefree hsf]; simp
          · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; simp
        exact_mod_cast h1
      calc |∑ k ∈ Finset.Icc 1 K,
              (((μ k : ℝ) / (k : ℝ) ^ 2) * harmSum (fun m => (d4 m : ℝ)) (X / (k : ℝ) ^ 2) -
                ((μ k : ℝ) / (k : ℝ) ^ 2) * (Real.log X ^ 4 / 24))|
          ≤ ∑ k ∈ Finset.Icc 1 K,
              |((μ k : ℝ) / (k : ℝ) ^ 2) *
                (harmSum (fun m => (d4 m : ℝ)) (X / (k : ℝ) ^ 2) - Real.log X ^ 4 / 24)| := by
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
            rw [← mul_sub]
        _ ≤ ∑ k ∈ Finset.Icc 1 K, (1 / (k : ℝ) ^ 2) *
              (4 * (Real.log X + 1) ^ 3 + Real.log (k : ℝ) * (Real.log X + 1) ^ 3) := by
            refine Finset.sum_le_sum fun k hk => ?_
            have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
            have hkK : k ≤ K := (Finset.mem_Icc.mp hk).2
            have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
            have hk2_le_X : (k : ℝ) ^ 2 ≤ X := by
              have hnat : k ^ 2 ≤ ⌊X⌋₊ := by
                have := Nat.mul_le_mul hkK hkK
                rw [← sq] at this
                exact le_trans this (Nat.sqrt_le ⌊X⌋₊)
              exact le_trans (by exact_mod_cast hnat) (Nat.floor_le (by linarith))
            have hXk : 1 ≤ X / (k : ℝ) ^ 2 := (one_le_div (by positivity)).mpr hk2_le_X
            rw [abs_mul, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (k : ℝ) ^ 2)]
            refine mul_le_mul (div_le_div_of_nonneg_right (hmu_le k) (by positivity)) ?_
              (abs_nonneg _) (by positivity)
            have h4b := harmSum_d4_bound hXk
            have hlog_sub : Real.log (X / (k : ℝ) ^ 2) = Real.log X - 2 * Real.log (k : ℝ) := by
              rw [Real.log_div (by linarith) (by positivity), Real.log_pow]; ring
            have hlog_k_nn : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast hk1)
            have hlog_sub_nn : 0 ≤ Real.log X - 2 * Real.log (k : ℝ) := by
              rw [← hlog_sub]; exact Real.log_nonneg hXk
            have hpow_diff : |(Real.log (X / (k : ℝ) ^ 2)) ^ 4 / 24 - Real.log X ^ 4 / 24| ≤
                Real.log (k : ℝ) * (Real.log X + 1) ^ 3 := by
              rw [hlog_sub]
              set a := Real.log X
              set b := 2 * Real.log (k : ℝ)
              have hab_le : a - b ≤ a := by linarith
              have hdiff_eq : a ^ 4 - (a - b) ^ 4 =
                  b * (a ^ 3 + a ^ 2 * (a - b) + a * (a - b) ^ 2 + (a - b) ^ 3) := by ring
              have hnn : 0 ≤ a ^ 4 - (a - b) ^ 4 := by
                have := pow_le_pow_left₀ hlog_sub_nn hab_le 4; linarith
              have hub : a ^ 4 - (a - b) ^ 4 ≤ 4 * b * a ^ 3 := by
                rw [hdiff_eq]
                have h1 : a ^ 2 * (a - b) ≤ a ^ 3 := by nlinarith
                have h2 : a * (a - b) ^ 2 ≤ a ^ 3 := by
                  have : (a - b) ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hlog_sub_nn hab_le 2
                  nlinarith
                have h3 : (a - b) ^ 3 ≤ a ^ 3 := pow_le_pow_left₀ hlog_sub_nn hab_le 3
                nlinarith
              rw [← sub_div, abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 24),
                abs_sub_comm, abs_of_nonneg hnn]
              have ha3 : a ^ 3 ≤ (a + 1) ^ 3 := pow_le_pow_left₀ hlog_pos.le (by linarith) 3
              nlinarith
            have hlog_mono : Real.log (X / (k : ℝ) ^ 2) + 1 ≤ Real.log X + 1 := by
              rw [hlog_sub]; linarith
            have h4b' : |harmSum (fun m => (d4 m : ℝ)) (X / (k : ℝ) ^ 2) -
                (Real.log (X / (k : ℝ) ^ 2)) ^ 4 / 24| ≤ 4 * (Real.log X + 1) ^ 3 := by
              refine h4b.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
              exact pow_le_pow_left₀ (by linarith [Real.log_nonneg hXk]) hlog_mono 3
            calc |harmSum (fun m => (d4 m : ℝ)) (X / (k : ℝ) ^ 2) - Real.log X ^ 4 / 24|
                = |(harmSum (fun m => (d4 m : ℝ)) (X / (k : ℝ) ^ 2) -
                      (Real.log (X / (k : ℝ) ^ 2)) ^ 4 / 24) +
                    ((Real.log (X / (k : ℝ) ^ 2)) ^ 4 / 24 - Real.log X ^ 4 / 24)| := by ring_nf
              _ ≤ |harmSum (fun m => (d4 m : ℝ)) (X / (k : ℝ) ^ 2) -
                      (Real.log (X / (k : ℝ) ^ 2)) ^ 4 / 24| +
                    |(Real.log (X / (k : ℝ) ^ 2)) ^ 4 / 24 - Real.log X ^ 4 / 24| := abs_add_le _ _
              _ ≤ 4 * (Real.log X + 1) ^ 3 + Real.log (k : ℝ) * (Real.log X + 1) ^ 3 :=
                  add_le_add h4b' hpow_diff
        _ = (4 * (∑ k ∈ Finset.Icc 1 K, (1 : ℝ) / (k : ℝ) ^ 2) +
              ∑ k ∈ Finset.Icc 1 K, Real.log (k : ℝ) / (k : ℝ) ^ 2) * (Real.log X + 1) ^ 3 := by
            simp_rw [mul_add, Finset.sum_add_distrib]
            rw [add_mul]
            congr 1
            · rw [← Finset.sum_mul]; ring
            · rw [Finset.sum_mul]
              refine Finset.sum_congr rfl fun k _ => by ring
        _ ≤ (4 * C_sq + C_log) * (Real.log X + 1) ^ 3 := by
            refine mul_le_mul_of_nonneg_right (add_le_add ?_ ?_) (by positivity)
            · refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
              dsimp only [C_sq]
              rw [← hasSum_zeta_two.tsum_eq]
              exact Summable.sum_le_tsum (Finset.Icc 1 K) (fun _ _ => by positivity) summable_one_div_sq
            · dsimp only [C_log]
              refine Summable.sum_le_tsum (Finset.Icc 1 K) (fun k _ => ?_) summable_log_div_sq
              cases k with
              | zero => simp
              | succ m => exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m + 1))) (by positivity)
    rw [Real.dist_eq]
    dsimp only [Pi.div_apply]
    have hsplit_q :
        (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 / (n : ℝ)) /
            ((1 / (4 * Real.pi ^ 2)) * Real.log X ^ 4) - 1 =
        ((∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 / (n : ℝ)) -
            (M K / 24) * Real.log X ^ 4) / ((1 / (4 * Real.pi ^ 2)) * Real.log X ^ 4) +
        ((M K / 24) / (1 / (4 * Real.pi ^ 2)) - 1) := by
      field_simp [hden_pos.ne', hlog_pos.ne', Real.pi_ne_zero]
      ring
    rw [hsplit_q]
    have hterm1 : |((∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 / (n : ℝ)) -
        (M K / 24) * Real.log X ^ 4) / ((1 / (4 * Real.pi ^ 2)) * Real.log X ^ 4)| < ε / 2 := by
      rw [abs_div, abs_of_pos hden_pos]
      have hle : |(∑ n ∈ Finset.Icc 1 ⌊X⌋₊, ((ArithmeticFunction.sigma 0 n : ℕ) : ℝ) ^ 2 / (n : ℝ)) -
          (M K / 24) * Real.log X ^ 4| / ((1 / (4 * Real.pi ^ 2)) * Real.log X ^ 4) ≤
          ((4 * C_sq + C_log) * (Real.log X + 1) ^ 3 / (Real.log X) ^ 4) / (1 / (4 * Real.pi ^ 2)) := by
        have hrew : ((4 * C_sq + C_log) * (Real.log X + 1) ^ 3 / (Real.log X) ^ 4) / (1 / (4 * Real.pi ^ 2)) =
            ((4 * C_sq + C_log) * (Real.log X + 1) ^ 3) / ((1 / (4 * Real.pi ^ 2)) * Real.log X ^ 4) := by
          field_simp [hlog_pos.ne', Real.pi_ne_zero]
        rw [hrew]
        exact div_le_div_of_nonneg_right hdiff hden_pos.le
      have h2 := hX₂ X (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX)
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (by
        have hC_log_nn : 0 ≤ C_log := tsum_nonneg fun k => by
          cases k with
          | zero => simp
          | succ m => exact div_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m + 1))) (by positivity)
        positivity)] at h2
      exact lt_of_le_of_lt hle h2
    have hterm2 : |(M K / 24) / (1 / (4 * Real.pi ^ 2)) - 1| < ε / 2 := by
      have h1 := hX₁ X (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX)
      rwa [Real.dist_eq] at h1
    exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    have hlog : 0 < Real.log X := Real.log_pos hX
    exact fun h => absurd h (by positivity)

end ZetaMomentsH3Proof

theorem OMA.solution : OMA.R_RiemannZetaMoments_moment_isEquiv_83_R1.H3 :=
  ZetaMomentsH3Proof.main_H3
