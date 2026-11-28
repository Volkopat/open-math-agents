import OMAReductions.R_Erdos67_erdos_67_R1
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Reduction of `Erdos67.erdos_67.R1.H2` (Tao's Generalized Borwein–Choi–Coons Theorem)

Following Section 4 of Terence Tao, *The Erdős discrepancy problem*, Discrete Anal. (2016),
Paper No. 1 (`arXiv:1509.05363`), we reduce `OMA.R_Erdos67_erdos_67_R1.H2` to two canonical
theorems in analytic and multiplicative number theory:

1. (`H1`) **Vinogradov–Korobov pretentious repulsion for Dirichlet characters**: for any
   `Q ≥ 1`, `δ ∈ (0, 1)`, and `M ≥ 0`, once `X` is sufficiently large, any two Dirichlet
   characters `χ (mod q)` and `χ' (mod q')` of moduli `≤ Q` and shifts `t, t'` with
   `X^δ ≤ |t' - t| ≤ 2 Q X` have pretentious distance `> M` over primes `p ≤ ⌊X^δ⌋`.
2. (`H2`) **Euler-product equidistribution of 1-pretentious multiplicative functions in
   arithmetic progressions**: for any `Q ≥ 1`, there exists `c > 0` such that for any
   `1 ≤ q ≤ Q`, `k ≥ 1`, and `η > 0`, once `X` is sufficiently large, any `S¹`-valued
   completely multiplicative function `h` with `h(p) = 1` for `p ∣ q` and
   `∑_{p ≤ X} (1 - Re h(p)) / p ≤ Q` satisfies
   `∑_{n ≡ b (mod q^k)} h(n) / n^{1 + 1/log X} = S / q^k + O(η (log X) / q^k)`
   for some `S : ℂ` with `‖S‖ ≥ c log X`.

Inside `main`, we prove all remaining steps of Tao's Section 4 completely from scratch:
- Lemma 4.1 (`t`-tightening) from `H1` and the exact pointwise pretentious triangle inequality.
- Elimination of the probability measure `μ` via `lintegral_tsum` and Markov's inequality on
  the continuous `n^{-(1 + 1/log X)}`-weighted short-sum energy.
- Primitive character reduction (`χ ↦ χ.primitiveCharacter`), factorization
  `g(n) = χ̃(n) n^{it} h(n)`, elimination of `n^{it}`, and decoupling over good residue classes
  modulo `q^k` via Cauchy–Schwarz and `H2`.
- Elimination of the `q = 1` case, reinstatement of bad residue classes, Granville's exact
  off-diagonal cancellation (`d₁ ≠ d₂`) via elementary `p`-orbit invariance under
  `Δ = (lcm(d₁, d₂) / p) * q`, and the `d = q^i` diagonal lower bound giving a contradiction
  for large `H`.
-/

-- Reduction Erdos67.erdos_67.R1.H2.R1 of Erdos67.erdos_67.R1.H2
-- Credit: @tkaiman
-- Each H becomes its own step once this file is accepted. Proving all of them closes the step.

open Filter Finset MeasureTheory Complex
open scoped Topology Classical BigOperators

namespace OMA.R_Erdos67_erdos_67_R1_H2_R1

/- ### Helper 1: Basic properties of `mulEval` and completely multiplicative functions -/

private lemma mulEval_mul (z : ℕ → Metric.sphere (0 : ℂ) 1) (a b : ℕ) :
    (if a * b = 0 then (0 : ℂ) else (a * b).factorization.prod fun p e => (z p).1 ^ e) =
      (if a = 0 then (0 : ℂ) else a.factorization.prod fun p e => (z p).1 ^ e) *
      (if b = 0 then (0 : ℂ) else b.factorization.prod fun p e => (z p).1 ^ e) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  simp only [ha, hb, hab, ↓reduceIte, Nat.factorization_mul ha hb]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

private lemma mulEval_prime (z : ℕ → Metric.sphere (0 : ℂ) 1) {p : ℕ} (hp : p.Prime) :
    (if p = 0 then (0 : ℂ) else p.factorization.prod fun q e => (z q).1 ^ e) = (z p).1 := by
  rw [if_neg hp.ne_zero, hp.factorization]
  simp [Finsupp.prod_single_index]

private lemma mulEval_norm (z : ℕ → Metric.sphere (0 : ℂ) 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖if n = 0 then (0 : ℂ) else n.factorization.prod fun p e => (z p).1 ^ e‖ = 1 := by
  rw [if_neg (by omega : n ≠ 0), Finsupp.prod, norm_prod]
  exact Finset.prod_eq_one fun p _ => by
    rw [norm_pow, mem_sphere_zero_iff_norm.mp (z p).2, one_pow]

private lemma mulEval_continuous (n : ℕ) :
    Continuous (fun z : ℕ → Metric.sphere (0 : ℂ) 1 =>
      if n = 0 then (0 : ℂ) else n.factorization.prod fun p e => (z p).1 ^ e) := by
  by_cases hn : n = 0
  · simp [hn]; exact continuous_const
  · simp only [hn, ↓reduceIte, Finsupp.prod]
    exact continuous_finsetProd _ fun p _ =>
      (continuous_subtype_val.comp (continuous_apply p)).pow _

private lemma cMul_of_prime_mul (f : ℕ → ℂ) (a b : ℕ) :
    (if a * b = 0 then (0 : ℂ) else (a * b).factorization.prod fun p e => f p ^ e) =
      (if a = 0 then (0 : ℂ) else a.factorization.prod fun p e => f p ^ e) *
      (if b = 0 then (0 : ℂ) else b.factorization.prod fun p e => f p ^ e) := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have hab : a * b ≠ 0 := mul_ne_zero ha hb
  simp only [ha, hb, hab, ↓reduceIte, Nat.factorization_mul ha hb]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

private lemma cMul_of_prime_norm (f : ℕ → ℂ) (hf : ∀ p, p.Prime → ‖f p‖ = 1)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖if n = 0 then (0 : ℂ) else n.factorization.prod fun p e => f p ^ e‖ = 1 := by
  rw [if_neg (by omega : n ≠ 0), Finsupp.prod, norm_prod]
  refine Finset.prod_eq_one fun p hp => ?_
  rw [norm_pow, hf p (Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mp hp |> fun h =>
    Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primeFactors (by
      rwa [Nat.support_factorization] at hp), Nat.dvd_of_mem_primeFactors (by
      rwa [Nat.support_factorization] at hp), by omega⟩)), one_pow]

private lemma cMul_of_prime_apply_prime (f : ℕ → ℂ) {p : ℕ} (hp : p.Prime) :
    (if p = 0 then (0 : ℂ) else p.factorization.prod fun q e => f q ^ e) = f p := by
  rw [if_neg hp.ne_zero, hp.factorization]
  simp [Finsupp.prod_single_index]

private lemma cMul_of_prime_eq_of_eq_on_primes (f g : ℕ → ℂ)
    (hfg : ∀ p, p.Prime → f p = g p) (n : ℕ) :
    (if n = 0 then (0 : ℂ) else n.factorization.prod fun p e => f p ^ e) =
      (if n = 0 then (0 : ℂ) else n.factorization.prod fun p e => g p ^ e) := by
  by_cases hn : n = 0
  · simp [hn]
  simp only [hn, ↓reduceIte, Finsupp.prod]
  refine Finset.prod_congr rfl fun p hp => ?_
  rw [Nat.support_factorization] at hp
  rw [hfg p (Nat.prime_of_mem_primeFactors hp)]

private lemma dirichlet_norm_eq_one_of_coprime {q : ℕ} (χ : DirichletCharacter ℂ q)
    {n : ℕ} (hn : Nat.Coprime n q) : ‖χ (n : ZMod q)‖ = 1 := by
  by_cases hq : q = 0
  · subst hq
    have hn1 : n = 1 := by simpa [Nat.Coprime] using hn
    subst hn1; simp
  · have : NeZero q := ⟨hq⟩
    have hu : IsUnit (n : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hn
    obtain ⟨u, hu'⟩ := hu
    rw [← hu']
    have hpow : χ (u : ZMod q) ^ Fintype.card (ZMod q)ˣ = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
    have hnorm : ‖χ (u : ZMod q)‖ ^ Fintype.card (ZMod q)ˣ = 1 := by
      rw [← norm_pow, hpow, norm_one]
    have hpos : 0 < Fintype.card (ZMod q)ˣ := Fintype.card_pos
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg (χ (u : ZMod q))) hpos.ne').mp hnorm

private lemma dirichlet_norm_le_one {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    ‖χ a‖ ≤ 1 := by
  by_cases hu : IsUnit a
  · obtain ⟨u, rfl⟩ := hu
    by_cases hq : q = 0
    · subst hq
      have hsq : u ^ 2 = 1 := by
        rcases Int.units_eq_one_or (u : ℤˣ) with h | h <;> (rw [h]; decide)
      have hsq' : (u : ZMod 0) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, hsq, Units.val_one]
      have : ‖χ (u : ZMod 0)‖ ^ 2 = 1 := by rw [← norm_pow, ← map_pow, hsq', map_one, norm_one]
      nlinarith [norm_nonneg (χ (u : ZMod 0))]
    · have : NeZero q := ⟨hq⟩
      have hpow : χ (u : ZMod q) ^ Fintype.card (ZMod q)ˣ = 1 := by
        rw [← map_pow, ← Units.val_pow_eq_pow_val, pow_card_eq_one, Units.val_one, map_one]
      have hnorm : ‖χ (u : ZMod q)‖ ^ Fintype.card (ZMod q)ˣ = 1 := by
        rw [← norm_pow, hpow, norm_one]
      have hpos : 0 < Fintype.card (ZMod q)ˣ := Fintype.card_pos
      have heq := (pow_eq_one_iff_of_nonneg (norm_nonneg (χ (u : ZMod q))) hpos.ne').mp hnorm
      linarith
  · rw [MulChar.map_nonunit χ hu, norm_zero]; norm_num

private lemma dirichlet_apply_eq_zero_of_dvd {q : ℕ} (_hq : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) (hdvd : p ∣ q) : χ (p : ZMod q) = 0 := by
  have : NeZero q := ⟨by omega⟩
  apply MulChar.map_nonunit
  rw [ZMod.isUnit_iff_coprime]
  intro hc
  have : p ∣ Nat.gcd p q := Nat.dvd_gcd dvd_rfl hdvd
  rw [hc.gcd_eq_one] at this
  exact hp.not_dvd_one this

/- ### Helper 2: Pointwise pretentious triangle inequality & primitive reduction -/

private lemma norm_exp_I_mul_real (r : ℝ) : ‖Complex.exp (Complex.I * r)‖ = 1 := by
  rw [mul_comm]; exact Complex.norm_exp_ofReal_mul_I r

private lemma norm_exp_neg_I_mul_real (r : ℝ) : ‖Complex.exp (-Complex.I * r)‖ = 1 := by
  have : (-Complex.I * (r : ℂ)) = ((-r : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private lemma pretentious_term_nonneg {w u : ℂ} (hw : ‖w‖ ≤ 1) (hu : ‖u‖ ≤ 1) :
    0 ≤ 1 - (w * u).re := by
  have h1 : (w * u).re ≤ ‖w * u‖ := Complex.re_le_norm _
  have h2 : ‖w * u‖ ≤ 1 := by
    rw [norm_mul]
    exact mul_le_one₀ hw (norm_nonneg u) hu
  linarith

private lemma pretentious_triangle_unit {u v w : ℂ} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1) :
    1 - (u * star v).re ≤ 2 * (1 - (w * star u).re) + 2 * (1 - (w * star v).re) := by
  have hid : ∀ x y : ℂ, ‖x‖ = 1 → ‖y‖ = 1 → ‖x - y‖ ^ 2 = 2 * (1 - (x * star y).re) := by
    intro x y hx hy
    have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    rw [hsq (x - y)]
    have hx2 : x.re ^ 2 + x.im ^ 2 = 1 := by rw [← hsq x, hx, one_pow]
    have hy2 : y.re ^ 2 + y.im ^ 2 = 1 := by rw [← hsq y, hy, one_pow]
    simp only [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.star_def,
      Complex.conj_re, Complex.conj_im]
    nlinarith
  have htri : ‖u - v‖ ≤ ‖w - u‖ + ‖w - v‖ := by
    calc ‖u - v‖ = ‖(w - v) - (w - u)‖ := by ring_nf
      _ ≤ ‖w - v‖ + ‖w - u‖ := norm_sub_le _ _
      _ = ‖w - u‖ + ‖w - v‖ := add_comm _ _
  have hsq : ‖u - v‖ ^ 2 ≤ 2 * ‖w - u‖ ^ 2 + 2 * ‖w - v‖ ^ 2 := by
    have h1 : ‖u - v‖ ^ 2 ≤ (‖w - u‖ + ‖w - v‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [sq_nonneg (‖w - u‖ - ‖w - v‖)]
  rw [hid u v hu hv, hid w u hw hu, hid w v hw hv] at hsq
  linarith

private lemma pretentious_triangle_pointwise {q q' : ℕ} (hq : 1 ≤ q) (hq' : 1 ≤ q')
    (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q') (t t' : ℝ)
    (g : ℂ) (hg : ‖g‖ = 1) {p : ℕ} (hp : p.Prime) :
    1 - (χ (p : ZMod q) * star (χ' (p : ZMod q')) *
      Complex.exp (-Complex.I * (t' - t) * Real.log (p : ℝ))).re ≤
    2 * (1 - (g * star (χ (p : ZMod q)) * Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) +
    2 * (1 - (g * star (χ' (p : ZMod q')) * Complex.exp (-Complex.I * t' * Real.log (p : ℝ))).re) := by
  have he1 : ‖Complex.exp (-Complex.I * t * Real.log (p : ℝ))‖ = 1 := by
    have : (-Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ)) =
        -Complex.I * ((t * Real.log (p : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact norm_exp_neg_I_mul_real _
  have he2 : ‖Complex.exp (-Complex.I * t' * Real.log (p : ℝ))‖ = 1 := by
    have : (-Complex.I * (t' : ℂ) * (Real.log (p : ℝ) : ℂ)) =
        -Complex.I * ((t' * Real.log (p : ℝ) : ℝ) : ℂ) := by push_cast; ring
    rw [this]; exact norm_exp_neg_I_mul_real _
  have ht1 : 0 ≤ 1 - (g * star (χ (p : ZMod q)) *
      Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re := by
    rw [mul_assoc]
    refine pretentious_term_nonneg (le_of_eq hg) ?_
    rw [norm_mul, norm_star, he1, mul_one]; exact dirichlet_norm_le_one χ _
  have ht2 : 0 ≤ 1 - (g * star (χ' (p : ZMod q')) *
      Complex.exp (-Complex.I * t' * Real.log (p : ℝ))).re := by
    rw [mul_assoc]
    refine pretentious_term_nonneg (le_of_eq hg) ?_
    rw [norm_mul, norm_star, he2, mul_one]; exact dirichlet_norm_le_one χ' _
  by_cases hd1 : p ∣ q
  · rw [dirichlet_apply_eq_zero_of_dvd hq χ hp hd1]
    simp only [zero_mul, star_zero, mul_zero, Complex.zero_re, sub_zero]
    linarith
  by_cases hd2 : p ∣ q'
  · rw [dirichlet_apply_eq_zero_of_dvd hq' χ' hp hd2]
    simp only [star_zero, mul_zero, zero_mul, Complex.zero_re, sub_zero]
    linarith
  have hc1 : Nat.Coprime p q := (hp.coprime_iff_not_dvd).mpr hd1
  have hc2 : Nat.Coprime p q' := (hp.coprime_iff_not_dvd).mpr hd2
  set u : ℂ := χ (p : ZMod q) * Complex.exp (Complex.I * ((t * Real.log (p : ℝ) : ℝ) : ℂ))
  set v : ℂ := χ' (p : ZMod q') * Complex.exp (Complex.I * ((t' * Real.log (p : ℝ) : ℝ) : ℂ))
  have hu : ‖u‖ = 1 := by
    dsimp [u]
    rw [norm_mul, dirichlet_norm_eq_one_of_coprime χ hc1, norm_exp_I_mul_real, one_mul]
  have hv : ‖v‖ = 1 := by
    dsimp [v]
    rw [norm_mul, dirichlet_norm_eq_one_of_coprime χ' hc2, norm_exp_I_mul_real, one_mul]
  have hstar_exp : ∀ r : ℝ,
      star (Complex.exp (Complex.I * (r : ℂ))) = Complex.exp (-Complex.I * (r : ℂ)) := by
    intro r
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1; simp
  have huv : u * star v = χ (p : ZMod q) * star (χ' (p : ZMod q')) *
      Complex.exp (-Complex.I * (t' - t) * Real.log (p : ℝ)) := by
    simp only [u, v, star_mul', hstar_exp]
    have hmul : Complex.exp (Complex.I * ((t * Real.log (p : ℝ) : ℝ) : ℂ)) *
        Complex.exp (-Complex.I * ((t' * Real.log (p : ℝ) : ℝ) : ℂ)) =
        Complex.exp (-Complex.I * (t' - t) * Real.log (p : ℝ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    calc χ (p : ZMod q) * Complex.exp (Complex.I * ((t * Real.log (p : ℝ) : ℝ) : ℂ)) *
          (star (χ' (p : ZMod q')) * Complex.exp (-Complex.I * ((t' * Real.log (p : ℝ) : ℝ) : ℂ)))
        = χ (p : ZMod q) * star (χ' (p : ZMod q')) *
          (Complex.exp (Complex.I * ((t * Real.log (p : ℝ) : ℝ) : ℂ)) *
            Complex.exp (-Complex.I * ((t' * Real.log (p : ℝ) : ℝ) : ℂ))) := by ring
      _ = _ := by rw [hmul]
  have hwu : g * star u = g * star (χ (p : ZMod q)) *
      Complex.exp (-Complex.I * t * Real.log (p : ℝ)) := by
    simp only [u, star_mul', hstar_exp]
    have : (-Complex.I * ((t * Real.log (p : ℝ) : ℝ) : ℂ)) =
        -Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ) := by push_cast; ring
    rw [this]; ring
  have hwv : g * star v = g * star (χ' (p : ZMod q')) *
      Complex.exp (-Complex.I * t' * Real.log (p : ℝ)) := by
    simp only [v, star_mul', hstar_exp]
    have : (-Complex.I * ((t' * Real.log (p : ℝ) : ℝ) : ℂ)) =
        -Complex.I * (t' : ℂ) * (Real.log (p : ℝ) : ℂ) := by push_cast; ring
    rw [this]; ring
  rw [← huv, ← hwu, ← hwv]
  exact pretentious_triangle_unit hu hv hg

/- ### Helper 3: `p`-series and elementary complex exponential estimates -/

private lemma norm_exp_I_sub_one_le (θ : ℝ) : ‖Complex.exp (Complex.I * θ) - 1‖ ≤ |θ| := by
  have hsq : ‖Complex.exp (Complex.I * θ) - 1‖ ^ 2 = (2 * Real.sin (θ / 2)) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hexp : Complex.exp (Complex.I * (θ : ℂ)) = Complex.cos θ + Complex.sin θ * Complex.I := by
      rw [mul_comm, Complex.exp_mul_I]
    rw [hexp]
    have hre : ((Complex.cos θ + Complex.sin θ * Complex.I - 1 : ℂ)).re = Real.cos θ - 1 := by
      simp [Complex.cos_ofReal_re, Complex.sin_ofReal_im]
    have him : ((Complex.cos θ + Complex.sin θ * Complex.I - 1 : ℂ)).im = Real.sin θ := by
      simp [Complex.cos_ofReal_im, Complex.sin_ofReal_re]
    rw [hre, him]
    have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
      have h2 := Real.cos_two_mul' (θ / 2)
      have hsc := Real.sin_sq_add_cos_sq (θ / 2)
      have harg : 2 * (θ / 2) = θ := by ring
      rw [harg] at h2
      linarith
    have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
      have h2 := Real.sin_two_mul (θ / 2)
      have harg : 2 * (θ / 2) = θ := by ring
      rw [harg] at h2; exact h2
    have hsc := Real.sin_sq_add_cos_sq (θ / 2)
    rw [hcos, hsin]
    nlinarith
  have hsin_le : |2 * Real.sin (θ / 2)| ≤ |θ| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have := Real.abs_sin_le_abs (x := θ / 2)
    rw [abs_div, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at this
    linarith
  have hsq_le : ‖Complex.exp (Complex.I * θ) - 1‖ ^ 2 ≤ |θ| ^ 2 := by
    rw [hsq, ← sq_abs (2 * Real.sin (θ / 2))]
    exact pow_le_pow_left₀ (abs_nonneg _) hsin_le 2
  nlinarith [norm_nonneg (Complex.exp (Complex.I * θ) - 1), abs_nonneg θ]

private lemma norm_cpow_shift_sub_le (t : ℝ) {n m : ℕ} (hn : 1 ≤ n) :
    ‖Complex.exp (Complex.I * t * Real.log ((n + m : ℕ) : ℝ)) -
      Complex.exp (Complex.I * t * Real.log (n : ℝ))‖ ≤ |t| * (m : ℝ) / (n : ℝ) := by
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hnm_pos : (0 : ℝ) < ((n + m : ℕ) : ℝ) := by exact_mod_cast (show 0 < n + m by omega)
  have hdiff : Complex.exp (Complex.I * t * Real.log ((n + m : ℕ) : ℝ)) -
      Complex.exp (Complex.I * t * Real.log (n : ℝ)) =
      Complex.exp (Complex.I * ((t * Real.log (n : ℝ) : ℝ) : ℂ)) *
        (Complex.exp (Complex.I * ((t * Real.log (((n + m : ℕ) : ℝ) / (n : ℝ)) : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    congr 1
    · congr 1
      rw [Real.log_div hnm_pos.ne' hn_pos.ne']
      push_cast; ring
    · push_cast; ring
  rw [hdiff, norm_mul, norm_exp_I_mul_real, one_mul]
  calc ‖Complex.exp (Complex.I * ((t * Real.log (((n + m : ℕ) : ℝ) / (n : ℝ)) : ℝ) : ℂ)) - 1‖
      ≤ |t * Real.log (((n + m : ℕ) : ℝ) / (n : ℝ))| := norm_exp_I_sub_one_le _
    _ = |t| * |Real.log (((n + m : ℕ) : ℝ) / (n : ℝ))| := abs_mul _ _
    _ = |t| * Real.log (((n + m : ℕ) : ℝ) / (n : ℝ)) := by
        rw [abs_of_nonneg (Real.log_nonneg (by
          rw [one_le_div hn_pos]; push_cast; linarith))]
    _ ≤ |t| * (((n + m : ℕ) : ℝ) / (n : ℝ) - 1) := by
        gcongr
        exact Real.log_le_sub_one_of_pos (div_pos hnm_pos hn_pos)
    _ = |t| * (m : ℝ) / (n : ℝ) := by
        push_cast; field_simp [hn_pos.ne']; ring

private lemma summable_one_div_succ_rpow {s : ℝ} (hs : 0 < s) :
    Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (1 + s)) := by
  have h : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ (1 + s)) :=
    Real.summable_one_div_nat_rpow.mpr (by linarith)
  exact (summable_nat_add_iff 1).mpr h

private lemma tsum_inv_rpow_le {s : ℝ} (hs : 0 < s) :
    (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (1 + s)) ≤ 1 + 2 / s := by
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (1 + s)) :=
    summable_one_div_succ_rpow hs
  -- Use Cauchy condensation on `ENNReal` via `ENNReal.le_tsum_condensed`
  let f : ℕ → ENNReal := fun n =>
    if n = 0 then 0 else ENNReal.ofReal ((1 : ℝ) / (n : ℝ) ^ (1 + s))
  have hf_mono : ∀ ⦃m n : ℕ⦄, 0 < m → m ≤ n → f n ≤ f m := by
    intro m n hm hmn
    have hn : n ≠ 0 := by omega
    have hm0 : m ≠ 0 := by omega
    simp only [f, hn, hm0, ↓reduceIte]
    apply ENNReal.ofReal_le_ofReal
    apply one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by exact_mod_cast hm) _)
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hmn) (by linarith)
  have hcond := ENNReal.le_tsum_condensed hf_mono
  have hcond0 : f 0 = 0 := by simp [f]
  rw [hcond0, zero_add] at hcond
  have hgeom_r : (0 : ℝ) ≤ (2 : ℝ) ^ (-s) ∧ (2 : ℝ) ^ (-s) < 1 := by
    refine ⟨by positivity, ?_⟩
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    rw [inv_lt_one_iff₀]; right
    exact Real.one_lt_rpow (by norm_num) hs
  have hterm : ∀ k : ℕ, (2 : ENNReal) ^ k * f (2 ^ k) =
      ENNReal.ofReal (((2 : ℝ) ^ (-s)) ^ k) := by
    intro k
    have h2k : (2 ^ k : ℕ) ≠ 0 := pow_ne_zero k two_ne_zero
    simp only [f, h2k, ↓reduceIte]
    rw [show (2 : ENNReal) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [Nat.cast_pow, Nat.cast_two, ← Real.rpow_natCast (2 : ℝ) k,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_natCast ((2 : ℝ) ^ (-s)) k,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), one_div,
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1; ring
  have htsum_rhs : (∑' k : ℕ, (2 : ENNReal) ^ k * f (2 ^ k)) =
      ENNReal.ofReal (1 / (1 - (2 : ℝ) ^ (-s))) := by
    simp_rw [hterm]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => pow_nonneg hgeom_r.1 k)
      (summable_geometric_of_lt_one hgeom_r.1 hgeom_r.2)]
    rw [tsum_geometric_of_lt_one hgeom_r.1 hgeom_r.2, one_div]
  have htsum_lhs : ENNReal.ofReal (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (1 + s)) =
      ∑' n : ℕ, f n := by
    have hsucc : ∑' n : ℕ, f (n + 1) = ∑' n : ℕ, f n :=
      Nat.succ_injective.tsum_eq fun n hn => by
        cases n with
        | zero => exact absurd (by simp [f]) hn
        | succ m => exact ⟨m, rfl⟩
    rw [ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum, ← hsucc]
    refine tsum_congr fun n => ?_
    simp [f]
  rw [← htsum_lhs, htsum_rhs] at hcond
  have hle1 : (∑' n : ℕ, (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (1 + s)) ≤ 1 / (1 - (2 : ℝ) ^ (-s)) := by
    have hpos_rhs : 0 ≤ 1 / (1 - (2 : ℝ) ^ (-s)) := by
      apply div_nonneg zero_le_one; linarith [hgeom_r.2]
    exact (ENNReal.ofReal_le_ofReal_iff hpos_rhs).mp hcond
  -- Bound `1 / (1 - 2^(-s)) ≤ 1 + 2 / s` via `1 + u ≤ exp u`
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by
    have h := Real.log_two_gt_d9
    linarith
  have hu_pos : 0 < s * Real.log 2 := by positivity
  have hexp : 1 + s * Real.log 2 ≤ Real.exp (s * Real.log 2) := by
    linarith [Real.add_one_le_exp (s * Real.log 2)]
  have h2pow : (2 : ℝ) ^ (-s) = (Real.exp (s * Real.log 2))⁻¹ := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_neg]
    congr 1; ring
  have h1sub : s * Real.log 2 / (1 + s * Real.log 2) ≤ 1 - (2 : ℝ) ^ (-s) := by
    rw [h2pow]
    have hexp_pos : 0 < Real.exp (s * Real.log 2) := Real.exp_pos _
    have hinv : (Real.exp (s * Real.log 2))⁻¹ ≤ (1 + s * Real.log 2)⁻¹ :=
      inv_anti₀ (by positivity) hexp
    have hEq : s * Real.log 2 / (1 + s * Real.log 2) = 1 - (1 + s * Real.log 2)⁻¹ := by
      field_simp [(by positivity : (1 + s * Real.log 2) ≠ 0)]; ring
    linarith
  have hdiv_le : 1 / (1 - (2 : ℝ) ^ (-s)) ≤ 1 + 1 / (s * Real.log 2) := by
    have hpos_l : 0 < s * Real.log 2 / (1 + s * Real.log 2) := by positivity
    have h1 := one_div_le_one_div_of_le hpos_l h1sub
    have h2 : 1 / (s * Real.log 2 / (1 + s * Real.log 2)) = 1 + 1 / (s * Real.log 2) := by
      field_simp [hu_pos.ne']; ring
    linarith
  have hlast : 1 / (s * Real.log 2) ≤ 2 / s := by
    rw [div_le_div_iff₀ hu_pos hs]
    nlinarith
  linarith

private lemma sum_inv_rpow_Icc_le {s : ℝ} (hs : 0 < s) (M : ℕ) (hM : 1 ≤ M) :
    (∑ n ∈ Finset.Icc 1 M, (1 : ℝ) / (n : ℝ) ^ (1 + s)) ≤ 1 + 2 * Real.log (M : ℝ) := by
  have h1 : (∑ n ∈ Finset.Icc 1 M, (1 : ℝ) / (n : ℝ) ^ (1 + s)) ≤
      ∑ n ∈ Finset.Icc 1 M, (1 : ℝ) / (n : ℝ) := by
    refine Finset.sum_le_sum fun n hn => ?_
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hn).1
    exact one_div_le_one_div_of_le (by positivity) (by
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ (1 + s) := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith))
  -- Dyadic bound: pick `K` with `M < 2 ^ K` and `2 ^ (K - 1) ≤ M`
  let K : ℕ := Nat.log 2 M + 1
  have hMK : M < 2 ^ K := Nat.lt_pow_succ_log_self (by norm_num) M
  have hsub : Finset.Icc (1 : ℕ) M ⊆ Finset.Ico (1 : ℕ) (2 ^ K) := by
    intro n hn; rw [Finset.mem_Icc] at hn; rw [Finset.mem_Ico]; omega
  have h2 : (∑ n ∈ Finset.Icc (1 : ℕ) M, (1 : ℝ) / (n : ℝ)) ≤
      ∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ K), (1 : ℝ) / (n : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
  have h3 : (∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ K), (1 : ℝ) / (n : ℝ)) ≤ (K : ℝ) := by
    have hc := Finset.le_sum_condensed' (f := fun n : ℕ => (1 : ℝ) / (n : ℝ))
      (fun m n hm hmn => one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast hmn)) K
    have hrhs : (∑ k ∈ Finset.range K, (2 ^ k) • ((1 : ℝ) / ((2 ^ k : ℕ) : ℝ))) = (K : ℝ) := by
      calc (∑ k ∈ Finset.range K, (2 ^ k) • ((1 : ℝ) / ((2 ^ k : ℕ) : ℝ)))
          = ∑ k ∈ Finset.range K, (1 : ℝ) := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [nsmul_eq_mul, mul_one_div_cancel (by positivity)]
        _ = (K : ℝ) := by simp
    linarith
  have hlog : ((Nat.log 2 M : ℕ) : ℝ) ≤ 2 * Real.log (M : ℝ) := by
    have hpow : (2 : ℝ) ^ (Nat.log 2 M) ≤ (M : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : M ≠ 0)
    have hle := Real.log_le_log (by positivity) hpow
    rw [Real.log_pow] at hle
    have hlog2 : (1 : ℝ) / 2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith
  have hK : (K : ℝ) = ((Nat.log 2 M : ℕ) : ℝ) + 1 := by simp [K]
  linarith

/- ### Helper 4: Telescoping shift bound for residue-class Dirichlet series -/

private lemma tsum_ap_shift_sub_le {s : ℝ} (hs : 0 < s) {qK H a m : ℕ}
    (hqK : 1 ≤ qK) (ha : 1 ≤ a) (ha_le : a ≤ qK) (hm1 : 1 ≤ m) (hm2 : m ≤ 2 * H)
    (h : ℕ → ℂ) (hh : ∀ n, 1 ≤ n → ‖h n‖ = 1) :
    ‖(∑' j : ℕ, h (a + (j + 1) * qK + m) /
        Complex.ofReal (((a + (j + 1) * qK : ℕ) : ℝ) ^ (1 + s))) -
      (∑' n : ℕ, if (n + 1) % qK = (a + m) % qK then
        h (n + 1) / Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (1 + s)) else 0)‖ ≤
    4 * (H : ℝ) + 1 := by
  have hsum_base : Summable (fun n : ℕ => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (1 + s)) :=
    summable_one_div_succ_rpow hs
  -- Compare `S1` (indexed by `j : ℕ`, term `a + (j + 1) * qK + m` over `(a + (j+1)*qK)^(1+s)`)
  -- with `S1'` (same numerator, denominator `(a + (j + 1) * qK + m)^(1+s)`),
  -- then compare `S1'` with `S2` (all `n ≥ 1` with `n ≡ a + m (mod qK)`).
  let f1 : ℕ → ℂ := fun j =>
    h (a + (j + 1) * qK + m) / Complex.ofReal (((a + (j + 1) * qK : ℕ) : ℝ) ^ (1 + s))
  let f1' : ℕ → ℂ := fun j =>
    h (a + (j + 1) * qK + m) / Complex.ofReal (((a + (j + 1) * qK + m : ℕ) : ℝ) ^ (1 + s))
  let g2 : ℕ → ℂ := fun n =>
    if (n + 1) % qK = (a + m) % qK then
      h (n + 1) / Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (1 + s)) else 0
  have hf1_norm : ∀ j : ℕ, ‖f1 j‖ = 1 / ((a + (j + 1) * qK : ℕ) : ℝ) ^ (1 + s) := by
    intro j
    dsimp [f1]
    rw [norm_div, hh _ (by omega), Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hf1'_norm : ∀ j : ℕ, ‖f1' j‖ = 1 / ((a + (j + 1) * qK + m : ℕ) : ℝ) ^ (1 + s) := by
    intro j
    dsimp [f1']
    rw [norm_div, hh _ (by omega), Complex.norm_real,
      Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  have hf1_sum : Summable f1 := by
    refine Summable.of_norm_bounded (g := fun j => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (1 + s))
      hsum_base fun j => ?_
    rw [hf1_norm]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_le_rpow (by positivity) (by
        have : j + 1 ≤ a + (j + 1) * qK := by nlinarith
        exact_mod_cast this) (by linarith))
  have hf1'_sum : Summable f1' := by
    refine Summable.of_norm_bounded (g := fun j => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (1 + s))
      hsum_base fun j => ?_
    rw [hf1'_norm]
    exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _)
      (Real.rpow_le_rpow (by positivity) (by
        have : j + 1 ≤ a + (j + 1) * qK + m := by nlinarith
        exact_mod_cast this) (by linarith))
  have hg2_sum : Summable g2 := by
    refine Summable.of_norm_bounded (g := fun n => (1 : ℝ) / ((n + 1 : ℕ) : ℝ) ^ (1 + s))
      hsum_base fun n => ?_
    by_cases hc : (n + 1) % qK = (a + m) % qK
    · dsimp [g2]
      rw [if_pos hc, norm_div, hh _ (by omega), Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
    · simp only [g2, hc, ↓reduceIte, norm_zero]; positivity
  -- Bound 1: `‖∑' f1 - ∑' f1'‖ ≤ 2 * H` by telescoping
  have hB1 : ‖(∑' j, f1 j) - (∑' j, f1' j)‖ ≤ 2 * (H : ℝ) := by
    rw [← hf1_sum.tsum_sub hf1'_sum]
    let d : ℕ → ℝ := fun j =>
      1 / ((a + (j + 1) * qK : ℕ) : ℝ) ^ (1 + s) -
      1 / ((a + (j + 1) * qK + m : ℕ) : ℝ) ^ (1 + s)
    have hd_nonneg : ∀ j, 0 ≤ d j := fun j => by
      dsimp [d]; rw [sub_nonneg]
      exact one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _)
        (Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.le_add_right _ _) (by linarith))
    have hdiff_norm : ∀ j, ‖f1 j - f1' j‖ ≤ d j := by
      intro j
      have : f1 j - f1' j = h (a + (j + 1) * qK + m) * ((d j : ℝ) : ℂ) := by
        dsimp [f1, f1', d]; push_cast; ring
      rw [this, norm_mul, hh _ (by omega), one_mul, Complex.norm_real,
        Real.norm_of_nonneg (hd_nonneg j)]
    have hd_sum : Summable d :=
      (hf1_sum.norm.congr fun j => hf1_norm j).sub (hf1'_sum.norm.congr fun j => hf1'_norm j)
    have h1 : ‖∑' j, (f1 j - f1' j)‖ ≤ ∑' j, d j :=
      (norm_tsum_le_tsum_norm (hf1_sum.sub hf1'_sum).norm).trans
        (Summable.tsum_le_tsum hdiff_norm (hf1_sum.sub hf1'_sum).norm hd_sum)
    have h2 : (∑' j, d j) ≤ 2 * (H : ℝ) := by
      refine hd_sum.tsum_le_of_sum_range_le fun N => ?_
      let u : ℕ → ℝ := fun j => 1 / ((a + (j + 1) * qK : ℕ) : ℝ) ^ (1 + s)
      have htele : ∀ j, d j ≤ u j - u (j + 2 * H) := fun j => by
        dsimp [d, u]
        have hle : a + (j + 1) * qK + m ≤ a + (j + 2 * H + 1) * qK := by nlinarith
        have hle_r : ((a + (j + 1) * qK + m : ℕ) : ℝ) ≤ ((a + (j + 2 * H + 1) * qK : ℕ) : ℝ) := by
          exact_mod_cast hle
        have hpow : ((a + (j + 1) * qK + m : ℕ) : ℝ) ^ (1 + s) ≤
            ((a + (j + 2 * H + 1) * qK : ℕ) : ℝ) ^ (1 + s) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hle_r (by linarith)
        have hdiv := one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity) _) hpow
        linarith
      calc ∑ j ∈ Finset.range N, d j
          ≤ ∑ j ∈ Finset.range N, (u j - u (j + 2 * H)) :=
            Finset.sum_le_sum fun j _ => htele j
        _ = (∑ j ∈ Finset.range N, u j) - ∑ j ∈ Finset.range N, u (j + 2 * H) :=
            Finset.sum_sub_distrib _ _
        _ ≤ ∑ j ∈ Finset.range (2 * H), u j := by
            by_cases hN : N ≤ 2 * H
            · have hu_nn : ∀ j, 0 ≤ u j := fun j => by dsimp [u]; positivity
              have hsub : Finset.sum (Finset.range N) u ≤ Finset.sum (Finset.range (2 * H)) u :=
                Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN) fun j _ _ => hu_nn j
              have hnn : 0 ≤ ∑ j ∈ Finset.range N, u (j + 2 * H) :=
                Finset.sum_nonneg fun _ _ => by dsimp [u]; positivity
              linarith
            · push Not at hN
              have hsplit1 : ∑ j ∈ Finset.range N, u j =
                  (∑ j ∈ Finset.range (2 * H), u j) +
                  ∑ j ∈ Finset.range (N - 2 * H), u (j + 2 * H) := by
                have := Finset.sum_range_add u (2 * H) (N - 2 * H)
                rw [Nat.add_sub_of_le hN.le] at this
                rw [this]; congr 1; apply Finset.sum_congr rfl; intro j _; ring_nf
              have hsplit2 : ∑ j ∈ Finset.range (N - 2 * H), u (j + 2 * H) ≤
                  ∑ j ∈ Finset.range N, u (j + 2 * H) :=
                Finset.sum_le_sum_of_subset_of_nonneg
                  (Finset.range_mono (Nat.sub_le N (2 * H)))
                  fun _ _ _ => by dsimp [u]; positivity
              linarith
        _ ≤ ∑ _j ∈ Finset.range (2 * H), (1 : ℝ) := by
            refine Finset.sum_le_sum fun j _ => ?_
            dsimp [u]
            rw [div_le_one (Real.rpow_pos_of_pos (by positivity) _)]
            exact Real.one_le_rpow (by exact_mod_cast (show 1 ≤ a + (j + 1) * qK by nlinarith))
              (by linarith)
        _ = 2 * (H : ℝ) := by simp [Nat.cast_mul]
    exact h1.trans h2
  -- Bound 2: `∑' g2 - ∑' f1'` is the finite sum over `n < a + m` with `(n+1) ≡ a+m (mod qK)`,
  -- which has at most `2 * H + 1` terms, each of norm `≤ 1`.
  have hB2 : ‖(∑' j, f1' j) - (∑' n, g2 n)‖ ≤ 2 * (H : ℝ) + 1 := by
    let head : Finset ℕ := (Finset.range (a + m)).filter fun n => (n + 1) % qK = (a + m) % qK
    have hsplit : (∑' n, g2 n) = (∑ n ∈ head, g2 n) + ∑' j, f1' j := by
      -- Split `∑' n, g2 n` at `N₀ = a + m`: terms `n ≥ a + m` with `n + 1 ≡ a + m (mod qK)`
      -- are precisely `n = a + m + (j + 1) * qK - 1`.
      rw [← hg2_sum.sum_add_tsum_nat_add (a + m)]
      have hhead : ∑ n ∈ Finset.range (a + m), g2 n = ∑ n ∈ head, g2 n := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun n _ => ?_
        by_cases hc : (n + 1) % qK = (a + m) % qK <;> simp [g2, hc]
      rw [hhead]
      congr 1
      -- Reindex tail `∑' k, g2 (k + (a + m))` by `k = j * qK + (qK - 1)`
      have htail_sum : Summable (fun k => g2 (k + (a + m))) :=
        (summable_nat_add_iff (a + m)).mpr hg2_sum
      let emb : ℕ → ℕ := fun j => (j + 1) * qK - 1
      have hemb_inj : Function.Injective emb := by
        intro j₁ j₂ h
        dsimp [emb] at h
        have h1 : 1 ≤ (j₁ + 1) * qK := by nlinarith
        have h2 : 1 ≤ (j₂ + 1) * qK := by nlinarith
        have h' := congrArg (· + 1) h
        have : (j₁ + 1) * qK = (j₂ + 1) * qK := by
          rwa [Nat.sub_add_cancel h1, Nat.sub_add_cancel h2] at h'
        exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_right (by omega : 0 < qK) this)
      have hsupp : Function.support (fun k => g2 (k + (a + m))) ⊆ Set.range emb := by
        intro k hk
        simp only [Function.mem_support, g2] at hk
        have hc : (k + (a + m) + 1) % qK = (a + m) % qK := by
          by_contra hne; exact hk (if_neg hne)
        have hdvd : qK ∣ (k + 1) := by
          have : (k + 1 + (a + m)) % qK = (0 + (a + m)) % qK := by
            simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hc
          have hmod : (k + 1) % qK = 0 := by
            have := Nat.ModEq.add_right_cancel' (a + m) this
            simpa [Nat.ModEq] using this
          exact Nat.dvd_of_mod_eq_zero hmod
        obtain ⟨c, hc'⟩ := hdvd
        have hcpos : 1 ≤ c := by
          by_contra h0; push Not at h0
          have : c = 0 := by omega
          rw [this, mul_zero] at hc'; omega
        refine ⟨c - 1, ?_⟩
        dsimp [emb]
        have : c - 1 + 1 = c := by omega
        rw [this, mul_comm]; omega
      rw [← hemb_inj.tsum_eq (fun k hk => hsupp (Function.mem_support.mpr hk))]
      refine tsum_congr fun j => ?_
      dsimp [emb, g2, f1']
      have hge1 : 1 ≤ (j + 1) * qK := by nlinarith
      have heq : (j + 1) * qK - 1 + (a + m) + 1 = a + (j + 1) * qK + m := by omega
      rw [heq]
      have hmod : (a + (j + 1) * qK + m) % qK = (a + m) % qK := by
        have : a + (j + 1) * qK + m = (a + m) + qK * (j + 1) := by ring
        rw [this, Nat.add_mul_mod_self_left]
      rw [if_pos hmod]
    have hrew : (∑' j, f1' j) - (∑' n, g2 n) = -(∑ n ∈ head, g2 n) := by rw [hsplit]; ring
    rw [hrew, norm_neg]
    calc ‖∑ n ∈ head, g2 n‖
        ≤ ∑ n ∈ head, ‖g2 n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ head, (1 : ℝ) := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hc := (Finset.mem_filter.mp hn).2
          dsimp [g2]
          rw [if_pos hc, norm_div, hh _ (by omega), Complex.norm_real,
            Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
          rw [div_le_one (Real.rpow_pos_of_pos (by positivity) _)]
          have h1 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast (show 1 ≤ n + 1 by omega)
          exact Real.one_le_rpow h1 (by linarith)
      _ = (head.card : ℝ) := by simp
      _ ≤ 2 * (H : ℝ) + 1 := by
          -- Every `n ∈ head` satisfies `n + 1 = (a + m) - t * qK` with `0 ≤ t ≤ 2 * H`
          have hcard : head.card ≤ 2 * H + 1 := by
            let φ : ℕ → ℕ := fun n => (a + m - (n + 1)) / qK
            have hinj : Set.InjOn φ (head : Set ℕ) := by
              intro n₁ hn₁ n₂ hn₂ hEq
              have h1 := Finset.mem_filter.mp hn₁
              have h2 := Finset.mem_filter.mp hn₂
              have hlt1 : n₁ + 1 ≤ a + m := Finset.mem_range.mp h1.1
              have hlt2 : n₂ + 1 ≤ a + m := Finset.mem_range.mp h2.1
              have hd1 : qK ∣ (a + m - (n₁ + 1)) := (Nat.modEq_iff_dvd' hlt1).mp h1.2
              have hd2 : qK ∣ (a + m - (n₂ + 1)) := (Nat.modEq_iff_dvd' hlt2).mp h2.2
              have he1 : a + m - (n₁ + 1) = qK * φ n₁ := (Nat.mul_div_cancel' hd1).symm
              have he2 : a + m - (n₂ + 1) = qK * φ n₂ := (Nat.mul_div_cancel' hd2).symm
              rw [hEq] at he1; omega
            have himg : Finset.image φ head ⊆ Finset.range (2 * H + 1) := by
              intro t ht
              obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ht
              rw [Finset.mem_range]
              have hlt : a + m - (n + 1) < (2 * H + 1) * qK := by
                have : a + m - (n + 1) < a + m := by omega
                have : a + m ≤ qK + 2 * H := by omega
                have : 2 * H ≤ 2 * H * qK := Nat.le_mul_of_pos_right _ (by omega)
                nlinarith
              exact (Nat.div_lt_iff_lt_mul (by omega : 0 < qK)).mpr hlt
            calc head.card = (Finset.image φ head).card := (Finset.card_image_of_injOn hinj).symm
              _ ≤ (Finset.range (2 * H + 1)).card := Finset.card_le_card himg
              _ = 2 * H + 1 := Finset.card_range _
          exact_mod_cast hcard
  calc ‖(∑' j, f1 j) - (∑' n, g2 n)‖
      = ‖((∑' j, f1 j) - (∑' j, f1' j)) + ((∑' j, f1' j) - (∑' n, g2 n))‖ := by ring_nf
    _ ≤ ‖(∑' j, f1 j) - (∑' j, f1' j)‖ + ‖(∑' j, f1' j) - (∑' n, g2 n)‖ := norm_add_le _ _
    _ ≤ 2 * (H : ℝ) + (2 * (H : ℝ) + 1) := add_le_add hB1 hB2
    _ = 4 * (H : ℝ) + 1 := by ring

/- ### Helper 5: Granville's exact off-diagonal cancellation for primitive characters -/

private lemma primitive_coset_sum_zero {q r : ℕ} [NeZero q] (hq : 2 ≤ q)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hr_dvd : r ∣ q) (hr_lt : r < q) (x : ZMod q) :
    ∑ y ∈ Finset.univ.filter (fun y : ZMod q => ZMod.castHom hr_dvd (ZMod r) y =
      ZMod.castHom hr_dvd (ZMod r) x), χ y = 0 := by
  have hr_pos : 0 < r := Nat.pos_of_dvd_of_pos hr_dvd (by omega)
  have : NeZero r := ⟨hr_pos.ne'⟩
  have hnot_fac : ¬ χ.FactorsThrough r := by
    rw [← DirichletCharacter.mem_conductorSet_iff,
      DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hr_dvd,
      hprim]
    exact Nat.not_dvd_of_pos_of_lt hr_pos hr_lt
  rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hr_dvd] at hnot_fac
  obtain ⟨v, hv_ker, hv_nker⟩ := SetLike.not_le_iff_exists.mp hnot_fac
  rw [MonoidHom.mem_ker] at hv_ker hv_nker
  have hv_cast : ZMod.castHom hr_dvd (ZMod r) (v : ZMod q) = 1 := by
    have := congrArg Units.val hv_ker
    simpa [ZMod.unitsMap_val] using this
  have hχv_ne : χ (v : ZMod q) ≠ 1 := by
    intro h1
    apply hv_nker
    apply Units.ext
    simpa [MulChar.coe_toUnitHom] using h1
  set S : Finset (ZMod q) := Finset.univ.filter fun y : ZMod q =>
    ZMod.castHom hr_dvd (ZMod r) y = ZMod.castHom hr_dvd (ZMod r) x
  have hperm : ∑ y ∈ S, χ ((v : ZMod q) * y) = ∑ y ∈ S, χ y := by
    refine Finset.sum_bij (fun y _ => (v : ZMod q) * y) ?_ ?_ ?_ ?_
    · intro y hy
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      rw [map_mul, hv_cast, one_mul, hy]
    · intro y₁ _ y₂ _ h
      exact (Units.mul_right_inj v).mp h
    · intro y hy
      refine ⟨((v⁻¹ : (ZMod q)ˣ) : ZMod q) * y, ?_, by
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]⟩
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
      have hv_inv : ZMod.castHom hr_dvd (ZMod r) ((v⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
        have : ZMod.castHom hr_dvd (ZMod r) (v : ZMod q) *
            ZMod.castHom hr_dvd (ZMod r) ((v⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
          rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
        rwa [hv_cast, one_mul] at this
      rw [map_mul, hv_inv, one_mul, hy]
    · intro _ _; rfl
  have hmul : χ (v : ZMod q) * ∑ y ∈ S, χ y = ∑ y ∈ S, χ y := by
    rw [Finset.mul_sum]
    simpa [map_mul] using hperm
  have hsub : (χ (v : ZMod q) - 1) * ∑ y ∈ S, χ y = 0 := by linear_combination hmul
  simpa [S] using (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hχv_ne)

private lemma granville_off_diagonal_zero {q k d₁ d₂ m₁ m₂ : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k)
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive)
    (hd₁ : d₁ ∣ q ^ (k - 1)) (hd₂ : d₂ ∣ q ^ (k - 1)) (hne : d₁ ≠ d₂) :
    ∑ a ∈ Finset.Icc 1 (q ^ k),
      (if d₁ ∣ a + m₁ ∧ d₂ ∣ a + m₂ then
        χ (((a + m₁) / d₁ : ℕ) : ZMod q) * star (χ (((a + m₂) / d₂ : ℕ) : ZMod q))
      else 0) = 0 := by
  have : NeZero q := ⟨by omega⟩
  have hqpos : 0 < q := by omega
  have hqk_pos : 0 < q ^ k := pow_pos hqpos k
  have : NeZero (q ^ k) := ⟨hqk_pos.ne'⟩
  have hd₁_pos : 0 < d₁ := Nat.pos_of_dvd_of_pos hd₁ (pow_pos hqpos _)
  have hd₂_pos : 0 < d₂ := Nat.pos_of_dvd_of_pos hd₂ (pow_pos hqpos _)
  -- WLOG there is a prime `p` with `d₁.factorization p > d₂.factorization p`
  suffices hWLOG : ∀ {e₁ e₂ n₁ n₂ : ℕ},
      e₁ ∣ q ^ (k - 1) → e₂ ∣ q ^ (k - 1) →
      (∃ p : ℕ, p.Prime ∧ e₂.factorization p < e₁.factorization p) →
      ∑ a ∈ Finset.Icc 1 (q ^ k),
        (if e₁ ∣ a + n₁ ∧ e₂ ∣ a + n₂ then
          χ (((a + n₁) / e₁ : ℕ) : ZMod q) * star (χ (((a + n₂) / e₂ : ℕ) : ZMod q))
        else 0) = 0 by
    have hfac_ne : d₁.factorization ≠ d₂.factorization := fun heq =>
      hne (Nat.eq_of_factorization_eq hd₁_pos.ne' hd₂_pos.ne' fun p => congrFun (congrArg DFunLike.coe heq) p)
    obtain ⟨p, hp_ne⟩ := Function.ne_iff.mp (DFunLike.coe_injective.ne hfac_ne)
    rcases lt_or_gt_of_ne hp_ne with hlt | hgt
    · have hp : p.Prime := by
        have hpos : 0 < d₂.factorization p := by omega
        exact Nat.prime_of_mem_primeFactors (Nat.support_factorization d₂ ▸ Finsupp.mem_support_iff.mpr hpos.ne')
      have hconj := hWLOG hd₂ hd₁ ⟨p, hp, hlt⟩ (n₁ := m₂) (n₂ := m₁)
      have := congrArg star hconj
      simp only [star_zero, star_sum] at this
      trans ∑ a ∈ Finset.Icc 1 (q ^ k), star (if d₂ ∣ a + m₂ ∧ d₁ ∣ a + m₁ then
          χ (((a + m₂) / d₂ : ℕ) : ZMod q) * star (χ (((a + m₁) / d₁ : ℕ) : ZMod q)) else 0)
      · refine Finset.sum_congr rfl fun a _ => ?_
        by_cases h12 : d₁ ∣ a + m₁ ∧ d₂ ∣ a + m₂
        · have h21 : d₂ ∣ a + m₂ ∧ d₁ ∣ a + m₁ := ⟨h12.2, h12.1⟩
          rw [if_pos h12, if_pos h21, star_mul, star_star]
        · have h21 : ¬ (d₂ ∣ a + m₂ ∧ d₁ ∣ a + m₁) := fun h => h12 ⟨h.2, h.1⟩
          rw [if_neg h12, if_neg h21, star_zero]
      · exact this
    · have hp : p.Prime := by
        have hpos : 0 < d₁.factorization p := by omega
        exact Nat.prime_of_mem_primeFactors (Nat.support_factorization d₁ ▸ Finsupp.mem_support_iff.mpr hpos.ne')
      exact hWLOG hd₁ hd₂ ⟨p, hp, hgt⟩
  intro e₁ e₂ n₁ n₂ he₁ he₂ ⟨p, hp, hvp⟩
  have he₁_pos : 0 < e₁ := Nat.pos_of_dvd_of_pos he₁ (pow_pos hqpos _)
  have he₂_pos : 0 < e₂ := Nat.pos_of_dvd_of_pos he₂ (pow_pos hqpos _)
  have hp_dvd_e₁ : p ∣ e₁ :=
    Nat.dvd_of_mem_primeFactors (Nat.support_factorization e₁ ▸ Finsupp.mem_support_iff.mpr (by omega))
  have hp_dvd_q : p ∣ q := hp.dvd_of_dvd_pow (hp_dvd_e₁.trans he₁)
  let L : ℕ := Nat.lcm e₁ e₂
  have hL_pos : 0 < L := Nat.lcm_pos he₁_pos he₂_pos
  have hL_dvd_qk1 : L ∣ q ^ (k - 1) := Nat.lcm_dvd he₁ he₂
  have he₁_dvd_L : e₁ ∣ L := Nat.dvd_lcm_left e₁ e₂
  have he₂_dvd_L : e₂ ∣ L := Nat.dvd_lcm_right e₁ e₂
  have hL_fac : ∀ ℓ, L.factorization ℓ = max (e₁.factorization ℓ) (e₂.factorization ℓ) :=
    fun ℓ => by simp [L, Nat.factorization_lcm he₁_pos.ne' he₂_pos.ne']
  have hp_dvd_L : p ∣ L := hp_dvd_e₁.trans he₁_dvd_L
  let r : ℕ := q / p
  have hr_mul : p * r = q := Nat.mul_div_cancel' hp_dvd_q
  have hr_dvd : r ∣ q := ⟨p, by linarith⟩
  have hr_lt : r < q := Nat.div_lt_self hqpos hp.one_lt
  let Δ : ℕ := (L / p) * q
  have hΔ_eq : Δ = L * r := by
    have h1 : p * (L / p) = L := Nat.mul_div_cancel' hp_dvd_L
    have h2 : p * Δ = p * (L * r) := by
      dsimp [Δ]; calc p * ((L / p) * q) = (p * (L / p)) * q := by ring
        _ = L * (p * r) := by rw [h1, hr_mul]
        _ = p * (L * r) := by ring
    exact Nat.eq_of_mul_eq_mul_left hp.pos h2
  have he₁_dvd_Δ : e₁ ∣ Δ := by
    rw [hΔ_eq]; exact dvd_mul_of_dvd_left he₁_dvd_L r
  have he₂q_dvd_Δ : e₂ * q ∣ Δ := by
    have : e₂ ∣ L / p := by
      have : e₂ * p ∣ L := by
        rw [← Nat.factorization_le_iff_dvd (mul_ne_zero he₂_pos.ne' hp.ne_zero) hL_pos.ne']
        intro ℓ
        rw [Nat.factorization_mul he₂_pos.ne' hp.ne_zero, Finsupp.add_apply, hL_fac, hp.factorization]
        by_cases hℓ : ℓ = p
        · subst hℓ; simp; omega
        · simp [hℓ]
      exact (Nat.dvd_div_iff_mul_dvd hp_dvd_L).mpr (by simpa [mul_comm] using this)
    exact mul_dvd_mul_right this q
  have he₂_dvd_Δ : e₂ ∣ Δ := dvd_trans (dvd_mul_right e₂ q) he₂q_dvd_Δ
  have hΔ_dvd_qk : Δ ∣ q ^ k := by
    have hk_eq : q ^ k = q ^ (k - 1) * q := by
      conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ]
    rw [hk_eq]
    exact mul_dvd_mul_right ((Nat.div_dvd_of_dvd hp_dvd_L).trans hL_dvd_qk1) q
  have he₁q_dvd_qk : e₁ * q ∣ q ^ k := by
    have hk_eq : q ^ k = q ^ (k - 1) * q := by
      conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ]
    rw [hk_eq]; exact mul_dvd_mul_right he₁ q
  have he₂q_dvd_qk : e₂ * q ∣ q ^ k := by
    have hk_eq : q ^ k = q ^ (k - 1) * q := by
      conv_lhs => rw [← Nat.sub_add_cancel hk, pow_succ]
    rw [hk_eq]; exact mul_dvd_mul_right he₂ q
  let s : ℕ := Δ / e₁
  have hs_mul : e₁ * s = Δ := Nat.mul_div_cancel' he₁_dvd_Δ
  have hs_eq : s = (L / e₁) * r := by
    apply Nat.eq_of_mul_eq_mul_left he₁_pos
    rw [hs_mul, hΔ_eq, ← mul_assoc, Nat.mul_div_cancel' he₁_dvd_L]
  have hp_ndvd_u : ¬ (p ∣ L / e₁) := by
    intro hd
    have hfac : (L / e₁).factorization p = L.factorization p - e₁.factorization p := by
      rw [Nat.factorization_div he₁_dvd_L]; simp
    have hzero : (L / e₁).factorization p = 0 := by
      rw [hfac, hL_fac]; omega
    have hpos : 0 < (L / e₁).factorization p := by
      have hne0 : L / e₁ ≠ 0 := (Nat.div_pos (Nat.le_of_dvd hL_pos he₁_dvd_L) he₁_pos).ne'
      exact Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by
        rw [Nat.support_factorization]; exact Nat.mem_primeFactors.mpr ⟨hp, hd, hne0⟩))
    omega
  -- Define the `q^k`-periodic summand `F : ℕ → ℂ`
  let F : ℕ → ℂ := fun a =>
    if e₁ ∣ a + n₁ ∧ e₂ ∣ a + n₂ then
      χ (((a + n₁) / e₁ : ℕ) : ZMod q) * star (χ (((a + n₂) / e₂ : ℕ) : ZMod q))
    else 0
  have hF_per : ∀ a : ℕ, F (a + q ^ k) = F a := by
    intro a
    have h1_iff : e₁ ∣ a + q ^ k + n₁ ↔ e₁ ∣ a + n₁ := by
      have : a + q ^ k + n₁ = (a + n₁) + q ^ k := by ring
      rw [this, Nat.dvd_add_left ((dvd_mul_right e₁ q).trans he₁q_dvd_qk)]
    have h2_iff : e₂ ∣ a + q ^ k + n₂ ↔ e₂ ∣ a + n₂ := by
      have : a + q ^ k + n₂ = (a + n₂) + q ^ k := by ring
      rw [this, Nat.dvd_add_left ((dvd_mul_right e₂ q).trans he₂q_dvd_qk)]
    dsimp [F]
    by_cases h : e₁ ∣ a + n₁ ∧ e₂ ∣ a + n₂
    · rw [if_pos ⟨h1_iff.mpr h.1, h2_iff.mpr h.2⟩, if_pos h]
      obtain ⟨c₁, hc₁⟩ := he₁q_dvd_qk
      obtain ⟨c₂, hc₂⟩ := he₂q_dvd_qk
      have hq1 : ((a + q ^ k + n₁) / e₁ : ℕ) = (a + n₁) / e₁ + q * c₁ := by
        apply Nat.eq_of_mul_eq_mul_left he₁_pos
        rw [Nat.mul_div_cancel' (h1_iff.mpr h.1), mul_add, Nat.mul_div_cancel' h.1]
        have : e₁ * (q * c₁) = q ^ k := by rw [← mul_assoc, ← hc₁]
        omega
      have hq2 : ((a + q ^ k + n₂) / e₂ : ℕ) = (a + n₂) / e₂ + q * c₂ := by
        apply Nat.eq_of_mul_eq_mul_left he₂_pos
        rw [Nat.mul_div_cancel' (h2_iff.mpr h.2), mul_add, Nat.mul_div_cancel' h.2]
        have : e₂ * (q * c₂) = q ^ k := by rw [← mul_assoc, ← hc₂]
        omega
      rw [hq1, hq2]; simp [Nat.cast_add, Nat.cast_mul]
    · have h' : ¬ (e₁ ∣ a + q ^ k + n₁ ∧ e₂ ∣ a + q ^ k + n₂) :=
        fun hx => h ⟨h1_iff.mp hx.1, h2_iff.mp hx.2⟩
      rw [if_neg h', if_neg h]
  have hF_mod : ∀ a b : ℕ, a % q ^ k = b % q ^ k → F a = F b := by
    have hper_mul : ∀ a t : ℕ, F (a + t * q ^ k) = F a := by
      intro a t; induction t with
      | zero => simp
      | succ t ih =>
        have : a + (t + 1) * q ^ k = (a + t * q ^ k) + q ^ k := by ring
        rw [this, hF_per, ih]
    intro a b hab
    have ha := hper_mul (a % q ^ k) (a / q ^ k)
    have hb := hper_mul (b % q ^ k) (b / q ^ k)
    rw [mul_comm, Nat.mod_add_div] at ha hb
    rw [ha, hb, hab]
  -- Shifting by `j * Δ` preserves the full sum over `Icc 1 (q^k)`
  have hshift : ∀ j : ℕ, ∑ a ∈ Finset.Icc 1 (q ^ k), F (a + j * Δ) =
      ∑ a ∈ Finset.Icc 1 (q ^ k), F a := by
    intro j
    refine Finset.sum_bij (fun a _ => (a + j * Δ - 1) % q ^ k + 1) ?_ ?_ ?_ ?_
    · intro a _
      rw [Finset.mem_Icc]
      exact ⟨Nat.succ_le_succ (Nat.zero_le _), Nat.succ_le_of_lt (Nat.mod_lt _ hqk_pos)⟩
    · intro a₁ ha₁ a₂ ha₂ hEq
      have h1 := Finset.mem_Icc.mp ha₁
      have h2 := Finset.mem_Icc.mp ha₂
      have hm : (a₁ + j * Δ - 1) % q ^ k = (a₂ + j * Δ - 1) % q ^ k := by omega
      have hmod1 : (a₁ - 1 + j * Δ) % q ^ k = (a₂ - 1 + j * Δ) % q ^ k := by
        rwa [show a₁ - 1 + j * Δ = a₁ + j * Δ - 1 by omega,
          show a₂ - 1 + j * Δ = a₂ + j * Δ - 1 by omega]
      have hmod2 : (a₁ - 1) % q ^ k = (a₂ - 1) % q ^ k :=
        Nat.ModEq.add_right_cancel' (j * Δ) hmod1
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod2
      omega
    · intro b hb
      have hb' := Finset.mem_Icc.mp hb
      let c := (b - 1 + (q ^ k - (j * Δ) % q ^ k)) % q ^ k + 1
      refine ⟨c, Finset.mem_Icc.mpr ⟨Nat.succ_le_succ (Nat.zero_le _),
        Nat.succ_le_of_lt (Nat.mod_lt _ hqk_pos)⟩, ?_⟩
      have h1 : (c + j * Δ - 1) % q ^ k = (b - 1) % q ^ k := by
        have hstep : c + j * Δ - 1 = (b - 1 + (q ^ k - (j * Δ) % q ^ k)) % q ^ k + j * Δ := by
          dsimp [c]; rw [Nat.add_right_comm, Nat.add_sub_cancel]
        rw [hstep, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have hrem : (j * Δ) % q ^ k ≤ q ^ k := le_of_lt (Nat.mod_lt _ hqk_pos)
        have hrew : b - 1 + (q ^ k - (j * Δ) % q ^ k) + j * Δ =
            b - 1 + (1 + (j * Δ) / q ^ k) * q ^ k := by
          have hdm := Nat.div_add_mod (j * Δ) (q ^ k)
          zify [hrem]
          linarith
        rw [hrew, Nat.add_mul_mod_self_right]
      rw [h1, Nat.mod_eq_of_lt (by omega)]; omega
    · intro a ha
      have ha1 := (Finset.mem_Icc.mp ha).1
      apply hF_mod
      have hpos : 1 ≤ a + j * Δ := by omega
      have hrew : (a + j * Δ - 1) % q ^ k + 1 ≡ a + j * Δ [MOD q ^ k] := by
        have : (a + j * Δ - 1) % q ^ k + 1 ≡ (a + j * Δ - 1) + 1 [MOD q ^ k] :=
          (Nat.mod_modEq _ _).add_right 1
        rwa [Nat.sub_add_cancel hpos] at this
      exact hrew.symm
  -- Average over `j ∈ range p`
  have havg : (p : ℂ) * ∑ a ∈ Finset.Icc 1 (q ^ k), F a =
      ∑ a ∈ Finset.Icc 1 (q ^ k), ∑ j ∈ Finset.range p, F (a + j * Δ) := by
    rw [Finset.sum_comm]
    calc (p : ℂ) * ∑ a ∈ Finset.Icc 1 (q ^ k), F a
        = ∑ _j ∈ Finset.range p, ∑ a ∈ Finset.Icc 1 (q ^ k), F a := by simp
      _ = ∑ j ∈ Finset.range p, ∑ a ∈ Finset.Icc 1 (q ^ k), F (a + j * Δ) :=
          Finset.sum_congr rfl fun j _ => (hshift j).symm
  -- Show every inner `j`-sum is `0` using `primitive_coset_sum_zero`
  have hinner : ∀ a ∈ Finset.Icc 1 (q ^ k), ∑ j ∈ Finset.range p, F (a + j * Δ) = 0 := by
    intro a _
    by_cases h : e₁ ∣ a + n₁ ∧ e₂ ∣ a + n₂
    · have hj_iff : ∀ j, e₁ ∣ a + j * Δ + n₁ ∧ e₂ ∣ a + j * Δ + n₂ := fun j => by
        refine ⟨?_, ?_⟩
        · have : a + j * Δ + n₁ = (a + n₁) + j * Δ := by ring
          rw [this]; exact dvd_add h.1 (dvd_mul_of_dvd_right he₁_dvd_Δ j)
        · have : a + j * Δ + n₂ = (a + n₂) + j * Δ := by ring
          rw [this]; exact dvd_add h.2 (dvd_mul_of_dvd_right he₂_dvd_Δ j)
      have hterm : ∀ j, F (a + j * Δ) =
          χ ((((a + n₁) / e₁ : ℕ) : ZMod q) + ((j * s : ℕ) : ZMod q)) *
            star (χ (((a + n₂) / e₂ : ℕ) : ZMod q)) := by
        intro j
        dsimp [F]
        rw [if_pos (hj_iff j)]
        have hq1 : (a + j * Δ + n₁) / e₁ = (a + n₁) / e₁ + j * s := by
          apply Nat.eq_of_mul_eq_mul_left he₁_pos
          rw [Nat.mul_div_cancel' (hj_iff j).1, mul_add, Nat.mul_div_cancel' h.1]
          have : e₁ * (j * s) = j * Δ := by rw [← mul_left_comm, hs_mul]
          omega
        obtain ⟨c, hc⟩ := he₂q_dvd_Δ
        have hq2 : (a + j * Δ + n₂) / e₂ = (a + n₂) / e₂ + q * (j * c) := by
          apply Nat.eq_of_mul_eq_mul_left he₂_pos
          rw [Nat.mul_div_cancel' (hj_iff j).2, mul_add, Nat.mul_div_cancel' h.2]
          have : e₂ * (q * (j * c)) = j * Δ := by rw [hc]; ring
          omega
        rw [hq1, hq2]; simp [Nat.cast_add, Nat.cast_mul]
      simp_rw [hterm, ← Finset.sum_mul]
      set x : ZMod q := (((a + n₁) / e₁ : ℕ) : ZMod q)
      suffices hsum0 : ∑ j ∈ Finset.range p, χ (x + ((j * s : ℕ) : ZMod q)) = 0 by
        rw [hsum0, zero_mul]
      rw [← primitive_coset_sum_zero hq χ hprim hr_dvd hr_lt x]
      refine Finset.sum_bij (fun j _ => x + ((j * s : ℕ) : ZMod q)) ?_ ?_ ?_ ?_
      · intro j _
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, map_add, hs_eq]
        have h0 : ZMod.castHom hr_dvd (ZMod r) (((j * ((L / e₁) * r) : ℕ) : ZMod q)) = 0 := by
          rw [map_natCast, Nat.cast_mul, Nat.cast_mul, ZMod.natCast_self, mul_zero, mul_zero]
        rw [h0, add_zero]
      · intro j₁ hj₁ j₂ hj₂ hEq
        have hj₁' := Finset.mem_range.mp hj₁
        have hj₂' := Finset.mem_range.mp hj₂
        have hsub : ((j₁ * s : ℕ) : ZMod q) = ((j₂ * s : ℕ) : ZMod q) := add_left_cancel hEq
        have hmod : j₁ * s ≡ j₂ * s [MOD q] := (ZMod.natCast_eq_natCast_iff _ _ _).mp hsub
        rw [hs_eq, ← hr_mul] at hmod
        have hmul_r : j₁ * (L / e₁) * r ≡ j₂ * (L / e₁) * r [MOD p * r] := by
          simpa [mul_assoc] using hmod
        have hmod_p : j₁ * (L / e₁) ≡ j₂ * (L / e₁) [MOD p] := by
          have hr_pos : 0 < r := Nat.pos_of_dvd_of_pos hr_dvd hqpos
          rw [Nat.modEq_iff_dvd] at hmul_r ⊢
          have hd : ((p : ℤ) * (r : ℤ)) ∣
              (((j₂ * (L / e₁) : ℕ) : ℤ) - ((j₁ * (L / e₁) : ℕ) : ℤ)) * (r : ℤ) := by
            simpa [Nat.cast_mul, sub_mul] using hmul_r
          exact (mul_dvd_mul_iff_right (by exact_mod_cast hr_pos.ne' : (r : ℤ) ≠ 0)).mp hd
        have hcop : Nat.Coprime (L / e₁) p := (hp.coprime_iff_not_dvd.mpr hp_ndvd_u).symm
        have hj_mod : j₁ ≡ j₂ [MOD p] := Nat.ModEq.cancel_right_of_coprime hcop.symm hmod_p
        rwa [Nat.ModEq, Nat.mod_eq_of_lt hj₁', Nat.mod_eq_of_lt hj₂'] at hj_mod
      · intro y hy
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        have hdiff_cast : ZMod.castHom hr_dvd (ZMod r) (y - x) = 0 := by
          rw [map_sub, hy, sub_self]
        have hr_dvd_val : r ∣ (y - x).val := by
          have : (((y - x).val : ℕ) : ZMod r) = 0 := by
            simpa [map_natCast, ZMod.natCast_zmod_val] using hdiff_cast
          exact (ZMod.natCast_eq_zero_iff _ _).mp this
        let t : ℕ := (y - x).val / r
        have : Fact p.Prime := ⟨hp⟩
        have hcop : Nat.Coprime (L / e₁) p := (hp.coprime_iff_not_dvd.mpr hp_ndvd_u).symm
        have hu_ne : ((L / e₁ : ℕ) : ZMod p) ≠ 0 := by
          intro h0; exact hp_ndvd_u ((ZMod.natCast_eq_zero_iff _ _).mp h0)
        let jz : ZMod p := (t : ZMod p) * ((L / e₁ : ℕ) : ZMod p)⁻¹
        refine ⟨jz.val, Finset.mem_range.mpr (ZMod.val_lt jz), ?_⟩
        have hj_mod : jz.val * (L / e₁) ≡ t [MOD p] := by
          rw [← ZMod.natCast_eq_natCast_iff]
          push_cast [ZMod.natCast_zmod_val]
          simp [jz, hu_ne]
        have hmul_mod : jz.val * s ≡ (y - x).val [MOD q] := by
          have h1 : jz.val * (L / e₁) * r ≡ t * r [MOD p * r] := by
            rw [Nat.modEq_iff_dvd] at hj_mod ⊢
            have hd := mul_dvd_mul_right hj_mod (r : ℤ)
            simpa [Nat.cast_mul, sub_mul] using hd
          have h2 : jz.val * ((L / e₁) * r) ≡ (y - x).val [MOD p * r] := by
            simpa [mul_assoc, t, Nat.div_mul_cancel hr_dvd_val] using h1
          rwa [← hs_eq, hr_mul] at h2
        have hcast : ((jz.val * s : ℕ) : ZMod q) = y - x := by
          have := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hmul_mod
          rwa [ZMod.natCast_zmod_val] at this
        rw [hcast, add_sub_cancel]
      · intro _ _; rfl
    · refine Finset.sum_eq_zero fun j _ => ?_
      dsimp [F]
      have hnj : ¬ (e₁ ∣ a + j * Δ + n₁ ∧ e₂ ∣ a + j * Δ + n₂) := by
        rintro ⟨h1, h2⟩
        apply h
        refine ⟨?_, ?_⟩
        · have : a + j * Δ + n₁ = (a + n₁) + j * Δ := by ring
          rw [this] at h1
          exact (Nat.dvd_add_left (dvd_mul_of_dvd_right he₁_dvd_Δ j)).mp h1
        · have : a + j * Δ + n₂ = (a + n₂) + j * Δ := by ring
          rw [this] at h2
          exact (Nat.dvd_add_left (dvd_mul_of_dvd_right he₂_dvd_Δ j)).mp h2
      rw [if_neg hnj]
  have hzero : (p : ℂ) * ∑ a ∈ Finset.Icc 1 (q ^ k), F a = 0 := by
    rw [havg, Finset.sum_eq_zero hinner]
  have hp_ne : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  exact (mul_eq_zero.mp hzero).resolve_left hp_ne


/- ### Helper 6: Good residue class GCD & shift invariance -/

private lemma good_gcd_props {q k H a m : ℕ} (hqpos : 0 < q)
    (ha_Icc : a ∈ Finset.Icc 1 (q ^ k))
    (ha_good : ∀ p : ℕ, p.Prime → p ∣ q → ∀ m ∈ Finset.Icc 1 (2 * H), ¬ (p ^ k ∣ a + m))
    (hm : m ∈ Finset.Icc 1 (2 * H)) :
    Nat.gcd (a + m) (q ^ k) ∣ q ^ (k - 1) ∧
      Nat.Coprime ((a + m) / Nat.gcd (a + m) (q ^ k)) q := by
  have hqk_pos : 0 < q ^ k := pow_pos hqpos k
  have ham_pos : 0 < a + m := by have := (Finset.mem_Icc.mp ha_Icc).1; omega
  let d : ℕ := Nat.gcd (a + m) (q ^ k)
  have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left (q ^ k) ham_pos
  have hd_dvd_am : d ∣ a + m := Nat.gcd_dvd_left _ _
  have hd_dvd_qk : d ∣ q ^ k := Nat.gcd_dvd_right _ _
  refine ⟨?_, ?_⟩
  · rw [← Nat.factorization_le_iff_dvd hd_pos.ne' (pow_pos hqpos _).ne']
    intro p
    by_cases hp : p.Prime
    · by_cases hpq : p ∣ q
      · have hnot : ¬ (p ^ k ∣ a + m) := ha_good p hp hpq m hm
        have hvp_lt : (a + m).factorization p < k := by
          by_contra hge; push Not at hge
          exact hnot (dvd_trans (pow_dvd_pow p hge) (Nat.ordProj_dvd (a + m) p))
        have hvp_d : d.factorization p ≤ (a + m).factorization p :=
          (Nat.factorization_le_iff_dvd hd_pos.ne' ham_pos.ne').mpr hd_dvd_am p
        have hvp_q : 1 ≤ q.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by
          rw [Nat.support_factorization]; exact Nat.mem_primeFactors.mpr ⟨hp, hpq, hqpos.ne'⟩))
        rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
        exact le_trans (by omega : d.factorization p ≤ k - 1) (Nat.le_mul_of_pos_right _ hvp_q)
      · have hvp_q : q.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpq
        have hvp_d : d.factorization p ≤ (q ^ k).factorization p :=
          (Nat.factorization_le_iff_dvd hd_pos.ne' hqk_pos.ne').mpr hd_dvd_qk p
        rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hvp_q, mul_zero] at hvp_d ⊢
        omega
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  · rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hp_div : p ∣ (a + m) / d := hpdvd.trans (Nat.gcd_dvd_left _ _)
    have hp_q : p ∣ q := hpdvd.trans (Nat.gcd_dvd_right _ _)
    have hnot : ¬ (p ^ k ∣ a + m) := ha_good p hp hp_q m hm
    have hvp_lt : (a + m).factorization p < k := by
      by_contra hge; push Not at hge
      exact hnot (dvd_trans (pow_dvd_pow p hge) (Nat.ordProj_dvd (a + m) p))
    have hvp_q : 1 ≤ q.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by
      rw [Nat.support_factorization]; exact Nat.mem_primeFactors.mpr ⟨hp, hp_q, hqpos.ne'⟩))
    have hvp_d : d.factorization p = (a + m).factorization p := by
      rw [Nat.factorization_gcd ham_pos.ne' hqk_pos.ne', Finsupp.inf_apply, Nat.factorization_pow,
        Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      exact min_eq_left (le_trans (by omega : (a + m).factorization p ≤ k) (Nat.le_mul_of_pos_right _ hvp_q))
    have hvp_quot : ((a + m) / d).factorization p = 0 := by
      rw [Nat.factorization_div hd_dvd_am]; simp [hvp_d]
    have hquot_ne0 : (a + m) / d ≠ 0 := (Nat.div_pos (Nat.le_of_dvd ham_pos hd_dvd_am) hd_pos).ne'
    have hvp_pos : 0 < ((a + m) / d).factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by
      rw [Nat.support_factorization]; exact Nat.mem_primeFactors.mpr ⟨hp, hp_div, hquot_ne0⟩))
    omega


/- ### Helper 7: Eliminating `n^{it}` from the weighted short-sum energy -/

private lemma step7_elim_nit {B Q δ t : ℝ} {H X : ℕ}
    (_hB : 0 ≤ B) (hQ1 : 1 ≤ Q) (hH_pos : 1 ≤ H) (hδ_pos : 0 < δ)
    (hX_ge1 : (1 : ℝ) ≤ (X : ℝ)) (hlogX_ge1 : 1 ≤ Real.log (X : ℝ))
    (hlogX_ge_H2 : 12 * (H : ℝ) ^ 2 ≤ Real.log (X : ℝ))
    (hXδ_sq : (4 * (H : ℝ) ^ 2 * (Q + 1)) ^ 2 * 6 ≤ ((X : ℝ) ^ δ) ^ 2)
    (hδ_eq : δ = 1 / (32 * (H : ℝ) ^ 2))
    (ht_tight : |t| ≤ (Q + 1) * (X : ℝ) ^ δ)
    (g χt h : ℕ → ℂ)
    (hχt_norm : ∀ n, 1 ≤ n → ‖χt n‖ = 1) (hh_norm : ∀ n, 1 ≤ n → ‖h n‖ = 1)
    (hfactor : ∀ n, 1 ≤ n → g n = χt n * Complex.exp (Complex.I * t * Real.log (n : ℝ)) * h n)
    (hreal_F : Summable (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ) ^ (1 + 1 / Real.log (X : ℝ))) *
        ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
          ‖∑ m ∈ Finset.Icc 1 H', g (n + 1 + m)‖ ^ 2)) ∧
      (∑' n : ℕ, (1 / ((n + 1 : ℕ) : ℝ) ^ (1 + 1 / Real.log (X : ℝ))) *
        ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
          ‖∑ m ∈ Finset.Icc 1 H', g (n + 1 + m)‖ ^ 2)) ≤ 192 * B * Real.log (X : ℝ) + 1) :
    Summable (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ) ^ (1 + 1 / Real.log (X : ℝ))) *
      ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
        ‖∑ m ∈ Finset.Icc 1 H', χt (n + 1 + m) * h (n + 1 + m)‖ ^ 2)) ∧
    (∑' n : ℕ, (1 / ((n + 1 : ℕ) : ℝ) ^ (1 + 1 / Real.log (X : ℝ))) *
      ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
        ‖∑ m ∈ Finset.Icc 1 H', χt (n + 1 + m) * h (n + 1 + m)‖ ^ 2)) ≤
      (384 * B + 5) * Real.log (X : ℝ) := by
  have hH_real_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH_pos
  have hX_pos : (0 : ℝ) < (X : ℝ) := by linarith
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  set s : ℝ := 1 / Real.log (X : ℝ)
  have hs_pos : 0 < s := by positivity
  let w : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + s)
  have hw_pos : ∀ n, 0 < w n := fun n => by dsimp [w]; positivity
  have hw_tsum_le : (∑' n : ℕ, w n) ≤ 3 * Real.log (X : ℝ) := by
    calc (∑' n : ℕ, w n) ≤ 1 + 2 / s := tsum_inv_rpow_le hs_pos
      _ = 1 + 2 * Real.log (X : ℝ) := by dsimp [s]; field_simp [hlogX_pos.ne']
      _ ≤ 3 * Real.log (X : ℝ) := by linarith
  let term0 : ℕ → ℝ := fun n =>
    w n * ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
      ‖∑ m ∈ Finset.Icc 1 H', g (n + 1 + m)‖ ^ 2)
  have hterm0_nonneg : ∀ n, 0 ≤ term0 n := fun n =>
    mul_nonneg (hw_pos n).le (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  let E_χh : ℕ → ℝ := fun n =>
    w n * ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
      ‖∑ m ∈ Finset.Icc 1 H', χt (n + 1 + m) * h (n + 1 + m)‖ ^ 2)
  have hEχh_nonneg : ∀ n, 0 ≤ E_χh n := fun n =>
    mul_nonneg (hw_pos n).le (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have h4H2_d_aux : 4 * (H : ℝ) ^ 2 * (4 * δ) = 1 / 2 := by
    rw [hδ_eq]; field_simp [hH_real_pos.ne']; ring
  let N₀ : ℕ := Nat.ceil ((X : ℝ) ^ (2 * δ))
  have hN₀_ge1 : 1 ≤ N₀ := by
    have : (1 : ℝ) ≤ (X : ℝ) ^ (2 * δ) :=
      Real.one_le_rpow (by linarith) (by positivity)
    exact_mod_cast this.trans (Nat.le_ceil _)
  -- Pointwise bound for `n + 1 ≥ N₀` (i.e. `n + 1 ≥ X^(2δ)`) and crude `4H^2` for `n + 1 < N₀`
  have hpt_large : ∀ n, N₀ ≤ n + 1 → E_χh n ≤ 2 * term0 n + w n * (1 / 3) := by
    intro n hn
    have hn_rpow : (X : ℝ) ^ (2 * δ) ≤ ((n + 1 : ℕ) : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have hcard : (Finset.Icc (H + 1) (2 * H)).card = H := by simp [Nat.card_Icc]; omega
    have hH'_bd : ∀ H' ∈ Finset.Icc (H + 1) (2 * H),
        ‖∑ m ∈ Finset.Icc 1 H', χt (n + 1 + m) * h (n + 1 + m)‖ ^ 2 ≤
        2 * ‖∑ m ∈ Finset.Icc 1 H', g (n + 1 + m)‖ ^ 2 + 1 / 3 := by
      intro H' hH'
      have hH'_le : H' ≤ 2 * H := (Finset.mem_Icc.mp hH').2
      have hmul_eq : ‖∑ m ∈ Finset.Icc 1 H', χt (n + 1 + m) * h (n + 1 + m)‖ =
          ‖∑ m ∈ Finset.Icc 1 H',
            χt (n + 1 + m) * Complex.exp (Complex.I * t * Real.log ((n + 1 : ℕ) : ℝ)) *
              h (n + 1 + m)‖ := by
        have he1 : ‖Complex.exp (Complex.I * t * Real.log ((n + 1 : ℕ) : ℝ))‖ = 1 := by
          have : Complex.I * (t : ℂ) * (Real.log ((n + 1 : ℕ) : ℝ) : ℂ) =
              Complex.I * ((t * Real.log ((n + 1 : ℕ) : ℝ) : ℝ) : ℂ) := by push_cast; ring
          rw [this]; exact norm_exp_I_mul_real _
        rw [← one_mul (‖∑ m ∈ Finset.Icc 1 H', _‖), ← he1, ← norm_mul, Finset.mul_sum]
        congr 1; refine Finset.sum_congr rfl fun m _ => by ring
      rw [hmul_eq]
      have herr : ‖(∑ m ∈ Finset.Icc 1 H',
            χt (n + 1 + m) * Complex.exp (Complex.I * t * Real.log ((n + 1 : ℕ) : ℝ)) *
              h (n + 1 + m)) -
          (∑ m ∈ Finset.Icc 1 H', g (n + 1 + m))‖ ≤
          4 * (H : ℝ) ^ 2 * (Q + 1) / ((X : ℝ) ^ δ) := by
        rw [← Finset.sum_sub_distrib]
        calc ‖∑ m ∈ Finset.Icc 1 H', _‖
            ≤ ∑ m ∈ Finset.Icc 1 H',
                ‖χt (n + 1 + m) * Complex.exp (Complex.I * t * Real.log ((n + 1 : ℕ) : ℝ)) *
                  h (n + 1 + m) - g (n + 1 + m)‖ := norm_sum_le _ _
          _ ≤ ∑ m ∈ Finset.Icc 1 H', |t| * (m : ℝ) / ((n + 1 : ℕ) : ℝ) := by
              refine Finset.sum_le_sum fun m hm => ?_
              rw [hfactor (n + 1 + m) (by omega)]
              have hrew : χt (n + 1 + m) * Complex.exp (Complex.I * t * Real.log ((n + 1 : ℕ) : ℝ)) *
                  h (n + 1 + m) -
                  χt (n + 1 + m) * Complex.exp (Complex.I * t * Real.log ((n + 1 + m : ℕ) : ℝ)) *
                  h (n + 1 + m) =
                  -(χt (n + 1 + m) * h (n + 1 + m)) *
                    (Complex.exp (Complex.I * t * Real.log ((n + 1 + m : ℕ) : ℝ)) -
                      Complex.exp (Complex.I * t * Real.log ((n + 1 : ℕ) : ℝ))) := by ring
              rw [hrew, norm_mul, norm_neg, norm_mul, hχt_norm _ (by omega),
                hh_norm _ (by omega), one_mul, one_mul]
              exact norm_cpow_shift_sub_le t (by omega)
          _ ≤ ∑ _m ∈ Finset.Icc 1 H',
                ((Q + 1) * (X : ℝ) ^ δ) * (2 * (H : ℝ)) / ((X : ℝ) ^ (2 * δ)) := by
              refine Finset.sum_le_sum fun m hm => ?_
              have hm_le : (m : ℝ) ≤ 2 * (H : ℝ) := by
                exact_mod_cast le_trans (Finset.mem_Icc.mp hm).2 hH'_le
              exact div_le_div₀ (by positivity)
                (mul_le_mul ht_tight hm_le (Nat.cast_nonneg _) (by positivity))
                (by positivity) hn_rpow
          _ ≤ 4 * (H : ℝ) ^ 2 * (Q + 1) / ((X : ℝ) ^ δ) := by
              rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
              have h2d : (X : ℝ) ^ (2 * δ) = (X : ℝ) ^ δ * (X : ℝ) ^ δ := by
                rw [← Real.rpow_add hX_pos]; ring_nf
              have hcard_le : ((H' + 1 - 1 : ℕ) : ℝ) ≤ 2 * (H : ℝ) := by
                exact_mod_cast (show H' + 1 - 1 ≤ 2 * H by omega)
              rw [h2d]
              have hXδ_pos : 0 < (X : ℝ) ^ δ := by positivity
              have hsimp : (Q + 1) * (X : ℝ) ^ δ * (2 * (H : ℝ)) /
                  ((X : ℝ) ^ δ * (X : ℝ) ^ δ) =
                  2 * (H : ℝ) * (Q + 1) / (X : ℝ) ^ δ := by
                field_simp [hXδ_pos.ne']
              rw [hsimp]
              calc ((H' + 1 - 1 : ℕ) : ℝ) * (2 * (H : ℝ) * (Q + 1) / (X : ℝ) ^ δ)
                  ≤ (2 * (H : ℝ)) * (2 * (H : ℝ) * (Q + 1) / (X : ℝ) ^ δ) := by gcongr
                _ = 4 * (H : ℝ) ^ 2 * (Q + 1) / (X : ℝ) ^ δ := by ring
      have htri : ‖∑ m ∈ Finset.Icc 1 H',
          χt (n + 1 + m) * Complex.exp (Complex.I * t * Real.log ((n + 1 : ℕ) : ℝ)) *
            h (n + 1 + m)‖ ≤
          ‖∑ m ∈ Finset.Icc 1 H', g (n + 1 + m)‖ +
            4 * (H : ℝ) ^ 2 * (Q + 1) / ((X : ℝ) ^ δ) := by
        have := norm_le_norm_add_norm_sub'
          (∑ m ∈ Finset.Icc 1 H',
            χt (n + 1 + m) * Complex.exp (Complex.I * t * Real.log ((n + 1 : ℕ) : ℝ)) *
              h (n + 1 + m))
          (∑ m ∈ Finset.Icc 1 H', g (n + 1 + m))
        linarith
      have hsq : ‖∑ m ∈ Finset.Icc 1 H',
          χt (n + 1 + m) * Complex.exp (Complex.I * t * Real.log ((n + 1 : ℕ) : ℝ)) *
            h (n + 1 + m)‖ ^ 2 ≤
          2 * ‖∑ m ∈ Finset.Icc 1 H', g (n + 1 + m)‖ ^ 2 +
            2 * (4 * (H : ℝ) ^ 2 * (Q + 1) / ((X : ℝ) ^ δ)) ^ 2 := by
        have h1 := pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖∑ m ∈ Finset.Icc 1 H', g (n + 1 + m)‖ -
          4 * (H : ℝ) ^ 2 * (Q + 1) / ((X : ℝ) ^ δ))]
      have herr_sq : 2 * (4 * (H : ℝ) ^ 2 * (Q + 1) / ((X : ℝ) ^ δ)) ^ 2 ≤ 1 / 3 := by
        rw [div_pow]
        have hpos : 0 < ((X : ℝ) ^ δ) ^ 2 := by positivity
        rw [← mul_div_assoc, div_le_div_iff₀ hpos (by norm_num : (0 : ℝ) < 3)]
        linarith [hXδ_sq]
      linarith
    dsimp [E_χh, term0]
    calc w n * (1 / (H : ℝ) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
          ‖∑ m ∈ Finset.Icc 1 H', χt (n + 1 + m) * h (n + 1 + m)‖ ^ 2)
        ≤ w n * (1 / (H : ℝ) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
            (2 * ‖∑ m ∈ Finset.Icc 1 H', g (n + 1 + m)‖ ^ 2 + 1 / 3)) := by
          gcongr; exact hH'_bd _ ‹_›
      _ = 2 * (w n * (1 / (H : ℝ) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
            ‖∑ m ∈ Finset.Icc 1 H', g (n + 1 + m)‖ ^ 2)) + w n * (1 / 3) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, hcard, nsmul_eq_mul]
          field_simp [hH_real_pos.ne']
  have hpt_crude : ∀ n, E_χh n ≤ w n * (4 * (H : ℝ) ^ 2) := fun n => by
    dsimp [E_χh]
    have hcard : (Finset.Icc (H + 1) (2 * H)).card = H := by simp [Nat.card_Icc]; omega
    have hH'_c : ∀ H' ∈ Finset.Icc (H + 1) (2 * H),
        ‖∑ m ∈ Finset.Icc 1 H', χt (n + 1 + m) * h (n + 1 + m)‖ ^ 2 ≤ 4 * (H : ℝ) ^ 2 := by
      intro H' hH'
      have h1 : ‖∑ m ∈ Finset.Icc 1 H', χt (n + 1 + m) * h (n + 1 + m)‖ ≤ 2 * (H : ℝ) := by
        calc ‖∑ m ∈ Finset.Icc 1 H', _‖
            ≤ ∑ m ∈ Finset.Icc 1 H', ‖χt (n + 1 + m) * h (n + 1 + m)‖ := norm_sum_le _ _
          _ = ∑ _m ∈ Finset.Icc 1 H', (1 : ℝ) := by
              refine Finset.sum_congr rfl fun m _ => by
                rw [norm_mul, hχt_norm _ (by omega), hh_norm _ (by omega), mul_one]
          _ = (H' : ℝ) := by simp [Nat.card_Icc]
          _ ≤ 2 * (H : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hH').2
      calc _ ≤ (2 * (H : ℝ)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = 4 * (H : ℝ) ^ 2 := by ring
    calc w n * (1 / (H : ℝ) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H), _)
        ≤ w n * (1 / (H : ℝ) * ∑ _H' ∈ Finset.Icc (H + 1) (2 * H), (4 * (H : ℝ) ^ 2)) := by
          gcongr; exact hH'_c _ ‹_›
      _ = w n * (4 * (H : ℝ) ^ 2) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
          field_simp [hH_real_pos.ne']
  have hw_sum : Summable w := summable_one_div_succ_rpow hs_pos
  have hEχh_sum : Summable E_χh :=
    Summable.of_nonneg_of_le hEχh_nonneg hpt_crude (hw_sum.mul_right _)
  refine ⟨hEχh_sum, ?_⟩
  rw [← hEχh_sum.sum_add_tsum_nat_add N₀]
  have hhead : ∑ n ∈ Finset.range N₀, E_χh n ≤ 2 * Real.log (X : ℝ) := by
    have hN₀_le : (N₀ : ℝ) ≤ 2 * (X : ℝ) ^ (2 * δ) := by
      have h1 : (1 : ℝ) ≤ (X : ℝ) ^ (2 * δ) := Real.one_le_rpow (by linarith) (by positivity)
      linarith [Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ (X : ℝ) ^ (2 * δ))]
    have hlog_N₀ : Real.log (N₀ : ℝ) ≤ 1 + 2 * δ * Real.log (X : ℝ) := by
      have h1 := Real.log_le_log (by exact_mod_cast hN₀_ge1) hN₀_le
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_rpow hX_pos] at h1
      have hlog2 : Real.log 2 ≤ 1 := by
        have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
      linarith
    have hsum_wN : ∑ n ∈ Finset.range N₀, w n ≤ 1 + 2 * Real.log (N₀ : ℝ) := by
      have hbij : ∑ n ∈ Finset.range N₀, w n =
          ∑ m ∈ Finset.Icc 1 N₀, (1 : ℝ) / (m : ℝ) ^ (1 + s) := by
        refine Finset.sum_bij (fun n _ => n + 1) ?_ ?_ ?_ ?_
        · intro n hn; rw [Finset.mem_range] at hn; rw [Finset.mem_Icc]; omega
        · intro _ _ _ _ h; omega
        · intro m hm; rw [Finset.mem_Icc] at hm
          exact ⟨m - 1, Finset.mem_range.mpr (by omega), by omega⟩
        · intro _ _; rfl
      rw [hbij]
      exact sum_inv_rpow_Icc_le hs_pos N₀ hN₀_ge1
    have h4H2_d : 4 * (H : ℝ) ^ 2 * (4 * δ) = 1 / 2 := h4H2_d_aux
    calc ∑ n ∈ Finset.range N₀, E_χh n
        ≤ ∑ n ∈ Finset.range N₀, w n * (4 * (H : ℝ) ^ 2) := Finset.sum_le_sum fun n _ => hpt_crude n
      _ = (∑ n ∈ Finset.range N₀, w n) * (4 * (H : ℝ) ^ 2) := (Finset.sum_mul _ _ _).symm
      _ ≤ (1 + 2 * (1 + 2 * δ * Real.log (X : ℝ))) * (4 * (H : ℝ) ^ 2) := by
          gcongr; linarith
      _ = 12 * (H : ℝ) ^ 2 + (4 * (H : ℝ) ^ 2 * (4 * δ)) * Real.log (X : ℝ) := by ring
      _ = 12 * (H : ℝ) ^ 2 + (1 / 2) * Real.log (X : ℝ) := by rw [h4H2_d]
      _ ≤ Real.log (X : ℝ) + (1 / 2) * Real.log (X : ℝ) := by linarith
      _ ≤ 2 * Real.log (X : ℝ) := by linarith
  have htail : (∑' n : ℕ, E_χh (n + N₀)) ≤ (384 * B + 3) * Real.log (X : ℝ) := by
    have hsum_t : Summable (fun n => E_χh (n + N₀)) := (summable_nat_add_iff N₀).mpr hEχh_sum
    have hsum_rhs : Summable (fun n => 2 * term0 (n + N₀) + w (n + N₀) * (1 / 3)) :=
      (((summable_nat_add_iff N₀).mpr hreal_F.1).mul_left 2).add
        (((summable_nat_add_iff N₀).mpr hw_sum).mul_right (1 / 3))
    have hle_pt : ∀ n, E_χh (n + N₀) ≤ 2 * term0 (n + N₀) + w (n + N₀) * (1 / 3) :=
      fun n => hpt_large (n + N₀) (by omega)
    have hle_sum : (∑' n, E_χh (n + N₀)) ≤
        2 * (∑' n, term0 (n + N₀)) + (∑' n, w (n + N₀)) * (1 / 3) := by
      calc (∑' n, E_χh (n + N₀))
          ≤ ∑' n, (2 * term0 (n + N₀) + w (n + N₀) * (1 / 3)) :=
            Summable.tsum_le_tsum hle_pt hsum_t hsum_rhs
        _ = (∑' n, 2 * term0 (n + N₀)) + ∑' n, w (n + N₀) * (1 / 3) :=
            Summable.tsum_add (((summable_nat_add_iff N₀).mpr hreal_F.1).mul_left 2)
              (((summable_nat_add_iff N₀).mpr hw_sum).mul_right (1 / 3))
        _ = 2 * (∑' n, term0 (n + N₀)) + (∑' n, w (n + N₀)) * (1 / 3) := by
            rw [tsum_mul_left, tsum_mul_right]
    have hterm_tail : (∑' n, term0 (n + N₀)) ≤ ∑' n, term0 n := by
      have hsum_t0 : Summable term0 := hreal_F.1
      rw [← hsum_t0.sum_add_tsum_nat_add N₀]
      linarith [Finset.sum_nonneg (s := Finset.range N₀) fun n _ => hterm0_nonneg n]
    have hw_tail : (∑' n, w (n + N₀)) ≤ ∑' n, w n := by
      rw [← hw_sum.sum_add_tsum_nat_add N₀]
      linarith [Finset.sum_nonneg (s := Finset.range N₀) fun n _ => (hw_pos n).le]
    nlinarith [hreal_F.2, hw_tsum_le, hlogX_ge1]
  linarith


/- ### Helper 8: Cauchy–Schwarz decoupling over good residue classes modulo `q^k` -/

private lemma step8_decouple_contra410 {B c C₀ : ℝ} {Qnat H k X q : ℕ}
    (hB : 0 ≤ B) (hc_pos : 0 < c) (hC₀_eq : C₀ = (6 * (384 * B + 5) + 1) / c ^ 2)
    (hH_pos : 1 ≤ H) (hk_ge1 : 1 ≤ k) (hq1 : 1 ≤ q) (hq_le_Qnat : q ≤ Qnat)
    (hlogX_ge1 : 1 ≤ Real.log (X : ℝ))
    (hlogX_shift : ((Qnat ^ k : ℕ) : ℝ) * (8 * (H : ℝ)) * (4 * (H : ℝ) + 1) ≤ Real.log (X : ℝ))
    (χ : DirichletCharacter ℂ q) (χt h : ℕ → ℂ)
    (hχt_mul : ∀ a b, χt (a * b) = χt a * χt b)
    (hχt_norm : ∀ n, 1 ≤ n → ‖χt n‖ = 1) (hh_norm : ∀ n, 1 ≤ n → ‖h n‖ = 1)
    (hχt_coprime : ∀ n, 1 ≤ n → Nat.Coprime n q → χt n = χ (n : ZMod q))
    (hEχh_bound : Summable (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ) ^ (1 + 1 / Real.log (X : ℝ))) *
        ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
          ‖∑ m ∈ Finset.Icc 1 H', χt (n + 1 + m) * h (n + 1 + m)‖ ^ 2)) ∧
      (∑' n : ℕ, (1 / ((n + 1 : ℕ) : ℝ) ^ (1 + 1 / Real.log (X : ℝ))) *
        ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
          ‖∑ m ∈ Finset.Icc 1 H', χt (n + 1 + m) * h (n + 1 + m)‖ ^ 2)) ≤
        (384 * B + 5) * Real.log (X : ℝ))
    {S : ℂ} (hS_lb : c * Real.log (X : ℝ) ≤ ‖S‖)
    (hS_ap : ∀ b : ℕ, ‖(∑' n : ℕ, if (n + 1) % (q ^ k) = b % (q ^ k) then
        h (n + 1) / Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (1 + 1 / Real.log (X : ℝ))) else 0) -
        S / ((q ^ k : ℕ) : ℂ)‖ ≤ (1 / (8 * (H : ℝ))) * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ)) :
    (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
      ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a =>
          ∀ p : ℕ, p.Prime → p ∣ q → ∀ m ∈ Finset.Icc 1 (2 * H), ¬ (p ^ k ∣ a + m)),
        ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2 ≤ C₀ * ((q ^ k : ℕ) : ℝ) := by
  have hH_real_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH_pos
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  set s : ℝ := 1 / Real.log (X : ℝ)
  have hs_pos : 0 < s := by positivity
  let w : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + s)
  have hw_pos : ∀ n, 0 < w n := fun n => by dsimp [w]; positivity
  have hw_tsum_le : (∑' n : ℕ, w n) ≤ 3 * Real.log (X : ℝ) := by
    calc (∑' n : ℕ, w n) ≤ 1 + 2 / s := tsum_inv_rpow_le hs_pos
      _ = 1 + 2 * Real.log (X : ℝ) := by dsimp [s]; field_simp [hlogX_pos.ne']
      _ ≤ 3 * Real.log (X : ℝ) := by linarith
  let E_χh : ℕ → ℝ := fun n =>
    w n * ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
      ‖∑ m ∈ Finset.Icc 1 H', χt (n + 1 + m) * h (n + 1 + m)‖ ^ 2)
  have hEχh_nonneg : ∀ n, 0 ≤ E_χh n := fun n =>
    mul_nonneg (hw_pos n).le (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hqpos : 0 < q := by omega
  have hqk_pos : 0 < q ^ k := pow_pos hqpos k
  let good : Finset ℕ := (Finset.Icc 1 (q ^ k)).filter fun a =>
    ∀ p : ℕ, p.Prime → p ∣ q → ∀ m ∈ Finset.Icc 1 (2 * H), ¬ (p ^ k ∣ a + m)
  have hgood_shift : ∀ a ∈ good, ∀ m ∈ Finset.Icc 1 (2 * H), ∀ j : ℕ,
      χt (a + (j + 1) * q ^ k + m) = χt (a + m) := by
    intro a ha m hm j
    have ha' := Finset.mem_filter.mp ha
    have ham_pos : 0 < a + m := by have := (Finset.mem_Icc.mp ha'.1).1; omega
    let d : ℕ := Nat.gcd (a + m) (q ^ k)
    have hd_pos : 0 < d := Nat.gcd_pos_of_pos_left (q ^ k) ham_pos
    have hd_dvd_am : d ∣ a + m := Nat.gcd_dvd_left _ _
    have hd_dvd_qk : d ∣ q ^ k := Nat.gcd_dvd_right _ _
    obtain ⟨hd_dvd_qk1, hcop_am⟩ := good_gcd_props hqpos ha'.1 ha'.2 hm
    have hq_dvd_quot : q ∣ (q ^ k / d) := by
      have hk_eq : q ^ k = q ^ (k - 1) * q := by
        conv_lhs => rw [← Nat.sub_add_cancel hk_ge1, pow_succ]
      obtain ⟨c, hc⟩ := hd_dvd_qk1
      refine ⟨c, ?_⟩
      apply Nat.eq_of_mul_eq_mul_left hd_pos
      rw [Nat.mul_div_cancel' hd_dvd_qk, hk_eq, hc]; ring
    have hd_dvd_shift : d ∣ a + (j + 1) * q ^ k + m := by
      have : a + (j + 1) * q ^ k + m = (a + m) + (j + 1) * q ^ k := by ring
      rw [this]; exact dvd_add hd_dvd_am (dvd_mul_of_dvd_right hd_dvd_qk _)
    have hquot_shift : (a + (j + 1) * q ^ k + m) / d = (a + m) / d + (j + 1) * (q ^ k / d) := by
      apply Nat.eq_of_mul_eq_mul_left hd_pos
      rw [Nat.mul_div_cancel' hd_dvd_shift, mul_add, Nat.mul_div_cancel' hd_dvd_am,
        ← mul_left_comm, Nat.mul_div_cancel' hd_dvd_qk]; ring
    have hcop_shift : Nat.Coprime ((a + (j + 1) * q ^ k + m) / d) q := by
      rw [hquot_shift]
      obtain ⟨c, hc⟩ := hq_dvd_quot
      rw [hc, Nat.coprime_iff_gcd_eq_one]
      have hgcd : Nat.gcd ((a + m) / d + (j + 1) * (q * c)) q = Nat.gcd ((a + m) / d) q := by
        apply Nat.dvd_antisymm
        · refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
          have h1 := Nat.gcd_dvd_left ((a + m) / d + (j + 1) * (q * c)) q
          have h2 : Nat.gcd ((a + m) / d + (j + 1) * (q * c)) q ∣ (j + 1) * (q * c) :=
            dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) c) (j + 1)
          exact (Nat.dvd_add_left h2).mp h1
        · refine Nat.dvd_gcd ?_ (Nat.gcd_dvd_right _ _)
          exact dvd_add (Nat.gcd_dvd_left _ _)
            (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left (Nat.gcd_dvd_right _ _) c) (j + 1))
      rw [hgcd]; exact hcop_am.gcd_eq_one
    have hmod_q : (((a + (j + 1) * q ^ k + m) / d : ℕ) : ZMod q) = (((a + m) / d : ℕ) : ZMod q) := by
      rw [hquot_shift]
      obtain ⟨c, hc⟩ := hq_dvd_quot
      rw [hc]; simp [Nat.cast_add, Nat.cast_mul]
    have h1 : a + (j + 1) * q ^ k + m = d * ((a + (j + 1) * q ^ k + m) / d) :=
      (Nat.mul_div_cancel' hd_dvd_shift).symm
    have h2 : a + m = d * ((a + m) / d) := (Nat.mul_div_cancel' hd_dvd_am).symm
    have hq1_pos : 1 ≤ (a + (j + 1) * q ^ k + m) / d :=
      Nat.div_pos (Nat.le_of_dvd (by omega) hd_dvd_shift) hd_pos
    have hq2_pos : 1 ≤ (a + m) / d := Nat.div_pos (Nat.le_of_dvd ham_pos hd_dvd_am) hd_pos
    rw [h1, hχt_mul, hχt_coprime _ hq1_pos hcop_shift, hmod_q, ← hχt_coprime _ hq2_pos hcop_am,
      ← hχt_mul, ← h2]
  -- First restrict `∑' n, E_χh n` to `n = a + (j + 1) * q^k - 1` (`a ∈ good`, `j : ℕ`)
  let E_aj : ℕ → ℕ → ℝ := fun a j => E_χh (a + (j + 1) * q ^ k - 1)
  have hE_aj_sum : ∀ a ∈ good, Summable (E_aj a) := fun a ha => by
    have ha1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
    have hinj : Function.Injective (fun j : ℕ => a + (j + 1) * q ^ k - 1) := by
      intro j₁ j₂ hEq
      have h1' := congrArg (· + 1) hEq; dsimp at h1'
      have h1 : a + (j₁ + 1) * q ^ k = a + (j₂ + 1) * q ^ k := by
        rwa [Nat.sub_add_cancel (by omega), Nat.sub_add_cancel (by omega)] at h1'
      exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_right hqk_pos (Nat.add_left_cancel h1))
    exact hEχh_bound.1.comp_injective hinj
  have hE_good_le : ∑ a ∈ good, (∑' j : ℕ, E_aj a j) ≤ (384 * B + 5) * Real.log (X : ℝ) := by
    -- Prove via finite partial sums over `j ∈ range N`
    have hfin : ∀ N : ℕ, ∑ a ∈ good, ∑ j ∈ Finset.range N, E_aj a j ≤
        ∑' n, E_χh n := by
      intro N
      rw [← Finset.sum_product']
      let f_idx : ℕ × ℕ → ℕ := fun p => p.1 + (p.2 + 1) * q ^ k - 1
      have hinj : Set.InjOn f_idx ((good ×ˢ Finset.range N : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)) := by
        intro p₁ hp₁ p₂ hp₂ hEq
        rw [Finset.mem_coe, Finset.mem_product] at hp₁ hp₂
        have ha1 := Finset.mem_Icc.mp (Finset.mem_filter.mp hp₁.1).1
        have ha2 := Finset.mem_Icc.mp (Finset.mem_filter.mp hp₂.1).1
        have heq' : (p₁.1 - 1) + (p₁.2 + 1) * q ^ k = (p₂.1 - 1) + (p₂.2 + 1) * q ^ k := by
          dsimp [f_idx] at hEq; omega
        have hmod : (p₁.1 - 1) % q ^ k = (p₂.1 - 1) % q ^ k := by
          have h1 := congrArg (· % q ^ k) heq'
          simpa [Nat.add_mul_mod_self_right] using h1
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
        have ha_eq : p₁.1 = p₂.1 := by omega
        have hj_eq : p₁.2 = p₂.2 := by
          have : (p₁.2 + 1) * q ^ k = (p₂.2 + 1) * q ^ k := by omega
          exact Nat.succ.inj (Nat.eq_of_mul_eq_mul_right hqk_pos this)
        exact Prod.ext ha_eq hj_eq
      have hsum_img : ∑ p ∈ good ×ˢ Finset.range N, E_χh (f_idx p) =
          ∑ n ∈ (good ×ˢ Finset.range N).image f_idx, E_χh n :=
        (Finset.sum_image hinj).symm
      calc ∑ p ∈ good ×ˢ Finset.range N, E_aj p.1 p.2
          = ∑ n ∈ (good ×ˢ Finset.range N).image f_idx, E_χh n := hsum_img
        _ ≤ ∑' n, E_χh n := hEχh_bound.1.sum_le_tsum _ fun n _ => hEχh_nonneg n
    have htend : Tendsto (fun N => ∑ a ∈ good, ∑ j ∈ Finset.range N, E_aj a j)
        atTop (𝓝 (∑ a ∈ good, ∑' j, E_aj a j)) :=
      tendsto_finsetSum good fun a ha => (hE_aj_sum a ha).hasSum.tendsto_sum_nat
    exact (le_of_tendsto htend (Eventually.of_forall hfin)).trans hEχh_bound.2
  -- Cauchy–Schwarz over `j` for each `a ∈ good` and `H' ∈ Icc (H+1) (2H)`
  have hCS : ∀ a ∈ good, ∀ H' ∈ Finset.Icc (H + 1) (2 * H),
      ‖∑ m ∈ Finset.Icc 1 H', χt (a + m) *
        (∑' j : ℕ, h (a + (j + 1) * q ^ k + m) /
          Complex.ofReal (((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s)))‖ ^ 2 ≤
      (3 * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ)) *
        ∑' j : ℕ, w (a + (j + 1) * q ^ k - 1) *
          ‖∑ m ∈ Finset.Icc 1 H', χt (a + (j + 1) * q ^ k + m) * h (a + (j + 1) * q ^ k + m)‖ ^ 2 := by
    intro a ha H' hH'
    have ha1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
    have hH'_le : H' ≤ 2 * H := (Finset.mem_Icc.mp hH').2
    let w_aj : ℕ → ℝ := fun j => w (a + (j + 1) * q ^ k - 1)
    let u_aj : ℕ → ℂ := fun j =>
      ∑ m ∈ Finset.Icc 1 H', χt (a + (j + 1) * q ^ k + m) * h (a + (j + 1) * q ^ k + m)
    have hw_aj_eq : ∀ j, w_aj j = 1 / ((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s) := fun j => by
      dsimp [w_aj, w]; congr 2; exact_mod_cast (show a + (j + 1) * q ^ k - 1 + 1 = a + (j + 1) * q ^ k by omega)
    have hsum_base : Summable (fun j : ℕ => (1 : ℝ) / ((j + 1 : ℕ) : ℝ) ^ (1 + s)) :=
      summable_one_div_succ_rpow hs_pos
    have hw_aj_le : ∀ j, w_aj j ≤ (1 / ((q ^ k : ℕ) : ℝ)) * (1 / ((j + 1 : ℕ) : ℝ) ^ (1 + s)) := by
      intro j
      rw [hw_aj_eq]
      have hbase : ((j + 1 : ℕ) : ℝ) * ((q ^ k : ℕ) : ℝ) ≤ ((a + (j + 1) * q ^ k : ℕ) : ℝ) := by
        exact_mod_cast (show (j + 1) * q ^ k ≤ a + (j + 1) * q ^ k by omega)
      have hpow : ((j + 1 : ℕ) : ℝ) ^ (1 + s) * ((q ^ k : ℕ) : ℝ) ^ (1 + s) ≤
          ((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s) := by
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        exact Real.rpow_le_rpow (by positivity) hbase (by linarith)
      have hqk_pow : ((q ^ k : ℕ) : ℝ) ≤ ((q ^ k : ℕ) : ℝ) ^ (1 + s) := by
        calc ((q ^ k : ℕ) : ℝ) = ((q ^ k : ℕ) : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ ((q ^ k : ℕ) : ℝ) ^ (1 + s) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hqk_pos) (by linarith)
      have hprod : ((j + 1 : ℕ) : ℝ) ^ (1 + s) * ((q ^ k : ℕ) : ℝ) ≤
          ((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s) :=
        le_trans (mul_le_mul_of_nonneg_left hqk_pow (by positivity)) hpow
      calc 1 / ((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s)
          ≤ 1 / (((j + 1 : ℕ) : ℝ) ^ (1 + s) * ((q ^ k : ℕ) : ℝ)) :=
            one_div_le_one_div_of_le (by positivity) hprod
        _ = (1 / ((q ^ k : ℕ) : ℝ)) * (1 / ((j + 1 : ℕ) : ℝ) ^ (1 + s)) := by ring
    have hw_aj_sum : Summable w_aj :=
      Summable.of_nonneg_of_le (fun j => (hw_pos _).le) hw_aj_le (hsum_base.mul_left _)
    have hw_aj_tsum : (∑' j, w_aj j) ≤ 3 * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ) := by
      calc (∑' j, w_aj j)
          ≤ ∑' j, (1 / ((q ^ k : ℕ) : ℝ)) * (1 / ((j + 1 : ℕ) : ℝ) ^ (1 + s)) :=
            Summable.tsum_le_tsum hw_aj_le hw_aj_sum (hsum_base.mul_left _)
        _ = (1 / ((q ^ k : ℕ) : ℝ)) * ∑' j, (1 / ((j + 1 : ℕ) : ℝ) ^ (1 + s)) := tsum_mul_left
        _ ≤ (1 / ((q ^ k : ℕ) : ℝ)) * (3 * Real.log (X : ℝ)) := by
            gcongr
        _ = 3 * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ) := by ring
    have hu_norm_bd : ∀ j, ‖u_aj j‖ ≤ 2 * (H : ℝ) := fun j => by
      calc ‖u_aj j‖ ≤ ∑ m ∈ Finset.Icc 1 H', ‖χt (a + (j + 1) * q ^ k + m) * h (a + (j + 1) * q ^ k + m)‖ :=
            norm_sum_le _ _
        _ = (H' : ℝ) := by
            trans ∑ _m ∈ Finset.Icc 1 H', (1 : ℝ)
            · exact Finset.sum_congr rfl fun m _ => by
                rw [norm_mul, hχt_norm _ (by omega), hh_norm _ (by omega), mul_one]
            · simp [Nat.card_Icc]
        _ ≤ 2 * (H : ℝ) := by exact_mod_cast hH'_le
    have hterm_sum_m : ∀ m ∈ Finset.Icc 1 H', Summable (fun j : ℕ =>
        h (a + (j + 1) * q ^ k + m) / Complex.ofReal (((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s))) := by
      intro m _
      refine Summable.of_norm_bounded hw_aj_sum fun j => ?_
      rw [norm_div, hh_norm _ (by omega), Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _), hw_aj_eq]
    have hswap : (∑ m ∈ Finset.Icc 1 H', χt (a + m) *
        (∑' j : ℕ, h (a + (j + 1) * q ^ k + m) /
          Complex.ofReal (((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s)))) =
        ∑' j : ℕ, u_aj j * (w_aj j : ℂ) := by
      have h1 : ∀ m ∈ Finset.Icc 1 H', χt (a + m) *
          (∑' j : ℕ, h (a + (j + 1) * q ^ k + m) /
            Complex.ofReal (((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s))) =
          ∑' j : ℕ, χt (a + (j + 1) * q ^ k + m) * h (a + (j + 1) * q ^ k + m) * (w_aj j : ℂ) := by
        intro m hm
        rw [← tsum_mul_left]
        refine tsum_congr fun j => ?_
        rw [hgood_shift a ha m (Finset.Icc_subset_Icc_right hH'_le hm) j, hw_aj_eq]
        push_cast; ring
      rw [Finset.sum_congr rfl h1, ← Summable.tsum_finsetSum (fun m hm => ?_)]
      · refine tsum_congr fun j => by dsimp [u_aj]; rw [Finset.sum_mul]
      · refine Summable.of_norm_bounded hw_aj_sum fun j => ?_
        rw [norm_mul, norm_mul, hχt_norm _ (by omega), hh_norm _ (by omega), one_mul, one_mul,
          Complex.norm_real, Real.norm_of_nonneg (hw_pos _).le]
    have huw_sum : Summable (fun j : ℕ => u_aj j * (w_aj j : ℂ)) :=
      Summable.of_norm_bounded (hw_aj_sum.mul_left (2 * (H : ℝ))) fun j => by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw_pos _).le]
        exact mul_le_mul_of_nonneg_right (hu_norm_bd j) (hw_pos _).le
    have hu2w_sum : Summable (fun j : ℕ => w_aj j * ‖u_aj j‖ ^ 2) :=
      Summable.of_nonneg_of_le (fun j => mul_nonneg (hw_pos _).le (sq_nonneg _))
        (fun j => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hu_norm_bd j) 2) (hw_pos _).le)
        (hw_aj_sum.mul_right _)
    rw [hswap]
    have hcs_fin : ∀ N : ℕ, ‖∑ j ∈ Finset.range N, u_aj j * (w_aj j : ℂ)‖ ^ 2 ≤
        (3 * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ)) * ∑' j, w_aj j * ‖u_aj j‖ ^ 2 := by
      intro N
      have h1 : ‖∑ j ∈ Finset.range N, u_aj j * (w_aj j : ℂ)‖ ≤
          ∑ j ∈ Finset.range N, Real.sqrt (w_aj j) * (Real.sqrt (w_aj j) * ‖u_aj j‖) := by
        calc ‖∑ j ∈ Finset.range N, u_aj j * (w_aj j : ℂ)‖
            ≤ ∑ j ∈ Finset.range N, ‖u_aj j * (w_aj j : ℂ)‖ := norm_sum_le _ _
          _ = ∑ j ∈ Finset.range N, Real.sqrt (w_aj j) * (Real.sqrt (w_aj j) * ‖u_aj j‖) := by
              refine Finset.sum_congr rfl fun j _ => ?_
              rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hw_pos _).le,
                ← mul_assoc, Real.mul_self_sqrt (hw_pos _).le, mul_comm]
      have h2 : (∑ j ∈ Finset.range N, Real.sqrt (w_aj j) * (Real.sqrt (w_aj j) * ‖u_aj j‖)) ^ 2 ≤
          (∑ j ∈ Finset.range N, w_aj j) * ∑ j ∈ Finset.range N, w_aj j * ‖u_aj j‖ ^ 2 := by
        have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
          (fun j => Real.sqrt (w_aj j)) (fun j => Real.sqrt (w_aj j) * ‖u_aj j‖)
        have hEq1 : ∑ j ∈ Finset.range N, Real.sqrt (w_aj j) ^ 2 = ∑ j ∈ Finset.range N, w_aj j :=
          Finset.sum_congr rfl fun j _ => Real.sq_sqrt (hw_pos _).le
        have hEq2 : ∑ j ∈ Finset.range N, (Real.sqrt (w_aj j) * ‖u_aj j‖) ^ 2 =
            ∑ j ∈ Finset.range N, w_aj j * ‖u_aj j‖ ^ 2 :=
          Finset.sum_congr rfl fun j _ => by rw [mul_pow, Real.sq_sqrt (hw_pos _).le]
        rwa [hEq1, hEq2] at hcs
      have h3 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      have h4 : ∑ j ∈ Finset.range N, w_aj j ≤ 3 * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ) :=
        (hw_aj_sum.sum_le_tsum _ fun _ _ => (hw_pos _).le).trans hw_aj_tsum
      have h5 : ∑ j ∈ Finset.range N, w_aj j * ‖u_aj j‖ ^ 2 ≤ ∑' j, w_aj j * ‖u_aj j‖ ^ 2 :=
        hu2w_sum.sum_le_tsum _ fun _ _ => mul_nonneg (hw_pos _).le (sq_nonneg _)
      exact (h3.trans h2).trans (mul_le_mul h4 h5
        (Finset.sum_nonneg fun _ _ => mul_nonneg (hw_pos _).le (sq_nonneg _)) (by positivity))
    have htend : Tendsto (fun N => ‖∑ j ∈ Finset.range N, u_aj j * (w_aj j : ℂ)‖ ^ 2)
        atTop (𝓝 (‖∑' j, u_aj j * (w_aj j : ℂ)‖ ^ 2)) :=
      ((continuous_norm.pow 2).tendsto _).comp huw_sum.hasSum.tendsto_sum_nat
    exact le_of_tendsto htend (Eventually.of_forall hcs_fin)
  -- Combine `hCS`, `hE_good_le`, `tsum_ap_shift_sub_le`, and `hS_ap`
  have hsum_CS : (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ good,
      ‖∑ m ∈ Finset.Icc 1 H', χt (a + m) *
        (∑' j : ℕ, h (a + (j + 1) * q ^ k + m) /
          Complex.ofReal (((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s)))‖ ^ 2 ≤
      3 * (384 * B + 5) * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ) := by
    have hswap_E : (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ good,
        ∑' j : ℕ, w (a + (j + 1) * q ^ k - 1) *
          ‖∑ m ∈ Finset.Icc 1 H', χt (a + (j + 1) * q ^ k + m) * h (a + (j + 1) * q ^ k + m)‖ ^ 2 =
        ∑ a ∈ good, ∑' j : ℕ, E_aj a j := by
      rw [Finset.sum_comm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      have hsum_m : ∀ H' ∈ Finset.Icc (H + 1) (2 * H), Summable (fun j : ℕ =>
          w (a + (j + 1) * q ^ k - 1) *
            ‖∑ m ∈ Finset.Icc 1 H', χt (a + (j + 1) * q ^ k + m) * h (a + (j + 1) * q ^ k + m)‖ ^ 2) := by
        intro H' hH'
        refine Summable.of_nonneg_of_le (fun j => mul_nonneg (hw_pos _).le (sq_nonneg _))
          (fun j => ?_) ((hE_aj_sum a ha).mul_left (H : ℝ))
        dsimp [E_aj, E_χh]
        have ha1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
        have hrew : a + (j + 1) * q ^ k - 1 + 1 = a + (j + 1) * q ^ k := by omega
        rw [hrew]
        have hle_sum : ‖∑ m ∈ Finset.Icc 1 H', χt (a + (j + 1) * q ^ k + m) * h (a + (j + 1) * q ^ k + m)‖ ^ 2 ≤
            ∑ H'' ∈ Finset.Icc (H + 1) (2 * H),
              ‖∑ m ∈ Finset.Icc 1 H'', χt (a + (j + 1) * q ^ k + m) * h (a + (j + 1) * q ^ k + m)‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun H'' => ‖∑ m ∈ Finset.Icc 1 H'', χt (a + (j + 1) * q ^ k + m) * h (a + (j + 1) * q ^ k + m)‖ ^ 2)
            (fun _ _ => sq_nonneg _) hH'
        calc w (a + (j + 1) * q ^ k - 1) * _
            ≤ w (a + (j + 1) * q ^ k - 1) * ∑ H'' ∈ Finset.Icc (H + 1) (2 * H), _ :=
              mul_le_mul_of_nonneg_left hle_sum (hw_pos _).le
          _ = (H : ℝ) * (w (a + (j + 1) * q ^ k - 1) * (1 / (H : ℝ) * ∑ H'' ∈ Finset.Icc (H + 1) (2 * H), _)) := by
              field_simp [hH_real_pos.ne']
      rw [← Summable.tsum_finsetSum hsum_m, ← tsum_mul_left]
      refine tsum_congr fun j => ?_
      have ha1 := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).1
      have hrew : a + (j + 1) * q ^ k - 1 + 1 = a + (j + 1) * q ^ k := by omega
      dsimp [E_aj, E_χh]; rw [hrew, ← Finset.mul_sum]; ring
    calc (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ good, _
        ≤ (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ good,
            ((3 * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ)) *
              ∑' j : ℕ, w (a + (j + 1) * q ^ k - 1) *
                ‖∑ m ∈ Finset.Icc 1 H', χt (a + (j + 1) * q ^ k + m) * h (a + (j + 1) * q ^ k + m)‖ ^ 2) := by
          gcongr; exact hCS _ ‹_› _ ‹_›
      _ = (3 * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ)) *
            ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ good,
              ∑' j : ℕ, w (a + (j + 1) * q ^ k - 1) *
                ‖∑ m ∈ Finset.Icc 1 H', χt (a + (j + 1) * q ^ k + m) * h (a + (j + 1) * q ^ k + m)‖ ^ 2) := by
          simp_rw [← Finset.mul_sum]; ring
      _ = (3 * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ)) * (∑ a ∈ good, ∑' j, E_aj a j) := by
          rw [hswap_E]
      _ ≤ (3 * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ)) * ((384 * B + 5) * Real.log (X : ℝ)) := by
          gcongr
      _ = 3 * (384 * B + 5) * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ) := by ring
  -- Compare `(S / q^k) * ∑_{m=1}^{H'} χ̃(a+m)` with the `j`-sum using `tsum_ap_shift_sub_le` + `hS_ap`
  have hpt_err : ∀ a ∈ good, ∀ H' ∈ Finset.Icc (H + 1) (2 * H),
      (‖S‖ ^ 2 / ((q ^ k : ℕ) : ℝ) ^ 2) * ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2 ≤
      2 * ‖∑ m ∈ Finset.Icc 1 H', χt (a + m) *
        (∑' j : ℕ, h (a + (j + 1) * q ^ k + m) /
          Complex.ofReal (((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s)))‖ ^ 2 +
      Real.log (X : ℝ) ^ 2 / (2 * ((q ^ k : ℕ) : ℝ) ^ 2) := by
    intro a ha H' hH'
    have haI := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
    have hH'_le : H' ≤ 2 * H := (Finset.mem_Icc.mp hH').2
    set U : ℂ := (S / ((q ^ k : ℕ) : ℂ)) * ∑ m ∈ Finset.Icc 1 H', χt (a + m)
    set W : ℂ := ∑ m ∈ Finset.Icc 1 H', χt (a + m) *
      (∑' j : ℕ, h (a + (j + 1) * q ^ k + m) /
        Complex.ofReal (((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s)))
    have hUW : ‖U - W‖ ≤ Real.log (X : ℝ) / (2 * ((q ^ k : ℕ) : ℝ)) := by
      have hrew : U - W = ∑ m ∈ Finset.Icc 1 H', χt (a + m) *
          ((S / ((q ^ k : ℕ) : ℂ)) -
            (∑' j : ℕ, h (a + (j + 1) * q ^ k + m) /
              Complex.ofReal (((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s)))) := by
        dsimp [U, W]; rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun m _ => by ring
      rw [hrew]
      have hqk_le : ((q ^ k : ℕ) : ℝ) ≤ ((Qnat ^ k : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_le_pow_left hq_le_Qnat k
      have hshift_bd : 4 * (H : ℝ) + 1 ≤ (1 / (8 * (H : ℝ))) * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ) := by
        rw [le_div_iff₀ (by exact_mod_cast hqk_pos), one_div, inv_mul_eq_div,
          le_div_iff₀ (by positivity)]
        calc (4 * (H : ℝ) + 1) * ((q ^ k : ℕ) : ℝ) * (8 * (H : ℝ))
            = ((q ^ k : ℕ) : ℝ) * (8 * (H : ℝ)) * (4 * (H : ℝ) + 1) := by ring
          _ ≤ ((Qnat ^ k : ℕ) : ℝ) * (8 * (H : ℝ)) * (4 * (H : ℝ) + 1) := by gcongr
          _ ≤ Real.log (X : ℝ) := hlogX_shift
      calc ‖∑ m ∈ Finset.Icc 1 H', _‖
          ≤ ∑ m ∈ Finset.Icc 1 H', ‖χt (a + m) * _‖ := norm_sum_le _ _
        _ ≤ ∑ _m ∈ Finset.Icc 1 H', ((1 / (4 * (H : ℝ))) * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ)) := by
            refine Finset.sum_le_sum fun m hm => ?_
            have hmI := Finset.mem_Icc.mp hm
            rw [norm_mul, hχt_norm _ (by omega), one_mul, norm_sub_rev]
            let T2 : ℂ := ∑' n : ℕ, if (n + 1) % (q ^ k) = (a + m) % (q ^ k) then
              h (n + 1) / Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (1 + s)) else 0
            have h1 := tsum_ap_shift_sub_le hs_pos hqk_pos haI.1 haI.2 hmI.1
              (le_trans hmI.2 hH'_le) h hh_norm
            have h2 := hS_ap (a + m)
            have htri : ‖(∑' j : ℕ, h (a + (j + 1) * q ^ k + m) /
                  Complex.ofReal (((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s))) - S / ((q ^ k : ℕ) : ℂ)‖ ≤
                ‖(∑' j : ℕ, h (a + (j + 1) * q ^ k + m) /
                  Complex.ofReal (((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s))) - T2‖ +
                ‖T2 - S / ((q ^ k : ℕ) : ℂ)‖ := by
              have := norm_add_le
                ((∑' j : ℕ, h (a + (j + 1) * q ^ k + m) /
                  Complex.ofReal (((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s))) - T2)
                (T2 - S / ((q ^ k : ℕ) : ℂ))
              simpa using this
            have h2' : ‖T2 - S / ((q ^ k : ℕ) : ℂ)‖ ≤
                (1 / (8 * (H : ℝ))) * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ) := h2
            calc _ ≤ (4 * (H : ℝ) + 1) + (1 / (8 * (H : ℝ))) * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ) :=
                  htri.trans (add_le_add h1 h2')
              _ ≤ (1 / (8 * (H : ℝ))) * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ) +
                  (1 / (8 * (H : ℝ))) * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ) := by linarith
              _ = (1 / (4 * (H : ℝ))) * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ) := by ring
        _ = (H' : ℝ) * ((1 / (4 * (H : ℝ))) * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ)) := by
            simp [Nat.card_Icc]
        _ ≤ (2 * (H : ℝ)) * ((1 / (4 * (H : ℝ))) * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ)) := by
            gcongr; exact_mod_cast hH'_le
        _ = Real.log (X : ℝ) / (2 * ((q ^ k : ℕ) : ℝ)) := by
            field_simp [hH_real_pos.ne']; ring
    have hU_norm : ‖U‖ ^ 2 = (‖S‖ ^ 2 / ((q ^ k : ℕ) : ℝ) ^ 2) *
        ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2 := by
      dsimp [U]
      rw [norm_mul, norm_div, Complex.norm_natCast, mul_pow, div_pow]
    have htri : ‖U‖ ≤ ‖W‖ + ‖U - W‖ := by
      have := norm_add_le W (U - W); simpa [add_sub_cancel] using this
    have hsq : ‖U‖ ^ 2 ≤ 2 * ‖W‖ ^ 2 + 2 * ‖U - W‖ ^ 2 := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) htri 2
      nlinarith [sq_nonneg (‖W‖ - ‖U - W‖)]
    have herr_sq : 2 * ‖U - W‖ ^ 2 ≤ Real.log (X : ℝ) ^ 2 / (2 * ((q ^ k : ℕ) : ℝ) ^ 2) := by
      have h1 := pow_le_pow_left₀ (norm_nonneg _) hUW 2
      have hrew : 2 * (Real.log (X : ℝ) / (2 * ((q ^ k : ℕ) : ℝ))) ^ 2 =
          Real.log (X : ℝ) ^ 2 / (2 * ((q ^ k : ℕ) : ℝ) ^ 2) := by ring
      nlinarith [h1, hrew]
    rw [← hU_norm]; linarith
  have hcard_good : (good.card : ℝ) ≤ ((q ^ k : ℕ) : ℝ) := by
    have : good.card ≤ (Finset.Icc 1 (q ^ k)).card := Finset.card_filter_le _ _
    simp only [Nat.card_Icc, Nat.add_sub_cancel] at this
    exact_mod_cast this
  have hcard_H' : (Finset.Icc (H + 1) (2 * H)).card = H := by simp [Nat.card_Icc]; omega
  have hcomb : (‖S‖ ^ 2 / ((q ^ k : ℕ) : ℝ) ^ 2) *
      ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ good,
        ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2) ≤
      (6 * (384 * B + 5) + 1) * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ) := by
    calc _ = (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ good,
          ((‖S‖ ^ 2 / ((q ^ k : ℕ) : ℝ) ^ 2) * ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2) := by
          simp_rw [← Finset.mul_sum]; ring
      _ ≤ (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ good,
          (2 * ‖∑ m ∈ Finset.Icc 1 H', χt (a + m) *
            (∑' j : ℕ, h (a + (j + 1) * q ^ k + m) /
              Complex.ofReal (((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s)))‖ ^ 2 +
            Real.log (X : ℝ) ^ 2 / (2 * ((q ^ k : ℕ) : ℝ) ^ 2)) := by
          gcongr; exact hpt_err _ ‹_› _ ‹_›
      _ = 2 * ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ good,
            ‖∑ m ∈ Finset.Icc 1 H', χt (a + m) *
              (∑' j : ℕ, h (a + (j + 1) * q ^ k + m) /
                Complex.ofReal (((a + (j + 1) * q ^ k : ℕ) : ℝ) ^ (1 + s)))‖ ^ 2) +
          (good.card : ℝ) * (Real.log (X : ℝ) ^ 2 / (2 * ((q ^ k : ℕ) : ℝ) ^ 2)) := by
          simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
            hcard_H']
          field_simp [hH_real_pos.ne']
      _ ≤ 2 * (3 * (384 * B + 5) * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ)) +
          ((q ^ k : ℕ) : ℝ) * (Real.log (X : ℝ) ^ 2 / (2 * ((q ^ k : ℕ) : ℝ) ^ 2)) := by
          gcongr
      _ ≤ (6 * (384 * B + 5) + 1) * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ) := by
          have hqk_r : (0 : ℝ) < ((q ^ k : ℕ) : ℝ) := by exact_mod_cast hqk_pos
          have hhalf : ((q ^ k : ℕ) : ℝ) * (Real.log (X : ℝ) ^ 2 / (2 * ((q ^ k : ℕ) : ℝ) ^ 2)) =
              (1 / 2) * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ) := by
            field_simp [hqk_r.ne']
          rw [hhalf]
          have hnn : 0 ≤ Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ) := by positivity
          have hrew : (6 * (384 * B + 5) + 1) * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ) -
              (2 * (3 * (384 * B + 5) * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ)) +
                (1 / 2) * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ)) =
              (1 / 2) * (Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ)) := by ring
          linarith [hrew, hnn]
  have hS2_lb : c ^ 2 * Real.log (X : ℝ) ^ 2 ≤ ‖S‖ ^ 2 := by
    calc c ^ 2 * Real.log (X : ℝ) ^ 2 = (c * Real.log (X : ℝ)) ^ 2 := by ring
      _ ≤ ‖S‖ ^ 2 := pow_le_pow_left₀ (by positivity) hS_lb 2
  have hqk_r : (0 : ℝ) < ((q ^ k : ℕ) : ℝ) := by exact_mod_cast hqk_pos
  have hLHS_nn : 0 ≤ (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ good,
      ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2 := by
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have hstep1 : (c ^ 2 * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ) ^ 2) *
      ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ good,
        ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2) ≤
      (6 * (384 * B + 5) + 1) * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ) := by
    refine le_trans ?_ hcomb
    gcongr
  have hpos_fac : 0 < c ^ 2 * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ) ^ 2 := by positivity
  have hstep2 : (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ good,
      ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2 ≤
      ((6 * (384 * B + 5) + 1) * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ)) /
        (c ^ 2 * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ) ^ 2) :=
    (le_div_iff₀' hpos_fac).mpr hstep1
  have hsimp_rhs : ((6 * (384 * B + 5) + 1) * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ)) /
      (c ^ 2 * Real.log (X : ℝ) ^ 2 / ((q ^ k : ℕ) : ℝ) ^ 2) = C₀ * ((q ^ k : ℕ) : ℝ) := by
    rw [hC₀_eq]
    field_simp [hc_pos.ne', hlogX_pos.ne', hqk_r.ne']
  rwa [hsimp_rhs] at hstep2


/- ### Helper 9: Reinstating bad residue classes and Granville's Pythagorean identity -/

private lemma step10_full_Asum_pythag {C₀ Q : ℝ} {H k q : ℕ}
    (_hQ1 : 1 ≤ Q) (hH_pos : 1 ≤ H) (hk_ge1 : 1 ≤ k) (hq2 : 2 ≤ q) (hqQ : (q : ℝ) ≤ Q)
    (h2k_large : 8 * (H : ℝ) ^ 3 * Q ≤ (2 : ℝ) ^ k)
    (χ : DirichletCharacter ℂ q) (hχ_prim : χ.IsPrimitive) (χt : ℕ → ℂ)
    (hχt_mul : ∀ a b, χt (a * b) = χt a * χt b)
    (hχt_norm : ∀ n, 1 ≤ n → ‖χt n‖ = 1)
    (hχt_coprime : ∀ n, 1 ≤ n → Nat.Coprime n q → χt n = χ (n : ZMod q))
    (hcontra410 : (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
      ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a =>
          ∀ p : ℕ, p.Prime → p ∣ q → ∀ m ∈ Finset.Icc 1 (2 * H), ¬ (p ^ k ∣ a + m)),
        ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2 ≤ C₀ * ((q ^ k : ℕ) : ℝ)) :
    ∑ d ∈ (q ^ (k - 1)).divisors, (1 / (H : ℝ)) *
      ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ Finset.Icc 1 (q ^ k),
        ‖∑ m ∈ (Finset.Icc 1 H').filter (fun m => d ∣ a + m),
          χ (((a + m) / d : ℕ) : ZMod q)‖ ^ 2 ≤ (C₀ + 1) * ((q ^ k : ℕ) : ℝ) := by
  have hH_real_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH_pos
  have hqpos : 0 < q := by omega
  have hqk_pos : 0 < q ^ k := pow_pos hqpos k
  let good : Finset ℕ := (Finset.Icc 1 (q ^ k)).filter fun a =>
    ∀ p : ℕ, p.Prime → p ∣ q → ∀ m ∈ Finset.Icc 1 (2 * H), ¬ (p ^ k ∣ a + m)
  let Bsum : ℕ → ℕ → ℕ → ℂ := fun d a H' =>
    ∑ m ∈ (Finset.Icc 1 H').filter (fun m => d ∣ a + m), χ (((a + m) / d : ℕ) : ZMod q)
  let Asum : ℕ → ℕ → ℂ := fun a H' =>
    ∑ d ∈ (q ^ (k - 1)).divisors, χt d * Bsum d a H'
  -- Step 10a: `Asum a H' = ∑_{m=1}^{H'} χ̃(a+m)` for `a ∈ good`, and `‖Asum a H'‖ ≤ 2*H` for all `a`
  have hAsum_good : ∀ a ∈ good, ∀ H' ∈ Finset.Icc (H + 1) (2 * H),
      Asum a H' = ∑ m ∈ Finset.Icc 1 H', χt (a + m) := by
    intro a ha H' hH'
    have ha' := Finset.mem_filter.mp ha
    have haI := Finset.mem_Icc.mp ha'.1
    have hH'_le : H' ≤ 2 * H := (Finset.mem_Icc.mp hH').2
    dsimp [Asum, Bsum]
    simp_rw [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm2H : m ∈ Finset.Icc 1 (2 * H) := Finset.Icc_subset_Icc_right hH'_le hm
    have ham_pos : 0 < a + m := by omega
    let d₀ : ℕ := Nat.gcd (a + m) (q ^ k)
    have hd₀_pos : 0 < d₀ := Nat.gcd_pos_of_pos_left _ ham_pos
    have hd₀_dvd_am : d₀ ∣ a + m := Nat.gcd_dvd_left _ _
    have hd₀_dvd_qk : d₀ ∣ q ^ k := Nat.gcd_dvd_right _ _
    obtain ⟨hd₀_dvd_qk1, hcop₀⟩ := good_gcd_props hqpos ha'.1 ha'.2 hm2H
    have hd₀_mem : d₀ ∈ (q ^ (k - 1)).divisors :=
      Nat.mem_divisors.mpr ⟨hd₀_dvd_qk1, (pow_pos hqpos _).ne'⟩
    rw [Finset.sum_eq_single d₀]
    · rw [if_pos hd₀_dvd_am]
      have hq_pos : 1 ≤ (a + m) / d₀ := Nat.div_pos (Nat.le_of_dvd ham_pos hd₀_dvd_am) hd₀_pos
      rw [← hχt_coprime _ hq_pos hcop₀, ← hχt_mul, Nat.mul_div_cancel' hd₀_dvd_am]
    · intro d hd hne
      by_cases hdd : d ∣ a + m
      · rw [if_pos hdd]
        have : NeZero q := ⟨hqpos.ne'⟩
        have hnot_cop : ¬ Nat.Coprime ((a + m) / d) q := by
          intro hcop
          apply hne
          have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdd ham_pos
          have hd_dvd_qk1 : d ∣ q ^ (k - 1) := (Nat.mem_divisors.mp hd).1
          apply Nat.eq_of_factorization_eq hd_pos.ne' hd₀_pos.ne'
          intro p
          by_cases hp : p.Prime
          · by_cases hpq : p ∣ q
            · have hnd_quot : ¬ (p ∣ (a + m) / d) := fun h =>
                hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h hpq)
              have hvp_q : ((a + m) / d).factorization p = 0 :=
                Nat.factorization_eq_zero_of_not_dvd hnd_quot
              have hvp_d : d.factorization p = (a + m).factorization p := by
                have h := Nat.factorization_div hdd
                have hp_eq := congrFun (congrArg DFunLike.coe h) p
                simp only [Finsupp.tsub_apply] at hp_eq
                have hle := (Nat.factorization_le_iff_dvd hd_pos.ne' ham_pos.ne').mpr hdd p
                omega
              have hnot : ¬ (p ^ k ∣ a + m) := ha'.2 p hp hpq m hm2H
              have hvp_lt : (a + m).factorization p < k := by
                by_contra hge; push Not at hge
                exact hnot (dvd_trans (pow_dvd_pow p hge) (Nat.ordProj_dvd (a + m) p))
              have hvp_q1 : 1 ≤ q.factorization p := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp (by
                rw [Nat.support_factorization]; exact Nat.mem_primeFactors.mpr ⟨hp, hpq, hqpos.ne'⟩))
              have hvp_d0 : d₀.factorization p = (a + m).factorization p := by
                rw [Nat.factorization_gcd ham_pos.ne' hqk_pos.ne', Finsupp.inf_apply,
                  Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
                exact min_eq_left (le_trans (by omega : (a + m).factorization p ≤ k) (Nat.le_mul_of_pos_right _ hvp_q1))
              rw [hvp_d, hvp_d0]
            · have hvp_q : q.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpq
              have h1 := (Nat.factorization_le_iff_dvd hd_pos.ne' (pow_pos hqpos _).ne').mpr hd_dvd_qk1 p
              have h2 := (Nat.factorization_le_iff_dvd hd₀_pos.ne' hqk_pos.ne').mpr hd₀_dvd_qk p
              rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hvp_q, mul_zero] at h1 h2
              omega
          · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
        have hnu : ¬ IsUnit (((a + m) / d : ℕ) : ZMod q) := by
          rwa [ZMod.isUnit_iff_coprime]
        rw [MulChar.map_nonunit χ hnu, mul_zero]
      · rw [if_neg hdd]
    · intro habs; exact absurd hd₀_mem habs
  have hAsum_bd : ∀ a ∈ Finset.Icc 1 (q ^ k), ∀ H' ∈ Finset.Icc (H + 1) (2 * H),
      ‖Asum a H'‖ ≤ 2 * (H : ℝ) := by
    intro a ha H' hH'
    have ha1 := (Finset.mem_Icc.mp ha).1
    have hH'_le : H' ≤ 2 * H := (Finset.mem_Icc.mp hH').2
    dsimp [Asum, Bsum]
    simp_rw [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    calc ‖∑ m ∈ Finset.Icc 1 H', ∑ d ∈ (q ^ (k - 1)).divisors, _‖
        ≤ ∑ m ∈ Finset.Icc 1 H', ‖∑ d ∈ (q ^ (k - 1)).divisors, _‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Finset.Icc 1 H', (1 : ℝ) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have ham_pos : 0 < a + m := by omega
          have : NeZero q := ⟨hqpos.ne'⟩
          -- At most one divisor `d ∈ (q^(k-1)).divisors` gives a nonzero summand
          by_cases hex : ∃ d ∈ (q ^ (k - 1)).divisors, d ∣ a + m ∧ Nat.Coprime ((a + m) / d) q
          · obtain ⟨d₀, hd₀_mem, hd₀_dvd, hd₀_cop⟩ := hex
            rw [Finset.sum_eq_single d₀]
            · rw [if_pos hd₀_dvd, norm_mul,
                hχt_norm d₀ (Nat.pos_of_dvd_of_pos hd₀_dvd ham_pos), one_mul]
              exact dirichlet_norm_le_one χ _
            · intro d hd hne
              by_cases hdd : d ∣ a + m
              · rw [if_pos hdd]
                have hnc : ¬ Nat.Coprime ((a + m) / d) q := by
                  intro hcop
                  apply hne
                  have hd_pos : 0 < d := Nat.pos_of_dvd_of_pos hdd ham_pos
                  have hd₀_pos : 0 < d₀ := Nat.pos_of_dvd_of_pos hd₀_dvd ham_pos
                  apply Nat.eq_of_factorization_eq hd_pos.ne' hd₀_pos.ne'
                  intro p
                  by_cases hp : p.Prime
                  · by_cases hpq : p ∣ q
                    · have hnd1 : ¬ (p ∣ (a + m) / d) := fun h =>
                        hp.not_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h hpq)
                      have hnd2 : ¬ (p ∣ (a + m) / d₀) := fun h =>
                        hp.not_dvd_one (hd₀_cop.gcd_eq_one ▸ Nat.dvd_gcd h hpq)
                      have hq1 : ((a + m) / d).factorization p = 0 :=
                        Nat.factorization_eq_zero_of_not_dvd hnd1
                      have hq2 : ((a + m) / d₀).factorization p = 0 :=
                        Nat.factorization_eq_zero_of_not_dvd hnd2
                      have h1 := congrFun (congrArg DFunLike.coe (Nat.factorization_div hdd)) p
                      have h2 := congrFun (congrArg DFunLike.coe (Nat.factorization_div hd₀_dvd)) p
                      simp only [Finsupp.tsub_apply] at h1 h2
                      have hl1 := (Nat.factorization_le_iff_dvd hd_pos.ne' ham_pos.ne').mpr hdd p
                      have hl2 := (Nat.factorization_le_iff_dvd hd₀_pos.ne' ham_pos.ne').mpr hd₀_dvd p
                      omega
                    · have hvp_q : q.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd hpq
                      have h1 := (Nat.factorization_le_iff_dvd hd_pos.ne' (pow_pos hqpos _).ne').mpr
                        (Nat.mem_divisors.mp hd).1 p
                      have h2 := (Nat.factorization_le_iff_dvd hd₀_pos.ne' (pow_pos hqpos _).ne').mpr
                        (Nat.mem_divisors.mp hd₀_mem).1 p
                      rw [Nat.factorization_pow, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, hvp_q, mul_zero] at h1 h2
                      omega
                  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
                rw [MulChar.map_nonunit χ (by rwa [ZMod.isUnit_iff_coprime]), mul_zero]
              · rw [if_neg hdd]
            · intro habs; exact absurd hd₀_mem habs
          · push Not at hex
            have hzero : ∑ d ∈ (q ^ (k - 1)).divisors,
                (if d ∣ a + m then χt d * χ (((a + m) / d : ℕ) : ZMod q) else 0) = 0 := by
              refine Finset.sum_eq_zero fun d hd => ?_
              by_cases hdd : d ∣ a + m
              · rw [if_pos hdd]
                have hnc := hex d hd hdd
                rw [MulChar.map_nonunit χ (by rwa [ZMod.isUnit_iff_coprime]), mul_zero]
              · rw [if_neg hdd]
            rw [hzero, norm_zero]; norm_num
      _ = (H' : ℝ) := by simp [Nat.card_Icc]
      _ ≤ 2 * (H : ℝ) := by exact_mod_cast hH'_le
  -- Step 10b: Count bad `a ∈ Icc 1 (q^k)` and bound the full sum `∑_{a ∈ Icc 1 (q^k)} ‖Asum a H'‖^2`
  let bad : Finset ℕ := (Finset.Icc 1 (q ^ k)) \ good
  have hbad_card : (bad.card : ℝ) ≤ 2 * (H : ℝ) * Q * (((q ^ k : ℕ) : ℝ) / (2 : ℝ) ^ k) := by
    -- Every `a ∈ bad` lies in `S(p, m) = {a ∈ Icc 1 (q^k) | p^k ∣ a + m}` for some `p ∈ q.primeFactors`, `m ∈ Icc 1 (2H)`
    have hcov : bad ⊆ q.primeFactors.biUnion fun p =>
        (Finset.Icc 1 (2 * H)).biUnion fun m =>
          (Finset.Icc 1 (q ^ k)).filter fun a => p ^ k ∣ a + m := by
      intro a ha
      have ha' := Finset.mem_sdiff.mp ha
      have hnot : ¬ (∀ p : ℕ, p.Prime → p ∣ q → ∀ m ∈ Finset.Icc 1 (2 * H), ¬ (p ^ k ∣ a + m)) :=
        fun h => ha'.2 (Finset.mem_filter.mpr ⟨ha'.1, h⟩)
      push Not at hnot
      obtain ⟨p, hp, hpq, m, hm, hdvd⟩ := hnot
      exact Finset.mem_biUnion.mpr ⟨p, Nat.mem_primeFactors.mpr ⟨hp, hpq, hqpos.ne'⟩,
        Finset.mem_biUnion.mpr ⟨m, hm, Finset.mem_filter.mpr ⟨ha'.1, hdvd⟩⟩⟩
    have hslice_card : ∀ p ∈ q.primeFactors, ∀ m ∈ Finset.Icc 1 (2 * H),
        (((Finset.Icc 1 (q ^ k)).filter fun a => p ^ k ∣ a + m).card : ℝ) ≤
        ((q ^ k : ℕ) : ℝ) / (2 : ℝ) ^ k := by
      intro p hp m _
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpq := Nat.dvd_of_mem_primeFactors hp
      have hpk_pos : 0 < p ^ k := pow_pos hpp.pos k
      have hpk_dvd : p ^ k ∣ q ^ k := pow_dvd_pow_of_dvd hpq k
      let φ : ℕ → ℕ := fun a => (a - 1) / (p ^ k)
      have hinj : Set.InjOn φ (((Finset.Icc 1 (q ^ k)).filter fun a => p ^ k ∣ a + m) : Set ℕ) := by
        intro a₁ ha₁ a₂ ha₂ hEq
        have h1 := Finset.mem_filter.mp ha₁
        have h2 := Finset.mem_filter.mp ha₂
        have ha₁1 := (Finset.mem_Icc.mp h1.1).1
        have ha₂1 := (Finset.mem_Icc.mp h2.1).1
        have hmod : (a₁ - 1) % (p ^ k) = (a₂ - 1) % (p ^ k) := by
          have hm1 : (a₁ - 1 + (m + 1)) % (p ^ k) = 0 := by
            have : a₁ - 1 + (m + 1) = a₁ + m := by omega
            rw [this]; exact Nat.mod_eq_zero_of_dvd h1.2
          have hm2 : (a₂ - 1 + (m + 1)) % (p ^ k) = 0 := by
            have : a₂ - 1 + (m + 1) = a₂ + m := by omega
            rw [this]; exact Nat.mod_eq_zero_of_dvd h2.2
          exact Nat.ModEq.add_right_cancel' (m + 1) (hm1.trans hm2.symm)
        have hdm1 := Nat.div_add_mod (a₁ - 1) (p ^ k)
        have hdm2 := Nat.div_add_mod (a₂ - 1) (p ^ k)
        dsimp [φ] at hEq
        rw [hEq, hmod] at hdm1
        omega
      have himg : Finset.image φ ((Finset.Icc 1 (q ^ k)).filter fun a => p ^ k ∣ a + m) ⊆
          Finset.range (q ^ k / p ^ k) := by
        intro t ht
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp ht
        rw [Finset.mem_range]
        have haI := Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1
        have hlt : a - 1 < (q ^ k / p ^ k) * p ^ k := by
          rw [Nat.div_mul_cancel hpk_dvd]; omega
        exact (Nat.div_lt_iff_lt_mul hpk_pos).mpr hlt
      have hcard_nat : ((Finset.Icc 1 (q ^ k)).filter fun a => p ^ k ∣ a + m).card ≤ q ^ k / p ^ k := by
        calc _ = (Finset.image φ _).card := (Finset.card_image_of_injOn hinj).symm
          _ ≤ (Finset.range (q ^ k / p ^ k)).card := Finset.card_le_card himg
          _ = q ^ k / p ^ k := Finset.card_range _
      have h2k_le : (2 : ℝ) ^ k ≤ ((p ^ k : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_le_pow_left hpp.two_le k
      calc (((Finset.Icc 1 (q ^ k)).filter fun a => p ^ k ∣ a + m).card : ℝ)
          ≤ ((q ^ k / p ^ k : ℕ) : ℝ) := by exact_mod_cast hcard_nat
        _ = ((q ^ k : ℕ) : ℝ) / ((p ^ k : ℕ) : ℝ) := by
            rw [Nat.cast_div hpk_dvd (by positivity)]
        _ ≤ ((q ^ k : ℕ) : ℝ) / (2 : ℝ) ^ k :=
            div_le_div_of_nonneg_left (by positivity) (by positivity) h2k_le
    have hpf_card : (q.primeFactors.card : ℝ) ≤ Q := by
      have hsub : q.primeFactors ⊆ Finset.Icc 1 q := fun p hp => Finset.mem_Icc.mpr
        ⟨(Nat.prime_of_mem_primeFactors hp).pos, Nat.le_of_dvd hqpos (Nat.dvd_of_mem_primeFactors hp)⟩
      have h1 : q.primeFactors.card ≤ q := by
        have := Finset.card_le_card hsub; simpa [Nat.card_Icc] using this
      exact le_trans (by exact_mod_cast h1) hqQ
    calc (bad.card : ℝ)
        ≤ ((q.primeFactors.biUnion fun p => (Finset.Icc 1 (2 * H)).biUnion fun m =>
            (Finset.Icc 1 (q ^ k)).filter fun a => p ^ k ∣ a + m).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hcov
      _ ≤ ∑ p ∈ q.primeFactors, (((Finset.Icc 1 (2 * H)).biUnion fun m =>
            (Finset.Icc 1 (q ^ k)).filter fun a => p ^ k ∣ a + m).card : ℝ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ p ∈ q.primeFactors, ∑ m ∈ Finset.Icc 1 (2 * H),
            (((Finset.Icc 1 (q ^ k)).filter fun a => p ^ k ∣ a + m).card : ℝ) := by
          refine Finset.sum_le_sum fun p _ => by exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ q.primeFactors, ∑ _m ∈ Finset.Icc 1 (2 * H), (((q ^ k : ℕ) : ℝ) / (2 : ℝ) ^ k) := by
          refine Finset.sum_le_sum fun p hp => Finset.sum_le_sum fun m hm => hslice_card p hp m hm
      _ = (q.primeFactors.card : ℝ) * (2 * (H : ℝ)) * (((q ^ k : ℕ) : ℝ) / (2 : ℝ) ^ k) := by
          simp [Nat.card_Icc, Nat.cast_mul]; ring
      _ ≤ Q * (2 * (H : ℝ)) * (((q ^ k : ℕ) : ℝ) / (2 : ℝ) ^ k) := by gcongr
      _ = 2 * (H : ℝ) * Q * (((q ^ k : ℕ) : ℝ) / (2 : ℝ) ^ k) := by ring
  have hfull_Asum : (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
      ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Asum a H'‖ ^ 2 ≤ (C₀ + 1) * ((q ^ k : ℕ) : ℝ) := by
    have hsplit : ∀ H' ∈ Finset.Icc (H + 1) (2 * H),
        ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Asum a H'‖ ^ 2 ≤
        (∑ a ∈ good, ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2) +
        (bad.card : ℝ) * (4 * (H : ℝ) ^ 2) := by
      intro H' hH'
      have hunion : Finset.Icc 1 (q ^ k) = good ∪ bad :=
        (Finset.union_sdiff_of_subset (Finset.filter_subset _ _)).symm
      have hdisj : Disjoint good bad := Finset.disjoint_sdiff
      rw [hunion, Finset.sum_union hdisj]
      refine add_le_add ?_ ?_
      · exact le_of_eq (Finset.sum_congr rfl fun a ha => by rw [hAsum_good a ha H' hH'])
      · calc ∑ a ∈ bad, ‖Asum a H'‖ ^ 2
            ≤ ∑ _a ∈ bad, (4 * (H : ℝ) ^ 2) := by
              refine Finset.sum_le_sum fun a ha => ?_
              have haI := (Finset.mem_sdiff.mp ha).1
              calc ‖Asum a H'‖ ^ 2 ≤ (2 * (H : ℝ)) ^ 2 :=
                    pow_le_pow_left₀ (norm_nonneg _) (hAsum_bd a haI H' hH') 2
                _ = 4 * (H : ℝ) ^ 2 := by ring
          _ = (bad.card : ℝ) * (4 * (H : ℝ) ^ 2) := by simp
    have hcard_H' : (Finset.Icc (H + 1) (2 * H)).card = H := by simp [Nat.card_Icc]; omega
    have hbad_small : (bad.card : ℝ) * (4 * (H : ℝ) ^ 2) ≤ ((q ^ k : ℕ) : ℝ) := by
      calc (bad.card : ℝ) * (4 * (H : ℝ) ^ 2)
          ≤ (2 * (H : ℝ) * Q * (((q ^ k : ℕ) : ℝ) / (2 : ℝ) ^ k)) * (4 * (H : ℝ) ^ 2) := by gcongr
        _ = (8 * (H : ℝ) ^ 3 * Q / (2 : ℝ) ^ k) * ((q ^ k : ℕ) : ℝ) := by ring
        _ ≤ 1 * ((q ^ k : ℕ) : ℝ) := by
            gcongr; rw [div_le_one (by positivity)]; exact h2k_large
        _ = ((q ^ k : ℕ) : ℝ) := one_mul _
    calc (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Asum a H'‖ ^ 2
        ≤ (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
            ((∑ a ∈ good, ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2) +
              (bad.card : ℝ) * (4 * (H : ℝ) ^ 2)) := by gcongr; exact hsplit _ ‹_›
      _ = ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
            ∑ a ∈ good, ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2) +
          (bad.card : ℝ) * (4 * (H : ℝ) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, hcard_H', nsmul_eq_mul]
          field_simp [hH_real_pos.ne']
      _ ≤ C₀ * ((q ^ k : ℕ) : ℝ) + ((q ^ k : ℕ) : ℝ) := add_le_add hcontra410 hbad_small
      _ = (C₀ + 1) * ((q ^ k : ℕ) : ℝ) := by ring
  -- Step 10c: Pythagorean orthogonality of `Bsum d` via Granville's off-diagonal cancellation
  have hpythag : ∀ H' : ℕ,
      ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Asum a H'‖ ^ 2 =
      ∑ d ∈ (q ^ (k - 1)).divisors, ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum d a H'‖ ^ 2 := by
    intro H'
    -- Lift to `ℂ` via `((‖z‖ ^ 2 : ℝ) : ℂ) = z * star z`
    apply Complex.ofReal_injective
    push_cast
    have hnorm_sq : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = z * star z := fun z => by
      rw [Complex.star_def, Complex.mul_conj']
    simp_rw [hnorm_sq]
    have hcross : ∀ d₁ ∈ (q ^ (k - 1)).divisors, ∀ d₂ ∈ (q ^ (k - 1)).divisors, d₁ ≠ d₂ →
        ∑ a ∈ Finset.Icc 1 (q ^ k), Bsum d₁ a H' * star (Bsum d₂ a H') = 0 := by
      intro d₁ hd₁ d₂ hd₂ hne
      have hd₁' := (Nat.mem_divisors.mp hd₁).1
      have hd₂' := (Nat.mem_divisors.mp hd₂).1
      have hexp : ∀ a, Bsum d₁ a H' * star (Bsum d₂ a H') =
          ∑ m₁ ∈ Finset.Icc 1 H', ∑ m₂ ∈ Finset.Icc 1 H',
            if d₁ ∣ a + m₁ ∧ d₂ ∣ a + m₂ then
              χ (((a + m₁) / d₁ : ℕ) : ZMod q) * star (χ (((a + m₂) / d₂ : ℕ) : ZMod q))
            else 0 := by
        intro a
        dsimp [Bsum]
        rw [map_sum, Finset.sum_mul]
        simp_rw [Finset.mul_sum, Finset.sum_filter]
        refine Finset.sum_congr rfl fun m₁ _ => ?_
        by_cases h1 : d₁ ∣ a + m₁
        · simp only [h1, true_and, ↓reduceIte]
        · simp [h1]
      simp_rw [hexp]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun m₁ _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun m₂ _ => ?_
      exact granville_off_diagonal_zero hq2 hk_ge1 χ hχ_prim hd₁' hd₂' hne
    calc ∑ a ∈ Finset.Icc 1 (q ^ k), Asum a H' * star (Asum a H')
        = ∑ a ∈ Finset.Icc 1 (q ^ k), ∑ d₁ ∈ (q ^ (k - 1)).divisors, ∑ d₂ ∈ (q ^ (k - 1)).divisors,
            (χt d₁ * star (χt d₂)) * (Bsum d₁ a H' * star (Bsum d₂ a H')) := by
          refine Finset.sum_congr rfl fun a _ => ?_
          dsimp [Asum]
          rw [map_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun d₁ _ => ?_
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun d₂ _ => ?_
          rw [map_mul]; ring
      _ = ∑ d₁ ∈ (q ^ (k - 1)).divisors, ∑ d₂ ∈ (q ^ (k - 1)).divisors,
            (χt d₁ * star (χt d₂)) * ∑ a ∈ Finset.Icc 1 (q ^ k), Bsum d₁ a H' * star (Bsum d₂ a H') := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d₁ _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun d₂ _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ d₁ ∈ (q ^ (k - 1)).divisors,
            (χt d₁ * star (χt d₁)) * ∑ a ∈ Finset.Icc 1 (q ^ k), Bsum d₁ a H' * star (Bsum d₁ a H') := by
          refine Finset.sum_congr rfl fun d₁ hd₁ => ?_
          rw [Finset.sum_eq_single d₁]
          · intro d₂ hd₂ hne; rw [hcross d₁ hd₁ d₂ hd₂ (Ne.symm hne), mul_zero]
          · intro habs; exact absurd hd₁ habs
      _ = ∑ d ∈ (q ^ (k - 1)).divisors, ∑ a ∈ Finset.Icc 1 (q ^ k), Bsum d a H' * star (Bsum d a H') := by
          refine Finset.sum_congr rfl fun d hd => ?_
          have hd_pos : 1 ≤ d := Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hd).1 (pow_pos hqpos _)
          rw [Complex.star_def, Complex.mul_conj', hχt_norm d hd_pos]; norm_num
  calc ∑ d ∈ (q ^ (k - 1)).divisors, (1 / (H : ℝ)) *
          ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum d a H'‖ ^ 2
      = (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
          ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Asum a H'‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1; refine Finset.sum_congr rfl fun H' _ => (hpythag H').symm
    _ ≤ (C₀ + 1) * ((q ^ k : ℕ) : ℝ) := hfull_Asum


/- ### Helper 10: Diagonal `d = q^i` lower bound and final contradiction -/

private lemma step10_sum_a_lb {q k i : ℕ} (hq2 : 2 ≤ q) (hi1_le_k : i + 1 ≤ k)
    (χ : DirichletCharacter ℂ q) (H' : ℕ) :
    ((q ^ (k - 1) : ℕ) : ℝ) ≤
      ∑ a ∈ Finset.Icc 1 (q ^ k), ‖χ ((((a + H') / q ^ i + 1 : ℕ) : ZMod q))‖ ^ 2 := by
  have hqpos : 0 < q := by omega
  have hqk_pos : 0 < q ^ k := pow_pos hqpos k
  have hqi_pos : 0 < q ^ i := pow_pos hqpos i
  have hq_dvd_qki : q ∣ q ^ (k - i) := by
    have : 1 ≤ k - i := by omega
    rw [← Nat.sub_add_cancel this, pow_succ]; exact dvd_mul_left _ _
  -- Reindex `a ∈ Icc 1 (q^k)` by `u = (a + H') % q^k ∈ range (q^k)`
  have hbij : ∑ a ∈ Finset.Icc 1 (q ^ k), ‖χ ((((a + H') / q ^ i + 1 : ℕ) : ZMod q))‖ ^ 2 =
      ∑ u ∈ Finset.range (q ^ k), ‖χ (((u / q ^ i + 1 : ℕ) : ZMod q))‖ ^ 2 := by
    refine Finset.sum_bij (fun a _ => (a + H') % q ^ k) ?_ ?_ ?_ ?_
    · intro a _; exact Finset.mem_range.mpr (Nat.mod_lt _ hqk_pos)
    · intro a₁ ha₁ a₂ ha₂ hEq
      have h1 := Finset.mem_Icc.mp ha₁
      have h2 := Finset.mem_Icc.mp ha₂
      have hm : a₁ % q ^ k = a₂ % q ^ k := Nat.ModEq.add_right_cancel' H' hEq
      by_cases hlt1 : a₁ < q ^ k
      · by_cases hlt2 : a₂ < q ^ k
        · rw [Nat.mod_eq_of_lt hlt1, Nat.mod_eq_of_lt hlt2] at hm; exact hm
        · have ha2eq : a₂ = q ^ k := by omega
          rw [Nat.mod_eq_of_lt hlt1, ha2eq, Nat.mod_self] at hm; omega
      · have ha1eq : a₁ = q ^ k := by omega
        by_cases hlt2 : a₂ < q ^ k
        · rw [ha1eq, Nat.mod_self, Nat.mod_eq_of_lt hlt2] at hm; omega
        · omega
    · intro u hu
      have hu_lt := Finset.mem_range.mp hu
      let r0 := (u + (q ^ k - H' % q ^ k)) % q ^ k
      let a := if r0 = 0 then q ^ k else r0
      refine ⟨a, Finset.mem_Icc.mpr ?_, ?_⟩
      · by_cases hr0 : r0 = 0
        · simp only [a, hr0, ↓reduceIte]; exact ⟨hqk_pos, le_rfl⟩
        · simp only [a, hr0, ↓reduceIte]
          exact ⟨Nat.pos_of_ne_zero hr0, (Nat.mod_lt _ hqk_pos).le⟩
      · have ha_mod : a % q ^ k = r0 := by
          by_cases hr0 : r0 = 0
          · simp [a, hr0]
          · simp only [a, hr0, ↓reduceIte]
            exact Nat.mod_eq_of_lt (Nat.mod_lt _ hqk_pos)
        rw [Nat.add_mod, ha_mod]
        have hrem : H' % q ^ k ≤ q ^ k := (Nat.mod_lt _ hqk_pos).le
        have hstep : (u + (q ^ k - H' % q ^ k)) % q ^ k + H' % q ^ k ≡ u [MOD q ^ k] := by
          calc (u + (q ^ k - H' % q ^ k)) % q ^ k + H' % q ^ k
              ≡ (u + (q ^ k - H' % q ^ k)) + H' % q ^ k [MOD q ^ k] :=
                (Nat.mod_modEq _ _).add_right _
            _ = u + q ^ k := by omega
            _ ≡ u [MOD q ^ k] := by simp [Nat.ModEq]
        dsimp [r0]
        simpa [Nat.ModEq, Nat.mod_eq_of_lt hu_lt] using hstep
    · intro a _
      have hmod_z : ((((a + H') / q ^ i + 1 : ℕ) : ZMod q)) =
          ((((a + H') % q ^ k) / q ^ i + 1 : ℕ) : ZMod q) := by
        have hdm := Nat.div_add_mod (a + H') (q ^ k)
        have hqk_fac : q ^ k = q ^ i * q ^ (k - i) := by
          rw [← pow_add, Nat.add_sub_cancel' (by omega)]
        have h1 : a + H' = q ^ i * (((a + H') / q ^ k) * q ^ (k - i)) + (a + H') % q ^ k := by
          calc a + H' = q ^ k * ((a + H') / q ^ k) + (a + H') % q ^ k := hdm.symm
            _ = (q ^ i * q ^ (k - i)) * ((a + H') / q ^ k) + (a + H') % q ^ k := by rw [hqk_fac]
            _ = q ^ i * (((a + H') / q ^ k) * q ^ (k - i)) + (a + H') % q ^ k := by ring
        have hdiv_eq : (a + H') / q ^ i = ((a + H') / q ^ k) * q ^ (k - i) + ((a + H') % q ^ k) / q ^ i := by
          conv_lhs => rw [h1]
          exact Nat.mul_add_div hqi_pos _ _
        rw [hdiv_eq]
        obtain ⟨c, hc⟩ := hq_dvd_qki
        rw [hc]; simp [Nat.cast_add, Nat.cast_mul]
      rw [hmod_z]
  rw [hbij]
  let emb : ℕ × ℕ → ℕ := fun p => (p.1 * q) * q ^ i + p.2
  let dom : Finset (ℕ × ℕ) := Finset.range (q ^ (k - i - 1)) ×ˢ Finset.range (q ^ i)
  have hinj : Set.InjOn emb (dom : Set (ℕ × ℕ)) := by
    intro p₁ hp₁ p₂ hp₂ hEq
    simp only [dom, Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_range] at hp₁ hp₂
    have hmod := congrArg (· % q ^ i) hEq
    dsimp [emb] at hmod
    rw [Nat.mul_add_mod_self_right, Nat.mul_add_mod_self_right,
      Nat.mod_eq_of_lt hp₁.2, Nat.mod_eq_of_lt hp₂.2] at hmod
    have h1 : p₁.1 * q * q ^ i = p₂.1 * q * q ^ i := by dsimp [emb] at hEq; omega
    have h2 : p₁.1 = p₂.1 := Nat.eq_of_mul_eq_mul_right hqpos
      (Nat.eq_of_mul_eq_mul_right hqi_pos h1)
    exact Prod.ext h2 hmod
  have himg : dom.image emb ⊆ Finset.range (q ^ k) := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    simp only [dom, Finset.mem_product, Finset.mem_range] at hp
    rw [Finset.mem_range]
    have hpow_eq : q ^ (k - i - 1) * q * q ^ i = q ^ k := by
      have : k - i - 1 + 1 + i = k := by omega
      calc q ^ (k - i - 1) * q * q ^ i = q ^ (k - i - 1 + 1) * q ^ i := by rw [pow_succ]
        _ = q ^ (k - i - 1 + 1 + i) := (pow_add q _ _).symm
        _ = q ^ k := by rw [this]
    have h1 : (p.1 * q + 1) * q ^ i ≤ q ^ (k - i - 1) * q * q ^ i := by
      have : p.1 * q + 1 ≤ (p.1 + 1) * q := by nlinarith
      have : (p.1 + 1) * q ≤ q ^ (k - i - 1) * q := Nat.mul_le_mul_right q hp.1
      exact Nat.mul_le_mul_right (q ^ i) (by omega)
    dsimp [emb]
    have hlt_step : p.1 * q * q ^ i + p.2 < (p.1 * q + 1) * q ^ i := by
      rw [add_mul, one_mul]; exact Nat.add_lt_add_left hp.2 _
    exact lt_of_lt_of_le hlt_step (h1.trans_eq hpow_eq)
  have hcard_dom : dom.card = q ^ (k - 1) := by
    dsimp [dom]
    rw [Finset.card_product, Finset.card_range, Finset.card_range, ← pow_add]
    congr 1; omega
  let fU : ℕ → ℝ := fun u => ‖χ (((u / q ^ i + 1 : ℕ) : ZMod q))‖ ^ 2
  calc ((q ^ (k - 1) : ℕ) : ℝ)
      = ∑ _p ∈ dom, (1 : ℝ) := by simp [hcard_dom]
    _ = ∑ p ∈ dom, fU (emb p) := by
        refine Finset.sum_congr rfl fun p hp => ?_
        simp only [dom, Finset.mem_product, Finset.mem_range] at hp
        have hdiv : emb p / q ^ i = p.1 * q := by
          dsimp [emb]
          rw [mul_comm (p.1 * q) (q ^ i), Nat.mul_add_div hqi_pos, Nat.div_eq_of_lt hp.2, add_zero]
        dsimp [fU]; rw [hdiv]; simp [Nat.cast_add, Nat.cast_mul]
    _ = ∑ u ∈ dom.image emb, fU u := (Finset.sum_image (f := fU) hinj).symm
    _ ≤ ∑ u ∈ Finset.range (q ^ k), fU u :=
        Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => sq_nonneg _



private lemma step10_diag_contradiction {C₀ Q : ℝ} {I Qnat Hhalf H k q : ℕ}
    (hQ1 : 1 ≤ Q) (hQnat_ge1 : 1 ≤ Qnat)
    (hI_gt : 8 * Q * (C₀ + 1) < (I : ℝ))
    (hHhalf_pos : 1 ≤ Hhalf) (hHhalf_ge : Qnat ^ I ≤ Hhalf) (hH_eq : H = 2 * Hhalf)
    (hk_ge : I + 1 ≤ k) (hq2 : 2 ≤ q) (hqQ : (q : ℝ) ≤ Q) (hq_le_Qnat : q ≤ Qnat)
    (χ : DirichletCharacter ℂ q)
    (hpythag_bd : ∑ d ∈ (q ^ (k - 1)).divisors, (1 / (H : ℝ)) *
      ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ Finset.Icc 1 (q ^ k),
        ‖∑ m ∈ (Finset.Icc 1 H').filter (fun m => d ∣ a + m),
          χ (((a + m) / d : ℕ) : ZMod q)‖ ^ 2 ≤ (C₀ + 1) * ((q ^ k : ℕ) : ℝ)) : False := by
  have hH_pos : 1 ≤ H := by omega
  have hH_real_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH_pos
  have hk_ge1 : 1 ≤ k := by omega
  have hqpos : 0 < q := by omega
  have hqk_pos : 0 < q ^ k := pow_pos hqpos k
  let Bsum : ℕ → ℕ → ℕ → ℂ := fun d a H' =>
    ∑ m ∈ (Finset.Icc 1 H').filter (fun m => d ∣ a + m), χ (((a + m) / d : ℕ) : ZMod q)
  -- Step 10d: Restrict to `d = q^i` for `i < I` and derive the lower bound `I ≤ 8 * Q * (C₀ + 1)`
  have hdiag_bound : ∑ i ∈ Finset.range I, (1 / (H : ℝ)) *
      ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H'‖ ^ 2 ≤
      (C₀ + 1) * ((q ^ k : ℕ) : ℝ) := by
    have hinj : Set.InjOn (fun i : ℕ => q ^ i) (Finset.range I : Set ℕ) :=
      fun i₁ _ i₂ _ h => Nat.pow_right_injective hq2 h
    have hsub : (Finset.range I).image (fun i => q ^ i) ⊆ (q ^ (k - 1)).divisors := by
      intro d hd
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
      have hi_le : i ≤ k - 1 := by have := Finset.mem_range.mp hi; omega
      exact Nat.mem_divisors.mpr ⟨Nat.pow_dvd_pow q hi_le, (pow_pos hqpos _).ne'⟩
    let termD : ℕ → ℝ := fun d => (1 / (H : ℝ)) *
      ∑ H' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum d a H'‖ ^ 2
    calc ∑ i ∈ Finset.range I, termD (q ^ i)
        = ∑ d ∈ (Finset.range I).image (fun i => q ^ i), termD d :=
          (Finset.sum_image (f := termD) hinj).symm
      _ ≤ ∑ d ∈ (q ^ (k - 1)).divisors, termD d :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
            mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _)
      _ ≤ (C₀ + 1) * ((q ^ k : ℕ) : ℝ) := hpythag_bd
  -- Lower bound each `i ∈ range I`: `(H / 2) * (q^k / Q) ≤ 4 * ∑_{H'=H+1}^{2H} ∑_a ‖Bsum (q^i) a H'‖^2`
  have hdiag_lb : ∀ i ∈ Finset.range I,
      ((q ^ k : ℕ) : ℝ) / (2 * Q) ≤
      4 * ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
        ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H'‖ ^ 2) := by
    intro i hi
    have hi_lt : i < I := Finset.mem_range.mp hi
    have hqi_pos : 0 < q ^ i := pow_pos hqpos i
    have hqi_le_Hhalf : q ^ i ≤ Hhalf := by
      calc q ^ i ≤ Qnat ^ i := Nat.pow_le_pow_left hq_le_Qnat i
        _ ≤ Qnat ^ I := Nat.pow_le_pow_right hQnat_ge1 hi_lt.le
        _ ≤ Hhalf := hHhalf_ge
    -- For each `H' ∈ Icc (H + 1) (H + Hhalf)` and `a ∈ Icc 1 (q^k)`:
    -- `Bsum (q^i) a (H' + q^i) - Bsum (q^i) a H' = χ ((a + H') / q^i + 1)`
    have hdiff_eq : ∀ H' : ℕ, ∀ a : ℕ,
        Bsum (q ^ i) a (H' + q ^ i) - Bsum (q ^ i) a H' =
        χ ((((a + H') / q ^ i + 1 : ℕ) : ZMod q)) := by
      intro H' a
      dsimp [Bsum]
      have hsplit : Finset.Icc 1 (H' + q ^ i) =
          Finset.Icc 1 H' ∪ Finset.Icc (H' + 1) (H' + q ^ i) := by
        ext m; simp only [Finset.mem_Icc, Finset.mem_union]; omega
      have hdisj : Disjoint (Finset.Icc 1 H') (Finset.Icc (H' + 1) (H' + q ^ i)) := by
        rw [Finset.disjoint_left]; intro m h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
      rw [hsplit, Finset.filter_union,
        Finset.sum_union (Disjoint.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _) hdisj),
        add_sub_cancel_left]
      let m₀ : ℕ := H' + (q ^ i - (a + H') % q ^ i)
      have hrem_lt : (a + H') % q ^ i < q ^ i := Nat.mod_lt _ hqi_pos
      have hm₀_mem : m₀ ∈ (Finset.Icc (H' + 1) (H' + q ^ i)).filter (fun m => q ^ i ∣ a + m) := by
        rw [Finset.mem_filter, Finset.mem_Icc]
        have hsub_pos : 0 < q ^ i - (a + H') % q ^ i := Nat.sub_pos_of_lt hrem_lt
        have hsub_le : q ^ i - (a + H') % q ^ i ≤ q ^ i := Nat.sub_le _ _
        refine ⟨⟨by dsimp [m₀]; omega, by dsimp [m₀]; omega⟩, ?_⟩
        have hsum_eq : a + m₀ = ((a + H') / q ^ i + 1) * q ^ i := by
          have hdm := Nat.div_add_mod (a + H') (q ^ i)
          dsimp [m₀]; zify [hrem_lt.le]; linarith
        rw [hsum_eq]; exact dvd_mul_left _ _
      have hquot : (a + m₀) / q ^ i = (a + H') / q ^ i + 1 := by
        have hsum_eq : a + m₀ = ((a + H') / q ^ i + 1) * q ^ i := by
          have hdm := Nat.div_add_mod (a + H') (q ^ i)
          dsimp [m₀]; zify [hrem_lt.le]; linarith
        rw [hsum_eq, Nat.mul_div_cancel _ hqi_pos]
      rw [Finset.sum_eq_single m₀]
      · rw [hquot]
      · intro m hm hne
        exfalso; apply hne
        have hm' := Finset.mem_filter.mp hm
        have hmI := Finset.mem_Icc.mp hm'.1
        obtain ⟨c, hc⟩ := hm'.2
        have hdm := Nat.div_add_mod (a + H') (q ^ i)
        have hc_eq : c = (a + H') / q ^ i + 1 := by
          have hle_dm : q ^ i * ((a + H') / q ^ i) ≤ a + H' := Nat.mul_div_le (a + H') (q ^ i)
          have hlo : q ^ i * ((a + H') / q ^ i) < q ^ i * c := by omega
          have hhi : q ^ i * c < q ^ i * ((a + H') / q ^ i + 2) := by
            have hmul2 : q ^ i * ((a + H') / q ^ i + 2) = q ^ i * ((a + H') / q ^ i) + q ^ i + q ^ i := by ring
            omega
          have hlo' : (a + H') / q ^ i < c := (Nat.mul_lt_mul_left hqi_pos).mp hlo
          have hhi' : c < (a + H') / q ^ i + 2 := (Nat.mul_lt_mul_left hqi_pos).mp hhi
          omega
        dsimp [m₀]; zify [hrem_lt.le] at hc hc_eq hdm ⊢; nlinarith
      · intro habs; exact absurd hm₀_mem habs
    have hsum_a_lb : ∀ H' : ℕ, ((q ^ (k - 1) : ℕ) : ℝ) ≤
        ∑ a ∈ Finset.Icc 1 (q ^ k), ‖χ ((((a + H') / q ^ i + 1 : ℕ) : ZMod q))‖ ^ 2 :=
      step10_sum_a_lb hq2 (by omega) χ
    -- Combine `hdiff_eq` and `hsum_a_lb` over `H' ∈ Icc (H + 1) (H + Hhalf)`
    have hH'_step : ∀ H' ∈ Finset.Icc (H + 1) (H + Hhalf),
        ((q ^ (k - 1) : ℕ) : ℝ) ≤
        2 * (∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a (H' + q ^ i)‖ ^ 2) +
        2 * (∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H'‖ ^ 2) := by
      intro H' _
      refine (hsum_a_lb H').trans ?_
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun a _ => ?_
      rw [← hdiff_eq H' a]
      have htri := norm_sub_le (Bsum (q ^ i) a (H' + q ^ i)) (Bsum (q ^ i) a H')
      have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
      nlinarith [sq_nonneg (‖Bsum (q ^ i) a (H' + q ^ i)‖ - ‖Bsum (q ^ i) a H'‖)]
    have hsum_H'_shift :
        ∑ H' ∈ Finset.Icc (H + 1) (H + Hhalf), ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a (H' + q ^ i)‖ ^ 2 ≤
        ∑ H'' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H''‖ ^ 2 := by
      have hinj : Set.InjOn (fun H' => H' + q ^ i) (Finset.Icc (H + 1) (H + Hhalf) : Set ℕ) :=
        fun _ _ _ _ h => Nat.add_right_cancel h
      have hsub : (Finset.Icc (H + 1) (H + Hhalf)).image (fun H' => H' + q ^ i) ⊆
          Finset.Icc (H + 1) (2 * H) := by
        intro H'' hH''
        obtain ⟨H', hH', rfl⟩ := Finset.mem_image.mp hH''
        rw [Finset.mem_Icc] at hH' ⊢; omega
      let fH : ℕ → ℝ := fun H'' => ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H''‖ ^ 2
      change ∑ H' ∈ Finset.Icc (H + 1) (H + Hhalf), fH (H' + q ^ i) ≤
        ∑ H'' ∈ Finset.Icc (H + 1) (2 * H), fH H''
      rw [← Finset.sum_image (f := fH) hinj]
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ =>
        Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hsum_H'_id :
        ∑ H' ∈ Finset.Icc (H + 1) (H + Hhalf), ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H'‖ ^ 2 ≤
        ∑ H'' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H''‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc_right (by omega))
        fun _ _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
    have hcard_half : (Finset.Icc (H + 1) (H + Hhalf)).card = Hhalf := by simp [Nat.card_Icc]
    have hsum_H' : (Hhalf : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ) ≤
        4 * ∑ H'' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H''‖ ^ 2 := by
      calc (Hhalf : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ)
          = ∑ _H' ∈ Finset.Icc (H + 1) (H + Hhalf), ((q ^ (k - 1) : ℕ) : ℝ) := by
            rw [Finset.sum_const, hcard_half, nsmul_eq_mul]
        _ ≤ ∑ H' ∈ Finset.Icc (H + 1) (H + Hhalf),
              (2 * (∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a (H' + q ^ i)‖ ^ 2) +
               2 * (∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H'‖ ^ 2)) :=
            Finset.sum_le_sum hH'_step
        _ = 2 * (∑ H' ∈ Finset.Icc (H + 1) (H + Hhalf), ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a (H' + q ^ i)‖ ^ 2) +
            2 * (∑ H' ∈ Finset.Icc (H + 1) (H + Hhalf), ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H'‖ ^ 2) := by
            rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        _ ≤ 4 * ∑ H'' ∈ Finset.Icc (H + 1) (2 * H), ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H''‖ ^ 2 := by
            linarith [hsum_H'_shift, hsum_H'_id]
    have hqk_rel : ((q ^ k : ℕ) : ℝ) = ((q ^ (k - 1) : ℕ) : ℝ) * (q : ℝ) := by
      have : q ^ k = q ^ (k - 1) * q := by conv_lhs => rw [← Nat.sub_add_cancel hk_ge1, pow_succ]
      exact_mod_cast this
    have hH_rel : (H : ℝ) = 2 * (Hhalf : ℝ) := by exact_mod_cast hH_eq
    have hqk_div_Q : ((q ^ k : ℕ) : ℝ) / (2 * Q) ≤ (Hhalf : ℝ) / (H : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ) := by
      rw [hH_rel, hqk_rel]
      have hHhalf_r : (0 : ℝ) < (Hhalf : ℝ) := by exact_mod_cast hHhalf_pos
      have hq_r : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hqpos
      have hQ_pos : (0 : ℝ) < Q := by linarith
      have h1 : (Hhalf : ℝ) / (2 * (Hhalf : ℝ)) = 1 / 2 := by field_simp [hHhalf_r.ne']
      rw [h1]
      rw [div_le_iff₀ (by positivity)]
      nlinarith [hqQ, Nat.cast_nonneg (α := ℝ) (q ^ (k - 1))]
    calc ((q ^ k : ℕ) : ℝ) / (2 * Q)
        ≤ (Hhalf : ℝ) / (H : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ) := hqk_div_Q
      _ = (1 / (H : ℝ)) * ((Hhalf : ℝ) * ((q ^ (k - 1) : ℕ) : ℝ)) := by ring
      _ ≤ (1 / (H : ℝ)) * (4 * ∑ H'' ∈ Finset.Icc (H + 1) (2 * H),
            ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H''‖ ^ 2) := by gcongr
      _ = 4 * ((1 / (H : ℝ)) * ∑ H'' ∈ Finset.Icc (H + 1) (2 * H),
            ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H''‖ ^ 2) := by ring
  -- Summing `hdiag_lb` over `i ∈ range I` contradicts `I = ⌈8 * Q * (C₀ + 1)⌉ + 1`
  have hfinal : (I : ℝ) * (((q ^ k : ℕ) : ℝ) / (2 * Q)) ≤ 4 * (C₀ + 1) * ((q ^ k : ℕ) : ℝ) := by
    calc (I : ℝ) * (((q ^ k : ℕ) : ℝ) / (2 * Q))
        = ∑ _i ∈ Finset.range I, (((q ^ k : ℕ) : ℝ) / (2 * Q)) := by simp
      _ ≤ ∑ i ∈ Finset.range I, 4 * ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
            ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H'‖ ^ 2) := Finset.sum_le_sum hdiag_lb
      _ = 4 * ∑ i ∈ Finset.range I, (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
            ∑ a ∈ Finset.Icc 1 (q ^ k), ‖Bsum (q ^ i) a H'‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ ≤ 4 * ((C₀ + 1) * ((q ^ k : ℕ) : ℝ)) := by gcongr
      _ = 4 * (C₀ + 1) * ((q ^ k : ℕ) : ℝ) := by ring
  have hI_le : (I : ℝ) ≤ 8 * Q * (C₀ + 1) := by
    have hqk_r : (0 : ℝ) < ((q ^ k : ℕ) : ℝ) := by exact_mod_cast hqk_pos
    have hQ_pos : (0 : ℝ) < Q := by linarith
    have h1 : (I : ℝ) / (2 * Q) * ((q ^ k : ℕ) : ℝ) ≤ (4 * (C₀ + 1)) * ((q ^ k : ℕ) : ℝ) := by
      linarith [show (I : ℝ) * (((q ^ k : ℕ) : ℝ) / (2 * Q)) =
        (I : ℝ) / (2 * Q) * ((q ^ k : ℕ) : ℝ) by ring]
    have h2 : (I : ℝ) / (2 * Q) ≤ 4 * (C₀ + 1) := le_of_mul_le_mul_right h1 hqk_r
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Q)).mp h2
    linarith
  linarith [hI_le, hI_gt]


/- ### Helper 11: Factorization `g = χ̃ · n^{it} · h` and `q = 1` contradiction -/

private lemma step6_factorize (z₀ : ℕ → Metric.sphere (0 : ℂ) 1) {q X : ℕ} {t Q : ℝ}
    (hq1 : 1 ≤ q) (χ : DirichletCharacter ℂ q)
    (hD_prim : ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
      (1 - ((if p = 0 then (0 : ℂ) else p.factorization.prod fun q e => (z₀ q).1 ^ e) *
        star (χ (p : ZMod q)) * Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ 2 * Q) :
    ∃ χt h : ℕ → ℂ,
      h 0 = 0 ∧
      (∀ a b, χt (a * b) = χt a * χt b) ∧
      (∀ a b, h (a * b) = h a * h b) ∧
      (∀ n, 1 ≤ n → ‖χt n‖ = 1) ∧
      (∀ n, 1 ≤ n → ‖h n‖ = 1) ∧
      (∀ n, 1 ≤ n → Nat.Coprime n q → χt n = χ (n : ZMod q)) ∧
      (∀ n, 1 ≤ n → (if n = 0 then (0 : ℂ) else n.factorization.prod fun p e => (z₀ p).1 ^ e) =
        χt n * Complex.exp (Complex.I * t * Real.log (n : ℝ)) * h n) ∧
      (∀ p, p.Prime → p ∣ q → h p = 1) ∧
      (∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, (1 - (h p).re) / (p : ℝ) ≤ 2 * Q) := by
  let g : ℕ → ℂ := fun n => if n = 0 then 0 else n.factorization.prod fun p e => (z₀ p).1 ^ e
  let χt_p : ℕ → ℂ := fun p =>
    if p ∣ q then g p * Complex.exp (-Complex.I * t * Real.log (p : ℝ)) else χ (p : ZMod q)
  let h_p : ℕ → ℂ := fun p =>
    if p ∣ q then 1 else g p * star (χ (p : ZMod q)) * Complex.exp (-Complex.I * t * Real.log (p : ℝ))
  let χt : ℕ → ℂ := fun n => if n = 0 then 0 else n.factorization.prod fun p e => χt_p p ^ e
  let h : ℕ → ℂ := fun n => if n = 0 then 0 else n.factorization.prod fun p e => h_p p ^ e
  have hχt_p_norm : ∀ p, p.Prime → ‖χt_p p‖ = 1 := by
    intro p hp
    have he : ‖Complex.exp (-Complex.I * t * Real.log (p : ℝ))‖ = 1 := by
      have : (-Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ)) =
          -Complex.I * ((t * Real.log (p : ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [this]; exact norm_exp_neg_I_mul_real _
    by_cases hd : p ∣ q
    · dsimp only [χt_p, g]
      rw [if_pos hd, norm_mul, mulEval_norm z₀ hp.one_lt.le, he, mul_one]
    · simp only [χt_p, hd, ↓reduceIte]
      exact dirichlet_norm_eq_one_of_coprime χ (hp.coprime_iff_not_dvd.mpr hd)
  have hh_p_norm : ∀ p, p.Prime → ‖h_p p‖ = 1 := by
    intro p hp
    have he : ‖Complex.exp (-Complex.I * t * Real.log (p : ℝ))‖ = 1 := by
      have : (-Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ)) =
          -Complex.I * ((t * Real.log (p : ℝ) : ℝ) : ℂ) := by push_cast; ring
      rw [this]; exact norm_exp_neg_I_mul_real _
    by_cases hd : p ∣ q
    · simp [h_p, hd]
    · dsimp only [h_p, g]
      rw [if_neg hd, norm_mul, norm_mul, mulEval_norm z₀ hp.one_lt.le, one_mul, norm_star,
        dirichlet_norm_eq_one_of_coprime χ (hp.coprime_iff_not_dvd.mpr hd), one_mul, he]
  refine ⟨χt, h, by simp [h], cMul_of_prime_mul χt_p, cMul_of_prime_mul h_p,
    fun n hn => cMul_of_prime_norm χt_p hχt_p_norm hn,
    fun n hn => cMul_of_prime_norm h_p hh_p_norm hn, ?_, ?_, ?_, ?_⟩
  · intro n hn hc
    have hn0 : n ≠ 0 := by omega
    simp only [χt, hn0, ↓reduceIte, Finsupp.prod]
    have hfac_prod : (∏ p ∈ n.factorization.support, χt_p p ^ n.factorization p) =
        ∏ p ∈ n.factorization.support, χ (p : ZMod q) ^ n.factorization p := by
      refine Finset.prod_congr rfl fun p hp => ?_
      rw [Nat.support_factorization] at hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpdvd := Nat.dvd_of_mem_primeFactors hp
      have hnd : ¬ (p ∣ q) := fun h => hpp.not_dvd_one (hc.gcd_eq_one ▸ Nat.dvd_gcd hpdvd h)
      simp [χt_p, hnd]
    rw [hfac_prod]
    have hnat : n = ∏ p ∈ n.factorization.support, p ^ n.factorization p :=
      (Nat.prod_factorization_pow_eq_self hn0).symm
    conv_rhs => rw [hnat, Nat.cast_prod, map_prod]
    refine Finset.prod_congr rfl fun p _ => by rw [Nat.cast_pow, map_pow]
  · intro n hn
    have hn0 : n ≠ 0 := by omega
    have hprod_n : n = ∏ p ∈ n.factorization.support, p ^ n.factorization p :=
      (Nat.prod_factorization_pow_eq_self hn0).symm
    have hlog_n : Real.log (n : ℝ) =
        ∑ p ∈ n.factorization.support, (n.factorization p : ℝ) * Real.log (p : ℝ) := by
      conv_lhs => rw [hprod_n, Nat.cast_prod]
      rw [Real.log_prod fun p hp => by
        rw [Nat.support_factorization] at hp
        rw [Nat.cast_pow]
        exact pow_ne_zero _ (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
      exact Finset.sum_congr rfl fun p _ => by rw [Nat.cast_pow, Real.log_pow]
    have hexp_prod : Complex.exp (Complex.I * t * Real.log (n : ℝ)) =
        ∏ p ∈ n.factorization.support,
          (Complex.exp (Complex.I * t * Real.log (p : ℝ))) ^ n.factorization p := by
      rw [hlog_n, Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← Complex.exp_nat_mul]; congr 1; push_cast; ring
    simp only [χt, h, hn0, ↓reduceIte, Finsupp.prod]
    rw [hexp_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [Nat.support_factorization] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    rw [← mul_pow, ← mul_pow]
    congr 1
    have hgp : g p = (z₀ p).1 := mulEval_prime z₀ hpp
    by_cases hd : p ∣ q
    · dsimp only [χt_p, h_p]
      rw [if_pos hd, if_pos hd, hgp, mul_one, mul_assoc, ← Complex.exp_add]
      have h0 : -Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ) +
          Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ) = 0 := by ring
      rw [h0, Complex.exp_zero, mul_one]
    · simp only [χt_p, h_p, hd, ↓reduceIte, hgp]
      have hχ1 : χ (p : ZMod q) * star (χ (p : ZMod q)) = 1 := by
        rw [Complex.star_def, Complex.mul_conj',
          dirichlet_norm_eq_one_of_coprime χ (hpp.coprime_iff_not_dvd.mpr hd)]
        norm_num
      have hexp1 : Complex.exp (Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ)) *
          Complex.exp (-Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ)) = 1 := by
        rw [← Complex.exp_add]
        have : Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ) +
            -Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ) = 0 := by ring
        rw [this, Complex.exp_zero]
      calc (z₀ p).1 = (z₀ p).1 * 1 * 1 := by ring
        _ = (z₀ p).1 * (χ (p : ZMod q) * star (χ (p : ZMod q))) *
            (Complex.exp (Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ)) *
              Complex.exp (-Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ))) := by
            rw [hχ1, hexp1]
        _ = _ := by ring
  · intro p hp hd
    dsimp only [h]; rw [cMul_of_prime_apply_prime h_p hp]; simp [h_p, hd]
  · refine le_trans (Finset.sum_le_sum fun p hp => ?_) hD_prim
    have hpp := (Finset.mem_filter.mp hp).2
    dsimp only [h]; rw [cMul_of_prime_apply_prime h_p hpp]
    by_cases hd : p ∣ q
    · simp only [h_p, hd, ↓reduceIte, Complex.one_re, sub_self, zero_div]
      apply div_nonneg _ (Nat.cast_nonneg _)
      rw [dirichlet_apply_eq_zero_of_dvd hq1 χ hpp hd]; simp
    · simp only [h_p, hd, ↓reduceIte, g]; exact le_rfl

private lemma step9_q_eq_one {C₀ : ℝ} {H k q : ℕ} (hq_eq1 : q = 1) (hH_pos : 1 ≤ H)
    (hH_sq_gt : C₀ < (H : ℝ) ^ 2)
    (χ : DirichletCharacter ℂ q) (χt : ℕ → ℂ)
    (hχt_coprime : ∀ n, 1 ≤ n → Nat.Coprime n q → χt n = χ (n : ZMod q))
    (hcontra410 : (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
      ∑ a ∈ (Finset.Icc 1 (q ^ k)).filter (fun a =>
          ∀ p : ℕ, p.Prime → p ∣ q → ∀ m ∈ Finset.Icc 1 (2 * H), ¬ (p ^ k ∣ a + m)),
        ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2 ≤ C₀ * ((q ^ k : ℕ) : ℝ)) : False := by
  subst hq_eq1
  have hH_real_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH_pos
  let good1 : Finset ℕ := (Finset.Icc 1 (1 ^ k)).filter fun a =>
    ∀ p : ℕ, p.Prime → p ∣ 1 → ∀ m ∈ Finset.Icc 1 (2 * H), ¬ (p ^ k ∣ a + m)
  have hgood1 : 1 ∈ good1 := by
    simp only [good1, Finset.mem_filter, Finset.mem_Icc, one_pow, le_refl, and_self, true_and]
    intro p hp hdvd
    exact absurd (Nat.dvd_one.mp hdvd) hp.ne_one
  have hχt1 : ∀ n, 1 ≤ n → χt n = 1 := fun n hn => by
    rw [hχt_coprime n hn (Nat.coprime_one_right n)]
    have h1 : (n : ZMod 1) = 1 := Subsingleton.elim _ _
    rw [h1, map_one]
  have hcard_H' : (Finset.Icc (H + 1) (2 * H)).card = H := by simp [Nat.card_Icc]; omega
  have hlb : (H : ℝ) ^ 2 ≤ (1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
      ∑ a ∈ good1, ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2 := by
    have hterm : ∀ H' ∈ Finset.Icc (H + 1) (2 * H),
        (H : ℝ) ^ 2 ≤ ∑ a ∈ good1, ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2 := by
      intro H' hH'
      have hH'_ge : H ≤ H' := by have := (Finset.mem_Icc.mp hH').1; omega
      calc (H : ℝ) ^ 2 ≤ (H' : ℝ) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hH'_ge) 2
        _ = ‖∑ m ∈ Finset.Icc 1 H', χt (1 + m)‖ ^ 2 := by
            have : ∑ m ∈ Finset.Icc 1 H', χt (1 + m) = (H' : ℂ) := by
              trans ∑ _m ∈ Finset.Icc 1 H', (1 : ℂ)
              · exact Finset.sum_congr rfl fun m _ => hχt1 _ (by omega)
              · simp [Nat.card_Icc]
            rw [this, Complex.norm_natCast]
        _ ≤ ∑ a ∈ good1, ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2 :=
            Finset.single_le_sum (f := fun a => ‖∑ m ∈ Finset.Icc 1 H', χt (a + m)‖ ^ 2)
              (fun _ _ => sq_nonneg _) hgood1
    calc (H : ℝ) ^ 2 = (1 / (H : ℝ)) * ∑ _H' ∈ Finset.Icc (H + 1) (2 * H), (H : ℝ) ^ 2 := by
          rw [Finset.sum_const, hcard_H', nsmul_eq_mul]; field_simp [hH_real_pos.ne']
      _ ≤ _ := by gcongr; exact hterm _ ‹_›
  have hgood1_eq : good1 = (Finset.Icc 1 1).filter (fun a =>
      ∀ p : ℕ, p.Prime → p ∣ 1 → ∀ m ∈ Finset.Icc 1 (2 * H), ¬ (p ^ k ∣ a + m)) := by
    simp [good1]
  rw [hgood1_eq] at hlb
  rw [one_pow, Nat.cast_one, mul_one] at hcontra410
  linarith [hH_sq_gt, hlb, hcontra410]

/- ### Helper 12: `lintegral_tsum` and Markov elimination of the probability measure `μ` -/

private lemma step3_markov_badE (μ : ProbabilityMeasure (ℕ → Metric.sphere (0 : ℂ) 1))
    {B : ℝ} {H X : ℕ} (hB : 0 ≤ B) (hH_pos : 1 ≤ H) (hlogX_ge1 : 1 ≤ Real.log (X : ℝ))
    (hEnergy : ∀ n : ℕ, ∫ z : ℕ → Metric.sphere (0 : ℂ) 1,
      ‖∑ k ∈ Finset.Icc 1 n, (if k = 0 then (0 : ℂ) else k.factorization.prod fun p e => (z p).1 ^ e)‖ ^ 2
        ∂(μ : Measure _) ≤ B) :
    (μ : Measure _) {z : ℕ → Metric.sphere (0 : ℂ) 1 |
      ENNReal.ofReal (192 * B * Real.log (X : ℝ) + 1) ≤
        ∑' n : ℕ, ENNReal.ofReal ((1 / ((n + 1 : ℕ) : ℝ) ^ (1 + 1 / Real.log (X : ℝ))) *
          ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
            ‖∑ m ∈ Finset.Icc 1 H',
              (if n + 1 + m = 0 then (0 : ℂ) else (n + 1 + m).factorization.prod fun p e => (z p).1 ^ e)‖ ^ 2))} ≤
      ENNReal.ofReal (1 / 8) := by
  let mulEval : (ℕ → Metric.sphere (0 : ℂ) 1) → ℕ → ℂ := fun z n =>
    if n = 0 then 0 else n.factorization.prod fun p e => (z p).1 ^ e
  have hH_real_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH_pos
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  set s : ℝ := 1 / Real.log (X : ℝ)
  have hs_pos : 0 < s := by positivity
  let w : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + s)
  have hw_pos : ∀ n, 0 < w n := fun n => by dsimp [w]; positivity
  have hw_tsum_le : (∑' n : ℕ, w n) ≤ 3 * Real.log (X : ℝ) := by
    calc (∑' n : ℕ, w n) ≤ 1 + 2 / s := tsum_inv_rpow_le hs_pos
      _ = 1 + 2 * Real.log (X : ℝ) := by dsimp [s]; field_simp [hlogX_pos.ne']
      _ ≤ 3 * Real.log (X : ℝ) := by linarith
  let term : ℕ → (ℕ → Metric.sphere (0 : ℂ) 1) → ℝ := fun n z =>
    w n * ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
      ‖∑ m ∈ Finset.Icc 1 H', mulEval z (n + 1 + m)‖ ^ 2)
  have hterm_nonneg : ∀ n z, 0 ≤ term n z := fun n z => by
    dsimp [term]
    exact mul_nonneg (hw_pos n).le (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  have hterm_cont : ∀ n, Continuous (term n) := fun n => by
    dsimp [term]
    refine continuous_const.mul (continuous_const.mul (continuous_finsetSum _ fun H' _ => ?_))
    exact ((continuous_finsetSum _ fun m _ => mulEval_continuous (n + 1 + m)).norm).pow 2
  have hterm_int : ∀ n, ∫ z, term n z ∂(μ : Measure _) ≤ w n * (4 * B) := by
    intro n
    have hbd_H' : ∀ H' ∈ Finset.Icc (H + 1) (2 * H),
        ∫ z, ‖∑ m ∈ Finset.Icc 1 H', mulEval z (n + 1 + m)‖ ^ 2 ∂(μ : Measure _) ≤ 4 * B := by
      intro H' _
      have hpt : ∀ z, ‖∑ m ∈ Finset.Icc 1 H', mulEval z (n + 1 + m)‖ ^ 2 ≤
          2 * ‖∑ k ∈ Finset.Icc 1 (n + 1 + H'), mulEval z k‖ ^ 2 +
          2 * ‖∑ k ∈ Finset.Icc 1 (n + 1), mulEval z k‖ ^ 2 := by
        intro z
        have hsum_diff : ∑ m ∈ Finset.Icc 1 H', mulEval z (n + 1 + m) =
            (∑ k ∈ Finset.Icc 1 (n + 1 + H'), mulEval z k) -
            (∑ k ∈ Finset.Icc 1 (n + 1), mulEval z k) := by
          have hdisj : Finset.Icc 1 (n + 1 + H') =
              Finset.Icc 1 (n + 1) ∪ Finset.Icc (n + 2) (n + 1 + H') := by
            ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
          have hd : Disjoint (Finset.Icc 1 (n + 1)) (Finset.Icc (n + 2) (n + 1 + H')) := by
            rw [Finset.disjoint_left]; intro k hk1 hk2
            rw [Finset.mem_Icc] at hk1 hk2; omega
          rw [hdisj, Finset.sum_union hd, add_sub_cancel_left]
          refine Finset.sum_bij (fun m _ => n + 1 + m) ?_ ?_ ?_ ?_
          · intro m hm; rw [Finset.mem_Icc] at hm ⊢; omega
          · intro m₁ _ m₂ _ h; omega
          · intro k hk; rw [Finset.mem_Icc] at hk
            exact ⟨k - (n + 1), Finset.mem_Icc.mpr (by omega), by omega⟩
          · intro _ _; rfl
        rw [hsum_diff]
        have htri := norm_sub_le (∑ k ∈ Finset.Icc 1 (n + 1 + H'), mulEval z k)
          (∑ k ∈ Finset.Icc 1 (n + 1), mulEval z k)
        have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
        nlinarith [sq_nonneg (‖∑ k ∈ Finset.Icc 1 (n + 1 + H'), mulEval z k‖ -
          ‖∑ k ∈ Finset.Icc 1 (n + 1), mulEval z k‖)]
      have hint_e : ∀ N : ℕ, Integrable
          (fun z => ‖∑ k ∈ Finset.Icc 1 N, mulEval z k‖ ^ 2) (μ : Measure _) := fun N => by
        refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
        exact ((continuous_finsetSum _ fun k _ => mulEval_continuous k).norm).pow 2
      have hint_lhs : Integrable
          (fun z => ‖∑ m ∈ Finset.Icc 1 H', mulEval z (n + 1 + m)‖ ^ 2) (μ : Measure _) := by
        refine Continuous.integrable_of_hasCompactSupport ?_ (HasCompactSupport.of_compactSpace _)
        exact ((continuous_finsetSum _ fun m _ => mulEval_continuous (n + 1 + m)).norm).pow 2
      calc ∫ z, ‖∑ m ∈ Finset.Icc 1 H', mulEval z (n + 1 + m)‖ ^ 2 ∂(μ : Measure _)
          ≤ ∫ z, (2 * ‖∑ k ∈ Finset.Icc 1 (n + 1 + H'), mulEval z k‖ ^ 2 +
              2 * ‖∑ k ∈ Finset.Icc 1 (n + 1), mulEval z k‖ ^ 2) ∂(μ : Measure _) :=
            integral_mono hint_lhs (((hint_e _).const_mul 2).add ((hint_e _).const_mul 2)) hpt
        _ = 2 * (∫ z, ‖∑ k ∈ Finset.Icc 1 (n + 1 + H'), mulEval z k‖ ^ 2 ∂(μ : Measure _)) +
            2 * (∫ z, ‖∑ k ∈ Finset.Icc 1 (n + 1), mulEval z k‖ ^ 2 ∂(μ : Measure _)) := by
            rw [integral_add ((hint_e _).const_mul 2) ((hint_e _).const_mul 2),
              integral_const_mul, integral_const_mul]
        _ ≤ 2 * B + 2 * B := add_le_add (mul_le_mul_of_nonneg_left (hEnergy _) (by norm_num))
            (mul_le_mul_of_nonneg_left (hEnergy _) (by norm_num))
        _ = 4 * B := by ring
    dsimp [term]
    have hint_H' : ∀ H' ∈ Finset.Icc (H + 1) (2 * H), Integrable
        (fun z => ‖∑ m ∈ Finset.Icc 1 H', mulEval z (n + 1 + m)‖ ^ 2) (μ : Measure _) := fun H' _ =>
      Continuous.integrable_of_hasCompactSupport
        (((continuous_finsetSum _ fun m _ => mulEval_continuous (n + 1 + m)).norm).pow 2)
        (HasCompactSupport.of_compactSpace _)
    rw [integral_const_mul, integral_const_mul, integral_finsetSum _ hint_H']
    have hcard : (Finset.Icc (H + 1) (2 * H)).card = H := by simp [Nat.card_Icc]; omega
    calc w n * (1 / (H : ℝ) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
          ∫ z, ‖∑ m ∈ Finset.Icc 1 H', mulEval z (n + 1 + m)‖ ^ 2 ∂(μ : Measure _))
        ≤ w n * (1 / (H : ℝ) * ∑ _H' ∈ Finset.Icc (H + 1) (2 * H), (4 * B)) := by
          gcongr; exact hbd_H' _ ‹_›
      _ = w n * (4 * B) := by
          rw [Finset.sum_const, hcard, nsmul_eq_mul]
          field_simp [hH_real_pos.ne']
  let F_en : (ℕ → Metric.sphere (0 : ℂ) 1) → ENNReal := fun z =>
    ∑' n : ℕ, ENNReal.ofReal (term n z)
  have hF_lint : ∫⁻ z, F_en z ∂(μ : Measure _) ≤ ENNReal.ofReal (12 * B * Real.log (X : ℝ)) := by
    have hmeas : ∀ n, AEMeasurable (fun z => ENNReal.ofReal (term n z)) (μ : Measure _) :=
      fun n => (ENNReal.continuous_ofReal.comp (hterm_cont n)).measurable.aemeasurable
    rw [lintegral_tsum hmeas]
    have hterm_lint : ∀ n, ∫⁻ z, ENNReal.ofReal (term n z) ∂(μ : Measure _) ≤
        ENNReal.ofReal (w n * (4 * B)) := fun n => by
      have hint : Integrable (term n) (μ : Measure _) :=
        (hterm_cont n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
      rw [← ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (hterm_nonneg n))]
      exact ENNReal.ofReal_le_ofReal (hterm_int n)
    have hsum_w : Summable (fun n => w n * (4 * B)) :=
      (summable_one_div_succ_rpow hs_pos).mul_right (4 * B)
    calc ∑' n : ℕ, ∫⁻ z, ENNReal.ofReal (term n z) ∂(μ : Measure _)
        ≤ ∑' n : ℕ, ENNReal.ofReal (w n * (4 * B)) := ENNReal.tsum_le_tsum hterm_lint
      _ = ENNReal.ofReal (∑' n : ℕ, w n * (4 * B)) :=
          (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum_w).symm
      _ = ENNReal.ofReal ((∑' n : ℕ, w n) * (4 * B)) := by rw [tsum_mul_right]
      _ ≤ ENNReal.ofReal (12 * B * Real.log (X : ℝ)) := by
          apply ENNReal.ofReal_le_ofReal
          nlinarith [hw_tsum_le]
  have hc_pos' : (0 : ℝ) < 192 * B * Real.log (X : ℝ) + 1 := by positivity
  have hF_meas : Measurable F_en := by
    have hsup : F_en = fun z => ⨆ s : Finset ℕ, ∑ n ∈ s, ENNReal.ofReal (term n z) := by
      ext z; exact ENNReal.tsum_eq_iSup_sum
    rw [hsup]
    exact Measurable.iSup fun s => Finset.measurable_sum s fun n _ =>
      (ENNReal.continuous_ofReal.comp (hterm_cont n)).measurable
  have hmarkov := mul_meas_ge_le_lintegral₀ (μ := (μ : Measure _)) hF_meas.aemeasurable
    (ENNReal.ofReal (192 * B * Real.log (X : ℝ) + 1))
  have h1 : ENNReal.ofReal (192 * B * Real.log (X : ℝ) + 1) *
      (μ : Measure _) {z | ENNReal.ofReal (192 * B * Real.log (X : ℝ) + 1) ≤ F_en z} ≤
      ENNReal.ofReal (12 * B * Real.log (X : ℝ)) := hmarkov.trans hF_lint
  have h2 : ENNReal.ofReal (12 * B * Real.log (X : ℝ)) ≤
      ENNReal.ofReal (192 * B * Real.log (X : ℝ) + 1) * ENNReal.ofReal (1 / 8) := by
    rw [← ENNReal.ofReal_mul hc_pos'.le]
    apply ENNReal.ofReal_le_ofReal
    nlinarith
  have hne0 : ENNReal.ofReal (192 * B * Real.log (X : ℝ) + 1) ≠ 0 :=
    (ENNReal.ofReal_pos.mpr hc_pos').ne'
  have hnetop : ENNReal.ofReal (192 * B * Real.log (X : ℝ) + 1) ≠ ⊤ := ENNReal.ofReal_ne_top
  exact (ENNReal.mul_le_mul_iff_right hne0 hnetop).mp (h1.trans h2)

/- ### Hypotheses -/

/-- **Hypothesis 1 (Vinogradov–Korobov pretentious repulsion for Dirichlet characters)**:
for any `Q ≥ 1`, `δ ∈ (0, 1)`, and `M ≥ 0`, once `X` is sufficiently large, any two Dirichlet
characters `χ (mod q)` and `χ' (mod q')` with `1 ≤ q, q' ≤ Q` and shifts `t, t' : ℝ` satisfying
`X^δ ≤ |t' - t| ≤ 2 Q X` have pretentious distance strictly greater than `M` over primes
`p ≤ ⌊X^δ⌋`. -/
def H1 : Prop :=
  ∀ (Q δ M : ℝ), 1 ≤ Q → 0 < δ → δ < 1 → 0 ≤ M →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ (q q' : ℕ) (χ : DirichletCharacter ℂ q) (χ' : DirichletCharacter ℂ q') (t t' : ℝ),
        1 ≤ q → (q : ℝ) ≤ Q → 1 ≤ q' → (q' : ℝ) ≤ Q →
        (X : ℝ) ^ δ ≤ |t' - t| → |t' - t| ≤ 2 * Q * (X : ℝ) →
        M < ∑ p ∈ (Finset.Icc 1 (Nat.floor ((X : ℝ) ^ δ))).filter Nat.Prime,
          (1 - (χ (p : ZMod q) * star (χ' (p : ZMod q')) *
            Complex.exp (-Complex.I * (t' - t) * Real.log (p : ℝ))).re) / (p : ℝ)

/-- **Hypothesis 2 (Euler-product equidistribution of 1-pretentious multiplicative functions)**:
for any `Q ≥ 1`, there is `c > 0` such that for any `1 ≤ q ≤ Q`, `k ≥ 1`, and `η > 0`, once `X`
is sufficiently large, every `S¹`-valued completely multiplicative function `h` with `h(p) = 1`
for `p ∣ q` and `∑_{p ≤ X} (1 - Re h(p)) / p ≤ Q` is equidistributed in residue classes modulo
`q^k` with weight `n^{-(1 + 1/log X)}`, around `S / q^k` for some `S : ℂ` with `‖S‖ ≥ c log X`. -/
def H2 : Prop :=
  ∀ Q : ℝ, 1 ≤ Q →
    ∃ c : ℝ, 0 < c ∧
      ∀ (q k : ℕ), 1 ≤ q → (q : ℝ) ≤ Q → 1 ≤ k →
        ∀ η : ℝ, 0 < η →
          ∃ X₁ : ℕ, 3 ≤ X₁ ∧ ∀ X : ℕ, X₁ ≤ X →
            ∀ h : ℕ → ℂ, h 0 = 0 → (∀ a b, h (a * b) = h a * h b) →
              (∀ n, 1 ≤ n → ‖h n‖ = 1) → (∀ p, p.Prime → p ∣ q → h p = 1) →
              (∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, (1 - (h p).re) / (p : ℝ) ≤ Q) →
              ∃ S : ℂ, c * Real.log (X : ℝ) ≤ ‖S‖ ∧
                ∀ b : ℕ, ‖(∑' n : ℕ, if (n + 1) % (q ^ k) = b % (q ^ k) then
                    h (n + 1) / Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (1 + 1 / Real.log (X : ℝ))) else 0) -
                    S / ((q ^ k : ℕ) : ℂ)‖ ≤ η * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ)

/- ### Main Reduction Theorem -/


theorem main : H1 → H2 → OMA.R_Erdos67_erdos_67_R1.H2 := by
  intro hVK hEuler
  dsimp only [OMA.R_Erdos67_erdos_67_R1.H2]
  intro μ B hB hEnergy hPret
  let mulEval : (ℕ → Metric.sphere (0 : ℂ) 1) → ℕ → ℂ := fun z n =>
    if n = 0 then 0 else n.factorization.prod fun p e => (z p).1 ^ e
  -- Step 1: Fix `ε = 1/8` and obtain the pretentious parameter `Q ≥ 1`
  obtain ⟨Q, hQ1, hQ⟩ := hPret (1 / 8) (by norm_num)
  -- Obtain the Euler-product lower bound constant `c > 0` for `2 * Q`
  obtain ⟨c, hc_pos, hc_euler⟩ := hEuler (2 * Q) (by linarith)
  -- Define the final energy constant `C₀` (independent of `H, k, q, X`)
  set C₀ : ℝ := (6 * (384 * B + 5) + 1) / c ^ 2
  have hC₀_nonneg : 0 ≤ C₀ := by positivity
  -- Choose `I, H, δ, k` in Tao's hierarchy `B, Q ≪ H ≪ 1/δ, k ≪ X`
  set I : ℕ := Nat.ceil (8 * Q * (C₀ + 1)) + 1
  set Qnat : ℕ := Nat.ceil Q
  have hQ_le_Qnat : Q ≤ (Qnat : ℝ) := Nat.le_ceil Q
  have hQnat_ge1 : 1 ≤ Qnat := by
    have : (1 : ℝ) ≤ (Qnat : ℝ) := hQ1.trans hQ_le_Qnat
    exact_mod_cast this
  set Hhalf : ℕ := max (Nat.ceil (Real.sqrt C₀) + 1) (Qnat ^ I)
  have hHhalf_pos : 1 ≤ Hhalf := le_trans (one_le_pow₀ hQnat_ge1) (le_max_right _ _)
  set H : ℕ := 2 * Hhalf
  have hH_pos : 1 ≤ H := by omega
  have hH_real_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH_pos
  have hH_sq_gt : C₀ < (H : ℝ) ^ 2 := by
    have h1 : Real.sqrt C₀ < (Hhalf : ℝ) := by
      have : Real.sqrt C₀ + 1 ≤ (Hhalf : ℝ) := by
        calc Real.sqrt C₀ + 1 ≤ ((Nat.ceil (Real.sqrt C₀) + 1 : ℕ) : ℝ) := by
              push_cast; linarith [Nat.le_ceil (Real.sqrt C₀)]
          _ ≤ (Hhalf : ℝ) := by exact_mod_cast le_max_left _ _
      linarith
    have h2 : Real.sqrt C₀ < (H : ℝ) := by
      have : (Hhalf : ℝ) ≤ (H : ℝ) := by exact_mod_cast (show Hhalf ≤ H by omega)
      linarith
    calc C₀ = Real.sqrt C₀ ^ 2 := (Real.sq_sqrt hC₀_nonneg).symm
      _ < (H : ℝ) ^ 2 := pow_lt_pow_left₀ h2 (Real.sqrt_nonneg _) two_ne_zero
  -- Choose `δ = 1 / (32 * H^2)` so `4 * H^2 * (4 * δ) ≤ 1/2`
  set δ : ℝ := 1 / (32 * (H : ℝ) ^ 2)
  have hδ_pos : 0 < δ := by positivity
  have hδ_lt : δ < 1 := by
    have hH2 : (1 : ℝ) ≤ (H : ℝ) ^ 2 := by
      have : (1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH_pos
      nlinarith
    dsimp [δ]; rw [div_lt_one (by positivity)]; linarith
  -- Choose `k` large enough that `2^k ≥ 8 * H^3 * Q` and `I + 1 ≤ k`
  set k : ℕ := max (I + 1) (Nat.ceil (8 * (H : ℝ) ^ 3 * Q) + 1)
  have hk_ge1 : 1 ≤ k := by omega
  have h2k_large : 8 * (H : ℝ) ^ 3 * Q ≤ (2 : ℝ) ^ k := by
    have hk_ge : 8 * (H : ℝ) ^ 3 * Q ≤ (k : ℝ) := by
      calc 8 * (H : ℝ) ^ 3 * Q ≤ (Nat.ceil (8 * (H : ℝ) ^ 3 * Q) : ℝ) := Nat.le_ceil _
        _ ≤ (k : ℝ) := by exact_mod_cast (show Nat.ceil (8 * (H : ℝ) ^ 3 * Q) ≤ k by omega)
    have hpow : (k : ℝ) ≤ (2 : ℝ) ^ k := by
      exact_mod_cast (Nat.lt_two_pow_self (n := k)).le
    linarith
  -- Step 2: Choose `X` sufficiently large depending on `Q, B, H, δ, k`
  obtain ⟨X_VK, hX_VK⟩ := hVK Q δ (4 * Q) hQ1 hδ_pos hδ_lt (by positivity)
  -- Uniform `X_E` over all `1 ≤ q ≤ Qnat` for `η = 1 / (8 * H)`
  have hEuler_all : ∃ X_E : ℕ, 3 ≤ X_E ∧ ∀ q ∈ Finset.Icc 1 Qnat, (q : ℝ) ≤ 2 * Q →
      ∀ X : ℕ, X_E ≤ X →
        ∀ h : ℕ → ℂ, h 0 = 0 → (∀ a b, h (a * b) = h a * h b) →
          (∀ n, 1 ≤ n → ‖h n‖ = 1) → (∀ p, p.Prime → p ∣ q → h p = 1) →
          (∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, (1 - (h p).re) / (p : ℝ) ≤ 2 * Q) →
          ∃ S : ℂ, c * Real.log (X : ℝ) ≤ ‖S‖ ∧
            ∀ b : ℕ, ‖(∑' n : ℕ, if (n + 1) % (q ^ k) = b % (q ^ k) then
                h (n + 1) / Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (1 + 1 / Real.log (X : ℝ))) else 0) -
                S / ((q ^ k : ℕ) : ℂ)‖ ≤
              (1 / (8 * (H : ℝ))) * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ) := by
    have hchoose : ∀ q ∈ Finset.Icc 1 Qnat, ∃ Xq : ℕ, 3 ≤ Xq ∧
        ((q : ℝ) ≤ 2 * Q → ∀ X : ℕ, Xq ≤ X →
          ∀ h : ℕ → ℂ, h 0 = 0 → (∀ a b, h (a * b) = h a * h b) →
            (∀ n, 1 ≤ n → ‖h n‖ = 1) → (∀ p, p.Prime → p ∣ q → h p = 1) →
            (∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, (1 - (h p).re) / (p : ℝ) ≤ 2 * Q) →
            ∃ S : ℂ, c * Real.log (X : ℝ) ≤ ‖S‖ ∧
              ∀ b : ℕ, ‖(∑' n : ℕ, if (n + 1) % (q ^ k) = b % (q ^ k) then
                  h (n + 1) / Complex.ofReal (((n + 1 : ℕ) : ℝ) ^ (1 + 1 / Real.log (X : ℝ))) else 0) -
                  S / ((q ^ k : ℕ) : ℂ)‖ ≤
                (1 / (8 * (H : ℝ))) * Real.log (X : ℝ) / ((q ^ k : ℕ) : ℝ)) := by
      intro q hq
      by_cases hqQ : (q : ℝ) ≤ 2 * Q
      · obtain ⟨Xq, hXq3, hXq⟩ := hc_euler q k (Finset.mem_Icc.mp hq).1 hqQ hk_ge1
          (1 / (8 * (H : ℝ))) (by positivity)
        exact ⟨Xq, hXq3, fun _ => hXq⟩
      · exact ⟨3, le_rfl, fun h => absurd h hqQ⟩
    choose fX hfX3 hfX using hchoose
    refine ⟨max 3 ((Finset.Icc 1 Qnat).sup fun q => if h : q ∈ Finset.Icc 1 Qnat then fX q h else 3),
      le_max_left _ _, fun q hq hqQ X hX => ?_⟩
    have hfq : fX q hq ≤ X := by
      refine le_trans ?_ (le_trans (le_max_right _ _) hX)
      have := Finset.le_sup (f := fun q => if h : q ∈ Finset.Icc 1 Qnat then fX q h else 3) hq
      simpa [hq] using this
    exact hfX q hq hqQ X hfq
  obtain ⟨X_E, hX_E3, hEuler_unif⟩ := hEuler_all
  -- Pick `X` large enough for all asymptotic inequalities simultaneously
  have hX_exists : ∃ X : ℕ,
      X_VK ≤ X ∧ X_E ≤ X ∧ Q ≤ (X : ℝ) ∧
      Q ≤ (Nat.floor ((X : ℝ) ^ δ) : ℝ) ∧
      1 ≤ Real.log (X : ℝ) ∧
      12 * (H : ℝ) ^ 2 ≤ Real.log (X : ℝ) ∧
      (4 * (H : ℝ) ^ 2 * (Q + 1)) ^ 2 * 6 ≤ ((X : ℝ) ^ δ) ^ 2 ∧
      ((Qnat ^ k : ℕ) : ℝ) * (8 * (H : ℝ)) * (4 * (H : ℝ) + 1) ≤ Real.log (X : ℝ) := by
    have hlog_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have hrpow_top : Tendsto (fun n : ℕ => (n : ℝ) ^ δ) atTop atTop :=
      (tendsto_rpow_atTop hδ_pos).comp tendsto_natCast_atTop_atTop
    have h1 : ∀ᶠ n : ℕ in atTop, Q + 1 ≤ (n : ℝ) ^ δ :=
      hrpow_top.eventually (Filter.eventually_ge_atTop (Q + 1))
    have h2 : ∀ᶠ n : ℕ in atTop,
        max (max 1 (12 * (H : ℝ) ^ 2))
          (((Qnat ^ k : ℕ) : ℝ) * (8 * (H : ℝ)) * (4 * (H : ℝ) + 1)) ≤ Real.log (n : ℝ) :=
      hlog_top.eventually (Filter.eventually_ge_atTop _)
    have h3 : ∀ᶠ n : ℕ in atTop,
        Real.sqrt ((4 * (H : ℝ) ^ 2 * (Q + 1)) ^ 2 * 6) ≤ (n : ℝ) ^ δ :=
      hrpow_top.eventually (Filter.eventually_ge_atTop _)
    have h4 : ∀ᶠ n : ℕ in atTop, max (max X_VK X_E) (Nat.ceil Q) ≤ n :=
      Filter.eventually_ge_atTop _
    obtain ⟨X, hX1, hX2, hX3, hX4⟩ := (h1.and (h2.and (h3.and h4))).exists
    refine ⟨X, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX4
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX4
    · exact le_trans (Nat.le_ceil Q) (by exact_mod_cast le_trans (le_max_right _ _) hX4)
    · have := Nat.lt_floor_add_one ((X : ℝ) ^ δ); linarith
    · exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX2
    · exact le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX2
    · calc (4 * (H : ℝ) ^ 2 * (Q + 1)) ^ 2 * 6
          = Real.sqrt ((4 * (H : ℝ) ^ 2 * (Q + 1)) ^ 2 * 6) ^ 2 :=
            (Real.sq_sqrt (by positivity)).symm
        _ ≤ ((X : ℝ) ^ δ) ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hX3 2
    · exact le_trans (le_max_right _ _) hX2
  obtain ⟨X, hX_ge_VK, hX_ge_E, hX_ge_Q, hXδ_ge_Q, hlogX_ge1, hlogX_ge_H2,
    hXδ_sq, hlogX_shift⟩ := hX_exists
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  set s : ℝ := 1 / Real.log (X : ℝ)
  have hs_pos : 0 < s := by positivity
  have hs_le1 : s ≤ 1 := by dsimp [s]; rw [div_le_one hlogX_pos]; exact hlogX_ge1
  have hX_pos : (0 : ℝ) < (X : ℝ) := by linarith
  -- Step 3: Eliminate the probability measure `μ` via `lintegral_tsum` and Markov
  let w : ℕ → ℝ := fun n => 1 / ((n + 1 : ℕ) : ℝ) ^ (1 + s)
  let term : ℕ → (ℕ → Metric.sphere (0 : ℂ) 1) → ℝ := fun n z =>
    w n * ((1 / (H : ℝ)) * ∑ H' ∈ Finset.Icc (H + 1) (2 * H),
      ‖∑ m ∈ Finset.Icc 1 H', mulEval z (n + 1 + m)‖ ^ 2)
  have hterm_nonneg : ∀ n z, 0 ≤ term n z := fun n z =>
    mul_nonneg (by dsimp [w]; positivity)
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _))
  let F_en : (ℕ → Metric.sphere (0 : ℂ) 1) → ENNReal := fun z =>
    ∑' n : ℕ, ENNReal.ofReal (term n z)
  let bad_E : Set (ℕ → Metric.sphere (0 : ℂ) 1) :=
    {z | ENNReal.ofReal (192 * B * Real.log (X : ℝ) + 1) ≤ F_en z}
  have hbad_E_meas : (μ : Measure _) bad_E ≤ ENNReal.ofReal (1 / 8) :=
    step3_markov_badE μ hB hH_pos hlogX_ge1 hEnergy
  -- Intersect with the pretentious events at `X` and `⌊X^δ⌋`
  let bad_X : Set (ℕ → Metric.sphere (0 : ℂ) 1) := {z |
    ¬ ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
        1 ≤ q ∧ (q : ℝ) ≤ Q ∧ |t| ≤ Q * (X : ℝ) ∧
        ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
          (1 - (mulEval z p * star (χ (p : ZMod q)) *
            Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q}
  let Xδ : ℕ := Nat.floor ((X : ℝ) ^ δ)
  let bad_Xδ : Set (ℕ → Metric.sphere (0 : ℂ) 1) := {z |
    ¬ ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
        1 ≤ q ∧ (q : ℝ) ≤ Q ∧ |t| ≤ Q * (Xδ : ℝ) ∧
        ∑ p ∈ (Finset.Icc 1 Xδ).filter Nat.Prime,
          (1 - (mulEval z p * star (χ (p : ZMod q)) *
            Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q}
  have hbad_union : (μ : Measure _) (bad_E ∪ bad_X ∪ bad_Xδ) < 1 := by
    calc (μ : Measure _) (bad_E ∪ bad_X ∪ bad_Xδ)
        ≤ (μ : Measure _) (bad_E ∪ bad_X) + (μ : Measure _) bad_Xδ := measure_union_le _ _
      _ ≤ (μ : Measure _) bad_E + (μ : Measure _) bad_X + (μ : Measure _) bad_Xδ :=
          add_le_add (measure_union_le _ _) le_rfl
      _ ≤ ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) + ENNReal.ofReal (1 / 8) :=
          add_le_add (add_le_add hbad_E_meas (hQ X hX_ge_Q)) (hQ Xδ hXδ_ge_Q)
      _ = ENNReal.ofReal (3 / 8) := by
          rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
            ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
          congr 1; norm_num
      _ < ENNReal.ofReal 1 := ENNReal.ofReal_lt_ofReal_iff zero_lt_one |>.mpr (by norm_num)
      _ = 1 := ENNReal.ofReal_one
  have hexists_z : ∃ z₀ : ℕ → Metric.sphere (0 : ℂ) 1, z₀ ∉ bad_E ∪ bad_X ∪ bad_Xδ := by
    by_contra hall; push Not at hall
    have huniv : bad_E ∪ bad_X ∪ bad_Xδ = Set.univ := Set.eq_univ_of_forall hall
    rw [huniv, measure_univ] at hbad_union
    exact lt_irrefl 1 hbad_union
  obtain ⟨z₀, hz₀⟩ := hexists_z
  have hz₀_E : F_en z₀ < ENNReal.ofReal (192 * B * Real.log (X : ℝ) + 1) := by
    have : z₀ ∉ bad_E := fun h => hz₀ (Or.inl (Or.inl h))
    simpa [bad_E] using this
  have hz₀_X : ∃ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
      1 ≤ q ∧ (q : ℝ) ≤ Q ∧ |t| ≤ Q * (X : ℝ) ∧
      ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
        (1 - (mulEval z₀ p * star (χ (p : ZMod q)) *
          Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q := by
    have : z₀ ∉ bad_X := fun h => hz₀ (Or.inl (Or.inr h))
    simpa [bad_X] using this
  have hz₀_Xδ : ∃ (q' : ℕ) (χ' : DirichletCharacter ℂ q') (t' : ℝ),
      1 ≤ q' ∧ (q' : ℝ) ≤ Q ∧ |t'| ≤ Q * (Xδ : ℝ) ∧
      ∑ p ∈ (Finset.Icc 1 Xδ).filter Nat.Prime,
        (1 - (mulEval z₀ p * star (χ' (p : ZMod q')) *
          Complex.exp (-Complex.I * t' * Real.log (p : ℝ))).re) / (p : ℝ) ≤ Q := by
    have : z₀ ∉ bad_Xδ := fun h => hz₀ (Or.inr h)
    simpa [bad_Xδ] using this
  obtain ⟨q_raw, χ_raw, t, hq_raw1, hq_rawQ, ht_raw, hD_raw⟩ := hz₀_X
  obtain ⟨q', χ', t', hq'1, hq'Q, ht', hD'⟩ := hz₀_Xδ
  -- Step 4: Lemma 4.1 (`t`-tightening) from `H1` + pointwise pretentious triangle inequality
  have ht_tight : |t| ≤ (Q + 1) * (X : ℝ) ^ δ := by
    have hXδ_le_rpow : (Xδ : ℝ) ≤ (X : ℝ) ^ δ := Nat.floor_le (by positivity)
    have hXδ_le_X : Xδ ≤ X := by
      have : (Xδ : ℝ) ≤ (X : ℝ) := by
        calc (Xδ : ℝ) ≤ (X : ℝ) ^ δ := hXδ_le_rpow
          _ ≤ (X : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hδ_lt.le
          _ = (X : ℝ) := Real.rpow_one _
      exact_mod_cast this
    have hdiff_lt : |t' - t| < (X : ℝ) ^ δ := by
      by_contra hge; push Not at hge
      have hdiff_le : |t' - t| ≤ 2 * Q * (X : ℝ) := by
        have h1 : |t'| ≤ Q * (X : ℝ) := by
          calc |t'| ≤ Q * (Xδ : ℝ) := ht'
            _ ≤ Q * (X : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hXδ_le_X) (by linarith)
        calc |t' - t| ≤ |t'| + |t| := abs_sub t' t
          _ ≤ Q * (X : ℝ) + Q * (X : ℝ) := add_le_add h1 ht_raw
          _ = 2 * Q * (X : ℝ) := by ring
      have hgt := hX_VK X hX_ge_VK q_raw q' χ_raw χ' t t' hq_raw1 hq_rawQ hq'1 hq'Q hge hdiff_le
      have hle : ∑ p ∈ (Finset.Icc 1 Xδ).filter Nat.Prime,
          (1 - (χ_raw (p : ZMod q_raw) * star (χ' (p : ZMod q')) *
            Complex.exp (-Complex.I * (t' - t) * Real.log (p : ℝ))).re) / (p : ℝ) ≤ 4 * Q := by
        have hpt_sum : ∀ p ∈ (Finset.Icc 1 Xδ).filter Nat.Prime,
            (1 - (χ_raw (p : ZMod q_raw) * star (χ' (p : ZMod q')) *
              Complex.exp (-Complex.I * (t' - t) * Real.log (p : ℝ))).re) / (p : ℝ) ≤
            2 * ((1 - (mulEval z₀ p * star (χ_raw (p : ZMod q_raw)) *
              Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ)) +
            2 * ((1 - (mulEval z₀ p * star (χ' (p : ZMod q')) *
              Complex.exp (-Complex.I * t' * Real.log (p : ℝ))).re) / (p : ℝ)) := by
          intro p hp
          have hpp := (Finset.mem_filter.mp hp).2
          have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpp.pos
          have htri := pretentious_triangle_pointwise hq_raw1 hq'1 χ_raw χ' t t' (mulEval z₀ p)
            (mulEval_norm z₀ hpp.one_lt.le) hpp
          have := div_le_div_of_nonneg_right htri hp_pos.le
          rw [add_div, mul_div_assoc, mul_div_assoc] at this
          exact this
        have hsub : (Finset.Icc 1 Xδ).filter Nat.Prime ⊆ (Finset.Icc 1 X).filter Nat.Prime :=
          Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right hXδ_le_X)
        have hnn : ∀ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
            0 ≤ (1 - (mulEval z₀ p * star (χ_raw (p : ZMod q_raw)) *
              Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) := by
          intro p hp
          have hpp := (Finset.mem_filter.mp hp).2
          apply div_nonneg _ (Nat.cast_nonneg _)
          rw [mul_assoc]
          refine pretentious_term_nonneg (le_of_eq (mulEval_norm z₀ hpp.one_lt.le)) ?_
          rw [norm_mul, norm_star]
          have he : ‖Complex.exp (-Complex.I * t * Real.log (p : ℝ))‖ = 1 := by
            have : (-Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ)) =
                -Complex.I * ((t * Real.log (p : ℝ) : ℝ) : ℂ) := by push_cast; ring
            rw [this]; exact norm_exp_neg_I_mul_real _
          rw [he, mul_one]; exact dirichlet_norm_le_one χ_raw _
        let f1 : ℕ → ℝ := fun p => (1 - (mulEval z₀ p * star (χ_raw (p : ZMod q_raw)) *
          Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ)
        let f2 : ℕ → ℝ := fun p => (1 - (mulEval z₀ p * star (χ' (p : ZMod q')) *
          Complex.exp (-Complex.I * t' * Real.log (p : ℝ))).re) / (p : ℝ)
        have hf1_sub : ∑ p ∈ (Finset.Icc 1 Xδ).filter Nat.Prime, f1 p ≤
            ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, f1 p :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ => hnn p hp
        calc ∑ p ∈ (Finset.Icc 1 Xδ).filter Nat.Prime,
              (1 - (χ_raw (p : ZMod q_raw) * star (χ' (p : ZMod q')) *
                Complex.exp (-Complex.I * (t' - t) * Real.log (p : ℝ))).re) / (p : ℝ)
            ≤ ∑ p ∈ (Finset.Icc 1 Xδ).filter Nat.Prime, (2 * f1 p + 2 * f2 p) :=
              Finset.sum_le_sum hpt_sum
          _ = 2 * (∑ p ∈ (Finset.Icc 1 Xδ).filter Nat.Prime, f1 p) +
              2 * (∑ p ∈ (Finset.Icc 1 Xδ).filter Nat.Prime, f2 p) := by
              rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
          _ ≤ 2 * (∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, f1 p) + 2 * Q := by
              linarith [hf1_sub, hD']
          _ ≤ 2 * Q + 2 * Q := by linarith [hD_raw]
          _ = 4 * Q := by ring
      linarith
    calc |t| = |t' - (t' - t)| := by ring_nf
      _ ≤ |t'| + |t' - t| := abs_sub t' (t' - t)
      _ ≤ Q * (Xδ : ℝ) + (X : ℝ) ^ δ := add_le_add ht' hdiff_lt.le
      _ ≤ Q * (X : ℝ) ^ δ + (X : ℝ) ^ δ := by gcongr
      _ = (Q + 1) * (X : ℝ) ^ δ := by ring
  -- Step 5: Primitive character reduction `χ_raw ↦ χ := χ_raw.primitiveCharacter`
  have : NeZero q_raw := ⟨by omega⟩
  set q : ℕ := χ_raw.conductor
  let χ : DirichletCharacter ℂ q := χ_raw.primitiveCharacter
  have hq_dvd : q ∣ q_raw := χ_raw.conductor_dvd_level
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero χ_raw.conductor_ne_zero
  have hqQ : (q : ℝ) ≤ Q := le_trans (by exact_mod_cast Nat.le_of_dvd (by omega) hq_dvd) hq_rawQ
  have hq_le_Qnat : q ≤ Qnat := by
    have : (q : ℝ) ≤ (Qnat : ℝ) := hqQ.trans hQ_le_Qnat
    exact_mod_cast this
  have hχ_prim : χ.IsPrimitive := χ_raw.primitiveCharacter_isPrimitive
  have hD_prim : ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
      (1 - (mulEval z₀ p * star (χ (p : ZMod q)) *
        Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤ 2 * Q := by
    have hpt : ∀ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
        (1 - (mulEval z₀ p * star (χ (p : ZMod q)) *
          Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) ≤
        2 * ((1 - (mulEval z₀ p * star (χ_raw (p : ZMod q_raw)) *
          Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ)) := by
      intro p hp
      have hpp := (Finset.mem_filter.mp hp).2
      have he : ‖Complex.exp (-Complex.I * t * Real.log (p : ℝ))‖ = 1 := by
        have : (-Complex.I * (t : ℂ) * (Real.log (p : ℝ) : ℂ)) =
            -Complex.I * ((t * Real.log (p : ℝ) : ℝ) : ℂ) := by push_cast; ring
        rw [this]; exact norm_exp_neg_I_mul_real _
      by_cases hd : p ∣ q_raw
      · rw [dirichlet_apply_eq_zero_of_dvd hq_raw1 χ_raw hpp hd]
        simp only [star_zero, mul_zero, zero_mul, Complex.zero_re, sub_zero]
        have hre_ge : -1 ≤ (mulEval z₀ p * star (χ (p : ZMod q)) *
            Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re := by
          have h1 := Complex.abs_re_le_norm (mulEval z₀ p * star (χ (p : ZMod q)) *
              Complex.exp (-Complex.I * t * Real.log (p : ℝ)))
          have h2 : ‖mulEval z₀ p * star (χ (p : ZMod q)) *
              Complex.exp (-Complex.I * t * Real.log (p : ℝ))‖ ≤ 1 := by
            rw [norm_mul, norm_mul, mulEval_norm z₀ hpp.one_lt.le, one_mul, norm_star, he, mul_one]
            exact dirichlet_norm_le_one χ _
          linarith [neg_abs_le (mulEval z₀ p * star (χ (p : ZMod q)) *
              Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re]
        have hnum : 1 - (mulEval z₀ p * star (χ (p : ZMod q)) *
            Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re ≤ 2 := by linarith
        have hdiv := div_le_div_of_nonneg_right hnum (Nat.cast_nonneg (α := ℝ) p)
        linarith [show (2 : ℝ) / (p : ℝ) = 2 * (1 / (p : ℝ)) by ring]
      · have hcop : IsCoprime (p : ℤ) (q_raw : ℤ) :=
          Nat.isCoprime_iff_coprime.mpr (hpp.coprime_iff_not_dvd.mpr hd)
        have heq := χ_raw.primitiveCharacter_apply_of_isCoprime hcop
        have heq' : χ (p : ZMod q) = χ_raw (p : ZMod q_raw) := by
          simpa [χ, Int.cast_natCast] using heq
        rw [heq']
        have hnn : 0 ≤ (1 - (mulEval z₀ p * star (χ_raw (p : ZMod q_raw)) *
            Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) := by
          apply div_nonneg _ (Nat.cast_nonneg _)
          rw [mul_assoc]
          refine pretentious_term_nonneg (le_of_eq (mulEval_norm z₀ hpp.one_lt.le)) ?_
          rw [norm_mul, norm_star, he, mul_one]; exact dirichlet_norm_le_one χ_raw _
        linarith
    calc ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, _
        ≤ ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
            2 * ((1 - (mulEval z₀ p * star (χ_raw (p : ZMod q_raw)) *
              Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ)) :=
          Finset.sum_le_sum hpt
      _ = 2 * ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime, _ := (Finset.mul_sum _ _ _).symm
      _ ≤ 2 * Q := by gcongr
  -- Step 6: Factorize `g(n) = χ̃(n) * exp(i * t * log n) * h(n)`
  obtain ⟨χt, h, hh0, hχt_mul, hh_mul, hχt_norm, hh_norm, hχt_coprime, hfactor, hh_p_one, hh_pret⟩ :=
    step6_factorize z₀ hq1 χ hD_prim
  -- Step 7: Eliminate `n^{it}` on the deterministic `z₀` to bound the `χ̃ · h` weighted energy
  have hreal_F : Summable (fun n => term n z₀) ∧
      (∑' n, term n z₀) ≤ 192 * B * Real.log (X : ℝ) + 1 := by
    have hnetop : F_en z₀ ≠ ⊤ := ne_top_of_lt (hz₀_E.trans_le le_top)
    have hsum : Summable (fun n => term n z₀) := by
      have h1 := ENNReal.tsum_coe_ne_top_iff_summable.mp (by
        convert hnetop using 1
        refine tsum_congr fun n => ?_
        rw [ENNReal.ofReal_eq_coe_nnreal (hterm_nonneg n z₀)])
      exact NNReal.summable_coe.mpr h1 |>.congr fun n => by simp
    refine ⟨hsum, ?_⟩
    have hle : ENNReal.ofReal (∑' n, term n z₀) ≤
        ENNReal.ofReal (192 * B * Real.log (X : ℝ) + 1) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun n => hterm_nonneg n z₀) hsum]
      exact hz₀_E.le
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  have hEχh_bound := step7_elim_nit hB hQ1 hH_pos hδ_pos (by linarith) hlogX_ge1 hlogX_ge_H2
    hXδ_sq rfl ht_tight (mulEval z₀) χt h hχt_norm hh_norm hfactor hreal_F
  -- Step 8: Apply `H2` to `h` and decouple `χ̃` and `h` over good residue classes modulo `q^k`
  obtain ⟨S, hS_lb, hS_ap⟩ := hEuler_unif q (Finset.mem_Icc.mpr ⟨hq1, hq_le_Qnat⟩) (by linarith)
    X hX_ge_E h hh0 hh_mul hh_norm hh_p_one hh_pret
  have hcontra410 := step8_decouple_contra410 hB hc_pos rfl hH_pos hk_ge1 hq1 hq_le_Qnat
    hlogX_ge1 hlogX_shift χ χt h hχt_mul hχt_norm hh_norm hχt_coprime hEχh_bound hS_lb hS_ap
  -- Step 9: Dispose of the easy case `q = 1`
  by_cases hq_eq1 : q = 1
  · exact step9_q_eq_one hq_eq1 hH_pos hH_sq_gt χ χt hχt_coprime hcontra410
  -- Step 10: `q ≥ 2` — Reinstate bad `a`, apply Granville's orthogonality, and derive contradiction
  have hq2 : 2 ≤ q := by omega
  have hpythag_bd := step10_full_Asum_pythag hQ1 hH_pos hk_ge1 hq2 hqQ h2k_large
    χ hχ_prim χt hχt_mul hχt_norm hχt_coprime hcontra410
  have hI_gt : 8 * Q * (C₀ + 1) < (I : ℝ) := by
    dsimp [I]; push_cast; linarith [Nat.le_ceil (8 * Q * (C₀ + 1))]
  exact step10_diag_contradiction hQ1 hQnat_ge1 hI_gt hHhalf_pos (le_max_right _ _) rfl
    (le_max_left _ _) hq2 hqQ hq_le_Qnat χ hpythag_bd

end OMA.R_Erdos67_erdos_67_R1_H2_R1
