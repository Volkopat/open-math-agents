import OMAReductions.R_Erdos67_erdos_67_R1

/-!
# Reduction of `Erdos67.erdos_67.R1.H1` (Tao's Logarithmically Averaged Two-Point Elliott Conjecture)

Following Terence Tao, *The logarithmically averaged Chowla and Elliott conjectures for two-point
correlations*, Forum Math. Pi **4** (2016), e8 (`arXiv:1509.05422`), specialized to the
`S¹`-valued completely multiplicative self-correlation case `g₁ = g`, `g₂ = star g` (`a = 1`,
`b = 0`, `c_p = 1`), we reduce `OMA.R_Erdos67_erdos_67_R1.H1` to three canonical theorems:

1. (`H1`) **Matomäki–Radziwiłł–Tao Fourier uniformity in short intervals** (Proposition 2.4 of
   Tao 2016; Theorem 2.3 of Matomäki–Radziwiłł–Tao 2015): non-pretentious `S¹`-valued completely
   multiplicative functions have small logarithmically averaged short-interval exponential sums
   uniformly in the frequency `α ∈ ℝ`.
2. (`H2`) **Tao's entropy decrement and bilinear Hoeffding decoupling** (Section 3 of Tao 2016):
   for any `h ≥ 1`, `δ ∈ (0, 1/4]`, `η > 0`, and `H₀ ≥ 2`, there exist `H₁ ≥ H₀` and `A ≥ 1` such
   that for any `X ≥ A` and any 1-bounded `g : ℕ → ℂ`, there is a scale `H ∈ [H₀, H₁]` where
   replacing `1_{p ∣ n + j}` by `1 / p` in the prime-averaged bilinear form changes the
   logarithmic expectation by at most `η H / log H`.
3. (`H3`) **Prime reciprocal density and Green–Tao/Selberg `L⁴` restriction for primes**
   (Lemma 3.5 of Tao 2016): on `P_H = {p prime : δ H / 2 ≤ p ≤ δ H}`, the reciprocal sum
   `∑_{p ∈ P_H} 1 / p` is comparable to `1 / log H` and the discrete `L⁴` moment
   `∑_{k < H} ‖∑_{p ∈ P_H} (1/p) e(-k p / H)‖⁴ ≪_δ 1 / (log H)⁴`.

Inside `main`, we prove all remaining steps of Tao's paper completely from scratch:
- Symmetry reduction to `h₁ < h₂` (`h = h₂ - h₁ ≥ 1`) and shift `n + h₁ ↦ n`.
- Explicit harmonic-sum estimates `∑_{n ∈ (√X, X]} 1 / n ≈ (1 / 2) log X` and **Lemma 2.5
  (logarithmic affine invariance)** for `1_{p ∣ n + j} g(n + j) conj(g(n + j + ph))`.
- **Proposition 2.6**: lower bound `≥ (c₁ ε / 8) H / log H` for the prime-averaged bilinear form.
- Application of `H2` to decouple `1_{p ∣ n + j}` to `1 / p`.
- **Lemma 3.4 (Hardy–Littlewood circle method)**: discrete Fourier inversion, orthogonality,
  Plancherel's identity, and Cauchy–Schwarz on `ZMod H`, splitting frequencies into the major
  spectrum `Ξ_H` and minor spectrum.
- Markov bound `#Ξ_H ≤ h * C / γ⁴` from `H3`, combined with `H1` over `ξ ∈ Ξ_H`, yielding
  the final contradiction.
-/

-- Reduction Erdos67.erdos_67.R1.H1.R1 of Erdos67.erdos_67.R1.H1
-- Credit: @tkaiman
-- Each H becomes its own step once this file is accepted. Proving all of them closes the step.

open Filter Finset Complex
open scoped Topology Classical BigOperators

namespace OMA.R_Erdos67_erdos_67_R1_H1_R1

/- ### Helper 1: Basic properties of `mulEval` and `e(α) = exp(2πi α)` -/

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

private lemma mulEval_norm (z : ℕ → Metric.sphere (0 : ℂ) 1) {n : ℕ} (hn : 1 ≤ n) :
    ‖if n = 0 then (0 : ℂ) else n.factorization.prod fun p e => (z p).1 ^ e‖ = 1 := by
  rw [if_neg (by omega : n ≠ 0), Finsupp.prod, norm_prod]
  exact Finset.prod_eq_one fun p _ => by
    rw [norm_pow, mem_sphere_zero_iff_norm.mp (z p).2, one_pow]

private lemma mulEval_norm_le_one (z : ℕ → Metric.sphere (0 : ℂ) 1) (n : ℕ) :
    ‖if n = 0 then (0 : ℂ) else n.factorization.prod fun p e => (z p).1 ^ e‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [hn]
  · rw [mulEval_norm z (by omega)]

private lemma norm_e_real (r : ℝ) : ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ))‖ = 1 := by
  have : 2 * (Real.pi : ℂ) * Complex.I * (r : ℂ) = ((2 * Real.pi * r : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

private lemma e_int (k : ℤ) : Complex.exp (2 * Real.pi * Complex.I * (k : ℂ)) = 1 := by
  have : 2 * (Real.pi : ℂ) * Complex.I * (k : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

/- ### Helper 2: Discrete Fourier inversion and Plancherel on `ZMod H` -/

private lemma zmod_orthogonality {H : ℕ} [NeZero H] (r : ZMod H) :
    (∑ j : ZMod H,
      Complex.exp (2 * Real.pi * Complex.I * (((r.val : ℕ) : ℂ) * ((j.val : ℕ) : ℂ) / (H : ℂ)))) =
    if r = 0 then (H : ℂ) else 0 := by
  have hH : 1 ≤ H := Nat.pos_of_ne_zero (NeZero.ne H)
  have hHne : (H : ℂ) ≠ 0 := by exact_mod_cast (show H ≠ 0 by omega)
  by_cases hr : r = 0
  · subst hr
    simp only [ZMod.val_zero, Nat.cast_zero, zero_mul, zero_div, mul_zero, Complex.exp_zero,
      Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one, ↓reduceIte]
  · rw [if_neg hr]
    set ω : ℂ := Complex.exp (2 * Real.pi * Complex.I * (((r.val : ℕ) : ℂ) / (H : ℂ)))
    have hω_ne1 : ω ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨k, hk⟩ := h1
      have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero, Complex.I_ne_zero]
      have hdiv : ((r.val : ℕ) : ℂ) / (H : ℂ) = (k : ℂ) := by
        apply mul_left_cancel₀ h2pi
        calc 2 * Real.pi * Complex.I * (((r.val : ℕ) : ℂ) / (H : ℂ))
            = (k : ℂ) * (2 * Real.pi * Complex.I) := hk
          _ = 2 * Real.pi * Complex.I * (k : ℂ) := by ring
      have hmul : ((r.val : ℕ) : ℂ) = (k : ℂ) * (H : ℂ) := (div_eq_iff hHne).mp hdiv
      have hmul_int : (r.val : ℤ) = k * (H : ℤ) := by exact_mod_cast hmul
      have hr_pos : 0 < r.val := Nat.pos_of_ne_zero fun h0 => hr (by
        rw [← ZMod.natCast_zmod_val r, h0, Nat.cast_zero])
      have hr_lt : r.val < H := r.val_lt
      have hk_pos : 0 < k := by nlinarith
      have hk_lt : k < 1 := by nlinarith
      omega
    have hbij : ∑ j : ZMod H,
        Complex.exp (2 * Real.pi * Complex.I * (((r.val : ℕ) : ℂ) * ((j.val : ℕ) : ℂ) / (H : ℂ))) =
        ∑ k ∈ Finset.range H, ω ^ k := by
      refine Finset.sum_bij (fun j _ => j.val) ?_ ?_ ?_ ?_
      · intro j _; exact Finset.mem_range.mpr j.val_lt
      · intro j₁ _ j₂ _ h; exact ZMod.val_injective H h
      · intro k hk
        refine ⟨(k : ZMod H), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)⟩
      · intro j _
        dsimp [ω]
        rw [← Complex.exp_nat_mul]
        congr 1; ring
    rw [hbij, geom_sum_eq hω_ne1]
    have hωH : ω ^ H = 1 := by
      dsimp [ω]
      rw [← Complex.exp_nat_mul]
      have : (H : ℂ) * (2 * Real.pi * Complex.I * (((r.val : ℕ) : ℂ) / (H : ℂ))) =
          2 * Real.pi * Complex.I * (((r.val : ℤ) : ℂ)) := by
        push_cast; field_simp [hHne]
      rw [this, e_int]
    rw [hωH, sub_self, zero_div]

private lemma zmod_exp_mod {H : ℕ} [NeZero H] (a b : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * ((((a : ZMod H).val : ℕ) : ℂ) * (b : ℂ) / (H : ℂ))) =
    Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) * (b : ℂ) / (H : ℂ))) := by
  have hH : 1 ≤ H := Nat.pos_of_ne_zero (NeZero.ne H)
  have hHne : (H : ℂ) ≠ 0 := by exact_mod_cast (show H ≠ 0 by omega)
  have hmod : (((a : ZMod H).val : ℤ) : ZMod H) = (a : ZMod H) := by simp
  have hdvd : (H : ℤ) ∣ (((a : ZMod H).val : ℤ) - a) := by
    rwa [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, sub_eq_zero]
  obtain ⟨q, hq⟩ := hdvd
  have hdiff : 2 * Real.pi * Complex.I * ((((a : ZMod H).val : ℕ) : ℂ) * (b : ℂ) / (H : ℂ)) =
      2 * Real.pi * Complex.I * ((a : ℂ) * (b : ℂ) / (H : ℂ)) +
      2 * Real.pi * Complex.I * (((q * b : ℤ) : ℂ)) := by
    have hqC : (((a : ZMod H).val : ℕ) : ℂ) = (a : ℂ) + (H : ℂ) * (q : ℂ) := by
      have : (((a : ZMod H).val : ℤ) : ℂ) = (a : ℂ) + (H : ℂ) * (q : ℂ) := by
        exact_mod_cast (show ((a : ZMod H).val : ℤ) = a + (H : ℤ) * q by linarith)
      simpa using this
    rw [hqC]; push_cast; field_simp [hHne]
  rw [hdiff, Complex.exp_add, e_int, mul_one]

private lemma zmod_plancherel {H : ℕ} [NeZero H] (x : ZMod H → ℂ) :
    ∑ ξ : ZMod H,
      ‖(1 / (H : ℂ)) * ∑ j : ZMod H,
        x j * Complex.exp (-2 * Real.pi * Complex.I * (((j.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))‖ ^ 2 =
    (1 / (H : ℝ)) * ∑ j : ZMod H, ‖x j‖ ^ 2 := by
  have hH : 1 ≤ H := Nat.pos_of_ne_zero (NeZero.ne H)
  have hHne : (H : ℂ) ≠ 0 := by exact_mod_cast (show H ≠ 0 by omega)
  apply Complex.ofReal_injective
  push_cast
  have hsq : ∀ z : ℂ, (‖z‖ : ℂ) ^ 2 = z * star z := fun z => by
    rw [Complex.star_def, Complex.mul_conj']
  simp_rw [hsq]
  have hstar_e : ∀ (j ξ : ZMod H),
      star (Complex.exp (-2 * Real.pi * Complex.I * (((j.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))) =
      Complex.exp (2 * Real.pi * Complex.I * (((j.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) := by
    intro j ξ
    rw [Complex.star_def, ← Complex.exp_conj]
    congr 1
    simp only [map_neg, map_mul, map_div₀, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
      Complex.conj_natCast]
    ring
  have hstarH : star (H : ℂ) = (H : ℂ) := by rw [Complex.star_def, Complex.conj_natCast]
  have hexp : ∀ ξ : ZMod H,
      ((1 / (H : ℂ)) * ∑ j : ZMod H,
        x j * Complex.exp (-2 * Real.pi * Complex.I * (((j.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))) *
      star ((1 / (H : ℂ)) * ∑ j : ZMod H,
        x j * Complex.exp (-2 * Real.pi * Complex.I * (((j.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))) =
      (1 / ((H : ℂ) ^ 2)) * ∑ j₁ : ZMod H, ∑ j₂ : ZMod H,
        (x j₁ * star (x j₂)) *
          Complex.exp (2 * Real.pi * Complex.I *
            ((((j₂ - j₁).val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) := by
    intro ξ
    rw [star_mul', star_div₀, star_one, hstarH, star_sum]
    let s₁ : ℂ := ∑ j₁ : ZMod H,
      x j₁ * Complex.exp (-2 * Real.pi * Complex.I * (((j₁.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))
    let s₂ : ℂ := ∑ j₂ : ZMod H,
      star (x j₂ * Complex.exp (-2 * Real.pi * Complex.I * (((j₂.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))))
    have hmul : (1 / (H : ℂ)) * s₁ * ((1 / (H : ℂ)) * s₂) =
        (1 / ((H : ℂ) ^ 2)) * (s₁ * s₂) := by ring
    change (1 / (H : ℂ)) * s₁ * ((1 / (H : ℂ)) * s₂) = _
    rw [hmul]; congr 1
    dsimp only [s₁, s₂]
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    rw [star_mul', hstar_e]
    have heq : Complex.exp (-2 * Real.pi * Complex.I * (((j₁.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) *
        Complex.exp (2 * Real.pi * Complex.I * (((j₂.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) =
        Complex.exp (2 * Real.pi * Complex.I * ((((j₂ - j₁).val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) := by
      rw [← Complex.exp_add]
      have hcast : (((j₂.val : ℤ) - (j₁.val : ℤ) : ℤ) : ZMod H) = j₂ - j₁ := by simp
      have hmod := zmod_exp_mod (H := H) ((j₂.val : ℤ) - (j₁.val : ℤ)) (ξ.val : ℤ)
      rw [hcast] at hmod
      simp only [Int.cast_natCast] at hmod
      rw [hmod]
      congr 1; push_cast; ring
    calc x j₁ * Complex.exp (-2 * Real.pi * Complex.I * (((j₁.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) *
          (star (x j₂) * Complex.exp (2 * Real.pi * Complex.I * (((j₂.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))))
        = (x j₁ * star (x j₂)) *
            (Complex.exp (-2 * Real.pi * Complex.I * (((j₁.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) *
              Complex.exp (2 * Real.pi * Complex.I * (((j₂.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))) := by ring
      _ = _ := by rw [heq]
  simp_rw [hexp, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ j₁ : ZMod H,
      ∑ ξ : ZMod H, ∑ j₂ : ZMod H,
        (x j₁ * star (x j₂)) *
          Complex.exp (2 * Real.pi * Complex.I * ((((j₂ - j₁).val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) =
      (H : ℂ) * (x j₁ * star (x j₁)) := by
    intro j₁
    rw [Finset.sum_comm]
    calc ∑ j₂ : ZMod H, ∑ ξ : ZMod H, (x j₁ * star (x j₂)) * _
        = ∑ j₂ : ZMod H, (x j₁ * star (x j₂)) *
            ∑ ξ : ZMod H, Complex.exp (2 * Real.pi * Complex.I * ((((j₂ - j₁).val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) := by
          refine Finset.sum_congr rfl fun j₂ _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ j₂ : ZMod H, (x j₁ * star (x j₂)) * (if j₂ - j₁ = 0 then (H : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun j₂ _ => by rw [zmod_orthogonality]
      _ = (x j₁ * star (x j₁)) * (H : ℂ) := by
          rw [Finset.sum_eq_single j₁]
          · simp
          · intro j₂ _ hne; rw [if_neg (sub_ne_zero.mpr hne), mul_zero]
          · intro h; exact absurd (Finset.mem_univ j₁) h
      _ = (H : ℂ) * (x j₁ * star (x j₁)) := mul_comm _ _
  simp_rw [hinner, ← Finset.mul_sum]
  field_simp [hHne]

private lemma zmod_convolution_fourier {H : ℕ} [NeZero H] (x₁ x₂ : ZMod H → ℂ) (d : ℕ) :
    ∑ j : ZMod H, x₁ j * x₂ (j + (d : ZMod H)) =
    (H : ℂ) * ∑ ξ : ZMod H,
      ((1 / (H : ℂ)) * ∑ j : ZMod H,
        x₁ j * Complex.exp (-2 * Real.pi * Complex.I * (((j.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))) *
      ((1 / (H : ℂ)) * ∑ j : ZMod H,
        x₂ j * Complex.exp (2 * Real.pi * Complex.I * (((j.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))) *
      Complex.exp (-2 * Real.pi * Complex.I * ((d : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) := by
  have hH : 1 ≤ H := Nat.pos_of_ne_zero (NeZero.ne H)
  have hHne : (H : ℂ) ≠ 0 := by exact_mod_cast (show H ≠ 0 by omega)
  have hexp : ∀ ξ : ZMod H,
      ((1 / (H : ℂ)) * ∑ j₁ : ZMod H,
        x₁ j₁ * Complex.exp (-2 * Real.pi * Complex.I * (((j₁.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))) *
      ((1 / (H : ℂ)) * ∑ j₂ : ZMod H,
        x₂ j₂ * Complex.exp (2 * Real.pi * Complex.I * (((j₂.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))) *
      Complex.exp (-2 * Real.pi * Complex.I * ((d : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) =
      (1 / ((H : ℂ) ^ 2)) * ∑ j₁ : ZMod H, ∑ j₂ : ZMod H,
        (x₁ j₁ * x₂ j₂) *
          Complex.exp (2 * Real.pi * Complex.I *
            ((((j₂ - (j₁ + (d : ZMod H))).val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) := by
    intro ξ
    let s₁ : ℂ := ∑ j₁ : ZMod H,
      x₁ j₁ * Complex.exp (-2 * Real.pi * Complex.I * (((j₁.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))
    let s₂ : ℂ := ∑ j₂ : ZMod H,
      x₂ j₂ * Complex.exp (2 * Real.pi * Complex.I * (((j₂.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))
    let ed : ℂ := Complex.exp (-2 * Real.pi * Complex.I * ((d : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))
    have hfac : (1 / (H : ℂ)) * s₁ * ((1 / (H : ℂ)) * s₂) * ed =
        (1 / ((H : ℂ) ^ 2)) * ((s₁ * s₂) * ed) := by ring
    change (1 / (H : ℂ)) * s₁ * ((1 / (H : ℂ)) * s₂) * ed = _
    rw [hfac]; congr 1
    dsimp only [s₁, s₂, ed]
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j₁ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j₂ _ => ?_
    have heq : Complex.exp (-2 * Real.pi * Complex.I * (((j₁.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) *
        Complex.exp (2 * Real.pi * Complex.I * (((j₂.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) *
        Complex.exp (-2 * Real.pi * Complex.I * ((d : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) =
        Complex.exp (2 * Real.pi * Complex.I *
          ((((j₂ - (j₁ + (d : ZMod H))).val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      have hcast : (((j₂.val : ℤ) - (j₁.val : ℤ) - (d : ℤ) : ℤ) : ZMod H) = j₂ - (j₁ + (d : ZMod H)) := by
        simp [sub_sub]
      have hmod := zmod_exp_mod (H := H) ((j₂.val : ℤ) - (j₁.val : ℤ) - (d : ℤ)) (ξ.val : ℤ)
      rw [hcast] at hmod
      simp only [Int.cast_natCast] at hmod
      rw [hmod]
      congr 1; push_cast; ring
    calc x₁ j₁ * Complex.exp (-2 * Real.pi * Complex.I * (((j₁.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) *
          (x₂ j₂ * Complex.exp (2 * Real.pi * Complex.I * (((j₂.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))) *
          Complex.exp (-2 * Real.pi * Complex.I * ((d : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))
        = (x₁ j₁ * x₂ j₂) *
            (Complex.exp (-2 * Real.pi * Complex.I * (((j₁.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) *
              Complex.exp (2 * Real.pi * Complex.I * (((j₂.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) *
              Complex.exp (-2 * Real.pi * Complex.I * ((d : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))) := by ring
      _ = _ := by rw [heq]
  simp_rw [hexp, ← Finset.mul_sum]
  rw [Finset.sum_comm]
  have hinner : ∀ j₁ : ZMod H,
      ∑ ξ : ZMod H, ∑ j₂ : ZMod H,
        (x₁ j₁ * x₂ j₂) *
          Complex.exp (2 * Real.pi * Complex.I *
            ((((j₂ - (j₁ + (d : ZMod H))).val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) =
      (H : ℂ) * (x₁ j₁ * x₂ (j₁ + (d : ZMod H))) := by
    intro j₁
    rw [Finset.sum_comm]
    calc ∑ j₂ : ZMod H, ∑ ξ : ZMod H, (x₁ j₁ * x₂ j₂) * _
        = ∑ j₂ : ZMod H, (x₁ j₁ * x₂ j₂) *
            ∑ ξ : ZMod H, Complex.exp (2 * Real.pi * Complex.I *
              ((((j₂ - (j₁ + (d : ZMod H))).val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) := by
          refine Finset.sum_congr rfl fun j₂ _ => (Finset.mul_sum _ _ _).symm
      _ = ∑ j₂ : ZMod H, (x₁ j₁ * x₂ j₂) * (if j₂ - (j₁ + (d : ZMod H)) = 0 then (H : ℂ) else 0) := by
          refine Finset.sum_congr rfl fun j₂ _ => by rw [zmod_orthogonality]
      _ = (x₁ j₁ * x₂ (j₁ + (d : ZMod H))) * (H : ℂ) := by
          rw [Finset.sum_eq_single (j₁ + (d : ZMod H))]
          · simp
          · intro j₂ _ hne; rw [if_neg (sub_ne_zero.mpr hne), mul_zero]
          · intro h; exact absurd (Finset.mem_univ _) h
      _ = (H : ℂ) * (x₁ j₁ * x₂ (j₁ + (d : ZMod H))) := mul_comm _ _
  simp_rw [hinner, ← Finset.mul_sum]
  field_simp [hHne]

/- ### Helper 3: Elementary harmonic sum and logarithmic affine invariance (Lemma 2.5) -/

private lemma harmonic_Icc_bounds {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Real.log ((b + 1 : ℕ) : ℝ) - Real.log (a : ℝ) ≤
      (∑ n ∈ Finset.Icc a b, (1 : ℝ) / (n : ℝ)) ∧
    (∑ n ∈ Finset.Icc a b, (1 : ℝ) / (n : ℝ)) ≤
      1 / (a : ℝ) + Real.log (b : ℝ) - Real.log (a : ℝ) := by
  have hlow : ∀ n : ℕ, 1 ≤ n → Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) ≤ 1 / (n : ℝ) := by
    intro n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    rw [← Real.log_div (by positivity) hn_pos.ne']
    calc Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ))
        ≤ ((n + 1 : ℕ) : ℝ) / (n : ℝ) - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ = 1 / (n : ℝ) := by push_cast; field_simp [hn_pos.ne']; ring
  have hup : ∀ n : ℕ, 2 ≤ n → 1 / (n : ℝ) ≤ Real.log (n : ℝ) - Real.log ((n - 1 : ℕ) : ℝ) := by
    intro n hn
    have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    have hn1_pos : (0 : ℝ) < ((n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - 1 by omega)
    rw [← Real.log_div hn_pos.ne' hn1_pos.ne']
    have hlog := Real.log_le_sub_one_of_pos (div_pos hn1_pos hn_pos)
    have hneg : -Real.log (((n - 1 : ℕ) : ℝ) / (n : ℝ)) = Real.log ((n : ℝ) / ((n - 1 : ℕ) : ℝ)) := by
      rw [← Real.log_inv, inv_div]
    have hsub : 1 - ((n - 1 : ℕ) : ℝ) / (n : ℝ) = 1 / (n : ℝ) := by
      have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
      rw [hcast]; field_simp [hn_pos.ne']; ring
    linarith
  constructor
  · have htele : ∀ k : ℕ, Real.log ((a + k + 1 : ℕ) : ℝ) - Real.log (a : ℝ) ≤
        ∑ n ∈ Finset.Icc a (a + k), (1 : ℝ) / (n : ℝ) := by
      intro k; induction k with
      | zero => simpa using hlow a ha
      | succ k ih =>
        have hsplit : Finset.Icc a (a + (k + 1)) = insert (a + k + 1) (Finset.Icc a (a + k)) := by
          ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnm : a + k + 1 ∉ Finset.Icc a (a + k) := by rw [Finset.mem_Icc]; omega
        rw [hsplit, Finset.sum_insert hnm]
        have hstep := hlow (a + k + 1) (by omega)
        have : a + (k + 1) + 1 = a + k + 1 + 1 := by omega
        rw [this]; linarith
    have := htele (b - a)
    rwa [Nat.add_sub_of_le hab] at this
  · have htele : ∀ k : ℕ, ∑ n ∈ Finset.Icc a (a + k), (1 : ℝ) / (n : ℝ) ≤
        1 / (a : ℝ) + Real.log ((a + k : ℕ) : ℝ) - Real.log (a : ℝ) := by
      intro k; induction k with
      | zero => simp
      | succ k ih =>
        have hsplit : Finset.Icc a (a + (k + 1)) = insert (a + k + 1) (Finset.Icc a (a + k)) := by
          ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
        have hnm : a + k + 1 ∉ Finset.Icc a (a + k) := by rw [Finset.mem_Icc]; omega
        rw [hsplit, Finset.sum_insert hnm]
        have hstep := hup (a + k + 1) (by omega)
        have hsub : a + k + 1 - 1 = a + k := by omega
        have hrew : a + (k + 1) = a + k + 1 := by omega
        rw [hsub] at hstep; rw [hrew]; linarith
    have := htele (b - a)
    rwa [Nat.add_sub_of_le hab] at this

private lemma log_shift_bound {X s : ℕ} (hX : 16 ≤ X) (hs : s ≤ Nat.sqrt X)
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖(∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, f (n + s) / (n : ℂ)) -
      (∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, f n / (n : ℂ))‖ ≤
    3 * (s : ℝ) / (Nat.sqrt X : ℝ) := by
  have hsq_ge4 : 4 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have hsq_pos : 1 ≤ Nat.sqrt X := by omega
  have hsq_r : (0 : ℝ) < (Nat.sqrt X : ℝ) := by exact_mod_cast hsq_pos
  have hov : Nat.sqrt X + 1 + s ≤ X := by
    have : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
    nlinarith
  -- Reindex the first sum by `m = n + s`
  have hreindex : ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, f (n + s) / (n : ℂ) =
      ∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) (X + s), f m / ((m - s : ℕ) : ℂ) := by
    refine Finset.sum_bij (fun n _ => n + s) ?_ ?_ ?_ ?_
    · intro n hn; rw [Finset.mem_Icc] at hn ⊢; omega
    · intro _ _ _ _ h; omega
    · intro m hm; rw [Finset.mem_Icc] at hm
      exact ⟨m - s, Finset.mem_Icc.mpr (by omega), by omega⟩
    · intro n _; simp
  rw [hreindex]
  have hS1 : Finset.Icc (Nat.sqrt X + 1 + s) (X + s) =
      Finset.Icc (Nat.sqrt X + 1 + s) X ∪ Finset.Icc (X + 1) (X + s) := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hd1 : Disjoint (Finset.Icc (Nat.sqrt X + 1 + s) X) (Finset.Icc (X + 1) (X + s)) := by
    rw [Finset.disjoint_left]; intro m h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
  have hS2 : Finset.Icc (Nat.sqrt X + 1) X =
      Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s) ∪ Finset.Icc (Nat.sqrt X + 1 + s) X := by
    ext m; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hd2 : Disjoint (Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s))
      (Finset.Icc (Nat.sqrt X + 1 + s) X) := by
    rw [Finset.disjoint_left]; intro m h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
  rw [hS1, Finset.sum_union hd1, hS2, Finset.sum_union hd2]
  have hrew : (∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m / ((m - s : ℕ) : ℂ)) +
      (∑ m ∈ Finset.Icc (X + 1) (X + s), f m / ((m - s : ℕ) : ℂ)) -
      ((∑ m ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), f m / (m : ℂ)) +
       (∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m / (m : ℂ))) =
      (∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m * (1 / ((m - s : ℕ) : ℂ) - 1 / (m : ℂ))) +
      (∑ m ∈ Finset.Icc (X + 1) (X + s), f m / ((m - s : ℕ) : ℂ)) -
      (∑ m ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), f m / (m : ℂ)) := by
    have : ∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m * (1 / ((m - s : ℕ) : ℂ) - 1 / (m : ℂ)) =
        (∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m / ((m - s : ℕ) : ℂ)) -
        (∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, f m / (m : ℂ)) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun m _ => by ring
    rw [this]; ring
  rw [hrew]
  have hB_ov : ‖∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X,
      f m * (1 / ((m - s : ℕ) : ℂ) - 1 / (m : ℂ))‖ ≤ (s : ℝ) / (Nat.sqrt X : ℝ) := by
    calc ‖∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, _‖
        ≤ ∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X,
            ‖f m * (1 / ((m - s : ℕ) : ℂ) - 1 / (m : ℂ))‖ := norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X,
            (1 / ((m - s : ℕ) : ℝ) - 1 / (m : ℝ)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm' := Finset.mem_Icc.mp hm
          have hnn : 0 ≤ 1 / ((m - s : ℕ) : ℝ) - 1 / (m : ℝ) := by
            rw [sub_nonneg]
            exact one_div_le_one_div_of_le (by exact_mod_cast (show 0 < m - s by omega))
              (by exact_mod_cast Nat.sub_le m s)
          rw [norm_mul]
          have h1 : ‖1 / ((m - s : ℕ) : ℂ) - 1 / (m : ℂ)‖ = 1 / ((m - s : ℕ) : ℝ) - 1 / (m : ℝ) := by
            have : (1 / ((m - s : ℕ) : ℂ) - 1 / (m : ℂ)) =
                ((1 / ((m - s : ℕ) : ℝ) - 1 / (m : ℝ) : ℝ) : ℂ) := by push_cast; ring
            rw [this, Complex.norm_real, Real.norm_of_nonneg hnn]
          rw [h1]
          exact mul_le_of_le_one_left hnn (hf m)
      _ ≤ (s : ℝ) / (Nat.sqrt X : ℝ) := by
          rw [Finset.sum_sub_distrib]
          have hsh : ∑ m ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, (1 : ℝ) / ((m - s : ℕ) : ℝ) =
              ∑ k ∈ Finset.Icc (Nat.sqrt X + 1) (X - s), (1 : ℝ) / (k : ℝ) := by
            refine Finset.sum_bij (fun m _ => m - s) ?_ ?_ ?_ ?_
            · intro m hm; rw [Finset.mem_Icc] at hm ⊢; omega
            · intro m₁ hm₁ m₂ hm₂ h; rw [Finset.mem_Icc] at hm₁ hm₂; omega
            · intro k hk; rw [Finset.mem_Icc] at hk
              exact ⟨k + s, Finset.mem_Icc.mpr (by omega), by omega⟩
            · intro _ _; rfl
          rw [hsh]
          have hsub1 : Finset.Icc (Nat.sqrt X + 1) (X - s) ⊆
              Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s) ∪ Finset.Icc (Nat.sqrt X + 1 + s) X := by
            intro k hk; rw [Finset.mem_Icc] at hk; simp only [Finset.mem_union, Finset.mem_Icc]; omega
          have hle1 : ∑ k ∈ Finset.Icc (Nat.sqrt X + 1) (X - s), (1 : ℝ) / (k : ℝ) ≤
              (∑ k ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), (1 : ℝ) / (k : ℝ)) +
              (∑ k ∈ Finset.Icc (Nat.sqrt X + 1 + s) X, (1 : ℝ) / (k : ℝ)) := by
            rw [← Finset.sum_union hd2]
            exact Finset.sum_le_sum_of_subset_of_nonneg hsub1 fun _ _ _ => by positivity
          have hhead : ∑ k ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), (1 : ℝ) / (k : ℝ) ≤
              (s : ℝ) / (Nat.sqrt X : ℝ) := by
            calc _ ≤ ∑ _k ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), (1 : ℝ) / (Nat.sqrt X : ℝ) := by
                  refine Finset.sum_le_sum fun k hk => ?_
                  exact one_div_le_one_div_of_le hsq_r (by exact_mod_cast (show Nat.sqrt X ≤ k by
                    have := (Finset.mem_Icc.mp hk).1; omega))
              _ = ((Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s)).card : ℝ) * (1 / (Nat.sqrt X : ℝ)) := by
                  simp
              _ = (s : ℝ) / (Nat.sqrt X : ℝ) := by
                  have hcard : (Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s)).card = s := by
                    simp [Nat.card_Icc]
                  rw [hcard]; ring
          linarith
  have hB_r : ‖∑ m ∈ Finset.Icc (X + 1) (X + s), f m / ((m - s : ℕ) : ℂ)‖ ≤
      (s : ℝ) / (Nat.sqrt X : ℝ) := by
    calc _ ≤ ∑ m ∈ Finset.Icc (X + 1) (X + s), ‖f m / ((m - s : ℕ) : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Finset.Icc (X + 1) (X + s), (1 : ℝ) / (Nat.sqrt X : ℝ) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm' := Finset.mem_Icc.mp hm
          rw [norm_div, Complex.norm_natCast]
          calc ‖f m‖ / ((m - s : ℕ) : ℝ) ≤ 1 / ((m - s : ℕ) : ℝ) :=
                div_le_div_of_nonneg_right (hf m) (Nat.cast_nonneg _)
            _ ≤ 1 / (Nat.sqrt X : ℝ) :=
                one_div_le_one_div_of_le hsq_r (by exact_mod_cast (show Nat.sqrt X ≤ m - s by omega))
      _ = (s : ℝ) / (Nat.sqrt X : ℝ) := by
          have hcard : (Finset.Icc (X + 1) (X + s)).card = s := by simp [Nat.card_Icc]
          simp [hcard, div_eq_mul_inv]
  have hB_l : ‖∑ m ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), f m / (m : ℂ)‖ ≤
      (s : ℝ) / (Nat.sqrt X : ℝ) := by
    calc _ ≤ ∑ m ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), ‖f m / (m : ℂ)‖ := norm_sum_le _ _
      _ ≤ ∑ _m ∈ Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s), (1 : ℝ) / (Nat.sqrt X : ℝ) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hm' := Finset.mem_Icc.mp hm
          rw [norm_div, Complex.norm_natCast]
          calc ‖f m‖ / (m : ℝ) ≤ 1 / (m : ℝ) := div_le_div_of_nonneg_right (hf m) (Nat.cast_nonneg _)
            _ ≤ 1 / (Nat.sqrt X : ℝ) :=
                one_div_le_one_div_of_le hsq_r (by exact_mod_cast (show Nat.sqrt X ≤ m by omega))
      _ = (s : ℝ) / (Nat.sqrt X : ℝ) := by
          have hcard : (Finset.Icc (Nat.sqrt X + 1) (Nat.sqrt X + s)).card = s := by
            simp [Nat.card_Icc]
          simp [hcard, div_eq_mul_inv]
  calc ‖_ + _ - _‖
      ≤ ‖_ + _‖ + ‖_‖ := norm_sub_le _ _
    _ ≤ (‖_‖ + ‖_‖) + ‖_‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((s : ℝ) / (Nat.sqrt X : ℝ) + (s : ℝ) / (Nat.sqrt X : ℝ)) + (s : ℝ) / (Nat.sqrt X : ℝ) :=
        add_le_add (add_le_add hB_ov hB_r) hB_l
    _ = 3 * (s : ℝ) / (Nat.sqrt X : ℝ) := by ring

/- ### Helper 4: Logarithmic affine invariance (Lemma 2.5 for `a = 1, b = 0`) -/

private lemma log_affine_invariance {X p j : ℕ} (hX : 16 ≤ X) (hp : 2 ≤ p)
    (hp_le : 2 * p * (j + 1) ≤ Nat.sqrt X)
    (f : ℕ → ℂ) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖(∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
        (if p ∣ n + j then f ((n + j) / p) / (n : ℂ) else 0)) -
      (1 / (p : ℂ)) * (∑ m ∈ Finset.Icc (Nat.sqrt X + 1) X, f m / (m : ℂ))‖ ≤
    (4 * Real.log (p : ℝ) + 8) / (p : ℝ) := by
  have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hsq_pos : 4 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have hsq_le_X : Nat.sqrt X ≤ X := Nat.sqrt_le_self X
  have h2p_le_sq : 2 * p ≤ Nat.sqrt X := by nlinarith
  have hj_le_sq : j ≤ Nat.sqrt X := by nlinarith
  let lo : ℕ := (Nat.sqrt X + j + p) / p
  let hi : ℕ := (X + j) / p
  have hbij : ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
      (if p ∣ n + j then f ((n + j) / p) / (n : ℂ) else 0) =
      ∑ m ∈ Finset.Icc lo hi, f m / ((p * m - j : ℕ) : ℂ) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun n _ => (n + j) / p) ?_ ?_ ?_ ?_
    · intro n hn
      have hn' := Finset.mem_filter.mp hn
      have hnI := Finset.mem_Icc.mp hn'.1
      rw [Finset.mem_Icc]
      obtain ⟨m, hm⟩ := hn'.2
      have hdiv : (n + j) / p = m := by rw [hm, Nat.mul_div_right m (by omega)]
      rw [hdiv]
      refine ⟨?_, ?_⟩
      · dsimp [lo]
        exact Nat.lt_succ_iff.mp ((Nat.div_lt_iff_lt_mul (by omega)).mpr (by nlinarith))
      · dsimp [hi]
        exact (Nat.le_div_iff_mul_le (by omega)).mpr (by nlinarith)
    · intro n₁ hn₁ n₂ hn₂ hEq
      have h1 := (Finset.mem_filter.mp hn₁).2
      have h2 := (Finset.mem_filter.mp hn₂).2
      have he1 := Nat.mul_div_cancel' h1
      have he2 := Nat.mul_div_cancel' h2
      rw [hEq] at he1; omega
    · intro m hm
      have hmI := Finset.mem_Icc.mp hm
      have hpm_lo : Nat.sqrt X + 1 + j ≤ p * m := by
        dsimp [lo] at hmI
        have h1 : p * ((Nat.sqrt X + j + p) / p) ≤ p * m := Nat.mul_le_mul_left p hmI.1
        have h2 := Nat.div_add_mod (Nat.sqrt X + j + p) p
        have h3 := Nat.mod_lt (Nat.sqrt X + j + p) (by omega : 0 < p)
        omega
      have hpm_hi : p * m ≤ X + j := by
        dsimp [hi] at hmI
        have := (Nat.le_div_iff_mul_le (by omega : 0 < p)).mp hmI.2
        linarith
      refine ⟨p * m - j, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, ?_⟩, ?_⟩
      · rw [Nat.sub_add_cancel (by omega)]; exact dvd_mul_right p m
      · rw [Nat.sub_add_cancel (by omega), Nat.mul_div_right m (by omega)]
    · intro n hn
      have hd := (Finset.mem_filter.mp hn).2
      have hmul : p * ((n + j) / p) = n + j := Nat.mul_div_cancel' hd
      rw [hmul, Nat.add_sub_cancel]
  rw [hbij]
  have hlo_ge1 : 1 ≤ lo := by
    dsimp [lo]; exact (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
  have hlo_le_sq : lo ≤ Nat.sqrt X + 1 := by
    dsimp [lo]
    exact Nat.div_le_of_le_mul (by nlinarith)
  have hhi_le_X : hi ≤ X := by
    dsimp [hi]; exact Nat.div_le_of_le_mul (by nlinarith)
  have hpm_gt_j : ∀ m ∈ Finset.Icc lo hi, Nat.sqrt X + 1 ≤ p * m - j ∧ 1 ≤ p * m - j := by
    intro m hm
    have hm1 := (Finset.mem_Icc.mp hm).1
    dsimp [lo] at hm1
    have h1 : p * ((Nat.sqrt X + j + p) / p) ≤ p * m := Nat.mul_le_mul_left p hm1
    have h2 := Nat.div_add_mod (Nat.sqrt X + j + p) p
    have h3 := Nat.mod_lt (Nat.sqrt X + j + p) (by omega : 0 < p)
    omega
  have hlo_lb : ((Nat.sqrt X : ℝ)) / (p : ℝ) ≤ (lo : ℝ) := by
    rw [div_le_iff₀ hp_pos]
    dsimp [lo]
    have h1 := Nat.div_add_mod (Nat.sqrt X + j + p) p
    have h2 := Nat.mod_lt (Nat.sqrt X + j + p) (by omega : 0 < p)
    have h3 : Nat.sqrt X ≤ p * ((Nat.sqrt X + j + p) / p) := by omega
    have h4 : (Nat.sqrt X : ℝ) ≤ (p : ℝ) * (((Nat.sqrt X + j + p) / p : ℕ) : ℝ) := by exact_mod_cast h3
    linarith
  have hstep1 : ‖(∑ m ∈ Finset.Icc lo hi, f m / ((p * m - j : ℕ) : ℂ)) -
      (1 / (p : ℂ)) * (∑ m ∈ Finset.Icc lo hi, f m / (m : ℂ))‖ ≤ 4 / (p : ℝ) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    calc ‖∑ m ∈ Finset.Icc lo hi, _‖
        ≤ ∑ m ∈ Finset.Icc lo hi, ‖f m / ((p * m - j : ℕ) : ℂ) - (1 / (p : ℂ)) * (f m / (m : ℂ))‖ :=
          norm_sum_le _ _
      _ ≤ ∑ m ∈ Finset.Icc lo hi, (j : ℝ) / (((p * m - j : ℕ) : ℝ) * ((p * m : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hmI := Finset.mem_Icc.mp hm
          have hmpos : 1 ≤ m := le_trans hlo_ge1 hmI.1
          have hpm := (hpm_gt_j m hm).2
          have hjle : j ≤ p * m := by omega
          have hrew : f m / ((p * m - j : ℕ) : ℂ) - (1 / (p : ℂ)) * (f m / (m : ℂ)) =
              f m * (((j : ℝ) / (((p * m - j : ℕ) : ℝ) * ((p * m : ℕ) : ℝ)) : ℝ) : ℂ) := by
            have hne1 : ((p * m - j : ℕ) : ℂ) ≠ 0 := by exact_mod_cast (by omega : p * m - j ≠ 0)
            have hne2 : (p : ℂ) ≠ 0 := by exact_mod_cast (by omega : p ≠ 0)
            have hne3 : (m : ℂ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
            have hsub : ((p * m - j : ℕ) : ℂ) = (p : ℂ) * (m : ℂ) - (j : ℂ) := by
              rw [Nat.cast_sub hjle, Nat.cast_mul]
            push_cast
            field_simp [hne1, hne2, hne3]
            rw [hsub]; ring
          rw [hrew, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
          exact mul_le_of_le_one_left (by positivity) (hf m)
      _ ≤ ∑ m ∈ Finset.Icc lo hi, (4 * (j : ℝ) / ((p : ℝ) ^ 2)) * (1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) := by
          refine Finset.sum_le_sum fun m hm => ?_
          have hmI := Finset.mem_Icc.mp hm
          have hmpos : 1 ≤ m := le_trans hlo_ge1 hmI.1
          have hpm := (hpm_gt_j m hm).1
          have hmj : (p * m : ℕ) ≤ 2 * (p * m - j) := by omega
          have hm_le : (m + 1 : ℕ) ≤ 2 * m := by omega
          have hm_r : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hmpos
          have hm1_r : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
          have hdiff : 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) = 1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) := by
            push_cast; field_simp [hm_r.ne', hm1_r.ne']; ring
          rw [hdiff]
          have hden : ((p : ℝ) ^ 2) * ((m : ℝ) * ((m + 1 : ℕ) : ℝ)) ≤
              4 * (((p * m - j : ℕ) : ℝ) * ((p * m : ℕ) : ℝ)) := by
            have h1 : (p : ℝ) * (m : ℝ) ≤ 2 * ((p * m - j : ℕ) : ℝ) := by exact_mod_cast hmj
            have h2 : ((m + 1 : ℕ) : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hm_le
            calc ((p : ℝ) ^ 2) * ((m : ℝ) * ((m + 1 : ℕ) : ℝ))
                = ((p : ℝ) * (m : ℝ)) * ((p : ℝ) * ((m + 1 : ℕ) : ℝ)) := by ring
              _ ≤ (2 * ((p * m - j : ℕ) : ℝ)) * ((p : ℝ) * (2 * (m : ℝ))) := by gcongr
              _ = 4 * (((p * m - j : ℕ) : ℝ) * ((p * m : ℕ) : ℝ)) := by push_cast; ring
          have hpmj_pos : (0 : ℝ) < ((p * m - j : ℕ) : ℝ) := by exact_mod_cast (hpm_gt_j m hm).2
          have hpm_pos : (0 : ℝ) < ((p * m : ℕ) : ℝ) := by positivity
          have h4mul : (4 * (j : ℝ) / ((p : ℝ) ^ 2)) * (1 / ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) =
              4 * (j : ℝ) / (((p : ℝ) ^ 2) * ((m : ℝ) * ((m + 1 : ℕ) : ℝ))) := by ring
          rw [h4mul, div_le_div_iff₀ (by positivity) (by positivity)]
          calc (j : ℝ) * (((p : ℝ) ^ 2) * ((m : ℝ) * ((m + 1 : ℕ) : ℝ)))
              ≤ (j : ℝ) * (4 * (((p * m - j : ℕ) : ℝ) * ((p * m : ℕ) : ℝ))) :=
                mul_le_mul_of_nonneg_left hden (Nat.cast_nonneg j)
            _ = 4 * (j : ℝ) * (((p * m - j : ℕ) : ℝ) * ((p * m : ℕ) : ℝ)) := by ring
      _ ≤ 4 / (p : ℝ) := by
          rw [← Finset.mul_sum]
          have htele : ∑ m ∈ Finset.Icc lo hi, ((1 : ℝ) / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) ≤ 1 / (lo : ℝ) := by
            by_cases hle : lo ≤ hi
            · have hrec : ∀ k : ℕ, ∑ m ∈ Finset.Icc lo (lo + k),
                  ((1 : ℝ) / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)) =
                  1 / (lo : ℝ) - 1 / ((lo + k + 1 : ℕ) : ℝ) := by
                intro k; induction k with
                | zero => simp
                | succ k ih =>
                  have hsp : Finset.Icc lo (lo + (k + 1)) = insert (lo + k + 1) (Finset.Icc lo (lo + k)) := by
                    ext m; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
                  have hnm : lo + k + 1 ∉ Finset.Icc lo (lo + k) := by rw [Finset.mem_Icc]; omega
                  rw [hsp, Finset.sum_insert hnm, ih]
                  have : lo + (k + 1) + 1 = lo + k + 1 + 1 := by omega
                  rw [this]; ring
              have hval := hrec (hi - lo)
              rw [Nat.add_sub_of_le hle] at hval
              rw [hval]; linarith [show (0 : ℝ) ≤ 1 / ((hi + 1 : ℕ) : ℝ) by positivity]
            · have hempty : Finset.Icc lo hi = ∅ := Finset.Icc_eq_empty hle
              rw [hempty, Finset.sum_empty]; positivity
          have hsq_r : (0 : ℝ) < (Nat.sqrt X : ℝ) := by exact_mod_cast (show 0 < Nat.sqrt X by omega)
          have hlo_inv : 1 / (lo : ℝ) ≤ (p : ℝ) / (Nat.sqrt X : ℝ) := by
            have := one_div_le_one_div_of_le (div_pos hsq_r hp_pos) hlo_lb
            simpa [one_div_div] using this
          have hj_le : (j : ℝ) / (Nat.sqrt X : ℝ) ≤ 1 / (p : ℝ) := by
            rw [div_le_div_iff₀ hsq_r hp_pos, one_mul]
            have : j * p ≤ Nat.sqrt X := by nlinarith
            exact_mod_cast this
          calc (4 * (j : ℝ) / ((p : ℝ) ^ 2)) * ∑ m ∈ Finset.Icc lo hi, _
              ≤ (4 * (j : ℝ) / ((p : ℝ) ^ 2)) * (1 / (lo : ℝ)) := by gcongr
            _ ≤ (4 * (j : ℝ) / ((p : ℝ) ^ 2)) * ((p : ℝ) / (Nat.sqrt X : ℝ)) := by gcongr
            _ = (4 / (p : ℝ)) * ((j : ℝ) / (Nat.sqrt X : ℝ)) := by field_simp [hp_pos.ne', hsq_r.ne']
            _ ≤ (4 / (p : ℝ)) * (1 / (p : ℝ)) := by gcongr
            _ ≤ (4 / (p : ℝ)) * 1 := by
                gcongr; rw [div_le_one hp_pos]; exact_mod_cast (show 1 ≤ p by omega)
            _ = 4 / (p : ℝ) := mul_one _
  have hlo_le_hi : lo ≤ hi := by
    have hX_ge : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
    have h1 : Nat.sqrt X + j + p ≤ X + j := by nlinarith
    exact Nat.div_le_div_right h1
  have hsq1_le_hi : Nat.sqrt X + 1 ≤ hi := by
    dsimp [hi]
    have hX_ge : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X
    have h1 : (Nat.sqrt X + 1) * p ≤ X + j := by nlinarith
    exact (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith)
  have hdiff_int : ‖(∑ m ∈ Finset.Icc lo hi, f m / (m : ℂ)) -
      (∑ m ∈ Finset.Icc (Nat.sqrt X + 1) X, f m / (m : ℂ))‖ ≤ 2 * Real.log (p : ℝ) + 4 := by
    have hA : Finset.Icc lo hi = Finset.Icc lo (Nat.sqrt X) ∪ Finset.Icc (Nat.sqrt X + 1) hi := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdA : Disjoint (Finset.Icc lo (Nat.sqrt X)) (Finset.Icc (Nat.sqrt X + 1) hi) := by
      rw [Finset.disjoint_left]; intro m h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
    have hB : Finset.Icc (Nat.sqrt X + 1) X =
        Finset.Icc (Nat.sqrt X + 1) hi ∪ Finset.Icc (hi + 1) X := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdB : Disjoint (Finset.Icc (Nat.sqrt X + 1) hi) (Finset.Icc (hi + 1) X) := by
      rw [Finset.disjoint_left]; intro m h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
    rw [hA, Finset.sum_union hdA, hB, Finset.sum_union hdB]
    have hcancel : (∑ m ∈ Finset.Icc lo (Nat.sqrt X), f m / (m : ℂ)) +
        (∑ m ∈ Finset.Icc (Nat.sqrt X + 1) hi, f m / (m : ℂ)) -
        ((∑ m ∈ Finset.Icc (Nat.sqrt X + 1) hi, f m / (m : ℂ)) +
         (∑ m ∈ Finset.Icc (hi + 1) X, f m / (m : ℂ))) =
        (∑ m ∈ Finset.Icc lo (Nat.sqrt X), f m / (m : ℂ)) -
        (∑ m ∈ Finset.Icc (hi + 1) X, f m / (m : ℂ)) := by ring
    rw [hcancel]
    have hL : ‖∑ m ∈ Finset.Icc lo (Nat.sqrt X), f m / (m : ℂ)‖ ≤ Real.log (p : ℝ) + 2 := by
      by_cases hle : lo ≤ Nat.sqrt X
      · calc ‖∑ m ∈ Finset.Icc lo (Nat.sqrt X), f m / (m : ℂ)‖
            ≤ ∑ m ∈ Finset.Icc lo (Nat.sqrt X), ‖f m / (m : ℂ)‖ := norm_sum_le _ _
          _ ≤ ∑ m ∈ Finset.Icc lo (Nat.sqrt X), (1 : ℝ) / (m : ℝ) := by
              refine Finset.sum_le_sum fun m _ => ?_
              rw [norm_div, Complex.norm_natCast]
              exact div_le_div_of_nonneg_right (hf m) (Nat.cast_nonneg _)
          _ ≤ 1 / (lo : ℝ) + Real.log (Nat.sqrt X : ℝ) - Real.log (lo : ℝ) :=
              (harmonic_Icc_bounds hlo_ge1 hle).2
          _ ≤ 1 + Real.log (p : ℝ) := by
              have hsq_r : (0 : ℝ) < (Nat.sqrt X : ℝ) := by exact_mod_cast (show 0 < Nat.sqrt X by omega)
              have hlog_le := Real.log_le_log (div_pos hsq_r hp_pos) hlo_lb
              rw [Real.log_div hsq_r.ne' hp_pos.ne'] at hlog_le
              have hinv : 1 / (lo : ℝ) ≤ 1 := by
                rw [div_le_one (by exact_mod_cast hlo_ge1)]; exact_mod_cast hlo_ge1
              linarith
          _ ≤ Real.log (p : ℝ) + 2 := by linarith
      · rw [Finset.Icc_eq_empty hle, Finset.sum_empty, norm_zero]
        have : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
        linarith
    have hR : ‖∑ m ∈ Finset.Icc (hi + 1) X, f m / (m : ℂ)‖ ≤ Real.log (p : ℝ) + 2 := by
      by_cases hle : hi + 1 ≤ X
      · calc ‖∑ m ∈ Finset.Icc (hi + 1) X, f m / (m : ℂ)‖
            ≤ ∑ m ∈ Finset.Icc (hi + 1) X, ‖f m / (m : ℂ)‖ := norm_sum_le _ _
          _ ≤ ∑ m ∈ Finset.Icc (hi + 1) X, (1 : ℝ) / (m : ℝ) := by
              refine Finset.sum_le_sum fun m _ => ?_
              rw [norm_div, Complex.norm_natCast]
              exact div_le_div_of_nonneg_right (hf m) (Nat.cast_nonneg _)
          _ ≤ 1 / ((hi + 1 : ℕ) : ℝ) + Real.log (X : ℝ) - Real.log ((hi + 1 : ℕ) : ℝ) :=
              (harmonic_Icc_bounds (by omega) hle).2
          _ ≤ 1 + Real.log (p : ℝ) := by
              have hhi_lb : (X : ℝ) / (p : ℝ) ≤ ((hi + 1 : ℕ) : ℝ) := by
                rw [div_le_iff₀ hp_pos]; dsimp [hi]
                have h1 := Nat.div_add_mod (X + j) p
                have h2 := Nat.mod_lt (X + j) (by omega : 0 < p)
                have h3 : X ≤ ((X + j) / p + 1) * p := by nlinarith
                exact_mod_cast h3
              have hX_r : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
              have hlog_le := Real.log_le_log (div_pos hX_r hp_pos) hhi_lb
              rw [Real.log_div hX_r.ne' hp_pos.ne'] at hlog_le
              have hinv : 1 / ((hi + 1 : ℕ) : ℝ) ≤ 1 := by
                rw [div_le_one (by positivity)]; exact_mod_cast (show 1 ≤ hi + 1 by omega)
              linarith
          _ ≤ Real.log (p : ℝ) + 2 := by linarith
      · rw [Finset.Icc_eq_empty hle, Finset.sum_empty, norm_zero]
        have : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
        linarith
    exact (norm_sub_le _ _).trans (by linarith)
  have hstep2 : ‖(1 / (p : ℂ)) * (∑ m ∈ Finset.Icc lo hi, f m / (m : ℂ)) -
      (1 / (p : ℂ)) * (∑ m ∈ Finset.Icc (Nat.sqrt X + 1) X, f m / (m : ℂ))‖ ≤
      (2 * Real.log (p : ℝ) + 4) / (p : ℝ) := by
    rw [← mul_sub, norm_mul, norm_div, norm_one, Complex.norm_natCast, one_div_mul_eq_div]
    exact div_le_div_of_nonneg_right hdiff_int hp_pos.le
  have htri := norm_add_le
    ((∑ m ∈ Finset.Icc lo hi, f m / ((p * m - j : ℕ) : ℂ)) -
      (1 / (p : ℂ)) * (∑ m ∈ Finset.Icc lo hi, f m / (m : ℂ)))
    ((1 / (p : ℂ)) * (∑ m ∈ Finset.Icc lo hi, f m / (m : ℂ)) -
      (1 / (p : ℂ)) * (∑ m ∈ Finset.Icc (Nat.sqrt X + 1) X, f m / (m : ℂ)))
  have hlog_nn : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
  calc ‖(∑ m ∈ Finset.Icc lo hi, f m / ((p * m - j : ℕ) : ℂ)) -
        (1 / (p : ℂ)) * (∑ m ∈ Finset.Icc (Nat.sqrt X + 1) X, f m / (m : ℂ))‖
      ≤ 4 / (p : ℝ) + (2 * Real.log (p : ℝ) + 4) / (p : ℝ) := by
        have := htri.trans (add_le_add hstep1 hstep2)
        simpa [sub_add_sub_cancel] using this
    _ = (2 * Real.log (p : ℝ) + 8) / (p : ℝ) := by ring
    _ ≤ (4 * Real.log (p : ℝ) + 8) / (p : ℝ) := by gcongr; linarith

/- ### Helper 5: Extracted core lemmas (harmonic bounds, Proposition 2.6, Markov bound, Lemma 3.4) -/

private lemma harmonic_sqrt_bounds {X : ℕ} (hX : 16 ≤ X) (hlog4 : 4 ≤ Real.log (X : ℝ)) :
    (1 / 4) * Real.log (X : ℝ) ≤ (∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 : ℝ) / (n : ℝ)) ∧
    (∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 : ℝ) / (n : ℝ)) ≤ (3 / 4) * Real.log (X : ℝ) := by
  have hsq_ge4 : 4 ≤ Nat.sqrt X := Nat.le_sqrt.mpr (by omega)
  have hsq1_le_X : Nat.sqrt X + 1 ≤ X := by
    have : Nat.sqrt X * Nat.sqrt X ≤ X := Nat.sqrt_le X; nlinarith
  obtain ⟨hL_lo, hL_hi⟩ := harmonic_Icc_bounds (by omega : 1 ≤ Nat.sqrt X + 1) hsq1_le_X
  have hX_pos : (0 : ℝ) < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hlog_sq_hi : Real.log ((Nat.sqrt X + 1 : ℕ) : ℝ) ≤ (1 / 2) * Real.log (X : ℝ) + 1 := by
    have h1 : ((Nat.sqrt X + 1 : ℕ) : ℝ) ≤ 2 * Real.sqrt (X : ℝ) := by
      have hsq_le : (Nat.sqrt X : ℝ) ≤ Real.sqrt (X : ℝ) := by
        rw [Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _), sq]
        exact_mod_cast Nat.sqrt_le X
      have h1_le : (1 : ℝ) ≤ Real.sqrt (X : ℝ) := by
        have : (1 : ℝ) ≤ (Nat.sqrt X : ℝ) := by exact_mod_cast (show 1 ≤ Nat.sqrt X by omega)
        linarith
      push_cast; linarith
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_mul (by norm_num) (Real.sqrt_pos.mpr hX_pos).ne', Real.log_sqrt hX_pos.le] at h2
    have hlog2 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    linarith
  have hlog_sq_lo : (1 / 2) * Real.log (X : ℝ) ≤ Real.log ((Nat.sqrt X + 1 : ℕ) : ℝ) := by
    have h1 : Real.sqrt (X : ℝ) ≤ ((Nat.sqrt X + 1 : ℕ) : ℝ) := by
      rw [Real.sqrt_le_left (by positivity), sq]
      exact_mod_cast (Nat.lt_succ_sqrt X).le
    have h2 := Real.log_le_log (Real.sqrt_pos.mpr hX_pos) h1
    rw [Real.log_sqrt hX_pos.le] at h2
    linarith
  have hlog_X1 : Real.log (X : ℝ) ≤ Real.log ((X + 1 : ℕ) : ℝ) :=
    Real.log_le_log hX_pos (by exact_mod_cast Nat.le_succ X)
  have hinv_le1 : (1 : ℝ) / ((Nat.sqrt X + 1 : ℕ) : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast (show 1 ≤ Nat.sqrt X + 1 by omega)
  constructor <;> linarith

private lemma prop26_bilinear_lb {X H H₁ h : ℕ} {ε δ : ℝ}
    (hX16 : 16 ≤ X) (hlog4 : 4 ≤ Real.log (X : ℝ))
    (hH_pos : 1 ≤ H) (hH_le_H₁ : H ≤ H₁) (hlogH_pos : 0 < Real.log (H : ℝ))
    (hε : 0 < ε) (hδ_h_le14 : δ * (h : ℝ) ≤ 1 / 4)
    (hH₁_sq : 2 * H₁ * (H₁ + 1) ≤ Nat.sqrt X)
    (haff_err : 8 * (4 * Real.log (H₁ : ℝ) + 8) / Real.log (X : ℝ) ≤ ε / 64)
    (P_H : Finset ℕ) (hp_in_P : ∀ p ∈ P_H, 2 ≤ p ∧ (p : ℝ) ≤ δ * (H : ℝ) ∧ p ≤ H)
    (hP_lb : 1 / (4 * Real.log (H : ℝ)) ≤ ∑ p ∈ P_H, (1 : ℝ) / (p : ℝ))
    (hP_ub : ∑ p ∈ P_H, (1 : ℝ) / (p : ℝ) ≤ 2 / Real.log (H : ℝ))
    (g : ℕ → ℂ) (hg_mul : ∀ a b, g (a * b) = g a * g b)
    (hg_norm : ∀ n, 1 ≤ n → ‖g n‖ = 1) (hg_le1 : ∀ n, ‖g n‖ ≤ 1)
    (hcorr_h : (3 * ε / 4) * Real.log (X : ℝ) ≤
      ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, g n * star (g (n + h)) / (n : ℂ)‖) :
    let L : ℝ := ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 : ℝ) / (n : ℝ)
    (11 * ε / 64) * (H : ℝ) / Real.log (H : ℝ) ≤
      ‖(1 / (L : ℂ)) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℂ)) *
        ∑ p ∈ P_H, ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then
            (if p ∣ n + j then (1 : ℂ) else 0) * g (n + j) * star (g (n + j + p * h))
          else 0‖ := by
  intro L
  have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
  have hL_bounds : (1 / 4) * Real.log (X : ℝ) ≤ L ∧ L ≤ (3 / 4) * Real.log (X : ℝ) :=
    harmonic_sqrt_bounds hX16 hlog4
  have hL_pos : 0 < L := by linarith [hL_bounds.1]
  let S_corr : ℂ := ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, g n * star (g (n + h)) / (n : ℂ)
  have hS_corr_divL : ε ≤ ‖S_corr / (L : ℂ)‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hL_pos.le, le_div_iff₀ hL_pos]
    calc ε * L ≤ ε * ((3 / 4) * Real.log (X : ℝ)) := mul_le_mul_of_nonneg_left hL_bounds.2 hε.le
      _ = (3 * ε / 4) * Real.log (X : ℝ) := by ring
      _ ≤ ‖S_corr‖ := hcorr_h
  let main_coeff : ℝ := ∑ p ∈ P_H, ((H - p * h : ℕ) : ℝ) / (p : ℝ)
  have hcoeff_lb : (3 / 16) * (H : ℝ) / Real.log (H : ℝ) ≤ main_coeff := by
    calc (3 / 16) * (H : ℝ) / Real.log (H : ℝ)
        = (3 / 4) * (H : ℝ) * (1 / (4 * Real.log (H : ℝ))) := by ring
      _ ≤ (3 / 4) * (H : ℝ) * (∑ p ∈ P_H, (1 : ℝ) / (p : ℝ)) := by gcongr
      _ = ∑ p ∈ P_H, ((3 / 4) * (H : ℝ)) / (p : ℝ) := by
          rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ main_coeff := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp_le := (hp_in_P p hp).2.1
          have hph_le : (p : ℝ) * (h : ℝ) ≤ (1 / 4) * (H : ℝ) := by nlinarith
          have hph_nat : p * h ≤ H := by
            have : ((p * h : ℕ) : ℝ) ≤ (H : ℝ) := by push_cast; linarith
            exact_mod_cast this
          have hsub_ge : (3 / 4) * (H : ℝ) ≤ ((H - p * h : ℕ) : ℝ) := by
            rw [Nat.cast_sub hph_nat, Nat.cast_mul]; linarith
          exact div_le_div_of_nonneg_right hsub_ge (Nat.cast_nonneg p)
  have hswap : (1 / (L : ℂ)) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℂ)) *
        ∑ p ∈ P_H, ∑ j ∈ Finset.Icc 1 H,
          (if j + p * h ≤ H then
            (if p ∣ n + j then (1 : ℂ) else 0) * g (n + j) * star (g (n + j + p * h))
          else 0) -
        (main_coeff : ℂ) * (S_corr / (L : ℂ)) =
      (1 / (L : ℂ)) * ∑ p ∈ P_H, ∑ j ∈ (Finset.Icc 1 H).filter (fun j => j + p * h ≤ H),
        ((∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
            if p ∣ n + j then (g ((n + j) / p) * star (g ((n + j) / p + h))) / (n : ℂ) else 0) -
          (1 / (p : ℂ)) * S_corr) := by
    have h1 : ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℂ)) *
          ∑ p ∈ P_H, ∑ j ∈ Finset.Icc 1 H,
            (if j + p * h ≤ H then
              (if p ∣ n + j then (1 : ℂ) else 0) * g (n + j) * star (g (n + j + p * h))
            else 0) =
        ∑ p ∈ P_H, ∑ j ∈ (Finset.Icc 1 H).filter (fun j => j + p * h ≤ H),
          ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
            if p ∣ n + j then (g ((n + j) / p) * star (g ((n + j) / p + h))) / (n : ℂ) else 0 := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [Finset.sum_comm, Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hjp : j + p * h ≤ H
      · rw [if_pos hjp]
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [if_pos hjp]
        by_cases hd : p ∣ n + j
        · rw [if_pos hd, if_pos hd, one_mul]
          set m : ℕ := (n + j) / p
          have hpm : n + j = p * m := (Nat.mul_div_cancel' hd).symm
          have hpmh : n + j + p * h = p * (m + h) := by rw [mul_add, ← hpm]
          have hgp : g p * star (g p) = 1 := by
            rw [Complex.star_def, Complex.mul_conj', hg_norm p (by have := (hp_in_P p hp).1; omega)]; norm_num
          rw [hpmh, hpm, hg_mul, hg_mul, star_mul']
          calc (1 / (n : ℂ)) * (g p * g m * (star (g p) * star (g (m + h))))
              = (g p * star (g p)) * (g m * star (g (m + h)) / (n : ℂ)) := by ring
            _ = g m * star (g (m + h)) / (n : ℂ) := by rw [hgp, one_mul]
        · simp [hd]
      · rw [if_neg hjp]
        exact Finset.sum_eq_zero fun n _ => by simp [hjp]
    have h2 : (main_coeff : ℂ) * S_corr =
        ∑ p ∈ P_H, ∑ _j ∈ (Finset.Icc 1 H).filter (fun j => j + p * h ≤ H), (1 / (p : ℂ)) * S_corr := by
      dsimp [main_coeff]
      push_cast
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun p hp => ?_
      have hp_le := (hp_in_P p hp).2.1
      have hph_nat : p * h ≤ H := by
        have : ((p * h : ℕ) : ℝ) ≤ (H : ℝ) := by push_cast; nlinarith
        exact_mod_cast this
      have hcard : ((Finset.Icc 1 H).filter (fun j => j + p * h ≤ H)).card = H - p * h := by
        have : (Finset.Icc 1 H).filter (fun j => j + p * h ≤ H) = Finset.Icc 1 (H - p * h) := by
          ext j; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
        rw [this, Nat.card_Icc]; omega
      rw [Finset.sum_const, hcard, nsmul_eq_mul]; ring
    rw [h1]
    simp_rw [Finset.sum_sub_distrib, mul_sub]
    rw [← h2]; ring
  have herr_norm : ‖(1 / (L : ℂ)) * ∑ p ∈ P_H, ∑ j ∈ (Finset.Icc 1 H).filter (fun j => j + p * h ≤ H),
      ((∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
          if p ∣ n + j then (g ((n + j) / p) * star (g ((n + j) / p + h))) / (n : ℂ) else 0) -
        (1 / (p : ℂ)) * S_corr)‖ ≤ (ε / 64) * (H : ℝ) / Real.log (H : ℝ) := by
    rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hL_pos.le]
    calc (1 / L) * ‖∑ p ∈ P_H, ∑ j ∈ _, _‖
        ≤ (1 / L) * ∑ p ∈ P_H, ∑ j ∈ (Finset.Icc 1 H).filter (fun j => j + p * h ≤ H),
            ‖(∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
                if p ∣ n + j then (g ((n + j) / p) * star (g ((n + j) / p + h))) / (n : ℂ) else 0) -
              (1 / (p : ℂ)) * S_corr‖ := by
          gcongr
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => norm_sum_le _ _)
      _ ≤ (1 / L) * ∑ p ∈ P_H, ∑ _j ∈ (Finset.Icc 1 H).filter (fun j => j + p * h ≤ H),
            ((4 * Real.log (H₁ : ℝ) + 8) / (p : ℝ)) := by
          gcongr with p hp j hj
          have hp2 := (hp_in_P p hp).1
          have hpH := (hp_in_P p hp).2.2
          have hjH : j ≤ H := (Finset.mem_Icc.mp (Finset.mem_filter.mp hj).1).2
          have hpj_sq : 2 * p * (j + 1) ≤ Nat.sqrt X := by
            calc 2 * p * (j + 1) ≤ 2 * H₁ * (H₁ + 1) := by
                  have hle1 : 2 * p ≤ 2 * H₁ := Nat.mul_le_mul_left 2 (le_trans hpH hH_le_H₁)
                  exact Nat.mul_le_mul hle1 (by omega)
              _ ≤ Nat.sqrt X := hH₁_sq
          have haff := log_affine_invariance hX16 hp2 hpj_sq (fun m => g m * star (g (m + h)))
            (fun m => by rw [norm_mul, norm_star]; exact mul_le_one₀ (hg_le1 _) (norm_nonneg _) (hg_le1 _))
          refine haff.trans ?_
          gcongr
          exact_mod_cast le_trans hpH hH_le_H₁
      _ ≤ (1 / L) * ((H : ℝ) * (4 * Real.log (H₁ : ℝ) + 8) * (∑ p ∈ P_H, (1 : ℝ) / (p : ℝ))) := by
          gcongr
          calc ∑ p ∈ P_H, ∑ _j ∈ (Finset.Icc 1 H).filter (fun j => j + p * h ≤ H),
                  ((4 * Real.log (H₁ : ℝ) + 8) / (p : ℝ))
              ≤ ∑ p ∈ P_H, (H : ℝ) * ((4 * Real.log (H₁ : ℝ) + 8) / (p : ℝ)) := by
                refine Finset.sum_le_sum fun p _ => ?_
                rw [Finset.sum_const, nsmul_eq_mul]
                have hcard : ((Finset.Icc 1 H).filter (fun j => j + p * h ≤ H)).card ≤ H := by
                  have := Finset.card_filter_le (Finset.Icc 1 H) (fun j => j + p * h ≤ H)
                  simpa [Nat.card_Icc] using this
                have hnn : 0 ≤ (4 * Real.log (H₁ : ℝ) + 8) / (p : ℝ) := by
                  apply div_nonneg _ (Nat.cast_nonneg _)
                  have : 0 ≤ Real.log (H₁ : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ H₁ by omega))
                  linarith
                exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hnn
            _ = (H : ℝ) * (4 * Real.log (H₁ : ℝ) + 8) * (∑ p ∈ P_H, (1 : ℝ) / (p : ℝ)) := by
                rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun p _ => by ring
      _ ≤ (4 / Real.log (X : ℝ)) * ((H : ℝ) * (4 * Real.log (H₁ : ℝ) + 8) * (2 / Real.log (H : ℝ))) := by
          have hL_inv : 1 / L ≤ 4 / Real.log (X : ℝ) := by
            have := one_div_le_one_div_of_le (by positivity) hL_bounds.1
            have hEq : 1 / ((1 / 4) * Real.log (X : ℝ)) = 4 / Real.log (X : ℝ) := by
              field_simp [hlogX_pos.ne']
            linarith
          have hnn_logH1 : 0 ≤ 4 * Real.log (H₁ : ℝ) + 8 := by
            have : 0 ≤ Real.log (H₁ : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ H₁ by omega))
            linarith
          exact mul_le_mul hL_inv (mul_le_mul_of_nonneg_left hP_ub (by positivity)) (by positivity) (by positivity)
      _ = (8 * (4 * Real.log (H₁ : ℝ) + 8) / Real.log (X : ℝ)) * ((H : ℝ) / Real.log (H : ℝ)) := by ring
      _ ≤ (ε / 64) * ((H : ℝ) / Real.log (H : ℝ)) := by gcongr
      _ = (ε / 64) * (H : ℝ) / Real.log (H : ℝ) := by ring
  have hmain_lb : (3 * ε / 16) * (H : ℝ) / Real.log (H : ℝ) ≤ ‖(main_coeff : ℂ) * (S_corr / (L : ℂ))‖ := by
    have hmc_nn : 0 ≤ main_coeff := Finset.sum_nonneg fun _ _ => by positivity
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hmc_nn]
    calc (3 * ε / 16) * (H : ℝ) / Real.log (H : ℝ)
        = ((3 / 16) * (H : ℝ) / Real.log (H : ℝ)) * ε := by ring
      _ ≤ main_coeff * ‖S_corr / (L : ℂ)‖ := mul_le_mul hcoeff_lb hS_corr_divL hε.le hmc_nn
  have htri := norm_sub_norm_le ((main_coeff : ℂ) * (S_corr / (L : ℂ)))
    ((1 / (L : ℂ)) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℂ)) *
      ∑ p ∈ P_H, ∑ j ∈ Finset.Icc 1 H,
        if j + p * h ≤ H then
          (if p ∣ n + j then (1 : ℂ) else 0) * g (n + j) * star (g (n + j + p * h))
        else 0)
  rw [norm_sub_rev, hswap] at htri
  have h11 : (11 * ε / 64) * (H : ℝ) / Real.log (H : ℝ) =
      (3 * ε / 16) * (H : ℝ) / Real.log (H : ℝ) - (ε / 64) * (H : ℝ) / Real.log (H : ℝ) := by ring
  linarith [hmain_lb, herr_norm, htri, h11]

private lemma markov_major_spectrum_card {H h : ℕ} [NeZero H] (hh_pos : 1 ≤ h)
    {C γ : ℝ} (hlogH_pos : 0 < Real.log (H : ℝ)) (hγ_pos : 0 < γ)
    (S_H : ℕ → ℂ) (hL4 : ∑ k ∈ Finset.range H, ‖S_H k‖ ^ 4 ≤ C / Real.log (H : ℝ) ^ 4) :
    ((Finset.univ.filter fun ξ : ZMod H => γ / Real.log (H : ℝ) ≤ ‖S_H (((h : ZMod H) * ξ).val)‖).card : ℝ) ≤
      (h : ℝ) * C / γ ^ 4 := by
  have hH_pos : 1 ≤ H := Nat.pos_of_ne_zero (NeZero.ne H)
  let Ξ_H : Finset (ZMod H) := Finset.univ.filter fun ξ : ZMod H =>
    γ / Real.log (H : ℝ) ≤ ‖S_H (((h : ZMod H) * ξ).val)‖
  have hfiber : ∀ k : ZMod H, (Finset.univ.filter fun ξ : ZMod H => (h : ZMod H) * ξ = k).card ≤ h := by
    intro k
    by_cases hne : (Finset.univ.filter fun ξ : ZMod H => (h : ZMod H) * ξ = k).Nonempty
    · obtain ⟨ξ₀, hξ₀⟩ := hne
      have hξ₀_eq : (h : ZMod H) * ξ₀ = k := (Finset.mem_filter.mp hξ₀).2
      let φ : ZMod H → ℕ := fun ξ => (h * (ξ - ξ₀).val) / H
      have hinj : Set.InjOn φ ((Finset.univ.filter fun ξ : ZMod H => (h : ZMod H) * ξ = k) : Set (ZMod H)) := by
        intro ξ₁ h₁ ξ₂ h₂ hEq
        have he₁ : (h : ZMod H) * (ξ₁ - ξ₀) = 0 := by
          rw [mul_sub, (Finset.mem_filter.mp h₁).2, hξ₀_eq, sub_self]
        have he₂ : (h : ZMod H) * (ξ₂ - ξ₀) = 0 := by
          rw [mul_sub, (Finset.mem_filter.mp h₂).2, hξ₀_eq, sub_self]
        have hd₁ : H ∣ h * (ξ₁ - ξ₀).val := by
          rw [← ZMod.natCast_eq_zero_iff]; simpa using he₁
        have hd₂ : H ∣ h * (ξ₂ - ξ₀).val := by
          rw [← ZMod.natCast_eq_zero_iff]; simpa using he₂
        have hm₁ : H * φ ξ₁ = h * (ξ₁ - ξ₀).val := Nat.mul_div_cancel' hd₁
        have hm₂ : H * φ ξ₂ = h * (ξ₂ - ξ₀).val := Nat.mul_div_cancel' hd₂
        rw [hEq] at hm₁
        have hval : (ξ₁ - ξ₀).val = (ξ₂ - ξ₀).val := Nat.eq_of_mul_eq_mul_left hh_pos (hm₁.symm.trans hm₂)
        exact sub_left_inj.mp (ZMod.val_injective H hval)
      have himg : (Finset.univ.filter fun ξ : ZMod H => (h : ZMod H) * ξ = k).image φ ⊆ Finset.range h := by
        intro t ht
        obtain ⟨ξ, _, rfl⟩ := Finset.mem_image.mp ht
        rw [Finset.mem_range]
        exact (Nat.div_lt_iff_lt_mul hH_pos).mpr (Nat.mul_lt_mul_of_pos_left (ξ - ξ₀).val_lt hh_pos)
      calc _ = ((Finset.univ.filter fun ξ : ZMod H => (h : ZMod H) * ξ = k).image φ).card :=
            (Finset.card_image_of_injOn hinj).symm
        _ ≤ (Finset.range h).card := Finset.card_le_card himg
        _ = h := Finset.card_range h
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.card_empty]; omega
  have h4sum : ∑ ξ : ZMod H, ‖S_H (((h : ZMod H) * ξ).val)‖ ^ 4 ≤ (h : ℝ) * (C / Real.log (H : ℝ) ^ 4) := by
    have hgroup : ∑ ξ : ZMod H, ‖S_H (((h : ZMod H) * ξ).val)‖ ^ 4 =
        ∑ k : ZMod H, ((Finset.univ.filter fun ξ : ZMod H => (h : ZMod H) * ξ = k).card : ℝ) *
          ‖S_H k.val‖ ^ 4 := by
      rw [← Finset.sum_fiberwise_of_maps_to (g := fun ξ : ZMod H => (h : ZMod H) * ξ)
        (fun _ _ => Finset.mem_univ _)]
      refine Finset.sum_congr rfl fun k _ => ?_
      trans ∑ _ξ ∈ Finset.univ.filter (fun ξ : ZMod H => (h : ZMod H) * ξ = k), ‖S_H k.val‖ ^ 4
      · exact Finset.sum_congr rfl fun ξ hξ => by rw [(Finset.mem_filter.mp hξ).2]
      · simp
    rw [hgroup]
    calc ∑ k : ZMod H, ((Finset.univ.filter fun ξ : ZMod H => (h : ZMod H) * ξ = k).card : ℝ) * ‖S_H k.val‖ ^ 4
        ≤ ∑ k : ZMod H, (h : ℝ) * ‖S_H k.val‖ ^ 4 := by
          refine Finset.sum_le_sum fun k _ =>
            mul_le_mul_of_nonneg_right (by exact_mod_cast hfiber k) (by positivity)
      _ = (h : ℝ) * ∑ k : ZMod H, ‖S_H k.val‖ ^ 4 := (Finset.mul_sum _ _ _).symm
      _ = (h : ℝ) * ∑ k ∈ Finset.range H, ‖S_H k‖ ^ 4 := by
          congr 1
          refine Finset.sum_bij (fun k _ => k.val) ?_ ?_ ?_ ?_
          · intro k _; exact Finset.mem_range.mpr k.val_lt
          · intro k₁ _ k₂ _ h; exact ZMod.val_injective H h
          · intro k hk; exact ⟨(k : ZMod H), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)⟩
          · intro _ _; rfl
      _ ≤ (h : ℝ) * (C / Real.log (H : ℝ) ^ 4) := by gcongr
  have hmarkov : (Ξ_H.card : ℝ) * (γ / Real.log (H : ℝ)) ^ 4 ≤ (h : ℝ) * (C / Real.log (H : ℝ) ^ 4) := by
    calc (Ξ_H.card : ℝ) * (γ / Real.log (H : ℝ)) ^ 4
        = ∑ _ξ ∈ Ξ_H, (γ / Real.log (H : ℝ)) ^ 4 := by simp
      _ ≤ ∑ ξ ∈ Ξ_H, ‖S_H (((h : ZMod H) * ξ).val)‖ ^ 4 :=
          Finset.sum_le_sum fun ξ hξ => pow_le_pow_left₀ (by positivity) (Finset.mem_filter.mp hξ).2 4
      _ ≤ ∑ ξ : ZMod H, ‖S_H (((h : ZMod H) * ξ).val)‖ ^ 4 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity
      _ ≤ (h : ℝ) * (C / Real.log (H : ℝ) ^ 4) := h4sum
  rw [div_pow] at hmarkov
  have hpos4 : 0 < γ ^ 4 / Real.log (H : ℝ) ^ 4 := by positivity
  have h1 := (le_div_iff₀ hpos4).mpr hmarkov
  have h2 : (h : ℝ) * (C / Real.log (H : ℝ) ^ 4) / (γ ^ 4 / Real.log (H : ℝ) ^ 4) = (h : ℝ) * C / γ ^ 4 := by
    field_simp [hlogH_pos.ne', hγ_pos.ne']
  linarith

private lemma circle_method_pointwise {H h : ℕ} [NeZero H] {ε δ : ℝ}
    (hlogH_pos : 0 < Real.log (H : ℝ)) (hε : 0 < ε)
    (hδ_h_le14 : δ * (h : ℝ) ≤ 1 / 4) (hδ_h_le_eps : δ * (h : ℝ) ≤ ε / 128)
    (P_H : Finset ℕ) (hp_in_P : ∀ p ∈ P_H, 2 ≤ p ∧ (p : ℝ) ≤ δ * (H : ℝ) ∧ p ≤ H)
    (hP_ub : ∑ p ∈ P_H, (1 : ℝ) / (p : ℝ) ≤ 2 / Real.log (H : ℝ))
    (g : ℕ → ℂ) (hg_le1 : ∀ n, ‖g n‖ ≤ 1) (n : ℕ) :
    let S_H : ℕ → ℂ := fun k =>
      ∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) *
        Complex.exp (-2 * Real.pi * Complex.I * ((k : ℂ) * (p : ℂ) / (H : ℂ)))
    let Ξ_H : Finset (ZMod H) := Finset.univ.filter fun ξ : ZMod H =>
      (ε / 64) / Real.log (H : ℝ) ≤ ‖S_H (((h : ZMod H) * ξ).val)‖
    ‖∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j ∈ Finset.Icc 1 H,
      if j + p * h ≤ H then g (n + j) * star (g (n + j + p * h)) else 0‖ ≤
    (ε / 32) * (H : ℝ) / Real.log (H : ℝ) +
    (2 / Real.log (H : ℝ)) * ∑ ξ ∈ Ξ_H,
      ‖∑ j ∈ Finset.Icc 1 H, g (n + j) *
        Complex.exp (2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) * (j : ℂ))‖ := by
  intro S_H Ξ_H
  have hH_pos : 1 ≤ H := Nat.pos_of_ne_zero (NeZero.ne H)
  have hH_r_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH_pos
  let x₁ : ZMod H → ℂ := fun j => g (n + j.val + 1)
  let x₂ : ZMod H → ℂ := fun j => star (g (n + j.val + 1))
  have hwrap : ‖(∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then g (n + j) * star (g (n + j + p * h)) else 0) -
        (∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j : ZMod H, x₁ j * x₂ (j + ((p * h : ℕ) : ZMod H)))‖ ≤
      (ε / 64) * (H : ℝ) / Real.log (H : ℝ) := by
    rw [← Finset.sum_sub_distrib]
    calc ‖∑ p ∈ P_H, _‖
        ≤ ∑ p ∈ P_H, ‖((1 : ℂ) / (p : ℂ)) * ((∑ j ∈ Finset.Icc 1 H,
            if j + p * h ≤ H then g (n + j) * star (g (n + j + p * h)) else 0) -
            ∑ j : ZMod H, x₁ j * x₂ (j + ((p * h : ℕ) : ZMod H)))‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => by rw [← mul_sub])
      _ ≤ ∑ p ∈ P_H, (1 / (p : ℝ)) * ((p * h : ℕ) : ℝ) := by
          refine Finset.sum_le_sum fun p hp => ?_
          have hp_le := (hp_in_P p hp).2.1
          have hph_le_H : p * h ≤ H := by
            have : ((p * h : ℕ) : ℝ) ≤ (H : ℝ) := by push_cast; nlinarith
            exact_mod_cast this
          rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
          gcongr
          have hbij : ∑ j : ZMod H, x₁ j * x₂ (j + ((p * h : ℕ) : ZMod H)) =
              ∑ k ∈ Finset.Icc 1 H, x₁ ((k - 1 : ℕ) : ZMod H) * x₂ (((k - 1 + p * h : ℕ) : ZMod H)) := by
            refine Finset.sum_bij (fun j _ => j.val + 1) ?_ ?_ ?_ ?_
            · intro j _; rw [Finset.mem_Icc]; exact ⟨by omega, j.val_lt⟩
            · intro j₁ _ j₂ _ h; exact ZMod.val_injective H (by omega)
            · intro k hk; rw [Finset.mem_Icc] at hk
              exact ⟨((k - 1 : ℕ) : ZMod H), Finset.mem_univ _, by
                rw [ZMod.val_natCast_of_lt (by omega)]; omega⟩
            · intro j _
              have h1 : ((j.val + 1 - 1 : ℕ) : ZMod H) = j := by simp
              have h2 : ((j.val + 1 - 1 + p * h : ℕ) : ZMod H) = j + ((p * h : ℕ) : ZMod H) := by simp
              rw [h1, h2]
          rw [hbij, ← Finset.sum_sub_distrib]
          calc ‖∑ k ∈ Finset.Icc 1 H, _‖
              ≤ ∑ k ∈ Finset.Icc 1 H,
                  ‖(if k + p * h ≤ H then g (n + k) * star (g (n + k + p * h)) else 0) -
                    x₁ ((k - 1 : ℕ) : ZMod H) * x₂ (((k - 1 + p * h : ℕ) : ZMod H))‖ := norm_sum_le _ _
            _ ≤ ∑ k ∈ (Finset.Icc 1 H).filter (fun k => ¬ (k + p * h ≤ H)), (1 : ℝ) := by
                rw [Finset.sum_filter]
                refine Finset.sum_le_sum fun k hk => ?_
                have hkI := Finset.mem_Icc.mp hk
                by_cases hle : k + p * h ≤ H
                · rw [if_pos hle, if_neg (not_not.mpr hle)]
                  have hval1 : (((k - 1 : ℕ) : ZMod H).val) = k - 1 := ZMod.val_natCast_of_lt (by omega)
                  have hval2 : (((k - 1 + p * h : ℕ) : ZMod H).val) = k - 1 + p * h :=
                    ZMod.val_natCast_of_lt (by omega)
                  dsimp [x₁, x₂]
                  rw [hval1, hval2]
                  have he1 : n + (k - 1) + 1 = n + k := by omega
                  have he2 : n + (k - 1 + p * h) + 1 = n + k + p * h := by omega
                  rw [he1, he2, sub_self, norm_zero]
                · rw [if_neg hle, if_pos hle, zero_sub, norm_neg, norm_mul]
                  dsimp [x₁, x₂]
                  rw [Complex.norm_conj]; exact mul_le_one₀ (hg_le1 _) (norm_nonneg _) (hg_le1 _)
            _ = ((p * h : ℕ) : ℝ) := by
                have hflt : (Finset.Icc 1 H).filter (fun k => ¬ (k + p * h ≤ H)) =
                    Finset.Icc (H - p * h + 1) H := by
                  ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega
                rw [hflt, Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, mul_one]
                exact_mod_cast (show H + 1 - (H - p * h + 1) = p * h by omega)
      _ ≤ (δ * (h : ℝ)) * (H : ℝ) * (∑ p ∈ P_H, (1 : ℝ) / (p : ℝ)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum fun p hp => ?_
          have hp_le := (hp_in_P p hp).2.1
          have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by have := (hp_in_P p hp).1; omega)
          push_cast
          calc 1 / (p : ℝ) * ((p : ℝ) * (h : ℝ)) = (h : ℝ) := by field_simp [hp_pos.ne']
            _ ≤ (δ * (H : ℝ) / (p : ℝ)) * (h : ℝ) := by
                have : 1 ≤ δ * (H : ℝ) / (p : ℝ) := (one_le_div hp_pos).mpr hp_le
                nlinarith
            _ = δ * (h : ℝ) * (H : ℝ) * (1 / (p : ℝ)) := by ring
      _ ≤ (ε / 128) * (H : ℝ) * (2 / Real.log (H : ℝ)) := by gcongr
      _ = (ε / 64) * (H : ℝ) / Real.log (H : ℝ) := by ring
  let G₁ : ZMod H → ℂ := fun ξ => (1 / (H : ℂ)) * ∑ j : ZMod H,
    x₁ j * Complex.exp (-2 * Real.pi * Complex.I * (((j.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))
  let G₂ : ZMod H → ℂ := fun ξ => (1 / (H : ℂ)) * ∑ j : ZMod H,
    x₂ j * Complex.exp (2 * Real.pi * Complex.I * (((j.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))
  have hfour : ∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j : ZMod H, x₁ j * x₂ (j + ((p * h : ℕ) : ZMod H)) =
      (H : ℂ) * ∑ ξ : ZMod H, G₁ ξ * G₂ ξ * S_H (((h : ZMod H) * ξ).val) := by
    have h1 : ∀ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j : ZMod H, x₁ j * x₂ (j + ((p * h : ℕ) : ZMod H)) =
        (H : ℂ) * ∑ ξ : ZMod H, G₁ ξ * G₂ ξ *
          (((1 : ℂ) / (p : ℂ)) *
            Complex.exp (-2 * Real.pi * Complex.I * ((((h : ZMod H) * ξ).val : ℕ) : ℂ) * (p : ℂ) / (H : ℂ))) := by
      intro p _
      rw [zmod_convolution_fourier x₁ x₂ (p * h)]
      rw [← mul_assoc, mul_comm ((1 : ℂ) / (p : ℂ)) (H : ℂ), mul_assoc, Finset.mul_sum]
      congr 1; refine Finset.sum_congr rfl fun ξ _ => ?_
      have hph_mod : Complex.exp (-2 * Real.pi * Complex.I * (((p * h : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) =
          Complex.exp (-2 * Real.pi * Complex.I * ((((h : ZMod H) * ξ).val : ℕ) : ℂ) * (p : ℂ) / (H : ℂ)) := by
        have hmod := zmod_exp_mod (H := H) ((h : ℤ) * (ξ.val : ℤ)) (-(p : ℤ))
        have hcast : (((h : ℤ) * (ξ.val : ℤ) : ℤ) : ZMod H) = (h : ZMod H) * ξ := by simp
        rw [hcast] at hmod
        convert hmod.symm using 2 <;> (push_cast; ring)
      dsimp [G₁, G₂]
      rw [hph_mod]; ring
    rw [Finset.sum_congr rfl h1, ← Finset.mul_sum, Finset.sum_comm]
    congr 1; refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [← Finset.mul_sum]
    congr 1; dsimp [S_H]
    refine Finset.sum_congr rfl fun p _ => by congr 2; ring
  have hCS_Planch : ∑ ξ : ZMod H, ‖G₁ ξ‖ * ‖G₂ ξ‖ ≤ 1 := by
    have hG₁_sq : ∑ ξ : ZMod H, ‖G₁ ξ‖ ^ 2 ≤ 1 := by
      rw [zmod_plancherel x₁]
      calc (1 / (H : ℝ)) * ∑ j : ZMod H, ‖x₁ j‖ ^ 2
          ≤ (1 / (H : ℝ)) * ∑ _j : ZMod H, (1 : ℝ) := by
            gcongr with j _
            have : ‖x₁ j‖ ≤ 1 := hg_le1 _
            nlinarith [norm_nonneg (x₁ j)]
        _ = 1 := by simp [ZMod.card]
    have hG₂_sq : ∑ ξ : ZMod H, ‖G₂ ξ‖ ^ 2 ≤ 1 := by
      have hG₂_eq : ∀ ξ : ZMod H, ‖G₂ ξ‖ =
          ‖(1 / (H : ℂ)) * ∑ j : ZMod H,
            star (x₂ j) * Complex.exp (-2 * Real.pi * Complex.I * (((j.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))‖ := by
        intro ξ
        rw [← norm_star]
        congr 1
        dsimp [G₂]
        rw [map_mul, map_div₀, map_one, Complex.conj_natCast, map_sum]
        congr 1; refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, ← Complex.exp_conj]
        congr 2
        simp only [map_mul, map_div₀, map_ofNat, Complex.conj_ofReal, Complex.conj_I,
          Complex.conj_natCast]
        ring
      simp_rw [hG₂_eq]
      rw [zmod_plancherel (fun j => star (x₂ j))]
      calc (1 / (H : ℝ)) * ∑ j : ZMod H, ‖star (x₂ j)‖ ^ 2
          ≤ (1 / (H : ℝ)) * ∑ _j : ZMod H, (1 : ℝ) := by
            gcongr with j _
            have : ‖star (x₂ j)‖ ≤ 1 := by rw [norm_star]; dsimp [x₂]; rw [Complex.norm_conj]; exact hg_le1 _
            nlinarith [norm_nonneg (star (x₂ j))]
        _ = 1 := by simp [ZMod.card]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun ξ => ‖G₁ ξ‖) (fun ξ => ‖G₂ ξ‖)
    have hsq_le : (∑ ξ : ZMod H, ‖G₁ ξ‖ * ‖G₂ ξ‖) ^ 2 ≤ 1 := by
      calc (∑ ξ : ZMod H, ‖G₁ ξ‖ * ‖G₂ ξ‖) ^ 2
          ≤ (∑ ξ : ZMod H, ‖G₁ ξ‖ ^ 2) * (∑ ξ : ZMod H, ‖G₂ ξ‖ ^ 2) := hcs
        _ ≤ 1 * 1 := mul_le_mul hG₁_sq hG₂_sq (Finset.sum_nonneg fun _ _ => sq_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    nlinarith [Finset.sum_nonneg fun ξ (_ : ξ ∈ Finset.univ) => mul_nonneg (norm_nonneg (G₁ ξ)) (norm_nonneg (G₂ ξ))]
  have hfour_bd : ‖(H : ℂ) * ∑ ξ : ZMod H, G₁ ξ * G₂ ξ * S_H (((h : ZMod H) * ξ).val)‖ ≤
      (ε / 64) * (H : ℝ) / Real.log (H : ℝ) +
      (2 / Real.log (H : ℝ)) * ∑ ξ ∈ Ξ_H,
        ‖∑ j ∈ Finset.Icc 1 H, g (n + j) *
          Complex.exp (2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) * (j : ℂ))‖ := by
    have hunion : (Finset.univ : Finset (ZMod H)) = Ξ_H ∪ (Finset.univ \ Ξ_H) :=
      (Finset.union_sdiff_of_subset (Finset.subset_univ _)).symm
    rw [norm_mul, Complex.norm_natCast, hunion, Finset.sum_union Finset.disjoint_sdiff]
    have hminor : (H : ℝ) * ‖∑ ξ ∈ Finset.univ \ Ξ_H, G₁ ξ * G₂ ξ * S_H (((h : ZMod H) * ξ).val)‖ ≤
        (ε / 64) * (H : ℝ) / Real.log (H : ℝ) := by
      calc (H : ℝ) * ‖∑ ξ ∈ Finset.univ \ Ξ_H, _‖
          ≤ (H : ℝ) * ∑ ξ ∈ Finset.univ \ Ξ_H, ‖G₁ ξ‖ * ‖G₂ ξ‖ * ‖S_H (((h : ZMod H) * ξ).val)‖ := by
            gcongr
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ _ => by rw [norm_mul, norm_mul])
        _ ≤ (H : ℝ) * ∑ ξ ∈ Finset.univ \ Ξ_H, ‖G₁ ξ‖ * ‖G₂ ξ‖ * ((ε / 64) / Real.log (H : ℝ)) := by
            gcongr with ξ hξ
            have hnot : ¬ ((ε / 64) / Real.log (H : ℝ) ≤ ‖S_H (((h : ZMod H) * ξ).val)‖) := by
              have := (Finset.mem_sdiff.mp hξ).2
              simpa [Ξ_H] using this
            exact le_of_lt (not_le.mp hnot)
        _ = ((ε / 64) * (H : ℝ) / Real.log (H : ℝ)) * ∑ ξ ∈ Finset.univ \ Ξ_H, ‖G₁ ξ‖ * ‖G₂ ξ‖ := by
            rw [← Finset.sum_mul]; ring
        _ ≤ ((ε / 64) * (H : ℝ) / Real.log (H : ℝ)) * 1 := by
            gcongr
            exact (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => by positivity).trans hCS_Planch
        _ = (ε / 64) * (H : ℝ) / Real.log (H : ℝ) := mul_one _
    have hmajor : (H : ℝ) * ‖∑ ξ ∈ Ξ_H, G₁ ξ * G₂ ξ * S_H (((h : ZMod H) * ξ).val)‖ ≤
        (2 / Real.log (H : ℝ)) * ∑ ξ ∈ Ξ_H,
          ‖∑ j ∈ Finset.Icc 1 H, g (n + j) *
            Complex.exp (2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) * (j : ℂ))‖ := by
      have hG₂_le1 : ∀ ξ, ‖G₂ ξ‖ ≤ 1 := fun ξ => by
        dsimp [G₂]
        rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
        calc (1 / (H : ℝ)) * ‖∑ j : ZMod H, _‖
            ≤ (1 / (H : ℝ)) * ∑ j : ZMod H, ‖x₂ j * Complex.exp _‖ := by gcongr; exact norm_sum_le _ _
          _ ≤ (1 / (H : ℝ)) * ∑ _j : ZMod H, (1 : ℝ) := by
              gcongr with j _
              rw [norm_mul]
              have he1 : ‖Complex.exp (2 * Real.pi * Complex.I * (((j.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))‖ = 1 := by
                have : (2 * (Real.pi : ℂ) * Complex.I * (((j.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ))) =
                    2 * Real.pi * Complex.I * (((((j.val : ℕ) : ℝ) * ((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) := by
                  push_cast; ring
                rw [this]; exact norm_e_real _
              rw [he1, mul_one]; dsimp [x₂]; rw [Complex.norm_conj]; exact hg_le1 _
          _ = 1 := by simp [ZMod.card]
      have hSH_ub : ∀ k, ‖S_H k‖ ≤ 2 / Real.log (H : ℝ) := fun k => by
        dsimp [S_H]
        calc ‖∑ p ∈ P_H, _‖
            ≤ ∑ p ∈ P_H, ‖((1 : ℂ) / (p : ℂ)) * Complex.exp _‖ := norm_sum_le _ _
          _ = ∑ p ∈ P_H, (1 : ℝ) / (p : ℝ) := by
              refine Finset.sum_congr rfl fun p _ => ?_
              rw [norm_mul, norm_div, norm_one, Complex.norm_natCast]
              have he1 : ‖Complex.exp (-2 * Real.pi * Complex.I * ((k : ℂ) * (p : ℂ) / (H : ℂ)))‖ = 1 := by
                have : (-2 * (Real.pi : ℂ) * Complex.I * ((k : ℂ) * (p : ℂ) / (H : ℂ))) =
                    2 * Real.pi * Complex.I * (((-((k : ℝ) * (p : ℝ) / (H : ℝ)) : ℝ) : ℂ)) := by
                  push_cast; ring
                rw [this]; exact norm_e_real _
              rw [he1, mul_one]
          _ ≤ 2 / Real.log (H : ℝ) := hP_ub
      have hG₁_Icc : ∀ ξ : ZMod H, (H : ℝ) * ‖G₁ ξ‖ =
          ‖∑ j ∈ Finset.Icc 1 H, g (n + j) *
            Complex.exp (2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) * (j : ℂ))‖ := by
        intro ξ
        dsimp [G₁]
        rw [norm_mul, norm_div, norm_one, Complex.norm_natCast, ← mul_assoc,
          mul_one_div_cancel hH_r_pos.ne', one_mul]
        have hphase : ‖Complex.exp (-2 * Real.pi * Complex.I * (((ξ.val : ℕ) : ℂ) / (H : ℂ)))‖ = 1 := by
          have : (-2 * (Real.pi : ℂ) * Complex.I * (((ξ.val : ℕ) : ℂ) / (H : ℂ))) =
              2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) := by
            push_cast; ring
          rw [this]; exact norm_e_real _
        rw [← one_mul (‖∑ j : ZMod H, _‖), ← hphase, ← norm_mul, Finset.mul_sum]
        congr 1
        refine Finset.sum_bij (fun j _ => j.val + 1) ?_ ?_ ?_ ?_
        · intro j _; rw [Finset.mem_Icc]; exact ⟨by omega, j.val_lt⟩
        · intro j₁ _ j₂ _ h; exact ZMod.val_injective H (by omega)
        · intro k hk; rw [Finset.mem_Icc] at hk
          exact ⟨((k - 1 : ℕ) : ZMod H), Finset.mem_univ _, by
            rw [ZMod.val_natCast_of_lt (by omega)]; omega⟩
        · intro j _
          dsimp [x₁]
          have : Complex.exp (-2 * Real.pi * Complex.I * (((ξ.val : ℕ) : ℂ) / (H : ℂ))) *
              (g (n + j.val + 1) *
                Complex.exp (-2 * Real.pi * Complex.I * (((j.val : ℕ) : ℂ) * ((ξ.val : ℕ) : ℂ) / (H : ℂ)))) =
              g (n + (j.val + 1)) *
                Complex.exp (2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) * ((j.val + 1 : ℕ) : ℂ)) := by
            rw [mul_left_comm, ← Complex.exp_add, Nat.add_assoc]
            congr 2; push_cast; ring
          exact this
      calc (H : ℝ) * ‖∑ ξ ∈ Ξ_H, _‖
          ≤ (H : ℝ) * ∑ ξ ∈ Ξ_H, ‖G₁ ξ‖ * ‖G₂ ξ‖ * ‖S_H (((h : ZMod H) * ξ).val)‖ := by
            gcongr
            exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun ξ _ => by rw [norm_mul, norm_mul])
        _ ≤ (H : ℝ) * ∑ ξ ∈ Ξ_H, ‖G₁ ξ‖ * 1 * (2 / Real.log (H : ℝ)) := by
            gcongr with ξ _
            · exact hG₂_le1 ξ
            · exact hSH_ub _
        _ = (2 / Real.log (H : ℝ)) * ∑ ξ ∈ Ξ_H, ((H : ℝ) * ‖G₁ ξ‖) := by
            rw [Finset.mul_sum, Finset.mul_sum]
            exact Finset.sum_congr rfl fun ξ _ => by ring
        _ = _ := by congr 1; exact Finset.sum_congr rfl fun ξ _ => hG₁_Icc ξ
    calc (H : ℝ) * ‖(∑ ξ ∈ Ξ_H, _) + (∑ ξ ∈ Finset.univ \ Ξ_H, _)‖
        ≤ (H : ℝ) * (‖∑ ξ ∈ Ξ_H, _‖ + ‖∑ ξ ∈ Finset.univ \ Ξ_H, _‖) := by
          gcongr; exact norm_add_le _ _
      _ = (H : ℝ) * ‖∑ ξ ∈ Ξ_H, _‖ + (H : ℝ) * ‖∑ ξ ∈ Finset.univ \ Ξ_H, _‖ := mul_add _ _ _
      _ ≤ _ := by linarith [hminor, hmajor]
  have htri := norm_add_le
    ((∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j ∈ Finset.Icc 1 H,
        if j + p * h ≤ H then g (n + j) * star (g (n + j + p * h)) else 0) -
      (∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j : ZMod H, x₁ j * x₂ (j + ((p * h : ℕ) : ZMod H))))
    (∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j : ZMod H, x₁ j * x₂ (j + ((p * h : ℕ) : ZMod H)))
  rw [sub_add_cancel, hfour] at htri
  rw [hfour] at hwrap
  have h32 : (ε / 32) * (H : ℝ) / Real.log (H : ℝ) =
      (ε / 64) * (H : ℝ) / Real.log (H : ℝ) + (ε / 64) * (H : ℝ) / Real.log (H : ℝ) := by ring
  linarith [htri, hwrap, hfour_bd, h32]

private lemma exists_large_A {A₁ A₂ ε : ℝ} {s₀ H₁ : ℕ}
    (hA₁_ge1 : 1 ≤ A₁) (hε : 0 < ε) :
    ∃ A : ℝ,
      1 ≤ A ∧ A₁ ≤ A ∧ A₂ ≤ A ∧ (16 : ℝ) ≤ A ∧
      ∀ X : ℕ, A ≤ (X : ℝ) →
        4 ≤ Real.log (X : ℝ) ∧
        s₀ ≤ Nat.sqrt X ∧
        3 * (s₀ : ℝ) / (Nat.sqrt X : ℝ) ≤ (ε / 4) * Real.log (X : ℝ) ∧
        2 * H₁ * (H₁ + 1) ≤ Nat.sqrt X ∧
        8 * (4 * Real.log (H₁ : ℝ) + 8) / Real.log (X : ℝ) ≤ ε / 64 := by
  have hlog_top : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : ∀ᶠ n : ℕ in atTop,
      max (max 4 (12 * (s₀ : ℝ) / ε)) (512 * (4 * Real.log (H₁ : ℝ) + 8) / ε) ≤ Real.log (n : ℝ) :=
    hlog_top.eventually (Filter.eventually_ge_atTop _)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp h1
  let N₂ : ℕ := max (max N₁ 16) ((max s₀ (2 * H₁ * (H₁ + 1))) ^ 2)
  let A : ℝ := max (max A₁ A₂) (N₂ : ℝ)
  refine ⟨A, le_trans hA₁_ge1 (le_trans (le_max_left _ _) (le_max_left _ _)),
    le_trans (le_max_left _ _) (le_max_left _ _),
    le_trans (le_max_right _ _) (le_max_left _ _),
    le_trans (by exact_mod_cast le_trans (le_max_right N₁ 16) (le_max_left _ _)) (le_max_right _ _),
    fun X hX => ?_⟩
  have hXN₂ : N₂ ≤ X := by exact_mod_cast (le_max_right _ _).trans hX
  have hXN₁ : N₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXN₂
  have hlog_bd := hN₁ X hXN₁
  have hlog4 : 4 ≤ Real.log (X : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hlog_bd
  have hsq_ge : max s₀ (2 * H₁ * (H₁ + 1)) ≤ Nat.sqrt X := by
    refine Nat.le_sqrt.mpr ?_
    rw [← sq]
    exact le_trans (le_max_right _ _) hXN₂
  refine ⟨hlog4, le_trans (le_max_left _ _) hsq_ge, ?_, le_trans (le_max_right _ _) hsq_ge, ?_⟩
  · have hs_log : 12 * (s₀ : ℝ) / ε ≤ Real.log (X : ℝ) :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hlog_bd
    have hsq1 : (1 : ℝ) ≤ (Nat.sqrt X : ℝ) := by
      exact_mod_cast Nat.le_sqrt.mpr (by
        have : 16 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXN₂; omega)
    calc 3 * (s₀ : ℝ) / (Nat.sqrt X : ℝ) ≤ 3 * (s₀ : ℝ) / 1 :=
          div_le_div_of_nonneg_left (by positivity) zero_lt_one hsq1
      _ = 3 * (s₀ : ℝ) := div_one _
      _ ≤ (ε / 4) * Real.log (X : ℝ) := by
          have := (div_le_iff₀ hε).mp hs_log; linarith
  · have hlog_big : 512 * (4 * Real.log (H₁ : ℝ) + 8) / ε ≤ Real.log (X : ℝ) :=
      le_trans (le_max_right _ _) hlog_bd
    have hlogX_pos : 0 < Real.log (X : ℝ) := by linarith
    rw [div_le_iff₀ hlogX_pos]
    have := (div_le_iff₀ hε).mp hlog_big
    linarith

private lemma mrt_average_upper_bound {X H h : ℕ} [NeZero H] {ε M_Ξ η₁ : ℝ}
    (hlog4 : 4 ≤ Real.log (X : ℝ)) (hlogH_pos : 0 < Real.log (H : ℝ))
    (hε : 0 < ε) (hM_Ξ_pos : 0 < M_Ξ) (hη₁_eq : η₁ = ε / (512 * (M_Ξ + 1)))
    (P_H : Finset ℕ) (Ξ_H : Finset (ZMod H)) (g : ℕ → ℂ)
    (hL_lo : (1 / 4) * Real.log (X : ℝ) ≤ ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 : ℝ) / (n : ℝ))
    (hΞ_card : (Ξ_H.card : ℝ) ≤ M_Ξ)
    (hCircle : ∀ n : ℕ,
      ‖∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j ∈ Finset.Icc 1 H,
        if j + p * h ≤ H then g (n + j) * star (g (n + j + p * h)) else 0‖ ≤
      (ε / 32) * (H : ℝ) / Real.log (H : ℝ) +
      (2 / Real.log (H : ℝ)) * ∑ ξ ∈ Ξ_H,
        ‖∑ j ∈ Finset.Icc 1 H, g (n + j) *
          Complex.exp (2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) * (j : ℂ))‖)
    (hMRT_ξ : ∀ ξ ∈ Ξ_H,
      ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / ((H : ℝ) * (n : ℝ))) *
        ‖∑ j ∈ Finset.Icc 1 H, g (n + j) *
          Complex.exp (2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) * (j : ℂ))‖ ≤
        η₁ * Real.log (X : ℝ)) :
    let L : ℝ := ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 : ℝ) / (n : ℝ)
    ‖(1 / (L : ℂ)) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℂ)) *
      ∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j ∈ Finset.Icc 1 H,
        if j + p * h ≤ H then g (n + j) * star (g (n + j + p * h)) else 0‖ ≤
    (3 * ε / 64) * (H : ℝ) / Real.log (H : ℝ) := by
  intro L
  have hH_pos : 1 ≤ H := Nat.pos_of_ne_zero (NeZero.ne H)
  have hH_r_pos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH_pos
  have hL_pos : 0 < L := by linarith
  have hη₁_pos : 0 < η₁ := by rw [hη₁_eq]; positivity
  have hMRT_bound : (1 / L) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) *
      ((2 / Real.log (H : ℝ)) * ∑ ξ ∈ Ξ_H,
        ‖∑ j ∈ Finset.Icc 1 H, g (n + j) *
          Complex.exp (2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) * (j : ℂ))‖) ≤
      (ε / 64) * (H : ℝ) / Real.log (H : ℝ) := by
    have hswap_ξ : (1 / L) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) *
          ((2 / Real.log (H : ℝ)) * ∑ ξ ∈ Ξ_H,
            ‖∑ j ∈ Finset.Icc 1 H, g (n + j) *
              Complex.exp (2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) * (j : ℂ))‖) =
        (2 * (H : ℝ) / (L * Real.log (H : ℝ))) * ∑ ξ ∈ Ξ_H,
          ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / ((H : ℝ) * (n : ℝ))) *
            ‖∑ j ∈ Finset.Icc 1 H, g (n + j) *
              Complex.exp (2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) * (j : ℂ))‖ := by
      simp_rw [← mul_assoc, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun ξ _ => ?_
      refine Finset.sum_congr rfl fun n _ => ?_
      field_simp [hL_pos.ne', hlogH_pos.ne', hH_r_pos.ne']
    rw [hswap_ξ]
    calc (2 * (H : ℝ) / (L * Real.log (H : ℝ))) * ∑ ξ ∈ Ξ_H, _
        ≤ (2 * (H : ℝ) / (L * Real.log (H : ℝ))) * ∑ _ξ ∈ Ξ_H, (η₁ * Real.log (X : ℝ)) := by
          gcongr with ξ hξ
          exact hMRT_ξ ξ hξ
      _ = (2 * (H : ℝ) / Real.log (H : ℝ)) * (Real.log (X : ℝ) / L) * ((Ξ_H.card : ℝ) * η₁) := by
          simp; ring
      _ ≤ (2 * (H : ℝ) / Real.log (H : ℝ)) * 4 * (M_Ξ * η₁) := by
          have hlog_divL : Real.log (X : ℝ) / L ≤ 4 := by
            rw [div_le_iff₀ hL_pos]; linarith
          gcongr
      _ ≤ (ε / 64) * (H : ℝ) / Real.log (H : ℝ) := by
          have hMη : 8 * (M_Ξ * η₁) ≤ ε / 64 := by
            rw [hη₁_eq]
            have h1 : M_Ξ / (M_Ξ + 1) ≤ 1 := (div_le_one (by positivity)).mpr (by linarith)
            calc 8 * (M_Ξ * (ε / (512 * (M_Ξ + 1)))) = (ε / 64) * (M_Ξ / (M_Ξ + 1)) := by
                  field_simp [(by positivity : M_Ξ + 1 ≠ 0)]; ring
              _ ≤ (ε / 64) * 1 := by gcongr
              _ = ε / 64 := mul_one _
          calc (2 * (H : ℝ) / Real.log (H : ℝ)) * 4 * (M_Ξ * η₁)
              = (8 * (M_Ξ * η₁)) * ((H : ℝ) / Real.log (H : ℝ)) := by ring
            _ ≤ (ε / 64) * ((H : ℝ) / Real.log (H : ℝ)) := by gcongr
            _ = (ε / 64) * (H : ℝ) / Real.log (H : ℝ) := by ring
  rw [norm_mul, norm_div, norm_one, Complex.norm_real, Real.norm_of_nonneg hL_pos.le]
  calc (1 / L) * ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, _‖
      ≤ (1 / L) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) *
          ‖∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j ∈ Finset.Icc 1 H,
            if j + p * h ≤ H then g (n + j) * star (g (n + j + p * h)) else 0‖ := by
        gcongr
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => by
          rw [norm_mul, norm_div, norm_one, Complex.norm_natCast])
    _ ≤ (1 / L) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) *
          ((ε / 32) * (H : ℝ) / Real.log (H : ℝ) +
            (2 / Real.log (H : ℝ)) * ∑ ξ ∈ Ξ_H,
              ‖∑ j ∈ Finset.Icc 1 H, g (n + j) *
                Complex.exp (2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) * (j : ℂ))‖) := by
        gcongr with n _; exact hCircle n
    _ = ((ε / 32) * (H : ℝ) / Real.log (H : ℝ)) +
        (1 / L) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℝ)) *
          ((2 / Real.log (H : ℝ)) * ∑ ξ ∈ Ξ_H,
            ‖∑ j ∈ Finset.Icc 1 H, g (n + j) *
              Complex.exp (2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) * (j : ℂ))‖) := by
        simp_rw [mul_add, Finset.sum_add_distrib, mul_add]
        congr 1
        rw [← Finset.sum_mul]
        change (1 / L) * (L * ((ε / 32) * (H : ℝ) / Real.log (H : ℝ))) = _
        field_simp [hL_pos.ne']
    _ ≤ (ε / 32) * (H : ℝ) / Real.log (H : ℝ) + (ε / 64) * (H : ℝ) / Real.log (H : ℝ) := by
        linarith [hMRT_bound]
    _ = (3 * ε / 64) * (H : ℝ) / Real.log (H : ℝ) := by ring

/- ### Hypotheses -/

/-- **Hypothesis 1 (Matomäki–Radziwiłł–Tao Fourier uniformity in short intervals)**:
for any `η > 0`, there is `H₀ ≥ 2` such that for any `H₁ ≥ H₀` there is `A ≥ 1` such that for
every `X ≥ A`, every `H ∈ [H₀, H₁]`, and every `A`-non-pretentious `S¹`-valued completely
multiplicative function `g`, the logarithmically averaged short-interval exponential sum of `g`
is at most `η log X` uniformly in `α : ℝ`. -/
def H1 : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ H₀ : ℕ, 2 ≤ H₀ ∧ ∀ H₁ : ℕ, H₀ ≤ H₁ →
      ∃ A : ℝ, 1 ≤ A ∧ ∀ X : ℕ, A ≤ (X : ℝ) → ∀ H ∈ Finset.Icc H₀ H₁,
        ∀ z : ℕ → Metric.sphere (0 : ℂ) 1,
          let g : ℕ → ℂ := fun n =>
            if n = 0 then 0 else n.factorization.prod fun p e => (z p).1 ^ e
          (∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
            1 ≤ q → (q : ℝ) ≤ A → |t| ≤ A * (X : ℝ) →
            A < ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
              (1 - (g p * star (χ (p : ZMod q)) *
                Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ)) →
          ∀ α : ℝ,
            ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X,
              (1 / ((H : ℝ) * (n : ℝ))) *
                ‖∑ j ∈ Finset.Icc 1 H,
                  g (n + j) * Complex.exp (2 * Real.pi * Complex.I * α * (j : ℂ))‖ ≤
              η * Real.log (X : ℝ)

/-- **Hypothesis 2 (Tao's entropy decrement and bilinear Hoeffding decoupling)**:
for any `h ≥ 1`, `δ ∈ (0, 1/4]`, `η > 0`, and `H₀ ≥ 2`, there exist `H₁ ≥ H₀` and `A ≥ 1` such
that for every `X ≥ A` and every 1-bounded `g : ℕ → ℂ`, there exists a scale `H ∈ [H₀, H₁]`
at which replacing `1_{p ∣ n + j}` by `1 / p` in the prime-averaged bilinear correlation over
`P_H = {p prime : δ H / 2 ≤ p ≤ δ H}` changes the logarithmic expectation by at most
`η H / log H`. -/
def H2 : Prop :=
  ∀ (h : ℕ), 1 ≤ h → ∀ (δ η : ℝ), 0 < δ → δ ≤ 1 / 4 → 0 < η → ∀ H₀ : ℕ, 2 ≤ H₀ →
    ∃ (H₁ : ℕ) (A : ℝ), H₀ ≤ H₁ ∧ 1 ≤ A ∧ ∀ X : ℕ, A ≤ (X : ℝ) →
      ∀ g : ℕ → ℂ, (∀ n : ℕ, ‖g n‖ ≤ 1) →
        ∃ H ∈ Finset.Icc H₀ H₁,
          let P_H : Finset ℕ :=
            (Finset.Icc (Nat.ceil (δ * (H : ℝ) / 2)) (Nat.floor (δ * (H : ℝ)))).filter Nat.Prime
          let L : ℝ := ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 : ℝ) / (n : ℝ)
          ‖(1 / (L : ℂ)) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℂ)) *
            ∑ p ∈ P_H, ∑ j ∈ Finset.Icc 1 H,
              if j + p * h ≤ H then
                ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
                  g (n + j) * star (g (n + j + p * h))
              else 0‖ ≤ η * (H : ℝ) / Real.log (H : ℝ)

/-- **Hypothesis 3 (Prime reciprocal density and Green–Tao/Selberg `L⁴` restriction)**:
for any `δ ∈ (0, 1/4]`, there exist `C > 0` and `H₀ ≥ 2` such that for all `H ≥ H₀`,
writing `P_H = {p prime : δ H / 2 ≤ p ≤ δ H}`, the reciprocal prime sum satisfies
`1 / (4 log H) ≤ ∑_{p ∈ P_H} 1 / p ≤ 2 / log H` and the discrete `L⁴` exponential sum moment
satisfies `∑_{k < H} ‖∑_{p ∈ P_H} (1 / p) e(-k p / H)‖⁴ ≤ C / (log H)⁴`. -/
def H3 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 4 →
    ∃ (C : ℝ) (H₀ : ℕ), 0 < C ∧ 2 ≤ H₀ ∧
      ∀ H : ℕ, H₀ ≤ H →
        let P_H : Finset ℕ :=
          (Finset.Icc (Nat.ceil (δ * (H : ℝ) / 2)) (Nat.floor (δ * (H : ℝ)))).filter Nat.Prime
        1 / (4 * Real.log (H : ℝ)) ≤ (∑ p ∈ P_H, (1 : ℝ) / (p : ℝ)) ∧
        (∑ p ∈ P_H, (1 : ℝ) / (p : ℝ)) ≤ 2 / Real.log (H : ℝ) ∧
        ∑ k ∈ Finset.range H,
          ‖∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) *
            Complex.exp (-2 * Real.pi * Complex.I * ((k : ℂ) * (p : ℂ) / (H : ℂ)))‖ ^ 4 ≤
          C / Real.log (H : ℝ) ^ 4

/- ### Main Reduction Theorem -/

theorem main : H1 → H2 → H3 → OMA.R_Erdos67_erdos_67_R1.H1 := by
  intro hMRT_all hDec_all hRestr_all
  dsimp only [OMA.R_Erdos67_erdos_67_R1.H1]
  intro h₁ h₂ hne ε hε
  set h : ℕ := if h₁ < h₂ then h₂ - h₁ else h₁ - h₂
  set s₀ : ℕ := min h₁ h₂
  have hh_pos : 1 ≤ h := by dsimp [h]; split_ifs <;> omega
  have hh_r_pos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh_pos
  set δ : ℝ := min (1 / (4 * (h : ℝ))) (ε / (128 * (h : ℝ)))
  have hδ_pos : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ_h_le14 : δ * (h : ℝ) ≤ 1 / 4 := by
    calc δ * (h : ℝ) ≤ (1 / (4 * (h : ℝ))) * (h : ℝ) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hh_r_pos.le
      _ = 1 / 4 := by field_simp [hh_r_pos.ne']
  have hδ_le14 : δ ≤ 1 / 4 := by
    have h1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast hh_pos
    nlinarith
  have hδ_h_le_eps : δ * (h : ℝ) ≤ ε / 128 := by
    calc δ * (h : ℝ) ≤ (ε / (128 * (h : ℝ))) * (h : ℝ) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hh_r_pos.le
      _ = ε / 128 := by field_simp [hh_r_pos.ne']
  obtain ⟨C, H₀_3, hC_pos, hH₀_3_ge2, hRestr⟩ := hRestr_all δ hδ_pos hδ_le14
  set γ : ℝ := ε / 64
  have hγ_pos : 0 < γ := by positivity
  set M_Ξ : ℝ := (h : ℝ) * C / γ ^ 4
  have hM_Ξ_pos : 0 < M_Ξ := by positivity
  set η₁ : ℝ := ε / (512 * (M_Ξ + 1))
  have hη₁_pos : 0 < η₁ := by positivity
  obtain ⟨H₀_1, hH₀_1_ge2, hMRT_H₁⟩ := hMRT_all η₁ hη₁_pos
  set H₀ : ℕ := max (max H₀_1 H₀_3) (Nat.ceil (4 / δ) + 4)
  have hH₀_ge2 : 2 ≤ H₀ := by omega
  obtain ⟨H₁, A₂, hH₀_le_H₁, hA₂_ge1, hDec⟩ :=
    hDec_all h hh_pos δ (ε / 64) hδ_pos hδ_le14 (by positivity) H₀ hH₀_ge2
  obtain ⟨A₁, hA₁_ge1, hMRT⟩ := hMRT_H₁ H₁ (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hH₀_le_H₁)
  obtain ⟨A, hA_ge1, hA₁_le, hA₂_le, hA_ge16, hA_props⟩ := exists_large_A (A₂ := A₂) (s₀ := s₀) (H₁ := H₁) hA₁_ge1 hε
  refine ⟨A, hA_ge1, fun X hX z hcorr => ?_⟩
  let g : ℕ → ℂ := fun n => if n = 0 then 0 else n.factorization.prod fun p e => (z p).1 ^ e
  have hg_mul : ∀ a b, g (a * b) = g a * g b := mulEval_mul z
  have hg_norm : ∀ n, 1 ≤ n → ‖g n‖ = 1 := fun n hn => mulEval_norm z hn
  have hg_le1 : ∀ n, ‖g n‖ ≤ 1 := mulEval_norm_le_one z
  have hX16 : 16 ≤ X := by exact_mod_cast hA_ge16.trans hX
  obtain ⟨hlog4, hs₀_le_sq, hs₀_err, hH₁_sq, haff_err⟩ := hA_props X hX
  by_contra hnonpret
  push Not at hnonpret
  have hcorr_h : (3 * ε / 4) * Real.log (X : ℝ) ≤
      ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, g n * star (g (n + h)) / (n : ℂ)‖ := by
    have hsym : ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, g (n + s₀) * star (g (n + s₀ + h)) / (n : ℂ)‖ =
        ‖∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, g (n + h₁) * star (g (n + h₂)) / (n : ℂ)‖ := by
      by_cases hlt : h₁ < h₂
      · have hs : s₀ = h₁ := min_eq_left hlt.le
        have hh' : s₀ + h = h₂ := by dsimp [h]; rw [if_pos hlt, hs]; omega
        congr 1; refine Finset.sum_congr rfl fun n _ => by rw [hs, Nat.add_assoc, ← hs, hh']
      · have hgt : h₂ < h₁ := by omega
        have hs : s₀ = h₂ := min_eq_right hgt.le
        have hh' : s₀ + h = h₁ := by dsimp [h]; rw [if_neg hlt, hs]; omega
        rw [← norm_star, star_sum]
        congr 1; refine Finset.sum_congr rfl fun n _ => ?_
        have hsn : star (n : ℂ) = (n : ℂ) := by rw [Complex.star_def, Complex.conj_natCast]
        rw [star_div₀, star_mul', star_star, hsn, mul_comm, hs, Nat.add_assoc, ← hs, hh']
    have hshift := log_shift_bound hX16 hs₀_le_sq (fun n => g n * star (g (n + h)))
      (fun n => by rw [norm_mul, norm_star]; exact mul_le_one₀ (hg_le1 _) (norm_nonneg _) (hg_le1 _))
    have htri := norm_sub_norm_le
      (∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, g (n + s₀) * star (g (n + s₀ + h)) / (n : ℂ))
      (∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, g n * star (g (n + h)) / (n : ℂ))
    have hrew_sh : ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (fun n => g n * star (g (n + h))) (n + s₀) / (n : ℂ) =
        ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, g (n + s₀) * star (g (n + s₀ + h)) / (n : ℂ) := rfl
    rw [hrew_sh] at hshift
    linarith [hcorr]
  let L : ℝ := ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 : ℝ) / (n : ℝ)
  have hL_bounds : (1 / 4) * Real.log (X : ℝ) ≤ L ∧ L ≤ (3 / 4) * Real.log (X : ℝ) :=
    harmonic_sqrt_bounds hX16 hlog4
  obtain ⟨H, hH_mem, hDec_H⟩ := hDec X (hA₂_le.trans hX) g hg_le1
  have hH_ge_H₀ : H₀ ≤ H := (Finset.mem_Icc.mp hH_mem).1
  have hH_le_H₁ : H ≤ H₁ := (Finset.mem_Icc.mp hH_mem).2
  have hH_ge4 : 4 ≤ H := le_trans (le_trans (by omega : 4 ≤ Nat.ceil (4 / δ) + 4) (le_max_right _ _)) hH_ge_H₀
  have hH_pos : 1 ≤ H := by omega
  have hlogH_ge1 : 1 ≤ Real.log (H : ℝ) := by
    have h4 : (Real.exp 1 : ℝ) ≤ (H : ℝ) := by
      have he := Real.exp_one_lt_d9
      have h4' : (4 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hH_ge4
      linarith
    have := Real.log_le_log (Real.exp_pos 1) h4
    rwa [Real.log_exp] at this
  have hlogH_pos : 0 < Real.log (H : ℝ) := by linarith
  have hH_ge_H₀_3 : H₀_3 ≤ H := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hH_ge_H₀
  obtain ⟨hP_lb, hP_ub, hL4⟩ := hRestr H hH_ge_H₀_3
  let P_H : Finset ℕ :=
    (Finset.Icc (Nat.ceil (δ * (H : ℝ) / 2)) (Nat.floor (δ * (H : ℝ)))).filter Nat.Prime
  have hp_in_P : ∀ p ∈ P_H, 2 ≤ p ∧ (p : ℝ) ≤ δ * (H : ℝ) ∧ p ≤ H := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpI := Finset.mem_Icc.mp hp'.1
    have hp_le_dH : (p : ℝ) ≤ δ * (H : ℝ) :=
      (by exact_mod_cast hpI.2 : (p : ℝ) ≤ (Nat.floor (δ * (H : ℝ)) : ℝ)).trans (Nat.floor_le (by positivity))
    have hp_le_H : p ≤ H := by
      have : (p : ℝ) ≤ (H : ℝ) := hp_le_dH.trans (by nlinarith)
      exact_mod_cast this
    exact ⟨hp'.2.two_le, hp_le_dH, hp_le_H⟩
  have hProp26 : (11 * ε / 64) * (H : ℝ) / Real.log (H : ℝ) ≤
      ‖(1 / (L : ℂ)) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℂ)) *
        ∑ p ∈ P_H, ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then
            (if p ∣ n + j then (1 : ℂ) else 0) * g (n + j) * star (g (n + j + p * h))
          else 0‖ :=
    prop26_bilinear_lb hX16 hlog4 hH_pos hH_le_H₁ hlogH_pos hε hδ_h_le14 hH₁_sq haff_err
      P_H hp_in_P hP_lb hP_ub g hg_mul hg_norm hg_le1 hcorr_h
  have hDec_lb : (10 * ε / 64) * (H : ℝ) / Real.log (H : ℝ) ≤
      ‖(1 / (L : ℂ)) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℂ)) *
        ∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then g (n + j) * star (g (n + j + p * h)) else 0‖ := by
    have hdiff_eq :
        ((1 / (L : ℂ)) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℂ)) *
          ∑ p ∈ P_H, ∑ j ∈ Finset.Icc 1 H,
            if j + p * h ≤ H then
              (if p ∣ n + j then (1 : ℂ) else 0) * g (n + j) * star (g (n + j + p * h))
            else 0) -
        ((1 / (L : ℂ)) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℂ)) *
          ∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j ∈ Finset.Icc 1 H,
            if j + p * h ≤ H then g (n + j) * star (g (n + j + p * h)) else 0) =
        (1 / (L : ℂ)) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℂ)) *
          ∑ p ∈ P_H, ∑ j ∈ Finset.Icc 1 H,
            if j + p * h ≤ H then
              ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
                g (n + j) * star (g (n + j + p * h))
            else 0 := by
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1; refine Finset.sum_congr rfl fun n _ => ?_
      rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1; refine Finset.sum_congr rfl fun p _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      split_ifs <;> ring
    have htri := norm_sub_norm_le
      ((1 / (L : ℂ)) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℂ)) *
        ∑ p ∈ P_H, ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then
            (if p ∣ n + j then (1 : ℂ) else 0) * g (n + j) * star (g (n + j + p * h))
          else 0)
      ((1 / (L : ℂ)) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℂ)) *
        ∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then g (n + j) * star (g (n + j + p * h)) else 0)
    rw [hdiff_eq] at htri
    change ‖(1 / (L : ℂ)) * ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / (n : ℂ)) *
        ∑ p ∈ P_H, ∑ j ∈ Finset.Icc 1 H,
          if j + p * h ≤ H then
            ((if p ∣ n + j then (1 : ℂ) else 0) - 1 / (p : ℂ)) *
              g (n + j) * star (g (n + j + p * h))
          else 0‖ ≤ (ε / 64) * (H : ℝ) / Real.log (H : ℝ) at hDec_H
    have h10 : (10 * ε / 64) * (H : ℝ) / Real.log (H : ℝ) =
        (11 * ε / 64) * (H : ℝ) / Real.log (H : ℝ) - (ε / 64) * (H : ℝ) / Real.log (H : ℝ) := by ring
    linarith [hProp26, hDec_H, htri, h10]
  have : NeZero H := ⟨by omega⟩
  let S_H : ℕ → ℂ := fun k =>
    ∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) *
      Complex.exp (-2 * Real.pi * Complex.I * ((k : ℂ) * (p : ℂ) / (H : ℂ)))
  let Ξ_H : Finset (ZMod H) := Finset.univ.filter fun ξ : ZMod H =>
    γ / Real.log (H : ℝ) ≤ ‖S_H (((h : ZMod H) * ξ).val)‖
  have hΞ_card : (Ξ_H.card : ℝ) ≤ M_Ξ :=
    markov_major_spectrum_card hh_pos hlogH_pos hγ_pos S_H hL4
  have hCircle : ∀ n : ℕ,
      ‖∑ p ∈ P_H, ((1 : ℂ) / (p : ℂ)) * ∑ j ∈ Finset.Icc 1 H,
        if j + p * h ≤ H then g (n + j) * star (g (n + j + p * h)) else 0‖ ≤
      (ε / 32) * (H : ℝ) / Real.log (H : ℝ) +
      (2 / Real.log (H : ℝ)) * ∑ ξ ∈ Ξ_H,
        ‖∑ j ∈ Finset.Icc 1 H, g (n + j) *
          Complex.exp (2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) * (j : ℂ))‖ :=
    fun n => circle_method_pointwise hlogH_pos hε hδ_h_le14 hδ_h_le_eps P_H hp_in_P hP_ub g hg_le1 n
  have hH_mem_MRT : H ∈ Finset.Icc H₀_1 H₁ :=
    Finset.mem_Icc.mpr ⟨le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hH_ge_H₀, hH_le_H₁⟩
  have hnonpret_A₁ : ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (t : ℝ),
      1 ≤ q → (q : ℝ) ≤ A₁ → |t| ≤ A₁ * (X : ℝ) →
      A₁ < ∑ p ∈ (Finset.Icc 1 X).filter Nat.Prime,
        (1 - (g p * star (χ (p : ZMod q)) *
          Complex.exp (-Complex.I * t * Real.log (p : ℝ))).re) / (p : ℝ) := by
    intro q χ t hq1 hqA₁ htA₁
    have h1 := hnonpret q χ t hq1 (hqA₁.trans hA₁_le)
      (htA₁.trans (mul_le_mul_of_nonneg_right hA₁_le (Nat.cast_nonneg X)))
    linarith
  have hMRT_ξ : ∀ ξ ∈ Ξ_H,
      ∑ n ∈ Finset.Icc (Nat.sqrt X + 1) X, (1 / ((H : ℝ) * (n : ℝ))) *
        ‖∑ j ∈ Finset.Icc 1 H, g (n + j) *
          Complex.exp (2 * Real.pi * Complex.I * (((-((ξ.val : ℕ) : ℝ) / (H : ℝ) : ℝ) : ℂ)) * (j : ℂ))‖ ≤
        η₁ * Real.log (X : ℝ) :=
    fun ξ _ => hMRT X (hA₁_le.trans hX) H hH_mem_MRT z hnonpret_A₁ (-((ξ.val : ℕ) : ℝ) / (H : ℝ))
  have hUpper := mrt_average_upper_bound hlog4 hlogH_pos hε hM_Ξ_pos rfl P_H Ξ_H g hL_bounds.1 hΞ_card hCircle hMRT_ξ
  have hpos_scale : 0 < ε * (H : ℝ) / Real.log (H : ℝ) := by positivity
  have hcontra : (10 * ε / 64) * (H : ℝ) / Real.log (H : ℝ) - (3 * ε / 64) * (H : ℝ) / Real.log (H : ℝ) =
      (7 / 64) * (ε * (H : ℝ) / Real.log (H : ℝ)) := by ring
  linarith [hDec_lb, hUpper, hpos_scale, hcontra]

end OMA.R_Erdos67_erdos_67_R1_H1_R1
