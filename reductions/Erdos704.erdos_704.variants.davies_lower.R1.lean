import FormalConjectures.ErdosProblems.«704»
import Mathlib

-- Reduction Erdos704.erdos_704.variants.davies_lower.R1 of Erdős Problem 704 — davies lower
-- Credit: @tkaiman
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Three-step reduction of Davies's `(2 + o(1))^d` lower bound for `χ(ℝ^d)`

Follows James Davies, *Measurable obstructions for unmeasurable colourings*
(arXiv:2610.12301), Sections 3, 6, 7, and 8 via the scalar independence density route:

* `H1` (Section 8, Theorem 1.4): for every `c ∈ (0, 2)` and all sufficiently large `d`,
  there is a real polynomial `P` with `P(0) = 1` and `B > 0` satisfying `c^d ≤ 1 + 1/B`
  and `P(s^2) * Ω_d(s / (2π)) ≥ -B` for all `s ≥ 0`, where `Ω_d` is the normalized
  spherical transform on `S^{d-1}` in 1D integral form.
* `H2` (Theorem 8.1 + DeCorte–Oliveira–Vallentin / Appendix A): for `d ≥ 5`, such a
  polynomial certificate yields a scaled rational finite-point Boolean-copositive
  (`BQC*`) scalar certificate on `ℤ^d` with value `z₀ < B / (1 + B) + ε`.
* `H3` (Section 6, Theorem 6.3): higher-dimensional radial transference for `d ≥ 5`,
  transferring any nonnegative radial linear combination of `Ω_d(‖w‖ τ)` to a finite
  symmetric family of integer Euclidean similitudes `Γ : M_d(ℤ)` with positive
  trigonometric polynomial average on `ℝ^d`.

Inside `main`, we prove the Cayley-graph `BQC*` Fourier independence bound on `(ℤ/Mℤ)^d`
(Section 3, Theorem 3.1) directly via discrete Fourier orthogonality, embed `ℤ^d` into
`unitDistanceGraph d` via `x ↦ (1 / (m * L)) • x`, and combine `H1`, `H2`, `H3` with
pigeonhole on a large box `[-N, N]^d` as `N → ∞` (Section 7).
-/

namespace OMA.R_Erdos704_erdos_704_variants_davies_lower_R1

open Filter Finset Real Complex
open scoped BigOperators

/-- Section 8 (Davies, arXiv:2610.12301): existence of a radial polynomial certificate
`P(s^2) * Ω_d(s/(2π)) ≥ -B` with `P(0) = 1` and `1 + 1/B ≥ c^d` for large `d`. -/
def H1 : Prop :=
  ∀ c ∈ Set.Ioo (0 : ℝ) 2, ∀ᶠ d : ℕ in atTop,
    let Ω : ℝ → ℝ := fun t =>
      (∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi * t * u) * (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)) /
      (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2))
    ∃ (P : Polynomial ℝ) (B : ℝ),
      P.eval 0 = 1 ∧ 0 < B ∧ c ^ d ≤ 1 + 1 / B ∧
      ∀ s : ℝ, 0 ≤ s → -B ≤ P.eval (s ^ 2) * Ω (s / (2 * Real.pi))

/-- Theorem 8.1 + DeCorte–Oliveira–Vallentin converse (Appendix A): a radial polynomial
certificate yields a scaled finite-point Boolean-copositive scalar certificate on `ℤ^d`. -/
def H2 : Prop :=
  ∀ (d : ℕ), 5 ≤ d →
    let Ω : ℝ → ℝ := fun t =>
      (∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi * t * u) * (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)) /
      (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2))
    ∀ (P : Polynomial ℝ) (B : ℝ),
      P.eval 0 = 1 → 0 < B → (∀ s : ℝ, 0 ≤ s → -B ≤ P.eval (s ^ 2) * Ω (s / (2 * Real.pi))) →
      ∀ ε : ℝ, 0 < ε →
        ∃ (m : ℕ) (ℓ : ℕ) (U : Fin ℓ → Finset (Fin d → ℤ))
          (Z : Fin ℓ → (Fin d → ℤ) → (Fin d → ℤ) → ℝ) (z₀ a : ℝ),
          0 < m ∧ z₀ < B / (1 + B) + ε ∧
          (∀ q (S : Finset (Fin d → ℤ)), S ⊆ U q → 0 ≤ ∑ u ∈ S, ∑ v ∈ S, Z q u v) ∧
          1 ≤ z₀ + a - ∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ U q, Z q u v ∧
          ∀ τ : ℝ, 0 ≤ τ →
            0 ≤ z₀ - ∑ q : Fin ℓ, ∑ u ∈ U q, Z q u u + a * Ω ((m : ℝ) * τ) -
              ∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ (U q).erase u,
                Z q u v * Ω (Real.sqrt (∑ i : Fin d, ((v i - u i : ℤ) : ℝ) ^ 2) * τ)

/-- Section 6 (Theorem 6.3, higher-dimensional radial transference for `d ≥ 5`):
a nonnegative radial combination of `Ω_d(‖w‖ τ)` transfers to an integer similitude
family with positive cosine average on `ℝ^d`. -/
def H3 : Prop :=
  ∀ (d : ℕ), 5 ≤ d →
    let Ω : ℝ → ℝ := fun t =>
      (∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi * t * u) * (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)) /
      (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2))
    ∀ (W : Finset (Fin d → ℤ)) (cInf : ℝ) (cw : (Fin d → ℤ) → ℝ),
      (∀ w ∈ W, w ≠ 0) →
      (∀ τ : ℝ, 0 ≤ τ →
        0 ≤ cInf + ∑ w ∈ W, cw w * Ω (Real.sqrt (∑ i : Fin d, ((w i : ℤ) : ℝ) ^ 2) * τ)) →
      ∀ ε : ℝ, 0 < ε →
        ∃ (L : ℕ) (ι : ℕ) (Γ : Fin ι → Matrix (Fin d) (Fin d) ℤ) (neg : Fin ι → Fin ι),
          0 < L ∧ 0 < ι ∧ Function.Involutive neg ∧
          (∀ t, Γ (neg t) = -(Γ t)) ∧
          (∀ t (w : Fin d → ℤ),
            ∑ i : Fin d, (((Γ t).mulVec w i : ℤ) : ℝ) ^ 2 =
              (L : ℝ) ^ 2 * ∑ i : Fin d, ((w i : ℤ) : ℝ) ^ 2) ∧
          ∀ θ : Fin d → ℝ,
            0 < cInf + ε + (1 / (ι : ℝ)) *
              ∑ t : Fin ι, ∑ w ∈ W,
                cw w * Real.cos (2 * Real.pi * ∑ i : Fin d, (((Γ t).mulVec w i : ℤ) : ℝ) * θ i)

lemma exp_two_pi_I_zmod_add {M : ℕ} [NeZero M] (a b c : ZMod M) :
    Complex.exp (2 * Real.pi * Complex.I * (((a + b).val : ℝ) * (c.val : ℝ) / (M : ℝ))) =
    Complex.exp (2 * Real.pi * Complex.I * ((a.val : ℝ) * (c.val : ℝ) / (M : ℝ))) *
    Complex.exp (2 * Real.pi * Complex.I * ((b.val : ℝ) * (c.val : ℝ) / (M : ℝ))) := by
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hval : (a + b).val = (a.val + b.val) % M := ZMod.val_add a b
  set q : ℕ := (a.val + b.val) / M
  have hdiv : a.val + b.val = (a + b).val + M * q := by
    rw [hval, Nat.mod_add_div]
  let n : ℤ := -((q * c.val : ℕ) : ℤ)
  have hn : (n : ℂ) = -((q : ℂ) * (c.val : ℂ)) := by dsimp [n]; push_cast; ring
  have hdivC : ((a.val : ℂ) + (b.val : ℂ)) = ((a + b).val : ℂ) + (M : ℂ) * (q : ℂ) := by
    exact_mod_cast hdiv
  have hfrac :
      (((a + b).val : ℂ) * (c.val : ℂ) / (M : ℂ)) =
      ((a.val : ℂ) * (c.val : ℂ) / (M : ℂ) + (b.val : ℂ) * (c.val : ℂ) / (M : ℂ)) + (n : ℂ) := by
    rw [hn]
    field_simp [hMC]
    linear_combination -(c.val : ℂ) * hdivC
  rw [← Complex.exp_add]
  have hdiff :
      2 * (Real.pi : ℂ) * Complex.I * (((a + b).val : ℝ) * (c.val : ℝ) / (M : ℝ)) =
      (2 * (Real.pi : ℂ) * Complex.I * ((a.val : ℝ) * (c.val : ℝ) / (M : ℝ)) +
       2 * (Real.pi : ℂ) * Complex.I * ((b.val : ℝ) * (c.val : ℝ) / (M : ℝ))) +
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    rw [hfrac]
    ring
  rw [hdiff, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma exp_two_pi_I_zmod_intCast {M : ℕ} [NeZero M] (z : ℤ) (c : ZMod M) :
    Complex.exp (2 * Real.pi * Complex.I * ((((z : ZMod M).val : ℝ) * (c.val : ℝ)) / (M : ℝ))) =
    Complex.exp (2 * Real.pi * Complex.I * ((z : ℝ) * ((c.val : ℝ) / (M : ℝ)))) := by
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hmod : (((z : ZMod M).val : ℤ) : ZMod M) = (z : ZMod M) := by simp
  have hdvd : (M : ℤ) ∣ ((z : ZMod M).val : ℤ) - z :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub z ((z : ZMod M).val : ℤ) M).mp hmod.symm
  obtain ⟨q, hq⟩ := hdvd
  let n : ℤ := q * (c.val : ℤ)
  have hn : (n : ℂ) = (q : ℂ) * (c.val : ℂ) := by dsimp [n]; push_cast; ring
  have hqC : (((z : ZMod M).val : ℂ) - (z : ℂ)) = (M : ℂ) * (q : ℂ) := by
    exact_mod_cast hq
  have hfrac :
      (((z : ZMod M).val : ℂ) * (c.val : ℂ) / (M : ℂ)) =
      (z : ℂ) * ((c.val : ℂ) / (M : ℂ)) + (n : ℂ) := by
    rw [hn]
    field_simp [hMC]
    linear_combination (c.val : ℂ) * hqC
  have hdiff :
      2 * (Real.pi : ℂ) * Complex.I * ((((z : ZMod M).val : ℝ) * (c.val : ℝ)) / (M : ℝ)) =
      2 * (Real.pi : ℂ) * Complex.I * ((z : ℝ) * ((c.val : ℝ) / (M : ℝ))) +
      (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast
    rw [hfrac]
    ring
  rw [hdiff, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma sum_zmod_char {M : ℕ} [NeZero M] (x : ZMod M) :
    (∑ w : ZMod M, Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℝ) * (w.val : ℝ) / (M : ℝ)))) =
      if x = 0 then (M : ℂ) else 0 := by
  have hMpos : 0 < M := NeZero.pos M
  have hM : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  have hMC : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne M)
  by_cases hx : x = 0
  · subst hx
    simp [ZMod.card]
  · simp only [hx, ↓reduceIte]
    have hxpos : 0 < x.val := Nat.pos_of_ne_zero (fun h => hx ((ZMod.val_eq_zero x).mp h))
    have hxlt : x.val < M := ZMod.val_lt x
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℝ) / (M : ℝ)))
    have hsum :
        (∑ w : ZMod M, Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℝ) * (w.val : ℝ) / (M : ℝ)))) =
        ∑ k ∈ Finset.range M, ζ ^ k := by
      have heq : ∀ w : ZMod M,
          Complex.exp (2 * Real.pi * Complex.I * ((x.val : ℝ) * (w.val : ℝ) / (M : ℝ))) =
          ζ ^ w.val := by
        intro w
        dsimp only [ζ]
        rw [← Complex.exp_nat_mul]
        congr 1
        push_cast
        ring
      simp_rw [heq]
      refine Finset.sum_bij (fun w _ => w.val) (fun w _ => Finset.mem_range.mpr (ZMod.val_lt w))
        (fun a _ b _ h => ZMod.val_injective M h) ?_ (fun _ _ => rfl)
      intro k hk
      refine ⟨(k : ZMod M), Finset.mem_univ _, ZMod.val_natCast_of_lt (Finset.mem_range.mp hk)⟩
    rw [hsum]
    have hζne : ζ ≠ 1 := by
      intro h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨m, hm⟩ := h1
      have him : 2 * Real.pi * ((x.val : ℝ) / (M : ℝ)) = (m : ℝ) * (2 * Real.pi) := by
        have := congrArg Complex.im hm
        simpa [Complex.mul_im, Complex.mul_re] using this
      have hdiv : (x.val : ℝ) / (M : ℝ) = (m : ℝ) := by
        have hpi : 2 * Real.pi ≠ 0 := by positivity
        exact mul_left_cancel₀ hpi (by linarith)
      have hmul : (x.val : ℝ) = (m : ℝ) * (M : ℝ) := (div_eq_iff hM).mp hdiv
      have hmulZ : (x.val : ℤ) = m * (M : ℤ) := by exact_mod_cast hmul
      have : (0 : ℤ) < m * (M : ℤ) ∧ m * (M : ℤ) < (M : ℤ) := by
        rw [← hmulZ]; exact ⟨by exact_mod_cast hxpos, by exact_mod_cast hxlt⟩
      have hm1 : 1 ≤ m := by nlinarith
      have : (M : ℤ) ≤ m * (M : ℤ) := by nlinarith
      omega
    rw [geom_sum_eq hζne]
    have hζM : ζ ^ M = 1 := by
      dsimp only [ζ]
      rw [← Complex.exp_nat_mul]
      have : (M : ℂ) * (2 * Real.pi * Complex.I * ((x.val : ℝ) / (M : ℝ))) =
          ((x.val : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        push_cast; field_simp [hMC]
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [hζM, sub_self, zero_div]

lemma sum_pi_zmod_char {d M : ℕ} [NeZero M] (x : Fin d → ZMod M) :
    (∑ w : Fin d → ZMod M,
      Complex.exp (2 * Real.pi * Complex.I *
        ∑ i : Fin d, ((x i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ))) =
      if x = 0 then ((M : ℂ) ^ d) else 0 := by
  set g : Fin d → ZMod M → ℂ := fun i a =>
    Complex.exp (2 * Real.pi * Complex.I * (((x i).val : ℝ) * (a.val : ℝ) / (M : ℝ)))
  have hprod : ∀ w : Fin d → ZMod M,
      Complex.exp (2 * Real.pi * Complex.I *
        ∑ i : Fin d, ((x i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ)) =
      ∏ i : Fin d, g i (w i) := by
    intro w
    dsimp only [g]
    simp only [Complex.ofReal_sum]
    rw [Finset.mul_sum, Complex.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    congr 1; push_cast; ring
  simp_rw [hprod]
  rw [← Fintype.prod_sum g]
  have hrow : ∀ i : Fin d, (∑ a : ZMod M, g i a) = if x i = 0 then (M : ℂ) else 0 := fun i =>
    sum_zmod_char (x i)
  simp_rw [hrow]
  by_cases hx : x = 0
  · subst hx
    simp
  · simp only [hx, ↓reduceIte]
    have hne : ∃ i : Fin d, x i ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hx (funext hall)
    obtain ⟨i₀, hi₀⟩ := hne
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])

lemma chi_mul_conj {d M : ℕ} [NeZero M] (w x y : Fin d → ZMod M) :
    Complex.exp (2 * Real.pi * Complex.I *
      ∑ i : Fin d, (((y - x) i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ)) =
    Complex.exp (2 * Real.pi * Complex.I *
      ∑ i : Fin d, ((y i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ)) *
    starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I *
      ∑ i : Fin d, ((x i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ))) := by
  have hconj :
      starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I *
        ∑ i : Fin d, ((x i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ))) =
      Complex.exp (-(2 * Real.pi * Complex.I *
        ∑ i : Fin d, ((x i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ))) := by
    rw [← Complex.exp_conj]
    congr 1
    simp [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  rw [hconj, ← Complex.exp_add]
  have hadd : ∀ i : Fin d,
      Complex.exp (2 * Real.pi * Complex.I * (((y i - x i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ))) *
      Complex.exp (2 * Real.pi * Complex.I * (((x i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ))) =
      Complex.exp (2 * Real.pi * Complex.I * (((y i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ))) := by
    intro i
    rw [← exp_two_pi_I_zmod_add, sub_add_cancel]
  have hprod :
      Complex.exp (2 * Real.pi * Complex.I *
        ∑ i : Fin d, (((y - x) i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ)) *
      Complex.exp (2 * Real.pi * Complex.I *
        ∑ i : Fin d, ((x i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ)) =
      Complex.exp (2 * Real.pi * Complex.I *
        ∑ i : Fin d, ((y i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ)) := by
    push_cast
    simp_rw [Finset.mul_sum, Complex.exp_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => hadd i
  have hne : Complex.exp (2 * Real.pi * Complex.I *
      ∑ i : Fin d, ((x i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ)) ≠ 0 := Complex.exp_ne_zero _
  apply mul_right_cancel₀ hne
  rw [hprod, ← Complex.exp_add]
  congr 1
  ring

lemma pair_count_dft {d M : ℕ} [NeZero M] (A : Finset (Fin d → ZMod M)) (v : Fin d → ZMod M) :
    (((∑ x ∈ A, ∑ y ∈ A, if y - x = v then (1 : ℝ) else 0 : ℝ) : ℝ) : ℂ) =
    (1 / ((M : ℂ) ^ d)) *
      ∑ w : Fin d → ZMod M,
        (Complex.normSq (∑ x ∈ A, Complex.exp (2 * Real.pi * Complex.I *
          ∑ i : Fin d, ((x i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ))) : ℂ) *
        starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I *
          ∑ i : Fin d, ((v i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ))) := by
  have hMd : ((M : ℂ) ^ d) ≠ 0 := pow_ne_zero d (Nat.cast_ne_zero.mpr (NeZero.ne M))
  set χ : (Fin d → ZMod M) → (Fin d → ZMod M) → ℂ := fun w x =>
    Complex.exp (2 * Real.pi * Complex.I *
      ∑ i : Fin d, ((x i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ))
  have hχsub : ∀ w x y, χ w (y - x) = χ w y * starRingEnd ℂ (χ w x) := fun w x y =>
    chi_mul_conj w x y
  have hind : ∀ x y : Fin d → ZMod M,
      ((if y - x = v then (1 : ℝ) else 0 : ℝ) : ℂ) =
      (1 / ((M : ℂ) ^ d)) * ∑ w : Fin d → ZMod M, χ w y * starRingEnd ℂ (χ w x) * starRingEnd ℂ (χ w v) := by
    intro x y
    have h1 : ∑ w : Fin d → ZMod M, χ w y * starRingEnd ℂ (χ w x) * starRingEnd ℂ (χ w v) =
        ∑ w : Fin d → ZMod M, χ w (y - x - v) := by
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hχsub w v (y - x), hχsub w x y]
    rw [h1, sum_pi_zmod_char]
    by_cases h : y - x = v
    · have h0 : y - x - v = 0 := sub_eq_zero.mpr h
      simp [h, hMd]
    · have h0 : y - x - v ≠ 0 := sub_ne_zero.mpr h
      simp [h, h0]
  conv_lhs => simp only [Complex.ofReal_sum]
  simp_rw [hind, ← Finset.mul_sum]
  congr 1
  trans ∑ x ∈ A, ∑ w : Fin d → ZMod M,
      ∑ y ∈ A, χ w y * starRingEnd ℂ (χ w x) * starRingEnd ℂ (χ w v)
  · refine Finset.sum_congr rfl fun x _ => Finset.sum_comm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun w _ => ?_
  have hnorm : ((Complex.normSq (∑ x ∈ A, χ w x) : ℝ) : ℂ) =
      (∑ y ∈ A, χ w y) * (∑ x ∈ A, starRingEnd ℂ (χ w x)) := by
    rw [← map_sum]
    exact (Complex.mul_conj (∑ x ∈ A, χ w x)).symm
  change ∑ x ∈ A, ∑ y ∈ A, χ w y * starRingEnd ℂ (χ w x) * starRingEnd ℂ (χ w v) =
      ((Complex.normSq (∑ x ∈ A, χ w x) : ℝ) : ℂ) * starRingEnd ℂ (χ w v)
  rw [hnorm]
  have hswap_xy : ∀ (a b : (Fin d → ZMod M) → ℂ) (c : ℂ),
      (∑ x ∈ A, ∑ y ∈ A, a y * b x * c) = ((∑ y ∈ A, a y) * (∑ x ∈ A, b x)) * c := by
    intro a b c
    rw [Finset.sum_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  exact hswap_xy (fun y => χ w y) (fun x => starRingEnd ℂ (χ w x)) (starRingEnd ℂ (χ w v))

lemma re_sum_invol_cos {ι d M : ℕ} [NeZero M]
    (Γ : Fin ι → Matrix (Fin d) (Fin d) ℤ) (neg : Fin ι → Fin ι)
    (hneg : Function.Involutive neg) (hΓneg : ∀ t, Γ (neg t) = -(Γ t))
    (u : Fin d → ℤ) (w : Fin d → ZMod M) :
    (∑ t : Fin ι, starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I *
      ∑ i : Fin d, ((((Γ t).mulVec u i : ZMod M).val : ℝ) * ((w i).val : ℝ)) / (M : ℝ)))) =
    ((∑ t : Fin ι, Real.cos (2 * Real.pi *
      ∑ i : Fin d, (((Γ t).mulVec u i : ℤ) : ℝ) * (((w i).val : ℝ) / (M : ℝ)))) : ℂ) := by
  have hterm : ∀ t : Fin ι,
      starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I *
        ∑ i : Fin d, ((((Γ t).mulVec u i : ZMod M).val : ℝ) * ((w i).val : ℝ)) / (M : ℝ))) =
      Complex.exp (-(2 * Real.pi * Complex.I *
        ∑ i : Fin d, (((Γ t).mulVec u i : ℤ) : ℝ) * (((w i).val : ℝ) / (M : ℝ)))) := by
    intro t
    have h1 :
        Complex.exp (2 * Real.pi * Complex.I *
          ∑ i : Fin d, ((((Γ t).mulVec u i : ZMod M).val : ℝ) * ((w i).val : ℝ)) / (M : ℝ)) =
        Complex.exp (2 * Real.pi * Complex.I *
          ∑ i : Fin d, (((Γ t).mulVec u i : ℤ) : ℝ) * (((w i).val : ℝ) / (M : ℝ))) := by
      simp only [Complex.ofReal_sum]
      rw [Finset.mul_sum, Finset.mul_sum, Complex.exp_sum, Complex.exp_sum]
      refine Finset.prod_congr rfl fun i _ => ?_
      have hi := exp_two_pi_I_zmod_intCast ((Γ t).mulVec u i) (w i)
      push_cast at hi ⊢
      exact hi
    rw [h1, ← Complex.exp_conj]
    congr 1
    simp [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  simp_rw [hterm]
  set f : Fin ι → ℝ := fun t =>
    2 * Real.pi * ∑ i : Fin d, (((Γ t).mulVec u i : ℤ) : ℝ) * (((w i).val : ℝ) / (M : ℝ))
  have hfneg : ∀ t, f (neg t) = -(f t) := by
    intro t
    dsimp only [f]
    rw [hΓneg t]
    simp only [Matrix.neg_mulVec, Pi.neg_apply, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, mul_neg]
  have h2 :
      (2 : ℂ) * ∑ t : Fin ι, Complex.exp (-(f t : ℂ) * Complex.I) =
      (2 : ℂ) * ∑ t : Fin ι, (Real.cos (f t) : ℂ) := by
    have hbij : ∑ t : Fin ι, Complex.exp (-(f t : ℂ) * Complex.I) =
        ∑ t : Fin ι, Complex.exp (-(f (neg t) : ℂ) * Complex.I) :=
      (Equiv.sum_comp (Function.Involutive.toPerm neg hneg) _).symm
    calc
      (2 : ℂ) * ∑ t : Fin ι, Complex.exp (-(f t : ℂ) * Complex.I)
          = (∑ t : Fin ι, Complex.exp (-(f t : ℂ) * Complex.I)) +
            (∑ t : Fin ι, Complex.exp (-(f (neg t) : ℂ) * Complex.I)) := by
              rw [two_mul]; congr 1
      _ = ∑ t : Fin ι, (Complex.exp (-(f t : ℂ) * Complex.I) +
            Complex.exp ((f t : ℂ) * Complex.I)) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl fun t _ => ?_
              rw [hfneg t]; push_cast; simp
      _ = ∑ t : Fin ι, (2 : ℂ) * (Real.cos (f t) : ℂ) := by
              refine Finset.sum_congr rfl fun t _ => ?_
              rw [Complex.exp_mul_I, Complex.exp_mul_I]
              simp only [Complex.cos_neg, Complex.sin_neg, ← Complex.ofReal_cos]
              ring
      _ = (2 : ℂ) * ∑ t : Fin ι, (Real.cos (f t) : ℂ) := by rw [Finset.mul_sum]
  have heq : (∑ t : Fin ι, Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I *
      ∑ i : Fin d, (((Γ t).mulVec u i : ℤ) : ℝ) * (((w i).val : ℝ) / (M : ℝ))))) =
      ∑ t : Fin ι, Complex.exp (-(f t : ℂ) * Complex.I) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    dsimp only [f]; congr 1; push_cast; ring
  rw [heq]
  have h2' := mul_left_cancel₀ (by norm_num : (2 : ℂ) ≠ 0) h2
  simpa [f] using h2'

lemma bqc_translate_nonneg {d M : ℕ} [NeZero M] (A : Finset (Fin d → ZMod M))
    (U : Finset (Fin d → ℤ)) (Z : (Fin d → ℤ) → (Fin d → ℤ) → ℝ)
    (hZ : ∀ S ⊆ U, 0 ≤ ∑ u ∈ S, ∑ v ∈ S, Z u v)
    (T : Matrix (Fin d) (Fin d) ℤ) :
    0 ≤ ∑ u ∈ U, ∑ v ∈ U, Z u v *
      ∑ x ∈ A, ∑ y ∈ A,
        if y - x = (fun i => (T.mulVec (v - u) i : ZMod M)) then (1 : ℝ) else 0 := by
  classical
  set emb : (Fin d → ℤ) → (Fin d → ZMod M) := fun u i => (T.mulVec u i : ZMod M)
  have hemb_sub : ∀ u v, (fun i => (T.mulVec (v - u) i : ZMod M)) = emb v - emb u := by
    intro u v; ext i
    simp [emb, Matrix.mulVec_sub]
  have hrewrite : ∀ u v,
      (∑ x ∈ A, ∑ y ∈ A, if y - x = emb v - emb u then (1 : ℝ) else 0) =
      ∑ s : Fin d → ZMod M,
        if s + emb u ∈ A ∧ s + emb v ∈ A then (1 : ℝ) else 0 := by
    intro u v
    have h1 : ∀ x ∈ A,
        (∑ y ∈ A, if y - x = emb v - emb u then (1 : ℝ) else 0) =
        if x - emb u + emb v ∈ A then (1 : ℝ) else 0 := by
      intro x _
      have heq : ∀ y : Fin d → ZMod M, (y - x = emb v - emb u) ↔ y = x - emb u + emb v := by
        intro y
        constructor <;> intro h
        · calc y = (y - x) + x := by abel
            _ = (emb v - emb u) + x := by rw [h]
            _ = x - emb u + emb v := by abel
        · rw [h]; abel
      simp_rw [heq]
      simp [Finset.sum_ite_eq']
    rw [Finset.sum_congr rfl h1]
    have h2 : (∑ x ∈ A, if x - emb u + emb v ∈ A then (1 : ℝ) else 0) =
        ∑ x : Fin d → ZMod M, if x ∈ A ∧ x - emb u + emb v ∈ A then (1 : ℝ) else 0 := by
      rw [show A = Finset.univ.filter (fun x => x ∈ A) by ext x; simp, Finset.sum_filter]
      refine Finset.sum_congr rfl fun x _ => by split_ifs <;> simp_all
    rw [h2]
    refine Fintype.sum_equiv (Equiv.subRight (emb u)) _ _ fun x => ?_
    simp [Equiv.subRight_apply, sub_add_cancel]
  simp_rw [hemb_sub, hrewrite, Finset.mul_sum]
  have hswap :
      (∑ u ∈ U, ∑ v ∈ U, ∑ s : Fin d → ZMod M,
        Z u v * (if s + emb u ∈ A ∧ s + emb v ∈ A then (1 : ℝ) else 0)) =
      ∑ s : Fin d → ZMod M, ∑ u ∈ U, ∑ v ∈ U,
        Z u v * (if s + emb u ∈ A ∧ s + emb v ∈ A then (1 : ℝ) else 0) := by
    calc
      (∑ u ∈ U, ∑ v ∈ U, ∑ s : Fin d → ZMod M,
          Z u v * (if s + emb u ∈ A ∧ s + emb v ∈ A then (1 : ℝ) else 0))
          = ∑ u ∈ U, ∑ s : Fin d → ZMod M, ∑ v ∈ U,
              Z u v * (if s + emb u ∈ A ∧ s + emb v ∈ A then (1 : ℝ) else 0) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = ∑ s : Fin d → ZMod M, ∑ u ∈ U, ∑ v ∈ U,
            Z u v * (if s + emb u ∈ A ∧ s + emb v ∈ A then (1 : ℝ) else 0) := Finset.sum_comm
  rw [hswap]
  apply Finset.sum_nonneg
  intro s _
  let S : Finset (Fin d → ℤ) := U.filter (fun u => s + emb u ∈ A)
  have hS : S ⊆ U := Finset.filter_subset _ _
  have hEq :
      (∑ u ∈ U, ∑ v ∈ U, Z u v * (if s + emb u ∈ A ∧ s + emb v ∈ A then (1 : ℝ) else 0)) =
      ∑ u ∈ S, ∑ v ∈ S, Z u v := by
    simp only [S, Finset.sum_filter]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases hu : s + emb u ∈ A
    · simp only [hu, true_and, ↓reduceIte]
      refine Finset.sum_congr rfl fun v _ => by split_ifs <;> ring
    · simp only [hu, false_and, ↓reduceIte, mul_zero, Finset.sum_const_zero]
  rw [hEq]
  exact hZ S hS

theorem main : H1 → H2 → H3 → type_of% @Erdos704.erdos_704.variants.davies_lower := by
  classical
  intro h1 h2 h3 c hc
  filter_upwards [h1 c hc, eventually_ge_atTop 5] with d hPoly hd5
  intro k hcol
  obtain ⟨col⟩ := hcol
  have hkpos : 0 < k := by
    by_contra hk0
    have hk0' : k = 0 := by omega
    subst hk0'
    exact Fin.elim0 (col 0)
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  obtain ⟨P, B, hP0, hBpos, hBc, hPbound⟩ := hPoly
  have h1B : 0 < 1 + B := by linarith
  suffices hinv : (k : ℝ)⁻¹ ≤ B / (1 + B) by
    have hle : (1 + B) / B ≤ (k : ℝ) := by
      rw [div_le_iff₀ hBpos]
      have hmul := mul_le_mul_of_nonneg_left hinv (mul_pos hkR h1B).le
      field_simp [hkR.ne', h1B.ne'] at hmul
      linarith
    have h1div : 1 + 1 / B = (1 + B) / B := by field_simp [hBpos.ne']; ring
    linarith
  apply le_of_forall_pos_le_add
  intro δ hδ
  set ε : ℝ := δ / 2 with hεdef
  have hε : 0 < ε := by positivity
  obtain ⟨m, ℓ, U, Z, z₀, a, hmpos, hz₀lt, hBQC, hnorm, hrad⟩ :=
    h2 d hd5 P B hP0 hBpos hPbound ε hε
  have hdpos : 0 < d := by omega
  let w₀ : Fin d → ℤ := fun i => if i.val = 0 then (m : ℤ) else 0
  have hw₀_ne : w₀ ≠ 0 := by
    intro h0
    have := congrFun h0 ⟨0, hdpos⟩
    simp only [w₀, Pi.zero_apply, ↓reduceIte] at this
    exact (Nat.cast_ne_zero.mpr hmpos.ne') this
  have hw₀_norm : Real.sqrt (∑ i : Fin d, ((w₀ i : ℤ) : ℝ) ^ 2) = (m : ℝ) := by
    have hsq : ∑ i : Fin d, ((w₀ i : ℤ) : ℝ) ^ 2 = (m : ℝ) ^ 2 := by
      rw [Finset.sum_eq_single ⟨0, hdpos⟩]
      · simp [w₀]
      · intro i _ hi
        have hival : i.val ≠ 0 := fun h => hi (Fin.ext h)
        simp [w₀, hival]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [hsq, Real.sqrt_sq (Nat.cast_nonneg m)]
  let W : Finset (Fin d → ℤ) :=
    insert w₀ ((Finset.univ : Finset (Fin ℓ)).biUnion fun q =>
      (U q).biUnion fun u => ((U q).erase u).image fun v => v - u)
  have hWne : ∀ w ∈ W, w ≠ 0 := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw'
    · exact hw₀_ne
    · obtain ⟨q, _, h1⟩ := Finset.mem_biUnion.mp hw'
      obtain ⟨u, _, h2⟩ := Finset.mem_biUnion.mp h1
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h2
      exact sub_ne_zero.mpr (Finset.ne_of_mem_erase hv)
  let cInf : ℝ := z₀ - ∑ q : Fin ℓ, ∑ u ∈ U q, Z q u u
  let cw : (Fin d → ℤ) → ℝ := fun w =>
    (if w = w₀ then a else 0) -
      ∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ (U q).erase u, if v - u = w then Z q u v else 0
  have hsum_cw : ∀ f : (Fin d → ℤ) → ℝ,
      (∑ w ∈ W, cw w * f w) =
      a * f w₀ - ∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ (U q).erase u, Z q u v * f (v - u) := by
    intro f
    have hsub :
        (∑ w ∈ W, cw w * f w) =
        (∑ w ∈ W, (if w = w₀ then a else 0) * f w) -
        ∑ w ∈ W, (∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ (U q).erase u,
          if v - u = w then Z q u v else 0) * f w := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun w _ => sub_mul _ _ _
    rw [hsub]
    have hA : (∑ w ∈ W, (if w = w₀ then a else 0) * f w) = a * f w₀ := by
      rw [Finset.sum_eq_single w₀]
      · simp
      · intro w _ hw; simp [hw]
      · intro h; exact absurd (Finset.mem_insert_self _ _) h
    have hB :
        (∑ w ∈ W, (∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ (U q).erase u,
          if v - u = w then Z q u v else 0) * f w) =
        ∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ (U q).erase u, Z q u v * f (v - u) := by
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u hu => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun v hv => ?_
      have hmem : v - u ∈ W :=
        Finset.mem_insert_of_mem (Finset.mem_biUnion.mpr ⟨q, Finset.mem_univ _,
          Finset.mem_biUnion.mpr ⟨u, hu, Finset.mem_image.mpr ⟨v, hv, rfl⟩⟩⟩)
      rw [Finset.sum_eq_single (v - u)]
      · simp
      · intro w _ hw; simp [hw.symm]
      · intro h; exact absurd hmem h
    rw [hA, hB]
  have hradW : ∀ τ : ℝ, 0 ≤ τ →
      0 ≤ cInf + ∑ w ∈ W, cw w *
        ((∫ u in (-1 : ℝ)..1, Real.cos (2 * Real.pi *
            (Real.sqrt (∑ i : Fin d, ((w i : ℤ) : ℝ) ^ 2) * τ) * u) *
            (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2)) /
          (∫ u in (-1 : ℝ)..1, (1 - u ^ 2) ^ (((d : ℝ) - 3) / 2))) := by
    intro τ hτ
    rw [hsum_cw, hw₀_norm]
    have h := hrad τ hτ
    dsimp only [cInf] at h ⊢
    simp only [Pi.sub_apply]
    linarith
  obtain ⟨L, ι, Γ, neg, hLpos, hιpos, hneg_inv, hΓneg, hΓsim, htrans⟩ :=
    h3 d hd5 W cInf cw hWne hradW ε hε
  have hιR : (0 : ℝ) < ι := by exact_mod_cast hιpos
  have hmLR : (0 : ℝ) < (m : ℝ) * (L : ℝ) := by positivity
  -- Embed ℤ^d into ℝ^d via E(x) = (1 / (m * L)) • x
  let E : (Fin d → ℤ) → EuclideanSpace ℝ (Fin d) :=
    fun x => WithLp.toLp 2 fun i => ((x i : ℤ) : ℝ) / ((m : ℝ) * (L : ℝ))
  have hE_adj : ∀ (x : Fin d → ℤ) (t : Fin ι),
      (Erdos704.unitDistanceGraph d).Adj (E x) (E (x + (Γ t).mulVec w₀)) := by
    intro x t
    change dist (E x) (E (x + (Γ t).mulVec w₀)) = 1
    rw [EuclideanSpace.dist_eq]
    have hsub : ∑ i : Fin d, dist ((E x) i) ((E (x + (Γ t).mulVec w₀)) i) ^ 2 = 1 := by
      have hcoord : ∀ i : Fin d,
          dist ((E x) i) ((E (x + (Γ t).mulVec w₀)) i) ^ 2 =
          (((Γ t).mulVec w₀ i : ℤ) : ℝ) ^ 2 / ((m : ℝ) * (L : ℝ)) ^ 2 := by
        intro i
        rw [Real.dist_eq]
        change |((x i : ℤ) : ℝ) / ((m : ℝ) * (L : ℝ)) -
          (((x i + (Γ t).mulVec w₀ i : ℤ) : ℝ)) / ((m : ℝ) * (L : ℝ))| ^ 2 = _
        rw [sq_abs]
        push_cast
        ring
      simp_rw [hcoord, ← Finset.sum_div, hΓsim t w₀]
      have hw₀sq : ∑ i : Fin d, ((w₀ i : ℤ) : ℝ) ^ 2 = (m : ℝ) ^ 2 := by
        rw [← Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _), hw₀_norm]
      rw [hw₀sq]
      field_simp [hmLR.ne']
    rw [hsub, Real.sqrt_one]
  -- Choose ρ > |((Γ t).mulVec w₀ i)| for all t, i
  let ρ : ℕ := (∑ t : Fin ι, ∑ i : Fin d, ((Γ t).mulVec w₀ i).natAbs) + 1
  have hρ_gt : ∀ (t : Fin ι) (i : Fin d), ((Γ t).mulVec w₀ i).natAbs < ρ := by
    intro t i
    have h1 : ((Γ t).mulVec w₀ i).natAbs ≤ ∑ j : Fin d, ((Γ t).mulVec w₀ j).natAbs :=
      Finset.single_le_sum (f := fun j => ((Γ t).mulVec w₀ j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have h2 : (∑ j : Fin d, ((Γ t).mulVec w₀ j).natAbs) ≤
        ∑ s : Fin ι, ∑ j : Fin d, ((Γ s).mulVec w₀ j).natAbs :=
      Finset.single_le_sum (f := fun s => ∑ j : Fin d, ((Γ s).mulVec w₀ j).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
    omega
  -- Prove for every N : ℕ that ((2N+1) / (2N+1+2ρ))^d * k⁻¹ ≤ z₀ + ε
  have hbox : ∀ N : ℕ,
      (((2 * N + 1 : ℕ) : ℝ) / ((2 * N + 1 + 2 * ρ : ℕ) : ℝ)) ^ d * (k : ℝ)⁻¹ ≤ z₀ + ε := by
    intro N
    set M : ℕ := 2 * N + 1 + 2 * ρ with hMdef
    have hMpos : 0 < M := by omega
    have : NeZero M := ⟨hMpos.ne'⟩
    let QN : Finset (Fin d → ℤ) := Fintype.piFinset fun _ : Fin d => Finset.Icc (-(N : ℤ)) (N : ℤ)
    have hQN_card : QN.card = (2 * N + 1) ^ d := by
      simp only [QN, Fintype.card_piFinset, Int.card_Icc]
      have hlen : ((N : ℤ) + 1 + (N : ℤ)).toNat = 2 * N + 1 := by omega
      simp [hlen]
    -- Pigeonhole a color class A_N ⊆ Q_N with k * A_N.card ≥ (2N+1)^d
    have hpig : ∃ c₀ : Fin k, (2 * N + 1) ^ d ≤ k * (QN.filter fun x => col (E x) = c₀).card := by
      have hsum : ∑ c₀ : Fin k, (QN.filter fun x => col (E x) = c₀).card = QN.card := by
        rw [← Finset.card_biUnion]
        · congr 1; ext x; simp
        · intro a _ b _ hab
          exact Finset.disjoint_filter.mpr fun x _ ha hb => hab (ha.symm.trans hb)
      have hne_fin : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hkpos⟩, Finset.mem_univ _⟩
      obtain ⟨c₀, _, hc₀⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin k))
        (fun c₀ => (QN.filter fun x => col (E x) = c₀).card) hne_fin
      refine ⟨c₀, ?_⟩
      calc (2 * N + 1) ^ d = QN.card := hQN_card.symm
        _ = ∑ c₁ : Fin k, (QN.filter fun x => col (E x) = c₁).card := hsum.symm
        _ ≤ ∑ _ : Fin k, (QN.filter fun x => col (E x) = c₀).card :=
              Finset.sum_le_sum fun c₁ _ => hc₀ c₁ (Finset.mem_univ c₁)
        _ = k * (QN.filter fun x => col (E x) = c₀).card := by simp
    obtain ⟨c₀, hc₀⟩ := hpig
    set AN : Finset (Fin d → ℤ) := QN.filter fun x => col (E x) = c₀
    let modM : (Fin d → ℤ) → (Fin d → ZMod M) := fun x i => (x i : ZMod M)
    have hmod_inj : Set.InjOn modM (AN : Set (Fin d → ℤ)) := by
      intro x hx y hy hxy
      have hxQ : x ∈ QN := (Finset.mem_filter.mp hx).1
      have hyQ : y ∈ QN := (Finset.mem_filter.mp hy).1
      ext i
      have hxi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hxQ i)
      have hyi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hyQ i)
      have hmod := congrFun hxy i
      have hdvd : (M : ℤ) ∣ y i - x i :=
        (ZMod.intCast_eq_intCast_iff_dvd_sub (x i) (y i) M).mp hmod
      obtain ⟨q, hq⟩ := hdvd
      have hlt : |y i - x i| < (M : ℤ) := by
        rw [abs_lt]; constructor <;> omega
      have hq0 : q = 0 := by
        by_contra hqne
        have hq1 : 1 ≤ |q| := Int.one_le_abs hqne
        have h1 : (M : ℤ) ≤ |y i - x i| := by
          rw [hq, abs_mul, abs_of_pos (by exact_mod_cast hMpos : (0 : ℤ) < M)]
          nlinarith
        omega
      rw [hq0, mul_zero] at hq
      omega
    set Abar : Finset (Fin d → ZMod M) := AN.image modM
    have hAbar_card : Abar.card = AN.card := Finset.card_image_of_injOn hmod_inj
    have hAbar_pos : 0 < Abar.card := by
      rw [hAbar_card]
      by_contra h0
      have h0' : AN.card = 0 := by omega
      rw [h0', mul_zero] at hc₀
      have : 0 < (2 * N + 1) ^ d := by positivity
      omega
    -- No-wraparound independence in (ZMod M)^d for generators Γ_t w₀
    have hindep : ∀ x ∈ Abar, ∀ y ∈ Abar, ∀ t : Fin ι,
        y - x ≠ (fun i => ((Γ t).mulVec w₀ i : ZMod M)) := by
      intro x hx y hy t heq
      obtain ⟨x₀, hx₀, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨y₀, hy₀, rfl⟩ := Finset.mem_image.mp hy
      have hxQ := (Finset.mem_filter.mp hx₀).1
      have hyQ := (Finset.mem_filter.mp hy₀).1
      have hxC := (Finset.mem_filter.mp hx₀).2
      have hyC := (Finset.mem_filter.mp hy₀).2
      have hZeq : y₀ = x₀ + (Γ t).mulVec w₀ := by
        ext i
        have hxi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hxQ i)
        have hyi := Finset.mem_Icc.mp (Fintype.mem_piFinset.mp hyQ i)
        have hgi : |((Γ t).mulVec w₀ i)| < (ρ : ℤ) := by
          rw [← Int.natCast_natAbs]
          exact_mod_cast hρ_gt t i
        have hmod : ((y₀ i - x₀ i : ℤ) : ZMod M) = (((Γ t).mulVec w₀ i : ℤ) : ZMod M) := by
          have := congrFun heq i
          simpa [modM] using this
        have hdvd : (M : ℤ) ∣ ((Γ t).mulVec w₀ i) - (y₀ i - x₀ i) :=
          (ZMod.intCast_eq_intCast_iff_dvd_sub (y₀ i - x₀ i) ((Γ t).mulVec w₀ i) M).mp hmod
        obtain ⟨q, hq⟩ := hdvd
        have hlt : |((Γ t).mulVec w₀ i) - (y₀ i - x₀ i)| < (M : ℤ) := by
          rw [abs_lt] at hgi ⊢
          constructor <;> omega
        have hq0 : q = 0 := by
          by_contra hqne
          have hq1 : 1 ≤ |q| := Int.one_le_abs hqne
          have h1 : (M : ℤ) ≤ |((Γ t).mulVec w₀ i) - (y₀ i - x₀ i)| := by
            rw [hq, abs_mul, abs_of_pos (by exact_mod_cast hMpos : (0 : ℤ) < M)]
            nlinarith
          omega
        rw [hq0, mul_zero] at hq
        simp only [Pi.add_apply]
        omega
      have hadj := hE_adj x₀ t
      rw [← hZeq] at hadj
      exact col.valid hadj (hxC.trans hyC.symm)
    -- Define the quadratic form Q on Abar
    let pairCnt : (Fin d → ZMod M) → ℝ := fun v =>
      ∑ x ∈ Abar, ∑ y ∈ Abar, if y - x = v then (1 : ℝ) else 0
    let Q : ℝ :=
      (z₀ + ε) * (Abar.card : ℝ) +
      (1 / (ι : ℝ)) * (a * ∑ t : Fin ι, pairCnt (fun i => ((Γ t).mulVec w₀ i : ZMod M))) -
      (1 / (ι : ℝ)) * ∑ t : Fin ι, ∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ U q,
        Z q u v * pairCnt (fun i => ((Γ t).mulVec (v - u) i : ZMod M))
    -- 1. Upper bound: Q ≤ (z₀ + ε) * Abar.card
    have hQ_upper : Q ≤ (z₀ + ε) * (Abar.card : ℝ) := by
      have hgen0 : ∑ t : Fin ι, pairCnt (fun i => ((Γ t).mulVec w₀ i : ZMod M)) = 0 := by
        apply Finset.sum_eq_zero
        intro t _
        dsimp only [pairCnt]
        apply Finset.sum_eq_zero; intro x hx
        apply Finset.sum_eq_zero; intro y hy
        rw [if_neg (hindep x hx y hy t)]
      have hmat : 0 ≤ ∑ t : Fin ι, ∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ U q,
          Z q u v * pairCnt (fun i => ((Γ t).mulVec (v - u) i : ZMod M)) :=
        Finset.sum_nonneg fun t _ => Finset.sum_nonneg fun q _ =>
          bqc_translate_nonneg Abar (U q) (Z q) (hBQC q) (Γ t)
      have hterm3 : 0 ≤ (1 / (ι : ℝ)) * ∑ t : Fin ι, ∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ U q,
          Z q u v * pairCnt (fun i => ((Γ t).mulVec (v - u) i : ZMod M)) :=
        mul_nonneg (by positivity) hmat
      dsimp only [Q]
      rw [hgen0, mul_zero, mul_zero, add_zero]
      linarith
    -- 2. Lower bound: (Abar.card : ℝ)^2 / M^d ≤ Q via DFT
    have hQ_lower : (Abar.card : ℝ) ^ 2 / ((M : ℝ) ^ d) ≤ Q := by
      have hdiag : pairCnt 0 = (Abar.card : ℝ) := by
        dsimp only [pairCnt]
        have : ∀ x ∈ Abar, (∑ y ∈ Abar, if y - x = 0 then (1 : ℝ) else 0) = 1 := by
          intro x hx
          have heq : ∀ y : Fin d → ZMod M, (y - x = 0) ↔ y = x := fun y => sub_eq_zero
          simp_rw [heq]
          rw [Finset.sum_ite_eq' Abar x, if_pos hx]
        rw [Finset.sum_congr rfl this]
        simp
      have hQ_sep : Q =
          (cInf + ε) * pairCnt 0 +
          (1 / (ι : ℝ)) * ∑ t : Fin ι, ∑ w ∈ W,
            cw w * pairCnt (fun i => ((Γ t).mulVec w i : ZMod M)) := by
        have hsplit : ∀ t : Fin ι,
            (∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ U q,
              Z q u v * pairCnt (fun i => ((Γ t).mulVec (v - u) i : ZMod M))) =
            (∑ q : Fin ℓ, ∑ u ∈ U q, Z q u u) * pairCnt 0 +
            ∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ (U q).erase u,
              Z q u v * pairCnt (fun i => ((Γ t).mulVec (v - u) i : ZMod M)) := by
          intro t
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [Finset.sum_mul, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun u hu => ?_
          rw [← Finset.add_sum_erase _ _ hu]
          have h0vec : (fun i : Fin d => ((Γ t).mulVec (u - u) i : ZMod M)) = 0 := by
            ext i; simp [Matrix.mulVec_zero]
          rw [h0vec]
        have hWsum : ∀ t : Fin ι,
            (∑ w ∈ W, cw w * pairCnt (fun i => ((Γ t).mulVec w i : ZMod M))) =
            a * pairCnt (fun i => ((Γ t).mulVec w₀ i : ZMod M)) -
            ∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ (U q).erase u,
              Z q u v * pairCnt (fun i => ((Γ t).mulVec (v - u) i : ZMod M)) := fun t =>
          hsum_cw (fun w => pairCnt (fun i => ((Γ t).mulVec w i : ZMod M)))
        dsimp only [Q, cInf]
        simp_rw [hsplit, hWsum]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← Finset.mul_sum, hdiag]
        field_simp [hιR.ne']
        ring
      -- Convert Q to ℂ and apply pair_count_dft
      set hatA : (Fin d → ZMod M) → ℝ := fun w =>
        Complex.normSq (∑ x ∈ Abar, Complex.exp (2 * Real.pi * Complex.I *
          ∑ i : Fin d, ((x i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ)))
      set Kspec : (Fin d → ZMod M) → ℝ := fun w =>
        cInf + ε + (1 / (ι : ℝ)) * ∑ t : Fin ι, ∑ u ∈ W,
          cw u * Real.cos (2 * Real.pi *
            ∑ i : Fin d, (((Γ t).mulVec u i : ℤ) : ℝ) * (((w i).val : ℝ) / (M : ℝ)))
      have hQ_fourier : Q = (1 / ((M : ℝ) ^ d)) * ∑ w : Fin d → ZMod M, hatA w * Kspec w := by
        apply Complex.ofReal_injective
        rw [hQ_sep]
        push_cast
        have hdft : ∀ v : Fin d → ZMod M, ((pairCnt v : ℝ) : ℂ) =
            (1 / ((M : ℂ) ^ d)) * ∑ w : Fin d → ZMod M, (hatA w : ℂ) *
              starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I *
                ∑ i : Fin d, ((v i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ))) := fun v =>
          pair_count_dft Abar v
        rw [hdft 0]
        have hzero_star : ∀ w : Fin d → ZMod M,
            starRingEnd ℂ (Complex.exp (2 * Real.pi * Complex.I *
              ∑ i : Fin d, (((0 : Fin d → ZMod M) i).val : ℝ) * ((w i).val : ℝ) / (M : ℝ))) = 1 := by
          intro w; simp
        simp_rw [hzero_star, mul_one]
        have hW_dft :
            (∑ t : Fin ι, ∑ u ∈ W,
              (cw u : ℂ) * (pairCnt (fun i => ((Γ t).mulVec u i : ZMod M)) : ℂ)) =
            (1 / ((M : ℂ) ^ d)) * ∑ w : Fin d → ZMod M, (hatA w : ℂ) *
              (∑ t : Fin ι, ∑ u ∈ W, (cw u : ℂ) *
                (Real.cos (2 * Real.pi *
                  ∑ i : Fin d, (((Γ t).mulVec u i : ℤ) : ℝ) * (((w i).val : ℝ) / (M : ℝ))) : ℂ)) := by
          have hstep1 :
              (∑ t : Fin ι, ∑ u ∈ W,
                (cw u : ℂ) * (pairCnt (fun i => ((Γ t).mulVec u i : ZMod M)) : ℂ)) =
              ∑ u ∈ W, (cw u : ℂ) *
                ∑ t : Fin ι, (pairCnt (fun i => ((Γ t).mulVec u i : ZMod M)) : ℂ) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun u _ => (Finset.mul_sum _ _ _).symm
          rw [hstep1]
          have hstep2 : ∀ u ∈ W,
              (∑ t : Fin ι, (pairCnt (fun i => ((Γ t).mulVec u i : ZMod M)) : ℂ)) =
              (1 / ((M : ℂ) ^ d)) * ∑ w : Fin d → ZMod M, (hatA w : ℂ) *
                ((∑ t : Fin ι, Real.cos (2 * Real.pi *
                  ∑ i : Fin d, (((Γ t).mulVec u i : ℤ) : ℝ) * (((w i).val : ℝ) / (M : ℝ)))) : ℂ) := by
            intro u _
            simp_rw [hdft, ← Finset.mul_sum]
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun w _ => ?_
            rw [← Finset.mul_sum, re_sum_invol_cos Γ neg hneg_inv hΓneg u w]
          have hstep2' :
              (∑ u ∈ W, (cw u : ℂ) * ∑ t : Fin ι, (pairCnt (fun i => ((Γ t).mulVec u i : ZMod M)) : ℂ)) =
              ∑ u ∈ W, (cw u : ℂ) * ((1 / ((M : ℂ) ^ d)) * ∑ w : Fin d → ZMod M, (hatA w : ℂ) *
                ((∑ t : Fin ι, Real.cos (2 * Real.pi *
                  ∑ i : Fin d, (((Γ t).mulVec u i : ℤ) : ℝ) * (((w i).val : ℝ) / (M : ℝ)))) : ℂ)) :=
            Finset.sum_congr rfl fun u hu => by rw [hstep2 u hu]
          rw [hstep2']
          simp_rw [mul_left_comm (cw _ : ℂ) (1 / ((M : ℂ) ^ d)), ← Finset.mul_sum]
          congr 1
          simp_rw [Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun w _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun u _ => by ring
        rw [hW_dft]
        simp_rw [Kspec]
        push_cast
        rw [← mul_assoc, mul_comm ((cInf : ℂ) + ε) (1 / ((M : ℂ) ^ d)), mul_assoc,
          ← mul_assoc (1 / (ι : ℂ)), mul_comm (1 / (ι : ℂ)) (1 / ((M : ℂ) ^ d)),
          mul_assoc (1 / ((M : ℂ) ^ d)), ← mul_add, Finset.mul_sum, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun w _ => by ring
      rw [hQ_fourier]
      have hterm_nonneg : ∀ w : Fin d → ZMod M, 0 ≤ hatA w * Kspec w := by
        intro w
        apply mul_nonneg (Complex.normSq_nonneg _)
        exact (htrans (fun i => ((w i).val : ℝ) / (M : ℝ))).le
      have hsingle : hatA 0 * Kspec 0 ≤ ∑ w : Fin d → ZMod M, hatA w * Kspec w :=
        Finset.single_le_sum (fun w _ => hterm_nonneg w) (Finset.mem_univ 0)
      have hhat0 : hatA 0 = (Abar.card : ℝ) ^ 2 := by
        dsimp only [hatA]
        simp [sq]
      have hK0 : 1 ≤ Kspec 0 := by
        dsimp only [Kspec]
        have hcos0 : ∀ (t : Fin ι) (u : Fin d → ℤ),
            Real.cos (2 * Real.pi * ∑ i : Fin d, (((Γ t).mulVec u i : ℤ) : ℝ) *
              ((((0 : Fin d → ZMod M) i).val : ℝ) / (M : ℝ))) = 1 := by
          intro t u; simp
        simp_rw [hcos0, mul_one]
        have hsum1 : (∑ u ∈ W, cw u) =
            a - ∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ (U q).erase u, Z q u v := by
          simpa only [mul_one] using hsum_cw (fun _ => (1 : ℝ))
        simp_rw [hsum1]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hdiag_merge :
            (∑ q : Fin ℓ, ∑ u ∈ U q, Z q u u) +
            (∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ (U q).erase u, Z q u v) =
            ∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ U q, Z q u v := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun u hu => Finset.add_sum_erase _ _ hu
        have hcancel : (1 / (ι : ℝ)) * ((ι : ℝ) * (a - ∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ (U q).erase u, Z q u v)) =
            a - ∑ q : Fin ℓ, ∑ u ∈ U q, ∑ v ∈ (U q).erase u, Z q u v := by
          field_simp [hιR.ne']
        rw [hcancel]
        dsimp only [cInf]
        linarith
      calc (Abar.card : ℝ) ^ 2 / ((M : ℝ) ^ d)
          = (1 / ((M : ℝ) ^ d)) * ((Abar.card : ℝ) ^ 2 * 1) := by ring
        _ ≤ (1 / ((M : ℝ) ^ d)) * (hatA 0 * Kspec 0) := by
              rw [hhat0]
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hK0 (sq_nonneg _)) (by positivity)
        _ ≤ (1 / ((M : ℝ) ^ d)) * ∑ w : Fin d → ZMod M, hatA w * Kspec w :=
              mul_le_mul_of_nonneg_left hsingle (by positivity)
    -- 3. Combine upper and lower bounds
    have hAbar_ratio : (Abar.card : ℝ) / ((M : ℝ) ^ d) ≤ z₀ + ε := by
      have hAposR : (0 : ℝ) < Abar.card := by exact_mod_cast hAbar_pos
      have hchain : (Abar.card : ℝ) ^ 2 / ((M : ℝ) ^ d) ≤ (z₀ + ε) * (Abar.card : ℝ) :=
        hQ_lower.trans hQ_upper
      have hmul : (Abar.card : ℝ) * ((Abar.card : ℝ) / ((M : ℝ) ^ d)) ≤
          (Abar.card : ℝ) * (z₀ + ε) := by
        have hsq : (Abar.card : ℝ) * ((Abar.card : ℝ) / ((M : ℝ) ^ d)) =
            (Abar.card : ℝ) ^ 2 / ((M : ℝ) ^ d) := by ring
        linarith
      exact le_of_mul_le_mul_left hmul hAposR
    have hc₀R : ((2 * N + 1 : ℕ) : ℝ) ^ d / (k : ℝ) ≤ (Abar.card : ℝ) := by
      rw [div_le_iff₀ hkR, hAbar_card]
      have : ((2 * N + 1 : ℕ) : ℝ) ^ d ≤ (k : ℝ) * (AN.card : ℝ) := by exact_mod_cast hc₀
      linarith
    calc (((2 * N + 1 : ℕ) : ℝ) / ((M : ℕ) : ℝ)) ^ d * (k : ℝ)⁻¹
        = (((2 * N + 1 : ℕ) : ℝ) ^ d / (k : ℝ)) / ((M : ℝ) ^ d) := by
            rw [div_pow]; ring
      _ ≤ (Abar.card : ℝ) / ((M : ℝ) ^ d) :=
            div_le_div_of_nonneg_right hc₀R (by positivity)
      _ ≤ z₀ + ε := hAbar_ratio
  -- Take N → ∞ to conclude k⁻¹ ≤ z₀ + ε ≤ B / (1 + B) + δ
  have hlim : Tendsto
      (fun N : ℕ => (((2 * N + 1 : ℕ) : ℝ) / ((2 * N + 1 + 2 * ρ : ℕ) : ℝ)) ^ d * (k : ℝ)⁻¹)
      atTop (nhds (1 ^ d * (k : ℝ)⁻¹)) := by
    have hratio : Tendsto
        (fun N : ℕ => (((2 * N + 1 : ℕ) : ℝ) / ((2 * N + 1 + 2 * ρ : ℕ) : ℝ)))
        atTop (nhds 1) := by
      have h1 : Tendsto (fun N : ℕ => (2 * (ρ : ℝ)) / (2 * (N : ℝ) + 1)) atTop (nhds 0) := by
        have hden : Tendsto (fun N : ℕ => 2 * (N : ℝ) + 1) atTop atTop :=
          (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).atTop_add tendsto_const_nhds
        exact tendsto_const_nhds.div_atTop hden
      have h2 : Tendsto (fun N : ℕ => (1 + (2 * (ρ : ℝ)) / (2 * (N : ℝ) + 1))⁻¹) atTop (nhds (1 + 0)⁻¹) :=
        (tendsto_const_nhds.add h1).inv₀ (by norm_num)
      rw [add_zero, inv_one] at h2
      refine h2.congr fun N => ?_
      have hpos : (2 * (N : ℝ) + 1) ≠ 0 := by positivity
      have hpos2 : (2 * (N : ℝ) + 1 + 2 * (ρ : ℝ)) ≠ 0 := by positivity
      push_cast
      field_simp [hpos, hpos2]
    exact (hratio.pow d).mul_const _
  have hle_z : (k : ℝ)⁻¹ ≤ z₀ + ε := by
    have := le_of_tendsto hlim (Eventually.of_forall hbox)
    simpa using this
  linarith

end OMA.R_Erdos704_erdos_704_variants_davies_lower_R1
