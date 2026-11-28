import FormalConjectures.Wikipedia.LehmerMahlerMeasureProblem
import Mathlib

-- Reduction LehmerMahlerMeasureProblem.lehmer_mahler_measure_problem.variants.best.R1 of Lehmer's Mahler measure problem — best
-- Credit: @sun-jiao
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Reduction of Strong Lehmer's Conjecture to Smyth, Bounded-Degree, and High-Degree Self-Reciprocal Regimes

We reduce `mahlerMeasureZ lehmerPolynomial ≤ lehmerConstant` (that Lehmer's decic
`L(X) = X^10 + X^9 - X^7 - X^6 - X^5 - X^4 - X^3 + X + 1` achieves the minimum Mahler measure `> 1`
among all integer polynomials) to three classical regimes on monic irreducible polynomials:

* **Proved unconditionally in this reduction:**
  1. **Multiplicativity & leading-coefficient lower bounds:** Using the bridge to
     `Polynomial.mahlerMeasure`, `M(f * g) = M(f) * M(g)`, `1 ≤ M(f)` for `f ≠ 0`, and `2 ≤ M(f)`
     whenever `|f.leadingCoeff| ≥ 2`.
  2. **Strong-induction reduction to monic irreducibles of degree `≥ 2`:** Every `f : ℤ[X]` with
     `1 < M(f)` either satisfies `2 ≤ M(f)` or admits a monic irreducible factor `p : ℤ[X]` of
     degree `≥ 2` with `1 < M(p) ≤ M(f)` (monic linear `X + c` has `M = max 1 |c|`, hence either
     `1` or `≥ 2`).
  3. **Exact Zhukovsky localization `M(lehmerPolynomial) ≤ 6 / 5 < 13 / 10 ≤ M(X^3 - X - 1)`:**
     Factoring `L(z) = z^5 g(z + z⁻¹)` with `g(w) = w^5 + w^4 - 5w^3 - 5w^2 + 4w + 3`, intermediate
     value sign changes on `(-2, -3/2)`, `(-3/2, -1)`, `(-1, 0)`, `(0, 1)`, and `(2, 61/30)` split
     `L` over `ℂ[X]` into four unit-circle quadratics (`M = 1`) and one real-root quadratic with
     `M = (w₅ + √(w₅^2 - 4)) / 2 ≤ 6 / 5`, strictly below `M(X^3 - X - 1) ≥ 13 / 10`.
  4. **Elimination of odd-degree self-reciprocal irreducibles:** Any monic irreducible `p : ℤ[X]`
     of degree `≥ 2` with `p.reverse = p` has `Even p.natDegree` (odd degree forces `p(-1) = 0`,
     contradicting irreducibility).

* **Remaining hypotheses (`H1`, `H2`, `H3`):**
  - `H1` (**Smyth's theorem, 1971**): Monic irreducible non-reciprocal `p : ℤ[X]` (`p.reverse ≠ p`)
    with `1 < M(p)` satisfy `M(X^3 - X - 1) ≤ M(p)`.
  - `H2` (**Mossinghoff–Rhin–Wu bounded-degree theorem**): Monic irreducible even-degree
    self-reciprocal `p : ℤ[X]` with `2 ≤ p.natDegree ≤ 40` and `1 < M(p)` satisfy `M(L) ≤ M(p)`.
  - `H3` (**High-degree self-reciprocal Lehmer regime**): Monic irreducible even-degree
    self-reciprocal `p : ℤ[X]` with `42 ≤ p.natDegree` and `1 < M(p)` satisfy `M(L) ≤ M(p)`.
-/

namespace OMA.R_LehmerMahlerMeasureProblem_lehmer_mahler_measure_problem_variants_best_R1

open Polynomial

/-- Step 1 (Smyth 1971): Non-reciprocal monic irreducible polynomials in `ℤ[X]` with Mahler measure
`> 1` have Mahler measure at least `M(X^3 - X - 1)`. -/
def H1 : Prop :=
  ∀ p : ℤ[X], p.Monic → Irreducible p → 2 ≤ p.natDegree →
    1 < LehmerMahlerMeasureProblem.mahlerMeasureZ p → p.reverse ≠ p →
    LehmerMahlerMeasureProblem.mahlerMeasureZ (X ^ 3 - X - 1) ≤
      LehmerMahlerMeasureProblem.mahlerMeasureZ p

/-- Step 2 (Mossinghoff–Rhin–Wu finite regime): Even-degree self-reciprocal monic irreducible
polynomials in `ℤ[X]` of degree `2 ≤ d ≤ 40` with Mahler measure `> 1` have Mahler measure at least
`M(lehmerPolynomial)`. -/
def H2 : Prop :=
  ∀ p : ℤ[X], p.Monic → Irreducible p → Even p.natDegree →
    2 ≤ p.natDegree → p.natDegree ≤ 40 →
    1 < LehmerMahlerMeasureProblem.mahlerMeasureZ p → p.reverse = p →
    LehmerMahlerMeasureProblem.mahlerMeasureZ LehmerMahlerMeasureProblem.lehmerPolynomial ≤
      LehmerMahlerMeasureProblem.mahlerMeasureZ p

/-- Step 3 (High-degree self-reciprocal regime): Even-degree self-reciprocal monic irreducible
polynomials in `ℤ[X]` of degree `d ≥ 42` with Mahler measure `> 1` have Mahler measure at least
`M(lehmerPolynomial)`. -/
def H3 : Prop :=
  ∀ p : ℤ[X], p.Monic → Irreducible p → Even p.natDegree →
    42 ≤ p.natDegree →
    1 < LehmerMahlerMeasureProblem.mahlerMeasureZ p → p.reverse = p →
    LehmerMahlerMeasureProblem.mahlerMeasureZ LehmerMahlerMeasureProblem.lehmerPolynomial ≤
      LehmerMahlerMeasureProblem.mahlerMeasureZ p

section Proof

lemma bridge (f : ℤ[X]) :
    LehmerMahlerMeasureProblem.mahlerMeasureZ f = (f.map (Int.castRingHom ℂ)).mahlerMeasure := by
  rw [Polynomial.mahlerMeasure_eq_leadingCoeff_mul_prod_roots]
  rfl

lemma mahlerMeasureZ_mul (f g : ℤ[X]) :
    LehmerMahlerMeasureProblem.mahlerMeasureZ (f * g) =
      LehmerMahlerMeasureProblem.mahlerMeasureZ f *
        LehmerMahlerMeasureProblem.mahlerMeasureZ g := by
  rw [bridge, bridge, bridge, Polynomial.map_mul, Polynomial.mahlerMeasure_mul]

lemma mahlerMeasureZ_neg (f : ℤ[X]) :
    LehmerMahlerMeasureProblem.mahlerMeasureZ (-f) =
      LehmerMahlerMeasureProblem.mahlerMeasureZ f := by
  rw [show (-f : ℤ[X]) = C (-1 : ℤ) * f by simp, mahlerMeasureZ_mul, bridge (C (-1 : ℤ)),
    Polynomial.map_C, Polynomial.mahlerMeasure_const]
  simp

lemma norm_leadingCoeff_map_int (f : ℤ[X]) :
    ‖(f.map (Int.castRingHom ℂ)).leadingCoeff‖ = (|f.leadingCoeff| : ℝ) := by
  rw [leadingCoeff_map_of_injective (RingHom.injective_int (Int.castRingHom ℂ)),
    Int.coe_castRingHom, Complex.norm_intCast]

private lemma monic_eq_one_of_natDegree_eq_zero {R : Type*} [Semiring R] {p : R[X]}
    (hp : p.Monic) (h0 : p.natDegree = 0) : p = 1 := by
  rw [eq_C_of_natDegree_eq_zero h0, ← h0, ← leadingCoeff, hp.leadingCoeff, map_one]

lemma one_le_mahlerMeasureZ_of_ne_zero {f : ℤ[X]} (hf : f ≠ 0) :
    1 ≤ LehmerMahlerMeasureProblem.mahlerMeasureZ f := by
  rw [bridge]
  apply Polynomial.one_le_mahlerMeasure_of_one_le_norm_leadingCoeff
  rw [norm_leadingCoeff_map_int]
  exact_mod_cast Int.one_le_abs (leadingCoeff_ne_zero.mpr hf)

lemma two_le_mahlerMeasureZ_of_two_le_abs_leadingCoeff {f : ℤ[X]} (hlc : 2 ≤ |f.leadingCoeff|) :
    2 ≤ LehmerMahlerMeasureProblem.mahlerMeasureZ f := by
  rw [bridge]
  refine le_trans ?_ (Polynomial.leadingCoeff_le_mahlerMeasure _)
  rw [norm_leadingCoeff_map_int]
  exact_mod_cast hlc

/-- Every monic `f : ℤ[X]` with `1 < M(f)` either satisfies `2 ≤ M(f)` or admits a monic
irreducible factor `p : ℤ[X]` of degree `≥ 2` with `1 < M(p) ≤ M(f)`. -/
lemma monic_irreducible_factor_of_gt_one :
    ∀ {f : ℤ[X]}, f.Monic → 1 < LehmerMahlerMeasureProblem.mahlerMeasureZ f →
      2 ≤ LehmerMahlerMeasureProblem.mahlerMeasureZ f ∨
        ∃ p : ℤ[X], p.Monic ∧ Irreducible p ∧ 2 ≤ p.natDegree ∧
          1 < LehmerMahlerMeasureProblem.mahlerMeasureZ p ∧
          LehmerMahlerMeasureProblem.mahlerMeasureZ p ≤
            LehmerMahlerMeasureProblem.mahlerMeasureZ f := by
  suffices aux : ∀ d : ℕ, ∀ f : ℤ[X], f.natDegree = d → f.Monic →
      1 < LehmerMahlerMeasureProblem.mahlerMeasureZ f →
      2 ≤ LehmerMahlerMeasureProblem.mahlerMeasureZ f ∨
        ∃ p : ℤ[X], p.Monic ∧ Irreducible p ∧ 2 ≤ p.natDegree ∧
          1 < LehmerMahlerMeasureProblem.mahlerMeasureZ p ∧
          LehmerMahlerMeasureProblem.mahlerMeasureZ p ≤
            LehmerMahlerMeasureProblem.mahlerMeasureZ f by
    intro f hf hm
    exact aux f.natDegree f rfl hf hm
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro f hdeg hf hm
    by_cases hd0 : d = 0
    · subst hd0
      have hf1 : f = 1 := monic_eq_one_of_natDegree_eq_zero hf hdeg
      subst hf1
      rw [bridge, Polynomial.map_one, show (1 : ℂ[X]) = C 1 by simp,
        Polynomial.mahlerMeasure_const, norm_one] at hm
      linarith
    by_cases hd1 : d = 1
    · subst hd1
      have hlin : f = X + C (f.coeff 0) := hf.eq_X_add_C hdeg
      have hm_eq : LehmerMahlerMeasureProblem.mahlerMeasureZ f = max 1 (|f.coeff 0| : ℝ) := by
        conv_lhs => rw [bridge, hlin]
        rw [Polynomial.map_add, Polynomial.map_X, Polynomial.map_C,
          Int.coe_castRingHom, Polynomial.mahlerMeasure_X_add_C, Complex.norm_intCast]
      rw [hm_eq] at hm ⊢
      have habs : 2 ≤ |f.coeff 0| := by
        by_contra! hlt
        have hle1 : |f.coeff 0| ≤ 1 := by omega
        have hle1R : (|f.coeff 0| : ℝ) ≤ 1 := by exact_mod_cast hle1
        rw [max_eq_left hle1R] at hm
        linarith
      left
      exact le_trans (by exact_mod_cast habs : (2 : ℝ) ≤ (|f.coeff 0| : ℝ)) (le_max_right _ _)
    have hd2 : 2 ≤ f.natDegree := by omega
    by_cases hirr : Irreducible f
    · exact Or.inr ⟨f, hf, hirr, hd2, hm, le_rfl⟩
    · have hnotUnit : ¬ IsUnit f := by
        intro hu
        have := natDegree_eq_zero_of_isUnit hu
        omega
      rw [irreducible_iff, not_and_or, not_not] at hirr
      rcases hirr with hu | hnot_mul
      · exact (hnotUnit hu).elim
      push Not at hnot_mul
      obtain ⟨a, b, hab, hna, hnb⟩ := hnot_mul
      have hlc_prod : a.leadingCoeff * b.leadingCoeff = 1 := by
        rw [← leadingCoeff_mul, ← hab, hf.leadingCoeff]
      obtain ⟨a', b', ha'm, hb'm, hab', hna', hnb'⟩ :
          ∃ a' b' : ℤ[X], a'.Monic ∧ b'.Monic ∧ f = a' * b' ∧ ¬ IsUnit a' ∧ ¬ IsUnit b' := by
        rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hlc_prod with ⟨ha1, hb1⟩ | ⟨ha1, hb1⟩
        · exact ⟨a, b, ha1, hb1, hab, hna, hnb⟩
        · refine ⟨-a, -b, ?_, ?_, by rw [neg_mul_neg, hab],
            fun ⟨u, hu⟩ => hna ⟨-u, by simp [hu]⟩, fun ⟨u, hu⟩ => hnb ⟨-u, by simp [hu]⟩⟩
          · rw [Monic, leadingCoeff_neg, ha1, neg_neg]
          · rw [Monic, leadingCoeff_neg, hb1, neg_neg]
      have ha'deg_pos : 1 ≤ a'.natDegree := by
        by_contra! h0
        have eq0 : a'.natDegree = 0 := by omega
        exact hna' (monic_eq_one_of_natDegree_eq_zero ha'm eq0 ▸ isUnit_one)
      have hb'deg_pos : 1 ≤ b'.natDegree := by
        by_contra! h0
        have eq0 : b'.natDegree = 0 := by omega
        exact hnb' (monic_eq_one_of_natDegree_eq_zero hb'm eq0 ▸ isUnit_one)
      have hdeg_sum : f.natDegree = a'.natDegree + b'.natDegree := by
        rw [hab', ha'm.natDegree_mul hb'm]
      have ha'lt : a'.natDegree < d := by omega
      have hb'lt : b'.natDegree < d := by omega
      have hma1 : 1 ≤ LehmerMahlerMeasureProblem.mahlerMeasureZ a' :=
        one_le_mahlerMeasureZ_of_ne_zero ha'm.ne_zero
      have hmb1 : 1 ≤ LehmerMahlerMeasureProblem.mahlerMeasureZ b' :=
        one_le_mahlerMeasureZ_of_ne_zero hb'm.ne_zero
      have hm_prod : LehmerMahlerMeasureProblem.mahlerMeasureZ f =
          LehmerMahlerMeasureProblem.mahlerMeasureZ a' *
            LehmerMahlerMeasureProblem.mahlerMeasureZ b' := by
        rw [hab', mahlerMeasureZ_mul]
      have hgt : 1 < LehmerMahlerMeasureProblem.mahlerMeasureZ a' ∨
          1 < LehmerMahlerMeasureProblem.mahlerMeasureZ b' := by
        by_contra! hle
        have hle1 : LehmerMahlerMeasureProblem.mahlerMeasureZ a' *
            LehmerMahlerMeasureProblem.mahlerMeasureZ b' ≤ 1 :=
          mul_le_one₀ hle.1 (by linarith) hle.2
        linarith
      rcases hgt with hma_gt | hmb_gt
      · rcases ih a'.natDegree ha'lt a' rfl ha'm hma_gt with h2 | ⟨p, hp1, hp2, hp3, hp4, hp5⟩
        · left
          nlinarith
        · exact Or.inr ⟨p, hp1, hp2, hp3, hp4,
            by rw [hm_prod]; exact hp5.trans (le_mul_of_one_le_right (by linarith) hmb1)⟩
      · rcases ih b'.natDegree hb'lt b' rfl hb'm hmb_gt with h2 | ⟨p, hp1, hp2, hp3, hp4, hp5⟩
        · left
          nlinarith
        · exact Or.inr ⟨p, hp1, hp2, hp3, hp4,
            by rw [hm_prod]; exact hp5.trans (le_mul_of_one_le_left (by linarith) hma1)⟩

/-- Any monic irreducible `p : ℤ[X]` of degree `≥ 2` satisfying `p.reverse = p` has even degree. -/
lemma even_natDegree_of_monic_irreducible_reverse_eq {p : ℤ[X]}
    (hi : Irreducible p) (hd : 2 ≤ p.natDegree) (hrev : p.reverse = p) :
    Even p.natDegree := by
  by_contra hnotEven
  have hodd : Odd p.natDegree := Nat.not_even_iff_odd.mp hnotEven
  have hev := @eval₂_reverse_mul_pow _ _ _ _ (RingHom.id ℤ) (-1 : ℤ) ⟨-1, by norm_num, by norm_num⟩ p
  rw [hrev] at hev
  change eval (-1 : ℤ) p * (-1 : ℤ) ^ p.natDegree = eval (-1 : ℤ) p at hev
  rw [hodd.neg_one_pow] at hev
  have hroot : p.IsRoot (-1 : ℤ) := by
    rw [IsRoot.def]
    linarith
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hroot
  rcases hi.isUnit_or_isUnit hq with hu | hu
  · exact not_isUnit_X_sub_C (-1 : ℤ) hu
  · have hq0 : q.natDegree = 0 := natDegree_eq_zero_of_isUnit hu
    have hq_ne : q ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hq
      exact hi.ne_zero hq
    have hpdeg : p.natDegree = 1 := by
      rw [hq, (monic_X_sub_C (-1 : ℤ)).natDegree_mul' hq_ne, natDegree_X_sub_C, hq0]
    omega

/-- The plastic cubic `X^3 - X - 1` has Mahler measure at least `13 / 10`. -/
lemma thirteen_tenths_le_cubic :
    (13 / 10 : ℝ) ≤ LehmerMahlerMeasureProblem.mahlerMeasureZ (X ^ 3 - X - 1) := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 - x - 1) (Set.Icc (13 / 10) 2) := by fun_prop
  obtain ⟨ρ, hρ_mem, hρ_eq⟩ := intermediate_value_Icc (by norm_num : (13 / 10 : ℝ) ≤ 2) hcont
    (show (0 : ℝ) ∈ Set.Icc ((fun x : ℝ => x ^ 3 - x - 1) (13 / 10))
        ((fun x : ℝ => x ^ 3 - x - 1) 2) by norm_num)
  have hρ_lo : (13 / 10 : ℝ) ≤ ρ := hρ_mem.1
  let pC : ℂ[X] := (X ^ 3 - X - 1 : ℤ[X]).map (Int.castRingHom ℂ)
  have hpC_eq : pC = X ^ 3 - X - 1 := by simp [pC]
  have hpC_root : pC.IsRoot (ρ : ℂ) := by
    rw [IsRoot.def, hpC_eq]
    simp only [eval_sub, eval_pow, eval_X, eval_one]
    exact_mod_cast hρ_eq
  obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hpC_root
  have hpC_monic : pC.Monic := by
    rw [hpC_eq]
    monicity!
  have hq_monic : q.Monic := (monic_X_sub_C (ρ : ℂ)).of_mul_monic_left (hq ▸ hpC_monic)
  have hq_ge1 : 1 ≤ q.mahlerMeasure :=
    Polynomial.one_le_mahlerMeasure_of_one_le_norm_leadingCoeff
      (by rw [hq_monic.leadingCoeff, norm_one])
  rw [bridge]
  change (13 / 10 : ℝ) ≤ pC.mahlerMeasure
  rw [hq, Polynomial.mahlerMeasure_mul, Polynomial.mahlerMeasure_X_sub_C, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by linarith), max_eq_right (by linarith)]
  nlinarith

private lemma mahlerMeasure_quad_unit {w : ℝ} (hw : |w| ≤ 2) :
    (X ^ 2 - C (w : ℂ) * X + 1 : ℂ[X]).mahlerMeasure = 1 := by
  let s : ℝ := Real.sqrt (4 - w ^ 2)
  have hs_nonneg : 0 ≤ 4 - w ^ 2 := by nlinarith [abs_le.mp hw]
  have hs_sq : s ^ 2 = 4 - w ^ 2 := Real.sq_sqrt hs_nonneg
  let α : ℂ := ((w / 2 : ℝ) : ℂ) + ((s / 2 : ℝ) : ℂ) * Complex.I
  let β : ℂ := ((w / 2 : ℝ) : ℂ) - ((s / 2 : ℝ) : ℂ) * Complex.I
  have hsum : α + β = (w : ℂ) := by
    simp only [α, β]
    push_cast
    ring
  have hprod : α * β = 1 := by
    have h1 : α * β = (((w / 2) ^ 2 + (s / 2) ^ 2 : ℝ) : ℂ) := by
      simp only [α, β]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [h1]
    exact_mod_cast (show (w / 2) ^ 2 + (s / 2) ^ 2 = 1 by linarith [hs_sq])
  have hfac : (X ^ 2 - C (w : ℂ) * X + 1 : ℂ[X]) = (X - C α) * (X - C β) := by
    calc (X ^ 2 - C (w : ℂ) * X + 1 : ℂ[X])
        = X ^ 2 - C (α + β) * X + C (α * β) := by rw [hsum, hprod, map_one]
      _ = (X - C α) * (X - C β) := by simp only [map_add, map_mul]; ring
  have hnorm_α : ‖α‖ = 1 := by
    have hnsq : Complex.normSq α = 1 := by
      have hid : α = ⟨w / 2, s / 2⟩ := by
        apply Complex.ext <;> simp [α]
      rw [hid, Complex.normSq_mk]
      linarith [hs_sq]
    rw [Complex.norm_def, hnsq, Real.sqrt_one]
  have hnorm_β : ‖β‖ = 1 := by
    have hnsq : Complex.normSq β = 1 := by
      have hid : β = ⟨w / 2, -(s / 2)⟩ := by
        apply Complex.ext <;> simp [β]
      rw [hid, Complex.normSq_mk]
      linarith [hs_sq]
    rw [Complex.norm_def, hnsq, Real.sqrt_one]
  rw [hfac, Polynomial.mahlerMeasure_mul, Polynomial.mahlerMeasure_X_sub_C,
    Polynomial.mahlerMeasure_X_sub_C, hnorm_α, hnorm_β]
  norm_num

private lemma mahlerMeasure_quad_real {w : ℝ} (hw2 : 2 < w) (hw_ub : w ≤ 61 / 30) :
    (X ^ 2 - C (w : ℂ) * X + 1 : ℂ[X]).mahlerMeasure ≤ 6 / 5 := by
  let s : ℝ := Real.sqrt (w ^ 2 - 4)
  have hs_pos : 0 ≤ w ^ 2 - 4 := by nlinarith
  have hs_sq : s ^ 2 = w ^ 2 - 4 := Real.sq_sqrt hs_pos
  have hs_nn : 0 ≤ s := Real.sqrt_nonneg _
  have hs_ub : s ≤ 11 / 30 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by norm_num, ?_⟩
    nlinarith
  let r₁ : ℝ := (w + s) / 2
  let r₂ : ℝ := (w - s) / 2
  have hr₁_gt1 : 1 < r₁ := by dsimp only [r₁]; linarith
  have hr₁_ub : r₁ ≤ 6 / 5 := by dsimp only [r₁]; linarith
  have hr_prod : r₁ * r₂ = 1 := by
    dsimp only [r₁, r₂]
    linarith [hs_sq]
  have hr₂_pos : 0 < r₂ := by nlinarith
  have hr₂_le1 : r₂ ≤ 1 := by nlinarith
  have hfac : (X ^ 2 - C (w : ℂ) * X + 1 : ℂ[X]) = (X - C (r₁ : ℂ)) * (X - C (r₂ : ℂ)) := by
    have hsum : (r₁ : ℂ) + (r₂ : ℂ) = (w : ℂ) := by
      exact_mod_cast (show r₁ + r₂ = w by dsimp [r₁, r₂]; ring)
    have hmul : (r₁ : ℂ) * (r₂ : ℂ) = 1 := by exact_mod_cast hr_prod
    calc (X ^ 2 - C (w : ℂ) * X + 1 : ℂ[X])
        = X ^ 2 - C ((r₁ : ℂ) + (r₂ : ℂ)) * X + C ((r₁ : ℂ) * (r₂ : ℂ)) := by
          rw [hsum, hmul, map_one]
      _ = (X - C (r₁ : ℂ)) * (X - C (r₂ : ℂ)) := by simp only [map_add, map_mul]; ring
  rw [hfac, Polynomial.mahlerMeasure_mul, Polynomial.mahlerMeasure_X_sub_C,
    Polynomial.mahlerMeasure_X_sub_C, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos (by linarith), abs_of_pos hr₂_pos,
    max_eq_right hr₁_gt1.le, max_eq_left hr₂_le1, mul_one]
  exact hr₁_ub

/-- Lehmer's decic polynomial satisfies `M(lehmerPolynomial) ≤ 6 / 5`. -/
lemma lehmerPolynomial_le_six_fifths :
    LehmerMahlerMeasureProblem.mahlerMeasureZ LehmerMahlerMeasureProblem.lehmerPolynomial ≤
      6 / 5 := by
  let gfn (w : ℝ) : ℝ := w ^ 5 + w ^ 4 - 5 * w ^ 3 - 5 * w ^ 2 + 4 * w + 3
  have hcont : Continuous gfn := by fun_prop
  obtain ⟨w₁, hw₁_mem, hw₁⟩ := intermediate_value_Ioo (by norm_num : (-2 : ℝ) ≤ -3 / 2)
    hcont.continuousOn (show (0 : ℝ) ∈ Set.Ioo (gfn (-2)) (gfn (-3 / 2)) by norm_num [gfn])
  obtain ⟨w₂, hw₂_mem, hw₂⟩ := intermediate_value_Ioo' (by norm_num : (-3 / 2 : ℝ) ≤ -1)
    hcont.continuousOn (show (0 : ℝ) ∈ Set.Ioo (gfn (-1)) (gfn (-3 / 2)) by norm_num [gfn])
  obtain ⟨w₃, hw₃_mem, hw₃⟩ := intermediate_value_Ioo (by norm_num : (-1 : ℝ) ≤ 0)
    hcont.continuousOn (show (0 : ℝ) ∈ Set.Ioo (gfn (-1)) (gfn 0) by norm_num [gfn])
  obtain ⟨w₄, hw₄_mem, hw₄⟩ := intermediate_value_Ioo' (by norm_num : (0 : ℝ) ≤ 1)
    hcont.continuousOn (show (0 : ℝ) ∈ Set.Ioo (gfn 1) (gfn 0) by norm_num [gfn])
  obtain ⟨w₅, hw₅_mem, hw₅⟩ := intermediate_value_Ioo (by norm_num : (2 : ℝ) ≤ 61 / 30)
    hcont.continuousOn (show (0 : ℝ) ∈ Set.Ioo (gfn 2) (gfn (61 / 30)) by norm_num [gfn])
  let g : ℝ[X] := X ^ 5 + X ^ 4 - 5 * X ^ 3 - 5 * X ^ 2 + 4 * X + 3
  have hg_eval (x : ℝ) : g.eval x = gfn x := by
    simp [g, gfn]
  obtain ⟨q₁, hq₁⟩ := dvd_iff_isRoot.mpr (show g.IsRoot w₁ by rw [IsRoot.def, hg_eval]; exact hw₁)
  have hq₁_w (x : ℝ) (hx : gfn x = 0) (hne : x ≠ w₁) : q₁.IsRoot x := by
    have he := congrArg (eval x) hq₁
    rw [hg_eval, hx, eval_mul, eval_sub, eval_X, eval_C] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (sub_ne_zero.mpr hne)
  obtain ⟨q₂, hq₂⟩ := dvd_iff_isRoot.mpr (hq₁_w w₂ hw₂ (by linarith [hw₁_mem.2, hw₂_mem.1]))
  have hq₂_w (x : ℝ) (hx : gfn x = 0) (hne₁ : x ≠ w₁) (hne₂ : x ≠ w₂) : q₂.IsRoot x := by
    have he := congrArg (eval x) hq₂
    rw [IsRoot.def.mp (hq₁_w x hx hne₁), eval_mul, eval_sub, eval_X, eval_C] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (sub_ne_zero.mpr hne₂)
  obtain ⟨q₃, hq₃⟩ := dvd_iff_isRoot.mpr
    (hq₂_w w₃ hw₃ (by linarith [hw₁_mem.2, hw₃_mem.1]) (by linarith [hw₂_mem.2, hw₃_mem.1]))
  have hq₃_w (x : ℝ) (hx : gfn x = 0) (hne₁ : x ≠ w₁) (hne₂ : x ≠ w₂) (hne₃ : x ≠ w₃) :
      q₃.IsRoot x := by
    have he := congrArg (eval x) hq₃
    rw [IsRoot.def.mp (hq₂_w x hx hne₁ hne₂), eval_mul, eval_sub, eval_X, eval_C] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (sub_ne_zero.mpr hne₃)
  obtain ⟨q₄, hq₄⟩ := dvd_iff_isRoot.mpr
    (hq₃_w w₄ hw₄ (by linarith [hw₁_mem.2, hw₄_mem.1]) (by linarith [hw₂_mem.2, hw₄_mem.1])
      (by linarith [hw₃_mem.2, hw₄_mem.1]))
  have hq₄_w₅ : q₄.IsRoot w₅ := by
    have he := congrArg (eval w₅) hq₄
    have hr := hq₃_w w₅ hw₅ (by linarith [hw₁_mem.2, hw₅_mem.1])
      (by linarith [hw₂_mem.2, hw₅_mem.1]) (by linarith [hw₃_mem.2, hw₅_mem.1])
    rw [IsRoot.def.mp hr, eval_mul, eval_sub, eval_X, eval_C] at he
    exact (mul_eq_zero.mp he.symm).resolve_left (sub_ne_zero.mpr (by linarith [hw₄_mem.2, hw₅_mem.1]))
  obtain ⟨q₅, hq₅⟩ := dvd_iff_isRoot.mpr hq₄_w₅
  let P₅ : ℝ[X] := (X - C w₁) * (X - C w₂) * (X - C w₃) * (X - C w₄) * (X - C w₅)
  have hg_fac : g = P₅ * q₅ := by
    rw [hq₁, hq₂, hq₃, hq₄, hq₅]
    simp only [P₅]
    ring
  have hP₅_monic : P₅.Monic :=
    ((((monic_X_sub_C w₁).mul (monic_X_sub_C w₂)).mul (monic_X_sub_C w₃)).mul
      (monic_X_sub_C w₄)).mul (monic_X_sub_C w₅)
  have hP₅_deg : P₅.natDegree = 5 := by
    dsimp only [P₅]
    rw [((((monic_X_sub_C w₁).mul (monic_X_sub_C w₂)).mul (monic_X_sub_C w₃)).mul
        (monic_X_sub_C w₄)).natDegree_mul (monic_X_sub_C w₅),
      (((monic_X_sub_C w₁).mul (monic_X_sub_C w₂)).mul (monic_X_sub_C w₃)).natDegree_mul
        (monic_X_sub_C w₄),
      ((monic_X_sub_C w₁).mul (monic_X_sub_C w₂)).natDegree_mul (monic_X_sub_C w₃),
      (monic_X_sub_C w₁).natDegree_mul (monic_X_sub_C w₂)]
    simp
  have hg_monic : g.Monic := by
    dsimp only [g]
    monicity!
  have hg_deg : g.natDegree = 5 := by
    dsimp only [g]
    compute_degree!
  have hq₅_monic : q₅.Monic := hP₅_monic.of_mul_monic_left (hg_fac ▸ hg_monic)
  have hq₅_deg : q₅.natDegree = 0 := by
    have := hP₅_monic.natDegree_mul hq₅_monic
    rw [← hg_fac, hg_deg, hP₅_deg] at this
    omega
  have hq₅_one : q₅ = 1 := monic_eq_one_of_natDegree_eq_zero hq₅_monic hq₅_deg
  rw [hq₅_one, mul_one] at hg_fac
  have hg_complex (u : ℂ) :
      u ^ 5 + u ^ 4 - 5 * u ^ 3 - 5 * u ^ 2 + 4 * u + 3 =
        (u - (w₁ : ℂ)) * (u - (w₂ : ℂ)) * (u - (w₃ : ℂ)) * (u - (w₄ : ℂ)) * (u - (w₅ : ℂ)) := by
    have hmap := congrArg (fun p : ℝ[X] => (p.map (algebraMap ℝ ℂ)).eval u) hg_fac
    simpa [g, P₅] using hmap
  let Q (w : ℝ) : ℂ[X] := X ^ 2 - C (w : ℂ) * X + 1
  have hL_fac :
      LehmerMahlerMeasureProblem.lehmerPolynomial.map (Int.castRingHom ℂ) =
        Q w₁ * Q w₂ * Q w₃ * Q w₄ * Q w₅ := by
    apply Polynomial.funext
    intro z
    by_cases hz : z = 0
    · subst hz
      simp [LehmerMahlerMeasureProblem.lehmerPolynomial, Q]
    · simp only [LehmerMahlerMeasureProblem.lehmerPolynomial, Q, Polynomial.map_add,
        Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_one,
        eval_mul, eval_add, eval_sub, eval_pow, eval_X, eval_C, eval_one]
      have hquad (w : ℝ) : z ^ 2 - (w : ℂ) * z + 1 = z * ((z + z⁻¹) - (w : ℂ)) := by
        field_simp [hz]
        ring
      rw [hquad w₁, hquad w₂, hquad w₃, hquad w₄, hquad w₅]
      have hprod :
          z * (z + z⁻¹ - ↑w₁) * (z * (z + z⁻¹ - ↑w₂)) * (z * (z + z⁻¹ - ↑w₃)) *
              (z * (z + z⁻¹ - ↑w₄)) * (z * (z + z⁻¹ - ↑w₅)) =
            z ^ 5 * ((z + z⁻¹ - ↑w₁) * (z + z⁻¹ - ↑w₂) * (z + z⁻¹ - ↑w₃) *
              (z + z⁻¹ - ↑w₄) * (z + z⁻¹ - ↑w₅)) := by ring
      rw [hprod, ← hg_complex (z + z⁻¹)]
      field_simp [hz]
      ring
  rw [bridge, hL_fac, Polynomial.mahlerMeasure_mul, Polynomial.mahlerMeasure_mul,
    Polynomial.mahlerMeasure_mul, Polynomial.mahlerMeasure_mul]
  have hm₁ : (Q w₁).mahlerMeasure = 1 :=
    mahlerMeasure_quad_unit (abs_le.mpr ⟨by linarith [hw₁_mem.1], by linarith [hw₁_mem.2]⟩)
  have hm₂ : (Q w₂).mahlerMeasure = 1 :=
    mahlerMeasure_quad_unit (abs_le.mpr ⟨by linarith [hw₂_mem.1], by linarith [hw₂_mem.2]⟩)
  have hm₃ : (Q w₃).mahlerMeasure = 1 :=
    mahlerMeasure_quad_unit (abs_le.mpr ⟨by linarith [hw₃_mem.1], by linarith [hw₃_mem.2]⟩)
  have hm₄ : (Q w₄).mahlerMeasure = 1 :=
    mahlerMeasure_quad_unit (abs_le.mpr ⟨by linarith [hw₄_mem.1], by linarith [hw₄_mem.2]⟩)
  have hm₅ : (Q w₅).mahlerMeasure ≤ 6 / 5 :=
    mahlerMeasure_quad_real hw₅_mem.1 hw₅_mem.2.le
  rw [hm₁, hm₂, hm₃, hm₄]
  linarith

theorem main :
    H1 → H2 → H3 →
      type_of% @LehmerMahlerMeasureProblem.lehmer_mahler_measure_problem.variants.best := by
  intro h1 h2 h3
  unfold LehmerMahlerMeasureProblem.lehmerConstant
  apply le_csInf
  · refine ⟨2, C (2 : ℤ), ?_, ?_⟩
    · rw [bridge, Polynomial.map_C, Polynomial.mahlerMeasure_const]
      simp
    · rw [bridge, Polynomial.map_C, Polynomial.mahlerMeasure_const]
      simp
  · rintro m ⟨f, hf_gt, rfl⟩
    have hL_ub := lehmerPolynomial_le_six_fifths
    have hcub_lb := thirteen_tenths_le_cubic
    have hf_ne : f ≠ 0 := by
      intro h0
      rw [h0, bridge, Polynomial.map_zero, Polynomial.mahlerMeasure_zero] at hf_gt
      linarith
    by_cases hlc2 : 2 ≤ |f.leadingCoeff|
    · exact hL_ub.trans ((by norm_num : (6 / 5 : ℝ) ≤ 2).trans
        (two_le_mahlerMeasureZ_of_two_le_abs_leadingCoeff hlc2))
    have hlc_abs1 : |f.leadingCoeff| = 1 := by
      have hge1 : 1 ≤ |f.leadingCoeff| := Int.one_le_abs (leadingCoeff_ne_zero.mpr hf_ne)
      omega
    obtain ⟨g, hgm, hmg_eq⟩ :
        ∃ g : ℤ[X], g.Monic ∧
          LehmerMahlerMeasureProblem.mahlerMeasureZ g =
            LehmerMahlerMeasureProblem.mahlerMeasureZ f := by
      rcases abs_eq (by norm_num : (0 : ℤ) ≤ 1) |>.mp hlc_abs1 with h1' | hm1'
      · exact ⟨f, h1', rfl⟩
      · refine ⟨-f, ?_, mahlerMeasureZ_neg f⟩
        rw [Monic, leadingCoeff_neg, hm1', neg_neg]
    rw [← hmg_eq] at hf_gt ⊢
    rcases monic_irreducible_factor_of_gt_one hgm hf_gt with h2_le | ⟨p, hpm, hpi, hpd, hpgt, hple⟩
    · linarith
    by_cases hrev : p.reverse = p
    · have heven : Even p.natDegree := even_natDegree_of_monic_irreducible_reverse_eq hpi hpd hrev
      by_cases hd40 : p.natDegree ≤ 40
      · exact (h2 p hpm hpi heven hpd hd40 hpgt hrev).trans hple
      · have hd42 : 42 ≤ p.natDegree := by
          obtain ⟨k, hk⟩ := heven
          omega
        exact (h3 p hpm hpi heven hd42 hpgt hrev).trans hple
    · have hsmyth := h1 p hpm hpi hpd hpgt hrev
      linarith

end Proof

end OMA.R_LehmerMahlerMeasureProblem_lehmer_mahler_measure_problem_variants_best_R1
