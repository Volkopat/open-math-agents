import OMAReductions.R_PfisterPythagorasNumber_pfister_problem_variants_eq_two_pow_R1

-- Step PfisterPythagorasNumber.pfister_problem.variants.eq_two_pow.R1.H2: hypothesis H2 of reduction PfisterPythagorasNumber.pfister_problem.variants.eq_two_pow.R1
-- Credit: @lettucrisp
-- H2 := ∀ n : ℕ, ¬IsSumSqOfLength n (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ)     (1 + ∑ i, MvPolynomial.X i * MvPolynomial.X i))

namespace CasselsProof

open Polynomial Finset

/-- Clear a common denominator for a finite tuple in `FractionRing R`. -/
private lemma clear_denom {R : Type*} [CommRing R] [IsDomain R] {m : ℕ}
    (f : Fin m → FractionRing R) :
    ∃ (d : R) (p : Fin m → R), d ≠ 0 ∧
      ∀ i, algebraMap R (FractionRing R) d * f i = algebraMap R (FractionRing R) (p i) := by
  classical
  have hrep : ∀ i : Fin m, ∃ (n : R) (den : nonZeroDivisors R),
      algebraMap R (FractionRing R) (den : R) * f i = algebraMap R (FractionRing R) n := by
    intro i
    obtain ⟨⟨n, den⟩, h⟩ := IsLocalization.mk'_surjective (nonZeroDivisors R) (f i)
    refine ⟨n, den, ?_⟩
    rw [← h]; dsimp only; rw [IsLocalization.mk'_spec' (FractionRing R) n den]
  choose num den hspec using hrep
  refine ⟨∏ j : Fin m, (den j : R),
    fun i => (∏ j ∈ univ.erase i, (den j : R)) * num i, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun j _ => nonZeroDivisors.ne_zero (den j).2
  · intro i
    have hprod : (∏ j : Fin m, (den j : R)) =
        (∏ j ∈ univ.erase i, (den j : R)) * (den i : R) := by
      rw [mul_comm, Finset.mul_prod_erase Finset.univ (fun j => (den j : R)) (Finset.mem_univ i)]
    rw [hprod, map_mul, mul_assoc, hspec i, ← map_mul]

/-- A univariate real polynomial vanishing everywhere is zero. -/
private lemma real_poly_eq_zero_of_eval_eq_zero (p : ℝ[X]) (h : ∀ x : ℝ, p.eval x = 0) : p = 0 := by
  by_contra hp
  have hcard : (Finset.range (p.natDegree + 1)).card ≤ p.roots.toFinset.card := by
    have hinj : Function.Injective (fun n : ℕ => (n : ℝ)) := Nat.cast_injective
    have hsub : (Finset.range (p.natDegree + 1)).image (fun n : ℕ => (n : ℝ)) ⊆ p.roots.toFinset := by
      intro x hx
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hp]
      exact h x
    calc (Finset.range (p.natDegree + 1)).card
        = ((Finset.range (p.natDegree + 1)).image (fun n : ℕ => (n : ℝ))).card :=
          (Finset.card_image_of_injective _ hinj).symm
      _ ≤ p.roots.toFinset.card := Finset.card_le_card hsub
  have hle : p.roots.toFinset.card ≤ p.natDegree :=
    le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' p)
  simp only [Finset.card_range] at hcard
  omega

/-- A multivariate real polynomial vanishing everywhere is zero. -/
private lemma mvPoly_eq_zero_of_eval_eq_zero :
    ∀ {k : ℕ} (p : MvPolynomial (Fin k) ℝ), (∀ x : Fin k → ℝ, MvPolynomial.eval x p = 0) → p = 0
  | 0, p, h => by
    have h0 : MvPolynomial.eval (fun i : Fin 0 => i.elim0) p = 0 := h _
    have hp : p = MvPolynomial.C (MvPolynomial.eval (fun i : Fin 0 => i.elim0) p) := by
      ext m
      have hm : m = 0 := Finsupp.ext fun i => i.elim0
      subst hm
      rw [MvPolynomial.coeff_C, if_pos rfl, MvPolynomial.eval_eq']
      rw [Finset.sum_eq_single (0 : Fin 0 →₀ ℕ)]
      · simp
      · intro b _ hb
        exact (hb (Finsupp.ext fun i => i.elim0)).elim
      · intro hnot
        simp [MvPolynomial.notMem_support_iff.mp hnot]
    rw [hp, h0, map_zero]
  | k + 1, p, h => by
    let q : Polynomial (MvPolynomial (Fin k) ℝ) := MvPolynomial.finSuccEquiv ℝ k p
    have hq : q = 0 := by
      apply Polynomial.ext
      intro d
      simp only [Polynomial.coeff_zero]
      apply mvPoly_eq_zero_of_eval_eq_zero (q.coeff d)
      intro x
      have hmap : q.map (MvPolynomial.eval x) = 0 := by
        apply real_poly_eq_zero_of_eval_eq_zero
        intro t
        have hev : (q.map (MvPolynomial.eval x)).eval t = MvPolynomial.eval (Fin.cons t x) p := by
          exact (MvPolynomial.eval_eq_eval_mv_eval' x t p).symm
        rw [hev]
        exact h (Fin.cons t x)
      have hc := congr_arg (fun r : ℝ[X] => r.coeff d) hmap
      simpa [Polynomial.coeff_map] using hc
    exact (MvPolynomial.finSuccEquiv ℝ k).injective (by simpa [q] using hq)

/-- Sums of squares in `MvPolynomial (Fin k) ℝ` are anisotropic. -/
private lemma anisotropic_mvPoly (k : ℕ) {m : ℕ} (p : Fin m → MvPolynomial (Fin k) ℝ)
    (h : ∑ i, p i ^ 2 = 0) : ∀ i, p i = 0 := by
  intro i
  apply mvPoly_eq_zero_of_eval_eq_zero
  intro x
  have hx : ∑ j : Fin m, (MvPolynomial.eval x (p j)) ^ 2 = 0 := by
    have := congr_arg (MvPolynomial.eval x) h
    simpa [map_sum, map_pow] using this
  have hsq : (MvPolynomial.eval x (p i)) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp hx i (Finset.mem_univ i)
  exact sq_eq_zero_iff.mp hsq

/-- Sums of squares in `MvRatFunc (Fin k) ℝ` are anisotropic. -/
private lemma anisotropic_mvRatFunc (k : ℕ) {m : ℕ} (f : Fin m → MvRatFunc (Fin k) ℝ)
    (h : ∑ i, f i ^ 2 = 0) : ∀ i, f i = 0 := by
  obtain ⟨d, p, hd, hspec⟩ := clear_denom f
  have hsum : ∑ i, p i ^ 2 = 0 := by
    apply IsFractionRing.injective (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ)
    rw [map_sum, map_zero]
    have hrewrite :
        ∑ i, algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) (p i ^ 2) =
        algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) d ^ 2 * ∑ i, f i ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_pow, ← hspec i, mul_pow]
    rw [hrewrite, h, mul_zero]
  have hp0 := anisotropic_mvPoly k p hsum
  intro i
  have hd_ne : algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) d ≠ 0 := by
    intro h0
    apply hd
    exact IsFractionRing.injective (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) (by simpa using h0)
  have hmul : algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ) d * f i = 0 := by
    rw [hspec i, hp0 i, map_zero]
  exact (mul_eq_zero.mp hmul).resolve_left hd_ne

/-- Over an anisotropic field `K`, the `2 * D`-th coefficient of a sum of squares of polynomials
with `natDegree ≤ D` is the sum of squares of their `D`-th coefficients. -/
private lemma coeff_two_mul_sq_of_natDegree_le {K : Type*} [Field K] {r : K[X]} {D : ℕ}
    (hr : r.natDegree ≤ D) : (r ^ 2).coeff (2 * D) = (r.coeff D) ^ 2 := by
  rw [sq, sq, Polynomial.coeff_mul, Finset.sum_eq_single (D, D)]
  · intro x hx hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hx
    by_cases h1 : D < x.1
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hr h1), zero_mul]
    · have h2 : D < x.2 := by
        by_contra h2'
        apply hne
        ext <;> omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hr h2), mul_zero]
  · intro hnot
    exfalso
    apply hnot
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    omega

/-- Over an anisotropic field, a nontrivial sum of squares of polynomials is nonzero and has
`natDegree = 2 * max_i (p i).natDegree`. -/
private lemma sum_sq_ne_zero_and_natDegree {K : Type*} [Field K]
    (haniso : ∀ {m : ℕ} (v : Fin m → K), ∑ i, v i ^ 2 = 0 → ∀ i, v i = 0)
    {m : ℕ} (p : Fin m → K[X]) (hne : ∃ i, p i ≠ 0) :
    let D := Finset.univ.sup (fun i => (p i).natDegree)
    (∑ i, p i ^ 2) ≠ 0 ∧ (∑ i, p i ^ 2).natDegree = 2 * D := by
  intro D
  have hle_D : ∀ i, (p i).natDegree ≤ D := fun i => Finset.le_sup (f := fun j => (p j).natDegree) (Finset.mem_univ i)
  have hcoeff : (∑ i, p i ^ 2).coeff (2 * D) = ∑ i, ((p i).coeff D) ^ 2 := by
    rw [Polynomial.finsetSum_coeff]
    exact Finset.sum_congr rfl fun i _ => coeff_two_mul_sq_of_natDegree_le (hle_D i)
  have hcoeff_ne : (∑ i, p i ^ 2).coeff (2 * D) ≠ 0 := by
    rw [hcoeff]
    intro hzero
    have hall := haniso (fun i => (p i).coeff D) hzero
    obtain ⟨i₀, hi₀⟩ := hne
    by_cases hD : D = 0
    · have hd0 : (p i₀).natDegree = 0 := Nat.eq_zero_of_le_zero (hD ▸ hle_D i₀)
      have hlc : (p i₀).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hi₀
      rw [Polynomial.leadingCoeff, hd0, ← hD] at hlc
      exact hlc (hall i₀)
    · have huniv : (Finset.univ : Finset (Fin m)).Nonempty := ⟨i₀, Finset.mem_univ i₀⟩
      obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ huniv (fun i => (p i).natDegree)
      have hj_ne : p j ≠ 0 := by
        intro hpj
        rw [hpj, Polynomial.natDegree_zero] at hj
        exact hD hj
      have hlc : (p j).leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hj_ne
      rw [Polynomial.leadingCoeff, ← hj] at hlc
      exact hlc (hall j)
  have hsum_ne : (∑ i, p i ^ 2) ≠ 0 := by
    intro h0
    rw [h0, Polynomial.coeff_zero] at hcoeff_ne
    exact hcoeff_ne rfl
  refine ⟨hsum_ne, le_antisymm ?_ (Polynomial.le_natDegree_of_ne_zero hcoeff_ne)⟩
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  calc (p i ^ 2).natDegree ≤ 2 * (p i).natDegree := Polynomial.natDegree_pow_le
    _ ≤ 2 * D := Nat.mul_le_mul_left 2 (hle_D i)

/-- Cassels' Lemma (1964): over an anisotropic field `K`, if `f ∈ K[X]` satisfies
`f * q^2 = ∑ p_i^2` with `q ≠ 0`, then `f = ∑ r_i^2` in `K[X]`. -/
private lemma cassels_lemma {K : Type*} [Field K]
    (haniso : ∀ {m : ℕ} (v : Fin m → K), ∑ i, v i ^ 2 = 0 → ∀ i, v i = 0)
    {m : ℕ} (f : K[X]) :
    ∀ (d : ℕ) (q : K[X]) (p : Fin m → K[X]),
      q ≠ 0 → q.natDegree ≤ d → f * q ^ 2 = ∑ i, p i ^ 2 →
      ∃ r : Fin m → K[X], f = ∑ i, r i ^ 2 := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro q p hq hqd hfq
    by_cases hdeg0 : q.natDegree = 0
    · set c₀ : K := q.coeff 0
      have hqC : q = Polynomial.C c₀ := Polynomial.eq_C_of_natDegree_eq_zero hdeg0
      have hc0 : c₀ ≠ 0 := by
        intro hc
        apply hq
        rw [hqC, hc, map_zero]
      refine ⟨fun i => Polynomial.C c₀⁻¹ * p i, ?_⟩
      have h1 : ∑ i, (Polynomial.C c₀⁻¹ * p i) ^ 2 =
          Polynomial.C (c₀⁻¹ ^ 2) * ∑ i, p i ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_pow, map_pow]
      rw [h1, ← hfq, hqC, ← map_pow, mul_left_comm, ← map_mul]
      have hinv : c₀⁻¹ ^ 2 * c₀ ^ 2 = 1 := by
        rw [← mul_pow, inv_mul_cancel₀ hc0, one_pow]
      rw [hinv, map_one, mul_one]
    · have hqpos : 0 < q.natDegree := Nat.pos_of_ne_zero hdeg0
      let g : Fin m → K[X] := fun i => p i / q
      let r : Fin m → K[X] := fun i => p i % q
      have hdiv : ∀ i, p i = q * g i + r i := fun i => (EuclideanDomain.div_add_mod (p i) q).symm
      by_cases hall0 : ∀ i, r i = 0
      · refine ⟨g, ?_⟩
        have hq2 : q ^ 2 ≠ 0 := pow_ne_zero 2 hq
        apply mul_right_cancel₀ hq2
        rw [hfq, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hdiv i, hall0 i, add_zero, mul_comm q (g i), mul_pow]
      · push Not at hall0
        have hr_deg : ∀ i, (r i).natDegree < q.natDegree := by
          intro i
          by_cases hri : r i = 0
          · rw [hri, Polynomial.natDegree_zero]
            exact hqpos
          · have hlt := Polynomial.degree_mod_lt (p i) hq
            rwa [Polynomial.degree_eq_natDegree hri, Polynomial.degree_eq_natDegree hq,
              Nat.cast_lt] at hlt
        obtain ⟨hS_ne, hS_deg⟩ := sum_sq_ne_zero_and_natDegree haniso r hall0
        let D := Finset.univ.sup (fun i => (r i).natDegree)
        have hD_lt : D < q.natDegree := by
          obtain ⟨i₀, _⟩ := hall0
          obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨i₀, Finset.mem_univ i₀⟩
            (fun i => (r i).natDegree)
          rw [show D = (r j).natDegree from hj]; exact hr_deg j
        -- Cassels reflection
        let A : K[X] := (∑ i, g i ^ 2) - f
        let B : K[X] := (∑ i, p i * g i) - f * q
        let q₁ : K[X] := q * A - 2 * B
        let p₁ : Fin m → K[X] := fun i => A * p i - 2 * B * g i
        have hS_eq : ∑ i, r i ^ 2 = q * q₁ := by
          have hr_sub : ∀ i, r i = p i - q * g i := fun i => by
            have := hdiv i
            linear_combination -this
          have hexp : ∑ i, r i ^ 2 =
              (∑ i, p i ^ 2) - 2 * q * (∑ i, p i * g i) + q ^ 2 * (∑ i, g i ^ 2) := by
            calc ∑ i, r i ^ 2
                = ∑ i, (p i ^ 2 - 2 * q * (p i * g i) + q ^ 2 * g i ^ 2) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  rw [hr_sub i]; ring
              _ = (∑ i, p i ^ 2) - ∑ i, 2 * q * (p i * g i) + ∑ i, q ^ 2 * g i ^ 2 := by
                  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              _ = (∑ i, p i ^ 2) - 2 * q * (∑ i, p i * g i) + q ^ 2 * (∑ i, g i ^ 2) := by
                  rw [← Finset.mul_sum, ← Finset.mul_sum]
          rw [hexp, ← hfq]
          simp only [q₁, A, B]
          ring
        have hq₁_ne : q₁ ≠ 0 := by
          intro h0
          rw [h0, mul_zero] at hS_eq
          exact hS_ne hS_eq
        have hq₁_deg : q₁.natDegree < q.natDegree := by
          have hmul_deg : (q * q₁).natDegree = q.natDegree + q₁.natDegree :=
            Polynomial.natDegree_mul hq hq₁_ne
          rw [← hS_eq, hS_deg] at hmul_deg
          omega
        have hfq₁ : f * q₁ ^ 2 = ∑ i, p₁ i ^ 2 := by
          have hexp : ∑ i, p₁ i ^ 2 =
              A ^ 2 * (∑ i, p i ^ 2) - 4 * A * B * (∑ i, p i * g i) +
                4 * B ^ 2 * (∑ i, g i ^ 2) := by
            calc ∑ i, p₁ i ^ 2
                = ∑ i, (A ^ 2 * p i ^ 2 - 4 * A * B * (p i * g i) + 4 * B ^ 2 * g i ^ 2) := by
                  refine Finset.sum_congr rfl fun i _ => ?_
                  simp only [p₁]; ring
              _ = (∑ i, A ^ 2 * p i ^ 2) - (∑ i, 4 * A * B * (p i * g i)) +
                    (∑ i, 4 * B ^ 2 * g i ^ 2) := by
                  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
              _ = A ^ 2 * (∑ i, p i ^ 2) - 4 * A * B * (∑ i, p i * g i) +
                    4 * B ^ 2 * (∑ i, g i ^ 2) := by
                  rw [← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
          rw [hexp, ← hfq]
          have hpg : ∑ i, p i * g i = B + f * q := by simp only [B]; ring
          have hgg : ∑ i, g i ^ 2 = A + f := by simp only [A]; ring
          rw [hpg, hgg]
          simp only [q₁]
          ring
        exact ih q₁.natDegree (lt_of_lt_of_le hq₁_deg hqd) q₁ p₁ hq₁_ne le_rfl hfq₁

/-- Variable-adjunction step: if `c` is not a sum of `m` squares in an anisotropic field `K`
of characteristic zero, then `C c + X^2` is not a sum of `m + 1` squares in `K[X]`. -/
private lemma not_sum_sq_poly_add_X_sq {K : Type*} [Field K] [CharZero K]
    (haniso : ∀ {m : ℕ} (v : Fin m → K), ∑ i, v i ^ 2 = 0 → ∀ i, v i = 0)
    {m : ℕ} {c : K} (hc : ¬ IsSumSqOfLength m c) :
    ¬ ∃ p : Fin (m + 1) → K[X], Polynomial.C c + Polynomial.X ^ 2 = ∑ i, p i ^ 2 := by
  rintro ⟨p, hp⟩
  have hne : ∃ i, p i ≠ 0 := by
    by_contra h0
    push Not at h0
    have hsum0 : (∑ i, p i ^ 2) = 0 := Finset.sum_eq_zero fun i _ => by rw [h0 i]; ring
    rw [hsum0] at hp
    have hcoeff2 := congr_arg (fun r : K[X] => r.coeff 2) hp
    simp [Polynomial.coeff_X_pow] at hcoeff2
  obtain ⟨_, hdeg⟩ := sum_sq_ne_zero_and_natDegree haniso p hne
  have hdeg_lhs : (Polynomial.C c + Polynomial.X ^ 2 : K[X]).natDegree = 2 := by
    have hCdeg : (Polynomial.C c : K[X]).natDegree < (Polynomial.X ^ 2 : K[X]).natDegree := by
      simp [Polynomial.natDegree_C]
    rw [add_comm, Polynomial.natDegree_add_eq_left_of_natDegree_lt hCdeg,
      Polynomial.natDegree_X_pow]
  rw [← hp, hdeg_lhs] at hdeg
  have hdeg_le : ∀ i, (p i).natDegree ≤ 1 := fun i => by
    have hi : (p i).natDegree ≤ Finset.univ.sup (fun j => (p j).natDegree) :=
      Finset.le_sup (f := fun j => (p j).natDegree) (Finset.mem_univ i)
    omega
  have hp0_lin : p 0 = Polynomial.C ((p 0).coeff 1) * Polynomial.X +
      Polynomial.C ((p 0).coeff 0) := by
    ext n
    rcases n with _ | _ | n
    · simp
    · simp
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by have := hdeg_le 0; omega)]
      simp
  set a : K := (p 0).coeff 1
  set b : K := (p 0).coeff 0
  have heval0 : ∃ t : K, ((p 0).eval t) ^ 2 = t ^ 2 := by
    by_cases ha : a = 1
    · refine ⟨-b / 2, ?_⟩
      rw [hp0_lin, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_C, ha]
      have h2 : (2 : K) ≠ 0 := by norm_num
      field_simp [h2]
      ring
    · refine ⟨b / (1 - a), ?_⟩
      rw [hp0_lin, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_X, Polynomial.eval_C]
      have h1a : (1 - a : K) ≠ 0 := sub_ne_zero.mpr (Ne.symm ha)
      field_simp [h1a]
      ring
  obtain ⟨t, ht⟩ := heval0
  have hev : c + t ^ 2 = ((p 0).eval t) ^ 2 + ∑ i : Fin m, ((p i.succ).eval t) ^ 2 := by
    have := congr_arg (Polynomial.eval t) hp
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_finsetSum] at this
    rw [Fin.sum_univ_succ] at this
    exact this
  rw [ht] at hev
  apply hc
  refine ⟨fun i => (p i.succ).eval t, ?_⟩
  have hcancel : c = ∑ i : Fin m, ((p i.succ).eval t) ^ 2 := by
    linear_combination hev
  simpa [sq] using hcancel

/-- The Cassels theorem for `n` variables by induction on `n`. -/
private theorem cassels :
    ∀ n : ℕ, ¬ IsSumSqOfLength n (algebraMap (MvPolynomial (Fin n) ℝ) (MvRatFunc (Fin n) ℝ)
      (1 + ∑ i, MvPolynomial.X i * MvPolynomial.X i))
  | 0 => by
    rintro ⟨f, hf⟩
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, map_one] at hf
    exact one_ne_zero hf
  | k + 1 => by
    intro hsum
    have ih := cassels k
    set K := MvRatFunc (Fin k) ℝ
    set ιK : MvPolynomial (Fin k) ℝ →+* K :=
      algebraMap (MvPolynomial (Fin k) ℝ) (MvRatFunc (Fin k) ℝ)
    set ιKX : K[X] →+* FractionRing K[X] := algebraMap K[X] (FractionRing K[X])
    -- Build the injective ring homomorphism MvPolynomial (Fin (k+1)) ℝ →+* FractionRing K[X]
    let e := MvPolynomial.finSuccEquiv ℝ k
    let φPoly : MvPolynomial (Fin (k + 1)) ℝ →+* K[X] :=
      (Polynomial.mapRingHom ιK).comp e.toAlgHom.toRingHom
    have hφPoly_inj : Function.Injective φPoly := by
      have hιK_inj : Function.Injective ιK :=
        IsFractionRing.injective (MvPolynomial (Fin k) ℝ) K
      exact (Polynomial.map_injective ιK hιK_inj).comp e.injective
    let φ : MvPolynomial (Fin (k + 1)) ℝ →+* FractionRing K[X] := ιKX.comp φPoly
    have hφ_inj : Function.Injective φ :=
      (IsFractionRing.injective K[X] (FractionRing K[X])).comp hφPoly_inj
    let Φ : MvRatFunc (Fin (k + 1)) ℝ →+* FractionRing K[X] :=
      IsFractionRing.lift hφ_inj
    -- Compute the image of 1 + ∑ i : Fin (k+1), X i * X i under φPoly
    set c : K := ιK (1 + ∑ i : Fin k, MvPolynomial.X i * MvPolynomial.X i)
    have himg : φPoly (1 + ∑ i : Fin (k + 1), MvPolynomial.X i * MvPolynomial.X i) =
        Polynomial.C c + Polynomial.X ^ 2 := by
      have hX0 : φPoly (MvPolynomial.X 0) = Polynomial.X := by
        simp [φPoly, e, MvPolynomial.finSuccEquiv_X_zero]
      have hXs : ∀ i : Fin k, φPoly (MvPolynomial.X i.succ) = Polynomial.C (ιK (MvPolynomial.X i)) := by
        intro i
        simp [φPoly, e, MvPolynomial.finSuccEquiv_X_succ]
      rw [Fin.sum_univ_succ, map_add, map_one, map_add, map_mul, hX0, map_sum]
      have hsum_eq : ∑ i : Fin k, φPoly (MvPolynomial.X i.succ * MvPolynomial.X i.succ) =
          Polynomial.C (ιK (∑ i : Fin k, MvPolynomial.X i * MvPolynomial.X i)) := by
        rw [map_sum, map_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [map_mul, hXs i, ← map_mul, ← map_mul]
      rw [hsum_eq]
      simp only [c, map_add, map_one]
      ring
    obtain ⟨g, hg⟩ := hsum
    have hΦg : ιKX (Polynomial.C c + Polynomial.X ^ 2) = ∑ i : Fin (k + 1), (Φ (g i)) ^ 2 := by
      have := congr_arg Φ hg
      rw [IsFractionRing.lift_algebraMap] at this
      simp only [φ, RingHom.comp_apply, himg, map_sum, map_mul] at this
      simpa [sq] using this
    obtain ⟨q, p, hq, hspec⟩ := clear_denom (fun i => Φ (g i))
    have hpoly_eq : (Polynomial.C c + Polynomial.X ^ 2) * q ^ 2 = ∑ i : Fin (k + 1), p i ^ 2 := by
      apply IsFractionRing.injective K[X] (FractionRing K[X])
      rw [map_mul, map_pow, map_sum, hΦg, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_pow, ← hspec i, mul_comm, mul_pow]
    have hpoly_sum := cassels_lemma (anisotropic_mvRatFunc k)
      (Polynomial.C c + Polynomial.X ^ 2) q.natDegree q p hq le_rfl hpoly_eq
    exact not_sum_sq_poly_add_X_sq (anisotropic_mvRatFunc k) ih hpoly_sum

end CasselsProof

theorem OMA.solution : OMA.R_PfisterPythagorasNumber_pfister_problem_variants_eq_two_pow_R1.H2 :=
  CasselsProof.cassels
