import OMAStatements.S_oeis_a003056
/-! The finite polynomial Gauss identity and its coefficient lemmas were contributed
by Surya Midatala (@kofls), https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/12238.
The proof below adapts the corresponding sections of `proofs/oeis-a001936.lean`. -/

namespace OMA.GaussTriangular

open Finset Polynomial
open scoped PowerSeries.WithPiTopology

/-! ## Part 1: Congruence of polynomials modulo `X ^ (D + 1)` -/

def EqMod {R : Type*} [CommRing R] (D : ℕ) (f g : Polynomial R) : Prop :=
  ∀ m ≤ D, f.coeff m = g.coeff m

lemma eqMod_refl {R : Type*} [CommRing R] (D : ℕ) (f : Polynomial R) : EqMod D f f :=
  fun _ _ => rfl

lemma eqMod_symm {R : Type*} [CommRing R] {D : ℕ} {f g : Polynomial R}
    (h : EqMod D f g) : EqMod D g f :=
  fun m hm => (h m hm).symm

lemma eqMod_trans {R : Type*} [CommRing R] {D : ℕ} {f g h : Polynomial R}
    (h1 : EqMod D f g) (h2 : EqMod D g h) : EqMod D f h :=
  fun m hm => (h1 m hm).trans (h2 m hm)

private lemma eqMod_add {R : Type*} [CommRing R] {D : ℕ} {f1 f2 g1 g2 : Polynomial R}
    (h1 : EqMod D f1 g1) (h2 : EqMod D f2 g2) : EqMod D (f1 + f2) (g1 + g2) := by
  intro m hm
  simp only [Polynomial.coeff_add, h1 m hm, h2 m hm]

lemma eqMod_mul {R : Type*} [CommRing R] {D : ℕ} {f1 f2 g1 g2 : Polynomial R}
    (h1 : EqMod D f1 g1) (h2 : EqMod D f2 g2) : EqMod D (f1 * f2) (g1 * g2) := by
  intro m hm
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u v => f1.coeff u * f2.coeff v),
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun u v => g1.coeff u * g2.coeff v)]
  refine Finset.sum_congr rfl ?_
  intro k hk
  have hk_le : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [h1 k (by omega), h2 (m - k) (by omega)]

private lemma eqMod_sum {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (D : ℕ)
    (f g : ι → Polynomial R) (h : ∀ i ∈ s, EqMod D (f i) (g i)) :
    EqMod D (∑ i ∈ s, f i) (∑ i ∈ s, g i) := by
  intro m hm
  simp only [Polynomial.finsetSum_coeff]
  refine Finset.sum_congr rfl ?_
  intro i hi
  exact h i hi m hm

private lemma eqMod_prod {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (D : ℕ)
    (f g : ι → Polynomial R) (h : ∀ i ∈ s, EqMod D (f i) (g i)) :
    EqMod D (∏ i ∈ s, f i) (∏ i ∈ s, g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [eqMod_refl]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact eqMod_mul (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

private lemma eqMod_X_pow_zero {R : Type*} [CommRing R] (D k : ℕ) (hk : D < k) :
    EqMod D (Polynomial.X ^ k : Polynomial R) 0 := by
  intro m hm
  rw [Polynomial.coeff_X_pow, Polynomial.coeff_zero, if_neg (by omega)]

private lemma eqMod_one_add_X_pow {R : Type*} [CommRing R] (D k : ℕ) (hk : D < k) :
    EqMod D (1 + Polynomial.X ^ k : Polynomial R) 1 := by
  simpa using eqMod_add (eqMod_refl D (1 : Polynomial R)) (eqMod_X_pow_zero (R := R) D k hk)

private lemma eqMod_one_sub_X_pow {R : Type*} [CommRing R] (D k : ℕ) (hk : D < k) :
    EqMod D (1 - Polynomial.X ^ k : Polynomial R) 1 := by
  intro m hm
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow, if_neg (by omega), sub_zero]

private lemma eqMod_cancel_unit {R : Type*} [CommRing R] {D : ℕ} {f g u : Polynomial R}
    (hu : u.coeff 0 = 1) (h : EqMod D (f * u) (g * u)) : EqMod D f g := by
  intro m hm
  induction m using Nat.strong_induction_on with
  | h m ih =>
    have hcoeff := h m hm
    rw [Polynomial.coeff_mul, Polynomial.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => f.coeff a * u.coeff b),
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b => g.coeff a * u.coeff b),
      Finset.sum_range_succ, Finset.sum_range_succ, Nat.sub_self, hu, mul_one, mul_one] at hcoeff
    have hrest :
        ∑ k ∈ Finset.range m, f.coeff k * u.coeff (m - k) =
        ∑ k ∈ Finset.range m, g.coeff k * u.coeff (m - k) := by
      refine Finset.sum_congr rfl ?_
      intro k hk
      have hlt : k < m := Finset.mem_range.mp hk
      rw [ih k hlt (by omega)]
    rw [hrest] at hcoeff
    exact add_left_cancel hcoeff

lemma eqMod_prod_one_sub_drop (D M : ℕ) (hM : D ≤ M) :
    EqMod D (∏ i ∈ Finset.range M, (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1)))
      (∏ i ∈ Finset.range D, (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1))) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hM
  rw [Finset.prod_range_add]
  have htail : EqMod D (∏ i ∈ Finset.range r, (1 - (Polynomial.X : Polynomial ℤ) ^ (D + i + 1))) 1 := by
    have h1 : (∏ _i ∈ Finset.range r, (1 : Polynomial ℤ)) = 1 := by simp
    conv_rhs => rw [← h1]
    exact eqMod_prod (Finset.range r) D _ _ (fun i _ => eqMod_one_sub_X_pow D (D + i + 1) (by omega))
  simpa [mul_one] using eqMod_mul (eqMod_refl D _) htail

private lemma eqMod_prod_one_add_sq_drop (D M : ℕ) (hM : D ≤ M) :
    EqMod D (∏ i ∈ Finset.range M, (1 + (Polynomial.X : Polynomial ℤ) ^ (i + 1)) ^ 2)
      (∏ i ∈ Finset.range D, (1 + (Polynomial.X : Polynomial ℤ) ^ (i + 1)) ^ 2) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hM
  rw [Finset.prod_range_add]
  have htail : EqMod D (∏ i ∈ Finset.range r, (1 + (Polynomial.X : Polynomial ℤ) ^ (D + i + 1)) ^ 2) 1 := by
    have h1 : (∏ _i ∈ Finset.range r, (1 : Polynomial ℤ)) = 1 := by simp
    conv_rhs => rw [← h1]
    refine eqMod_prod (Finset.range r) D _ _ (fun i _ => ?_)
    have hadd := eqMod_one_add_X_pow (R := ℤ) D (D + i + 1) (by omega)
    simpa [sq] using eqMod_mul hadd hadd
  simpa [mul_one] using eqMod_mul (eqMod_refl D _) htail

/-! ## Part 2: Finite-polynomial Gauss triangular number identity -/

private noncomputable def PPoly (N : ℕ) : Polynomial (Polynomial ℤ) :=
  ∏ k ∈ Finset.range N,
    ((1 + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (k + 1)) * Polynomial.X) *
     (Polynomial.X + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ k)))

lemma coeff_comp_C_mul_X {R : Type*} [CommRing R] (a : R) (f : Polynomial R) (j : ℕ) :
    (f.comp (Polynomial.C a * Polynomial.X)).coeff j = a ^ j * f.coeff j := by
  induction f using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp only [Polynomial.add_comp, Polynomial.coeff_add, ihp, ihq, mul_add]
  | monomial n c =>
    rw [Polynomial.monomial_comp, mul_pow, ← Polynomial.C_pow, ← mul_assoc, ← Polynomial.C_mul,
      Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_monomial]
    by_cases h : n = j
    · subst h; simp [mul_comm]
    · simp [h, Ne.symm h]

lemma comp_finset_prod {R ι : Type*} [CommRing R] (s : Finset ι)
    (f : ι → Polynomial R) (g : Polynomial R) :
    (∏ i ∈ s, f i).comp g = ∏ i ∈ s, (f i).comp g := by
  classical
  induction s using Finset.induction with
  | empty => simp [Polynomial.one_comp]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Polynomial.mul_comp, ih]

private lemma PPoly_func_eq (N : ℕ) (hN : 1 ≤ N) :
    (Polynomial.X + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (N - 1))) *
      (PPoly N).comp (Polynomial.C Polynomial.X * Polynomial.X) =
    Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (N - 1)) *
      (1 + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (N + 1)) * Polynomial.X) * PPoly N := by
  set q : Polynomial (Polynomial ℤ) := Polynomial.C Polynomial.X
  set z : Polynomial (Polynomial ℤ) := Polynomial.X
  have hcomp_prod :
      (PPoly N).comp (q * z) =
      (∏ k ∈ Finset.range N, (1 + q ^ (k + 2) * z)) *
      (∏ k ∈ Finset.range N, (q * z + q ^ k)) := by
    unfold PPoly
    rw [Finset.prod_mul_distrib, Polynomial.mul_comp, comp_finset_prod, comp_finset_prod]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl ?_) (Finset.prod_congr rfl ?_)
    · intro k _
      simp only [Polynomial.add_comp, Polynomial.one_comp, Polynomial.mul_comp, Polynomial.C_comp,
        Polynomial.X_comp]
      simp only [q, z, map_pow]
      ring
    · intro k _
      simp only [Polynomial.add_comp, Polynomial.C_comp, Polynomial.X_comp]
      simp only [q, z, map_pow]
  have hP_split :
      PPoly N =
      (∏ k ∈ Finset.range N, (1 + q ^ (k + 1) * z)) *
      (∏ k ∈ Finset.range N, (z + q ^ k)) := by
    unfold PPoly
    rw [Finset.prod_mul_distrib]
    exact congrArg₂ (· * ·)
      (Finset.prod_congr rfl (fun k _ => by simp only [q, z, map_pow]))
      (Finset.prod_congr rfl (fun k _ => by simp only [q, z, map_pow]))
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [show 1 + M = M + 1 by omega] at hcomp_prod hP_split ⊢
  simp only [Nat.add_sub_cancel]
  have hA : (1 + q * z) * (∏ k ∈ Finset.range (M + 1), (1 + q ^ (k + 2) * z)) =
      (1 + q ^ (M + 2) * z) * (∏ k ∈ Finset.range (M + 1), (1 + q ^ (k + 1) * z)) := by
    rw [Finset.prod_range_succ, Finset.prod_range_succ']
    simp only [zero_add, pow_one]
    ring
  have hB : ∏ k ∈ Finset.range (M + 1), (q * z + q ^ k) =
      (1 + q * z) * q ^ M * (∏ k ∈ Finset.range M, (z + q ^ k)) := by
    rw [Finset.prod_range_succ']
    have hfactor : ∏ k ∈ Finset.range M, (q * z + q ^ (k + 1)) =
        q ^ M * ∏ k ∈ Finset.range M, (z + q ^ k) := by
      have : ∀ k, q * z + q ^ (k + 1) = q * (z + q ^ k) := fun k => by ring
      simp_rw [this, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range]
    rw [hfactor]
    simp only [pow_zero]
    ring
  have hC : (z + q ^ M) * (∏ k ∈ Finset.range M, (z + q ^ k)) =
      ∏ k ∈ Finset.range (M + 1), (z + q ^ k) := by
    rw [Finset.prod_range_succ]; ring
  have hqM : Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ M) = q ^ M := map_pow _ _ _
  have hqM2 : Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (M + 2)) = q ^ (M + 2) := map_pow _ _ _
  rw [hqM, hqM2]
  change (z + q ^ M) * (PPoly (M + 1)).comp (q * z) = q ^ M * (1 + q ^ (M + 2) * z) * PPoly (M + 1)
  rw [hcomp_prod, hP_split, hB]
  calc (z + q ^ M) * ((∏ k ∈ Finset.range (M + 1), (1 + q ^ (k + 2) * z)) *
        ((1 + q * z) * q ^ M * ∏ k ∈ Finset.range M, (z + q ^ k)))
      = q ^ M * ((1 + q * z) * ∏ k ∈ Finset.range (M + 1), (1 + q ^ (k + 2) * z)) *
        ((z + q ^ M) * ∏ k ∈ Finset.range M, (z + q ^ k)) := by ring
    _ = q ^ M * ((1 + q ^ (M + 2) * z) * ∏ k ∈ Finset.range (M + 1), (1 + q ^ (k + 1) * z)) *
        ∏ k ∈ Finset.range (M + 1), (z + q ^ k) := by rw [hA, hC]
    _ = q ^ M * (1 + q ^ (M + 2) * z) *
        ((∏ k ∈ Finset.range (M + 1), (1 + q ^ (k + 1) * z)) *
        ∏ k ∈ Finset.range (M + 1), (z + q ^ k)) := by ring

private lemma PPoly_coeff_rec (N j : ℕ) (hN : 1 ≤ N) (hj : 1 ≤ j) (hj2 : j ≤ 2 * N) :
    (Polynomial.X : Polynomial ℤ) ^ (N - 1) * (1 - Polynomial.X ^ j) * (PPoly N).coeff j =
    (Polynomial.X : Polynomial ℤ) ^ (j - 1) * (1 - Polynomial.X ^ (2 * N + 1 - j)) *
      (PPoly N).coeff (j - 1) := by
  have hfe := congrArg (fun f => f.coeff j) (PPoly_func_eq N hN)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj
  rw [show 1 + m = m + 1 by omega] at hfe hj2 ⊢
  simp only [Nat.add_sub_cancel]
  have hlhs :
      ((Polynomial.X + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (N - 1))) *
        (PPoly N).comp (Polynomial.C Polynomial.X * Polynomial.X)).coeff (m + 1) =
      Polynomial.X ^ m * (PPoly N).coeff m +
        Polynomial.X ^ (N - 1) * (Polynomial.X ^ (m + 1) * (PPoly N).coeff (m + 1)) := by
    rw [add_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul, Polynomial.coeff_C_mul,
      coeff_comp_C_mul_X, coeff_comp_C_mul_X]
  have hrhs :
      (Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (N - 1)) *
        (1 + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (N + 1)) * Polynomial.X) *
        PPoly N).coeff (m + 1) =
      Polynomial.X ^ (N - 1) * (PPoly N).coeff (m + 1) +
        Polynomial.X ^ (N - 1) * (Polynomial.X ^ (N + 1) * (PPoly N).coeff m) := by
    rw [mul_assoc, Polynomial.coeff_C_mul, add_mul, one_mul, Polynomial.coeff_add,
      mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, mul_add]
  rw [hlhs, hrhs] at hfe
  have hexp : (Polynomial.X : Polynomial ℤ) ^ (N - 1) * Polynomial.X ^ (N + 1) =
      Polynomial.X ^ m * Polynomial.X ^ (2 * N - m) := by
    rw [← pow_add, ← pow_add]
    congr 1; omega
  have hsub : 2 * N + 1 - (m + 1) = 2 * N - m := by omega
  rw [hsub]
  linear_combination -hfe - (PPoly N).coeff m * hexp

private def triExp (N j : ℕ) : ℕ :=
  if N ≤ j then (j - N) * (j - N + 1) / 2 else (N - 1 - j) * (N - j) / 2

private lemma triExp_step (N j : ℕ) (hN : 1 ≤ N) (hj : 1 ≤ j) :
    (j - 1) + triExp N (j - 1) = (N - 1) + triExp N j := by
  unfold triExp
  by_cases h1 : N < j
  · have hge1 : N ≤ j - 1 := by omega
    have hge2 : N ≤ j := by omega
    rw [if_pos hge1, if_pos hge2]
    set k := j - 1 - N
    have hk1 : j - N = k + 1 := by omega
    have hk2 : j - 1 - N + 1 = k + 1 := by omega
    rw [hk1, hk2]
    have hdiv : (k + 1) * (k + 1 + 1) / 2 = k * (k + 1) / 2 + (k + 1) := by
      have : (k + 1) * (k + 1 + 1) = k * (k + 1) + (k + 1) * 2 := by ring
      rw [this, Nat.add_mul_div_right _ _ (by norm_num)]
    omega
  · by_cases h2 : j = N
    · subst h2
      have hlt : ¬ (j ≤ j - 1) := by omega
      rw [if_neg hlt, if_pos le_rfl]
      simp
    · have hlt1 : ¬ (N ≤ j - 1) := by omega
      have hlt2 : ¬ (N ≤ j) := by omega
      rw [if_neg hlt1, if_neg hlt2]
      set k := N - 1 - j
      have hk1 : N - j = k + 1 := by omega
      have hk2 : N - 1 - (j - 1) = k + 1 := by omega
      have hk3 : N - (j - 1) = k + 2 := by omega
      rw [hk1, hk2, hk3]
      have hdiv : (k + 1) * (k + 2) / 2 = k * (k + 1) / 2 + (k + 1) := by
        have : (k + 1) * (k + 2) = k * (k + 1) + (k + 1) * 2 := by ring
        rw [this, Nat.add_mul_div_right _ _ (by norm_num)]
      omega

private lemma PPoly_coeff_zero (N : ℕ) :
    (PPoly N).coeff 0 = (Polynomial.X : Polynomial ℤ) ^ (N * (N - 1) / 2) := by
  rw [Polynomial.coeff_zero_eq_eval_zero, PPoly, Polynomial.eval_prod]
  have hfac : ∀ k ∈ Finset.range N,
      Polynomial.eval 0 ((1 + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (k + 1)) * Polynomial.X) *
        (Polynomial.X + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ k))) =
      (Polynomial.X : Polynomial ℤ) ^ k := by
    intro k _; simp
  rw [Finset.prod_congr rfl hfac, Finset.prod_pow_eq_pow_sum]
  congr 1
  rw [Finset.sum_range_id]

private lemma PPoly_coeff_formula (N j : ℕ) (hN : 1 ≤ N) (hj : j ≤ 2 * N) :
    (PPoly N).coeff j *
      (∏ i ∈ Finset.range j, (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1))) *
      (∏ i ∈ Finset.range (2 * N - j), (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1))) =
    (Polynomial.X : Polynomial ℤ) ^ (triExp N j) *
      ∏ i ∈ Finset.range (2 * N), (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1)) := by
  induction j with
  | zero =>
    have htri : triExp N 0 = N * (N - 1) / 2 := by
      unfold triExp
      rw [if_neg (by omega)]
      simp [mul_comm]
    rw [PPoly_coeff_zero, htri]
    simp
  | succ j ih =>
    have hrec := PPoly_coeff_rec N (j + 1) hN (by omega) hj
    simp only [Nat.add_sub_cancel] at hrec
    have hstep := triExp_step N (j + 1) hN (by omega)
    simp only [Nat.add_sub_cancel] at hstep
    have hsub : 2 * N - j = (2 * N - (j + 1)) + 1 := by omega
    have hsub2 : 2 * N + 1 - (j + 1) = (2 * N - (j + 1)) + 1 := by omega
    have hih := ih (by omega)
    have hmul :
        (Polynomial.X : Polynomial ℤ) ^ (N - 1) *
        ((PPoly N).coeff (j + 1) *
          (∏ i ∈ Finset.range (j + 1), (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1))) *
          (∏ i ∈ Finset.range (2 * N - (j + 1)), (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1)))) =
        (Polynomial.X : Polynomial ℤ) ^ (N - 1) *
        ((Polynomial.X : Polynomial ℤ) ^ (triExp N (j + 1)) *
          ∏ i ∈ Finset.range (2 * N), (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1))) := by
      calc (Polynomial.X : Polynomial ℤ) ^ (N - 1) *
            ((PPoly N).coeff (j + 1) *
              (∏ i ∈ Finset.range (j + 1), (1 - Polynomial.X ^ (i + 1))) *
              (∏ i ∈ Finset.range (2 * N - (j + 1)), (1 - Polynomial.X ^ (i + 1))))
          = ((Polynomial.X ^ (N - 1) * (1 - Polynomial.X ^ (j + 1)) * (PPoly N).coeff (j + 1))) *
              (∏ i ∈ Finset.range j, (1 - Polynomial.X ^ (i + 1))) *
              (∏ i ∈ Finset.range (2 * N - (j + 1)), (1 - Polynomial.X ^ (i + 1))) := by
            rw [Finset.prod_range_succ]; ring
        _ = (Polynomial.X ^ j * (1 - Polynomial.X ^ (2 * N + 1 - (j + 1))) * (PPoly N).coeff j) *
              (∏ i ∈ Finset.range j, (1 - Polynomial.X ^ (i + 1))) *
              (∏ i ∈ Finset.range (2 * N - (j + 1)), (1 - Polynomial.X ^ (i + 1))) := by
            rw [hrec]
        _ = Polynomial.X ^ j *
              ((PPoly N).coeff j *
                (∏ i ∈ Finset.range j, (1 - Polynomial.X ^ (i + 1))) *
                (∏ i ∈ Finset.range (2 * N - j), (1 - Polynomial.X ^ (i + 1)))) := by
            rw [hsub, hsub2, Finset.prod_range_succ]; ring
        _ = Polynomial.X ^ j *
              (Polynomial.X ^ (triExp N j) *
                ∏ i ∈ Finset.range (2 * N), (1 - Polynomial.X ^ (i + 1))) := by
            rw [hih]
        _ = Polynomial.X ^ (N - 1) *
              (Polynomial.X ^ (triExp N (j + 1)) *
                ∏ i ∈ Finset.range (2 * N), (1 - Polynomial.X ^ (i + 1))) := by
            rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add, hstep]
    exact mul_left_cancel₀ (pow_ne_zero (N - 1) Polynomial.X_ne_zero) hmul

private lemma prod_one_sub_coeff_zero (M : ℕ) :
    (∏ i ∈ Finset.range M, (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1))).coeff 0 = 1 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod]
  refine Finset.prod_eq_one ?_
  intro i _
  simp [zero_pow (Nat.succ_ne_zero i)]

private lemma PPoly_natDegree_le (N : ℕ) : (PPoly N).natDegree ≤ 2 * N := by
  unfold PPoly
  calc (∏ k ∈ Finset.range N,
          ((1 + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (k + 1)) * Polynomial.X) *
           (Polynomial.X + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ k)))).natDegree
      ≤ ∑ k ∈ Finset.range N,
          ((1 + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (k + 1)) * Polynomial.X) *
           (Polynomial.X + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ k))).natDegree :=
        Polynomial.natDegree_prod_le _ _
    _ ≤ ∑ _k ∈ Finset.range N, 2 := by
        refine Finset.sum_le_sum ?_
        intro k _
        have h1 : (1 + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (k + 1)) * Polynomial.X).natDegree ≤ 1 := by
          refine le_trans (Polynomial.natDegree_add_le _ _) ?_
          simp only [Polynomial.natDegree_one, max_le_iff, zero_le, true_and]
          exact le_trans (Polynomial.natDegree_C_mul_le _ _) (by simp)
        have h2 : (Polynomial.X + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ k)).natDegree ≤ 1 := by
          refine le_trans (Polynomial.natDegree_add_le _ _) ?_
          simp
        exact le_trans (Polynomial.natDegree_mul_le) (by omega)
    _ = 2 * N := by simp [mul_comm]

private lemma PPoly_eval_one (N : ℕ) (hN : 1 ≤ N) :
    (PPoly N).eval 1 =
    2 * (1 + (Polynomial.X : Polynomial ℤ) ^ N) *
      ∏ k ∈ Finset.range (N - 1), (1 + (Polynomial.X : Polynomial ℤ) ^ (k + 1)) ^ 2 := by
  unfold PPoly
  rw [Polynomial.eval_prod]
  have hfac : ∀ k ∈ Finset.range N,
      Polynomial.eval 1 ((1 + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ (k + 1)) * Polynomial.X) *
        (Polynomial.X + Polynomial.C ((Polynomial.X : Polynomial ℤ) ^ k))) =
      (1 + (Polynomial.X : Polynomial ℤ) ^ (k + 1)) * (1 + (Polynomial.X : Polynomial ℤ) ^ k) := by
    intro k _; simp
  rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib]
  obtain ⟨M, rfl⟩ := Nat.exists_eq_add_of_le hN
  rw [show 1 + M = M + 1 by omega]
  simp only [Nat.add_sub_cancel]
  rw [Finset.prod_range_succ (fun k => (1 + (Polynomial.X : Polynomial ℤ) ^ (k + 1))),
    Finset.prod_range_succ' (fun k => (1 + (Polynomial.X : Polynomial ℤ) ^ k))]
  simp only [pow_zero]
  rw [show (1 : Polynomial ℤ) + 1 = 2 by ring, Finset.prod_pow]
  ring

lemma gauss_triangular_eqMod (D : ℕ) :
    EqMod D
      (∏ k ∈ Finset.range D,
        ((1 + (Polynomial.X : Polynomial ℤ) ^ (k + 1)) * (1 - (Polynomial.X : Polynomial ℤ) ^ (2 * (k + 1)))))
      (∑ k ∈ Finset.range (D + 1), (Polynomial.X : Polynomial ℤ) ^ (k * (k + 1) / 2)) := by
  set N := 2 * D + 2
  have hN : 1 ≤ N := by omega
  set E := ∏ i ∈ Finset.range D, (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1))
  have hE0 : E.coeff 0 = 1 := prod_one_sub_coeff_zero D
  -- For each j ≤ 2 * N, relate (PPoly N).coeff j * E to X ^ (triExp N j) modulo X ^ (D + 1).
  have hterm : ∀ j ∈ Finset.range (2 * N + 1),
      EqMod D ((PPoly N).coeff j * E) ((Polynomial.X : Polynomial ℤ) ^ (triExp N j)) := by
    intro j hj
    have hj_le : j ≤ 2 * N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hform := PPoly_coeff_formula N j hN hj_le
    by_cases htri : triExp N j ≤ D
    · have hj_gt : D ≤ j := by
        by_contra hlt
        have hlt' : j < D := Nat.lt_of_not_ge hlt
        have hle_j : ¬ (N ≤ j) := by omega
        have hval : triExp N j = (N - 1 - j) * (N - j) / 2 := by unfold triExp; rw [if_neg hle_j]
        have hbig : D + 2 ≤ N - 1 - j := by omega
        have hprod : (D + 2) * (D + 3) ≤ (N - 1 - j) * (N - j) :=
          Nat.mul_le_mul hbig (by omega)
        have h2D : 2 * (D + 1) ≤ (N - 1 - j) * (N - j) := by nlinarith
        omega
      have h2Nj_gt : D ≤ 2 * N - j := by
        by_contra hlt
        have hlt' : 2 * N - j < D := Nat.lt_of_not_ge hlt
        have hge_j : N ≤ j := by omega
        have hval : triExp N j = (j - N) * (j - N + 1) / 2 := by unfold triExp; rw [if_pos hge_j]
        have hbig : D + 2 ≤ j - N := by omega
        have hprod : (D + 2) * (D + 3) ≤ (j - N) * (j - N + 1) :=
          Nat.mul_le_mul hbig (by omega)
        have h2D : 2 * (D + 1) ≤ (j - N) * (j - N + 1) := by nlinarith
        omega
      have h1 : EqMod D (∏ i ∈ Finset.range j, (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1))) E :=
        eqMod_prod_one_sub_drop D j hj_gt
      have h2 : EqMod D (∏ i ∈ Finset.range (2 * N - j), (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1))) E :=
        eqMod_prod_one_sub_drop D (2 * N - j) h2Nj_gt
      have h3 : EqMod D (∏ i ∈ Finset.range (2 * N), (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1))) E :=
        eqMod_prod_one_sub_drop D (2 * N) (by omega)
      have hlhs : EqMod D
          ((PPoly N).coeff j *
            (∏ i ∈ Finset.range j, (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1))) *
            (∏ i ∈ Finset.range (2 * N - j), (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1))))
          ((PPoly N).coeff j * E * E) :=
        eqMod_mul (eqMod_mul (eqMod_refl D _) h1) h2
      have hrhs : EqMod D
          ((Polynomial.X : Polynomial ℤ) ^ (triExp N j) *
            ∏ i ∈ Finset.range (2 * N), (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1)))
          ((Polynomial.X : Polynomial ℤ) ^ (triExp N j) * E) :=
        eqMod_mul (eqMod_refl D _) h3
      have hcomb : EqMod D ((PPoly N).coeff j * E * E)
          ((Polynomial.X : Polynomial ℤ) ^ (triExp N j) * E) :=
        eqMod_trans (eqMod_symm hlhs) (hform ▸ hrhs)
      exact eqMod_cancel_unit hE0 hcomb
    · have hgt : D < triExp N j := Nat.lt_of_not_ge htri
      set u := (∏ i ∈ Finset.range j, (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1))) *
          (∏ i ∈ Finset.range (2 * N - j), (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1)))
      have hu0 : u.coeff 0 = 1 := by
        rw [Polynomial.mul_coeff_zero, prod_one_sub_coeff_zero, prod_one_sub_coeff_zero, mul_one]
      have hzero : EqMod D ((PPoly N).coeff j * u) (0 * u) := by
        rw [zero_mul]
        have hform' : (PPoly N).coeff j * u =
            (Polynomial.X : Polynomial ℤ) ^ (triExp N j) *
              ∏ i ∈ Finset.range (2 * N), (1 - (Polynomial.X : Polynomial ℤ) ^ (i + 1)) := by
          simpa [u, mul_assoc] using hform
        rw [hform']
        simpa [zero_mul] using eqMod_mul (eqMod_X_pow_zero (R := ℤ) D (triExp N j) hgt) (eqMod_refl D _)
      have hc0 : EqMod D ((PPoly N).coeff j) 0 := eqMod_cancel_unit hu0 hzero
      exact eqMod_trans (by simpa [zero_mul] using eqMod_mul hc0 (eqMod_refl D E))
        (eqMod_symm (eqMod_X_pow_zero (R := ℤ) D (triExp N j) hgt))
  -- Sum over j ∈ range (2 * N + 1)
  have hsum_eq : EqMod D ((PPoly N).eval 1 * E)
      (∑ j ∈ Finset.range (2 * N + 1), (Polynomial.X : Polynomial ℤ) ^ (triExp N j)) := by
    have heval : (PPoly N).eval 1 = ∑ j ∈ Finset.range (2 * N + 1), (PPoly N).coeff j := by
      rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (PPoly_natDegree_le N))]
      simp
    rw [heval, Finset.sum_mul]
    exact eqMod_sum (Finset.range (2 * N + 1)) D _ _ hterm
  -- Simplify LHS: (PPoly N).eval 1 * E ≡ 2 * ∏_{k < D} (1 + X^(k+1)) * (1 - X^(2*(k+1)))
  have hlhs_mod : EqMod D ((PPoly N).eval 1 * E)
      (2 * ∏ k ∈ Finset.range D,
        ((1 + (Polynomial.X : Polynomial ℤ) ^ (k + 1)) * (1 - (Polynomial.X : Polynomial ℤ) ^ (2 * (k + 1))))) := by
    rw [PPoly_eval_one N hN]
    have h1 : EqMod D (1 + (Polynomial.X : Polynomial ℤ) ^ N) 1 :=
      eqMod_one_add_X_pow D N (by omega)
    have h2 : EqMod D
        (∏ k ∈ Finset.range (N - 1), (1 + (Polynomial.X : Polynomial ℤ) ^ (k + 1)) ^ 2)
        (∏ k ∈ Finset.range D, (1 + (Polynomial.X : Polynomial ℤ) ^ (k + 1)) ^ 2) :=
      eqMod_prod_one_add_sq_drop D (N - 1) (by omega)
    have hcomb : EqMod D
        (2 * (1 + (Polynomial.X : Polynomial ℤ) ^ N) *
          (∏ k ∈ Finset.range (N - 1), (1 + (Polynomial.X : Polynomial ℤ) ^ (k + 1)) ^ 2) * E)
        (2 * 1 * (∏ k ∈ Finset.range D, (1 + (Polynomial.X : Polynomial ℤ) ^ (k + 1)) ^ 2) * E) :=
      eqMod_mul (eqMod_mul (eqMod_mul (eqMod_refl D 2) h1) h2) (eqMod_refl D E)
    have hrewrite :
        2 * (1 : Polynomial ℤ) *
          (∏ k ∈ Finset.range D, (1 + (Polynomial.X : Polynomial ℤ) ^ (k + 1)) ^ 2) * E =
        2 * ∏ k ∈ Finset.range D,
          ((1 + (Polynomial.X : Polynomial ℤ) ^ (k + 1)) * (1 - (Polynomial.X : Polynomial ℤ) ^ (2 * (k + 1)))) := by
      dsimp only [E]
      rw [mul_one, mul_assoc, ← Finset.prod_mul_distrib]
      congr 1
      refine Finset.prod_congr rfl ?_
      intro k _
      rw [mul_comm 2 (k + 1), pow_mul]
      ring
    rw [hrewrite] at hcomb
    exact hcomb
  -- Simplify RHS: ∑_{j < 2*N + 1} X^(triExp N j) ≡ 2 * ∑_{k ≤ D} X^(k*(k+1)/2)
  have hrhs_mod : EqMod D
      (∑ j ∈ Finset.range (2 * N + 1), (Polynomial.X : Polynomial ℤ) ^ (triExp N j))
      (2 * ∑ k ∈ Finset.range (D + 1), (Polynomial.X : Polynomial ℤ) ^ (k * (k + 1) / 2)) := by
    have hsplit :
        ∑ j ∈ Finset.range (2 * N + 1), (Polynomial.X : Polynomial ℤ) ^ (triExp N j) =
        (∑ k ∈ Finset.range N, (Polynomial.X : Polynomial ℤ) ^ (k * (k + 1) / 2)) +
        (∑ k ∈ Finset.range (N + 1), (Polynomial.X : Polynomial ℤ) ^ (k * (k + 1) / 2)) := by
      rw [show 2 * N + 1 = N + (N + 1) by omega, Finset.sum_range_add]
      congr 1
      · refine Finset.sum_bij (fun j _ => N - 1 - j) ?_ ?_ ?_ ?_
        · intro j hj; simp only [Finset.mem_range] at hj ⊢; omega
        · intro j1 hj1 j2 hj2 h
          simp only [Finset.mem_range] at hj1 hj2; omega
        · intro k hk
          simp only [Finset.mem_range] at hk
          exact ⟨N - 1 - k, Finset.mem_range.mpr (by omega), by omega⟩
        · intro j hj
          simp only [Finset.mem_range] at hj
          unfold triExp
          rw [if_neg (by omega), show N - j = N - 1 - j + 1 by omega]
      · refine Finset.sum_congr rfl ?_
        intro k _
        unfold triExp
        rw [if_pos (by omega), Nat.add_sub_cancel_left]
    rw [hsplit]
    have hdrop : ∀ M : ℕ, D + 1 ≤ M →
        EqMod D (∑ k ∈ Finset.range M, (Polynomial.X : Polynomial ℤ) ^ (k * (k + 1) / 2))
          (∑ k ∈ Finset.range (D + 1), (Polynomial.X : Polynomial ℤ) ^ (k * (k + 1) / 2)) := by
      intro M hM
      obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hM
      rw [Finset.sum_range_add]
      have htail : EqMod D
          (∑ i ∈ Finset.range r, (Polynomial.X : Polynomial ℤ) ^ ((D + 1 + i) * (D + 1 + i + 1) / 2)) 0 := by
        have h0 : (0 : Polynomial ℤ) = ∑ _i ∈ Finset.range r, (0 : Polynomial ℤ) := by simp
        rw [h0]
        refine eqMod_sum (Finset.range r) D _ _ (fun i _ => ?_)
        refine eqMod_X_pow_zero D _ ?_
        have : (D + 1) * (D + 2) ≤ (D + 1 + i) * (D + 1 + i + 1) :=
          Nat.mul_le_mul (by omega) (by omega)
        have h2D : 2 * (D + 1) ≤ (D + 1 + i) * (D + 1 + i + 1) := by nlinarith
        omega
      simpa [add_zero] using eqMod_add (eqMod_refl D _) htail
    have hadd := eqMod_add (hdrop N (by omega)) (hdrop (N + 1) (by omega))
    simpa [two_mul] using hadd
  -- Combine and cancel factor of 2 in ℤ!
  have h2 := eqMod_trans (eqMod_symm hlhs_mod) (eqMod_trans hsum_eq hrhs_mod)
  intro m hm
  have hcm := h2 m hm
  simp only [Polynomial.coeff_ofNat_mul] at hcm
  omega

end OMA.GaussTriangular
namespace OMA.S_oeis_a003056
open Finset Polynomial
private def tri (k : ℕ) : ℕ := ∑ i ∈ range (k+1), i
private theorem tri_succ (k : ℕ) : tri (k+1)=tri k+(k+1) := sum_range_succ _ _
private theorem tri_zero : tri 0=0 := by simp [tri]
private theorem tri_strict : StrictMono tri := strictMono_nat_of_lt_succ fun i => by rw [tri_succ]; omega
private theorem le_tri (k : ℕ) : k≤tri k := by
  induction k with
  | zero => omega
  | succ k ih => rw [tri_succ]; omega
private theorem triangular (k : ℕ) : tri k=k*(k+1)/2 := by
  simp [tri,sum_range_id,mul_comm]

private theorem minimal_sum (s : Finset ℕ) (hs : ∀ i ∈ s, 0 < i) : tri s.card ≤ ∑ i ∈ s, i := by
  induction s using Finset.induction_on_max with
  | empty => simp [tri]
  | insert a s hmax ih =>
    have hp : ∀ i ∈ s, 0 < i := fun i hi => hs i (mem_insert_of_mem hi)
    have ha : 0<a := hs a (mem_insert_self _ _)
    have han : a∉s := fun e => (lt_irrefl _) (hmax a e)
    have hsub : s⊆Ico 1 a := fun i hi => mem_Ico.mpr ⟨hp i hi,hmax i hi⟩
    have hcard := card_le_card hsub
    rw [Nat.card_Ico] at hcard
    rw [card_insert_of_notMem han,sum_insert han,tri_succ]
    have hh := ih hp
    omega

private theorem tri_b_le (n : ℕ) : tri (b n) ≤ n := by
  classical
  obtain ⟨p,_,h⟩ := (univ : Finset n.Partition).exists_mem_eq_sup
    ⟨Nat.Partition.indiscrete n,mem_univ _⟩ (fun p => p.parts.toFinset.card)
  change tri ((univ : Finset n.Partition).sup _) ≤ n
  rw [h]
  apply (minimal_sum p.parts.toFinset (fun i hi => p.parts_pos (by simpa using hi))).trans
  obtain ⟨z,hz⟩ := Multiset.le_iff_exists_add.mp p.parts.dedup_le
  have hsum := p.parts_sum
  rw [hz,Multiset.sum_add] at hsum
  change p.parts.toFinset.sum id ≤ n
  rw [← sum_val,Multiset.toFinset_val]
  omega

private theorem staircase (k n : ℕ) (h : tri k ≤ n) : k ≤ b n := by
  classical
  let s := (range (k+1)).erase 0
  have hs : 0∈range (k+1) := by simp
  have hval : s.val.sum = tri k := by
    change ((range (k+1)).erase 0).val.sum=_
    rw [sum_val]
    simpa [tri] using sum_erase_add (range (k+1)) id hs
  let p : n.Partition := {
    parts := s.val + Multiset.replicate (n-tri k) 1
    parts_pos := by
      intro i hi
      rcases Multiset.mem_add.mp hi with h1|h1
      · have hh : i∈s := h1
        exact Nat.pos_of_ne_zero (mem_erase.mp hh).1
      · have := Multiset.eq_of_mem_replicate h1
        omega
    parts_sum := by simp [hval]; omega }
  have hsub : s ⊆ p.parts.toFinset := by
    intro i hi
    apply Multiset.mem_toFinset.mpr
    exact Multiset.mem_add.mpr (Or.inl hi)
  have hcard : s.card=k := by simp [s,card_erase_of_mem hs]
  rw [← hcard]
  apply (card_le_card hsub).trans
  exact le_sup (f:=fun q : n.Partition => q.parts.toFinset.card) (mem_univ p)

private theorem cutoff {n k : ℕ} : tri k ≤ n ↔ k ≤ b n :=
  ⟨staircase k n, fun h => (tri_strict.monotone h).trans (tri_b_le n)⟩

private theorem cumulative (D n : ℕ) (hn : n≤D) :
    (∑ j ∈ range (D+1), if tri j ≤ n then (1:ℤ) else 0) = (b n:ℤ)+1 := by
  have hb : b n ≤ n := (le_tri _).trans (tri_b_le n)
  have hs : (range (D+1)).filter (fun j => tri j ≤ n) = range (b n+1) := by
    ext i; simp [cutoff]; omega
  simp [sum_boole,hs]


private theorem trunc_coeff (D m : ℕ) (hm : m≤D) : (truncB D).coeff m = (b m:ℤ) := by
  simp [truncB,coeff_monomial,mem_range.mpr (by omega : m<D+1)]

private theorem first_diff (D : ℕ) : OMA.GaussTriangular.EqMod D ((1-X)*truncB D + 1)
    (∑ j ∈ range (D+1), (X : ℤ[X])^(j*(j+1)/2)) := by
  intro m hm
  simp only [sub_mul,one_mul,coeff_add,coeff_sub,Polynomial.finsetSum_coeff,coeff_X_pow,← triangular]
  cases m with
  | zero =>
    rw [trunc_coeff D 0 (by omega),coeff_X_mul_zero]
    simpa [eq_comm] using (cumulative D 0 (by omega)).symm
  | succ m =>
    rw [trunc_coeff D (m+1) hm,coeff_X_mul,trunc_coeff D m (by omega)]
    have hadd : ∑ j ∈ range (D+1), (if tri j ≤ m+1 then (1:ℤ) else 0) =
        (∑ j ∈ range (D+1), if tri j ≤ m then 1 else 0) +
        ∑ j ∈ range (D+1), if m+1 = tri j then 1 else 0 := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      by_cases hh : tri j ≤ m
      · simp [hh,show tri j ≤ m+1 by omega,show m+1≠tri j by omega]
      · by_cases he : m+1=tri j
        · simp [← he]
        · simp [hh,he,show ¬ tri j ≤ m+1 by omega]
    rw [cumulative D _ hm,cumulative D _ (by omega)] at hadd
    simp only [coeff_one, Nat.succ_ne_zero,if_false,add_zero]
    omega

private theorem product_formula (D : ℕ) :
    (((1-X)*truncB D + 1)*eulerProd D 1).coeff D = ((eulerProd D 2)^2).coeff D := by
  let P := ∏ i ∈ range D, (1+(X:ℤ[X])^(i+1))
  have hg := OMA.GaussTriangular.gauss_triangular_eqMod D
  rw [prod_mul_distrib] at hg
  have ht : OMA.GaussTriangular.EqMod D ((1-X)*truncB D + 1) (P*eulerProd D 2) :=
    OMA.GaussTriangular.eqMod_trans (first_diff D) (OMA.GaussTriangular.eqMod_symm hg)
  have hf : P * eulerProd D 1 = eulerProd D 2 := by
    simp only [P,eulerProd,one_mul,← prod_mul_distrib]
    apply prod_congr rfl
    intro i hi
    rw [pow_mul']
    ring
  have hh := OMA.GaussTriangular.eqMod_mul ht (OMA.GaussTriangular.eqMod_refl D (eulerProd D 1))
  have h := hh D le_rfl
  rwa [show P * eulerProd D 2 * eulerProd D 1 = (P * eulerProd D 1) * eulerProd D 2 by ac_rfl,hf,← pow_two] at h

end OMA.S_oeis_a003056

theorem OMA.solution : type_of% @OMA.S_oeis_a003056.main := OMA.S_oeis_a003056.product_formula
