import OMAReductions.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

/-!
# Cassels-Ellison-Pfister 定理（Motzkin 多项式非三平方和）的规约

本文件将 `PfisterPythagorasNumber.pfister_problem.variants.lower_bound.R1.H1`
规约为两个独立且经典的数学定理：
- `H1`：Cassels 定理（1964），实单变量有理函数域 `ℝ(x)` 上的多项式若在 `ℝ(x)(y)` 中表为
  `m` 个平方和，则在多项式环 `ℝ(x)[y]` 中已可表为 `m` 个平方和；
- `H2`：Cassels-Ellison-Pfister 椭圆曲线定理（1971），曲线
  `v^2 = (u - 2x)(u + 2x)(u - (x^4 - 3x^2))` 上的任意 `ℝ(x)`-有理点 `(u, v)`，若满足
  `x^4 - 3x^2 - u` 是 `ℝ(x)` 中的三平方和，则必为退化挠点 `x^4 - 3x^2 - u = 0`。
-/

-- Reduction PfisterPythagorasNumber.pfister_problem.variants.lower_bound.R1.H1.R1
-- Credit: @volskew90

open scoped Polynomial

namespace OMA.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1_H1_R1

/-- Cassels 定理（1964）：`ℝ(x)[y]` 中的多项式若在 `ℝ(x)(y)` 中为 `m` 平方和，则在 `ℝ(x)[y]` 中亦然。 -/
def H1 : Prop :=
  ∀ (m : ℕ) (f : Polynomial (RatFunc ℝ)),
    IsSumSqOfLength m (algebraMap (Polynomial (RatFunc ℝ)) (RatFunc (RatFunc ℝ)) f) →
    IsSumSqOfLength m f

/-- Cassels-Ellison-Pfister 椭圆曲线障碍定理（1971）：Motzkin 伴随椭圆曲线在 `ℝ(x)` 上无非退化实正有理点。 -/
def H2 : Prop :=
  ∀ (u v : RatFunc ℝ),
    let x : RatFunc ℝ := algebraMap (Polynomial ℝ) (RatFunc ℝ) Polynomial.X
    v ^ 2 = (u - 2 * x) * (u + 2 * x) * (u - (x ^ 4 - 3 * x ^ 2)) →
    IsSumSqOfLength 3 (x ^ 4 - 3 * x ^ 2 - u) →
    x ^ 4 - 3 * x ^ 2 - u = 0

section Proof

-- 非零实系数多项式在任意给定实数下界右侧必有非零求值点
private lemma exists_eval_ne_zero_ge {p : ℝ[X]} (hp : p ≠ 0) (c : ℝ) :
    ∃ t : ℝ, c ≤ t ∧ p.eval t ≠ 0 := by
  obtain ⟨t, htc, hmem⟩ := (Set.Ici_infinite c).exists_notMem_finset p.roots.toFinset
  refine ⟨t, htc, fun h0 => hmem ?_⟩
  rwa [Multiset.mem_toFinset, Polynomial.mem_roots hp]

-- 实系数多项式的平方和为零则每项皆为零
private lemma real_poly_sum_sq_zero {n : ℕ} {p : Fin n → ℝ[X]}
    (hp : ∑ i, p i * p i = 0) : ∀ i, p i = 0 := by
  intro i
  by_contra hne
  obtain ⟨t, _, hpt⟩ := exists_eval_ne_zero_ge hne 0
  have hev := congr_arg (Polynomial.eval t) hp
  simp only [Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_zero] at hev
  have hnonneg : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (p j).eval t * (p j).eval t :=
    fun j _ => mul_self_nonneg _
  have hi0 := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hev i (Finset.mem_univ i)
  exact hpt (mul_self_eq_zero.mp hi0)

-- 单变量有理函数域 ℝ(x) 的形式实性：平方和为零则每项皆为零
private lemma ratFunc_sum_sq_zero {n : ℕ} {c : Fin n → RatFunc ℝ}
    (hc : ∑ i, c i * c i = 0) : ∀ i, c i = 0 := by
  choose num den hden hfrac using fun i => IsFractionRing.div_surjective ℝ[X] (c i)
  let B : ℝ[X] := ∏ j : Fin n, den j
  have hB : B ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => mem_nonZeroDivisors_iff_ne_zero.mp (hden j)
  let p : Fin n → ℝ[X] := fun i => num i * ∏ j ∈ Finset.univ.erase i, den j
  have hp_eq : ∀ i, algebraMap ℝ[X] (RatFunc ℝ) (p i) = algebraMap ℝ[X] (RatFunc ℝ) B * c i := by
    intro i
    have hBi : B = den i * ∏ j ∈ Finset.univ.erase i, den j := by
      dsimp only [B]
      rw [← Finset.mul_prod_erase Finset.univ den (Finset.mem_univ i)]
    have hdi0 : algebraMap ℝ[X] (RatFunc ℝ) (den i) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℝ[X] (RatFunc ℝ))).mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp (hden i))
    rw [← hfrac i]
    simp only [p, map_mul, map_prod, hBi]
    field_simp [hdi0]
  have hp_sum : ∑ i, p i * p i = 0 := by
    apply IsFractionRing.injective ℝ[X] (RatFunc ℝ)
    simp only [map_sum, map_mul, map_zero]
    have hmul : ∑ i : Fin n, algebraMap ℝ[X] (RatFunc ℝ) (p i) * algebraMap ℝ[X] (RatFunc ℝ) (p i) =
        algebraMap ℝ[X] (RatFunc ℝ) B * algebraMap ℝ[X] (RatFunc ℝ) B * ∑ i : Fin n, c i * c i := by
      simp only [hp_eq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => by ring
    rw [hc, mul_zero] at hmul
    exact hmul
  have hp0 := real_poly_sum_sq_zero hp_sum
  have hBK : algebraMap ℝ[X] (RatFunc ℝ) B ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective ℝ[X] (RatFunc ℝ))).mpr hB
  intro i
  have hmul := hp_eq i
  rw [hp0 i, map_zero] at hmul
  exact (mul_eq_zero.mp hmul.symm).resolve_left hBK

-- 在射线 [c, +∞) 上恒负的实多项式在 ℝ(x) 中不可能是平方和
private lemma not_sum_sq_of_neg_on_Ici {n : ℕ} {q : ℝ[X]} (c : ℝ)
    (hneg : ∀ t : ℝ, c ≤ t → q.eval t < 0) :
    ¬ IsSumSqOfLength n (algebraMap ℝ[X] (RatFunc ℝ) q) := by
  rintro ⟨g, hg⟩
  choose num den hden hfrac using fun i => IsFractionRing.div_surjective ℝ[X] (g i)
  let B : ℝ[X] := ∏ j : Fin n, den j
  have hB : B ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => mem_nonZeroDivisors_iff_ne_zero.mp (hden j)
  let p : Fin n → ℝ[X] := fun i => num i * ∏ j ∈ Finset.univ.erase i, den j
  have hp_eq : ∀ i, algebraMap ℝ[X] (RatFunc ℝ) (p i) = algebraMap ℝ[X] (RatFunc ℝ) B * g i := by
    intro i
    have hBi : B = den i * ∏ j ∈ Finset.univ.erase i, den j := by
      dsimp only [B]
      rw [← Finset.mul_prod_erase Finset.univ den (Finset.mem_univ i)]
    have hdi0 : algebraMap ℝ[X] (RatFunc ℝ) (den i) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective ℝ[X] (RatFunc ℝ))).mpr
        (mem_nonZeroDivisors_iff_ne_zero.mp (hden i))
    rw [← hfrac i]
    simp only [p, map_mul, map_prod, hBi]
    field_simp [hdi0]
  have hpoly : B * B * q = ∑ i : Fin n, p i * p i := by
    apply IsFractionRing.injective ℝ[X] (RatFunc ℝ)
    simp only [map_sum, map_mul]
    calc
      algebraMap ℝ[X] (RatFunc ℝ) B * algebraMap ℝ[X] (RatFunc ℝ) B * algebraMap ℝ[X] (RatFunc ℝ) q
          = algebraMap ℝ[X] (RatFunc ℝ) B * algebraMap ℝ[X] (RatFunc ℝ) B * ∑ i : Fin n, g i * g i := by
              rw [hg]
      _ = ∑ i : Fin n, algebraMap ℝ[X] (RatFunc ℝ) (p i) * algebraMap ℝ[X] (RatFunc ℝ) (p i) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [hp_eq i]
              ring
  obtain ⟨t, htc, hBt⟩ := exists_eval_ne_zero_ge hB c
  have hev := congr_arg (Polynomial.eval t) hpoly
  simp only [Polynomial.eval_mul, Polynomial.eval_finset_sum] at hev
  have hrhs : 0 ≤ ∑ i : Fin n, (p i).eval t * (p i).eval t :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hBpos : 0 < B.eval t * B.eval t := mul_self_pos.mpr hBt
  have hqneg : q.eval t < 0 := hneg t htc
  nlinarith

-- 多项式平方在偶数最高次项处的系数公式
private lemma coeff_two_mul_sq {R : Type*} [CommRing R] {D : ℕ} {p : R[X]}
    (hp : p.natDegree ≤ D) : (p * p).coeff (2 * D) = p.coeff D * p.coeff D := by
  rw [Polynomial.coeff_mul, Finset.sum_eq_single (D, D)]
  · rintro ⟨a, b⟩ hab hne
    have hab' : a + b = 2 * D := by simpa using hab
    have hcases : D < a ∨ D < b := by
      by_contra h
      push Not at h
      exact hne (Prod.ext (by omega) (by omega))
    rcases hcases with ha | hb
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp ha), zero_mul]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp hb), mul_zero]
  · intro h
    exfalso
    exact h (by simp [Nat.two_mul])

-- ℝ(x)[y] 中平方和的次数控制：若平方和的次数不超过 4，则每项次数不超过 2
private lemma natDegree_le_two_of_sum_sq {n : ℕ} {p : Fin n → (RatFunc ℝ)[X]} {M : (RatFunc ℝ)[X]}
    (hM : M.natDegree ≤ 4) (heq : M = ∑ i, p i * p i) :
    ∀ i, (p i).natDegree ≤ 2 := by
  by_contra hgt
  push Not at hgt
  let D : ℕ := Finset.univ.sup fun i => (p i).natDegree
  have hD3 : 3 ≤ D := by
    obtain ⟨i0, hi0⟩ := hgt
    exact le_trans hi0 (Finset.le_sup (f := fun i => (p i).natDegree) (Finset.mem_univ i0))
  have hle : ∀ i, (p i).natDegree ≤ D := fun i =>
    Finset.le_sup (f := fun i => (p i).natDegree) (Finset.mem_univ i)
  have hM0 : M.coeff (2 * D) = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  have hsum : ∑ i : Fin n, (p i).coeff D * (p i).coeff D = 0 := by
    have hc := congr_arg (fun r => r.coeff (2 * D)) heq
    rw [hM0, Polynomial.finsetSum_coeff] at hc
    have hsq : ∑ i : Fin n, (p i * p i).coeff (2 * D) = ∑ i : Fin n, (p i).coeff D * (p i).coeff D :=
      Finset.sum_congr rfl fun i _ => coeff_two_mul_sq (hle i)
    exact hsq.symm.trans hc.symm
  have hc0 := ratFunc_sum_sq_zero hsum
  obtain ⟨i0, hi0⟩ := hgt
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ ⟨i0, Finset.mem_univ i0⟩
    (fun i => (p i).natDegree)
  have hj_ne : p j ≠ 0 := by
    intro hz
    rw [hz, Polynomial.natDegree_zero] at hj
    omega
  have hlead := hc0 j
  dsimp only [D] at hlead
  rw [hj] at hlead
  exact hj_ne (Polynomial.leadingCoeff_eq_zero.mp hlead)

-- 次数不超过 2 的多项式展开为二次三项式
private lemma eq_quadratic_of_natDegree_le_two {R : Type*} [Semiring R] {p : R[X]}
    (hp : p.natDegree ≤ 2) :
    p = Polynomial.C (p.coeff 2) * Polynomial.X ^ 2 +
        Polynomial.C (p.coeff 1) * Polynomial.X +
        Polynomial.C (p.coeff 0) := by
  ext k
  rcases k with _ | _ | _ | k
  · simp
  · simp
  · simp
  · simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

-- 将二元有理函数域 ℝ(X_0, X_1) 中的 Motzkin 多项式嵌入单变量迭代有理函数域 ℝ(x)(y)
private lemma motzkin_embed_sum_sq
    (h : IsSumSqOfLength 3 (algebraMap (MvPolynomial (Fin 2) ℝ) (MvRatFunc (Fin 2) ℝ)
      (1 + MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4 +
        MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 2 -
        3 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2))) :
    let x : RatFunc ℝ := algebraMap ℝ[X] (RatFunc ℝ) Polynomial.X
    IsSumSqOfLength 3 (algebraMap (RatFunc ℝ)[X] (RatFunc (RatFunc ℝ))
      (Polynomial.C (x ^ 2) * Polynomial.X ^ 4 +
        Polynomial.C (x ^ 4 - 3 * x ^ 2) * Polynomial.X ^ 2 + 1)) := by
  intro x
  obtain ⟨f, hf⟩ := h
  let coeffHom : MvPolynomial (Fin 1) ℝ →+* RatFunc ℝ :=
    (algebraMap ℝ[X] (RatFunc ℝ)).comp (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).toRingEquiv.toRingHom
  have hcoeff_inj : Function.Injective coeffHom :=
    (IsFractionRing.injective ℝ[X] (RatFunc ℝ)).comp (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)).injective
  let polyHom : MvPolynomial (Fin 2) ℝ →+* (RatFunc ℝ)[X] :=
    (Polynomial.mapRingHom coeffHom).comp (MvPolynomial.finSuccEquiv ℝ 1).toRingEquiv.toRingHom
  have hpoly_inj : Function.Injective polyHom :=
    (Polynomial.map_injective _ hcoeff_inj).comp (MvPolynomial.finSuccEquiv ℝ 1).injective
  let ratHom : MvPolynomial (Fin 2) ℝ →+* RatFunc (RatFunc ℝ) :=
    (algebraMap (RatFunc ℝ)[X] (RatFunc (RatFunc ℝ))).comp polyHom
  have hrat_inj : Function.Injective ratHom :=
    (IsFractionRing.injective (RatFunc ℝ)[X] (RatFunc (RatFunc ℝ))).comp hpoly_inj
  let Φ : MvRatFunc (Fin 2) ℝ →+* RatFunc (RatFunc ℝ) := IsFractionRing.lift hrat_inj
  have hX0 : polyHom (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
    simp [polyHom, MvPolynomial.finSuccEquiv_X_zero]
  have hX1 : polyHom (MvPolynomial.X (1 : Fin 2)) = Polynomial.C x := by
    change Polynomial.map coeffHom (MvPolynomial.finSuccEquiv ℝ 1 (MvPolynomial.X (Fin.succ 0))) =
      Polynomial.C x
    rw [MvPolynomial.finSuccEquiv_X_succ, Polynomial.map_C]
    simp [coeffHom, x]
  have hmap : Φ (algebraMap (MvPolynomial (Fin 2) ℝ) (MvRatFunc (Fin 2) ℝ)
      (1 + MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 4 +
        MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 2 -
        3 * MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)) =
      algebraMap (RatFunc ℝ)[X] (RatFunc (RatFunc ℝ))
        (Polynomial.C (x ^ 2) * Polynomial.X ^ 4 +
          Polynomial.C (x ^ 4 - 3 * x ^ 2) * Polynomial.X ^ 2 + 1) := by
    rw [IsFractionRing.lift_algebraMap hrat_inj]
    change algebraMap (RatFunc ℝ)[X] (RatFunc (RatFunc ℝ)) (polyHom _) = _
    congr 1
    simp only [map_sub, map_add, map_mul, map_pow, map_one, map_ofNat, hX0, hX1]
    ring
  refine ⟨fun i => Φ (f i), ?_⟩
  rw [← hmap, hf, map_sum]
  exact Finset.sum_congr rfl fun i _ => map_mul Φ (f i) (f i)

theorem main : H1 → H2 →
    OMA.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1.H1 := by
  intro hcassels hcurve hmotz
  let x : RatFunc ℝ := algebraMap ℝ[X] (RatFunc ℝ) Polynomial.X
  let M : (RatFunc ℝ)[X] :=
    Polynomial.C (x ^ 2) * Polynomial.X ^ 4 +
    Polynomial.C (x ^ 4 - 3 * x ^ 2) * Polynomial.X ^ 2 + 1
  obtain ⟨p, hp⟩ := hcassels 3 M (motzkin_embed_sum_sq hmotz)
  have hMdeg : M.natDegree ≤ 4 := by
    dsimp only [M]
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
    · exact Polynomial.natDegree_C_mul_X_pow_le _ 4
    · exact (Polynomial.natDegree_C_mul_X_pow_le _ 2).trans (by omega)
  have hpdeg := natDegree_le_two_of_sum_sq hMdeg hp
  rw [Fin.sum_univ_three] at hp
  set a₀ := (p 0).coeff 2; set b₀ := (p 0).coeff 1; set c₀ := (p 0).coeff 0
  set a₁ := (p 1).coeff 2; set b₁ := (p 1).coeff 1; set c₁ := (p 1).coeff 0
  set a₂ := (p 2).coeff 2; set b₂ := (p 2).coeff 1; set c₂ := (p 2).coeff 0
  have hexp : M =
      Polynomial.C (a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2) * Polynomial.X ^ 4 +
      Polynomial.C (2 * (a₀ * b₀ + a₁ * b₁ + a₂ * b₂)) * Polynomial.X ^ 3 +
      Polynomial.C (b₀ ^ 2 + b₁ ^ 2 + b₂ ^ 2 + 2 * (a₀ * c₀ + a₁ * c₁ + a₂ * c₂)) * Polynomial.X ^ 2 +
      Polynomial.C (2 * (b₀ * c₀ + b₁ * c₁ + b₂ * c₂)) * Polynomial.X +
      Polynomial.C (c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2) := by
    rw [hp, eq_quadratic_of_natDegree_le_two (hpdeg 0),
      eq_quadratic_of_natDegree_le_two (hpdeg 1),
      eq_quadratic_of_natDegree_le_two (hpdeg 2)]
    simp only [map_add, map_mul, map_pow, map_ofNat]
    ring
  have hcf := fun k : ℕ => congr_arg (fun q => q.coeff k) hexp
  have e4 : a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2 = x ^ 2 := by
    have h := hcf 4
    simp only [M, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one] at h
    norm_num at h; exact h.symm
  have e3 : a₀ * b₀ + a₁ * b₁ + a₂ * b₂ = 0 := by
    have h := hcf 3
    simp only [M, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one] at h
    norm_num at h; exact h
  have e2 : b₀ ^ 2 + b₁ ^ 2 + b₂ ^ 2 + 2 * (a₀ * c₀ + a₁ * c₁ + a₂ * c₂) = x ^ 4 - 3 * x ^ 2 := by
    have h := hcf 2
    simp only [M, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one] at h
    norm_num at h; exact h.symm
  have e1 : b₀ * c₀ + b₁ * c₁ + b₂ * c₂ = 0 := by
    have h := hcf 1
    simp only [M, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one] at h
    norm_num at h; exact h
  have e0 : c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2 = 1 := by
    have h := hcf 0
    simp only [M, Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
      Polynomial.coeff_X, Polynomial.coeff_C, Polynomial.coeff_one] at h
    norm_num at h; exact h.symm
  let u : RatFunc ℝ := 2 * (a₀ * c₀ + a₁ * c₁ + a₂ * c₂)
  let v : RatFunc ℝ :=
    2 * (a₀ * (c₁ * b₂ - c₂ * b₁) + a₁ * (c₂ * b₀ - c₀ * b₂) + a₂ * (c₀ * b₁ - c₁ * b₀))
  have hb_eq : x ^ 4 - 3 * x ^ 2 - u = b₀ ^ 2 + b₁ ^ 2 + b₂ ^ 2 := by
    dsimp only [u]; linear_combination -e2
  have huv : v ^ 2 = (u - 2 * x) * (u + 2 * x) * (u - (x ^ 4 - 3 * x ^ 2)) := by
    have hid :
        4 * (a₀ * (c₁ * b₂ - c₂ * b₁) + a₁ * (c₂ * b₀ - c₀ * b₂) + a₂ * (c₀ * b₁ - c₁ * b₀)) ^ 2 +
        4 * ((a₀ * b₀ + a₁ * b₁ + a₂ * b₂) * c₀ - (b₀ * c₀ + b₁ * c₁ + b₂ * c₂) * a₀) ^ 2 +
        4 * ((a₀ * b₀ + a₁ * b₁ + a₂ * b₂) * c₁ - (b₀ * c₀ + b₁ * c₁ + b₂ * c₂) * a₁) ^ 2 +
        4 * ((a₀ * b₀ + a₁ * b₁ + a₂ * b₂) * c₂ - (b₀ * c₀ + b₁ * c₁ + b₂ * c₂) * a₂) ^ 2 =
        (4 * (a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2) * (c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2) -
          (2 * (a₀ * c₀ + a₁ * c₁ + a₂ * c₂)) ^ 2) * (b₀ ^ 2 + b₁ ^ 2 + b₂ ^ 2) := by ring
    rw [e3, e1, e4, e0] at hid
    have hv2 : v ^ 2 = (4 * x ^ 2 - u ^ 2) * (b₀ ^ 2 + b₁ ^ 2 + b₂ ^ 2) := by
      dsimp only [v, u]; linear_combination hid
    rw [hv2, ← hb_eq]; ring
  have hb_sq : IsSumSqOfLength 3 (x ^ 4 - 3 * x ^ 2 - u) := by
    refine ⟨![b₀, b₁, b₂], ?_⟩
    rw [hb_eq, Fin.sum_univ_three]
    simp [sq]
  have hu0 : x ^ 4 - 3 * x ^ 2 - u = 0 := hcurve u v huv hb_sq
  have hu_eq : u = x ^ 4 - 3 * x ^ 2 := by linear_combination -hu0
  have hlag : 4 * x ^ 2 - (x ^ 4 - 3 * x ^ 2) ^ 2 =
      (2 * (a₁ * c₂ - a₂ * c₁)) ^ 2 + (2 * (a₂ * c₀ - a₀ * c₂)) ^ 2 +
      (2 * (a₀ * c₁ - a₁ * c₀)) ^ 2 := by
    have hid2 :
        4 * (a₀ ^ 2 + a₁ ^ 2 + a₂ ^ 2) * (c₀ ^ 2 + c₁ ^ 2 + c₂ ^ 2) -
        (2 * (a₀ * c₀ + a₁ * c₁ + a₂ * c₂)) ^ 2 =
        (2 * (a₁ * c₂ - a₂ * c₁)) ^ 2 + (2 * (a₂ * c₀ - a₀ * c₂)) ^ 2 +
        (2 * (a₀ * c₁ - a₁ * c₀)) ^ 2 := by ring
    rw [e4, e0, mul_one] at hid2
    change 4 * x ^ 2 - u ^ 2 = _ at hid2
    rwa [hu_eq] at hid2
  have hbad : IsSumSqOfLength 3 (algebraMap ℝ[X] (RatFunc ℝ)
      (4 * Polynomial.X ^ 2 - (Polynomial.X ^ 4 - 3 * Polynomial.X ^ 2) ^ 2)) := by
    refine ⟨![2 * (a₁ * c₂ - a₂ * c₁), 2 * (a₂ * c₀ - a₀ * c₂), 2 * (a₀ * c₁ - a₁ * c₀)], ?_⟩
    simp only [map_sub, map_mul, map_pow, map_ofNat, Fin.sum_univ_three]
    change 4 * x ^ 2 - (x ^ 4 - 3 * x ^ 2) ^ 2 = _
    rw [hlag]; simp [sq]
  exact not_sum_sq_of_neg_on_Ici 3 (fun t ht => by
    simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_ofNat]
    have ht2 : 9 ≤ t ^ 2 := by nlinarith
    have ht4 : 54 ≤ t ^ 4 - 3 * t ^ 2 := by nlinarith
    nlinarith) hbad

end Proof

end OMA.R_PfisterPythagorasNumber_pfister_problem_variants_lower_bound_R1_H1_R1
