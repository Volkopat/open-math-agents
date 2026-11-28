import OMAReductions.R_Erdos6_erdos_6_variants_increasing_R1_H1_R1_H2_R2
import Mathlib

-- Step Erdos6.erdos_6.variants.increasing.R1.H1.R1.H2.R2.H2: hypothesis H2 of reduction Erdos6.erdos_6.variants.increasing.R1.H1.R1.H2.R2
-- Credit: @JamesSlash (port). Mathematics and Lean proof of Vaughan's Basic Mean Value Theorem by
-- Jonas Whidden (@kimihiro64), Bombieri-Vinogradov in Lean, https://github.com/kimihiro64/bombieri-vinogradov
-- (Apache License 2.0). The 64 modules in the import closure of
-- BombieriVinogradov.Assembly.VaughanMeanValue.RealEndpoint.Main are flattened below in dependency order,
-- with comments, imports and the autoImplicit option removed; the code is otherwise unchanged.
-- The final bridge (OMA.solution) is new: it specialises the real cutoff to natural x and drops the
-- principal character from the primitive-character sum.

noncomputable section

section
noncomputable section
open Finset
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
theorem sum_divisorsAntidiagonal_Icc_eq_hyperbola
    {A : Type*} [AddCommMonoid A] (F : Nat -> Nat -> A) (y : Nat) :
    ∑ n ∈ Icc 1 y, ∑ pair ∈ Nat.divisorsAntidiagonal n,
        F pair.1 pair.2 =
      ∑ m ∈ Icc 1 y, ∑ k ∈ Icc 1 (y / m), F m k := by
  classical
  rw [Finset.sum_sigma', Finset.sum_sigma']
  apply Finset.sum_bij
    (fun x _ => Sigma.mk x.2.1 x.2.2)
  · intro x hx
    rcases Finset.mem_sigma.mp hx with ⟨hn, hp⟩
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hprod, hn0⟩
    have hm0 : Ne x.2.1 0 := Nat.left_ne_zero_of_mem_divisorsAntidiagonal hp
    have hk0 : Ne x.2.2 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
    apply Finset.mem_sigma.mpr
    constructor
    · exact Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr hm0, by
        calc
          x.2.1 <= x.2.1 * x.2.2 :=
            Nat.le_mul_of_pos_right x.2.1 (Nat.pos_of_ne_zero hk0)
          _ = x.1 := hprod
          _ <= y := (Finset.mem_Icc.mp hn).2⟩
    · apply Finset.mem_Icc.mpr
      constructor
      · exact Nat.one_le_iff_ne_zero.mpr hk0
      · apply (Nat.le_div_iff_mul_le (Nat.pos_of_ne_zero hm0)).mpr
        simpa [Nat.mul_comm, hprod] using (Finset.mem_Icc.mp hn).2
  · intro x hx z hz heq
    rcases x with ⟨n, ⟨m, k⟩⟩
    rcases z with ⟨n', ⟨m', k'⟩⟩
    simp only [Sigma.mk.injEq] at heq
    rcases heq with ⟨rfl, rfl⟩
    have hxprod := (Nat.mem_divisorsAntidiagonal.mp
      (Finset.mem_sigma.mp hx).2).1
    have hzprod := (Nat.mem_divisorsAntidiagonal.mp
      (Finset.mem_sigma.mp hz).2).1
    have hnn : n = n' := hxprod.symm.trans hzprod
    cases hnn
    rfl
  · intro z hz
    rcases z with ⟨m, k⟩
    rcases Finset.mem_sigma.mp hz with ⟨hm, hk⟩
    have hmpos : 0 < m := (Finset.mem_Icc.mp hm).1
    have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
    have hprod : m * k <= y :=
      (by
        have := (Nat.le_div_iff_mul_le hmpos).mp (Finset.mem_Icc.mp hk).2
        simpa [Nat.mul_comm] using this)
    refine ⟨Sigma.mk (m * k) (m, k), ?_, ?_⟩
    · apply Finset.mem_sigma.mpr
      constructor
      · exact Finset.mem_Icc.mpr ⟨Nat.mul_pos hmpos hkpos, hprod⟩
      · exact Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,
          (Nat.mul_pos hmpos hkpos).ne'⟩
    · rfl
  · intro x hx
    rfl
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Finset
open scoped BigOperators
namespace BombieriVinogradov.LargeSieve
def primitiveCharacters (q : Nat) : Finset (DirichletCharacter Complex q) := by
  classical
  exact Finset.univ.filter DirichletCharacter.IsPrimitive
def intervalCharacterSum (a : Int -> Complex) (M : Int) (N q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ n ∈ Ioc M (M + (N : Int)), a n * chi (n : ZMod q)
def unitCharacterSum {q : Nat} (a : (ZMod q)ˣ -> Complex)
    (chi : DirichletCharacter Complex q) : Complex := by
  letI : Fintype (ZMod q)ˣ := Fintype.ofFinite _
  exact ∑ x, a x * chi (x : ZMod q)
def CharacterLargeSieveStatement : Prop :=
  Exists fun C : Real =>
    0 < C ∧
      ∀ (M : Int) (N Q : Nat) (a : Int -> Complex), 1 <= Q ->
        ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
            ∑ chi ∈ primitiveCharacters q,
              ‖intervalCharacterSum a M N q chi‖ ^ 2 <=
          C * ((N : Real) + (Q : Real) ^ 2) *
            ∑ n ∈ Ioc M (M + (N : Int)), ‖a n‖ ^ 2
end BombieriVinogradov.LargeSieve
end
end

section
noncomputable section
open Finset
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
def psiCharacterSum (y q : Nat) (chi : DirichletCharacter Complex q) : Complex :=
  ∑ n ∈ Icc 1 y,
    (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod q)
def maximalPsiNorm (x : Real) {q : Nat}
    (chi : DirichletCharacter Complex q) : Real :=
  (range (⌊x⌋₊ + 1)).sup' (by simp) fun y => ‖psiCharacterSum y q chi‖
def primitivePsiMean (x : Real) (Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalPsiNorm x chi
def basicMeanValueMajorant (x : Real) (Q : Nat) : Real :=
  (x + x ^ (5 / 6 : Real) * (Q : Real) +
      x ^ (1 / 2 : Real) * (Q : Real) ^ 2) *
    Real.log (x * (Q : Real)) ^ 3
def VaughanMeanValueStatement : Prop :=
  Exists fun C : Real =>
    0 < C ∧ ∀ (x : Real) (Q : Nat), 2 <= x -> 1 <= Q ->
      primitivePsiMean x Q <= C * basicMeanValueMajorant x Q
def restrictedBilinearCharacterSum (a b : Nat -> Complex)
    (M N Y q : Nat) (chi : DirichletCharacter Complex q) : Complex :=
  ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
    if m * n <= Y then a m * b n * chi ((m * n : Nat) : ZMod q) else 0
def maximalBilinearNorm (a b : Nat -> Complex)
    (M N X : Nat) {q : Nat} (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖restrictedBilinearCharacterSum a b M N Y q chi‖
def coefficientMass (a : Nat -> Complex) (M : Nat) : Real :=
  ∑ m ∈ Icc 1 M, ‖a m‖ ^ 2
def MaximalBilinearLargeSieveStatement : Prop :=
  Exists fun C : Real =>
    0 < C ∧
      ∀ (X M N Q : Nat) (a b : Nat -> Complex),
        2 <= X -> 1 <= M -> 1 <= N -> 1 <= Q ->
          ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
              ∑ chi ∈ primitiveCharacters q,
                maximalBilinearNorm a b M N X chi <=
            C * Real.log ((X * M * N : Nat) : Real) *
              Real.sqrt (((M : Real) + (Q : Real) ^ 2) *
                ((N : Real) + (Q : Real) ^ 2) *
                coefficientMass a M * coefficientMass b N)
def positiveIntervalCoefficients (a : Nat -> Complex) (n : Int) : Complex :=
  a n.toNat
def positiveCharacterSum (a : Nat -> Complex) (M q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  intervalCharacterSum (positiveIntervalCoefficients a) 0 M q chi
def positiveCoefficientMass (a : Nat -> Complex) (M : Nat) : Real :=
  ∑ n ∈ Ioc (0 : Int) (M : Int), ‖positiveIntervalCoefficients a n‖ ^ 2
def bilinearCharacterProduct (a b : Nat -> Complex) (M N q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  positiveCharacterSum a M q chi * positiveCharacterSum b N q chi
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Finset
open scoped BigOperators
namespace BombieriVinogradov.LargeSieve
theorem star_stdAddChar_apply {q : Nat} [NeZero q] (x : ZMod q) :
    star (ZMod.stdAddChar x) = ZMod.stdAddChar (-x) := by
  have hq : 0 < ringChar (ZMod q) := by
    rw [ZMod.ringChar_zmod_n]
    exact Nat.pos_of_ne_zero (NeZero.ne q)
  simpa only [RCLike.star_def, AddChar.inv_apply] using
    (AddChar.starComp_apply hq (φ := ZMod.stdAddChar) x)
theorem stdAddCharOrthogonality {q : Nat} [NeZero q] (x y : ZMod q) :
    (∑ a : ZMod q,
        star (ZMod.stdAddChar (x * a)) * ZMod.stdAddChar (y * a)) =
      if x = y then (q : Complex) else 0 := by
  have rearrange (a : ZMod q) : -(x * a) + y * a = a * (y - x) := by
    ring
  simp_rw [star_stdAddChar_apply, ← AddChar.map_add_eq_mul, rearrange]
  simpa [sub_eq_zero, eq_comm] using
    (AddChar.sum_mulShift (R := ZMod q) (R' := Complex) (y - x)
      (ZMod.isPrimitive_stdAddChar q))
def additiveTransform {q : Nat} [NeZero q] (f : ZMod q -> Complex)
    (a : ZMod q) : Complex :=
  ∑ x, f x * ZMod.stdAddChar (x * a)
theorem additiveParseval {q : Nat} [NeZero q] (f : ZMod q -> Complex) :
    (∑ a : ZMod q, star (additiveTransform f a) * additiveTransform f a) =
      (q : Complex) * ∑ x, star (f x) * f x := by
  classical
  unfold additiveTransform
  simp_rw [star_sum, star_mul, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, x]
    rw [Finset.sum_comm]
  have rearrange (a x y : ZMod q) :
      star (ZMod.stdAddChar (x * a)) * star (f x) *
          (f y * ZMod.stdAddChar (y * a)) =
        (star (f x) * f y) *
          (star (ZMod.stdAddChar (x * a)) * ZMod.stdAddChar (y * a)) := by
    ring
  simp_rw [rearrange]
  simp_rw [← Finset.mul_sum]
  simp_rw [stdAddCharOrthogonality]
  simp [mul_ite]
  rw [← Finset.sum_mul]
  ring
theorem additiveParseval_normSq {q : Nat} [NeZero q]
    (f : ZMod q -> Complex) :
    (∑ a : ZMod q, ‖additiveTransform f a‖ ^ 2) =
      (q : Real) * ∑ x, ‖f x‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp_rw [← Complex.normSq_eq_norm_sq]
  push_cast
  simpa only [Complex.normSq_eq_conj_mul_self, RCLike.star_def] using
    (additiveParseval f)
end BombieriVinogradov.LargeSieve
end
end

section
noncomputable section
open Finset
open scoped BigOperators
namespace BombieriVinogradov.LargeSieve
noncomputable local instance unitFintype (q : Nat) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _
theorem primitiveSum_le_all (q : Nat) (f : DirichletCharacter Complex q -> Real)
    (hf : ∀ chi, 0 <= f chi) :
    ∑ chi ∈ primitiveCharacters q, f chi <= ∑ chi, f chi := by
  classical
  exact Finset.sum_le_univ_sum_of_nonneg (s := primitiveCharacters q) hf
theorem star_character_apply_unit {q : Nat} (chi : DirichletCharacter Complex q)
    (x : (ZMod q)ˣ) :
    star (chi (x : ZMod q)) = chi ((x : ZMod q)⁻¹) := by
  rw [MulChar.star_apply']
  rw [MulChar.inv_apply_eq_inv']
  simp
theorem characterOrthogonalityOnUnits {q : Nat} [NeZero q]
    (x y : (ZMod q)ˣ) :
    (∑ chi : DirichletCharacter Complex q,
        star (chi (x : ZMod q)) * chi (y : ZMod q)) =
      if x = y then (q.totient : Complex) else 0 := by
  simp_rw [star_character_apply_unit]
  simpa only [Units.val_inj] using
    (DirichletCharacter.sum_char_inv_mul_char_eq (R := Complex)
      x.isUnit (y : ZMod q))
theorem characterParseval {q : Nat} [NeZero q]
    (a : (ZMod q)ˣ -> Complex) :
    (∑ chi : DirichletCharacter Complex q,
        star (unitCharacterSum a chi) * unitCharacterSum a chi) =
      (q.totient : Complex) * ∑ x, star (a x) * a x := by
  classical
  unfold unitCharacterSum
  simp_rw [star_sum, star_mul, Fintype.sum_mul_sum]
  rw [Finset.sum_comm]
  conv_lhs =>
    enter [2, y]
    rw [Finset.sum_comm]
  have rearrange (chi : DirichletCharacter Complex q) (x y : (ZMod q)ˣ) :
      star (chi (x : ZMod q)) * star (a x) *
          (a y * chi (y : ZMod q)) =
        (star (a x) * a y) *
          (star (chi (x : ZMod q)) * chi (y : ZMod q)) := by
    ring
  simp_rw [rearrange]
  simp_rw [← Finset.mul_sum]
  simp_rw [characterOrthogonalityOnUnits]
  simp [mul_ite]
  rw [← Finset.sum_mul]
  ring
theorem characterParseval_normSq {q : Nat} [NeZero q]
    (a : (ZMod q)ˣ -> Complex) :
    (∑ chi : DirichletCharacter Complex q, ‖unitCharacterSum a chi‖ ^ 2) =
      (q.totient : Real) * ∑ x, ‖a x‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp_rw [← Complex.normSq_eq_norm_sq]
  push_cast
  simpa only [Complex.normSq_eq_conj_mul_self, RCLike.star_def] using
    (characterParseval a)
theorem primitiveCharacterParseval_le {q : Nat} [NeZero q]
    (a : (ZMod q)ˣ -> Complex) :
    ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum a chi‖ ^ 2 <=
      (q.totient : Real) * ∑ x, ‖a x‖ ^ 2 := by
  calc
    _ <= ∑ chi : DirichletCharacter Complex q,
        ‖unitCharacterSum a chi‖ ^ 2 :=
      primitiveSum_le_all q _ (fun chi => sq_nonneg ‖unitCharacterSum a chi‖)
    _ = _ := characterParseval_normSq a
end BombieriVinogradov.LargeSieve
end
end

section
noncomputable section
open Finset
open scoped BigOperators
namespace BombieriVinogradov.LargeSieve
theorem dirichletCharacterEnergy {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) :
    (∑ x : ZMod q, star (chi x) * chi x) = (q.totient : Complex) := by
  calc
    _ = ∑ x : ZMod q, (star chi * chi) x := by
      simp only [MulChar.star_apply, MulChar.mul_apply]
    _ = ∑ x : ZMod q, (1 : DirichletCharacter Complex q) x := by
      rw [MulChar.star_eq_inv]
      simp
    _ = _ := by
      rw [MulChar.sum_one_eq_card_units]
      norm_cast
      exact ZMod.card_units_eq_totient q
theorem gaussSumShiftParseval {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) :
    (∑ a : ZMod q,
        star (gaussSum chi ((ZMod.stdAddChar).mulShift a)) *
          gaussSum chi ((ZMod.stdAddChar).mulShift a)) =
      (q : Complex) * (q.totient : Complex) := by
  calc
    _ = ∑ a : ZMod q,
        star (additiveTransform (fun x => chi x) a) *
          additiveTransform (fun x => chi x) a := by
      simp only [additiveTransform, gaussSum, AddChar.mulShift_apply, mul_comm]
    _ = (q : Complex) * ∑ x : ZMod q, star (chi x) * chi x :=
      additiveParseval (fun x => chi x)
    _ = _ := by rw [dirichletCharacterEnergy]
theorem gaussSumShiftEnergy_of_isPrimitive {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi) :
    (∑ a : ZMod q,
        star (gaussSum chi ((ZMod.stdAddChar).mulShift a)) *
          gaussSum chi ((ZMod.stdAddChar).mulShift a)) =
      (q.totient : Complex) *
        (star (gaussSum chi ZMod.stdAddChar) * gaussSum chi ZMod.stdAddChar) := by
  simp_rw [gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hchi]
  simp_rw [star_mul]
  have rearrange (a : ZMod q) :
      star (gaussSum chi ZMod.stdAddChar) * star (chi⁻¹ a) *
          (chi⁻¹ a * gaussSum chi ZMod.stdAddChar) =
        (star (chi⁻¹ a) * chi⁻¹ a) *
          (star (gaussSum chi ZMod.stdAddChar) * gaussSum chi ZMod.stdAddChar) := by
    ring
  simp_rw [rearrange]
  rw [← Finset.sum_mul]
  rw [dirichletCharacterEnergy (chi := chi⁻¹)]
theorem gaussSum_star_mul_self_of_isPrimitive {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi) :
    star (gaussSum chi ZMod.stdAddChar) * gaussSum chi ZMod.stdAddChar =
      (q : Complex) := by
  have htotient : (q.totient : Complex) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (NeZero.pos q)).ne'
  apply mul_left_cancel₀ htotient
  calc
    (q.totient : Complex) *
        (star (gaussSum chi ZMod.stdAddChar) * gaussSum chi ZMod.stdAddChar) =
      ∑ a : ZMod q,
        star (gaussSum chi ((ZMod.stdAddChar).mulShift a)) *
          gaussSum chi ((ZMod.stdAddChar).mulShift a) :=
      (gaussSumShiftEnergy_of_isPrimitive hchi).symm
    _ = (q : Complex) * (q.totient : Complex) := gaussSumShiftParseval chi
    _ = (q.totient : Complex) * (q : Complex) := by ring
theorem normSq_gaussSum_stdAddChar {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi) :
    Complex.normSq (gaussSum chi ZMod.stdAddChar) = (q : Real) := by
  apply Complex.ofReal_injective
  push_cast
  rw [Complex.normSq_eq_conj_mul_self]
  simpa only [RCLike.star_def] using gaussSum_star_mul_self_of_isPrimitive hchi
theorem norm_gaussSum_stdAddChar_sq {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi) :
    ‖gaussSum chi ZMod.stdAddChar‖ ^ 2 = (q : Real) := by
  rw [← Complex.normSq_eq_norm_sq]
  exact normSq_gaussSum_stdAddChar hchi
end BombieriVinogradov.LargeSieve
end
end

section
open Finset
open scoped BigOperators
namespace BombieriVinogradov.LargeSieve
theorem schurBound {ι : Type*} [Fintype ι] (k : ι -> ι -> Real)
    (hk : ∀ i j, 0 <= k i j) (hsymm : ∀ i j, k i j = k j i)
    {B : Real} (hrow : ∀ i, ∑ j, k i j <= B) (b : ι -> Real) :
    ∑ i, ∑ j, b i * b j * k i j <= B * ∑ i, b i ^ 2 := by
  classical
  have hpoint (i j : ι) :
      2 * (b i * b j * k i j) <= b i ^ 2 * k i j + b j ^ 2 * k i j := by
    have hab : 2 * (b i * b j) <= b i ^ 2 + b j ^ 2 := by
      nlinarith [sq_nonneg (b i - b j)]
    nlinarith [mul_le_mul_of_nonneg_right hab (hk i j)]
  have hcol (j : ι) : ∑ i, k i j <= B := by
    calc
      ∑ i, k i j = ∑ i, k j i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hsymm i j
      _ <= B := hrow j
  have hdouble :
      2 * (∑ i, ∑ j, b i * b j * k i j) <=
        2 * (B * ∑ i, b i ^ 2) := by
    calc
      2 * (∑ i, ∑ j, b i * b j * k i j) =
          ∑ i, ∑ j, 2 * (b i * b j * k i j) := by
        simp_rw [Finset.mul_sum]
      _ <= ∑ i, ∑ j, (b i ^ 2 * k i j + b j ^ 2 * k i j) := by
        exact Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpoint i j
      _ = (∑ i, b i ^ 2 * ∑ j, k i j) +
          (∑ i, ∑ j, b j ^ 2 * k i j) := by
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (∑ i, b i ^ 2 * ∑ j, k i j) +
          (∑ j, b j ^ 2 * ∑ i, k i j) := by
        congr 1
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ <= (∑ i, b i ^ 2 * B) + (∑ j, b j ^ 2 * B) := by
        apply add_le_add
        · exact Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg (b i))
        · exact Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hcol j) (sq_nonneg (b j))
      _ = 2 * (B * ∑ i, b i ^ 2) := by
        simp_rw [← Finset.sum_mul]
        ring
  linarith
theorem schurBoundFinset {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (k : ι -> ι -> Real) (hk : ∀ i ∈ s, ∀ j ∈ s, 0 <= k i j)
    (hsymm : ∀ i ∈ s, ∀ j ∈ s, k i j = k j i)
    {B : Real} (hrow : ∀ i ∈ s, ∑ j ∈ s, k i j <= B) (b : ι -> Real) :
    ∑ i ∈ s, ∑ j ∈ s, b i * b j * k i j <=
      B * ∑ i ∈ s, b i ^ 2 := by
  have hpoint (i : ι) (hi : i ∈ s) (j : ι) (hj : j ∈ s) :
      2 * (b i * b j * k i j) <= b i ^ 2 * k i j + b j ^ 2 * k i j := by
    have hab : 2 * (b i * b j) <= b i ^ 2 + b j ^ 2 := by
      nlinarith [sq_nonneg (b i - b j)]
    nlinarith [mul_le_mul_of_nonneg_right hab (hk i hi j hj)]
  have hcol (j : ι) (hj : j ∈ s) : ∑ i ∈ s, k i j <= B := by
    calc
      ∑ i ∈ s, k i j = ∑ i ∈ s, k j i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsymm i hi j hj
      _ <= B := hrow j hj
  have hdouble :
      2 * (∑ i ∈ s, ∑ j ∈ s, b i * b j * k i j) <=
        2 * (B * ∑ i ∈ s, b i ^ 2) := by
    calc
      2 * (∑ i ∈ s, ∑ j ∈ s, b i * b j * k i j) =
          ∑ i ∈ s, ∑ j ∈ s, 2 * (b i * b j * k i j) := by
        simp_rw [Finset.mul_sum]
      _ <= ∑ i ∈ s, ∑ j ∈ s,
          (b i ^ 2 * k i j + b j ^ 2 * k i j) := by
        exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
          hpoint i hi j hj
      _ = (∑ i ∈ s, b i ^ 2 * ∑ j ∈ s, k i j) +
          (∑ i ∈ s, ∑ j ∈ s, b j ^ 2 * k i j) := by
        simp_rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (∑ i ∈ s, b i ^ 2 * ∑ j ∈ s, k i j) +
          (∑ j ∈ s, b j ^ 2 * ∑ i ∈ s, k i j) := by
        congr 1
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
      _ <= (∑ i ∈ s, b i ^ 2 * B) + (∑ j ∈ s, b j ^ 2 * B) := by
        apply add_le_add
        · exact Finset.sum_le_sum fun i hi =>
            mul_le_mul_of_nonneg_left (hrow i hi) (sq_nonneg (b i))
        · exact Finset.sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_left (hcol j hj) (sq_nonneg (b j))
      _ = 2 * (B * ∑ i ∈ s, b i ^ 2) := by
        simp_rw [← Finset.sum_mul]
        ring
  linarith
end BombieriVinogradov.LargeSieve
end

section
noncomputable section
open Complex Finset
open scoped BigOperators ComplexConjugate
namespace BombieriVinogradov.LargeSieve
theorem complexEnergy_eq_gram {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (A : ρ -> ι -> Complex) (b : ι -> Complex) :
    (((∑ r, ‖∑ i, A r i * b i‖ ^ 2 : Real) : Real) : Complex) =
      ∑ i, ∑ j, conj (b i) * b j *
        ∑ r, conj (A r i) * A r j := by
  have hterm (z : Complex) : ((‖z‖ ^ 2 : Real) : Complex) = conj z * z := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rw [Complex.ofReal_sum]
  simp_rw [hterm]
  simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro r hr
  ring
theorem complexGramSchurBound {ρ ι : Type*} [Fintype ρ] [Fintype ι]
    (A : ρ -> ι -> Complex) (b : ι -> Complex)
    (k : ι -> ι -> Real)
    (hk : ∀ i j, 0 <= k i j) (hsymm : ∀ i j, k i j = k j i)
    {B : Real} (hrow : ∀ i, ∑ j, k i j <= B)
    (hgram : ∀ i j, ‖∑ r, conj (A r i) * A r j‖ <= k i j) :
    ∑ r, ‖∑ i, A r i * b i‖ ^ 2 <= B * ∑ i, ‖b i‖ ^ 2 := by
  let G : Complex := ∑ i, ∑ j, conj (b i) * b j *
    ∑ r, conj (A r i) * A r j
  have henergy := complexEnergy_eq_gram A b
  change ((∑ r, ‖∑ i, A r i * b i‖ ^ 2 : Real) : Complex) = G at henergy
  have hre : ∑ r, ‖∑ i, A r i * b i‖ ^ 2 = G.re := by
    calc
      ∑ r, ‖∑ i, A r i * b i‖ ^ 2 =
          (((∑ r, ‖∑ i, A r i * b i‖ ^ 2 : Real) : Complex)).re :=
        (Complex.ofReal_re _).symm
      _ = G.re := congrArg Complex.re henergy
  calc
    ∑ r, ‖∑ i, A r i * b i‖ ^ 2 = G.re := hre
    _ <= ‖G‖ := Complex.re_le_norm G
    _ <= ∑ i, ‖∑ j, conj (b i) * b j *
          ∑ r, conj (A r i) * A r j‖ := by
      exact norm_sum_le _ _
    _ <= ∑ i, ∑ j, ‖conj (b i) * b j *
          ∑ r, conj (A r i) * A r j‖ := by
      exact Finset.sum_le_sum fun i hi => norm_sum_le _ _
    _ = ∑ i, ∑ j, ‖b i‖ * ‖b j‖ *
          ‖∑ r, conj (A r i) * A r j‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [norm_mul, norm_conj]
    _ <= ∑ i, ∑ j, ‖b i‖ * ‖b j‖ * k i j := by
      exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hgram i j)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ <= B * ∑ i, ‖b i‖ ^ 2 :=
      schurBound k hk hsymm hrow (fun i => ‖b i‖)
theorem complexEnergyFinset_eq_gram {ρ ι : Type*}
    [DecidableEq ρ] [DecidableEq ι] (sr : Finset ρ) (si : Finset ι)
    (A : ρ -> ι -> Complex) (b : ι -> Complex) :
    (((∑ r ∈ sr, ‖∑ i ∈ si, A r i * b i‖ ^ 2 : Real) : Real) : Complex) =
      ∑ i ∈ si, ∑ j ∈ si, conj (b i) * b j *
        ∑ r ∈ sr, conj (A r i) * A r j := by
  have hterm (z : Complex) : ((‖z‖ ^ 2 : Real) : Complex) = conj z * z := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rw [Complex.ofReal_sum]
  simp_rw [hterm]
  simp_rw [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro r hr
  ring
theorem complexGramSchurBoundFinset {ρ ι : Type*}
    [DecidableEq ρ] [DecidableEq ι] (sr : Finset ρ) (si : Finset ι)
    (A : ρ -> ι -> Complex) (b : ι -> Complex)
    (k : ι -> ι -> Real)
    (hk : ∀ i ∈ si, ∀ j ∈ si, 0 <= k i j)
    (hsymm : ∀ i ∈ si, ∀ j ∈ si, k i j = k j i)
    {B : Real} (hrow : ∀ i ∈ si, ∑ j ∈ si, k i j <= B)
    (hgram : ∀ i ∈ si, ∀ j ∈ si,
      ‖∑ r ∈ sr, conj (A r i) * A r j‖ <= k i j) :
    ∑ r ∈ sr, ‖∑ i ∈ si, A r i * b i‖ ^ 2 <=
      B * ∑ i ∈ si, ‖b i‖ ^ 2 := by
  let G : Complex := ∑ i ∈ si, ∑ j ∈ si, conj (b i) * b j *
    ∑ r ∈ sr, conj (A r i) * A r j
  have henergy := complexEnergyFinset_eq_gram sr si A b
  change ((∑ r ∈ sr, ‖∑ i ∈ si, A r i * b i‖ ^ 2 : Real) : Complex) = G at henergy
  have hre : ∑ r ∈ sr, ‖∑ i ∈ si, A r i * b i‖ ^ 2 = G.re := by
    calc
      ∑ r ∈ sr, ‖∑ i ∈ si, A r i * b i‖ ^ 2 =
          (((∑ r ∈ sr, ‖∑ i ∈ si, A r i * b i‖ ^ 2 : Real) : Complex)).re :=
        (Complex.ofReal_re _).symm
      _ = G.re := congrArg Complex.re henergy
  calc
    ∑ r ∈ sr, ‖∑ i ∈ si, A r i * b i‖ ^ 2 = G.re := hre
    _ <= ‖G‖ := Complex.re_le_norm G
    _ <= ∑ i ∈ si, ‖∑ j ∈ si, conj (b i) * b j *
          ∑ r ∈ sr, conj (A r i) * A r j‖ := by
      exact norm_sum_le _ _
    _ <= ∑ i ∈ si, ∑ j ∈ si, ‖conj (b i) * b j *
          ∑ r ∈ sr, conj (A r i) * A r j‖ := by
      exact Finset.sum_le_sum fun i hi => norm_sum_le _ _
    _ = ∑ i ∈ si, ∑ j ∈ si, ‖b i‖ * ‖b j‖ *
          ‖∑ r ∈ sr, conj (A r i) * A r j‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      simp only [norm_mul, norm_conj]
    _ <= ∑ i ∈ si, ∑ j ∈ si, ‖b i‖ * ‖b j‖ * k i j := by
      exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj =>
        mul_le_mul_of_nonneg_left (hgram i hi j hj)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ <= B * ∑ i ∈ si, ‖b i‖ ^ 2 :=
      schurBoundFinset si k hk hsymm hrow (fun i => ‖b i‖)
theorem sum_comp_le_sum_of_injective {α β : Type*}
    [Fintype α] [Fintype β] [DecidableEq β]
    (e : α -> β) (he : Function.Injective e)
    (g : β -> Real) (hg : ∀ b, 0 <= g b) :
    ∑ a, g (e a) <= ∑ b, g b := by
  have hsubset : Finset.univ.image e ⊆ (Finset.univ : Finset β) := by
    exact fun b hb => Finset.mem_univ b
  calc
    ∑ a, g (e a) = ∑ b ∈ Finset.univ.image e, g b :=
      (Finset.sum_image he.injOn).symm
    _ <= ∑ b, g b :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro b hb hnot
        exact hg b)
end BombieriVinogradov.LargeSieve
end
end

section
namespace BombieriVinogradov.LargeSieve
theorem ratAbsLowerBound {D : Nat} (hD : 0 < D) {z : Rat}
    (hzden : z.den <= D) (hz : Ne z 0) :
    (1 : Real) / (D : Real) <= |(z : Real)| := by
  have hnumNat : 1 <= z.num.natAbs :=
    Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr (Rat.num_ne_zero.mpr hz))
  have hnum : (1 : Real) <= |(z.num : Real)| := by
    calc
      (1 : Real) <= (z.num.natAbs : Real) := by exact_mod_cast hnumNat
      _ = |(z.num : Real)| := by simp
  have hDReal : 0 < (D : Real) := by exact_mod_cast hD
  have hdenReal : 0 < (z.den : Real) := by exact_mod_cast z.den_pos
  have hrecip : (1 : Real) / (D : Real) <= 1 / (z.den : Real) := by
    gcongr
  calc
    (1 : Real) / (D : Real) <= 1 / (z.den : Real) := hrecip
    _ <= |(z.num : Real)| / (z.den : Real) := by gcongr
    _ = |(z : Real)| := by
      rw [Rat.cast_def, abs_div, abs_of_pos hdenReal]
theorem ratAbsSubLowerBound {Q : Nat} (hQ : 0 < Q) {x y : Rat}
    (hx : x.den <= Q) (hy : y.den <= Q) (hxy : Ne x y) :
    (1 : Real) / (Q : Real) ^ 2 <= |(x : Real) - (y : Real)| := by
  let z : Rat := x - y
  have hz : Ne z 0 := sub_ne_zero.mpr hxy
  have hden : z.den <= x.den * y.den :=
    Nat.le_of_dvd (Nat.mul_pos x.den_pos y.den_pos) (Rat.sub_den_dvd x y)
  have hdenQ : z.den <= Q ^ 2 := by
    calc
      z.den <= x.den * y.den := hden
      _ <= Q * Q := Nat.mul_le_mul hx hy
      _ = Q ^ 2 := by ring
  simpa [z, Nat.cast_pow] using
    ratAbsLowerBound (D := Q ^ 2) (Nat.pow_pos hQ) hdenQ hz
def ratCircleDistance (x y : Rat) : Real :=
  min |(x : Real) - (y : Real)| (1 - |(x : Real) - (y : Real)|)
theorem ratCircleSeparation {Q : Nat} (hQ : 0 < Q) {x y : Rat}
    (hx0 : 0 <= x) (hx1 : x < 1) (hy0 : 0 <= y) (hy1 : y < 1)
    (hxden : x.den <= Q) (hyden : y.den <= Q) (hxy : Ne x y) :
    (1 : Real) / (Q : Real) ^ 2 <= ratCircleDistance x y := by
  have hlinear := ratAbsSubLowerBound hQ hxden hyden hxy
  have hsub_lt_one : |x - y| < (1 : Rat) := by
    rw [abs_lt]
    constructor <;> linarith
  let w : Rat := 1 - |x - y|
  have hwpos : 0 < w := sub_pos.mpr hsub_lt_one
  have hwden : w.den <= Q ^ 2 := by
    have hxyden : (x - y).den <= Q ^ 2 := by
      apply Nat.le_trans
      · exact Nat.le_of_dvd (Nat.mul_pos x.den_pos y.den_pos) (Rat.sub_den_dvd x y)
      · simpa [pow_two] using Nat.mul_le_mul hxden hyden
    simpa [w] using hxyden
  have hcircular : (1 : Real) / (Q : Real) ^ 2 <= |(w : Real)| := by
    simpa only [Nat.cast_pow] using
      ratAbsLowerBound (D := Q ^ 2) (Nat.pow_pos hQ) hwden hwpos.ne'
  have hwcast : |(w : Real)| = 1 - |(x : Real) - (y : Real)| := by
    rw [abs_of_pos]
    · simp [w]
    · exact_mod_cast hwpos
  rw [ratCircleDistance, le_min_iff]
  exact And.intro hlinear (hwcast ▸ hcircular)
end BombieriVinogradov.LargeSieve
end

section
namespace BombieriVinogradov.LargeSieve
def unitFraction {q : Nat} (a : (ZMod q)ˣ) : Rat :=
  (a.val.val : Rat) / (q : Rat)
theorem unitFraction_coprime {q : Nat} [NeZero q] (a : (ZMod q)ˣ) :
    Nat.Coprime a.val.val q := by
  rw [← ZMod.isUnit_iff_coprime]
  simpa only [ZMod.natCast_zmod_val] using a.isUnit
theorem unitFraction_den {q : Nat} [NeZero q] (a : (ZMod q)ˣ) :
    (unitFraction a).den = q := by
  have hqInt : (0 : Int) < q := by exact_mod_cast NeZero.pos q
  have hcInt : Nat.Coprime (a.val.val : Int).natAbs (q : Int).natAbs := by
    change Nat.Coprime a.val.val q
    exact unitFraction_coprime a
  have hden : ((unitFraction a).den : Int) = (q : Int) := by
    simpa [unitFraction] using Rat.den_div_eq_of_coprime hqInt hcInt
  exact Int.ofNat_inj.mp hden
theorem unitFraction_num {q : Nat} [NeZero q] (a : (ZMod q)ˣ) :
    (unitFraction a).num = (a.val.val : Int) := by
  have hqInt : (0 : Int) < q := by exact_mod_cast NeZero.pos q
  have hcInt : Nat.Coprime (a.val.val : Int).natAbs (q : Int).natAbs := by
    change Nat.Coprime a.val.val q
    exact unitFraction_coprime a
  simpa [unitFraction] using Rat.num_div_eq_of_coprime hqInt hcInt
abbrev FareyIndex (Q : Nat) :=
  Sigma fun q : {q : Nat // q ∈ Finset.Icc 1 Q} => (ZMod q.1)ˣ
def fareyValue {Q : Nat} (i : FareyIndex Q) : Rat :=
  unitFraction i.2
theorem fareyValue_den {Q : Nat} (i : FareyIndex Q) :
    (fareyValue i).den = i.1.1 := by
  let _ : NeZero i.1.1 := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp i.1.2).1⟩
  exact unitFraction_den i.2
theorem fareyValue_nonneg {Q : Nat} (i : FareyIndex Q) :
    0 <= fareyValue i := by
  unfold fareyValue unitFraction
  positivity
theorem fareyValue_lt_one {Q : Nat} (i : FareyIndex Q) :
    fareyValue i < 1 := by
  let _ : NeZero i.1.1 := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp i.1.2).1⟩
  unfold fareyValue unitFraction
  rw [div_lt_one]
  · exact_mod_cast ZMod.val_lt i.2.val
  · exact_mod_cast NeZero.pos i.1.1
theorem fareyValue_injective (Q : Nat) :
    Function.Injective (fareyValue (Q := Q)) := by
  intro x y hxy
  have hxpos : 0 < x.1.1 := (Finset.mem_Icc.mp x.1.2).1
  have hypos : 0 < y.1.1 := (Finset.mem_Icc.mp y.1.2).1
  let _ : NeZero x.1.1 := ⟨hxpos.ne'⟩
  let _ : NeZero y.1.1 := ⟨hypos.ne'⟩
  have hq : x.1.1 = y.1.1 := by
    calc
      x.1.1 = (fareyValue x).den := (fareyValue_den x).symm
      _ = (fareyValue y).den := congrArg Rat.den hxy
      _ = y.1.1 := fareyValue_den y
  cases x with
  | mk q a =>
      cases y with
      | mk r b =>
          simp only at hq
          have hqr : q = r := Subtype.ext hq
          subst r
          have hnum : (a.val.val : Int) = (b.val.val : Int) := by
            calc
              (a.val.val : Int) = (unitFraction a).num := (unitFraction_num a).symm
              _ = (unitFraction b).num := congrArg Rat.num hxy
              _ = (b.val.val : Int) := unitFraction_num b
          have habNat : a.val.val = b.val.val := Int.ofNat_inj.mp hnum
          have habZMod : a.val = b.val := ZMod.val_injective q.1 habNat
          have hab : a = b := Units.ext habZMod
          subst b
          rfl
theorem fareyValue_circle_separation {Q : Nat} (hQ : 0 < Q)
    {x y : FareyIndex Q} (hxy : Ne x y) :
    (1 : Real) / (Q : Real) ^ 2 <= ratCircleDistance (fareyValue x) (fareyValue y) := by
  apply ratCircleSeparation hQ
  · exact fareyValue_nonneg x
  · exact fareyValue_lt_one x
  · exact fareyValue_nonneg y
  · exact fareyValue_lt_one y
  · rw [fareyValue_den]
    exact (Finset.mem_Icc.mp x.1.2).2
  · rw [fareyValue_den]
    exact (Finset.mem_Icc.mp y.1.2).2
  · intro hvalue
    exact hxy (fareyValue_injective Q hvalue)
end BombieriVinogradov.LargeSieve
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators ComplexConjugate
namespace BombieriVinogradov.LargeSieve
def additivePhase (x : Real) : Complex :=
  circleMap 0 1 (2 * Real.pi * x)
@[simp]
theorem norm_additivePhase (x : Real) : ‖additivePhase x‖ = 1 := by
  simp [additivePhase]
@[simp]
theorem additivePhase_zero : additivePhase 0 = 1 := by
  simp [additivePhase, circleMap_zero]
theorem additivePhase_add (x y : Real) :
    additivePhase (x + y) = additivePhase x * additivePhase y := by
  simpa [additivePhase, mul_add] using
    (circleMap_zero_mul 1 1 (2 * Real.pi * x) (2 * Real.pi * y)).symm
theorem additivePhase_nat_mul (n : Nat) (x : Real) :
    additivePhase ((n : Real) * x) = additivePhase x ^ n := by
  rw [additivePhase, additivePhase, circleMap_zero, circleMap_zero]
  norm_num
  rw [← Complex.exp_nat_mul]
  congr 1
  ring
@[simp]
theorem additivePhase_one : additivePhase 1 = 1 := by
  simp [additivePhase, circleMap_zero, Complex.exp_two_pi_mul_I]
@[simp]
theorem additivePhase_nat (n : Nat) : additivePhase (n : Real) = 1 := by
  calc
    additivePhase (n : Real) = additivePhase ((n : Real) * 1) := by simp
    _ = additivePhase 1 ^ n := additivePhase_nat_mul n 1
    _ = 1 := by simp
@[simp]
theorem conj_additivePhase (x : Real) :
    conj (additivePhase x) = additivePhase (-x) := by
  rw [additivePhase, additivePhase, conj_circleMap_zero]
  congr 2
  ring
def phaseSum (N : Nat) (x : Real) : Complex :=
  ∑ j ∈ range N, additivePhase ((j : Real) * x)
theorem conj_phaseSum (N : Nat) (x : Real) :
    conj (phaseSum N x) = phaseSum N (-x) := by
  simp [phaseSum, conj_additivePhase]
theorem phaseSum_one_sub (N : Nat) (x : Real) :
    phaseSum N (1 - x) = conj (phaseSum N x) := by
  rw [phaseSum, phaseSum]
  simp_rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    additivePhase ((j : Real) * (1 - x)) =
        additivePhase ((j : Real) + (-((j : Real) * x))) := by
      congr 1
      ring
    _ = additivePhase (j : Real) * additivePhase (-((j : Real) * x)) :=
      additivePhase_add _ _
    _ = 1 * conj (additivePhase ((j : Real) * x)) := by
      rw [additivePhase_nat, conj_additivePhase]
    _ = conj (additivePhase ((j : Real) * x)) := one_mul _
@[simp]
theorem norm_phaseSum_neg (N : Nat) (x : Real) :
    ‖phaseSum N (-x)‖ = ‖phaseSum N x‖ := by
  rw [← conj_phaseSum]
  exact norm_conj _
@[simp]
theorem norm_phaseSum_one_sub (N : Nat) (x : Real) :
    ‖phaseSum N (1 - x)‖ = ‖phaseSum N x‖ := by
  rw [phaseSum_one_sub]
  exact norm_conj _
@[simp]
theorem norm_phaseSum_abs (N : Nat) (x : Real) :
    ‖phaseSum N |x|‖ = ‖phaseSum N x‖ := by
  by_cases hx : 0 <= x
  · rw [abs_of_nonneg hx]
  · rw [abs_of_neg (lt_of_not_ge hx), norm_phaseSum_neg]
def phaseDistance (x : Real) : Real := min |x| (1 - |x|)
theorem phaseDistance_pos {x : Real} (hx0 : Ne x 0) (hx1 : |x| < 1) :
    0 < phaseDistance x := by
  rw [phaseDistance, lt_min_iff]
  exact And.intro (abs_pos.mpr hx0) (sub_pos.mpr hx1)
def fejerKernel (N : Nat) (x : Real) : Real :=
  (2 / (N : Real)) * ‖phaseSum N x‖ ^ 2
@[simp]
theorem fejerKernel_neg (N : Nat) (x : Real) :
    fejerKernel N (-x) = fejerKernel N x := by
  unfold fejerKernel
  rw [norm_phaseSum_neg]
theorem fejerKernel_nonneg (N : Nat) (x : Real) :
    0 <= fejerKernel N x := by
  unfold fejerKernel
  positivity
@[simp]
theorem fejerKernel_zero (x : Real) : fejerKernel 0 x = 0 := by
  simp [fejerKernel]
theorem norm_phaseSum_le (N : Nat) (x : Real) :
    ‖phaseSum N x‖ <= N := by
  calc
    ‖phaseSum N x‖ <= ∑ j ∈ range N, ‖additivePhase ((j : Real) * x)‖ :=
      norm_sum_le _ _
    _ = N := by simp
theorem fejerKernel_le (N : Nat) (x : Real) :
    fejerKernel N x <= 2 * N := by
  by_cases hN : N = 0
  · simp [hN]
  have hNpos : (0 : Real) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hsq : ‖phaseSum N x‖ ^ 2 <= (N : Real) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_phaseSum_le N x) 2
  calc
    fejerKernel N x <= (2 / (N : Real)) * (N : Real) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 2 * N := by field_simp
theorem phaseSum_eq_geom (N : Nat) (x : Real) :
    phaseSum N x = ∑ j ∈ range N, additivePhase x ^ j := by
  apply Finset.sum_congr rfl
  intro j hj
  exact additivePhase_nat_mul j x
theorem phaseSum_mul_sub_one (N : Nat) (x : Real) :
    phaseSum N x * (additivePhase x - 1) = additivePhase x ^ N - 1 := by
  rw [phaseSum_eq_geom]
  exact geom_sum_mul (additivePhase x) N
theorem norm_additivePhase_sub_one_lower {x : Real}
    (hx0 : 0 <= x) (hx : x <= 1 / 2) :
    4 * x <= ‖additivePhase x - 1‖ := by
  have hpix0 : 0 <= Real.pi * x := mul_nonneg Real.pi_pos.le hx0
  have hpix : |Real.pi * x| <= Real.pi / 2 := by
    rw [abs_of_nonneg hpix0]
    nlinarith [Real.pi_pos]
  have hsin := Real.mul_abs_le_abs_sin hpix
  rw [abs_of_nonneg hpix0] at hsin
  rw [additivePhase, circleMap_zero]
  norm_num
  have harg : (2 : Complex) * Real.pi * x * I =
      I * ((2 * Real.pi * x : Real) : Complex) := by
    push_cast
    ring
  rw [harg, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * x) / 2 = Real.pi * x by ring]
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : Real) <= 2)]
  have hcancel : 2 / Real.pi * (Real.pi * x) = 2 * x := by
    field_simp [Real.pi_ne_zero]
  nlinarith [Real.pi_pos]
theorem norm_phaseSum_le_inv {N : Nat} {x : Real}
    (hx0 : 0 < x) (hx : x <= 1 / 2) :
    ‖phaseSum N x‖ <= 1 / (2 * x) := by
  have hden := norm_additivePhase_sub_one_lower hx0.le hx
  have hgeom := congrArg norm (phaseSum_mul_sub_one N x)
  rw [norm_mul] at hgeom
  have hright : ‖additivePhase x ^ N - 1‖ <= 2 := by
    calc
      ‖additivePhase x ^ N - 1‖ <=
          ‖additivePhase x ^ N‖ + ‖(1 : Complex)‖ := norm_sub_le _ _
      _ = 2 := by norm_num [norm_additivePhase]
  have hprod : ‖phaseSum N x‖ * ‖additivePhase x - 1‖ <= 2 := by
    rw [hgeom]
    exact hright
  have hscaled : ‖phaseSum N x‖ * (4 * x) <= 2 := by
    calc
      ‖phaseSum N x‖ * (4 * x) <=
          ‖phaseSum N x‖ * ‖additivePhase x - 1‖ :=
        mul_le_mul_of_nonneg_left hden (norm_nonneg _)
      _ <= 2 := hprod
  have htwo : ‖phaseSum N x‖ * (2 * x) <= 1 := by
    nlinarith [norm_nonneg (phaseSum N x)]
  exact (le_div_iff₀ (mul_pos (by norm_num) hx0)).2 htwo
theorem norm_phaseSum_le_phaseDistance {N : Nat} {x : Real}
    (hx0 : Ne x 0) (hx1 : |x| < 1) :
    ‖phaseSum N x‖ <= 1 / (2 * phaseDistance x) := by
  have habs0 : 0 < |x| := abs_pos.mpr hx0
  by_cases hhalf : |x| <= 1 / 2
  · have hmin : min |x| (1 - |x|) = |x| := min_eq_left (by linarith)
    calc
      ‖phaseSum N x‖ = ‖phaseSum N |x|‖ := (norm_phaseSum_abs N x).symm
      _ <= 1 / (2 * |x|) := norm_phaseSum_le_inv habs0 hhalf
      _ = 1 / (2 * phaseDistance x) := by rw [phaseDistance, hmin]
  · have hhalf' : 1 - |x| <= 1 / 2 := by linarith
    have hcomp0 : 0 < 1 - |x| := sub_pos.mpr hx1
    have hmin : min |x| (1 - |x|) = 1 - |x| := min_eq_right (by linarith)
    calc
      ‖phaseSum N x‖ = ‖phaseSum N |x|‖ := (norm_phaseSum_abs N x).symm
      _ = ‖phaseSum N (1 - |x|)‖ := (norm_phaseSum_one_sub N |x|).symm
      _ <= 1 / (2 * (1 - |x|)) := norm_phaseSum_le_inv hcomp0 hhalf'
      _ = 1 / (2 * phaseDistance x) := by rw [phaseDistance, hmin]
theorem fejerKernel_le_inv_phaseDistance {N : Nat} (hN : 0 < N)
    {x : Real} (hx0 : Ne x 0) (hx1 : |x| < 1) :
    fejerKernel N x <= 1 / (2 * (N : Real) * phaseDistance x ^ 2) := by
  have hdist := phaseDistance_pos hx0 hx1
  have hnorm := norm_phaseSum_le_phaseDistance (N := N) hx0 hx1
  have hsq : ‖phaseSum N x‖ ^ 2 <= (1 / (2 * phaseDistance x)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  unfold fejerKernel
  calc
    2 / (N : Real) * ‖phaseSum N x‖ ^ 2 <=
        2 / (N : Real) * (1 / (2 * phaseDistance x)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = 1 / (2 * (N : Real) * phaseDistance x ^ 2) := by
      field_simp [Nat.ne_of_gt hN, ne_of_gt hdist]
theorem phaseDistance_rat_sub (x y : Rat) :
    phaseDistance ((x : Real) - (y : Real)) = ratCircleDistance x y := rfl
theorem fejerKernel_rat_sub_le {N : Nat} (hN : 0 < N)
    {x y : Rat} (hx0 : 0 <= x) (hx1 : x < 1)
    (hy0 : 0 <= y) (hy1 : y < 1) (hxy : Ne x y) :
    fejerKernel N ((x : Real) - (y : Real)) <=
      1 / (2 * (N : Real) * ratCircleDistance x y ^ 2) := by
  have hx0' : (0 : Real) <= x := by exact_mod_cast hx0
  have hx1' : (x : Real) < 1 := by exact_mod_cast hx1
  have hy0' : (0 : Real) <= y := by exact_mod_cast hy0
  have hy1' : (y : Real) < 1 := by exact_mod_cast hy1
  have hcast : Ne (x : Real) (y : Real) := by exact_mod_cast hxy
  have hsub : Ne ((x : Real) - (y : Real)) 0 := sub_ne_zero.mpr hcast
  have habs : |(x : Real) - (y : Real)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith
  simpa [phaseDistance_rat_sub] using
    fejerKernel_le_inv_phaseDistance hN hsub habs
end BombieriVinogradov.LargeSieve
end
end

section
noncomputable section
open Finset Real
open scoped BigOperators
namespace BombieriVinogradov.LargeSieve
def packingBin (delta x : Real) : Nat := Nat.floor (x / delta)
theorem abs_sub_lt_of_packingBin_eq {delta x y : Real} (hdelta : 0 < delta)
    (hx : 0 <= x) (hy : 0 <= y)
    (hbin : packingBin delta x = packingBin delta y) :
    |x - y| < delta := by
  have hxq0 : 0 <= x / delta := div_nonneg hx hdelta.le
  have hyq0 : 0 <= y / delta := div_nonneg hy hdelta.le
  have hxlo : ((packingBin delta x : Nat) : Real) <= x / delta :=
    Nat.floor_le hxq0
  have hxhi : x / delta < (packingBin delta x : Nat) + 1 :=
    Nat.lt_floor_add_one _
  have hylo : ((packingBin delta y : Nat) : Real) <= y / delta :=
    Nat.floor_le hyq0
  have hyhi : y / delta < (packingBin delta y : Nat) + 1 :=
    Nat.lt_floor_add_one _
  have hxyq : x / delta - y / delta < 1 := by
    rw [hbin] at hxhi
    linarith
  have hyxq : y / delta - x / delta < 1 := by
    rw [hbin] at hxlo
    linarith
  have hxy : x - y < delta := by
    rw [← sub_div] at hxyq
    exact (div_lt_one hdelta).mp hxyq
  have hyx : y - x < delta := by
    rw [← sub_div] at hyxq
    exact (div_lt_one hdelta).mp hyxq
  rw [abs_lt]
  exact And.intro (by linarith) hxy
theorem packingBin_injective {ι : Type*} {delta : Real} (hdelta : 0 < delta)
    (x : ι -> Real) (hx : ∀ i, 0 <= x i)
    (hsep : ∀ i j, Ne i j -> delta <= |x i - x j|) :
    Function.Injective (fun i => packingBin delta (x i)) := by
  intro i j hbin
  by_contra hij
  have hlt := abs_sub_lt_of_packingBin_eq hdelta (hx i) (hx j) hbin
  exact (not_lt_of_ge (hsep i j hij)) hlt
def fejerRankMajorant (N : Nat) (delta : Real) (k : Nat) : Real :=
  if k = 0 then 0
  else min (2 * (N : Real))
    (1 / (2 * (N : Real) * ((k : Real) * delta) ^ 2))
theorem fejerRankMajorant_nonneg {N : Nat} (hN : 0 < N)
    {delta : Real} (hdelta : 0 < delta) (k : Nat) :
    0 <= fejerRankMajorant N delta k := by
  rw [fejerRankMajorant]
  split_ifs
  · exact le_rfl
  · rw [le_min_iff]
    exact And.intro (by positivity) (by positivity)
theorem fejerRankMajorant_le_diagonal (N : Nat) (delta : Real) (k : Nat) :
    fejerRankMajorant N delta k <= 2 * (N : Real) := by
  rw [fejerRankMajorant]
  split_ifs
  · positivity
  · exact min_le_left _ _
theorem fejerRankMajorant_le_inv {N k : Nat} (hN : 0 < N) (hk : Ne k 0)
    {delta : Real} (hdelta : 0 < delta) :
    fejerRankMajorant N delta k <=
      (1 / (2 * (N : Real) * delta ^ 2)) * (((k : Real) ^ 2)⁻¹) := by
  rw [fejerRankMajorant, if_neg hk]
  calc
    min (2 * (N : Real))
        (1 / (2 * (N : Real) * ((k : Real) * delta) ^ 2)) <=
      1 / (2 * (N : Real) * ((k : Real) * delta) ^ 2) := min_le_right _ _
    _ = (1 / (2 * (N : Real) * delta ^ 2)) * (((k : Real) ^ 2)⁻¹) := by
      field_simp [Nat.ne_of_gt hN, hk, ne_of_gt hdelta]
theorem sum_fejerRankMajorant_le {N : Nat} (hN : 0 < N)
    {delta : Real} (hdelta : 0 < delta) (K : Nat) :
    ∑ k ∈ range K, fejerRankMajorant N delta k <=
      4 * (N : Real) + 5 / (2 * delta) := by
  let a : Real := 1 / ((N : Real) * delta)
  let A : Nat := Nat.ceil a
  have ha0 : 0 < a := by simp [a]; positivity
  have hAone : 1 <= A := Nat.one_le_ceil_iff.mpr ha0
  have hAne : Ne A 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le hAone)
  have hApos : (0 : Real) < A := by exact_mod_cast hAone
  have hAle : a <= (A : Real) := Nat.le_ceil a
  have hAlt : (A : Real) < a + 1 := Nat.ceil_lt_add_one ha0.le
  let head : Finset Nat := (range K).filter fun k => k <= A
  let tail : Finset Nat := (range K).filter fun k => ¬k <= A
  have hhead_subset : head ⊆ range (A + 1) := by
    intro k hk
    simp only [head, mem_filter] at hk
    exact mem_range.mpr (Nat.lt_succ_iff.mpr hk.2)
  have hhead_card : (head.card : Real) <= A + 1 := by
    have hcardNat : head.card <= A + 1 := by
      simpa using Finset.card_le_card hhead_subset
    exact_mod_cast hcardNat
  have hhead : ∑ k ∈ head, fejerRankMajorant N delta k <=
      2 * (N : Real) * (A + 1) := by
    calc
      ∑ k ∈ head, fejerRankMajorant N delta k <=
          ∑ k ∈ head, 2 * (N : Real) :=
        Finset.sum_le_sum fun k hk => fejerRankMajorant_le_diagonal N delta k
      _ = head.card * (2 * (N : Real)) := by simp
      _ <= 2 * (N : Real) * (A + 1) := by
        nlinarith
  have hhead_final : ∑ k ∈ head, fejerRankMajorant N delta k <=
      4 * (N : Real) + 2 / delta := by
    apply hhead.trans
    have hAone' : (A : Real) + 1 <= a + 2 := by linarith
    calc
      2 * (N : Real) * ((A : Real) + 1) <=
          2 * (N : Real) * (a + 2) := by gcongr
      _ = 4 * (N : Real) + 2 / delta := by
        dsimp [a]
        field_simp [Nat.ne_of_gt hN, ne_of_gt hdelta]
        ring
  have htail_subset : tail ⊆ Ioc A (max A K) := by
    intro k hk
    simp only [tail, mem_filter, mem_range] at hk
    exact mem_Ioc.mpr ⟨Nat.lt_of_not_ge hk.2, (Nat.le_of_lt hk.1).trans (le_max_right _ _)⟩
  have htail_inv : ∑ k ∈ tail, (((k : Real) ^ 2)⁻¹) <= ((A : Real)⁻¹) := by
    calc
      ∑ k ∈ tail, (((k : Real) ^ 2)⁻¹) <=
          ∑ k ∈ Ioc A (max A K), (((k : Real) ^ 2)⁻¹) :=
        Finset.sum_le_sum_of_subset_of_nonneg htail_subset (by
          intro k hk hnot
          positivity)
      _ <= (A : Real)⁻¹ - (((max A K : Nat) : Real)⁻¹) :=
        sum_Ioc_inv_sq_le_sub hAne (le_max_left _ _)
      _ <= (A : Real)⁻¹ := by
        exact sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _))
  have htail : ∑ k ∈ tail, fejerRankMajorant N delta k <=
      (1 / (2 * (N : Real) * delta ^ 2)) * ((A : Real)⁻¹) := by
    calc
      ∑ k ∈ tail, fejerRankMajorant N delta k <=
          ∑ k ∈ tail,
            (1 / (2 * (N : Real) * delta ^ 2)) * (((k : Real) ^ 2)⁻¹) := by
        apply Finset.sum_le_sum
        intro k hk
        have hkA : A < k := by
          simp only [tail, mem_filter] at hk
          exact Nat.lt_of_not_ge hk.2
        have hk0 : Ne k 0 := by omega
        exact fejerRankMajorant_le_inv hN hk0 hdelta
      _ = (1 / (2 * (N : Real) * delta ^ 2)) *
          ∑ k ∈ tail, (((k : Real) ^ 2)⁻¹) := by rw [Finset.mul_sum]
      _ <= (1 / (2 * (N : Real) * delta ^ 2)) * ((A : Real)⁻¹) := by
        gcongr
  have hAinv : ((A : Real)⁻¹) <= (N : Real) * delta := by
    apply (inv_le_iff_one_le_mul₀ hApos).2
    have hmul := mul_le_mul_of_nonneg_left hAle
      (mul_nonneg (Nat.cast_nonneg N) hdelta.le)
    have hcancel : (N : Real) * delta * a = 1 := by
      dsimp [a]
      field_simp [Nat.ne_of_gt hN, ne_of_gt hdelta]
    nlinarith
  have htail_final : ∑ k ∈ tail, fejerRankMajorant N delta k <=
      1 / (2 * delta) := by
    apply htail.trans
    calc
      (1 / (2 * (N : Real) * delta ^ 2)) * ((A : Real)⁻¹) <=
          (1 / (2 * (N : Real) * delta ^ 2)) * ((N : Real) * delta) := by
        gcongr
      _ = 1 / (2 * delta) := by
        field_simp [Nat.ne_of_gt hN, ne_of_gt hdelta]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (range K) (fun k => k <= A) (fejerRankMajorant N delta)
  change (∑ k ∈ head, fejerRankMajorant N delta k) +
      (∑ k ∈ tail, fejerRankMajorant N delta k) =
        ∑ k ∈ range K, fejerRankMajorant N delta k at hsplit
  calc
    ∑ k ∈ range K, fejerRankMajorant N delta k =
        (∑ k ∈ head, fejerRankMajorant N delta k) +
          (∑ k ∈ tail, fejerRankMajorant N delta k) := hsplit.symm
    _ <= (4 * (N : Real) + 2 / delta) + 1 / (2 * delta) :=
      add_le_add hhead_final htail_final
    _ = 4 * (N : Real) + 5 / (2 * delta) := by ring
theorem sum_le_sum_range_of_injective {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (e : ι -> Nat) (K : Nat)
    (he : ∀ i ∈ s, e i < K) (hinj : Set.InjOn e (s : Set ι))
    (g : Nat -> Real) (hg : ∀ k, 0 <= g k)
    (w : ι -> Real) (hw : ∀ i ∈ s, w i <= g (e i)) :
    ∑ i ∈ s, w i <= ∑ k ∈ range K, g k := by
  have hsubset : s.image e ⊆ range K := by
    intro k hk
    rw [mem_image] at hk
    obtain ⟨i, hi, rfl⟩ := hk
    exact mem_range.mpr (he i hi)
  calc
    ∑ i ∈ s, w i <= ∑ i ∈ s, g (e i) :=
      Finset.sum_le_sum fun i hi => hw i hi
    _ = ∑ k ∈ s.image e, g k := (Finset.sum_image hinj).symm
    _ <= ∑ k ∈ range K, g k :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro k hk hnot
        exact hg k)
theorem packedFejerSum {ι : Type*} [DecidableEq ι]
    {N : Nat} (hN : 0 < N) {delta : Real} (hdelta : 0 < delta)
    (s : Finset ι) (d : ι -> Real)
    (hd0 : ∀ i ∈ s, delta <= d i) (hd1 : ∀ i ∈ s, d i < 1)
    (hsep : ∀ i ∈ s, ∀ j ∈ s, Ne i j -> delta <= |d i - d j|)
    (w : ι -> Real)
    (hw : ∀ i ∈ s, w i <=
      min (2 * (N : Real)) (1 / (2 * (N : Real) * d i ^ 2))) :
    ∑ i ∈ s, w i <= 4 * (N : Real) + 5 / (2 * delta) := by
  let e : ι -> Nat := fun i => packingBin delta (d i)
  let K : Nat := Nat.ceil (1 / delta)
  have hdnonneg : ∀ i ∈ s, 0 <= d i := by
    intro i hi
    exact hdelta.le.trans (hd0 i hi)
  have heinj : Set.InjOn e (s : Set ι) := by
    intro i hi j hj heq
    by_contra hij
    have hlt := abs_sub_lt_of_packingBin_eq hdelta
      (hdnonneg i hi) (hdnonneg j hj) heq
    exact (not_lt_of_ge (hsep i hi j hj hij)) hlt
  have heK : ∀ i ∈ s, e i < K := by
    intro i hi
    apply Nat.floor_lt_ceil_of_lt_of_pos
    · exact (div_lt_div_iff_of_pos_right hdelta).2 (hd1 i hi)
    · positivity
  have hweight : ∀ i ∈ s, w i <= fejerRankMajorant N delta (e i) := by
    intro i hi
    have hquot : ((1 : Nat) : Real) <= d i / delta :=
      (le_div_iff₀ hdelta).2 (by simpa using hd0 i hi)
    have heone : 1 <= e i := Nat.le_floor hquot
    have he0 : Ne (e i) 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le heone)
    have hfloor : ((e i : Nat) : Real) <= d i / delta :=
      Nat.floor_le (div_nonneg (hdnonneg i hi) hdelta.le)
    have helower : (e i : Real) * delta <= d i := by
      have hmul := mul_le_mul_of_nonneg_right hfloor hdelta.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hdelta)] at hmul
    apply (hw i hi).trans
    rw [fejerRankMajorant, if_neg he0]
    apply min_le_min le_rfl
    apply one_div_le_one_div_of_le
    · positivity
    · have hesq : ((e i : Real) * delta) ^ 2 <= d i ^ 2 := by
        exact pow_le_pow_left₀ (by positivity) helower 2
      nlinarith [show (0 : Real) < N by exact_mod_cast hN]
  calc
    ∑ i ∈ s, w i <= ∑ k ∈ range K, fejerRankMajorant N delta k :=
      sum_le_sum_range_of_injective s e K heK heinj
        (fejerRankMajorant N delta)
        (fejerRankMajorant_nonneg hN hdelta) w hweight
    _ <= 4 * (N : Real) + 5 / (2 * delta) :=
      sum_fejerRankMajorant_le hN hdelta K
end BombieriVinogradov.LargeSieve
end
end

section
noncomputable section
open Finset Real
open scoped BigOperators
namespace BombieriVinogradov.LargeSieve
theorem fareyFejerSubsum {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (x : FareyIndex Q) (s : Finset (FareyIndex Q)) (d : FareyIndex Q -> Real)
    (hdist : ∀ y ∈ s, ratCircleDistance (fareyValue x) (fareyValue y) = d y)
    (hdlt : ∀ y ∈ s, d y < 1)
    (hdiff : ∀ y ∈ s, ∀ z ∈ s,
      |d y - d z| = |(fareyValue y : Real) - (fareyValue z : Real)|)
    (hne : ∀ y ∈ s, Ne x y) :
    ∑ y ∈ s,
        fejerKernel N ((fareyValue x : Real) - (fareyValue y : Real)) <=
      4 * (N : Real) + 5 / (2 * ((1 : Real) / (Q : Real) ^ 2)) := by
  let delta : Real := (1 : Real) / (Q : Real) ^ 2
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  apply packedFejerSum hN hdelta s d
  · intro y hy
    rw [← hdist y hy]
    exact fareyValue_circle_separation hQ (hne y hy)
  · exact hdlt
  · intro y hy z hz hyz
    calc
      delta <= ratCircleDistance (fareyValue y) (fareyValue z) :=
        fareyValue_circle_separation hQ hyz
      _ <= |(fareyValue y : Real) - (fareyValue z : Real)| := by
        exact min_le_left _ _
      _ = |d y - d z| := (hdiff y hy z hz).symm
  · intro y hy
    rw [le_min_iff]
    constructor
    · exact fejerKernel_le N _
    · have hvalue : Ne (fareyValue x) (fareyValue y) := by
        intro hxy
        exact hne y hy (fareyValue_injective Q hxy)
      have hinv := fejerKernel_rat_sub_le hN
          (fareyValue_nonneg x) (fareyValue_lt_one x)
          (fareyValue_nonneg y) (fareyValue_lt_one y) hvalue
      rwa [hdist y hy] at hinv
def fareyIndices (Q : Nat) : Finset (FareyIndex Q) :=
  (Icc 1 Q).attach.sigma fun q => by
    letI : Fintype (ZMod q.1)ˣ := Fintype.ofFinite _
    exact Finset.univ
@[simp]
theorem mem_fareyIndices {Q : Nat} (x : FareyIndex Q) : x ∈ fareyIndices Q := by
  rcases x with ⟨q, a⟩
  simp [fareyIndices]
def fareyRightNear {Q : Nat} (x : FareyIndex Q) : Finset (FareyIndex Q) :=
  (fareyIndices Q).filter fun y =>
    (fareyValue x : Real) < (fareyValue y : Real) ∧
      (fareyValue y : Real) - (fareyValue x : Real) <= 1 / 2
def fareyRightFar {Q : Nat} (x : FareyIndex Q) : Finset (FareyIndex Q) :=
  (fareyIndices Q).filter fun y =>
    (fareyValue x : Real) < (fareyValue y : Real) ∧
      1 / 2 < (fareyValue y : Real) - (fareyValue x : Real)
def fareyLeftNear {Q : Nat} (x : FareyIndex Q) : Finset (FareyIndex Q) :=
  (fareyIndices Q).filter fun y =>
    (fareyValue y : Real) < (fareyValue x : Real) ∧
      (fareyValue x : Real) - (fareyValue y : Real) <= 1 / 2
def fareyLeftFar {Q : Nat} (x : FareyIndex Q) : Finset (FareyIndex Q) :=
  (fareyIndices Q).filter fun y =>
    (fareyValue y : Real) < (fareyValue x : Real) ∧
      1 / 2 < (fareyValue x : Real) - (fareyValue y : Real)
theorem fareyRightNear_disjoint_rightFar {Q : Nat} (x : FareyIndex Q) :
    Disjoint (fareyRightNear x) (fareyRightFar x) := by
  rw [Finset.disjoint_left]
  intro y hyNear hyFar
  simp only [fareyRightNear, fareyRightFar, mem_filter] at hyNear hyFar
  linarith [hyNear.2.2, hyFar.2.2]
theorem fareyLeftNear_disjoint_leftFar {Q : Nat} (x : FareyIndex Q) :
    Disjoint (fareyLeftNear x) (fareyLeftFar x) := by
  rw [Finset.disjoint_left]
  intro y hyNear hyFar
  simp only [fareyLeftNear, fareyLeftFar, mem_filter] at hyNear hyFar
  linarith [hyNear.2.2, hyFar.2.2]
theorem fareyRight_disjoint_left {Q : Nat} (x : FareyIndex Q) :
    Disjoint (fareyRightNear x ∪ fareyRightFar x)
      (fareyLeftNear x ∪ fareyLeftFar x) := by
  rw [Finset.disjoint_left]
  intro y hyRight hyLeft
  simp only [mem_union] at hyRight hyLeft
  rcases hyRight with hyNear | hyFar
  · rcases hyLeft with hzNear | hzFar
    · simp only [fareyRightNear, fareyLeftNear, mem_filter] at hyNear hzNear
      linarith [hyNear.2.1, hzNear.2.1]
    · simp only [fareyRightNear, fareyLeftFar, mem_filter] at hyNear hzFar
      linarith [hyNear.2.1, hzFar.2.1]
  · rcases hyLeft with hzNear | hzFar
    · simp only [fareyRightFar, fareyLeftNear, mem_filter] at hyFar hzNear
      linarith [hyFar.2.1, hzNear.2.1]
    · simp only [fareyRightFar, fareyLeftFar, mem_filter] at hyFar hzFar
      linarith [hyFar.2.1, hzFar.2.1]
theorem fareyOffdiag_partition {Q : Nat} (x : FareyIndex Q) :
    (fareyIndices Q).erase x =
      (fareyRightNear x ∪ fareyRightFar x) ∪
        (fareyLeftNear x ∪ fareyLeftFar x) := by
  ext y
  simp only [mem_erase, mem_fareyIndices, and_true, mem_union,
    fareyRightNear, fareyRightFar, fareyLeftNear, fareyLeftFar, mem_filter]
  constructor
  · intro hy
    have hvalue : Ne (fareyValue y : Real) (fareyValue x : Real) := by
      intro hxy
      have hrat : fareyValue y = fareyValue x := by exact_mod_cast hxy
      exact hy (fareyValue_injective Q hrat)
    rcases lt_or_gt_of_ne hvalue with hyx | hxy
    · by_cases hhalf : (fareyValue x : Real) - (fareyValue y : Real) <= 1 / 2
      · exact Or.inr (Or.inl ⟨trivial, hyx, hhalf⟩)
      · exact Or.inr (Or.inr ⟨trivial, hyx, lt_of_not_ge hhalf⟩)
    · by_cases hhalf : (fareyValue y : Real) - (fareyValue x : Real) <= 1 / 2
      · exact Or.inl (Or.inl ⟨trivial, hxy, hhalf⟩)
      · exact Or.inl (Or.inr ⟨trivial, hxy, lt_of_not_ge hhalf⟩)
  · intro hy
    rcases hy with (⟨_, hxy, _⟩ | ⟨_, hxy, _⟩) |
      (⟨_, hyx, _⟩ | ⟨_, hyx, _⟩)
    · exact fun heq => by subst y; exact lt_irrefl _ hxy
    · exact fun heq => by subst y; exact lt_irrefl _ hxy
    · exact fun heq => by subst y; exact lt_irrefl _ hyx
    · exact fun heq => by subst y; exact lt_irrefl _ hyx
theorem fareyRightNear_sum {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (x : FareyIndex Q) :
    ∑ y ∈ fareyRightNear x,
        fejerKernel N ((fareyValue x : Real) - (fareyValue y : Real)) <=
      4 * (N : Real) + 5 / (2 * ((1 : Real) / (Q : Real) ^ 2)) := by
  apply fareyFejerSubsum hQ hN x (fareyRightNear x)
    (fun y => (fareyValue y : Real) - (fareyValue x : Real))
  · intro y hy
    simp only [fareyRightNear, mem_filter] at hy
    rw [ratCircleDistance]
    have habs : |(fareyValue x : Real) - (fareyValue y : Real)| =
        (fareyValue y : Real) - (fareyValue x : Real) := by
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hy.2.1)), neg_sub]
    rw [habs, min_eq_left]
    linarith [hy.2.2]
  · intro y hy
    simp only [fareyRightNear, mem_filter] at hy
    have hx0 : (0 : Real) <= fareyValue x := by
      exact_mod_cast fareyValue_nonneg x
    have hy1 : (fareyValue y : Real) < 1 := by
      exact_mod_cast fareyValue_lt_one y
    linarith
  · intro y hy z hz
    congr 1
    ring
  · intro y hy hxy
    subst y
    simp only [fareyRightNear, mem_filter] at hy
    exact (lt_irrefl _ hy.2.1)
theorem fareyRightFar_sum {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (x : FareyIndex Q) :
    ∑ y ∈ fareyRightFar x,
        fejerKernel N ((fareyValue x : Real) - (fareyValue y : Real)) <=
      4 * (N : Real) + 5 / (2 * ((1 : Real) / (Q : Real) ^ 2)) := by
  apply fareyFejerSubsum hQ hN x (fareyRightFar x)
    (fun y => 1 - ((fareyValue y : Real) - (fareyValue x : Real)))
  · intro y hy
    simp only [fareyRightFar, mem_filter] at hy
    rw [ratCircleDistance]
    have habs : |(fareyValue x : Real) - (fareyValue y : Real)| =
        (fareyValue y : Real) - (fareyValue x : Real) := by
      rw [abs_of_nonpos (sub_nonpos.mpr (le_of_lt hy.2.1)), neg_sub]
    rw [habs, min_eq_right]
    linarith [hy.2.2]
  · intro y hy
    simp only [fareyRightFar, mem_filter] at hy
    linarith [hy.2.1]
  · intro y hy z hz
    rw [show
      (1 - ((fareyValue y : Real) - (fareyValue x : Real))) -
          (1 - ((fareyValue z : Real) - (fareyValue x : Real))) =
        -((fareyValue y : Real) - (fareyValue z : Real)) by ring, abs_neg]
  · intro y hy hxy
    subst y
    simp only [fareyRightFar, mem_filter] at hy
    exact (lt_irrefl _ hy.2.1)
theorem fareyLeftNear_sum {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (x : FareyIndex Q) :
    ∑ y ∈ fareyLeftNear x,
        fejerKernel N ((fareyValue x : Real) - (fareyValue y : Real)) <=
      4 * (N : Real) + 5 / (2 * ((1 : Real) / (Q : Real) ^ 2)) := by
  apply fareyFejerSubsum hQ hN x (fareyLeftNear x)
    (fun y => (fareyValue x : Real) - (fareyValue y : Real))
  · intro y hy
    simp only [fareyLeftNear, mem_filter] at hy
    rw [ratCircleDistance]
    have habs : |(fareyValue x : Real) - (fareyValue y : Real)| =
        (fareyValue x : Real) - (fareyValue y : Real) := by
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hy.2.1))]
    rw [habs, min_eq_left]
    linarith [hy.2.2]
  · intro y hy
    simp only [fareyLeftNear, mem_filter] at hy
    have hx1 : (fareyValue x : Real) < 1 := by
      exact_mod_cast fareyValue_lt_one x
    have hy0 : (0 : Real) <= fareyValue y := by
      exact_mod_cast fareyValue_nonneg y
    linarith
  · intro y hy z hz
    rw [show
      ((fareyValue x : Real) - (fareyValue y : Real)) -
          ((fareyValue x : Real) - (fareyValue z : Real)) =
        -((fareyValue y : Real) - (fareyValue z : Real)) by ring, abs_neg]
  · intro y hy hxy
    subst y
    simp only [fareyLeftNear, mem_filter] at hy
    exact (lt_irrefl _ hy.2.1)
theorem fareyLeftFar_sum {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (x : FareyIndex Q) :
    ∑ y ∈ fareyLeftFar x,
        fejerKernel N ((fareyValue x : Real) - (fareyValue y : Real)) <=
      4 * (N : Real) + 5 / (2 * ((1 : Real) / (Q : Real) ^ 2)) := by
  apply fareyFejerSubsum hQ hN x (fareyLeftFar x)
    (fun y => 1 - ((fareyValue x : Real) - (fareyValue y : Real)))
  · intro y hy
    simp only [fareyLeftFar, mem_filter] at hy
    rw [ratCircleDistance]
    have habs : |(fareyValue x : Real) - (fareyValue y : Real)| =
        (fareyValue x : Real) - (fareyValue y : Real) := by
      rw [abs_of_nonneg (sub_nonneg.mpr (le_of_lt hy.2.1))]
    rw [habs, min_eq_right]
    linarith [hy.2.2]
  · intro y hy
    simp only [fareyLeftFar, mem_filter] at hy
    linarith [hy.2.1]
  · intro y hy z hz
    congr 1
    ring
  · intro y hy hxy
    subst y
    simp only [fareyLeftFar, mem_filter] at hy
    exact (lt_irrefl _ hy.2.1)
theorem fareyFejerRowSum {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (x : FareyIndex Q) :
    ∑ y ∈ fareyIndices Q,
        fejerKernel N ((fareyValue x : Real) - (fareyValue y : Real)) <=
      18 * ((N : Real) + (Q : Real) ^ 2) := by
  let f : FareyIndex Q -> Real := fun y =>
    fejerKernel N ((fareyValue x : Real) - (fareyValue y : Real))
  let B : Real := 4 * (N : Real) + 5 / (2 * ((1 : Real) / (Q : Real) ^ 2))
  have hpartition : ∑ y ∈ (fareyIndices Q).erase x, f y =
      (∑ y ∈ fareyRightNear x, f y) + (∑ y ∈ fareyRightFar x, f y) +
        ((∑ y ∈ fareyLeftNear x, f y) + (∑ y ∈ fareyLeftFar x, f y)) := by
    rw [fareyOffdiag_partition]
    rw [Finset.sum_union (fareyRight_disjoint_left x)]
    rw [Finset.sum_union (fareyRightNear_disjoint_rightFar x)]
    rw [Finset.sum_union (fareyLeftNear_disjoint_leftFar x)]
  have hrightNear : ∑ y ∈ fareyRightNear x, f y <= B := by
    exact fareyRightNear_sum hQ hN x
  have hrightFar : ∑ y ∈ fareyRightFar x, f y <= B := by
    exact fareyRightFar_sum hQ hN x
  have hleftNear : ∑ y ∈ fareyLeftNear x, f y <= B := by
    exact fareyLeftNear_sum hQ hN x
  have hleftFar : ∑ y ∈ fareyLeftFar x, f y <= B := by
    exact fareyLeftFar_sum hQ hN x
  have hoffdiag : ∑ y ∈ (fareyIndices Q).erase x, f y <= 4 * B := by
    rw [hpartition]
    linarith
  have hdiag : f x <= 2 * (N : Real) := by
    simpa [f] using fejerKernel_le N 0
  have htotal := add_le_add hoffdiag hdiag
  have hdecomp := Finset.sum_erase_add (fareyIndices Q) f (mem_fareyIndices x)
  change (∑ y ∈ (fareyIndices Q).erase x, f y) + f x =
    ∑ y ∈ fareyIndices Q, f y at hdecomp
  calc
    ∑ y ∈ fareyIndices Q, f y =
        (∑ y ∈ (fareyIndices Q).erase x, f y) + f x := hdecomp.symm
    _ <= 4 * B + 2 * (N : Real) := htotal
    _ <= 18 * ((N : Real) + (Q : Real) ^ 2) := by
      dsimp [B]
      have hQreal : (0 : Real) < Q := by exact_mod_cast hQ
      field_simp [ne_of_gt hQreal]
      nlinarith
end BombieriVinogradov.LargeSieve
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators ComplexConjugate
namespace BombieriVinogradov.LargeSieve
def doubledPhaseMatrix {ι : Type*} (L : Nat) (x : ι -> Real)
    (r : Fin L × Fin L) (i : ι) : Complex :=
  additivePhase ((r.1 : Nat) * x i) * additivePhase (-((r.2 : Nat) * x i))
theorem doubledPhase_gram {ι : Type*} (L : Nat) (x : ι -> Real) (i j : ι) :
    ∑ r : Fin L × Fin L,
        conj (doubledPhaseMatrix L x r i) * doubledPhaseMatrix L x r j =
      phaseSum L (x j - x i) * conj (phaseSum L (x j - x i)) := by
  rw [Fintype.sum_prod_type]
  simp_rw [doubledPhaseMatrix, map_mul, conj_additivePhase]
  simp only [neg_neg]
  have hterm (u v : Fin L) :
      (additivePhase (-((u : Nat) * x i)) * additivePhase ((v : Nat) * x i)) *
          (additivePhase ((u : Nat) * x j) * additivePhase (-((v : Nat) * x j))) =
        additivePhase ((u : Nat) * (x j - x i)) *
          additivePhase (-((v : Nat) * (x j - x i))) := by
    calc
      (additivePhase (-((u : Nat) * x i)) * additivePhase ((v : Nat) * x i)) *
          (additivePhase ((u : Nat) * x j) * additivePhase (-((v : Nat) * x j))) =
        additivePhase (-((u : Nat) * x i) + (v : Nat) * x i) *
          additivePhase ((u : Nat) * x j + (-((v : Nat) * x j))) := by
            rw [additivePhase_add, additivePhase_add]
      _ = additivePhase
          ((-((u : Nat) * x i) + (v : Nat) * x i) +
            ((u : Nat) * x j + (-((v : Nat) * x j)))) :=
        (additivePhase_add _ _).symm
      _ = additivePhase
          ((u : Nat) * (x j - x i) + (-((v : Nat) * (x j - x i)))) := by
        congr 1
        ring
      _ = additivePhase ((u : Nat) * (x j - x i)) *
          additivePhase (-((v : Nat) * (x j - x i))) := additivePhase_add _ _
  simp_rw [hterm]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  have hpos : (∑ u : Fin L, additivePhase ((u : Nat) * (x j - x i))) =
      phaseSum L (x j - x i) := by
    rw [phaseSum]
    exact (Finset.sum_range (fun u => additivePhase ((u : Real) * (x j - x i)))).symm
  have hneg : (∑ v : Fin L, additivePhase (-((v : Nat) * (x j - x i)))) =
      conj (phaseSum L (x j - x i)) := by
    calc
      (∑ v : Fin L, additivePhase (-((v : Nat) * (x j - x i)))) =
          ∑ v : Fin L, conj (additivePhase ((v : Nat) * (x j - x i))) := by
        apply Finset.sum_congr rfl
        intro v hv
        rw [conj_additivePhase]
      _ = conj (∑ v : Fin L, additivePhase ((v : Nat) * (x j - x i))) := by
        rw [map_sum]
      _ = conj (phaseSum L (x j - x i)) := by rw [hpos]
  rw [hpos, hneg]
theorem norm_doubledPhase_gram {ι : Type*} {N : Nat} (hN : 0 < N)
    (x : ι -> Real) (i j : ι) :
    ‖∑ r : Fin (2 * N) × Fin (2 * N),
        conj (doubledPhaseMatrix (2 * N) x r i) *
          doubledPhaseMatrix (2 * N) x r j‖ =
      (N : Real) * fejerKernel (2 * N) (x j - x i) := by
  rw [doubledPhase_gram, norm_mul, norm_conj]
  unfold fejerKernel
  have hNreal : Ne (N : Real) 0 := by exact_mod_cast Nat.ne_of_gt hN
  push_cast
  field_simp [hNreal]
theorem fareyDoubledWindowEnergy {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (b : FareyIndex Q -> Complex) :
    ∑ r ∈ (Finset.univ : Finset (Fin (2 * N) × Fin (2 * N))),
        ‖∑ i ∈ fareyIndices Q,
          doubledPhaseMatrix (2 * N)
            (fun y => (fareyValue y : Real)) r i * b i‖ ^ 2 <=
      ((N : Real) * 18 * ((2 * N : Nat) + (Q : Real) ^ 2)) *
        ∑ i ∈ fareyIndices Q, ‖b i‖ ^ 2 := by
  let xv : FareyIndex Q -> Real := fun y => (fareyValue y : Real)
  let k : FareyIndex Q -> FareyIndex Q -> Real := fun i j =>
    (N : Real) * fejerKernel (2 * N) (xv j - xv i)
  apply complexGramSchurBoundFinset
    (Finset.univ : Finset (Fin (2 * N) × Fin (2 * N)))
    (fareyIndices Q) (doubledPhaseMatrix (2 * N) xv) b k
  · intro i hi j hj
    dsimp [k]
    exact mul_nonneg (Nat.cast_nonneg N) (fejerKernel_nonneg _ _)
  · intro i hi j hj
    dsimp [k, xv]
    congr 1
    rw [show (fareyValue j : Real) - (fareyValue i : Real) =
      -((fareyValue i : Real) - (fareyValue j : Real)) by ring, fejerKernel_neg]
  · intro i hi
    have hrow := fareyFejerRowSum hQ
      (Nat.mul_pos (by norm_num : 0 < 2) hN) i
    dsimp [k, xv]
    calc
      ∑ j ∈ fareyIndices Q, (N : Real) *
          fejerKernel (2 * N) ((fareyValue j : Real) - (fareyValue i : Real)) =
        (N : Real) * ∑ j ∈ fareyIndices Q,
          fejerKernel (2 * N) ((fareyValue j : Real) - (fareyValue i : Real)) := by
            rw [Finset.mul_sum]
      _ = (N : Real) * ∑ j ∈ fareyIndices Q,
          fejerKernel (2 * N) ((fareyValue i : Real) - (fareyValue j : Real)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro j hj
        rw [show (fareyValue j : Real) - (fareyValue i : Real) =
          -((fareyValue i : Real) - (fareyValue j : Real)) by ring, fejerKernel_neg]
      _ <= (N : Real) *
          (18 * (((2 * N : Nat) : Real) + (Q : Real) ^ 2)) := by
        gcongr
      _ = (N : Real) * 18 * ((2 * N : Nat) + (Q : Real) ^ 2) := by ring
  · intro i hi j hj
    simpa using (norm_doubledPhase_gram hN xv i j).le
def fareyDualSample {Q : Nat} (b : FareyIndex Q -> Complex) (n : Nat) : Complex :=
  ∑ i ∈ fareyIndices Q,
    additivePhase ((n : Real) * (fareyValue i : Real)) * b i
def doubledWindowEmbedding (N : Nat) :
    Fin N × Fin N -> Fin (2 * N) × Fin (2 * N) := fun p =>
  (⟨p.1.1 + p.2.1, by omega⟩, ⟨p.2.1, by omega⟩)
theorem doubledWindowEmbedding_injective (N : Nat) :
    Function.Injective (doubledWindowEmbedding N) := by
  intro p q hpq
  have hsecond : p.2.1 = q.2.1 := congrArg (fun z => z.2.1) hpq
  have hfirst : p.1.1 + p.2.1 = q.1.1 + q.2.1 :=
    congrArg (fun z => z.1.1) hpq
  apply Prod.ext
  · apply Fin.ext
    omega
  · apply Fin.ext
    exact hsecond
theorem doubledWindowEmbedding_apply {Q N : Nat}
    (b : FareyIndex Q -> Complex) (p : Fin N × Fin N) :
    ∑ i ∈ fareyIndices Q,
        doubledPhaseMatrix (2 * N) (fun y => (fareyValue y : Real))
          (doubledWindowEmbedding N p) i * b i =
      fareyDualSample b p.1.1 := by
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [doubledPhaseMatrix, doubledWindowEmbedding, fareyDualSample]
  congr 1
  rw [← additivePhase_add]
  congr 1
  push_cast
  ring
theorem fareyDualSample_le_doubledWindow {Q N : Nat}
    (b : FareyIndex Q -> Complex) :
    (N : Real) * ∑ n : Fin N, ‖fareyDualSample b n.1‖ ^ 2 <=
      ∑ r : Fin (2 * N) × Fin (2 * N),
        ‖∑ i ∈ fareyIndices Q,
          doubledPhaseMatrix (2 * N) (fun y => (fareyValue y : Real)) r i * b i‖ ^ 2 := by
  let g : (Fin (2 * N) × Fin (2 * N)) -> Real := fun r =>
    ‖∑ i ∈ fareyIndices Q,
      doubledPhaseMatrix (2 * N) (fun y => (fareyValue y : Real)) r i * b i‖ ^ 2
  have hinj := doubledWindowEmbedding_injective N
  have hle := sum_comp_le_sum_of_injective (doubledWindowEmbedding N) hinj g
    (fun r => sq_nonneg _)
  have heq : ∑ p : Fin N × Fin N, g (doubledWindowEmbedding N p) =
      (N : Real) * ∑ n : Fin N, ‖fareyDualSample b n.1‖ ^ 2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [g, doubledWindowEmbedding_apply]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    rw [Finset.mul_sum]
  rw [← heq]
  exact hle
theorem fareyDualEnergy {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (b : FareyIndex Q -> Complex) :
    ∑ n : Fin N, ‖fareyDualSample b n.1‖ ^ 2 <=
      36 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ i ∈ fareyIndices Q, ‖b i‖ ^ 2 := by
  have hmajor := fareyDualSample_le_doubledWindow (N := N) b
  have hwindow := fareyDoubledWindowEnergy hQ hN b
  have hmul : (N : Real) * ∑ n : Fin N, ‖fareyDualSample b n.1‖ ^ 2 <=
      (N : Real) *
        (18 * (((2 * N : Nat) : Real) + (Q : Real) ^ 2) *
          ∑ i ∈ fareyIndices Q, ‖b i‖ ^ 2) := by
    exact hmajor.trans (by simpa [mul_assoc] using hwindow)
  have hNreal : (0 : Real) < N := by exact_mod_cast hN
  have hbase : ∑ n : Fin N, ‖fareyDualSample b n.1‖ ^ 2 <=
      18 * (((2 * N : Nat) : Real) + (Q : Real) ^ 2) *
        ∑ i ∈ fareyIndices Q, ‖b i‖ ^ 2 :=
    (mul_le_mul_iff_of_pos_left hNreal).mp hmul
  apply hbase.trans
  have hmass : 0 <= ∑ i ∈ fareyIndices Q, ‖b i‖ ^ 2 := by positivity
  have hcoef : 18 * (((2 * N : Nat) : Real) + (Q : Real) ^ 2) <=
      36 * ((N : Real) + (Q : Real) ^ 2) := by
    push_cast
    nlinarith [sq_nonneg (Q : Real)]
  exact mul_le_mul_of_nonneg_right hcoef hmass
def fareyAdditiveSample {Q : Nat} (a : Nat -> Complex) (N : Nat)
    (i : FareyIndex Q) : Complex :=
  ∑ n ∈ range N,
    a n * additivePhase ((n : Real) * (fareyValue i : Real))
theorem fareyAdditive_duality {Q N : Nat} (a : Nat -> Complex) :
    (((∑ i ∈ fareyIndices Q, ‖fareyAdditiveSample a N i‖ ^ 2 : Real) : Real) :
        Complex) =
      ∑ n ∈ range N, a n *
        fareyDualSample (Q := Q)
          (fun i : FareyIndex Q => conj (fareyAdditiveSample (Q := Q) a N i)) n := by
  have hterm (z : Complex) : ((‖z‖ ^ 2 : Real) : Complex) = conj z * z := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  rw [Complex.ofReal_sum]
  simp_rw [hterm, fareyAdditiveSample, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [fareyDualSample, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro i hi
  ring
theorem additiveLargeSieve {Q N : Nat} (hQ : 0 < Q) (hN : 0 < N)
    (a : Nat -> Complex) :
    ∑ i ∈ fareyIndices Q, ‖fareyAdditiveSample a N i‖ ^ 2 <=
      36 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ n ∈ range N, ‖a n‖ ^ 2 := by
  let S : FareyIndex Q -> Complex := fun i => fareyAdditiveSample a N i
  let E : Real := ∑ i ∈ fareyIndices Q, ‖S i‖ ^ 2
  let mass : Real := ∑ n ∈ range N, ‖a n‖ ^ 2
  let b : FareyIndex Q -> Complex := fun i => conj (S i)
  let T : Nat -> Complex := fun n => fareyDualSample b n
  let B : Real := 36 * ((N : Real) + (Q : Real) ^ 2)
  have hE0 : 0 <= E := by dsimp [E]; positivity
  have hid := fareyAdditive_duality (Q := Q) (N := N) a
  change (E : Complex) = ∑ n ∈ range N, a n * T n at hid
  have hnorm : E = ‖∑ n ∈ range N, a n * T n‖ := by
    calc
      E = ‖(E : Complex)‖ := by simp [abs_of_nonneg hE0]
      _ = ‖∑ n ∈ range N, a n * T n‖ := congrArg norm hid
  have htri : E <= ∑ n ∈ range N, ‖a n‖ * ‖T n‖ := by
    calc
      E = ‖∑ n ∈ range N, a n * T n‖ := hnorm
      _ <= ∑ n ∈ range N, ‖a n * T n‖ := norm_sum_le _ _
      _ = ∑ n ∈ range N, ‖a n‖ * ‖T n‖ := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [norm_mul]
  have hsq : E ^ 2 <= (∑ n ∈ range N, ‖a n‖ * ‖T n‖) ^ 2 :=
    pow_le_pow_left₀ hE0 htri 2
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range N)
    (fun n => ‖a n‖) (fun n => ‖T n‖)
  have hpre : E ^ 2 <= mass * ∑ n ∈ range N, ‖T n‖ ^ 2 := by
    exact hsq.trans (by simpa [mass] using hcs)
  have hdualFin := fareyDualEnergy hQ hN b
  have hdual : ∑ n ∈ range N, ‖T n‖ ^ 2 <= B * E := by
    rw [Finset.sum_range]
    simpa [T, B, b, E] using hdualFin
  have hmass0 : 0 <= mass := by dsimp [mass]; positivity
  have hE2 : E ^ 2 <= mass * (B * E) :=
    hpre.trans (mul_le_mul_of_nonneg_left hdual hmass0)
  by_cases hEz : E = 0
  · change E <= B * mass
    rw [hEz]
    dsimp [B, mass]
    positivity
  · have hEpos : 0 < E := lt_of_le_of_ne hE0 (Ne.symm hEz)
    have hcancel : E <= mass * B := by
      apply (mul_le_mul_iff_of_pos_right hEpos).mp
      nlinarith [hE2]
    change E <= B * mass
    nlinarith
end BombieriVinogradov.LargeSieve
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators ComplexConjugate
namespace BombieriVinogradov.LargeSieve
noncomputable local instance characterReductionUnitFintype
    (q : Nat) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _
theorem additivePhase_int_unitFraction {q : Nat} [NeZero q]
    (n : Int) (u : (ZMod q)ˣ) :
    additivePhase ((n : Real) * (unitFraction u : Real)) =
      ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) := by
  rw [show (n : ZMod q) * (u : ZMod q) =
    (n * u.val.val : Int) by norm_num]
  rw [ZMod.stdAddChar_coe]
  rw [additivePhase, circleMap_zero]
  unfold unitFraction
  push_cast
  field_simp [NeZero.ne q]
theorem sum_units_eq_sum_residues {q : Nat} [NeZero q]
    (chi : DirichletCharacter Complex q) (f : ZMod q -> Complex) :
    ∑ u : (ZMod q)ˣ, chi (u : ZMod q) * f u =
      ∑ x : ZMod q, chi x * f x := by
  classical
  let s : Finset (ZMod q) := Finset.univ.filter IsUnit
  have hunits : (∑ u : (ZMod q)ˣ, chi (u : ZMod q) * f u) =
      ∑ x ∈ s, chi x * f x := by
    apply Finset.sum_bij (s := (Finset.univ : Finset (ZMod q)ˣ))
      (t := s) (fun u hu => (u : ZMod q))
    · intro u hu
      simp [s, u.isUnit]
    · intro u hu v hv huv
      exact Units.ext huv
    · intro x hx
      have hxunit : IsUnit x := by simpa [s] using hx
      exact ⟨hxunit.unit, Finset.mem_univ _, hxunit.unit_spec⟩
    · intro u hu
      rfl
  rw [hunits]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro x hxuniv hxnot
  have hxnonunit : ¬IsUnit x := by simpa [s] using hxnot
  rw [MulChar.map_nonunit chi hxnonunit, zero_mul]
def intervalAdditiveResidueSum (a : Int -> Complex) (M : Int) (N q : Nat)
    [NeZero q] (u : (ZMod q)ˣ) : Complex :=
  ∑ n ∈ Ioc M (M + (N : Int)),
    a n * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q))
theorem gauss_mul_intervalCharacterSum {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi)
    (a : Int -> Complex) (M : Int) (N : Nat) :
    gaussSum chi⁻¹ ZMod.stdAddChar * intervalCharacterSum a M N q chi =
      unitCharacterSum (intervalAdditiveResidueSum a M N q) chi⁻¹ := by
  classical
  have hchiInv : DirichletCharacter.IsPrimitive chi⁻¹ := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hchi
  have hshift (n : Int) :
      ∑ u : (ZMod q)ˣ,
          chi⁻¹ (u : ZMod q) *
            ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) =
        chi (n : ZMod q) * gaussSum chi⁻¹ ZMod.stdAddChar := by
    calc
      _ = ∑ x : ZMod q,
          chi⁻¹ x * ZMod.stdAddChar ((n : ZMod q) * x) :=
        sum_units_eq_sum_residues chi⁻¹ _
      _ = gaussSum chi⁻¹ (ZMod.stdAddChar.mulShift (n : ZMod q)) := by
        simp only [gaussSum, AddChar.mulShift_apply]
      _ = _ := by
        simpa using
          (gaussSum_mulShift_of_isPrimitive ZMod.stdAddChar hchiInv (n : ZMod q))
  unfold intervalCharacterSum unitCharacterSum intervalAdditiveResidueSum
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    gaussSum chi⁻¹ ZMod.stdAddChar * (a n * chi (n : ZMod q)) =
        a n * (chi (n : ZMod q) * gaussSum chi⁻¹ ZMod.stdAddChar) := by ring
    _ = a n * ∑ u : (ZMod q)ˣ,
        chi⁻¹ (u : ZMod q) * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) := by
      rw [hshift n]
    _ = ∑ u : (ZMod q)ˣ,
        a n * (chi⁻¹ (u : ZMod q) *
          ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q))) := by
      rw [Finset.mul_sum]
    _ = ∑ u : (ZMod q)ˣ,
        a n * ZMod.stdAddChar ((n : ZMod q) * (u : ZMod q)) *
          chi⁻¹ (u : ZMod q) := by
      apply Finset.sum_congr rfl
      intro u hu
      ring
theorem q_mul_norm_intervalCharacterSum_sq {q : Nat} [NeZero q]
    {chi : DirichletCharacter Complex q} (hchi : DirichletCharacter.IsPrimitive chi)
    (a : Int -> Complex) (M : Int) (N : Nat) :
    (q : Real) * ‖intervalCharacterSum a M N q chi‖ ^ 2 =
      ‖unitCharacterSum (intervalAdditiveResidueSum a M N q) chi⁻¹‖ ^ 2 := by
  have hchiInv : DirichletCharacter.IsPrimitive chi⁻¹ := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hchi
  calc
    (q : Real) * ‖intervalCharacterSum a M N q chi‖ ^ 2 =
        ‖gaussSum chi⁻¹ ZMod.stdAddChar‖ ^ 2 *
          ‖intervalCharacterSum a M N q chi‖ ^ 2 := by
      rw [norm_gaussSum_stdAddChar_sq hchiInv]
    _ = ‖gaussSum chi⁻¹ ZMod.stdAddChar * intervalCharacterSum a M N q chi‖ ^ 2 := by
      rw [norm_mul]
      ring
    _ = _ := by
      rw [gauss_mul_intervalCharacterSum hchi a M N]
theorem sum_primitive_inv (q : Nat) (f : DirichletCharacter Complex q -> Real) :
    ∑ chi ∈ primitiveCharacters q, f chi⁻¹ =
      ∑ chi ∈ primitiveCharacters q, f chi := by
  classical
  apply Finset.sum_bij (s := primitiveCharacters q) (t := primitiveCharacters q)
    (fun chi hchi => chi⁻¹)
  · intro chi hchi
    have hprimitive : DirichletCharacter.IsPrimitive chi := by
      simpa [primitiveCharacters] using hchi
    have hinv : DirichletCharacter.IsPrimitive chi⁻¹ := by
      rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
      exact hprimitive
    simpa [primitiveCharacters] using hinv
  · intro chi hchi psi hpsi heq
    simpa only [inv_inv] using congrArg Inv.inv heq
  · intro psi hpsi
    refine ⟨psi⁻¹, ?_, ?_⟩
    · have hprimitive : DirichletCharacter.IsPrimitive psi := by
        simpa [primitiveCharacters] using hpsi
      have hinv : DirichletCharacter.IsPrimitive psi⁻¹ := by
        rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
        exact hprimitive
      simpa [primitiveCharacters] using hinv
    · simp
  · intro chi hchi
    rfl
theorem weightedPrimitiveCharacterSum_le_additive {q : Nat} [NeZero q]
    (a : Int -> Complex) (M : Int) (N : Nat) :
    ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖intervalCharacterSum a M N q chi‖ ^ 2 <=
      ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖ ^ 2 := by
  classical
  let b : (ZMod q)ˣ -> Complex := intervalAdditiveResidueSum a M N q
  let S : Real := ∑ chi ∈ primitiveCharacters q,
    ‖intervalCharacterSum a M N q chi‖ ^ 2
  let E : Real := ∑ u : (ZMod q)ˣ, ‖b u‖ ^ 2
  have hscaled : (q : Real) * S =
      ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi⁻¹‖ ^ 2 := by
    dsimp [S]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hchi
    have hprimitive : DirichletCharacter.IsPrimitive chi := by
      simpa [primitiveCharacters] using hchi
    exact q_mul_norm_intervalCharacterSum_sq hprimitive a M N
  have hinv :
      (∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi⁻¹‖ ^ 2) =
        ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi‖ ^ 2 := by
    exact sum_primitive_inv q (fun chi => ‖unitCharacterSum b chi‖ ^ 2)
  have hparseval :
      ∑ chi ∈ primitiveCharacters q, ‖unitCharacterSum b chi‖ ^ 2 <=
        (q.totient : Real) * E := by
    simpa [E] using primitiveCharacterParseval_le b
  have hcore : (q : Real) * S <= (q.totient : Real) * E := by
    rw [hscaled, hinv]
    exact hparseval
  have hphi : 0 < (q.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  change ((q : Real) / (q.totient : Real)) * S <= E
  calc
    ((q : Real) / (q.totient : Real)) * S =
        ((q : Real) * S) / (q.totient : Real) := by ring
    _ <= ((q.totient : Real) * E) / (q.totient : Real) := by
      exact (div_le_div_iff_of_pos_right hphi).2 hcore
    _ = E := by field_simp
theorem sum_int_Ioc_eq_sum_range {R : Type*} [AddCommMonoid R]
    (f : Int -> R) (M : Int) (N : Nat) :
    ∑ n ∈ Ioc M (M + (N : Int)), f n =
      ∑ k ∈ range N, f (M + (k : Int) + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hle : M <= M + (N : Int) := by omega
      rw [Nat.cast_succ]
      rw [← add_assoc]
      rw [← Finset.insert_Ioc_right_eq_Ioc_add_one hle]
      rw [Finset.sum_insert]
      · rw [Finset.sum_range_succ, ih]
        simp [add_comm, add_assoc]
      · simp
def shiftedIntervalCoefficients (a : Int -> Complex) (M : Int) (k : Nat) : Complex :=
  a (M + (k : Int) + 1)
theorem intervalAdditiveResidueSum_eq_phase_mul_fareySample
    {Q q : Nat} [NeZero q] (hq : q ∈ Icc 1 Q)
    (a : Int -> Complex) (M : Int) (N : Nat) (u : (ZMod q)ˣ) :
    intervalAdditiveResidueSum a M N q u =
      additivePhase (((M + 1 : Int) : Real) * (unitFraction u : Real)) *
        fareyAdditiveSample (shiftedIntervalCoefficients a M) N ⟨⟨q, hq⟩, u⟩ := by
  rw [intervalAdditiveResidueSum, sum_int_Ioc_eq_sum_range]
  unfold fareyAdditiveSample shiftedIntervalCoefficients fareyValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← additivePhase_int_unitFraction (M + (k : Int) + 1) u]
  rw [show (((M + (k : Int) + 1 : Int) : Real) * (unitFraction u : Real)) =
      (((M + 1 : Int) : Real) * (unitFraction u : Real)) +
        ((k : Real) * (unitFraction u : Real)) by
    push_cast
    ring]
  rw [additivePhase_add]
  ring
theorem norm_intervalAdditiveResidueSum_eq_fareySample
    {Q q : Nat} [NeZero q] (hq : q ∈ Icc 1 Q)
    (a : Int -> Complex) (M : Int) (N : Nat) (u : (ZMod q)ˣ) :
    ‖intervalAdditiveResidueSum a M N q u‖ =
      ‖fareyAdditiveSample (shiftedIntervalCoefficients a M) N ⟨⟨q, hq⟩, u⟩‖ := by
  rw [intervalAdditiveResidueSum_eq_phase_mul_fareySample hq a M N u]
  rw [norm_mul, norm_additivePhase, one_mul]
theorem sum_fareyIndices_eq_sum_attach {Q : Nat} (f : FareyIndex Q -> Real) :
    ∑ i ∈ fareyIndices Q, f i =
      ∑ q ∈ (Icc 1 Q).attach, ∑ u : (ZMod q.1)ˣ, f ⟨q, u⟩ := by
  unfold fareyIndices
  rw [Finset.sum_sigma]
def modulusAdditiveEnergy (a : Int -> Complex) (M : Int) (N q : Nat) : Real :=
  if hq : q = 0 then 0 else
    letI : NeZero q := ⟨hq⟩
    ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖ ^ 2
theorem modulusAdditiveEnergy_eq {q : Nat} [NeZero q]
    (a : Int -> Complex) (M : Int) (N : Nat) :
    modulusAdditiveEnergy a M N q =
      ∑ u : (ZMod q)ˣ, ‖intervalAdditiveResidueSum a M N q u‖ ^ 2 := by
  simp [modulusAdditiveEnergy, NeZero.ne q]
theorem sum_modulusAdditiveEnergy_eq_fareySamples
    (Q : Nat) (a : Int -> Complex) (M : Int) (N : Nat) :
    ∑ q ∈ Icc 1 Q, modulusAdditiveEnergy a M N q =
      ∑ i ∈ fareyIndices Q,
        ‖fareyAdditiveSample (shiftedIntervalCoefficients a M) N i‖ ^ 2 := by
  rw [sum_fareyIndices_eq_sum_attach]
  rw [← Finset.sum_attach (Icc 1 Q) (modulusAdditiveEnergy a M N)]
  apply Finset.sum_congr rfl
  intro q hqattach
  let _ : NeZero q.1 := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp q.2).1⟩
  rw [modulusAdditiveEnergy_eq]
  apply Finset.sum_congr rfl
  intro u hu
  rw [norm_intervalAdditiveResidueSum_eq_fareySample q.2 a M N u]
theorem characterLargeSieveNat (M : Int) (N Q : Nat) (a : Int -> Complex)
    (hQ : 1 <= Q) :
    ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖intervalCharacterSum a M N q chi‖ ^ 2 <=
      36 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ n ∈ Ioc M (M + (N : Int)), ‖a n‖ ^ 2 := by
  by_cases hNzero : N = 0
  · subst N
    simp [intervalCharacterSum]
  have hN : 0 < N := Nat.pos_of_ne_zero hNzero
  have hQpos : 0 < Q := Nat.zero_lt_of_lt hQ
  have hfixed :
      (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q,
            ‖intervalCharacterSum a M N q chi‖ ^ 2) <=
        ∑ q ∈ Icc 1 Q, modulusAdditiveEnergy a M N q := by
    apply Finset.sum_le_sum
    intro q hq
    let _ : NeZero q := ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
    rw [modulusAdditiveEnergy_eq]
    exact weightedPrimitiveCharacterSum_le_additive a M N
  calc
    _ <= ∑ q ∈ Icc 1 Q, modulusAdditiveEnergy a M N q := hfixed
    _ = ∑ i ∈ fareyIndices Q,
        ‖fareyAdditiveSample (shiftedIntervalCoefficients a M) N i‖ ^ 2 :=
      sum_modulusAdditiveEnergy_eq_fareySamples Q a M N
    _ <= 36 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ k ∈ range N, ‖shiftedIntervalCoefficients a M k‖ ^ 2 :=
      additiveLargeSieve hQpos hN (shiftedIntervalCoefficients a M)
    _ = 36 * ((N : Real) + (Q : Real) ^ 2) *
        ∑ n ∈ Ioc M (M + (N : Int)), ‖a n‖ ^ 2 := by
      rw [sum_int_Ioc_eq_sum_range (fun n => ‖a n‖ ^ 2) M N]
      rfl
theorem characterLargeSieve : CharacterLargeSieveStatement := by
  refine ⟨36, by norm_num, ?_⟩
  intro M N Q a hQ
  exact characterLargeSieveNat M N Q a hQ
end BombieriVinogradov.LargeSieve
end
end

section
noncomputable section
open Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
abbrev PrimitiveCharacterIndex :=
  Sigma fun q : Nat => DirichletCharacter Complex q
def primitiveCharacterIndices (Q : Nat) : Finset PrimitiveCharacterIndex :=
  (Icc 1 Q).sigma primitiveCharacters
theorem positiveCharacterEnergy (M Q : Nat) (a : Nat -> Complex)
    (hQ : 1 <= Q) :
    ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q, ‖positiveCharacterSum a M q chi‖ ^ 2 <=
      36 * ((M : Real) + (Q : Real) ^ 2) * positiveCoefficientMass a M := by
  simpa [positiveCharacterSum, positiveCoefficientMass] using
    (characterLargeSieveNat 0 M Q (positiveIntervalCoefficients a) hQ)
theorem nonmaximalBilinearLargeSieve
    (M N Q : Nat) (a b : Nat -> Complex) (hQ : 1 <= Q) :
    ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖bilinearCharacterProduct a b M N q chi‖ <=
      Real.sqrt (36 * ((M : Real) + (Q : Real) ^ 2) *
          positiveCoefficientMass a M) *
        Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) *
          positiveCoefficientMass b N) := by
  let weight : PrimitiveCharacterIndex -> Real := fun i =>
    (i.1 : Real) / (i.1.totient : Real)
  let left : PrimitiveCharacterIndex -> Real := fun i =>
    ‖positiveCharacterSum a M i.1 i.2‖
  let right : PrimitiveCharacterIndex -> Real := fun i =>
    ‖positiveCharacterSum b N i.1 i.2‖
  let leftWeighted : PrimitiveCharacterIndex -> Real := fun i =>
    Real.sqrt (weight i) * left i
  let rightWeighted : PrimitiveCharacterIndex -> Real := fun i =>
    Real.sqrt (weight i) * right i
  have hweight (i : PrimitiveCharacterIndex) (hi : i ∈ primitiveCharacterIndices Q) :
      0 <= weight i := by
    dsimp [weight]
    positivity
  have hleftSquare :
      ∑ i ∈ primitiveCharacterIndices Q, leftWeighted i ^ 2 =
        ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q, ‖positiveCharacterSum a M q chi‖ ^ 2 := by
    unfold primitiveCharacterIndices
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hchi
    have hw : 0 <= (q : Real) / (q.totient : Real) := by positivity
    dsimp [leftWeighted, weight, left]
    rw [mul_pow, Real.sq_sqrt hw]
  have hrightSquare :
      ∑ i ∈ primitiveCharacterIndices Q, rightWeighted i ^ 2 =
        ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q, ‖positiveCharacterSum b N q chi‖ ^ 2 := by
    unfold primitiveCharacterIndices
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hchi
    have hw : 0 <= (q : Real) / (q.totient : Real) := by positivity
    dsimp [rightWeighted, weight, right]
    rw [mul_pow, Real.sq_sqrt hw]
  have hcauchy := Real.sum_mul_le_sqrt_mul_sqrt
    (primitiveCharacterIndices Q) leftWeighted rightWeighted
  have hflatten :
      (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q,
            ‖bilinearCharacterProduct a b M N q chi‖) =
        ∑ i ∈ primitiveCharacterIndices Q, leftWeighted i * rightWeighted i := by
    unfold primitiveCharacterIndices
    rw [Finset.sum_sigma]
    apply Finset.sum_congr rfl
    intro q hq
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro chi hchi
    have hw : 0 <= (q : Real) / (q.totient : Real) := by positivity
    rw [show bilinearCharacterProduct a b M N q chi =
      positiveCharacterSum a M q chi * positiveCharacterSum b N q chi by rfl]
    rw [norm_mul]
    dsimp [leftWeighted, rightWeighted, weight, left, right]
    calc
      ((q : Real) / (q.totient : Real)) *
          (‖positiveCharacterSum a M q chi‖ *
            ‖positiveCharacterSum b N q chi‖) =
        (Real.sqrt ((q : Real) / (q.totient : Real)) *
            Real.sqrt ((q : Real) / (q.totient : Real))) *
          ‖positiveCharacterSum a M q chi‖ *
          ‖positiveCharacterSum b N q chi‖ := by
            rw [Real.mul_self_sqrt hw]
            ring
      _ = (Real.sqrt ((q : Real) / (q.totient : Real)) *
              ‖positiveCharacterSum a M q chi‖) *
            (Real.sqrt ((q : Real) / (q.totient : Real)) *
              ‖positiveCharacterSum b N q chi‖) := by ring
  rw [hflatten]
  apply hcauchy.trans
  rw [hleftSquare, hrightSquare]
  have hleftEnergy := positiveCharacterEnergy M Q a hQ
  have hrightEnergy := positiveCharacterEnergy N Q b hQ
  gcongr
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex MeasureTheory Real Set
open scoped FourierTransform Interval
namespace BombieriVinogradov.LogCutoff
def intervalBox (a b : Real) : Real -> Complex :=
  (Icc a b).indicator fun _ => 1
theorem intervalBox_integrable (a b : Real) : Integrable (intervalBox a b) := by
  exact continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
theorem integral_intervalBox (a b : Real) (hab : a <= b) :
    ∫ x : Real, intervalBox a b x = (b - a : Complex) := by
  rw [intervalBox, integral_indicator measurableSet_Icc]
  simp [hab]
theorem intervalBox_fourier_eq_intervalIntegral (a b xi : Real) (hab : a <= b) :
    𝓕 (intervalBox a b) xi =
      ∫ x in a..b, Complex.exp ((-2 * Real.pi * Complex.I * (xi : Complex)) * x) := by
  rw [Real.fourier_eq]
  simp only [intervalBox, Circle.smul_def, Real.fourierChar_apply]
  rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Icc a b
  · simp only [indicator_of_mem hx, smul_eq_mul, mul_one]
    congr 1
    push_cast
    simp
    ring
  · simp [hx]
theorem intervalBox_fourier_of_ne (a b xi : Real) (hab : a <= b) (hxi : Ne xi 0) :
    𝓕 (intervalBox a b) xi =
      (Complex.exp ((-2 * Real.pi * Complex.I * (xi : Complex)) * b) -
          Complex.exp ((-2 * Real.pi * Complex.I * (xi : Complex)) * a)) /
        (-2 * Real.pi * Complex.I * (xi : Complex)) := by
  rw [intervalBox_fourier_eq_intervalIntegral a b xi hab]
  have hc : Ne (-2 * Real.pi * Complex.I * (xi : Complex)) 0 := by
    norm_num [hxi, Real.pi_ne_zero]
  simpa using
    (integral_exp_mul_complex (a := a) (b := b) hc)
theorem intervalBox_fourier_norm_le_inv (a b xi : Real) (hab : a <= b)
    (hxi : Ne xi 0) :
    ‖𝓕 (intervalBox a b) xi‖ <= 1 / (Real.pi * |xi|) := by
  rw [intervalBox_fourier_of_ne a b xi hab hxi, norm_div]
  have hnum :
      ‖Complex.exp ((-2 * Real.pi * Complex.I * (xi : Complex)) * b) -
          Complex.exp ((-2 * Real.pi * Complex.I * (xi : Complex)) * a)‖ <= 2 := by
    calc
      _ <= ‖Complex.exp ((-2 * Real.pi * Complex.I * (xi : Complex)) * b)‖ +
          ‖Complex.exp ((-2 * Real.pi * Complex.I * (xi : Complex)) * a)‖ :=
        norm_sub_le _ _
      _ = 2 := by
        simp [Complex.norm_exp]
        norm_num
  have hden :
      ‖-2 * Real.pi * Complex.I * (xi : Complex)‖ = 2 * Real.pi * |xi| := by
    simp [abs_of_nonneg Real.pi_pos.le, Real.norm_eq_abs]
  rw [hden]
  calc
    _ <= 2 / (2 * Real.pi * |xi|) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = 1 / (Real.pi * |xi|) := by
      field_simp
theorem intervalBox_fourier_norm_le_length (a b xi : Real) (hab : a <= b) :
    ‖𝓕 (intervalBox a b) xi‖ <= b - a := by
  calc
    ‖𝓕 (intervalBox a b) xi‖ <= ∫ x : Real, ‖intervalBox a b x‖ :=
      VectorFourier.norm_fourierIntegral_le_integral_norm
        Real.fourierChar volume (innerₗ Real) (intervalBox a b) xi
    _ = b - a := by
      simp only [intervalBox, norm_indicator_eq_indicator_norm, norm_one]
      rw [integral_indicator measurableSet_Icc]
      simp [hab]
end BombieriVinogradov.LogCutoff
end
end

section
noncomputable section
open Complex MeasureTheory Real Set
open scoped Convolution FourierTransform Interval
namespace BombieriVinogradov.LogCutoff
def logTrapezoid (eps L : Real) : Real -> Complex :=
  (eps : Complex)⁻¹ •
    (intervalBox 0 eps ⋆[ContinuousLinearMap.mul Complex Complex]
      intervalBox (-2 * eps) (L + eps))
theorem logTrapezoid_integrable (eps L : Real) : Integrable (logTrapezoid eps L) := by
  have h := (intervalBox_integrable 0 eps).integrable_convolution
    (ContinuousLinearMap.mul Complex Complex)
    (intervalBox_integrable (-2 * eps) (L + eps))
  change Integrable (fun x : Real => (eps : Complex)⁻¹ *
    (intervalBox 0 eps ⋆[ContinuousLinearMap.mul Complex Complex]
      intervalBox (-2 * eps) (L + eps)) x)
  exact h.const_mul ((eps : Complex)⁻¹)
theorem fourier_logTrapezoid (eps L xi : Real) :
    𝓕 (logTrapezoid eps L) xi =
      (eps : Complex)⁻¹ * 𝓕 (intervalBox 0 eps) xi *
        𝓕 (intervalBox (-2 * eps) (L + eps)) xi := by
  rw [logTrapezoid]
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Real)
      ((eps : Complex)⁻¹ •
        (intervalBox 0 eps ⋆[ContinuousLinearMap.mul Complex Complex]
          intervalBox (-2 * eps) (L + eps))) xi = _
  rw [VectorFourier.fourierIntegral_const_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  have hconv := Real.fourier_mul_convolution_eq
    (intervalBox_integrable 0 eps)
    (intervalBox_integrable (-2 * eps) (L + eps)) xi
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Real)
      (intervalBox 0 eps ⋆[ContinuousLinearMap.mul Complex Complex]
        intervalBox (-2 * eps) (L + eps)) xi = _ at hconv
  rw [hconv]
  ring
theorem norm_fourier_logTrapezoid_le_length (eps L xi : Real)
    (heps : 0 < eps) (hL : 0 <= L) :
    ‖𝓕 (logTrapezoid eps L) xi‖ <= L + 3 * eps := by
  have horder : -2 * eps <= L + eps := by linarith
  have hsmall : ‖𝓕 (intervalBox 0 eps) xi‖ <= eps := by
    simpa using intervalBox_fourier_norm_le_length 0 eps xi heps.le
  have hlarge : ‖𝓕 (intervalBox (-2 * eps) (L + eps)) xi‖ <= L + 3 * eps := by
    convert intervalBox_fourier_norm_le_length (-2 * eps) (L + eps) xi horder using 1
    ring
  have hinv : ‖(eps : Complex)⁻¹‖ = eps⁻¹ := by
    simp [abs_of_pos heps]
  rw [fourier_logTrapezoid, norm_mul, norm_mul, hinv]
  calc
    eps⁻¹ * ‖𝓕 (intervalBox 0 eps) xi‖ *
        ‖𝓕 (intervalBox (-2 * eps) (L + eps)) xi‖ <=
      eps⁻¹ * eps * (L + 3 * eps) := by gcongr
    _ = L + 3 * eps := by field_simp [heps.ne']
theorem norm_fourier_logTrapezoid_le_inv (eps L xi : Real)
    (heps : 0 < eps) (hL : 0 <= L) (hxi : Ne xi 0) :
    ‖𝓕 (logTrapezoid eps L) xi‖ <= 1 / (Real.pi * |xi|) := by
  have horder : -2 * eps <= L + eps := by linarith
  have hsmall : ‖𝓕 (intervalBox 0 eps) xi‖ <= eps := by
    simpa using intervalBox_fourier_norm_le_length 0 eps xi heps.le
  have hlarge := intervalBox_fourier_norm_le_inv
    (-2 * eps) (L + eps) xi horder hxi
  have hinv : ‖(eps : Complex)⁻¹‖ = eps⁻¹ := by
    simp [abs_of_pos heps]
  rw [fourier_logTrapezoid, norm_mul, norm_mul, hinv]
  calc
    eps⁻¹ * ‖𝓕 (intervalBox 0 eps) xi‖ *
        ‖𝓕 (intervalBox (-2 * eps) (L + eps)) xi‖ <=
      eps⁻¹ * eps * (1 / (Real.pi * |xi|)) := by gcongr
    _ = 1 / (Real.pi * |xi|) := by field_simp [heps.ne']
theorem norm_fourier_logTrapezoid_le_inv_sq (eps L xi : Real)
    (heps : 0 < eps) (hL : 0 <= L) (hxi : Ne xi 0) :
    ‖𝓕 (logTrapezoid eps L) xi‖ <=
      1 / (eps * Real.pi ^ 2 * |xi| ^ 2) := by
  have horder : -2 * eps <= L + eps := by linarith
  have hsmall := intervalBox_fourier_norm_le_inv 0 eps xi heps.le hxi
  have hlarge := intervalBox_fourier_norm_le_inv
    (-2 * eps) (L + eps) xi horder hxi
  have hinv : ‖(eps : Complex)⁻¹‖ = eps⁻¹ := by
    simp [abs_of_pos heps]
  rw [fourier_logTrapezoid, norm_mul, norm_mul, hinv]
  calc
    eps⁻¹ * ‖𝓕 (intervalBox 0 eps) xi‖ *
        ‖𝓕 (intervalBox (-2 * eps) (L + eps)) xi‖ <=
      eps⁻¹ * (1 / (Real.pi * |xi|)) *
        (1 / (Real.pi * |xi|)) := by gcongr
    _ = 1 / (eps * Real.pi ^ 2 * |xi| ^ 2) := by
      field_simp [heps.ne', Real.pi_ne_zero, abs_ne_zero.mpr hxi]
def centerMajorant (A : Real) : Real -> Real :=
  (Icc 0 A⁻¹).indicator fun _ => A
def middleMajorant (A eps : Real) : Real -> Real :=
  (Ioc A⁻¹ eps⁻¹).indicator fun x => x⁻¹
def tailMajorant (eps : Real) : Real -> Real :=
  (Ioi eps⁻¹).indicator fun x => eps⁻¹ * x ^ (-2 : Real)
def positiveSpectralMajorant (A eps : Real) : Real -> Real :=
  centerMajorant A + middleMajorant A eps + tailMajorant eps
def spectralMajorant (A eps : Real) (x : Real) : Real :=
  positiveSpectralMajorant A eps |x|
theorem centerMajorant_integrable (A : Real) : Integrable (centerMajorant A) := by
  exact continuous_const.integrableOn_Icc.integrable_indicator measurableSet_Icc
theorem middleMajorant_integrable (A eps : Real) (hA : 0 < A) :
    Integrable (middleMajorant A eps) := by
  have hcontinuous : ContinuousOn (fun x : Real => x⁻¹) (Icc A⁻¹ eps⁻¹) :=
    continuousOn_inv₀.mono fun x hx => ne_of_gt ((inv_pos.mpr hA).trans_le hx.1)
  exact IntegrableOn.integrable_indicator
    (hcontinuous.integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc
theorem tailMajorant_integrable (eps : Real) (heps : 0 < eps) :
    Integrable (tailMajorant eps) := by
  have htail := integrableOn_Ioi_rpow_of_lt (a := (-2 : Real)) (by norm_num)
    (inv_pos.mpr heps)
  exact IntegrableOn.integrable_indicator (htail.const_mul eps⁻¹) measurableSet_Ioi
theorem positiveSpectralMajorant_integrable (A eps : Real)
    (hA : 0 < A) (heps : 0 < eps) :
    Integrable (positiveSpectralMajorant A eps) := by
  exact ((centerMajorant_integrable A).add (middleMajorant_integrable A eps hA)).add
    (tailMajorant_integrable eps heps)
theorem integral_centerMajorant (A : Real) (hA : 0 < A) :
    ∫ x : Real, centerMajorant A x = 1 := by
  rw [centerMajorant, integral_indicator measurableSet_Icc]
  simp only [integral_const, Measure.real, smul_eq_mul]
  rw [Measure.restrict_apply_univ, Real.volume_Icc]
  simp only [sub_zero, ENNReal.toReal_ofReal (inv_nonneg.mpr hA.le)]
  field_simp [hA.ne']
theorem integral_middleMajorant (A eps : Real) (hA : 0 < A)
    (heps : 0 < eps) (hepsA : eps <= A) :
    ∫ x : Real, middleMajorant A eps x = Real.log (A / eps) := by
  have hinvle : A⁻¹ <= eps⁻¹ := (inv_le_inv₀ hA heps).2 hepsA
  rw [middleMajorant, integral_indicator measurableSet_Ioc]
  rw [← intervalIntegral.integral_of_le hinvle]
  rw [integral_inv_of_pos (inv_pos.mpr hA) (inv_pos.mpr heps)]
  congr 1
  field_simp [hA.ne', heps.ne']
theorem integral_tailMajorant (eps : Real) (heps : 0 < eps) :
    ∫ x : Real, tailMajorant eps x = 1 := by
  rw [tailMajorant, integral_indicator measurableSet_Ioi]
  rw [integral_const_mul]
  rw [integral_Ioi_rpow_of_lt (a := (-2 : Real)) (by norm_num) (inv_pos.mpr heps)]
  norm_num [Real.rpow_neg_one, heps.ne']
theorem integral_positiveSpectralMajorant (A eps : Real) (hA : 0 < A)
    (heps : 0 < eps) (hepsA : eps <= A) :
    ∫ x : Real, positiveSpectralMajorant A eps x = 2 + Real.log (A / eps) := by
  have hc := centerMajorant_integrable A
  have hm := middleMajorant_integrable A eps hA
  have ht := tailMajorant_integrable eps heps
  change ∫ x : Real, (centerMajorant A x + middleMajorant A eps x) +
    tailMajorant eps x = _
  calc
    _ = (∫ x : Real, centerMajorant A x + middleMajorant A eps x) +
        ∫ x : Real, tailMajorant eps x := integral_add (hc.add hm) ht
    _ = ((∫ x : Real, centerMajorant A x) +
          ∫ x : Real, middleMajorant A eps x) +
        ∫ x : Real, tailMajorant eps x := by rw [integral_add hc hm]
    _ = 2 + Real.log (A / eps) := by
      rw [integral_centerMajorant A hA,
        integral_middleMajorant A eps hA heps hepsA,
        integral_tailMajorant eps heps]
      ring
theorem positiveSpectralMajorant_eq_zero_of_nonpos (A eps x : Real)
    (hA : 0 < A) (heps : 0 < eps) (hx : x < 0) :
    positiveSpectralMajorant A eps x = 0 := by
  have hAinv : 0 < A⁻¹ := inv_pos.mpr hA
  have hepsinv : 0 < eps⁻¹ := inv_pos.mpr heps
  have hnotcenter : x ∉ Icc (0 : Real) A⁻¹ := fun hmem =>
    (not_le_of_gt hx) hmem.1
  have hnotmiddle : x ∉ Ioc A⁻¹ eps⁻¹ := fun hmem =>
    (not_lt_of_ge hAinv.le) (hmem.1.trans hx)
  have hnottail : x ∉ Ioi eps⁻¹ := fun hmem =>
    (not_lt_of_ge hepsinv.le) (hmem.trans hx)
  simp [positiveSpectralMajorant, centerMajorant, middleMajorant,
    tailMajorant, hnotcenter, hnotmiddle, hnottail]
theorem spectralMajorant_integrable (A eps : Real) (hA : 0 < A)
    (heps : 0 < eps) : Integrable (spectralMajorant A eps) := by
  have hpositive := positiveSpectralMajorant_integrable A eps hA heps
  have hright : IntegrableOn (spectralMajorant A eps) (Ioi (0 : Real)) := by
    refine hpositive.integrableOn.congr_fun ?_ measurableSet_Ioi
    intro x hx
    rw [spectralMajorant, abs_of_pos (mem_Ioi.mp hx)]
  change IntegrableOn (fun x : Real => positiveSpectralMajorant A eps |x|)
    (Ioi (0 : Real)) at hright
  have hleft : IntegrableOn (spectralMajorant A eps) (Iic (0 : Real)) := by
    rw [← Measure.map_neg_eq_self (volume : Measure Real)]
    let m : MeasurableEmbedding fun x : Real => -x := (Homeomorph.neg Real).measurableEmbedding
    rw [m.integrableOn_map_iff]
    simpa only [Function.comp_def, spectralMajorant, abs_neg, neg_preimage,
      neg_Iic, neg_zero] using
      (Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi hright)
  rw [← integrableOn_univ, ← Iic_union_Ioi]
  exact hleft.union hright
theorem integral_spectralMajorant (A eps : Real) (hA : 0 < A)
    (heps : 0 < eps) (hepsA : eps <= A) :
    ∫ x : Real, spectralMajorant A eps x =
      4 + 2 * Real.log (A / eps) := by
  change ∫ x : Real, positiveSpectralMajorant A eps |x| = _
  rw [integral_comp_abs]
  have hrestrict :
      ∫ x : Real in Ioi 0, positiveSpectralMajorant A eps x =
        ∫ x : Real, positiveSpectralMajorant A eps x := by
    rw [← integral_indicator measurableSet_Ioi]
    apply integral_congr_ae
    filter_upwards [(volume : Measure Real).ae_ne 0] with x hxzero
    by_cases hx : x ∈ Ioi (0 : Real)
    · simp [hx]
    · simp only [Set.indicator_apply, if_neg hx]
      exact (positiveSpectralMajorant_eq_zero_of_nonpos A eps x hA heps
        (lt_of_le_of_ne (not_lt.mp hx) hxzero)).symm
  rw [hrestrict, integral_positiveSpectralMajorant A eps hA heps hepsA]
  ring
theorem norm_fourier_logTrapezoid_le_spectralMajorant (eps L xi : Real)
    (heps : 0 < eps) (hL : 0 <= L) :
    ‖𝓕 (logTrapezoid eps L) xi‖ <= spectralMajorant (L + 3 * eps) eps xi := by
  let A : Real := L + 3 * eps
  have hA : 0 < A := by dsimp [A]; linarith
  have hepsA : eps <= A := by dsimp [A]; linarith
  have hinvle : A⁻¹ <= eps⁻¹ := (inv_le_inv₀ hA heps).2 hepsA
  have hpi : 1 <= Real.pi := by nlinarith [Real.one_le_pi_div_two]
  change ‖𝓕 (logTrapezoid eps L) xi‖ <= spectralMajorant A eps xi
  by_cases hcenter : |xi| <= A⁻¹
  · have hcenterMem : |xi| ∈ Icc (0 : Real) A⁻¹ := ⟨abs_nonneg xi, hcenter⟩
    have hmiddleNot : |xi| ∉ Ioc A⁻¹ eps⁻¹ := fun hmem =>
      (not_lt_of_ge hcenter) hmem.1
    have htailNot : |xi| ∉ Ioi eps⁻¹ := fun hmem =>
      (not_lt_of_ge (hcenter.trans hinvle)) hmem
    have hbound : ‖𝓕 (logTrapezoid eps L) xi‖ <= A := by
      simpa [A] using norm_fourier_logTrapezoid_le_length eps L xi heps hL
    rw [spectralMajorant]
    simpa [positiveSpectralMajorant, centerMajorant, middleMajorant,
      tailMajorant, hcenterMem, hmiddleNot, htailNot] using hbound
  · have hAxi : A⁻¹ < |xi| := lt_of_not_ge hcenter
    by_cases hmiddle : |xi| <= eps⁻¹
    · have hmiddleMem : |xi| ∈ Ioc A⁻¹ eps⁻¹ := ⟨hAxi, hmiddle⟩
      have hcenterNot : |xi| ∉ Icc (0 : Real) A⁻¹ := fun hmem =>
        (not_lt_of_ge hmem.2) hAxi
      have htailNot : |xi| ∉ Ioi eps⁻¹ := fun hmem =>
        (not_lt_of_ge hmiddle) hmem
      have hy : 0 < |xi| := (inv_pos.mpr hA).trans hAxi
      have hxi : Ne xi 0 := abs_pos.mp hy
      have hpiBound : 1 / (Real.pi * |xi|) <= |xi|⁻¹ := by
        have hyMul : |xi| <= Real.pi * |xi| := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi hy.le
        simpa only [one_div] using one_div_le_one_div_of_le hy hyMul
      have hbound := (norm_fourier_logTrapezoid_le_inv eps L xi heps hL hxi).trans
        hpiBound
      rw [spectralMajorant]
      simpa [positiveSpectralMajorant, centerMajorant, middleMajorant,
        tailMajorant, hcenterNot, hmiddleMem, htailNot] using hbound
    · have htail : eps⁻¹ < |xi| := lt_of_not_ge hmiddle
      have htailMem : |xi| ∈ Ioi eps⁻¹ := htail
      have hcenterNot : |xi| ∉ Icc (0 : Real) A⁻¹ := fun hmem =>
        (not_lt_of_ge hmem.2) hAxi
      have hmiddleNot : |xi| ∉ Ioc A⁻¹ eps⁻¹ := fun hmem =>
        (not_lt_of_ge hmem.2) htail
      have hy : 0 < |xi| := (inv_pos.mpr heps).trans htail
      have hxi : Ne xi 0 := abs_pos.mp hy
      have hpiSq : 1 <= Real.pi ^ 2 := by nlinarith
      have hden : eps * |xi| ^ 2 <= eps * Real.pi ^ 2 * |xi| ^ 2 := by
        calc
          eps * |xi| ^ 2 = (eps * |xi| ^ 2) * 1 := by ring
          _ <= (eps * |xi| ^ 2) * Real.pi ^ 2 :=
            mul_le_mul_of_nonneg_left hpiSq (mul_nonneg heps.le (sq_nonneg _))
          _ = eps * Real.pi ^ 2 * |xi| ^ 2 := by ring
      have hdenPos : 0 < eps * |xi| ^ 2 := mul_pos heps (sq_pos_of_pos hy)
      have hpiBound :
          1 / (eps * Real.pi ^ 2 * |xi| ^ 2) <= 1 / (eps * |xi| ^ 2) := by
        exact one_div_le_one_div_of_le hdenPos hden
      have hrpow : |xi| ^ (-2 : Real) = (|xi| ^ 2)⁻¹ := by
        calc
          |xi| ^ (-2 : Real) = |xi| ^ (-2 : Int) :=
            Real.rpow_neg_natCast |xi| 2
          _ = (|xi| ^ 2)⁻¹ := by norm_num [zpow_neg]
      have halgebra : 1 / (eps * |xi| ^ 2) = eps⁻¹ * |xi| ^ (-2 : Real) := by
        rw [hrpow]
        field_simp [heps.ne', abs_ne_zero.mpr hxi]
      have hbound := (norm_fourier_logTrapezoid_le_inv_sq eps L xi heps hL hxi).trans
        hpiBound
      rw [spectralMajorant]
      simpa [positiveSpectralMajorant, centerMajorant, middleMajorant,
        tailMajorant, hcenterNot, hmiddleNot, htailMem, halgebra, mul_comm] using hbound
theorem fourier_logTrapezoid_integrable (eps L : Real)
    (heps : 0 < eps) (hL : 0 <= L) : Integrable (𝓕 (logTrapezoid eps L)) := by
  have hA : 0 < L + 3 * eps := by linarith
  have hmajorant := spectralMajorant_integrable (L + 3 * eps) eps hA heps
  have hcontinuous : Continuous (𝓕 (logTrapezoid eps L)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (innerSL Real).continuous₂ (logTrapezoid_integrable eps L)
  exact hmajorant.mono' hcontinuous.aestronglyMeasurable
    (ae_of_all volume fun xi =>
      norm_fourier_logTrapezoid_le_spectralMajorant eps L xi heps hL)
theorem integral_norm_fourier_logTrapezoid_le (eps L : Real)
    (heps : 0 < eps) (hL : 0 <= L) :
    ∫ xi : Real, ‖𝓕 (logTrapezoid eps L) xi‖ <=
      4 + 2 * Real.log ((L + 3 * eps) / eps) := by
  have hA : 0 < L + 3 * eps := by linarith
  have hepsA : eps <= L + 3 * eps := by linarith
  have hfourier := fourier_logTrapezoid_integrable eps L heps hL
  have hmajorant := spectralMajorant_integrable (L + 3 * eps) eps hA heps
  calc
    ∫ xi : Real, ‖𝓕 (logTrapezoid eps L) xi‖ <=
        ∫ xi : Real, spectralMajorant (L + 3 * eps) eps xi := by
      exact integral_mono hfourier.norm hmajorant fun xi =>
        norm_fourier_logTrapezoid_le_spectralMajorant eps L xi heps hL
    _ = 4 + 2 * Real.log ((L + 3 * eps) / eps) :=
      integral_spectralMajorant (L + 3 * eps) eps hA heps hepsA
theorem logTrapezoid_eq_one (eps L x : Real) (heps : 0 < eps)
    (hxlow : -eps <= x) (hxhigh : x <= L + eps) :
    logTrapezoid eps L x = 1 := by
  have hintegrand :
      (fun t : Real => intervalBox 0 eps t *
        intervalBox (-2 * eps) (L + eps) (x - t)) = intervalBox 0 eps := by
    funext t
    by_cases ht : t ∈ Icc (0 : Real) eps
    · have hxtlow : -2 * eps <= x - t := by
        rcases ht with ⟨htlow, hthigh⟩
        linarith
      have hxthigh : x - t <= L + eps := by
        rcases ht with ⟨htlow, hthigh⟩
        linarith
      have hxt : x - t ∈ Icc (-2 * eps) (L + eps) := ⟨hxtlow, hxthigh⟩
      simp only [intervalBox, Set.indicator_apply, if_pos ht, if_pos hxt, one_mul]
    · simp only [intervalBox, Set.indicator_apply, if_neg ht, zero_mul]
  change (eps : Complex)⁻¹ *
      (∫ t : Real, intervalBox 0 eps t *
        intervalBox (-2 * eps) (L + eps) (x - t)) = 1
  rw [hintegrand, integral_intervalBox 0 eps heps.le]
  norm_num [heps.ne']
theorem logTrapezoid_eq_zero_of_gt (eps L x : Real)
    (hx : L + 2 * eps < x) : logTrapezoid eps L x = 0 := by
  have hintegrand :
      (fun t : Real => intervalBox 0 eps t *
        intervalBox (-2 * eps) (L + eps) (x - t)) = 0 := by
    funext t
    by_cases ht : t ∈ Icc (0 : Real) eps
    · have hxt : L + eps < x - t := by
        rcases ht with ⟨htlow, hthigh⟩
        linarith
      have hnot : x - t ∉ Icc (-2 * eps) (L + eps) := fun hmem =>
        (not_le_of_gt hxt) hmem.2
      simp only [intervalBox, Set.indicator_apply, if_pos ht, if_neg hnot, mul_zero]
      rfl
    · simp only [intervalBox, Set.indicator_apply, if_neg ht, zero_mul]
      rfl
  change (eps : Complex)⁻¹ *
      (∫ t : Real, intervalBox 0 eps t *
        intervalBox (-2 * eps) (L + eps) (x - t)) = 0
  rw [hintegrand]
  simp
theorem continuousAt_logTrapezoid_of_mem_plateau (eps L x : Real)
    (heps : 0 < eps) (hxlow : -eps < x) (hxhigh : x < L + eps) :
    ContinuousAt (logTrapezoid eps L) x := by
  apply (continuousAt_const : ContinuousAt (fun _ : Real => (1 : Complex)) x).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds ⟨hxlow, hxhigh⟩] with y hy
  exact logTrapezoid_eq_one eps L y heps hy.1.le hy.2.le
theorem continuousAt_logTrapezoid_of_gt (eps L x : Real)
    (hx : L + 2 * eps < x) : ContinuousAt (logTrapezoid eps L) x := by
  apply (continuousAt_const : ContinuousAt (fun _ : Real => (0 : Complex)) x).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
  exact logTrapezoid_eq_zero_of_gt eps L y hy
theorem logTrapezoid_fourier_inversion (eps L x : Real)
    (heps : 0 < eps) (hL : 0 <= L)
    (hcontinuous : ContinuousAt (logTrapezoid eps L) x) :
    logTrapezoid eps L x =
      ∫ xi : Real, Real.fourierChar (xi * x) • 𝓕 (logTrapezoid eps L) xi := by
  have hinversion := (logTrapezoid_integrable eps L).fourierInv_fourier_eq
    (fourier_logTrapezoid_integrable eps L heps hL) hcontinuous
  rw [Real.fourierInv_eq] at hinversion
  simpa [mul_comm] using hinversion.symm
end BombieriVinogradov.LogCutoff
end
end

section
noncomputable section
open Complex MeasureTheory Real Set
open scoped FourierTransform
namespace BombieriVinogradov.LogCutoff
def integerLogGap (Y : Nat) : Real :=
  Real.log ((Y + 1 : Nat) : Real) - Real.log (Y : Real)
def integerLogEpsilon (Y : Nat) : Real :=
  integerLogGap Y / 4
def integerLogCutoff (Y : Nat) : Real -> Complex :=
  logTrapezoid (integerLogEpsilon Y) (Real.log (Y : Real))
theorem integerLogGap_pos (Y : Nat) (hY : 1 <= Y) : 0 < integerLogGap Y := by
  have hYpos : 0 < (Y : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hY)
  have hsuccpos : 0 < ((Y + 1 : Nat) : Real) := by positivity
  have hlt : (Y : Real) < ((Y + 1 : Nat) : Real) := by exact_mod_cast Nat.lt_succ_self Y
  exact sub_pos.mpr (Real.strictMonoOn_log hYpos hsuccpos hlt)
theorem integerLogEpsilon_pos (Y : Nat) (hY : 1 <= Y) :
    0 < integerLogEpsilon Y := by
  exact div_pos (integerLogGap_pos Y hY) (by norm_num)
theorem log_nat_nonneg (Y : Nat) (hY : 1 <= Y) : 0 <= Real.log (Y : Real) := by
  exact Real.log_nonneg (by exact_mod_cast hY)
theorem integerLogCutoff_eq_one (Y k : Nat) (hY : 1 <= Y)
    (hk : 1 <= k) (hkY : k <= Y) :
    integerLogCutoff Y (Real.log (k : Real)) = 1 := by
  have heps := integerLogEpsilon_pos Y hY
  have hkpos : 0 < (k : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hYpos : 0 < (Y : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hY)
  have hlogk : 0 <= Real.log (k : Real) := Real.log_nonneg (by exact_mod_cast hk)
  have hlogle : Real.log (k : Real) <= Real.log (Y : Real) :=
    Real.strictMonoOn_log.monotoneOn hkpos hYpos (by exact_mod_cast hkY)
  apply logTrapezoid_eq_one
  · exact heps
  · linarith
  · linarith
theorem integerLogCutoff_eq_zero (Y k : Nat) (hY : 1 <= Y)
    (hk : Y + 1 <= k) :
    integerLogCutoff Y (Real.log (k : Real)) = 0 := by
  have heps := integerLogEpsilon_pos Y hY
  have hsuccpos : 0 < ((Y + 1 : Nat) : Real) := by positivity
  have hkpos : 0 < (k : Real) := by
    exact_mod_cast (lt_of_lt_of_le (Nat.zero_lt_succ Y) hk)
  have hlogle : Real.log ((Y + 1 : Nat) : Real) <= Real.log (k : Real) :=
    Real.strictMonoOn_log.monotoneOn hsuccpos hkpos (by exact_mod_cast hk)
  apply logTrapezoid_eq_zero_of_gt
  calc
    Real.log (Y : Real) + 2 * integerLogEpsilon Y <
        Real.log (Y : Real) + 4 * integerLogEpsilon Y := by linarith
    _ = Real.log ((Y + 1 : Nat) : Real) := by
      rw [integerLogEpsilon, integerLogGap]
      ring
    _ <= Real.log (k : Real) := hlogle
theorem continuousAt_integerLogCutoff (Y k : Nat) (hY : 1 <= Y)
    (hk : 1 <= k) :
    ContinuousAt (integerLogCutoff Y) (Real.log (k : Real)) := by
  have heps := integerLogEpsilon_pos Y hY
  have hkpos : 0 < (k : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hlogk : 0 <= Real.log (k : Real) := Real.log_nonneg (by exact_mod_cast hk)
  by_cases hkY : k <= Y
  · have hYpos : 0 < (Y : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hY)
    have hlogle : Real.log (k : Real) <= Real.log (Y : Real) :=
      Real.strictMonoOn_log.monotoneOn hkpos hYpos (by exact_mod_cast hkY)
    apply continuousAt_logTrapezoid_of_mem_plateau
    · exact heps
    · linarith
    · linarith
  · have hsucc : Y + 1 <= k := Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge hkY)
    have hsuccpos : 0 < ((Y + 1 : Nat) : Real) := by positivity
    have hlogle : Real.log ((Y + 1 : Nat) : Real) <= Real.log (k : Real) :=
      Real.strictMonoOn_log.monotoneOn hsuccpos hkpos (by exact_mod_cast hsucc)
    apply continuousAt_logTrapezoid_of_gt
    calc
      Real.log (Y : Real) + 2 * integerLogEpsilon Y <
          Real.log (Y : Real) + 4 * integerLogEpsilon Y := by linarith
      _ = Real.log ((Y + 1 : Nat) : Real) := by
        rw [integerLogEpsilon, integerLogGap]
        ring
      _ <= Real.log (k : Real) := hlogle
theorem integerLogCutoff_indicator (Y k : Nat) (hY : 1 <= Y)
    (hk : 1 <= k) :
    integerLogCutoff Y (Real.log (k : Real)) = if k <= Y then 1 else 0 := by
  split_ifs with hkY
  · exact integerLogCutoff_eq_one Y k hY hk hkY
  · exact integerLogCutoff_eq_zero Y k hY
      (Nat.add_one_le_iff.mpr (Nat.lt_of_not_ge hkY))
theorem integerLogCutoff_fourier_inversion (Y k : Nat) (hY : 1 <= Y)
    (hk : 1 <= k) :
    integerLogCutoff Y (Real.log (k : Real)) =
      ∫ xi : Real, Real.fourierChar (xi * Real.log (k : Real)) •
        𝓕 (integerLogCutoff Y) xi := by
  exact logTrapezoid_fourier_inversion
    (integerLogEpsilon Y) (Real.log (Y : Real)) (Real.log (k : Real))
    (integerLogEpsilon_pos Y hY) (log_nat_nonneg Y hY)
    (continuousAt_integerLogCutoff Y k hY hk)
theorem integerIndicator_fourier_representation (Y k : Nat) (hY : 1 <= Y)
    (hk : 1 <= k) :
    (if k <= Y then 1 else 0 : Complex) =
      ∫ xi : Real, Real.fourierChar (xi * Real.log (k : Real)) •
        𝓕 (integerLogCutoff Y) xi := by
  rw [← integerLogCutoff_fourier_inversion Y k hY hk]
  exact (integerLogCutoff_indicator Y k hY hk).symm
theorem fourier_integerLogCutoff_integrable (Y : Nat) (hY : 1 <= Y) :
    Integrable (𝓕 (integerLogCutoff Y)) := by
  exact fourier_logTrapezoid_integrable
    (integerLogEpsilon Y) (Real.log (Y : Real))
    (integerLogEpsilon_pos Y hY) (log_nat_nonneg Y hY)
theorem integral_norm_fourier_integerLogCutoff_le (Y : Nat) (hY : 1 <= Y) :
    ∫ xi : Real, ‖𝓕 (integerLogCutoff Y) xi‖ <=
      4 + 2 * Real.log ((Real.log (Y : Real) + 3 * integerLogEpsilon Y) /
        integerLogEpsilon Y) := by
  exact integral_norm_fourier_logTrapezoid_le
    (integerLogEpsilon Y) (Real.log (Y : Real))
    (integerLogEpsilon_pos Y hY) (log_nat_nonneg Y hY)
theorem one_div_succ_le_integerLogGap (Y : Nat) (hY : 1 <= Y) :
    1 / ((Y : Real) + 1) <= integerLogGap Y := by
  have hYpos : 0 < (Y : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hY)
  have hgap : integerLogGap Y = Real.log (1 + ((Y : Real))⁻¹) := by
    rw [integerLogGap, ← Real.log_div (by positivity) hYpos.ne']
    congr 1
    push_cast
    field_simp [hYpos.ne']
  rw [hgap]
  apply (show 1 / ((Y : Real) + 1) <=
    2 * ((Y : Real))⁻¹ / (((Y : Real))⁻¹ + 2) by
      field_simp [hYpos.ne']
      nlinarith).trans
  exact Real.le_log_one_add_of_nonneg (inv_nonneg.mpr hYpos.le)
theorem integerLogCutoff_ratio_le (Y : Nat) (hY : 1 <= Y) :
    (Real.log (Y : Real) + 3 * integerLogEpsilon Y) / integerLogEpsilon Y <=
      7 * ((Y : Real) + 1) ^ 2 := by
  let y : Real := Y
  let gap : Real := integerLogGap Y
  have hy : 1 <= y := by
    dsimp [y]
    exact_mod_cast hY
  have hypos : 0 < y := zero_lt_one.trans_le hy
  have hgap : 0 < gap := by exact integerLogGap_pos Y hY
  have hgapLower : 1 / (y + 1) <= gap := by
    simpa [y, gap] using one_div_succ_le_integerLogGap Y hY
  have hgapInv : gap⁻¹ <= y + 1 := by
    have h := (inv_le_inv₀ hgap (one_div_pos.mpr (by linarith))).2 hgapLower
    simpa [one_div] using h
  have hlogle : Real.log y <= y :=
    (Real.log_le_sub_one_of_pos hypos).trans (by linarith)
  have hproduct : Real.log y * gap⁻¹ <= y * (y + 1) := by
    exact mul_le_mul hlogle hgapInv (inv_nonneg.mpr hgap.le) hypos.le
  have hratio :
      (Real.log y + 3 * (gap / 4)) / (gap / 4) =
        4 * (Real.log y * gap⁻¹) + 3 := by
    field_simp [hgap.ne']
  change (Real.log y + 3 * (gap / 4)) / (gap / 4) <= 7 * (y + 1) ^ 2
  rw [hratio]
  nlinarith [sq_nonneg (y + 1)]
theorem log_integerLogCutoff_ratio_le (Y : Nat) (hY : 1 <= Y) :
    Real.log ((Real.log (Y : Real) + 3 * integerLogEpsilon Y) /
      integerLogEpsilon Y) <= 6 + 2 * Real.log ((Y : Real) + 1) := by
  have heps := integerLogEpsilon_pos Y hY
  have hL := log_nat_nonneg Y hY
  have hratioPos : 0 <
      (Real.log (Y : Real) + 3 * integerLogEpsilon Y) /
        integerLogEpsilon Y := div_pos (by linarith) heps
  have htargetPos : 0 < 7 * ((Y : Real) + 1) ^ 2 := by positivity
  have hlog := Real.strictMonoOn_log.monotoneOn hratioPos htargetPos
    (integerLogCutoff_ratio_le Y hY)
  have hlogSeven : Real.log (7 : Real) <= 6 := by
    have h := Real.log_le_sub_one_of_pos (show (0 : Real) < 7 by norm_num)
    norm_num at h ⊢
    exact h
  calc
    Real.log ((Real.log (Y : Real) + 3 * integerLogEpsilon Y) /
        integerLogEpsilon Y) <= Real.log (7 * ((Y : Real) + 1) ^ 2) := hlog
    _ = Real.log 7 + 2 * Real.log ((Y : Real) + 1) := by
      rw [Real.log_mul (by norm_num : Ne (7 : Real) 0)
        (by positivity : Ne (((Y : Real) + 1) ^ 2) 0)]
      rw [Real.log_pow]
      norm_num
    _ <= 6 + 2 * Real.log ((Y : Real) + 1) := by linarith
theorem integral_norm_fourier_integerLogCutoff_le_log (Y : Nat) (hY : 1 <= Y) :
    ∫ xi : Real, ‖𝓕 (integerLogCutoff Y) xi‖ <=
      16 + 4 * Real.log ((Y : Real) + 1) := by
  exact (integral_norm_fourier_integerLogCutoff_le Y hY).trans
    (by linarith [log_integerLogCutoff_ratio_le Y hY])
end BombieriVinogradov.LogCutoff
end
end

section
noncomputable section
open Complex Finset MeasureTheory Real Set
open scoped BigOperators FourierTransform
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
open BombieriVinogradov.LogCutoff
theorem positiveCharacterSum_eq_sum_nat (a : Nat -> Complex) (M q : Nat)
    (chi : DirichletCharacter Complex q) :
    positiveCharacterSum a M q chi =
      ∑ m ∈ Icc 1 M, a m * chi (m : ZMod q) := by
  unfold positiveCharacterSum intervalCharacterSum
  apply Finset.sum_bij (fun n _ => n.toNat)
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hnpos : (0 : Int) < n := by omega
    have hnle : n <= (M : Int) := by omega
    simp only [Finset.mem_Icc]
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr fun hzero =>
        (not_le_of_gt hnpos) (Int.toNat_eq_zero.mp hzero)
    · have hcast : (n.toNat : Int) <= (M : Int) := by
        simpa [Int.toNat_of_nonneg hnpos.le] using hnle
      exact_mod_cast hcast
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_Ioc] at hn₁ hn₂
    have hn₁pos : (0 : Int) < n₁ := by omega
    have hn₂pos : (0 : Int) < n₂ := by omega
    calc
      n₁ = (n₁.toNat : Int) := (Int.toNat_of_nonneg hn₁pos.le).symm
      _ = (n₂.toNat : Int) := by exact_mod_cast heq
      _ = n₂ := Int.toNat_of_nonneg hn₂pos.le
  · intro m hm
    refine ⟨(m : Int), ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      constructor
      · exact_mod_cast (show 0 < m from (Finset.mem_Icc.mp hm).1)
      · simpa using (show (m : Int) <= (M : Int) by
          exact_mod_cast (Finset.mem_Icc.mp hm).2)
    · simp
  · intro n hn
    have hnpos : (0 : Int) <= n := by
      have := Finset.mem_Ioc.mp hn
      omega
    rw [show n = (n.toNat : Int) by exact (Int.toNat_of_nonneg hnpos).symm]
    simp [positiveIntervalCoefficients]
theorem positiveCoefficientMass_eq_coefficientMass (a : Nat -> Complex) (M : Nat) :
    positiveCoefficientMass a M = coefficientMass a M := by
  unfold positiveCoefficientMass coefficientMass
  apply Finset.sum_bij (fun n _ => n.toNat)
  · intro n hn
    simp only [Finset.mem_Ioc] at hn
    have hnpos : (0 : Int) < n := by omega
    have hnle : n <= (M : Int) := by omega
    simp only [Finset.mem_Icc]
    constructor
    · exact Nat.one_le_iff_ne_zero.mpr fun hzero =>
        (not_le_of_gt hnpos) (Int.toNat_eq_zero.mp hzero)
    · have hcast : (n.toNat : Int) <= (M : Int) := by
        simpa [Int.toNat_of_nonneg hnpos.le] using hnle
      exact_mod_cast hcast
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_Ioc] at hn₁ hn₂
    have hn₁pos : (0 : Int) < n₁ := by omega
    have hn₂pos : (0 : Int) < n₂ := by omega
    calc
      n₁ = (n₁.toNat : Int) := (Int.toNat_of_nonneg hn₁pos.le).symm
      _ = (n₂.toNat : Int) := by exact_mod_cast heq
      _ = n₂ := Int.toNat_of_nonneg hn₂pos.le
  · intro m hm
    refine ⟨(m : Int), ?_, ?_⟩
    · simp only [Finset.mem_Ioc]
      constructor
      · exact_mod_cast (show 0 < m from (Finset.mem_Icc.mp hm).1)
      · simpa using (show (m : Int) <= (M : Int) by
          exact_mod_cast (Finset.mem_Icc.mp hm).2)
    · simp
  · intro n hn
    simp [positiveIntervalCoefficients]
def fourierTwist (xi : Real) (a : Nat -> Complex) (m : Nat) : Complex :=
  Real.fourierChar (xi * Real.log (m : Real)) • a m
theorem norm_fourierTwist (xi : Real) (a : Nat -> Complex) (m : Nat) :
    ‖fourierTwist xi a m‖ = ‖a m‖ := by
  simp [fourierTwist, Circle.norm_smul]
theorem coefficientMass_fourierTwist (xi : Real) (a : Nat -> Complex) (M : Nat) :
    coefficientMass (fourierTwist xi a) M = coefficientMass a M := by
  simp [coefficientMass, norm_fourierTwist]
theorem positiveCoefficientMass_fourierTwist
    (xi : Real) (a : Nat -> Complex) (M : Nat) :
    positiveCoefficientMass (fourierTwist xi a) M = positiveCoefficientMass a M := by
  rw [positiveCoefficientMass_eq_coefficientMass,
    coefficientMass_fourierTwist,
    positiveCoefficientMass_eq_coefficientMass]
theorem fourierChar_log_mul (xi : Real) (m n : Nat)
    (hm : 1 <= m) (hn : 1 <= n) :
    Real.fourierChar (xi * Real.log ((m * n : Nat) : Real)) =
      Real.fourierChar (xi * Real.log (m : Real)) *
        Real.fourierChar (xi * Real.log (n : Real)) := by
  have hm0 : Ne (m : Real) 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hm))
  have hn0 : Ne (n : Real) 0 := by exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hn))
  push_cast
  rw [Real.log_mul hm0 hn0]
  rw [mul_add, AddChar.map_add_eq_mul]
theorem bilinearCharacterProduct_fourierTwist (xi : Real)
    (a b : Nat -> Complex) (M N q : Nat)
    (chi : DirichletCharacter Complex q) :
    bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b) M N q chi =
      ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
        Real.fourierChar (xi * Real.log ((m * n : Nat) : Real)) •
          (a m * b n * chi ((m * n : Nat) : ZMod q)) := by
  rw [bilinearCharacterProduct, positiveCharacterSum_eq_sum_nat,
    positiveCharacterSum_eq_sum_nat]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have hm1 : 1 <= m := (Finset.mem_Icc.mp hm).1
  have hn1 : 1 <= n := (Finset.mem_Icc.mp hn).1
  have hchi : chi ((m * n : Nat) : ZMod q) =
      chi (m : ZMod q) * chi (n : ZMod q) := by
    rw [show ((m * n : Nat) : ZMod q) = (m : ZMod q) * (n : ZMod q) by
      push_cast
      rfl]
    exact map_mul chi _ _
  rw [fourierChar_log_mul xi m n hm1 hn1]
  simp only [fourierTwist, Circle.smul_def, hchi, Circle.coe_mul]
  ring
theorem fourierCutoffTerm_integrable (Y k : Nat) (hY : 1 <= Y)
    (c : Complex) :
    Integrable (fun xi : Real =>
      (Real.fourierChar (xi * Real.log (k : Real)) •
        𝓕 (integerLogCutoff Y) xi) * c) := by
  have hcontinuous : Continuous (fun xi : Real =>
      Real.fourierChar (xi * Real.log (k : Real))) := by
    fun_prop
  have hfourier := fourier_integerLogCutoff_integrable Y hY
  have hproduct : Integrable (fun xi : Real =>
      Real.fourierChar (xi * Real.log (k : Real)) •
        𝓕 (integerLogCutoff Y) xi) := by
    simp_rw [← integrable_norm_iff
      (hcontinuous.aestronglyMeasurable.fun_smul hfourier.1),
      Circle.norm_smul]
    exact hfourier.norm
  exact hproduct.mul_const c
theorem restrictedBilinearCharacterSum_fourier (a b : Nat -> Complex)
    (M N Y q : Nat) (chi : DirichletCharacter Complex q) (hY : 1 <= Y) :
    restrictedBilinearCharacterSum a b M N Y q chi =
      ∫ xi : Real, 𝓕 (integerLogCutoff Y) xi *
        bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
          M N q chi := by
  rw [restrictedBilinearCharacterSum]
  calc
    (∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
        if m * n <= Y then a m * b n * chi ((m * n : Nat) : ZMod q) else 0) =
        ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
          (if m * n <= Y then 1 else 0 : Complex) *
            (a m * b n * chi ((m * n : Nat) : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      split_ifs <;> simp
    _ = ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
          (∫ xi : Real,
            Real.fourierChar (xi * Real.log ((m * n : Nat) : Real)) •
              𝓕 (integerLogCutoff Y) xi) *
            (a m * b n * chi ((m * n : Nat) : ZMod q)) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro n hn
      rw [integerIndicator_fourier_representation Y (m * n) hY]
      exact Nat.mul_pos (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hm).1)
        (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1)
    _ = ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
          ∫ xi : Real,
            (Real.fourierChar (xi * Real.log ((m * n : Nat) : Real)) •
              𝓕 (integerLogCutoff Y) xi) *
              (a m * b n * chi ((m * n : Nat) : ZMod q)) := by
      simp_rw [integral_mul_const]
    _ = ∫ xi : Real, ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
          (Real.fourierChar (xi * Real.log ((m * n : Nat) : Real)) •
            𝓕 (integerLogCutoff Y) xi) *
            (a m * b n * chi ((m * n : Nat) : ZMod q)) := by
      rw [integral_finsetSum]
      · congr 1
        funext m
        rw [integral_finsetSum]
        intro n hn
        exact fourierCutoffTerm_integrable Y (m * n) hY _
      · intro m hm
        exact integrable_finsetSum (Icc 1 N) (fun n hn =>
          fourierCutoffTerm_integrable Y (m * n) hY _)
    _ = ∫ xi : Real, 𝓕 (integerLogCutoff Y) xi *
        bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
          M N q chi := by
      apply integral_congr_ae
      filter_upwards with xi
      rw [bilinearCharacterProduct_fourierTwist]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      simp only [Circle.smul_def]
      ring
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset MeasureTheory Real Set
open scoped BigOperators FourierTransform
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LogCutoff
theorem integerLogGap_eq_log_ratio (Y : Nat) (hY : 1 <= Y) :
    integerLogGap Y = Real.log (((Y + 1 : Nat) : Real) / (Y : Real)) := by
  have hY0 : Ne (Y : Real) 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_of_lt hY))
  rw [integerLogGap, Real.log_div (by positivity) hY0]
theorem integerLogEpsilon_antitone {Y X : Nat} (hY : 1 <= Y) (hYX : Y <= X) :
    integerLogEpsilon X <= integerLogEpsilon Y := by
  have hX : 1 <= X := hY.trans hYX
  have hYpos : 0 < (Y : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hY)
  have hXpos : 0 < (X : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hX)
  have hratio : (((X + 1 : Nat) : Real) / (X : Real)) <=
      (((Y + 1 : Nat) : Real) / (Y : Real)) := by
    rw [div_le_div_iff₀ hXpos hYpos]
    push_cast
    nlinarith [show (Y : Real) <= (X : Real) by exact_mod_cast hYX]
  have hratioPos : 0 < (((X + 1 : Nat) : Real) / (X : Real)) := by positivity
  have hlog := Real.log_le_log hratioPos hratio
  rw [← integerLogGap_eq_log_ratio X hX,
    ← integerLogGap_eq_log_ratio Y hY] at hlog
  unfold integerLogEpsilon
  linarith
theorem integerLogAmplitude_monotone {Y X : Nat}
    (hY : 1 <= Y) (hYX : Y <= X) :
    Real.log (Y : Real) + 3 * integerLogEpsilon Y <=
      Real.log (X : Real) + 3 * integerLogEpsilon X := by
  have hX : 1 <= X := hY.trans hYX
  have hYpos : 0 < (Y : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hY)
  have hXpos : 0 < (X : Real) := by exact_mod_cast (Nat.zero_lt_of_lt hX)
  have hlogY : Real.log (Y : Real) <= Real.log (X : Real) :=
    Real.strictMonoOn_log.monotoneOn hYpos hXpos (by exact_mod_cast hYX)
  have hlogSucc : Real.log ((Y + 1 : Nat) : Real) <=
      Real.log ((X + 1 : Nat) : Real) := by
    exact Real.strictMonoOn_log.monotoneOn
      (show 0 < ((Y + 1 : Nat) : Real) by positivity)
      (show 0 < ((X + 1 : Nat) : Real) by positivity)
      (by exact_mod_cast Nat.add_le_add_right hYX 1)
  unfold integerLogEpsilon integerLogGap
  linarith
theorem norm_fourier_integerLogCutoff_le_commonSpectralMajorant
    {Y X : Nat} (hY : 1 <= Y) (hYX : Y <= X) (xi : Real) :
    ‖𝓕 (integerLogCutoff Y) xi‖ <=
      spectralMajorant
        (Real.log (X : Real) + 3 * integerLogEpsilon X)
        (integerLogEpsilon X) xi := by
  let A : Real := Real.log (X : Real) + 3 * integerLogEpsilon X
  let eps : Real := integerLogEpsilon X
  have hX : 1 <= X := hY.trans hYX
  have hepsY := integerLogEpsilon_pos Y hY
  have heps : 0 < eps := by simpa [eps] using integerLogEpsilon_pos X hX
  have hLY := log_nat_nonneg Y hY
  have hA : 0 < A := by
    dsimp [A, eps]
    linarith [integerLogEpsilon_pos X hX, log_nat_nonneg X hX]
  have hepsA : eps <= A := by
    dsimp [A, eps]
    linarith [integerLogEpsilon_pos X hX, log_nat_nonneg X hX]
  have hAmplitude : Real.log (Y : Real) + 3 * integerLogEpsilon Y <= A := by
    simpa [A] using integerLogAmplitude_monotone hY hYX
  have hepsOrder : eps <= integerLogEpsilon Y := by
    simpa [eps] using integerLogEpsilon_antitone hY hYX
  have hinvle : A⁻¹ <= eps⁻¹ := (inv_le_inv₀ hA heps).2 hepsA
  have hpi : 1 <= Real.pi := by nlinarith [Real.one_le_pi_div_two]
  change ‖𝓕 (logTrapezoid (integerLogEpsilon Y)
    (Real.log (Y : Real))) xi‖ <= spectralMajorant A eps xi
  by_cases hcenter : |xi| <= A⁻¹
  · have hcenterMem : |xi| ∈ Icc (0 : Real) A⁻¹ := ⟨abs_nonneg xi, hcenter⟩
    have hmiddleNot : |xi| ∉ Ioc A⁻¹ eps⁻¹ := fun hmem =>
      (not_lt_of_ge hcenter) hmem.1
    have htailNot : |xi| ∉ Ioi eps⁻¹ := fun hmem =>
      (not_lt_of_ge (hcenter.trans hinvle)) hmem
    have hbound := norm_fourier_logTrapezoid_le_length
      (integerLogEpsilon Y) (Real.log (Y : Real)) xi hepsY hLY
    rw [spectralMajorant]
    simpa [positiveSpectralMajorant, centerMajorant, middleMajorant,
      tailMajorant, hcenterMem, hmiddleNot, htailNot] using hbound.trans hAmplitude
  · have hAxi : A⁻¹ < |xi| := lt_of_not_ge hcenter
    by_cases hmiddle : |xi| <= eps⁻¹
    · have hmiddleMem : |xi| ∈ Ioc A⁻¹ eps⁻¹ := ⟨hAxi, hmiddle⟩
      have hcenterNot : |xi| ∉ Icc (0 : Real) A⁻¹ := fun hmem =>
        (not_lt_of_ge hmem.2) hAxi
      have htailNot : |xi| ∉ Ioi eps⁻¹ := fun hmem =>
        (not_lt_of_ge hmiddle) hmem
      have hy : 0 < |xi| := (inv_pos.mpr hA).trans hAxi
      have hxi : Ne xi 0 := abs_pos.mp hy
      have hpiBound : 1 / (Real.pi * |xi|) <= |xi|⁻¹ := by
        have hyMul : |xi| <= Real.pi * |xi| := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hpi hy.le
        simpa only [one_div] using one_div_le_one_div_of_le hy hyMul
      have hbound := (norm_fourier_logTrapezoid_le_inv
        (integerLogEpsilon Y) (Real.log (Y : Real)) xi hepsY hLY hxi).trans hpiBound
      rw [spectralMajorant]
      simpa [positiveSpectralMajorant, centerMajorant, middleMajorant,
        tailMajorant, hcenterNot, hmiddleMem, htailNot] using hbound
    · have htail : eps⁻¹ < |xi| := lt_of_not_ge hmiddle
      have htailMem : |xi| ∈ Ioi eps⁻¹ := htail
      have hcenterNot : |xi| ∉ Icc (0 : Real) A⁻¹ := fun hmem =>
        (not_lt_of_ge hmem.2) hAxi
      have hmiddleNot : |xi| ∉ Ioc A⁻¹ eps⁻¹ := fun hmem =>
        (not_lt_of_ge hmem.2) htail
      have hy : 0 < |xi| := (inv_pos.mpr heps).trans htail
      have hxi : Ne xi 0 := abs_pos.mp hy
      have hpiSq : 1 <= Real.pi ^ 2 := by nlinarith
      have hden : eps * |xi| ^ 2 <=
          integerLogEpsilon Y * Real.pi ^ 2 * |xi| ^ 2 := by
        calc
          eps * |xi| ^ 2 <= integerLogEpsilon Y * |xi| ^ 2 :=
            mul_le_mul_of_nonneg_right hepsOrder (sq_nonneg _)
          _ = (integerLogEpsilon Y * |xi| ^ 2) * 1 := by ring
          _ <= (integerLogEpsilon Y * |xi| ^ 2) * Real.pi ^ 2 :=
            mul_le_mul_of_nonneg_left hpiSq
              (mul_nonneg hepsY.le (sq_nonneg _))
          _ = integerLogEpsilon Y * Real.pi ^ 2 * |xi| ^ 2 := by ring
      have hdenPos : 0 < eps * |xi| ^ 2 := mul_pos heps (sq_pos_of_pos hy)
      have hpiBound :
          1 / (integerLogEpsilon Y * Real.pi ^ 2 * |xi| ^ 2) <=
            1 / (eps * |xi| ^ 2) := by
        exact one_div_le_one_div_of_le hdenPos hden
      have hrpow : |xi| ^ (-2 : Real) = (|xi| ^ 2)⁻¹ := by
        calc
          |xi| ^ (-2 : Real) = |xi| ^ (-2 : Int) :=
            Real.rpow_neg_natCast |xi| 2
          _ = (|xi| ^ 2)⁻¹ := by norm_num [zpow_neg]
      have halgebra : 1 / (eps * |xi| ^ 2) =
          eps⁻¹ * |xi| ^ (-2 : Real) := by
        rw [hrpow]
        field_simp [heps.ne', abs_ne_zero.mpr hxi]
      have hbound := (norm_fourier_logTrapezoid_le_inv_sq
        (integerLogEpsilon Y) (Real.log (Y : Real)) xi hepsY hLY hxi).trans hpiBound
      rw [spectralMajorant]
      simpa [positiveSpectralMajorant, centerMajorant, middleMajorant,
        tailMajorant, hcenterNot, hmiddleNot, htailMem, halgebra, mul_comm] using hbound
theorem spectralMajorant_nonneg (A eps xi : Real)
    (hA : 0 <= A) (heps : 0 <= eps) :
    0 <= spectralMajorant A eps xi := by
  rw [spectralMajorant, positiveSpectralMajorant, centerMajorant,
    middleMajorant, tailMajorant]
  simp only [Pi.add_apply, Set.indicator_apply]
  split_ifs <;> positivity
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset MeasureTheory Real Set
open scoped BigOperators FourierTransform
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
open BombieriVinogradov.LogCutoff
theorem norm_positiveCharacterSum_fourierTwist_le (xi : Real)
    (a : Nat -> Complex) (M q : Nat) (chi : DirichletCharacter Complex q) :
    ‖positiveCharacterSum (fourierTwist xi a) M q chi‖ <=
      ∑ m ∈ Icc 1 M, ‖a m‖ := by
  rw [positiveCharacterSum_eq_sum_nat]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro m hm
  rw [norm_mul, norm_fourierTwist]
  exact mul_le_of_le_one_right (norm_nonneg _) (chi.norm_le_one _)
theorem norm_bilinearCharacterProduct_fourierTwist_le (xi : Real)
    (a b : Nat -> Complex) (M N q : Nat)
    (chi : DirichletCharacter Complex q) :
    ‖bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
      M N q chi‖ <=
      (∑ m ∈ Icc 1 M, ‖a m‖) * (∑ n ∈ Icc 1 N, ‖b n‖) := by
  rw [bilinearCharacterProduct, norm_mul]
  exact mul_le_mul
    (norm_positiveCharacterSum_fourierTwist_le xi a M q chi)
    (norm_positiveCharacterSum_fourierTwist_le xi b N q chi)
    (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
theorem continuous_bilinearCharacterProduct_fourierTwist
    (a b : Nat -> Complex) (M N q : Nat)
    (chi : DirichletCharacter Complex q) :
    Continuous (fun xi : Real =>
      bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
        M N q chi) := by
  rw [show (fun xi : Real =>
      bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
        M N q chi) = fun xi : Real =>
      ∑ m ∈ Icc 1 M, ∑ n ∈ Icc 1 N,
        Real.fourierChar (xi * Real.log ((m * n : Nat) : Real)) •
          (a m * b n * chi ((m * n : Nat) : ZMod q)) by
    funext xi
    exact bilinearCharacterProduct_fourierTwist xi a b M N q chi]
  fun_prop
theorem commonSpectralBilinearIntegrable (X : Nat) (hX : 1 <= X)
    (a b : Nat -> Complex) (M N q : Nat)
    (chi : DirichletCharacter Complex q) :
    Integrable (fun xi : Real =>
      spectralMajorant
          (Real.log (X : Real) + 3 * integerLogEpsilon X)
          (integerLogEpsilon X) xi *
        ‖bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
          M N q chi‖) := by
  have heps := integerLogEpsilon_pos X hX
  have hA : 0 < Real.log (X : Real) + 3 * integerLogEpsilon X := by
    linarith [log_nat_nonneg X hX]
  have hmajorant := spectralMajorant_integrable
    (Real.log (X : Real) + 3 * integerLogEpsilon X)
    (integerLogEpsilon X) hA heps
  have hmeas : AEStronglyMeasurable (fun xi : Real =>
      ‖bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
        M N q chi‖) :=
    (continuous_bilinearCharacterProduct_fourierTwist a b M N q chi).norm
      |>.aestronglyMeasurable
  exact hmajorant.mul_bdd hmeas (Filter.Eventually.of_forall fun xi =>
    by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        norm_bilinearCharacterProduct_fourierTwist_le xi a b M N q chi)
theorem fourierBilinearIntegrable (Y : Nat) (hY : 1 <= Y)
    (a b : Nat -> Complex) (M N q : Nat)
    (chi : DirichletCharacter Complex q) :
    Integrable (fun xi : Real =>
      𝓕 (integerLogCutoff Y) xi *
        bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
          M N q chi) := by
  have hfourier := fourier_integerLogCutoff_integrable Y hY
  have hmeas : AEStronglyMeasurable (fun xi : Real =>
      bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
        M N q chi) :=
    (continuous_bilinearCharacterProduct_fourierTwist a b M N q chi)
      |>.aestronglyMeasurable
  exact hfourier.mul_bdd hmeas (Filter.Eventually.of_forall fun xi =>
    norm_bilinearCharacterProduct_fourierTwist_le xi a b M N q chi)
theorem maximalBilinearNorm_le_commonIntegral
    (X M N : Nat) (a b : Nat -> Complex) (q : Nat)
    (chi : DirichletCharacter Complex q) (hX : 2 <= X) :
    maximalBilinearNorm a b M N X chi <=
      ∫ xi : Real,
        spectralMajorant
            (Real.log (X : Real) + 3 * integerLogEpsilon X)
            (integerLogEpsilon X) xi *
          ‖bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
            M N q chi‖ := by
  have hX1 : 1 <= X := le_trans (by norm_num) hX
  have hepsX := integerLogEpsilon_pos X hX1
  have hAX : 0 <= Real.log (X : Real) + 3 * integerLogEpsilon X := by
    have := log_nat_nonneg X hX1
    positivity
  unfold maximalBilinearNorm
  apply Finset.sup'_le (by simp) _
  intro Y hYrange
  have hYX : Y <= X := Nat.le_of_lt_succ (Finset.mem_range.mp hYrange)
  by_cases hYzero : Y = 0
  · subst Y
    have hrestricted : restrictedBilinearCharacterSum a b M N 0 q chi = 0 := by
      rw [restrictedBilinearCharacterSum]
      apply Finset.sum_eq_zero
      intro m hm
      apply Finset.sum_eq_zero
      intro n hn
      have hmpos : 0 < m := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hm).1
      have hnpos : 0 < n := Nat.zero_lt_of_lt (Finset.mem_Icc.mp hn).1
      simp [Nat.not_le_of_lt (Nat.mul_pos hmpos hnpos)]
    rw [hrestricted, norm_zero]
    apply integral_nonneg
    intro xi
    exact mul_nonneg (spectralMajorant_nonneg _ _ _ hAX hepsX.le) (norm_nonneg _)
  · have hY1 : 1 <= Y := Nat.one_le_iff_ne_zero.mpr hYzero
    rw [restrictedBilinearCharacterSum_fourier a b M N Y q chi hY1]
    apply (norm_integral_le_integral_norm _).trans
    apply integral_mono
      (fourierBilinearIntegrable Y hY1 a b M N q chi).norm
      (commonSpectralBilinearIntegrable X hX1 a b M N q chi)
    intro xi
    simpa only [norm_mul] using
      mul_le_mul_of_nonneg_right
        (norm_fourier_integerLogCutoff_le_commonSpectralMajorant hY1 hYX xi)
        (norm_nonneg (bilinearCharacterProduct
          (fourierTwist xi a) (fourierTwist xi b) M N q chi))
def twistedBilinearMean (xi : Real) (a b : Nat -> Complex)
    (M N Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q,
      ‖bilinearCharacterProduct (fourierTwist xi a) (fourierTwist xi b)
        M N q chi‖
theorem commonSpectralTwistedMeanIntegrable (X M N Q : Nat)
    (a b : Nat -> Complex) (hX : 1 <= X) :
    Integrable (fun xi : Real =>
      spectralMajorant
          (Real.log (X : Real) + 3 * integerLogEpsilon X)
          (integerLogEpsilon X) xi *
        twistedBilinearMean xi a b M N Q) := by
  unfold twistedBilinearMean
  simpa only [Finset.mul_sum] using
    integrable_finsetSum (Icc 1 Q) (fun q hq => by
      exact integrable_finsetSum (primitiveCharacters q) (fun chi hchi => by
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          (commonSpectralBilinearIntegrable X hX a b M N q chi).const_mul
            ((q : Real) / (q.totient : Real))))
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset MeasureTheory Real Set
open scoped BigOperators FourierTransform
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
open BombieriVinogradov.LogCutoff
theorem weightedMaximalBilinear_le_commonIntegral
    (X M N Q : Nat) (a b : Nat -> Complex) (hX : 2 <= X) :
    ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          maximalBilinearNorm a b M N X chi <=
      ∫ xi : Real,
        spectralMajorant
            (Real.log (X : Real) + 3 * integerLogEpsilon X)
            (integerLogEpsilon X) xi *
          twistedBilinearMean xi a b M N Q := by
  calc
    (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          maximalBilinearNorm a b M N X chi) <=
        ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q,
            ∫ xi : Real,
              spectralMajorant
                  (Real.log (X : Real) + 3 * integerLogEpsilon X)
                  (integerLogEpsilon X) xi *
                ‖bilinearCharacterProduct
                  (fourierTwist xi a) (fourierTwist xi b) M N q chi‖ := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro chi hchi
        exact maximalBilinearNorm_le_commonIntegral X M N a b q chi hX
      · positivity
    _ = ∫ xi : Real,
        spectralMajorant
            (Real.log (X : Real) + 3 * integerLogEpsilon X)
            (integerLogEpsilon X) xi *
          twistedBilinearMean xi a b M N Q := by
      unfold twistedBilinearMean
      symm
      calc
        (∫ xi : Real,
            spectralMajorant
                (Real.log (X : Real) + 3 * integerLogEpsilon X)
                (integerLogEpsilon X) xi *
              ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
                ∑ chi ∈ primitiveCharacters q,
                  ‖bilinearCharacterProduct
                    (fourierTwist xi a) (fourierTwist xi b) M N q chi‖) =
            ∫ xi : Real,
              ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
                ∑ chi ∈ primitiveCharacters q,
                  spectralMajorant
                      (Real.log (X : Real) + 3 * integerLogEpsilon X)
                      (integerLogEpsilon X) xi *
                    ‖bilinearCharacterProduct
                      (fourierTwist xi a) (fourierTwist xi b) M N q chi‖ := by
          apply integral_congr_ae
          filter_upwards with xi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q hq
          rw [← Finset.mul_sum]
          ring
        _ = ∑ q ∈ Icc 1 Q,
              ∫ xi : Real, ((q : Real) / (q.totient : Real)) *
                ∑ chi ∈ primitiveCharacters q,
                  spectralMajorant
                      (Real.log (X : Real) + 3 * integerLogEpsilon X)
                      (integerLogEpsilon X) xi *
                    ‖bilinearCharacterProduct
                      (fourierTwist xi a) (fourierTwist xi b) M N q chi‖ := by
          rw [integral_finsetSum]
          intro q hq
          exact (integrable_finsetSum (primitiveCharacters q) (fun chi hchi =>
            commonSpectralBilinearIntegrable X
              (le_trans (by norm_num) hX) a b M N q chi)).const_mul _
        _ = ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
              ∑ chi ∈ primitiveCharacters q,
                ∫ xi : Real,
                  spectralMajorant
                      (Real.log (X : Real) + 3 * integerLogEpsilon X)
                      (integerLogEpsilon X) xi *
                    ‖bilinearCharacterProduct
                      (fourierTwist xi a) (fourierTwist xi b) M N q chi‖ := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [integral_const_mul]
          rw [integral_finsetSum]
          intro chi hchi
          exact commonSpectralBilinearIntegrable X
            (le_trans (by norm_num) hX) a b M N q chi
theorem weightedMaximalBilinear_le_cutoffFactor
    (X M N Q : Nat) (a b : Nat -> Complex)
    (hX : 2 <= X) (hQ : 1 <= Q) :
    ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          maximalBilinearNorm a b M N X chi <=
      (16 + 4 * Real.log ((X : Real) + 1)) *
        (Real.sqrt (36 * ((M : Real) + (Q : Real) ^ 2) *
            positiveCoefficientMass a M) *
          Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) *
            positiveCoefficientMass b N)) := by
  let A : Real := Real.log (X : Real) + 3 * integerLogEpsilon X
  let eps : Real := integerLogEpsilon X
  let K : Real :=
    Real.sqrt (36 * ((M : Real) + (Q : Real) ^ 2) *
        positiveCoefficientMass a M) *
      Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) *
        positiveCoefficientMass b N)
  have hX1 : 1 <= X := le_trans (by norm_num) hX
  have heps : 0 < eps := by simpa [eps] using integerLogEpsilon_pos X hX1
  have hA : 0 < A := by
    dsimp [A]
    linarith [log_nat_nonneg X hX1, integerLogEpsilon_pos X hX1]
  have hepsA : eps <= A := by
    dsimp [A, eps]
    linarith [log_nat_nonneg X hX1, integerLogEpsilon_pos X hX1]
  have hK : 0 <= K := by dsimp [K]; positivity
  have hnonmax (xi : Real) : twistedBilinearMean xi a b M N Q <= K := by
    unfold twistedBilinearMean
    simpa only [positiveCoefficientMass_fourierTwist] using
      nonmaximalBilinearLargeSieve M N Q
        (fourierTwist xi a) (fourierTwist xi b) hQ
  have hmajorant := spectralMajorant_integrable A eps hA heps
  have hintegral : ∫ xi : Real, spectralMajorant A eps xi <=
      16 + 4 * Real.log ((X : Real) + 1) := by
    calc
      (∫ xi : Real, spectralMajorant A eps xi) =
          4 + 2 * Real.log (A / eps) :=
        integral_spectralMajorant A eps hA heps hepsA
      _ <= 16 + 4 * Real.log ((X : Real) + 1) := by
        dsimp [A, eps]
        linarith [log_integerLogCutoff_ratio_le X hX1]
  calc
    (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          maximalBilinearNorm a b M N X chi) <=
        ∫ xi : Real, spectralMajorant A eps xi *
          twistedBilinearMean xi a b M N Q := by
      simpa [A, eps] using
        weightedMaximalBilinear_le_commonIntegral X M N Q a b hX
    _ <= ∫ xi : Real, spectralMajorant A eps xi * K := by
      apply integral_mono
        (by simpa [A, eps] using
          commonSpectralTwistedMeanIntegrable X M N Q a b hX1)
        (hmajorant.mul_const K)
      intro xi
      exact mul_le_mul_of_nonneg_left (hnonmax xi)
        (spectralMajorant_nonneg A eps xi hA.le heps.le)
    _ = (∫ xi : Real, spectralMajorant A eps xi) * K :=
      integral_mul_const K _
    _ <= (16 + 4 * Real.log ((X : Real) + 1)) * K :=
      mul_le_mul_of_nonneg_right hintegral hK
    _ = (16 + 4 * Real.log ((X : Real) + 1)) *
        (Real.sqrt (36 * ((M : Real) + (Q : Real) ^ 2) *
            positiveCoefficientMass a M) *
          Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) *
            positiveCoefficientMass b N)) := by rfl
theorem cutoffFactor_le_log_product (X M N : Nat)
    (hX : 2 <= X) (hM : 1 <= M) (hN : 1 <= N) :
    16 + 4 * Real.log ((X : Real) + 1) <=
      40 * Real.log ((X * M * N : Nat) : Real) := by
  have hZNat : X <= X * M * N := by
    simpa [mul_assoc] using
      Nat.mul_le_mul (Nat.mul_le_mul_left X hM) hN
  have hXReal : (2 : Real) <= (X : Real) := by exact_mod_cast hX
  have hZReal : (X : Real) <= ((X * M * N : Nat) : Real) := by
    exact_mod_cast hZNat
  have hZPos : 0 < ((X * M * N : Nat) : Real) := by linarith
  have hXp1Zsq : (X : Real) + 1 <= ((X * M * N : Nat) : Real) ^ 2 := by
    have hXsq : (X : Real) + 1 <= (X : Real) ^ 2 := by nlinarith
    have hsq : (X : Real) ^ 2 <= ((X * M * N : Nat) : Real) ^ 2 := by
      nlinarith
    exact hXsq.trans hsq
  have hlogXp1 : Real.log ((X : Real) + 1) <=
      2 * Real.log ((X * M * N : Nat) : Real) := by
    calc
      Real.log ((X : Real) + 1) <=
          Real.log (((X * M * N : Nat) : Real) ^ 2) :=
        Real.log_le_log (by linarith) hXp1Zsq
      _ = 2 * Real.log ((X * M * N : Nat) : Real) := by
        rw [Real.log_pow]
        norm_num
  have hhalfLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : Real)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlogTwoZ : Real.log 2 <= Real.log ((X * M * N : Nat) : Real) :=
    Real.log_le_log (by norm_num) (hXReal.trans hZReal)
  have hhalfLogZ : (1 / 2 : Real) <=
      Real.log ((X * M * N : Nat) : Real) := hhalfLogTwo.trans hlogTwoZ
  linarith
theorem coefficientMass_nonneg (a : Nat -> Complex) (M : Nat) :
    0 <= coefficientMass a M := by
  unfold coefficientMass
  positivity
theorem sqrt_thirtySix_mul_product (U V : Real) (hU : 0 <= U) :
    Real.sqrt (36 * U) * Real.sqrt (36 * V) =
      36 * Real.sqrt (U * V) := by
  calc
    Real.sqrt (36 * U) * Real.sqrt (36 * V) =
        Real.sqrt ((36 * U) * (36 * V)) := by
      rw [Real.sqrt_mul (by positivity : 0 <= 36 * U)]
    _ = Real.sqrt (36 ^ 2 * (U * V)) := by
      congr 1
      ring
    _ = Real.sqrt (36 ^ 2) * Real.sqrt (U * V) := by
      rw [Real.sqrt_mul (sq_nonneg (36 : Real))]
    _ = 36 * Real.sqrt (U * V) := by norm_num
theorem maximalBilinearLargeSieve : MaximalBilinearLargeSieveStatement := by
  refine ⟨1440, by norm_num, ?_⟩
  intro X M N Q a b hX hM hN hQ
  have hraw := weightedMaximalBilinear_le_cutoffFactor X M N Q a b hX hQ
  rw [positiveCoefficientMass_eq_coefficientMass,
    positiveCoefficientMass_eq_coefficientMass] at hraw
  have hMterm : 0 <= ((M : Real) + (Q : Real) ^ 2) * coefficientMass a M := by
    exact mul_nonneg (by positivity) (coefficientMass_nonneg a M)
  have hsqrt :
      Real.sqrt (36 * ((M : Real) + (Q : Real) ^ 2) * coefficientMass a M) *
          Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) * coefficientMass b N) =
        36 * Real.sqrt (((M : Real) + (Q : Real) ^ 2) *
          ((N : Real) + (Q : Real) ^ 2) *
          coefficientMass a M * coefficientMass b N) := by
    rw [show 36 * ((M : Real) + (Q : Real) ^ 2) * coefficientMass a M =
        36 * (((M : Real) + (Q : Real) ^ 2) * coefficientMass a M) by ring,
      show 36 * ((N : Real) + (Q : Real) ^ 2) * coefficientMass b N =
        36 * (((N : Real) + (Q : Real) ^ 2) * coefficientMass b N) by ring,
      sqrt_thirtySix_mul_product
      (((M : Real) + (Q : Real) ^ 2) * coefficientMass a M)
      (((N : Real) + (Q : Real) ^ 2) * coefficientMass b N)
      hMterm]
    congr 2
    ring
  have hcutoff := cutoffFactor_le_log_product X M N hX hM hN
  calc
    (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          maximalBilinearNorm a b M N X chi) <=
        (16 + 4 * Real.log ((X : Real) + 1)) *
          (Real.sqrt (36 * ((M : Real) + (Q : Real) ^ 2) * coefficientMass a M) *
            Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) * coefficientMass b N)) :=
      hraw
    _ = (16 + 4 * Real.log ((X : Real) + 1)) *
        (36 * Real.sqrt (((M : Real) + (Q : Real) ^ 2) *
          ((N : Real) + (Q : Real) ^ 2) *
          coefficientMass a M * coefficientMass b N)) := by rw [hsqrt]
    _ <= (40 * Real.log ((X * M * N : Nat) : Real)) *
        (36 * Real.sqrt (((M : Real) + (Q : Real) ^ 2) *
          ((N : Real) + (Q : Real) ^ 2) *
          coefficientMass a M * coefficientMass b N)) := by
      exact mul_le_mul_of_nonneg_right hcutoff (by positivity)
    _ = 1440 * Real.log ((X * M * N : Nat) : Real) *
        Real.sqrt (((M : Real) + (Q : Real) ^ 2) *
          ((N : Real) + (Q : Real) ^ 2) *
          coefficientMass a M * coefficientMass b N) := by ring
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Finset
open scoped BigOperators
namespace BombieriVinogradov.VaughanIdentity
open ArithmeticFunction
def truncateLE {R : Type*} [Zero R] (a : ArithmeticFunction R)
    (cutoff : Nat) : ArithmeticFunction R :=
  ⟨fun n => if n <= cutoff then a n else 0, by simp⟩
@[simp]
theorem truncateLE_apply {R : Type*} [Zero R]
    (a : ArithmeticFunction R) (cutoff n : Nat) :
    truncateLE a cutoff n = if n <= cutoff then a n else 0 := rfl
def lambdaHead (u : Nat) : ArithmeticFunction Real :=
  truncateLE ArithmeticFunction.vonMangoldt u
def moebiusHead (v : Nat) : ArithmeticFunction Real :=
  truncateLE (ArithmeticFunction.moebius : ArithmeticFunction Real) v
def typeI1Kernel (v : Nat) : ArithmeticFunction Real :=
  moebiusHead v * ArithmeticFunction.log
def typeI2Kernel (u v : Nat) : ArithmeticFunction Real :=
  lambdaHead u * moebiusHead v * ArithmeticFunction.zeta
def typeIIKernel (u v : Nat) : ArithmeticFunction Real :=
  (ArithmeticFunction.log - lambdaHead u * ArithmeticFunction.zeta) *
    ((ArithmeticFunction.moebius : ArithmeticFunction Real) - moebiusHead v)
def weightedKernelSum (kernel : ArithmeticFunction Real)
    (y : Nat) (f : Nat -> Complex) : Complex :=
  ∑ n ∈ Icc 1 y, (kernel n : Complex) * f n
def mangoldtSum (y : Nat) (f : Nat -> Complex) : Complex :=
  weightedKernelSum ArithmeticFunction.vonMangoldt y f
def vaughanS1 (v y : Nat) (f : Nat -> Complex) : Complex :=
  weightedKernelSum (typeI1Kernel v) y f
def vaughanS2 (u v y : Nat) (f : Nat -> Complex) : Complex :=
  weightedKernelSum (typeI2Kernel u v) y f
def vaughanS3 (u v y : Nat) (f : Nat -> Complex) : Complex :=
  weightedKernelSum (typeIIKernel u v) y f
def vaughanS4 (u y : Nat) (f : Nat -> Complex) : Complex :=
  weightedKernelSum (lambdaHead u) y f
def VaughanIdentityStatement : Prop :=
  ∀ (u v y : Nat) (f : Nat -> Complex), 0 < u -> 0 < v -> 2 <= y ->
    mangoldtSum y f =
      vaughanS1 v y f - vaughanS2 u v y f +
        vaughanS3 u v y f + vaughanS4 u y f
end BombieriVinogradov.VaughanIdentity
end
end

section
noncomputable section
open Finset
open scoped BigOperators
namespace BombieriVinogradov.VaughanIdentity
open ArithmeticFunction
theorem vaughanKernelIdentity (u v : Nat) :
    ArithmeticFunction.vonMangoldt =
      typeI1Kernel v - typeI2Kernel u v + typeIIKernel u v + lambdaHead u := by
  have hzetaMu :
      (ArithmeticFunction.zeta : ArithmeticFunction Real) *
          (ArithmeticFunction.moebius : ArithmeticFunction Real) = 1 :=
    ArithmeticFunction.coe_zeta_mul_coe_moebius
  calc
    ArithmeticFunction.vonMangoldt =
        ArithmeticFunction.log *
          (ArithmeticFunction.moebius : ArithmeticFunction Real) :=
      ArithmeticFunction.log_mul_moebius_eq_vonMangoldt.symm
    _ = typeI1Kernel v - typeI2Kernel u v + typeIIKernel u v + lambdaHead u := by
      calc
        ArithmeticFunction.log *
            (ArithmeticFunction.moebius : ArithmeticFunction Real) =
          typeI1Kernel v - typeI2Kernel u v + typeIIKernel u v + lambdaHead u +
            lambdaHead u *
              ((ArithmeticFunction.zeta : ArithmeticFunction Real) *
                (ArithmeticFunction.moebius : ArithmeticFunction Real) - 1) := by
            unfold typeI1Kernel typeI2Kernel typeIIKernel
            ring
        _ = _ := by rw [hzetaMu]; simp
theorem typeI1Kernel_apply (v n : Nat) :
    typeI1Kernel v n =
      ∑ pair ∈ Nat.divisorsAntidiagonal n,
        (if pair.1 <= v then
          ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.1)
        else 0) * Real.log pair.2 := by
  unfold typeI1Kernel
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro pair hpair
  simp [moebiusHead, truncateLE, ArithmeticFunction.log_apply]
theorem typeI2Kernel_apply (u v n : Nat) :
    typeI2Kernel u v n =
      ∑ pair ∈ Nat.divisorsAntidiagonal n,
        (∑ factors ∈ Nat.divisorsAntidiagonal pair.1,
          (if factors.1 <= u then ArithmeticFunction.vonMangoldt factors.1 else 0) *
            (if factors.2 <= v then
              ((ArithmeticFunction.moebius : ArithmeticFunction Real) factors.2)
            else 0)) *
          ((ArithmeticFunction.zeta : ArithmeticFunction Real) pair.2) := by
  unfold typeI2Kernel
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro pair hpair
  apply congrArg (fun value : Real =>
    value * ((ArithmeticFunction.zeta : ArithmeticFunction Real) pair.2))
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro factors hfactors
  simp [lambdaHead, moebiusHead, truncateLE]
theorem log_sub_lambdaHead_mul_zeta (u : Nat) :
    ArithmeticFunction.log - lambdaHead u * ArithmeticFunction.zeta =
      (ArithmeticFunction.vonMangoldt - lambdaHead u) * ArithmeticFunction.zeta := by
  rw [← ArithmeticFunction.vonMangoldt_mul_zeta]
  ring
theorem typeIIKernel_apply (u v n : Nat) :
    typeIIKernel u v n =
      ∑ pair ∈ Nat.divisorsAntidiagonal n,
        (∑ factors ∈ Nat.divisorsAntidiagonal pair.1,
          (if factors.1 <= u then 0 else ArithmeticFunction.vonMangoldt factors.1) *
            ((ArithmeticFunction.zeta : ArithmeticFunction Real) factors.2)) *
          (if pair.2 <= v then 0 else
            ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.2)) := by
  rw [typeIIKernel, log_sub_lambdaHead_mul_zeta]
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro pair hpair
  have hleft :
      ((ArithmeticFunction.vonMangoldt - lambdaHead u) *
          ArithmeticFunction.zeta) pair.1 =
        ∑ factors ∈ Nat.divisorsAntidiagonal pair.1,
          (if factors.1 <= u then 0 else ArithmeticFunction.vonMangoldt factors.1) *
            ((ArithmeticFunction.zeta : ArithmeticFunction Real) factors.2) := by
    rw [ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl
    intro factors hfactors
    have htail :
        (ArithmeticFunction.vonMangoldt - lambdaHead u) factors.1 =
          if factors.1 <= u then 0 else ArithmeticFunction.vonMangoldt factors.1 := by
      change ArithmeticFunction.vonMangoldt factors.1 -
        (if factors.1 <= u then ArithmeticFunction.vonMangoldt factors.1 else 0) = _
      by_cases hle : factors.1 <= u <;> simp [hle]
    rw [htail]
  have hright :
      ((ArithmeticFunction.moebius : ArithmeticFunction Real) - moebiusHead v) pair.2 =
        if pair.2 <= v then 0 else
          ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.2) := by
    change ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.2) -
      (if pair.2 <= v then
        ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.2) else 0) = _
    by_cases hle : pair.2 <= v <;> simp [hle]
  rw [hleft, hright]
end BombieriVinogradov.VaughanIdentity
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
open BombieriVinogradov.VaughanIdentity
def typeIILeftKernelCoefficient (u m : Nat) : Real :=
  ∑ factors ∈ Nat.divisorsAntidiagonal m,
    (if factors.1 <= u then 0 else ArithmeticFunction.vonMangoldt factors.1) *
      ((ArithmeticFunction.zeta : ArithmeticFunction Real) factors.2)
def typeIIBlockLeftCoefficient (u M m : Nat) : Complex :=
  if M < m ∧ m <= 2 * M then (typeIILeftKernelCoefficient u m : Complex) else 0
def typeIIRightCoefficient (v n : Nat) : Complex :=
  if n <= v then 0 else
    (((ArithmeticFunction.moebius : ArithmeticFunction Real) n : Real) : Complex)
theorem typeIILeftKernelCoefficient_nonneg (u m : Nat) :
    0 <= typeIILeftKernelCoefficient u m := by
  unfold typeIILeftKernelCoefficient
  apply Finset.sum_nonneg
  intro factors hfactors
  have hright : Ne factors.2 0 :=
    Nat.right_ne_zero_of_mem_divisorsAntidiagonal hfactors
  by_cases hcutoff : factors.1 <= u
  · simp [hcutoff]
  · simp [hcutoff, ArithmeticFunction.zeta_apply_ne hright,
      ArithmeticFunction.vonMangoldt_nonneg]
theorem typeIILeftKernelCoefficient_le_log (u m : Nat) :
    typeIILeftKernelCoefficient u m <= Real.log (m : Real) := by
  calc
    typeIILeftKernelCoefficient u m <=
        ∑ factors ∈ Nat.divisorsAntidiagonal m,
          ArithmeticFunction.vonMangoldt factors.1 *
            ((ArithmeticFunction.zeta : ArithmeticFunction Real) factors.2) := by
      unfold typeIILeftKernelCoefficient
      apply Finset.sum_le_sum
      intro factors hfactors
      have hright : Ne factors.2 0 :=
        Nat.right_ne_zero_of_mem_divisorsAntidiagonal hfactors
      by_cases hcutoff : factors.1 <= u
      · simp [hcutoff, ArithmeticFunction.zeta_apply_ne hright,
          ArithmeticFunction.vonMangoldt_nonneg]
      · simp [hcutoff]
    _ = (ArithmeticFunction.vonMangoldt *
        (ArithmeticFunction.zeta : ArithmeticFunction Real)) m := by
      rw [ArithmeticFunction.mul_apply]
    _ = Real.log (m : Real) := by
      rw [ArithmeticFunction.vonMangoldt_mul_zeta]
      rfl
theorem typeIIKernel_apply_coefficients (u v n : Nat) :
    typeIIKernel u v n =
      ∑ pair ∈ Nat.divisorsAntidiagonal n,
        typeIILeftKernelCoefficient u pair.1 *
          (if pair.2 <= v then 0 else
            ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.2)) := by
  rw [typeIIKernel_apply]
  rfl
def typeIICharacterSum (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ m ∈ Icc 1 Y, ∑ n ∈ Icc 1 (Y / m),
    (typeIILeftKernelCoefficient u m : Complex) * typeIIRightCoefficient v n *
      chi ((m * n : Nat) : ZMod q)
theorem vaughanS3_eq_typeIICharacterSum (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) :
    vaughanS3 u v Y (fun n => chi (n : ZMod q)) =
      typeIICharacterSum u v Y q chi := by
  unfold vaughanS3 weightedKernelSum
  simp_rw [typeIIKernel_apply_coefficients]
  push_cast
  simp_rw [Finset.sum_mul]
  have hreindex :
      (∑ k ∈ Icc 1 Y, ∑ pair ∈ Nat.divisorsAntidiagonal k,
        (typeIILeftKernelCoefficient u pair.1 : Complex) *
          (((if pair.2 <= v then 0 else
            ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.2)) : Real) : Complex) *
              chi (k : ZMod q)) =
        ∑ k ∈ Icc 1 Y, ∑ pair ∈ Nat.divisorsAntidiagonal k,
          (typeIILeftKernelCoefficient u pair.1 : Complex) *
            (((if pair.2 <= v then 0 else
              ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.2)) : Real) : Complex) *
                chi ((pair.1 * pair.2 : Nat) : ZMod q) := by
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro pair hpair
    rw [(Nat.mem_divisorsAntidiagonal.mp hpair).1]
  rw [hreindex]
  have hhyper := sum_divisorsAntidiagonal_Icc_eq_hyperbola
    (fun m n =>
      (typeIILeftKernelCoefficient u m : Complex) *
        (((if n <= v then 0 else
          ((ArithmeticFunction.moebius : ArithmeticFunction Real) n)) : Real) : Complex) *
            chi ((m * n : Nat) : ZMod q)) Y
  rw [hhyper]
  unfold typeIICharacterSum typeIIRightCoefficient
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hcutoff : n <= v <;> simp [hcutoff]
theorem norm_typeIIBlockLeftCoefficient_le (u M m : Nat) :
    ‖typeIIBlockLeftCoefficient u M m‖ <= Real.log ((2 * M : Nat) : Real) := by
  by_cases hsupport : M < m ∧ m <= 2 * M
  · rw [typeIIBlockLeftCoefficient, if_pos hsupport]
    have hnonneg := typeIILeftKernelCoefficient_nonneg u m
    have hlog := typeIILeftKernelCoefficient_le_log u m
    have hlogMono : Real.log (m : Real) <= Real.log ((2 * M : Nat) : Real) := by
      apply Real.log_le_log
      · exact_mod_cast (show 0 < m by omega)
      · exact_mod_cast hsupport.2
    simpa [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg] using hlog.trans hlogMono
  · rw [typeIIBlockLeftCoefficient, if_neg hsupport, norm_zero]
    simpa using Real.log_natCast_nonneg (2 * M)
theorem typeIIBlockLeftCoefficient_mass_le (u M : Nat) :
    coefficientMass (typeIIBlockLeftCoefficient u M) (2 * M) <=
      (2 * M : Nat) * Real.log ((2 * M : Nat) : Real) ^ 2 := by
  unfold coefficientMass
  have hlog : 0 <= Real.log ((2 * M : Nat) : Real) :=
    Real.log_natCast_nonneg (2 * M)
  calc
    ∑ m ∈ Icc 1 (2 * M), ‖typeIIBlockLeftCoefficient u M m‖ ^ 2 <=
        ∑ m ∈ Icc 1 (2 * M),
          Real.log ((2 * M : Nat) : Real) ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      nlinarith [norm_nonneg (typeIIBlockLeftCoefficient u M m),
        norm_typeIIBlockLeftCoefficient_le u M m]
    _ = (2 * M : Nat) * Real.log ((2 * M : Nat) : Real) ^ 2 := by simp
theorem norm_typeIIRightCoefficient_le_one (v n : Nat) :
    ‖typeIIRightCoefficient v n‖ <= 1 := by
  by_cases hcutoff : n <= v
  · simp [typeIIRightCoefficient, hcutoff]
  · rw [typeIIRightCoefficient, if_neg hcutoff]
    rcases ArithmeticFunction.moebius_eq_or n with hzero | hone | hneg
    · simp [hzero]
    · simp [hone]
    · simp [hneg]
theorem typeIIRightCoefficient_mass_le (v N : Nat) :
    coefficientMass (typeIIRightCoefficient v) N <= (N : Real) := by
  unfold coefficientMass
  calc
    ∑ n ∈ Icc 1 N, ‖typeIIRightCoefficient v n‖ ^ 2 <=
        ∑ n ∈ Icc 1 N, (1 : Real) := by
      apply Finset.sum_le_sum
      intro n hn
      nlinarith [norm_nonneg (typeIIRightCoefficient v n),
        norm_typeIIRightCoefficient_le_one v n]
    _ = (N : Real) := by simp
def typeIIBlockMean (u v M N X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q,
      maximalBilinearNorm
        (typeIIBlockLeftCoefficient u M) (typeIIRightCoefficient v)
        (2 * M) N X chi
theorem typeIIBlockMean_le (u v M N X Q : Nat)
    (hX : 2 <= X) (hQ : 1 <= Q) :
    typeIIBlockMean u v M N X Q <=
      (16 + 4 * Real.log ((X : Real) + 1)) *
        (Real.sqrt (36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
            (((2 * M : Nat) : Real) * Real.log ((2 * M : Nat) : Real) ^ 2)) *
          Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) * (N : Real))) := by
  have hraw := weightedMaximalBilinear_le_cutoffFactor
    X (2 * M) N Q
      (typeIIBlockLeftCoefficient u M) (typeIIRightCoefficient v) hX hQ
  rw [positiveCoefficientMass_eq_coefficientMass,
    positiveCoefficientMass_eq_coefficientMass] at hraw
  unfold typeIIBlockMean
  apply hraw.trans
  have hleft := typeIIBlockLeftCoefficient_mass_le u M
  have hright := typeIIRightCoefficient_mass_le v N
  have hleftFactor : 0 <=
      36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) := by positivity
  have hrightFactor : 0 <= 36 * ((N : Real) + (Q : Real) ^ 2) := by positivity
  have hcutoff : 0 <= 16 + 4 * Real.log ((X : Real) + 1) := by
    have : 0 <= Real.log ((X : Real) + 1) := by
      apply Real.log_nonneg
      have hnat : 1 <= X + 1 := by omega
      exact_mod_cast hnat
    positivity
  have hsqrtLeft :
      Real.sqrt (36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
          coefficientMass (typeIIBlockLeftCoefficient u M) (2 * M)) <=
        Real.sqrt (36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
          (((2 * M : Nat) : Real) * Real.log ((2 * M : Nat) : Real) ^ 2)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hleft hleftFactor
  have hsqrtRight :
      Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) *
          coefficientMass (typeIIRightCoefficient v) N) <=
        Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) * (N : Real)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hright hrightFactor
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul hsqrtLeft hsqrtRight (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hcutoff
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
open BombieriVinogradov.VaughanIdentity
def dyadicExponentSet (X : Nat) : Finset Nat :=
  range (Nat.log 2 X + 1)
theorem dyadicExponent_mem_for {m X : Nat} (hm : 2 <= m) (hmX : m <= X) :
    let k := Nat.log 2 (m - 1)
    k ∈ dyadicExponentSet X ∧ 2 ^ k < m ∧ m <= 2 * 2 ^ k := by
  let k := Nat.log 2 (m - 1)
  have hmSub : Ne (m - 1) 0 := by omega
  have hpowLower : 2 ^ k <= m - 1 := by
    exact Nat.pow_log_le_self 2 hmSub
  have hpowUpper : m - 1 < 2 ^ (k + 1) := by
    simpa [k] using Nat.lt_pow_succ_log_self Nat.one_lt_two (m - 1)
  have hlogMono : k <= Nat.log 2 X := by
    apply Nat.log_mono_right
    omega
  have hsubLt : m - 1 < m := Nat.sub_lt (by omega) (by omega)
  refine ⟨Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hlogMono), ?_, ?_⟩
  · exact hpowLower.trans_lt hsubLt
  · have hmEq : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
    have hmle : m <= 2 ^ (k + 1) := by
      rw [← hmEq]
      exact Nat.succ_le_iff.mpr hpowUpper
    simpa [pow_succ, mul_comm] using hmle
theorem dyadicExponent_unique {k m : Nat}
    (hblock : 2 ^ k < m ∧ m <= 2 * 2 ^ k) :
    Nat.log 2 (m - 1) = k := by
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · have hsubLt : m - 1 < m := Nat.sub_lt (by omega) (by omega)
    simpa [pow_succ, mul_comm] using hsubLt.trans_le hblock.2
theorem typeIILeftKernelCoefficient_eq_zero_of_le {u m : Nat} (hmu : m <= u) :
    typeIILeftKernelCoefficient u m = 0 := by
  unfold typeIILeftKernelCoefficient
  apply Finset.sum_eq_zero
  intro factors hfactors
  have hright : 0 < factors.2 := Nat.pos_of_ne_zero
    (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hfactors)
  have hproduct := (Nat.mem_divisorsAntidiagonal.mp hfactors).1
  have hleft : factors.1 <= m := by
    calc
      factors.1 <= factors.1 * factors.2 :=
        Nat.le_mul_of_pos_right factors.1 hright
      _ = m := hproduct
  simp [hleft.trans hmu]
theorem sum_typeIIBlockLeftCoefficient_eq (u X m : Nat)
    (hu : 1 <= u) (hmX : m <= X) :
    ∑ k ∈ dyadicExponentSet X, typeIIBlockLeftCoefficient u (2 ^ k) m =
      (typeIILeftKernelCoefficient u m : Complex) := by
  by_cases hmu : m <= u
  · have hzero := typeIILeftKernelCoefficient_eq_zero_of_le hmu
    simp [typeIIBlockLeftCoefficient, hzero]
  · have hm : 2 <= m := by omega
    let k₀ := Nat.log 2 (m - 1)
    have hk₀Data := dyadicExponent_mem_for hm hmX
    change k₀ ∈ dyadicExponentSet X ∧ 2 ^ k₀ < m ∧ m <= 2 * 2 ^ k₀ at hk₀Data
    rw [Finset.sum_eq_single k₀]
    · rw [typeIIBlockLeftCoefficient, if_pos hk₀Data.2]
    · intro k hk hne
      rw [typeIIBlockLeftCoefficient, if_neg]
      intro hblock
      apply hne
      exact (dyadicExponent_unique hblock).symm
    · intro hknot
      exact (hknot hk₀Data.1).elim
theorem Icc_one_div_eq_filter (Y m : Nat) (hm : 1 <= m) :
    Icc 1 (Y / m) = (Icc 1 Y).filter fun n => m * n <= Y := by
  ext n
  simp only [Finset.mem_Icc, Finset.mem_filter]
  constructor
  · intro hn
    have hproduct : m * n <= Y := by
      have := (Nat.le_div_iff_mul_le (by omega : 0 < m)).mp hn.2
      simpa [Nat.mul_comm] using this
    exact ⟨⟨hn.1, (Nat.le_mul_of_pos_left n (by omega)).trans hproduct⟩, hproduct⟩
  · intro hn
    refine ⟨hn.1.1, ?_⟩
    apply (Nat.le_div_iff_mul_le (by omega : 0 < m)).mpr
    simpa [Nat.mul_comm] using hn.2
theorem typeIICharacterSum_eq_restricted (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) :
    typeIICharacterSum u v Y q chi =
      restrictedBilinearCharacterSum
        (fun m => (typeIILeftKernelCoefficient u m : Complex))
        (typeIIRightCoefficient v) Y Y Y q chi := by
  unfold typeIICharacterSum restrictedBilinearCharacterSum
  apply Finset.sum_congr rfl
  intro m hm
  rw [Icc_one_div_eq_filter Y m (Finset.mem_Icc.mp hm).1]
  rw [Finset.sum_filter]
def typeIIDyadicGlobalBlockSum (u v Y q k : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  restrictedBilinearCharacterSum
    (typeIIBlockLeftCoefficient u (2 ^ k)) (typeIIRightCoefficient v)
    Y Y Y q chi
theorem typeIICharacterSum_eq_sum_dyadicGlobalBlocks
    (u v X Y q : Nat) (chi : DirichletCharacter Complex q)
    (hu : 1 <= u) (hYX : Y <= X) :
    typeIICharacterSum u v Y q chi =
      ∑ k ∈ dyadicExponentSet X, typeIIDyadicGlobalBlockSum u v Y q k chi := by
  rw [typeIICharacterSum_eq_restricted]
  unfold typeIIDyadicGlobalBlockSum restrictedBilinearCharacterSum
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hproduct : m * n <= Y
  · simp only [hproduct, if_true]
    rw [← Finset.sum_mul]
    rw [← Finset.sum_mul]
    rw [sum_typeIIBlockLeftCoefficient_eq u X m hu
      ((Finset.mem_Icc.mp hm).2.trans hYX)]
  · simp [hproduct]
def typeIIBlockPairSet (M A B Y : Nat) : Finset (Nat × Nat) :=
  (Icc 1 A ×ˢ Icc 1 B).filter fun pair =>
    M < pair.1 ∧ pair.1 <= 2 * M ∧ pair.1 * pair.2 <= Y
def typeIIBlockPairSum (u v M A B Y q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ pair ∈ typeIIBlockPairSet M A B Y,
    (typeIILeftKernelCoefficient u pair.1 : Complex) * typeIIRightCoefficient v pair.2 *
      chi ((pair.1 * pair.2 : Nat) : ZMod q)
theorem restricted_typeIIBlock_eq_pairSum
    (u v M A B Y q : Nat) (chi : DirichletCharacter Complex q) :
    restrictedBilinearCharacterSum
        (typeIIBlockLeftCoefficient u M) (typeIIRightCoefficient v)
        A B Y q chi = typeIIBlockPairSum u v M A B Y q chi := by
  unfold restrictedBilinearCharacterSum typeIIBlockPairSum typeIIBlockPairSet
  rw [← Finset.sum_product']
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro pair hpair
  by_cases hsupport : M < pair.1 ∧ pair.1 <= 2 * M
  · by_cases hproduct : pair.1 * pair.2 <= Y
    · simp [hsupport, hproduct, typeIIBlockLeftCoefficient]
    · simp [hsupport, hproduct]
  · rw [typeIIBlockLeftCoefficient, if_neg hsupport]
    have hall : ¬(M < pair.1 ∧ pair.1 <= 2 * M ∧ pair.1 * pair.2 <= Y) := by
      intro h
      exact hsupport ⟨h.1, h.2.1⟩
    simp [hall]
theorem typeIIBlockPairSet_global_eq_efficient
    (M X Y : Nat) (hM : 1 <= M) (hYX : Y <= X) :
    typeIIBlockPairSet M Y Y Y = typeIIBlockPairSet M (2 * M) (X / M) Y := by
  ext pair
  unfold typeIIBlockPairSet
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc]
  constructor
  · intro hpair
    have hMn : M * pair.2 <= pair.1 * pair.2 :=
      Nat.mul_le_mul_right pair.2 hpair.2.1.le
    have hnDiv : pair.2 <= X / M := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < M)).mpr
      simpa [Nat.mul_comm] using hMn.trans (hpair.2.2.2.trans hYX)
    exact ⟨⟨⟨hpair.1.1.1, hpair.2.2.1⟩, ⟨hpair.1.2.1, hnDiv⟩⟩,
      hpair.2⟩
  · intro hpair
    have hmpos : 0 < pair.1 := by omega
    have hnpos : 0 < pair.2 := by omega
    have hmY : pair.1 <= Y :=
      (Nat.le_mul_of_pos_right pair.1 hnpos).trans hpair.2.2.2
    have hnY : pair.2 <= Y :=
      (Nat.le_mul_of_pos_left pair.2 hmpos).trans hpair.2.2.2
    exact ⟨⟨⟨by omega, hmY⟩, ⟨by omega, hnY⟩⟩, hpair.2⟩
def typeIIDyadicBlockSum (u v X Y q k : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  restrictedBilinearCharacterSum
    (typeIIBlockLeftCoefficient u (2 ^ k)) (typeIIRightCoefficient v)
    (2 * 2 ^ k) (X / 2 ^ k) Y q chi
theorem typeIIDyadicGlobalBlockSum_eq_blockSum
    (u v X Y q k : Nat) (chi : DirichletCharacter Complex q)
    (hYX : Y <= X) :
    typeIIDyadicGlobalBlockSum u v Y q k chi =
      typeIIDyadicBlockSum u v X Y q k chi := by
  unfold typeIIDyadicGlobalBlockSum typeIIDyadicBlockSum
  rw [restricted_typeIIBlock_eq_pairSum, restricted_typeIIBlock_eq_pairSum]
  unfold typeIIBlockPairSum
  have hpowOne : 1 <= 2 ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k (by omega))
  rw [typeIIBlockPairSet_global_eq_efficient (2 ^ k) X Y hpowOne hYX]
theorem vaughanS3_eq_sum_dyadicBlocks
    (u v X Y q : Nat) (chi : DirichletCharacter Complex q)
    (hu : 1 <= u) (hYX : Y <= X) :
    vaughanS3 u v Y (fun n => chi (n : ZMod q)) =
      ∑ k ∈ dyadicExponentSet X, typeIIDyadicBlockSum u v X Y q k chi := by
  rw [vaughanS3_eq_typeIICharacterSum]
  rw [typeIICharacterSum_eq_sum_dyadicGlobalBlocks u v X Y q chi hu hYX]
  apply Finset.sum_congr rfl
  intro k hk
  exact typeIIDyadicGlobalBlockSum_eq_blockSum u v X Y q k chi hYX
def maximalTypeIICharacterNorm (u v X q : Nat)
    (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖vaughanS3 u v Y (fun n => chi (n : ZMod q))‖
theorem maximalTypeIICharacterNorm_le_sum_blocks
    (u v X q : Nat) (chi : DirichletCharacter Complex q) (hu : 1 <= u) :
    maximalTypeIICharacterNorm u v X q chi <=
      ∑ k ∈ dyadicExponentSet X,
        maximalBilinearNorm
          (typeIIBlockLeftCoefficient u (2 ^ k)) (typeIIRightCoefficient v)
          (2 * 2 ^ k) (X / 2 ^ k) X chi := by
  unfold maximalTypeIICharacterNorm
  apply Finset.sup'_le
  intro Y hY
  have hYX : Y <= X := by
    have := Finset.mem_range.mp hY
    omega
  rw [vaughanS3_eq_sum_dyadicBlocks u v X Y q chi hu hYX]
  calc
    ‖∑ k ∈ dyadicExponentSet X, typeIIDyadicBlockSum u v X Y q k chi‖ <=
        ∑ k ∈ dyadicExponentSet X,
          ‖typeIIDyadicBlockSum u v X Y q k chi‖ := norm_sum_le _ _
    _ <= ∑ k ∈ dyadicExponentSet X,
        maximalBilinearNorm
          (typeIIBlockLeftCoefficient u (2 ^ k)) (typeIIRightCoefficient v)
          (2 * 2 ^ k) (X / 2 ^ k) X chi := by
      apply Finset.sum_le_sum
      intro k hk
      unfold typeIIDyadicBlockSum maximalBilinearNorm
      exact Finset.le_sup'
        (fun Z => ‖restrictedBilinearCharacterSum
          (typeIIBlockLeftCoefficient u (2 ^ k)) (typeIIRightCoefficient v)
          (2 * 2 ^ k) (X / 2 ^ k) Z q chi‖) hY
def typeIIDyadicMean (u v X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalTypeIICharacterNorm u v X q chi
theorem typeIIDyadicMean_le_sum_blockMeans
    (u v X Q : Nat) (hu : 1 <= u) :
    typeIIDyadicMean u v X Q <=
      ∑ k ∈ dyadicExponentSet X,
        typeIIBlockMean u v (2 ^ k) (X / 2 ^ k) X Q := by
  unfold typeIIDyadicMean
  calc
    ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q, maximalTypeIICharacterNorm u v X q chi <=
      ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ∑ k ∈ dyadicExponentSet X,
            maximalBilinearNorm
              (typeIIBlockLeftCoefficient u (2 ^ k)) (typeIIRightCoefficient v)
              (2 * 2 ^ k) (X / 2 ^ k) X chi := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro chi hchi
        exact maximalTypeIICharacterNorm_le_sum_blocks u v X q chi hu
      · positivity
    _ = ∑ k ∈ dyadicExponentSet X,
        typeIIBlockMean u v (2 ^ k) (X / 2 ^ k) X Q := by
      unfold typeIIBlockMean
      let F : (q : Nat) -> DirichletCharacter Complex q -> Nat -> Real :=
        fun q chi k => maximalBilinearNorm
          (typeIIBlockLeftCoefficient u (2 ^ k)) (typeIIRightCoefficient v)
          (2 * 2 ^ k) (X / 2 ^ k) X chi
      change (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q, ∑ k ∈ dyadicExponentSet X, F q chi k) =
        ∑ k ∈ dyadicExponentSet X, ∑ q ∈ Icc 1 Q,
          ((q : Real) / (q.totient : Real)) *
            ∑ chi ∈ primitiveCharacters q, F q chi k
      calc
        _ = ∑ q ∈ Icc 1 Q, ∑ chi ∈ primitiveCharacters q,
            ∑ k ∈ dyadicExponentSet X,
              ((q : Real) / (q.totient : Real)) * F q chi k := by
          simp_rw [Finset.mul_sum]
        _ = ∑ q ∈ Icc 1 Q, ∑ k ∈ dyadicExponentSet X,
            ∑ chi ∈ primitiveCharacters q,
              ((q : Real) / (q.totient : Real)) * F q chi k := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.sum_comm]
        _ = ∑ k ∈ dyadicExponentSet X, ∑ q ∈ Icc 1 Q,
            ∑ chi ∈ primitiveCharacters q,
              ((q : Real) / (q.totient : Real)) * F q chi k := by
          rw [Finset.sum_comm]
        _ = ∑ k ∈ dyadicExponentSet X, ∑ q ∈ Icc 1 Q,
            ((q : Real) / (q.totient : Real)) *
              ∑ chi ∈ primitiveCharacters q, F q chi k := by
          simp_rw [Finset.mul_sum]
def typeIIBlockMajorant (M N X Q : Nat) : Real :=
  (16 + 4 * Real.log ((X : Real) + 1)) *
    (Real.sqrt (36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
        (((2 * M : Nat) : Real) * Real.log ((2 * M : Nat) : Real) ^ 2)) *
      Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) * (N : Real)))
theorem typeIIDyadicMean_le_sum_majorants
    (u v X Q : Nat) (hu : 1 <= u) (hX : 2 <= X) (hQ : 1 <= Q) :
    typeIIDyadicMean u v X Q <=
      ∑ k ∈ dyadicExponentSet X,
        typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := by
  calc
    typeIIDyadicMean u v X Q <=
        ∑ k ∈ dyadicExponentSet X,
          typeIIBlockMean u v (2 ^ k) (X / 2 ^ k) X Q :=
      typeIIDyadicMean_le_sum_blockMeans u v X Q hu
    _ <= ∑ k ∈ dyadicExponentSet X,
        typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := by
      apply Finset.sum_le_sum
      intro k hk
      simpa [typeIIBlockMajorant] using
        typeIIBlockMean_le u v (2 ^ k) (X / 2 ^ k) X Q hX hQ
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
def activeDyadicExponentSet (u v X : Nat) : Finset Nat :=
  (dyadicExponentSet X).filter fun k =>
    u < 2 * 2 ^ k ∧ v < X / 2 ^ k
theorem typeIIBlockLeftCoefficient_eq_zero_of_double_le
    {u M : Nat} (hMu : 2 * M <= u) (m : Nat) :
    typeIIBlockLeftCoefficient u M m = 0 := by
  by_cases hsupport : M < m ∧ m <= 2 * M
  · rw [typeIIBlockLeftCoefficient, if_pos hsupport]
    rw [typeIILeftKernelCoefficient_eq_zero_of_le (hsupport.2.trans hMu)]
    rfl
  · simp [typeIIBlockLeftCoefficient, hsupport]
theorem typeIIBlockMean_eq_zero_of_left
    {u v M N X Q : Nat} (hMu : 2 * M <= u) :
    typeIIBlockMean u v M N X Q = 0 := by
  have hleft : typeIIBlockLeftCoefficient u M = 0 := by
    funext m
    exact typeIIBlockLeftCoefficient_eq_zero_of_double_le hMu m
  unfold typeIIBlockMean maximalBilinearNorm restrictedBilinearCharacterSum
  rw [hleft]
  simp
theorem restricted_typeIIBlock_eq_zero_of_right
    {u v M N Y q : Nat} (hNv : N <= v)
    (chi : DirichletCharacter Complex q) :
    restrictedBilinearCharacterSum
      (typeIIBlockLeftCoefficient u M) (typeIIRightCoefficient v)
      (2 * M) N Y q chi = 0 := by
  unfold restrictedBilinearCharacterSum
  apply Finset.sum_eq_zero
  intro m hm
  apply Finset.sum_eq_zero
  intro n hn
  have hnv : n <= v := (Finset.mem_Icc.mp hn).2.trans hNv
  simp [typeIIRightCoefficient, hnv]
theorem typeIIBlockMean_eq_zero_of_right
    {u v M N X Q : Nat} (hNv : N <= v) :
    typeIIBlockMean u v M N X Q = 0 := by
  unfold typeIIBlockMean maximalBilinearNorm
  simp_rw [restricted_typeIIBlock_eq_zero_of_right hNv]
  simp
theorem typeIIBlockMean_eq_zero_of_inactive
    {u v M N X Q : Nat} (hinactive : 2 * M <= u ∨ N <= v) :
    typeIIBlockMean u v M N X Q = 0 := by
  rcases hinactive with hleft | hright
  · exact typeIIBlockMean_eq_zero_of_left hleft
  · exact typeIIBlockMean_eq_zero_of_right hright
theorem typeIIDyadicMean_le_sum_activeBlockMeans
    (u v X Q : Nat) (hu : 1 <= u) :
    typeIIDyadicMean u v X Q <=
      ∑ k ∈ activeDyadicExponentSet u v X,
        typeIIBlockMean u v (2 ^ k) (X / 2 ^ k) X Q := by
  calc
    typeIIDyadicMean u v X Q <=
        ∑ k ∈ dyadicExponentSet X,
          typeIIBlockMean u v (2 ^ k) (X / 2 ^ k) X Q :=
      typeIIDyadicMean_le_sum_blockMeans u v X Q hu
    _ = ∑ k ∈ activeDyadicExponentSet u v X,
        typeIIBlockMean u v (2 ^ k) (X / 2 ^ k) X Q := by
      symm
      unfold activeDyadicExponentSet
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hactive : u < 2 * 2 ^ k ∧ v < X / 2 ^ k
      · simp [hactive]
      · have hinactive : 2 * 2 ^ k <= u ∨ X / 2 ^ k <= v := by omega
        rw [typeIIBlockMean_eq_zero_of_inactive hinactive]
        simp [hactive]
theorem typeIIDyadicMean_le_sum_activeMajorants
    (u v X Q : Nat) (hu : 1 <= u) (hX : 2 <= X) (hQ : 1 <= Q) :
    typeIIDyadicMean u v X Q <=
      ∑ k ∈ activeDyadicExponentSet u v X,
        typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := by
  calc
    typeIIDyadicMean u v X Q <=
        ∑ k ∈ activeDyadicExponentSet u v X,
          typeIIBlockMean u v (2 ^ k) (X / 2 ^ k) X Q :=
      typeIIDyadicMean_le_sum_activeBlockMeans u v X Q hu
    _ <= ∑ k ∈ activeDyadicExponentSet u v X,
        typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := by
      apply Finset.sum_le_sum
      intro k hk
      simpa [typeIIBlockMajorant] using
        typeIIBlockMean_le u v (2 ^ k) (X / 2 ^ k) X Q hX hQ
theorem typeII_sqrt_core_bound
    {x u m n q : Real}
    (hx : 0 <= x) (hu : 0 < u) (hm : 0 <= m) (hn : 0 <= n) (hq : 0 <= q)
    (hmn : m * n <= x) (hum : u <= 2 * m) (hun : u <= n) :
    Real.sqrt ((2 * m + q ^ 2) * (2 * m) * (n + q ^ 2) * n) <=
      2 * x + 3 * (x * q / Real.sqrt u) +
        2 * (Real.sqrt x * q ^ 2) := by
  let B : Real := x * q / Real.sqrt u
  let C : Real := Real.sqrt x * q ^ 2
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hB : 0 <= B := by dsimp [B]; positivity
  have hC : 0 <= C := by dsimp [C]; positivity
  have hBmul : B ^ 2 * u = x ^ 2 * q ^ 2 := by
    dsimp [B]
    rw [div_pow, Real.sq_sqrt hu.le]
    field_simp [hu.ne']
  have hCsq : C ^ 2 = x * q ^ 4 := by
    dsimp [C]
    rw [mul_pow, Real.sq_sqrt hx]
    ring
  have hmu : m * u <= x := by
    exact (mul_le_mul_of_nonneg_left hun hm).trans hmn
  have hunTwo : u * n <= 2 * x := by
    calc
      u * n <= (2 * m) * n := mul_le_mul_of_nonneg_right hum hn
      _ = 2 * (m * n) := by ring
      _ <= 2 * x := by linarith
  have hmnNonneg : 0 <= m * n := mul_nonneg hm hn
  have htermOne : (m * n) ^ 2 <= x ^ 2 := by nlinarith
  have hprodTwo : (m * n) * (m * u) <= x * x :=
    mul_le_mul hmn hmu (mul_nonneg hm hu.le) hx
  have hprodTwoQ := mul_le_mul_of_nonneg_right hprodTwo (sq_nonneg q)
  have htermTwo : m ^ 2 * n * q ^ 2 <= B ^ 2 := by
    have hscaled : (m ^ 2 * n * q ^ 2) * u <= (B ^ 2) * u := by
      nlinarith [hprodTwoQ, hBmul]
    exact (mul_le_mul_iff_of_pos_right hu).mp (by simpa [mul_assoc] using hscaled)
  have hprodThree : (m * n) * (u * n) <= x * (2 * x) :=
    mul_le_mul hmn hunTwo (mul_nonneg hu.le hn) hx
  have hprodThreeQ := mul_le_mul_of_nonneg_right hprodThree (sq_nonneg q)
  have htermThree : m * n ^ 2 * q ^ 2 <= 2 * B ^ 2 := by
    have hscaled : (m * n ^ 2 * q ^ 2) * u <= (2 * B ^ 2) * u := by
      nlinarith [hprodThreeQ, hBmul]
    exact (mul_le_mul_iff_of_pos_right hu).mp (by simpa [mul_assoc] using hscaled)
  have htermFour : m * n * q ^ 4 <= C ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hmn (by positivity : 0 <= q ^ 4), hCsq]
  have hradicand :
      (2 * m + q ^ 2) * (2 * m) * (n + q ^ 2) * n <=
        (2 * x + 3 * B + 2 * C) ^ 2 := by
    nlinarith [htermOne, htermTwo, htermThree, htermFour,
      sq_nonneg (2 * x + 3 * B + 2 * C)]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · simpa [B, C] using hradicand
theorem typeIIBlockMajorant_eq_core (M N X Q : Nat) :
    typeIIBlockMajorant M N X Q =
      36 * (16 + 4 * Real.log ((X : Real) + 1)) *
        Real.log ((2 * M : Nat) : Real) *
          Real.sqrt (((((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
            ((2 * M : Nat) : Real)) *
              (((N : Real) + (Q : Real) ^ 2) * (N : Real))) := by
  let L : Real := Real.log ((2 * M : Nat) : Real)
  let U : Real := ((((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
    (((2 * M : Nat) : Real) * L ^ 2))
  let V : Real := (((N : Real) + (Q : Real) ^ 2) * (N : Real))
  have hU : 0 <= U := by dsimp [U]; positivity
  have hL : 0 <= L := by
    dsimp [L]
    exact Real.log_natCast_nonneg (2 * M)
  unfold typeIIBlockMajorant
  rw [show 36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
      (((2 * M : Nat) : Real) * Real.log ((2 * M : Nat) : Real) ^ 2) =
        36 * U by dsimp [U, L]; ring]
  rw [show 36 * ((N : Real) + (Q : Real) ^ 2) * (N : Real) =
      36 * V by dsimp [V]; ring]
  rw [sqrt_thirtySix_mul_product U V hU]
  have hfactor : U * V = L ^ 2 *
      (((((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
        ((2 * M : Nat) : Real)) *
          (((N : Real) + (Q : Real) ^ 2) * (N : Real))) := by
    dsimp [U, V]
    ring
  rw [hfactor, Real.sqrt_mul (sq_nonneg L), Real.sqrt_sq_eq_abs, abs_of_nonneg hL]
  dsimp [L]
  ring
def typeIISourceCore (X u Q : Nat) : Real :=
  2 * (X : Real) + 3 * ((X : Real) * (Q : Real) / Real.sqrt (u : Real)) +
    2 * (Real.sqrt (X : Real) * (Q : Real) ^ 2)
theorem active_typeIIBlockMajorant_le
    (M X u Q : Nat) (hX : 2 <= X) (hu : 1 <= u)
    (hMX : M <= X) (hactive : u < 2 * M ∧ u < X / M) :
    typeIIBlockMajorant M (X / M) X Q <=
      2880 * Real.log (X : Real) ^ 2 * typeIISourceCore X u Q := by
  have hXnonneg : 0 <= (X : Real) := by positivity
  have hupos : 0 < (u : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hu)
  have hMnonneg : 0 <= (M : Real) := by positivity
  have hNnonneg : 0 <= ((X / M : Nat) : Real) := by positivity
  have hQnonneg : 0 <= (Q : Real) := by positivity
  have hMNnat : M * (X / M) <= X := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self X M
  have hMN : (M : Real) * ((X / M : Nat) : Real) <= (X : Real) := by
    exact_mod_cast hMNnat
  have huM : (u : Real) <= 2 * (M : Real) := by
    exact_mod_cast hactive.1.le
  have huN : (u : Real) <= ((X / M : Nat) : Real) := by
    exact_mod_cast hactive.2.le
  have hcore := typeII_sqrt_core_bound hXnonneg hupos hMnonneg hNnonneg hQnonneg
    hMN huM huN
  have hcore' :
      Real.sqrt (((((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
        ((2 * M : Nat) : Real)) *
          ((((X / M : Nat) : Real) + (Q : Real) ^ 2) * ((X / M : Nat) : Real))) <=
        2 * (X : Real) + 3 * ((X : Real) * (Q : Real) / Real.sqrt (u : Real)) +
          2 * (Real.sqrt (X : Real) * (Q : Real) ^ 2) := by
    simpa [typeIISourceCore, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hcore
  have hcutoff : 16 + 4 * Real.log ((X : Real) + 1) <=
      40 * Real.log (X : Real) := by
    simpa using cutoffFactor_le_log_product X 1 1 hX (by norm_num) (by norm_num)
  have hMpos : 0 < M := by omega
  have hlogMX : Real.log (M : Real) <= Real.log (X : Real) := by
    apply Real.log_le_log
    · exact_mod_cast hMpos
    · exact_mod_cast hMX
  have hlogTwoX : Real.log 2 <= Real.log (X : Real) := by
    apply Real.log_le_log
    · norm_num
    · exact_mod_cast hX
  have hlogDouble : Real.log ((2 * M : Nat) : Real) <=
      2 * Real.log (X : Real) := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num : Ne (2 : Real) 0)
      (by exact_mod_cast hMpos.ne' : Ne (M : Real) 0)]
    linarith
  have hlogX : 0 <= Real.log (X : Real) :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num) hX))
  have hsource : 0 <= typeIISourceCore X u Q := by
    unfold typeIISourceCore
    positivity
  rw [typeIIBlockMajorant_eq_core]
  calc
    36 * (16 + 4 * Real.log ((X : Real) + 1)) *
          Real.log ((2 * M : Nat) : Real) *
            Real.sqrt (((((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
              ((2 * M : Nat) : Real)) *
                ((((X / M : Nat) : Real) + (Q : Real) ^ 2) *
                  ((X / M : Nat) : Real))) <=
        36 * (40 * Real.log (X : Real)) *
          (2 * Real.log (X : Real)) * typeIISourceCore X u Q := by
      unfold typeIISourceCore
      gcongr
    _ = 2880 * Real.log (X : Real) ^ 2 * typeIISourceCore X u Q := by ring
theorem dyadicExponentSet_card_le_log (X : Nat) (hX : 2 <= X) :
    ((dyadicExponentSet X).card : Real) <= 4 * Real.log (X : Real) := by
  have hXne : Ne X 0 := by omega
  have hpowNat : 2 ^ Nat.log 2 X <= X := Nat.pow_log_le_self 2 hXne
  have hpow : ((2 : Real) ^ Nat.log 2 X) <= (X : Real) := by
    exact_mod_cast hpowNat
  have hpowPos : 0 < ((2 : Real) ^ Nat.log 2 X) := by positivity
  have hlogPow : Real.log ((2 : Real) ^ Nat.log 2 X) <= Real.log (X : Real) :=
    Real.log_le_log hpowPos hpow
  rw [Real.log_pow] at hlogPow
  have hhalfLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : Real)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlogTwoX : Real.log 2 <= Real.log (X : Real) := by
    apply Real.log_le_log
    · norm_num
    · exact_mod_cast hX
  have hcard : (dyadicExponentSet X).card = Nat.log 2 X + 1 := by
    simp [dyadicExponentSet]
  rw [hcard]
  push_cast
  nlinarith
theorem typeIIDyadicMean_le_sourceScale
    (u X Q : Nat) (hu : 1 <= u) (hX : 2 <= X) (hQ : 1 <= Q) :
    typeIIDyadicMean u u X Q <=
      11520 * Real.log (X : Real) ^ 3 * typeIISourceCore X u Q := by
  have hbase := typeIIDyadicMean_le_sum_activeMajorants u u X Q hu hX hQ
  have hlogX : 0 <= Real.log (X : Real) :=
    Real.log_nonneg (by exact_mod_cast (le_trans (by norm_num) hX))
  have hsource : 0 <= typeIISourceCore X u Q := by
    unfold typeIISourceCore
    positivity
  let C : Real := 2880 * Real.log (X : Real) ^ 2 * typeIISourceCore X u Q
  have hC : 0 <= C := by dsimp [C]; positivity
  calc
    typeIIDyadicMean u u X Q <=
        ∑ k ∈ activeDyadicExponentSet u u X,
          typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := hbase
    _ <= ∑ k ∈ activeDyadicExponentSet u u X, C := by
      apply Finset.sum_le_sum
      intro k hk
      have hkData := Finset.mem_filter.mp hk
      have hkLog : k <= Nat.log 2 X := by
        have := Finset.mem_range.mp hkData.1
        simp only [dyadicExponentSet] at hkData
        omega
      have hpowX : 2 ^ k <= X := by
        calc
          2 ^ k <= 2 ^ Nat.log 2 X := Nat.pow_le_pow_right (by omega) hkLog
          _ <= X := Nat.pow_log_le_self 2 (by omega)
      exact active_typeIIBlockMajorant_le (2 ^ k) X u Q hX hu hpowX hkData.2
    _ = ((activeDyadicExponentSet u u X).card : Real) * C := by simp
    _ <= ((dyadicExponentSet X).card : Real) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ <= (4 * Real.log (X : Real)) * C := by
      exact mul_le_mul_of_nonneg_right (dyadicExponentSet_card_le_log X hX) hC
    _ = 11520 * Real.log (X : Real) ^ 3 * typeIISourceCore X u Q := by
      dsimp [C]
      ring
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators ComplexConjugate
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
noncomputable local instance polyaVinogradovUnitFintype
    (q : Nat) : Fintype (ZMod q)ˣ :=
  Fintype.ofFinite _
def oneIntegerCoefficient (_ : Int) : Complex := 1
theorem norm_intervalAdditiveResidueSum_one_eq_phaseSum
    {q : Nat} [NeZero q] (M : Int) (N : Nat) (u : (ZMod q)ˣ) :
    ‖intervalAdditiveResidueSum oneIntegerCoefficient M N q u‖ =
      ‖phaseSum N (unitFraction u : Real)‖ := by
  have hq : q ∈ Finset.Icc 1 q :=
    Finset.mem_Icc.mpr ⟨NeZero.pos q, le_rfl⟩
  rw [norm_intervalAdditiveResidueSum_eq_fareySample hq
    oneIntegerCoefficient M N u]
  simp [fareyAdditiveSample, shiftedIntervalCoefficients,
    oneIntegerCoefficient, phaseSum, fareyValue]
theorem unitValue_pos {q : Nat} [NeZero q] (hq : 1 < q) (u : (ZMod q)ˣ) :
    0 < u.val.val := by
  have hcoprime := unitFraction_coprime u
  have hne : Ne u.val.val 0 := by
    intro hzero
    have : q = 1 := by simpa [hzero] using hcoprime
    omega
  exact Nat.pos_of_ne_zero hne
theorem unitFraction_ne_zero {q : Nat} [NeZero q]
    (hq : 1 < q) (u : (ZMod q)ˣ) :
    Ne (unitFraction u : Real) 0 := by
  have hnum : Ne (unitFraction u).num 0 := by
    rw [unitFraction_num]
    exact_mod_cast (Nat.ne_of_gt (unitValue_pos hq u))
  have hrat : Ne (unitFraction u) 0 := Rat.num_ne_zero.mp hnum
  exact_mod_cast hrat
theorem norm_phaseSum_unitFraction_le (N : Nat) {q : Nat} [NeZero q]
    (hq : 1 < q) (u : (ZMod q)ˣ) :
    ‖phaseSum N (unitFraction u : Real)‖ <=
      ((q : Real) / 2) *
        (((u.val.val : Real))⁻¹ + ((q - u.val.val : Nat) : Real)⁻¹) := by
  have hqpos : 0 < (q : Real) := by exact_mod_cast (lt_trans Nat.zero_lt_one hq)
  have haposNat : 0 < u.val.val := unitValue_pos hq u
  have hapos : 0 < (u.val.val : Real) := by exact_mod_cast haposNat
  have haltNat : u.val.val < q := ZMod.val_lt u.val
  have haleNat : u.val.val <= q := haltNat.le
  have hbposNat : 0 < q - u.val.val := Nat.sub_pos_of_lt haltNat
  have hbpos : 0 < ((q - u.val.val : Nat) : Real) := by exact_mod_cast hbposNat
  have hfrac : (unitFraction u : Real) = (u.val.val : Real) / (q : Real) := by
    unfold unitFraction
    push_cast
    rfl
  have hfracPos : 0 < (unitFraction u : Real) := by rw [hfrac]; positivity
  have hfracLt : (unitFraction u : Real) < 1 := by
    rw [hfrac, div_lt_one hqpos]
    exact_mod_cast haltNat
  have hbase := norm_phaseSum_le_phaseDistance (N := N)
    hfracPos.ne' (by rw [abs_of_pos hfracPos]; exact hfracLt)
  apply hbase.trans
  rw [phaseDistance, abs_of_pos hfracPos]
  by_cases hside : (unitFraction u : Real) <= 1 - (unitFraction u : Real)
  · rw [min_eq_left hside, hfrac]
    have hidentity : 1 / (2 * ((u.val.val : Real) / (q : Real))) =
        ((q : Real) / 2) * (u.val.val : Real)⁻¹ := by
      field_simp [hqpos.ne', hapos.ne']
    rw [hidentity]
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_right (inv_nonneg.mpr hbpos.le)) (by positivity)
  · rw [min_eq_right (le_of_not_ge hside), hfrac]
    have hcomplement : 1 - (u.val.val : Real) / (q : Real) =
        ((q - u.val.val : Nat) : Real) / (q : Real) := by
      rw [Nat.cast_sub haleNat]
      field_simp [hqpos.ne']
    rw [hcomplement]
    have hidentity : 1 / (2 * (((q - u.val.val : Nat) : Real) / (q : Real))) =
        ((q : Real) / 2) * ((q - u.val.val : Nat) : Real)⁻¹ := by
      field_simp [hqpos.ne', hbpos.ne']
    rw [hidentity]
    exact mul_le_mul_of_nonneg_left
      (le_add_of_nonneg_left (inv_nonneg.mpr hapos.le)) (by positivity)
def phaseReciprocalWeight (q a : Nat) : Real :=
  ((q : Real) / 2) * (((a : Real))⁻¹ + ((q - a : Nat) : Real)⁻¹)
def unitValues (q : Nat) : Finset Nat :=
  Finset.univ.image fun u : (ZMod q)ˣ => u.val.val
theorem unitValues_subset_Ico {q : Nat} [NeZero q] (hq : 1 < q) :
    unitValues q ⊆ Ico 1 q := by
  intro a ha
  rw [unitValues] at ha
  rcases Finset.mem_image.mp ha with ⟨u, hu, rfl⟩
  exact Finset.mem_Ico.mpr ⟨unitValue_pos hq u, ZMod.val_lt u.val⟩
theorem sum_unit_phaseReciprocalWeight_eq {q : Nat} [NeZero q] :
    ∑ u : (ZMod q)ˣ, phaseReciprocalWeight q u.val.val =
      ∑ a ∈ unitValues q, phaseReciprocalWeight q a := by
  rw [unitValues]
  symm
  apply Finset.sum_image
  intro u hu v hv huv
  apply Units.ext
  exact ZMod.val_injective q huv
theorem sum_phaseReciprocalWeight_Ico (q : Nat) (hq : 1 <= q) :
    ∑ a ∈ Ico 1 q, phaseReciprocalWeight q a =
      (q : Real) * (harmonic (q - 1) : Real) := by
  have hreflect :
      (∑ a ∈ Ico 1 q, ((q - a : Nat) : Real)⁻¹) =
        ∑ a ∈ Ico 1 q, (a : Real)⁻¹ := by
    simpa using
      (Finset.sum_Ico_reflect (fun a : Nat => (a : Real)⁻¹) 1
        (m := q) (n := q) (by omega))
  have hinterval : Ico 1 q = Icc 1 (q - 1) := by
    ext a
    simp only [Finset.mem_Ico, Finset.mem_Icc]
    omega
  have hharmonic :
      (∑ a ∈ Ico 1 q, (a : Real)⁻¹) =
        (harmonic (q - 1) : Real) := by
    rw [hinterval, harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  unfold phaseReciprocalWeight
  rw [← Finset.mul_sum]
  rw [Finset.sum_add_distrib]
  rw [hreflect, hharmonic]
  ring
theorem sum_unit_phaseSum_le_q_harmonic (M : Int) (N : Nat)
    {q : Nat} [NeZero q] (hq : 1 < q) :
    ∑ u : (ZMod q)ˣ,
        ‖intervalAdditiveResidueSum oneIntegerCoefficient M N q u‖ <=
      (q : Real) * (harmonic (q - 1) : Real) := by
  calc
    (∑ u : (ZMod q)ˣ,
        ‖intervalAdditiveResidueSum oneIntegerCoefficient M N q u‖) =
        ∑ u : (ZMod q)ˣ, ‖phaseSum N (unitFraction u : Real)‖ := by
      apply Finset.sum_congr rfl
      intro u hu
      exact norm_intervalAdditiveResidueSum_one_eq_phaseSum M N u
    _ <= ∑ u : (ZMod q)ˣ, phaseReciprocalWeight q u.val.val := by
      apply Finset.sum_le_sum
      intro u hu
      exact norm_phaseSum_unitFraction_le N hq u
    _ = ∑ a ∈ unitValues q, phaseReciprocalWeight q a :=
      sum_unit_phaseReciprocalWeight_eq
    _ <= ∑ a ∈ Ico 1 q, phaseReciprocalWeight q a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (unitValues_subset_Ico hq)
      intro a haIco haUnits
      unfold phaseReciprocalWeight
      positivity
    _ = (q : Real) * (harmonic (q - 1) : Real) :=
      sum_phaseReciprocalWeight_Ico q hq.le
theorem harmonic_sub_one_le_two_log (q : Nat) (hq : 1 < q) :
    (harmonic (q - 1) : Real) <= 2 * Real.log (2 * (q : Real)) := by
  have hq1 : 1 <= q := hq.le
  have hsubposNat : 0 < q - 1 := Nat.sub_pos_of_lt hq
  have hsubpos : 0 < ((q - 1 : Nat) : Real) := by exact_mod_cast hsubposNat
  have hsuble : ((q - 1 : Nat) : Real) <= (q : Real) := by
    exact_mod_cast Nat.sub_le q 1
  have hlogSub : Real.log ((q - 1 : Nat) : Real) <= Real.log (q : Real) :=
    Real.log_le_log hsubpos hsuble
  have hlogq : 0 <= Real.log (q : Real) := Real.log_nonneg (by exact_mod_cast hq1)
  have hhalfLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : Real)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlogProduct : Real.log (2 * (q : Real)) =
      Real.log 2 + Real.log (q : Real) := by
    rw [Real.log_mul (by norm_num : Ne (2 : Real) 0)]
    exact_mod_cast (Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq))
  calc
    (harmonic (q - 1) : Real) <= 1 + Real.log ((q - 1 : Nat) : Real) :=
      harmonic_le_one_add_log (q - 1)
    _ <= 2 * Real.log (2 * (q : Real)) := by
      rw [hlogProduct]
      linarith
theorem sum_unit_phaseSum_le_log (M : Int) (N : Nat)
    {q : Nat} [NeZero q] (hq : 1 < q) :
    ∑ u : (ZMod q)ˣ,
        ‖intervalAdditiveResidueSum oneIntegerCoefficient M N q u‖ <=
      2 * (q : Real) * Real.log (2 * (q : Real)) := by
  calc
    _ <= (q : Real) * (harmonic (q - 1) : Real) :=
      sum_unit_phaseSum_le_q_harmonic M N hq
    _ <= (q : Real) * (2 * Real.log (2 * (q : Real))) := by
      exact mul_le_mul_of_nonneg_left (harmonic_sub_one_le_two_log q hq) (by positivity)
    _ = 2 * (q : Real) * Real.log (2 * (q : Real)) := by ring
theorem norm_unitCharacterSum_intervalOne_le_log (M : Int) (N : Nat)
    {q : Nat} [NeZero q] (hq : 1 < q)
    (chi : DirichletCharacter Complex q) :
    ‖unitCharacterSum
        (intervalAdditiveResidueSum oneIntegerCoefficient M N q) chi‖ <=
      2 * (q : Real) * Real.log (2 * (q : Real)) := by
  unfold unitCharacterSum
  calc
    ‖∑ u : (ZMod q)ˣ,
        intervalAdditiveResidueSum oneIntegerCoefficient M N q u *
          chi (u : ZMod q)‖ <=
        ∑ u : (ZMod q)ˣ,
          ‖intervalAdditiveResidueSum oneIntegerCoefficient M N q u *
            chi (u : ZMod q)‖ := norm_sum_le _ _
    _ = ∑ u : (ZMod q)ˣ,
        ‖intervalAdditiveResidueSum oneIntegerCoefficient M N q u‖ := by
      apply Finset.sum_congr rfl
      intro u hu
      rw [norm_mul, DirichletCharacter.unit_norm_eq_one, mul_one]
    _ <= _ := sum_unit_phaseSum_le_log M N hq
theorem polyaVinogradov {q : Nat} [NeZero q] (hq : 1 < q)
    {chi : DirichletCharacter Complex q}
    (hchi : DirichletCharacter.IsPrimitive chi) (M : Int) (N : Nat) :
    ‖intervalCharacterSum oneIntegerCoefficient M N q chi‖ <=
      2 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) := by
  have hchiInv : DirichletCharacter.IsPrimitive chi⁻¹ := by
    rw [DirichletCharacter.isPrimitive_def, DirichletCharacter.conductor_inv]
    exact hchi
  have hqnonneg : 0 <= (q : Real) := by positivity
  have hsqrtPos : 0 < Real.sqrt (q : Real) := Real.sqrt_pos.2 (by
    exact_mod_cast (lt_trans Nat.zero_lt_one hq))
  have hgauss : ‖gaussSum chi⁻¹ ZMod.stdAddChar‖ = Real.sqrt (q : Real) := by
    have hsq := norm_gaussSum_stdAddChar_sq hchiInv
    nlinarith [Real.sq_sqrt hqnonneg, norm_nonneg (gaussSum chi⁻¹ ZMod.stdAddChar),
      Real.sqrt_nonneg (q : Real)]
  have hinversion := congrArg norm
    (gauss_mul_intervalCharacterSum hchi oneIntegerCoefficient M N)
  rw [norm_mul, hgauss] at hinversion
  have hunit := norm_unitCharacterSum_intervalOne_le_log M N hq chi⁻¹
  have hscaled :
      Real.sqrt (q : Real) *
          ‖intervalCharacterSum oneIntegerCoefficient M N q chi‖ <=
        Real.sqrt (q : Real) *
          (2 * Real.sqrt (q : Real) * Real.log (2 * (q : Real))) := by
    calc
      _ = ‖unitCharacterSum
          (intervalAdditiveResidueSum oneIntegerCoefficient M N q) chi⁻¹‖ := hinversion
      _ <= 2 * (q : Real) * Real.log (2 * (q : Real)) := hunit
      _ = Real.sqrt (q : Real) *
          (2 * Real.sqrt (q : Real) * Real.log (2 * (q : Real))) := by
        let L : Real := Real.log (2 * (q : Real))
        change 2 * (q : Real) * L =
          Real.sqrt (q : Real) * (2 * Real.sqrt (q : Real) * L)
        calc
          2 * (q : Real) * L =
              2 * (Real.sqrt (q : Real) * Real.sqrt (q : Real)) * L := by
            rw [Real.mul_self_sqrt hqnonneg]
          _ = _ := by ring
  exact (mul_le_mul_iff_of_pos_left hsqrtPos).mp hscaled
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
def logWeightedCharacterPrefix (L q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ n ∈ Icc 1 L, (Real.log (n : Real) : Complex) * chi (n : ZMod q)
theorem intervalCharacterSum_one_eq_sum_range (N q : Nat)
    (chi : DirichletCharacter Complex q) :
    intervalCharacterSum oneIntegerCoefficient 0 N q chi =
      ∑ i ∈ range N, chi ((i + 1 : Nat) : ZMod q) := by
  calc
    intervalCharacterSum oneIntegerCoefficient 0 N q chi =
        positiveCharacterSum (fun _ : Nat => (1 : Complex)) N q chi := by
      rfl
    _ = ∑ n ∈ Icc 1 N, chi (n : ZMod q) := by
      rw [positiveCharacterSum_eq_sum_nat]
      simp
    _ = ∑ i ∈ range N, chi ((i + 1 : Nat) : ZMod q) := by
      apply Finset.sum_bij (fun n _ => n - 1)
      · intro n hn
        simp only [Finset.mem_Icc] at hn
        simp only [Finset.mem_range]
        omega
      · intro n₁ hn₁ n₂ hn₂ heq
        simp only [Finset.mem_Icc] at hn₁ hn₂
        omega
      · intro i hi
        refine ⟨i + 1, ?_, ?_⟩
        · simp only [Finset.mem_Icc, Nat.one_le_iff_ne_zero, ne_eq]
          constructor
          · omega
          · exact Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
        · omega
      · intro n hn
        simp only [Finset.mem_Icc] at hn
        congr 2
        omega
theorem logWeightedCharacterPrefix_eq_sum_range (L q : Nat)
    (chi : DirichletCharacter Complex q) :
    logWeightedCharacterPrefix L q chi =
      ∑ i ∈ range L,
        (Real.log ((i + 1 : Nat) : Real) : Complex) *
          chi ((i + 1 : Nat) : ZMod q) := by
  unfold logWeightedCharacterPrefix
  apply Finset.sum_bij (fun n _ => n - 1)
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    simp only [Finset.mem_range]
    omega
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_Icc] at hn₁ hn₂
    omega
  · intro i hi
    have hil : i < L := Finset.mem_range.mp hi
    refine ⟨i + 1, ?_, ?_⟩
    · simp only [Finset.mem_Icc]
      omega
    · omega
  · intro n hn
    simp only [Finset.mem_Icc] at hn
    have hback : n - 1 + 1 = n := Nat.sub_add_cancel hn.1
    rw [hback]
theorem logWeightedCharacterPrefix_by_parts (L q : Nat)
    (chi : DirichletCharacter Complex q) :
    logWeightedCharacterPrefix L q chi =
      (Real.log (L : Real) : Complex) *
          intervalCharacterSum oneIntegerCoefficient 0 L q chi -
        ∑ i ∈ range (L - 1),
          (Real.log ((i + 2 : Nat) : Real) -
              Real.log ((i + 1 : Nat) : Real) : Real) •
            intervalCharacterSum oneIntegerCoefficient 0 (i + 1) q chi := by
  by_cases hL : L = 0
  · simp [hL, logWeightedCharacterPrefix, intervalCharacterSum]
  rw [logWeightedCharacterPrefix_eq_sum_range]
  change (∑ i ∈ range L,
      Real.log ((i + 1 : Nat) : Real) • chi ((i + 1 : Nat) : ZMod q)) = _
  change _ = Real.log (L : Real) •
      intervalCharacterSum oneIntegerCoefficient 0 L q chi - _
  have hparts := Finset.sum_range_by_parts
    (fun i : Nat => Real.log ((i + 1 : Nat) : Real))
    (fun i : Nat => chi ((i + 1 : Nat) : ZMod q)) L
  rw [hparts]
  simp_rw [← intervalCharacterSum_one_eq_sum_range]
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL
  rw [Nat.sub_add_cancel hLpos]
theorem sum_log_successive_differences (K : Nat) :
    ∑ i ∈ range K,
        (Real.log ((i + 2 : Nat) : Real) -
          Real.log ((i + 1 : Nat) : Real)) =
      Real.log ((K + 1 : Nat) : Real) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
      rw [Finset.sum_range_succ, ih]
      ring
theorem log_successive_difference_nonneg (i : Nat) :
    0 <= Real.log ((i + 2 : Nat) : Real) -
      Real.log ((i + 1 : Nat) : Real) := by
  apply sub_nonneg.mpr
  apply Real.log_le_log
  · positivity
  · exact_mod_cast (show i + 1 <= i + 2 by omega)
theorem norm_logWeightedCharacterPrefix_le_of_prefix_bound
    (L q : Nat) (chi : DirichletCharacter Complex q) (B : Real)
    (hB : 0 <= B)
    (hprefix : ∀ k, k <= L ->
      ‖intervalCharacterSum oneIntegerCoefficient 0 k q chi‖ <= B) :
    ‖logWeightedCharacterPrefix L q chi‖ <=
      2 * B * Real.log ((L + 1 : Nat) : Real) := by
  by_cases hL : L = 0
  · simp [hL, logWeightedCharacterPrefix]
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL
  have hlogL : 0 <= Real.log (L : Real) := Real.log_natCast_nonneg L
  have hmain :
      ‖logWeightedCharacterPrefix L q chi‖ <=
        Real.log (L : Real) * B + Real.log (L : Real) * B := by
    rw [logWeightedCharacterPrefix_by_parts]
    calc
      ‖(Real.log (L : Real) : Complex) *
            intervalCharacterSum oneIntegerCoefficient 0 L q chi -
          ∑ i ∈ range (L - 1),
            (Real.log ((i + 2 : Nat) : Real) -
                Real.log ((i + 1 : Nat) : Real) : Real) •
              intervalCharacterSum oneIntegerCoefficient 0 (i + 1) q chi‖ <=
          ‖(Real.log (L : Real) : Complex) *
              intervalCharacterSum oneIntegerCoefficient 0 L q chi‖ +
            ‖∑ i ∈ range (L - 1),
              (Real.log ((i + 2 : Nat) : Real) -
                  Real.log ((i + 1 : Nat) : Real) : Real) •
                intervalCharacterSum oneIntegerCoefficient 0 (i + 1) q chi‖ :=
        norm_sub_le _ _
      _ <= Real.log (L : Real) * B +
          ∑ i ∈ range (L - 1),
            (Real.log ((i + 2 : Nat) : Real) -
              Real.log ((i + 1 : Nat) : Real)) * B := by
        apply add_le_add
        · rw [norm_mul]
          simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogL]
          exact mul_le_mul_of_nonneg_left (hprefix L le_rfl) hlogL
        · calc
            ‖∑ i ∈ range (L - 1),
                (Real.log ((i + 2 : Nat) : Real) -
                    Real.log ((i + 1 : Nat) : Real) : Real) •
                  intervalCharacterSum oneIntegerCoefficient 0 (i + 1) q chi‖ <=
                ∑ i ∈ range (L - 1),
                  ‖(Real.log ((i + 2 : Nat) : Real) -
                      Real.log ((i + 1 : Nat) : Real) : Real) •
                    intervalCharacterSum oneIntegerCoefficient 0 (i + 1) q chi‖ :=
              norm_sum_le _ _
            _ <= ∑ i ∈ range (L - 1),
                (Real.log ((i + 2 : Nat) : Real) -
                  Real.log ((i + 1 : Nat) : Real)) * B := by
              apply Finset.sum_le_sum
              intro i hi
              have hiL : i + 1 <= L := by
                have hirange := Finset.mem_range.mp hi
                omega
              rw [norm_smul, Real.norm_eq_abs,
                abs_of_nonneg (log_successive_difference_nonneg i)]
              exact mul_le_mul_of_nonneg_left (hprefix (i + 1) hiL)
                (log_successive_difference_nonneg i)
      _ = Real.log (L : Real) * B + Real.log (L : Real) * B := by
        rw [← Finset.sum_mul, sum_log_successive_differences]
        rw [Nat.sub_add_cancel hLpos]
  have hlogMono : Real.log (L : Real) <=
      Real.log ((L + 1 : Nat) : Real) := by
    apply Real.log_le_log
    · exact_mod_cast hLpos
    · exact_mod_cast (show L <= L + 1 by omega)
  calc
    ‖logWeightedCharacterPrefix L q chi‖ <=
        Real.log (L : Real) * B + Real.log (L : Real) * B := hmain
    _ = 2 * B * Real.log (L : Real) := by ring
    _ <= 2 * B * Real.log ((L + 1 : Nat) : Real) := by
      exact mul_le_mul_of_nonneg_left hlogMono (by positivity)
theorem norm_logWeightedCharacterPrefix_le {q : Nat} [NeZero q]
    (hq : 1 < q) {chi : DirichletCharacter Complex q}
    (hchi : DirichletCharacter.IsPrimitive chi) (L : Nat) :
    ‖logWeightedCharacterPrefix L q chi‖ <=
      4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
        Real.log ((L + 1 : Nat) : Real) := by
  have hlogq : 0 <= Real.log (2 * (q : Real)) := by
    apply Real.log_nonneg
    have : (1 : Real) <= (q : Real) := by exact_mod_cast hq.le
    linarith
  have hbound := norm_logWeightedCharacterPrefix_le_of_prefix_bound
    L q chi (2 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)))
    (by positivity) (fun k hk => polyaVinogradov hq hchi 0 k)
  convert hbound using 1
  all_goals ring
theorem norm_logWeightedCharacterPrefix_trivial (L q : Nat)
    (chi : DirichletCharacter Complex q) :
    ‖logWeightedCharacterPrefix L q chi‖ <=
      (L : Real) * Real.log ((L + 1 : Nat) : Real) := by
  unfold logWeightedCharacterPrefix
  calc
    ‖∑ n ∈ Icc 1 L,
        (Real.log (n : Real) : Complex) * chi (n : ZMod q)‖ <=
        ∑ n ∈ Icc 1 L,
          ‖(Real.log (n : Real) : Complex) * chi (n : ZMod q)‖ :=
      norm_sum_le _ _
    _ <= ∑ n ∈ Icc 1 L,
        Real.log ((L + 1 : Nat) : Real) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnBounds := Finset.mem_Icc.mp hn
      have hlogn : 0 <= Real.log (n : Real) := Real.log_natCast_nonneg n
      have hlog : Real.log (n : Real) <=
          Real.log ((L + 1 : Nat) : Real) := by
        apply Real.log_le_log
        · exact_mod_cast (show 0 < n by omega)
        · exact_mod_cast (show n <= L + 1 by omega)
      calc
        ‖(Real.log (n : Real) : Complex) * chi (n : ZMod q)‖ =
            Real.log (n : Real) * ‖chi (n : ZMod q)‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlogn]
        _ <= Real.log (n : Real) * 1 := by
          exact mul_le_mul_of_nonneg_left
            (DirichletCharacter.norm_le_one chi (n : ZMod q)) hlogn
        _ <= Real.log ((L + 1 : Nat) : Real) := by simpa using hlog
    _ = (L : Real) * Real.log ((L + 1 : Nat) : Real) := by simp
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
open BombieriVinogradov.VaughanIdentity
def typeIOneCharacterSum (v y q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ m ∈ Icc 1 y,
    if m <= v then
      (((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
        chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi
    else 0
theorem vaughanS1_eq_typeIOneCharacterSum (v y q : Nat)
    (chi : DirichletCharacter Complex q) :
    vaughanS1 v y (fun n => chi (n : ZMod q)) =
      typeIOneCharacterSum v y q chi := by
  unfold vaughanS1 weightedKernelSum
  simp_rw [typeI1Kernel_apply]
  push_cast
  simp_rw [Finset.sum_mul]
  have hreindex :
      (∑ n ∈ Icc 1 y, ∑ pair ∈ Nat.divisorsAntidiagonal n,
        (((if pair.1 <= v then
            ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.1 : Real)
          else 0) : Real) : Complex) * Complex.log (pair.2 : Complex) * chi (n : ZMod q)) =
        ∑ n ∈ Icc 1 y, ∑ pair ∈ Nat.divisorsAntidiagonal n,
          (((if pair.1 <= v then
              ((ArithmeticFunction.moebius : ArithmeticFunction Real) pair.1 : Real)
            else 0) : Real) : Complex) * Complex.log (pair.2 : Complex) *
              chi ((pair.1 * pair.2 : Nat) : ZMod q) := by
    apply Finset.sum_congr rfl
    intro n hn
    apply Finset.sum_congr rfl
    intro pair hp
    rw [(Nat.mem_divisorsAntidiagonal.mp hp).1]
  rw [hreindex]
  have hhyper := sum_divisorsAntidiagonal_Icc_eq_hyperbola
    (fun m k =>
      ((((if m <= v then
          ((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real)
        else 0) : Real) : Complex) * Complex.log (k : Complex) *
          chi ((m * k : Nat) : ZMod q))) y
  rw [hhyper]
  unfold typeIOneCharacterSum
  apply Finset.sum_congr rfl
  intro m hm
  by_cases hmv : m <= v
  · simp only [hmv, if_true]
    unfold logWeightedCharacterPrefix
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hchiMul : chi ((m * k : Nat) : ZMod q) =
        chi (m : ZMod q) * chi (k : ZMod q) := by
      rw [Nat.cast_mul, map_mul]
    rw [hchiMul, ← Complex.natCast_log]
    ring
  · simp [hmv]
theorem norm_realMoebius_le_one (m : Nat) :
    ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex)‖ <= 1 := by
  rcases ArithmeticFunction.moebius_eq_or m with hzero | hone | hneg
  · simp [hzero]
  · simp [hone]
  · simp [hneg]
theorem norm_typeIOneCharacterSum_le {q : Nat} [NeZero q]
    (hq : 1 < q) {chi : DirichletCharacter Complex q}
    (hchi : DirichletCharacter.IsPrimitive chi) (v y : Nat) :
    ‖typeIOneCharacterSum v y q chi‖ <=
      (v : Real) *
        (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
          Real.log ((y + 1 : Nat) : Real)) := by
  let C : Real :=
    4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
      Real.log ((y + 1 : Nat) : Real)
  have hlogq : 0 <= Real.log (2 * (q : Real)) := by
    apply Real.log_nonneg
    have : (1 : Real) <= (q : Real) := by exact_mod_cast hq.le
    linarith
  have hlogy : 0 <= Real.log ((y + 1 : Nat) : Real) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 <= y + 1 by omega)
  have hfront : 0 <=
      4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) := by
    positivity
  have hC : 0 <= C := by
    dsimp [C]
    exact mul_nonneg hfront hlogy
  let active : Finset Nat := (Icc 1 y).filter fun m => m <= v
  have hrewrite : typeIOneCharacterSum v y q chi =
      ∑ m ∈ active,
        (((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi := by
    unfold typeIOneCharacterSum active
    rw [Finset.sum_filter]
  have hterm : ∀ m ∈ active,
      ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ <= C := by
    intro m hm
    have hprefix : ‖logWeightedCharacterPrefix (y / m) q chi‖ <= C := by
      calc
        ‖logWeightedCharacterPrefix (y / m) q chi‖ <=
            4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
              Real.log (((y / m) + 1 : Nat) : Real) :=
          norm_logWeightedCharacterPrefix_le hq hchi (y / m)
        _ <= C := by
          dsimp [C]
          have hnat : y / m + 1 <= y + 1 :=
            Nat.add_le_add_right (Nat.div_le_self y m) 1
          have hlog : Real.log (((y / m) + 1 : Nat) : Real) <=
              Real.log ((y + 1 : Nat) : Real) := by
            apply Real.log_le_log
            · positivity
            · exact_mod_cast hnat
          exact mul_le_mul_of_nonneg_left hlog hfront
    calc
      ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ =
          ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex)‖ *
            ‖chi (m : ZMod q)‖ *
              ‖logWeightedCharacterPrefix (y / m) q chi‖ := by
        rw [norm_mul, norm_mul]
      _ <= 1 * 1 * C := by
        gcongr
        · exact norm_realMoebius_le_one m
        · exact DirichletCharacter.norm_le_one chi (m : ZMod q)
      _ = C := by ring
  have hactive : active ⊆ Icc 1 v := by
    intro m hm
    simp only [active, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
    exact ⟨hm.1.1, hm.2⟩
  have hcardNat : active.card <= v := by
    have := Finset.card_le_card hactive
    simpa using this
  have hcard : (active.card : Real) <= (v : Real) := by exact_mod_cast hcardNat
  rw [hrewrite]
  calc
    ‖∑ m ∈ active,
        (((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ <=
        ∑ m ∈ active,
          ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
            chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ :=
      norm_sum_le _ _
    _ <= ∑ m ∈ active, C := by
      exact Finset.sum_le_sum hterm
    _ = (active.card : Real) * C := by simp
    _ <= (v : Real) * C := mul_le_mul_of_nonneg_right hcard hC
    _ = (v : Real) *
        (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
          Real.log ((y + 1 : Nat) : Real)) := by rfl
theorem harmonic_le_three_log_add_one (y : Nat) :
    (harmonic y : Real) <= 3 * Real.log ((y + 1 : Nat) : Real) := by
  by_cases hy : y = 0
  · simp [hy]
  have hypos : 0 < y := Nat.pos_of_ne_zero hy
  have hlogMono : Real.log (y : Real) <=
      Real.log ((y + 1 : Nat) : Real) := by
    apply Real.log_le_log
    · exact_mod_cast hypos
    · exact_mod_cast (show y <= y + 1 by omega)
  have hhalfLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : Real)) (by norm_num)
    norm_num at h ⊢
    linarith
  have hlogTwo : Real.log 2 <= Real.log ((y + 1 : Nat) : Real) := by
    apply Real.log_le_log
    · norm_num
    · exact_mod_cast (show 2 <= y + 1 by omega)
  calc
    (harmonic y : Real) <= 1 + Real.log (y : Real) :=
      harmonic_le_one_add_log y
    _ <= 3 * Real.log ((y + 1 : Nat) : Real) := by linarith
theorem norm_typeIOneCharacterSum_trivial (v y q : Nat)
    (chi : DirichletCharacter Complex q) :
    ‖typeIOneCharacterSum v y q chi‖ <=
      3 * (y : Real) * Real.log ((y + 1 : Nat) : Real) ^ 2 := by
  let active : Finset Nat := (Icc 1 y).filter fun m => m <= v
  have hrewrite : typeIOneCharacterSum v y q chi =
      ∑ m ∈ active,
        (((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi := by
    unfold typeIOneCharacterSum active
    rw [Finset.sum_filter]
  have hlogy : 0 <= Real.log ((y + 1 : Nat) : Real) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 <= y + 1 by omega)
  have hterm : ∀ m ∈ active,
      ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ <=
        (y : Real) * (m : Real)⁻¹ * Real.log ((y + 1 : Nat) : Real) := by
    intro m hm
    have hmActive := Finset.mem_filter.mp hm
    have hmpos : 0 < m := (Finset.mem_Icc.mp hmActive.1).1
    have hprefix : ‖logWeightedCharacterPrefix (y / m) q chi‖ <=
        (y : Real) * (m : Real)⁻¹ * Real.log ((y + 1 : Nat) : Real) := by
      have hfloor : ((y / m : Nat) : Real) <= (y : Real) / (m : Real) :=
        Nat.cast_div_le
      have hnat : y / m + 1 <= y + 1 :=
        Nat.add_le_add_right (Nat.div_le_self y m) 1
      have hlog : Real.log (((y / m) + 1 : Nat) : Real) <=
          Real.log ((y + 1 : Nat) : Real) := by
        apply Real.log_le_log
        · positivity
        · exact_mod_cast hnat
      calc
        ‖logWeightedCharacterPrefix (y / m) q chi‖ <=
            ((y / m : Nat) : Real) *
              Real.log (((y / m) + 1 : Nat) : Real) :=
          norm_logWeightedCharacterPrefix_trivial (y / m) q chi
        _ <= ((y : Real) / (m : Real)) *
              Real.log (((y / m) + 1 : Nat) : Real) :=
          mul_le_mul_of_nonneg_right hfloor (Real.log_natCast_nonneg _)
        _ <= ((y : Real) / (m : Real)) *
              Real.log ((y + 1 : Nat) : Real) := by
          exact mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = (y : Real) * (m : Real)⁻¹ *
              Real.log ((y + 1 : Nat) : Real) := by
          rw [div_eq_mul_inv]
    calc
      ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ =
          ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex)‖ *
            ‖chi (m : ZMod q)‖ *
              ‖logWeightedCharacterPrefix (y / m) q chi‖ := by
        rw [norm_mul, norm_mul]
      _ <= 1 * 1 *
          ((y : Real) * (m : Real)⁻¹ * Real.log ((y + 1 : Nat) : Real)) := by
        gcongr
        · exact norm_realMoebius_le_one m
        · exact DirichletCharacter.norm_le_one chi (m : ZMod q)
      _ = (y : Real) * (m : Real)⁻¹ *
          Real.log ((y + 1 : Nat) : Real) := by ring
  have hactive : active ⊆ Icc 1 y := by
    exact fun m hm => (Finset.mem_filter.mp hm).1
  have hharmonic :
      ∑ m ∈ Icc 1 y, (m : Real)⁻¹ = (harmonic y : Real) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [hrewrite]
  calc
    ‖∑ m ∈ active,
        (((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
          chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ <=
        ∑ m ∈ active,
          ‖(((ArithmeticFunction.moebius : ArithmeticFunction Real) m : Real) : Complex) *
            chi (m : ZMod q) * logWeightedCharacterPrefix (y / m) q chi‖ :=
      norm_sum_le _ _
    _ <= ∑ m ∈ active,
        (y : Real) * (m : Real)⁻¹ *
          Real.log ((y + 1 : Nat) : Real) := Finset.sum_le_sum hterm
    _ <= ∑ m ∈ Icc 1 y,
        (y : Real) * (m : Real)⁻¹ *
          Real.log ((y + 1 : Nat) : Real) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hactive
      intro m hmAll hmActive
      positivity
    _ = (y : Real) * (harmonic y : Real) *
        Real.log ((y + 1 : Nat) : Real) := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.sum_mul, hharmonic]
    _ <= (y : Real) *
        (3 * Real.log ((y + 1 : Nat) : Real)) *
          Real.log ((y + 1 : Nat) : Real) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (harmonic_le_three_log_add_one y) (by positivity)) hlogy
    _ = 3 * (y : Real) * Real.log ((y + 1 : Nat) : Real) ^ 2 := by ring
theorem primitiveCharacters_card_le_totient (q : Nat) [NeZero q] :
    (primitiveCharacters q).card <= q.totient := by
  calc
    (primitiveCharacters q).card <=
        (Finset.univ : Finset (DirichletCharacter Complex q)).card :=
      Finset.card_le_card (Finset.subset_univ _)
    _ = q.totient := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity Complex q
theorem weighted_primitive_typeIOne_le {q : Nat} [NeZero q]
    (hq : 1 < q) (v y : Nat) :
    ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖ <=
      (q : Real) * (v : Real) *
        (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
          Real.log ((y + 1 : Nat) : Real)) := by
  classical
  let B : Real := (v : Real) *
    (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
      Real.log ((y + 1 : Nat) : Real))
  have hB : 0 <= B := by
    dsimp [B]
    have hlogq : 0 <= Real.log (2 * (q : Real)) := by
      apply Real.log_nonneg
      have : (1 : Real) <= (q : Real) := by exact_mod_cast hq.le
      linarith
    have hlogy : 0 <= Real.log ((y + 1 : Nat) : Real) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 <= y + 1 by omega)
    positivity
  have hchars :
      ∑ chi ∈ primitiveCharacters q,
          ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖ <=
        (q.totient : Real) * B := by
    calc
      ∑ chi ∈ primitiveCharacters q,
          ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖ <=
          ∑ chi ∈ primitiveCharacters q, B := by
        apply Finset.sum_le_sum
        intro chi hchiMem
        have hchi : DirichletCharacter.IsPrimitive chi := by
          simpa [primitiveCharacters] using (Finset.mem_filter.mp hchiMem).2
        rw [vaughanS1_eq_typeIOneCharacterSum]
        exact norm_typeIOneCharacterSum_le hq hchi v y
      _ = ((primitiveCharacters q).card : Real) * B := by simp
      _ <= (q.totient : Real) * B := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast primitiveCharacters_card_le_totient q) hB
  have hphi : 0 < (q.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  calc
    ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖ <=
        ((q : Real) / (q.totient : Real)) *
          ((q.totient : Real) * B) := by
      exact mul_le_mul_of_nonneg_left hchars (by positivity)
    _ = (q : Real) * B := by field_simp
    _ = (q : Real) * (v : Real) *
        (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
          Real.log ((y + 1 : Nat) : Real)) := by
      dsimp [B]
      ring
def nontrivialTypeIOneMean (v y Q : Nat) : Real :=
  ∑ q ∈ Icc 2 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q,
      ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖
theorem nontrivialTypeIOneMean_le (v y Q : Nat) :
    nontrivialTypeIOneMean v y Q <=
      4 * (v : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
        Real.log (2 * (Q : Real)) * Real.log ((y + 1 : Nat) : Real) := by
  let D : Real := (Q : Real) * (v : Real) *
    (4 * Real.sqrt (Q : Real) * Real.log (2 * (Q : Real)) *
      Real.log ((y + 1 : Nat) : Real))
  have hlogQ : 0 <= Real.log (2 * (Q : Real)) := by
    by_cases hQ : Q = 0
    · simp [hQ]
    · apply Real.log_nonneg
      have : (1 : Real) <= (Q : Real) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
      linarith
  have hlogy : 0 <= Real.log ((y + 1 : Nat) : Real) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 <= y + 1 by omega)
  have hD : 0 <= D := by
    dsimp [D]
    positivity
  have hterm : ∀ q ∈ Icc 2 Q,
      ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q,
            ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖ <= D := by
    intro q hqMem
    have hqBounds := Finset.mem_Icc.mp hqMem
    let _ : NeZero q := ⟨(Nat.zero_lt_of_lt hqBounds.1).ne'⟩
    have hbase := weighted_primitive_typeIOne_le
      (show 1 < q by omega) v y
    apply hbase.trans
    dsimp [D]
    have hqcast : (q : Real) <= (Q : Real) := by exact_mod_cast hqBounds.2
    have hsqrt : Real.sqrt (q : Real) <= Real.sqrt (Q : Real) :=
      Real.sqrt_le_sqrt hqcast
    have hlog : Real.log (2 * (q : Real)) <=
        Real.log (2 * (Q : Real)) := by
      apply Real.log_le_log
      · have : (0 : Real) < (q : Real) := by exact_mod_cast NeZero.pos q
        positivity
      · nlinarith
    have hlogq : 0 <= Real.log (2 * (q : Real)) := by
      apply Real.log_nonneg
      have hqone : 1 <= q := by omega
      have : (1 : Real) <= (q : Real) := by exact_mod_cast hqone
      linarith
    gcongr
  unfold nontrivialTypeIOneMean
  calc
    ∑ q ∈ Icc 2 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖ <=
        ∑ q ∈ Icc 2 Q, D := by
      exact Finset.sum_le_sum hterm
    _ = ((Icc 2 Q).card : Real) * D := by simp
    _ <= (Q : Real) * D := by
      apply mul_le_mul_of_nonneg_right _ hD
      exact_mod_cast (show (Icc 2 Q).card <= Q by simp)
    _ = 4 * (v : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
        Real.log (2 * (Q : Real)) * Real.log ((y + 1 : Nat) : Real) := by
      dsimp [D]
      ring
def typeIOneMean (v y Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q,
      ‖vaughanS1 v y (fun n => chi (n : ZMod q))‖
theorem levelOne_typeIOne_le (v y : Nat) :
    (((1 : Nat) : Real) / ((1 : Nat).totient : Real)) *
        ∑ chi ∈ primitiveCharacters 1,
          ‖vaughanS1 v y (fun n => chi (n : ZMod 1))‖ <=
      3 * (y : Real) * Real.log ((y + 1 : Nat) : Real) ^ 2 := by
  let B : Real := 3 * (y : Real) * Real.log ((y + 1 : Nat) : Real) ^ 2
  have hB : 0 <= B := by
    dsimp [B]
    positivity
  have hsum :
      ∑ chi ∈ primitiveCharacters 1,
          ‖vaughanS1 v y (fun n => chi (n : ZMod 1))‖ <= B := by
    calc
      ∑ chi ∈ primitiveCharacters 1,
          ‖vaughanS1 v y (fun n => chi (n : ZMod 1))‖ <=
          ∑ chi ∈ primitiveCharacters 1, B := by
        apply Finset.sum_le_sum
        intro chi hchi
        rw [vaughanS1_eq_typeIOneCharacterSum]
        exact norm_typeIOneCharacterSum_trivial v y 1 chi
      _ = ((primitiveCharacters 1).card : Real) * B := by simp
      _ <= B := by
        have hcard : ((primitiveCharacters 1).card : Real) <= 1 := by
          exact_mod_cast primitiveCharacters_card_le_totient 1
        nlinarith
  norm_num
  simpa [B, Nat.cast_add, Nat.cast_one] using hsum
theorem typeIOneMean_le (v y Q : Nat) (hQ : 1 <= Q) :
    typeIOneMean v y Q <=
      3 * (y : Real) * Real.log ((y + 1 : Nat) : Real) ^ 2 +
        4 * (v : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
          Real.log (2 * (Q : Real)) * Real.log ((y + 1 : Nat) : Real) := by
  have hsplit : typeIOneMean v y Q =
      (((1 : Nat) : Real) / ((1 : Nat).totient : Real)) *
          ∑ chi ∈ primitiveCharacters 1,
            ‖vaughanS1 v y (fun n => chi (n : ZMod 1))‖ +
        nontrivialTypeIOneMean v y Q := by
    unfold typeIOneMean nontrivialTypeIOneMean
    rw [← Finset.insert_Icc_succ_left_eq_Icc hQ]
    rw [Finset.sum_insert (by simp)]
    simp
  rw [hsplit]
  exact add_le_add (levelOne_typeIOne_le v y)
    (nontrivialTypeIOneMean_le v y Q)
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
open BombieriVinogradov.VaughanIdentity
def typeITwoKernelCoefficient (u v m : Nat) : Real :=
  ∑ factors ∈ Nat.divisorsAntidiagonal m,
    (if factors.1 <= u then ArithmeticFunction.vonMangoldt factors.1 else 0) *
      (if factors.2 <= v then
        ((ArithmeticFunction.moebius : ArithmeticFunction Real) factors.2)
      else 0)
theorem typeI2Kernel_apply_coefficients (u v n : Nat) :
    typeI2Kernel u v n =
      ∑ pair ∈ Nat.divisorsAntidiagonal n,
        typeITwoKernelCoefficient u v pair.1 *
          ((ArithmeticFunction.zeta : ArithmeticFunction Real) pair.2) := by
  rw [typeI2Kernel_apply]
  rfl
theorem typeITwoKernelCoefficient_abs_le_log (u v m : Nat) :
    |typeITwoKernelCoefficient u v m| <= Real.log (m : Real) := by
  calc
    |typeITwoKernelCoefficient u v m| <=
        ∑ factors ∈ Nat.divisorsAntidiagonal m,
          |(if factors.1 <= u then ArithmeticFunction.vonMangoldt factors.1 else 0) *
            (if factors.2 <= v then
              ((ArithmeticFunction.moebius : ArithmeticFunction Real) factors.2)
            else 0)| := by
      unfold typeITwoKernelCoefficient
      exact Finset.abs_sum_le_sum_abs _ _
    _ <= ∑ factors ∈ Nat.divisorsAntidiagonal m,
          ArithmeticFunction.vonMangoldt factors.1 *
            ((ArithmeticFunction.zeta : ArithmeticFunction Real) factors.2) := by
      apply Finset.sum_le_sum
      intro factors hfactors
      have hright : Ne factors.2 0 :=
        Nat.right_ne_zero_of_mem_divisorsAntidiagonal hfactors
      have hlambda : 0 <= ArithmeticFunction.vonMangoldt factors.1 :=
        ArithmeticFunction.vonMangoldt_nonneg
      by_cases hleftCutoff : factors.1 <= u
      · by_cases hrightCutoff : factors.2 <= v
        · rcases ArithmeticFunction.moebius_eq_or factors.2 with hzero | hone | hneg
          · simp [hleftCutoff, hrightCutoff, hzero,
              ArithmeticFunction.zeta_apply_ne hright,
              ArithmeticFunction.vonMangoldt_nonneg]
          · simp [hleftCutoff, hrightCutoff, hone,
              ArithmeticFunction.zeta_apply_ne hright,
              abs_of_nonneg hlambda]
          · simp [hleftCutoff, hrightCutoff, hneg,
              ArithmeticFunction.zeta_apply_ne hright,
              abs_of_nonneg hlambda]
        · simp [hleftCutoff, hrightCutoff,
            ArithmeticFunction.zeta_apply_ne hright,
            ArithmeticFunction.vonMangoldt_nonneg]
      · simp [hleftCutoff, ArithmeticFunction.zeta_apply_ne hright,
          ArithmeticFunction.vonMangoldt_nonneg]
    _ = (ArithmeticFunction.vonMangoldt *
        (ArithmeticFunction.zeta : ArithmeticFunction Real)) m := by
      rw [ArithmeticFunction.mul_apply]
    _ = Real.log (m : Real) := by
      rw [ArithmeticFunction.vonMangoldt_mul_zeta]
      rfl
def typeITwoCharacterSum (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ m ∈ Icc 1 Y, ∑ n ∈ Icc 1 (Y / m),
    (typeITwoKernelCoefficient u v m : Complex) *
      chi ((m * n : Nat) : ZMod q)
theorem vaughanS2_eq_typeITwoCharacterSum (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) :
    vaughanS2 u v Y (fun n => chi (n : ZMod q)) =
      typeITwoCharacterSum u v Y q chi := by
  unfold vaughanS2 weightedKernelSum
  simp_rw [typeI2Kernel_apply_coefficients]
  push_cast
  simp_rw [Finset.sum_mul]
  have hreindex :
      (∑ k ∈ Icc 1 Y, ∑ pair ∈ Nat.divisorsAntidiagonal k,
        (typeITwoKernelCoefficient u v pair.1 : Complex) *
          (((ArithmeticFunction.zeta : ArithmeticFunction Real) pair.2 : Real) : Complex) *
            chi (k : ZMod q)) =
        ∑ k ∈ Icc 1 Y, ∑ pair ∈ Nat.divisorsAntidiagonal k,
          (typeITwoKernelCoefficient u v pair.1 : Complex) *
            (((ArithmeticFunction.zeta : ArithmeticFunction Real) pair.2 : Real) : Complex) *
              chi ((pair.1 * pair.2 : Nat) : ZMod q) := by
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro pair hpair
    rw [(Nat.mem_divisorsAntidiagonal.mp hpair).1]
  rw [hreindex]
  have hhyper := sum_divisorsAntidiagonal_Icc_eq_hyperbola
    (fun m n =>
      (typeITwoKernelCoefficient u v m : Complex) *
        (((ArithmeticFunction.zeta : ArithmeticFunction Real) n : Real) : Complex) *
          chi ((m * n : Nat) : ZMod q)) Y
  rw [hhyper]
  unfold typeITwoCharacterSum
  apply Finset.sum_congr rfl
  intro m hm
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : Ne n 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  simp [ArithmeticFunction.zeta_apply_ne hn0]
theorem intervalCharacterSum_one_eq_Icc (L q : Nat)
    (chi : DirichletCharacter Complex q) :
    intervalCharacterSum oneIntegerCoefficient 0 L q chi =
      ∑ n ∈ Icc 1 L, chi (n : ZMod q) := by
  calc
    intervalCharacterSum oneIntegerCoefficient 0 L q chi =
        positiveCharacterSum (fun _ : Nat => (1 : Complex)) L q chi := by
      rfl
    _ = ∑ n ∈ Icc 1 L, chi (n : ZMod q) := by
      rw [positiveCharacterSum_eq_sum_nat]
      simp
theorem typeITwoInnerSum_eq_prefix (u v Y m q : Nat)
    (chi : DirichletCharacter Complex q) :
    (∑ n ∈ Icc 1 (Y / m),
      (typeITwoKernelCoefficient u v m : Complex) *
        chi ((m * n : Nat) : ZMod q)) =
      (typeITwoKernelCoefficient u v m : Complex) * chi (m : ZMod q) *
        intervalCharacterSum oneIntegerCoefficient 0 (Y / m) q chi := by
  rw [intervalCharacterSum_one_eq_Icc]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Nat.cast_mul, map_mul]
  ring
def typeITwoSmallCharacterSum (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ m ∈ (Icc 1 Y).filter (fun m => m <= u), ∑ n ∈ Icc 1 (Y / m),
    (typeITwoKernelCoefficient u v m : Complex) *
      chi ((m * n : Nat) : ZMod q)
def typeITwoLargeCharacterSum (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ m ∈ (Icc 1 Y).filter (fun m => u < m), ∑ n ∈ Icc 1 (Y / m),
    (typeITwoKernelCoefficient u v m : Complex) *
      chi ((m * n : Nat) : ZMod q)
theorem typeITwoCharacterSum_eq_small_add_large (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) :
    typeITwoCharacterSum u v Y q chi =
      typeITwoSmallCharacterSum u v Y q chi +
        typeITwoLargeCharacterSum u v Y q chi := by
  let F : Nat -> Complex := fun m =>
    ∑ n ∈ Icc 1 (Y / m),
      (typeITwoKernelCoefficient u v m : Complex) *
        chi ((m * n : Nat) : ZMod q)
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (Icc 1 Y) (fun m => m <= u) F
  unfold typeITwoCharacterSum typeITwoSmallCharacterSum typeITwoLargeCharacterSum
  change (∑ m ∈ Icc 1 Y, F m) =
    (∑ m ∈ (Icc 1 Y).filter (fun m => m <= u), F m) +
      ∑ m ∈ (Icc 1 Y).filter (fun m => u < m), F m
  rw [hsplit.symm]
  simp only [not_le]
theorem norm_typeITwoSmallCharacterSum_le {q : Nat} [NeZero q]
    (hq : 1 < q) {chi : DirichletCharacter Complex q}
    (hchi : DirichletCharacter.IsPrimitive chi) (u v Y : Nat) :
    ‖typeITwoSmallCharacterSum u v Y q chi‖ <=
      (u : Real) *
        (2 * Real.log (u : Real) * Real.sqrt (q : Real) *
          Real.log (2 * (q : Real))) := by
  let active : Finset Nat := (Icc 1 Y).filter fun m => m <= u
  let C : Real :=
    2 * Real.log (u : Real) * Real.sqrt (q : Real) *
      Real.log (2 * (q : Real))
  have hlogq : 0 <= Real.log (2 * (q : Real)) := by
    apply Real.log_nonneg
    have hqone : (1 : Real) <= (q : Real) := by exact_mod_cast hq.le
    linarith
  have hterm : ∀ m ∈ active,
      ‖∑ n ∈ Icc 1 (Y / m),
        (typeITwoKernelCoefficient u v m : Complex) *
          chi ((m * n : Nat) : ZMod q)‖ <= C := by
    intro m hm
    have hmData := Finset.mem_filter.mp hm
    have hmpos : 0 < m := (Finset.mem_Icc.mp hmData.1).1
    have hupos : 0 < u := lt_of_lt_of_le hmpos hmData.2
    have hlogu : 0 <= Real.log (u : Real) :=
      Real.log_nonneg (by exact_mod_cast hupos)
    have hcoeff : ‖(typeITwoKernelCoefficient u v m : Complex)‖ <=
        Real.log (u : Real) := by
      calc
        ‖(typeITwoKernelCoefficient u v m : Complex)‖ =
            |typeITwoKernelCoefficient u v m| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
        _ <= Real.log (m : Real) := typeITwoKernelCoefficient_abs_le_log u v m
        _ <= Real.log (u : Real) := by
          apply Real.log_le_log
          · exact_mod_cast hmpos
          · exact_mod_cast hmData.2
    rw [typeITwoInnerSum_eq_prefix]
    calc
      ‖(typeITwoKernelCoefficient u v m : Complex) * chi (m : ZMod q) *
          intervalCharacterSum oneIntegerCoefficient 0 (Y / m) q chi‖ =
          ‖(typeITwoKernelCoefficient u v m : Complex)‖ *
            ‖chi (m : ZMod q)‖ *
              ‖intervalCharacterSum oneIntegerCoefficient 0 (Y / m) q chi‖ := by
        rw [norm_mul, norm_mul]
      _ <= Real.log (u : Real) * 1 *
          (2 * Real.sqrt (q : Real) * Real.log (2 * (q : Real))) := by
        gcongr
        · exact DirichletCharacter.norm_le_one chi (m : ZMod q)
        · exact polyaVinogradov hq hchi 0 (Y / m)
      _ = C := by
        dsimp [C]
        ring
  have hactive : active ⊆ Icc 1 u := by
    intro m hm
    have hmData := Finset.mem_filter.mp hm
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hmData.1).1, hmData.2⟩
  have hcard : ((active.card : Nat) : Real) <= (u : Real) := by
    have hcardNat : active.card <= u := by
      calc
        active.card <= (Icc 1 u).card := Finset.card_le_card hactive
        _ = u := by simp
    exact_mod_cast hcardNat
  have hC : 0 <= C := by
    by_cases hu : u = 0
    · simp [C, hu]
    · dsimp [C]
      have hlogu : 0 <= Real.log (u : Real) :=
        Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hu)
      positivity
  unfold typeITwoSmallCharacterSum
  change ‖∑ m ∈ active, ∑ n ∈ Icc 1 (Y / m),
      (typeITwoKernelCoefficient u v m : Complex) *
        chi ((m * n : Nat) : ZMod q)‖ <= _
  calc
    _ <= ∑ m ∈ active, ‖∑ n ∈ Icc 1 (Y / m),
        (typeITwoKernelCoefficient u v m : Complex) *
          chi ((m * n : Nat) : ZMod q)‖ := norm_sum_le _ _
    _ <= ∑ m ∈ active, C := Finset.sum_le_sum hterm
    _ = (active.card : Real) * C := by simp
    _ <= (u : Real) * C := mul_le_mul_of_nonneg_right hcard hC
    _ = (u : Real) *
        (2 * Real.log (u : Real) * Real.sqrt (q : Real) *
          Real.log (2 * (q : Real))) := by
      dsimp [C]
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
def typeITwoBlockLeftCoefficient (u v M m : Nat) : Complex :=
  if u < m ∧ M < m ∧ m <= 2 * M then
    (typeITwoKernelCoefficient u v m : Complex)
  else 0
def typeITwoRightCoefficient (_ : Nat) : Complex := 1
theorem norm_typeITwoBlockLeftCoefficient_le (u v M m : Nat) :
    ‖typeITwoBlockLeftCoefficient u v M m‖ <=
      Real.log ((2 * M : Nat) : Real) := by
  by_cases hsupport : u < m ∧ M < m ∧ m <= 2 * M
  · rw [typeITwoBlockLeftCoefficient, if_pos hsupport]
    have hlog := typeITwoKernelCoefficient_abs_le_log u v m
    have hlogMono : Real.log (m : Real) <= Real.log ((2 * M : Nat) : Real) := by
      apply Real.log_le_log
      · exact_mod_cast (show 0 < m by omega)
      · exact_mod_cast hsupport.2.2
    simpa [Complex.norm_real, Real.norm_eq_abs] using hlog.trans hlogMono
  · rw [typeITwoBlockLeftCoefficient, if_neg hsupport, norm_zero]
    simpa using Real.log_natCast_nonneg (2 * M)
theorem typeITwoBlockLeftCoefficient_mass_le (u v M : Nat) :
    coefficientMass (typeITwoBlockLeftCoefficient u v M) (2 * M) <=
      (2 * M : Nat) * Real.log ((2 * M : Nat) : Real) ^ 2 := by
  unfold coefficientMass
  calc
    ∑ m ∈ Icc 1 (2 * M), ‖typeITwoBlockLeftCoefficient u v M m‖ ^ 2 <=
        ∑ m ∈ Icc 1 (2 * M),
          Real.log ((2 * M : Nat) : Real) ^ 2 := by
      apply Finset.sum_le_sum
      intro m hm
      nlinarith [norm_nonneg (typeITwoBlockLeftCoefficient u v M m),
        norm_typeITwoBlockLeftCoefficient_le u v M m,
        Real.log_natCast_nonneg (2 * M)]
    _ = (2 * M : Nat) * Real.log ((2 * M : Nat) : Real) ^ 2 := by simp
theorem typeITwoRightCoefficient_mass_le (N : Nat) :
    coefficientMass typeITwoRightCoefficient N <= (N : Real) := by
  unfold coefficientMass typeITwoRightCoefficient
  simp
def typeITwoBlockMean (u v M N X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q,
      maximalBilinearNorm
        (typeITwoBlockLeftCoefficient u v M) typeITwoRightCoefficient
        (2 * M) N X chi
theorem typeITwoBlockMean_le (u v M N X Q : Nat)
    (hX : 2 <= X) (hQ : 1 <= Q) :
    typeITwoBlockMean u v M N X Q <= typeIIBlockMajorant M N X Q := by
  have hraw := weightedMaximalBilinear_le_cutoffFactor
    X (2 * M) N Q
      (typeITwoBlockLeftCoefficient u v M) typeITwoRightCoefficient hX hQ
  rw [positiveCoefficientMass_eq_coefficientMass,
    positiveCoefficientMass_eq_coefficientMass] at hraw
  unfold typeITwoBlockMean typeIIBlockMajorant
  apply hraw.trans
  have hleft := typeITwoBlockLeftCoefficient_mass_le u v M
  have hright := typeITwoRightCoefficient_mass_le N
  have hleftFactor : 0 <=
      36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) := by positivity
  have hrightFactor : 0 <= 36 * ((N : Real) + (Q : Real) ^ 2) := by positivity
  have hcutoff : 0 <= 16 + 4 * Real.log ((X : Real) + 1) := by
    have : 0 <= Real.log ((X : Real) + 1) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 <= X + 1 by omega)
    positivity
  have hsqrtLeft :
      Real.sqrt (36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
          coefficientMass (typeITwoBlockLeftCoefficient u v M) (2 * M)) <=
        Real.sqrt (36 * (((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
          (((2 * M : Nat) : Real) * Real.log ((2 * M : Nat) : Real) ^ 2)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hleft hleftFactor
  have hsqrtRight :
      Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) *
          coefficientMass typeITwoRightCoefficient N) <=
        Real.sqrt (36 * ((N : Real) + (Q : Real) ^ 2) * (N : Real)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left hright hrightFactor
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul hsqrtLeft hsqrtRight (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hcutoff
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
def typeITwoLargeCoefficient (u v m : Nat) : Complex :=
  if u < m then (typeITwoKernelCoefficient u v m : Complex) else 0
theorem sum_typeITwoBlockLeftCoefficient_eq (u v X m : Nat)
    (hu : 1 <= u) (hmX : m <= X) :
    ∑ k ∈ dyadicExponentSet X, typeITwoBlockLeftCoefficient u v (2 ^ k) m =
      typeITwoLargeCoefficient u v m := by
  by_cases hmu : m <= u
  · simp [typeITwoBlockLeftCoefficient, typeITwoLargeCoefficient,
      not_lt.mpr hmu]
  · have hm : 2 <= m := by omega
    let k₀ := Nat.log 2 (m - 1)
    have hk₀Data := dyadicExponent_mem_for hm hmX
    change k₀ ∈ dyadicExponentSet X ∧ 2 ^ k₀ < m ∧ m <= 2 * 2 ^ k₀ at hk₀Data
    rw [Finset.sum_eq_single k₀]
    · rw [typeITwoBlockLeftCoefficient,
        if_pos ⟨lt_of_not_ge hmu, hk₀Data.2⟩,
        typeITwoLargeCoefficient, if_pos (lt_of_not_ge hmu)]
    · intro k hk hne
      rw [typeITwoBlockLeftCoefficient, if_neg]
      intro hblock
      apply hne
      exact (dyadicExponent_unique hblock.2).symm
    · intro hknot
      exact (hknot hk₀Data.1).elim
theorem typeITwoLargeCharacterSum_eq_restricted (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) :
    typeITwoLargeCharacterSum u v Y q chi =
      restrictedBilinearCharacterSum
        (typeITwoLargeCoefficient u v) typeITwoRightCoefficient Y Y Y q chi := by
  unfold typeITwoLargeCharacterSum restrictedBilinearCharacterSum
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Icc_one_div_eq_filter Y m (Finset.mem_Icc.mp hm).1]
  rw [Finset.sum_filter]
  by_cases hmu : u < m
  · simp [hmu, typeITwoLargeCoefficient, typeITwoRightCoefficient]
  · simp [hmu, typeITwoLargeCoefficient]
def typeITwoDyadicGlobalBlockSum (u v Y q k : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  restrictedBilinearCharacterSum
    (typeITwoBlockLeftCoefficient u v (2 ^ k)) typeITwoRightCoefficient
    Y Y Y q chi
theorem typeITwoLargeCharacterSum_eq_sum_globalBlocks
    (u v X Y q : Nat) (chi : DirichletCharacter Complex q)
    (hu : 1 <= u) (hYX : Y <= X) :
    typeITwoLargeCharacterSum u v Y q chi =
      ∑ k ∈ dyadicExponentSet X, typeITwoDyadicGlobalBlockSum u v Y q k chi := by
  rw [typeITwoLargeCharacterSum_eq_restricted]
  unfold typeITwoDyadicGlobalBlockSum restrictedBilinearCharacterSum
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hproduct : m * n <= Y
  · simp only [hproduct, if_true, typeITwoRightCoefficient]
    simp_rw [mul_one]
    rw [← Finset.sum_mul]
    rw [sum_typeITwoBlockLeftCoefficient_eq u v X m hu
      ((Finset.mem_Icc.mp hm).2.trans hYX)]
  · simp [hproduct]
def typeITwoBlockPairSum (u v M A B Y q : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  ∑ pair ∈ typeIIBlockPairSet M A B Y,
    typeITwoLargeCoefficient u v pair.1 *
      chi ((pair.1 * pair.2 : Nat) : ZMod q)
theorem restricted_typeITwoBlock_eq_pairSum
    (u v M A B Y q : Nat) (chi : DirichletCharacter Complex q) :
    restrictedBilinearCharacterSum
        (typeITwoBlockLeftCoefficient u v M) typeITwoRightCoefficient
        A B Y q chi = typeITwoBlockPairSum u v M A B Y q chi := by
  unfold restrictedBilinearCharacterSum typeITwoBlockPairSum typeIIBlockPairSet
  rw [← Finset.sum_product']
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro pair hpair
  by_cases hblock : M < pair.1 ∧ pair.1 <= 2 * M
  · by_cases hlarge : u < pair.1
    · have hsupport : u < pair.1 ∧ M < pair.1 ∧ pair.1 <= 2 * M :=
        ⟨hlarge, hblock⟩
      by_cases hproduct : pair.1 * pair.2 <= Y
      · simp [hsupport, hproduct, typeITwoBlockLeftCoefficient,
          typeITwoLargeCoefficient, typeITwoRightCoefficient]
      · simp [hsupport, hproduct]
    · have hsupport : ¬(u < pair.1 ∧ M < pair.1 ∧ pair.1 <= 2 * M) := by
        exact fun h => hlarge h.1
      simp [hlarge, typeITwoBlockLeftCoefficient,
        typeITwoLargeCoefficient]
  · have hsupport : ¬(u < pair.1 ∧ M < pair.1 ∧ pair.1 <= 2 * M) := by
      exact fun h => hblock h.2
    rw [typeITwoBlockLeftCoefficient, if_neg hsupport]
    have hall : ¬(M < pair.1 ∧ pair.1 <= 2 * M ∧ pair.1 * pair.2 <= Y) := by
      intro h
      exact hblock ⟨h.1, h.2.1⟩
    simp [hall]
def typeITwoDyadicBlockSum (u v X Y q k : Nat)
    (chi : DirichletCharacter Complex q) : Complex :=
  restrictedBilinearCharacterSum
    (typeITwoBlockLeftCoefficient u v (2 ^ k)) typeITwoRightCoefficient
    (2 * 2 ^ k) (X / 2 ^ k) Y q chi
theorem typeITwoDyadicGlobalBlockSum_eq_blockSum
    (u v X Y q k : Nat) (chi : DirichletCharacter Complex q)
    (hYX : Y <= X) :
    typeITwoDyadicGlobalBlockSum u v Y q k chi =
      typeITwoDyadicBlockSum u v X Y q k chi := by
  unfold typeITwoDyadicGlobalBlockSum typeITwoDyadicBlockSum
  rw [restricted_typeITwoBlock_eq_pairSum, restricted_typeITwoBlock_eq_pairSum]
  unfold typeITwoBlockPairSum
  have hpowOne : 1 <= 2 ^ k := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero k (by omega))
  rw [typeIIBlockPairSet_global_eq_efficient (2 ^ k) X Y hpowOne hYX]
theorem typeITwoLargeCharacterSum_eq_sum_dyadicBlocks
    (u v X Y q : Nat) (chi : DirichletCharacter Complex q)
    (hu : 1 <= u) (hYX : Y <= X) :
    typeITwoLargeCharacterSum u v Y q chi =
      ∑ k ∈ dyadicExponentSet X, typeITwoDyadicBlockSum u v X Y q k chi := by
  rw [typeITwoLargeCharacterSum_eq_sum_globalBlocks u v X Y q chi hu hYX]
  apply Finset.sum_congr rfl
  intro k hk
  exact typeITwoDyadicGlobalBlockSum_eq_blockSum u v X Y q k chi hYX
def maximalTypeITwoLargeCharacterNorm (u v X q : Nat)
    (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖typeITwoLargeCharacterSum u v Y q chi‖
theorem maximalTypeITwoLargeCharacterNorm_le_sum_blocks
    (u v X q : Nat) (chi : DirichletCharacter Complex q) (hu : 1 <= u) :
    maximalTypeITwoLargeCharacterNorm u v X q chi <=
      ∑ k ∈ dyadicExponentSet X,
        maximalBilinearNorm
          (typeITwoBlockLeftCoefficient u v (2 ^ k)) typeITwoRightCoefficient
          (2 * 2 ^ k) (X / 2 ^ k) X chi := by
  unfold maximalTypeITwoLargeCharacterNorm
  apply Finset.sup'_le
  intro Y hY
  have hYX : Y <= X := by
    have := Finset.mem_range.mp hY
    omega
  rw [typeITwoLargeCharacterSum_eq_sum_dyadicBlocks u v X Y q chi hu hYX]
  calc
    _ <= ∑ k ∈ dyadicExponentSet X,
        ‖typeITwoDyadicBlockSum u v X Y q k chi‖ := norm_sum_le _ _
    _ <= ∑ k ∈ dyadicExponentSet X,
        maximalBilinearNorm
          (typeITwoBlockLeftCoefficient u v (2 ^ k)) typeITwoRightCoefficient
          (2 * 2 ^ k) (X / 2 ^ k) X chi := by
      apply Finset.sum_le_sum
      intro k hk
      unfold typeITwoDyadicBlockSum maximalBilinearNorm
      exact Finset.le_sup'
        (fun Z => ‖restrictedBilinearCharacterSum
          (typeITwoBlockLeftCoefficient u v (2 ^ k)) typeITwoRightCoefficient
          (2 * 2 ^ k) (X / 2 ^ k) Z q chi‖) hY
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
def typeITwoLargeMean (u v X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalTypeITwoLargeCharacterNorm u v X q chi
theorem typeITwoLargeMean_le_sum_blockMeans
    (u v X Q : Nat) (hu : 1 <= u) :
    typeITwoLargeMean u v X Q <=
      ∑ k ∈ dyadicExponentSet X,
        typeITwoBlockMean u v (2 ^ k) (X / 2 ^ k) X Q := by
  unfold typeITwoLargeMean
  calc
    _ <= ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q, ∑ k ∈ dyadicExponentSet X,
          maximalBilinearNorm
            (typeITwoBlockLeftCoefficient u v (2 ^ k)) typeITwoRightCoefficient
            (2 * 2 ^ k) (X / 2 ^ k) X chi := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro chi hchi
        exact maximalTypeITwoLargeCharacterNorm_le_sum_blocks u v X q chi hu
      · positivity
    _ = ∑ k ∈ dyadicExponentSet X,
        typeITwoBlockMean u v (2 ^ k) (X / 2 ^ k) X Q := by
      unfold typeITwoBlockMean
      let F : (q : Nat) -> DirichletCharacter Complex q -> Nat -> Real :=
        fun q chi k => maximalBilinearNorm
          (typeITwoBlockLeftCoefficient u v (2 ^ k)) typeITwoRightCoefficient
          (2 * 2 ^ k) (X / 2 ^ k) X chi
      change (∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q, ∑ k ∈ dyadicExponentSet X, F q chi k) =
        ∑ k ∈ dyadicExponentSet X, ∑ q ∈ Icc 1 Q,
          ((q : Real) / (q.totient : Real)) *
            ∑ chi ∈ primitiveCharacters q, F q chi k
      calc
        _ = ∑ q ∈ Icc 1 Q, ∑ chi ∈ primitiveCharacters q,
            ∑ k ∈ dyadicExponentSet X,
              ((q : Real) / (q.totient : Real)) * F q chi k := by
          simp_rw [Finset.mul_sum]
        _ = ∑ q ∈ Icc 1 Q, ∑ k ∈ dyadicExponentSet X,
            ∑ chi ∈ primitiveCharacters q,
              ((q : Real) / (q.totient : Real)) * F q chi k := by
          apply Finset.sum_congr rfl
          intro q hq
          rw [Finset.sum_comm]
        _ = ∑ k ∈ dyadicExponentSet X, ∑ q ∈ Icc 1 Q,
            ∑ chi ∈ primitiveCharacters q,
              ((q : Real) / (q.totient : Real)) * F q chi k := by
          rw [Finset.sum_comm]
        _ = _ := by simp_rw [Finset.mul_sum]
theorem typeITwoKernelCoefficient_eq_zero_of_mul_lt
    {u v m : Nat} (huv : u * v < m) :
    typeITwoKernelCoefficient u v m = 0 := by
  unfold typeITwoKernelCoefficient
  apply Finset.sum_eq_zero
  intro factors hfactors
  have hproduct := (Nat.mem_divisorsAntidiagonal.mp hfactors).1
  by_cases hleft : factors.1 <= u
  · by_cases hright : factors.2 <= v
    · have : m <= u * v := by
        rw [← hproduct]
        exact Nat.mul_le_mul hleft hright
      omega
    · simp [hright]
  · simp [hleft]
theorem typeITwoBlockMean_eq_zero_of_upper
    {u v M N X Q : Nat} (huvM : u * v <= M) :
    typeITwoBlockMean u v M N X Q = 0 := by
  have hcoeff : ∀ m, typeITwoBlockLeftCoefficient u v M m = 0 := by
    intro m
    unfold typeITwoBlockLeftCoefficient
    by_cases hs : u < m ∧ M < m ∧ m <= 2 * M
    · rw [if_pos hs, typeITwoKernelCoefficient_eq_zero_of_mul_lt (lt_of_le_of_lt huvM hs.2.1)]
      simp
    · simp [hs]
  unfold typeITwoBlockMean maximalBilinearNorm restrictedBilinearCharacterSum
  simp_rw [hcoeff]
  simp
def activeTypeITwoExponentSet (u v X : Nat) : Finset Nat :=
  (dyadicExponentSet X).filter fun k => u < 2 * 2 ^ k ∧ 2 ^ k < u * v
theorem typeITwoLargeMean_le_sum_activeMajorants
    (u v X Q : Nat) (hu : 1 <= u) (hX : 2 <= X) (hQ : 1 <= Q) :
    typeITwoLargeMean u v X Q <=
      ∑ k ∈ activeTypeITwoExponentSet u v X,
        typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := by
  calc
    typeITwoLargeMean u v X Q <=
        ∑ k ∈ dyadicExponentSet X,
          typeITwoBlockMean u v (2 ^ k) (X / 2 ^ k) X Q :=
      typeITwoLargeMean_le_sum_blockMeans u v X Q hu
    _ = ∑ k ∈ activeTypeITwoExponentSet u v X,
        typeITwoBlockMean u v (2 ^ k) (X / 2 ^ k) X Q := by
      symm
      unfold activeTypeITwoExponentSet
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hactive : u < 2 * 2 ^ k ∧ 2 ^ k < u * v
      · simp [hactive]
      · have hinactive : 2 * 2 ^ k <= u ∨ u * v <= 2 ^ k := by omega
        rcases hinactive with hlow | hupp
        · have hzero : typeITwoBlockLeftCoefficient u v (2 ^ k) = 0 := by
            funext m
            unfold typeITwoBlockLeftCoefficient
            rw [if_neg (by
              intro hs
              omega)]
            rfl
          unfold typeITwoBlockMean maximalBilinearNorm restrictedBilinearCharacterSum
          simp_rw [hzero]
          simp [hactive]
        · rw [typeITwoBlockMean_eq_zero_of_upper hupp]
          simp [hactive]
    _ <= ∑ k ∈ activeTypeITwoExponentSet u v X,
        typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := by
      apply Finset.sum_le_sum
      intro k hk
      exact typeITwoBlockMean_le u v (2 ^ k) (X / 2 ^ k) X Q hX hQ
def typeITwoSourceCore (X u Q : Nat) : Real :=
  2 * (X : Real) + 2 * ((X : Real) * (Q : Real) / Real.sqrt (u : Real)) +
    2 * ((u : Real) * Real.sqrt (X : Real) * (Q : Real)) +
      2 * (Real.sqrt (X : Real) * (Q : Real) ^ 2)
theorem typeITwo_sqrt_core_bound
    {x u m n q : Real}
    (hx : 0 <= x) (hu : 0 < u) (hm : 0 <= m) (hn : 0 <= n) (hq : 0 <= q)
    (hmn : m * n <= x) (hum : u <= 2 * m) (hmu : m <= u ^ 2) :
    Real.sqrt ((2 * m + q ^ 2) * (2 * m) * (n + q ^ 2) * n) <=
      2 * x + 2 * (x * q / Real.sqrt u) +
        2 * (u * Real.sqrt x * q) + 2 * (Real.sqrt x * q ^ 2) := by
  let A : Real := u * Real.sqrt x * q
  let B : Real := x * q / Real.sqrt u
  let C : Real := Real.sqrt x * q ^ 2
  have hsu : 0 < Real.sqrt u := Real.sqrt_pos.2 hu
  have hA : 0 <= A := by dsimp [A]; positivity
  have hB : 0 <= B := by dsimp [B]; positivity
  have hC : 0 <= C := by dsimp [C]; positivity
  have hA2 : A ^ 2 = u ^ 2 * x * q ^ 2 := by
    dsimp [A]
    rw [mul_pow, mul_pow, Real.sq_sqrt hx]
  have hBmul : B ^ 2 * u = x ^ 2 * q ^ 2 := by
    dsimp [B]
    rw [div_pow, Real.sq_sqrt hu.le]
    field_simp [hu.ne']
  have hC2 : C ^ 2 = x * q ^ 4 := by
    dsimp [C]
    rw [mul_pow, Real.sq_sqrt hx]
    ring
  have hmnNonneg : 0 <= m * n := mul_nonneg hm hn
  have htermOne : 4 * (m * n) ^ 2 <= 4 * x ^ 2 := by nlinarith
  have hmProduct : m * (m * n) <= u ^ 2 * x :=
    mul_le_mul hmu hmn hmnNonneg (sq_nonneg u)
  have hmProductQ := mul_le_mul_of_nonneg_right hmProduct (sq_nonneg q)
  have htermTwo : 4 * m ^ 2 * n * q ^ 2 <= 4 * A ^ 2 := by
    nlinarith [hA2, hmProductQ]
  have huProduct : u * (m * n ^ 2) <= 2 * (m * n) ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_right hum (mul_nonneg hm (sq_nonneg n))
    nlinarith
  have huProductX : u * (m * n ^ 2) <= 2 * x ^ 2 := by
    have hsquare : (m * n) ^ 2 <= x ^ 2 :=
      (sq_le_sq₀ hmnNonneg hx).2 hmn
    nlinarith [huProduct, hsquare]
  have huProductQ := mul_le_mul_of_nonneg_right huProductX (sq_nonneg q)
  have htermThree : 2 * m * n ^ 2 * q ^ 2 <= 4 * B ^ 2 := by
    have hscaled : (2 * m * n ^ 2 * q ^ 2) * u <= (4 * B ^ 2) * u := by
      nlinarith [huProductQ, hBmul]
    exact (mul_le_mul_iff_of_pos_right hu).mp (by simpa [mul_assoc] using hscaled)
  have htermFour : 2 * m * n * q ^ 4 <= 2 * C ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hmn (by positivity : 0 <= q ^ 4), hC2]
  have hradicand :
      (2 * m + q ^ 2) * (2 * m) * (n + q ^ 2) * n <=
        (2 * x + 2 * B + 2 * A + 2 * C) ^ 2 := by
    nlinarith [htermOne, htermTwo, htermThree, htermFour,
      sq_nonneg (2 * x + 2 * B + 2 * A + 2 * C)]
  apply Real.sqrt_le_iff.mpr
  constructor
  · positivity
  · simpa [A, B, C] using hradicand
theorem active_typeITwoBlockMajorant_le
    (M X u Q : Nat) (hX : 2 <= X) (hu : 1 <= u)
    (hMX : M <= X) (hactive : u < 2 * M ∧ M < u * u) :
    typeIIBlockMajorant M (X / M) X Q <=
      2880 * Real.log (X : Real) ^ 2 * typeITwoSourceCore X u Q := by
  have hMNnat : M * (X / M) <= X := by
    simpa [Nat.mul_comm] using Nat.div_mul_le_self X M
  have hMN : (M : Real) * ((X / M : Nat) : Real) <= (X : Real) := by
    exact_mod_cast hMNnat
  have hcore := typeITwo_sqrt_core_bound
    (show 0 <= (X : Real) by positivity)
    (show 0 < (u : Real) by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hu))
    (show 0 <= (M : Real) by positivity)
    (show 0 <= ((X / M : Nat) : Real) by positivity)
    (show 0 <= (Q : Real) by positivity) hMN
    (by exact_mod_cast hactive.1.le)
    (by
      have hNat : M <= u ^ 2 := by simpa [pow_two] using hactive.2.le
      exact_mod_cast hNat)
  have hcore' :
      Real.sqrt (((((2 * M : Nat) : Real) + (Q : Real) ^ 2) *
        ((2 * M : Nat) : Real)) *
          ((((X / M : Nat) : Real) + (Q : Real) ^ 2) * ((X / M : Nat) : Real))) <=
        typeITwoSourceCore X u Q := by
    simpa [typeITwoSourceCore, Nat.cast_mul, Nat.cast_ofNat, mul_assoc] using hcore
  have hcutoff : 16 + 4 * Real.log ((X : Real) + 1) <=
      40 * Real.log (X : Real) := by
    simpa using cutoffFactor_le_log_product X 1 1 hX (by norm_num) (by norm_num)
  have hMpos : 0 < M := by omega
  have hlogMX : Real.log (M : Real) <= Real.log (X : Real) := by
    apply Real.log_le_log
    · exact_mod_cast hMpos
    · exact_mod_cast hMX
  have hlogTwoX : Real.log 2 <= Real.log (X : Real) := by
    apply Real.log_le_log
    · norm_num
    · exact_mod_cast hX
  have hlogDouble : Real.log ((2 * M : Nat) : Real) <=
      2 * Real.log (X : Real) := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    rw [Real.log_mul (by norm_num : Ne (2 : Real) 0)
      (by exact_mod_cast hMpos.ne' : Ne (M : Real) 0)]
    linarith
  have hsource : 0 <= typeITwoSourceCore X u Q := by
    unfold typeITwoSourceCore
    positivity
  rw [typeIIBlockMajorant_eq_core]
  calc
    _ <= 36 * (40 * Real.log (X : Real)) *
        (2 * Real.log (X : Real)) * typeITwoSourceCore X u Q := by
      gcongr
    _ = 2880 * Real.log (X : Real) ^ 2 * typeITwoSourceCore X u Q := by ring
theorem typeITwoLargeMean_le_sourceScale
    (u X Q : Nat) (hu : 1 <= u) (hX : 2 <= X) (hQ : 1 <= Q) :
    typeITwoLargeMean u u X Q <=
      11520 * Real.log (X : Real) ^ 3 * typeITwoSourceCore X u Q := by
  have hbase := typeITwoLargeMean_le_sum_activeMajorants u u X Q hu hX hQ
  let C : Real := 2880 * Real.log (X : Real) ^ 2 * typeITwoSourceCore X u Q
  have hC : 0 <= C := by
    dsimp [C]
    unfold typeITwoSourceCore
    positivity
  calc
    typeITwoLargeMean u u X Q <=
        ∑ k ∈ activeTypeITwoExponentSet u u X,
          typeIIBlockMajorant (2 ^ k) (X / 2 ^ k) X Q := hbase
    _ <= ∑ k ∈ activeTypeITwoExponentSet u u X, C := by
      apply Finset.sum_le_sum
      intro k hk
      have hkData := Finset.mem_filter.mp hk
      have hkLog : k <= Nat.log 2 X := by
        have hkRange := Finset.mem_range.mp hkData.1
        simp only [dyadicExponentSet] at hkData
        omega
      have hpowX : 2 ^ k <= X := by
        calc
          2 ^ k <= 2 ^ Nat.log 2 X := Nat.pow_le_pow_right (by omega) hkLog
          _ <= X := Nat.pow_log_le_self 2 (by omega)
      exact active_typeITwoBlockMajorant_le (2 ^ k) X u Q hX hu hpowX hkData.2
    _ = ((activeTypeITwoExponentSet u u X).card : Real) * C := by simp
    _ <= ((dyadicExponentSet X).card : Real) * C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ <= (4 * Real.log (X : Real)) * C := by
      exact mul_le_mul_of_nonneg_right (dyadicExponentSet_card_le_log X hX) hC
    _ = 11520 * Real.log (X : Real) ^ 3 * typeITwoSourceCore X u Q := by
      dsimp [C]
      ring
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
open BombieriVinogradov.VaughanIdentity
theorem norm_intervalCharacterSum_one_le (L q : Nat)
    (chi : DirichletCharacter Complex q) :
    ‖intervalCharacterSum oneIntegerCoefficient 0 L q chi‖ <= (L : Real) := by
  rw [intervalCharacterSum_one_eq_Icc]
  calc
    _ <= ∑ n ∈ Icc 1 L, ‖chi (n : ZMod q)‖ := norm_sum_le _ _
    _ <= ∑ n ∈ Icc 1 L, (1 : Real) := by
      apply Finset.sum_le_sum
      intro n hn
      exact DirichletCharacter.norm_le_one chi (n : ZMod q)
    _ = (L : Real) := by simp
theorem norm_typeITwoSmallCharacterSum_trivial (u v Y q : Nat)
    (chi : DirichletCharacter Complex q) :
    ‖typeITwoSmallCharacterSum u v Y q chi‖ <=
      3 * (Y : Real) * Real.log ((Y + 1 : Nat) : Real) ^ 2 := by
  let active : Finset Nat := (Icc 1 Y).filter fun m => m <= u
  have hterm : ∀ m ∈ active,
      ‖∑ n ∈ Icc 1 (Y / m),
        (typeITwoKernelCoefficient u v m : Complex) *
          chi ((m * n : Nat) : ZMod q)‖ <=
        (Y : Real) * (m : Real)⁻¹ * Real.log ((Y + 1 : Nat) : Real) := by
    intro m hm
    have hmData := Finset.mem_filter.mp hm
    have hmpos : 0 < m := (Finset.mem_Icc.mp hmData.1).1
    have hcoeff : ‖(typeITwoKernelCoefficient u v m : Complex)‖ <=
        Real.log ((Y + 1 : Nat) : Real) := by
      calc
        ‖(typeITwoKernelCoefficient u v m : Complex)‖ =
            |typeITwoKernelCoefficient u v m| := by
          rw [Complex.norm_real, Real.norm_eq_abs]
        _ <= Real.log (m : Real) := typeITwoKernelCoefficient_abs_le_log u v m
        _ <= Real.log ((Y + 1 : Nat) : Real) := by
          apply Real.log_le_log
          · exact_mod_cast hmpos
          · exact_mod_cast Nat.le_succ_of_le (Finset.mem_Icc.mp hmData.1).2
    rw [typeITwoInnerSum_eq_prefix, norm_mul, norm_mul]
    have hprefix := norm_intervalCharacterSum_one_le (Y / m) q chi
    have hfloor : ((Y / m : Nat) : Real) <= (Y : Real) / (m : Real) :=
      Nat.cast_div_le
    calc
      _ <= Real.log ((Y + 1 : Nat) : Real) * 1 * ((Y / m : Nat) : Real) := by
        gcongr
        exact DirichletCharacter.norm_le_one chi (m : ZMod q)
      _ <= Real.log ((Y + 1 : Nat) : Real) * 1 *
          ((Y : Real) / (m : Real)) := by gcongr
      _ = (Y : Real) * (m : Real)⁻¹ * Real.log ((Y + 1 : Nat) : Real) := by
        rw [div_eq_mul_inv]
        ring
  have hactive : active ⊆ Icc 1 Y := fun m hm => (Finset.mem_filter.mp hm).1
  have hharmonic : ∑ m ∈ Icc 1 Y, (m : Real)⁻¹ = (harmonic Y : Real) := by
    rw [harmonic_eq_sum_Icc]
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  unfold typeITwoSmallCharacterSum
  change ‖∑ m ∈ active, ∑ n ∈ Icc 1 (Y / m),
      (typeITwoKernelCoefficient u v m : Complex) *
        chi ((m * n : Nat) : ZMod q)‖ <= _
  calc
    _ <= ∑ m ∈ active, ‖∑ n ∈ Icc 1 (Y / m),
        (typeITwoKernelCoefficient u v m : Complex) *
          chi ((m * n : Nat) : ZMod q)‖ := norm_sum_le _ _
    _ <= ∑ m ∈ active,
        (Y : Real) * (m : Real)⁻¹ * Real.log ((Y + 1 : Nat) : Real) :=
      Finset.sum_le_sum hterm
    _ <= ∑ m ∈ Icc 1 Y,
        (Y : Real) * (m : Real)⁻¹ * Real.log ((Y + 1 : Nat) : Real) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hactive
      intro m hmAll hmActive
      positivity
    _ = (Y : Real) * (harmonic Y : Real) *
        Real.log ((Y + 1 : Nat) : Real) := by
      simp_rw [mul_assoc]
      rw [← Finset.mul_sum, ← Finset.sum_mul, hharmonic]
    _ <= (Y : Real) * (3 * Real.log ((Y + 1 : Nat) : Real)) *
        Real.log ((Y + 1 : Nat) : Real) := by
      gcongr
      exact harmonic_le_three_log_add_one Y
    _ = 3 * (Y : Real) * Real.log ((Y + 1 : Nat) : Real) ^ 2 := by ring
def maximalTypeITwoSmallCharacterNorm (u v X q : Nat)
    (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖typeITwoSmallCharacterSum u v Y q chi‖
theorem maximalTypeITwoSmallCharacterNorm_le {q : Nat} [NeZero q]
    (hq : 1 < q) {chi : DirichletCharacter Complex q}
    (hchi : DirichletCharacter.IsPrimitive chi) (u v X : Nat) :
    maximalTypeITwoSmallCharacterNorm u v X q chi <=
      (u : Real) *
        (2 * Real.log (u : Real) * Real.sqrt (q : Real) *
          Real.log (2 * (q : Real))) := by
  unfold maximalTypeITwoSmallCharacterNorm
  apply Finset.sup'_le
  intro Y hY
  exact norm_typeITwoSmallCharacterSum_le hq hchi u v Y
def typeITwoSmallMean (u v X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalTypeITwoSmallCharacterNorm u v X q chi
theorem maximalTypeITwoSmallCharacterNorm_trivial (u v X q : Nat)
    (chi : DirichletCharacter Complex q) :
    maximalTypeITwoSmallCharacterNorm u v X q chi <=
      3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 := by
  unfold maximalTypeITwoSmallCharacterNorm
  apply Finset.sup'_le
  intro Y hY
  have hYX : Y <= X := by
    have := Finset.mem_range.mp hY
    omega
  have hbase := norm_typeITwoSmallCharacterSum_trivial u v Y q chi
  apply hbase.trans
  have hlog : Real.log ((Y + 1 : Nat) : Real) <=
      Real.log ((X + 1 : Nat) : Real) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.add_le_add_right hYX 1
  have hlogY : 0 <= Real.log ((Y + 1 : Nat) : Real) :=
    Real.log_natCast_nonneg (Y + 1)
  have hlogX : 0 <= Real.log ((X + 1 : Nat) : Real) :=
    Real.log_natCast_nonneg (X + 1)
  gcongr
theorem weighted_primitive_typeITwoSmall_le {q : Nat} [NeZero q]
    (hq : 1 < q) (u v X : Nat) :
    ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q, maximalTypeITwoSmallCharacterNorm u v X q chi <=
      (q : Real) * (u : Real) *
        (2 * Real.log (u : Real) * Real.sqrt (q : Real) *
          Real.log (2 * (q : Real))) := by
  classical
  let B : Real := (u : Real) *
    (2 * Real.log (u : Real) * Real.sqrt (q : Real) *
      Real.log (2 * (q : Real)))
  have hB : 0 <= B := by
    dsimp [B]
    have hlogu := Real.log_natCast_nonneg u
    have hlogq : 0 <= Real.log (2 * (q : Real)) := by
      apply Real.log_nonneg
      have : (1 : Real) <= (q : Real) := by exact_mod_cast hq.le
      linarith
    positivity
  have hchars :
      ∑ chi ∈ primitiveCharacters q, maximalTypeITwoSmallCharacterNorm u v X q chi <=
        (q.totient : Real) * B := by
    calc
      _ <= ∑ chi ∈ primitiveCharacters q, B := by
        apply Finset.sum_le_sum
        intro chi hchiMem
        have hchi : DirichletCharacter.IsPrimitive chi := by
          simpa [primitiveCharacters] using (Finset.mem_filter.mp hchiMem).2
        exact maximalTypeITwoSmallCharacterNorm_le hq hchi u v X
      _ = ((primitiveCharacters q).card : Real) * B := by simp
      _ <= (q.totient : Real) * B := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast primitiveCharacters_card_le_totient q) hB
  have hphi : 0 < (q.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  calc
    _ <= ((q : Real) / (q.totient : Real)) * ((q.totient : Real) * B) :=
      mul_le_mul_of_nonneg_left hchars (by positivity)
    _ = (q : Real) * B := by field_simp
    _ = _ := by dsimp [B]; ring
def nontrivialTypeITwoSmallMean (u v X Q : Nat) : Real :=
  ∑ q ∈ Icc 2 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalTypeITwoSmallCharacterNorm u v X q chi
theorem nontrivialTypeITwoSmallMean_le (u v X Q : Nat) :
    nontrivialTypeITwoSmallMean u v X Q <=
      2 * (u : Real) * Real.log (u : Real) * (Q : Real) ^ 2 *
        Real.sqrt (Q : Real) * Real.log (2 * (Q : Real)) := by
  let D : Real := (Q : Real) * (u : Real) *
    (2 * Real.log (u : Real) * Real.sqrt (Q : Real) * Real.log (2 * (Q : Real)))
  have hD : 0 <= D := by
    dsimp [D]
    have hlogu := Real.log_natCast_nonneg u
    by_cases hQ : Q = 0
    · simp [hQ]
    · have hlogQ : 0 <= Real.log (2 * (Q : Real)) := by
        apply Real.log_nonneg
        have : (1 : Real) <= (Q : Real) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
        linarith
      positivity
  have hterm : ∀ q ∈ Icc 2 Q,
      ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q, maximalTypeITwoSmallCharacterNorm u v X q chi <= D := by
    intro q hqMem
    have hqBounds := Finset.mem_Icc.mp hqMem
    let _ : NeZero q := ⟨(by omega)⟩
    apply (weighted_primitive_typeITwoSmall_le (show 1 < q by omega) u v X).trans
    dsimp [D]
    have hlogq : 0 <= Real.log (2 * (q : Real)) := by
      apply Real.log_nonneg
      have : (1 : Real) <= (q : Real) := by exact_mod_cast (show 1 <= q by omega)
      linarith
    have hqcast : (q : Real) <= (Q : Real) := by exact_mod_cast hqBounds.2
    have hsqrt : Real.sqrt (q : Real) <= Real.sqrt (Q : Real) :=
      Real.sqrt_le_sqrt hqcast
    have hlog : Real.log (2 * (q : Real)) <= Real.log (2 * (Q : Real)) := by
      apply Real.log_le_log
      · exact mul_pos (by norm_num) (by exact_mod_cast (show 0 < q by omega))
      · nlinarith
    gcongr
  unfold nontrivialTypeITwoSmallMean
  calc
    _ <= ∑ q ∈ Icc 2 Q, D := Finset.sum_le_sum hterm
    _ = ((Icc 2 Q).card : Real) * D := by simp
    _ <= (Q : Real) * D := by
      apply mul_le_mul_of_nonneg_right _ hD
      exact_mod_cast (show (Icc 2 Q).card <= Q by simp)
    _ = _ := by dsimp [D]; ring
theorem typeITwoSmallMean_le (u v X Q : Nat) (hQ : 1 <= Q) :
    typeITwoSmallMean u v X Q <=
      3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 +
        2 * (u : Real) * Real.log (u : Real) * (Q : Real) ^ 2 *
          Real.sqrt (Q : Real) * Real.log (2 * (Q : Real)) := by
  have hlevel :
      (((1 : Nat) : Real) / ((1 : Nat).totient : Real)) *
          ∑ chi ∈ primitiveCharacters 1,
            maximalTypeITwoSmallCharacterNorm u v X 1 chi <=
        3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 := by
    let B : Real := 3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2
    have hB : 0 <= B := by dsimp [B]; positivity
    have hsum : ∑ chi ∈ primitiveCharacters 1,
        maximalTypeITwoSmallCharacterNorm u v X 1 chi <= B := by
      calc
        _ <= ∑ chi ∈ primitiveCharacters 1, B := by
          apply Finset.sum_le_sum
          intro chi hchi
          exact maximalTypeITwoSmallCharacterNorm_trivial u v X 1 chi
        _ = ((primitiveCharacters 1).card : Real) * B := by simp
        _ <= B := by
          have hcard : ((primitiveCharacters 1).card : Real) <= 1 := by
            exact_mod_cast primitiveCharacters_card_le_totient 1
          nlinarith
    norm_num
    simpa [B] using hsum
  have hsplit : typeITwoSmallMean u v X Q =
      (((1 : Nat) : Real) / ((1 : Nat).totient : Real)) *
          ∑ chi ∈ primitiveCharacters 1,
            maximalTypeITwoSmallCharacterNorm u v X 1 chi +
        nontrivialTypeITwoSmallMean u v X Q := by
    unfold typeITwoSmallMean nontrivialTypeITwoSmallMean
    rw [← Finset.insert_Icc_succ_left_eq_Icc hQ]
    rw [Finset.sum_insert (by simp)]
    simp
  rw [hsplit]
  exact add_le_add hlevel (nontrivialTypeITwoSmallMean_le u v X Q)
def maximalTypeITwoCharacterNorm (u v X q : Nat)
    (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖vaughanS2 u v Y (fun n => chi (n : ZMod q))‖
theorem maximalTypeITwoCharacterNorm_le (u v X q : Nat)
    (chi : DirichletCharacter Complex q) :
    maximalTypeITwoCharacterNorm u v X q chi <=
      maximalTypeITwoSmallCharacterNorm u v X q chi +
        maximalTypeITwoLargeCharacterNorm u v X q chi := by
  unfold maximalTypeITwoCharacterNorm
  apply Finset.sup'_le
  intro Y hY
  rw [vaughanS2_eq_typeITwoCharacterSum,
    typeITwoCharacterSum_eq_small_add_large]
  calc
    _ <= ‖typeITwoSmallCharacterSum u v Y q chi‖ +
        ‖typeITwoLargeCharacterSum u v Y q chi‖ := norm_add_le _ _
    _ <= maximalTypeITwoSmallCharacterNorm u v X q chi +
        maximalTypeITwoLargeCharacterNorm u v X q chi := by
      apply add_le_add
      · unfold maximalTypeITwoSmallCharacterNorm
        exact Finset.le_sup'
          (fun Z => ‖typeITwoSmallCharacterSum u v Z q chi‖) hY
      · unfold maximalTypeITwoLargeCharacterNorm
        exact Finset.le_sup'
          (fun Z => ‖typeITwoLargeCharacterSum u v Z q chi‖) hY
def typeITwoMean (u v X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalTypeITwoCharacterNorm u v X q chi
theorem typeITwoMean_le_hybrid
    (u X Q : Nat) (hu : 1 <= u) (hX : 2 <= X) (hQ : 1 <= Q) :
    typeITwoMean u u X Q <=
      3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 +
        2 * (u : Real) * Real.log (u : Real) * (Q : Real) ^ 2 *
          Real.sqrt (Q : Real) * Real.log (2 * (Q : Real)) +
        11520 * Real.log (X : Real) ^ 3 * typeITwoSourceCore X u Q := by
  have hsplit : typeITwoMean u u X Q <=
      typeITwoSmallMean u u X Q + typeITwoLargeMean u u X Q := by
    unfold typeITwoMean typeITwoSmallMean typeITwoLargeMean
    calc
      _ <= ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q,
            (maximalTypeITwoSmallCharacterNorm u u X q chi +
              maximalTypeITwoLargeCharacterNorm u u X q chi) := by
        apply Finset.sum_le_sum
        intro q hq
        apply mul_le_mul_of_nonneg_left
        · apply Finset.sum_le_sum
          intro chi hchi
          exact maximalTypeITwoCharacterNorm_le u u X q chi
        · positivity
      _ = _ := by
        simp_rw [Finset.sum_add_distrib, mul_add, Finset.sum_add_distrib]
  exact hsplit.trans (add_le_add (typeITwoSmallMean_le u u X Q hQ)
    (typeITwoLargeMean_le_sourceScale u X Q hu hX hQ))
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Finset
open scoped BigOperators
namespace BombieriVinogradov.VaughanIdentity
theorem vaughanIdentity : VaughanIdentityStatement := by
  intro u v y f hu hv hy
  unfold mangoldtSum vaughanS1 vaughanS2 vaughanS3 vaughanS4 weightedKernelSum
  rw [← Finset.sum_sub_distrib]
  rw [← Finset.sum_add_distrib]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hcoeff := congrArg (fun kernel : ArithmeticFunction Real => kernel n)
    (vaughanKernelIdentity u v)
  change ((ArithmeticFunction.vonMangoldt n : Real) : Complex) * f n = _
  rw [hcoeff]
  change (((typeI1Kernel v n - typeI2Kernel u v n + typeIIKernel u v n +
    lambdaHead u n : Real) : Complex) * f n) = _
  push_cast
  ring
end BombieriVinogradov.VaughanIdentity
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
open BombieriVinogradov.VaughanIdentity
theorem norm_vaughanS4_le (u Y q : Nat)
    (chi : DirichletCharacter Complex q) :
    ‖vaughanS4 u Y (fun n => chi (n : ZMod q))‖ <=
      (u : Real) * Real.log ((u + 1 : Nat) : Real) := by
  let active : Finset Nat := (Icc 1 Y).filter fun n => n <= u
  have hterm : ∀ n ∈ active,
      ‖(ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod q)‖ <=
        Real.log ((u + 1 : Nat) : Real) := by
    intro n hn
    have hnData := Finset.mem_filter.mp hn
    have hnpos : 0 < n := (Finset.mem_Icc.mp hnData.1).1
    calc
      _ = ArithmeticFunction.vonMangoldt n * ‖chi (n : ZMod q)‖ := by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      _ <= Real.log (n : Real) * 1 := by
        exact mul_le_mul ArithmeticFunction.vonMangoldt_le_log
          (DirichletCharacter.norm_le_one chi (n : ZMod q))
          (norm_nonneg _) (Real.log_natCast_nonneg n)
      _ <= Real.log ((u + 1 : Nat) : Real) := by
        rw [mul_one]
        apply Real.log_le_log
        · exact_mod_cast hnpos
        · exact_mod_cast Nat.le_succ_of_le hnData.2
  have hactive : active ⊆ Icc 1 u := by
    intro n hn
    have hnData := Finset.mem_filter.mp hn
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hnData.1).1, hnData.2⟩
  unfold vaughanS4 weightedKernelSum lambdaHead truncateLE
  change ‖∑ n ∈ Icc 1 Y,
      ((if n <= u then ArithmeticFunction.vonMangoldt n else 0 : Real) : Complex) *
        chi (n : ZMod q)‖ <= _
  have hrewrite :
      (∑ n ∈ Icc 1 Y,
        ((if n <= u then ArithmeticFunction.vonMangoldt n else 0 : Real) : Complex) *
          chi (n : ZMod q)) =
        ∑ n ∈ active,
          (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod q) := by
    unfold active
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hnu : n <= u <;> simp [hnu]
  rw [hrewrite]
  change ‖∑ n ∈ active,
      (ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod q)‖ <= _
  calc
    _ <= ∑ n ∈ active,
        ‖(ArithmeticFunction.vonMangoldt n : Complex) * chi (n : ZMod q)‖ :=
      norm_sum_le _ _
    _ <= ∑ n ∈ active, Real.log ((u + 1 : Nat) : Real) :=
      Finset.sum_le_sum hterm
    _ = (active.card : Real) * Real.log ((u + 1 : Nat) : Real) := by simp
    _ <= (u : Real) * Real.log ((u + 1 : Nat) : Real) := by
      apply mul_le_mul_of_nonneg_right _ (Real.log_natCast_nonneg (u + 1))
      have hcard : active.card <= u := by
        calc
          active.card <= (Icc 1 u).card := Finset.card_le_card hactive
          _ = u := by simp
      exact_mod_cast hcard
def maximalVaughanS4Norm (u X q : Nat)
    (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖vaughanS4 u Y (fun n => chi (n : ZMod q))‖
theorem maximalVaughanS4Norm_le (u X q : Nat)
    (chi : DirichletCharacter Complex q) :
    maximalVaughanS4Norm u X q chi <=
      (u : Real) * Real.log ((u + 1 : Nat) : Real) := by
  unfold maximalVaughanS4Norm
  apply Finset.sup'_le
  intro Y hY
  exact norm_vaughanS4_le u Y q chi
def vaughanS4Mean (u X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalVaughanS4Norm u X q chi
theorem vaughanS4Mean_le (u X Q : Nat) :
    vaughanS4Mean u X Q <=
      (u : Real) * (Q : Real) ^ 2 * Real.log ((u + 1 : Nat) : Real) := by
  let B : Real := (u : Real) * Real.log ((u + 1 : Nat) : Real)
  have hB : 0 <= B := by dsimp [B]; positivity
  unfold vaughanS4Mean
  calc
    _ <= ∑ q ∈ Icc 1 Q, (q : Real) * B := by
      apply Finset.sum_le_sum
      intro q hq
      let _ : NeZero q :=
        ⟨Nat.ne_of_gt (Finset.mem_Icc.mp hq).1⟩
      have hchars : ∑ chi ∈ primitiveCharacters q, maximalVaughanS4Norm u X q chi <=
          (q.totient : Real) * B := by
        calc
          _ <= ∑ chi ∈ primitiveCharacters q, B := by
            apply Finset.sum_le_sum
            intro chi hchi
            exact maximalVaughanS4Norm_le u X q chi
          _ = ((primitiveCharacters q).card : Real) * B := by simp
          _ <= (q.totient : Real) * B := by
            exact mul_le_mul_of_nonneg_right
              (by exact_mod_cast primitiveCharacters_card_le_totient q) hB
      have hphi : 0 < (q.totient : Real) := by
        exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
      calc
        _ <= ((q : Real) / (q.totient : Real)) * ((q.totient : Real) * B) :=
          mul_le_mul_of_nonneg_left hchars (by positivity)
        _ = (q : Real) * B := by field_simp
    _ <= ∑ q ∈ Icc 1 Q, (Q : Real) * B := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_right _ hB
      exact_mod_cast (Finset.mem_Icc.mp hq).2
    _ = (Q : Real) ^ 2 * B := by simp; ring
    _ = _ := by dsimp [B]; ring
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
open BombieriVinogradov.VaughanIdentity
theorem vaughanIdentity_allEndpoints (u v Y : Nat) (f : Nat -> Complex) :
    mangoldtSum Y f =
      vaughanS1 v Y f - vaughanS2 u v Y f +
        vaughanS3 u v Y f + vaughanS4 u Y f := by
  unfold mangoldtSum vaughanS1 vaughanS2 vaughanS3 vaughanS4 weightedKernelSum
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have hcoeff := congrArg (fun kernel : ArithmeticFunction Real => kernel n)
    (vaughanKernelIdentity u v)
  change ((ArithmeticFunction.vonMangoldt n : Real) : Complex) * f n = _
  rw [hcoeff]
  change (((typeI1Kernel v n - typeI2Kernel u v n + typeIIKernel u v n +
    lambdaHead u n : Real) : Complex) * f n) = _
  push_cast
  ring
def maximalMangoldtCharacterNorm (X q : Nat)
    (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖mangoldtSum Y (fun n => chi (n : ZMod q))‖
def maximalVaughanS1Norm (v X q : Nat)
    (chi : DirichletCharacter Complex q) : Real :=
  (range (X + 1)).sup' (by simp) fun Y =>
    ‖vaughanS1 v Y (fun n => chi (n : ZMod q))‖
theorem maximalMangoldtCharacterNorm_le_parts
    (u v X q : Nat) (chi : DirichletCharacter Complex q) :
    maximalMangoldtCharacterNorm X q chi <=
      maximalVaughanS1Norm v X q chi +
        maximalTypeITwoCharacterNorm u v X q chi +
          maximalTypeIICharacterNorm u v X q chi + maximalVaughanS4Norm u X q chi := by
  unfold maximalMangoldtCharacterNorm
  apply Finset.sup'_le
  intro Y hY
  rw [vaughanIdentity_allEndpoints]
  calc
    _ <= ‖vaughanS1 v Y (fun n => chi (n : ZMod q))‖ +
          ‖vaughanS2 u v Y (fun n => chi (n : ZMod q))‖ +
        ‖vaughanS3 u v Y (fun n => chi (n : ZMod q))‖ +
          ‖vaughanS4 u Y (fun n => chi (n : ZMod q))‖ := by
      calc
        _ <= ‖vaughanS1 v Y (fun n => chi (n : ZMod q)) -
            vaughanS2 u v Y (fun n => chi (n : ZMod q)) +
              vaughanS3 u v Y (fun n => chi (n : ZMod q))‖ +
            ‖vaughanS4 u Y (fun n => chi (n : ZMod q))‖ := norm_add_le _ _
        _ <= (‖vaughanS1 v Y (fun n => chi (n : ZMod q)) -
              vaughanS2 u v Y (fun n => chi (n : ZMod q))‖ +
            ‖vaughanS3 u v Y (fun n => chi (n : ZMod q))‖) +
            ‖vaughanS4 u Y (fun n => chi (n : ZMod q))‖ := by gcongr; exact norm_add_le _ _
        _ <= ((‖vaughanS1 v Y (fun n => chi (n : ZMod q))‖ +
              ‖vaughanS2 u v Y (fun n => chi (n : ZMod q))‖) +
            ‖vaughanS3 u v Y (fun n => chi (n : ZMod q))‖) +
            ‖vaughanS4 u Y (fun n => chi (n : ZMod q))‖ := by
          gcongr
          exact norm_sub_le _ _
        _ = _ := by ring
    _ <= _ := by
      gcongr
      · unfold maximalVaughanS1Norm
        exact Finset.le_sup' (fun Z => ‖vaughanS1 v Z (fun n => chi (n : ZMod q))‖) hY
      · unfold maximalTypeITwoCharacterNorm
        exact Finset.le_sup' (fun Z => ‖vaughanS2 u v Z (fun n => chi (n : ZMod q))‖) hY
      · unfold maximalTypeIICharacterNorm
        exact Finset.le_sup' (fun Z => ‖vaughanS3 u v Z (fun n => chi (n : ZMod q))‖) hY
      · unfold maximalVaughanS4Norm
        exact Finset.le_sup' (fun Z => ‖vaughanS4 u Z (fun n => chi (n : ZMod q))‖) hY
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
theorem maximalVaughanS1Norm_le {q : Nat} [NeZero q]
    (hq : 1 < q) {chi : DirichletCharacter Complex q}
    (hchi : DirichletCharacter.IsPrimitive chi) (v X : Nat) :
    maximalVaughanS1Norm v X q chi <=
      (v : Real) *
        (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
          Real.log ((X + 1 : Nat) : Real)) := by
  unfold maximalVaughanS1Norm
  apply Finset.sup'_le
  intro Y hY
  have hYX : Y <= X := by
    have := Finset.mem_range.mp hY
    omega
  rw [vaughanS1_eq_typeIOneCharacterSum]
  apply (norm_typeIOneCharacterSum_le hq hchi v Y).trans
  have hlog : Real.log ((Y + 1 : Nat) : Real) <=
      Real.log ((X + 1 : Nat) : Real) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.add_le_add_right hYX 1
  have hlogq : 0 <= Real.log (2 * (q : Real)) := by
    apply Real.log_nonneg
    have : (1 : Real) <= (q : Real) := by exact_mod_cast hq.le
    linarith
  gcongr
theorem maximalVaughanS1Norm_trivial (v X q : Nat)
    (chi : DirichletCharacter Complex q) :
    maximalVaughanS1Norm v X q chi <=
      3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 := by
  unfold maximalVaughanS1Norm
  apply Finset.sup'_le
  intro Y hY
  have hYX : Y <= X := by
    have := Finset.mem_range.mp hY
    omega
  rw [vaughanS1_eq_typeIOneCharacterSum]
  apply (norm_typeIOneCharacterSum_trivial v Y q chi).trans
  have hlog : Real.log ((Y + 1 : Nat) : Real) <=
      Real.log ((X + 1 : Nat) : Real) := by
    apply Real.log_le_log
    · positivity
    · exact_mod_cast Nat.add_le_add_right hYX 1
  have hlogY := Real.log_natCast_nonneg (Y + 1)
  have hlogX := Real.log_natCast_nonneg (X + 1)
  gcongr
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
open BombieriVinogradov.LargeSieve
def typeIOneMaximalMean (v X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalVaughanS1Norm v X q chi
theorem weighted_primitive_maximalVaughanS1_le {q : Nat} [NeZero q]
    (hq : 1 < q) (v X : Nat) :
    ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q, maximalVaughanS1Norm v X q chi <=
      (q : Real) * (v : Real) *
        (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
          Real.log ((X + 1 : Nat) : Real)) := by
  classical
  let B : Real := (v : Real) *
    (4 * Real.sqrt (q : Real) * Real.log (2 * (q : Real)) *
      Real.log ((X + 1 : Nat) : Real))
  have hB : 0 <= B := by
    dsimp [B]
    have hlogq : 0 <= Real.log (2 * (q : Real)) := by
      apply Real.log_nonneg
      have : (1 : Real) <= (q : Real) := by exact_mod_cast hq.le
      linarith
    positivity
  have hchars :
      ∑ chi ∈ primitiveCharacters q, maximalVaughanS1Norm v X q chi <=
        (q.totient : Real) * B := by
    calc
      _ <= ∑ chi ∈ primitiveCharacters q, B := by
        apply Finset.sum_le_sum
        intro chi hchiMem
        have hchi : DirichletCharacter.IsPrimitive chi := by
          simpa [primitiveCharacters] using (Finset.mem_filter.mp hchiMem).2
        exact maximalVaughanS1Norm_le hq hchi v X
      _ = ((primitiveCharacters q).card : Real) * B := by simp
      _ <= (q.totient : Real) * B := by
        exact mul_le_mul_of_nonneg_right
          (by exact_mod_cast primitiveCharacters_card_le_totient q) hB
  have hphi : 0 < (q.totient : Real) := by
    exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  calc
    _ <= ((q : Real) / (q.totient : Real)) * ((q.totient : Real) * B) :=
      mul_le_mul_of_nonneg_left hchars (by positivity)
    _ = (q : Real) * B := by field_simp
    _ = _ := by dsimp [B]; ring
def nontrivialTypeIOneMaximalMean (v X Q : Nat) : Real :=
  ∑ q ∈ Icc 2 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalVaughanS1Norm v X q chi
theorem nontrivialTypeIOneMaximalMean_le (v X Q : Nat) :
    nontrivialTypeIOneMaximalMean v X Q <=
      4 * (v : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
        Real.log (2 * (Q : Real)) * Real.log ((X + 1 : Nat) : Real) := by
  let D : Real := (Q : Real) * (v : Real) *
    (4 * Real.sqrt (Q : Real) * Real.log (2 * (Q : Real)) *
      Real.log ((X + 1 : Nat) : Real))
  have hD : 0 <= D := by
    dsimp [D]
    by_cases hQ : Q = 0
    · simp [hQ]
    · have hlogQ : 0 <= Real.log (2 * (Q : Real)) := by
        apply Real.log_nonneg
        have : (1 : Real) <= (Q : Real) := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr hQ
        linarith
      positivity
  have hterm : ∀ q ∈ Icc 2 Q,
      ((q : Real) / (q.totient : Real)) *
          ∑ chi ∈ primitiveCharacters q, maximalVaughanS1Norm v X q chi <= D := by
    intro q hqMem
    have hqBounds := Finset.mem_Icc.mp hqMem
    let _ : NeZero q := ⟨(by omega)⟩
    apply (weighted_primitive_maximalVaughanS1_le (show 1 < q by omega) v X).trans
    dsimp [D]
    have hqcast : (q : Real) <= (Q : Real) := by exact_mod_cast hqBounds.2
    have hsqrt := Real.sqrt_le_sqrt hqcast
    have hlog : Real.log (2 * (q : Real)) <= Real.log (2 * (Q : Real)) := by
      apply Real.log_le_log
      · exact mul_pos (by norm_num) (by exact_mod_cast (show 0 < q by omega))
      · nlinarith
    have hlogq : 0 <= Real.log (2 * (q : Real)) := by
      apply Real.log_nonneg
      have : (1 : Real) <= (q : Real) := by exact_mod_cast (show 1 <= q by omega)
      linarith
    have hlogX : 0 <= Real.log ((X + 1 : Nat) : Real) :=
      Real.log_natCast_nonneg (X + 1)
    gcongr
  unfold nontrivialTypeIOneMaximalMean
  calc
    _ <= ∑ q ∈ Icc 2 Q, D := Finset.sum_le_sum hterm
    _ = ((Icc 2 Q).card : Real) * D := by simp
    _ <= (Q : Real) * D := by
      apply mul_le_mul_of_nonneg_right _ hD
      exact_mod_cast (show (Icc 2 Q).card <= Q by simp)
    _ = _ := by dsimp [D]; ring
theorem typeIOneMaximalMean_le (v X Q : Nat) (hQ : 1 <= Q) :
    typeIOneMaximalMean v X Q <=
      3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 +
        4 * (v : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
          Real.log (2 * (Q : Real)) * Real.log ((X + 1 : Nat) : Real) := by
  have hlevel :
      (((1 : Nat) : Real) / ((1 : Nat).totient : Real)) *
          ∑ chi ∈ primitiveCharacters 1, maximalVaughanS1Norm v X 1 chi <=
        3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 := by
    let B : Real := 3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2
    have hB : 0 <= B := by dsimp [B]; positivity
    have hsum : ∑ chi ∈ primitiveCharacters 1, maximalVaughanS1Norm v X 1 chi <= B := by
      calc
        _ <= ∑ chi ∈ primitiveCharacters 1, B := by
          apply Finset.sum_le_sum
          intro chi hchi
          exact maximalVaughanS1Norm_trivial v X 1 chi
        _ = ((primitiveCharacters 1).card : Real) * B := by simp
        _ <= B := by
          have hcard : ((primitiveCharacters 1).card : Real) <= 1 := by
            exact_mod_cast primitiveCharacters_card_le_totient 1
          nlinarith
    norm_num
    simpa [B] using hsum
  have hsplit : typeIOneMaximalMean v X Q =
      (((1 : Nat) : Real) / ((1 : Nat).totient : Real)) *
          ∑ chi ∈ primitiveCharacters 1, maximalVaughanS1Norm v X 1 chi +
        nontrivialTypeIOneMaximalMean v X Q := by
    unfold typeIOneMaximalMean nontrivialTypeIOneMaximalMean
    rw [← Finset.insert_Icc_succ_left_eq_Icc hQ]
    rw [Finset.sum_insert (by simp)]
    simp
  rw [hsplit]
  exact add_le_add hlevel (nontrivialTypeIOneMaximalMean_le v X Q)
def vaughanMean (X Q : Nat) : Real :=
  ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
    ∑ chi ∈ primitiveCharacters q, maximalMangoldtCharacterNorm X q chi
theorem vaughanMean_le_parts (u X Q : Nat) :
    vaughanMean X Q <=
      typeIOneMaximalMean u X Q + typeITwoMean u u X Q +
        typeIIDyadicMean u u X Q + vaughanS4Mean u X Q := by
  unfold vaughanMean typeIOneMaximalMean typeITwoMean typeIIDyadicMean vaughanS4Mean
  calc
    _ <= ∑ q ∈ Icc 1 Q, ((q : Real) / (q.totient : Real)) *
        ∑ chi ∈ primitiveCharacters q,
          (maximalVaughanS1Norm u X q chi +
            maximalTypeITwoCharacterNorm u u X q chi +
              maximalTypeIICharacterNorm u u X q chi + maximalVaughanS4Norm u X q chi) := by
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum
        intro chi hchi
        exact maximalMangoldtCharacterNorm_le_parts u u X q chi
      · positivity
    _ = _ := by
      simp_rw [Finset.sum_add_distrib, mul_add]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_add_distrib]
      rw [Finset.sum_add_distrib]
theorem vaughanMean_le_preoptimized
    (u X Q : Nat) (hu : 1 <= u) (hX : 2 <= X) (hQ : 1 <= Q) :
    vaughanMean X Q <=
      (3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 +
        4 * (u : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) *
          Real.log (2 * (Q : Real)) * Real.log ((X + 1 : Nat) : Real)) +
      (3 * (X : Real) * Real.log ((X + 1 : Nat) : Real) ^ 2 +
        2 * (u : Real) * Real.log (u : Real) * (Q : Real) ^ 2 *
          Real.sqrt (Q : Real) * Real.log (2 * (Q : Real)) +
        11520 * Real.log (X : Real) ^ 3 * typeITwoSourceCore X u Q) +
      (11520 * Real.log (X : Real) ^ 3 * typeIISourceCore X u Q) +
      ((u : Real) * (Q : Real) ^ 2 * Real.log ((u + 1 : Nat) : Real)) := by
  exact (vaughanMean_le_parts u X Q).trans
    (add_le_add
      (add_le_add
        (add_le_add (typeIOneMaximalMean_le u X Q hQ)
          (typeITwoMean_le_hybrid u X Q hu hX hQ))
        (typeIIDyadicMean_le_sourceScale u X Q hu hX hQ))
      (vaughanS4Mean_le u X Q))
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
theorem maximalPsiNorm_eq_naturalEndpoint
    (x : Real) (q : Nat) (chi : DirichletCharacter Complex q) :
    maximalPsiNorm x chi = maximalMangoldtCharacterNorm (Nat.floor x) q chi := by
  rfl
theorem primitivePsiMean_eq_vaughanMean (x : Real) (Q : Nat) :
    primitivePsiMean x Q = vaughanMean (Nat.floor x) Q := by
  rfl
end BombieriVinogradov.VaughanMeanValue
end
end

section
namespace BombieriVinogradov.VaughanMeanValue
theorem scale_four_sq_le_eight_cube {S L : Real}
    (hS : 0 <= S) (hLtwo : L ^ 2 <= 2 * L ^ 3) :
    S * (4 * L ^ 2) <= S * (8 * L ^ 3) := by
  have hscaled := mul_le_mul_of_nonneg_left hLtwo hS
  nlinarith
theorem mul_le_two_sq {a b L : Real}
    (ha : 0 <= a) (hb : 0 <= b) (haL : a <= L) (hbL : b <= 2 * L) :
    a * b <= 2 * L ^ 2 := by
  have hmul := mul_le_mul haL hbL hb (by linarith : 0 <= L)
  nlinarith
theorem mul_le_sq {a b L : Real}
    (ha : 0 <= a) (hb : 0 <= b) (haL : a <= L) (hbL : b <= L) :
    a * b <= L ^ 2 := by
  have hmul := mul_le_mul haL hbL hb (by linarith : 0 <= L)
  nlinarith
theorem absorb_vaughan_terms
    {x a b c d short logX logXOne logTwoQ logu loguOne L S : Real}
    (hLhalf : 1 / 2 <= L)
    (hx : 0 <= x) (ha : 0 <= a) (hb : 0 <= b) (hc : 0 <= c)
    (hd : 0 <= d)
    (hlogX0 : 0 <= logX) (hlogXOne0 : 0 <= logXOne)
    (hlogTwoQ0 : 0 <= logTwoQ) (hlogu0 : 0 <= logu)
    (hloguOne0 : 0 <= loguOne) (hS : 0 <= S)
    (hxS : x <= S) (haS : a <= S) (hbS : b <= S) (hcS : c <= S)
    (hdS : d <= S) (hshortS : short <= S)
    (hlogX : logX <= L) (hlogXOne : logXOne <= 2 * L)
    (hlogTwoQ : logTwoQ <= L) (hlogu : logu <= L)
    (hloguOne : loguOne <= 2 * L) :
    (3 * x * logXOne ^ 2 + 4 * a * logTwoQ * logXOne) +
        (3 * x * logXOne ^ 2 + 2 * a * logu * logTwoQ +
          11520 * logX ^ 3 * (2 * x + 2 * b + 2 * c + 2 * d)) +
      11520 * logX ^ 3 * (2 * x + 3 * b + 2 * d) + short * loguOne <=
        200000 * S * L ^ 3 := by
  have hL : 0 <= L := by linarith
  have hLtwo : L ^ 2 <= 2 * L ^ 3 := by nlinarith [sq_nonneg L]
  have hLone : L <= 4 * L ^ 3 := by nlinarith [sq_nonneg L]
  have hlogXOneSq : logXOne ^ 2 <= 4 * L ^ 2 := by
    nlinarith [sq_nonneg (2 * L - logXOne)]
  have hbase : x * logXOne ^ 2 <= 8 * S * L ^ 3 := by
    calc
      _ <= S * (4 * L ^ 2) := mul_le_mul hxS hlogXOneSq (sq_nonneg _) hS
      _ <= S * (8 * L ^ 3) := scale_four_sq_le_eight_cube hS hLtwo
      _ = _ := by ring
  have hfirstLogs : a * logTwoQ * logXOne <= 4 * S * L ^ 3 := by
    have hlogs := mul_le_two_sq hlogTwoQ0 hlogXOne0 hlogTwoQ hlogXOne
    calc
      _ <= a * (2 * L ^ 2) := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hlogs ha
      _ <= S * (2 * L ^ 2) := mul_le_mul_of_nonneg_right haS (by positivity)
      _ <= 4 * S * L ^ 3 := by
        have := mul_le_mul_of_nonneg_left hLtwo hS
        nlinarith
  have hsecondLogs : a * logu * logTwoQ <= 2 * S * L ^ 3 := by
    have hlogs := mul_le_sq hlogu0 hlogTwoQ0 hlogu hlogTwoQ
    calc
      _ <= a * L ^ 2 := by
        simpa [mul_assoc] using mul_le_mul_of_nonneg_left hlogs ha
      _ <= S * L ^ 2 := mul_le_mul_of_nonneg_right haS (sq_nonneg L)
      _ <= S * (2 * L ^ 3) := mul_le_mul_of_nonneg_left hLtwo hS
      _ = 2 * S * L ^ 3 := by ring
  have hlogXpow : logX ^ 3 <= L ^ 3 := by gcongr
  have hcoreTwo : 2 * x + 2 * b + 2 * c + 2 * d <= 8 * S := by linarith
  have hcoreThree : 2 * x + 3 * b + 2 * d <= 7 * S := by linarith
  have hlargeTwo : logX ^ 3 * (2 * x + 2 * b + 2 * c + 2 * d) <=
      8 * S * L ^ 3 := by
    nlinarith [mul_le_mul hlogXpow hcoreTwo (by positivity) (pow_nonneg hL 3)]
  have hlargeThree : logX ^ 3 * (2 * x + 3 * b + 2 * d) <=
      7 * S * L ^ 3 := by
    nlinarith [mul_le_mul hlogXpow hcoreThree (by positivity) (pow_nonneg hL 3)]
  have hremainder : short * loguOne <= 8 * S * L ^ 3 := by
    calc
      _ <= S * (2 * L) := mul_le_mul hshortS hloguOne hloguOne0 hS
      _ <= 8 * S * L ^ 3 := by
        have := mul_le_mul_of_nonneg_left hLone hS
        nlinarith
  nlinarith
end BombieriVinogradov.VaughanMeanValue
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
def vaughanLogScale (X Q : Nat) : Real :=
  Real.log ((X : Real) * (Q : Real))
theorem two_le_cast_product (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) :
    (2 : Real) <= (X : Real) * (Q : Real) := by
  have hXcast : (2 : Real) <= (X : Real) := by exact_mod_cast hX
  have hQcast : (1 : Real) <= (Q : Real) := by exact_mod_cast hQ
  nlinarith [mul_le_mul hXcast hQcast (by norm_num : (0 : Real) <= 1)
    (by positivity : (0 : Real) <= (X : Real))]
theorem half_le_vaughanLogScale (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) :
    (1 / 2 : Real) <= vaughanLogScale X Q := by
  have hhalfLogTwo : (1 / 2 : Real) <= Real.log 2 := by
    have h := Real.le_log_one_add_of_nonneg (x := (1 : Real)) (by norm_num)
    norm_num at h ⊢
    linarith
  exact hhalfLogTwo.trans
    (Real.log_le_log (by norm_num) (two_le_cast_product X Q hX hQ))
theorem log_X_le_vaughanLogScale (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) :
    Real.log (X : Real) <= vaughanLogScale X Q := by
  unfold vaughanLogScale
  apply Real.log_le_log
  · exact_mod_cast (show 0 < X by omega)
  · have hQcast : (1 : Real) <= (Q : Real) := by exact_mod_cast hQ
    nlinarith [mul_le_mul_of_nonneg_left hQcast (by positivity : (0 : Real) <= (X : Real))]
theorem log_twoQ_le_vaughanLogScale (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) :
    Real.log (2 * (Q : Real)) <= vaughanLogScale X Q := by
  unfold vaughanLogScale
  apply Real.log_le_log
  · exact mul_pos (by norm_num) (by exact_mod_cast (show 0 < Q by omega))
  · have hXcast : (2 : Real) <= (X : Real) := by exact_mod_cast hX
    have hQcast : 0 <= (Q : Real) := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hXcast hQcast]
theorem log_X_add_one_le_two_vaughanLogScale
    (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) :
    Real.log ((X + 1 : Nat) : Real) <= 2 * vaughanLogScale X Q := by
  have hXpos : 0 < (X : Real) := by exact_mod_cast (show 0 < X by omega)
  have hXOne : ((X + 1 : Nat) : Real) <= 2 * (X : Real) := by
    push_cast
    nlinarith [show (1 : Real) <= (X : Real) by exact_mod_cast (show 1 <= X by omega)]
  have hlogTwoX : Real.log (2 * (X : Real)) <= 2 * vaughanLogScale X Q := by
    rw [Real.log_mul (by norm_num : Ne (2 : Real) 0) hXpos.ne']
    have hlogTwo : Real.log 2 <= vaughanLogScale X Q :=
      Real.log_le_log (by norm_num) (two_le_cast_product X Q hX hQ)
    have hlogX := log_X_le_vaughanLogScale X Q hX hQ
    linarith
  exact (Real.log_le_log (by positivity) hXOne).trans hlogTwoX
theorem log_u_le_vaughanLogScale
    (u X Q : Nat) (hu : 1 <= u) (huX : u <= X) (hX : 2 <= X) (hQ : 1 <= Q) :
    Real.log (u : Real) <= vaughanLogScale X Q := by
  have huXcast : (u : Real) <= (X : Real) := by exact_mod_cast huX
  apply (Real.log_le_log (by exact_mod_cast (show 0 < u by omega)) huXcast).trans
  exact log_X_le_vaughanLogScale X Q hX hQ
theorem log_u_add_one_le_two_vaughanLogScale
    (u X Q : Nat) (huX : u <= X) (hX : 2 <= X) (hQ : 1 <= Q) :
    Real.log ((u + 1 : Nat) : Real) <= 2 * vaughanLogScale X Q := by
  have huXcast : ((u + 1 : Nat) : Real) <= ((X + 1 : Nat) : Real) := by
    exact_mod_cast Nat.add_le_add_right huX 1
  apply (Real.log_le_log (by positivity) huXcast).trans
  exact log_X_add_one_le_two_vaughanLogScale X Q hX hQ
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
def vaughanSourceScale (X Q : Nat) : Real :=
  (X : Real) + (X : Real) ^ (5 / 6 : Real) * (Q : Real) +
    Real.sqrt (X : Real) * (Q : Real) ^ 2
theorem vaughanMean_le_of_cutoff_bounds
    (u X Q : Nat) (hu : 1 <= u) (huX : u <= X) (hX : 2 <= X) (hQ : 1 <= Q)
    (hsmall : (u : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) <=
      vaughanSourceScale X Q)
    (hinverse : (X : Real) * (Q : Real) / Real.sqrt (u : Real) <=
      vaughanSourceScale X Q)
    (hforward : (u : Real) * Real.sqrt (X : Real) * (Q : Real) <=
      vaughanSourceScale X Q)
    (hshort : (u : Real) * (Q : Real) ^ 2 <= vaughanSourceScale X Q) :
    vaughanMean X Q <=
      200000 * vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 := by
  apply (vaughanMean_le_preoptimized u X Q hu hX hQ).trans
  dsimp [typeITwoSourceCore, typeIISourceCore]
  let S : Real := vaughanSourceScale X Q
  have hS : 0 <= S := by dsimp [S, vaughanSourceScale]; positivity
  have hXscale : (X : Real) <= S := by
    dsimp [S, vaughanSourceScale]
    have hmiddle : 0 <= (X : Real) ^ (5 / 6 : Real) * (Q : Real) := by positivity
    have hlast : 0 <= Real.sqrt (X : Real) * (Q : Real) ^ 2 := by positivity
    linarith
  have hsqrtScale : Real.sqrt (X : Real) * (Q : Real) ^ 2 <= S := by
    dsimp [S, vaughanSourceScale]
    have hfirst : 0 <= (X : Real) := by positivity
    have hmiddle : 0 <= (X : Real) ^ (5 / 6 : Real) * (Q : Real) := by positivity
    linarith
  have hsmall' : (u : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real) <= S := by
    exact hsmall
  have hinverse' : (X : Real) * (Q : Real) / Real.sqrt (u : Real) <= S := by
    exact hinverse
  have hforward' : (u : Real) * Real.sqrt (X : Real) * (Q : Real) <= S := by
    exact hforward
  have hshort' : (u : Real) * (Q : Real) ^ 2 <= S := by exact hshort
  have habsorb := absorb_vaughan_terms
    (x := (X : Real))
    (a := (u : Real) * (Q : Real) ^ 2 * Real.sqrt (Q : Real))
    (b := (X : Real) * (Q : Real) / Real.sqrt (u : Real))
    (c := (u : Real) * Real.sqrt (X : Real) * (Q : Real))
    (d := Real.sqrt (X : Real) * (Q : Real) ^ 2)
    (short := (u : Real) * (Q : Real) ^ 2)
    (logX := Real.log (X : Real))
    (logXOne := Real.log ((X + 1 : Nat) : Real))
    (logTwoQ := Real.log (2 * (Q : Real)))
    (logu := Real.log (u : Real))
    (loguOne := Real.log ((u + 1 : Nat) : Real))
    (L := vaughanLogScale X Q) (S := S)
    (half_le_vaughanLogScale X Q hX hQ)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
    (Real.log_natCast_nonneg X) (Real.log_natCast_nonneg (X + 1))
    (by apply Real.log_nonneg; nlinarith [show (1 : Real) <= (Q : Real) by exact_mod_cast hQ])
    (Real.log_natCast_nonneg u) (Real.log_natCast_nonneg (u + 1)) hS
    hXscale hsmall' hinverse' hforward' hsqrtScale hshort'
    (log_X_le_vaughanLogScale X Q hX hQ)
    (log_X_add_one_le_two_vaughanLogScale X Q hX hQ)
    (log_twoQ_le_vaughanLogScale X Q hX hQ)
    (log_u_le_vaughanLogScale u X Q hu huX hX hQ)
    (log_u_add_one_le_two_vaughanLogScale u X Q huX hX hQ)
  dsimp [S] at habsorb
  simpa only [mul_assoc, mul_comm, mul_left_comm] using habsorb
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
def middleLevelRoot (x : Real) : Real := x ^ (1 / 3 : Real)
theorem middleLevelRoot_nonneg {x : Real} (hx : 0 <= x) :
    0 <= middleLevelRoot x := by
  exact Real.rpow_nonneg hx _
theorem middleLevelRoot_pos {x : Real} (hx : 0 < x) :
    0 < middleLevelRoot x := by
  exact Real.rpow_pos_of_pos hx _
theorem middleLevelRoot_cube {x : Real} (hx : 0 <= x) :
    middleLevelRoot x ^ 3 = x := by
  simpa [middleLevelRoot, one_div] using
    (Real.rpow_inv_natCast_pow hx (by norm_num : Ne (3 : Nat) 0))
theorem middleLevelRoot_mul_sqrt {x : Real} (hx : 0 < x) :
    middleLevelRoot x * Real.sqrt x = x ^ (5 / 6 : Real) := by
  rw [middleLevelRoot, Real.sqrt_eq_rpow, ← Real.rpow_add hx]
  norm_num
theorem sqrt_middleLevelRoot {x : Real} (hx : 0 <= x) :
    Real.sqrt (middleLevelRoot x) = x ^ (1 / 6 : Real) := by
  rw [Real.sqrt_eq_rpow, middleLevelRoot, ← Real.rpow_mul hx]
  norm_num
theorem middleLevelRoot_le_self {x : Real} (hx : 1 <= x) :
    middleLevelRoot x <= x := by
  have hpow := Real.rpow_le_rpow_of_exponent_le hx
    (by norm_num : (1 / 3 : Real) <= 1)
  simpa [middleLevelRoot] using hpow
theorem le_middleLevelRoot_of_cube_le {x q : Real}
    (hx : 0 <= x) (hq : 0 <= q) (hqCubeX : q ^ 3 <= x) :
    q <= middleLevelRoot x := by
  apply (pow_le_pow_iff_left₀ hq (middleLevelRoot_nonneg hx)
    (by norm_num : Ne (3 : Nat) 0)).mp
  rw [middleLevelRoot_cube hx]
  exact hqCubeX
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
theorem middleLevelQSqrt_le_sqrtX {x q : Real}
    (hx : 0 <= x) (hq : 0 <= q) (hqCubeX : q ^ 3 <= x) :
    q * Real.sqrt q <= Real.sqrt x := by
  apply (pow_le_pow_iff_left₀ (mul_nonneg hq (Real.sqrt_nonneg q))
    (Real.sqrt_nonneg x) (by norm_num : Ne (2 : Nat) 0)).mp
  rw [mul_pow, Real.sq_sqrt hq, Real.sq_sqrt hx]
  nlinarith
theorem middleLevelSqrtQ_le_sqrtX {x q : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hqCubeX : q ^ 3 <= x) :
    Real.sqrt q <= Real.sqrt x := by
  apply Real.sqrt_le_sqrt
  have hqRoot := le_middleLevelRoot_of_cube_le (by positivity) (by linarith) hqCubeX
  exact hqRoot.trans (middleLevelRoot_le_self hx)
theorem middleLevelSmallTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hqCubeX : q ^ 3 <= x)
    (hu : u <= middleLevelRoot x + 1) :
    u * q ^ 2 * Real.sqrt q <=
      x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 := by
  have hx0 : 0 <= x := by linarith
  have hxpos : 0 < x := by linarith
  have hq0 : 0 <= q := by linarith
  have hroot0 : 0 <= middleLevelRoot x := middleLevelRoot_nonneg hx0
  have hqSqrt := middleLevelQSqrt_le_sqrtX hx0 hq0 hqCubeX
  have hsqrt := middleLevelSqrtQ_le_sqrtX hx hq hqCubeX
  have huScaled := mul_le_mul_of_nonneg_right hu
    (show 0 <= q ^ 2 * Real.sqrt q by positivity)
  have hfirst := mul_le_mul_of_nonneg_left hqSqrt
    (mul_nonneg hroot0 hq0)
  have hsecond := mul_le_mul_of_nonneg_left hsqrt (sq_nonneg q)
  calc
    u * q ^ 2 * Real.sqrt q = u * (q ^ 2 * Real.sqrt q) := by ring
    _ <= (middleLevelRoot x + 1) * (q ^ 2 * Real.sqrt q) := huScaled
    _ = middleLevelRoot x * q * (q * Real.sqrt q) + q ^ 2 * Real.sqrt q := by ring
    _ <= middleLevelRoot x * q * Real.sqrt x + q ^ 2 * Real.sqrt x :=
      add_le_add hfirst hsecond
    _ = x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 := by
      rw [show middleLevelRoot x * q * Real.sqrt x =
        (middleLevelRoot x * Real.sqrt x) * q by ring,
        middleLevelRoot_mul_sqrt hxpos]
      ring
theorem middleLevelInverseTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hrootU : middleLevelRoot x <= u) :
    x * q / Real.sqrt u <= x ^ (5 / 6 : Real) * q := by
  have hx0 : 0 <= x := by linarith
  have hxpos : 0 < x := by linarith
  have hq0 : 0 <= q := by linarith
  have huPos : 0 < u := (middleLevelRoot_pos hxpos).trans_le hrootU
  have hsqrtUPos : 0 < Real.sqrt u := Real.sqrt_pos.2 huPos
  have hden : x ^ (1 / 6 : Real) <= Real.sqrt u := by
    rw [← sqrt_middleLevelRoot hx0]
    exact Real.sqrt_le_sqrt hrootU
  have hproduct : x <= x ^ (5 / 6 : Real) * Real.sqrt u := by
    calc
      x = x ^ (5 / 6 : Real) * x ^ (1 / 6 : Real) := by
        rw [← Real.rpow_add hxpos]
        norm_num
      _ <= x ^ (5 / 6 : Real) * Real.sqrt u :=
        mul_le_mul_of_nonneg_left hden (Real.rpow_nonneg hx0 _)
  have hquotient : x / Real.sqrt u <= x ^ (5 / 6 : Real) :=
    (div_le_iff₀ hsqrtUPos).mpr hproduct
  calc
    x * q / Real.sqrt u = (x / Real.sqrt u) * q := by ring
    _ <= x ^ (5 / 6 : Real) * q :=
      mul_le_mul_of_nonneg_right hquotient hq0
theorem middleLevelForwardTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hu : u <= middleLevelRoot x + 1) :
    u * Real.sqrt x * q <=
      x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 := by
  have hxpos : 0 < x := by linarith
  have hq0 : 0 <= q := by linarith
  have huScaled := mul_le_mul_of_nonneg_right hu
    (mul_nonneg (Real.sqrt_nonneg x) hq0)
  have hqSq : q <= q ^ 2 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)]
  have hsqrtScaled := mul_le_mul_of_nonneg_left hqSq (Real.sqrt_nonneg x)
  calc
    u * Real.sqrt x * q = u * (Real.sqrt x * q) := by ring
    _ <= (middleLevelRoot x + 1) * (Real.sqrt x * q) := huScaled
    _ = (middleLevelRoot x * Real.sqrt x) * q + Real.sqrt x * q := by ring
    _ <= (middleLevelRoot x * Real.sqrt x) * q + Real.sqrt x * q ^ 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left hsqrtScaled (middleLevelRoot x * Real.sqrt x * q)
    _ = x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 := by
      rw [middleLevelRoot_mul_sqrt hxpos]
theorem middleLevelShortTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hqCubeX : q ^ 3 <= x)
    (hu : u <= middleLevelRoot x + 1) :
    u * q ^ 2 <= x + Real.sqrt x * q ^ 2 := by
  have hx0 : 0 <= x := by linarith
  have hq0 : 0 <= q := by linarith
  have hroot0 : 0 <= middleLevelRoot x := middleLevelRoot_nonneg hx0
  have hqRoot := le_middleLevelRoot_of_cube_le hx0 hq0 hqCubeX
  have hqSq := pow_le_pow_left₀ hq0 hqRoot 2
  have hrootScaled := mul_le_mul_of_nonneg_left hqSq hroot0
  have hrootTerm : middleLevelRoot x * q ^ 2 <= x := by
    calc
      middleLevelRoot x * q ^ 2 <=
          middleLevelRoot x * middleLevelRoot x ^ 2 := hrootScaled
      _ = middleLevelRoot x ^ 3 := by ring
      _ = x := middleLevelRoot_cube hx0
  have hsqrtOne : 1 <= Real.sqrt x := by
    have hsqrt := Real.sqrt_le_sqrt hx
    simpa using hsqrt
  have hlast := mul_le_mul_of_nonneg_right hsqrtOne (sq_nonneg q)
  have huScaled := mul_le_mul_of_nonneg_right hu (sq_nonneg q)
  calc
    u * q ^ 2 <= (middleLevelRoot x + 1) * q ^ 2 := huScaled
    _ = middleLevelRoot x * q ^ 2 + q ^ 2 := by ring
    _ <= x + Real.sqrt x * q ^ 2 := add_le_add hrootTerm (by simpa using hlast)
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
def middleLevelCutoff (X : Nat) : Nat :=
  Nat.ceil (middleLevelRoot (X : Real))
theorem middleLevelCutoff_one_le (X : Nat) (hX : 2 <= X) :
    1 <= middleLevelCutoff X := by
  apply Nat.one_le_ceil_iff.mpr
  apply middleLevelRoot_pos
  exact_mod_cast (show 0 < X by omega)
theorem middleLevelRoot_le_cutoff (X : Nat) :
    middleLevelRoot (X : Real) <= (middleLevelCutoff X : Real) := by
  exact Nat.le_ceil _
theorem middleLevelCutoff_lt_root_add_one (X : Nat) :
    (middleLevelCutoff X : Real) < middleLevelRoot (X : Real) + 1 := by
  exact Nat.ceil_lt_add_one (middleLevelRoot_nonneg (by positivity))
theorem middleLevelCutoff_le (X : Nat) (hX : 2 <= X) :
    middleLevelCutoff X <= X := by
  apply Nat.ceil_le.mpr
  apply middleLevelRoot_le_self
  exact_mod_cast (show 1 <= X by omega)
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
theorem vaughanMean_le_middleLevel
    (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) (hqCubeX : Q ^ 3 <= X) :
    vaughanMean X Q <=
      200000 * vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 := by
  let u := middleLevelCutoff X
  have hxReal : (1 : Real) <= (X : Real) := by exact_mod_cast (show 1 <= X by omega)
  have hqReal : (1 : Real) <= (Q : Real) := by exact_mod_cast hQ
  have hqCubeXReal : (Q : Real) ^ 3 <= (X : Real) := by exact_mod_cast hqCubeX
  have hrootU : middleLevelRoot (X : Real) <= (u : Real) := by
    simpa [u] using middleLevelRoot_le_cutoff X
  have huRoot : (u : Real) <= middleLevelRoot (X : Real) + 1 := by
    exact (by simpa [u] using (middleLevelCutoff_lt_root_add_one X).le)
  have hx0 : (0 : Real) <= (X : Real) := by positivity
  have hmiddle :
      0 <= (X : Real) ^ (5 / 6 : Real) * (Q : Real) := by positivity
  have hlast : 0 <= Real.sqrt (X : Real) * (Q : Real) ^ 2 := by positivity
  have hmiddleLastScale :
      (X : Real) ^ (5 / 6 : Real) * (Q : Real) +
          Real.sqrt (X : Real) * (Q : Real) ^ 2 <= vaughanSourceScale X Q := by
    dsimp [vaughanSourceScale]
    linarith
  have hmiddleScale :
      (X : Real) ^ (5 / 6 : Real) * (Q : Real) <= vaughanSourceScale X Q := by
    dsimp [vaughanSourceScale]
    linarith
  have hxLastScale :
      (X : Real) + Real.sqrt (X : Real) * (Q : Real) ^ 2 <=
        vaughanSourceScale X Q := by
    dsimp [vaughanSourceScale]
    linarith
  apply vaughanMean_le_of_cutoff_bounds u X Q
  · simpa [u] using middleLevelCutoff_one_le X hX
  · simpa [u] using middleLevelCutoff_le X hX
  · exact hX
  · exact hQ
  · exact (middleLevelSmallTerm_le hxReal hqReal hqCubeXReal huRoot).trans
      hmiddleLastScale
  · exact (middleLevelInverseTerm_le hxReal hqReal hrootU).trans hmiddleScale
  · exact (middleLevelForwardTerm_le hxReal hqReal huRoot).trans hmiddleLastScale
  · exact (middleLevelShortTerm_le hxReal hqReal hqCubeXReal huRoot).trans hxLastScale
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
theorem outerRangeSqrtProduct_le {x q ell : Real}
    (hx : 0 <= x) (hq : 1 <= q) (hxq : x <= q ^ 2) (hell : 0 <= ell) :
    Real.sqrt (36 * (1 + q ^ 2)) *
        Real.sqrt (36 * (x + q ^ 2) * (x * ell ^ 2)) <=
      81 * Real.sqrt x * q ^ 2 * ell := by
  have hq0 : 0 <= q := by linarith
  have honeq : 1 <= q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  have hfirst : Real.sqrt (36 * (1 + q ^ 2)) <= 9 * q := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith
  have hxplus : x + q ^ 2 <= 2 * q ^ 2 := by linarith
  have hscaled := mul_le_mul_of_nonneg_right hxplus
    (mul_nonneg hx (sq_nonneg ell))
  have hsecondRad :
      36 * (x + q ^ 2) * (x * ell ^ 2) <=
        (9 * q * Real.sqrt x * ell) ^ 2 := by
    rw [show (9 * q * Real.sqrt x * ell) ^ 2 =
      81 * q ^ 2 * x * ell ^ 2 by
        rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hx]
        ring]
    have hterm : 0 <= q ^ 2 * (x * ell ^ 2) := by positivity
    calc
      _ = 36 * ((x + q ^ 2) * (x * ell ^ 2)) := by ring
      _ <= 36 * (2 * q ^ 2 * (x * ell ^ 2)) :=
        mul_le_mul_of_nonneg_left hscaled (by norm_num)
      _ <= 81 * q ^ 2 * x * ell ^ 2 := by nlinarith
  have hsecond : Real.sqrt (36 * (x + q ^ 2) * (x * ell ^ 2)) <=
      9 * q * Real.sqrt x * ell := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨by positivity, hsecondRad⟩
  calc
    _ <= (9 * q) * (9 * q * Real.sqrt x * ell) :=
      mul_le_mul hfirst hsecond (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring
theorem outerRangeLogProduct_le
    {sqrtTerm ell ellOne L S : Real}
    (hLhalf : 1 / 2 <= L) (hsqrt : 0 <= sqrtTerm)
    (hell : 0 <= ell) (hellOne : 0 <= ellOne) (hS : 0 <= S)
    (hsqrtS : sqrtTerm <= S) (hellL : ell <= L)
    (hellOneL : ellOne <= 2 * L) :
    (16 + 4 * ellOne) * (81 * sqrtTerm * ell) <=
      6480 * S * L ^ 3 := by
  have hL : 0 <= L := by linarith
  have hfactor0 : 0 <= 16 + 4 * ellOne := by linarith
  have hfactor : 16 + 4 * ellOne <= 40 * L := by linarith [hfactor0]
  have hproduct : sqrtTerm * ell <= S * L :=
    mul_le_mul hsqrtS hellL hell hS
  have hcore : 81 * sqrtTerm * ell <= 81 * S * L := by nlinarith
  have hcore0 : 0 <= 81 * sqrtTerm * ell := by positivity
  have hupper0 : 0 <= 40 * L := by positivity
  have hLsq : L ^ 2 <= 2 * L ^ 3 := by nlinarith [sq_nonneg L]
  calc
    _ <= (40 * L) * (81 * S * L) := by
      exact mul_le_mul hfactor hcore hcore0 hupper0
    _ = 3240 * S * L ^ 2 := by ring
    _ <= 6480 * S * L ^ 3 := by
      have hscaled := mul_le_mul_of_nonneg_left hLsq (by positivity : 0 <= 3240 * S)
      nlinarith
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
def outerRangeUnitCoefficient (_ : Nat) : Complex := 1
def outerRangeMangoldtCoefficient (n : Nat) : Complex :=
  (ArithmeticFunction.vonMangoldt n : Complex)
theorem outerRangeRestrictedSum_eq
    (X Y q : Nat) (chi : DirichletCharacter Complex q) (hYX : Y <= X) :
    restrictedBilinearCharacterSum outerRangeUnitCoefficient
        outerRangeMangoldtCoefficient 1 X Y q chi =
      psiCharacterSum Y q chi := by
  unfold restrictedBilinearCharacterSum psiCharacterSum
  simp [outerRangeUnitCoefficient, outerRangeMangoldtCoefficient]
  rw [← Finset.sum_filter]
  congr 1
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega
theorem maximalBilinearNorm_outerRange_eq
    (X q : Nat) (chi : DirichletCharacter Complex q) :
    maximalBilinearNorm outerRangeUnitCoefficient
        outerRangeMangoldtCoefficient 1 X X chi =
      maximalMangoldtCharacterNorm X q chi := by
  unfold maximalBilinearNorm maximalMangoldtCharacterNorm
  apply Finset.sup'_congr (H := by simp) rfl
  intro Y hY
  have hYX : Y <= X := Nat.le_of_lt_succ (Finset.mem_range.mp hY)
  rw [outerRangeRestrictedSum_eq X Y q chi hYX]
  rfl
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
theorem outerRangeUnitCoefficient_mass :
    coefficientMass outerRangeUnitCoefficient 1 = 1 := by
  simp [coefficientMass, outerRangeUnitCoefficient]
theorem outerRangeMangoldtCoefficient_norm_le
    (X n : Nat) (hn : n ∈ Finset.Icc 1 X) :
    ‖outerRangeMangoldtCoefficient n‖ <= Real.log (X : Real) := by
  have hnBounds := Finset.mem_Icc.mp hn
  rw [outerRangeMangoldtCoefficient, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  exact ArithmeticFunction.vonMangoldt_le_log.trans
    (Real.log_le_log (by exact_mod_cast (show 0 < n by omega))
      (by exact_mod_cast hnBounds.2))
theorem outerRangeMangoldtCoefficient_mass_le (X : Nat) :
    coefficientMass outerRangeMangoldtCoefficient X <=
      (X : Real) * Real.log (X : Real) ^ 2 := by
  unfold coefficientMass
  have hlog : 0 <= Real.log (X : Real) := Real.log_natCast_nonneg X
  calc
    ∑ n ∈ Icc 1 X, ‖outerRangeMangoldtCoefficient n‖ ^ 2 <=
        ∑ n ∈ Icc 1 X, Real.log (X : Real) ^ 2 := by
      apply Finset.sum_le_sum
      intro n hn
      nlinarith [norm_nonneg (outerRangeMangoldtCoefficient n),
        outerRangeMangoldtCoefficient_norm_le X n hn]
    _ = (X : Real) * Real.log (X : Real) ^ 2 := by simp
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
open Complex Finset Real
open scoped BigOperators
namespace BombieriVinogradov.VaughanMeanValue
theorem vaughanMean_le_outerRange
    (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) (hXQ : X <= Q ^ 2) :
    vaughanMean X Q <=
      6480 * vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 := by
  have hraw := weightedMaximalBilinear_le_cutoffFactor X 1 X Q
    outerRangeUnitCoefficient outerRangeMangoldtCoefficient hX hQ
  rw [positiveCoefficientMass_eq_coefficientMass,
    positiveCoefficientMass_eq_coefficientMass] at hraw
  simp_rw [maximalBilinearNorm_outerRange_eq] at hraw
  change vaughanMean X Q <= _ at hraw
  simp only [Nat.cast_one, outerRangeUnitCoefficient_mass, mul_one] at hraw
  have hcutoff : 0 <= 16 + 4 * Real.log ((X : Real) + 1) := by
    have hlog : 0 <= Real.log ((X : Real) + 1) := by
      apply Real.log_nonneg
      exact_mod_cast (show 1 <= X + 1 by omega)
    positivity
  have hmassSecond :
      Real.sqrt (36 * ((X : Real) + (Q : Real) ^ 2) *
          coefficientMass outerRangeMangoldtCoefficient X) <=
        Real.sqrt (36 * ((X : Real) + (Q : Real) ^ 2) *
          ((X : Real) * Real.log (X : Real) ^ 2)) := by
    apply Real.sqrt_le_sqrt
    exact mul_le_mul_of_nonneg_left
      (outerRangeMangoldtCoefficient_mass_le X) (by positivity)
  have hmassProduct :
      Real.sqrt (36 * ((1 : Real) + (Q : Real) ^ 2)) *
          Real.sqrt (36 * ((X : Real) + (Q : Real) ^ 2) *
            coefficientMass outerRangeMangoldtCoefficient X) <=
        Real.sqrt (36 * ((1 : Real) + (Q : Real) ^ 2)) *
          Real.sqrt (36 * ((X : Real) + (Q : Real) ^ 2) *
            ((X : Real) * Real.log (X : Real) ^ 2)) :=
    mul_le_mul_of_nonneg_left hmassSecond (Real.sqrt_nonneg _)
  have hraw' : vaughanMean X Q <=
      (16 + 4 * Real.log ((X : Real) + 1)) *
        (Real.sqrt (36 * ((1 : Real) + (Q : Real) ^ 2)) *
          Real.sqrt (36 * ((X : Real) + (Q : Real) ^ 2) *
            ((X : Real) * Real.log (X : Real) ^ 2))) := by
    simpa using hraw.trans (mul_le_mul_of_nonneg_left hmassProduct hcutoff)
  have hsqrtProduct :
      Real.sqrt (36 * ((1 : Real) + (Q : Real) ^ 2)) *
          Real.sqrt (36 * ((X : Real) + (Q : Real) ^ 2) *
            ((X : Real) * Real.log (X : Real) ^ 2)) <=
        81 * Real.sqrt (X : Real) * (Q : Real) ^ 2 * Real.log (X : Real) := by
    apply outerRangeSqrtProduct_le
    · positivity
    · exact_mod_cast hQ
    · exact_mod_cast hXQ
    · exact Real.log_natCast_nonneg X
  let S : Real := vaughanSourceScale X Q
  let L : Real := vaughanLogScale X Q
  have hS : 0 <= S := by dsimp [S, vaughanSourceScale]; positivity
  have hsqrtS : Real.sqrt (X : Real) * (Q : Real) ^ 2 <= S := by
    dsimp [S, vaughanSourceScale]
    have hfirst : 0 <= (X : Real) := by positivity
    have hmiddle : 0 <= (X : Real) ^ (5 / 6 : Real) * (Q : Real) := by positivity
    linarith
  have hlogs := outerRangeLogProduct_le
    (sqrtTerm := Real.sqrt (X : Real) * (Q : Real) ^ 2)
    (ell := Real.log (X : Real))
    (ellOne := Real.log ((X : Real) + 1))
    (L := L) (S := S)
    (by simpa [L] using half_le_vaughanLogScale X Q hX hQ)
    (by positivity) (Real.log_natCast_nonneg X)
    (by
      apply Real.log_nonneg
      exact_mod_cast (show 1 <= X + 1 by omega)) hS hsqrtS
    (by simpa [L] using log_X_le_vaughanLogScale X Q hX hQ)
    (by simpa [L, Nat.cast_add, Nat.cast_one] using
      log_X_add_one_le_two_vaughanLogScale X Q hX hQ)
  dsimp [S, L] at hlogs
  calc
    vaughanMean X Q <=
        (16 + 4 * Real.log ((X : Real) + 1)) *
          (Real.sqrt (36 * ((1 : Real) + (Q : Real) ^ 2)) *
            Real.sqrt (36 * ((X : Real) + (Q : Real) ^ 2) *
              ((X : Real) * Real.log (X : Real) ^ 2))) := hraw'
    _ <= (16 + 4 * Real.log ((X : Real) + 1)) *
        (81 * Real.sqrt (X : Real) * (Q : Real) ^ 2 * Real.log (X : Real)) :=
      mul_le_mul_of_nonneg_left hsqrtProduct hcutoff
    _ <= 6480 * vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 := by
      simpa [mul_assoc] using hlogs
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
theorem smallLevelSqrt_le_sq {q : Real} (hq : 1 <= q) :
    Real.sqrt q <= q ^ 2 := by
  have hq0 : 0 <= q := by linarith
  have hqSq : q <= q ^ 2 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)]
  have hqSqOne : 1 <= q ^ 2 := hq.trans hqSq
  have hqFourth : q ^ 2 <= (q ^ 2) ^ 2 := by
    nlinarith [mul_nonneg (sq_nonneg q) (sub_nonneg.mpr hqSqOne)]
  apply Real.sqrt_le_iff.mpr
  exact And.intro (sq_nonneg q) (hqSq.trans hqFourth)
theorem smallLevelSmallTerm_le {x q : Real}
    (hq : 1 <= q) (hqSixthX : q ^ 6 <= x) :
    q ^ 2 * q ^ 2 * Real.sqrt q <= x := by
  have hscaled := mul_le_mul_of_nonneg_left (smallLevelSqrt_le_sq hq)
    (show 0 <= q ^ 2 * q ^ 2 by positivity)
  calc
    q ^ 2 * q ^ 2 * Real.sqrt q <= q ^ 2 * q ^ 2 * q ^ 2 := hscaled
    _ = q ^ 6 := by ring
    _ <= x := hqSixthX
theorem smallLevelInverseTerm_eq {x q : Real} (hq : 1 <= q) :
    x * q / Real.sqrt (q ^ 2) = x := by
  have hq0 : 0 <= q := by linarith
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hq0]
  field_simp [show Ne q 0 by linarith]
theorem smallLevelForwardTerm_le {x q : Real}
    (hx : 0 <= x) (hq : 1 <= q) (hqSixthX : q ^ 6 <= x) :
    q ^ 2 * Real.sqrt x * q <= x := by
  have hq0 : 0 <= q := by linarith
  have hcube0 : 0 <= q ^ 3 := by positivity
  have hcube : q ^ 3 <= Real.sqrt x := by
    have hsqrt := Real.sqrt_le_sqrt hqSixthX
    rw [show q ^ 6 = (q ^ 3) ^ 2 by ring, Real.sqrt_sq_eq_abs,
      abs_of_nonneg hcube0] at hsqrt
    exact hsqrt
  have hscaled := mul_le_mul_of_nonneg_right hcube (Real.sqrt_nonneg x)
  calc
    q ^ 2 * Real.sqrt x * q = q ^ 3 * Real.sqrt x := by ring
    _ <= Real.sqrt x * Real.sqrt x := hscaled
    _ = x := by nlinarith [Real.sq_sqrt hx]
theorem smallLevelShortTerm_le {x q : Real}
    (hq : 1 <= q) (hqSixthX : q ^ 6 <= x) :
    q ^ 2 * q ^ 2 <= x := by
  have hq0 : 0 <= q := by linarith
  have hqSqOne : 1 <= q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  have hscaled := mul_le_mul_of_nonneg_left hqSqOne
    (show 0 <= q ^ 4 by positivity)
  calc
    q ^ 2 * q ^ 2 = q ^ 4 := by ring
    _ <= q ^ 4 * q ^ 2 := by simpa using hscaled
    _ = q ^ 6 := by ring
    _ <= x := hqSixthX
end BombieriVinogradov.VaughanMeanValue
end
end

section
namespace BombieriVinogradov.VaughanMeanValue
def smallLevelCutoff (Q : Nat) : Nat := Q ^ 2
theorem smallLevelCutoff_one_le (Q : Nat) (hQ : 1 <= Q) :
    1 <= smallLevelCutoff Q := by
  exact Nat.one_le_pow 2 Q (by omega)
theorem smallLevelCutoff_le (X Q : Nat) (hQ : 1 <= Q)
    (hqSixthX : Q ^ 6 <= X) :
    smallLevelCutoff Q <= X := by
  apply (Nat.pow_le_pow_right (by omega : 0 < Q) (by omega : 2 <= 6)).trans
  exact hqSixthX
end BombieriVinogradov.VaughanMeanValue
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
theorem vaughanMean_le_smallLevel
    (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) (hqSixthX : Q ^ 6 <= X) :
    vaughanMean X Q <=
      200000 * vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 := by
  let u := smallLevelCutoff Q
  have hqReal : (1 : Real) <= (Q : Real) := by exact_mod_cast hQ
  have hx0 : (0 : Real) <= (X : Real) := by positivity
  have hqSixthXReal : (Q : Real) ^ 6 <= (X : Real) := by exact_mod_cast hqSixthX
  have hxScale : (X : Real) <= vaughanSourceScale X Q := by
    dsimp [vaughanSourceScale]
    have hmiddle : 0 <= (X : Real) ^ (5 / 6 : Real) * (Q : Real) := by positivity
    have hlast : 0 <= Real.sqrt (X : Real) * (Q : Real) ^ 2 := by positivity
    linarith
  apply vaughanMean_le_of_cutoff_bounds u X Q
  · exact smallLevelCutoff_one_le Q hQ
  · exact smallLevelCutoff_le X Q hQ hqSixthX
  · exact hX
  · exact hQ
  · simpa [u, smallLevelCutoff, Nat.cast_pow] using
      (smallLevelSmallTerm_le hqReal hqSixthXReal).trans hxScale
  · calc
      (X : Real) * (Q : Real) / Real.sqrt (u : Real) = (X : Real) := by
        simpa [u, smallLevelCutoff, Nat.cast_pow] using
          (smallLevelInverseTerm_eq (x := (X : Real)) (q := (Q : Real)) hqReal)
      _ <= vaughanSourceScale X Q := hxScale
  · simpa [u, smallLevelCutoff, Nat.cast_pow] using
      (smallLevelForwardTerm_le hx0 hqReal hqSixthXReal).trans hxScale
  · simpa [u, smallLevelCutoff, Nat.cast_pow] using
      (smallLevelShortTerm_le hqReal hqSixthXReal).trans hxScale
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
def upperLevelRatio (x q : Real) : Real := x / q ^ 2
theorem upperLevelRatio_nonneg {x q : Real} (hx : 0 <= x) :
    0 <= upperLevelRatio x q := by
  exact div_nonneg hx (sq_nonneg q)
theorem upperLevelRatio_pos {x q : Real} (hx : 0 < x) (hq : 0 < q) :
    0 < upperLevelRatio x q := by
  exact div_pos hx (sq_pos_of_pos hq)
theorem one_le_upperLevelRatio {x q : Real}
    (hq : 0 < q) (hqSqX : q ^ 2 <= x) :
    1 <= upperLevelRatio x q := by
  rw [upperLevelRatio, le_div_iff₀ (sq_pos_of_pos hq)]
  simpa using hqSqX
theorem upperLevelRatio_le_self {x q : Real}
    (hx : 0 <= x) (hq : 1 <= q) :
    upperLevelRatio x q <= x := by
  have hqSqPos : 0 < q ^ 2 := sq_pos_of_pos (by linarith)
  have hqSqOne : 1 <= q ^ 2 := by nlinarith [sq_nonneg (q - 1)]
  rw [upperLevelRatio, div_le_iff₀ hqSqPos]
  exact le_mul_of_one_le_right hx hqSqOne
theorem upperLevelRatio_mul_sq {x q : Real} (hq : Ne q 0) :
    upperLevelRatio x q * q ^ 2 = x := by
  rw [upperLevelRatio]
  field_simp
theorem sqrt_upperLevelRatio {x q : Real}
    (hx : 0 <= x) (hq : 0 <= q) :
    Real.sqrt (upperLevelRatio x q) = Real.sqrt x / q := by
  rw [upperLevelRatio, Real.sqrt_div hx, Real.sqrt_sq_eq_abs, abs_of_nonneg hq]
theorem upperLevelSixth_le_sqrt {x q : Real}
    (hx : 0 <= x) (hq : 0 <= q) (hxCube : x <= q ^ 3) :
    x ^ (1 / 6 : Real) <= Real.sqrt q := by
  have hpow := Real.rpow_le_rpow hx hxCube (by norm_num : (0 : Real) <= 1 / 6)
  calc
    x ^ (1 / 6 : Real) <= (q ^ 3) ^ (1 / 6 : Real) := hpow
    _ = (Real.rpow q (3 : Real)) ^ (1 / 6 : Real) := by
      congr 1
      exact (Real.rpow_natCast q 3).symm
    _ = Real.rpow q ((3 : Real) * (1 / 6 : Real)) := by
      exact (Real.rpow_mul hq (3 : Real) (1 / 6 : Real)).symm
    _ = Real.sqrt q := by
      norm_num
      exact (Real.sqrt_eq_rpow q).symm
theorem upperLevelTwoThird_le_sq {x q : Real}
    (hx : 0 <= x) (hq : 0 <= q) (hxCube : x <= q ^ 3) :
    x ^ (2 / 3 : Real) <= q ^ 2 := by
  have hpow := Real.rpow_le_rpow hx hxCube (by norm_num : (0 : Real) <= 2 / 3)
  calc
    x ^ (2 / 3 : Real) <= (q ^ 3) ^ (2 / 3 : Real) := hpow
    _ = (Real.rpow q (3 : Real)) ^ (2 / 3 : Real) := by
      congr 1
      exact (Real.rpow_natCast q 3).symm
    _ = Real.rpow q ((3 : Real) * (2 / 3 : Real)) := by
      exact (Real.rpow_mul hq (3 : Real) (2 / 3 : Real)).symm
    _ = q ^ 2 := by
      norm_num
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
theorem upperLevelXSqrtQ_le {x q : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hxCube : x <= q ^ 3) :
    x * Real.sqrt q <= x ^ (5 / 6 : Real) * q := by
  have hx0 : 0 <= x := by linarith
  have hxpos : 0 < x := by linarith
  have hq0 : 0 <= q := by linarith
  have hsixth := upperLevelSixth_le_sqrt hx0 hq0 hxCube
  have hscaled := mul_le_mul_of_nonneg_right hsixth (Real.sqrt_nonneg q)
  have hroot : x ^ (1 / 6 : Real) * Real.sqrt q <= q := by
    nlinarith [Real.sq_sqrt hq0]
  have hfactor : x = x ^ (5 / 6 : Real) * x ^ (1 / 6 : Real) := by
    rw [← Real.rpow_add hxpos]
    norm_num
  calc
    x * Real.sqrt q =
        (x ^ (5 / 6 : Real) * x ^ (1 / 6 : Real)) * Real.sqrt q :=
      congrArg (fun t : Real => t * Real.sqrt q) hfactor
    _ = x ^ (5 / 6 : Real) * (x ^ (1 / 6 : Real) * Real.sqrt q) := by ring
    _ <= x ^ (5 / 6 : Real) * q :=
      mul_le_mul_of_nonneg_left hroot (Real.rpow_nonneg hx0 _)
theorem upperLevelRatioSqrtTerm_eq {x q : Real}
    (hx : 0 < x) (hq : Ne q 0) :
    upperLevelRatio x q * Real.sqrt x * q =
      x ^ (5 / 6 : Real) * (x ^ (2 / 3 : Real) / q) := by
  have hpowers :
      x ^ (5 / 6 : Real) * x ^ (2 / 3 : Real) = x * Real.sqrt x := by
    rw [← Real.rpow_add hx]
    rw [show (5 / 6 : Real) + 2 / 3 = 1 + 1 / 2 by norm_num,
      Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [upperLevelRatio]
  field_simp
  nlinarith
theorem upperLevelSmallTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hqSqX : q ^ 2 <= x) (hxCube : x <= q ^ 3)
    (hu : u <= upperLevelRatio x q + 1) :
    u * q ^ 2 * Real.sqrt q <=
      x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 := by
  have hx0 : 0 <= x := by linarith
  have hq0 : 0 <= q := by linarith
  have hqne : Ne q 0 := by linarith
  have hqSq : q <= q ^ 2 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)]
  have hqX : q <= x := hqSq.trans hqSqX
  have hsqrt := Real.sqrt_le_sqrt hqX
  have huScaled := mul_le_mul_of_nonneg_right hu
    (show 0 <= q ^ 2 * Real.sqrt q by positivity)
  have hfirst := upperLevelXSqrtQ_le hx hq hxCube
  have hsecond := mul_le_mul_of_nonneg_left hsqrt (sq_nonneg q)
  calc
    u * q ^ 2 * Real.sqrt q = u * (q ^ 2 * Real.sqrt q) := by ring
    _ <= (upperLevelRatio x q + 1) * (q ^ 2 * Real.sqrt q) := huScaled
    _ = upperLevelRatio x q * q ^ 2 * Real.sqrt q + q ^ 2 * Real.sqrt q := by ring
    _ = x * Real.sqrt q + q ^ 2 * Real.sqrt q := by
      rw [upperLevelRatio_mul_sq hqne]
    _ <= x ^ (5 / 6 : Real) * q + q ^ 2 * Real.sqrt x :=
      add_le_add hfirst hsecond
    _ = x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 := by ring
theorem upperLevelInverseTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hRatioU : upperLevelRatio x q <= u) :
    x * q / Real.sqrt u <= Real.sqrt x * q ^ 2 := by
  have hx0 : 0 <= x := by linarith
  have hxpos : 0 < x := by linarith
  have hq0 : 0 <= q := by linarith
  have hqpos : 0 < q := by linarith
  have huPos : 0 < u := (upperLevelRatio_pos hxpos hqpos).trans_le hRatioU
  have hsqrtUPos : 0 < Real.sqrt u := Real.sqrt_pos.2 huPos
  have hden : Real.sqrt x / q <= Real.sqrt u := by
    rw [← sqrt_upperLevelRatio hx0 hq0]
    exact Real.sqrt_le_sqrt hRatioU
  have hproduct : x * q <= Real.sqrt x * q ^ 2 * Real.sqrt u := by
    calc
      x * q = Real.sqrt x * q ^ 2 * (Real.sqrt x / q) := by
        field_simp
        nlinarith [Real.sq_sqrt hx0]
      _ <= Real.sqrt x * q ^ 2 * Real.sqrt u :=
        mul_le_mul_of_nonneg_left hden (by positivity)
  exact (div_le_iff₀ hsqrtUPos).mpr hproduct
theorem upperLevelForwardTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hxCube : x <= q ^ 3)
    (hu : u <= upperLevelRatio x q + 1) :
    u * Real.sqrt x * q <=
      x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 := by
  have hx0 : 0 <= x := by linarith
  have hxpos : 0 < x := by linarith
  have hq0 : 0 <= q := by linarith
  have hqpos : 0 < q := by linarith
  have htwoThird := upperLevelTwoThird_le_sq hx0 hq0 hxCube
  have hquotient : x ^ (2 / 3 : Real) / q <= q :=
    (div_le_iff₀ hqpos).mpr (by simpa [pow_two] using htwoThird)
  have hfirst := mul_le_mul_of_nonneg_left hquotient
    (Real.rpow_nonneg hx0 (5 / 6 : Real))
  have hqSq : q <= q ^ 2 := by
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq)]
  have hsecond := mul_le_mul_of_nonneg_left hqSq (Real.sqrt_nonneg x)
  have huScaled := mul_le_mul_of_nonneg_right hu
    (mul_nonneg (Real.sqrt_nonneg x) hq0)
  calc
    u * Real.sqrt x * q = u * (Real.sqrt x * q) := by ring
    _ <= (upperLevelRatio x q + 1) * (Real.sqrt x * q) := huScaled
    _ = upperLevelRatio x q * Real.sqrt x * q + Real.sqrt x * q := by ring
    _ = x ^ (5 / 6 : Real) * (x ^ (2 / 3 : Real) / q) +
        Real.sqrt x * q := by rw [upperLevelRatioSqrtTerm_eq hxpos (ne_of_gt hqpos)]
    _ <= x ^ (5 / 6 : Real) * q + Real.sqrt x * q ^ 2 :=
      add_le_add hfirst hsecond
theorem upperLevelShortTerm_le {x q u : Real}
    (hx : 1 <= x) (hq : 1 <= q) (hu : u <= upperLevelRatio x q + 1) :
    u * q ^ 2 <= x + Real.sqrt x * q ^ 2 := by
  have hq0 : 0 <= q := by linarith
  have hqne : Ne q 0 := by linarith
  have hsqrtOne : 1 <= Real.sqrt x := by
    have hsqrt := Real.sqrt_le_sqrt hx
    simpa using hsqrt
  have hlast := mul_le_mul_of_nonneg_right hsqrtOne (sq_nonneg q)
  have huScaled := mul_le_mul_of_nonneg_right hu (sq_nonneg q)
  calc
    u * q ^ 2 <= (upperLevelRatio x q + 1) * q ^ 2 := huScaled
    _ = x + q ^ 2 := by rw [add_mul, upperLevelRatio_mul_sq hqne, one_mul]
    _ <= x + Real.sqrt x * q ^ 2 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_left (by simpa using hlast) x
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
def upperLevelCutoff (X Q : Nat) : Nat :=
  Nat.ceil (upperLevelRatio (X : Real) (Q : Real))
theorem upperLevelCutoff_one_le (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) :
    1 <= upperLevelCutoff X Q := by
  apply Nat.one_le_ceil_iff.mpr
  apply upperLevelRatio_pos
  · exact_mod_cast (show 0 < X by omega)
  · exact_mod_cast (show 0 < Q by omega)
theorem upperLevelRatio_le_cutoff (X Q : Nat) :
    upperLevelRatio (X : Real) (Q : Real) <= (upperLevelCutoff X Q : Real) := by
  exact Nat.le_ceil _
theorem upperLevelCutoff_lt_ratio_add_one (X Q : Nat) :
    (upperLevelCutoff X Q : Real) <
      upperLevelRatio (X : Real) (Q : Real) + 1 := by
  exact Nat.ceil_lt_add_one (upperLevelRatio_nonneg (by positivity))
theorem upperLevelCutoff_le (X Q : Nat) (hQ : 1 <= Q) :
    upperLevelCutoff X Q <= X := by
  apply Nat.ceil_le.mpr
  apply upperLevelRatio_le_self
  · positivity
  · exact_mod_cast hQ
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
theorem vaughanMean_le_upperLevel
    (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q)
    (hqSqX : Q ^ 2 <= X) (hxCube : X <= Q ^ 3) :
    vaughanMean X Q <=
      200000 * vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 := by
  let u := upperLevelCutoff X Q
  have hxReal : (1 : Real) <= (X : Real) := by exact_mod_cast (show 1 <= X by omega)
  have hqReal : (1 : Real) <= (Q : Real) := by exact_mod_cast hQ
  have hqSqXReal : (Q : Real) ^ 2 <= (X : Real) := by exact_mod_cast hqSqX
  have hxCubeReal : (X : Real) <= (Q : Real) ^ 3 := by exact_mod_cast hxCube
  have hratioU : upperLevelRatio (X : Real) (Q : Real) <= (u : Real) := by
    simpa [u] using upperLevelRatio_le_cutoff X Q
  have huRatio : (u : Real) <= upperLevelRatio (X : Real) (Q : Real) + 1 := by
    exact (by simpa [u] using (upperLevelCutoff_lt_ratio_add_one X Q).le)
  have hx0 : (0 : Real) <= (X : Real) := by positivity
  have hmiddle :
      0 <= (X : Real) ^ (5 / 6 : Real) * (Q : Real) := by positivity
  have hlast : 0 <= Real.sqrt (X : Real) * (Q : Real) ^ 2 := by positivity
  have hmiddleLastScale :
      (X : Real) ^ (5 / 6 : Real) * (Q : Real) +
          Real.sqrt (X : Real) * (Q : Real) ^ 2 <= vaughanSourceScale X Q := by
    dsimp [vaughanSourceScale]
    linarith
  have hlastScale :
      Real.sqrt (X : Real) * (Q : Real) ^ 2 <= vaughanSourceScale X Q := by
    dsimp [vaughanSourceScale]
    linarith
  have hxLastScale :
      (X : Real) + Real.sqrt (X : Real) * (Q : Real) ^ 2 <=
        vaughanSourceScale X Q := by
    dsimp [vaughanSourceScale]
    linarith
  apply vaughanMean_le_of_cutoff_bounds u X Q
  · simpa [u] using upperLevelCutoff_one_le X Q hX hQ
  · simpa [u] using upperLevelCutoff_le X Q hQ
  · exact hX
  · exact hQ
  · exact (upperLevelSmallTerm_le hxReal hqReal hqSqXReal hxCubeReal huRatio).trans
      hmiddleLastScale
  · exact (upperLevelInverseTerm_le hxReal hqReal hratioU).trans hlastScale
  · exact (upperLevelForwardTerm_le hxReal hqReal hxCubeReal huRatio).trans
      hmiddleLastScale
  · exact (upperLevelShortTerm_le hxReal hqReal huRatio).trans hxLastScale
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
theorem vaughanMean_le_sourceScale_nat
    (X Q : Nat) (hX : 2 <= X) (hQ : 1 <= Q) :
    vaughanMean X Q <=
      200000 * vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 := by
  by_cases hOuter : X <= Q ^ 2
  · have hbound := vaughanMean_le_outerRange X Q hX hQ hOuter
    have hS : 0 <= vaughanSourceScale X Q := by
      dsimp [vaughanSourceScale]
      positivity
    have hL : 0 <= vaughanLogScale X Q :=
      (by norm_num : (0 : Real) <= 1 / 2).trans
        (half_le_vaughanLogScale X Q hX hQ)
    have hproduct : 0 <= vaughanSourceScale X Q * vaughanLogScale X Q ^ 3 :=
      mul_nonneg hS (pow_nonneg hL 3)
    have hconstants := mul_le_mul_of_nonneg_right
      (by norm_num : (6480 : Real) <= 200000) hproduct
    exact hbound.trans (by simpa [mul_assoc] using hconstants)
  · have hInner : Q ^ 2 <= X := by omega
    by_cases hSmall : Q ^ 6 <= X
    · exact vaughanMean_le_smallLevel X Q hX hQ hSmall
    · by_cases hMiddle : Q ^ 3 <= X
      · exact vaughanMean_le_middleLevel X Q hX hQ hMiddle
      · have hUpper : X <= Q ^ 3 := by omega
        exact vaughanMean_le_upperLevel X Q hX hQ hInner hUpper
end BombieriVinogradov.VaughanMeanValue
end
end

section

end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
theorem naturalScale_le_realScale
    (x : Real) (Q : Nat) (hx : 2 <= x) :
    vaughanSourceScale (Nat.floor x) Q <=
      x + x ^ (5 / 6 : Real) * (Q : Real) +
        x ^ (1 / 2 : Real) * (Q : Real) ^ 2 := by
  have hx0 : 0 <= x := by linarith
  have hfloor : ((Nat.floor x : Nat) : Real) <= x := Nat.floor_le hx0
  have hfloor0 : (0 : Real) <= (Nat.floor x : Nat) := by positivity
  have hq0 : (0 : Real) <= (Q : Real) := by positivity
  have hpow := Real.rpow_le_rpow hfloor0 hfloor
    (by norm_num : (0 : Real) <= 5 / 6)
  have hmiddle := mul_le_mul_of_nonneg_right hpow hq0
  have hsqrt : Real.sqrt ((Nat.floor x : Nat) : Real) <= x ^ (1 / 2 : Real) := by
    rw [← Real.sqrt_eq_rpow]
    exact Real.sqrt_le_sqrt hfloor
  have hlast := mul_le_mul_of_nonneg_right hsqrt (sq_nonneg (Q : Real))
  dsimp [vaughanSourceScale]
  linarith
theorem naturalLogScale_le_realLog
    (x : Real) (Q : Nat) (hx : 2 <= x) (hQ : 1 <= Q) :
    vaughanLogScale (Nat.floor x) Q <= Real.log (x * (Q : Real)) := by
  have hx0 : 0 <= x := by linarith
  have hfloor : ((Nat.floor x : Nat) : Real) <= x := Nat.floor_le hx0
  have hfloorNat : 2 <= Nat.floor x := Nat.le_floor hx
  have hq0 : (0 : Real) <= (Q : Real) := by positivity
  unfold vaughanLogScale
  apply Real.log_le_log
  · have hfloorPos : (0 : Real) < (Nat.floor x : Nat) := by exact_mod_cast (show 0 < Nat.floor x by omega)
    have hqPos : (0 : Real) < (Q : Real) := by exact_mod_cast (show 0 < Q by omega)
    positivity
  · exact mul_le_mul_of_nonneg_right hfloor hq0
theorem naturalMajorant_le_basicMeanValueMajorant
    (x : Real) (Q : Nat) (hx : 2 <= x) (hQ : 1 <= Q) :
    vaughanSourceScale (Nat.floor x) Q *
        vaughanLogScale (Nat.floor x) Q ^ 3 <=
      basicMeanValueMajorant x Q := by
  have hfloorNat : 2 <= Nat.floor x := Nat.le_floor hx
  have hsource := naturalScale_le_realScale x Q hx
  have hlog := naturalLogScale_le_realLog x Q hx hQ
  have hnaturalLog0 : 0 <= vaughanLogScale (Nat.floor x) Q :=
    (by norm_num : (0 : Real) <= 1 / 2).trans
      (half_le_vaughanLogScale (Nat.floor x) Q hfloorNat hQ)
  have hrealLog0 : 0 <= Real.log (x * (Q : Real)) := hnaturalLog0.trans hlog
  have hlogPow := pow_le_pow_left₀ hnaturalLog0 hlog 3
  have hrealScale0 :
      0 <= x + x ^ (5 / 6 : Real) * (Q : Real) +
        x ^ (1 / 2 : Real) * (Q : Real) ^ 2 := by positivity
  have hproduct := mul_le_mul hsource hlogPow
    (pow_nonneg hnaturalLog0 3) hrealScale0
  simpa [basicMeanValueMajorant] using hproduct
end BombieriVinogradov.VaughanMeanValue
end
end

section
noncomputable section
namespace BombieriVinogradov.VaughanMeanValue
theorem vaughanMeanValue : VaughanMeanValueStatement := by
  refine Exists.intro 200000 (And.intro (by norm_num) ?_)
  intro x Q hx hQ
  rw [primitivePsiMean_eq_vaughanMean]
  have hfloor : 2 <= Nat.floor x := Nat.le_floor hx
  have hnatural := vaughanMean_le_sourceScale_nat (Nat.floor x) Q hfloor hQ
  have hmajorant := naturalMajorant_le_basicMeanValueMajorant x Q hx hQ
  calc
    vaughanMean (Nat.floor x) Q <=
        200000 * vaughanSourceScale (Nat.floor x) Q *
          vaughanLogScale (Nat.floor x) Q ^ 3 := hnatural
    _ = 200000 * (vaughanSourceScale (Nat.floor x) Q *
          vaughanLogScale (Nat.floor x) Q ^ 3) := by ring
    _ <= 200000 * basicMeanValueMajorant x Q :=
      mul_le_mul_of_nonneg_left hmajorant (by norm_num)
end BombieriVinogradov.VaughanMeanValue
end
end

end

open Finset in
theorem OMA.solution : OMA.R_Erdos6_erdos_6_variants_increasing_R1_H1_R1_H2_R2.H2 := by
  classical
  obtain ⟨C, hC, hb⟩ := BombieriVinogradov.VaughanMeanValue.vaughanMeanValue
  unfold OMA.R_Erdos6_erdos_6_variants_increasing_R1_H1_R1_H2_R2.H2
  dsimp only
  refine ⟨C, hC, ?_⟩
  intro x k hx hk
  have hxr : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have key := hb (x : ℝ) k hxr hk
  unfold BombieriVinogradov.VaughanMeanValue.primitivePsiMean
    BombieriVinogradov.VaughanMeanValue.basicMeanValueMajorant at key
  have hfl : ⌊(x : ℝ)⌋₊ = x := Nat.floor_natCast x
  refine le_trans ?_ (le_of_le_of_eq key (by ring))
  apply Finset.sum_le_sum
  intro d hd
  have hS : (∑ χ ∈ ((Finset.univ.filter
      (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).erase 1),
        (Finset.range (x+1)).sup' (by simp) (fun y => ‖∑ n ∈ Icc 1 y,
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d)‖)) ≤
      ∑ χ ∈ BombieriVinogradov.LargeSieve.primitiveCharacters d,
        BombieriVinogradov.VaughanMeanValue.maximalPsiNorm (x : ℝ) χ := by
    have heq : ∀ χ : DirichletCharacter ℂ d,
        (Finset.range (x+1)).sup' (by simp) (fun y => ‖∑ n ∈ Icc 1 y,
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d)‖) =
        BombieriVinogradov.VaughanMeanValue.maximalPsiNorm (x : ℝ) χ := by
      intro χ
      unfold BombieriVinogradov.VaughanMeanValue.maximalPsiNorm
        BombieriVinogradov.VaughanMeanValue.psiCharacterSum
      simp only [hfl]
    rw [Finset.sum_congr rfl (fun χ _ => heq χ)]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro χ hχ
      have h1 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hχ)).2
      unfold BombieriVinogradov.LargeSieve.primitiveCharacters
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩
    · intro χ _ _
      rw [← heq χ]
      exact le_trans (norm_nonneg _)
        (Finset.le_sup' (fun y => ‖∑ n ∈ Icc 1 y,
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d)‖)
          (Finset.mem_range.mpr (Nat.succ_pos x)))
  have hφ : (0 : ℝ) ≤ (d : ℝ) / (d.totient : ℝ) := by positivity
  calc (d : ℝ) * ((∑ χ ∈ ((Finset.univ.filter
      (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).erase 1),
        (Finset.range (x+1)).sup' (by simp) (fun y => ‖∑ n ∈ Icc 1 y,
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d)‖)) / (d.totient : ℝ))
      = ((d : ℝ) / (d.totient : ℝ)) * (∑ χ ∈ ((Finset.univ.filter
      (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive)).erase 1),
        (Finset.range (x+1)).sup' (by simp) (fun y => ‖∑ n ∈ Icc 1 y,
          (ArithmeticFunction.vonMangoldt n : ℂ) * χ (n : ZMod d)‖)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hS hφ
