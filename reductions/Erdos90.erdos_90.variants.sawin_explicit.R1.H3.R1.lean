import OMAReductions.R_Erdos90_erdos_90_variants_sawin_explicit_R1

/-! Will Sawin, "An explicit lower bound for the unit distance problem",
arXiv:2605.20579, Lemmas 6 and 9. We separate the algebra of integral ideals
and units, the norm index on ideal classes, and the relative class-number
estimate. In the algebraic count we retain both elements of each pair ±β. -/
namespace OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1
open NumberField
open scoped nonZeroDivisors

/-- An equal-norm ideal family gives distinct norm-one scalars. The index is
that of the ideal norm on class groups; its defining values are specified so
this statement does not require a choice of class-group model. -/
def H1 : Prop :=
  ∀ (F K : Type) [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [Algebra.IsQuadraticExtension F K],
    ∃ T : ClassGroup (𝓞 K) →* ClassGroup (𝓞 F),
      (∀ I : (Ideal (𝓞 K))⁰, ∃ J : (Ideal (𝓞 F))⁰,
        J.val = Ideal.relNorm (𝓞 F) I.val ∧ T (ClassGroup.mk0 I) = ClassGroup.mk0 J) ∧
      ∀ L : Finset (Ideal (𝓞 K)), L.Nonempty → (∀ I ∈ L, I ≠ ⊥) →
        (∀ I ∈ L, ∀ J ∈ L, Ideal.relNorm (𝓞 F) I = Ideal.relNorm (𝓞 F) J) →
        ∃ J₀ ∈ L, ∃ B : Finset K,
          (∀ β ∈ B, (∀ a ∈ J₀, ∃ b : 𝓞 K,
            algebraMap (𝓞 K) K b = β * algebraMap (𝓞 K) K a) ∧ Algebra.norm F β = 1) ∧
          2 * L.card * classNumber F ≤
            B.card * 2 ^ (Module.finrank ℚ F) * classNumber K * T.range.index

/-- The image of the norm on ordinary ideal classes has index at most the
extension degree (here two). This is the class-field-theoretic input. -/
def H2 : Prop :=
  ∀ (F K : Type) [Field F] [NumberField F] [IsTotallyReal F]
    [Field K] [NumberField K] [IsTotallyComplex K]
    [Algebra F K] [Algebra.IsQuadraticExtension F K]
    (T : ClassGroup (𝓞 K) →* ClassGroup (𝓞 F)),
    (∀ I : (Ideal (𝓞 K))⁰, ∃ J : (Ideal (𝓞 F))⁰,
      J.val = Ideal.relNorm (𝓞 F) I.val ∧ T (ClassGroup.mk0 I) = ClassGroup.mk0 J) →
    T.range.index ≤ 2

/-- Louboutin's bound for the relative class number, with the explicit
parameters used in Sawin's Lemma 9. -/
def H3 : Prop :=
  ∀ (F K : Type) [Field F] [CharZero F] [NumberField F] [IsTotallyReal F]
    [Field K] [CharZero K] [NumberField K] [IsTotallyComplex K]
    [Algebra F K] [Algebra.IsQuadraticExtension F K] (lam : ℝ), 1 < lam →
    |(discr K : ℝ)| / |(discr F : ℝ)| ≤ lam ^ (Module.finrank ℚ F) →
    (classNumber K : ℝ) ≤ (classNumber F : ℝ) *
      (8 * lam ^ 2 * (Real.sqrt lam * Real.log lam * (Real.exp 1 / (4 * Real.pi))) ^
        (Module.finrank ℚ F))

theorem main : H1 → H2 → H3 → OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1.H3 := by
  intro algebra index classbound F K _ _ _ _ _ _ _ _ _ _ lam hlam hdisc L inh nz same
  obtain ⟨T,spec,build⟩ := algebra F K
  obtain ⟨J,hJ,B,ok,bound⟩ := build L inh nz same
  refine ⟨J,hJ,B,ok,?_⟩
  have doubled := bound.trans (Nat.mul_le_mul_left _ (index F K T spec))
  have nbound : L.card * classNumber F ≤ B.card * 2^(Module.finrank ℚ F) * classNumber K := by
    rw [Nat.mul_assoc, Nat.mul_comm _ 2] at doubled
    omega
  have rb : (L.card : ℝ) * classNumber F ≤
      (B.card : ℝ) * 2^(Module.finrank ℚ F) * classNumber K := by exact_mod_cast nbound
  apply le_of_mul_le_mul_right (a := (classNumber F : ℝ)) _ (Nat.cast_pos.mpr (classNumber_pos F))
  calc _ ≤ _ := rb
       _ ≤ _ := mul_le_mul_of_nonneg_left (classbound F K lam hlam hdisc)
                  (by positivity : 0 ≤ (B.card : ℝ) * 2 ^ (Module.finrank ℚ F))
       _ = _ := by ring

end OMA.R_Erdos90_erdos_90_variants_sawin_explicit_R1_H3_R1
