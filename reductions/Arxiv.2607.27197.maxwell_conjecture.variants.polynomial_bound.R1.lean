import FormalConjectures.Arxiv.«2607.27197».MaxwellConjecture
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
For collinear charges a nondegenerate equilibrium lies on the common line.
Order the sites by their line parameters. On each sign region the zeros
of the projected field are roots of a nonzero polynomial of degree at
most 2(n−1). Multiplying these polynomials yields the bound 2(n²−1).
For noncollinear charges with proper affine span, the reduction
separates equilibria in the span from balanced equilibria off it.

The Coulomb derivative and Hessian argument adapt the merged three-charge
reduction by brandonyee-cs to an arbitrary number of charges.
-/

open InnerProductSpace Polynomial
open scoped RealInnerProductSpace Gradient BigOperators

namespace OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_polynomial_bound_R1
open Arxiv.«2607.27197»

/-- Equilibria in the proper affine span of noncollinear configurations. -/
def H1 : Prop :=
  ∃ C d : ℕ, ∀ (n : ℕ), 0 < n → ∀ (q : Fin n → ℝ) (a : Fin n → EuclideanSpace ℝ (Fin 3)),
    Function.Injective a → (∀ j, q j ≠ 0) →
    (∀ x ∈ equilibria q a, HasNondegenerateHessianAt (potential q a) x) →
    ¬ Collinear ℝ (Set.range a) → affineSpan ℝ (Set.range a) ≠ ⊤ →
    (equilibria q a ∩ (affineSpan ℝ (Set.range a) : Set _)).encard ≤ (C * n ^ d : ℕ)

/-- Balanced equilibria off the proper affine span of noncollinear configurations. -/
def H2 : Prop :=
  ∃ C d : ℕ, ∀ (n : ℕ), 0 < n → ∀ (q : Fin n → ℝ) (a : Fin n → EuclideanSpace ℝ (Fin 3)),
    Function.Injective a → (∀ j, q j ≠ 0) →
    (∀ x ∈ equilibria q a, HasNondegenerateHessianAt (potential q a) x) →
    ¬ Collinear ℝ (Set.range a) → affineSpan ℝ (Set.range a) ≠ ⊤ →
    {x ∈ equilibria q a | x ∉ affineSpan ℝ (Set.range a) ∧
      (∑ j, q j / ‖x - a j‖^3) = 0 ∧
      (∑ j, (q j / ‖x - a j‖^3) • a j) = 0}.encard ≤ (C * n ^ d : ℕ)

/-- Configurations with full affine span in three dimensions. -/
def H3 : Prop :=
  ∃ C d : ℕ, ∀ (n : ℕ), 0 < n → ∀ (q : Fin n → ℝ) (a : Fin n → EuclideanSpace ℝ (Fin 3)),
    Function.Injective a → (∀ j, q j ≠ 0) →
    (∀ x ∈ equilibria q a, HasNondegenerateHessianAt (potential q a) x) →
    affineSpan ℝ (Set.range a) = ⊤ →
    (equilibria q a).encard ≤ (C * n ^ d : ℕ)

section Proof

private lemma charge_hasGradient (q : ℝ) (a x : (EuclideanSpace ℝ (Fin 3))) (hxa : x ≠ a) :
    HasGradientAt (fun y : (EuclideanSpace ℝ (Fin 3)) => q / dist y a) ((-q / ‖x-a‖^3) • (x-a)) x := by
  have hn : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hs : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖^2) (2 • innerSL ℝ (x-a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq
  have hd : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖) (‖x-a‖⁻¹ • innerSL ℝ (x-a)) x := by
    convert! hs.sqrt (pow_ne_zero 2 hn) using 1
    · funext y; exact (Real.sqrt_sq (norm_nonneg _)).symm
    · simp only [Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 1
      field_simp
      norm_num
  have hi := ((hasDerivAt_inv hn).comp_hasFDerivAt x hd).const_mul q
  apply hasGradientAt_iff_hasFDerivAt.mpr
  convert! hi using 1
  ext v
  simp [div_eq_mul_inv, toDual_apply_apply, smul_smul]
  field_simp [hn]
  simp

private lemma potential_hasGradient {n : ℕ} (q : Fin n → ℝ) (a : Fin n → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3))) (hx : x ∉ Set.range a) :
    HasGradientAt (Arxiv.«2607.27197».potential q a) (-((∑ j, (q j / ‖x - a j‖^3) • (x - a j)))) x := by
  have hn (j : Fin n) : x ≠ a j := fun h => hx ⟨j, h.symm⟩
  apply hasGradientAt_iff_hasFDerivAt.mpr
  have hf : Arxiv.«2607.27197».potential q a = fun y => ∑ j, q j / dist y (a j) := rfl
  rw [hf]
  have := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => (charge_hasGradient (q j) (a j) x (hn j)).hasFDerivAt)
  have key : (toDual ℝ (EuclideanSpace ℝ (Fin 3))) (-((∑ j, (q j / ‖x - a j‖^3) • (x - a j)))) =
      ∑ i, (toDual ℝ (EuclideanSpace ℝ (Fin 3))) ((-q i / ‖x - a i‖ ^ 3) • (x - a i)) := by
    rw [← Finset.sum_neg_distrib, map_sum]
    simp only [neg_div, neg_smul]
  rw [key]
  exact this

private lemma mem_equilibria_iff {n : ℕ} (q : Fin n → ℝ) (a : Fin n → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3))) :
    x ∈ Arxiv.«2607.27197».equilibria q a ↔ x ∉ Set.range a ∧ (∑ j, (q j / ‖x - a j‖^3) • (x - a j)) = 0 := by
  constructor
  · rintro ⟨hx, hg⟩
    refine ⟨hx, ?_⟩
    have := (potential_hasGradient q a x hx).gradient
    rw [hg] at this
    exact neg_eq_zero.mp this.symm
  · rintro ⟨hx, hg⟩
    refine ⟨hx, ?_⟩
    rw [(potential_hasGradient q a x hx).gradient, hg, neg_zero]


private lemma norm_sub_hasFDerivAt (a x : (EuclideanSpace ℝ (Fin 3))) (hxa : x ≠ a) :
    HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖) (‖x-a‖⁻¹ • innerSL ℝ (x-a)) x := by
  have hn : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hs : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖^2) (2 • innerSL ℝ (x-a)) x := by
    simpa using ((hasFDerivAt_id x).sub_const a).norm_sq
  convert! hs.sqrt (pow_ne_zero 2 hn) using 1
  · funext y; exact (Real.sqrt_sq (norm_nonneg _)).symm
  · simp only [Real.sqrt_sq (norm_nonneg _), ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    congr 1
    field_simp
    norm_num

/-- the coefficient `q / ‖y - a‖^3` has a derivative that kills every vector orthogonal to `x - a`. -/
private lemma coeff_hasFDerivAt (q : ℝ) (a x : (EuclideanSpace ℝ (Fin 3))) (hxa : x ≠ a) :
    ∃ C : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ, HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => q / ‖y-a‖^3) C x ∧
      ∀ u : (EuclideanSpace ℝ (Fin 3)), ⟪x - a, u⟫ = 0 → C u = 0 := by
  have hn : ‖x-a‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxa)
  have hg : DifferentiableAt ℝ (fun r : ℝ => q / r^3) ‖x-a‖ :=
    (differentiableAt_const q).div (differentiableAt_pow 3) (pow_ne_zero 3 hn)
  refine ⟨deriv (fun r : ℝ => q / r^3) ‖x-a‖ • (‖x-a‖⁻¹ • innerSL ℝ (x-a)), ?_, ?_⟩
  · have h := hg.hasDerivAt.comp_hasFDerivAt (f := fun y : (EuclideanSpace ℝ (Fin 3)) => ‖y-a‖) x
      (norm_sub_hasFDerivAt a x hxa)
    exact h
  · intro u hu
    rw [smul_apply, smul_apply, innerSL_apply_apply, hu]
    simp

private lemma field_hasFDerivAt {n : ℕ} (q : Fin n → ℝ) (a : Fin n → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3))) (hx : x ∉ Set.range a) :
    ∃ D : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (EuclideanSpace ℝ (Fin 3)), HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => (∑ j, (q j / ‖y - a j‖^3) • (y - a j))) D x ∧
      ∀ u : (EuclideanSpace ℝ (Fin 3)), (∀ j, ⟪x - a j, u⟫ = 0) → D u = (∑ j, q j / ‖x - a j‖^3) • u := by
  have hn (j : Fin n) : x ≠ a j := fun h => hx ⟨j, h.symm⟩
  choose C hC hCu using fun j => coeff_hasFDerivAt (q j) (a j) x (hn j)
  have hj (j : Fin n) : HasFDerivAt (fun y : (EuclideanSpace ℝ (Fin 3)) => (q j / ‖y - a j‖^3) • (y - a j))
      ((q j / ‖x - a j‖^3) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) + (C j).smulRight (x - a j)) x :=
    (hC j).fun_smul ((hasFDerivAt_id x).sub_const (a j))
  refine ⟨∑ j, ((q j / ‖x - a j‖^3) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 3)) + (C j).smulRight (x - a j)),
    ?_, ?_⟩
  · have := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => hj j)
    exact this
  · intro u hu
    simp only [FunLike.coe_sum, Finset.sum_apply, add_apply,
      FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.coe_id', id_eq,
      ContinuousLinearMap.smulRight_apply, hCu _ u (hu _), zero_smul, add_zero, Finset.sum_smul]

/-- **Lemma D**: an equilibrium at which some nonzero `u` is orthogonal to all `x - a j` while
`∑ q j / r_j^3 = 0` is degenerate. -/
private lemma not_nondegenerate {n : ℕ} (q : Fin n → ℝ) (a : Fin n → (EuclideanSpace ℝ (Fin 3))) (x : (EuclideanSpace ℝ (Fin 3))) (hx : x ∉ Set.range a)
    (u : (EuclideanSpace ℝ (Fin 3))) (hu : u ≠ 0) (horth : ∀ j, ⟪x - a j, u⟫ = 0)
    (hsum : ∑ j, q j / ‖x - a j‖^3 = 0) :
    ¬ Arxiv.«2607.27197».HasNondegenerateHessianAt (Arxiv.«2607.27197».potential q a) x := by
  intro hnd
  obtain ⟨D, hD, hDu⟩ := field_hasFDerivAt q a x hx
  have hopen : IsOpen (Set.range a)ᶜ := (Set.finite_range a).isClosed.isOpen_compl
  have hev : fderiv ℝ (Arxiv.«2607.27197».potential q a) =ᶠ[nhds x]
      fun y => -(innerSL ℝ ((∑ j, (q j / ‖y - a j‖^3) • (y - a j)))) := by
    filter_upwards [hopen.mem_nhds hx] with y hy
    rw [(potential_hasGradient q a y hy).hasFDerivAt.fderiv]
    ext w
    simp [toDual_apply_apply, innerSL_apply_apply]
  have hF : HasFDerivAt (fun y => -(innerSL ℝ ((∑ j, (q j / ‖y - a j‖^3) • (y - a j))))) (-((innerSL ℝ).comp D)) x :=
    (((innerSL ℝ : (EuclideanSpace ℝ (Fin 3)) →L[ℝ] (EuclideanSpace ℝ (Fin 3)) →L[ℝ] ℝ).hasFDerivAt).comp x hD).neg
  obtain ⟨w, hw⟩ := hnd u hu
  apply hw
  rw [iteratedFDeriv_two_apply, hev.fderiv_eq, hF.fderiv]
  simp [hDu u horth, hsum]

private lemma exists_orth (d v : (EuclideanSpace ℝ (Fin 3))) : ∃ u : (EuclideanSpace ℝ (Fin 3)), u ≠ 0 ∧ ⟪d, u⟫ = 0 ∧ ⟪v, u⟫ = 0 := by
  set K : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) := Submodule.span ℝ (Set.range ![d, v])
  have hK : Module.finrank ℝ K ≤ 2 := by
    have := finrank_range_le_card (R := ℝ) ![d, v]
    simpa [Set.finrank] using this
  have hsum := Submodule.finrank_add_finrank_orthogonal K
  rw [finrank_euclideanSpace_fin] at hsum
  have hne : Kᗮ ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hsum
    omega
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  refine ⟨u, hu0, ?_, ?_⟩
  · exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (show d ∈ Set.range ![d, v] from ⟨0, rfl⟩)) hu
  · exact Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (show v ∈ Set.range ![d, v] from ⟨1, rfl⟩)) hu

private lemma signs_eq_of_card_eq {n : ℕ} (r : Fin n → ℝ) {s t : ℝ}
    (h : (Finset.univ.filter (fun j => r j < s)).card =
      (Finset.univ.filter (fun j => r j < t)).card) :
    ∀ j, r j < s ↔ r j < t := by
  classical
  have hsub {u v : ℝ} (huv : u ≤ v) :
      Finset.univ.filter (fun j => r j < u) ⊆ Finset.univ.filter (fun j => r j < v) := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    exact hj.trans_le huv
  have heq : Finset.univ.filter (fun j => r j < s) =
      Finset.univ.filter (fun j => r j < t) := by
    rcases le_total s t with hst | hts
    · exact Finset.eq_of_subset_of_card_le (hsub hst) h.ge
    · exact (Finset.eq_of_subset_of_card_le (hsub hts) h.le).symm
  intro j
  simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using
    (show (j ∈ Finset.univ.filter (fun i => r i < s)) ↔
      j ∈ Finset.univ.filter (fun i => r i < t) by rw [heq])

private lemma signed_term (q u : ℝ) (hu : u ≠ 0) :
    q / |u|^3 * u = (if 0 < u then q else -q) / u^2 := by
  by_cases h : 0 < u
  · rw [if_pos h, abs_of_pos h]
    field_simp
  · rw [if_neg h, abs_of_neg (lt_of_le_of_ne (le_of_not_gt h) hu)]
    field_simp

/-- A single nonzero polynomial vanishes at every zero of the field on the
line away from the charges. Its factors are indexed by the number of
charges to the left. -/
private lemma axis_polynomial_bound {n : ℕ} (hn : 0 < n) (r q : Fin n → ℝ)
    (hr : Function.Injective r) (hq : ∀ j, q j ≠ 0) :
    {s : ℝ | (∀ j, s ≠ r j) ∧ ∑ j, q j / |s - r j|^3 * (s - r j) = 0}.encard ≤
      ((n + 1) * (2 * (n - 1)) : ℕ) := by
  classical
  let index (s : ℝ) : Fin (n + 1) :=
    ⟨(Finset.univ.filter (fun j => r j < s)).card, by
      have h := Finset.card_le_univ (Finset.univ.filter (fun j => r j < s))
      exact Nat.lt_succ_of_le (by simpa using h)⟩
  let rep (k : Fin (n + 1)) : ℝ := if h : ∃ s, index s = k then h.choose else 0
  have hrep (s : ℝ) : index (rep (index s)) = index s := by
    have h : ∃ u, index u = index s := ⟨s, rfl⟩
    simpa only [rep, dif_pos h] using h.choose_spec
  let coeff (k : Fin (n + 1)) (j : Fin n) : ℝ := if r j < rep k then q j else -q j
  let D (j : Fin n) : ℝ[X] := (Polynomial.X - Polynomial.C (r j)) ^ 2
  let cell (k : Fin (n + 1)) : ℝ[X] :=
    ∑ j, Polynomial.C (coeff k j) * ∏ i ∈ Finset.univ.erase j, D i
  have heval (k : Fin (n + 1)) (s : ℝ) :
      Polynomial.eval s (cell k) = ∑ j, coeff k j * ∏ i ∈ Finset.univ.erase j, (s - r i)^2 := by
    simp only [cell, D, Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_prod,
      Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X]
  have hnonzero (k : Fin (n + 1)) : cell k ≠ 0 := by
    let j : Fin n := ⟨0, hn⟩
    have he : Polynomial.eval (r j) (cell k) =
        coeff k j * ∏ i ∈ Finset.univ.erase j, (r j - r i)^2 := by
      rw [heval, Finset.sum_eq_single j]
      · intro i hi hij
        have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
        rw [Finset.prod_eq_zero hmem (by simp), mul_zero]
      · simp
    have hcoeff : coeff k j ≠ 0 := by
      dsimp only [coeff]
      split <;> simp [hq j]
    have hproduct : (∏ i ∈ Finset.univ.erase j, (r j - r i)^2) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro i hi
      exact pow_ne_zero _ (sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hi).1 ((hr h).symm)))
    intro hzero
    rw [hzero, Polynomial.eval_zero] at he
    exact (mul_ne_zero hcoeff hproduct) he.symm
  have hdegree (k : Fin (n + 1)) : (cell k).natDegree ≤ 2 * (n - 1) := by
    dsimp only [cell]
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    refine Polynomial.natDegree_mul_le.trans ?_
    rw [Polynomial.natDegree_C, zero_add]
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    have hD (i : Fin n) : (D i).natDegree ≤ 2 := by
      dsimp only [D]
      exact Polynomial.natDegree_pow_le.trans (by rw [Polynomial.natDegree_X_sub_C, mul_one])
    refine (Finset.sum_le_sum (fun i _ => hD i)).trans_eq ?_
    simp [Finset.card_erase_of_mem, Finset.mem_univ, Fintype.card_fin, Nat.mul_comm]
  let P : ℝ[X] := ∏ k, cell k
  have hP : P ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun k _ => hnonzero k)
  have hPd : P.natDegree ≤ (n + 1) * (2 * (n - 1)) := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    calc
      _ ≤ ∑ _ : Fin (n + 1), 2 * (n - 1) := Finset.sum_le_sum (fun k _ => hdegree k)
      _ = _ := by simp [Finset.sum_const, Fintype.card_fin]
  have hroot (s : ℝ) (hs : ∀ j, s ≠ r j)
      (hf : ∑ j, q j / |s - r j|^3 * (s - r j) = 0) : Polynomial.eval s P = 0 := by
    have hsign := signs_eq_of_card_eq r (s := rep (index s)) (t := s)
      (congrArg Fin.val (hrep s))
    have hsigned : ∑ j, coeff (index s) j / (s - r j)^2 = 0 := by
      rw [← hf]
      apply Finset.sum_congr rfl
      intro j _
      rw [signed_term (q j) (s - r j) (sub_ne_zero.mpr (hs j))]
      simp only [coeff, hsign j, sub_pos]
    let den := ∏ i, (s - r i)^2
    have hcell : Polynomial.eval s (cell (index s)) = den * ∑ j, coeff (index s) j / (s - r j)^2 := by
      rw [heval, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hsplit : (∏ i ∈ Finset.univ.erase j, (s - r i)^2) * (s - r j)^2 = den :=
        Finset.prod_erase_mul _ _ (Finset.mem_univ j)
      rw [← hsplit]
      field_simp [sub_ne_zero.mpr (hs j)]
    dsimp only [P]
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ (index s)) (by rw [hcell, hsigned, mul_zero])
  calc
    _ ≤ ((P.roots.toFinset : Finset ℝ) : Set ℝ).encard := by
      apply Set.encard_le_encard
      rintro s ⟨hs, hf⟩
      exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hP).mpr (hroot s hs hf))
    _ = (P.roots.toFinset.card : ℕ∞) := Set.encard_coe_eq_coe_finsetCard _
    _ ≤ (P.natDegree : ℕ∞) := by
      exact_mod_cast (Multiset.toFinset_card_le _).trans (Polynomial.card_roots' P)
    _ ≤ _ := by exact_mod_cast hPd

private lemma nonempty_axis_parameter_bound {n : ℕ} (hn : 0 < n)
    (q : Fin n → ℝ) (a : Fin n → EuclideanSpace ℝ (Fin 3))
    (hq : ∀ j, q j ≠ 0)
    (ha : Function.Injective a) (hcol : Collinear ℝ (Set.range a)) :
    (nondegenerateEquilibria q a).encard ≤ ((n + 1) * (2 * (n - 1)) : ℕ) := by
  by_cases hn1 : n = 1
  · subst n
    have hnone : equilibria q a = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨hxa, hf⟩ := (mem_equilibria_iff q a x).mp hx
      have hx0 : x - a 0 ≠ 0 := sub_ne_zero.mpr fun h => hxa ⟨0, h.symm⟩
      rw [Fin.sum_univ_one] at hf
      exact (div_ne_zero (hq 0) (pow_ne_zero _ (norm_ne_zero_iff.mpr hx0)))
        ((smul_eq_zero.mp hf).resolve_right hx0)
    simp [nondegenerateEquilibria, hnone]
  have hn2 : 1 < n := by omega
  obtain ⟨p₀, v, hv⟩ := (collinear_iff_exists_forall_eq_smul_vadd _).mp hcol
  choose r hr using fun j => hv (a j) ⟨j, rfl⟩
  simp only [vadd_eq_add] at hr
  have hrinj : Function.Injective r := by
    intro i j hij
    exact ha (by rw [hr i, hr j, hij])
  have hv0 : v ≠ 0 := by
    intro h0
    let i : Fin n := ⟨0, hn⟩
    let j : Fin n := ⟨1, hn2⟩
    have hij : i ≠ j := by
      intro h
      have := congrArg Fin.val h
      simp only [i, j] at this
      omega
    exact hij (ha (by rw [hr i, hr j, h0]; simp))
  have hvv : ⟪v, v⟫ ≠ 0 := by
    rw [real_inner_self_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hv0)
  let g : EuclideanSpace ℝ (Fin 3) → ℝ := fun x => ⟪x - p₀, v⟫ / ⟪v, v⟫
  have hline : ∀ x ∈ nondegenerateEquilibria q a, x = g x • v + p₀ := by
    intro x hx
    by_contra hoff
    have hx' := (mem_equilibria_iff q a x).mp hx.1
    let d := x - p₀
    let c : Fin n → ℝ := fun j => q j / ‖x - a j‖^3
    have hxa (j : Fin n) : x - a j = d - r j • v := by rw [hr j]; dsimp [d]; abel
    have hF : (∑ j, c j) • d - (∑ j, c j * r j) • v = 0 := by
      rw [← hx'.2, Finset.sum_smul, Finset.sum_smul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      change c j • d - (c j * r j) • v = c j • (x - a j)
      have he := congrArg (fun y : EuclideanSpace ℝ (Fin 3) => c j • y) (hxa j)
      simpa only [smul_sub, smul_smul] using he.symm
    have hS : ∑ j, c j = 0 := by
      by_contra hS
      apply hoff
      have hd : d = ((∑ j, c j * r j) / ∑ j, c j) • v := by
        rw [sub_eq_zero] at hF
        rw [div_eq_inv_mul, mul_smul, ← hF, smul_smul, inv_mul_cancel₀ hS, one_smul]
      have hg : g x = (∑ j, c j * r j) / ∑ j, c j := by
        change ⟪d, v⟫ / ⟪v, v⟫ = _
        rw [hd, real_inner_smul_left, mul_div_assoc, div_self hvv, mul_one]
      rw [hg, ← hd]
      exact (sub_add_cancel x p₀).symm
    obtain ⟨u, hu0, hdu, hvu⟩ := exists_orth d v
    apply not_nondegenerate q a x hx'.1 u hu0 _ hS hx.2
    intro j
    rw [hxa, inner_sub_left, real_inner_smul_left, hdu, hvu]
    ring
  have hmaps : Set.MapsTo g (nondegenerateEquilibria q a)
      {s : ℝ | (∀ j, s ≠ r j) ∧ ∑ j, q j / |s - r j|^3 * (s - r j) = 0} := by
    intro x hx
    have hx' := (mem_equilibria_iff q a x).mp hx.1
    have hxl := hline x hx
    let s := g x
    have hxa (j : Fin n) : x - a j = (s - r j) • v := by
      rw [hr j]
      conv_lhs => rw [hxl]
      rw [sub_smul]
      abel
    have hsr (j : Fin n) : s ≠ r j := by
      intro hj
      have h := hxa j
      rw [hj, sub_self, zero_smul] at h
      exact hx'.1 ⟨j, (sub_eq_zero.mp h).symm⟩
    refine ⟨hsr, ?_⟩
    · have h0 := hx'.2
      simp only [hxa, norm_smul, Real.norm_eq_abs, smul_smul, ← Finset.sum_smul] at h0
      have h1 := (smul_eq_zero.mp h0).resolve_right hv0
      have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
      have hscale : ∑ j, q j / |s - r j|^3 * (s - r j) =
          ‖v‖^3 * ∑ j, q j / (|s - r j| * ‖v‖)^3 * (s - r j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [mul_pow]
        field_simp [hn, abs_ne_zero.mpr (sub_ne_zero.mpr (hsr j))]
      rw [hscale, h1, mul_zero]
  have hinj : Set.InjOn g (nondegenerateEquilibria q a) := by
    intro x hx y hy hxy
    rw [hline x hx, hline y hy, hxy]
  exact (Set.encard_le_encard_of_injOn hmaps hinj).trans (axis_polynomial_bound hn r q hrinj hq)

/-- For arbitrary nonzero signed charges on a line, every nondegenerate equilibrium
is on the line. The signed polynomial numerators give the bound 2(n² − 1). -/
lemma collinear_nondegenerate_bound {n : ℕ} (hn : 0 < n)
    (q : Fin n → ℝ) (a : Fin n → EuclideanSpace ℝ (Fin 3))
    (hq : ∀ j, q j ≠ 0)
    (ha : Function.Injective a) (hcol : Collinear ℝ (Set.range a)) :
    (nondegenerateEquilibria q a).encard ≤ (2 * (n ^ 2 - 1) : ℕ) := by
  have h : (n + 1) * (2 * (n - 1)) = 2 * (n ^ 2 - 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    change (k + 1 + 1) * (2 * (k + 1 - 1)) = 2 * ((k + 1)^2 - 1)
    have he : (k + 1)^2 = k * k + 2 * k + 1 := by ring
    simp only [he, Nat.add_sub_cancel]
    ring
  rw [← h]
  exact nonempty_axis_parameter_bound hn q a hq ha hcol

/-- Off the affine span, both the total and the first moment of the
Coulomb weights at an equilibrium vanish. -/
lemma off_span_balance {n : ℕ} (q : Fin n → ℝ) (a : Fin n → EuclideanSpace ℝ (Fin 3))
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ equilibria q a)
    (hoff : x ∉ affineSpan ℝ (Set.range a)) :
    (∑ j, q j / ‖x - a j‖^3) = 0 ∧ (∑ j, (q j / ‖x - a j‖^3) • a j) = 0 := by
  let w (j : Fin n) := q j / ‖x - a j‖^3
  have hforce : ∑ j, w j • (x - a j) = 0 := ((mem_equilibria_iff q a x).mp hx).2
  have htotal : ∑ j, w j = 0 := by
    by_contra hne
    apply hoff
    let u (j : Fin n) := (∑ i, w i)⁻¹ * w j
    have hu : ∑ j, u j = 1 := by
      simp only [u, ← Finset.mul_sum]
      exact inv_mul_cancel₀ hne
    have hscaled : ∑ j, u j • (x -ᵥ a j) = 0 := by
      simp only [vsub_eq_sub, u, mul_smul, ← Finset.smul_sum, hforce, smul_zero]
    have he := Finset.sum_smul_const_vsub_eq_vsub_affineCombination
      Finset.univ u a x hu
    rw [hscaled] at he
    rw [vsub_eq_zero_iff_eq.mp he.symm]
    exact affineCombination_mem_affineSpan hu a
  refine ⟨htotal, ?_⟩
  simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, htotal, zero_smul,
    zero_sub, neg_eq_zero] at hforce
  exact hforce

theorem main : H1 → H2 → H3 → type_of% @Arxiv.«2607.27197».maxwell_conjecture.variants.polynomial_bound := by
  intro h1 h2 h3
  obtain ⟨C1, d1, h1⟩ := h1
  obtain ⟨C2, d2, h2⟩ := h2
  obtain ⟨C3, d3, h3⟩ := h3
  let C := 2 + C1 + C2 + C3
  let d := max 2 (max d1 (max d2 d3))
  refine ⟨C, d, ?_⟩
  intro n hn q a hi hq hnd
  have hd2 : 2 ≤ d := le_max_left _ _
  have hd1' : d1 ≤ d := (le_max_left d1 _).trans (le_max_right _ _)
  have hd2' : d2 ≤ d := (le_max_left d2 _).trans ((le_max_right d1 _).trans (le_max_right _ _))
  have hd3' : d3 ≤ d := (le_max_right d2 d3).trans ((le_max_right d1 _).trans (le_max_right _ _))
  have hincrease (c e : ℕ) (he : e ≤ d) : ((c * n ^ e : ℕ) : ℕ∞) ≤ (c * n ^ d : ℕ) := by
    exact_mod_cast Nat.mul_le_mul_left c (Nat.pow_le_pow_right hn he)
  by_cases hcol : Collinear ℝ (Set.range a)
  · have heq : equilibria q a = nondegenerateEquilibria q a := by
      ext x
      exact ⟨fun hx => ⟨hx, hnd x hx⟩, fun hx => hx.1⟩
    rw [heq]
    refine (collinear_nondegenerate_bound hn q a hq hi hcol).trans ?_
    have hle : (2 * (n ^ 2 - 1) : ℕ) ≤ 2 * n ^ 2 := Nat.mul_le_mul_left 2 (Nat.sub_le _ _)
    have hle' : ((2 * (n ^ 2 - 1) : ℕ) : ℕ∞) ≤ (2 * n ^ 2 : ℕ) := by exact_mod_cast hle
    exact hle'.trans
      ((hincrease 2 2 hd2).trans (by exact_mod_cast Nat.mul_le_mul_right (n ^ d) (by dsimp [C]; omega : 2 ≤ C)))
  · by_cases hspan : affineSpan ℝ (Set.range a) = ⊤
    · exact ((h3 n hn q a hi hq hnd hspan).trans (hincrease C3 d3 hd3')).trans
        (by exact_mod_cast Nat.mul_le_mul_right (n ^ d) (by dsimp [C]; omega : C3 ≤ C))
    · let A := (affineSpan ℝ (Set.range a) : Set (EuclideanSpace ℝ (Fin 3)))
      have hins := (h1 n hn q a hi hq hnd hcol hspan).trans (hincrease C1 d1 hd1')
      have hout : (equilibria q a \ A).encard ≤ (C2 * n ^ d : ℕ) := by
        refine (Set.encard_le_encard ?_).trans
          ((h2 n hn q a hi hq hnd hcol hspan).trans (hincrease C2 d2 hd2'))
        rintro x ⟨hx, hxa⟩
        exact ⟨hx, hxa, off_span_balance q a hx hxa⟩
      calc
        (equilibria q a).encard = (equilibria q a \ A).encard + (equilibria q a ∩ A).encard :=
          (Set.encard_sdiff_add_encard_inter _ _).symm
        _ ≤ ((C2 * n ^ d : ℕ) : ℕ∞) + ((C1 * n ^ d : ℕ) : ℕ∞) := add_le_add hout hins
        _ ≤ (C * n ^ d : ℕ) := by
          exact_mod_cast (show C2 * n ^ d + C1 * n ^ d ≤ C * n ^ d by
            rw [← Nat.add_mul]
            exact Nat.mul_le_mul_right _ (by dsimp [C]; omega))

end Proof

end OMA.R_Arxiv_2607_27197_maxwell_conjecture_variants_polynomial_bound_R1
