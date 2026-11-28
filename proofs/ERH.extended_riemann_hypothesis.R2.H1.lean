import OMAReductions.R_ERH_extended_riemann_hypothesis_R2

/-!
# Abelian cases of the extended Riemann hypothesis

Credit: @deepqntm. Every quadratic field has a nontrivial primitive quadratic character whose
L-function, together with Riemann zeta, accounts for its Dedekind zeros in the positive
half-plane away from 1. For Gaussian rationals, the factorization holds at every prime. All
cyclotomic fields admit an analogous zero criterion. The zero-location corollaries use the
primitive Dirichlet critical-strip statement as an explicit hypothesis.

The prime-ideal Euler product, the rational-field ideal count and the finite root-product
identity are adapted from the merged results credited below.
-/

/- Prime-ideal Euler product, adapted from the merged proof of
`Erdos436.erdos_436.variants.ge_four.R1.H2` in this repository. The original authors
credit Chris Birkbeck, Riccardo Brasca and the contributors to chebotarev-density
(commit a00054a0e6bbc394b0e81de750db0cd2efc8bd88) and flt-regular-bernoulli,
under Apache-2.0. We retain the convergence statement before passing to the product. -/
noncomputable section

open NumberField
open scoped Topology nonZeroDivisors

namespace Chebotarev

section NumberFieldEulerProduct

variable (L : Type*) [Field L] [NumberField L]

abbrev NonzeroIdeal : Type _ := {I : Ideal (𝓞 L) // I ≠ ⊥}

noncomputable def idealNormMultiplicity (n : ℕ) : ℕ :=
  Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 = n}

lemma idealNormMultiplicity_zero : idealNormMultiplicity L 0 = 0 := by
  unfold idealNormMultiplicity
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun ⟨⟨I, hI⟩, hnorm⟩ ↦ hI (Ideal.absNorm_eq_zero_iff.mp hnorm)⟩

lemma idealNormMultiplicity_one : idealNormMultiplicity L 1 = 1 := by
  unfold idealNormMultiplicity
  have : Unique {I : NonzeroIdeal L // Ideal.absNorm I.1 = 1} :=
    { default := ⟨⟨⊤, by simp⟩, Ideal.absNorm_top⟩
      uniq := fun ⟨⟨I, hI⟩, hnorm⟩ ↦
        Subtype.ext (Subtype.ext (Ideal.absNorm_eq_one_iff.mp hnorm)) }
  exact Nat.card_unique

lemma dedekindZeta_eq_tsum_idealNormMultiplicity {s : ℂ} (hs : 1 < s.re) :
    NumberField.dedekindZeta L s =
      ∑' n : ℕ, (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
  unfold NumberField.dedekindZeta LSeries
  refine tsum_congr fun n ↦ ?_
  unfold LSeries.term
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hs0 : s ≠ 0 := by rintro rfl; norm_num at hs
    simp [idealNormMultiplicity_zero, Complex.zero_cpow (neg_ne_zero.mpr hs0)]
  · simp only [hn.ne', ↓reduceIte]
    rw [Complex.cpow_neg, div_eq_mul_inv]
    congr 1
    unfold idealNormMultiplicity
    have hequiv : {I : Ideal (𝓞 L) // Ideal.absNorm I = n} ≃
        {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} := by
      refine {
        toFun := fun ⟨I, hI⟩ ↦ ⟨⟨I, ?_⟩, hI⟩
        invFun := fun ⟨⟨I, _⟩, hI⟩ ↦ ⟨I, hI⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
      intro h
      rw [h, Ideal.absNorm_bot] at hI
      lia
    exact_mod_cast Nat.card_congr hequiv

lemma sum_idealNormMultiplicity_isBigO :
    (fun n : ℕ ↦ ∑ k ∈ Finset.Icc 1 n, (idealNormMultiplicity L k : ℝ))
      =O[Filter.atTop] (fun n : ℕ ↦ (n : ℝ) ^ (1 : ℝ)) := by
  classical
  have h_finite : ∀ (b : ℕ), {I : NonzeroIdeal L | Ideal.absNorm I.1 = b}.Finite := fun b ↦
    Set.Finite.preimage (f := fun I : NonzeroIdeal L ↦ I.1) (fun _ _ _ _ ↦ Subtype.ext)
      (Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 L) b)
  have h_sum_card : ∀ n : ℕ, ∑ k ∈ Finset.Icc 1 n, idealNormMultiplicity L k =
      Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} := fun n ↦ by
    have key := Finset.card_preimage_eq_sum_card_image_eq (f := fun I : NonzeroIdeal L ↦
      Ideal.absNorm I.1) (s := Finset.Icc 1 n) (fun b _ ↦ h_finite b)
    rw [show ((fun I : NonzeroIdeal L ↦ Ideal.absNorm I.1) ⁻¹' ↑(Finset.Icc 1 n)) =
        {I : NonzeroIdeal L | Ideal.absNorm I.1 ≤ n} by
      ext ⟨I, hI⟩
      simp only [Set.mem_preimage, Finset.coe_Icc, Set.mem_Icc, Set.mem_ofPred_eq]
      exact ⟨fun h ↦ h.2, fun h ↦
        ⟨Nat.one_le_iff_ne_zero.mpr (mt Ideal.absNorm_eq_zero_iff.mp hI), h⟩⟩] at key
    exact key.symm
  have h_card_bridge : ∀ n : ℕ,
      Nat.card {I : NonzeroIdeal L // Ideal.absNorm I.1 ≤ n} =
      Nat.card {I : (Ideal (𝓞 L))⁰ // ((Ideal.absNorm I.1 : ℕ) : ℝ) ≤ (n : ℝ)} :=
    fun n ↦ Nat.card_congr
      { toFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
          ⟨⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩, by exact_mod_cast hn⟩
        invFun := fun ⟨⟨I, hI⟩, hn⟩ ↦
          ⟨⟨I, mem_nonZeroDivisors_iff_ne_zero.mp hI⟩, by exact_mod_cast hn⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
  refine Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow
    (((NumberField.Ideal.tendsto_norm_le_div_atTop₀ L).comp
      tendsto_natCast_atTop_atTop).congr' ?_)
  filter_upwards with n
  simp only [Function.comp_apply, Real.rpow_one]
  rw [← Nat.cast_sum, h_sum_card n, h_card_bridge n]
  push_cast
  rfl

lemma summable_idealNormMultiplicity_mul_cpow_neg {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ ↦ ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖ := by
  classical
  have h_lss : LSeriesSummable (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) s :=
    LSeriesSummable_of_sum_norm_bigO_and_nonneg
      (f := fun n ↦ (idealNormMultiplicity L n : ℝ))
      (sum_idealNormMultiplicity_isBigO L) (fun _ ↦ Nat.cast_nonneg _) zero_le_one
      (by exact_mod_cast hs)
  have h_term_eq : LSeries.term (fun n : ℕ ↦ ((idealNormMultiplicity L n : ℝ) : ℂ)) s =
      fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) := by
    funext n
    simp only [LSeries.term]
    split_ifs with hn
    · subst hn
      simp [idealNormMultiplicity_zero]
    · simp [Complex.cpow_neg, div_eq_mul_inv]
  exact (h_term_eq ▸ h_lss :
    Summable fun n ↦ (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)).norm

private noncomputable def insertPiEquiv {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) : ({i // i ∈ insert a s} → ℕ) ≃ ℕ × ({i // i ∈ s} → ℕ) :=
  ((Finset.subtypeInsertEquivOption ha).arrowCongr (Equiv.refl ℕ)).trans Equiv.piOptionEquivProd

@[simp] private lemma insertPiEquiv_fst {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) :
    (insertPiEquiv a s ha e).1 = e ⟨a, Finset.mem_insert_self a s⟩ := rfl

@[simp] private lemma insertPiEquiv_snd {ι : Type*} [DecidableEq ι] (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) (i : {i // i ∈ s}) :
    (insertPiEquiv a s ha e).2 i = e ⟨i.1, Finset.mem_insert_of_mem i.2⟩ := rfl

private lemma prodInsertAttach {ι : Type*} [DecidableEq ι] (g : ι → ℂ) (a : ι) (s : Finset ι)
    (ha : a ∉ s) (e : {i // i ∈ insert a s} → ℕ) :
    ∏ i ∈ (insert a s).attach, g i.1 ^ e i =
      g a ^ (insertPiEquiv a s ha e).1 *
        ∏ i ∈ s.attach, g i.1 ^ (insertPiEquiv a s ha e).2 i := by
  rw [insertPiEquiv_fst]
  conv_rhs => rw [show (∏ i ∈ s.attach, g i.1 ^ (insertPiEquiv a s ha e).2 i)
    = ∏ i ∈ s.attach, g i.1 ^ e ⟨i.1, Finset.mem_insert_of_mem i.2⟩ from
    Finset.prod_congr rfl fun i _ ↦ by rw [insertPiEquiv_snd]]
  rw [Finset.attach_insert, Finset.prod_insert, Finset.prod_image]
  · exact fun x _ y _ h ↦ Subtype.ext (Subtype.mk.inj h)
  · simpa only [Finset.mem_image, Finset.mem_attach, Subtype.mk.injEq, true_and,
      Subtype.exists, exists_prop, exists_eq_right] using ha

private lemma finsetGeometricProd_summable_and_hasSum {ι : Type*} (g : ι → ℂ)
    (hg : ∀ i, ‖g i‖ < 1) (s : Finset ι) :
    (Summable fun e : {i // i ∈ s} → ℕ ↦ ‖∏ i ∈ s.attach, g i.1 ^ e i‖) ∧
      HasSum (fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i)
        (∏ i ∈ s, (1 - g i)⁻¹) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.prod_empty]
    refine ⟨?_, ?_⟩
    · have h1 : (fun e : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ ‖∏ i ∈ Finset.attach ∅, g i.1 ^ e i‖)
          = fun _ ↦ (1 : ℝ) := by
        funext e
        simp [Finset.attach_empty]
      rw [h1]
      exact (hasSum_unique (fun _ : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ (1 : ℝ))).summable
    · have h1 : (fun e : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ ∏ i ∈ Finset.attach ∅, g i.1 ^ e i)
          = fun _ ↦ (1 : ℂ) := by
        funext e
        simp [Finset.attach_empty]
      rw [h1]
      exact hasSum_unique (fun _ : {i // i ∈ (∅ : Finset ι)} → ℕ ↦ (1 : ℂ))
  | insert a s ha ih =>
    obtain ⟨ihsum, ihhas⟩ := ih
    rw [Finset.prod_insert ha]
    have hgeo : HasSum (fun n : ℕ ↦ g a ^ n) (1 - g a)⁻¹ :=
      hasSum_geometric_of_norm_lt_one (hg a)
    have hgeosum : Summable (fun n : ℕ ↦ ‖g a ^ n‖) := by
      simp_rw [norm_pow]
      exact summable_geometric_of_lt_one (norm_nonneg _) (hg a)
    have hprodsum : Summable (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) :=
      summable_mul_of_summable_norm (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeosum ihsum
    have hHsum : Summable (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        ‖g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i‖) :=
      Summable.mul_norm (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeosum ihsum
    have hHhas : HasSum (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
        g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) ((1 - g a)⁻¹ * ∏ i ∈ s, (1 - g i)⁻¹) :=
      HasSum.mul (f := fun n : ℕ ↦ g a ^ n)
        (g := fun e : {i // i ∈ s} → ℕ ↦ ∏ i ∈ s.attach, g i.1 ^ e i) hgeo ihhas hprodsum
    refine ⟨?_, ?_⟩
    · have heq : (fun e : {i // i ∈ insert a s} → ℕ ↦ ‖∏ i ∈ (insert a s).attach, g i.1 ^ e i‖)
          = (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
              ‖g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i‖) ∘ insertPiEquiv a s ha := by
        funext e
        rw [Function.comp_apply, prodInsertAttach g a s ha e]
      rw [heq]
      exact (insertPiEquiv a s ha).summable_iff.mpr hHsum
    · have heq : (fun e : {i // i ∈ insert a s} → ℕ ↦ ∏ i ∈ (insert a s).attach, g i.1 ^ e i)
          = (fun x : ℕ × ({i // i ∈ s} → ℕ) ↦
              g a ^ x.1 * ∏ i ∈ s.attach, g i.1 ^ x.2 i) ∘ insertPiEquiv a s ha := by
        funext e
        rw [Function.comp_apply, prodInsertAttach g a s ha e]
      rw [heq]
      exact (insertPiEquiv a s ha).hasSum_iff.mpr hHhas

private lemma prod_natCast_cpow {ι : Type*} (S : Finset ι) (m : ι → ℕ) (z : ℂ) :
    (∏ i ∈ S, (m i : ℂ) ^ z) = ((∏ i ∈ S, m i : ℕ) : ℂ) ^ z := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ih, Nat.cast_mul,
      Complex.natCast_mul_natCast_cpow]

lemma norm_absNorm_cpow_neg_lt_one {s : ℂ} (hs : 1 < s.re)
    (𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := by
  have hne0 : Ideal.absNorm 𝔭.1 ≠ 0 := fun h ↦ 𝔭.2.2 (Ideal.absNorm_eq_zero_iff.mp h)
  have hne1 : Ideal.absNorm 𝔭.1 ≠ 1 := fun h ↦ 𝔭.2.1.ne_top (Ideal.absNorm_eq_one_iff.mp h)
  have h2 : 2 ≤ Ideal.absNorm 𝔭.1 := by lia
  rw [Complex.norm_natCast_cpow_of_pos (by lia), Complex.neg_re]
  exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast h2.trans_lt' one_lt_two) (by linarith)

theorem prod_eulerFactor_eq_tsum_exponentVector {s : ℂ} (hs : 1 < s.re)
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    (∏ 𝔭 ∈ S, (1 - (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹) =
      ∑' e : S →₀ ℕ, ∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) := by
  classical
  have hg : ∀ 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ‖(Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := norm_absNorm_cpow_neg_lt_one L hs
  have hHS := (finsetGeometricProd_summable_and_hasSum
    (fun 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) hg S).2
  have hrw : ∀ e : S → ℕ,
      (∏ 𝔭 ∈ S.attach, ((Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭) =
        ∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) := fun e ↦
    Finset.prod_congr rfl fun 𝔭 _ ↦ by
      rw [← Complex.cpow_nat_mul]
      ring_nf
  rw [← hHS.tsum_eq, ← (Finsupp.equivFunOnFinite (α := S) (M := ℕ)).tsum_eq
    (fun e : S → ℕ ↦ ∏ 𝔭 ∈ S.attach, ((Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭)]
  refine tsum_congr fun e ↦ ?_
  simp only [Finsupp.equivFunOnFinite_apply]
  rw [hrw]

theorem absNorm_prod_pow_of_primeIdeal
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    Ideal.absNorm (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) =
      ∏ 𝔭 ∈ S.attach, Ideal.absNorm 𝔭.1.1 ^ e 𝔭 := by
  rw [map_prod]
  exact Finset.prod_congr rfl fun 𝔭 _ ↦ map_pow Ideal.absNorm 𝔭.1.1 (e 𝔭)

theorem prod_absNorm_cpow_eq_absNorm_prod_pow_cpow {s : ℂ}
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    (∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s)) =
      (Ideal.absNorm (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) : ℂ) ^ (-s) := by
  have hinner : ∀ 𝔭 ∈ S.attach,
      (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) =
        ((Ideal.absNorm 𝔭.1.1 ^ e 𝔭 : ℕ) : ℂ) ^ (-s) := fun 𝔭 _ ↦ by
    rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul]
    ring_nf
  rw [Finset.prod_congr rfl hinner, prod_natCast_cpow, absNorm_prod_pow_of_primeIdeal]

private instance instFiniteAbsNormFiber (n : ℕ) :
    Finite {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} :=
  Set.Finite.to_subtype <| Set.Finite.of_finite_image (f := fun I : NonzeroIdeal L ↦ I.1)
    ((Ideal.finite_setOfPred_absNorm_eq (S := 𝓞 L) n).subset (by rintro _ ⟨⟨I, _⟩, rfl, rfl⟩; rfl))
    (fun _ _ _ _ ↦ Subtype.ext)

private lemma tsum_absNormFiber {M : Type*} [AddCommGroup M] [TopologicalSpace M] [T2Space M]
    [IsTopologicalAddGroup M] (n : ℕ) (g : ℕ → M) :
    (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n}, g (Ideal.absNorm y.1.1))
      = idealNormMultiplicity L n • g n :=
  (tsum_congr fun y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} ↦ by rw [y.2]).trans
    (tsum_const (g n))

theorem hasSum_nonzeroIdeal_absNorm_cpow {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun I : NonzeroIdeal L ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s))
      (NumberField.dedekindZeta L s) := by
  classical
  set e := Equiv.sigmaFiberEquiv (fun I : NonzeroIdeal L ↦ Ideal.absNorm I.1)
  have hval : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n},
      (Ideal.absNorm (y.1).1 : ℂ) ^ (-s)) = (idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s) :=
    fun n ↦ by rw [tsum_absNormFiber L n fun k ↦ (k : ℂ) ^ (-s), nsmul_eq_mul]
  have hnorm : ∀ n : ℕ, (∑' y : {I : NonzeroIdeal L // Ideal.absNorm I.1 = n},
      ‖(Ideal.absNorm (y.1).1 : ℂ) ^ (-s)‖) = ‖(idealNormMultiplicity L n : ℂ) * (n : ℂ) ^ (-s)‖ :=
    fun n ↦ by
      rw [tsum_absNormFiber L n fun k ↦ ‖(k : ℂ) ^ (-s)‖, nsmul_eq_mul, norm_mul,
        Complex.norm_natCast]
  have hsummable : Summable fun I : NonzeroIdeal L ↦ ‖(Ideal.absNorm I.1 : ℂ) ^ (-s)‖ := by
    rw [← e.summable_iff]
    refine (summable_sigma_of_nonneg (fun _ ↦ norm_nonneg _)).mpr ⟨fun _ ↦ Summable.of_finite, ?_⟩
    exact (summable_idealNormMultiplicity_mul_cpow_neg L hs).congr fun n ↦ (hnorm n).symm
  have hsummable_sigma : Summable fun p : Σ n, {I : NonzeroIdeal L // Ideal.absNorm I.1 = n} ↦
      (Ideal.absNorm (e p).1 : ℂ) ^ (-s) :=
    (e.summable_iff (f := fun I : NonzeroIdeal L ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s))).mpr
      hsummable.of_norm
  have hval_sum : (∑' I : NonzeroIdeal L, (Ideal.absNorm I.1 : ℂ) ^ (-s))
      = NumberField.dedekindZeta L s := by
    rw [dedekindZeta_eq_tsum_idealNormMultiplicity L hs,
      ← e.tsum_eq (fun I ↦ (Ideal.absNorm I.1 : ℂ) ^ (-s)), hsummable_sigma.tsum_sigma]
    exact tsum_congr hval
  exact hval_sum ▸ hsummable.of_norm.hasSum

open UniqueFactorizationMonoid in

private theorem factorization_primePow_apply
    (𝔭 𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (n : ℕ) :
    factorization (𝔭.1 ^ n) 𝔮.1 = if 𝔮 = 𝔭 then n else 0 := by
  rw [factorization_pow, Finsupp.smul_apply, smul_eq_mul, factorization_eq_count,
    normalizedFactors_irreducible (Ideal.prime_of_isPrime 𝔭.2.2 𝔭.2.1).irreducible,
    normalize_eq, Multiset.count_singleton]
  split_ifs <;> simp_all [Subtype.ext_iff]

open UniqueFactorizationMonoid in

private theorem factorization_prod_primePow_apply
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (e : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℕ)
    (𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭.1) 𝔮.1 =
      ∑ 𝔭 ∈ S.attach, factorization (𝔭.1.1 ^ e 𝔭.1) 𝔮.1 := by
  classical
  induction S using Finset.induction with
  | empty => rw [Finset.attach_empty, Finset.prod_empty, Finset.sum_empty, factorization_one,
      Finsupp.coe_zero, Pi.zero_apply]
  | insert a s ha ih =>
    rw [Finset.attach_insert, Finset.prod_insert, Finset.sum_insert,
      factorization_mul (pow_ne_zero _ a.2.2)
        (Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)), Finsupp.add_apply,
      Finset.prod_image (fun x _ y _ h ↦ Subtype.ext (by simpa using h)),
      Finset.sum_image (fun x _ y _ h ↦ Subtype.ext (by simpa using h)), ih] <;>
    · rw [Finset.mem_image]
      rintro ⟨x, -, hx⟩
      exact ha ((Subtype.mk.inj hx) ▸ x.2)

open UniqueFactorizationMonoid in

private theorem factorization_prod_primePow_eq
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (e : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} → ℕ)
    (𝔮 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭.1) 𝔮.1 = if 𝔮 ∈ S then e 𝔮 else 0 := by
  classical
  rw [factorization_prod_primePow_apply L S e 𝔮]
  simp_rw [factorization_primePow_apply L]
  by_cases h𝔮 : 𝔮 ∈ S
  · rw [if_pos h𝔮, Finset.sum_eq_single (⟨𝔮, h𝔮⟩ : {x // x ∈ S})]
    · rw [if_pos rfl]
    · rintro b _ hb
      rw [if_neg (fun h ↦ hb (Subtype.ext h.symm))]
    · exact fun h ↦ absurd (Finset.mem_attach S _) h
  · rw [if_neg h𝔮, Finset.sum_eq_zero]
    rintro ⟨b, hb⟩ -
    rw [if_neg (fun h : 𝔮 = b ↦ h𝔮 (h.symm ▸ hb))]

open UniqueFactorizationMonoid in

private noncomputable def primeFactorsOf (𝔞 : NonzeroIdeal L) :
    Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} :=
  (normalizedFactors 𝔞.1).toFinset.attach.map
    (⟨fun p : {x // x ∈ (normalizedFactors 𝔞.1).toFinset} ↦ (⟨p.1, by
        have hp := p.2
        rw [Multiset.mem_toFinset] at hp
        exact ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor p.1 hp),
          (prime_of_normalized_factor p.1 hp).ne_zero⟩⟩ :
        {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}),
      fun a b h ↦ Subtype.ext (congrArg
        (fun x : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦ (x : Ideal (𝓞 L))) h)⟩ :
      {x // x ∈ (normalizedFactors 𝔞.1).toFinset} ↪ {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})

open UniqueFactorizationMonoid in

private theorem mem_primeFactorsOf (𝔞 : NonzeroIdeal L) (p : Ideal (𝓞 L))
    (hp : p ∈ normalizedFactors 𝔞.1) :
    ∃ 𝔭 ∈ primeFactorsOf L 𝔞, 𝔭.1 = p := by
  refine ⟨⟨p, ⟨Ideal.isPrime_of_prime (prime_of_normalized_factor p hp),
      (prime_of_normalized_factor p hp).ne_zero⟩⟩, ?_, rfl⟩
  rw [primeFactorsOf, Finset.mem_map]
  exact ⟨⟨p, by rwa [Multiset.mem_toFinset]⟩, Finset.mem_attach _ _, rfl⟩

open UniqueFactorizationMonoid in
private theorem factorization_idealOfExp_eq
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (f : S →₀ ℕ) (𝔮 : S) :
    factorization (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ f 𝔭) 𝔮.1.1 = f 𝔮 := by
  classical
  have hprod : (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (fun q ↦ if h : q ∈ S then f ⟨q, h⟩ else 0) 𝔭.1)
      = ∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ f 𝔭 :=
    Finset.prod_congr rfl fun 𝔭 _ ↦ by simp only [dif_pos 𝔭.2]
  rw [← hprod, factorization_prod_primePow_eq L S
    (fun q ↦ if h : q ∈ S then f ⟨q, h⟩ else 0) 𝔮.1, if_pos 𝔮.2, dif_pos 𝔮.2]

open UniqueFactorizationMonoid in
private theorem prod_primePow_count_eq (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (𝔞 : NonzeroIdeal L) (hsupp : ∀ p ∈ normalizedFactors 𝔞.1, ∃ 𝔭 ∈ S, 𝔭.1 = p) :
    (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (normalizedFactors 𝔞.1).count 𝔭.1.1) = 𝔞.1 := by
  classical
  rw [show (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ (normalizedFactors 𝔞.1).count 𝔭.1.1)
      = ∏ p ∈ S.image (fun 𝔭 ↦ 𝔭.1), p ^ (normalizedFactors 𝔞.1).count p by
    rw [Finset.prod_image (fun x _ y _ h ↦ Subtype.ext h), ← Finset.prod_attach S
      (fun p ↦ p.1 ^ (normalizedFactors 𝔞.1).count p.1)]]
  rw [← Finset.prod_subset (s₁ := (normalizedFactors 𝔞.1).toFinset)
    (s₂ := S.image (fun 𝔭 ↦ 𝔭.1))
    (fun p hp ↦ by
      rw [Multiset.mem_toFinset] at hp
      obtain ⟨𝔭, h𝔭S, rfl⟩ := hsupp p hp
      exact Finset.mem_image.mpr ⟨𝔭, h𝔭S, rfl⟩)
    (fun p _ hp ↦ by
      rw [Multiset.mem_toFinset] at hp
      rw [Multiset.count_eq_zero_of_notMem hp, pow_zero])]
  conv_rhs => rw [← finprod_pow_count_eq_of_subsingleton_units 𝔞.2]
  exact (finprod_eq_finsetProd_of_mulSupport_subset _ (by
    intro p hp
    simp only [Function.mem_mulSupport] at hp
    rw [Finset.mem_coe, Multiset.mem_toFinset]
    by_contra hc
    rw [Multiset.count_eq_zero_of_notMem hc, pow_zero] at hp
    exact hp rfl)).symm

omit [NumberField L] in

private theorem weight_prod_primePow (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}) (e : S → ℕ) :
    w (∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭) = ∏ 𝔭 ∈ S.attach, (w 𝔭.1.1) ^ e 𝔭 := by
  classical
  have wpow : ∀ (𝔭 : Ideal (𝓞 L)) (_ : 𝔭 ≠ ⊥) (k : ℕ), w (𝔭 ^ k) = (w 𝔭) ^ k := by
    intro 𝔭 h𝔭 k
    induction k with
    | zero => simpa using hw_one
    | succ n ih => rw [pow_succ, hw_mul (pow_ne_zero _ h𝔭) h𝔭, ih, pow_succ]
  have key : ∀ T : Finset S, w (∏ 𝔭 ∈ T, 𝔭.1.1 ^ e 𝔭) = ∏ 𝔭 ∈ T, (w 𝔭.1.1) ^ e 𝔭 := by
    intro T
    induction T using Finset.induction with
    | empty => simpa using hw_one
    | insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        hw_mul (pow_ne_zero _ a.1.2.2)
          (Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)),
        wpow a.1.1 a.1.2.2, ih]
  exact key S.attach

private theorem weighted_prod_eulerFactor_eq_tsum {s : ℂ} (hs : 1 < s.re)
    (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (hw_norm : ∀ 𝔞, ‖w 𝔞‖ ≤ 1)
    (S : Finset {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥})
    (idealOfExp : (S →₀ ℕ) → NonzeroIdeal L)
    (hidealOfExp : ∀ e : S →₀ ℕ,
      (idealOfExp e).1 = ∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭)
    (hinj : Function.Injective idealOfExp) :
    (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
      = ∑' 𝔞 : Set.range idealOfExp,
          w 𝔞.1.1 * (Ideal.absNorm 𝔞.1.1 : ℂ) ^ (-s) := by
  classical
  have hg : ∀ 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥},
      ‖w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)‖ < 1 := fun 𝔭 ↦
    ((norm_mul_le_of_le (hw_norm _) le_rfl).trans_eq (one_mul _)).trans_lt
      (norm_absNorm_cpow_neg_lt_one L hs 𝔭)
  have hHS := (finsetGeometricProd_summable_and_hasSum
    (fun 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
      w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s)) hg S).2
  have hsummand : ∀ e : S →₀ ℕ,
      (∏ 𝔭 ∈ S.attach, (w 𝔭.1.1 * (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭)
        = w (idealOfExp e).1 * (Ideal.absNorm (idealOfExp e).1 : ℂ) ^ (-s) := fun e ↦ by
    simp_rw [mul_pow]
    rw [Finset.prod_mul_distrib,
      show (∏ 𝔭 ∈ S.attach, ((Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-s)) ^ e 𝔭)
        = ∏ 𝔭 ∈ S.attach, (Ideal.absNorm 𝔭.1.1 : ℂ) ^ (-(e 𝔭 : ℂ) * s) from
      Finset.prod_congr rfl fun 𝔭 _ ↦ by
        rw [← Complex.cpow_nat_mul]
        ring_nf,
      prod_absNorm_cpow_eq_absNorm_prod_pow_cpow L S (fun 𝔭 ↦ e 𝔭),
      ← weight_prod_primePow L w hw_one hw_mul S (fun 𝔭 ↦ e 𝔭), hidealOfExp e]
  have hHS' : HasSum
      (fun e : S →₀ ℕ ↦ w (idealOfExp e).1 * (Ideal.absNorm (idealOfExp e).1 : ℂ) ^ (-s))
      (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹) := by
    have hbase := (Finsupp.equivFunOnFinite (α := S) (M := ℕ)).hasSum_iff.mpr hHS
    refine hbase.congr_fun fun e ↦ ?_
    simp only [Function.comp_apply, Finsupp.equivFunOnFinite_apply]
    exact (hsummand e).symm
  rw [← hHS'.tsum_eq]
  exact (tsum_range
    (fun 𝔞 : NonzeroIdeal L ↦ w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) hinj).symm

open UniqueFactorizationMonoid in

theorem weighted_eulerProduct_hasProd {s : ℂ} (hs : 1 < s.re)
    (w : Ideal (𝓞 L) → ℂ) (hw_one : w ⊤ = 1)
    (hw_mul : ∀ {𝔞 𝔟 : Ideal (𝓞 L)}, 𝔞 ≠ ⊥ → 𝔟 ≠ ⊥ → w (𝔞 * 𝔟) = w 𝔞 * w 𝔟)
    (hw_norm : ∀ 𝔞, ‖w 𝔞‖ ≤ 1) :
    HasProd (fun 𝔭 : {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥} ↦
        (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
      (∑' 𝔞 : NonzeroIdeal L, w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s)) := by
  classical
  set P := {𝔭 : Ideal (𝓞 L) // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥}
  set Dw : NonzeroIdeal L → ℂ := fun 𝔞 ↦ w 𝔞.1 * (Ideal.absNorm 𝔞.1 : ℂ) ^ (-s) with hDw
  set idealOfExp : (S : Finset P) → (S →₀ ℕ) → NonzeroIdeal L :=
    fun S e ↦ ⟨∏ 𝔭 ∈ S.attach, 𝔭.1.1 ^ e 𝔭,
      Finset.prod_ne_zero_iff.mpr (fun 𝔭 _ ↦ pow_ne_zero _ 𝔭.1.2.2)⟩ with hidealOfExp
  have hnormD : Summable fun 𝔞 : NonzeroIdeal L ↦ ‖Dw 𝔞‖ := by
    refine ((hasSum_nonzeroIdeal_absNorm_cpow L hs).summable.norm).of_nonneg_of_le
      (fun _ ↦ norm_nonneg _) (fun 𝔞 ↦ ?_)
    rw [hDw]
    exact (norm_mul_le_of_le (hw_norm _) le_rfl).trans_eq (one_mul _)
  have hinj : ∀ S : Finset P, Function.Injective (idealOfExp S) := by
    intro S e e' h
    rw [hidealOfExp, Subtype.mk.injEq] at h
    ext 𝔮
    rw [← factorization_idealOfExp_eq L S e 𝔮, ← factorization_idealOfExp_eq L S e' 𝔮, h]
  have hmem : ∀ (S : Finset P) (𝔞 : NonzeroIdeal L),
      (∀ p ∈ normalizedFactors 𝔞.1, ∃ 𝔭 ∈ S, 𝔭.1 = p) →
      𝔞 ∈ Set.range (idealOfExp S) := by
    intro S 𝔞 hsupp
    refine ⟨Finsupp.onFinset S.attach
      (fun 𝔭 ↦ (normalizedFactors 𝔞.1).count 𝔭.1.1) (by simp), ?_⟩
    rw [hidealOfExp, Subtype.ext_iff]
    simpa only [Finsupp.onFinset_apply] using prod_primePow_count_eq L S 𝔞 hsupp
  have hpartial : ∀ S : Finset P,
      (∏ 𝔭 ∈ S, (1 - w 𝔭.1 * (Ideal.absNorm 𝔭.1 : ℂ) ^ (-s))⁻¹)
        = ∑' 𝔞 : Set.range (idealOfExp S), Dw 𝔞.1 := by
    intro S
    exact weighted_prod_eulerFactor_eq_tsum L hs w hw_one hw_mul hw_norm S (idealOfExp S)
      (fun e ↦ rfl) (hinj S)
  rw [HasProd, SummationFilter.unconditional, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨F, hF⟩ := ((tendsto_tsum_compl_atTop_zero (fun 𝔞 ↦ ‖Dw 𝔞‖)).eventually
    (gt_mem_nhds hε)).exists
  refine ⟨F.biUnion (primeFactorsOf L), fun S hS ↦ ?_⟩
  have hF_sub : ∀ 𝔞 ∈ F, 𝔞 ∈ Set.range (idealOfExp S) := by
    intro 𝔞 h𝔞F
    refine hmem S 𝔞 fun p hp ↦ ?_
    obtain ⟨𝔭, h𝔭, rfl⟩ := mem_primeFactorsOf L 𝔞 p hp
    exact ⟨𝔭, hS (Finset.mem_biUnion.mpr ⟨𝔞, h𝔞F, h𝔭⟩), rfl⟩
  rw [dist_eq_norm, hpartial S]
  have hsplit : ∑' 𝔞 : NonzeroIdeal L, Dw 𝔞 =
      (∑' 𝔞 : Set.range (idealOfExp S), Dw 𝔞.1) +
        ∑' 𝔞 : ↥(Set.range (idealOfExp S))ᶜ, Dw 𝔞.1 :=
    (hnormD.of_norm.tsum_subtype_add_tsum_subtype_compl _).symm
  rw [hsplit, sub_add_cancel_left, norm_neg]
  refine (norm_tsum_le_tsum_norm (hnormD.subtype _)).trans_lt ?_
  refine lt_of_le_of_lt ?_ hF
  refine (hnormD.subtype _).tsum_le_tsum_of_inj
    (fun 𝔞 : ↥(Set.range (idealOfExp S))ᶜ ↦
      (⟨𝔞.1, fun h ↦ 𝔞.2 (hF_sub 𝔞.1 h)⟩ : {x // x ∉ F}))
    (fun x y h ↦ Subtype.ext (congrArg (fun z : {x // x ∉ F} ↦ (z : NonzeroIdeal L)) h))
    (fun _ _ ↦ norm_nonneg _) (fun _ ↦ le_rfl) (hnormD.subtype _)

open UniqueFactorizationMonoid in

theorem dedekindZeta_hasProd_primeIdeal {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun P : {I : Ideal (𝓞 L) // I.IsPrime ∧ I ≠ ⊥} ↦
      (1 - (Ideal.absNorm P.1 : ℂ) ^ (-s))⁻¹) (NumberField.dedekindZeta L s) := by
  simpa only [one_mul, (hasSum_nonzeroIdeal_absNorm_cpow L hs).tsum_eq] using
    weighted_eulerProduct_hasProd L hs (fun _ ↦ 1) (by simp) (by simp) (by simp)

end NumberFieldEulerProduct
end Chebotarev
end

/- Analytic continuation and transfer of critical-strip zeros to primitive characters. -/

namespace OMA.AbelianERH

open Complex Filter Set NumberField
open scoped Topology NumberField

/-- The statement of `LFunction_eq_zero_re_of_isPrimitive` in the verified Dirichlet GRH
library (`src/Statements.lean` and `src/Main.lean` at d27f71347abceb76cd37dc8a5fccbe556ec2be90).
The pinned Formal Conjectures dependency supplies the definitions. -/
def PrimitiveStripGRH : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
    ∀ s : ℂ, 0 < s.re → s.re < 1 → χ.LFunction s = 0 → s.re = 1 / 2

/-- The extra Euler factors of an induced character have no zeros on the open right half-plane. -/
theorem changeLevelFactor_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {p : ℕ} (hp : p.Prime) {s : ℂ} (hs : 0 < s.re) :
    1 - χ p * (p : ℂ) ^ (-s) ≠ 0 := by
  have hp' : 0 < (p : ℝ) := by exact_mod_cast hp.pos
  have hpow : ‖(p : ℂ) ^ (-s)‖ < 1 := by
    change ‖((p : ℝ) : ℂ) ^ (-s)‖ < 1
    rw [norm_cpow_eq_rpow_re_of_pos hp']
    exact Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hp.one_lt) (by simpa)
  have hlt : ‖χ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.norm_le_one p)).trans_lt hpow
  intro h
  rw [← sub_eq_zero.mp h, norm_one] at hlt
  exact hlt.false

theorem lFunction_zero_iff_primitive_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] {s : ℂ} (hpos : 0 < s.re) (hs : s ≠ 1) :
    χ.LFunction s = 0 ↔ χ.primitiveCharacter.LFunction s = 0 := by
  have h := DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (s := s) (Or.inr hs)
  rw [χ.changeLevel_primitiveCharacter] at h
  rw [h, mul_eq_zero]
  exact or_iff_left (Finset.prod_ne_zero_iff.mpr fun p hp =>
    changeLevelFactor_ne_zero χ.primitiveCharacter (Nat.prime_of_mem_primeFactors hp) hpos)

theorem PrimitiveStripGRH.dirichlet {q : ℕ} [NeZero q] (h : PrimitiveStripGRH)
    (χ : DirichletCharacter ℂ q) {s : ℂ} (hpos : 0 < s.re) (hlt : s.re < 1)
    (hz : χ.LFunction s = 0) : s.re = 1 / 2 := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact h _ _ χ.primitiveCharacter_isPrimitive s hpos hlt
    ((lFunction_zero_iff_primitive_zero χ hpos (fun e => by simp [e] at hlt)).mp hz)

theorem PrimitiveStripGRH.riemann (h : PrimitiveStripGRH) {s : ℂ} (hpos : 0 < s.re)
    (hlt : s.re < 1) (hz : riemannZeta s = 0) : s.re = 1 / 2 :=
  h 1 1 DirichletCharacter.isPrimitive_one_level_one s hpos hlt (by simpa using hz)

/-- Agreement on the half-plane of convergence determines both functions off the pole. -/
theorem eqOffOne_of_halfPlane {Z W : ℂ → ℂ}
    (hZ : DifferentiableOn ℂ Z ({1}ᶜ : Set ℂ)) (hW : DifferentiableOn ℂ W ({1}ᶜ : Set ℂ))
    (heq : ∀ s : ℂ, 1 < s.re → Z s = W s) : EqOn Z W ({1}ᶜ : Set ℂ) := by
  apply (hZ.analyticOnNhd isOpen_compl_singleton).eqOn_of_preconnected_of_eventuallyEq
    (hW.analyticOnNhd isOpen_compl_singleton)
    (isConnected_compl_singleton_of_one_lt_rank
      (Complex.rank_real_complex ▸ Nat.one_lt_ofNat) _).isPreconnected
    (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
  have hneigh : ∀ᶠ z : ℂ in 𝓝 2, 1 < z.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  exact hneigh.mono heq

/-- Two Dedekind continuations agree away from their possible pole. -/
theorem continuation_unique {K : Type*} [Field K] [NumberField K] {Z W : ℂ → ℂ}
    (hZ : ERH.IsDedekindZeta K Z) (hW : ERH.IsDedekindZeta K W) :
    EqOn Z W ({1}ᶜ : Set ℂ) :=
  eqOffOne_of_halfPlane hZ.1 hW.1 fun z hz => (hZ.2 z hz).trans (hW.2 z hz).symm

/-- A half-plane product supplies the analytic continuation itself. The characters may
have different moduli. -/
theorem isDedekindZeta_of_halfPlaneProduct {K : Type*} [Field K] [NumberField K]
    {ι : Type*} (S : Finset ι) {q : ι → ℕ} [∀ i, NeZero (q i)]
    (χ : (i : ι) → DirichletCharacter ℂ (q i))
    (hprod : ∀ s : ℂ, 1 < s.re →
      dedekindZeta K s = riemannZeta s * ∏ i ∈ S, (χ i).LFunction s) :
    ERH.IsDedekindZeta K (fun s => riemannZeta s * ∏ i ∈ S, (χ i).LFunction s) := by
  refine ⟨analyticOn_riemannZeta.differentiableOn.mul <| DifferentiableOn.fun_finsetProd
    (fun i _ s hs => ((χ i).differentiableAt_LFunction s (Or.inl hs)).differentiableWithinAt),
    fun s hs => (hprod s hs).symm⟩

theorem erh_of_halfPlaneProduct {K : Type*} [Field K] [NumberField K]
    {ι : Type*} (S : Finset ι) {q : ι → ℕ} [∀ i, NeZero (q i)]
    (χ : (i : ι) → DirichletCharacter ℂ (q i))
    (hprod : ∀ s : ℂ, 1 < s.re →
      dedekindZeta K s = riemannZeta s * ∏ i ∈ S, (χ i).LFunction s)
    (h : PrimitiveStripGRH) : ERH.ExtendedRiemannHypothesis K := by
  intro Z hZ s hpos hlt hz
  have hs : s ≠ 1 := fun e => by simp [e] at hlt
  rw [continuation_unique hZ (isDedekindZeta_of_halfPlaneProduct S χ hprod) hs] at hz
  rcases mul_eq_zero.mp hz with hz | hz
  · exact h.riemann hpos hlt hz
  · obtain ⟨i, _, hi⟩ := Finset.prod_eq_zero_iff.mp hz
    exact h.dirichlet (χ i) hpos hlt hi

end OMA.AbelianERH

namespace OMA.AbelianERH

/-- The catalogue's nontrivial-zero formulation of primitive Dirichlet GRH suffices for
the positive-strip formulation used here. This is an implication between statements. -/
theorem primitiveStripGRH_of_nontrivial_zeros
    (h : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive →
      ∀ s : ℂ, χ.LFunction s = 0 → s ∉ Int.cast '' GRH.trivialZeros χ → s.re = 1 / 2) :
    PrimitiveStripGRH := by
  intro q _ χ hχ s hs _ hz
  apply h q χ hχ s hz
  rintro ⟨n, hn, rfl⟩
  have hn' : n ≤ 0 := by
    unfold GRH.trivialZeros at hn
    split at hn
    · obtain ⟨k, rfl⟩ := hn
      omega
    · split at hn
      · obtain ⟨k, rfl⟩ := hn
        omega
      · obtain ⟨k, rfl⟩ := hn
        omega
  have hcast : (n : ℝ) ≤ 0 := by exact_mod_cast hn'
  exact (not_lt_of_ge hcast) (by simpa using hs)

end OMA.AbelianERH

/- The Euler product over rational primes, with one finite factor for the prime ideals above each. -/

namespace OMA.AbelianERH

open NumberField
open scoped NumberField

noncomputable abbrev primeIdealsAbove (K : Type*) [Field K] [NumberField K] (p : Nat.Primes) :=
  IsDedekindDomain.primesOverFinset (Ideal.span {(p.val : ℤ)}) (𝓞 K)

private theorem above_spec {K : Type*} [Field K] [NumberField K] (p : Nat.Primes)
    {P : Ideal (𝓞 K)} : P ∈ primeIdealsAbove K p ↔
      P.IsPrime ∧ P.LiesOver (Ideal.span {(p.val : ℤ)}) := by
  let : Fact p.val.Prime := ⟨p.property⟩
  let := Int.ideal_span_isMaximal_of_prime p.val
  exact IsDedekindDomain.mem_primesOverFinset_iff (by simp [p.property.ne_zero]) _

private def fromAbove (K : Type*) [Field K] [NumberField K]
    (x : Σ p : Nat.Primes, primeIdealsAbove K p) :
    {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} := by
  refine ⟨x.2.val, ?_⟩
  obtain ⟨hP, hLie⟩ := (above_spec x.1).mp x.2.property
  exact ⟨hP, Ideal.ne_bot_of_liesOver_of_ne_bot
    (p := Ideal.span {(x.1.val : ℤ)}) (by simp [x.1.property.ne_zero]) x.2.val⟩

private theorem under_absNorm {K : Type*} [Field K] [NumberField K] (p : Nat.Primes)
    (P : primeIdealsAbove K p) : (P.val.under ℤ).absNorm = p.val := by
  have := ((above_spec p).mp P.property).2
  rw [← P.val.over_def (Ideal.span {(p.val : ℤ)})]
  simp

private noncomputable def primesAboveEquiv (K : Type*) [Field K] [NumberField K] :
    (Σ p : Nat.Primes, primeIdealsAbove K p) ≃ {P : Ideal (𝓞 K) // P.IsPrime ∧ P ≠ ⊥} :=
  Equiv.ofBijective (fromAbove K) <| by
    constructor
    · rintro ⟨p, P⟩ ⟨q, Q⟩ h
      have hPQ : P.val = Q.val := congrArg Subtype.val h
      have hpq : p = q := Subtype.ext <| (under_absNorm p P).symm.trans <|
        (congrArg (fun I : Ideal (𝓞 K) => (I.under ℤ).absNorm) hPQ).trans (under_absNorm q Q)
      subst q
      exact congrArg (Sigma.mk p) (Subtype.ext hPQ)
    · rintro ⟨P, hP, hne⟩
      let : P.IsPrime := hP
      let : NeZero P := ⟨hne⟩
      let p : Nat.Primes := ⟨(P.under ℤ).absNorm, Nat.absNorm_under_prime P⟩
      exact ⟨⟨p, ⟨P, (above_spec p).mpr ⟨hP, Int.liesOver_span_absNorm P⟩⟩⟩, rfl⟩

noncomputable def localPolynomial (K : Type*) [Field K] [NumberField K] (p : Nat.Primes)
    (s : ℂ) : ℂ := ∏ P ∈ primeIdealsAbove K p, (1 - (P.absNorm : ℂ) ^ (-s))

private theorem one_lt_ideal_norm {K : Type*} [Field K] [NumberField K] {p : Nat.Primes}
    {P : Ideal (𝓞 K)} (hP : P ∈ primeIdealsAbove K p) : 1 < P.absNorm := by
  obtain ⟨hprime, hlies⟩ := (above_spec p).mp hP
  have hne := Ideal.ne_bot_of_liesOver_of_ne_bot (p := Ideal.span {(p.val : ℤ)})
    (by simp [p.property.ne_zero]) P
  have hz := mt Ideal.absNorm_eq_zero_iff.mp hne
  have ho := mt Ideal.absNorm_eq_one_iff.mp hprime.ne_top
  omega

theorem localPolynomial_differentiable (K : Type*) [Field K] [NumberField K] (p : Nat.Primes) :
    Differentiable ℂ (localPolynomial K p) := by
  apply Differentiable.fun_finsetProd
  intro P hP
  have hn : 0 < P.absNorm := lt_trans zero_lt_one (one_lt_ideal_norm hP)
  let : NeZero (P.absNorm : ℂ) := ⟨Nat.cast_ne_zero.mpr hn.ne'⟩
  fun_prop

theorem localPolynomial_ne_zero (K : Type*) [Field K] [NumberField K] (p : Nat.Primes)
    {s : ℂ} (hs : 0 < s.re) : localPolynomial K p s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro P hP hzero
  have hn : 1 < (P.absNorm : ℝ) := by exact_mod_cast one_lt_ideal_norm hP
  have hn' : ‖(P.absNorm : ℂ) ^ (-s)‖ < 1 := by
    change ‖((P.absNorm : ℝ) : ℂ) ^ (-s)‖ < 1
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith)]
    exact Real.rpow_lt_one_of_one_lt_of_neg hn (by simpa)
  rw [← sub_eq_zero.mp hzero, norm_one] at hn'
  exact hn'.false

theorem dedekindZeta_hasProd_rationalPrimes (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (localPolynomial K p s)⁻¹) (dedekindZeta K s) := by
  classical
  have h := (primesAboveEquiv K).hasProd_iff.mpr
    (Chebotarev.dedekindZeta_hasProd_primeIdeal K hs)
  refine h.sigma fun p => ?_
  change HasProd (fun P : primeIdealsAbove K p => (1 - (P.val.absNorm : ℂ) ^ (-s))⁻¹) _
  rw [localPolynomial, ← Finset.prod_inv_distrib, ← Finset.prod_attach,
    ← Finset.prod_coe_sort_eq_attach]
  exact hasProd_fintype _

/-- When all primes above a rational prime have degree `f`, their common norm is `p ^ f`. -/
theorem localPolynomial_of_uniform_inertia {K : Type*} [Field K] [NumberField K]
    (p : Nat.Primes) {f : ℕ}
    (hf : ∀ (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(p.val : ℤ)})],
      P.inertiaDeg ℤ = f) (s : ℂ) :
    localPolynomial K p s = (1 - ((p.val : ℂ) ^ (-s)) ^ f) ^ (primeIdealsAbove K p).card := by
  classical
  unfold localPolynomial
  rw [← Finset.prod_const]
  apply Finset.prod_congr rfl
  intro P hP
  obtain ⟨hprime, hlies⟩ := (above_spec p).mp hP
  rw [← Ideal.pow_inertiaDeg p.val P, hf P, Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

/-- For a quadratic field the splitting law can be supplied prime by prime.
Matching these polynomials proves the factorization on the full half-plane of convergence. -/
theorem quadratic_factorization_of_local_factors {K : Type*} [Field K] [NumberField K]
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hlocal : ∀ (p : Nat.Primes) (s : ℂ), 1 < s.re →
      localPolynomial K p s = (1 - (p.val : ℂ) ^ (-s)) * (1 - χ p.val * (p.val : ℂ) ^ (-s)))
    {s : ℂ} (hs : 1 < s.re) : dedekindZeta K s = riemannZeta s * χ.LFunction s := by
  rw [χ.LFunction_eq_LSeries hs]
  apply (dedekindZeta_hasProd_rationalPrimes K hs).unique
  apply ((riemannZeta_eulerProduct_hasProd hs).mul (χ.LSeries_eulerProduct_hasProd hs)).congr_fun
  intro p
  simp only [hlocal p s hs, mul_inv_rev, mul_comm]

end OMA.AbelianERH

/- Splitting of rational primes in cyclotomic fields, including the ramified prime of ℚ(i). -/

namespace OMA.AbelianERH

open NumberField
open scoped NumberField

theorem card_primeIdealsAbove (K : Type*) [Field K] [NumberField K] (p : Nat.Primes) :
    (primeIdealsAbove K p).card = (Ideal.primesOver (Ideal.span {(p.val : ℤ)}) (𝓞 K)).ncard := by
  let : Fact p.val.Prime := ⟨p.property⟩
  let := Int.ideal_span_isMaximal_of_prime p.val
  rw [← IsDedekindDomain.coe_primesOverFinset (p := Ideal.span {(p.val : ℤ)})
    (by simp [p.property.ne_zero]) (𝓞 K), Set.ncard_coe_finset]

theorem cyclotomic_unramified_count (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (p : Nat.Primes) (hp : ¬ p.val ∣ n) :
    (primeIdealsAbove K p).card * orderOf (p.val : ZMod n) = n.totient := by
  let : Fact p.val.Prime := ⟨p.property⟩
  let := Int.ideal_span_isMaximal_of_prime p.val
  let : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (Ideal.span {(p.val : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rwa [← card_primeIdealsAbove K p,
    IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p.val K hp, one_mul,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p.val K hp,
    IsGaloisGroup.card_eq_finrank Gal(K/ℚ) ℚ K, IsCyclotomicExtension.Rat.finrank n K] at h

theorem cyclotomic_unramified_polynomial (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (p : Nat.Primes) (hp : ¬ p.val ∣ n) (s : ℂ) :
    localPolynomial K p s = (1 - ((p.val : ℂ) ^ (-s)) ^ orderOf (p.val : ZMod n)) ^
      (primeIdealsAbove K p).card := by
  let : Fact p.val.Prime := ⟨p.property⟩
  exact localPolynomial_of_uniform_inertia p
    (fun P _ _ => IsCyclotomicExtension.Rat.inertiaDeg_eq_of_not_dvd p.val K P hp) s

/-- The complex primitive character of discriminant −4. -/
abbrev gaussianChar : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

theorem gaussianChar_isPrimitive : gaussianChar.IsPrimitive := by
  rw [DirichletCharacter.isPrimitive_def]
  have hd := gaussianChar.conductor_dvd_level
  have hodd : gaussianChar (-1) = -1 := by
    change ((ZMod.χ₄ (-1) : ℤ) : ℂ) = -1
    rw [show ZMod.χ₄ (-1) = -1 by decide]
    norm_num
  by_contra hn
  have hd2 : gaussianChar.conductor ∣ 2 := by
    have : gaussianChar.conductor ∈ (4 : ℕ).divisors := Nat.mem_divisors.mpr ⟨hd, by decide⟩
    have hset : (4 : ℕ).divisors = {1, 2, 4} := by decide
    rw [hset] at this
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    rcases this with h | h | h <;> simp_all
  have hc : IsCoprime (-1 : ℤ) (4 : ℕ) := ⟨-1, 0, by norm_num⟩
  have he := gaussianChar.primitiveCharacter_apply_of_isCoprime hc
  have hcast : (-1 : ZMod gaussianChar.conductor) = 1 := by
    have h2 : (2 : ZMod gaussianChar.conductor) = 0 := by
      simpa using (ZMod.natCast_eq_zero_iff 2 gaussianChar.conductor).mpr hd2
    linear_combination -h2
  simp only [Int.cast_neg, Int.cast_one, hcast, map_one, hodd] at he
  norm_num at he

/-- The three local splitting types of rational primes in the fourth cyclotomic field give
the classical Euler factor (1 − x)(1 − χ₄(p)x), including p = 2. -/
theorem gaussian_localPolynomial (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {4} ℚ K] (p : Nat.Primes) (s : ℂ) :
    localPolynomial K p s =
      (1 - (p.val : ℂ) ^ (-s)) * (1 - gaussianChar p.val * (p.val : ℂ) ^ (-s)) := by
  let : Fact p.val.Prime := ⟨p.property⟩
  by_cases h₂ : p.val = 2
  · have hp : p = ⟨2, Nat.prime_two⟩ := Subtype.ext h₂
    subst p
    let : IsCyclotomicExtension {2 ^ (1 + 1)} ℚ K := inferInstanceAs
      (IsCyclotomicExtension {4} ℚ K)
    have hc := (card_primeIdealsAbove K ⟨2, Nat.prime_two⟩).trans
      (IsCyclotomicExtension.Rat.ncard_primesOver_of_prime_pow 2 1 K)
    rw [localPolynomial_of_uniform_inertia (K := K) (⟨2, Nat.prime_two⟩ : Nat.Primes) (f := 1)
      (fun P _ _ => IsCyclotomicExtension.Rat.inertiaDeg_eq_of_prime_pow 2 1 K P) s, hc]
    have hχ : gaussianChar (2 : ℕ) = 0 := by
      change ((ZMod.χ₄ (2 : ZMod 4) : ℤ) : ℂ) = 0
      norm_num [show ZMod.χ₄ 2 = 0 from rfl]
    simp only [pow_one, hχ, zero_mul, sub_zero, mul_one]
  · have hnd : ¬ p.val ∣ 4 := by
      intro h
      have := p.property.dvd_of_dvd_pow (show p.val ∣ 2 ^ 2 from h)
      exact h₂ ((Nat.prime_dvd_prime_iff_eq p.property Nat.prime_two).mp this)
    have hodd := p.property.eq_two_or_odd.resolve_left h₂
    have hc := cyclotomic_unramified_count 4 K p hnd
    rw [cyclotomic_unramified_polynomial 4 K p hnd]
    have hφ : Nat.totient 4 = 2 := by decide
    rw [hφ] at hc
    rcases (show p.val % 4 = 1 ∨ p.val % 4 = 3 by omega) with h1 | h3
    · have hmod : (p.val : ZMod 4) = 1 := by
        simpa using (ZMod.natCast_eq_natCast_iff' p.val 1 4).mpr h1
      have hχ : gaussianChar p.val = 1 := by
        change ((ZMod.χ₄ p.val : ℤ) : ℂ) = 1
        rw [ZMod.χ₄_nat_one_mod_four h1, Int.cast_one]
      rw [hmod, orderOf_one, mul_one] at hc
      rw [hc, hχ, hmod, orderOf_one, pow_one, one_mul, sq]
    · have hmod : (p.val : ZMod 4) = 3 := by
        simpa using (ZMod.natCast_eq_natCast_iff' p.val 3 4).mpr h3
      have horder : orderOf (3 : ZMod 4) = 2 :=
        orderOf_eq_prime (by decide) (by decide)
      have hχ : gaussianChar p.val = -1 := by
        change ((ZMod.χ₄ p.val : ℤ) : ℂ) = -1
        rw [ZMod.χ₄_nat_three_mod_four h3]
        norm_num
      rw [hmod, horder] at hc
      have hcount : (primeIdealsAbove K p).card = 1 := by omega
      rw [hχ, hmod, horder, hcount, pow_one]
      ring

theorem gaussian_factorization (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {4} ℚ K] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s * gaussianChar.LFunction s :=
  quadratic_factorization_of_local_factors gaussianChar (fun p s _ => gaussian_localPolynomial K p s) hs

end OMA.AbelianERH

/- Grouping the Euler factors of all Dirichlet characters according to their values
at one unit. The finite root-product identity is from the merged RegularPrimes
R3.H2.R1.H1 proof, adapted there from Riccardo Brasca et al., KummerCriterion, Apache-2.0. -/

namespace OMA.AbelianERH

lemma prod_nthRootsFinset_one_sub_mul (d : ℕ) (hd : 0 < d) (T : ℂ) :
    ∏ ζ ∈ Polynomial.nthRootsFinset d (1 : ℂ), (1 - ζ * T) = 1 - T ^ d := by
  by_cases hT : T = 0
  · subst hT
    simp [zero_pow hd.ne']
  · have hζ : IsPrimitiveRoot (Complex.exp (2 * Real.pi * Complex.I / d)) d :=
      Complex.isPrimitiveRoot_exp d hd.ne'
    have hcard : (Polynomial.nthRootsFinset d (1 : ℂ)).card = d := hζ.card_nthRootsFinset
    have hpoly : Polynomial.X ^ d - 1 = ∏ ζ ∈ Polynomial.nthRootsFinset d (1 : ℂ),
        (Polynomial.X - Polynomial.C ζ) := Polynomial.X_pow_sub_one_eq_prod hd hζ
    have heval := congrArg (Polynomial.eval T⁻¹) hpoly
    simp only [Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_sub,
      Polynomial.eval_one, Polynomial.eval_prod, Polynomial.eval_C] at heval
    have key : ∀ ζ : ℂ, (1 - ζ * T) = T * (T⁻¹ - ζ) := fun ζ => by field_simp
    rw [Finset.prod_congr rfl (fun ζ _ => key ζ), Finset.prod_mul_distrib,
      Finset.prod_const, hcard, ← heval]
    have hTT : T ^ d * T⁻¹ ^ d = 1 := by rw [← mul_pow, mul_inv_cancel₀ hT, one_pow]
    linear_combination hTT

private noncomputable def characterEval {n : ℕ} (u : (ZMod n)ˣ) :
    DirichletCharacter ℂ n →* rootsOfUnity (orderOf u) ℂ where
  toFun χ := ⟨χ.toUnitHom u, by
    rw [mem_rootsOfUnity, ← map_pow, pow_orderOf_eq_one, map_one]⟩
  map_one' := Subtype.ext <| Units.ext (MulChar.one_apply u.isUnit)
  map_mul' χ ψ := Subtype.ext <| Units.ext (MulChar.mul_apply χ ψ u)

private theorem characterEval_surjective {n : ℕ} [NeZero n] (u : (ZMod n)ˣ) :
    Function.Surjective (characterEval u) := by
  classical
  let : NeZero (orderOf u) := ⟨(orderOf_pos u).ne'⟩
  let e := characterEval u
  apply MonoidHom.range_eq_top.mp
  apply e.range.eq_top_of_card_eq
  apply le_antisymm (Nat.card_le_card_of_injective _ Subtype.val_injective)
  rw [Complex.card_rootsOfUnity]
  apply Nat.le_of_dvd Nat.card_pos
  apply orderOf_dvd_of_pow_eq_one
  apply Units.ext
  by_contra hn
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity ℂ hn
  have h : (⟨e χ, ⟨χ, rfl⟩⟩ : e.range) ^ Nat.card e.range = 1 := pow_card_eq_one'
  apply hχ
  change χ ((u : ZMod n) ^ Nat.card e.range) = 1
  rw [map_pow]
  exact congrArg (fun z : e.range => (((z.val.val : ℂˣ) : ℂ))) h

private theorem roots_product (d : ℕ) [NeZero d] [Fintype (rootsOfUnity d ℂ)] (T : ℂ) :
    (∏ z : rootsOfUnity d ℂ, (1 - ((z.val : ℂˣ) : ℂ) * T)) = 1 - T ^ d := by
  classical
  let e : rootsOfUnity d ℂ ≃ ↥(Polynomial.nthRootsFinset d (1 : ℂ)) :=
    (rootsOfUnityEquivNthRoots ℂ d).trans (Equiv.subtypeEquivRight fun _ =>
      Multiset.mem_toFinset.symm)
  calc
    _ = ∏ z : ↥(Polynomial.nthRootsFinset d (1 : ℂ)), (1 - z.val * T) :=
      Fintype.prod_equiv e _ _ (fun _ => rfl)
    _ = _ := by
      rw [Finset.prod_coe_sort_eq_attach, Finset.prod_attach _ (fun z : ℂ => 1 - z * T),
        prod_nthRootsFinset_one_sub_mul d (NeZero.pos d)]

/-- Every root of unity of order dividing the order of a unit occurs equally often
among the values of all Dirichlet characters at that unit. -/
theorem character_product_at_unit {n : ℕ} [NeZero n] (u : (ZMod n)ˣ) (T : ℂ) :
    (∏ χ : DirichletCharacter ℂ n, (1 - χ u * T)) =
      (1 - T ^ orderOf u) ^ (n.totient / orderOf u) := by
  classical
  let : NeZero (orderOf u) := ⟨(orderOf_pos u).ne'⟩
  let e := characterEval u
  let := Fintype.ofFinite (rootsOfUnity (orderOf u) ℂ)
  have hsur : Function.Surjective e := characterEval_surjective u
  have hc : Nat.card e.ker = n.totient / orderOf u := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup e.ker
    rw [DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective e hsur).toEquiv,
      Complex.card_rootsOfUnity] at h
    rw [h, Nat.mul_div_cancel_left _ (orderOf_pos u)]
  let a (z : rootsOfUnity (orderOf u) ℂ) := 1 - ((z.val : ℂˣ) : ℂ) * T
  change (∏ χ, a (e χ)) = _
  rw [← Fintype.prod_fiberwise' e a]
  have hf (z : rootsOfUnity (orderOf u) ℂ) :
      Fintype.card {χ // e χ = z} = Nat.card e.ker := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective hsur z)
  simp only [Finset.prod_const, Finset.card_univ, hf, hc]
  rw [Finset.prod_pow, show ∏ z, a z = 1 - T ^ orderOf u from roots_product _ T]

end OMA.AbelianERH

/- Dedekind zeros of cyclotomic fields and Dirichlet zeros at arbitrary conductor. -/

namespace OMA.AbelianERH

open NumberField Complex Set
open scoped NumberField

noncomputable def characterPolynomial (n : ℕ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∏ χ : DirichletCharacter ℂ n, (1 - χ p.val * (p.val : ℂ) ^ (-s))

private theorem characterPolynomial_of_dvd (n : ℕ) [NeZero n] (p : Nat.Primes) (hp : p.val ∣ n)
    (s : ℂ) : characterPolynomial n p s = 1 := by
  have hu : ¬ IsUnit (p.val : ZMod n) := by
    rwa [ZMod.isUnit_iff_coprime, p.property.coprime_iff_not_dvd, not_not]
  exact Finset.prod_eq_one fun χ _ => by rw [χ.map_nonunit hu, zero_mul, sub_zero]

theorem cyclotomic_good_localPolynomial (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (p : Nat.Primes) (hp : ¬ p.val ∣ n) (s : ℂ) :
    localPolynomial K p s = characterPolynomial n p s := by
  let u := ZMod.unitOfCoprime p.val (p.property.coprime_iff_not_dvd.mpr hp)
  have ho : orderOf (p.val : ZMod n) = orderOf u :=
    orderOf_injective (Units.coeHom (ZMod n)) Units.coeHom_injective u
  have hcount := cyclotomic_unramified_count n K p hp
  rw [ho] at hcount
  rw [cyclotomic_unramified_polynomial n K p hp s, ho]
  change _ = ∏ χ : DirichletCharacter ℂ n, (1 - χ u * (p.val : ℂ) ^ (-s))
  rw [character_product_at_unit, ← hcount, Nat.mul_div_cancel _ (orderOf_pos u)]

noncomputable def excludedPrimes (n : ℕ) : Finset Nat.Primes := n.primeFactors.subtype Nat.Prime

noncomputable def ramifiedFactors (n : ℕ) (K : Type*) [Field K] [NumberField K] (s : ℂ) : ℂ :=
  ∏ p ∈ excludedPrimes n, localPolynomial K p s

theorem ramifiedFactors_ne_zero (n : ℕ) (K : Type*) [Field K] [NumberField K]
    {s : ℂ} (hs : 0 < s.re) : ramifiedFactors n K s ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun p _ => localPolynomial_ne_zero K p hs

theorem ramifiedFactors_differentiable (n : ℕ) (K : Type*) [Field K] [NumberField K] :
    Differentiable ℂ (ramifiedFactors n K) :=
  Differentiable.fun_finsetProd fun p _ => localPolynomial_differentiable K p

/-- The product of all characters of level n omits exactly the primes over the divisors of n. -/
theorem cyclotomic_LProduct (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {s : ℂ} (hs : 1 < s.re) :
    (∏ χ : DirichletCharacter ℂ n, χ.LFunction s) =
      dedekindZeta K s * ramifiedFactors n K s := by
  classical
  have hchar : HasProd (fun p => (characterPolynomial n p s)⁻¹)
      (∏ χ : DirichletCharacter ℂ n, χ.LFunction s) := by
    simp only [DirichletCharacter.LFunction_eq_LSeries _ hs, characterPolynomial, ← Finset.prod_inv_distrib]
    exact hasProd_prod fun χ _ => χ.LSeries_eulerProduct_hasProd hs
  let c (p : Nat.Primes) := if p ∈ excludedPrimes n then localPolynomial K p s else 1
  have hcorr : HasProd c (ramifiedFactors n K s) := by
    have h : HasProd c (∏ p ∈ excludedPrimes n, c p) :=
      hasProd_prod_of_ne_finset_one (s := excludedPrimes n) (f := c)
      (fun p hp => if_neg hp)
    convert h using 1
    exact Finset.prod_congr rfl fun p hp => (if_pos hp).symm
  apply hchar.unique
  apply ((dedekindZeta_hasProd_rationalPrimes K hs).mul hcorr).congr_fun
  intro p
  have hmem : p ∈ excludedPrimes n ↔ p.val ∣ n := by
    have he : p ∈ excludedPrimes n ↔ p.val ∈ n.primeFactors := Finset.mem_subtype
    rw [he, Nat.mem_primeFactors]
    simp [p.property, NeZero.ne n]
  by_cases hp : p.val ∣ n
  · simp [c, hmem.mpr hp, characterPolynomial_of_dvd n p hp,
      localPolynomial_ne_zero K p (lt_trans zero_lt_one hs)]
  · simp [c, mt hmem.mp hp, cyclotomic_good_localPolynomial n K p hp]

/-- The cross-multiplied identity continues across the critical strip, including fields
whose conductor has several ramified primes. -/
theorem cyclotomic_continuation_product (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {Z : ℂ → ℂ} (hZ : ERH.IsDedekindZeta K Z)
    {s : ℂ} (hs : s ≠ 1) :
    (∏ χ : DirichletCharacter ℂ n, χ.LFunction s) = Z s * ramifiedFactors n K s := by
  refine eqOffOne_of_halfPlane (Z := fun w => ∏ χ : DirichletCharacter ℂ n, χ.LFunction w)
    (W := fun w => Z w * ramifiedFactors n K w) ?_ ?_ ?_ hs
  · exact DifferentiableOn.fun_finsetProd fun χ _ w hw =>
      (χ.differentiableAt_LFunction w (Or.inl hw)).differentiableWithinAt
  · exact hZ.1.mul (ramifiedFactors_differentiable n K).differentiableOn
  · intro w hw
    rw [hZ.2 w hw, cyclotomic_LProduct n K hw]

/-- In the positive half-plane off the pole, Dedekind zeros are exactly the zeros of
primitive characters induced by level-n characters. -/
theorem cyclotomic_zero_iff (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] {Z : ℂ → ℂ} (hZ : ERH.IsDedekindZeta K Z)
    {s : ℂ} (hpos : 0 < s.re) (hs : s ≠ 1) :
    Z s = 0 ↔ ∃ χ : DirichletCharacter ℂ n,
      letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
      χ.primitiveCharacter.LFunction s = 0 := by
  classical
  have hmul : Z s * ramifiedFactors n K s = 0 ↔ Z s = 0 :=
    mul_eq_zero.trans (or_iff_left (ramifiedFactors_ne_zero n K hpos))
  rw [← hmul,
    ← cyclotomic_continuation_product n K hZ hs, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and]
  apply exists_congr
  intro χ
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact lFunction_zero_iff_primitive_zero χ hpos hs

theorem cyclotomic_erh (n : ℕ) [NeZero n] (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {n} ℚ K] (h : PrimitiveStripGRH) : ERH.ExtendedRiemannHypothesis K := by
  intro Z hZ s hpos hlt hz
  obtain ⟨χ, hχ⟩ := (cyclotomic_zero_iff n K hZ hpos (fun e => by simp [e] at hlt)).mp hz
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  exact h _ _ χ.primitiveCharacter_isPrimitive s hpos hlt hχ

end OMA.AbelianERH

/- Exact Gaussian and rational factorizations. The ideal count over ℚ and invariance under
field isomorphism are from the merged ERH reductions R1 and R1.H1.R1. -/

namespace OMA.AbelianERH

open NumberField Complex Set
open scoped NumberField

theorem dedekindZeta_eq_of_ringEquiv {K L : Type*} [Field K] [Field L] [NumberField K]
    [NumberField L] (e : K ≃+* L) : dedekindZeta K = dedekindZeta L := by
  let r : 𝓞 K ≃+* 𝓞 L := RingOfIntegers.mapRingEquiv e
  let i : Ideal (𝓞 K) ≃ Ideal (𝓞 L) := (Ideal.relIsoOfBijective r.toRingHom r.bijective).symm.toEquiv
  have hnorm (I : Ideal (𝓞 K)) : Ideal.absNorm I = Ideal.absNorm (i I) :=
    Nat.card_congr (Ideal.quotientEquiv I (i I) r rfl).toEquiv
  have hcard (n : ℕ) : Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n} =
      Nat.card {J : Ideal (𝓞 L) // Ideal.absNorm J = n} :=
    Nat.card_congr (i.subtypeEquiv fun I => by rw [hnorm I])
  funext z
  simp only [dedekindZeta, hcard]


theorem int_ideal_of_norm (I : Ideal ℤ) : I = Ideal.span {(Ideal.absNorm I : ℤ)} := by
  obtain ⟨a, rfl⟩ := (inferInstance : I.IsPrincipal).principal
  rw [Ideal.absNorm_span_singleton, Algebra.norm_self, MonoidHom.id_apply, Int.span_natAbs]

theorem int_ideals_of_norm_card (n : ℕ) :
    Nat.card {I : Ideal ℤ // Ideal.absNorm I = n} = 1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨Ideal.span {(n : ℤ)}, by simp⟩, ?_⟩
  intro J
  apply Subtype.ext
  simpa only [J.property] using int_ideal_of_norm J.val

theorem rational_ideals_of_norm_card (n : ℕ) :
    Nat.card {I : Ideal (𝓞 ℚ) // Ideal.absNorm I = n} = 1 := by
  let e := Rat.ringOfIntegersEquiv
  let i : Ideal (𝓞 ℚ) ≃ Ideal ℤ := (Ideal.relIsoOfBijective e.toRingHom e.bijective).symm.toEquiv
  have hi (J : Ideal (𝓞 ℚ)) : Ideal.absNorm J = Ideal.absNorm (i J) :=
    Nat.card_congr (Ideal.quotientEquiv J (i J) e rfl).toEquiv
  exact (Nat.card_congr (i.subtypeEquiv (p := fun J => Ideal.absNorm J = n)
    (q := fun J => Ideal.absNorm J = n) (fun J => by rw [hi J]))).trans (int_ideals_of_norm_card n)

theorem zeta_eq_in_half_plane {z : ℂ} (hz : 1 < z.re) : dedekindZeta ℚ z = riemannZeta z := by
  calc dedekindZeta ℚ z = LSeries (1 : ℕ → ℂ) z := by
         apply LSeries_congr
         intro n _
         simp [rational_ideals_of_norm_card]
       _ = riemannZeta z := LSeries_one_eq_riemannZeta hz

theorem degree_one_factorization (K : Type*) [Field K] [NumberField K]
    (hd : Module.finrank ℚ K = 1) {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s := by
  let e : ℚ ≃+* K := RingEquiv.ofBijective (algebraMap ℚ K)
    (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hd)
  exact (congrFun (dedekindZeta_eq_of_ringEquiv e) s).symm.trans (zeta_eq_in_half_plane hs)

theorem degree_one_erh_of_rh {K : Type*} [Field K] [NumberField K] (hd : Module.finrank ℚ K = 1)
    (h : RiemannHypothesis) : ERH.ExtendedRiemannHypothesis K := by
  intro Z hZ s hpos hlt hz
  have hs : s ≠ 1 := fun e => by simp [e] at hlt
  have hR : ERH.IsDedekindZeta K riemannZeta :=
    ⟨analyticOn_riemannZeta.differentiableOn, fun w hw => (degree_one_factorization K hd hw).symm⟩
  rw [continuation_unique hZ hR hs] at hz
  apply h s hz _ hs
  rintro ⟨n, rfl⟩
  simp at hpos
  linarith [Nat.cast_nonneg (α := ℝ) n]

/-- A quadratic zeta-times-L factorization on the half-plane identifies every continuation
away from 1, and supplies one unconditionally whenever the factorization is known. -/
theorem isDedekindZeta_quadratic_product {K : Type*} [Field K] [NumberField K]
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hf : ∀ w : ℂ, 1 < w.re → dedekindZeta K w = riemannZeta w * χ.LFunction w) :
    ERH.IsDedekindZeta K (fun w => riemannZeta w * χ.LFunction w) :=
  ⟨analyticOn_riemannZeta.differentiableOn.mul
      (fun s hs => (χ.differentiableAt_LFunction s (Or.inl hs)).differentiableWithinAt),
    fun w hw => (hf w hw).symm⟩

theorem gaussian_continuation (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {4} ℚ K] :
    ERH.IsDedekindZeta K (fun s => riemannZeta s * gaussianChar.LFunction s) :=
  isDedekindZeta_quadratic_product gaussianChar (fun _ => gaussian_factorization K)

theorem gaussian_zero_iff (K : Type*) [Field K] [NumberField K]
    [IsCyclotomicExtension {4} ℚ K] {Z : ℂ → ℂ} (hZ : ERH.IsDedekindZeta K Z)
    {s : ℂ} (hs : s ≠ 1) : Z s = 0 ↔ riemannZeta s = 0 ∨ gaussianChar.LFunction s = 0 := by
  rw [continuation_unique hZ (gaussian_continuation K) hs, mul_eq_zero]

end OMA.AbelianERH

/- A Dirichlet character recording the splitting of x² − D away from 2D. -/

namespace OMA.AbelianERH

private theorem odd_val_of_unit {D : ℤ} (hD : D ≠ 0) {u : ZMod (4 * D.natAbs)} (hu : IsUnit u) :
    Odd u.val := by
  let : NeZero (4 * D.natAbs) := ⟨Nat.mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hD)⟩
  have hcop := (ZMod.isUnit_iff_coprime u.val (4 * D.natAbs)).mp (by simpa using hu)
  exact Nat.coprime_two_right.mp (hcop.coprime_dvd_right (by omega : 2 ∣ 4 * D.natAbs))

noncomputable def discriminantChar (D : ℤ) (hD : D ≠ 0) : DirichletCharacter ℂ (4 * D.natAbs) := by
  classical
  let : NeZero (4 * D.natAbs) := ⟨Nat.mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hD)⟩
  have hN : 1 < 4 * D.natAbs := by
    have := Int.natAbs_pos.mpr hD
    omega
  refine { toFun := fun z => if IsUnit z then (jacobiSym D z.val : ℂ) else 0
           map_one' := ?_, map_mul' := ?_, map_nonunit' := ?_ }
  · simp [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt hN]
  · intro x y
    by_cases hx : IsUnit x <;> by_cases hy : IsUnit y <;> simp only [IsUnit.mul_iff, hx, hy,
      and_self, false_and, and_false, if_true, if_false, zero_mul, mul_zero]
    have hxo := odd_val_of_unit hD hx
    have hyo := odd_val_of_unit hD hy
    rw [ZMod.val_mul, ← jacobiSym.mod_right D (hxo.mul hyo),
      jacobiSym.mul_right' D hxo.pos.ne' hyo.pos.ne', Int.cast_mul]
  · intro z hz
    exact if_neg hz

theorem discriminantChar_prime {D : ℤ} (hD : D ≠ 0) (p : Nat.Primes) [Fact p.val.Prime]
    (hp : ¬ p.val ∣ 4 * D.natAbs) :
    discriminantChar D hD p.val = (legendreSym p.val D : ℂ) := by
  let : NeZero (4 * D.natAbs) := ⟨Nat.mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hD)⟩
  have hu := (ZMod.isUnit_iff_coprime p.val (4 * D.natAbs)).mpr
    (p.property.coprime_iff_not_dvd.mpr hp)
  have hodd : Odd p.val := Nat.coprime_two_right.mp <|
    (p.property.coprime_iff_not_dvd.mpr hp).coprime_dvd_right (by omega : 2 ∣ 4 * D.natAbs)
  simp only [discriminantChar, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, hu, if_true,
    ZMod.val_natCast, ← jacobiSym.mod_right D hodd, jacobiSym.legendreSym.to_jacobiSym]

theorem discriminantChar_isQuadratic (D : ℤ) (hD : D ≠ 0) :
    (discriminantChar D hD).IsQuadratic := by
  intro u
  by_cases hu : IsUnit u
  · simp only [discriminantChar, MulChar.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk, hu, if_true]
    rcases jacobiSym.trichotomy D u.val with h | h | h <;> simp [h]
  · exact Or.inl ((discriminantChar D hD).map_nonunit hu)

theorem primitiveCharacter_isQuadratic {m : ℕ} [NeZero m] (χ : DirichletCharacter ℂ m)
    (hχ : χ.IsQuadratic) : χ.primitiveCharacter.IsQuadratic := by
  apply MulChar.isQuadratic_iff_sq_eq_one.mpr
  apply DirichletCharacter.changeLevel_injective χ.conductor_dvd_level
  rw [map_pow, map_one, χ.changeLevel_primitiveCharacter, hχ.sq_eq_one]

end OMA.AbelianERH

/- A square-root generator for any quadratic number field and the finite exceptional index. -/

namespace OMA.AbelianERH

open NumberField Polynomial IntermediateField
open scoped NumberField IntermediateField

theorem generator_exponent_ne_zero {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K)
    (hdeg : (minpoly ℤ θ).natDegree = Module.finrank ℚ K) : RingOfIntegers.exponent θ ≠ 0 := by
  let A := Algebra.adjoin ℤ ({θ} : Set (𝓞 K))
  let M := A.toSubmodule
  have heq : Module.finrank ℤ M = Module.finrank ℤ (𝓞 K) := by
    change Module.finrank ℤ A = _
    rw [(Algebra.adjoin.powerBasis' θ.isIntegral).finrank, Algebra.adjoin.powerBasis'_dim,
      RingOfIntegers.rank, hdeg]
  let := M.finiteQuotientOfFreeOfRankEq heq
  let m := Nat.card ((𝓞 K) ⧸ M)
  have hm : 0 < m := Nat.card_pos
  have hmem : (m : ℤ) ∈ (Ideal.under ℤ (conductor ℤ θ)) := by
    apply mem_conductor_iff.mpr
    intro x
    simp only [map_natCast]
    change (m : 𝓞 K) * x ∈ M
    have hq : M.mkQ (m • x) = 0 := by rw [map_nsmul]; exact card_nsmul_eq_zero'
    simpa only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, nsmul_eq_mul] using hq
  intro hzero
  have ht : Ideal.under ℤ (conductor ℤ θ) = ⊥ := Ideal.absNorm_eq_zero_iff.mp hzero
  rw [ht, Ideal.mem_bot] at hmem
  exact hm.ne' (by exact_mod_cast hmem)

theorem quadratic_generator (K : Type*) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2) :
    ∃ (D : ℤ) (θ : 𝓞 K), D ≠ 0 ∧ minpoly ℤ θ = X ^ 2 - C D ∧
      RingOfIntegers.exponent θ ≠ 0 := by
  let : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  have hroots : (primitiveRoots (Module.finrank ℚ K) ℚ).Nonempty := by
    rw [hK]
    exact ⟨-1, (mem_primitiveRoots (by decide)).mpr (IsPrimitiveRoot.neg_one 0 (by decide))⟩
  obtain ⟨α, ⟨a, ha⟩, hα⟩ := exists_root_adjoin_eq_top_of_isCyclic ℚ K hroots
  rw [hK] at ha
  let x : K := a.den * α
  let D : ℤ := a.num * a.den
  have hd : (a.den : K) ≠ 0 := Nat.cast_ne_zero.mpr a.den_ne_zero
  have hnum : (a : K) * (a.den : K) = a.num := by
    have hrat := (div_eq_iff (Nat.cast_ne_zero.mpr a.den_ne_zero : (a.den : ℚ) ≠ 0)).mp a.num_div_den
    exact_mod_cast hrat.symm
  have hx2 : x ^ 2 = (D : K) := by
    dsimp [x, D]
    push_cast
    rw [mul_pow, ← ha]
    change (a.den : K) ^ 2 * (a : K) = _
    linear_combination (a.den : K) * hnum
  have hxgen : ℚ⟮x⟯ = ⊤ := by
    apply top_unique
    rw [← hα, adjoin_simple_le_iff]
    have hxmem := mem_adjoin_simple_self ℚ x
    have he : α = x / (a.den : K) := (eq_div_iff hd).mpr (mul_comm _ _)
    rw [he]
    exact div_mem hxmem (_root_.natCast_mem _ _)
  have hD : D ≠ 0 := by
    intro hz
    rw [hz, Int.cast_zero, sq_eq_zero_iff] at hx2
    have hb : Module.finrank ℚ (⊥ : IntermediateField ℚ K) = Module.finrank ℚ (⊤ : IntermediateField ℚ K) :=
      congrArg (fun M : IntermediateField ℚ K => Module.finrank ℚ M) (by simpa [hx2] using hxgen)
    simp [hK] at hb
  have hmonic := monic_X_pow_sub_C D (by decide : (2 : ℕ) ≠ 0)
  have hroot : aeval x (X ^ 2 - C D) = 0 := by simp [hx2]
  let θ : 𝓞 K := ⟨x, ⟨_, hmonic, hroot⟩⟩
  have hirr : Irreducible (X ^ 2 - C (D : ℚ)) := by
    have hpow : x ^ Module.finrank ℚ K = algebraMap ℚ K (D : ℚ) := by simpa [hK] using hx2
    simpa [hK] using irreducible_X_pow_sub_C_of_root_adjoin_eq_top hpow hxgen
  have hminQ : minpoly ℚ x = X ^ 2 - C (D : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr (by simp [hx2]) (monic_X_pow_sub_C _ (by decide))).symm
  have hminZ : minpoly ℤ θ = X ^ 2 - C D := by
    apply Polynomial.map_injective (algebraMap ℤ ℚ) (FaithfulSMul.algebraMap_injective _ _)
    rw [← RingOfIntegers.minpoly_coe θ,
      ← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ θ.isIntegral_coe]
    change minpoly ℚ x = _
    simpa using hminQ
  exact ⟨D, θ, hD, hminZ, generator_exponent_ne_zero θ (by rw [hminZ, natDegree_X_pow_sub_C, hK])⟩

end OMA.AbelianERH

/- The local Euler factors of an integral square-root generator at good primes. -/

namespace OMA.AbelianERH

open NumberField Polynomial RingOfIntegers UniqueFactorizationMonoid
open scoped NumberField

theorem localPolynomial_kummerDedekind {K : Type*} [Field K] [NumberField K]
    (θ : 𝓞 K) (p : Nat.Primes) [Fact p.val.Prime] (hp : ¬ p.val ∣ exponent θ) (s : ℂ) :
    localPolynomial K p s = ∏ Q ∈ monicFactorsMod θ p.val,
      (1 - ((p.val : ℂ) ^ (-s)) ^ Q.natDegree) := by
  classical
  let := Int.ideal_span_isMaximal_of_prime p.val
  have hp₀ : (Ideal.span {(p.val : ℤ)} : Ideal ℤ) ≠ ⊥ := by simp [p.property.ne_zero]
  let e₁ : ↥(primeIdealsAbove K p) ≃ (Ideal.span {(p.val : ℤ)}).primesOver (𝓞 K) :=
    Equiv.subtypeEquivRight fun _ => IsDedekindDomain.mem_primesOverFinset_iff hp₀ _
  let e₂ := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hp
  let F (P : Ideal (𝓞 K)) := 1 - (P.absNorm : ℂ) ^ (-s)
  let G (Q : (ZMod p.val)[X]) := 1 - ((p.val : ℂ) ^ (-s)) ^ Q.natDegree
  have hq (Q : monicFactorsMod θ p.val) : F (e₂.symm Q).val = G Q := by
    let P := (e₂.symm Q).val
    have hP : P.IsPrime := (e₂.symm Q).property.1
    have hL : P.LiesOver (Ideal.span {(p.val : ℤ)}) := (e₂.symm Q).property.2
    have hf : P.inertiaDeg ℤ = Q.val.natDegree :=
      NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' hp Q.property
    change 1 - (P.absNorm : ℂ) ^ (-s) = _
    rw [← Ideal.pow_inertiaDeg p.val P, hf, Nat.cast_pow,
      ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]
  calc
    localPolynomial K p s = ∏ P : primeIdealsAbove K p, F P.val := by
      rw [Finset.prod_coe_sort_eq_attach, Finset.prod_attach _ F]
      rfl
    _ = ∏ Q : monicFactorsMod θ p.val, G Q.val := by
      apply Fintype.prod_equiv (e₁.trans e₂)
      intro P
      simpa [e₁] using hq (e₂ (e₁ P))
    _ = _ := by rw [Finset.prod_coe_sort_eq_attach, Finset.prod_attach _ G]

theorem squareRoot_localPolynomial {K : Type*} [Field K] [NumberField K]
    {D : ℤ} (hD : D ≠ 0) (θ : 𝓞 K) (hθ : minpoly ℤ θ = X ^ 2 - C D)
    (p : Nat.Primes) (hp : ¬ p.val ∣ 4 * D.natAbs) (hindex : ¬ p.val ∣ exponent θ) (s : ℂ) :
    localPolynomial K p s = (1 - (p.val : ℂ) ^ (-s)) *
      (1 - discriminantChar D hD p.val * (p.val : ℂ) ^ (-s)) := by
  classical
  let : Fact p.val.Prime := ⟨p.property⟩
  let x := (p.val : ℂ) ^ (-s)
  have hdisc : (D : ZMod p.val) ≠ 0 := by
    intro h
    have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd D p.val).mp h
    have hdvd' : p.val ∣ D.natAbs := by simpa using Int.natAbs_dvd_natAbs.mpr hdvd
    exact hp (dvd_mul_of_dvd_right hdvd' _)
  have htwo : (2 : ZMod p.val) ≠ 0 := by
    intro h
    have h2 : p.val ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p.val).mp (by simpa using h)
    exact hp (h2.trans (by omega))
  rw [localPolynomial_kummerDedekind θ p hindex, discriminantChar_prime hD p hp]
  have hm : (minpoly ℤ θ).map (Int.castRingHom (ZMod p.val)) = X ^ 2 - C (D : ZMod p.val) := by
    simp [hθ]
  unfold monicFactorsMod
  rw [hm]
  by_cases hsq : IsSquare (D : ZMod p.val)
  · rw [(legendreSym.eq_one_iff p.val hdisc).mpr hsq, Int.cast_one, one_mul]
    obtain ⟨r, hr⟩ := hsq
    have hr0 : r ≠ 0 := fun h => hdisc (by simp [hr, h])
    have hneg : r ≠ -r := by
      intro h
      apply (mul_ne_zero htwo hr0)
      linear_combination sub_eq_zero.mpr h
    have hpoly : (X ^ 2 - C (D : ZMod p.val)) =
        (X - C r) * (X - C (-r)) := by rw [hr, C_neg, C_mul]; ring
    have hdiff : (X - C r : (ZMod p.val)[X]) ≠ X - C (-r) := by
      intro he
      exact hneg (C_injective (sub_right_inj.mp he))
    rw [hpoly, normalizedFactors_mul (X_sub_C_ne_zero r) (X_sub_C_ne_zero (-r)),
      normalizedFactors_irreducible (irreducible_X_sub_C r),
      normalizedFactors_irreducible (irreducible_X_sub_C (-r)),
      (monic_X_sub_C r).normalize_eq_self, (monic_X_sub_C (-r)).normalize_eq_self]
    have hmem : (X - C r : (ZMod p.val)[X]) ∉ ({X - C (-r)} : Finset _) :=
      fun h => hdiff (Finset.mem_singleton.mp h)
    simp only [Multiset.toFinset_add, Multiset.toFinset_singleton, Finset.singleton_union,
      Finset.prod_insert hmem, Finset.prod_singleton, natDegree_X_sub_C, pow_one]
  · have hi : Irreducible (X ^ 2 - C (D : ZMod p.val)) :=
      X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two |>.mpr fun r hr =>
        hsq ⟨r, by simpa [sq] using hr.symm⟩
    rw [(legendreSym.eq_neg_one_iff p.val).mpr hsq, normalizedFactors_irreducible hi,
      (monic_X_pow_sub_C _ (by decide : 2 ≠ 0)).normalize_eq_self]
    simp only [Multiset.toFinset_singleton, Finset.prod_singleton, natDegree_X_pow_sub_C,
      Int.cast_neg, Int.cast_one, neg_one_mul]
    ring

end OMA.AbelianERH

namespace OMA.AbelianERH

open NumberField Complex Filter Set
open scoped Topology

/-- The class number formula forces a simple pole along the real axis. A square of the
Riemann zeta function with a nonvanishing correction would have a double pole. -/
theorem dedekind_no_double_riemann_pole (K : Type*) [Field K] [NumberField K]
    {A B : ℂ → ℂ} (hA : ContinuousAt A 1) (hB : ContinuousAt B 1) (hB₁ : B 1 ≠ 0)
    (heq : ∀ s : ℂ, 1 < s.re → dedekindZeta K s * A s =
      (riemannZeta s * riemannZeta s) * B s) : False := by
  have hembed : Tendsto ofReal (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℂ)) := by
    simpa using (continuous_ofReal.continuousAt (x := (1 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 1))
  have hpunct : Tendsto ofReal (𝓝[>] (1 : ℝ)) (𝓝[≠] (1 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr ⟨hembed, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact fun h => (ne_of_gt hx) (by exact_mod_cast (show (x : ℂ) = 1 from h))
  have hz : Tendsto (fun x : ℝ => ((x : ℂ) - 1) * riemannZeta x) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp hpunct
  have hd : Tendsto (fun x : ℝ => ((x : ℂ) - 1) * dedekindZeta K x)
      (𝓝[>] 1) (𝓝 ((dedekindZeta_residue K : ℝ) : ℂ)) := by
    simpa only [ofReal_sub, ofReal_one] using tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have hx : Tendsto (fun x : ℝ => (x : ℂ) - 1) (𝓝[>] 1) (𝓝 (0 : ℂ)) := by
    simpa using hembed.sub (tendsto_const_nhds (x := (1 : ℂ)))
  have hleft := (hx.mul hd).mul (hA.tendsto.comp hembed)
  have hright := (hz.mul hz).mul (hB.tendsto.comp hembed)
  have hlim : Tendsto (fun x : ℝ => (((x : ℂ) - 1) * riemannZeta x) *
        (((x : ℂ) - 1) * riemannZeta x) * B x) (𝓝[>] 1) (𝓝 0) := by
    simp only [zero_mul] at hleft
    apply hleft.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx'
    simpa only [Function.comp_apply, mul_assoc, mul_left_comm, mul_comm] using
      congrArg (fun z => ((x : ℂ) - 1) * (((x : ℂ) - 1) * z)) (heq x hx')
  apply hB₁
  simpa only [one_mul] using tendsto_nhds_unique hright hlim

end OMA.AbelianERH

/- Euler comparison with finitely many omitted rational primes. Their local factors never
vanish in the positive half-plane. -/

namespace OMA.AbelianERH

open NumberField Complex Set
open scoped NumberField

private theorem omit_euler_factors {ι : Type*} [DecidableEq ι] {F : ι → ℂ} {a : ℂ}
    (h : HasProd (fun p => (F p)⁻¹) a) (B : Finset ι) (hne : ∀ p ∈ B, F p ≠ 0) :
    HasProd (fun p => if p ∈ B then 1 else (F p)⁻¹) (a * ∏ p ∈ B, F p) := by
  let g (p : ι) := if p ∈ B then F p else 1
  have hg' : HasProd g (∏ p ∈ B, g p) :=
    hasProd_prod_of_ne_finset_one fun p hp => if_neg hp
  have hg : HasProd g (∏ p ∈ B, F p) := by
    rwa [Finset.prod_congr rfl (fun p hp => (show g p = F p from if_pos hp))] at hg'
  apply (h.mul hg).congr_fun
  intro p
  by_cases hp : p ∈ B <;> simp [hp, g, hne]

private noncomputable def quadraticEulerFactor {q : ℕ} (χ : DirichletCharacter ℂ q)
    (p : Nat.Primes) (s : ℂ) : ℂ :=
  (1 - (p.val : ℂ) ^ (-s)) * (1 - χ p.val * (p.val : ℂ) ^ (-s))

private theorem quadraticEulerFactor_differentiable {q : ℕ} (χ : DirichletCharacter ℂ q)
    (p : Nat.Primes) : Differentiable ℂ (quadraticEulerFactor χ p) := by
  let : NeZero (p.val : ℂ) := ⟨Nat.cast_ne_zero.mpr p.property.ne_zero⟩
  unfold quadraticEulerFactor
  fun_prop

private theorem quadraticEulerFactor_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (p : Nat.Primes) {s : ℂ} (hpos : 0 < s.re) : quadraticEulerFactor χ p s ≠ 0 := by
  apply mul_ne_zero _ (changeLevelFactor_ne_zero χ p.property hpos)
  have h := changeLevelFactor_ne_zero (1 : DirichletCharacter ℂ 1) p.property hpos
  simpa [Subsingleton.elim (p.val : ZMod 1) 1] using h

/-- Removing the finitely many unmatched local factors makes the Euler products agree on
the half-plane of convergence. -/
theorem quadratic_product_halfPlane_away_from_finite {K : Type*} [Field K] [NumberField K]
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset Nat.Primes)
    (hgood : ∀ p ∉ B, ∀ w : ℂ, 1 < w.re → localPolynomial K p w =
      (1 - (p.val : ℂ) ^ (-w)) * (1 - χ p.val * (p.val : ℂ) ^ (-w)))
    {w : ℂ} (hw : 1 < w.re) :
    dedekindZeta K w * (∏ p ∈ B, localPolynomial K p w) =
      (riemannZeta w * χ.LFunction w) * ∏ p ∈ B,
        ((1 - (p.val : ℂ) ^ (-w)) * (1 - χ p.val * (p.val : ℂ) ^ (-w))) := by
  classical
  have hpos := lt_trans zero_lt_one hw
  have hchar : HasProd (fun p => (quadraticEulerFactor χ p w)⁻¹)
      (riemannZeta w * χ.LFunction w) := by
    rw [χ.LFunction_eq_LSeries hw]
    apply ((riemannZeta_eulerProduct_hasProd hw).mul (χ.LSeries_eulerProduct_hasProd hw)).congr_fun
    intro p
    simp [quadraticEulerFactor, mul_comm]
  apply (omit_euler_factors (dedekindZeta_hasProd_rationalPrimes K hw) B
    (fun p _ => localPolynomial_ne_zero K p hpos)).unique
  apply (omit_euler_factors hchar B (fun p _ => quadraticEulerFactor_ne_zero χ p hpos)).congr_fun
  intro p
  by_cases hp : p ∈ B
  · simp [hp]
  · simp [hp, hgood p hp w hw, quadraticEulerFactor]

theorem quadratic_product_away_from_finite {K : Type*} [Field K] [NumberField K]
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset Nat.Primes)
    (hgood : ∀ p ∉ B, ∀ w : ℂ, 1 < w.re → localPolynomial K p w =
      (1 - (p.val : ℂ) ^ (-w)) * (1 - χ p.val * (p.val : ℂ) ^ (-w)))
    {Z : ℂ → ℂ} (hZ : ERH.IsDedekindZeta K Z) {s : ℂ} (hs : s ≠ 1) :
    Z s * (∏ p ∈ B, localPolynomial K p s) =
      (riemannZeta s * χ.LFunction s) * ∏ p ∈ B,
        ((1 - (p.val : ℂ) ^ (-s)) * (1 - χ p.val * (p.val : ℂ) ^ (-s))) := by
  classical
  apply eqOffOne_of_halfPlane (Z := fun w => Z w * ∏ p ∈ B, localPolynomial K p w)
    (W := fun w => (riemannZeta w * χ.LFunction w) * ∏ p ∈ B, quadraticEulerFactor χ p w) _ _ _ hs
  · exact hZ.1.mul (DifferentiableOn.fun_finsetProd fun p _ =>
      (localPolynomial_differentiable K p).differentiableOn)
  · exact (analyticOn_riemannZeta.differentiableOn.mul (fun w hw =>
      (χ.differentiableAt_LFunction w (Or.inl hw)).differentiableWithinAt)).mul
        (DifferentiableOn.fun_finsetProd fun p _ => (quadraticEulerFactor_differentiable χ p).differentiableOn)
  · intro w hw
    rw [hZ.2 w hw]
    exact quadratic_product_halfPlane_away_from_finite χ B hgood hw

theorem quadratic_zero_iff_of_good_primes {K : Type*} [Field K] [NumberField K]
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (B : Finset Nat.Primes)
    (hgood : ∀ p ∉ B, ∀ w : ℂ, 1 < w.re → localPolynomial K p w =
      (1 - (p.val : ℂ) ^ (-w)) * (1 - χ p.val * (p.val : ℂ) ^ (-w)))
    {Z : ℂ → ℂ} (hZ : ERH.IsDedekindZeta K Z) {s : ℂ} (hpos : 0 < s.re) (hs : s ≠ 1) :
    Z s = 0 ↔ riemannZeta s = 0 ∨ χ.LFunction s = 0 := by
  have heq := quadratic_product_away_from_finite χ B hgood hZ hs
  have hleft : (∏ p ∈ B, localPolynomial K p s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ => localPolynomial_ne_zero K p hpos
  have hright : (∏ p ∈ B, quadraticEulerFactor χ p s) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun p _ => quadraticEulerFactor_ne_zero χ p hpos
  calc
    Z s = 0 ↔ Z s * (∏ p ∈ B, localPolynomial K p s) = 0 :=
      (mul_eq_zero.trans (or_iff_left hleft)).symm
    _ ↔ (riemannZeta s * χ.LFunction s) * (∏ p ∈ B, quadraticEulerFactor χ p s) = 0 := by
      rw [heq]
      rfl
    _ ↔ _ := (mul_eq_zero.trans (or_iff_left hright)).trans mul_eq_zero

private theorem primitive_ne_one_of_good_factors {K : Type*} [Field K] [NumberField K]
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (B : Finset Nat.Primes)
    (hgood : ∀ p ∉ B, ∀ s : ℂ, localPolynomial K p s =
      (1 - (p.val : ℂ) ^ (-s)) * (1 - χ p.val * (p.val : ℂ) ^ (-s))) : χ ≠ 1 := by
  rintro rfl
  have hq : q = 1 := ((DirichletCharacter.isPrimitive_def _).mp hχ).symm.trans
    (DirichletCharacter.conductor_one (R := ℂ) (n := q))
  subst q
  let χ : DirichletCharacter ℂ 1 := 1
  apply dedekind_no_double_riemann_pole K
    (A := fun s => ∏ p ∈ B, localPolynomial K p s)
    (B := fun s => ∏ p ∈ B, quadraticEulerFactor χ p s)
  · exact (Differentiable.fun_finsetProd fun p _ => localPolynomial_differentiable K p).continuous.continuousAt
  · exact (Differentiable.fun_finsetProd fun p _ => quadraticEulerFactor_differentiable χ p).continuous.continuousAt
  · exact Finset.prod_ne_zero_iff.mpr fun p _ => quadraticEulerFactor_ne_zero χ p (by norm_num)
  · intro s hs
    simpa only [DirichletCharacter.LFunction_modOne_eq, quadraticEulerFactor, χ] using
      (quadratic_product_halfPlane_away_from_finite χ B (fun p hp w _ => hgood p hp w) hs)

/-- The primitive quadratic character agrees with the splitting law at every prime outside a
finite set. The construction uses a square-root generator and its finite order index. -/
theorem quadratic_good_local_factors (K : Type*) [Field K] [NumberField K]
    (hd : Module.finrank ℚ K = 2) :
    ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q), χ.IsPrimitive ∧ χ.IsQuadratic ∧ χ ≠ 1 ∧
      ∃ B : Finset Nat.Primes, ∀ p ∉ B, ∀ s : ℂ, localPolynomial K p s =
        (1 - (p.val : ℂ) ^ (-s)) * (1 - χ p.val * (p.val : ℂ) ^ (-s)) := by
  classical
  obtain ⟨D, θ, hD, hθ, hindex⟩ := quadratic_generator K hd
  let m := 4 * D.natAbs
  let : NeZero m := ⟨Nat.mul_ne_zero (by decide) (Int.natAbs_ne_zero.mpr hD)⟩
  let χ : DirichletCharacter ℂ m := discriminantChar D hD
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  let B := excludedPrimes (m * RingOfIntegers.exponent θ)
  have hgood (p : Nat.Primes) (hp : p ∉ B) (w : ℂ) : localPolynomial K p w =
      (1 - (p.val : ℂ) ^ (-w)) * (1 - χ.primitiveCharacter p.val * (p.val : ℂ) ^ (-w)) := by
    have hp' : ¬ p.val ∣ m * RingOfIntegers.exponent θ := by
      intro h
      apply hp
      exact Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨p.property, h,
        Nat.mul_ne_zero (NeZero.ne m) hindex⟩)
    have hm : ¬ p.val ∣ m := fun h => hp' (dvd_mul_of_dvd_left h _)
    have hcop := p.property.coprime_iff_not_dvd.mpr hm
    have hval : χ.primitiveCharacter p.val = χ p.val := by
      simpa using χ.primitiveCharacter_apply_of_isCoprime (Nat.isCoprime_iff_coprime.mpr hcop)
    rw [hval]
    exact squareRoot_localPolynomial hD θ hθ p hm (fun h => hp' (dvd_mul_of_dvd_right h _)) w
  exact ⟨χ.conductor, inferInstance, χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive,
    primitiveCharacter_isQuadratic χ (discriminantChar_isQuadratic D hD),
    primitive_ne_one_of_good_factors χ.primitiveCharacter χ.primitiveCharacter_isPrimitive B hgood,
    B, hgood⟩

/-- Every quadratic field factors as a zeta-times-primitive-L product after deleting finitely
many Euler factors. Both deleted products are explicitly displayed. -/
theorem quadratic_factorization_up_to_finite (K : Type*) [Field K] [NumberField K]
    (hd : Module.finrank ℚ K = 2) :
    ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q), χ.IsPrimitive ∧ χ.IsQuadratic ∧ χ ≠ 1 ∧
      ∃ B : Finset Nat.Primes, ∀ s : ℂ, 1 < s.re →
        dedekindZeta K s * (∏ p ∈ B, localPolynomial K p s) =
          (riemannZeta s * χ.LFunction s) * ∏ p ∈ B,
            ((1 - (p.val : ℂ) ^ (-s)) * (1 - χ p.val * (p.val : ℂ) ^ (-s))) := by
  obtain ⟨q, hq, χ, hχ, hquad, hnon, B, hgood⟩ := quadratic_good_local_factors K hd
  exact ⟨q, hq, χ, hχ, hquad, hnon, B, fun _ hs =>
    quadratic_product_halfPlane_away_from_finite χ B (fun p hp s _ => hgood p hp s) hs⟩

/-- Every quadratic number field has one primitive quadratic character whose zeros, together
with the Riemann zeros, are precisely the Dedekind zeros in the positive half-plane off 1. -/
theorem quadratic_primitive_zero_criterion (K : Type*) [Field K] [NumberField K]
    (hd : Module.finrank ℚ K = 2) :
    ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q), χ.IsPrimitive ∧ χ.IsQuadratic ∧ χ ≠ 1 ∧
      ∀ Z : ℂ → ℂ, ERH.IsDedekindZeta K Z → ∀ s : ℂ, 0 < s.re → s ≠ 1 →
        (Z s = 0 ↔ riemannZeta s = 0 ∨ χ.LFunction s = 0) := by
  obtain ⟨q, hq, χ, hχ, hquad, hnon, B, hgood⟩ := quadratic_good_local_factors K hd
  exact ⟨q, hq, χ, hχ, hquad, hnon, fun _ hZ _ hpos hs =>
    quadratic_zero_iff_of_good_primes χ B (fun p hp s _ => hgood p hp s) hZ hpos hs⟩

theorem quadratic_erh (K : Type*) [Field K] [NumberField K]
    (hd : Module.finrank ℚ K = 2) (h : PrimitiveStripGRH) : ERH.ExtendedRiemannHypothesis K := by
  obtain ⟨q, hq, χ, hχ, _, _, hcrit⟩ := quadratic_primitive_zero_criterion K hd
  intro Z hZ s hpos hlt hz
  rcases (hcrit Z hZ s hpos (fun e => by simp [e] at hlt)).mp hz with hζ | hL
  · exact h.riemann hpos hlt hζ
  · exact h q χ hχ s hpos hlt hL

/-- Clearing entire factors which are nonzero in the positive half-plane constructs a
holomorphic continuation there, even without a previously supplied Dedekind continuation. -/
theorem rightHalfPlane_continuation_of_cleared (K : Type*) [Field K] [NumberField K]
    (F P Q : ℂ → ℂ) (hF : DifferentiableOn ℂ F ({1}ᶜ : Set ℂ))
    (hP : Differentiable ℂ P) (hQ : Differentiable ℂ Q)
    (hP₀ : ∀ s : ℂ, 0 < s.re → P s ≠ 0) (hQ₀ : ∀ s : ℂ, 0 < s.re → Q s ≠ 0)
    (he : ∀ s : ℂ, 1 < s.re → dedekindZeta K s * P s = F s * Q s) :
    ∃ W : ℂ → ℂ, DifferentiableOn ℂ W {s | 0 < s.re ∧ s ≠ 1} ∧
      (∀ s : ℂ, 1 < s.re → W s = dedekindZeta K s) ∧
      ∀ s : ℂ, 0 < s.re → s ≠ 1 → (W s = 0 ↔ F s = 0) := by
  refine ⟨fun s => F s * Q s / P s, ?_, ?_, ?_⟩
  · exact ((hF.mono fun s hs => hs.2).mul hQ.differentiableOn).div hP.differentiableOn
      (fun s hs => hP₀ s hs.1)
  · intro s hs
    exact (div_eq_iff (hP₀ s (lt_trans zero_lt_one hs))).mpr (he s hs).symm
  · intro s hs _
    simp [div_eq_zero_iff, hP₀ s hs, hQ₀ s hs]

/-- Every quadratic field has a Dedekind continuation throughout the positive half-plane off
the pole. Its zeros there are precisely the Riemann zeros and those of the constructed
nontrivial primitive quadratic character. -/
theorem quadratic_rightHalfPlane_continuation (K : Type*) [Field K] [NumberField K]
    (hd : Module.finrank ℚ K = 2) :
    ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q), χ.IsPrimitive ∧ χ.IsQuadratic ∧ χ ≠ 1 ∧
      ∃ W : ℂ → ℂ, DifferentiableOn ℂ W {s | 0 < s.re ∧ s ≠ 1} ∧
        (∀ s : ℂ, 1 < s.re → W s = dedekindZeta K s) ∧
        ∀ s : ℂ, 0 < s.re → s ≠ 1 → (W s = 0 ↔ riemannZeta s = 0 ∨ χ.LFunction s = 0) := by
  obtain ⟨q, hq, χ, hχ, hquad, hnon, B, hgood⟩ := quadratic_good_local_factors K hd
  have hF := analyticOn_riemannZeta.differentiableOn.mul (fun w (hw : w ∈ ({1}ᶜ : Set ℂ)) =>
    (χ.differentiableAt_LFunction w (Or.inl hw)).differentiableWithinAt)
  obtain ⟨W, hW, he, hz⟩ := rightHalfPlane_continuation_of_cleared K
    (fun s => riemannZeta s * χ.LFunction s)
    (fun s => ∏ p ∈ B, localPolynomial K p s) (fun s => ∏ p ∈ B, quadraticEulerFactor χ p s) hF
    (Differentiable.fun_finsetProd fun p _ => localPolynomial_differentiable K p)
    (Differentiable.fun_finsetProd fun p _ => quadraticEulerFactor_differentiable χ p)
    (fun _ h => Finset.prod_ne_zero_iff.mpr fun p _ => localPolynomial_ne_zero K p h)
    (fun _ h => Finset.prod_ne_zero_iff.mpr fun p _ => quadraticEulerFactor_ne_zero χ p h)
    (fun _ hs => quadratic_product_halfPlane_away_from_finite χ B (fun p hp s _ => hgood p hp s) hs)
  exact ⟨q, hq, χ, hχ, hquad, hnon, W, hW, he, fun s hp hs => (hz s hp hs).trans mul_eq_zero⟩

/-- Every full cyclotomic field has a continuation throughout the positive half-plane off the
pole with exactly the zeros of the product of the Dirichlet L-functions of its level. -/
theorem cyclotomic_rightHalfPlane_continuation (n : ℕ) [NeZero n] (K : Type*) [Field K]
    [NumberField K] [IsCyclotomicExtension {n} ℚ K] :
    ∃ W : ℂ → ℂ, DifferentiableOn ℂ W {s | 0 < s.re ∧ s ≠ 1} ∧
      (∀ s : ℂ, 1 < s.re → W s = dedekindZeta K s) ∧
      ∀ s : ℂ, 0 < s.re → s ≠ 1 → (W s = 0 ↔ (∏ χ : DirichletCharacter ℂ n, χ.LFunction s) = 0) := by
  apply rightHalfPlane_continuation_of_cleared K _ (ramifiedFactors n K) (fun _ => 1)
  · exact DifferentiableOn.fun_finsetProd fun χ _ w hw =>
      (χ.differentiableAt_LFunction w (Or.inl hw)).differentiableWithinAt
  · exact ramifiedFactors_differentiable n K
  · exact differentiable_const _
  · exact fun _ hs => ramifiedFactors_ne_zero n K hs
  · exact fun _ _ => one_ne_zero
  · intro s hs
    simpa only [mul_one] using (cyclotomic_LProduct n K hs).symm

end OMA.AbelianERH

/- Transfer to a primitive Dirichlet zero for the union of the field families. -/

namespace OMA.AbelianERH

open NumberField

theorem degree_one_continuation (K : Type*) [Field K] [NumberField K]
    (hd : Module.finrank ℚ K = 1) : ERH.IsDedekindZeta K riemannZeta :=
  ⟨analyticOn_riemannZeta.differentiableOn, fun _ hs => (degree_one_factorization K hd hs).symm⟩

/-- Each zero in the positive half-plane away from the pole for a number field of degree at
most two or a full cyclotomic field is a zero of a primitive Dirichlet L-function. -/
theorem covered_field_zero_transfer (K : Type*) [Field K] [NumberField K]
    (hK : Module.finrank ℚ K ≤ 2 ∨ ∃ n : ℕ, 0 < n ∧ IsCyclotomicExtension {n} ℚ K)
    (Z : ℂ → ℂ) (hZ : ERH.IsDedekindZeta K Z) (s : ℂ)
    (hpos : 0 < s.re) (hs : s ≠ 1) (hz : Z s = 0) :
    ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q), χ.IsPrimitive ∧ χ.LFunction s = 0 := by
  have hr (h : riemannZeta s = 0) :
      ∃ (q : ℕ) (_ : NeZero q) (χ : DirichletCharacter ℂ q), χ.IsPrimitive ∧ χ.LFunction s = 0 :=
    ⟨1, inferInstance, 1, DirichletCharacter.isPrimitive_one_level_one, by simpa using h⟩
  rcases hK with hdeg | ⟨n, hn, hcyc⟩
  · have hposdeg : 0 < Module.finrank ℚ K := Module.finrank_pos
    rcases (show Module.finrank ℚ K = 1 ∨ Module.finrank ℚ K = 2 by omega) with hd | hd
    · exact hr ((continuation_unique hZ (degree_one_continuation K hd) hs).symm.trans hz)
    · obtain ⟨q, hq, χ, hχ, _, _, hcrit⟩ := quadratic_primitive_zero_criterion K hd
      rcases (hcrit Z hZ s hpos hs).mp hz with h | h
      · exact hr h
      · exact ⟨q, hq, χ, hχ, h⟩
  · let : NeZero n := ⟨hn.ne'⟩
    obtain ⟨χ, hχ⟩ := (cyclotomic_zero_iff n K hZ hpos hs).mp hz
    exact ⟨χ.conductor, ⟨χ.conductor_ne_zero⟩, χ.primitiveCharacter, χ.primitiveCharacter_isPrimitive, hχ⟩

end OMA.AbelianERH

theorem OMA.solution : OMA.R_ERH_extended_riemann_hypothesis_R2.H1 := by
  intro K _ _ hK Z hZ s hpos hs hz
  exact OMA.AbelianERH.covered_field_zero_transfer K hK Z hZ s hpos hs hz
