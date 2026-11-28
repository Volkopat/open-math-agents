import OMAReductions.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1

-- Step ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.parts.i.R1.H4: hypothesis H4 of reduction ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.parts.i.R1
-- Credit: @senamakel
-- Positivity of Artin's density for a not a square, a not -1. Write a = a0 c^2 with a0 squarefree.
-- [K_k : Q] m(k) = k phi(k) for squarefree k, where m(k) collects the primes q | k with a a q-th
-- power (q = 2: sqrt a in Q(zeta_k), which by the conductor of Q(sqrt a0) means a0 = 1 mod 4 and
-- |a0| divides k). The series then factors as an Euler product times a correction, both positive.


namespace Artin
open Polynomial
set_option synthInstance.maxHeartbeats 400000 in
noncomputable def kummerDegree (a : ℤ) (k : ℕ) : ℕ :=
  Module.finrank ℚ (X ^ k - C (a : ℚ)).SplittingField
end Artin

section
namespace Artin.Kummer
open Polynomial IntermediateField
set_option synthInstance.maxHeartbeats 400000 in
abbrev KField (a : ℤ) (k : ℕ) := (X ^ k - C (a : ℚ)).SplittingField
set_option synthInstance.maxHeartbeats 400000 in
instance kfIsSplittingField (a : ℤ) (k : ℕ) : IsSplittingField ℚ (KField a k) (X ^ k - C (a : ℚ)) :=
  Polynomial.IsSplittingField.splittingField _
variable {a : ℤ} {k : ℕ}
set_option synthInstance.maxHeartbeats 400000 in
lemma poly_ne_zero (hk : k ≠ 0) : (X ^ k - C (a : ℚ)) ≠ 0 :=
  Polynomial.X_pow_sub_C_ne_zero (Nat.pos_of_ne_zero hk) _
set_option synthInstance.maxHeartbeats 400000 in
lemma mem_rootSet_iff (hk : k ≠ 0) {x : KField a k} :
    x ∈ (X ^ k - C (a : ℚ)).rootSet (KField a k) ↔ x ^ k = a := by
  rw [mem_rootSet_of_ne (poly_ne_zero hk)]
  simp [sub_eq_zero]
set_option synthInstance.maxHeartbeats 400000 in
lemma card_rootSet (ha : a ≠ 0) (hk : k ≠ 0) :
    Fintype.card ((X ^ k - C (a : ℚ)).rootSet (KField a k)) = k := by
  rw [card_rootSet_eq_natDegree (separable_X_pow_sub_C _ (by exact_mod_cast hk)
    (by exact_mod_cast ha)) (IsSplittingField.splits (KField a k) _), natDegree_X_pow_sub_C]
set_option synthInstance.maxHeartbeats 400000 in
lemma exists_root (ha : a ≠ 0) (hk : k ≠ 0) : ∃ α : KField a k, α ^ k = a := by
  have : Nonempty ((X ^ k - C (a : ℚ)).rootSet (KField a k)) := by
    rw [← Fintype.card_pos_iff, card_rootSet ha hk]; exact Nat.pos_of_ne_zero hk
  obtain ⟨⟨α, hα⟩⟩ := this
  exact ⟨α, (mem_rootSet_iff hk).1 hα⟩
set_option synthInstance.maxHeartbeats 400000 in
lemma exists_isPrimitiveRoot (ha : a ≠ 0) (hk : k ≠ 0) :
    ∃ ζ : KField a k, IsPrimitiveRoot ζ k := by
  have : NeZero k := ⟨hk⟩
  obtain ⟨α, hα⟩ := exists_root ha hk
  have hα0 : α ≠ 0 := by
    rintro rfl; rw [zero_pow hk] at hα; exact ha (by exact_mod_cast hα.symm)
  let f : (X ^ k - C (a : ℚ)).rootSet (KField a k) → rootsOfUnity k (KField a k) :=
    fun r => ⟨Units.mk0 (r.1 / α) (div_ne_zero (by
      intro h0; have := (mem_rootSet_iff hk).1 r.2; rw [h0, zero_pow hk] at this
      exact ha (by exact_mod_cast this.symm)) hα0), by
      rw [mem_rootsOfUnity']
      simp [div_pow, (mem_rootSet_iff hk).1 r.2, hα, ha]⟩
  have hf : Function.Injective f := by
    intro r s hrs
    have := congrArg (fun u : rootsOfUnity k (KField a k) => ((u : (KField a k)ˣ) : KField a k)) hrs
    simp only [f, Units.val_mk0] at this
    exact Subtype.ext ((div_left_inj' hα0).1 this)
  have hcard : k ≤ Nat.card (rootsOfUnity k (KField a k)) := by
    have := Nat.card_le_card_of_injective f hf
    rwa [Nat.card_eq_fintype_card, card_rootSet ha hk] at this
  exact (HasEnoughRootsOfUnity.of_card_le hcard).prim
section Tower
variable {ζ α : KField a k}
set_option synthInstance.maxHeartbeats 400000 in
lemma finrank_adjoin_zeta (hk : k ≠ 0) (hζ : IsPrimitiveRoot ζ k) :
    Module.finrank ℚ ℚ⟮ζ⟯ = k.totient := by
  have : NeZero k := ⟨hk⟩
  have : IsCyclotomicExtension {k} ℚ ℚ⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  exact IsCyclotomicExtension.finrank ℚ⟮ζ⟯
    (Polynomial.cyclotomic.irreducible_rat (Nat.pos_of_ne_zero hk))
set_option synthInstance.maxHeartbeats 400000 in
lemma div_mem_adjoin_zeta (hk : k ≠ 0) (hζ : IsPrimitiveRoot ζ k) {x y : KField a k}
    (hy : y ≠ 0) (h : x ^ k = y ^ k) : x / y ∈ ℚ⟮ζ⟯ := by
  have : NeZero k := ⟨hk⟩
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one (ξ := x / y) (by
    rw [div_pow, h, div_self (pow_ne_zero _ hy)])
  rw [← hi]
  exact pow_mem (mem_adjoin_simple_self ℚ ζ) _
set_option synthInstance.maxHeartbeats 400000 in
lemma adjoin_root_eq_top (ha : a ≠ 0) (hk : k ≠ 0) (hζ : IsPrimitiveRoot ζ k)
    (hα : α ^ k = a) : ℚ⟮ζ⟯⟮α⟯ = ⊤ := by
  have hα0 : α ≠ 0 := by
    rintro rfl; rw [zero_pow hk] at hα; exact ha (by exact_mod_cast hα.symm)
  rw [← restrictScalars_eq_top_iff (K := ℚ), eq_top_iff]
  have hsplit := (isSplittingField_iff_intermediateField (K := ℚ) (L := KField a k)
    (p := X ^ k - C (a : ℚ))).1 inferInstance
  rw [← hsplit.2, adjoin_le_iff]
  intro r hr
  rw [mem_rootSet_iff hk] at hr
  have hmem : r / α ∈ ℚ⟮ζ⟯ := div_mem_adjoin_zeta hk hζ hα0 (by rw [hr, hα])
  have : r = (r / α) * α := by field_simp
  rw [this]
  refine mul_mem ?_ (mem_adjoin_simple_self _ α)
  exact IntermediateField.algebraMap_mem (ℚ⟮ζ⟯⟮α⟯) (⟨r / α, hmem⟩ : ℚ⟮ζ⟯)
set_option synthInstance.maxHeartbeats 400000 in
lemma isIntegral_root : IsIntegral ℚ⟮ζ⟯ α := Algebra.IsIntegral.isIntegral α
set_option synthInstance.maxHeartbeats 400000 in
lemma kummerDegree_eq_totient_mul (ha : a ≠ 0) (hk : k ≠ 0) (hζ : IsPrimitiveRoot ζ k)
    (hα : α ^ k = a) :
    kummerDegree a k = k.totient * (minpoly ℚ⟮ζ⟯ α).natDegree := by
  unfold kummerDegree
  rw [← Module.finrank_mul_finrank ℚ ℚ⟮ζ⟯ (KField a k), finrank_adjoin_zeta hk hζ,
    ← finrank_top', ← adjoin_root_eq_top ha hk hζ hα, adjoin.finrank isIntegral_root]
set_option synthInstance.maxHeartbeats 400000 in
lemma natDegree_minpoly_le {e : ℕ} (he : 0 < e) (h : α ^ e ∈ ℚ⟮ζ⟯) :
    (minpoly ℚ⟮ζ⟯ α).natDegree ≤ e := by
  have hne : (X ^ e - C (⟨α ^ e, h⟩ : ℚ⟮ζ⟯)) ≠ 0 := X_pow_sub_C_ne_zero he _
  have := minpoly.degree_le_of_ne_zero ℚ⟮ζ⟯ α hne (by simp)
  rw [degree_X_pow_sub_C he, degree_eq_natDegree (minpoly.ne_zero isIntegral_root)] at this
  exact_mod_cast this
set_option synthInstance.maxHeartbeats 400000 in
lemma pow_natDegree_minpoly_mem (ha : a ≠ 0) (hk : k ≠ 0) (hζ : IsPrimitiveRoot ζ k)
    (hα : α ^ k = a) : α ^ (minpoly ℚ⟮ζ⟯ α).natDegree ∈ ℚ⟮ζ⟯ := by
  set F := ℚ⟮ζ⟯
  set f := minpoly F α with hf
  set d := f.natDegree with hd
  have hα0 : α ≠ 0 := by
    rintro rfl; rw [zero_pow hk] at hα; exact ha (by exact_mod_cast hα.symm)
  have hmon : (f.map (algebraMap F (KField a k))).Monic := (minpoly.monic isIntegral_root).map _
  have hdvd : f ∣ (X ^ k - C (a : ℚ)).map (algebraMap ℚ F) :=
    minpoly.dvd F α (by simp [hα])
  have hsplitP : ((X ^ k - C (a : ℚ)).map (algebraMap ℚ F)).map (algebraMap F (KField a k))
      |>.Splits := by
    rw [Polynomial.map_map, ← IsScalarTower.algebraMap_eq]; exact SplittingField.splits _
  have hsplit : (f.map (algebraMap F (KField a k))).Splits :=
    hsplitP.of_dvd (Polynomial.map_ne_zero (Polynomial.map_ne_zero (poly_ne_zero hk)))
      (Polynomial.map_dvd _ hdvd)
  set P := (f.map (algebraMap F (KField a k))).roots.prod with hP
  have hroot : ∀ r ∈ (f.map (algebraMap F (KField a k))).roots, r ^ k = a := by
    intro r hr
    have h1 : (f.map (algebraMap F (KField a k))).IsRoot r := (mem_roots hmon.ne_zero).1 hr
    have h2 : ((X ^ k - C (a : ℚ)).map (algebraMap ℚ F)).map (algebraMap F (KField a k))
        |>.IsRoot r := by
      obtain ⟨g, hg⟩ := hdvd
      rw [hg, Polynomial.map_mul]
      exact root_mul_right_of_isRoot _ h1
    simpa [sub_eq_zero] using h2
  have hcard : Multiset.card (f.map (algebraMap F (KField a k))).roots = d := by
    rw [← hsplit.natDegree_eq_card_roots, natDegree_map]
  have hPk : P ^ k = (α ^ d) ^ k := by
    have hP' : P ^ k = ((f.map (algebraMap F (KField a k))).roots.map (fun r => r ^ k)).prod := by
      rw [Multiset.prod_map_pow, Multiset.map_id']
    rw [hP', Multiset.map_congr rfl hroot, Multiset.map_const',
      Multiset.prod_replicate, hcard, ← pow_mul, mul_comm, pow_mul, hα]
  have hPmem : P ∈ F := by
    have h0 := hsplit.coeff_zero_eq_prod_roots_of_monic hmon
    rw [← hP, natDegree_map, coeff_map] at h0
    have : P = algebraMap F (KField a k) ((-1) ^ d * f.coeff 0) := by
      rw [map_mul, h0, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg,
        one_pow, one_mul]
    rw [this]; exact ((-1) ^ d * f.coeff 0 : F).2
  have hq : P / α ^ d ∈ F := div_mem_adjoin_zeta hk hζ (pow_ne_zero _ hα0) hPk
  have hP0 : P / α ^ d ≠ 0 := by
    intro h0
    rw [div_eq_zero_iff] at h0
    rcases h0 with h0 | h0
    · rw [h0, zero_pow hk] at hPk
      exact pow_ne_zero _ (pow_ne_zero _ hα0) hPk.symm
    · exact pow_ne_zero _ hα0 h0
  have : α ^ d = P / (P / α ^ d) := by
    have hPne : P ≠ 0 := left_ne_zero_of_mul (by rwa [div_eq_mul_inv] at hP0)
    rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ hPne]
  rw [this]
  exact div_mem hPmem hq
set_option synthInstance.maxHeartbeats 400000 in
lemma natDegree_minpoly_dvd (ha : a ≠ 0) (hk : k ≠ 0) (hζ : IsPrimitiveRoot ζ k)
    (hα : α ^ k = a) : (minpoly ℚ⟮ζ⟯ α).natDegree ∣ k := by
  set d := (minpoly ℚ⟮ζ⟯ α).natDegree with hd
  have hd0 : 0 < d := minpoly.natDegree_pos isIntegral_root
  have hα0 : α ≠ 0 := by
    rintro rfl; rw [zero_pow hk] at hα; exact ha (by exact_mod_cast hα.symm)
  set g := Nat.gcd d k with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hd0
  have hmem : α ^ g ∈ ℚ⟮ζ⟯ := by
    have h1 : α ^ (g : ℤ) = (α ^ d) ^ (Nat.gcdA d k) * (α ^ k) ^ (Nat.gcdB d k) := by
      rw [hg, Nat.gcd_eq_gcd_ab, zpow_add₀ hα0, zpow_mul, zpow_mul]; simp
    rw [← zpow_natCast, h1]
    refine mul_mem (zpow_mem (pow_natDegree_minpoly_mem ha hk hζ hα) _) (zpow_mem ?_ _)
    rw [hα]; exact intCast_mem _ a
  have hgd : g = d := le_antisymm (Nat.gcd_le_left _ hd0) (natDegree_minpoly_le hg0 hmem)
  rw [← hgd]; exact Nat.gcd_dvd_right _ _
end Tower
set_option synthInstance.maxHeartbeats 400000 in
lemma exists_int_pow_of_rat_pow {q : ℕ} (hq : q ≠ 0) {b : ℚ} (h : b ^ q = (a : ℚ)) :
    ∃ c : ℤ, c ^ q = a := by
  have hden : b.den = 1 := by
    have := congrArg Rat.den h
    rw [Rat.den_pow, Rat.den_intCast] at this
    exact (Nat.pow_eq_one.1 this).resolve_right hq
  refine ⟨b.num, ?_⟩
  have : (b.num : ℚ) = b := Rat.coe_int_num_of_den_eq_one hden
  exact_mod_cast (this ▸ h)
set_option synthInstance.maxHeartbeats 400000 in
theorem exists_int_pow_of_isAbelianGalois {E : Type*} [Field E] [Algebra ℚ E]
    [IsAbelianGalois ℚ E] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {β : E}
    (hβ : β ^ q = (a : E)) : ∃ c : ℤ, c ^ q = a := by
  by_contra hno
  push Not at hno
  have ha0 : a ≠ 0 := by rintro rfl; exact hno 0 (zero_pow hq.ne_zero)
  have hrat : ∀ b : ℚ, b ^ q ≠ (a : ℚ) := fun b hb => by
    obtain ⟨c, hc⟩ := exists_int_pow_of_rat_pow hq.ne_zero hb
    exact hno c hc
  have hirr := X_pow_sub_C_irreducible_of_prime hq hrat
  have hmon : (X ^ q - C (a : ℚ)).Monic := monic_X_pow_sub_C _ hq.ne_zero
  have hβ' : aeval β (X ^ q - C (a : ℚ)) = 0 := by simp [hβ]
  have hint : IsIntegral ℚ β := ⟨_, hmon, by rwa [← aeval_def]⟩
  have hmin : minpoly ℚ β = X ^ q - C (a : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hβ' hmon).symm
  have hfin : Module.finrank ℚ ℚ⟮β⟯ = q := by
    rw [adjoin.finrank hint, hmin, natDegree_X_pow_sub_C]
  let x : ℚ⟮β⟯ := ⟨β, mem_adjoin_simple_self ℚ β⟩
  have hab : IsAbelianGalois ℚ ℚ⟮β⟯ := IsAbelianGalois.tower_bot ℚ ℚ⟮β⟯ E
  have hsplit := hab.toIsGalois.to_normal.splits x
  have hminx : minpoly ℚ x = X ^ q - C (a : ℚ) := by
    refine (minpoly.eq_of_irreducible_of_monic hirr ?_ hmon).symm
    apply Subtype.ext
    simp [x, hβ]
  rw [hminx] at hsplit
  have hsep : (X ^ q - C (a : ℚ)).Separable :=
    separable_X_pow_sub_C _ (by exact_mod_cast hq.ne_zero) (by exact_mod_cast ha0)
  have hcard := card_rootSet_eq_natDegree hsep hsplit
  rw [natDegree_X_pow_sub_C] at hcard
  obtain ⟨⟨r₁, h₁⟩, ⟨r₂, h₂⟩, hne⟩ := Fintype.one_lt_card_iff.1 (hcard ▸ hq.one_lt)
  rw [mem_rootSet_of_ne hmon.ne_zero] at h₁ h₂
  simp only [map_sub, map_pow, aeval_X, aeval_C, sub_eq_zero] at h₁ h₂
  have hr₂ : r₂ ≠ 0 := by
    rintro rfl; rw [zero_pow hq.ne_zero] at h₂
    exact ha0 (by simpa using h₂.symm)
  have hξ : IsPrimitiveRoot (r₁ / r₂) q := by
    refine isPrimitiveRoot_of_mem_nthRootsFinset hq ?_ ?_
    · rw [mem_nthRootsFinset hq.pos, div_pow, h₁, h₂, div_self]
      rw [← h₂]; exact pow_ne_zero _ hr₂
    · intro h1
      exact hne (Subtype.ext ((div_eq_one_iff_eq hr₂).1 h1))
  have hdvd := minpoly.degree_dvd ((hξ.isIntegral hq.pos).tower_top (A := ℚ))
  rw [← cyclotomic_eq_minpoly_rat hξ hq.pos, natDegree_cyclotomic, Nat.totient_prime hq] at hdvd
  replace hdvd : q - 1 ∣ q := by
    convert hdvd using 1; rw [← hfin]; congr 1; exact Subsingleton.elim _ _
  have h1 : q - 1 ∣ 1 := by
    have : q = (q - 1) + 1 := (Nat.sub_add_cancel hq.one_lt.le).symm
    conv_rhs at hdvd => rw [this]
    exact (Nat.dvd_add_right (dvd_refl _)).1 hdvd
  have := Nat.dvd_one.1 h1
  omega
set_option synthInstance.maxHeartbeats 400000 in
lemma le_natAbs_of_pow_eq {q : ℕ} (c : ℤ) (h : c ^ q = a) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (ha2 : a ≠ -1) : q ≤ a.natAbs := by
  have hc0 : c.natAbs ≠ 0 := by
    intro h0; rw [Int.natAbs_eq_zero] at h0; subst h0
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · exact ha1 (by simpa using h.symm)
    · exact ha0 (by rw [← h, zero_pow hq.ne'])
  have hca : a.natAbs = c.natAbs ^ q := by rw [← h, Int.natAbs_pow]
  have hc1 : c.natAbs ≠ 1 := by
    intro h1
    rw [h1, one_pow] at hca
    rcases Int.natAbs_eq_iff.1 hca with h' | h'
    · exact ha1 (by simpa using h')
    · exact ha2 (by simpa using h')
  rw [hca]
  calc q ≤ 2 ^ q := (Nat.lt_two_pow_self).le
    _ ≤ c.natAbs ^ q := Nat.pow_le_pow_left (by omega) _
set_option synthInstance.maxHeartbeats 400000 in
lemma exists_structure (ha : a ≠ 0) (hk : k ≠ 0) :
    ∃ (ζ α : KField a k) (d : ℕ), IsPrimitiveRoot ζ k ∧ α ^ k = a ∧ d ∣ k ∧ 0 < d ∧
      kummerDegree a k = k.totient * d ∧ α ^ d ∈ ℚ⟮ζ⟯ ∧
      ∀ e, 0 < e → α ^ e ∈ ℚ⟮ζ⟯ → d ≤ e := by
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot ha hk
  obtain ⟨α, hα⟩ := exists_root ha hk
  exact ⟨ζ, α, _, hζ, hα, natDegree_minpoly_dvd ha hk hζ hα,
    minpoly.natDegree_pos isIntegral_root, kummerDegree_eq_totient_mul ha hk hζ hα,
    pow_natDegree_minpoly_mem ha hk hζ hα, fun e he h => natDegree_minpoly_le he h⟩
set_option synthInstance.maxHeartbeats 400000 in
lemma exists_int_pow_of_mem_adjoin_zeta (hk : k ≠ 0) {ζ : KField a k}
    (hζ : IsPrimitiveRoot ζ k) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {β : KField a k}
    (hβ : β ∈ ℚ⟮ζ⟯) (hβq : β ^ q = a) : ∃ c : ℤ, c ^ q = a := by
  have : NeZero k := ⟨hk⟩
  have : IsCyclotomicExtension {k} ℚ ℚ⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have := IsCyclotomicExtension.isAbelianGalois {k} ℚ ℚ⟮ζ⟯
  refine exists_int_pow_of_isAbelianGalois (E := ℚ⟮ζ⟯) hq hq2 (β := ⟨β, hβ⟩) ?_
  apply Subtype.ext
  simp [hβq]
set_option synthInstance.maxHeartbeats 400000 in
lemma exists_int_pow_of_prime_dvd (hk : k ≠ 0) {ζ α : KField a k} {d : ℕ}
    (hζ : IsPrimitiveRoot ζ k) (hα : α ^ k = a) (hdk : d ∣ k) (hmem : α ^ d ∈ ℚ⟮ζ⟯)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hqm : q ∣ k / d) : ∃ c : ℤ, c ^ q = a := by
  obtain ⟨m, hm⟩ := hdk
  have hd0 : d ≠ 0 := by rintro rfl; simp at hm; exact hk hm
  rw [hm, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hd0)] at hqm
  obtain ⟨j, rfl⟩ := hqm
  refine exists_int_pow_of_mem_adjoin_zeta hk hζ hq hq2 (β := (α ^ d) ^ j)
    (pow_mem hmem _) ?_
  rw [← pow_mul, ← pow_mul, ← hα]; congr 1; rw [hm]; ring
set_option synthInstance.maxHeartbeats 400000 in
lemma le_four_pow_of_squarefree {m N : ℕ} (hm : Squarefree m) (h : ∀ q, q.Prime → q ∣ m → q ≤ N) :
    m ≤ 4 ^ N := by
  have hm0 : m ≠ 0 := hm.ne_zero
  refine le_trans (Nat.le_of_dvd (primorial_pos N) ?_) (primorial_le_four_pow N)
  rw [← Nat.prod_primeFactors_of_squarefree hm, primorial]
  apply Finset.prod_dvd_prod_of_subset
  intro q hq
  have hq' := Nat.mem_primeFactors.1 hq
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le (h q hq'.1 hq'.2.1), hq'.1⟩
set_option synthInstance.maxHeartbeats 400000 in
theorem mul_totient_le_kummerDegree (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : a ≠ -1) {k : ℕ}
    (hk : Squarefree k) : k * k.totient ≤ 4 ^ a.natAbs * kummerDegree a k := by
  have hk0 : k ≠ 0 := hk.ne_zero
  obtain ⟨ζ, α, d, hζ, hα, hdk, hd0, hdeg, hmem, -⟩ := exists_structure ha0 hk0
  obtain ⟨m, hm⟩ := hdk
  have hmk : m = k / d := by rw [hm, Nat.mul_div_cancel_left _ hd0]
  have hmsq : Squarefree m := hk.squarefree_of_dvd ⟨d, by rw [hm, mul_comm]⟩
  have hmle : m ≤ 4 ^ a.natAbs := by
    refine le_four_pow_of_squarefree hmsq fun q hq hqm => ?_
    by_cases hq2 : q = 2
    · subst hq2
      by_contra hlt
      push Not at hlt
      have : a.natAbs ≤ 1 := by omega
      rcases Int.natAbs_eq a with h | h <;> interval_cases (a.natAbs) <;> simp_all
    · obtain ⟨c, hc⟩ := exists_int_pow_of_prime_dvd hk0 hζ hα ⟨m, hm⟩ hmem hq hq2
        (hmk ▸ hqm)
      exact le_natAbs_of_pow_eq c hc ha0 ha1 ha2
  rw [hdeg]
  calc k * k.totient = m * (k.totient * d) := by rw [hm]; ring
    _ ≤ 4 ^ a.natAbs * (k.totient * d) := Nat.mul_le_mul_right _ hmle
set_option synthInstance.maxHeartbeats 400000 in
def NotPerfectPower (a : ℤ) : Prop := ∀ (b : ℤ) (n : ℕ), 2 ≤ n → b ^ n ≠ a
set_option synthInstance.maxHeartbeats 400000 in
open Classical in
noncomputable def kummerEps (a : ℤ) (k : ℕ) : ℕ :=
  if 2 ∣ k ∧ ∃ β : CyclotomicField k ℚ, β ^ 2 = a then 2 else 1
set_option synthInstance.maxHeartbeats 400000 in
lemma kummerEps_of_odd (hk : ¬ 2 ∣ k) : kummerEps a k = 1 := by
  simp [kummerEps, hk]
set_option synthInstance.maxHeartbeats 400000 in
lemma NotPerfectPower.ne_zero (h : NotPerfectPower a) : a ≠ 0 := by
  rintro rfl; exact h 0 2 le_rfl (by simp)
set_option synthInstance.maxHeartbeats 400000 in
lemma exists_sq_iff (hk : k ≠ 0) {ζ : KField a k} (hζ : IsPrimitiveRoot ζ k) :
    (∃ β ∈ ℚ⟮ζ⟯, β ^ 2 = (a : KField a k)) ↔ ∃ β : CyclotomicField k ℚ, β ^ 2 = a := by
  have : NeZero k := ⟨hk⟩
  have : IsCyclotomicExtension {k} ℚ ℚ⟮ζ⟯ := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  let _ : Algebra ℚ (CyclotomicField k ℚ) := CyclotomicField.algebra k ℚ
  let e := IsCyclotomicExtension.algEquiv {k} ℚ ℚ⟮ζ⟯ (CyclotomicField k ℚ)
  constructor
  · rintro ⟨β, hβ, h⟩
    refine ⟨e ⟨β, hβ⟩, ?_⟩
    rw [← map_pow, show (⟨β, hβ⟩ : ℚ⟮ζ⟯) ^ 2 = (a : ℚ⟮ζ⟯) from Subtype.ext (by simp [h])]
    simp
  · rintro ⟨γ, h⟩
    refine ⟨(e.symm γ : KField a k), (e.symm γ).2, ?_⟩
    have : (e.symm γ) ^ 2 = (a : ℚ⟮ζ⟯) := by rw [← map_pow, h]; simp
    simpa using congrArg (fun x : ℚ⟮ζ⟯ => (x : KField a k)) this
set_option synthInstance.maxHeartbeats 400000 in
open Classical in
noncomputable def kummerM (a : ℤ) (k : ℕ) : ℕ :=
  ∏ q ∈ k.primeFactors.filter (fun q =>
    if q = 2 then ∃ β : CyclotomicField k ℚ, β ^ 2 = a else ∃ c : ℤ, c ^ q = a), q
section General
variable {ζ α : KField a k}
set_option synthInstance.maxHeartbeats 400000 in
lemma pow_gcd_mem (ha : a ≠ 0) (hk : k ≠ 0) (hα : α ^ k = a) {i j : ℕ} (hi : α ^ i ∈ ℚ⟮ζ⟯)
    (hj : α ^ j ∈ ℚ⟮ζ⟯) : α ^ Nat.gcd i j ∈ ℚ⟮ζ⟯ := by
  have hα0 : α ≠ 0 := by
    rintro rfl; rw [zero_pow hk] at hα; exact ha (by exact_mod_cast hα.symm)
  have h1 : α ^ (Nat.gcd i j : ℤ) = (α ^ i) ^ (Nat.gcdA i j) * (α ^ j) ^ (Nat.gcdB i j) := by
    rw [Nat.gcd_eq_gcd_ab, zpow_add₀ hα0, zpow_mul, zpow_mul]; simp
  rw [← zpow_natCast, h1]
  exact mul_mem (zpow_mem hi _) (zpow_mem hj _)
set_option synthInstance.maxHeartbeats 400000 in
lemma pow_div_mem_iff (ha : a ≠ 0) (hk : k ≠ 0) (hζ : IsPrimitiveRoot ζ k) (hα : α ^ k = a)
    {q : ℕ} (hqk : q ∣ k) (hq0 : q ≠ 0) :
    α ^ (k / q) ∈ ℚ⟮ζ⟯ ↔ ∃ γ ∈ ℚ⟮ζ⟯, γ ^ q = a := by
  constructor
  · intro h
    refine ⟨_, h, ?_⟩
    rw [← pow_mul, Nat.div_mul_cancel hqk, hα]
  · rintro ⟨γ, hγ, hγq⟩
    have hγ0 : γ ≠ 0 := by
      rintro rfl; rw [zero_pow hq0] at hγq; exact ha (by exact_mod_cast hγq.symm)
    have e1 : (α ^ (k / q)) ^ q = γ ^ q := by rw [← pow_mul, Nat.div_mul_cancel hqk, hα, hγq]
    have hpow : (α ^ (k / q)) ^ k = γ ^ k := by
      obtain ⟨t, ht⟩ := hqk
      calc (α ^ (k / q)) ^ k = ((α ^ (k / q)) ^ q) ^ t := by rw [← pow_mul (α ^ (k / q)) q t, ← ht]
        _ = (γ ^ q) ^ t := by rw [e1]
        _ = γ ^ k := by rw [← pow_mul γ q t, ← ht]
    have := div_mem_adjoin_zeta hk hζ hγ0 hpow
    have heq : α ^ (k / q) = (α ^ (k / q) / γ) * γ := by field_simp
    rw [heq]; exact mul_mem this hγ
set_option synthInstance.maxHeartbeats 400000 in
theorem kummerDegree_mul_kummerM (ha : a ≠ 0) (hk : Squarefree k) :
    kummerDegree a k * kummerM a k = k * k.totient := by
  classical
  have hk0 : k ≠ 0 := hk.ne_zero
  obtain ⟨ζ, α, d, hζ, hα, ⟨m, hm⟩, hd0, hdeg, hmem, hmin⟩ := exists_structure ha hk0
  have hm0 : m ≠ 0 := by rintro rfl; simp at hm; exact hk0 hm
  have hmsq : Squarefree m := hk.squarefree_of_dvd ⟨d, by rw [hm, mul_comm]⟩
  have hdvd_of : ∀ i, 0 < i → α ^ i ∈ ℚ⟮ζ⟯ → d ∣ i := by
    intro i hi h
    have hg := pow_gcd_mem ha hk0 hα hmem h
    have := hmin _ (Nat.gcd_pos_of_pos_left _ hd0) hg
    have hle := Nat.gcd_le_left i hd0
    have : Nat.gcd d i = d := le_antisymm hle this
    rw [← this]; exact Nat.gcd_dvd_right _ _
  have key : ∀ q ∈ k.primeFactors, q ∣ m ↔ ∃ γ ∈ ℚ⟮ζ⟯, γ ^ q = a := by
    intro q hq
    have hq' := Nat.mem_primeFactors.1 hq
    rw [← pow_div_mem_iff ha hk0 hζ hα hq'.2.1 hq'.1.ne_zero]
    constructor
    · rintro ⟨t, rfl⟩
      have : k / q = d * t := by
        rw [hm, show d * (q * t) = q * (d * t) by ring,
          Nat.mul_div_cancel_left _ hq'.1.pos]
      rw [this, pow_mul]; exact pow_mem hmem _
    · intro h
      obtain ⟨t, ht⟩ := hdvd_of _ (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hk0) hq'.2.1)
        hq'.1.pos) h
      refine ⟨t, ?_⟩
      have h1 : k = q * (d * t) := by rw [← ht, Nat.mul_div_cancel' hq'.2.1]
      have : d * m = d * (q * t) := by rw [← hm, h1]; ring
      exact Nat.eq_of_mul_eq_mul_left hd0 this
  have hM : kummerM a k = m := by
    rw [← Nat.prod_primeFactors_of_squarefree hmsq]
    unfold kummerM
    congr 1
    ext q
    rw [Finset.mem_filter, Nat.mem_primeFactors, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hq, hqk, -⟩, hP⟩
      refine ⟨hq, (key q (Nat.mem_primeFactors.2 ⟨hq, hqk, hk0⟩)).2 ?_, hm0⟩
      by_cases h2 : q = 2
      · subst h2
        simp only [↓reduceIte] at hP
        exact (exists_sq_iff hk0 hζ).2 hP
      · simp only [h2, ↓reduceIte] at hP
        obtain ⟨c, hc⟩ := hP
        exact ⟨c, intCast_mem _ c, by rw [← hc]; push_cast; ring⟩
    · rintro ⟨hq, hqm, -⟩
      have hqk : q ∣ k := hqm.trans ⟨d, by rw [hm, mul_comm]⟩
      have hmem' := (key q (Nat.mem_primeFactors.2 ⟨hq, hqk, hk0⟩)).1 hqm
      refine ⟨⟨hq, hqk, hk0⟩, ?_⟩
      by_cases h2 : q = 2
      · subst h2
        simp only [↓reduceIte]
        exact (exists_sq_iff hk0 hζ).1 hmem'
      · simp only [h2, ↓reduceIte]
        obtain ⟨γ, hγ, hγq⟩ := hmem'
        exact exists_int_pow_of_mem_adjoin_zeta hk0 hζ hq h2 hγ hγq
  rw [hdeg, hM, hm]; ring
end General
end Artin.Kummer
end
section
namespace Artin.Kummer
open Polynomial IntermediateField
lemma adjoin_cyc_of_charZero {L : Type*} [Field L] [CharZero L] {n : ℕ} [NeZero n] {ζ : L}
    (hζ : IsPrimitiveRoot ζ n) : IsCyclotomicExtension {n} ℚ ℚ⟮ζ⟯ := by
  change IsCyclotomicExtension {n} ℚ (IntermediateField.adjoin ℚ {ζ}).toSubalgebra
  rw [IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
    ((hζ.isIntegral (NeZero.pos n)).tower_top (A := ℚ)).isAlgebraic]
  exact hζ.adjoin_isCyclotomicExtension ℚ
lemma cdf_eq_card (n : ℕ) : ArithmeticFunction.cardDistinctFactors n = n.primeFactors.card := by
  rw [ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors, List.card_toFinset]
section Unramified
variable {n : ℕ} [NeZero n] {L : Type*} [Field L] [CharZero L]
  [hL : IsCyclotomicExtension {n} ℚ L]
lemma exists_aeval_of_isIntegral {ζ : L} (hζ : IsPrimitiveRoot ζ n) {x : L}
    (hx : IsIntegral ℤ x) : ∃ h : ℤ[X], aeval ζ h = x := by
  have := IsCyclotomicExtension.Rat.isIntegralClosure_adjoin_singleton hζ
  obtain ⟨y, hy⟩ := (IsIntegralClosure.isIntegral_iff (A := Algebra.adjoin ℤ {ζ})).1 hx
  have hy2 : (y : L) ∈ (aeval (R := ℤ) ζ).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact y.2
  obtain ⟨h, hh⟩ := hy2
  exact ⟨h, by rw [← hy]; exact hh⟩
omit [CharZero L] hL in
lemma isIntegral_aeval {ζ : L} (hζ : IsPrimitiveRoot ζ n) (h : ℤ[X]) :
    IsIntegral ℤ (aeval ζ h) := by
  have hint : IsIntegral ℤ ζ := hζ.isIntegral (NeZero.pos n)
  have : aeval ζ h ∈ Algebra.adjoin ℤ {ζ} := by
    rw [Algebra.adjoin_singleton_eq_range_aeval]; exact ⟨h, rfl⟩
  exact adjoin_le_integralClosure hint this
lemma exists_eq_mul_of_sq_eq_mul {ζ : L} (hζ : IsPrimitiveRoot ζ n) {p : ℕ} (hp : p.Prime)
    (hpn : ¬ p ∣ n) {x y : L} (hx : IsIntegral ℤ x) (hy : IsIntegral ℤ y)
    (hxy : x ^ 2 = p * y) : ∃ z : L, IsIntegral ℤ z ∧ x = p * z := by
  obtain ⟨h, rfl⟩ := exists_aeval_of_isIntegral hζ hx
  obtain ⟨g, rfl⟩ := exists_aeval_of_isIntegral hζ hy
  have hint : IsIntegral ℤ ζ := hζ.isIntegral (NeZero.pos n)
  have hmin : minpoly ℤ ζ = cyclotomic n ℤ := (cyclotomic_eq_minpoly hζ (NeZero.pos n)).symm
  have hdvd : cyclotomic n ℤ ∣ h ^ 2 - C (p : ℤ) * g := by
    rw [← hmin]; apply minpoly.isIntegrallyClosed_dvd hint; simp [hxy]
  have := Fact.mk hp
  have hdvd' : cyclotomic n (ZMod p) ∣ (h.map (Int.castRingHom (ZMod p))) ^ 2 := by
    have := Polynomial.map_dvd (Int.castRingHom (ZMod p)) hdvd
    simpa [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow, map_cyclotomic] using this
  have hn0 : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]; exact hpn
  have hsq : Squarefree (cyclotomic n (ZMod p)) :=
    ((X_pow_sub_one_separable_iff.2 hn0).of_dvd (cyclotomic.dvd_X_pow_sub_one n _)).squarefree
  obtain ⟨q, hq⟩ := (hsq.dvd_pow_iff_dvd two_ne_zero).1 hdvd'
  obtain ⟨q', rfl⟩ := Polynomial.map_surjective (Int.castRingHom (ZMod p))
    (ZMod.ringHom_surjective _) q
  have hker : (h - cyclotomic n ℤ * q').map (Int.castRingHom (ZMod p)) = 0 := by
    simp [hq, map_cyclotomic]
  have hcoeff : ∀ i, (p : ℤ) ∣ (h - cyclotomic n ℤ * q').coeff i := fun i => by
    have := congrArg (fun f => f.coeff i) hker
    simp only [Polynomial.coeff_map, coeff_zero, eq_intCast] at this
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 this
  obtain ⟨r, hr⟩ := (Polynomial.C_dvd_iff_dvd_coeff _ _).2 hcoeff
  refine ⟨aeval ζ r, isIntegral_aeval hζ r, ?_⟩
  have := congrArg (aeval ζ) hr
  have hcyc : aeval ζ (cyclotomic n ℤ) = 0 := by rw [← hmin]; exact minpoly.aeval ℤ ζ
  simp only [map_sub, map_mul, hcyc, zero_mul, sub_zero, map_natCast] at this
  exact this
omit [NeZero n] hL in
lemma dvd_of_eq_mul_isIntegral {c m : ℤ} (hm : m ≠ 0) {z : L} (hz : IsIntegral ℤ z)
    (h : (c : L) = m * z) : m ∣ c := by
  have hzq : z = algebraMap ℚ L ((c : ℚ) / m) := by
    have hm' : (m : L) ≠ 0 := by exact_mod_cast hm
    rw [map_div₀, map_intCast, map_intCast, h]; field_simp
  rw [hzq] at hz
  have hq : IsIntegral ℤ ((c : ℚ) / m) :=
    (isIntegral_algHom_iff ((Algebra.ofId ℚ L).restrictScalars ℤ)
      (algebraMap ℚ L).injective).1 hz
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hq
  refine ⟨y, ?_⟩
  have hm' : (m : ℚ) ≠ 0 := by exact_mod_cast hm
  have : (c : ℚ) = m * y := by rw [algebraMap_int_eq, eq_intCast] at hy; rw [hy]; field_simp
  exact_mod_cast this
theorem mod_four_and_dvd_of_sq_eq {ζ : L} (hζ : IsPrimitiveRoot ζ n) (hn : Odd n) {a₀ : ℤ}
    (h₀ : Squarefree a₀) {β : L} (hβ : β ^ 2 = a₀) : a₀ % 4 = 1 ∧ a₀.natAbs ∣ n := by
  have hβi : IsIntegral ℤ β :=
    ⟨X ^ 2 - C a₀, monic_X_pow_sub_C _ two_ne_zero, by rw [← aeval_def]; simp [hβ]⟩
  have hprime : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ a₀ → p ∣ n := by
    intro p hp hpa
    by_contra hpn
    obtain ⟨e, he⟩ := hpa
    obtain ⟨z, hz, hβz⟩ := exists_eq_mul_of_sq_eq_mul hζ hp hpn hβi
      (y := (e : L)) (by simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ L e)))
      (by rw [hβ, he]; push_cast; ring)
    have h2 : ((p : ℤ) * p) ∣ a₀ := by
      refine dvd_of_eq_mul_isIntegral
        (mul_ne_zero (by exact_mod_cast hp.ne_zero) (by exact_mod_cast hp.ne_zero)) (hz.pow 2) ?_
      rw [← hβ, hβz]; push_cast; ring
    have := h₀ p h2
    rw [Int.isUnit_iff] at this
    have := hp.two_le
    omega
  have hodd : ¬ (2 : ℤ) ∣ a₀ := fun h2 =>
    (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 (hprime 2 Nat.prime_two (by exact_mod_cast h2)))
  refine ⟨?_, ?_⟩
  · obtain ⟨t, ht⟩ : ∃ t, a₀ = 2 * t + 1 := ⟨a₀ / 2, by omega⟩
    have h2n : ¬ 2 ∣ n := fun h => (Nat.not_even_iff_odd.2 hn) (even_iff_two_dvd.2 h)
    have hti : IsIntegral ℤ (((t + 1 : ℤ) : L)) := by
      simpa using (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ L (t + 1)))
    obtain ⟨z, hz, h1z⟩ := exists_eq_mul_of_sq_eq_mul hζ Nat.prime_two h2n
      (isIntegral_one.add hβi) (hti.add hβi)
      (x := 1 + β) (y := ((t + 1 : ℤ) : L) + β) (by
        rw [add_sq, hβ, ht]; push_cast; ring)
    have h4 : (4 : ℤ) ∣ a₀ - 1 := by
      refine dvd_of_eq_mul_isIntegral (by norm_num) ((hz.pow 2).sub hz) ?_
      have hβ' : β = 2 * z - 1 := by push_cast at h1z; linear_combination h1z
      have : (a₀ : L) = (2 * z - 1) ^ 2 := by rw [← hβ, hβ']
      push_cast; rw [this]; ring
    omega
  · have hsq : Squarefree a₀.natAbs := Int.squarefree_natAbs.2 h₀
    rw [← Nat.prod_primeFactors_of_squarefree hsq]
    refine Finset.prod_primes_dvd _ (fun p hp => (Nat.prime_of_mem_primeFactors hp).prime)
      fun p hp => hprime p (Nat.prime_of_mem_primeFactors hp) ?_
    exact Int.natCast_dvd.2 (Nat.dvd_of_mem_primeFactors hp)
end Unramified
section GaussSum
open ZMod in
lemma exists_sq_eq_chi_four_mul {L : Type*} [Field L] [CharZero L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {ζ : L} (hζ : IsPrimitiveRoot ζ p) :
    ∃ g : L, g ^ 2 = ((χ₄ (p : ZMod 4) * p : ℤ) : L) := by
  have := Fact.mk hp
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hL : ringChar L ≠ 2 := by rw [ringChar.eq_zero]; norm_num
  let χ := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom L)
  have hχ₁ : χ ≠ 1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one' hF
    refine MulChar.ne_one_iff.mpr ⟨a, ?_⟩
    simpa only [MulChar.ringHomComp_apply, ha, eq_intCast, Int.cast_neg, Int.cast_one, χ] using
      Ring.neg_one_ne_one_of_char_ne_two hL
  refine ⟨gaussSum χ (AddChar.zmodChar p ((IsPrimitiveRoot.iff_def ζ p).mp hζ).left), ?_⟩
  rw [gaussSum_sq hχ₁ ((quadraticChar_isQuadratic _).comp _)
    (AddChar.zmodChar_primitive_of_primitive_root p hζ)]
  simp [χ, quadraticChar_neg_one hF, ZMod.card]
end GaussSum
section CyclotomicField
variable {k : ℕ}
theorem mod_four_and_dvd_of_sq_eq' {L : Type*} [Field L] [CharZero L] (hk : Squarefree k)
    [hL : IsCyclotomicExtension {k} ℚ L] {a₀ : ℤ} (h₀ : Squarefree a₀) {β : L}
    (hβ : β ^ 2 = a₀) : a₀ % 4 = 1 ∧ a₀.natAbs ∣ k := by
  have : NeZero k := ⟨hk.ne_zero⟩
  have hζ := IsCyclotomicExtension.zeta_spec k ℚ L
  set ζ := IsCyclotomicExtension.zeta k ℚ L
  obtain ⟨n, e, hn, he, hkne⟩ : ∃ n e, Odd n ∧ (e = 1 ∨ e = 2) ∧ k = e * n := by
    by_cases h2 : 2 ∣ k
    · obtain ⟨n, rfl⟩ := h2
      refine ⟨n, 2, Nat.not_even_iff_odd.1 fun ⟨m, hm⟩ => ?_, Or.inr rfl, rfl⟩
      have := hk 2 ⟨m, by rw [hm]; ring⟩
      exact absurd this (by decide)
    · exact ⟨k, 1, Nat.not_even_iff_odd.1 (fun h => h2 (even_iff_two_dvd.1 h)), Or.inl rfl,
        (one_mul k).symm⟩
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hη : IsPrimitiveRoot (ζ ^ e) n := hζ.pow (NeZero.pos k) hkne
  have hζmem : ζ ∈ ℚ⟮ζ ^ e⟯ := by
    rcases he with rfl | rfl
    · simpa using mem_adjoin_simple_self ℚ ζ
    · have hneg : ζ ^ n = -1 := by
        have h1 : (ζ ^ n) ^ 2 = 1 := by rw [← pow_mul, mul_comm, ← hkne]; exact hζ.pow_eq_one
        have h2 : ζ ^ n ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hn0 (by omega)
        have : (ζ ^ n - 1) * (ζ ^ n + 1) = 0 := by linear_combination h1
        rcases mul_eq_zero.1 this with h | h
        · exact absurd (sub_eq_zero.1 h) h2
        · exact eq_neg_of_add_eq_zero_left h
      have : ζ = -((ζ ^ 2) ^ ((n + 1) / 2)) := by
        rw [← pow_mul, Nat.mul_div_cancel' (even_iff_two_dvd.1 (hn.add_one)), pow_succ, hneg]
        ring
      have hmem : -((ζ ^ 2) ^ ((n + 1) / 2)) ∈ ℚ⟮ζ ^ 2⟯ :=
        neg_mem (pow_mem (mem_adjoin_simple_self ℚ (ζ ^ 2)) _)
      exact Eq.mpr (congrArg (fun x => x ∈ ℚ⟮ζ ^ 2⟯) this) hmem
  have hβmem : β ∈ ℚ⟮ζ ^ e⟯ := by
    have htop := IsCyclotomicExtension.adjoin_primitive_root_eq_top (A := ℚ) hζ
    have : β ∈ Algebra.adjoin ℚ {ζ} := htop ▸ Algebra.mem_top
    exact (Algebra.adjoin_le (Set.singleton_subset_iff.2 hζmem) :
      Algebra.adjoin ℚ {ζ} ≤ (ℚ⟮ζ ^ e⟯).toSubalgebra) this
  have : NeZero n := ⟨hn0⟩
  have hcyc := adjoin_cyc_of_charZero hη
  have hη' : IsPrimitiveRoot (AdjoinSimple.gen ℚ (ζ ^ e)) n :=
    IsPrimitiveRoot.coe_submonoidClass_iff.mp hη
  obtain ⟨h1, h2⟩ := mod_four_and_dvd_of_sq_eq (hL := by convert hcyc) hη' hn h₀
    (β := ⟨β, hβmem⟩) (Subtype.ext (by simpa using hβ))
  exact ⟨h1, h2.trans ⟨e, by rw [hkne, mul_comm]⟩⟩
theorem mod_four_and_dvd_of_exists_sq (hk : Squarefree k) {a₀ : ℤ} (h₀ : Squarefree a₀)
    {β : CyclotomicField k ℚ} (hβ : β ^ 2 = a₀) : a₀ % 4 = 1 ∧ a₀.natAbs ∣ k := by
  have : NeZero k := ⟨hk.ne_zero⟩
  exact mod_four_and_dvd_of_sq_eq' hk
    (hL := CyclotomicField.isCyclotomicExtension k ℚ) h₀ hβ
open ZMod in
theorem exists_sq_of_mod_four (hk : k ≠ 0) {a₀ : ℤ} (h₀ : Squarefree a₀) (h4 : a₀ % 4 = 1)
    (hdvd : a₀.natAbs ∣ k) : ∃ β : CyclotomicField k ℚ, β ^ 2 = a₀ := by
  have : NeZero k := ⟨hk⟩
  let _ : Algebra ℚ (CyclotomicField k ℚ) := CyclotomicField.algebra k ℚ
  set F := CyclotomicField k ℚ
  have hζ := IsCyclotomicExtension.zeta_spec k ℚ F
  set ζ := IsCyclotomicExtension.zeta k ℚ F
  set s := a₀.natAbs.primeFactors
  have hg : ∀ p ∈ s, ∃ g : F, g ^ 2 = ((χ₄ (p : ZMod 4) * p : ℤ) : F) := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hpk : p ∣ k := (Nat.dvd_of_mem_primeFactors hp).trans hdvd
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : (2 : ℤ) ∣ a₀ := Int.natCast_dvd.2 (Nat.dvd_of_mem_primeFactors hp)
      omega
    obtain ⟨m, hm⟩ := hpk
    exact exists_sq_eq_chi_four_mul hp' hp2 (hζ.pow (NeZero.pos k) (by rw [hm, mul_comm]))
  choose! g hg' using hg
  refine ⟨∏ p ∈ s, g p, ?_⟩
  rw [← Finset.prod_pow, Finset.prod_congr rfl hg', ← Int.cast_prod]
  congr 1
  have hsq : Squarefree a₀.natAbs := Int.squarefree_natAbs.2 h₀
  rw [Finset.prod_mul_distrib, ← map_prod, ← Nat.cast_prod, ← Nat.cast_prod,
    Nat.prod_primeFactors_of_squarefree hsq, χ₄_nat_eq_if_mod_four]
  have habs := Int.natAbs_eq a₀
  generalize a₀.natAbs = m at habs ⊢
  rcases habs with h | h
  · have : m % 4 = 1 := by omega
    have h2 : m % 2 = 1 := by omega
    simp only [h2, this]
    norm_num
    omega
  · have : m % 4 = 3 := by omega
    have h2 : m % 2 = 1 := by omega
    simp only [h2, this]
    norm_num
    omega
end CyclotomicField
end Artin.Kummer
end

section
namespace Artin.Kummer
open ArithmeticFunction Finset
noncomputable def sqfreeWeight (k : ℕ) : ℝ :=
  if Squarefree k then ∏ p ∈ k.primeFactors, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ else 0
lemma inv_mul_pred_nonneg {p : ℕ} (hp : 1 ≤ p) : 0 ≤ ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
  have : (1 : ℝ) ≤ p := by exact_mod_cast hp
  exact inv_nonneg.2 (mul_nonneg (by linarith) (by linarith))
lemma sqfreeWeight_nonneg (k : ℕ) : 0 ≤ sqfreeWeight k := by
  unfold sqfreeWeight
  split_ifs
  · exact prod_nonneg fun p hp => inv_mul_pred_nonneg (Nat.prime_of_mem_primeFactors hp).one_le
  · exact le_rfl
lemma sqfreeWeight_eq {k : ℕ} (hk : Squarefree k) :
    sqfreeWeight k = ((k : ℝ) * k.totient)⁻¹ := by
  have hk0 : k ≠ 0 := hk.ne_zero
  have hprod := Nat.prod_primeFactors_of_squarefree hk
  have htot : k.totient = ∏ p ∈ k.primeFactors, (p - 1) := by
    have h := Nat.totient_mul_prod_primeFactors k
    rw [hprod] at h
    exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hk0) (by rw [h, mul_comm])
  have e1 : (k : ℝ) = ∏ p ∈ k.primeFactors, (p : ℝ) := by rw [← Nat.cast_prod, hprod]
  have e2 : (k.totient : ℝ) = ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) := by
    rw [htot, Nat.cast_prod]
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]
  simp only [sqfreeWeight, hk, ↓reduceIte]
  rw [e1, e2, ← prod_mul_distrib, prod_inv_distrib]
lemma sum_prod_le_prod_one_add {s P : Finset ℕ} {x : ℕ → ℝ} (hx : ∀ p, 0 ≤ x p)
    (hs : ∀ k ∈ s, Squarefree k ∧ k.primeFactors ⊆ P) :
    ∑ k ∈ s, ∏ p ∈ k.primeFactors, x p ≤ ∏ p ∈ P, (1 + x p) := by
  rw [prod_one_add]
  have hinj : Set.InjOn Nat.primeFactors s := by
    intro k hk l hl hkl
    rw [← Nat.prod_primeFactors_of_squarefree (hs k hk).1,
      ← Nat.prod_primeFactors_of_squarefree (hs l hl).1, hkl]
  rw [← sum_image (f := fun t => ∏ p ∈ t, x p) hinj]
  refine sum_le_sum_of_subset_of_nonneg ?_ fun t _ _ => prod_nonneg fun p _ => hx p
  intro t ht
  obtain ⟨k, hk, rfl⟩ := mem_image.1 ht
  exact mem_powerset.2 (hs k hk).2
lemma prod_one_add_le_exp {P : Finset ℕ} {x : ℕ → ℝ} (hx : ∀ p, 0 ≤ x p) :
    ∏ p ∈ P, (1 + x p) ≤ Real.exp (∑ p ∈ P, x p) := by
  rw [Real.exp_sum]
  exact Finset.prod_le_prod (fun p _ => by linarith [hx p])
    fun p _ => by have := Real.add_one_le_exp (x p); linarith
lemma sum_Ico_inv_mul_pred {m : ℕ} (hm : 2 ≤ m) (j : ℕ) :
    ∑ n ∈ Ico m (m + j), ((n : ℝ) * ((n : ℝ) - 1))⁻¹
      = ((m : ℝ) - 1)⁻¹ - ((m + j : ℕ) - 1 : ℝ)⁻¹ := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [← add_assoc, sum_Ico_succ_top (by omega), ih]
    have h1 : (2 : ℝ) ≤ (m + j : ℕ) := by exact_mod_cast (show 2 ≤ m + j by omega)
    have h2 : ((m + j : ℕ) : ℝ) - 1 ≠ 0 := by linarith
    have h3 : ((m + j : ℕ) : ℝ) ≠ 0 := by linarith
    have key : (((m + j : ℕ) : ℝ) * (((m + j : ℕ) : ℝ) - 1))⁻¹
        = (((m + j : ℕ) : ℝ) - 1)⁻¹ - (((m + j : ℕ) : ℝ))⁻¹ := by
      field_simp; ring
    rw [key]
    push_cast
    ring
lemma sum_inv_mul_pred_le {P : Finset ℕ} {m : ℕ} (hm : 2 ≤ m) (hP : ∀ p ∈ P, m ≤ p) :
    ∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ ≤ ((m : ℝ) - 1)⁻¹ := by
  set j := P.sup id + 1
  have hsub : P ⊆ Ico m (m + j) := by
    intro p hp
    have : p ≤ P.sup id := le_sup (f := id) hp
    exact mem_Ico.2 ⟨hP p hp, by omega⟩
  calc ∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹
      ≤ ∑ n ∈ Ico m (m + j), ((n : ℝ) * ((n : ℝ) - 1))⁻¹ :=
        sum_le_sum_of_subset_of_nonneg hsub fun n hn _ =>
          inv_mul_pred_nonneg (by have := (mem_Ico.1 hn).1; omega)
    _ = ((m : ℝ) - 1)⁻¹ - ((m + j : ℕ) - 1 : ℝ)⁻¹ := sum_Ico_inv_mul_pred hm j
    _ ≤ ((m : ℝ) - 1)⁻¹ := by
        have : (1 : ℝ) ≤ ((m + j : ℕ) : ℝ) - 1 := by
          have : (2 : ℝ) ≤ ((m + j : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ m + j by omega)
          linarith
        linarith [inv_nonneg.2 (show (0 : ℝ) ≤ ((m + j : ℕ) : ℝ) - 1 by linarith)]
lemma sum_sqfreeWeight_le (s : Finset ℕ) : ∑ k ∈ s, sqfreeWeight k ≤ Real.exp 1 := by
  set P := (range (s.sup id + 1)).filter Nat.Prime
  have hP : ∀ p ∈ P, 2 ≤ p := fun p hp => (mem_filter.1 hp).2.two_le
  calc ∑ k ∈ s, sqfreeWeight k
      = ∑ k ∈ s.filter Squarefree, ∏ p ∈ k.primeFactors, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
        rw [sum_filter]; rfl
    _ ≤ ∏ p ∈ P, (1 + ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
        refine sum_prod_le_prod_one_add (fun p => ?_) fun k hk => ⟨(mem_filter.1 hk).2, ?_⟩
        · rcases Nat.eq_zero_or_pos p with rfl | hp
          · simp
          · exact inv_mul_pred_nonneg hp
        · intro p hp
          have hp' := Nat.mem_primeFactors.1 hp
          have hks : k ≤ s.sup id := le_sup (f := id) (mem_filter.1 hk).1
          exact mem_filter.2 ⟨mem_range.2 (by
            have := Nat.le_of_dvd (Nat.pos_of_ne_zero hp'.2.2) hp'.2.1; omega), hp'.1⟩
    _ ≤ Real.exp (∑ p ∈ P, ((p : ℝ) * ((p : ℝ) - 1))⁻¹) := by
        refine prod_one_add_le_exp fun p => ?_
        rcases Nat.eq_zero_or_pos p with rfl | hp
        · simp
        · exact inv_mul_pred_nonneg hp
    _ ≤ Real.exp 1 := by
        refine Real.exp_le_exp.2 ((sum_inv_mul_pred_le le_rfl hP).trans ?_)
        norm_num
noncomputable def oddWeight (k : ℕ) : ℝ := if Odd k ∧ k ≠ 1 then sqfreeWeight k else 0
lemma oddWeight_nonneg (k : ℕ) : 0 ≤ oddWeight k := by
  unfold oddWeight; split_ifs
  · exact sqfreeWeight_nonneg k
  · exact le_rfl
lemma sum_oddWeight_le (s : Finset ℕ) : ∑ k ∈ s, oddWeight k ≤ Real.exp (1 / 2) - 1 := by
  set s' := s.filter fun k => Squarefree k ∧ Odd k ∧ k ≠ 1
  set P := (range (s.sup id + 1)).filter fun p => Nat.Prime p ∧ 3 ≤ p
  set x : ℕ → ℝ := fun p => ((p : ℝ) * ((p : ℝ) - 1))⁻¹
  have hx : ∀ p, 0 ≤ x p := fun p => by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp [x]
    · exact inv_mul_pred_nonneg hp
  have h1 : (1 : ℕ) ∉ s' := by simp [s']
  have heq : ∑ k ∈ s, oddWeight k = ∑ k ∈ s', ∏ p ∈ k.primeFactors, x p := by
    rw [sum_filter]
    refine sum_congr rfl fun k _ => ?_
    simp only [oddWeight, sqfreeWeight, x]
    by_cases hsq : Squarefree k <;> by_cases ho : Odd k <;> by_cases h1 : k = 1 <;>
      simp [hsq, ho, h1]
  have hle : ∑ k ∈ insert 1 s', ∏ p ∈ k.primeFactors, x p ≤ ∏ p ∈ P, (1 + x p) := by
    refine sum_prod_le_prod_one_add hx fun k hk => ?_
    rcases mem_insert.1 hk with rfl | hk
    · exact ⟨squarefree_one, by simp⟩
    · have hk' := mem_filter.1 hk
      refine ⟨hk'.2.1, fun p hp => ?_⟩
      have hp' := Nat.mem_primeFactors.1 hp
      have hks : k ≤ s.sup id := le_sup (f := id) hk'.1
      have hp3 : 3 ≤ p := by
        rcases hp'.1.eq_two_or_odd' with h2 | hodd
        · subst h2
          exact absurd (even_iff_two_dvd.2 hp'.2.1) (Nat.not_even_iff_odd.2 hk'.2.2.1)
        · have := hp'.1.two_le
          rcases Nat.lt_or_ge p 3 with h | h
          · interval_cases p; exact absurd hodd (by decide)
          · exact h
      exact mem_filter.2 ⟨mem_range.2 (by
        have := Nat.le_of_dvd (Nat.pos_of_ne_zero hp'.2.2) hp'.2.1; omega), hp'.1, hp3⟩
  rw [sum_insert h1, Nat.primeFactors_one, prod_empty] at hle
  have hexp : ∏ p ∈ P, (1 + x p) ≤ Real.exp (1 / 2) := by
    refine (prod_one_add_le_exp hx).trans (Real.exp_le_exp.2 ?_)
    refine (sum_inv_mul_pred_le (m := 3) (by norm_num)
      fun p hp => (mem_filter.1 hp).2.2).trans ?_
    norm_num
  rw [heq]
  linarith
lemma exp_half_lt_two : Real.exp (1 / 2) < 2 := by
  have h := Real.exp_one_lt_d9
  have hsq : Real.exp (1 / 2) * Real.exp (1 / 2) = Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [Real.exp_pos (1 / 2)]
lemma summable_sqfreeWeight : Summable sqfreeWeight :=
  summable_of_sum_le sqfreeWeight_nonneg sum_sqfreeWeight_le
lemma summable_oddWeight : Summable oddWeight :=
  summable_of_sum_le oddWeight_nonneg sum_oddWeight_le
lemma tsum_oddWeight_lt_one : ∑' k, oddWeight k < 1 := by
  have := Real.tsum_le_of_sum_le oddWeight_nonneg sum_oddWeight_le
  linarith [exp_half_lt_two]
noncomputable def kummerDensity (a : ℤ) : ℝ :=
  ∑' k : ℕ, (moebius k : ℝ) / kummerDegree a k
variable {a : ℤ}
lemma moebius_div_kummerDegree_of_not_squarefree {k : ℕ} (hk : ¬ Squarefree k) :
    (moebius k : ℝ) / kummerDegree a k = 0 := by
  simp [moebius_eq_zero_of_not_squarefree hk]
lemma not_squarefree_two_mul_of_even {j : ℕ} (hj : Even j) : ¬ Squarefree (2 * j) := by
  obtain ⟨i, rfl⟩ := hj
  intro h
  have := h 2 ⟨i, by ring⟩
  exact absurd this (by decide)
lemma squarefree_two_mul {j : ℕ} (hj : Odd j) (hsq : Squarefree j) : Squarefree (2 * j) :=
  Nat.squarefree_mul_iff.2 ⟨(Nat.coprime_two_left.2 hj), Nat.squarefree_two, hsq⟩
theorem summable_moebius_div_kummerDegree_of_ne (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : a ≠ -1) :
    Summable fun k : ℕ => (moebius k : ℝ) / kummerDegree a k := by
  refine Summable.of_norm_bounded (summable_sqfreeWeight.mul_left ((4 : ℝ) ^ a.natAbs)) fun k => ?_
  rw [Real.norm_eq_abs]
  by_cases hk : Squarefree k
  · have hle : (k * k.totient : ℝ) ≤ 4 ^ a.natAbs * kummerDegree a k := by
      exact_mod_cast mul_totient_le_kummerDegree ha0 ha1 ha2 hk
    have hpos : (0 : ℝ) < k * k.totient := by
      have := Nat.pos_of_ne_zero hk.ne_zero
      have := Nat.totient_pos.2 this
      positivity
    have hdeg : (0 : ℝ) < kummerDegree a k := by
      by_contra h; push Not at h; nlinarith [pow_pos (show (0 : ℝ) < 4 by norm_num) a.natAbs]
    rw [abs_div, abs_of_pos hdeg, sqfreeWeight_eq hk, div_le_iff₀ hdeg]
    have hμ : |(moebius k : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
    calc |(moebius k : ℝ)| ≤ 1 := hμ
      _ = 4 ^ a.natAbs * ((k : ℝ) * k.totient)⁻¹ * (4 ^ a.natAbs)⁻¹ * ((k : ℝ) * k.totient) := by
        field_simp; exact (div_self hpos.ne').symm
      _ ≤ 4 ^ a.natAbs * ((k : ℝ) * k.totient)⁻¹ * (4 ^ a.natAbs)⁻¹ *
          (4 ^ a.natAbs * kummerDegree a k) := by gcongr
      _ = 4 ^ a.natAbs * ((k : ℝ) * k.totient)⁻¹ * kummerDegree a k := by field_simp
  · rw [moebius_div_kummerDegree_of_not_squarefree hk, abs_zero]
    exact mul_nonneg (by positivity) (sqfreeWeight_nonneg k)
theorem exists_sq_cyclotomicField_iff {a₀ c : ℤ} (ha : ¬ IsSquare a) (h₀ : Squarefree a₀)
    (hac : a = a₀ * c ^ 2) {k : ℕ} (hk : Squarefree k) :
    (∃ β : CyclotomicField k ℚ, β ^ 2 = a) ↔ a₀ % 4 = 1 ∧ a₀.natAbs ∣ k := by
  have hc : c ≠ 0 := by
    rintro rfl; exact ha ⟨0, by simp [hac]⟩
  have hc' : (c : CyclotomicField k ℚ) ≠ 0 := by exact_mod_cast hc
  constructor
  · rintro ⟨β, hβ⟩
    refine mod_four_and_dvd_of_exists_sq hk h₀ (β := β / c) ?_
    rw [div_pow, hβ, hac]; push_cast; field_simp
  · rintro ⟨h4, hdvd⟩
    obtain ⟨β, hβ⟩ := exists_sq_of_mod_four hk.ne_zero h₀ h4 hdvd
    exact ⟨β * c, by rw [mul_pow, hβ, hac]; push_cast; ring⟩
section Weights
variable (P : ℕ → Prop) [DecidablePred P]
noncomputable def xw (p : ℕ) : ℝ := (if P p then (p : ℝ) else 1) * ((p : ℝ) * ((p : ℝ) - 1))⁻¹
noncomputable def hw (j : ℕ) : ℝ :=
  if Odd j ∧ Squarefree j then ∏ p ∈ j.primeFactors, -xw P p else 0
noncomputable def coprimeSum (g : ℕ → ℝ) (D : ℕ) : ℝ := ∑' j, if Nat.Coprime j D then g j else 0
variable {P}
lemma xw_pos {p : ℕ} (hp : p.Prime) : 0 < xw P p := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  unfold xw
  apply mul_pos
  · split_ifs <;> linarith
  · apply inv_pos.2; nlinarith
lemma xw_le {p : ℕ} (hp : p.Prime) : xw P p ≤ ((p : ℝ) - 1)⁻¹ := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hp1 : (0 : ℝ) < p - 1 := by linarith
  unfold xw
  calc (if P p then (p : ℝ) else 1) * ((p : ℝ) * ((p : ℝ) - 1))⁻¹
      ≤ p * ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        split_ifs <;> linarith
    _ = ((p : ℝ) - 1)⁻¹ := by field_simp
lemma xw_le_half {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : xw P p ≤ 1 / 2 := by
  have h3 : (3 : ℝ) ≤ p := by have := hp.two_le; exact_mod_cast (by omega : 3 ≤ p)
  refine (xw_le hp).trans ?_
  calc ((p : ℝ) - 1)⁻¹ ≤ (2 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    _ = 1 / 2 := by norm_num
lemma xw_lt_half {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) : xw P p < 1 / 2 := by
  have h5 : (5 : ℝ) ≤ p := by
    have := hp.two_le
    have h4 : p ≠ 4 := by rintro rfl; exact absurd hp (by decide)
    exact_mod_cast (by omega : 5 ≤ p)
  refine (xw_le hp).trans_lt ?_
  calc ((p : ℝ) - 1)⁻¹ ≤ (4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) (by linarith)
    _ < 1 / 2 := by norm_num
lemma xw_two (hP2 : ¬ P 2) : xw P 2 = 1 / 2 := by
  simp [xw, hP2]; norm_num
lemma hw_one : hw P 1 = 1 := by simp [hw]
lemma hw_of_not_odd {j : ℕ} (hj : ¬ Odd j) : hw P j = 0 := by simp [hw, hj]
lemma hw_eq_prod {j : ℕ} (hj : Odd j) (hsq : Squarefree j) :
    hw P j = ∏ p ∈ j.primeFactors, -xw P p := by simp [hw, hj, hsq]
lemma hw_mul_prime {p j : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hj : ¬ p ∣ j) :
    hw P (p * j) = -xw P p * hw P j := by
  have hj0 : j ≠ 0 := by rintro rfl; exact hj (dvd_zero p)
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hcop : Nat.Coprime p j := (Nat.Prime.coprime_iff_not_dvd hp).2 hj
  have hodd : Odd (p * j) ↔ Odd j := by rw [Nat.odd_mul]; simp [hpodd]
  have hsq : Squarefree (p * j) ↔ Squarefree j := by
    rw [Nat.squarefree_mul_iff]
    exact ⟨fun h => h.2.2, fun h => ⟨hcop, hp.prime.squarefree, h⟩⟩
  unfold hw
  by_cases h : Odd j ∧ Squarefree j
  · rw [if_pos ⟨hodd.2 h.1, hsq.2 h.2⟩, if_pos h, Nat.primeFactors_mul hp.ne_zero hj0,
      hp.primeFactors, Finset.singleton_union,
      Finset.prod_insert (fun h' => hj (Nat.dvd_of_mem_primeFactors h'))]
  · rw [if_neg (fun h' => h ⟨hodd.1 h'.1, hsq.1 h'.2⟩), if_neg h, mul_zero]
lemma hw_mul_prime_of_dvd {p j : ℕ} (hp : p.Prime) (hj : p ∣ j) : hw P (p * j) = 0 := by
  unfold hw
  rw [if_neg]
  rintro ⟨-, hsq⟩
  obtain ⟨i, rfl⟩ := hj
  have := hsq p ⟨i, by ring⟩
  exact hp.one_lt.ne' (Nat.isUnit_iff.1 this)
lemma hw_mul_of_coprime {m j : ℕ} (h : Nat.Coprime m j) : hw P (m * j) = hw P m * hw P j := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [hw]
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp [hw]
  have hsq : Squarefree (m * j) ↔ Squarefree m ∧ Squarefree j := by
    rw [Nat.squarefree_mul_iff]
    exact ⟨fun h' => ⟨h'.2.1, h'.2.2⟩, fun h' => ⟨h, h'.1, h'.2⟩⟩
  unfold hw
  by_cases h1 : Odd m ∧ Squarefree m <;> by_cases h2 : Odd j ∧ Squarefree j
  · rw [if_pos ⟨Nat.odd_mul.2 ⟨h1.1, h2.1⟩, hsq.2 ⟨h1.2, h2.2⟩⟩, if_pos h1, if_pos h2,
      Nat.primeFactors_mul hm.ne' hj.ne', Finset.prod_union h.disjoint_primeFactors]
  · rw [if_neg (fun h' => h2 ⟨(Nat.odd_mul.1 h'.1).2, (hsq.1 h'.2).2⟩), if_neg h2, mul_zero]
  · rw [if_neg (fun h' => h1 ⟨(Nat.odd_mul.1 h'.1).1, (hsq.1 h'.2).1⟩), if_neg h1, zero_mul]
  · rw [if_neg (fun h' => h1 ⟨(Nat.odd_mul.1 h'.1).1, (hsq.1 h'.2).1⟩), if_neg h1, zero_mul]
lemma hw_mul_of_not_coprime {m j : ℕ} (h : ¬ Nat.Coprime m j) : hw P (m * j) = 0 := by
  unfold hw
  rw [if_neg]
  rintro ⟨-, hsq⟩
  exact h (Nat.squarefree_mul_iff.1 hsq).1
end Weights
section Peel
lemma summable_coprime {g : ℕ → ℝ} (hg : Summable g) (D : ℕ) :
    Summable fun j => if Nat.Coprime j D then g j else 0 :=
  Summable.of_norm_bounded hg.norm fun j => by split_ifs <;> simp
lemma coprimeSum_peel {g : ℕ → ℝ} (hg : Summable g) {p D : ℕ} (hp : p.Prime) (hpD : ¬ p ∣ D)
    {c : ℝ} (hmul : ∀ j, ¬ p ∣ j → g (p * j) = c * g j) (hsq : ∀ j, p ∣ j → g (p * j) = 0) :
    coprimeSum g D = (1 + c) * coprimeSum g (p * D) := by
  set A : ℕ → ℝ := fun j => if Nat.Coprime j D then g j else 0 with hA_def
  set B : ℕ → ℝ := fun j => if Nat.Coprime j (p * D) then g j else 0 with hB_def
  set C : ℕ → ℝ := fun j => if p ∣ j then A j else 0 with hC_def
  have hA : Summable A := summable_coprime hg D
  have hB : Summable B := summable_coprime hg (p * D)
  have hC : Summable C :=
    Summable.of_norm_bounded hA.norm fun j => by simp only [C]; split_ifs <;> simp
  have hcopD : Nat.Coprime p D := (Nat.Prime.coprime_iff_not_dvd hp).2 hpD
  have hiff : ∀ j, Nat.Coprime j p ↔ ¬ p ∣ j := fun j =>
    Nat.coprime_comm.trans hp.coprime_iff_not_dvd
  have hsplit : A = B + C := by
    funext j
    simp only [A, B, C, Pi.add_apply, Nat.coprime_mul_iff_right, hiff]
    by_cases hj : p ∣ j <;> simp [hj]
  have hCsum : ∑' j, C j = c * ∑' j, B j := by
    have hsupp : Function.support C ⊆ Set.range (p * ·) := by
      intro j hj
      simp only [Function.mem_support, C] at hj
      split_ifs at hj with h
      · obtain ⟨i, rfl⟩ := h; exact ⟨i, rfl⟩
      · exact absurd rfl hj
    rw [← (mul_right_injective₀ hp.ne_zero).tsum_eq hsupp, ← tsum_mul_left]
    congr 1; funext i
    simp only [C, A, B, dvd_mul_right, ite_true, Nat.coprime_mul_iff_left,
      Nat.coprime_mul_iff_right, hiff]
    by_cases hi : p ∣ i
    · simp [hsq i hi, hi]
    · simp only [hmul i hi, hi, not_false_eq_true]
      by_cases hc : i.Coprime D
      · rw [if_pos ⟨hcopD, hc⟩, if_pos ⟨trivial, hc⟩]
      · rw [if_neg (fun h => hc h.2), if_neg (fun h => hc h.2), mul_zero]
  unfold coprimeSum
  change ∑' j, A j = (1 + c) * ∑' j, B j
  rw [hsplit, show ∑' j, (B + C) j = ∑' j, (B j + C j) from rfl, hB.tsum_add hC, hCsum]; ring
variable {P : ℕ → Prop} [DecidablePred P]
lemma coprimeSum_hw_peel (hs : Summable (hw P)) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2)
    {D : ℕ} (hSD : ∀ p ∈ S, ¬ p ∣ D) :
    coprimeSum (hw P) D = (∏ p ∈ S, (1 - xw P p)) * coprimeSum (hw P) (D * ∏ p ∈ S, p) := by
  induction S using Finset.induction_on generalizing D with
  | empty => simp
  | insert p S hpS ih =>
    have hp := hS p (Finset.mem_insert_self p S)
    rw [ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
      (fun q hq => hSD q (Finset.mem_insert_of_mem hq))]
    have hpD' : ¬ p ∣ D * ∏ q ∈ S, q := by
      intro h
      rcases (Nat.Prime.dvd_mul hp.1).1 h with h | h
      · exact hSD p (Finset.mem_insert_self p S) h
      · obtain ⟨q, hq, hpq⟩ := (hp.1.prime.dvd_finsetProd_iff _).1 h
        have := (Nat.prime_dvd_prime_iff_eq hp.1 (hS q (Finset.mem_insert_of_mem hq)).1).1 hpq
        exact hpS (this ▸ hq)
    rw [coprimeSum_peel hs hp.1 hpD' (c := -xw P p) (fun j hj => hw_mul_prime hp.1 hp.2 hj)
      (fun j hj => hw_mul_prime_of_dvd hp.1 hj), Finset.prod_insert hpS, Finset.prod_insert hpS,
      show p * (D * ∏ q ∈ S, q) = D * (p * ∏ q ∈ S, q) by ring]
    ring
lemma tsum_dvd_hw (D : ℕ) (hD : D ≠ 0) :
    ∑' j, (if D ∣ j then hw P j else 0) = hw P D * coprimeSum (hw P) D := by
  have hsupp : Function.support (fun j => if D ∣ j then hw P j else 0) ⊆ Set.range (D * ·) := by
    intro j hj
    simp only [Function.mem_support] at hj
    split_ifs at hj with h
    · obtain ⟨i, rfl⟩ := h; exact ⟨i, rfl⟩
    · exact absurd rfl hj
  rw [← (mul_right_injective₀ hD).tsum_eq hsupp, coprimeSum, ← tsum_mul_left]
  congr 1; funext i
  simp only [dvd_mul_right, ite_true]
  by_cases hi : Nat.Coprime i D
  · rw [if_pos hi, hw_mul_of_coprime hi.symm]
  · rw [if_neg hi, hw_mul_of_not_coprime (fun h => hi h.symm), mul_zero]
lemma coprimeSum_hw_pos (hs : Summable (hw P)) {M : ℕ} (hM : ∀ p, p.Prime → P p → p ∣ M) :
    0 < coprimeSum (hw P) M := by
  have hlow : ∀ j, (if j = 1 then (1 : ℝ) else 0) - oddWeight j ≤
      if Nat.Coprime j M then hw P j else 0 := by
    intro j
    by_cases h1 : j = 1
    · subst h1; simp [hw_one, oddWeight]
    simp only [h1, ↓reduceIte, zero_sub]
    by_cases hgood : Nat.Coprime j M ∧ Odd j ∧ Squarefree j
    · obtain ⟨hc, ho, hsq⟩ := hgood
      rw [if_pos hc, hw_eq_prod ho hsq]
      have hw' : oddWeight j = ∏ p ∈ j.primeFactors, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
        simp [oddWeight, sqfreeWeight, ho, h1, hsq]
      have hx : ∀ p ∈ j.primeFactors, xw P p = ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
        intro p hp
        have hp' := Nat.mem_primeFactors.1 hp
        have hnP : ¬ P p := fun hP =>
          hp'.1.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hp'.2.1 hc)
            (hM p hp'.1 hP))
        simp [xw, hnP]
      have hprod : ∏ p ∈ j.primeFactors, -xw P p =
          ∏ p ∈ j.primeFactors, -((p : ℝ) * ((p : ℝ) - 1))⁻¹ :=
        Finset.prod_congr rfl fun p hp => by rw [hx p hp]
      have habs : |∏ p ∈ j.primeFactors, -((p : ℝ) * ((p : ℝ) - 1))⁻¹| =
          ∏ p ∈ j.primeFactors, ((p : ℝ) * ((p : ℝ) - 1))⁻¹ := by
        rw [Finset.abs_prod]
        exact Finset.prod_congr rfl fun p hp => by
          rw [abs_neg, abs_of_nonneg (inv_mul_pred_nonneg (Nat.prime_of_mem_primeFactors hp).one_le)]
      rw [hw', hprod]
      linarith [neg_abs_le (∏ p ∈ j.primeFactors, -((p : ℝ) * ((p : ℝ) - 1))⁻¹)]
    · have : (if Nat.Coprime j M then hw P j else 0) = 0 := by
        split_ifs with hc
        · unfold hw; rw [if_neg (fun h => hgood ⟨hc, h⟩)]
        · rfl
      rw [this]; linarith [oddWeight_nonneg j]
  have hs1 : Summable fun j : ℕ => (if j = 1 then (1 : ℝ) else 0) - oddWeight j :=
    (summable_of_ne_finset_zero (s := {1}) fun j hj => by
      rw [Finset.mem_singleton] at hj; simp [hj]).sub summable_oddWeight
  have hs2 := summable_coprime hs M
  have hle := hs1.tsum_le_tsum hlow hs2
  rw [Summable.tsum_sub (summable_of_ne_finset_zero (s := {1}) fun j hj => by
      rw [Finset.mem_singleton] at hj; simp [hj]) summable_oddWeight,
    tsum_ite_eq 1 (fun _ => (1 : ℝ))] at hle
  unfold coprimeSum
  linarith [tsum_oddWeight_lt_one]
end Peel
section Main
variable {P : ℕ → Prop} [DecidablePred P]
lemma dfactor_pos {D : ℕ} (hD : Squarefree D) (hodd : Odd D) (hD1 : D ≠ 1) :
    0 < ∏ p ∈ D.primeFactors, (1 - xw P p) - hw P D := by
  rw [hw_eq_prod hodd hD]
  have hp2 : ∀ p ∈ D.primeFactors, p.Prime ∧ p ≠ 2 := fun p hp =>
    ⟨Nat.prime_of_mem_primeFactors hp, by
      rintro rfl
      exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))⟩
  by_cases h : ∃ p ∈ D.primeFactors, p ≠ 3
  · have hlt : ∏ p ∈ D.primeFactors, xw P p < ∏ p ∈ D.primeFactors, (1 - xw P p) := by
      refine Finset.prod_lt_prod (fun p hp => xw_pos (hp2 p hp).1) (fun p hp => ?_) ?_
      · linarith [xw_le_half (P := P) (hp2 p hp).1 (hp2 p hp).2]
      · obtain ⟨p, hp, hp3⟩ := h
        exact ⟨p, hp, by linarith [xw_lt_half (P := P) (hp2 p hp).1 (hp2 p hp).2 hp3]⟩
    have habs : |∏ p ∈ D.primeFactors, -xw P p| = ∏ p ∈ D.primeFactors, xw P p := by
      rw [Finset.abs_prod]
      exact Finset.prod_congr rfl fun p hp => by rw [abs_neg, abs_of_pos (xw_pos (hp2 p hp).1)]
    linarith [le_abs_self (∏ p ∈ D.primeFactors, -xw P p)]
  · push Not at h
    have hne : D.primeFactors.Nonempty := Nat.nonempty_primeFactors.2 (by
      have := hD.ne_zero; omega)
    have h3 : D.primeFactors = {3} := by
      refine Finset.eq_singleton_iff_unique_mem.2 ⟨?_, h⟩
      obtain ⟨p, hp⟩ := hne
      exact h p hp ▸ hp
    rw [h3]; simp
open Classical in
lemma moebius_div_kummerDegree_eq_prod (ha0 : a ≠ 0) (hP2 : ¬ ∃ c : ℤ, c ^ 2 = a)
    {k : ℕ} (hk : Squarefree k) :
    (moebius k : ℝ) / kummerDegree a k =
      kummerEps a k * ∏ q ∈ k.primeFactors, -xw (fun q => ∃ c : ℤ, c ^ q = a) q := by
  set P : ℕ → Prop := fun q => ∃ c : ℤ, c ^ q = a with hP
  have hk0 : k ≠ 0 := hk.ne_zero
  have hM : (kummerM a k : ℝ) =
      kummerEps a k * ∏ q ∈ k.primeFactors, (if P q then (q : ℝ) else 1) := by
    unfold kummerM
    rw [Finset.prod_filter]
    push_cast
    by_cases h2 : 2 ∣ k
    · have h2m : 2 ∈ k.primeFactors := Nat.mem_primeFactors.2 ⟨Nat.prime_two, h2, hk0⟩
      rw [← Finset.mul_prod_erase _ _ h2m, ← Finset.mul_prod_erase _ _ h2m]
      have hB : (if P 2 then ((2 : ℕ) : ℝ) else 1) = 1 := if_neg hP2
      rw [hB, one_mul]
      unfold kummerEps
      simp only [↓reduceIte, h2, true_and]
      congr 1
      · split_ifs <;> simp
      · refine Finset.prod_congr rfl fun x hx => ?_
        have hx2 := Finset.ne_of_mem_erase hx
        simp only [hx2, ↓reduceIte, P]
    · rw [kummerEps_of_odd h2, Nat.cast_one, one_mul]
      refine Finset.prod_congr rfl fun x hx => ?_
      have hx2 : x ≠ 2 := by rintro rfl; exact h2 (Nat.dvd_of_mem_primeFactors hx)
      simp only [hx2, ↓reduceIte, P]
  have hdegR : (kummerDegree a k : ℝ) * kummerM a k = k * k.totient := by
    exact_mod_cast kummerDegree_mul_kummerM ha0 hk
  have hpos : (0 : ℝ) < k * k.totient := by
    have := Nat.pos_of_ne_zero hk0
    have := Nat.totient_pos.2 this
    positivity
  have hdeg0 : (kummerDegree a k : ℝ) ≠ 0 := by
    intro h; rw [h, zero_mul] at hdegR; linarith
  have hM0 : (kummerM a k : ℝ) ≠ 0 := by
    intro h; rw [h, mul_zero] at hdegR; linarith
  have hf : (moebius k : ℝ) / kummerDegree a k = moebius k * kummerM a k * sqfreeWeight k := by
    rw [sqfreeWeight_eq hk, ← hdegR]; field_simp
  have hμ : (moebius k : ℝ) = ∏ q ∈ k.primeFactors, (-1 : ℝ) := by
    rw [moebius_apply_of_squarefree hk, Finset.prod_const,
      ← (cardDistinctFactors_eq_cardFactors_iff_squarefree hk0).2 hk,
      cdf_eq_card]
    push_cast; ring
  have hw : sqfreeWeight k = ∏ q ∈ k.primeFactors, ((q : ℝ) * ((q : ℝ) - 1))⁻¹ := by
    simp [sqfreeWeight, hk]
  rw [hf, hμ, hM, hw, Finset.prod_congr rfl (fun q _ => show -xw P q =
    (-1) * (if P q then (q : ℝ) else 1) * ((q : ℝ) * ((q : ℝ) - 1))⁻¹ by unfold xw; ring),
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring
lemma prod_one_sub_xw_pos {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2) :
    0 < ∏ p ∈ S, (1 - xw P p) :=
  Finset.prod_pos fun p hp => by linarith [xw_le_half (P := P) (hS p hp).1 (hS p hp).2]
theorem kummerDensity_pos_of_not_isSquare (ha : ¬ IsSquare a) (ha' : a ≠ -1) :
    0 < kummerDensity a := by
  classical
  have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by simp⟩
  have ha1 : a ≠ 1 := by rintro rfl; exact ha ⟨1, by simp⟩
  obtain ⟨a₀, c, h₀, hac⟩ : ∃ a₀ c : ℤ, Squarefree a₀ ∧ a = a₀ * c ^ 2 := by
    obtain ⟨b, c, hbc, hb⟩ := Nat.sq_mul_squarefree a.natAbs
    rcases Int.natAbs_eq a with h | h
    · exact ⟨b, c, Int.squarefree_natCast.2 hb, by rw [h, ← hbc]; push_cast; ring⟩
    · exact ⟨-b, c, Int.squarefree_natAbs.1 (by simpa using hb), by rw [h, ← hbc]; push_cast; ring⟩
  have hc0 : c ≠ 0 := by rintro rfl; exact ha ⟨0, by simp [hac]⟩
  set P : ℕ → Prop := fun q => ∃ c : ℤ, c ^ q = a with hP
  have hP2 : ¬ ∃ c : ℤ, c ^ 2 = a := fun ⟨c, hc⟩ => ha ⟨c, by rw [← hc]; ring⟩
  have hPle : ∀ q, P q → q ≤ a.natAbs := fun q ⟨c, hc⟩ => le_natAbs_of_pow_eq c hc ha0 ha1 ha'
  set D : ℕ := a₀.natAbs with hD
  have hDsq : Squarefree D := Int.squarefree_natAbs.2 h₀
  have hDodd : a₀ % 4 = 1 → Odd D := fun h => by
    rw [hD, Int.natAbs_odd]; exact Int.odd_iff.2 (by omega)
  have hD0 : D ≠ 0 := hDsq.ne_zero
  set f : ℕ → ℝ := fun k => (moebius k : ℝ) / kummerDegree a k with hf_def
  have hf : Summable f := summable_moebius_div_kummerDegree_of_ne ha0 ha1 ha'
  have hform : ∀ k, Squarefree k → f k = kummerEps a k * ∏ q ∈ k.primeFactors, -xw P q :=
    fun k hk => moebius_div_kummerDegree_eq_prod ha0 hP2 hk
  have hf0 : ∀ k, ¬ Squarefree k → f k = 0 := fun k hk =>
    moebius_div_kummerDegree_of_not_squarefree hk
  have hodd_eq : ∀ j, Odd j → f j = hw P j := by
    intro j hj
    by_cases hsq : Squarefree j
    · rw [hform j hsq, kummerEps_of_odd (fun h => (Nat.not_even_iff_odd.2 hj)
        (even_iff_two_dvd.2 h)), hw_eq_prod hj hsq]
      simp
    · rw [hf0 j hsq]; simp [hw, hsq]
  have hs : Summable (hw P) := Summable.of_norm_bounded hf.norm fun j => by
    by_cases hj : Odd j
    · rw [hodd_eq j hj]
    · rw [hw_of_not_odd hj]; simp
  set g : ℕ → ℝ := fun j => if a₀ % 4 = 1 ∧ D ∣ j then 0 else hw P j with hg_def
  have hpair : ∀ j, f (2 * j) + (if Odd j then f j else 0) = g j / 2 := by
    intro j
    by_cases hgood : Odd j ∧ Squarefree j
    · obtain ⟨hj, hsq⟩ := hgood
      have h2sq : Squarefree (2 * j) := squarefree_two_mul hj hsq
      rw [if_pos hj, hodd_eq j hj]
      have h2j : (2 : ℕ) ∉ j.primeFactors := fun h =>
        (Nat.not_even_iff_odd.2 hj) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors h))
      have hf2 : f (2 * j) = kummerEps a (2 * j) * (-(1 / 2)) * hw P j := by
        rw [hform _ h2sq, Nat.primeFactors_mul two_ne_zero hsq.ne_zero,
          Nat.prime_two.primeFactors, Finset.singleton_union, Finset.prod_insert h2j,
          xw_two hP2, hw_eq_prod hj hsq]
        ring
      have hiff : (2 ∣ 2 * j ∧ ∃ β : CyclotomicField (2 * j) ℚ, β ^ 2 = a) ↔
          (a₀ % 4 = 1 ∧ D ∣ j) := by
        rw [exists_sq_cyclotomicField_iff ha h₀ hac h2sq]
        constructor
        · rintro ⟨-, h4, hdvd⟩
          exact ⟨h4, (Nat.Coprime.dvd_mul_left (Nat.coprime_two_right.2 (hDodd h4))).1 hdvd⟩
        · rintro ⟨h4, hdvd⟩; exact ⟨dvd_mul_right 2 j, h4, hdvd.mul_left 2⟩
      have hε : kummerEps a (2 * j) = if a₀ % 4 = 1 ∧ D ∣ j then 2 else 1 := by
        unfold kummerEps
        by_cases h : a₀ % 4 = 1 ∧ D ∣ j
        · rw [if_pos (hiff.2 h), if_pos h]
        · rw [if_neg (fun h' => h (hiff.1 h')), if_neg h]
      rw [hf2, hε]
      simp only [g]
      split_ifs <;> push_cast <;> ring
    · have h2 : ¬ Squarefree (2 * j) := by
        intro h
        by_cases hj : Odd j
        · exact hgood ⟨hj, h.squarefree_of_dvd (dvd_mul_left j 2)⟩
        · exact not_squarefree_two_mul_of_even (Nat.not_odd_iff_even.1 hj) h
      have h1 : (if Odd j then f j else 0) = 0 := by
        split_ifs with hj
        · exact hf0 j fun h => hgood ⟨hj, h⟩
        · rfl
      have hg0 : g j = 0 := by
        simp only [g]
        split_ifs
        · rfl
        · unfold hw; rw [if_neg hgood]
      rw [hf0 _ h2, h1, hg0]; ring
  have hs_e : Summable fun j => f (2 * j) :=
    hf.comp_injective (mul_right_injective₀ two_ne_zero)
  have hs_o : Summable fun j => f (2 * j + 1) :=
    hf.comp_injective fun x y h => by simpa using h
  set ind : ℕ → ℝ := fun j => if Odd j then f j else 0
  have hs_i : Summable ind :=
    Summable.of_norm_bounded hf.norm fun j => by
      simp only [ind]; split_ifs <;> simp
  have hind : ∑' j, ind j = ∑' j, f (2 * j + 1) := by
    rw [← tsum_even_add_odd (hs_i.comp_injective (mul_right_injective₀ two_ne_zero))
      (hs_i.comp_injective fun x y h => by simpa using h)]
    have he : ∀ j, ind (2 * j) = 0 := fun j => by simp [ind]
    have ho : ∀ j, ind (2 * j + 1) = f (2 * j + 1) := fun j => by simp [ind]
    simp only [he, ho, tsum_zero, zero_add]
  have hsum : kummerDensity a = ∑' j, g j / 2 := by
    rw [kummerDensity, ← hf_def, ← tsum_even_add_odd hs_e hs_o, ← hind, ← hs_e.tsum_add hs_i]
    exact tsum_congr hpair
  rw [hsum, tsum_div_const]
  refine div_pos ?_ two_pos
  set H : Finset ℕ := (Finset.range (a.natAbs + 1)).filter fun q => q.Prime ∧ q ≠ 2 ∧ P q
  have hH : ∀ p ∈ H, p.Prime ∧ p ≠ 2 := fun p hp => by
    have := (Finset.mem_filter.1 hp).2; exact ⟨this.1, this.2.1⟩
  have hPmem : ∀ p, p.Prime → P p → p ∈ H := by
    intro p hp hPp
    have hp2 : p ≠ 2 := by rintro rfl; exact hP2 hPp
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.lt_succ_of_le (hPle p hPp)), hp, hp2, hPp⟩
  have hcs1 : ∑' j, hw P j = coprimeSum (hw P) 1 := by
    unfold coprimeSum; simp
  by_cases hE : a₀ % 4 = 1
  · have hD1 : D ≠ 1 := by
      intro h1
      rcases Int.natAbs_eq a₀ with h | h <;> rw [← hD, h1] at h
      · exact ha ⟨c, by rw [hac, h]; ring⟩
      · rw [h] at hE; norm_num at hE
    have hDo := hDodd hE
    have hpfD : ∀ p ∈ D.primeFactors, p.Prime ∧ p ≠ 2 := fun p hp =>
      ⟨Nat.prime_of_mem_primeFactors hp, by
        rintro rfl
        exact (Nat.not_even_iff_odd.2 hDo) (even_iff_two_dvd.2 (Nat.dvd_of_mem_primeFactors hp))⟩
    have hgeq : g = fun j => hw P j - if D ∣ j then hw P j else 0 := by
      funext j
      simp only [g, hE, true_and]
      split_ifs <;> ring
    have hsD : Summable fun j => if D ∣ j then hw P j else 0 :=
      Summable.of_norm_bounded hs.norm fun j => by split_ifs <;> simp
    have h1 : coprimeSum (hw P) 1 =
        (∏ p ∈ D.primeFactors, (1 - xw P p)) * coprimeSum (hw P) D := by
      rw [coprimeSum_hw_peel hs D.primeFactors hpfD (D := 1) (fun p hp h =>
        (Nat.prime_of_mem_primeFactors hp).one_lt.ne' (Nat.dvd_one.1 h)), one_mul,
        Nat.prod_primeFactors_of_squarefree hDsq]
    set S := H \ D.primeFactors
    have hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2 := fun p hp => hH p (Finset.mem_sdiff.1 hp).1
    have hSD : ∀ p ∈ S, ¬ p ∣ D := fun p hp h =>
      (Finset.mem_sdiff.1 hp).2 (Nat.mem_primeFactors.2 ⟨(hS p hp).1, h, hD0⟩)
    have h2 := coprimeSum_hw_peel hs S hS hSD
    have hpos : 0 < coprimeSum (hw P) (D * ∏ p ∈ S, p) := by
      refine coprimeSum_hw_pos hs fun p hp hPp => ?_
      by_cases hpD : p ∈ D.primeFactors
      · exact (Nat.dvd_of_mem_primeFactors hpD).trans (dvd_mul_right _ _)
      · exact (Finset.dvd_prod_of_mem (fun q : ℕ => q)
          (Finset.mem_sdiff.2 ⟨hPmem p hp hPp, hpD⟩)).trans (dvd_mul_left _ _)
    rw [hgeq]
    show 0 < ∑' j, (hw P j - if D ∣ j then hw P j else 0)
    rw [hs.tsum_sub hsD, tsum_dvd_hw D hD0, hcs1, h1, h2]
    have hfac := dfactor_pos (P := P) hDsq hDo hD1
    have hSpos := prod_one_sub_xw_pos (P := P) hS
    have heq : (∏ p ∈ D.primeFactors, (1 - xw P p)) *
          ((∏ p ∈ S, (1 - xw P p)) * coprimeSum (hw P) (D * ∏ p ∈ S, p)) -
        hw P D * ((∏ p ∈ S, (1 - xw P p)) * coprimeSum (hw P) (D * ∏ p ∈ S, p)) =
        (∏ p ∈ D.primeFactors, (1 - xw P p) - hw P D) *
          ((∏ p ∈ S, (1 - xw P p)) * coprimeSum (hw P) (D * ∏ p ∈ S, p)) := by ring
    rw [heq]
    exact mul_pos hfac (mul_pos hSpos hpos)
  · have hgeq : g = hw P := by
      funext j; simp only [g, hE, false_and, ↓reduceIte]
    rw [hgeq, hcs1, coprimeSum_hw_peel hs H hH (D := 1) (fun p hp h =>
      (hH p hp).1.one_lt.ne' (Nat.dvd_one.1 h)), one_mul]
    refine mul_pos (prod_one_sub_xw_pos hH) (coprimeSum_hw_pos hs fun p hp hPp => ?_)
    exact Finset.dvd_prod_of_mem (fun q : ℕ => q) (hPmem p hp hPp)
end Main
end Artin.Kummer
end

theorem OMA.solution : OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1.H4 := by
  intro a ha ha'
  exact Artin.Kummer.kummerDensity_pos_of_not_isSquare ha ha'
