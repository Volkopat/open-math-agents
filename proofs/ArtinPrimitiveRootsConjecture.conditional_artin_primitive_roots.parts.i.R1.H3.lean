import OMAReductions.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1

-- Step ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.parts.i.R1.H3: hypothesis H3 of reduction ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.parts.i.R1
-- Credit: @senamakel
-- Kummer degrees: K_k = Q(zeta, alpha) with [Q(zeta) : Q] = phi(k) and d = [K_k : Q(zeta)] dividing k;
-- a is an (k/d)-th power in Q(zeta), and for odd primes q an integer q-th power in an abelian field
-- is a q-th power in Z, so k/d is squarefree with prime factors at most |a|, giving c = 4^|a|.



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
theorem exists_mul_totient_le_kummerDegree (ha0 : a ≠ 0) (ha1 : a ≠ 1) (ha2 : a ≠ -1) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, Squarefree k → 1 ≤ k →
      (k * k.totient : ℝ) ≤ c * kummerDegree a k :=
  ⟨4 ^ a.natAbs, by positivity, fun k hk _ => by
    exact_mod_cast mul_totient_le_kummerDegree ha0 ha1 ha2 hk⟩
set_option synthInstance.maxHeartbeats 400000 in
def NotPerfectPower (a : ℤ) : Prop := ∀ (b : ℤ) (n : ℕ), 2 ≤ n → b ^ n ≠ a
set_option synthInstance.maxHeartbeats 400000 in
lemma NotPerfectPower.ne_zero (h : NotPerfectPower a) : a ≠ 0 := by
  rintro rfl; exact h 0 2 le_rfl (by simp)
section General
variable {ζ α : KField a k}
end General
end Artin.Kummer
end


theorem OMA.solution : OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1.H3 := by
  intro a h0 h1 h2
  obtain ⟨c, hc, h⟩ := Artin.Kummer.exists_mul_totient_le_kummerDegree h0 h1 h2
  exact ⟨c, hc, fun k hk hk0 => h k hk hk0⟩
