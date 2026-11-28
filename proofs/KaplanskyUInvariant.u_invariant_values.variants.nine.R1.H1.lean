import OMAReductions.R_KaplanskyUInvariant_u_invariant_values_variants_nine_R1
import Mathlib

/-!
# Proof of `KaplanskyUInvariant.u_invariant_values.variants.nine.R1.H1`

We construct a countable field `K` of characteristic `0` carrying an essential 9-dimensional
diagonal quadratic form `a = <t_0, ..., t_8>` (anisotropic, not similar to a subform of any
4-fold Pfister form, and whose even Clifford algebra is not isomorphic to `M_8(Q)` for any
quaternion algebra `Q = (p, q)_K`).

Architecture:
1. Work inside the Hahn series field `H := HahnSeries (Lex (Fin 9 -> Int)) (AlgebraicClosure Rat)`,
   where every nonzero element of order `0` is a square via `AlgebraicClosure.isAlgClosed` and
   Mathlib's binomial power `(1 + eps)^(1/2)` in `HahnSeries.Binomial`.
2. Build a countable subfield `K` of `H` containing `t_i = single (e_i) 1` (`i : Fin 9`) and
   closed under taking square roots of nonzero order-`0` elements, so every nonzero `x : K` with
   even valuation `par (ord x) = 0` is a square in `K` (including `-1`).
3. Distinct mod-2 valuations yield a general no-cancellation lemma proving anisotropy of `a`.
4. Non-similarity to a subform of any 4-fold Pfister form `<<u_0, u_1, u_2, u_3>>`:
   - If the mod-2 valuations of `u_0, ..., u_3` are `ZMod 2`-dependent, pair up coordinates along
     the dependency to exhibit an 8-dimensional totally isotropic subspace inside `K^16`,
     intersecting the 9-dimensional anisotropic image of `T` nontrivially.
   - If they are `ZMod 2`-independent, no cancellation occurs in `<<u_0, u_1, u_2, u_3>>`,
     forcing all 9 values `par(c) + e_i` into a 4-dimensional `ZMod 2`-subspace, impossible since
     the differences `e_i - e_8` (`i < 8`) span an 8-dimensional subspace.
5. Non-isomorphism of `CliffordAlgebra.even` with `M_8(Q)`:
   - Construct the explicit 512-dimensional twisted Clifford algebra `TwistedCl a` on `(Fin 9 -> Bool) -> K`
     with 256-dimensional even subalgebra `EvenCl a`.
   - Prove `TwistedCl a` has no zero divisors via the doubled valuation `2 * ord(f s) + 1_s`
     whose mod-2 parity recovers `s` uniquely.
   - Lift `CliffordAlgebra.even` onto `EvenCl a` via `CliffordAlgebra.even.lift`; surjectivity onto
     all 256 even basis masks plus `finrank K (M_8(Q)) = 256 = finrank K (EvenCl a)` forces any
     isomorphism to inject `M_8(Q)` into `EvenCl a`, contradicting `E_{0,0} * E_{1,1} = 0`.
-/

namespace KaplanskyNineH1Proof

open scoped BigOperators

/- ### Section 1: Ambient Hahn Series Field and Square Roots of Units -/

private abbrev Γ := Lex (Fin 9 → ℤ)
private abbrev k := AlgebraicClosure ℚ
private abbrev H := HahnSeries Γ k

private def basisVec (i : Fin 9) : Γ := toLex (Pi.single i (1 : ℤ))

private noncomputable def genT (i : Fin 9) : H :=
  HahnSeries.single (basisVec i) (1 : k)

private lemma genT_ne_zero (i : Fin 9) : genT i ≠ 0 := by
  simp [genT]

private lemma order_genT (i : Fin 9) : (genT i).order = basisVec i := by
  simp [genT, HahnSeries.order_single]

private lemma zmod2_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private lemma hahn_pow_one (x : HahnSeries.orderTopSubOnePos Γ k) : x ^ (1 : k) = x := by
  apply SetLike.coe_eq_coe.mp
  apply Units.val_inj.mp
  change (HahnSeries.SummableFamily.binomialFamily (x.1 : H) (1 : k)).hsum = (x.1 : H)
  ext g
  rw [HahnSeries.SummableFamily.coeff_hsum]
  have hsupp : ∀ n : ℕ, n ≠ 0 → n ≠ 1 →
      ((HahnSeries.SummableFamily.binomialFamily (x.1 : H) (1 : k) n).coeff g) = 0 := by
    intro n hn0 hn1
    rw [HahnSeries.SummableFamily.binomialFamily_apply x.2]
    have hch : Ring.choose (1 : k) n = 0 := by
      have h1 : (1 : k) = ((1 : ℕ) : k) := by simp
      rw [h1, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega : 1 < n), Nat.cast_zero]
    simp [hch]
  rw [finsum_eq_sum_of_support_subset _ (s := ({0, 1} : Finset ℕ))]
  · simp only [Finset.sum_pair (by decide : (0 : ℕ) ≠ 1)]
    rw [HahnSeries.SummableFamily.binomialFamily_apply x.2,
      HahnSeries.SummableFamily.binomialFamily_apply x.2]
    simp
  · intro n hn
    simp only [Function.mem_support, ne_eq] at hn
    by_contra hnot
    simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
    exact hn (hsupp n hnot.1 hnot.2)

private lemma exists_sqrt_of_order_zero {x : H} (hx : x ≠ 0) (hord : x.order = 0) :
    ∃ y : H, y ^ 2 = x := by
  have hlc : x.leadingCoeff ≠ 0 := HahnSeries.leadingCoeff_ne_zero.mpr hx
  obtain ⟨d, hd⟩ := IsAlgClosed.exists_pow_nat_eq x.leadingCoeff (by norm_num : 0 < 2)
  have hd0 : d ≠ 0 := by
    intro h0; rw [h0, zero_pow (by norm_num)] at hd; exact hlc hd.symm
  have hC_ne : (HahnSeries.C (d⁻¹ ^ 2) : H) ≠ 0 := by
    intro h
    have h0 := congrArg (fun z : H => z.coeff 0) h
    rw [HahnSeries.C_apply, HahnSeries.coeff_single_same, HahnSeries.coeff_zero] at h0
    exact pow_ne_zero 2 (inv_ne_zero hd0) h0
  let u : H := HahnSeries.C (d⁻¹ ^ 2) * x
  have hu_ne : u ≠ 0 := mul_ne_zero hC_ne hx
  have hu_ord : u.order = 0 := by
    rw [HahnSeries.order_mul hC_ne hx, HahnSeries.order_C, hord, add_zero]
  have hu_lc : u.leadingCoeff = 1 := by
    rw [HahnSeries.leadingCoeff_eq, hu_ord]
    have hcoeff : u.coeff 0 = (d⁻¹ ^ 2) * x.coeff 0 := by
      simp only [u, HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
    rw [hcoeff, ← hord, ← HahnSeries.leadingCoeff_eq, ← hd]
    field_simp [hd0]
  have hu_pos : (0 : WithTop Γ) < (u - 1).orderTop := by
    rw [HahnSeries.orderTop_self_sub_one_pos_iff]
    refine ⟨?_, hu_lc⟩
    rw [← HahnSeries.order_eq_orderTop_of_ne_zero hu_ne, hu_ord]
    rfl
  let uPos : HahnSeries.orderTopSubOnePos Γ k := HahnSeries.toOrderTopSubOnePos hu_pos
  let rPos : HahnSeries.orderTopSubOnePos Γ k := uPos ^ ((1 : k) / 2)
  have hr_sq : rPos * rPos = uPos := by
    rw [← HahnSeries.pow_add]
    have hhalf : (1 : k) / 2 + (1 : k) / 2 = 1 := by ring
    rw [hhalf, hahn_pow_one]
  have hr_val : ((rPos.1 : H) ^ 2) = u := by
    have h1 := congrArg (fun z : HahnSeries.orderTopSubOnePos Γ k => (z.1 : H)) hr_sq
    simpa [sq, uPos] using h1
  refine ⟨HahnSeries.C d * (rPos.1 : H), ?_⟩
  rw [mul_pow, hr_val]
  have hC : (HahnSeries.C d : H) ^ 2 * HahnSeries.C (d⁻¹ ^ 2) = 1 := by
    rw [← map_pow, ← map_mul]
    have : d ^ 2 * d⁻¹ ^ 2 = 1 := by field_simp [hd0]
    rw [this, map_one]
  calc (HahnSeries.C d : H) ^ 2 * u
      = ((HahnSeries.C d : H) ^ 2 * HahnSeries.C (d⁻¹ ^ 2)) * x := by simp only [u, mul_assoc]
    _ = x := by rw [hC, one_mul]

open Classical in
private noncomputable def sqrtUnit (x : H) : H :=
  if h : x ≠ 0 ∧ x.order = 0 then Classical.choose (exists_sqrt_of_order_zero h.1 h.2) else 0

private lemma sqrtUnit_sq {x : H} (hx : x ≠ 0) (hord : x.order = 0) :
    (sqrtUnit x) ^ 2 = x := by
  have h : x ≠ 0 ∧ x.order = 0 := ⟨hx, hord⟩
  simp only [sqrtUnit, dif_pos h]
  exact Classical.choose_spec (exists_sqrt_of_order_zero hx hord)

/- ### Section 2: Countable Square-Root-Closed Subfield `K` of `H` -/

private noncomputable def stepSet (A : Set H) : Set H :=
  A ∪ ({0, 1} : Set H) ∪
    ((fun p : H × H => p.1 + p.2) '' (A ×ˢ A)) ∪
    ((fun x : H => -x) '' A) ∪
    ((fun p : H × H => p.1 * p.2) '' (A ×ˢ A)) ∪
    ((fun x : H => x⁻¹) '' A) ∪
    (sqrtUnit '' A)

private noncomputable def stageSet : ℕ → Set H
  | 0 => Set.range genT
  | n + 1 => stepSet (stageSet n)

private lemma stageSet_mono_succ (n : ℕ) : stageSet n ⊆ stageSet (n + 1) := by
  intro x hx
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl hx)))))

private lemma stageSet_mono {m n : ℕ} (h : m ≤ n) : stageSet m ⊆ stageSet n := by
  induction h with
  | refl => exact Set.Subset.rfl
  | step _ ih => exact ih.trans (stageSet_mono_succ _)

private lemma stageSet_countable (n : ℕ) : (stageSet n).Countable := by
  induction n with
  | zero => exact Set.countable_range genT
  | succ n ih =>
    have hprod : (stageSet n ×ˢ stageSet n).Countable := ih.prod ih
    exact (((((ih.union (Set.to_countable _)).union (hprod.image _)).union (ih.image _)).union
      (hprod.image _)).union (ih.image _)).union (ih.image _)

private def KCarrier : Set H := ⋃ n : ℕ, stageSet n

private lemma KCarrier_countable : KCarrier.Countable :=
  Set.countable_iUnion stageSet_countable

private noncomputable def KSub : Subfield H where
  carrier := KCarrier
  zero_mem' := Set.mem_iUnion.mpr ⟨1, Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inl rfl))))))⟩
  one_mem' := Set.mem_iUnion.mpr ⟨1, Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr (Or.inr rfl))))))⟩
  add_mem' := by
    rintro x y hx hy
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨max m n + 1, ?_⟩
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(x, y), ⟨stageSet_mono (le_max_left _ _) hm,
      stageSet_mono (le_max_right _ _) hn⟩, rfl⟩))))
  neg_mem' := by
    rintro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n + 1, Or.inl (Or.inl (Or.inl (Or.inr ⟨x, hn, rfl⟩)))⟩
  mul_mem' := by
    rintro x y hx hy
    obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
    refine Set.mem_iUnion.mpr ⟨max m n + 1, ?_⟩
    exact Or.inl (Or.inl (Or.inr ⟨(x, y), ⟨stageSet_mono (le_max_left _ _) hm,
      stageSet_mono (le_max_right _ _) hn⟩, rfl⟩))
  inv_mem' := by
    rintro x hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨n + 1, Or.inl (Or.inr ⟨x, hn, rfl⟩)⟩

private structure K where
  toSub : ↥KSub

private lemma K.ext {x y : K} (h : x.toSub = y.toSub) : x = y := by
  cases x; cases y; cases h; rfl

private def K.equivSub : K ≃ ↥KSub where
  toFun := K.toSub
  invFun := K.mk
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable instance : Field K := K.equivSub.field

private noncomputable def K.toH : K →+* H where
  toFun x := (x.toSub : H)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

private lemma K.toH_injective : Function.Injective K.toH := by
  intro x y h
  exact K.ext (Subtype.ext h)

private lemma K.toH_ne_zero {x : K} (hx : x ≠ 0) : K.toH x ≠ 0 := by
  intro h
  exact hx (K.toH_injective (h.trans (map_zero K.toH).symm))

private lemma sqrtUnit_mem_K {x : H} (hx : x ∈ KSub) : sqrtUnit x ∈ KSub := by
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
  exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr ⟨x, hn, rfl⟩⟩

private noncomputable def aK (i : Fin 9) : K :=
  ⟨⟨genT i, Set.mem_iUnion.mpr ⟨0, Set.mem_range_self i⟩⟩⟩

private lemma aK_ne_zero (i : Fin 9) : aK i ≠ 0 := by
  intro h
  exact genT_ne_zero i (congrArg K.toH h)

private instance : Countable K := by
  have : Countable ↥KSub := KCarrier_countable.to_subtype
  exact Countable.of_equiv ↥KSub K.equivSub.symm

private instance : NeZero (2 : K) := by
  refine ⟨fun h => ?_⟩
  have h2 : (2 : H) = 0 := by
    rw [← map_ofNat K.toH 2, h, map_zero]
  have h3 := congrArg (fun z : H => z.coeff 0) h2
  have h2eq : (2 : H) = HahnSeries.C (2 : k) := by rw [map_ofNat]
  rw [h2eq, HahnSeries.C_apply, HahnSeries.coeff_single_same, HahnSeries.coeff_zero] at h3
  exact (two_ne_zero : (2 : k) ≠ 0) h3

/- ### Section 3: Valuation, Parity Map, No-Cancellation, and Squares in `K` -/

private noncomputable def ordK (x : K) : Γ := (K.toH x).order

private def par (g : Γ) : Fin 9 → ZMod 2 := fun i => (ofLex g i : ZMod 2)

private lemma par_zero : par 0 = 0 := by
  ext i
  change ((0 : ℤ) : ZMod 2) = 0
  simp

private lemma par_add (g₁ g₂ : Γ) : par (g₁ + g₂) = par g₁ + par g₂ := by
  ext i
  change ((ofLex g₁ i + ofLex g₂ i : ℤ) : ZMod 2) = (ofLex g₁ i : ZMod 2) + (ofLex g₂ i : ZMod 2)
  push_cast
  rfl

private lemma par_neg (g : Γ) : par (-g) = par g := by
  ext i
  simp only [par, ofLex_neg, Pi.neg_apply, Int.cast_neg]
  exact CharTwo.neg_eq _

private lemma par_two_smul (g : Γ) : par (2 • g) = 0 := by
  ext i
  change (((2 : ℤ) * ofLex g i : ℤ) : ZMod 2) = 0
  rw [Int.cast_mul]
  have h2 : ((2 : ℤ) : ZMod 2) = 0 := by decide
  rw [h2, zero_mul]

private lemma ofLex_finset_sum {ι : Type*} (s : Finset ι) (f : ι → Γ) :
    ofLex (∑ i ∈ s, f i) = ∑ i ∈ s, ofLex (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    change ofLex (f a) + ofLex (∑ i ∈ s, f i) = ofLex (f a) + ∑ i ∈ s, ofLex (f i)
    rw [ih]

private lemma ordK_one : ordK (1 : K) = 0 := by
  rw [ordK, map_one, HahnSeries.order_one]

private lemma ordK_neg_one : ordK (-1 : K) = 0 := by
  rw [ordK, map_neg, map_one, HahnSeries.order_neg, HahnSeries.order_one]

private lemma ordK_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordK (x * y) = ordK x + ordK y := by
  rw [ordK, map_mul]
  exact HahnSeries.order_mul (K.toH_ne_zero hx) (K.toH_ne_zero hy)

private lemma ordK_inv {x : K} (hx : x ≠ 0) : ordK x⁻¹ = -ordK x := by
  have h1 : ordK (x * x⁻¹) = ordK x + ordK x⁻¹ := ordK_mul hx (inv_ne_zero hx)
  rw [mul_inv_cancel₀ hx, ordK_one] at h1
  exact eq_neg_of_add_eq_zero_right h1.symm

private lemma ordK_div {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    ordK (x / y) = ordK x - ordK y := by
  rw [div_eq_mul_inv, ordK_mul hx (inv_ne_zero hy), ordK_inv hy, sub_eq_add_neg]

private lemma ordK_pow {x : K} (hx : x ≠ 0) (n : ℕ) : ordK (x ^ n) = n • ordK x := by
  induction n with
  | zero => rw [pow_zero, ordK_one, zero_nsmul]
  | succ n ih =>
    rw [pow_succ, ordK_mul (pow_ne_zero n hx) hx, ih, succ_nsmul]

private lemma ordK_zpow {x : K} (hx : x ≠ 0) (m : ℤ) : ordK (x ^ m) = m • ordK x := by
  cases m with
  | ofNat n => simpa using ordK_pow hx n
  | negSucc n =>
    rw [zpow_negSucc, ordK_inv (pow_ne_zero _ hx), ordK_pow hx (n + 1)]
    exact (negSucc_zsmul (ordK x) n).symm

private lemma ordK_prod {ι : Type*} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, f i ≠ 0) :
    ordK (∏ i ∈ s, f i) = ∑ i ∈ s, ordK (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, ordK_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    have ha0 : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
    have hs0 : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    rw [ordK_mul ha0 (Finset.prod_ne_zero_iff.mpr hs0), ih hs0]

private lemma ordK_aK (i : Fin 9) : ordK (aK i) = basisVec i := order_genT i

private lemma par_aK (i : Fin 9) : par (ordK (aK i)) = Pi.single i (1 : ZMod 2) := by
  ext j
  rw [ordK_aK]
  by_cases hij : j = i
  · subst hij; simp [par, basisVec]
  · simp [par, basisVec, hij]

private lemma par_mul {x y : K} (hx : x ≠ 0) (hy : y ≠ 0) :
    par (ordK (x * y)) = par (ordK x) + par (ordK y) := by
  rw [ordK_mul hx hy, par_add]

private lemma par_sq {x : K} (hx : x ≠ 0) : par (ordK (x ^ 2)) = 0 := by
  rw [ordK_pow hx 2, par_two_smul]

private lemma exists_sq_of_par_zero {x : K} (hx : x ≠ 0) (hpar : par (ordK x) = 0) :
    ∃ y : K, y ^ 2 = x := by
  let g : Fin 9 → ℤ := fun i => ofLex (ordK x) i / 2
  have hg2 : ∀ i : Fin 9, 2 * g i = ofLex (ordK x) i := by
    intro i
    have h0 : ((ofLex (ordK x) i : ℤ) : ZMod 2) = 0 := congrFun hpar i
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
    exact Int.mul_ediv_cancel' h0
  let m : K := ∏ i : Fin 9, (aK i) ^ (g i)
  have hm0 : m ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => zpow_ne_zero _ (aK_ne_zero i)
  have hm_ord : ordK m = toLex g := by
    rw [ordK_prod Finset.univ _ (fun i _ => zpow_ne_zero _ (aK_ne_zero i))]
    apply ofLex.injective
    ext j
    rw [ofLex_finset_sum, Finset.sum_apply, ofLex_toLex]
    have hterm : ∀ i : Fin 9, ofLex (ordK ((aK i) ^ (g i))) j = if j = i then g i else 0 := by
      intro i
      rw [ordK_zpow (aK_ne_zero i), ordK_aK]
      change g i * (Pi.single (M := fun _ => ℤ) i (1 : ℤ) j) = if j = i then g i else 0
      by_cases hji : j = i
      · subst hji; simp
      · simp [hji]
    simp [hterm]
  have hm2_ord : ordK (m ^ 2) = ordK x := by
    rw [ordK_pow hm0 2, hm_ord]
    apply ofLex.injective
    ext i
    change 2 * g i = ofLex (ordK x) i
    exact hg2 i
  let u : K := x / m ^ 2
  have hu0 : u ≠ 0 := div_ne_zero hx (pow_ne_zero 2 hm0)
  have hu_ord : (K.toH u).order = 0 := by
    change ordK u = 0
    rw [ordK_div hx (pow_ne_zero 2 hm0), hm2_ord, sub_self]
  let w : K := ⟨⟨sqrtUnit (K.toH u), sqrtUnit_mem_K u.toSub.2⟩⟩
  have hw_sq : w ^ 2 = u := by
    apply K.toH_injective
    rw [map_pow]
    exact sqrtUnit_sq (K.toH_ne_zero hu0) hu_ord
  refine ⟨m * w, ?_⟩
  rw [mul_pow, hw_sq, mul_div_cancel₀ _ (pow_ne_zero 2 hm0)]

private lemma exists_sqrt_neg_one : ∃ I : K, I ^ 2 = -1 := by
  have hne : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  exact exists_sq_of_par_zero hne (by rw [ordK_neg_one, par_zero])

private lemma sum_ne_zero_and_ord_of_inj_ord {ι : Type*} (s : Finset ι) (f : ι → K)
    (hne : ∃ i ∈ s, f i ≠ 0)
    (hinj : ∀ i ∈ s, ∀ j ∈ s, f i ≠ 0 → f j ≠ 0 → ordK (f i) = ordK (f j) → i = j) :
    (∑ i ∈ s, f i) ≠ 0 ∧ ∃ i₀ ∈ s, f i₀ ≠ 0 ∧ ordK (∑ i ∈ s, f i) = ordK (f i₀) := by
  classical
  let s' := s.filter (fun i => f i ≠ 0)
  have hs' : s'.Nonempty := by
    obtain ⟨i, hi, hfi⟩ := hne
    exact ⟨i, Finset.mem_filter.mpr ⟨hi, hfi⟩⟩
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image s' (fun i => ordK (f i)) hs'
  have hi₀_s : i₀ ∈ s := (Finset.mem_filter.mp hi₀).1
  have hfi₀ : f i₀ ≠ 0 := (Finset.mem_filter.mp hi₀).2
  have hsum_coe : K.toH (∑ i ∈ s, f i) = ∑ i ∈ s, K.toH (f i) := map_sum K.toH f s
  have hcoeff_i₀ : (K.toH (∑ i ∈ s, f i)).coeff (ordK (f i₀)) = (K.toH (f i₀)).leadingCoeff := by
    rw [hsum_coe, HahnSeries.coeff_sum]
    rw [Finset.sum_eq_single i₀]
    · exact (HahnSeries.leadingCoeff_eq (x := K.toH (f i₀))).symm
    · intro j hjs hji
      by_cases hfj : f j = 0
      · simp [hfj]
      · have hj' : j ∈ s' := Finset.mem_filter.mpr ⟨hjs, hfj⟩
        have hle : ordK (f i₀) ≤ ordK (f j) := hmin j hj'
        have hne_ord : ordK (f i₀) ≠ ordK (f j) := fun heq =>
          hji (hinj i₀ hi₀_s j hjs hfi₀ hfj heq).symm
        have hlt : ordK (f i₀) < ordK (f j) := lt_of_le_of_ne hle hne_ord
        exact HahnSeries.coeff_eq_zero_of_lt_order hlt
    · intro hnot; exact absurd hi₀_s hnot
  have hsum_ne : (∑ i ∈ s, f i) ≠ 0 := by
    intro h0
    have hcoeff0 : (K.toH (∑ i ∈ s, f i)).coeff (ordK (f i₀)) = 0 := by rw [h0, map_zero]; simp
    rw [hcoeff_i₀] at hcoeff0
    exact (HahnSeries.leadingCoeff_ne_zero.mpr (K.toH_ne_zero hfi₀)) hcoeff0
  have hord_eq : ordK (∑ i ∈ s, f i) = ordK (f i₀) := by
    apply le_antisymm
    · exact HahnSeries.order_le_of_coeff_ne_zero (by
        rw [hcoeff_i₀]
        exact HahnSeries.leadingCoeff_ne_zero.mpr (K.toH_ne_zero hfi₀))
    · by_contra hlt
      push Not at hlt
      have hlc_ne : (K.toH (∑ i ∈ s, f i)).coeff (ordK (∑ i ∈ s, f i)) ≠ 0 := by
        dsimp only [ordK]
        rw [← HahnSeries.leadingCoeff_eq]
        exact HahnSeries.leadingCoeff_ne_zero.mpr (K.toH_ne_zero hsum_ne)
      have hzero : (K.toH (∑ i ∈ s, f i)).coeff (ordK (∑ i ∈ s, f i)) = 0 := by
        rw [hsum_coe, HahnSeries.coeff_sum]
        refine Finset.sum_eq_zero fun j hjs => ?_
        by_cases hfj : f j = 0
        · simp [hfj]
        · have hj' : j ∈ s' := Finset.mem_filter.mpr ⟨hjs, hfj⟩
          exact HahnSeries.coeff_eq_zero_of_lt_order (lt_of_lt_of_le hlt (hmin j hj'))
      exact hlc_ne hzero
  exact ⟨hsum_ne, i₀, hi₀_s, hfi₀, hord_eq⟩

/- ### Section 4: Anisotropy of `aK` and Non-4-Pfister-Neighbor Property -/

private lemma aK_anisotropic (x : Fin 9 → K) (h : (∑ i : Fin 9, aK i * x i ^ 2) = 0) :
    x = 0 := by
  by_contra hx
  have hne : ∃ i ∈ (Finset.univ : Finset (Fin 9)), aK i * x i ^ 2 ≠ 0 := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := Function.ne_iff.mp hx
    exact ⟨i, Finset.mem_univ i, mul_ne_zero (aK_ne_zero i) (pow_ne_zero 2 hi)⟩
  have hres := sum_ne_zero_and_ord_of_inj_ord Finset.univ (fun i : Fin 9 => aK i * x i ^ 2) hne ?_
  · exact hres.1 h
  · intro i _ j _ hi hj hord
    have hxi : x i ≠ 0 := fun h0 => hi (by simp [h0])
    have hxj : x j ≠ 0 := fun h0 => hj (by simp [h0])
    have hpi : par (ordK (aK i * x i ^ 2)) = Pi.single i (1 : ZMod 2) := by
      rw [par_mul (aK_ne_zero i) (pow_ne_zero 2 hxi), par_aK, par_sq hxi, add_zero]
    have hpj : par (ordK (aK j * x j ^ 2)) = Pi.single j (1 : ZMod 2) := by
      rw [par_mul (aK_ne_zero j) (pow_ne_zero 2 hxj), par_aK, par_sq hxj, add_zero]
    have heq : (Pi.single (M := fun _ => ZMod 2) i (1 : ZMod 2)) =
        (Pi.single (M := fun _ => ZMod 2) j (1 : ZMod 2)) := by
      rw [← hpi, ← hpj, hord]
    by_contra hij
    have hval := congrFun heq i
    simp [hij] at hval

private lemma not_pfister4_neighbor (c : K) (hc : c ≠ 0) (u : Fin 4 → K)
    (hu : ∀ j : Fin 4, u j ≠ 0) (T : (Fin 9 → K) →ₗ[K] ((Fin 4 → Bool) → K)) :
    ¬ ∀ x : Fin 9 → K,
      (∑ s : Fin 4 → Bool, (∏ j : Fin 4, if s j then u j else 1) * (T x s) ^ 2) =
        c * ∑ i : Fin 9, aK i * x i ^ 2 := by
  intro hT
  let P : (Fin 4 → Bool) → K := fun s => ∏ j : Fin 4, if s j then u j else 1
  have hP_ne : ∀ s, P s ≠ 0 := fun s =>
    Finset.prod_ne_zero_iff.mpr fun j _ => by split_ifs; exacts [hu j, one_ne_zero]
  let v : Fin 4 → (Fin 9 → ZMod 2) := fun j => par (ordK (u j))
  have hparP : ∀ s : Fin 4 → Bool, par (ordK (P s)) = ∑ j : Fin 4, (if s j then (1 : ZMod 2) else 0) • v j := by
    intro s
    rw [ordK_prod Finset.univ _ (fun j _ => by split_ifs; exacts [hu j, one_ne_zero])]
    have hpar_sum : ∀ (t : Finset (Fin 4)) (g : Fin 4 → Γ),
        par (∑ j ∈ t, g j) = ∑ j ∈ t, par (g j) := by
      intro t g
      classical
      induction t using Finset.induction_on with
      | empty => simp [par_zero]
      | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, par_add, ih]
    rw [hpar_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hs : s j = true
    · simp [hs, v]
    · simp [hs, ordK_one, par_zero]
  by_cases hind : LinearIndependent (ZMod 2) v
  · -- Case 1: Independent -> all 16 Pfister weights have distinct parities in span(v) of dim <= 4.
    let W : Submodule (ZMod 2) (Fin 9 → ZMod 2) := Submodule.span (ZMod 2) (Set.range v)
    have hparP_mem : ∀ s, par (ordK (P s)) ∈ W := by
      intro s
      rw [hparP s]
      exact Submodule.sum_mem W fun j _ =>
        Submodule.smul_mem W _ (Submodule.subset_span (Set.mem_range_self j))
    have hparP_inj : Function.Injective (fun s => par (ordK (P s))) := by
      intro s₁ s₂ heq
      dsimp only at heq
      rw [hparP s₁, hparP s₂] at heq
      have hsub : ∑ j : Fin 4, ((if s₁ j then (1 : ZMod 2) else 0) -
          (if s₂ j then (1 : ZMod 2) else 0)) • v j = 0 := by
        simp only [sub_smul, Finset.sum_sub_distrib, heq, sub_self]
      have hzero := Fintype.linearIndependent_iff.mp hind _ hsub
      funext j
      have hj := hzero j
      cases h1 : s₁ j <;> cases h2 : s₂ j <;> simp [h1, h2] at hj ⊢
    have he_mem : ∀ i : Fin 9, par (ordK c) + Pi.single i (1 : ZMod 2) ∈ W := by
      intro i
      let x : Fin 9 → K := Pi.single i 1
      have hrhs : c * ∑ m : Fin 9, aK m * x m ^ 2 = c * aK i := by
        congr 1
        rw [Finset.sum_eq_single i]
        · simp [x]
        · intro m _ hmi; simp [x, hmi]
        · intro h; exact absurd (Finset.mem_univ i) h
      have heq := hT x
      rw [hrhs] at heq
      have hca_ne : c * aK i ≠ 0 := mul_ne_zero hc (aK_ne_zero i)
      have hne : ∃ s ∈ (Finset.univ : Finset (Fin 4 → Bool)), P s * (T x s) ^ 2 ≠ 0 := by
        by_contra hall
        push Not at hall
        have hsum0 : ∑ s : Fin 4 → Bool, P s * (T x s) ^ 2 = 0 :=
          Finset.sum_eq_zero fun s _ => hall s (Finset.mem_univ s)
        rw [hsum0] at heq
        exact hca_ne heq.symm
      have hres := sum_ne_zero_and_ord_of_inj_ord Finset.univ
        (fun s : Fin 4 → Bool => P s * (T x s) ^ 2) hne (by
          intro s₁ _ s₂ _ h1 h2 hord
          have ht1 : T x s₁ ≠ 0 := fun h0 => h1 (by simp [h0])
          have ht2 : T x s₂ ≠ 0 := fun h0 => h2 (by simp [h0])
          apply hparP_inj
          have hp1 : par (ordK (P s₁ * (T x s₁) ^ 2)) = par (ordK (P s₁)) := by
            rw [par_mul (hP_ne s₁) (pow_ne_zero 2 ht1), par_sq ht1, add_zero]
          have hp2 : par (ordK (P s₂ * (T x s₂) ^ 2)) = par (ordK (P s₂)) := by
            rw [par_mul (hP_ne s₂) (pow_ne_zero 2 ht2), par_sq ht2, add_zero]
          dsimp only
          rw [← hp1, ← hp2, hord])
      obtain ⟨_, s₀, _, hs₀_ne, hs₀_ord⟩ := hres
      have ht0 : T x s₀ ≠ 0 := fun h0 => hs₀_ne (by simp [h0])
      rw [heq] at hs₀_ord
      have hpar_eq : par (ordK c) + Pi.single i (1 : ZMod 2) = par (ordK (P s₀)) := by
        calc par (ordK c) + Pi.single i (1 : ZMod 2)
            = par (ordK (c * aK i)) := by rw [par_mul hc (aK_ne_zero i), par_aK]
          _ = par (ordK (P s₀ * (T x s₀) ^ 2)) := by rw [hs₀_ord]
          _ = par (ordK (P s₀)) := by rw [par_mul (hP_ne s₀) (pow_ne_zero 2 ht0), par_sq ht0, add_zero]
      rw [hpar_eq]
      exact hparP_mem s₀
    -- Differences e_i - e_8 for i : Fin 8 lie in W and are linearly independent -> 8 <= finrank W <= 4.
    let w : Fin 8 → (Fin 9 → ZMod 2) := fun i => Pi.single i.castSucc 1 - Pi.single (8 : Fin 9) 1
    have hw_mem : ∀ i : Fin 8, w i ∈ W := by
      intro i
      have h1 := he_mem i.castSucc
      have h2 := he_mem 8
      have hsub := W.sub_mem h1 h2
      simpa [w] using hsub
    have hw_ind : LinearIndependent (ZMod 2) w := by
      rw [Fintype.linearIndependent_iff]
      intro g hg i
      have hval := congrFun hg i.castSucc
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, w, Pi.sub_apply] at hval
      have hne8 : (i.castSucc : Fin 9) ≠ 8 := by
        intro h
        have hv := congrArg Fin.val h
        change (i : ℕ) = 8 at hv
        omega
      rw [Finset.sum_eq_single i] at hval
      · simp [hne8] at hval; exact hval
      · intro j _ hji
        have hne : (i.castSucc : Fin 9) ≠ j.castSucc := fun h => hji (Fin.castSucc_inj.mp h).symm
        simp [hne, hne8]
      · intro h; exact absurd (Finset.mem_univ i) h
    have h8_le : 8 ≤ Module.finrank (ZMod 2) W := by
      let wW : Fin 8 → W := fun i => ⟨w i, hw_mem i⟩
      have hwW_ind : LinearIndependent (ZMod 2) wW := by
        refine LinearIndependent.of_comp W.subtype ?_
        exact hw_ind
      have hle := hwW_ind.fintype_card_le_finrank
      simpa using hle
    have hW_le : Module.finrank (ZMod 2) W ≤ 4 := by
      have hle := finrank_span_le_card (R := ZMod 2) (Set.range v)
      calc Module.finrank (ZMod 2) W ≤ (Set.range v).toFinset.card := by
            simpa [W, Set.toFinset_card] using hle
        _ ≤ Fintype.card (Fin 4) := by
            rw [Set.toFinset_range]
            exact Finset.card_image_le
        _ = 4 := by simp
    omega
  · -- Case 2: Dependent -> construct an 8-dim totally isotropic subspace U intersecting range T.
    rw [Fintype.linearIndependent_iff] at hind
    push Not at hind
    obtain ⟨g, hg_sum, j₀, hj₀⟩ := hind
    let S : Fin 4 → Bool := fun j => decide (g j ≠ 0)
    have hSj₀ : S j₀ = true := decide_eq_true hj₀
    let flip : (Fin 4 → Bool) → (Fin 4 → Bool) := fun s j => xor (s j) (S j)
    have hflip_inv : ∀ s, flip (flip s) = s := by
      intro s; funext j; simp only [flip]; cases s j <;> cases S j <;> rfl
    have hflip_j₀ : ∀ s, flip s j₀ = !s j₀ := by
      intro s; simp [flip, hSj₀]
    have hpar_ratio : ∀ s : Fin 4 → Bool, par (ordK (P (flip s) / P s)) = 0 := by
      intro s
      rw [ordK_div (hP_ne (flip s)) (hP_ne s), sub_eq_add_neg, par_add, par_neg,
        hparP (flip s), hparP s, ← Finset.sum_add_distrib]
      have hterm : ∀ j : Fin 4,
          (if flip s j then (1 : ZMod 2) else 0) • v j +
            (if s j then (1 : ZMod 2) else 0) • v j = g j • v j := by
        intro j
        rw [← add_smul]
        congr 1
        by_cases hgj : g j = 0
        · have hSj : S j = false := decide_eq_false (not_not.mpr hgj)
          have hfj : flip s j = s j := by simp [flip, hSj]
          rw [hfj, hgj]
          cases s j <;> decide
        · have hgj1 : g j = 1 := (zmod2_eq_zero_or_one (g j)).resolve_left hgj
          have hSj : S j = true := decide_eq_true hgj
          have hfj : flip s j = !s j := by simp [flip, hSj]
          rw [hfj, hgj1]
          cases s j <;> decide
      simp_rw [hterm]
      exact hg_sum
    have hsq_ratio : ∀ s, ∃ r : K, r ^ 2 = P (flip s) / P s := fun s =>
      exists_sq_of_par_zero (div_ne_zero (hP_ne (flip s)) (hP_ne s)) (hpar_ratio s)
    choose r hr using hsq_ratio
    obtain ⟨I, hI⟩ := exists_sqrt_neg_one
    let Half := {s : Fin 4 → Bool // s j₀ = false}
    have hcard_half : Fintype.card Half = 8 := by
      let eHalf : Half ≃ ({j : Fin 4 // j ≠ j₀} → Bool) :=
        { toFun := fun s j => s.1 j.1
          invFun := fun f => ⟨fun j => if h : j = j₀ then false else f ⟨j, h⟩, by simp⟩
          left_inv := fun ⟨s, hs⟩ => Subtype.ext (funext fun j => by
            by_cases h : j = j₀
            · subst h; simp [hs]
            · simp [h])
          right_inv := fun f => funext fun ⟨j, hj⟩ => by simp [hj] }
      rw [Fintype.card_congr eHalf, Fintype.card_fun, Fintype.card_bool, Fintype.card_subtype_compl,
        Fintype.card_fin, Fintype.card_unique]
      norm_num
    have hL_exists : ∃ L : (Half → K) →ₗ[K] ((Fin 4 → Bool) → K),
        Function.Injective L ∧ ∀ y : Half → K, ∑ s : Fin 4 → Bool, P s * (L y s) ^ 2 = 0 := by
      let L : (Half → K) →ₗ[K] ((Fin 4 → Bool) → K) :=
        { toFun := fun y s =>
            if hs : s j₀ = false then y ⟨s, hs⟩
            else I * r s * y ⟨flip s, by rw [hflip_j₀]; cases h : s j₀ <;> simp_all⟩
          map_add' := fun y₁ y₂ => by
            funext s
            by_cases hs : s j₀ = false
            · simp only [Pi.add_apply, dif_pos hs]
            · simp only [Pi.add_apply, dif_neg hs]; ring
          map_smul' := fun a y => by
            funext s
            by_cases hs : s j₀ = false
            · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, dif_pos hs]
            · simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, dif_neg hs]; ring }
      have hL_inj : Function.Injective L := by
        intro y₁ y₂ heq
        funext ⟨s, hs⟩
        have := congrFun heq s
        simpa [L, hs] using this
      have hL_iso : ∀ y : Half → K, ∑ s : Fin 4 → Bool, P s * (L y s) ^ 2 = 0 := by
        intro y
        let S0 := Finset.univ.filter (fun s : Fin 4 → Bool => s j₀ = false)
        let S1 := Finset.univ.filter (fun s : Fin 4 → Bool => s j₀ = true)
        have hsplit : ∑ s : Fin 4 → Bool, P s * (L y s) ^ 2 =
            (∑ s ∈ S0, P s * (L y s) ^ 2) + ∑ s ∈ S1, P s * (L y s) ^ 2 := by
          rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun s : Fin 4 → Bool => s j₀ = false)]
          congr 1
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext s; simp [S1]
        rw [hsplit]
        have hS1 : ∑ s ∈ S1, P s * (L y s) ^ 2 = ∑ s ∈ S0, P (flip s) * (L y (flip s)) ^ 2 := by
          refine Finset.sum_bij (fun s _ => flip s) ?_ ?_ ?_ ?_
          · intro s hs
            simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
            rw [hflip_j₀, hs]; rfl
          · intro s₁ _ s₂ _ h; rw [← hflip_inv s₁, ← hflip_inv s₂, h]
          · intro s hs
            refine ⟨flip s, ?_, hflip_inv s⟩
            simp only [S0, S1, Finset.mem_filter, Finset.mem_univ, true_and] at hs ⊢
            rw [hflip_j₀, hs]; rfl
          · intro s _; rw [hflip_inv]
        rw [hS1, ← Finset.sum_add_distrib]
        refine Finset.sum_eq_zero fun s hs => ?_
        have hs0 : s j₀ = false := (Finset.mem_filter.mp hs).2
        have hfs1 : flip s j₀ = true := by rw [hflip_j₀, hs0]; rfl
        have hfs_ne : ¬ flip s j₀ = false := by rw [hfs1]; decide
        simp only [L, LinearMap.coe_mk, AddHom.coe_mk, dif_pos hs0, dif_neg hfs_ne]
        have hflip_sub : (⟨flip (flip s), by rw [hflip_j₀]; cases h : flip s j₀ <;> simp_all⟩ : Half) =
            ⟨s, hs0⟩ := Subtype.ext (hflip_inv s)
        rw [hflip_sub]
        have hrs : (r (flip s)) ^ 2 = P s / P (flip s) := by
          have := hr (flip s)
          rwa [hflip_inv] at this
        calc P s * (y ⟨s, hs0⟩) ^ 2 + P (flip s) * (I * r (flip s) * y ⟨s, hs0⟩) ^ 2
            = P s * (y ⟨s, hs0⟩) ^ 2 + P (flip s) * (I ^ 2 * (r (flip s)) ^ 2) * (y ⟨s, hs0⟩) ^ 2 := by ring
          _ = P s * (y ⟨s, hs0⟩) ^ 2 + P (flip s) * ((-1) * (P s / P (flip s))) * (y ⟨s, hs0⟩) ^ 2 := by
              rw [hI, hrs]
          _ = 0 := by field_simp [hP_ne (flip s)]; ring
      exact ⟨L, hL_inj, hL_iso⟩
    obtain ⟨L, hL_inj, hL_iso⟩ := hL_exists
    have hT_inj : Function.Injective T := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      have hTx : T x = 0 := LinearMap.mem_ker.mp hx
      have heq := hT x
      rw [hTx] at heq
      simp only [Pi.zero_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        mul_zero, Finset.sum_const_zero] at heq
      have hsum0 : ∑ i : Fin 9, aK i * x i ^ 2 = 0 := (mul_eq_zero.mp heq.symm).resolve_left hc
      exact aK_anisotropic x hsum0
    have hdimT : Module.finrank K (LinearMap.range T) = 9 := by
      rw [LinearMap.finrank_range_of_inj hT_inj, Module.finrank_pi, Fintype.card_fin]
    have hdimL : Module.finrank K (LinearMap.range L) = 8 := by
      rw [LinearMap.finrank_range_of_inj hL_inj, Module.finrank_pi, hcard_half]
    have hdim_amb : Module.finrank K ((Fin 4 → Bool) → K) = 16 := by
      rw [Module.finrank_pi, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
      norm_num
    have hsup_le : Module.finrank K ↥(LinearMap.range T ⊔ LinearMap.range L) ≤ 16 := by
      rw [← hdim_amb]; exact Submodule.finrank_le _
    have hinf_pos : 0 < Module.finrank K ↥(LinearMap.range T ⊓ LinearMap.range L) := by
      have hadd := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range T) (LinearMap.range L)
      rw [hdimT, hdimL] at hadd
      omega
    have hinf_nontriv : (LinearMap.range T ⊓ LinearMap.range L) ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hinf_pos
      omega
    have hinf_exists : ∃ z ∈ LinearMap.range T ⊓ LinearMap.range L, z ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hinf_nontriv
      rw [Submodule.eq_bot_iff]
      exact hall
    obtain ⟨z, hz_mem, hz_ne⟩ := hinf_exists
    obtain ⟨⟨x, hx_eq⟩, ⟨y, hy_eq⟩⟩ := hz_mem
    have hx_ne : x ≠ 0 := by
      intro hx0; apply hz_ne; rw [← hx_eq, hx0, map_zero]
    have h0 := hT x
    rw [hx_eq, ← hy_eq, hL_iso y] at h0
    have hsum0 : ∑ i : Fin 9, aK i * x i ^ 2 = 0 := (mul_eq_zero.mp h0.symm).resolve_left hc
    exact hx_ne (aK_anisotropic x hsum0)

/- ### Section 5: Explicit Twisted Clifford Algebra `TwistedCl` and Non-Isomorphism with `M_8(Q)` -/

private abbrev Mask := Fin 9 → Bool

private def maskXor (s t : Mask) : Mask := fun i => xor (s i) (t i)

private def maskZero : Mask := fun _ => false

private def maskSingle (i : Fin 9) : Mask := fun j => decide (j = i)

private def maskParity (s : Mask) : ZMod 2 :=
  ∑ i : Fin 9, if s i then (1 : ZMod 2) else 0

private lemma maskXor_zero_left (s : Mask) : maskXor maskZero s = s := by
  funext i; simp [maskXor, maskZero]

private lemma maskXor_zero_right (s : Mask) : maskXor s maskZero = s := by
  funext i; simp [maskXor, maskZero]

private lemma maskXor_self (s : Mask) : maskXor s s = maskZero := by
  funext i; simp [maskXor, maskZero]

private lemma maskXor_assoc (s t u : Mask) : maskXor (maskXor s t) u = maskXor s (maskXor t u) := by
  funext i; simp only [maskXor]; cases s i <;> cases t i <;> cases u i <;> rfl

private lemma maskXor_comm (s t : Mask) : maskXor s t = maskXor t s := by
  funext i; simp only [maskXor]; cases s i <;> cases t i <;> rfl

private lemma maskParity_zero : maskParity maskZero = 0 := by
  simp [maskParity, maskZero]

private lemma bool_zmod2_xor (b₁ b₂ : Bool) :
    (if (xor b₁ b₂) = true then (1 : ZMod 2) else 0) =
      (if b₁ = true then (1 : ZMod 2) else 0) + (if b₂ = true then (1 : ZMod 2) else 0) := by
  cases b₁ <;> cases b₂ <;> decide

private lemma maskParity_xor (s t : Mask) :
    maskParity (maskXor s t) = maskParity s + maskParity t := by
  simp only [maskParity, maskXor, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => bool_zmod2_xor (s i) (t i)

private lemma maskParity_single (i : Fin 9) : maskParity (maskSingle i) = 1 := by
  simp only [maskParity, maskSingle]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji; simp [hji]
  · intro h; exact absurd (Finset.mem_univ i) h

private noncomputable def signFactor (s t : Mask) : K :=
  ∏ p : Fin 9 × Fin 9, if p.2 < p.1 ∧ s p.1 = true ∧ t p.2 = true then (-1 : K) else 1

private noncomputable def diagFactor (s t : Mask) : K :=
  ∏ i : Fin 9, if s i = true ∧ t i = true then aK i else 1

private noncomputable def twCoeff (s t : Mask) : K :=
  signFactor s t * diagFactor s t

private lemma signFactor_ne_zero (s t : Mask) : signFactor s t ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => by
    split_ifs
    · exact neg_ne_zero.mpr one_ne_zero
    · exact one_ne_zero

private lemma diagFactor_ne_zero (s t : Mask) : diagFactor s t ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => by
    split_ifs
    · exact aK_ne_zero i
    · exact one_ne_zero

private lemma twCoeff_ne_zero (s t : Mask) : twCoeff s t ≠ 0 :=
  mul_ne_zero (signFactor_ne_zero s t) (diagFactor_ne_zero s t)

private lemma twCoeff_zero_left (t : Mask) : twCoeff maskZero t = 1 := by
  simp [twCoeff, signFactor, diagFactor, maskZero]

private lemma twCoeff_zero_right (s : Mask) : twCoeff s maskZero = 1 := by
  simp [twCoeff, signFactor, diagFactor, maskZero]

private lemma sign_bool_cocycle (b₁ b₂ b₃ b₄ : Bool) :
    (if b₁ = true ∧ b₃ = true then (-1 : K) else 1) *
      (if (xor b₁ b₂) = true ∧ b₄ = true then (-1 : K) else 1) =
    (if b₁ = true ∧ (xor b₃ b₄) = true then (-1 : K) else 1) *
      (if b₂ = true ∧ b₄ = true then (-1 : K) else 1) := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> cases b₄ <;> simp

private lemma diag_bool_cocycle (c : K) (b₁ b₂ b₃ : Bool) :
    (if b₁ = true ∧ b₂ = true then c else 1) *
      (if (xor b₁ b₂) = true ∧ b₃ = true then c else 1) =
    (if b₁ = true ∧ (xor b₂ b₃) = true then c else 1) *
      (if b₂ = true ∧ b₃ = true then c else 1) := by
  cases b₁ <;> cases b₂ <;> cases b₃ <;> simp

private lemma signFactor_cocycle (s t u : Mask) :
    signFactor s t * signFactor (maskXor s t) u = signFactor s (maskXor t u) * signFactor t u := by
  simp only [signFactor, ← Finset.prod_mul_distrib, maskXor]
  refine Finset.prod_congr rfl fun p _ => ?_
  by_cases hlt : p.2 < p.1
  · simp only [hlt, true_and]
    exact sign_bool_cocycle (s p.1) (t p.1) (t p.2) (u p.2)
  · simp [hlt]

private lemma diagFactor_cocycle (s t u : Mask) :
    diagFactor s t * diagFactor (maskXor s t) u = diagFactor s (maskXor t u) * diagFactor t u := by
  simp only [diagFactor, ← Finset.prod_mul_distrib, maskXor]
  refine Finset.prod_congr rfl fun i _ => diag_bool_cocycle (aK i) (s i) (t i) (u i)

private lemma twCoeff_cocycle (s t u : Mask) :
    twCoeff s t * twCoeff (maskXor s t) u = twCoeff s (maskXor t u) * twCoeff t u := by
  simp only [twCoeff]
  calc signFactor s t * diagFactor s t * (signFactor (maskXor s t) u * diagFactor (maskXor s t) u)
      = (signFactor s t * signFactor (maskXor s t) u) * (diagFactor s t * diagFactor (maskXor s t) u) := by ring
    _ = (signFactor s (maskXor t u) * signFactor t u) * (diagFactor s (maskXor t u) * diagFactor t u) := by
        rw [signFactor_cocycle, diagFactor_cocycle]
    _ = signFactor s (maskXor t u) * diagFactor s (maskXor t u) * (signFactor t u * diagFactor t u) := by ring

private structure TwistedCl where
  coeff : Mask → K

private lemma TwistedCl.ext {x y : TwistedCl} (h : x.coeff = y.coeff) : x = y := by
  cases x; cases y; cases h; rfl

private noncomputable def twZero : TwistedCl := ⟨fun _ => 0⟩

private noncomputable def twOne : TwistedCl := ⟨fun s => if s = maskZero then 1 else 0⟩

private noncomputable def twAdd (x y : TwistedCl) : TwistedCl :=
  ⟨fun s => x.coeff s + y.coeff s⟩

private noncomputable def twNeg (x : TwistedCl) : TwistedCl :=
  ⟨fun s => -x.coeff s⟩

private noncomputable def twSmul (c : K) (x : TwistedCl) : TwistedCl :=
  ⟨fun s => c * x.coeff s⟩

private noncomputable def twMul (x y : TwistedCl) : TwistedCl :=
  ⟨fun r => ∑ s : Mask, twCoeff s (maskXor s r) * x.coeff s * y.coeff (maskXor s r)⟩

private lemma twMul_assoc (x y z : TwistedCl) : twMul (twMul x y) z = twMul x (twMul y z) := by
  apply TwistedCl.ext; funext r
  simp only [twMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.sum_bij (fun p _ => maskXor s p) (fun _ _ => Finset.mem_univ _)
    (fun p₁ _ p₂ _ h => by
      have := congrArg (maskXor s) h
      simpa [← maskXor_assoc, maskXor_self, maskXor_zero_left] using this)
    (fun t _ => ⟨maskXor s t, Finset.mem_univ _, by
      rw [← maskXor_assoc, maskXor_self, maskXor_zero_left]⟩)
    (fun p _ => ?_)
  have h1 : maskXor (maskXor s p) (maskXor s r) = maskXor p r := by
    rw [maskXor_assoc, ← maskXor_assoc p s r, maskXor_comm p s, maskXor_assoc s p r,
      ← maskXor_assoc s s, maskXor_self, maskXor_zero_left]
  rw [h1]
  have h2 : maskXor s (maskXor s p) = p := by
    rw [← maskXor_assoc, maskXor_self, maskXor_zero_left]
  have hcoc := twCoeff_cocycle s (maskXor s p) (maskXor p r)
  rw [h2] at hcoc
  have h3 : maskXor (maskXor s p) (maskXor p r) = maskXor s r := by
    rw [maskXor_assoc, ← maskXor_assoc p p r, maskXor_self, maskXor_zero_left]
  rw [h3] at hcoc
  calc twCoeff p (maskXor p r) * (twCoeff s (maskXor s p) * x.coeff s * y.coeff (maskXor s p)) *
          z.coeff (maskXor p r)
      = (twCoeff s (maskXor s p) * twCoeff p (maskXor p r)) *
          (x.coeff s * y.coeff (maskXor s p) * z.coeff (maskXor p r)) := by ring
    _ = (twCoeff s (maskXor s r) * twCoeff (maskXor s p) (maskXor p r)) *
          (x.coeff s * y.coeff (maskXor s p) * z.coeff (maskXor p r)) := by rw [hcoc]
    _ = twCoeff s (maskXor s r) * x.coeff s *
          (twCoeff (maskXor s p) (maskXor p r) * y.coeff (maskXor s p) * z.coeff (maskXor p r)) := by ring

private lemma twMul_coeff_def (x y : TwistedCl) (r : Mask) :
    (twMul x y).coeff r = ∑ s : Mask, twCoeff s (maskXor s r) * x.coeff s * y.coeff (maskXor s r) :=
  rfl

private noncomputable instance : Ring TwistedCl where
  add := twAdd
  add_assoc x y z := TwistedCl.ext (funext fun s => add_assoc _ _ _)
  zero := twZero
  zero_add x := TwistedCl.ext (funext fun s => zero_add _)
  add_zero x := TwistedCl.ext (funext fun s => add_zero _)
  nsmul n x := ⟨fun s => (n : K) * x.coeff s⟩
  nsmul_zero x := TwistedCl.ext (funext fun s => by
    show ((0 : ℕ) : K) * x.coeff s = twZero.coeff s
    simp [twZero])
  nsmul_succ n x := TwistedCl.ext (funext fun s => by
    show ((n + 1 : ℕ) : K) * x.coeff s = (n : K) * x.coeff s + x.coeff s
    push_cast; ring)
  neg := twNeg
  sub x y := ⟨fun s => x.coeff s - y.coeff s⟩
  sub_eq_add_neg x y := TwistedCl.ext (funext fun s => sub_eq_add_neg _ _)
  zsmul n x := ⟨fun s => (n : K) * x.coeff s⟩
  zsmul_zero' x := TwistedCl.ext (funext fun s => by
    show ((0 : ℤ) : K) * x.coeff s = twZero.coeff s
    simp [twZero])
  zsmul_succ' n x := TwistedCl.ext (funext fun s => by
    show (((n + 1 : ℕ) : ℤ) : K) * x.coeff s = ((n : ℤ) : K) * x.coeff s + x.coeff s
    push_cast; ring)
  zsmul_neg' n x := TwistedCl.ext (funext fun s => by
    show (Int.negSucc n : K) * x.coeff s = -((((n + 1 : ℕ) : ℤ) : K) * x.coeff s)
    push_cast; ring)
  neg_add_cancel x := TwistedCl.ext (funext fun s => neg_add_cancel _)
  add_comm x y := TwistedCl.ext (funext fun s => add_comm _ _)
  mul := twMul
  mul_assoc := twMul_assoc
  one := twOne
  one_mul x := TwistedCl.ext (funext fun r => by
    show (twMul twOne x).coeff r = x.coeff r
    rw [twMul_coeff_def, Finset.sum_eq_single maskZero]
    · simp [twOne, twCoeff_zero_left, maskXor_zero_left]
    · intro s _ hs; simp [twOne, hs]
    · intro h; exact absurd (Finset.mem_univ _) h)
  mul_one x := TwistedCl.ext (funext fun r => by
    show (twMul x twOne).coeff r = x.coeff r
    rw [twMul_coeff_def, Finset.sum_eq_single r]
    · simp [twOne, maskXor_self, twCoeff_zero_right]
    · intro s _ hsr
      have hne : maskXor s r ≠ maskZero := by
        intro h
        apply hsr
        have := congrArg (maskXor s) h
        rw [← maskXor_assoc, maskXor_self, maskXor_zero_left, maskXor_zero_right] at this
        exact this.symm
      simp [twOne, hne]
    · intro h; exact absurd (Finset.mem_univ _) h)
  left_distrib x y z := TwistedCl.ext (funext fun r => by
    show (twMul x (twAdd y z)).coeff r = (twAdd (twMul x y) (twMul x z)).coeff r
    simp only [twMul_coeff_def, twAdd, mul_add, Finset.sum_add_distrib])
  right_distrib x y z := TwistedCl.ext (funext fun r => by
    show (twMul (twAdd x y) z).coeff r = (twAdd (twMul x z) (twMul y z)).coeff r
    simp only [twMul_coeff_def, twAdd, mul_add, add_mul, Finset.sum_add_distrib])
  zero_mul x := TwistedCl.ext (funext fun r => by
    show (twMul twZero x).coeff r = twZero.coeff r
    simp only [twMul_coeff_def, twZero, mul_zero, zero_mul, Finset.sum_const_zero])
  mul_zero x := TwistedCl.ext (funext fun r => by
    show (twMul x twZero).coeff r = twZero.coeff r
    simp only [twMul_coeff_def, twZero, mul_zero, Finset.sum_const_zero])

private lemma tw_zero_coeff (s : Mask) : (0 : TwistedCl).coeff s = 0 := rfl
private lemma tw_one_coeff (s : Mask) : (1 : TwistedCl).coeff s = if s = maskZero then 1 else 0 := rfl
private lemma tw_add_coeff (x y : TwistedCl) (s : Mask) : (x + y).coeff s = x.coeff s + y.coeff s := rfl
private lemma tw_neg_coeff (x : TwistedCl) (s : Mask) : (-x).coeff s = -x.coeff s := rfl
private lemma tw_mul_coeff (x y : TwistedCl) (r : Mask) :
    (x * y).coeff r = ∑ s : Mask, twCoeff s (maskXor s r) * x.coeff s * y.coeff (maskXor s r) :=
  twMul_coeff_def x y r

private noncomputable instance : Algebra K TwistedCl where
  algebraMap :=
    { toFun := fun c => twSmul c (1 : TwistedCl)
      map_one' := TwistedCl.ext (funext fun s => by simp [twSmul, tw_one_coeff])
      map_mul' := fun c₁ c₂ => TwistedCl.ext (funext fun r => by
        rw [tw_mul_coeff, Finset.sum_eq_single maskZero]
        · simp [twSmul, tw_one_coeff, twCoeff_zero_left, maskXor_zero_left]
        · intro s _ hs; simp [twSmul, tw_one_coeff, hs]
        · intro h; exact absurd (Finset.mem_univ _) h)
      map_zero' := TwistedCl.ext (funext fun s => by simp [twSmul, tw_zero_coeff])
      map_add' := fun c₁ c₂ => TwistedCl.ext (funext fun s => by
        simp only [twSmul, tw_add_coeff, tw_one_coeff]; split_ifs <;> ring) }
  smul := twSmul
  commutes' := fun c x => TwistedCl.ext (funext fun r => by
    simp only [tw_mul_coeff]
    rw [Finset.sum_eq_single maskZero, Finset.sum_eq_single r]
    · simp [twSmul, tw_one_coeff, twCoeff_zero_left, twCoeff_zero_right,
        maskXor_zero_left, maskXor_self, mul_comm]
    · intro s _ hsr
      have hne : maskXor s r ≠ maskZero := by
        intro h; apply hsr
        have := congrArg (maskXor s) h
        rw [← maskXor_assoc, maskXor_self, maskXor_zero_left, maskXor_zero_right] at this
        exact this.symm
      simp [twSmul, tw_one_coeff, hne]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro s _ hs; simp [twSmul, tw_one_coeff, hs]
    · intro h; exact absurd (Finset.mem_univ _) h)
  smul_def' := fun c x => TwistedCl.ext (funext fun r => by
    change c * x.coeff r = (twSmul c (1 : TwistedCl) * x).coeff r
    rw [tw_mul_coeff, Finset.sum_eq_single maskZero]
    · simp [twSmul, tw_one_coeff, twCoeff_zero_left, maskXor_zero_left]
    · intro s _ hs; simp [twSmul, tw_one_coeff, hs]
    · intro h; exact absurd (Finset.mem_univ _) h)

private lemma tw_smul_coeff (c : K) (x : TwistedCl) (s : Mask) : (c • x).coeff s = c * x.coeff s := rfl

private noncomputable def twBasis (s : Mask) : TwistedCl :=
  ⟨fun r => if r = s then 1 else 0⟩

private lemma twBasis_mul (s t : Mask) :
    twBasis s * twBasis t = twCoeff s t • twBasis (maskXor s t) := by
  apply TwistedCl.ext; funext r
  rw [tw_mul_coeff, Finset.sum_eq_single s]
  · by_cases hr : r = maskXor s t
    · subst hr
      have h1 : maskXor s (maskXor s t) = t := by
        rw [← maskXor_assoc, maskXor_self, maskXor_zero_left]
      simp [twBasis, tw_smul_coeff, h1]
    · have hne : maskXor s r ≠ t := by
        intro h; apply hr
        have := congrArg (maskXor s) h
        rw [← maskXor_assoc, maskXor_self, maskXor_zero_left] at this
        exact this
      simp [twBasis, tw_smul_coeff, hr, hne]
  · intro u _ hus; simp [twBasis, hus]
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma twBasis_zero : twBasis maskZero = 1 := rfl

private lemma twCoeff_single_self (i : Fin 9) :
    twCoeff (maskSingle i) (maskSingle i) = aK i := by
  have hs : signFactor (maskSingle i) (maskSingle i) = 1 := by
    refine Finset.prod_eq_one fun p _ => ?_
    simp only [maskSingle, decide_eq_true_eq]
    split_ifs with h
    · exfalso; obtain ⟨hlt, h1, h2⟩ := h; rw [h1, h2] at hlt; exact lt_irrefl _ hlt
    · rfl
  have hd : diagFactor (maskSingle i) (maskSingle i) = aK i := by
    rw [diagFactor, Finset.prod_eq_single i]
    · simp [maskSingle]
    · intro j _ hji; simp [maskSingle, hji]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [twCoeff, hs, hd, one_mul]

private lemma twCoeff_single_lt {i j : Fin 9} (hij : i < j) :
    twCoeff (maskSingle i) (maskSingle j) = 1 := by
  have hs : signFactor (maskSingle i) (maskSingle j) = 1 := by
    refine Finset.prod_eq_one fun p _ => ?_
    simp only [maskSingle, decide_eq_true_eq]
    split_ifs with h
    · exfalso; obtain ⟨hlt, h1, h2⟩ := h; rw [h1, h2] at hlt; exact lt_asymm hij hlt
    · rfl
  have hd : diagFactor (maskSingle i) (maskSingle j) = 1 := by
    refine Finset.prod_eq_one fun m _ => ?_
    simp only [maskSingle, decide_eq_true_eq]
    split_ifs with h
    · exfalso; exact hij.ne (h.1.symm.trans h.2)
    · rfl
  rw [twCoeff, hs, hd, one_mul]

private lemma twCoeff_single_gt {i j : Fin 9} (hji : j < i) :
    twCoeff (maskSingle i) (maskSingle j) = -1 := by
  have hs : signFactor (maskSingle i) (maskSingle j) = -1 := by
    rw [signFactor, Finset.prod_eq_single (i, j)]
    · simp [maskSingle, hji]
    · intro p _ hp
      simp only [maskSingle, decide_eq_true_eq]
      split_ifs with h
      · exfalso; exact hp (Prod.ext h.2.1 h.2.2)
      · rfl
    · intro h; exact absurd (Finset.mem_univ _) h
  have hd : diagFactor (maskSingle i) (maskSingle j) = 1 := by
    refine Finset.prod_eq_one fun m _ => ?_
    simp only [maskSingle, decide_eq_true_eq]
    split_ifs with h
    · exfalso; exact hji.ne' (h.1.symm.trans h.2)
    · rfl
  rw [twCoeff, hs, hd, mul_one]

/- ### Section 6: `TwistedCl` Has No Zero Divisors via Doubled Valuation -/

private def maskVec (s : Mask) : Γ := toLex (fun i : Fin 9 => if s i then (1 : ℤ) else 0)

private lemma ordK_twCoeff (s t : Mask) :
    ordK (twCoeff s t) = toLex (fun i : Fin 9 => if s i = true ∧ t i = true then (1 : ℤ) else 0) := by
  rw [twCoeff, ordK_mul (signFactor_ne_zero s t) (diagFactor_ne_zero s t)]
  have hs_ord : ordK (signFactor s t) = 0 := by
    rw [signFactor, ordK_prod Finset.univ _ (fun _ _ => by
      split_ifs; exacts [neg_ne_zero.mpr one_ne_zero, one_ne_zero])]
    refine Finset.sum_eq_zero fun p _ => ?_
    split_ifs
    · exact ordK_neg_one
    · exact ordK_one
  rw [hs_ord, zero_add, diagFactor, ordK_prod Finset.univ _ (fun i _ => by
    split_ifs; exacts [aK_ne_zero i, one_ne_zero])]
  apply ofLex.injective
  ext j
  rw [ofLex_finset_sum, Finset.sum_apply, ofLex_toLex]
  rw [Finset.sum_eq_single j]
  · split_ifs with h
    · rw [ordK_aK]; simp [basisVec]
    · rw [ordK_one]; rfl
  · intro i _ hij
    split_ifs with h
    · rw [ordK_aK]; simp [basisVec, hij.symm]
    · rw [ordK_one]; rfl
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma doubled_valuation_add (s t : Mask) :
    2 • ordK (twCoeff s t) + maskVec (maskXor s t) = maskVec s + maskVec t := by
  apply ofLex.injective
  ext i
  rw [ordK_twCoeff]
  change 2 * (if s i = true ∧ t i = true then (1 : ℤ) else 0) +
      (if xor (s i) (t i) = true then (1 : ℤ) else 0) =
    (if s i = true then (1 : ℤ) else 0) + (if t i = true then (1 : ℤ) else 0)
  cases s i <;> cases t i <;> norm_num

private noncomputable def dblVal (x : TwistedCl) (s : Mask) : Γ :=
  2 • ordK (x.coeff s) + maskVec s

private lemma par_dblVal (x : TwistedCl) (s : Mask) :
    par (dblVal x s) = fun i => if s i then (1 : ZMod 2) else 0 := by
  rw [dblVal, par_add, par_two_smul, zero_add]
  ext i
  simp only [par, maskVec, ofLex_toLex]
  cases s i <;> simp

private lemma dblVal_inj (x : TwistedCl) {s₁ s₂ : Mask} (h : dblVal x s₁ = dblVal x s₂) :
    s₁ = s₂ := by
  have hp := congrArg par h
  rw [par_dblVal, par_dblVal] at hp
  funext i
  have hi := congrFun hp i
  cases h1 : s₁ i <;> cases h2 : s₂ i <;> simp [h1, h2] at hi ⊢

private lemma hahn_coeff_sum {ι : Type*} (s : Finset ι) (f : ι → H) (g : Γ) :
    (∑ i ∈ s, f i).coeff g = ∑ i ∈ s, (f i).coeff g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, HahnSeries.coeff_add, ih]

private lemma tw_sum_coeff {ι : Type*} (s : Finset ι) (f : ι → TwistedCl) (r : Mask) :
    (∑ i ∈ s, f i).coeff r = ∑ i ∈ s, (f i).coeff r := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, tw_add_coeff, ih]

private lemma twistedCl_mul_ne_zero {x y : TwistedCl} (hx : x ≠ 0) (hy : y ≠ 0) :
    x * y ≠ 0 := by
  classical
  let sx := Finset.univ.filter (fun s : Mask => x.coeff s ≠ 0)
  let sy := Finset.univ.filter (fun t : Mask => y.coeff t ≠ 0)
  have hsx : sx.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hx; apply TwistedCl.ext; funext s
    by_contra hc
    have hc' : x.coeff s ≠ 0 := hc
    have : s ∈ sx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc'⟩
    rw [h] at this; exact Finset.notMem_empty s this
  have hsy : sy.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply hy; apply TwistedCl.ext; funext t
    by_contra hc
    have hc' : y.coeff t ≠ 0 := hc
    have : t ∈ sy := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hc'⟩
    rw [h] at this; exact Finset.notMem_empty t this
  obtain ⟨s₀, hs₀, hminx⟩ := Finset.exists_min_image sx (dblVal x) hsx
  obtain ⟨t₀, ht₀, hminy⟩ := Finset.exists_min_image sy (dblVal y) hsy
  have hxs₀ : x.coeff s₀ ≠ 0 := (Finset.mem_filter.mp hs₀).2
  have hyt₀ : y.coeff t₀ ≠ 0 := (Finset.mem_filter.mp ht₀).2
  let r₀ : Mask := maskXor s₀ t₀
  have hterm_val : ∀ s : Mask,
      x.coeff s ≠ 0 → y.coeff (maskXor s r₀) ≠ 0 →
      2 • ordK (twCoeff s (maskXor s r₀) * x.coeff s * y.coeff (maskXor s r₀)) + maskVec r₀ =
        dblVal x s + dblVal y (maskXor s r₀) := by
    intro s hxs hys
    have hmul_ne : twCoeff s (maskXor s r₀) * x.coeff s ≠ 0 :=
      mul_ne_zero (twCoeff_ne_zero _ _) hxs
    rw [ordK_mul hmul_ne hys, ordK_mul (twCoeff_ne_zero _ _) hxs]
    have hxor_eq : maskXor s (maskXor s r₀) = r₀ := by
      rw [← maskXor_assoc, maskXor_self, maskXor_zero_left]
    calc 2 • (ordK (twCoeff s (maskXor s r₀)) + ordK (x.coeff s) + ordK (y.coeff (maskXor s r₀))) +
            maskVec r₀
        = (2 • ordK (twCoeff s (maskXor s r₀)) + maskVec (maskXor s (maskXor s r₀))) +
            2 • ordK (x.coeff s) + 2 • ordK (y.coeff (maskXor s r₀)) := by
          rw [hxor_eq, nsmul_add, nsmul_add]; abel
      _ = (maskVec s + maskVec (maskXor s r₀)) +
            2 • ordK (x.coeff s) + 2 • ordK (y.coeff (maskXor s r₀)) := by
          rw [doubled_valuation_add]
      _ = dblVal x s + dblVal y (maskXor s r₀) := by
          simp only [dblVal]; abel
  have hr₀_s₀ : maskXor s₀ r₀ = t₀ := by
    simp only [r₀, ← maskXor_assoc, maskXor_self, maskXor_zero_left]
  have hterm_s₀_ne : twCoeff s₀ (maskXor s₀ r₀) * x.coeff s₀ * y.coeff (maskXor s₀ r₀) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (twCoeff_ne_zero _ _) hxs₀) (by rw [hr₀_s₀]; exact hyt₀)
  have hstrict : ∀ s : Mask, s ≠ s₀ →
      let term := twCoeff s (maskXor s r₀) * x.coeff s * y.coeff (maskXor s r₀)
      term ≠ 0 →
      ordK (twCoeff s₀ (maskXor s₀ r₀) * x.coeff s₀ * y.coeff (maskXor s₀ r₀)) < ordK term := by
    intro s hne term hterm
    have hxs : x.coeff s ≠ 0 := fun h0 => hterm (by simp [term, h0])
    have hys : y.coeff (maskXor s r₀) ≠ 0 := fun h0 => hterm (by simp [term, h0])
    have hs_mem : s ∈ sx := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxs⟩
    have ht_mem : maskXor s r₀ ∈ sy := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hys⟩
    have hlt_x : dblVal x s₀ < dblVal x s :=
      lt_of_le_of_ne (hminx s hs_mem) (fun h => hne (dblVal_inj x h).symm)
    have hle_y : dblVal y (maskXor s₀ r₀) ≤ dblVal y (maskXor s r₀) := by
      rw [hr₀_s₀]; exact hminy _ ht_mem
    have hlt_sum : dblVal x s₀ + dblVal y (maskXor s₀ r₀) < dblVal x s + dblVal y (maskXor s r₀) :=
      add_lt_add_of_lt_of_le hlt_x hle_y
    rw [← hterm_val s₀ hxs₀ (by rw [hr₀_s₀]; exact hyt₀), ← hterm_val s hxs hys] at hlt_sum
    have h2lt : 2 • ordK (twCoeff s₀ (maskXor s₀ r₀) * x.coeff s₀ * y.coeff (maskXor s₀ r₀)) <
        2 • ordK term := lt_of_add_lt_add_right hlt_sum
    by_contra hnot
    have hge : ordK term ≤ ordK (twCoeff s₀ (maskXor s₀ r₀) * x.coeff s₀ * y.coeff (maskXor s₀ r₀)) :=
      le_of_not_gt hnot
    have h2ge : 2 • ordK term ≤ 2 • ordK (twCoeff s₀ (maskXor s₀ r₀) * x.coeff s₀ * y.coeff (maskXor s₀ r₀)) :=
      nsmul_le_nsmul_right hge 2
    exact not_lt_of_ge h2ge h2lt
  intro hxy0
  have hcoeff0 : (K.toH ((x * y).coeff r₀)).coeff
      (ordK (twCoeff s₀ (maskXor s₀ r₀) * x.coeff s₀ * y.coeff (maskXor s₀ r₀))) = 0 := by
    rw [hxy0, tw_zero_coeff, map_zero]; simp
  rw [tw_mul_coeff] at hcoeff0
  have hsum_coe : K.toH (∑ s : Mask, twCoeff s (maskXor s r₀) * x.coeff s * y.coeff (maskXor s r₀)) =
      ∑ s : Mask, K.toH (twCoeff s (maskXor s r₀) * x.coeff s * y.coeff (maskXor s r₀)) :=
    map_sum K.toH _ _
  rw [hsum_coe, hahn_coeff_sum, Finset.sum_eq_single s₀] at hcoeff0
  · dsimp only [ordK] at hcoeff0
    rw [← HahnSeries.leadingCoeff_eq] at hcoeff0
    exact (HahnSeries.leadingCoeff_ne_zero.mpr (K.toH_ne_zero hterm_s₀_ne)) hcoeff0
  · intro s _ hne
    by_cases hterm : twCoeff s (maskXor s r₀) * x.coeff s * y.coeff (maskXor s r₀) = 0
    · simp [hterm]
    · exact HahnSeries.coeff_eq_zero_of_lt_order (hstrict s hne hterm)
  · intro h; exact absurd (Finset.mem_univ _) h

/- ### Section 7: Even Subalgebra `EvenCl`, Lift from `CliffordAlgebra.even`, and Part 4 -/

private noncomputable def EvenCl : Subalgebra K TwistedCl where
  carrier := {x : TwistedCl | ∀ s : Mask, maskParity s = 1 → x.coeff s = 0}
  mul_mem' := by
    intro x y hx hy r hr
    rw [tw_mul_coeff]
    refine Finset.sum_eq_zero fun s _ => ?_
    have hpar : maskParity s + maskParity (maskXor s r) = 1 := by
      rw [← maskParity_xor, ← maskXor_assoc, maskXor_self, maskXor_zero_left, hr]
    by_cases hs : maskParity s = 1
    · simp [hx s hs]
    · have hs0 : maskParity s = 0 := (zmod2_eq_zero_or_one (maskParity s)).resolve_right hs
      rw [hs0, zero_add] at hpar
      simp [hy _ hpar]
  one_mem' := by
    intro s hs
    have hne : s ≠ maskZero := by
      intro h; rw [h, maskParity_zero] at hs; exact zero_ne_one hs
    simp [tw_one_coeff, hne]
  add_mem' := fun hx hy s hs => by simp [tw_add_coeff, hx s hs, hy s hs]
  zero_mem' := fun s _ => rfl
  algebraMap_mem' := fun c s hs => by
    have hne : s ≠ maskZero := by
      intro h; rw [h, maskParity_zero] at hs; exact zero_ne_one hs
    show (c • (1 : TwistedCl)).coeff s = 0
    simp [tw_smul_coeff, tw_one_coeff, hne]

private abbrev EvenMask := {s : Mask // maskParity s = 0}

private lemma card_EvenMask : Fintype.card EvenMask = 256 := by
  let eEven : EvenMask ≃ (Fin 8 → Bool) :=
    { toFun := fun s i => s.1 i.castSucc
      invFun := fun f =>
        ⟨fun i => if h : i.1 < 8 then f ⟨i.1, h⟩
          else decide ((∑ j : Fin 8, if f j then (1 : ZMod 2) else 0) = 1), by
          rw [maskParity, Fin.sum_univ_castSucc]
          have h1 : (∑ j : Fin 8, if (if h : (j.castSucc : Fin 9).1 < 8 then f ⟨(j.castSucc : Fin 9).1, h⟩
              else decide ((∑ m : Fin 8, if f m then (1 : ZMod 2) else 0) = 1)) = true
              then (1 : ZMod 2) else 0) = ∑ j : Fin 8, if f j then (1 : ZMod 2) else 0 := by
            refine Finset.sum_congr rfl fun j _ => ?_
            simp [Fin.is_lt]
          rw [h1]
          have hlast : ¬ ((Fin.last 8 : Fin 9).1 < 8) := by simp
          simp only [dif_neg hlast]
          rcases zmod2_eq_zero_or_one (∑ j : Fin 8, if f j then (1 : ZMod 2) else 0) with hS | hS
          · rw [hS]; decide
          · rw [hS]; decide⟩
      left_inv := fun ⟨s, hs⟩ => by
        apply Subtype.ext
        funext i
        by_cases h : i.1 < 8
        · simp [h]
        · have hi8 : i = Fin.last 8 := Fin.ext (by simp [Fin.last]; omega)
          subst hi8
          simp only [dif_neg h]
          have hpar := hs
          rw [maskParity, Fin.sum_univ_castSucc] at hpar
          cases hs8 : s (Fin.last 8)
          · simp only [hs8, Bool.false_eq_true, ↓reduceIte, add_zero] at hpar
            simp [hpar]
          · simp only [hs8, ↓reduceIte] at hpar
            have hS1 : (∑ j : Fin 8, if s j.castSucc then (1 : ZMod 2) else 0) = 1 := by
              rcases zmod2_eq_zero_or_one (∑ j : Fin 8, if s j.castSucc then (1 : ZMod 2) else 0) with h0 | h1
              · rw [h0, zero_add] at hpar; exact absurd hpar one_ne_zero
              · exact h1
            simp [hS1]
      right_inv := fun f => funext fun j => by simp [Fin.is_lt] }
  rw [Fintype.card_congr eEven, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  norm_num

private noncomputable def evenClEquiv : EvenCl ≃ₗ[K] (EvenMask → K) where
  toFun x s := x.1.coeff s.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f :=
    ⟨⟨fun s => if h : maskParity s = 0 then f ⟨s, h⟩ else 0⟩, by
      intro s hs
      have hne : maskParity s ≠ 0 := by rw [hs]; exact one_ne_zero
      simp [hne]⟩
  left_inv x := by
    apply Subtype.ext; apply TwistedCl.ext; funext s
    by_cases h : maskParity s = 0
    · simp [h]
    · have h1 : maskParity s = 1 := (zmod2_eq_zero_or_one (maskParity s)).resolve_left h
      simp [h, x.2 s h1]
  right_inv f := by
    funext ⟨s, hs⟩; simp [hs]

private lemma finrank_EvenCl : Module.finrank K EvenCl = 256 := by
  rw [evenClEquiv.finrank_eq, Module.finrank_pi, card_EvenMask]

private noncomputable def twIota : (Fin 9 → K) →ₗ[K] TwistedCl where
  toFun v := ∑ i : Fin 9, v i • twBasis (maskSingle i)
  map_add' v w := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul]

private lemma twIota_mul_self (v : Fin 9 → K) :
    twIota v * twIota v = algebraMap K TwistedCl (QuadraticMap.weightedSumSquares K aK v) := by
  have hQ : QuadraticMap.weightedSumSquares K aK v = ∑ i : Fin 9, aK i * v i ^ 2 := by
    simp [QuadraticMap.weightedSumSquares_apply, sq, mul_comm]
  rw [hQ]
  simp only [twIota, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  let F : Fin 9 → Fin 9 → TwistedCl := fun i j =>
    (v i * v j * twCoeff (maskSingle i) (maskSingle j)) •
      twBasis (maskXor (maskSingle i) (maskSingle j))
  have hterm : ∀ i j : Fin 9,
      (v i • twBasis (maskSingle i)) * (v j • twBasis (maskSingle j)) = F i j := by
    intro i j
    simp only [F]
    rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, twBasis_mul, smul_smul, smul_smul, mul_assoc]
  simp_rw [hterm]
  have h2ne : (2 : K) ≠ 0 := NeZero.ne (2 : K)
  let S : TwistedCl := ∑ i : Fin 9, ∑ j : Fin 9, F i j
  let R : TwistedCl := algebraMap K TwistedCl (∑ i : Fin 9, aK i * v i ^ 2)
  change S = R
  have h2S : (2 : K) • S = (2 : K) • R := by
    have hadd : (2 : K) • S = S + S := by rw [two_smul]
    rw [hadd]
    have hswap : S = ∑ i : Fin 9, ∑ j : Fin 9, F j i := Finset.sum_comm
    calc S + S
        = (∑ i : Fin 9, ∑ j : Fin 9, F i j) + (∑ i : Fin 9, ∑ j : Fin 9, F j i) := by
          conv_rhs => rw [← hswap]
      _ = ∑ i : Fin 9, ∑ j : Fin 9, (F i j + F j i) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => (Finset.sum_add_distrib).symm
      _ = ∑ i : Fin 9, (2 : K) • ((aK i * v i ^ 2) • (1 : TwistedCl)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_eq_single i]
          · simp only [F, twCoeff_single_self, maskXor_self, twBasis_zero, ← add_smul, smul_smul]
            congr 1; ring
          · intro j _ hji
            simp only [F]
            rcases lt_or_gt_of_ne hji with hlt | hgt
            · rw [twCoeff_single_gt hlt, twCoeff_single_lt hlt,
                maskXor_comm (maskSingle j) (maskSingle i), ← add_smul]
              have h0 : v i * v j * -1 + v j * v i * 1 = 0 := by ring
              rw [h0, zero_smul]
            · rw [twCoeff_single_lt hgt, twCoeff_single_gt hgt,
                maskXor_comm (maskSingle j) (maskSingle i), ← add_smul]
              have h0 : v i * v j * 1 + v j * v i * -1 = 0 := by ring
              rw [h0, zero_smul]
          · intro h; exact absurd (Finset.mem_univ _) h
      _ = (2 : K) • R := by
          rw [← Finset.smul_sum]
          congr 1
          simp only [R, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Algebra.algebraMap_eq_smul_one]
  calc S = (2 : K)⁻¹ • ((2 : K) • S) := by rw [smul_smul, inv_mul_cancel₀ h2ne, one_smul]
    _ = (2 : K)⁻¹ • ((2 : K) • R) := by rw [h2S]
    _ = R := by rw [smul_smul, inv_mul_cancel₀ h2ne, one_smul]

private lemma twIota_mul_mem_EvenCl (v w : Fin 9 → K) : twIota v * twIota w ∈ EvenCl := by
  intro r hr
  simp only [twIota, LinearMap.coe_mk, AddHom.coe_mk]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [tw_sum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [tw_sum_coeff]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Algebra.smul_mul_assoc, Algebra.mul_smul_comm, twBasis_mul, smul_smul, smul_smul,
    tw_smul_coeff]
  have hne : r ≠ maskXor (maskSingle i) (maskSingle j) := by
    intro h
    rw [h, maskParity_xor, maskParity_single, maskParity_single] at hr
    exact absurd hr (by decide)
  simp [twBasis, hne]

private noncomputable def evenHomTw :
    CliffordAlgebra.EvenHom (QuadraticMap.weightedSumSquares K aK) EvenCl where
  bilin := LinearMap.mk₂ K (fun v w => ⟨twIota v * twIota w, twIota_mul_mem_EvenCl v w⟩)
    (fun v₁ v₂ w => Subtype.ext (by simp [map_add, add_mul]))
    (fun c v w => Subtype.ext (by simp [map_smul, Algebra.smul_mul_assoc]))
    (fun v w₁ w₂ => Subtype.ext (by simp [map_add, mul_add]))
    (fun c v w => Subtype.ext (by simp [map_smul, Algebra.mul_smul_comm]))
  contract v := Subtype.ext (twIota_mul_self v)
  contract_mid u v w := Subtype.ext (by
    change twIota u * twIota v * (twIota v * twIota w) =
      QuadraticMap.weightedSumSquares K aK v • (twIota u * twIota w)
    calc twIota u * twIota v * (twIota v * twIota w)
        = twIota u * (twIota v * twIota v) * twIota w := by simp only [mul_assoc]
      _ = twIota u * algebraMap K TwistedCl (QuadraticMap.weightedSumSquares K aK v) * twIota w := by
          rw [twIota_mul_self]
      _ = algebraMap K TwistedCl (QuadraticMap.weightedSumSquares K aK v) * (twIota u * twIota w) := by
          rw [← Algebra.commutes, mul_assoc]
      _ = QuadraticMap.weightedSumSquares K aK v • (twIota u * twIota w) := by
          rw [Algebra.smul_def])

private noncomputable def phiEven :
    CliffordAlgebra.even (QuadraticMap.weightedSumSquares K aK) →ₐ[K] EvenCl :=
  CliffordAlgebra.even.lift _ evenHomTw

private lemma phiEven_pair (i j : Fin 9) (hij : i < j) :
    (phiEven ((CliffordAlgebra.even.ι (QuadraticMap.weightedSumSquares K aK)).bilin
      (Pi.single i 1) (Pi.single j 1)) : TwistedCl) =
      twBasis (maskXor (maskSingle i) (maskSingle j)) := by
  have h1 : phiEven ((CliffordAlgebra.even.ι (QuadraticMap.weightedSumSquares K aK)).bilin
      (Pi.single i 1) (Pi.single j 1)) =
      evenHomTw.bilin (Pi.single i 1) (Pi.single j 1) :=
    CliffordAlgebra.even.lift_ι _ evenHomTw (Pi.single i 1) (Pi.single j 1)
  rw [h1]
  change twIota (Pi.single i 1) * twIota (Pi.single j 1) = _
  have hi : twIota (Pi.single i 1) = twBasis (maskSingle i) := by
    simp only [twIota, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single i]
    · simp
    · intro m _ hm; simp [hm]
    · intro h; exact absurd (Finset.mem_univ _) h
  have hj : twIota (Pi.single j 1) = twBasis (maskSingle j) := by
    simp only [twIota, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single j]
    · simp
    · intro m _ hm; simp [hm]
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hi, hj, twBasis_mul, twCoeff_single_lt hij, one_smul]

private lemma twCoeff_ordered_pair (s : Mask) {i j : Fin 9} (hij : i < j)
    (hs : ∀ m : Fin 9, s m = true → j < m) :
    twCoeff (maskXor (maskSingle i) (maskSingle j)) s = 1 := by
  have hs_ne : s i = false ∧ s j = false := by
    constructor
    · cases h : s i
      · rfl
      · exfalso; exact lt_asymm hij (hs i h)
    · cases h : s j
      · rfl
      · exfalso; exact lt_irrefl j (hs j h)
  have hsign : signFactor (maskXor (maskSingle i) (maskSingle j)) s = 1 := by
    refine Finset.prod_eq_one fun p _ => ?_
    split_ifs with h
    · exfalso
      obtain ⟨hlt, h1, h2⟩ := h
      have hgt : j < p.2 := hs p.2 h2
      have hp1 : p.1 = i ∨ p.1 = j := by
        simp only [maskXor, maskSingle] at h1
        by_cases hi : p.1 = i
        · exact Or.inl hi
        · by_cases hj : p.1 = j
          · exact Or.inr hj
          · simp [hi, hj] at h1
      rcases hp1 with rfl | rfl
      · exact lt_asymm (lt_trans hij hgt) hlt
      · exact lt_asymm hgt hlt
    · rfl
  have hdiag : diagFactor (maskXor (maskSingle i) (maskSingle j)) s = 1 := by
    refine Finset.prod_eq_one fun m _ => ?_
    split_ifs with h
    · exfalso
      obtain ⟨h1, h2⟩ := h
      have hgt : j < m := hs m h2
      simp only [maskXor, maskSingle] at h1
      have hne1 : m ≠ i := (lt_trans hij hgt).ne'
      have hne2 : m ≠ j := hgt.ne'
      simp [hne1, hne2] at h1
    · rfl
  rw [twCoeff, hsign, hdiag, one_mul]

private lemma twBasis_mem_range_phiEven_aux :
    ∀ l : List (Fin 9), l.Pairwise (· < ·) → Even l.length →
      ∃ x : CliffordAlgebra.even (QuadraticMap.weightedSumSquares K aK),
        (phiEven x : TwistedCl) = twBasis (fun i => decide (i ∈ l))
  | [], _, _ => ⟨1, by rw [map_one]; rfl⟩
  | [_], _, hev => by simp at hev
  | i :: j :: rest, hpair, hev => by
    have hij : i < j := (List.pairwise_cons.mp hpair).1 j (List.mem_cons_self ..)
    have hrest_gt : ∀ m ∈ rest, j < m := fun m hm =>
      (List.pairwise_cons.mp (List.pairwise_cons.mp hpair).2).1 m hm
    have hrest_pair : rest.Pairwise (· < ·) :=
      (List.pairwise_cons.mp (List.pairwise_cons.mp hpair).2).2
    have hrest_ev : Even rest.length := by
      simp only [List.length_cons] at hev
      obtain ⟨k, hk⟩ := hev
      exact ⟨k - 1, by omega⟩
    obtain ⟨xrest, hxrest⟩ := twBasis_mem_range_phiEven_aux rest hrest_pair hrest_ev
    let xpair := (CliffordAlgebra.even.ι (QuadraticMap.weightedSumSquares K aK)).bilin
      (Pi.single i 1) (Pi.single j 1)
    refine ⟨xpair * xrest, ?_⟩
    rw [map_mul]
    change (phiEven xpair : TwistedCl) * (phiEven xrest : TwistedCl) = _
    rw [phiEven_pair i j hij, hxrest, twBasis_mul]
    have hcoeff : twCoeff (maskXor (maskSingle i) (maskSingle j))
        (fun m => decide (m ∈ rest)) = 1 :=
      twCoeff_ordered_pair _ hij (fun m hm => hrest_gt m (of_decide_eq_true hm))
    rw [hcoeff, one_smul]
    congr 1
    funext m
    simp only [maskXor, maskSingle, List.mem_cons]
    have hij_ne : i ≠ j := hij.ne
    have hi_not : i ∉ rest := fun h => lt_asymm hij (hrest_gt i h)
    have hj_not : j ∉ rest := fun h => lt_irrefl j (hrest_gt j h)
    by_cases hmi : m = i
    · simp [hmi, hij_ne, hi_not]
    · by_cases hmj : m = j
      · simp [hmj, hij_ne.symm, hj_not]
      · simp [hmi, hmj]

private lemma twBasis_mem_range_phiEven (s : Mask) (hs : maskParity s = 0) :
    ∃ x : CliffordAlgebra.even (QuadraticMap.weightedSumSquares K aK),
      (phiEven x : TwistedCl) = twBasis s := by
  let L : List (Fin 9) := (List.finRange 9).filter (fun i => s i)
  have hsorted : L.Pairwise (· < ·) :=
    (List.pairwise_lt_finRange 9).filter _
  have hmemL : ∀ i : Fin 9, i ∈ L ↔ s i = true := by
    intro i; simp [L]
  have hcard : L.length = (Finset.univ.filter (fun i : Fin 9 => s i = true)).card := by
    have hnodup : L.Nodup := (List.nodup_finRange 9).filter _
    rw [← List.toFinset_card_of_nodup hnodup]
    congr 1
    ext i; simp [L]
  have heven : Even L.length := by
    have hpar : maskParity s = ((Finset.univ.filter (fun i : Fin 9 => s i = true)).card : ZMod 2) := by
      simp [maskParity]
    rw [hs] at hpar
    have hdvd : (2 : ℕ) ∣ (Finset.univ.filter (fun i : Fin 9 => s i = true)).card := by
      exact (ZMod.natCast_eq_zero_iff _ 2).mp hpar.symm
    rw [hcard]
    exact even_iff_two_dvd.mpr hdvd
  obtain ⟨x, hx⟩ := twBasis_mem_range_phiEven_aux L hsorted heven
  refine ⟨x, ?_⟩
  rw [hx]
  congr 1; funext i
  by_cases hsi : s i = true
  · simp [hsi, hmemL]
  · have hsf : s i = false := Bool.eq_false_iff.mpr hsi
    simp [hsf, hmemL]

private lemma phiEven_surjective : Function.Surjective phiEven := by
  intro y
  have hy : (y : TwistedCl) = ∑ s : EvenMask, (y.1.coeff s.1) • twBasis s.1 := by
    apply TwistedCl.ext; funext r
    rw [tw_sum_coeff]
    by_cases hr : maskParity r = 0
    · rw [Finset.sum_eq_single ⟨r, hr⟩]
      · simp [tw_smul_coeff, twBasis]
      · intro s _ hsr
        have hne : r ≠ s.1 := fun h => hsr (Subtype.ext h.symm)
        simp [tw_smul_coeff, twBasis, hne]
      · intro h; exact absurd (Finset.mem_univ _) h
    · have hr1 : maskParity r = 1 := (zmod2_eq_zero_or_one (maskParity r)).resolve_left hr
      rw [y.2 r hr1]
      symm
      refine Finset.sum_eq_zero fun s _ => ?_
      have hne : r ≠ s.1 := fun h => hr (h ▸ s.2)
      simp [tw_smul_coeff, twBasis, hne]
  have hgen : ∀ s : EvenMask, ∃ x : CliffordAlgebra.even (QuadraticMap.weightedSumSquares K aK),
      (phiEven x : TwistedCl) = twBasis s.1 := fun s => twBasis_mem_range_phiEven s.1 s.2
  choose xs hxs using hgen
  refine ⟨∑ s : EvenMask, (y.1.coeff s.1) • xs s, ?_⟩
  apply Subtype.ext
  rw [map_sum, AddSubmonoidClass.coe_finsetSum]
  simp_rw [map_smul]
  have hcoe_smul : ∀ s : EvenMask, ((y.1.coeff s.1 • phiEven (xs s) : EvenCl) : TwistedCl) =
      y.1.coeff s.1 • (phiEven (xs s) : TwistedCl) := fun _ => rfl
  simp_rw [hcoe_smul, hxs]
  exact hy.symm

private lemma clifford_not_iso_matrix_quat (p q : K) (_hp : p ≠ 0) (_hq : q ≠ 0) :
    IsEmpty (CliffordAlgebra.even (QuadraticMap.weightedSumSquares K aK) ≃ₐ[K]
      Matrix (Fin 8) (Fin 8) (QuaternionAlgebra K p 0 q)) := by
  refine ⟨fun e => ?_⟩
  let Ψ : Matrix (Fin 8) (Fin 8) (QuaternionAlgebra K p 0 q) →ₐ[K] EvenCl :=
    phiEven.comp e.symm.toAlgHom
  have hΨ_surj : Function.Surjective Ψ.toLinearMap :=
    phiEven_surjective.comp e.symm.surjective
  have : FiniteDimensional K EvenCl := evenClEquiv.symm.finiteDimensional
  have hdim_mat : Module.finrank K (Matrix (Fin 8) (Fin 8) (QuaternionAlgebra K p 0 q)) = 256 := by
    rw [Module.finrank_matrix, QuaternionAlgebra.finrank_eq_four]
    norm_num
  have hΨ_inj : Function.Injective Ψ := by
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (hdim_mat.trans finrank_EvenCl.symm)).mpr hΨ_surj
  let E0 : Matrix (Fin 8) (Fin 8) (QuaternionAlgebra K p 0 q) := Matrix.single 0 0 1
  let E1 : Matrix (Fin 8) (Fin 8) (QuaternionAlgebra K p 0 q) := Matrix.single 1 1 1
  have hE0 : E0 ≠ 0 := by
    intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [E0] at h00
  have hE1 : E1 ≠ 0 := by
    intro h
    have h11 := congrFun (congrFun h 1) 1
    simp [E1] at h11
  have hE01 : E0 * E1 = 0 := by
    apply Matrix.ext; intro i j
    simp only [E0, E1, Matrix.mul_apply, Matrix.single, Matrix.zero_apply, Matrix.of_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk0 : (0 : Fin 8) = k
    · have hk1 : (1 : Fin 8) ≠ k := by rw [← hk0]; decide
      simp [hk1]
    · simp [hk0]
  have hΨ0 : (Ψ E0 : TwistedCl) ≠ 0 := by
    intro h
    exact hE0 (hΨ_inj (by rw [map_zero]; exact Subtype.ext h))
  have hΨ1 : (Ψ E1 : TwistedCl) ≠ 0 := by
    intro h
    exact hE1 (hΨ_inj (by rw [map_zero]; exact Subtype.ext h))
  have hmul0 : (Ψ E0 : TwistedCl) * (Ψ E1 : TwistedCl) = 0 := by
    have h := congrArg (fun z : EvenCl => (z : TwistedCl)) (congrArg Ψ hE01)
    simpa [map_mul, map_zero] using h
  exact twistedCl_mul_ne_zero hΨ0 hΨ1 hmul0

private theorem main_H1 :
    OMA.R_KaplanskyUInvariant_u_invariant_values_variants_nine_R1.H1 :=
  ⟨K, inferInstance, inferInstance, inferInstance, aK,
    aK_ne_zero, aK_anisotropic, not_pfister4_neighbor, clifford_not_iso_matrix_quat⟩

end KaplanskyNineH1Proof

theorem OMA.solution : OMA.R_KaplanskyUInvariant_u_invariant_values_variants_nine_R1.H1 :=
  KaplanskyNineH1Proof.main_H1
