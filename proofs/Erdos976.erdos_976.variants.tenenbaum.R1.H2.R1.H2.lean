import OMAReductions.R_Erdos976_erdos_976_variants_tenenbaum_R1_H2_R1
import Mathlib

/-! The Hall–Tenenbaum weighted divisor-window moment for the root counts of an
irreducible integer polynomial. The finite prime recurrence bounds the mixed
terms using shifted divisor windows. A comparison for its derivative gives the
squarefree moment. A convergent squarefull Euler product recovers all moduli.
The positive mean supplies both the unweighted Dirichlet bound and the sharp
logarithmically weighted prime bound by tilting the series at two nearby points.

G. Tenenbaum, “Sur une question d’Erdős et Schinzel, II”, Invent. Math. 99
(1990), especially §2 and the moment estimate (2.14). The arithmetic proof of
the positive mean and uniform prime-power bounds is reproduced from JaviSoto,
Open Math Agents #12593. The companion deterministic window estimates appear in
romechenko’s #16801. -/

section
namespace OMA.Kummer975

open Polynomial NumberField Ideal
open scoped NumberField

private noncomputable def linearFactorEquiv {F : Type*} [Field F] [DecidableEq F] (g : F[X]) (hg : g ≠ 0) :
    {r : F // g.IsRoot r} ≃
      {Q : (UniqueFactorizationMonoid.normalizedFactors g).toFinset // Q.val.natDegree = 1} where
  toFun r := ⟨⟨X - C r.val, by
    rw [Multiset.mem_toFinset, Polynomial.mem_normalizedFactors_iff hg]
    exact ⟨irreducible_X_sub_C _, monic_X_sub_C _, dvd_iff_isRoot.mpr r.property⟩⟩,
      natDegree_X_sub_C _⟩
  invFun Q := ⟨-Q.val.val.coeff 0, by
    obtain ⟨_, hm, hd⟩ := (Polynomial.mem_normalizedFactors_iff hg).mp
      (Multiset.mem_toFinset.mp Q.val.property)
    have e := eq_X_add_C_of_degree_eq_one
      ((degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 1)).mpr Q.property)
    apply dvd_iff_isRoot.mp
    convert! hd using 1
    simp [hm.leadingCoeff] at e
    simpa using e.symm⟩
  left_inv r := by ext; simp
  right_inv Q := by
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨_, hm, _⟩ := (Polynomial.mem_normalizedFactors_iff hg).mp
      (Multiset.mem_toFinset.mp Q.val.property)
    simpa [hm.leadingCoeff] using (eq_X_add_C_of_degree_eq_one
      ((degree_eq_iff_natDegree_eq_of_pos (by decide : 0 < 1)).mpr Q.property)).symm

private def primesEquiv {K : Type*} [Field K] [NumberField K] (p : ℕ) (hp : p.Prime) :
    {P : Ideal.primesOver (Ideal.span {(p : ℤ)}) (𝓞 K) // P.val.inertiaDeg ℤ = 1} ≃
      {P : Ideal (𝓞 K) // P.absNorm = p} where
  toFun P := ⟨P.val.val, by
    have : P.val.val.IsPrime := P.val.property.1
    have : P.val.val.LiesOver (Ideal.span {(p : ℤ)}) := P.val.property.2
    simpa [P.property] using (Ideal.natAbs_pow_inertiaDeg (p : ℤ) P.val.val).symm⟩
  invFun P := by
    have hprime : P.val.absNorm.Prime := P.property.symm ▸ hp
    have : P.val.IsPrime := Ideal.isPrime_of_irreducible_absNorm hprime
    have : P.val.LiesOver (Ideal.span {(p : ℤ)}) :=
      ⟨by simpa only [P.property] using Ideal.span_singleton_absNorm hprime⟩
    refine ⟨⟨P.val, inferInstance, inferInstance⟩, ?_⟩
    apply (Nat.pow_right_injective hp.one_lt)
    simpa [P.property] using Ideal.natAbs_pow_inertiaDeg (p : ℤ) P.val
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable def rootIdealEquiv {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K)
    (p : ℕ) [hp : Fact p.Prime] (good : ¬ p ∣ RingOfIntegers.exponent θ) :
    {r : ZMod p // ((minpoly ℤ θ).map (Int.castRingHom (ZMod p))).IsRoot r} ≃
      {P : Ideal (𝓞 K) // P.absNorm = p} := by
  classical
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod good
  apply (linearFactorEquiv _ (Polynomial.map_monic_ne_zero (minpoly.monic θ.isIntegral))).trans
  apply Equiv.trans _ (primesEquiv p hp.out)
  refine Equiv.subtypeEquiv e.symm (fun Q => ?_)
  rw [NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply' good Q.property]

open Filter
open scoped Topology

/-- Landau's ideal-count asymptotic, with the count grouped by its positive norm.
The reindexing follows Mathlib's proof of the Dirichlet class number formula. -/
lemma coefficient_mean (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun N : ℕ => (∑ n ∈ Finset.Icc 1 N,
      (Nat.card {I : Ideal (𝓞 K) // I.absNorm = n} : ℝ)) / N)
      atTop (𝓝 (NumberField.dedekindZeta_residue K)) := by
  refine ((NumberField.Ideal.tendsto_norm_le_div_atTop₀ K).comp
    tendsto_natCast_atTop_atTop).congr fun n => ?_
  simp only [Function.comp_apply, Nat.cast_le, ← Nat.cast_sum]
  congr
  rw [← add_left_inj 1, ← Ideal.card_norm_le_eq_card_norm_le_add_one,
    show Finset.Icc 1 n = Finset.Ioc 0 n from Finset.Icc_succ_left_eq_Ioc _ _,
    show 1 = Nat.card {I : Ideal (𝓞 K) // I.absNorm = 0} by simp [Ideal.absNorm_eq_zero_iff],
    Finset.sum_Ioc_add_eq_sum_Icc n.zero_le,
    ← Finset.card_preimage_eq_sum_card_image_eq (fun k _ => Ideal.finite_setOfPred_absNorm_eq k)]
  simp [Set.coe_eq_subtype]

end OMA.Kummer975
end

section
namespace OMA.Field975

open Polynomial NumberField
open scoped NumberField

/-- Changing variables by a unit identifies the integral normalization over the rationals. -/
theorem irreducible_normalization (f : ℤ[X]) (hf : Irreducible f) (hd : 0 < f.natDegree) :
    Irreducible (f.integralNormalization.map (Int.castRingHom ℚ)) := by
  let a : ℚ := f.leadingCoeff
  have ha : a ≠ 0 := by dsimp [a]; exact_mod_cast leadingCoeff_ne_zero.mpr hf.ne_zero
  let : Invertible a := invertibleOfNonzero ha
  let e := Polynomial.algEquivCMulXAddC a 0
  apply (MulEquiv.irreducible_iff e).mp
  have he : e (f.integralNormalization.map (Int.castRingHom ℚ)) =
      C (a ^ (f.natDegree - 1)) * f.map (Int.castRingHom ℚ) := by
    simp only [e, algEquivCMulXAddC_apply, map_zero, add_zero, ← comp_eq_aeval]
    ext j
    simp only [comp_C_mul_X_coeff, coeff_map, coeff_C_mul, Int.coe_castRingHom, a]
    rw [mul_comm ((f.leadingCoeff : ℚ) ^ _) _]
    exact_mod_cast f.integralNormalization_coeff_mul_leadingCoeff_pow j hd
  rw [he]
  apply (irreducible_isUnit_mul ((isUnit_iff_ne_zero.mpr (pow_ne_zero _ ha)).map C)).mpr
  exact (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hf.isPrimitive hd.ne')).mp hf

noncomputable def scaledRoots (f : ℤ[X]) (hd : 0 < f.natDegree) (p : ℕ) [Fact p.Prime]
    (good : (f.leadingCoeff : ZMod p) ≠ 0) :
    {r : ZMod p // (f.map (Int.castRingHom (ZMod p))).IsRoot r} ≃
      {r : ZMod p // (f.integralNormalization.map (Int.castRingHom (ZMod p))).IsRoot r} := by
  apply Equiv.subtypeEquiv (Equiv.mulLeft₀ (f.leadingCoeff : ZMod p) good)
  intro r
  simp only [Polynomial.IsRoot, eval_map, Equiv.mulLeft₀_apply]
  rw [show (f.leadingCoeff : ZMod p) = (Int.castRingHom (ZMod p)) f.leadingCoeff from rfl,
    f.integralNormalization_eval₂_leadingCoeff_mul hd]
  simp [good]

lemma exponent_pos {K : Type*} [Field K] [NumberField K] (θ : 𝓞 K)
    (hθ : (minpoly ℤ θ).natDegree = Module.finrank ℚ K) :
    0 < RingOfIntegers.exponent θ := by
  let A := Algebra.adjoin ℤ ({θ} : Set (𝓞 K))
  have hfull : Module.finrank ℤ A.toSubmodule = Module.finrank ℤ (𝓞 K) := by
    change Module.finrank ℤ (Algebra.adjoin ℤ ({θ} : Set (𝓞 K))) = _
    rw [(Algebra.adjoin.powerBasis' θ.isIntegral).finrank, Algebra.adjoin.powerBasis'_dim,
      hθ, RingOfIntegers.rank]
  let U := (𝓞 K) ⧸ A.toSubmodule
  have : Finite U := Submodule.finiteQuotientOfFreeOfRankEq _ hfull
  let m := Nat.card U
  have hm : 0 < m := Nat.card_pos
  have hmθ : (m : 𝓞 K) ∈ conductor ℤ θ := by
    apply mem_conductor_iff.mpr
    intro b
    change (m : 𝓞 K) * b ∈ A.toSubmodule
    rw [← nsmul_eq_mul, ← Submodule.Quotient.mk_eq_zero]
    change A.toSubmodule.mkQ (m • b) = 0
    rw [map_nsmul]
    exact card_nsmul_eq_zero'
  rw [RingOfIntegers.exponent_eq_sInf]
  exact (Nat.sInf_mem (show {d : ℕ | 0 < d ∧ (d : 𝓞 K) ∈ conductor ℤ θ}.Nonempty from
    ⟨m, hm, hmθ⟩)).1

private lemma original_isRoot_cast (f : ℤ[X]) (p r : ℕ) :
    (f.map (Int.castRingHom (ZMod p))).IsRoot (r : ZMod p) ↔
      (p : ℤ) ∣ f.eval (r : ℤ) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Polynomial.IsRoot, eval_map]
  have he := eval₂_at_apply (p := f) (Int.castRingHom (ZMod p)) (r : ℤ)
  simpa only [Int.coe_castRingHom, Int.cast_natCast] using congrArg (· = 0) he |>.to_iff

theorem root_count (f : ℤ[X]) (p : ℕ) [NeZero p] :
    Nat.count (fun r : ℕ => (p : ℤ) ∣ f.eval (r : ℤ)) p =
      Nat.card {r : ZMod p // (f.map (Int.castRingHom (ZMod p))).IsRoot r} := by
  classical
  rw [Nat.count_eq_card_fintype]
  have aux (A : Type) (i : Fintype A) : @Fintype.card A i = Nat.card A :=
    (@Nat.card_eq_fintype_card A i).symm
  rw [aux]
  apply Nat.card_congr
  exact {
    toFun := fun r => ⟨r.val, (original_isRoot_cast f p r.val).mpr r.property.2⟩
    invFun := fun r => ⟨r.val.val, ZMod.val_lt _, (original_isRoot_cast f p _).mp
      (by simpa only [ZMod.natCast_zmod_val] using r.property)⟩
    left_inv := fun r => Subtype.ext (by simp [ZMod.val_natCast, Nat.mod_eq_of_lt r.property.1])
    right_inv := fun r => Subtype.ext (ZMod.natCast_zmod_val _)
  }

noncomputable abbrev definingPolynomial (f : ℤ[X]) := f.integralNormalization.map (Int.castRingHom ℚ)

abbrev canonicalField (f : ℤ[X]) := AdjoinRoot (definingPolynomial f)

theorem canonical_link (f : ℤ[X]) (hf : Irreducible f) (hd : 0 < f.natDegree)
    [Fact (Irreducible (definingPolynomial f))] :
    ∃ M : ℕ, 0 < M ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M →
        Nat.count (fun r : ℕ => (p : ℤ) ∣ f.eval (r : ℤ)) p =
          Nat.card {I : Ideal (𝓞 (canonicalField f)) // I.absNorm = p} := by
  let g := f.integralNormalization
  let F := g.map (Int.castRingHom ℚ)
  have irr : Irreducible F := irreducible_normalization f hf hd
  let K := AdjoinRoot F
  let x := AdjoinRoot.root F
  have mon : g.Monic := f.monic_integralNormalization hf.ne_zero
  have hx : Polynomial.aeval x g = 0 := by
    rw [← aeval_map_algebraMap ℚ]
    change Polynomial.aeval (AdjoinRoot.root F) F = 0
    rw [Polynomial.aeval_def]
    exact AdjoinRoot.eval₂_root F
  have hxint : IsIntegral ℤ x := ⟨g, mon, hx⟩
  let θ : 𝓞 K := ⟨x, hxint⟩
  have hmin : minpoly ℤ θ = g := by
    rw [← RingOfIntegers.minpoly_coe]
    apply Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective
    change (minpoly ℤ x).map (algebraMap ℤ ℚ) = F
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions' ℚ hxint]
    exact AdjoinRoot.minpoly_powerBasis_gen_of_monic (mon.map _) irr.ne_zero
  have hdeg : (minpoly ℤ θ).natDegree = Module.finrank ℚ K := by
    rw [hmin, (AdjoinRoot.powerBasis irr.ne_zero).finrank]
    exact (Polynomial.natDegree_map_eq_of_injective Int.cast_injective g).symm
  refine ⟨f.leadingCoeff.natAbs * RingOfIntegers.exponent θ,
    Nat.mul_pos (Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hf.ne_zero))
      (exponent_pos θ hdeg), ?_⟩
  intro p hp good
  let : Fact p.Prime := ⟨hp⟩
  have h1 : ¬ p ∣ f.leadingCoeff.natAbs := fun h => good (dvd_mul_of_dvd_left h _)
  have h2 : ¬ p ∣ RingOfIntegers.exponent θ := fun h => good (dvd_mul_of_dvd_right h _)
  have hnon : (f.leadingCoeff : ZMod p) ≠ 0 := by
    intro h
    exact h1 (Int.natAbs_dvd_natAbs.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp h))
  rw [root_count]
  apply Nat.card_congr
  apply (scaledRoots f hd p hnon).trans
  simpa [hmin] using OMA.Kummer975.rootIdealEquiv θ p h2

theorem field_link (f : ℤ[X]) (hf : Irreducible f) (hd : 0 < f.natDegree) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K), ∃ M : ℕ, 0 < M ∧
      ∀ p : ℕ, p.Prime → ¬ p ∣ M →
        Nat.count (fun r : ℕ => (p : ℤ) ∣ f.eval (r : ℤ)) p =
          Nat.card {I : Ideal (𝓞 K) // I.absNorm = p} := by
  let : Fact (Irreducible (definingPolynomial f)) := ⟨irreducible_normalization f hf hd⟩
  exact ⟨canonicalField f, inferInstance, inferInstance, canonical_link f hf hd⟩

end OMA.Field975
end

section
/- The ordinary root-counting function is multiplicative by the Chinese remainder
theorem.  Away from the leading coefficient, its prime values are bounded by the degree. -/
namespace OMA.RootsEuler975

open Polynomial

noncomputable def rho (f : ℤ[X]) : ArithmeticFunction ℝ :=
  ⟨fun n => (Nat.count (fun r : ℕ => (n:ℤ) ∣ f.eval (r:ℤ)) n : ℝ), by simp⟩

@[simp] theorem rho_apply (f : ℤ[X]) (n : ℕ) : rho f n =
    (Nat.count (fun r : ℕ => (n:ℤ) ∣ f.eval (r:ℤ)) n : ℝ) := rfl

@[simp] theorem rho_one (f : ℤ[X]) : rho f 1 = 1 := by simp [Nat.count_succ]

private abbrev Root (f : ℤ[X]) (n : ℕ) :=
  {x : ZMod n // (f.map (Int.castRingHom (ZMod n))).IsRoot x}

private lemma commute {R S : Type*} [CommRing R] [CommRing S] (g : R →+* S)
    (f : ℤ[X]) (x : R) :
    g ((f.map (Int.castRingHom R)).eval x) = (f.map (Int.castRingHom S)).eval (g x) := by
  simp only [eval_map, hom_eval₂]
  congr 1
  exact Subsingleton.elim ..

private noncomputable def rootsCRT (f : ℤ[X]) {m n : ℕ} (h : m.Coprime n) :
    Root f (m*n) ≃ Root f m × Root f n := by
  let e := ZMod.chineseRemainder h
  let g : ZMod (m*n) →+* ZMod m := (RingHom.fst _ _).comp e.toRingHom
  let q : ZMod (m*n) →+* ZMod n := (RingHom.snd _ _).comp e.toRingHom
  refine (Equiv.subtypeEquiv e.toEquiv ?_).trans Equiv.subtypeProdEquivProd
  intro x
  change (f.map _).eval x = 0 ↔ (f.map _).eval (g x) = 0 ∧ (f.map _).eval (q x) = 0
  rw [← commute g, ← commute q]
  constructor
  · intro hz; simp [hz]
  · intro hz
    apply e.injective
    rw [map_zero]
    exact Prod.ext hz.1 hz.2

theorem multiplicative (f : ℤ[X]) : (rho f).IsMultiplicative := by
  refine ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr ⟨rho_one f, ?_⟩
  intro m n hm hn cop
  let : NeZero m := ⟨hm⟩
  let : NeZero n := ⟨hn⟩
  simp only [rho_apply, Field975.root_count]
  exact_mod_cast (Nat.card_congr (rootsCRT f cop)).trans (Nat.card_prod ..)

theorem prime_le_degree (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (good : (f.leadingCoeff : ZMod p) ≠ 0) : rho f p ≤ f.natDegree := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let F := f.map (Int.castRingHom (ZMod p))
  have nz : F ≠ 0 := by
    intro h
    apply good
    simpa only [F,coeff_map,coeff_natDegree,Int.coe_castRingHom,coeff_zero] using
      congrArg (fun q : (ZMod p)[X] => q.coeff f.natDegree) h
  have e : Root f p ≃ ↥F.roots.toFinset :=
    Equiv.subtypeEquivRight fun x => by simp [F,mem_roots nz]
  rw [rho_apply,Field975.root_count]
  have card : Nat.card (Root f p) ≤ f.natDegree := calc
    _ = Nat.card ↥F.roots.toFinset := Nat.card_congr e
    _ = F.roots.toFinset.card := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
    _ ≤ F.roots.card := Multiset.toFinset_card_le _
    _ ≤ _ := f.card_roots_map_le_natDegree
  exact_mod_cast card

theorem prime_le_degree_of_not_dvd (f : ℤ[X]) (p : ℕ) (hp : p.Prime)
    (h : ¬ (p:ℤ) ∣ f.leadingCoeff) : rho f p ≤ f.natDegree :=
  prime_le_degree f p hp fun he => h ((ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp he)

end OMA.RootsEuler975
end

section
namespace OMA.IdealEuler975

open Finset NumberField Ideal ArithmeticFunction
open scoped NumberField Classical

noncomputable def atom (d : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≠ 0 ∧ n = d then 1 else 0, by simp⟩

lemma atom_mul (b : ArithmeticFunction ℝ) {d n : ℕ} (hd : 0 < d) (hn : 0 < n) :
    (atom d * b) n = if d ∣ n then b (n / d) else 0 := by
  classical
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal fun i j => atom d i * b j]
  have h (i : ℕ) : atom d i * b (n / i) = if i = d then b (n / d) else 0 := by
    by_cases hi : i = d <;> simp [atom, hi, hd.ne']
  simp_rw [h]
  simp [Nat.mem_divisors, hn.ne']

lemma atom_mul_atom {u v : ℕ} (hu : 0 < u) :
    atom u * atom v = atom (u*v) := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [atom_mul _ hu hn]
  by_cases hd : u ∣ n
  · obtain ⟨m, rfl⟩ := hd
    have hm : m ≠ 0 := fun h => by simp [h] at hn
    simp [atom, hu.ne', hn.ne', hm]
  · have ne : n ≠ u*v := fun h => hd ⟨v, h⟩
    simp [atom, hd, ne]

variable (K : Type*) [Field K] [NumberField K]

noncomputable def fiber (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_eq n).toFinset

lemma mem_fiber {n : ℕ} {I : Ideal (𝓞 K)} : I ∈ fiber K n ↔ I.absNorm = n := by
  simp [fiber]

noncomputable def avoid (S : Finset (Ideal (𝓞 K))) (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (fiber K n).filter fun I => ∀ P ∈ S, ¬P ∣ I

lemma mem_avoid {n : ℕ} {I : Ideal (𝓞 K)} {S : Finset (Ideal (𝓞 K))} :
    I ∈ avoid K S n ↔ I.absNorm = n ∧ ∀ P ∈ S, ¬P ∣ I := by
  simp [avoid, mem_fiber]

noncomputable def countAvoid (S : Finset (Ideal (𝓞 K))) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else (avoid K S n).card, by simp⟩

private lemma countAvoid_apply (S : Finset (Ideal (𝓞 K))) (n : ℕ) :
    countAvoid K S n = if n = 0 then (0 : ℝ) else ((avoid K S n).card : ℝ) := rfl

noncomputable abbrev a := countAvoid K ∅

lemma a_apply {n : ℕ} (hn : n ≠ 0) :
    a K n = (Nat.card {I : Ideal (𝓞 K) // I.absNorm = n} : ℝ) := by
  classical
  simp [a, countAvoid, hn, avoid, fiber]
  exact (Set.ncard_eq_toFinset_card _ _).symm

private lemma norm_pos {P : Ideal (𝓞 K)} (hP : Prime P) : 0 < P.absNorm :=
  Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)

private lemma insert_count {S : Finset (Ideal (𝓞 K))} {P : Ideal (𝓞 K)} (hP : Prime P)
    (hPS : P ∉ S) (hs : ∀ Q ∈ S, Prime Q) :
    countAvoid K (insert P S) = (1 - atom P.absNorm) * countAvoid K S := by
  classical
  ext n
  rcases Nat.eq_zero_or_pos n with rfl|hn
  · simp
  rw [sub_mul, one_mul]
  change (countAvoid K (insert P S)) n = (countAvoid K S) n - (atom P.absNorm * countAvoid K S) n
  rw [atom_mul _ (norm_pos K hP) hn]
  have split : avoid K (insert P S) n = (avoid K S n).filter (fun I => ¬ P ∣ I) := by
    ext I; simp [mem_avoid]; tauto
  simp only [countAvoid_apply, if_neg hn.ne', split]
  by_cases hd : P.absNorm ∣ n
  · have hdiv : 0 < n / P.absNorm := Nat.div_pos (Nat.le_of_dvd hn hd) (norm_pos K hP)
    simp only [if_pos hd, if_neg hdiv.ne']
    have bij : (avoid K S (n / P.absNorm)).card =
        ((avoid K S n).filter (fun I => P ∣ I)).card := by
      apply card_nbij (fun J => P * J)
      · intro J hJ
        obtain ⟨hjn, hjs⟩ := (mem_avoid K).mp hJ
        apply mem_filter.mpr
        refine ⟨(mem_avoid K).mpr ⟨by rw [map_mul, hjn, Nat.mul_div_cancel' hd], ?_⟩, dvd_mul_right _ _⟩
        intro Q hQ h
        rcases (hs Q hQ).dvd_or_dvd h with h | h
        · exact hPS (associated_iff_eq.mp ((hs Q hQ).irreducible.associated_of_dvd hP.irreducible h) ▸ hQ)
        · exact hjs Q hQ h
      · exact fun J _ J' _ hh => mul_left_cancel₀ hP.ne_zero hh
      · intro I hI
        obtain ⟨hI, J, rfl⟩ := mem_filter.mp hI
        obtain ⟨hjn, hjs⟩ := (mem_avoid K).mp hI
        refine ⟨J, (mem_avoid K).mpr ?_, rfl⟩
        refine ⟨?_, fun Q hQ h => hjs Q hQ (dvd_mul_of_dvd_right h P)⟩
        rw [← hjn, map_mul, Nat.mul_div_cancel_left _ (norm_pos K hP)]
    have cnt := (avoid K S n).card_filter_add_card_filter_not (fun I => P ∣ I)
    rw [← bij] at cnt
    linarith only [show (((avoid K S (n / P.absNorm)).card : ℝ) +
      (((avoid K S n).filter fun I => ¬P ∣ I).card : ℝ)) = (avoid K S n).card by exact_mod_cast cnt]
  · simp only [if_neg hd, sub_zero]
    norm_cast
    congr 1
    apply filter_true_of_mem
    intro I hI h
    apply hd
    rw [← ((mem_avoid K).mp hI).1]
    exact map_dvd Ideal.absNorm h

noncomputable def euler (S : Finset (Ideal (𝓞 K))) : ArithmeticFunction ℝ :=
  ∏ P ∈ S, (1 - atom P.absNorm)

private lemma sieve (S : Finset (Ideal (𝓞 K))) (hs : ∀ P ∈ S, Prime P) :
    euler K S * a K = countAvoid K S := by
  induction S using Finset.induction_on with
  | empty => simp [euler, a]
  | @insert P S hp ih =>
    rw [insert_count K (hs P (mem_insert_self ..)) hp (fun Q hQ => hs Q (mem_insert_of_mem hQ))]
    rw [← ih (fun Q hQ => hs Q (mem_insert_of_mem hQ)), ← mul_assoc]
    simp [euler, hp]

noncomputable def smallPrimes (n : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le n).toFinset.filter Prime

lemma mem_small {P : Ideal (𝓞 K)} {n : ℕ} :
    P ∈ smallPrimes K n ↔ P.absNorm ≤ n ∧ Prime P := by simp [smallPrimes]

private lemma no_large_change (S T : Finset (Ideal (𝓞 K))) (hST : S ⊆ T) {n : ℕ} (hn : 0 < n)
    (exclude : ∀ P ∈ T \ S, Prime P ∧ ¬P.absNorm ∣ n) :
    (euler K T) n = (euler K S) n := by
  have main (U : Finset (Ideal (𝓞 K))) (hU : ∀ P ∈ U, Prime P ∧ ¬P.absNorm ∣ n) :
      (euler K U * euler K S) n = euler K S n := by
    induction U using Finset.induction_on with
    | empty => simp [euler]
    | @insert P U hp ih =>
      have hP := hU P (mem_insert_self ..)
      rw [show euler K (insert P U) = (1 - atom P.absNorm) * euler K U by simp [euler, hp],
        mul_assoc, sub_mul, one_mul]
      change (euler K U * euler K S) n - (atom P.absNorm * _) n = _
      rw [atom_mul _ (norm_pos K hP.1) hn, if_neg hP.2, sub_zero]
      exact ih (fun Q hQ => hU Q (mem_insert_of_mem hQ))
  rw [← show euler K (T \ S) * euler K S = euler K T from Finset.prod_sdiff hST]
  exact main _ exclude

noncomputable def mu : ArithmeticFunction ℝ :=
  ⟨fun n => euler K (smallPrimes K n) n, by simp⟩

lemma mu_eq {n N : ℕ} (hn : n ≤ N) :
    (mu K) n = euler K (smallPrimes K N) n := by
  rcases Nat.eq_zero_or_pos n with rfl|hn'
  · simp
  symm
  exact no_large_change K _ _ (fun P hP => (mem_small K).mpr
    ⟨((mem_small K).mp hP).1.trans hn, ((mem_small K).mp hP).2⟩) hn' (by
      intro P hP
      obtain ⟨hPN,hnP⟩ := mem_sdiff.mp hP
      have hp := ((mem_small K).mp hPN).2
      exact ⟨hp, fun h => hnP ((mem_small K).mpr ⟨Nat.le_of_dvd hn' h, hp⟩)⟩)

lemma inverse : a K * mu K = 1 := by
  ext n
  rcases Nat.eq_zero_or_pos n with rfl|hn
  · simp
  rw [mul_comm]
  have h : (mu K * a K) n = (euler K (smallPrimes K n) * a K) n := by
    simp only [ArithmeticFunction.mul_apply]
    apply Finset.sum_congr rfl
    intro x hx
    rw [mu_eq K (Nat.divisor_le (Nat.fst_mem_divisors_of_mem_antidiagonal hx))]
  rw [h, sieve K _ (fun P hP => ((mem_small K).mp hP).2), countAvoid_apply, if_neg hn.ne',
    ArithmeticFunction.one_apply]
  by_cases h1 : n = 1
  · subst n
    have hsingleton : avoid K (smallPrimes K 1) 1 = {1} := by
      ext I
      rw [mem_avoid, mem_singleton, Ideal.absNorm_eq_one_iff, Ideal.one_eq_top]
      refine ⟨fun h => h.1, ?_⟩
      rintro rfl
      exact ⟨rfl, fun P hP => Ideal.one_eq_top (R:=𝓞 K) ▸ ((mem_small K).mp hP).2.not_dvd_one⟩
    simp [hsingleton]
  · rw [if_neg h1]
    suffices avoid K (smallPrimes K n) n = ∅ by simp [this]
    apply eq_empty_iff_forall_notMem.mpr
    intro I hI
    obtain ⟨he, hnop⟩ := (mem_avoid K).mp hI
    have hnunit : ¬IsUnit I := fun h => h1 (he.symm.trans (Ideal.absNorm_eq_one_iff.mpr
      (Ideal.isUnit_iff.mp h)))
    have hne : I ≠ 0 := fun e => hn.ne' (by simp [← he,e])
    obtain ⟨P, irr, dvd⟩ := WfDvdMonoid.exists_irreducible_factor hnunit hne
    exact hnop P ((mem_small K).mpr ⟨Nat.le_of_dvd hn (he ▸ map_dvd Ideal.absNorm dvd),
      UniqueFactorizationMonoid.irreducible_iff_prime.mp irr⟩) dvd

private lemma prime_dvd_factor {p n j : ℕ} (hp : p.Prime) (hn : n ≠ 1) (h : n ∣ p^j) : p ∣ n := by
  obtain ⟨k, _, rfl⟩ := (Nat.dvd_prime_pow hp).mp h
  exact dvd_pow_self _ (by intro hk; simp [hk] at hn)

private lemma factor_mult {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    (1 - atom (p^e)).IsMultiplicative := by
  let t := p^e
  have ht : 1 < t := one_lt_pow₀ hp.one_lt he.ne'
  have hval (k : ℕ) : (1 - atom t : ArithmeticFunction ℝ) k =
      (if k = 1 then 1 else 0) - (if k = t then 1 else 0) := by
    change (if k = 1 then (1:ℝ) else 0) - (if k ≠ 0 ∧ k = t then 1 else 0) = _
    by_cases h : k = t <;> simp [h, Nat.ne_zero_of_lt (zero_lt_one.trans ht)]
  have hone : (1 - atom t : ArithmeticFunction ℝ) 1 = 1 := by simp [hval, ht.ne]
  refine ⟨hone, ?_⟩
  intro m n hmn
  change (1 - atom t : ArithmeticFunction ℝ) (m*n) =
    (1 - atom t : ArithmeticFunction ℝ) m * (1 - atom t : ArithmeticFunction ℝ) n
  by_cases hm : m = 1
  · simp [hm, hone]
  by_cases hn : n = 1
  · simp [hn, hone]
  have nc : ¬(p ∣ m ∧ p ∣ n) := fun h => hp.not_dvd_one (hmn ▸ Nat.dvd_gcd h.1 h.2)
  have ne : m*n ≠ t := by
    intro eq
    exact nc ⟨prime_dvd_factor hp hm (eq ▸ dvd_mul_right m n),
      prime_dvd_factor hp hn (eq ▸ dvd_mul_left n m)⟩
  have n1 : m*n ≠ 1 := fun h => hm (Nat.dvd_one.mp (h ▸ dvd_mul_right m n))
  change (1 - atom t : ArithmeticFunction ℝ) (m*n) =
    (1 - atom t : ArithmeticFunction ℝ) m * (1 - atom t : ArithmeticFunction ℝ) n
  simp only [hval, if_neg ne, if_neg n1, if_neg hm, if_neg hn, sub_self, zero_sub, neg_mul_neg]
  by_cases h : m = t
  · have hn' : n ≠ t := fun h' => nc ⟨h ▸ dvd_pow_self _ he.ne', h' ▸ dvd_pow_self _ he.ne'⟩
    simp [hn']
  · simp [h]

lemma multiplicative : (mu K).IsMultiplicative := by
  have fm (N : ℕ) : (euler K (smallPrimes K N)).IsMultiplicative := by
    apply ArithmeticFunction.isMultiplicative_finsetProd
    intro P hP
    have hp := ((mem_small K).mp hP).2
    have : P.IsPrime := Ideal.isPrime_of_prime hp
    have : P.IsMaximal := this.isMaximal hp.ne_zero
    obtain ⟨p, d, hd, _, hprime, eq⟩ := Ideal.exists_prime_and_absNorm_eq_pow P
    rw [eq]
    exact factor_mult hprime hd
  refine ⟨(mu_eq K (le_refl 1)).trans (fm 1).1, ?_⟩
  intro m n hmn
  by_cases hm : m = 0
  · simp [hm]
  by_cases hn : n = 0
  · simp [hn]
  rw [mu_eq K (le_refl (m*n)), mu_eq K (Nat.le_mul_of_pos_right m (Nat.pos_of_ne_zero hn)),
    mu_eq K (Nat.le_mul_of_pos_left n (Nat.pos_of_ne_zero hm))]
  exact (fm (m*n)).2 hmn

open Polynomial

private lemma factors_coeff {p : ℕ} (hp : p.Prime) (e : Ideal (𝓞 K) → ℕ)
    (S : Finset (Ideal (𝓞 K))) (norms : ∀ P ∈ S, P.absNorm = p ^ e P) (k : ℕ) :
    euler K S (p^k) = (∏ P ∈ S, (1 - X ^ e P : ℝ[X])).coeff k := by
  classical
  induction S using Finset.induction_on generalizing k with
  | empty =>
    cases k with
    | zero => simp [euler]
    | succ k => simp [euler, hp.ne_one, Polynomial.coeff_one]
  | insert P S hPS ih =>
    have nt := norms P (mem_insert_self P S)
    have ns := fun Q (hQ : Q ∈ S) => norms Q (mem_insert_of_mem hQ)
    rw [show euler K (insert P S) = (1-atom P.absNorm)*euler K S by simp [euler,hPS],
      Finset.prod_insert hPS, sub_mul, one_mul, sub_mul, one_mul, coeff_sub, coeff_X_pow_mul']
    change euler K S (p^k) - (atom P.absNorm * euler K S) (p^k) = _
    rw [nt, atom_mul _ (pow_pos hp.pos _) (pow_pos hp.pos _), ih ns k]
    simp only [Nat.pow_dvd_pow_iff_le_right hp.one_lt]
    by_cases h : e P ≤ k
    · have div : p^k / p^(e P) = p^(k-e P) := by
        calc p^k / p^(e P) = (p^(k-e P)*p^e P)/p^e P := by rw [←pow_add, Nat.sub_add_cancel h]
             _ = _ := Nat.mul_div_cancel _ (pow_pos hp.pos _)
      simp only [if_pos h, div, ih ns]
    · simp only [if_neg h]

theorem «local» (p : ℕ) (hp : p.Prime) :
    ∃ L : Finset (Ideal (𝓞 K)), ∃ e : Ideal (𝓞 K) → ℕ, (∀ P ∈ L, 0 < e P) ∧
      (∑ P ∈ L, e P) ≤ Module.finrank ℚ K ∧
      ∀ k : ℕ, (mu K) (p^k) = (∏ P ∈ L, (1 - X ^ (e P) : ℝ[X])).coeff k := by
  classical
  let pI : Ideal ℤ := Ideal.span {(p : ℤ)}
  let : Fact p.Prime := ⟨hp⟩
  let : pI.IsMaximal := Int.ideal_span_isMaximal_of_prime p
  let L := Finset.univ.image (Subtype.val : pI.primesOver (𝓞 K) → Ideal (𝓞 K))
  have memL (P : Ideal (𝓞 K)) : P ∈ L ↔ P ∈ pI.primesOver (𝓞 K) := by
    constructor
    · rintro h
      obtain ⟨Q, _, rfl⟩ := mem_image.mp h
      exact Q.property
    · intro h
      exact mem_image.mpr ⟨⟨P,h⟩, mem_univ _, rfl⟩
  have normL (P : Ideal (𝓞 K)) (hP : P ∈ L) : P.absNorm = p^(P.inertiaDeg ℤ) := by
    have : P.IsPrime := ((memL P).mp hP).1
    have : P.LiesOver (Ideal.span {(p : ℤ)}) := ((memL P).mp hP).2
    simpa using (Ideal.natAbs_pow_inertiaDeg (p:ℤ) P).symm
  have primeL (P : Ideal (𝓞 K)) (hP : P ∈ L) : Prime P := by
    have : P.IsPrime := ((memL P).mp hP).1
    apply Ideal.prime_of_isPrime _ this
    intro heq
    exact (pow_ne_zero _ hp.ne_zero) ((normL P hP).symm.trans (by simp [heq]))
  refine ⟨L, fun P => P.inertiaDeg ℤ, ?_, ?_, ?_⟩
  · intro P hP
    have : P.IsPrime := ((memL P).mp hP).1
    exact P.inertiaDeg_pos ℤ
  · change (∑ P ∈ Finset.univ.image _, _) ≤ _
    rw [Finset.sum_image (fun _ _ _ _ eq => Subtype.ext eq),
      ← NumberField.RingOfIntegers.rank K, ← Ideal.sum_ramification_inertia_eq_finrank pI (𝓞 K)]
    apply Finset.sum_le_sum
    intro Q _
    have : Q.val.IsPrime := Q.property.1
    exact Nat.le_mul_of_pos_left _ (Q.val.ramificationIdx_pos ℤ)
  · intro k
    have hn := pow_pos hp.pos k
    let S := smallPrimes K (p^k)
    have h1 : euler K (S ∪ L) (p^k) = euler K S (p^k) := by
      apply no_large_change K _ _ subset_union_left hn
      intro P hP
      obtain ⟨h, notS⟩ := mem_sdiff.mp hP
      have hL := (mem_union.mp h).resolve_left notS
      have hpr := primeL P hL
      exact ⟨hpr, fun hd => notS ((mem_small K).mpr ⟨Nat.le_of_dvd hn hd,hpr⟩)⟩
    have h2 : euler K (S ∪ L) (p^k) = euler K L (p^k) := by
      apply no_large_change K _ _ subset_union_right hn
      intro P hP
      obtain ⟨h, notL⟩ := mem_sdiff.mp hP
      have hpr := ((mem_small K).mp ((mem_union.mp h).resolve_right notL)).2
      refine ⟨hpr, ?_⟩
      intro hd
      have : P.IsPrime := Ideal.isPrime_of_prime hpr
      let : NeZero P := ⟨hpr.ne_zero⟩
      let q := (Ideal.under ℤ P).absNorm
      have hq : q.Prime := Nat.absNorm_under_prime P
      have nP : q^(P.inertiaDeg ℤ) = P.absNorm := by
        simpa [q] using Ideal.natAbs_pow_inertiaDeg (q:ℤ) P
      have qd : q ∣ p^k := dvd_trans (nP ▸ dvd_pow_self q (P.inertiaDeg_pos ℤ).ne') hd
      have qp : q = p := (hp.eq_one_or_self_of_dvd q (hq.dvd_of_dvd_pow qd)).resolve_left hq.ne_one
      apply notL ((memL P).mpr ⟨inferInstance, ?_⟩)
      change P.LiesOver (Ideal.span {(p:ℤ)})
      rw [←qp]
      exact Int.liesOver_span_absNorm P
    exact h1.symm.trans (h2.trans (factors_coeff K hp _ L normL k))

end OMA.IdealEuler975
end

section
/- Integral Bézout and Taylor estimates for counts of polynomial roots modulo prime powers. -/

open Polynomial Finset

namespace OMA.Local975

theorem resultant_nonzero (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0) :
    f.resultant f.derivative ≠ 0 := by
  let φ := Int.castRingHom ℚ
  have hφ : Function.Injective φ := Int.cast_injective
  have hirr : Irreducible (f.map φ) :=
    (Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast (hf.isPrimitive hd)).mp hf
  have hcop : IsCoprime (f.map φ) ((f.derivative).map φ) := by
    rw [← Polynomial.derivative_map]
    exact hirr.separable
  have hn := Polynomial.resultant_ne_zero _ _ hcop
  intro he
  apply hn
  rw [natDegree_map_eq_of_injective hφ, natDegree_map_eq_of_injective hφ,
    resultant_map_map, he, map_zero]

theorem derivative_not_dvd (f : ℤ[X]) (hd : f.natDegree ≠ 0) {p : ℕ} [Fact p.Prime]
    (hn : f.resultant f.derivative ≠ 0) {k : ℕ} {r : ℤ}
    (hk : padicValInt p (f.resultant f.derivative) < k) (hr : (p:ℤ)^k ∣ f.eval r) :
    ¬ (p:ℤ)^(padicValInt p (f.resultant f.derivative)+1) ∣ f.derivative.eval r := by
  let D := f.resultant f.derivative
  let w := padicValInt p D
  obtain ⟨a,b,_,_,hab⟩ := exists_mul_add_mul_eq_C_resultant f f.derivative le_rfl le_rfl (Or.inl hd)
  have hev : f.eval r * a.eval r + f.derivative.eval r * b.eval r = D := by
    simpa [D] using congrArg (fun P : ℤ[X] => P.eval r) hab
  intro hder
  have hroot : (p:ℤ)^(w+1) ∣ f.eval r := dvd_trans (pow_dvd_pow _ hk) hr
  have hD : (p:ℤ)^(w+1) ∣ D := hev ▸ dvd_add (dvd_mul_of_dvd_left hroot _) (dvd_mul_of_dvd_left hder _)
  have hbad := ((padicValInt_dvd_iff (p:=p) _ _).mp hD).resolve_left hn
  change w+1 ≤ w at hbad
  omega

/-- In a fixed residue class modulo p^(w+1), two roots agree modulo p^(k-w).
Only the bound on the valuation of the derivative at the first root is needed. -/
theorem root_separation (f : ℤ[X]) {p : ℕ} [Fact p.Prime] {k w : ℕ} {r s : ℤ}
    (hr : (p:ℤ)^k ∣ f.eval r) (hs : (p:ℤ)^k ∣ f.eval s)
    (hder : ¬ (p:ℤ)^(w+1) ∣ f.derivative.eval r)
    (hclose : (p:ℤ)^(w+1) ∣ s-r) : (p:ℤ)^(k-w) ∣ s-r := by
  by_cases heq : s-r=0
  · simp [heq]
  obtain ⟨c,hc⟩ := f.exists_mul_sq_add_linear_part_eq_eval_add r (s-r)
  rw [add_sub_cancel] at hc
  let b := f.derivative.eval r + c*(s-r)
  have hprod : (p:ℤ)^k ∣ (s-r)*b := by
    rw [show (s-r)*b = f.eval s-f.eval r by dsimp [b]; linarith only [hc]]
    exact dvd_sub hs hr
  have hnd : ¬ (p:ℤ)^(w+1) ∣ b := by
    intro hb
    apply hder
    have h := dvd_sub hb (dvd_mul_of_dvd_right hclose c)
    simpa [b] using h
  have hb : b≠0 := fun e => hnd (by rw [e]; exact dvd_zero _)
  have hval : padicValInt p b ≤ w := by
    by_contra! h
    exact hnd ((padicValInt_dvd_iff _ _).mpr (Or.inr h))
  have hle := ((padicValInt_dvd_iff _ _).mp hprod).resolve_left (mul_ne_zero heq hb)
  rw [padicValInt.mul heq hb] at hle
  exact (padicValInt_dvd_iff _ _).mpr (Or.inr (by omega))

theorem count (f : ℤ[X]) (hd : f.natDegree ≠ 0) (hD : f.resultant f.derivative ≠ 0)
    (p : ℕ) (hp : p.Prime) (k : ℕ) :
    Nat.count (fun r : ℕ => ((p^k:ℕ):ℤ) ∣ f.eval (r:ℤ)) (p^k) ≤
      p^(2*padicValInt p (f.resultant f.derivative)+1) := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  let w := padicValInt p (f.resultant f.derivative)
  change _ ≤ p^(2*w+1)
  by_cases hk : k≤2*w+1
  · exact (Nat.count_le _).trans (Nat.pow_le_pow_right hp.pos hk)
  let a := p^(w+1)
  let b := p^(k-w)
  let S := (range (p^k)).filter (fun r : ℕ => ((p^k:ℕ):ℤ) ∣ f.eval (r:ℤ))
  let key (r : ℕ) := (r%a, r/b)
  have hpa : 0<a := pow_pos hp.pos _
  have hpb : 0<b := pow_pos hp.pos _
  have hb : p^k = p^w*b := by dsimp [b]; rw [← pow_add]; congr 1; omega
  rw [Nat.count_eq_card_filter_range]
  change S.card ≤ _
  suffices S.card ≤ ((range a) ×ˢ (range (p^w))).card by
    simpa [a,Finset.card_product,← pow_add,show w+1+w=2*w+1 by omega] using this
  apply Finset.card_le_card_of_injOn key
  · intro r hr
    apply Finset.mem_product.mpr
    refine ⟨Finset.mem_range.mpr (Nat.mod_lt r hpa), Finset.mem_range.mpr ?_⟩
    apply (Nat.div_lt_iff_lt_mul hpb).mpr
    rw [← hb]
    exact Finset.mem_range.mp (Finset.mem_filter.mp hr).1
  · intro r hr s hs he
    have hr' : (p:ℤ)^k ∣ f.eval (r:ℤ) := by simpa using (Finset.mem_filter.mp hr).2
    have hs' : (p:ℤ)^k ∣ f.eval (s:ℤ) := by simpa using (Finset.mem_filter.mp hs).2
    have hrem : r ≡ s [MOD a] := congrArg Prod.fst he
    have hquot : r/b = s/b := congrArg Prod.snd he
    have hcl : (p:ℤ)^(w+1) ∣ (s:ℤ)-r := by
      simpa [a] using (Int.natCast_modEq_iff.mpr hrem).dvd
    have hsep := root_separation f hr' hs'
      (derivative_not_dvd f hd hD (show w<k by omega) hr') hcl
    change (p:ℤ)^(k-w) ∣ (s:ℤ)-r at hsep
    have hfin : r ≡ s [MOD b] := by
      apply Int.natCast_modEq_iff.mp
      exact Int.modEq_of_dvd (by simpa only [b,Nat.cast_pow] using hsep)
    have e : r%b=s%b := hfin
    calc r = r%b+b*(r/b) := (Nat.mod_add_div _ _).symm
         _ = s := by rw [e,hquot,Nat.mod_add_div]

theorem bounded (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0) (p : ℕ) (hp : p.Prime) :
    ∃ B : ℕ, ∀ k : ℕ,
      Nat.count (fun r : ℕ => ((p^k:ℕ):ℤ) ∣ f.eval (r:ℤ)) (p^k) ≤ B :=
  ⟨_, count f hd (resultant_nonzero f hf hd) p hp⟩

/-- A simple root modulo p^k, k positive, lifts to the next power. The new
base-p digit is solved in the field Z/pZ. -/
theorem lift (f : ℤ[X]) {p k r : ℕ} [hp : Fact p.Prime] (hk : 0<k)
    (hrange : r < p^k) (hr : (p:ℤ)^k ∣ f.eval (r:ℤ))
    (hsimple : ¬ (p:ℤ) ∣ f.derivative.eval (r:ℤ)) :
    ∃ s : ℕ, s < p^(k+1) ∧ (p:ℤ)^(k+1) ∣ f.eval (s:ℤ) ∧ s % (p^k) = r := by
  obtain ⟨u,hu⟩ := hr
  let d := f.derivative.eval (r:ℤ)
  have hd : (d : ZMod p) ≠ 0 := fun e => hsimple ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp e)
  let t : ZMod p := -(u:ZMod p)/(d:ZMod p)
  have h0 : (u:ZMod p) + (d:ZMod p)*t = 0 := by
    dsimp [t]; field_simp; ring
  have hdiv : (p:ℤ) ∣ u+d*(t.val:ℤ) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val] using h0
  let s := r+p^k*t.val
  have hpk : 0<p^k := pow_pos hp.out.pos k
  refine ⟨s, ?_, ?_, ?_⟩
  · have ht := t.val_lt
    have h : p^k*(t.val+1) ≤ p^k*p := Nat.mul_le_mul_left _ ht
    dsimp [s]; rw [pow_succ]; nlinarith
  · obtain ⟨c,hc⟩ := f.exists_mul_sq_add_linear_part_eq_eval_add (r:ℤ) ((p:ℤ)^k*t.val)
    have hs : (s:ℤ) = (r:ℤ)+(p:ℤ)^k*t.val := by simp [s]
    rw [hs, ← hc, hu]
    change (p:ℤ)^(k+1) ∣ c*((p:ℤ)^k*t.val)^2+d*((p:ℤ)^k*t.val)+(p:ℤ)^k*u
    have hv : (p:ℤ) ∣ (p:ℤ)^k := dvd_pow_self _ hk.ne'
    obtain ⟨v,hv'⟩ := hdiv
    obtain ⟨w,hw⟩ := hv
    refine ⟨v + c*w*(t.val:ℤ)^2, ?_⟩
    calc c*((p:ℤ)^k*t.val)^2 + d*((p:ℤ)^k*t.val) + (p:ℤ)^k*u =
            (p:ℤ)^k * ((u+d*t.val) + c*(p:ℤ)^k*(t.val:ℤ)^2) := by ring
         _ = _ := by simp only [hv',pow_succ (p:ℤ) k,hw]; ring
  · simp [s,Nat.add_mod, Nat.mod_eq_of_lt hrange, Nat.mul_mod_right]

private noncomputable def residues (f : ℤ[X]) (q : ℕ) : Finset ℕ :=
  (range q).filter fun r : ℕ => (q:ℤ) ∣ f.eval (r:ℤ)

theorem hensel (f : ℤ[X]) (hd : f.natDegree ≠ 0) (p : ℕ) (hp : p.Prime)
    (hgood : ¬ (p:ℤ) ∣ f.resultant f.derivative) (k : ℕ) (hk : 0 < k) :
    Nat.count (fun r : ℕ => ((p^k:ℕ):ℤ) ∣ f.eval (r:ℤ)) (p^k) =
      Nat.count (fun r : ℕ => (p:ℤ) ∣ f.eval (r:ℤ)) p := by
  classical
  let : Fact p.Prime := ⟨hp⟩
  have hD : f.resultant f.derivative ≠ 0 := fun e => hgood (e ▸ dvd_zero _)
  have hw : padicValInt p (f.resultant f.derivative) = 0 := by
    by_contra! e
    apply hgood
    have h := (padicValInt_dvd_iff (p:=p) 1 (f.resultant f.derivative)).mpr (Or.inr (by omega))
    simpa using h
  have simple {m r : ℕ} (hm : 0 < m) (hr : (p:ℤ)^m ∣ f.eval (r:ℤ)) :
      ¬ (p:ℤ) ∣ f.derivative.eval (r:ℤ) := by
    simpa only [hw, zero_add, pow_one] using derivative_not_dvd f hd hD (hw ▸ hm) hr
  have step (m : ℕ) (hm : 0 < m) : (residues f (p^(m+1))).card = (residues f (p^m)).card := by
    let big := residues f (p^(m+1))
    let small := residues f (p^m)
    let red (r : ℕ) := r % p^m
    have red_mem (r : ℕ) (hr : r∈big) : red r∈small := by
      have hmpos : 0<p^m := pow_pos hp.pos _
      refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.mod_lt _ hmpos), ?_⟩
      have hr' : (p:ℤ)^(m+1) ∣ f.eval (r:ℤ) := by simpa using (Finset.mem_filter.mp hr).2
      have hroot : (p:ℤ)^m ∣ f.eval (r:ℤ) := (pow_dvd_pow _ (Nat.le_succ m)).trans hr'
      have hmod : red r ≡ r [MOD p^m] := Nat.mod_modEq _ _
      have hh := (Int.natCast_modEq_iff.mpr hmod.symm).dvd.trans
        (Polynomial.sub_dvd_eval_sub (red r:ℤ) (r:ℤ) f)
      have hroot' : ((p^m:ℕ):ℤ) ∣ f.eval (r:ℤ) := by simpa only [Nat.cast_pow] using hroot
      simpa using dvd_add hh hroot'
    have eq : big.image red = small := by
      apply Finset.Subset.antisymm
      · exact Finset.image_subset_iff.mpr red_mem
      · intro r hr
        have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
        have hr' : (p:ℤ)^m ∣ f.eval (r:ℤ) := by simpa using (Finset.mem_filter.mp hr).2
        obtain ⟨s,hs,hs',hsr⟩ := lift f hm hrange hr' (simple hm hr')
        exact Finset.mem_image.mpr ⟨s,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hs,
          by simpa only [Nat.cast_pow] using hs'⟩,hsr⟩
    have inj : Set.InjOn red big := by
      intro r hr s hs he
      have hrange := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
      have hsrange := Finset.mem_range.mp (Finset.mem_filter.mp hs).1
      have hr' : (p:ℤ)^(m+1) ∣ f.eval (r:ℤ) := by simpa using (Finset.mem_filter.mp hr).2
      have hs' : (p:ℤ)^(m+1) ∣ f.eval (s:ℤ) := by simpa using (Finset.mem_filter.mp hs).2
      have hmod : r ≡ s [MOD p^m] := he
      have hpmod : r ≡ s [MOD p] := hmod.of_dvd (dvd_pow_self p hm.ne')
      have hcl := (Int.natCast_modEq_iff.mpr hpmod).dvd
      have hsep := root_separation (w:=0) f hr' hs'
        (by simpa using simple (Nat.succ_pos m) hr') (by simpa using hcl)
      have hstrong : r ≡ s [MOD p^(m+1)] :=
        Int.natCast_modEq_iff.mp (Int.modEq_of_dvd (by simpa only [Nat.cast_pow,Nat.sub_zero] using hsep))
      exact hstrong.eq_of_lt_of_lt hrange hsrange
    calc big.card = (big.image red).card := (Finset.card_image_of_injOn inj).symm
         _ = small.card := congrArg Finset.card eq
  rw [Nat.count_eq_card_filter_range,Nat.count_eq_card_filter_range]
  change (residues f (p^k)).card = (residues f p).card
  induction k, hk using Nat.le_induction with
  | base => simp
  | succ m hm ih => exact (step m hm).trans ih

end OMA.Local975
end

section
/- Uniform bounds for the prime-power coefficients of the root-counting function
and its correction by the inverse ideal-counting function. -/
namespace OMA.CoeffBound975
open Polynomial Finset ArithmeticFunction
open RootsEuler975

theorem roots_uniform (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℕ, p.Prime → ∀ j : ℕ, |rho f (p^j)| ≤ B := by
  classical
  let D := (f.resultant f.derivative).natAbs * f.leadingCoeff.natAbs
  have Dpos : 0 < D := Nat.mul_pos (Int.natAbs_pos.mpr (Local975.resultant_nonzero f hf hd))
    (Int.natAbs_pos.mpr (leadingCoeff_ne_zero.mpr hf.ne_zero))
  let b (p : ℕ) := if h : p.Prime then (Local975.bounded f hf hd p h).choose else 0
  have hb (p : ℕ) (hp : p.Prime) (j : ℕ) : rho f (p^j) ≤ b p := by
    dsimp only [b]
    rw [dif_pos hp,rho_apply]
    exact_mod_cast (Local975.bounded f hf hd p hp).choose_spec j
  let C := f.natDegree + 1 + ∑ p ∈ D.primeFactors, b p
  refine ⟨C, by positivity, fun p hp j => ?_⟩
  have pos : 0 ≤ rho f (p^j) := Nat.cast_nonneg _
  rw [abs_of_nonneg pos]
  by_cases bad : p ∣ D
  · have sub := single_le_sum (fun q (_ : q ∈ D.primeFactors) => Nat.zero_le (b q))
      (Nat.mem_primeFactors.mpr ⟨hp,bad,Dpos.ne'⟩)
    exact (hb p hp j).trans (by exact_mod_cast (show b p ≤ C by dsimp [C]; omega))
  · have hR : ¬(p:ℤ) ∣ f.resultant f.derivative :=
      fun h => bad (dvd_mul_of_dvd_left (Int.natAbs_dvd_natAbs.mpr h) _)
    have hL : ¬(p:ℤ) ∣ f.leadingCoeff :=
      fun h => bad (dvd_mul_of_dvd_right (Int.natAbs_dvd_natAbs.mpr h) _)
    cases j with
    | zero =>
      rw [pow_zero,rho_one]
      exact_mod_cast (show 1 ≤ C by dsimp [C]; omega)
    | succ j =>
      have eq : rho f (p^(j+1)) = rho f p := by
        simp only [rho_apply]
        rw [Local975.hensel f hd p hp hR _ (by omega)]
      rw [eq]
      exact (prime_le_degree_of_not_dvd f p hp hL).trans
        (by exact_mod_cast (show f.natDegree ≤ C by dsimp [C]; omega))

/-- Coefficients of a product of `s.card` local inverse factors are bounded by
`2^s.card`, since multiplying by `1-X^e` subtracts two earlier coefficients. -/
theorem poly_coeff {ι : Type*} (s : Finset ι) (e : ι → ℕ) (j : ℕ) :
    |(∏ i ∈ s, (1-X^(e i) : ℝ[X])).coeff j| ≤ (2:ℝ)^s.card := by
  classical
  induction s using Finset.induction_on generalizing j with
  | empty => by_cases h : j = 0 <;> simp [coeff_one,h]
  | @insert i s hi ih =>
    rw [prod_insert hi,mul_comm, mul_sub, mul_one,coeff_sub,coeff_mul_X_pow',
      card_insert_of_notMem hi,pow_succ]
    apply (abs_sub _ _).trans
    split_ifs
    · linarith only [ih j,ih (j-e i)]
    · simp only [abs_zero,add_zero]
      linarith only [ih j, pow_nonneg (by norm_num : (0:ℝ) ≤ 2) s.card]

theorem poly_support {ι : Type*} (s : Finset ι) (e : ι → ℕ) {j : ℕ}
    (b : (∑ i ∈ s, e i) < j) : (∏ i ∈ s, (1-X^(e i) : ℝ[X])).coeff j = 0 := by
  apply coeff_eq_zero_of_natDegree_lt
  apply (natDegree_prod_le ..).trans_lt
  refine (sum_le_sum fun i _ => (natDegree_sub_le ..).trans ?_).trans_lt b
  simp

theorem conv_power (g v : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (g*v) (p^k) = ∑ j ∈ range (k+1), g (p^(k-j))*v (p^j) := by
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal' (fun a b => g a*v b),
    Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro j hj
  have hjk : j ≤ k := by simpa using mem_range.mp hj
  have eq : p^k / p^j = p^(k-j) := by
    conv_lhs => rw [← Nat.sub_add_cancel hjk, pow_add]
    exact Nat.mul_div_cancel _ (pow_pos hp.pos _)
  rw [eq]

theorem conv_prime (g v : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) :
    (g*v) p = g p * v 1 + g 1*v p := by
  simpa [sum_range_succ] using conv_power g v hp 1

theorem conv_bound (g v : ArithmeticFunction ℝ) {B U : ℝ} {d : ℕ}
    (bn : 0 ≤ B) (un : 0 ≤ U)
    (gB : ∀ p : ℕ, p.Prime → ∀ j : ℕ, |g (p^j)| ≤ B)
    (vB : ∀ p : ℕ, p.Prime → ∀ j : ℕ, |v (p^j)| ≤ U)
    (off : ∀ p : ℕ, p.Prime → ∀ j : ℕ, d < j → v (p^j) = 0)
    {p : ℕ} (hp : p.Prime) (k : ℕ) : |(g*v) (p^k)| ≤ (d+1:ℕ)*B*U := by
  classical
  rw [conv_power g v hp k]
  apply (abs_sum_le_sum_abs ..).trans
  calc
    _ ≤ ∑ j ∈ range (k+1), if j < d+1 then B*U else 0 := by
      apply sum_le_sum
      intro j _
      split_ifs with h
      · rw [abs_mul]
        exact mul_le_mul (gB _ hp _) (vB _ hp _) (abs_nonneg _) bn
      · rw [off _ hp _ (by omega),mul_zero,abs_zero]
    _ = ∑ j ∈ (range (k+1)).filter (· < d+1), B*U := by rw [sum_filter]
    _ ≤ ∑ _j ∈ range (d+1), B*U := by
      exact sum_le_sum_of_subset_of_nonneg (fun j hj => mem_range.mpr (mem_filter.mp hj).2)
        (fun _ _ _ => mul_nonneg bn un)
    _ = _ := by simp [mul_assoc]

/-- Positivity of the residue degrees bounds the number of Euler factors by the field degree. -/
theorem local_bounds {ι : Type*} {v : ArithmeticFunction ℝ} {p d : ℕ}
    (h : ∃ L : Finset ι, ∃ e : ι → ℕ, (∀ i ∈ L, 0 < e i) ∧ (∑ i ∈ L, e i) ≤ d ∧
      ∀ j : ℕ, v (p^j) = (∏ i ∈ L, (1-X^(e i) : ℝ[X])).coeff j) :
    (∀ j : ℕ, |v (p^j)| ≤ (2:ℝ)^d) ∧ ∀ j : ℕ, d < j → v (p^j) = 0 := by
  obtain ⟨L,e,pos,deg,eq⟩ := h
  have size : L.card ≤ ∑ i ∈ L, e i := calc
    _ = ∑ _i ∈ L, 1 := by simp
    _ ≤ _ := sum_le_sum fun i hi => pos i hi
  constructor
  · intro j
    rw [eq j]
    exact (poly_coeff L e j).trans (pow_le_pow_right₀ (by norm_num) (size.trans deg))
  · intro j hj
    exact (eq j).trans (poly_support L e (deg.trans_lt hj))

theorem uniform_of_local {ι : Type*} (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0)
    (v : ArithmeticFunction ℝ) (d : ℕ)
    (loc : ∀ p : ℕ, p.Prime → ∃ L : Finset ι, ∃ e : ι → ℕ,
      (∀ i ∈ L, 0 < e i) ∧ (∑ i ∈ L, e i) ≤ d ∧
      ∀ j : ℕ, v (p^j) = (∏ i ∈ L, (1-X^(e i) : ℝ[X])).coeff j) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℕ, p.Prime → ∀ j : ℕ, |(rho f*v) (p^j)| ≤ B := by
  obtain ⟨B,bn,root⟩ := roots_uniform f hf hd
  refine ⟨((d+1 : ℕ) : ℝ)*B*(2:ℝ)^d, by positivity, fun p hp j => ?_⟩
  exact conv_bound _ _ bn (by positivity) root (fun q hq => (local_bounds (loc q hq)).1)
    (fun q hq => (local_bounds (loc q hq)).2) hp j

open scoped NumberField

theorem uniform (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0)
    (K : Type*) [Field K] [NumberField K] :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℕ, p.Prime → ∀ j : ℕ,
      |(rho f * IdealEuler975.mu K) (p^j)| ≤ B :=
  uniform_of_local f hf hd _ _ (IdealEuler975.local K)

/-- The linear Euler coefficients cancel at primes where the two counting functions agree. -/
theorem vanish (f : ℤ[X]) (K : Type*) [Field K] [NumberField K] (M : ℕ)
    (link : ∀ p : ℕ, p.Prime → ¬p ∣ M →
      Nat.count (fun r : ℕ => (p : ℤ) ∣ f.eval (r:ℤ)) p =
        Nat.card {I : Ideal (𝓞 K) // I.absNorm = p})
    {p : ℕ} (hp : p.Prime) (good : ¬p ∣ M) : (rho f * IdealEuler975.mu K) p = 0 := by
  let a := IdealEuler975.a K
  let v := IdealEuler975.mu K
  have inv : a*v = 1 := IdealEuler975.inverse K
  have a1 : a 1 = 1 := by
    rw [show a 1 = _ from IdealEuler975.a_apply K one_ne_zero]
    suffices h : Nat.card {I : Ideal (𝓞 K) // I.absNorm = 1} = 1 by exact_mod_cast h
    exact Nat.card_eq_one_iff_exists.mpr
      ⟨⟨⊤,Ideal.absNorm_eq_one_iff.mpr rfl⟩,fun I => Subtype.ext (Ideal.absNorm_eq_one_iff.mp I.2)⟩
  have eq : rho f p = a p := by
    rw [rho_apply,show a p = _ from IdealEuler975.a_apply K hp.ne_zero]
    exact_mod_cast link p hp good
  change (rho f*v) p = 0
  rw [conv_prime _ _ hp, eq, rho_one, ← a1, ← conv_prime _ _ hp, inv,
    ArithmeticFunction.one_apply_ne hp.ne_one]

end OMA.CoeffBound975
end

section
/- A local inverse Euler polynomial evaluates positively at the reciprocal of
its prime. Multiplying by the bounded nonnegative root-counting series preserves
strict positivity, including at the ramified and leading-coefficient primes. -/
namespace OMA.LocalPos975

open Polynomial Finset

private theorem geometric_majorant (a : ℕ → ℝ) (ha : ∀ k, 0 ≤ a k)
    (hbound : ∃ B : ℝ, ∀ k, a k ≤ B) {t : ℝ} (ht : 0 ≤ t) (ht' : t < 1) :
    Summable (fun k => ‖a k * t^k‖) := by
  obtain ⟨B,hB⟩ := hbound
  apply ((summable_geometric_of_lt_one ht ht').mul_left B).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (ha k) (pow_nonneg ht k))]
  exact mul_le_mul_of_nonneg_right (hB k) (pow_nonneg ht k)

/-- Evaluation of the local Dirichlet convolution, where the second sequence
of prime-power values is supplied as a polynomial. -/
theorem factor (rho mu : ArithmeticFunction ℝ) (p : ℕ) (hp : p.Prime)
    (h0 : ∀ k : ℕ, 0 ≤ rho (p^k)) (hbound : ∃ B : ℝ, ∀ k : ℕ, rho (p^k) ≤ B)
    (P : ℝ[X]) (hpoly : ∀ k : ℕ, mu (p^k) = P.coeff k) :
    (∑' k : ℕ, (rho*mu) (p^k) / (p:ℝ)^k) =
      P.eval (p:ℝ)⁻¹ * ∑' k : ℕ, rho (p^k) / (p:ℝ)^k := by
  let t := (p:ℝ)⁻¹
  have ht : 0 ≤ t := inv_nonneg.mpr (Nat.cast_nonneg _)
  have ht' : t < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  let F (k : ℕ) := P.coeff k * t^k
  let G (k : ℕ) := rho (p^k) * t^k
  have outside (k : ℕ) (hk : k ∉ range (P.natDegree + 1)) : F k = 0 := by
    simp only [mem_range,not_lt] at hk
    simp [F, coeff_eq_zero_of_natDegree_lt (by omega : P.natDegree < k)]
  have polySum : Summable (fun k => ‖F k‖) :=
    summable_of_ne_finset_zero (s := range (P.natDegree+1))
      (fun k hk => by rw [outside k hk,norm_zero])
  have polyValue : (∑' k, F k) = P.eval t := by
    rw [tsum_eq_sum outside,Polynomial.eval_eq_sum_range]
  have rootsSum : Summable (fun k => ‖G k‖) :=
    geometric_majorant (fun k => rho (p^k)) h0 hbound ht ht'
  have coeff (k : ℕ) : (rho*mu) (p^k) * t^k =
      ∑ j ∈ range (k+1), F j * G (k-j) := by
    rw [CoeffBound975.conv_power rho mu hp k, Finset.sum_mul]
    apply sum_congr rfl
    intro j hj
    have hjk : j ≤ k := by simpa using mem_range.mp hj
    have powSplit : t^k = t^(k-j)*t^j := by
      rw [← pow_add,Nat.sub_add_cancel hjk]
    rw [hpoly j,powSplit]
    dsimp [F,G]
    ring
  calc
    (∑' k : ℕ, (rho*mu) (p^k) / (p:ℝ)^k) = ∑' k, ∑ j ∈ range (k+1), F j * G (k-j) := by
      apply tsum_congr
      intro k
      simpa only [t,div_eq_mul_inv,inv_pow] using coeff k
    _ = (∑' k, F k) * ∑' k, G k :=
      (tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm polySum rootsSum).symm
    _ = _ := by simp only [polyValue,G,t,div_eq_mul_inv,inv_pow]

/-- Each factor at a prime is positive, without a good-prime hypothesis. -/
theorem positive {ι : Type*} (rho mu : ArithmeticFunction ℝ) (p : ℕ) (hp : p.Prime)
    (h1 : rho 1 = 1) (h0 : ∀ k : ℕ, 0 ≤ rho (p^k))
    (hbound : ∃ B : ℝ, ∀ k : ℕ, rho (p^k) ≤ B) (L : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ L, 0 < e i)
    (hpoly : ∀ k : ℕ, mu (p^k) = (∏ i ∈ L, (1-X^(e i) : ℝ[X])).coeff k) :
    0 < ∑' k : ℕ, (rho*mu) (p^k) / (p:ℝ)^k := by
  rw [factor rho mu p hp h0 hbound _ hpoly,Polynomial.eval_prod]
  have ht : 0 ≤ (p:ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have ht' : (p:ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  apply mul_pos
  · apply Finset.prod_pos
    intro i hi
    simpa only [eval_sub,eval_one,eval_pow,eval_X] using
      sub_pos.mpr (pow_lt_one₀ ht ht' (he i hi).ne')
  · have hs : Summable (fun k : ℕ => rho (p^k) / (p:ℝ)^k) := by
      simpa only [div_eq_mul_inv, inv_pow] using
        (geometric_majorant (fun k => rho (p^k)) h0 hbound ht ht').of_norm
    have h := hs.le_tsum 0 (fun k _ => div_nonneg (h0 k) (by positivity))
    simpa only [pow_zero, h1, div_one] using (lt_of_lt_of_le (by simp [h1]) h)

/-- The root-counting correction for any irreducible polynomial of positive degree. -/
theorem roots_positive {ι : Type*} (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0)
    (mu : ArithmeticFunction ℝ) (p : ℕ) (hp : p.Prime) (L : Finset ι) (e : ι → ℕ)
    (he : ∀ i ∈ L, 0 < e i)
    (hpoly : ∀ k : ℕ, mu (p^k) = (∏ i ∈ L, (1-X^(e i) : ℝ[X])).coeff k) :
    0 < ∑' k : ℕ, (RootsEuler975.rho f * mu) (p^k) / (p:ℝ)^k := by
  obtain ⟨B,hB⟩ := Local975.bounded f hf hd p hp
  apply positive (RootsEuler975.rho f) mu p hp (RootsEuler975.rho_one f)
    (fun _ => Nat.cast_nonneg _) _ L e he hpoly
  exact ⟨B, fun k => by rw [RootsEuler975.rho_apply]; exact_mod_cast hB k⟩

end OMA.LocalPos975
end

section
/- Summatory means and logarithmic means under Dirichlet convolution. -/

open Finset Filter
open scoped Topology BigOperators Asymptotics

namespace OMA.Convolve975

theorem hyperbola (h a : ℕ → ℝ) (N : ℕ) :
    (∑ n ∈ Icc 1 N, ∑ v ∈ n.divisorsAntidiagonal, h v.1*a v.2) =
      ∑ d ∈ Icc 1 N, h d * ∑ k ∈ Icc 1 (N/d), a k := by
  simp_rw [Finset.mul_sum]
  rw [sum_sigma',sum_sigma']
  refine sum_bij (fun x _ => ⟨x.2.1,x.2.2⟩) ?_ ?_ ?_ (by simp)
  · rintro ⟨n,d,k⟩ hx
    obtain ⟨hn,hdk⟩ := Finset.mem_sigma.mp hx
    obtain ⟨hdk,hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hdk
    change d*k=n at hdk
    obtain rfl := hdk
    obtain ⟨h1,hN⟩ := Finset.mem_Icc.mp hn
    have hd : 0<d := by by_contra! hz; simp_all
    have hk : 0<k := by by_contra! hz; simp_all
    refine Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd,? _⟩,Finset.mem_Icc.mpr ⟨hk,?_⟩⟩
    · exact (Nat.le_mul_of_pos_right d hk).trans hN
    · exact (Nat.le_div_iff_mul_le hd).mpr (by simpa [mul_comm] using hN)
  · rintro ⟨n,d,k⟩ hx ⟨m,e,l⟩ hy he
    have h1 := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hx).2).1
    have h2 := (Nat.mem_divisorsAntidiagonal.mp (Finset.mem_sigma.mp hy).2).1
    change d*k=n at h1
    change e*l=m at h2
    have hd : d=e := congrArg Sigma.fst he
    have hk : k=l := congrArg (fun x : (_ : ℕ) × ℕ => x.2) he
    subst e; subst l; subst n; subst m; rfl
  · rintro ⟨d,k⟩ hy
    obtain ⟨hd,hk⟩ := Finset.mem_sigma.mp hy
    obtain ⟨hd,_⟩ := Finset.mem_Icc.mp hd
    obtain ⟨hk,hle⟩ := Finset.mem_Icc.mp hk
    have hN := (Nat.le_div_iff_mul_le hd).mp hle
    refine ⟨⟨d*k,(d,k)⟩,Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hd hk,
      by simpa [mul_comm] using hN⟩,Nat.mem_divisorsAntidiagonal.mpr ⟨rfl,(Nat.mul_pos hd hk).ne'⟩⟩,rfl⟩

/-- Convolution by an absolutely summable sequence for the measure 1/d
multiplies the ordinary summatory mean by its Dirichlet series at one. -/
theorem mean (a h : ℕ → ℝ) (R : ℝ)
    (ha : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, a n)/(N:ℝ)) atTop (𝓝 R))
    (hh : Summable (fun d : ℕ => |h d|/(d:ℝ))) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, ∑ v ∈ n.divisorsAntidiagonal,
      h v.1*a v.2)/(N:ℝ)) atTop (𝓝 (R*∑' d : ℕ, h d/(d:ℝ))) := by
  let A (N : ℕ) := ∑ n ∈ Icc 1 N, a n
  have hA : Tendsto (fun N : ℕ => A N/(N:ℝ)) atTop (𝓝 R) := ha
  have hzero : A 0=0 := by simp [A]
  obtain ⟨C,hC⟩ := hA.norm.bddAbove_range
  have hbound (m : ℕ) : |A m| ≤ C*m := by
    obtain rfl | hm := Nat.eq_zero_or_pos m
    · simp [hzero]
    have H := hC (Set.mem_range_self m)
    have hm' : (0:ℝ) < m := by exact_mod_cast hm
    simpa only [Real.norm_eq_abs,abs_div,abs_of_nonneg hm'.le,div_le_iff₀ hm'] using H
  have hC0 : 0≤C := (norm_nonneg _).trans (hC (Set.mem_range_self 0))
  let F (N d : ℕ) := h d * A (N/d)/(N:ℝ)
  have point (d : ℕ) : Tendsto (fun N => F N d) atTop (𝓝 (R*(h d/d))) := by
    obtain rfl | hd := Nat.eq_zero_or_pos d
    · simp [F,hzero]
    have hd' : (0:ℝ)<d := by exact_mod_cast hd
    have hf : Tendsto (fun N:ℕ => ((N/d:ℕ):ℝ)/(N:ℝ)) atTop (𝓝 ((d:ℝ)⁻¹)) := by
      have H := (tendsto_nat_floor_mul_div_atTop (inv_nonneg.mpr hd'.le)).comp
        (tendsto_natCast_atTop_atTop (R:=ℝ))
      simpa only [Function.comp_def,inv_mul_eq_div,Nat.floor_div_eq_div] using H
    have HH := ((hA.comp (Nat.tendsto_div_const_atTop hd.ne')).mul hf).const_mul (h d)
    rw [show R*(h d/d) = h d * (R*(d:ℝ)⁻¹) by ring]
    apply HH.congr'
    filter_upwards [eventually_ge_atTop d] with N hN
    have hm : (0:ℝ)<(N/d:ℕ) := by exact_mod_cast Nat.div_pos hN hd
    dsimp [F]
    field_simp
  have dom (N d : ℕ) : ‖F N d‖ ≤ C*(|h d|/d) := by
    obtain rfl | hN := Nat.eq_zero_or_pos N
    · simp [F]; positivity
    obtain rfl | hd := Nat.eq_zero_or_pos d
    · simp [F,hzero]
    have hN' : (0:ℝ)<N := by exact_mod_cast hN
    have hd' : (0:ℝ)<d := by exact_mod_cast hd
    have hfloor : ((N/d:ℕ):ℝ)*(d:ℝ) ≤ N := by exact_mod_cast Nat.div_mul_le_self N d
    dsimp [F]
    rw [abs_div,abs_mul,abs_of_nonneg hN'.le]
    calc |h d| * |A (N/d)| / (N:ℝ) ≤ |h d| * (C*((N/d:ℕ):ℝ))/(N:ℝ) := by gcongr; exact hbound _
         _ ≤ C*(|h d|/d) := by
            rw [div_le_iff₀ hN', mul_div_assoc',div_mul_eq_mul_div,le_div_iff₀ hd']
            nlinarith only [mul_le_mul_of_nonneg_left hfloor (mul_nonneg hC0 (abs_nonneg (h d)))]
  have H := tendsto_tsum_of_dominated_convergence (hh.mul_left C) point
    (Eventually.of_forall dom)
  rw [tsum_mul_left] at H
  refine H.congr (fun N => ?_)
  rw [hyperbola,Finset.sum_div]
  apply tsum_eq_sum
  intro d hd
  by_cases h : d=0
  · simp [F,h,hzero]
  · have hlt : N<d := by simpa [Finset.mem_Icc, Nat.one_le_iff_ne_zero,h] using hd
    simp [F,Nat.div_eq_of_lt hlt,hzero]

end OMA.Convolve975
end

section
/- Absolute convergence and positivity of a multiplicative correction
whose local Euler factors differ summably from one. -/

namespace OMA.EulerMass975
open Finset Real

set_option maxHeartbeats 800000 in
theorem product_mass (g : ℕ → ℝ) (g0 : g 0 = 0) (g1 : g 1 = 1)
    (gm : ∀ {m n}, Nat.Coprime m n → g (m*n) = g m*g n)
    (localSum : ∀ p : ℕ, p.Prime → Summable (fun k : ℕ => |g (p^k)|))
    (w : ℕ → ℝ) (wn : ∀ n, 0 ≤ w n) (ws : Summable w)
    (tail : ∀ p : ℕ, p.Prime → (∑' k : ℕ, |g (p^(k+1))|) ≤ w p)
    (positive : ∀ p : ℕ, p.Prime → 0 < ∑' k : ℕ, g (p^k)) :
    Summable (fun n => |g n|) ∧ 0 < ∑' n, g n := by
  classical
  let G (n : ℕ) := |g n|
  have G1 : G 1 = 1 := by simp [G,g1]
  have Gm : ∀ {m n}, Nat.Coprime m n → G (m*n) = G m*G n := by
    intro m n h; simp [G,gm h,abs_mul]
  have loc {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => ‖G (p^k)‖) := by
    simpa [G,Real.norm_eq_abs] using localSum p hp
  have locBd {p : ℕ} (hp : p.Prime) : (∑' k : ℕ, G (p^k)) ≤ Real.exp (w p) := by
    have h := localSum p hp
    change (∑' k : ℕ, |g (p^k)|) ≤ _
    rw [h.tsum_eq_zero_add]
    simp only [pow_zero,g1,abs_one]
    linarith [tail p hp,Real.add_one_le_exp (w p)]
  have absSum : Summable G := by
    apply summable_of_sum_range_le (c:=Real.exp (∑' j, w j)) (fun i => abs_nonneg (g i))
    intro N
    have hs := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum (f:=G)
      G1 Gm (fun h => loc h) N
    have hi := (hasSum_subtype_iff_indicator (s:=N.smoothNumbers) (f:=G)).mp hs.2
    have hsrange : (∑ n ∈ range N, G n) ≤ ∏ p ∈ N.primesBelow, ∑' k : ℕ, G (p^k) := by
      have he : (∑ n ∈ range N, G n) = ∑ n ∈ range N, N.smoothNumbers.indicator G n := by
        apply sum_congr rfl
        intro n hn
        by_cases hz : n = 0
        · simp [hz,G,g0,Set.indicator]
        · rw [Set.indicator_of_mem (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hz) (mem_range.mp hn))]
      rw [he,← hi.tsum_eq]
      apply hi.summable.sum_le_tsum
      intro i _
      exact Set.indicator_nonneg (fun i _ => abs_nonneg (g i)) _
    apply hsrange.trans
    calc (∏ p ∈ N.primesBelow, ∑' k : ℕ, G (p^k)) ≤ ∏ p ∈ N.primesBelow, Real.exp (w p) := by
           apply prod_le_prod
           · exact fun _ _ => tsum_nonneg (fun k => abs_nonneg _)
           · exact fun p hp => locBd (Nat.prime_of_mem_primesBelow hp)
         _ = Real.exp (∑ p ∈ N.primesBelow, w p) := (Real.exp_sum ..).symm
         _ ≤ _ := Real.exp_le_exp.mpr (ws.sum_le_tsum _ (fun i _ => wn i))
  let a (p : Nat.Primes) := ∑' k : ℕ, g (p.val^k)
  have equal : ∏' p, a p = ∑' n, g n := by
    exact EulerProduct.eulerProduct_tprod g1 gm (by simpa [Real.norm_eq_abs] using absSum) g0
  have hsdev : Summable (fun p : Nat.Primes => a p-1) := by
    apply (ws.comp_injective (i:=fun p : Nat.Primes => p.val) Subtype.val_injective).of_norm_bounded
    intro p
    have h := localSum p p.property
    have h' : Summable (fun k : ℕ => g (p.val^k)) := Summable.of_norm (by simpa [Real.norm_eq_abs] using h)
    dsimp [a]
    rw [h'.tsum_eq_zero_add,pow_zero,g1,add_sub_cancel_left]
    apply le_trans _ (tail p p.property)
    simpa [Real.norm_eq_abs] using norm_tsum_le_tsum_norm (f:=fun k : ℕ => g (p.val^(k+1)))
      (by simpa [Real.norm_eq_abs, Function.comp_def] using h.comp_injective (i:=fun n : ℕ => n+1) Nat.succ_injective)
  have hlog : Summable (fun p => log (a p)) := by
    simpa using Real.summable_log_one_add_of_summable hsdev
  refine ⟨absSum,?_⟩
  rw [← equal,← Real.rexp_tsum_eq_tprod (f:=a) (fun p => positive p p.property) hlog]
  exact Real.exp_pos _

/-- Bounded coefficients at prime powers and cancellation at the first power
outside a finite set give summable local tails of order 1/p². -/
theorem weighted_mass (h : ArithmeticFunction ℝ) (hm : h.IsMultiplicative)
    (B : ℝ) (hB : 0 ≤ B) (bd : ∀ p : ℕ, p.Prime → ∀ k : ℕ, |h (p^k)| ≤ B)
    (E : Finset ℕ) (good : ∀ p : ℕ, p.Prime → p ∉ E → h p = 0)
    (pos : ∀ p : ℕ, p.Prime → 0 < ∑' k : ℕ, h (p^k)/(p:ℝ)^k) :
    Summable (fun n : ℕ => |h n|/(n:ℝ)) ∧ 0 < ∑' n : ℕ, h n/(n:ℝ) := by
  let g (n : ℕ) := h n/(n:ℝ)
  let err (n : ℕ) := if n ∈ E then B else 0
  let w (n : ℕ) := err n + (2*B)*((n:ℝ)^2)⁻¹
  have ws : Summable w := by
    apply Summable.add (f:=err)
    · exact summable_of_ne_finset_zero (s:=E) (fun i hi => by simp [err,hi])
    · exact (Real.summable_nat_pow_inv.mpr (by omega : 1 < 2)).mul_left (2*B)
  have wn (n : ℕ) : 0 ≤ w n := by dsimp [w,err]; split <;> positivity
  have primeTerm (p k : ℕ) : |g (p^k)| = |h (p^k)| * ((p:ℝ)⁻¹)^k := by
    simp [g,div_eq_mul_inv, inv_pow]
  have invLt {p : ℕ} (hp : p.Prime) : (p:ℝ)⁻¹ < 1 :=
    inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  have ls (p : ℕ) (hp : p.Prime) : Summable (fun k : ℕ => |g (p^k)|) := by
    apply Summable.of_nonneg_of_le (fun _ => abs_nonneg _)
      (f:=fun k : ℕ => B*((p:ℝ)⁻¹)^k)
    · intro k; rw [primeTerm]; gcongr; exact bd p hp k
    · exact (summable_geometric_of_lt_one (by positivity) (invLt hp)).mul_left B
  have tail (p : ℕ) (hp : p.Prime) : (∑' k : ℕ, |g (p^(k+1))|) ≤ w p := by
    let v : ℝ := (p:ℝ)⁻¹
    have hv : 0 ≤ v := by dsimp [v]; positivity
    have hv1 : v < 1 := invLt hp
    have hv2 : v ≤ 1/2 := by
      dsimp [v]; rw [inv_eq_one_div]
      exact one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hp.two_le)
    have geom := summable_geometric_of_lt_one hv hv1
    have hsum := (ls p hp).comp_injective (i:=fun k : ℕ => k+1) Nat.succ_injective
    have hsum' : Summable (fun k : ℕ => |g (p^(k+1))|) := hsum
    have hsum2 : Summable (fun k : ℕ => |g (p^(k+1+1))|) :=
      hsum'.comp_injective (i:=fun k : ℕ => k+1) Nat.succ_injective
    have bound2 : (∑' k : ℕ, |g (p^(k+1+1))|) ≤ (2*B)*((p:ℝ)^2)⁻¹ := by
      calc
        _ ≤ ∑' k : ℕ, (B*v^2)*v^k := by
          apply hsum2.tsum_le_tsum _ (geom.mul_left _)
          intro k
          rw [primeTerm]
          calc _ ≤ B*(v^(k+1+1)) := mul_le_mul_of_nonneg_right (bd p hp _) (by positivity)
               _ = _ := by ring
        _ = (B*v^2)*(1-v)⁻¹ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hv hv1]
        _ ≤ (B*v^2)*2 := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [inv_le_iff_one_le_mul₀ (by linarith)]
          linarith
        _ = _ := by simp [v,inv_pow]; ring
    have first : |g p| ≤ err p := by
      by_cases he : p ∈ E
      · rw [show err p = B by simp [err,he]]
        calc |g p| = |h p| * v := by simp [g,v,div_eq_mul_inv]
             _ ≤ B*v := mul_le_mul_of_nonneg_right (by simpa using bd p hp 1) hv
             _ ≤ B := mul_le_of_le_one_right hB hv1.le
      · simp [err,g,he,good p hp he]
    rw [hsum'.tsum_eq_zero_add]
    simp only [zero_add,pow_one]
    exact add_le_add first bound2
  have mass := product_mass g (by simp [g]) (by simp [g,hm.1])
    (fun hcop => by simp [g, hm.2 hcop,div_mul_div_comm]) ls w wn ws tail
    (fun p hp => by simpa [g] using pos p hp)
  simpa [g,abs_div] using mass

end OMA.EulerMass975
end




namespace OMA.Band976
open Finset Filter Polynomial RootsEuler975
open scoped Topology NumberField

/-- The root density is positive for all nonconstant irreducible polynomials, without an
assumption on the sign of their integer values. -/
theorem positive_mean (f : ℤ[X]) (hirr : Irreducible f) (hd : f.natDegree ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ Tendsto (fun n : ℕ => (∑ d ∈ Icc 1 n, rho f d)/(n:ℝ)) atTop (𝓝 R) := by
  obtain ⟨K,fieldK,numK,M,hM,link⟩ := Field975.field_link f hirr (Nat.pos_of_ne_zero hd)
  let a := IdealEuler975.a K
  let μ := IdealEuler975.mu K
  let h := rho f * μ
  obtain ⟨B,hB,bound⟩ := CoeffBound975.uniform f hirr hd K
  have good (p : ℕ) (hp : p.Prime) (hne : p ∉ M.divisors) : h p = 0 :=
    CoeffBound975.vanish f K M link hp (by simpa [Nat.mem_divisors,hM.ne'] using hne)
  have pos (p : ℕ) (hp : p.Prime) : 0 < ∑' j : ℕ, h (p^j)/(p:ℝ)^j := by
    obtain ⟨S,e,he,_,hc⟩ := IdealEuler975.local K p hp
    exact LocalPos975.roots_positive f hirr hd μ p hp S e he hc
  obtain ⟨hs,hp⟩ := EulerMass975.weighted_mass h
    ((multiplicative f).mul (IdealEuler975.multiplicative K)) B hB bound M.divisors good pos
  let R := NumberField.dedekindZeta_residue K
  have avg : Tendsto (fun n : ℕ => (∑ d ∈ Icc 1 n, a d)/(n:ℝ)) atTop (𝓝 R) := by
    apply (Kummer975.coefficient_mean K).congr
    intro n
    congr 1
    exact sum_congr rfl fun d hd => (IdealEuler975.a_apply K (Nat.ne_of_gt (mem_Icc.mp hd).1)).symm
  have prod : a*h = rho f := by
    dsimp only [h,a,μ]
    rw [mul_left_comm,IdealEuler975.inverse,mul_one]
  refine ⟨_,mul_pos (NumberField.dedekindZeta_residue_pos K) hp,?_⟩
  rw [←prod, mul_comm a h]
  exact Convolve975.mean a h R avg hs

end OMA.Band976

section
/- The divisor window splits into its old layer and its logarithmic translate
when one new prime factor is adjoined, as in Tenenbaum's moment argument. -/

namespace TenenbaumLayers
open Finset Real
open scoped Classical

noncomputable def window (b : ℕ) (t : ℝ) : ℝ :=
  ∑ d ∈ b.divisors, (Set.Ico (log d - 1) (log d)).indicator (fun _ => (1:ℝ)) t

theorem sum_divisors_mul_prime {α : Type*} [AddCommMonoid α] {b p : ℕ}
    (hp : p.Prime) (fresh : ¬ p ∣ b) (f : ℕ → α) :
    ∑ d ∈ (b*p).divisors, f d =
      (∑ d ∈ b.divisors, f d) + ∑ d ∈ b.divisors, f (p*d) := by
  classical
  have bn : b ≠ 0 := by rintro rfl; exact fresh (dvd_zero _)
  have bpn : b*p ≠ 0 := Nat.mul_ne_zero bn hp.ne_zero
  have split : (b*p).divisors = b.divisors ∪ b.divisors.image (fun x => p*x) := by
    ext d
    simp only [mem_union, mem_image]
    constructor
    · intro hm
      have hd := Nat.dvd_of_mem_divisors hm
      by_cases pd : p ∣ d
      · right
        obtain ⟨x,rfl⟩ := pd
        have xb := (Nat.mul_dvd_mul_iff_left hp.pos).mp (by simpa only [Nat.mul_comm b p] using hd)
        exact ⟨x,Nat.mem_divisors.mpr ⟨xb,bn⟩,rfl⟩
      · left
        exact Nat.mem_divisors.mpr ⟨((hp.coprime_iff_not_dvd.mpr pd).symm.dvd_mul_right).mp hd, bn⟩
    · rintro (hd | ⟨x,hx,rfl⟩)
      · exact Nat.mem_divisors.mpr ⟨dvd_mul_of_dvd_left (Nat.dvd_of_mem_divisors hd) p, bpn⟩
      · apply Nat.mem_divisors.mpr
        exact ⟨by simpa only [Nat.mul_comm b p] using
          Nat.mul_dvd_mul_left p (Nat.dvd_of_mem_divisors hx), bpn⟩
  have separate : Disjoint b.divisors (b.divisors.image fun x => p*x) := by
    apply Finset.disjoint_left.mpr
    intro d hd hm
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hm
    exact fresh ((dvd_mul_right p x).trans (Nat.dvd_of_mem_divisors hd))
  rw [split, Finset.sum_union separate, Finset.sum_image]
  intro x _ y _ eq
  exact Nat.eq_of_mul_eq_mul_left hp.pos eq

theorem window_mul_prime {b p : ℕ} (hp : p.Prime) (fresh : ¬ p ∣ b) (t : ℝ) :
    window (b*p) t = window b t + window b (t-log p) := by
  unfold window
  rw [sum_divisors_mul_prime hp fresh]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have pd : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have pp : (p:ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Nat.cast_mul, Real.log_mul pp pd]
  have shift : t ∈ Set.Ico (log p + log d - 1) (log p + log d) ↔
      t-log p ∈ Set.Ico (log d-1) (log d) := by
    simp only [Set.mem_Ico]
    constructor <;> rintro ⟨lo,hi⟩ <;> constructor <;> linarith
  simp only [Set.indicator_apply, shift]

end TenenbaumLayers
end

section
/- Hooley's moment after adjoining one new prime. Analytic measurability
and domination use the finite-window argument of @romechenko, PR #16801. -/

namespace TenenbaumLayers
open Finset Filter MeasureTheory Real
open scoped BigOperators Classical

theorem window_bounds (b : ℕ) (t : ℝ) : 0 ≤ window b t ∧ window b t ≤ b.divisors.card := by
  classical
  have point (d : ℕ) : 0 ≤ (Set.Ico (log d - 1) (log d)).indicator (fun _ => (1:ℝ)) t ∧
      (Set.Ico (log d - 1) (log d)).indicator (fun _ => (1:ℝ)) t ≤ 1 := by
    by_cases ht : t ∈ Set.Ico (log (d:ℝ)-1) (log d) <;> simp [ht]
  constructor
  · exact sum_nonneg fun d _ => (point d).1
  · calc
      _ ≤ ∑ _ ∈ b.divisors, (1 : ℝ) := Finset.sum_le_sum fun d _ => (point d).2
      _ = _ := by simp

theorem window_measurable (b : ℕ) : Measurable (window b) :=
  Finset.measurable_sum _ fun _ _ => measurable_const.indicator measurableSet_Ico

theorem window_integrable (b : ℕ) : Integrable (window b) := by
  apply integrable_finsetSum b.divisors
  intro d _
  apply IntegrableOn.integrable_indicator _ measurableSet_Ico
  exact integrableOn_const (measure_Ico_lt_top.ne)

theorem window_power_integrable (b q : ℕ) : Integrable (fun t => window b t ^ (q+1)) := by
  refine ((window_integrable b).mul_const ((b.divisors.card : ℝ)^q)).mono'
    ((window_measurable b).pow_const _).aestronglyMeasurable ?_
  filter_upwards with t
  obtain ⟨lo,hi⟩ := window_bounds b t
  rw [Real.norm_of_nonneg (pow_nonneg lo _),pow_succ,mul_comm]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ lo hi q) lo

noncomputable def moment (b q : ℕ) : ℝ := ∫ t, window b t ^ q
noncomputable def mixed (b p q j : ℕ) (t : ℝ) : ℝ :=
  window b t ^ j * window b (t-log p)^(q-j) * (q.choose j : ℝ)

/-- The integral expansion is finite and exact for every positive order.
The intermediate terms are the correlations that the weighted estimate must bound. -/
theorem moment_mul_prime {b p : ℕ} (prime : p.Prime) (fresh : ¬p∣b) (q : ℕ) :
    moment (b*p) (q+1) =
      ∑ j ∈ range (q+2), ∫ t : ℝ, mixed b p (q+1) j t := by
  classical
  have point (t : ℝ) : (window (b*p) t)^(q+1) =
      ∑ j ∈ range (q+2), mixed b p (q+1) j t := by
    rw [window_mul_prime prime fresh]
    exact add_pow _ _ _
  have nonneg (j : ℕ) (t : ℝ) : 0 ≤ mixed b p (q+1) j t :=
    mul_nonneg (mul_nonneg (pow_nonneg (window_bounds b t).1 _)
      (pow_nonneg (window_bounds b (t-log p)).1 _)) (Nat.cast_nonneg _)
  have meas (j : ℕ) : Measurable (mixed b p (q+1) j) :=
    (((window_measurable b).pow_const _).mul
      (((window_measurable b).comp (measurable_id.sub measurable_const)).pow_const _)).mul_const _
  have integrable (j : ℕ) (hj : j ∈ range (q+2)) : Integrable (mixed b p (q+1) j) := by
    apply (window_power_integrable (b*p) q).mono' (meas j).aestronglyMeasurable
    filter_upwards with t
    rw [Real.norm_of_nonneg (nonneg j t),point]
    exact single_le_sum (fun i _ => nonneg i t) hj
  rw [moment]
  simp_rw [point]
  exact integral_finsetSum _ integrable

end TenenbaumLayers
end

section
/- Smoothing a divisor window over a logarithmic interval of length one. -/

namespace TenenbaumLayers
open Finset Real
open scoped Classical

theorem window_neighbor (b : ℕ) {u v a : ℝ} (h : a-1 ≤ v) (g : v ≤ a) :
    window b (u-a) ≤ window b (u-v) + window b (u-v-1) := by
  unfold window
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun d _ => ?_
  let I := Set.Ico (log (d : ℝ)-1) (log d)
  change I.indicator (fun _ => (1:ℝ)) (u-a) ≤
    I.indicator (fun _ => (1:ℝ)) (u-v) + I.indicator (fun _ => (1:ℝ)) (u-v-1)
  by_cases old : u-a ∈ I
  · have lo := old.1
    have hi := old.2
    by_cases right : u-v < log d
    · have hit : u-v ∈ I := ⟨by linarith, right⟩
      have nonneg : 0 ≤ I.indicator (fun _ => (1:ℝ)) (u-v-1) :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) _
      simpa only [Set.indicator_of_mem old, Set.indicator_of_mem hit] using
        (le_add_of_nonneg_right nonneg : (1:ℝ) ≤ _)
    · have hit : u-v-1 ∈ I := ⟨by linarith, by linarith⟩
      have nonneg : 0 ≤ I.indicator (fun _ => (1:ℝ)) (u-v) :=
        Set.indicator_nonneg (fun _ _ => zero_le_one) _
      simpa only [Set.indicator_of_mem old, Set.indicator_of_mem hit] using
        (le_add_of_nonneg_left nonneg : (1:ℝ) ≤ _)
  · rw [Set.indicator_of_notMem old]
    exact add_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) _)
      (Set.indicator_nonneg (fun _ _ => zero_le_one) _)

theorem window_power_neighbor (b : ℕ) {u v a : ℝ} (s : ℕ)
    (h : a-1 ≤ v) (g : v ≤ a) :
    window b (u-a)^s ≤ (2:ℝ)^(s-1)*(window b (u-v)^s + window b (u-v-1)^s) := by
  have nonneg (t : ℝ) : 0 ≤ window b t :=
    Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  exact (pow_le_pow_left₀ (nonneg _) (window_neighbor b h g) s).trans
    (add_pow_le (nonneg _) (nonneg _) s)

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Finset Real MeasureTheory
open scoped Classical

/-- Chebyshev's elementary bound supplies a uniform mass bound in a logarithmic
interval of length one. The prime set may be any finite subset of that interval. -/
theorem prime_packet (P : Finset ℕ) (a : ℝ) (primes : ∀ p ∈ P, p.Prime)
    (band : ∀ p ∈ P, a ≤ log p ∧ log p ≤ a+1) :
    ∑ p ∈ P, log p / (p:ℝ) ≤ log 4 * exp 1 := by
  have pe (p : ℕ) (hp : p ∈ P) : exp (log (p:ℝ)) = p :=
    exp_log (by exact_mod_cast (primes p hp).pos)
  have sub : P ⊆ Nat.primesLE ⌊exp (a+1)⌋₊ := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨Nat.le_floor ((pe p hp) ▸ exp_le_exp.mpr (band p hp).2),primes p hp⟩
  have bounded : (∑ p ∈ P, log (p:ℝ)) ≤ log 4 * exp (a+1) := by
    apply le_trans _ (Chebyshev.theta_le_log4_mul_x (exp_pos (a+1)).le)
    rw [Chebyshev.theta_eq_sum_primesLE]
    exact sum_le_sum_of_subset_of_nonneg sub fun p hp _ => log_nonneg
      (by exact_mod_cast (Nat.prime_of_mem_primesLE hp).one_le)
  calc
    _ ≤ ∑ p ∈ P, log (p:ℝ) / exp a := by
      apply sum_le_sum
      intro p hp
      apply div_le_div_of_nonneg_left (log_nonneg (by exact_mod_cast (primes p hp).one_le)) (exp_pos a)
      rw [← pe p hp]; exact exp_le_exp.mpr (band p hp).1
    _ = (∑ p ∈ P, log (p:ℝ)) / exp a := by rw [Finset.sum_div]
    _ ≤ log 4 * exp 1 := (div_le_iff₀ (exp_pos a)).mpr (by simpa [exp_add,mul_assoc,mul_left_comm,mul_comm] using bounded)

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Finset Real MeasureTheory
open scoped Classical

/-- Averaging over one logarithmic unit turns Chebyshev's prime-packet
bound into a bound for translates of an arbitrary integrable majorant. -/
theorem prime_average (P : Finset ℕ) (primes : ∀ p ∈ P, p.Prime) (t : ℝ)
    (spec : ℕ → ℝ) (f : ℝ → ℝ) (hf : Integrable f) (pos : ∀ v, 0 ≤ f v)
    (major : ∀ p ∈ P, ∀ v ∈ Set.Icc (t-log p) (t-log p+1), spec p ≤ f v) :
    ∑ p ∈ P, log p / (p:ℝ) * spec p ≤ (log 4 * exp 1) * ∫ v, f v := by
  classical
  let I (p : ℕ) := Set.Icc (t-log p) (t-log p+1)
  let w (p : ℕ) := log p / (p:ℝ)
  have wn (p : ℕ) (hp : p ∈ P) : 0 ≤ w p :=
    div_nonneg (log_nonneg (by exact_mod_cast (primes p hp).one_le)) (Nat.cast_nonneg _)
  have base (p : ℕ) (hp : p ∈ P) : spec p ≤ ∫ v in I p, f v := by
    calc
      _ = ∫ _v in I p, spec p := by simp [I,Real.volume_real_Icc]
      _ ≤ ∫ v in I p, f v := setIntegral_mono_on
        (integrableOn_const measure_Icc_lt_top.ne) hf.integrableOn measurableSet_Icc (major p hp)
  have wi (p : ℕ) : Integrable (fun v => w p * (I p).indicator f v) :=
    (hf.indicator measurableSet_Icc).const_mul _
  calc
    _ ≤ ∑ p ∈ P, w p * ∫ v in I p, f v := sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (base p hp) (wn p hp)
    _ = ∫ v, ∑ p ∈ P, w p * (I p).indicator f v := by
      rw [integral_finsetSum P fun p _ => wi p]; apply sum_congr rfl; intro p _
      rw [integral_const_mul, integral_indicator measurableSet_Icc]
    _ ≤ ∫ v, (log 4 * exp 1) * f v := by
      apply integral_mono (integrable_finsetSum P fun p _ => wi p) (hf.const_mul _)
      intro v
      have localMass : ∑ p ∈ P.filter (fun p => v ∈ I p), w p ≤ log 4 * exp 1 := by
        apply prime_packet _ (t-v) (fun p hp => primes p (mem_filter.mp hp).1)
        intro p hp
        obtain ⟨lo,hi⟩ := (mem_filter.mp hp).2
        change t-log p ≤ v at lo
        change v ≤ t-log p+1 at hi
        constructor <;> linarith
      convert mul_le_mul_of_nonneg_right localMass (pos v) using 1
      rw [sum_mul, sum_filter]; apply sum_congr rfl; intro p _
      by_cases hp : v ∈ I p <;> simp [hp]
    _ = _ := integral_const_mul _ _

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Finset Real MeasureTheory
open scoped Classical

theorem translated_window_power (P : Finset ℕ) (primes : ∀ p ∈ P, p.Prime)
    (b s : ℕ) (t : ℝ) :
    ∑ p ∈ P, log p / (p:ℝ) * window b (t-log p)^(s+1) ≤
      (log 4 * exp 1) * (2:ℝ)^(s+1) * moment b (s+1) := by
  let f (v : ℝ) := window b v ^ (s+1)
  have hf : Integrable f := window_power_integrable b s
  have hs : Integrable (fun v : ℝ => f (v-1)) := hf.comp_sub_right 1
  have h := prime_average P primes t (fun p => f (t-log p))
    (fun v => (2:ℝ)^s * (f v + f (v-1))) ((hf.add hs).const_mul _)
    (fun v => mul_nonneg (by positivity) (add_nonneg (pow_nonneg (window_bounds _ _).1 _) (pow_nonneg (window_bounds _ _).1 _))) (by
      intro p _ v hv
      obtain ⟨lo,hi⟩ := hv
      have neigh := window_power_neighbor b (u:=t) (v:=t-v) (a:=log p) (s+1) (by linarith) (by linarith)
      simpa only [f,sub_sub_cancel,Nat.add_sub_cancel] using neigh)
  rw [integral_const_mul,integral_add hf hs,integral_sub_right_eq_self] at h
  change _ ≤ log 4 * exp 1 * ((2:ℝ)^s * (moment b (s+1) + moment b (s+1))) at h
  convert h using 1; ring

/-- A finite prime average of one of the genuinely mixed binomial correlations
is bounded by the product of the two separate moments. The constant is absolute. -/
theorem prime_mixed (P : Finset ℕ) (primes : ∀ p ∈ P, p.Prime) (b r s : ℕ) :
    ∑ p ∈ P, (log p / (p:ℝ)) * ∫ t, window b t^(r+1) * window b (t-log p)^(s+1) ≤
      (log 4 * exp 1) * (2:ℝ)^(s+1) * moment b (r+1) * moment b (s+1) := by
  let F (p : ℕ) (t : ℝ) := window b t^(r+1) * window b (t-log p)^(s+1)
  have Fi (p : ℕ) : Integrable (F p) := by
    apply ((window_power_integrable b r).mul_const ((b.divisors.card:ℝ)^(s+1))).mono'
    · exact (((window_measurable b).pow_const _).mul (((window_measurable b).comp (measurable_id.sub measurable_const)).pow_const _)).aestronglyMeasurable
    · filter_upwards with t
      change ‖window b t^(r+1) * window b (t-log p)^(s+1)‖ ≤ _
      rw [Real.norm_of_nonneg (mul_nonneg (pow_nonneg (window_bounds _ _).1 _) (pow_nonneg (window_bounds _ _).1 _))]
      apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (window_bounds _ _).1 (window_bounds _ _).2 _) (pow_nonneg (window_bounds _ _).1 _)
  let C := (log 4 * exp 1) * (2:ℝ)^(s+1) * moment b (s+1)
  calc
    _ = ∫ t, ∑ p ∈ P, (log p/(p:ℝ)) * F p t := by
      rw [integral_finsetSum P fun p _ => (Fi p).const_mul _]
      simp only [integral_const_mul,F]
    _ ≤ ∫ t, window b t^(r+1) * C := by
      apply integral_mono (integrable_finsetSum P fun p _ => (Fi p).const_mul _) ((window_power_integrable b r).mul_const _)
      intro t
      convert mul_le_mul_of_nonneg_left (translated_window_power P primes b s t) (pow_nonneg (window_bounds b t).1 (r+1)) using 1
      rw [mul_sum]; apply sum_congr rfl; intro p _; dsimp [F]; ring
    _ = _ := by rw [integral_mul_const]; change moment b (r+1) * C = _; dsimp [C]; ring

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Finset Real MeasureTheory
open scoped Classical

/-- The total of all genuinely mixed terms has geometric constant 3^q:
expand (1+2)^q after applying the prime-kernel bound to each summand. -/
theorem prime_error (P : Finset ℕ) (primes : ∀ p ∈ P, p.Prime) (b q : ℕ)
    {B : ℝ} (hB : 0 ≤ B) (products : ∀ j ∈ Finset.Ioo 0 q, moment b j * moment b (q-j) ≤ B) :
    ∑ p ∈ P, (log p / (p:ℝ)) * ∑ j ∈ Finset.Ioo 0 q, ∫ t, mixed b p q j t ≤
      (log 4 * exp 1) * 3^q * B := by
  have err (j : ℕ) (hj : j ∈ Finset.Ioo 0 q) :
      ∑ p ∈ P, log p / (p:ℝ) * ∫ t, mixed b p q j t ≤
        (2:ℝ)^(q-j) * (q.choose j:ℝ) * ((log 4 * exp 1) * B) := by
    have jp := (Finset.mem_Ioo.mp hj).1
    have lt := (Finset.mem_Ioo.mp hj).2
    obtain ⟨r,hr⟩ : ∃ r, j = r+1 := ⟨j-1,by omega⟩
    obtain ⟨s,hs⟩ : ∃ s, q-j = s+1 := ⟨q-j-1,by omega⟩
    have bound := prime_mixed P primes b r s
    rw [← hr,← hs] at bound
    have res := mul_le_mul_of_nonneg_right bound (Nat.cast_nonneg (q.choose j) (α:=ℝ))
    have logPos : 0 ≤ log 4 := log_nonneg (by norm_num)
    calc
      _ = (∑ p ∈ P, log p / (p:ℝ) * ∫ t, window b t^j * window b (t-log p)^(q-j)) * (q.choose j:ℝ) := by
        rw [sum_mul]; apply sum_congr rfl; intro p _
        unfold mixed
        rw [integral_mul_const,mul_assoc]
      _ ≤ _ := res
      _ = (2:ℝ)^(q-j) * (q.choose j:ℝ) * (log 4 * exp 1) * (moment b j * moment b (q-j)) := by ring
      _ ≤ (2:ℝ)^(q-j) * (q.choose j:ℝ) * (log 4 * exp 1) * B := mul_le_mul_of_nonneg_left (products j hj) (by positivity)
      _ = _ := by ring
  have total : ∑ j ∈ Finset.Ioo 0 q, (2:ℝ)^(q-j) * (q.choose j:ℝ) ≤ 3^q := by
    calc
      _ ≤ ∑ j ∈ range (q+1), (2:ℝ)^(q-j) * (q.choose j:ℝ) := by
        apply sum_le_sum_of_subset_of_nonneg (fun j hj => mem_range.mpr (by have := (mem_Ioo.mp hj).2; omega))
        intro j _ _; positivity
      _ = (1+2:ℝ)^q := by simpa only [one_pow,one_mul] using (add_pow (1:ℝ) 2 q).symm
      _ = _ := by norm_num
  calc
    _ = ∑ j ∈ Finset.Ioo 0 q, ∑ p ∈ P, log p / (p:ℝ) * ∫ t, mixed b p q j t := by
      simp only [mul_sum]; rw [sum_comm]
    _ ≤ _ := sum_le_sum err
    _ = (∑ j ∈ Finset.Ioo 0 q,(2:ℝ)^(q-j) * (q.choose j:ℝ)) * ((log 4 * exp 1) * B) := (sum_mul ..).symm
    _ ≤ (3:ℝ)^q * ((log 4 * exp 1) * B) := mul_le_mul_of_nonneg_right total (by apply mul_nonneg _ hB; apply mul_nonneg (log_nonneg (by norm_num)) (exp_pos _).le)
    _ = _ := by ring

end TenenbaumLayers
end

section
/- The second Hooley moment counts ordered pairs of close divisors, weighted
by the overlap length of their two logarithmic windows. -/

namespace TenenbaumLayers
open Set Finset MeasureTheory Real

private noncomputable def strip (a t : ℝ) : ℝ :=
  (Set.Ico (a-1) a).indicator (fun _ => (1:ℝ)) t

theorem moment_one (b : ℕ) : moment b 1 = b.divisors.card := by
  simp only [moment, pow_one, window]
  rw [integral_finsetSum]
  · simp only [integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico,
      smul_eq_mul, mul_one, sub_sub_cancel, max_eq_left zero_le_one,
      sum_const, nsmul_eq_mul, mul_one]
  · intro d _
    exact (integrableOn_const (measure_Ico_lt_top.ne)).integrable_indicator measurableSet_Ico

private theorem product_is_inter (a b : ℝ) : (fun t => strip a t*strip b t) =
    (Set.Ico (max (a-1) (b-1)) (min a b)).indicator (fun _ => (1:ℝ)) := by
  ext t
  rw [← Set.Ico_inter_Ico]
  by_cases ha : t ∈ Set.Ico (a-1) a <;> by_cases hb : t ∈ Set.Ico (b-1) b <;> simp [strip,ha,hb]

theorem window_overlap (a b : ℝ) : (∫ t : ℝ, strip a t*strip b t) = max (1-|a-b|) 0 := by
  rw [product_is_inter, integral_indicator_const _ measurableSet_Ico, Real.volume_real_Ico,
    smul_eq_mul, mul_one]
  congr 1
  by_cases h : a ≤ b
  · rw [min_eq_left h, max_eq_right (sub_le_sub_right h _), abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · have h' := le_of_not_ge h
    rw [min_eq_right h', max_eq_left (sub_le_sub_right h' _), abs_of_nonneg (sub_nonneg.mpr h')]
    ring

theorem moment_two (b : ℕ) : moment b 2 =
    ∑ d ∈ b.divisors, ∑ e ∈ b.divisors, max (1-|log d-log e|) 0 := by
  have calcPoint (t : ℝ) : (window b t)^2 =
      ∑ d ∈ b.divisors, ∑ e ∈ b.divisors, strip (log d) t * strip (log e) t := by
    simp only [window, strip, sq, sum_mul, mul_sum]
    exact sum_congr rfl fun d _ => sum_congr rfl fun e _ => mul_comm _ _
  have pair (a c : ℝ) : Integrable (fun t => strip a t * strip c t) := by
    rw [product_is_inter]
    exact (integrableOn_const (measure_Ico_lt_top.ne)).integrable_indicator measurableSet_Ico
  rw [moment]
  simp_rw [calcPoint]
  rw [integral_finsetSum]
  · refine sum_congr rfl fun d _ => ?_
    rw [integral_finsetSum]
    · exact sum_congr rfl fun e _ => window_overlap _ _
    · exact fun e _ => pair _ _
  · intro d _
    exact integrable_finsetSum _ fun e _ => pair _ _

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open MeasureTheory Real

private theorem interpolation_nonneg (b n : ℕ) : 0 ≤ moment b n :=
  integral_nonneg (fun t => pow_nonneg (window_bounds b t).1 n)

private theorem interpolation_lintegral (b n : ℕ) (hn : 1 ≤ n) :
    ENNReal.ofReal (moment b n) = ∫⁻ t : ℝ, ENNReal.ofReal (window b t ^ n) := by
  apply ofReal_integral_eq_lintegral_ofReal
  · obtain ⟨k,rfl⟩ : ∃ k,n=k+1 := ⟨n-1,by omega⟩
    exact window_power_integrable b k
  · exact Filter.Eventually.of_forall (fun t => pow_nonneg (window_bounds b t).1 n)

/-- Hölder interpolation of the window moments between orders one and q. -/
theorem moment_interpolate (b j q : ℕ) (hq : 2≤ q) (hj : 1≤ j) (hjq : j≤ q) :
    moment b j ≤ moment b 1 ^ (((q:ℝ)-j)/(q-1)) * moment b q ^ (((j:ℝ)-1)/(q-1)) := by
  let a : ℝ := ((q:ℝ)-j)/(q-1)
  let c : ℝ := ((j:ℝ)-1)/(q-1)
  have q2 : (2:ℝ)≤ q := by exact_mod_cast hq
  have j1 : (1:ℝ)≤ j := by exact_mod_cast hj
  have jq : (j:ℝ)≤ q := by exact_mod_cast hjq
  have d : 0 < (q:ℝ)-1 := by linarith
  have ha : 0≤ a := div_nonneg (sub_nonneg.mpr jq) d.le
  have hc : 0≤ c := div_nonneg (sub_nonneg.mpr j1) d.le
  have one : a+c=1 := by dsimp [a,c]; rw [←add_div]; field_simp; ring
  have order : a+(q:ℝ)*c=j := by dsimp [a,c]; field_simp; ring
  let W (n : ℕ) (t : ℝ) := ENNReal.ofReal (window b t ^ n)
  have wm (n) : Measurable (W n) := (ENNReal.measurable_ofReal.comp ((window_measurable b).pow_const n))
  have holder := ENNReal.lintegral_mul_norm_pow_le (μ:=volume) (wm 1).aemeasurable
    (wm q).aemeasurable ha hc one
  have point (t : ℝ) : W j t = W 1 t ^ a * W q t ^ c := by
    have h := (window_bounds b t).1
    dsimp only [W]
    rw [pow_one, ENNReal.ofReal_rpow_of_nonneg h ha,
      ENNReal.ofReal_rpow_of_nonneg (pow_nonneg h q) hc,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg h a)]
    rw [←Real.rpow_natCast (window b t) j, ←Real.rpow_natCast (window b t) q,
      ←Real.rpow_mul h, ←Real.rpow_add_of_nonneg h ha (mul_nonneg (Nat.cast_nonneg q) hc),order]
  change moment b j ≤ moment b 1 ^ a * moment b q ^ c
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg
    (Real.rpow_nonneg (interpolation_nonneg b 1) _) (Real.rpow_nonneg (interpolation_nonneg b q) _))).mp
  rw [ENNReal.ofReal_mul (Real.rpow_nonneg (interpolation_nonneg b 1) a),
    ←ENNReal.ofReal_rpow_of_nonneg (interpolation_nonneg b 1) ha,
    ←ENNReal.ofReal_rpow_of_nonneg (interpolation_nonneg b q) hc,
    interpolation_lintegral b j hj, interpolation_lintegral b 1 (by decide),
    interpolation_lintegral b q (by omega)]
  change (∫⁻ t, W j t) ≤ (∫⁻ t, W 1 t)^a * (∫⁻ t, W q t)^c
  simpa only [←point] using holder

/-- The two interpolated exponents add independently of the split j+k=q. -/
theorem moment_mul_interpolate (b j k q : ℕ) (hj : 1≤ j) (hk : 1≤ k) (split : j+k=q) :
    moment b j * moment b k ≤
      moment b 1 ^ ((q:ℝ)/(q-1)) * moment b q ^ (((q:ℝ)-2)/(q-1)) := by
  have hq : 2≤ q := by omega
  let a (m : ℕ) : ℝ := ((q:ℝ)-m)/(q-1)
  let c (m : ℕ) : ℝ := ((m:ℝ)-1)/(q-1)
  have r (m) (lo : 1≤ m) (hi : m≤ q) : 0≤ a m ∧ 0≤ c m := by
    have l : (1:ℝ)≤ m := by exact_mod_cast lo
    have h : (m:ℝ)≤ q := by exact_mod_cast hi
    exact ⟨div_nonneg (sub_nonneg.mpr h) (sub_nonneg.mpr (l.trans h)),
      div_nonneg (sub_nonneg.mpr l) (sub_nonneg.mpr (l.trans h))⟩
  have rs : (j:ℝ)+k=q := by exact_mod_cast split
  have aj := r j hj (by omega)
  have ak := r k hk (by omega)
  have aa : a j+a k=(q:ℝ)/(q-1) := by
    dsimp [a]; rw [←add_div]; congr 1; linarith
  have cc : c j+c k=((q:ℝ)-2)/(q-1) := by
    dsimp [c]; rw [←add_div]; congr 1; linarith
  calc
    _ ≤ (moment b 1 ^ a j * moment b q ^ c j) * (moment b 1 ^ a k * moment b q ^ c k) :=
      mul_le_mul (moment_interpolate b j q hq hj (by omega)) (moment_interpolate b k q hq hk (by omega))
        (interpolation_nonneg b k) (mul_nonneg (Real.rpow_nonneg (interpolation_nonneg b 1) _)
          (Real.rpow_nonneg (interpolation_nonneg b q) _))
    _ = (moment b 1 ^ a j * moment b 1 ^ a k) * (moment b q ^ c j * moment b q ^ c k) := by ring
    _ = _ := by rw [←Real.rpow_add_of_nonneg (interpolation_nonneg b 1) aj.1 ak.1,
      ←Real.rpow_add_of_nonneg (interpolation_nonneg b q) aj.2 ak.2,aa,cc]
end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Finset MeasureTheory Real
open scoped Classical

/-- The finite, uniformly weighted Hall--Tenenbaum prime estimate preceding
(2.10) of *Sur une question d'Erdős et Schinzel, II*. The elementary
Chebyshev kernel gives the explicit bound (log 4)e·3^q before weighting. -/
theorem hall_error (P : Finset ℕ) (primes : ∀ p ∈ P, p.Prime) (b q : ℕ)
    (w : ℕ → ℝ) (D : ℝ) (hD : 0 ≤ D) (upper : ∀ p ∈ P,w p ≤ D * (log p / p)) :
    ∑ p ∈ P, w p * ∑ j ∈ Finset.Ioo 0 q, ∫ t, mixed b p q j t ≤
      D * (log 4 * exp 1) * 3^q * (b.divisors.card:ℝ)^((q:ℝ)/(q-1)) * moment b q^(((q:ℝ)-2)/(q-1)) := by
  let B := moment b 1 ^ ((q:ℝ)/(q-1)) * moment b q ^ (((q:ℝ)-2)/(q-1))
  have mn (i : ℕ) : 0 ≤ moment b i := integral_nonneg fun t => pow_nonneg (window_bounds b t).1 _
  have hb : 0 ≤ B := mul_nonneg (rpow_nonneg (mn _) _) (rpow_nonneg (mn _) _)
  have interp (j : ℕ) (hj : j ∈ Finset.Ioo 0 q) : moment b j * moment b (q-j) ≤ B := by
    obtain ⟨h1,h2⟩ := mem_Ioo.mp hj
    exact moment_mul_interpolate b j (q-j) q (by omega) (by omega) (by omega)
  have err (p : ℕ) : 0 ≤ ∑ j ∈ Finset.Ioo 0 q, ∫ t, mixed b p q j t := by
    refine sum_nonneg fun j _ => integral_nonneg fun t => ?_
    exact mul_nonneg (mul_nonneg (pow_nonneg (window_bounds _ _).1 _) (pow_nonneg (window_bounds _ _).1 _)) (Nat.cast_nonneg _)
  calc
    _ ≤ ∑ p ∈ P, D * ((log p / p) * ∑ j ∈ Finset.Ioo 0 q, ∫ t, mixed b p q j t) := by
      refine sum_le_sum fun p hp => ?_; rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (upper p hp) (err p)
    _ = _ := (mul_sum ..).symm
    _ ≤ D * ((log 4 * exp 1) * 3^q * B) := mul_le_mul_of_nonneg_left (prime_error P primes b q hb interp) hD
    _ = _ := by simp only [B,moment_one]; ring

end TenenbaumLayers
end

section
/- Separating the endpoint terms in the new-prime recurrence. -/

namespace TenenbaumLayers
open Finset MeasureTheory Real
open scoped Classical

theorem moment_mul_prime_interior {b p : ℕ} (prime : p.Prime) (fresh : ¬p∣b)
    (q : ℕ) (hq : 0 < q) : moment (b*p) q =
    2*moment b q + ∑ j ∈ Ioo 0 q, ∫ t : ℝ, mixed b p q j t := by
  classical
  let f := fun j : ℕ => ∫ t : ℝ, mixed b p q j t
  have first : f 0 = moment b q := by
    simpa [f,mixed,moment] using (integral_sub_right_eq_self
      (fun t : ℝ => window b t^q) (log p) (μ := volume))
  have last : f q = moment b q := by simp [f,mixed,moment]
  have interval : range q = insert 0 (Ioo 0 q) := by ext i; simp; omega
  have sum : moment (b*p) q = ∑ j ∈ range (q+1), f j := by
    cases q with
    | zero => omega
    | succ k => exact moment_mul_prime prime fresh k
  rw [sum, sum_range_succ,interval,sum_insert (by simp),first,last]
  dsimp only [f]
  ring

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Finset MeasureTheory Real
open scoped Classical

/-- The finite truncation of Tenenbaum (2.10), for all heights σ≥1 and
bounded local polynomial root-count weights ρ. -/
theorem logarithmic_step (P : Finset ℕ) (primes : ∀ p ∈ P, p.Prime) (b q : ℕ)
    (fresh : ∀ p ∈ P, ¬p ∣ b) (hq : 0 < q)
    (ρ : ℕ → ℝ) (D σ : ℝ) (hD : 0 ≤ D) (hσ : 1 ≤ σ) (upper : ∀ p ∈ P, ρ p ≤ D) :
    ∑ p ∈ P, (ρ p * log p / (p:ℝ)^σ) * moment (b*p) q ≤
      2*moment b q * (∑ p ∈ P, ρ p * log p / (p:ℝ)^σ) +
        D * (log 4 * exp 1) * 3^q * (b.divisors.card:ℝ)^((q:ℝ)/(q-1)) * moment b q^(((q:ℝ)-2)/(q-1)) := by
  let w (p : ℕ) := ρ p * log p / (p:ℝ)^σ
  have bound (p : ℕ) (hp : p ∈ P) : w p ≤ D * (log p / (p:ℝ)) := by
    have pone : (1:ℝ) ≤ p := by exact_mod_cast (primes p hp).one_le
    have pp : (0:ℝ) < p := zero_lt_one.trans_le pone
    refine (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (upper p hp) (log_nonneg pone)) (rpow_nonneg pp.le _)).trans ?_
    rw [←mul_div_assoc]
    exact div_le_div_of_nonneg_left (mul_nonneg hD (log_nonneg pone)) pp (self_le_rpow_of_one_le pone hσ)
  have expansion : ∑ p ∈ P, w p * moment (b*p) q =
      2*moment b q * (∑ p ∈ P, w p) + ∑ p ∈ P, w p * ∑ j ∈ Finset.Ioo 0 q, ∫ t, mixed b p q j t := by
    rw [mul_sum,←sum_add_distrib]; apply sum_congr rfl; intro p hp; rw [moment_mul_prime_interior (primes p hp) (fresh p hp) q hq]; ring
  exact expansion.trans_le (add_le_add_right (hall_error P primes b q w D hD bound) _)

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Finset MeasureTheory Real

/-- The homogeneous concave-power bound, including vanishing total mass. -/
theorem fractional_mass {ι : Type*} (P : Finset ι) (w x : ι → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (hx : ∀ p ∈ P, 0 ≤ x p) {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1) :
    ∑ p ∈ P, w p * x p^u ≤ (∑ p ∈ P, w p)^(1-u) * (∑ p ∈ P, w p*x p)^u := by
  let S := ∑ p ∈ P, w p
  have hs : 0 ≤ S := sum_nonneg hw
  by_cases zero : S = 0
  · have allzero := (sum_eq_zero_iff_of_nonneg hw).mp zero
    have z : ∑ p ∈ P,w p * x p ^ u = 0 := sum_eq_zero fun p hp => by rw [allzero p hp,zero_mul]
    rw [z]; exact mul_nonneg (rpow_nonneg hs _) (rpow_nonneg (sum_nonneg fun p hp => mul_nonneg (hw p hp) (hx p hp)) _)
  have sp := lt_of_le_of_ne hs (Ne.symm zero)
  have sumone : ∑ p ∈ P,w p/S = 1 := by rw [←sum_div,div_self zero]
  have jensen := (Real.concaveOn_rpow hu hu').le_map_sum
    (fun p hp => div_nonneg (hw p hp) hs) sumone (fun p hp => (hx p hp : x p ∈ Set.Ici (0:ℝ)))
  simp only [smul_eq_mul] at jensen
  have swap (t : ℝ) (v : ℝ) : t/S*v = t*v/S := by ring
  simp only [swap,←sum_div] at jensen
  rw [div_rpow (sum_nonneg fun p hp => mul_nonneg (hw p hp) (hx p hp)) hs] at jensen
  have j := (div_le_iff₀ sp).mp jensen
  have powS : S^(1-u) = S / S^u := by rw [rpow_sub sp,rpow_one]
  change _ ≤ S^(1-u) * _
  rw [powS]
  exact j.trans_eq (by ring)

/-- Passing a weighted first moment to the fractional moment. The coefficient
of the old moment is exactly 2^u, as required in the differential inequality. -/
theorem fractional_recurrence {ι : Type*} (P : Finset ι) (w x : ι → ℝ)
    (hw : ∀ p ∈ P, 0 ≤ w p) (hx : ∀ p ∈ P, 0 ≤ x p) {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1)
    {M E : ℝ} (hM : 0 ≤ M) (hE : 0 ≤ E)
    (estimate : ∑ p ∈ P,w p*x p ≤ 2*M*(∑ p ∈ P,w p) + E) :
    ∑ p ∈ P, w p * x p^u ≤ 2^u * (∑ p ∈ P,w p) * M^u + (∑ p ∈ P,w p)^(1-u) * E^u := by
  let S := ∑ p ∈ P, w p
  have hs : 0 ≤ S := sum_nonneg hw
  have hprod : 0 ≤ 2*M := by positivity
  have result := fractional_mass P w x hw hx hu hu'
  have cond : 0 ≤ ∑ p ∈ P, w p * x p := sum_nonneg fun p hp => mul_nonneg (hw p hp) (hx p hp)
  have join : S^(1-u) * S^u = S := by rw [←rpow_add_of_nonneg hs (sub_nonneg.mpr hu') hu,sub_add_cancel,rpow_one]
  calc
    _ ≤ S^(1-u) * (2*M*S + E)^u := result.trans (mul_le_mul_of_nonneg_left (rpow_le_rpow cond estimate hu) (rpow_nonneg hs _))
    _ ≤ S^(1-u) * ((2*M*S)^u + E^u) := mul_le_mul_of_nonneg_left (rpow_add_le_add_rpow (mul_nonneg hprod hs) hE hu hu') (rpow_nonneg hs _)
    _ = _ := by
      rw [mul_add,mul_rpow hprod hs,mul_rpow (by norm_num : (0:ℝ)≤2) hM]
      change _ = (2:ℝ)^u*S*M^u+S^(1-u)*E^u
      rw [show S^(1-u)*((2^u*M^u)*S^u) = 2^u*(S^(1-u)*S^u)*M^u by ring,join]

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Finset MeasureTheory Real

/-- The finite-prime fractional-moment estimate used between (2.10) and (2.13).
Setting u=t/q removes q from the factor (3^q)^u in the error. -/
theorem logarithmic_fractional_step (P : Finset ℕ) (primes : ∀ p ∈ P, p.Prime) (b q : ℕ)
    (fresh : ∀ p ∈ P, ¬p ∣ b) (hq : 0 < q) (ρ : ℕ → ℝ) (D σ : ℝ) (hD : 0 ≤ D)
    (hσ : 1 ≤ σ) (nonneg : ∀ p ∈ P, 0 ≤ ρ p) (upper : ∀ p ∈ P, ρ p ≤ D)
    (u : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) :
    let w (p : ℕ) := ρ p * log (p:ℝ) / (p:ℝ)^σ
    let S := ∑ p ∈ P, w p
    ∑ p ∈ P,w p * (moment (b*p) q)^u ≤
       2^u * S * (moment b q)^u + S^(1-u) * (D*(log 4*exp 1))^u *
         (3:ℝ)^((q:ℝ)*u) * (b.divisors.card:ℝ)^(((q:ℝ)/(q-1))*u) *
         (moment b q)^((((q:ℝ)-2)/(q-1))*u) := by
  let w (p : ℕ) := ρ p * log (p:ℝ) / (p:ℝ)^σ
  let S := ∑ p ∈ P, w p
  have wn (p : ℕ) (hp : p ∈ P) : 0 ≤ w p :=
    div_nonneg (mul_nonneg (nonneg p hp) (log_nonneg (by exact_mod_cast (primes p hp).one_le))) (rpow_nonneg (Nat.cast_nonneg _) _)
  have pos (k : ℕ) : 0 ≤ moment k q := integral_nonneg fun z => pow_nonneg (window_bounds k z).1 _
  have cpos : 0 ≤ D*(log 4 * exp 1) := mul_nonneg hD (mul_nonneg (log_nonneg (by norm_num)) (exp_pos _).le)
  have err := logarithmic_step P primes b q fresh hq ρ D σ hD hσ upper
  have h := fractional_recurrence P w (fun p => moment (b*p) q) wn (fun p _ => pos (b*p)) hu hu' (pos b)
    (mul_nonneg (mul_nonneg (mul_nonneg cpos (by positivity)) (rpow_nonneg (Nat.cast_nonneg _) _)) (rpow_nonneg (pos b) _)) err
  refine h.trans_eq ?_
  dsimp only
  congr 1
  rw [mul_rpow (mul_nonneg (mul_nonneg cpos (by positivity)) (rpow_nonneg (Nat.cast_nonneg _) _)) (rpow_nonneg (pos b) _),
    mul_rpow (mul_nonneg cpos (by positivity)) (rpow_nonneg (Nat.cast_nonneg _) _), mul_rpow cpos (by positivity),
    ←rpow_natCast (3:ℝ) q, ←rpow_mul (by norm_num : (0:ℝ)≤3), ←rpow_mul (Nat.cast_nonneg b.divisors.card), ←rpow_mul (pos b)]
  ring

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Finset Real

/-- Homogeneous Hölder, with the same counting density attached to two
nonnegative functions. -/
theorem weighted_holder {ι : Type*} (I : Finset ι) (w x y : ι → ℝ)
    (wn : ∀ i ∈ I, 0 ≤ w i) (xn : ∀ i ∈ I, 0 ≤ x i) (yn : ∀ i ∈ I, 0 ≤ y i)
    (a r : ℝ) (ha : 0< a) (hr : 0< r) (total : a+r=1) :
    ∑ i ∈ I, w i * (x i)^a * (y i)^r ≤ (∑ i ∈ I,w i*x i)^a * (∑ i ∈ I,w i*y i)^r := by
  have hc : a⁻¹.HolderConjugate r⁻¹ := by
    rw [show r=1-a by linarith]; exact Real.HolderConjugate.inv_one_sub_inv ha (by linarith)
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg I hc
    (f:=fun i => (w i*x i)^a) (g:=fun i => (w i*y i)^r)
    (fun i hi => rpow_nonneg (mul_nonneg (wn i hi) (xn i hi)) _)
    (fun i hi => rpow_nonneg (mul_nonneg (wn i hi) (yn i hi)) _)
  have cancel (f : ι → ℝ) (non : ∀ i ∈ I,0≤ f i) (e : ℝ) (he : 0< e) :
      ∑ i ∈ I,((w i*f i)^e)^e⁻¹ = ∑ i ∈ I,w i*f i := by
    refine sum_congr rfl fun i hi => ?_
    rw [←rpow_mul (mul_nonneg (wn _ hi) (non _ hi)),mul_inv_cancel₀ he.ne',rpow_one]
  rw [cancel x xn a ha,cancel y yn r hr,one_div,one_div,inv_inv,inv_inv] at h
  refine le_trans (le_of_eq ?_) h
  apply sum_congr rfl; intro i hi
  rw [mul_rpow (wn i hi) (xn i hi),mul_rpow (wn i hi) (yn i hi),
    show (w i^a*x i^a)*(w i^r*y i^r) = (w i^a*w i^r)*x i^a*y i^r by ring,
    ←rpow_add_of_nonneg (wn i hi) ha.le hr.le,total,rpow_one]

/-- Average a family of one-prime recurrences and retain the exact coefficient
of its homogeneous term. In the application I is a powerset of primes. -/
theorem sum_fractional_layers {ι : Type*} (I : Finset ι) (w x y h : ι → ℝ)
    (wn : ∀ i ∈ I, 0 ≤ w i) (xn : ∀ i ∈ I, 0 ≤ x i) (yn : ∀ i ∈ I, 0 ≤ y i)
    (a r : ℝ) (ha : 0< a) (hr : 0< r) (total : a+r=1) (A E : ℝ) (hE : 0≤ E)
    (layer : ∀ i ∈ I,h i ≤ A*y i + E*x i^a*y i^r) :
    ∑ i ∈ I,w i*h i ≤ A*(∑ i ∈ I,w i*y i) + E*(∑ i ∈ I,w i*x i)^a*(∑ i ∈ I,w i*y i)^r := by
  calc
    _ ≤ ∑ i ∈ I,w i*(A*y i + E*x i^a*y i^r) := sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (layer i hi) (wn i hi)
    _ = A*(∑ i ∈ I,w i*y i) + E*(∑ i ∈ I,w i*x i^a*y i^r) := by
      rw [mul_sum,mul_sum,←sum_add_distrib]; refine sum_congr rfl fun i _ => ?_; ring
    _ ≤ _ := by rw [mul_assoc E]; exact add_le_add_right (mul_le_mul_of_nonneg_left (weighted_holder I w x y wn xn yn a r ha hr total) hE) _

end TenenbaumLayers
end

section
/- Marking one prime in a finite Euler sum. The coefficient may be any arithmetic function. -/

namespace TenenbaumMoments
open Finset Real

/-- Mark a member of a subset by removing it and recording it in the complementary set. -/
theorem mark_powerset {α M : Type*} [DecidableEq α] [AddCommMonoid M]
    (P : Finset α) (F : Finset α → α → M) :
    (∑ S ∈ P.powerset, ∑ p ∈ S, F (S.erase p) p) =
      ∑ S ∈ P.powerset, ∑ p ∈ P \ S, F S p := by
  rw [sum_sigma',sum_sigma']
  apply sum_bij' (fun (x : Σ _ : Finset α, α) _ => ⟨x.1.erase x.2,x.2⟩)
    (fun (x : Σ _ : Finset α, α) _ => ⟨insert x.2 x.1,x.2⟩)
  · rintro ⟨S,p⟩ hx
    obtain ⟨sub,mem⟩ := mem_sigma.mp hx
    have sub' : S ⊆ P := mem_powerset.mp sub
    exact mem_sigma.mpr ⟨mem_powerset.mpr (erase_subset _ _ |>.trans sub'),mem_sdiff.mpr ⟨sub' mem,notMem_erase p S⟩⟩
  · rintro ⟨S,p⟩ hx
    obtain ⟨sub,mem⟩ := mem_sigma.mp hx
    exact mem_sigma.mpr ⟨mem_powerset.mpr (insert_subset (mem_sdiff.mp mem).1 (mem_powerset.mp sub)),mem_insert_self p S⟩
  · rintro ⟨S,p⟩ hx
    simp only [insert_erase (mem_sigma.mp hx).2]
  · rintro ⟨S,p⟩ hx
    simp only [erase_insert (mem_sdiff.mp (mem_sigma.mp hx).2).2]
  · intro x _
    rfl

/-- The Mellin weight of a product is the product of the local weights. -/
theorem euler_weight (S : Finset ℕ) (ρ : ℕ → ℝ) (t : ℝ) :
    (∏ q ∈ S, ρ q /(q:ℝ)^t) = (∏ q ∈ S, ρ q) / ((∏ q ∈ S,q : ℕ):ℝ)^t := by
  rw [prod_div_distrib]
  congr 1
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p s np ih =>
    rw [prod_insert np,prod_insert np,Nat.cast_mul,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),ih]

/-- The negative derivative of the finite squarefree moment sum marks an absent prime.
Taking `A m = M_q(m)^u` gives the differentiated sum from the moment argument. -/
theorem marked_euler (P : Finset ℕ) (pos : ∀ p ∈ P, 0 < p) (ρ A : ℕ → ℝ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∑ S ∈ P.powerset,
      A (∏ q ∈ S,q) * (∏ q ∈ S,ρ q) / ((∏ q ∈ S,q : ℕ):ℝ)^(1+t))
      (-(∑ S ∈ P.powerset, ∑ p ∈ P \ S,
        log (p:ℝ) * (ρ p /(p:ℝ)^(1+s)) * A (p * ∏ q ∈ S,q) * (∏ q ∈ S, ρ q /(q:ℝ)^(1+s)))) s := by
  let a (q : ℕ) (t : ℝ) := ρ q /(q:ℝ)^(1+t)
  have single (q : ℕ) (hq : q∈P) : HasDerivAt (a q) (-(log (q:ℝ) * a q s)) s := by
    have qp : (0:ℝ) < q := by exact_mod_cast pos q hq
    have der : HasDerivAt (fun t : ℝ => -(1+t)) (-1) s := by
      exact ((hasDerivAt_id s).const_add (1:ℝ)).neg
    have coeff := (der.const_rpow qp).const_mul (ρ q)
    convert! coeff using 1
    · ext t
      simp only [a,Real.rpow_neg qp.le,div_eq_mul_inv]
    · dsimp [a]
      rw [Real.rpow_neg qp.le]
      ring
  let marked (S : Finset ℕ) (p : ℕ) := log (p:ℝ)*a p s*A (p*∏ q∈S,q)*(∏ q∈S,a q s)
  have atom (S : Finset ℕ) (hS : S∈P.powerset) :
      HasDerivAt (fun t => A (∏ q∈S,q)*(∏ q∈S,a q t)) (-(∑ p∈S,marked (S.erase p) p)) s := by
    have diff := (HasDerivAt.fun_finsetProd (u:=S) fun q hq => single q (mem_powerset.mp hS hq)).const_mul (A (∏ q∈S,q))
    convert! diff using 1
    simp only [mul_sum,←sum_neg_distrib]
    apply sum_congr rfl
    intro p hp
    change -(log (p:ℝ)*a p s*A (p*∏ q∈S.erase p,q)*(∏ q∈S.erase p,a q s)) = _
    rw [S.mul_prod_erase (fun j => j) hp]
    simp only [smul_eq_mul]
    ring
  have derivative := HasDerivAt.fun_sum atom
  convert! derivative using 1
  · ext t
    apply sum_congr rfl
    intro S _
    change _ = A _ *(∏ q ∈ S, ρ q / (q:ℝ)^(1+t))
    rw [euler_weight]
    ring
  · change -(∑ S∈P.powerset, ∑ p∈P\S, marked S p) = _
    rw [←mark_powerset, sum_neg_distrib]

end TenenbaumMoments
end

section
namespace TenenbaumLayers
open Finset Real
open scoped Classical

theorem finite_moment_slope (P : Finset ℕ) (primes : ∀ p ∈ P, p.Prime)
    (q : ℕ) (hq : 2 < q) (u t : ℝ) (hu : 0 ≤ u) (hu' : u ≤ 1) (qt : (q:ℝ)*u=t)
    (ρ : ℕ → ℝ) (D A C ν s : ℝ) (hD : 0≤ D) (hA : 0≤ A) (hC : 0≤ C) (hs : 0< s)
    (rn : ∀ p ∈ P, 0≤ ρ p) (upper : ∀ p ∈ P, ρ p ≤ D) :
    let Z (p : ℕ) := ρ p/(p:ℝ)^(1+s)
    let n (S : Finset ℕ) := ∏ p ∈ S,p
    let W (S : Finset ℕ) := ∏ p ∈ S,Z p
    let M (S : Finset ℕ) := moment (n S) q ^ u
    let L := ∑ S ∈ P.powerset,W S*M S
    let a := 1/((q:ℝ)-1)
    let r := ((q:ℝ)-2)/((q:ℝ)-1)
    (∑ p ∈ P,log p*Z p) ≤ A/s →
    (∑ S ∈ P.powerset,W S*(n S).divisors.card^t) ≤ C*s^(-ν) →
    (∑ S ∈ P.powerset,∑ p ∈ P\S,log p*Z p*(moment (p*n S) q)^u*W S) ≤
      (A*2^u)*L/s + (A^(1-u)*(D*(log 4*exp 1))^u*3^t*C^a)*s^(-(1-u+ν*a))*L^r := by
  intro Z n W M L a r total euler
  let x (S : Finset ℕ) := ((n S).divisors.card:ℝ)^t
  let F := (D*(log 4*exp 1))^u*(3:ℝ)^t
  let E := (A/s)^(1-u)*F
  let H (S : Finset ℕ) := ∑ p ∈ P\S,log p*Z p*(moment (p*n S) q)^u
  have non (b : ℕ) : 0 ≤ moment b q := MeasureTheory.integral_nonneg fun z => pow_nonneg (window_bounds b z).1 _
  have zn (p : ℕ) (hp : p ∈ P) : 0≤ Z p := div_nonneg (rn p hp) (rpow_nonneg (Nat.cast_nonneg _) _)
  have wn (S : Finset ℕ) (hS : S∈P.powerset) : 0≤ W S := prod_nonneg fun p hp => zn p (mem_powerset.mp hS hp)
  have mn (S : Finset ℕ) : 0≤ M S := rpow_nonneg (non _) _
  have xn (S : Finset ℕ) : 0≤ x S := rpow_nonneg (Nat.cast_nonneg _) _
  have fn : 0≤ F := mul_nonneg (rpow_nonneg (mul_nonneg hD (mul_nonneg (log_nonneg (by norm_num)) (exp_pos _).le)) _) (by positivity)
  have en : 0≤ E := mul_nonneg (rpow_nonneg (div_nonneg hA hs.le) _) fn
  have qreal : 2 < (q:ℝ) := by exact_mod_cast hq
  have denom : 0 < (q:ℝ)-1 := by linarith
  have aq : 0< a := one_div_pos.mpr denom
  have rr : 0< r := div_pos (by linarith) denom
  have ar : a+r=1 := by dsimp [a,r]; field_simp [denom.ne']; ring
  have layer (S : Finset ℕ) (sub : S∈P.powerset) : H S ≤ (2^u*(A/s))*M S + E*x S^a*M S^r := by
    have rp (p : ℕ) (hp : p∈P\S) := primes p (mem_sdiff.mp hp).1
    have fresh (p : ℕ) (hp : p∈P\S) : ¬p∣n S := by
      intro dv
      obtain ⟨d,hd,hpd⟩ := ((rp p hp).prime.dvd_finsetProd_iff (fun i : ℕ => i)).mp dv
      have eq := (Nat.prime_dvd_prime_iff_eq (rp p hp) (primes d (mem_powerset.mp sub hd))).mp hpd
      exact (mem_sdiff.mp hp).2 (eq ▸ hd)
    let T := ∑ p ∈ P\S,log p*Z p
    have sumpos : 0≤ T := sum_nonneg fun p hp => mul_nonneg (log_nonneg (by exact_mod_cast (rp p hp).one_le)) (zn p (mem_sdiff.mp hp).1)
    have bound : T ≤ A/s := (sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p hp _ => mul_nonneg (log_nonneg (by exact_mod_cast (primes p hp).one_le)) (zn p hp))).trans total
    have loc := logarithmic_fractional_step (P\S) rp (n S) q fresh (by omega) ρ D (1+s) hD (by linarith) (fun p hp => rn p (mem_sdiff.mp hp).1) (fun p hp => upper p (mem_sdiff.mp hp).1) u hu hu'
    dsimp only at loc
    have ident (p : ℕ) : ρ p * log (p:ℝ) / (p:ℝ)^(1+s) = log p*Z p := by dsimp [Z]; ring
    simp only [ident, mul_comm (n S) _,qt] at loc
    have ex : ((q:ℝ)/(q-1))*u=t*a := by dsimp [a]; rw [←qt]; ring
    have ey : (((q:ℝ)-2)/(q-1))*u=u*r := by dsimp [r]; ring
    rw [ex,ey,rpow_mul (Nat.cast_nonneg _),rpow_mul (non _)] at loc
    change H S ≤ 2^u*T*M S + T^(1-u)*(D*(log 4*exp 1))^u*3^t*x S^a*M S^r at loc
    apply loc.trans; apply add_le_add
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left bound (by positivity)) (mn S)
    · calc
        _ = T^(1-u)*F*x S^a*M S^r := by dsimp [F]; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (rpow_le_rpow sumpos bound (sub_nonneg.mpr hu')) fn) (rpow_nonneg (xn _) _)) (rpow_nonneg (mn _) _)
  have agg := sum_fractional_layers P.powerset W x M H wn (fun S _ => xn S) (fun S _ => mn S) a r aq rr ar (2^u*(A/s)) E en layer
  have lpos : 0 ≤ L := sum_nonneg fun S hS => mul_nonneg (wn S hS) (mn S)
  have masspos : 0 ≤ ∑ S ∈ P.powerset,W S*x S := sum_nonneg fun S hS => mul_nonneg (wn S hS) (xn S)
  have rest := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (rpow_le_rpow masspos euler aq.le) en) (rpow_nonneg lpos r)
  have lhs : ∑ S ∈ P.powerset, ∑ p ∈ P\S, log p*Z p*moment (p*n S) q^u*W S = ∑ S ∈ P.powerset,W S*H S := by
    apply sum_congr rfl;intro S _; dsimp only [H];rw [←sum_mul,mul_comm]
  rw [lhs]; refine agg.trans ((add_le_add_right rest _).trans_eq ?_)
  change 2^u*(A/s)*L+E*(C*s^(-ν))^a*L^r = _
  have excl : E*(C*s^(-ν))^a = (A^(1-u)*F*C^a)*s^(-(1-u+ν*a)) := by
    dsimp only [E]
    rw [div_rpow hA hs.le,mul_rpow hC (rpow_nonneg hs.le _),←rpow_mul hs.le,
      div_eq_mul_inv,←rpow_neg hs.le]
    have expo : -(1-u)+(-ν)*a= -(1-u+ν*a) := by ring
    rw [←expo,rpow_add hs]
    ring
  rw [excl]; dsimp only [F]; ring

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Real Set Filter

/-- Tenenbaum's differential inequality (2.13) has the power majorant (2.14).
The constant is uniform over differentiable functions and thus over finite
Dirichlet-series truncations. -/
theorem ode_comparison (a r α γ C B : ℝ) (hr : r < 1) (gap : a < γ)
    (balance : α + γ*r = γ+1) :
    ∃ K : ℝ, 0 < K ∧ ∀ L dL : ℝ → ℝ, L 2 ≤ B →
      (∀ σ ∈ Ioc (1:ℝ) 2, HasDerivAt L (dL σ) σ) →
      (∀ σ ∈ Ioc (1:ℝ) 2, -dL σ ≤ a*L σ/(σ-1) + C*(σ-1)^(-α)*(L σ)^r) →
      ∀ σ ∈ Ioc (1:ℝ) 2, L σ ≤ K*(σ-1)^(-γ) := by
  have eg : 0 < γ-a := sub_pos.mpr gap
  have grows : ∀ᶠ z : ℝ in atTop, C/(γ-a) < z^(1-r) :=
    (tendsto_rpow_atTop (sub_pos.mpr hr)).eventually_gt_atTop _
  obtain ⟨K,large,bound,positive⟩ := (grows.and ((eventually_ge_atTop B).and (eventually_gt_atTop (0:ℝ)))).exists
  have strict : a*K + C*K^r < γ*K := by
    have small := (div_lt_iff₀ eg).mp large
    have smaller := mul_lt_mul_of_pos_right small (rpow_pos_of_pos positive r)
    rw [mul_right_comm,←rpow_add positive,sub_add_cancel,rpow_one] at smaller
    nlinarith
  refine ⟨K,positive,?_⟩
  intro L dL start actual differential σ hσ
  let f (x : ℝ) := L (2-x)
  let F (x : ℝ) := K*(1-x)^(-γ)
  have dom (x : ℝ) (hx : x ∈ Icc 0 (2-σ)) : 2-x ∈ Ioc (1:ℝ) 2 := by
    obtain ⟨h1,h2⟩ := hx; obtain ⟨h3,h4⟩ := hσ; constructor <;> linarith
  have fd (x : ℝ) (hx : x ∈ Icc 0 (2-σ)) : HasDerivAt f (-dL (2-x)) x := by
    exact (actual (2-x) (dom x hx)).comp_const_sub 2
  have bd (x : ℝ) (hx : x ∈ Icc 0 (2-σ)) : HasDerivAt F (γ*K*(1-x)^(-γ-1)) x := by
    have lo := (dom x hx).1
    have step := ((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).rpow_const (p := -γ) (Or.inl (by change 1-x ≠ 0; linarith))
    exact (step.const_mul K).congr_deriv (by simp only [Pi.sub_apply,id_eq]; ring)
  have sign (x : ℝ) (hx : x ∈ Ico 0 (2-σ)) (eq : f x = F x) : -dL (2-x) < γ*K*(1-x)^(-γ-1) := by
    have inp := dom x (Ico_subset_Icc_self hx)
    have zp : 0 < 1-x := by have := inp.1; linarith
    have ed := differential (2-x) inp
    rw [show 2-x-1 = 1-x by ring] at ed
    change L (2-x) = K*(1-x)^(-γ) at eq
    rw [eq,mul_rpow positive.le (rpow_nonneg zp.le _),←rpow_mul zp.le] at ed
    have expo : -α + -γ*r = -γ-1 := by linarith
    apply lt_of_le_of_lt ed
    calc
      _ = (a*K+C*K^r)*(1-x)^(-γ-1) := by
        rw [rpow_sub_one zp.ne',div_eq_mul_inv]
        have join := rpow_add zp (-α) (-γ*r)
        rw [expo,rpow_sub_one zp.ne'] at join
        linear_combination (norm := ring_nf) -C*K^r*join
      _ < _ := mul_lt_mul_of_pos_right strict (rpow_pos_of_pos zp _)
  have fence := image_le_of_deriv_right_lt_deriv_boundary'
    (fun x hx => (fd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (fd x (Ico_subset_Icc_self hx)).hasDerivWithinAt)
    (by simpa [f,F] using start.trans bound : f 0 ≤ F 0)
    (fun x hx => (bd x hx).continuousAt.continuousWithinAt)
    (fun x hx => (bd x (Ico_subset_Icc_self hx)).hasDerivWithinAt) sign
    (right_mem_Icc.mpr (sub_nonneg.mpr hσ.2))
  simpa only [f,F,sub_sub_cancel,show 1-(2-σ)=σ-1 by ring] using fence

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Real Set

/-- Rescale the ODE majorant to an arbitrary short interval 0< s≤ s₀ while
keeping the constant independent of the particular differentiable function. -/
theorem local_barrier (a r α γ E B s₀ : ℝ) (hs₀ : 0< s₀) (hr : r<1) (gap : a< γ)
    (balance : α+γ*r=γ+1) :
    ∃ K : ℝ, 0< K ∧ ∀ L dL : ℝ → ℝ, L s₀ ≤ B →
      (∀ s ∈ Ioc (0:ℝ) s₀, HasDerivAt L (dL s) s) →
      (∀ s ∈ Ioc (0:ℝ) s₀, -dL s ≤ a*L s/s + E*s^(-α)*(L s)^r) →
      ∀ s ∈ Ioc (0:ℝ) s₀, L s ≤ K*s^(-γ) := by
  obtain ⟨k,hk,control⟩ := ode_comparison a r α γ (s₀*E*s₀^(-α)) B hr gap balance
  refine ⟨k*s₀^γ,mul_pos hk (rpow_pos_of_pos hs₀ _),?_⟩
  intro L dL endpoint hd slope s h
  let g (σ : ℝ) := s₀*(σ-1)
  have dom (σ : ℝ) (hσ : σ∈Ioc 1 2) : g σ ∈ Ioc 0 s₀ := by
    obtain ⟨hx,hy⟩ := hσ
    exact ⟨mul_pos hs₀ (by linarith), by dsimp [g]; nlinarith⟩
  have gd (σ : ℝ) : HasDerivAt g s₀ σ := by
    have H := ((hasDerivAt_id σ).sub_const 1).const_mul s₀
    simpa only [g,id_eq,mul_one] using H
  have bound := control (L ∘ g) (fun σ => dL (g σ)*s₀) (by change L (s₀*(2-1)) ≤ B; norm_num; exact endpoint)
    (fun σ hσ => (hd _ (dom σ hσ)).comp σ (gd σ)) (by
      intro σ hσ
      have zp := sub_pos.mpr hσ.1
      have h := mul_le_mul_of_nonneg_right (slope _ (dom σ hσ)) hs₀.le
      change -(dL (g σ)*s₀) ≤ a*L (g σ)/(σ-1)+(s₀*E*s₀^(-α))*(σ-1)^(-α)*L (g σ)^r
      rw [←neg_mul];apply h.trans_eq
      have left : a*L (g σ)/g σ*s₀=a*L (g σ)/(σ-1) := by dsimp only [g]; field_simp
      rw [add_mul,left]
      change _ + E*(s₀*(σ-1))^(-α)*L (g σ)^r*s₀ = _
      rw [mul_rpow hs₀.le zp.le]; ring)
  have zpos : 0< s/s₀ := div_pos h.1 hs₀
  have zle : s/s₀≤1 := (div_le_one hs₀).mpr h.2
  have res := bound (1+s/s₀) ⟨by linarith,by linarith⟩
  have hit : g (1+s/s₀)=s := by dsimp [g]; field_simp; ring
  simp only [Function.comp_apply,hit,add_sub_cancel_left] at res
  rw [div_rpow h.1.le hs₀.le,rpow_neg hs₀.le,div_inv_eq_mul] at res
  exact res.trans_eq (by ring)

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open MeasureTheory Finset Real

theorem moment_le_divisors (b q : ℕ) (hq : 0< q) : moment b q ≤ (b.divisors.card:ℝ)^q := by
  obtain ⟨k,rfl⟩ : ∃ k,q=k+1 := ⟨q-1,by omega⟩
  have h := integral_mono (window_power_integrable b k) ((window_integrable b).mul_const ((b.divisors.card:ℝ)^k)) (fun t => by
    rw [pow_succ,mul_comm]; exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (window_bounds b t).1 (window_bounds b t).2 k) (window_bounds b t).1)
  rw [integral_mul_const] at h
  have main : (∫ t,window b t) = b.divisors.card := by simpa [moment] using moment_one b
  rw [main,mul_comm,←pow_succ] at h
  exact h

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Finset Real Set

/-- Uniform bound for each finite squarefree Mellin sum. Only the two
prime/Euler supplies in the short strip are needed; neither an infinite
Dirichlet-series derivative nor differentiability of an asymptotic is used. -/
theorem uniform_squarefree_moment (q : ℕ) (hq : 2< q) (u t ν : ℝ) (hu : 0≤ u) (hu' : u≤1)
    (qt : (q:ℝ)*u=t) (D A C s₀ : ℝ) (hD : 0≤ D) (hA : 0≤ A) (hC : 0≤ C) (hs₀ : 0< s₀)
    (gap : A*2^u < ν-t+u) :
    ∃ K : ℝ, 0< K ∧ ∀ (P : Finset ℕ) (ρ : ℕ → ℝ), (∀ p ∈ P,p.Prime) →
      (∀ p ∈ P,0≤ ρ p) → (∀ p ∈ P,ρ p≤ D) →
      (∀ s ∈ Ioc (0:ℝ) s₀, ∑ p ∈ P,log (p:ℝ)*(ρ p/(p:ℝ)^(1+s)) ≤ A/s) →
      (∀ s ∈ Ioc (0:ℝ) s₀, ∑ S ∈ P.powerset, (∏ p ∈ S,ρ p/(p:ℝ)^(1+s))*
          ((∏ p ∈ S,p : ℕ).divisors.card:ℝ)^t ≤ C*s^(-ν)) →
      ∀ s ∈ Ioc (0:ℝ) s₀, ∑ S ∈ P.powerset, moment (∏ p ∈ S,p) q^u *
        (∏ p ∈ S,ρ p)/((∏ p ∈ S,p : ℕ):ℝ)^(1+s) ≤ K*s^(-(ν-t+u)) := by
  let a := 1/((q:ℝ)-1)
  let r := ((q:ℝ)-2)/((q:ℝ)-1)
  let E := A^(1-u)*(D*(log 4*exp 1))^u*3^t*C^a
  have qreal : 2<(q:ℝ) := by exact_mod_cast hq
  have denom : 0<(q:ℝ)-1 := by linarith
  have hr : r<1 := (div_lt_iff₀ denom).mpr (by linarith)
  have eqn : (1-u+ν*a) + (ν-t+u)*r = (ν-t+u)+1 := by
    dsimp [a,r]; rw [←qt]; field_simp [denom.ne']; ring
  obtain ⟨K,kpos,control⟩ := local_barrier (A*2^u) r (1-u+ν*a) (ν-t+u) E (C*s₀^(-ν)) s₀ hs₀ hr gap eqn
  refine ⟨K,kpos,?_⟩
  intro P ρ primes rn upper total euler
  let n (S : Finset ℕ) := ∏ p ∈ S,p
  let w (s : ℝ) (p : ℕ) := ρ p/(p:ℝ)^(1+s)
  let F (b : ℕ) := moment b q^u
  let L (s : ℝ) := ∑ S ∈ P.powerset, F (n S)*(∏ p ∈ S,ρ p)/((n S:ℕ):ℝ)^(1+s)
  let dL (s : ℝ) := -(∑ S ∈ P.powerset,∑ p ∈ P\S,log p*w s p*F (p*n S)*(∏ p ∈ S,w s p))
  have weight (s : ℝ) : (∑ S ∈ P.powerset,(∏ p ∈ S,w s p)*F (n S))=L s := by
    apply sum_congr rfl; intro S _
    change (∏ p ∈ S,ρ p/(p:ℝ)^(1+s))*F (n S) = _
    rw [TenenbaumMoments.euler_weight]; dsimp only [n]; ring
  have init : L s₀ ≤ C*s₀^(-ν) := by
    rw [←weight]
    apply le_trans _ (euler _ (right_mem_Ioc.mpr hs₀))
    apply sum_le_sum;intro S hS
    have wn : 0 ≤ ∏ p ∈ S,w s₀ p := prod_nonneg fun p hp => div_nonneg (rn p (mem_powerset.mp hS hp)) (rpow_nonneg (Nat.cast_nonneg _) _)
    apply mul_le_mul_of_nonneg_left _ wn
    have mn : 0 ≤ moment (n S) q := MeasureTheory.integral_nonneg fun z => pow_nonneg (window_bounds _ _).1 _
    have bound := rpow_le_rpow mn (moment_le_divisors (n S) q (by omega)) hu
    rwa [←rpow_natCast,←rpow_mul (Nat.cast_nonneg _),qt] at bound
  apply control L dL init
  · intro s _; exact TenenbaumMoments.marked_euler P (fun p hp => (primes p hp).pos) ρ F s
  · intro s range
    have bound := finite_moment_slope P primes q hq u t hu hu' qt ρ D A C ν s hD hA hC range.1 rn upper (total s range) (euler s range)
    change -dL s ≤ A*2^u*L s/s + E*s^(-(1-u+ν*a))*L s^r
    rw [←weight]; simpa only [dL,neg_neg] using bound

end TenenbaumLayers
end

section
namespace TenenbaumMoments
open Finset Real

/-- Enlarge the squarefree expansion to a complete finite Dirichlet sum and apply Bernoulli to its Euler factors. -/
theorem euler_mass_of_interval (P : Finset ℕ) (primes : ∀ p ∈ P, p.Prime)
    (f : ℕ → ℝ) (f1 : f 1 = 1) (fm : ∀ a b, Nat.Coprime a b → f (a*b) = f a * f b)
    (fn : ∀ a, 0 ≤ f a) (z : ℝ) (hz : 1 ≤ z) :
    ∏ p ∈ P, (1+z*f p) ≤ (∑ m ∈ Icc 1 (∏ p ∈ P,p), f m)^z := by
  have fac (S : Finset ℕ) (ps : ∀ p ∈ S, p.Prime) : (∏ p ∈ S, f p) = f (∏ p ∈ S,p) := by
    induction S using Finset.induction_on with
    | empty => simp [f1]
    | @insert a s ha ih =>
      have prime := ps a (mem_insert_self a s)
      have sp (p : ℕ) (hp : p ∈ s) := ps p (mem_insert_of_mem hp)
      have cop : Nat.Coprime a (∏ p ∈ s,p) := Nat.coprime_prod_right_iff.mpr
        fun p hp => (Nat.coprime_primes prime (sp p hp)).mpr (fun eq => ha (eq.symm ▸ hp))
      rw [prod_insert ha,prod_insert ha,fm a _ cop,ih sp]
  let prodS (S : Finset ℕ) := ∏ q ∈ S, q
  have inj : Set.InjOn prodS (P.powerset : Set (Finset ℕ)) := by
    intro S hS T hT eq
    apply_fun Nat.primeFactors at eq
    have a := Nat.primeFactors_prod (fun q hq => primes q ((mem_powerset.mp hS) hq))
    have b := Nat.primeFactors_prod (fun q hq => primes q ((mem_powerset.mp hT) hq))
    exact a.symm.trans (eq.trans b)
  have inside : P.powerset.image prodS ⊆ Icc 1 (prodS P) := by
    intro m hm
    obtain ⟨S,mem,rfl⟩ := mem_image.mp hm
    have sub := mem_powerset.mp mem
    exact mem_Icc.mpr ⟨prod_pos fun p hp => (primes p (sub hp)).pos,
      prod_le_prod_of_subset_of_one_le sub (fun _ _ => Nat.zero_le _) (fun p hp _ => (primes p hp).one_le)⟩
  have ordinary : (∏ p ∈ P, (1 + f p)) ≤ ∑ m ∈ Icc 1 (prodS P), f m := by
    rw [prod_one_add]
    calc
      _ = ∑ S ∈ P.powerset, f (prodS S) := sum_congr rfl fun S hS =>
        fac S (fun p hp => primes p (mem_powerset.mp hS hp))
      _ = ∑ n ∈ P.powerset.image prodS, f n := (sum_image inj).symm
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg inside (fun n _ _ => fn n)
  calc
    _ ≤ ∏ p ∈ P, (1+f p)^z := prod_le_prod
      (fun p _ => by have := fn p; positivity)
      (fun p _ => one_add_mul_self_le_rpow_one_add (by linarith [fn p]) hz)
    _ = (∏ p ∈ P, (1+f p))^z := Real.finsetProd_rpow P _ (fun p _ => by linarith [fn p]) z
    _ ≤ _ := Real.rpow_le_rpow (prod_nonneg (fun p _ => by linarith [fn p])) ordinary (by linarith)

theorem tau_euler_mass (P : Finset ℕ) (primes : ∀ p ∈ P, p.Prime)
    (ρ : ℕ → ℝ) (r1 : ρ 1 = 1) (rm : ∀ a b, Nat.Coprime a b → ρ (a*b) = ρ a*ρ b)
    (rn : ∀ n, 0 ≤ ρ n) (s t C : ℝ) (ht : 0 ≤ t)
    (ordinary : ∀ N : ℕ, (∑ n ∈ Icc 1 N, ρ n/(n:ℝ)^(1+s)) ≤ C/s) :
    ∏ p ∈ P, (1+(2:ℝ)^t*(ρ p/(p:ℝ)^(1+s))) ≤ (C/s)^((2:ℝ)^t) := by
  let f (n : ℕ) := ρ n/(n:ℝ)^(1+s)
  have fn (n : ℕ) : 0 ≤ f n := div_nonneg (rn n) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have fm (a b : ℕ) (h : Nat.Coprime a b) : f (a*b) = f a * f b := by
    simp only [f,Nat.cast_mul,rm a b h,Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),div_mul_div_comm]
  have hz : (1:ℝ) ≤ 2^t := Real.one_le_rpow (by norm_num) ht
  exact (euler_mass_of_interval P primes f (by simp [f,r1]) fm fn _ hz).trans
    (Real.rpow_le_rpow (sum_nonneg (fun n _ => fn n)) (ordinary _) (zero_le_one.trans hz))

end TenenbaumMoments

namespace TenenbaumMoments
open Finset Real

/-- Each distinct prime factor doubles the divisor count of a squarefree product. -/
theorem tau_product (S : Finset ℕ) (primes : ∀ p ∈ S, p.Prime) : (∏ p ∈ S,p).divisors.card = 2^S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | @insert p S hp ih =>
    have pp := primes p (mem_insert_self p S)
    have qs (q : ℕ) (hq : q ∈ S) := primes q (mem_insert_of_mem hq)
    have cop : Nat.Coprime p (∏ q ∈ S,q) := Nat.coprime_prod_right_iff.mpr
      fun q hq => (Nat.coprime_primes pp (qs q hq)).mpr (fun eq => hp (eq.symm ▸ hq))
    rw [prod_insert hp,cop.card_divisors_mul,ih qs,pp.divisors,card_insert_of_notMem hp,pow_succ]
    simp [Ne.symm pp.ne_one,mul_comm]

/-- The weighted divisor-power mass over all squarefree subsets is its finite Euler product. -/
theorem tau_sum_euler (P : Finset ℕ) (primes : ∀ p ∈ P, p.Prime) (t : ℝ) (f : ℕ → ℝ) :
    (∑ S ∈ P.powerset, ((∏ q ∈ S,q).divisors.card:ℝ)^t * ∏ q ∈ S, f q) =
      ∏ p ∈ P, (1+(2:ℝ)^t*f p) := by
  rw [prod_one_add]
  apply sum_congr rfl
  intro S sm
  have ps (p : ℕ) (hp : p ∈ S) := primes p (mem_powerset.mp sm hp)
  rw [tau_product S ps,prod_mul_distrib,prod_const]
  congr 1
  push_cast
  rw [←rpow_natCast (2:ℝ),←rpow_mul (by norm_num : (0:ℝ) ≤ 2),
    ←rpow_natCast ((2:ℝ)^t),←rpow_mul (by norm_num : (0:ℝ) ≤ 2),mul_comm]

/-- A Dirichlet sum bound also controls the full divisor-power moment on finite prime supports. -/
theorem tau_power_mass (P : Finset ℕ) (primes : ∀ p ∈ P, p.Prime)
    (ρ : ℕ → ℝ) (r1 : ρ 1 = 1) (rm : ∀ a b, Nat.Coprime a b → ρ (a*b) = ρ a*ρ b)
    (rn : ∀ n, 0 ≤ ρ n) (s t C : ℝ) (ht : 0 ≤ t)
    (ordinary : ∀ N : ℕ, (∑ n ∈ Icc 1 N, ρ n/(n:ℝ)^(1+s)) ≤ C/s) :
    (∑ S ∈ P.powerset, ((∏ q ∈ S,q).divisors.card:ℝ)^t *
      ∏ p ∈ S, (ρ p/(p:ℝ)^(1+s))) ≤ (C/s)^((2:ℝ)^t) := by
  rw [tau_sum_euler P primes]
  exact tau_euler_mass P primes ρ r1 rm rn s t C ht ordinary

end TenenbaumMoments
end

section
namespace TenenbaumLayers
open Finset Real Set

/-- The two global inputs suffice: a linear bound for the ordinary Dirichlet
sum and the sharp prime logarithmic sum near its simple pole. -/
theorem uniform_squarefree_of_prime_sums (ρ : ℕ → ℝ) (r1 : ρ 1 = 1)
    (rm : ∀ a b, Nat.Coprime a b → ρ (a*b)=ρ a*ρ b) (rn : ∀ n, 0≤ ρ n)
    (q : ℕ) (hq : 2< q) (u t : ℝ) (hu : 0≤ u) (hu' : u≤1) (qt : (q:ℝ)*u=t)
    (D A C s₀ : ℝ) (hD : 0≤ D) (hA : 0≤ A) (hC : 0≤ C) (hs₀ : 0< s₀)
    (cap : ∀ p : ℕ, p.Prime → ρ p≤ D) (gap : A*2^u < 2^t-t+u)
    (ordinary : ∀ s ∈ Ioc (0:ℝ) s₀, ∀ N : ℕ, ∑ n ∈ Icc 1 N,ρ n/(n:ℝ)^(1+s) ≤ C/s)
    (prime_sum : ∀ s ∈ Ioc (0:ℝ) s₀, ∀ P : Finset ℕ, (∀ p ∈ P,p.Prime) →
      ∑ p ∈ P,log (p:ℝ)*(ρ p/(p:ℝ)^(1+s)) ≤ A/s) :
    ∃ K : ℝ, 0< K ∧ ∀ P : Finset ℕ, (∀ p ∈ P,p.Prime) → ∀ s ∈ Ioc (0:ℝ) s₀,
      ∑ S ∈ P.powerset,moment (∏ p ∈ S,p) q^u * (∏ p ∈ S,ρ p)/((∏ p ∈ S,p : ℕ):ℝ)^(1+s) ≤ K*s^(-(2^t-t+u)) := by
  obtain ⟨K,hK,main⟩ := uniform_squarefree_moment q hq u t (2^t) hu hu' qt D A (C^(2^t)) s₀ hD hA (rpow_nonneg hC _) hs₀ gap
  refine ⟨K,hK,fun P primes => main P ρ primes (fun p _ => rn p) (fun p hp => cap p (primes p hp)) (fun s h => prime_sum s h P primes) ?_⟩
  intro s hs
  have ht : 0≤ t := qt ▸ mul_nonneg (Nat.cast_nonneg _) hu
  have bound := TenenbaumMoments.tau_power_mass P primes ρ r1 rm rn s t C ht (ordinary s hs)
  calc
    _ = ∑ S ∈ P.powerset,((∏ p ∈ S,p : ℕ).divisors.card:ℝ)^t * ∏ p ∈ S,ρ p/(p:ℝ)^(1+s) := by
      apply sum_congr rfl;intro S _;rw [mul_comm]
    _ ≤ _ := bound
    _ = _ := by rw [div_rpow hC hs.1.le,div_eq_mul_inv,←rpow_neg hs.1.le]

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Finset Real

/-- Embed a truncated sum on squarefree integers into the finite Mellin sum
by sending each integer to the set of its prime factors. -/
theorem squarefree_mellin_cut (N : ℕ) (ρ F : ℕ → ℝ) (r1 : ρ 1 = 1)
    (rm : ∀ a b, Nat.Coprime a b → ρ (a*b)=ρ a*ρ b) (rn : ∀ b,0≤ ρ b)
    (fn : ∀ b,0≤ F b) (s : ℝ) :
    ∑ b ∈ (Icc 1 N).filter Squarefree, ρ b * F b / (b:ℝ)^(1+s) ≤
      ∑ S ∈ (Nat.primesLE N).powerset,F (∏ p ∈ S,p) * (∏ p ∈ S,ρ p)/((∏ p ∈ S,p : ℕ):ℝ)^(1+s) := by
  classical
  let T := (Icc 1 N).filter Squarefree
  let term (S : Finset ℕ) := F (∏ p ∈ S,p) * (∏ p ∈ S,ρ p) / ((∏ p ∈ S,p : ℕ):ℝ)^(1+s)
  have fac (S : Finset ℕ) (ps : ∀ p∈S,p.Prime) : (∏ p∈S,ρ p)=ρ (∏p∈S,p) := by
    induction S using Finset.induction_on with
    | empty => simp [r1]
    | @insert a S na ih =>
      have ap := ps a (mem_insert_self a S)
      have sp (p : ℕ) (hp : p∈S) := ps p (mem_insert_of_mem hp)
      have cp := Nat.coprime_prod_right_iff.mpr (fun p hp => (Nat.coprime_primes ap (sp p hp)).mpr (fun eq => na (eq.symm ▸ hp)))
      rw [prod_insert na,prod_insert na,rm a _ cp,ih sp]
  have part : T.image Nat.primeFactors ⊆ (Nat.primesLE N).powerset := by
    intro S hS; obtain ⟨b,hb,rfl⟩ := mem_image.mp hS
    refine mem_powerset.mpr fun p hp => ?_
    have per := Nat.mem_primeFactors.mp hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one ((mem_Icc.mp (mem_filter.mp hb).1).1)) per.2.1).trans (mem_Icc.mp (mem_filter.mp hb).1).2,per.1⟩
  calc
    _ = ∑ S ∈ T.image Nat.primeFactors,term S := by
      rw [sum_image]
      · apply sum_congr rfl; intro b hb;dsimp only [term]
        rw [fac _ (fun p hp => (Nat.mem_primeFactors.mp hp).1),Nat.prod_primeFactors_of_squarefree (mem_filter.mp hb).2,mul_comm]
      · intro a ha b hb eq
        have hx := congrArg (fun S : Finset ℕ => ∏ p∈S,p) eq
        simpa only [Nat.prod_primeFactors_of_squarefree (mem_filter.mp ha).2,Nat.prod_primeFactors_of_squarefree (mem_filter.mp hb).2] using hx
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg part fun S _ _ => div_nonneg (mul_nonneg (fn _) (prod_nonneg fun p _ => rn p)) (rpow_nonneg (Nat.cast_nonneg _) _)

end TenenbaumLayers
end

section
/- A single moment order suffices for each prescribed loss ε. -/

namespace TenenbaumMoments
open Real

theorem choose_order (ε : ℝ) (ep : 0 < ε) :
    ∃ q : ℕ, 2 < q ∧
      (5/4 : ℝ)*2^((3/2 : ℝ)/q) < 2*sqrt 2-3/2+(3/2:ℝ)/q ∧
      2*sqrt 2-3/2+(3/2:ℝ)/q < 2*sqrt 2-3/2+ε := by
  obtain ⟨q,hq⟩ := exists_nat_gt (max (100:ℝ) ((3/2:ℝ)/ε))
  have big := (le_max_left _ _).trans_lt hq
  have height := (le_max_right _ _).trans_lt hq
  have pos : (0:ℝ)< q := by linarith
  let u := (3/2:ℝ)/q
  have up : 0< u := div_pos (by norm_num) pos
  have sm : u < 1/50 := (div_lt_iff₀ pos).mpr (by linarith)
  have ue : u < ε := (div_lt_iff₀ pos).mpr (by have z := (div_lt_iff₀ ep).mp height; linarith)
  have l2 : log 2 ≤ 1 := by linarith [log_le_sub_one_of_pos (by norm_num : 0<(2:ℝ))]
  have ub : (2:ℝ)^u ≤ exp u := by rw [rpow_def_of_pos (by norm_num)]; exact exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_nonneg.mpr l2) up.le])
  have neg := add_one_le_exp (-u)
  rw [exp_neg] at neg
  have mult : (1-u)*exp u ≤ 1 := by
    have h : 1-u ≤ 1/exp u := by simpa [one_div, sub_eq_add_neg, add_comm] using neg
    exact (le_div_iff₀ (exp_pos _)).mp h
  have eu : exp u < 26/25 := by nlinarith [mul_pos (show 1/50-u>0 by linarith) (exp_pos u)]
  have sq : (7/5:ℝ) < sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : 0≤(2:ℝ)), Real.sqrt_nonneg 2]
  refine ⟨q, by exact_mod_cast (show (2:ℝ)< q by linarith), ?_, by linarith only [ue]⟩
  change (5/4:ℝ)*2^u < 2*sqrt 2-3/2+u
  linarith

end TenenbaumMoments
end

section
/- Recovering the finite harmonic sum from positive Dirichlet coefficients. -/

namespace TenenbaumLayers
open Finset Filter Real

/-- At σ=1+1/log n, each nonnegative term with index b≤ n loses at most e. -/
theorem harmonic_truncation (n : ℕ) (hn : 1 < n) (T : Finset ℕ)
    (inside : ∀ b ∈ T, 0 < b ∧ b ≤ n) (A : ℕ → ℝ) (positive : ∀ b ∈ T, 0 ≤ A b) :
    (∑ b ∈ T, A b / (b : ℝ)) ≤ exp 1 *
      ∑ b ∈ T, A b / (b : ℝ)^(1+(log n)⁻¹) := by
  have lp := log_pos (show (1:ℝ)< n by exact_mod_cast hn)
  rw [mul_sum]
  refine sum_le_sum fun b hb => ?_
  obtain ⟨bp, bn⟩ := inside b hb
  have br : 0 < (b:ℝ) := by exact_mod_cast bp
  have ratio : log b * (log n)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one lp]
    exact log_le_log br (by exact_mod_cast bn)
  have supply : (b:ℝ)^((log n)⁻¹) ≤ exp 1 := by
    rw [rpow_def_of_pos br]; exact exp_le_exp.mpr ratio
  rw [rpow_add br, rpow_one]
  have pp : 0 < (b:ℝ)^((log n)⁻¹) := rpow_pos_of_pos br _
  calc
    _ = (b:ℝ)^((log n)⁻¹) * (A b / (b * (b:ℝ)^((log n)⁻¹))) := by field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_right supply (by positivity [positive b hb])

/-- A fixed constant and a fixed-order loss can be absorbed in any strictly
larger logarithmic exponent. The coefficients may vary with n. -/
theorem absorb_log_constant (A : ℕ → ℝ) (K β J : ℝ) (gap : β < J)
    (bound : ∀ᶠ n : ℕ in atTop, A n ≤ K*(log n)^β) :
    ∀ᶠ n : ℕ in atTop, A n ≤ (log n)^J := by
  have logGrow := tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have grow := ((tendsto_rpow_atTop (sub_pos.mpr gap)).comp logGrow).eventually_ge_atTop K
  filter_upwards [bound,grow, eventually_ge_atTop (2:ℕ)] with n h g big
  have pos : 0 < log (n:ℝ) := log_pos (by exact_mod_cast (show 1< n by omega))
  calc
    _ ≤ K*(log n)^β := h
    _ ≤ (log n)^(J-β)*(log n)^β := mul_le_mul_of_nonneg_right g (rpow_nonneg pos.le _)
    _ = (log n)^J := by rw [← rpow_add pos]; congr 1; ring

/-- The Mellin cutoff turns a uniform s^{-γ} estimate for finite Dirichlet
polynomials into logarithmic growth, with an arbitrarily small slack. -/
theorem harmonic_of_dirichlet (A : ℕ → ℝ) (T : ℕ → Finset ℕ)
    (inside : ∀ n b, b ∈ T n → 0 < b ∧ b ≤ n) (nonneg : ∀ b,0 ≤ A b)
    {K γ J s₀ : ℝ} (hp : 0 < s₀) (gap : γ < J)
    (series : ∀ᶠ n : ℕ in atTop, ∀ s : ℝ, 0 < s → s ≤ s₀ →
      (∑ b ∈ T n, A b / (b:ℝ)^(1+s)) ≤ K*s^(-γ)) :
    ∀ᶠ n : ℕ in atTop, (∑ b ∈ T n, A b / b) ≤ (log n)^J := by
  apply absorb_log_constant _ (exp 1*K) γ J gap
  filter_upwards [series, (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop s₀⁻¹,
    eventually_ge_atTop (2:ℕ)] with n hs wide big
  change s₀⁻¹ ≤ log (n:ℝ) at wide
  have pos : 0 < log (n:ℝ) := (inv_pos.mpr hp).trans_le wide
  have chosen := hs ((log n)⁻¹) (inv_pos.mpr pos) (by simpa using (inv_anti₀ (inv_pos.mpr hp) wide))
  have cmp := harmonic_truncation n (by omega) (T n) (inside n) A (fun b _ => nonneg b)
  apply cmp.trans
  calc
    _ ≤ exp 1*(K*((log n)⁻¹)^(-γ)) := mul_le_mul_of_nonneg_left chosen (exp_pos _).le
    _ = _ := by rw [inv_rpow pos.le, rpow_neg pos.le, inv_inv]; ring

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Finset Real Set Filter
open scoped Topology Classical

/-- Fractional moments of the required fixed order, given the two arithmetic
supplies and the squarefull transfer. The output has precisely the indexing in
Erdős 976, R1.H2.R1.H2. -/
theorem harmonic_terminal (ρ : ℕ → ℝ) (rn : ∀ n,0≤ ρ n) (unit : ρ 1=1)
    (mult : ∀ a b, Nat.Coprime a b → ρ (a*b)=ρ a*ρ b) (D : ℝ) (dn : 0≤ D)
    (cap : ∀ p : ℕ,p.Prime → ρ p≤ D)
    (supplies : ∃ s₀ > (0:ℝ), ∃ C ≥ (0:ℝ),
      (∀ s ∈ Ioc (0:ℝ) s₀, ∀ N : ℕ, (∑ n ∈ Icc 1 N, ρ n/(n:ℝ)^(1+s)) ≤ C/s) ∧
      (∀ s ∈ Ioc (0:ℝ) s₀, ∀ P : Finset ℕ, (∀ p ∈ P,p.Prime) →
        (∑ p ∈ P,log (p:ℝ)*(ρ p/(p:ℝ)^(1+s))) ≤ (5/4:ℝ)/s))
    (transfer : ∃ C : ℝ, 0≤ C ∧ ∀ N q : ℕ, 0< q → let e := 3/(2*(q:ℝ));
      (∑ n ∈ Icc 1 N,ρ n*moment n q^e/n) ≤ C*∑ a∈(Finset.Icc 1 N).filter Squarefree,ρ a*moment a q^e/a) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ᶠ N : ℕ in atTop,
      (∑ b ∈ Icc 1 N,ρ b*(moment b (k+1))^(3/(2*((k:ℝ)+1)):ℝ)/b) ≤ (log N)^(2*sqrt 2-3/2+ε) := by
  obtain ⟨Dfull,hDfull,complete⟩ := transfer
  obtain ⟨s₀,sp,C,cn,plain,prime⟩ := supplies
  intro ε ep
  obtain ⟨q,hq,coef,room⟩ := TenenbaumMoments.choose_order ε ep
  let u : ℝ := (3/2:ℝ)/q
  have qpos : 0<(q:ℝ) := by exact_mod_cast (show 0< q by omega)
  have up : 0≤ u := div_nonneg (by norm_num) qpos.le
  have qreal : (2:ℝ)< q := by exact_mod_cast hq
  have ul : u≤1 := (div_le_one qpos).mpr (by linarith)
  have qu : (q:ℝ)*u=3/2 := by dsimp [u];field_simp
  have nu : (2:ℝ)^(3/2:ℝ)=2*sqrt 2 := by
    rw [show (3/2:ℝ)=1+1/2 by norm_num,rpow_add (by norm_num : (0:ℝ)<2),rpow_one,←sqrt_eq_rpow]
  let γ := 2*sqrt 2-3/2+u
  let J := 2*sqrt 2-3/2+ε
  let mid := (γ+J)/2
  have room' : γ< J := room
  have gm : γ< mid := by dsimp [mid];linarith
  have mj : mid< J := by dsimp [mid];linarith
  have gap : (5/4:ℝ)*2^u < (2:ℝ)^(3/2:ℝ)-3/2+u := by rw [nu];exact coef
  obtain ⟨K,hK,mellin⟩ := uniform_squarefree_of_prime_sums ρ unit mult rn q hq u (3/2) up ul qu D (5/4) C s₀ dn (by norm_num) cn sp cap gap plain prime
  let F (b : ℕ) := moment b q^u
  let T (N : ℕ) := (Finset.Icc 1 N).filter Squarefree
  have fn (b : ℕ) : 0≤ F b := rpow_nonneg (MeasureTheory.integral_nonneg fun z => pow_nonneg (window_bounds b z).1 q) _
  have small := harmonic_of_dirichlet (fun b => ρ b*F b) T (by
    intro N b hb;exact (mem_Icc.mp (mem_filter.mp hb).1)) (fun b => mul_nonneg (rn b) (fn b)) sp gm (K:=K) (Filter.Eventually.of_forall (fun N s spos slim => by
      have big := mellin (Nat.primesLE N) (fun p hp => Nat.prime_of_mem_primesLE hp) s ⟨spos,slim⟩
      rw [nu] at big
      exact (squarefree_mellin_cut N ρ F unit mult rn fn s).trans big))
  have ee : 3/(2*(q:ℝ))=u := by dsimp [u];ring
  have all := absorb_log_constant (fun N => ∑ b ∈ Icc 1 N,ρ b*F b/b) Dfull mid J mj (by
    filter_upwards [small] with N hn
    have whole := complete N q (by omega)
    dsimp only at whole;rw [ee] at whole
    exact whole.trans (mul_le_mul_of_nonneg_left hn hDfull))
  obtain ⟨k,hk⟩ : ∃ k,q=k+1 := ⟨q-1,by omega⟩
  refine ⟨k,?_⟩
  have eqe : 3/(2*((k:ℝ)+1))=u := by simpa [hk] using ee
  simp only [eqe,←hk]; exact all

end TenenbaumLayers
end

section
/- The divisor window of a coprime product is a sum of translated windows.
Finite Jensen and translation invariance then bound its moments. -/

namespace TenenbaumLayers
open Finset Real MeasureTheory
open scoped Classical Pointwise

theorem window_mul_coprime {a s : ℕ} (cop : a.Coprime s) (t : ℝ) :
    window (a*s) t = ∑ d ∈ s.divisors, window a (t - log d) := by
  classical
  rw [Nat.mul_comm a s, window, Nat.divisors_mul, Finset.mul_def,
    Finset.sum_image cop.symm.mul_injOn_divisors, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro d hd
  unfold window
  apply Finset.sum_congr rfl
  intro e he
  have dp : (d:ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hd).ne'
  have ep : (e:ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors he).ne'
  rw [Nat.cast_mul, log_mul dp ep]
  have shift : t ∈ Set.Ico (log d + log e - 1) (log d + log e) ↔
      t-log d ∈ Set.Ico (log e-1) (log e) := by
    simp only [Set.mem_Ico]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  simp only [Set.indicator_apply, shift]

theorem moment_mul_le {a s : ℕ} (cop : a.Coprime s) (q : ℕ) :
    moment (a*s) (q+1) ≤ (s.divisors.card:ℝ)^(q+1) * moment a (q+1) := by
  let f (d : ℕ) (t : ℝ) := window a (t - log d)^(q+1)
  have integrable (d : ℕ) : Integrable (f d) :=
    (window_power_integrable a q).comp_sub_right (log d)
  calc
    _ ≤ ∫ t : ℝ, (s.divisors.card:ℝ)^q * ∑ d ∈ s.divisors, f d t := by
      apply integral_mono (window_power_integrable _ _) ((integrable_finsetSum _ fun d _ => integrable d).const_mul _)
      intro t
      dsimp only
      rw [window_mul_coprime cop]
      exact pow_sum_le_card_mul_sum_pow (s:=s.divisors) (fun d _ => (window_bounds a (t-log d)).1) q
    _ = (s.divisors.card:ℝ)^q * ∑ d ∈ s.divisors, moment a (q+1) := by
      rw [integral_const_mul, integral_finsetSum _ fun d _ => integrable d]
      congr 1
      apply Finset.sum_congr rfl
      intro d _
      exact integral_sub_right_eq_self (fun t : ℝ => window a t ^ (q+1)) _
    _ = _ := by simp [pow_succ, nsmul_eq_mul, mul_assoc]

end TenenbaumLayers
end

section
namespace TenenbaumLayers

def Squarefull (s : ℕ) : Prop := ∀ p : ℕ, p.Prime → p ∣ s → p^2 ∣ s

theorem squarefree_squarefull (n : ℕ) (hn : 0 < n) :
    ∃ a s : ℕ, n = a*s ∧ a.Coprime s ∧ Squarefree a ∧ Squarefull s := by
  revert hn
  refine Nat.recOnPrimePow ?_ ?_ ?_ n
  · intro h
    omega
  · intro _
    refine ⟨1,1,by simp,by simp,squarefree_one,?_⟩
    intro p hp h
    exact False.elim (hp.not_dvd_one h)
  · intro n p e hp fresh he ih hn
    obtain ⟨a,s,rfl,cop,ha,hs⟩ := ih (Nat.pos_of_mul_pos_left hn)
    have pa : p.Coprime a := hp.coprime_iff_not_dvd.mpr fun h => fresh (dvd_mul_of_dvd_left h _)
    have ps : p.Coprime s := hp.coprime_iff_not_dvd.mpr fun h => fresh (dvd_mul_of_dvd_right h _)
    by_cases e1 : e=1
    · subst e
      exact ⟨p*a,s,by simp [mul_assoc], ps.mul_left cop, (Nat.squarefree_mul pa).mpr ⟨hp.squarefree,ha⟩,hs⟩
    · refine ⟨a,p^e*s,by ac_rfl, (pa.symm.pow_right e).mul_right cop,ha,?_⟩
      intro l hl ld
      rcases hl.dvd_mul.mp ld with lpe | ls
      · obtain rfl := Nat.prime_dvd_prime_iff_eq hl hp |>.mp (hl.dvd_of_dvd_pow lpe)
        exact dvd_mul_of_dvd_left (pow_dvd_pow l (by omega : 2≤ e)) _
      · exact dvd_mul_of_dvd_right (hs l hl ls) _

open Finset
open scoped Classical

theorem separated_sum_le (N : ℕ) (F X Y : ℕ → ℝ)
    (hX : ∀ a, 0 ≤ X a) (hY : ∀ s, 0 ≤ Y s)
    (separate : ∀ a s : ℕ, a.Coprime s → Squarefree a → Squarefull s → F (a*s) ≤ X a * Y s) :
    ∑ n ∈ Icc 1 N, F n ≤ (∑ a ∈ (Icc 1 N).filter Squarefree, X a) *
      ∑ s ∈ (Icc 1 N).filter Squarefull, Y s := by
  classical
  have chooseParts (n : ℕ) : ∃ c : ℕ×ℕ, n = 0 ∨
      n=c.1*c.2 ∧ c.1.Coprime c.2 ∧ Squarefree c.1 ∧ Squarefull c.2 := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · exact ⟨(1,1), Or.inl hn⟩
    · obtain ⟨a,s,h⟩ := squarefree_squarefull n hn
      exact ⟨(a,s), Or.inr h⟩
  choose c hc using chooseParts
  have parts (n : ℕ) (hn : n ∈ Icc 1 N) := (hc n).resolve_left (Nat.ne_of_gt (mem_Icc.mp hn).1)
  let S := (Icc 1 N).filter Squarefree
  let T := (Icc 1 N).filter Squarefull
  have sub : (Icc 1 N).image c ⊆ S ×ˢ T := by
    intro x hx
    obtain ⟨n,hn,rfl⟩ := mem_image.mp hx
    obtain ⟨hprod,_,ha,hs⟩ := parts n hn
    obtain ⟨pos,upper⟩ := mem_Icc.mp hn
    have h : 0<(c n).1*(c n).2 := hprod ▸ pos
    have lo₁ := Nat.pos_of_mul_pos_right h
    have lo₂ := Nat.pos_of_mul_pos_left h
    have up₁ : (c n).1 ≤ N := (Nat.le_of_dvd pos ((dvd_mul_right (c n).1 (c n).2).trans (dvd_of_eq hprod.symm))).trans upper
    have up₂ : (c n).2 ≤ N := (Nat.le_of_dvd pos ((dvd_mul_left (c n).2 (c n).1).trans (dvd_of_eq hprod.symm))).trans upper
    exact mem_product.mpr ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨lo₁,up₁⟩,ha⟩,
      mem_filter.mpr ⟨mem_Icc.mpr ⟨lo₂,up₂⟩,hs⟩⟩
  have inj : Set.InjOn c ↑(Icc 1 N) := by
    intro i hi j hj e
    rw [(parts i hi).1, (parts j hj).1, e]
  calc
    _ ≤ ∑ n ∈ Icc 1 N, X (c n).1 * Y (c n).2 := by
      apply sum_le_sum
      intro n hn
      obtain ⟨eq,cop,ha,hs⟩ := parts n hn
      exact (congrArg F eq).le.trans (separate _ _ cop ha hs)
    _ = ∑ x ∈ (Icc 1 N).image c, X x.1 * Y x.2 := (sum_image (f:=fun x : ℕ×ℕ => X x.1*Y x.2) inj).symm
    _ ≤ ∑ x ∈ S ×ˢ T, X x.1 * Y x.2 := sum_le_sum_of_subset_of_nonneg sub
      fun x _ _ => mul_nonneg (hX _) (hY _)
    _ = _ := by rw [sum_product]; simp only [← mul_sum, ← sum_mul]; rfl

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open MeasureTheory Finset Real
open scoped Classical

/-- Separate the squarefull contribution at the fractional moment exponent. -/
theorem harmonic_squarefree_transfer (N q : ℕ) (hq : 0< q)
    (ρ : ℕ → ℝ) (rn : ∀ n, 0 ≤ ρ n)
    (mult : ∀ {a s : ℕ}, a.Coprime s → ρ (a*s)=ρ a*ρ s) :
    let e := 3/(2*(q:ℝ))
    (∑ n ∈ Icc 1 N, ρ n * (moment n q)^e / n) ≤
      (∑ a ∈ (Icc 1 N).filter Squarefree, ρ a * (moment a q)^e / a) *
      ∑ s ∈ (Icc 1 N).filter Squarefull, ρ s * (s.divisors.card:ℝ)^(3/2:ℝ) / s := by
  obtain ⟨l,rfl⟩ : ∃ l, q = l+1 := ⟨q-1,by omega⟩
  let e := 3/(2*((l+1:ℕ):ℝ))
  have ep : 0≤ e := by dsimp [e]; positivity
  have ev : ((l+1:ℕ):ℝ)*e=3/2 := by dsimp [e]; field_simp
  have mn (b : ℕ) : 0≤ moment b (l+1) :=
    integral_nonneg (fun t => pow_nonneg (window_bounds b t).1 _)
  apply separated_sum_le
  · intro a
    exact div_nonneg (mul_nonneg (rn a) (rpow_nonneg (mn a) _)) (Nat.cast_nonneg a)
  · intro s
    exact div_nonneg (mul_nonneg (rn s) (rpow_nonneg (Nat.cast_nonneg _) _)) (Nat.cast_nonneg s)
  · intro a s cop _ _
    have lift := rpow_le_rpow (mn (a*s)) (moment_mul_le cop l) ep
    rw [mul_rpow (pow_nonneg (Nat.cast_nonneg _) _) (mn _),
      ←rpow_natCast (s.divisors.card:ℝ) (l+1), ←rpow_mul (Nat.cast_nonneg _),ev] at lift
    rw [mult cop, Nat.cast_mul]
    exact (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left lift (mul_nonneg (rn a) (rn s)))
      (mul_nonneg (Nat.cast_nonneg a) (Nat.cast_nonneg s))).trans_eq (by ring)

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Finset Real
open scoped Classical

private theorem squarefull_mul {a b : ℕ} (cop : a.Coprime b) :
    Squarefull (a*b) ↔ Squarefull a ∧ Squarefull b := by
  constructor
  · intro h
    constructor
    · intro p hp hd
      exact ((cop.coprime_dvd_left hd).pow_left 2).dvd_of_dvd_mul_right
        (h p hp (dvd_mul_of_dvd_left hd b))
    · intro p hp hd
      exact ((cop.symm.coprime_dvd_left hd).pow_left 2).dvd_of_dvd_mul_left
        (h p hp (dvd_mul_of_dvd_right hd a))
  · rintro ⟨ha,hb⟩ p hp hd
    rcases hp.dvd_mul.mp hd with pa|pb
    · exact dvd_mul_of_dvd_left (ha p hp pa) _
    · exact dvd_mul_of_dvd_right (hb p hp pb) _

private theorem squarefull_geom : Summable (fun k : ℕ => ((k:ℝ)+3)^2 * (1/2:ℝ)^k) := by
  have p (d : ℕ) := summable_pow_mul_geometric_of_norm_lt_one d
    (r:=(1/2:ℝ)) (by norm_num)
  apply (((p 2).add ((p 1).mul_left 6)).add ((p 0).mul_left 9)).congr
  intro k
  simp only [pow_zero,pow_one,one_mul]
  ring_nf

/-- The Euler product for the squarefull part converges at exponent one because
its first nonconstant term at a prime has degree two. The smooth-number comparison
in the last paragraph follows the argument of OMA PR 12593, EulerMass975.product_mass. -/
theorem squarefull_harmonic_bound (ρ : ℕ → ℝ) (rn : ∀ n, 0 ≤ ρ n) (unit : ρ 1=1)
    (mult : ∀ {a b : ℕ}, a.Coprime b → ρ (a*b)=ρ a*ρ b)
    (B : ℝ) (Bn : 0≤ B) (bound : ∀ p : ℕ, p.Prime → ∀ e : ℕ, ρ (p^e) ≤ B) :
    ∃ C : ℝ, 0≤ C ∧ ∀ N : ℕ,
      (∑ s ∈ (Icc 1 N).filter Squarefull, ρ s*(s.divisors.card:ℝ)^(3/2:ℝ)/s) ≤ C := by
  classical
  let g (n : ℕ) : ℝ := if Squarefull n then ρ n * (n.divisors.card:ℝ)^2 / n else 0
  have gn (n : ℕ) : 0 ≤ g n := by
    dsimp [g]
    split_ifs <;> positivity [rn n]
  have one : Squarefull 1 := fun p hp h => False.elim (hp.not_dvd_one h)
  have g1 : g 1=1 := by simp [g,one,unit]
  have gm {a b : ℕ} (cop : a.Coprime b) : g (a*b)=g a*g b := by
    by_cases ha : Squarefull a <;> by_cases hb : Squarefull b <;>
      simp [g,squarefull_mul cop,ha,hb,mult cop,cop.card_divisors_mul]
    ring_nf
  have gp {p : ℕ} (hp : p.Prime) : g p = 0 := by
    have h : ¬Squarefull p := by
      intro h
      have hh := h p hp (dvd_refl p)
      have ll := Nat.le_of_dvd hp.pos hh
      nlinarith [hp.two_le]
    simp [g,h]
  let H (k : ℕ) : ℝ := ((k:ℝ)+3)^2 * (1/2:ℝ)^k
  let w (p : ℕ) : ℝ := (B * ∑' k, H k) / (p:ℝ)^2
  have Hn (k : ℕ) : 0≤ H k := by dsimp [H]; positivity
  have wn (p : ℕ) : 0≤ w p := div_nonneg (mul_nonneg Bn (tsum_nonneg Hn)) (sq_nonneg _)
  have ws : Summable w := (Real.summable_nat_pow_inv.mpr (by decide : 1<2)).mul_left _ |>.congr
    (fun p => by dsimp [w]; rw [div_eq_mul_inv])
  have localTail {p : ℕ} (hp : p.Prime) (k : ℕ) :
      g (p^(k+2)) ≤ B / (p:ℝ)^2 * H k := by
    have pp : (2:ℝ)≤ p := by exact_mod_cast hp.two_le
    have pin : 0 < (p:ℝ) := by linarith
    have coeff : ρ (p^(k+2))≤ B := bound p hp _
    have card : (p^(k+2)).divisors.card = k+3 := by simp [Nat.divisors_prime_pow hp]
    have dec : (p:ℝ)⁻¹ ≤ 1/2 := by rw [←one_div]; exact one_div_le_one_div_of_le (by norm_num) pp
    simp only [g]
    split_ifs
    · rw [card,Nat.cast_add,Nat.cast_ofNat,Nat.cast_pow,pow_add]
      calc
        _ = ρ (p^(k+2)) / (p:ℝ)^2 * (((k:ℝ)+3)^2 * ((p:ℝ)⁻¹)^k) := by rw [inv_pow]; field_simp; ring_nf
        _ ≤ _ := mul_le_mul (div_le_div_of_nonneg_right coeff (sq_nonneg _))
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (inv_nonneg.mpr pin.le) dec k) (sq_nonneg _))
          (by positivity) (by positivity)
    · dsimp [H]; positivity
  have loc2 {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => g (p^(k+2))) :=
    (squarefull_geom.mul_left (B/(p:ℝ)^2)).of_nonneg_of_le (fun _ => gn _) (localTail hp)
  have loc {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ => g (p^k)) :=
    (summable_nat_add_iff 2).mp (loc2 hp)
  have localUpper {p : ℕ} (hp : p.Prime) : (∑' k : ℕ, g (p^k)) ≤ exp (w p) := by
    have sub := (loc2 hp).tsum_le_tsum (localTail hp) (squarefull_geom.mul_left (B/(p:ℝ)^2))
    change _ ≤ ∑' k, B / (p:ℝ)^2 * H k at sub
    rw [tsum_mul_left] at sub
    have tail : (∑' k : ℕ, g (p^(k+2))) ≤ w p := sub.trans_eq (by dsimp [w]; ring_nf)
    have h1 : Summable (fun k : ℕ => g (p^(k+1))) := (summable_nat_add_iff 1).mpr (loc hp)
    rw [(loc hp).tsum_eq_zero_add,h1.tsum_eq_zero_add,pow_zero,g1]
    simp only [zero_add,pow_one,gp hp]
    linarith [Real.add_one_le_exp (w p)]
  refine ⟨exp (∑' p, w p),(exp_pos _).le,?_⟩
  intro N
  let S := (Icc 1 N).filter Squarefull
  have leG : (∑ s ∈ S, ρ s * (s.divisors.card:ℝ)^(3/2:ℝ)/s) ≤ ∑ s ∈ S, g s := by
    apply sum_le_sum
    intro s hs
    obtain ⟨range,sqf⟩ := mem_filter.mp hs
    have pos := (mem_Icc.mp range).1
    have dn : (1:ℝ) ≤ s.divisors.card := by
      exact_mod_cast (card_pos.mpr ⟨1,Nat.one_mem_divisors.mpr (Nat.ne_of_gt pos)⟩)
    simp only [g,if_pos sqf]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg s)
    apply mul_le_mul_of_nonneg_left _ (rn s)
    simpa only [rpow_natCast] using rpow_le_rpow_of_exponent_le dn (show (3/2:ℝ) ≤ (2:ℕ) by norm_num)
  apply leG.trans
  have prod := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum (f:=g)
    g1 (fun h => gm h) (fun {p} hp => by simpa only [Real.norm_eq_abs, abs_of_nonneg (gn _)] using loc hp) (N+1)
  have mem (s : ℕ) (hs : s∈S) : s ∈ (N+1).smoothNumbers := by
    obtain ⟨l,r⟩ := mem_Icc.mp (mem_filter.mp hs).1
    exact Nat.mem_smoothNumbers_of_lt l (by omega)
  have sm := (hasSum_subtype_iff_indicator (s:=(N+1).smoothNumbers) (f:=g)).mp prod.2
  calc
    _ = ∑ s ∈ S, (N+1).smoothNumbers.indicator g s := sum_congr rfl fun s hs =>
      (Set.indicator_of_mem (mem s hs) _).symm
    _ ≤ _ := sm.summable.sum_le_tsum S (fun i _ => Set.indicator_nonneg (fun i _ => gn i) _)
    _ = _ := sm.tsum_eq
    _ ≤ ∏ p ∈ (N+1).primesBelow, exp (w p) := prod_le_prod (fun _ _ => tsum_nonneg (fun _ => gn _))
      (fun p hp => localUpper (Nat.prime_of_mem_primesBelow hp))
    _ = _ := (exp_sum ..).symm
    _ ≤ _ := exp_le_exp.mpr (ws.sum_le_tsum _ (fun p _ => wn p))

end TenenbaumLayers
end

section
namespace TenenbaumLayers
open Finset Real MeasureTheory
open scoped Classical

/-- A constant depending only on the multiplicative root weight transfers the
positive-order fractional moment from squarefree moduli to all moduli. -/
theorem squarefree_suffices (ρ : ℕ → ℝ) (rn : ∀ n, 0≤ ρ n) (unit : ρ 1=1)
    (mult : ∀ {a b : ℕ}, a.Coprime b → ρ (a*b)=ρ a*ρ b)
    (bounded : ∃ B : ℝ, 0≤ B ∧ ∀ p : ℕ, p.Prime → ∀ e : ℕ, ρ (p^e) ≤ B) :
    ∃ C : ℝ, 0≤ C ∧ ∀ N q : ℕ, 0< q →
      let e := 3/(2*(q:ℝ))
      (∑ n ∈ Icc 1 N, ρ n * (moment n q)^e / n) ≤
        C * ∑ a ∈ (Icc 1 N).filter Squarefree, ρ a * (moment a q)^e / a := by
  obtain ⟨B,Bn,bp⟩ := bounded
  obtain ⟨C,Cn,bd⟩ := squarefull_harmonic_bound ρ rn unit mult B Bn bp
  refine ⟨C,Cn,?_⟩
  intro N q hq
  apply (harmonic_squarefree_transfer N q hq ρ rn mult).trans
  rw [mul_comm C]
  apply mul_le_mul_of_nonneg_left (bd N)
  apply sum_nonneg
  intro a _
  have mn : 0≤ moment a q := integral_nonneg fun t => pow_nonneg (window_bounds _ _).1 _
  exact div_nonneg (mul_nonneg (rn a) (rpow_nonneg mn _)) (Nat.cast_nonneg a)

end TenenbaumLayers
end

section
/- An exponential tilt of a positive Dirichlet series bounds the expected
sum of logarithms of the marked prime divisors. -/

namespace TenenbaumMoments
open Real Finset
open scoped Classical

theorem marked_logs_le {P : Finset ℕ} (primes : ∀ p ∈ P, p.Prime) (n : ℕ) (pos : 0 < n) :
    (∑ p ∈ P, if p ∣ n then log (p:ℝ) else 0) ≤ log n := by
  let T := P.filter (· ∣ n)
  have sub : T ⊆ n.primeFactors := by
    intro p hp
    obtain ⟨pp,dv⟩ := mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨primes p pp,dv,pos.ne'⟩
  have dv := (Finset.prod_dvd_prod_of_subset T n.primeFactors (fun p => p) sub).trans (Nat.prod_primeFactors_dvd n)
  have le := Nat.le_of_dvd pos dv
  have pz : ∀ p ∈ T, 0 < p := fun p hp => (primes p (mem_filter.mp hp).1).pos
  have logprod := Real.log_prod (s := T) (f := fun p : ℕ => (p:ℝ))
    (fun p hp => by exact_mod_cast (pz p hp).ne')
  rw [← sum_filter]
  change (∑ p ∈ T, log (p:ℝ)) ≤ log n
  rw [← logprod]
  apply Real.log_le_log (Finset.prod_pos fun p hp => by exact_mod_cast pz p hp)
  rw [← Nat.cast_prod]
  exact_mod_cast le

/-- Tangent-line version of Jensen for a positive summable sequence.
Only the finite family of divisibility indicators is integrated. -/
theorem prime_tilt {A B : ℕ → ℝ} (P : Finset ℕ) (x : ℕ → ℝ) (h : ℝ)
    (apos : ∀ n, 0 ≤ A n) (bpos : ∀ n, 0 ≤ B n) (anull : A 0 = 0)
    (sa : Summable A) (sb : Summable B) (hh : 0 ≤ h) (primes : ∀ p ∈ P, p.Prime)
    (lower : ∀ p ∈ P, x p*(∑' n, A n) ≤ ∑' n, if p∣n then A n else 0)
    (tilt : ∀ n : ℕ, 0< n → exp (h*log n)*A n ≤ B n) :
    exp (h * ∑ p ∈ P, x p*log p) * (∑' n, A n) ≤ ∑' n, B n := by
  classical
  let m := h * ∑ p ∈ P, x p*log p
  let I := fun p n : ℕ => if p∣n then A n else 0
  let Y := fun n : ℕ => ∑ p ∈ P, log p * I p n
  have si (p : ℕ) : Summable (I p) := sa.of_nonneg_of_le
    (fun n => by dsimp [I]; split <;> simp [apos]) (fun n => by dsimp [I]; split <;> simp [apos])
  have parts (p : ℕ) : Summable (fun n => log p * I p n) := (si p).mul_left _
  have sy : Summable Y := summable_sum fun p _ => parts p
  have means : m*(∑' n, A n) ≤ h*(∑' n, Y n) := by
    have rearr : (∑' n, Y n) = ∑ p ∈ P, log p * (∑' n, I p n) := by
      dsimp only [Y]
      rw [Summable.tsum_finsetSum (fun p _ => parts p)]
      apply sum_congr rfl
      intro p _
      exact (si p).tsum_mul_left _
    rw [rearr]
    dsimp [m]
    rw [mul_assoc, sum_mul]
    apply mul_le_mul_of_nonneg_left _ hh
    refine sum_le_sum fun p hp => ?_
    calc
      _ = log p * (x p*(∑' n, A n)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (lower p hp) (log_nonneg (by exact_mod_cast (primes p hp).one_le))
  have support (n : ℕ) : exp m * ((1-m)*A n+h*Y n) ≤ B n := by
    by_cases z : n=0
    · subst n
      simpa [anull,Y,I] using bpos 0
    let y := ∑ p ∈ P, if p∣n then log (p:ℝ) else 0
    have calcY : Y n = y*A n := by
      dsimp only [Y,y,I]
      rw [sum_mul]
      refine sum_congr rfl fun p _ => ?_
      split <;> simp
    have envelope : exp m*(1-m+h*y) ≤ exp (h*y) := by
      have bound := add_one_le_exp (h*y-m)
      rw [exp_sub] at bound
      have prod := (le_div_iff₀ (exp_pos m)).mp bound
      linarith only [prod]
    rw [calcY,show (1-m)*A n+h*(y*A n)=(1-m+h*y)*A n by ring,← mul_assoc]
    exact (mul_le_mul_of_nonneg_right
      (envelope.trans (exp_le_exp.mpr (mul_le_mul_of_nonneg_left (marked_logs_le primes n (Nat.pos_of_ne_zero z)) hh))) (apos n)).trans (tilt n (Nat.pos_of_ne_zero z))
  have scl := (sa.mul_left (1-m)).add (sy.mul_left h)
  have total := ((scl.mul_left (exp m)).tsum_le_tsum support sb)
  rw [scl.tsum_mul_left, (sa.mul_left (1-m)).tsum_add (sy.mul_left h),
    sa.tsum_mul_left, sy.tsum_mul_left] at total
  calc
    _ ≤ exp m*((1-m)*(∑' n, A n)+h*(∑' n, Y n)) :=
      mul_le_mul_of_nonneg_left (by linarith only [means]) (exp_pos m).le
    _ ≤ _ := total

end TenenbaumMoments
end

section
/- Removing the correction factor 1/(1+x_p) costs a bounded prime sum. -/

namespace TenenbaumMoments
open Real Finset

theorem sum_log_over_square : Summable (fun n : ℕ => log (n:ℝ)/(n:ℝ)^2) := by
  have h := (Real.summable_nat_rpow.mpr (by norm_num : (-3/2 : ℝ) < -1)).mul_left 2
  apply h.of_nonneg_of_le
  · intro n
    by_cases z : n=0
    · simp [z]
    · exact div_nonneg (log_nonneg (by exact_mod_cast (show 1≤ n by omega))) (sq_nonneg _)
  · intro n
    by_cases z : n=0
    · simp [z]
    have pos : (0:ℝ)< n := by exact_mod_cast Nat.pos_of_ne_zero z
    have half := log_le_sub_one_of_pos (rpow_pos_of_pos pos (1/2:ℝ))
    rw [log_rpow pos] at half
    rw [div_le_iff₀ (sq_pos_of_pos pos)]
    have combine : (n:ℝ)^(-3/2:ℝ)*(n:ℝ)^2 = (n:ℝ)^(1/2:ℝ) := by
      rw [← rpow_natCast, ← rpow_add pos]
      norm_num
    nlinarith only [half,combine]

theorem prime_marking_loss (P : Finset ℕ) (primes : ∀ p∈P,p.Prime) (f : ℕ → ℝ)
    (D s : ℝ) (hD : 0 ≤ D) (hs : 0 ≤ s) (hf : ∀ p ∈ P, 0 ≤ f p ∧ f p ≤ D) :
    let x := fun p : ℕ => f p / (p:ℝ)^(1+s)
    (∑ p∈P,x p*log p) ≤ (∑ p∈P,(x p/(1+x p))*log p) +
      D^2 * (∑' n : ℕ, log (n:ℝ)/(n:ℝ)^2) := by
  intro x
  have each (p : ℕ) (pp : p ∈ P) : (x p-x p/(1+x p))*log p ≤ D^2*(log p/(p:ℝ)^2) := by
    have pos : 0 < (p:ℝ) := by exact_mod_cast (primes p pp).pos
    have big : 1 ≤ (p:ℝ) := by exact_mod_cast (primes p pp).one_le
    have low : (p:ℝ) ≤ (p:ℝ)^(1+s) := by
      simpa only [rpow_one] using (rpow_le_rpow_of_exponent_le big (by linarith : 1≤1+s))
    obtain ⟨lo,hi⟩ := hf p pp
    have xp : 0 ≤ x p := by dsimp [x]; positivity
    have xb : x p ≤ D/(p:ℝ) := div_le_div₀ hD hi pos low
    have small : x p-x p/(1+x p) ≤ (x p)^2 := by
      have exactLoss : x p - x p/(1+x p) = (x p)^2/(1+x p) := by field_simp; ring
      rw [exactLoss]
      apply div_le_self (sq_nonneg _)
      linarith
    calc
      _ ≤ (D/(p:ℝ))^2*log p := mul_le_mul_of_nonneg_right
        (small.trans (pow_le_pow_left₀ xp xb 2)) (log_nonneg big)
      _ = _ := by ring
  have finite := sum_le_sum each
  simp only [sub_mul, sum_sub_distrib, ←mul_sum] at finite
  have full := sum_log_over_square.sum_le_tsum P (fun n hn => by
    by_cases z : n=0
    · simp [z]
    · exact div_nonneg (log_nonneg (by exact_mod_cast (show 1≤ n by omega))) (sq_nonneg _))
  exact (sub_le_iff_le_add'.mp (finite.trans (mul_le_mul_of_nonneg_left full (sq_nonneg D))))

end TenenbaumMoments
end

section
/- A simple pole controls the ratio at two nearby real arguments. -/

namespace TenenbaumMoments
open Real Filter Set
open scoped Topology

theorem residue_ratio {F : ℝ → ℝ} {R : ℝ} (rp : 0< R)
    (pole : Tendsto (fun s : ℝ => s * F s) (𝓝[>] 0) (𝓝 R)) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < F s ∧ F ((9/10:ℝ)*s) / F s ≤ 28/25 := by
  let scale : ℝ := 9/10
  have lp : 0 < scale := by norm_num [scale]
  have ds : Tendsto (fun s : ℝ => scale*s) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · apply tendsto_nhdsWithin_of_tendsto_nhds
      simpa using (tendsto_const_nhds (x:=scale)).mul (tendsto_id (x:=𝓝 (0:ℝ)))
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact mul_pos lp hs
  have before := pole.comp ds
  have ratio := (before.div pole rp.ne').div_const scale
  have bound := ratio.eventually_lt_const (show (R/R)/scale < 28/25 by rw [div_self rp.ne']; norm_num [scale])
  have positive := pole.eventually_const_lt rp
  filter_upwards [bound,positive,self_mem_nhdsWithin] with s small pos hs
  change 0< s at hs
  change 0< s*F s at pos
  have fs := (mul_pos_iff_of_pos_left hs).mp pos
  change ((scale*s)*F (scale*s))/(s*F s)/scale < 28/25 at small
  refine ⟨fs, ?_⟩
  change F (scale*s) / F s ≤ 28/25
  calc
    _ = ((scale*s)*F (scale*s))/(s*F s)/scale := by field_simp
    _ ≤ _ := small.le

end TenenbaumMoments
end

section
namespace TenenbaumMoments

/-- Multiplication by p sends the mass away from p into the mass divisible by p. -/
theorem divisible_mass_lower (A : ℕ → ℝ) (nonneg : ∀ n, 0 ≤ A n) (summable : Summable A)
    (p : ℕ) (prime : p.Prime) (x : ℝ) (xn : 0 ≤ x)
    (step : ∀ m : ℕ, ¬ p ∣ m → A (p*m) = x * A m) :
    x/(1+x) * (∑' m, A m) ≤ ∑' m, if p ∣ m then A m else 0 := by
  let hits (m : ℕ) := if p ∣ m then A m else 0
  let rest (m : ℕ) := if p ∣ m then 0 else A m
  have hn (m : ℕ) : 0 ≤ hits m := by unfold hits; split <;> simp [nonneg]
  have rn (m : ℕ) : 0 ≤ rest m := by unfold rest; split <;> simp [nonneg]
  have hs : Summable hits := Summable.of_nonneg_of_le hn (fun m => by unfold hits; split <;> simp [nonneg]) summable
  have rs : Summable rest := Summable.of_nonneg_of_le rn (fun m => by unfold rest; split <;> simp [nonneg]) summable
  have inj : Function.Injective (fun m : ℕ => p*m) := fun _ _ h => Nat.eq_of_mul_eq_mul_left prime.pos h
  have comp := tsum_comp_le_tsum_of_inj hs hn inj
  have pointwise (m : ℕ) : x*rest m ≤ hits (p*m) := by
    rw [show hits (p*m)=A (p*m) from if_pos (dvd_mul_right p m)]
    dsimp [rest]
    split
    · simpa using nonneg (p*m)
    · rename_i missed
      rw [step m missed]
  have all : (∑'m,A m) = (∑'m,hits m) + ∑'m,rest m := by
    rw [← hs.tsum_add rs]
    apply tsum_congr
    intro m
    by_cases h : p∣m <;> simp [hits,rest,h]
  have weight : x*(∑'m,rest m) ≤ ∑'m,hits m := by
    rw [← rs.tsum_mul_left x]
    exact ((rs.mul_left x).tsum_le_tsum pointwise (hs.comp_injective inj)).trans comp
  rw [all,div_mul_eq_mul_div]
  apply (div_le_iff₀ (by linarith : 0 < 1+x)).mpr
  nlinarith only [weight]

end TenenbaumMoments
end

section
/- An arithmetic function with a positive mean and bounded values at primes
has the sharp leading constant needed in the Hall–Tenenbaum differential inequality. -/

namespace TenenbaumMoments
open Real Filter Finset Set
open scoped Topology Classical

theorem sharp_prime_sum (f : ℕ → ℝ) (f0 : f 0=0) (pos : ∀ n, 0 ≤ f n)
    (mult : ∀ m n : ℕ, m.Coprime n → f (m*n) = f m * f n)
    (D R : ℝ) (dp : 0 ≤ D) (rp : 0 < R) (maxp : ∀ p : ℕ, p.Prime → f p ≤ D)
    (summable : ∀ s : ℝ, 0 < s → Summable (fun n : ℕ => f n / (n:ℝ)^(1+s)))
    (pole : Tendsto (fun s : ℝ => s * ∑' n : ℕ, f n / (n:ℝ)^(1+s)) (𝓝[>] 0) (𝓝 R)) :
    ∀ᶠ s : ℝ in 𝓝[>] 0, ∀ P : Finset ℕ, (∀ p∈P,p.Prime) →
      (∑ p∈P, (f p / (p:ℝ)^(1+s))*log p) ≤ (5/4:ℝ)/s := by
  let K := D^2 * (∑' n : ℕ, log (n:ℝ)/(n:ℝ)^2)
  have err : ∀ᶠ s : ℝ in 𝓝[>] 0, s*K < 1/20 := by
    have t : Tendsto (fun s : ℝ => s*K) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_nhdsWithin_of_tendsto_nhds (tendsto_id (x:=𝓝 (0:ℝ)))).mul_const K
    exact t.eventually_lt_const (by norm_num)
  filter_upwards [err, residue_ratio rp pole, self_mem_nhdsWithin] with s sk ratios hs
  change 0 < s at hs
  intro P primes
  let x := fun n : ℕ => f n / (n:ℝ)^(1+s)
  let y := fun n : ℕ => f n / (n:ℝ)^(1+(9/10:ℝ)*s)
  have xn (n : ℕ) : 0 ≤ x n := div_nonneg (pos n) (rpow_nonneg (Nat.cast_nonneg n) _)
  have yn (n : ℕ) : 0 ≤ y n := div_nonneg (pos n) (rpow_nonneg (Nat.cast_nonneg n) _)
  have split (p : ℕ) (hp : p ∈ P) :
      (x p / (1+x p))*(∑' n, x n) ≤ ∑' n, if p∣n then x n else 0 := by
    apply divisible_mass_lower x xn (summable _ hs) p (primes p hp) (x p) (xn p)
    intro m fresh
    dsimp [x]
    rw [mult _ _ ((primes p hp).coprime_iff_not_dvd.mpr fresh), Nat.cast_mul,
      mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  have tilt (n : ℕ) (nz : 0< n) : exp ((s/10)*log n)*x n ≤ y n := by
    have npos : 0<(n:ℝ) := by exact_mod_cast nz
    rw [mul_comm (s/10), ←rpow_def_of_pos npos]
    have eq : (1:ℝ)+s = (s/10) + (1+(9/10)*s) := by ring
    dsimp only [x,y]
    rw [eq,rpow_add npos]
    have hpow := rpow_pos_of_pos npos (s/10)
    exact le_of_eq (by field_simp)
  have tilted := prime_tilt P (fun p => x p/(1+x p)) (s/10) xn yn (by simp [x,f0])
    (summable _ hs) (summable _ (by positivity)) (by positivity) primes split tilt
  have first : 0 < ∑' n, x n := ratios.1
  have second : (∑' n, y n) / (∑' n,x n) ≤ 28/25 := ratios.2
  have logbound := add_one_le_exp ((s/10) * ∑ p ∈ P, x p/(1+x p)*log p)
  have clip := ((le_div_iff₀ first).mpr tilted).trans second
  have loss : (∑ p∈P,x p*log p) ≤ (∑ p∈P,(x p/(1+x p))*log p) + K :=
    prime_marking_loss P primes f D s dp hs.le (fun p hp => ⟨pos p, maxp p (primes p hp)⟩)
  change (∑ p∈P,x p*log p) ≤ (5/4:ℝ)/s
  apply (le_div_iff₀ hs).mpr
  nlinarith only [mul_le_mul_of_nonneg_right loss hs.le, logbound.trans clip, sk]

end TenenbaumMoments
end

section
namespace TenenbaumMoments
open Finset Filter Topology Asymptotics

/-- The real Dirichlet series of a nonnegative sequence of finite mean has that mean as its residue. -/
theorem mean_residue (f : ℕ → ℝ) (f0 : f 0=0) (fn : ∀ n,0≤ f n) (R : ℝ)
    (mean : Tendsto (fun n : ℕ => (∑ j ∈ Icc 1 n, f j)/(n:ℝ)) atTop (𝓝 R)) :
    (∀ s : ℝ, 0 < s → Summable (fun n : ℕ => f n/(n:ℝ)^(1+s))) ∧
      Tendsto (fun s : ℝ => s * ∑' n : ℕ, f n/(n:ℝ)^(1+s)) (𝓝[>] 0) (𝓝 R) := by
  have entry (n : ℕ) (s : ℝ) : LSeries.term (fun q => (f q : ℂ)) (s:ℂ) n = ((f n / (n:ℝ)^s : ℝ):ℂ) := by
    by_cases z : n=0
    · simp [z,f0]
    · rw [LSeries.term_of_ne_zero z,Complex.ofReal_div,Complex.ofReal_cpow (Nat.cast_nonneg n)]
      rfl
  have convert_series (s : ℝ) : LSeries (fun n => (f n : ℂ)) (s:ℂ) = ((∑' n : ℕ,f n/(n:ℝ)^s : ℝ):ℂ) := by
    rw [Complex.ofReal_tsum]
    exact tsum_congr (entry · s)
  constructor
  · intro s sp
    have big : (fun n : ℕ => ∑ j∈Icc 1 n,f j) =O[atTop] fun n : ℕ => (n:ℝ)^(1:ℝ) :=
      isBigO_atTop_natCast_rpow_of_tendsto_div_rpow (by simpa using mean)
    have hs : LSeriesSummable (fun n => (f n : ℂ)) ((1+s:ℝ):ℂ) :=
      LSeriesSummable_of_sum_norm_bigO_and_nonneg big fn zero_le_one (by change 1<1+s; linarith)
    apply Complex.summable_ofReal.mp
    exact hs.congr (entry · (1+s))
  · have slide : Tendsto (fun s : ℝ => 1+s) (𝓝[>] 0) (𝓝[>] 1) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · have c : Continuous (fun s : ℝ => 1+s) := continuous_const.add continuous_id
        simpa using ((c.continuousAt (x:=0)).continuousWithinAt (s:=Set.Ioi 0)).tendsto
      · filter_upwards [self_mem_nhdsWithin] with s hs
        change 1<1+s
        change 0< s at hs
        linarith
    have result := (LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_and_nonneg f mean fn).comp slide
    have real := Complex.continuous_re.continuousAt.tendsto.comp result
    convert! real using 1
    ext s
    simp only [Function.comp_apply,convert_series,Complex.mul_re,Complex.sub_re,Complex.ofReal_re,
      Complex.one_re,Complex.ofReal_im,Complex.one_im,Complex.sub_im,sub_zero,zero_mul,add_sub_cancel_left]

end TenenbaumMoments
end

section
/- The residue of the root-counting series supplies both estimates in the
finite Hall–Tenenbaum moment inequality on a common real interval. -/

namespace TenenbaumMoments
open Real Filter Finset Set
open scoped Topology

theorem mean_supplies (f : ℕ → ℝ) (f0 : f 0 = 0) (fn : ∀ n, 0 ≤ f n)
    (mult : ∀ m n : ℕ, m.Coprime n → f (m*n) = f m*f n)
    (D R : ℝ) (dp : 0 ≤ D) (rp : 0 < R) (cap : ∀ p : ℕ, p.Prime → f p ≤ D)
    (mean : Tendsto (fun n : ℕ => (∑ j ∈ Icc 1 n, f j)/(n:ℝ)) atTop (𝓝 R)) :
    ∃ s₀ > (0:ℝ), ∃ C ≥ (0:ℝ),
      (∀ s ∈ Ioc (0:ℝ) s₀, ∀ N : ℕ, (∑ n ∈ Icc 1 N, f n/(n:ℝ)^(1+s)) ≤ C/s) ∧
      (∀ s ∈ Ioc (0:ℝ) s₀, ∀ P : Finset ℕ, (∀ p ∈ P,p.Prime) →
        (∑ p ∈ P,log (p:ℝ)*(f p/(p:ℝ)^(1+s))) ≤ (5/4:ℝ)/s) := by
  obtain ⟨summable,pole⟩ := mean_residue f f0 fn R mean
  have sharp := sharp_prime_sum f f0 fn mult D R dp rp cap summable pole
  have bounded := pole.eventually_lt_const (show R < R+1 by linarith)
  obtain ⟨s₀,sp,strip⟩ := mem_nhdsGT_iff_exists_Ioc_subset.mp (bounded.and sharp)
  refine ⟨s₀,sp,R+1,by linarith,?_,?_⟩
  · intro s hs N
    have h := (strip hs).1
    apply ((summable s hs.1).sum_le_tsum (Icc 1 N) (fun n _ => div_nonneg (fn n) (rpow_nonneg (Nat.cast_nonneg n) _))).trans
    apply (le_div_iff₀ hs.1).mpr
    simpa only [mul_comm] using h.le
  · intro s hs P hp
    simpa only [mul_comm] using (strip hs).2 P hp

end TenenbaumMoments
end

section
namespace TenenbaumLayers
open Finset Real Filter
open scoped Topology

/-- The fixed-order Hall–Tenenbaum weighted harmonic moment follows from a
positive mean of the multiplicative coefficients and bounded prime powers. -/
theorem weighted_harmonic_of_mean (ρ : ℕ → ℝ) (zero : ρ 0=0) (unit : ρ 1=1)
    (rn : ∀ n,0≤ ρ n) (mult : ∀ a b, Nat.Coprime a b → ρ (a*b)=ρ a*ρ b)
    (D R : ℝ) (dn : 0≤ D) (rp : 0< R)
    (cap : ∀ p : ℕ,p.Prime → ∀ e : ℕ,ρ (p^e) ≤ D)
    (mean : Tendsto (fun n : ℕ => (∑ b ∈ Icc 1 n,ρ b)/(n:ℝ)) atTop (𝓝 R)) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ᶠ N : ℕ in atTop,
      (∑ b ∈ Icc 1 N,ρ b*(moment b (k+1))^(3/(2*((k:ℝ)+1)):ℝ)/b) ≤ (log N)^(2*sqrt 2-3/2+ε) := by
  have prime (p : ℕ) (hp : p.Prime) : ρ p ≤ D := by simpa only [pow_one] using cap p hp 1
  exact harmonic_terminal ρ rn unit mult D dn prime (TenenbaumMoments.mean_supplies ρ zero rn mult D R dn rp prime mean)
    (squarefree_suffices ρ rn unit (fun h => mult _ _ h) ⟨D,dn,cap⟩)

end TenenbaumLayers
end

theorem OMA.solution : OMA.R_Erdos976_erdos_976_variants_tenenbaum_R1_H2_R1.H2 := by
  intro f hf hd
  obtain ⟨R,rp,mean⟩ := OMA.Band976.positive_mean f hf (by omega)
  obtain ⟨D,dn,bounded⟩ := OMA.CoeffBound975.roots_uniform f hf (by omega)
  exact TenenbaumLayers.weighted_harmonic_of_mean (OMA.RootsEuler975.rho f)
    (by simp) (OMA.RootsEuler975.rho_one f) (fun n => Nat.cast_nonneg _)
    (fun a b cop => (OMA.RootsEuler975.multiplicative f).map_mul_of_coprime cop)
    D R dn rp (fun p hp e => (le_abs_self _).trans (bounded p hp e)) mean
