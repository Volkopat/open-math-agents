import FormalConjectures.ErdosProblems.«975»
import Mathlib

/-! Hooley's quadratic divisor asymptotic with an explicit constant.
The Dedekind zeta residue times an absolutely convergent Euler correction gives the
positive root-count mean. Comparing the two polynomial threshold counts with the
harmonic sum preserves that constant for degrees at least two and halves it for degree one.
The complementary-factor identities, periodic counts and real-endpoint transfer in
namespace OMA.R_Erdos975_erdos_975_R1 below are from @desenyon's accepted reduction
Erdos975.erdos_975.R1 (open-math-agents pull request 3938). -/

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

/-- A summatory mean gives the same logarithmic mean, even for signed coefficients. -/
theorem logarithmic (a : ℕ → ℝ) (R : ℝ)
    (ha : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, a n)/(N:ℝ)) atTop (𝓝 R)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, a n/(n:ℝ))/Real.log N) atTop (𝓝 R) := by
  let A (N : ℕ) := ∑ n ∈ Icc 1 N, a n
  let u (n : ℕ) := A n/(n:ℝ)
  let w (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  let H (N : ℕ) := ∑ n ∈ Finset.range N, w n
  have hu : Tendsto u atTop (𝓝 R) := ha
  have hA (N : ℕ) : A (N+1)=A N+a (N+1) := by
    dsimp [A]; rw [Finset.sum_Icc_succ_top (by omega)]
  have abel (N : ℕ) :
      (∑ n ∈ Icc 1 N, a n/(n:ℝ)) = u N + ∑ n ∈ Finset.range N, u n*w n := by
    induction N with
    | zero => simp [u,A]
    | succ N ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
      obtain rfl | hN := Nat.eq_zero_or_pos N
      · simp [u,A,w]
      · have hN' : (0:ℝ)<N := by exact_mod_cast hN
        dsimp only [u,w]
        rw [hA, Nat.cast_add_one]
        field_simp
        ring
  have hH (n : ℕ) : H n = (harmonic n : ℝ) := by
    simp [H,w,harmonic,one_div]
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ => H n-Real.log n) atTop (𝓝 Real.eulerMascheroniConstant) := by
    simpa only [hH] using Real.tendsto_harmonic_sub_log
  have hHtop : Tendsto H atTop atTop := by
    have e := Filter.Tendsto.atTop_add hlog hd
    simpa only [add_sub_cancel] using e
  have hRatio : Tendsto (fun n : ℕ => H n/Real.log n) atTop (𝓝 1) := by
    have e := (hd.div_atTop hlog).add (tendsto_const_nhds (x:=(1:ℝ)) (f:=atTop (α:=ℕ)))
    rw [zero_add] at e
    refine e.congr' ?_
    filter_upwards [hlog.eventually_gt_atTop 0] with n hn
    field_simp; ring
  have hzero : Tendsto (fun n => u n-R) atTop (𝓝 0) := tendsto_sub_nhds_zero_iff.mpr hu
  have ho : (fun n => (u n-R)*w n) =o[atTop] w := by
    have h := ((Asymptotics.isLittleO_one_iff ℝ).mpr hzero).mul_isBigO (Asymptotics.isBigO_refl w _)
    simpa using h
  have hwe : (0:ℕ→ℝ) ≤ w := by intro n; dsimp [w]; positivity
  have hsmall := (ho.sum_range hwe hHtop).tendsto_div_nhds_zero
  have he : Tendsto (fun n : ℕ => (∑ i ∈ Finset.range n, (u i-R)*w i)/Real.log n) atTop (𝓝 0) := by
    have e := hsmall.mul hRatio
    rw [zero_mul] at e
    refine e.congr' ?_
    filter_upwards [hHtop.eventually_gt_atTop 0] with n hn
    change (_/H n)*(H n/_) = _
    field_simp [hn.ne']
  have head := hu.div_atTop hlog
  have fin := (head.add he).add (hRatio.const_mul R)
  rw [zero_add,zero_add,mul_one] at fin
  refine fin.congr (fun n => ?_)
  rw [abel]
  dsimp [H]
  simp_rw [sub_mul,Finset.sum_sub_distrib,← Finset.mul_sum]
  ring

/-- The two mean-value transfers in the arithmetic-function notation used for Euler factors. -/
theorem transfer (a h : ArithmeticFunction ℝ) (R : ℝ)
    (ha : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, a n)/(N:ℝ)) atTop (𝓝 R))
    (hh : Summable (fun d : ℕ => |h d|/(d:ℝ))) :
    let L := R * ∑' d : ℕ, h d/(d:ℝ)
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, (a*h) n)/(N:ℝ)) atTop (𝓝 L) ∧
      Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, (a*h) n/(n:ℝ))/Real.log N) atTop (𝓝 L) := by
  have H : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, (a*h) n)/(N:ℝ)) atTop
      (𝓝 (R*∑' d : ℕ, h d/(d:ℝ))) := by
    rw [mul_comm a h]
    exact mean a h R ha hh
  exact ⟨H,logarithmic (fun n => (a*h) n) _ H⟩

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

section
/- Archimedean estimates for the two small-divisor threshold counts. -/

namespace OMA.Height975
open Polynomial Finset Filter Real
open scoped Topology

/-- Eventual positivity makes at least half the leading monomial a lower
bound, even for a polynomial with some negative lower coefficients. -/
theorem lower_tail (f : ℤ[X]) (hd : 0 < f.natDegree)
    (hp : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    ∃ T : ℕ, ∀ n : ℕ, T ≤ n → (n:ℤ)^f.natDegree ≤ 2 * f.eval (n:ℤ) := by
  let P := f.map (Int.castRingHom ℝ)
  have deg : P.natDegree = f.natDegree :=
    natDegree_map_eq_of_injective (Int.cast_injective (α:=ℝ)) f
  have lc : P.leadingCoeff = (f.leadingCoeff : ℝ) :=
    leadingCoeff_map_of_injective (Int.cast_injective (α:=ℝ)) f
  have hfn : f ≠ 0 := by intro e; simp [e] at hd
  have habs : 1 ≤ |f.leadingCoeff| := by
    have := abs_pos.mpr (leadingCoeff_ne_zero.mpr hfn)
    omega
  have ha : 1 ≤ |P.leadingCoeff| := by rw [lc]; exact_mod_cast habs
  have ht := P.isEquivalent_atTop_lead.isLittleO.bound (show 0 < (1/2 : ℝ) by norm_num)
  have ht' := (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually ht
  have hp' := (tendsto_natCast_atTop_atTop (R:=ℤ)).eventually hp
  apply eventually_atTop.mp
  filter_upwards [ht',hp'] with n hn hnpos
  have ev : P.eval (n:ℝ) = (↑(f.eval (n:ℤ)) : ℝ) := by simp [P, Polynomial.eval_map]
  change ‖P.eval (n:ℝ) - P.leadingCoeff*(n:ℝ)^P.natDegree‖ ≤ _ at hn
  have tri := abs_sub_abs_le_abs_sub (P.leadingCoeff*(n:ℝ)^P.natDegree) (P.eval (n:ℝ))
  rw [abs_sub_comm] at tri
  have hn0 : 0 ≤ P.eval (n:ℝ) := by
    rw [ev]
    exact_mod_cast (show (0:ℤ) ≤ f.eval (n:ℤ) by omega)
  have hb : (n:ℝ)^f.natDegree ≤ |P.leadingCoeff*(n:ℝ)^P.natDegree| := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n:ℝ)^P.natDegree), deg]
    exact le_mul_of_one_le_left (by positivity) ha
  simp only [Real.norm_eq_abs, abs_of_nonneg hn0] at hn tri
  have hh : (n:ℝ)^f.natDegree ≤ 2 * P.eval (n:ℝ) := by linarith
  rw [ev] at hh
  exact_mod_cast hh

def length (f : ℤ[X]) (N i q : ℕ) :=
  ((range (N+1)).filter (fun n : ℕ => (q:ℤ)*q+i ≤ f.eval (n:ℤ))).card

/-- Only the initial interval preceding a uniform threshold can be missed. -/
theorem length_misses (f : ℤ[X]) (N i q B : ℕ)
    (h : ∀ n : ℕ, B ≤ n → (q:ℤ)*q+i ≤ f.eval (n:ℤ)) :
    N+1 ≤ length f N i q + B := by
  let good := fun n : ℕ => (q:ℤ)*q+i ≤ f.eval (n:ℤ)
  have hbad : ((range (N+1)).filter (fun n => ¬good n)).card ≤ B := by
    rw [← card_range B]
    apply card_le_card
    intro n hn
    apply mem_range.mpr
    exact lt_of_not_ge (fun hBn => (mem_filter.mp hn).2 (h n hBn))
  have hall := card_filter_add_card_filter_not (s:=range (N+1)) good
  simp only [card_range] at hall
  change N+1 ≤ ((range (N+1)).filter good).card+B
  omega

theorem degree_ge_two (f : ℤ[X]) (hd : 2 ≤ f.natDegree)
    (hp : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    ∃ A : ℕ, ∀ N i q : ℕ, i ≤ 1 → 0 < q →
      N + 1 ≤ length f N i q + A*q := by
  obtain ⟨T,hT⟩ := lower_tail f (by omega) hp
  refine ⟨T+3, ?_⟩
  intro N i q hi hq
  apply length_misses
  intro n hn
  have h1 : 1 ≤ q := hq
  have htq : T ≤ T*q := le_mul_of_one_le_right (Nat.zero_le _) h1
  have hs : n ≥ 2*q+1 := by rw [Nat.add_mul] at hn; omega
  have hnt : T ≤ n := by rw [Nat.add_mul] at hn; omega
  have h2 := hT n hnt
  have hpow : (n:ℤ)^2 ≤ (n:ℤ)^f.natDegree := by
    apply pow_le_pow_right₀ _ hd
    exact_mod_cast (show 1 ≤ n by omega)
  have hn' : 2*(q:ℤ)+1 ≤ n := by exact_mod_cast hs
  have hi' : (i:ℤ) ≤ 1 := by exact_mod_cast hi
  have hq' : (0:ℤ) < q := by exact_mod_cast hq
  nlinarith [sq_nonneg ((n:ℤ) - (2*q+1)), mul_self_le_mul_self (by positivity : (0:ℤ) ≤ 2*q+1) hn']

theorem linear_lower (f : ℤ[X]) (hd : f.natDegree = 1)
    (hp : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    ∃ A : ℕ, ∀ N i q : ℕ, i ≤ 1 → 0 < q →
      N + 1 ≤ length f N i q + A*q*q := by
  obtain ⟨T,hT⟩ := lower_tail f (by omega) hp
  refine ⟨T+4, ?_⟩
  intro N i q hi hq
  apply length_misses
  intro n hn
  have h1 : 1 ≤ q := hq
  have hqq : 1 ≤ q*q := Nat.mul_pos hq hq
  have ht : T ≤ T*(q*q) := le_mul_of_one_le_right (Nat.zero_le _) hqq
  rw [Nat.mul_assoc, Nat.add_mul] at hn
  have h := hT n (by omega)
  simp only [hd, pow_one] at h
  have hbig : 2*(q*q)+2 ≤ n := by omega
  have hbig' : 2*((q:ℤ)*q)+2 ≤ n := by exact_mod_cast hbig
  have hi' : (i:ℤ) ≤ 1 := by exact_mod_cast hi
  omega

/-- A linear polynomial never reaches a threshold q² for q larger than a
constant multiple of the square root of the endpoint. -/
theorem linear_support (f : ℤ[X]) (hd : f.natDegree = 1) :
    ∃ L : ℕ, ∀ N i q : ℕ, 0 < N → L*N.sqrt < q → length f N i q = 0 := by
  let M := (f.coeff 0).natAbs + (f.coeff 1).natAbs + 1
  refine ⟨2*M, ?_⟩
  intro N i q hN hq
  apply card_eq_zero.mpr
  apply eq_empty_iff_forall_notMem.mpr
  intro n hn
  obtain ⟨hnN,hval⟩ := mem_filter.mp hn
  have hnle : n ≤ N := by simpa [Nat.lt_succ_iff] using mem_range.mp hnN
  have ev := f.eval_eq_sum_range' (n:=2) (by omega) (n:ℤ)
  simp only [sum_range_succ,sum_range_zero,zero_add,pow_zero,pow_one,mul_one] at ev
  have hcoeff (j : ℕ) : f.coeff j ≤ ((f.coeff j).natAbs:ℤ) := by
    simpa using le_abs_self (f.coeff j)
  have hval' : f.eval (n:ℤ) ≤ (M:ℤ)*N := by
    rw [ev]
    calc
      _ ≤ ((f.coeff 0).natAbs:ℤ)*N + ((f.coeff 1).natAbs:ℤ)*N := by
        apply add_le_add
        · exact (hcoeff 0).trans (le_mul_of_one_le_right (by positivity) (by exact_mod_cast hN))
        · gcongr
          · exact hcoeff 1
      _ ≤ _ := by dsimp [M]; push_cast; nlinarith
  have hb : q*q ≤ M*N := by
    exact_mod_cast (show (q:ℤ)*q ≤ (M:ℤ)*N by omega)
  have hs : 1 ≤ N.sqrt := Nat.sqrt_pos.mpr hN
  have hsq := Nat.lt_succ_sqrt N
  have hN4 : N ≤ (2*N.sqrt)*(2*N.sqrt) := by
    have hm := Nat.mul_le_mul (by omega : N.sqrt+1 ≤ 2*N.sqrt) (by omega : N.sqrt+1 ≤ 2*N.sqrt)
    nlinarith
  have hM : 1 ≤ M := by dsimp [M]; omega
  have hM2 : M ≤ M*M := le_mul_of_one_le_right (Nat.zero_le _) hM
  have hlast : M*N ≤ (2*M*N.sqrt)*(2*M*N.sqrt) := by
    calc M*N ≤ (M*M)*((2*N.sqrt)*(2*N.sqrt)) := Nat.mul_le_mul hM2 hN4
         _ = _ := by ring
  exact (Nat.not_lt_of_ge (hb.trans hlast)) (Nat.mul_lt_mul_of_lt_of_le hq (Nat.le_of_lt hq) (by omega))

end OMA.Height975
end

section
/- Finite comparison of the threshold model with a truncated harmonic mean. -/

namespace OMA.Model975
open Finset

noncomputable def harmonicSum (ρ : ℕ → ℝ) (S : ℕ) := ∑ q ∈ Icc 1 S, ρ q / q

private theorem sum_prefix (N S : ℕ) (g : ℕ → ℝ) :
    (∑ q ∈ Icc 1 N, if q ≤ S then g q else 0) = ∑ q ∈ Icc 1 (min N S), g q := by
  rw [← sum_filter]
  congr 1
  ext q
  simp [and_assoc]

/-- Compare one threshold with N times its harmonic main term. Up to S the
threshold misses at most A*q*M points. Beyond L*S nothing contributes. -/
theorem estimate (ρ : ℕ → ℝ) (nonneg : ∀ q, 0 ≤ ρ q) (C : ℝ)
    (hC : 0 ≤ C) (mean : ∀ X : ℕ, (∑ q ∈ Icc 1 X, ρ q) ≤ C*X)
    (N S M A L : ℕ) (hS : 0 < S) (hM : 0 < M) (hsN : S ≤ N) (hMN : M*S ≤ N)
    (len : ℕ → ℕ) (upper : ∀ q, len q ≤ N+1)
    (miss : ∀ q, 0 < q → q ≤ S → N+1 ≤ len q+A*q*M)
    (supp : ∀ q, q ≤ N → L*S < q → len q = 0) :
    |(∑ q ∈ Icc 1 N, (len q : ℝ)/q*ρ q) - N*harmonicSum ρ S| ≤
      ((A:ℝ)+1+2*L)*C*N := by
  let main (q : ℕ) := if q ≤ S then (N:ℝ)*(ρ q/q) else 0
  let small (q : ℕ) := if q ≤ S then ((A:ℝ)+1)*M*ρ q else 0
  let large (q : ℕ) := if q ≤ L*S then ((N:ℝ)+1)/S*ρ q else 0
  have refsum : (∑ q ∈ Icc 1 N, main q) = N*harmonicSum ρ S := by
    dsimp [main,harmonicSum]
    rw [sum_prefix, min_eq_right hsN, mul_sum]
  have ssum : (∑ q ∈ Icc 1 N, small q) ≤ ((A:ℝ)+1)*C*N := by
    dsimp [small]
    rw [sum_prefix, min_eq_right hsN, ← mul_sum]
    have hn : (M:ℝ)*S ≤ N := by exact_mod_cast hMN
    calc ((A:ℝ)+1)*M*(∑ q ∈ Icc 1 S, ρ q) ≤ ((A:ℝ)+1)*M*(C*S) :=
           mul_le_mul_of_nonneg_left (mean S) (by positivity)
         _ = ((A:ℝ)+1)*C*(M*S) := by ring
         _ ≤ _ := by gcongr
  have lsum : (∑ q ∈ Icc 1 N, large q) ≤ 2*(L:ℝ)*C*N := by
    dsimp [large]
    rw [sum_prefix, ← mul_sum]
    have htail : (∑ q ∈ Icc 1 (min N (L*S)), ρ q) ≤ C*((L:ℝ)*S) := by
      calc _ ≤ C*(min N (L*S):ℕ) := mean _
           _ ≤ _ := by push_cast; gcongr; exact_mod_cast min_le_right N (L*S)
    have hs : (0:ℝ) < S := by exact_mod_cast hS
    have hn : (1:ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
    calc ((N:ℝ)+1)/S*(∑ q ∈ Icc 1 (min N (L*S)), ρ q) ≤ ((N:ℝ)+1)/S*(C*(L*S)) :=
           mul_le_mul_of_nonneg_left htail (by positivity)
         _ = ((N:ℝ)+1)*(L*C) := by field_simp
         _ ≤ (2*N)*(L*C) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
         _ = _ := by ring
  have single (q : ℕ) (hq : q ∈ Icc 1 N) :
      |(len q:ℝ)/q*ρ q-main q| ≤ small q+large q := by
    have hqpos := (mem_Icc.mp hq).1
    have hqr : 0 < (q:ℝ) := by exact_mod_cast (show 0 < q from hqpos)
    have hs : 0 < (S:ℝ) := by exact_mod_cast hS
    have poslarge : 0 ≤ large q := by dsimp [large]; split <;> positivity [nonneg q]
    by_cases h : q ≤ S
    · have hup : (len q:ℝ) ≤ N+1 := by exact_mod_cast upper q
      have hlo : (N:ℝ)+1 ≤ len q+(A:ℝ)*q*M := by exact_mod_cast miss q hqpos h
      have hm : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M from hM)
      have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hqpos
      have hmq : 1 ≤ (M:ℝ)*q := one_le_mul_of_one_le_of_one_le hm hq1
      have diff : |(len q:ℝ)-N| ≤ ((A:ℝ)+1)*M*q := by
        rw [abs_le]
        constructor <;> nlinarith [show 0 ≤ (A:ℝ)*(M*q) by positivity]
      have eqv : (len q:ℝ)/q*ρ q-main q = ((len q:ℝ)-N)/q*ρ q := by
        dsimp [main]; rw [if_pos h]; ring
      rw [eqv, abs_mul,abs_div,abs_of_pos hqr,abs_of_nonneg (nonneg q)]
      apply le_trans _ (le_add_of_nonneg_right poslarge)
      dsimp [small]; rw [if_pos h]
      exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hqr).mpr diff) (nonneg q)
    · dsimp [main,small,large]; rw [if_neg h,if_neg h,sub_zero,zero_add]
      rw [abs_of_nonneg (mul_nonneg (by positivity) (nonneg q))]
      by_cases hsupp : q ≤ L*S
      · rw [if_pos hsupp]
        apply mul_le_mul_of_nonneg_right _ (nonneg q)
        apply div_le_div₀ (by positivity) _ hs _
        · exact_mod_cast upper q
        · exact_mod_cast (le_of_lt (lt_of_not_ge h))
      · simp [hsupp,supp q (mem_Icc.mp hq).2 (lt_of_not_ge hsupp)]
  rw [← refsum, ← sum_sub_distrib]
  calc
    _ ≤ ∑ q ∈ Icc 1 N, |(len q:ℝ)/q*ρ q-main q| := abs_sum_le_sum_abs ..
    _ ≤ ∑ q ∈ Icc 1 N, (small q+large q) := sum_le_sum single
    _ ≤ _ := by rw [sum_add_distrib]; linarith [ssum,lsum]

end OMA.Model975
end

section
/- Transfer the finite threshold comparison to the normalized density model. -/

namespace OMA.Scale975
open Polynomial Finset Filter Real Height975 Model975
open scoped Topology

theorem sqrt_tends : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b*b)] with n hn
  exact Nat.le_sqrt.mpr hn

theorem log_sqrt_ratio : Tendsto (fun n : ℕ => log (n.sqrt:ℝ)/log (n:ℝ)) atTop (𝓝 (1/2)) := by
  have ht : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  apply (tendsto_sub_nhds_zero_iff.mp ?_)
  apply squeeze_zero_norm' (a:=fun n : ℕ => log 2 / log (n:ℝ))
  · filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn
    have hN : (1:ℝ) < n := by exact_mod_cast (show 1 < n by omega)
    have hs : (0:ℝ) < n.sqrt := by exact_mod_cast Nat.sqrt_pos.mpr (show 0 < n by omega)
    have h1 : n.sqrt*n.sqrt ≤ n := Nat.sqrt_le n
    have h2 : n ≤ (2*n.sqrt)*(2*n.sqrt) := by
      have hs1 : 1 ≤ n.sqrt := Nat.sqrt_pos.mpr (by omega)
      have h := Nat.lt_succ_sqrt n
      exact h.le.trans (Nat.mul_le_mul (by omega) (by omega))
    have hln : 0 < log (n:ℝ) := log_pos hN
    have lo : 2*log (n.sqrt:ℝ) ≤ log (n:ℝ) := by
      have h := Real.log_le_log (mul_pos hs hs) (by exact_mod_cast h1 : (n.sqrt:ℝ)*n.sqrt ≤ n)
      rw [Real.log_mul hs.ne' hs.ne'] at h; linarith
    have hi : log (n:ℝ) ≤ 2*(log 2+log (n.sqrt:ℝ)) := by
      have h := Real.log_le_log (by positivity : (0:ℝ) < n)
        (by exact_mod_cast h2 : (n:ℝ) ≤ (2*n.sqrt)*(2*n.sqrt))
      rw [Real.log_mul (by positivity : (2:ℝ)*n.sqrt ≠ 0) (by positivity), Real.log_mul (by norm_num) hs.ne'] at h
      linarith
    rw [Real.norm_eq_abs,abs_le]
    constructor <;> field_simp [hln.ne'] <;> linarith [Real.log_nonneg (by norm_num : (1:ℝ) ≤ 2)]
  · exact ht.const_div_atTop _

def scale (d N : ℕ) := if d = 1 then N.sqrt else N
noncomputable def constant (d : ℕ) (b : ℝ) := if d = 1 then b else 2*b
noncomputable def row (f : ℤ[X]) (ρ : ℕ → ℝ) (N i : ℕ) :=
  ∑ q ∈ Icc 1 N, (length f N i q : ℝ)/q*ρ q

theorem finite (f : ℤ[X]) (hd : f.natDegree ≠ 0) (hp : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n)
    (ρ : ℕ → ℝ) (hn : ∀ q, 0 ≤ ρ q) (C : ℝ) (hC : 0 ≤ C)
    (hav : ∀ N : ℕ, (∑ q ∈ Icc 1 N, ρ q) ≤ C*N) :
    ∃ K : ℝ, ∀ N : ℕ, 0 < N → ∀ i : ℕ, i ≤ 1 →
      |row f ρ N i - N*harmonicSum ρ (scale f.natDegree N)| ≤ K*N := by
  have hup (N i q : ℕ) : length f N i q ≤ N+1 :=
    (card_filter_le ..).trans_eq (card_range _)
  by_cases h : f.natDegree = 1
  · obtain ⟨A,hA⟩ := linear_lower f h hp
    obtain ⟨L,hL⟩ := linear_support f h
    refine ⟨((A:ℝ)+1+2*L)*C, ?_⟩
    intro N hN i hi
    have hs := Nat.sqrt_pos.mpr hN
    have hmiss (q : ℕ) (hq : 0 < q) (hqS : q ≤ N.sqrt) :
        N+1 ≤ length f N i q + A*q*N.sqrt :=
      (hA N i q hi hq).trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ hqS) _)
    simpa only [scale,if_pos h,row] using
      estimate ρ hn C hC hav N N.sqrt N.sqrt A L hs hs (Nat.sqrt_le_self N) (Nat.sqrt_le N)
        (length f N i) (hup N i) hmiss (fun q _ hab => hL N i q hN hab)
  · obtain ⟨A,hA⟩ := degree_ge_two f (by omega) hp
    refine ⟨((A:ℝ)+1+2*(1:ℕ))*C, ?_⟩
    intro N hN i hi
    simpa only [scale,if_neg h,row] using
      estimate ρ hn C hC hav N N 1 A 1 hN (by omega) le_rfl (by simp)
        (length f N i) (hup N i) (fun q hq _ => by simpa using hA N i q hi hq)
        (fun q hq hbad => by simp at hbad; omega)

theorem transfer (f : ℤ[X]) (hd : f.natDegree ≠ 0) (hp : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n)
    (ρ : ℕ → ℝ) (hn : ∀ q, 0 ≤ ρ q) (C : ℝ) (hC : 0 ≤ C)
    (hav : ∀ N : ℕ, (∑ q ∈ Icc 1 N, ρ q) ≤ C*N)
    (b : ℝ) (hb : 0 < b)
    (hlog : Tendsto (fun N : ℕ => harmonicSum ρ N / log (N:ℝ)) atTop (𝓝 b)) :
    0 < constant f.natDegree b ∧
      Tendsto (fun N : ℕ => (∑ i ∈ range 2, row f ρ N i) /
      ((N:ℝ)*log (N:ℝ))) atTop (𝓝 (constant f.natDegree b)) := by
  let S := scale f.natDegree
  let θ : ℝ := if f.natDegree = 1 then 1/2 else 1
  have hθ : 0 < θ := by dsimp [θ]; split <;> norm_num
  have hS : Tendsto S atTop atTop := by
    change Tendsto (fun N : ℕ => scale f.natDegree N) atTop atTop
    by_cases h : f.natDegree = 1
    · simpa [S,scale,h] using sqrt_tends
    · simp only [scale,if_neg h]
      exact tendsto_id
  have ratio : Tendsto (fun N : ℕ => log (S N:ℝ)/log (N:ℝ)) atTop (𝓝 θ) := by
    by_cases h : f.natDegree = 1
    · simpa [S,scale,h,θ] using log_sqrt_ratio
    · rw [show θ = 1 by simp [θ,h]]
      apply (tendsto_const_nhds (x:=1)).congr'
      filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn'
      have hl := Real.log_pos (by exact_mod_cast (show 1 < n by omega) : (1:ℝ) < n)
      simp [S,scale,h,hl.ne']
  have hmain : Tendsto (fun N : ℕ => harmonicSum ρ (S N)/log (N:ℝ)) atTop (𝓝 (b*θ)) := by
    apply ((hlog.comp hS).mul ratio).congr'
    filter_upwards [hS.eventually_ge_atTop 2] with n hn'
    have hl := Real.log_pos (by exact_mod_cast (show 1 < S n by omega) : (1:ℝ) < S n)
    dsimp [Function.comp_def]
    field_simp
  obtain ⟨K,hK⟩ := finite f hd hp ρ hn C hC hav
  have ht : Tendsto (fun n : ℕ => log (n:ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hi (i : ℕ) (h : i ≤ 1) :
      Tendsto (fun n : ℕ => row f ρ n i / ((n:ℝ)*log n)) atTop (𝓝 (b*θ)) := by
    have err : Tendsto (fun n : ℕ => (row f ρ n i - n*harmonicSum ρ (S n))/((n:ℝ)*log n))
        atTop (𝓝 0) := by
      apply squeeze_zero_norm' (a:=fun n : ℕ => K/log n)
      · filter_upwards [eventually_ge_atTop (2:ℕ)] with n hn'
        have ha : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
        have hl := Real.log_pos (by exact_mod_cast (show 1 < n by omega) : (1:ℝ) < n)
        rw [Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos ha hl)]
        rw [div_le_div_iff₀ (mul_pos ha hl) hl]
        have hh := hK n (by omega) i h
        change |row f ρ n i - n*harmonicSum ρ (S n)| ≤ K*n at hh
        calc _ ≤ K*n*log n := mul_le_mul_of_nonneg_right hh hl.le
             _ = _ := by ring
      · exact ht.const_div_atTop K
    have he := err.add hmain
    rw [zero_add] at he
    apply he.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn'
    have hnn : (n:ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    by_cases hl : log (n:ℝ) = 0
    · simp [hl]
    · field_simp; ring
  have heq : constant f.natDegree b = b*θ+b*θ := by
    by_cases h : f.natDegree = 1 <;> simp [constant, θ, h] <;> ring
  rw [heq]
  refine ⟨add_pos (mul_pos hb hθ) (mul_pos hb hθ), ?_⟩
  apply ((hi 0 (by omega)).add (hi 1 (by omega))).congr
  intro n
  simp [sum_range_succ,add_div]

end OMA.Scale975
end

section
/- The positive mean of the short-divisor model from its corrected sum of
ideal coefficients. -/

namespace OMA.CloseModel975
open Finset Polynomial Filter Real RootsEuler975
open scoped Topology NumberField

theorem from_inverse (f : ℤ[X]) (hd : f.natDegree ≠ 0)
    (hp : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n)
    (K : Type*) [Field K] [NumberField K] (a μ : ArithmeticFunction ℝ)
    (ha : ∀ n : ℕ, n ≠ 0 → a n = (Nat.card {I : Ideal (𝓞 K) // I.absNorm=n} : ℝ))
    (hμ : μ.IsMultiplicative) (hinv : a*μ = 1)
    (B : ℝ) (hB : 0 ≤ B) (bd : ∀ p : ℕ, p.Prime → ∀ k : ℕ, |(rho f*μ) (p^k)| ≤ B)
    (M : ℕ) (hM : 0 < M) (vanish : ∀ p : ℕ, p.Prime → ¬p ∣ M → (rho f*μ) p = 0)
    (localpos : ∀ p : ℕ, p.Prime → 0 < ∑' k : ℕ, (rho f*μ) (p^k)/(p:ℝ)^k) :
    let b := Scale975.constant f.natDegree (NumberField.dedekindZeta_residue K *
      ∑' d : ℕ, (rho f*μ) d/(d:ℝ))
    (∃ C ≥ (0:ℝ), ∀ N : ℕ, (∑ q ∈ Icc 1 N, rho f q) ≤ C*N) ∧
    0 < b ∧ Tendsto (fun N : ℕ => (∑ i ∈ range 2, Scale975.row f (rho f) N i) /
      ((N:ℝ)*log (N:ℝ))) atTop (𝓝 b) := by
  let h := rho f*μ
  have good (p : ℕ) (hp' : p.Prime) (hE : p ∉ M.divisors) : h p = 0 := by
    apply vanish p hp'; simpa [Nat.mem_divisors, hM.ne'] using hE
  obtain ⟨summable,pos⟩ := EulerMass975.weighted_mass h ((multiplicative f).mul hμ)
    B hB bd M.divisors good localpos
  let R := NumberField.dedekindZeta_residue K
  have ha' : Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, a n)/(N:ℝ)) atTop (𝓝 R) := by
    apply (Kummer975.coefficient_mean K).congr
    intro n
    congr 1
    apply sum_congr rfl
    intro m hm
    exact (ha m (Nat.ne_of_gt (mem_Icc.mp hm).1)).symm
  have idn : a*h = rho f := by dsimp [h]; rw [mul_left_comm,hinv,mul_one]
  obtain ⟨avg,harm⟩ := Convolve975.transfer a h R ha' summable
  rw [idn] at avg harm
  obtain ⟨C,hC⟩ := avg.bddAbove_range
  have hbound (N : ℕ) : (∑ q ∈ Icc 1 N, rho f q) ≤ (max 0 C)*N := by
    obtain rfl | hpN := Nat.eq_zero_or_pos N
    · simp
    have hN : (0:ℝ) < N := by exact_mod_cast hpN
    exact (div_le_iff₀ hN).mp ((hC (Set.mem_range_self N)).trans (le_max_right _ _))
  refine ⟨⟨max 0 C,le_max_left _ _,hbound⟩,?_⟩
  apply Scale975.transfer f hd hp (rho f) (fun _ => Nat.cast_nonneg _) (max 0 C)
    (le_max_left _ _) hbound (R * ∑' d : ℕ, h d/(d:ℝ))
    (mul_pos (NumberField.dedekindZeta_residue_pos K) pos)
  exact harm

end OMA.CloseModel975
end

section
/- The small-divisor density for irreducible polynomials of every degree. -/

namespace OMA.AllModel975
open Finset Polynomial Filter Real RootsEuler975
open scoped Topology NumberField

theorem exact_model (f : ℤ[X]) (hd : f.natDegree ≠ 0) (hf : Irreducible f)
    (hp : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n)
    (K : Type*) [Field K] [NumberField K] (M : ℕ) (hM : 0 < M)
    (link : ∀ p : ℕ, p.Prime → ¬ p ∣ M →
      Nat.count (fun r : ℕ => (p:ℤ) ∣ f.eval (r:ℤ)) p =
      Nat.card {I : Ideal (𝓞 K) // I.absNorm = p}) :
    let b := Scale975.constant f.natDegree (NumberField.dedekindZeta_residue K *
      ∑' d : ℕ, (rho f * IdealEuler975.mu K) d/(d:ℝ))
    (∃ C ≥ (0:ℝ), ∀ N : ℕ, (∑ q ∈ Icc 1 N, rho f q) ≤ C*N) ∧
    0 < b ∧ Tendsto (fun N : ℕ => (∑ i ∈ range 2, Scale975.row f (rho f) N i) /
      ((N:ℝ)*log (N:ℝ))) atTop (𝓝 b) := by
  obtain ⟨B,hB,bound⟩ := CoeffBound975.uniform f hf hd K
  apply CloseModel975.from_inverse f hd hp K (IdealEuler975.a K) (IdealEuler975.mu K)
    (fun _ hn => IdealEuler975.a_apply K hn) (IdealEuler975.multiplicative K)
    (IdealEuler975.inverse K) B hB bound M hM (fun _ => CoeffBound975.vanish f K M link)
  intro p hp'
  obtain ⟨L,e,he,_,hcoef⟩ := IdealEuler975.local K p hp'
  exact LocalPos975.roots_positive f hf hd _ p hp' L e he hcoef

end OMA.AllModel975
end

section
namespace OMA.QuadraticField975

open Polynomial NumberField Field975
open scoped NumberField

/-- Twice the residue at one, corrected by the root counts of the given polynomial. -/
noncomputable def residueValue (f : ℤ[X]) (K : Type*) [Field K] [NumberField K] : ℝ :=
  2 * (dedekindZeta_residue K *
    ∑' n : ℕ, (RootsEuler975.rho f * IdealEuler975.mu K) n / (n : ℝ))

/-- The quadratic constant is computed in the field cut out by the integral normalization.
Outside irreducible quadratics the question imposes no condition. -/
noncomputable def constant (f : ℤ[X]) : ℝ := by
  classical
  by_cases h : Irreducible f ∧ f.natDegree = 2
  · let : Fact (Irreducible (definingPolynomial f)) :=
      ⟨irreducible_normalization f h.1 (by rw [h.2]; decide)⟩
    exact residueValue f (canonicalField f)
  · exact 0

theorem constant_eq (f : ℤ[X]) (hf : Irreducible f) (hd : f.natDegree = 2)
    [Fact (Irreducible (definingPolynomial f))] :
    constant f = residueValue f (canonicalField f) := by
  classical
  simp [constant, hf, hd]

theorem with_field (f : ℤ[X]) (hf : Irreducible f) (hd : f.degree = 2) :
    ∃ (K : Type) (_ : Field K) (_ : NumberField K), constant f =
      2 * (dedekindZeta_residue K * ∑' n : ℕ,
        (RootsEuler975.rho f * IdealEuler975.mu K) n / (n : ℝ)) ∧
      ∃ M : ℕ, 0 < M ∧ ∀ p : ℕ, p.Prime → ¬p ∣ M →
        Nat.count (fun r : ℕ => (p : ℤ) ∣ f.eval (r : ℤ)) p =
          Nat.card {I : Ideal (𝓞 K) // I.absNorm = p} := by
  have hn : f.natDegree = 2 := natDegree_eq_of_degree_eq_some hd
  have hp : 0 < f.natDegree := by omega
  let : Fact (Irreducible (definingPolynomial f)) := ⟨irreducible_normalization f hf hp⟩
  exact ⟨canonicalField f, inferInstance, inferInstance, constant_eq f hf hn, canonical_link f hf hp⟩

end OMA.QuadraticField975
end

section
/- A reduction by complementary factor pairs and periodic counting on short moduli. -/

open Finset Polynomial Real Filter Function
open scoped ArithmeticFunction.sigma Topology

namespace OMA.R_Erdos975_erdos_975_R1


-- Counting ties with weight one avoids a separate square-value error.
theorem pair_identity (m N : ℕ) :
    σ 0 m =
      (∑ d ∈ m.divisors, if d ≤ N ∧ d * d ≤ m then 1 else 0) +
      (∑ d ∈ m.divisors, if d ≤ N ∧ d * d < m then 1 else 0) +
      (m.divisorsAntidiagonal.filter (fun p ↦ N < p.1 ∧ N < p.2)).card := by
  let s := m.divisorsAntidiagonal
  have first : (∑ p ∈ s, if p.1 ≤ N ∧ p.1 ≤ p.2 then 1 else 0) =
      ∑ d ∈ m.divisors, if d ≤ N ∧ d*d ≤ m then 1 else 0 := by
    rw [show s = _ from rfl, Nat.sum_divisorsAntidiagonal
      (fun a b ↦ if a ≤ N ∧ a ≤ b then 1 else 0)]
    apply sum_congr rfl
    intro d hd
    have h := Nat.mem_divisors.mp hd
    have hp := Nat.pos_of_mem_divisors hd
    have he := Nat.mul_div_cancel' h.1
    have hh : d ≤ m / d ↔ d*d ≤ m := by
      calc d ≤ m / d ↔ d*d ≤ d*(m/d) := (Nat.mul_le_mul_left_iff hp).symm
           _ ↔ _ := by rw [he]
    simp only [hh]
  have second : (∑ p ∈ s, if p.2 ≤ N ∧ p.2 < p.1 then 1 else 0) =
      ∑ d ∈ m.divisors, if d ≤ N ∧ d*d < m then 1 else 0 := by
    rw [show s = _ from rfl, Nat.sum_divisorsAntidiagonal'
      (fun a b ↦ if b ≤ N ∧ b < a then 1 else 0)]
    apply sum_congr rfl
    intro d hd
    have h := Nat.mem_divisors.mp hd
    have hp := Nat.pos_of_mem_divisors hd
    have he := Nat.mul_div_cancel' h.1
    have hh : d < m / d ↔ d*d < m := by
      calc d < m / d ↔ d*d < d*(m/d) := (Nat.mul_lt_mul_left hp).symm
           _ ↔ _ := by rw [he]
    simp only [hh]
  rw [← first, ← second, ArithmeticFunction.sigma_zero_apply]
  have cardeq : m.divisors.card = ∑ _p ∈ s, 1 := by
    rw [show s = _ from rfl, Nat.sum_divisorsAntidiagonal (fun _ _ ↦ 1)]
    simp
  rw [cardeq, Finset.card_filter, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro p _
  split_ifs <;> omega

theorem weighted_short (m N : ℕ) (strict : Bool) :
    (∑ d ∈ m.divisors, if d ≤ N ∧ (if strict then d*d < m else d*d ≤ m) then 1 else 0) =
    ∑ d ∈ Icc 1 N, if d ∣ m ∧ (if strict then d*d < m else d*d ≤ m) then 1 else 0 := by
  classical
  rw [← Finset.card_filter, ← Finset.card_filter]
  congr 1
  ext d
  simp only [mem_filter, Nat.mem_divisors, mem_Icc]
  have hpos : d ∣ m → m ≠ 0 → 1 ≤ d := fun h hm ↦ Nat.pos_of_dvd_of_pos h (Nat.pos_of_ne_zero hm)
  have hsq : 1 ≤ d → 0 < d*d := fun hd ↦ Nat.mul_pos hd hd
  cases strict <;> simp <;> constructor <;> rintro h <;> obtain ⟨_,_⟩ := h <;> grind

-- Relate integer evaluations to the natural floor in the target, even at a root.
theorem floor_test (z : ℤ) {d : ℕ} (hd : 0 < d) (strict : Bool) :
    (d ∣ ⌊z⌋₊ ∧ (if strict then d*d < ⌊z⌋₊ else d*d ≤ ⌊z⌋₊)) ↔
    ((d : ℤ) ∣ z ∧ (if strict then (d : ℤ)*d < z else (d : ℤ)*d ≤ z)) := by
  rcases le_or_gt 0 z with h | h
  · lift z to ℕ using h with m
    simp only [Nat.floor_natCast]
    cases strict <;> simp <;> exact_mod_cast Iff.rfl
  · have hz : ⌊z⌋₊ = 0 := Nat.floor_of_nonpos h.le
    have hp : 0 < d*d := Nat.mul_pos hd hd
    have hpi : (0 : ℤ) < ↑d * ↑d := by exact_mod_cast hp
    cases strict <;> simp [hz] <;> omega


theorem periodic_roots (f : ℤ[X]) (d : ℕ) :
    Periodic (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ)) d := by
  intro n
  apply propext
  have h : (d : ℤ) ∣ f.eval ((n+d : ℕ) : ℤ) - f.eval (n : ℤ) := by
    simpa using Polynomial.sub_dvd_eval_sub ((n+d : ℕ) : ℤ) (n : ℤ) f
  exact ⟨fun h1 ↦ by simpa using dvd_sub h1 h, fun h2 ↦ by simpa using dvd_add h h2⟩

theorem count_period_block (P : ℕ → Prop) [DecidablePred P] {d : ℕ}
    (hp : Periodic P d) (A q : ℕ) :
    Nat.count (fun n ↦ P (A+n)) (q*d) = q * Nat.count P d := by
  have shift (B : ℕ) : Nat.count (fun n ↦ P (B+n)) d = Nat.count P d := by
    rw [Nat.count_eq_card_filter_range, ← Nat.filter_Ico_card_eq_of_periodic B d P hp,
      Finset.card_filter, Finset.card_filter]
    simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel, Nat.add_comm B] using
      (Finset.sum_Ico_eq_sum_range (f := fun n ↦ if P n then 1 else 0) (m := B) (n := B+d)).symm
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, Nat.count_add, ih, Nat.succ_mul]
    simpa [Nat.add_assoc] using congrArg (q * Nat.count P d + ·) (shift (A+q*d))

theorem interval_error (P : ℕ → Prop) [DecidablePred P] {d : ℕ}
    (hd : 0 < d) (hp : Periodic P d) (A L : ℕ) :
    |(Nat.count (fun n ↦ P (A+n)) L : ℝ) - (L : ℝ) / d * Nat.count P d| ≤ Nat.count P d := by
  let q := L / d
  have lo : q*d ≤ L := Nat.div_mul_le_self L d
  have hi : L ≤ (q+1)*d := by simpa [q, Nat.mul_comm] using (Nat.lt_mul_div_succ L hd).le
  have c1 := Nat.count_monotone (fun n ↦ P (A+n)) lo
  have c2 := Nat.count_monotone (fun n ↦ P (A+n)) hi
  rw [count_period_block P hp] at c1 c2
  have hlo : (q : ℝ) ≤ (L : ℝ)/d := (le_div_iff₀ (by positivity)).2 (by exact_mod_cast lo)
  have hhi : (L : ℝ)/d ≤ q+1 := (div_le_iff₀ (by positivity)).2 (by exact_mod_cast hi)
  have u := mul_le_mul_of_nonneg_right hlo (Nat.cast_nonneg (α := ℝ) (Nat.count P d))
  have v := mul_le_mul_of_nonneg_right hhi (Nat.cast_nonneg (α := ℝ) (Nat.count P d))
  have cl : (q : ℝ)*Nat.count P d ≤ Nat.count (fun n ↦ P (A+n)) L := by exact_mod_cast c1
  have cu : (Nat.count (fun n ↦ P (A+n)) L : ℝ) ≤ (q+1)*Nat.count P d := by exact_mod_cast c2
  rw [abs_le]
  constructor <;> linarith

theorem ico_root_error (P : ℕ → Prop) [DecidablePred P] {d : ℕ}
    (hd : 0 < d) (hp : Function.Periodic P d) (A T : ℕ) :
    |(((Ico A T).filter P).card : ℝ) - ((Ico A T).card : ℝ) / d * Nat.count P d| ≤ Nat.count P d := by
  have he : ((Ico A T).filter P).card = Nat.count (fun n ↦ P (A+n)) (T-A) := by
    simp only [Nat.count_eq_card_filter_range, card_filter]
    simpa only [add_comm A] using (Finset.sum_Ico_eq_sum_range (f := fun n ↦ if P n then 1 else 0) (m := A) (n := T))
  simpa only [he, Nat.card_Ico] using interval_error P hd hp A (T-A)

theorem threshold_error (f : ℤ[X]) {K : ℕ}
    (hK : Monotone (fun n : ℕ ↦ f.eval ((K+n : ℕ) : ℤ)))
    (T : ℕ) (u : ℤ) {d : ℕ} (hd : 0 < d) :
    let S := (range T).filter (fun n : ℕ ↦ u ≤ f.eval (n : ℤ))
    let P := fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ)
    |((S.filter P).card : ℝ) - (S.card : ℝ)/d * Nat.count P d| ≤ K + Nat.count P d := by
  dsimp only
  let S := (range T).filter (fun n : ℕ ↦ u ≤ f.eval (n : ℤ))
  let B := S.filter (· < K)
  let U := S.filter (K ≤ ·)
  let P := fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ)
  have hmono {n k : ℕ} (hn : K ≤ n) (hnk : n ≤ k) : f.eval (n : ℤ) ≤ f.eval (k : ℤ) := by
    simpa [Nat.add_sub_of_le hn, Nat.add_sub_of_le (hn.trans hnk)] using
      hK (show n-K ≤ k-K by omega)
  have suffix : ∃ A, U = Ico A T := by
    by_cases h : U.Nonempty
    · let a := U.min' h
      have ha : a ∈ U := U.min'_mem h
      simp only [U,S, mem_filter, mem_range] at ha
      refine ⟨a, Finset.ext (fun n ↦ ?_)⟩
      constructor
      · intro hn
        have hmin := U.min'_le n hn
        simp only [U,S,mem_filter,mem_range] at hn
        exact mem_Ico.mpr ⟨hmin, hn.1.1⟩
      · intro hn
        obtain ⟨han, hnT⟩ := mem_Ico.mp hn
        exact mem_filter.mpr ⟨mem_filter.mpr ⟨mem_range.mpr hnT, ha.1.2.trans (hmono ha.2 han)⟩, ha.2.trans han⟩
    · exact ⟨T, by simp [Finset.not_nonempty_iff_eq_empty.mp h]⟩
  obtain ⟨A, hA⟩ := suffix
  have hpart : B ∪ U = S := by
    ext n
    simp only [B,U,mem_union,mem_filter]
    by_cases hn : n < K <;> simp [hn, show K ≤ n ↔ ¬n < K from not_lt.symm]
  have hdis : Disjoint B U := by
    apply Finset.disjoint_left.mpr
    intro n hb hu
    exact (mem_filter.mp hb).2.not_ge (mem_filter.mp hu).2
  have hboth : (B.filter P).card + (U.filter P).card = (S.filter P).card := by
    rw [← card_union_of_disjoint (hdis.mono (filter_subset ..) (filter_subset ..)), ← filter_union, hpart]
  have hall : B.card + U.card = S.card := by rw [← card_union_of_disjoint hdis, hpart]
  have hB : B.card ≤ K := by
    calc B.card ≤ (range K).card := card_le_card (fun n hn ↦ mem_range.mpr (mem_filter.mp hn).2)
         _ = K := card_range _
  have hBP : (B.filter P).card ≤ K := (card_le_card (filter_subset ..)).trans hB
  have hR : Nat.count P d ≤ d := Nat.count_le _
  have hBmodel : (B.card : ℝ)/d * Nat.count P d ≤ K := by
    calc _ ≤ (B.card : ℝ)/d * d := mul_le_mul_of_nonneg_left (by exact_mod_cast hR) (by positivity)
         _ = B.card := div_mul_cancel₀ _ (by positivity)
         _ ≤ K := by exact_mod_cast hB
  have hE : |((B.filter P).card : ℝ) - (B.card : ℝ)/d * Nat.count P d| ≤ K := by
    rw [abs_le]
    have v : 0 ≤ (B.card : ℝ)/d * Nat.count P d := by positivity
    have hb' : ((B.filter P).card : ℝ) ≤ K := by exact_mod_cast hBP
    constructor <;> linarith [Nat.cast_nonneg (α := ℝ) (B.filter P).card]
  have hU : |((U.filter P).card : ℝ) - (U.card : ℝ)/d * Nat.count P d| ≤ Nat.count P d := by
    rw [hA]
    exact ico_root_error P hd (periodic_roots f d) A T
  change |((S.filter P).card : ℝ) - (S.card : ℝ)/d * Nat.count P d| ≤ _
  rw [← hboth, ← hall, Nat.cast_add, Nat.cast_add, add_div, add_mul]
  calc _ = |(((B.filter P).card : ℝ) - (B.card : ℝ)/d * Nat.count P d) +
            (((U.filter P).card : ℝ) - (U.card : ℝ)/d * Nat.count P d)| := by congr 1; ring
       _ ≤ _ := (abs_add_le ..).trans (add_le_add hE hU)


theorem eventual_sign (g : ℤ[X]) :
    (∀ᶠ n : ℕ in atTop, 0 ≤ g.eval (n : ℤ)) ∨ (∀ᶠ n : ℕ in atTop, g.eval (n : ℤ) < 0) := by
  let p := g.map (Int.castRingHom ℝ)
  have he (n : ℕ) : p.eval (n : ℝ) = (↑(g.eval (n : ℤ)) : ℝ) := by
    simp [p, Polynomial.eval_map]
  by_cases h : 0 < p.degree
  · rcases le_or_gt 0 p.leadingCoeff with hl | hl
    · left
      have hh := ((p.tendsto_atTop_of_leadingCoeff_nonneg h hl).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 0
      filter_upwards [hh] with n hn
      change 0 ≤ p.eval (n : ℝ) at hn
      rw [he] at hn
      exact_mod_cast hn
    · right
      have hh := ((p.tendsto_atBot_of_leadingCoeff_nonpos h hl.le).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_lt_atBot 0
      filter_upwards [hh] with n hn
      change p.eval (n : ℝ) < 0 at hn
      rw [he] at hn
      exact_mod_cast hn
  · have hc := Polynomial.eq_C_of_degree_le_zero (le_of_not_gt h)
    have hh (n : ℕ) : (↑(g.eval (n : ℤ)) : ℝ) = p.coeff 0 := by
      rw [← he, hc, Polynomial.eval_C]
      simp
    rcases le_or_gt 0 (p.coeff 0) with h0 | h0
    · left
      exact Eventually.of_forall fun n ↦ by exact_mod_cast (hh n ▸ h0 : 0 ≤ (↑(g.eval (n : ℤ)) : ℝ))
    · right
      exact Eventually.of_forall fun n ↦ by exact_mod_cast (hh n ▸ h0 : (↑(g.eval (n : ℤ)) : ℝ) < 0)

theorem monotone_tail (f : ℤ[X]) (hpos : ∀ᶠ n : ℤ in atTop, 1 ≤ f.eval n) :
    ∃ K : ℕ, Monotone (fun n : ℕ ↦ f.eval ((K+n : ℕ) : ℤ)) := by
  let g := f.comp (X + 1) - f
  have he (n : ℕ) : g.eval (n : ℤ) = f.eval ((n+1 : ℕ) : ℤ) - f.eval (n : ℤ) := by simp [g]
  rcases eventual_sign g with h | h
  · obtain ⟨K, hK⟩ := eventually_atTop.1 h
    refine ⟨K, monotone_nat_of_le_succ (fun n ↦ ?_)⟩
    have hn := hK (K+n) (by omega)
    rw [he] at hn
    simpa [Nat.add_assoc] using sub_nonneg.mp hn
  · have hp := tendsto_natCast_atTop_atTop (R := ℤ) |>.eventually hpos
    obtain ⟨K, hK⟩ := eventually_atTop.1 (h.and hp)
    have bound (n : ℕ) : f.eval ((K+n : ℕ) : ℤ) ≤ f.eval (K : ℤ) - n := by
      induction n with
      | zero => simp
      | succ n ih =>
        have hn := (hK (K+n) (by omega)).1
        rw [he] at hn
        push_cast at ih hn ⊢
        rw [← add_assoc]
        omega
    obtain ⟨i, hi⟩ := exists_nat_gt (f.eval (K : ℤ))
    have hb := bound i
    have hc := (hK (K+i) (by omega)).2
    omega


theorem row_middle_bound (z : ℤ) (N U : ℕ) (hz : ⌊z⌋₊ ≤ U*U) :
    ((⌊z⌋₊.divisorsAntidiagonal).filter (fun p ↦ N < p.1 ∧ N < p.2)).card ≤
    2 * ∑ d ∈ Ioc N U, if (d : ℤ) ∣ z then 1 else 0 := by
  let m := ⌊z⌋₊
  let w (d : ℕ) := if N < d ∧ d ≤ U then 1 else 0
  have hcard : ((m.divisorsAntidiagonal).filter (fun p ↦ N < p.1 ∧ N < p.2)).card ≤
      (∑ d ∈ m.divisors, w d) + ∑ d ∈ m.divisors, w d := by
    rw [Finset.card_filter]
    nth_rw 1 [← Nat.sum_divisorsAntidiagonal (n := m) (fun a _ ↦ w a)]
    rw [← Nat.sum_divisorsAntidiagonal' (n := m) (fun _ b ↦ w b), ← sum_add_distrib]
    apply sum_le_sum
    intro p hp
    have he := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have hsmall : p.1 ≤ U ∨ p.2 ≤ U := by
      by_contra! h
      have hc : (U+1)*(U+1) ≤ p.1*p.2 := Nat.mul_le_mul h.1 h.2
      change m ≤ U*U at hz
      rw [he] at hc
      nlinarith
    dsimp [w]
    split_ifs <;> omega
  have hdiv : (∑ d ∈ m.divisors, w d) ≤ ∑ d ∈ Ioc N U, if (d : ℤ) ∣ z then 1 else 0 := by
    change (∑ d ∈ m.divisors, if N < d ∧ d ≤ U then 1 else 0) ≤ _
    rw [← card_filter, ← card_filter]
    apply card_le_card
    intro d hd
    obtain ⟨hm,hdu⟩ := mem_filter.mp hd
    have hm' := Nat.mem_divisors.mp hm
    refine mem_filter.mpr ⟨mem_Ioc.mpr hdu, ?_⟩
    have hpos : 0 ≤ z := by
      by_contra! hz'
      have : m = 0 := Nat.floor_of_nonpos hz'.le
      exact hm'.2 this
    have hh : (d : ℤ) ∣ (↑m : ℤ) := by exact_mod_cast hm'.1
    simpa [m, Nat.floor_int, Int.toNat_of_nonneg hpos] using hh
  exact hcard.trans (by omega)

/-- Above the input cutoff, each residue class is visited at most once. -/
theorem total_middle_bound (f : ℤ[X]) (N U : ℕ)
    (hsize : ∀ n ≤ N, ⌊f.eval (n : ℤ)⌋₊ ≤ U*U) :
    (∑ n ∈ range (N+1), ((⌊f.eval (n : ℤ)⌋₊.divisorsAntidiagonal).filter
      (fun p ↦ N < p.1 ∧ N < p.2)).card) ≤
    2 * ∑ d ∈ Icc 1 U, Nat.count (fun n : ℕ ↦ (d : ℤ) ∣ f.eval (n : ℤ)) d := by
  let P (d n : ℕ) := (d : ℤ) ∣ f.eval (n : ℤ)
  calc
    _ ≤ ∑ n ∈ range (N+1), 2 * ∑ d ∈ Ioc N U, if P d n then 1 else 0 := by
      exact sum_le_sum fun n hn ↦ row_middle_bound _ N U (hsize n (by simpa using hn))
    _ = 2 * ∑ d ∈ Ioc N U, ∑ n ∈ range (N+1), if P d n then 1 else 0 := by
      rw [← mul_sum, sum_comm]
    _ ≤ 2 * ∑ d ∈ Ioc N U, Nat.count (P d) d := by
      gcongr with d hd
      rw [← card_filter, ← Nat.count_eq_card_filter_range]
      exact Nat.count_monotone _ (mem_Ioc.mp hd).1
    _ ≤ _ := Nat.mul_le_mul_left _ (sum_le_sum_of_subset_of_nonneg (fun d hd ↦
      mem_Icc.mpr ⟨Nat.zero_lt_of_lt (mem_Ioc.mp hd).1, (mem_Ioc.mp hd).2⟩) (by simp))

/-- A fixed multiple of the input cutoff bounds the smaller factor in degree at most two. -/
theorem quadratic_height (f : ℤ[X]) (hdeg : f.natDegree ≤ 2) :
    ∃ L : ℕ, ∀ N : ℕ, 1 ≤ N → ∀ n ≤ N, ⌊f.eval (n : ℤ)⌋₊ ≤ (L*N)*(L*N) := by
  let A := (f.coeff 0).natAbs + (f.coeff 1).natAbs + (f.coeff 2).natAbs + 1
  refine ⟨A, fun N hN n hn ↦ ?_⟩
  have he := f.eval_eq_sum_range' (n := 3) (by omega) (n : ℤ)
  simp only [sum_range_succ, sum_range_zero, zero_add, pow_zero, pow_one, mul_one] at he
  have hc (j : ℕ) : f.coeff j ≤ (↑(f.coeff j).natAbs : ℤ) := by simpa using le_abs_self (f.coeff j)
  have hN' : (1 : ℤ) ≤ N := by exact_mod_cast hN
  have hn' : (n : ℤ) ≤ N := by exact_mod_cast hn
  have h1 : (1 : ℤ) ≤ (N : ℤ)^2 := by nlinarith
  have h2 : (n : ℤ) ≤ (N : ℤ)^2 := by nlinarith
  have h3 : (n : ℤ)^2 ≤ (N : ℤ)^2 := by gcongr
  have hb : f.eval (n : ℤ) ≤ (A : ℤ) * (N : ℤ)^2 := by
    rw [he]
    calc _ ≤ (↑(f.coeff 0).natAbs : ℤ)*(N : ℤ)^2 +
             (↑(f.coeff 1).natAbs : ℤ)*(N : ℤ)^2 +
             (↑(f.coeff 2).natAbs : ℤ)*(N : ℤ)^2 := by
           gcongr
           · exact (hc 0).trans (le_mul_of_one_le_right (by positivity) h1)
           · exact hc 1
           · exact hc 2
         _ ≤ _ := by simp only [A, Nat.cast_add, Nat.cast_one]; nlinarith [sq_nonneg (N : ℤ)]
  have hA : 1 ≤ A := by dsimp [A]; omega
  have hh : f.eval (n : ℤ) ≤ ((A*N)*(A*N) : ℕ) := by
    apply hb.trans
    push_cast
    have hAA : (A : ℤ) ≤ (A : ℤ)*(A : ℤ) := le_mul_of_one_le_right (by positivity) (by exact_mod_cast hA)
    nlinarith [mul_le_mul_of_nonneg_right hAA (sq_nonneg (N : ℤ))]
  exact (Nat.floor_mono hh).trans_eq (Nat.floor_natCast _)

/-- Assign the smaller factor to the short sum, with different endpoints for the two orientations. -/
theorem integer_row (z : ℤ) (N : ℕ) :
    σ 0 ⌊z⌋₊ =
      (∑ i ∈ range 2, ∑ d ∈ Icc 1 N,
        if (d : ℤ) ∣ z ∧ (d : ℤ)*d+i ≤ z then 1 else 0) +
      (⌊z⌋₊.divisorsAntidiagonal.filter (fun p ↦ N < p.1 ∧ N < p.2)).card := by
  have hw (b : Bool) :
      (∑ d ∈ ⌊z⌋₊.divisors, if d ≤ N ∧ (if b then d*d < ⌊z⌋₊ else d*d ≤ ⌊z⌋₊) then 1 else 0) =
      ∑ d ∈ Icc 1 N, if (d : ℤ) ∣ z ∧ (if b then (d : ℤ)*d < z else (d : ℤ)*d ≤ z) then 1 else 0 := by
    rw [weighted_short]
    exact sum_congr rfl fun d hd ↦ if_congr (floor_test z (mem_Icc.mp hd).1 b) rfl rfl
  have h0 := hw false
  have h1 := hw true
  simp only [Bool.false_eq_true, if_false, if_true] at h0 h1
  rw [pair_identity, h0, h1]
  simp only [sum_range_succ, sum_range_zero, zero_add, Nat.cast_zero, add_zero, Nat.cast_one,
    Int.add_one_le_iff]

/-- Total error when each short-modulus count is replaced by interval length times root density. -/
theorem finite_estimate (f : ℤ[X]) {K : ℕ}
    (hK : Monotone (fun n : ℕ ↦ f.eval ((K+n : ℕ) : ℤ))) (x : ℝ) :
    let N := ⌊x⌋₊
    let P := fun (d n : ℕ) ↦ (d : ℤ) ∣ f.eval (n : ℤ)
    let S := fun (i d : ℕ) ↦ (range (N+1)).filter (fun n : ℕ ↦ (d : ℤ)*d+i ≤ f.eval (n : ℤ))
    let M := ∑ i ∈ range 2, ∑ d ∈ Icc 1 N, ((S i d).card : ℝ)/d * Nat.count (P d) d
    let B := ∑ n ∈ range (N+1), (((⌊f.eval (n : ℤ)⌋₊).divisorsAntidiagonal.filter
      (fun p ↦ N < p.1 ∧ N < p.2)).card : ℝ)
    |Erdos975.Erdos975Sum f x - (M+B)| ≤
      2 * ((N : ℝ)*K + ∑ d ∈ Icc 1 N, (Nat.count (P d) d : ℝ)) := by
  intro N P S M B
  let A (i d : ℕ) := (((S i d).filter (P d)).card : ℝ)
  have hcount (i d : ℕ) : A i d =
      ∑ n ∈ range (N+1), if P d n ∧ (d : ℤ)*d+i ≤ f.eval (n : ℤ) then (1 : ℝ) else 0 := by
    simp only [A,S,filter_filter,card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    exact sum_congr rfl fun n _ ↦ if_congr and_comm rfl rfl
  have hsum : Erdos975.Erdos975Sum f x = (∑ i ∈ range 2, ∑ d ∈ Icc 1 N, A i d) + B := by
    simp_rw [hcount]
    simp_rw [sum_comm (s := Icc 1 N) (t := range (N+1))]
    rw [sum_comm (s := range 2) (t := range (N+1))]
    unfold B
    rw [← sum_add_distrib]
    change (∑ n ∈ Iic N, (σ 0 ⌊f.eval (n : ℤ)⌋₊ : ℝ)) = _
    rw [← Nat.range_succ_eq_Iic]
    apply sum_congr rfl
    intro n _
    have h := congrArg (Nat.cast : ℕ → ℝ) (integer_row (f.eval (n : ℤ)) N)
    push_cast at h
    simpa [P] using h
  rw [hsum, add_sub_add_right_eq_sub, show M = _ from rfl, ← sum_sub_distrib]
  calc _ ≤ ∑ i ∈ range 2, |(∑ d ∈ Icc 1 N, A i d) -
         ∑ d ∈ Icc 1 N, ((S i d).card : ℝ)/d * Nat.count (P d) d| := Finset.abs_sum_le_sum_abs ..
       _ ≤ ∑ _i ∈ range 2, ∑ d ∈ Icc 1 N, ((K : ℝ) + Nat.count (P d) d) := by
         apply sum_le_sum
         intro i _
         rw [← sum_sub_distrib]
         exact (Finset.abs_sum_le_sum_abs ..).trans (sum_le_sum fun d hd ↦
           threshold_error f hK (N+1) ((d : ℤ)*d+i) (mem_Icc.mp hd).1)
       _ = _ := by simp [sum_add_distrib, nsmul_eq_mul]; ring

/-- Transfer a count at integer endpoints to the real normalization in the original statement. -/
theorem floor_transfer {F : ℕ → ℝ} {c : ℝ}
    (hc : Tendsto (fun N : ℕ ↦ F N / ((N : ℝ)*log N)) atTop (𝓝 c)) :
    Tendsto (fun x : ℝ ↦ F ⌊x⌋₊ / (x*log x)) atTop (𝓝 c) := by
  have hratio : Tendsto (fun x : ℝ ↦ (⌊x⌋₊ : ℝ)/x) atTop (𝓝 1) := tendsto_nat_floor_div_atTop
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hratio
  have hdiff := hlog.div_atTop Real.tendsto_log_atTop
  have hlogRatio : Tendsto (fun x : ℝ ↦ log ⌊x⌋₊ / log x) atTop (𝓝 1) := by
    have ht := hdiff.add (tendsto_const_nhds (x := (1 : ℝ)))
    rw [zero_add] at ht
    apply ht.congr'
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
    have hfloor : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
    change log ((⌊x⌋₊ : ℝ) / x) / log x + 1 = _
    rw [Real.log_div (by positivity) (by linarith)]
    field_simp [(Real.log_pos (by linarith : 1 < x)).ne']
    ring
  have ht := (hc.comp tendsto_nat_floor_atTop).mul (hratio.mul hlogRatio)
  rw [one_mul, mul_one] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (3 : ℝ)] with x hx
  have hf : 2 ≤ ⌊x⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hfn : 1 < (⌊x⌋₊ : ℝ) := by exact_mod_cast (show 1 < ⌊x⌋₊ by omega)
  change F ⌊x⌋₊ / ((⌊x⌋₊ : ℝ)*log ⌊x⌋₊) *
    (((⌊x⌋₊ : ℝ)/x)*(log ⌊x⌋₊ / log x)) = _
  field_simp [(Real.log_pos hfn).ne', (by linarith : (⌊x⌋₊ : ℝ) ≠ 0)]

end OMA.R_Erdos975_erdos_975_R1
end

section
/- Quadratic specialization of the complementary-factor argument of @desenyon
(codex-spark, with approach assistance from qwen3.6:35b-a3b), LeftToSolve PR #3938:
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/3938 .
We bound the entire discarded count linearly
before passing to the limit, thereby retaining the given threshold-model constant. -/
namespace OMA.QuadraticTransfer975
open Finset Polynomial Real Filter
open scoped Topology
open R_Erdos975_erdos_975_R1

theorem int_pos (f : ℤ[X]) (hp : ∀ᶠ n : ℕ in atTop, 1 ≤ f.eval (n : ℤ)) :
    ∀ᶠ z : ℤ in atTop, 1 ≤ f.eval z := by
  obtain ⟨b,hb⟩ := eventually_atTop.mp hp
  filter_upwards [eventually_ge_atTop (b:ℤ)] with z hz
  have eq : (z.toNat : ℤ) = z := Int.toNat_of_nonneg (by omega)
  exact eq ▸ hb z.toNat (by omega)

set_option maxHeartbeats 800000 in
theorem quadratic (f : ℤ[X]) (hd : f.natDegree ≤ 2)
    (hp : ∀ᶠ n : ℕ in atTop, 1 ≤ f.eval (n : ℤ)) (C : ℝ) (hC : 0 ≤ C)
    (hroot : ∀ N : ℕ,
      (∑ d ∈ Icc 1 N, (Nat.count (fun n : ℕ => (d:ℤ) ∣ f.eval (n:ℤ)) d : ℝ)) ≤ C*N)
    (a : ℝ)
    (model : Tendsto (fun N : ℕ =>
      (∑ i ∈ range 2, ∑ d ∈ Icc 1 N, (((range (N+1)).filter
        (fun n : ℕ => (d:ℤ)*d+i ≤ f.eval (n:ℤ))).card : ℝ)/d *
        Nat.count (fun n : ℕ => (d:ℤ) ∣ f.eval (n:ℤ)) d) / ((N:ℝ)*log N))
      atTop (𝓝 a)) :
    Tendsto (fun x : ℝ => Erdos975.Erdos975Sum f x / (x*log x)) atTop (𝓝 a) := by
  obtain ⟨K,hK⟩ := monotone_tail f (int_pos f hp)
  obtain ⟨L,hL⟩ := quadratic_height f hd
  let ρ (d : ℕ) := Nat.count (fun n : ℕ => (d:ℤ) ∣ f.eval (n:ℤ)) d
  let M (N : ℕ) := ∑ i ∈ range 2, ∑ d ∈ Icc 1 N, (((range (N+1)).filter
    (fun n : ℕ => (d:ℤ)*d+i ≤ f.eval (n:ℤ))).card : ℝ)/d * ρ d
  let B (N : ℕ) := ∑ n ∈ range (N+1), (((⌊f.eval (n:ℤ)⌋₊).divisorsAntidiagonal.filter
    (fun p => N < p.1 ∧ N < p.2)).card : ℝ)
  let E : ℝ := 2*(K+C)+2*C*L
  have middle (N : ℕ) (hN : 1 ≤ N) : B N ≤ (2*C*L)*N := by
    have bound : B N ≤ 2*(∑ d ∈ Icc 1 (L*N), (ρ d:ℝ)) := by
      unfold B ρ
      exact_mod_cast total_middle_bound f N (L*N) (hL N hN)
    calc _ ≤ _ := bound
         _ ≤ 2*(C*(L*N : ℕ)) := by gcongr; exact hroot _
         _ = _ := by push_cast; ring
  have err : Tendsto (fun x : ℝ => (Erdos975.Erdos975Sum f x-M ⌊x⌋₊)/(x*log x))
      atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun x : ℝ => E/log x)
    · filter_upwards [eventually_gt_atTop (2:ℝ)] with x hx
      let N := ⌊x⌋₊
      have hN : 1 ≤ N := Nat.le_floor (by push_cast; linarith)
      have hx' : 0 < x := by linarith
      have hl : 0 < log x := Real.log_pos (by linarith)
      have hb : 0 ≤ B N := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
      have hfin := finite_estimate f hK x
      change |Erdos975.Erdos975Sum f x-(M N+B N)| ≤
        2*((N:ℝ)*K+∑ d ∈ Icc 1 N, (ρ d:ℝ)) at hfin
      have hr : (∑ d ∈ Icc 1 N, (ρ d:ℝ)) ≤ C*N := hroot N
      have bound : |Erdos975.Erdos975Sum f x-M N| ≤ E*x := calc
        _ = |(Erdos975.Erdos975Sum f x-(M N+B N))+B N| := by ring_nf
        _ ≤ |Erdos975.Erdos975Sum f x-(M N+B N)|+|B N| := abs_add_le ..
        _ ≤ E*N := by rw [abs_of_nonneg hb]; dsimp only [E]; linarith [middle N hN]
        _ ≤ _ := mul_le_mul_of_nonneg_left (Nat.floor_le hx'.le) (by dsimp [E]; positivity)
      rw [Real.norm_eq_abs,abs_div,abs_of_pos (mul_pos hx' hl)]
      calc _ ≤ (E*x)/(x*log x) := div_le_div_of_nonneg_right bound (mul_pos hx' hl).le
           _ = _ := by field_simp
    · exact Real.tendsto_log_atTop.const_div_atTop _
  change Tendsto (fun N : ℕ => M N / ((N:ℝ)*log N)) atTop (𝓝 a) at model
  have h := (floor_transfer model).add err
  rw [add_zero] at h
  exact h.congr (fun x => by ring)

end OMA.QuadraticTransfer975
end

section
/- Explicit leading coefficient for the divisor sum of an irreducible quadratic. -/

noncomputable def OMA.answer : Polynomial ℤ → ℝ := OMA.QuadraticField975.constant

theorem OMA.solution : Erdos975.erdos_975.variants.quadratic.answer = OMA.answer →
    type_of% @Erdos975.erdos_975.variants.quadratic := by
  intro hanswer f hf hp hd c hc
  have hn : f.natDegree = 2 := Polynomial.natDegree_eq_of_degree_eq_some hd
  obtain ⟨K,fieldK,nfK,hvalue,M,hM,link⟩ := OMA.QuadraticField975.with_field f hf hd
  obtain ⟨⟨C,hC,hroot⟩,positive,model⟩ := OMA.AllModel975.exact_model f (by omega) hf
    (OMA.QuadraticTransfer975.int_pos f hp) K M hM link
  have he : c = 2*(NumberField.dedekindZeta_residue K *
      ∑' d : ℕ, (OMA.RootsEuler975.rho f*OMA.IdealEuler975.mu K) d/(d:ℝ)) := by
    rw [hc,hanswer]
    exact hvalue
  simp only [hn,OMA.Scale975.constant,show ¬(2:ℕ)=1 by decide,if_false,← he] at positive model
  exact ⟨positive,OMA.QuadraticTransfer975.quadratic f hn.le hp C hC hroot c model⟩
end
