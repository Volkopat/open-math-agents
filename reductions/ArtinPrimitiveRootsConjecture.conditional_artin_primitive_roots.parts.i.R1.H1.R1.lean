import OMAReductions.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1

/-!
Reduction of `ArtinPrimitiveRootsConjecture.conditional_artin_primitive_roots.parts.i.R1.H1`
(effective Chebotarev density estimate for the Kummer fields `Q(zeta_k, a^(1/k))` under Hooley's
hypothesis) to two standard, non-circular theorems of algebraic and analytic number theory:

- `H1`: Kummer-Dedekind complete-splitting characterization at unramified rational primes
  (`p` not dividing `a * k`) together with Hensel's discriminant upper bound for the Kummer
  splitting field `K_k = (X^k - C (a : Q)).SplittingField` (`Squarefree k`, `2 <= k`).
- `H2`: Effective Chebotarev density bound (Lagarias-Odlyzko 1977; Serre 1981, Theoreme 4)
  for completely split rational primes in any Galois number field `L / Q` under
  `ERH.ExtendedRiemannHypothesis Q` and `ERH.ExtendedRiemannHypothesis L`.

In `main`, we prove completely from scratch in Lean 4:
1. Ring-isomorphism invariance of `NumberField.dedekindZeta` and `ERH.ExtendedRiemannHypothesis`,
   deriving `ERH.ExtendedRiemannHypothesis Q` from the `k = 1` specialization of `HooleyHypothesis a`.
2. Unconditional `k = 1` error bound via Fermat's little theorem and prime-factor counting.
3. Unconditional `x <= k` regime via separability of `X^k - a`, existence of a primitive `k`-th root
   of unity in `K_k`, cyclotomic irreducibility giving `k.totient <= [K_k : Q]`, and the squarefree
   totient bound `k <= 2 * k.totient^2`.
4. Full mod-`p` Kummer splitting equivalence `k | p - 1 /\ a^((p-1)/k) = 1 <-> (X^k - a).Splits`
   over `ZMod p` for every prime `p` not dividing `a * k` via cyclicity of `(ZMod p)^*`.
5. Unification of the `2 <= k < x` regime with `H1`, `H2`, and the ramified-prime discrepancy bound
   `omega(k * |a|) <= log(k * |a|) / log 2`.
-/

namespace OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1_H1_R1

/- Kummer-Dedekind prime-splitting characterization at primes not dividing a * k and Hensel's
discriminant bound for the Kummer splitting field K = (X^k - C (a : Q)).SplittingField. -/
def H1 : Prop :=
  ∀ (a : ℤ), a ≠ 0 → ∀ (k : ℕ), Squarefree k → 2 ≤ k →
    let K := (Polynomial.X ^ k - Polynomial.C (a : ℚ)).SplittingField
    let _ : NumberField K := NumberField.of_module_finite ℚ K
    (∀ p : ℕ, p.Prime → ¬ (p : ℤ) ∣ a → ¬ p ∣ k →
      ((Polynomial.X ^ k - Polynomial.C (a : ZMod p)).Splits ↔
        (Ideal.primesOver (Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers K)).ncard =
          Module.finrank ℚ K)) ∧
    Real.log |(NumberField.discr K : ℝ)| ≤
      4 * (Module.finrank ℚ K : ℝ) * Real.log ((k : ℝ) * (a.natAbs : ℝ) + 2)

/- Lagarias-Odlyzko (1977) / Serre (1981) effective Chebotarev density bound for completely split
rational primes in a Galois number field L / Q under the Extended Riemann Hypothesis for Q and L. -/
def H2 : Prop :=
  ERH.ExtendedRiemannHypothesis ℚ →
    ∃ C : ℝ, 0 < C ∧
      ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
        ERH.ExtendedRiemannHypothesis L →
        ∀ x : ℕ, 2 ≤ x →
          |(({p : ℕ | p < x ∧ p.Prime ∧
              (Ideal.primesOver (Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers L)).ncard =
                Module.finrank ℚ L}.ncard : ℕ) : ℝ) -
            (Nat.primeCounting x : ℝ) / (Module.finrank ℚ L : ℝ)| ≤
          C * Real.sqrt x *
            (Real.log |(NumberField.discr L : ℝ)| / (Module.finrank ℚ L : ℝ) + Real.log x)

/- ============================================================================
   Part 1: Dedekind Zeta Invariance Across RingEquiv and ERH Q from HooleyHypothesis
   ============================================================================ -/

/- A ring isomorphism between number fields preserves ideal absolute norms on rings of integers. -/
lemma absNorm_map_ringEquiv {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃+* L) (I : Ideal (NumberField.RingOfIntegers K)) :
    Ideal.absNorm (I.map (NumberField.RingOfIntegers.mapRingEquiv e).toRingHom) =
      Ideal.absNorm I := by
  let eO : NumberField.RingOfIntegers K ≃+* NumberField.RingOfIntegers L :=
    NumberField.RingOfIntegers.mapRingEquiv e
  have hq : ((NumberField.RingOfIntegers K) ⧸ I) ≃+*
      ((NumberField.RingOfIntegers L) ⧸ I.map eO.toRingHom) :=
    Ideal.quotientEquiv I (I.map eO.toRingHom) eO rfl
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  exact (Nat.card_congr hq.toEquiv).symm

/- Isomorphic number fields have identical Dedekind zeta Dirichlet series. -/
lemma dedekindZeta_eq_of_ringEquiv {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃+* L) :
    NumberField.dedekindZeta K = NumberField.dedekindZeta L := by
  funext s
  unfold NumberField.dedekindZeta
  congr 1
  funext n
  congr 1
  let eO : NumberField.RingOfIntegers K ≃+* NumberField.RingOfIntegers L :=
    NumberField.RingOfIntegers.mapRingEquiv e
  have hmap_symm : ∀ I : Ideal (NumberField.RingOfIntegers K),
      (I.map eO.toRingHom).map eO.symm.toRingHom = I := by
    intro I
    rw [Ideal.map_map]
    have hcomp : eO.symm.toRingHom.comp eO.toRingHom = RingHom.id _ := by
      ext x
      exact congrArg Subtype.val (eO.symm_apply_apply x)
    rw [hcomp, Ideal.map_id]
  have hsymm_map : ∀ J : Ideal (NumberField.RingOfIntegers L),
      (J.map eO.symm.toRingHom).map eO.toRingHom = J := by
    intro J
    rw [Ideal.map_map]
    have hcomp : eO.toRingHom.comp eO.symm.toRingHom = RingHom.id _ := by
      ext x
      exact congrArg Subtype.val (eO.apply_symm_apply x)
    rw [hcomp, Ideal.map_id]
  have hnorm_symm : ∀ J : Ideal (NumberField.RingOfIntegers L),
      Ideal.absNorm (J.map eO.symm.toRingHom) = Ideal.absNorm J := by
    intro J
    have h := absNorm_map_ringEquiv e (J.map eO.symm.toRingHom)
    rw [hsymm_map J] at h
    exact h.symm
  let eqv : {I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n} ≃
      {J : Ideal (NumberField.RingOfIntegers L) // Ideal.absNorm J = n} :=
    { toFun := fun I => ⟨I.1.map eO.toRingHom, by rw [absNorm_map_ringEquiv e I.1, I.2]⟩
      invFun := fun J => ⟨J.1.map eO.symm.toRingHom, by rw [hnorm_symm J.1, J.2]⟩
      left_inv := fun I => Subtype.ext (hmap_symm I.1)
      right_inv := fun J => Subtype.ext (hsymm_map J.1) }
  exact Nat.card_congr eqv

/- Transferring ERH.ExtendedRiemannHypothesis across a ring isomorphism of number fields. -/
lemma erh_of_ringEquiv {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃+* L) (hK : ERH.ExtendedRiemannHypothesis K) :
    ERH.ExtendedRiemannHypothesis L := by
  intro Z hZL s hs0 hs1 hZs
  have hZK : ERH.IsDedekindZeta K Z := by
    refine ⟨hZL.1, fun w hw => ?_⟩
    rw [hZL.2 w hw, dedekindZeta_eq_of_ringEquiv e]
  exact hK Z hZK s hs0 hs1 hZs

/- Q itself is a splitting field of X^1 - C (a : Q) over Q. -/
lemma isSplittingField_rat_X_pow_one_sub_C (a : ℤ) :
    Polynomial.IsSplittingField ℚ ℚ (Polynomial.X ^ 1 - Polynomial.C (a : ℚ)) := by
  refine ⟨?_, ?_⟩
  · have h1 : (Polynomial.X ^ 1 - Polynomial.C (a : ℚ)).map (algebraMap ℚ ℚ) =
        (Polynomial.X - Polynomial.C (a : ℚ)) * 1 := by
      simp [pow_one]
    rw [h1, Polynomial.splits_X_sub_C_mul_iff]
    exact Polynomial.Splits.one
  · rw [eq_top_iff]
    intro q _
    exact Subalgebra.algebraMap_mem _ q

/- The splitting field of X^1 - C (a : Q) over Q is Q-algebra-isomorphic to Q. -/
lemma splittingField_one_equiv_rat (a : ℤ) :
    Nonempty ((Polynomial.X ^ 1 - Polynomial.C (a : ℚ)).SplittingField ≃ₐ[ℚ] ℚ) := by
  let _ : Polynomial.IsSplittingField ℚ ℚ (Polynomial.X ^ 1 - Polynomial.C (a : ℚ)) :=
    isSplittingField_rat_X_pow_one_sub_C a
  exact ⟨(Polynomial.IsSplittingField.algEquiv ℚ (Polynomial.X ^ 1 - Polynomial.C (a : ℚ))).symm⟩

/- The degree of the k = 1 Kummer splitting field over Q is 1. -/
lemma finrank_splittingField_one (a : ℤ) :
    Module.finrank ℚ (Polynomial.X ^ 1 - Polynomial.C (a : ℚ)).SplittingField = 1 := by
  obtain ⟨e⟩ := splittingField_one_equiv_rat a
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_self]

/- HooleyHypothesis a implies ERH.ExtendedRiemannHypothesis Q via specialization at k = 1. -/
lemma erh_rat_of_hooley {a : ℤ} (hHooley : ArtinPrimitiveRootsConjecture.HooleyHypothesis a) :
    ERH.ExtendedRiemannHypothesis ℚ := by
  have h1 := hHooley 1 squarefree_one
  let K1 := (Polynomial.X ^ 1 - Polynomial.C (a : ℚ)).SplittingField
  let _ : NumberField K1 := NumberField.of_module_finite ℚ K1
  obtain ⟨e⟩ := splittingField_one_equiv_rat a
  exact erh_of_ringEquiv e.toRingEquiv h1

/- ============================================================================
   Part 2: Prime Counting, Prime Factor Bounds, and the Unconditional k = 1 Case
   ============================================================================ -/

/- The number of primes <= x is at most x for every natural number x. -/
lemma primeCounting_le_self (x : ℕ) : Nat.primeCounting x ≤ x := by
  rw [Nat.primeCounting_eq_primeCounting'_succ, ← Nat.primesBelow_card_eq_primeCounting']
  have hsub : Nat.primesBelow (x + 1) ⊆ (Finset.range (x + 1)).erase 0 := by
    intro p hp
    rw [Nat.mem_primesBelow] at hp
    exact Finset.mem_erase.mpr ⟨hp.2.ne_zero, Finset.mem_range.mpr hp.1⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem (Finset.mem_range.mpr (Nat.succ_pos x)), Finset.card_range] at hle
  omega

/- Comparing Nat.primeCounting x with Nat.primeCounting' x. -/
lemma primeCounting_bounds_primeCounting' (x : ℕ) :
    Nat.primeCounting' x ≤ Nat.primeCounting x ∧ Nat.primeCounting x ≤ Nat.primeCounting' x + 1 := by
  rw [Nat.primeCounting_eq_primeCounting'_succ]
  unfold Nat.primeCounting'
  rw [Nat.count_succ]
  split_ifs <;> omega

/- Every natural number m has at most m distinct prime factors. -/
lemma card_primeFactors_le_self (m : ℕ) : m.primeFactors.card ≤ m := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h2 : 2 ^ m.primeFactors.card ≤ m := by
      have hprod : 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p := by
        simpa using Finset.pow_card_le_prod m.primeFactors id 2 (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
      exact hprod.trans (Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m))
    exact le_trans (Nat.lt_two_pow_self.le) h2

/- Logarithmic bound on the number of distinct prime factors of m >= 1. -/
lemma card_primeFactors_le_log {m : ℕ} (hm : 1 ≤ m) :
    (m.primeFactors.card : ℝ) ≤ Real.log (m : ℝ) / Real.log 2 := by
  have hm0 : 0 < m := by omega
  have h2 : 2 ^ m.primeFactors.card ≤ m := by
    have hprod : 2 ^ m.primeFactors.card ≤ ∏ p ∈ m.primeFactors, p := by
      simpa using Finset.pow_card_le_prod m.primeFactors id 2 (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    exact hprod.trans (Nat.le_of_dvd hm0 (Nat.prod_primeFactors_dvd m))
  have h2R : ((2 : ℝ) ^ m.primeFactors.card) ≤ (m : ℝ) := by exact_mod_cast h2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [le_div_iff₀ hlog2]
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (2 : ℝ) ^ m.primeFactors.card) h2R
  rw [Real.log_pow] at hlog
  exact hlog

/- Unconditional error bound at k = 1 for all x >= 2. -/
lemma kummer_bound_k_eq_one {a : ℤ} (ha : a ≠ 0) {x : ℕ} (hx : 2 ≤ x)
    {dec : DecidablePred (fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧ 1 ∣ p - 1 ∧
      (a : ZMod p) ^ ((p - 1) / 1) = 1)} :
    |(((@Finset.filter ℕ _ dec (Finset.range x)).card : ℕ) : ℝ) -
        (Nat.primeCounting x : ℝ) /
          ((Module.finrank ℚ (Polynomial.X ^ 1 - Polynomial.C (a : ℚ)).SplittingField : ℕ) : ℝ)| ≤
      (((a.natAbs : ℝ) + 1) / (Real.sqrt 2 * Real.log 2)) *
        Real.sqrt x * Real.log (((1 : ℕ) : ℝ) * (x : ℝ)) := by
  classical
  rw [finrank_splittingField_one a, Nat.cast_one, div_one]
  set S1 := @Finset.filter ℕ _ dec (Finset.range x)
  set P := (Finset.range x).filter Nat.Prime
  have hP_card : P.card = Nat.primeCounting' x := Nat.primesBelow_card_eq_primeCounting' x
  have hS1_sub : S1 ⊆ P := by
    intro p hp
    simp only [S1, P, Finset.mem_filter] at hp ⊢
    exact ⟨hp.1, hp.2.1⟩
  have hdiff_sub : P \ S1 ⊆ a.natAbs.primeFactors := by
    intro p hp
    simp only [Finset.mem_sdiff, P, S1, Finset.mem_filter] at hp
    rcases hp with ⟨⟨hpx, hprime⟩, hnot⟩
    have hdvdZ : (p : ℤ) ∣ a := by
      by_contra hndvd
      apply hnot
      refine ⟨hpx, hprime, hndvd, one_dvd _, ?_⟩
      rw [Nat.div_one]
      have _ : Fact p.Prime := Fact.mk hprime
      have hne : (a : ZMod p) ≠ 0 := by
        rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact ZMod.pow_card_sub_one_eq_one hne
    have hdvdN : p ∣ a.natAbs := Int.natCast_dvd.mp hdvdZ
    exact Nat.mem_primeFactors.mpr ⟨hprime, hdvdN, Int.natAbs_ne_zero.mpr ha⟩
  have hS1_le_P : S1.card ≤ P.card := Finset.card_le_card hS1_sub
  have hP_sub_S1 : P.card - S1.card ≤ a.natAbs := by
    have h1 : (P \ S1).card = P.card - S1.card := Finset.card_sdiff_of_subset hS1_sub
    rw [← h1]
    exact (Finset.card_le_card hdiff_sub).trans (card_primeFactors_le_self a.natAbs)
  obtain ⟨hpi_lo, hpi_hi⟩ := primeCounting_bounds_primeCounting' x
  rw [← hP_card] at hpi_lo hpi_hi
  have habs : |((S1.card : ℕ) : ℝ) - (Nat.primeCounting x : ℝ)| ≤ (a.natAbs : ℝ) + 1 := by
    rw [abs_le]
    have h1 : (S1.card : ℝ) ≤ (Nat.primeCounting x : ℝ) := by exact_mod_cast hS1_le_P.trans hpi_lo
    have h2 : (Nat.primeCounting x : ℝ) ≤ (S1.card : ℝ) + (a.natAbs : ℝ) + 1 := by
      have : Nat.primeCounting x ≤ S1.card + a.natAbs + 1 := by omega
      exact_mod_cast this
    constructor <;> linarith
  have hxR : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hden_pos : 0 < Real.sqrt 2 * Real.log 2 := mul_pos hsqrt2 hlog2
  have hsqrt_le : Real.sqrt 2 ≤ Real.sqrt x := Real.sqrt_le_sqrt hxR
  have hlog_le : Real.log 2 ≤ Real.log (1 * (x : ℝ)) := by
    rw [one_mul]
    exact Real.log_le_log (by norm_num) hxR
  have hprod_le : Real.sqrt 2 * Real.log 2 ≤ Real.sqrt x * Real.log (1 * (x : ℝ)) :=
    mul_le_mul hsqrt_le hlog_le hlog2.le (Real.sqrt_nonneg _)
  calc
    |((S1.card : ℕ) : ℝ) - (Nat.primeCounting x : ℝ)|
      ≤ (a.natAbs : ℝ) + 1 := habs
    _ = (((a.natAbs : ℝ) + 1) / (Real.sqrt 2 * Real.log 2)) * (Real.sqrt 2 * Real.log 2) := by
        field_simp [hden_pos.ne']
    _ ≤ (((a.natAbs : ℝ) + 1) / (Real.sqrt 2 * Real.log 2)) *
          (Real.sqrt x * Real.log (1 * (x : ℝ))) := by
        gcongr
    _ = (((a.natAbs : ℝ) + 1) / (Real.sqrt 2 * Real.log 2)) *
          Real.sqrt x * Real.log (1 * (x : ℝ)) := by
        ring

/- ============================================================================
   Part 3: Cyclotomic Degree Lower Bound, Squarefree Totient Inequality, and x <= k
   ============================================================================ -/

/- The Kummer splitting field of X^k - a over Q contains a primitive k-th root of unity, so its
degree over Q is at least k.totient. -/
lemma totient_le_finrank_splittingField {a : ℤ} (ha : a ≠ 0) {k : ℕ} (hk : 1 ≤ k) :
    k.totient ≤ Module.finrank ℚ (Polynomial.X ^ k - Polynomial.C (a : ℚ)).SplittingField := by
  classical
  let f : Polynomial ℚ := Polynomial.X ^ k - Polynomial.C (a : ℚ)
  let K := f.SplittingField
  have hk0 : k ≠ 0 := by omega
  have _ : NeZero k := ⟨hk0⟩
  have haQ : (a : ℚ) ≠ 0 := Int.cast_ne_zero.mpr ha
  have hkQ : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk0
  have hf_sep : f.Separable := Polynomial.separable_X_pow_sub_C (a : ℚ) hkQ haQ
  have hf_map_sep : (f.map (algebraMap ℚ K)).Separable := hf_sep.map
  have hf_splits : (f.map (algebraMap ℚ K)).Splits := Polynomial.SplittingField.splits f
  have hf_map_eq : f.map (algebraMap ℚ K) = Polynomial.X ^ k - Polynomial.C (algebraMap ℚ K (a : ℚ)) := by
    simp [f]
  have hdeg : (f.map (algebraMap ℚ K)).natDegree = k := by
    rw [hf_map_eq, Polynomial.natDegree_X_pow_sub_C]
  have hf_map_ne : f.map (algebraMap ℚ K) ≠ 0 := by
    intro h0
    have := congrArg Polynomial.natDegree h0
    rw [hdeg, Polynomial.natDegree_zero] at this
    omega
  have hroots_card : (f.map (algebraMap ℚ K)).roots.card = k := by
    rw [← hdeg]
    exact (Polynomial.splits_iff_card_roots.mp hf_splits)
  have hroots_nodup : (f.map (algebraMap ℚ K)).roots.Nodup := Polynomial.nodup_roots hf_map_sep
  have htoFinset_card : (f.map (algebraMap ℚ K)).roots.toFinset.card = k := by
    rw [Multiset.toFinset_card_of_nodup hroots_nodup, hroots_card]
  have hne_roots : (f.map (algebraMap ℚ K)).roots.toFinset.Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨α, hα_mem⟩ := hne_roots
  have hroot_eval : ∀ x ∈ (f.map (algebraMap ℚ K)).roots.toFinset, x ^ k = algebraMap ℚ K (a : ℚ) := by
    intro x hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hf_map_ne] at hx
    rw [Polynomial.IsRoot.def, hf_map_eq] at hx
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      sub_eq_zero] at hx
    exact hx
  have hα_pow : α ^ k = algebraMap ℚ K (a : ℚ) := hroot_eval α hα_mem
  have haK : algebraMap ℚ K (a : ℚ) ≠ 0 := (map_ne_zero (algebraMap ℚ K)).mpr haQ
  have hα_ne : α ≠ 0 := by
    intro h0
    rw [h0, zero_pow hk0] at hα_pow
    exact haK hα_pow.symm
  have hroot_ne : ∀ x ∈ (f.map (algebraMap ℚ K)).roots.toFinset, x ≠ 0 := by
    intro x hx h0
    have hxp := hroot_eval x hx
    rw [h0, zero_pow hk0] at hxp
    exact haK hxp.symm
  let toUnit : (f.map (algebraMap ℚ K)).roots.toFinset → rootsOfUnity k K := fun x =>
    ⟨Units.mk0 (x.1 / α) (div_ne_zero (hroot_ne x.1 x.2) hα_ne), by
      rw [mem_rootsOfUnity]
      ext
      simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, div_pow,
        hroot_eval x.1 x.2, hα_pow, div_self haK]⟩
  have htoUnit_inj : Function.Injective toUnit := by
    intro x y hxy
    have hval : (x.1 / α) = (y.1 / α) := by
      have := congrArg (fun u : rootsOfUnity k K => ((u : Kˣ) : K)) hxy
      simpa [toUnit] using this
    exact Subtype.ext (div_left_inj' hα_ne |>.mp hval)
  have hcard_ge : k ≤ Nat.card (rootsOfUnity k K) := by
    have hfin : Finite (rootsOfUnity k K) := by infer_instance
    have h1 : Nat.card (f.map (algebraMap ℚ K)).roots.toFinset ≤ Nat.card (rootsOfUnity k K) :=
      Nat.card_le_card_of_injective toUnit htoUnit_inj
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, htoFinset_card] at h1
    exact h1
  have hcard_eq : Nat.card (rootsOfUnity k K) = k :=
    le_antisymm (card_rootsOfUnity K k) hcard_ge
  obtain ⟨ζ, hζ⟩ := card_rootsOfUnity_eq_iff_exists_isPrimitiveRoot.mp hcard_eq
  have hζ_int : IsIntegral ℚ ζ := by
    refine ⟨Polynomial.X ^ k - 1, Polynomial.monic_X_pow_sub_C 1 hk0, ?_⟩
    simp [hζ.pow_eq_one]
  have hminpoly : minpoly ℚ ζ = Polynomial.cyclotomic k ℚ := by
    refine (minpoly.eq_of_irreducible_of_monic
      (Polynomial.cyclotomic.irreducible_rat (by omega)) ?_ (Polynomial.cyclotomic.monic k ℚ)).symm
    have hroot : (Polynomial.cyclotomic k K).IsRoot ζ :=
      (Polynomial.isRoot_cyclotomic_iff_charZero (n := k) (R := K) (by omega)).mpr hζ
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hroot
  have hsub_finrank : Module.finrank ℚ (IntermediateField.adjoin ℚ ({ζ} : Set K)) = k.totient := by
    rw [IntermediateField.adjoin.finrank hζ_int, hminpoly, Polynomial.natDegree_cyclotomic]
  have hle : Module.finrank ℚ (IntermediateField.adjoin ℚ ({ζ} : Set K)) ≤ Module.finrank ℚ K :=
    Submodule.finrank_le (IntermediateField.adjoin ℚ ({ζ} : Set K)).toSubmodule
  rw [hsub_finrank] at hle
  exact hle

/- Every odd squarefree natural number m satisfies m <= m.totient ^ 2. -/
lemma le_totient_sq_of_squarefree_odd :
    ∀ m : ℕ, Squarefree m → Odd m → m ≤ m.totient ^ 2 := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro hsqf hodd
    have hm0 : m ≠ 0 := hsqf.ne_zero
    by_cases hm1 : m = 1
    · subst hm1; norm_num
    · let p := m.minFac
      have hp : p.Prime := Nat.minFac_prime hm1
      have hpdvd : p ∣ m := Nat.minFac_dvd m
      obtain ⟨r, hr⟩ := hpdvd
      have hcop : Nat.Coprime p r := by
        rw [Nat.Prime.coprime_iff_not_dvd hp]
        intro hpr
        have hsq : p * p ∣ m := by
          rcases hpr with ⟨t, rfl⟩
          exact ⟨t, by rw [hr]; ring⟩
        exact hp.not_isUnit (hsqf p hsq)
      have hr_sqf : Squarefree r := by
        have hmul : Squarefree (p * r) := hr ▸ hsqf
        exact hmul.of_mul_right
      have hr_odd : Odd r := by
        rw [hr] at hodd
        exact (Nat.odd_mul.mp hodd).2
      have hp_odd : Odd p := by
        rw [hr] at hodd
        exact (Nat.odd_mul.mp hodd).1
      have hp3 : 3 ≤ p := by
        have hp2 := hp.two_le
        rcases hp_odd with ⟨t, ht⟩
        omega
      have hr_lt : r < m := by
        have hr0 : 0 < r := Nat.pos_of_ne_zero hr_sqf.ne_zero
        have hp2 := hp.two_le
        rw [hr]
        nlinarith
      have hih : r ≤ r.totient ^ 2 := ih r hr_lt hr_sqf hr_odd
      have htot : m.totient = (p - 1) * r.totient := by
        rw [hr, Nat.totient_mul hcop, Nat.totient_prime hp]
      have hp_sq : p ≤ (p - 1) ^ 2 := by
        obtain ⟨t, ht⟩ : ∃ t, p = t + 3 := ⟨p - 3, by omega⟩
        rw [ht]
        have hsub : t + 3 - 1 = t + 2 := by omega
        rw [hsub]
        nlinarith
      rw [htot, hr, mul_pow]
      exact Nat.mul_le_mul hp_sq hih

/- Every squarefree natural number k satisfies k <= 2 * k.totient ^ 2. -/
lemma le_two_mul_totient_sq_of_squarefree {k : ℕ} (hsqf : Squarefree k) :
    k ≤ 2 * k.totient ^ 2 := by
  rcases Nat.even_or_odd k with ⟨m, hm⟩ | hodd
  · have hk2m : k = 2 * m := by omega
    have hm_sqf : Squarefree m := (hk2m ▸ hsqf).of_mul_right
    have hnot2 : ¬ 2 ∣ m := by
      intro h2m
      rcases h2m with ⟨t, rfl⟩
      have hsq : 2 * 2 ∣ k := ⟨t, by omega⟩
      exact (by decide : ¬ IsUnit (2 : ℕ)) (hsqf 2 hsq)
    have hm_odd : Odd m := Nat.odd_iff.mpr (by omega)
    have hcop : Nat.Coprime 2 m := Nat.Prime.coprime_iff_not_dvd Nat.prime_two |>.mpr hnot2
    have htot : k.totient = m.totient := by
      rw [hk2m, Nat.totient_mul hcop, Nat.totient_two, one_mul]
    rw [htot, hk2m]
    have := le_totient_sq_of_squarefree_odd m hm_sqf hm_odd
    omega
  · have := le_totient_sq_of_squarefree_odd k hsqf hodd
    omega

/- Unconditional error bound in the large-k regime x <= k (Squarefree k, 2 <= x). -/
lemma kummer_bound_x_le_k {a : ℤ} (ha : a ≠ 0) {k x : ℕ}
    (hsqf : Squarefree k) (hx : 2 ≤ x) (hxk : x ≤ k)
    {dec : DecidablePred (fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧ k ∣ p - 1 ∧
      (a : ZMod p) ^ ((p - 1) / k) = 1)} :
    |(((@Finset.filter ℕ _ dec (Finset.range x)).card : ℕ) : ℝ) -
        (Nat.primeCounting x : ℝ) /
          ((Module.finrank ℚ (Polynomial.X ^ k - Polynomial.C (a : ℚ)).SplittingField : ℕ) : ℝ)| ≤
      (Real.sqrt 2 / Real.log 2) * Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ)) := by
  classical
  have hempty : @Finset.filter ℕ _ dec (Finset.range x) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro p hp ⟨hprime, _, hkdvd, _⟩
    rw [Finset.mem_range] at hp
    have hp2 := hprime.two_le
    have hle := Nat.le_of_dvd (by omega : 0 < p - 1) hkdvd
    omega
  rw [hempty, Finset.card_empty, Nat.cast_zero, zero_sub, abs_neg]
  set nk : ℕ := Module.finrank ℚ (Polynomial.X ^ k - Polynomial.C (a : ℚ)).SplittingField
  have hnk_nonneg : (0 : ℝ) ≤ (Nat.primeCounting x : ℝ) / (nk : ℝ) := by positivity
  rw [abs_of_nonneg hnk_nonneg]
  have hk1 : 1 ≤ k := by omega
  have htot_le : k.totient ≤ nk := totient_le_finrank_splittingField ha hk1
  have hk_le : k ≤ 2 * k.totient ^ 2 := le_two_mul_totient_sq_of_squarefree hsqf
  have hx_le_sq : (x : ℝ) ≤ 2 * (nk : ℝ) ^ 2 := by
    have h1 : x ≤ 2 * nk ^ 2 := by
      have : k.totient ^ 2 ≤ nk ^ 2 := Nat.pow_le_pow_left htot_le 2
      omega
    exact_mod_cast h1
  have hxR_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
  have hnk_pos : (0 : ℝ) < (nk : ℝ) := by
    have hpos : 0 < k.totient := Nat.totient_pos.mpr (by omega)
    exact_mod_cast (by omega : 0 < nk)
  have hsqrt_le : Real.sqrt (x : ℝ) ≤ Real.sqrt 2 * (nk : ℝ) := by
    have h1 : Real.sqrt (x : ℝ) ≤ Real.sqrt (2 * (nk : ℝ) ^ 2) := Real.sqrt_le_sqrt hx_le_sq
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_sq hnk_pos.le] at h1
    exact h1
  have hpi_le : (Nat.primeCounting x : ℝ) ≤ (x : ℝ) := by exact_mod_cast primeCounting_le_self x
  have hdiv_le : (Nat.primeCounting x : ℝ) / (nk : ℝ) ≤ Real.sqrt 2 * Real.sqrt x := by
    rw [div_le_iff₀ hnk_pos]
    calc
      (Nat.primeCounting x : ℝ) ≤ (x : ℝ) := hpi_le
      _ = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hxR_pos.le).symm
      _ ≤ Real.sqrt x * (Real.sqrt 2 * (nk : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrt_le (Real.sqrt_nonneg _)
      _ = Real.sqrt 2 * Real.sqrt x * (nk : ℝ) := by ring
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkx_ge : (2 : ℝ) ≤ (k : ℝ) * (x : ℝ) := by
    have : 2 ≤ k * x := by nlinarith
    exact_mod_cast this
  have hlog_ge : Real.log 2 ≤ Real.log ((k : ℝ) * (x : ℝ)) :=
    Real.log_le_log (by norm_num) hkx_ge
  calc
    (Nat.primeCounting x : ℝ) / (nk : ℝ)
      ≤ Real.sqrt 2 * Real.sqrt x := hdiv_le
    _ = (Real.sqrt 2 / Real.log 2) * Real.sqrt x * Real.log 2 := by
        field_simp [hlog2.ne']
    _ ≤ (Real.sqrt 2 / Real.log 2) * Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ)) := by
        gcongr

/- ============================================================================
   Part 4: Mod-p Kummer Splitting Equivalence via Cyclicity of (ZMod p)^*
   ============================================================================ -/

/- A prime p cannot divide k if k divides p - 1. -/
lemma not_dvd_of_dvd_sub_one {p k : ℕ} (hp : p.Prime) (hk : k ∣ p - 1) : ¬ p ∣ k := by
  intro hpk
  have hp_sub : p ∣ p - 1 := dvd_trans hpk hk
  have hp2 := hp.two_le
  have hle := Nat.le_of_dvd (by omega : 0 < p - 1) hp_sub
  omega

/- In the cyclic group (ZMod p)^* of order p - 1, at most gcd(p - 1, k) elements satisfy z^k = 1. -/
lemma card_pow_eq_one_units_zmod {p k : ℕ} [Fact p.Prime] (hp : p.Prime) :
    ((Finset.univ : Finset (ZMod p)ˣ).filter fun z => z ^ k = 1).card ≤ Nat.gcd (p - 1) k := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hcardU : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardU]
  have hp1_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  set g0 := Nat.gcd (p - 1) k
  set d := (p - 1) / g0
  have hg0_pos : 0 < g0 := Nat.gcd_pos_of_pos_left k hp1_pos
  have hg0_dvd : g0 ∣ p - 1 := Nat.gcd_dvd_left (p - 1) k
  have hd_mul : d * g0 = p - 1 := Nat.div_mul_cancel hg0_dvd
  have hd_pos : 0 < d := by
    by_contra h0
    have hd0 : d = 0 := Nat.eq_zero_of_not_pos h0
    rw [hd0, zero_mul] at hd_mul
    omega
  have hmem_pow : ∀ z : (ZMod p)ˣ, ∃ j : ℕ, j < p - 1 ∧ g ^ j = z := by
    intro z
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg z)
    refine ⟨(m % ((p - 1 : ℕ) : ℤ)).toNat, ?_, ?_⟩
    · have hmod_nn : 0 ≤ m % ((p - 1 : ℕ) : ℤ) := Int.emod_nonneg m (by omega)
      have hmod_lt : m % ((p - 1 : ℕ) : ℤ) < ((p - 1 : ℕ) : ℤ) := Int.emod_lt_of_pos m (by omega)
      omega
    · have hmod_nn : 0 ≤ m % ((p - 1 : ℕ) : ℤ) := Int.emod_nonneg m (by omega)
      have hcast : (((m % ((p - 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ) = m % ((p - 1 : ℕ) : ℤ) :=
        Int.toNat_of_nonneg hmod_nn
      rw [← zpow_natCast, hcast]
      have hdiv : m = ((p - 1 : ℕ) : ℤ) * (m / ((p - 1 : ℕ) : ℤ)) + m % ((p - 1 : ℕ) : ℤ) :=
        (Int.mul_ediv_add_emod m ((p - 1 : ℕ) : ℤ)).symm
      rw [← hm]
      conv_rhs => rw [hdiv, zpow_add, zpow_mul, zpow_natCast, ← hord, pow_orderOf_eq_one,
        one_zpow, one_mul]
      rw [hord]
  let S := (Finset.univ : Finset (ZMod p)ˣ).filter fun z => z ^ k = 1
  have hsub : S ⊆ (Finset.range g0).image (fun r => g ^ (r * d)) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨j, hj_lt, rfl⟩ := hmem_pow z
    have hpow1 : g ^ (j * k) = 1 := by
      rw [pow_mul]
      exact hz.2
    have hdvd_jk : p - 1 ∣ j * k := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hpow1
    have hd_dvd_j : d ∣ j := by
      have hk' : g0 ∣ k := Nat.gcd_dvd_right (p - 1) k
      have hcop : Nat.Coprime d (k / g0) := by
        have h := Nat.coprime_div_gcd_div_gcd hg0_pos (m := p - 1) (n := k)
        exact h
      have h1 : d * g0 ∣ j * (k / g0 * g0) := by
        rw [hd_mul, Nat.div_mul_cancel hk']
        exact hdvd_jk
      have h2 : g0 * d ∣ g0 * (j * (k / g0)) := by
        have ha : g0 * d = d * g0 := mul_comm _ _
        have hb : g0 * (j * (k / g0)) = j * (k / g0 * g0) := by ring
        rw [ha, hb]
        exact h1
      have h3 : d ∣ j * (k / g0) := (Nat.mul_dvd_mul_iff_left hg0_pos).mp h2
      exact hcop.dvd_of_dvd_mul_right h3
    obtain ⟨r, rfl⟩ := hd_dvd_j
    have hr_lt : r < g0 := by
      by_contra hge
      have h1 : g0 ≤ r := by omega
      have h2 : d * g0 ≤ d * r := Nat.mul_le_mul_left d h1
      omega
    rw [Finset.mem_image]
    exact ⟨r, Finset.mem_range.mpr hr_lt, by rw [mul_comm]⟩
  calc
    S.card ≤ ((Finset.range g0).image (fun r => g ^ (r * d))).card := Finset.card_le_card hsub
    _ ≤ (Finset.range g0).card := Finset.card_image_le
    _ = g0 := Finset.card_range g0

/- Mod-p Kummer splitting equivalence for primes p not dividing a * k. -/
lemma kummer_cond_iff_splits_zmod {a : ℤ} {p k : ℕ} (hp : p.Prime) (hk : 1 ≤ k)
    (hpa : ¬ (p : ℤ) ∣ a) (hpk : ¬ p ∣ k) :
    (k ∣ p - 1 ∧ (a : ZMod p) ^ ((p - 1) / k) = 1) ↔
      (Polynomial.X ^ k - Polynomial.C (a : ZMod p)).Splits := by
  classical
  have _ : Fact p.Prime := Fact.mk hp
  have ha_ne : (a : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  let f : Polynomial (ZMod p) := Polynomial.X ^ k - Polynomial.C (a : ZMod p)
  have hf_deg : f.natDegree = k := Polynomial.natDegree_X_pow_sub_C
  have hf_ne : f ≠ 0 := by
    intro h0
    have := congrArg Polynomial.natDegree h0
    rw [hf_deg, Polynomial.natDegree_zero] at this
    omega
  have hp1_pos : 0 < p - 1 := Nat.sub_pos_of_lt hp.one_lt
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  have hcardU : Nat.card (ZMod p)ˣ = p - 1 := by
    rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
  have hord : orderOf g = p - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcardU]
  let u : (ZMod p)ˣ := Units.mk0 (a : ZMod p) ha_ne
  constructor
  · rintro ⟨hkdvd, hpow⟩
    set m := (p - 1) / k
    have hkm : k * m = p - 1 := Nat.mul_div_cancel' hkdvd
    have hm_pos : 0 < m := by
      by_contra h0
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos h0
      rw [hm0, mul_zero] at hkm
      omega
    have hu_mem : ∃ t : ℕ, g ^ t = u := by
      obtain ⟨z, hz⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
      refine ⟨(z % ((p - 1 : ℕ) : ℤ)).toNat, ?_⟩
      have hnn : 0 ≤ z % ((p - 1 : ℕ) : ℤ) := Int.emod_nonneg z (by omega)
      have hcast : (((z % ((p - 1 : ℕ) : ℤ)).toNat : ℕ) : ℤ) = z % ((p - 1 : ℕ) : ℤ) :=
        Int.toNat_of_nonneg hnn
      rw [← zpow_natCast, hcast]
      have hdiv : z = ((p - 1 : ℕ) : ℤ) * (z / ((p - 1 : ℕ) : ℤ)) + z % ((p - 1 : ℕ) : ℤ) :=
        (Int.mul_ediv_add_emod z ((p - 1 : ℕ) : ℤ)).symm
      rw [← hz]
      conv_rhs => rw [hdiv, zpow_add, zpow_mul, zpow_natCast, ← hord, pow_orderOf_eq_one,
        one_zpow, one_mul]
      rw [hord]
    obtain ⟨t, ht⟩ := hu_mem
    have hgtm : g ^ (t * m) = 1 := by
      rw [pow_mul, ht]
      ext
      simpa [u] using hpow
    have hdvd_tm : k * m ∣ t * m := by
      rw [hkm, ← hord]
      exact orderOf_dvd_of_pow_eq_one hgtm
    have hkt : k ∣ t := (Nat.mul_dvd_mul_iff_right hm_pos).mp hdvd_tm
    obtain ⟨r, rfl⟩ := hkt
    let b : (ZMod p)ˣ := g ^ r
    let ζ : (ZMod p)ˣ := g ^ m
    have hbk : (b : ZMod p) ^ k = (a : ZMod p) := by
      have h1 : b ^ k = u := by
        dsimp only [b]
        rw [← pow_mul, mul_comm, ht]
      have := congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) h1
      simpa [u] using this
    have hζk : (ζ : ZMod p) ^ k = 1 := by
      have h1 : ζ ^ k = 1 := by
        dsimp only [ζ]
        rw [← pow_mul, mul_comm, hkm, ← hord, pow_orderOf_eq_one]
      have := congrArg (fun x : (ZMod p)ˣ => (x : ZMod p)) h1
      simpa using this
    let rootOf : ℕ → ZMod p := fun i => (b : ZMod p) * (ζ : ZMod p) ^ i
    have hroot_mem : ∀ i ∈ Finset.range k, rootOf i ∈ f.roots.toFinset := by
      intro i _
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hf_ne, Polynomial.IsRoot.def]
      simp only [f, rootOf, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
        Polynomial.eval_C, mul_pow, hbk]
      rw [← pow_mul, mul_comm i k, pow_mul, hζk, one_pow, mul_one, sub_self]
    have hroot_inj : Set.InjOn rootOf (Finset.range k : Set ℕ) := by
      intro i hi j hj hij
      wlog hle : i ≤ j generalizing i j
      · exact (this hj hi hij.symm (le_of_not_ge hle)).symm
      rw [Finset.mem_coe, Finset.mem_range] at hi hj
      have hb_ne : (b : ZMod p) ≠ 0 := b.ne_zero
      have hζ_eq : (ζ : ZMod p) ^ i = (ζ : ZMod p) ^ j := mul_left_cancel₀ hb_ne hij
      have hζu_eq : ζ ^ i = ζ ^ j := by
        ext
        simpa using hζ_eq
      have hdiff : ζ ^ (j - i) = 1 := by
        have h1 : ζ ^ i * ζ ^ (j - i) = ζ ^ i * 1 := by
          rw [← pow_add, Nat.add_sub_cancel' hle, mul_one, hζu_eq]
        exact mul_left_cancel h1
      have hg_diff : g ^ (m * (j - i)) = 1 := by
        dsimp only [ζ] at hdiff
        rwa [← pow_mul] at hdiff
      have hdvd_diff : k * m ∣ m * (j - i) := by
        rw [hkm, ← hord]
        exact orderOf_dvd_of_pow_eq_one hg_diff
      have hkdvd_diff : k ∣ j - i := by
        rw [mul_comm k m] at hdvd_diff
        exact (Nat.mul_dvd_mul_iff_left hm_pos).mp hdvd_diff
      by_contra hne
      have hpos : 0 < j - i := by omega
      have hle_diff := Nat.le_of_dvd hpos hkdvd_diff
      omega
    have hcard_ge : k ≤ f.roots.card := by
      have h1 : ((Finset.range k).image rootOf).card = k := by
        rw [Finset.card_image_of_injOn hroot_inj, Finset.card_range]
      have h2 : (Finset.range k).image rootOf ⊆ f.roots.toFinset := by
        intro x hx
        rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
        exact hroot_mem i hi
      calc
        k = ((Finset.range k).image rootOf).card := h1.symm
        _ ≤ f.roots.toFinset.card := Finset.card_le_card h2
        _ ≤ f.roots.card := Multiset.toFinset_card_le f.roots
    have hcard_eq : f.roots.card = f.natDegree := by
      have hle : f.roots.card ≤ f.natDegree := Polynomial.card_roots' f
      omega
    exact Polynomial.splits_iff_card_roots.mpr hcard_eq
  · intro hsplits
    have hsep : f.Separable := Polynomial.separable_X_pow_sub_C' p k (a : ZMod p) hpk ha_ne
    have hroots_card : f.roots.card = k := by
      rw [← hf_deg]
      exact Polynomial.splits_iff_card_roots.mp hsplits
    have hroots_nodup : f.roots.Nodup := Polynomial.nodup_roots hsep
    have htoFinset_card : f.roots.toFinset.card = k := by
      rw [Multiset.toFinset_card_of_nodup hroots_nodup, hroots_card]
    obtain ⟨x, hx_mem⟩ : f.roots.toFinset.Nonempty := Finset.card_pos.mp (by omega)
    have hroot_pow : ∀ y ∈ f.roots.toFinset, y ^ k = (a : ZMod p) := by
      intro y hy
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hf_ne, Polynomial.IsRoot.def] at hy
      simp only [f, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
        sub_eq_zero] at hy
      exact hy
    have hroot_ne : ∀ y ∈ f.roots.toFinset, y ≠ 0 := by
      intro y hy h0
      have hyp := hroot_pow y hy
      rw [h0, zero_pow (by omega : k ≠ 0)] at hyp
      exact ha_ne hyp.symm
    have hx_ne : x ≠ 0 := hroot_ne x hx_mem
    have hx_pow : x ^ k = (a : ZMod p) := hroot_pow x hx_mem
    let S := (Finset.univ : Finset (ZMod p)ˣ).filter fun z => z ^ k = 1
    let toS : f.roots.toFinset → S := fun y =>
      ⟨Units.mk0 (y.1 / x) (div_ne_zero (hroot_ne y.1 y.2) hx_ne), by
        rw [Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        ext
        simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, div_pow,
          hroot_pow y.1 y.2, hx_pow, div_self ha_ne]⟩
    have htoS_inj : Function.Injective toS := by
      intro y1 y2 h12
      have hval : y1.1 / x = y2.1 / x := by
        have := congrArg (fun w : S => ((w.1 : (ZMod p)ˣ) : ZMod p)) h12
        simpa [toS] using this
      exact Subtype.ext ((div_left_inj' hx_ne).mp hval)
    have hk_le_S : k ≤ S.card := by
      have h1 : Fintype.card f.roots.toFinset ≤ Fintype.card S := Fintype.card_le_of_injective toS htoS_inj
      simp only [Fintype.card_coe, htoFinset_card] at h1
      exact h1
    have hk_le_gcd : k ≤ Nat.gcd (p - 1) k := hk_le_S.trans (card_pow_eq_one_units_zmod hp)
    have hgcd_eq : Nat.gcd (p - 1) k = k :=
      le_antisymm (Nat.gcd_le_right (p - 1) (by omega)) hk_le_gcd
    have hkdvd : k ∣ p - 1 := by
      rw [← hgcd_eq]
      exact Nat.gcd_dvd_left (p - 1) k
    refine ⟨hkdvd, ?_⟩
    rw [← hx_pow, ← pow_mul, Nat.mul_div_cancel' hkdvd]
    exact ZMod.pow_card_sub_one_eq_one hx_ne

/- ============================================================================
   Part 5: Logarithmic Comparison and the Main 2 <= k < x Regime
   ============================================================================ -/

/- Controlling log(k * |a| + 2) linearly in log(k * x) for all k >= 2, x >= 2, a != 0. -/
lemma log_k_mul_natAbs_add_two_le {a : ℤ} (ha : a ≠ 0) {k x : ℕ} (hk : 2 ≤ k) (hx : 2 ≤ x) :
    Real.log ((k : ℝ) * (a.natAbs : ℝ) + 2) ≤
      (1 + Real.log ((a.natAbs : ℝ) + 1) / Real.log 2) * Real.log ((k : ℝ) * (x : ℝ)) := by
  have ha1 : 1 ≤ a.natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr ha)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hxR : (2 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have haR : (1 : ℝ) ≤ (a.natAbs : ℝ) := by exact_mod_cast ha1
  have hkx_pos : (0 : ℝ) < (k : ℝ) * (x : ℝ) := by positivity
  have hkx_ge2 : (2 : ℝ) ≤ (k : ℝ) * (x : ℝ) := by nlinarith
  have hlog_kx : Real.log 2 ≤ Real.log ((k : ℝ) * (x : ℝ)) := Real.log_le_log (by norm_num) hkx_ge2
  have hinner : (k : ℝ) * (a.natAbs : ℝ) + 2 ≤ ((k : ℝ) * (x : ℝ)) * ((a.natAbs : ℝ) + 1) := by
    have h1 : (k : ℝ) * (a.natAbs : ℝ) + 2 ≤ (k : ℝ) * ((a.natAbs : ℝ) + 1) := by nlinarith
    have hkx : (k : ℝ) ≤ (k : ℝ) * (x : ℝ) := by nlinarith
    have h2 : (k : ℝ) * ((a.natAbs : ℝ) + 1) ≤ (k : ℝ) * (x : ℝ) * ((a.natAbs : ℝ) + 1) :=
      mul_le_mul_of_nonneg_right hkx (by positivity)
    exact h1.trans h2
  have hlog1 : Real.log ((k : ℝ) * (a.natAbs : ℝ) + 2) ≤
      Real.log ((k : ℝ) * (x : ℝ)) + Real.log ((a.natAbs : ℝ) + 1) := by
    have := Real.log_le_log (by positivity : (0 : ℝ) < (k : ℝ) * (a.natAbs : ℝ) + 2) hinner
    rwa [Real.log_mul hkx_pos.ne' (by positivity : ((a.natAbs : ℝ) + 1) ≠ 0)] at this
  have hlog_a_nn : 0 ≤ Real.log ((a.natAbs : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hlog_a_le : Real.log ((a.natAbs : ℝ) + 1) ≤
      (Real.log ((a.natAbs : ℝ) + 1) / Real.log 2) * Real.log ((k : ℝ) * (x : ℝ)) := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2]
    exact mul_le_mul_of_nonneg_left hlog_kx hlog_a_nn
  linarith

/- Combining H1, H2, and the mod-p Kummer equivalence in the 2 <= k < x regime. -/
lemma kummer_bound_two_le_k_lt_x {a : ℤ} (ha : a ≠ 0)
    (hHooley : ArtinPrimitiveRootsConjecture.HooleyHypothesis a)
    (hH1 : H1) {C_LO : ℝ} (hC_LO_pos : 0 < C_LO)
    (hCheb : ∀ (L : Type) [Field L] [NumberField L] [IsGalois ℚ L],
      ERH.ExtendedRiemannHypothesis L →
      ∀ x : ℕ, 2 ≤ x →
        |(({p : ℕ | p < x ∧ p.Prime ∧
            (Ideal.primesOver (Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers L)).ncard =
              Module.finrank ℚ L}.ncard : ℕ) : ℝ) -
          (Nat.primeCounting x : ℝ) / (Module.finrank ℚ L : ℝ)| ≤
        C_LO * Real.sqrt x *
          (Real.log |(NumberField.discr L : ℝ)| / (Module.finrank ℚ L : ℝ) + Real.log x))
    {k x : ℕ} (hsqf : Squarefree k) (hk2 : 2 ≤ k) (hx2 : 2 ≤ x)
    {dec : DecidablePred (fun p : ℕ => p.Prime ∧ ¬ (p : ℤ) ∣ a ∧ k ∣ p - 1 ∧
      (a : ZMod p) ^ ((p - 1) / k) = 1)} :
    |(((@Finset.filter ℕ _ dec (Finset.range x)).card : ℕ) : ℝ) -
        (Nat.primeCounting x : ℝ) /
          ((Module.finrank ℚ (Polynomial.X ^ k - Polynomial.C (a : ℚ)).SplittingField : ℕ) : ℝ)| ≤
      (((1 + Real.log ((a.natAbs : ℝ) + 1) / Real.log 2) / Real.log 2) +
        C_LO * (4 * (1 + Real.log ((a.natAbs : ℝ) + 1) / Real.log 2) + 1)) *
        Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ)) := by
  classical
  let f : Polynomial ℚ := Polynomial.X ^ k - Polynomial.C (a : ℚ)
  let _ : NumberField f.SplittingField := NumberField.of_module_finite ℚ f.SplittingField
  let _ : Polynomial.IsSplittingField ℚ f.SplittingField f :=
    Polynomial.IsSplittingField.splittingField f
  have hf_sep : f.Separable :=
    Polynomial.separable_X_pow_sub_C (a : ℚ) (Nat.cast_ne_zero.mpr (by omega)) (Int.cast_ne_zero.mpr ha)
  let _ : IsGalois ℚ f.SplittingField := IsGalois.of_separable_splitting_field hf_sep
  have hERH_K : ERH.ExtendedRiemannHypothesis f.SplittingField := hHooley k hsqf
  obtain ⟨hsplit_iff, hdiscr⟩ := hH1 a ha k hsqf hk2
  have hcheb_K := hCheb f.SplittingField hERH_K x hx2
  set S_kum := @Finset.filter ℕ _ dec (Finset.range x)
  set S_spl := (Finset.range x).filter fun p : ℕ => p.Prime ∧
    (Ideal.primesOver (Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers f.SplittingField)).ncard =
      Module.finrank ℚ f.SplittingField
  have hncard_eq : ({p : ℕ | p < x ∧ p.Prime ∧
      (Ideal.primesOver (Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers f.SplittingField)).ncard =
        Module.finrank ℚ f.SplittingField}.ncard : ℕ) = S_spl.card := by
    have hset : {p : ℕ | p < x ∧ p.Prime ∧
        (Ideal.primesOver (Ideal.span {(p : ℤ)}) (NumberField.RingOfIntegers f.SplittingField)).ncard =
          Module.finrank ℚ f.SplittingField} = (S_spl : Set ℕ) := by
      ext p
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, S_spl, Finset.mem_filter, Finset.mem_range]
    rw [hset, Set.ncard_coe_finset]
  rw [hncard_eq] at hcheb_K
  have hsub : S_kum ⊆ S_spl := by
    intro p hp
    simp only [S_kum, S_spl, Finset.mem_filter] at hp ⊢
    rcases hp with ⟨hpx, hprime, hpa, hkdvd, hpow⟩
    have hpk : ¬ p ∣ k := not_dvd_of_dvd_sub_one hprime hkdvd
    have hsp : (Polynomial.X ^ k - Polynomial.C (a : ZMod p)).Splits :=
      (kummer_cond_iff_splits_zmod hprime (by omega) hpa hpk).mp ⟨hkdvd, hpow⟩
    exact ⟨hpx, hprime, (hsplit_iff p hprime hpa hpk).mp hsp⟩
  have hdiff_sub : S_spl \ S_kum ⊆ (k * a.natAbs).primeFactors := by
    intro p hp
    simp only [Finset.mem_sdiff, S_spl, S_kum, Finset.mem_filter] at hp
    rcases hp with ⟨⟨hpx, hprime, hspl_p⟩, hnot⟩
    have hdvd_ka : p ∣ k * a.natAbs := by
      by_cases hpa : (p : ℤ) ∣ a
      · exact dvd_mul_of_dvd_right (Int.natCast_dvd.mp hpa) k
      · by_cases hpk : p ∣ k
        · exact dvd_mul_of_dvd_left hpk a.natAbs
        · exfalso
          apply hnot
          have hsp : (Polynomial.X ^ k - Polynomial.C (a : ZMod p)).Splits :=
            (hsplit_iff p hprime hpa hpk).mpr hspl_p
          obtain ⟨hkdvd, hpow⟩ := (kummer_cond_iff_splits_zmod hprime (by omega) hpa hpk).mpr hsp
          exact ⟨hpx, hprime, hpa, hkdvd, hpow⟩
    have hka_ne : k * a.natAbs ≠ 0 := mul_ne_zero (by omega) (Int.natAbs_ne_zero.mpr ha)
    exact Nat.mem_primeFactors.mpr ⟨hprime, hdvd_ka, hka_ne⟩
  have hka_pos : 1 ≤ k * a.natAbs := by
    have ha1 : 1 ≤ a.natAbs := Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr ha)
    nlinarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set Ma : ℝ := 1 + Real.log ((a.natAbs : ℝ) + 1) / Real.log 2
  have hMa_ge1 : 1 ≤ Ma := by
    have hnn : 0 ≤ Real.log ((a.natAbs : ℝ) + 1) := by
      have ha1 : (1 : ℝ) ≤ (a.natAbs : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero (Int.natAbs_ne_zero.mpr ha)
      exact Real.log_nonneg (by linarith)
    dsimp only [Ma]
    have : 0 ≤ Real.log ((a.natAbs : ℝ) + 1) / Real.log 2 := div_nonneg hnn hlog2.le
    linarith
  have hlog_ka_le : Real.log ((k : ℝ) * (a.natAbs : ℝ) + 2) ≤ Ma * Real.log ((k : ℝ) * (x : ℝ)) :=
    log_k_mul_natAbs_add_two_le ha hk2 hx2
  have hdiff_abs : |((S_kum.card : ℕ) : ℝ) - ((S_spl.card : ℕ) : ℝ)| ≤
      (Ma / Real.log 2) * Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ)) := by
    have hcard_le : S_kum.card ≤ S_spl.card := Finset.card_le_card hsub
    have hdiff_nat : S_spl.card - S_kum.card ≤ (k * a.natAbs).primeFactors.card := by
      rw [← Finset.card_sdiff_of_subset hsub]
      exact Finset.card_le_card hdiff_sub
    have habs_eq : |((S_kum.card : ℕ) : ℝ) - ((S_spl.card : ℕ) : ℝ)| =
        ((S_spl.card - S_kum.card : ℕ) : ℝ) := by
      rw [abs_sub_comm, abs_of_nonneg (by exact_mod_cast Nat.zero_le _)]
      rw [Nat.cast_sub hcard_le]
    rw [habs_eq]
    have h1 : ((S_spl.card - S_kum.card : ℕ) : ℝ) ≤
        Real.log ((k * a.natAbs : ℕ) : ℝ) / Real.log 2 := by
      have hcast : ((S_spl.card - S_kum.card : ℕ) : ℝ) ≤ ((k * a.natAbs).primeFactors.card : ℝ) := by
        exact_mod_cast hdiff_nat
      exact hcast.trans (card_primeFactors_le_log hka_pos)
    have h2 : Real.log ((k * a.natAbs : ℕ) : ℝ) ≤ Real.log ((k : ℝ) * (a.natAbs : ℝ) + 2) := by
      rw [Nat.cast_mul]
      exact Real.log_le_log (by exact_mod_cast (by omega : 0 < k * a.natAbs) : (0 : ℝ) < (k : ℝ) * (a.natAbs : ℝ))
        (by linarith)
    have hsqrt_ge1 : (1 : ℝ) ≤ Real.sqrt x := by
      rw [Real.le_sqrt (by norm_num) (by positivity)]
      have : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (by omega : 1 ≤ x)
      nlinarith
    have hlog_kx_nn : 0 ≤ Real.log ((k : ℝ) * (x : ℝ)) := by
      have : (1 : ℝ) ≤ (k : ℝ) * (x : ℝ) := by
        have : 1 ≤ k * x := by nlinarith
        exact_mod_cast this
      exact Real.log_nonneg this
    have hMa_nn : 0 ≤ Ma / Real.log 2 := div_nonneg (by linarith) hlog2.le
    calc
      ((S_spl.card - S_kum.card : ℕ) : ℝ)
        ≤ Real.log ((k * a.natAbs : ℕ) : ℝ) / Real.log 2 := h1
      _ ≤ Real.log ((k : ℝ) * (a.natAbs : ℝ) + 2) / Real.log 2 :=
          div_le_div_of_nonneg_right h2 hlog2.le
      _ ≤ (Ma * Real.log ((k : ℝ) * (x : ℝ))) / Real.log 2 :=
          div_le_div_of_nonneg_right hlog_ka_le hlog2.le
      _ = (Ma / Real.log 2) * 1 * Real.log ((k : ℝ) * (x : ℝ)) := by ring
      _ ≤ (Ma / Real.log 2) * Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ)) := by gcongr
  have hfin_pos : (0 : ℝ) < (Module.finrank ℚ f.SplittingField : ℝ) := by
    have h1 : 1 ≤ k.totient := Nat.totient_pos.mpr (by omega)
    have h2 : k.totient ≤ Module.finrank ℚ f.SplittingField := totient_le_finrank_splittingField ha (by omega)
    exact_mod_cast (by omega : 0 < Module.finrank ℚ f.SplittingField)
  have hdiscr_div : Real.log |(NumberField.discr f.SplittingField : ℝ)| / (Module.finrank ℚ f.SplittingField : ℝ) ≤
      4 * Ma * Real.log ((k : ℝ) * (x : ℝ)) := by
    rw [div_le_iff₀ hfin_pos]
    calc
      Real.log |(NumberField.discr f.SplittingField : ℝ)|
        ≤ 4 * (Module.finrank ℚ f.SplittingField : ℝ) * Real.log ((k : ℝ) * (a.natAbs : ℝ) + 2) := hdiscr
      _ ≤ 4 * (Module.finrank ℚ f.SplittingField : ℝ) * (Ma * Real.log ((k : ℝ) * (x : ℝ))) := by
          gcongr
      _ = 4 * Ma * Real.log ((k : ℝ) * (x : ℝ)) * (Module.finrank ℚ f.SplittingField : ℝ) := by ring
  have hlogx_le : Real.log (x : ℝ) ≤ Real.log ((k : ℝ) * (x : ℝ)) := by
    have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : 1 ≤ k)
    exact Real.log_le_log hx_pos (by nlinarith)
  have hcheb_le : |((S_spl.card : ℕ) : ℝ) - (Nat.primeCounting x : ℝ) / (Module.finrank ℚ f.SplittingField : ℝ)| ≤
      C_LO * (4 * Ma + 1) * Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ)) := by
    calc
      |((S_spl.card : ℕ) : ℝ) - (Nat.primeCounting x : ℝ) / (Module.finrank ℚ f.SplittingField : ℝ)|
        ≤ C_LO * Real.sqrt x *
            (Real.log |(NumberField.discr f.SplittingField : ℝ)| / (Module.finrank ℚ f.SplittingField : ℝ) + Real.log x) := hcheb_K
      _ ≤ C_LO * Real.sqrt x *
            (4 * Ma * Real.log ((k : ℝ) * (x : ℝ)) + Real.log ((k : ℝ) * (x : ℝ))) := by
          gcongr
      _ = C_LO * (4 * Ma + 1) * Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ)) := by ring
  have htri : |((S_kum.card : ℕ) : ℝ) - (Nat.primeCounting x : ℝ) / (Module.finrank ℚ f.SplittingField : ℝ)| ≤
      |((S_kum.card : ℕ) : ℝ) - ((S_spl.card : ℕ) : ℝ)| +
      |((S_spl.card : ℕ) : ℝ) - (Nat.primeCounting x : ℝ) / (Module.finrank ℚ f.SplittingField : ℝ)| := by
    have hsplit : ((S_kum.card : ℕ) : ℝ) - (Nat.primeCounting x : ℝ) / (Module.finrank ℚ f.SplittingField : ℝ) =
        (((S_kum.card : ℕ) : ℝ) - ((S_spl.card : ℕ) : ℝ)) +
        (((S_spl.card : ℕ) : ℝ) - (Nat.primeCounting x : ℝ) / (Module.finrank ℚ f.SplittingField : ℝ)) := by ring
    rw [hsplit]
    exact abs_add_le _ _
  calc
    |((S_kum.card : ℕ) : ℝ) - (Nat.primeCounting x : ℝ) / (Module.finrank ℚ f.SplittingField : ℝ)|
      ≤ (Ma / Real.log 2) * Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ)) +
          C_LO * (4 * Ma + 1) * Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ)) :=
        htri.trans (add_le_add hdiff_abs hcheb_le)
    _ = ((Ma / Real.log 2) + C_LO * (4 * Ma + 1)) *
          Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ)) := by ring

/- ============================================================================
   Part 6: Main Reduction Theorem
   ============================================================================ -/

/- Deduction of OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1.H1
from H1 (Kummer-Dedekind splitting + Hensel discriminant bound) and H2 (effective Chebotarev). -/
theorem main : H1 → H2 →
    OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1.H1 := by
  intro hH1 hH2 a ha hHooley
  have hERH_Q : ERH.ExtendedRiemannHypothesis ℚ := erh_rat_of_hooley hHooley
  obtain ⟨C_LO, hC_LO_pos, hCheb⟩ := hH2 hERH_Q
  let C1 : ℝ := ((a.natAbs : ℝ) + 1) / (Real.sqrt 2 * Real.log 2)
  let C2 : ℝ := Real.sqrt 2 / Real.log 2
  let Ma : ℝ := 1 + Real.log ((a.natAbs : ℝ) + 1) / Real.log 2
  let C3 : ℝ := Ma / Real.log 2 + C_LO * (4 * Ma + 1)
  refine ⟨max C1 (max C2 C3), ?_⟩
  intro k x hsqf hx
  have hk0 : k ≠ 0 := hsqf.ne_zero
  have hkx_nn : 0 ≤ Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ)) := by
    have hkx1 : (1 : ℝ) ≤ (k : ℝ) * (x : ℝ) := by
      have : 1 ≤ k * x := by
        have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
        nlinarith
      exact_mod_cast this
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hkx1)
  by_cases hk1 : k = 1
  · subst hk1
    have hC : C1 ≤ max C1 (max C2 C3) := le_max_left _ _
    refine (kummer_bound_k_eq_one ha hx).trans ?_
    calc
      C1 * Real.sqrt x * Real.log (((1 : ℕ) : ℝ) * (x : ℝ))
        = C1 * (Real.sqrt x * Real.log (((1 : ℕ) : ℝ) * (x : ℝ))) := by ring
      _ ≤ max C1 (max C2 C3) * (Real.sqrt x * Real.log (((1 : ℕ) : ℝ) * (x : ℝ))) :=
          mul_le_mul_of_nonneg_right hC hkx_nn
      _ = max C1 (max C2 C3) * Real.sqrt x * Real.log (((1 : ℕ) : ℝ) * (x : ℝ)) := by ring
  · by_cases hxk : x ≤ k
    · have hC : C2 ≤ max C1 (max C2 C3) := le_trans (le_max_left _ _) (le_max_right _ _)
      refine (kummer_bound_x_le_k ha hsqf hx hxk).trans ?_
      calc
        C2 * Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ))
          = C2 * (Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ))) := by ring
        _ ≤ max C1 (max C2 C3) * (Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ))) :=
            mul_le_mul_of_nonneg_right hC hkx_nn
        _ = max C1 (max C2 C3) * Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ)) := by ring
    · have hk2 : 2 ≤ k := by omega
      have hC : C3 ≤ max C1 (max C2 C3) := le_trans (le_max_right _ _) (le_max_right _ _)
      refine (kummer_bound_two_le_k_lt_x ha hHooley hH1 hC_LO_pos hCheb hsqf hk2 hx).trans ?_
      calc
        C3 * Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ))
          = C3 * (Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ))) := by ring
        _ ≤ max C1 (max C2 C3) * (Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ))) :=
            mul_le_mul_of_nonneg_right hC hkx_nn
        _ = max C1 (max C2 C3) * Real.sqrt x * Real.log ((k : ℝ) * (x : ℝ)) := by ring

end OMA.R_ArtinPrimitiveRootsConjecture_conditional_artin_primitive_roots_parts_i_R1_H1_R1
