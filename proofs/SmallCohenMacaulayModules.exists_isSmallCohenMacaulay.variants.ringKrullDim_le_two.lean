import FormalConjectures.Wikipedia.SmallCohenMacaulayModules

open IsLocalRing Module

namespace SmallCohenMacaulayLeTwo

universe u

/-!
Part 1: Quotient Completeness, Prime Avoidance, Systems of Parameters, and Dimensions 0 and 1
-/

private lemma quotient_isAdicComplete
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] (P : Ideal R) [P.IsPrime]
    [IsLocalRing (R ⧸ P)] :
    IsAdicComplete (maximalIdeal (R ⧸ P)) (R ⧸ P) := by
  have hsurj : Function.Surjective (Ideal.Quotient.mk P) := Ideal.Quotient.mk_surjective
  have hmap : (maximalIdeal R).map (Ideal.Quotient.mk P) = maximalIdeal (R ⧸ P) := by
    have hker : RingHom.ker (Ideal.Quotient.mk P) ≤ maximalIdeal R := by
      rw [Ideal.mk_ker]
      exact le_maximalIdeal (Ideal.IsPrime.ne_top ‹P.IsPrime›)
    have hmax : ((maximalIdeal R).map (Ideal.Quotient.mk P)).IsMaximal :=
      Ideal.IsMaximal.map_of_surjective_of_ker_le hsurj hker
    exact IsLocalRing.eq_maximalIdeal hmax
  rw [← hmap]
  have : Module.Finite R (R ⧸ P) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ R P).toLinearMap hsurj
  have hpre : IsPrecomplete (maximalIdeal R) (R ⧸ P) := by
    refine ⟨fun f hf => ?_⟩
    let c : AdicCompletion (maximalIdeal R) (R ⧸ P) :=
      ⟨fun n => (maximalIdeal R ^ n • (⊤ : Submodule R (R ⧸ P))).mkQ (f n),
        fun {m n} hmn => (SModEq.def.mp (hf hmn)).symm⟩
    have hms := AdicCompletion.map_surjective (maximalIdeal R)
      (f := (Ideal.Quotient.mkₐ R P).toLinearMap) hsurj
    obtain ⟨x, hx⟩ := hms c
    let r : R := (AdicCompletion.ofAlgEquiv (maximalIdeal R)).symm x
    have hr : AdicCompletion.of (maximalIdeal R) R r = x :=
      (AdicCompletion.ofAlgEquiv (maximalIdeal R)).apply_symm_apply x
    refine ⟨Ideal.Quotient.mk P r, fun n => ?_⟩
    have hval := congrArg (fun z : AdicCompletion (maximalIdeal R) (R ⧸ P) => z.val n) hx
    rw [← hr] at hval
    have hcomm : AdicCompletion.map (maximalIdeal R) (Ideal.Quotient.mkₐ R P).toLinearMap
        (AdicCompletion.of (maximalIdeal R) R r) =
        AdicCompletion.of (maximalIdeal R) (R ⧸ P) (Ideal.Quotient.mk P r) := rfl
    rw [hcomm, AdicCompletion.of_apply] at hval
    exact SModEq.def.mpr hval.symm
  have hcompR : IsAdicComplete (maximalIdeal R) (R ⧸ P) :=
    { toIsHausdorff := inferInstance, toIsPrecomplete := hpre }
  exact (IsAdicComplete.map_algebraMap_iff (maximalIdeal R) (R ⧸ P)).mpr hcompR

private lemma ringKrullDim_le_two_cases
    {R : Type u} [CommRing R] [IsLocalRing R] (hR : ringKrullDim R ≤ 2) :
    ringKrullDim R = 0 ∨ ringKrullDim R = 1 ∨ ringKrullDim R = 2 := by
  have hnn : (0 : WithBot ℕ∞) ≤ ringKrullDim R := ringKrullDim_nonneg_of_nontrivial
  cases hd : ringKrullDim R with
  | bot =>
    rw [hd] at hnn
    exact absurd hnn (by decide)
  | coe a =>
    rw [hd] at hR
    cases a with
    | top =>
      exact absurd hR (by decide)
    | coe n =>
      have hn : n ≤ 2 := by
        have h1 : ((n : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := hR
        rw [WithBot.coe_le_coe] at h1
        exact_mod_cast h1
      have h012 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
      rcases h012 with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)

private lemma exists_mem_maximalIdeal_notMem_minimalPrimes_of_height_pos
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I : Ideal R)
    (hmax : maximalIdeal R ∉ I.minimalPrimes) :
    ∃ x ∈ maximalIdeal R, ∀ P ∈ I.minimalPrimes, x ∉ P := by
  classical
  have hfin : I.minimalPrimes.Finite := Ideal.finite_minimalPrimes_of_isNoetherianRing R I
  by_contra h
  have hsub : (maximalIdeal R : Set R) ⊆ ⋃ P ∈ I.minimalPrimes, (P : Set R) := by
    intro x hx
    by_contra hnx
    apply h
    refine ⟨x, hx, fun P hP hxP => hnx (Set.mem_biUnion hP hxP)⟩
  rcases I.minimalPrimes.eq_empty_or_nonempty with hemp | ⟨P₀, hP₀⟩
  · rw [hemp, Set.biUnion_empty] at hsub
    have h0 : (0 : R) ∈ (∅ : Set R) := hsub (maximalIdeal R).zero_mem
    exact h0
  · have hprime : ∀ P ∈ I.minimalPrimes, P ≠ P₀ → P ≠ P₀ → P.IsPrime := fun P hP _ _ => hP.1.1
    obtain ⟨P, hP, hle⟩ := (Ideal.subset_union_prime_finite hfin P₀ P₀ hprime).mp hsub
    have heq : P = maximalIdeal R :=
      (IsLocalRing.maximalIdeal.isMaximal R).eq_of_le hP.1.1.ne_top hle |>.symm
    rw [heq] at hP
    exact hmax hP

private lemma exists_ltSeries_of_ringKrullDim_eq
    {R : Type u} [CommRing R] [IsLocalRing R] {n : ℕ} (hR : ringKrullDim R = n) :
    ∃ P : Ideal R, P ∈ minimalPrimes R ∧ ringKrullDim (R ⧸ P) = n := by
  have hht : (maximalIdeal R).height = n := by
    have h := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [hR] at h
    exact WithBot.coe_injective h
  have : (maximalIdeal R).FiniteHeight := ⟨Or.inr (by rw [hht]; exact WithTop.coe_ne_top)⟩
  obtain ⟨s, _hlast, hlen⟩ := Ideal.exists_ltSeries_length_eq_height (maximalIdeal R)
  rw [hht] at hlen
  let P₀ : Ideal R := (s 0).asIdeal
  have hP₀_prime : P₀.IsPrime := (s 0).isPrime
  obtain ⟨P, hPmin, hPle⟩ := Ideal.exists_minimalPrimes_le (J := P₀) bot_le
  have : P.IsPrime := hPmin.1.1
  refine ⟨P, hPmin, le_antisymm ?_ ?_⟩
  · rw [← hR]
    exact ringKrullDim_quotient_le P
  · let t : LTSeries (PrimeSpectrum (R ⧸ P)) :=
      { length := s.length
        toFun := fun i =>
          ⟨(s i).asIdeal.map (Ideal.Quotient.mk P),
            Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
              (by
                rw [Ideal.mk_ker]
                exact hPle.trans (s.monotone (Fin.zero_le i)))⟩
        step := fun i => by
          change (s i.castSucc).asIdeal.map (Ideal.Quotient.mk P) <
            (s i.succ).asIdeal.map (Ideal.Quotient.mk P)
          have hlt : (s i.castSucc).asIdeal < (s i.succ).asIdeal := s.step i
          have hker1 : RingHom.ker (Ideal.Quotient.mk P) ≤ (s i.castSucc).asIdeal := by
            rw [Ideal.mk_ker]
            exact hPle.trans (s.monotone (Fin.zero_le _))
          have hker2 : RingHom.ker (Ideal.Quotient.mk P) ≤ (s i.succ).asIdeal := by
            rw [Ideal.mk_ker]
            exact hPle.trans (s.monotone (Fin.zero_le _))
          refine (Ideal.map_mono hlt.le).lt_of_not_ge fun hge => hlt.not_ge ?_
          have hc := Ideal.comap_mono (f := Ideal.Quotient.mk P) hge
          rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
            Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
            ← RingHom.ker_eq_comap_bot, sup_eq_left.mpr hker1, sup_eq_left.mpr hker2] at hc
          exact hc }
    have hle_dim : (t.length : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P) :=
      le_iSup (fun l : LTSeries (PrimeSpectrum (R ⧸ P)) => (l.length : WithBot ℕ∞)) t
    have hsn : s.length = n := by exact_mod_cast hlen
    have htn : (t.length : WithBot ℕ∞) = (n : WithBot ℕ∞) := by
      change ((s.length : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞)
      rw [hsn]
    rwa [htn] at hle_dim

private lemma exists_sop_dim_one
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : ringKrullDim R = 1) :
    ∃ x : R, IsSystemOfParameters R [x] ∧ ∀ P ∈ minimalPrimes R, x ∉ P := by
  have hmax_not_min : maximalIdeal R ∉ (⊥ : Ideal R).minimalPrimes := by
    intro hmem
    have hht : (maximalIdeal R).height = 0 :=
      (Ideal.height_eq_zero_iff (I := maximalIdeal R)).mpr hmem
    have hdim := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [hht, hR] at hdim
    exact absurd hdim (by decide)
  obtain ⟨x, hxm, hxnot⟩ := exists_mem_maximalIdeal_notMem_minimalPrimes_of_height_pos ⊥ hmax_not_min
  refine ⟨x, ?_, hxnot⟩
  refine ⟨by simp [hR], ?_⟩
  rw [Ideal.ofList_singleton]
  refine le_antisymm ?_ ?_
  · exact (IsLocalRing.maximalIdeal.isMaximal R).isPrime.isRadical.radical_le_iff.mpr
      (Ideal.span_singleton_le_iff_mem _ |>.mpr hxm)
  · rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro Q ⟨hQx, hQp⟩
    have : Q.IsPrime := hQp
    obtain ⟨P, hPmin, hPQ⟩ := Ideal.exists_minimalPrimes_le (J := Q) bot_le
    have : P.IsPrime := hPmin.1.1
    have hlt : P < Q := hPQ.lt_of_ne fun heq => by
      subst heq
      exact hxnot P hPmin (hQx (Ideal.subset_span rfl))
    have hQle : Q ≤ maximalIdeal R := le_maximalIdeal hQp.ne_top
    by_contra hne
    have hQlt : Q < maximalIdeal R := hQle.lt_of_not_ge hne
    let s : LTSeries (PrimeSpectrum R) :=
      { length := 2
        toFun := ![⟨P, hPmin.1.1⟩, ⟨Q, hQp⟩, ⟨maximalIdeal R, (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩]
        step := fun i => by fin_cases i <;> assumption }
    have h2 : (2 : WithBot ℕ∞) ≤ ringKrullDim R :=
      le_iSup (fun l : LTSeries (PrimeSpectrum R) => (l.length : WithBot ℕ∞)) s
    rw [hR] at h2
    exact absurd h2 (by decide)

private lemma exists_isSmallCohenMacaulay_dim_one
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : ringKrullDim R = 1) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M), IsSmallCohenMacaulay R M := by
  obtain ⟨x, hsop, hxnot⟩ := exists_sop_dim_one hR
  obtain ⟨P, hPmin, -⟩ := exists_ltSeries_of_ringKrullDim_eq hR
  have : P.IsPrime := hPmin.1.1
  have : IsDomain (R ⧸ P) := Ideal.Quotient.isDomain P
  have : Module.Finite R (R ⧸ P) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R P).toLinearMap Ideal.Quotient.mk_surjective
  refine ⟨R ⧸ P, inferInstance, inferInstance, inferInstance, [x], hsop, ?_⟩
  rw [RingTheory.Sequence.isRegular_cons_iff]
  refine ⟨?_, ?_⟩
  · intro a b hab
    have hne : Ideal.Quotient.mk P x ≠ 0 := by
      intro h0
      exact hxnot P hPmin (Ideal.Quotient.eq_zero_iff_mem.mp h0)
    change Ideal.Quotient.mk P x * a = Ideal.Quotient.mk P x * b at hab
    exact mul_left_cancel₀ hne hab
  · have hnt : Nontrivial (QuotSMulTop x (R ⧸ P)) := by
      rw [Submodule.Quotient.nontrivial_iff]
      intro htop
      have h1 : (1 : R ⧸ P) ∈ _ := htop.symm ▸ (Submodule.mem_top : (1 : R ⧸ P) ∈ ⊤)
      rw [Submodule.mem_smul_pointwise_iff_exists] at h1
      obtain ⟨u, -, hu⟩ := h1
      have hxm : x ∈ maximalIdeal R := hsop.mem_maximalIdeal (by simp)
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective u
      have hsub : 1 - x * r ∈ P := by
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, map_mul]
        exact sub_eq_zero.mpr hu.symm
      have h1m : (1 : R) ∈ maximalIdeal R := by
        have hP : P ≤ maximalIdeal R := le_maximalIdeal hPmin.1.1.ne_top
        have hadd := (maximalIdeal R).add_mem (hP hsub) ((maximalIdeal R).mul_mem_right r hxm)
        simp at hadd
      exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top
        (Ideal.eq_top_of_isUnit_mem _ h1m isUnit_one)
    exact RingTheory.Sequence.IsRegular.nil R (QuotSMulTop x (R ⧸ P))

private lemma exists_sop_of_not_mem_minimalPrimes_dim_two
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : ringKrullDim R = 2) {x : R} (hxm : x ∈ maximalIdeal R)
    (hx_dim : ∀ Q : Ideal R, Q.IsPrime → x ∈ Q → Q ≠ maximalIdeal R →
      ∀ Q' : Ideal R, Q'.IsPrime → Q < Q' → Q' = maximalIdeal R) :
    ∃ y : R, IsSystemOfParameters R [x, y] := by
  have hmax_not_min : maximalIdeal R ∉ (Ideal.span {x}).minimalPrimes := by
    intro hmem
    have hht : (maximalIdeal R).height ≤ 1 :=
      Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {x}) (maximalIdeal R) hmem
    have hdim := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [hR] at hdim
    have h2 : (2 : ℕ∞) ≤ 1 := by
      have heq : (maximalIdeal R).height = 2 := WithBot.coe_injective hdim
      rw [← heq]
      exact hht
    exact absurd h2 (by decide)
  obtain ⟨y, hym, hynot⟩ :=
    exists_mem_maximalIdeal_notMem_minimalPrimes_of_height_pos (Ideal.span {x}) hmax_not_min
  refine ⟨y, ⟨by simp [hR], ?_⟩⟩
  refine le_antisymm ?_ ?_
  · refine (IsLocalRing.maximalIdeal.isMaximal R).isPrime.isRadical.radical_le_iff.mpr ?_
    rw [Ideal.ofList_cons, Ideal.ofList_singleton]
    exact sup_le (Ideal.span_singleton_le_iff_mem _ |>.mpr hxm)
      (Ideal.span_singleton_le_iff_mem _ |>.mpr hym)
  · rw [Ideal.radical_eq_sInf, le_sInf_iff]
    rintro Q ⟨hQxy, hQp⟩
    have hQx : Ideal.span {x} ≤ Q := by
      refine le_trans ?_ hQxy
      rw [Ideal.ofList_cons]
      exact le_sup_left
    have hQy : y ∈ Q := hQxy (by rw [Ideal.ofList_cons, Ideal.ofList_singleton]; exact Ideal.mem_sup_right (Ideal.subset_span rfl))
    obtain ⟨P, hPmin, hPQ⟩ := Ideal.exists_minimalPrimes_le (J := Q) hQx
    have hPne : P ≠ maximalIdeal R := fun heq => hmax_not_min (heq ▸ hPmin)
    have hlt : P < Q := hPQ.lt_of_ne fun heq => by
      subst heq
      exact hynot P hPmin hQy
    have hPx : x ∈ P := hPmin.1.2 (Ideal.subset_span rfl)
    exact (hx_dim P hPmin.1.1 hPx hPne Q hQp hlt).ge

private lemma exists_sop_dim_two
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (hR : ringKrullDim R = 2) :
    ∃ x y : R, IsSystemOfParameters R [x, y] := by
  have hmax_not_min : maximalIdeal R ∉ (⊥ : Ideal R).minimalPrimes := by
    intro hmem
    have hht : (maximalIdeal R).height = 0 :=
      (Ideal.height_eq_zero_iff (I := maximalIdeal R)).mpr hmem
    have hdim := IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)
    rw [hht, hR] at hdim
    exact absurd hdim (by decide)
  obtain ⟨x, hxm, hxnot⟩ :=
    exists_mem_maximalIdeal_notMem_minimalPrimes_of_height_pos ⊥ hmax_not_min
  obtain ⟨y, hy⟩ := exists_sop_of_not_mem_minimalPrimes_dim_two hR hxm (fun Q hQp hQx _ Q' hQ'p hQQ' => by
    obtain ⟨P, hPmin, hPQ⟩ := Ideal.exists_minimalPrimes_le (J := Q) bot_le
    have hPQ_lt : P < Q := hPQ.lt_of_ne fun heq => by
      subst heq
      exact hxnot P hPmin hQx
    by_contra hne
    have hQ'lt : Q' < maximalIdeal R := (le_maximalIdeal hQ'p.ne_top).lt_of_ne hne
    let s : LTSeries (PrimeSpectrum R) :=
      { length := 3
        toFun := ![⟨P, hPmin.1.1⟩, ⟨Q, hQp⟩, ⟨Q', hQ'p⟩,
          ⟨maximalIdeal R, (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩]
        step := fun i => by fin_cases i <;> assumption }
    have h3 : (3 : WithBot ℕ∞) ≤ ringKrullDim R :=
      le_iSup (fun l : LTSeries (PrimeSpectrum R) => (l.length : WithBot ℕ∞)) s
    rw [hR] at h3
    exact absurd h3 (by decide))
  exact ⟨x, y, hy⟩

/-!
Part 2: Small Cohen-Macaulay Module Hom_A(D, A) from a Finite Regular Subalgebra
-/

private lemma exists_dual_module
    {R D A : Type u} [CommRing R] [CommRing D] [CommRing A] [Algebra A D] (q : R →+* D) :
    ∃ (m : Module R (D →ₗ[A] A)),
      ∀ (r : R) (φ : D →ₗ[A] A) (d : D),
        (@SMul.smul R (D →ₗ[A] A) m.toSMul r φ) d = φ (q r * d) := by
  refine ⟨{
    smul := fun r φ => φ.comp (LinearMap.mulLeft A (q r))
    one_smul := fun φ => by ext d; change φ (q 1 * d) = φ d; rw [map_one, one_mul]
    mul_smul := fun r s φ => by
      ext d
      change φ (q (r * s) * d) = φ (q s * (q r * d))
      congr 1
      rw [map_mul]
      ring
    smul_zero := fun r => by ext d; rfl
    smul_add := fun r φ ψ => by ext d; rfl
    add_smul := fun r s φ => by
      ext d
      change φ (q (r + s) * d) = φ (q r * d) + φ (q s * d)
      rw [map_add, add_mul, map_add]
    zero_smul := fun φ => by
      ext d
      change φ (q 0 * d) = 0
      rw [map_zero, zero_mul, map_zero] }, fun _ _ _ => rfl⟩

private lemma exists_isSmallCohenMacaulay_of_finite_regular
    {R D A : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [CommRing D] [IsDomain D] [CommRing A] [IsNoetherianRing A] [IsDomain A]
    [Algebra A D] [Module.Finite A D]
    (q : R →+* D) (hq_surj : Function.Surjective q)
    (hinj : Function.Injective (algebraMap A D))
    {x y : R} (hsop : IsSystemOfParameters R [x, y])
    {a₁ a₂ : A} (ha₁ : algebraMap A D a₁ = q x) (ha₂ : algebraMap A D a₂ = q y)
    (ha₁_ne : a₁ ≠ 0)
    (hreg : ∀ u v : A, a₂ * u = a₁ * v → ∃ w : A, a₁ * w = u) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M), IsSmallCohenMacaulay R M := by
  obtain ⟨mR, hsmul0⟩ := exists_dual_module (A := A) q
  let _ : Module R (D →ₗ[A] A) := mR
  have hsmul : ∀ (r : R) (φ : D →ₗ[A] A) (d : D), (r • φ) d = φ (q r * d) := hsmul0
  have hfinA : Module.Finite A (D →ₗ[A] A) := by
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin (R := A) (M := D)
    let g : (D →ₗ[A] A) →ₗ[A] (Fin n → A) :=
      { toFun := fun φ i => φ (f i)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hg : Function.Injective g := by
      intro φ ψ h
      ext d
      have hmem : d ∈ Submodule.span A (Set.range f) := hf ▸ Submodule.mem_top
      refine Submodule.span_induction (fun z hz => ?_) (by simp) (fun _ _ _ _ h1 h2 => by simp [h1, h2])
        (fun a _ _ h1 => by simp [h1]) hmem
      rcases hz with ⟨i, rfl⟩
      exact congrFun h i
    exact Module.Finite.of_injective g hg
  have hfinR : Module.Finite R (D →ₗ[A] A) := by
    obtain ⟨S, hS⟩ := hfinA
    refine ⟨S, eq_top_iff.mpr fun φ _ => ?_⟩
    have hmem : φ ∈ Submodule.span A (S : Set (D →ₗ[A] A)) := hS ▸ Submodule.mem_top
    refine Submodule.span_induction (fun z hz => Submodule.subset_span hz)
      (Submodule.zero_mem _) (fun _ _ _ _ h1 h2 => Submodule.add_mem _ h1 h2)
      (fun a z _ hz => ?_) hmem
    obtain ⟨r, hr⟩ := hq_surj (algebraMap A D a)
    have hsm : a • z = r • z := by
      ext d
      rw [LinearMap.smul_apply, hsmul, hr, ← Algebra.smul_def, map_smul, smul_eq_mul]
    rw [hsm]
    exact Submodule.smul_mem _ r hz
  have hnt : Nontrivial (D →ₗ[A] A) := by
    classical
    let K := FractionRing A
    let L := FractionRing D
    have hnz : ∀ y : nonZeroDivisors A, IsUnit (algebraMap A L y.1) := by
      intro y
      have ha0 : y.1 ≠ 0 := nonZeroDivisors.ne_zero y.2
      have hda : algebraMap A D y.1 ≠ 0 := fun h => ha0 (hinj (h.trans (map_zero _).symm))
      have hla : algebraMap A L y.1 ≠ 0 := by
        rw [IsScalarTower.algebraMap_apply A D L]
        intro h0
        exact hda (IsFractionRing.injective D L (h0.trans (map_zero _).symm))
      exact isUnit_iff_ne_zero.mpr hla
    let ι : K →+* L := IsLocalization.lift hnz
    let _ : Algebra K L := ι.toAlgebra
    have hcomm : ∀ a : A, ι (algebraMap A K a) = algebraMap A L a :=
      fun a => IsLocalization.lift_eq hnz a
    have : IsScalarTower A K L := IsScalarTower.of_algebraMap_eq fun a => (hcomm a).symm
    have h1ne : (1 : L) ≠ 0 := one_ne_zero
    let bL := Module.Basis.ofVectorSpace K L
    have h1repr : bL.repr (1 : L) ≠ 0 := fun h => h1ne (bL.repr.injective (h.trans (map_zero _).symm))
    obtain ⟨i0, hi0⟩ := Finsupp.ne_iff.mp h1repr
    let lamL : L →ₗ[K] K := (bL.repr 1 i0)⁻¹ • bL.coord i0
    have hlam1 : lamL 1 = 1 := by
      simp [lamL, Module.Basis.coord_apply, inv_mul_cancel₀ hi0]
    obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin (R := A) (M := D)
    have hclear : ∀ i : Fin n, ∃ s : A, s ≠ 0 ∧ ∃ b : A,
        algebraMap A K b = algebraMap A K s * lamL (algebraMap D L (f i)) := by
      intro i
      obtain ⟨⟨b, s⟩, hs⟩ := IsLocalization.mk'_surjective (nonZeroDivisors A) (lamL (algebraMap D L (f i)))
      refine ⟨s.1, nonZeroDivisors.ne_zero s.2, b, ?_⟩
      rw [← hs, IsLocalization.mul_mk'_eq_mk'_of_mul]
      exact (IsLocalization.mk'_mul_cancel_left (M := nonZeroDivisors A) b s).symm
    choose s hs0 b hb using hclear
    let Sprod : A := ∏ i : Fin n, s i
    have hS0 : Sprod ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hs0 i
    have hmemA : ∀ d : D, ∃ c : A, algebraMap A K c = algebraMap A K Sprod * lamL (algebraMap D L d) := by
      intro d
      have hmem : d ∈ Submodule.span A (Set.range f) := hf ▸ Submodule.mem_top
      refine Submodule.span_induction (fun z hz => ?_)
        ⟨0, by simp⟩
        (fun u v _ _ ⟨cu, hcu⟩ ⟨cv, hcv⟩ => ⟨cu + cv, by rw [map_add, map_add, map_add, mul_add, hcu, hcv]⟩)
        (fun a u _ ⟨cu, hcu⟩ => ⟨a * cu, by
          rw [map_mul, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply A D L,
            ← Algebra.smul_def (R := A) (A := L),
            ← algebraMap_smul K a, map_smul, smul_eq_mul, hcu]
          ring⟩) hmem
      rcases hz with ⟨i, rfl⟩
      let rest : A := ∏ j ∈ Finset.univ.erase i, s j
      have hS_eq : Sprod = rest * s i := by
        dsimp only [Sprod, rest]
        rw [mul_comm, Finset.mul_prod_erase Finset.univ s (Finset.mem_univ i)]
      refine ⟨rest * b i, ?_⟩
      rw [map_mul, hb i, hS_eq, map_mul, mul_assoc]
    choose φfun hφ using hmemA
    let φ : D →ₗ[A] A :=
      { toFun := φfun
        map_add' := fun u v => IsFractionRing.injective A K <| by
          rw [map_add, hφ (u + v), hφ u, hφ v, map_add, map_add, mul_add]
        map_smul' := fun a u => IsFractionRing.injective A K <| by
          simp only [RingHom.id_apply, smul_eq_mul, map_mul, hφ (a • u), hφ u]
          rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply A D L,
            ← Algebra.smul_def (R := A) (A := L),
            ← algebraMap_smul K a, map_smul, smul_eq_mul]
          ring }
    have hφ1 : φ 1 = Sprod := IsFractionRing.injective A K <| by
      change algebraMap A K (φfun 1) = algebraMap A K Sprod
      rw [hφ 1, map_one, hlam1, mul_one]
    have hφne : φ ≠ 0 := fun h0 => hS0 (by rw [← hφ1, h0]; rfl)
    exact ⟨⟨φ, 0, hφne⟩⟩
  refine ⟨D →ₗ[A] A, inferInstance, mR, hfinR, [x, y], hsop, ?_⟩
  have hreg1 : IsSMulRegular (D →ₗ[A] A) x := by
    intro φ ψ h
    ext d
    have hd : (x • φ) d = (x • ψ) d := congrFun (congrArg DFunLike.coe h) d
    rw [hsmul, hsmul, ← ha₁, ← Algebra.smul_def, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hd
    exact mul_left_cancel₀ ha₁_ne hd
  have hreg2 : IsSMulRegular (QuotSMulTop x (D →ₗ[A] A)) y := by
    classical
    intro a b hab
    obtain ⟨φ, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    obtain ⟨ψ, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    rw [← sub_eq_zero] at hab
    have hab' : (Submodule.Quotient.mk (y • (φ - ψ)) : QuotSMulTop x (D →ₗ[A] A)) = 0 := by
      simpa [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, smul_sub] using hab
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hab'
    rw [Submodule.mem_smul_pointwise_iff_exists]
    obtain ⟨χ, -, hχ⟩ := hab'
    have hdiv : ∀ d : D, ∃ w : A, a₁ * w = (φ - ψ) d := fun d => by
      have hd := congrFun (congrArg DFunLike.coe hχ) d
      rw [hsmul, hsmul, ← ha₁, ← ha₂, ← Algebra.smul_def, ← Algebra.smul_def,
        map_smul, map_smul, smul_eq_mul, smul_eq_mul] at hd
      exact hreg ((φ - ψ) d) (χ d) hd.symm
    choose θfun hθ using hdiv
    let θ : D →ₗ[A] A :=
      { toFun := θfun
        map_add' := fun u v => mul_left_cancel₀ ha₁_ne <| by
          rw [mul_add, hθ (u + v), hθ u, hθ v, map_add]
        map_smul' := fun a u => mul_left_cancel₀ ha₁_ne <| by
          simp only [RingHom.id_apply, smul_eq_mul, hθ (a • u), map_smul]
          rw [← hθ u]
          ring }
    refine ⟨θ, Submodule.mem_top, ?_⟩
    ext d
    rw [hsmul, ← ha₁, ← Algebra.smul_def, map_smul, smul_eq_mul]
    exact hθ d
  have hweak : RingTheory.Sequence.IsWeaklyRegular (D →ₗ[A] A) [x, y] := by
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff, RingTheory.Sequence.isWeaklyRegular_cons_iff]
    exact ⟨hreg1, hreg2, ⟨fun i hi => absurd hi (by simp)⟩⟩
  refine ⟨hweak, ?_⟩
  intro htop
  have hleI : Ideal.ofList [x, y] ≤ maximalIdeal R := by
    rw [Ideal.ofList_cons, Ideal.ofList_singleton]
    exact sup_le
      (Ideal.span_singleton_le_iff_mem _ |>.mpr (hsop.mem_maximalIdeal (by simp)))
      (Ideal.span_singleton_le_iff_mem _ |>.mpr (hsop.mem_maximalIdeal (by simp)))
  have hle : (⊤ : Submodule R (D →ₗ[A] A)) ≤ maximalIdeal R • (⊤ : Submodule R (D →ₗ[A] A)) := by
    conv_lhs => rw [htop]
    exact Submodule.smul_le.mpr fun r hr m _ => Submodule.smul_mem_smul (hleI hr) Submodule.mem_top
  have hbot : (⊤ : Submodule R (D →ₗ[A] A)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (maximalIdeal R) ⊤
      Module.Finite.fg_top hle (IsLocalRing.maximalIdeal_le_jacobson _)
  have hsub : Subsingleton (D →ₗ[A] A) := (Submodule.subsingleton_iff R).mp (subsingleton_of_bot_eq_top hbot.symm)
  exact not_subsingleton (D →ₗ[A] A) hsub

/-!
Part 3: Power Series Evaluation, Complete Nakayama, and Reduction to a Complete DVR Map
-/

private noncomputable def evalPSMod {S D : Type u} [CommRing S] [CommRing D]
    (I : Ideal D) (f : S →+* D) (y : D) (hy : y ∈ I) (n : ℕ) :
    PowerSeries S →+* D ⧸ I ^ n where
  toFun F := ∑ k ∈ Finset.range n, Ideal.Quotient.mk (I ^ n) (f (PowerSeries.coeff k F) * y ^ k)
  map_one' := by
    cases n with
    | zero =>
      have : Subsingleton (D ⧸ I ^ 0) := by simp
      exact Subsingleton.elim _ _
    | succ m =>
      rw [Finset.sum_range_succ']
      have h0 : ∑ k ∈ Finset.range m,
          Ideal.Quotient.mk (I ^ (m + 1)) (f (PowerSeries.coeff (k + 1) (1 : PowerSeries S)) * y ^ (k + 1)) = 0 := by
        refine Finset.sum_eq_zero fun k _ => ?_
        simp [PowerSeries.coeff_one]
      rw [h0, zero_add]
      simp [PowerSeries.coeff_one]
  map_mul' F G := by
    have hmul :
        (∑ i ∈ Finset.range n, Ideal.Quotient.mk (I ^ n) (f (PowerSeries.coeff i F) * y ^ i)) *
          (∑ j ∈ Finset.range n, Ideal.Quotient.mk (I ^ n) (f (PowerSeries.coeff j G) * y ^ j)) =
        ∑ k ∈ Finset.range n,
          ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
            Ideal.Quotient.mk (I ^ n) (f (PowerSeries.coeff p.1 F) * f (PowerSeries.coeff p.2 G) * y ^ k) := by
      rw [Finset.sum_mul_sum]
      have hpair :
          ∑ p ∈ Finset.range n ×ˢ Finset.range n,
            Ideal.Quotient.mk (I ^ n) (f (PowerSeries.coeff p.1 F) * y ^ p.1) *
              Ideal.Quotient.mk (I ^ n) (f (PowerSeries.coeff p.2 G) * y ^ p.2) =
          ∑ p ∈ (Finset.range n ×ˢ Finset.range n).filter (fun p => p.1 + p.2 < n),
            Ideal.Quotient.mk (I ^ n) (f (PowerSeries.coeff p.1 F) * f (PowerSeries.coeff p.2 G) * y ^ (p.1 + p.2)) := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [← map_mul]
        have hrew : f (PowerSeries.coeff p.1 F) * y ^ p.1 * (f (PowerSeries.coeff p.2 G) * y ^ p.2) =
            f (PowerSeries.coeff p.1 F) * f (PowerSeries.coeff p.2 G) * y ^ (p.1 + p.2) := by
          rw [pow_add]; ring
        rw [hrew]
        split_ifs with hlt
        · rfl
        · rw [Ideal.Quotient.eq_zero_iff_mem]
          have hge : n ≤ p.1 + p.2 := Nat.le_of_not_lt hlt
          exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hge (Ideal.pow_mem_pow hy _))
      rw [← Finset.sum_product', hpair]
      symm
      refine Finset.sum_sigma' (Finset.range n) (fun k => Finset.HasAntidiagonal.antidiagonal k) _ |>.trans ?_
      refine Finset.sum_bij (fun x _ => x.2) ?_ ?_ ?_ ?_
      · intro ⟨k, p⟩ hx
        simp only [Finset.mem_sigma, Finset.mem_range, Finset.HasAntidiagonal.mem_antidiagonal] at hx
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
        exact ⟨⟨by omega, by omega⟩, by omega⟩
      · intro ⟨k₁, p₁⟩ hx₁ ⟨k₂, p₂⟩ hx₂ h
        simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at hx₁ hx₂
        dsimp only at h
        subst h
        have hk : k₁ = k₂ := by rw [← hx₁.2, hx₂.2]
        subst hk
        rfl
      · intro p hp
        simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp
        exact ⟨⟨p.1 + p.2, p⟩, by simp [Finset.HasAntidiagonal.mem_antidiagonal, hp.2], rfl⟩
      · intro ⟨k, p⟩ hx
        simp only [Finset.mem_sigma, Finset.HasAntidiagonal.mem_antidiagonal] at hx
        rw [hx.2]
    rw [hmul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [PowerSeries.coeff_mul, map_sum, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [map_mul f]
  map_zero' := by simp
  map_add' F G := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, map_add, add_mul, map_add]

private lemma evalPSMod_compat {S D : Type u} [CommRing S] [CommRing D]
    (I : Ideal D) (f : S →+* D) (y : D) (hy : y ∈ I) {m n : ℕ} (hle : m ≤ n) :
    (Ideal.Quotient.factorPow I hle).comp (evalPSMod I f y hy n) = evalPSMod I f y hy m := by
  ext F
  simp only [RingHom.comp_apply, evalPSMod, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
    map_sum]
  have hterm : ∀ k, Ideal.Quotient.factorPow I hle
      (Ideal.Quotient.mk (I ^ n) (f (PowerSeries.coeff k F) * y ^ k)) =
      Ideal.Quotient.mk (I ^ m) (f (PowerSeries.coeff k F) * y ^ k) := fun _ => rfl
  simp only [hterm]
  symm
  refine Finset.sum_subset (Finset.range_mono hle) fun k hk hkm => ?_
  rw [Finset.mem_range] at hkm
  have hge : m ≤ k := Nat.le_of_not_lt hkm
  rw [Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hge (Ideal.pow_mem_pow hy _))

private noncomputable def evalPS {S D : Type u} [CommRing S] [CommRing D]
    (I : Ideal D) [IsAdicComplete I D] (f : S →+* D) (y : D) (hy : y ∈ I) :
    PowerSeries S →+* D :=
  IsAdicComplete.liftRingHom I (evalPSMod I f y hy) (evalPSMod_compat I f y hy)

private lemma evalPS_C {S D : Type u} [CommRing S] [CommRing D]
    (I : Ideal D) [IsAdicComplete I D] (f : S →+* D) (y : D) (hy : y ∈ I) (s : S) :
    evalPS I f y hy (PowerSeries.C s) = f s := by
  refine sub_eq_zero.mp (IsHausdorff.haus' (I := I) _ fun n => ?_)
  rw [SModEq.zero, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, ← Ideal.Quotient.eq_zero_iff_mem,
    map_sub, sub_eq_zero]
  rw [evalPS, IsAdicComplete.mk_liftRingHom]
  cases n with
  | zero =>
    have : Subsingleton (D ⧸ I ^ 0) := by simp
    exact Subsingleton.elim _ _
  | succ m =>
    dsimp only [evalPSMod, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
    rw [Finset.sum_range_succ']
    have h0 : ∑ k ∈ Finset.range m,
        Ideal.Quotient.mk (I ^ (m + 1)) (f (PowerSeries.coeff (k + 1) (PowerSeries.C s)) * y ^ (k + 1)) = 0 := by
      refine Finset.sum_eq_zero fun k _ => ?_
      simp
    rw [h0, zero_add]
    simp [PowerSeries.coeff_C]

private lemma evalPS_X {S D : Type u} [CommRing S] [CommRing D]
    (I : Ideal D) [IsAdicComplete I D] (f : S →+* D) (y : D) (hy : y ∈ I) :
    evalPS I f y hy PowerSeries.X = y := by
  refine sub_eq_zero.mp (IsHausdorff.haus' (I := I) _ fun n => ?_)
  rw [SModEq.zero, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, ← Ideal.Quotient.eq_zero_iff_mem,
    map_sub, sub_eq_zero]
  rw [evalPS, IsAdicComplete.mk_liftRingHom]
  cases n with
  | zero =>
    have : Subsingleton (D ⧸ I ^ 0) := by simp
    exact Subsingleton.elim _ _
  | succ m =>
    cases m with
    | zero =>
      dsimp only [evalPSMod, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      rw [Finset.sum_range_one]
      simp only [PowerSeries.coeff_zero_X, map_zero, zero_mul, map_zero]
      symm
      rw [Ideal.Quotient.eq_zero_iff_mem, pow_one]
      exact hy
    | succ k =>
      dsimp only [evalPSMod, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      rw [Finset.sum_range_succ', Finset.sum_range_succ']
      have h0 : ∑ j ∈ Finset.range k,
          Ideal.Quotient.mk (I ^ (k + 2)) (f (PowerSeries.coeff (j + 2) (PowerSeries.X : PowerSeries S)) * y ^ (j + 2)) = 0 := by
        refine Finset.sum_eq_zero fun j _ => ?_
        simp [PowerSeries.coeff_X]
      rw [h0, zero_add]
      simp [PowerSeries.coeff_X]

private lemma powerSeries_isLocalRing_of_dvr
    {S : Type u} [CommRing S] [IsLocalRing S] :
    IsLocalRing (PowerSeries S) := by
  refine IsLocalRing.of_nonunits_add fun {F G} hF hG hFG => ?_
  rw [mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff, ← mem_nonunits_iff,
    ← IsLocalRing.mem_maximalIdeal] at hF hG
  rw [PowerSeries.isUnit_iff_constantCoeff] at hFG
  have hsum : PowerSeries.constantCoeff (F + G) ∈ maximalIdeal S := by
    rw [map_add]
    exact (maximalIdeal S).add_mem hF hG
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hsum
  exact hsum hFG

private lemma powerSeries_maximalIdeal_eq
    {S : Type u} [CommRing S] [IsLocalRing S] {π : S} (hπ : maximalIdeal S = Ideal.span {π}) :
    letI : IsLocalRing (PowerSeries S) := powerSeries_isLocalRing_of_dvr
    maximalIdeal (PowerSeries S) = Ideal.span {PowerSeries.C π, PowerSeries.X} := by
  let _ : IsLocalRing (PowerSeries S) := powerSeries_isLocalRing_of_dvr
  refine le_antisymm ?_ ?_
  · intro F hF
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
      ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, hπ, Ideal.mem_span_singleton] at hF
    obtain ⟨c, hc⟩ := hF
    let G : PowerSeries S := PowerSeries.mk fun n => PowerSeries.coeff (n + 1) F
    have hEq : F = PowerSeries.C c * PowerSeries.C π + PowerSeries.X * G := by
      ext n
      cases n with
      | zero =>
        simp [G, PowerSeries.coeff_zero_eq_constantCoeff, hc, mul_comm]
      | succ k =>
        simp [G, PowerSeries.coeff_succ_X_mul]
    rw [hEq]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Or.inl rfl)))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (Or.inr rfl)))
  · rw [Ideal.span_le]
    intro F hF
    rcases hF with rfl | rfl
    · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_C,
        ← mem_nonunits_iff, ← IsLocalRing.mem_maximalIdeal, hπ]
      exact Ideal.subset_span rfl
    · rw [SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
      exact not_isUnit_zero

private lemma powerSeries_ringKrullDim_le_two
    {S : Type u} [CommRing S] [IsNoetherianRing S] [IsLocalRing S]
    {π : S} (hπ : maximalIdeal S = Ideal.span {π}) :
    ringKrullDim (PowerSeries S) ≤ 2 := by
  classical
  let _ : IsLocalRing (PowerSeries S) := powerSeries_isLocalRing_of_dvr
  have hmax : maximalIdeal (PowerSeries S) = Ideal.span ({PowerSeries.C π, PowerSeries.X} : Finset (PowerSeries S)) := by
    rw [powerSeries_maximalIdeal_eq hπ]
    simp
  have hmem : maximalIdeal (PowerSeries S) ∈
      (Ideal.span ({PowerSeries.C π, PowerSeries.X} : Finset (PowerSeries S))).minimalPrimes := by
    rw [← hmax]
    exact ⟨⟨(IsLocalRing.maximalIdeal.isMaximal _).isPrime, le_rfl⟩, fun _ hQ _ => hQ.2⟩
  have hht := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmem
  have hcard : ({PowerSeries.C π, PowerSeries.X} : Finset (PowerSeries S)).card ≤ 2 :=
    Finset.card_le_two
  have hht2 : (maximalIdeal (PowerSeries S)).height ≤ 2 :=
    hht.trans (by exact_mod_cast hcard)
  rw [← IsLocalRing.maximalIdeal_height_eq_ringKrullDim]
  exact WithBot.coe_le_coe.mpr hht2

private lemma powerSeries_weaklyRegular_C_X
    {S : Type u} [CommRing S] {π : S}
    (F G : PowerSeries S) (h : PowerSeries.X * F = PowerSeries.C π * G) :
    ∃ H : PowerSeries S, PowerSeries.C π * H = F := by
  refine ⟨PowerSeries.mk fun n => PowerSeries.coeff (n + 1) G, ?_⟩
  ext n
  have hn := congrArg (PowerSeries.coeff (n + 1)) h
  rw [PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_C_mul] at hn
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]
  exact hn.symm

private lemma exists_fin_gen_quot_pow_le
    {S D : Type u} [CommRing S] [CommRing D] [IsNoetherianRing D] [IsLocalRing D]
    (f : S →+* D) (hf_res : ∀ d : D, ∃ s : S, d - f s ∈ maximalIdeal D) :
    ∀ (k : ℕ) (J : Ideal D), maximalIdeal D ^ k ≤ J →
      ∃ (m : ℕ) (e : Fin m → D), ∀ d : D, ∃ (c : Fin m → S), d - ∑ i, f (c i) * e i ∈ J := by
  intro k
  induction k with
  | zero =>
    intro J hJ
    refine ⟨0, Fin.elim0, fun d => ⟨Fin.elim0, ?_⟩⟩
    have htop : J = ⊤ := top_le_iff.mp (by simpa using hJ)
    rw [htop]
    exact Submodule.mem_top
  | succ k ih =>
    intro J hJ
    obtain ⟨m, e, he⟩ := ih (J ⊔ maximalIdeal D ^ k) le_sup_right
    have hfg : (maximalIdeal D ^ k).FG := IsNoetherian.noetherian _
    obtain ⟨t, ht⟩ := hfg
    let g : Fin t.card → D := fun j => (t.equivFin.symm j).1
    have hspan : Submodule.span D (Set.range g) = maximalIdeal D ^ k := by
      rw [← ht]
      congr 1
      ext x
      simp only [Set.mem_range, Finset.mem_coe, g]
      constructor
      · rintro ⟨j, rfl⟩; exact (t.equivFin.symm j).2
      · intro hx; exact ⟨t.equivFin ⟨x, hx⟩, by simp⟩
    let E : Fin (m + t.card) → D := Fin.append e g
    refine ⟨m + t.card, E, fun d => ?_⟩
    obtain ⟨c, hc⟩ := he d
    rw [Submodule.mem_sup] at hc
    obtain ⟨j₀, hj₀, z, hz, hcz⟩ := hc
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun D] at hz
    obtain ⟨a, ha⟩ := hz
    have hlift : ∀ j : Fin t.card, ∃ s : S, a j - f s ∈ maximalIdeal D := fun j => hf_res (a j)
    choose b hb using hlift
    refine ⟨Fin.append c b, ?_⟩
    have hsum : ∑ i : Fin (m + t.card), f (Fin.append c b i) * E i =
        (∑ i : Fin m, f (c i) * e i) + ∑ j : Fin t.card, f (b j) * g j := by
      rw [Fin.sum_univ_add]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        simp [E, Fin.append_left]
      · refine Finset.sum_congr rfl fun j _ => ?_
        simp [E, Fin.append_right]
    rw [hsum]
    have hdiff : d - ((∑ i : Fin m, f (c i) * e i) + ∑ j : Fin t.card, f (b j) * g j) =
        j₀ + ∑ j : Fin t.card, (a j - f (b j)) * g j := by
      have h1 : d - ∑ i : Fin m, f (c i) * e i = j₀ + z := hcz.symm
      have h2 : z = ∑ j : Fin t.card, a j * g j := by
        simpa [smul_eq_mul] using ha.symm
      calc
        d - ((∑ i : Fin m, f (c i) * e i) + ∑ j : Fin t.card, f (b j) * g j)
            = (d - ∑ i : Fin m, f (c i) * e i) - ∑ j : Fin t.card, f (b j) * g j := by ring
        _ = j₀ + (∑ j : Fin t.card, a j * g j - ∑ j : Fin t.card, f (b j) * g j) := by
              rw [h1, h2]; ring
        _ = j₀ + ∑ j : Fin t.card, (a j - f (b j)) * g j := by
              congr 1
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl fun j _ => by ring
    rw [hdiff]
    refine J.add_mem hj₀ (J.sum_mem fun j _ => ?_)
    have hgmem : g j ∈ maximalIdeal D ^ k := by
      rw [← hspan]
      exact Submodule.subset_span ⟨j, rfl⟩
    have hmul : (a j - f (b j)) * g j ∈ maximalIdeal D ^ (k + 1) := by
      rw [pow_succ']
      exact Ideal.mul_mem_mul (hb j) hgmem
    exact hJ hmul

private lemma exists_adic_series_limit
    {S : Type u} [CommRing S] {π : S} [IsAdicComplete (Ideal.span {π}) S] (a : ℕ → S) :
    ∃ g : S, ∀ K : ℕ, g - ∑ k ∈ Finset.range K, a k * π ^ k ∈ Ideal.span {π} ^ K := by
  let seq : ℕ → S := fun K => ∑ k ∈ Finset.range K, a k * π ^ k
  have hcauchy : ∀ {M N : ℕ}, M ≤ N → seq M ≡ seq N [SMOD (Ideal.span {π} ^ M • ⊤ : Ideal S)] := by
    intro M N hMN
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem, ← Ideal.neg_mem_iff, neg_sub]
    have hdiff : seq N - seq M = ∑ k ∈ Finset.Ico M N, a k * π ^ k := by
      dsimp only [seq]
      rw [← Finset.sum_range_add_sum_Ico _ hMN]
      ring
    rw [hdiff]
    refine Ideal.sum_mem _ fun k hk => ?_
    have hkM : M ≤ k := (Finset.mem_Ico.mp hk).1
    have hπk : π ^ k ∈ Ideal.span {π} ^ M :=
      Ideal.pow_le_pow_right hkM (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton π)) k)
    exact Ideal.mul_mem_left (Ideal.span {π} ^ M) (a k) hπk
  obtain ⟨g, hg⟩ := IsPrecomplete.prec' (I := Ideal.span {π}) seq (fun {M N} h => hcauchy h)
  refine ⟨g, fun K => ?_⟩
  have hK := hg K
  rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem, ← Ideal.neg_mem_iff, neg_sub] at hK
  exact hK

private lemma finite_evalPS_of_dvr_map
    {S D : Type u} [CommRing S] [IsLocalRing S]
    [CommRing D] [IsNoetherianRing D] [IsLocalRing D]
    [IsAdicComplete (maximalIdeal D) D]
    {π : S} [IsAdicComplete (Ideal.span {π}) S]
    (f : S →+* D) (hf_res : ∀ d : D, ∃ s : S, d - f s ∈ maximalIdeal D)
    {x y : D} (hfx : f π = x) (hxm : x ∈ maximalIdeal D) (hym : y ∈ maximalIdeal D)
    (hprim : ∃ r : ℕ, maximalIdeal D ^ r ≤ Ideal.span {x, y}) :
    letI : Algebra (PowerSeries S) D := (evalPS (maximalIdeal D) f y hym).toAlgebra
    Module.Finite (PowerSeries S) D := by
  classical
  let φ : PowerSeries S →+* D := evalPS (maximalIdeal D) f y hym
  let _ : Algebra (PowerSeries S) D := φ.toAlgebra
  obtain ⟨r, hr⟩ := hprim
  obtain ⟨m, e, he⟩ := exists_fin_gen_quot_pow_le f hf_res r (Ideal.span {x, y}) hr
  have hstep : ∀ d : D, ∃ (c : Fin m → S) (u v : D),
      d = (∑ i, f (c i) * e i) + x * u + y * v := by
    intro d
    obtain ⟨c, hc⟩ := he d
    rw [Ideal.mem_span_pair] at hc
    obtain ⟨u, v, huv⟩ := hc
    refine ⟨c, u, v, ?_⟩
    linear_combination -huv
  refine (Module.finite_def (R := PowerSeries S) (M := D)).mpr ⟨Finset.univ.image e, eq_top_iff.mpr fun d _ => ?_⟩
  let stepRec : (n : ℕ) → (Fin (n + 1) → D) × (Fin (n + 1) → Fin m → S) :=
    Nat.rec
      (fun _ => d, fun _ => (hstep d).choose)
      (fun n prev =>
        let rem := prev.1
        let u := fun k : Fin (n + 1) => (hstep (rem k)).choose_spec.choose
        let v := fun k : Fin (n + 1) => (hstep (rem k)).choose_spec.choose_spec.choose
        let rem' : Fin (n + 2) → D := fun j =>
          if h0 : j.1 = 0 then u ⟨0, Nat.zero_lt_succ n⟩
          else if hlast : j.1 = n + 1 then v ⟨n, Nat.lt_succ_self n⟩
          else u ⟨j.1, by omega⟩ + v ⟨j.1 - 1, by omega⟩
        (rem', fun j => (hstep (rem' j)).choose))
  let rem : (n : ℕ) → Fin (n + 1) → D := fun n => (stepRec n).1
  let coeffC : (n : ℕ) → Fin (n + 1) → Fin m → S := fun n => (stepRec n).2
  have hcoeffC : ∀ (n : ℕ) (k : Fin (n + 1)), coeffC n k = (hstep (rem n k)).choose := by
    intro n k
    cases n <;> rfl
  have hrem_spec : ∀ (n : ℕ) (k : Fin (n + 1)),
      rem n k = (∑ i, f (coeffC n k i) * e i) +
        x * (hstep (rem n k)).choose_spec.choose +
        y * (hstep (rem n k)).choose_spec.choose_spec.choose := fun n k => by
    rw [hcoeffC]
    exact (hstep (rem n k)).choose_spec.choose_spec.choose_spec
  have hrem_step : ∀ (n : ℕ),
      ∑ k : Fin (n + 1),
        (x * (hstep (rem n k)).choose_spec.choose +
          y * (hstep (rem n k)).choose_spec.choose_spec.choose) * x ^ (n - k.1) * y ^ k.1 =
      ∑ j : Fin (n + 2), rem (n + 1) j * x ^ (n + 1 - j.1) * y ^ j.1 := by
    intro n
    let u := fun k : Fin (n + 1) => (hstep (rem n k)).choose_spec.choose
    let v := fun k : Fin (n + 1) => (hstep (rem n k)).choose_spec.choose_spec.choose
    have h1 :
        ∑ k : Fin (n + 1), (x * u k + y * v k) * x ^ (n - k.1) * y ^ k.1 =
        (∑ k : Fin (n + 1), u k * x ^ (n + 1 - k.1) * y ^ k.1) +
          ∑ k : Fin (n + 1), v k * x ^ (n - k.1) * y ^ (k.1 + 1) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hpow : x * x ^ (n - k.1) = x ^ (n + 1 - k.1) := by
        rw [← pow_succ']
        congr 1
        omega
      calc
        (x * u k + y * v k) * x ^ (n - k.1) * y ^ k.1
            = u k * (x * x ^ (n - k.1)) * y ^ k.1 + v k * x ^ (n - k.1) * (y * y ^ k.1) := by ring
        _ = u k * x ^ (n + 1 - k.1) * y ^ k.1 + v k * x ^ (n - k.1) * y ^ (k.1 + 1) := by
              rw [hpow, ← pow_succ']
    rw [h1]
    have hsplit : ∀ (j : Fin (n + 2)),
        rem (n + 1) j * x ^ (n + 1 - j.1) * y ^ j.1 =
        (if hj : j.1 < n + 1 then u ⟨j.1, hj⟩ * x ^ (n + 1 - j.1) * y ^ j.1 else 0) +
        (if hj0 : 0 < j.1 then v ⟨j.1 - 1, by omega⟩ * x ^ (n + 1 - j.1) * y ^ j.1 else 0) := by
      intro j
      change (if h0 : j.1 = 0 then u ⟨0, Nat.zero_lt_succ n⟩
        else if hlast : j.1 = n + 1 then v ⟨n, Nat.lt_succ_self n⟩
        else u ⟨j.1, by omega⟩ + v ⟨j.1 - 1, by omega⟩) * x ^ (n + 1 - j.1) * y ^ j.1 = _
      split_ifs with h0 hlast hj hj0
      all_goals try omega
      · simp [h0]
      · have hj1 : j.1 - 1 = n := by omega
        have hfin : (⟨j.1 - 1, by omega⟩ : Fin (n + 1)) = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext hj1
        rw [hfin]; ring
      · ring
    rw [Finset.sum_congr rfl fun j _ => hsplit j, Finset.sum_add_distrib]
    congr 1
    · symm
      rw [Fin.sum_univ_castSucc]
      have hlast : (if hj : (Fin.last (n + 1)).1 < n + 1 then
          u ⟨(Fin.last (n + 1)).1, hj⟩ * x ^ (n + 1 - (Fin.last (n + 1)).1) * y ^ (Fin.last (n + 1)).1
        else 0) = 0 := by simp
      rw [hlast, add_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk : k.1 < n + 1 := k.2
      simp only [Fin.val_castSucc, hk, ↓reduceDIte, Fin.eta]
    · symm
      rw [Fin.sum_univ_succ]
      have hzero : (if hj0 : 0 < (0 : Fin (n + 2)).1 then
          v ⟨(0 : Fin (n + 2)).1 - 1, by omega⟩ * x ^ (n + 1 - (0 : Fin (n + 2)).1) * y ^ (0 : Fin (n + 2)).1
        else 0) = 0 := by simp
      rw [hzero, zero_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [Fin.val_succ, Nat.succ_pos, ↓reduceDIte, Nat.succ_sub_succ, Nat.sub_zero, Fin.eta]
  have hinv : ∀ N : ℕ,
      d = (∑ n ∈ Finset.range N, ∑ k : Fin (n + 1), ∑ i : Fin m,
            f (coeffC n k i) * e i * x ^ (n - k.1) * y ^ k.1) +
          ∑ j : Fin (N + 1), rem N j * x ^ (N - j.1) * y ^ j.1 := by
    intro N
    induction N with
    | zero =>
      simp [rem, stepRec]
    | succ N ih =>
      rw [Finset.sum_range_succ, add_assoc]
      rw [ih]
      congr 1
      have hsub :
          ∑ j : Fin (N + 1), rem N j * x ^ (N - j.1) * y ^ j.1 =
          (∑ k : Fin (N + 1), ∑ i : Fin m, f (coeffC N k i) * e i * x ^ (N - k.1) * y ^ k.1) +
            ∑ k : Fin (N + 1),
              (x * (hstep (rem N k)).choose_spec.choose +
                y * (hstep (rem N k)).choose_spec.choose_spec.choose) * x ^ (N - k.1) * y ^ k.1 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        conv_lhs => rw [hrem_spec N k]
        rw [add_assoc, add_mul, add_mul, Finset.sum_mul, Finset.sum_mul]
      rw [hsub, hrem_step N]
  let cAB : Fin m → ℕ → ℕ → S := fun i a b => coeffC (a + b) ⟨b, by omega⟩ i
  have hlim : ∀ (i : Fin m) (b : ℕ), ∃ g : S,
      ∀ K : ℕ, g - ∑ a ∈ Finset.range K, cAB i a b * π ^ a ∈ Ideal.span {π} ^ K :=
    fun i b => exists_adic_series_limit (fun a => cAB i a b)
  choose g hg using hlim
  let F : Fin m → PowerSeries S := fun i => PowerSeries.mk (g i)
  have hEq : d = ∑ i : Fin m, φ (F i) * e i := by
    refine sub_eq_zero.mp (IsHausdorff.haus' (I := maximalIdeal D) _ fun N => ?_)
    rw [SModEq.zero, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, ← Ideal.Quotient.eq_zero_iff_mem,
      map_sub, sub_eq_zero]
    have hphi : ∀ i : Fin m,
        Ideal.Quotient.mk (maximalIdeal D ^ N) (φ (F i)) =
        ∑ b ∈ Finset.range N, ∑ a ∈ Finset.range (N - b),
          Ideal.Quotient.mk (maximalIdeal D ^ N) (f (cAB i a b) * x ^ a * y ^ b) := by
      intro i
      rw [show φ (F i) = evalPS (maximalIdeal D) f y hym (F i) from rfl,
        evalPS, IsAdicComplete.mk_liftRingHom]
      dsimp only [evalPSMod, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
      refine Finset.sum_congr rfl fun b hb => ?_
      rw [Finset.mem_range] at hb
      rw [PowerSeries.coeff_mk, ← map_sum]
      rw [Ideal.Quotient.eq]
      have hmem := hg i b (N - b)
      rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hmem
      obtain ⟨w, hw⟩ := hmem
      have hdiff : f (g i b) * y ^ b - ∑ a ∈ Finset.range (N - b), f (cAB i a b) * x ^ a * y ^ b =
          f w * (x ^ (N - b) * y ^ b) := by
        have hf1 : f (g i b) - ∑ a ∈ Finset.range (N - b), f (cAB i a b) * x ^ a =
            f w * x ^ (N - b) := by
          have h2 : f (g i b - ∑ a ∈ Finset.range (N - b), cAB i a b * π ^ a) =
              f (π ^ (N - b) * w) := congrArg f hw
          rw [map_sub, map_sum, map_mul, map_pow, hfx] at h2
          have hsum2 : ∑ a ∈ Finset.range (N - b), f (cAB i a b * π ^ a) =
              ∑ a ∈ Finset.range (N - b), f (cAB i a b) * x ^ a := by
            refine Finset.sum_congr rfl fun a _ => by rw [map_mul, map_pow, hfx]
          rw [hsum2] at h2
          rw [h2, mul_comm]
        calc
          f (g i b) * y ^ b - ∑ a ∈ Finset.range (N - b), f (cAB i a b) * x ^ a * y ^ b
              = (f (g i b) - ∑ a ∈ Finset.range (N - b), f (cAB i a b) * x ^ a) * y ^ b := by
                rw [sub_mul, Finset.sum_mul]
          _ = f w * (x ^ (N - b) * y ^ b) := by rw [hf1]; ring
      rw [hdiff]
      have hpow : x ^ (N - b) * y ^ b ∈ maximalIdeal D ^ N := by
        have hN : (N - b) + b = N := by omega
        have h1 : x ^ (N - b) * y ^ b ∈ maximalIdeal D ^ ((N - b) + b) := by
          rw [pow_add]
          exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hxm _) (Ideal.pow_mem_pow hym _)
        rwa [hN] at h1
      exact Ideal.mul_mem_left _ _ hpow
    have hrem0 : Ideal.Quotient.mk (maximalIdeal D ^ N)
        (∑ j : Fin (N + 1), rem N j * x ^ (N - j.1) * y ^ j.1) = 0 := by
      rw [Ideal.Quotient.eq_zero_iff_mem]
      refine Ideal.sum_mem _ fun j _ => ?_
      have hN : (N - j.1) + j.1 = N := by omega
      have hpow : x ^ (N - j.1) * y ^ j.1 ∈ maximalIdeal D ^ N := by
        have h1 : x ^ (N - j.1) * y ^ j.1 ∈ maximalIdeal D ^ ((N - j.1) + j.1) := by
          rw [pow_add]
          exact Ideal.mul_mem_mul (Ideal.pow_mem_pow hxm _) (Ideal.pow_mem_pow hym _)
        rwa [hN] at h1
      rw [mul_assoc]
      exact Ideal.mul_mem_left _ _ hpow
    rw [hinv N, map_add, hrem0, add_zero, map_sum]
    have hR : Ideal.Quotient.mk (maximalIdeal D ^ N) (∑ i : Fin m, φ (F i) * e i) =
        ∑ i : Fin m, ∑ b ∈ Finset.range N, ∑ a ∈ Finset.range (N - b),
          Ideal.Quotient.mk (maximalIdeal D ^ N) (f (cAB i a b) * e i * x ^ a * y ^ b) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_mul, hphi i, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← map_mul]
      congr 1
      ring
    rw [hR]
    have hL : Ideal.Quotient.mk (maximalIdeal D ^ N)
        (∑ n ∈ Finset.range N, ∑ k : Fin (n + 1), ∑ i : Fin m,
          f (coeffC n k i) * e i * x ^ (n - k.1) * y ^ k.1) =
        ∑ i : Fin m, ∑ n ∈ Finset.range N, ∑ k : Fin (n + 1),
          Ideal.Quotient.mk (maximalIdeal D ^ N) (f (coeffC n k i) * e i * x ^ (n - k.1) * y ^ k.1) := by
      rw [map_sum]
      simp only [map_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Finset.sum_comm]
    rw [← map_sum]
    rw [hL]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (Finset.sum_sigma' (Finset.range N) (fun n => (Finset.univ : Finset (Fin (n + 1)))) _).trans ?_
    symm
    refine (Finset.sum_sigma' (Finset.range N) (fun b => Finset.range (N - b)) _).trans ?_
    refine Finset.sum_bij (fun p _ => ⟨p.2 + p.1, ⟨p.1, by omega⟩⟩) ?_ ?_ ?_ ?_
    · intro ⟨b, a⟩ hp
      simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
      exact ⟨by omega, Finset.mem_univ _⟩
    · intro ⟨b₁, a₁⟩ _ ⟨b₂, a₂⟩ _ h
      have hb : b₁ = b₂ := by
        have h1 := congrArg (fun z : Σ n : ℕ, Fin (n + 1) => z.2.1) h
        exact h1
      have ha : a₁ = a₂ := by
        have h2 := congrArg Sigma.fst h
        dsimp only at h2
        omega
      subst hb; subst ha; rfl
    · intro ⟨n, k⟩ hn
      simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_univ, and_true] at hn
      refine ⟨⟨k.1, n - k.1⟩, ?_, ?_⟩
      · simp only [Finset.mem_sigma, Finset.mem_range]
        exact ⟨by omega, by omega⟩
      · refine Sigma.ext (by dsimp only; omega) ?_
        exact (Fin.heq_ext_iff (by dsimp only; omega)).mpr rfl
    · intro ⟨b, a⟩ _
      dsimp only [cAB]
      have hsub : a + b - b = a := by omega
      rw [hsub]
  rw [hEq]
  refine Submodule.sum_mem _ fun i _ => ?_
  change F i • e i ∈ Submodule.span (PowerSeries S) (Finset.univ.image e : Set D)
  exact Submodule.smul_mem _ (F i) (Submodule.subset_span (Finset.mem_image_of_mem e (Finset.mem_univ i)))

private lemma ringKrullDim_le_of_isIntegral
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] :
    ringKrullDim B ≤ ringKrullDim A := by
  refine Order.krullDim_le_of_strictMono (fun P : PrimeSpectrum B => PrimeSpectrum.comap (algebraMap A B) P) ?_
  intro P Q hPQ
  change P.asIdeal.comap (algebraMap A B) < Q.asIdeal.comap (algebraMap A B)
  have : P.asIdeal.IsPrime := P.isPrime
  exact Ideal.IsIntegral.comap_lt_comap (R := A) hPQ

private lemma ringKrullDim_quotient_lt_of_domain_ne_bot
    {A : Type u} [CommRing A] [IsDomain A] {Q : Ideal A} [Q.IsPrime]
    (hQ : Q ≠ ⊥) (hdim : ringKrullDim A ≤ 2) :
    ringKrullDim (A ⧸ Q) ≤ 1 := by
  rw [ringKrullDim, Order.krullDim, iSup_le_iff]
  intro s
  by_contra hgt
  have h2 : 2 ≤ s.length := by
    by_contra hlt
    apply hgt
    have h1 : s.length ≤ 1 := by omega
    exact WithBot.coe_le_coe.mpr (by exact_mod_cast h1)
  let P₀ : Ideal A := (s ⟨0, by omega⟩).asIdeal.comap (Ideal.Quotient.mk Q)
  let P₁ : Ideal A := (s ⟨1, by omega⟩).asIdeal.comap (Ideal.Quotient.mk Q)
  let P₂ : Ideal A := (s ⟨2, by omega⟩).asIdeal.comap (Ideal.Quotient.mk Q)
  have h01 : P₀ < P₁ := by
    have hlt := s.strictMono (show (⟨0, by omega⟩ : Fin (s.length + 1)) < ⟨1, by omega⟩ from
      Fin.mk_lt_mk.mpr (by omega))
    exact (Ideal.comap_mono hlt.le).lt_of_not_ge fun hge => hlt.not_ge <| by
      have hm := Ideal.map_mono (f := Ideal.Quotient.mk Q) hge
      rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hm
  have h12 : P₁ < P₂ := by
    have hlt := s.strictMono (show (⟨1, by omega⟩ : Fin (s.length + 1)) < ⟨2, by omega⟩ from
      Fin.mk_lt_mk.mpr (by omega))
    exact (Ideal.comap_mono hlt.le).lt_of_not_ge fun hge => hlt.not_ge <| by
      have hm := Ideal.map_mono (f := Ideal.Quotient.mk Q) hge
      rwa [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective,
        Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hm
  have hbot : (⊥ : Ideal A) < P₀ := by
    have hle : Q ≤ P₀ := by
      rw [← Ideal.mk_ker (I := Q)]
      exact Ideal.ker_le_comap _
    exact bot_lt_iff_ne_bot.mpr fun h0 => hQ (le_bot_iff.mp (hle.trans h0.le))
  let t : LTSeries (PrimeSpectrum A) :=
    { length := 3
      toFun := ![⟨⊥, Ideal.isPrime_bot⟩, ⟨P₀, inferInstance⟩, ⟨P₁, inferInstance⟩, ⟨P₂, inferInstance⟩]
      step := fun i => by fin_cases i <;> assumption }
  have h3 : (3 : WithBot ℕ∞) ≤ ringKrullDim A :=
    le_iSup (fun l : LTSeries (PrimeSpectrum A) => (l.length : WithBot ℕ∞)) t
  have hle32 : (3 : WithBot ℕ∞) ≤ 2 := h3.trans hdim
  exact absurd hle32 (by decide)

private lemma exists_isSmallCohenMacaulay_of_dvr_map
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    {P : Ideal R} [P.IsPrime] [IsLocalRing (R ⧸ P)] (hD_dim : ringKrullDim (R ⧸ P) = 2)
    {x y : R} (hsop : IsSystemOfParameters R [x, y])
    {S : Type u} [CommRing S] [IsNoetherianRing S] [IsDomain S] [IsLocalRing S]
    {π : S} (hπ0 : π ≠ 0) (hπmax : maximalIdeal S = Ideal.span {π})
    [IsAdicComplete (Ideal.span {π}) S]
    (f : S →+* R ⧸ P) (hfπ : f π = Ideal.Quotient.mk P x)
    (hf_res : ∀ d : R ⧸ P, ∃ s : S, d - f s ∈ maximalIdeal (R ⧸ P)) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M), IsSmallCohenMacaulay R M := by
  let D := R ⧸ P
  have : IsDomain D := Ideal.Quotient.isDomain P
  have : IsAdicComplete (maximalIdeal D) D := quotient_isAdicComplete P
  have hxmR : x ∈ maximalIdeal R := hsop.mem_maximalIdeal (by simp)
  have hymR : y ∈ maximalIdeal R := hsop.mem_maximalIdeal (by simp)
  have hmap_max : (maximalIdeal R).map (Ideal.Quotient.mk P) = maximalIdeal D := by
    have hker : RingHom.ker (Ideal.Quotient.mk P) ≤ maximalIdeal R := by
      rw [Ideal.mk_ker]
      exact le_maximalIdeal (Ideal.IsPrime.ne_top ‹P.IsPrime›)
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker)
  have hxm : Ideal.Quotient.mk P x ∈ maximalIdeal D := by
    rw [← hmap_max]
    exact Ideal.mem_map_of_mem _ hxmR
  have hym : Ideal.Quotient.mk P y ∈ maximalIdeal D := by
    rw [← hmap_max]
    exact Ideal.mem_map_of_mem _ hymR
  have hprim : ∃ r : ℕ, maximalIdeal D ^ r ≤ Ideal.span {Ideal.Quotient.mk P x, Ideal.Quotient.mk P y} := by
    obtain ⟨r, hr⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hsop.radical_eq.ge
      (IsNoetherian.noetherian _)
    refine ⟨r, ?_⟩
    rw [← hmap_max, ← Ideal.map_pow]
    refine (Ideal.map_mono hr).trans ?_
    rw [Ideal.ofList_cons, Ideal.ofList_singleton, Ideal.map_sup, Ideal.map_span, Ideal.map_span]
    simp only [Set.image_singleton]
    rw [← Ideal.span_union, Set.singleton_union]
  let φ : PowerSeries S →+* D := evalPS (maximalIdeal D) f (Ideal.Quotient.mk P y) hym
  let _ : Algebra (PowerSeries S) D := φ.toAlgebra
  have : Module.Finite (PowerSeries S) D :=
    finite_evalPS_of_dvr_map f hf_res hfπ hxm hym hprim
  have hinj : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra hne
    let Q : Ideal (PowerSeries S) := RingHom.ker φ
    have : Q.IsPrime := RingHom.ker_isPrime φ
    have hdimA : ringKrullDim (PowerSeries S) ≤ 2 := powerSeries_ringKrullDim_le_two hπmax
    have hdimQ : ringKrullDim (PowerSeries S ⧸ Q) ≤ 1 :=
      ringKrullDim_quotient_lt_of_domain_ne_bot hne hdimA
    let φ' : PowerSeries S ⧸ Q →+* D := Ideal.Quotient.lift Q φ fun _ h => h
    let _ : Algebra (PowerSeries S ⧸ Q) D := φ'.toAlgebra
    have : IsScalarTower (PowerSeries S) (PowerSeries S ⧸ Q) D :=
      ⟨fun a q d => by
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
        have hsm : a • Ideal.Quotient.mk Q b = Ideal.Quotient.mk Q (a * b) := by
          rw [Algebra.smul_def]
          exact (map_mul (Ideal.Quotient.mk Q) a b).symm
        rw [hsm]
        change φ' (Ideal.Quotient.mk Q (a * b)) * d = φ a * (φ' (Ideal.Quotient.mk Q b) * d)
        simp only [φ', map_mul, mul_assoc]
        rfl⟩
    have : Module.Finite (PowerSeries S ⧸ Q) D :=
      Module.Finite.of_restrictScalars_finite (PowerSeries S) (PowerSeries S ⧸ Q) D
    have hDle : ringKrullDim D ≤ ringKrullDim (PowerSeries S ⧸ Q) :=
      ringKrullDim_le_of_isIntegral (A := PowerSeries S ⧸ Q) (B := D)
    have h21 : (2 : WithBot ℕ∞) ≤ 1 := by
      rw [← hD_dim]
      exact hDle.trans hdimQ
    exact absurd h21 (by decide)
  exact exists_isSmallCohenMacaulay_of_finite_regular
    (R := R) (D := D) (A := PowerSeries S)
    (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective hinj hsop
    (a₁ := PowerSeries.C π) (a₂ := PowerSeries.X)
    (by change φ (PowerSeries.C π) = _; rw [evalPS_C, hfπ])
    (by change φ PowerSeries.X = _; exact evalPS_X _ _ _ _)
    (fun h => hπ0 (PowerSeries.C_injective (h.trans (map_zero _).symm)))
    powerSeries_weaklyRegular_C_X

private lemma powerSeries_field_isAdicComplete (k : Type u) [Field k] :
    IsAdicComplete (Ideal.span {(PowerSeries.X : PowerSeries k)}) (PowerSeries k) := by
  have hmem : ∀ (n : ℕ) (F : PowerSeries k),
      F ∈ Ideal.span {(PowerSeries.X : PowerSeries k)} ^ n ↔ ∀ i < n, PowerSeries.coeff i F = 0 := by
    intro n F
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff]
  exact
    { toIsHausdorff := ⟨fun F hF => by
        ext n
        have hn := hF (n + 1)
        rw [SModEq.zero, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, hmem] at hn
        exact hn n (Nat.lt_succ_self n)⟩
      toIsPrecomplete := ⟨fun seq hseq => by
        refine ⟨PowerSeries.mk fun n => PowerSeries.coeff n (seq (n + 1)), fun n => ?_⟩
        rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem, hmem]
        intro i hi
        rw [map_sub, PowerSeries.coeff_mk, sub_eq_zero]
        have hle : i + 1 ≤ n := hi
        have hstep := hseq hle
        rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem, hmem] at hstep
        have h0 := hstep i (Nat.lt_succ_self i)
        rw [map_sub, sub_eq_zero] at h0
        exact h0.symm⟩ }

private lemma exists_isSmallCohenMacaulay_of_coeff_field
    {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R]
    {P : Ideal R} [P.IsPrime] [IsLocalRing (R ⧸ P)] (hD_dim : ringKrullDim (R ⧸ P) = 2)
    {x y : R} (hsop : IsSystemOfParameters R [x, y])
    (ι : ResidueField (R ⧸ P) →+* R ⧸ P)
    (hι : ∀ a : ResidueField (R ⧸ P), residue (R ⧸ P) (ι a) = a) :
    ∃ (M : Type u) (_ : AddCommGroup M) (_ : Module R M), IsSmallCohenMacaulay R M := by
  let D := R ⧸ P
  have : IsAdicComplete (maximalIdeal D) D := quotient_isAdicComplete P
  let k := ResidueField D
  have hmap_max : (maximalIdeal R).map (Ideal.Quotient.mk P) = maximalIdeal D := by
    have hker : RingHom.ker (Ideal.Quotient.mk P) ≤ maximalIdeal R := by
      rw [Ideal.mk_ker]
      exact le_maximalIdeal (Ideal.IsPrime.ne_top ‹P.IsPrime›)
    exact IsLocalRing.eq_maximalIdeal
      (Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker)
  have hxm : Ideal.Quotient.mk P x ∈ maximalIdeal D := by
    rw [← hmap_max]
    exact Ideal.mem_map_of_mem _ (hsop.mem_maximalIdeal (by simp))
  have : IsLocalRing (PowerSeries k) := powerSeries_isLocalRing_of_dvr
  have hmaxPS : maximalIdeal (PowerSeries k) = Ideal.span {PowerSeries.X} := by
    refine le_antisymm ?_ ?_
    · intro F hF
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, PowerSeries.isUnit_iff_constantCoeff,
        isUnit_iff_ne_zero, not_not] at hF
      rw [Ideal.mem_span_singleton]
      refine ⟨PowerSeries.mk fun n => PowerSeries.coeff (n + 1) F, ?_⟩
      ext n
      cases n with
      | zero => simp [PowerSeries.coeff_zero_eq_constantCoeff, hF]
      | succ j => simp [PowerSeries.coeff_succ_X_mul]
    · rw [Ideal.span_singleton_le_iff_mem, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
        PowerSeries.isUnit_iff_constantCoeff, PowerSeries.constantCoeff_X]
      exact not_isUnit_zero
  have : IsAdicComplete (Ideal.span {(PowerSeries.X : PowerSeries k)}) (PowerSeries k) :=
    powerSeries_field_isAdicComplete k
  let f : PowerSeries k →+* D := evalPS (maximalIdeal D) ι (Ideal.Quotient.mk P x) hxm
  exact exists_isSmallCohenMacaulay_of_dvr_map hD_dim hsop
    (S := PowerSeries k) (π := PowerSeries.X) PowerSeries.X_ne_zero hmaxPS f
    (evalPS_X _ _ _ _) (fun d => ⟨PowerSeries.C (residue D d), by
      rw [evalPS_C, ← Ideal.Quotient.eq_zero_iff_mem]
      change residue D (d - ι (residue D d)) = 0
      rw [map_sub, hι, sub_self]⟩)

/-!
Part 4: p-Basis of Characteristic p Fields and Formal Smoothness over Q and F_p
-/

private lemma formallySmooth_rat_of_charZero (k : Type u) [Field k] [CharZero k] :
    Algebra.FormallySmooth ℚ k := by
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℚ k
  have halgA : Algebra.IsAlgebraic (↥(Algebra.adjoin ℚ (Set.range ((↑) : s → k)))) k :=
    hs.isAlgebraic
  have hle : Algebra.adjoin ℚ (Set.range ((↑) : s → k)) ≤
      (IntermediateField.adjoin ℚ (Set.range ((↑) : s → k))).toSubalgebra := by
    rw [Algebra.adjoin_le_iff]
    exact IntermediateField.subset_adjoin ℚ _
  have : Algebra.IsAlgebraic (↥(IntermediateField.adjoin ℚ (Set.range ((↑) : s → k)))) k := by
    refine ⟨fun x => ?_⟩
    obtain ⟨q, hq0, hqroot⟩ := halgA.isAlgebraic x
    let inc : ↥(Algebra.adjoin ℚ (Set.range ((↑) : s → k))) →+*
        ↥(IntermediateField.adjoin ℚ (Set.range ((↑) : s → k))) :=
      (Subalgebra.inclusion hle).toRingHom
    have hinc : Function.Injective inc := Subalgebra.inclusion_injective hle
    refine ⟨q.map inc, ?_, ?_⟩
    · intro h0
      apply hq0
      ext n
      have hn := congrArg (fun r => Polynomial.coeff r n) h0
      rw [Polynomial.coeff_map, Polynomial.coeff_zero] at hn
      exact congrArg Subtype.val (hinc (hn.trans (map_zero inc).symm))
    · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
      exact hqroot
  exact Algebra.FormallySmooth.of_algebraicIndependent_of_isSeparable hs.1

private def frobPow (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p] : ℕ → (k →+* k)
  | 0 => RingHom.id k
  | n + 1 => (frobenius k p).comp (frobPow k p n)

private lemma frobPow_apply {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (n : ℕ) (y : k) : frobPow k p n y = y ^ (p ^ n) := by
  induction n with
  | zero => simp [frobPow]
  | succ n ih =>
    simp only [frobPow, RingHom.comp_apply, ih, frobenius_def, ← pow_mul, pow_succ]

private noncomputable def frobRange (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) : Subfield k :=
  (frobPow k p n).fieldRange

private lemma mem_frobRange_iff {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (n : ℕ) (x : k) :
    x ∈ frobRange k p n ↔ ∃ y : k, y ^ (p ^ n) = x := by
  change x ∈ (frobPow k p n).fieldRange ↔ _
  rw [RingHom.mem_fieldRange]
  exact exists_congr fun y => by rw [frobPow_apply]

private def evalPMon {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime]
    (n : ℕ) (B : Set k) (α : B →₀ Fin (p ^ n)) : k :=
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  α.prod fun b e => (b : k) ^ (e : ℕ)

private lemma linearIndependent_powers_of_notMem_subfield
    {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
    (F : Subfield k) (hfrob : ∀ x : k, x ^ p ∈ F) {a : k} (ha : a ∉ F)
    (g : Fin p → k) (hg : ∀ i, g i ∈ F)
    (hsum : (∑ i : Fin p, g i * a ^ (i : ℕ)) = 0) :
    ∀ i, g i = 0 := by
  have halg : ∀ x : ↥F, algebraMap (↥F) k x = (x : k) := fun _ => rfl
  let poly : Polynomial ↥F := ∑ i : Fin p, Polynomial.C (⟨g i, hg i⟩ : ↥F) * Polynomial.X ^ (i : ℕ)
  have hpoly_zero : poly = 0 := by
    by_contra hpne
    have hroot : Polynomial.aeval a poly = 0 := by
      simp only [poly, map_sum, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, halg]
      exact hsum
    have hdeg : poly.natDegree < p := by
      refine lt_of_le_of_lt (Polynomial.natDegree_sum_le _ _) ?_
      rw [Finset.fold_max_lt]
      refine ⟨hp.out.pos, fun i _ => ?_⟩
      calc
        (Polynomial.C (⟨g i, hg i⟩ : ↥F) * Polynomial.X ^ (i : ℕ)).natDegree
            ≤ (Polynomial.C (⟨g i, hg i⟩ : ↥F)).natDegree + (Polynomial.X ^ (i : ℕ)).natDegree :=
              Polynomial.natDegree_mul_le
        _ ≤ 0 + (i : ℕ) := by simp
        _ < p := by simp
    have hapF : a ^ p ∈ F := hfrob a
    have hint : IsIntegral ↥F a := by
      refine ⟨Polynomial.X ^ p - Polynomial.C (⟨a ^ p, hapF⟩ : ↥F), ?_, ?_⟩
      · exact Polynomial.monic_X_pow_sub_C _ hp.out.ne_zero
      · simp [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, halg]
    let μ := minpoly ↥F a
    have hμ_dvd_poly : μ ∣ poly := minpoly.dvd ↥F a hroot
    have hμ_deg : μ.natDegree < p :=
      lt_of_le_of_lt (Polynomial.natDegree_le_of_dvd hμ_dvd_poly hpne) hdeg
    have hμ_pos : 0 < μ.natDegree := minpoly.natDegree_pos hint
    have hμ_dvd_Xp : μ ∣ Polynomial.X ^ p - Polynomial.C (⟨a ^ p, hapF⟩ : ↥F) :=
      minpoly.dvd ↥F a (by simp [halg])
    let μk : Polynomial k := μ.map F.subtype
    have hμk_dvd : μk ∣ (Polynomial.X - Polynomial.C a) ^ p := by
      have h1 := Polynomial.map_dvd F.subtype hμ_dvd_Xp
      have h2 : (Polynomial.X ^ p - Polynomial.C (⟨a ^ p, hapF⟩ : ↥F)).map F.subtype =
          (Polynomial.X - Polynomial.C a) ^ p := by
        rw [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
          sub_pow_char, ← map_pow]
        rfl
      rwa [h2] at h1
    have hμk_monic : μk.Monic := (minpoly.monic hint).map F.subtype
    have hμk_deg : μk.natDegree = μ.natDegree := (minpoly.monic hint).natDegree_map F.subtype
    have hpow_fac : μk = (Polynomial.X - Polynomial.C a) ^ μ.natDegree := by
      have hirr : Prime (Polynomial.X - Polynomial.C a) :=
        (Polynomial.irreducible_X_sub_C a).prime
      obtain ⟨d, _, hassoc⟩ := (dvd_prime_pow hirr p).mp hμk_dvd
      have hmon : ((Polynomial.X - Polynomial.C a) ^ d).Monic :=
        (Polynomial.monic_X_sub_C a).pow d
      have heq := Polynomial.eq_of_monic_of_associated hμk_monic hmon hassoc
      have hd_eq : d = μ.natDegree := by
        have := congrArg Polynomial.natDegree heq
        rw [hμk_deg, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one] at this
        exact this.symm
      rwa [← hd_eq]
    have hcoeff : μk.coeff (μ.natDegree - 1) = -((μ.natDegree : k) * a) := by
      rw [hpow_fac]
      have hbin : (Polynomial.X - Polynomial.C a) ^ μ.natDegree =
          ∑ j ∈ Finset.range (μ.natDegree + 1),
            Polynomial.C ((μ.natDegree.choose j : k) * (-a) ^ (μ.natDegree - j)) * Polynomial.X ^ j := by
        rw [sub_eq_add_neg, add_pow]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_mul, map_pow, map_neg, Polynomial.C_eq_natCast]
        ring
      rw [hbin, Polynomial.finsetSum_coeff]
      rw [Finset.sum_eq_single (μ.natDegree - 1)]
      · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_self, mul_one]
        have hsub : μ.natDegree - (μ.natDegree - 1) = 1 := by omega
        have hch : μ.natDegree.choose (μ.natDegree - 1) = μ.natDegree := by
          rw [← Nat.choose_symm (by omega : μ.natDegree - 1 ≤ μ.natDegree), hsub, Nat.choose_one_right]
        rw [hsub, hch, pow_one]
        ring
      · intro j _ hne
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
        simp [Ne.symm hne]
      · intro hnot
        exfalso
        exact hnot (Finset.mem_range.mpr (by omega))
    have hmemF : -((μ.natDegree : k) * a) ∈ F := by
      rw [← hcoeff]
      change (μ.map F.subtype).coeff (μ.natDegree - 1) ∈ F
      rw [Polynomial.coeff_map]
      exact (μ.coeff (μ.natDegree - 1)).2
    have hd_ne : (μ.natDegree : k) ≠ 0 := by
      intro h0
      have hdvd : p ∣ μ.natDegree := (CharP.cast_eq_zero_iff k p _).mp h0
      exact absurd (Nat.le_of_dvd hμ_pos hdvd) (not_le_of_gt hμ_deg)
    have ha_mem : a ∈ F := by
      have h1 : (μ.natDegree : k) * a ∈ F := by simpa using F.neg_mem hmemF
      have h2 : (μ.natDegree : k) ∈ F := natCast_mem F _
      have h3 := F.mul_mem (F.inv_mem h2) h1
      rwa [inv_mul_cancel_left₀ hd_ne] at h3
    exact ha ha_mem
  intro i
  have hi := congrArg (fun q => Polynomial.coeff q (i : ℕ)) hpoly_zero
  simp only [poly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow,
    Polynomial.coeff_zero] at hi
  rw [Finset.sum_eq_single i] at hi
  · simpa using congrArg Subtype.val hi
  · intro j _ hne
    have hne' : (i : ℕ) ≠ (j : ℕ) := fun h => hne (Fin.ext h.symm)
    simp [hne']
  · intro hnot; exact absurd (Finset.mem_univ i) hnot

private lemma exists_pBasis (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] :
    haveI : NeZero p := ⟨hp.out.ne_zero⟩
    ∃ B : Set k,
      LinearIndependent ↥(frobRange k p 1) (evalPMon (p := p) 1 B) ∧
      Submodule.span ↥(frobRange k p 1) (Set.range (evalPMon (p := p) 1 B)) = ⊤ := by
  classical
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have : NeZero (p ^ 1) := ⟨pow_ne_zero 1 hp.out.ne_zero⟩
  let kp := frobRange k p 1
  let P : Set k → Prop := fun B => LinearIndependent ↥kp (evalPMon (p := p) 1 B)
  have hchain : ∀ C ⊆ {B : Set k | P B}, IsChain (· ⊆ ·) C →
      ∃ ub ∈ {B : Set k | P B}, ∀ B ∈ C, B ⊆ ub := by
    intro C hCP hC
    refine ⟨⋃₀ C, ?_, fun B hB => Set.subset_sUnion_of_mem hB⟩
    change LinearIndependent ↥kp (evalPMon (p := p) 1 (⋃₀ C))
    rw [linearIndependent_iff']
    intro s c hc α hα
    let suppU : Finset (⋃₀ C) := s.biUnion (fun β => β.support)
    let suppK : Finset k := suppU.image Subtype.val
    have hsubU : (suppK : Set k) ⊆ ⋃₀ C := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_image] at hx
      obtain ⟨y, -, rfl⟩ := hx
      exact y.2
    have hexB : ∃ B : Set k, P B ∧ (suppK : Set k) ⊆ B := by
      rcases C.eq_empty_or_nonempty with rfl | ⟨B₀, hB₀⟩
      · refine ⟨∅, ?_, by simpa using hsubU⟩
        change LinearIndependent ↥kp (evalPMon (p := p) 1 ∅)
        rw [linearIndependent_iff']
        intro s0 c0 hc0 β hβ
        have hβ0 : β = 0 := by ext ⟨x, hx⟩; exact hx.elim
        have hs0 : s0 = {0} := by
          ext γ
          simp only [Finset.mem_singleton]
          refine ⟨fun _ => by ext ⟨x, hx⟩; exact hx.elim, fun h => h ▸ hβ0 ▸ hβ⟩
        rw [hs0, Finset.sum_singleton] at hc0
        have heval0 : evalPMon (k := k) (p := p) 1 ∅ 0 = 1 := by simp [evalPMon]
        rw [heval0, Algebra.smul_def, mul_one] at hc0
        have hcz : c0 0 = 0 := Subtype.ext (by simpa using hc0)
        rwa [hβ0]
      · have hfin_sub : ∀ (T : Finset k), (T : Set k) ⊆ ⋃₀ C → ∃ B ∈ C, (T : Set k) ⊆ B := by
          intro T
          induction T using Finset.induction_on with
          | empty => intro _; exact ⟨B₀, hB₀, by rw [Finset.coe_empty]; exact Set.empty_subset _⟩
          | insert a T ha ih =>
            intro hT
            have haU : a ∈ ⋃₀ C := hT (Finset.mem_coe.mpr (Finset.mem_insert_self a T))
            obtain ⟨Ba, hBa, haBa⟩ := Set.mem_sUnion.mp haU
            obtain ⟨BT, hBT, hTBT⟩ := ih (Set.Subset.trans (Finset.coe_subset.mpr (Finset.subset_insert a T)) hT)
            rcases hC.total hBa hBT with hle | hle
            · refine ⟨BT, hBT, ?_⟩
              rw [Finset.coe_insert, Set.insert_subset_iff]
              exact ⟨hle haBa, hTBT⟩
            · refine ⟨Ba, hBa, ?_⟩
              rw [Finset.coe_insert, Set.insert_subset_iff]
              exact ⟨haBa, hTBT.trans hle⟩
        obtain ⟨B, hBC, hTB⟩ := hfin_sub suppK hsubU
        exact ⟨B, hCP hBC, hTB⟩
    obtain ⟨B, hPB, hsuppB⟩ := hexB
    have hmap : ∀ β ∈ s, ∃ γ : B →₀ Fin (p ^ 1),
        (∀ x : B, (γ x : ℕ) = if hx : x.1 ∈ ⋃₀ C then (β ⟨x.1, hx⟩ : ℕ) else 0) ∧
        evalPMon (p := p) 1 B γ = evalPMon (p := p) 1 (⋃₀ C) β := by
      intro β hβ
      let Sβ : Finset B := β.support.attach.image fun x =>
        ⟨x.1.1, hsuppB (Finset.mem_coe.mpr (Finset.mem_image.mpr
          ⟨x.1, Finset.mem_biUnion.mpr ⟨β, hβ, x.2⟩, rfl⟩))⟩
      let γ : B →₀ Fin (p ^ 1) :=
        Finsupp.onFinset Sβ (fun x => if hx : x.1 ∈ ⋃₀ C then β ⟨x.1, hx⟩ else 0) (fun x hx => by
          split_ifs at hx with hxu
          · refine Finset.mem_image.mpr ⟨⟨⟨x.1, hxu⟩, Finsupp.mem_support_iff.mpr hx⟩,
              Finset.mem_attach _ _, by ext; rfl⟩
          · exact absurd rfl hx)
      refine ⟨γ, fun x => by dsimp only [γ, Finsupp.onFinset_apply]; split_ifs <;> rfl, ?_⟩
      dsimp only [evalPMon]
      rw [Finsupp.prod, Finsupp.prod]
      refine Finset.prod_bij (fun x hx => ⟨x.1, by
        have hxs : x ∈ Sβ := Finsupp.support_onFinset_subset hx
        rw [Finset.mem_image] at hxs
        obtain ⟨y, -, hy⟩ := hxs
        have hyx : y.1.1 = x.1 := congrArg Subtype.val hy
        rw [← hyx]
        exact y.1.2⟩) ?_ ?_ ?_ ?_
      · intro x hx
        rw [Finsupp.mem_support_iff] at hx ⊢
        dsimp only [γ, Finsupp.onFinset_apply] at hx
        split_ifs at hx with hxu
        · exact hx
        · exact absurd rfl hx
      · intro x₁ _ x₂ _ h
        ext
        exact congrArg (Subtype.val : ↥(⋃₀ C) → k) h
      · intro y hy
        have hyB : y.1 ∈ B := hsuppB (Finset.mem_coe.mpr (Finset.mem_image.mpr
          ⟨y, Finset.mem_biUnion.mpr ⟨β, hβ, hy⟩, rfl⟩))
        refine ⟨⟨y.1, hyB⟩, ?_, by ext; rfl⟩
        rw [Finsupp.mem_support_iff] at hy ⊢
        dsimp only [γ, Finsupp.onFinset_apply]
        simp only [y.2, ↓reduceDIte]
        exact hy
      · intro x hx
        dsimp only [γ, Finsupp.onFinset_apply]
        split_ifs with hxu
        · rfl
        · exfalso
          rw [Finsupp.mem_support_iff] at hx
          dsimp only [γ, Finsupp.onFinset_apply] at hx
          simp only [hxu, ↓reduceDIte] at hx
          exact hx rfl
    let toB : (β : ⋃₀ C →₀ Fin (p ^ 1)) → B →₀ Fin (p ^ 1) := fun β =>
      if h : β ∈ s then (hmap β h).choose else 0
    have htoB_inj : Set.InjOn toB (s : Set (⋃₀ C →₀ Fin (p ^ 1))) := by
      intro β₁ hβ₁ β₂ hβ₂ heq
      have h1 := (hmap β₁ hβ₁).choose_spec.1
      have h2 := (hmap β₂ hβ₂).choose_spec.1
      have heq' : (hmap β₁ hβ₁).choose = (hmap β₂ hβ₂).choose := by
        dsimp only [toB] at heq
        simp only [Finset.mem_coe.mp hβ₁, Finset.mem_coe.mp hβ₂, ↓reduceDIte] at heq
        exact heq
      ext ⟨x, hxU⟩
      by_cases h1s : ⟨x, hxU⟩ ∈ β₁.support
      · have hxB : x ∈ B := hsuppB (Finset.mem_coe.mpr (Finset.mem_image.mpr
          ⟨⟨x, hxU⟩, Finset.mem_biUnion.mpr ⟨β₁, hβ₁, h1s⟩, rfl⟩))
        have e1 := h1 ⟨x, hxB⟩
        have e2 := h2 ⟨x, hxB⟩
        rw [heq'] at e1
        simp only [hxU, ↓reduceDIte] at e1 e2
        exact e1.symm.trans e2
      · by_cases h2s : ⟨x, hxU⟩ ∈ β₂.support
        · have hxB : x ∈ B := hsuppB (Finset.mem_coe.mpr (Finset.mem_image.mpr
            ⟨⟨x, hxU⟩, Finset.mem_biUnion.mpr ⟨β₂, hβ₂, h2s⟩, rfl⟩))
          have e1 := h1 ⟨x, hxB⟩
          have e2 := h2 ⟨x, hxB⟩
          rw [heq'] at e1
          simp only [hxU, ↓reduceDIte] at e1 e2
          exact e1.symm.trans e2
        · rw [Finsupp.notMem_support_iff] at h1s h2s
          rw [h1s, h2s]
    let cB : (B →₀ Fin (p ^ 1)) → ↥kp := fun γ =>
      if h : ∃ β ∈ s, toB β = γ then c h.choose else 0
    have hsumB : ∑ γ ∈ s.image toB, cB γ • evalPMon (p := p) 1 B γ = 0 := by
      rw [Finset.sum_image htoB_inj]
      rw [← hc]
      refine Finset.sum_congr rfl fun β hβ => ?_
      have hcB : cB (toB β) = c β := by
        dsimp only [cB]
        split_ifs with h
        · have hch2 : h.choose = β := htoB_inj h.choose_spec.1 hβ h.choose_spec.2
          rw [hch2]
        · exact absurd ⟨β, hβ, rfl⟩ h
      have hev : evalPMon (p := p) 1 B (toB β) = evalPMon (p := p) 1 (⋃₀ C) β := by
        dsimp only [toB]
        simp only [hβ, ↓reduceDIte]
        exact (hmap β hβ).choose_spec.2
      rw [hcB, hev]
    have hzero := (linearIndependent_iff'.mp hPB) (s.image toB) cB hsumB (toB α)
      (Finset.mem_image_of_mem toB hα)
    dsimp only [cB] at hzero
    split_ifs at hzero with h
    · have hch2 : h.choose = α := htoB_inj h.choose_spec.1 hα h.choose_spec.2
      rwa [hch2] at hzero
    · exact absurd ⟨α, hα, rfl⟩ h
  obtain ⟨B, hPB, hBmax⟩ := zorn_subset {B : Set k | P B} hchain
  refine ⟨B, hPB, ?_⟩
  let V : Submodule ↥kp k := Submodule.span ↥kp (Set.range (evalPMon (p := p) 1 B))
  have h1V : (1 : k) ∈ V := by
    have : evalPMon (p := p) 1 B 0 = 1 := by simp [evalPMon]
    rw [← this]
    exact Submodule.subset_span ⟨0, rfl⟩
  have hmulV : ∀ u ∈ V, ∀ v ∈ V, u * v ∈ V := by
    intro u hu
    refine Submodule.span_induction (fun x hx => ?_) (by simp)
      (fun a b _ _ ha hb v hv => by rw [add_mul]; exact V.add_mem (ha v hv) (hb v hv))
      (fun c a _ ha v hv => by
        rw [Algebra.smul_def, mul_assoc, ← Algebra.smul_def]
        exact V.smul_mem c (ha v hv)) hu
    rcases hx with ⟨α, rfl⟩
    intro v hv
    refine Submodule.span_induction (fun y hy => ?_) (by simp)
      (fun a b _ _ ha hb => by rw [mul_add]; exact V.add_mem ha hb)
      (fun c a _ ha => by
        rw [Algebra.smul_def, mul_left_comm, ← Algebra.smul_def]
        exact V.smul_mem c ha) hv
    rcases hy with ⟨β, rfl⟩
    let S := α.support ∪ β.support
    let q : B → ℕ := fun b => ((α b : ℕ) + (β b : ℕ)) / p
    let r : B →₀ Fin (p ^ 1) :=
      Finsupp.onFinset S (fun b => ⟨((α b : ℕ) + (β b : ℕ)) % p,
        Nat.lt_of_lt_of_eq (Nat.mod_lt _ hp.out.pos) (pow_one p).symm⟩) (fun b hb => by
          by_contra hnot
          have ha0 : α b = 0 := Finsupp.notMem_support_iff.mp fun h => hnot (Finset.mem_union_left _ h)
          have hb0 : β b = 0 := Finsupp.notMem_support_iff.mp fun h => hnot (Finset.mem_union_right _ h)
          apply hb
          ext
          simp [ha0, hb0])
    let cprod : k := ∏ b ∈ S, ((b : k) ^ q b) ^ p
    have hc_mem : cprod ∈ kp := by
      rw [mem_frobRange_iff]
      refine ⟨∏ b ∈ S, (b : k) ^ q b, ?_⟩
      dsimp only [cprod]
      rw [pow_one, Finset.prod_pow]
    have hprod_eq : evalPMon (p := p) 1 B α * evalPMon (p := p) 1 B β =
        (⟨cprod, hc_mem⟩ : ↥kp) • evalPMon (p := p) 1 B r := by
      dsimp only [evalPMon, cprod]
      rw [Algebra.smul_def]
      change (α.prod fun b e => (b : k) ^ (e : ℕ)) * (β.prod fun b e => (b : k) ^ (e : ℕ)) =
        (∏ b ∈ S, ((b : k) ^ q b) ^ p) * (r.prod fun b e => (b : k) ^ (e : ℕ))
      have hαS : α.prod (fun b e => (b : k) ^ (e : ℕ)) = ∏ b ∈ S, (b : k) ^ (α b : ℕ) := by
        rw [Finsupp.prod]
        refine Finset.prod_subset Finset.subset_union_left fun b _ hb => ?_
        rw [Finsupp.notMem_support_iff.mp hb]
        simp
      have hβS : β.prod (fun b e => (b : k) ^ (e : ℕ)) = ∏ b ∈ S, (b : k) ^ (β b : ℕ) := by
        rw [Finsupp.prod]
        refine Finset.prod_subset Finset.subset_union_right fun b _ hb => ?_
        rw [Finsupp.notMem_support_iff.mp hb]
        simp
      have hrS : r.prod (fun b e => (b : k) ^ (e : ℕ)) = ∏ b ∈ S, (b : k) ^ (r b : ℕ) := by
        rw [Finsupp.prod]
        refine Finset.prod_subset (Finsupp.support_onFinset_subset) fun b _ hb => ?_
        rw [Finsupp.notMem_support_iff.mp hb]
        simp
      rw [hαS, hβS, hrS, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [← pow_add, ← pow_mul, ← pow_add]
      congr 1
      dsimp only [q, r, Finsupp.onFinset_apply]
      exact (Nat.div_add_mod' ((α b : ℕ) + (β b : ℕ)) p).symm
    rw [hprod_eq]
    exact V.smul_mem ⟨cprod, hc_mem⟩ (Submodule.subset_span ⟨r, rfl⟩)
  let Vfield : Subfield k :=
    { carrier := V
      zero_mem' := V.zero_mem
      one_mem' := h1V
      add_mem' := fun hu hv => V.add_mem hu hv
      neg_mem' := fun hu => V.neg_mem hu
      mul_mem' := fun hu hv => hmulV _ hu _ hv
      inv_mem' := fun {u} hu => by
        by_cases hu0 : u = 0
        · rw [hu0, inv_zero]; exact V.zero_mem
        · have hup : u ^ p ∈ kp := (mem_frobRange_iff 1 _).mpr ⟨u, by rw [pow_one]⟩
          have hinvp : (u ^ p)⁻¹ ∈ kp := kp.inv_mem hup
          have hpow : u ^ (p - 1) ∈ V := by
            have hsub : ∀ m : ℕ, u ^ m ∈ V := fun m => by
              induction m with
              | zero => simpa using h1V
              | succ m ihm => rw [pow_succ]; exact hmulV _ ihm _ hu
            exact hsub (p - 1)
          have heq : u⁻¹ = (⟨(u ^ p)⁻¹, hinvp⟩ : ↥kp) • u ^ (p - 1) := by
            rw [Algebra.smul_def]
            change u⁻¹ = (u ^ p)⁻¹ * u ^ (p - 1)
            have hmul : u ^ p * u⁻¹ = u ^ (p - 1) := by
              have hp1 : p = (p - 1) + 1 := (Nat.sub_add_cancel hp.out.one_le).symm
              calc
                u ^ p * u⁻¹ = u ^ ((p - 1) + 1) * u⁻¹ := by rw [← hp1]
                _ = u ^ (p - 1) * (u * u⁻¹) := by rw [pow_succ, mul_assoc]
                _ = u ^ (p - 1) := by rw [mul_inv_cancel₀ hu0, mul_one]
            rw [← hmul, inv_mul_cancel_left₀ (pow_ne_zero p hu0)]
          rw [heq]
          exact V.smul_mem _ hpow }
  refine eq_top_iff.mpr fun a _ => ?_
  by_contra haV
  have haB : a ∉ B := fun h => haV (by
    let α : B →₀ Fin (p ^ 1) := Finsupp.single ⟨a, h⟩ ⟨1, by rw [pow_one]; exact hp.out.one_lt⟩
    have hev : evalPMon (p := p) 1 B α = a := by
      dsimp only [evalPMon, α]
      rw [Finsupp.prod_single_index (by simp)]
      simp
    rw [← hev]
    exact Submodule.subset_span ⟨α, rfl⟩)
  have hlin_a : ∀ g : Fin p → k, (∀ i, g i ∈ Vfield) →
      (∑ i : Fin p, g i * a ^ (i : ℕ)) = 0 → ∀ i, g i = 0 :=
    linearIndependent_powers_of_notMem_subfield Vfield
      (fun x => by
        have hmem : x ^ p ∈ kp := (mem_frobRange_iff 1 _).mpr ⟨x, by rw [pow_one]⟩
        have h1 : (⟨x ^ p, hmem⟩ : ↥kp) • (1 : k) ∈ V := V.smul_mem _ h1V
        change x ^ p ∈ V
        have hsm : (⟨x ^ p, hmem⟩ : ↥kp) • (1 : k) = x ^ p := by
          rw [Algebra.smul_def, mul_one]
          rfl
        rwa [hsm] at h1)
      haV
  have hP_ins : P (insert a B) := by
    let B' : Set k := insert a B
    let a' : B' := ⟨a, Set.mem_insert a B⟩
    let emb : B → B' := fun x => ⟨x.1, Set.mem_insert_of_mem a x.2⟩
    have hemb_inj : Function.Injective emb := fun _ _ h => Subtype.ext (congrArg (Subtype.val : B' → k) h)
    change LinearIndependent ↥kp (evalPMon (p := p) 1 B')
    rw [linearIndependent_iff']
    intro s c hc β hβ
    let restrB : (B' →₀ Fin (p ^ 1)) → (B →₀ Fin (p ^ 1)) := fun γ =>
      Finsupp.onFinset
        (γ.support.preimage emb hemb_inj.injOn)
        (fun x => γ (emb x))
        (fun x hx => by
          rw [Finset.mem_preimage]
          exact Finsupp.mem_support_iff.mpr hx)
    have hsplit_ev : ∀ γ : B' →₀ Fin (p ^ 1),
        evalPMon (p := p) 1 B' γ =
          evalPMon (p := p) 1 B (restrB γ) * a ^ (γ a' : ℕ) := by
      intro γ
      dsimp only [evalPMon]
      rw [Finsupp.prod, Finsupp.prod]
      have herase :
          ∏ y ∈ γ.support, (y.1 : k) ^ (γ y : ℕ) =
          (∏ y ∈ γ.support.erase a', (y.1 : k) ^ (γ y : ℕ)) * a ^ (γ a' : ℕ) := by
        by_cases hmem : a' ∈ γ.support
        · rw [mul_comm]
          exact (Finset.mul_prod_erase γ.support (fun y => (y.1 : k) ^ (γ y : ℕ)) hmem).symm
        · have h0 : γ a' = 0 := Finsupp.notMem_support_iff.mp hmem
          rw [Finset.erase_eq_of_notMem hmem, h0]
          simp
      rw [herase]
      congr 1
      symm
      refine Finset.prod_bij (fun x _ => emb x) ?_ ?_ ?_ ?_
      · intro x hx
        rw [Finset.mem_erase]
        refine ⟨fun h => haB (by
          have hval : x.1 = a := congrArg (Subtype.val : B' → k) h
          rw [← hval]
          exact x.2), ?_⟩
        rw [Finsupp.mem_support_iff] at hx ⊢
        simpa [restrB] using hx
      · intro x₁ _ x₂ _ h
        exact Subtype.ext (congrArg (Subtype.val : B' → k) h)
      · intro y hy
        rw [Finset.mem_erase] at hy
        have hya : y.1 ≠ a := fun h => hy.1 (Subtype.ext h)
        have hyB : y.1 ∈ B := (Set.mem_insert_iff.mp y.2).resolve_left hya
        refine ⟨⟨y.1, hyB⟩, ?_, by ext; rfl⟩
        rw [Finsupp.mem_support_iff]
        have hy0 : γ y ≠ 0 := Finsupp.mem_support_iff.mp hy.2
        simpa [restrB] using hy0
      · intro x _
        simp [restrB, emb]
    let g : Fin p → k := fun e =>
      ∑ γ ∈ s.filter (fun γ => (γ a' : ℕ) = (e : ℕ)),
        (c γ : k) * evalPMon (p := p) 1 B (restrB γ)
    have hgV : ∀ e : Fin p, g e ∈ Vfield := fun e => by
      refine Vfield.sum_mem fun γ _ => ?_
      have hcV : (c γ : k) ∈ Vfield := by
        have h1 : (c γ) • (1 : k) ∈ V := V.smul_mem (c γ) h1V
        change (c γ : k) ∈ V
        have hsm : (c γ) • (1 : k) = (c γ : k) := by
          rw [Algebra.smul_def, mul_one]
          rfl
        rwa [hsm] at h1
      exact Vfield.mul_mem hcV (Submodule.subset_span ⟨restrB γ, rfl⟩)
    have hgsum : ∑ e : Fin p, g e * a ^ (e : ℕ) = 0 := by
      let degA : (B' →₀ Fin (p ^ 1)) → Fin p := fun γ =>
        ⟨(γ a' : ℕ), Nat.lt_of_lt_of_eq (γ a').2 (pow_one p)⟩
      have h1 : ∑ e : Fin p, g e * a ^ (e : ℕ) =
          ∑ γ ∈ s, (c γ : k) * evalPMon (p := p) 1 B' γ := by
        calc
          ∑ e : Fin p, g e * a ^ (e : ℕ)
              = ∑ e : Fin p, ∑ γ ∈ s.filter (fun γ => (γ a' : ℕ) = (e : ℕ)),
                  ((c γ : k) * evalPMon (p := p) 1 B (restrB γ)) * a ^ (e : ℕ) := by
                refine Finset.sum_congr rfl fun e _ => ?_
                rw [Finset.sum_mul]
          _ = ∑ e : Fin p, ∑ γ ∈ s.filter (fun γ => (γ a' : ℕ) = (e : ℕ)),
                  (c γ : k) * evalPMon (p := p) 1 B' γ := by
                refine Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun γ hγ => ?_
                have he : (γ a' : ℕ) = (e : ℕ) := (Finset.mem_filter.mp hγ).2
                rw [hsplit_ev γ, he, mul_assoc]
          _ = ∑ γ ∈ s, (c γ : k) * evalPMon (p := p) 1 B' γ := by
                rw [← Finset.sum_fiberwise_of_maps_to (g := degA) (fun _ _ => Finset.mem_univ _)]
                refine Finset.sum_congr rfl fun e _ => Finset.sum_congr ?_ fun _ _ => rfl
                ext γ
                simp [degA, Fin.ext_iff]
      rw [h1]
      have hsm : ∀ γ, c γ • evalPMon (p := p) 1 B' γ = (c γ : k) * evalPMon (p := p) 1 B' γ :=
        fun _ => rfl
      simpa only [hsm] using hc
    have hg0 : ∀ e : Fin p, g e = 0 := hlin_a g hgV hgsum
    let eβ : Fin p := ⟨(β a' : ℕ), Nat.lt_of_lt_of_eq (β a').2 (pow_one p)⟩
    let sβ := s.filter (fun γ => (γ a' : ℕ) = (eβ : ℕ))
    have hrestr_inj : Set.InjOn restrB (sβ : Set _) := by
      intro γ₁ hγ₁ γ₂ hγ₂ heq
      have h1 : (γ₁ a' : ℕ) = (eβ : ℕ) := (Finset.mem_filter.mp hγ₁).2
      have h2 : (γ₂ a' : ℕ) = (eβ : ℕ) := (Finset.mem_filter.mp hγ₂).2
      ext y
      by_cases hya : y.1 = a
      · have hy : y = a' := Subtype.ext hya
        rw [hy]
        exact h1.trans h2.symm
      · have hyB : y.1 ∈ B := (Set.mem_insert_iff.mp y.2).resolve_left hya
        have hy : y = emb ⟨y.1, hyB⟩ := Subtype.ext rfl
        have hval := congrArg (fun f : B →₀ Fin (p ^ 1) => (f ⟨y.1, hyB⟩ : ℕ)) heq
        dsimp only [restrB, Finsupp.onFinset_apply] at hval
        rwa [hy]
    let cB : (B →₀ Fin (p ^ 1)) → ↥kp := fun δ =>
      if h : ∃ γ ∈ sβ, restrB γ = δ then c h.choose else 0
    have hsumB : ∑ δ ∈ sβ.image restrB, cB δ • evalPMon (p := p) 1 B δ = 0 := by
      rw [Finset.sum_image hrestr_inj]
      have hge := hg0 eβ
      rw [← hge]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [Algebra.smul_def]
      have hcB : cB (restrB γ) = c γ := by
        dsimp only [cB]
        split_ifs with h
        · have hch : h.choose = γ := hrestr_inj h.choose_spec.1 hγ h.choose_spec.2
          rw [hch]
        · exact absurd ⟨γ, hγ, rfl⟩ h
      rw [hcB]
      rfl
    have hβ_mem : β ∈ sβ := Finset.mem_filter.mpr ⟨hβ, rfl⟩
    have hzero := (linearIndependent_iff'.mp hPB) (sβ.image restrB) cB hsumB (restrB β)
      (Finset.mem_image_of_mem restrB hβ_mem)
    dsimp only [cB] at hzero
    split_ifs at hzero with h
    · have hch : h.choose = β := hrestr_inj h.choose_spec.1 hβ_mem h.choose_spec.2
      rwa [hch] at hzero
    · exact absurd ⟨β, hβ_mem, rfl⟩ h
  have hsub : B ⊆ insert a B := Set.subset_insert a B
  have heq := hBmax hP_ins hsub
  exact haB (heq (Set.mem_insert a B))

private lemma evalPMon_mul_decomp
    {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
    (n : ℕ) (B : Set k) (α β : B →₀ Fin (p ^ n)) :
    ∃ (c : k) (r : B →₀ Fin (p ^ n)),
      c ∈ frobRange k p n ∧ evalPMon (p := p) n B α * evalPMon (p := p) n B β = c * evalPMon (p := p) n B r := by
  classical
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  let S := α.support ∪ β.support
  let q : B → ℕ := fun b => ((α b : ℕ) + (β b : ℕ)) / p ^ n
  let r : B →₀ Fin (p ^ n) :=
    Finsupp.onFinset S (fun b => ⟨((α b : ℕ) + (β b : ℕ)) % p ^ n,
      Nat.mod_lt _ (pow_pos hp.out.pos n)⟩) (fun b hb => by
        by_contra hnot
        have ha0 : α b = 0 := Finsupp.notMem_support_iff.mp fun h => hnot (Finset.mem_union_left _ h)
        have hb0 : β b = 0 := Finsupp.notMem_support_iff.mp fun h => hnot (Finset.mem_union_right _ h)
        apply hb
        ext
        simp [ha0, hb0])
  let c : k := ∏ b ∈ S, ((b : k) ^ q b) ^ (p ^ n)
  have hc : c ∈ frobRange k p n := by
    rw [mem_frobRange_iff]
    refine ⟨∏ b ∈ S, (b : k) ^ q b, ?_⟩
    dsimp only [c]
    rw [Finset.prod_pow]
  refine ⟨c, r, hc, ?_⟩
  dsimp only [evalPMon, c]
  have hαS : α.prod (fun b e => (b : k) ^ (e : ℕ)) = ∏ b ∈ S, (b : k) ^ (α b : ℕ) := by
    rw [Finsupp.prod]
    refine Finset.prod_subset Finset.subset_union_left fun b _ hb => ?_
    rw [Finsupp.notMem_support_iff.mp hb]
    simp
  have hβS : β.prod (fun b e => (b : k) ^ (e : ℕ)) = ∏ b ∈ S, (b : k) ^ (β b : ℕ) := by
    rw [Finsupp.prod]
    refine Finset.prod_subset Finset.subset_union_right fun b _ hb => ?_
    rw [Finsupp.notMem_support_iff.mp hb]
    simp
  have hrS : r.prod (fun b e => (b : k) ^ (e : ℕ)) = ∏ b ∈ S, (b : k) ^ (r b : ℕ) := by
    rw [Finsupp.prod]
    refine Finset.prod_subset Finsupp.support_onFinset_subset fun b _ hb => ?_
    rw [Finsupp.notMem_support_iff.mp hb]
    simp
  rw [hαS, hβS, hrS, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← pow_add, ← pow_mul, ← pow_add]
  congr 1
  dsimp only [q, r, Finsupp.onFinset_apply]
  exact (Nat.div_add_mod' ((α b : ℕ) + (β b : ℕ)) (p ^ n)).symm

private noncomputable def splitR {k : Type u} {p : ℕ} [hp : Fact p.Prime] (n : ℕ) (B : Set k)
    (γ : B →₀ Fin (p ^ (n + 1))) : B →₀ Fin (p ^ n) := by
  classical
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  exact Finsupp.onFinset γ.support
    (fun b => ⟨(γ b : ℕ) % p ^ n, Nat.mod_lt _ (pow_pos hp.out.pos n)⟩)
    (fun b hb => by
      by_contra hnot
      have h0 : γ b = 0 := Finsupp.notMem_support_iff.mp hnot
      apply hb
      ext
      simp [h0])

private noncomputable def splitQ {k : Type u} {p : ℕ} [hp : Fact p.Prime] (n : ℕ) (B : Set k)
    (γ : B →₀ Fin (p ^ (n + 1))) : B →₀ Fin (p ^ 1) := by
  classical
  haveI : NeZero (p ^ 1) := ⟨pow_ne_zero 1 hp.out.ne_zero⟩
  exact Finsupp.onFinset γ.support
    (fun b => ⟨(γ b : ℕ) / p ^ n, by
      have hlt : (γ b : ℕ) < p * p ^ n := by
        simpa [pow_succ'] using (γ b).2
      have hdiv : (γ b : ℕ) / p ^ n < p := (Nat.div_lt_iff_lt_mul (pow_pos hp.out.pos n)).mpr hlt
      exact Nat.lt_of_lt_of_eq hdiv (pow_one p).symm⟩)
    (fun b hb => by
      by_contra hnot
      have h0 : γ b = 0 := Finsupp.notMem_support_iff.mp hnot
      apply hb
      ext
      simp [h0])

private noncomputable def combineRQ {k : Type u} {p : ℕ} [hp : Fact p.Prime] (n : ℕ) (B : Set k)
    (r : B →₀ Fin (p ^ n)) (q : B →₀ Fin (p ^ 1)) : B →₀ Fin (p ^ (n + 1)) := by
  classical
  haveI : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hp.out.ne_zero⟩
  exact Finsupp.onFinset (r.support ∪ q.support)
    (fun b => ⟨(q b : ℕ) * p ^ n + (r b : ℕ), by
      have hq : (q b : ℕ) < p := Nat.lt_of_lt_of_eq (q b).2 (pow_one p)
      have hr : (r b : ℕ) < p ^ n := (r b).2
      have hle : (q b : ℕ) + 1 ≤ p := hq
      calc
        (q b : ℕ) * p ^ n + (r b : ℕ) < (q b : ℕ) * p ^ n + p ^ n := Nat.add_lt_add_left hr _
        _ = ((q b : ℕ) + 1) * p ^ n := by ring
        _ ≤ p * p ^ n := Nat.mul_le_mul_right _ hle
        _ = p ^ (n + 1) := by rw [pow_succ']⟩)
    (fun b hb => by
      by_contra hnot
      have hr0 : r b = 0 := Finsupp.notMem_support_iff.mp fun h => hnot (Finset.mem_union_left _ h)
      have hq0 : q b = 0 := Finsupp.notMem_support_iff.mp fun h => hnot (Finset.mem_union_right _ h)
      apply hb
      ext
      simp [hr0, hq0])

private lemma evalPMon_split {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime]
    (n : ℕ) (B : Set k) (γ : B →₀ Fin (p ^ (n + 1))) :
    evalPMon (p := p) (n + 1) B γ =
      (evalPMon (p := p) 1 B (splitQ (p := p) n B γ)) ^ (p ^ n) *
        evalPMon (p := p) n B (splitR (p := p) n B γ) := by
  classical
  have : NeZero (p ^ 1) := ⟨pow_ne_zero 1 hp.out.ne_zero⟩
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hp.out.ne_zero⟩
  dsimp only [evalPMon]
  have hQ : (splitQ (p := p) n B γ).prod (fun b e => (b : k) ^ (e : ℕ)) =
      ∏ b ∈ γ.support, (b : k) ^ ((γ b : ℕ) / p ^ n) := by
    rw [Finsupp.prod]
    have hsub : (splitQ (p := p) n B γ).support ⊆ γ.support := Finsupp.support_onFinset_subset
    refine (Finset.prod_subset hsub fun b _ hb => ?_).trans (Finset.prod_congr rfl fun b _ => ?_)
    · rw [Finsupp.notMem_support_iff.mp hb]; simp
    · rfl
  have hR : (splitR (p := p) n B γ).prod (fun b e => (b : k) ^ (e : ℕ)) =
      ∏ b ∈ γ.support, (b : k) ^ ((γ b : ℕ) % p ^ n) := by
    rw [Finsupp.prod]
    have hsub : (splitR (p := p) n B γ).support ⊆ γ.support := Finsupp.support_onFinset_subset
    refine (Finset.prod_subset hsub fun b _ hb => ?_).trans (Finset.prod_congr rfl fun b _ => ?_)
    · rw [Finsupp.notMem_support_iff.mp hb]; simp
    · rfl
  rw [Finsupp.prod, hQ, hR, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← pow_mul, ← pow_add]
  congr 1
  exact (Nat.div_add_mod' (γ b : ℕ) (p ^ n)).symm

private lemma evalPMon_combine {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime]
    (n : ℕ) (B : Set k) (r : B →₀ Fin (p ^ n)) (q : B →₀ Fin (p ^ 1)) :
    evalPMon (p := p) (n + 1) B (combineRQ (p := p) n B r q) =
      (evalPMon (p := p) 1 B q) ^ (p ^ n) * evalPMon (p := p) n B r := by
  classical
  have : NeZero (p ^ 1) := ⟨pow_ne_zero 1 hp.out.ne_zero⟩
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hp.out.ne_zero⟩
  let S := r.support ∪ q.support
  dsimp only [evalPMon]
  have hC : (combineRQ (p := p) n B r q).prod (fun b e => (b : k) ^ (e : ℕ)) =
      ∏ b ∈ S, (b : k) ^ ((q b : ℕ) * p ^ n + (r b : ℕ)) := by
    rw [Finsupp.prod]
    have hsub : (combineRQ (p := p) n B r q).support ⊆ S := Finsupp.support_onFinset_subset
    refine (Finset.prod_subset hsub fun b _ hb => ?_).trans (Finset.prod_congr rfl fun b _ => ?_)
    · rw [Finsupp.notMem_support_iff.mp hb]; simp
    · rfl
  have hQ : q.prod (fun b e => (b : k) ^ (e : ℕ)) = ∏ b ∈ S, (b : k) ^ (q b : ℕ) := by
    rw [Finsupp.prod]
    refine Finset.prod_subset Finset.subset_union_right fun b _ hb => ?_
    rw [Finsupp.notMem_support_iff.mp hb]; simp
  have hR : r.prod (fun b e => (b : k) ^ (e : ℕ)) = ∏ b ∈ S, (b : k) ^ (r b : ℕ) := by
    rw [Finsupp.prod]
    refine Finset.prod_subset Finset.subset_union_left fun b _ hb => ?_
    rw [Finsupp.notMem_support_iff.mp hb]; simp
  rw [hC, hQ, hR, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← pow_mul, ← pow_add]

private lemma pBasis_pow {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
    {B : Set k}
    (hli1 : LinearIndependent ↥(frobRange k p 1) (evalPMon (p := p) 1 B))
    (hsp1 : Submodule.span ↥(frobRange k p 1) (Set.range (evalPMon (p := p) 1 B)) = ⊤) :
    ∀ n : ℕ,
      LinearIndependent ↥(frobRange k p n) (evalPMon (p := p) n B) ∧
      Submodule.span ↥(frobRange k p n) (Set.range (evalPMon (p := p) n B)) = ⊤ := by
  classical
  intro n
  induction n with
  | zero =>
    have : NeZero (p ^ 0) := ⟨pow_ne_zero 0 hp.out.ne_zero⟩
    have huniq : ∀ α : B →₀ Fin (p ^ 0), α = 0 := fun α => by
      ext b
      have h1 := (α b).2
      simp only [pow_zero] at h1
      change (α b : ℕ) = 0
      omega
    have hev0 : evalPMon (p := p) 0 B 0 = 1 := by
      simp only [evalPMon, Finsupp.prod_zero_index]
    refine ⟨?_, ?_⟩
    · rw [linearIndependent_iff']
      intro s c hc α hα
      have hα0 : α = 0 := huniq α
      have hs0 : s = {0} := by
        ext γ
        simp only [Finset.mem_singleton]
        exact ⟨fun _ => huniq γ, fun h => h ▸ hα0 ▸ hα⟩
      rw [hs0, Finset.sum_singleton, hev0, Algebra.smul_def, mul_one] at hc
      have h0 : c 0 = 0 := Subtype.ext (by simpa using hc)
      rwa [hα0]
    · refine eq_top_iff.mpr fun x _ => ?_
      have hx : x ∈ frobRange k p 0 := (mem_frobRange_iff 0 x).mpr ⟨x, by simp⟩
      have hsm : (⟨x, hx⟩ : ↥(frobRange k p 0)) • evalPMon (p := p) 0 B 0 = x := by
        rw [hev0, Algebra.smul_def, mul_one]; rfl
      rw [← hsm]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩)
  | succ n ih =>
    rcases ih with ⟨hlin, hspn⟩
    have : NeZero (p ^ 1) := ⟨pow_ne_zero 1 hp.out.ne_zero⟩
    have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
    have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hp.out.ne_zero⟩
    refine ⟨?_, ?_⟩
    · rw [linearIndependent_iff']
      intro s c hc α hα
      let rα := splitR (p := p) n B α
      let coeffR : (B →₀ Fin (p ^ n)) → k := fun r =>
        ∑ γ ∈ s.filter (fun γ => splitR (p := p) n B γ = r),
          (c γ : k) * (evalPMon (p := p) 1 B (splitQ (p := p) n B γ)) ^ (p ^ n)
      have hmemR : ∀ r, coeffR r ∈ frobRange k p n := fun r => by
        refine (frobRange k p n).sum_mem fun γ _ => ?_
        have hcγ : (c γ : k) ∈ frobRange k p n := by
          obtain ⟨y, hy⟩ := (mem_frobRange_iff (n + 1) (c γ : k)).mp (c γ).2
          rw [mem_frobRange_iff]
          exact ⟨y ^ p, by rw [← pow_mul, ← pow_succ', hy]⟩
        have hqγ : (evalPMon (p := p) 1 B (splitQ (p := p) n B γ)) ^ (p ^ n) ∈ frobRange k p n :=
          (mem_frobRange_iff n _).mpr ⟨_, rfl⟩
        exact (frobRange k p n).mul_mem hcγ hqγ
      have hsumR : ∑ r ∈ s.image (splitR (p := p) n B),
          (⟨coeffR r, hmemR r⟩ : ↥(frobRange k p n)) • evalPMon (p := p) n B r = 0 := by
        have h1 : ∑ r ∈ s.image (splitR (p := p) n B),
            (⟨coeffR r, hmemR r⟩ : ↥(frobRange k p n)) • evalPMon (p := p) n B r =
            ∑ γ ∈ s, (c γ : k) * evalPMon (p := p) (n + 1) B γ := by
          calc
            ∑ r ∈ s.image (splitR (p := p) n B),
                (⟨coeffR r, hmemR r⟩ : ↥(frobRange k p n)) • evalPMon (p := p) n B r
                = ∑ r ∈ s.image (splitR (p := p) n B),
                    ∑ γ ∈ s.filter (fun γ => splitR (p := p) n B γ = r),
                      (c γ : k) * ((evalPMon (p := p) 1 B (splitQ (p := p) n B γ)) ^ (p ^ n) *
                        evalPMon (p := p) n B r) := by
                  refine Finset.sum_congr rfl fun r _ => ?_
                  change coeffR r * evalPMon (p := p) n B r = _
                  dsimp only [coeffR]
                  rw [Finset.sum_mul]
                  refine Finset.sum_congr rfl fun γ _ => by ring
            _ = ∑ r ∈ s.image (splitR (p := p) n B),
                  ∑ γ ∈ s.filter (fun γ => splitR (p := p) n B γ = r),
                    (c γ : k) * evalPMon (p := p) (n + 1) B γ := by
                  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun γ hγ => ?_
                  have hr : splitR (p := p) n B γ = r := (Finset.mem_filter.mp hγ).2
                  rw [evalPMon_split (p := p) n B γ, hr]
            _ = ∑ γ ∈ s, (c γ : k) * evalPMon (p := p) (n + 1) B γ :=
                  Finset.sum_fiberwise_of_maps_to (fun _ h => Finset.mem_image_of_mem _ h) _
        rw [h1]
        have hsm : ∀ γ, c γ • evalPMon (p := p) (n + 1) B γ = (c γ : k) * evalPMon (p := p) (n + 1) B γ :=
          fun _ => rfl
        simpa only [hsm] using hc
      have hcr0 : coeffR rα = 0 := congrArg Subtype.val
        ((linearIndependent_iff'.mp hlin) (s.image (splitR (p := p) n B))
          (fun r => ⟨coeffR r, hmemR r⟩) hsumR rα (Finset.mem_image_of_mem _ hα))
      let sα := s.filter (fun γ => splitR (p := p) n B γ = rα)
      have hrootC : ∀ γ : B →₀ Fin (p ^ (n + 1)), ∃ d : ↥(frobRange k p 1), (d : k) ^ (p ^ n) = (c γ : k) := by
        intro γ
        obtain ⟨y, hy⟩ := (mem_frobRange_iff (n + 1) (c γ : k)).mp (c γ).2
        refine ⟨⟨y ^ p, (mem_frobRange_iff 1 _).mpr ⟨y, by rw [pow_one]⟩⟩, ?_⟩
        rw [← pow_mul, ← pow_succ', hy]
      choose d hd using hrootC
      have hsumQ0 : ∑ γ ∈ sα, (d γ : k) * evalPMon (p := p) 1 B (splitQ (p := p) n B γ) = 0 := by
        have hpow : (∑ γ ∈ sα, (d γ : k) * evalPMon (p := p) 1 B (splitQ (p := p) n B γ)) ^ (p ^ n) = 0 := by
          have hfrob : (∑ γ ∈ sα, (d γ : k) * evalPMon (p := p) 1 B (splitQ (p := p) n B γ)) ^ (p ^ n) =
              frobPow k p n (∑ γ ∈ sα, (d γ : k) * evalPMon (p := p) 1 B (splitQ (p := p) n B γ)) :=
            (frobPow_apply n _).symm
          rw [hfrob, map_sum]
          have hterm : ∑ γ ∈ sα, frobPow k p n ((d γ : k) * evalPMon (p := p) 1 B (splitQ (p := p) n B γ)) =
              coeffR rα := by
            refine Finset.sum_congr rfl fun γ _ => ?_
            rw [map_mul, frobPow_apply, frobPow_apply, hd γ]
          rw [hterm, hcr0]
        exact eq_zero_of_pow_eq_zero hpow
      have hQinj : Set.InjOn (splitQ (p := p) n B) (sα : Set _) := by
        intro γ₁ hγ₁ γ₂ hγ₂ heq
        have hr1 : splitR (p := p) n B γ₁ = rα := (Finset.mem_filter.mp hγ₁).2
        have hr2 : splitR (p := p) n B γ₂ = rα := (Finset.mem_filter.mp hγ₂).2
        ext b
        have hq : (γ₁ b : ℕ) / p ^ n = (γ₂ b : ℕ) / p ^ n :=
          congrArg (fun f : B →₀ Fin (p ^ 1) => (f b : ℕ)) heq
        have hr : (γ₁ b : ℕ) % p ^ n = (γ₂ b : ℕ) % p ^ n :=
          congrArg (fun f : B →₀ Fin (p ^ n) => (f b : ℕ)) (hr1.trans hr2.symm)
        have h1 := Nat.div_add_mod' (γ₁ b : ℕ) (p ^ n)
        have h2 := Nat.div_add_mod' (γ₂ b : ℕ) (p ^ n)
        rw [← h1, ← h2, hq, hr]
      let dQ : (B →₀ Fin (p ^ 1)) → ↥(frobRange k p 1) := fun q =>
        if h : ∃ γ ∈ sα, splitQ (p := p) n B γ = q then d h.choose else 0
      have hsumQ : ∑ q ∈ sα.image (splitQ (p := p) n B), dQ q • evalPMon (p := p) 1 B q = 0 := by
        rw [Finset.sum_image hQinj, ← hsumQ0]
        refine Finset.sum_congr rfl fun γ hγ => ?_
        have hdQ : dQ (splitQ (p := p) n B γ) = d γ := by
          dsimp only [dQ]
          split_ifs with h
          · rw [hQinj h.choose_spec.1 hγ h.choose_spec.2]
          · exact absurd ⟨γ, hγ, rfl⟩ h
        rw [hdQ]
        rfl
      have hα_mem : α ∈ sα := Finset.mem_filter.mpr ⟨hα, rfl⟩
      have hdα0 : d α = 0 := by
        have h0 := (linearIndependent_iff'.mp hli1) (sα.image (splitQ (p := p) n B)) dQ hsumQ
          (splitQ (p := p) n B α) (Finset.mem_image_of_mem _ hα_mem)
        dsimp only [dQ] at h0
        split_ifs at h0 with h
        · rwa [hQinj h.choose_spec.1 hα_mem h.choose_spec.2] at h0
        · exact absurd ⟨α, hα_mem, rfl⟩ h
      ext
      rw [← hd α, hdα0]
      exact zero_pow (pow_ne_zero n hp.out.ne_zero)
    · refine eq_top_iff.mpr fun x _ => ?_
      have hxn : x ∈ Submodule.span ↥(frobRange k p n) (Set.range (evalPMon (p := p) n B)) :=
        hspn ▸ Submodule.mem_top
      refine Submodule.span_induction (fun z hz => ?_) (Submodule.zero_mem _)
        (fun _ _ _ _ h1 h2 => Submodule.add_mem _ h1 h2) (fun a z _ hz => ?_) hxn
      · rcases hz with ⟨r, rfl⟩
        have hcomb : evalPMon (p := p) (n + 1) B (combineRQ (p := p) n B r 0) = evalPMon (p := p) n B r := by
          rw [evalPMon_combine]
          simp [evalPMon]
        rw [← hcomb]
        exact Submodule.subset_span ⟨combineRQ (p := p) n B r 0, rfl⟩
      · obtain ⟨u, hu⟩ := (mem_frobRange_iff n (a : k)).mp a.2
        have hu1 : u ∈ Submodule.span ↥(frobRange k p 1) (Set.range (evalPMon (p := p) 1 B)) :=
          hsp1 ▸ Submodule.mem_top
        have hmul_mon : ∀ (q : B →₀ Fin (p ^ 1)) (w : k),
            w ∈ Submodule.span ↥(frobRange k p (n + 1)) (Set.range (evalPMon (p := p) (n + 1) B)) →
            (evalPMon (p := p) 1 B q) ^ (p ^ n) * w ∈
              Submodule.span ↥(frobRange k p (n + 1)) (Set.range (evalPMon (p := p) (n + 1) B)) := by
          intro q w hw
          refine Submodule.span_induction (fun y hy => ?_) (by simp)
            (fun _ _ _ _ h1 h2 => by rw [mul_add]; exact Submodule.add_mem _ h1 h2)
            (fun c _ _ h1 => by
              rw [Algebra.smul_def, mul_left_comm, ← Algebra.smul_def]
              exact Submodule.smul_mem _ c h1) hw
          rcases hy with ⟨γ, rfl⟩
          have hqpow : (evalPMon (p := p) 1 B q) ^ (p ^ n) =
              evalPMon (p := p) (n + 1) B (combineRQ (p := p) n B 0 q) := by
            rw [evalPMon_combine]
            simp [evalPMon]
          rw [hqpow]
          obtain ⟨c, r', hc, hmul⟩ := evalPMon_mul_decomp (p := p) (n + 1) B (combineRQ (p := p) n B 0 q) γ
          rw [hmul]
          exact Submodule.smul_mem _ (⟨c, hc⟩ : ↥(frobRange k p (n + 1))) (Submodule.subset_span ⟨r', rfl⟩)
        have hmul_u : ∀ v : k,
            v ∈ Submodule.span ↥(frobRange k p 1) (Set.range (evalPMon (p := p) 1 B)) →
            v ^ (p ^ n) * z ∈
              Submodule.span ↥(frobRange k p (n + 1)) (Set.range (evalPMon (p := p) (n + 1) B)) := by
          intro v hv
          refine Submodule.span_induction (fun y hy => ?_)
            (by rw [zero_pow (pow_ne_zero n hp.out.ne_zero), zero_mul]; exact Submodule.zero_mem _)
            (fun v₁ v₂ _ _ h1 h2 => by
              have hadd : (v₁ + v₂) ^ (p ^ n) = v₁ ^ (p ^ n) + v₂ ^ (p ^ n) := by
                rw [← frobPow_apply, map_add, frobPow_apply, frobPow_apply]
              rw [hadd, add_mul]
              exact Submodule.add_mem _ h1 h2)
            (fun c v₁ _ h1 => by
              have hc : (c : k) ^ (p ^ n) ∈ frobRange k p (n + 1) := by
                obtain ⟨y, hy⟩ := (mem_frobRange_iff 1 (c : k)).mp c.2
                rw [pow_one] at hy
                rw [mem_frobRange_iff]
                exact ⟨y, by rw [pow_succ', pow_mul, hy]⟩
              have hsm : (c • v₁) ^ (p ^ n) * z =
                  (⟨(c : k) ^ (p ^ n), hc⟩ : ↥(frobRange k p (n + 1))) • (v₁ ^ (p ^ n) * z) := by
                change ((c : k) * v₁) ^ (p ^ n) * z = (c : k) ^ (p ^ n) * (v₁ ^ (p ^ n) * z)
                rw [mul_pow, mul_assoc]
              rw [hsm]
              exact Submodule.smul_mem _ _ h1) hv
          rcases hy with ⟨q, rfl⟩
          exact hmul_mon q z hz
        have hres := hmul_u u hu1
        rwa [hu] at hres

private lemma formallySmooth_zmod_of_charP
    (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    [Algebra (ZMod p) k] :
    Algebra.FormallySmooth (ZMod p) k := by
  classical
  refine Algebra.FormallySmooth.of_comp_surjective fun S _ _ I hI f => ?_
  by_cases hsub : Subsingleton S
  · refine ⟨{
      toFun := fun _ => 0
      map_one' := Subsingleton.elim _ _
      map_mul' := fun _ _ => Subsingleton.elim _ _
      map_zero' := rfl
      map_add' := fun _ _ => Subsingleton.elim _ _
      commutes' := fun _ => Subsingleton.elim _ _ }, ?_⟩
    ext x
    have : Subsingleton (S ⧸ I) := Quotient.instSubsingletonQuotient _
    exact Subsingleton.elim _ _
  have : Nontrivial S := not_subsingleton_iff_nontrivial.mp hsub
  have : CharP S p := (RingHom.charP_iff_charP (algebraMap (ZMod p) S) p).mp inferInstance
  have hker_frob : I ≤ RingHom.ker (frobenius S p) := by
    intro z hz
    rw [RingHom.mem_ker, frobenius_def]
    have hp2 : 2 ≤ p := hp.out.two_le
    have hzp : z ^ p ∈ I ^ 2 := Ideal.pow_le_pow_right hp2 (Ideal.pow_mem_pow hz p)
    rw [hI, Ideal.mem_bot] at hzp
    exact hzp
  let φ : S ⧸ I →+* S := Ideal.Quotient.lift I (frobenius S p) hker_frob
  have hφ_mk : ∀ s : S, φ (Ideal.Quotient.mk I s) = s ^ p := fun _ => rfl
  have hmk_φ : ∀ q : S ⧸ I, Ideal.Quotient.mk I (φ q) = q ^ p := fun q => by
    obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective q
    rw [hφ_mk, map_pow]
  have : NeZero (p ^ 1) := ⟨pow_ne_zero 1 hp.out.ne_zero⟩
  obtain ⟨B, hli, hsp⟩ := exists_pBasis k p
  let kp := frobRange k p 1
  let eFrob : k ≃+* ↥kp :=
    RingEquiv.ofBijective
      ((frobenius k p).codRestrict kp.toSubring fun x => (mem_frobRange_iff 1 _).mpr ⟨x, by rw [pow_one, frobenius_def]⟩)
      ⟨fun x y h => frobenius_inj k p (congrArg Subtype.val h),
        fun ⟨y, hy⟩ => by
          obtain ⟨x, hx⟩ := (mem_frobRange_iff 1 y).mp hy
          exact ⟨x, Subtype.ext (by simpa [frobenius_def, pow_one] using hx)⟩⟩
  let h : ↥kp →+* S := φ.comp (f.toRingHom.comp eFrob.symm.toRingHom)
  have hh_frob : ∀ x : k, h (eFrob x) = φ (f x) := fun x => by
    simp [h]
  have hmk_h : ∀ c : ↥kp, Ideal.Quotient.mk I (h c) = f (c : k) := fun c => by
    obtain ⟨x, rfl⟩ := eFrob.surjective c
    rw [hh_frob, hmk_φ, ← map_pow]
    rfl
  have hliftB : ∀ b : B, ∃ s : S, Ideal.Quotient.mk I s = f (b : k) :=
    fun b => Ideal.Quotient.mk_surjective (f (b : k))
  choose liftB hliftB_eq using hliftB
  have hliftB_pow : ∀ b : B, liftB b ^ p = h (eFrob (b : k)) := fun b => by
    rw [hh_frob, ← hliftB_eq b, hφ_mk]
  let liftMon : (B →₀ Fin (p ^ 1)) → S := fun α => α.prod fun b e => liftB b ^ (e : ℕ)
  have hmk_liftMon : ∀ α, Ideal.Quotient.mk I (liftMon α) = f (evalPMon (p := p) 1 B α) := by
    intro α
    dsimp only [liftMon, evalPMon]
    rw [Finsupp.prod, Finsupp.prod, map_prod, map_prod]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [map_pow, map_pow, hliftB_eq b]
  let bBasis : Module.Basis (B →₀ Fin (p ^ 1)) ↥kp k := Module.Basis.mk hli (le_of_eq hsp.symm)
  have hbBasis_apply : ∀ α, bBasis α = evalPMon (p := p) 1 B α := fun α => Module.Basis.mk_apply hli _ α
  let gFun : k → S := fun x => (bBasis.repr x).sum fun α c => h c * liftMon α
  have hg_add : ∀ x y : k, gFun (x + y) = gFun x + gFun y := fun x y => by
    dsimp only [gFun]
    rw [map_add, Finsupp.sum_add_index']
    · intro _; simp
    · intro _ _ _; rw [map_add, add_mul]
  have hg_smul : ∀ (c : ↥kp) (x : k), gFun (c • x) = h c * gFun x := fun c x => by
    dsimp only [gFun]
    rw [map_smul, Finsupp.sum_smul_index' (by intro _; simp)]
    dsimp only [Finsupp.sum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [smul_eq_mul, map_mul, mul_assoc]
  have hg_basis : ∀ α : B →₀ Fin (p ^ 1), gFun (evalPMon (p := p) 1 B α) = liftMon α := fun α => by
    dsimp only [gFun]
    rw [← hbBasis_apply α, bBasis.repr_self, Finsupp.sum_single_index (by simp), map_one, one_mul]
  have hg_one : gFun 1 = 1 := by
    have h1 : (1 : k) = evalPMon (p := p) 1 B 0 := by simp [evalPMon]
    rw [h1, hg_basis 0]
    simp [liftMon]
  have hmul_mon : ∀ α β : B →₀ Fin (p ^ 1),
      gFun (evalPMon (p := p) 1 B α * evalPMon (p := p) 1 B β) = liftMon α * liftMon β := by
    intro α β
    let Ssup := α.support ∪ β.support
    let q : B → ℕ := fun b => ((α b : ℕ) + (β b : ℕ)) / p
    let r : B →₀ Fin (p ^ 1) :=
      Finsupp.onFinset Ssup (fun b => ⟨((α b : ℕ) + (β b : ℕ)) % p,
        Nat.lt_of_lt_of_eq (Nat.mod_lt _ hp.out.pos) (pow_one p).symm⟩) (fun b hb => by
          by_contra hnot
          have ha0 : α b = 0 := Finsupp.notMem_support_iff.mp fun h => hnot (Finset.mem_union_left _ h)
          have hb0 : β b = 0 := Finsupp.notMem_support_iff.mp fun h => hnot (Finset.mem_union_right _ h)
          apply hb; ext; simp [ha0, hb0])
    let cprod : ↥kp := eFrob (∏ b ∈ Ssup, (b : k) ^ q b)
    have hprod_k : evalPMon (p := p) 1 B α * evalPMon (p := p) 1 B β = cprod • evalPMon (p := p) 1 B r := by
      dsimp only [evalPMon, cprod]
      change (α.prod fun b e => (b : k) ^ (e : ℕ)) * (β.prod fun b e => (b : k) ^ (e : ℕ)) =
        (∏ b ∈ Ssup, (b : k) ^ q b) ^ p * (r.prod fun b e => (b : k) ^ (e : ℕ))
      have hαS : α.prod (fun b e => (b : k) ^ (e : ℕ)) = ∏ b ∈ Ssup, (b : k) ^ (α b : ℕ) := by
        rw [Finsupp.prod]
        refine Finset.prod_subset Finset.subset_union_left fun b _ hb => ?_
        rw [Finsupp.notMem_support_iff.mp hb]; simp
      have hβS : β.prod (fun b e => (b : k) ^ (e : ℕ)) = ∏ b ∈ Ssup, (b : k) ^ (β b : ℕ) := by
        rw [Finsupp.prod]
        refine Finset.prod_subset Finset.subset_union_right fun b _ hb => ?_
        rw [Finsupp.notMem_support_iff.mp hb]; simp
      have hrS : r.prod (fun b e => (b : k) ^ (e : ℕ)) = ∏ b ∈ Ssup, (b : k) ^ (r b : ℕ) := by
        rw [Finsupp.prod]
        refine Finset.prod_subset Finsupp.support_onFinset_subset fun b _ hb => ?_
        rw [Finsupp.notMem_support_iff.mp hb]; simp
      rw [hαS, hβS, hrS, ← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [← pow_add, ← pow_mul, ← pow_add]
      congr 1
      dsimp only [q, r, Finsupp.onFinset_apply]
      exact (Nat.div_add_mod' ((α b : ℕ) + (β b : ℕ)) p).symm
    rw [hprod_k, hg_smul, hg_basis]
    have hc_S : h cprod = ∏ b ∈ Ssup, (liftB b ^ q b) ^ p := by
      dsimp only [cprod]
      rw [map_prod, map_prod]
      refine Finset.prod_congr rfl fun b _ => ?_
      rw [map_pow, map_pow, ← hliftB_pow b, ← pow_mul, ← pow_mul, mul_comm]
    rw [hc_S]
    dsimp only [liftMon]
    have hαS : α.prod (fun b e => liftB b ^ (e : ℕ)) = ∏ b ∈ Ssup, liftB b ^ (α b : ℕ) := by
      rw [Finsupp.prod]
      refine Finset.prod_subset Finset.subset_union_left fun b _ hb => ?_
      rw [Finsupp.notMem_support_iff.mp hb]; simp
    have hβS : β.prod (fun b e => liftB b ^ (e : ℕ)) = ∏ b ∈ Ssup, liftB b ^ (β b : ℕ) := by
      rw [Finsupp.prod]
      refine Finset.prod_subset Finset.subset_union_right fun b _ hb => ?_
      rw [Finsupp.notMem_support_iff.mp hb]; simp
    have hrS : r.prod (fun b e => liftB b ^ (e : ℕ)) = ∏ b ∈ Ssup, liftB b ^ (r b : ℕ) := by
      rw [Finsupp.prod]
      refine Finset.prod_subset Finsupp.support_onFinset_subset fun b _ hb => ?_
      rw [Finsupp.notMem_support_iff.mp hb]; simp
    rw [hαS, hβS, hrS, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [← pow_add, ← pow_mul, ← pow_add]
    congr 1
    dsimp only [q, r, Finsupp.onFinset_apply]
    exact Nat.div_add_mod' ((α b : ℕ) + (β b : ℕ)) p
  have hg_mul : ∀ x y : k, gFun (x * y) = gFun x * gFun y := by
    intro x y
    have hx : x = ∑ α ∈ (bBasis.repr x).support, (bBasis.repr x α) • evalPMon (p := p) 1 B α := by
      have hlin := bBasis.linearCombination_repr x
      simpa only [Finsupp.linearCombination_apply, Finsupp.sum, hbBasis_apply] using hlin.symm
    have hy : y = ∑ β ∈ (bBasis.repr y).support, (bBasis.repr y β) • evalPMon (p := p) 1 B β := by
      have hlin := bBasis.linearCombination_repr y
      simpa only [Finsupp.linearCombination_apply, Finsupp.sum, hbBasis_apply] using hlin.symm
    have hg_sum : ∀ {ι : Type _} (t : Finset ι) (u : ι → k), gFun (∑ i ∈ t, u i) = ∑ i ∈ t, gFun (u i) := by
      intro ι t u
      induction t using Finset.induction_on with
      | empty => simp [gFun]
      | insert a t ha ih => rw [Finset.sum_insert ha, hg_add, ih, Finset.sum_insert ha]
    conv_lhs => rw [hx, hy]
    rw [Finset.sum_mul]
    rw [hg_sum]
    conv_rhs => rw [hx, hy]
    rw [hg_sum, hg_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [Finset.mul_sum, hg_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun β _ => ?_
    have hsm : (bBasis.repr x α • evalPMon (p := p) 1 B α) * (bBasis.repr y β • evalPMon (p := p) 1 B β) =
        (bBasis.repr x α * bBasis.repr y β) • (evalPMon (p := p) 1 B α * evalPMon (p := p) 1 B β) := by
      change ((bBasis.repr x α : k) * evalPMon (p := p) 1 B α) *
          ((bBasis.repr y β : k) * evalPMon (p := p) 1 B β) =
        ((bBasis.repr x α : k) * (bBasis.repr y β : k)) *
          (evalPMon (p := p) 1 B α * evalPMon (p := p) 1 B β)
      ring
    rw [hsm, hg_smul, hg_smul, hg_smul, hg_basis, hg_basis, hmul_mon, map_mul]
    ring
  let gRing : k →+* S :=
    { toFun := gFun
      map_one' := hg_one
      map_mul' := hg_mul
      map_zero' := by simp [gFun]
      map_add' := hg_add }
  let gAlg : k →ₐ[ZMod p] S :=
    { toRingHom := gRing
      commutes' := fun z => by
        rw [← ZMod.natCast_zmod_val z]
        change gRing (algebraMap (ZMod p) k (z.val : ZMod p)) = algebraMap (ZMod p) S (z.val : ZMod p)
        rw [map_natCast, map_natCast, map_natCast] }
  refine ⟨gAlg, ?_⟩
  ext x
  change Ideal.Quotient.mk I (gFun x) = f x
  have hx : x = ∑ α ∈ (bBasis.repr x).support, (bBasis.repr x α) • evalPMon (p := p) 1 B α := by
    have hlin := bBasis.linearCombination_repr x
    simpa only [Finsupp.linearCombination_apply, Finsupp.sum, hbBasis_apply] using hlin.symm
  dsimp only [gFun, Finsupp.sum]
  rw [map_sum]
  conv_rhs => rw [hx, map_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [map_mul, hmk_h, hmk_liftMon, ← map_mul]
  rfl

/-!
Part 5: Explicit Cohen Ring in Witt Vectors and Square-Zero Lifting
-/

private noncomputable def wittFrobSubring (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (n : ℕ) : Subring (WittVector p (AlgebraicClosure k)) :=
  (WittVector.map ((algebraMap k (AlgebraicClosure k)).comp (frobRange k p n).subtype)).range

private lemma mem_wittFrobSubring_iff {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (n : ℕ) (w : WittVector p (AlgebraicClosure k)) :
    w ∈ wittFrobSubring k p n ↔
      ∀ i : ℕ, ∃ y : k, algebraMap k (AlgebraicClosure k) (y ^ (p ^ n)) = w.coeff i := by
  let ιK := algebraMap k (AlgebraicClosure k)
  constructor
  · rintro ⟨v, rfl⟩ i
    rw [WittVector.map_coeff]
    obtain ⟨y, hy⟩ := (mem_frobRange_iff n (v.coeff i : k)).mp (v.coeff i).2
    exact ⟨y, by change ιK (y ^ (p ^ n)) = ιK (v.coeff i : k); rw [hy]⟩
  · intro h
    choose y hy using h
    let v : WittVector p ↥(frobRange k p n) :=
      WittVector.mk p fun i => ⟨y i ^ (p ^ n), (mem_frobRange_iff n _).mpr ⟨y i, rfl⟩⟩
    refine ⟨v, ?_⟩
    ext i
    rw [WittVector.map_coeff, WittVector.coeff_mk]
    exact hy i

private lemma witt_p_mul_coeff_succ {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] [CharP R p]
    (w : WittVector p R) (i : ℕ) :
    ((p : WittVector p R) * w).coeff (i + 1) = (w.coeff i) ^ p := by
  rw [mul_comm, ← WittVector.verschiebung_frobenius, WittVector.verschiebung_coeff_succ,
    WittVector.coeff_frobenius_charP]

private lemma witt_p_ne_zero (K : Type u) [Field K] (p : ℕ) [Fact p.Prime] [CharP K p] :
    (p : WittVector p K) ≠ 0 := by
  intro h0
  have h1 := congrArg (fun w : WittVector p K => w.coeff 1) h0
  have h2 : ((p : WittVector p K) * 1).coeff 1 = ((1 : WittVector p K).coeff 0) ^ p :=
    witt_p_mul_coeff_succ 1 0
  rw [mul_one] at h2
  rw [h2, WittVector.one_coeff_zero, one_pow, WittVector.zero_coeff] at h1
  exact one_ne_zero h1

private lemma p_mul_mem_wittFrobSubring_succ
    {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (n : ℕ) {w : WittVector p (AlgebraicClosure k)} (hw : w ∈ wittFrobSubring k p n) :
    (p : WittVector p (AlgebraicClosure k)) * w ∈ wittFrobSubring k p (n + 1) := by
  rw [mem_wittFrobSubring_iff] at hw ⊢
  intro i
  cases i with
  | zero =>
    refine ⟨0, ?_⟩
    rw [zero_pow (pow_ne_zero (n + 1) (Fact.out : p.Prime).ne_zero), map_zero, mul_comm,
      WittVector.mul_charP_coeff_zero]
  | succ j =>
    obtain ⟨y, hy⟩ := hw j
    refine ⟨y, ?_⟩
    rw [witt_p_mul_coeff_succ, ← hy, ← map_pow, ← pow_mul, pow_succ]

private lemma wittFrobSubring_antitone
    {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p] (n : ℕ) :
    wittFrobSubring k p (n + 1) ≤ wittFrobSubring k p n := by
  intro w hw
  rw [mem_wittFrobSubring_iff] at hw ⊢
  intro i
  obtain ⟨y, hy⟩ := hw i
  exact ⟨y ^ p, by rw [← pow_mul, ← pow_succ', hy]⟩

private noncomputable def teichMon {k : Type u} [Field k] (p : ℕ) [Fact p.Prime]
    (n : ℕ) (B : Set k) (α : B →₀ Fin (p ^ n)) : WittVector p (AlgebraicClosure k) :=
  WittVector.teichmuller p (algebraMap k (AlgebraicClosure k) (evalPMon (p := p) n B α))

private lemma teichmuller_alg_mul {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] (a b : k) :
    WittVector.teichmuller p (algebraMap k (AlgebraicClosure k) a) *
      WittVector.teichmuller p (algebraMap k (AlgebraicClosure k) b) =
    WittVector.teichmuller p (algebraMap k (AlgebraicClosure k) (a * b)) := by
  rw [map_mul, map_mul]

private lemma teichmuller_mem_wittFrobSubring
    {k : Type u} [Field k] {p : ℕ} [Fact p.Prime] [CharP k p]
    (n : ℕ) {c : k} (hc : c ∈ frobRange k p n) :
    WittVector.teichmuller p (algebraMap k (AlgebraicClosure k) c) ∈ wittFrobSubring k p n := by
  refine ⟨WittVector.teichmuller p (⟨c, hc⟩ : ↥(frobRange k p n)), ?_⟩
  rw [WittVector.map_teichmuller]
  rfl

private noncomputable def cohenLayerMod (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    (B : Set k) (n : ℕ) :
    Submodule ↥(wittFrobSubring k p n) (WittVector p (AlgebraicClosure k)) :=
  Submodule.span ↥(wittFrobSubring k p n) (Set.range (teichMon p n B))

private noncomputable def cohenLayerSubring (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (B : Set k) (n : ℕ) : Subring (WittVector p (AlgebraicClosure k)) where
  carrier := cohenLayerMod k p B n
  zero_mem' := (cohenLayerMod k p B n).zero_mem
  add_mem' := fun hu hv => (cohenLayerMod k p B n).add_mem hu hv
  neg_mem' := fun hu => (cohenLayerMod k p B n).neg_mem hu
  one_mem' := by
    have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
    have h1 : teichMon (k := k) p n B 0 = 1 := by
      simp [teichMon, evalPMon]
    rw [← h1]
    exact Submodule.subset_span ⟨0, rfl⟩
  mul_mem' := fun {u v} hu hv => by
    refine Submodule.span_induction (fun x hx => ?_) (by simp)
      (fun a b _ _ ha hb => by rw [add_mul]; exact (cohenLayerMod k p B n).add_mem ha hb)
      (fun c a _ ha => by
        rw [Algebra.smul_def, mul_assoc, ← Algebra.smul_def]
        exact (cohenLayerMod k p B n).smul_mem c ha) hu
    rcases hx with ⟨α, rfl⟩
    refine Submodule.span_induction (fun y hy => ?_) (by simp)
      (fun a b _ _ ha hb => by rw [mul_add]; exact (cohenLayerMod k p B n).add_mem ha hb)
      (fun c a _ ha => by
        rw [Algebra.smul_def, mul_left_comm, ← Algebra.smul_def]
        exact (cohenLayerMod k p B n).smul_mem c ha) hv
    rcases hy with ⟨β, rfl⟩
    obtain ⟨c, r, hc, hmul⟩ := evalPMon_mul_decomp (p := p) n B α β
    have hteich : teichMon p n B α * teichMon p n B β =
        (⟨WittVector.teichmuller p (algebraMap k (AlgebraicClosure k) c),
          teichmuller_mem_wittFrobSubring n hc⟩ : ↥(wittFrobSubring k p n)) • teichMon p n B r := by
      change WittVector.teichmuller p (algebraMap k (AlgebraicClosure k) (evalPMon (p := p) n B α)) *
          WittVector.teichmuller p (algebraMap k (AlgebraicClosure k) (evalPMon (p := p) n B β)) =
        WittVector.teichmuller p (algebraMap k (AlgebraicClosure k) c) *
          WittVector.teichmuller p (algebraMap k (AlgebraicClosure k) (evalPMon (p := p) n B r))
      rw [teichmuller_alg_mul, teichmuller_alg_mul, hmul]
    rw [hteich]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)

private lemma wittFrobSubring_le_cohenLayer
    {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p] (B : Set k) (n : ℕ) :
    wittFrobSubring k p n ≤ cohenLayerSubring k p B n := by
  intro w hw
  have h1 : (1 : WittVector p (AlgebraicClosure k)) ∈ cohenLayerMod k p B n :=
    (cohenLayerSubring k p B n).one_mem
  have hsm := (cohenLayerMod k p B n).smul_mem ⟨w, hw⟩ h1
  change w * 1 ∈ cohenLayerMod k p B n at hsm
  rwa [mul_one] at hsm

private lemma cohenLayer_antitone
    {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p] (B : Set k) (n : ℕ) :
    cohenLayerSubring k p B (n + 1) ≤ cohenLayerSubring k p B n := by
  intro x hx
  refine Submodule.span_induction (fun y hy => ?_) (Submodule.zero_mem _)
    (fun _ _ _ _ h1 h2 => Submodule.add_mem _ h1 h2)
    (fun c _ _ h1 => by
      have hc : (c : WittVector p (AlgebraicClosure k)) ∈ wittFrobSubring k p n :=
        wittFrobSubring_antitone n c.2
      exact (cohenLayerMod k p B n).smul_mem ⟨c.1, hc⟩ h1) hx
  rcases hy with ⟨γ, rfl⟩
  have hsplit := evalPMon_split (p := p) n B γ
  have hcq : (evalPMon (p := p) 1 B (splitQ (p := p) n B γ)) ^ (p ^ n) ∈ frobRange k p n :=
    (mem_frobRange_iff n _).mpr ⟨_, rfl⟩
  have hteich : teichMon p (n + 1) B γ =
      (⟨WittVector.teichmuller p (algebraMap k (AlgebraicClosure k)
          ((evalPMon (p := p) 1 B (splitQ (p := p) n B γ)) ^ (p ^ n))),
        teichmuller_mem_wittFrobSubring n hcq⟩ : ↥(wittFrobSubring k p n)) •
        teichMon p n B (splitR (p := p) n B γ) := by
    change WittVector.teichmuller p (algebraMap k (AlgebraicClosure k) (evalPMon (p := p) (n + 1) B γ)) =
      WittVector.teichmuller p (algebraMap k (AlgebraicClosure k)
        ((evalPMon (p := p) 1 B (splitQ (p := p) n B γ)) ^ (p ^ n))) *
      WittVector.teichmuller p (algebraMap k (AlgebraicClosure k)
        (evalPMon (p := p) n B (splitR (p := p) n B γ)))
    rw [teichmuller_alg_mul, hsplit]
  rw [hteich]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨splitR (p := p) n B γ, rfl⟩)

private lemma p_mul_mem_cohenLayer_succ
    {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p] (B : Set k) (n : ℕ)
    {x : WittVector p (AlgebraicClosure k)} (hx : x ∈ cohenLayerSubring k p B n) :
    (p : WittVector p (AlgebraicClosure k)) * x ∈ cohenLayerSubring k p B (n + 1) := by
  have : NeZero (p ^ 1) := ⟨pow_ne_zero 1 hp.out.ne_zero⟩
  have : NeZero (p ^ n) := ⟨pow_ne_zero n hp.out.ne_zero⟩
  have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) hp.out.ne_zero⟩
  change x ∈ cohenLayerMod k p B n at hx
  rw [cohenLayerMod, Finsupp.mem_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, rfl⟩ := hx
  rw [Finsupp.sum, Finset.mul_sum]
  refine (cohenLayerSubring k p B (n + 1)).sum_mem fun α _ => ?_
  have hcomb : teichMon p (n + 1) B (combineRQ (p := p) n B α 0) = teichMon p n B α := by
    dsimp only [teichMon]
    rw [evalPMon_combine]
    simp [evalPMon]
  have hpc : (p : WittVector p (AlgebraicClosure k)) * (c α : WittVector p (AlgebraicClosure k)) ∈
      wittFrobSubring k p (n + 1) := p_mul_mem_wittFrobSubring_succ n (c α).2
  have hterm : (p : WittVector p (AlgebraicClosure k)) * (c α • teichMon p n B α) =
      (⟨(p : WittVector p (AlgebraicClosure k)) * (c α : WittVector p (AlgebraicClosure k)), hpc⟩ :
        ↥(wittFrobSubring k p (n + 1))) • teichMon p (n + 1) B (combineRQ (p := p) n B α 0) := by
    rw [hcomb]
    change (p : WittVector p (AlgebraicClosure k)) * ((c α : WittVector p (AlgebraicClosure k)) * teichMon p n B α) =
      ((p : WittVector p (AlgebraicClosure k)) * (c α : WittVector p (AlgebraicClosure k))) * teichMon p n B α
    rw [mul_assoc]
  rw [hterm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨combineRQ (p := p) n B α 0, rfl⟩)

private lemma cohenLayer_coeff_zero_mem_range
    {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p] (B : Set k) (n : ℕ)
    {x : WittVector p (AlgebraicClosure k)} (hx : x ∈ cohenLayerSubring k p B n) :
    x.coeff 0 ∈ Set.range (algebraMap k (AlgebraicClosure k)) := by
  let ιK := algebraMap k (AlgebraicClosure k)
  change x ∈ cohenLayerMod k p B n at hx
  refine Submodule.span_induction (fun y hy => ?_) ⟨0, by rw [map_zero, WittVector.zero_coeff]⟩
    (fun a b _ _ ⟨ua, hua⟩ ⟨ub, hub⟩ => ⟨ua + ub, by
      rw [map_add, ← WittVector.constantCoeff_apply, map_add, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, hua, hub]⟩)
    (fun c a _ ⟨ua, hua⟩ => by
      obtain ⟨y, hy⟩ := (mem_wittFrobSubring_iff n c.1).mp c.2 0
      refine ⟨y ^ (p ^ n) * ua, ?_⟩
      change ιK (y ^ (p ^ n) * ua) = (c.1 * a).coeff 0
      rw [map_mul, ← WittVector.constantCoeff_apply, map_mul, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, hy, hua]) hx
  rcases hy with ⟨α, rfl⟩
  exact ⟨evalPMon (p := p) n B α, by simp [teichMon, WittVector.teichmuller_coeff_zero]⟩

private lemma exists_cohenLayer_coeff_zero
    {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p] {B : Set k} (n : ℕ)
    (hsp : Submodule.span ↥(frobRange k p n) (Set.range (evalPMon (p := p) n B)) = ⊤)
    (a : k) :
    ∃ y ∈ cohenLayerSubring k p B n, y.coeff 0 = algebraMap k (AlgebraicClosure k) a := by
  have ha : a ∈ Submodule.span ↥(frobRange k p n) (Set.range (evalPMon (p := p) n B)) :=
    hsp ▸ Submodule.mem_top
  refine Submodule.span_induction (fun x hx => ?_)
    ⟨0, (cohenLayerSubring k p B n).zero_mem, by simp⟩
    (fun u v _ _ ⟨yu, hyu, hcu⟩ ⟨yv, hyv, hcv⟩ => ⟨yu + yv, (cohenLayerSubring k p B n).add_mem hyu hyv, by
      rw [← WittVector.constantCoeff_apply, map_add, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, hcu, hcv, map_add]⟩)
    (fun c u _ ⟨yu, hyu, hcu⟩ => by
      let tc : WittVector p (AlgebraicClosure k) :=
        WittVector.teichmuller p (algebraMap k (AlgebraicClosure k) (c : k))
      have htc : tc ∈ wittFrobSubring k p n := teichmuller_mem_wittFrobSubring n c.2
      refine ⟨tc * yu, (cohenLayerSubring k p B n).mul_mem (wittFrobSubring_le_cohenLayer B n htc) hyu, ?_⟩
      rw [← WittVector.constantCoeff_apply, map_mul, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, hcu]
      change (WittVector.teichmuller p (algebraMap k (AlgebraicClosure k) (c : k))).coeff 0 * _ =
        algebraMap k (AlgebraicClosure k) ((c : k) * u)
      rw [WittVector.teichmuller_coeff_zero, map_mul]) ha
  rcases hx with ⟨α, rfl⟩
  exact ⟨teichMon p n B α, Submodule.subset_span ⟨α, rfl⟩, by simp [teichMon, WittVector.teichmuller_coeff_zero]⟩

private lemma div_p_of_mem_cohenLayer_succ
    {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p] {B : Set k} (n : ℕ)
    (hli : LinearIndependent ↥(frobRange k p (n + 1)) (evalPMon (p := p) (n + 1) B))
    {x : WittVector p (AlgebraicClosure k)} (hx : x ∈ cohenLayerSubring k p B (n + 1))
    (hx0 : x.coeff 0 = 0) :
    ∃ u ∈ cohenLayerSubring k p B n, x = (p : WittVector p (AlgebraicClosure k)) * u := by
  classical
  let K := AlgebraicClosure k
  let ιK := algebraMap k K
  have hι_inj : Function.Injective ιK := RingHom.injective ιK
  change x ∈ cohenLayerMod k p B (n + 1) at hx
  rw [cohenLayerMod, Finsupp.mem_span_range_iff_exists_finsupp] at hx
  obtain ⟨c, rfl⟩ := hx
  have hcoeff : ∀ α : B →₀ Fin (p ^ (n + 1)), ∃ a : ↥(frobRange k p (n + 1)), ιK (a : k) = (c α).1.coeff 0 := by
    intro α
    obtain ⟨y, hy⟩ := (mem_wittFrobSubring_iff (n + 1) (c α).1).mp (c α).2 0
    exact ⟨⟨y ^ (p ^ (n + 1)), (mem_frobRange_iff (n + 1) _).mpr ⟨y, rfl⟩⟩, hy⟩
  choose a ha using hcoeff
  have hsum0 : ∑ α ∈ c.support, a α • evalPMon (p := p) (n + 1) B α = 0 := by
    apply hι_inj
    rw [map_zero, map_sum]
    have h0 : (c.sum fun α w => w • teichMon p (n + 1) B α).coeff 0 = 0 := hx0
    rw [← WittVector.constantCoeff_apply, Finsupp.sum, map_sum] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun α _ => ?_
    change ιK ((a α : k) * evalPMon (p := p) (n + 1) B α) =
      WittVector.constantCoeff ((c α).1 * teichMon p (n + 1) B α)
    rw [map_mul, map_mul, ha α, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply]
    dsimp only [ιK, teichMon]
    rw [WittVector.teichmuller_coeff_zero]
  have ha0 : ∀ α ∈ c.support, a α = 0 := (linearIndependent_iff'.mp hli) c.support a hsum0
  have hdivW : ∀ α ∈ c.support, ∃ y : WittVector p K, y ∈ wittFrobSubring k p n ∧ (c α).1 = (p : WittVector p K) * y := by
    intro α hα
    have hker : (c α).1 ∈ RingHom.ker (WittVector.constantCoeff (p := p) (R := K)) := by
      rw [RingHom.mem_ker, WittVector.constantCoeff_apply, ← ha α, ha0 α hα]
      simp
    rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at hker
    obtain ⟨y, hy⟩ := hker
    refine ⟨y, ?_, hy⟩
    rw [mem_wittFrobSubring_iff]
    intro i
    obtain ⟨z, hz⟩ := (mem_wittFrobSubring_iff (n + 1) (c α).1).mp (c α).2 (i + 1)
    refine ⟨z, ?_⟩
    have hfrob_eq : (y.coeff i) ^ p = (ιK (z ^ (p ^ n))) ^ p := by
      rw [← witt_p_mul_coeff_succ y i, ← hy, ← hz, ← map_pow, ← pow_mul, ← pow_succ]
    exact (frobenius_inj K p (by simpa [frobenius_def] using hfrob_eq.symm))
  let yFun : (B →₀ Fin (p ^ (n + 1))) → WittVector p K := fun α =>
    if h : α ∈ c.support then (hdivW α h).choose else 0
  have hy_mem : ∀ α ∈ c.support, yFun α ∈ wittFrobSubring k p n := fun α hα => by
    dsimp only [yFun]
    simp only [hα, ↓reduceDIte]
    exact (hdivW α hα).choose_spec.1
  have hy_eq : ∀ α ∈ c.support, (c α).1 = (p : WittVector p K) * yFun α := fun α hα => by
    dsimp only [yFun]
    simp only [hα, ↓reduceDIte]
    exact (hdivW α hα).choose_spec.2
  refine ⟨∑ α ∈ c.support, yFun α * teichMon p (n + 1) B α, ?_, ?_⟩
  · refine (cohenLayerSubring k p B n).sum_mem fun α hα => ?_
    refine (cohenLayerSubring k p B n).mul_mem (wittFrobSubring_le_cohenLayer B n (hy_mem α hα)) ?_
    exact cohenLayer_antitone B n (Submodule.subset_span ⟨α, rfl⟩)
  · rw [Finsupp.sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α hα => ?_
    change (c α).1 * teichMon p (n + 1) B α = (p : WittVector p K) * (yFun α * teichMon p (n + 1) B α)
    rw [hy_eq α hα, mul_assoc]

private lemma cohenLayer_approx_succ
    {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p] {B : Set k}
    (hli : ∀ n, LinearIndependent ↥(frobRange k p n) (evalPMon (p := p) n B))
    (hsp : ∀ n, Submodule.span ↥(frobRange k p n) (Set.range (evalPMon (p := p) n B)) = ⊤) :
    ∀ (n : ℕ) {x : WittVector p (AlgebraicClosure k)}, x ∈ cohenLayerSubring k p B (n + 1) →
      ∃ y ∈ cohenLayerSubring k p B (n + 2),
        x - y ∈ Ideal.span {(p : WittVector p (AlgebraicClosure k))} ^ (n + 1) := by
  intro n
  induction n with
  | zero =>
    intro x hx
    obtain ⟨a, ha⟩ := cohenLayer_coeff_zero_mem_range B 1 hx
    obtain ⟨y, hyM, hy0⟩ := exists_cohenLayer_coeff_zero 2 (hsp 2) a
    refine ⟨y, hyM, ?_⟩
    rw [pow_one, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, hy0, ha, sub_self]
  | succ n ih =>
    intro x hx
    obtain ⟨a, ha⟩ := cohenLayer_coeff_zero_mem_range B (n + 2) hx
    obtain ⟨y, hyM, hy0⟩ := exists_cohenLayer_coeff_zero (n + 3) (hsp (n + 3)) a
    have hxyM : x - y ∈ cohenLayerSubring k p B (n + 2) :=
      (cohenLayerSubring k p B (n + 2)).sub_mem hx (cohenLayer_antitone B (n + 2) hyM)
    have hxy0 : (x - y).coeff 0 = 0 := by
      rw [← WittVector.constantCoeff_apply, map_sub, WittVector.constantCoeff_apply,
        WittVector.constantCoeff_apply, hy0, ha, sub_self]
    obtain ⟨u, huM, hxy_eq⟩ := div_p_of_mem_cohenLayer_succ (n + 1) (hli (n + 2)) hxyM hxy0
    obtain ⟨u', hu'M, huu'⟩ := ih huM
    refine ⟨y + (p : WittVector p (AlgebraicClosure k)) * u',
      (cohenLayerSubring k p B (n + 3)).add_mem hyM (p_mul_mem_cohenLayer_succ B (n + 2) hu'M), ?_⟩
    have hdiff : x - (y + (p : WittVector p (AlgebraicClosure k)) * u') =
        (p : WittVector p (AlgebraicClosure k)) * (u - u') := by
      linear_combination hxy_eq
    rw [hdiff, pow_succ']
    exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton _)) huu'

private noncomputable def cohenApproxSubring (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (B : Set k) (n : ℕ) : Subring (WittVector p (AlgebraicClosure k)) where
  carrier := { w | ∃ x ∈ cohenLayerSubring k p B n,
    w - x ∈ Ideal.span {(p : WittVector p (AlgebraicClosure k))} ^ n }
  zero_mem' := ⟨0, (cohenLayerSubring k p B n).zero_mem, by simp⟩
  one_mem' := ⟨1, (cohenLayerSubring k p B n).one_mem, by simp⟩
  add_mem' := fun {a b} ⟨x, hxM, hxa⟩ ⟨y, hyM, hyb⟩ => ⟨x + y, (cohenLayerSubring k p B n).add_mem hxM hyM, by
    have heq : a + b - (x + y) = (a - x) + (b - y) := by ring
    rw [heq]
    exact Ideal.add_mem _ hxa hyb⟩
  neg_mem' := fun {a} ⟨x, hxM, hxa⟩ => ⟨-x, (cohenLayerSubring k p B n).neg_mem hxM, by
    have heq : -a - -x = -(a - x) := by ring
    rw [heq]
    exact (Ideal.neg_mem_iff _).mpr hxa⟩
  mul_mem' := fun {a b} ⟨x, hxM, hxa⟩ ⟨y, hyM, hyb⟩ => ⟨x * y, (cohenLayerSubring k p B n).mul_mem hxM hyM, by
    have heq : a * b - x * y = (a - x) * b + x * (b - y) := by ring
    rw [heq]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hxa) (Ideal.mul_mem_left _ _ hyb)⟩

private noncomputable def cohenSubring (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p]
    (B : Set k) : Subring (WittVector p (AlgebraicClosure k)) :=
  ⨅ n : ℕ, cohenApproxSubring k p B (n + 1)

private lemma mem_cohenSubring_iff {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]
    (B : Set k) (w : WittVector p (AlgebraicClosure k)) :
    w ∈ cohenSubring k p B ↔
      ∀ n : ℕ, ∃ x ∈ cohenLayerSubring k p B (n + 1),
        w - x ∈ Ideal.span {(p : WittVector p (AlgebraicClosure k))} ^ (n + 1) := by
  simp only [cohenSubring, Subring.mem_iInf]
  rfl

private lemma cohenSubring_closed
    {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p] {B : Set k}
    {w : WittVector p (AlgebraicClosure k)}
    (h : ∀ n : ℕ, ∃ v ∈ cohenSubring k p B,
      w - v ∈ Ideal.span {(p : WittVector p (AlgebraicClosure k))} ^ (n + 1)) :
    w ∈ cohenSubring k p B := by
  rw [mem_cohenSubring_iff]
  intro n
  obtain ⟨v, hvC, hwv⟩ := h n
  obtain ⟨x, hxM, hvx⟩ := (mem_cohenSubring_iff B v).mp hvC n
  refine ⟨x, hxM, ?_⟩
  have heq : w - x = (w - v) + (v - x) := by ring
  rw [heq]
  exact Ideal.add_mem _ hwv hvx

private lemma cohenSubring_p_saturated
    {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p] {B : Set k}
    (hli : ∀ n, LinearIndependent ↥(frobRange k p n) (evalPMon (p := p) n B))
    {w : WittVector p (AlgebraicClosure k)}
    (hpw : (p : WittVector p (AlgebraicClosure k)) * w ∈ cohenSubring k p B) :
    w ∈ cohenSubring k p B := by
  let K := AlgebraicClosure k
  let W := WittVector p K
  have hp0 : (p : W) ≠ 0 := witt_p_ne_zero K p
  rw [mem_cohenSubring_iff] at hpw ⊢
  intro n
  obtain ⟨x, hxM, hdiff⟩ := hpw (n + 1)
  have hx0 : x.coeff 0 = 0 := by
    have hmem1 : (p : W) * w - x ∈ Ideal.span {(p : W)} :=
      Ideal.pow_le_self (Nat.succ_ne_zero _) hdiff
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, sub_eq_zero,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, mul_comm,
      WittVector.mul_charP_coeff_zero] at hmem1
    exact hmem1.symm
  obtain ⟨u, huM, hxu⟩ := div_p_of_mem_cohenLayer_succ (n + 1) (hli (n + 2)) hxM hx0
  refine ⟨u, huM, ?_⟩
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hdiff ⊢
  obtain ⟨v, hv⟩ := hdiff
  refine ⟨v, ?_⟩
  apply mul_left_cancel₀ hp0
  calc
    (p : W) * (w - u) = (p : W) * w - x := by rw [mul_sub, hxu]
    _ = (p : W) ^ (n + 2) * v := hv
    _ = (p : W) * ((p : W) ^ (n + 1) * v) := by rw [pow_succ', mul_assoc]

private lemma cohenSubring_p_pow_saturated
    {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p] {B : Set k}
    (hli : ∀ n, LinearIndependent ↥(frobRange k p n) (evalPMon (p := p) n B)) :
    ∀ (m : ℕ) {w : WittVector p (AlgebraicClosure k)},
      (p : WittVector p (AlgebraicClosure k)) ^ m * w ∈ cohenSubring k p B → w ∈ cohenSubring k p B := by
  intro m
  induction m with
  | zero => intro w hw; simpa using hw
  | succ m ih =>
    intro w hw
    rw [pow_succ', mul_assoc] at hw
    exact ih (cohenSubring_p_saturated hli hw)

private lemma cohenSubring_coeff_zero_mem_range
    {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p] {B : Set k}
    {w : WittVector p (AlgebraicClosure k)} (hw : w ∈ cohenSubring k p B) :
    w.coeff 0 ∈ Set.range (algebraMap k (AlgebraicClosure k)) := by
  obtain ⟨x, hxM, hwx⟩ := (mem_cohenSubring_iff B w).mp hw 0
  rw [pow_one, ← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, sub_eq_zero,
    WittVector.constantCoeff_apply, WittVector.constantCoeff_apply] at hwx
  rw [hwx]
  exact cohenLayer_coeff_zero_mem_range B 1 hxM

private lemma cohenSubring_surj_coeff_zero
    {k : Type u} [Field k] {p : ℕ} [hp : Fact p.Prime] [CharP k p] {B : Set k}
    (hli : ∀ n, LinearIndependent ↥(frobRange k p n) (evalPMon (p := p) n B))
    (hsp : ∀ n, Submodule.span ↥(frobRange k p n) (Set.range (evalPMon (p := p) n B)) = ⊤)
    (a : k) :
    ∃ w ∈ cohenSubring k p B, w.coeff 0 = algebraMap k (AlgebraicClosure k) a := by
  let K := AlgebraicClosure k
  let W := WittVector p K
  obtain ⟨x₀, hx₀M, hx₀0⟩ := exists_cohenLayer_coeff_zero 1 (hsp 1) a
  let seq : (n : ℕ) → { x : W // x ∈ cohenLayerSubring k p B (n + 1) } :=
    Nat.rec ⟨x₀, hx₀M⟩ fun n prev =>
      let hex := cohenLayer_approx_succ hli hsp n prev.2
      ⟨hex.choose, hex.choose_spec.1⟩
  have hstep : ∀ n : ℕ, (seq n).1 - (seq (n + 1)).1 ∈ Ideal.span {(p : W)} ^ (n + 1) := fun n =>
    (cohenLayer_approx_succ hli hsp n (seq n).2).choose_spec.2
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → (seq m).1 ≡ (seq n).1 [SMOD (Ideal.span {(p : W)} ^ m • ⊤ : Ideal W)] := by
    intro m n hmn
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem]
    induction hmn with
    | refl => simp
    | @step r hmr ih =>
      have hdiff : (seq m).1 - (seq (r + 1)).1 = ((seq m).1 - (seq r).1) + ((seq r).1 - (seq (r + 1)).1) := by ring
      rw [hdiff]
      refine Ideal.add_mem _ ih ?_
      exact Ideal.pow_le_pow_right (Nat.le_succ_of_le hmr) (hstep r)
  obtain ⟨w, hw⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : W)}) (fun n => (seq n).1) (fun {m n} h => hcauchy h)
  have hw_sub : ∀ n : ℕ, w - (seq n).1 ∈ Ideal.span {(p : W)} ^ n := fun n => by
    have hn := hw n
    rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem, ← Ideal.neg_mem_iff, neg_sub] at hn
    exact hn
  refine ⟨w, ?_, ?_⟩
  · rw [mem_cohenSubring_iff]
    intro n
    have hmem : (seq (n + 1)).1 ∈ cohenLayerSubring k p B (n + 1) :=
      cohenLayer_antitone B (n + 1) (seq (n + 1)).2
    exact ⟨(seq (n + 1)).1, hmem, hw_sub (n + 1)⟩
  · have h1 : w - (seq 1).1 ∈ Ideal.span {(p : W)} := by
      simpa [pow_one] using hw_sub 1
    have h01 : (seq 0).1 - (seq 1).1 ∈ Ideal.span {(p : W)} := by
      simpa [pow_one] using hstep 0
    have h0w : w - x₀ ∈ Ideal.span {(p : W)} := by
      have heq : w - x₀ = (w - (seq 1).1) - ((seq 0).1 - (seq 1).1) := by
        change w - (seq 0).1 = _
        ring
      rw [heq]
      exact Ideal.sub_mem _ h1 h01
    rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, sub_eq_zero,
      WittVector.constantCoeff_apply, WittVector.constantCoeff_apply] at h0w
    rw [h0w, hx₀0]

private lemma exists_cohenRing (k : Type u) [Field k] (p : ℕ) [hp : Fact p.Prime] [CharP k p] :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsNoetherianRing C) (_ : IsDomain C) (_ : IsLocalRing C)
      (_ : IsAdicComplete (Ideal.span {(p : C)}) C) (resC : C →+* k),
      (p : C) ≠ 0 ∧
      maximalIdeal C = Ideal.span {(p : C)} ∧
      Function.Surjective resC ∧
      RingHom.ker resC = Ideal.span {(p : C)} := by
  classical
  let K := AlgebraicClosure k
  let ιK := algebraMap k K
  have hι_inj : Function.Injective ιK := RingHom.injective ιK
  let W := WittVector p K
  have hpW0 : (p : W) ≠ 0 := witt_p_ne_zero K p
  obtain ⟨B, hli1, hsp1⟩ := exists_pBasis k p
  have hli : ∀ n, LinearIndependent ↥(frobRange k p n) (evalPMon (p := p) n B) :=
    fun n => (pBasis_pow hli1 hsp1 n).1
  have hsp : ∀ n, Submodule.span ↥(frobRange k p n) (Set.range (evalPMon (p := p) n B)) = ⊤ :=
    fun n => (pBasis_pow hli1 hsp1 n).2
  let Csub := cohenSubring k p B
  let C := ↥Csub
  have hpC0 : (p : C) ≠ 0 := fun h => hpW0 (congrArg Subtype.val h)
  have hres_ex : ∀ c : C, ∃ a : k, ιK a = c.1.coeff 0 := fun c => cohenSubring_coeff_zero_mem_range c.2
  choose resFun hresFun using hres_ex
  let resC : C →+* k :=
    { toFun := resFun
      map_one' := hι_inj (by rw [hresFun 1, map_one]; exact WittVector.one_coeff_zero p K)
      map_mul' := fun x y => hι_inj (by
        rw [map_mul, hresFun, hresFun, hresFun, ← WittVector.constantCoeff_apply]
        change WittVector.constantCoeff (x.1 * y.1) = _
        rw [map_mul]
        rfl)
      map_zero' := hι_inj (by rw [hresFun 0, map_zero]; exact WittVector.zero_coeff p K 0)
      map_add' := fun x y => hι_inj (by
        rw [map_add, hresFun, hresFun, hresFun, ← WittVector.constantCoeff_apply]
        change WittVector.constantCoeff (x.1 + y.1) = _
        rw [map_add]
        rfl) }
  have hresC_surj : Function.Surjective resC := fun a => by
    obtain ⟨w, hwC, hw0⟩ := cohenSubring_surj_coeff_zero hli hsp a
    refine ⟨⟨w, hwC⟩, hι_inj ?_⟩
    rw [show resC ⟨w, hwC⟩ = resFun ⟨w, hwC⟩ from rfl, hresFun, hw0]
  have hpow_iff : ∀ (n : ℕ) (c : C), c ∈ Ideal.span {(p : C)} ^ n ↔ c.1 ∈ Ideal.span {(p : W)} ^ n := by
    intro n c
    rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨d, hd⟩
      exact ⟨d.1, congrArg Subtype.val hd⟩
    · rintro ⟨w, hw⟩
      have hwC : w ∈ Csub := cohenSubring_p_pow_saturated hli n (hw ▸ c.2)
      exact ⟨⟨w, hwC⟩, Subtype.ext hw⟩
  have hker_resC : RingHom.ker resC = Ideal.span {(p : C)} := by
    ext c
    rw [RingHom.mem_ker, ← pow_one (Ideal.span {(p : C)}), hpow_iff 1 c, pow_one,
      ← WittVector.ker_constantCoeff, RingHom.mem_ker, WittVector.constantCoeff_apply, ← hresFun c]
    exact ⟨fun h => by rw [show resFun c = 0 from h, map_zero],
      fun h => hι_inj (h.trans (map_zero ιK).symm)⟩
  have hisUnit_iff : ∀ c : C, IsUnit c ↔ c.1.coeff 0 ≠ 0 := by
    intro c
    constructor
    · rintro ⟨u, rfl⟩ h0
      have h1 : (u.1 * u.2).1.coeff 0 = 1 := by
        have : (u.1 * u.2 : C) = 1 := u.3
        rw [this]
        exact WittVector.one_coeff_zero p K
      rw [← WittVector.constantCoeff_apply] at h1
      change WittVector.constantCoeff (u.1.1 * u.2.1) = 1 at h1
      rw [map_mul, WittVector.constantCoeff_apply, h0, zero_mul] at h1
      exact zero_ne_one h1
    · intro hc0
      have ha0 : resC c ≠ 0 := fun h => hc0 (by rw [← hresFun c, show resFun c = 0 from h, map_zero])
      have hstepInv : ∀ n : ℕ, ∀ y : C, 1 - c.1 * y.1 ∈ Ideal.span {(p : W)} ^ n →
          ∃ z : C, (1 - c.1 * (y.1 + (p : W) ^ n * z.1)) ∈ Ideal.span {(p : W)} ^ (n + 1) := by
        intro n y hy
        rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hy
        obtain ⟨r, hr⟩ := hy
        have hrC : r ∈ Csub := by
          have hmem : (1 - c * y : C).1 ∈ Csub := (1 - c * y).2
          change (1 : W) - c.1 * y.1 ∈ Csub at hmem
          rw [hr] at hmem
          exact cohenSubring_p_pow_saturated hli n hmem
        obtain ⟨z, hz⟩ := hresC_surj ((resC c)⁻¹ * resC ⟨r, hrC⟩)
        refine ⟨z, ?_⟩
        have heq : 1 - c.1 * (y.1 + (p : W) ^ n * z.1) = (p : W) ^ n * (r - c.1 * z.1) := by
          calc
            1 - c.1 * (y.1 + (p : W) ^ n * z.1) = (1 - c.1 * y.1) - (p : W) ^ n * (c.1 * z.1) := by ring
            _ = (p : W) ^ n * r - (p : W) ^ n * (c.1 * z.1) := by rw [hr]
            _ = (p : W) ^ n * (r - c.1 * z.1) := by ring
        rw [heq, pow_succ]
        refine Ideal.mul_mem_mul (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) n) ?_
        rw [← WittVector.ker_constantCoeff, RingHom.mem_ker, map_sub, map_mul,
          WittVector.constantCoeff_apply, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply]
        have hr0 : r.coeff 0 = ιK (resC ⟨r, hrC⟩) := (hresFun ⟨r, hrC⟩).symm
        have hc0' : c.1.coeff 0 = ιK (resC c) := (hresFun c).symm
        have hz0 : z.1.coeff 0 = ιK (resC z) := (hresFun z).symm
        rw [hr0, hc0', hz0, hz, ← map_mul, mul_inv_cancel_left₀ ha0, sub_self]
      let ySeq : (n : ℕ) → { y : C // 1 - c.1 * y.1 ∈ Ideal.span {(p : W)} ^ n } :=
        Nat.rec ⟨0, by simp⟩ fun n prev =>
          let hex := hstepInv n prev.1 prev.2
          ⟨prev.1 + (p : C) ^ n * hex.choose, by
            change 1 - c.1 * (prev.1.1 + (p : W) ^ n * hex.choose.1) ∈ _
            exact hex.choose_spec⟩
      have hdiff_y : ∀ n : ℕ, (ySeq (n + 1)).1.1 - (ySeq n).1.1 ∈ Ideal.span {(p : W)} ^ n := fun n => by
        change ((ySeq n).1.1 + (p : W) ^ n * (hstepInv n (ySeq n).1 (ySeq n).2).choose.1) - (ySeq n).1.1 ∈ _
        rw [add_sub_cancel_left]
        exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_singleton _)) n)
      have hcauchy : ∀ {m n : ℕ}, m ≤ n →
          (ySeq m).1.1 ≡ (ySeq n).1.1 [SMOD (Ideal.span {(p : W)} ^ m • ⊤ : Ideal W)] := by
        intro m n hmn
        rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem, ← Ideal.neg_mem_iff, neg_sub]
        induction hmn with
        | refl => simp
        | @step r hmr ih =>
          have hadd : (ySeq (r + 1)).1.1 - (ySeq m).1.1 =
              ((ySeq (r + 1)).1.1 - (ySeq r).1.1) + ((ySeq r).1.1 - (ySeq m).1.1) := by ring
          rw [hadd]
          exact Ideal.add_mem _ (Ideal.pow_le_pow_right hmr (hdiff_y r)) ih
      obtain ⟨u, hu⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : W)}) (fun n => (ySeq n).1.1)
        (fun {m n} h => hcauchy h)
      have hu_sub : ∀ n : ℕ, u - (ySeq n).1.1 ∈ Ideal.span {(p : W)} ^ n := fun n => by
        have hn := hu n
        rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem, ← Ideal.neg_mem_iff, neg_sub] at hn
        exact hn
      have huC : u ∈ Csub := cohenSubring_closed fun n => ⟨(ySeq (n + 1)).1.1, (ySeq (n + 1)).1.2, hu_sub (n + 1)⟩
      have hcu : c.1 * u = 1 := by
        refine sub_eq_zero.mp (IsHausdorff.haus' (I := Ideal.span {(p : W)}) _ fun n => ?_)
        rw [SModEq.zero, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
        have heq : c.1 * u - 1 = c.1 * (u - (ySeq n).1.1) - (1 - c.1 * (ySeq n).1.1) := by ring
        rw [heq]
        exact Ideal.sub_mem _ (Ideal.mul_mem_left _ _ (hu_sub n)) (ySeq n).2
      exact isUnit_iff_exists_inv.mpr ⟨⟨u, huC⟩, Subtype.ext hcu⟩
  have hp_irr : Irreducible (p : C) := by
    refine ⟨?_, ?_⟩
    · intro hu
      have h0 := (hisUnit_iff (p : C)).mp hu
      have h1 : ((p : W) * 1).coeff 0 = 0 := by rw [mul_comm]; exact WittVector.mul_charP_coeff_zero 1
      rw [mul_one] at h1
      exact h0 h1
    · intro a b hab
      have h0 : a.1.coeff 0 * b.1.coeff 0 = 0 := by
        have h1 : (a * b).1.coeff 0 = 0 := by
          rw [← hab]
          change (p : W).coeff 0 = 0
          have h2 : ((p : W) * 1).coeff 0 = 0 := by rw [mul_comm]; exact WittVector.mul_charP_coeff_zero 1
          rwa [mul_one] at h2
        rw [← WittVector.constantCoeff_apply] at h1
        change WittVector.constantCoeff (a.1 * b.1) = 0 at h1
        rwa [map_mul, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply] at h1
      rcases mul_eq_zero.mp h0 with ha0 | hb0
      · right
        have ha_mem : a ∈ Ideal.span {(p : C)} := by
          rw [← pow_one (Ideal.span {(p : C)}), hpow_iff 1 a, pow_one, ← WittVector.ker_constantCoeff]
          exact ha0
        rw [Ideal.mem_span_singleton] at ha_mem
        obtain ⟨a', rfl⟩ := ha_mem
        have hba : a' * b = 1 := mul_left_cancel₀ hpC0 (by rw [mul_one, ← mul_assoc]; exact hab.symm)
        exact isUnit_iff_exists_inv'.mpr ⟨a', hba⟩
      · left
        have hb_mem : b ∈ Ideal.span {(p : C)} := by
          rw [← pow_one (Ideal.span {(p : C)}), hpow_iff 1 b, pow_one, ← WittVector.ker_constantCoeff]
          exact hb0
        rw [Ideal.mem_span_singleton] at hb_mem
        obtain ⟨b', rfl⟩ := hb_mem
        have hab' : a * b' = 1 := mul_left_cancel₀ hpC0 (by
          calc (p : C) * (a * b') = a * ((p : C) * b') := by ring
            _ = (p : C) * 1 := by rw [← hab, mul_one])
        exact isUnit_iff_exists_inv.mpr ⟨b', hab'⟩
  have hfac : IsDiscreteValuationRing.HasUnitMulPowIrreducibleFactorization C := by
    refine ⟨(p : C), hp_irr, fun {x} hx0 => ?_⟩
    have hex_not : ∃ n : ℕ, x.1 ∉ Ideal.span {(p : W)} ^ (n + 1) := by
      by_contra hall
      exact hx0 (Subtype.ext (IsHausdorff.haus' (I := Ideal.span {(p : W)}) x.1 fun n => by
        rw [SModEq.zero, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one]
        by_contra hnot
        cases n with
        | zero => exact hnot (by simp)
        | succ m => exact hall ⟨m, hnot⟩))
    let n := Nat.find hex_not
    have hn_not : x.1 ∉ Ideal.span {(p : W)} ^ (n + 1) := Nat.find_spec hex_not
    have hn_mem : x.1 ∈ Ideal.span {(p : W)} ^ n := by
      cases hn : n with
      | zero => simp
      | succ m =>
        by_contra hnot
        have hle := Nat.find_min' hex_not hnot
        omega
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hn_mem
    obtain ⟨w, hw⟩ := hn_mem
    have hwC : w ∈ Csub := cohenSubring_p_pow_saturated hli n (hw ▸ x.2)
    have hw0 : w.coeff 0 ≠ 0 := by
      intro h0
      have hw_mem : w ∈ Ideal.span {(p : W)} := by
        rw [← WittVector.ker_constantCoeff]; exact h0
      rw [Ideal.mem_span_singleton] at hw_mem
      obtain ⟨v, rfl⟩ := hw_mem
      apply hn_not
      rw [hw, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact ⟨v, by rw [pow_succ, mul_assoc]⟩
    obtain ⟨u, hu⟩ := (hisUnit_iff ⟨w, hwC⟩).mpr hw0
    refine ⟨n, ⟨u, ?_⟩⟩
    apply Subtype.ext
    change (p : W) ^ n * (u : C).1 = x.1
    rw [hu, hw]
  have : IsDiscreteValuationRing C :=
    IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization hfac
  have hmax_p : maximalIdeal C = Ideal.span {(p : C)} := by
    have hmax : (Ideal.span {(p : C)}).IsMaximal := by
      rw [← hker_resC]
      exact RingHom.ker_isMaximal_of_surjective resC hresC_surj
    exact (IsLocalRing.eq_maximalIdeal hmax).symm
  have hcompC : IsAdicComplete (Ideal.span {(p : C)}) C :=
    { toIsHausdorff := ⟨fun c hc => Subtype.ext (IsHausdorff.haus' (I := Ideal.span {(p : W)}) c.1 fun n => by
        rw [SModEq.zero, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, ← hpow_iff n c]
        have hn := hc n
        rwa [SModEq.zero, ← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one] at hn)⟩
      toIsPrecomplete := ⟨fun seq hseq => by
        have hcW : ∀ {m n : ℕ}, m ≤ n →
            (seq m).1 ≡ (seq n).1 [SMOD (Ideal.span {(p : W)} ^ m • ⊤ : Ideal W)] := by
          intro m n hmn
          rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem]
          change (seq m - seq n).1 ∈ Ideal.span {(p : W)} ^ m
          rw [← hpow_iff m]
          have h := hseq hmn
          rwa [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem] at h
        obtain ⟨w, hw⟩ := IsPrecomplete.prec' (I := Ideal.span {(p : W)}) (fun n => (seq n).1)
          (fun {m n} h => hcW h)
        have hw_sub : ∀ n : ℕ, w - (seq n).1 ∈ Ideal.span {(p : W)} ^ n := fun n => by
          have hn := hw n
          rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem, ← Ideal.neg_mem_iff, neg_sub] at hn
          exact hn
        have hwC : w ∈ Csub := cohenSubring_closed fun n => ⟨(seq (n + 1)).1, (seq (n + 1)).2, hw_sub (n + 1)⟩
        refine ⟨⟨w, hwC⟩, fun n => ?_⟩
        rw [← Ideal.one_eq_top, Ideal.smul_eq_mul, mul_one, SModEq.sub_mem, hpow_iff n]
        change (seq n).1 - w ∈ Ideal.span {(p : W)} ^ n
        rw [← Ideal.neg_mem_iff, neg_sub]
        exact hw_sub n⟩ }
  exact ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, hcompC, resC,
    hpC0, hmax_p, hresC_surj, hker_resC⟩

/-!
Part 5B: Square-Zero Lifting for p-Torsion-Free Cohen Rings
-/

private noncomputable def zmodHomOfCastEqZero {R : Type u} [CommRing R] {p : ℕ} (hp : (p : R) = 0) :
    ZMod p →+* R :=
  (Ideal.Quotient.lift (Ideal.span {(p : ℤ)}) (Int.castRingHom R) fun z hz => by
    rw [Ideal.mem_span_singleton] at hz
    obtain ⟨q, rfl⟩ := hz
    simp [hp]).comp (Int.quotientSpanNatEquivZMod p).symm.toRingHom

private lemma ideal_sq (A : Type u) [CommRing A] (I : Ideal A) : I ^ 2 = I * I := sq I

private lemma exists_section_of_formallySmooth_sq_zero
    {k A : Type u} [Field k] [CommRing A] {p : ℕ} [Fact p.Prime] [CharP k p]
    [Algebra (ZMod p) k] [Algebra (ZMod p) A]
    (ψ : A →ₐ[ZMod p] k) (hsurj : Function.Surjective ψ)
    (hsq : (RingHom.ker ψ.toRingHom) ^ 2 = ⊥) :
    ∃ σ : k →ₐ[ZMod p] A, ∀ a : k, ψ (σ a) = a := by
  have : Algebra.FormallySmooth (ZMod p) k := formallySmooth_zmod_of_charP k p
  let e := Ideal.quotientKerAlgEquivOfSurjective hsurj
  obtain ⟨σ, hσ⟩ := Algebra.FormallySmooth.comp_surjective (ZMod p) k (RingHom.ker ψ) hsq e.symm.toAlgHom
  refine ⟨σ, fun a => ?_⟩
  have h1 := AlgHom.congr_fun hσ a
  have h2 := congrArg e h1
  simpa [e] using h2

private lemma exists_lift_of_p_torsionFree
    {C k S : Type u} [CommRing C] [Field k] [CommRing S]
    {p : ℕ} [hp : Fact p.Prime] [CharP k p] [Algebra (ZMod p) k]
    (hp_tf : ∀ c : C, (p : C) * c = 0 → c = 0)
    (resC : C →+* k) (hres_surj : Function.Surjective resC)
    (hker_res : RingHom.ker resC = Ideal.span {(p : C)})
    (I : Ideal S) (hI2 : I ^ 2 = ⊥) (hpI : ∀ z ∈ I, (p : S) * z = 0)
    (f : C →+* S ⧸ I) :
    ∃ g : C →+* S, (Ideal.Quotient.mk I).comp g = f := by
  classical
  let P := MvPolynomial C ℤ
  let π : P →+* C := MvPolynomial.eval₂Hom (Int.castRingHom C) id
  have hπ_X : ∀ c : C, π (MvPolynomial.X c) = c := fun c => MvPolynomial.eval₂Hom_X' _ _ c
  have hπ_surj : Function.Surjective π := fun c => ⟨MvPolynomial.X c, hπ_X c⟩
  let J : Ideal P := RingHom.ker π
  let P_p := P ⧸ Ideal.span {(p : P)}
  let q_p : P →+* P_p := Ideal.Quotient.mk (Ideal.span {(p : P)})
  have hpPp : (p : P_p) = 0 := by
    rw [← map_natCast q_p, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Set.mem_singleton _)
  let Jbar : Ideal P_p := J.map q_p
  let P2 := P_p ⧸ Jbar ^ 2
  let q2 : P_p →+* P2 := Ideal.Quotient.mk (Jbar ^ 2)
  let u : P →+* P2 := q2.comp q_p
  have hpP2 : (p : P2) = 0 := by rw [← map_natCast q2, hpPp, map_zero]
  let _ : Algebra (ZMod p) P2 := (zmodHomOfCastEqZero (R := P2) hpP2).toAlgebra
  have hψ_ker : Ideal.span {(p : P)} ≤ RingHom.ker (resC.comp π) := by
    rw [Ideal.span_singleton_le_iff_mem, RingHom.mem_ker, RingHom.comp_apply, map_natCast, map_natCast]
    exact CharP.cast_eq_zero k p
  let ψ : P_p →+* k := Ideal.Quotient.lift (Ideal.span {(p : P)}) (resC.comp π) hψ_ker
  have hker_ψ : RingHom.ker ψ = Jbar := by
    refine le_antisymm ?_ ?_
    · intro x hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [RingHom.mem_ker] at hx
      change resC (π y) = 0 at hx
      have hpy : π y ∈ Ideal.span {(p : C)} := by rw [← hker_res]; exact hx
      rw [Ideal.mem_span_singleton] at hpy
      obtain ⟨c, hc⟩ := hpy
      have hyJ : y - (p : P) * MvPolynomial.X c ∈ J := by
        rw [RingHom.mem_ker, map_sub, map_mul, map_natCast, hπ_X, hc, sub_self]
      have hqp_eq : q_p (y - (p : P) * MvPolynomial.X c) = q_p y := by
        rw [map_sub, map_mul, map_natCast, hpPp, zero_mul, sub_zero]
      rw [← hqp_eq]
      exact Ideal.mem_map_of_mem q_p hyJ
    · rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, RingHom.mem_ker]
      change resC (π y) = 0
      rw [RingHom.mem_ker.mp hy, map_zero]
  have hJbar2_le : Jbar ^ 2 ≤ RingHom.ker ψ := by
    rw [hker_ψ]
    exact Ideal.pow_le_self (by decide)
  let ψ2Ring : P2 →+* k := Ideal.Quotient.lift (Jbar ^ 2) ψ hJbar2_le
  let ψ2 : P2 →ₐ[ZMod p] k :=
    { toRingHom := ψ2Ring
      commutes' := fun z => by
        rw [← ZMod.natCast_zmod_val z]
        change ψ2Ring (algebraMap (ZMod p) P2 (z.val : ZMod p)) = algebraMap (ZMod p) k (z.val : ZMod p)
        rw [map_natCast, map_natCast, map_natCast] }
  have hψ2_u : ∀ x : P, ψ2 (u x) = resC (π x) := fun _ => rfl
  have hψ2_surj : Function.Surjective ψ2 := fun a => by
    obtain ⟨c, rfl⟩ := hres_surj a
    exact ⟨u (MvPolynomial.X c), by rw [hψ2_u, hπ_X]⟩
  let K2 : Ideal P2 := RingHom.ker ψ2.toRingHom
  have hK2_eq : K2 = J.map u := by
    have hK2_q2 : K2 = Jbar.map q2 := by
      refine le_antisymm ?_ ?_
      · intro z hz
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
        have hy : y ∈ RingHom.ker ψ := hz
        rw [hker_ψ] at hy
        exact Ideal.mem_map_of_mem q2 hy
      · rw [Ideal.map_le_iff_le_comap]
        intro y hy
        rw [← hker_ψ] at hy
        exact hy
    rw [hK2_q2, Ideal.map_map]
  have hK2_sq : K2 ^ 2 = ⊥ := by
    rw [ideal_sq P2 K2, eq_bot_iff, Ideal.mul_le]
    intro a ha b hb
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    have hx : x ∈ Jbar := by rw [← hker_ψ]; exact ha
    have hy : y ∈ Jbar := by rw [← hker_ψ]; exact hb
    rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, sq Jbar]
    exact Ideal.mul_mem_mul hx hy
  obtain ⟨σ, hψ2_σ⟩ := exists_section_of_formallySmooth_sq_zero ψ2 hψ2_surj hK2_sq
  let δ : P → P2 := fun x => u x - σ (resC (π x))
  have hδ_mem : ∀ x : P, δ x ∈ K2 := fun x => by
    rw [RingHom.mem_ker]
    change ψ2 (u x - σ (resC (π x))) = 0
    rw [map_sub, hψ2_u, hψ2_σ, sub_self]
  have hδ_J : ∀ x ∈ J, δ x = u x := fun x hx => by
    dsimp only [δ]
    rw [RingHom.mem_ker.mp hx, map_zero, map_zero, sub_zero]
  have hδ_add : ∀ x y : P, δ (x + y) = δ x + δ y := fun x y => by
    dsimp only [δ]; rw [map_add, map_add, map_add, map_add]; ring
  have hδ_one : δ 1 = 0 := by
    dsimp only [δ]; rw [map_one, map_one, map_one, map_one, sub_self]
  have hδ_mul : ∀ x y : P, δ (x * y) = u x * δ y + u y * δ x := fun x y => by
    have hmul0 : δ x * δ y = 0 := by
      have hmem : δ x * δ y ∈ K2 ^ 2 := by
        rw [ideal_sq P2 K2]
        exact Ideal.mul_mem_mul (hδ_mem x) (hδ_mem y)
      rwa [hK2_sq, Ideal.mem_bot] at hmem
    dsimp only [δ] at hmul0 ⊢
    rw [map_mul, map_mul, map_mul, map_mul]
    linear_combination -hmul0
  have hlift_f : ∀ c : C, ∃ s : S, Ideal.Quotient.mk I s = f c :=
    fun c => Ideal.Quotient.mk_surjective (f c)
  choose liftF hliftF using hlift_f
  let h : P →+* S := MvPolynomial.eval₂Hom (Int.castRingHom S) liftF
  have hh_mk : (Ideal.Quotient.mk I).comp h = f.comp π := by
    apply MvPolynomial.ringHom_ext
    · intro n; simp [h, π]
    · intro c; simp [h, π, hliftF c]
  have hh_J : ∀ x ∈ J, h x ∈ I := fun x hx => by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have h1 := RingHom.congr_fun hh_mk x
    rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.mem_ker.mp hx, map_zero] at h1
    exact h1
  have hkill : ∀ x ∈ J, u x = 0 → h x = 0 := by
    intro x hxJ hux
    have hqp : q_p x ∈ Jbar ^ 2 := Ideal.Quotient.eq_zero_iff_mem.mp hux
    have hqp_map : Jbar ^ 2 = (J ^ 2).map q_p := (Ideal.map_pow q_p J 2).symm
    rw [hqp_map, Ideal.mem_map_iff_of_surjective q_p Ideal.Quotient.mk_surjective] at hqp
    obtain ⟨a, haJ2, haeq⟩ := hqp
    have hdiff : x - a ∈ Ideal.span {(p : P)} := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub]
      exact sub_eq_zero.mpr haeq.symm
    rw [Ideal.mem_span_singleton] at hdiff
    obtain ⟨b, hb⟩ := hdiff
    have hx_eq : x = a + (p : P) * b := by linear_combination hb
    have hbJ : b ∈ J := by
      rw [RingHom.mem_ker]
      apply hp_tf
      have ha0 : π a = 0 := RingHom.mem_ker.mp (Ideal.pow_le_self (by decide) haJ2)
      have hx0 : π x = 0 := RingHom.mem_ker.mp hxJ
      have h1 := congrArg π hx_eq
      rw [hx0, map_add, ha0, zero_add, map_mul, map_natCast] at h1
      exact h1.symm
    have ha_h0 : h a = 0 := by
      have hmem : h a ∈ I ^ 2 := by
        have hle1 : J.map h ≤ I := Ideal.map_le_iff_le_comap.mpr fun y hy => hh_J y hy
        have hle : (J ^ 2).map h ≤ I ^ 2 := by
          rw [sq J, sq I, Ideal.map_mul]
          exact Ideal.mul_mono hle1 hle1
        exact hle (Ideal.mem_map_of_mem h haJ2)
      rwa [hI2, Ideal.mem_bot] at hmem
    rw [hx_eq, map_add, ha_h0, zero_add, map_mul, map_natCast]
    exact hpI (h b) (hh_J b hbJ)
  have hK2_lift : ∀ z : P2, z ∈ K2 → ∃ x ∈ J, u x = z := fun z hz => by
    rw [hK2_eq, Ideal.mem_map_iff_of_surjective u (Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective)] at hz
    exact hz
  let η : P2 → S := fun z => if hz : z ∈ K2 then h (hK2_lift z hz).choose else 0
  have hη_eq : ∀ x ∈ J, η (u x) = h x := fun x hxJ => by
    have huz : u x ∈ K2 := by rw [hK2_eq]; exact Ideal.mem_map_of_mem u hxJ
    dsimp only [η]
    simp only [huz, ↓reduceDIte]
    have hspec := (hK2_lift (u x) huz).choose_spec
    have hsub : (hK2_lift (u x) huz).choose - x ∈ J := J.sub_mem hspec.1 hxJ
    have hu0 : u ((hK2_lift (u x) huz).choose - x) = 0 := by rw [map_sub, hspec.2, sub_self]
    have hh0 := hkill _ hsub hu0
    rw [map_sub, sub_eq_zero] at hh0
    exact hh0
  have hη_mem : ∀ z ∈ K2, η z ∈ I := fun z hz => by
    obtain ⟨x, hxJ, rfl⟩ := hK2_lift z hz
    rw [hη_eq x hxJ]
    exact hh_J x hxJ
  have hη_zero : η 0 = 0 := by
    have h0 := hη_eq 0 J.zero_mem
    rwa [map_zero, map_zero] at h0
  have hη_add : ∀ z₁ ∈ K2, ∀ z₂ ∈ K2, η (z₁ + z₂) = η z₁ + η z₂ := fun z₁ hz₁ z₂ hz₂ => by
    obtain ⟨x₁, hx₁, rfl⟩ := hK2_lift z₁ hz₁
    obtain ⟨x₂, hx₂, rfl⟩ := hK2_lift z₂ hz₂
    rw [← map_add, hη_eq _ (J.add_mem hx₁ hx₂), hη_eq _ hx₁, hη_eq _ hx₂, map_add]
  have hη_mul : ∀ (x : P) (z : P2), z ∈ K2 → η (u x * z) = h x * η z := fun x z hz => by
    obtain ⟨y, hyJ, rfl⟩ := hK2_lift z hz
    rw [← map_mul, hη_eq _ (J.mul_mem_left x hyJ), hη_eq _ hyJ, map_mul]
  let g₀ : P →+* S :=
    { toFun := fun x => h x - η (δ x)
      map_one' := by rw [map_one, hδ_one, hη_zero, sub_zero]
      map_zero' := by
        have hδ0 : δ 0 = 0 := by simp [δ]
        rw [map_zero, hδ0, hη_zero, sub_zero]
      map_add' := fun x y => by
        rw [map_add, hδ_add, hη_add _ (hδ_mem x) _ (hδ_mem y)]
        ring
      map_mul' := fun x y => by
        rw [map_mul, hδ_mul, hη_add _ (K2.mul_mem_left _ (hδ_mem y)) _ (K2.mul_mem_left _ (hδ_mem x)),
          hη_mul x _ (hδ_mem y), hη_mul y _ (hδ_mem x)]
        have hsq : η (δ x) * η (δ y) = 0 := by
          have hmem : η (δ x) * η (δ y) ∈ I ^ 2 := by
            rw [sq]
            exact Ideal.mul_mem_mul (hη_mem _ (hδ_mem x)) (hη_mem _ (hδ_mem y))
          rwa [hI2, Ideal.mem_bot] at hmem
        linear_combination -hsq }
  have hg₀_J : J ≤ RingHom.ker g₀ := fun x hx => by
    rw [RingHom.mem_ker]
    change h x - η (δ x) = 0
    rw [hδ_J x hx, hη_eq x hx, sub_self]
  let g : C →+* S :=
    (Ideal.Quotient.lift J g₀ hg₀_J).comp (RingHom.quotientKerEquivOfSurjective hπ_surj).symm.toRingHom
  refine ⟨g, ?_⟩
  ext c
  have hgc : g c = g₀ (MvPolynomial.X c) := by
    have h1 : (RingHom.quotientKerEquivOfSurjective hπ_surj).symm c = Ideal.Quotient.mk J (MvPolynomial.X c) := by
      apply (RingHom.quotientKerEquivOfSurjective hπ_surj).injective
      rw [RingEquiv.apply_symm_apply]
      exact (hπ_X c).symm
    change Ideal.Quotient.lift J g₀ hg₀_J ((RingHom.quotientKerEquivOfSurjective hπ_surj).symm c) = _
    rw [h1]
    rfl
  rw [RingHom.comp_apply, hgc]
  change Ideal.Quotient.mk I (h (MvPolynomial.X c) - η (δ (MvPolynomial.X c))) = f c
  rw [map_sub, Ideal.Quotient.eq_zero_iff_mem.mpr (hη_mem _ (hδ_mem _)), sub_zero]
  have hmk := RingHom.congr_fun hh_mk (MvPolynomial.X c)
  rw [RingHom.comp_apply, RingHom.comp_apply, hπ_X c] at hmk
  exact hmk

private lemma exists_cohenRing_hom
    {D : Type u} [CommRing D] [IsLocalRing D] [IsAdicComplete (maximalIdeal D) D]
    {p : ℕ} [hp : Fact p.Prime] (hp_mem : (p : D) ∈ maximalIdeal D) :
    ∃ (C : Type u) (_ : CommRing C) (_ : IsNoetherianRing C) (_ : IsDomain C) (_ : IsLocalRing C)
      (_ : IsAdicComplete (Ideal.span {(p : C)}) C) (f : C →+* D),
      (p : C) ≠ 0 ∧
      maximalIdeal C = Ideal.span {(p : C)} ∧
      f (p : C) = (p : D) ∧
      ∀ d : D, ∃ c : C, d - f c ∈ maximalIdeal D := by
  let k := ResidueField D
  have hpk0 : (p : k) = 0 := by
    change Ideal.Quotient.mk (maximalIdeal D) (p : D) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp_mem
  have : CharP k p := by
    refine (CharP.charP_iff_prime_eq_zero hp.out).mpr hpk0
  let _ : Algebra (ZMod p) k := (zmodHomOfCastEqZero hpk0).toAlgebra
  obtain ⟨C, _, _, _, _, _, resC, hpC0, hmaxC, hresC_surj, hker_resC⟩ := exists_cohenRing k p
  have hp_tf : ∀ c : C, (p : C) * c = 0 → c = 0 := fun c h =>
    (mul_eq_zero.mp h).resolve_left hpC0
  have hstep : ∀ (n : ℕ) (fn : C →+* D ⧸ maximalIdeal D ^ (n + 1)),
      ∃ fn1 : C →+* D ⧸ maximalIdeal D ^ (n + 2),
        (Ideal.Quotient.factorPow (maximalIdeal D) (Nat.le_succ (n + 1))).comp fn1 = fn := by
    intro n fn
    let q : D ⧸ maximalIdeal D ^ (n + 2) →+* D ⧸ maximalIdeal D ^ (n + 1) :=
      Ideal.Quotient.factorPow (maximalIdeal D) (Nat.le_succ (n + 1))
    have hq_surj : Function.Surjective q := fun y => by
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨Ideal.Quotient.mk _ d, rfl⟩
    let I : Ideal (D ⧸ maximalIdeal D ^ (n + 2)) := RingHom.ker q
    have hI2 : I ^ 2 = ⊥ := by
      rw [sq, eq_bot_iff, Ideal.mul_le]
      intro a ha b hb
      obtain ⟨da, rfl⟩ := Ideal.Quotient.mk_surjective a
      obtain ⟨db, rfl⟩ := Ideal.Quotient.mk_surjective b
      have hda : da ∈ maximalIdeal D ^ (n + 1) := Ideal.Quotient.eq_zero_iff_mem.mp ha
      have hdb : db ∈ maximalIdeal D ^ (n + 1) := Ideal.Quotient.eq_zero_iff_mem.mp hb
      rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have hmul : da * db ∈ maximalIdeal D ^ ((n + 1) + (n + 1)) := by
        rw [pow_add]; exact Ideal.mul_mem_mul hda hdb
      exact Ideal.pow_le_pow_right (by omega : n + 2 ≤ (n + 1) + (n + 1)) hmul
    have hpI : ∀ z ∈ I, (p : D ⧸ maximalIdeal D ^ (n + 2)) * z = 0 := by
      intro z hz
      obtain ⟨d, rfl⟩ := Ideal.Quotient.mk_surjective z
      have hd : d ∈ maximalIdeal D ^ (n + 1) := Ideal.Quotient.eq_zero_iff_mem.mp hz
      rw [← map_natCast (Ideal.Quotient.mk _), ← map_mul, Ideal.Quotient.eq_zero_iff_mem, pow_succ']
      exact Ideal.mul_mem_mul hp_mem hd
    let eI : (D ⧸ maximalIdeal D ^ (n + 2)) ⧸ I ≃+* D ⧸ maximalIdeal D ^ (n + 1) :=
      RingHom.quotientKerEquivOfSurjective hq_surj
    obtain ⟨g, hg⟩ := exists_lift_of_p_torsionFree hp_tf resC hresC_surj hker_resC I hI2 hpI
      (eI.symm.toRingHom.comp fn)
    refine ⟨g, ?_⟩
    ext c
    have h1 := RingHom.congr_fun hg c
    have h2 := congrArg eI h1
    change eI (Ideal.Quotient.mk I (g c)) = eI (eI.symm (fn c)) at h2
    rw [RingEquiv.apply_symm_apply] at h2
    exact h2
  let resD : C →+* (D ⧸ maximalIdeal D) :=
    { toFun := resC
      map_one' := map_one resC
      map_mul' := map_mul resC
      map_zero' := map_zero resC
      map_add' := map_add resC }
  let f0 : C →+* D ⧸ maximalIdeal D ^ 1 :=
    (Ideal.quotEquivOfEq (pow_one (maximalIdeal D))).symm.toRingHom.comp resD
  let fSeq : (n : ℕ) → C →+* D ⧸ maximalIdeal D ^ (n + 1) :=
    Nat.rec f0 fun n prev => (hstep n prev).choose
  have hfSeq_compat : ∀ {m : ℕ},
      (Ideal.Quotient.factorPow (maximalIdeal D) (Nat.le_succ (m + 1))).comp (fSeq (m + 1)) = fSeq m :=
    fun {m} => (hstep m (fSeq m)).choose_spec
  let f : C →+* D :=
    IsAdicComplete.StrictMono.liftRingHom (maximalIdeal D) (a := fun n => n + 1)
      (fun _ _ h => Nat.succ_lt_succ h) fSeq (fun {m} => hfSeq_compat)
  refine ⟨C, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, f,
    hpC0, hmaxC, map_natCast f p, fun d => ?_⟩
  obtain ⟨c, hc⟩ := hresC_surj (residue D d)
  refine ⟨c, ?_⟩
  rw [← pow_one (maximalIdeal D), ← Ideal.Quotient.eq_zero_iff_mem, map_sub, sub_eq_zero]
  have hmk : Ideal.Quotient.mk (maximalIdeal D ^ 1) (f c) = f0 c := by
    have h1 := RingHom.congr_fun
      (IsAdicComplete.StrictMono.mk_comp_liftRingHom (maximalIdeal D) (a := fun n => n + 1)
        (fun _ _ h => Nat.succ_lt_succ h) fSeq (fun {m} => hfSeq_compat) (n := 0)) c
    exact h1
  rw [hmk]
  dsimp only [f0]
  rw [RingHom.comp_apply]
  have hrc : resD c = Ideal.Quotient.mk (maximalIdeal D) d := hc
  rw [hrc]
  symm
  let eq1 := Ideal.quotEquivOfEq (pow_one (maximalIdeal D))
  apply eq1.injective
  change eq1 (eq1.symm (Ideal.Quotient.mk (maximalIdeal D) d)) = eq1 (Ideal.Quotient.mk (maximalIdeal D ^ 1) d)
  rw [RingEquiv.apply_symm_apply]
  rfl

/-!
Part 6: Equal-Characteristic Q-Algebra Helper and Main Proof
-/

private noncomputable def ratHomOfLocalCharZero
    (D : Type u) [CommRing D] [IsLocalRing D] [CharZero (ResidueField D)] : ℚ →+* D := by
  have hnz : ∀ y : nonZeroDivisors ℤ, IsUnit (Int.castRingHom D y.1) := by
    intro y
    have hy0 : y.1 ≠ 0 := nonZeroDivisors.ne_zero y.2
    by_contra hnu
    have hmem : (y.1 : D) ∈ maximalIdeal D := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h0 : residue D (y.1 : D) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    rw [map_intCast] at h0
    exact hy0 (Int.cast_eq_zero.mp h0)
  exact IsLocalization.lift (M := nonZeroDivisors ℤ) (g := Int.castRingHom D) hnz

end SmallCohenMacaulayLeTwo

theorem OMA.solution :
    type_of% @SmallCohenMacaulayModules.exists_isSmallCohenMacaulay.variants.ringKrullDim_le_two := by
  intro R _ _ _ _ hR
  rcases SmallCohenMacaulayLeTwo.ringKrullDim_le_two_cases hR with h0 | h1 | h2
  · have : Ring.KrullDimLE 0 R := Ring.krullDimLE_iff.mpr (by rw [h0]; rfl)
    refine ⟨R, inferInstance, inferInstance, ?_⟩
    exact (SmallCohenMacaulayModules.isSmallCohenMacaulay_iff_of_krullDimLE_zero R R).mpr
      ⟨inferInstance, inferInstance⟩
  · exact SmallCohenMacaulayLeTwo.exists_isSmallCohenMacaulay_dim_one h1
  · cases hchar : ringChar (IsLocalRing.ResidueField R) with
    | zero =>
      have : CharP (IsLocalRing.ResidueField R) 0 := hchar ▸ ringChar.charP _
      have : CharZero (IsLocalRing.ResidueField R) :=
        CharP.charP_to_charZero (IsLocalRing.ResidueField R)
      obtain ⟨P, hPmin, hPdim⟩ := SmallCohenMacaulayLeTwo.exists_ltSeries_of_ringKrullDim_eq h2
      have : P.IsPrime := hPmin.1.1
      have : IsLocalRing (R ⧸ P) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
      have : IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ P)) (R ⧸ P) :=
        SmallCohenMacaulayLeTwo.quotient_isAdicComplete P
      have hres_char0 : CharZero (IsLocalRing.ResidueField (R ⧸ P)) := by
        let fR : R →+* IsLocalRing.ResidueField (R ⧸ P) :=
          (IsLocalRing.residue (R ⧸ P)).comp (Ideal.Quotient.mk P)
        have hfR_ker : IsLocalRing.maximalIdeal R ≤ RingHom.ker fR := by
          have hker_max : (RingHom.ker fR).IsMaximal :=
            RingHom.ker_isMaximal_of_surjective fR
              (Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective)
          exact (IsLocalRing.eq_maximalIdeal hker_max).ge
        let emb : IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField (R ⧸ P) :=
          Ideal.Quotient.lift (IsLocalRing.maximalIdeal R) fR hfR_ker
        exact ⟨fun m n h => Nat.cast_injective (RingHom.injective emb (by simpa [map_natCast] using h))⟩
      let _ : Algebra ℚ (R ⧸ P) := (SmallCohenMacaulayLeTwo.ratHomOfLocalCharZero (R ⧸ P)).toAlgebra
      have : Algebra.FormallySmooth ℚ (IsLocalRing.ResidueField (R ⧸ P)) :=
        SmallCohenMacaulayLeTwo.formallySmooth_rat_of_charZero _
      let idQ : IsLocalRing.ResidueField (R ⧸ P) →ₐ[ℚ] (R ⧸ P) ⧸ IsLocalRing.maximalIdeal (R ⧸ P) :=
        { toFun := id
          map_one' := rfl
          map_mul' := fun _ _ => rfl
          map_zero' := rfl
          map_add' := fun _ _ => rfl
          commutes' := fun q => by
            let f1 : ℚ →+* IsLocalRing.ResidueField (R ⧸ P) := algebraMap ℚ (IsLocalRing.ResidueField (R ⧸ P))
            let f2 : ℚ →+* IsLocalRing.ResidueField (R ⧸ P) :=
              (IsLocalRing.residue (R ⧸ P)).comp (algebraMap ℚ (R ⧸ P))
            exact RingHom.congr_fun (Subsingleton.elim f1 f2) q }
      obtain ⟨ι, hι⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
        (R := ℚ) (A := IsLocalRing.ResidueField (R ⧸ P)) (S := R ⧸ P)
        (I := IsLocalRing.maximalIdeal (R ⧸ P)) idQ
      obtain ⟨x, y, hsop⟩ := SmallCohenMacaulayLeTwo.exists_sop_dim_two h2
      exact SmallCohenMacaulayLeTwo.exists_isSmallCohenMacaulay_of_coeff_field hPdim hsop ι.toRingHom
        (fun a => AlgHom.congr_fun hι a)
    | succ m =>
      let p : ℕ := m + 1
      have hp_char : CharP (IsLocalRing.ResidueField R) p := by
        change CharP (IsLocalRing.ResidueField R) (m + 1)
        rw [← hchar]
        exact ringChar.charP (IsLocalRing.ResidueField R)
      have hp_prime : p.Prime := (CharP.char_is_prime_or_zero (IsLocalRing.ResidueField R) p).resolve_right
        (Nat.succ_ne_zero m)
      have : Fact p.Prime := ⟨hp_prime⟩
      by_cases hex : ∃ P ∈ minimalPrimes R, ringKrullDim (R ⧸ P) = 2 ∧ (p : R) ∈ P
      · obtain ⟨P, hPmin, hPdim, hpP⟩ := hex
        have : P.IsPrime := hPmin.1.1
        have : IsLocalRing (R ⧸ P) :=
          IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
        have : IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ P)) (R ⧸ P) :=
          SmallCohenMacaulayLeTwo.quotient_isAdicComplete P
        have hpD0 : (p : R ⧸ P) = 0 := by
          rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]
          exact hpP
        have hpk0 : (p : IsLocalRing.ResidueField (R ⧸ P)) = 0 := by
          rw [← map_natCast (IsLocalRing.residue (R ⧸ P)), hpD0, map_zero]
        have : CharP (IsLocalRing.ResidueField (R ⧸ P)) p :=
          (CharP.charP_iff_prime_eq_zero hp_prime).mpr hpk0
        let _ : Algebra (ZMod p) (R ⧸ P) :=
          (SmallCohenMacaulayLeTwo.zmodHomOfCastEqZero hpD0).toAlgebra
        have : Algebra.FormallySmooth (ZMod p) (IsLocalRing.ResidueField (R ⧸ P)) :=
          SmallCohenMacaulayLeTwo.formallySmooth_zmod_of_charP _ p
        obtain ⟨ι, hι⟩ := Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete
          (R := ZMod p) (A := IsLocalRing.ResidueField (R ⧸ P)) (S := R ⧸ P)
          (I := IsLocalRing.maximalIdeal (R ⧸ P))
          (AlgHom.id (ZMod p) (IsLocalRing.ResidueField (R ⧸ P)))
        obtain ⟨x, y, hsop⟩ := SmallCohenMacaulayLeTwo.exists_sop_dim_two h2
        exact SmallCohenMacaulayLeTwo.exists_isSmallCohenMacaulay_of_coeff_field hPdim hsop ι.toRingHom
          (fun a => AlgHom.congr_fun hι a)
      · have hp_memR : (p : R) ∈ IsLocalRing.maximalIdeal R := by
          rw [← Ideal.Quotient.eq_zero_iff_mem]
          change (p : IsLocalRing.ResidueField R) = 0
          exact CharP.cast_eq_zero (IsLocalRing.ResidueField R) p
        obtain ⟨y, hsop⟩ := SmallCohenMacaulayLeTwo.exists_sop_of_not_mem_minimalPrimes_dim_two
          h2 hp_memR (fun Q hQp hQp_mem _ Q' hQ'p hQQ' => by
            by_contra hQ'ne
            have hQ'lt : Q' < IsLocalRing.maximalIdeal R :=
              (IsLocalRing.le_maximalIdeal hQ'p.ne_top).lt_of_ne hQ'ne
            obtain ⟨P₀, hP₀min, hP₀Q⟩ := Ideal.exists_minimalPrimes_le (J := Q) bot_le
            have : P₀.IsPrime := hP₀min.1.1
            by_cases hP₀eq : P₀ = Q
            · subst hP₀eq
              let s : LTSeries (PrimeSpectrum (R ⧸ P₀)) :=
                { length := 2
                  toFun := ![
                    ⟨P₀.map (Ideal.Quotient.mk P₀),
                      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker])⟩,
                    ⟨Q'.map (Ideal.Quotient.mk P₀),
                      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hQQ'.le)⟩,
                    ⟨(IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk P₀),
                      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
                        (by rw [Ideal.mk_ker]; exact IsLocalRing.le_maximalIdeal hP₀min.1.1.ne_top)⟩]
                  step := fun i => by
                    fin_cases i
                    · change P₀.map (Ideal.Quotient.mk P₀) < Q'.map (Ideal.Quotient.mk P₀)
                      refine (Ideal.map_mono hQQ'.le).lt_of_not_ge fun hge => hQQ'.not_ge ?_
                      have hc := Ideal.comap_mono (f := Ideal.Quotient.mk P₀) hge
                      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
                        Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
                        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_idem,
                        sup_eq_left.mpr hQQ'.le] at hc
                      exact hc
                    · change Q'.map (Ideal.Quotient.mk P₀) < (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk P₀)
                      refine (Ideal.map_mono hQ'lt.le).lt_of_not_ge fun hge => hQ'lt.not_ge ?_
                      have hc := Ideal.comap_mono (f := Ideal.Quotient.mk P₀) hge
                      rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
                        Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
                        ← RingHom.ker_eq_comap_bot, Ideal.mk_ker,
                        sup_eq_left.mpr hQQ'.le,
                        sup_eq_left.mpr (IsLocalRing.le_maximalIdeal hP₀min.1.1.ne_top)] at hc
                      exact hc }
              have h2le : (2 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ P₀) :=
                le_iSup (fun l : LTSeries (PrimeSpectrum (R ⧸ P₀)) => (l.length : WithBot ℕ∞)) s
              have hle2 : ringKrullDim (R ⧸ P₀) ≤ 2 := by
                rw [← h2]; exact ringKrullDim_quotient_le P₀
              exact hex ⟨P₀, hP₀min, le_antisymm hle2 h2le, hQp_mem⟩
            · have hP₀lt : P₀ < Q := hP₀Q.lt_of_ne hP₀eq
              let s : LTSeries (PrimeSpectrum R) :=
                { length := 3
                  toFun := ![⟨P₀, hP₀min.1.1⟩, ⟨Q, hQp⟩, ⟨Q', hQ'p⟩,
                    ⟨IsLocalRing.maximalIdeal R, (IsLocalRing.maximalIdeal.isMaximal R).isPrime⟩]
                  step := fun i => by fin_cases i <;> assumption }
              have h3 : (3 : WithBot ℕ∞) ≤ ringKrullDim R :=
                le_iSup (fun l : LTSeries (PrimeSpectrum R) => (l.length : WithBot ℕ∞)) s
              rw [h2] at h3
              exact absurd h3 (by decide))
        obtain ⟨P, hPmin, hPdim⟩ := SmallCohenMacaulayLeTwo.exists_ltSeries_of_ringKrullDim_eq h2
        have : P.IsPrime := hPmin.1.1
        have : IsLocalRing (R ⧸ P) :=
          IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
        have : IsAdicComplete (IsLocalRing.maximalIdeal (R ⧸ P)) (R ⧸ P) :=
          SmallCohenMacaulayLeTwo.quotient_isAdicComplete P
        have hp_memD : (p : R ⧸ P) ∈ IsLocalRing.maximalIdeal (R ⧸ P) := by
          have hker : RingHom.ker (Ideal.Quotient.mk P) ≤ IsLocalRing.maximalIdeal R := by
            rw [Ideal.mk_ker]
            exact IsLocalRing.le_maximalIdeal hPmin.1.1.ne_top
          have hmap : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk P) =
              IsLocalRing.maximalIdeal (R ⧸ P) :=
            IsLocalRing.eq_maximalIdeal
              (Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective hker)
          rw [← hmap, ← map_natCast (Ideal.Quotient.mk P)]
          exact Ideal.mem_map_of_mem _ hp_memR
        obtain ⟨C, _, _, _, _, _, f, hpC0, hmaxC, hfp, hf_res⟩ :=
          SmallCohenMacaulayLeTwo.exists_cohenRing_hom hp_memD
        exact SmallCohenMacaulayLeTwo.exists_isSmallCohenMacaulay_of_dvr_map hPdim hsop
          hpC0 hmaxC f (by rw [hfp, map_natCast]) hf_res
