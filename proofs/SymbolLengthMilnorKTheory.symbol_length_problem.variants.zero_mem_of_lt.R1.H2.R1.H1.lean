import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1_H2_R1

-- Step SymbolLengthMilnorKTheory.symbol_length_problem.variants.zero_mem_of_lt.R1.H2.R1.H1:
-- K_{m+1}(C(x_1, ..., x_m))/2 = 0 (proved here for every m, the step asks m >= 3).
-- Credit: @hyprspacecoyote
--
-- Proof.
-- (1) Over C, R polynomials without constant term in N > R variables have a common nonzero
--     zero (Krull's height theorem against an explicit chain of primes, plus the
--     Nullstellensatz).
-- (2) Lang's box count over C[x_1, ..., x_m]: a diagonal quadratic form in more than 2^m
--     variables has a nonzero zero (N S^m unknowns against (r + 2S - 1)^m equations, S from a
--     limit argument). Clearing denominators: u(C(x_1, ..., x_m)) <= 2^m.
-- (3) Pfister values by recursion, Q(a :: l) = Q(l) + a Q(l) and P(a :: l) = P(l) + a Q(l).
--     In K_*/2 with -1 a square: a nonzero value q of Q(l) gives {l}{q} = 0 (norm lemma), and
--     a nonzero value e of P(l) gives {l} = {e}{l'} (slot lemma).
-- (4) <<a_1, ..., a_m>> + <c> has 2^m + 1 entries, so it is isotropic. Its pure part takes a
--     value e = -(x^2 + c z^2). Then {a_1, ..., a_m, c} = {l'}{e, c} = 0, and the degenerate
--     cases come from universality of an isotropic pure part.
namespace OMA.Artin2

open MvPolynomial

variable {k : Type*} [Field k]

/-- Substitute `0` for the variables `X j` with `j < i`. -/
noncomputable def kill (N i : ℕ) : MvPolynomial (Fin N) k →ₐ[k] MvPolynomial (Fin N) k :=
  aeval fun j ↦ if (j : ℕ) < i then 0 else X j

theorem kill_succ_comp (N i : ℕ) :
    (kill (k := k) N (i + 1)).comp (kill N i) = kill N (i + 1) := by
  apply MvPolynomial.algHom_ext
  intro j
  simp only [kill, AlgHom.comp_apply, aeval_X]
  split_ifs with h1 h2 <;> simp_all
  omega

theorem ker_kill_le (N i : ℕ) :
    RingHom.ker (kill (k := k) N i) ≤ RingHom.ker (kill (k := k) N (i + 1)) := by
  intro f hf
  rw [RingHom.mem_ker] at hf ⊢
  rw [← kill_succ_comp, AlgHom.comp_apply]
  erw [hf]
  simp

theorem height_ker_kill (N : ℕ) :
    ∀ i ≤ N, (i : ℕ∞) ≤ (RingHom.ker (kill (k := k) N i)).height := by
  intro i
  induction i with
  | zero => intro _; simp
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have : (RingHom.ker (kill (k := k) N i)).IsPrime := RingHom.ker_isPrime _
    have : (RingHom.ker (kill (k := k) N (i + 1))).IsPrime := RingHom.ker_isPrime _
    have hlt : RingHom.ker (kill (k := k) N i) < RingHom.ker (kill (k := k) N (i + 1)) := by
      refine lt_of_le_of_ne (ker_kill_le N i) ?_
      intro h
      have hx : (X ⟨i, by omega⟩ : MvPolynomial (Fin N) k) ∈ RingHom.ker (kill (k := k) N (i + 1)) := by
        rw [RingHom.mem_ker]; simp [kill]
      rw [← h, RingHom.mem_ker] at hx
      simp [kill, X_ne_zero] at hx
    have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    calc ((i + 1 : ℕ) : ℕ∞) = (i : ℕ∞) + 1 := by push_cast; rfl
      _ ≤ (RingHom.ker (kill (k := k) N i)).height + 1 := by gcongr
      _ ≤ _ := this

theorem mem_ker_kill_N {N : ℕ} (f : MvPolynomial (Fin N) k) :
    f ∈ RingHom.ker (kill (k := k) N N) ↔ constantCoeff f = 0 := by
  have : kill (k := k) N N = aeval 0 := by
    apply MvPolynomial.algHom_ext; intro j; simp [kill]
  rw [RingHom.mem_ker, this, aeval_zero]
  simp

/-- Over an algebraically closed field, finitely many polynomials without constant term, fewer
than the number of variables, have a common nonzero zero. -/
theorem exists_common_zero [IsAlgClosed k] {N : ℕ} (s : Finset (MvPolynomial (Fin N) k))
    (hs : s.card < N) (h0 : ∀ f ∈ s, constantCoeff f = 0) :
    ∃ v : Fin N → k, v ≠ 0 ∧ ∀ f ∈ s, eval v f = 0 := by
  by_contra hcon
  push Not at hcon
  set I : Ideal (MvPolynomial (Fin N) k) := Ideal.span (s : Set _)
  set M := RingHom.ker (kill (k := k) N N)
  have hM : M.IsPrime := RingHom.ker_isPrime _
  have hIM : I ≤ M := by
    rw [Ideal.span_le]
    intro f hf
    exact (mem_ker_kill_N f).mpr (h0 f hf)
  -- every common zero of `I` is `0`
  have hzero : ∀ v ∈ zeroLocus k I, v = 0 := by
    intro v hv
    by_contra hv0
    obtain ⟨f, hf, hfv⟩ := hcon v hv0
    apply hfv
    have := (mem_zeroLocus_iff.mp hv) f (Ideal.subset_span hf)
    simpa [aeval_eq_eval] using this
  have hMrad : M ≤ I.radical := by
    rw [← vanishingIdeal_zeroLocus_eq_radical (K := k)]
    intro f hf v hv
    rw [hzero v hv]
    have := (mem_ker_kill_N f).mp hf
    simpa [aeval_zero] using this
  have hmin : M ∈ I.minimalPrimes := by
    refine ⟨⟨hM, hIM⟩, fun q hq hqM ↦ ?_⟩
    exact hMrad.trans ((Ideal.IsPrime.radical_le_iff hq.1).mpr hq.2)
  have h1 := Ideal.height_le_card_of_mem_minimalPrimes_span_finset hmin
  have h2 := height_ker_kill (k := k) N N le_rfl
  have : ((N : ℕ) : ℕ∞) ≤ s.card := h2.trans h1
  exact absurd (by exact_mod_cast this) (not_le.mpr hs)



theorem exists_common_zero' [IsAlgClosed k] {σ : Type*} [Fintype σ]
    (s : Finset (MvPolynomial σ k)) (hs : s.card < Fintype.card σ)
    (h0 : ∀ f ∈ s, constantCoeff f = 0) :
    ∃ v : σ → k, v ≠ 0 ∧ ∀ f ∈ s, eval v f = 0 := by
  classical
  set e := Fintype.equivFin σ
  obtain ⟨w, hw0, hw⟩ := exists_common_zero (s.image (rename e))
    (lt_of_le_of_lt Finset.card_image_le (by simpa using hs)) (by
      intro f hf
      obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf
      rw [constantCoeff_rename]; exact h0 g hg)
  refine ⟨w ∘ e, ?_, ?_⟩
  · intro h; apply hw0; funext j
    have := congrFun h (e.symm j); simpa using this
  · intro f hf
    have := hw (rename e f) (Finset.mem_image_of_mem _ hf)
    rwa [eval_rename] at this

/-- The exponent of `x ^ j * y ^ l`. -/
noncomputable def mono (j l : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 j + Finsupp.single 1 l

@[simp] lemma mono_zero (j l : ℕ) : mono j l 0 = j := by simp [mono]
@[simp] lemma mono_one (j l : ℕ) : mono j l 1 = l := by simp [mono]
lemma eq_mono (m : Fin 2 →₀ ℕ) : m = mono (m 0) (m 1) := by
  ext i; fin_cases i <;> simp

lemma degreeOf_map_le' {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (n : Fin 2) (p : MvPolynomial (Fin 2) R) : degreeOf n (map f p) ≤ degreeOf n p := by
  rw [degreeOf_le_iff]
  intro m hm
  exact monomial_le_degreeOf n (support_map_subset f p hm)

/-- Lang's count for `C(x, y)`: a diagonal quadratic form in `5` variables with polynomial
coefficients has a nonzero polynomial zero. -/
theorem lang_poly (P : Fin 5 → MvPolynomial (Fin 2) ℂ) :
    ∃ W : Fin 5 → MvPolynomial (Fin 2) ℂ, W ≠ 0 ∧ ∑ i, P i * W i ^ 2 = 0 := by
  classical
  set r := ∑ i, (degreeOf 0 (P i) + degreeOf 1 (P i)) with hr
  set S := 5 * r + 5 with hS
  set E := 11 * r + 9 with hE
  have hPr : ∀ i n, degreeOf n (P i) ≤ r := by
    intro i n
    have h1 : degreeOf 0 (P i) + degreeOf 1 (P i) ≤ r :=
      Finset.single_le_sum (f := fun i ↦ degreeOf 0 (P i) + degreeOf 1 (P i))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)
    fin_cases n <;> simp <;> omega
  let U := Fin 5 × Fin S × Fin S
  let V : Fin 5 → MvPolynomial (Fin 2) (MvPolynomial U ℂ) := fun i ↦
    ∑ jl : Fin S × Fin S, monomial (mono jl.1 jl.2) (X (i, jl.1, jl.2))
  let Q : MvPolynomial (Fin 2) (MvPolynomial U ℂ) := ∑ i, map C (P i) * V i ^ 2
  let eqs : Finset (MvPolynomial U ℂ) :=
    (Finset.univ : Finset (Fin E × Fin E)).image fun jl ↦ coeff (mono jl.1 jl.2) Q
  have hV : ∀ i n, degreeOf n (V i) ≤ S - 1 := by
    intro i n
    rw [degreeOf_le_iff]
    intro m hm
    obtain ⟨jl, -, hjl⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
    have := support_monomial_subset hjl
    rw [Finset.mem_singleton] at this
    subst this
    have h1 := jl.1.isLt
    have h2 := jl.2.isLt
    fin_cases n <;> simp <;> omega
  have hQ : ∀ n, degreeOf n Q ≤ r + 2 * (S - 1) := by
    intro n
    refine (degreeOf_sum_le n _ _).trans (Finset.sup_le fun i _ ↦ ?_)
    refine (degreeOf_mul_le n _ _).trans (add_le_add ((degreeOf_map_le' C n _).trans (hPr i n))
      ((degreeOf_pow_le n _ 2).trans ?_))
    exact Nat.mul_le_mul_left 2 (hV i n)
  have hcoeff : ∀ m : Fin 2 →₀ ℕ, E ≤ m 0 ∨ E ≤ m 1 → coeff m Q = 0 := by
    intro m hm
    by_contra hc
    have hsupp : m ∈ Q.support := mem_support_iff.mpr hc
    have h0 := (monomial_le_degreeOf 0 hsupp).trans (hQ 0)
    have h1 := (monomial_le_degreeOf 1 hsupp).trans (hQ 1)
    omega
  have hmap0 : map (constantCoeff : MvPolynomial U ℂ →+* ℂ) Q = 0 := by
    have : ∀ i, map (constantCoeff : MvPolynomial U ℂ →+* ℂ) (V i) = 0 := by
      intro i
      simp [V, map_sum, map_monomial]
    simp [Q, map_sum, this]
  have hcard : eqs.card < Fintype.card U := by
    refine lt_of_le_of_lt Finset.card_image_le ?_
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_fin, U]
    nlinarith
  have h0 : ∀ f ∈ eqs, constantCoeff f = 0 := by
    intro f hf
    obtain ⟨jl, -, rfl⟩ := Finset.mem_image.mp hf
    rw [← coeff_map, hmap0, coeff_zero]
  obtain ⟨t, ht0, ht⟩ := exists_common_zero' (k := ℂ) eqs hcard h0
  let W : Fin 5 → MvPolynomial (Fin 2) ℂ := fun i ↦ map (eval t) (V i)
  have hmapQ : map (eval t) Q = ∑ i, P i * W i ^ 2 := by
    have hc : (eval t).comp (C : ℂ →+* MvPolynomial U ℂ) = RingHom.id ℂ := by
      ext; simp
    simp only [Q, W, map_sum, map_mul, map_pow, map_map, hc, map_id]
  have hQ0 : map (eval t) Q = 0 := by
    ext m
    rw [coeff_map, coeff_zero]
    by_cases hm : m 0 < E ∧ m 1 < E
    · apply ht
      refine Finset.mem_image.mpr ⟨(⟨m 0, hm.1⟩, ⟨m 1, hm.2⟩), Finset.mem_univ _, ?_⟩
      simp only
      rw [← eq_mono m]
    · rw [hcoeff m (by omega), map_zero]
  refine ⟨W, ?_, hmapQ ▸ hQ0⟩
  obtain ⟨⟨i, j, l⟩, hu⟩ := Function.ne_iff.mp ht0
  intro hW
  apply hu
  have hWi : W i = 0 := congrFun hW i
  have key : coeff (mono j l) (W i) = t (i, j, l) := by
    simp only [W, V, map_sum, map_monomial, eval_X, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single (j, l)]
    · simp
    · rintro ⟨j', l'⟩ _ hne
      rw [if_neg]
      intro h
      apply hne
      have e0 := congrArg (fun m ↦ m 0) h
      have e1 := congrArg (fun m ↦ m 1) h
      simp only [mono_zero, mono_one] at e0 e1
      ext <;> simp [e0, e1]
    · simp
  rw [← key, hWi, coeff_zero]
  rfl



/-- Exponent vector of the monomial `∏ x_i ^ e_i`. -/
noncomputable def expo {m : ℕ} (e : Fin m → ℕ) : Fin m →₀ ℕ := Finsupp.equivFunOnFinite.symm e

@[simp] lemma expo_apply {m : ℕ} (e : Fin m → ℕ) (i : Fin m) : expo e i = e i := by
  simp [expo]

lemma expo_injective {m : ℕ} : Function.Injective (expo (m := m)) := by
  intro e e' h; funext i; simpa using congrArg (fun f ↦ f i) h

lemma degreeOf_map_le'' {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S) {m : ℕ}
    (n : Fin m) (p : MvPolynomial (Fin m) R) : degreeOf n (map f p) ≤ degreeOf n p := by
  rw [degreeOf_le_iff]
  intro d hd
  exact monomial_le_degreeOf n (support_map_subset f p hd)

/-- Lang's count over `C[x_1, ..., x_m]`, for a box of side `S`. -/
theorem lang_poly_gen {m : ℕ} {ι : Type*} [Fintype ι] (P : ι → MvPolynomial (Fin m) ℂ)
    (r S : ℕ) (hr : ∀ j n, degreeOf n (P j) ≤ r) (hS : 0 < S)
    (hcnt : (r + 2 * S - 1) ^ m < Fintype.card ι * S ^ m) :
    ∃ W : ι → MvPolynomial (Fin m) ℂ, W ≠ 0 ∧ ∑ j, P j * W j ^ 2 = 0 := by
  classical
  set E := r + 2 * S - 1 with hE
  let U := ι × (Fin m → Fin S)
  let V : ι → MvPolynomial (Fin m) (MvPolynomial U ℂ) := fun j ↦
    ∑ e : Fin m → Fin S, monomial (expo fun i ↦ (e i : ℕ)) (X (j, e))
  let Q : MvPolynomial (Fin m) (MvPolynomial U ℂ) := ∑ j, map C (P j) * V j ^ 2
  let eqs : Finset (MvPolynomial U ℂ) :=
    (Finset.univ : Finset (Fin m → Fin E)).image fun e ↦ coeff (expo fun i ↦ (e i : ℕ)) Q
  have hV : ∀ j n, degreeOf n (V j) ≤ S - 1 := by
    intro j n
    rw [degreeOf_le_iff]
    intro d hd
    obtain ⟨e, -, he⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
    have := support_monomial_subset he
    rw [Finset.mem_singleton] at this
    subst this
    have := (e n).isLt
    simp only [expo_apply]
    omega
  have hQ : ∀ n, degreeOf n Q ≤ r + 2 * (S - 1) := by
    intro n
    refine (degreeOf_sum_le n _ _).trans (Finset.sup_le fun j _ ↦ ?_)
    refine (degreeOf_mul_le n _ _).trans (add_le_add ((degreeOf_map_le'' C n _).trans (hr j n))
      ((degreeOf_pow_le n _ 2).trans ?_))
    exact Nat.mul_le_mul_left 2 (hV j n)
  have hcoeff : ∀ d : Fin m →₀ ℕ, (∃ n, E ≤ d n) → coeff d Q = 0 := by
    rintro d ⟨n, hn⟩
    by_contra hc
    have := (monomial_le_degreeOf n (mem_support_iff.mpr hc)).trans (hQ n)
    omega
  have hmap0 : map (constantCoeff : MvPolynomial U ℂ →+* ℂ) Q = 0 := by
    have : ∀ j, map (constantCoeff : MvPolynomial U ℂ →+* ℂ) (V j) = 0 := by
      intro j
      simp [V, map_sum, map_monomial]
    simp [Q, map_sum, this]
  have hcard : eqs.card < Fintype.card U := by
    refine lt_of_le_of_lt Finset.card_image_le ?_
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_pi, Fintype.card_fin,
      Finset.prod_const, Finset.card_univ, U]
    simpa using hcnt
  have h0 : ∀ f ∈ eqs, constantCoeff f = 0 := by
    intro f hf
    obtain ⟨e, -, rfl⟩ := Finset.mem_image.mp hf
    rw [← coeff_map, hmap0, coeff_zero]
  obtain ⟨t, ht0, ht⟩ := exists_common_zero' (k := ℂ) eqs hcard h0
  let W : ι → MvPolynomial (Fin m) ℂ := fun j ↦ map (eval t) (V j)
  have hmapQ : map (eval t) Q = ∑ j, P j * W j ^ 2 := by
    have hc : (eval t).comp (C : ℂ →+* MvPolynomial U ℂ) = RingHom.id ℂ := by
      ext; simp
    simp only [Q, W, map_sum, map_mul, map_pow, map_map, hc, map_id]
  have hQ0 : map (eval t) Q = 0 := by
    ext d
    rw [coeff_map, coeff_zero]
    by_cases hd : ∀ n, d n < E
    · apply ht
      refine Finset.mem_image.mpr ⟨fun n ↦ ⟨d n, hd n⟩, Finset.mem_univ _, ?_⟩
      congr 1
      ext n
      simp
    · push Not at hd
      rw [hcoeff d hd, map_zero]
  refine ⟨W, ?_, hmapQ ▸ hQ0⟩
  obtain ⟨⟨j, e⟩, hu⟩ := Function.ne_iff.mp ht0
  intro hW
  apply hu
  have hWj : W j = 0 := congrFun hW j
  have key : coeff (expo fun i ↦ (e i : ℕ)) (W j) = t (j, e) := by
    simp only [W, V, map_sum, map_monomial, eval_X, coeff_sum, coeff_monomial]
    rw [Finset.sum_eq_single e]
    · simp
    · intro e' _ hne
      rw [if_neg]
      intro h
      apply hne
      funext i
      have := congrArg (fun f ↦ f i) (expo_injective h)
      exact Fin.ext (by simpa using this)
    · simp
  rw [← key, hWj, coeff_zero]
  rfl

/-- A box side that makes Lang's count work when there are more than `2 ^ m` variables. -/
theorem exists_side (m r N : ℕ) (hN : 2 ^ m < N) :
    ∃ S, 0 < S ∧ (r + 2 * S - 1) ^ m < N * S ^ m := by
  have hlim : Filter.Tendsto (fun S : ℕ ↦ ((r : ℝ) / S + 2) ^ m) Filter.atTop
      (nhds ((0 + 2) ^ m)) :=
    ((tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)).add_const 2).pow m
  have hlt : ((0 : ℝ) + 2) ^ m < N := by
    rw [zero_add]; exact_mod_cast hN
  obtain ⟨S, hS1, hS⟩ :=
    ((Filter.eventually_ge_atTop 1).and (hlim.eventually (gt_mem_nhds hlt))).exists
  refine ⟨S, hS1, ?_⟩
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS1
  have h1 : ((r + 2 * S : ℕ) : ℝ) ^ m < N * (S : ℝ) ^ m := by
    have : ((r : ℝ) / S + 2) ^ m * (S : ℝ) ^ m = ((r + 2 * S : ℕ) : ℝ) ^ m := by
      rw [← mul_pow]; congr 1; push_cast; field_simp
    rw [← this]
    exact mul_lt_mul_of_pos_right hS (pow_pos hSpos m)
  have h2 : (r + 2 * S) ^ m < N * S ^ m := by exact_mod_cast h1
  exact lt_of_le_of_lt (Nat.pow_le_pow_left (Nat.sub_le _ _) m) h2

/-- `C(x_1, ..., x_m)` has `u`-invariant at most `2 ^ m`. -/
theorem isotropic_gen {m : ℕ} {ι : Type*} [Fintype ι] (hι : 2 ^ m < Fintype.card ι)
    (q : ι → MvRatFunc (Fin m) ℂ) :
    ∃ v : ι → MvRatFunc (Fin m) ℂ, v ≠ 0 ∧ ∑ j, q j * v j ^ 2 = 0 := by
  classical
  have hex : ∀ j, ∃ nd : MvPolynomial (Fin m) ℂ × MvPolynomial (Fin m) ℂ, nd.2 ≠ 0 ∧
      q j = algebraMap _ (MvRatFunc (Fin m) ℂ) nd.1 / algebraMap _ (MvRatFunc (Fin m) ℂ) nd.2 := by
    intro j
    obtain ⟨n, d, hd, h⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin m) ℂ) (q j)
    exact ⟨(n, d), nonZeroDivisors.ne_zero hd, h.symm⟩
  choose nd hd hq using hex
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin m) ℂ) (MvRatFunc (Fin m) ℂ)) :=
    IsFractionRing.injective _ _
  let P : ι → MvPolynomial (Fin m) ℂ := fun j ↦
    (nd j).1 * ∏ k ∈ Finset.univ.erase j, (nd k).2
  set r := ∑ j, ∑ n, degreeOf n (P j)
  have hr : ∀ j n, degreeOf n (P j) ≤ r := by
    intro j n
    exact (Finset.single_le_sum (f := fun n ↦ degreeOf n (P j)) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ n)).trans (Finset.single_le_sum (f := fun j ↦ ∑ n, degreeOf n (P j))
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ j))
  obtain ⟨S, hS, hcnt⟩ := exists_side m r (Fintype.card ι) hι
  obtain ⟨W, hW0, hW⟩ := lang_poly_gen P r S hr hS hcnt
  set Dn := ∏ k, (nd k).2
  have hDn : algebraMap _ (MvRatFunc (Fin m) ℂ) Dn ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (Finset.prod_ne_zero_iff.mpr fun k _ ↦ hd k)
  have hP : ∀ j, algebraMap _ (MvRatFunc (Fin m) ℂ) (P j) =
      q j * algebraMap _ (MvRatFunc (Fin m) ℂ) Dn := by
    intro j
    have hdj : algebraMap _ (MvRatFunc (Fin m) ℂ) (nd j).2 ≠ 0 := (map_ne_zero_iff _ hinj).mpr (hd j)
    simp only [P, Dn, map_mul, map_prod, hq j]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun k ↦ algebraMap _ (MvRatFunc (Fin m) ℂ) (nd k).2) (Finset.mem_univ j)]
    field_simp
  refine ⟨fun j ↦ algebraMap _ (MvRatFunc (Fin m) ℂ) (W j), ?_, ?_⟩
  · intro h
    apply hW0
    funext j
    have := congrFun h j
    simp only [Pi.zero_apply] at this ⊢
    exact (map_eq_zero_iff _ hinj).mp this
  · have := congrArg (algebraMap _ (MvRatFunc (Fin m) ℂ)) hW
    simp only [map_sum, map_mul, map_pow, map_zero, hP] at this
    have h2 : (∑ j, q j * algebraMap _ (MvRatFunc (Fin m) ℂ) (W j) ^ 2) *
        algebraMap _ (MvRatFunc (Fin m) ℂ) Dn = 0 := by
      rw [Finset.sum_mul, ← this]
      refine Finset.sum_congr rfl fun j _ ↦ by ring
    exact (mul_eq_zero.mp h2).resolve_right hDn

end OMA.Artin2


namespace OMA.Artin2K

open MilnorK

variable {F : Type*} [Field F]

theorem add_self_eq_zero (x : MilnorK F 2) : x + x = 0 := by
  have h2 : (2 : MilnorK F 2) = 0 := by exact_mod_cast natCast_eq_zero (F := F) 2
  rw [← two_mul, h2, zero_mul]

theorem neg_eq_self (x : MilnorK F 2) : -x = x := by
  rw [neg_eq_iff_add_eq_zero, add_self_eq_zero]

theorem of_sq (u : Fˣ) : of 2 (u ^ 2) = 0 := by
  rw [of_pow, two_smul, add_self_eq_zero]

theorem of_neg_one (hi : ∃ i : F, i * i = -1) : of 2 (-1 : Fˣ) = 0 := by
  obtain ⟨i, hi⟩ := hi
  have hi0 : i ≠ 0 := by
    rintro rfl; simp at hi
  have : (-1 : Fˣ) = (Units.mk0 i hi0) ^ 2 := by
    ext; simp [sq, hi]
  rw [this, of_sq]

theorem of_neg (hi : ∃ i : F, i * i = -1) (a : Fˣ) : of 2 (-a) = of 2 a := by
  rw [show -a = (-1) * a by simp, of_mul, of_neg_one hi, zero_add]

theorem of_mul_self (hi : ∃ i : F, i * i = -1) (a : Fˣ) : of 2 a * of 2 a = 0 := by
  by_cases ha : a = 1
  · simp [ha]
  have h1 : (1 : F) - a ≠ 0 := by
    intro h; apply ha; apply Units.ext; show (a : F) = 1; linear_combination -h
  have h2 : (1 : F) - (a⁻¹ : Fˣ) ≠ 0 := by
    intro h; apply ha; apply Units.ext; show (a : F) = 1
    have : ((a⁻¹ : Fˣ) : F) = 1 := by linear_combination -h
    simpa using congrArg (fun z : F ↦ z⁻¹) this
  set b := Units.mk0 _ h1
  set c := Units.mk0 _ h2
  have hb : of 2 a * of 2 b = 0 := of_mul_of_eq_zero 2 a b (by simp [b])
  have hc : of 2 a⁻¹ * of 2 c = 0 := of_mul_of_eq_zero 2 a⁻¹ c (by simp [c])
  have hc' : of 2 a * of 2 c = 0 := by
    rw [of_inv, neg_eq_self] at hc; exact hc
  have hneg : -a = b * c⁻¹ := by
    have ha0 : (a : F) ≠ 0 := a.ne_zero
    ext
    simp only [Units.val_neg, Units.val_mul, b, c, Units.val_mk0, Units.val_inv_eq_inv_val]
    field_simp
    have : (a : F) - 1 ≠ 0 := by intro h; apply h1; linear_combination -h
    field_simp
    ring
  have : of 2 a * of 2 (-a) = 0 := by
    rw [hneg, of_mul, of_inv, neg_eq_self, mul_add, hb, hc', add_zero]
  rwa [of_neg hi] at this

theorem of_comm (hi : ∃ i : F, i * i = -1) (a b : Fˣ) : of 2 a * of 2 b = of 2 b * of 2 a := by
  have h := of_mul_self hi (a * b)
  rw [of_mul, add_mul, mul_add, mul_add, of_mul_self hi a, of_mul_self hi b, zero_add,
    add_zero] at h
  rw [← neg_eq_self (of 2 b * of 2 a)]
  exact eq_neg_of_add_eq_zero_left h

/-- `{s, t} = {e, s t}` when `s + t = e`. -/
theorem steinberg2 (hi : ∃ i : F, i * i = -1) (s t e : Fˣ) (h : (s : F) + t = e) :
    of 2 s * of 2 t = of 2 e * of 2 (s * t) := by
  have hst : of 2 (s * e⁻¹) * of 2 (t * e⁻¹) = 0 :=
    of_mul_of_eq_zero 2 _ _ (by
      have he : (e : F) ≠ 0 := e.ne_zero
      simp only [Units.val_mul, Units.val_inv_eq_inv_val]
      field_simp; linear_combination h)
  simp only [of_mul, of_inv, neg_eq_self] at hst
  rw [add_mul, mul_add, mul_add, of_mul_self hi e, add_zero] at hst
  rw [of_mul, mul_add, of_comm hi e s]
  have h3 : of 2 s * of 2 t = -(of 2 s * of 2 e + of 2 e * of 2 t) :=
    eq_neg_of_add_eq_zero_left (by rw [← add_assoc]; exact hst)
  rw [h3, neg_eq_self]

/-- If `e = a x² + b y²` then `{a, b} = {e, a b}`. -/
theorem slot2 (hi : ∃ i : F, i * i = -1) (a b e : Fˣ) (x y : F) (h : (e : F) = a * x ^ 2 + b * y ^ 2) :
    of 2 a * of 2 b = of 2 e * of 2 (a * b) := by
  by_cases hx : x = 0
  · have hy : y ≠ 0 := by rintro rfl; subst hx; simp at h
    have he : e = b * (Units.mk0 y hy) ^ 2 := by ext; simp [h, hx]
    rw [he, of_mul, of_sq, add_zero, of_mul, mul_add, of_mul_self hi, add_zero, of_comm hi]
  by_cases hy : y = 0
  · have he : e = a * (Units.mk0 x hx) ^ 2 := by ext; simp [h, hy]
    rw [he, of_mul, of_sq, add_zero, of_mul, mul_add, of_mul_self hi, zero_add]
  set s := a * (Units.mk0 x hx) ^ 2
  set t := b * (Units.mk0 y hy) ^ 2
  have hst := steinberg2 hi s t e (by simp [s, t, h])
  have e1 : of 2 s = of 2 a := by simp only [s, of_mul, of_sq, add_zero]
  have e2 : of 2 t = of 2 b := by simp only [t, of_mul, of_sq, add_zero]
  have e3 : of 2 (s * t) = of 2 (a * b) := by
    simp only [s, t, of_mul, of_sq, add_zero]
  rw [e1, e2, e3] at hst
  exact hst

/-- If `u = x² + b z² ≠ 0` then `{u, b} = 0`. -/
theorem norm_slot (hi : ∃ i : F, i * i = -1) (b u : Fˣ) (x z : F) (h : (u : F) = x ^ 2 + b * z ^ 2) :
    of 2 u * of 2 b = 0 := by
  have := slot2 hi b 1 u z x (by rw [h]; simp; ring)
  rw [of_one, mul_zero, mul_one] at this
  exact this.symm

/-- If `e = a x² + b y² + a b z² ≠ 0` then `{a, b} = {e, f}` for some `f`. -/
theorem slot3 (hi : ∃ i : F, i * i = -1) (a b e : Fˣ) (x y z : F) (h : (e : F) = a * x ^ 2 + b * y ^ 2 + a * b * z ^ 2) :
    ∃ f : Fˣ, of 2 a * of 2 b = of 2 e * of 2 f := by
  by_cases hu : x ^ 2 + (b : F) * z ^ 2 = 0
  · exact ⟨a * b, slot2 hi a b e 0 y (by rw [h]; linear_combination (a : F) * hu)⟩
  set u := Units.mk0 _ hu
  have hub := norm_slot hi b u x z rfl
  refine ⟨a * u * b, ?_⟩
  have h2 := slot2 hi (a * u) b e 1 y (by rw [h]; simp [u]; ring)
  rw [of_mul 2 a u, add_mul, hub, add_zero] at h2
  exact h2

/-- If `a x² + b y² + a b z² = 0` with `(x, y, z) ≠ 0` then `{a, b} = 0`. -/
theorem slot3_zero (hi : ∃ i : F, i * i = -1) (a b : Fˣ) (x y z : F) (hne : x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0)
    (h : (a : F) * x ^ 2 + b * y ^ 2 + a * b * z ^ 2 = 0) : of 2 a * of 2 b = 0 := by
  by_cases hu : x ^ 2 + (b : F) * z ^ 2 = 0
  · have hy : (b : F) * y ^ 2 = 0 := by linear_combination h - (a : F) * hu
    have hy0 : y = 0 := by
      rcases mul_eq_zero.mp hy with hb | hy
      · exact absurd hb b.ne_zero
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hy
    have hz : z ≠ 0 := by
      rintro rfl
      have : x = 0 := by simpa using hu
      rcases hne with h1 | h1 | h1 <;> contradiction
    have hx : x ≠ 0 := by
      rintro rfl
      have : (b : F) * z ^ 2 = 0 := by simpa using hu
      rcases mul_eq_zero.mp this with hb | hz'
      · exact b.ne_zero hb
      · exact hz (pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz')
    have hb : b = -(Units.mk0 x hx * (Units.mk0 z hz)⁻¹) ^ 2 := by
      ext
      simp only [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mk0,
        Units.val_inv_eq_inv_val]
      field_simp
      linear_combination hu
    rw [hb, of_neg hi, of_sq, mul_zero]
  · set u := Units.mk0 _ hu
    have hub := norm_slot hi b u x z rfl
    have hy : y ≠ 0 := by
      rintro rfl
      apply hu
      have : (a : F) * (x ^ 2 + b * z ^ 2) = 0 := by linear_combination h
      exact (mul_eq_zero.mp this).resolve_left a.ne_zero
    -- a u = -b y², so a = -b y² u⁻¹
    have ha : a = -(b * (Units.mk0 y hy) ^ 2 * u⁻¹) := by
      ext
      have hu0 : (u : F) ≠ 0 := u.ne_zero
      simp only [Units.val_neg, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_mk0,
        Units.val_inv_eq_inv_val]
      field_simp
      simp only [u, Units.val_mk0]
      linear_combination h
    rw [ha, of_neg hi, of_mul, of_mul, of_sq, add_zero, of_inv, neg_eq_self, add_mul,
      of_mul_self hi, hub, add_zero]

/-- Common slot: over a field where `-1` is a square and every diagonal quadratic form in `5`
variables is isotropic, the sum of two symbols mod `2` is a symbol. -/
theorem sum_two (hi : ∃ i : F, i * i = -1) (hu : ∀ q : Fin 5 → F, ∃ v : Fin 5 → F, v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0)
    (a b c d : Fˣ) : ∃ e f : Fˣ, of 2 a * of 2 b + of 2 c * of 2 d = of 2 e * of 2 f := by
  obtain ⟨i, hi'⟩ := hi
  obtain ⟨v, hv0, hv⟩ := hu ![a, b, a * b, c, d]
  replace hv : (a : F) * v 0 ^ 2 + b * v 1 ^ 2 + a * b * v 2 ^ 2 + c * v 3 ^ 2 + d * v 4 ^ 2 = 0 := by
    simpa [Fin.sum_univ_five] using hv
  set E : F := a * v 0 ^ 2 + b * v 1 ^ 2 + a * b * v 2 ^ 2 with hE
  by_cases hE0 : E = 0
  · have hcd : (c : F) * v 3 ^ 2 + d * v 4 ^ 2 = 0 := by linear_combination hv - hE0
    by_cases hx : v 0 ≠ 0 ∨ v 1 ≠ 0 ∨ v 2 ≠ 0
    · refine ⟨c, d, ?_⟩
      rw [slot3_zero ⟨i, hi'⟩ a b _ _ _ hx hE0, zero_add]
    · push Not at hx
      have hy : v 3 ≠ 0 ∨ v 4 ≠ 0 := by
        by_contra hy; push Not at hy
        apply hv0; funext j; fin_cases j <;> simp [hx, hy]
      refine ⟨a, b, ?_⟩
      have := slot3_zero ⟨i, hi'⟩ c d (v 3) (v 4) 0 (by tauto) (by simpa using hcd)
      rw [this, add_zero]
  · set e := Units.mk0 E hE0
    obtain ⟨f, hf⟩ := slot3 ⟨i, hi'⟩ a b e (v 0) (v 1) (v 2) rfl
    have hcd := slot2 ⟨i, hi'⟩ c d e (i * v 3) (i * v 4) (by
      simp only [e, Units.val_mk0]
      linear_combination (-(c : F) * v 3 ^ 2 - d * v 4 ^ 2) * hi' + hv)
    refine ⟨e, f * (c * d), ?_⟩
    rw [hf, hcd, ← mul_add, ← of_mul]

end OMA.Artin2K

namespace OMA.PfK

open MilnorK OMA.Artin2K

variable {F : Type*} [Field F]

/-- The class `{a_1, ..., a_n}` of a list of units. -/
noncomputable def S (l : List Fˣ) : MilnorK F 2 := (l.map (of 2)).prod

@[simp] lemma S_nil : S ([] : List Fˣ) = 1 := rfl

@[simp] lemma S_cons (a : Fˣ) (l : List Fˣ) : S (a :: l) = of 2 a * S l := by
  simp [S]

lemma commute_S (hi : ∃ i : F, i * i = -1) (a : Fˣ) (l : List Fˣ) :
    Commute (of 2 a) (S l) := by
  induction l with
  | nil => exact Commute.one_right _
  | cons b l ih => rw [S_cons]; exact Commute.mul_right (of_comm hi a b) ih

/-- Values (including `0`) of the Pfister form `<<l>>`. -/
def Qv : List Fˣ → Set F
  | [] => {y | ∃ x, y = x ^ 2}
  | a :: l => {y | ∃ q₁ ∈ Qv l, ∃ q₂ ∈ Qv l, y = q₁ + a * q₂}

/-- Values (including `0`) of the pure part of `<<l>>`. -/
def Pv : List Fˣ → Set F
  | [] => {0}
  | a :: l => {y | ∃ p ∈ Pv l, ∃ q ∈ Qv l, y = p + a * q}

/-- Values of a Pfister form are norms: `{l, q} = 0`. -/
theorem norm_Qv (hi : ∃ i : F, i * i = -1) :
    ∀ (l : List Fˣ) (q : Fˣ), (q : F) ∈ Qv l → S l * of 2 q = 0 := by
  intro l
  induction l with
  | nil =>
    rintro q ⟨x, hx⟩
    have hx0 : x ≠ 0 := by rintro rfl; exact q.ne_zero (by simpa using hx)
    have : q = (Units.mk0 x hx0) ^ 2 := by ext; simp [hx]
    rw [this, of_sq, mul_zero]
  | cons a l ih =>
    rintro q ⟨q₁, h₁, q₂, h₂, hq⟩
    have hcomm := commute_S hi a l
    rw [S_cons]
    by_cases hq₂ : q₂ = 0
    · have hq₁ : q₁ ≠ 0 := by rintro rfl; apply q.ne_zero; rw [hq, hq₂]; simp
      have hu : ((Units.mk0 q₁ hq₁ : Fˣ) : F) ∈ Qv l := by simpa using h₁
      have : q = Units.mk0 q₁ hq₁ := by ext; simp [hq, hq₂]
      rw [this, mul_assoc, ih _ hu, mul_zero]
    by_cases hq₁ : q₁ = 0
    · have hu : ((Units.mk0 q₂ hq₂ : Fˣ) : F) ∈ Qv l := by simpa using h₂
      have : q = a * Units.mk0 q₂ hq₂ := by ext; simp [hq, hq₁]
      rw [this, of_mul, mul_add]
      have t1 : of 2 a * S l * of 2 a = 0 := by
        rw [mul_assoc, ← hcomm.eq, ← mul_assoc, of_mul_self hi, zero_mul]
      have t2 : of 2 a * S l * of 2 (Units.mk0 q₂ hq₂) = 0 := by
        rw [mul_assoc, ih _ hu, mul_zero]
      rw [t1, t2, add_zero]
    set u₁ := Units.mk0 q₁ hq₁ with hu₁def
    set u₂ := Units.mk0 q₂ hq₂ with hu₂def
    have hu1 : (u₁ : F) ∈ Qv l := by simpa [hu₁def] using h₁
    have hu2 : (u₂ : F) ∈ Qv l := by simpa [hu₂def] using h₂
    set c := a * u₂ * u₁⁻¹ with hcdef
    have hw : (1 : F) + c ≠ 0 := by
      intro h
      apply q.ne_zero
      rw [hq]
      have : (q₁ : F) + a * q₂ = q₁ * (1 + c) := by
        simp only [hcdef, hu₁def, hu₂def, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val]
        field_simp
      rw [this, h, mul_zero]
    set w := Units.mk0 _ hw with hwdef
    have hqw : q = u₁ * w := by
      ext
      simp only [hq, hwdef, hu₁def, hcdef, hu₂def, Units.val_mul, Units.val_mk0,
        Units.val_inv_eq_inv_val]
      field_simp
    have ha : a = c * u₁ * u₂⁻¹ := by
      rw [hcdef]; group
    have hcw : of 2 c * of 2 w = 0 := by
      have := of_mul_of_eq_zero 2 (-c) w (by simp only [hwdef, Units.val_neg, Units.val_mk0]; ring)
      rwa [of_neg hi] at this
    rw [hqw, of_mul, mul_add]
    have t1 : of 2 a * S l * of 2 u₁ = 0 := by rw [mul_assoc, ih u₁ hu1, mul_zero]
    have t2 : of 2 a * S l * of 2 w = 0 := by
      rw [hcomm.eq, mul_assoc]
      have hsplit : of 2 a * of 2 w = of 2 u₁ * of 2 w + of 2 u₂ * of 2 w := by
        rw [ha, of_mul, of_mul, of_inv, OMA.Artin2K.neg_eq_self, add_mul, add_mul, hcw, zero_add]
      rw [hsplit, mul_add, ← mul_assoc, ← mul_assoc, ih u₁ hu1, ih u₂ hu2, zero_mul, add_zero]
    rw [t1, t2, add_zero]

/-- Slot lemma: a nonzero value `e` of the pure part of `<<l>>` is a slot of `{l}`. -/
theorem slot_Pv (hi : ∃ i : F, i * i = -1) :
    ∀ (l : List Fˣ) (e : Fˣ), (e : F) ∈ Pv l → ∃ l' : List Fˣ, S l = of 2 e * S l' := by
  intro l
  induction l with
  | nil =>
    rintro e he
    exact absurd (show (e : F) = 0 from he) e.ne_zero
  | cons a l ih =>
    rintro e ⟨p, hp, q, hq, he⟩
    by_cases hq0 : q = 0
    · obtain ⟨l', hl'⟩ := ih e (by rw [he, hq0, mul_zero, add_zero]; exact hp)
      refine ⟨a :: l', ?_⟩
      rw [S_cons, hl', S_cons, ← mul_assoc, ← mul_assoc, of_comm hi a e]
    set uq := Units.mk0 q hq0 with huqdef
    have hnorm := norm_Qv hi l uq (by simpa [huqdef] using hq)
    have hSa : S (a :: l) = S l * of 2 (a * uq) := by
      rw [S_cons, (commute_S hi a l).eq, of_mul, mul_add, hnorm, add_zero]
    by_cases hp0 : p = 0
    · refine ⟨l, ?_⟩
      have : e = a * uq := by ext; simp [he, hp0, huqdef]
      rw [hSa, ← this, (commute_S hi e l).eq]
    set up := Units.mk0 p hp0 with hupdef
    obtain ⟨l', hl'⟩ := ih up (by simpa [hupdef] using hp)
    set c := a * uq
    have hst := steinberg2 hi up c e (by simp [hupdef, c, huqdef, he])
    refine ⟨(up * c) :: l', ?_⟩
    rw [hSa, hl', S_cons, mul_assoc, ← (commute_S hi c l').eq, ← mul_assoc, hst, mul_assoc]

/-- The coefficient `∏_{i ∈ s} a_i` of the Pfister form. -/
noncomputable def coef {n : ℕ} (a : Fin n → Fˣ) (s : Fin n → Bool) : F :=
  ∏ i, if s i then (a i : F) else 1

lemma coef_ne_zero {n : ℕ} (a : Fin n → Fˣ) (s : Fin n → Bool) : coef a s ≠ 0 := by
  unfold coef
  refine Finset.prod_ne_zero_iff.mpr fun i _ ↦ ?_
  split_ifs
  · exact (a i).ne_zero
  · exact one_ne_zero

lemma coef_false {n : ℕ} (a : Fin n → Fˣ) : coef a (fun _ ↦ false) = 1 := by
  simp [coef]

lemma coef_cons {n : ℕ} (a : Fin (n + 1) → Fˣ) (b : Bool) (t : Fin n → Bool) :
    coef a (Fin.cons b t) = (if b then (a 0 : F) else 1) * coef (fun i ↦ a i.succ) t := by
  simp [coef, Fin.prod_univ_succ]

lemma sum_cons {n : ℕ} (g : (Fin (n + 1) → Bool) → F) :
    ∑ s, g s = ∑ t : Fin n → Bool, g (Fin.cons true t) + ∑ t : Fin n → Bool, g (Fin.cons false t) := by
  rw [← Fintype.sum_equiv (Fin.consEquiv fun _ ↦ Bool) (fun p ↦ g (Fin.cons p.1 p.2)) g
    (fun _ ↦ rfl), Fintype.sum_prod_type, Fintype.sum_bool]

/-- Values of the diagonal form `∑ coef a s * x_s ^ 2` lie in `Qv`, and in `Pv` when the
coefficient of `1` is not used. -/
theorem mem_Qv_Pv : ∀ (n : ℕ) (a : Fin n → Fˣ) (x : (Fin n → Bool) → F),
    (∑ s, coef a s * x s ^ 2 ∈ Qv (List.ofFn a)) ∧
    (x (fun _ ↦ false) = 0 → ∑ s, coef a s * x s ^ 2 ∈ Pv (List.ofFn a)) := by
  intro n
  induction n with
  | zero =>
    intro a x
    have hs : ∀ s : Fin 0 → Bool, s = fun _ ↦ false := fun s ↦ funext fun i ↦ i.elim0
    have hsum : ∑ s, coef a s * x s ^ 2 = x (fun _ ↦ false) ^ 2 := by
      rw [Fintype.sum_eq_single (fun _ ↦ false) (fun s h ↦ absurd (hs s) h), coef_false, one_mul]
    refine ⟨⟨x (fun _ ↦ false), hsum⟩, fun h0 ↦ ?_⟩
    show _ = (0 : F)
    rw [hsum, h0]; ring
  | succ n ih =>
    intro a x
    rw [List.ofFn_succ]
    have hsplit : ∑ s, coef a s * x s ^ 2 =
        ∑ t, coef (fun i ↦ a i.succ) t * x (Fin.cons false t) ^ 2 +
        a 0 * ∑ t, coef (fun i ↦ a i.succ) t * x (Fin.cons true t) ^ 2 := by
      rw [sum_cons, Finset.mul_sum, add_comm]
      congr 1
      · refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [coef_cons]; simp
      · refine Finset.sum_congr rfl fun t _ ↦ ?_
        rw [coef_cons]; simp; ring
    obtain ⟨h1, h1'⟩ := ih (fun i ↦ a i.succ) (fun t ↦ x (Fin.cons false t))
    obtain ⟨h2, -⟩ := ih (fun i ↦ a i.succ) (fun t ↦ x (Fin.cons true t))
    refine ⟨⟨_, h1, _, h2, hsplit⟩, fun h0 ↦ ⟨_, h1' ?_, _, h2, hsplit⟩⟩
    have : (Fin.cons false (fun _ ↦ false) : Fin (n + 1) → Bool) = fun _ ↦ false := by
      funext i; refine Fin.cases rfl (fun j ↦ rfl) i
    simpa [this] using h0

/-- An isotropic pure part represents `1`. -/
theorem pure_universal {n : ℕ} (h2 : (2 : F) ≠ 0) (a : Fin n → Fˣ)
    (x : (Fin n → Bool) → F) (hx0 : x (fun _ ↦ false) = 0) (hx : x ≠ 0)
    (hsum : ∑ s, coef a s * x s ^ 2 = 0) :
    ∃ y : (Fin n → Bool) → F, y (fun _ ↦ false) = 0 ∧ ∑ s, coef a s * y s ^ 2 = 1 := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hx
  have hk0 : k ≠ fun _ ↦ false := by rintro rfl; exact hk hx0
  have hck := coef_ne_zero a k
  have hk' : x k ≠ 0 := hk
  set lam := (1 - coef a k) / (2 * coef a k * x k)
  refine ⟨fun s ↦ lam * x s + if s = k then 1 else 0, ?_, ?_⟩
  · simp [hx0, Ne.symm hk0]
  · have : ∀ s, coef a s * (lam * x s + if s = k then 1 else 0) ^ 2 =
        lam ^ 2 * (coef a s * x s ^ 2) +
          (if s = k then 2 * lam * coef a k * x k + coef a k else 0) := by
      intro s
      split_ifs with h
      · subst h; ring
      · ring
    rw [Finset.sum_congr rfl fun s _ ↦ this s, Finset.sum_add_distrib, ← Finset.mul_sum, hsum,
      mul_zero, zero_add, Finset.sum_ite_eq' Finset.univ k, if_pos (Finset.mem_univ k)]
    simp only [lam]
    field_simp
    ring

/-- `K_{m+1}/2 = 0` once `-1` is a square, `2 ≠ 0`, and forms of dimension `2^m + 1` are
isotropic: `{a_1, ..., a_m, c} = 0`. -/
theorem kill (hi : ∃ i : F, i * i = -1) (h2 : (2 : F) ≠ 0) {m : ℕ}
    (hu : ∀ q : ((Fin m → Bool) ⊕ Unit) → F, ∃ v : ((Fin m → Bool) ⊕ Unit) → F, v ≠ 0 ∧
      ∑ j, q j * v j ^ 2 = 0)
    (a : Fin m → Fˣ) (c : Fˣ) : S (List.ofFn a) * of 2 c = 0 := by
  classical
  obtain ⟨i, hi'⟩ := hi
  obtain ⟨v, hv0, hv⟩ := hu (Sum.elim (coef a) fun _ ↦ (c : F))
  rw [Fintype.sum_sum_type] at hv
  simp only [Sum.elim_inl, Sum.elim_inr, Fintype.univ_unit, Finset.sum_singleton] at hv
  set x : (Fin m → Bool) → F := fun s ↦ v (Sum.inl s)
  set z := v (Sum.inr ())
  set o : Fin m → Bool := fun _ ↦ false
  set x' := Function.update x o 0
  set E := ∑ s, coef a s * x' s ^ 2
  have hv' : ∑ s, coef a s * x s ^ 2 + c * z ^ 2 = 0 := hv
  have hx_split : ∑ s, coef a s * x s ^ 2 =
      x o ^ 2 + ∑ s ∈ Finset.univ.erase o, coef a s * x s ^ 2 := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o), coef_false, one_mul]
  have hE_split : E = ∑ s ∈ Finset.univ.erase o, coef a s * x s ^ 2 := by
    simp only [E]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ o)]
    simp only [x', Function.update_self]
    rw [zero_pow two_ne_zero, mul_zero, zero_add]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
  have hE : E + x o ^ 2 + c * z ^ 2 = 0 := by
    rw [hx_split] at hv'; rw [hE_split]; linear_combination hv'
  have hEP : E ∈ Pv (List.ofFn a) := (mem_Qv_Pv m a x').2 (by show x' o = 0; simp [x'])
  by_cases hE0 : E = 0
  · have hoz : x o ^ 2 + (c : F) * z ^ 2 = 0 := by linear_combination hE - hE0
    by_cases hz : z = 0
    · have hxo : x o = 0 := by simpa [hz] using hoz
      -- pure part isotropic
      have hx' : x' = x := by
        funext s; by_cases hs : s = o
        · subst hs; simp [x', hxo]
        · simp [x', Function.update_of_ne hs]
      have hxne : x ≠ 0 := by
        intro h; apply hv0; funext j
        rcases j with s | u
        · exact congrFun h s
        · cases u; exact hz
      obtain ⟨y, hy0, hy⟩ := pure_universal h2 a x hxo hxne (by rw [← hx']; exact hE0)
      have h1 : ((1 : Fˣ) : F) ∈ Pv (List.ofFn a) := by
        rw [Units.val_one, ← hy]; exact (mem_Qv_Pv m a y).2 hy0
      obtain ⟨l', hl'⟩ := slot_Pv ⟨i, hi'⟩ _ 1 h1
      rw [hl', of_one, zero_mul, zero_mul]
    · have hxo : x o ≠ 0 := by
        intro h; apply hz
        have : (c : F) * z ^ 2 = 0 := by simpa [h] using hoz
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp
          ((mul_eq_zero.mp this).resolve_left c.ne_zero)
      have hc : c = -(Units.mk0 (x o) hxo * (Units.mk0 z hz)⁻¹) ^ 2 := by
        ext
        simp only [Units.val_neg, Units.val_pow_eq_pow_val, Units.val_mul, Units.val_mk0,
          Units.val_inv_eq_inv_val]
        field_simp
        linear_combination hoz
      rw [hc, of_neg ⟨i, hi'⟩, of_sq, mul_zero]
  · set e := Units.mk0 E hE0
    obtain ⟨l', hl'⟩ := slot_Pv ⟨i, hi'⟩ _ e hEP
    have hec : of 2 e * of 2 c = 0 :=
      norm_slot ⟨i, hi'⟩ c e (i * x o) (i * z) (by
        simp only [e, Units.val_mk0]
        linear_combination (-(x o) ^ 2 - (c : F) * z ^ 2) * hi' + hE)
    rw [hl', mul_assoc, ← (commute_S ⟨i, hi'⟩ c l').eq, ← mul_assoc, hec, zero_mul]

end OMA.PfK

namespace OMA.PfK

open MilnorK

theorem sqrt_neg_one (m : ℕ) : ∃ i : MvRatFunc (Fin m) ℂ, i * i = -1 :=
  ⟨algebraMap (MvPolynomial (Fin m) ℂ) _ (MvPolynomial.C Complex.I), by
    rw [← map_mul, ← MvPolynomial.C_mul, Complex.I_mul_I, MvPolynomial.C_neg,
      MvPolynomial.C_1, map_neg, map_one]⟩

theorem two_ne_zero' (m : ℕ) : (2 : MvRatFunc (Fin m) ℂ) ≠ 0 := by
  have hinj := IsFractionRing.injective (MvPolynomial (Fin m) ℂ) (MvRatFunc (Fin m) ℂ)
  have h : (MvPolynomial.C (2 : ℂ) : MvPolynomial (Fin m) ℂ) ≠ 0 := by
    rw [Ne, MvPolynomial.C_eq_zero]; norm_num
  have h' := (map_ne_zero_iff _ hinj).mpr h
  have e : (algebraMap (MvPolynomial (Fin m) ℂ) (MvRatFunc (Fin m) ℂ)) (MvPolynomial.C 2) = 2 := by
    rw [show (MvPolynomial.C (2 : ℂ) : MvPolynomial (Fin m) ℂ) = 2 from map_ofNat _ 2, map_ofNat]
  rwa [e] at h'

/-- Bass-Tate vanishing for `p = 2`: `K_{m+1}(C(x_1, ..., x_m))/2 = 0`. -/
theorem grade_succ_bot (m : ℕ) : grade (MvRatFunc (Fin m) ℂ) 2 (m + 1) = ⊥ := by
  rw [eq_bot_iff, MilnorK.grade, AddSubgroup.closure_le]
  rintro _ ⟨s, rfl⟩
  rw [SetLike.mem_coe, AddSubgroup.mem_bot, symbol_succ]
  have hS : symbol 2 (fun i ↦ s i.succ) = S (List.ofFn fun i ↦ s i.succ) := by
    simp [symbol, S, List.map_ofFn, Function.comp_def]
  rw [hS, (commute_S (sqrt_neg_one m) (s 0) _).eq]
  refine kill (sqrt_neg_one m) (two_ne_zero' m) (fun q ↦ OMA.Artin2.isotropic_gen ?_ q) _ (s 0)
  simp [Fintype.card_sum]

end OMA.PfK


theorem OMA.solution : OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1_H2_R1.H1 :=
  fun m _ ↦ (MilnorK.zero_mem_symbolLengthBounds_iff _ _).mpr (OMA.PfK.grade_succ_bot m)
