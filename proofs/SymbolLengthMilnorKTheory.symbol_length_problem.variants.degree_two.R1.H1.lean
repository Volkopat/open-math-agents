import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_R1

-- Step SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two.R1.H1:
-- every class of K_2(C(x_1, ..., x_m))/2 is a sum of 2^(m-1) - 1 symbols (Matzri at p = 2, t = 1).
-- Credit: @hyprspacecoyote
--
-- Proof.
-- (1) u(C(x_1, ..., x_m)) <= 2^m: over C, polynomials without constant term, fewer than the
--     variables, have a common nonzero zero (Krull's height theorem + Nullstellensatz); Lang's
--     box count over C[x_1, ..., x_m] then gives an isotropic vector for any diagonal form in more
--     than 2^m variables.
-- (2) Milnor's second Stiefel-Whitney class e<c_1, ..., c_N> = sum_{i<j} {c_i, c_j} in K_2/2 (with
--     -1 a square): every class is e of a list with square product (blocks [a, b, ab]); e is
--     invariant under swaps, square scaling, removing an equal pair, and the move
--     <c, d> -> <c x^2 + d y^2, c d (c x^2 + d y^2)> (Steinberg relation / two-term slot lemma).
-- (3) Merging along an isotropic vector removes two entries, so the list shrinks to length <= 2^m.
-- (4) A list of odd length 2k + 1 has e = sum of k symbols ({a, bP} + {b, P} = {aP, bP}); an even
--     list with square product reduces to its tail.
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

theorem sqrt_neg_one (m : ℕ) : ∃ i : MvRatFunc (Fin m) ℂ, i * i = -1 :=
  ⟨algebraMap (MvPolynomial (Fin m) ℂ) _ (MvPolynomial.C Complex.I), by
    rw [← map_mul, ← MvPolynomial.C_mul, Complex.I_mul_I, MvPolynomial.C_neg,
      MvPolynomial.C_1, map_neg, map_one]⟩

end OMA.PfK

namespace OMA.SW

open MilnorK

variable {F : Type*} [Field F]

/-- Milnor's second Stiefel-Whitney class of `<c_1, ..., c_N>`: `∑_{i<j} {c_i, c_j}` in `K_2/2`. -/
noncomputable def e : List Fˣ → MilnorK F 2
  | [] => 0
  | c :: L => of 2 c * of 2 L.prod + e L

@[simp] lemma e_nil : e ([] : List Fˣ) = 0 := rfl
@[simp] lemma e_cons (c : Fˣ) (L : List Fˣ) : e (c :: L) = of 2 c * of 2 L.prod + e L := rfl

lemma two_add (x : MilnorK F 2) : x + x = 0 := OMA.Artin2K.add_self_eq_zero x

lemma e_cons_congr (c : Fˣ) {L L' : List Fˣ} (he : e L = e L')
    (hp : of 2 L.prod = of 2 L'.prod) : e (c :: L) = e (c :: L') := by
  simp only [e_cons, hp, he]

lemma e_scale (c t : Fˣ) (L : List Fˣ) : e ((c * t ^ 2) :: L) = e (c :: L) := by
  simp only [e_cons, of_mul, OMA.Artin2K.of_sq, add_zero]


lemma e_swap (hi : ∃ i : F, i * i = -1) (a b : Fˣ) (L : List Fˣ) : e (a :: b :: L) = e (b :: a :: L) := by
  simp only [e_cons, List.prod_cons, of_mul, mul_add]
  rw [OMA.Artin2K.of_comm hi a b]; abel

lemma e_pair (hi : ∃ i : F, i * i = -1) (c : Fˣ) (L : List Fˣ) : e (c :: c :: L) = e L := by
  simp only [e_cons, List.prod_cons, of_mul, mul_add, OMA.Artin2K.of_mul_self hi, zero_add]
  rw [← add_assoc, two_add, zero_add]

/-- The move `<c, d> ≅ <c', c d c'>` for `c' = c x² + d y²`. -/
lemma e_move (hi : ∃ i : F, i * i = -1) (c d c' : Fˣ) (x y : F) (h : (c' : F) = c * x ^ 2 + d * y ^ 2) (L : List Fˣ) :
    e (c :: d :: L) = e (c' :: (c * d * c') :: L) := by
  have hs := OMA.Artin2K.slot2 hi c d c' x y h
  rw [of_mul, mul_add] at hs
  simp only [e_cons, List.prod_cons, of_mul, mul_add, add_mul, OMA.Artin2K.of_mul_self hi]
  have h2 : of 2 c' * of 2 L.prod + of 2 c' * of 2 L.prod = 0 := two_add _
  calc of 2 c * of 2 d + of 2 c * of 2 L.prod + (of 2 d * of 2 L.prod + e L)
      = (of 2 c' * of 2 c + of 2 c' * of 2 d) + 0 + 0 + of 2 c * of 2 L.prod +
          of 2 d * of 2 L.prod + e L := by rw [← hs]; abel
    _ = of 2 c' * of 2 c + of 2 c' * of 2 d + 0 +
          (of 2 c' * of 2 L.prod + of 2 c' * of 2 L.prod) + of 2 c * of 2 L.prod +
          of 2 d * of 2 L.prod + e L := by rw [h2]
    _ = _ := by abel

lemma e_append (L₁ L₂ : List Fˣ) :
    e (L₁ ++ L₂) = e L₁ + e L₂ + of 2 L₁.prod * of 2 L₂.prod := by
  induction L₁ with
  | nil => simp
  | cons c L ih =>
    simp only [List.cons_append, e_cons, List.prod_append, List.prod_cons, of_mul, mul_add, ih,
      add_mul]
    abel

/-- Representation: if `s = ∑ c_i x_i² ≠ 0` then `<c> ≅ <s> ⊥ <R>` (on the level of `e`). -/
theorem rep (hi : ∃ i : F, i * i = -1) : ∀ (n : ℕ) (c : Fin n → Fˣ) (x : Fin n → F) (hs : ∑ i, (c i : F) * x i ^ 2 ≠ 0),
    ∃ R : List Fˣ, R.length + 1 = n ∧ e (Units.mk0 _ hs :: R) = e (List.ofFn c) ∧
      of 2 (Units.mk0 _ hs :: R).prod = of 2 (List.ofFn c).prod := by
  intro n
  induction n with
  | zero => intro c x hs; simp at hs
  | succ n ih =>
    intro c x hs
    rw [List.ofFn_succ]
    have hsum : ∑ i, (c i : F) * x i ^ 2 =
        c 0 * x 0 ^ 2 + ∑ i : Fin n, (c i.succ : F) * x i.succ ^ 2 := Fin.sum_univ_succ _
    by_cases hx0 : x 0 = 0
    · have hs' : ∑ i : Fin n, (c i.succ : F) * x i.succ ^ 2 ≠ 0 := by
        rw [hsum, hx0] at hs; simpa using hs
      obtain ⟨R, hR, he, hp⟩ := ih (fun i ↦ c i.succ) (fun i ↦ x i.succ) hs'
      have heq : Units.mk0 _ hs = Units.mk0 _ hs' := by ext; simp [hsum, hx0]
      refine ⟨c 0 :: R, by simp [hR], ?_, ?_⟩
      · rw [heq, e_swap hi]
        exact e_cons_congr (c 0) he (by simpa using hp)
      · rw [heq]
        simp only [List.prod_cons, of_mul] at hp ⊢
        rw [← hp]; abel
    by_cases hr : ∑ i : Fin n, (c i.succ : F) * x i.succ ^ 2 = 0
    · have heq : Units.mk0 _ hs = c 0 * (Units.mk0 (x 0) hx0) ^ 2 := by
        ext; simp [hsum, hr]
      refine ⟨List.ofFn (fun i ↦ c i.succ), by simp, ?_, ?_⟩
      · rw [heq, e_scale]
      · rw [heq]; simp only [List.prod_cons, of_mul, OMA.Artin2K.of_sq, add_zero]
    · obtain ⟨R, hR, he, hp⟩ := ih (fun i ↦ c i.succ) (fun i ↦ x i.succ) hr
      set s' := Units.mk0 _ hr
      have hmove := e_move hi (c 0) s' (Units.mk0 _ hs) (x 0) 1 (by simp [s', hsum]) R
      refine ⟨(c 0 * s' * Units.mk0 _ hs) :: R, by simp [hR], ?_, ?_⟩
      · rw [← hmove]
        exact e_cons_congr (c 0) he hp
      · simp only [List.prod_cons, of_mul] at hp ⊢
        rw [← hp]
        have h2 := two_add (of 2 (Units.mk0 _ hs))
        calc of 2 (Units.mk0 _ hs) + (of 2 (c 0) + of 2 s' + of 2 (Units.mk0 _ hs) + of 2 R.prod)
            = (of 2 (Units.mk0 _ hs) + of 2 (Units.mk0 _ hs)) + of 2 (c 0) +
                (of 2 s' + of 2 R.prod) := by abel
          _ = _ := by rw [h2, zero_add]

/-- An isotropic diagonal form loses a hyperbolic plane (on the level of `e`). -/
theorem red (hi : ∃ i : F, i * i = -1) : ∀ (n : ℕ) (c : Fin n → Fˣ) (x : Fin n → F), x ≠ 0 →
    ∑ i, (c i : F) * x i ^ 2 = 0 →
    ∃ R : List Fˣ, R.length + 2 = n ∧ e R = e (List.ofFn c) ∧
      of 2 R.prod = of 2 (List.ofFn c).prod := by
  intro n
  induction n with
  | zero => intro c x hx _; exact absurd (funext fun i ↦ i.elim0) hx
  | succ n ih =>
    intro c x hx hsum0
    rw [List.ofFn_succ]
    have hsum : ∑ i, (c i : F) * x i ^ 2 =
        c 0 * x 0 ^ 2 + ∑ i : Fin n, (c i.succ : F) * x i.succ ^ 2 := Fin.sum_univ_succ _
    by_cases hx0 : x 0 = 0
    · have hx' : (fun i : Fin n ↦ x i.succ) ≠ 0 := by
        intro h; apply hx; funext i
        refine Fin.cases hx0 (fun j ↦ ?_) i
        exact congrFun h j
      have hs' : ∑ i : Fin n, (c i.succ : F) * x i.succ ^ 2 = 0 := by
        rw [hsum, hx0] at hsum0; simpa using hsum0
      obtain ⟨R, hR, he, hp⟩ := ih (fun i ↦ c i.succ) (fun i ↦ x i.succ) hx' hs'
      refine ⟨c 0 :: R, by simp; omega, ?_, ?_⟩
      · exact e_cons_congr (c 0) he hp
      · simp only [List.prod_cons, of_mul, hp]
    · have hr : ∑ i : Fin n, (c i.succ : F) * x i.succ ^ 2 ≠ 0 := by
        intro h0
        rw [hsum, h0, add_zero] at hsum0
        exact (mul_ne_zero (c 0).ne_zero (pow_ne_zero 2 hx0)) hsum0
      obtain ⟨R, hR, he, hp⟩ := rep hi n (fun i ↦ c i.succ) (fun i ↦ x i.succ) hr
      obtain ⟨i, hi'⟩ := hi
      have hi0 : i ≠ 0 := by rintro rfl; simp at hi'
      have hs'eq : Units.mk0 _ hr = c 0 * (Units.mk0 (i * x 0) (mul_ne_zero hi0 hx0)) ^ 2 := by
        ext
        simp only [Units.val_mk0, Units.val_mul, Units.val_pow_eq_pow_val]
        linear_combination hsum0 - hsum - (c 0 : F) * x 0 ^ 2 * hi'
      refine ⟨R, by omega, ?_, ?_⟩
      · have h1 := e_cons_congr (c 0) he hp
        rw [hs'eq, e_swap ⟨i, hi'⟩, e_scale, e_pair ⟨i, hi'⟩] at h1
        exact h1
      · simp only [List.prod_cons, of_mul] at hp ⊢
        rw [← hp, hs'eq, of_mul, OMA.Artin2K.of_sq, add_zero, ← add_assoc, two_add, zero_add]



/-- Shrink any list to length `≤ 2^m` when forms of dimension `> 2^m` are isotropic. -/
theorem reduce_all (hi : ∃ i : F, i * i = -1) {m : ℕ} (hu : ∀ (ι : Type) [Fintype ι], 2 ^ m < Fintype.card ι →
      ∀ q : ι → F, ∃ v : ι → F, v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0) :
    ∀ (N : ℕ) (L : List Fˣ), L.length = N → ∃ L' : List Fˣ, L'.length ≤ 2 ^ m ∧
      L'.length % 2 = L.length % 2 ∧ e L' = e L ∧ of 2 L'.prod = of 2 L.prod := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro L hL
    by_cases hN : L.length ≤ 2 ^ m
    · exact ⟨L, hN, rfl, rfl, rfl⟩
    obtain ⟨x, hx0, hx⟩ := hu (Fin L.length) (by simp; omega) (fun i ↦ (L.get i : F))
    obtain ⟨R, hR, he, hp⟩ := red hi L.length L.get x hx0 hx
    rw [List.ofFn_get] at he hp
    obtain ⟨L', h1, h2, h3, h4⟩ := ih R.length (by omega) R rfl
    exact ⟨L', h1, by rw [h2]; omega, h3.trans he, h4.trans hp⟩

/-- `{a, bP} + {b, P} = {aP, bP}`. -/
lemma pair_identity (hi : ∃ i : F, i * i = -1) (a b P : Fˣ) :
    of 2 a * of 2 (b * P) + of 2 b * of 2 P = of 2 (a * P) * of 2 (b * P) := by
  simp only [of_mul, mul_add, add_mul, OMA.Artin2K.of_mul_self hi, add_zero]
  rw [OMA.Artin2K.of_comm hi P b]
  abel

/-- A list of odd length `2k + 1` has `e` equal to a sum of `k` symbols. -/
theorem odd_count (hi : ∃ i : F, i * i = -1) : ∀ (k : ℕ) (L : List Fˣ), L.length = 2 * k + 1 →
    ∃ s : Fin k → Fin 2 → Fˣ, e L = ∑ t, symbol 2 (s t) := by
  intro k
  induction k with
  | zero =>
    intro L hL
    match L, hL with
    | [c], _ => exact ⟨Fin.elim0, by simp⟩
  | succ k ih =>
    intro L hL
    match L, hL with
    | a :: b :: L'', hL =>
      obtain ⟨s, hs⟩ := ih L'' (by simp at hL; omega)
      refine ⟨Fin.cons ![a * L''.prod, b * L''.prod] s, ?_⟩
      rw [Fin.sum_univ_succ, Fin.cons_zero]
      simp only [e_cons, List.prod_cons, Fin.cons_succ, ← hs]
      rw [← add_assoc, pair_identity hi a b L''.prod, symbol_pair]

theorem count' (hi : ∃ i : F, i * i = -1) (L : List Fˣ) (hp : of 2 L.prod = 0) :
    ∃ j, 2 * j + 1 ≤ max L.length 1 ∧ ∃ s : Fin j → Fin 2 → Fˣ, e L = ∑ t, symbol 2 (s t) := by
  rcases Nat.even_or_odd L.length with ⟨r, hr⟩ | ⟨k, hk⟩
  · cases L with
    | nil => exact ⟨0, by simp, Fin.elim0, by simp⟩
    | cons c L' =>
      have hc : of 2 c = of 2 L'.prod := by
        simp only [List.prod_cons, of_mul] at hp
        rw [← OMA.Artin2K.neg_eq_self (of 2 L'.prod)]
        exact eq_neg_of_add_eq_zero_left hp
      obtain ⟨k, hk⟩ : ∃ k, L'.length = 2 * k + 1 := ⟨r - 1, by simp at hr; omega⟩
      obtain ⟨s, hs⟩ := odd_count hi k L' hk
      refine ⟨k, by simp; omega, s, ?_⟩
      rw [e_cons, hc, OMA.Artin2K.of_mul_self hi, zero_add, hs]
  · obtain ⟨s, hs⟩ := odd_count hi k L hk
    exact ⟨k, by omega, s, hs⟩

/-- Every class of `K_2/2` is `e` of a list whose product is a square. -/
theorem grade_eq_e (hi : ∃ i : F, i * i = -1) (x : MilnorK F 2) (hx : x ∈ grade F 2 2) :
    ∃ L : List Fˣ, e L = x ∧ of 2 L.prod = 0 := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    have hsym : symbol 2 s = of 2 (s 0) * of 2 (s 1) := by simp [symbol_succ]
    refine ⟨[s 0, s 1, s 0 * s 1], ?_, ?_⟩
    · rw [hsym]
      simp only [e_cons, e_nil, List.prod_cons, List.prod_nil, mul_one, of_one, mul_zero,
        add_zero, of_mul, mul_add, OMA.Artin2K.of_mul_self hi, zero_add]
      rw [OMA.Artin2K.of_comm hi (s 1) (s 0)]
      calc _ = (of 2 (s 0) * of 2 (s 1) + of 2 (s 0) * of 2 (s 1)) + of 2 (s 0) * of 2 (s 1) := by
            abel
        _ = _ := by rw [two_add, zero_add]
    · simp only [List.prod_cons, List.prod_nil, mul_one, of_mul]
      calc _ = (of 2 (s 0) + of 2 (s 0)) + (of 2 (s 1) + of 2 (s 1)) := by abel
        _ = 0 := by rw [two_add, two_add, add_zero]
  | zero => exact ⟨[], rfl, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨L₁, rfl, h₁⟩ := hy
    obtain ⟨L₂, rfl, h₂⟩ := hz
    refine ⟨L₁ ++ L₂, ?_, ?_⟩
    · rw [e_append, h₁, zero_mul, add_zero]
    · rw [List.prod_append, of_mul, h₁, h₂, add_zero]
  | neg y _ hy =>
    obtain ⟨L, rfl, h⟩ := hy
    exact ⟨L, OMA.Artin2K.neg_eq_self _ |>.symm, h⟩

/-- Matzri's bound at `p = 2` from the `u`-invariant: every class of `K_2/2` is a sum of
`2^(m-1) - 1` symbols when forms of dimension `> 2^m` are isotropic. -/
theorem matzri_two (hi : ∃ i : F, i * i = -1) {m : ℕ} (hm : 1 ≤ m)
    (hu : ∀ (ι : Type) [Fintype ι], 2 ^ m < Fintype.card ι →
      ∀ q : ι → F, ∃ v : ι → F, v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0) :
    2 ^ (m - 1) - 1 ∈ symbolLengthBounds F 2 2 := by
  intro x hx
  obtain ⟨L, rfl, hp⟩ := grade_eq_e hi x hx
  obtain ⟨L', hlen, -, he, hp'⟩ := reduce_all hi hu L.length L rfl
  obtain ⟨j, hj, s, hs⟩ := count' hi L' (hp'.trans hp)
  refine ⟨j, ?_, s, he.symm.trans hs⟩
  have h2 : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
  rcases Nat.lt_or_ge L'.length 1 with h | h
  · simp [Nat.lt_one_iff.mp h] at hj; omega
  · rw [max_eq_left h] at hj; omega

end OMA.SW

namespace OMA.SW

open MilnorK

/-- Matzri's bound at `p = 2` for `C(x_1, ..., x_m)`. -/
theorem matzri_two_C (m : ℕ) (hm : 1 ≤ m) :
    2 ^ (m - 1) - 1 ∈ symbolLengthBounds (MvRatFunc (Fin m) ℂ) 2 2 :=
  matzri_two (OMA.PfK.sqrt_neg_one m) hm (fun ι _ hι q ↦ OMA.Artin2.isotropic_gen hι q)

end OMA.SW


theorem OMA.solution : OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_R1.H1 :=
  fun m hm ↦ OMA.SW.matzri_two_C m hm
