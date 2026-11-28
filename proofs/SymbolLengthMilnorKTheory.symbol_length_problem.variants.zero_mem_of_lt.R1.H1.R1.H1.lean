import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1_H1_R1

/-!
Step H1 of reduction SymbolLengthMilnorKTheory.symbol_length_problem.variants.zero_mem_of_lt.R1.H1.R1:
every finite extension AdjoinRoot pi of C(x) = MvRatFunc (Fin 1) C is C_1 (a homogeneous form of
degree d >= 1 in more than d variables has a nontrivial zero).

Proof.
(A) Tsen-Lang for C(x_1, ..., x_m) (Lang's box count), copied below: forms of degree d in more than
    d ^ m variables over MvRatFunc (Fin m) C have a nontrivial zero; m = 1 gives C_1 for C(x).
(B) Lang's norm-form argument. Let E / F be a field extension with an F-basis b_1, ..., b_r and Phi a
    form of degree d over E in N > d variables. Substitute v_j = sum_i x_(i, j) b_i with r N new
    variables over F. Applying the F-linear functionals e |-> (leftMulMatrix b e)_(i, k) to the
    coefficients of Phi(v) gives an r x r matrix M of degree-d forms over F with
    eval x M = leftMulMatrix b (Phi(v x)), so det M is a form of degree r d in r N > r d variables
    whose value at x is the norm of Phi(v x). C_1 for F gives x /= 0 with norm Phi(v x) = 0, so
    Phi(v x) = 0 in the field E, and v x /= 0 because b is a basis.
-/

namespace OMA.LangC1

namespace TsenLang

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

/-- Lang's count over `C[x_1, ..., x_m]` for a form of degree `d` given by the coefficients
`p s` on the monomials `s ∈ T`, for a box of side `S`. -/
theorem lang_hom {m N : ℕ} (d r S : ℕ) (hd : 0 < d) (hS : 0 < S)
    (T : Finset (Fin N →₀ ℕ)) (p : (Fin N →₀ ℕ) → MvPolynomial (Fin m) ℂ)
    (hT : ∀ s ∈ T, ∑ i, s i = d) (hr : ∀ s ∈ T, ∀ n, degreeOf n (p s) ≤ r)
    (hcnt : (r + d * S) ^ m < N * S ^ m) :
    ∃ W : Fin N → MvPolynomial (Fin m) ℂ, W ≠ 0 ∧ ∑ s ∈ T, p s * ∏ i, W i ^ s i = 0 := by
  classical
  set E := r + d * S with hE
  let U := Fin N × (Fin m → Fin S)
  let V : Fin N → MvPolynomial (Fin m) (MvPolynomial U ℂ) := fun j ↦
    ∑ e : Fin m → Fin S, monomial (expo fun i ↦ (e i : ℕ)) (X (j, e))
  let Q : MvPolynomial (Fin m) (MvPolynomial U ℂ) := ∑ s ∈ T, map C (p s) * ∏ i, V i ^ s i
  let eqs : Finset (MvPolynomial U ℂ) :=
    (Finset.univ : Finset (Fin m → Fin E)).image fun e ↦ coeff (expo fun i ↦ (e i : ℕ)) Q
  have hV : ∀ j n, degreeOf n (V j) ≤ S - 1 := by
    intro j n
    rw [degreeOf_le_iff]
    intro c hc
    obtain ⟨e, -, he⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hc)
    have := support_monomial_subset he
    rw [Finset.mem_singleton] at this
    subst this
    have := (e n).isLt
    simp only [expo_apply]
    omega
  have hQ : ∀ n, degreeOf n Q ≤ r + d * (S - 1) := by
    intro n
    refine (degreeOf_sum_le n _ _).trans (Finset.sup_le fun s hs ↦ ?_)
    refine (degreeOf_mul_le n _ _).trans
      (add_le_add ((degreeOf_map_le'' C n _).trans (hr s hs n)) ?_)
    refine (degreeOf_prod_le n _ _).trans ?_
    calc ∑ i, degreeOf n (V i ^ s i) ≤ ∑ i, s i * (S - 1) :=
          Finset.sum_le_sum fun i _ ↦
            (degreeOf_pow_le n _ _).trans (Nat.mul_le_mul_left _ (hV i n))
      _ = d * (S - 1) := by rw [← Finset.sum_mul, hT s hs]
  have hcoeff : ∀ c : Fin m →₀ ℕ, (∃ n, E ≤ c n) → coeff c Q = 0 := by
    rintro c ⟨n, hn⟩
    by_contra hc
    have := (monomial_le_degreeOf n (mem_support_iff.mpr hc)).trans (hQ n)
    have h1 : d * (S - 1) = d * S - d := Nat.mul_sub_one d S
    have h2 : d ≤ d * S := Nat.le_mul_of_pos_right d hS
    omega
  have hmap0 : map (constantCoeff : MvPolynomial U ℂ →+* ℂ) Q = 0 := by
    have hV0 : ∀ j, map (constantCoeff : MvPolynomial U ℂ →+* ℂ) (V j) = 0 := by
      intro j
      simp [V, map_sum, map_monomial]
    simp only [Q, map_sum, map_mul, map_prod, map_pow, hV0]
    refine Finset.sum_eq_zero fun s hs ↦ ?_
    have hs0 : s ≠ 0 := by
      rintro rfl
      have := hT 0 hs
      simp at this
      omega
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hs0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (zero_pow hi), mul_zero]
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
  let W : Fin N → MvPolynomial (Fin m) ℂ := fun j ↦ map (eval t) (V j)
  have hmapQ : map (eval t) Q = ∑ s ∈ T, p s * ∏ i, W i ^ s i := by
    have hc : (eval t).comp (C : ℂ →+* MvPolynomial U ℂ) = RingHom.id ℂ := by
      ext; simp
    simp only [Q, W, map_sum, map_mul, map_prod, map_pow, map_map, hc, map_id]
  have hQ0 : map (eval t) Q = 0 := by
    ext c
    rw [coeff_map, coeff_zero]
    by_cases hc : ∀ n, c n < E
    · apply ht
      refine Finset.mem_image.mpr ⟨fun n ↦ ⟨c n, hc n⟩, Finset.mem_univ _, ?_⟩
      congr 1
      ext n
      simp
    · push Not at hc
      rw [hcoeff c hc, map_zero]
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

/-- A box side that makes Lang's count work when there are more than `d ^ m` variables. -/
theorem exists_side (m d r N : ℕ) (hN : d ^ m < N) :
    ∃ S, 0 < S ∧ (r + d * S) ^ m < N * S ^ m := by
  have hlim : Filter.Tendsto (fun S : ℕ ↦ ((r : ℝ) / S + d) ^ m) Filter.atTop
      (nhds ((0 + (d : ℝ)) ^ m)) :=
    ((tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)).add_const (d : ℝ)).pow m
  have hlt : ((0 : ℝ) + d) ^ m < N := by
    rw [zero_add]; exact_mod_cast hN
  obtain ⟨S, hS1, hS⟩ :=
    ((Filter.eventually_ge_atTop 1).and (hlim.eventually (gt_mem_nhds hlt))).exists
  refine ⟨S, hS1, ?_⟩
  have hSpos : (0 : ℝ) < S := by exact_mod_cast hS1
  have h1 : ((r + d * S : ℕ) : ℝ) ^ m < N * (S : ℝ) ^ m := by
    have : ((r : ℝ) / S + d) ^ m * (S : ℝ) ^ m = ((r + d * S : ℕ) : ℝ) ^ m := by
      rw [← mul_pow]; congr 1; push_cast
      rw [add_mul, div_mul_cancel₀ _ hSpos.ne']
    rw [← this]
    exact mul_lt_mul_of_pos_right hS (pow_pos hSpos m)
  exact_mod_cast h1

/-- Tsen-Lang: `C(x_1, ..., x_m)` is `C_m`. -/
theorem tsen_lang : ∀ m d N : ℕ, ∀ Φ : MvPolynomial (Fin N) (MvRatFunc (Fin m) ℂ),
    0 < d → Φ.IsHomogeneous d → d ^ m < N →
    ∃ v : Fin N → MvRatFunc (Fin m) ℂ, v ≠ 0 ∧ MvPolynomial.eval v Φ = 0 := by
  intro m d N Φ hd hΦ hN
  classical
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin m) ℂ) (MvRatFunc (Fin m) ℂ)) :=
    IsFractionRing.injective _ _
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (nonZeroDivisors (MvPolynomial (Fin m) ℂ)) (Φ.support.image Φ.coeff)
  have hint : ∀ s : Fin N →₀ ℕ, ∃ q : MvPolynomial (Fin m) ℂ,
      algebraMap _ (MvRatFunc (Fin m) ℂ) q = (b : MvPolynomial (Fin m) ℂ) • coeff s Φ := by
    intro s
    by_cases hs : s ∈ Φ.support
    · exact hb _ (Finset.mem_image_of_mem _ hs)
    · refine ⟨0, ?_⟩
      rw [notMem_support_iff.mp hs]
      simp
  choose p hp using hint
  set r := ∑ s ∈ Φ.support, ∑ n, degreeOf n (p s)
  have hr : ∀ s ∈ Φ.support, ∀ n, degreeOf n (p s) ≤ r := by
    intro s hs n
    exact (Finset.single_le_sum (f := fun n ↦ degreeOf n (p s)) (fun _ _ ↦ Nat.zero_le _)
      (Finset.mem_univ n)).trans (Finset.single_le_sum (f := fun s ↦ ∑ n, degreeOf n (p s))
        (fun _ _ ↦ Nat.zero_le _) hs)
  have hT : ∀ s ∈ Φ.support, ∑ i, s i = d := by
    intro s hs
    rw [hΦ.degree_eq_sum_deg_support hs]
    refine (Finset.sum_subset (Finset.subset_univ _) fun i _ hi ↦ ?_).symm
    simpa using hi
  obtain ⟨S, hS, hcnt⟩ := exists_side m d r N hN
  obtain ⟨W, hW0, hW⟩ := lang_hom d r S hd hS Φ.support p hT hr hcnt
  have hb0 : algebraMap _ (MvRatFunc (Fin m) ℂ) (b : MvPolynomial (Fin m) ℂ) ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.coe_ne_zero b)
  refine ⟨fun j ↦ algebraMap _ (MvRatFunc (Fin m) ℂ) (W j), ?_, ?_⟩
  · intro h
    apply hW0
    funext j
    have := congrFun h j
    simp only [Pi.zero_apply] at this ⊢
    exact (map_eq_zero_iff _ hinj).mp this
  · have := congrArg (algebraMap _ (MvRatFunc (Fin m) ℂ)) hW
    simp only [map_sum, map_mul, map_prod, map_pow, map_zero, hp, Algebra.smul_def,
      mul_assoc, ← Finset.mul_sum] at this
    rw [eval_eq']
    exact (mul_eq_zero.mp this).resolve_left hb0

end TsenLang

open MvPolynomial

section Lang

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- Apply an `F`-linear functional `E → F` to every coefficient of a polynomial over `E`. -/
noncomputable def cmap {σ : Type*} (ℓ : E →ₗ[F] F) (P : MvPolynomial σ E) : MvPolynomial σ F :=
  ∑ m ∈ P.support, monomial m (ℓ (coeff m P))

theorem coeff_cmap {σ : Type*} (ℓ : E →ₗ[F] F) (P : MvPolynomial σ E) (m : σ →₀ ℕ) :
    coeff m (cmap ℓ P) = ℓ (coeff m P) := by
  classical
  simp only [cmap, coeff_sum, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, map_zero]

theorem cmap_isHomogeneous {σ : Type*} (ℓ : E →ₗ[F] F) {P : MvPolynomial σ E} {n : ℕ}
    (hP : P.IsHomogeneous n) : (cmap ℓ P).IsHomogeneous n := by
  intro m hm
  rw [coeff_cmap] at hm
  exact hP fun h ↦ hm (by rw [h, map_zero])

theorem eval_cmap {σ : Type*} (ℓ : E →ₗ[F] F) (P : MvPolynomial σ E) (x : σ → F) :
    eval x (cmap ℓ P) = ℓ (eval (fun i ↦ algebraMap F E (x i)) P) := by
  conv_rhs => rw [P.as_sum]
  simp only [cmap, map_sum, eval_monomial]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  have h : (m.prod fun n e ↦ (algebraMap F E (x n)) ^ e) =
      algebraMap F E (m.prod fun n e ↦ x n ^ e) := by
    rw [map_finsuppProd]
    simp only [map_pow]
  rw [h, ← Algebra.commutes, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The entry `(i, k)` of the matrix of left multiplication, as a linear functional. -/
noncomputable def entry (b : Module.Basis ι F E) (i k : ι) : E →ₗ[F] F :=
  b.coord i ∘ₗ LinearMap.mulRight F (b k)

theorem entry_apply (b : Module.Basis ι F E) (i k : ι) (e : E) :
    entry b i k e = Algebra.leftMulMatrix b e i k := by
  simp [entry, Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply, Module.Basis.coord_apply]

/-- `C_1` for `F`, transported to any finite type of variables. -/
theorem c1_fintype
    (hF : ∀ (n d : ℕ) (Ψ : MvPolynomial (Fin n) F), 0 < d → Ψ.IsHomogeneous d → d < n →
      ∃ x : Fin n → F, x ≠ 0 ∧ eval x Ψ = 0)
    {σ : Type*} [Fintype σ] (d : ℕ) (Ψ : MvPolynomial σ F) (hd : 0 < d)
    (hΨ : Ψ.IsHomogeneous d) (hn : d < Fintype.card σ) :
    ∃ x : σ → F, x ≠ 0 ∧ eval x Ψ = 0 := by
  set e := Fintype.equivFin σ
  obtain ⟨w, hw0, hw⟩ := hF _ d (rename e Ψ) hd hΨ.rename_isHomogeneous hn
  refine ⟨w ∘ e, ?_, ?_⟩
  · intro h; apply hw0; funext j
    have := congrFun h (e.symm j); simpa using this
  · rwa [eval_rename] at hw

/-- Lang: a finite extension (with a basis) of a `C_1` field is `C_1`. -/
theorem lang_step (b : Module.Basis ι F E)
    (hF : ∀ (n d : ℕ) (Ψ : MvPolynomial (Fin n) F), 0 < d → Ψ.IsHomogeneous d → d < n →
      ∃ x : Fin n → F, x ≠ 0 ∧ eval x Ψ = 0)
    (d N : ℕ) (Φ : MvPolynomial (Fin N) E) (hd : 0 < d) (hΦ : Φ.IsHomogeneous d) (hN : d < N) :
    ∃ v : Fin N → E, v ≠ 0 ∧ eval v Φ = 0 := by
  have := Module.Finite.of_basis b
  have := Module.Free.of_basis b
  have : Nonempty ι := b.index_nonempty
  let V : Fin N → MvPolynomial (ι × Fin N) E := fun j ↦ ∑ i, C (b i) * X (i, j)
  let Ψ : MvPolynomial (ι × Fin N) E := bind₁ V Φ
  have hV : ∀ j, (V j).IsHomogeneous 1 := by
    intro j
    apply IsHomogeneous.sum
    intro i _
    simpa using (isHomogeneous_C _ (b i)).mul (isHomogeneous_X E (i, j))
  have hΨ : Ψ.IsHomogeneous d := by
    have := hΦ.eval₂ (C : E →+* MvPolynomial (ι × Fin N) E) V (fun r ↦ isHomogeneous_C _ r) hV
    rw [one_mul] at this
    exact this
  let M : Matrix ι ι (MvPolynomial (ι × Fin N) F) := Matrix.of fun i k ↦ cmap (entry b i k) Ψ
  have hM : M.det.IsHomogeneous (Fintype.card ι * d) := by
    rw [Matrix.det_apply']
    apply IsHomogeneous.sum
    intro τ _
    have h0 : IsHomogeneous
        ((((Equiv.Perm.sign τ : ℤˣ) : ℤ) : MvPolynomial (ι × Fin N) F)) 0 := by
      rw [← map_intCast (C : F →+* MvPolynomial (ι × Fin N) F)]
      exact isHomogeneous_C _ _
    have h1 := IsHomogeneous.prod (s := Finset.univ)
      (φ := fun i : ι ↦ M (τ i) i) (n := fun _ ↦ d) (fun i _ ↦ cmap_isHomogeneous _ hΨ)
    simpa using h0.mul h1
  let v : (ι × Fin N → F) → Fin N → E := fun x j ↦ ∑ i, x (i, j) • b i
  have hev : ∀ x : ι × Fin N → F, eval x M.det = Algebra.norm F (eval (v x) Φ) := by
    intro x
    have hw : eval (fun u ↦ algebraMap F E (x u)) Ψ = eval (v x) Φ := by
      have h1 : eval (fun u ↦ algebraMap F E (x u)) Ψ =
          eval (fun j ↦ eval (fun u ↦ algebraMap F E (x u)) (V j)) Φ :=
        eval₂Hom_bind₁ (RingHom.id E) _ V Φ
      rw [h1]
      refine congrArg (fun g ↦ eval g Φ) (funext fun j ↦ ?_)
      simp only [V, v, map_sum, map_mul, eval_C, eval_X, Algebra.smul_def, mul_comm]
    rw [RingHom.map_det, Algebra.norm_eq_matrix_det b, ← hw]
    congr 1
    ext i k
    simp only [M, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, eval_cmap,
      entry_apply]
  obtain ⟨x, hx0, hx⟩ := c1_fintype hF (Fintype.card ι * d) M.det
    (Nat.mul_pos Fintype.card_pos hd) hM (by
      rw [Fintype.card_prod, Fintype.card_fin]
      exact Nat.mul_lt_mul_of_pos_left hN Fintype.card_pos)
  rw [hev, Algebra.norm_eq_zero_iff] at hx
  refine ⟨v x, ?_, hx⟩
  intro hv
  apply hx0
  funext ⟨i, j⟩
  have hli := Fintype.linearIndependent_iff.mp b.linearIndependent (fun i ↦ x (i, j))
    (congrFun hv j) i
  simpa using hli

end Lang

theorem adjoinRoot_c1 (π : Polynomial (MvRatFunc (Fin 1) ℂ)) [Fact (Irreducible π)] (d N : ℕ)
    (Φ : MvPolynomial (Fin N) (AdjoinRoot π)) (hd : 0 < d) (hΦ : Φ.IsHomogeneous d) (hN : d < N) :
    ∃ v : Fin N → AdjoinRoot π, v ≠ 0 ∧ MvPolynomial.eval v Φ = 0 := by
  have hπ : π ≠ 0 := (Fact.out : Irreducible π).ne_zero
  exact lang_step (AdjoinRoot.powerBasis hπ).basis
    (fun n d Ψ hd hΨ hn ↦ TsenLang.tsen_lang 1 d n Ψ hd hΨ (by simpa using hn)) d N Φ hd hΦ hN

end OMA.LangC1

theorem OMA.solution : OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_zero_mem_of_lt_R1_H1_R1.H1 := by
  intro π _ d N Φ hd hΦ hN
  exact OMA.LangC1.adjoinRoot_c1 π d N Φ hd hΦ hN
