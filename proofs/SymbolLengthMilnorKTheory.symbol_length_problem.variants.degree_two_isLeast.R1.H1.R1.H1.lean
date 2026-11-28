import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1

-- Step SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two_isLeast.R1.H1.R1.H1:
-- every class of K_2(C(x, y))/2 is a single symbol (Artin's theorem for p = 2).
-- Credit: @hyprspacecoyote
--
-- Proof.
-- (1) Over an algebraically closed field, R polynomials without constant term in N > R variables
--     have a common nonzero zero: otherwise the ideal (X_0, ..., X_{N-1}), which has height >= N
--     (explicit chain of primes), would be a minimal prime of an ideal with R generators, against
--     Krull's height theorem (via the Nullstellensatz).
-- (2) Lang's count: a diagonal quadratic form in 5 variables over C[x, y] has a nonzero zero:
--     substituting polynomials of bidegree < S = 5r + 5 gives 5 S^2 unknowns and at most
--     (11r + 9)^2 coefficient equations. Clearing denominators, every 5-dimensional diagonal
--     form over C(x, y) is isotropic.
-- (3) In K_2/2, with -1 a square: {a, b} = {b, a}, {a, a} = 0, and {a, b} = {e, a b} whenever
--     e = a x^2 + b y^2 (Steinberg relation for a x^2/e + b y^2/e = 1). From an isotropic vector
--     of <a, b, ab, c, d> one gets a common slot e, so {a, b} + {c, d} is a single symbol.
-- (4) By induction over the generating set, every class of K_2/2 is a single symbol.
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



/-- `C(x, y)` has `u`-invariant at most `4`: every diagonal quadratic form in `5` variables is
isotropic. -/
theorem isotropic5 (q : Fin 5 → (MvRatFunc (Fin 2) ℂ)) : ∃ v : Fin 5 → (MvRatFunc (Fin 2) ℂ), v ≠ 0 ∧ ∑ i, q i * v i ^ 2 = 0 := by
  classical
  have hex : ∀ i, ∃ nd : MvPolynomial (Fin 2) ℂ × MvPolynomial (Fin 2) ℂ, nd.2 ≠ 0 ∧
      q i = algebraMap _ (MvRatFunc (Fin 2) ℂ) nd.1 / algebraMap _ (MvRatFunc (Fin 2) ℂ) nd.2 := by
    intro i
    obtain ⟨n, d, hd, h⟩ := IsFractionRing.div_surjective (MvPolynomial (Fin 2) ℂ) (q i)
    exact ⟨(n, d), nonZeroDivisors.ne_zero hd, h.symm⟩
  choose nd hd hq using hex
  have hinj : Function.Injective (algebraMap (MvPolynomial (Fin 2) ℂ) (MvRatFunc (Fin 2) ℂ)) :=
    IsFractionRing.injective _ _
  let P : Fin 5 → MvPolynomial (Fin 2) ℂ := fun i ↦
    (nd i).1 * ∏ j ∈ Finset.univ.erase i, (nd j).2
  obtain ⟨W, hW0, hW⟩ := lang_poly P
  set Dn := ∏ j, (nd j).2
  have hDn : algebraMap _ (MvRatFunc (Fin 2) ℂ) Dn ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr (Finset.prod_ne_zero_iff.mpr fun j _ ↦ hd j)
  have hP : ∀ i, algebraMap _ (MvRatFunc (Fin 2) ℂ) (P i) = q i * algebraMap _ (MvRatFunc (Fin 2) ℂ) Dn := by
    intro i
    have hdi : algebraMap _ (MvRatFunc (Fin 2) ℂ) (nd i).2 ≠ 0 := (map_ne_zero_iff _ hinj).mpr (hd i)
    simp only [P, Dn, map_mul, map_prod, hq i]
    rw [← Finset.mul_prod_erase Finset.univ (fun j ↦ algebraMap _ (MvRatFunc (Fin 2) ℂ) (nd j).2)
      (Finset.mem_univ i)]
    field_simp
  refine ⟨fun i ↦ algebraMap _ (MvRatFunc (Fin 2) ℂ) (W i), ?_, ?_⟩
  · intro h
    apply hW0
    funext i
    have := congrFun h i
    simp only [Pi.zero_apply] at this ⊢
    exact (map_eq_zero_iff _ hinj).mp this
  · have := congrArg (algebraMap _ (MvRatFunc (Fin 2) ℂ)) hW
    simp only [map_sum, map_mul, map_pow, map_zero, hP] at this
    have h2 : (∑ i, q i * algebraMap _ (MvRatFunc (Fin 2) ℂ) (W i) ^ 2) * algebraMap _ (MvRatFunc (Fin 2) ℂ) Dn = 0 := by
      rw [Finset.sum_mul, ← this]
      refine Finset.sum_congr rfl fun i _ ↦ by ring
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

namespace OMA.Artin2K

open MilnorK

theorem exists_sqrt_neg_one : ∃ i : MvRatFunc (Fin 2) ℂ, i * i = -1 :=
  ⟨algebraMap (MvPolynomial (Fin 2) ℂ) _ (MvPolynomial.C Complex.I), by
    rw [← map_mul, ← MvPolynomial.C_mul, Complex.I_mul_I, MvPolynomial.C_neg,
      MvPolynomial.C_1, map_neg, map_one]⟩

theorem symbol_two {F : Type*} [Field F] (s : Fin 2 → Fˣ) :
    symbol 2 s = of 2 (s 0) * of 2 (s 1) := by
  simp [symbol_succ]

/-- Every class of `K^M_2(C(x, y))/2` is a single symbol. -/
theorem grade_two_single (x : MilnorK (MvRatFunc (Fin 2) ℂ) 2)
    (hx : x ∈ grade (MvRatFunc (Fin 2) ℂ) 2 2) :
    ∃ e f : (MvRatFunc (Fin 2) ℂ)ˣ, x = of 2 e * of 2 f := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    exact ⟨s 0, s 1, symbol_two s⟩
  | zero => exact ⟨1, 1, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨c, d, rfl⟩ := hz
    exact sum_two exists_sqrt_neg_one OMA.Artin2.isotropic5 a b c d
  | neg y _ hy =>
    obtain ⟨a, b, rfl⟩ := hy
    exact ⟨a⁻¹, b, by rw [of_inv, neg_eq_self, neg_eq_self]⟩

/-- Artin's theorem for `p = 2`: the symbol length of `K^M_2(C(x, y))/2` is at most `1`. -/
theorem one_mem : 1 ∈ symbolLengthBounds (MvRatFunc (Fin 2) ℂ) 2 2 := by
  intro x hx
  obtain ⟨e, f, rfl⟩ := grade_two_single x hx
  exact ⟨1, le_rfl, fun _ ↦ ![e, f], by simp [symbol_two]⟩

end OMA.Artin2K

theorem OMA.solution : OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_degree_two_isLeast_R1_H1_R1.H1 :=
  OMA.Artin2K.one_mem
