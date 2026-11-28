import OMAReductions.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_bounded_R1

/-!
Step H2 of reduction SymbolLengthMilnorKTheory.symbol_length_problem.variants.bounded.R1:
degree-two finiteness. For every m >= 2 and every prime p, the symbol length of
K_2(C(x_1, ..., x_m))/p is at most p^(m-1) - 1 (Matzri 2016, Theorem 8.2).

Contents:
(1) Tsen-Lang for C(x_1, ..., x_m) (Lang box count, Krull height theorem, Nullstellensatz).
(2) The Bass-Tate transfer for simple extensions via Milnor's degree filtration of K_*(F(t))/p,
    the projection formula, and the Kummer norm relation {a, N(k)} = 0.
(3) Matzri's Kummer-space argument: norm forms, slot lemma, zero lemma, Tsen-Lang count.
-/


-- Step SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two.R1.H2.R1.H1.R1.H2: Tsen-Lang for C(x_1, ..., x_m).
-- Credit: @hyprspacecoyote

/-!
Tsen-Lang for C(x_1, ..., x_m): a homogeneous form of degree d >= 1 in more than d ^ m
variables over MvRatFunc (Fin m) C has a nontrivial zero.

Proof (Lang's box count).
(1) Over C, finitely many polynomials without constant term, fewer than the variables, have a
    common nonzero zero (Krull's height theorem + Nullstellensatz).
(2) Clear denominators: a nonzero polynomial b makes every b * coeff s Phi a polynomial p s.
(3) Substitute V_j = sum over e in the box [0, S)^m of X_(j, e) x^e with unknown complex
    coefficients X_(j, e). The result Q has x-degree < r + d S in every variable, and its
    coefficients are polynomials in the unknowns without constant term (Phi is homogeneous of
    positive degree). There are at most (r + d S)^m of them and N S^m unknowns; since
    N > d ^ m the count works for S large.
(4) A common nonzero zero t gives polynomials W_j, not all zero, with sum p s W^s = 0; dividing
    by b gives a zero of Phi over MvRatFunc (Fin m) C.
-/
namespace OMA.TsenLang

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

end OMA.TsenLang


-- Step H1 of SymbolLengthMilnorKTheory.symbol_length_problem.variants.degree_two.R1.H2.R1.H1.R1:
-- the Kummer norm relation {a, N(k)} = 0 in K_2(F)/p for k in F[t]/(t^p - a).
--
-- Proof (Bass-Tate transfer via Milnor's exact sequence, all degrees at once, mod p).
-- For a field F with of(-1) = 0 in K_*/p (p odd, or p = 2 with i^2 = -1 in F):
--   * tame symbols at the finite places pi and at infinity of F(t), as ring maps
--     K_*(F(t))/p -> End(K_*(kappa)/p x K_*(kappa)/p), {u pi^i} acting by (x, y) -> ({u} x, i x - {u} y);
--   * Milnor's filtration S d (subring generated by classes of polynomials of degree <= d) and his
--     generation lemma S (d+1) = S d + sum {pi} S d over monic irreducible pi of degree d+1;
--   * for pi of degree d+1, the transfer N_pi : K_*(kappa(pi))/p -> K_*(F)/p, defined from the functional
--     Phi(Y) = -res_inf Y - sum over lower primes N_pi'(res_pi' Y), which vanishes on S d by induction
--     (Weil reciprocity); well-definedness comes from a ring map out of K_*(kappa(pi))/p acting on
--     functionals on S d through canonical lifts of degree < d+1 (the defect of multiplicativity is a
--     Steinberg relation of lower degree);
--   * by induction on d: Weil reciprocity on S d, the projection formula N({b} x) = {b} N(x) for b in F,
--     and N({u}) = {Norm(u)} (degree one Weil reciprocity, from the resultant swap of norms).
-- Then for a not a p-th power, pi = t^p - a is irreducible, {a} = p {theta} = 0 in K_1(kappa(pi))/p, so
-- {a, Norm(k)} = N({a}{k}) = 0. If a is a p-th power, {a} = 0 already.


/-! Basics on `MilnorK` and the generic tame symbol. -/

namespace OMA.NormRel

open MilnorK

section Basic

variable {E : Type*} [Field E] (p : ℕ)

/-- `mul_neg` for `MilnorK` (the generic lemma does not rewrite there). -/
theorem mul_neg' (x y : MilnorK E p) : x * -y = -(x * y) := mul_neg x y

theorem neg_mul' (x y : MilnorK E p) : -x * y = -(x * y) := neg_mul x y

theorem nsmul_p (x : MilnorK E p) : p • x = 0 := by
  rw [nsmul_eq_mul, natCast_eq_zero, zero_mul]

theorem of_add_of_inv (a : Eˣ) : of p a + of p a⁻¹ = 0 := by
  rw [← of_mul, mul_inv_cancel, of_one]

theorem mul_of_inv (x : MilnorK E p) (a : Eˣ) : x * of p a + x * of p a⁻¹ = 0 := by
  rw [← mul_add, of_add_of_inv, mul_zero]

theorem of_inv_mul (x : MilnorK E p) (a : Eˣ) : of p a * x + of p a⁻¹ * x = 0 := by
  rw [← add_mul, of_add_of_inv, zero_mul]

theorem eq_zero_of_add_eq_zero_left' {x y : MilnorK E p} (h1 : x + y = 0) (h2 : x = 0) :
    y = 0 := by
  rw [h2, zero_add] at h1; exact h1

/-- `{x, -x} = 0`. -/
theorem of_mul_of_neg_self (a : Eˣ) : of p a * of p (-a) = 0 := by
  by_cases ha : a = 1
  · simp [ha]
  have h1 : (1 : E) - a ≠ 0 := by
    intro h; apply ha; apply Units.ext; show (a : E) = 1; linear_combination -h
  have h2 : (1 : E) - (a⁻¹ : Eˣ) ≠ 0 := by
    intro h; apply ha; apply Units.ext; show (a : E) = 1
    have : ((a⁻¹ : Eˣ) : E) = 1 := by linear_combination -h
    simpa using congrArg (fun z : E ↦ z⁻¹) this
  set b := Units.mk0 _ h1
  set c := Units.mk0 _ h2
  have hb : of p a * of p b = 0 := of_mul_of_eq_zero p a b (by simp [b])
  have hc : of p a⁻¹ * of p c = 0 := of_mul_of_eq_zero p a⁻¹ c (by simp [c])
  have hc' : of p a * of p c = 0 := by
    have := of_inv_mul p (of p c) a
    rw [hc, add_zero] at this; exact this
  have hc'' : of p a * of p c⁻¹ = 0 :=
    eq_zero_of_add_eq_zero_left' p (mul_of_inv p (of p a) c) hc'
  have hneg : -a = b * c⁻¹ := by
    have ha0 : (a : E) ≠ 0 := a.ne_zero
    ext
    simp only [Units.val_neg, Units.val_mul, b, c, Units.val_mk0, Units.val_inv_eq_inv_val]
    field_simp
    have : (a : E) - 1 ≠ 0 := by intro h; apply h1; linear_combination -h
    field_simp
    ring
  rw [hneg, of_mul, mul_add, hb, hc'', add_zero]

/-- Anticommutativity in degree one. -/
theorem of_anticomm (a b : Eˣ) : of p a * of p b + of p b * of p a = 0 := by
  have h := of_mul_of_neg_self p (a * b)
  rw [of_mul, add_mul] at h
  have e1 : -(a * b) = (-a) * b := by simp
  have e2 : -(a * b) = a * (-b) := by simp
  have t1 : of p a * of p (-(a * b)) = of p a * of p b := by
    rw [e1, of_mul, mul_add, of_mul_of_neg_self, zero_add]
  have t2 : of p b * of p (-(a * b)) = of p b * of p a := by
    rw [e2, of_mul, mul_add, of_mul_of_neg_self, add_zero]
  rw [t1, t2] at h; exact h

theorem of_comm (a b : Eˣ) : of p a * of p b = -(of p b * of p a) :=
  eq_neg_of_add_eq_zero_left (of_anticomm p a b)

theorem of_neg_eq (h1 : of p (-1 : Eˣ) = 0) (a : Eˣ) : of p (-a) = of p a := by
  rw [show -a = (-1) * a by simp, of_mul, h1, zero_add]

theorem of_mul_self (h1 : of p (-1 : Eˣ) = 0) (a : Eˣ) : of p a * of p a = 0 := by
  have := of_mul_of_neg_self p a
  rwa [of_neg_eq p h1] at this

/-- `of (-1) = 0` when `p` is odd, or `p = 2` and `-1` is a square. -/
theorem of_neg_one_eq_zero (h : Odd p ∨ (p = 2 ∧ ∃ i : E, i * i = -1)) :
    of p (-1 : Eˣ) = 0 := by
  have h2 : 2 • of p (-1 : Eˣ) = 0 := by
    rw [← of_pow]; simp
  rcases h with ⟨k, hk⟩ | ⟨rfl, i, hi⟩
  · have h3 : (2 * k + 1) • of p (-1 : Eˣ) = 0 := by rw [← hk]; exact nsmul_p p _
    rw [add_nsmul, Nat.mul_comm 2 k, mul_nsmul', h2, nsmul_zero, zero_add, one_nsmul] at h3
    exact h3
  · have hi0 : i ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hi
      exact one_ne_zero (neg_eq_zero.mp hi.symm)
    have : (-1 : Eˣ) = Units.mk0 i hi0 ^ 2 := by
      ext; simp [sq, hi]
    rw [this, of_pow, nsmul_p]

/-- Ring maps out of `MilnorK E p`. -/
noncomputable def liftK {R : Type*} [Ring R] (f : Additive Eˣ →+ R)
    (hst : ∀ a b : Eˣ, (a : E) + (b : E) = 1 → f (Additive.ofMul a) * f (Additive.ofMul b) = 0)
    (hℓ : (p : R) = 0) : MilnorK E p →+* R :=
  RingQuot.lift ⟨(TensorAlgebra.lift ℤ f.toIntLinearMap).toRingHom, by
    intro x y h
    cases h with
    | steinberg a b h => simpa using hst a b h
    | natCast => simpa using hℓ⟩

theorem liftK_of {R : Type*} [Ring R] (f : Additive Eˣ →+ R)
    (hst : ∀ a b : Eˣ, (a : E) + (b : E) = 1 → f (Additive.ofMul a) * f (Additive.ofMul b) = 0)
    (hℓ : (p : R) = 0) (a : Eˣ) : liftK p f hst hℓ (of p a) = f (Additive.ofMul a) := by
  simp [liftK, MilnorK.of, RingQuot.lift_mkRingHom_apply]

/-- Induction principle for `MilnorK`. -/
theorem induction {P : MilnorK E p → Prop} (x : MilnorK E p) (h_int : ∀ n : ℤ, P n)
    (h_of : ∀ a : Eˣ, P (of p a)) (h_add : ∀ x y, P x → P y → P (x + y))
    (h_mul : ∀ x y, P x → P y → P (x * y)) : P x := by
  obtain ⟨t, rfl⟩ := RingQuot.mkRingHom_surjective (Rel E p) x
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
    have : RingQuot.mkRingHom (Rel E p) (algebraMap ℤ (TensorAlgebra ℤ (Additive Eˣ)) r) =
        (r : MilnorK E p) := by simp
    rw [this]; exact h_int r
  | ι a =>
    have : RingQuot.mkRingHom (Rel E p) (TensorAlgebra.ι ℤ a) = of p a.toMul := rfl
    rw [this]; exact h_of _
  | mul a b ha hb => rw [map_mul]; exact h_mul _ _ ha hb
  | add a b ha hb => rw [map_add]; exact h_add _ _ ha hb

end Basic

section EndLemmas

variable {M : Type*} [AddCommGroup M]

theorem End_add_apply (f g : AddMonoid.End M) (m : M) : (f + g) m = f m + g m := rfl
theorem End_neg_apply (f : AddMonoid.End M) (m : M) : (-f) m = -(f m) := rfl
theorem End_sub_apply (f g : AddMonoid.End M) (m : M) : (f - g) m = f m - g m := rfl
theorem End_mul_apply (f g : AddMonoid.End M) (m : M) : (f * g) m = f (g m) := rfl
theorem End_one_apply (m : M) : (1 : AddMonoid.End M) m = m := rfl
theorem End_zero_apply (m : M) : (0 : AddMonoid.End M) m = 0 := rfl

end EndLemmas

/-! ### The generic tame symbol -/

/-- A discrete valuation `v` with angular component `r` on `K`, with values in the residue
field `κ`, compatible with the Steinberg relation. -/
structure ValData (K κ : Type*) [Field K] [Field κ] where
  v : Kˣ → ℤ
  r : Kˣ → κˣ
  v_mul : ∀ f g, v (f * g) = v f + v g
  r_mul : ∀ f g, r (f * g) = r f * r g
  st : ∀ f g : Kˣ, (f : K) + g = 1 → (v f = 0 ∧ r f = 1) ∨ (v g = 0 ∧ r g = 1) ∨
    (v f = v g ∧ r g = -r f) ∨ (v f = 0 ∧ v g = 0 ∧ ((r f : κ) + r g = 1))

section Tame

variable {K κ : Type*} [Field K] [Field κ] (p : ℕ)

theorem ValData.v_one (D : ValData K κ) : D.v 1 = 0 := by
  have := D.v_mul 1 1; simp at this; linarith

theorem ValData.r_one (D : ValData K κ) : D.r 1 = 1 := by
  have := D.r_mul 1 1; simpa using this

/-- The action of a single class `{f}`: `(x, y) ↦ ({r f} x, v(f) x - {r f} y)`. -/
noncomputable def tameEnd (D : ValData K κ) (f : Kˣ) :
    AddMonoid.End (MilnorK κ p × MilnorK κ p) where
  toFun xy := (of p (D.r f) * xy.1, D.v f • xy.1 - of p (D.r f) * xy.2)
  map_zero' := by simp
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, mul_add, smul_add, Prod.mk_add_mk]
    congr 1; abel

theorem tameEnd_apply (D : ValData K κ) (f : Kˣ) (xy : MilnorK κ p × MilnorK κ p) :
    tameEnd p D f xy = (of p (D.r f) * xy.1, D.v f • xy.1 - of p (D.r f) * xy.2) := rfl

noncomputable def tameGen (D : ValData K κ) :
    Additive Kˣ →+ AddMonoid.End (MilnorK κ p × MilnorK κ p) where
  toFun f := tameEnd p D f.toMul
  map_zero' := by
    ext xy <;> simp [tameEnd_apply, D.v_one, D.r_one]
  map_add' f g := by
    ext xy <;> simp only [tameEnd_apply, toMul_add, D.v_mul, D.r_mul, of_mul,
      End_add_apply, Prod.fst_add, Prod.snd_add, add_mul, add_smul]
    abel

theorem tame_st (hκ : of p (-1 : κˣ) = 0) (D : ValData K κ) (f g : Kˣ) (h : (f : K) + g = 1) :
    tameGen p D (Additive.ofMul f) * tameGen p D (Additive.ofMul g) = 0 := by
  have key1 : of p (D.r f) * of p (D.r g) = 0 := by
    rcases D.st f g h with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, _, h3⟩
    · rw [h2, of_one, zero_mul]
    · rw [h2, of_one, mul_zero]
    · rw [h2]; exact of_mul_of_neg_self p _
    · exact of_mul_of_eq_zero p _ _ h3
  have key2 : D.v f • of p (D.r g) - D.v g • of p (D.r f) = 0 := by
    rcases D.st f g h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2, _⟩
    · rw [h1, h2, of_one]; simp
    · rw [h1, h2, of_one]; simp
    · rw [h2, h1, of_neg_eq p hκ, sub_self]
    · rw [h1, h2]; simp
  ext xy
  · show of p (D.r f) * (of p (D.r g) * xy.1) = 0
    rw [← mul_assoc, key1, zero_mul]
  · show D.v f • (of p (D.r g) * xy.1) -
        of p (D.r f) * (D.v g • xy.1 - of p (D.r g) * xy.2) = 0
    have e : D.v f • (of p (D.r g) * xy.1) -
        of p (D.r f) * (D.v g • xy.1 - of p (D.r g) * xy.2) =
        (D.v f • of p (D.r g) - D.v g • of p (D.r f)) * xy.1 +
          (of p (D.r f) * of p (D.r g)) * xy.2 := by
      rw [mul_sub, sub_mul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, ← mul_assoc]
      abel
    rw [e, key1, key2, zero_mul, zero_mul, add_zero]

theorem tame_nat : ((p : AddMonoid.End (MilnorK κ p × MilnorK κ p))) = 0 := by
  ext xy <;> simp [AddMonoid.End.natCast_apply, nsmul_p]

/-- The tame symbol of a valuation datum, as a ring map into endomorphisms of `K(κ)²`. -/
noncomputable def tame (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) :
    MilnorK K p →+* AddMonoid.End (MilnorK κ p × MilnorK κ p) :=
  liftK (R := AddMonoid.End (MilnorK κ p × MilnorK κ p)) p (tameGen p D) (tame_st p hκ D)
    (tame_nat p)

variable {p}

theorem tame_of (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (f : Kˣ)
    (xy : MilnorK κ p × MilnorK κ p) :
    tame p D hκ (of p f) xy = (of p (D.r f) * xy.1, D.v f • xy.1 - of p (D.r f) * xy.2) := by
  rw [tame, liftK_of]; rfl

/-- Right multiplication commutes with the tame action. -/
theorem tame_rmul (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (z : MilnorK K p)
    (x y w : MilnorK κ p) :
    tame p D hκ z (x * w, y * w) =
      ((tame p D hκ z (x, y)).1 * w, (tame p D hκ z (x, y)).2 * w) := by
  induction z using induction (p := p) generalizing x y with
  | h_int n =>
    simp [map_intCast, AddMonoid.End.intCast_apply, mul_assoc]
  | h_of a =>
    simp only [tame_of]
    ext
    · simp [mul_assoc]
    · simp [sub_mul, smul_mul_assoc, mul_assoc]
  | h_add z1 z2 h1 h2 =>
    rw [map_add, End_add_apply, End_add_apply, h1 x y, h2 x y]
    simp [add_mul]
  | h_mul z1 z2 h1 h2 =>
    rw [map_mul, End_mul_apply, End_mul_apply, h2 x y, h1]

/-- The residue. -/
noncomputable def res (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (z : MilnorK K p) :
    MilnorK κ p := (tame p D hκ z (1, 0)).2

/-- The specialization. -/
noncomputable def spec (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (z : MilnorK K p) :
    MilnorK κ p := (tame p D hκ z (1, 0)).1

theorem tame_eq (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (z : MilnorK K p) :
    tame p D hκ z (1, 0) = (spec D hκ z, res D hκ z) := rfl

theorem tame_x0 (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (z : MilnorK K p)
    (x : MilnorK κ p) :
    tame p D hκ z (x, 0) = (spec D hκ z * x, res D hκ z * x) := by
  have := tame_rmul D hκ z 1 0 x
  rw [one_mul, zero_mul] at this
  rw [this]; rfl

theorem res_add (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (z w : MilnorK K p) :
    res D hκ (z + w) = res D hκ z + res D hκ w := by
  simp only [res, map_add, End_add_apply, Prod.snd_add]

theorem spec_add (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (z w : MilnorK K p) :
    spec D hκ (z + w) = spec D hκ z + spec D hκ w := by
  simp only [spec, map_add, End_add_apply, Prod.fst_add]

theorem res_neg (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (z : MilnorK K p) :
    res D hκ (-z) = -res D hκ z := by
  simp only [res, map_neg, End_neg_apply, Prod.snd_neg]

theorem spec_neg (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (z : MilnorK K p) :
    spec D hκ (-z) = -spec D hκ z := by
  simp only [spec, map_neg, End_neg_apply, Prod.fst_neg]

theorem tame_mul_apply (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (z w : MilnorK K p)
    (xy : MilnorK κ p × MilnorK κ p) :
    tame p D hκ (z * w) xy = tame p D hκ z (tame p D hκ w xy) := by
  rw [map_mul]; rfl

theorem res_one (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) : res D hκ 1 = 0 := by
  simp [res]

theorem spec_one (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) : spec D hκ 1 = 1 := by
  simp [spec]

theorem res_intCast (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (n : ℤ) :
    res D hκ (n : MilnorK K p) = 0 := by
  simp [res, map_intCast, AddMonoid.End.intCast_apply]

theorem spec_intCast (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (n : ℤ) :
    spec D hκ (n : MilnorK K p) = n := by
  simp [spec, map_intCast, AddMonoid.End.intCast_apply]

theorem tame_of_mul (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (f : Kˣ) (z : MilnorK K p) :
    tame p D hκ (of p f * z) (1, 0) = (of p (D.r f) * spec D hκ z,
      D.v f • spec D hκ z - of p (D.r f) * res D hκ z) := by
  rw [tame_mul_apply, tame_eq, tame_of]

theorem res_of_mul (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (f : Kˣ) (z : MilnorK K p) :
    res D hκ (of p f * z) = D.v f • spec D hκ z - of p (D.r f) * res D hκ z :=
  congrArg Prod.snd (tame_of_mul D hκ f z)

theorem spec_of_mul (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (f : Kˣ) (z : MilnorK K p) :
    spec D hκ (of p f * z) = of p (D.r f) * spec D hκ z :=
  congrArg Prod.fst (tame_of_mul D hκ f z)

theorem res_of (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (f : Kˣ) :
    res D hκ (of p f) = D.v f • (1 : MilnorK κ p) := by
  have := res_of_mul D hκ f 1
  rw [mul_one, spec_one, res_one, mul_zero, sub_zero] at this
  exact this

theorem spec_of (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (f : Kˣ) :
    spec D hκ (of p f) = of p (D.r f) := by
  have := spec_of_mul D hκ f 1
  rw [mul_one, spec_one, mul_one] at this
  exact this

theorem tame_mul_of_res_eq_zero (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0)
    (z w : MilnorK K p) (hw : res D hκ w = 0) :
    tame p D hκ (z * w) (1, 0) = (spec D hκ z * spec D hκ w, res D hκ z * spec D hκ w) := by
  rw [tame_mul_apply, tame_eq D hκ w, hw, tame_x0]

theorem res_mul_of_res_eq_zero (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (z w : MilnorK K p)
    (hw : res D hκ w = 0) : res D hκ (z * w) = res D hκ z * spec D hκ w :=
  congrArg Prod.snd (tame_mul_of_res_eq_zero D hκ z w hw)

theorem spec_mul_of_res_eq_zero (D : ValData K κ) (hκ : of p (-1 : κˣ) = 0) (z w : MilnorK K p)
    (hw : res D hκ w = 0) : spec D hκ (z * w) = spec D hκ z * spec D hκ w :=
  congrArg Prod.fst (tame_mul_of_res_eq_zero D hκ z w hw)

end Tame

end OMA.NormRel


/-! Valuations on `RatFunc F` coming from polynomial data: the finite places and `∞`. -/

namespace OMA.NormRel

open MilnorK Polynomial

/-- Valuation data on polynomials, with an angular component in `κ`. -/
structure PolyVal (F κ : Type*) [Field F] [Field κ] [Algebra F κ] where
  vp : F[X] → ℤ
  rp : F[X] → κ
  rp_ne : ∀ P, P ≠ 0 → rp P ≠ 0
  vp_mul : ∀ P Q, P ≠ 0 → Q ≠ 0 → vp (P * Q) = vp P + vp Q
  rp_mul : ∀ P Q, P ≠ 0 → Q ≠ 0 → rp (P * Q) = rp P * rp Q
  vp_C : ∀ c : F, c ≠ 0 → vp (C c) = 0
  rp_C : ∀ c : F, c ≠ 0 → rp (C c) = algebraMap F κ c
  ultra_lt : ∀ A B, A ≠ 0 → B ≠ 0 → vp A < vp B →
    A + B ≠ 0 ∧ vp (A + B) = vp A ∧ rp (A + B) = rp A
  ultra_eq : ∀ A B, A ≠ 0 → B ≠ 0 → vp A = vp B → rp A + rp B ≠ 0 →
    A + B ≠ 0 ∧ vp (A + B) = vp A ∧ rp (A + B) = rp A + rp B

section PolyVal

variable {F : Type*} [Field F] {κ : Type*} [Field κ] [Algebra F κ] (V : PolyVal F κ)

theorem PolyVal.vp_one : V.vp 1 = 0 := by simpa using V.vp_C 1 one_ne_zero

theorem PolyVal.rp_one : V.rp 1 = 1 := by simpa using V.rp_C 1 one_ne_zero

theorem PolyVal.vp_neg (P : F[X]) (hP : P ≠ 0) : V.vp (-P) = V.vp P := by
  have := V.vp_mul (C (-1)) P (by simp) hP
  rw [V.vp_C _ (by simp)] at this; simpa using this

theorem PolyVal.rp_neg (P : F[X]) (hP : P ≠ 0) : V.rp (-P) = -V.rp P := by
  have := V.rp_mul (C (-1)) P (by simp) hP
  rw [V.rp_C _ (by simp)] at this; simpa using this

/-- The valuation of a nonzero rational function. -/
noncomputable def PolyVal.v (f : (RatFunc F)ˣ) : ℤ :=
  V.vp (f : RatFunc F).num - V.vp (f : RatFunc F).denom

/-- The angular component of a nonzero rational function. -/
noncomputable def PolyVal.r (f : (RatFunc F)ˣ) : κˣ :=
  Units.mk0 (V.rp (f : RatFunc F).num / V.rp (f : RatFunc F).denom)
    (div_ne_zero (V.rp_ne _ (RatFunc.num_ne_zero f.ne_zero)) (V.rp_ne _ (RatFunc.denom_ne_zero _)))

theorem PolyVal.rep (f : (RatFunc F)ˣ) (P Q : F[X]) (hP : P ≠ 0) (hQ : Q ≠ 0)
    (h : (f : RatFunc F) = algebraMap F[X] (RatFunc F) P / algebraMap F[X] (RatFunc F) Q) :
    V.v f = V.vp P - V.vp Q ∧ (V.r f : κ) = V.rp P / V.rp Q := by
  have hn : (f : RatFunc F).num ≠ 0 := RatFunc.num_ne_zero f.ne_zero
  have hd : (f : RatFunc F).denom ≠ 0 := RatFunc.denom_ne_zero _
  have hinj := RatFunc.algebraMap_injective F
  have hQ' : algebraMap F[X] (RatFunc F) Q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hQ
  have hd' : algebraMap F[X] (RatFunc F) (f : RatFunc F).denom ≠ 0 :=
    (map_ne_zero_iff _ hinj).mpr hd
  have key : (f : RatFunc F).num * Q = P * (f : RatFunc F).denom := by
    apply hinj
    have e := (RatFunc.num_div_denom (f : RatFunc F)).trans h
    rw [map_mul, map_mul]
    exact (div_eq_div_iff hd' hQ').mp e
  have hv := congrArg V.vp key
  rw [V.vp_mul _ _ hn hQ, V.vp_mul _ _ hP hd] at hv
  have hr := congrArg V.rp key
  rw [V.rp_mul _ _ hn hQ, V.rp_mul _ _ hP hd] at hr
  refine ⟨by unfold PolyVal.v; omega, ?_⟩
  simp only [PolyVal.r, Units.val_mk0]
  exact (div_eq_div_iff (V.rp_ne _ hd) (V.rp_ne _ hQ)).mpr hr

theorem PolyVal.v_def (f : (RatFunc F)ˣ) :
    V.v f = V.vp (f : RatFunc F).num - V.vp (f : RatFunc F).denom := rfl

theorem PolyVal.r_def (f : (RatFunc F)ˣ) :
    (V.r f : κ) = V.rp (f : RatFunc F).num / V.rp (f : RatFunc F).denom := rfl

theorem num_div_denom' (f : RatFunc F) :
    f = algebraMap F[X] (RatFunc F) f.num / algebraMap F[X] (RatFunc F) f.denom :=
  (RatFunc.num_div_denom f).symm

theorem PolyVal.v_mul (f g : (RatFunc F)ˣ) : V.v (f * g) = V.v f + V.v g ∧
    V.r (f * g) = V.r f * V.r g := by
  have hfn : (f : RatFunc F).num ≠ 0 := RatFunc.num_ne_zero f.ne_zero
  have hgn : (g : RatFunc F).num ≠ 0 := RatFunc.num_ne_zero g.ne_zero
  have hfd : (f : RatFunc F).denom ≠ 0 := RatFunc.denom_ne_zero _
  have hgd : (g : RatFunc F).denom ≠ 0 := RatFunc.denom_ne_zero _
  have e : ((f * g : (RatFunc F)ˣ) : RatFunc F) =
      algebraMap F[X] (RatFunc F) ((f : RatFunc F).num * (g : RatFunc F).num) /
        algebraMap F[X] (RatFunc F) ((f : RatFunc F).denom * (g : RatFunc F).denom) := by
    rw [Units.val_mul, map_mul, map_mul, ← div_mul_div_comm, ← num_div_denom',
      ← num_div_denom']
  obtain ⟨h1, h2⟩ := V.rep (f * g) _ _ (mul_ne_zero hfn hgn) (mul_ne_zero hfd hgd) e
  refine ⟨?_, ?_⟩
  · rw [h1, V.vp_mul _ _ hfn hgn, V.vp_mul _ _ hfd hgd, V.v_def, V.v_def]; ring
  · ext
    rw [h2, V.rp_mul _ _ hfn hgn, V.rp_mul _ _ hfd hgd, Units.val_mul, V.r_def, V.r_def,
      div_mul_div_comm]

theorem PolyVal.st (f g : (RatFunc F)ˣ) (h : (f : RatFunc F) + g = 1) :
    (V.v f = 0 ∧ V.r f = 1) ∨ (V.v g = 0 ∧ V.r g = 1) ∨
    (V.v f = V.v g ∧ V.r g = -V.r f) ∨
    (V.v f = 0 ∧ V.v g = 0 ∧ ((V.r f : κ) + V.r g = 1)) := by
  set P := (f : RatFunc F).num
  set Q := (f : RatFunc F).denom
  have hP : P ≠ 0 := RatFunc.num_ne_zero f.ne_zero
  have hQ : Q ≠ 0 := RatFunc.denom_ne_zero _
  have hinj := RatFunc.algebraMap_injective F
  have hQ' : algebraMap F[X] (RatFunc F) Q ≠ 0 := (map_ne_zero_iff _ hinj).mpr hQ
  have hf : (f : RatFunc F) = algebraMap F[X] (RatFunc F) P / algebraMap F[X] (RatFunc F) Q :=
    num_div_denom' _
  have hg : (g : RatFunc F) =
      algebraMap F[X] (RatFunc F) (Q - P) / algebraMap F[X] (RatFunc F) Q := by
    have : (g : RatFunc F) = 1 - f := by rw [← h]; ring
    rw [this, hf, map_sub]; field_simp
  have hQP : Q - P ≠ 0 := by
    intro h0; rw [h0, map_zero, zero_div] at hg; exact g.ne_zero hg
  obtain ⟨hvf, hrf⟩ := V.rep f P Q hP hQ hf
  obtain ⟨hvg, hrg⟩ := V.rep g (Q - P) Q hQP hQ hg
  have hrQ := V.rp_ne Q hQ
  rcases lt_trichotomy (V.vp P) (V.vp Q) with hlt | heq | hgt
  · obtain ⟨_, h2, h3⟩ := V.ultra_lt (-P) Q (neg_ne_zero.mpr hP) hQ (by rwa [V.vp_neg P hP])
    rw [← sub_eq_neg_add] at h2 h3
    rw [V.vp_neg P hP] at h2
    rw [V.rp_neg P hP] at h3
    right; right; left
    refine ⟨by rw [hvf, hvg, h2], ?_⟩
    ext; rw [hrg, Units.val_neg, hrf, h3, neg_div]
  · by_cases hr : V.rp P = V.rp Q
    · left
      refine ⟨by rw [hvf, heq, sub_self], ?_⟩
      ext; rw [hrf, hr, div_self hrQ, Units.val_one]
    · have hne : V.rp Q + V.rp (-P) ≠ 0 := by
        rw [V.rp_neg P hP, ← sub_eq_add_neg]
        exact sub_ne_zero.mpr (Ne.symm hr)
      obtain ⟨_, h2, h3⟩ := V.ultra_eq Q (-P) hQ (neg_ne_zero.mpr hP)
        (by rw [V.vp_neg P hP, heq]) hne
      rw [← sub_eq_add_neg] at h2 h3
      rw [V.rp_neg P hP, ← sub_eq_add_neg] at h3
      right; right; right
      refine ⟨by rw [hvf, heq, sub_self], by rw [hvg, h2, sub_self], ?_⟩
      rw [hrf, hrg, h3]; field_simp; ring
  · obtain ⟨_, h2, h3⟩ := V.ultra_lt Q (-P) hQ (neg_ne_zero.mpr hP) (by rwa [V.vp_neg P hP])
    rw [← sub_eq_add_neg] at h2 h3
    right; left
    refine ⟨by rw [hvg, h2, sub_self], ?_⟩
    ext; rw [hrg, h3, div_self hrQ, Units.val_one]

/-- The valuation datum on `RatFunc F`. -/
noncomputable def PolyVal.toVal : ValData (RatFunc F) κ where
  v := V.v
  r := V.r
  v_mul f g := (V.v_mul f g).1
  r_mul f g := (V.v_mul f g).2
  st := V.st

/-- A nonzero polynomial as a unit of `RatFunc F`. -/
noncomputable def uP (P : F[X]) (hP : P ≠ 0) : (RatFunc F)ˣ :=
  Units.mk0 (algebraMap F[X] (RatFunc F) P)
    ((map_ne_zero_iff _ (RatFunc.algebraMap_injective F)).mpr hP)

theorem uP_val (P : F[X]) (hP : P ≠ 0) :
    ((uP P hP : (RatFunc F)ˣ) : RatFunc F) = algebraMap F[X] (RatFunc F) P := rfl

theorem PolyVal.toVal_uP (P : F[X]) (hP : P ≠ 0) :
    V.toVal.v (uP P hP) = V.vp P ∧ (V.toVal.r (uP P hP) : κ) = V.rp P := by
  obtain ⟨h1, h2⟩ := V.rep (uP P hP) P 1 hP one_ne_zero (by rw [uP_val, map_one, div_one])
  exact ⟨by rw [show V.toVal.v = V.v from rfl, h1, V.vp_one, sub_zero],
    by rw [show V.toVal.r = V.r from rfl, h2, V.rp_one, div_one]⟩

theorem uP_mul (P Q : F[X]) (hP : P ≠ 0) (hQ : Q ≠ 0) :
    uP (P * Q) (mul_ne_zero hP hQ) = uP P hP * uP Q hQ := by
  ext; simp [uP_val]

theorem uP_congr {P Q : F[X]} (h : P = Q) (hP : P ≠ 0) (hQ : Q ≠ 0) : uP P hP = uP Q hQ := by
  subst h; rfl

end PolyVal

/-! ### The finite places -/

section Finite

variable {F : Type*} [Field F]

theorem exists_decomp {π : F[X]} (hπ : Irreducible π) {P : F[X]} (hP : P ≠ 0) :
    ∃ n : ℕ, ∃ Q : F[X], P = π ^ n * Q ∧ ¬ π ∣ Q := by
  induction h : P.natDegree using Nat.strong_induction_on generalizing P with
  | _ N ih =>
    by_cases hd : π ∣ P
    · obtain ⟨P1, rfl⟩ := hd
      have hP1 : P1 ≠ 0 := right_ne_zero_of_mul hP
      have hπ0 : π ≠ 0 := hπ.ne_zero
      have hπd : 0 < π.natDegree :=
        natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible hπ)
      have hdeg : P1.natDegree < N := by
        rw [← h, natDegree_mul hπ0 hP1]; omega
      obtain ⟨n, Q, hQ, hn⟩ := ih _ hdeg hP1 rfl
      exact ⟨n + 1, Q, by rw [hQ, pow_succ]; ring, hn⟩
    · exact ⟨0, P, by simp, hd⟩

theorem decomp_unique {π : F[X]} (hπ : Irreducible π) {n m : ℕ} {Q Q' : F[X]}
    (h : π ^ n * Q = π ^ m * Q') (hQ : ¬ π ∣ Q) (hQ' : ¬ π ∣ Q') : n = m ∧ Q = Q' := by
  have hπ0 : π ≠ 0 := hπ.ne_zero
  rcases le_total n m with hnm | hnm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add, mul_assoc] at h
    have h2 := mul_left_cancel₀ (pow_ne_zero n hπ0) h
    rcases k with _ | k
    · simp at h2; exact ⟨by simp, h2⟩
    · exact absurd (h2 ▸ dvd_mul_of_dvd_left (dvd_pow_self π (Nat.succ_ne_zero k)) Q') hQ
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnm
    rw [pow_add, mul_assoc] at h
    have h2 := mul_left_cancel₀ (pow_ne_zero m hπ0) h
    rcases k with _ | k
    · simp at h2; exact ⟨by simp, h2⟩
    · exact absurd (h2 ▸ dvd_mul_of_dvd_left (dvd_pow_self π (Nat.succ_ne_zero k)) Q) hQ'

open Classical in
/-- The exponent of `π` in `P`. -/
noncomputable def dexp (π P : F[X]) : ℕ :=
  if h : Irreducible π ∧ P ≠ 0 then (exists_decomp h.1 h.2).choose else 0

open Classical in
/-- The cofactor of `π` in `P`. -/
noncomputable def dcof (π P : F[X]) : F[X] :=
  if h : Irreducible π ∧ P ≠ 0 then (exists_decomp h.1 h.2).choose_spec.choose else 0

theorem decomp_spec {π : F[X]} (hπ : Irreducible π) {P : F[X]} (hP : P ≠ 0) :
    P = π ^ dexp π P * dcof π P ∧ ¬ π ∣ dcof π P := by
  have h : Irreducible π ∧ P ≠ 0 := ⟨hπ, hP⟩
  simp only [dexp, dcof, dif_pos h]
  exact (exists_decomp h.1 h.2).choose_spec.choose_spec

theorem decomp_eq {π : F[X]} (hπ : Irreducible π) {P : F[X]} (n : ℕ) (Q : F[X])
    (h : P = π ^ n * Q) (hQ : ¬ π ∣ Q) : dexp π P = n ∧ dcof π P = Q := by
  have hP : P ≠ 0 := by
    rintro rfl
    rcases mul_eq_zero.mp h.symm with h1 | h1
    · exact hπ.ne_zero (pow_eq_zero_iff'.mp h1).1
    · exact hQ (h1 ▸ dvd_zero π)
  obtain ⟨h1, h2⟩ := decomp_spec hπ hP
  have := decomp_unique hπ (h1.symm.trans h) h2 hQ
  exact this

/-- The `π`-adic valuation datum on polynomials. -/
noncomputable def finVal (π : F[X]) [hπ : Fact (Irreducible π)] : PolyVal F (AdjoinRoot π) where
  vp P := dexp π P
  rp P := AdjoinRoot.mk π (dcof π P)
  rp_ne P hP := by
    rw [Ne, AdjoinRoot.mk_eq_zero]; exact (decomp_spec hπ.out hP).2
  vp_mul P Q hP hQ := by
    obtain ⟨h1, h2⟩ := decomp_spec hπ.out hP
    obtain ⟨h3, h4⟩ := decomp_spec hπ.out hQ
    have := decomp_eq hπ.out (P := P * Q) (dexp π P + dexp π Q) (dcof π P * dcof π Q)
      (by rw [pow_add]; nth_rewrite 1 [h1]; nth_rewrite 1 [h3]; ring)
      (fun hd => (hπ.out.prime.dvd_or_dvd hd).elim h2 h4)
    rw [this.1]; push_cast; ring
  rp_mul P Q hP hQ := by
    obtain ⟨h1, h2⟩ := decomp_spec hπ.out hP
    obtain ⟨h3, h4⟩ := decomp_spec hπ.out hQ
    have := decomp_eq hπ.out (P := P * Q) (dexp π P + dexp π Q) (dcof π P * dcof π Q)
      (by rw [pow_add]; nth_rewrite 1 [h1]; nth_rewrite 1 [h3]; ring)
      (fun hd => (hπ.out.prime.dvd_or_dvd hd).elim h2 h4)
    rw [this.2, map_mul]
  vp_C c hc := by
    have := decomp_eq hπ.out (P := C c) 0 (C c) (by simp)
      (fun hd => hπ.out.not_isUnit (isUnit_of_dvd_unit hd (isUnit_C.mpr (Ne.isUnit hc))))
    rw [this.1]; rfl
  rp_C c hc := by
    have := decomp_eq hπ.out (P := C c) 0 (C c) (by simp)
      (fun hd => hπ.out.not_isUnit (isUnit_of_dvd_unit hd (isUnit_C.mpr (Ne.isUnit hc))))
    rw [this.2, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]
  ultra_lt A B hA hB h := by
    obtain ⟨h1, h2⟩ := decomp_spec hπ.out hA
    obtain ⟨h3, h4⟩ := decomp_spec hπ.out hB
    have hlt : dexp π A < dexp π B := by exact_mod_cast h
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_lt hlt
    have hsum : A + B = π ^ dexp π A * (dcof π A + π ^ (k + 1) * dcof π B) := by
      nth_rewrite 1 [h1]; nth_rewrite 1 [h3]; rw [hk]; ring
    have hnd : ¬ π ∣ dcof π A + π ^ (k + 1) * dcof π B := by
      intro hd
      exact h2 ((dvd_add_left (dvd_mul_of_dvd_left (dvd_pow_self π (Nat.succ_ne_zero k)) _)).mp hd)
    have := decomp_eq hπ.out _ _ hsum hnd
    refine ⟨?_, by rw [this.1], ?_⟩
    · intro h0; rw [h0] at hsum
      rcases mul_eq_zero.mp hsum.symm with h5 | h5
      · exact hπ.out.ne_zero (pow_eq_zero_iff'.mp h5).1
      · exact hnd (h5 ▸ dvd_zero π)
    · show AdjoinRoot.mk π (dcof π (A + B)) = AdjoinRoot.mk π (dcof π A)
      rw [this.2, map_add, map_mul, map_pow, AdjoinRoot.mk_self, zero_pow (Nat.succ_ne_zero k),
        zero_mul, add_zero]
  ultra_eq A B hA hB h hne := by
    obtain ⟨h1, h2⟩ := decomp_spec hπ.out hA
    obtain ⟨h3, h4⟩ := decomp_spec hπ.out hB
    have heq : dexp π A = dexp π B := by exact_mod_cast h
    have hsum : A + B = π ^ dexp π A * (dcof π A + dcof π B) := by
      nth_rewrite 1 [h1]; nth_rewrite 1 [h3]; rw [heq]; ring
    have hnd : ¬ π ∣ dcof π A + dcof π B := by
      intro hd; apply hne
      show AdjoinRoot.mk π (dcof π A) + AdjoinRoot.mk π (dcof π B) = 0
      rw [← map_add, AdjoinRoot.mk_eq_zero]; exact hd
    have := decomp_eq hπ.out _ _ hsum hnd
    refine ⟨?_, by rw [this.1], ?_⟩
    · intro h0; rw [h0] at hsum
      rcases mul_eq_zero.mp hsum.symm with h5 | h5
      · exact hπ.out.ne_zero (pow_eq_zero_iff'.mp h5).1
      · exact hnd (h5 ▸ dvd_zero π)
    · show AdjoinRoot.mk π (dcof π (A + B)) =
        AdjoinRoot.mk π (dcof π A) + AdjoinRoot.mk π (dcof π B)
      rw [this.2, map_add]

theorem finVal_of_not_dvd (π : F[X]) [hπ : Fact (Irreducible π)] {P : F[X]} (hP : ¬ π ∣ P) :
    (finVal π).vp P = 0 ∧ (finVal π).rp P = AdjoinRoot.mk π P := by
  have := decomp_eq hπ.out (P := P) 0 P (by simp) hP
  exact ⟨by show (dexp π P : ℤ) = 0; rw [this.1]; rfl,
    by show AdjoinRoot.mk π (dcof π P) = _; rw [this.2]⟩

theorem finVal_self (π : F[X]) [hπ : Fact (Irreducible π)] :
    (finVal π).vp π = 1 ∧ (finVal π).rp π = 1 := by
  have := decomp_eq hπ.out (P := π) 1 1 (by simp)
    (fun hd => hπ.out.not_isUnit (isUnit_of_dvd_one hd))
  exact ⟨by show (dexp π π : ℤ) = 1; rw [this.1]; rfl,
    by show AdjoinRoot.mk π (dcof π π) = 1; rw [this.2, map_one]⟩

end Finite

/-! ### The place at infinity -/

section Infinite

variable {F : Type*} [Field F]

/-- The valuation at `∞`: minus the degree, with the leading coefficient. -/
noncomputable def infVal : PolyVal F F where
  vp P := -(P.natDegree : ℤ)
  rp P := P.leadingCoeff
  rp_ne P hP := leadingCoeff_ne_zero.mpr hP
  vp_mul P Q hP hQ := by rw [natDegree_mul hP hQ]; push_cast; ring
  rp_mul P Q _ _ := leadingCoeff_mul P Q
  vp_C c _ := by simp
  rp_C c _ := by simp
  ultra_lt A B hA hB h := by
    have hlt : B.natDegree < A.natDegree := by omega
    have hdeg : B.degree < A.degree := degree_lt_degree hlt
    have h1 := natDegree_add_eq_left_of_natDegree_lt hlt
    refine ⟨?_, by rw [h1], leadingCoeff_add_of_degree_lt' hdeg⟩
    intro h0; rw [h0, natDegree_zero] at h1; omega
  ultra_eq A B hA hB h hne := by
    have hdeg : A.natDegree = B.natDegree := by omega
    have hdeg' : A.degree = B.degree := by
      rw [degree_eq_natDegree hA, degree_eq_natDegree hB, hdeg]
    have hsum := leadingCoeff_add_of_degree_eq hdeg' hne
    have hAB : A + B ≠ 0 := by
      intro h0; rw [h0, leadingCoeff_zero] at hsum; exact hne hsum.symm
    refine ⟨hAB, ?_, hsum⟩
    have h2 := degree_add_eq_of_leadingCoeff_add_ne_zero hne
    rw [hdeg', max_self] at h2
    have h3 : (A + B).natDegree = B.natDegree := natDegree_eq_of_degree_eq h2
    show -((A + B).natDegree : ℤ) = -(A.natDegree : ℤ)
    rw [h3, hdeg]

end Infinite

/-! ### Primes and residue fields -/

/-- Monic irreducible polynomials. -/
abbrev Prim (F : Type*) [Field F] := {P : F[X] // P.Monic ∧ Irreducible P}

instance Prim.fact {F : Type*} [Field F] (π : Prim F) : Fact (Irreducible π.1) := ⟨π.2.2⟩

/-- The residue field of a prime. -/
abbrev Kap {F : Type*} [Field F] (π : Prim F) := AdjoinRoot π.1

section Places

variable {F : Type*} [Field F]

/-- The valuation datum of a finite place. -/
noncomputable def valF (π : Prim F) : ValData (RatFunc F) (Kap π) := (finVal π.1).toVal

/-- The valuation datum at `∞`. -/
noncomputable def valI : ValData (RatFunc F) F := (infVal (F := F)).toVal

theorem valF_uP (π : Prim F) (P : F[X]) (hP : P ≠ 0) :
    (valF π).v (uP P hP) = (finVal π.1).vp P ∧ ((valF π).r (uP P hP) : Kap π) =
      (finVal π.1).rp P :=
  (finVal π.1).toVal_uP P hP

theorem valI_uP (P : F[X]) (hP : P ≠ 0) :
    valI.v (uP P hP) = -(P.natDegree : ℤ) ∧ (valI.r (uP P hP) : F) = P.leadingCoeff :=
  (infVal (F := F)).toVal_uP P hP

theorem valF_uP_of_not_dvd (π : Prim F) {P : F[X]} (hP : P ≠ 0) (hd : ¬ π.1 ∣ P) :
    (valF π).v (uP P hP) = 0 ∧ ((valF π).r (uP P hP) : Kap π) = AdjoinRoot.mk π.1 P := by
  rw [(valF_uP π P hP).1, (valF_uP π P hP).2]
  exact finVal_of_not_dvd π.1 hd

theorem valF_uP_self (π : Prim F) :
    (valF π).v (uP π.1 π.2.2.ne_zero) = 1 ∧ (valF π).r (uP π.1 π.2.2.ne_zero) = 1 := by
  refine ⟨by rw [(valF_uP π _ _).1]; exact (finVal_self π.1).1, ?_⟩
  ext; rw [(valF_uP π _ _).2]; exact (finVal_self π.1).2

theorem finite_prim_dvd (P : F[X]) (hP : P ≠ 0) : {π : Prim F | π.1 ∣ P}.Finite := by
  classical
  refine Set.Finite.subset ((UniqueFactorizationMonoid.normalizedFactors P).toFinset.finite_toSet.preimage
    Subtype.val_injective.injOn) ?_
  intro π hπ
  simp only [Set.mem_ofPred_eq] at hπ
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset]
  obtain ⟨q, hq, hassoc⟩ :=
    UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd hP π.2.2 hπ
  have hq0 : q ≠ 0 := UniqueFactorizationMonoid.ne_zero_of_mem_normalizedFactors hq
  have hqm : q.Monic := by
    have := monic_normalize hq0
    rwa [UniqueFactorizationMonoid.normalize_normalized_factor q hq] at this
  rwa [eq_of_monic_of_associated π.2.1 hqm hassoc]

theorem valF_v_eq_zero (π : Prim F) (f : (RatFunc F)ˣ) (h1 : ¬ π.1 ∣ (f : RatFunc F).num)
    (h2 : ¬ π.1 ∣ (f : RatFunc F).denom) : (valF π).v f = 0 := by
  show (finVal π.1).vp _ - (finVal π.1).vp _ = 0
  rw [(finVal_of_not_dvd π.1 h1).1, (finVal_of_not_dvd π.1 h2).1, sub_self]

variable (p : ℕ)

/-- Only finitely many residues of a class are nonzero. -/
theorem res_finite (h1 : ∀ π : Prim F, of p (-1 : (Kap π)ˣ) = 0) (Y : MilnorK (RatFunc F) p) :
    ∃ s : Set (Prim F), s.Finite ∧ ∀ π ∉ s, res (valF π) (h1 π) Y = 0 := by
  induction Y using induction (p := p) with
  | h_int n => exact ⟨∅, Set.finite_empty, fun π _ => res_intCast _ _ n⟩
  | h_of f =>
    refine ⟨{π | π.1 ∣ (f : RatFunc F).num} ∪ {π | π.1 ∣ (f : RatFunc F).denom},
      (finite_prim_dvd _ (RatFunc.num_ne_zero f.ne_zero)).union
        (finite_prim_dvd _ (RatFunc.denom_ne_zero _)), fun π hπ => ?_⟩
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or] at hπ
    rw [res_of, valF_v_eq_zero π f hπ.1 hπ.2, zero_smul]
  | h_add x y hx hy =>
    obtain ⟨s, hs, hs'⟩ := hx
    obtain ⟨t, ht, ht'⟩ := hy
    refine ⟨s ∪ t, hs.union ht, fun π hπ => ?_⟩
    simp only [Set.mem_union, not_or] at hπ
    rw [res_add, hs' π hπ.1, ht' π hπ.2, add_zero]
  | h_mul x y hx hy =>
    obtain ⟨s, hs, hs'⟩ := hx
    obtain ⟨t, ht, ht'⟩ := hy
    refine ⟨s ∪ t, hs.union ht, fun π hπ => ?_⟩
    simp only [Set.mem_union, not_or] at hπ
    rw [res_mul_of_res_eq_zero _ _ _ _ (ht' π hπ.2), hs' π hπ.1, zero_mul]

theorem res_hasFiniteSupport (h1 : ∀ π : Prim F, of p (-1 : (Kap π)ˣ) = 0)
    {M : Type*} [AddCommGroup M] (N : ∀ π : Prim F, MilnorK (Kap π) p →+ M)
    (Y : MilnorK (RatFunc F) p) :
    Function.HasFiniteSupport (fun π => N π (res (valF π) (h1 π) Y)) := by
  obtain ⟨s, hs, hs'⟩ := res_finite p h1 Y
  refine Set.Finite.subset hs ?_
  intro π hπ
  by_contra hn
  exact hπ (by simp [hs' π hn])

end Places

end OMA.NormRel


/-! Milnor's degree filtration on `K_*(F(t))/p` and its generation lemma. -/

namespace OMA.NormRel

open MilnorK Polynomial

section Filt

variable {F : Type*} [Field F] (p : ℕ)

/-- Classes of nonzero polynomials of degree at most `d`. -/
noncomputable def gens (d : ℕ) : Set (MilnorK (RatFunc F) p) :=
  {x | ∃ (P : F[X]) (hP : P ≠ 0), P.natDegree ≤ d ∧ x = of p (uP P hP)}

/-- The subring generated by classes of polynomials of degree at most `d`. -/
noncomputable def S (d : ℕ) : Subring (MilnorK (RatFunc F) p) := Subring.closure (gens p d)

theorem of_mem_S {d : ℕ} (P : F[X]) (hP : P ≠ 0) (h : P.natDegree ≤ d) :
    of p (uP P hP) ∈ S p d :=
  Subring.subset_closure ⟨P, hP, h, rfl⟩

theorem S_mono {d e : ℕ} (h : d ≤ e) : S (F := F) p d ≤ S p e :=
  Subring.closure_mono (fun _ ⟨P, hP, hd, hx⟩ => ⟨P, hP, hd.trans h, hx⟩)

/-- Constants. -/
noncomputable def bK (b : Fˣ) : (RatFunc F)ˣ := uP (C (b : F)) (C_ne_zero.mpr b.ne_zero)

theorem bK_mem (d : ℕ) (b : Fˣ) : of p (bK b) ∈ S p d :=
  of_mem_S p _ _ (by simp)

/-- Classes of `S d` commute with a class of degree one, up to an element of `S d`. -/
theorem S_comm (d : ℕ) (c : (RatFunc F)ˣ) {z : MilnorK (RatFunc F) p} (hz : z ∈ S p d) :
    ∃ z' ∈ S p d, z * of p c = of p c * z' := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨P, hP, _, rfl⟩ := hx
    refine ⟨-of p (uP P hP), neg_mem (Subring.subset_closure ⟨P, hP, by assumption, rfl⟩), ?_⟩
    rw [of_comm, mul_neg']
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | one => exact ⟨1, one_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    exact ⟨x' + y', add_mem hx' hy', by rw [add_mul, ex, ey, mul_add]⟩
  | neg x _ hx =>
    obtain ⟨x', hx', ex⟩ := hx
    exact ⟨-x', neg_mem hx', by rw [neg_mul', ex, mul_neg']⟩
  | mul x y _ _ hx hy =>
    obtain ⟨x', hx', ex⟩ := hx
    obtain ⟨y', hy', ey⟩ := hy
    exact ⟨x' * y', mul_mem hx' hy', by rw [mul_assoc, ey, ← mul_assoc, ex, mul_assoc]⟩

theorem not_dvd_of_natDegree_lt (π : Prim F) {P : F[X]} (hP : P ≠ 0)
    (h : P.natDegree < π.1.natDegree) : ¬ π.1 ∣ P := by
  intro hd
  exact absurd (natDegree_le_of_dvd hd hP) (by omega)

/-- Classes in `S d` have no residue at primes of degree `> d`. -/
theorem res_S_eq_zero (h1 : ∀ π : Prim F, of p (-1 : (Kap π)ˣ) = 0) (d : ℕ) (π : Prim F)
    (hπ : d < π.1.natDegree) {z : MilnorK (RatFunc F) p} (hz : z ∈ S p d) :
    res (valF π) (h1 π) z = 0 := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨P, hP, hd, rfl⟩ := hx
    rw [res_of, (valF_uP_of_not_dvd π hP (not_dvd_of_natDegree_lt π hP (by omega))).1,
      zero_smul]
  | zero => simpa using res_intCast (valF π) (h1 π) 0
  | one => exact res_one _ _
  | add x y _ _ hx hy => rw [res_add, hx, hy, add_zero]
  | neg x _ hx => rw [res_neg, hx, neg_zero]
  | mul x y _ _ hx hy => rw [res_mul_of_res_eq_zero _ _ _ _ hy, hx, zero_mul]

/-- `{b}{a} = {b}{c} - {a}{c}` when `a + c = b`. -/
theorem key_rel {K : Type*} [Field K] (h1 : of p (-1 : Kˣ) = 0) (a b c : Kˣ)
    (h : (a : K) + c = b) : of p b * of p a = of p b * of p c - of p a * of p c := by
  have hst : of p (a * b⁻¹) * of p (c * b⁻¹) = 0 := by
    apply of_mul_of_eq_zero
    simp only [Units.val_mul, Units.val_inv_eq_inv_val]
    rw [← add_mul, h, mul_inv_cancel₀ b.ne_zero]
  rw [of_mul, of_mul, of_inv, add_mul, mul_add, mul_add, neg_mul', mul_neg', neg_mul', mul_neg',
    neg_neg, of_mul_self p h1 b, add_zero] at hst
  rw [of_comm p b a]
  have : of p a * of p b = of p a * of p c - of p b * of p c := by
    rw [← sub_eq_zero, ← neg_eq_zero, ← hst]; abel
  rw [this]; abel

/-- The generators of the next filtration step modulo `S d`. -/
noncomputable def Tset (d : ℕ) : Set (MilnorK (RatFunc F) p) :=
  {x | ∃ π : Prim F, π.1.natDegree = d + 1 ∧ ∃ z ∈ S p d, x = of p (uP π.1 π.2.2.ne_zero) * z} ∪
    ((S (F := F) p d : Subring (MilnorK (RatFunc F) p)) : Set (MilnorK (RatFunc F) p))

/-- `S d` plus the span of `{π} S d` for primes `π` of degree `d + 1`. -/
noncomputable def T (d : ℕ) : AddSubgroup (MilnorK (RatFunc F) p) := AddSubgroup.closure (Tset p d)

theorem S_le_T (d : ℕ) {x : MilnorK (RatFunc F) p} (hx : x ∈ S p d) : x ∈ T p d :=
  AddSubgroup.subset_closure (Or.inr hx)

theorem piS_mem_T (d : ℕ) (π : Prim F) (hπ : π.1.natDegree = d + 1) {z : MilnorK (RatFunc F) p}
    (hz : z ∈ S p d) : of p (uP π.1 π.2.2.ne_zero) * z ∈ T p d :=
  AddSubgroup.subset_closure (Or.inl ⟨π, hπ, z, hz, rfl⟩)

/-- A polynomial of degree `≤ d + 1` is either a product of lower degree ones, or a constant
times a monic irreducible of degree `d + 1`. -/
theorem gen_cases (d : ℕ) (Q : F[X]) (hQ : Q ≠ 0) (hdeg : Q.natDegree ≤ d + 1) :
    of p (uP Q hQ) ∈ S p d ∨ ∃ (c : (RatFunc F)ˣ) (π : Prim F), of p c ∈ S p d ∧
      π.1.natDegree = d + 1 ∧ of p (uP Q hQ) = of p c + of p (uP π.1 π.2.2.ne_zero) := by
  by_cases hd : Q.natDegree ≤ d
  · exact Or.inl (of_mem_S p Q hQ hd)
  have hd' : Q.natDegree = d + 1 := by omega
  by_cases hirr : Irreducible Q
  · right
    have hlc : Q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hQ
    set π0 := Q * C Q.leadingCoeff⁻¹ with hπ0
    have hmon : π0.Monic := monic_mul_leadingCoeff_inv hQ
    have hirr' : Irreducible π0 :=
      (irreducible_mul_isUnit (isUnit_C.mpr (inv_ne_zero hlc).isUnit)).mpr hirr
    let π : Prim F := ⟨π0, hmon, hirr'⟩
    have hdegπ : π0.natDegree = d + 1 := by
      rw [hπ0, natDegree_mul_C (inv_ne_zero hlc), hd']
    have hQe : Q = C Q.leadingCoeff * π0 := by
      rw [hπ0, mul_comm Q, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]
    refine ⟨uP (C Q.leadingCoeff) (C_ne_zero.mpr hlc), π, of_mem_S p _ _ (by simp), hdegπ, ?_⟩
    rw [← of_mul, ← uP_mul]
    exact congrArg (of p) (uP_congr hQe _ _)
  · left
    have hnu : ¬ IsUnit Q := by
      intro hu
      have := natDegree_eq_zero_of_isUnit hu
      omega
    have : ∃ a b, Q = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
      by_contra hcon
      push Not at hcon
      exact hirr ⟨hnu, fun a b hab => by
        by_contra h'; push Not at h'; exact h'.2 (hcon a b hab h'.1)⟩
    obtain ⟨a, b, hab, ha, hb⟩ := this
    have ha0 : a ≠ 0 := left_ne_zero_of_mul (hab ▸ hQ)
    have hb0 : b ≠ 0 := right_ne_zero_of_mul (hab ▸ hQ)
    have hda : 0 < a.natDegree := by
      by_contra h0; push Not at h0
      exact ha (isUnit_iff_degree_eq_zero.mpr
        (by rw [degree_eq_natDegree ha0]; exact_mod_cast Nat.le_zero.mp h0))
    have hdb : 0 < b.natDegree := by
      by_contra h0; push Not at h0
      exact hb (isUnit_iff_degree_eq_zero.mpr
        (by rw [degree_eq_natDegree hb0]; exact_mod_cast Nat.le_zero.mp h0))
    have hsum : a.natDegree + b.natDegree = d + 1 := by
      rw [← hd', hab, natDegree_mul ha0 hb0]
    rw [show uP Q hQ = uP a ha0 * uP b hb0 from by rw [← uP_mul]; exact uP_congr hab _ _,
      of_mul]
    exact add_mem (of_mem_S p a ha0 (by omega)) (of_mem_S p b hb0 (by omega))

theorem sub_prim (d : ℕ) (π π' : Prim F) (hπ : π.1.natDegree = d + 1)
    (hπ' : π'.1.natDegree = d + 1) (hne : π' ≠ π) :
    π'.1 - π.1 ≠ 0 ∧ (π'.1 - π.1).natDegree ≤ d := by
  have h0 : π'.1 - π.1 ≠ 0 := by
    intro h; apply hne; exact Subtype.ext (sub_eq_zero.mp h)
  refine ⟨h0, ?_⟩
  have hπ'0 : π'.1 ≠ 0 := π'.2.2.ne_zero
  have hlt := degree_sub_lt_left (p := π'.1) (q := π.1)
    (by rw [degree_eq_natDegree hπ'0, degree_eq_natDegree π.2.2.ne_zero, hπ, hπ'])
    hπ'0 (by rw [π'.2.1.leadingCoeff, π.2.1.leadingCoeff])
  have := natDegree_lt_natDegree h0 hlt
  omega

theorem T_mul_gen (h1 : of p (-1 : (RatFunc F)ˣ) = 0) (d : ℕ) (Q : F[X]) (hQ : Q ≠ 0)
    (hdeg : Q.natDegree ≤ d + 1) {y : MilnorK (RatFunc F) p} (hy : y ∈ T p d) :
    of p (uP Q hQ) * y ∈ T p d := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    rcases hy with ⟨π, hπ, z, hz, rfl⟩ | hy
    · rcases gen_cases p d Q hQ hdeg with hS | ⟨c, π', hc, hπ', e⟩
      · rw [← mul_assoc, of_comm, neg_mul', mul_assoc]
        exact neg_mem (piS_mem_T p d π hπ (mul_mem hS hz))
      · rw [e, add_mul, ← mul_assoc, of_comm p c, neg_mul', mul_assoc]
        refine add_mem (neg_mem (piS_mem_T p d π hπ (mul_mem hc hz))) ?_
        by_cases hne : π' = π
        · subst hne
          rw [← mul_assoc, of_mul_self p h1, zero_mul]
          exact zero_mem _
        · obtain ⟨hr0, hrd⟩ := sub_prim d π π' hπ hπ' hne
          have kr := key_rel p h1 (uP π.1 π.2.2.ne_zero) (uP π'.1 π'.2.2.ne_zero)
            (uP (π'.1 - π.1) hr0) (by simp [uP_val])
          rw [← mul_assoc, kr, sub_mul, mul_assoc, mul_assoc]
          exact sub_mem (piS_mem_T p d π' hπ' (mul_mem (of_mem_S p _ _ hrd) hz))
            (piS_mem_T p d π hπ (mul_mem (of_mem_S p _ _ hrd) hz))
    · rcases gen_cases p d Q hQ hdeg with hS | ⟨c, π', hc, hπ', e⟩
      · exact S_le_T p d (mul_mem hS hy)
      · rw [e, add_mul]
        exact add_mem (S_le_T p d (mul_mem hc hy)) (piS_mem_T p d π' hπ' hy)
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg']; exact neg_mem hx

/-- Milnor's generation lemma: `S (d + 1) ⊆ S d + Σ {π} S d`. -/
theorem S_succ_le_T (h1 : of p (-1 : (RatFunc F)ˣ) = 0) (d : ℕ) {x : MilnorK (RatFunc F) p}
    (hx : x ∈ S p (d + 1)) : x ∈ T p d := by
  rw [S, Subring.mem_closure_iff] at hx
  refine (AddSubgroup.closure_le (T p d)).mpr ?_ hx
  intro y hy
  induction hy using Submonoid.closure_induction_left with
  | one => exact S_le_T p d (one_mem _)
  | mul_left x hx y _ hy =>
    obtain ⟨Q, hQ, hdeg, rfl⟩ := hx
    exact T_mul_gen p h1 d Q hQ hdeg hy

end Filt

end OMA.NormRel


/-! The transfer for one prime, from a functional vanishing on the lower filtration step. -/

namespace OMA.NormRel

open MilnorK Polynomial

section Lift

variable {F : Type*} [Field F]

theorem prim_natDegree_pos (π : Prim F) : 0 < π.1.natDegree :=
  natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible π.2.2)

theorem prim_ne_one (π : Prim F) : π.1 ≠ 1 := fun h => π.2.2.not_isUnit (h ▸ isUnit_one)

/-- The canonical lift of a residue class: its representative of degree `< deg π`. -/
noncomputable def liftP (π : Prim F) (u : Kap π) : F[X] := AdjoinRoot.modByMonicHom π.2.1 u

theorem mk_liftP (π : Prim F) (u : Kap π) : AdjoinRoot.mk π.1 (liftP π u) = u :=
  AdjoinRoot.mk_leftInverse π.2.1 u

theorem liftP_add (π : Prim F) (u v : Kap π) : liftP π (u + v) = liftP π u + liftP π v :=
  map_add _ u v

theorem liftP_mk (π : Prim F) (P : F[X]) : liftP π (AdjoinRoot.mk π.1 P) = P %ₘ π.1 :=
  AdjoinRoot.modByMonicHom_mk π.2.1 P

theorem natDegree_liftP_lt (π : Prim F) (u : Kap π) :
    (liftP π u).natDegree < π.1.natDegree := by
  obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective u
  rw [liftP_mk]; exact natDegree_modByMonic_lt P π.2.1 (prim_ne_one π)

theorem liftP_eq (π : Prim F) {P : F[X]} (hP : P.natDegree < π.1.natDegree) :
    liftP π (AdjoinRoot.mk π.1 P) = P := by
  rw [liftP_mk, modByMonic_eq_self_iff π.2.1]
  exact degree_lt_degree hP

theorem liftP_one (π : Prim F) : liftP π 1 = 1 := by
  have := liftP_eq π (P := 1) (by rw [natDegree_one]; exact prim_natDegree_pos π)
  rwa [map_one] at this

theorem liftP_ne_zero (π : Prim F) (u : (Kap π)ˣ) : liftP π (u : Kap π) ≠ 0 := by
  intro h; apply u.ne_zero; rw [← mk_liftP π u, h, map_zero]

/-- The image of a constant in a residue field. -/
noncomputable def bbar (π : Prim F) (b : Fˣ) : (Kap π)ˣ :=
  Units.map (algebraMap F (Kap π)).toMonoidHom b

theorem bbar_val (π : Prim F) (b : Fˣ) :
    ((bbar π b : (Kap π)ˣ) : Kap π) = AdjoinRoot.mk π.1 (C (b : F)) := by
  simp [bbar, AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq]

theorem valF_bK (π : Prim F) (b : Fˣ) : (valF π).v (bK b) = 0 ∧ (valF π).r (bK b) = bbar π b := by
  have hd : ¬ π.1 ∣ C (b : F) := not_dvd_of_natDegree_lt π (C_ne_zero.mpr b.ne_zero)
    (by rw [natDegree_C]; exact prim_natDegree_pos π)
  obtain ⟨h1, h2⟩ := valF_uP_of_not_dvd π (C_ne_zero.mpr b.ne_zero) hd
  exact ⟨h1, Units.ext (by rw [bbar_val]; exact h2)⟩

theorem valI_bK (b : Fˣ) : (valI (F := F)).v (bK b) = 0 ∧ (valI (F := F)).r (bK b) = b := by
  obtain ⟨h1, h2⟩ := valI_uP (C (b : F)) (C_ne_zero.mpr b.ne_zero)
  exact ⟨by rw [show bK b = uP (C (b : F)) (C_ne_zero.mpr b.ne_zero) from rfl, h1]; simp,
    Units.ext (by rw [show bK b = uP (C (b : F)) (C_ne_zero.mpr b.ne_zero) from rfl, h2]; simp)⟩

end Lift

section TC

variable {F : Type*} [Field F] (p : ℕ)

/-- The class of the canonical lift of a unit of a residue field. -/
noncomputable def ell (π : Prim F) (u : (Kap π)ˣ) : MilnorK (RatFunc F) p :=
  of p (uP (liftP π u) (liftP_ne_zero π u))

theorem ell_mem (π : Prim F) (d : ℕ) (hπ : π.1.natDegree = d + 1) (u : (Kap π)ˣ) :
    ell p π u ∈ S p d :=
  of_mem_S p _ _ (by have := natDegree_liftP_lt π u; omega)

theorem ell_st (π : Prim F) (u v : (Kap π)ˣ) (h : (u : Kap π) + v = 1) :
    ell p π u * ell p π v = 0 := by
  apply of_mul_of_eq_zero
  have : liftP π u + liftP π v = 1 := by rw [← liftP_add, h, liftP_one]
  simp only [uP_val, ← map_add, this, map_one]

theorem ell_bbar (π : Prim F) (b : Fˣ) : ell p π (bbar π b) = of p (bK b) := by
  have : liftP π (bbar π b : Kap π) = C (b : F) := by
    rw [bbar_val, liftP_eq π (by rw [natDegree_C]; exact prim_natDegree_pos π)]
  exact congrArg (of p) (uP_congr this _ _)

theorem ell_mk (π : Prim F) (u : (Kap π)ˣ) {P : F[X]} (hP : P ≠ 0)
    (hd : P.natDegree < π.1.natDegree) (hu : (u : Kap π) = AdjoinRoot.mk π.1 P) :
    ell p π u = of p (uP P hP) := by
  have : liftP π (u : Kap π) = P := by rw [hu, liftP_eq π hd]
  exact congrArg (of p) (uP_congr this _ _)

/-- The defect of multiplicativity of lifts, polynomial form. -/
theorem defect_mem (π : Prim F) (d : ℕ) (hπ : π.1.natDegree = d + 1) (A B Cc s : F[X])
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : Cc ≠ 0) (hAd : A.natDegree ≤ d) (hBd : B.natDegree ≤ d)
    (hCd : Cc.natDegree ≤ d) (hsd : s.natDegree ≤ d) (hid : Cc + π.1 * s = A * B) :
    of p (uP π.1 π.2.2.ne_zero) * of p (uP A hA0 * uP B hB0 * (uP Cc hC0)⁻¹) ∈ S p d := by
  have hcS : of p (uP A hA0 * uP B hB0 * (uP Cc hC0)⁻¹) ∈ S p d := by
    rw [of_mul, of_mul, of_inv]
    exact add_mem (add_mem (of_mem_S p A hA0 hAd) (of_mem_S p B hB0 hBd))
      (neg_mem (of_mem_S p Cc hC0 hCd))
  by_cases hs0 : s = 0
  · rw [hs0, mul_zero, add_zero] at hid
    have hc1 : uP A hA0 * uP B hB0 * (uP Cc hC0)⁻¹ = 1 := by
      rw [← uP_mul, uP_congr hid.symm (mul_ne_zero hA0 hB0) hC0, mul_inv_cancel]
    rw [hc1, of_one, mul_zero]; exact zero_mem _
  have hπ0 : π.1 ≠ 0 := π.2.2.ne_zero
  have hst : of p (uP A hA0 * uP B hB0 * (uP Cc hC0)⁻¹)⁻¹ *
      of p (uP s hs0 * uP π.1 hπ0 * (uP A hA0 * uP B hB0)⁻¹) = 0 := by
    apply of_mul_of_eq_zero
    have hid' := congrArg (algebraMap F[X] (RatFunc F)) hid
    rw [map_add, map_mul, map_mul] at hid'
    simp only [mul_inv_rev, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val, uP_val]
    have ha : algebraMap F[X] (RatFunc F) A ≠ 0 :=
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective F)).mpr hA0
    have hb : algebraMap F[X] (RatFunc F) B ≠ 0 :=
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective F)).mpr hB0
    field_simp
    linear_combination hid'
  set c := uP A hA0 * uP B hB0 * (uP Cc hC0)⁻¹ with hc
  rw [of_mul, of_mul, mul_add, mul_add] at hst
  have hkey : of p c⁻¹ * of p (uP π.1 hπ0) =
      -(of p c⁻¹ * of p (uP s hs0) + of p c⁻¹ * of p (uP A hA0 * uP B hB0)⁻¹) := by
    rw [eq_neg_iff_add_eq_zero, ← hst]; abel
  have hcinv : of p c⁻¹ ∈ S p d := by rw [of_inv]; exact neg_mem hcS
  have hABinv : of p (uP A hA0 * uP B hB0)⁻¹ ∈ S p d := by
    rw [of_inv, of_mul]
    exact neg_mem (add_mem (of_mem_S p A hA0 hAd) (of_mem_S p B hB0 hBd))
  have e : of p (uP π.1 π.2.2.ne_zero) * of p c = of p c⁻¹ * of p (uP π.1 hπ0) := by
    rw [of_comm p (uP π.1 _) c, of_inv, neg_mul']
  rw [e, hkey]
  exact neg_mem (add_mem (mul_mem hcinv (of_mem_S p s hs0 hsd)) (mul_mem hcinv hABinv))

theorem liftP_mul (π : Prim F) (u v : Kap π) :
    liftP π (u * v) = (liftP π u * liftP π v) %ₘ π.1 := by
  rw [← liftP_mk, map_mul, mk_liftP, mk_liftP]

/-- The defect of multiplicativity of the lift is harmless. -/
theorem ell_mul (π : Prim F) (d : ℕ) (hπ : π.1.natDegree = d + 1) (u v : (Kap π)ˣ) :
    ∃ c : (RatFunc F)ˣ, of p c ∈ S p d ∧ of p (uP π.1 π.2.2.ne_zero) * of p c ∈ S p d ∧
      ell p π u + ell p π v = ell p π (u * v) + of p c := by
  have hAd : (liftP π (u : Kap π)).natDegree ≤ d := by
    have := natDegree_liftP_lt π (u : Kap π); omega
  have hBd : (liftP π (v : Kap π)).natDegree ≤ d := by
    have := natDegree_liftP_lt π (v : Kap π); omega
  have hCd : (liftP π ((u * v : (Kap π)ˣ) : Kap π)).natDegree ≤ d := by
    have := natDegree_liftP_lt π ((u * v : (Kap π)ˣ) : Kap π); omega
  have hid : liftP π ((u * v : (Kap π)ˣ) : Kap π) +
      π.1 * ((liftP π (u : Kap π) * liftP π (v : Kap π)) /ₘ π.1) =
      liftP π (u : Kap π) * liftP π (v : Kap π) := by
    rw [Units.val_mul, liftP_mul]; exact modByMonic_add_div _ _
  have hsd : ((liftP π (u : Kap π) * liftP π (v : Kap π)) /ₘ π.1).natDegree ≤ d := by
    rw [natDegree_divByMonic _ π.2.1, natDegree_mul (liftP_ne_zero π u) (liftP_ne_zero π v), hπ]
    omega
  refine ⟨uP _ (liftP_ne_zero π u) * uP _ (liftP_ne_zero π v) * (uP _ (liftP_ne_zero π (u * v)))⁻¹,
    ?_, defect_mem p π d hπ _ _ _ _ _ _ _ hAd hBd hCd hsd hid, ?_⟩
  · rw [of_mul, of_mul, of_inv]
    exact add_mem (add_mem (ell_mem p π d hπ u) (ell_mem p π d hπ v))
      (neg_mem (ell_mem p π d hπ (u * v)))
  · rw [of_mul, of_mul, of_inv]
    show ell p π u + ell p π v = ell p π (u * v) + (ell p π u + ell p π v + -ell p π (u * v))
    abel

end TC

end OMA.NormRel


/-! The transfer for one prime (continued). -/

namespace OMA.NormRel

open MilnorK Polynomial

section TC

variable {F : Type*} [Field F] (p : ℕ)

variable (π : Prim F) (d : ℕ)

/-- Functionals on `S d` adapted to `π`. -/
noncomputable def Gsub : AddSubgroup (↥(S (F := F) p d) →+ MilnorK F p) where
  carrier := {φ | (∀ (c : (RatFunc F)ˣ) (hc : of p c ∈ S p d),
      of p (uP π.1 π.2.2.ne_zero) * of p c ∈ S p d → ∀ z : S p d, φ (z * ⟨of p c, hc⟩) = 0) ∧
      (∀ (b : Fˣ) (z : S p d), φ (⟨of p (bK b), bK_mem p d b⟩ * z) = of p b * φ z)}
  add_mem' := by
    rintro φ ψ ⟨hφ1, hφ2⟩ ⟨hψ1, hψ2⟩
    refine ⟨fun c hc hπc z => ?_, fun b z => ?_⟩
    · rw [AddMonoidHom.add_apply, hφ1 c hc hπc z, hψ1 c hc hπc z, add_zero]
    · rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, hφ2, hψ2, mul_add]
  zero_mem' := ⟨fun _ _ _ _ => rfl, fun _ _ => by simp⟩
  neg_mem' := by
    rintro φ ⟨hφ1, hφ2⟩
    refine ⟨fun c hc hπc z => ?_, fun b z => ?_⟩
    · rw [AddMonoidHom.neg_apply, hφ1 c hc hπc z, neg_zero]
    · rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, hφ2, mul_neg']

variable {d}

/-- The action of a unit of `κ(π)` on adapted functionals: precompose with right
multiplication by the lift. -/
noncomputable def actG (hπ : π.1.natDegree = d + 1) (u : (Kap π)ˣ) :
    AddMonoid.End (Gsub p π d) where
  toFun φ := ⟨φ.1.comp (AddMonoidHom.mulRight ⟨ell p π u, ell_mem p π d hπ u⟩), by
    obtain ⟨h1, h2⟩ := φ.2
    refine ⟨fun c hc hπc z => ?_, fun b z => ?_⟩
    · show φ.1 (z * ⟨of p c, hc⟩ * ⟨ell p π u, ell_mem p π d hπ u⟩) = 0
      have e : z * ⟨of p c, hc⟩ * ⟨ell p π u, ell_mem p π d hπ u⟩ =
          -(z * ⟨ell p π u, ell_mem p π d hπ u⟩ * ⟨of p c, hc⟩) := by
        apply Subtype.ext
        show (z : MilnorK (RatFunc F) p) * of p c * ell p π u =
          -((z : MilnorK (RatFunc F) p) * ell p π u * of p c)
        rw [mul_assoc, mul_assoc, ell, of_comm p c, mul_neg']
      rw [e, map_neg, h1 c hc hπc, neg_zero]
    · show φ.1 (⟨of p (bK b), bK_mem p d b⟩ * z * ⟨ell p π u, ell_mem p π d hπ u⟩) =
        of p b * φ.1 (z * ⟨ell p π u, ell_mem p π d hπ u⟩)
      rw [mul_assoc, h2]⟩
  map_zero' := rfl
  map_add' _ _ := rfl

theorem actG_apply (hπ : π.1.natDegree = d + 1) (u : (Kap π)ˣ) (φ : Gsub p π d)
    (z : S p d) : (actG p π hπ u φ).1 z = φ.1 (z * ⟨ell p π u, ell_mem p π d hπ u⟩) := rfl

theorem actG_mul (hπ : π.1.natDegree = d + 1) (u v : (Kap π)ˣ) :
    actG p π hπ (u * v) = actG p π hπ u + actG p π hπ v := by
  obtain ⟨c, hc, hπc, e⟩ := ell_mul p π d hπ u v
  ext φ z
  show φ.1 (z * ⟨ell p π (u * v), _⟩) =
    φ.1 (z * ⟨ell p π u, _⟩) + φ.1 (z * ⟨ell p π v, _⟩)
  have e' : (⟨ell p π u, ell_mem p π d hπ u⟩ : S p d) + ⟨ell p π v, ell_mem p π d hπ v⟩ =
      ⟨ell p π (u * v), ell_mem p π d hπ (u * v)⟩ + ⟨of p c, hc⟩ := Subtype.ext e
  rw [← map_add, ← mul_add, e', mul_add, map_add, φ.2.1 c hc hπc z, add_zero]

/-- The generator map into endomorphisms of the adapted functionals. -/
noncomputable def genG (hπ : π.1.natDegree = d + 1) :
    Additive (Kap π)ˣ →+ AddMonoid.End (Gsub p π d) :=
  AddMonoidHom.mk' (fun f => actG p π hπ f.toMul) (fun _ _ => actG_mul p π hπ _ _)

theorem genG_st (hπ : π.1.natDegree = d + 1) (u v : (Kap π)ˣ) (h : (u : Kap π) + v = 1) :
    genG p π hπ (Additive.ofMul u) * genG p π hπ (Additive.ofMul v) = 0 := by
  ext φ z
  show φ.1 (z * ⟨ell p π u, _⟩ * ⟨ell p π v, _⟩) = 0
  have e : z * ⟨ell p π u, ell_mem p π d hπ u⟩ * ⟨ell p π v, ell_mem p π d hπ v⟩ = 0 := by
    apply Subtype.ext
    show (z : MilnorK (RatFunc F) p) * ell p π u * ell p π v = 0
    rw [mul_assoc, ell_st p π u v h, mul_zero]
  rw [e, map_zero]

theorem genG_nat : ((p : AddMonoid.End (Gsub p π d))) = 0 := by
  ext φ z
  show p • φ.1 z = 0
  exact nsmul_p p _

/-- The ring map `K_*(κ(π))/p → End(G)`. -/
noncomputable def HG (hπ : π.1.natDegree = d + 1) : MilnorK (Kap π) p →+* AddMonoid.End (Gsub p π d) :=
  liftK (R := AddMonoid.End (Gsub p π d)) p (genG p π hπ) (genG_st p π hπ) (genG_nat p π)

theorem HG_of (hπ : π.1.natDegree = d + 1) (u : (Kap π)ˣ) :
    HG p π hπ (of p u) = actG p π hπ u := by
  rw [HG, liftK_of]; rfl

theorem HG_add_apply (hπ : π.1.natDegree = d + 1) (x y : MilnorK (Kap π) p) (ψ : Gsub p π d)
    (w : S p d) : ((HG p π hπ (x + y)) ψ).1 w = ((HG p π hπ x) ψ).1 w + ((HG p π hπ y) ψ).1 w := by
  rw [map_add]; rfl

theorem HG_neg_apply (hπ : π.1.natDegree = d + 1) (x : MilnorK (Kap π) p) (ψ : Gsub p π d)
    (w : S p d) : ((HG p π hπ (-x)) ψ).1 w = -((HG p π hπ x) ψ).1 w := by
  rw [map_neg]; rfl

theorem HG_mul_apply (hπ : π.1.natDegree = d + 1) (x y : MilnorK (Kap π) p) (ψ : Gsub p π d)
    (w : S p d) : ((HG p π hπ (x * y)) ψ).1 w = ((HG p π hπ x) ((HG p π hπ y) ψ)).1 w := by
  rw [map_mul]; rfl

theorem HG_one_apply (hπ : π.1.natDegree = d + 1) (ψ : Gsub p π d) (w : S p d) :
    ((HG p π hπ 1) ψ).1 w = ψ.1 w := by
  rw [map_one]; rfl

theorem HG_zero_apply (hπ : π.1.natDegree = d + 1) (ψ : Gsub p π d) (w : S p d) :
    ((HG p π hπ 0) ψ).1 w = 0 := by
  rw [map_zero]; rfl

variable (Φ : MilnorK (RatFunc F) p →+ MilnorK F p) (hΦ0 : ∀ Y ∈ S p d, Φ Y = 0)
  (hΦb : ∀ (b : Fˣ) Y, Φ (of p (bK b) * Y) = -(of p b * Φ Y))

/-- The functional `z ↦ Φ({π} z)`. -/
noncomputable def phi0 : Gsub p π d :=
  ⟨Φ.comp ((AddMonoidHom.mulLeft (of p (uP π.1 π.2.2.ne_zero))).comp
      (S p d).subtype.toAddMonoidHom), by
    refine ⟨fun c hc hπc z => ?_, fun b z => ?_⟩
    · show Φ (of p (uP π.1 π.2.2.ne_zero) * ((z : MilnorK (RatFunc F) p) * of p c)) = 0
      obtain ⟨z', hz', e⟩ := S_comm p d c z.2
      rw [e, ← mul_assoc]
      exact hΦ0 _ (mul_mem hπc hz')
    · show Φ (of p (uP π.1 π.2.2.ne_zero) * (of p (bK b) * (z : MilnorK (RatFunc F) p))) =
        of p b * Φ (of p (uP π.1 π.2.2.ne_zero) * (z : MilnorK (RatFunc F) p))
      rw [← mul_assoc, of_comm p (uP π.1 _) (bK b), neg_mul', mul_assoc, map_neg, hΦb, neg_neg]⟩

theorem phi0_apply (z : S p d) : (phi0 p π Φ hΦ0 hΦb).1 z =
    Φ (of p (uP π.1 π.2.2.ne_zero) * (z : MilnorK (RatFunc F) p)) := rfl

/-- The transfer attached to `Φ`. -/
noncomputable def trOf (hπ : π.1.natDegree = d + 1) : MilnorK (Kap π) p →+ MilnorK F p :=
  AddMonoidHom.mk' (fun x => ((HG p π hπ x) (phi0 p π Φ hΦ0 hΦb)).1 1)
    (fun x y => by rw [map_add]; rfl)

theorem trOf_apply (hπ : π.1.natDegree = d + 1) (x : MilnorK (Kap π) p) :
    trOf p π Φ hΦ0 hΦb hπ x = ((HG p π hπ x) (phi0 p π Φ hΦ0 hΦb)).1 1 := rfl

theorem trOf_one (hπ : π.1.natDegree = d + 1) :
    trOf p π Φ hΦ0 hΦb hπ 1 = Φ (of p (uP π.1 π.2.2.ne_zero)) := by
  rw [trOf_apply, (HG p π hπ).map_one]
  show Φ (of p (uP π.1 π.2.2.ne_zero) * 1) = _
  rw [mul_one]

theorem trOf_of (hπ : π.1.natDegree = d + 1) (u : (Kap π)ˣ) :
    trOf p π Φ hΦ0 hΦb hπ (of p u) = Φ (of p (uP π.1 π.2.2.ne_zero) * ell p π u) := by
  rw [trOf_apply, HG_of, actG_apply, phi0_apply]
  congr 2
  show (1 : MilnorK (RatFunc F) p) * ell p π u = ell p π u
  rw [one_mul]

set_option maxHeartbeats 1000000 in
theorem trOf_bbar (hπ : π.1.natDegree = d + 1) (b : Fˣ) (x : MilnorK (Kap π) p) :
    trOf p π Φ hΦ0 hΦb hπ (of p (bbar π b) * x) = of p b * trOf p π Φ hΦ0 hΦb hπ x := by
  have e : (1 : S p d) * ⟨ell p π (bbar π b), ell_mem p π d hπ (bbar π b)⟩ =
      ⟨of p (bK b), bK_mem p d b⟩ * 1 := by
    apply Subtype.ext
    show (1 : MilnorK (RatFunc F) p) * ell p π (bbar π b) = of p (bK b) * 1
    rw [one_mul, mul_one, ell_bbar]
  rw [trOf_apply, trOf_apply, HG_mul_apply, HG_of, actG_apply, e]
  exact (HG p π hπ x (phi0 p π Φ hΦ0 hΦb)).2.2 b 1

variable (h1 : ∀ π : Prim F, of p (-1 : (Kap π)ˣ) = 0)

set_option maxHeartbeats 1000000 in
theorem HG_spec (hπ : π.1.natDegree = d + 1) {z : MilnorK (RatFunc F) p} (hz : z ∈ S p d)
    (ψ : Gsub p π d) (w : S p d) :
    ((HG p π hπ (spec (valF π) (h1 π) z)) ψ).1 w = ψ.1 (w * ⟨z, hz⟩) := by
  induction hz using Subring.closure_induction generalizing ψ w with
  | mem x hx =>
    obtain ⟨P, hP, hd, rfl⟩ := hx
    rw [spec_of, HG_of, actG_apply]
    have hnd : ¬ π.1 ∣ P := not_dvd_of_natDegree_lt π hP (by omega)
    have hr := (valF_uP_of_not_dvd π hP hnd).2
    have e : (⟨ell p π ((valF π).r (uP P hP)), ell_mem p π d hπ _⟩ : S p d) =
        ⟨of p (uP P hP), Subring.subset_closure ⟨P, hP, hd, rfl⟩⟩ :=
      Subtype.ext (ell_mk p π _ hP (by omega) hr)
    rw [e]
  | zero =>
    have : spec (valF π) (h1 π) (0 : MilnorK (RatFunc F) p) = 0 := by
      simpa using spec_intCast (valF π) (h1 π) 0
    rw [this, HG_zero_apply]
    have e : w * (⟨0, zero_mem _⟩ : S p d) = 0 := mul_zero w
    rw [e, map_zero]
  | one =>
    rw [spec_one, HG_one_apply]
    have e : w * (⟨1, one_mem _⟩ : S p d) = w := mul_one w
    rw [e]
  | add x y hx hy ihx ihy =>
    rw [spec_add, HG_add_apply, ihx, ihy, ← map_add]
    congr 1
    rw [← mul_add]
    rfl
  | neg x hx ihx =>
    rw [spec_neg, HG_neg_apply, ihx, ← map_neg]
    congr 1
    rw [← mul_neg]
    rfl
  | mul x y hx hy ihx ihy =>
    rw [spec_mul_of_res_eq_zero _ _ _ _ (res_S_eq_zero p h1 d π (by omega) hy), HG_mul_apply,
      ihx, ihy]
    congr 1
    rw [mul_assoc]
    rfl

theorem trOf_spec (hπ : π.1.natDegree = d + 1) {z : MilnorK (RatFunc F) p} (hz : z ∈ S p d) :
    trOf p π Φ hΦ0 hΦb hπ (spec (valF π) (h1 π) z) = Φ (of p (uP π.1 π.2.2.ne_zero) * z) := by
  rw [trOf_apply, HG_spec p π h1 hπ hz, phi0_apply]
  show Φ (of p (uP π.1 π.2.2.ne_zero) * (1 * z)) = _
  rw [one_mul]

end TC

end OMA.NormRel


/-! The transfer family by induction on the degree, with Weil reciprocity, the projection
formula and compatibility with the norm in degree one. -/

namespace OMA.NormRel

open MilnorK Polynomial

section Induction

variable {F : Type*} [Field F] (p : ℕ) (h1 : ∀ π : Prim F, of p (-1 : (Kap π)ˣ) = 0)
  (hF : of p (-1 : Fˣ) = 0)

/-- Families of transfers. -/
abbrev Fam (F : Type*) [Field F] (p : ℕ) := ∀ π : Prim F, MilnorK (Kap π) p →+ MilnorK F p

/-- The residue at a finite prime. -/
noncomputable def resF (π : Prim F) (Y : MilnorK (RatFunc F) p) : MilnorK (Kap π) p :=
  res (valF π) (h1 π) Y

/-- The residue at `∞`. -/
noncomputable def resI (Y : MilnorK (RatFunc F) p) : MilnorK F p := res valI hF Y

/-- The norm on units. -/
noncomputable def normU (π : Prim F) (u : (Kap π)ˣ) : Fˣ :=
  Units.map (Algebra.norm F : Kap π →* F) u

/-- The Weil sum. -/
noncomputable def Psi (N : Fam F p) (Y : MilnorK (RatFunc F) p) : MilnorK F p :=
  resI p hF Y + ∑ᶠ π, N π (resF p h1 π Y)

def PropP (N : Fam F p) (d : ℕ) : Prop :=
  ∀ π : Prim F, π.1.natDegree ≤ d → ∀ (b : Fˣ) (x : MilnorK (Kap π) p),
    N π (of p (bbar π b) * x) = of p b * N π x

def PropC (N : Fam F p) (d : ℕ) : Prop :=
  ∀ π : Prim F, π.1.natDegree ≤ d → ∀ u : (Kap π)ˣ, N π (of p u) = of p (normU π u)

def PropW (N : Fam F p) (d : ℕ) : Prop := ∀ Y ∈ S p d, Psi p h1 hF N Y = 0

theorem prim_not_dvd (π π' : Prim F) (h : π' ≠ π) : ¬ π'.1 ∣ π.1 := by
  intro hd
  exact h (Subtype.ext (eq_of_monic_of_associated π'.2.1 π.2.1
    (π'.2.2.associated_of_dvd π.2.2 hd)))

theorem resF_add (π : Prim F) (Y Z : MilnorK (RatFunc F) p) :
    resF p h1 π (Y + Z) = resF p h1 π Y + resF p h1 π Z := res_add _ _ _ _

theorem resI_add (Y Z : MilnorK (RatFunc F) p) :
    resI p hF (Y + Z) = resI p hF Y + resI p hF Z := res_add _ _ _ _

theorem fin_supp (N : Fam F p) (Y : MilnorK (RatFunc F) p) :
    Function.HasFiniteSupport (fun π => N π (resF p h1 π Y)) :=
  res_hasFiniteSupport p h1 N Y

theorem fin_supp_of {f : Prim F → MilnorK F p} (N : Fam F p) (Y : MilnorK (RatFunc F) p)
    (h : ∀ π, N π (resF p h1 π Y) = 0 → f π = 0) : Function.HasFiniteSupport f := by
  refine Set.Finite.subset (fin_supp p h1 N Y) ?_
  intro π hπ hn
  exact hπ (h π hn)

theorem Psi_add (N : Fam F p) (Y Z : MilnorK (RatFunc F) p) :
    Psi p h1 hF N (Y + Z) = Psi p h1 hF N Y + Psi p h1 hF N Z := by
  simp only [Psi, resI_add, resF_add, map_add]
  rw [finsum_add_distrib (fin_supp p h1 N Y) (fin_supp p h1 N Z)]
  abel

theorem Psi_zero (N : Fam F p) : Psi p h1 hF N 0 = 0 := by
  have := Psi_add p h1 hF N 0 0
  rw [add_zero] at this
  have h2 : Psi p h1 hF N 0 + Psi p h1 hF N 0 - Psi p h1 hF N 0 = Psi p h1 hF N 0 := by abel
  rw [← this, sub_self] at h2
  exact h2.symm

theorem Psi_neg (N : Fam F p) (Y : MilnorK (RatFunc F) p) :
    Psi p h1 hF N (-Y) = -Psi p h1 hF N Y := by
  have := Psi_add p h1 hF N (-Y) Y
  rw [neg_add_cancel, Psi_zero] at this
  exact eq_neg_of_add_eq_zero_left this.symm

/-- Residues at `∞` of `S 0` vanish. -/
theorem resI_S0 {z : MilnorK (RatFunc F) p} (hz : z ∈ S p 0) : resI p hF z = 0 := by
  induction hz using Subring.closure_induction with
  | mem x hx =>
    obtain ⟨P, hP, hd, rfl⟩ := hx
    simp only [resI]
    rw [res_of, (valI_uP P hP).1, Nat.le_zero.mp hd]; simp
  | zero => simpa [resI] using res_intCast (valI (F := F)) hF 0
  | one => exact res_one _ _
  | add x y _ _ hx hy => simp only [resI] at *; rw [res_add, hx, hy, add_zero]
  | neg x _ hx => simp only [resI] at *; rw [res_neg, hx, neg_zero]
  | mul x y _ _ hx hy => simp only [resI] at *; rw [res_mul_of_res_eq_zero _ _ _ _ hy, hx, zero_mul]

theorem base : ∃ N : Fam F p, PropP p N 0 ∧ PropC p N 0 ∧ PropW p h1 hF N 0 := by
  refine ⟨fun _ => 0, fun π hπ => absurd hπ (by have := prim_natDegree_pos π; omega),
    fun π hπ => absurd hπ (by have := prim_natDegree_pos π; omega), fun Y hY => ?_⟩
  simp only [Psi, AddMonoidHom.zero_apply, finsum_zero, add_zero]
  exact resI_S0 p hF hY

/-! ### The step -/

variable (N : Fam F p) (d : ℕ)

/-- The lower part of the Weil sum. -/
noncomputable def fD (Y : MilnorK (RatFunc F) p) (π : Prim F) : MilnorK F p :=
  if π.1.natDegree ≤ d then N π (resF p h1 π Y) else 0

theorem fD_fin (Y : MilnorK (RatFunc F) p) : Function.HasFiniteSupport (fD p h1 N d Y) :=
  fin_supp_of p h1 N Y (fun π h => by simp only [fD]; split_ifs <;> simp [h])

theorem fD_add (Y Z : MilnorK (RatFunc F) p) (π : Prim F) :
    fD p h1 N d (Y + Z) π = fD p h1 N d Y π + fD p h1 N d Z π := by
  simp only [fD]; split_ifs <;> simp [resF_add, map_add]

/-- The functional defining the new transfers. -/
noncomputable def PhiD : MilnorK (RatFunc F) p →+ MilnorK F p :=
  AddMonoidHom.mk' (fun Y => -(resI p hF Y) - ∑ᶠ π, fD p h1 N d Y π) (by
    intro Y Z
    simp only [resI_add]
    rw [show (fun π => fD p h1 N d (Y + Z) π) = fun π => fD p h1 N d Y π + fD p h1 N d Z π from
      funext (fD_add p h1 N d Y Z), finsum_add_distrib (fD_fin p h1 N d Y) (fD_fin p h1 N d Z)]
    abel)

theorem PhiD_apply (Y : MilnorK (RatFunc F) p) :
    PhiD p h1 hF N d Y = -(resI p hF Y) - ∑ᶠ π, fD p h1 N d Y π := rfl

theorem PhiD_zero (hW : PropW p h1 hF N d) (Y : MilnorK (RatFunc F) p) (hY : Y ∈ S p d) :
    PhiD p h1 hF N d Y = 0 := by
  have hW' := hW Y hY
  simp only [Psi] at hW'
  have e : (fun π => fD p h1 N d Y π) = fun π => N π (resF p h1 π Y) := by
    funext π
    simp only [fD]
    split_ifs with h
    · rfl
    · rw [show resF p h1 π Y = 0 from res_S_eq_zero p h1 d π (by omega) hY, map_zero]
  rw [PhiD_apply, e, ← neg_add', hW', neg_zero]

theorem resI_bK (b : Fˣ) (Y : MilnorK (RatFunc F) p) :
    resI p hF (of p (bK b) * Y) = -(of p b * resI p hF Y) := by
  simp only [resI]
  rw [res_of_mul, (valI_bK b).1, (valI_bK b).2, zero_smul, zero_sub]

theorem resF_bK (π : Prim F) (b : Fˣ) (Y : MilnorK (RatFunc F) p) :
    resF p h1 π (of p (bK b) * Y) = -(of p (bbar π b) * resF p h1 π Y) := by
  simp only [resF]
  rw [res_of_mul, (valF_bK π b).1, (valF_bK π b).2, zero_smul, zero_sub]

theorem PhiD_b (hP : PropP p N d) (b : Fˣ) (Y : MilnorK (RatFunc F) p) :
    PhiD p h1 hF N d (of p (bK b) * Y) = -(of p b * PhiD p h1 hF N d Y) := by
  have e : (fun π => fD p h1 N d (of p (bK b) * Y) π) =
      fun π => (-(AddMonoidHom.mulLeft (of p b))) (fD p h1 N d Y π) := by
    funext π
    simp only [fD, AddMonoidHom.neg_apply, AddMonoidHom.coe_mulLeft]
    split_ifs with h
    · rw [resF_bK, map_neg, hP π h]
    · rw [mul_zero, neg_zero]
  rw [PhiD_apply, PhiD_apply, e, ← AddMonoidHom.map_finsum _ (fD_fin p h1 N d Y), resI_bK,
    AddMonoidHom.neg_apply, AddMonoidHom.coe_mulLeft, mul_sub, mul_neg']
  abel

end Induction

end OMA.NormRel


/-! The induction step: transfers for the primes of degree `d + 1`. -/

namespace OMA.NormRel

open MilnorK Polynomial

section Step

variable {F : Type*} [Field F] (p : ℕ) (h1 : ∀ π : Prim F, of p (-1 : (Kap π)ˣ) = 0)
  (hF : of p (-1 : Fˣ) = 0) (N : Fam F p) (d : ℕ)
  (hP : PropP p N d) (hW : PropW p h1 hF N d)

/-- The new family: transfers from `PhiD` at the primes of degree `d + 1`. -/
noncomputable def Nnext : Fam F p := fun π =>
  if h : π.1.natDegree = d + 1 then
    trOf p π (PhiD p h1 hF N d) (PhiD_zero p h1 hF N d hW) (PhiD_b p h1 hF N d hP) h
  else N π

theorem Nnext_eq (π : Prim F) (h : π.1.natDegree = d + 1) :
    Nnext p h1 hF N d hP hW π =
      trOf p π (PhiD p h1 hF N d) (PhiD_zero p h1 hF N d hW) (PhiD_b p h1 hF N d hP) h := by
  rw [Nnext, dif_pos h]

theorem Nnext_ne (π : Prim F) (h : π.1.natDegree ≠ d + 1) : Nnext p h1 hF N d hP hW π = N π := by
  rw [Nnext, dif_neg h]

theorem step_P : PropP p (Nnext p h1 hF N d hP hW) (d + 1) := by
  intro π hπ b x
  by_cases h : π.1.natDegree = d + 1
  · rw [Nnext_eq p h1 hF N d hP hW π h]; exact trOf_bbar _ _ _ _ _ h b x
  · rw [Nnext_ne p h1 hF N d hP hW π h]; exact hP π (by omega) b x

theorem resF_pi_mul (π : Prim F) {z : MilnorK (RatFunc F) p} (_hz : res (valF π) (h1 π) z = 0) :
    resF p h1 π (of p (uP π.1 π.2.2.ne_zero) * z) = spec (valF π) (h1 π) z := by
  simp only [resF]
  rw [res_of_mul, (valF_uP_self π).1, (valF_uP_self π).2, of_one, zero_mul, sub_zero, one_smul]

theorem resF_other_mul (π π' : Prim F) (hne : π' ≠ π) {z : MilnorK (RatFunc F) p}
    (hz : res (valF π') (h1 π') z = 0) :
    resF p h1 π' (of p (uP π.1 π.2.2.ne_zero) * z) = 0 := by
  simp only [resF]
  rw [res_of_mul, (valF_uP_of_not_dvd π' π.2.2.ne_zero (prim_not_dvd π π' hne)).1, hz, zero_smul,
    mul_zero, sub_zero]

theorem step_W (hR : of p (-1 : (RatFunc F)ˣ) = 0) :
    PropW p h1 hF (Nnext p h1 hF N d hP hW) (d + 1) := by
  classical
  intro Y hY
  have hT := S_succ_le_T p hR d hY
  clear hY
  induction hT using AddSubgroup.closure_induction with
  | mem Y hY' =>
    rcases hY' with ⟨π, hπ, z, hz, rfl⟩ | hY'
    · have hzπ : res (valF π) (h1 π) z = 0 := res_S_eq_zero p h1 d π (by omega) hz
      have e : (fun π' => Nnext p h1 hF N d hP hW π'
          (resF p h1 π' (of p (uP π.1 π.2.2.ne_zero) * z))) =
          fun π' => fD p h1 N d (of p (uP π.1 π.2.2.ne_zero) * z) π' +
            (if π' = π then Nnext p h1 hF N d hP hW π
              (resF p h1 π (of p (uP π.1 π.2.2.ne_zero) * z)) else 0) := by
        funext π'
        by_cases e : π' = π
        · subst e
          rw [if_pos rfl]
          simp only [fD, if_neg (show ¬ π'.1.natDegree ≤ d by omega), zero_add]
        · rw [if_neg e]
          simp only [fD]
          by_cases hd : π'.1.natDegree ≤ d
          · rw [if_pos hd, add_zero, Nnext_ne p h1 hF N d hP hW π' (by omega)]
          · rw [if_neg hd, add_zero,
              resF_other_mul p h1 π π' e (res_S_eq_zero p h1 d π' (by omega) hz), map_zero]
      have hfin2 : Function.HasFiniteSupport (fun π' => if π' = π then
          Nnext p h1 hF N d hP hW π (resF p h1 π (of p (uP π.1 π.2.2.ne_zero) * z)) else 0) := by
        refine Set.Finite.subset (Set.finite_singleton π) ?_
        intro π' hπ'
        by_contra hn
        exact hπ' (if_neg hn)
      simp only [Psi]
      rw [e, finsum_add_distrib (fD_fin p h1 N d _) hfin2,
        finsum_eq_single _ π (fun π' h => if_neg h), if_pos rfl,
        Nnext_eq p h1 hF N d hP hW π hπ, resF_pi_mul p h1 π hzπ, trOf_spec _ _ _ _ _ h1 hπ hz,
        PhiD_apply]
      abel
    · simp only [Psi]
      have e : (fun π' => Nnext p h1 hF N d hP hW π' (resF p h1 π' Y)) =
          fun π' => N π' (resF p h1 π' Y) := by
        funext π'
        by_cases h : π'.1.natDegree = d + 1
        · rw [show resF p h1 π' Y = 0 from res_S_eq_zero p h1 d π' (by omega) hY', map_zero,
            map_zero]
        · rw [Nnext_ne p h1 hF N d hP hW π' h]
      rw [e]
      exact hW Y hY'
  | zero => exact Psi_zero p h1 hF _
  | add x y _ _ hx hy => rw [Psi_add, hx, hy, add_zero]
  | neg x _ hx => rw [Psi_neg, hx, neg_zero]

end Step

end OMA.NormRel


/-! The induction step, compatibility with the norm in degree one. -/

namespace OMA.NormRel

open MilnorK Polynomial

section StepC

variable {F : Type*} [Field F] (p : ℕ) (h1 : ∀ π : Prim F, of p (-1 : (Kap π)ˣ) = 0)
  (hF : of p (-1 : Fˣ) = 0) (N : Fam F p) (d : ℕ)
  (hP : PropP p N d) (hW : PropW p h1 hF N d)

theorem finrank_kap (π : Prim F) : Module.finrank F (Kap π) = π.1.natDegree := by
  rw [(AdjoinRoot.powerBasis π.2.2.ne_zero).finrank, AdjoinRoot.powerBasis_dim]

theorem normU_val (π : Prim F) (u : (Kap π)ˣ) :
    ((normU π u : Fˣ) : F) = Algebra.norm F (u : Kap π) := rfl

theorem normU_mul (π : Prim F) (u v : (Kap π)ˣ) : normU π (u * v) = normU π u * normU π v :=
  map_mul _ u v

theorem norm_bbar (π : Prim F) (c : Fˣ) : normU π (bbar π c) = c ^ π.1.natDegree := by
  ext
  have := Module.Free.of_basis (AdjoinRoot.powerBasis π.2.2.ne_zero).basis
  rw [normU_val, Units.val_pow_eq_pow_val]
  show Algebra.norm F (algebraMap F (Kap π) (c : F)) = _
  rw [Algebra.norm_algebraMap, finrank_kap]

theorem of_eq_of_neg_pow (hF0 : of p (-1 : Fˣ) = 0) (x y : Fˣ) (k : ℕ)
    (h : (x : F) = (-1) ^ k * y) : of p x = of p y := by
  have : x = (-1) ^ k * y := by ext; simp [h]
  rw [this, of_mul, of_pow, hF0, nsmul_zero, zero_add]

theorem PhiD_pi (π : Prim F) (hπ : π.1.natDegree = d + 1) :
    PhiD p h1 hF N d (of p (uP π.1 π.2.2.ne_zero)) = ((d + 1 : ℕ) : ℤ) • (1 : MilnorK F p) := by
  have e : (fun π' => fD p h1 N d (of p (uP π.1 π.2.2.ne_zero)) π') = fun _ => 0 := by
    funext π'
    simp only [fD]
    split_ifs with h
    · have hne : π' ≠ π := fun e => by subst e; omega
      rw [resF, res_of, (valF_uP_of_not_dvd π' π.2.2.ne_zero (prim_not_dvd π π' hne)).1,
        zero_smul, map_zero]
    · rfl
  rw [PhiD_apply, e, finsum_zero, sub_zero, resI, res_of, (valI_uP _ _).1, hπ, neg_smul, neg_neg]

theorem C_const (π : Prim F) (hπ : π.1.natDegree = d + 1) (c : Fˣ) :
    Nnext p h1 hF N d hP hW π (of p (bbar π c)) = of p (normU π (bbar π c)) := by
  rw [Nnext_eq p h1 hF N d hP hW π hπ]
  have := trOf_bbar p π (PhiD p h1 hF N d) (PhiD_zero p h1 hF N d hW) (PhiD_b p h1 hF N d hP) hπ c 1
  rw [mul_one] at this
  rw [this, trOf_one, PhiD_pi p h1 hF N d π hπ, norm_bbar, hπ, of_pow, mul_smul_comm, mul_one,
    natCast_zsmul]

theorem valI_monic (P : F[X]) (hP : P.Monic) : (valI (F := F)).r (uP P hP.ne_zero) = 1 := by
  ext; rw [(valI_uP P hP.ne_zero).2, hP.leadingCoeff, Units.val_one]

theorem C_prime (hC : PropC p N d)
    (hswap : ∀ π π' : Prim F, Algebra.norm F (AdjoinRoot.mk π.1 π'.1) =
      (-1) ^ (π.1.natDegree * π'.1.natDegree) * Algebra.norm F (AdjoinRoot.mk π'.1 π.1))
    (π : Prim F) (hπ : π.1.natDegree = d + 1) (π' : Prim F) (hd' : π'.1.natDegree ≤ d)
    (hu : AdjoinRoot.mk π.1 π'.1 ≠ 0) :
    Nnext p h1 hF N d hP hW π (of p (Units.mk0 _ hu)) = of p (normU π (Units.mk0 _ hu)) := by
  classical
  have hne : π' ≠ π := fun e => by subst e; omega
  rw [Nnext_eq p h1 hF N d hP hW π hπ, trOf_of,
    ell_mk p π _ π'.2.2.ne_zero (by omega) rfl]
  set r := (valF π').r (uP π.1 π.2.2.ne_zero) with hr
  have hrv : (r : Kap π') = AdjoinRoot.mk π'.1 π.1 :=
    (valF_uP_of_not_dvd π' π.2.2.ne_zero (prim_not_dvd π π' hne)).2
  have hI : resI p hF (of p (uP π.1 π.2.2.ne_zero) * of p (uP π'.1 π'.2.2.ne_zero)) = 0 := by
    rw [resI, res_of_mul, spec_of, valI_monic π'.1 π'.2.1, valI_monic π.1 π.2.1, of_one, smul_zero,
      zero_mul, sub_zero]
  have hres : ∀ π'' : Prim F, π'' ≠ π → resF p h1 π''
      (of p (uP π.1 π.2.2.ne_zero) * of p (uP π'.1 π'.2.2.ne_zero)) =
      -(of p ((valF π'').r (uP π.1 π.2.2.ne_zero)) *
        ((valF π'').v (uP π'.1 π'.2.2.ne_zero) • (1 : MilnorK (Kap π'') p))) := by
    intro π'' h''
    rw [resF, res_of_mul, res_of,
      (valF_uP_of_not_dvd π'' π.2.2.ne_zero (prim_not_dvd π π'' h'')).1, zero_smul, zero_sub]
  have e : (fun π'' => fD p h1 N d
      (of p (uP π.1 π.2.2.ne_zero) * of p (uP π'.1 π'.2.2.ne_zero)) π'') =
      fun π'' => if π'' = π' then -of p (normU π' r) else 0 := by
    funext π''
    simp only [fD]
    by_cases h'' : π'' = π'
    · subst h''
      rw [if_pos hd', if_pos rfl, hres π'' hne, (valF_uP_self π'').1, one_smul, mul_one, map_neg,
        hC π'' hd']
    · rw [if_neg h'']
      split_ifs with hd''
      · have hne'' : π'' ≠ π := fun e => by subst e; omega
        rw [hres π'' hne'',
          (valF_uP_of_not_dvd π'' π'.2.2.ne_zero (prim_not_dvd π' π'' h'')).1, zero_smul,
          mul_zero, neg_zero, map_zero]
      · rfl
  rw [PhiD_apply, hI, e, finsum_eq_single _ π' (fun x hx => if_neg hx), if_pos rfl, neg_zero,
    zero_sub, neg_neg]
  symm
  apply of_eq_of_neg_pow p hF _ _ (π.1.natDegree * π'.1.natDegree)
  rw [normU_val, normU_val, hrv, Units.val_mk0]
  exact hswap π π'

end StepC

end OMA.NormRel


/-! Swap lemma for norms of residues: `N_P(Q mod P) = (-1)^(deg P deg Q) N_Q(P mod Q)`. -/

namespace OMA.NormRel

open Polynomial

section Swap

variable {F : Type*} [Field F] [CharZero F]

theorem norm_mk_eq_prod_aroots (P Q : F[X]) [hP : Fact (Irreducible P)] (hm : P.Monic) :
    algebraMap F (AlgebraicClosure F) (Algebra.norm F (AdjoinRoot.mk P Q)) =
      ((P.aroots (AlgebraicClosure F)).map fun a ↦ aeval a Q).prod := by
  classical
  have hP0 : P ≠ 0 := hP.out.ne_zero
  let pb := AdjoinRoot.powerBasis hP0
  have : FiniteDimensional F (AdjoinRoot P) := pb.finite
  have : Algebra.IsSeparable F (AdjoinRoot P) := inferInstance
  rw [Algebra.norm_eq_prod_embeddings F (AlgebraicClosure F)]
  have hmin : minpoly F pb.gen = P := by
    rw [AdjoinRoot.powerBasis_gen, AdjoinRoot.minpoly_root hP0, hm.leadingCoeff, inv_one, C_1,
      mul_one]
  have hsep : (P.aroots (AlgebraicClosure F)).Nodup :=
    nodup_roots ((Irreducible.separable hP.out).map)
  have key : ∀ σ : AdjoinRoot P →ₐ[F] AlgebraicClosure F,
      σ (AdjoinRoot.mk P Q) = aeval ((pb.liftEquiv' σ : AlgebraicClosure F)) Q := by
    intro σ
    rw [PowerBasis.liftEquiv'_apply_coe, ← AdjoinRoot.aeval_eq, aeval_algHom_apply,
      AdjoinRoot.powerBasis_gen]
  rw [Fintype.prod_congr _ _ key]
  have hR : ((P.aroots (AlgebraicClosure F)).map fun a ↦ aeval a Q).prod =
      ∏ y ∈ (P.aroots (AlgebraicClosure F)).toFinset, aeval y Q := by
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hsep]
  rw [hR]
  refine Finset.prod_bij (fun σ _ ↦ (pb.liftEquiv' σ : AlgebraicClosure F)) ?_ ?_ ?_ ?_
  · intro σ _
    have hmem : ∀ y : AlgebraicClosure F, y ∈ (minpoly F pb.gen).aroots (AlgebraicClosure F) →
        y ∈ P.aroots (AlgebraicClosure F) := fun y hy ↦ by rwa [hmin] at hy
    exact Multiset.mem_toFinset.mpr (hmem _ (pb.liftEquiv' σ).2)
  · intro a _ b _ hab
    exact pb.liftEquiv'.injective (Subtype.ext hab)
  · intro y hy
    have hy' : y ∈ (minpoly F pb.gen).aroots (AlgebraicClosure F) := by
      rw [hmin]; exact Multiset.mem_toFinset.mp hy
    exact ⟨pb.liftEquiv'.symm ⟨y, hy'⟩, Finset.mem_univ _, by simp⟩
  · intro σ _
    rfl

theorem prod_sub_swap {E : Type*} [CommRing E] (s t : Multiset E) :
    (s.map fun a ↦ (t.map fun b ↦ a - b).prod).prod =
      (-1) ^ (Multiset.card s * Multiset.card t) *
        (t.map fun b ↦ (s.map fun a ↦ b - a).prod).prod := by
  rw [Multiset.prod_map_prod_map s t]
  have h1 : ∀ b : E, (s.map fun a ↦ a - b).prod =
      (-1) ^ Multiset.card s * (s.map fun a ↦ b - a).prod := by
    intro b
    have : (fun a ↦ a - b) = fun a ↦ (-1) * (b - a) := by
      funext a; ring
    rw [this, Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate]
  simp only [h1]
  rw [Multiset.prod_map_mul, Multiset.map_const', Multiset.prod_replicate, ← pow_mul]

theorem norm_swap (P Q : F[X]) [hP : Fact (Irreducible P)] [hQ : Fact (Irreducible Q)]
    (hPm : P.Monic) (hQm : Q.Monic) :
    Algebra.norm F (AdjoinRoot.mk P Q) =
      (-1) ^ (P.natDegree * Q.natDegree) * Algebra.norm F (AdjoinRoot.mk Q P) := by
  apply (algebraMap F (AlgebraicClosure F)).injective
  rw [map_mul, map_pow, map_neg, map_one, norm_mk_eq_prod_aroots P Q hPm,
    norm_mk_eq_prod_aroots Q P hQm]
  set E := AlgebraicClosure F
  have hsP : (P.map (algebraMap F E)).Splits := IsAlgClosed.splits _
  have hsQ : (Q.map (algebraMap F E)).Splits := IsAlgClosed.splits _
  have evQ : ∀ a : E, aeval a Q = ((Q.aroots E).map fun b ↦ a - b).prod := by
    intro a
    rw [aeval_def, ← eval_map, hsQ.eval_eq_prod_roots, leadingCoeff_map_of_injective
      (algebraMap F E).injective, hQm.leadingCoeff, map_one, one_mul]
  have evP : ∀ b : E, aeval b P = ((P.aroots E).map fun a ↦ b - a).prod := by
    intro b
    rw [aeval_def, ← eval_map, hsP.eval_eq_prod_roots, leadingCoeff_map_of_injective
      (algebraMap F E).injective, hPm.leadingCoeff, map_one, one_mul]
  have cP : Multiset.card (P.aroots E) = P.natDegree := by
    rw [← hsP.natDegree_eq_card_roots, natDegree_map]
  have cQ : Multiset.card (Q.aroots E) = Q.natDegree := by
    rw [← hsQ.natDegree_eq_card_roots, natDegree_map]
  simp only [evQ, evP]
  rw [prod_sub_swap, cP, cQ]

end Swap

end OMA.NormRel


/-! The transfer exists in every degree; the Kummer norm relation. -/

namespace OMA.NormRel

open MilnorK Polynomial

section Final

variable {F : Type*} [Field F] (p : ℕ)

/-- `T({u}) = {N u}` for the residue of `Q`. -/
def GoodQ (π : Prim F) (T : MilnorK (Kap π) p →+ MilnorK F p) (Q : F[X]) : Prop :=
  ∀ hQ : AdjoinRoot.mk π.1 Q ≠ 0, T (of p (Units.mk0 _ hQ)) = of p (normU π (Units.mk0 _ hQ))

theorem good_mul (π : Prim F) (T : MilnorK (Kap π) p →+ MilnorK F p) {A B : F[X]}
    (hA : GoodQ p π T A) (hB : GoodQ p π T B) : GoodQ p π T (A * B) := by
  intro hAB
  have hA0 : AdjoinRoot.mk π.1 A ≠ 0 := fun h => hAB (by rw [map_mul, h, zero_mul])
  have hB0 : AdjoinRoot.mk π.1 B ≠ 0 := fun h => hAB (by rw [map_mul, h, mul_zero])
  have e : Units.mk0 (AdjoinRoot.mk π.1 (A * B)) hAB =
      Units.mk0 (AdjoinRoot.mk π.1 A) hA0 * Units.mk0 (AdjoinRoot.mk π.1 B) hB0 := by
    ext; simp [map_mul]
  rw [e, of_mul, map_add, hA hA0, hB hB0, normU_mul, of_mul]

theorem good_C (π : Prim F) (T : MilnorK (Kap π) p →+ MilnorK F p)
    (hT : ∀ c : Fˣ, T (of p (bbar π c)) = of p (normU π (bbar π c))) (c : F) (hc : c ≠ 0) :
    GoodQ p π T (C c) := by
  intro hQ
  have e : Units.mk0 (AdjoinRoot.mk π.1 (C c)) hQ = bbar π (Units.mk0 c hc) := by
    ext; rw [bbar_val]; rfl
  rw [e, hT]

variable (h1 : ∀ π : Prim F, of p (-1 : (Kap π)ˣ) = 0) (hF : of p (-1 : Fˣ) = 0)

theorem step_C (N : Fam F p) (d : ℕ) (hP : PropP p N d) (hW : PropW p h1 hF N d)
    (hC : PropC p N d)
    (hswap : ∀ π π' : Prim F, Algebra.norm F (AdjoinRoot.mk π.1 π'.1) =
      (-1) ^ (π.1.natDegree * π'.1.natDegree) * Algebra.norm F (AdjoinRoot.mk π'.1 π.1)) :
    PropC p (Nnext p h1 hF N d hP hW) (d + 1) := by
  intro π hπ u
  by_cases h : π.1.natDegree = d + 1
  swap
  · rw [Nnext_ne p h1 hF N d hP hW π h]; exact hC π (by omega) u
  set T := Nnext p h1 hF N d hP hW π with hT
  have hconst : ∀ c : Fˣ, T (of p (bbar π c)) = of p (normU π (bbar π c)) :=
    C_const p h1 hF N d hP hW π h
  have good : ∀ Q : F[X], Q ≠ 0 → Q.natDegree ≤ d → GoodQ p π T Q := by
    intro Q
    refine UniqueFactorizationMonoid.induction_on_prime Q ?_ ?_ ?_
    · intro h0; exact absurd rfl h0
    · intro x hx _ _
      obtain ⟨r, hr, rfl⟩ := Polynomial.isUnit_iff.mp hx
      exact good_C p π T hconst r hr.ne_zero
    · intro a q ha hq ih hqa hdeg
      have hq0 : q ≠ 0 := hq.ne_zero
      have hdq : q.natDegree ≤ d := by
        rw [natDegree_mul hq0 ha] at hdeg; omega
      have hda : a.natDegree ≤ d := by
        rw [natDegree_mul hq0 ha] at hdeg; omega
      refine good_mul p π T ?_ (ih ha hda)
      -- `q` is a constant times a monic irreducible
      have hlc : q.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hq0
      have hmon : (q * C q.leadingCoeff⁻¹).Monic := monic_mul_leadingCoeff_inv hq0
      have hirr : Irreducible (q * C q.leadingCoeff⁻¹) :=
        (irreducible_mul_isUnit (isUnit_C.mpr (inv_ne_zero hlc).isUnit)).mpr hq.irreducible
      let π' : Prim F := ⟨q * C q.leadingCoeff⁻¹, hmon, hirr⟩
      have hdπ' : π'.1.natDegree ≤ d := by
        show (q * C q.leadingCoeff⁻¹).natDegree ≤ d
        rw [natDegree_mul_C (inv_ne_zero hlc)]; exact hdq
      have hqe : q = C q.leadingCoeff * π'.1 := by
        show q = C q.leadingCoeff * (q * C q.leadingCoeff⁻¹)
        rw [mul_comm q, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul]
      rw [hqe]
      refine good_mul p π T (good_C p π T hconst _ hlc) ?_
      intro hu
      exact C_prime p h1 hF N d hP hW hC hswap π h π' hdπ' hu
  have hu : AdjoinRoot.mk π.1 (liftP π (u : Kap π)) ≠ 0 := by rw [mk_liftP]; exact u.ne_zero
  have e : u = Units.mk0 _ hu := Units.ext (mk_liftP π (u : Kap π)).symm
  rw [e]
  exact good _ (liftP_ne_zero π u) (by have := natDegree_liftP_lt π (u : Kap π); omega) hu

theorem exists_transfer (hR : of p (-1 : (RatFunc F)ˣ) = 0)
    (hswap : ∀ π π' : Prim F, Algebra.norm F (AdjoinRoot.mk π.1 π'.1) =
      (-1) ^ (π.1.natDegree * π'.1.natDegree) * Algebra.norm F (AdjoinRoot.mk π'.1 π.1))
    (d : ℕ) : ∃ N : Fam F p, PropP p N d ∧ PropC p N d ∧ PropW p h1 hF N d := by
  induction d with
  | zero => exact base p h1 hF
  | succ d ih =>
    obtain ⟨N, hP, hC, hW⟩ := ih
    exact ⟨Nnext p h1 hF N d hP hW, step_P p h1 hF N d hP hW,
      step_C p h1 hF N d hP hW hC hswap, step_W p h1 hF N d hP hW hR⟩

theorem of_neg_one_of_alg (E : Type*) [Field E] [Algebra F E]
    (h : Odd p ∨ (p = 2 ∧ ∃ i : F, i * i = -1)) : of p (-1 : Eˣ) = 0 := by
  apply of_neg_one_eq_zero
  rcases h with h | ⟨h2, i, hi⟩
  · exact Or.inl h
  · exact Or.inr ⟨h2, algebraMap F E i, by rw [← map_mul, hi, map_neg, map_one]⟩

/-- The Kummer norm relation `{a, N(k)} = 0` in `K_2(F)/p`. -/
theorem kummer_general {F : Type*} [Field F] [CharZero F] (hi : ∃ i : F, i * i = -1) (p : ℕ)
    (hp : p.Prime) (a : Fˣ) (k : AdjoinRoot (Polynomial.X ^ p - Polynomial.C (a : F)))
    (hk : Algebra.norm F k ≠ 0) : MilnorK.of p a * MilnorK.of p (Units.mk0 _ hk) = 0 := by
  have hneg : Odd p ∨ (p = 2 ∧ ∃ i : F, i * i = -1) := by
    rcases hp.eq_two_or_odd' with h | h
    · exact Or.inr ⟨h, hi⟩
    · exact Or.inl h
  by_cases ha : ∃ b : F, b ^ p = a
  · obtain ⟨b, hb⟩ := ha
    have hb0 : b ≠ 0 := by
      rintro rfl; rw [zero_pow hp.ne_zero] at hb; exact a.ne_zero hb.symm
    have e : a = Units.mk0 b hb0 ^ p := by ext; simp [hb]
    have h0 : of p a = 0 := by rw [e, of_pow, nsmul_p]
    rw [h0, zero_mul]
  push Not at ha
  have hirr : Irreducible (X ^ p - C (a : F)) := X_pow_sub_C_irreducible_of_prime hp ha
  let π : Prim F := ⟨X ^ p - C (a : F), monic_X_pow_sub_C _ hp.ne_zero, hirr⟩
  have hdeg : π.1.natDegree = p := natDegree_X_pow_sub_C
  have hF : of p (-1 : Fˣ) = 0 := of_neg_one_of_alg p F hneg
  have hR : of p (-1 : (RatFunc F)ˣ) = 0 := of_neg_one_of_alg p (RatFunc F) hneg
  have h1 : ∀ π : Prim F, of p (-1 : (Kap π)ˣ) = 0 := fun π => of_neg_one_of_alg p (Kap π) hneg
  have hswap : ∀ π π' : Prim F, Algebra.norm F (AdjoinRoot.mk π.1 π'.1) =
      (-1) ^ (π.1.natDegree * π'.1.natDegree) * Algebra.norm F (AdjoinRoot.mk π'.1 π.1) :=
    fun π π' => norm_swap π.1 π'.1 π.2.1 π'.2.1
  obtain ⟨N, hP, hC, -⟩ := exists_transfer p h1 hF hR hswap p
  have hfact : Fact (Irreducible (X ^ p - C (a : F))) := ⟨hirr⟩
  have hk0 : (k : Kap π) ≠ 0 := by
    intro h0
    apply hk
    have h0' : k = 0 := h0
    have := (AdjoinRoot.powerBasis hirr.ne_zero).finite
    have := Module.Free.of_basis (AdjoinRoot.powerBasis hirr.ne_zero).basis
    rw [h0']
    exact Algebra.norm_zero
  let ku : (Kap π)ˣ := Units.mk0 (k : Kap π) hk0
  have hr : AdjoinRoot.root (X ^ p - C (a : F)) ^ p =
      AdjoinRoot.mk (X ^ p - C (a : F)) (C (a : F)) := by
    have h0 : AdjoinRoot.mk (X ^ p - C (a : F)) (X ^ p - C (a : F)) = 0 := AdjoinRoot.mk_self
    rwa [map_sub, map_pow, AdjoinRoot.mk_X, sub_eq_zero] at h0
  have hroot : (AdjoinRoot.root (X ^ p - C (a : F)) : Kap π) ≠ 0 := by
    intro h0
    have h2 : AdjoinRoot.mk (X ^ p - C (a : F)) (C (a : F)) = 0 := by
      rw [← hr, h0, zero_pow hp.ne_zero]
    rw [AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq] at h2
    exact a.ne_zero ((map_eq_zero_iff _ (algebraMap F (Kap π)).injective).mp h2)
  have hbar : bbar π a = Units.mk0 _ hroot ^ p := by
    ext
    rw [bbar_val, Units.val_pow_eq_pow_val, Units.val_mk0]
    exact hr.symm
  have hzero : of p (bbar π a) = 0 := by rw [hbar, of_pow, nsmul_p]
  have key := hP π (by omega) a (of p ku)
  rw [hzero, zero_mul, map_zero, hC π (by omega) ku] at key
  have e : normU π ku = Units.mk0 (Algebra.norm F k) hk := Units.ext rfl
  rw [← e]
  exact key.symm

end Final

end OMA.NormRel

namespace OMA.NormRel

theorem exists_sqrt_neg_one_of_complex (K : Type*) [Field K] [Algebra ℂ K] :
    ∃ i : K, i * i = -1 :=
  ⟨algebraMap ℂ K Complex.I, by rw [← map_mul, Complex.I_mul_I, map_neg, map_one]⟩

theorem charZero_of_complex (K : Type*) [Field K] [Algebra ℂ K] : CharZero K :=
  charZero_of_injective_algebraMap (algebraMap ℂ K).injective

end OMA.NormRel

namespace OMA.MatzriOdd

namespace MatzriK

open MilnorK

variable {F : Type*} [Field F] (ℓ : ℕ)

theorem nsmul_ell (x : MilnorK F ℓ) : ℓ • x = 0 := by
  rw [nsmul_eq_mul, natCast_eq_zero, zero_mul]

theorem of_pow_ell (u : Fˣ) : of ℓ (u ^ ℓ) = 0 := by
  rw [of_pow, nsmul_ell]

theorem of_add_of_inv (a : Fˣ) : of ℓ a + of ℓ a⁻¹ = 0 := by
  rw [← of_mul, mul_inv_cancel, of_one]

theorem mul_of_inv (x : MilnorK F ℓ) (a : Fˣ) : x * of ℓ a + x * of ℓ a⁻¹ = 0 := by
  rw [← mul_add, of_add_of_inv, mul_zero]

theorem of_inv_mul (x : MilnorK F ℓ) (a : Fˣ) : of ℓ a * x + of ℓ a⁻¹ * x = 0 := by
  rw [← add_mul, of_add_of_inv, zero_mul]

theorem eq_of_add_eq_zero' {x y z : MilnorK F ℓ} (h1 : x + y = 0) (h2 : y + z = 0) : x = z := by
  calc x = x + (y + z) := by rw [h2, add_zero]
    _ = (x + y) + z := by rw [add_assoc]
    _ = z := by rw [h1, zero_add]

theorem eq_zero_of_add_eq_zero_left' {x y : MilnorK F ℓ} (h1 : x + y = 0) (h2 : x = 0) : y = 0 := by
  rw [h2, zero_add] at h1; exact h1

/-- `{x, -x} = 0`. -/
theorem of_mul_of_neg_self (a : Fˣ) : of ℓ a * of ℓ (-a) = 0 := by
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
  have hb : of ℓ a * of ℓ b = 0 := of_mul_of_eq_zero ℓ a b (by simp [b])
  have hc : of ℓ a⁻¹ * of ℓ c = 0 := of_mul_of_eq_zero ℓ a⁻¹ c (by simp [c])
  have hc' : of ℓ a * of ℓ c = 0 := by
    have := of_inv_mul ℓ (of ℓ c) a
    rw [hc, add_zero] at this; exact this
  have hc'' : of ℓ a * of ℓ c⁻¹ = 0 :=
    eq_zero_of_add_eq_zero_left' ℓ (mul_of_inv ℓ (of ℓ a) c) hc'
  have hneg : -a = b * c⁻¹ := by
    have ha0 : (a : F) ≠ 0 := a.ne_zero
    ext
    simp only [Units.val_neg, Units.val_mul, b, c, Units.val_mk0, Units.val_inv_eq_inv_val]
    field_simp
    have : (a : F) - 1 ≠ 0 := by intro h; apply h1; linear_combination -h
    field_simp
    ring
  rw [hneg, of_mul, mul_add, hb, hc'', add_zero]

/-- Anticommutativity in degree one. -/
theorem of_anticomm (a b : Fˣ) : of ℓ a * of ℓ b + of ℓ b * of ℓ a = 0 := by
  have h := of_mul_of_neg_self ℓ (a * b)
  rw [of_mul, add_mul] at h
  have e1 : -(a * b) = (-a) * b := by simp
  have e2 : -(a * b) = a * (-b) := by simp
  have t1 : of ℓ a * of ℓ (-(a * b)) = of ℓ a * of ℓ b := by
    rw [e1, of_mul, mul_add, of_mul_of_neg_self, zero_add]
  have t2 : of ℓ b * of ℓ (-(a * b)) = of ℓ b * of ℓ a := by
    rw [e2, of_mul, mul_add, of_mul_of_neg_self, add_zero]
  rw [t1, t2] at h; exact h

/-- `{a, b} = {b, a⁻¹}`. -/
theorem of_swap (a b : Fˣ) : of ℓ a * of ℓ b = of ℓ b * of ℓ a⁻¹ :=
  eq_of_add_eq_zero' ℓ (of_anticomm ℓ a b) (mul_of_inv ℓ (of ℓ b) a)

/-- `{a, b} = {a + b, -a⁻¹ b}`. -/
theorem of_add_slot (a b e : Fˣ) (h : (a : F) + b = e) :
    of ℓ a * of ℓ b = of ℓ e * of ℓ (-a⁻¹ * b) := by
  have hu : (1 : F) + ((a⁻¹ * b : Fˣ) : F) ≠ 0 := by
    have : (1 : F) + ((a⁻¹ * b : Fˣ) : F) = (a : F)⁻¹ * e := by
      rw [← h]; simp only [Units.val_mul, Units.val_inv_eq_inv_val]; field_simp
    rw [this]; exact mul_ne_zero (inv_ne_zero a.ne_zero) e.ne_zero
  set u := Units.mk0 _ hu
  have he : e = a * u := by
    ext; simp only [u, Units.val_mul, Units.val_mk0, Units.val_inv_eq_inv_val, ← h]
    field_simp
  have hst : of ℓ u * of ℓ (-(a⁻¹ * b)) = 0 :=
    of_mul_of_eq_zero ℓ u _ (by simp [u])
  have e1 : -a⁻¹ * b = -(a⁻¹ * b) := by simp
  rw [he, e1, of_mul, add_mul, hst, add_zero]
  have e2 : -(a⁻¹ * b) = (-a)⁻¹ * b := by simp
  have h0 : of ℓ a * of ℓ (-a)⁻¹ = 0 :=
    eq_zero_of_add_eq_zero_left' ℓ (mul_of_inv ℓ (of ℓ a) (-a)) (of_mul_of_neg_self ℓ a)
  rw [e2, of_mul, mul_add, h0, zero_add]

/-- `{a, b} + {c, d} = {a, b d⁻¹} + {a c, d}`. -/
theorem of_shift (a b c d : Fˣ) :
    of ℓ a * of ℓ b + of ℓ c * of ℓ d = of ℓ a * of ℓ (b * d⁻¹) + of ℓ (a * c) * of ℓ d := by
  have h0 : of ℓ a * of ℓ d + of ℓ a * of ℓ d⁻¹ = 0 := mul_of_inv ℓ (of ℓ a) d
  rw [of_mul, of_mul, mul_add, add_mul]
  calc of ℓ a * of ℓ b + of ℓ c * of ℓ d
      = of ℓ a * of ℓ b + of ℓ c * of ℓ d + (of ℓ a * of ℓ d + of ℓ a * of ℓ d⁻¹) := by
        rw [h0, add_zero]
    _ = of ℓ a * of ℓ b + of ℓ a * of ℓ d⁻¹ + (of ℓ a * of ℓ d + of ℓ c * of ℓ d) := by abel

/-- `{c^ℓ a, b} = {a, b}`. -/
theorem of_pow_mul_left (u a : Fˣ) (b : MilnorK F ℓ) : of ℓ (u ^ ℓ * a) * b = of ℓ a * b := by
  rw [of_mul, of_pow_ell, zero_add]

end MatzriK

namespace MatzriN

open Polynomial

variable {F : Type*} [Field F] (p : ℕ)

/-- The norm form of `F[θ]/(θ^p - a)` in the power coordinates is a homogeneous polynomial of
degree `p`. -/
theorem exists_normPoly (hp : 0 < p) (a : F) : ∃ Φ : MvPolynomial (Fin p) F, Φ.IsHomogeneous p ∧
    ∀ c : Fin p → F, MvPolynomial.eval c Φ = Algebra.norm F
      (∑ l : Fin p, c l • (AdjoinRoot.root (X ^ p - C a)) ^ (l : ℕ)) := by
  set B := AdjoinRoot.powerBasis' (monic_X_pow_sub_C a hp.ne') with hB
  have hdim : B.dim = p := by
    rw [hB, AdjoinRoot.powerBasis'_dim, natDegree_X_pow_sub_C]
  set M : Matrix (Fin B.dim) (Fin B.dim) (MvPolynomial (Fin p) F) := Matrix.of fun i j ↦
    ∑ l : Fin p, MvPolynomial.X l * MvPolynomial.C (Algebra.leftMulMatrix B.basis
      ((AdjoinRoot.root (X ^ p - C a)) ^ (l : ℕ)) i j) with hM
  refine ⟨M.det, ?_, ?_⟩
  · have key : M.det.IsHomogeneous B.dim := by
      rw [Matrix.det_apply']
      apply MvPolynomial.IsHomogeneous.sum
      intro σ _
      have h0 : MvPolynomial.IsHomogeneous
          ((((Equiv.Perm.sign σ : ℤˣ) : ℤ) : MvPolynomial (Fin p) F)) 0 := by
        rw [← map_intCast (MvPolynomial.C : F →+* MvPolynomial (Fin p) F)]
        exact MvPolynomial.isHomogeneous_C _ _
      have h1 := MvPolynomial.IsHomogeneous.prod (s := Finset.univ)
        (φ := fun i : Fin B.dim ↦ M (σ i) i) (n := fun _ ↦ 1) (by
        intro i _
        simp only [hM, Matrix.of_apply]
        apply MvPolynomial.IsHomogeneous.sum
        intro l _
        simpa using (MvPolynomial.isHomogeneous_X F l).mul (MvPolynomial.isHomogeneous_C _ _))
      simpa using h0.mul h1
    convert key using 1
    exact hdim.symm
  · intro c
    rw [RingHom.map_det, Algebra.norm_eq_matrix_det B.basis]
    congr 1
    ext i j
    simp only [hM, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_sum, map_mul,
      MvPolynomial.eval_X, MvPolynomial.eval_C, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun l _ ↦ ?_
    simp only [map_smul, Matrix.smul_apply, smul_eq_mul]

theorem norm_zero' (hp : 0 < p) (a : F) : Algebra.norm F
    (∑ l : Fin p, (0 : Fin p → F) l • (AdjoinRoot.root (X ^ p - C a)) ^ (l : ℕ)) = 0 := by
  set B := AdjoinRoot.powerBasis' (monic_X_pow_sub_C a hp.ne')
  have hdeg : (X ^ p - C a).degree ≠ 0 := by
    rw [degree_X_pow_sub_C hp]; exact_mod_cast hp.ne'
  haveI : Nontrivial (AdjoinRoot (X ^ p - C a)) := AdjoinRoot.nontrivial _ hdeg
  letI := Module.Free.of_basis B.basis
  letI := B.finite
  simp

/-- Over a non-`p`-th power, the norm vanishes only at `0`. -/
theorem norm_eq_zero' (hp : p.Prime) (a : F) (ha : ∀ b : F, b ^ p ≠ a) (c : Fin p → F)
    (h : Algebra.norm F (∑ l : Fin p, c l • (AdjoinRoot.root (X ^ p - C a)) ^ (l : ℕ)) = 0) :
    c = 0 := by
  haveI : Fact (Irreducible (X ^ p - C a)) := ⟨X_pow_sub_C_irreducible_of_prime hp ha⟩
  have hp0 := hp.pos
  set B := AdjoinRoot.powerBasis' (monic_X_pow_sub_C a hp0.ne') with hB
  letI := Module.Free.of_basis B.basis
  letI := B.finite
  have he := (Algebra.norm_eq_zero_iff).mp h
  have hli := B.basis.linearIndependent
  have hd : B.dim = p := by rw [hB, AdjoinRoot.powerBasis'_dim, natDegree_X_pow_sub_C]
  rw [Fintype.linearIndependent_iff] at hli
  funext l
  have := hli (fun i ↦ c (Fin.cast hd i)) (by
    rw [← he]
    refine Fintype.sum_equiv (finCongr hd) _ _ fun i ↦ ?_
    rw [PowerBasis.coe_basis]
    simp only [hB, AdjoinRoot.powerBasis'_gen]
    rfl)
  simpa using this (Fin.cast hd.symm l)

end MatzriN

namespace MatzriR

open MilnorK MatzriK

variable {F : Type*} [Field F] (p : ℕ)

theorem SumLE_zero : ∃ l : List (Fˣ × Fˣ), l.length ≤ 0 ∧
    (0 : MilnorK F p) = (l.map fun q ↦ of p q.1 * of p q.2).sum := ⟨[], le_rfl, rfl⟩

theorem SumLE_mono {k k' : ℕ} {x : MilnorK F p}
    (h : ∃ l : List (Fˣ × Fˣ), l.length ≤ k ∧ x = (l.map fun q ↦ of p q.1 * of p q.2).sum)
    (hk : k ≤ k') :
    ∃ l : List (Fˣ × Fˣ), l.length ≤ k' ∧ x = (l.map fun q ↦ of p q.1 * of p q.2).sum :=
  let ⟨l, hl, hx⟩ := h; ⟨l, hl.trans hk, hx⟩

theorem SumLE_add {k k' : ℕ} {x y : MilnorK F p}
    (hx : ∃ l : List (Fˣ × Fˣ), l.length ≤ k ∧ x = (l.map fun q ↦ of p q.1 * of p q.2).sum)
    (hy : ∃ l : List (Fˣ × Fˣ), l.length ≤ k' ∧ y = (l.map fun q ↦ of p q.1 * of p q.2).sum) :
    ∃ l : List (Fˣ × Fˣ), l.length ≤ k + k' ∧ x + y = (l.map fun q ↦ of p q.1 * of p q.2).sum := by
  obtain ⟨l, hl, rfl⟩ := hx
  obtain ⟨l', hl', rfl⟩ := hy
  exact ⟨l ++ l', by rw [List.length_append]; omega, by simp⟩

theorem SumLE_add_sym {k : ℕ} {x : MilnorK F p}
    (hx : ∃ l : List (Fˣ × Fˣ), l.length ≤ k ∧ x = (l.map fun q ↦ of p q.1 * of p q.2).sum)
    (u v : Fˣ) : ∃ l : List (Fˣ × Fˣ), l.length ≤ k + 1 ∧
      x + of p u * of p v = (l.map fun q ↦ of p q.1 * of p q.2).sum :=
  SumLE_add p hx ⟨[(u, v)], le_rfl, by simp⟩

theorem S_SumLE (a b : ℕ → Fˣ) (t : ℕ) : ∃ l : List (Fˣ × Fˣ), l.length ≤ t ∧
    ∑ j ∈ Finset.range t, of p (a j) * of p (b j) = (l.map fun q ↦ of p q.1 * of p q.2).sum := by
  induction t with
  | zero => exact ⟨[], le_rfl, by simp⟩
  | succ t ih =>
    rw [Finset.sum_range_succ]
    exact SumLE_add_sym p ih _ _

theorem Ico_SumLE (a b : ℕ → Fˣ) (lo : ℕ) : ∀ hi, lo ≤ hi →
    ∃ l : List (Fˣ × Fˣ), l.length ≤ hi - lo ∧
      ∑ j ∈ Finset.Ico lo hi, of p (a j) * of p (b j) = (l.map fun q ↦ of p q.1 * of p q.2).sum := by
  intro hi hle
  induction hi, hle using Nat.le_induction with
  | base => exact ⟨[], by simp, by simp⟩
  | succ hi hle ih =>
    rw [Finset.sum_Ico_succ_top hle, show hi + 1 - lo = (hi - lo) + 1 by omega]
    exact SumLE_add_sym p ih _ _

theorem helper (hp : 0 < p) (f : F) (N : ℕ → F) (hN0 : N 0 = f ^ p) (t : ℕ)
    (x : MilnorK F p)
    (hx : ∃ l : List (Fˣ × Fˣ), l.length ≤ t - 1 ∧ x = (l.map fun q ↦ of p q.1 * of p q.2).sum)
    (h : N t ≠ 0) (z : Fˣ) : ∃ l : List (Fˣ × Fˣ), l.length ≤ t ∧
      x + of p (Units.mk0 _ h) * of p z = (l.map fun q ↦ of p q.1 * of p q.2).sum := by
  cases t with
  | zero =>
    have hf : f ≠ 0 := by
      intro hf; apply h; rw [hN0, hf, zero_pow hp.ne']
    have e : Units.mk0 (N 0) h = (Units.mk0 f hf) ^ p := by
      ext; simp [hN0]
    rw [e, of_pow_ell, zero_mul, add_zero]
    simpa using hx
  | succ s =>
    simpa using SumLE_add_sym p hx (Units.mk0 _ h) z

/-- Matzri's slot lemma: a nonzero value of the norm form is a slot. -/
theorem slot (hp : 0 < p) (nrm : F → (Fin p → F) → F)
    (hrel : ∀ (a : Fˣ) (c : Fin p → F) (h : nrm a c ≠ 0), of p a * of p (Units.mk0 _ h) = 0)
    (a b : ℕ → Fˣ) (f : F) (c : ℕ → Fin p → F) (N : ℕ → F) (hN0 : N 0 = f ^ p)
    (hNs : ∀ t, N (t + 1) = N t * a t + nrm (a t) (c t) * b t) :
    ∀ t (h : N t ≠ 0), ∃ x, (∃ l : List (Fˣ × Fˣ), l.length ≤ t - 1 ∧
        x = (l.map fun q ↦ of p q.1 * of p q.2).sum) ∧
      ∃ e : Fˣ, ∑ j ∈ Finset.range t, of p (a j) * of p (b j) =
        x + of p (Units.mk0 _ h) * of p e := by
  intro t
  induction t with
  | zero =>
    intro h
    exact ⟨0, ⟨[], le_rfl, rfl⟩, 1, by simp⟩
  | succ t ih =>
    intro h
    have hval := hNs t
    have hS : ∑ j ∈ Finset.range (t + 1), of p (a j) * of p (b j) =
        ∑ j ∈ Finset.range t, of p (a j) * of p (b j) + of p (a t) * of p (b t) :=
      Finset.sum_range_succ _ _
    by_cases hn : nrm (a t) (c t) = 0
    · have hN' : N t ≠ 0 := by
        intro h0; apply h; rw [hval, h0, hn]; ring
      obtain ⟨x', hx', e', he'⟩ := ih hN'
      have hu : Units.mk0 _ h = Units.mk0 _ hN' * a t := by
        ext; simp [hval, hn]
      refine ⟨x' + of p (Units.mk0 _ hN') * of p (e' * (b t)⁻¹), ?_, b t, ?_⟩
      · rw [Nat.add_sub_cancel]; exact helper p hp f N hN0 t x' hx' hN' _
      · rw [hS, he', add_assoc, of_shift, hu, add_assoc]
    · have hrel' : of p (a t) * of p (b t) = of p (a t) * of p (Units.mk0 _ hn * b t) := by
        rw [of_mul, mul_add, hrel (a t) (c t) hn, zero_add]
      set b' := Units.mk0 _ hn * b t with hb'
      by_cases hN0' : N t = 0
      · have hu : Units.mk0 _ h = b' := by
          ext; simp [hval, hN0', b']
        refine ⟨∑ j ∈ Finset.range t, of p (a j) * of p (b j), ?_, (a t)⁻¹, ?_⟩
        · rw [Nat.add_sub_cancel]; exact S_SumLE p a b t
        · rw [hS, hrel', of_swap, hu]
      · obtain ⟨x', hx', e', he'⟩ := ih hN0'
        have hsum : ((Units.mk0 _ hN0' * a t : Fˣ) : F) + b' = Units.mk0 _ h := by
          simp [hval, b']
        refine ⟨x' + of p (Units.mk0 _ hN0') * of p (e' * b'⁻¹), ?_,
          -(Units.mk0 _ hN0' * a t)⁻¹ * b', ?_⟩
        · rw [Nat.add_sub_cancel]; exact helper p hp f N hN0 t x' hx' hN0' _
        · rw [hS, he', hrel', add_assoc, of_shift, of_add_slot p _ _ _ hsum, add_assoc]

/-- Matzri's zero lemma: a nontrivial zero of the norm form shortens the sum. -/
theorem zero_reduce (hp : p.Prime) (nrm : F → (Fin p → F) → F)
    (hrel : ∀ (a : Fˣ) (c : Fin p → F) (h : nrm a c ≠ 0), of p a * of p (Units.mk0 _ h) = 0)
    (hzero : ∀ a : F, nrm a 0 = 0)
    (hnd : ∀ a : F, (∀ u : F, u ^ p ≠ a) → ∀ c, nrm a c = 0 → c = 0)
    (a b : ℕ → Fˣ) (t : ℕ) (hpow : ∀ j < t, ∀ u : F, u ^ p ≠ a j) (f : F) (c : ℕ → Fin p → F)
    (hnt : f ≠ 0 ∨ ∃ j < t, c j ≠ 0)
    (h0 : Nat.rec (motive := fun _ ↦ F) (f ^ p)
      (fun s acc ↦ acc * a s + nrm (a s) (c s) * b s) t = 0) :
    ∃ l : List (Fˣ × Fˣ), l.length ≤ t - 1 ∧
      ∑ j ∈ Finset.range t, of p (a j) * of p (b j) = (l.map fun q ↦ of p q.1 * of p q.2).sum := by
  classical
  have hp0 := hp.pos
  let Q : ℕ → Prop := fun s ↦ ∃ (f' : F) (c' : ℕ → Fin p → F),
    (f' ≠ 0 ∨ ∃ j < s, c' j ≠ 0) ∧ Nat.rec (motive := fun _ ↦ F) (f' ^ p)
      (fun s acc ↦ acc * a s + nrm (a s) (c' s) * b s) s = 0
  have hQ : ∃ s, Q s := ⟨t, f, c, hnt, h0⟩
  have hle : Nat.find hQ ≤ t := Nat.find_min' hQ ⟨f, c, hnt, h0⟩
  obtain ⟨f', c', hnt', h0'⟩ := Nat.find_spec hQ
  have ht'0 : Nat.find hQ ≠ 0 := by
    intro h; rw [h] at hnt' h0'
    rcases hnt' with hf | ⟨j, hj, _⟩
    · exact hf (pow_eq_zero_iff hp0.ne' |>.mp h0')
    · omega
  obtain ⟨u, hu⟩ := Nat.exists_eq_succ_of_ne_zero ht'0
  rw [hu] at hnt' h0'
  set N : ℕ → F := fun s ↦ Nat.rec (motive := fun _ ↦ F) (f' ^ p)
      (fun s acc ↦ acc * a s + nrm (a s) (c' s) * b s) s with hNdef
  have hN0 : N 0 = f' ^ p := rfl
  have hNs : ∀ s, N (s + 1) = N s * a s + nrm (a s) (c' s) * b s := fun _ ↦ rfl
  have h0u : N (u + 1) = 0 := h0'
  have hpu : ∀ v : F, v ^ p ≠ a u := hpow u (by omega)
  have htriv : ∀ s, (∀ j < s, c' j = 0) → f' = 0 → N s = 0 := by
    intro s
    induction s with
    | zero => intro _ hf; rw [hN0, hf, zero_pow hp0.ne']
    | succ s ih =>
      intro hc hf
      rw [hNs, ih (fun j hj ↦ hc j (by omega)) hf, hc s (by omega), hzero]; ring
  have hpre : f' ≠ 0 ∨ ∃ j < u, c' j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hf0, hc0⟩ := hcon
    have hz := htriv u hc0 hf0
    rw [hNs, hz, zero_mul, zero_add] at h0u
    have hn : nrm (a u) (c' u) = 0 := (mul_eq_zero.mp h0u).resolve_right (b u).ne_zero
    have hcu := hnd (a u) hpu _ hn
    rcases hnt' with hf | ⟨j, hj, hcj⟩
    · exact hf hf0
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact hcj (hc0 j hj')
      · exact hcj hcu
  have hNu : N u ≠ 0 := by
    intro hz
    exact Nat.find_min hQ (show u < Nat.find hQ by omega) ⟨f', c', hpre, hz⟩
  obtain ⟨x, hx, e, he⟩ := slot p hp0 nrm hrel a b f' c' N hN0 hNs u hNu
  have hn : nrm (a u) (c' u) ≠ 0 := by
    intro hn; rw [hNs, hn, zero_mul, add_zero] at h0u
    exact hNu ((mul_eq_zero.mp h0u).resolve_right (a u).ne_zero)
  have hrel' : of p (a u) * of p (b u) = of p (a u) * of p (Units.mk0 _ hn * b u) := by
    rw [of_mul, mul_add, hrel (a u) (c' u) hn, zero_add]
  have hneg : Units.mk0 _ hn * b u = -(Units.mk0 _ hNu * a u) := by
    ext
    have := h0u
    rw [hNs] at this
    simp only [Units.val_mul, Units.val_mk0, Units.val_neg]
    linear_combination this
  have hSu1 : ∑ j ∈ Finset.range (u + 1), of p (a j) * of p (b j) =
      x + of p (Units.mk0 _ hNu) * of p (e * (Units.mk0 _ hn * b u)⁻¹) := by
    rw [Finset.sum_range_succ, he, hrel', add_assoc, of_shift, hneg, of_mul_of_neg_self, add_zero]
  have hA := helper p hp0 f' N hN0 u x hx hNu (e * (Units.mk0 _ hn * b u)⁻¹)
  rw [← hSu1] at hA
  have hsplit : ∑ j ∈ Finset.range t, of p (a j) * of p (b j) =
      ∑ j ∈ Finset.range (u + 1), of p (a j) * of p (b j) +
      ∑ j ∈ Finset.Ico (u + 1) t, of p (a j) * of p (b j) := by
    rw [Finset.sum_range_add_sum_Ico _ (by omega)]
  rw [hsplit]
  exact SumLE_mono p (SumLE_add p hA (Ico_SumLE p a b (u + 1) t (by omega))) (by omega)

end MatzriR

namespace MatzriR

open MilnorK MatzriK

variable {F : Type*} [Field F] (p : ℕ)

theorem closed_form (a b : ℕ → Fˣ) (nrm : F → (Fin p → F) → F) (f : F) (c : ℕ → Fin p → F) :
    ∀ s, Nat.rec (motive := fun _ ↦ F) (f ^ p)
      (fun s acc ↦ acc * a s + nrm (a s) (c s) * b s) s =
      f ^ p * ∏ i ∈ Finset.range s, (a i : F) +
        ∑ j ∈ Finset.range s, nrm (a j) (c j) * b j * ∏ i ∈ Finset.Ico (j + 1) s, (a i : F) := by
  intro s
  induction s with
  | zero => simp
  | succ s ih =>
    show (Nat.rec (motive := fun _ ↦ F) (f ^ p)
      (fun s acc ↦ acc * a s + nrm (a s) (c s) * b s) s) * a s + nrm (a s) (c s) * b s = _
    rw [ih, Finset.prod_range_succ, Finset.sum_range_succ, Finset.Ico_self, Finset.prod_empty,
      add_mul, Finset.sum_mul]
    have : ∀ j ∈ Finset.range s, nrm (a j) (c j) * b j * (∏ i ∈ Finset.Ico (j + 1) s, (a i : F)) * a s =
        nrm (a j) (c j) * b j * ∏ i ∈ Finset.Ico (j + 1) (s + 1), (a i : F) := by
      intro j hj
      rw [Finset.prod_Ico_succ_top (by simp at hj; omega)]; ring
    rw [Finset.sum_congr rfl this]; ring

theorem count_reduce (hp : p.Prime) (m : ℕ) (nrm : F → (Fin p → F) → F)
    (hrel : ∀ (a : Fˣ) (c : Fin p → F) (h : nrm a c ≠ 0), of p a * of p (Units.mk0 _ h) = 0)
    (hzero : ∀ a : F, nrm a 0 = 0)
    (hnd : ∀ a : F, (∀ u : F, u ^ p ≠ a) → ∀ c, nrm a c = 0 → c = 0)
    (hpoly : ∀ a : F, ∃ Φ : MvPolynomial (Fin p) F, Φ.IsHomogeneous p ∧
      ∀ c, MvPolynomial.eval c Φ = nrm a c)
    (hT : ∀ (N : ℕ) (Φ : MvPolynomial (Fin N) F), Φ.IsHomogeneous p → p ^ m < N →
      ∃ v : Fin N → F, v ≠ 0 ∧ MvPolynomial.eval v Φ = 0)
    (a b : ℕ → Fˣ) (t : ℕ) (ht : p ^ m < t * p + 1) (hpow : ∀ j < t, ∀ u : F, u ^ p ≠ a j) :
    ∃ l : List (Fˣ × Fˣ), l.length ≤ t - 1 ∧
      ∑ j ∈ Finset.range t, of p (a j) * of p (b j) = (l.map fun q ↦ of p q.1 * of p q.2).sum := by
  classical
  choose Ψ hΨh hΨe using hpoly
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : MvPolynomial (Option (Fin t × Fin p)) F, Φ =
      MvPolynomial.C (∏ i ∈ Finset.range t, (a i : F)) * MvPolynomial.X none ^ p +
      ∑ j : Fin t, MvPolynomial.C ((b j : F) * ∏ i ∈ Finset.Ico ((j : ℕ) + 1) t, (a i : F)) *
        MvPolynomial.rename (fun l ↦ some (j, l)) (Ψ (a j : F)) := ⟨_, rfl⟩
  have h1 : (MvPolynomial.C (∏ i ∈ Finset.range t, (a i : F)) * MvPolynomial.X none ^ p :
      MvPolynomial (Option (Fin t × Fin p)) F).IsHomogeneous p := by
    have := (MvPolynomial.isHomogeneous_C (Option (Fin t × Fin p)) (∏ i ∈ Finset.range t, (a i : F))).mul
      ((MvPolynomial.isHomogeneous_X F (none : Option (Fin t × Fin p))).pow p)
    rwa [zero_add, one_mul] at this
  have h2 : (∑ j : Fin t, MvPolynomial.C ((b j : F) * ∏ i ∈ Finset.Ico ((j : ℕ) + 1) t, (a i : F)) *
      MvPolynomial.rename (fun l ↦ (some (j, l) : Option (Fin t × Fin p))) (Ψ (a j : F))).IsHomogeneous p := by
    apply MvPolynomial.IsHomogeneous.sum
    intro j _
    have := (MvPolynomial.isHomogeneous_C (Option (Fin t × Fin p))
      ((b j : F) * ∏ i ∈ Finset.Ico ((j : ℕ) + 1) t, (a i : F))).mul
      ((hΨh (a j : F)).rename_isHomogeneous (f := fun l ↦ (some (j, l) : Option (Fin t × Fin p))))
    rwa [zero_add] at this
  have hΦ : Φ.IsHomogeneous p := by rw [hΦdef]; exact h1.add h2
  set e := Fintype.equivFin (Option (Fin t × Fin p))
  have hcard : Fintype.card (Option (Fin t × Fin p)) = t * p + 1 := by simp
  obtain ⟨v, hv0, hv⟩ := hT _ (MvPolynomial.rename e Φ) hΦ.rename_isHomogeneous
    (by rw [hcard]; exact ht)
  rw [MvPolynomial.eval_rename] at hv
  set w : Option (Fin t × Fin p) → F := v ∘ e with hw
  set f := w none
  set c : ℕ → Fin p → F := fun j l ↦ if h : j < t then w (some (⟨j, h⟩, l)) else 0 with hc
  have hcj : ∀ j : Fin t, c j = fun l ↦ w (some (j, l)) := by
    intro j; funext l; simp [hc, j.isLt]
  have hval : Nat.rec (motive := fun _ ↦ F) (f ^ p)
      (fun s acc ↦ acc * a s + nrm (a s) (c s) * b s) t = 0 := by
    rw [closed_form, ← hv, hΦdef]
    simp only [map_add, map_mul, map_pow, map_sum, MvPolynomial.eval_C, MvPolynomial.eval_X,
      MvPolynomial.eval_rename, hΨe]
    rw [Finset.sum_range (fun j ↦ nrm (a j) (c j) * b j * ∏ i ∈ Finset.Ico (j + 1) t, (a i : F))]
    congr 1
    · ring
    · refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [hcj j]
      simp only [Function.comp_def]
      ring
  have hnt : f ≠ 0 ∨ ∃ j < t, c j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hf, hc0⟩ := hcon
    apply hv0
    funext i
    obtain ⟨i', rfl⟩ := e.surjective i
    show w i' = 0
    rcases i' with _ | ⟨j, l⟩
    · exact hf
    · have := congrFun (hc0 j j.isLt) l
      rw [hcj j] at this
      exact this
  exact zero_reduce p hp nrm hrel hzero hnd a b t hpow f c hnt hval

end MatzriR

namespace MatzriR

open MilnorK MatzriK

variable {F : Type*} [Field F] (p : ℕ)

theorem list_sum_range (l : List (Fˣ × Fˣ)) :
    (l.map fun q ↦ of p q.1 * of p q.2).sum = ∑ j ∈ Finset.range l.length,
      of p (l.getD j (1, 1)).1 * of p (l.getD j (1, 1)).2 := by
  induction l with
  | nil => simp
  | cons q l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp [add_comm]

theorem reduce_one (hp : p.Prime) (m : ℕ) (hm : 1 ≤ m) (nrm : F → (Fin p → F) → F)
    (hrel : ∀ (a : Fˣ) (c : Fin p → F) (h : nrm a c ≠ 0), of p a * of p (Units.mk0 _ h) = 0)
    (hzero : ∀ a : F, nrm a 0 = 0)
    (hnd : ∀ a : F, (∀ u : F, u ^ p ≠ a) → ∀ c, nrm a c = 0 → c = 0)
    (hpoly : ∀ a : F, ∃ Φ : MvPolynomial (Fin p) F, Φ.IsHomogeneous p ∧
      ∀ c, MvPolynomial.eval c Φ = nrm a c)
    (hT : ∀ (N : ℕ) (Φ : MvPolynomial (Fin N) F), Φ.IsHomogeneous p → p ^ m < N →
      ∃ v : Fin N → F, v ≠ 0 ∧ MvPolynomial.eval v Φ = 0)
    (l : List (Fˣ × Fˣ)) (hl : l.length = p ^ (m - 1)) :
    ∃ l' : List (Fˣ × Fˣ), l'.length ≤ p ^ (m - 1) - 1 ∧
      (l.map fun q ↦ of p q.1 * of p q.2).sum = (l'.map fun q ↦ of p q.1 * of p q.2).sum := by
  classical
  by_cases hpw : ∃ q ∈ l, ∃ u : F, u ^ p = q.1
  · obtain ⟨q, hq, u, hu⟩ := hpw
    have hu0 : u ≠ 0 := by
      intro h0; apply q.1.ne_zero; rw [← hu, h0, zero_pow hp.pos.ne']
    have hq0 : of p q.1 * of p q.2 = 0 := by
      have : q.1 = (Units.mk0 u hu0) ^ p := by ext; simp [hu]
      rw [this, of_pow_ell, zero_mul]
    refine ⟨l.erase q, by rw [List.length_erase_of_mem hq, hl], ?_⟩
    have hperm := ((List.perm_cons_erase hq).map fun q ↦ of p q.1 * of p q.2).sum_eq
    rw [hperm, List.map_cons, List.sum_cons, hq0, zero_add]
  · push Not at hpw
    have hpow : ∀ j < l.length, ∀ u : F, u ^ p ≠ (l.getD j (1, 1)).1 := by
      intro j hj u
      rw [List.getD_eq_getElem _ _ hj]
      exact hpw _ (List.getElem_mem hj) u
    have ht : p ^ m < l.length * p + 1 := by
      rw [hl, ← pow_succ, Nat.sub_add_cancel hm]; omega
    obtain ⟨l', hl', he⟩ := count_reduce p hp m nrm hrel hzero hnd hpoly hT
      (fun j ↦ (l.getD j (1, 1)).1) (fun j ↦ (l.getD j (1, 1)).2) l.length ht hpow
    refine ⟨l', by rw [← hl]; exact hl', ?_⟩
    rw [list_sum_range, he]

theorem main_bound (hp : p.Prime) (m : ℕ) (hm : 1 ≤ m) (nrm : F → (Fin p → F) → F)
    (hrel : ∀ (a : Fˣ) (c : Fin p → F) (h : nrm a c ≠ 0), of p a * of p (Units.mk0 _ h) = 0)
    (hzero : ∀ a : F, nrm a 0 = 0)
    (hnd : ∀ a : F, (∀ u : F, u ^ p ≠ a) → ∀ c, nrm a c = 0 → c = 0)
    (hpoly : ∀ a : F, ∃ Φ : MvPolynomial (Fin p) F, Φ.IsHomogeneous p ∧
      ∀ c, MvPolynomial.eval c Φ = nrm a c)
    (hT : ∀ (N : ℕ) (Φ : MvPolynomial (Fin N) F), Φ.IsHomogeneous p → p ^ m < N →
      ∃ v : Fin N → F, v ≠ 0 ∧ MvPolynomial.eval v Φ = 0) :
    ∀ n (l : List (Fˣ × Fˣ)), l.length = n → ∃ l' : List (Fˣ × Fˣ),
      l'.length ≤ p ^ (m - 1) - 1 ∧
      (l.map fun q ↦ of p q.1 * of p q.2).sum = (l'.map fun q ↦ of p q.1 * of p q.2).sum := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l hl
    have hK : 1 ≤ p ^ (m - 1) := Nat.one_le_pow _ _ hp.pos
    by_cases hn : n ≤ p ^ (m - 1) - 1
    · exact ⟨l, by omega, rfl⟩
    · set K := p ^ (m - 1)
      have htake : (l.take K).length = K := by rw [List.length_take]; omega
      obtain ⟨l₁, hl₁, he₁⟩ := reduce_one p hp m hm nrm hrel hzero hnd hpoly hT (l.take K) htake
      have hlen : (l₁ ++ l.drop K).length < n := by
        rw [List.length_append, List.length_drop]; omega
      obtain ⟨l', hl', he'⟩ := ih _ hlen (l₁ ++ l.drop K) rfl
      refine ⟨l', hl', ?_⟩
      rw [← he', ← List.take_append_drop K l, List.map_append, List.sum_append, he₁,
        List.take_append_drop, List.map_append, List.sum_append]

theorem list_sum_neg (l : List (Fˣ × Fˣ)) :
    ((l.map fun q ↦ (q.1⁻¹, q.2)).map fun q ↦ of p q.1 * of p q.2).sum +
      (l.map fun q ↦ of p q.1 * of p q.2).sum = 0 := by
  induction l with
  | nil => simp
  | cons q l ih =>
    simp only [List.map_cons, List.sum_cons]
    have h1 : of p q.1⁻¹ * of p q.2 + of p q.1 * of p q.2 = 0 := by
      rw [add_comm]; exact of_inv_mul p (of p q.2) q.1
    calc of p q.1⁻¹ * of p q.2 + ((l.map fun q ↦ (q.1⁻¹, q.2)).map fun q ↦ of p q.1 * of p q.2).sum +
          (of p q.1 * of p q.2 + (l.map fun q ↦ of p q.1 * of p q.2).sum)
        = (of p q.1⁻¹ * of p q.2 + of p q.1 * of p q.2) +
          (((l.map fun q ↦ (q.1⁻¹, q.2)).map fun q ↦ of p q.1 * of p q.2).sum +
            (l.map fun q ↦ of p q.1 * of p q.2).sum) := by abel
      _ = 0 := by rw [h1, ih, add_zero]

theorem grade_sum (x : MilnorK F p) (hx : x ∈ MilnorK.grade F p 2) :
    ∃ l : List (Fˣ × Fˣ), x = (l.map fun q ↦ of p q.1 * of p q.2).sum := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨s, rfl⟩ := hy
    exact ⟨[(s 0, s 1)], by simp [MilnorK.symbol, List.ofFn_succ]⟩
  | zero => exact ⟨[], by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨l, rfl⟩ := hy
    obtain ⟨l', rfl⟩ := hz
    exact ⟨l ++ l', by simp⟩
  | neg y _ hy =>
    obtain ⟨l, rfl⟩ := hy
    exact ⟨l.map fun q ↦ (q.1⁻¹, q.2), (eq_neg_of_add_eq_zero_left (list_sum_neg p l)).symm⟩

theorem list_sum_symbol (l : List (Fˣ × Fˣ)) :
    (l.map fun q ↦ of p q.1 * of p q.2).sum =
      ∑ i : Fin l.length, MilnorK.symbol p ![(l.get i).1, (l.get i).2] := by
  rw [← Fin.sum_univ_fun_getElem]
  simp [MilnorK.symbol_pair]

theorem bound_of (hp : p.Prime) (m : ℕ) (hm : 1 ≤ m) (nrm : F → (Fin p → F) → F)
    (hrel : ∀ (a : Fˣ) (c : Fin p → F) (h : nrm a c ≠ 0), of p a * of p (Units.mk0 _ h) = 0)
    (hzero : ∀ a : F, nrm a 0 = 0)
    (hnd : ∀ a : F, (∀ u : F, u ^ p ≠ a) → ∀ c, nrm a c = 0 → c = 0)
    (hpoly : ∀ a : F, ∃ Φ : MvPolynomial (Fin p) F, Φ.IsHomogeneous p ∧
      ∀ c, MvPolynomial.eval c Φ = nrm a c)
    (hT : ∀ (N : ℕ) (Φ : MvPolynomial (Fin N) F), Φ.IsHomogeneous p → p ^ m < N →
      ∃ v : Fin N → F, v ≠ 0 ∧ MvPolynomial.eval v Φ = 0) :
    p ^ (m - 1) - 1 ∈ MilnorK.symbolLengthBounds F p 2 := by
  intro x hx
  obtain ⟨l, rfl⟩ := grade_sum p x hx
  obtain ⟨l', hl', he⟩ := main_bound p hp m hm nrm hrel hzero hnd hpoly hT _ l rfl
  exact ⟨l'.length, hl', fun i ↦ ![(l'.get i).1, (l'.get i).2], by rw [he, list_sum_symbol]⟩

end MatzriR

/-- Matzri's bound for every prime `p` over `C(x_1, ..., x_m)`. -/
theorem matzri_bound (m : ℕ) (hm : 1 ≤ m) (p : ℕ) (hp : p.Prime) :
    p ^ (m - 1) - 1 ∈ MilnorK.symbolLengthBounds (MvRatFunc (Fin m) ℂ) p 2 := by
  have hp0 := hp.pos
  have := OMA.NormRel.charZero_of_complex (MvRatFunc (Fin m) ℂ)
  exact MatzriR.bound_of p hp m hm
    (fun a c ↦ Algebra.norm (MvRatFunc (Fin m) ℂ)
      (∑ l : Fin p, c l • (AdjoinRoot.root (Polynomial.X ^ p - Polynomial.C a)) ^ (l : ℕ)))
    (fun a c h ↦ OMA.NormRel.kummer_general (OMA.NormRel.exists_sqrt_neg_one_of_complex _) p hp a _ h)
    (fun a ↦ MatzriN.norm_zero' p hp0 a)
    (fun a ha c h ↦ MatzriN.norm_eq_zero' p hp a ha c h)
    (fun a ↦ MatzriN.exists_normPoly p hp0 a)
    (fun N Φ hΦ hN' ↦ OMA.TsenLang.tsen_lang m p N Φ hp0 hΦ hN')

end OMA.MatzriOdd

theorem OMA.solution : OMA.R_SymbolLengthMilnorKTheory_symbol_length_problem_variants_bounded_R1.H2 :=
  fun m p hm hp ↦ ⟨_, OMA.MatzriOdd.matzri_bound m (by omega) p hp⟩
