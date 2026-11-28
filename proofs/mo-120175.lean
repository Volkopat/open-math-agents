import OMAStatements.S_mo_120175

/-!
This is the characteristic-three instance of Peter Müller's elementary
construction for Lampe's equivalent question (MathOverflow https://mathoverflow.net/questions/6820). It simplifies the counterexample of Will Johnson,
Chieu-Minh Tran, Erik Walsberg, and Jinhe Ye, *Large implies henselian*,
arXiv:2508.10886v1, Proposition 10.4.

A maximal intermediate field omitting a chosen square root forces every
nonlinear separable irreducible polynomial to have even degree. A quintic
then attains every nonzero value, while the two factors have no roots.
-/

open Polynomial IntermediateField

namespace OMA.CofinitePolynomial

private theorem maximal_omitting {k E : Type*} [Field k] [Field E] [Algebra k E]
    (z : E) (hz : z ∉ (⊥ : IntermediateField k E)) :
    ∃ K : IntermediateField k E, z ∉ K ∧
      ∀ L : IntermediateField k E, K ≤ L → z ∉ L → L ≤ K := by
  let acceptable : Set (IntermediateField k E) := {K | z ∉ K}
  obtain ⟨K, _, hK⟩ := zorn_le_nonempty₀ acceptable (fun c hc hchain Y hY => by
    have : Nonempty c := ⟨⟨Y, hY⟩⟩
    let F (L : c) : IntermediateField k E := L.val
    have hdir : Directed (· ≤ ·) F := hchain.directedOn.directed_val
    refine ⟨⨆ L, F L, ?_, ?_⟩
    · intro hzsup
      have hzmem : z ∈ ⋃ L, (F L : Set E) := by
        rw [← IntermediateField.coe_iSup_of_directed hdir]
        exact hzsup
      obtain ⟨L, hL⟩ := Set.mem_iUnion.mp hzmem
      exact hc L.property hL
    · intro L hL
      exact le_iSup F ⟨L, hL⟩) ⊥ hz
  exact ⟨K, hK.1, fun L hle hav => hK.2 hav hle⟩

private theorem square_eq_sign {F : Type*} [Field F] {x z : F} (h : x^2 = z^2) :
    x = z ∨ x = -z := by
  have hw : (x - z) * (x + z) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hw with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (eq_neg_of_add_eq_zero_left h)

private theorem square_root_avoided {k E : Type*} [Field k] [Field E] [Algebra k E]
    (K : IntermediateField k E) (a : k) {z : E} (hz : z ∉ K)
    (hzsq : z ^ 2 = algebraMap k E a) :
    ∀ x : K, x ^ 2 ≠ algebraMap k K a := by
  intro x hx
  have hh : (x : E)^2 = z^2 := by
    rw [hzsq]
    rw [IsScalarTower.algebraMap_apply k K E]
    exact (map_pow (algebraMap K E) x 2).symm.trans (congrArg (algebraMap K E) hx)
  rcases square_eq_sign hh with he | he
  · exact hz (he ▸ x.property)
  · have hneg : -z ∈ K := he ▸ x.property
    exact hz (neg_mem_iff.mp hneg)

private theorem degree_even_of_maximal_omitting {k E : Type*} [Field k] [Field E]
    [Algebra k E] [IsSepClosed E] {K : IntermediateField k E} {z : E} {a : k}
    (hz : z ∉ K) (hzsq : z^2 = algebraMap k E a)
    (hmax : ∀ L : IntermediateField k E, K ≤ L → z ∉ L → L ≤ K)
    {p : K[X]} (hp : Irreducible p) (hsep : p.Separable) (hdeg : p.natDegree ≠ 1) :
    2 ∣ p.natDegree := by
  obtain ⟨x, hx⟩ := IsSepClosed.exists_aeval_eq_zero E p
    (degree_pos_of_irreducible hp).ne' hsep
  let L : IntermediateField K E := K⟮x⟯
  have hxl : x ∈ L := IntermediateField.mem_adjoin_simple_self K x
  have hxk : x ∉ K := by
    intro h
    let y : K := ⟨x, h⟩
    have he : algebraMap K E (p.eval y) = 0 := by
      rw [← Polynomial.aeval_algebraMap_apply_eq_algebraMap_eval]
      exact hx
    exact hp.not_isRoot_of_natDegree_ne_one hdeg
      ((algebraMap K E).injective (he.trans (map_zero _).symm))
  have hkl : K ≤ L.restrictScalars k := by
    intro y hy
    exact L.algebraMap_mem ⟨y, hy⟩
  have hzl : z ∈ L := by
    by_contra hav
    exact hxk (hmax (L.restrictScalars k) hkl hav hxl)
  let q : K[X] := X^2 - C (algebraMap k K a)
  have hqmon : q.Monic := monic_X_pow_sub_C _ (by decide)
  have hqdeg : q.natDegree = 2 := natDegree_X_pow_sub_C
  have hqirr : Irreducible q := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · simp [hqdeg]
    · intro y hy
      apply square_root_avoided K a hz hzsq y
      exact sub_eq_zero.mp (by simpa [q, IsRoot.def] using hy)
  have hqev : aeval z q = 0 := by
    simp only [q, map_sub, map_pow, aeval_X, aeval_C, hzsq]
    rw [← IsScalarTower.algebraMap_apply k K E, sub_self]
  have hminz : minpoly K z = q := (minpoly.eq_of_irreducible_of_monic hqirr hqev hqmon).symm
  have hintz : IsIntegral K z := ⟨q, hqmon, hqev⟩
  let p' := p * C p.leadingCoeff⁻¹
  have hp'mon : p'.Monic := monic_mul_leadingCoeff_inv hp.ne_zero
  have hp'irr : Irreducible p' := irreducible_mul_leadingCoeff_inv.mpr hp
  have hp'ev : aeval x p' = 0 := by simp [p', hx]
  have hminx : minpoly K x = p' := (minpoly.eq_of_irreducible_of_monic hp'irr hp'ev hp'mon).symm
  have hintx : IsIntegral K x := ⟨p', hp'mon, hp'ev⟩
  have hdvd := IntermediateField.finrank_dvd_of_le_right
    (IntermediateField.adjoin_simple_le_iff.mpr hzl)
  rw [IntermediateField.adjoin.finrank hintz, hminz, hqdeg,
    IntermediateField.adjoin.finrank hintx, hminx,
    natDegree_mul_leadingCoeff_inv _ hp.ne_zero] at hdvd
  exact hdvd

end OMA.CofinitePolynomial

open Polynomial IntermediateField

namespace OMA.CofinitePolynomial

private theorem transcendental_parameter_not_power {k : Type*} [Field k]
    (m : ℕ) (hm : m = 2 ∨ m = 3) (x : RatFunc k) :
    x ^ m ≠ RatFunc.X := by
  intro hx
  have hx0 : x ≠ 0 := by
    intro h
    exact RatFunc.X_ne_zero (show (RatFunc.X : RatFunc k) = 0 by rw [← hx, h, zero_pow]; omega)
  have pow_degree (n : ℕ) : (x ^ n).intDegree = (n : ℤ) * x.intDegree := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, RatFunc.intDegree_mul (pow_ne_zero _ hx0) hx0, ih, Nat.cast_succ]
      ring
  have h := pow_degree m
  rw [hx, RatFunc.intDegree_X] at h
  rcases hm with rfl | rfl <;> norm_num at h <;> omega

private theorem no_cube_in_separable {k E : Type*} [Field k] [Field E]
    [Algebra k E] [CharP k 3] [Algebra.IsSeparable k E] (a : k)
    (ha : ∀ x : k, x ^ 3 ≠ a) (x : E) : x ^ 3 ≠ algebraMap k E a := by
  intro hx
  let : Fact (Nat.Prime 3) := ⟨by decide⟩
  have heq := IntermediateField.adjoin_simple_eq_adjoin_pow_expChar_of_isSeparable' k E x 3
  have hlo : k⟮x ^ 3⟯ ≤ (⊥ : IntermediateField k E) :=
    adjoin_simple_le_iff.mpr (mem_bot.mpr ⟨a, hx.symm⟩)
  have hm : x ∈ (⊥ : IntermediateField k E) := (heq ▸ mem_adjoin_simple_self k x : x ∈ k⟮x^3⟯) |> hlo
  obtain ⟨y, hy⟩ := mem_bot.mp hm
  exact ha y ((algebraMap k E).injective (by rw [map_pow, hy, hx]))

private theorem odd_separable_has_root {K : Type*} [Field K]
    (hK : ∀ p : K[X], Irreducible p → p.Separable → p.natDegree ≠ 1 → 2 ∣ p.natDegree)
    (p : K[X]) (hsep : p.Separable) (hodd : Odd p.natDegree) :
    ∃ x : K, p.eval x = 0 := by
  generalize hn : p.natDegree = n at hodd
  induction n using Nat.strong_induction_on generalizing p with
  | h n ih =>
    by_cases hi : Irreducible p
    · have h1 : p.natDegree = 1 := by
        by_contra hne
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (hn ▸ hK p hi hsep hne))
      exact exists_root_of_degree_eq_one (by rw [degree_eq_natDegree hi.ne_zero, h1]; rfl)
    · have hpos : 0 < p.natDegree := by rw [hn]; exact hodd.pos
      have hu := not_isUnit_of_natDegree_pos p hpos
      rw [irreducible_iff] at hi
      push Not at hi
      obtain ⟨q, r, hqr, hqu, hru⟩ := hi hu
      have hqr0 : q * r ≠ 0 := by
        rw [← hqr]
        exact ne_zero_of_natDegree_gt hpos
      have hpositive (a : K[X]) (ha : a ≠ 0) (hau : ¬IsUnit a) : 0 < a.natDegree := by
        apply Nat.pos_of_ne_zero
        intro hd
        have hc : C (a.coeff 0) = a := (eq_C_of_natDegree_eq_zero hd).symm
        exact hau (hc ▸ isUnit_C.mpr (by
          apply Ne.isUnit
          intro hh
          exact ha (by rw [← hc, hh, map_zero])))
      have hq0 : q ≠ 0 := left_ne_zero_of_mul hqr0
      have hr0 : r ≠ 0 := right_ne_zero_of_mul hqr0
      have hqpos := hpositive q hq0 hqu
      have hrpos := hpositive r hr0 hru
      have hs : q.natDegree + r.natDegree = n := by
        rwa [hqr, natDegree_mul hq0 hr0] at hn
      by_cases hoq : Odd q.natDegree
      · obtain ⟨x, hx⟩ := ih q.natDegree (by omega) q (hsep.of_dvd ⟨r, hqr⟩) rfl hoq
        exact ⟨x, by rw [hqr, eval_mul, hx, zero_mul]⟩
      · have hor : Odd r.natDegree := by
          rw [← hs, Nat.odd_add'] at hodd
          exact hodd.mpr (Nat.not_odd_iff_even.mp hoq)
        obtain ⟨x, hx⟩ := ih r.natDegree (by omega) r (hsep.of_dvd ⟨q, hqr.trans (mul_comm _ _)⟩)
          rfl hor
        exact ⟨x, by rw [hqr, eval_mul, hx, mul_zero]⟩

end OMA.CofinitePolynomial

open Polynomial IntermediateField

namespace OMA.CofinitePolynomial

private noncomputable def examplePolynomial {K : Type*} [Field K] (t : K) : K[X] :=
  (X ^ 2 - C t) * (X ^ 3 - C t)

private theorem example_separable {K : Type*} [Field K] [CharP K 3]
    {t c : K} (hc : c ≠ 0) (htc : t^2 ≠ c) : (examplePolynomial t - C c).Separable := by
  have hn2 : (2 : K) ≠ 0 := by
    have h := CharP.cast_eq_zero_iff K 3 2
    norm_num at h
    exact h
  let b : K[X] := X ^ 3 - C t
  let p : K[X] := examplePolynomial t - C c
  have hp1 : p = (X ^ 2 - C t) * b - C c := rfl
  have hd : p.derivative = C 2 * X * b := by
    have h3 : (3 : K) = 0 := CharP.cast_eq_zero K 3
    simp only [hp1, b, derivative_sub, derivative_mul, derivative_C, derivative_X_pow,
      Nat.cast_ofNat, h3, map_zero, zero_mul, sub_zero, mul_zero, add_zero]
    ring
  have hC : IsCoprime p (C (2 : K)) :=
    ⟨0, C (2 : K)⁻¹, by rw [zero_mul, zero_add, ← map_mul, inv_mul_cancel₀ hn2, map_one]⟩
  have hX : IsCoprime p X := by
    let q : K[X] := X ^ 4 - C t * X ^ 2 - C t * X
    have he : p = X * q + C (t^2-c) := by
      rw [hp1]
      simp only [b, q, map_sub, map_pow]
      ring
    have hz : C ((t^2-c)⁻¹) * C (t^2-c) = (1 : K[X]) := by
      rw [← map_mul, inv_mul_cancel₀ (sub_ne_zero.mpr htc), map_one]
    exact ⟨C ((t^2-c)⁻¹), -(C ((t^2-c)⁻¹) * q), by rw [he]; linear_combination hz⟩
  have hb : IsCoprime p b := by
    have hz : C c⁻¹ * C c = (1 : K[X]) := by rw [← map_mul, inv_mul_cancel₀ hc, map_one]
    exact ⟨-C c⁻¹, C c⁻¹ * (X^2-C t), by rw [hp1]; linear_combination hz⟩
  rw [separable_def, hd]
  exact (hC.mul_right hX).mul_right hb

end OMA.CofinitePolynomial

-- This section is concatenated after the prerequisite lemmas.

namespace OMA.CofinitePolynomial

private theorem example_degree {K : Type*} [Field K] (t c : K) :
    (examplePolynomial t - C c).natDegree = 5 := by
  rw [natDegree_sub_C, examplePolynomial,
    natDegree_mul (X_pow_sub_C_ne_zero (by decide) t) (X_pow_sub_C_ne_zero (by decide) t),
    natDegree_X_pow_sub_C, natDegree_X_pow_sub_C]

private theorem example_omits_zero {K : Type*} [Field K] {t : K}
    (hsq : ∀ x : K, x ^ 2 ≠ t) (hcu : ∀ x : K, x ^ 3 ≠ t) :
    ¬ Function.Surjective (fun x : K => (examplePolynomial t).eval x) := by
  intro h
  obtain ⟨x, hx⟩ := h 0
  simp only [examplePolynomial, eval_mul, eval_sub, eval_pow, eval_X, eval_C, mul_eq_zero,
    sub_eq_zero] at hx
  exact hx.elim (hsq x) (hcu x)

private theorem example_cofinite {K : Type*} [Field K] [CharP K 3] {t : K}
    (hK : ∀ p : K[X], Irreducible p → p.Separable → p.natDegree ≠ 1 → 2 ∣ p.natDegree) :
    ((Set.range (fun x : K => (examplePolynomial t).eval x))ᶜ).Finite := by
  apply (Set.finite_singleton (0 : K)).subset
  intro x hx
  apply Set.mem_singleton_iff.mpr
  by_contra hx0
  apply hx
  by_cases hxt : t^2 = x
  · exact ⟨0, by simpa [examplePolynomial] using (sq t).symm.trans hxt⟩
  · obtain ⟨y, hy⟩ := odd_separable_has_root hK _ (example_separable hx0 hxt)
      (by rw [example_degree]; decide)
    exact ⟨y, by simpa only [eval_sub, eval_C, sub_eq_zero] using hy⟩

private theorem exists_field_with_cofinite_example :
    ∃ (K : Type) (_ : Field K) (_ : Infinite K), ∃ f : K[X],
      ¬ Function.Surjective (fun x => f.eval x) ∧
        ((Set.range (fun x => f.eval x))ᶜ).Finite := by
  let k := RatFunc (ZMod 3)
  let E := SeparableClosure k
  let t : k := RatFunc.X
  have : CharP k 3 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 3) k).injective 3
  have : CharP E 3 := charP_of_injective_algebraMap (algebraMap k E).injective 3
  have hnt : ∀ x : k, x ^ 2 ≠ t := transcendental_parameter_not_power 2 (Or.inl rfl)
  have hn2 : (2 : E) ≠ 0 := by
    simpa using (CharP.cast_eq_zero_iff E 3 2).not.mpr (by decide : ¬ 3 ∣ 2)
  have : NeZero (2 : E) := ⟨hn2⟩
  obtain ⟨z, hz⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap k E t) 2
  have hzbot : z ∉ (⊥ : IntermediateField k E) := by
    intro h
    obtain ⟨y, hy⟩ := mem_bot.mp h
    exact hnt y ((algebraMap k E).injective (by rw [map_pow, hy, hz]))
  obtain ⟨K, hzK, hmax⟩ := maximal_omitting z hzbot
  have : CharP K 3 := charP_of_injective_algebraMap (algebraMap k K).injective 3
  let a := algebraMap k K t
  have hsq := square_root_avoided K t hzK hz
  have hcu (x : K) : x ^ 3 ≠ a := by
    intro hx
    apply no_cube_in_separable t (transcendental_parameter_not_power 3 (Or.inr rfl)) (x : E)
    rw [IsScalarTower.algebraMap_apply k K E]
    exact (map_pow (algebraMap K E) x 3).symm.trans (congrArg (algebraMap K E) hx)
  have hK (p : K[X]) (hp : Irreducible p) (hsep : p.Separable) (hd : p.natDegree ≠ 1) :
      2 ∣ p.natDegree := degree_even_of_maximal_omitting hzK hz hmax hp hsep hd
  have : Infinite k := Infinite.of_injective
    (fun n : ℕ => algebraMap (Polynomial (ZMod 3)) k (X ^ n))
    (by
      intro m n h
      have h' := RatFunc.algebraMap_injective (ZMod 3) h
      simpa using congrArg natDegree h')
  have : Infinite K := Infinite.of_injective (algebraMap k K) (algebraMap k K).injective
  exact ⟨K, inferInstance, inferInstance, examplePolynomial a, example_omits_zero hsq hcu,
    example_cofinite hK⟩

end OMA.CofinitePolynomial

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_120175.main) := by
  intro h
  obtain ⟨K, hfield, hinf, f, hfn, hfc⟩ := OMA.CofinitePolynomial.exists_field_with_cofinite_example
  exact hfc.not_infinite (@h K hfield hinf f hfn)
