import FormalConjectures.Arxiv.«0805.3777».TensorRank

/-!
# Generic rank of cubic tensors

The rank predicted by the parameter count is attained for cubic tensors of size other
than three in Thomas Lickteig, *Typical tensorial rank*, Linear Algebra Appl. **69**
(1985), 95–120, Theorem 4.4 and Corollary 4.5,
https://doi.org/10.1016/0024-3795(85)90070-9.

The Lean proof establishes the lower bound in every positive dimension by covering
low-rank tensors with finitely many normalized polynomial charts. For the upper bound it
passes from a surjective tangent map to algebraic independence, then uses Chevalley and
the Nullstellensatz to get an open dense set of actual decompositions. Explicit tangent
configurations settle the allowed dimensions through eight.

From side nine on a spanning tangent configuration is produced by induction. The statement
is generalised to boxes carrying tangent points and single lines; a box is cut along a side
and the tangent points of each half are seen by the other half as lines, as in the
splitting method of Bürgisser–Clausen–Shokrollahi and Abo–Ottaviani–Peterson,
*Induction for secant varieties of Segre varieties*, Trans. Amer. Math. Soc. **361** (2009).
For side eleven no cut of a single side works: the dimension count leaves only the cut
into thicknesses one and ten, and there the thin slab is not filled. So the first step cuts
two sides at once and lets a few points straddle two cells; such a point sends one of its
lines to the diagonally opposite cell. The four cells are cut into
slabs, bars and finitely many kinds of cells of side at most eighteen, and each of those is
reduced by an explicit tree of cuts to boxes of thickness one and one box with twelve
entries.
-/

namespace OMA.Cube

open Arxiv.«0805.3777»
open scoped Arxiv.«0805.3777»
open MvPolynomial

abbrev Triple (n : ℕ) := Fin n × Fin n × Fin n

def cubeIndex {n : ℕ} (t : Triple n) : HolorIndex [n,n,n] :=
  ⟨[t.1, t.2.1, t.2.2], .cons t.1.isLt (.cons t.2.1.isLt (.cons t.2.2.isLt .nil))⟩

private theorem cubeIndex_bijective (n : ℕ) : Function.Bijective (@cubeIndex n) := by
  constructor
  · rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ h
    simpa [cubeIndex, Subtype.ext_iff, Fin.ext_iff] using congrArg Subtype.val h
  · rintro ⟨l,h⟩
    cases h with
    | cons hi h =>
      cases h with
      | cons hj h =>
        cases h with
        | cons hk h =>
          cases h
          exact ⟨(⟨_,hi⟩,⟨_,hj⟩,⟨_,hk⟩), rfl⟩

noncomputable def indexEquiv (n : ℕ) : Triple n ≃ HolorIndex [n,n,n] :=
  Equiv.ofBijective cubeIndex (cubeIndex_bijective n)

def vectorIndex {n : ℕ} (i : Fin n) : HolorIndex [n] := ⟨[i], .cons i.isLt .nil⟩

abbrev Factors (n : ℕ) := (Fin n → ℂ) × (Fin n → ℂ) × (Fin n → ℂ)

def term {n : ℕ} (v : Factors n) (t : Triple n) : ℂ := v.1 t.1 * v.2.1 t.2.1 * v.2.2 t.2.2

def secant {n r : ℕ} (v : Fin r → Factors n) (t : Triple n) : ℂ := ∑ k, term (v k) t

private theorem rankOne_factors {n : ℕ} {T : Holor ℂ [n,n,n]} (h : Holor.CPRankMax1 T) :
    ∃ v : Factors n, ∀ t, T (cubeIndex t) = term v t := by
  cases h with
  | cons a _ h =>
    cases h with
    | cons b _ h =>
      cases h with
      | cons c d h =>
        cases h with
        | nil =>
          refine ⟨(fun i => a (vectorIndex i), fun j => b (vectorIndex j),
            fun k => c (vectorIndex k) * d ⟨[], .nil⟩), ?_⟩
          intro t
          exact (mul_assoc _ _ _).symm

private theorem rankMax_factors {n r : ℕ} {T : Holor ℂ [n,n,n]} (h : Holor.CPRankMax r T) :
    ∃ v : Fin r → Factors n, ∀ t, T (cubeIndex t) = secant v t := by
  induction r generalizing T with
  | zero =>
    cases h
    exact ⟨Fin.elim0, fun t => by simp [secant]; rfl⟩
  | succ r ih =>
    cases h with
    | succ _ A B hA hB =>
      obtain ⟨a,ha⟩ := rankOne_factors hA
      obtain ⟨b,hb⟩ := ih hB
      refine ⟨Fin.cons a b, fun t => ?_⟩
      change A _ + B _ = _
      simp [secant, Fin.sum_univ_succ, ha, hb]

/-- A chart fixes a pivot coordinate to one in each of the first two factors. -/
abbrev Pivots (n r : ℕ) := Fin r → Fin n × Fin n

abbrev Variables {n r : ℕ} (p : Pivots n r) :=
  (k : Fin r) × ({i : Fin n // i ≠ (p k).1} ⊕ {j : Fin n // j ≠ (p k).2} ⊕ Fin n)

private noncomputable def chart {n r : ℕ} (p : Pivots n r) (t : Triple n) :
    MvPolynomial (Variables p) ℂ :=
  ∑ k, (if h : t.1 = (p k).1 then 1 else X ⟨k, .inl ⟨t.1,h⟩⟩) *
    (if h : t.2.1 = (p k).2 then 1 else X ⟨k, .inr (.inl ⟨t.2.1,h⟩)⟩) *
    X ⟨k, .inr (.inr t.2.2)⟩

private theorem pickPivot {n : ℕ} (hn : 0 < n) (v : Fin n → ℂ) :
    ∃ p : Fin n, ∀ i, (if i = p then 1 else v i / v p) * v p = v i := by
  classical
  by_cases h : ∃ i, v i ≠ 0
  · obtain ⟨p,hp⟩ := h
    refine ⟨p, fun i => ?_⟩
    split_ifs with hi
    · simp [hi]
    · exact div_mul_cancel₀ _ hp
  · push Not at h
    exact ⟨⟨0,hn⟩, by simp [h]⟩

private theorem secant_in_chart {n r : ℕ} (hn : 0 < n) (v : Fin r → Factors n) :
    ∃ (p : Pivots n r) (x : Variables p → ℂ),
      ∀ t, secant v t = eval x (chart p t) := by
  classical
  choose a ha using fun k => pickPivot hn (v k).1
  choose b hb using fun k => pickPivot hn (v k).2.1
  let p : Pivots n r := fun k => (a k,b k)
  let x : Variables p → ℂ := fun ⟨k,s⟩ => match s with
    | .inl i => (v k).1 i / (v k).1 (a k)
    | .inr (.inl j) => (v k).2.1 j / (v k).2.1 (b k)
    | .inr (.inr l) => (v k).1 (a k) * (v k).2.1 (b k) * (v k).2.2 l
  refine ⟨p, x, fun t => ?_⟩
  simp only [secant, chart, map_sum, map_mul]
  apply Finset.sum_congr rfl
  intro k _
  have A := ha k t.1
  have B := hb k t.2.1
  dsimp [p]
  split_ifs at * <;> simp only [map_one, eval_X, x, term] <;>
    (conv_lhs => rw [← A, ← B]) <;> ac_rfl

private theorem chart_relation {n r : ℕ} (hn : 0 < n) (hr : (3 * n - 2) * r < n ^ 3)
    (p : Pivots n r) : ∃ q : MvPolynomial (Triple n) ℂ, q ≠ 0 ∧ aeval (chart p) q = 0 := by
  classical
  by_contra! h
  have hi : AlgebraicIndependent ℂ (chart p) :=
    algebraicIndependent_iff.mpr fun q hq => by
      by_contra hne
      exact h q hne hq
  have hb := hi.cardinalMk_le_trdeg
  rw [MvPolynomial.trdeg_of_isDomain, Cardinal.lift_id, Cardinal.mk_fintype,
    Cardinal.mk_fintype] at hb
  have hb' : Fintype.card (Triple n) ≤ Fintype.card (Variables p) := by exact_mod_cast hb
  have hk (i : Fin n) : Fintype.card {j : Fin n // j ≠ i} = n - 1 := by
    rw [Fintype.card_subtype_compl (fun j => j = i)]
    simp
  have he : (n - 1) + ((n - 1) + n) = 3 * n - 2 := by omega
  simp [Triple, Variables, hk, he] at hb'
  apply (Nat.not_le_of_lt hr)
  simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hb'

/-- All sums with a subcritical number of terms satisfy one nonzero polynomial equation. -/
theorem secant_relation {n r : ℕ} (hn : 0 < n) (hr : (3 * n - 2) * r < n ^ 3) :
    ∃ q : MvPolynomial (Triple n) ℂ, q ≠ 0 ∧ ∀ v : Fin r → Factors n, eval (secant v) q = 0 := by
  classical
  choose q hq hrel using chart_relation hn hr
  refine ⟨∏ p, q p, Finset.prod_ne_zero_iff.mpr (fun p _ => hq p), fun v => ?_⟩
  obtain ⟨p,x,hx⟩ := secant_in_chart hn v
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ p)
  have he := congrArg (aeval x) (hrel p)
  rw [comp_aeval_apply, map_zero] at he
  simpa only [aeval_eq_eval, ← hx] using he

private theorem polynomial_open_dense {ι : Type} [Fintype ι] {q : MvPolynomial ι ℂ} (hq : q ≠ 0) :
    IsOpen {x : ι → ℂ | eval x q ≠ 0} ∧ Dense {x : ι → ℂ | eval x q ≠ 0} := by
  have ha := AnalyticOnNhd.eval_mvPolynomial q
  refine ⟨isOpen_ne_fun (continuousOn_univ.mp ha.continuousOn) continuous_const, dense_iff_inter_open.mpr ?_⟩
  rintro U hU ⟨u,hu⟩
  by_contra! hempty
  have hz : (fun x => eval x q) =ᶠ[nhds u] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hu] with x hx
    by_contra hne
    exact Set.not_nonempty_empty (hempty ▸ (show (U ∩ {x | eval x q ≠ 0}).Nonempty from ⟨x,hx,hne⟩))
  have he := ha.eq_of_eventuallyEq analyticOnNhd_const hz
  exact hq (MvPolynomial.funext fun x => by simpa using congrFun he x)


private theorem constructible_eventually {X : Type} [TopologicalSpace X] {g : X}
    (hg : IsGenericPoint g Set.univ) {S : Set X} (hS : Topology.IsConstructible S) :
    ∀ᶠ x in nhds g, x ∈ S ↔ g ∈ S := by
  induction hS using Topology.IsConstructible.empty_union_induction with
  | open_retrocompact U hU _ =>
    by_cases h : g ∈ U
    · filter_upwards [hU.mem_nhds h] with x hx using iff_of_true hx h
    · have e : U = ∅ := Set.not_nonempty_iff_eq_empty.mp fun hne =>
        h ((hg.mem_open_set_iff hU).mpr (by simpa using hne))
      simp [e]
  | union s _ t _ hs ht =>
    filter_upwards [hs,ht] with x hx hy using or_congr hx hy
  | compl s _ hs =>
    filter_upwards [hs] with x hx using not_congr hx

/-- Chevalley's theorem on prime spectra and the Nullstellensatz on closed points
give a principal open subset of the image of a dominant polynomial map. -/
theorem dominant_image {ι κ : Type} [Fintype ι] [Fintype κ]
    (f : ι → MvPolynomial κ ℂ) (hi : AlgebraicIndependent ℂ f) :
    ∃ q : MvPolynomial ι ℂ, q ≠ 0 ∧
      ∀ y, eval y q ≠ 0 → ∃ x, ∀ i, eval x (f i) = y i := by
  classical
  let φ := (aeval (R := ℂ) f).toRingHom
  let g : PrimeSpectrum (MvPolynomial ι ℂ) := ⟨⊥, inferInstance⟩
  have hg : IsGenericPoint g Set.univ := by
    rw [isGenericPoint_def, PrimeSpectrum.closure_singleton]
    exact PrimeSpectrum.zeroLocus_bot
  have hφ : φ.FinitePresentation := by
    apply RingHom.FinitePresentation.of_finiteType.mp
    apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap ℂ (MvPolynomial ι ℂ))
    have e : φ.comp (algebraMap ℂ (MvPolynomial ι ℂ)) = algebraMap ℂ (MvPolynomial κ ℂ) :=
      (aeval f).comp_algebraMap
    rw [e]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  let S := Set.range (PrimeSpectrum.comap φ)
  have hgS : g ∈ S := by
    refine ⟨⟨⊥, inferInstance⟩, PrimeSpectrum.ext ?_⟩
    change RingHom.ker φ = ⊥
    exact (RingHom.injective_iff_ker_eq_bot φ).mp hi
  have hS : S ∈ nhds g := by
    filter_upwards [constructible_eventually hg (PrimeSpectrum.isConstructible_range_comap hφ)]
      with x hx using hx.mpr hgS
  obtain ⟨_,⟨q,rfl⟩,hq,hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.mem_nhds_iff.mp hS
  refine ⟨q, (PrimeSpectrum.mem_basicOpen q g).mp hq, fun y hy => ?_⟩
  have hy' : pointToPoint (k := ℂ) y ∈ PrimeSpectrum.basicOpen q := by
    change q ∉ vanishingIdeal ℂ {y}
    rwa [mem_vanishingIdeal_singleton_iff]
  obtain ⟨P,hP⟩ := hsub hy'
  obtain ⟨M,hM,hPM⟩ := P.asIdeal.exists_le_maximal P.isPrime.ne_top
  obtain ⟨x,hx⟩ := eq_vanishingIdeal_singleton_of_isMaximal ℂ hM
  refine ⟨x,fun i => ?_⟩
  have hm : X i - C (y i) ∈ (pointToPoint (k := ℂ) y).asIdeal :=
    (mem_vanishingIdeal_singleton_iff _ _).mpr (by simp)
  rw [← hP] at hm
  have hz := hPM (Ideal.mem_comap.mp hm)
  rw [hx, mem_vanishingIdeal_singleton_iff] at hz
  simpa [φ, sub_eq_zero] using hz


abbrev predicted (n : ℕ) := n ^ 3 ⌈/⌉ (3 * n - 2)

/-- A single nonzero polynomial excludes every cube below the dimension bound. -/
theorem lower_polynomial {n : ℕ} (hn : 0 < n) :
    ∃ q : MvPolynomial (Triple n) ℂ, q ≠ 0 ∧
      ∀ T : Holor ℂ [n,n,n], eval (fun t => T (cubeIndex t)) q ≠ 0 → predicted n ≤ T.cprank := by
  classical
  have hr (r : Fin (predicted n)) : (3 * n - 2) * r.val < n ^ 3 := by
    by_contra! h
    exact r.isLt.not_ge ((ceilDiv_le_iff_le_mul (by omega : 0 < 3 * n - 2)).mpr h)
  choose q hq hrel using fun r => secant_relation hn (hr r)
  refine ⟨∏ r, q r, Finset.prod_ne_zero_iff.mpr (fun r _ => hq r), fun T hT => ?_⟩
  by_contra! h
  let r : Fin (predicted n) := ⟨T.cprank, h⟩
  have hmax : Holor.CPRankMax T.cprank T := Nat.find_spec (p := fun k => Holor.CPRankMax k T) _
  obtain ⟨v,hv⟩ := rankMax_factors hmax
  apply hT
  rw [map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ r)
  simpa only [hv] using (hrel r v)

/-- The parameter count bounds any generic rank, even in the exceptional dimension three. -/
theorem generic_lower_bound {n r : ℕ} (hn : 0 < n) (h : IsGenericRank [n,n,n] r) :
    predicted n ≤ r := by
  obtain ⟨U,hU,hUd,hUr⟩ := h
  obtain ⟨q,hq,hL⟩ := lower_polynomial hn
  let e : Holor ℂ [n,n,n] ≃ₜ (Triple n → ℂ) :=
    (Homeomorph.piCongrLeft (Y := fun _ => ℂ) (indexEquiv n)).symm
  have hd := (polynomial_open_dense hq).2.preimage e.isOpenMap
  obtain ⟨T,hTU,hTq⟩ := hd.inter_open_nonempty U hU hUd.nonempty
  exact hUr T hTU ▸ hL T hTq

private noncomputable def oneDim {n : ℕ} (a : Fin n → ℂ) : Holor ℂ [n] :=
  Function.extend vectorIndex a (fun _ => 0)

private theorem oneDim_apply {n : ℕ} (a : Fin n → ℂ) (i : Fin n) :
    oneDim a (vectorIndex i) = a i := by
  apply Function.Injective.extend_apply
  intro i j hij
  simpa [vectorIndex, Fin.ext_iff] using congrArg Subtype.val hij

private theorem factors_rankMax {n r : ℕ} (v : Fin r → Factors n)
    (T : Holor ℂ [n,n,n]) (hT : ∀ t, T (cubeIndex t) = secant v t) :
    Holor.CPRankMax r T := by
  classical
  let A (k : Fin r) := Holor.mul (oneDim (v k).1)
    (Holor.mul (oneDim (v k).2.1) (Holor.mul (oneDim (v k).2.2) (fun _ : HolorIndex [] => (1 : ℂ))))
  have hA (k) : Holor.CPRankMax 1 (A k) :=
    Holor.cprankMax_1 (.cons _ _ (.cons _ _ (.cons _ _ (.nil _))))
  have he : T = ∑ k, A k := by
    funext i
    obtain ⟨t,rfl⟩ := (cubeIndex_bijective n).2 i
    rw [hT]
    change ∑ k, term (v k) t = (∑ k, (A k : HolorIndex [n,n,n] → ℂ)) (cubeIndex t)
    apply Eq.trans _ ((Finset.sum_apply (cubeIndex t) Finset.univ
      (fun k => (A k : HolorIndex [n,n,n] → ℂ))).symm)
    apply Finset.sum_congr rfl
    intro k _
    change _ = oneDim _ (vectorIndex t.1) * (oneDim _ (vectorIndex t.2.1) *
      (oneDim _ (vectorIndex t.2.2) * 1))
    simp [oneDim_apply, term, mul_assoc]
  rw [he]
  simpa using Holor.cprankMax_sum (n := 1) Finset.univ A (fun k _ => hA k)

/-- The three vector factors of each of the r summands are independent parameters. -/
abbrev Slots (n r : ℕ) := Fin r × Fin 3 × Fin n

private noncomputable def polynomials (n r : ℕ) (t : Triple n) : MvPolynomial (Slots n r) ℂ :=
  ∑ k, X (k,0,t.1) * X (k,1,t.2.1) * X (k,2,t.2.2)

def parametrization {n r : ℕ} (z : Slots n r → ℂ) : Triple n → ℂ :=
  secant (fun k => (fun i => z (k,0,i), fun j => z (k,1,j), fun l => z (k,2,l)))

private theorem eval_polynomials {n r : ℕ} (z : Slots n r → ℂ) (t : Triple n) :
    eval z (polynomials n r t) = parametrization z t := by
  simp [polynomials, parametrization, secant, term]

private theorem independent_of_submersion {n r : ℕ} {z : Slots n r → ℂ}
    {D : (Slots n r → ℂ) →L[ℂ] (Triple n → ℂ)} (hd : HasStrictFDerivAt parametrization D z)
    (hs : Function.Surjective D) : AlgebraicIndependent ℂ (polynomials n r) := by
  classical
  apply algebraicIndependent_iff.mpr
  intro q hq
  by_contra hn
  have him : Set.range (@parametrization n r) ∈ nhds (parametrization z) := by
    rw [← hd.map_nhds_eq_of_surj (LinearMap.range_eq_top.mpr hs)]
    exact Filter.range_mem_map
  have hp : ∀ᶠ y in nhds (parametrization z), eval y q = 0 := by
    filter_upwards [him] with y hy
    obtain ⟨x,rfl⟩ := hy
    have he := congrArg (aeval x) hq
    rw [comp_aeval_apply, map_zero] at he
    simpa only [aeval_eq_eval, eval_polynomials] using he
  have he := (AnalyticOnNhd.eval_mvPolynomial q).eq_of_eventuallyEq analyticOnNhd_const hp
  exact hn (MvPolynomial.funext fun x => by simpa using congrFun he x)


private noncomputable def projection {n r : ℕ} (i : Slots n r) :
    (Slots n r → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj i

/-- The linear map whose columns are the three families of tangent tensors. -/
noncomputable def tangentMap {n r : ℕ} (z : Slots n r → ℂ) :
    (Slots n r → ℂ) →L[ℂ] (Triple n → ℂ) :=
  ContinuousLinearMap.pi fun t => ∑ k,
    ((z (k,0,t.1) * z (k,1,t.2.1)) • projection (k,2,t.2.2) +
    z (k,2,t.2.2) • (z (k,0,t.1) • projection (k,1,t.2.1) +
      z (k,1,t.2.1) • projection (k,0,t.1)))

theorem tangentMap_apply {n r : ℕ} (z w : Slots n r → ℂ) (t : Triple n) :
    tangentMap z w t = ∑ k, (z (k,0,t.1) * z (k,1,t.2.1) * w (k,2,t.2.2) +
      z (k,2,t.2.2) * (z (k,0,t.1) * w (k,1,t.2.1) + z (k,1,t.2.1) * w (k,0,t.1))) := by
  simp [tangentMap, projection, mul_add]

private theorem derivative {n r : ℕ} (z : Slots n r → ℂ) :
    HasStrictFDerivAt parametrization (tangentMap z) z := by
  apply hasStrictFDerivAt_pi.mpr
  intro t
  unfold parametrization secant term
  apply HasStrictFDerivAt.fun_sum (A := fun k (x : Slots n r → ℂ) =>
    x (k,0,t.1) * x (k,1,t.2.1) * x (k,2,t.2.2))
  intro k _
  exact ((hasStrictFDerivAt_apply (𝕜 := ℂ) (k,0,t.1) z).mul
    (hasStrictFDerivAt_apply (k,1,t.2.1) z)).mul (hasStrictFDerivAt_apply (k,2,t.2.2) z)

/-- A full-rank tangent configuration at the predicted number of terms. -/
def FullTangents (n : ℕ) : Prop :=
  ∃ z : Slots n (predicted n) → ℂ, Function.Surjective (tangentMap z)

/-- A single spanning configuration suffices for generic rank in the specified Holor topology. -/
theorem generic_of_tangents {n : ℕ} (hn : 0 < n) (h : FullTangents n) :
    IsGenericRank [n,n,n] (predicted n) := by
  classical
  obtain ⟨z,hz⟩ := h
  obtain ⟨p,hp,hU⟩ := dominant_image _ (independent_of_submersion (derivative z) hz)
  obtain ⟨q,hq,hL⟩ := lower_polynomial hn
  let e : Holor ℂ [n,n,n] ≃ₜ (Triple n → ℂ) :=
    (Homeomorph.piCongrLeft (Y := fun _ => ℂ) (indexEquiv n)).symm
  obtain ⟨ho,hd⟩ := polynomial_open_dense (mul_ne_zero hp hq)
  refine ⟨e ⁻¹' _, e.continuous.isOpen_preimage _ ho, hd.preimage e.isOpenMap, ?_⟩
  intro T hT
  change eval (fun t => T (cubeIndex t)) (p * q) ≠ 0 at hT
  rw [map_mul, mul_ne_zero_iff] at hT
  refine le_antisymm ?_ (hL T hT.2)
  obtain ⟨x,hx⟩ := hU _ hT.1
  have hm := factors_rankMax (r := predicted n) (fun k => (fun i => x (k,0,i),
    fun j => x (k,1,j), fun l => x (k,2,l))) T (fun t => by
      simpa only [eval_polynomials, parametrization] using (hx t).symm)
  exact Nat.find_min' _ hm


private def diagonalPoint (n : ℕ) : Slots n n → ℂ :=
  fun (k,_,i) => if k = i then 1 else 0

private def diagonalLift {n : ℕ} (y : Triple n → ℂ) : Slots n n → ℂ :=
  fun (s,f,i) => if f = 2 then y (s,s,i) else if i = s then 0 else
    if f = 1 then y (s,i,s) else y (i,s,s)

theorem fullTangents_one : FullTangents 1 := by
  change ∃ z : Slots 1 1 → ℂ, Function.Surjective (tangentMap z)
  refine ⟨diagonalPoint 1, fun y => ⟨diagonalLift y, ?_⟩⟩
  funext ⟨i,j,k⟩
  fin_cases i; fin_cases j; fin_cases k
  simp [tangentMap_apply, diagonalPoint, diagonalLift]

theorem fullTangents_two : FullTangents 2 := by
  change ∃ z : Slots 2 2 → ℂ, Function.Surjective (tangentMap z)
  refine ⟨diagonalPoint 2, fun y => ⟨diagonalLift y, ?_⟩⟩
  funext ⟨i,j,k⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;>
    simp [tangentMap_apply, diagonalPoint, diagonalLift, Fin.sum_univ_two]


/-- A triangular family of columns spans the full coordinate space. -/
private theorem surjective_of_pivots {α β : Type} [Fintype β] [DecidableEq α] [DecidableEq β]
    (D : (α → ℂ) →ₗ[ℂ] (β → ℂ)) (level : β → ℕ) (pivot : β → α)
    (diag : ∀ t, D (Pi.single (pivot t) 1) t = 1)
    (below : ∀ t u, u ≠ t → D (Pi.single (pivot t) 1) u ≠ 0 → level u < level t) :
    Function.Surjective D := by
  have hunit (t : β) : Pi.single t 1 ∈ D.range := by
    induction t using (measure level).wf.induction with
    | h t ih =>
      let c := D (Pi.single (pivot t) 1)
      have hc : c ∈ D.range := LinearMap.mem_range_self D _
      have he := Finset.sum_erase_add Finset.univ
        (fun u => c u • (Pi.single u 1 : β → ℂ)) (Finset.mem_univ t)
      rw [← pi_eq_sum_univ', show c t = 1 from diag t, one_smul] at he
      rw [← he] at hc
      refine (D.range.add_mem_iff_right ?_).mp hc
      apply D.range.sum_mem
      intro u hu
      by_cases hz : c u = 0
      · simp [hz]
      · exact D.range.smul_mem _ (ih u (below t u (Finset.ne_of_mem_erase hu) hz))
  intro y
  change y ∈ D.range
  rw [pi_eq_sum_univ' y]
  exact D.range.sum_mem (fun t _ => D.range.smul_mem _ (hunit t))

private def active {n r : ℕ} (z : Slots n r → Bool) (s : Slots n r) (t : Triple n) : Bool :=
  let (k,f,i) := s
  if f = 0 then decide (i = t.1) && z (k,1,t.2.1) && z (k,2,t.2.2)
  else if f = 1 then z (k,0,t.1) && decide (i = t.2.1) && z (k,2,t.2.2)
  else z (k,0,t.1) && z (k,1,t.2.1) && decide (i = t.2.2)

private theorem tangent_single {n r : ℕ} (z : Slots n r → Bool) (s : Slots n r) (t : Triple n) :
    tangentMap (fun a => if z a then 1 else 0) (Pi.single s 1) t =
      if active z s t then 1 else 0 := by
  obtain ⟨k,f,i⟩ := s
  rw [tangentMap_apply, Fintype.sum_eq_single k]
  · fin_cases f <;> simp [active, Pi.single_apply] <;>
      split_ifs <;> simp_all
  · intro j hj
    simp [Ne.symm hj]

private def onPlane {n r : ℕ} (s : Slots n r) (ij : Fin n × Fin n) : Triple n :=
  if s.2.1 = 0 then (s.2.2,ij.1,ij.2) else if s.2.1 = 1 then (ij.1,s.2.2,ij.2)
  else (ij.1,ij.2,s.2.2)

private theorem active_in_plane {n r : ℕ} (z : Slots n r → Bool) (s : Slots n r) (u : Triple n)
    (h : active z s u = true) : ∃ ij, onPlane s ij = u := by
  obtain ⟨k,f,i⟩ := s
  obtain ⟨a,b,c⟩ := u
  fin_cases f
  · simp [active] at h
    exact ⟨(b,c), by simp [onPlane, h.1.1]⟩
  · simp [active] at h
    exact ⟨(a,c), by simp [onPlane, h.1.2]⟩
  · simp [active] at h
    exact ⟨(a,b), by simp [onPlane, h.2]⟩

private theorem fullTangents_of_certificate {n : ℕ}
    (z : Slots n (predicted n) → Bool) (level : Triple n → ℕ) (pivot : Triple n → Slots n (predicted n))
    (h : ∀ a b c : Fin n, let t : Triple n := (a,b,c)
      active z (pivot t) t = true ∧ ∀ i j : Fin n, let u := onPlane (pivot t) (i,j)
        u ≠ t → active z (pivot t) u = true → level u < level t) : FullTangents n := by
  refine ⟨fun a => if z a then 1 else 0, surjective_of_pivots _ level pivot ?_ ?_⟩
  · intro t
    change tangentMap _ _ t = _
    rw [tangent_single, (h t.1 t.2.1 t.2.2).1]
    rfl
  · intro t u hut hne
    have ha : active z (pivot t) u = true := by
      change tangentMap _ _ u ≠ 0 at hne
      simpa only [tangent_single, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false, not_not] using hne
    obtain ⟨ij,hij⟩ := active_in_plane _ _ _ ha
    exact (show u ≠ t → active z (pivot t) u = true → level u < level t by
      simpa only [hij] using (h t.1 t.2.1 t.2.2).2 ij.1 ij.2) hut ha




/-- Each row of masks specifies the three zero-one vectors of one summand. -/
private def maskPoint {n r : ℕ} (masks : Array ℕ) (s : Slots n r) : Bool :=
  (masks[3 * s.1.val + s.2.1.val]!).testBit s.2.2.val

private def tripleNumber {n : ℕ} (t : Triple n) : ℕ := (t.1.val * n + t.2.1.val) * n + t.2.2.val

/-- The lookup table stores an elimination level and an index of a tangent column.
Coordinates at the same level can be eliminated independently. -/
private def certificateData {n r : ℕ} [NeZero n] [NeZero r]
    (data : Array (ℕ × ℕ)) (t : Triple n) : ℕ × Slots n r :=
  let (level,col) := data[tripleNumber t]!
  (level, Fin.ofNat r (col / n / 3), Fin.ofNat 3 (col / n), Fin.ofNat n col)

private def pointMasks4 : Array ℕ :=
  #[1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 8, 8, 4, 12, 12, 7, 15, 9, 11, 5, 7]

private def pivots4 : Array (ℕ × ℕ) :=
  #[(0,0), (0,9), (0,10), (0,11), (0,5), (0,12), (6,70), (3,65), (0,6), (1,72), (0,24), (4,60), (0,7),
    (2,69), (5,48), (0,36), (0,1), (0,16), (4,73), (2,64), (0,20), (0,13), (0,22), (0,23), (3,68),
    (0,18), (0,25), (4,61), (2,67), (0,19), (5,49), (0,37), (0,2), (1,74), (0,28), (1,52), (2,62),
    (0,14), (0,29), (1,53), (0,32), (0,33), (0,26), (0,35), (1,56), (1,57), (0,31), (0,38), (0,3),
    (6,75), (5,82), (0,40), (5,63), (0,15), (7,77), (0,41), (4,80), (5,78), (0,27), (0,42), (0,44),
    (0,45), (0,46), (0,39)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem fullTangents_4 : FullTangents 4 := by
  let z := @maskPoint 4 7 pointMasks4
  let data := @certificateData 4 7 inferInstance inferInstance pivots4
  apply fullTangents_of_certificate z (fun t => (data t).1) (fun t => (data t).2)
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

private def pointMasks5 : Array ℕ :=
  #[1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 8, 8, 16, 16, 16, 5, 31, 23, 3, 19, 26, 20, 25, 17, 25, 13, 26, 30,
    12, 6]

private def pivots5 : Array (ℕ × ℕ) :=
  #[(0,0), (0,11), (0,12), (0,13), (0,14), (0,6), (0,15), (9,87), (10,96), (9,89), (0,7), (6,135),
    (0,30), (8,120), (7,82), (0,8), (4,128), (5,83), (0,45), (1,105), (0,9), (1,101), (8,84), (11,90),
    (0,60), (0,1), (0,20), (10,140), (11,95), (10,104), (0,25), (0,16), (0,27), (0,28), (0,29),
    (12,145), (0,22), (0,31), (14,97), (13,76), (11,106), (0,23), (1,136), (0,46), (5,98), (1,100),
    (0,24), (11,102), (12,91), (0,61), (0,2), (2,80), (0,35), (3,122), (1,110), (3,85), (0,17), (0,36),
    (18,88), (8,77), (0,40), (0,41), (0,32), (0,43), (0,44), (2,115), (1,137), (0,38), (0,47), (2,119),
    (1,114), (7,86), (0,39), (17,118), (0,62), (0,3), (9,131), (6,132), (0,50), (15,123), (17,78),
    (0,18), (11,141), (0,51), (16,93), (2,130), (1,138), (0,33), (0,52), (14,149), (0,55), (0,56),
    (0,57), (0,48), (0,59), (16,108), (12,129), (13,144), (0,54), (0,63), (0,4), (8,116), (3,117),
    (16,124), (0,65), (9,111), (0,19), (10,79), (17,94), (0,66), (1,112), (2,142), (0,34), (15,127),
    (0,67), (1,109), (3,139), (2,147), (0,49), (0,68), (0,70), (0,71), (0,72), (0,73), (0,64)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem fullTangents_5 : FullTangents 5 := by
  let z := @maskPoint 5 10 pointMasks5
  let data := @certificateData 5 10 inferInstance inferInstance pivots5
  apply fullTangents_of_certificate z (fun t => (data t).1) (fun t => (data t).2)
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

private def pointMasks6 : Array ℕ :=
  #[1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 8, 8, 16, 16, 16, 32, 32, 32, 17, 10, 6, 45, 27, 62, 28, 46, 22, 48,
    41, 34, 9, 16, 63, 10, 28, 18, 43, 52, 37, 5, 49, 3]

private def pivots6 : Array (ℕ × ℕ) :=
  #[(0,0), (0,13), (0,14), (0,15), (0,16), (0,17), (0,7), (0,18), (9,108), (20,126), (10,124), (19,125),
    (0,8), (1,242), (0,36), (27,188), (10,198), (5,216), (0,9), (4,121), (8,117), (0,54), (9,189),
    (5,162), (0,10), (2,193), (3,118), (1,195), (0,72), (4,180), (0,11), (3,234), (4,248), (20,191),
    (11,144), (0,90), (0,1), (0,24), (29,222), (30,127), (23,204), (28,163), (0,30), (0,19), (0,32),
    (0,33), (0,34), (0,35), (27,217), (0,26), (0,37), (24,213), (2,199), (26,233), (28,210), (0,27),
    (1,109), (0,55), (1,207), (27,215), (21,235), (0,28), (5,212), (23,181), (0,73), (22,226), (20,227),
    (0,29), (12,145), (29,231), (11,209), (0,91), (0,2), (1,240), (0,42), (22,249), (12,250), (9,251),
    (1,241), (0,20), (0,43), (25,128), (9,151), (24,143), (0,48), (0,49), (0,38), (0,51), (0,52),
    (0,53), (5,243), (1,110), (0,45), (0,56), (6,200), (10,164), (6,244), (5,154), (0,46), (9,182),
    (0,74), (8,218), (7,236), (6,247), (0,47), (21,137), (10,146), (0,92), (0,3), (18,139), (21,140),
    (0,60), (22,142), (19,165), (24,187), (0,21), (1,111), (0,61), (1,205), (23,129), (26,219), (2,211),
    (0,39), (0,62), (3,152), (25,161), (0,66), (0,67), (0,68), (0,57), (0,70), (0,71), (1,192), (1,208),
    (4,194), (0,64), (0,75), (5,183), (19,237), (7,157), (9,158), (0,65), (10,147), (0,93), (0,4),
    (18,175), (19,114), (22,130), (0,78), (19,166), (28,120), (0,22), (8,112), (21,123), (0,79),
    (1,169), (20,220), (2,116), (0,40), (26,159), (0,80), (9,170), (27,174), (3,202), (7,153), (0,58),
    (0,81), (18,171), (0,84), (0,85), (0,86), (0,87), (0,76), (0,89), (19,238), (1,173), (5,119),
    (24,177), (0,83), (0,94), (0,5), (16,239), (20,176), (23,132), (19,178), (0,96), (25,223), (0,23),
    (20,113), (24,131), (21,149), (0,97), (16,221), (8,229), (0,41), (28,134), (12,232), (0,98),
    (26,138), (17,167), (19,135), (0,59), (18,203), (0,99), (15,185), (1,172), (13,230), (14,136),
    (0,77), (0,100), (0,102), (0,103), (0,104), (0,105), (0,106), (0,95)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem fullTangents_6 : FullTangents 6 := by
  let z := @maskPoint 6 14 pointMasks6
  let data := @certificateData 6 14 inferInstance inferInstance pivots6
  apply fullTangents_of_certificate z (fun t => (data t).1) (fun t => (data t).2)
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

private def pointMasks7 : Array ℕ :=
  #[1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 8, 8, 16, 16, 16, 32, 32, 32, 64, 64, 64, 93, 43, 116, 100, 97, 36,
    80, 36, 18, 67, 14, 51, 72, 29, 24, 46, 65, 16, 34, 84, 9, 24, 53, 54, 56, 2, 17, 40, 13, 12, 81, 5,
    69, 18, 22, 40]

private def pivots7 : Array (ℕ × ℕ) :=
  #[(0,0), (0,15), (0,16), (0,17), (0,18), (0,19), (0,20), (0,8), (0,21), (29,226), (20,227), (1,315),
    (17,218), (38,365), (0,9), (15,372), (0,42), (12,374), (5,375), (13,376), (1,357), (0,10), (16,225),
    (13,336), (0,63), (21,210), (20,229), (39,147), (0,11), (24,221), (31,294), (22,231), (0,84),
    (23,378), (32,368), (0,12), (23,189), (30,163), (28,164), (22,165), (0,105), (31,369), (0,13),
    (32,223), (30,370), (23,273), (1,252), (31,160), (0,126), (0,1), (0,28), (27,268), (3,280), (6,253),
    (13,385), (34,272), (0,35), (0,22), (0,37), (0,38), (0,39), (0,40), (0,41), (18,224), (0,30),
    (0,43), (19,282), (1,396), (19,219), (35,358), (14,283), (0,31), (28,337), (0,64), (20,211),
    (18,388), (40,230), (19,392), (0,32), (25,394), (20,284), (0,85), (20,397), (38,398), (13,285),
    (0,33), (28,169), (12,390), (2,190), (0,106), (41,148), (26,274), (0,34), (26,289), (25,290),
    (5,291), (21,292), (0,127), (0,2), (31,162), (0,49), (1,338), (7,186), (5,170), (1,359), (12,317),
    (0,23), (0,50), (23,380), (11,260), (21,166), (39,155), (0,56), (0,57), (0,44), (0,59), (0,60),
    (0,61), (0,62), (29,161), (30,212), (0,52), (0,65), (21,262), (17,178), (40,149), (28,275),
    (32,296), (0,53), (22,233), (0,86), (16,179), (33,158), (28,182), (6,191), (0,54), (27,185),
    (5,264), (0,107), (32,159), (27,266), (32,183), (0,55), (26,269), (6,265), (4,181), (0,128), (0,3),
    (13,297), (1,339), (0,70), (2,255), (8,355), (13,154), (9,329), (0,24), (23,344), (0,71), (10,318),
    (10,334), (24,150), (11,213), (6,192), (0,45), (0,72), (3,234), (7,303), (14,156), (0,77), (0,78),
    (0,79), (0,66), (0,81), (0,82), (0,83), (18,245), (12,305), (6,310), (0,74), (0,87), (11,381),
    (15,251), (26,308), (5,306), (1,348), (0,75), (4,312), (0,108), (16,314), (19,276), (30,307),
    (23,171), (0,76), (1,244), (22,271), (0,129), (0,4), (13,298), (5,373), (11,235), (0,91), (12,313),
    (6,364), (1,319), (0,25), (24,302), (8,332), (0,92), (9,386), (37,335), (6,371), (1,393), (0,46),
    (10,382), (0,93), (2,208), (7,361), (14,325), (16,199), (12,340), (0,67), (0,94), (17,214),
    (38,151), (0,98), (0,99), (0,100), (0,101), (0,88), (0,103), (0,104), (25,203), (2,193), (2,205),
    (11,206), (0,96), (0,109), (8,209), (26,328), (1,202), (29,172), (27,277), (0,97), (28,391),
    (0,130), (0,5), (15,351), (2,352), (2,353), (3,322), (0,112), (33,188), (8,281), (0,26), (22,176),
    (7,383), (9,320), (0,113), (36,152), (12,324), (5,194), (0,47), (1,345), (4,261), (0,114), (34,362),
    (13,350), (14,215), (1,346), (0,68), (5,354), (0,115), (35,356), (19,326), (16,299), (7,347),
    (6,236), (0,89), (0,116), (39,293), (0,119), (0,120), (0,121), (0,122), (0,123), (0,110), (0,125),
    (25,278), (17,288), (3,173), (24,349), (4,257), (0,118), (0,131), (0,6), (14,196), (4,184), (3,238),
    (1,258), (5,174), (0,133), (2,321), (0,27), (17,153), (11,239), (1,197), (16,384), (0,134), (5,363),
    (5,198), (0,48), (4,248), (4,249), (1,177), (0,135), (17,216), (15,246), (5,342), (0,69), (1,241),
    (16,250), (0,136), (6,279), (1,200), (7,247), (1,242), (0,90), (15,300), (0,137), (24,222), (6,195),
    (1,180), (6,243), (5,207), (0,111), (0,138), (0,140), (0,141), (0,142), (0,143), (0,144), (0,145),
    (0,132)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem fullTangents_7 : FullTangents 7 := by
  let z := @maskPoint 7 19 pointMasks7
  let data := @certificateData 7 19 inferInstance inferInstance pivots7
  apply fullTangents_of_certificate z (fun t => (data t).1) (fun t => (data t).2)
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

private def pointMasks8 : Array ℕ :=
  #[1, 1, 1, 2, 2, 2, 4, 4, 4, 8, 8, 8, 16, 16, 16, 32, 32, 32, 64, 64, 64, 128, 128, 128, 25, 98, 72,
    161, 206, 133, 56, 136, 169, 196, 72, 104, 22, 80, 107, 144, 192, 129, 19, 17, 48, 86, 213, 137, 99,
    85, 20, 88, 120, 40, 138, 160, 39, 18, 99, 68, 81, 176, 33, 14, 142, 18, 11, 137, 9, 20, 12, 5]

private def pivots8 : Array (ℕ × ℕ) :=
  #[(0,0), (0,17), (0,18), (0,19), (0,20), (0,21), (0,22), (0,23), (0,9), (0,24), (70,216), (31,211),
    (63,345), (62,213), (43,192), (58,215), (0,10), (78,504), (0,48), (50,538), (66,346), (59,490),
    (51,202), (52,360), (0,11), (77,545), (1,552), (0,72), (74,347), (10,264), (9,203), (11,240),
    (0,12), (73,353), (39,354), (29,355), (0,96), (1,336), (39,358), (51,359), (0,13), (75,209),
    (71,456), (30,408), (66,349), (0,120), (42,205), (57,503), (0,14), (74,288), (67,384), (8,206),
    (65,350), (7,494), (0,144), (1,312), (0,15), (76,432), (69,231), (1,528), (75,351), (2,480),
    (43,502), (0,168), (0,1), (0,32), (38,474), (1,536), (1,356), (2,344), (38,478), (36,479), (0,40),
    (0,25), (0,42), (0,43), (0,44), (0,45), (0,46), (0,47), (24,376), (0,34), (0,49), (49,523),
    (65,385), (60,405), (19,466), (39,217), (1,539), (0,35), (25,553), (0,73), (73,515), (18,549),
    (26,467), (18,371), (1,352), (0,36), (4,306), (28,289), (0,97), (2,348), (5,468), (50,361), (4,481),
    (0,37), (37,469), (29,409), (65,476), (0,121), (30,193), (35,455), (4,304), (0,38), (3,470),
    (19,374), (64,308), (27,265), (0,145), (5,313), (2,544), (0,39), (38,433), (2,547), (74,505),
    (3,453), (39,471), (0,169), (0,2), (73,296), (0,56), (21,530), (62,338), (61,381), (40,382),
    (52,362), (33,520), (0,26), (0,57), (48,194), (78,506), (49,297), (47,458), (34,218), (0,64),
    (0,65), (0,50), (0,67), (0,68), (0,69), (0,70), (0,71), (1,554), (72,299), (0,59), (0,74), (1,572),
    (18,266), (17,286), (17,575), (1,564), (29,305), (0,60), (29,307), (0,98), (28,309), (6,310),
    (51,311), (29,482), (72,301), (0,61), (30,410), (79,517), (0,122), (46,277), (57,373), (3,566),
    (28,302), (0,62), (16,283), (63,386), (17,278), (0,146), (18,287), (19,314), (71,303), (0,63),
    (20,375), (77,519), (21,242), (22,279), (0,170), (0,3), (74,512), (70,546), (0,80), (18,339),
    (17,416), (38,200), (37,551), (32,208), (0,27), (66,441), (0,81), (77,507), (61,525), (42,195),
    (57,527), (1,555), (73,521), (0,51), (0,82), (74,514), (57,250), (48,526), (56,363), (0,88), (0,89),
    (0,90), (0,75), (0,92), (0,93), (0,94), (0,95), (30,540), (30,516), (75,387), (0,84), (0,99),
    (2,411), (40,204), (55,252), (31,424), (72,435), (71,459), (0,85), (78,212), (0,123), (41,430),
    (34,253), (20,542), (41,291), (68,219), (0,86), (65,518), (1,267), (0,147), (21,315), (1,531),
    (68,447), (67,522), (0,87), (76,548), (2,243), (44,207), (0,171), (0,4), (72,473), (1,560),
    (15,532), (0,104), (1,340), (37,460), (1,320), (5,472), (0,28), (34,561), (30,475), (0,105),
    (28,477), (35,465), (35,220), (1,562), (61,298), (0,52), (1,571), (0,106), (19,573), (18,574),
    (16,364), (2,556), (71,508), (1,570), (0,76), (0,107), (2,419), (8,268), (13,323), (0,112), (0,113),
    (0,114), (0,115), (0,100), (0,117), (0,118), (0,119), (4,484), (71,436), (30,565), (8,412), (0,109),
    (0,124), (36,196), (33,325), (2,316), (8,292), (2,388), (7,422), (0,110), (6,429), (0,148), (1,335),
    (1,327), (70,329), (20,567), (14,244), (0,111), (3,261), (1,334), (0,172), (0,5), (93,401),
    (82,392), (17,533), (1,341), (0,128), (83,461), (38,248), (37,232), (0,29), (69,221), (62,249),
    (89,236), (0,129), (63,197), (59,239), (20,557), (90,509), (0,53), (51,403), (83,389), (0,130),
    (68,238), (53,226), (15,251), (72,257), (19,227), (0,77), (82,395), (0,131), (28,269), (14,263),
    (17,485), (92,293), (77,228), (28,413), (0,101), (0,132), (84,406), (54,365), (0,136), (0,137),
    (0,138), (0,139), (0,140), (0,125), (0,142), (0,143), (25,400), (91,233), (68,230), (27,254),
    (69,398), (0,134), (0,149), (26,317), (16,245), (69,437), (68,258), (15,259), (82,399), (0,135),
    (45,262), (0,173), (0,6), (92,377), (81,378), (16,534), (6,342), (2,488), (0,152), (53,366),
    (63,489), (0,30), (81,222), (8,198), (90,393), (62,417), (0,153), (64,369), (23,558), (91,510),
    (0,54), (50,379), (82,380), (58,418), (0,154), (51,370), (11,491), (73,281), (22,282), (0,78),
    (81,428), (1,270), (0,155), (16,246), (6,486), (7,294), (78,396), (6,420), (0,102), (5,501),
    (0,156), (52,372), (5,493), (74,425), (79,426), (7,414), (80,397), (0,126), (0,157), (56,431),
    (0,160), (0,161), (0,162), (0,163), (0,164), (0,165), (0,150), (0,167), (1,318), (77,497), (80,438),
    (15,423), (81,500), (4,495), (0,159), (0,174), (0,7), (86,440), (83,224), (13,535), (86,343),
    (85,272), (84,463), (0,176), (36,321), (0,31), (37,223), (63,235), (88,511), (65,273), (64,199),
    (0,177), (17,322), (74,442), (0,55), (35,367), (87,391), (66,237), (67,274), (0,178), (12,280),
    (26,443), (18,559), (0,79), (82,284), (13,247), (16,271), (0,179), (1,324), (70,295), (76,444),
    (34,415), (0,103), (33,487), (35,276), (0,180), (32,448), (73,439), (72,229), (30,451), (79,452),
    (0,127), (45,454), (0,181), (1,319), (69,446), (21,330), (15,331), (1,332), (7,333), (0,151),
    (0,182), (0,184), (0,185), (0,186), (0,187), (0,188), (0,189), (0,190), (0,175)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
theorem fullTangents_8 : FullTangents 8 := by
  let z := @maskPoint 8 24 pointMasks8
  let data := @certificateData 8 24 inferInstance inferInstance pivots8
  apply fullTangents_of_certificate z (fun t => (data t).1) (fun t => (data t).2)
  intro a b
  fin_cases a <;> fin_cases b <;> decide +kernel

/-- Unconditional verification of the admissible dimensions through eight. -/
theorem generic_rank_le_eight {n : ℕ} (hn : 1 ≤ n) (hn3 : n ≠ 3) (hn8 : n ≤ 8) :
    IsGenericRank [n,n,n] (predicted n) := by
  apply generic_of_tangents hn
  interval_cases n <;> first | contradiction | exact fullTangents_one | exact fullTangents_two
                             | exact fullTangents_4 | exact fullTangents_5 | exact fullTangents_6
                             | exact fullTangents_7 | exact fullTangents_8

end OMA.Cube

namespace OMA.Cube

open MvPolynomial

/- Spanning configurations of tangent lines in a box. -/

/-- The three vectors of a point are indexed by the disjoint union of the three sides. -/
abbrev Coord (α β γ : Type) := α ⊕ β ⊕ γ

/-- Points come in four kinds: tangent points and points carrying one line only. -/
abbrev Pt (S E F G : Type) := S ⊕ E ⊕ F ⊕ G

abbrev Conf (α β γ S E F G : Type) := Pt S E F G × Coord α β γ → ℂ

abbrev Col (α β γ S E F G : Type) := ((S ⊕ E) × α) ⊕ ((S ⊕ F) × β) ⊕ ((S ⊕ G) × γ)

def pt1 {S E F G : Type} : S ⊕ E → Pt S E F G :=
  Sum.elim Sum.inl (fun x => Sum.inr (Sum.inl x))

def pt2 {S E F G : Type} : S ⊕ F → Pt S E F G :=
  Sum.elim Sum.inl (fun y => Sum.inr (Sum.inr (Sum.inl y)))

def pt3 {S E F G : Type} : S ⊕ G → Pt S E F G :=
  Sum.elim Sum.inl (fun z => Sum.inr (Sum.inr (Sum.inr z)))

section gens

variable {α β γ S E F G : Type}

def gen1 [DecidableEq α] (v : β → ℂ) (w : γ → ℂ) (i : α) : α × β × γ → ℂ :=
  fun t => if t.1 = i then v t.2.1 * w t.2.2 else 0

def gen2 [DecidableEq β] (u : α → ℂ) (w : γ → ℂ) (j : β) : α × β × γ → ℂ :=
  fun t => if t.2.1 = j then u t.1 * w t.2.2 else 0

def gen3 [DecidableEq γ] (u : α → ℂ) (v : β → ℂ) (k : γ) : α × β × γ → ℂ :=
  fun t => if t.2.2 = k then u t.1 * v t.2.1 else 0

def uvec (c : Conf α β γ S E F G) (p : Pt S E F G) : α → ℂ := fun i => c (p, Sum.inl i)
def vvec (c : Conf α β γ S E F G) (p : Pt S E F G) : β → ℂ := fun j => c (p, Sum.inr (Sum.inl j))
def wvec (c : Conf α β γ S E F G) (p : Pt S E F G) : γ → ℂ := fun k => c (p, Sum.inr (Sum.inr k))

variable [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- The tangent lines of a configuration, one generator for each free coordinate. -/
def gens (c : Conf α β γ S E F G) : Col α β γ S E F G → (α × β × γ → ℂ)
  | Sum.inl (p, i) => gen1 (vvec c (pt1 p)) (wvec c (pt1 p)) i
  | Sum.inr (Sum.inl (p, j)) => gen2 (uvec c (pt2 p)) (wvec c (pt2 p)) j
  | Sum.inr (Sum.inr (p, k)) => gen3 (uvec c (pt3 p)) (vvec c (pt3 p)) k

def SpanC (c : Conf α β γ S E F G) : Submodule ℂ (α × β × γ → ℂ) :=
  Submodule.span ℂ (Set.range (gens c))

theorem gen1_mem (c : Conf α β γ S E F G) (p : S ⊕ E) (i : α) :
    gen1 (vvec c (pt1 p)) (wvec c (pt1 p)) i ∈ SpanC c :=
  Submodule.subset_span ⟨Sum.inl (p, i), rfl⟩

theorem gen2_mem (c : Conf α β γ S E F G) (p : S ⊕ F) (j : β) :
    gen2 (uvec c (pt2 p)) (wvec c (pt2 p)) j ∈ SpanC c :=
  Submodule.subset_span ⟨Sum.inr (Sum.inl (p, j)), rfl⟩

theorem gen3_mem (c : Conf α β γ S E F G) (p : S ⊕ G) (k : γ) :
    gen3 (uvec c (pt3 p)) (vvec c (pt3 p)) k ∈ SpanC c :=
  Submodule.subset_span ⟨Sum.inr (Sum.inr (p, k)), rfl⟩

end gens

/-- Some configuration of the given numbers of points spans the whole box. -/
def FillsT (α β γ S E F G : Type) [DecidableEq α] [DecidableEq β] [DecidableEq γ] : Prop :=
  ∃ c : Conf α β γ S E F G, SpanC c = ⊤

/-- Every configuration outside a proper hypersurface spans the whole box. -/
def GenT (α β γ S E F G : Type) [DecidableEq α] [DecidableEq β] [DecidableEq γ] : Prop :=
  ∃ P : MvPolynomial (Pt S E F G × Coord α β γ) ℂ, P ≠ 0 ∧
    ∀ c : Conf α β γ S E F G, eval c P ≠ 0 → SpanC c = ⊤

theorem exists_eval_ne_zero {σ : Type} {P : MvPolynomial σ ℂ} (hP : P ≠ 0) :
    ∃ x : σ → ℂ, eval x P ≠ 0 := by
  by_contra! h
  exact hP (MvPolynomial.funext fun x => by simpa using h x)

section basic

variable {α β γ S E F G : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem GenT.fills (h : GenT α β γ S E F G) : FillsT α β γ S E F G := by
  obtain ⟨P, hP, hfill⟩ := h
  obtain ⟨c, hc⟩ := exists_eval_ne_zero hP
  exact ⟨c, hfill c hc⟩

/-- A submodule containing every coordinate tensor is everything. -/
theorem eq_top_of_single {T : Type} [Fintype T] [DecidableEq T] (N : Submodule ℂ (T → ℂ))
    (h : ∀ t, (Pi.single t 1 : T → ℂ) ∈ N) : N = ⊤ := by
  rw [eq_top_iff]
  intro y _
  rw [pi_eq_sum_univ' y]
  exact N.sum_mem fun t _ => N.smul_mem _ (h t)

/-- Linear images of the generators of a spanning configuration stay inside any submodule
containing them. -/
theorem map_mem_of_span {V : Type} [AddCommGroup V] [Module ℂ V]
    (L : (α × β × γ → ℂ) →ₗ[ℂ] V) (N : Submodule ℂ V) (c : Conf α β γ S E F G)
    (hc : SpanC c = ⊤) (h : ∀ col, L (gens c col) ∈ N) (f : α × β × γ → ℂ) : L f ∈ N := by
  have hle : (SpanC c).map L ≤ N := by
    rw [SpanC, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨_, ⟨col, rfl⟩, rfl⟩
    exact h col
  exact hle (Submodule.mem_map_of_mem (by rw [hc]; trivial))

end basic

end OMA.Cube

namespace OMA.Cube

open MvPolynomial

section generic

variable {α β γ S E F G : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- The generators as polynomials in the coordinates of the configuration. -/
noncomputable def gensP : Col α β γ S E F G → (α × β × γ) →
    MvPolynomial (Pt S E F G × Coord α β γ) ℂ
  | Sum.inl (p, i) => fun t =>
      if t.1 = i then X (pt1 p, Sum.inr (Sum.inl t.2.1)) * X (pt1 p, Sum.inr (Sum.inr t.2.2)) else 0
  | Sum.inr (Sum.inl (p, j)) => fun t =>
      if t.2.1 = j then X (pt2 p, Sum.inl t.1) * X (pt2 p, Sum.inr (Sum.inr t.2.2)) else 0
  | Sum.inr (Sum.inr (p, k)) => fun t =>
      if t.2.2 = k then X (pt3 p, Sum.inl t.1) * X (pt3 p, Sum.inr (Sum.inl t.2.1)) else 0

theorem eval_gensP (c : Conf α β γ S E F G) (col : Col α β γ S E F G) (t : α × β × γ) :
    eval c (gensP col t) = gens c col t := by
  rcases col with ⟨p, i⟩ | ⟨p, j⟩ | ⟨p, k⟩
  · simp only [gensP, gens, gen1, vvec, wvec]
    split_ifs <;> simp
  · simp only [gensP, gens, gen2, uvec, wvec]
    split_ifs <;> simp
  · simp only [gensP, gens, gen3, uvec, vvec]
    split_ifs <;> simp

variable [Fintype α] [Fintype β] [Fintype γ] [Fintype S] [Fintype E] [Fintype F] [Fintype G]

/-- One spanning configuration forces all configurations off a hypersurface to span. -/
theorem FillsT.gen (h : FillsT α β γ S E F G) : GenT α β γ S E F G := by
  classical
  obtain ⟨c0, hc0⟩ := h
  have hmem : ∀ t : α × β × γ, ∃ r : Col α β γ S E F G → ℂ,
      ∑ col, r col • gens c0 col = Pi.single t 1 := by
    intro t
    have ht : (Pi.single t 1 : α × β × γ → ℂ) ∈ Submodule.span ℂ (Set.range (gens c0)) := by
      have : (Pi.single t 1 : α × β × γ → ℂ) ∈ SpanC c0 := by rw [hc0]; trivial
      exact this
    exact (Submodule.mem_span_range_iff_exists_fun ℂ).mp ht
  choose r hr using hmem
  let NP : Matrix (α × β × γ) (α × β × γ) (MvPolynomial (Pt S E F G × Coord α β γ) ℂ) :=
    fun t t' => ∑ col, gensP col t * C (r t' col)
  have hN : ∀ c : Conf α β γ S E F G, ∀ t t',
      (eval c).mapMatrix NP t t' = ∑ col, r t' col * gens c col t := by
    intro c t t'
    show eval c (∑ col, gensP col t * C (r t' col)) = _
    rw [map_sum]
    refine Finset.sum_congr rfl fun col _ => ?_
    rw [map_mul, eval_gensP, eval_C, mul_comm]
  have hdet : ∀ c : Conf α β γ S E F G, eval c NP.det = ((eval c).mapMatrix NP).det :=
    fun c => RingHom.map_det _ _
  refine ⟨NP.det, ?_, ?_⟩
  · intro h0
    have h1 : ((eval c0).mapMatrix NP) = 1 := by
      ext t t'
      rw [hN]
      have := congrFun (hr t') t
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at this
      rw [this, Matrix.one_apply, Pi.single_apply]
    have h2 := hdet c0
    rw [h0, map_zero, h1, Matrix.det_one] at h2
    exact zero_ne_one h2
  · intro c hc
    rw [hdet] at hc
    set N := (eval c).mapMatrix NP with hNdef
    rw [eq_top_iff]
    intro y _
    have hunit : IsUnit N.det := isUnit_iff_ne_zero.mpr hc
    have hy : y = ∑ t', (N⁻¹.mulVec y) t' • ∑ col, r t' col • gens c col := by
      have h3 : N.mulVec (N⁻¹.mulVec y) = y := by
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv N hunit, Matrix.one_mulVec]
      conv_lhs => rw [← h3]
      funext t
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      apply Finset.sum_congr rfl
      intro t' _
      rw [hNdef, hN, mul_comm]
    rw [hy]
    refine Submodule.sum_mem _ fun t' _ => Submodule.smul_mem _ _ ?_
    refine Submodule.sum_mem _ fun col _ => Submodule.smul_mem _ _ ?_
    exact Submodule.subset_span ⟨col, rfl⟩

end generic

end OMA.Cube

namespace OMA.Cube

section transport

variable {α β γ S E F G : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]
variable {α' β' γ' S' E' F' G' : Type} [DecidableEq α'] [DecidableEq β'] [DecidableEq γ']

/-- Spanning only depends on the sizes of the index types. -/
theorem FillsT.congr (ea : α ≃ α') (eb : β ≃ β') (ec : γ ≃ γ') (eS : S ≃ S') (eE : E ≃ E')
    (eF : F ≃ F') (eG : G ≃ G') (h : FillsT α β γ S E F G) : FillsT α' β' γ' S' E' F' G' := by
  obtain ⟨c, hc⟩ := h
  let ptm : Pt S' E' F' G' → Pt S E F G :=
    Sum.map eS.symm (Sum.map eE.symm (Sum.map eF.symm eG.symm))
  let cm : Coord α' β' γ' → Coord α β γ := Sum.map ea.symm (Sum.map eb.symm ec.symm)
  let c' : Conf α' β' γ' S' E' F' G' := fun pc => c (ptm pc.1, cm pc.2)
  let Φ : (α × β × γ → ℂ) →ₗ[ℂ] (α' × β' × γ' → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun t => (ea.symm t.1, eb.symm t.2.1, ec.symm t.2.2))
  refine ⟨c', ?_⟩
  rw [eq_top_iff]
  intro f' _
  have key := map_mem_of_span Φ (SpanC c') c hc ?_ (fun t => f' (ea t.1, eb t.2.1, ec t.2.2))
  · have he : Φ (fun t => f' (ea t.1, eb t.2.1, ec t.2.2)) = f' := by
      funext t
      simp [Φ, LinearMap.funLeft]
    rwa [he] at key
  · intro col
    rcases col with ⟨p, i⟩ | ⟨p, j⟩ | ⟨p, k⟩
    · have : Φ (gens c (Sum.inl (p, i))) = gens c' (Sum.inl (Sum.map eS eE p, ea i)) := by
        funext t
        rcases p with s | e <;>
          simp [Φ, gens, gen1, vvec, wvec, pt1, c', ptm, cm, LinearMap.funLeft,
            Equiv.symm_apply_eq]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : Φ (gens c (Sum.inr (Sum.inl (p, j)))) =
          gens c' (Sum.inr (Sum.inl (Sum.map eS eF p, eb j))) := by
        funext t
        rcases p with s | e <;>
          simp [Φ, gens, gen2, uvec, wvec, pt2, c', ptm, cm, LinearMap.funLeft,
            Equiv.symm_apply_eq]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : Φ (gens c (Sum.inr (Sum.inr (p, k)))) =
          gens c' (Sum.inr (Sum.inr (Sum.map eS eG p, ec k))) := by
        funext t
        rcases p with s | e <;>
          simp [Φ, gens, gen3, uvec, vvec, pt3, c', ptm, cm, LinearMap.funLeft,
            Equiv.symm_apply_eq]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩

/-- Exchanging the first two sides exchanges the first two families of lines. -/
theorem FillsT.swap12 (h : FillsT α β γ S E F G) : FillsT β α γ S F E G := by
  obtain ⟨c, hc⟩ := h
  let ptm : Pt S F E G → Pt S E F G :=
    Sum.elim Sum.inl (Sum.elim (fun f => Sum.inr (Sum.inr (Sum.inl f)))
      (Sum.elim (fun e => Sum.inr (Sum.inl e)) (fun g => Sum.inr (Sum.inr (Sum.inr g)))))
  let cm : Coord β α γ → Coord α β γ :=
    Sum.elim (fun b => Sum.inr (Sum.inl b)) (Sum.elim Sum.inl (fun k => Sum.inr (Sum.inr k)))
  let c' : Conf β α γ S F E G := fun pc => c (ptm pc.1, cm pc.2)
  let Φ : (α × β × γ → ℂ) →ₗ[ℂ] (β × α × γ → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun t => (t.2.1, t.1, t.2.2))
  refine ⟨c', ?_⟩
  rw [eq_top_iff]
  intro f' _
  have key := map_mem_of_span Φ (SpanC c') c hc ?_ (fun t => f' (t.2.1, t.1, t.2.2))
  · have he : Φ (fun t => f' (t.2.1, t.1, t.2.2)) = f' := by
      funext t
      simp [Φ, LinearMap.funLeft]
    rwa [he] at key
  · intro col
    rcases col with ⟨p, i⟩ | ⟨p, j⟩ | ⟨p, k⟩
    · have : Φ (gens c (Sum.inl (p, i))) = gens c' (Sum.inr (Sum.inl (p, i))) := by
        funext t
        rcases p with s | e <;>
          simp [Φ, gens, gen1, gen2, uvec, vvec, wvec, pt1, pt2, c', ptm, cm, LinearMap.funLeft]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : Φ (gens c (Sum.inr (Sum.inl (p, j)))) = gens c' (Sum.inl (p, j)) := by
        funext t
        rcases p with s | e <;>
          simp [Φ, gens, gen1, gen2, uvec, vvec, wvec, pt1, pt2, c', ptm, cm, LinearMap.funLeft]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : Φ (gens c (Sum.inr (Sum.inr (p, k)))) = gens c' (Sum.inr (Sum.inr (p, k))) := by
        funext t
        rcases p with s | e <;>
          simp [Φ, gens, gen3, uvec, vvec, pt3, c', ptm, cm, LinearMap.funLeft, mul_comm]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩

/-- Exchanging the last two sides exchanges the last two families of lines. -/
theorem FillsT.swap23 (h : FillsT α β γ S E F G) : FillsT α γ β S E G F := by
  obtain ⟨c, hc⟩ := h
  let ptm : Pt S E G F → Pt S E F G :=
    Sum.elim Sum.inl (Sum.elim (fun e => Sum.inr (Sum.inl e))
      (Sum.elim (fun g => Sum.inr (Sum.inr (Sum.inr g))) (fun f => Sum.inr (Sum.inr (Sum.inl f)))))
  let cm : Coord α γ β → Coord α β γ :=
    Sum.elim Sum.inl (Sum.elim (fun k => Sum.inr (Sum.inr k)) (fun b => Sum.inr (Sum.inl b)))
  let c' : Conf α γ β S E G F := fun pc => c (ptm pc.1, cm pc.2)
  let Φ : (α × β × γ → ℂ) →ₗ[ℂ] (α × γ × β → ℂ) :=
    LinearMap.funLeft ℂ ℂ (fun t => (t.1, t.2.2, t.2.1))
  refine ⟨c', ?_⟩
  rw [eq_top_iff]
  intro f' _
  have key := map_mem_of_span Φ (SpanC c') c hc ?_ (fun t => f' (t.1, t.2.2, t.2.1))
  · have he : Φ (fun t => f' (t.1, t.2.2, t.2.1)) = f' := by
      funext t
      simp [Φ, LinearMap.funLeft]
    rwa [he] at key
  · intro col
    rcases col with ⟨p, i⟩ | ⟨p, j⟩ | ⟨p, k⟩
    · have : Φ (gens c (Sum.inl (p, i))) = gens c' (Sum.inl (p, i)) := by
        funext t
        rcases p with s | e <;>
          simp [Φ, gens, gen1, vvec, wvec, pt1, c', ptm, cm, LinearMap.funLeft, mul_comm]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : Φ (gens c (Sum.inr (Sum.inl (p, j)))) = gens c' (Sum.inr (Sum.inr (p, j))) := by
        funext t
        rcases p with s | e <;>
          simp [Φ, gens, gen2, gen3, uvec, vvec, wvec, pt2, pt3, c', ptm, cm, LinearMap.funLeft]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : Φ (gens c (Sum.inr (Sum.inr (p, k)))) = gens c' (Sum.inr (Sum.inl (p, k))) := by
        funext t
        rcases p with s | e <;>
          simp [Φ, gens, gen2, gen3, uvec, vvec, wvec, pt2, pt3, c', ptm, cm, LinearMap.funLeft]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩

/-- Additional points never hurt. -/
theorem FillsT.mono {fS : S → S'} {fE : E → E'} {fF : F → F'} {fG : G → G'}
    (hS : Function.Injective fS) (hE : Function.Injective fE) (hF : Function.Injective fF)
    (hG : Function.Injective fG) (h : FillsT α β γ S E F G) : FillsT α β γ S' E' F' G' := by
  classical
  obtain ⟨c, hc⟩ := h
  let pe : Pt S E F G → Pt S' E' F' G' := Sum.map fS (Sum.map fE (Sum.map fF fG))
  have hpe : Function.Injective pe :=
    hS.sumMap (hE.sumMap (hF.sumMap hG))
  let e : Pt S E F G × Coord α β γ → Pt S' E' F' G' × Coord α β γ := Prod.map pe id
  have he : Function.Injective e := hpe.prodMap Function.injective_id
  let c' : Conf α β γ S' E' F' G' := Function.extend e c 0
  have hc' : ∀ p x, c' (pe p, x) = c (p, x) := fun p x => he.extend_apply c 0 (p, x)
  refine ⟨c', ?_⟩
  rw [eq_top_iff, ← hc]
  apply Submodule.span_le.mpr
  rintro _ ⟨col, rfl⟩
  rcases col with ⟨p, i⟩ | ⟨p, j⟩ | ⟨p, k⟩
  · have : gens c (Sum.inl (p, i)) = gens c' (Sum.inl (Sum.map fS fE p, i)) := by
      rcases p with s | x <;> simp only [gens, pt1, Sum.elim_inl, Sum.elim_inr,
        Sum.map_inl, Sum.map_inr] <;> congr 1 <;> funext y <;> exact (hc' _ _).symm
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩
  · have : gens c (Sum.inr (Sum.inl (p, j))) = gens c' (Sum.inr (Sum.inl (Sum.map fS fF p, j))) := by
      rcases p with s | x <;> simp only [gens, pt2, Sum.elim_inl, Sum.elim_inr,
        Sum.map_inl, Sum.map_inr] <;> congr 1 <;> funext y <;> exact (hc' _ _).symm
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩
  · have : gens c (Sum.inr (Sum.inr (p, k))) = gens c' (Sum.inr (Sum.inr (Sum.map fS fG p, k))) := by
      rcases p with s | x <;> simp only [gens, pt3, Sum.elim_inl, Sum.elim_inr,
        Sum.map_inl, Sum.map_inr] <;> congr 1 <;> funext y <;> exact (hc' _ _).symm
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩

end transport

/-- Spanning in a box with given side lengths and numbers of points of each kind. -/
def Fills (a b c s x y z : ℕ) : Prop :=
  FillsT (Fin a) (Fin b) (Fin c) (Fin s) (Fin x) (Fin y) (Fin z)

theorem Fills.swap12 {a b c s x y z : ℕ} (h : Fills a b c s x y z) : Fills b a c s y x z :=
  FillsT.swap12 h

theorem Fills.swap23 {a b c s x y z : ℕ} (h : Fills a b c s x y z) : Fills a c b s x z y :=
  FillsT.swap23 h

theorem Fills.swap13 {a b c s x y z : ℕ} (h : Fills a b c s x y z) : Fills c b a s z y x :=
  h.swap12.swap23.swap12

theorem Fills.mono {a b c s x y z s' x' y' z' : ℕ} (h : Fills a b c s x y z)
    (hs : s ≤ s') (hx : x ≤ x') (hy : y ≤ y') (hz : z ≤ z') : Fills a b c s' x' y' z' :=
  FillsT.mono (Fin.castLE_injective hs) (Fin.castLE_injective hx) (Fin.castLE_injective hy)
    (Fin.castLE_injective hz) h

end OMA.Cube

namespace OMA.Cube

open MvPolynomial

section ext

variable {α1 α2 β γ : Type}

/-- Extension by zero from the first block of the first side. -/
def extL : (α1 × β × γ → ℂ) →ₗ[ℂ] ((α1 ⊕ α2) × β × γ → ℂ) where
  toFun f := fun t => Sum.elim (fun i => f (i, t.2)) (fun _ => 0) t.1
  map_add' f g := by
    funext ⟨a, t⟩
    cases a <;> simp
  map_smul' r f := by
    funext ⟨a, t⟩
    cases a <;> simp

/-- Extension by zero from the second block of the first side. -/
def extR : (α2 × β × γ → ℂ) →ₗ[ℂ] ((α1 ⊕ α2) × β × γ → ℂ) where
  toFun f := fun t => Sum.elim (fun _ => 0) (fun i => f (i, t.2)) t.1
  map_add' f g := by
    funext ⟨a, t⟩
    cases a <;> simp
  map_smul' r f := by
    funext ⟨a, t⟩
    cases a <;> simp

theorem extL_gen1 [DecidableEq α1] [DecidableEq α2] (v : β → ℂ) (w : γ → ℂ) (i : α1) :
    extL (α2 := α2) (gen1 v w i) = gen1 v w (Sum.inl i) := by
  funext ⟨a, b, k⟩
  cases a <;> simp [extL, gen1]

theorem extL_gen2 [DecidableEq β] (u : α1 → ℂ) (w : γ → ℂ) (j : β) :
    extL (α2 := α2) (gen2 u w j) = gen2 (Sum.elim u 0) w j := by
  funext ⟨a, b, k⟩
  cases a <;> simp [extL, gen2]

theorem extL_gen3 [DecidableEq γ] (u : α1 → ℂ) (v : β → ℂ) (k : γ) :
    extL (α2 := α2) (gen3 u v k) = gen3 (Sum.elim u 0) v k := by
  funext ⟨a, b, l⟩
  cases a <;> simp [extL, gen3]

theorem extR_gen1 [DecidableEq α1] [DecidableEq α2] (v : β → ℂ) (w : γ → ℂ) (i : α2) :
    extR (α1 := α1) (gen1 v w i) = gen1 v w (Sum.inr i) := by
  funext ⟨a, b, k⟩
  cases a <;> simp [extR, gen1]

theorem extR_gen2 [DecidableEq β] (u : α2 → ℂ) (w : γ → ℂ) (j : β) :
    extR (α1 := α1) (gen2 u w j) = gen2 (Sum.elim 0 u) w j := by
  funext ⟨a, b, k⟩
  cases a <;> simp [extR, gen2]

theorem extR_gen3 [DecidableEq γ] (u : α2 → ℂ) (v : β → ℂ) (k : γ) :
    extR (α1 := α1) (gen3 u v k) = gen3 (Sum.elim 0 u) v k := by
  funext ⟨a, b, l⟩
  cases a <;> simp [extR, gen3]

theorem single_inl [DecidableEq α1] [DecidableEq α2] [DecidableEq β] [DecidableEq γ] (i : α1) (t : β × γ) :
    (Pi.single (Sum.inl i, t) 1 : (α1 ⊕ α2) × β × γ → ℂ) = extL (Pi.single (i, t) 1) := by
  funext ⟨a, t'⟩
  cases a <;> simp [extL, Pi.single_apply]

theorem single_inr [DecidableEq α1] [DecidableEq α2] [DecidableEq β] [DecidableEq γ] (i : α2) (t : β × γ) :
    (Pi.single (Sum.inr i, t) 1 : (α1 ⊕ α2) × β × γ → ℂ) = extR (Pi.single (i, t) 1) := by
  funext ⟨a, t'⟩
  cases a <;> simp [extR, Pi.single_apply]

end ext

section split

variable {α1 α2 β γ S1 S2 E F1 F2 G1 G2 : Type}
  [Fintype α1] [Fintype α2] [Fintype β] [Fintype γ]
  [DecidableEq α1] [DecidableEq α2] [DecidableEq β] [DecidableEq γ]

/-- Splitting the first side: points of one half only contribute their first line to the
other half. -/
theorem splitT (h1 : GenT α1 β γ S1 (E ⊕ S2) F1 G1) (h2 : GenT α2 β γ S2 (E ⊕ S1) F2 G2) :
    FillsT (α1 ⊕ α2) β γ (S1 ⊕ S2) E (F1 ⊕ F2) (G1 ⊕ G2) := by
  obtain ⟨P1, hP1, hf1⟩ := h1
  obtain ⟨P2, hP2, hf2⟩ := h2
  let p1 : Pt S1 (E ⊕ S2) F1 G1 → Pt (S1 ⊕ S2) E (F1 ⊕ F2) (G1 ⊕ G2) :=
    Sum.elim (fun s => Sum.inl (Sum.inl s))
      (Sum.elim (Sum.elim (fun e => Sum.inr (Sum.inl e)) (fun s => Sum.inl (Sum.inr s)))
        (Sum.elim (fun f => Sum.inr (Sum.inr (Sum.inl (Sum.inl f))))
          (fun g => Sum.inr (Sum.inr (Sum.inr (Sum.inl g))))))
  let p2 : Pt S2 (E ⊕ S1) F2 G2 → Pt (S1 ⊕ S2) E (F1 ⊕ F2) (G1 ⊕ G2) :=
    Sum.elim (fun s => Sum.inl (Sum.inr s))
      (Sum.elim (Sum.elim (fun e => Sum.inr (Sum.inl e)) (fun s => Sum.inl (Sum.inl s)))
        (Sum.elim (fun f => Sum.inr (Sum.inr (Sum.inl (Sum.inr f))))
          (fun g => Sum.inr (Sum.inr (Sum.inr (Sum.inr g))))))
  let k1 : Coord α1 β γ → Coord (α1 ⊕ α2) β γ := Sum.map Sum.inl id
  let k2 : Coord α2 β γ → Coord (α1 ⊕ α2) β γ := Sum.map Sum.inr id
  have hp1 : Function.Injective p1 := by
    rintro (s | (e | s) | f | g) (s' | (e' | s') | f' | g') h <;> simp [p1] at h <;> simp [h]
  have hp2 : Function.Injective p2 := by
    rintro (s | (e | s) | f | g) (s' | (e' | s') | f' | g') h <;> simp [p2] at h <;> simp [h]
  have hk1 : Function.Injective k1 := Sum.inl_injective.sumMap Function.injective_id
  have hk2 : Function.Injective k2 := Sum.inr_injective.sumMap Function.injective_id
  let e1 := Prod.map p1 k1
  let e2 := Prod.map p2 k2
  have he1 : Function.Injective e1 := hp1.prodMap hk1
  have he2 : Function.Injective e2 := hp2.prodMap hk2
  have hQ : rename e1 P1 * rename e2 P2 ≠ 0 :=
    mul_ne_zero ((map_ne_zero_iff _ (rename_injective e1 he1)).mpr hP1)
      ((map_ne_zero_iff _ (rename_injective e2 he2)).mpr hP2)
  obtain ⟨g, hg⟩ := exists_eval_ne_zero hQ
  rw [map_mul, eval_rename, eval_rename] at hg
  have hs1 := hf1 (g ∘ e1) (left_ne_zero_of_mul hg)
  have hs2 := hf2 (g ∘ e2) (right_ne_zero_of_mul hg)
  let noR : Pt (S1 ⊕ S2) E (F1 ⊕ F2) (G1 ⊕ G2) → Bool :=
    Sum.elim (Sum.elim (fun _ => true) (fun _ => false))
      (Sum.elim (fun _ => false)
        (Sum.elim (Sum.elim (fun _ => true) (fun _ => false))
          (Sum.elim (fun _ => true) (fun _ => false))))
  let noL : Pt (S1 ⊕ S2) E (F1 ⊕ F2) (G1 ⊕ G2) → Bool :=
    Sum.elim (Sum.elim (fun _ => false) (fun _ => true))
      (Sum.elim (fun _ => false)
        (Sum.elim (Sum.elim (fun _ => false) (fun _ => true))
          (Sum.elim (fun _ => false) (fun _ => true))))
  let c : Conf (α1 ⊕ α2) β γ (S1 ⊕ S2) E (F1 ⊕ F2) (G1 ⊕ G2) := fun pc =>
    Sum.elim
      (Sum.elim (fun i => if noL pc.1 then 0 else g (pc.1, Sum.inl (Sum.inl i)))
        (fun i => if noR pc.1 then 0 else g (pc.1, Sum.inl (Sum.inr i))))
      (fun y => g (pc.1, Sum.inr y)) pc.2
  refine ⟨c, eq_top_of_single _ ?_⟩
  have hL : ∀ f, extL f ∈ SpanC c := by
    apply map_mem_of_span extL (SpanC c) (g ∘ e1) hs1
    rintro (⟨s | e | s, i⟩ | ⟨s | f, j⟩ | ⟨s | f, k⟩)
    · simp only [gens, extL_gen1]
      convert gen1_mem c (Sum.inl (Sum.inl s)) (Sum.inl i) using 2 <;>
        (funext y; simp [vvec, wvec, c, e1, p1, k1, pt1])
    · simp only [gens, extL_gen1]
      convert gen1_mem c (Sum.inr e) (Sum.inl i) using 2 <;>
        (funext y; simp [vvec, wvec, c, e1, p1, k1, pt1])
    · simp only [gens, extL_gen1]
      convert gen1_mem c (Sum.inl (Sum.inr s)) (Sum.inl i) using 2 <;>
        (funext y; simp [vvec, wvec, c, e1, p1, k1, pt1])
    · simp only [gens, extL_gen2]
      convert gen2_mem c (Sum.inl (Sum.inl s)) j using 2 <;>
        (funext y; first | (rcases y with y | y <;> simp [uvec, c, e1, p1, k1, pt2, noL, noR]) | simp [wvec, c, e1, p1, k1, pt2])
    · simp only [gens, extL_gen2]
      convert gen2_mem c (Sum.inr (Sum.inl f)) j using 2 <;>
        (funext y; first | (rcases y with y | y <;> simp [uvec, c, e1, p1, k1, pt2, noL, noR]) | simp [wvec, c, e1, p1, k1, pt2])
    · simp only [gens, extL_gen3]
      convert gen3_mem c (Sum.inl (Sum.inl s)) k using 2 <;>
        (funext y; first | (rcases y with y | y <;> simp [uvec, c, e1, p1, k1, pt3, noL, noR]) | simp [vvec, c, e1, p1, k1, pt3])
    · simp only [gens, extL_gen3]
      convert gen3_mem c (Sum.inr (Sum.inl f)) k using 2 <;>
        (funext y; first | (rcases y with y | y <;> simp [uvec, c, e1, p1, k1, pt3, noL, noR]) | simp [vvec, c, e1, p1, k1, pt3])
  have hR : ∀ f, extR f ∈ SpanC c := by
    apply map_mem_of_span extR (SpanC c) (g ∘ e2) hs2
    rintro (⟨s | e | s, i⟩ | ⟨s | f, j⟩ | ⟨s | f, k⟩)
    · simp only [gens, extR_gen1]
      convert gen1_mem c (Sum.inl (Sum.inr s)) (Sum.inr i) using 2 <;>
        (funext y; simp [vvec, wvec, c, e2, p2, k2, pt1])
    · simp only [gens, extR_gen1]
      convert gen1_mem c (Sum.inr e) (Sum.inr i) using 2 <;>
        (funext y; simp [vvec, wvec, c, e2, p2, k2, pt1])
    · simp only [gens, extR_gen1]
      convert gen1_mem c (Sum.inl (Sum.inl s)) (Sum.inr i) using 2 <;>
        (funext y; simp [vvec, wvec, c, e2, p2, k2, pt1])
    · simp only [gens, extR_gen2]
      convert gen2_mem c (Sum.inl (Sum.inr s)) j using 2 <;>
        (funext y; first | (rcases y with y | y <;> simp [uvec, c, e2, p2, k2, pt2, noL, noR]) | simp [wvec, c, e2, p2, k2, pt2])
    · simp only [gens, extR_gen2]
      convert gen2_mem c (Sum.inr (Sum.inr f)) j using 2 <;>
        (funext y; first | (rcases y with y | y <;> simp [uvec, c, e2, p2, k2, pt2, noL, noR]) | simp [wvec, c, e2, p2, k2, pt2])
    · simp only [gens, extR_gen3]
      convert gen3_mem c (Sum.inl (Sum.inr s)) k using 2 <;>
        (funext y; first | (rcases y with y | y <;> simp [uvec, c, e2, p2, k2, pt3, noL, noR]) | simp [vvec, c, e2, p2, k2, pt3])
    · simp only [gens, extR_gen3]
      convert gen3_mem c (Sum.inr (Sum.inr f)) k using 2 <;>
        (funext y; first | (rcases y with y | y <;> simp [uvec, c, e2, p2, k2, pt3, noL, noR]) | simp [vvec, c, e2, p2, k2, pt3])
  rintro ⟨a | a, t⟩
  · rw [single_inl]
    exact hL _
  · rw [single_inr]
    exact hR _

end split

end OMA.Cube

namespace OMA.Cube

open MvPolynomial

section extC

variable {α β γ1 γ2 : Type}

/-- Extension by zero from the first block of the third side. -/
def extCL : (α × β × γ1 → ℂ) →ₗ[ℂ] (α × β × (γ1 ⊕ γ2) → ℂ) where
  toFun f := fun t => Sum.elim (fun k => f (t.1, t.2.1, k)) (fun _ => 0) t.2.2
  map_add' f g := by
    funext ⟨a, b, k⟩
    cases k <;> simp
  map_smul' r f := by
    funext ⟨a, b, k⟩
    cases k <;> simp

/-- Extension by zero from the second block of the third side. -/
def extCR : (α × β × γ2 → ℂ) →ₗ[ℂ] (α × β × (γ1 ⊕ γ2) → ℂ) where
  toFun f := fun t => Sum.elim (fun _ => 0) (fun k => f (t.1, t.2.1, k)) t.2.2
  map_add' f g := by
    funext ⟨a, b, k⟩
    cases k <;> simp
  map_smul' r f := by
    funext ⟨a, b, k⟩
    cases k <;> simp

end extC

section diag

variable {αs αr β γs γr Nss Nsr Nrs Nrr D1 D2 : Type}

/-- The six kinds of points of the specialised configuration. -/
abbrev DPt (Nss Nsr Nrs Nrr D1 D2 : Type) := Nss ⊕ Nsr ⊕ Nrs ⊕ Nrr ⊕ D1 ⊕ D2

def qss (n : Nss) : DPt Nss Nsr Nrs Nrr D1 D2 := Sum.inl n
def qsr (n : Nsr) : DPt Nss Nsr Nrs Nrr D1 D2 := Sum.inr (Sum.inl n)
def qrs (n : Nrs) : DPt Nss Nsr Nrs Nrr D1 D2 := Sum.inr (Sum.inr (Sum.inl n))
def qrr (n : Nrr) : DPt Nss Nsr Nrs Nrr D1 D2 := Sum.inr (Sum.inr (Sum.inr (Sum.inl n)))
def qd1 (n : D1) : DPt Nss Nsr Nrs Nrr D1 D2 :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl n))))
def qd2 (n : D2) : DPt Nss Nsr Nrs Nrr D1 D2 :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr n))))

/-- Which blocks of the first and third vectors of a point are allowed to be nonzero. -/
def uS : DPt Nss Nsr Nrs Nrr D1 D2 → Bool :=
  Sum.elim (fun _ => true) (Sum.elim (fun _ => true) (Sum.elim (fun _ => false)
    (Sum.elim (fun _ => false) (Sum.elim (fun _ => false) (fun _ => true)))))
def uR : DPt Nss Nsr Nrs Nrr D1 D2 → Bool :=
  Sum.elim (fun _ => false) (Sum.elim (fun _ => false) (Sum.elim (fun _ => true)
    (Sum.elim (fun _ => true) (Sum.elim (fun _ => true) (fun _ => true)))))
def wS : DPt Nss Nsr Nrs Nrr D1 D2 → Bool :=
  Sum.elim (fun _ => true) (Sum.elim (fun _ => false) (Sum.elim (fun _ => true)
    (Sum.elim (fun _ => false) (Sum.elim (fun _ => true) (fun _ => false)))))
def wR : DPt Nss Nsr Nrs Nrr D1 D2 → Bool :=
  Sum.elim (fun _ => false) (Sum.elim (fun _ => true) (Sum.elim (fun _ => false)
    (Sum.elim (fun _ => true) (Sum.elim (fun _ => true) (fun _ => true)))))

/-- The specialised configuration: forbidden blocks are set to zero. -/
def dmask (g : Conf (αs ⊕ αr) β (γs ⊕ γr) (DPt Nss Nsr Nrs Nrr D1 D2) Empty Empty Empty) :
    Conf (αs ⊕ αr) β (γs ⊕ γr) (DPt Nss Nsr Nrs Nrr D1 D2) Empty Empty Empty := fun pc =>
  Sum.elim
    (fun q => Sum.elim
      (Sum.elim (fun i => if uS q then g (Sum.inl q, Sum.inl (Sum.inl i)) else 0)
        (fun i => if uR q then g (Sum.inl q, Sum.inl (Sum.inr i)) else 0))
      (Sum.elim (fun j => g (Sum.inl q, Sum.inr (Sum.inl j)))
        (Sum.elim (fun k => if wS q then g (Sum.inl q, Sum.inr (Sum.inr (Sum.inl k))) else 0)
          (fun k => if wR q then g (Sum.inl q, Sum.inr (Sum.inr (Sum.inr k))) else 0))) pc.2)
    (fun _ => 0) pc.1

def pss : Pt Nss Nrs Empty Nsr → Pt (DPt Nss Nsr Nrs Nrr D1 D2) Empty Empty Empty :=
  Sum.elim (fun n => Sum.inl (qss n)) (Sum.elim (fun n => Sum.inl (qrs n))
    (Sum.elim (fun e => e.elim) (fun n => Sum.inl (qsr n))))

def psr : Pt (Nsr ⊕ D2) (Nrr ⊕ D1) Empty Nss → Pt (DPt Nss Nsr Nrs Nrr D1 D2) Empty Empty Empty :=
  Sum.elim (Sum.elim (fun n => Sum.inl (qsr n)) (fun d => Sum.inl (qd2 d)))
    (Sum.elim (Sum.elim (fun n => Sum.inl (qrr n)) (fun d => Sum.inl (qd1 d)))
      (Sum.elim (fun e => e.elim) (fun n => Sum.inl (qss n))))

def prs : Pt (Nrs ⊕ D1) Nss Empty (Nrr ⊕ D2) → Pt (DPt Nss Nsr Nrs Nrr D1 D2) Empty Empty Empty :=
  Sum.elim (Sum.elim (fun n => Sum.inl (qrs n)) (fun d => Sum.inl (qd1 d)))
    (Sum.elim (fun n => Sum.inl (qss n))
      (Sum.elim (fun e => e.elim) (Sum.elim (fun n => Sum.inl (qrr n)) (fun d => Sum.inl (qd2 d)))))

def prr : Pt Nrr (Nsr ⊕ D2) Empty (Nrs ⊕ D1) → Pt (DPt Nss Nsr Nrs Nrr D1 D2) Empty Empty Empty :=
  Sum.elim (fun n => Sum.inl (qrr n))
    (Sum.elim (Sum.elim (fun n => Sum.inl (qsr n)) (fun d => Sum.inl (qd2 d)))
      (Sum.elim (fun e => e.elim) (Sum.elim (fun n => Sum.inl (qrs n)) (fun d => Sum.inl (qd1 d)))))

theorem pss_injective : Function.Injective (pss (Nrr := Nrr) (D1 := D1) (D2 := D2) (Nss := Nss)
    (Nsr := Nsr) (Nrs := Nrs)) := by
  rintro (n | n | e | n) (n' | n' | e' | n') h <;>
    first | exact e.elim | exact e'.elim | (simp [pss, qss, qsr, qrs] at h <;> simp [h])

theorem psr_injective : Function.Injective (psr (Nrr := Nrr) (D1 := D1) (D2 := D2) (Nss := Nss)
    (Nsr := Nsr) (Nrs := Nrs)) := by
  rintro ((n | n) | (n | n) | e | n) ((n' | n') | (n' | n') | e' | n') h <;>
    first | exact e.elim | exact e'.elim
          | (simp [psr, qss, qsr, qrr, qd1, qd2] at h <;> simp [h])

theorem prs_injective : Function.Injective (prs (Nrr := Nrr) (D1 := D1) (D2 := D2) (Nss := Nss)
    (Nsr := Nsr) (Nrs := Nrs)) := by
  rintro ((n | n) | n | e | (n | n)) ((n' | n') | n' | e' | (n' | n')) h <;>
    first | exact e.elim | exact e'.elim
          | (simp [prs, qss, qrs, qrr, qd1, qd2] at h <;> simp [h])

theorem prr_injective : Function.Injective (prr (Nrr := Nrr) (D1 := D1) (D2 := D2) (Nss := Nss)
    (Nsr := Nsr) (Nrs := Nrs)) := by
  rintro (n | (n | n) | e | (n | n)) (n' | (n' | n') | e' | (n' | n')) h <;>
    first | exact e.elim | exact e'.elim
          | (simp [prr, qsr, qrs, qrr, qd1, qd2] at h <;> simp [h])

variable [Fintype αs] [Fintype αr] [Fintype β] [Fintype γs] [Fintype γr]
  [DecidableEq αs] [DecidableEq αr] [DecidableEq β] [DecidableEq γs] [DecidableEq γr]

/-- Splitting the first and the third side at once. Besides the points lying in one of the
four cells there are points straddling two cells; such a point sends one of its lines to the
diagonally opposite cell. -/
theorem diagT (hss : GenT αs β γs Nss Nrs Empty Nsr)
    (hsr : GenT αs β γr (Nsr ⊕ D2) (Nrr ⊕ D1) Empty Nss)
    (hrs : GenT αr β γs (Nrs ⊕ D1) Nss Empty (Nrr ⊕ D2))
    (hrr : GenT αr β γr Nrr (Nsr ⊕ D2) Empty (Nrs ⊕ D1)) :
    FillsT (αs ⊕ αr) β (γs ⊕ γr) (DPt Nss Nsr Nrs Nrr D1 D2) Empty Empty Empty := by
  obtain ⟨Pss, hPss, fss⟩ := hss
  obtain ⟨Psr, hPsr, fsr⟩ := hsr
  obtain ⟨Prs, hPrs, frs⟩ := hrs
  obtain ⟨Prr, hPrr, frr⟩ := hrr
  let kss : Coord αs β γs → Coord (αs ⊕ αr) β (γs ⊕ γr) := Sum.map Sum.inl (Sum.map id Sum.inl)
  let ksr : Coord αs β γr → Coord (αs ⊕ αr) β (γs ⊕ γr) := Sum.map Sum.inl (Sum.map id Sum.inr)
  let krs : Coord αr β γs → Coord (αs ⊕ αr) β (γs ⊕ γr) := Sum.map Sum.inr (Sum.map id Sum.inl)
  let krr : Coord αr β γr → Coord (αs ⊕ αr) β (γs ⊕ γr) := Sum.map Sum.inr (Sum.map id Sum.inr)
  have hkss : Function.Injective kss :=
    Sum.inl_injective.sumMap (Function.injective_id.sumMap Sum.inl_injective)
  have hksr : Function.Injective ksr :=
    Sum.inl_injective.sumMap (Function.injective_id.sumMap Sum.inr_injective)
  have hkrs : Function.Injective krs :=
    Sum.inr_injective.sumMap (Function.injective_id.sumMap Sum.inl_injective)
  have hkrr : Function.Injective krr :=
    Sum.inr_injective.sumMap (Function.injective_id.sumMap Sum.inr_injective)
  let ess := Prod.map (pss (Nss := Nss) (Nsr := Nsr) (Nrs := Nrs) (Nrr := Nrr) (D1 := D1) (D2 := D2)) kss
  let esr := Prod.map (psr (Nss := Nss) (Nsr := Nsr) (Nrs := Nrs) (Nrr := Nrr) (D1 := D1) (D2 := D2)) ksr
  let ers := Prod.map (prs (Nss := Nss) (Nsr := Nsr) (Nrs := Nrs) (Nrr := Nrr) (D1 := D1) (D2 := D2)) krs
  let err := Prod.map (prr (Nss := Nss) (Nsr := Nsr) (Nrs := Nrs) (Nrr := Nrr) (D1 := D1) (D2 := D2)) krr
  have hess : Function.Injective ess := pss_injective.prodMap hkss
  have hesr : Function.Injective esr := psr_injective.prodMap hksr
  have hers : Function.Injective ers := prs_injective.prodMap hkrs
  have herr : Function.Injective err := prr_injective.prodMap hkrr
  have hQ : (rename ess Pss * rename esr Psr) * (rename ers Prs * rename err Prr) ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero ((map_ne_zero_iff _ (rename_injective ess hess)).mpr hPss)
        ((map_ne_zero_iff _ (rename_injective esr hesr)).mpr hPsr))
      (mul_ne_zero ((map_ne_zero_iff _ (rename_injective ers hers)).mpr hPrs)
        ((map_ne_zero_iff _ (rename_injective err herr)).mpr hPrr))
  obtain ⟨g, hg⟩ := exists_eval_ne_zero hQ
  rw [map_mul, map_mul, map_mul, eval_rename, eval_rename, eval_rename, eval_rename] at hg
  have sss := fss (g ∘ ess) (left_ne_zero_of_mul (left_ne_zero_of_mul hg))
  have ssr := fsr (g ∘ esr) (right_ne_zero_of_mul (left_ne_zero_of_mul hg))
  have srs := frs (g ∘ ers) (left_ne_zero_of_mul (right_ne_zero_of_mul hg))
  have srr := frr (g ∘ err) (right_ne_zero_of_mul (right_ne_zero_of_mul hg))
  let c := dmask g
  let ιss : (αs × β × γs → ℂ) →ₗ[ℂ] ((αs ⊕ αr) × β × (γs ⊕ γr) → ℂ) := extCL.comp extL
  let ιsr : (αs × β × γr → ℂ) →ₗ[ℂ] ((αs ⊕ αr) × β × (γs ⊕ γr) → ℂ) := extCR.comp extL
  let ιrs : (αr × β × γs → ℂ) →ₗ[ℂ] ((αs ⊕ αr) × β × (γs ⊕ γr) → ℂ) := extCL.comp extR
  let ιrr : (αr × β × γr → ℂ) →ₗ[ℂ] ((αs ⊕ αr) × β × (γs ⊕ γr) → ℂ) := extCR.comp extR
  refine ⟨c, eq_top_of_single _ ?_⟩
  have Hrr : ∀ f, ιrr f ∈ SpanC c := by
    apply map_mem_of_span ιrr (SpanC c) (g ∘ err) srr
    rintro (⟨n | (n | d), i⟩ | ⟨n | e, j⟩ | ⟨n | (n | d), k⟩)
    · have : ιrr (gens (g ∘ err) (Sum.inl (Sum.inl n, i))) = gens c (Sum.inl (Sum.inl (qrr n), Sum.inr i)) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen1, vvec, wvec, extR, extCR, pt1, c, dmask,
          err, prr, krr, qsr, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrr]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιrr (gens (g ∘ err) (Sum.inl (Sum.inr (Sum.inl n), i))) = gens c (Sum.inl (Sum.inl (qsr n), Sum.inr i)) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen1, vvec, wvec, extR, extCR, pt1, c, dmask,
          err, prr, krr, qsr, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrr]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιrr (gens (g ∘ err) (Sum.inl (Sum.inr (Sum.inr d), i))) = gens c (Sum.inl (Sum.inl (qd2 d), Sum.inr i)) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen1, vvec, wvec, extR, extCR, pt1, c, dmask,
          err, prr, krr, qsr, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrr]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιrr (gens (g ∘ err) (Sum.inr (Sum.inl (Sum.inl n, j)))) = gens c (Sum.inr (Sum.inl (Sum.inl (qrr n), j))) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen2, uvec, wvec, extR, extCR, pt2, c, dmask,
          err, prr, krr, qsr, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrr]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · exact e.elim
    · have : ιrr (gens (g ∘ err) (Sum.inr (Sum.inr (Sum.inl n, k)))) = gens c (Sum.inr (Sum.inr (Sum.inl (qrr n), Sum.inr k))) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen3, uvec, vvec, extR, extCR, pt3, c, dmask,
          err, prr, krr, qsr, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrr]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιrr (gens (g ∘ err) (Sum.inr (Sum.inr (Sum.inr (Sum.inl n), k)))) = gens c (Sum.inr (Sum.inr (Sum.inl (qrs n), Sum.inr k))) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen3, uvec, vvec, extR, extCR, pt3, c, dmask,
          err, prr, krr, qsr, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrr]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιrr (gens (g ∘ err) (Sum.inr (Sum.inr (Sum.inr (Sum.inr d), k)))) = gens c (Sum.inr (Sum.inr (Sum.inl (qd1 d), Sum.inr k))) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen3, uvec, vvec, extR, extCR, pt3, c, dmask,
          err, prr, krr, qsr, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrr]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
  have Hss : ∀ f, ιss f ∈ SpanC c := by
    apply map_mem_of_span ιss (SpanC c) (g ∘ ess) sss
    rintro (⟨n | n, i⟩ | ⟨n | e, j⟩ | ⟨n | n, k⟩)
    · have : ιss (gens (g ∘ ess) (Sum.inl (Sum.inl n, i))) = gens c (Sum.inl (Sum.inl (qss n), Sum.inl i)) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen1, vvec, wvec, extL, extCL, pt1, c, dmask,
          ess, pss, kss, qss, qsr, qrs, uS, uR, wS, wR,
          ιss]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιss (gens (g ∘ ess) (Sum.inl (Sum.inr n, i))) = gens c (Sum.inl (Sum.inl (qrs n), Sum.inl i)) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen1, vvec, wvec, extL, extCL, pt1, c, dmask,
          ess, pss, kss, qss, qsr, qrs, uS, uR, wS, wR,
          ιss]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιss (gens (g ∘ ess) (Sum.inr (Sum.inl (Sum.inl n, j)))) = gens c (Sum.inr (Sum.inl (Sum.inl (qss n), j))) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen2, uvec, wvec, extL, extCL, pt2, c, dmask,
          ess, pss, kss, qss, qsr, qrs, uS, uR, wS, wR,
          ιss]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · exact e.elim
    · have : ιss (gens (g ∘ ess) (Sum.inr (Sum.inr (Sum.inl n, k)))) = gens c (Sum.inr (Sum.inr (Sum.inl (qss n), Sum.inl k))) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen3, uvec, vvec, extL, extCL, pt3, c, dmask,
          ess, pss, kss, qss, qsr, qrs, uS, uR, wS, wR,
          ιss]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιss (gens (g ∘ ess) (Sum.inr (Sum.inr (Sum.inr n, k)))) = gens c (Sum.inr (Sum.inr (Sum.inl (qsr n), Sum.inl k))) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen3, uvec, vvec, extL, extCL, pt3, c, dmask,
          ess, pss, kss, qss, qsr, qrs, uS, uR, wS, wR,
          ιss]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
  have Hrs : ∀ f, ιrs f ∈ SpanC c := by
    apply map_mem_of_span ιrs (SpanC c) (g ∘ ers) srs
    rintro (⟨(n | d) | n, i⟩ | ⟨(n | d) | e, j⟩ | ⟨(n | d) | (n | d), k⟩)
    · have : ιrs (gens (g ∘ ers) (Sum.inl (Sum.inl (Sum.inl n), i))) = gens c (Sum.inl (Sum.inl (qrs n), Sum.inr i)) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen1, vvec, wvec, extR, extCL, pt1, c, dmask,
          ers, prs, krs, qss, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrs]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιrs (gens (g ∘ ers) (Sum.inl (Sum.inl (Sum.inr d), i))) = gens c (Sum.inl (Sum.inl (qd1 d), Sum.inr i)) - ιrr (gen1 (fun j => g (Sum.inl (qd1 d), Sum.inr (Sum.inl j))) (fun k => g (Sum.inl (qd1 d), Sum.inr (Sum.inr (Sum.inr k)))) i) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen1, vvec, wvec, extR, extCL, extCR, pt1, c, dmask,
          ers, prs, krs, qss, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrs, ιrr]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Hrr _)
    · have : ιrs (gens (g ∘ ers) (Sum.inl (Sum.inr n, i))) = gens c (Sum.inl (Sum.inl (qss n), Sum.inr i)) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen1, vvec, wvec, extR, extCL, pt1, c, dmask,
          ers, prs, krs, qss, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrs]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιrs (gens (g ∘ ers) (Sum.inr (Sum.inl (Sum.inl (Sum.inl n), j)))) = gens c (Sum.inr (Sum.inl (Sum.inl (qrs n), j))) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen2, uvec, wvec, extR, extCL, pt2, c, dmask,
          ers, prs, krs, qss, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrs]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιrs (gens (g ∘ ers) (Sum.inr (Sum.inl (Sum.inl (Sum.inr d), j)))) = gens c (Sum.inr (Sum.inl (Sum.inl (qd1 d), j))) - ιrr (gen2 (fun i => g (Sum.inl (qd1 d), Sum.inl (Sum.inr i))) (fun k => g (Sum.inl (qd1 d), Sum.inr (Sum.inr (Sum.inr k)))) j) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen2, uvec, wvec, extR, extCL, extCR, pt2, c, dmask,
          ers, prs, krs, qss, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrs, ιrr]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Hrr _)
    · exact e.elim
    · have : ιrs (gens (g ∘ ers) (Sum.inr (Sum.inr (Sum.inl (Sum.inl n), k)))) = gens c (Sum.inr (Sum.inr (Sum.inl (qrs n), Sum.inl k))) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen3, uvec, vvec, extR, extCL, pt3, c, dmask,
          ers, prs, krs, qss, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrs]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιrs (gens (g ∘ ers) (Sum.inr (Sum.inr (Sum.inl (Sum.inr d), k)))) = gens c (Sum.inr (Sum.inr (Sum.inl (qd1 d), Sum.inl k))) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen3, uvec, vvec, extR, extCL, pt3, c, dmask,
          ers, prs, krs, qss, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrs]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιrs (gens (g ∘ ers) (Sum.inr (Sum.inr (Sum.inr (Sum.inl n), k)))) = gens c (Sum.inr (Sum.inr (Sum.inl (qrr n), Sum.inl k))) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen3, uvec, vvec, extR, extCL, pt3, c, dmask,
          ers, prs, krs, qss, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιrs]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιrs (gens (g ∘ ers) (Sum.inr (Sum.inr (Sum.inr (Sum.inr d), k)))) = gens c (Sum.inr (Sum.inr (Sum.inl (qd2 d), Sum.inl k))) - ιss (gen3 (fun i => g (Sum.inl (qd2 d), Sum.inl (Sum.inl i))) (fun j => g (Sum.inl (qd2 d), Sum.inr (Sum.inl j))) k) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen3, uvec, vvec, extL, extR, extCL, pt3, c, dmask,
          ers, prs, krs, qss, qrs, qrr, qd1, qd2, uS, uR, wS, wR,
          ιss, ιrs]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Hss _)
  have Hsr : ∀ f, ιsr f ∈ SpanC c := by
    apply map_mem_of_span ιsr (SpanC c) (g ∘ esr) ssr
    rintro (⟨(n | d) | (n | d), i⟩ | ⟨(n | d) | e, j⟩ | ⟨(n | d) | n, k⟩)
    · have : ιsr (gens (g ∘ esr) (Sum.inl (Sum.inl (Sum.inl n), i))) = gens c (Sum.inl (Sum.inl (qsr n), Sum.inl i)) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen1, vvec, wvec, extL, extCR, pt1, c, dmask,
          esr, psr, ksr, qss, qsr, qrr, qd1, qd2, uS, uR, wS, wR,
          ιsr]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιsr (gens (g ∘ esr) (Sum.inl (Sum.inl (Sum.inr d), i))) = gens c (Sum.inl (Sum.inl (qd2 d), Sum.inl i)) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen1, vvec, wvec, extL, extCR, pt1, c, dmask,
          esr, psr, ksr, qss, qsr, qrr, qd1, qd2, uS, uR, wS, wR,
          ιsr]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιsr (gens (g ∘ esr) (Sum.inl (Sum.inr (Sum.inl n), i))) = gens c (Sum.inl (Sum.inl (qrr n), Sum.inl i)) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen1, vvec, wvec, extL, extCR, pt1, c, dmask,
          esr, psr, ksr, qss, qsr, qrr, qd1, qd2, uS, uR, wS, wR,
          ιsr]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιsr (gens (g ∘ esr) (Sum.inl (Sum.inr (Sum.inr d), i))) = gens c (Sum.inl (Sum.inl (qd1 d), Sum.inl i)) - ιss (gen1 (fun j => g (Sum.inl (qd1 d), Sum.inr (Sum.inl j))) (fun k => g (Sum.inl (qd1 d), Sum.inr (Sum.inr (Sum.inl k)))) i) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen1, vvec, wvec, extL, extCL, extCR, pt1, c, dmask,
          esr, psr, ksr, qss, qsr, qrr, qd1, qd2, uS, uR, wS, wR,
          ιss, ιsr]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Hss _)
    · have : ιsr (gens (g ∘ esr) (Sum.inr (Sum.inl (Sum.inl (Sum.inl n), j)))) = gens c (Sum.inr (Sum.inl (Sum.inl (qsr n), j))) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen2, uvec, wvec, extL, extCR, pt2, c, dmask,
          esr, psr, ksr, qss, qsr, qrr, qd1, qd2, uS, uR, wS, wR,
          ιsr]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιsr (gens (g ∘ esr) (Sum.inr (Sum.inl (Sum.inl (Sum.inr d), j)))) = gens c (Sum.inr (Sum.inl (Sum.inl (qd2 d), j))) - ιrr (gen2 (fun i => g (Sum.inl (qd2 d), Sum.inl (Sum.inr i))) (fun k => g (Sum.inl (qd2 d), Sum.inr (Sum.inr (Sum.inr k)))) j) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen2, uvec, wvec, extL, extR, extCR, pt2, c, dmask,
          esr, psr, ksr, qss, qsr, qrr, qd1, qd2, uS, uR, wS, wR,
          ιsr, ιrr]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Hrr _)
    · exact e.elim
    · have : ιsr (gens (g ∘ esr) (Sum.inr (Sum.inr (Sum.inl (Sum.inl n), k)))) = gens c (Sum.inr (Sum.inr (Sum.inl (qsr n), Sum.inr k))) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen3, uvec, vvec, extL, extCR, pt3, c, dmask,
          esr, psr, ksr, qss, qsr, qrr, qd1, qd2, uS, uR, wS, wR,
          ιsr]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
    · have : ιsr (gens (g ∘ esr) (Sum.inr (Sum.inr (Sum.inl (Sum.inr d), k)))) = gens c (Sum.inr (Sum.inr (Sum.inl (qd2 d), Sum.inr k))) - ιrr (gen3 (fun i => g (Sum.inl (qd2 d), Sum.inl (Sum.inr i))) (fun j => g (Sum.inl (qd2 d), Sum.inr (Sum.inl j))) k) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen3, uvec, vvec, extL, extR, extCR, pt3, c, dmask,
          esr, psr, ksr, qss, qsr, qrr, qd1, qd2, uS, uR, wS, wR,
          ιsr, ιrr]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩) (Hrr _)
    · have : ιsr (gens (g ∘ esr) (Sum.inr (Sum.inr (Sum.inr n, k)))) = gens c (Sum.inr (Sum.inr (Sum.inl (qss n), Sum.inr k))) := by
        funext ⟨a, b, l⟩
        rcases a with a | a <;> rcases l with l | l <;> simp [gens, gen3, uvec, vvec, extL, extCR, pt3, c, dmask,
          esr, psr, ksr, qss, qsr, qrr, qd1, qd2, uS, uR, wS, wR,
          ιsr]
      rw [this]
      exact Submodule.subset_span ⟨_, rfl⟩
  rintro ⟨a | a, b, l | l⟩
  · have : (Pi.single (Sum.inl a, b, Sum.inl l) 1 : (αs ⊕ αr) × β × (γs ⊕ γr) → ℂ) =
        ιss (Pi.single (a, b, l) 1) := by
      funext ⟨a', b', l'⟩
      rcases a' with a' | a' <;> rcases l' with l' | l' <;>
        simp [ιss, extL, extCL, Pi.single_apply]
    rw [this]
    exact Hss _
  · have : (Pi.single (Sum.inl a, b, Sum.inr l) 1 : (αs ⊕ αr) × β × (γs ⊕ γr) → ℂ) =
        ιsr (Pi.single (a, b, l) 1) := by
      funext ⟨a', b', l'⟩
      rcases a' with a' | a' <;> rcases l' with l' | l' <;>
        simp [ιsr, extL, extCR, Pi.single_apply]
    rw [this]
    exact Hsr _
  · have : (Pi.single (Sum.inr a, b, Sum.inl l) 1 : (αs ⊕ αr) × β × (γs ⊕ γr) → ℂ) =
        ιrs (Pi.single (a, b, l) 1) := by
      funext ⟨a', b', l'⟩
      rcases a' with a' | a' <;> rcases l' with l' | l' <;>
        simp [ιrs, extR, extCL, Pi.single_apply]
    rw [this]
    exact Hrs _
  · have : (Pi.single (Sum.inr a, b, Sum.inr l) 1 : (αs ⊕ αr) × β × (γs ⊕ γr) → ℂ) =
        ιrr (Pi.single (a, b, l) 1) := by
      funext ⟨a', b', l'⟩
      rcases a' with a' | a' <;> rcases l' with l' | l' <;>
        simp [ιrr, extR, extCR, Pi.single_apply]
    rw [this]
    exact Hrr _

end diag

end OMA.Cube

namespace OMA.Cube

/-- Cutting the first side into two blocks. -/
theorem Fills.splitA {a1 a2 b c s1 s2 x y1 y2 z1 z2 : ℕ}
    (h1 : Fills a1 b c s1 (x + s2) y1 z1) (h2 : Fills a2 b c s2 (x + s1) y2 z2) :
    Fills (a1 + a2) b c (s1 + s2) x (y1 + y2) (z1 + z2) := by
  have g1 : GenT (Fin a1) (Fin b) (Fin c) (Fin s1) (Fin x ⊕ Fin s2) (Fin y1) (Fin z1) :=
    (FillsT.congr (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
      finSumFinEquiv.symm (Equiv.refl _) (Equiv.refl _) h1).gen
  have g2 : GenT (Fin a2) (Fin b) (Fin c) (Fin s2) (Fin x ⊕ Fin s1) (Fin y2) (Fin z2) :=
    (FillsT.congr (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _)
      finSumFinEquiv.symm (Equiv.refl _) (Equiv.refl _) h2).gen
  exact FillsT.congr finSumFinEquiv (Equiv.refl _) (Equiv.refl _) finSumFinEquiv (Equiv.refl _)
    finSumFinEquiv finSumFinEquiv (splitT g1 g2)

/-- Cutting the second side into two blocks. -/
theorem Fills.splitB {a b1 b2 c s1 s2 x1 x2 y z1 z2 : ℕ}
    (h1 : Fills a b1 c s1 x1 (y + s2) z1) (h2 : Fills a b2 c s2 x2 (y + s1) z2) :
    Fills a (b1 + b2) c (s1 + s2) (x1 + x2) y (z1 + z2) :=
  (Fills.splitA h1.swap12 h2.swap12).swap12

/-- Cutting the third side into two blocks. -/
theorem Fills.splitC {a b c1 c2 s1 s2 x1 x2 y1 y2 z : ℕ}
    (h1 : Fills a b c1 s1 x1 y1 (z + s2)) (h2 : Fills a b c2 s2 x2 y2 (z + s1)) :
    Fills a b (c1 + c2) (s1 + s2) (x1 + x2) (y1 + y2) z :=
  (Fills.splitA h1.swap13 h2.swap13).swap13

/-- Cutting the first and third sides at once, with `d1 + d2` points straddling two cells. -/
theorem Fills.diag {as ar b cs cr nss nsr nrs nrr d1 d2 : ℕ}
    (hss : Fills as b cs nss nrs 0 nsr) (hsr : Fills as b cr (nsr + d2) (nrr + d1) 0 nss)
    (hrs : Fills ar b cs (nrs + d1) nss 0 (nrr + d2))
    (hrr : Fills ar b cr nrr (nsr + d2) 0 (nrs + d1)) :
    Fills (as + ar) b (cs + cr) (nss + (nsr + (nrs + (nrr + (d1 + d2))))) 0 0 0 := by
  have e0 : Fin 0 ≃ Empty := finZeroEquiv
  have gss : GenT (Fin as) (Fin b) (Fin cs) (Fin nss) (Fin nrs) Empty (Fin nsr) :=
    (FillsT.congr (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) e0
      (Equiv.refl _) hss).gen
  have gsr : GenT (Fin as) (Fin b) (Fin cr) (Fin nsr ⊕ Fin d2) (Fin nrr ⊕ Fin d1) Empty
      (Fin nss) :=
    (FillsT.congr (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) finSumFinEquiv.symm
      finSumFinEquiv.symm e0 (Equiv.refl _) hsr).gen
  have grs : GenT (Fin ar) (Fin b) (Fin cs) (Fin nrs ⊕ Fin d1) (Fin nss) Empty
      (Fin nrr ⊕ Fin d2) :=
    (FillsT.congr (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) finSumFinEquiv.symm (Equiv.refl _)
      e0 finSumFinEquiv.symm hrs).gen
  have grr : GenT (Fin ar) (Fin b) (Fin cr) (Fin nrr) (Fin nsr ⊕ Fin d2) Empty
      (Fin nrs ⊕ Fin d1) :=
    (FillsT.congr (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) (Equiv.refl _) finSumFinEquiv.symm
      e0 finSumFinEquiv.symm hrr).gen
  have eP : DPt (Fin nss) (Fin nsr) (Fin nrs) (Fin nrr) (Fin d1) (Fin d2) ≃
      Fin (nss + (nsr + (nrs + (nrr + (d1 + d2))))) :=
    (Equiv.sumCongr (Equiv.refl _)
      ((Equiv.sumCongr (Equiv.refl _)
        ((Equiv.sumCongr (Equiv.refl _)
          ((Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv)).trans
            finSumFinEquiv)).trans finSumFinEquiv)).trans finSumFinEquiv
  exact FillsT.congr finSumFinEquiv (Equiv.refl _) finSumFinEquiv eP e0.symm e0.symm e0.symm
    (diagT gss gsr grs grr)

/-- Rewriting the parameters of a box. -/
theorem Fills.cast {a b c s x y z a' b' c' s' x' y' z' : ℕ} (h : Fills a b c s x y z)
    (ha : a = a') (hb : b = b') (hc : c = c') (hs : s = s') (hx : x = x') (hy : y = y')
    (hz : z = z') : Fills a' b' c' s' x' y' z' := by
  subst ha hb hc hs hx hy hz
  exact h

end OMA.Cube

namespace OMA.Cube

section pivots

/-- A triangular family of generators spans everything. -/
theorem eq_top_of_pivots {T K : Type} [Fintype T] [DecidableEq T] (N : Submodule ℂ (T → ℂ))
    (gv : K → T → ℂ) (hg : ∀ col, gv col ∈ N) (level : T → ℕ) (pivot : T → K)
    (diag : ∀ t, gv (pivot t) t = 1)
    (below : ∀ t u, u ≠ t → gv (pivot t) u ≠ 0 → level u < level t) : N = ⊤ := by
  apply eq_top_of_single
  intro t
  induction t using (measure level).wf.induction with
  | h t ih =>
    let c := gv (pivot t)
    have hc : c ∈ N := hg _
    have he := Finset.sum_erase_add Finset.univ
      (fun u => c u • (Pi.single u 1 : T → ℂ)) (Finset.mem_univ t)
    rw [← pi_eq_sum_univ', show c t = 1 from diag t, one_smul] at he
    rw [← he] at hc
    refine (N.add_mem_iff_right ?_).mp hc
    apply N.sum_mem
    intro u hu
    by_cases hz : c u = 0
    · simp [hz]
    · exact N.smul_mem _ (ih u (below t u (Finset.ne_of_mem_erase hu) hz))

variable {α β γ S E F G : Type} [DecidableEq α] [DecidableEq β] [DecidableEq γ]

/-- The support of a generator of a configuration of zero-one vectors. -/
def actB (m : Pt S E F G × Coord α β γ → Bool) : Col α β γ S E F G → α × β × γ → Bool
  | Sum.inl (p, i) => fun t =>
      decide (t.1 = i) && m (pt1 p, Sum.inr (Sum.inl t.2.1)) && m (pt1 p, Sum.inr (Sum.inr t.2.2))
  | Sum.inr (Sum.inl (p, j)) => fun t =>
      decide (t.2.1 = j) && m (pt2 p, Sum.inl t.1) && m (pt2 p, Sum.inr (Sum.inr t.2.2))
  | Sum.inr (Sum.inr (p, k)) => fun t =>
      decide (t.2.2 = k) && m (pt3 p, Sum.inl t.1) && m (pt3 p, Sum.inr (Sum.inl t.2.1))

theorem gens_bool (m : Pt S E F G × Coord α β γ → Bool) (col : Col α β γ S E F G)
    (t : α × β × γ) :
    gens (fun pc => if m pc then (1 : ℂ) else 0) col t = if actB m col t then 1 else 0 := by
  rcases col with ⟨p, i⟩ | ⟨p, j⟩ | ⟨p, k⟩
  · simp only [gens, gen1, vvec, wvec, actB]
    split_ifs <;> simp_all
  · simp only [gens, gen2, uvec, wvec, actB]
    split_ifs <;> simp_all
  · simp only [gens, gen3, uvec, vvec, actB]
    split_ifs <;> simp_all

theorem fills_of_pivots [Fintype α] [Fintype β] [Fintype γ]
    (m : Pt S E F G × Coord α β γ → Bool) (level : α × β × γ → ℕ)
    (pivot : α × β × γ → Col α β γ S E F G)
    (h : ∀ t, actB m (pivot t) t = true ∧
      ∀ u, u ≠ t → actB m (pivot t) u = true → level u < level t) :
    FillsT α β γ S E F G := by
  refine ⟨fun pc => if m pc then 1 else 0,
    eq_top_of_pivots _ (gens _) (fun col => Submodule.subset_span ⟨col, rfl⟩) level pivot ?_ ?_⟩
  · intro t
    rw [gens_bool, (h t).1]
    rfl
  · intro t u hut hne
    rw [gens_bool] at hne
    refine (h t).2 u hut ?_
    by_contra hb
    simp [hb] at hne

end pivots

section atomW

def wMask : Pt (Fin 0) (Fin 3) (Fin 0) (Fin 3) × Coord (Fin 2) (Fin 3) (Fin 2) → Bool := fun pc =>
  Sum.elim (fun p : Fin 0 => p.elim0)
    (Sum.elim
      (fun l : Fin 3 => Sum.elim (fun _ => false)
        (Sum.elim (fun j : Fin 3 => ([7, 2, 6].getD l.val 0).testBit j.val)
          (fun k : Fin 2 => ([1, 3, 2].getD l.val 0).testBit k.val)))
      (Sum.elim (fun p : Fin 0 => p.elim0)
        (fun l : Fin 3 => Sum.elim (fun i : Fin 2 => ([2, 1, 3].getD l.val 0).testBit i.val)
          (Sum.elim (fun j : Fin 3 => ([5, 4, 1].getD l.val 0).testBit j.val)
            (fun _ => false)))))
    pc.1 pc.2

def wCell (t : Fin 2 × Fin 3 × Fin 2) : ℕ := (t.1.val * 3 + t.2.1.val) * 2 + t.2.2.val

def wLevel (t : Fin 2 × Fin 3 × Fin 2) : ℕ := [4, 11, 2, 1, 3, 0, 5, 10, 7, 8, 6, 9].getD (wCell t) 0

def wPivot (t : Fin 2 × Fin 3 × Fin 2) :
    Col (Fin 2) (Fin 3) (Fin 2) (Fin 0) (Fin 3) (Fin 0) (Fin 3) :=
  let g := [0, 11, 2, 4, 8, 9, 10, 7, 1, 3, 6, 5].getD (wCell t) 0
  if g < 6 then Sum.inl (Sum.inr (Fin.ofNat 3 (g / 2)), Fin.ofNat 2 g)
  else Sum.inr (Sum.inr (Sum.inr (Fin.ofNat 3 ((g - 6) / 2)), Fin.ofNat 2 g))

/-- Three lines in each of two directions fill the box with sides two, three, two. -/
theorem fills_W : Fills 2 3 2 0 3 0 3 :=
  fills_of_pivots wMask wLevel wPivot (by decide)

end atomW

end OMA.Cube

namespace OMA.Cube

section unit

/-- Coordinate vectors covering a box of thickness one: rows, columns and single cells. -/
def unitConf (a b s x y z : ℕ) :
    Conf (Fin a) (Fin b) (Fin 1) (Fin s) (Fin x) (Fin y) (Fin z) := fun pc =>
  Sum.elim
    (fun p : Fin s => Sum.elim (fun i : Fin a => if i.val = p.val then (1 : ℂ) else 0)
        (Sum.elim (fun j : Fin b => if j.val = p.val then (1 : ℂ) else 0) (fun _ => 1)))
    (Sum.elim
      (fun q : Fin x => Sum.elim (fun _ => 0)
        (Sum.elim (fun j : Fin b => if j.val = s + q.val then (1 : ℂ) else 0) (fun _ => 1)))
      (Sum.elim
        (fun q : Fin y => Sum.elim (fun i : Fin a => if i.val = s + q.val then (1 : ℂ) else 0)
          (Sum.elim (fun _ => 0) (fun _ => 1)))
        (fun q : Fin z => Sum.elim
          (fun i : Fin a => if i.val = s + y + q.val / (b - s - x) then (1 : ℂ) else 0)
          (Sum.elim (fun j : Fin b => if j.val = s + x + q.val % (b - s - x) then (1 : ℂ) else 0)
            (fun _ => 1)))))
    pc.1 pc.2

/-- In a box of thickness one the tangent points and lines cover rows and columns of a matrix
and the remaining lines cover single cells. -/
theorem Fills.unitC {a b s x y z : ℕ} (h : (a - s - y) * (b - s - x) ≤ z) :
    Fills a b 1 s x y z := by
  refine ⟨unitConf a b s x y z, eq_top_of_single _ ?_⟩
  rintro ⟨i, j, k⟩
  by_cases h1 : i.val < s
  · have : (Pi.single (i, j, k) 1 : Fin a × Fin b × Fin 1 → ℂ) =
        gens (unitConf a b s x y z) (Sum.inr (Sum.inl (Sum.inl ⟨i.val, h1⟩, j))) := by
      funext ⟨i', j', k'⟩
      obtain rfl : k' = k := Subsingleton.elim _ _
      by_cases hi : i'.val = i.val <;> by_cases hj : j'.val = j.val <;>
        simp [gens, gen2, uvec, wvec, pt2, unitConf, Pi.single_apply, hi, hj, Fin.ext_iff]
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩
  by_cases h2 : i.val < s + y
  · have hq : i.val - s < y := by omega
    have : (Pi.single (i, j, k) 1 : Fin a × Fin b × Fin 1 → ℂ) =
        gens (unitConf a b s x y z) (Sum.inr (Sum.inl (Sum.inr ⟨i.val - s, hq⟩, j))) := by
      funext ⟨i', j', k'⟩
      obtain rfl : k' = k := Subsingleton.elim _ _
      have hs : s + (i.val - s) = i.val := by omega
      by_cases hi : i'.val = i.val <;> by_cases hj : j'.val = j.val <;>
        simp [gens, gen2, uvec, wvec, pt2, unitConf, Pi.single_apply, hi, hj, Fin.ext_iff, hs]
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩
  by_cases h3 : j.val < s
  · have : (Pi.single (i, j, k) 1 : Fin a × Fin b × Fin 1 → ℂ) =
        gens (unitConf a b s x y z) (Sum.inl (Sum.inl ⟨j.val, h3⟩, i)) := by
      funext ⟨i', j', k'⟩
      obtain rfl : k' = k := Subsingleton.elim _ _
      by_cases hi : i'.val = i.val <;> by_cases hj : j'.val = j.val <;>
        simp [gens, gen1, vvec, wvec, pt1, unitConf, Pi.single_apply, hi, hj, Fin.ext_iff]
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩
  by_cases h4 : j.val < s + x
  · have hq : j.val - s < x := by omega
    have : (Pi.single (i, j, k) 1 : Fin a × Fin b × Fin 1 → ℂ) =
        gens (unitConf a b s x y z) (Sum.inl (Sum.inr ⟨j.val - s, hq⟩, i)) := by
      funext ⟨i', j', k'⟩
      obtain rfl : k' = k := Subsingleton.elim _ _
      have hs : s + (j.val - s) = j.val := by omega
      by_cases hi : i'.val = i.val <;> by_cases hj : j'.val = j.val <;>
        simp [gens, gen1, vvec, wvec, pt1, unitConf, Pi.single_apply, hi, hj, Fin.ext_iff, hs]
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩
  · have hw : 0 < b - s - x := by have := j.isLt; omega
    have hjw : j.val - s - x < b - s - x := by have := j.isLt; omega
    have hia : i.val - s - y < a - s - y := by have := i.isLt; omega
    have hq : (j.val - s - x) + (i.val - s - y) * (b - s - x) < z := by
      have h5 : (i.val - s - y + 1) * (b - s - x) ≤ (a - s - y) * (b - s - x) :=
        Nat.mul_le_mul_right _ hia
      have h6 : (i.val - s - y + 1) * (b - s - x) =
          (i.val - s - y) * (b - s - x) + (b - s - x) := by ring
      omega
    have hdiv : ((j.val - s - x) + (i.val - s - y) * (b - s - x)) / (b - s - x) = i.val - s - y := by
      rw [Nat.add_mul_div_right _ _ hw, Nat.div_eq_of_lt hjw, Nat.zero_add]
    have hmod : ((j.val - s - x) + (i.val - s - y) * (b - s - x)) % (b - s - x) = j.val - s - x := by
      rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hjw]
    have : (Pi.single (i, j, k) 1 : Fin a × Fin b × Fin 1 → ℂ) =
        gens (unitConf a b s x y z) (Sum.inr (Sum.inr (Sum.inr
          ⟨(j.val - s - x) + (i.val - s - y) * (b - s - x), hq⟩, k))) := by
      funext ⟨i', j', k'⟩
      obtain rfl : k' = k := Subsingleton.elim _ _
      have hsi : s + y + (i.val - s - y) = i.val := by omega
      have hsj : s + x + (j.val - s - x) = j.val := by omega
      by_cases hi : i'.val = i.val <;> by_cases hj : j'.val = j.val <;>
        simp [gens, gen3, uvec, vvec, pt3, unitConf, Pi.single_apply, hi, hj, Fin.ext_iff, hdiv,
          hmod, hsi, hsj]
    rw [this]
    exact Submodule.subset_span ⟨_, rfl⟩

theorem Fills.unitB {a c s x y z : ℕ} (h : (a - s - z) * (c - s - x) ≤ y) :
    Fills a 1 c s x y z :=
  (Fills.unitC (a := a) (b := c) (s := s) (x := x) (y := z) (z := y) h).swap23

theorem Fills.unitA {b c s x y z : ℕ} (h : (c - s - y) * (b - s - z) ≤ x) :
    Fills 1 b c s x y z :=
  (Fills.unitC (a := c) (b := b) (s := s) (x := z) (y := y) (z := x) h).swap13

end unit

end OMA.Cube

namespace OMA.Cube

/-- Derivations of spanning statements: boxes of thickness one, one explicit small box, and
cuts along one of the three sides. -/
inductive Der : Type
  | U : Der
  | W : Der
  | P : ℕ → ℕ → ℕ → ℕ → ℕ → Der → Der → Der

def checkUnit (a b c s x y z : ℕ) : Bool :=
  (c == 1 && decide ((a - s - y) * (b - s - x) ≤ z)) ||
  (b == 1 && decide ((a - s - z) * (c - s - x) ≤ y)) ||
  (a == 1 && decide ((c - s - y) * (b - s - z) ≤ x))

def checkW (a b c x y z : ℕ) : Bool :=
  (a == 2 && b == 3 && c == 2 && decide (3 ≤ x) && decide (3 ≤ z)) ||
  (a == 3 && b == 2 && c == 2 && decide (3 ≤ y) && decide (3 ≤ z)) ||
  (a == 2 && b == 2 && c == 3 && decide (3 ≤ x) && decide (3 ≤ y))

/-- The bookkeeping of a derivation: a cut along a side sends the tangent points of each half
to the other half as lines in the direction of the cut. -/
def check : Der → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | Der.U, a, b, c, s, x, y, z => checkUnit a b c s x y z
  | Der.W, a, b, c, _, x, y, z => checkW a b c x y z
  | Der.P ax k s1 l1 l2 d1 d2, a, b, c, s, x, y, z =>
    if ax = 0 then
      decide (k ≤ a) && decide (s1 ≤ s) && decide (l1 ≤ y) && decide (l2 ≤ z) &&
        check d1 k b c s1 (x + (s - s1)) l1 l2 &&
        check d2 (a - k) b c (s - s1) (x + s1) (y - l1) (z - l2)
    else if ax = 1 then
      decide (k ≤ b) && decide (s1 ≤ s) && decide (l1 ≤ x) && decide (l2 ≤ z) &&
        check d1 a k c s1 l1 (y + (s - s1)) l2 &&
        check d2 a (b - k) c (s - s1) (x - l1) (y + s1) (z - l2)
    else
      decide (k ≤ c) && decide (s1 ≤ s) && decide (l1 ≤ x) && decide (l2 ≤ y) &&
        check d1 a b k s1 l1 l2 (z + (s - s1)) &&
        check d2 a b (c - k) (s - s1) (x - l1) (y - l2) (z + s1)

theorem check_sound : ∀ (d : Der) (a b c s x y z : ℕ),
    check d a b c s x y z = true → Fills a b c s x y z := by
  intro d
  induction d with
  | U =>
    intro a b c s x y z h
    simp only [check, checkUnit, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    rcases h with (⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨rfl, h⟩
    · exact Fills.unitC h
    · exact Fills.unitB h
    · exact Fills.unitA h
  | W =>
    intro a b c s x y z h
    simp only [check, checkW, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    rcases h with (⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hx⟩, hz⟩ | ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hy⟩, hz⟩) |
      ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hx⟩, hy⟩
    · exact fills_W.mono (Nat.zero_le _) hx (Nat.zero_le _) hz
    · exact fills_W.swap12.mono (Nat.zero_le _) (Nat.zero_le _) hy hz
    · exact fills_W.swap23.mono (Nat.zero_le _) hx hy (Nat.zero_le _)
  | P ax k s1 l1 l2 d1 d2 ih1 ih2 =>
    intro a b c s x y z h
    simp only [check] at h
    split_ifs at h with h0 h1
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨hk, hs⟩, hl1⟩, hl2⟩, hc1⟩, hc2⟩ := h
      exact (Fills.splitA (ih1 _ _ _ _ _ _ _ hc1) (ih2 _ _ _ _ _ _ _ hc2)).cast
        (by omega) rfl rfl (by omega) rfl (by omega) (by omega)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨hk, hs⟩, hl1⟩, hl2⟩, hc1⟩, hc2⟩ := h
      exact (Fills.splitB (ih1 _ _ _ _ _ _ _ hc1) (ih2 _ _ _ _ _ _ _ hc2)).cast
        rfl (by omega) rfl (by omega) (by omega) rfl (by omega)
    · simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨hk, hs⟩, hl1⟩, hl2⟩, hc1⟩, hc2⟩ := h
      exact (Fills.splitC (ih1 _ _ _ _ _ _ _ hc1) (ih2 _ _ _ _ _ _ _ hc2)).cast
        rfl rfl (by omega) (by omega) (by omega) (by omega) rfl

end OMA.Cube

namespace OMA.Cube

section peel

/-- An empty box is filled by anything. -/
theorem Fills.zeroA {b c s x y z : ℕ} : Fills 0 b c s x y z :=
  ⟨fun _ => 0, eq_top_of_single _ fun t => t.1.elim0⟩

/-- Stacking plates without tangent points along the second side. -/
theorem Fills.peelB {a bp b c s xp x y zp z : ℕ} (hp : Fills a bp c 0 xp (y + s) zp)
    (hb : Fills a b c s x y z) (k : ℕ) :
    Fills a (k * bp + b) c s (k * xp + x) y (k * zp + z) := by
  induction k with
  | zero => exact hb.cast rfl (by simp) rfl rfl (by simp) rfl (by simp)
  | succ k ih =>
    exact (Fills.splitB hp (ih.cast rfl rfl rfl rfl rfl (Nat.add_zero y).symm rfl)).cast
      rfl (by ring) rfl (by simp) (by ring) rfl (by ring)

/-- Stacking plates without tangent points along the first side. -/
theorem Fills.peelA {ap a b c s x yp y zp z : ℕ} (hp : Fills ap b c 0 (x + s) yp zp)
    (hb : Fills a b c s x y z) (k : ℕ) :
    Fills (k * ap + a) b c s x (k * yp + y) (k * zp + z) := by
  induction k with
  | zero => exact hb.cast (by simp) rfl rfl rfl rfl (by simp) (by simp)
  | succ k ih =>
    exact (Fills.splitA hp (ih.cast rfl rfl rfl rfl (Nat.add_zero x).symm rfl rfl)).cast
      (by ring) rfl rfl (by simp) rfl (by ring) (by ring)

/-- Stacking identical blocks along the first side; every block sees the tangent points of
the others as lines. -/
theorem Fills.repA {ap b c σ xb zp : ℕ} (hblock : Fills ap b c σ xb 0 zp) :
    ∀ k x : ℕ, x + k * σ = xb + σ → Fills (k * ap) b c (k * σ) x 0 (k * zp) := by
  intro k
  induction k with
  | zero =>
    intro x _
    exact Fills.zeroA.cast (by simp) rfl rfl rfl rfl rfl rfl
  | succ k ih =>
    intro x hx
    have h1 : Fills ap b c σ (x + k * σ) 0 zp :=
      hblock.cast rfl rfl rfl rfl (by rw [Nat.add_mul, Nat.one_mul] at hx; omega) rfl rfl
    have h2 := ih (x + σ) (by rw [Nat.add_mul, Nat.one_mul] at hx; omega)
    exact (Fills.splitA h1 h2).cast (by ring) rfl rfl (by ring) rfl rfl (by ring)

/-- Stacking identical blocks along the third side. -/
theorem Fills.repC {a b cp σ xp zb : ℕ} (hblock : Fills a b cp σ xp 0 zb) (k z : ℕ)
    (hz : z + k * σ = zb + σ) : Fills a b (k * cp) (k * σ) (k * xp) 0 z :=
  (Fills.repA hblock.swap13 k z hz).swap13

end peel

section families

/-- Bars of cross section nine by nine carrying twenty-seven tangent points. -/
theorem bar_all (hB9 : Fills 9 9 9 27 2 0 4) (hB10 : Fills 9 10 9 27 5 0 7)
    (hB11 : Fills 9 11 9 27 8 0 10) (hZP : Fills 9 3 9 0 9 27 9) (m : ℕ) :
    Fills 9 (m + 9) 9 27 (3 * m + 2) 0 (3 * m + 4) := by
  have hp : Fills 9 3 9 0 9 (0 + 27) 9 := hZP
  obtain ⟨k, r, hr, rfl⟩ : ∃ k r, r < 3 ∧ m = 3 * k + r :=
    ⟨m / 3, m % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod m 3).symm⟩
  interval_cases r
  · exact (Fills.peelB hp hB9 k).cast rfl (by omega) rfl rfl (by omega) rfl (by omega)
  · exact (Fills.peelB hp hB10 k).cast rfl (by omega) rfl rfl (by omega) rfl (by omega)
  · exact (Fills.peelB hp hB11 k).cast rfl (by omega) rfl rfl (by omega) rfl (by omega)

/-- The cube of side `9 * (k + 1) + rem`: both the first and the third side are cut into a
block of size `rem` and a block of size `9 * (k + 1)`, with `k + 1` straddling points of
each kind. The four cells are then cut into slabs, bars and finitely many kinds of cells. -/
theorem cube_uniform (hbar : ∀ m, Fills 9 (m + 9) 9 27 (3 * m + 2) 0 (3 * m + 4))
    (hZ29 : Fills 9 9 9 0 27 29 25) (rem sr t : ℕ) (ht : t + 1 = 3 * rem)
    (hSpHead : Fills 9 (rem + 9) 9 29 (3 * rem) 0 (3 * rem))
    (hSRBase : Fills rem (rem + 9) 9 (3 * rem) 30 0 sr)
    (hSRPlate : Fills rem 9 9 0 27 (3 * rem) (3 * rem))
    (hZCss : Fills rem 9 rem 0 t sr t)
    (hQSS : Fills rem (rem + 9) rem sr t 0 t) (k : ℕ) :
    Fills (9 * k + 9 + rem) (9 * k + 9 + rem) (9 * k + 9 + rem)
      (27 * (k + 1) * (k + 1) + 6 * (k + 1) * rem + 2 * (k + 1) + sr) 0 0 0 := by
  have hSp : Fills 9 (9 * k + 9 + rem) 9 29 (3 * rem + k * 27) 0 (k * 25 + 3 * rem) :=
    (Fills.peelB (hZ29.cast rfl rfl rfl rfl rfl (Nat.zero_add 29).symm rfl) hSpHead k).cast
      rfl (by omega) rfl rfl (by ring) rfl rfl
  have hBar : Fills 9 (9 * k + 9 + rem) 9 27 (27 * k + 3 * rem + 2) 0 (27 * k + 3 * rem + 4) :=
    (hbar (9 * k + rem)).cast rfl (by omega) rfl rfl (by ring) rfl (by ring)
  have hReg : Fills (k * 9) (9 * k + 9 + rem) 9 (k * 27) (3 * rem + 29) 0
      (k * (27 * k + 3 * rem + 4)) :=
    Fills.repA hBar k (3 * rem + 29) (by ring)
  have hSlab : Fills (9 * (k + 1)) (9 * k + 9 + rem) 9 (27 * (k + 1) + 2) (3 * rem) 0
      (27 * k * k + 29 * k + 3 * k * rem + 3 * rem) :=
    (Fills.splitA hSp hReg).cast (by ring) rfl rfl (by ring) rfl rfl (by ring)
  have hrr : Fills (9 * (k + 1)) (9 * k + 9 + rem) (9 * (k + 1)) ((k + 1) * (27 * (k + 1) + 2))
      (3 * (k + 1) * rem) 0 (3 * (k + 1) * rem) :=
    (Fills.repC hSlab (k + 1) (3 * (k + 1) * rem) (by ring)).cast
      rfl rfl (by ring) rfl (by ring) rfl rfl
  have hSR : Fills rem (9 * k + 9 + rem) 9 (3 * rem) (27 * k + 30) 0 (k * (3 * rem) + sr) :=
    (Fills.peelB (hSRPlate.cast rfl rfl rfl rfl rfl (Nat.zero_add _).symm rfl) hSRBase k).cast
      rfl (by omega) rfl rfl (by ring) rfl rfl
  have hsr : Fills rem (9 * k + 9 + rem) (9 * (k + 1)) (3 * (k + 1) * rem)
      ((k + 1) * (27 * k + 30)) 0 sr :=
    (Fills.repC hSR (k + 1) sr (by ring)).cast rfl rfl (by ring) (by ring) rfl rfl rfl
  have hss : Fills rem (9 * k + 9 + rem) rem sr ((k + 1) * t) 0 ((k + 1) * t) :=
    (Fills.peelB (hZCss.cast rfl rfl rfl rfl rfl (Nat.zero_add sr).symm rfl) hQSS k).cast
      rfl (by omega) rfl rfl (by ring) rfl (by ring)
  have h2 : (k + 1) * t + (k + 1) = 3 * (k + 1) * rem := by
    rw [show 3 * (k + 1) * rem = (k + 1) * (3 * rem) by ring, ← ht]
    ring
  have h3 : (k + 1) * (27 * (k + 1) + 2) + (k + 1) = (k + 1) * (27 * k + 30) := by ring
  have key := Fills.diag (as := rem) (ar := 9 * (k + 1)) (b := 9 * k + 9 + rem) (cs := rem)
    (cr := 9 * (k + 1)) (nss := sr) (nsr := (k + 1) * t) (nrs := (k + 1) * t)
    (nrr := (k + 1) * (27 * (k + 1) + 2)) (d1 := k + 1) (d2 := k + 1) hss
    (hsr.cast rfl rfl rfl h2.symm h3.symm rfl rfl)
    (hsr.swap13.cast rfl rfl rfl h2.symm rfl rfl h3.symm)
    (hrr.cast rfl rfl rfl rfl h2.symm rfl h2.symm)
  refine key.cast (by omega) rfl (by omega) ?_ rfl rfl rfl
  have h4 : (k + 1) * (27 * (k + 1) + 2) = 27 * (k + 1) * (k + 1) + 2 * (k + 1) := by ring
  have h5 : 6 * (k + 1) * rem = 2 * (3 * (k + 1) * rem) := by ring
  omega

/-- Cubes of side congruent to one modulo nine: slabs of thickness nine and one slab of
thickness ten, each cut by peeling off two bars at a time. -/
theorem cube_one (hbar : ∀ m, Fills 9 (m + 9) 9 27 (3 * m + 2) 0 (3 * m + 4))
    (hS9 : Fills 10 10 9 32 0 0 4) (hZB : Fills 10 9 9 0 27 32 28)
    (hP9 : Fills 9 9 9 0 27 27 27) (hA10 : Fills 9 10 10 30 6 0 4)
    (hZ10 : Fills 10 9 10 0 30 36 28) (hP10 : Fills 9 9 10 0 30 30 27)
    (hC10 : Fills 10 10 10 36 0 0 0) (j : ℕ) :
    Fills (9 * j + 19) (9 * j + 19) (9 * j + 19)
      (27 * (j + 1) * (j + 1) + 62 * (j + 1) + 36) 0 0 0 := by
  have zeroBar : ∀ i, Fills (9 * i + 10) 9 9 0 27 (27 * i + 32) (27 * i + 28) := fun i =>
    (Fills.peelA (hP9.cast rfl rfl rfl rfl (Nat.add_zero 27).symm rfl rfl) hZB i).cast
      (by omega) rfl rfl rfl rfl (by omega) (by omega)
  have slab9 : ∀ i, Fills (9 * i + 10) (9 * i + 10) 9 (27 * i + 32) 0 0
      (27 * i * i + 35 * i + 4) := by
    intro i
    induction i with
    | zero => exact hS9
    | succ i ih =>
      have hB : Fills 9 (9 * i + 19) 9 27 (0 + (27 * i + 32)) 0 (27 * i + 34) :=
        (hbar (9 * i + 10)).cast rfl rfl rfl rfl (by omega) rfl (by omega)
      have hR : Fills (9 * i + 10) (9 * i + 19) 9 (27 * i + 32) (0 + 27) 0
          (27 * i + 28 + (27 * i * i + 35 * i + 4)) :=
        (Fills.splitB ((zeroBar i).cast rfl rfl rfl rfl rfl (Nat.zero_add _).symm rfl)
          (ih.cast rfl rfl rfl rfl rfl (Nat.zero_add 0).symm rfl)).cast
          rfl (by omega) rfl (by omega) (by omega) rfl rfl
      exact (Fills.splitA hB hR).cast (by omega) (by omega) rfl (by omega) rfl rfl (by ring)
  have aBar : ∀ i, Fills 9 (9 * i + 10) 10 30 (30 * i + 6) 0 (27 * i + 4) := fun i =>
    (Fills.peelB (hP10.cast rfl rfl rfl rfl rfl (Nat.zero_add 30).symm rfl) hA10 i).cast
      rfl (by omega) rfl rfl (by omega) rfl (by omega)
  have zBar : ∀ i, Fills (9 * i + 10) 9 10 0 30 (30 * i + 36) (27 * i + 28) := fun i =>
    (Fills.peelA (hP10.cast rfl rfl rfl rfl (Nat.add_zero 30).symm rfl rfl) hZ10 i).cast
      (by omega) rfl rfl rfl rfl (by omega) (by omega)
  have slab10 : ∀ i, Fills (9 * i + 10) (9 * i + 10) 10 (30 * i + 36) 0 0
      (27 * i * i + 32 * i) := by
    intro i
    induction i with
    | zero => exact hC10
    | succ i ih =>
      have hA : Fills 9 (9 * i + 19) 10 30 (0 + (30 * i + 36)) 0 (27 * i + 31) :=
        (aBar (i + 1)).cast rfl (by omega) rfl rfl (by omega) rfl (by omega)
      have hR : Fills (9 * i + 10) (9 * i + 19) 10 (30 * i + 36) (0 + 30) 0
          (27 * i + 28 + (27 * i * i + 32 * i)) :=
        (Fills.splitB ((zBar i).cast rfl rfl rfl rfl rfl (Nat.zero_add _).symm rfl)
          (ih.cast rfl rfl rfl rfl rfl (Nat.zero_add 0).symm rfl)).cast
          rfl (by omega) rfl (by omega) (by omega) rfl rfl
      exact (Fills.splitA hA hR).cast (by omega) (by omega) rfl (by omega) rfl rfl (by ring)
  have hstack : Fills (9 * j + 19) (9 * j + 19) ((j + 1) * 9) ((j + 1) * (27 * (j + 1) + 32))
      ((j + 1) * 0) 0 (0 + (30 * (j + 1) + 36)) :=
    Fills.repC ((slab9 (j + 1)).cast (by omega) (by omega) rfl rfl rfl rfl rfl) (j + 1) _
      (by ring)
  have hbase : Fills (9 * j + 19) (9 * j + 19) 10 (30 * (j + 1) + 36) 0 0
      (0 + (j + 1) * (27 * (j + 1) + 32)) :=
    (slab10 (j + 1)).cast (by omega) (by omega) rfl rfl rfl rfl (by ring)
  exact (Fills.splitC hstack hbase).cast rfl rfl (by omega) (by ring) (by simp) rfl rfl

end families

end OMA.Cube

namespace OMA.Cube

section cells

open Der

def dBar9 : Der :=
  P 0 4 13 0 0 (P 2 3 3 9 0 (P 1 3 1 1 6 (P 2 2 0 1 2 (P 1 2 0 1 4 (P 0 2 0 1 2 (P 2 1 0 0 1 U U)
  (P 2 1 0 0 1 U U)) U) U) (P 1 3 0 6 1 (P 0 3 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) (P 0 2 1
  1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) (P 2 2 0 3 0 W U)))) (P 1 3 3 3 1 (P 2 3 1
  1 5 (P 1 2 1 1 1 (P 0 3 1 3 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) U) (P 0 2 1 1
  1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U)
  U) U))) (P 1 3 3 3 1 (P 2 3 1 1 5 (P 1 2 1 1 1 (P 0 3 1 3 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0
  1 U U) U) U) U) U) (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) (P 2 2 1 1 1
  (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U))) (P 2 2 1 0 3 (P 0 2 0 2 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U)
  U) (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U)) (P 2 2 1 0 3 (P 0 2 0 2 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U)
  U) (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U)) (P 0 3 1 0 3 (P 0 2 0 0 3 W U) U)))))) (P 2 3 3 9 0 (P 1 3
  1 3 5 (P 0 3 0 2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 2 2 0 3
  0 W U)) (P 1 3 1 3 5 (P 0 3 0 2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U)
  U) (P 2 2 0 3 0 W U)) (P 0 3 0 2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U)
  U) U) (P 2 2 0 3 0 W U)))) (P 1 3 4 3 1 (P 2 3 1 3 3 (P 0 3 0 2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1
  2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U)) (P 0 3 3 2
  0 (P 1 2 2 0 0 (P 0 2 2 1 0 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 2 0 1 2 (P 2 2 0 1 1 (P
  2 1 0 1 0 U U) U) U))) (P 2 3 3 0 4 (P 0 3 3 1 6 (P 1 2 1 0 2 (P 2 2 0 0 3 W U) (P 1 2 1 0 2 (P
  2 2 0 0 3 W U) (P 2 2 0 0 3 W U))) (P 1 3 0 3 1 (P 1 2 0 3 0 W U) (P 1 2 0 0 2 (P 2 2 0 0 2 (P 2
  1 0 0 1 U U) U) U))) (P 1 3 1 3 4 (P 0 3 0 2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0
  1 U U) U) U) U) (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U)) (P 0 3 3 0 2 (P 2 2 2 0 0 (P
  0 2 2 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U) (P 2 2 0 3 0 W U))))))

theorem cBar9 : Fills 9 9 9 27 2 0 4 :=
  check_sound dBar9 _ _ _ _ _ _ _ (by decide +kernel)

def dBar10 : Der :=
  P 1 3 9 1 1 (P 2 3 3 0 7 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 3 0 4 2 (P 0 2 0 2
  2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P
  1 1 0 0 1 U U) U) U) U))) (P 0 3 3 4 0 (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0
  1 0 0 1 U U) U) U) U) (P 0 2 2 0 0 (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U)) (P 0 3
  0 5 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1
  1 0 0 1 U U) U) U) U)) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) (P 2 2 1 1
  1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) (P 0 2 0 0 3 W U)))))) (P 2 2 3 4 0 (P 0 3 1
  0 7 (P 1 3 0 3 3 (P 0 2 0 0 3 W U) (P 1 2 0 2 2 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) (P 0 2 1 0 1
  (P 0 1 0 0 1 U U) U))) (P 1 3 1 2 6 (P 0 3 0 1 3 (P 0 2 0 0 3 W U) (P 0 2 0 0 3 W U)) (P 0 3 0 1
  4 (P 1 2 0 2 2 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U)) (P 1 2 0 2 2
  (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U))))) (P 0 3 5 3 3 (P 2 3 2 3
  2 (P 1 3 0 2 3 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 1 2 1 1 1 (P
  2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) (P 2 2 0 0 3 W U))) (P 1 3 2 2 2 (P 2 2 1 1 1 (P
  1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U) (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U)
  U)) (P 1 3 1 5 1 (P 0 2 1 1 1 (P 2 3 1 3 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U)
  U) U))) (P 2 3 4 1 4 (P 1 3 3 0 3 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 2 0 0 (P
  0 2 2 1 0 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U)) (P 0 3 0 3 6 (P 1 3 0 2 4 (P 1 2 0 2 2 (P 2 2
  0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U) U) (P 1 3 0 1 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U)
  U))) (P 1 3 2 2 5 (P 0 3 1 5 1 (P 1 2 1 1 1 (P 2 3 1 1 3 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0
  U U) U) U) U) U) (P 2 3 0 3 1 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) U)) (P 0 3 1 3 3 (P 2 3 1 5 1 (P
  0 2 1 1 1 (P 1 3 1 3 1 (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U) U) U) (P 2 2 1 3 0
  (P 1 2 0 2 2 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U)) (P 1 3 1 0 3
  (P 1 2 0 0 3 W U) U)))))))

theorem cBar10 : Fills 9 10 9 27 5 0 7 :=
  check_sound dBar10 _ _ _ _ _ _ _ (by decide +kernel)

def dBar11 : Der :=
  P 1 3 9 1 1 (P 2 3 3 0 7 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 3 0 4 2 (P 0 2 0 2
  2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P
  1 1 0 0 1 U U) U) U) U))) (P 0 3 3 4 0 (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0
  1 0 0 1 U U) U) U) U) (P 0 2 2 0 0 (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U)) (P 0 3
  0 5 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1
  1 0 0 1 U U) U) U) U)) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) (P 2 2 1 1
  1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) (P 0 2 0 0 3 W U)))))) (P 2 3 5 4 3 (P 0 3 2
  0 9 (P 1 3 0 3 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) (P 1 3 0 3 4
  (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) (P 2 2 1 1 0 (P 0 2 1 0 1 (P 0
  1 0 0 1 U U) U) U))) (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P
  2 2 0 3 0 W U) U)) (P 0 3 1 3 2 (P 1 3 0 3 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0
  U U) U) U) U) (P 0 2 0 3 0 W U)) (P 1 3 0 3 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1
  0 U U) U) U) U) (P 2 2 1 1 0 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U))))) (P 0 3 4 3 4 (P 1 3 0 5 3
  (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0
  1 U U) U) U) U)) (P 2 3 1 3 3 (P 1 3 0 2 3 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U
  U) U) U) U) (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U)) (P 1 3 3 2 0 (P 0 2 2 0 0 (P 1 2
  2 1 0 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U) (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U)
  U)))) (P 1 3 3 3 4 (P 2 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 2
  2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U)) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0
  1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U)
  U))) (P 2 3 3 2 3 (P 0 3 1 0 8 (P 1 3 0 2 6 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) (P 2 2 1 1 0 (P 0
  2 1 0 1 (P 0 1 0 0 1 U U) U) U)) (P 1 3 0 3 1 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 2 1 0 (P
  2 2 1 0 1 (P 2 1 0 0 1 U U) U) U))) (P 0 3 1 0 8 (P 1 3 0 2 6 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U)
  (P 2 2 1 1 0 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U)) (P 1 3 0 3 1 (P 0 2 0 3 1 (P 1 2 0 3 0 W U)
  U) (P 0 2 2 1 0 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U)))))))

theorem cBar11 : Fills 9 11 9 27 8 0 10 :=
  check_sound dBar11 _ _ _ _ _ _ _ (by decide +kernel)

def dZP99 : Der :=
  P 0 3 0 9 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0
  3 W U) U) (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U))) (P 2 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3
  0 W U) U) (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U)) (P 2 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0
  W U) U) (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U)) (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2
  0 3 1 (P 1 2 0 3 0 W U) U))))

theorem cZP99 : Fills 9 3 9 0 9 27 9 :=
  check_sound dZP99 _ _ _ _ _ _ _ (by decide +kernel)

def dZ29 : Der :=
  P 0 3 0 10 8 (P 1 3 0 8 3 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 3 0 3 3 (P 2 2 0 3
  1 (P 0 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U))) (P 2
  3 0 7 3 (P 1 3 0 3 3 (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U) (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P
  2 1 0 0 1 U U) U) U) U)) (P 1 3 0 7 2 (P 2 3 0 4 3 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1
  0 0 1 U U) U) U) U) (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U)) (P 2 3 0
  3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U)
  U) U) U))))) (P 1 3 0 10 5 (P 2 3 0 3 7 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0
  2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U)) (P 0 3 0 7 2 (P 2 3 0 3 4 (P 0 2 0 2 2
  (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2
  1 0 0 1 U U) U) U) U)) (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 0 2 0 2 1
  (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U)))) (P 2 3 0 6 6 (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3
  (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W
  U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U))) (P 2 3 0 6 6 (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P
  2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U)
  U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U))) (P 1 3 0 2 7 (P 0 3 0 3 4 (P 1 2 0 2 2 (P 2 2 0 2 1 (P 0
  2 0 1 1 (P 0 1 0 1 0 U U) U) U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U)
  U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P
  2 1 0 1 0 U U) U) U) U))))))

theorem cZ29 : Fills 9 9 9 0 27 29 25 :=
  check_sound dZ29 _ _ _ _ _ _ _ (by decide +kernel)

def dSpHead2 : Der :=
  P 1 3 3 6 6 (P 0 3 0 9 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 3 0 3 3 (P 2 2 0 1
  3 (P 1 2 0 0 3 W U) U) (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U))) (P 2 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 3
  1 (P 1 2 0 3 0 W U) U) (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U)) (P 2 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 3 1
  (P 1 2 0 3 0 W U) U) (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W
  U) U) (P 1 2 2 0 0 (P 0 2 2 1 0 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U))))) (P 1 4 13 0 0 (P 0 3
  3 9 0 (P 2 3 1 6 1 (P 0 2 0 1 2 (P 2 2 0 4 1 (P 1 2 0 2 1 (P 0 1 0 0 1 U U) (P 0 1 0 0 1 U U))
  U) U) (P 2 3 0 1 6 (P 1 3 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) (P 1 2 1 1 1 (P 0 2 1 1 1
  (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 0 3 0 W U)))) (P 2 3 3 1 3 (P 0 3 1 1 5 (P 2 2 1 1 1
  (P 1 3 1 1 3 (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U) U) U) (P 1 2 1 1 1 (P 0 2 1 1 1
  (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U))) (P 2 3
  3 1 3 (P 0 3 1 1 5 (P 2 2 1 1 1 (P 1 3 1 1 3 (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U)
  U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 1 1 1 (P 2 2 1 0 1
  (P 2 1 0 0 1 U U) U) U))) (P 0 2 1 0 3 (P 1 2 0 2 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) (P 2 2 1 1
  0 (P 2 1 0 1 0 U U) U)) (P 0 2 1 0 3 (P 1 2 0 2 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) (P 2 2 1 1 0
  (P 2 1 0 1 0 U U) U)) (P 1 3 1 3 0 (P 1 2 0 3 0 W U) U)))))) (P 0 3 3 9 0 (P 2 3 1 6 1 (P 0 2 0
  1 2 (P 2 2 0 4 1 (P 1 2 0 2 1 (P 0 1 0 0 1 U U) (P 0 1 0 0 1 U U)) U) U) (P 2 3 0 1 6 (P 1 3 0 1
  2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U)
  U) U) (P 0 2 0 3 0 W U)))) (P 2 3 3 1 3 (P 0 3 1 1 5 (P 2 2 1 1 1 (P 1 3 1 1 3 (P 1 2 1 1 1 (P 0
  2 1 0 1 (P 0 1 0 0 1 U U) U) U) U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U)
  U) U) (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U))) (P 2 3 3 1 3 (P 0 3 1 1 5 (P 2 2 1 1 1
  (P 1 3 1 1 3 (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U) U) U) (P 1 2 1 1 1 (P 0 2 1 1 1
  (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U))) (P 0 2
  1 0 3 (P 1 2 0 2 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U)) (P 0 2 1
  0 3 (P 1 2 0 2 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U)) (P 1 3 1 3
  0 (P 1 2 0 3 0 W U) U)))))))

theorem cSpHead2 : Fills 9 11 9 29 6 0 6 :=
  check_sound dSpHead2 _ _ _ _ _ _ _ (by decide +kernel)

def dSRBase2 : Der :=
  P 1 3 2 9 0 (P 2 3 1 3 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) (P 2 3 0 3 2 (P 2 2 0
  1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U))) (P
  2 3 1 7 1 (P 1 3 0 3 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) (P 1 3 1 3 1 (P 1 2 1 1
  1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U))) (P 1 3 1 6 1 (P 2 3 0
  3 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U
  U) U) U)) (P 2 3 1 4 1 (P 1 3 1 3 1 (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) (P 2 2 0 1
  1 (P 2 1 0 1 0 U U) U)) (P 1 3 1 3 1 (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) (P 2 2 0
  1 1 (P 2 1 0 1 0 U U) U)))))

theorem cSRBase2 : Fills 2 11 9 6 30 0 2 :=
  check_sound dSRBase2 _ _ _ _ _ _ _ (by decide +kernel)

def dSRPlate2 : Der :=
  P 1 3 0 9 2 (P 2 3 0 3 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) (P 2 3 0 3 2 (P 2 2 0
  1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U))) (P
  2 3 0 6 2 (P 1 3 0 3 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) (P 1 2 0 1 2 (P 2 2 0 1
  1 (P 2 1 0 1 0 U U) U) U)) (P 2 3 0 6 2 (P 1 3 0 3 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U)
  U) U) (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U)) (P 1 3 0 3 2 (P 1 2 0 1 2 (P 2 2 0 1 1
  (P 2 1 0 1 0 U U) U) U) (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U))))

theorem cSRPlate2 : Fills 2 9 9 0 27 6 6 :=
  check_sound dSRPlate2 _ _ _ _ _ _ _ (by decide +kernel)

def dZCss2 : Der :=
  P 1 3 0 2 2 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) (P 1 3 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) (P
  1 2 0 1 1 (P 1 1 0 0 1 U U) U))

theorem cZCss2 : Fills 2 9 2 0 5 2 5 :=
  check_sound dZCss2 _ _ _ _ _ _ _ (by decide +kernel)

def dQSS2 : Der :=
  P 1 3 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) (P 1 3 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) (P
  1 3 1 2 1 (P 1 2 1 1 1 (P 1 1 0 0 1 U U) U) (P 1 1 0 0 1 U U)))

theorem cQSS2 : Fills 2 11 2 2 5 0 5 :=
  check_sound dQSS2 _ _ _ _ _ _ _ (by decide +kernel)

def dSpHead3 : Der :=
  P 1 3 7 3 2 (P 0 3 3 7 0 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 3 0 2 4 (P 2 2 0 2
  2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 0 2 2 0 0 (P 2 2 2 1 0 (P 1 2 1 1 0 (P
  1 1 0 1 0 U U) U) U) U))) (P 2 3 1 2 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 1 1
  1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U)) (P 0 3 0 5 3 (P 2 3 0 3 3 (P 2 2 0 1 3
  (P 1 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U)) (P 2 3 0
  2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 0 2 2 0 0 (P 2 2 2 1 0
  (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U))))) (P 1 3 7 2 3 (P 2 3 3 0 7 (P 0 3 0 3 3 (P 0 2 0 3 1
  (P 1 2 0 3 0 W U) U) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U)
  U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))) (P 0 3 1 6 2 (P 2 3 0 3 3
  (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U)
  U)) (P 2 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2
  0 1 1 (P 1 1 0 1 0 U U) U) U) U)) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1
  0 U U) U) U) U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))))) (P 2 3 6 1
  3 (P 0 3 3 0 4 (P 1 3 0 2 4 (P 1 2 0 2 2 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U) (P
  0 2 2 0 0 (P 1 2 2 1 0 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U)) (P 0 3 0 3 5 (P 1 3 0 3 3 (P 1 2
  0 1 3 (P 2 2 0 0 3 W U) U) (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U)) (P
  1 3 0 2 4 (P 1 2 0 2 2 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U) (P 0 2 2 0 0 (P 1 2
  2 1 0 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U)))) (P 0 3 3 4 3 (P 1 3 0 5 3 (P 2 3 0 3 3 (P 2 2 0
  3 1 (P 0 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U)) (P 2
  3 0 4 2 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 1 2 2 0 0 (P 2 2 2
  0 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U))) (P 1 2 1 3 3 (P 2 3 0 2 6 (P 0 3 0 3 2 (P 0 2 0 1
  2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U)) (P 0 3
  0 3 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U
  U) U) U))) (P 2 2 2 1 2 (P 0 2 1 0 3 (P 1 2 0 1 2 (P 2 1 0 1 0 U U) (P 2 1 0 1 0 U U)) (P 0 2 0
  1 3 (P 1 2 0 1 2 (P 2 1 0 1 0 U U) (P 0 1 0 0 1 U U)) (P 1 3 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U
  U) U) U))) (P 0 2 1 2 2 (P 2 2 0 3 1 (P 1 2 0 2 1 (P 0 1 0 0 1 U U) (P 2 1 0 1 0 U U)) (P 1 3 1
  1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U)) (P 2 2 0 3 2 (P 0 2 0 1 3 (P 1 2 0 1 2 (P 2 1 0 1 0 U
  U) (P 0 1 0 0 1 U U)) (P 1 2 0 1 2 (P 2 1 0 1 0 U U) (P 0 1 0 0 1 U U))) (P 1 3 1 0 4 (P 0 2 0 2
  2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U)) U))))))))

theorem cSpHead3 : Fills 9 12 9 29 9 0 9 :=
  check_sound dSpHead3 _ _ _ _ _ _ _ (by decide +kernel)

def dSRBase3 : Der :=
  P 1 3 3 8 0 (P 2 3 0 4 2 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 2
  3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 0 2 2 0 0 (P 2 2 2
  1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U))) (P 2 3 3 7 0 (P 1 3 0 3 3 (P 1 2 0 3 1 (P 0 2 0 3
  0 W U) U) (P 1 3 0 4 2 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 2 2
  2 0 0 (P 1 2 2 0 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U) U))) (P 1 3 0 6 3 (P 2 3 0 3 3 (P 2 2 0
  3 1 (P 0 2 0 0 3 W U) U) (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U)) (P 2 3 0 5 3 (P 1 3 0 3 3 (P 1 2 0 3
  1 (P 0 2 0 3 0 W U) U) (P 1 2 0 2 2 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U)) (P 1 3
  0 4 2 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 2 2 2 0 0 (P 1 2 2 0
  1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U) U)))))

theorem cSRBase3 : Fills 3 12 9 9 30 0 4 :=
  check_sound dSRBase3 _ _ _ _ _ _ _ (by decide +kernel)

def dSRPlate3 : Der :=
  P 1 3 0 9 3 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0
  3 W U) U) (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U))) (P 2 3 0 6 3 (P 1 3 0 3 3 (P 1 2 0 3 1 (P 0 2 0 3
  0 W U) U) (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U)) (P 2 3 0 6 3 (P 1 3 0 3 3 (P 1 2 0 3 1 (P 0 2 0 3 0
  W U) U) (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U)) (P 1 3 0 3 3 (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U) (P 1 2
  0 3 1 (P 0 2 0 3 0 W U) U))))

theorem cSRPlate3 : Fills 3 9 9 0 27 9 9 :=
  check_sound dSRPlate3 _ _ _ _ _ _ _ (by decide +kernel)

def dZCss3 : Der :=
  P 1 3 0 3 3 (P 1 2 0 2 2 (P 0 2 0 3 1 (P 2 2 0 1 2 (P 1 1 0 1 0 U U) U) U) U) (P 1 3 0 2 3 (P 2
  2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0
  1 1 (P 2 1 0 1 0 U U) U) U) U))

theorem cZCss3 : Fills 3 9 3 0 8 4 8 :=
  check_sound dZCss3 _ _ _ _ _ _ _ (by decide +kernel)

def dQSS3 : Der :=
  P 1 3 1 2 2 (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 3 1 2 2 (P 1
  2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 3 1 2 2 (P 1 2 1 1 1 (P 0 2 1
  1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1
  U U) U) U) U)))

theorem cQSS3 : Fills 3 12 3 4 8 0 8 :=
  check_sound dQSS3 _ _ _ _ _ _ _ (by decide +kernel)

def dSpHead4 : Der :=
  P 1 3 7 2 3 (P 2 3 3 0 7 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 3 0 4 2 (P 0 2 0 2
  2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P
  1 1 0 0 1 U U) U) U) U))) (P 0 3 1 6 2 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 1 1
  1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U)) (P 2 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 3 1
  (P 1 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U)) (P 0 3 0
  4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 2 0 0 (P 0 2 2 0 1
  (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))))) (P 1 3 7 3 2 (P 0 3 3 7 0 (P 2 3 0 3 3 (P 2 2 0 1 3
  (P 1 2 0 0 3 W U) U) (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U)
  U) (P 0 2 2 0 0 (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U))) (P 2 3 1 2 6 (P 0 3 0 3 3
  (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U)
  U)) (P 0 3 0 5 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2
  0 1 1 (P 1 1 0 0 1 U U) U) U) U)) (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0
  1 U U) U) U) U) (P 0 2 2 0 0 (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U))))) (P 0 3 5 5
  2 (P 2 3 2 4 2 (P 1 3 0 2 3 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P
  1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1
  0 U U) U) U))) (P 1 3 0 6 3 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 2 0 3 1 (P 0 2 0
  0 3 W U) U)) (P 2 3 1 5 1 (P 0 2 1 1 1 (P 1 3 1 3 1 (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U)
  U) U) U) U) (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) (P 2 2 1 1 1 (P 0 2 1
  1 0 (P 0 1 0 1 0 U U) U) U))))) (P 2 3 4 4 2 (P 1 3 1 2 6 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0
  W U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U)) (P 0 3 0 3 3 (P 1 3 0
  3 3 (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U) U) (P 1 3 3 0 2 (P 2 2 2 0 0 (P 1 2 2 0 1 (P 0 2 1 0 1 (P
  0 1 0 0 1 U U) U) U) U) U))) (P 1 3 4 3 2 (P 0 3 1 5 2 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W
  U) U) (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U)) (P 2 3 0 2 4 (P 2 2 0 2
  2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 0 2 2 0 0 (P 2 2 2 1 0 (P 1 2 1 1 0 (P
  1 1 0 1 0 U U) U) U) U))) (P 2 2 1 1 4 (P 0 3 0 2 5 (P 1 3 0 2 3 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0
  1 0 0 1 U U) U) U) U) (P 1 3 1 0 3 (P 1 2 0 0 3 W U) U)) (P 0 2 1 2 2 (P 2 2 0 3 1 (P 1 2 0 2 1
  (P 0 1 0 0 1 U U) (P 2 1 0 1 0 U U)) (P 1 3 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U)) (P 2 2 0
  2 3 (P 1 2 0 1 3 (P 0 2 0 1 2 (P 2 1 0 0 1 U U) (P 1 1 0 0 1 U U)) (P 0 2 0 1 2 (P 2 1 0 0 1 U
  U) (P 1 1 0 0 1 U U))) (P 0 2 0 1 3 (P 1 2 0 1 2 (P 2 1 0 1 0 U U) (P 0 1 0 0 1 U U)) (P 1 2 0 1
  2 (P 2 1 0 1 0 U U) (P 0 1 0 0 1 U U))))))))))

theorem cSpHead4 : Fills 9 13 9 29 12 0 12 :=
  check_sound dSpHead4 _ _ _ _ _ _ _ (by decide +kernel)

def dSRBase4 : Der :=
  P 1 3 3 6 2 (P 2 3 1 2 3 (P 0 3 1 3 2 (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U)
  U) U) U) U) (P 2 3 1 2 3 (P 0 3 1 3 2 (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U)
  U) U) U) U) (P 0 3 1 3 2 (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) U)))
  (P 1 3 2 8 2 (P 2 3 0 3 4 (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U)
  U) U) U) U) (P 2 3 1 1 5 (P 1 2 1 1 1 (P 0 3 1 3 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U)
  U) U) U) U) (P 0 3 0 1 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) U))) (P 2 3 3 5 1 (P 1 3 2 2 2 (P 0 2
  1 1 1 (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U
  U) U) U)) (P 1 3 1 1 5 (P 2 2 1 1 1 (P 0 3 1 1 3 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U)
  U) U) U) U)) (P 1 3 2 5 2 (P 2 3 1 1 5 (P 1 2 1 1 1 (P 0 3 1 3 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2
  1 0 0 1 U U) U) U) U) U) (P 0 3 0 1 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) U)) (P 2 3 1 3 3 (P 1 3
  1 1 5 (P 2 2 1 1 1 (P 0 3 1 1 3 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U) U) U) (P 1
  3 1 1 5 (P 2 2 1 1 1 (P 0 3 1 1 3 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U) U) U)))))

theorem cSRBase4 : Fills 4 13 9 12 30 0 7 :=
  check_sound dSRBase4 _ _ _ _ _ _ _ (by decide +kernel)

def dSRPlate4 : Der :=
  P 1 3 0 9 4 (P 2 3 0 3 4 (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U)
  U) U) U) U) (P 2 3 0 3 4 (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U)
  U) U) U) U) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) U)))
  (P 2 3 0 6 4 (P 1 3 0 3 4 (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U)
  U) U) U) U) (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) U))
  (P 2 3 0 6 4 (P 1 3 0 3 4 (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U)
  U) U) U) U) (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) U))
  (P 1 3 0 3 4 (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) U)
  (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) U))))

theorem cSRPlate4 : Fills 4 9 9 0 27 12 12 :=
  check_sound dSRPlate4 _ _ _ _ _ _ _ (by decide +kernel)

def dZCss4 : Der :=
  P 1 3 0 4 4 (P 0 3 0 5 3 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) U) U) (P 1 3 0 3 4 (P 2
  3 0 3 4 (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) U) U) (P
  0 3 0 4 3 (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) U) U))

theorem cZCss4 : Fills 4 9 4 0 11 7 11 :=
  check_sound dZCss4 _ _ _ _ _ _ _ (by decide +kernel)

def dQSS4 : Der :=
  P 1 3 2 3 3 (P 0 3 1 4 2 (P 2 3 1 2 3 (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U)
  U) U) U) U) U) (P 1 3 2 2 2 (P 0 3 1 5 1 (P 1 2 1 1 1 (P 2 3 1 1 3 (P 2 2 1 1 1 (P 0 2 1 1 0 (P
  0 1 0 1 0 U U) U) U) U) U) U) (P 1 3 1 3 3 (P 0 3 1 4 2 (P 2 3 1 3 2 (P 0 2 1 1 1 (P 2 2 1 1 1
  (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U) U) U) (P 1 2 1 1 2 (P 2 2 0 1 3 (P 0 2 0 2 1 (P 1 1 0 0
  1 U U) (P 2 1 0 0 1 U U)) (P 0 2 0 2 1 (P 1 1 0 0 1 U U) (P 1 1 0 0 1 U U))) (P 0 2 0 3 1 (P 2 2
  0 1 2 (P 1 1 0 1 0 U U) (P 0 1 0 1 0 U U)) (P 2 2 0 1 2 (P 1 1 0 1 0 U U) (P 1 1 0 1 0 U U))))))

theorem cQSS4 : Fills 4 13 4 7 11 0 11 :=
  check_sound dQSS4 _ _ _ _ _ _ _ (by decide +kernel)

def dSpHead5 : Der :=
  P 1 3 6 4 3 (P 0 3 2 8 1 (P 2 3 1 3 2 (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U)
  U) U) U) (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0
  (P 0 1 0 1 0 U U) U) U) U))) (P 2 3 1 2 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2
  1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U)) (P 0 3 0 5 3 (P 2 3 0 3 3 (P 2 2 0 1
  3 (P 1 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U)) (P 2 3
  0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 0 2 2 0 0 (P 2 2 2 1
  0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U))))) (P 1 3 6 3 4 (P 2 3 2 1 8 (P 0 3 1 2 3 (P 2 2 1 1
  1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W
  U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U))) (P 0 3 1 6 2 (P 2 3 0
  3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U)
  U) U) U)) (P 2 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 2 2 0 1 2
  (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U)) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P
  2 1 0 1 0 U U) U) U) U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))))) (P
  2 3 6 3 3 (P 0 3 2 0 9 (P 1 3 0 3 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U)
  U) U) (P 1 3 0 3 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) (P 2 2 1 1
  0 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U))) (P 1 3 3 0 4 (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P
  1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) (P 1 2 2 0 0 (P 0 2 2 1 0 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U)
  U) U)) (P 0 3 0 3 4 (P 1 3 0 4 2 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U)
  U) (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U)) (P 1 3 0 3 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P
  2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 0 2 0 3 0 W U))))) (P 0 3 4 3 4 (P 1 3 0 5 3 (P 2 3 0 3
  3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U)
  U) U)) (P 2 3 1 3 3 (P 1 3 0 2 3 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U)
  U) (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U)) (P 1 3 3 2 0 (P 0 2 2 0 0 (P 1 2 2 1 0 (P
  2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U) (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U)))) (P 1 2
  1 3 3 (P 2 3 0 2 6 (P 0 3 0 3 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 0 1 2
  (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U)) (P 0 3 0 3 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U)
  U) U) (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U))) (P 1 2 1 3 3 (P 2 3 0 2 6 (P 0 3 0 3 2
  (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U)
  U)) (P 0 3 0 3 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 1 1 1 (P 2 2 1 0 1 (P
  2 1 0 0 1 U U) U) U))) (P 2 2 2 1 2 (P 0 2 1 0 3 (P 1 2 0 1 2 (P 2 1 0 1 0 U U) (P 2 1 0 1 0 U
  U)) (P 0 2 0 1 3 (P 1 2 0 1 2 (P 2 1 0 1 0 U U) (P 0 1 0 0 1 U U)) (P 1 3 1 1 1 (P 1 2 1 0 1 (P
  1 1 0 0 1 U U) U) U))) (P 0 2 1 2 2 (P 2 2 0 3 1 (P 1 2 0 2 1 (P 0 1 0 0 1 U U) (P 2 1 0 1 0 U
  U)) (P 1 3 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U)) (P 2 2 0 3 2 (P 0 2 0 1 3 (P 1 2 0 1 2 (P
  2 1 0 1 0 U U) (P 0 1 0 0 1 U U)) (P 1 2 0 1 2 (P 2 1 0 1 0 U U) (P 0 1 0 0 1 U U))) (P 1 3 1 0
  4 (P 0 2 0 2 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U)) U)))))))))

theorem cSpHead5 : Fills 9 14 9 29 15 0 15 :=
  check_sound dSpHead5 _ _ _ _ _ _ _ (by decide +kernel)

def dSRBase5 : Der :=
  P 1 3 3 9 1 (P 2 3 1 3 4 (P 0 3 0 3 2 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U)
  U) U) U) (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U)) (P 2 3 1 3 4 (P 0 3 0 3 2 (P 1 2 0 2
  2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U
  U) U) U)) (P 0 3 0 3 2 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 2
  1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U)))) (P 1 3 3 9 1 (P 2 3 1 3 4 (P 0 3 0 3 2 (P 1 2 0 2
  2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U
  U) U) U)) (P 2 3 1 3 4 (P 0 3 0 3 2 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U)
  U) U) (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U)) (P 0 3 0 3 2 (P 1 2 0 2 2 (P 0 2 0 1 2
  (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U)))) (P
  2 3 3 4 2 (P 1 3 1 3 3 (P 0 3 0 3 2 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U)
  U) U) (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U)) (P 1 3 1 0 8 (P 0 3 0 2 6 (P 2 2 0 1 1
  (P 2 1 0 1 0 U U) U) (P 2 2 1 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U)) (P 0 3 1 3 1 (P 0 2 1 1
  1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U)))) (P 1 3 3 3 3 (P 2 3
  1 3 2 (P 0 3 0 2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 2 2 0 3
  0 W U)) (P 0 3 0 4 3 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 1 2 1
  0 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U))) (P 2 2 1 2 2 (P 1 3 0 1 8 (P 0 3 0 1 6 (P 2 1 0 0 1 U
  U) (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U)) (P 0 3 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) (P 0 1 0 0
  1 U U))) (P 1 3 2 1 5 (P 0 3 2 3 2 (P 2 2 1 1 1 (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U)
  U) (P 1 2 0 0 3 W U)) (P 2 3 0 3 1 (P 2 2 0 3 0 W U) U)) (P 0 3 0 5 2 (P 2 3 0 2 3 (P 2 2 0 2 1
  (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U) (P 2 3 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U)))))))

theorem cSRBase5 : Fills 5 14 9 15 30 0 10 :=
  check_sound dSRBase5 _ _ _ _ _ _ _ (by decide +kernel)

def dSRPlate5 : Der :=
  P 1 3 0 9 5 (P 2 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2 0 1 2 (P 1 2 0 1
  1 (P 1 1 0 1 0 U U) U) U)) (P 2 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2 0
  1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U)) (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2
  0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U)))) (P 2 3 0 6 5 (P 1 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 1
  3 (P 2 2 0 3 0 W U) U) (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U)) (P 0 3 0 3 3 (P 0 2 0
  1 3 (P 2 2 0 3 0 W U) U) (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U))) (P 2 3 0 6 5 (P 1 3
  0 3 5 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U)
  U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U
  U) U) U))) (P 1 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 0 1 2 (P 2 2 0 1 1
  (P 2 1 0 1 0 U U) U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 0 1 2 (P 2 2 0 1
  1 (P 2 1 0 1 0 U U) U) U)))))

theorem cSRPlate5 : Fills 5 9 9 0 27 15 15 :=
  check_sound dSRPlate5 _ _ _ _ _ _ _ (by decide +kernel)

def dZCss5 : Der :=
  P 1 3 0 5 5 (P 0 3 0 6 3 (P 2 3 0 3 4 (P 1 2 0 2 2 (P 2 2 0 1 3 (P 0 2 0 2 1 (P 1 1 0 0 1 U U)
  U) U) U) (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U)) (P 2 3 0 3 2 (P 2 2 0 1 2 (P 1 2 0 1
  1 (P 1 1 0 1 0 U U) U) U) (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U))) (P 1 3 0 4 5 (P 2 3 0 3 5 (P 0 3 0
  3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U)) (P 0 3
  0 3 3 (P 1 2 0 0 3 W U) (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U))) (P 0 3 0 5 3 (P 2 3 0 3 3 (P 2 2 0 1
  3 (P 1 2 0 0 3 W U) U) (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U)) (P 2 3 0 3 3 (P 1 2 0
  3 0 W U) (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U))))

theorem cZCss5 : Fills 5 9 5 0 14 10 14 :=
  check_sound dZCss5 _ _ _ _ _ _ _ (by decide +kernel)

def dQSS5 : Der :=
  P 1 3 2 3 3 (P 0 3 1 5 2 (P 2 3 1 2 3 (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U)
  U) U) U) (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U)) (P 2 3 1 3 1 (P 2 2 1 1 1 (P 1 2 1 1
  0 (P 1 1 0 1 0 U U) U) U) (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U))) (P 1 3 2 3 3 (P 0 3 1 5 2 (P 2 3 1
  2 3 (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U) (P 1 2 0 2 1 (P 0 2 0 1 1
  (P 0 1 0 0 1 U U) U) U)) (P 2 3 1 3 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) (P 1 2 0
  1 1 (P 1 1 0 1 0 U U) U))) (P 1 3 2 3 3 (P 0 3 1 5 2 (P 2 3 1 2 3 (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0
  2 1 1 0 (P 0 1 0 1 0 U U) U) U) U) (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U)) (P 2 3 1 3
  1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U))) (P 1 3 2
  3 3 (P 0 3 1 5 2 (P 2 3 1 2 3 (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U)
  (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U)) (P 2 3 1 3 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1
  0 1 0 U U) U) U) (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U))) (P 0 3 1 5 1 (P 2 3 1 1 3 (P 2 2 1 1 1 (P 0
  2 1 1 0 (P 0 1 0 1 0 U U) U) U) (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U)) (P 2 3 1 2 2 (P 2 2 1 1 1 (P
  2 1 0 0 1 U U) U) (P 2 1 0 0 1 U U))))))

theorem cQSS5 : Fills 5 14 5 10 14 0 14 :=
  check_sound dQSS5 _ _ _ _ _ _ _ (by decide +kernel)

def dSpHead6 : Der :=
  P 1 3 6 3 4 (P 2 3 2 1 8 (P 0 3 1 2 3 (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U)
  U) U) U) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1
  (P 2 1 0 0 1 U U) U) U) U))) (P 0 3 1 6 2 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2
  1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U)) (P 2 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 3
  1 (P 1 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U)) (P 0 3
  0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 2 0 0 (P 0 2 2 0
  1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))))) (P 1 3 6 4 3 (P 0 3 2 8 1 (P 2 3 1 3 2 (P 0 2 1 1
  1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U) (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W
  U) U) (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U))) (P 2 3 1 2 6 (P 0 3 0
  3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U)
  U) U) U)) (P 0 3 0 5 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 0 2 0 2 1
  (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U)) (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P
  0 1 0 0 1 U U) U) U) U) (P 0 2 2 0 0 (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U))))) (P
  1 3 7 3 2 (P 0 3 3 7 0 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 3 0 2 4 (P 2 2 0 2 2
  (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 0 2 2 0 0 (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1
  1 0 1 0 U U) U) U) U))) (P 2 3 1 2 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 1 1 1
  (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U)) (P 0 3 0 5 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P
  1 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U)) (P 2 3 0 2
  4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 0 2 2 0 0 (P 2 2 2 1 0 (P
  1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U))))) (P 2 3 4 2 6 (P 0 3 1 2 6 (P 1 3 0 3 3 (P 1 2 0 3 1 (P
  0 2 0 3 0 W U) U) (P 2 2 1 1 1 (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U) U)) (P 1 3 0 3
  5 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0
  1 0 U U) U) U) U)) (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U)
  U) (P 1 2 2 0 0 (P 0 2 2 1 0 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U)))) (P 0 3 3 4 3 (P 1 3 0 5
  3 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0
  0 1 U U) U) U) U)) (P 2 3 0 4 2 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U)
  U) (P 1 2 2 0 0 (P 2 2 2 0 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U))) (P 2 2 1 3 3 (P 0 3 0 2 6
  (P 1 3 0 2 3 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1
  0 0 1 U U) U) U)) (P 1 3 0 2 3 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) (P 1 2 1 1 1 (P
  0 2 1 0 1 (P 0 1 0 0 1 U U) U) U))) (P 0 3 1 2 7 (P 1 3 0 1 6 (P 2 3 0 1 2 (P 2 2 0 1 1 (P 2 1 0
  1 0 U U) U) U) (P 0 2 0 2 1 (P 1 2 0 4 1 (P 2 2 0 2 1 (P 0 1 0 1 0 U U) (P 0 1 0 1 0 U U)) U)
  U)) (P 1 2 0 2 2 (P 2 3 0 2 3 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U) (P 1 2 0 2 2
  (P 2 3 0 2 3 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U) (P 2 2 0 2 2 (P 0 2 0 1 1 (P 0
  1 0 0 1 U U) U) (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U))))))))))

theorem cSpHead6 : Fills 9 15 9 29 18 0 18 :=
  check_sound dSpHead6 _ _ _ _ _ _ _ (by decide +kernel)

def dSRBase6 : Der :=
  P 1 3 3 7 3 (P 2 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 3 1 (P 1 2 0 3
  0 W U) U)) (P 0 3 0 5 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 0 2 0 2 1
  (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U)) (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P
  0 1 0 0 1 U U) U) U) U) (P 0 2 2 0 0 (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U)))) (P
  1 3 3 7 3 (P 2 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 3 1 (P 1 2 0 3 0
  W U) U)) (P 0 3 0 5 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 0 2 0 2 1
  (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U)) (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P
  0 1 0 0 1 U U) U) U) U) (P 0 2 2 0 0 (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U)))) (P
  2 3 3 6 3 (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0
  W U) U)) (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W
  U) U)) (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P
  1 1 0 0 1 U U) U) U) U)))) (P 1 3 3 3 4 (P 2 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U)
  U) (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U)) (P 0 3 0 4 2 (P 0 2 0 2 2
  (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1
  1 0 0 1 U U) U) U) U))) (P 2 2 1 3 3 (P 0 3 0 2 6 (P 1 3 0 2 3 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1
  0 0 1 U U) U) U) (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U)) (P 1 3 0 2 3 (P 1 2 0 2 1 (P
  0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U))) (P 0 2 2 1
  2 (P 1 2 1 3 0 (P 2 2 0 2 1 (P 0 1 0 1 0 U U) (P 0 1 0 1 0 U U)) (P 1 2 0 3 1 (P 2 2 0 2 1 (P 0
  1 0 1 0 U U) (P 1 1 0 1 0 U U)) (P 2 3 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U))) (P 1 2 1 2 2
  (P 0 2 0 3 1 (P 2 2 0 1 2 (P 1 1 0 1 0 U U) (P 0 1 0 1 0 U U)) (P 2 3 1 1 1 (P 2 2 1 0 1 (P 2 1
  0 0 1 U U) U) U)) (P 0 2 0 3 2 (P 1 2 0 3 1 (P 2 2 0 2 1 (P 0 1 0 1 0 U U) (P 1 1 0 1 0 U U)) (P
  2 2 0 2 1 (P 0 1 0 1 0 U U) (P 1 1 0 1 0 U U))) (P 2 3 1 4 0 (P 1 2 0 2 2 (P 2 2 0 1 1 (P 2 1 0
  0 1 U U) U) (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U)) U))))))))

theorem cSRBase6 : Fills 6 15 9 18 30 0 14 :=
  check_sound dSRBase6 _ _ _ _ _ _ _ (by decide +kernel)

def dSRPlate6 : Der :=
  P 1 3 0 9 6 (P 2 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 3 1 (P 1 2 0 3
  0 W U) U)) (P 2 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 3 1 (P 1 2 0 3 0
  W U) U)) (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U)))) (P
  2 3 0 6 6 (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0
  W U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U))) (P 2
  3 0 6 6 (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W
  U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U))) (P 1 3
  0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U)) (P 0 3 0
  3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U)))))

theorem cSRPlate6 : Fills 6 9 9 0 27 18 18 :=
  check_sound dSRPlate6 _ _ _ _ _ _ _ (by decide +kernel)

def dZCss6 : Der :=
  P 1 3 0 6 6 (P 0 3 0 7 3 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 0 2 2 (P 2 2 0 1
  3 (P 0 2 0 2 1 (P 1 1 0 0 1 U U) U) U) U)) (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2
  0 2 2 (P 2 2 0 1 3 (P 0 2 0 2 1 (P 1 1 0 0 1 U U) U) U) U))) (P 1 3 0 5 6 (P 2 3 0 2 8 (P 0 3 0
  4 3 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 2 2 0 2 2 (P 1 2 0 2 1
  (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U)) (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0
  3 1 (P 1 2 0 3 0 W U) U))) (P 0 3 0 8 2 (P 2 3 0 3 4 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2
  1 0 1 0 U U) U) U) U) (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U)) (P 2 3
  0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U))))

theorem cZCss6 : Fills 6 9 6 0 17 14 17 :=
  check_sound dZCss6 _ _ _ _ _ _ _ (by decide +kernel)

def dQSS6 : Der :=
  P 1 3 3 3 3 (P 0 3 0 6 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 1 3 (P 1 2 0 0
  3 W U) U)) (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 2 0 0 (P 2 2 2 0 1 (P 0 2 1 1 0
  (P 0 1 0 1 0 U U) U) U) U))) (P 1 3 3 3 3 (P 0 3 0 6 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W
  U) U) (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U)) (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 2
  0 0 (P 2 2 2 0 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U))) (P 1 3 3 4 4 (P 0 3 1 5 2 (P 2 3 0 3
  3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U)
  U) U)) (P 2 3 1 2 3 (P 2 2 1 1 2 (P 1 2 1 0 2 (P 0 2 1 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 2 2 1 2
  2 (P 1 2 1 1 2 (P 0 2 1 1 1 (P 0 1 0 0 1 U U) U) U) U))) (P 1 3 2 4 4 (P 0 3 1 6 2 (P 2 3 0 3 3
  (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U)
  U)) (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1
  0 1 0 U U) U) U) U))) (P 0 3 0 6 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 1 3
  (P 1 2 0 0 3 W U) U)) (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 2 0 0 (P 2 2 2 0 1
  (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U))))))

theorem cQSS6 : Fills 6 15 6 14 17 0 17 :=
  check_sound dQSS6 _ _ _ _ _ _ _ (by decide +kernel)

def dSpHead7 : Der :=
  P 1 3 5 4 5 (P 2 3 2 1 8 (P 0 3 1 2 3 (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U)
  U) U) U) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1
  (P 2 1 0 0 1 U U) U) U) U))) (P 0 3 1 6 2 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2
  1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U)) (P 2 3 1 2 5 (P 0 3 0 3 3 (P 0 2 0 3
  1 (P 1 2 0 3 0 W U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U)) (P 0 3
  0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U)
  U) U) U))))) (P 1 3 6 4 3 (P 0 3 2 8 1 (P 2 3 1 3 2 (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1
  1 0 1 0 U U) U) U) U) (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 1 1 1 (P 2 2 1 1 1
  (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U))) (P 2 3 1 2 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W
  U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U)) (P 0 3 0 5 3 (P 2 3 0 3
  3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U)
  U) U)) (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 0 2 2 0
  0 (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U))))) (P 1 3 7 2 3 (P 2 3 3 0 7 (P 0 3 0 3
  3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0
  1 0 U U) U) U) U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))) (P 0 3 1 6
  2 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0
  1 0 U U) U) U) U)) (P 2 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 2
  2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U)) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0
  1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U)
  U))))) (P 0 3 4 7 2 (P 2 3 2 5 2 (P 1 3 0 3 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1
  0 U U) U) U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 1 1 1 (P 2
  2 1 0 1 (P 2 1 0 0 1 U U) U) U))) (P 1 3 0 7 2 (P 2 3 0 4 3 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1
  1 (P 2 1 0 0 1 U U) U) U) U) (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U))
  (P 2 3 1 5 1 (P 0 2 1 1 1 (P 1 3 1 3 1 (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U) U)
  (P 1 3 0 1 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) U)))) (P 2 3 2 4 5 (P 1 3 0 2 7 (P 0 3 0 3 4 (P 1
  2 0 2 2 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0
  1 1 (P 0 1 0 0 1 U U) U) U) U)) (P 0 3 1 1 5 (P 2 2 1 1 1 (P 1 3 1 1 3 (P 1 2 1 1 1 (P 0 2 1 0 1
  (P 0 1 0 0 1 U U) U) U) U) U) (P 1 3 0 3 1 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) U))) (P 1 3 1 5 6
  (P 2 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1
  1 (P 1 1 0 1 0 U U) U) U) U)) (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2 1 1 1 (P 0 2
  1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))) (P 0 3 2 5 1 (P 2 3 0 5 3 (P 1 3 0 3 3 (P 1 2 0
  1 3 (P 2 2 0 0 3 W U) U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) (P 0
  2 0 3 0 W U))) (P 2 2 1 3 0 (P 1 2 0 2 2 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) (P 0 2 1 0 1 (P 0 1 0
  0 1 U U) U)) (P 2 2 0 2 2 (P 1 3 0 2 3 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 1
  2 0 2 2 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U))))))))))

theorem cSpHead7 : Fills 9 16 9 29 21 0 21 :=
  check_sound dSpHead7 _ _ _ _ _ _ _ (by decide +kernel)

def dSRBase7 : Der :=
  P 1 3 4 5 4 (P 2 3 1 2 6 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 3 1 3 2 (P 1 2 1 1
  1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) U)) (P 0 3 0 6 3 (P 2 3 0 3 3 (P 2 2 0 1
  3 (P 1 2 0 0 3 W U) U) (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U)) (P 2 3 0 3 3 (P 0 3 0 3 3 (P 0 2 0 3 1
  (P 1 2 0 3 0 W U) U) U) (P 0 3 3 2 0 (P 1 2 2 0 0 (P 0 2 2 1 0 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U)
  U) U) U)))) (P 1 3 4 5 4 (P 2 3 1 2 6 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 3 1 3
  2 (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) U)) (P 0 3 0 6 3 (P 2 3 0 3
  3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U)) (P 2 3 0 3 3 (P 0 3 0 3 3
  (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) U) (P 0 3 3 2 0 (P 1 2 2 0 0 (P 0 2 2 1 0 (P 2 2 1 0 1 (P 2 1
  0 0 1 U U) U) U) U) U)))) (P 1 3 4 5 4 (P 2 3 1 2 6 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U)
  U) (P 0 3 1 3 2 (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) U)) (P 0 3 0 6
  3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U)) (P 2 3 0 3 3
  (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) U) (P 0 3 3 2 0 (P 1 2 2 0 0 (P 0 2 2 1 0 (P 2 2
  1 0 1 (P 2 1 0 0 1 U U) U) U) U) U)))) (P 2 3 3 5 4 (P 0 3 1 1 8 (P 1 3 0 4 3 (P 2 2 0 2 2 (P 0
  2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 2 2 1 1 1 (P 1 3 1 1 3 (P 1 2 1 1 1 (P 0 2 1
  0 1 (P 0 1 0 0 1 U U) U) U) U) U)) (P 1 3 0 3 3 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U)
  U) (P 1 2 0 2 2 (P 0 3 0 3 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 0 3 1 3 0
  (P 0 2 0 3 0 W U) U)))) (P 0 3 3 3 4 (P 1 3 0 6 3 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U)
  (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U)) (P 2 3 1 5 1 (P 0 2 1 1 1 (P 1 3 1 3 1 (P 1 2 1 1 1 (P 2 2 1
  1 0 (P 2 1 0 1 0 U U) U) U) U) U) (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U)
  (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U)))) (P 1 3 1 7 2 (P 2 3 0 6 1 (P 0 3 0 1 2 (P 0
  2 0 1 1 (P 0 1 0 1 0 U U) U) U) (P 1 2 0 1 2 (P 2 2 0 1 4 (P 0 2 0 2 1 (P 1 1 0 0 1 U U) (P 1 1
  0 0 1 U U)) U) U)) (P 2 3 1 3 3 (P 1 3 1 1 5 (P 2 2 1 1 1 (P 0 3 1 1 3 (P 0 2 1 1 1 (P 1 2 1 0 1
  (P 1 1 0 0 1 U U) U) U) U) U) U) (P 1 3 1 1 5 (P 2 2 1 1 1 (P 0 3 1 1 3 (P 0 2 1 1 1 (P 1 2 1 0
  1 (P 1 1 0 0 1 U U) U) U) U) U) U)))))))

theorem cSRBase7 : Fills 7 16 9 21 30 0 19 :=
  check_sound dSRBase7 _ _ _ _ _ _ _ (by decide +kernel)

def dSRPlate7 : Der :=
  P 1 3 0 9 7 (P 2 3 0 3 7 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 3 0 4 2 (P 0 2 0 2
  2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) U)) (P 0 3 0 6 3 (P 2 3 0 3 3 (P 2 2 0 1
  3 (P 1 2 0 0 3 W U) U) (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U)) (P 2 3 0 3 4 (P 0 3 0 4 2 (P 0 2 0 2 2
  (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) U) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2
  (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) U)))) (P 2 3 0 6 7 (P 0 3 0 3 6 (P 1 3 0 3 3 (P 1 2 0 1
  3 (P 2 2 0 0 3 W U) U) (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U)) (P 1 3 0 3 4 (P 0 3 0 2 4 (P 0 2 0 2 2
  (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) U) (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2
  (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) U))) (P 0 3 0 6 6 (P 2 3 0 6 3 (P 1 3 0 3 3 (P 1 2 0 3 1
  (P 0 2 0 3 0 W U) U) (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U)) (P 1 3 0 3 3 (P 1 2 0 3 1 (P 0 2 0 3 0 W
  U) U) (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U))) (P 2 3 0 6 4 (P 1 3 0 3 4 (P 0 3 0 2 4 (P 0 2 0 2 2 (P
  2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) U) (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1
  2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) U)) (P 1 3 0 3 4 (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1
  2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) U) (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1
  0 1 0 U U) U) U) U) U)))))

theorem cSRPlate7 : Fills 7 9 9 0 27 21 21 :=
  check_sound dSRPlate7 _ _ _ _ _ _ _ (by decide +kernel)

def dZCss7 : Der :=
  P 1 3 0 7 7 (P 0 3 0 8 3 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 3 0 3 3 (P 2 2 0 3
  1 (P 0 2 0 0 3 W U) U) U)) (P 2 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) U) (P 2 3
  0 3 4 (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) U) U))) (P
  0 3 0 9 5 (P 2 3 0 5 4 (P 1 3 0 3 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U)
  U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U)) (P 1 3 0 5 2 (P 2 3 0 4
  3 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) U) (P 2 3 0 3 3 (P 2 2 0 3 1
  (P 0 2 0 0 3 W U) U) U))) (P 2 3 0 6 4 (P 1 3 0 3 4 (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1
  2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) U) (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1
  0 1 0 U U) U) U) U) U)) (P 1 2 0 2 3 (P 2 2 0 1 3 (P 0 2 0 2 1 (P 1 1 0 0 1 U U) (P 2 1 0 0 1 U
  U)) (P 0 2 0 2 1 (P 1 1 0 0 1 U U) (P 2 1 0 0 1 U U))) (P 1 2 0 3 2 (P 0 2 0 3 1 (P 2 2 0 1 2 (P
  1 1 0 1 0 U U) (P 0 1 0 1 0 U U)) (P 2 2 0 1 2 (P 1 1 0 1 0 U U) (P 0 1 0 1 0 U U))) (P 2 2 0 1
  3 (P 0 2 0 2 1 (P 1 1 0 0 1 U U) (P 2 1 0 0 1 U U)) (P 0 2 0 2 1 (P 1 1 0 0 1 U U) (P 2 1 0 0 1
  U U)))))))

theorem cZCss7 : Fills 7 9 7 0 20 19 20 :=
  check_sound dZCss7 _ _ _ _ _ _ _ (by decide +kernel)

def dQSS7 : Der :=
  P 1 3 4 4 4 (P 0 3 2 6 2 (P 2 3 1 3 3 (P 2 2 1 2 2 (P 0 2 1 1 2 (P 1 2 1 1 1 (P 1 1 0 0 1 U U)
  U) U) U) (P 2 3 1 2 2 (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U) U)) (P 2
  3 1 3 4 (P 0 3 1 3 2 (P 0 2 1 2 1 (P 1 2 1 2 0 (P 2 2 1 1 1 (P 1 1 0 1 0 U U) U) U) U) U) (P 2 3
  1 1 5 (P 1 2 1 1 1 (P 0 3 1 3 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) U) U))) (P
  1 3 3 4 4 (P 0 3 1 7 2 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 3 1 3 2 (P 0 2 1 1 1
  (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U) U)) (P 2 3 1 2 4 (P 0 3 1 2 3 (P 2 2 1 1 1
  (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U) U) (P 2 3 1 1 5 (P 1 2 1 1 1 (P 0 3 1 3 1
  (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) U) U))) (P 1 3 4 3 4 (P 2 3 2 1 6 (P 0 3 1
  3 2 (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) (P 0 3 1 3 2 (P 1 2 1 1 1
  (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) U)) (P 0 3 1 4 3 (P 2 3 1 2 3 (P 2 2 1 1 2
  (P 1 2 1 0 2 (P 0 2 1 1 1 (P 1 1 0 0 1 U U) U) U) U) U) (P 0 3 1 5 1 (P 1 2 1 1 1 (P 2 3 1 1 3
  (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U) U) U))) (P 1 3 3 4 4 (P 0 3 1 7 2 (P 2 3 0
  3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 3 1 3 2 (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1
  0 1 0 U U) U) U) U) U)) (P 2 3 1 2 4 (P 0 3 1 2 3 (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1
  0 0 1 U U) U) U) U) U) (P 2 3 1 1 5 (P 1 2 1 1 1 (P 0 3 1 3 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0
  0 1 U U) U) U) U) U) U))) (P 0 3 2 6 2 (P 2 3 1 3 3 (P 1 3 1 2 2 (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0
  2 1 1 0 (P 0 1 0 1 0 U U) U) U) U) U) (P 2 3 1 5 1 (P 0 2 1 1 1 (P 1 3 1 3 1 (P 1 2 1 1 1 (P 2 2
  1 1 0 (P 2 1 0 1 0 U U) U) U) U) U) U)) (P 2 3 1 3 4 (P 1 3 0 3 3 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2
  2 0 3 0 W U) U) U) U) (P 1 2 0 2 3 (P 2 2 0 1 3 (P 0 2 0 2 1 (P 1 1 0 0 1 U U) (P 2 1 0 0 1 U
  U)) (P 0 2 0 2 1 (P 1 1 0 0 1 U U) (P 2 1 0 0 1 U U))) (P 0 3 1 4 0 (P 2 2 0 2 2 (P 0 2 0 1 1 (P
  0 1 0 0 1 U U) U) (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U)) U)))))))

theorem cQSS7 : Fills 7 16 7 19 20 0 20 :=
  check_sound dQSS7 _ _ _ _ _ _ _ (by decide +kernel)

def dSpHead8 : Der :=
  P 1 3 5 4 5 (P 2 3 2 1 8 (P 0 3 1 2 3 (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U)
  U) U) U) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1
  (P 2 1 0 0 1 U U) U) U) U))) (P 0 3 1 6 2 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2
  1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U)) (P 2 3 1 2 5 (P 0 3 0 3 3 (P 0 2 0 3
  1 (P 1 2 0 3 0 W U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U)) (P 0 3
  0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U)
  U) U) U))))) (P 1 3 5 5 4 (P 0 3 2 8 1 (P 2 3 1 3 2 (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1
  1 0 1 0 U U) U) U) U) (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 1 1 1 (P 2 2 1 1 1
  (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U))) (P 2 3 1 2 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W
  U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U)) (P 0 3 1 5 2 (P 2 3 0 3
  3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U)
  U) U)) (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P
  1 1 0 1 0 U U) U) U) U))))) (P 1 3 7 2 3 (P 2 3 3 0 7 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W
  U) U) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 2 0
  0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))) (P 0 3 1 6 2 (P 2 3 0 3 3 (P 2 2 0 3 1
  (P 0 2 0 0 3 W U) U) (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U)) (P 2 3 0
  3 5 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1
  0 1 0 U U) U) U) U)) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U)
  U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))))) (P 0 3 4 8 2 (P 2 3 1 7
  3 (P 1 3 0 3 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 1 3 0 3 2 (P
  0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1
  0 0 1 U U) U) U))) (P 1 3 1 6 1 (P 2 3 0 3 4 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0
  U U) U) U) U) (P 1 2 1 2 0 (P 0 2 0 3 0 W U) U)) (P 2 3 1 4 3 (P 1 3 0 3 2 (P 0 2 0 2 2 (P 1 2 0
  1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U))
  (P 1 3 0 3 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 0 2 1 1 1 (P 2
  2 1 0 1 (P 2 1 0 0 1 U U) U) U))))) (P 2 3 3 5 3 (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0
  3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U)) (P 0 3 1 0 8 (P 1 3 0 2 6 (P 2 2 0 1 1 (P 2 1 0 0
  1 U U) U) (P 2 2 1 1 0 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U)) (P 1 3 0 3 1 (P 0 2 0 3 1 (P 1 2 0
  3 0 W U) U) (P 0 2 2 1 0 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U)))) (P 1 2 2 3 2 (P 0 2 1 4 0 (P 2
  2 0 1 2 (P 1 1 0 1 0 U U) (P 2 2 0 2 1 (P 0 1 0 1 0 U U) (P 0 1 0 1 0 U U))) (P 2 2 0 2 1 (P 0 3
  0 1 2 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) (P 2 2 0 1 3 (P 0 2 0 2 1 (P 1 1 0 0 1 U U) (P 2 1 0
  0 1 U U)) (P 0 3 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U)))) (P 2 3 0 5 6 (P 1 3 0 2 8 (P 0 3
  0 3 4 (P 1 2 0 2 2 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U) (P 1 2 0 2 2 (P 2 2 0 2
  1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2
  0 1 3 (P 2 2 0 3 0 W U) U))) (P 0 3 0 2 7 (P 1 3 0 3 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P
  1 1 0 1 0 U U) U) U) U) (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U)) (P 1
  3 0 2 4 (P 1 2 0 2 2 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U) (P 0 2 2 0 0 (P 1 2 2
  1 0 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U)))))))))

theorem cSpHead8 : Fills 9 17 9 29 24 0 24 :=
  check_sound dSpHead8 _ _ _ _ _ _ _ (by decide +kernel)

def dSRBase8 : Der :=
  P 1 3 4 6 4 (P 2 3 1 3 5 (P 0 3 0 2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U)
  U) U) U) (P 0 3 0 2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 2 2 1
  1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U))) (P 0 3 0 6 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W
  U) U) (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U)) (P 2 3 1 0 8 (P 0 3 0 6 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U
  U) U) (P 1 2 1 0 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U)) (P 0 3 0 1 3 (P 2 2 0 3 1 (P 0 2 0 0 3
  W U) U) (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U))))) (P 1 3 4 6 4 (P 2 3 1 3 5 (P 0 3 0
  2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 0 3 0 2 3 (P 2 2 0 2 2
  (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U)
  U) U))) (P 0 3 0 6 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 1 3 (P 1 2 0 0 3 W
  U) U)) (P 2 3 1 0 8 (P 0 3 0 6 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) (P 1 2 1 0 1 (P 2 2 1 0 1 (P
  2 1 0 0 1 U U) U) U)) (P 0 3 0 1 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 2 2 1 0 (P 1 2 1 1 0
  (P 1 1 0 1 0 U U) U) U))))) (P 1 3 4 6 4 (P 2 3 1 3 5 (P 0 3 0 2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P
  1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 0 3 0 2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1
  0 0 1 U U) U) U) U) (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U))) (P 0 3 0 6 3 (P 2 3 0 3
  3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U)) (P 2 3 1 0 8 (P 0 3 0 6 2
  (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) (P 1 2 1 0 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U)) (P 0 3 0 1
  3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U))))) (P 2 3
  4 4 4 (P 1 3 1 3 5 (P 0 3 0 3 2 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U)
  U) (P 0 3 0 3 2 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 2 1 1 1
  (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U))) (P 0 3 1 3 4 (P 1 3 0 2 3 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0
  2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U)) (P 0 3 2 0
  7 (P 1 3 0 1 6 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) (P 2 2 1 1 0 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U)
  U)) (P 1 3 0 3 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) (P 2 2 0 1 1 (P 2 1 0 1 0 U
  U) U))))) (P 1 3 3 3 6 (P 0 3 0 6 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 1 3
  (P 1 2 0 0 3 W U) U)) (P 2 3 1 3 2 (P 0 3 0 2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0
  0 1 U U) U) U) U) (P 2 2 0 3 0 W U)) (P 0 3 0 4 3 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1
  0 0 1 U U) U) U) U) (P 1 2 1 0 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U)))) (P 0 3 2 6 2 (P 2 3 1 4
  3 (P 1 3 0 3 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 0 2 1 1 1 (P
  2 2 1 0 1 (P 2 1 0 0 1 U U) U) U)) (P 1 3 0 3 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0
  1 0 U U) U) U) U) (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U))) (P 2 2 1 2 2 (P 0 3 0 1 8
  (P 1 3 0 1 6 (P 2 1 0 1 0 U U) (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U)) (P 1 3 1 1 1 (P 1 2 1 0 1 (P 1
  1 0 0 1 U U) U) (P 1 1 0 0 1 U U))) (P 0 3 2 1 5 (P 1 3 2 3 2 (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1
  0 1 (P 1 1 0 0 1 U U) U) U) (P 0 2 0 0 3 W U)) (P 2 3 0 1 3 (P 2 2 0 0 3 W U) U)) (P 1 3 0 5 2
  (P 2 3 0 3 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) (P 2 3 0 2 1 (P 2 2 0 1 1 (P 2
  1 0 0 1 U U) U) U)))))))))

theorem cSRBase8 : Fills 8 17 9 24 30 0 24 :=
  check_sound dSRBase8 _ _ _ _ _ _ _ (by decide +kernel)

def dSRPlate8 : Der :=
  P 1 3 0 9 8 (P 2 3 0 3 8 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 3 0 3 3 (P 0 2 0 3
  1 (P 1 2 0 3 0 W U) U) (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U))) (P 0 3 0 6 3 (P 2 3 0
  3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U)) (P 2 3 0 3 5 (P 0 3 0 3
  3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U)) (P 0 3 0
  3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U))))) (P 2
  3 0 6 8 (P 0 3 0 3 6 (P 1 3 0 3 3 (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U) (P 1 2 0 1 3 (P 2 2 0 0 3 W
  U) U)) (P 1 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 0 1 2 (P 2 2 0 1 1 (P
  2 1 0 1 0 U U) U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 0 1 2 (P 2 2 0 1 1
  (P 2 1 0 1 0 U U) U) U)))) (P 0 3 0 6 6 (P 2 3 0 6 3 (P 1 3 0 3 3 (P 1 2 0 3 1 (P 0 2 0 3 0 W U)
  U) (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U)) (P 1 3 0 3 3 (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U) (P 1 2 0 3
  1 (P 0 2 0 3 0 W U) U))) (P 2 3 0 6 5 (P 1 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U)
  U) (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W
  U) U) (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U))) (P 1 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 1 3
  (P 2 2 0 3 0 W U) U) (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U)) (P 0 3 0 3 3 (P 0 2 0 1
  3 (P 2 2 0 3 0 W U) U) (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U))))))

theorem cSRPlate8 : Fills 8 9 9 0 27 24 24 :=
  check_sound dSRPlate8 _ _ _ _ _ _ _ (by decide +kernel)

def dZCss8 : Der :=
  P 1 3 0 8 8 (P 0 3 0 9 3 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 3 0 3 4 (P 1 2 0 2
  2 (P 2 2 0 1 3 (P 0 2 0 2 1 (P 1 1 0 0 1 U U) U) U) U) (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U
  U) U) U))) (P 2 3 0 3 6 (P 0 3 0 4 3 (P 1 2 0 2 2 (P 0 2 0 3 1 (P 2 2 0 1 2 (P 1 1 0 1 0 U U) U)
  U) U) (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U)) (P 2 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 3 1
  (P 1 2 0 3 0 W U) U) (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U)) (P 0 3 0 2 3 (P 0 2 0 2
  1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U))))) (P 0 2 0 7 3 (P 2 2
  0 3 2 (P 1 3 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U)) (P 1 2 0
  4 1 (P 2 2 0 1 2 (P 1 1 0 1 0 U U) (P 2 2 0 2 1 (P 0 1 0 1 0 U U) (P 1 1 0 1 0 U U))) (P 2 3 0 5
  2 (P 1 3 0 3 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 1 3 0 3 1 (P 1 2 0 3 0 W
  U) U)))) (P 2 3 0 6 6 (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3
  (P 2 2 0 3 0 W U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W
  U) U))) (P 1 3 0 2 9 (P 0 3 0 8 3 (P 2 3 0 1 5 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 1 2 0 0 3 W
  U)) (P 2 3 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) (P 2 1 0 1 0 U U))) (P 2 1 0 0 5 U (P 0 2 0 2
  1 (P 1 2 0 4 1 (P 2 2 0 2 1 (P 0 1 0 1 0 U U) (P 0 1 0 1 0 U U)) U) (P 0 2 0 2 1 (P 1 2 0 4 1 (P
  2 2 0 2 1 (P 0 1 0 1 0 U U) (P 0 1 0 1 0 U U)) U) (P 1 2 0 4 1 (P 2 2 0 2 1 (P 0 1 0 1 0 U U) (P
  0 1 0 1 0 U U)) U)))))))

theorem cZCss8 : Fills 8 9 8 0 23 24 23 :=
  check_sound dZCss8 _ _ _ _ _ _ _ (by decide +kernel)

def dQSS8 : Der :=
  P 1 3 4 4 4 (P 0 3 1 5 3 (P 2 3 0 3 2 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U)
  U) U) U) (P 2 3 0 3 2 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) (P 0 2 1
  1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U))) (P 2 3 1 3 4 (P 0 3 0 3 2 (P 1 2 0 2 2 (P 0 2 0 1 2
  (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U)) (P 2
  3 2 0 7 (P 0 3 0 6 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) (P 1 2 1 0 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U
  U) U) U)) (P 0 3 0 2 3 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) (P 1 2 0 1 1 (P 1 1 0 0
  1 U U) U))))) (P 1 3 4 4 4 (P 0 3 1 5 3 (P 2 3 0 3 2 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1
  1 0 1 0 U U) U) U) U) (P 2 3 0 3 2 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U)
  U) U) (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U))) (P 2 3 1 3 4 (P 0 3 0 3 2 (P 1 2 0 2 2
  (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U)
  U) U)) (P 2 3 2 0 7 (P 0 3 0 6 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) (P 1 2 1 0 1 (P 2 2 1 0 1 (P
  2 1 0 0 1 U U) U) U)) (P 0 3 0 2 3 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) (P 1 2 0 1
  1 (P 1 1 0 0 1 U U) U))))) (P 1 3 4 4 4 (P 0 3 1 5 3 (P 2 3 0 3 2 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1
  2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) (P 2 3 0 3 2 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0
  1 0 U U) U) U) U) (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U))) (P 2 3 1 3 4 (P 0 3 0 3 2
  (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2
  1 0 1 0 U U) U) U)) (P 2 3 2 0 7 (P 0 3 0 6 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) (P 1 2 1 0 1 (P
  2 2 1 0 1 (P 2 1 0 0 1 U U) U) U)) (P 0 3 0 2 3 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U)
  U) (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U))))) (P 1 3 4 4 4 (P 0 3 1 5 3 (P 2 3 0 3 2 (P 0 2 0 2 2 (P
  2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) (P 2 3 0 3 2 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2
  0 1 1 (P 1 1 0 1 0 U U) U) U) U) (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U))) (P 2 3 1 3
  4 (P 0 3 0 3 2 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 2 1 1 1 (P
  2 2 1 1 0 (P 2 1 0 1 0 U U) U) U)) (P 2 3 2 0 7 (P 0 3 0 6 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U)
  (P 1 2 1 0 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U)) (P 0 3 0 2 3 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1
  0 0 1 U U) U) U) (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U))))) (P 0 3 3 6 3 (P 2 3 1 4 2 (P 1 3 1 2 3 (P
  2 2 1 1 1 (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U) U) (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1
  0 1 0 U U) U) U)) (P 2 3 1 5 2 (P 1 3 1 3 3 (P 2 2 1 2 1 (P 0 2 1 0 2 (P 1 2 1 1 1 (P 0 1 0 0 1
  U U) U) U) U) (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U)) (P 1 3 1 2 3 (P 1 2 1 1 2 (P 0
  2 1 1 1 (P 0 1 0 0 1 U U) U) U) (P 0 2 0 2 1 (P 1 1 0 0 1 U U) U)))) (P 2 3 2 4 4 (P 0 3 1 2 4
  (P 1 3 1 3 2 (P 0 2 1 1 1 (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U) (P 0 2 0 1 2 (P 2
  2 0 1 1 (P 2 1 0 0 1 U U) U) U)) (P 1 3 1 3 2 (P 1 2 1 2 1 (P 2 2 1 1 1 (P 2 1 0 1 0 U U) U) U)
  (P 2 2 0 1 2 (P 1 1 0 1 0 U U) U))) (P 2 3 2 3 4 (P 1 3 1 2 4 (P 0 3 1 3 2 (P 1 2 1 1 1 (P 0 2 1
  1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U))
  (P 0 3 1 3 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) (P 2 2 0 1 1 (P 2 1 0 0 1 U U)
  U))) (P 0 3 1 1 4 (P 1 3 1 1 3 (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U) (P 0 2 0 1 1 (P
  0 1 0 0 1 U U) U)) (P 1 3 0 2 3 (P 1 2 0 1 2 (P 2 1 0 1 0 U U) U) (P 0 1 0 0 1 U U)))))))))

theorem cQSS8 : Fills 8 17 8 24 23 0 23 :=
  check_sound dQSS8 _ _ _ _ _ _ _ (by decide +kernel)

def dSpHead9 : Der :=
  P 1 3 5 4 5 (P 2 3 2 1 8 (P 0 3 1 2 3 (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U)
  U) U) U) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1
  (P 2 1 0 0 1 U U) U) U) U))) (P 0 3 1 6 2 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2
  1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U)) (P 2 3 1 2 5 (P 0 3 0 3 3 (P 0 2 0 3
  1 (P 1 2 0 3 0 W U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U)) (P 0 3
  0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U)
  U) U) U))))) (P 1 3 5 5 4 (P 0 3 2 8 1 (P 2 3 1 3 2 (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1
  1 0 1 0 U U) U) U) U) (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 1 1 1 (P 2 2 1 1 1
  (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U))) (P 2 3 1 2 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W
  U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U)) (P 0 3 1 5 2 (P 2 3 0 3
  3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U)
  U) U)) (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P
  1 1 0 1 0 U U) U) U) U))))) (P 1 3 6 3 4 (P 2 3 2 1 8 (P 0 3 1 2 3 (P 2 2 1 1 1 (P 0 2 1 1 1 (P
  1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 1 1 1
  (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U))) (P 0 3 1 6 2 (P 2 3 0 3 3 (P 2 2 0 3 1 (P
  0 2 0 0 3 W U) U) (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U)) (P 2 3 0 3
  5 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0
  1 0 U U) U) U) U)) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U)
  U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))))) (P 1 3 3 5 7 (P 2 3 0 3
  8 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U)
  (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U))) (P 0 3 0 7 3 (P 2 3 0 3 3 (P
  2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U)
  U)) (P 2 3 0 2 7 (P 0 3 0 4 3 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U)
  (P 1 2 0 2 2 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U)) (P 0 3 0 4 2 (P 0 2 0 2 2 (P
  1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1
  0 0 1 U U) U) U) U))))) (P 0 3 3 6 3 (P 2 3 0 6 3 (P 1 3 0 3 3 (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U)
  (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U)) (P 2 3 0 6 3 (P 1 3 0 3 3 (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U)
  (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U)) (P 1 3 0 3 3 (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U) (P 0 2 2 0 0
  (P 1 2 2 1 0 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U)))) (P 2 3 1 5 6 (P 1 3 0 3 5 (P 0 3 0 3 3
  (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U)
  U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1
  0 0 1 U U) U) U) U))) (P 0 3 3 3 3 (P 1 3 0 6 3 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U)
  (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U)) (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 0 2 2 0 0
  (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U))) (P 1 3 0 7 2 (P 2 3 0 4 3 (P 1 2 0 2 2 (P
  0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1
  0 1 0 U U) U) U) U)) (P 2 3 0 4 2 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U)
  U) (P 1 2 2 0 0 (P 2 2 2 0 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U)))))))))

theorem cSpHead9 : Fills 9 18 9 29 27 0 27 :=
  check_sound dSpHead9 _ _ _ _ _ _ _ (by decide +kernel)

def dSRBase9 : Der :=
  P 1 3 0 7 11 (P 2 3 0 2 10 (P 0 3 0 3 4 (P 1 2 0 2 2 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U)
  U) U) U) (P 0 3 0 4 3 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 1 2 0
  2 2 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U))) (P 0 3 0 5 4 (P 2 3 0 2 3 (P 1 2 0 2
  2 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U) (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P
  1 1 0 1 0 U U) U) U) U)) (P 2 3 0 2 7 (P 0 3 0 4 3 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1
  0 0 1 U U) U) U) U) (P 1 2 0 2 2 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U)) (P 0 3 0
  3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U)
  U) U) U))))) (P 1 3 9 0 2 (P 2 3 3 0 6 (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1
  1 0 1 0 U U) U) U) U) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U)
  U) U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))) (P 0 3 3 3 1 (P 2 2 1
  1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P
  1 1 0 0 1 U U) U) U) (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U))) (P 2 3 0 3 5 (P 0 3 0 3
  3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U)
  U) U)) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 2 0
  0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))))) (P 1 3 0 8 10 (P 2 3 0 3 8 (P 0 3 0 3
  3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 2 2
  (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U))) (P 0 3 0 7 3 (P 2 3 0 3 3 (P 2 2 0 3 1 (P
  0 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U)) (P 2 3 0 2
  7 (P 0 3 0 4 3 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 1 2 0 2 2 (P
  2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U)) (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U)
  U) (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U))))) (P 0 3 9 0 0 (P 1 3 3 8
  0 (P 2 3 0 4 2 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 2 3 0 2 4 (P
  2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 0 2 2 0 0 (P 2 2 2 1 0 (P 1 2
  1 1 0 (P 1 1 0 1 0 U U) U) U) U))) (P 2 3 3 5 0 (P 1 3 0 3 3 (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U)
  (P 0 2 2 0 0 (P 1 2 2 1 0 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U)) (P 2 3 0 6 3 (P 1 3 0 3 3 (P
  1 2 0 3 1 (P 0 2 0 3 0 W U) U) (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U)) (P 1 3 0 3 3 (P 1 2 0 1 3 (P 2
  2 0 0 3 W U) U) (P 0 2 2 0 0 (P 1 2 2 1 0 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U))))) (P 1 3 3 7
  3 (P 2 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U))
  (P 0 3 0 5 3 (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1
  1 (P 1 1 0 0 1 U U) U) U) U)) (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U
  U) U) U) U) (P 0 2 2 0 0 (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U)))) (P 2 3 3 4 4 (P
  0 3 0 3 5 (P 1 3 0 3 3 (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U) (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1
  (P 2 1 0 0 1 U U) U) U) U)) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) (P 1
  2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 0 3 0 W U)))) (P 0 3 0 4 6 (P 2
  3 0 8 2 (P 1 3 0 4 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 2 2 0
  2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U)) (P 1 3 0 4 3 (P 2 2 0 2 2 (P 0 2 0 2 1
  (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U)
  U) U) U))) (P 1 3 0 9 1 (P 2 3 0 3 5 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 1 1 (P 0 1 0 0 1
  U U) U)) (P 2 3 0 4 2 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 1 2 2
  0 0 (P 2 2 2 0 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U)))))))))

theorem cSRBase9 : Fills 9 18 9 27 30 0 30 :=
  check_sound dSRBase9 _ _ _ _ _ _ _ (by decide +kernel)

def dSRPlate9 : Der :=
  P 0 3 0 9 9 (P 1 3 0 9 3 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 3 0 3 3 (P 2 2 0 3
  1 (P 0 2 0 0 3 W U) U) (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U))) (P 2 3 0 6 3 (P 1 3 0 3 3 (P 1 2 0 3
  1 (P 0 2 0 3 0 W U) U) (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U)) (P 2 3 0 6 3 (P 1 3 0 3 3 (P 1 2 0 3 1
  (P 0 2 0 3 0 W U) U) (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U)) (P 1 3 0 3 3 (P 1 2 0 3 1 (P 0 2 0 3 0 W
  U) U) (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U))))) (P 1 3 0 9 6 (P 2 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 3 1
  (P 1 2 0 3 0 W U) U) (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U)) (P 2 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 3 1
  (P 1 2 0 3 0 W U) U) (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U)) (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W
  U) U) (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U)))) (P 2 3 0 6 6 (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3
  (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W
  U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U))) (P 2 3 0 6 6 (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P
  2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U)
  U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U))) (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U)
  U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1
  3 (P 2 2 0 3 0 W U) U))))))

theorem cSRPlate9 : Fills 9 9 9 0 27 27 27 :=
  check_sound dSRPlate9 _ _ _ _ _ _ _ (by decide +kernel)

def dZCss9 : Der :=
  P 1 3 0 9 9 (P 0 3 0 10 3 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 3 0 3 3 (P 2 2 0 3
  1 (P 0 2 0 0 3 W U) U) (P 1 2 0 2 2 (P 2 2 0 1 3 (P 0 2 0 2 1 (P 1 1 0 0 1 U U) U) U) U))) (P 2
  3 0 3 7 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 0 2 2 (P 0 2 0 3 1 (P 2 2 0 1 2 (P
  1 1 0 1 0 U U) U) U) U)) (P 2 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 3
  1 (P 1 2 0 3 0 W U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 0 2 2 (P 0 2 0 3 1
  (P 2 2 0 1 2 (P 1 1 0 1 0 U U) U) U) U))))) (P 0 3 0 11 5 (P 2 3 0 5 4 (P 1 3 0 3 2 (P 0 2 0 2 2
  (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0
  1 0 0 1 U U) U) U) U)) (P 1 3 0 7 2 (P 2 3 0 4 3 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0
  0 1 U U) U) U) U) (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U)) (P 2 3 0 3
  3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U)
  U) U)))) (P 2 3 0 6 6 (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3
  (P 2 2 0 3 0 W U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W
  U) U))) (P 2 3 0 6 6 (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P
  2 2 0 3 0 W U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U)
  U))) (P 1 3 0 2 7 (P 0 3 0 3 4 (P 1 2 0 2 2 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U)
  (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P
  2 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U))))))

theorem cZCss9 : Fills 9 9 9 0 26 30 26 :=
  check_sound dZCss9 _ _ _ _ _ _ _ (by decide +kernel)

def dQSS9 : Der :=
  P 1 3 5 4 5 (P 2 3 2 1 8 (P 0 3 1 2 3 (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U)
  U) U) U) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1
  (P 2 1 0 0 1 U U) U) U) U))) (P 0 3 1 6 2 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2
  1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U)) (P 2 3 1 2 5 (P 0 3 0 3 3 (P 0 2 0 3
  1 (P 1 2 0 3 0 W U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U)) (P 0 3
  0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2 1 1 2 (P 1 2 1 0 2 (P 0 2 1 1 1 (P 1 1 0 0 1 U U)
  U) U) U))))) (P 1 3 5 5 4 (P 0 3 2 8 1 (P 2 3 1 3 2 (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1
  1 0 1 0 U U) U) U) U) (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 1 1 1 (P 2 2 1 1 1
  (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U))) (P 2 3 1 2 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W
  U) U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U)) (P 0 3 1 5 2 (P 2 3 0 3
  3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U)
  U) U)) (P 2 3 0 3 3 (P 2 2 0 1 3 (P 1 2 0 0 3 W U) U) (P 0 2 1 2 1 (P 1 2 1 2 0 (P 2 2 1 1 1 (P
  1 1 0 1 0 U U) U) U) U))))) (P 1 3 5 4 5 (P 2 3 2 1 8 (P 0 3 1 2 3 (P 2 2 1 1 1 (P 0 2 1 1 1 (P
  1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 1 2 1 1 1
  (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U))) (P 0 3 1 6 2 (P 2 3 0 3 3 (P 2 2 0 3 1 (P
  0 2 0 0 3 W U) U) (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U)) (P 2 3 1 2
  5 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0
  0 1 U U) U) U) U)) (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2 1 1 2 (P 1 2 1 0 2 (P 0
  2 1 1 1 (P 1 1 0 0 1 U U) U) U) U))))) (P 1 3 6 3 4 (P 2 3 2 1 8 (P 0 3 1 2 3 (P 2 2 1 1 1 (P 0
  2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U)
  (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U))) (P 0 3 1 6 2 (P 2 3 0 3 3 (P
  2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U)
  U)) (P 2 3 1 2 5 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2
  1 0 1 (P 1 1 0 0 1 U U) U) U) U)) (P 0 3 1 3 2 (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0
  1 U U) U) U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))))) (P 0 3 3 8
  2 (P 2 3 0 5 4 (P 1 3 0 3 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P
  2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U)) (P 1 3 0 7 2 (P 2 3 0 4 3 (P 1 2
  0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1
  1 (P 2 1 0 1 0 U U) U) U) U)) (P 2 3 0 4 2 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U
  U) U) U) U) (P 1 2 2 0 0 (P 2 2 2 0 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U)))) (P 2 3 3 3 4 (P
  1 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1
  (P 2 1 0 1 0 U U) U) U) U)) (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U
  U) U) U) U) (P 1 2 2 0 0 (P 0 2 2 1 0 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U))) (P 0 2 1 3 3 (P
  2 3 0 6 2 (P 1 3 0 3 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) (P 1 2 0 1 2 (P 2 2 0 1
  1 (P 2 1 0 1 0 U U) U) U)) (P 1 3 0 3 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) (P 1 2
  1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U))) (P 2 3 1 7 2 (P 1 3 0 6 1 (P 0 3 0 2 1 (P 0 2 0 1 1
  (P 0 1 0 0 1 U U) U) U) (P 2 2 0 1 2 (P 1 2 0 1 4 (P 0 2 0 1 2 (P 2 1 0 0 1 U U) (P 2 1 0 0 1 U
  U)) U) U)) (P 1 2 0 2 2 (P 0 3 0 3 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 1 2
  0 2 2 (P 0 3 0 3 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 0 2 0 2 2 (P 2 2 0 1
  1 (P 2 1 0 1 0 U U) U) (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U)))))))))))

theorem cQSS9 : Fills 9 18 9 30 26 0 26 :=
  check_sound dQSS9 _ _ _ _ _ _ _ (by decide +kernel)

def dSlab9Base : Der :=
  P 0 5 16 0 2 (P 1 3 4 6 1 (P 2 3 1 3 3 (P 0 3 0 2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1
  1 0 0 1 U U) U) U) U) (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U)) (P 2 3 1 0 8 (P 0 3 0 6
  2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) (P 1 2 1 0 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U)) (P 0 3 0
  1 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U)))) (P 2
  3 4 1 3 (P 1 3 2 0 4 (P 0 3 0 4 3 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U)
  U) (P 1 2 1 0 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U)) (P 0 3 2 2 3 (P 1 2 1 1 1 (P 2 2 1 1 1 (P
  0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) (P 2 2 0 0 3 W U)) (P 1 3 0 3 1 (P 1 2 0 3 0 W U) U))) (P 1 3
  4 3 2 (P 2 3 1 3 2 (P 0 3 0 2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U)
  U) (P 2 2 0 3 0 W U)) (P 0 3 3 2 0 (P 1 2 2 0 0 (P 0 2 2 1 0 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U)
  U) U) (P 2 2 0 3 0 W U))) (P 2 3 1 4 3 (P 0 3 0 3 3 (P 1 3 0 3 3 (P 1 2 0 1 3 (P 2 2 0 0 3 W U)
  U) U) (P 1 2 0 2 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U))) (P 0 3
  2 2 1 (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 0 3 0 W U)) (P 1 2 0
  2 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U))))))) (P 1 3 4 6 1 (P 2
  3 1 3 3 (P 0 3 0 2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 2 2 1
  1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U)) (P 2 3 1 0 8 (P 0 3 0 6 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U
  U) U) (P 1 2 1 0 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U)) (P 0 3 0 1 3 (P 2 2 0 3 1 (P 0 2 0 0 3
  W U) U) (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U)))) (P 2 3 4 1 3 (P 1 3 2 0 4 (P 0 3 0
  4 3 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 1 2 1 0 1 (P 2 2 1 0 1
  (P 2 1 0 0 1 U U) U) U)) (P 0 3 2 2 3 (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U)
  U) U) (P 2 2 0 0 3 W U)) (P 1 3 0 3 1 (P 1 2 0 3 0 W U) U))) (P 1 3 4 3 2 (P 2 3 1 3 2 (P 0 3 0
  2 3 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 2 2 0 3 0 W U)) (P 0 3
  3 2 0 (P 1 2 2 0 0 (P 0 2 2 1 0 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) (P 2 2 0 3 0 W U))) (P 2
  3 1 4 3 (P 0 3 0 3 3 (P 1 3 0 3 3 (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U) U) (P 1 2 0 2 2 (P 2 2 0 1 1
  (P 2 1 0 0 1 U U) U) (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U))) (P 0 3 2 2 1 (P 1 2 1 1 1 (P 0 2 1 1 1
  (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 0 3 0 W U)) (P 1 2 0 2 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U
  U) U) (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U)))))))

theorem cSlab9Base : Fills 10 10 9 32 0 0 4 :=
  check_sound dSlab9Base _ _ _ _ _ _ _ (by decide +kernel)

def dZeroBarBase : Der :=
  P 0 3 0 10 8 (P 1 3 0 8 3 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 3 0 3 3 (P 2 2 0 3
  1 (P 0 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U))) (P 2
  3 0 7 3 (P 1 3 0 3 3 (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U) (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P
  2 1 0 0 1 U U) U) U) U)) (P 1 3 0 7 2 (P 2 3 0 4 3 (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1
  0 0 1 U U) U) U) U) (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U)) (P 2 3 0
  3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U)
  U) U) U))))) (P 1 3 0 6 9 (P 2 3 0 3 5 (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1
  1 0 1 0 U U) U) U) U) (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) U)) (P 0 3 0 9 3 (P 2 3 0 2
  4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) (P 2 2 0 1 3 (P 1 2 0 0 3 W
  U) U)) (P 2 3 0 0 6 (P 0 3 0 6 3 (P 1 2 0 0 2 (P 2 2 0 0 4 (P 0 2 0 2 2 (P 1 1 0 0 1 U U) U) U)
  U) U) (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) U)))) (P 2
  3 0 9 5 (P 0 3 0 2 5 (P 1 3 0 3 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) U)
  U) (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U)) (P 1 3 0 3 5 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U)
  U) U) (P 0 3 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U))) (P 0 3 0 7 5 (P 1 3 0 7 2 (P 2 3 0 4 3
  (P 1 2 0 2 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U) (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2
  2 0 1 1 (P 2 1 0 1 0 U U) U) U) U)) (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 2 0 2 2
  (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U))) (P 1 3 0 6 3 (P 2 3 0 3 5 (P 0 3 0 3 3 (P
  0 2 0 1 3 (P 2 2 0 3 0 W U) U) U) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) U)) (P 2 3 0 3
  5 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) U) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U)
  U) U))))))

theorem cZeroBarBase : Fills 10 9 9 0 27 32 28 :=
  check_sound dZeroBarBase _ _ _ _ _ _ _ (by decide +kernel)

def dABar10Base : Der :=
  P 2 3 9 2 0 (P 1 3 3 0 8 (P 0 3 0 2 4 (P 0 2 0 2 2 (P 2 2 0 1 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U)
  U) U) U) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 2
  0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))) (P 0 3 2 1 6 (P 1 3 1 2 3 (P 2 2 1 1
  1 (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U) U) (P 1 3 1 2 3 (P 2 2 1 1 1 (P 1 2 1 1 1 (P
  0 2 1 0 1 (P 0 1 0 0 1 U U) U) U) U) U)) (P 1 3 1 2 6 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W
  U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U)) (P 0 3 0 3 3 (P 1 3 0 3
  3 (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U) U) (P 1 3 3 0 2 (P 2 2 2 0 0 (P 1 2 2 0 1 (P 0 2 1 0 1 (P 0
  1 0 0 1 U U) U) U) U) U))))) (P 1 3 7 0 4 (P 0 3 2 4 2 (P 2 3 0 3 2 (P 0 2 0 2 2 (P 2 2 0 1 2 (P
  1 2 0 1 1 (P 1 1 0 1 0 U U) U) U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U)
  U) (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U))) (P 2 3 3 0 4 (P 0 3 0 4 2 (P 0 2 0 2 2 (P
  1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 2 0 0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1
  0 0 1 U U) U) U) U)) (P 0 3 1 5 1 (P 1 2 1 1 1 (P 2 3 1 1 3 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1
  0 U U) U) U) U) U) (P 2 3 0 3 1 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) U)))) (P 0 3 6 2 1 (P 1 3 3 5
  0 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 3 3 2 0 (P 0 2 2 0 0 (P 2 2 2 1 0 (P 1 2 1
  1 0 (P 1 1 0 1 0 U U) U) U) U) U)) (P 2 3 2 2 2 (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0
  1 0 U U) U) U) (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U)) (P 2 3 1 5 1 (P 0 2 1 1 1 (P 1
  3 1 3 1 (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U) U) U))) (P 2 3 3 4 3 (P 1 3 0 3 6
  (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U)) (P 0 3 1 1 5
  (P 2 2 1 1 1 (P 1 3 1 1 3 (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U) U) U) (P 1 2 1 1 1
  (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U)
  U)))) (P 1 3 2 2 6 (P 0 3 1 4 2 (P 2 3 1 3 2 (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0
  U U) U) U) U) U) (P 2 3 0 3 1 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) U)) (P 0 2 1 1 2 (P 2 2 0 3 1 (P
  1 2 0 2 1 (P 0 1 0 0 1 U U) (P 2 1 0 1 0 U U)) (P 1 2 0 2 1 (P 0 1 0 0 1 U U) (P 0 1 0 0 1 U
  U))) (P 0 2 1 2 1 (P 1 2 0 3 1 (P 2 2 0 2 1 (P 0 1 0 1 0 U U) (P 1 1 0 1 0 U U)) (P 2 2 0 2 1 (P
  0 1 0 1 0 U U) (P 0 1 0 1 0 U U))) (P 2 2 0 3 1 (P 1 2 0 2 1 (P 0 1 0 0 1 U U) (P 2 1 0 1 0 U
  U)) (P 1 2 0 2 1 (P 0 1 0 0 1 U U) (P 0 1 0 0 1 U U)))))))))

theorem cABar10Base : Fills 9 10 10 30 6 0 4 :=
  check_sound dABar10Base _ _ _ _ _ _ _ (by decide +kernel)

def dZBar10Base : Der :=
  P 0 3 0 10 9 (P 2 3 0 9 3 (P 1 3 0 3 3 (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U) (P 1 3 0 3 3 (P 1 2 0 3
  1 (P 0 2 0 3 0 W U) U) (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U))) (P 1 3 0 7 3 (P 2 3 0 3 3 (P 2 2 0 3
  1 (P 0 2 0 0 3 W U) U) (P 2 3 0 4 2 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U)
  U) U) U)) (P 2 3 0 6 3 (P 1 3 0 3 3 (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U) (P 1 2 0 3 1 (P 0 2 0 3 0
  W U) U)) (P 1 3 0 4 3 (P 2 3 0 4 2 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U)
  U) U) U) (P 2 3 0 4 2 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) U)))))
  (P 2 3 0 9 8 (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 3 0 3 3 (P 0 2 0 1
  3 (P 2 2 0 3 0 W U) U) U)) (P 0 3 0 3 6 (P 1 3 0 3 3 (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U) (P 1 2 0
  1 3 (P 2 2 0 0 3 W U) U)) (P 1 3 0 3 3 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) U) (P 0 3
  0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) U)))) (P 1 2 0 4 5 (P 2 3 0 2 7 (P 0 3 0 3 2 (P 0 2 0 1
  2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) (P 0 3 0 3 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U)
  U) U) U)) (P 0 3 0 5 2 (P 2 3 0 2 3 (P 2 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U) (P 2 2
  0 1 3 (P 0 2 0 2 1 (P 1 1 0 0 1 U U) (P 2 1 0 0 1 U U)) (P 0 2 0 2 1 (P 1 1 0 0 1 U U) (P 2 1 0
  0 1 U U))))) (P 2 3 0 7 8 (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 3 0 3
  3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) U)) (P 0 3 0 3 4 (P 1 3 0 2 4 (P 1 2 0 2 2 (P 2 2 0 2 1 (P 0
  2 0 1 1 (P 0 1 0 1 0 U U) U) U) U) U) (P 1 2 0 2 2 (P 0 3 0 3 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1
  0 0 1 U U) U) U) U) (P 0 3 0 3 2 (P 0 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 0 1 U U) U) U) U)))) (P 1 3
  0 6 3 (P 0 3 0 6 0 (P 2 3 0 3 6 (P 1 2 0 2 0 (P 0 2 0 4 0 (P 2 2 0 2 2 (P 1 1 0 1 0 U U) U) U)
  U) U) (P 0 3 0 2 3 (P 2 3 0 4 2 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U)
  U) U) U)) (P 0 3 0 4 5 (P 2 2 0 2 2 (P 1 3 0 2 3 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U)
  U) U) (P 1 3 0 2 3 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U)) (P 2 2 0 2 3 (P 1 2 0 1
  3 (P 0 2 0 1 2 (P 2 1 0 0 1 U U) (P 1 1 0 0 1 U U)) (P 0 2 0 1 2 (P 2 1 0 0 1 U U) (P 1 1 0 0 1
  U U))) (P 1 2 0 1 3 (P 0 2 0 1 2 (P 2 1 0 0 1 U U) (P 1 1 0 0 1 U U)) (P 0 2 0 1 2 (P 2 1 0 0 1
  U U) (P 1 1 0 0 1 U U)))))))))

theorem cZBar10Base : Fills 10 9 10 0 30 36 28 :=
  check_sound dZBar10Base _ _ _ _ _ _ _ (by decide +kernel)

def dPlate9910 : Der :=
  P 2 3 0 9 9 (P 0 3 0 3 9 (P 1 3 0 3 3 (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U) (P 1 3 0 3 3 (P 1 2 0 1
  3 (P 2 2 0 0 3 W U) U) (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U))) (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1
  3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U)) (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3
  (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W
  U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U))))) (P 0 3 0 7 9 (P 1 3 0 7 3 (P 2 3 0 3 3 (P 2 2 0 3 1
  (P 0 2 0 0 3 W U) U) (P 2 3 0 4 2 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U)
  U) U)) (P 2 3 0 6 3 (P 1 3 0 3 3 (P 1 2 0 3 1 (P 0 2 0 3 0 W U) U) (P 1 2 0 3 1 (P 0 2 0 3 0 W
  U) U)) (P 1 3 0 4 3 (P 2 3 0 4 2 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U)
  U) U) (P 2 3 0 4 2 (P 2 2 0 2 2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) U)))) (P 1
  3 0 7 6 (P 2 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 3 1 (P 1 2 0 3 0 W
  U) U)) (P 0 3 0 4 3 (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U)
  U) U) (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) U))) (P 2 3
  0 6 6 (P 1 3 0 3 6 (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U)
  U)) (P 0 3 0 3 3 (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) U))) (P 1 3 0
  4 6 (P 0 3 0 4 3 (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U)
  U) (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) U)) (P 0 3 0 4
  3 (P 2 3 0 2 4 (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) U) (P 2 3 0 2 4
  (P 2 2 0 2 2 (P 1 2 0 2 1 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) U) U) U))))))

theorem cPlate9910 : Fills 9 9 10 0 30 30 27 :=
  check_sound dPlate9910 _ _ _ _ _ _ _ (by decide +kernel)

def dCube10 : Der :=
  P 0 3 11 0 0 (P 1 3 3 8 0 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 3 0 3 3 (P 2 2 0 3
  1 (P 0 2 0 0 3 W U) U) (P 2 3 3 2 0 (P 0 2 2 0 0 (P 2 2 2 1 0 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U)
  U) U) U))) (P 2 3 2 6 1 (P 1 3 1 3 2 (P 0 2 1 1 1 (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U)
  U) U) (P 1 3 1 3 2 (P 0 2 1 1 1 (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U) U)) (P 2 3
  3 4 1 (P 1 3 1 2 2 (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U) (P 1 3 1 2
  2 (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U) U)) (P 1 3 2 2 2 (P 2 2 1 1
  1 (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U) (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U)
  U) U)) (P 1 3 1 5 1 (P 0 2 1 1 1 (P 2 3 1 3 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U)
  U) U) U))))) (P 1 3 9 0 0 (P 2 3 3 0 4 (P 0 3 0 3 3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 1
  3 (P 2 2 0 3 0 W U) (P 2 2 2 0 0 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U))) (P 2 3 3 0 4 (P 0 3 0 3
  3 (P 0 2 0 3 1 (P 1 2 0 3 0 W U) U) (P 0 2 0 1 3 (P 2 2 0 3 0 W U) (P 2 2 2 0 0 (P 1 2 1 0 1 (P
  1 1 0 0 1 U U) U) U))) (P 0 3 2 3 2 (P 2 2 1 1 1 (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U)
  U) (P 1 2 0 0 3 W U)) (P 2 2 0 2 2 (P 0 3 0 2 3 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U)
  U) U) (P 0 2 0 2 2 (P 1 2 0 1 1 (P 1 1 0 1 0 U U) U) (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U)))))) (P 2
  3 6 2 2 (P 0 3 3 1 3 (P 1 3 1 2 2 (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U)
  U) (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) (P 0 2 0 3 0 W U))) (P 1 3 2 2
  2 (P 0 2 1 1 1 (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2
  1 0 1 0 U U) U) U)) (P 1 3 1 1 5 (P 2 2 1 1 1 (P 0 3 1 1 3 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0
  1 U U) U) U) U) U) U))) (P 0 3 4 3 3 (P 1 3 2 4 2 (P 2 3 0 2 3 (P 1 2 0 2 2 (P 2 2 0 2 1 (P 0 2
  0 1 1 (P 0 1 0 1 0 U U) U) U) U) (P 2 2 1 1 1 (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U)
  (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U))) (P 2 3 1 6 1 (P 0 2 0 1 2 (P 2 2 0 4 1 (P 1
  2 0 2 1 (P 0 1 0 0 1 U U) (P 0 1 0 0 1 U U)) U) U) (P 1 2 0 2 2 (P 2 3 0 2 3 (P 2 2 0 2 1 (P 0 2
  0 1 1 (P 0 1 0 1 0 U U) U) U) U) (P 2 2 0 2 2 (P 0 2 0 1 1 (P 0 1 0 0 1 U U) U) (P 0 2 1 1 0 (P
  0 1 0 1 0 U U) U))))) (P 1 3 3 5 1 (P 2 3 2 2 2 (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0
  1 0 U U) U) U) (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U)) (P 2 3 1 1 5 (P 1 2 1 1 1 (P 0
  3 1 3 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) U) U)) (P 2 3 1 4 3 (P 0 3 0 3 3 (P
  1 3 0 3 3 (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U) U) U) (P 0 2 0 2 3 (P 2 2 0 3 1 (P 1 2 0 2 1 (P 0 1
  0 0 1 U U) (P 2 1 0 1 0 U U)) (P 1 2 0 2 1 (P 0 1 0 0 1 U U) (P 2 1 0 1 0 U U))) (P 1 3 1 4 0 (P
  2 2 0 2 2 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U)) U)))))))

theorem cCube10 : Fills 10 10 10 36 0 0 0 :=
  check_sound dCube10 _ _ _ _ _ _ _ (by decide +kernel)

def dCube9 : Der :=
  P 0 3 10 0 0 (P 1 3 3 7 0 (P 2 3 0 3 3 (P 2 2 0 3 1 (P 0 2 0 0 3 W U) U) (P 2 3 0 4 2 (P 2 2 0 2
  2 (P 0 2 0 2 1 (P 1 2 0 1 1 (P 1 1 0 0 1 U U) U) U) U) (P 1 2 2 0 0 (P 2 2 2 0 1 (P 0 2 1 1 0 (P
  0 1 0 1 0 U U) U) U) U))) (P 2 3 2 5 1 (P 1 3 1 3 2 (P 0 2 1 1 1 (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2
  1 0 1 0 U U) U) U) U) (P 2 2 1 1 1 (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U) U)) (P 2 3
  2 5 1 (P 1 3 1 3 2 (P 0 2 1 1 1 (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 1 1
  1 (P 1 2 1 1 1 (P 0 2 1 0 1 (P 0 1 0 0 1 U U) U) U) U)) (P 1 3 1 2 2 (P 1 2 1 1 1 (P 2 2 1 1 1
  (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U) (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U)
  U) U) U))))) (P 1 3 7 3 0 (P 2 3 2 1 5 (P 0 3 1 3 2 (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2
  1 0 0 1 U U) U) U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U)) (P 2 3
  2 1 5 (P 0 3 1 3 2 (P 1 2 1 1 1 (P 0 2 1 1 1 (P 2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) (P 2 2 1 1
  1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U)) (P 0 3 1 2 2 (P 0 2 1 1 1 (P 2 2 1 1 1
  (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U) (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U)
  U) U) U)))) (P 2 3 4 3 2 (P 0 3 1 2 5 (P 1 3 0 3 3 (P 1 2 0 1 3 (P 2 2 0 0 3 W U) U) (P 0 2 1 1
  1 (P 1 2 1 1 1 (P 2 2 1 1 0 (P 2 1 0 1 0 U U) U) U) U)) (P 1 3 0 2 4 (P 1 2 0 2 2 (P 2 2 0 2 1
  (P 0 2 0 1 1 (P 0 1 0 1 0 U U) U) U) U) (P 0 2 2 0 0 (P 1 2 2 1 0 (P 2 2 1 1 0 (P 2 1 0 1 0 U U)
  U) U) U))) (P 1 3 4 3 2 (P 0 3 2 5 1 (P 2 3 1 2 3 (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1
  0 1 0 U U) U) U) U) (P 0 2 1 1 1 (P 2 2 1 1 1 (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U)) (P 2 3 1
  2 3 (P 1 2 1 1 1 (P 2 2 1 1 1 (P 0 2 1 1 0 (P 0 1 0 1 0 U U) U) U) U) (P 0 2 1 1 1 (P 2 2 1 1 1
  (P 1 2 1 1 0 (P 1 1 0 1 0 U U) U) U) U))) (P 2 3 2 1 5 (P 0 3 1 3 2 (P 1 2 1 1 1 (P 0 2 1 1 1 (P
  2 2 1 0 1 (P 2 1 0 0 1 U U) U) U) U) (P 2 2 1 1 1 (P 0 2 1 1 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U)
  U) U)) (P 0 3 0 4 2 (P 0 2 0 2 2 (P 1 2 0 1 2 (P 2 2 0 1 1 (P 2 1 0 1 0 U U) U) U) U) (P 2 2 2 0
  0 (P 0 2 2 0 1 (P 1 2 1 0 1 (P 1 1 0 0 1 U U) U) U) U))))))

theorem cCube9 : Fills 9 9 9 30 0 0 0 :=
  check_sound dCube9 _ _ _ _ _ _ _ (by decide +kernel)

end cells

end OMA.Cube

namespace OMA.Cube

section final

theorem ceilDiv_eq_of {a b s : ℕ} (hb : 0 < b) (h1 : a ≤ s * b) (h2 : s * b < a + b) :
    a ⌈/⌉ b = s := by
  rw [Nat.ceilDiv_eq_add_pred_div]
  exact Nat.div_eq_of_lt_le (by omega) (by rw [Nat.add_mul, Nat.one_mul]; omega)

theorem predicted_r2 (k : ℕ) : predicted (9 * k + 9 + 2) =
    27 * (k + 1) * (k + 1) + 6 * (k + 1) * 2 + 2 * (k + 1) + 2 := by
  have hb : 3 * (9 * k + 9 + 2) - 2 = 27 * k + 31 := by omega
  have hid : (27 * (k + 1) * (k + 1) + 6 * (k + 1) * 2 + 2 * (k + 1) + 2) * (27 * k + 31) =
      (9 * k + 9 + 2) ^ 3 + (2 * k + 2) := by ring
  show (9 * k + 9 + 2) ^ 3 ⌈/⌉ (3 * (9 * k + 9 + 2) - 2) = _
  rw [hb]
  exact ceilDiv_eq_of (by omega) (by rw [hid]; omega) (by rw [hid]; omega)

theorem predicted_r3 (k : ℕ) : predicted (9 * k + 9 + 3) =
    27 * (k + 1) * (k + 1) + 6 * (k + 1) * 3 + 2 * (k + 1) + 4 := by
  have hb : 3 * (9 * k + 9 + 3) - 2 = 27 * k + 34 := by omega
  have hid : (27 * (k + 1) * (k + 1) + 6 * (k + 1) * 3 + 2 * (k + 1) + 4) * (27 * k + 34) =
      (9 * k + 9 + 3) ^ 3 + (5 * k + 6) := by ring
  show (9 * k + 9 + 3) ^ 3 ⌈/⌉ (3 * (9 * k + 9 + 3) - 2) = _
  rw [hb]
  exact ceilDiv_eq_of (by omega) (by rw [hid]; omega) (by rw [hid]; omega)

theorem predicted_r4 (k : ℕ) : predicted (9 * k + 9 + 4) =
    27 * (k + 1) * (k + 1) + 6 * (k + 1) * 4 + 2 * (k + 1) + 7 := by
  have hb : 3 * (9 * k + 9 + 4) - 2 = 27 * k + 37 := by omega
  have hid : (27 * (k + 1) * (k + 1) + 6 * (k + 1) * 4 + 2 * (k + 1) + 7) * (27 * k + 37) =
      (9 * k + 9 + 4) ^ 3 + (17 * k + 23) := by ring
  show (9 * k + 9 + 4) ^ 3 ⌈/⌉ (3 * (9 * k + 9 + 4) - 2) = _
  rw [hb]
  exact ceilDiv_eq_of (by omega) (by rw [hid]; omega) (by rw [hid]; omega)

theorem predicted_r5 (k : ℕ) : predicted (9 * k + 9 + 5) =
    27 * (k + 1) * (k + 1) + 6 * (k + 1) * 5 + 2 * (k + 1) + 10 := by
  have hb : 3 * (9 * k + 9 + 5) - 2 = 27 * k + 40 := by omega
  have hid : (27 * (k + 1) * (k + 1) + 6 * (k + 1) * 5 + 2 * (k + 1) + 10) * (27 * k + 40) =
      (9 * k + 9 + 5) ^ 3 + (11 * k + 16) := by ring
  show (9 * k + 9 + 5) ^ 3 ⌈/⌉ (3 * (9 * k + 9 + 5) - 2) = _
  rw [hb]
  exact ceilDiv_eq_of (by omega) (by rw [hid]; omega) (by rw [hid]; omega)

theorem predicted_r6 (k : ℕ) : predicted (9 * k + 9 + 6) =
    27 * (k + 1) * (k + 1) + 6 * (k + 1) * 6 + 2 * (k + 1) + 14 := by
  have hb : 3 * (9 * k + 9 + 6) - 2 = 27 * k + 43 := by omega
  have hid : (27 * (k + 1) * (k + 1) + 6 * (k + 1) * 6 + 2 * (k + 1) + 14) * (27 * k + 43) =
      (9 * k + 9 + 6) ^ 3 + (14 * k + 22) := by ring
  show (9 * k + 9 + 6) ^ 3 ⌈/⌉ (3 * (9 * k + 9 + 6) - 2) = _
  rw [hb]
  exact ceilDiv_eq_of (by omega) (by rw [hid]; omega) (by rw [hid]; omega)

theorem predicted_r7 (k : ℕ) : predicted (9 * k + 9 + 7) =
    27 * (k + 1) * (k + 1) + 6 * (k + 1) * 7 + 2 * (k + 1) + 19 := by
  have hb : 3 * (9 * k + 9 + 7) - 2 = 27 * k + 46 := by omega
  have hid : (27 * (k + 1) * (k + 1) + 6 * (k + 1) * 7 + 2 * (k + 1) + 19) * (27 * k + 46) =
      (9 * k + 9 + 7) ^ 3 + (26 * k + 44) := by ring
  show (9 * k + 9 + 7) ^ 3 ⌈/⌉ (3 * (9 * k + 9 + 7) - 2) = _
  rw [hb]
  exact ceilDiv_eq_of (by omega) (by rw [hid]; omega) (by rw [hid]; omega)

theorem predicted_r8 (k : ℕ) : predicted (9 * k + 9 + 8) =
    27 * (k + 1) * (k + 1) + 6 * (k + 1) * 8 + 2 * (k + 1) + 24 := by
  have hb : 3 * (9 * k + 9 + 8) - 2 = 27 * k + 49 := by omega
  have hid : (27 * (k + 1) * (k + 1) + 6 * (k + 1) * 8 + 2 * (k + 1) + 24) * (27 * k + 49) =
      (9 * k + 9 + 8) ^ 3 + (20 * k + 36) := by ring
  show (9 * k + 9 + 8) ^ 3 ⌈/⌉ (3 * (9 * k + 9 + 8) - 2) = _
  rw [hb]
  exact ceilDiv_eq_of (by omega) (by rw [hid]; omega) (by rw [hid]; omega)

theorem predicted_r9 (k : ℕ) : predicted (9 * k + 9 + 9) =
    27 * (k + 1) * (k + 1) + 6 * (k + 1) * 9 + 2 * (k + 1) + 30 := by
  have hb : 3 * (9 * k + 9 + 9) - 2 = 27 * k + 52 := by omega
  have hid : (27 * (k + 1) * (k + 1) + 6 * (k + 1) * 9 + 2 * (k + 1) + 30) * (27 * k + 52) =
      (9 * k + 9 + 9) ^ 3 + (23 * k + 44) := by ring
  show (9 * k + 9 + 9) ^ 3 ⌈/⌉ (3 * (9 * k + 9 + 9) - 2) = _
  rw [hb]
  exact ceilDiv_eq_of (by omega) (by rw [hid]; omega) (by rw [hid]; omega)

theorem predicted_r1 (j : ℕ) : predicted (9 * j + 19) =
    27 * (j + 1) * (j + 1) + 62 * (j + 1) + 36 := by
  have hb : 3 * (9 * j + 19) - 2 = 27 * j + 55 := by omega
  have hid : (27 * (j + 1) * (j + 1) + 62 * (j + 1) + 36) * (27 * j + 55) =
      (9 * j + 19) ^ 3 + (8 * j + 16) := by ring
  show (9 * j + 19) ^ 3 ⌈/⌉ (3 * (9 * j + 19) - 2) = _
  rw [hb]
  exact ceilDiv_eq_of (by omega) (by rw [hid]; omega) (by rw [hid]; omega)

/-- A spanning configuration of tangent points is a surjective tangent map. -/
theorem fullTangents_of_fills {n r : ℕ} (h : Fills n n n r 0 0 0) :
    ∃ z : Slots n r → ℂ, Function.Surjective (tangentMap z) := by
  obtain ⟨c, hc⟩ := h
  let z : Slots n r → ℂ := fun s =>
    if s.2.1 = 0 then c (Sum.inl s.1, Sum.inl s.2.2)
    else if s.2.1 = 1 then c (Sum.inl s.1, Sum.inr (Sum.inl s.2.2))
    else c (Sum.inl s.1, Sum.inr (Sum.inr s.2.2))
  refine ⟨z, ?_⟩
  have hle : SpanC c ≤ LinearMap.range (tangentMap z).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨col, rfl⟩
    rcases col with ⟨p | e, i⟩ | ⟨p | e, j⟩ | ⟨p | e, k⟩
    · refine ⟨Pi.single (p, 0, i) 1, ?_⟩
      funext t
      simp only [ContinuousLinearMap.coe_coe, tangentMap_apply]
      rw [Fintype.sum_eq_single p]
      · simp [gens, gen1, vvec, wvec, pt1, z, Pi.single_apply]
        split_ifs <;> simp_all [mul_comm]
      · intro q hq
        simp [hq]
    · exact e.elim0
    · refine ⟨Pi.single (p, 1, j) 1, ?_⟩
      funext t
      simp only [ContinuousLinearMap.coe_coe, tangentMap_apply]
      rw [Fintype.sum_eq_single p]
      · simp [gens, gen2, uvec, wvec, pt2, z, Pi.single_apply]
        split_ifs <;> simp_all [mul_comm]
      · intro q hq
        simp [hq]
    · exact e.elim0
    · refine ⟨Pi.single (p, 2, k) 1, ?_⟩
      funext t
      simp only [ContinuousLinearMap.coe_coe, tangentMap_apply]
      rw [Fintype.sum_eq_single p]
      · simp [gens, gen3, uvec, vvec, pt3, z, Pi.single_apply]
      · intro q hq
        simp [hq]
    · exact e.elim0
  intro y
  have hy : y ∈ LinearMap.range (tangentMap z).toLinearMap := hle (by rw [hc]; trivial)
  exact hy

theorem bar (m : ℕ) : Fills 9 (m + 9) 9 27 (3 * m + 2) 0 (3 * m + 4) :=
  bar_all cBar9 cBar10 cBar11 cZP99 m

/-- Lickteig's theorem: from side nine on the tangent spaces at the predicted number of
points span the space of all cubic tensors. -/
theorem fullTangents_ge_nine (n : ℕ) (hn : 9 ≤ n) : FullTangents n := by
  apply fullTangents_of_fills
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 9 ∧ n = 9 * q + r :=
    ⟨n / 9, n % 9, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod n 9).symm⟩
  interval_cases r
  · obtain rfl | hq : q = 1 ∨ 2 ≤ q := by omega
    · exact cCube9.cast rfl rfl rfl (by decide) rfl rfl rfl
    · obtain ⟨k, rfl⟩ : ∃ k, q = k + 2 := ⟨q - 2, by omega⟩
      exact (cube_uniform bar cZ29 9 30 26 rfl cSpHead9 cSRBase9 cSRPlate9 cZCss9 cQSS9 k).cast (by omega) (by omega) (by omega)
        (by rw [show 9 * (k + 2) + 0 = 9 * k + 9 + 9 by omega, predicted_r9]) rfl rfl rfl
  · obtain rfl | hq : q = 1 ∨ 2 ≤ q := by omega
    · exact cCube10.cast rfl rfl rfl (by decide) rfl rfl rfl
    · obtain ⟨j, rfl⟩ : ∃ j, q = j + 2 := ⟨q - 2, by omega⟩
      exact (cube_one bar cSlab9Base cZeroBarBase cSRPlate9 cABar10Base cZBar10Base cPlate9910
        cCube10 j).cast (by omega) (by omega) (by omega)
        (by rw [show 9 * (j + 2) + 1 = 9 * j + 19 by omega, predicted_r1]) rfl rfl rfl
  · obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    exact (cube_uniform bar cZ29 2 2 5 rfl cSpHead2 cSRBase2 cSRPlate2 cZCss2 cQSS2 k).cast (by omega) (by omega) (by omega)
      (by rw [show 9 * (k + 1) + 2 = 9 * k + 9 + 2 by omega, predicted_r2]) rfl rfl rfl
  · obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    exact (cube_uniform bar cZ29 3 4 8 rfl cSpHead3 cSRBase3 cSRPlate3 cZCss3 cQSS3 k).cast (by omega) (by omega) (by omega)
      (by rw [show 9 * (k + 1) + 3 = 9 * k + 9 + 3 by omega, predicted_r3]) rfl rfl rfl
  · obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    exact (cube_uniform bar cZ29 4 7 11 rfl cSpHead4 cSRBase4 cSRPlate4 cZCss4 cQSS4 k).cast (by omega) (by omega) (by omega)
      (by rw [show 9 * (k + 1) + 4 = 9 * k + 9 + 4 by omega, predicted_r4]) rfl rfl rfl
  · obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    exact (cube_uniform bar cZ29 5 10 14 rfl cSpHead5 cSRBase5 cSRPlate5 cZCss5 cQSS5 k).cast (by omega) (by omega) (by omega)
      (by rw [show 9 * (k + 1) + 5 = 9 * k + 9 + 5 by omega, predicted_r5]) rfl rfl rfl
  · obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    exact (cube_uniform bar cZ29 6 14 17 rfl cSpHead6 cSRBase6 cSRPlate6 cZCss6 cQSS6 k).cast (by omega) (by omega) (by omega)
      (by rw [show 9 * (k + 1) + 6 = 9 * k + 9 + 6 by omega, predicted_r6]) rfl rfl rfl
  · obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    exact (cube_uniform bar cZ29 7 19 20 rfl cSpHead7 cSRBase7 cSRPlate7 cZCss7 cQSS7 k).cast (by omega) (by omega) (by omega)
      (by rw [show 9 * (k + 1) + 7 = 9 * k + 9 + 7 by omega, predicted_r7]) rfl rfl rfl
  · obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    exact (cube_uniform bar cZ29 8 24 23 rfl cSpHead8 cSRBase8 cSRPlate8 cZCss8 cQSS8 k).cast (by omega) (by omega) (by omega)
      (by rw [show 9 * (k + 1) + 8 = 9 * k + 9 + 8 by omega, predicted_r8]) rfl rfl rfl

end final

end OMA.Cube

/-- Lickteig's theorem on the generic rank of cubic tensors of size other than three. -/
theorem OMA.solution : type_of% @Arxiv.«0805.3777».isGenericRank_cube := by
  intro n hn hn3
  by_cases hlarge : 9 ≤ n
  · exact OMA.Cube.generic_of_tangents hn (OMA.Cube.fullTangents_ge_nine n hlarge)
  · exact OMA.Cube.generic_rank_le_eight hn hn3 (by omega)
