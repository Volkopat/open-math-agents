import OMAStatements.S_mo_514879
import Mathlib

/-!
# Degree of a polynomial defined by a product over all sign choices

Source: https://mathoverflow.net/questions/514879
Credit: @rleshner

Successive quadratic norms construct the sign product as a polynomial `Q(t,y)`.
In Laurent series at infinity, `t + sqrt(t²-a)` has order `-1`. Its conjugate has
order `1` because their product is `a`. A choice of `j` minus signs therefore gives
a factor of order `min 0 (2*j-n)`. The two candidate orders are distinct for odd `n`.
Summing these orders gives `-n * choose (n-1) ((n-1)/2)`. Multiplication of `t`
by a primitive root rotates the radicands, so only powers divisible by `n` occur in `Q`.
-/

open Polynomial Finset
open scoped LaurentSeries PowerSeries

noncomputable section

local instance (n : ℕ) [NeZero n] : Fintype (rootsOfUnity n ℂ) := Fintype.ofFinite _


universe u v
private def splitHom {R : Type u} {K : Type v} [CommRing R] [CommRing K]
    (f : R →+* K) {d : R} (r : K) (h : r ^ 2 = f d) : QuadraticAlgebra R d 0 →+* K where
  toFun z := f z.re + f z.im * r
  map_one' := by change f 1 + f 0 * r = 1; simp
  map_zero' := by change f 0 + f 0 * r = 0; simp
  map_add' x y := by simp [QuadraticAlgebra.re_add, QuadraticAlgebra.im_add]; ring
  map_mul' x y := by simp [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul, ← h]; ring

private theorem split_norm {R : Type u} {K : Type v} [CommRing R] [CommRing K]
    (f : R →+* K) {d : R} (r : K) (h : r ^ 2 = f d) (z : QuadraticAlgebra R d 0) :
    f z.norm = splitHom f r h z * splitHom f (-r) (by simpa using h) z := by
  simp [QuadraticAlgebra.norm_def, splitHom, ← h]; ring

private theorem split_base {R : Type u} {K : Type v} [CommRing R] [CommRing K]
    (f : R →+* K) {d : R} (r : K) (h : r ^ 2 = f d) (a : R) :
    splitHom f r h (algebraMap R (QuadraticAlgebra R d 0) a) = f a := by simp [splitHom]

private theorem split_w {R : Type u} {K : Type v} [CommRing R] [CommRing K]
    (f : R →+* K) {d : R} (r : K) (h : r ^ 2 = f d) :
    splitHom f r h QuadraticAlgebra.omega = r := by simp [splitHom, QuadraticAlgebra.omega]

/-- Pairing the two signs of each radical is the norm in its quadratic algebra. -/
private theorem exists_tower {ι : Type} [DecidableEq ι] (s : Finset ι) :
    ∀ (R : Type) [CommRing R] (t y a : R) (d : ι → R), ∃ b : R,
      ∀ (K : Type) [CommRing K] (f : R →+* K) (r : ι → K),
      (∀ i ∈ s, r i ^ 2 = f (d i)) →
      f b = ∏ z ∈ s.powerset, (f y - f a * ∏ i ∈ s,
        (if i ∈ z then f t - r i else f t + r i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => intro R _ t y a d; exact ⟨y - a, by simp⟩
  | @insert i s hi ih =>
    intro R _ t y a d
    let S := QuadraticAlgebra R (d i) 0
    let g := algebraMap R S
    obtain ⟨b, hb⟩ := ih S (g t) (g y) (g a * (g t + QuadraticAlgebra.omega)) (g ∘ d)
    refine ⟨b.norm, ?_⟩
    intro K _ f r h
    have hr := h i (mem_insert_self ..)
    have hneg : (-r i) ^ 2 = f (d i) := by simpa using hr
    rw [split_norm f (r i) hr, Finset.prod_powerset_insert hi]
    have he (u : K) (hu : u ^ 2 = f (d i)) : ∀ j ∈ s,
        r j ^ 2 = splitHom f u hu ((g ∘ d) j) := by
      intro j hj; simpa [Function.comp_def, g, S, split_base] using h j (mem_insert_of_mem hj)
    rw [hb K (splitHom f (r i) hr) r (he _ _), hb K (splitHom f (-r i) hneg) r (he _ _)]
    simp only [map_mul, map_add, g, S, split_base, split_w, Finset.prod_insert hi, ← mul_assoc]
    congr 1
    · apply prod_congr rfl; intro z hz
      have hni : i ∉ z := fun hiz => hi ((mem_powerset.mp hz) hiz)
      simp [hni]
    · apply prod_congr rfl; intro z hz
      simp only [mem_insert_self, ↓reduceIte, sub_eq_add_neg]
      congr 2
      congr 1
      apply prod_congr rfl; intro j hj
      have hji : j ≠ i := fun hji => hi (hji ▸ hj)
      simp [hji]


private abbrev A := Polynomial ℂ
private abbrev L := LaurentSeries A
private def T : L := HahnSeries.single (-1) 1
private def c : A →+* L := HahnSeries.C
/-- The binomial series for the square root of `1 - a z²`, with constant coefficient one. -/
private def normRoot (a : A) : PowerSeries A :=
  PowerSeries.expand 2 (by decide) (PowerSeries.rescale (-a) (PowerSeries.binomialSeries A (1/2 : ℚ)))
private theorem normRoot_sq (a : A) : (normRoot a)^2 = 1 - PowerSeries.C a * PowerSeries.X^2 := by
  have h : (PowerSeries.binomialSeries A (1/2 : ℚ))^2 = 1 + PowerSeries.X := by
    rw [pow_two, ← PowerSeries.binomialSeries_add, show (1/2:ℚ)+1/2 = 1 by norm_num]
    simpa using PowerSeries.binomialSeries_nat (A := A) (R := ℚ) 1
  rw [normRoot, ← map_pow, ← map_pow, h]
  simp [PowerSeries.rescale_X, PowerSeries.expand_X, sub_eq_add_neg]
  rw [← PowerSeries.monomial_zero_eq_C_apply a, PowerSeries.expand_monomial]
private theorem normRoot_zero (a : A) : (normRoot a).constantCoeff = 1 := by
  rw [normRoot, PowerSeries.constantCoeff_expand, ← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_rescale]
  simp
private theorem series_unit_order (p : PowerSeries A) (hp : p.constantCoeff ≠ 0) :
    ((p : L)).orderTop = 0 := by
  apply le_antisymm
  · apply HahnSeries.orderTop_le_of_coeff_ne_zero
    change (p : L).coeff (0 : ℤ) ≠ 0
    rw [PowerSeries.coeff_coe]; simpa using hp
  · apply HahnSeries.le_orderTop_iff_forall.mpr
    intro i hi
    rw [PowerSeries.coeff_coe, if_pos (by exact_mod_cast hi)]
private def rootAt (a : A) : L := T * (normRoot a : L)
private theorem T_sq_cancel : T ^ 2 * ((PowerSeries.X : PowerSeries A) : L)^2 = 1 := by
  simp [T, HahnSeries.single_pow, HahnSeries.single_mul_single,
    ← HahnSeries.C_apply]
private theorem rootAt_sq (a : A) : (rootAt a)^2 = T^2 - c a := by
  have h := congrArg (HahnSeries.ofPowerSeries ℤ A) (normRoot_sq a)
  simp only [map_pow, map_sub, map_one, map_mul, HahnSeries.ofPowerSeries_C] at h
  rw [rootAt, mul_pow]
  change T ^ 2 * ((HahnSeries.ofPowerSeries ℤ A) (normRoot a) ^ 2) = _
  rw [h, mul_sub, mul_one]
  apply congrArg (fun w : L => T ^ 2 - w)
  change T ^ 2 * (c a * ((PowerSeries.X : PowerSeries A) : L)^2) = c a
  rw [mul_left_comm, T_sq_cancel, mul_one]
private theorem rootAt_orders (a : A) (ha : a ≠ 0) :
    (T + rootAt a).orderTop = ((-1 : ℤ) : WithTop ℤ) ∧
    (T - rootAt a).orderTop = ((1 : ℤ) : WithTop ℤ) := by
  have hplus : T + rootAt a = T * (((1 + normRoot a : PowerSeries A) : L)) := by
    change T + T * _ = T * (HahnSeries.ofPowerSeries ℤ A _); rw [map_add, map_one]; ring
  have h0 : (1 + normRoot a).constantCoeff ≠ 0 := by simp [normRoot_zero]
  have hp : (T + rootAt a).orderTop = ((-1 : ℤ) : WithTop ℤ) := by
    rw [hplus, HahnSeries.orderTop_mul, series_unit_order _ h0, add_zero]
    exact HahnSeries.orderTop_single one_ne_zero
  refine ⟨hp, ?_⟩
  have he : (T + rootAt a) * (T - rootAt a) = c a := by
    calc _ = T ^ 2 - (rootAt a)^2 := by ring
         _ = _ := by rw [rootAt_sq]; ring
  have he' := congrArg HahnSeries.orderTop he
  rw [HahnSeries.orderTop_mul,hp, show (c a).orderTop = 0 from HahnSeries.orderTop_single ha] at he'
  cases hq : (T - rootAt a).orderTop with
  | top => simp [hq] at he'
  | coe q =>
    rw [hq, ← WithTop.coe_add] at he'
    have hq' : (-1 : ℤ) + q = 0 := by exact_mod_cast he'
    norm_cast; omega

/-- Evaluate at `b/z`. The Laurent coefficient at `-j` recovers the polynomial coefficient at `j`, multiplied by `b^j`. -/
private def evalInf (b : A) : A[X] →+* L := eval₂RingHom HahnSeries.C (HahnSeries.single (-1) b)
private theorem evalInf_sum (b : A) (Q : A[X]) : evalInf b Q =
    ∑ i ∈ Q.support, HahnSeries.single (-(i : ℤ)) (Q.coeff i * b^i) := by
  change Q.eval₂ HahnSeries.C (HahnSeries.single (-1) b) = _
  rw [eval₂_eq_sum, Polynomial.sum]
  apply sum_congr rfl; intro i hi
  simp [HahnSeries.C_apply, HahnSeries.single_pow, HahnSeries.single_mul_single]
private theorem evalInf_coeff (b : A) (Q : A[X]) (j : ℕ) :
    (evalInf b Q).coeff (-(j:ℤ)) = Q.coeff j * b^j := by
  rw [evalInf_sum, HahnSeries.coeff_sum]
  have he (i : ℕ) : (-(j:ℤ)) = -(i:ℤ) ↔ j=i := by omega
  simp [HahnSeries.coeff_single, he, eq_comm (a:=j), Finset.sum_ite_eq', mem_support_iff]; tauto
private theorem degree_order (Q : A[X]) (hQ : Q ≠ 0) :
    (evalInf 1 Q).orderTop = ((-(Q.natDegree : ℤ)) : WithTop ℤ) := by
  apply le_antisymm
  · apply HahnSeries.orderTop_le_of_coeff_ne_zero
    simpa [evalInf_coeff, coeff_natDegree] using leadingCoeff_ne_zero.mpr hQ
  · apply HahnSeries.le_orderTop_iff_forall.mpr; intro j hj
    rw [evalInf_sum, HahnSeries.coeff_sum]
    apply sum_eq_zero; intro i hi
    have hi' := le_natDegree_of_ne_zero (mem_support_iff.mp hi)
    apply HahnSeries.coeff_single_of_ne
    have hj' : j < -(Q.natDegree:ℤ) := by exact_mod_cast hj
    omega

private theorem orderProd {ι : Type*} (s : Finset ι) (f : ι → L) :
    (∏ i ∈ s, f i).orderTop = ∑ i ∈ s, (f i).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih => simp [hi, HahnSeries.orderTop_mul, ih]
private theorem orderProd_int {ι : Type*} (s : Finset ι) (f : ι → L) (q : ι → ℤ)
    (hq : ∀ i ∈ s, (f i).orderTop = (q i : WithTop ℤ)) :
    (∏ i ∈ s, f i).orderTop = ((∑ i ∈ s, q i : ℤ) : WithTop ℤ) := by
  rw [orderProd]; push_cast; exact sum_congr rfl hq
/-- Odd cardinality prevents cancellation between the term of order zero and the signed product. -/
private theorem factor_order {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (hn : Fintype.card ι = 2*k+1) (y : L) (hy : y.orderTop = 0) (t : L) (r : ι → L)
    (hr : ∀ i, (t+r i).orderTop = ((-1:ℤ) : WithTop ℤ) ∧ (t-r i).orderTop = ((1:ℤ) : WithTop ℤ))
    (s : Finset ι) :
    (y - ∏ i, if i ∈ s then t-r i else t+r i).orderTop =
    ((min 0 (2 * s.card - (2*k+1:ℕ) : ℤ)) : WithTop ℤ) := by
  have hp : (∏ i, if i ∈ s then t-r i else t+r i).orderTop =
      ((2 * s.card - (2*k+1:ℕ) : ℤ) : WithTop ℤ) := by
    rw [orderProd_int _ _ (fun i => if i ∈ s then (1:ℤ) else -1) (by
      intro i _; by_cases h : i ∈ s <;> simp [h, (hr i).1, (hr i).2])]
    congr 1
    rw [sum_ite]
    have hc : univ.filter (fun x => x ∉ s) = sᶜ := by ext; simp
    simp [hc, Finset.card_compl, hn]
    have h := s.card_le_univ; rw [hn] at h; omega
  have ha : (2 * s.card - (2*k+1:ℕ) : ℤ) ≠ 0 := by omega
  by_cases h : 0 < (2 * s.card - (2*k+1:ℕ) : ℤ)
  · rw [min_eq_left (by exact_mod_cast h.le), HahnSeries.orderTop_sub (by rw [hy,hp]; exact_mod_cast h), hy]
  · have h' : (2 * s.card - (2*k+1:ℕ) : ℤ) < 0 := by omega
    rw [min_eq_right (by exact_mod_cast h'.le)]
    calc _ = (-(y - ∏ i, if i ∈ s then t-r i else t+r i)).orderTop := HahnSeries.orderTop_neg.symm
         _ = _ := by rw [neg_sub, HahnSeries.orderTop_sub (by rw [hy,hp]; exact_mod_cast h'), hp]

/-- The weighted binomial sum telescopes by the two neighboring Pascal identities. -/
private theorem partial_choose (N m : ℕ) (hm : m ≤ N) :
    ∑ j ∈ range (m+1), ((N+1).choose j : ℤ) * ((N:ℤ)+1-2*j) =
      ((N:ℤ)+1) * N.choose m := by
  induction m with
  | zero => simp
  | succ j ih =>
    rw [sum_range_succ, ih (by omega)]
    have h1 := Nat.choose_mul_succ_eq N (j+1)
    have h2 := Nat.add_one_mul_choose_eq N j
    zify [show j+1 ≤ N+1 by omega] at h1 h2
    push_cast; nlinarith
private theorem sum_negative {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (hn : Fintype.card ι = 2*k+1) :
    ∑ s : Finset ι, min (0:ℤ) (2 * s.card - (2*k+1:ℕ)) =
      - ((2*k+1:ℕ) : ℤ) * (2*k).choose k := by
  classical
  rw [← powerset_univ (α := ι), sum_powerset_apply_card (fun j => min (0:ℤ) (2*j - (2*k+1:ℕ)))]
  simp only [card_univ, hn, nsmul_eq_mul]
  rw [← sum_range_add_sum_Ico _ (show k+1 ≤ 2*k+1+1 by omega)]
  have hz : ∑ j ∈ Ico (k+1) (2*k+1+1), ((2*k+1).choose j : ℤ) * min (0:ℤ) (2*j-(2*k+1:ℕ)) = 0 := by
    apply sum_eq_zero; intro j hj; rw [mem_Ico] at hj; rw [min_eq_left (by omega), mul_zero]
  rw [hz, add_zero]
  have hh := partial_choose (2*k) k (by omega)
  push_cast at hh ⊢
  rw [neg_mul, ← hh, ← sum_neg_distrib]
  apply sum_congr rfl; intro j hj
  rw [mem_range] at hj
  rw [min_eq_right (by omega)]; ring

private theorem rotate {ι K : Type*} [Fintype ι] [DecidableEq ι] [CommRing K]
    (e : ι ≃ ι) (t y b : K) (hb : b ^ Fintype.card ι = 1) (r : ι → K) :
    (∏ s : Finset ι, (y - ∏ i, if i ∈ s then b*t - b*r (e.symm i) else b*t + b*r (e.symm i))) =
    (∏ s : Finset ι, (y - ∏ i, if i ∈ s then t-r i else t+r i)) := by
  symm
  apply Fintype.prod_equiv (e.finsetCongr) _ _
  intro s
  congr 1
  calc
    _ = ∏ i, b * (if i ∈ s then t-r i else t+r i) := by rw [prod_mul_distrib]; simp [hb]
    _ = _ := by
      apply Fintype.prod_equiv e _ _; intro i
      simp [Equiv.finsetCongr, mul_ite, mul_sub, mul_add]
private theorem sparse_contract {R : Type*} [CommSemiring R] (n : ℕ) (hn : n ≠ 0) (Q : R[X])
    (h : ∀ j, ¬ n ∣ j → Q.coeff j = 0) : expand R n (Q.contract n) = Q := by
  ext j
  rw [coeff_expand (Nat.pos_of_ne_zero hn), coeff_contract hn]
  split_ifs with hh
  · rw [Nat.div_mul_cancel hh]
  · exact (h _ hh).symm
private theorem universal {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → A) :
    ∃ Q : A[X], ∀ (K : Type) [CommRing K] (f : A →+* K) (t : K) (r : ι → K),
      (∀ i, r i ^ 2 = t ^ 2 - f (w i)) → Q.eval₂ f t =
      ∏ s : Finset ι, (f X - ∏ i, if i ∈ s then t - r i else t + r i) := by
  obtain ⟨Q, hQ⟩ := exists_tower (univ : Finset ι) A[X] X (C X) 1 (fun i => X^2 - C (w i))
  use Q; intro K _ f t r hr
  have h := hQ K (eval₂RingHom f t) r (by intro i _; simpa [eval₂_sub, eval₂_pow] using hr i)
  simpa using h

private theorem degree_universal {ι : Type} [Fintype ι] [DecidableEq ι] (w : ι → A)
    (hw : ∀ i, w i ≠ 0) (k : ℕ) (hk : Fintype.card ι = 2*k+1) (Q : A[X])
    (hQ : Q.eval₂ c T = ∏ s : Finset ι, (c X - ∏ i, if i ∈ s then T - rootAt (w i) else T + rootAt (w i))) :
    Q.natDegree = (2*k+1)*(2*k).choose k := by
  have hO : (evalInf 1 Q).orderTop = ((-((2*k+1:ℕ):ℤ) * (2*k).choose k : ℤ) : WithTop ℤ) := by
    change (Q.eval₂ c T).orderTop = _
    rw [hQ, orderProd_int _ _ (fun s => min (0:ℤ) (2*s.card-(2*k+1:ℕ))) (by
      intro s _; exact factor_order k hk _ (HahnSeries.orderTop_single X_ne_zero) _ _ (fun i => rootAt_orders _ (hw i)) s), sum_negative k hk]
  have hn : Q ≠ 0 := by
    intro hz
    rw [hz, map_zero, HahnSeries.orderTop_zero] at hO
    exact WithTop.top_ne_coe hO
  rw [degree_order Q hn] at hO
  have h := WithTop.coe_injective hO
  exact_mod_cast (show (Q.natDegree : ℤ) = ((2*k+1:ℕ):ℤ) * (2*k).choose k by linarith)

/-- Rotating the radicands by the square of a primitive root fixes the product. -/
private theorem descent {n : ℕ} [NeZero n] [Fintype (rootsOfUnity n ℂ)]
    (hn : Fintype.card (rootsOfUnity n ℂ) = n) (Q : A[X])
    (hQ : ∀ (t : L) (r : rootsOfUnity n ℂ → L),
      (∀ i, r i ^ 2 = t ^ 2 - c (C (i.val : ℂ))) → Q.eval₂ c t =
      ∏ s : Finset (rootsOfUnity n ℂ), (c X - ∏ i, if i ∈ s then t - r i else t + r i)) :
    expand A n (Q.contract n) = Q := by
  classical
  let ζ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hz : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp _ NeZero.out
  let u := hz.toRootsOfUnity
  let e : rootsOfUnity n ℂ ≃ rootsOfUnity n ℂ := Equiv.mulLeft (u ^ 2)
  let w (i : rootsOfUnity n ℂ) : A := C (i.val : ℂ)
  let r (i : rootsOfUnity n ℂ) := rootAt (w i)
  let b : L := c (C ζ)
  have hb : b ^ Fintype.card (rootsOfUnity n ℂ) = 1 := by rw [hn]; simp [b, ← map_pow, hz.pow_eq_one]
  have he (i : rootsOfUnity n ℂ) : b ^ 2 * c (w i) = c (w (e i)) := by
    change c (C ζ) ^ 2 * c (C (i.val : ℂ)) = c (C (((u ^ 2 * i).val : ℂˣ) : ℂ))
    rw [← map_pow, ← map_mul, ← map_pow, ← map_mul]
    rfl
  have hs (i : rootsOfUnity n ℂ) : (b * r (e.symm i)) ^ 2 = (b*T)^2 - c (w i) := by
    simp only [mul_pow, r, rootAt_sq, mul_sub, he, Equiv.apply_symm_apply]
  have h := (hQ (b*T) (fun i => b*r (e.symm i)) hs).trans <|
    (rotate e T (c X) b hb r).trans (hQ T r (fun i => rootAt_sq _)).symm
  have ht : b*T = HahnSeries.single (-1) (C ζ) := by simp [b, c, T, HahnSeries.C_apply, HahnSeries.single_mul_single]
  rw [ht] at h
  change evalInf (C ζ) Q = evalInf 1 Q at h
  apply sparse_contract n NeZero.out Q
  intro j hj
  have hh := congrArg (fun z : L => z.coeff (-(j:ℤ))) h
  simp only [evalInf_coeff, one_pow, mul_one] at hh
  by_contra hc
  have hp : (C ζ : A)^j = 1 := mul_left_cancel₀ hc (hh.trans (mul_one _).symm)
  have hzj : ζ^j = 1 := C_injective (by rw [map_pow, hp, map_one])
  exact hj (hz.dvd_of_pow_eq_one _ hzj)

theorem OMA.solution : type_of% @OMA.S_mo_514879.main := by
  classical
  intro k
  let n := 2*k+1
  let U := rootsOfUnity n ℂ
  have hn : Fintype.card U = n := by rw [← Nat.card_eq_fintype_card]; exact Complex.card_rootsOfUnity _
  let w (i : U) : A := C (i.val : ℂ)
  obtain ⟨Q, hQ⟩ := universal w
  have hd := degree_universal w (fun i => C_ne_zero.mpr i.val.ne_zero) k hn Q (hQ L c T _ (fun i => rootAt_sq _))
  have he := descent hn Q (hQ L c)
  refine ⟨Q.contract n, ?_, ?_⟩
  · have hdeg := congrArg natDegree he
    rw [natDegree_expand, hd] at hdeg
    dsimp [n] at hdeg; nlinarith
  · intro t y r hr
    have h := hQ ℂ (evalRingHom y) t r (by intro i; simpa [w] using hr i)
    rw [← he, expand_eq_comp_X_pow, eval₂_comp, eval₂_pow, eval₂_X] at h
    simpa [n, U] using h

end

