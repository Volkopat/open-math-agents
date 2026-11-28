import FormalConjectures.ErdosProblems.«1109»
import Mathlib

/-!
# A spacing reduction for Konyagin's squarefree sumset bound

We sample the exponential sum of the set at all nonzero prime-square fractions.
Squarefreeness makes the sum of the complex squares vanish when the zero
frequency is included. Thus each prime contributes at least the square of the
cardinality to the nonzero-frequency energy.

Keep three frequencies per interval of length 1/M. Each discarded frequency
determines a different close quadruple, and the retained points split into six
separated classes. Following S. V. Konyagin, "Problems on the set of squarefree numbers" (2004),
Lemma 2, we count the six minors by their Plücker relation and the divisor
bound. For fixed minors the prime denominators determine the numerators.
The remaining arithmetic input counts prime points on two diagonal quadrics.
The analytic input is the ordinary large sieve for separated points.

Credit: @yuka30240
-/

namespace OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R2

open Filter Finset
open scoped Pointwise

/-- Fixed-coefficient prime quadruples in the corollary of Bombieri and
Zannier, "On the number of rational points on certain elliptic curves" (2004).
Only coefficient sizes that occur as minors of the sampled points are needed. -/
def H1 : Prop :=
  ∀ η : ℝ, 0 < η → ∀ᶠ X : ℕ in atTop, ∀ D : Fin 4 → Fin 4 → ℤ,
    (∀ i j, D i j = -D j i ∧ (D i j).natAbs ≤ X^4) →
    (∀ i j, i ≠ j → D i j ≠ 0) → ∀ U : Finset (Fin 4 → ℕ),
    (∀ p ∈ U, Function.Injective p ∧ (∀ i, (p i).Prime ∧ p i ≤ X) ∧
      ∀ i j k, (p i : ℤ)^2 * D j k - (p j : ℤ)^2 * D i k + (p k : ℤ)^2 * D i j = 0) →
    (U.card : ℝ) ≤ (X : ℝ)^η

/-- Classical large sieve for the indicator of a set and circle-separated
sample points. The constant eight suffices by the discrete Fejér kernel. -/
def H2 : Prop :=
  ∀ (J : Finset (ℕ × ℕ)) (M : ℕ), 0 < M → ∀ A ⊆ Icc 1 M, ∀ α : ℕ × ℕ → ℝ,
    (∀ x ∈ J, 0 < α x ∧ α x < 1) →
    (∀ x ∈ J, ∀ y ∈ J, x ≠ y →
      1 / (M : ℝ) ≤ |α x - α y| ∧ 1 / (M : ℝ) ≤ 1 - |α x - α y|) →
    ∑ x ∈ J, ‖∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * ↑(α x * a))‖ ^ 2 ≤
      8 * (M : ℝ) * A.card

/-- Number the points in each bin. The first three receive colours. Each
subsequent point, together with the first three, gives a distinct quadruple. -/
lemma pack_bins {ι : Type*} [DecidableEq ι] (J : Finset ι) (bin : ι → ℕ) :
    ∃ (B : Finset ι) (color : ι → ℕ) (T : Finset (Fin 4 → ι)),
      B ⊆ J ∧ B.card ≤ T.card ∧
      (∀ t ∈ T, Function.Injective t ∧ ∀ i, t i ∈ J ∧ bin (t i) = bin (t 0)) ∧
      (∀ u ∈ J \ B, color u < 3) ∧
      ∀ u ∈ J \ B, ∀ v ∈ J \ B, bin u = bin v → color u = color v → u = v := by
  classical
  let fiber (k : ℕ) := J.filter (fun u => bin u = k)
  let rank (k : ℕ) := Fintype.equivFin ↥(fiber k)
  let number (k : ℕ) (u : ι) := if h : u ∈ fiber k then (rank k ⟨u,h⟩).val else 0
  let color (u : ι) := number (bin u) u
  have own {u : ι} (hu : u ∈ J) : u ∈ fiber (bin u) := mem_filter.mpr ⟨hu,rfl⟩
  let B := J.filter (fun u => 3 ≤ color u)
  have witness (u : ι) (hu : u ∈ B) :
      ∃ t : Fin 4 → ι, t 3 = u ∧ Function.Injective t ∧
        ∀ i, t i ∈ J ∧ bin (t i) = bin (t 0) := by
    obtain ⟨huJ, hu3⟩ := mem_filter.mp hu
    let k := bin u
    let r := rank k ⟨u,own huJ⟩
    have hr : 3 ≤ r.val := by simpa [color,number,own huJ,r,k] using hu3
    let ix (i : Fin 4) : Fin (Fintype.card ↥(fiber k)) :=
      if i.val < 3 then ⟨i.val, by omega⟩ else r
    have hix : Function.Injective ix := by
      intro i j hij
      have he := congrArg Fin.val hij
      dsimp [ix] at he
      split_ifs at he <;> apply Fin.ext <;> simp_all <;> omega
    let t (i : Fin 4) : ι := ((rank k).symm (ix i)).val
    have ht (i : Fin 4) := mem_filter.mp ((rank k).symm (ix i)).property
    refine ⟨t, ?_, ?_, fun i => ⟨(ht i).1, (ht i).2.trans (ht 0).2.symm⟩⟩
    · simp [t,ix,r]
    · intro i j he
      exact hix ((rank k).symm.injective (Subtype.ext he))
  choose w hw using witness
  let T := B.attach.image (fun u => w u.val u.property)
  refine ⟨B,color,T, filter_subset _ _, ?_, ?_, ?_, ?_⟩
  · have hi : Function.Injective (fun u : ↥B => w u.val u.property) := by
      intro u v he
      apply Subtype.ext
      exact (hw u.val u.property).1.symm.trans
        ((congrFun he 3).trans (hw v.val v.property).1)
    simp [T,card_image_of_injective _ hi]
  · intro t ht
    obtain ⟨u,_,rfl⟩ := mem_image.mp ht
    exact (hw u.val u.property).2
  · intro u hu
    obtain ⟨hin,hout⟩ := mem_sdiff.mp hu
    exact lt_of_not_ge (fun h => hout (mem_filter.mpr ⟨hin,h⟩))
  · intro u hu v hv hb hc
    have hu' := own (mem_sdiff.mp hu).1
    have hv' : v ∈ fiber (bin u) := mem_filter.mpr ⟨(mem_sdiff.mp hv).1,hb.symm⟩
    change number (bin u) u = number (bin v) v at hc
    rw [← hb] at hc
    simp only [number,dif_pos hu',dif_pos hv'] at hc
    exact congrArg Subtype.val ((rank _).injective (Fin.ext hc))

-- These two divisor estimates are adapted from @mattdorman, open-math-agents
-- commit 31c7aaa8a168df5860b5e00b8ec84bb8a9d104d0, based on OpenAI math
-- commit adc7f1241b42e322a6451854ab7e4b4c146bf78a under Apache-2.0.
private theorem succ_le_geometric (r : ℝ) (hr : 1 < r) (a : ℕ) :
    (a : ℝ) + 1 ≤ (1 + (r - 1)⁻¹) * r ^ a := by
  have h₁ := a.cast_le_pow_div_sub hr
  have h₂ : (1 : ℝ) ≤ r ^ a := one_le_pow₀ hr.le
  calc
    (a : ℝ) + 1 ≤ r ^ a / (r - 1) + r ^ a := add_le_add h₁ h₂
    _ = (1 + (r - 1)⁻¹) * r ^ a := by ring

private theorem divisors_card_le_rpow (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, (n.divisors.card : ℝ) ≤ C * (n : ℝ) ^ ε := by
  let r : ℝ := (2 : ℝ) ^ ε
  have hr : 1 < r := Real.one_lt_rpow (by norm_num) hε
  let c : ℝ := 1 + (r - 1)⁻¹
  have hc : 1 ≤ c := by
    have hh : 0 ≤ (r - 1)⁻¹ := inv_nonneg.mpr (sub_nonneg.mpr hr.le)
    dsimp [c]
    linarith
  have hc0 : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have ht : Tendsto (fun p : ℕ => (p : ℝ) ^ ε) atTop atTop :=
    (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop (2 : ℝ)))
  refine ⟨c ^ N, pow_pos hc0 _, ?_⟩
  intro n
  by_cases hn : n = 0
  · simp [hn, Real.zero_rpow hε.ne']
  have hfactor (p : ℕ) (hp : p ∈ n.primeFactors) :
      (n.factorization p : ℝ) + 1 ≤
        (if p < N then c else 1) * ((p : ℝ) ^ ε) ^ n.factorization p := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    by_cases hsmall : p < N
    · rw [if_pos hsmall]
      exact (succ_le_geometric r hr _).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (Real.rpow_le_rpow (by norm_num) hp2 hε.le) _)
        hc0.le)
    · rw [if_neg hsmall, one_mul]
      have hh : (n.factorization p : ℝ) + 1 ≤ (2 : ℝ) ^ n.factorization p := by
        exact_mod_cast Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := n.factorization p))
      exact hh.trans (pow_le_pow_left₀ (by norm_num) (hN p (Nat.le_of_not_gt hsmall)) _)
  have hconstant : (∏ p ∈ n.primeFactors, if p < N then c else 1) ≤ c ^ N := by
    rw [Finset.prod_ite]
    simp only [Finset.prod_const_one, mul_one, Finset.prod_const]
    apply pow_le_pow_right₀ hc
    exact (Finset.card_le_card (show n.primeFactors.filter (fun p => p < N) ⊆
      Finset.range N from fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2)).trans
        (by rw [Finset.card_range])
  have hpowers : (∏ p ∈ n.primeFactors, ((p : ℝ) ^ ε) ^ n.factorization p) =
      (n : ℝ) ^ ε := by
    simp_rw [← Real.rpow_mul_natCast (Nat.cast_nonneg _) ε,
      mul_comm ε, Real.rpow_natCast_mul (Nat.cast_nonneg _) _ ε]
    rw [Real.finsetProd_rpow _ _ (fun _ _ => by positivity)]
    congr 1
    exact_mod_cast (Nat.prod_primeFactors_pow_factorization hn).symm
  calc
    (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn]
      push_cast
      rfl
    _ ≤ ∏ p ∈ n.primeFactors,
        (if p < N then c else 1) * ((p : ℝ) ^ ε) ^ n.factorization p :=
      Finset.prod_le_prod (fun p _ => by positivity) hfactor
    _ = (∏ p ∈ n.primeFactors, if p < N then c else 1) * (n : ℝ) ^ ε := by
      rw [Finset.prod_mul_distrib, hpowers]
    _ ≤ c ^ N * (n : ℝ) ^ ε := mul_le_mul_of_nonneg_right hconstant (by positivity)

lemma count_fibers {ι κ : Type*} [DecidableEq κ] (S : Finset ι) (f : ι → κ) (B : ℝ)
    (h : ∀ k ∈ S.image f, ((S.filter (fun u => f u = k)).card : ℝ) ≤ B) :
    (S.card : ℝ) ≤ ((S.image f).card : ℝ) * B := by
  have eq := sum_fiberwise_of_maps_to (s := S) (t := S.image f) (g := f)
    (fun i hi => mem_image_of_mem _ hi) (fun _ => (1 : ℝ))
  simp only [sum_const,nsmul_eq_mul,mul_one] at eq
  rw [← eq]
  simpa using sum_le_sum h

/-- The relation between the three complementary minor products leaves two
free products. Each of the three signed factorizations costs at most twice
the divisor count of its absolute value. -/
lemma count_patterns (η : ℝ) (hη : 0 < η) : ∀ᶠ X : ℕ in atTop,
    ∀ L : ℕ, 0 < L → L ≤ X^4 → ∀ S : Finset (Fin 4 → Fin 4 → ℤ),
    (∀ d ∈ S, (∀ i j, d i j = -d j i ∧ (d i j).natAbs ≤ L) ∧
      (∀ i j, i ≠ j → d i j ≠ 0) ∧
      d 0 1 * d 2 3 - d 0 2 * d 1 3 + d 0 3 * d 1 2 = 0) →
    (S.card : ℝ) ≤ (X : ℝ)^η * L^4 := by
  classical
  let δ := η / 48
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C,hC,τ⟩ := divisors_card_le_rpow δ hδ
  have grow := ((tendsto_rpow_atTop (half_pos hη)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop (72*C^3)
  filter_upwards [grow,eventually_ge_atTop (1 : ℕ)] with X hlarge hX
  intro L hL hLX S spec
  let factors (n : ℤ) := n.natAbs.divisors.image (fun d : ℕ => (d : ℤ)) ∪
    n.natAbs.divisors.image (fun d : ℕ => -(d : ℤ))
  have mem_factors {a b n : ℤ} (hn : n ≠ 0) (he : a*b = n) : a ∈ factors n := by
    have ha : a.natAbs ∈ n.natAbs.divisors := Nat.mem_divisors.mpr
      ⟨⟨b.natAbs,by rw [← he, Int.natAbs_mul]⟩, Int.natAbs_ne_zero.mpr hn⟩
    by_cases h : 0 ≤ a
    · exact mem_union_left _ (mem_image.mpr ⟨_,ha,Int.natAbs_of_nonneg h⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨_,ha,by rw [Int.ofNat_natAbs_of_nonpos (by omega : a ≤ 0)]; simp⟩)
  let B := 2 * C * ((X : ℝ)^8)^δ
  have factor_bound (n : ℤ) (hn : n.natAbs ≤ L^2) : ((factors n).card : ℝ) ≤ B := by
    have hc : (factors n).card ≤ 2 * n.natAbs.divisors.card :=
      (card_union_le _ _).trans (by have h1 := card_image_le (f := fun d : ℕ => (d : ℤ)) (s := n.natAbs.divisors)
                                    have h2 := card_image_le (f := fun d : ℕ => -(d : ℤ)) (s := n.natAbs.divisors)
                                    omega)
    have hnX : n.natAbs ≤ X^8 := hn.trans (by calc
      L^2 ≤ (X^4)^2 := Nat.pow_le_pow_left hLX 2
      _ = _ := by ring)
    have hr := Real.rpow_le_rpow (Nat.cast_nonneg n.natAbs) (by exact_mod_cast hnX : (n.natAbs : ℝ) ≤ (X : ℝ)^8) hδ.le
    calc
      _ ≤ 2*(n.natAbs.divisors.card : ℝ) := by exact_mod_cast hc
      _ ≤ _ := by dsimp [B]; nlinarith only [τ n.natAbs,mul_le_mul_of_nonneg_left hr hC.le]
  let key (d : Fin 4 → Fin 4 → ℤ) := (d 0 1*d 2 3, d 0 2*d 1 3)
  let small := Icc (-(L^2 : ℕ) : ℤ) ((L^2 : ℕ) : ℤ)
  have prod_size {d} (hd : d ∈ S) (i j k l : Fin 4) :
      (d i j * d k l).natAbs ≤ L^2 := by
    rw [Int.natAbs_mul,pow_two]
    exact Nat.mul_le_mul ((spec d hd).1 i j).2 ((spec d hd).1 k l).2
  have in_small {z : ℤ} (hz : z.natAbs ≤ L^2) : z ∈ small := by
    apply mem_Icc.mpr
    omega
  have hkey : (S.image key).card ≤ (2*L^2+1)^2 := by
    have sub : S.image key ⊆ small ×ˢ small := by
      intro k hk
      obtain ⟨d,hd,rfl⟩ := mem_image.mp hk
      exact mem_product.mpr ⟨in_small (prod_size hd 0 1 2 3),in_small (prod_size hd 0 2 1 3)⟩
    apply (card_le_card sub).trans_eq
    have size : small.card = 2*L^2+1 := by
      rw [show small = Icc (-(L^2 : ℕ) : ℤ) ((L^2 : ℕ) : ℤ) by rfl, Int.card_Icc]
      omega
    rw [card_product,size]; ring
  have each (k : ℤ × ℤ) (hk : k ∈ S.image key) :
      ((S.filter (fun d => key d = k)).card : ℝ) ≤ B^3 := by
    obtain ⟨base,hbase,rfl⟩ := mem_image.mp hk
    let a := (key base).1
    let b := (key base).2
    let c := b-a
    have basec : base 0 3 * base 1 2 = c := by
      dsimp [c,b,a,key]
      linarith [(spec base hbase).2.2]
    let encode (d : Fin 4 → Fin 4 → ℤ) := (d 0 1,d 0 2,d 0 3)
    let V := S.filter (fun d => key d = key base)
    have prods {d} (hd : d ∈ V) : d 0 1*d 2 3 = a ∧ d 0 2*d 1 3 = b ∧ d 0 3*d 1 2 = c := by
      obtain ⟨hs,he⟩ := mem_filter.mp hd
      have ha := congrArg Prod.fst he
      have hb := congrArg Prod.snd he
      change d 0 1*d 2 3 = a at ha
      change d 0 2*d 1 3 = b at hb
      exact ⟨ha,hb,by dsimp [c]; linarith [(spec d hs).2.2]⟩
    have nz := (spec base hbase).2.1
    have hzA : a ≠ 0 := mul_ne_zero (nz 0 1 (by decide)) (nz 2 3 (by decide))
    have hzB : b ≠ 0 := mul_ne_zero (nz 0 2 (by decide)) (nz 1 3 (by decide))
    have hzC : c ≠ 0 := basec ▸ mul_ne_zero (nz 0 3 (by decide)) (nz 1 2 (by decide))
    have maps : Set.MapsTo encode V (↑(factors a ×ˢ (factors b ×ˢ factors c)) : Set (ℤ × ℤ × ℤ)) := by
      intro d hd
      obtain ⟨ha,hb,hc⟩ := prods hd
      change (d 0 1,d 0 2,d 0 3) ∈ factors a ×ˢ (factors b ×ˢ factors c)
      exact mem_product.mpr ⟨mem_factors hzA ha,mem_product.mpr ⟨mem_factors hzB hb,mem_factors hzC hc⟩⟩
    have inj : Set.InjOn encode V := by
      intro d hd e he hh
      obtain ⟨ha,hb,hc⟩ := prods hd
      obtain ⟨ha',hb',hc'⟩ := prods he
      obtain ⟨h01,h02,h03⟩ : d 0 1 = e 0 1 ∧ d 0 2 = e 0 2 ∧ d 0 3 = e 0 3 := by
        simpa [encode] using hh
      have nd := (spec e (mem_filter.mp he).1).2.1
      rw [h01] at ha
      rw [h02] at hb
      rw [h03] at hc
      have h23 := mul_left_cancel₀ (nd 0 1 (by decide)) (ha.trans ha'.symm)
      have h13 := mul_left_cancel₀ (nd 0 2 (by decide)) (hb.trans hb'.symm)
      have h12 := mul_left_cancel₀ (nd 0 3 (by decide)) (hc.trans hc'.symm)
      have skew (i j) := ((spec d (mem_filter.mp hd).1).1 i j).1
      have skew' (i j) := ((spec e (mem_filter.mp he).1).1 i j).1
      have upper (i j : Fin 4) (h : i < j) : d i j = e i j := by
        fin_cases i <;> fin_cases j <;> first | assumption | exfalso; revert h; decide
      funext i j
      rcases lt_trichotomy i j with h | rfl | h
      · exact upper i j h
      · linarith only [skew i i,skew' i i]
      · rw [skew i j,skew' i j,upper j i h]
    have bound := card_le_card_of_injOn encode maps inj
    simp only [card_product] at bound
    have b0 : 0 ≤ B := by dsimp [B]; positivity
    have ab := factor_bound a (prod_size hbase 0 1 2 3)
    have bb := factor_bound b (prod_size hbase 0 2 1 3)
    have cb := factor_bound c (basec ▸ prod_size hbase 0 3 1 2)
    calc
      _ ≤ ((factors a).card : ℝ) * ((factors b).card * ((factors c).card : ℝ)) := by exact_mod_cast bound
      _ ≤ B*(B*B) := mul_le_mul ab (mul_le_mul bb cb (Nat.cast_nonneg _) b0)
        (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) b0
      _ = _ := by ring
  have hh := count_fibers S key (B^3) each
  have hI : ((S.image key).card : ℝ) ≤ 9*(L : ℝ)^4 := by
    have hl : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ 2*(L : ℝ)^2+1)
      (by nlinarith [one_le_pow₀ hl (n := 2)] : 2*(L : ℝ)^2+1 ≤ 3*(L : ℝ)^2) 2
    exact (by exact_mod_cast hkey : ((S.image key).card : ℝ) ≤ (2*(L : ℝ)^2+1)^2).trans (by nlinarith only [h])
  have hx0 : 0 < (X : ℝ) := by exact_mod_cast hX
  have eqp : (((X : ℝ)^8)^δ)^3 = (X : ℝ)^(η/2) := by
    rw [← Real.rpow_natCast_mul hx0.le,← Real.rpow_mul_natCast hx0.le]
    congr 1
    dsimp [δ]
    ring
  calc
    _ ≤ 9*(L : ℝ)^4 * B^3 := hh.trans (mul_le_mul_of_nonneg_right hI (by dsimp [B]; positivity))
    _ = (72*C^3) * (X : ℝ)^(η/2) * L^4 := by
      dsimp [B]
      rw [mul_pow,eqp]; ring
    _ ≤ (X : ℝ)^(η/2) * (X : ℝ)^(η/2) * L^4 := by gcongr; exact hlarge
    _ = _ := by rw [← Real.rpow_add hx0]; congr 2; ring

/-- A fixed minor and two coprime denominators determine the first
numerator modulo its denominator. Its chosen representative is unique. -/
lemma recover_numerator {p q r s b c : ℕ} (cop : p.Coprime q) (hr : r < p^2) (hs : s < p^2)
    (he : (r : ℤ)*q^2 - (b : ℤ)*p^2 = (s : ℤ)*q^2 - (c : ℤ)*p^2) : r = s := by
  have cp : IsCoprime ((p : ℤ)^2) ((q : ℤ)^2) := cop.isCoprime.pow
  have dvd : (p : ℤ)^2 ∣ (r : ℤ)-s := cp.dvd_of_dvd_mul_right
    ⟨(b : ℤ)-c,by linarith only [he]⟩
  have small : ((r : ℤ)-s).natAbs < ((p : ℤ)^2).natAbs := by
    simp only [Int.natAbs_pow,Int.natAbs_natCast]
    omega
  have := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs dvd small
  omega

/-- Count the labelled close quadruples via their matrix of signed minors. -/
lemma count_quadruples (points : H1) :
    ∀ η : ℝ, 0 < η → ∀ᶠ X : ℕ in atTop, ∀ Y : ℝ, 1 ≤ Y →
    ∀ T : Finset (Fin 4 → ℕ × ℕ),
      (∀ t ∈ T, Function.Injective (fun i => (t i).1) ∧
        (∀ i, (t i).1.Prime ∧ (t i).1 ≤ X ∧ 0 < (t i).2 ∧ (t i).2 < (t i).1^2) ∧
        ∀ i j, |((t i).2 : ℝ) * (t j).1^2 - (t j).2 * ((t i).1 : ℝ)^2| ≤ Y) →
      (T.card : ℝ) ≤ (X : ℝ)^η * Y^4 := by
  classical
  intro η hη
  filter_upwards [points (η/2) (half_pos hη), count_patterns (η/2) (half_pos hη),
    eventually_ge_atTop (1 : ℕ)] with X fixed patterns hX
  intro Y hY T spec
  let L := min ⌊Y⌋₊ (X^4)
  have hL : 0 < L := lt_min (Nat.le_floor (by simpa using hY)) (pow_pos (by omega) _)
  let minors (t : Fin 4 → ℕ × ℕ) (i j : Fin 4) :=
    ((t i).2 : ℤ) * (t j).1^2 - (t j).2 * ((t i).1 : ℤ)^2
  let den (t : Fin 4 → ℕ × ℕ) (i : Fin 4) := (t i).1
  have bounds (t) (ht : t ∈ T) (i j) : (minors t i j).natAbs ≤ L := by
    obtain ⟨_,v,sm⟩ := spec t ht
    have real_abs : ((minors t i j).natAbs : ℝ) =
        |((t i).2 : ℝ) * (t j).1^2 - (t j).2 * ((t i).1 : ℝ)^2| := by
      dsimp [minors]
      rw [← Int.cast_natCast (R := ℝ),Int.natCast_natAbs,Int.cast_abs]
      push_cast
      rfl
    have prod_le (i j) : (t i).2 * (t j).1^2 ≤ X^4 := by
      have hi := (v i).2.2.2.le.trans (Nat.pow_le_pow_left (v i).2.1 2)
      exact (Nat.mul_le_mul hi (Nat.pow_le_pow_left (v j).2.1 2)).trans_eq (by ring)
    have a : ((t i).2 : ℤ) * (t j).1^2 ≤ (X^4 : ℕ) := by exact_mod_cast prod_le i j
    have b : ((t j).2 : ℤ) * (t i).1^2 ≤ (X^4 : ℕ) := by exact_mod_cast prod_le j i
    have a0 : (0 : ℤ) ≤ (t i).2 * ((t j).1 : ℤ)^2 := by positivity
    have b0 : (0 : ℤ) ≤ (t j).2 * ((t i).1 : ℤ)^2 := by positivity
    apply le_min (Nat.le_floor (real_abs.le.trans (sm i j)))
    dsimp [minors]
    omega
  have skew (t) (i j) : minors t i j = -minors t j i := by dsimp [minors]; ring
  have nz (t) (ht : t ∈ T) (i j) (hij : i ≠ j) : minors t i j ≠ 0 := by
    intro he
    obtain ⟨inj,v,_⟩ := spec t ht
    have cp := (Nat.coprime_primes (v i).1 (v j).1).mpr (fun e => hij (inj e))
    have h := recover_numerator (s := 0) (c := 0) cp (v i).2.2.2
      (pow_pos (v i).1.pos 2) (by simpa [minors] using he)
    exact (Nat.ne_of_gt (v i).2.2.1) h
  let S := T.image minors
  have nmat := patterns L hL (min_le_right _ _) S (by
    intro d hd
    obtain ⟨t,ht,rfl⟩ := mem_image.mp hd
    exact ⟨fun i j => ⟨skew _ _ _,bounds t ht i j⟩,nz t ht,by dsimp [minors]; ring⟩)
  have fiber (d) (hd : d ∈ S) :
      ((T.filter (fun t => minors t = d)).card : ℝ) ≤ (X : ℝ)^(η/2) := by
    obtain ⟨t₀,ht₀,rfl⟩ := mem_image.mp hd
    let V := T.filter (fun t => minors t = minors t₀)
    have ns := fixed (minors t₀)
      (fun i j => ⟨skew _ _ _,(bounds t₀ ht₀ i j).trans (min_le_right _ _)⟩)
      (nz t₀ ht₀) (V.image den) (by
        intro p hp
        obtain ⟨t,ht,rfl⟩ := mem_image.mp hp
        obtain ⟨ht,he⟩ := mem_filter.mp ht
        obtain ⟨inj,v,_⟩ := spec t ht
        refine ⟨inj,fun i => ⟨(v i).1,(v i).2.1⟩,?_⟩
        intro i j k
        rw [← he]
        dsimp [den,minors]
        ring)
    have inj : Set.InjOn den V := by
      intro t ht u hu he
      obtain ⟨ht,htd⟩ := mem_filter.mp ht
      obtain ⟨hu,hud⟩ := mem_filter.mp hu
      obtain ⟨it,vt,_⟩ := spec t ht
      obtain ⟨_,vu,_⟩ := spec u hu
      have pd (i) : (t i).1 = (u i).1 := congrFun he i
      have md := htd.trans hud.symm
      funext i
      obtain ⟨j,hj⟩ := exists_ne i
      have hh := congrFun (congrFun md i) j
      dsimp [minors] at hh
      rw [← pd i,← pd j] at hh
      apply Prod.ext (pd i)
      exact recover_numerator ((Nat.coprime_primes (vt i).1 (vt j).1).mpr (fun e => hj (it e).symm))
        (vt i).2.2.2 (by rw [pd]; exact (vu i).2.2.2) hh
    simpa only [Finset.card_image_iff.mpr inj] using ns
  have total := count_fibers T minors _ fiber
  have xl : 0 < (X : ℝ) := by exact_mod_cast hX
  have ly : (L : ℝ) ≤ Y := (by exact_mod_cast (min_le_left ⌊Y⌋₊ (X^4)) : (L : ℝ) ≤ ⌊Y⌋₊).trans
    (Nat.floor_le (by linarith))
  calc
    _ ≤ ((X : ℝ)^(η/2) * L^4) * (X : ℝ)^(η/2) :=
      total.trans (mul_le_mul_of_nonneg_right nmat (by positivity))
    _ = (X : ℝ)^η * L^4 := by
      rw [mul_right_comm,← Real.rpow_add xl]; congr 2; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ly 4) (by positivity)

/-- Cancellation for sums, including diagonal pairs. -/
lemma energy_at_prime (A : Finset ℕ) (hs : ∀ n ∈ A + A, Squarefree n)
    (p : ℕ) (hp : p.Prime) :
    (A.card : ℝ)^2 ≤ ∑ r ∈ (range (p^2)).erase 0,
      ‖∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * ↑(((r : ℝ) / (p : ℝ)^2) * a))‖^2 := by
  classical
  let q := p^2
  have hq : 0 < q := pow_pos hp.pos _
  let z := Complex.exp (2 * Real.pi * Complex.I / q)
  have hz := Complex.isPrimitiveRoot_exp q hq.ne'
  let S (r : ℕ) := ∑ a ∈ A, z^(a*r)
  have vanish (a : ℕ) (ha : a ∈ A) (b : ℕ) (hb : b ∈ A) :
      ∑ r ∈ range q, (z^(a+b))^r = 0 := by
    have hnd := Nat.squarefree_iff_prime_squarefree.mp (hs _ (add_mem_add ha hb)) p hp
    have hne : z ^ (a+b) ≠ 1 := by
      intro he
      exact hnd (by simpa [q,pow_two] using (hz.pow_eq_one_iff_dvd _).mp he)
    have hpow : (z^(a+b))^q = 1 := by
      rw [← pow_mul,Nat.mul_comm,pow_mul,show z^q = 1 from hz.pow_eq_one,one_pow]
    have h := geom_sum_mul (z^(a+b)) q
    rw [hpow,sub_self,mul_eq_zero] at h
    exact h.resolve_right (sub_ne_zero.mpr hne)
  have zero : ∑ r ∈ range q, (S r)^2 = 0 := by
    have term (r : ℕ) : (S r)^2 = ∑ a ∈ A, ∑ b ∈ A, (z^(a+b))^r := by
      simp only [S,pow_two,Finset.sum_mul_sum,← pow_add,← pow_mul,Nat.add_mul]
    simp_rw [term]
    rw [sum_comm]
    apply sum_eq_zero
    intro a ha
    rw [sum_comm]
    exact sum_eq_zero (fun b hb => vanish _ ha _ hb)
  have erased := sum_erase_add (range q) (fun r => (S r)^2) (mem_range.mpr hq)
  have e0 : S 0 = (A.card : ℂ) := by simp [S]
  rw [zero,e0] at erased
  have hsum : ∑ r ∈ (range q).erase 0, (S r)^2 = -(A.card : ℂ)^2 := by
    linear_combination erased
  have bound := norm_sum_le ((range q).erase 0) (fun r => (S r)^2)
  rw [hsum,norm_neg,norm_pow] at bound
  simp only [Complex.norm_natCast,norm_pow] at bound
  convert bound using 2 with r
  congr 2
  apply sum_congr rfl
  intro a _
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  dsimp [q]
  push_cast
  ring

/-- A bin has width at most the spacing within any single denominator.
Cross multiplication converts its diameter into a bound on the six minors. -/
lemma bin_geometry {M X : ℕ} {Y : ℝ} (hm : 0 < M) (hXM : X^2 ≤ M)
    (hXY : (X : ℝ)^4 ≤ M * Y) :
    let α (u : ℕ × ℕ) := (u.2 : ℝ) / (u.1 : ℝ)^2
    let bin (u : ℕ × ℕ) := ⌊(M : ℝ) * α u⌋₊
    let valid (u : ℕ × ℕ) := u.1.Prime ∧ u.1 ≤ X ∧ 0 < u.2 ∧ u.2 < u.1^2
    (∀ u, valid u → 1 / (M : ℝ) ≤ α u ∧ α u ≤ 1 - 1 / M) ∧
    (∀ u v, valid u → valid v → bin u = bin v → u.1 = v.1 → u = v) ∧
    ∀ u v, valid u → valid v → bin u = bin v →
      |(u.2 : ℝ) * (v.1 : ℝ)^2 - v.2 * (u.1 : ℝ)^2| ≤ Y := by
  dsimp only
  have hmR : (0 : ℝ) < M := by exact_mod_cast hm
  have denom {p : ℕ} (hp : p ≤ X) : (p : ℝ)^2 ≤ M := by
    exact_mod_cast (pow_le_pow_left' hp 2).trans hXM
  have near (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y)
      (hb : ⌊(M : ℝ)*x⌋₊ = ⌊(M : ℝ)*y⌋₊) : |x-y| < 1 / (M : ℝ) := by
    have h1 := Nat.floor_le (mul_nonneg hmR.le hx)
    have h2 := Nat.floor_le (mul_nonneg hmR.le hy)
    have h3 := Nat.lt_floor_add_one ((M : ℝ)*x)
    have h4 := Nat.lt_floor_add_one ((M : ℝ)*y)
    rw [hb] at h1 h3
    rw [abs_lt]
    constructor
    · rw [neg_lt,neg_sub,lt_div_iff₀ hmR]
      linarith
    · apply (lt_div_iff₀ hmR).mpr
      linarith
  constructor
  · rintro ⟨p,r⟩ ⟨hp,hX,hr,hrp⟩
    change 1 / (M : ℝ) ≤ (r : ℝ) / (p : ℝ)^2 ∧ _ / _ ≤ _
    have hq : 0 < (p : ℝ)^2 := by exact_mod_cast pow_pos hp.pos 2
    have dlo : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have dhi : (r : ℝ) + 1 ≤ (p : ℝ)^2 := by exact_mod_cast hrp
    have dq := denom hX
    constructor
    · exact (one_div_le_one_div_of_le hq dq).trans (div_le_div_of_nonneg_right dlo hq.le)
    · have hi : (r : ℝ) / (p : ℝ)^2 + 1 / (p : ℝ)^2 ≤ 1 := by
        rw [← add_div,div_le_one hq]
        exact dhi
      linarith [one_div_le_one_div_of_le hq dq]
  constructor
  · rintro ⟨p,r⟩ ⟨s,t⟩ ⟨hp,hpX,hr,hrp⟩ ⟨hs,hsX,ht,hts⟩ hb he
    change p = s at he
    subst s
    congr 1
    have hq : 0 < (p : ℝ)^2 := by exact_mod_cast pow_pos hp.pos 2
    have h := near ((r : ℝ)/p^2) ((t : ℝ)/p^2) (by positivity) (by positivity) hb
    rw [← sub_div,abs_div,abs_of_pos hq] at h
    have h' := h.trans_le (one_div_le_one_div_of_le hq (denom hpX))
    rw [div_lt_div_iff_of_pos_right hq, abs_lt] at h'
    have hl : (r : ℝ) < t+1 := by linarith [h'.2]
    have hu : (t : ℝ) < r+1 := by linarith [h'.1]
    have hl' : r < t+1 := by exact_mod_cast hl
    have hu' : t < r+1 := by exact_mod_cast hu
    change r = t
    omega
  · rintro ⟨p,r⟩ ⟨s,t⟩ ⟨hp,hpX,hr,hrp⟩ ⟨hs,hsX,ht,hts⟩ hb
    have hp0 : 0 < (p : ℝ)^2 := by exact_mod_cast pow_pos hp.pos 2
    have hs0 : 0 < (s : ℝ)^2 := by exact_mod_cast pow_pos hs.pos 2
    have h := near ((r : ℝ)/p^2) ((t : ℝ)/s^2) (by positivity) (by positivity) hb
    rw [div_sub_div _ _ hp0.ne' hs0.ne',abs_div,abs_of_pos (mul_pos hp0 hs0)] at h
    have hX : (p : ℝ)^2 * (s : ℝ)^2 ≤ (X : ℝ)^4 := by
      rw [show (X : ℝ)^4 = (X : ℝ)^2 * (X : ℝ)^2 by ring]
      exact_mod_cast Nat.mul_le_mul (Nat.pow_le_pow_left hpX 2) (Nat.pow_le_pow_left hsX 2)
    change |(r : ℝ)* (s : ℝ)^2 - (t : ℝ)*(p : ℝ)^2| ≤ Y
    apply (le_of_mul_le_mul_right (a := (M : ℝ)) ?_ hmR)
    have hh := (div_lt_div_iff₀ (mul_pos hp0 hs0) hmR).mp h
    rw [mul_comm ((p : ℝ)^2) (t : ℝ)] at hh
    linarith

/-- Six applications of the classical sieve cover the three retained ranks
in the even and odd bins. The end margins guarantee separation on the circle. -/
lemma sample_colors (sieve : H2) (M : ℕ) (hM : 0 < M) (A : Finset ℕ) (hA : A ⊆ Icc 1 M)
    (G : Finset (ℕ × ℕ)) (α : ℕ × ℕ → ℝ) (c : ℕ × ℕ → ℕ)
    (edge : ∀ u ∈ G, 1 / (M : ℝ) ≤ α u ∧ α u ≤ 1 - 1 / M)
    (hc : ∀ u ∈ G, c u < 3)
    (inj : ∀ u ∈ G, ∀ v ∈ G, ⌊(M : ℝ) * α u⌋₊ = ⌊(M : ℝ) * α v⌋₊ → c u = c v → u = v) :
    ∑ u ∈ G, ‖∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * ↑(α u * a))‖^2 ≤
      48 * (M : ℝ) * A.card := by
  classical
  let bin (u : ℕ × ℕ) := ⌊(M : ℝ) * α u⌋₊
  let key (u : ℕ × ℕ) := 2 * c u + bin u % 2
  let F (u : ℕ × ℕ) := ‖∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * ↑(α u * a))‖^2
  have hm : (0 : ℝ) < M := by exact_mod_cast hM
  have hd : 0 < 1 / (M : ℝ) := by positivity
  have gap {u v : ℕ × ℕ} (hu : u ∈ G) (hv : v ∈ G) (hb : bin u + 2 ≤ bin v) :
      1 / (M : ℝ) ≤ α v - α u := by
    have h1 : (M : ℝ) * α u < (bin u : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : (bin v : ℝ) ≤ M * α v := Nat.floor_le (mul_nonneg hm.le (hd.le.trans (edge v hv).1))
    have h3 : (bin u : ℝ) + 2 ≤ bin v := by exact_mod_cast hb
    apply (div_le_iff₀ hm).mpr
    linarith
  have per (k : ℕ) : ∑ u ∈ G.filter (fun u => key u = k), F u ≤ 8 * (M : ℝ) * A.card := by
    apply sieve _ M hM A hA α
    · intro u hu
      obtain ⟨lo,hi⟩ := edge u (mem_filter.mp hu).1
      constructor <;> linarith
    · intro u hu v hv hne
      obtain ⟨hu,hu'⟩ := mem_filter.mp hu
      obtain ⟨hv,hv'⟩ := mem_filter.mp hv
      have hk : 2*c u + bin u%2 = 2*c v + bin v%2 := hu'.trans hv'.symm
      have hbin : bin u ≠ bin v := fun hb => hne (inj _ hu _ hv hb (by omega))
      obtain ⟨ul,ur⟩ := edge u hu
      obtain ⟨vl,vr⟩ := edge v hv
      constructor
      · rcases lt_or_gt_of_ne hbin with h | h
        · exact (gap hu hv (by omega)).trans (by rw [abs_sub_comm]; exact le_abs_self _)
        · exact (gap hv hu (by omega)).trans (le_abs_self _)
      · rw [le_sub_comm]
        apply abs_le.mpr
        constructor <;> linarith
  have maps (u) (hu : u ∈ G) : key u ∈ range 6 := by
    have := hc u hu
    apply mem_range.mpr
    dsimp [key]
    omega
  calc
    _ = ∑ k ∈ range 6, ∑ u ∈ G.filter (fun u => key u = k), F u :=
      (sum_fiberwise_of_maps_to maps F).symm
    _ ≤ ∑ _k ∈ range 6, 8 * (M : ℝ) * A.card := sum_le_sum fun k _ => per k
    _ = _ := by simp; ring

/-- The critical finite estimate. The contribution of discarded points is at
most one squared cardinality per quadruple. -/
lemma finite_bound (sieve : H2) (X M : ℕ) (Y K : ℝ) (hm : 0 < M) (hXM : X^2 ≤ M)
    (hXY : (X : ℝ)^4 ≤ M * Y)
    (count : ∀ T : Finset (Fin 4 → ℕ × ℕ),
      (∀ t ∈ T, Function.Injective (fun i => (t i).1) ∧
        (∀ i, (t i).1.Prime ∧ (t i).1 ≤ X ∧ 0 < (t i).2 ∧ (t i).2 < (t i).1^2) ∧
        ∀ i j, |((t i).2 : ℝ) * (t j).1^2 - (t j).2 * ((t i).1 : ℝ)^2| ≤ Y) →
      (T.card : ℝ) ≤ K)
    (A : Finset ℕ) (hA : A ⊆ Icc 1 M) (hs : ∀ n ∈ A+A, Squarefree n) :
    (((range (X+1)).filter Nat.Prime).card : ℝ) * (A.card : ℝ)^2 ≤
      48 * (M : ℝ) * A.card + K * (A.card : ℝ)^2 := by
  classical
  let P := (range (X+1)).filter Nat.Prime
  let J := (P ×ˢ range (X^2)).filter (fun u => 0 < u.2 ∧ u.2 < u.1^2)
  let α (u : ℕ × ℕ) := (u.2 : ℝ) / (u.1 : ℝ)^2
  let bin (u : ℕ × ℕ) := ⌊(M : ℝ) * α u⌋₊
  let F (u : ℕ × ℕ) := ‖∑ a ∈ A, Complex.exp (2 * Real.pi * Complex.I * ↑(α u * a))‖^2
  have valid {u : ℕ × ℕ} :
      u ∈ J ↔ u.1.Prime ∧ u.1 ≤ X ∧ 0 < u.2 ∧ u.2 < u.1^2 := by
    simp only [J,P,mem_filter,mem_product,mem_range,Nat.lt_succ_iff]
    constructor
    · tauto
    · rintro ⟨hp,hx,hr,hq⟩
      exact ⟨⟨⟨hx,hp⟩, hq.trans_le (Nat.pow_le_pow_left hx 2)⟩,hr,hq⟩
  obtain ⟨edge, same, minor⟩ := bin_geometry hm hXM hXY
  obtain ⟨B,c,T,hBJ,hBT,quad,hc,hi⟩ := pack_bins J bin
  have hTK : (T.card : ℝ) ≤ K := by
    apply count T
    intro t ht
    obtain ⟨ti,tm⟩ := quad t ht
    have tv (i) := valid.mp (tm i).1
    have beq (i j) := (tm i).2.trans (tm j).2.symm
    exact ⟨fun i j he => ti (same _ _ (tv i) (tv j) (beq i j) he),tv,
      fun i j => minor _ _ (tv i) (tv j) (beq i j)⟩
  have good : ∑ u ∈ J \ B, F u ≤ 48 * (M : ℝ) * A.card :=
    sample_colors sieve M hm A hA _ α c (fun u hu => edge _ (valid.mp (mem_sdiff.mp hu).1)) hc hi
  have bad : ∑ u ∈ B, F u ≤ K * (A.card : ℝ)^2 := by
    have point (u : ℕ × ℕ) : F u ≤ (A.card : ℝ)^2 := by
      apply pow_le_pow_left₀ (norm_nonneg _) _ 2
      calc
        _ ≤ _ := norm_sum_le _ _
        _ = (A.card : ℝ) := by
          simp [Complex.norm_exp,Complex.mul_re,Complex.mul_im]
    calc
      _ ≤ ∑ _u ∈ B, (A.card : ℝ)^2 := sum_le_sum fun u _ => point u
      _ = (B.card : ℝ) * (A.card : ℝ)^2 := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right ((by exact_mod_cast hBT : (B.card : ℝ) ≤ T.card).trans hTK)
        (sq_nonneg _)
  have spec (u : ℕ × ℕ) : u ∈ J ↔ u.1 ∈ P ∧ u.2 ∈ (range (u.1^2)).erase 0 := by
    rw [valid]
    simp only [P,mem_filter,mem_range,Nat.lt_succ_iff,mem_erase]
    simp only [ne_eq, Nat.pos_iff_ne_zero]
    tauto
  calc
    _ = ∑ _p ∈ P, (A.card : ℝ)^2 := by simp [P]
    _ ≤ ∑ p ∈ P, ∑ r ∈ (range (p^2)).erase 0, F (p,r) :=
      sum_le_sum fun p hp => energy_at_prime A hs p (mem_filter.mp hp).2
    _ = ∑ u ∈ J, F u := (sum_finset_product J P _ spec).symm
    _ = (∑ u ∈ J \ B, F u) + ∑ u ∈ B, F u := (sum_sdiff hBJ).symm
    _ ≤ _ := add_le_add good bad

/-- Chebyshev bound, adapted from the merged R1.H2 proof by OrangeHeadz. -/
theorem pi_lower :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) / 2 / Real.log (n : ℝ) ≤ (Nat.primeCounting n : ℝ) := by
  have h0 : ∀ᶠ x : ℝ in atTop, ‖Real.log x‖ ≤ (9 / 100 : ℝ) * ‖x‖ :=
    Real.isLittleO_log_id_atTop.bound (by norm_num)
  have h1 : ∀ᶠ n : ℕ in atTop,
      ‖Real.log ((n : ℝ) + 1)‖ ≤ (9 / 100 : ℝ) * ‖(n : ℝ) + 1‖ :=
    (tendsto_atTop_add_const_right atTop 1 (tendsto_natCast_atTop_atTop (R := ℝ))).eventually h0
  filter_upwards [h1, eventually_ge_atTop 2] with n hn hn2
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hlogpos : 0 < Real.log (n : ℝ) := Real.log_pos (by linarith)
  have hl : Real.log ((n : ℝ) + 1) ≤ 9 / 100 * ((n : ℝ) + 1) := by
    have h := (Real.le_norm_self _).trans hn
    rwa [Real.norm_of_nonneg (by linarith)] at h
  have h2 := Chebyshev.pi_ge n
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h3 : (n : ℝ) * 0.6931471803 ≤ (n : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2.le (by linarith)
  refine le_trans ?_ h2
  rw [div_le_div_iff₀ hlogpos hlogpos]
  apply mul_le_mul_of_nonneg_right _ hlogpos.le
  linarith

lemma primes_at_cutoff :
    ∀ η : ℝ, 0 < η → ∀ᶠ N : ℕ in atTop,
      (N : ℝ)^(4/15-η) ≤ (((range (⌊(N : ℝ)^(4/15 : ℝ)⌋₊+1)).filter Nat.Prime).card : ℝ) := by
  intro η hη
  have hX : Tendsto (fun N : ℕ => ⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp
      ((tendsto_rpow_atTop (by norm_num)).comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hA : ∀ᶠ N : ℕ in atTop,
      ((⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ : ℕ) : ℝ) / 2 /
          Real.log ((⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ : ℕ) : ℝ) ≤
        (Nat.primeCounting ⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ : ℝ) ∧
      2 ≤ ⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ :=
    hX.eventually (pi_lower.and (eventually_ge_atTop 2))
  have hB : ∀ᶠ N : ℕ in atTop, ‖Real.log (N : ℝ)‖ ≤ (1 / 4 : ℝ) * ‖(N : ℝ) ^ η‖ :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      ((isLittleO_log_rpow_atTop hη).bound (by norm_num))
  filter_upwards [hA, hB, eventually_ge_atTop 2] with N hA hB hN2
  obtain ⟨hpi, hX2⟩ := hA
  have hNr : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNpos : (0 : ℝ) < N := by linarith
  have hP : (0 : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 15) := Real.rpow_nonneg hNpos.le _
  have hXle : ((⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ : ℕ) : ℝ) ≤ (N : ℝ) ^ ((4 : ℝ) / 15) :=
    Nat.floor_le hP
  have hXgt : (N : ℝ) ^ ((4 : ℝ) / 15) < ((⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hXr : (2 : ℝ) ≤ ((⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ : ℕ) : ℝ) := by exact_mod_cast hX2
  have hcard : ((Finset.range (⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ + 1)).filter Nat.Prime).card =
      Nat.primeCounting ⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ := by
    rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  rw [hcard]
  generalize ⌊(N : ℝ) ^ ((4 : ℝ) / 15)⌋₊ = X at hpi hX2 hXle hXgt hXr ⊢
  have hPN : (N : ℝ) ^ ((4 : ℝ) / 15) ≤ N := by
    calc (N : ℝ) ^ ((4 : ℝ) / 15) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = N := Real.rpow_one _
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos (by linarith)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith)
  have hlogle : Real.log (X : ℝ) ≤ Real.log (N : ℝ) :=
    Real.log_le_log (by linarith) (by linarith)
  have hNη : 0 < (N : ℝ) ^ η := Real.rpow_pos_of_pos hNpos _
  have h4 : 4 * Real.log (N : ℝ) ≤ (N : ℝ) ^ η := by
    rw [Real.norm_of_nonneg hlogN.le, Real.norm_of_nonneg hNη.le] at hB
    linarith
  refine le_trans ?_ hpi
  rw [Real.rpow_sub hNpos, div_le_div_iff₀ hNη hlogX]
  have h5 : (N : ℝ) ^ ((4 : ℝ) / 15) ≤ 2 * (X : ℝ) := by linarith
  have h6 : Real.log (X : ℝ) ≤ (N : ℝ) ^ η / 4 := by linarith
  calc (N : ℝ) ^ ((4 : ℝ) / 15) * Real.log (X : ℝ)
      ≤ (2 * (X : ℝ)) * ((N : ℝ) ^ η / 4) := mul_le_mul h5 h6 hlogX.le (by linarith)
    _ = (X : ℝ) / 2 * (N : ℝ) ^ η := by ring

theorem main : H1 → H2 → type_of% @Erdos1109.erdos_1109.variants.konyagin_upper := by
  classical
  intro points sieve ε hε
  have quadruples := count_quadruples points
  let η := min (1/30 : ℝ) (ε/4)
  have hη : 0 < η := lt_min (by norm_num) (by positivity)
  have hη₁ : η ≤ 1/30 := min_le_left _ _
  have hη₂ : η ≤ ε/4 := min_le_right _ _
  have hcut : Tendsto (fun N : ℕ => ⌊(N : ℝ)^(4/15 : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp ((tendsto_rpow_atTop (by norm_num)).comp tendsto_natCast_atTop_atTop)
  have grow := ((tendsto_rpow_atTop hη).comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 2
  apply Asymptotics.IsBigO.of_bound 192
  filter_upwards [hcut.eventually (quadruples η hη), primes_at_cutoff η hη, grow,
    eventually_ge_atTop (1 : ℕ)] with N hquad hpr hge hN
  let X := ⌊(N : ℝ)^(4/15 : ℝ)⌋₊
  let M := ⌈(N : ℝ)^(1+η)⌉₊
  let Y := (N : ℝ)^(1/15-η)
  let K := (X : ℝ)^η * Y^4
  let P := ((range (X+1)).filter Nat.Prime).card
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have hr (a b : ℝ) (h : a ≤ b) := Real.rpow_le_rpow_of_exponent_le hn h
  have power (a : ℝ) (k : ℕ) : ((N : ℝ)^a)^k = (N : ℝ)^(a*k) := by
    rw [Real.rpow_mul hn0.le,Real.rpow_natCast]
  have hx : (X : ℝ) ≤ (N : ℝ)^(4/15 : ℝ) := Nat.floor_le (by positivity)
  have hxN : (X : ℝ) ≤ N := hx.trans (by simpa using hr _ 1 (by norm_num : (4/15 : ℝ) ≤ 1))
  have hmlo : (N : ℝ)^(1+η) ≤ M := Nat.le_ceil _
  have hnM : N ≤ M := by
    exact_mod_cast (show (N : ℝ) ≤ M from (by simpa using hr 1 (1+η) (by linarith) :
      (N : ℝ) ≤ (N : ℝ)^(1+η)).trans hmlo)
  have hmhi : (M : ℝ) ≤ 2 * (N : ℝ)^(1+η) := by
    have h := Nat.ceil_lt_add_one (by positivity : 0 ≤ (N : ℝ)^(1+η))
    change (⌈(N : ℝ)^(1+η)⌉₊ : ℝ) ≤ _
    linarith [Real.one_le_rpow hn (by linarith : 0 ≤ 1+η)]
  have hxM : X^2 ≤ M := by
    have hh := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) X) hx 2
    rw [power] at hh
    exact_mod_cast hh.trans ((hr _ _ (by norm_num : (4/15 : ℝ)*2 ≤ 1)).trans
      ((Real.rpow_one _).le.trans (by exact_mod_cast hnM : (N : ℝ) ≤ M)))
  have hY : 1 ≤ Y := Real.one_le_rpow hn (by linarith)
  have hXY : (X : ℝ)^4 ≤ M * Y := by
    calc
      _ ≤ ((N : ℝ)^(4/15 : ℝ))^4 := pow_le_pow_left₀ (by positivity) hx 4
      _ = (N : ℝ)^(1+η) * Y := by
        rw [power, ← Real.rpow_add hn0]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hmlo (by linarith)
  have hK : 2 * K ≤ (N : ℝ)^(4/15-η) := by
    have loss : K ≤ (N : ℝ)^(4/15-3*η) := by
      calc
        _ ≤ (N : ℝ)^η * Y^4 := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by positivity) hxN hη.le) (by positivity)
        _ = _ := by
          dsimp [Y]
          rw [power,← Real.rpow_add hn0]; congr 1; ring
    calc
      _ ≤ (N : ℝ)^η * (N : ℝ)^(4/15-3*η) :=
        mul_le_mul hge loss (by dsimp [K,Y]; positivity) (by positivity)
      _ = (N : ℝ)^(4/15-2*η) := by rw [← Real.rpow_add hn0]; congr 1; ring
      _ ≤ _ := hr _ _ (by linarith)
  change (N : ℝ)^(4/15-η) ≤ P at hpr
  simp only [Real.norm_eq_abs,Nat.abs_cast,abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  apply (Nat.le_floor_iff (by positivity)).mp
  unfold Erdos1109.f
  apply csSup_le
  · exact ⟨0,∅,by simp,by simp,rfl⟩
  rintro _ ⟨A,hA,hs,rfl⟩
  apply Nat.le_floor
  by_cases hz : A.card = 0
  · simp [hz,Real.rpow_nonneg]
  have hzR : (0 : ℝ) < A.card := by exact_mod_cast Nat.pos_of_ne_zero hz
  have bound := finite_bound sieve X M Y K (by omega) hxM hXY (hquad Y hY) A
    (hA.trans (Icc_subset_Icc_right hnM)) hs
  change (P : ℝ) * (A.card : ℝ)^2 ≤ _ at bound
  have sub : (N : ℝ)^(4/15-η) * A.card ≤ 96 * M := by
    apply le_of_mul_le_mul_right (a := (A.card : ℝ)) _ hzR
    nlinarith only [bound,mul_le_mul_of_nonneg_right hpr (sq_nonneg (A.card : ℝ)),
      mul_le_mul_of_nonneg_right hK (sq_nonneg (A.card : ℝ))]
  have ht : (A.card : ℝ) ≤ 192 * (N : ℝ)^(11/15+2*η) := by
    apply le_of_mul_le_mul_left (a := (N : ℝ)^(4/15-η)) _ (Real.rpow_pos_of_pos hn0 _)
    calc
      _ ≤ 192 * (N : ℝ)^(1+η) := by linarith
      _ = _ := by
        rw [mul_left_comm,← Real.rpow_add hn0]
        congr 2; ring
  exact ht.trans (mul_le_mul_of_nonneg_left (hr _ _ (by linarith)) (by norm_num))

end OMA.R_Erdos1109_erdos_1109_variants_konyagin_upper_R2
