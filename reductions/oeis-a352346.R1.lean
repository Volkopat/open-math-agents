import OMAStatements.S_oeis_a352346

/-!
# Common partial sums of decimal digit products

The odd summatory function attains every dyadic residue in every sufficiently
long run of repunit exponents. Modulo every power of two greater than one,
the even summatory function attains exactly the even residues. The first reduction step
is proved here. The remaining step asks for a bound on the least odd-side
preimages at increasing dyadic precision. The height condition is necessary
and sufficient for the original infinitude conjecture.

Other unconditional results include 1,099 distinct certified values, the
modulo-three and modulo-twenty-five digit obstructions, and the bound
C(X) ≤ 120 X^(log_45(6)) on the number of common values below X. A finite
Fourier correlation criterion gives another exact formulation.

Sources: OEIS A352346 and Chai Wah Wu's 205-entry table. The original
question and complete-decade sums occur in A. Murthy, “Smarandache friendly
numbers and a few more sequences”, Smarandache Notions Journal 12 (2001),
p. 267. The larger list was found by a decimal-prefix search and is checked
by the kernel directly against the original summatory definitions.
-/

namespace Digit352
open OMA.S_oeis_a352346 Finset

theorem digit_append (t r : ℕ) (hr : r < 10) (h : t ≠ 0 ∨ r ≠ 0) :
    digitProd (10*t+r) = r * digitProd t := by
  unfold digitProd
  rw [Nat.add_comm, Nat.digits_add 10 (by decide) r t hr h.symm, List.prod_cons]

private theorem even_succ (n : ℕ) :
    a061078 (n+1) = a061078 n + digitProd (2*(n+1)) := by
  unfold a061078
  rw [sum_Icc_succ_top (by omega)]

private theorem odd_succ (n : ℕ) :
    a061077 (n+1) = a061077 n + digitProd (2*(n+1)-1) := by
  unfold a061077
  rw [sum_Icc_succ_top (by omega)]

theorem even_partial (t r : ℕ) (hr : r ≤ 4) :
    a061078 (5*t+r) = a061078 (5*t) + r*(r+1)*digitProd t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 5*t+(r+1)=5*t+r+1 by omega,even_succ, ih (by omega),
      show 2*(5*t+r+1) = 10*t+2*(r+1) by ring,
      digit_append _ _ (by omega) (Or.inr (by omega))]
    ring

theorem odd_partial (t r : ℕ) (hr : r ≤ 5) :
    a061077 (5*t+r) = a061077 (5*t) + r^2*digitProd t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 5*t+(r+1)=5*t+r+1 by omega,odd_succ, ih (by omega),
      show 2*(5*t+r+1)-1 = 10*t+(2*r+1) by omega,
      digit_append _ _ (by omega) (Or.inr (by omega))]
    ring

theorem complete_blocks (t : ℕ) :
    a061078 (5*t) = 20*(∑ j ∈ range t, digitProd j) ∧
    a061077 (5*t) = 25*(∑ j ∈ range t, digitProd j) := by
  induction t with
  | zero => simp [a061078,a061077]
  | succ t ih =>
    rw [sum_range_succ]
    constructor
    · rw [show 5*(t+1)=5*t+4+1 by omega, even_succ, even_partial t 4 (by decide),
        show 2*(5*t+4+1) = 10*(t+1)+0 by ring, digit_append _ 0 (by decide) (Or.inl (by omega)), ih.1]
      ring
    · rw [show 5*(t+1)=5*t+5 by omega, odd_partial t 5 (by decide), ih.2]
      ring

theorem even_block (t r : ℕ) (hr : r ≤ 4) :
    a061078 (5*t+r) = 20*(∑ j ∈ range t, digitProd j) + r*(r+1)*digitProd t := by
  rw [even_partial t r hr,(complete_blocks t).1]

theorem odd_block (t r : ℕ) (hr : r ≤ 5) :
    a061077 (5*t+r) = 25*(∑ j ∈ range t, digitProd j) + r^2*digitProd t := by
  rw [odd_partial t r hr,(complete_blocks t).2]

end Digit352

namespace Digit352
open OMA.S_oeis_a352346 Finset

theorem prefix_partial (t r : ℕ) (ht : 0<t) (hr : r≤10) :
    (∑ j ∈ range (10*t+r), digitProd j) =
    (∑ j ∈ range (10*t), digitProd j) + (r.choose 2)*digitProd t := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [show 10*t+(r+1)=10*t+r+1 by omega, sum_range_succ, ih (by omega),
      digit_append t r (by omega) (Or.inl ht.ne'), Nat.choose_succ_succ r 1,
      Nat.choose_one_right]
    ring

theorem prefix_decade (t : ℕ) (ht : 0<t) :
    (∑ j ∈ range (10*t), digitProd j) = 45*(∑ j ∈ range t, digitProd j)+1 := by
  obtain ⟨u,rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht.ne'
  induction u with
  | zero => decide +kernel
  | succ u ih =>
    rw [show 10*(u+1+1)=10*(u+1)+10 by ring, prefix_partial (u+1) 10 (by omega) (by decide),
      ih (by omega), sum_range_succ (f:=digitProd) (n:=u+1)]
    rw [show Nat.choose 10 2=45 by decide]
    ring

theorem prefix_append (t r : ℕ) (ht : 0<t) (hr : r≤10) :
    (∑ j ∈ range (10*t+r), digitProd j) =
      45*(∑ j ∈ range t, digitProd j)+1+(r*(r-1)/2)*digitProd t := by
  rw [prefix_partial t r ht hr,prefix_decade t ht,Nat.choose_two_right]

end Digit352

namespace Digit352
open OMA.S_oeis_a352346 Finset

/-- Delete two decimal places of the original even/odd argument (equivalently,
divide its index by 50). The resulting prefixes cannot both contain a digit
divisible by three, nor can both products be divisible by 25. -/
theorem collision_prefix_obstructions {n m : ℕ} (h : a061078 n = a061077 m) :
    (¬3 ∣ digitProd (n/50) ∨ ¬3 ∣ digitProd (m/50)) ∧
    (¬25 ∣ digitProd (n/50) ∨ ¬25 ∣ digitProd (m/50)) := by
  by_cases hn : n/50=0
  · simp [hn,digitProd]
  by_cases hm : m/50=0
  · simp [hm,digitProd]
  let a := (n/5)%10
  let b := (m/5)%10
  let r := n%5
  let s := m%5
  have ha : a < 10 := Nat.mod_lt _ (by decide)
  have hb : b < 10 := Nat.mod_lt _ (by decide)
  have hr : r < 5 := Nat.mod_lt _ (by decide)
  have hs : s < 5 := Nat.mod_lt _ (by decide)
  have en : n=5*(10*(n/50)+a)+r := by dsimp only [a,r]; omega
  have em : m=5*(10*(m/50)+b)+s := by dsimp only [b,s]; omega
  conv at h => lhs; rw [en]
  conv at h => rhs; rw [em]
  rw [even_block _ _ (by omega), odd_block _ _ (by omega),
      prefix_append _ _ (by omega) ha.le, prefix_append _ _ (by omega) hb.le,
      digit_append _ _ ha (Or.inl hn), digit_append _ _ hb (Or.inl hm)] at h
  constructor <;> by_contra! bad
  all_goals
    obtain ⟨⟨u,hu⟩,⟨v,hv⟩⟩ := bad
    rw [hu,hv] at h
    ring_nf at h
    omega

end Digit352

namespace Digit352
open OMA.S_oeis_a352346 Finset

/-- There are six permitted decimal digits at each positive position.
The exceptional number zero has empty digit list and digit product one. -/
theorem not_three_dvd_count (k : ℕ) :
    5*((range (10^k)).filter (fun n => ¬3 ∣ digitProd n)).card+1 = 6^(k+1) := by
  classical
  let T := fun k : ℕ => (range (10^k)).filter (fun n => ¬3 ∣ digitProd n)
  let A : Finset ℕ := (range 10).filter (fun d => ¬3 ∣ d)
  have hA : A.card=6 := by decide
  have hA' {q r : ℕ} (hr : r<10) (h : q ≠ 0 ∨ r ≠ 0) :
      (¬3 ∣ digitProd (10*q+r)) ↔ (¬3 ∣ digitProd q ∧ ¬3 ∣ r) := by
    rw [digit_append q r hr h, (by decide : Nat.Prime 3).dvd_mul]
    tauto
  have step (d : ℕ) : (T (d+1)).card = 6*(T d).card + 1 := by
    let f := fun z : ℕ×ℕ => 10*z.1+z.2
    have eq : T (d+1) = insert 0 (((T d) ×ˢ A).image f) := by
      ext x
      simp only [T,mem_filter,mem_range,mem_insert,mem_image,mem_product,A,pow_succ]
      constructor
      · rintro ⟨hx,hx3⟩
        by_cases hz : x=0
        · exact Or.inl hz
        · right
          have hxq : 10*(x/10)+x%10=x := by omega
          have hxr : x%10<10 := Nat.mod_lt _ (by decide)
          have hnz : x/10 ≠ 0 ∨ x%10 ≠ 0 := by omega
          obtain ⟨hnq,hnr⟩ := (hA' hxr hnz).mp (by rw [hxq]; exact hx3)
          exact ⟨(x/10,x%10),⟨⟨by omega,hnq⟩,hxr,hnr⟩,hxq⟩
      · rintro (rfl|⟨⟨q,r⟩,⟨⟨hq,hq3⟩,hr,hr3⟩,rfl⟩)
        · exact ⟨by positivity, by simp [digitProd]⟩
        · have hr0 : r ≠ 0 := by rintro rfl; simp at hr3
          exact ⟨by dsimp [f] at *; omega, (hA' hr (Or.inr hr0)).mpr ⟨hq3,hr3⟩⟩
    have hzero : 0 ∉ ((T d)×ˢA).image f := by
      rintro h
      obtain ⟨⟨q,r⟩,hz,he⟩ := mem_image.mp h
      obtain ⟨_,hr⟩ := mem_product.mp hz
      have hr3 := (mem_filter.mp hr).2
      have : r=0 := by dsimp [f] at he; omega
      simp [this] at hr3
    have inj : Set.InjOn f (↑((T d)×ˢA) : Set (ℕ×ℕ)) := by
      rintro ⟨q,r⟩ hq ⟨u,v⟩ hu he
      have hr := mem_range.mp (mem_filter.mp (mem_product.mp hq).2).1
      have hv := mem_range.mp (mem_filter.mp (mem_product.mp hu).2).1
      dsimp only [f] at he
      congr 1 <;> omega
    rw [eq,card_insert_of_notMem hzero,Finset.card_image_of_injOn inj,Finset.card_product,hA,Nat.mul_comm]
  change 5*(T k).card+1=_
  induction k with
  | zero => decide
  | succ k ih => rw [step,pow_succ 6 (k+1)]; omega

end Digit352

namespace Digit352
open OMA.S_oeis_a352346 Finset Filter
open scoped Classical Topology

/-- The prefix sum includes the empty digit product at zero. -/
theorem prefix_power_ten (k : ℕ) :
    44*(∑ j ∈ range (10^k), digitProd j)+1 = 45^(k+1) := by
  induction k with
  | zero => decide +kernel
  | succ k ih =>
    rw [pow_succ',prefix_decade _ (by positivity),pow_succ]
    omega

private theorem even_mono : Monotone a061078 := by
  intro a b hab
  apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hab)
  simp

private theorem odd_mono : Monotone a061077 := by
  intro a b hab
  apply sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hab)
  simp

/-- Up to this height, every common value comes from one of two sets of
indices whose two-place prefix has digit product indivisible by three. -/
theorem common_count_le (k X : ℕ) (hX : X ≤ 20*45^(k+1)) :
    5*((range X).filter (· ∈ a352346Set)).card ≤ 100*(6^(k+1)-1) := by
  classical
  let S := (range (10^k)).filter (fun t => ¬ 3 ∣ digitProd t)
  let I := (S ×ˢ (range 50)).image (fun z : ℕ×ℕ => 50*z.1+z.2)
  have hmem {i : ℕ} (hi : i<50*10^k) (hd : ¬3 ∣ digitProd (i/50)) : i ∈ I := by
    apply mem_image.mpr
    refine ⟨(i/50,i%50),mem_product.mpr ⟨mem_filter.mpr ⟨mem_range.mpr ?_,hd⟩,
      mem_range.mpr (Nat.mod_lt _ (by decide))⟩,?_⟩
    · exact (Nat.div_lt_iff_lt_mul (by decide : 0<50)).mpr (by simpa [mul_comm] using hi)
    · exact Nat.div_add_mod _ _
  have hcut : 20*45^(k+1) ≤ a061078 (50*10^k) ∧ 20*45^(k+1) ≤ a061077 (50*10^k) := by
    have hk := prefix_power_ten (k+1)
    rw [pow_succ (n:=k+1)] at hk
    have hp : 45^(k+1) ≤ (∑ j ∈ range (10^(k+1)), digitProd j) := by omega
    rw [show 50*10^k = 5*10^(k+1) by rw [pow_succ]; ring,
      (complete_blocks _).1,(complete_blocks _).2]
    omega
  have hcover : ((range X).filter (· ∈ a352346Set)) ⊆ I.image a061078 ∪ I.image a061077 := by
    intro v hv
    obtain ⟨hv,hvterm⟩ := mem_filter.mp hv
    have hvlt := (mem_range.mp hv).trans_le hX
    obtain ⟨⟨n,_,hen⟩,⟨m,_,hom⟩⟩ := hvterm
    have hn : n < 50*10^k := by
      by_contra! h
      have hh := hcut.1.trans (even_mono h)
      omega
    have hm : m < 50*10^k := by
      by_contra! h
      have hh := hcut.2.trans (odd_mono h)
      omega
    obtain he | ho := (collision_prefix_obstructions (hen.trans hom.symm)).1
    · exact mem_union_left _ (mem_image.mpr ⟨n,hmem hn he,hen⟩)
    · exact mem_union_right _ (mem_image.mpr ⟨m,hmem hm ho,hom⟩)
  have hI : I.card ≤ S.card*50 := by
    apply card_image_le.trans
    simp
  have hc := (card_le_card hcover).trans ((card_union_le _ _).trans
    (add_le_add (card_image_le (f:=a061078) (s:=I)) (card_image_le (f:=a061077) (s:=I))))
  have hs : 5*S.card+1 = 6^(k+1) := not_three_dvd_count k
  omega

theorem common_count_le_log (X : ℕ) :
    ((range X).filter (· ∈ a352346Set)).card ≤ 120*6^(Nat.log 45 X) := by
  have hU := Nat.lt_pow_succ_log_self (by decide : 1<45) X
  have hc := common_count_le (Nat.log 45 X) X (by omega)
  rw [pow_succ] at hc
  omega

/-- Integer-power bounds yield every rational exponent above log(6)/log(45). -/
theorem common_count_pow_le {a b : ℕ} (hab : 6^b ≤ 45^a) {X : ℕ} (hX : 0<X) :
    ((range X).filter (· ∈ a352346Set)).card^b ≤ 120^b*X^a := by
  let k := Nat.log 45 X
  have hx : 45^k ≤ X := Nat.pow_log_le_self _ hX.ne'
  calc
    _ ≤ (120*6^k)^b := Nat.pow_le_pow_left (common_count_le_log X) b
    _ = 120^b*(6^b)^k := by rw [mul_pow,pow_right_comm]
    _ ≤ 120^b*(45^a)^k := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hab _)
    _ = 120^b*(45^k)^a := by rw [pow_right_comm (45:ℕ)]
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx _)

/-- The power law obtained by comparing six permitted digits with total digit weight 45. -/
theorem common_count_rpow {X : ℕ} (hX : 0<X) :
    (((range X).filter (· ∈ a352346Set)).card : ℝ) ≤
      120*(X:ℝ)^(Real.logb 45 6) := by
  let k := Nat.log 45 X
  have hq : (45:ℝ)^k ≤ X := by exact_mod_cast Nat.pow_log_le_self 45 hX.ne'
  have hpow : (6:ℝ)^k = ((45:ℝ)^k)^(Real.logb 45 6) := by
    rw [← Real.rpow_natCast_mul (by norm_num),mul_comm,Real.rpow_mul_natCast (by norm_num),
      Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)]
  calc
    _ ≤ 120*(6:ℝ)^k := by exact_mod_cast common_count_le_log X
    _ = 120*((45:ℝ)^k)^(Real.logb 45 6) := by rw [hpow]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hq
      (Real.logb_nonneg (by norm_num) (by norm_num))) (by norm_num)

/-- The number of distinct common values below X is little-o of its square root. -/
theorem common_count_div_sqrt :
    Tendsto (fun X : ℕ => (((range X).filter (· ∈ a352346Set)).card : ℝ)/Real.sqrt X)
      atTop (𝓝 0) := by
  let F (X : ℕ) : ℝ := ((range X).filter (· ∈ a352346Set)).card
  have hk : Tendsto (Nat.log 45) atTop atTop := by
    apply tendsto_atTop.2
    intro j
    filter_upwards [eventually_ge_atTop (45^j : ℕ)] with X hX
    exact Nat.le_log_of_pow_le (by decide) hX
  have hs : (6:ℝ) < Real.sqrt 45 := (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
  have hz := (tendsto_pow_atTop_nhds_zero_of_lt_one
    (by positivity : (0:ℝ) ≤ 6/Real.sqrt 45) ((div_lt_one (by positivity)).mpr hs)).comp hk
  have hlim : Tendsto (fun X : ℕ => 120*((6:ℝ)/Real.sqrt 45)^(Nat.log 45 X)) atTop (𝓝 0) := by
    simpa using hz.const_mul 120
  apply squeeze_zero' (Eventually.of_forall fun X => by positivity) _ hlim
  filter_upwards [eventually_ge_atTop (1:ℕ)] with X hX
  let k := Nat.log 45 X
  change F X/Real.sqrt X ≤ 120*((6:ℝ)/Real.sqrt 45)^k
  have hcR : F X ≤ 120*(6:ℝ)^k := by
    dsimp only [F,k]
    exact_mod_cast common_count_le_log X
  have hp : (45:ℝ)^k ≤ X := by exact_mod_cast Nat.pow_log_le_self 45 (show X≠0 by omega)
  have hq : (Real.sqrt 45)^k ≤ Real.sqrt X := Real.le_sqrt_of_sq_le <| calc
    _ = (45:ℝ)^k := by rw [← pow_mul,Nat.mul_comm k 2,pow_mul,Real.sq_sqrt (by norm_num)]
    _ ≤ _ := hp
  rw [div_pow,← mul_div_assoc]
  apply div_le_div₀ _ hcR (by positivity) hq
  positivity

theorem common_count_littleO_sqrt :
    (fun X : ℕ => (((range X).filter (· ∈ a352346Set)).card : ℝ)) =o[atTop]
      (fun X : ℕ => Real.sqrt (X:ℝ)) := by
  apply Asymptotics.isLittleO_of_tendsto' _ common_count_div_sqrt
  filter_upwards [eventually_ge_atTop (1:ℕ)] with X hX h
  have : 0 < Real.sqrt (X:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (show 0<X by omega))
  simp_all

end Digit352

namespace Digit352
open OMA.S_oeis_a352346 Finset

private theorem geom_append (a j b : ℕ) :
    (∑ i ∈ range (j+b), a^i) = (∑ i ∈ range j, a^i) + a^j * ∑ i ∈ range b,a^i := by
  simp [sum_range_add,pow_add,Finset.mul_sum]

/-- The 45-geometric sum of length 2^k is exactly 2^k times an odd number. -/
theorem geom45_period (k : ℕ) :
    ∃ u : ℕ, (∑ i ∈ range (2^k), 45^i) = 2^k*(2*u+1) := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨u,hu⟩ := ih
    have hp : 1 ≡ 45^(2^k) [MOD 4] := by
      simpa using (show 1 ≡ 45 [MOD 4] by decide).pow (2^k)
    obtain ⟨w,hw⟩ := (Nat.modEq_iff_exists_eq_add (Nat.succ_le_iff.mpr (pow_pos (by decide : 0<45) _))).mp hp
    refine ⟨u+w+2*u*w,?_⟩
    rw [show 2^(k+1)=2^k+2^k by rw [pow_succ]; omega,geom_append,hu,hw]
    ring

private theorem lift_one_bit {m x r w : ℕ} (h : x ≡ r [MOD m]) (hw : Odd w) :
    x ≡ r [MOD 2*m] ∨ x+m*w ≡ r [MOD 2*m] := by
  obtain ⟨q,hq⟩ := Nat.modEq_iff_dvd.mp h
  obtain ⟨s,hs|hs⟩ := Int.even_or_odd' q
  · left
    apply Nat.modEq_iff_dvd.mpr
    refine ⟨s,?_⟩
    rw [hs] at hq
    push_cast
    linear_combination hq
  · right
    obtain ⟨u,hu⟩ := hw
    apply Nat.modEq_iff_dvd.mpr
    refine ⟨s-u,?_⟩
    rw [hs] at hq
    rw [hu]
    push_cast
    linear_combination hq

/-- A power-of-two lifting argument for affine images of the 45-geometric sum. -/
theorem repunit_affine_residue_window (A B k r N : ℕ) (hA : Odd A) :
    ∃ j : ℕ, N ≤ j ∧ j < N+2^k ∧
      A*(∑ i ∈ range j,45^i)+B ≡ r [MOD 2^k] := by
  induction k with
  | zero => exact ⟨N,le_rfl,by simp, by simp [Nat.ModEq,Nat.mod_one]⟩
  | succ k ih =>
    obtain ⟨j,hN,hbound,hj⟩ := ih
    obtain ⟨u,hu⟩ := geom45_period k
    let w := A*45^j*(2*u+1)
    have hw : Odd w := hA.mul ((by decide : Odd (45:ℕ)).pow (n:=j)) |>.mul ⟨u,rfl⟩
    obtain h | h := lift_one_bit hj hw
    · exact ⟨j,hN,by rw [pow_succ]; omega,by simpa only [pow_succ'] using h⟩
    · refine ⟨j+2^k,hN.trans (Nat.le_add_right _ _),by rw [pow_succ]; omega,?_⟩
      rw [geom_append,hu,pow_succ']
      convert h using 1
      dsimp only [w]
      ring

theorem repunit_index_ge (j : ℕ) : j ≤ ∑ i ∈ range j,10^i := by
  calc
    j = ∑ _i ∈ range j,1 := by simp
    _ ≤ _ := sum_le_sum (fun i _ => Nat.succ_le_iff.mpr (pow_pos (by decide : 0<10) _))

theorem repunit_prefix (j : ℕ) :
    digitProd (∑ i ∈ range j, 10^i)=1 ∧
    (∑ d ∈ range (∑ i ∈ range j,10^i), digitProd d) = ∑ i ∈ range j,45^i := by
  induction j with
  | zero => simp [digitProd]
  | succ j ih =>
    obtain rfl | hj := Nat.eq_zero_or_pos j
    · decide +kernel
    have hpos := lt_of_lt_of_le hj (repunit_index_ge j)
    rw [geom_sum_succ (x:=10),geom_sum_succ (x:=45), digit_append _ _ (by decide) (Or.inr (by decide)),
      prefix_append _ _ hpos (by decide),ih.1,ih.2]
    simp

theorem odd_residue_late (k r N : ℕ) :
    ∃ j : ℕ, N ≤ j ∧ 0<j ∧ a061077 j ≡ r [MOD 2^k] := by
  obtain ⟨d,hN,_,hd⟩ := repunit_affine_residue_window 25 1 k r N (by decide)
  let q := ∑ i ∈ range d,10^i
  have H : N ≤ q := hN.trans (repunit_index_ge d)
  obtain ⟨D,P⟩ := repunit_prefix d
  refine ⟨5*q+1,by omega,by omega,?_⟩
  rw [odd_block _ 1 (by decide)]
  dsimp only [q]
  simpa only [P,D,one_pow,mul_one] using hd

theorem odd_residue_exists (k r : ℕ) :
    ∃ j : ℕ, 0<j ∧ Nat.ModEq (2^k) (a061077 j) r := by
  obtain ⟨j,_,h,hr⟩ := odd_residue_late k r 0
  exact ⟨j,h,hr⟩

theorem even_residue_late (k r N : ℕ) :
    ∃ j : ℕ, N ≤ j ∧ 0<j ∧ a061078 j ≡ 2*r [MOD 2^k] := by
  obtain ⟨d,hN,_,hd⟩ := repunit_affine_residue_window 5 0 k (r/2) (N+1) (by decide)
  let q := ∑ i ∈ range d,10^i
  have H : N+1 ≤ q := hN.trans (repunit_index_ge d)
  obtain ⟨D,P⟩ := repunit_prefix d
  let s := r%2
  have hs : s < 2 := Nat.mod_lt r (by decide)
  have hh : s*(s+1)=2*s := by interval_cases s <;> decide
  refine ⟨5*q+s,by omega,by omega,?_⟩
  rw [even_block q s (by omega)]
  dsimp only [q]
  rw [P,D,hh,mul_one]
  simp only [add_zero] at hd
  have h := (hd.mul_left 4).add_right (2*s)
  rw [show 2*r = 4*(r/2)+2*s by dsimp [s]; omega]
  convert h using 1
  ring

theorem even_value_two_dvd (j : ℕ) : 2 ∣ a061078 j := by
  let q := j/5
  let r := j%5
  have hr : r < 5 := Nat.mod_lt _ (by decide)
  have he := even_block q r (by omega)
  rw [show 5*q+r=j from Nat.div_add_mod j 5] at he
  rw [he]
  exact dvd_add (dvd_mul_of_dvd_left (by decide : 2∣20) _)
    (dvd_mul_of_dvd_left (Nat.two_dvd_mul_add_one r) _)

theorem even_residue_iff (k r N : ℕ) (hk : 0<k) :
    (∃ j : ℕ, N ≤ j ∧ 0<j ∧ a061078 j ≡ r [MOD 2^k]) ↔ 2 ∣ r := by
  constructor
  · rintro ⟨j,_,_,hj⟩
    have h := hj.of_dvd (dvd_pow_self 2 hk.ne')
    exact Nat.modEq_zero_iff_dvd.mp (h.symm.trans (Nat.modEq_zero_iff_dvd.mpr (even_value_two_dvd j)))
  · rintro ⟨s,rfl⟩
    exact even_residue_late k s N

end Digit352

namespace Digit352
open OMA.S_oeis_a352346 Finset

theorem read_decimal_word (ds : List ℕ) (hd : ∀ d ∈ ds, d < 10) :
    let step := fun (s : ℕ × ℕ × ℕ) (d : ℕ) =>
      if s.1=0 ∧ d=0 then s else
      (10*s.1+d,45*s.2.1+1+d*(d-1)/2*s.2.2,d*s.2.2)
    ∀ a : ℕ, let s := ds.foldl step (a,∑ j ∈ range a, digitProd j,digitProd a)
      s.2.1 = ∑ j ∈ range s.1, digitProd j ∧ s.2.2 = digitProd s.1 := by
  intro step
  induction ds with
  | nil => intro a; exact ⟨rfl,rfl⟩
  | cons d ds ih =>
    intro a
    have bd := hd d (by simp)
    have tail := ih (fun r hr => hd r (by simp [hr]))
    by_cases h : a=0 ∧ d=0
    · simpa only [List.foldl_cons,step,if_pos h] using tail a
    · have ha : a ≠ 0 ∨ d ≠ 0 := by omega
      have p : (∑ j ∈ range (10*a+d), digitProd j) =
          45*(∑ j ∈ range a, digitProd j)+1+d*(d-1)/2*digitProd a := by
        by_cases az : a=0
        · subst a
          interval_cases d <;> first | omega | decide +kernel
        · exact prefix_append a d (by omega) (by omega)
      simpa only [List.foldl_cons,step,if_neg h,←p,←digit_append a d bd ha]
        using tail (10*a+d)

theorem certified_chunk (lo hi cnt : ℕ)
    (rows : List ((List ℕ × ℕ) × (List ℕ × ℕ) × ℕ)) :
    let step := fun (s : ℕ × ℕ × ℕ) (d : ℕ) =>
      if s.1=0 ∧ d=0 then s else
      (10*s.1+d,45*s.2.1+1+d*(d-1)/2*s.2.2,d*s.2.2)
    let vals := (rows.map (fun x => x.2.2)).toFinset
    vals.card = cnt →
    rows.all (fun z =>
      let e := z.1.1.foldl step (0,0,1)
      let o := z.2.1.1.foldl step (0,0,1)
      let r := z.1.2
      let s := z.2.1.2
      let v := z.2.2
      z.1.1.all (fun d => decide (d<10)) && z.2.1.1.all (fun d => decide (d<10)) &&
      decide (r≤4 ∧ s≤4 ∧ 0<5*e.1+r ∧ 0<5*o.1+s ∧ lo≤v ∧ v≤hi ∧
        20*e.2.1+r*(r+1)*e.2.2=v ∧ 25*o.2.1+s^2*o.2.2=v)) = true →
    ∃ T : Finset ℕ, T.card=cnt ∧ ∀ n ∈ T, lo≤n ∧ n≤hi ∧ n∈a352346Set := by
  intro step vals size checks
  refine ⟨vals,size,?_⟩
  intro n hn
  obtain ⟨z,hz,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hn)
  have ok := List.all_eq_true.mp checks z hz
  simp only [Bool.and_eq_true, decide_eq_true_eq] at ok
  obtain ⟨⟨d1,d2⟩,r,s,ep,op,lb,ub,ev,ov⟩ := ok
  let e := z.1.1.foldl step (0,0,1)
  let o := z.2.1.1.foldl step (0,0,1)
  have ed := read_decimal_word z.1.1 (fun d h => of_decide_eq_true (List.all_eq_true.mp d1 d h)) 0
  have od := read_decimal_word z.2.1.1 (fun d h => of_decide_eq_true (List.all_eq_true.mp d2 d h)) 0
  change e.2.1 = ∑ j ∈ range e.1, digitProd j ∧ e.2.2 = digitProd e.1 at ed
  change o.2.1 = ∑ j ∈ range o.1, digitProd j ∧ o.2.2 = digitProd o.1 at od
  exact ⟨lb,ub,⟨⟨5*e.1+z.1.2,ep,by rw [even_block _ _ r,←ed.1,←ed.2]; exact ev⟩,
    ⟨5*o.1+z.2.1.2,op,by rw [odd_block _ _ (by omega),←od.1,←od.2]; exact ov⟩⟩⟩

theorem join_witness_sets {a b c d m n : ℕ} (ab : a≤b) (bc : b<c) (cd : c≤d)
    (x : ∃ T : Finset ℕ, T.card=m ∧ ∀ t ∈ T, a≤t ∧ t≤b ∧ t∈a352346Set)
    (y : ∃ T : Finset ℕ, T.card=n ∧ ∀ t ∈ T, c≤t ∧ t≤d ∧ t∈a352346Set) :
    ∃ T : Finset ℕ, T.card=m+n ∧ ∀ t ∈ T, a≤t ∧ t≤d ∧ t∈a352346Set := by
  obtain ⟨S,hs,hS⟩ := x
  obtain ⟨T,ht,hT⟩ := y
  have dj : Disjoint S T := by
    apply disjoint_left.mpr
    intro v hv hw
    exact (hT v hw).1.not_gt ((hS v hv).2.1.trans_lt bc)
  refine ⟨S∪T,by rw [card_union_of_disjoint dj,hs,ht],?_⟩
  intro w hw
  rcases mem_union.mp hw with h|h
  · exact ⟨(hS _ h).1,((hS _ h).2.1.trans bc.le).trans cd,(hS _ h).2.2⟩
  · exact ⟨(ab.trans bc.le).trans (hT _ h).1,(hT _ h).2⟩

end Digit352

namespace Digit352
open OMA.S_oeis_a352346 Finset

set_option maxRecDepth 6500 in
private theorem witness_block_0 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 26≤n ∧ n≤2353700 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1],2),([1],1),26),
    (([2],2),([2],1),52),
    (([4],1),([3],4),148),
    (([5],3),([5],1),280),
    (([5],4),([5],3),320),
    (([7],1),([6],3),454),
    (([1,5],2),([1,0],0),1150),
    (([1,7],4),([1,5],4),1480),
    (([4,6],4),([4,2],0),8000),
    (([1,1,5],2),([9,0],0),41650),
    (([1,9,8],4),([1,7,8],0),80300),
    (([3,2,1],2),([2,8,1],4),165656),
    (([3,2,3],2),([2,8,2],3),166088),
    (([5,9,4],2),([5,5,2],0),614900),
    (([1,5,6,8],1),([1,1,7,2],0),2353700)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_1 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 2859460≤n ∧ n≤5355218900 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,7,7,5],3),([1,5,3,6],3),2859460),
    (([5,9,7,1],3),([5,5,7,1],1),28233200),
    (([8,9,7,6],4),([8,1,2,5],0),66130400),
    (([9,3,6,2],4),([8,4,5,4],4),68941640),
    (([1,2,1,5,2],2),([9,3,1,5],3),85717240),
    (([1,5,7,8,5],2),([1,2,2,6,5],4),107300320),
    (([1,7,8,8,1],4),([1,5,6,2,8],4),131507080),
    (([1,9,6,5,4],2),([1,7,4,7,2],0),155478800),
    (([2,5,5,8,2],3),([2,1,3,1,5],2),207666520),
    (([6,5,2,9,4],4),([5,7,8,7,7],4),1426680920),
    (([7,2,5,1,7],1),([6,5,8,5,3],2),1824596800),
    (([8,4,1,5,4],1),([7,5,8,3,6],0),2468014900),
    (([8,4,4,2,4],4),([7,5,8,8,2],2),2475648820),
    (([1,6,8,6,4,8],4),([1,4,2,1,5,4],1),5342351060),
    (([1,6,8,7,5,6],2),([1,4,2,8,7,5],0),5355218900)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_2 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 5857281500≤n ∧ n≤178139569120 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,7,8,2,5,4],3),([1,5,5,1,4,1],4),5857281500),
    (([2,4,4,5,4,2],2),([1,9,4,5,3,2],0),8550475900),
    (([4,8,6,4,1,9],4),([4,4,8,7,5,4],4),36025361120),
    (([4,9,1,9,7,2],4),([4,5,8,2,5,7],4),37786361600),
    (([5,1,2,7,1,4],4),([4,6,9,6,5,6],2),40697695420),
    (([5,2,8,2,7,5],3),([4,7,4,9,5,2],3),41606981620),
    (([5,4,7,8,4,7],4),([4,8,2,9,4,5],4),44073205720),
    (([5,5,1,8,5,5],2),([4,8,5,7,7,8],4),44811068920),
    (([6,5,9,1,3,1],2),([5,8,4,8,8,7],4),66022660280),
    (([7,9,1,1,8,5],4),([7,1,7,4,1,5],3),101945140220),
    (([8,7,2,1,4,4],4),([7,7,9,5,8,8],4),120991043320),
    (([1,1,5,8,4,1,4],1),([9,1,4,5,1,9],0),170934766900),
    (([1,2,2,1,2,5,8],3),([9,3,2,8,5,4],3),173704599160),
    (([1,2,4,1,2,7,5],3),([9,3,6,3,8,5],4),174525119440),
    (([1,2,8,1,5,2,1],4),([9,4,7,4,5,2],3),178139569120)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_3 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 218246846740≤n ∧ n≤679148834708 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,5,8,1,4,1,1],1),([1,2,4,3,8,5,6],3),218246846740),
    (([1,5,8,2,5,4,4],4),([1,2,4,5,3,4,6],2),218344906420),
    (([1,5,8,3,7,1,4],2),([1,2,4,7,4,5,4],1),218558007380),
    (([1,5,8,3,7,5,9],1),([1,2,4,7,5,4,1],1),218568546020),
    (([1,5,8,9,7,8,1],1),([1,2,7,1,1,5,7],4),221231250740),
    (([1,8,8,4,4,1,1],4),([1,6,6,6,8,7,6],0),292318369900),
    (([1,9,8,8,2,7,1],4),([1,7,7,7,8,2,8],0),327096573500),
    (([2,4,8,4,2,2,7],4),([1,9,7,5,4,1,1],1),399293856160),
    (([2,5,5,8,4,1,7],1),([2,1,3,3,7,9,5],1),420586958320),
    (([2,5,6,4,2,6,8],2),([2,1,5,8,8,4,1],1),422712239960),
    (([2,7,4,5,2,2,5],3),([2,4,8,3,6,8,5],3),498850474120),
    (([2,7,4,7,1,5,4],1),([2,4,8,5,6,6,5],2),499964777800),
    (([2,7,4,7,3,7,3],4),([2,4,8,5,7,2,7],4),500031841160),
    (([2,7,4,7,4,5,5],2),([2,4,8,5,7,6,7],3),500072170120),
    (([3,2,1,1,4,1,1],3),([2,8,1,7,7,7,1],4),679148834708)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_4 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 680623768820≤n ∧ n≤15386784636260 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([3,2,3,1,1,5,2],4),([2,8,2,5,2,2,7],2),680623768820),
    (([3,2,4,1,3,5,8],1),([2,8,2,8,5,8,7],4),682103597780),
    (([3,2,4,3,4,3,6],3),([2,8,2,8,7,7,7],4),682249641428),
    (([3,2,7,2,8,4,5],3),([2,8,4,5,4,5,2],3),689657080100),
    (([5,7,8,8,4,5,5],3),([5,2,2,7,6,2,4],4),2313409196920),
    (([1,1,8,4,1,5,1,4],1),([9,2,5,7,6,6,4],0),7750524144400),
    (([1,4,5,8,4,1,7,4],1),([9,7,9,8,9,5,2],2),8835002458360),
    (([1,5,7,1,4,6,2,6],3),([1,1,8,5,4,1,7,4],1),9691970157380),
    (([1,5,7,1,5,1,1,2],2),([1,1,8,5,4,7,2,7],3),9692138882020),
    (([1,5,7,1,5,4,1,7],1),([1,1,8,5,4,7,9,1],2),9692181705220),
    (([1,9,5,1,3,7,3,7],4),([1,7,2,4,1,5,7,8],3),13954465683020),
    (([1,9,7,1,9,1,6,5],3),([1,7,5,7,7,2,1,7],2),14323608345440),
    (([2,1,8,9,4,5,9,2],1),([1,8,1,4,5,5,8,1],2),15372440430500),
    (([2,1,9,2,3,3,3,1],1),([1,8,1,7,2,1,4,2],3),15384035430164),
    (([2,1,9,3,1,3,4,5],2),([1,8,1,7,7,5,1,1],4),15386784636260)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_5 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 15391267980500≤n ∧ n≤103123720322120 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,1,9,4,1,7,2,7],4),([1,8,1,8,5,5,1,1],4),15391267980500),
    (([2,2,2,1,4,7,2,7],4),([1,8,2,9,3,2,5,5],0),15463655899900),
    (([2,2,4,4,5,7,2,1],1),([1,8,3,8,1,9,5,7],1),15546665786380),
    (([2,2,4,5,7,8,1,4],1),([1,8,3,8,6,7,5,3],1),15554171414860),
    (([2,2,6,9,5,3,1,3],2),([1,8,5,2,8,4,1,4],1),15745139124140),
    (([2,2,7,1,5,7,2,1],4),([1,8,5,3,9,8,1,3],4),15759416042620),
    (([2,2,7,4,8,2,4,5],3),([1,8,5,5,3,4,5,5],4),15778327039900),
    (([2,3,3,1,2,9,1,8],4),([1,8,7,4,4,4,8,2],0),16179595402700),
    (([2,3,3,7,5,8,1,7],2),([1,8,7,5,7,5,2,8],0),16213523699900),
    (([2,3,4,5,7,8,3,5],4),([1,8,7,7,5,1,1,7],4),16271192453420),
    (([2,3,4,5,9,3,4,7],4),([1,8,7,7,5,7,7,7],2),16273652175020),
    (([2,3,6,5,7,2,9,1],2),([1,8,8,5,7,4,5,8],3),16481776740500),
    (([2,3,6,5,7,9,9,4],2),([1,8,8,5,7,7,8,4],4),16483863119060),
    (([2,4,2,5,1,2,1,4],1),([1,9,3,1,3,1,8,6],0),17152181386900),
    (([5,7,7,8,4,9,5,2],3),([5,1,4,4,4,8,7,4],2),103123720322120)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_6 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 291803401145900≤n ∧ n≤583352898652420 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([9,5,2,1,8,7,7,3],1),([8,5,7,4,5,2,4,5],3),291803401145900),
    (([1,2,1,4,2,5,2,1,4],1),([9,3,1,2,1,2,9,5],0),351464373399400),
    (([1,2,1,4,2,8,8,1,1],4),([9,3,1,2,3,9,4,0],0),351465040191400),
    (([1,2,5,8,8,5,8,7,5],2),([9,3,9,2,2,9,5,3],4),355973525294920),
    (([1,4,2,1,4,4,5,1,2],2),([9,7,6,1,3,5,9,4],0),389454720631900),
    (([1,5,4,2,1,1,8,2,5],2),([9,9,8,2,8,5,7,9],4),423735753671620),
    (([1,5,7,8,2,2,8,5,4],4),([1,2,2,3,5,7,1,3,2],1),439759640093920),
    (([1,5,7,8,7,2,7,8,2],2),([1,2,2,8,3,9,5,9,7],1),440224134386560),
    (([1,5,7,8,7,4,4,4,4],1),([1,2,2,8,5,3,6,2,1],3),440240052934240),
    (([1,5,7,8,7,4,5,8,5],3),([1,2,2,8,5,4,9,9,7],2),440242206989920),
    (([1,5,8,5,3,6,2,7,8],1),([1,2,5,2,1,4,8,4,7],1),443472326911820),
    (([1,5,8,7,7,1,8,8,7],1),([1,2,6,1,5,4,7,6,9],3),445515159218380),
    (([1,5,9,4,1,1,1,9,7],1),([1,2,7,7,7,4,2,1,8],0),449569651911500),
    (([1,7,8,5,2,1,7,2,2],2),([1,5,5,6,3,7,4,2,2],1),535527836747800),
    (([1,8,7,5,4,7,5,8,5],3),([1,6,5,4,1,8,6,9,7],2),583352898652420)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_7 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 680249254174360≤n ∧ n≤870861088154920 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,1,1,1,4,2,2,5,7],1),([1,7,9,4,3,3,3,5,3],4),680249254174360),
    (([2,1,1,5,5,8,7,1,2],2),([1,7,9,4,4,3,8,8,5],3),680333158728520),
    (([2,1,4,1,4,1,5,1,1],4),([1,7,9,5,8,2,7,8,3],1),682245107752120),
    (([2,4,2,1,1,8,8,1,1],4),([1,9,2,9,5,1,1,6,9],0),771258487341400),
    (([2,5,5,7,5,1,1,4,1],4),([2,1,1,6,8,5,6,1,1],2),850485710903920),
    (([2,5,5,7,7,4,2,1,4],1),([2,1,2,3,9,5,9,4,7],2),850828639597720),
    (([2,5,5,7,8,1,2,5,2],2),([2,1,2,6,1,3,7,5,1],1),851002544759920),
    (([2,5,5,8,8,4,2,1,1],1),([2,1,3,8,7,5,8,4,8],3),852444404890120),
    (([2,5,7,6,7,3,9,8,6],3),([2,2,1,5,7,1,5,7,1],1),869221462809800),
    (([2,5,7,6,7,4,2,8,3],4),([2,2,1,5,7,4,4,8,4],2),869223532652120),
    (([2,5,7,6,7,4,2,8,4],1),([2,2,1,5,7,4,4,8,5],0),869223534157400),
    (([2,5,7,6,9,6,7,2,7],3),([2,2,2,1,4,5,5,2,1],4),869829898943000),
    (([2,5,7,7,6,2,9,1,4],2),([2,2,2,7,4,1,4,5,2],0),870633708874400),
    (([2,5,7,7,6,8,1,7,2],3),([2,2,2,7,8,5,2,1,4],2),870770250036080),
    (([2,5,7,7,7,1,2,5,1],4),([2,2,2,8,1,7,7,4,5],4),870861088154920)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_8 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 873119486799520≤n ∧ n≤9761839477216900 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,5,7,8,8,2,1,2,5],2),([2,2,3,8,4,8,4,3,5],4),873119486799520),
    (([2,5,8,3,5,1,1,5,8],3),([2,2,5,1,2,2,2,4,2],3),877299702924920),
    (([2,5,8,3,5,1,1,6,4],3),([2,2,5,1,2,2,2,7,1],1),877299705598520),
    (([2,5,8,8,2,1,8,1,1],1),([2,2,6,7,9,9,8,2,0],0),884537922729400),
    (([2,7,8,4,7,2,4,5,1],1),([2,5,5,6,9,3,3,1,3],1),1062491214662800),
    (([2,7,8,7,5,5,2,2,5],2),([2,5,6,2,3,9,2,3,8],1),1068627587675920),
    (([2,9,6,5,3,6,2,4,3],2),([2,7,4,8,1,2,4,8,2],0),1267336060515200),
    (([5,7,8,7,8,2,8,9,2],3),([5,2,1,4,2,4,1,5,5],3),4680704202964400),
    (([5,8,2,7,8,8,8,1,7],1),([5,2,9,8,5,6,2,3,5],4),4767643788397900),
    (([5,8,4,2,4,4,8,1,8],2),([5,3,4,3,8,1,5,9,6],2),4793871150285100),
    (([7,8,7,1,8,7,8,5,8],3),([6,9,8,1,3,1,1,6,5],0),9067434476331400),
    (([7,8,7,2,1,5,5,1,4],1),([6,9,8,1,5,7,2,9,3],3),9067849813447720),
    (([7,8,8,4,1,4,8,8,5],3),([6,9,8,9,4,1,1,9,5],1),9141438277315240),
    (([8,1,1,1,5,7,4,4,1],4),([7,4,6,8,4,9,6,5,6],1),9760424131454020),
    (([8,1,2,2,5,8,8,1,1],1),([7,4,6,8,6,8,9,9,5],0),9761839477216900)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_9 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 15820954945120780≤n ∧ n≤25261174064199400 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,2,1,7,2,8,4,4,5,8],2),([9,3,1,9,8,1,6,1,5],3),15820954945120780),
    (([1,5,6,1,7,4,1,1,4,4],3),([1,1,4,1,8,1,5,7,4,2],0),19403516251226900),
    (([1,5,6,1,7,4,1,1,4,6],4),([1,1,4,1,8,1,5,7,4,4],4),19403516252073620),
    (([1,5,6,1,7,4,1,1,8,7],1),([1,1,4,1,8,1,5,7,7,2],0),19403516270210900),
    (([1,5,6,1,7,4,1,2,9,9],3),([1,1,4,1,8,1,5,8,8,7],4),19403516347097780),
    (([1,5,6,3,8,6,3,5,3,3],3),([1,1,4,8,1,1,4,1,5,7],2),19426249648648820),
    (([1,5,7,5,1,1,5,5,7,7],1),([1,1,9,1,3,6,4,5,9,8],3),19683419526980170),
    (([1,6,9,3,2,3,8,8,5,1],3),([1,4,4,7,2,5,8,2,7,5],0),22163989023524900),
    (([1,7,5,4,8,5,1,7,8,5],3),([1,4,8,8,5,1,3,4,3,9],4),23113315689427420),
    (([1,7,5,4,8,5,5,7,4,4],4),([1,4,8,8,5,2,1,1,6,7],1),23113436946451420),
    (([1,7,6,9,1,4,5,1,4,1],1),([1,5,1,7,7,1,8,8,8,2],0),23575936587748400),
    (([1,7,6,9,3,9,7,7,9,5],2),([1,5,1,8,7,2,7,4,5,7],2),23583724771285100),
    (([1,7,8,2,5,4,8,4,4,7],1),([1,5,5,1,4,2,5,5,8,9],2),24018523901269900),
    (([1,7,9,5,4,9,6,5,9,6],3),([1,5,7,2,1,1,1,4,4,1],1),24538877727921020),
    (([1,8,4,2,5,8,2,8,7,7],1),([1,5,9,3,2,5,2,8,5,1],2),25261174064199400)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_10 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 34791914841397900≤n ∧ n≤167860058387304400 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,4,2,8,7,5,8,8,1,7],1),([1,9,3,5,3,8,4,2,7,3],0),34791914841397900),
    (([2,4,4,8,2,1,5,4,4,8],2),([1,9,4,7,5,5,8,3,1,1],1),35155282515981100),
    (([4,7,1,1,7,4,4,9,5,7],1),([4,2,1,1,5,1,2,1,5,4],1),134530926321854000),
    (([4,7,1,2,5,8,2,5,2,4],4),([4,2,1,3,3,6,8,5,7,7],4),134536012091483920),
    (([4,7,1,7,2,8,5,7,2,2],2),([4,2,2,4,4,9,5,4,4,7],3),134627992762262560),
    (([4,7,1,7,3,4,7,6,9,5],2),([4,2,2,4,5,7,1,1,2,8],0),134628861462298400),
    (([4,7,1,7,6,5,9,8,2,8],3),([4,2,2,5,1,4,4,4,2,1],4),134638560102866240),
    (([4,7,2,1,2,8,7,1,2,7],4),([4,2,2,9,6,9,7,3,3,5],3),134738399425093360),
    (([4,7,2,5,8,4,1,2,1,2],2),([4,2,3,7,2,7,5,3,1,8],2),134860940054017360),
    (([4,7,3,7,2,6,5,2,4,6],1),([4,2,5,7,1,8,4,5,7,4],1),135453115141086800),
    (([4,7,4,2,4,7,4,7,5,8],3),([4,2,6,6,4,3,2,5,7,6],0),135809371502742400),
    (([4,7,8,2,7,2,4,1,5,1],1),([4,3,7,5,6,8,9,1,5,3],3),140460031072376800),
    (([4,8,7,7,2,2,1,1,2,7],4),([4,5,1,7,3,7,9,9,7,2],1),149754496308433360),
    (([4,8,7,7,3,6,7,5,8,9],4),([4,5,1,7,8,8,4,4,2,1],4),149772791734659920),
    (([5,1,8,1,1,8,4,8,1,1],1),([4,6,9,9,5,5,8,3,4,5],2),167860058387304400)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_11 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 168166993748382380≤n ∧ n≤188328362662472420 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([5,1,9,2,2,6,8,9,7,9],3),([4,7,1,2,2,5,1,1,2,4],1),168166993748382380),
    (([5,1,9,2,5,5,8,1,6,1],3),([4,7,1,2,5,8,8,8,2,1],4),168170176158422420),
    (([5,1,9,3,9,6,9,1,2,7],1),([4,7,1,4,5,4,4,2,7,5],0),168201226536712400),
    (([5,2,1,8,4,7,4,8,1,8],3),([4,7,2,5,3,6,7,5,6,1],2),168544058036438500),
    (([5,2,1,8,4,8,1,7,7,7],4),([4,7,2,5,3,6,9,1,3,6],2),168544209628590820),
    (([5,2,2,1,9,1,6,7,8,4],4),([4,7,2,5,7,8,8,8,8,8],3),168572596790399420),
    (([5,2,2,5,7,4,5,2,4,5],3),([4,7,2,6,4,9,5,2,3,1],2),168611295017071420),
    (([5,2,2,5,8,7,5,2,8,4],1),([4,7,2,6,5,6,3,9,3,6],2),168614964653545420),
    (([5,2,2,5,8,7,8,7,4,1],1),([4,7,2,6,5,6,6,1,7,7],4),168615185557350220),
    (([5,2,2,9,2,6,2,1,3,9],1),([4,7,2,7,5,8,5,5,5,5],0),168690618895079900),
    (([5,3,9,3,5,8,5,4,9,1],2),([4,7,8,5,4,1,8,4,2,1],4),175981037656284920),
    (([5,3,9,5,1,9,7,4,8,6],4),([4,7,8,5,8,8,2,1,8,1],2),176120297097444920),
    (([5,5,1,1,5,6,6,9,3,4],2),([4,8,5,7,2,8,2,4,2,1],4),183629916109472420),
    (([5,5,5,9,3,9,9,7,9,9],3),([4,8,7,2,4,4,5,4,2,1],4),186269220514472420),
    (([5,5,7,7,9,3,3,5,6,1],3),([4,8,8,1,7,5,4,4,2,1],4),188328362662472420)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_12 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 267378351711111020≤n ∧ n≤1392268994749948120 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([6,5,7,1,5,8,3,4,6,1],1),([5,8,1,2,1,1,2,1,7,1],1),267378351711111020),
    (([1,1,5,8,1,8,2,5,8,7,5],2),([9,1,4,3,8,9,3,6,5,3],1),700903611957232420),
    (([1,2,1,7,5,5,1,1,5,1,8],3),([9,3,2,1,4,1,6,6,4,5],1),711963466191086920),
    (([1,2,1,8,1,2,8,4,5,2,4],4),([9,3,2,4,5,8,3,9,3,3],1),712042395310499920),
    (([1,2,1,8,7,8,1,7,2,1,4],4),([9,3,2,5,8,3,3,7,1,4],1),712109669015248720),
    (([1,5,5,8,8,2,1,8,5,9,3],3),([1,1,1,7,1,1,8,1,5,7,7],4),870808867740293420),
    (([1,5,9,2,5,1,5,1,2,6,2],2),([1,2,7,5,7,7,2,8,4,7,2],3),908846856338427920),
    (([1,7,7,4,7,7,4,1,4,4,5],2),([1,5,3,3,7,5,8,4,2,4,5],1),1066724286501670900),
    (([1,7,8,8,4,2,8,5,2,1,7],1),([1,5,6,3,5,7,7,9,9,5,7],4),1092391354906680400),
    (([1,8,5,8,8,8,2,2,4,8,2],2),([1,6,2,3,3,7,4,8,7,1,2],0),1157260049970833500),
    (([1,8,8,5,8,2,4,8,2,2,7],4),([1,6,6,8,3,5,7,2,7,8,6],2),1201847081968085020),
    (([1,8,8,8,5,2,4,1,4,8,4],1),([1,6,7,4,3,5,1,6,6,5,9],3),1209817651701161500),
    (([1,9,9,1,1,8,3,2,1,1,5],1),([1,7,8,1,1,7,8,5,1,8,8],0),1350270745277807900),
    (([2,1,7,2,7,2,2,1,5,2,2],2),([1,7,9,8,5,9,8,9,6,8,5],1),1391830456118012800),
    (([2,1,7,4,2,5,4,7,7,5,7],1),([1,7,9,8,6,8,5,1,4,8,1],1),1392268994749948120)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_13 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 1561916239281804400≤n ∧ n≤9430094779280318920 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,4,2,2,1,2,5,4,8,1,1],1),([1,9,2,9,5,8,6,9,3,3,7],0),1561916239281804400),
    (([2,4,2,2,2,1,5,4,8,1,1],1),([1,9,2,9,5,8,7,9,8,9,9],0),1561921435593804400),
    (([2,4,2,5,1,1,4,4,8,1,1],1),([1,9,3,1,3,1,1,5,1,6,9],0),1562992276086804400),
    (([2,4,2,7,5,2,1,7,2,8,7],1),([1,9,3,4,1,5,8,8,6,9,2],1),1564495662942360880),
    (([2,4,5,7,8,8,1,8,2,1,7],1),([1,9,5,5,3,4,2,6,3,5,2],2),1593822339813180400),
    (([2,4,7,4,5,5,2,8,8,4,4],4),([1,9,6,6,9,5,7,1,4,6,2],2),1618530429351623920),
    (([2,5,5,7,3,6,4,1,7,4,6],2),([2,1,1,1,7,5,7,1,4,1,8],3),1721887909699180520),
    (([2,5,5,7,5,5,8,1,5,2,1],1),([2,1,1,7,6,5,1,9,2,8,6],2),1722318251733338920),
    (([2,5,6,2,2,3,6,4,1,9,6],1),([2,1,5,4,8,4,8,8,8,4,1],2),1731092271610783160),
    (([2,5,7,1,1,5,1,2,4,4,8],3),([2,1,8,9,1,2,1,5,8,9,6],3),1750801083134881120),
    (([5,7,8,2,2,2,8,2,8,1,7],1),([5,1,7,1,1,9,9,4,6,8,2],0),9427416628984635400),
    (([5,7,8,2,7,2,4,2,5,1,8],3),([5,1,7,3,9,7,8,1,1,1,4],3),9429285729438360520),
    (([5,7,8,2,7,2,5,2,2,2,2],3),([5,1,7,3,9,7,8,7,2,6,4],4),9429288293361557320),
    (([5,7,8,2,7,5,1,7,5,2,2],3),([5,1,7,4,2,4,9,7,1,3,4],4),9429412798239206920),
    (([5,7,8,2,8,5,4,1,7,5,5],2),([5,1,7,4,7,7,7,8,6,4,7],2),9430094779280318920)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_14 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 11465741592220802600≤n ∧ n≤48609514251668541220 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([6,4,2,3,3,7,1,5,6,1,4],2),([5,7,4,4,1,7,5,4,1,4,7],1),11465741592220802600),
    (([8,3,4,8,2,5,3,8,1,7,1],1),([7,5,4,8,2,7,5,7,2,5,8],0),20196752370915179900),
    (([1,1,7,1,4,4,1,8,1,5,1,7],4),([9,1,9,5,3,1,8,6,2,8,9],2),31660204071765090220),
    (([1,1,7,4,8,4,1,7,7,2,7,5],2),([9,1,9,9,2,9,9,7,9,5,5],1),31680070865559875500),
    (([1,1,8,2,2,1,5,2,4,8,1,1],1),([9,2,5,4,6,8,9,1,9,1,9],0),31768608514516554400),
    (([1,1,8,2,2,2,1,4,2,2,1,1],4),([9,2,5,4,6,8,9,5,7,5,2],3),31768612661853930400),
    (([1,1,8,2,5,5,5,7,5,8,8,7],1),([9,2,5,4,9,1,1,3,8,8,9],4),31769834901100133920),
    (([1,2,1,4,7,8,4,2,2,5,8,4],4),([9,3,1,4,4,7,4,7,6,8,5],3),32028630382792918420),
    (([1,2,1,5,4,1,8,4,4,2,1,1],1),([9,3,1,5,8,1,7,3,6,2,8],0),32030247498251056900),
    (([1,5,7,2,2,2,8,3,6,6,9,8],3),([1,1,8,5,8,8,8,5,8,2,7,1],2),39753557972104217600),
    (([1,5,7,2,2,7,8,5,1,2,1,2],2),([1,1,8,5,8,9,7,9,9,6,8,4],1),39754100980781422720),
    (([1,5,7,2,7,1,5,2,7,8,8,5],2),([1,1,8,6,5,9,2,6,1,1,4,4],4),39763986282183164920),
    (([1,7,7,7,7,4,1,2,2,4,4,5],2),([1,5,4,2,5,4,8,4,9,5,8,6],1),48270240811107813400),
    (([1,7,7,7,7,8,5,5,5,4,7,4],1),([1,5,4,2,9,2,9,7,9,2,4,6],1),48279809581562597920),
    (([1,7,8,1,1,1,8,2,2,7,1,4],4),([1,5,4,9,8,4,4,8,4,1,9,4],2),48609514251668541220)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_15 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 422823610080475977400≤n ∧ n≤1004242667091207510400 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([5,7,7,8,4,2,2,8,8,4,4,2],2),([5,1,4,2,2,5,3,5,2,4,6,5],3),422823610080475977400),
    (([5,7,7,8,4,2,4,1,7,2,7,8],2),([5,1,4,2,2,7,5,6,5,2,8,3],4),422823816511108329400),
    (([5,9,1,2,1,1,2,4,8,6,7,2],3),([5,4,8,8,5,5,2,7,8,1,8,2],0),460395114577609754900),
    (([7,9,1,3,9,3,8,4,9,9,1,5],2),([7,1,7,5,4,8,2,1,5,4,4,5],3),846629930276689052900),
    (([7,9,1,6,3,3,5,6,6,5,8,1],3),([7,1,7,7,2,4,1,1,8,8,5,4],1),846841107685987406720),
    (([7,9,3,8,2,5,7,2,4,8,4,6],1),([7,2,4,1,1,2,4,8,4,5,4,2],0),851171583820289425400),
    (([7,9,3,9,3,3,9,1,8,8,5,6],1),([7,2,4,7,5,4,4,7,7,4,7,2],3),851705288985792011960),
    (([7,9,4,1,2,2,1,6,7,5,3,6],1),([7,2,5,1,4,8,5,5,1,4,2,5],0),852236586554055329900),
    (([7,9,4,2,8,2,6,7,7,1,5,8],1),([7,2,5,4,4,5,7,1,7,4,2,7],2),852426043113706575500),
    (([7,9,5,1,2,4,7,4,9,7,2,4],2),([7,2,7,7,4,4,4,4,2,8,8,5],3),856051479549061551560),
    (([7,9,5,4,9,7,5,6,9,2,4,1],4),([7,2,8,2,5,1,1,4,8,4,2,1],4),857066017526297222420),
    (([7,9,5,4,9,7,7,4,4,3,8,2],2),([7,2,8,2,5,5,7,2,8,7,8,2],3),857068893933786852500),
    (([7,9,5,5,1,8,7,5,4,8,1,9],1),([7,2,8,2,8,8,8,4,1,2,5,1],1),857116021019109782420),
    (([8,4,8,1,4,2,5,2,7,2,1,7],1),([7,6,3,3,9,2,8,9,6,3,9,6],0),935677952118300630400),
    (([8,7,1,7,4,4,1,8,8,8,7,7],4),([7,7,9,5,5,7,6,2,3,4,3,5],4),1004242667091207510400)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_16 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 1004285512141896342400≤n ∧ n≤1425404260852318933360 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([8,7,1,7,7,2,2,4,2,2,5,8],3),([7,7,9,5,5,9,8,5,8,6,4,2],0),1004285512141896342400),
    (([9,3,2,2,9,4,5,9,7,1,3,3],2),([8,4,2,4,5,5,5,1,4,1,8,2],0),1153426773209646742400),
    (([9,3,5,9,1,1,2,8,9,7,3,3],2),([8,4,5,1,2,8,8,5,5,4,5,7],4),1158690289804797022400),
    (([9,4,8,5,4,3,2,7,7,9,3,3],3),([8,5,5,2,8,8,2,5,2,4,5,7],4),1187647920177081397400),
    (([9,5,1,1,7,9,9,2,6,7,4,7],2),([8,5,7,2,1,5,4,5,5,4,7,1],2),1195882891158105502400),
    (([9,5,4,7,2,4,1,3,8,4,3,1],3),([8,5,8,2,4,7,4,4,4,7,1,2],0),1201242795652103146400),
    (([9,8,3,3,8,5,6,2,9,3,9,7],1),([8,8,4,2,1,7,5,4,1,4,1,8],0),1309830062390948896400),
    (([9,8,3,6,7,7,8,8,4,7,3,8],4),([8,8,4,5,1,5,2,5,4,5,5,1],2),1310798906049920992400),
    (([9,8,4,6,8,4,5,5,1,5,4,6],3),([8,8,5,1,2,1,2,2,7,8,8,1],2),1314565785858784419920),
    (([9,8,4,7,3,5,3,1,2,3,8,9],3),([8,8,5,2,7,2,7,8,5,7,2,1],4),1314824859400567163600),
    (([9,8,4,7,3,5,3,2,6,2,1,8],1),([8,8,5,2,7,2,7,8,7,5,8,4],2),1314824871641496597200),
    (([9,8,4,7,3,6,4,5,3,4,2,6],1),([8,8,5,2,7,4,7,7,5,1,8,8],3),1314830473597503102800),
    (([9,8,4,7,3,9,1,9,2,9,1,8],4),([8,8,5,2,7,8,5,5,8,2,2,4],4),1314850802434214200400),
    (([1,1,2,8,1,4,7,1,1,8,4,5,5],3),([8,9,9,7,3,9,3,8,5,4,6,3],2),1411921962832423201720),
    (([1,1,7,4,4,7,4,1,2,1,1,2,7],4),([9,1,9,8,6,3,4,8,5,3,6,8],4),1425404260852318933360)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_17 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 1443990780236644198720≤n ∧ n≤1803189061310759379920 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,2,2,7,8,8,8,5,4,5,7,8,4],1),([9,3,3,9,3,1,3,3,6,7,6,5],2),1443990780236644198720),
    (([1,4,2,2,2,7,8,5,4,2,5,8,1],4),([9,7,6,1,9,2,8,2,4,5,1,1],3),1597122557851788325420),
    (([1,4,2,5,8,2,8,8,2,7,2,1,5],2),([9,7,6,5,1,1,9,7,4,3,8,4],3),1598583224707749303820),
    (([1,4,2,5,8,4,1,7,8,2,2,1,7],1),([9,7,6,5,1,7,5,5,1,7,3,9],4),1598591790377789317900),
    (([1,4,7,5,5,5,7,1,7,1,7,2,1],1),([9,8,6,6,5,9,4,2,9,2,6,7],4),1656243777696014503420),
    (([1,4,8,8,8,4,7,2,7,1,2,5,4],4),([9,8,9,6,7,1,5,9,1,8,1,2],1),1686630478145312719420),
    (([1,5,5,9,2,5,8,7,3,1,6,2,3],3),([1,1,2,7,1,8,4,4,5,4,4,8,1],2),1764640255311716094920),
    (([1,5,7,5,1,2,4,4,1,5,5,8,8],3),([1,1,9,1,3,7,2,8,2,1,2,5,6],2),1793652960445415596420),
    (([1,5,7,5,1,2,4,4,4,4,4,5,2],2),([1,1,9,1,3,7,2,8,5,3,4,4,2],1),1793652963353372620420),
    (([1,5,7,5,4,1,5,8,2,5,5,8,5],3),([1,1,9,2,7,8,9,2,2,8,1,5,1],1),1794005918029843313920),
    (([1,5,7,7,7,5,7,7,1,4,5,8,1],1),([1,2,1,2,6,9,9,9,7,5,3,3,3],4),1801370722244147969920),
    (([1,5,7,7,9,9,7,4,6,5,2,8,1],4),([1,2,2,2,5,2,7,2,4,8,4,8,1],2),1803110172367397094920),
    (([1,5,7,8,1,1,3,4,1,5,2,1,2],1),([1,2,2,2,8,7,8,8,2,4,5,7,7],4),1803185606987884770320),
    (([1,5,7,8,1,2,6,3,2,5,5,9,6],2),([1,2,2,2,8,8,7,2,4,5,1,2,1],4),1803188974857482259920),
    (([1,5,7,8,1,2,6,5,1,8,4,8,3],4),([1,2,2,2,8,8,7,4,4,1,5,1,1],4),1803189061310759379920)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_18 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 1803189061471071699920≤n ∧ n≤2790892894895340899920 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,5,7,8,1,2,6,5,1,8,9,5,2],2),([1,2,2,2,8,8,7,4,4,2,5,2,1],2),1803189061471071699920),
    (([1,5,7,8,1,2,6,5,2,9,3,1,1],2),([1,2,2,2,8,8,7,4,4,7,1,2,5],3),1803189064025785607120),
    (([1,5,7,8,5,2,2,8,4,7,4,7,1],1),([1,2,2,6,1,6,3,3,8,4,5,2,9],2),1804138631583021650320),
    (([1,5,7,8,5,7,1,5,2,8,1,1,5],2),([1,2,2,6,7,1,3,6,6,5,3,4,2],3),1804347184177440383920),
    (([1,5,8,6,6,1,8,5,2,2,8,4,1],1),([1,2,5,7,4,4,1,8,8,7,7,1,1],4),1822487931722525877020),
    (([1,5,8,7,5,2,5,5,8,7,5,1,7],4),([1,2,5,9,6,8,6,9,3,1,6,8,9],2),1825859643594000751420),
    (([1,5,8,7,8,2,5,2,2,1,4,5,2],2),([1,2,6,3,3,2,2,3,3,2,9,6,5],1),1827563061858827995420),
    (([1,8,7,2,1,7,2,1,8,7,2,5,8],3),([1,6,4,8,8,9,3,8,5,5,4,2,6],0),2383743683121658954900),
    (([1,8,7,2,4,2,7,4,8,8,2,7,7],4),([1,6,4,8,9,4,2,8,4,7,8,8,0],0),2383958646532000186900),
    (([1,8,7,2,4,5,1,5,4,2,8,4,4],4),([1,6,4,8,9,4,7,1,5,9,6,8,2],2),2383985535856847686420),
    (([1,8,7,2,4,5,5,1,7,2,8,4,5],2),([1,6,4,8,9,4,7,6,5,7,6,1,3],1),2383989187194272134420),
    (([1,9,6,6,3,5,4,1,7,1,6,2,9],4),([1,7,4,8,2,8,1,2,1,5,4,2,1],4),2618232232322929284920),
    (([2,1,2,1,7,4,4,8,8,2,2,7,4],1),([1,7,9,4,6,4,9,9,4,3,4,4,8],1),2790834694639249479568),
    (([2,1,2,1,7,4,8,1,7,7,2,7,5],2),([1,7,9,4,6,4,9,9,5,8,5,9,9],1),2790835051054208938000),
    (([2,1,2,2,5,2,5,1,8,2,8,5,8],3),([1,7,9,4,6,5,8,9,9,7,6,1,3],2),2790892894895340899920)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_19 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 3310802144871854904232≤n ∧ n≤5442298099765917586400 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,4,8,2,2,8,2,2,7,2,4,1,8],3),([1,9,7,4,4,4,8,9,4,8,4,9,1],2),3310802144871854904232),
    (([2,5,5,7,6,8,2,2,3,2,4,2,1],3),([2,1,2,1,8,2,5,7,1,8,1,4,4],1),3488553824684695766120),
    (([2,5,5,8,1,4,5,4,8,2,4,2,5],2),([2,1,2,9,8,3,4,6,5,2,8,2,3],3),3491663479233809468920),
    (([2,5,7,6,6,2,9,6,6,4,2,2,4],3),([2,2,1,1,4,1,5,5,4,1,2,5,5],0),3563427789236300767400),
    (([2,5,7,6,6,8,2,9,2,8,3,5,5],2),([2,2,1,4,4,1,2,7,5,8,4,8,1],2),3563912054601797094920),
    (([2,5,8,9,7,2,2,3,7,6,6,6,7],3),([2,2,7,5,7,8,7,1,4,7,4,7,2],3),3641747220363465761960),
    (([2,5,9,6,9,9,3,2,3,2,2,3,6],3),([2,2,8,8,2,1,2,4,7,7,4,1,5],0),3675816832052931586400),
    (([2,7,7,1,1,1,1,7,8,4,8,5,8],3),([2,5,2,9,7,4,9,4,3,8,8,4,8],0),4276774478667695826400),
    (([2,7,7,1,1,5,2,2,4,8,7,5,8],2),([2,5,2,9,7,4,9,9,8,4,4,1,6],4),4276781879748267915520),
    (([2,7,7,2,8,4,5,4,7,1,5,8,4],4),([2,5,3,3,1,2,6,3,8,7,2,4,1],1),4280184828450521933920),
    (([2,8,5,8,4,1,4,8,1,7,2,1,5],2),([2,6,2,4,6,9,1,5,3,2,1,3,2],4),4649751014908186991320),
    (([2,8,8,1,7,1,4,8,5,1,8,4,2],3),([2,6,6,6,5,3,8,9,2,5,7,3,9],4),4811593598814082931800),
    (([2,8,8,1,8,1,8,5,8,2,7,1,5],3),([2,6,6,6,5,6,9,7,6,1,2,9,8],1),4811898798257794924120),
    (([2,8,8,2,5,1,8,1,2,7,2,1,7],1),([2,6,6,6,7,1,5,7,6,9,9,8,9],0),4813492321447045005400),
    (([2,9,9,2,7,6,9,4,1,9,5,7,7],1),([2,7,8,4,2,1,8,4,1,7,4,1,5],0),5442298099765917586400)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_20 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 5450816127434573896400≤n ∧ n≤23858571042442047808640 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,9,9,3,9,5,4,7,9,4,6,2,2],1),([2,7,8,5,2,1,4,4,4,1,4,1,8],0),5450816127434573896400),
    (([2,9,9,6,7,5,7,1,7,9,1,6,5],1),([2,7,8,7,7,5,8,4,8,2,4,4,4],4),5481486845534898737120),
    (([4,4,1,1,1,1,4,1,4,2,2,1,1],4),([3,8,5,8,1,5,6,9,4,8,8,5,7],3),10420188954412909867900),
    (([4,4,1,1,4,8,2,1,5,7,7,2,8],2),([3,8,5,8,1,6,6,6,7,8,5,9,7],3),10420234701888985733500),
    (([4,4,1,1,5,1,4,1,1,4,8,1,1],1),([3,8,5,8,1,6,7,6,9,9,8,1,3],0),10420242826560050491900),
    (([4,4,1,1,5,1,5,4,7,7,8,2,4],4),([3,8,5,8,1,6,7,7,2,6,2,3,1],3),10420242891830542711420),
    (([4,4,1,1,7,1,4,8,2,2,7,8,4],4),([3,8,5,8,1,7,7,7,6,7,4,7,1],2),10420302094299229433020),
    (([4,4,1,1,7,5,2,4,2,7,7,2,8],3),([3,8,5,8,1,7,8,6,1,5,6,5,7],1),10420310424843481867900),
    (([4,4,1,5,2,1,7,8,2,2,2,4,7],1),([3,8,5,8,4,3,5,7,2,8,7,1,6],0),10422637895213118979900),
    (([4,5,8,5,4,8,5,7,4,5,1,7,1],4),([3,9,5,4,4,6,4,9,4,4,1,4,7],2),11318435629018496551420),
    (([5,7,7,7,4,6,4,1,5,5,3,7,3],1),([5,1,1,2,8,8,8,7,8,1,2,8,1],1),19001359083262961664920),
    (([5,7,9,8,7,7,8,3,4,6,8,6,7],2),([5,2,8,1,5,5,5,1,2,4,4,5,2],3),19431388560535001692400),
    (([5,8,4,2,8,2,1,2,2,7,8,4,2],3),([5,3,4,4,5,2,4,3,9,4,3,9,4],1),19660173301551661294300),
    (([6,4,8,1,6,3,3,5,2,2,3,6,8],1),([5,7,7,2,7,2,2,5,4,7,7,5,2],0),23658026911487300842400),
    (([6,4,9,7,3,6,7,6,4,6,7,6,8],4),([5,7,8,1,4,7,8,7,7,1,2,4,1],1),23858571042442047808640)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_21 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 23899366172071640007200≤n ∧ n≤89684183026257464282420 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([6,4,9,8,8,9,3,1,5,6,3,4,8],1),([5,7,8,4,7,2,5,1,1,7,7,7,1],2),23899366172071640007200),
    (([1,1,5,7,4,2,2,7,4,8,2,2,4,8],3),([9,1,3,5,4,8,7,3,9,7,9,6,4],1),63848855017362348913660),
    (([1,1,7,5,5,7,5,4,2,4,1,4,4,2],3),([9,2,1,2,5,3,3,8,7,1,6,4,1],3),64165521936774022772920),
    (([1,1,7,7,4,8,1,5,2,8,2,7,5,5],3),([9,2,3,4,3,9,5,6,9,2,2,9,7],3),64217627042027211851920),
    (([1,1,8,1,4,8,4,2,2,7,5,8,4,2],3),([9,2,5,3,8,5,6,6,8,2,4,3,4],4),64326778980336802331800),
    (([1,5,5,8,8,2,4,4,6,9,5,3,7,9],2),([1,1,1,7,2,2,8,1,8,5,4,4,2,1],4),79352601897786194034920),
    (([1,5,6,1,7,3,2,9,5,8,2,5,6,3],1),([1,1,4,1,7,8,2,8,2,4,5,1,8,1],2),79566344727573482132420),
    (([1,5,6,1,7,3,3,9,4,4,3,6,9,4],4),([1,1,4,1,7,8,4,8,1,1,5,4,2,1],4),79566357772953001472420),
    (([1,5,6,1,7,3,6,5,2,9,7,2,2,2],4),([1,1,4,1,7,8,8,8,1,5,2,1,8,1],2),79566409031841534632420),
    (([1,5,6,1,7,7,9,7,7,8,2,1,8,8],2),([1,1,4,2,2,5,5,5,5,4,8,5,4,7],2),79568053467986301779900),
    (([1,5,6,1,7,9,4,2,5,5,1,4,2,4],2),([1,1,4,2,4,2,2,7,5,4,8,1,8,1],2),79568749136440853132420),
    (([1,5,6,1,8,1,7,6,4,3,5,6,7,5],1),([1,1,4,2,5,1,2,1,7,8,8,4,8,1],2),79569340211061169907420),
    (([1,5,7,7,4,5,1,1,8,5,1,2,5,7],4),([1,1,9,9,4,7,7,8,5,9,6,9,9,3],2),81002039829288674288920),
    (([1,6,8,5,6,2,7,2,1,5,6,1,5,9],2),([1,4,1,2,7,4,1,1,7,1,5,2,2,7],1),89684182581993169178420),
    (([1,6,8,5,6,2,7,2,3,3,5,2,1,3],4),([1,4,1,2,7,4,1,5,1,4,8,4,8,1],2),89684183026257464282420)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_22 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 89839475103861900122420≤n ∧ n≤102956865626997549097400 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,6,8,6,5,4,6,7,6,1,8,5,6,1],4),([1,4,2,2,4,4,1,8,2,1,5,7,2,1],4),89839475103861900122420),
    (([1,6,9,7,4,4,6,9,3,9,7,5,7,1],2),([1,4,5,7,4,2,2,4,2,4,1,4,1,8],0),91583407106889966083900),
    (([1,7,5,8,2,2,8,7,4,7,7,7,2,2],2),([1,4,9,2,6,2,5,1,7,7,4,4,3,3],3),95244998822111816260180),
    (([1,8,1,1,2,4,7,4,7,7,1,2,5,8],3),([1,5,8,3,6,8,6,5,1,4,3,4,5,5],4),102081240922542084777400),
    (([1,8,1,1,5,2,1,2,2,5,7,5,8,4],1),([1,5,8,3,6,8,9,1,4,8,1,1,3,2],3),102082301072794793732920),
    (([1,8,1,2,4,2,7,2,4,5,4,2,1,7],1),([1,5,8,3,7,4,5,7,5,6,6,3,8,9],1),102088019651511678105400),
    (([1,8,1,2,4,8,5,7,8,1,1,2,1,7],1),([1,5,8,3,7,4,8,7,4,8,3,3,9,9],0),102088629542757843705400),
    (([1,8,2,4,8,4,2,7,1,5,1,8,4,2],3),([1,5,8,5,9,4,9,8,8,3,9,4,4,9],2),102419800823026692431800),
    (([1,8,2,8,5,2,1,1,4,7,1,4,2,7],1),([1,5,8,7,1,2,5,4,2,3,5,3,8,2],3),102650921375968439769400),
    (([1,8,3,4,4,6,6,1,9,2,2,2,5,2],2),([1,5,8,8,4,1,5,4,1,8,4,5,4,7],1),102925550504444255305400),
    (([1,8,3,4,4,6,8,6,4,9,3,9,2,7],4),([1,5,8,8,4,1,8,8,5,8,4,1,5,1],4),102925822210898075593400),
    (([1,8,3,4,4,9,8,1,1,1,9,9,1,5],1),([1,5,8,8,4,4,2,5,7,2,7,5,5,5],3),102928725507284775817400),
    (([1,8,3,4,5,3,9,3,8,8,8,2,6,7],1),([1,5,8,8,4,4,8,4,4,7,2,4,5,5],3),102930047595147122953400),
    (([1,8,3,4,7,9,5,3,6,4,4,6,7,1],3),([1,5,8,8,5,4,2,4,7,7,7,5,4,2],3),102953753884079887993400),
    (([1,8,3,4,8,4,1,1,9,8,7,3,6,8],4),([1,5,8,8,5,5,4,4,7,7,7,5,4,1],1),102956865626997549097400)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_23 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 103585824784581738757720≤n ∧ n≤694007840958969225601420 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,8,4,2,5,7,2,4,7,7,5,8,1,7],1),([1,5,9,3,2,3,4,2,7,2,1,6,4,9],4),103585824784581738757720),
    (([2,4,2,5,7,2,4,7,2,4,7,8,7,4],1),([1,9,3,2,3,6,6,1,8,2,4,2,7,3],0),142453345923052368538300),
    (([2,4,4,4,1,1,1,2,5,2,2,2,1,1],1),([1,9,4,4,5,5,7,2,6,2,6,5,6,2],3),143675282194345216231900),
    (([2,4,4,5,2,1,4,1,8,2,7,2,1,7],1),([1,9,4,4,9,9,7,9,3,1,8,1,6,6],0),143764887634417456567900),
    (([4,6,8,9,9,5,9,6,8,6,8,2,6,4],2),([4,1,1,8,7,1,4,4,8,1,4,4,4,8],0),544872181784616795854000),
    (([4,8,8,4,4,7,2,4,5,8,5,5,8,4],4),([4,5,4,4,8,1,1,9,6,7,6,7,2,6],4),618891597186815061113920),
    (([4,8,8,4,4,7,2,4,6,7,5,8,7,4],1),([4,5,4,4,8,1,2,2,2,7,8,2,5,1],1),618891601201969637211200),
    (([4,8,8,4,4,7,2,4,8,4,7,8,9,2],4),([4,5,4,4,8,1,2,5,2,5,8,2,4,4],1),618891610854399515278400),
    (([4,8,8,4,4,7,4,2,8,4,4,2,2,7],4),([4,5,4,4,8,1,9,9,9,2,1,3,8,2],4),618892643874609319935040),
    (([5,1,1,2,8,7,7,1,7,7,2,7,4,2],3),([4,6,9,6,1,1,9,5,1,7,1,3,7,4],2),684048671422599523039540),
    (([5,1,2,1,8,7,7,8,2,2,2,2,4,8],3),([4,6,9,6,4,2,5,3,8,6,4,9,3,2],4),684198512187621180538660),
    (([5,1,9,1,6,5,1,7,7,4,7,5,3,8],3),([4,7,1,1,4,2,8,7,8,2,1,8,5,8],3),689567706295021910849420),
    (([5,2,4,1,7,2,8,4,2,8,7,4,4,5],2),([4,7,3,1,3,3,2,2,8,5,7,7,1,2],3),692787290244331619267620),
    (([5,2,4,5,1,5,7,4,4,4,2,1,5,1],1),([4,7,3,3,5,4,1,9,3,9,4,2,8,9],4),693047604266669855836420),
    (([5,2,5,1,5,2,2,5,1,2,2,8,1,7],4),([4,7,3,6,6,4,7,2,7,5,8,9,2,2],1),694007840958969225601420)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_24 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 694372017747257670376420≤n ∧ n≤3671378131841190117334420 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([5,2,5,5,4,7,8,5,4,1,5,1,8,4],4),([4,7,3,7,4,7,3,7,3,8,7,4,5,7],2),694372017747257670376420),
    (([5,2,6,5,6,4,7,1,3,9,7,5,3,7],1),([4,7,4,1,4,4,4,4,5,1,1,1,8,1],2),696013934889126508007420),
    (([5,5,4,4,1,5,1,1,7,1,2,5,5,7],1),([4,8,6,5,4,7,6,3,3,6,7,1,4,7],1),757999687091742438863920),
    (([5,5,4,7,5,2,8,2,5,7,5,8,5,2],2),([4,8,6,6,7,1,4,8,4,4,1,5,8,1],4),759128452220363333063920),
    (([8,4,8,4,1,5,5,7,8,2,5,1,5,2],3),([7,6,3,6,1,1,7,8,8,5,3,9,1,1],2),1895774076746899578608920),
    (([1,1,7,1,1,5,2,4,2,4,4,4,7,2,8],2),([9,1,9,4,9,9,6,6,7,6,6,8,5,5],1),2885006001916944581258500),
    (([1,2,1,4,4,8,5,7,1,2,8,1,8,4,2],3),([9,3,1,2,9,5,8,3,8,9,2,1,5,9],2),2918517195907540704806800),
    (([1,2,2,5,4,7,5,8,1,8,1,7,4,7,1],1),([9,3,3,4,9,3,1,7,2,7,6,5,7,7],3),2922195679992756458525320),
    (([1,2,4,4,2,4,1,1,5,2,8,7,2,1,7],1),([9,3,6,6,4,1,9,5,2,4,7,9,1,8],0),2936149335869610209880400),
    (([1,2,7,8,7,1,8,2,5,1,2,2,2,4,8],3),([9,4,6,7,3,4,5,9,7,9,6,3,6,3],1),2989644512376412154601160),
    (([1,5,8,1,1,2,1,7,1,5,1,8,5,7,8],2),([1,2,4,3,7,4,6,3,3,5,1,4,9,7,4],1),3669685263570252633598420),
    (([1,5,8,1,1,2,8,2,4,1,1,2,7,4,7],1),([1,2,4,3,7,4,6,7,5,8,5,3,5,5,2],0),3669686010370200760954900),
    (([1,5,8,1,5,8,5,5,1,7,8,1,7,5,8],2),([1,2,4,3,9,6,8,8,5,8,6,8,8,1,7],2),3670047781369314528826420),
    (([1,5,8,1,7,5,9,7,3,9,5,9,1,9,9],1),([1,2,4,4,4,2,1,7,1,1,4,5,4,2,1],4),3670318079273334011972420),
    (([1,5,8,2,4,8,4,1,4,8,5,5,2,4,4],1),([1,2,4,5,1,1,4,8,4,4,8,7,8,6,3],4),3671378131841190117334420)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_25 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 3671647453253257065622420≤n ∧ n≤4660579416840962166946060 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,5,8,2,5,8,7,1,7,2,4,7,5,8,4],1),([1,2,4,5,4,7,3,4,1,3,4,1,3,7,1],2),3671647453253257065622420),
    (([1,5,8,4,1,2,5,5,8,1,7,8,2,4,1],4),([1,2,4,8,2,9,6,2,7,6,4,7,7,7,5],2),3677043235949929544266420),
    (([1,5,8,4,1,4,2,7,5,7,1,2,8,1,8],2),([1,2,4,8,2,9,9,5,8,1,6,1,6,6,1],4),3677054544235838153127220),
    (([1,5,8,4,1,7,7,1,8,8,1,7,8,2,2],3),([1,2,4,8,3,5,5,4,8,6,9,3,1,6,4],4),3677098383230932803483700),
    (([1,5,8,4,2,2,8,8,8,2,5,5,8,8,8],3),([1,2,4,8,3,8,2,7,7,4,2,8,5,2,6],1),3677160676487667427882420),
    (([1,5,8,4,4,9,1,4,4,1,4,9,7,1,2],3),([1,2,4,8,7,1,7,2,8,5,2,1,5,2,4],2),3678042313321706200776500),
    (([1,5,8,4,5,1,4,1,6,8,3,2,5,8,7],4),([1,2,4,8,7,5,4,7,8,4,4,1,7,7,7],2),3678130825867635203066420),
    (([1,5,8,4,5,5,7,1,1,3,9,4,4,5,4],3),([1,2,4,8,7,8,2,7,2,7,8,5,7,2,7],2),3678278520501397638266420),
    (([1,5,8,4,8,2,5,2,8,2,7,8,5,7,7],4),([1,2,4,9,5,7,6,4,6,6,7,4,1,8,1],4),3680118714536657665786420),
    (([1,5,9,1,7,3,3,7,8,3,4,2,8,1,2],3),([1,2,7,5,2,7,1,2,5,1,4,4,7,5,8],3),3725506015271362432190900),
    (([1,5,9,5,9,1,6,1,2,3,1,4,5,1,7],2),([1,2,8,1,1,4,7,1,5,2,1,8,4,2,1],4),3744163588565397209409920),
    (([1,5,9,6,7,2,1,8,1,3,6,4,2,9,8],4),([1,2,8,4,8,4,2,2,2,2,8,1,8,5,7],1),3749423156843532115646720),
    (([1,5,9,6,8,1,9,2,4,5,3,2,3,3,8],2),([1,2,8,5,4,2,4,7,8,7,7,2,4,4,4],4),3750707217495652668737120),
    (([1,7,7,1,4,5,4,4,2,8,7,1,8,7,4],1),([1,5,2,6,9,7,4,2,2,5,3,6,1,2,9],3),4362200021232229681363300),
    (([1,8,4,1,8,8,7,8,7,2,5,4,4,1,2],3),([1,5,9,2,9,2,8,9,6,6,7,8,2,8,6],2),4660579416840962166946060)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_26 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 4738572704017740997009420≤n ∧ n≤7991945823850570543459592 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,8,5,8,2,4,2,4,5,7,7,8,7,8,7],4),([1,6,1,7,3,3,5,4,2,6,4,3,6,4,2],4),4738572704017740997009420),
    (([1,8,8,1,1,4,7,7,4,4,7,8,8,7,1],4),([1,6,6,5,1,1,2,2,1,2,5,9,6,3,2],2),4902563681362369429521100),
    (([1,8,8,1,1,5,4,7,7,4,4,8,7,7,2],2),([1,6,6,5,1,1,9,1,6,4,5,1,4,6,6],2),4902566331729666326404300),
    (([1,9,6,8,8,1,8,2,5,6,1,9,4,6,3],1),([1,7,5,4,7,8,8,1,1,8,7,1,5,8,4],2),5330884925652946387722200),
    (([1,9,9,1,2,2,4,9,4,6,8,5,1,8,2],1),([1,7,8,1,2,2,5,4,2,5,8,5,1,7,8],3),5536977614521161218485400),
    (([1,9,9,1,7,8,8,7,3,4,3,7,7,5,7],3),([1,7,8,1,8,5,7,1,7,5,1,4,2,5,1],2),5538366199931860742200400),
    (([1,9,9,7,1,8,3,9,6,3,7,8,7,5,6],4),([1,7,8,7,7,4,1,5,2,2,7,4,7,1,1],4),5589295908018721267157120),
    (([1,9,9,7,9,8,1,6,8,5,4,9,9,8,4],2),([1,7,8,8,7,2,7,2,4,5,5,7,5,8,1],1),5605116066941787981016400),
    (([2,4,2,1,4,4,1,1,5,2,8,7,2,1,7],1),([1,9,2,9,5,3,6,6,2,2,4,7,9,1,8],0),6404412918789610991130400),
    (([2,4,2,5,1,1,8,5,2,8,4,2,5,8,5],3),([1,9,3,1,3,1,6,7,8,6,8,3,8,8,5],3),6409245822768004909253920),
    (([2,4,2,5,2,5,2,7,4,1,4,7,4,7,1],1),([1,9,3,1,4,3,8,4,3,8,9,3,5,3,2],1),6409324246526389352900320),
    (([2,4,7,4,5,1,4,2,1,2,8,1,8,4,2],3),([1,9,6,6,9,4,9,2,3,4,5,6,6,1,5],3),6636814477081656486056800),
    (([2,5,6,6,9,3,3,4,4,4,7,9,9,7,8],1),([2,1,7,1,2,2,4,4,5,2,8,1,2,8,4],2),7133190342433235309789480),
    (([2,6,8,4,2,4,9,2,2,4,9,9,2,9,8],4),([2,4,1,1,5,7,4,8,5,4,8,2,7,4,1],4),7991721668691519913973000),
    (([2,6,8,4,2,8,2,9,7,9,6,4,3,1,8],3),([2,4,1,2,1,4,8,8,4,8,4,7,8,4,1],4),7991945823850570543459592)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_27 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 8012458864227228885403400≤n ∧ n≤11421999332884656468347420 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,6,8,5,8,3,2,9,7,2,7,3,6,1,7],2),([2,4,2,5,5,8,4,5,8,8,2,1,2,1,4],1),8012458864227228885403400),
    (([2,6,8,5,8,5,6,9,7,5,7,4,7,1,6],3),([2,4,2,5,7,1,2,2,1,1,2,8,4,8,1],2),8012986647792151577094920),
    (([2,7,1,8,2,2,2,1,7,5,4,5,8,1,8],2),([2,4,6,9,4,4,5,1,3,1,1,9,8,2,6],4),8267120341310498857189720),
    (([2,7,5,1,1,2,7,1,5,2,4,4,8,4,5],2),([2,4,8,8,3,5,7,7,9,8,3,9,7,7,9],3),8448096577739717064821920),
    (([2,7,5,2,4,2,6,2,6,2,9,1,3,1,2],1),([2,4,8,8,5,2,2,1,8,1,4,7,2,4,7],4),8450825977375124174003360),
    (([2,7,6,8,4,7,3,7,5,2,9,8,8,6,9],3),([2,5,1,7,2,4,7,7,4,2,5,4,8,1,5],3),8620335057146192174986400),
    (([2,7,8,1,8,3,4,3,1,6,8,2,5,4,2],1),([2,5,5,4,5,1,8,2,8,7,4,4,4,5,8],3),8797797248502911626357400),
    (([2,7,9,9,5,3,4,1,1,3,4,8,6,4,4],1),([2,5,8,1,8,7,8,2,8,4,5,1,4,4,5],0),9097091616299359969942400),
    (([2,8,1,3,6,9,5,3,3,4,7,3,6,7,4],2),([2,5,8,5,2,4,2,7,1,4,5,8,2,2,4],4),9125956510677038151700400),
    (([2,8,2,6,6,9,2,2,9,2,3,2,2,5,4],4),([2,5,8,7,4,7,8,7,7,8,8,1,4,1,7],1),9163196766758978481591920),
    (([2,9,4,7,6,8,9,9,3,4,6,9,8,6,2],4),([2,7,1,1,2,5,2,2,8,7,1,2,7,8,2],0),10318801607208203690410400),
    (([3,2,1,3,1,3,9,5,9,6,9,3,4,4,1],1),([2,8,1,7,8,5,2,8,8,4,2,4,8,5,7],2),11420501436853991559699500),
    (([3,2,1,3,3,2,9,2,2,1,1,3,6,7,2],4),([2,8,1,7,8,5,7,4,8,2,5,8,1,4,4],2),11420538820437867034112300),
    (([3,2,1,3,8,5,6,4,7,8,7,8,6,1,3],1),([2,8,1,7,8,8,7,4,7,1,1,4,2,2,2],0),11420868836741795270173100),
    (([3,2,1,5,5,3,4,7,1,7,9,9,1,5,8],1),([2,8,1,8,1,7,2,2,1,2,1,5,4,2,1],4),11421999332884656468347420)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_28 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 11421999416605100708507420≤n ∧ n≤22873394741664329186626420 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([3,2,1,5,5,3,4,7,9,7,5,8,7,9,8],3),([2,8,1,8,1,7,2,4,1,2,2,5,1,8,1],2),11421999416605100708507420),
    (([3,2,1,5,6,8,6,3,1,5,7,3,7,6,1],2),([2,8,1,8,2,7,7,7,5,2,1,7,7,1,1],4),11422177215286165496094620),
    (([3,2,1,6,1,2,5,2,1,4,2,2,3,4,8],1),([2,8,1,8,4,5,4,7,1,1,8,7,7,8,7],4),11422707183820616851781660),
    (([3,2,1,6,2,3,1,9,5,7,6,5,2,7,1],3),([2,8,1,8,4,5,8,8,2,1,4,8,7,1,4],2),11422734241665529730133020),
    (([3,2,1,6,3,7,1,9,2,5,2,9,7,3,5],2),([2,8,1,8,4,7,4,2,4,4,5,8,2,8,4],1),11422814471602066778517020),
    (([3,2,2,5,5,5,9,2,2,8,9,9,6,9,6],3),([2,8,2,1,1,4,7,1,2,1,4,5,4,2,1],4),11432372345208659252597420),
    (([3,2,2,5,6,7,9,3,8,6,4,9,3,2,7],1),([2,8,2,1,5,4,2,8,1,2,5,5,4,5,7],4),11432658752265206214209900),
    (([3,2,2,6,4,8,7,8,5,1,8,2,8,8,3],3),([2,8,2,2,5,4,1,8,5,5,5,8,4,7,2],0),11434174895127947491829900),
    (([3,2,2,6,4,9,8,7,4,1,6,9,4,8,3],4),([2,8,2,2,5,5,8,2,2,1,7,5,1,7,8],3),11434217708080420863797900),
    (([3,2,2,9,9,9,7,8,8,7,5,8,6,3,9],3),([2,8,2,5,1,8,5,2,4,7,8,4,4,4,5],0),11444716020221980577129900),
    (([3,2,3,9,8,5,9,8,7,7,2,7,8,2,8],2),([2,8,2,8,4,1,7,2,2,7,5,5,5,5,5],3),11468007273833770796129900),
    (([3,2,6,7,7,2,3,1,3,3,5,7,1,5,6],4),([2,8,4,1,5,4,7,1,2,4,1,2,1,8,1],2),11570865062941716379007420),
    (([3,2,7,3,9,6,5,3,1,3,4,3,3,7,4],3),([2,8,4,5,7,5,2,5,1,5,2,4,8,8,1],4),11600940135756032660099900),
    (([4,5,7,4,2,4,8,1,2,2,8,2,7,5,1],4),([3,9,4,1,1,8,2,5,3,7,9,2,3,7,4],3),22699267670108163690568420),
    (([4,5,8,2,5,5,2,2,5,5,5,1,5,8,7],1),([3,9,4,9,8,5,9,4,2,2,7,3,3,1,8],2),22873394741664329186626420)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_29 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 38882469366568481080076120≤n ∧ n≤95069690026491749610604300 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([5,7,8,7,9,6,7,8,5,9,8,7,4,7,3],2),([5,2,2,1,4,1,1,4,1,2,2,2,4,7,4],1),38882469366568481080076120),
    (([6,4,3,6,9,3,3,5,6,9,7,6,8,3,7],1),([5,7,4,7,8,5,5,5,1,4,5,7,1,7,1],2),47121936138653382677617400),
    (([8,2,8,9,5,7,2,3,6,5,3,3,8,4,1],4),([7,5,1,4,2,1,8,4,2,2,4,1,1,8,1],2),82313385980479243636757420),
    (([8,8,1,2,8,7,5,8,6,8,5,8,7,7,2],4),([7,8,8,5,1,1,2,8,1,1,4,2,1,4,1],2),94953795339412753985777420),
    (([8,8,1,2,8,7,8,5,7,9,3,4,9,4,2],1),([7,8,8,5,1,2,1,4,4,7,5,4,7,5,5],0),94953835880962716205829900),
    (([8,8,1,2,8,7,8,9,8,8,2,6,3,5,7],3),([7,8,8,5,1,2,4,5,1,7,1,2,1,7,4],1),94953848582517013321273100),
    (([8,8,1,3,5,2,9,7,8,9,7,4,7,7,9],1),([7,8,8,5,2,4,4,7,2,7,1,1,2,4,7],1),94956268012894162945737740),
    (([8,8,1,3,8,1,5,1,7,3,2,4,6,7,1],2),([7,8,8,5,2,8,8,8,8,8,2,5,7,5,8],3),94958585592969911554757900),
    (([8,8,2,1,8,2,5,1,1,1,2,7,8,4,2],3),([7,8,8,6,1,3,2,4,2,9,9,7,7,1,7],0),95039757691195854200044300),
    (([8,8,2,4,1,1,8,7,4,1,7,1,2,5,4],4),([7,8,8,6,4,9,3,7,5,4,6,9,8,3,2],1),95060835845356816777969420),
    (([8,8,2,4,1,5,2,7,7,5,8,8,8,2,8],3),([7,8,8,6,4,9,4,3,5,2,4,1,2,6,9],1),95060909638835107699595020),
    (([8,8,2,4,1,7,4,1,8,5,7,2,7,7,2],2),([7,8,8,6,4,9,4,8,3,6,9,3,1,5,5],4),95061000372879123498604300),
    (([8,8,2,4,7,8,2,7,1,4,4,7,4,2,5],3),([7,8,8,6,5,8,2,7,2,9,6,9,9,6,5],2),95069689940119751527122700),
    (([8,8,2,4,7,8,2,7,1,5,2,1,7,2,2],3),([7,8,8,6,5,8,2,7,2,9,7,5,4,3,4],2),95069689945166403230418700),
    (([8,8,2,4,7,8,2,7,2,5,1,2,7,7,2],2),([7,8,8,6,5,8,2,7,3,1,9,8,2,5,8],4),95069690026491749610604300)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_30 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 95069737810477603796977420≤n ∧ n≤160688744386773279007433920 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([8,8,2,4,7,8,4,5,2,1,5,8,8,2,5],2),([7,8,8,6,5,8,3,1,4,7,2,6,6,7,1],4),95069737810477603796977420),
    (([8,8,2,4,8,1,1,1,1,7,1,5,4,8,8],3),([7,8,8,6,5,8,7,4,1,7,3,2,1,1,7],1),95070593349166013873782540),
    (([8,8,2,4,8,1,1,1,1,7,4,8,5,7,5],2),([7,8,8,6,5,8,7,4,1,7,3,2,3,2,6],1),95070593349185866012196620),
    (([8,8,2,8,6,9,2,4,5,9,8,8,3,2,9],3),([7,8,8,7,4,5,1,1,7,4,8,7,7,7,4],2),95160960570376932271094540),
    (([8,8,2,8,9,2,7,6,2,4,7,9,7,5,3],2),([7,8,8,7,5,5,4,8,5,5,4,5,4,7,5],3),95172517399214316637829900),
    (([8,8,2,8,9,2,7,6,2,5,2,4,9,3,1],3),([7,8,8,7,5,5,4,8,5,5,4,8,2,2,2],3),95172517409098505944709900),
    (([1,1,7,7,1,2,5,2,1,7,2,8,7,5,4,4],1),([9,2,3,1,6,4,4,5,2,1,7,3,3,2,2],2),130027990529828400794990620),
    (([1,1,8,8,4,8,7,8,5,2,1,4,4,8,8,7],1),([9,2,7,1,2,6,8,5,7,1,5,1,7,7,7],3),130585973869082275785934000),
    (([1,2,1,4,2,4,7,1,4,5,7,7,4,8,7,4],1),([9,3,1,1,9,9,7,2,9,1,2,1,2,4,8],0),131331475761377692979263300),
    (([1,2,1,4,8,2,1,4,5,4,1,2,7,2,1,7],1),([9,3,1,4,6,1,6,9,2,4,1,2,2,9,6],0),131338053346883365574692900),
    (([1,2,2,7,1,4,7,5,1,5,5,1,8,2,8,7],4),([9,3,3,7,9,7,3,3,3,4,1,2,5,3,7],3),131554703680731066148741420),
    (([1,2,4,7,7,5,2,2,2,1,7,4,4,8,7,4],1),([9,3,7,3,1,5,4,9,6,2,6,1,5,3,8],1),132329703779083333982263300),
    (([1,4,1,1,2,5,1,2,7,8,1,8,8,1,1,7],1),([9,7,5,7,7,4,2,1,5,5,6,1,8,1,2],2),145277659362306668404575400),
    (([1,4,1,1,2,5,1,2,7,8,2,2,8,2,1,7],1),([9,7,5,7,7,4,2,1,5,5,6,1,8,9,2],4),145277659362312740657055400),
    (([1,5,5,8,8,2,2,1,7,7,8,2,2,7,5,7],4),([1,1,1,7,1,3,4,4,5,1,9,7,8,3,6,7],4),160688744386773279007433920)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_31 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 162963965890217806500722420≤n ∧ n≤235015281689705642087657120 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,5,7,1,1,4,4,8,4,9,9,3,4,5,9,1],4),([1,1,8,5,2,1,1,4,7,1,4,2,2,4,2,1],4),162963965890217806500722420),
    (([1,5,7,4,8,5,5,5,2,5,7,5,2,2,4,8],2),([1,1,8,9,7,4,6,5,3,7,8,8,1,4,6,1],2),163382106395818090756126420),
    (([1,5,7,4,8,5,7,1,1,2,5,1,5,5,5,2],3),([1,1,8,9,7,4,9,5,6,2,2,3,7,6,7,7],4),163382942843159228290126420),
    (([1,5,7,4,8,8,2,1,7,8,1,7,1,7,5,2],3),([1,1,8,9,7,9,4,7,3,5,1,7,2,3,2,4],4),163395031329056556724712020),
    (([1,7,6,8,9,9,5,9,1,7,4,3,8,1,9,8],2),([1,5,1,7,5,2,8,8,2,7,7,8,1,5,4,2],3),195754514424512510284243400),
    (([1,7,7,7,6,6,3,9,7,7,4,4,9,5,9,4],2),([1,5,4,1,1,8,2,2,1,4,7,4,1,4,1,8],0),197887366398973126505146400),
    (([1,7,7,7,7,2,5,3,3,4,1,8,4,2,8,9],4),([1,5,4,2,4,2,4,2,7,2,1,1,4,1,8,1],2),197930730026656153855382420),
    (([1,8,4,4,5,1,2,7,8,2,1,8,7,7,7,2],2),([1,5,9,4,2,4,4,2,2,4,4,9,8,5,4,1],3),209996954402924822534666800),
    (([1,8,4,4,5,1,2,8,4,8,5,5,8,1,7,8],3),([1,5,9,4,2,4,4,2,6,7,4,3,8,8,2,3],4),209996956192476148501775920),
    (([1,8,4,4,5,5,2,8,5,7,2,2,1,8,5,4],4),([1,5,9,4,2,7,1,6,8,7,7,3,6,1,9,6],2),210001405689976037522063920),
    (([1,9,5,4,1,1,7,2,1,9,8,1,5,3,3,7],1),([1,7,2,7,2,4,4,7,7,5,4,1,8,7,1,1],2),235012354071011944478207120),
    (([1,9,5,4,1,1,7,2,8,5,8,7,8,9,2,6],2),([1,7,2,7,2,4,4,7,7,8,1,7,5,1,1,1],4),235012354626561234779807120),
    (([1,9,5,4,1,4,4,1,8,1,8,7,3,7,4,4],1),([1,7,2,7,2,5,5,4,1,2,7,8,7,2,5,8],3),235013097900955779119500400),
    (([1,9,5,4,1,7,7,3,3,9,1,7,7,1,2,4],4),([1,7,2,7,2,7,7,1,4,1,8,1,1,5,1,2],3),235015281055556816117517920),
    (([1,9,5,4,1,7,7,3,4,8,4,7,3,6,2,3],4),([1,7,2,7,2,7,7,1,5,8,1,8,2,7,1,1],4),235015281689705642087657120)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_32 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 258393046425542627043008900≤n ∧ n≤260301334534562509460853820 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,1,8,8,8,3,2,8,3,4,5,7,9,8,7,4],3),([1,8,1,1,2,2,1,8,5,4,4,1,2,7,1,8],0),258393046425542627043008900),
    (([2,1,8,9,6,5,6,4,7,8,8,2,3,5,3,2],4),([1,8,1,5,1,2,1,1,8,1,7,4,2,4,2,1],4),258530665066050109361972420),
    (([2,1,9,2,2,4,1,3,3,3,5,5,5,4,8,2],1),([1,8,1,7,1,1,5,2,8,4,2,1,1,4,2,1],4),258682337409627854239847420),
    (([2,1,9,2,2,8,5,4,2,7,9,9,8,2,4,5],4),([1,8,1,7,1,7,7,7,4,7,1,5,7,7,1,4],1),258683508995751552616079420),
    (([2,1,9,2,3,3,1,9,3,9,5,7,2,7,6,1],2),([1,8,1,7,2,1,2,2,8,5,1,4,1,4,1,8],0),258684474073377913978583900),
    (([2,1,9,2,6,9,8,8,8,7,6,2,2,4,5,6],2),([1,8,1,7,5,1,2,1,8,8,4,2,2,5,1,7],4),258703783912760032304486300),
    (([2,1,9,3,1,8,7,9,4,9,4,3,8,1,5,2],3),([1,8,1,7,7,5,8,4,2,4,4,7,7,7,7,4],2),258731790966118175292344540),
    (([2,1,9,9,4,9,6,5,9,6,9,8,8,3,3,7],2),([1,8,2,7,2,1,8,2,1,7,8,4,1,8,5,4],2),259596909656252275881273140),
    (([2,1,9,9,8,1,8,5,8,6,9,3,6,8,1,1],2),([1,8,2,7,7,5,2,1,2,4,8,2,7,2,4,7],1),259689346000230251331612740),
    (([2,1,9,9,8,8,8,2,2,2,2,8,1,7,5,7],3),([1,8,2,7,8,4,5,1,1,2,5,5,5,8,8,1],4),259717884871959670863224900),
    (([2,1,9,9,8,8,9,1,2,6,5,4,5,1,7,5],1),([1,8,2,7,8,4,8,1,7,8,5,7,7,4,1,7],1),259719112126468930938404420),
    (([2,2,2,7,4,8,7,5,5,8,7,8,1,4,1,5],3),([1,8,3,1,6,1,3,3,6,3,5,6,2,9,3,7],1),260268243492682022422663420),
    (([2,2,2,7,7,2,2,5,1,7,2,4,4,8,7,4],1),([1,8,3,1,9,5,1,2,2,3,1,6,9,8,9,5],4),260289380505476515879138300),
    (([2,2,2,7,7,8,4,8,5,4,5,5,5,8,4,7],1),([1,8,3,2,1,8,3,2,4,6,3,9,3,5,1,4],1),260296982134474787319691420),
    (([2,2,2,7,8,1,8,8,4,5,5,8,8,1,1,4],1),([1,8,3,2,3,1,2,1,3,6,6,7,4,4,5,8],1),260301334534562509460853820)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_33 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 260301699573924018858538300≤n ∧ n≤262283037815955805044175420 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,2,2,7,8,2,7,1,4,1,2,5,7,8,7,4],1),([1,8,3,2,3,3,1,1,4,5,1,5,3,3,6,3],1),260301699573924018858538300),
    (([2,2,2,8,2,8,2,7,4,5,2,1,1,2,1,5],2),([1,8,3,2,7,2,1,4,2,8,4,5,7,6,6,9],3),260334716788648091380353820),
    (([2,2,2,8,2,8,2,7,5,1,7,5,7,4,5,7],4),([1,8,3,2,7,2,1,4,6,3,9,8,5,9,6,3],2),260334717126977655276571420),
    (([2,2,2,8,4,1,4,2,1,1,8,7,2,4,2,4],4),([1,8,3,2,7,7,9,3,6,8,8,5,1,1,1,6],3),260342075510897168627054620),
    (([2,2,2,8,4,8,7,7,1,8,7,4,8,1,2,5],3),([1,8,3,2,8,2,3,6,4,5,7,2,7,7,8,5],2),260347686064304736651804700),
    (([2,2,2,8,5,5,4,5,8,7,2,2,4,2,8,2],3),([1,8,3,2,8,6,2,2,7,3,7,3,4,8,7,5],4),260352250828216604862139420),
    (([2,2,2,8,5,5,4,7,5,1,4,2,5,4,2,5],3),([1,8,3,2,8,6,2,5,6,7,4,7,2,2,6,7],4),260352270261094032085051420),
    (([2,2,2,8,5,5,4,7,5,2,2,1,7,4,5,7],1),([1,8,3,2,8,6,2,5,6,7,6,3,4,3,9,9],3),260352270294915884001211420),
    (([2,2,2,8,5,5,4,7,8,7,5,7,1,7,4,2],3),([1,8,3,2,8,6,2,6,4,1,8,8,2,1,5,4],1),260352277646786718338107420),
    (([2,2,2,8,7,5,7,4,1,7,7,5,2,8,4,1],1),([1,8,3,2,9,9,1,5,4,2,9,2,3,3,1,8],4),260375266380628901515310620),
    (([2,2,2,8,8,4,5,7,4,2,1,2,2,7,5,1],4),([1,8,3,3,3,3,7,6,8,6,6,3,8,7,5,4],2),260387678465362898504443420),
    (([2,2,5,1,2,2,7,2,2,7,1,8,2,2,4,8],3),([1,8,4,2,8,9,3,8,6,7,9,4,9,4,5,8],1),262256104262195506031413660),
    (([2,2,5,1,5,7,7,2,1,4,5,5,7,2,7,8],2),([1,8,4,2,9,4,6,4,6,1,4,8,6,7,4,5],2),262263221844375599592571420),
    (([2,2,5,2,1,1,8,5,7,2,5,5,7,8,4,7],4),([1,8,4,3,1,6,6,1,4,5,6,9,8,9,7,9],3),262283037770501226795151420),
    (([2,2,5,2,1,1,8,5,7,7,8,7,2,7,7,1],4),([1,8,4,3,1,6,6,1,4,8,1,9,2,7,5,7],4),262283037815955805044175420)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_34 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 262283184570771334007997820≤n ∧ n≤263552922723294168823027100 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,2,5,2,1,4,1,8,5,8,7,8,7,7,7,7],1),([1,8,4,3,1,6,8,2,9,6,9,2,9,7,1,5],3),262283184570771334007997820),
    (([2,2,5,2,1,4,7,1,2,4,7,4,2,1,7,1],4),([1,8,4,3,1,6,8,8,2,2,3,8,5,8,6,8],2),262283233794062206616061820),
    (([2,2,5,2,4,4,7,5,1,7,2,8,7,4,5,7],4),([1,8,4,3,2,9,2,3,1,1,6,6,5,9,2,9],2),262291246740328113434071420),
    (([2,2,5,2,4,4,7,5,2,2,2,8,5,5,2,5],3),([1,8,4,3,2,9,2,3,2,1,1,8,5,3,9,4],1),262291246836421707062551420),
    (([2,2,5,2,4,4,7,5,2,2,5,4,2,2,4,1],4),([1,8,4,3,2,9,2,3,2,1,8,4,8,1,5,9],4),262291246839181089402391420),
    (([2,2,5,2,7,1,4,7,7,7,8,5,5,2,1,1],1),([1,8,4,3,4,6,3,6,6,1,8,9,7,5,3,6],1),262308796564859668285579420),
    (([2,2,5,5,5,6,6,2,7,5,3,5,4,7,4,4],1),([1,8,4,4,7,7,5,8,4,7,1,1,1,7,8,7],2),262567694887675681255151420),
    (([2,2,5,5,5,7,5,3,2,4,9,5,4,7,4,4],1),([1,8,4,4,7,7,8,4,5,7,1,1,1,7,8,7],2),262569592662158078755151420),
    (([2,2,5,5,6,8,6,2,1,1,2,9,6,7,6,3],3),([1,8,4,4,8,4,2,4,4,7,5,2,2,2,8,4],1),262589757242150874223017020),
    (([2,2,5,6,6,8,3,6,6,1,1,8,9,6,6,4],3),([1,8,4,5,5,5,8,8,5,4,7,8,8,5,7,2],3),262738405157947643971379900),
    (([2,2,5,9,9,6,3,8,6,7,8,1,6,9,9,4],2),([1,8,4,7,7,4,5,7,2,1,1,7,1,2,4,1],1),263464234622270120721246140),
    (([2,2,6,1,3,1,1,6,1,7,1,5,2,4,7,3],1),([1,8,4,7,7,8,8,1,5,7,7,8,4,4,8,1],2),263498790750812650239298940),
    (([2,2,6,1,7,9,4,8,8,8,3,5,1,5,8,5],2),([1,8,4,7,8,2,1,2,7,2,1,2,8,1,5,8],3),263516354244084514565579420),
    (([2,2,6,1,7,9,5,9,8,1,1,3,1,3,7,7],2),([1,8,4,7,8,2,2,7,1,7,2,8,8,5,7,4],1),263516482620847059980701340),
    (([2,2,6,2,6,4,1,1,2,2,7,4,8,4,5,1],1),([1,8,4,7,8,7,7,8,4,5,2,4,5,1,4,4],4),263552922723294168823027100)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_35 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 263552922723295119678297500≤n ∧ n≤271448349912440588834654420 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,2,6,2,6,4,1,1,2,2,7,4,8,8,4,8],4),([1,8,4,7,8,7,7,8,4,5,2,4,5,1,4,7],4),263552922723295119678297500),
    (([2,2,6,2,6,4,5,2,4,7,5,9,5,1,6,7],2),([1,8,4,7,8,7,7,8,8,8,8,2,1,5,4,1],4),263553099684444929898923420),
    (([2,2,6,2,6,4,5,2,4,7,8,1,2,5,5,4],1),([1,8,4,7,8,7,7,8,8,8,8,2,5,2,8,1],2),263553099700852241054123420),
    (([2,2,6,3,9,5,5,1,3,7,1,6,5,3,4,2],1),([1,8,4,8,2,7,4,7,7,5,2,8,7,4,1,7],1),263680212670121611850279420),
    (([2,2,7,1,9,5,2,1,9,7,5,2,3,1,2,8],1),([1,8,5,4,2,2,2,4,2,4,7,8,8,2,8,4],1),265018585127748858529767020),
    (([2,2,7,1,9,7,3,2,5,3,2,8,4,6,6,6],1),([1,8,5,4,2,4,7,7,8,1,2,5,4,5,8,5],3),265020535748738269285049900),
    (([2,2,7,1,9,7,3,2,5,3,9,6,1,9,3,8],3),([1,8,5,4,2,4,7,7,8,1,5,4,5,4,7,4],2),265020535770251826216377900),
    (([2,2,7,1,9,7,4,9,3,4,3,2,2,7,3,5],2),([1,8,5,4,2,4,8,7,1,5,1,8,5,7,2,7],1),265020700285870194636857900),
    (([2,2,7,2,1,9,3,7,2,3,1,1,7,2,5,1],2),([1,8,5,4,2,8,2,2,8,8,1,7,1,8,5,4],4),265025978398625322951901100),
    (([2,2,7,2,2,7,5,4,5,7,7,5,2,2,2,4],4),([1,8,5,4,2,8,9,9,1,7,6,8,9,6,2,4],4),265028017768935681878101420),
    (([2,3,2,4,7,2,2,8,8,7,7,6,5,4,7,8],2),([1,8,7,1,5,1,4,1,5,4,5,7,8,8,4,7],1),271446236688943619619482900),
    (([2,3,2,4,7,2,3,4,5,6,7,8,2,2,8,5],2),([1,8,7,1,5,1,4,7,2,4,8,1,8,8,7,4],4),271446246564210614737209620),
    (([2,3,2,4,7,2,4,3,4,2,3,2,2,1,5,7],1),([1,8,7,1,5,1,5,8,5,4,2,5,7,4,8,7],2),271446275359520971400234900),
    (([2,3,2,4,7,2,4,3,9,2,8,7,2,3,7,1],4),([1,8,7,1,5,1,5,8,8,2,1,7,4,7,4,7],2),271446277190465594437073300),
    (([2,3,2,4,7,5,3,2,6,6,6,1,8,8,3,9],4),([1,8,7,1,5,4,8,8,7,7,2,8,7,4,1,7],1),271448349912440588834654420)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_36 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 271492828723236751499685620≤n ∧ n≤1845646719089385394210395800 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,3,2,5,4,3,2,6,7,8,8,8,6,6,6,3],4),([1,8,7,1,8,7,1,2,4,7,8,8,8,5,2,4],2),271492828723236751499685620),
    (([2,3,2,5,4,8,2,3,1,2,9,9,4,3,8,2],2),([1,8,7,1,8,8,7,1,8,7,8,2,8,8,1,2],0),271496927877649174199731700),
    (([2,3,2,5,4,8,7,2,9,4,7,5,9,9,3,1],4),([1,8,7,1,8,8,8,5,2,4,7,7,7,4,1,7],1),271497517204612276507154420),
    (([2,3,2,5,4,8,7,2,9,9,4,5,8,3,3,8],2),([1,8,7,1,8,8,8,5,2,8,1,4,2,2,8,4],1),271497518384318131454892020),
    (([2,3,2,5,4,8,8,1,8,1,7,5,6,4,6,5],3),([1,8,7,1,8,8,8,7,8,8,8,8,2,5,7,1],2),271497711748835544604178420),
    (([2,3,5,2,2,6,6,9,7,3,1,3,5,8,8,8],1),([1,8,7,8,8,8,8,8,2,4,7,8,8,4,5,7],2),274711550774494376979727220),
    (([2,3,5,8,1,6,7,6,3,5,4,4,9,6,9,8],3),([1,8,8,1,7,7,1,2,4,7,5,8,2,4,4,4],4),275828256931873172078424620),
    (([2,3,5,8,1,8,2,6,6,5,5,5,4,8,4,3],3),([1,8,8,1,7,7,8,1,8,1,7,4,5,7,2,7],2),275829922790052075494141420),
    (([2,3,5,8,1,8,2,6,6,8,3,9,3,8,2,7],1),([1,8,8,1,7,7,8,1,8,5,2,8,5,1,4,4],2),275829923196992569909112300),
    (([2,3,7,2,7,8,4,2,4,1,7,2,3,8,5,7],3),([1,8,8,8,2,5,2,4,8,4,1,4,7,4,8,4],4),278886298867908027233785580),
    (([2,3,7,3,5,4,4,3,8,7,6,7,3,4,4,1],3),([1,8,8,8,4,2,4,7,1,2,7,5,7,1,4,8],0),278977866893788861715825900),
    (([2,4,2,5,7,1,2,8,8,8,7,4,4,5,7,4],4),([1,9,3,2,3,5,8,6,4,8,7,7,7,1,9,6],1),288467531745155800811146420),
    (([5,8,7,8,8,4,8,1,7,4,4,8,8,4,2,1],1),([5,4,3,2,8,8,1,6,3,3,6,7,9,3,8,4],3),1841108213558847455364147640),
    (([5,8,7,9,9,9,2,7,4,2,8,8,7,6,7,7],2),([5,4,4,1,2,7,7,2,1,5,1,7,4,2,5,1],2),1845513809939101074045325400),
    (([5,8,8,1,1,1,2,3,8,7,7,9,1,8,1,6],2),([5,4,4,2,1,5,2,1,1,8,7,1,8,1,4,8],3),1845646719089385394210395800)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_37 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 1845646737917748560183797400≤n ∧ n≤5150225055016383331305085580 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([5,8,8,1,1,1,3,8,7,2,2,1,7,4,3,4],3),([5,4,4,2,1,5,2,8,1,2,8,1,5,2,5,8],3),1845646737917748560183797400),
    (([5,8,8,1,1,1,3,8,9,8,6,1,8,8,3,4],2),([5,4,4,2,1,5,2,8,5,2,2,4,4,8,2,2],3),1845646739121575934360565400),
    (([5,8,8,1,1,1,8,4,8,3,8,8,6,6,9,4],3),([5,4,4,2,1,5,5,1,7,4,7,1,5,4,8,2],0),1845646856111806558554517400),
    (([5,8,8,1,1,7,8,1,4,1,2,1,1,8,4,2],3),([5,4,4,2,2,2,9,7,7,7,7,9,6,8,9,5],1),1845652239523554854395931800),
    (([5,8,8,1,2,1,4,1,8,2,4,1,4,8,8,1],1),([5,4,4,2,2,6,8,1,8,5,3,2,7,9,4,7],4),1845656578369231563923791000),
    (([5,8,8,1,2,1,4,1,8,7,7,7,7,2,1,4],1),([5,4,4,2,2,6,8,1,8,5,8,6,8,8,3,1],4),1845656578449456191622683800),
    (([5,8,8,1,2,1,4,7,8,5,4,5,7,4,8,5],2),([5,4,4,2,2,6,8,3,6,1,1,2,2,7,8,1],1),1845656599915591985679008920),
    (([5,8,8,1,4,2,7,6,3,1,6,8,3,1,4,8],2),([5,4,4,2,5,2,1,7,7,7,2,5,2,5,4,4],2),1845707330732037190378837400),
    (([5,8,8,2,4,5,8,5,4,4,5,5,8,2,8,8],2),([5,4,4,3,8,8,6,3,9,6,7,4,8,1,1,9],4),1846228915787454956825888920),
    (([5,8,9,4,6,6,8,4,6,3,2,8,3,8,9,7],2),([5,4,7,2,7,4,5,1,2,8,4,4,5,4,7,4],2),1869256987135491069333565400),
    (([6,3,8,8,4,3,9,3,1,8,5,4,1,2,4,1],1),([5,7,2,2,2,1,7,4,8,4,5,1,1,2,8,1],1),2100844112887021063654475300),
    (([6,4,4,6,9,2,1,2,6,6,2,8,5,3,1,1],3),([5,7,5,2,5,5,5,5,1,5,8,1,7,1,2,4],2),2125605493757639921766329900),
    (([8,2,9,4,1,6,4,7,9,2,5,3,2,8,1,9],1),([7,5,2,1,2,2,5,7,2,7,4,8,2,4,4,7],2),3706452723139492503642510800),
    (([9,6,9,1,3,9,6,6,8,7,2,4,7,6,5,3],1),([8,7,2,2,8,7,7,8,4,1,8,5,7,8,4,7],2),5150218261536084140260247180),
    (([9,6,9,1,4,2,1,6,5,3,4,4,9,2,9,4],2),([8,7,2,2,8,8,4,7,5,2,7,4,1,4,8,1],1),5150225055016383331305085580)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_38 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 5817962877026907029004383920≤n ∧ n≤8817748522085445182312799620 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,1,5,7,1,8,2,2,4,5,2,7,8,7,4,5,7],4),([9,1,3,3,8,9,4,3,9,1,1,4,5,8,4,3],1),5817962877026907029004383920),
    (([1,2,1,4,1,8,2,4,4,7,7,8,7,2,8,7,1],4),([9,3,1,1,9,2,6,5,9,9,1,3,5,9,2,8],3),5909908439759172948268138600),
    (([1,2,1,4,2,8,8,1,2,1,1,2,5,7,2,1,7],1),([9,3,1,2,3,9,4,1,1,1,1,6,5,3,4,7],0),5909928721239465600259755400),
    (([1,2,2,4,2,2,4,8,4,8,1,1,8,5,8,8,5],2),([9,3,3,1,8,7,7,8,1,4,6,2,1,1,3,5],4),5916254781490076671551574720),
    (([1,4,2,2,5,1,2,8,5,2,5,2,4,1,7,5,5],2),([9,7,6,2,2,6,4,8,6,2,1,6,4,7,9,5],2),6549374243883094150820851420),
    (([1,4,2,4,5,5,7,5,5,8,2,5,5,7,4,5,2],2),([9,7,6,3,8,9,5,4,1,6,2,9,1,7,3,9],1),6552138501292569619704751420),
    (([1,5,4,7,2,8,1,2,7,8,2,8,7,2,1,1,8],3),([9,9,8,7,7,8,3,1,3,1,5,1,1,8,9,4],3),7150425369411961447201037140),
    (([1,5,5,8,7,5,1,3,9,9,3,7,3,9,4,3,9],2),([1,1,1,2,1,2,2,1,2,7,4,4,4,5,4,2,1],4),7229441222983876681470722420),
    (([1,5,5,8,8,8,1,5,4,1,4,8,1,7,2,7,7],4),([1,1,1,9,5,3,4,4,4,1,9,4,6,7,4,8,3],3),7232317219522248227616286420),
    (([1,5,7,7,7,5,2,1,8,4,8,8,8,2,8,8,8],3),([1,2,1,2,2,4,4,4,4,8,9,2,6,2,5,3,2],1),7386610096179103523499957220),
    (([1,5,7,8,2,9,8,3,3,3,3,3,9,1,1,2,6],2),([1,2,2,4,1,1,5,4,2,1,5,4,8,5,4,5,7],4),7395289345657403842422022400),
    (([1,5,8,5,2,8,1,4,5,7,4,4,2,8,2,8,4],4),([1,2,5,1,6,6,1,7,9,4,8,9,6,7,3,6,7],3),7456553700497699870926801420),
    (([1,5,8,8,1,8,8,4,7,2,2,7,8,7,4,7,8],2),([1,2,6,5,3,7,4,9,4,8,4,4,3,8,5,4,4],2),7500941393299196426133347500),
    (([1,5,8,9,9,7,4,7,2,3,6,1,1,2,7,1,3],2),([1,2,7,4,5,2,5,2,4,2,2,5,1,7,4,1,1],4),7540553251458424552104533900),
    (([1,7,6,9,6,3,9,8,3,2,8,5,7,6,8,5,1],1),([1,5,2,1,4,2,7,7,8,7,1,4,8,2,4,4,4],4),8817748522085445182312799620)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_39 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 9595658687132951572617722500≤n ∧ n≤14629594782227873302878089920 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,8,5,8,2,4,8,4,7,2,2,7,8,7,4,7,8],2),([1,6,1,7,3,5,8,9,4,8,4,4,3,8,5,4,4],2),9595658687132951572617722500),
    (([1,8,5,8,4,7,8,1,7,4,2,5,7,8,1,5,8],3),([1,6,1,8,1,8,7,4,7,3,2,8,8,9,5,1,9],3),9598691365571538086429548420),
    (([1,9,5,9,8,1,9,1,9,2,2,4,9,8,3,4,6],2),([1,7,4,1,4,5,7,4,8,8,4,7,4,1,4,8,1],1),10675048876007690867430085580),
    (([2,1,1,1,7,7,4,2,4,7,1,8,5,1,7,7,4],4),([1,7,9,4,3,3,8,5,3,8,2,2,7,2,9,7,3],1),11438527033504744140798896920),
    (([2,1,1,1,7,7,4,2,4,7,1,8,8,5,7,5,2],3),([1,7,9,4,3,3,8,5,3,8,2,2,7,3,8,2,4],2),11438527033505034550585674520),
    (([2,1,1,1,8,7,8,8,4,1,8,4,7,7,4,2,5],3),([1,7,9,4,3,3,9,8,2,2,9,1,2,7,8,1,7],0),11438549748812259759383960200),
    (([2,1,1,5,1,5,1,7,1,5,5,8,1,2,7,8,2],2),([1,7,9,4,4,1,7,2,6,1,4,7,3,9,3,5,6],2),11439703921045079042611943920),
    (([2,1,1,5,2,8,1,7,1,1,4,8,4,1,2,1,7],1),([1,7,9,4,4,2,3,7,1,1,5,7,6,7,9,8,3],0),11439731843440435919584830400),
    (([2,1,1,7,4,4,1,4,1,2,1,1,7,8,1,5,5],2),([1,7,9,4,4,9,6,1,8,3,5,6,1,9,4,4,8],2),11441192258030635159272106720),
    (([2,1,1,7,4,4,1,7,7,8,4,4,4,2,8,7,1],4),([1,7,9,4,4,9,6,1,8,6,8,9,1,4,4,8,3],0),11441192322339415085033413600),
    (([2,5,5,7,5,5,2,1,7,2,1,4,4,7,1,2,7],4),([2,1,1,7,4,9,7,9,2,7,3,3,3,4,1,5,6],4),14301566091305420533070738920),
    (([2,5,5,7,5,5,2,1,7,5,7,2,2,1,5,1,4],1),([2,1,1,7,4,9,7,9,2,9,6,1,5,7,6,8,1],2),14301566101691451738136688920),
    (([2,5,5,7,5,6,2,7,7,7,4,1,1,2,7,1,6],2),([2,1,1,7,7,2,1,2,7,2,8,5,7,2,4,8,7],4),14301843188026544909461836920),
    (([2,5,5,8,2,8,7,7,7,8,8,5,4,7,2,7,4],4),([2,1,3,1,7,6,6,4,4,2,6,9,2,8,5,6,9],1),14319263686872318306878138920),
    (([2,5,7,7,1,5,1,2,2,1,4,1,1,7,1,8,5],2),([2,2,2,3,9,3,8,5,1,2,2,2,7,8,4,2,9],1),14629594782227873302878089920)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_40 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 14630168592548308597026911920≤n ∧ n≤78283000818857204036798373200 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,5,7,7,2,2,5,8,8,2,4,5,8,4,1,4,2],2),([2,2,2,4,3,7,1,1,5,3,9,3,6,1,9,3,6],1),14630168592548308597026911920),
    (([2,5,7,7,2,7,8,4,2,8,4,5,8,2,7,8,1],4),([2,2,2,4,6,6,7,6,7,4,5,7,6,2,4,1,8],2),14630886962669297787113111920),
    (([2,5,7,7,3,6,9,9,4,8,1,2,7,3,3,7,8],3),([2,2,2,5,1,1,7,8,5,4,4,4,4,4,4,4,5],0),14632409040995351597594317400),
    (([2,5,7,7,4,1,1,1,2,2,4,4,2,2,1,7,1],4),([2,2,2,5,6,4,2,6,2,7,6,3,8,3,2,8,8],3),14633498989301349097562249320),
    (([2,5,7,7,4,4,2,1,4,1,7,7,4,5,2,2,5],3),([2,2,2,5,7,1,9,1,1,4,9,6,1,8,3,7,2],1),14633864751493290721026542920),
    (([2,5,8,8,8,7,7,2,7,7,2,8,8,1,8,7,7],1),([2,2,6,9,8,8,7,3,4,2,8,5,3,3,5,7,2],1),14901237137955509170146683800),
    (([2,5,9,1,6,9,8,2,4,4,3,1,4,2,2,6,1],2),([2,2,7,7,7,8,2,7,5,5,7,8,5,1,5,2,1],1),14959657872152585899046872400),
    (([2,7,6,8,9,8,2,6,6,6,7,1,8,5,2,5,8],3),([2,5,2,4,7,8,2,2,4,1,2,7,2,4,4,1,7],2),17487440466609702828680907320),
    (([2,7,8,2,8,7,9,2,4,9,9,3,2,4,3,5,3],3),([2,5,5,5,2,4,8,8,1,1,4,4,1,4,2,1,4],1),17828183938420468370751028400),
    (([2,9,7,1,1,6,7,6,9,5,9,2,9,8,9,8,3],3),([2,7,5,8,4,1,2,5,2,4,2,8,1,1,4,7,7],4),21542074366761967348050296600),
    (([2,9,7,1,2,1,7,9,8,8,3,5,9,9,2,3,6],3),([2,7,5,8,4,2,4,4,4,4,2,4,8,1,1,7,1],4),21542182521193387326781913240),
    (([2,9,8,7,3,8,6,8,5,3,5,7,2,8,3,4,3],3),([2,7,7,7,4,1,7,8,4,8,2,8,7,5,4,4,4],1),22088607708807506996303807720),
    (([4,1,5,2,4,1,7,5,5,5,8,1,4,7,8,8,5],3),([3,7,6,9,7,4,7,2,2,2,4,3,7,6,2,6,5],2),39826581570360420966246151420),
    (([4,2,1,4,2,2,1,7,7,1,5,1,8,7,8,7,4],1),([3,7,7,8,5,9,3,8,5,9,4,2,4,4,4,1,3],2),40218992669070227468558038300),
    (([5,7,8,2,2,1,7,9,2,6,1,9,6,2,9,2,3],3),([5,1,7,1,1,1,8,8,8,8,4,8,1,2,1,5,4],1),78283000818857204036798373200)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_41 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 78283327705120500599821523920≤n ∧ n≤263407936968584941626538448920 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([5,7,8,2,2,5,2,2,1,4,5,2,1,7,4,5,7],1),([5,1,7,1,3,9,2,9,2,2,8,4,8,4,3,9,9],3),78283327705120500599821523920),
    (([5,7,8,3,1,1,1,9,1,8,7,7,6,9,2,3,8],1),([5,1,7,5,7,5,2,4,1,8,7,5,1,2,1,2,5],0),78316960753538058436310392400),
    (([5,7,8,3,1,1,2,3,2,6,2,6,9,9,9,1,1],3),([5,1,7,5,7,5,2,4,5,1,4,5,8,1,2,7,5],0),78316960945235391564432892400),
    (([5,7,8,4,4,8,7,4,1,2,1,2,1,2,7,7,2],2),([5,1,7,9,3,5,2,1,8,2,6,6,9,4,3,6,1],2),78382735145981310054779666800),
    (([5,7,8,9,4,4,4,6,8,4,8,4,4,3,3,2,7],2),([5,2,4,1,8,2,7,5,7,8,7,5,5,2,4,2,5],3),78913285137954298232247292400),
    (([5,8,4,1,8,2,5,2,2,4,8,2,8,5,2,7,1],1),([5,3,4,3,4,4,2,3,9,7,6,9,1,2,6,2,8],1),80602869163517304479933617420),
    (([6,4,5,2,2,1,1,7,1,7,8,9,6,1,1,8,7],3),([5,7,5,5,8,1,7,1,7,7,4,2,4,5,8,5,5],3),95809995025088452914570892400),
    (([7,2,4,4,2,2,1,5,1,8,1,5,5,8,5,2,5],3),([6,5,8,3,1,4,6,8,9,7,9,6,1,8,4,8,4],1),125673248776685035854465676420),
    (([7,2,4,4,8,7,1,1,4,1,2,4,1,1,8,7,7],4),([6,5,8,3,4,6,9,7,2,5,1,1,4,3,8,5,1],2),125682728687447168386728592900),
    (([8,1,4,1,2,1,5,2,4,2,7,2,4,5,7,8,4],1),([7,4,6,9,6,9,2,3,8,1,7,5,6,9,2,7,3],4),164256706599887901147235761220),
    (([8,3,8,7,2,9,6,7,9,1,3,1,4,1,2,6,5],4),([7,5,7,2,7,1,7,1,1,8,8,8,4,2,7,1,1],1),169270553017215726000588219620),
    (([8,3,8,7,4,7,3,1,8,9,5,2,8,7,4,1,8],1),([7,5,7,2,8,7,7,5,4,2,2,1,7,7,1,7,8],3),169280087129653469284828259300),
    (([1,1,7,7,8,8,1,7,8,5,4,4,7,5,8,8,2,4],1),([9,2,3,7,7,1,8,3,4,1,6,5,4,3,4,3,6],1),263406916695493272776097892120),
    (([1,1,7,7,8,8,1,8,2,7,8,1,7,2,8,4,8,5],3),([9,2,3,7,7,1,8,6,7,4,4,6,3,9,8,5,3],3),263406922516193292148182017560),
    (([1,1,7,7,8,8,5,5,4,2,2,4,8,1,5,5,2,2],3),([9,2,3,7,7,5,4,3,4,7,1,4,7,3,9,9,6],4),263407936968584941626538448920)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_42 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 263408986221192563916851312920≤n ∧ n≤326450553314415882198909374900 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,1,7,7,8,8,7,4,5,7,2,4,5,1,1,7,2,5],2),([9,2,3,7,7,7,1,6,2,9,9,2,2,5,8,9,7],4),263408986221192563916851312920),
    (([1,1,8,1,1,4,8,1,1,5,2,2,2,2,7,2,1,7],1),([9,2,5,3,7,2,2,6,2,3,9,3,3,2,5,9,5],3),263775829500021676742293755400),
    (([1,1,8,4,5,4,7,5,4,5,2,8,8,1,1,2,7,7],4),([9,2,5,7,9,3,2,2,1,9,4,2,7,2,2,7,6],2),263931406496638604666866598920),
    (([1,1,8,5,7,7,7,2,8,7,4,1,8,4,5,7,1,8],3),([9,2,6,1,4,7,1,2,1,7,5,9,6,8,7,7,8],4),264060662909538982222047802120),
    (([1,1,8,5,7,7,7,4,4,2,7,5,8,4,8,8,2,4],1),([9,2,6,1,4,7,6,1,4,3,2,9,6,5,8,7,1],1),264060701512356096022929142120),
    (([1,1,8,5,7,7,7,4,4,2,8,1,2,4,2,1,1,8],3),([9,2,6,1,4,7,6,1,4,7,9,6,3,4,5,6,3],1),264060701528558444266890849640),
    (([1,2,2,4,4,5,8,2,5,4,8,5,1,5,4,1,8,7],4),([9,3,3,2,6,3,3,3,8,2,1,9,6,4,4,1,5],3),266237528475883996398244726420),
    (([1,5,5,8,7,7,2,8,4,1,2,2,5,5,8,4,1,8],3),([1,1,1,4,5,9,6,1,4,6,7,1,8,7,1,7,6,6],3),325346752633349336426496428920),
    (([1,5,6,2,6,7,5,4,3,1,6,4,7,5,7,3,7,1],2),([1,1,4,4,8,2,1,1,1,2,1,7,5,1,8,1,8,1],2),326382605554133788568501882420),
    (([1,5,6,2,6,7,5,4,3,1,7,4,1,7,5,1,4,1],1),([1,1,4,4,8,2,1,1,2,4,8,7,1,1,5,7,2,8],3),326382605560765052402997434420),
    (([1,5,6,2,6,7,5,4,8,7,4,6,9,4,2,2,8,3],2),([1,1,4,4,8,2,2,8,1,8,5,4,4,7,1,2,8,4],1),326382627615851591058311892020),
    (([1,5,6,2,6,7,8,2,6,6,4,2,5,2,3,6,1,4],3),([1,1,4,4,8,4,5,8,1,4,7,7,1,1,2,4,1,7],2),326383966014976976990147344820),
    (([1,5,6,2,6,9,2,8,7,6,2,1,3,4,8,7,8,4],1),([1,1,4,4,8,8,7,5,8,4,2,4,2,1,7,2,5,7],1),326389467544003638527559634100),
    (([1,5,6,2,6,9,2,8,7,6,2,2,9,7,6,7,8,4],1),([1,1,4,4,8,8,7,5,8,4,2,5,2,7,8,8,5,2],3),326389467545979577933821086900),
    (([1,5,6,2,9,2,4,7,3,8,1,2,3,6,7,7,8,7],3),([1,1,4,5,8,5,8,2,8,5,2,8,5,7,2,8,7,7],2),326450553314415882198909374900)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_43 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 331096034284798511613006001420≤n ∧ n≤386007665827750896226612154420 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,5,7,5,5,4,5,2,4,2,7,5,5,5,2,7,1,5],2),([1,1,9,3,5,6,8,7,9,7,9,6,9,3,4,9,8,4],2),331096034284798511613006001420),
    (([1,5,7,5,7,2,2,7,5,8,2,4,1,5,2,8,4,1],4),([1,1,9,4,6,4,2,6,4,7,9,7,3,5,7,3,4,1],1),331209008045019808860327526420),
    (([1,6,9,3,1,1,1,8,7,4,1,6,9,2,1,1,5,4],2),([1,4,4,7,1,4,5,8,2,5,7,8,1,4,2,8,2,4],1),372677872589078129260507592300),
    (([1,6,9,5,6,8,4,2,8,2,3,3,6,2,3,8,2,9],2),([1,4,5,1,7,2,4,1,2,2,8,8,8,2,4,8,5,7],2),374049811486372395147253449500),
    (([1,7,2,2,1,4,8,5,2,8,5,8,1,5,8,2,8,4],4),([1,4,6,8,8,3,4,5,2,3,3,4,3,1,6,9,1,3],4),379930526114469615527640863920),
    (([1,7,4,6,2,1,5,1,6,7,9,9,1,3,2,3,7,9],1),([1,4,8,2,4,5,2,1,5,7,8,1,4,1,1,4,7,7],4),385472816575500558071948734100),
    (([1,7,4,6,2,2,3,6,7,5,3,1,4,4,3,9,8,8],1),([1,4,8,2,4,5,5,2,2,4,1,2,4,4,4,1,5,1],4),385473263005757654857011530900),
    (([1,7,4,6,2,3,4,8,9,9,6,9,7,3,1,3,1,7],4),([1,4,8,2,4,5,8,8,2,7,2,4,1,8,1,1,7,1],4),385474386927780236224630350740),
    (([1,7,4,6,2,6,6,6,6,5,6,1,2,8,1,1,9,2],3),([1,4,8,2,4,8,1,5,7,4,8,4,7,2,4,2,5,2],0),385480732013963382279198314900),
    (([1,7,4,6,2,8,8,6,4,3,5,3,9,9,8,2,6,7],3),([1,4,8,2,5,1,2,2,8,2,2,7,4,4,2,1,5,4],1),385488225772847115458369935700),
    (([1,7,4,6,2,8,9,4,8,9,4,8,2,8,5,8,3,1],1),([1,4,8,2,5,2,2,5,7,8,4,8,7,5,1,4,5,1],4),385488802419368355454312514900),
    (([1,7,4,7,1,8,8,1,7,5,2,2,1,7,5,2,2,5],3),([1,4,8,3,9,4,5,2,9,1,4,2,2,8,3,6,6,3],2),385940358456971296170002230420),
    (([1,7,4,7,1,8,8,7,8,2,5,5,5,2,5,7,8,7],1),([1,4,8,3,9,4,5,6,6,3,3,7,8,8,9,6,1,3],4),385940571128826184699875766420),
    (([1,7,4,7,4,1,8,7,1,8,4,8,8,5,1,5,7,2],3),([1,4,8,4,1,9,3,4,8,2,7,4,4,4,7,5,1,4],2),386005182696630799238753664820),
    (([1,7,4,7,4,3,1,2,5,6,9,1,7,4,4,3,9,5],4),([1,4,8,4,2,2,5,4,7,4,1,7,7,4,7,4,1,7],1),386007665827750896226612154420)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_44 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 386027297532230304785331322420≤n ∧ n≤2262267302182310396138897381200 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,7,4,7,4,7,2,1,8,4,2,4,7,2,8,4,5,4],4),([1,4,8,4,3,1,8,4,2,8,7,5,8,6,6,7,7,7],1),386027297532230304785331322420),
    (([1,7,4,7,5,8,7,5,8,2,2,4,4,7,2,4,8,1],4),([1,4,8,4,5,1,3,2,6,8,9,6,6,2,2,2,8,1],1),386096450157347245050788074420),
    (([2,4,4,5,8,5,1,1,7,8,5,2,2,5,4,4,5,1],4),([1,9,4,5,6,9,2,9,7,2,2,4,4,3,8,2,4,8],2),589811574707854260417540001420),
    (([4,6,9,1,4,8,5,1,4,7,2,5,2,4,2,8,1,3],3),([4,1,2,7,1,1,2,4,2,8,7,8,8,1,2,5,1,7],2),2235088117374836693806670532320),
    (([4,6,9,1,7,6,3,4,1,5,3,6,3,1,4,1,9,7],1),([4,1,2,8,1,7,1,7,7,1,4,1,5,7,1,2,4,1],1),2235285921101637551232410308640),
    (([4,6,9,1,7,6,3,5,5,4,1,1,6,6,1,8,8,3],4),([4,1,2,8,1,7,4,2,4,5,7,7,2,8,7,4,1,7],1),2235286016823810661335514341920),
    (([4,6,9,1,7,6,5,9,2,6,8,1,8,4,2,2,8,4],1),([4,1,2,8,2,2,5,1,8,2,5,4,8,2,1,4,4,4],1),2235288879021070875915702912800),
    (([4,6,9,1,7,9,5,6,8,3,1,3,4,3,8,6,1,8],3),([4,1,2,8,5,2,1,7,4,8,5,1,4,1,1,4,7,7],4),2235333804652093545215503421600),
    (([4,6,9,1,8,7,6,7,3,2,7,8,5,4,8,1,6,5],1),([4,1,2,8,7,7,2,2,2,1,2,8,1,7,5,4,4,4],4),2235404194597838368610919737120),
    (([4,7,1,1,7,1,2,5,1,1,1,5,8,1,2,8,4,5],2),([4,2,1,1,4,5,6,2,2,1,3,2,9,3,2,6,1,7],4),2262152555590148820768149321920),
    (([4,7,1,1,7,2,1,8,2,5,5,1,8,8,8,8,2,8],3),([4,2,1,1,4,6,5,6,3,2,4,2,9,6,2,6,7,4],1),2262152824753645945993844907520),
    (([4,7,1,1,7,2,5,8,8,2,7,1,4,4,4,2,7,8],3),([4,2,1,1,4,6,8,8,2,3,7,5,4,2,4,2,9,1],4),2262152981438388988913795606080),
    (([4,7,1,1,7,2,5,8,8,2,7,1,5,7,2,5,1,8],2),([4,2,1,1,4,6,8,8,2,3,7,5,4,9,3,3,6,6],4),2262152981438426425071039161920),
    (([4,7,1,2,5,5,7,8,5,7,2,5,5,8,4,2,4,1],1),([4,2,1,3,2,2,6,2,4,5,6,8,1,1,6,1,9,4],4),2262233965327129587913223963920),
    (([4,7,1,2,7,1,4,2,4,1,2,5,2,8,2,7,2,2],3),([4,2,1,3,6,8,5,3,6,1,8,1,2,1,8,8,5,2],3),2262267302182310396138897381200)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_45 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 2262267324339535663377616701520≤n ∧ n≤2297409704216174560631015003920 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([4,7,1,2,7,1,4,7,4,4,1,5,5,7,4,2,7,2],2),([4,2,1,3,6,8,5,4,8,2,8,1,4,7,8,8,7,6],3),2262267324339535663377616701520),
    (([4,7,1,2,7,5,7,1,1,2,1,4,7,5,4,4,7,1],4),([4,2,1,3,7,4,9,8,8,3,7,7,5,7,8,8,9,8],1),2262273896005215735376648787920),
    (([4,7,1,3,6,1,9,1,2,9,7,8,9,4,5,6,9,4],1),([4,2,1,5,1,8,1,7,4,2,2,5,1,8,2,7,4,1],4),2262429382113156955737398348000),
    (([4,7,1,3,7,5,1,2,8,3,6,6,8,4,1,3,3,9],3),([4,2,1,5,5,8,2,5,1,7,2,1,7,4,2,4,1,1],2),2262468216126586751410748596400),
    (([4,7,1,5,5,7,1,4,4,4,5,5,4,4,2,8,4,7],1),([4,2,1,8,6,1,9,6,3,3,7,2,6,4,5,6,7,2],2),2263005153063205869224765003920),
    (([4,7,1,5,7,8,5,1,2,8,4,7,7,5,2,7,5,7],4),([4,2,1,8,9,5,6,6,6,6,2,4,1,7,3,2,1,9],1),2263120672360148102858344763920),
    (([4,7,2,2,8,8,1,4,5,7,5,5,5,4,5,2,1,5],2),([4,2,3,2,3,8,4,1,8,9,1,3,5,2,4,4,2,3],2),2266020332784594276657030563920),
    (([4,7,2,5,4,5,7,4,8,5,5,8,4,5,2,7,5,1],4),([4,2,3,6,5,8,3,4,9,7,2,6,2,7,8,7,4,6],1),2267322084705574854053735063920),
    (([4,7,3,1,7,9,8,8,7,4,5,3,2,1,2,7,8,2],4),([4,2,4,8,1,1,8,4,7,5,2,1,8,1,1,7,1,7],2),2272816121205295215805842132320),
    (([4,7,3,2,3,2,6,3,6,8,6,8,4,7,8,5,8,3],2),([4,2,4,8,4,2,8,4,1,5,2,5,8,4,8,7,2,8],3),2272939028445195919536460968800),
    (([4,7,3,2,5,4,1,7,8,8,6,6,7,3,6,3,2,8],1),([4,2,4,8,5,2,5,7,4,1,8,8,5,2,7,4,8,1],4),2273017842170736806203512226400),
    (([4,7,3,3,4,2,4,4,7,6,1,5,6,3,5,1,8,8],3),([4,2,4,8,8,8,2,1,8,8,2,1,8,4,2,2,5,7],4),2273471364233612301671782817120),
    (([4,7,3,3,4,2,4,4,9,8,7,3,7,5,6,9,1,8],3),([4,2,4,8,8,8,2,2,2,5,5,5,2,1,5,8,8,4],1),2273471373524551502967063682400),
    (([4,7,3,6,3,1,2,9,6,8,1,8,7,6,6,3,2,5],1),([4,2,5,5,5,5,4,1,2,8,2,8,7,8,8,5,7,2],3),2276284605137319465691822942400),
    (([4,7,5,1,5,7,1,4,4,4,5,5,4,4,2,8,4,7],1),([4,2,8,1,6,1,9,6,3,3,7,2,6,4,5,6,7,2],2),2297409704216174560631015003920)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_46 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 2297525223513116794264594763920≤n ∧ n≤2833329961001526059794019610620 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([4,7,5,1,7,8,5,1,2,8,4,7,7,5,2,7,5,7],4),([4,2,8,1,9,5,6,6,6,6,2,4,1,7,3,2,1,9],1),2297525223513116794264594763920),
    (([4,7,5,2,4,8,7,1,6,9,1,7,6,9,6,7,9,4],2),([4,2,8,2,8,4,1,8,5,5,8,7,1,5,1,1,5,1],2),2297846779132664691928912912400),
    (([4,7,5,2,4,8,7,2,2,4,4,1,4,8,4,7,7,8],2),([4,2,8,2,8,4,1,9,4,7,5,4,8,5,1,4,9,6],1),2297846805488133577927020970000),
    (([4,7,5,2,4,8,7,2,7,1,4,8,4,5,8,7,5,2],3),([4,2,8,2,8,4,2,2,6,2,5,2,8,8,2,2,4,6],1),2297846842960439443776228347920),
    (([4,7,5,2,5,8,7,7,2,7,5,4,2,7,4,2,4,2],3),([4,2,8,2,9,4,5,7,6,3,2,8,8,9,8,8,3,7],1),2297929655681841012226781531920),
    (([4,7,5,2,5,8,7,7,7,4,4,7,2,2,8,1,2,4],4),([4,2,8,2,9,4,5,8,7,3,9,2,1,9,2,2,3,4],4),2297929822079927293883224283920),
    (([4,7,7,1,7,7,2,8,5,1,1,5,5,5,2,2,7,5],2),([4,3,4,9,4,7,1,4,9,2,4,7,2,8,3,1,5,2],3),2336303494827454195052812913920),
    (([4,8,8,7,1,1,5,8,1,1,7,4,2,1,2,7,7,2],2),([4,5,5,1,3,4,6,7,9,8,9,8,1,1,3,2,1,1],3),2548065512649511387727954666800),
    (([4,8,8,7,3,6,8,9,1,2,7,9,8,5,4,8,8,6],2),([4,5,5,2,5,1,8,4,8,4,2,2,2,4,5,7,1,7],2),2548543625389677954571782532400),
    (([5,1,9,1,8,1,3,7,1,2,7,9,2,2,7,3,5,3],1),([4,7,1,1,7,2,5,4,1,7,1,2,1,8,7,7,1,1],4),2827691181753302033669492657120),
    (([5,1,9,1,8,1,3,7,1,2,8,7,7,6,8,1,1,9],2),([4,7,1,1,7,2,5,4,1,7,2,4,4,4,4,2,4,5],3),2827691181753952995361047404000),
    (([5,1,9,1,8,1,8,1,1,2,1,1,8,6,4,7,6,2],4),([4,7,1,1,7,2,8,1,2,8,8,2,2,4,5,1,1,7],2),2827691442113448178492701432320),
    (([5,1,9,2,2,4,4,8,7,5,4,1,3,1,2,3,2,6],1),([4,7,1,2,1,8,7,1,8,2,1,8,7,5,4,8,2,4],2),2827745876753088198095064810620),
    (([5,2,1,2,7,1,1,7,5,1,2,7,8,2,2,5,5,1],4),([4,7,2,4,4,1,9,7,2,9,2,2,2,2,5,1,6,1],4),2833321901858018816318173351420),
    (([5,2,1,2,7,9,8,3,6,9,3,6,2,7,2,8,8,1],4),([4,7,2,4,4,4,2,4,2,2,7,7,8,1,2,5,2,4],2),2833329961001526059794019610620)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_47 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 2833710027231839552603252879420≤n ∧ n≤7031987816696336048954752216640 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([5,2,1,6,4,2,9,5,1,8,2,3,2,1,5,4,4,1],2),([4,7,2,4,8,2,8,5,7,2,7,7,1,4,4,1,1,7],1),2833710027231839552603252879420),
    (([5,2,1,6,7,5,1,6,3,8,8,9,9,9,9,2,9,4],3),([4,7,2,4,8,7,4,4,1,5,7,7,4,7,2,4,4,4],1),2833770803097017552155550620220),
    (([5,2,1,9,8,7,8,4,3,9,6,8,1,9,3,9,4,3],2),([4,7,2,5,7,1,4,8,8,2,4,4,5,7,2,7,2,1],1),2834454976484653634790438798500),
    (([5,2,2,8,5,1,1,8,4,1,1,5,4,4,8,1,1,8],3),([4,7,2,7,2,4,4,2,4,1,3,6,3,7,5,3,1,3],1),2836187720327302758192443905420),
    (([5,2,2,8,5,1,1,8,5,3,2,6,8,8,1,1,8,1],4),([4,7,2,7,2,4,4,2,4,5,1,8,1,7,2,7,1,7],2),2836187720748298531913198081420),
    (([5,2,2,8,5,1,4,9,4,2,5,8,3,6,3,3,1,7],1),([4,7,2,7,2,4,4,7,2,1,5,2,7,4,8,4,1,7],1),2836187932719353484243130529420),
    (([5,2,3,4,2,6,7,1,1,9,7,2,6,6,2,4,1,1],3),([4,7,2,8,2,2,5,5,1,1,7,5,2,2,8,4,7,4],2),2837553891316209200279878877900),
    (([5,2,3,4,2,6,7,5,7,5,9,2,7,8,5,1,7,1],1),([4,7,2,8,2,2,5,7,2,7,2,2,1,7,2,4,2,7],2),2837553977509938291752632841420),
    (([5,5,1,7,8,2,1,2,2,4,7,5,7,8,5,1,5,5],2),([4,8,5,7,7,4,9,2,8,9,4,4,8,8,6,9,1,3],3),3089513623947214996221855751420),
    (([6,3,8,8,8,8,6,6,4,9,1,5,7,9,7,1,3,7],1),([5,7,2,4,8,8,4,8,4,7,7,5,1,1,2,7,2,1],1),4256142176332541530323710673500),
    (([6,5,7,6,4,4,7,9,6,2,6,1,3,8,1,4,8,6],2),([5,8,2,5,4,5,4,7,4,5,7,2,4,8,2,4,2,1],2),4505152948371994779984682514900),
    (([7,9,1,2,9,2,1,5,6,8,7,3,4,3,3,1,2,6],3),([7,1,7,4,7,5,1,8,1,2,4,1,1,5,8,5,4,8],3),7029713794450868153083680496400),
    (([7,9,1,3,2,5,4,3,9,3,7,2,3,3,4,1,2,7],1),([7,1,7,4,8,2,4,4,4,2,7,1,2,1,8,5,7,4],1),7029799902065565276240402076340),
    (([7,9,1,3,3,3,2,8,9,8,3,4,7,5,2,1,7,3],4),([7,1,7,4,8,4,8,7,1,4,1,5,1,7,2,7,1,1],1),7029820251227367110385861969620),
    (([7,9,1,6,3,6,2,1,7,2,9,9,2,6,9,3,9,5],3),([7,1,7,7,2,7,1,1,4,1,7,5,8,4,2,7,7,7],2),7031987816696336048954752216640)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_48 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 7054734904970561324450619969620≤n ∧ n≤11973112626277096986224885927920 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([7,9,3,3,3,6,6,5,1,7,6,4,4,4,8,6,7,5],2),([7,2,1,1,1,7,8,7,5,2,2,2,7,1,4,7,1,1],4),7054734904970561324450619969620),
    (([7,9,3,3,7,4,1,2,3,4,5,3,6,4,9,2,1,2],1),([7,2,1,5,7,8,2,2,2,5,2,5,1,4,2,4,1,1],2),7055360817219591950361061096400),
    (([7,9,3,3,7,4,4,2,9,4,3,6,4,3,2,1,3,5],4),([7,2,1,5,7,8,7,2,2,7,4,7,8,2,1,7,8,7],1),7055363838805684430101957291520),
    (([8,2,9,1,4,5,8,2,2,9,8,6,3,9,4,7,1,7],1),([7,5,1,7,8,5,8,1,7,4,2,1,4,1,1,5,4,2],3),7503205226108270696185196743400),
    (([8,5,9,7,9,4,2,7,6,1,7,1,1,2,6,3,1,8],2),([7,7,1,4,8,2,4,5,8,8,2,7,7,5,2,1,1,7],2),8045809379362234034835410282600),
    (([8,5,9,7,9,4,2,8,4,2,5,1,4,2,3,1,2,8],4),([7,7,1,4,8,2,5,8,1,8,8,7,7,1,1,4,1,7],1),8045810089415408699827418466920),
    (([8,5,9,7,9,4,2,8,4,9,6,3,6,9,1,5,6,4],2),([7,7,1,4,8,2,5,8,8,7,1,7,4,7,2,4,4,4],1),8045810162970015259716917807720),
    (([8,6,3,7,3,3,6,7,9,4,4,3,8,2,5,4,3,2],4),([7,7,4,1,7,2,7,4,8,8,8,1,5,7,2,4,4,4],1),8090860074617077876570217807720),
    (([1,1,5,7,5,2,1,2,1,7,8,1,7,7,8,1,4,7,1],4),([9,1,3,6,2,2,7,1,6,3,6,4,3,6,8,4,3,5],3),11782301874326011223959079350420),
    (([1,1,7,2,2,2,5,1,7,8,1,8,7,8,2,7,8,8,4],4),([9,1,9,5,8,2,6,3,8,7,9,6,3,4,4,8,4,3],2),11831244603827863688534944990420),
    (([1,2,1,5,5,7,4,1,4,2,7,8,8,1,4,2,7,8,7],4),([9,3,1,6,1,3,5,1,4,7,8,2,7,4,7,4,9,8],4),11968903222578773703007168946920),
    (([1,2,1,5,5,8,5,2,4,7,2,7,5,2,2,8,2,7,4],1),([9,3,1,6,2,7,5,8,3,6,3,8,4,6,1,6,9,3],1),11968927639711696125134113523920),
    (([1,2,1,5,8,8,1,1,2,2,4,4,4,1,8,1,7,5,8],3),([9,3,1,7,1,8,1,5,6,8,7,2,7,9,8,8,4,8],2),11969476833179435297906647165120),
    (([1,2,1,7,5,5,4,7,4,4,2,8,8,2,1,5,5,2,2],3),([9,3,2,1,4,5,4,2,8,2,9,1,8,6,4,9,3,8],1),11971758795862973064601532198920),
    (([1,2,1,8,1,8,8,1,4,1,7,7,7,5,2,7,8,8,4],4),([9,3,2,4,6,1,5,7,4,3,9,8,3,6,3,6,1,3],2),11973112626277096986224885927920)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_49 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 11978520927950649160111526349640≤n ∧ n≤29439946377536901656231956748920 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,2,2,2,8,5,2,2,8,7,7,4,2,1,7,2,1,1,8],3),([9,3,2,9,1,4,3,4,4,3,8,2,2,5,1,3,2,6],3),11978520927950649160111526349640),
    (([1,5,6,9,3,4,3,9,8,1,4,2,2,3,1,7,9,6,4],1),([1,1,7,8,1,5,2,1,7,4,5,4,8,4,4,2,8,2,4],1),14818736260980849064745093529800),
    (([1,5,7,5,4,1,8,4,2,1,2,4,7,8,1,2,7,8,7],4),([1,1,9,2,7,9,1,3,1,9,4,2,7,4,6,3,1,1,5],2),14897020062117579754012123946920),
    (([1,5,8,9,7,8,2,6,9,1,7,3,2,2,8,1,4,8,7],1),([1,2,7,1,2,4,4,7,4,2,5,2,7,4,5,2,8,4,7],4),15254502530445300800920835922500),
    (([1,5,8,9,7,8,3,1,4,5,2,2,9,2,3,3,3,7,9],2),([1,2,7,1,2,7,2,2,5,7,7,8,4,8,1,2,7,1,1],1),15254533936765985197846045719620),
    (([1,7,6,8,7,7,7,8,2,7,7,5,9,6,2,1,3,2,6],2),([1,5,1,1,2,7,4,8,7,4,4,4,5,2,5,4,2,2,2],0),17820416013392074997065503854900),
    (([1,7,8,2,9,7,4,2,4,1,7,8,3,3,6,1,7,9,1],4),([1,5,5,2,8,8,5,4,1,8,5,2,8,4,1,8,1,5,5],3),18183558504993292246455632392400),
    (([1,7,8,2,9,7,4,2,4,1,7,8,3,8,9,7,5,3,4],3),([1,5,5,2,8,8,5,4,1,8,5,2,8,8,4,4,4,2,2],0),18183558504997659915423056392400),
    (([1,8,8,8,5,2,2,7,2,5,1,7,8,1,2,7,8,8,8],3),([1,6,7,4,3,4,9,4,1,4,5,3,2,8,2,6,9,2,7],4),20343206750317078797300379332220),
    (([1,9,9,4,8,6,7,9,8,8,3,4,8,8,4,2,6,3,7],4),([1,7,8,5,2,5,1,8,4,8,1,2,2,5,7,1,5,4,7],1),22794241687276607050395365984900),
    (([2,4,2,8,2,8,2,4,4,2,2,7,1,5,7,1,1,8,1],4),([1,9,3,4,8,6,8,5,8,2,9,4,3,6,7,7,2,9,7],4),26318908084216172406838308664720),
    (([2,5,6,1,9,7,2,6,2,8,3,2,3,9,4,9,9,6,3],1),([2,1,5,4,7,1,7,1,2,5,5,5,7,1,5,5,5,8,1],2),29107342616937312341695424767400),
    (([2,5,7,1,1,5,1,1,1,4,4,2,8,1,2,7,4,7,1],1),([2,1,8,9,1,2,1,5,7,6,6,1,9,7,1,3,4,7,3],3),29439939733025800752336822275320),
    (([2,5,7,1,1,5,1,4,7,5,8,1,8,7,8,8,8,8,8],2),([2,1,8,9,1,2,1,6,9,7,7,2,9,6,5,7,4,1,3],3),29439939819315188022102360824920),
    (([2,5,7,1,1,5,5,8,8,8,4,1,7,1,4,4,8,7,1],4),([2,1,8,9,1,2,5,8,8,1,3,2,4,4,4,9,2,2,7],2),29439946377536901656231956748920)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_50 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 29441437512820521066978563534920≤n ∧ n≤192670580314091182637359524967400 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,5,7,1,4,7,2,4,2,5,8,5,7,1,1,1,4,2,4],1),([2,1,8,9,3,1,2,5,4,1,1,2,2,7,7,4,8,7,6],4),29441437512820521066978563534920),
    (([2,5,7,1,7,2,1,7,8,2,2,4,1,4,5,1,4,5,7],4),([2,1,8,9,4,7,7,3,4,8,7,4,2,5,1,9,7,6,2],4),29444032551825947992877040758920),
    (([2,5,7,1,7,2,2,8,8,7,1,8,1,4,8,7,7,4,8],3),([2,1,8,9,4,7,7,4,1,2,5,7,3,1,7,7,4,1,7],0),29444035161793420691324897331400),
    (([2,5,7,1,7,2,2,8,8,7,2,4,7,4,7,8,1,4,8],3),([2,1,8,9,4,7,7,4,1,2,5,9,8,5,2,2,8,5,4],1),29444035162009492307926752051400),
    (([2,5,7,1,7,2,2,8,8,7,5,5,1,1,5,1,4,8,1],1),([2,1,8,9,4,7,7,4,1,3,1,1,7,2,1,9,2,1,5],2),29444035164890582826104642078920),
    (([2,7,7,7,7,8,8,7,1,9,5,1,7,9,2,8,1,1,8],2),([2,5,4,5,8,2,7,8,4,1,2,1,7,7,1,5,2,5,2],0),35822209633004865987380074642400),
    (([3,1,9,8,7,2,6,3,5,1,4,2,7,2,9,8,3,3,3],2),([2,8,1,4,5,1,4,2,8,1,1,5,5,8,5,8,7,1,7],2),46784070341627246244565079407400),
    (([3,1,9,8,9,3,8,5,4,2,7,7,8,4,6,9,9,3,4],1),([2,8,1,5,4,1,2,2,1,2,4,8,4,7,8,1,2,5,4],4),46793562260515930336320381038600),
    (([3,1,9,8,9,3,8,8,3,7,2,8,7,1,6,3,8,2,2],4),([2,8,1,5,4,2,2,5,4,5,4,2,5,7,8,4,8,5,7],1),46793588138685436076901348667400),
    (([3,3,6,4,1,2,5,4,8,2,3,1,7,1,5,2,9,1,1],4),([2,8,7,2,1,8,2,4,2,4,7,4,7,8,4,1,5,4,1],4),49159923549917814114403660110920),
    (([3,3,6,4,1,7,5,9,6,2,9,8,7,4,1,8,2,5,1],4),([2,8,7,2,2,1,1,1,7,2,8,7,8,5,4,7,4,1,7],1),49160215021324187683075007466920),
    (([3,3,6,4,5,2,7,5,6,7,8,5,9,8,4,7,3,8,2],1),([2,8,7,2,4,8,1,1,2,7,7,4,2,2,5,7,4,1,7],1),49166070750003536253565044966920),
    (([4,5,7,4,5,7,5,8,1,5,8,5,2,8,4,8,5,8,8],2),([3,9,4,2,2,1,4,7,4,1,8,9,6,8,8,5,6,8,4],4),93098672549868397312731421126420),
    (([5,7,8,8,4,3,6,6,6,6,6,1,4,9,3,3,2,7,6],2),([5,2,2,7,4,5,1,1,4,5,8,2,8,5,5,4,4,4,4],2),159511348301805961985224938067400),
    (([6,4,1,4,9,5,1,2,1,4,1,7,1,2,6,4,4,4,8],2),([5,7,4,1,5,5,8,8,5,7,4,1,7,2,5,7,8,8,7],4),192670580314091182637359524967400)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_51 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 196458207596264561187634876159400≤n ∧ n≤8715718455545951703952185759239900 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([6,4,8,1,8,4,7,4,4,7,2,6,8,4,8,4,9,4,2],4),([5,7,7,2,7,8,4,5,5,2,7,2,7,7,7,8,4,4,4],4),196458207596264561187634876159400),
    (([8,3,3,8,8,7,8,9,7,8,4,7,2,4,9,1,1,5,9],3),([7,5,4,4,7,8,1,2,1,8,5,8,8,2,8,8,8,2,1],4),339168783302167316038636831917500),
    (([1,1,7,7,2,8,5,7,5,8,4,8,5,1,5,8,5,7,7,2],2),([9,2,3,2,7,5,9,3,8,6,6,8,2,3,6,1,8,2,3],4),533210262009951479142365165476420),
    (([1,4,1,4,2,1,1,7,7,8,8,5,1,2,8,7,4,1,7,8],3),([9,7,5,7,9,6,8,1,3,2,1,2,9,7,1,6,2,2,7],4),595866206749242181739212044611080),
    (([1,4,5,5,2,4,7,1,8,2,8,4,2,1,7,5,8,2,7,1],4),([9,7,9,5,4,4,3,7,2,4,3,8,2,7,1,4,2,4,7],4),607055378538597293900791480748920),
    (([1,5,6,4,9,3,4,6,7,3,3,6,8,7,1,7,1,1,4,7],2),([1,1,5,4,4,5,4,4,7,8,5,8,1,4,8,2,1,2,1,8],0),662190588242801354889565467554900),
    (([1,5,7,1,5,2,2,2,5,7,2,1,7,5,2,1,1,2,7,8],2),([1,1,8,5,4,7,4,7,3,7,9,6,1,4,7,4,9,1,7,8],1),668297946090345875278937409758920),
    (([1,9,5,1,3,6,3,2,8,3,9,4,2,9,2,1,6,9,3,8],1),([1,7,2,4,1,1,8,4,2,1,5,1,2,8,4,4,2,1,5,4],1),962193234781718004853003315248200),
    (([1,9,5,1,3,7,1,4,6,8,1,4,4,1,2,6,1,6,3,2],2),([1,7,2,4,1,5,5,8,1,8,2,2,4,7,5,4,2,4,5,1],4),962195348293251556833560245327400),
    (([1,9,5,2,7,1,3,7,8,1,9,2,3,6,5,7,4,5,1,2],3),([1,7,2,5,4,4,7,1,4,7,1,8,2,7,4,4,1,4,1,7],1),962662622162726539309014406904420),
    (([1,9,5,2,7,1,4,5,2,8,3,2,9,4,3,7,2,2,3,9],2),([1,7,2,5,4,4,7,4,4,4,7,1,8,1,7,7,2,4,4,4],1),962662708934492531677754216245220),
    (([5,8,7,7,1,1,7,1,4,7,4,8,8,8,8,2,8,8,2,2],2),([5,4,1,3,8,8,8,1,9,8,5,5,3,7,6,4,9,7,8,8],4),7530306220094975232723998351175400),
    (([5,8,7,7,7,5,7,4,1,1,5,7,8,1,7,4,7,2,7,4],1),([5,4,2,1,3,7,3,3,2,2,3,7,4,9,3,8,6,3,6,6],2),7535952588944951660642768586806920),
    (([6,3,8,8,3,2,5,4,1,9,8,1,3,7,9,2,4,1,3,8],3),([5,7,2,1,2,8,8,4,1,1,2,8,5,4,5,1,8,1,1,7],1),8614283808638435883360771278018900),
    (([6,4,4,6,8,1,3,4,6,3,1,4,5,1,1,2,4,1,7,4],3),([5,7,5,2,1,7,2,1,4,4,5,2,5,1,4,8,2,8,1,4],1),8715718455545951703952185759239900)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_52 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 15199049988692681535522910107358400≤n ∧ n≤30321003858715622780856934939571920 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([8,2,9,4,3,6,7,2,6,2,3,6,7,3,3,7,3,9,6,6],4),([7,5,2,1,7,8,8,8,7,4,5,2,5,7,4,2,4,4,2,4],4),15199049988692681535522910107358400),
    (([8,4,8,2,7,8,4,8,1,1,7,2,7,4,8,5,7,8,2,2],2),([7,6,3,4,8,5,7,5,4,1,4,7,8,1,2,1,6,6,3,5],1),15736439087154875613628381778850400),
    (([8,9,7,7,1,1,2,5,2,6,4,2,4,1,6,3,6,4,8,9],2),([8,1,2,5,1,2,1,7,7,1,7,8,1,1,5,2,2,4,4,7],2),18698268008992217575857540061260800),
    (([8,9,7,7,1,1,2,5,2,7,4,4,9,6,1,8,3,1,1,7],3),([8,1,2,5,1,2,1,7,8,1,7,4,2,8,5,8,8,8,5,2],3),18698268009292506772637506900774400),
    (([8,9,7,7,1,1,3,3,4,5,2,6,5,2,3,6,3,3,1,9],1),([8,1,2,5,1,2,8,7,4,1,7,8,2,7,7,7,2,4,4,4],1),18698268398228892157026451864682720),
    (([8,9,7,7,1,1,3,3,4,5,2,7,8,9,4,6,2,6,6,9],3),([8,1,2,5,1,2,8,7,4,1,8,7,1,5,1,4,2,8,2,4],1),18698268398233180974893968202904800),
    (([8,9,8,6,2,7,8,4,5,7,8,7,1,7,4,8,6,1,4,8],1),([8,2,2,5,1,1,4,5,8,1,7,8,5,4,2,2,2,1,5,1],2),18816456660698820312140845669162400),
    (([8,9,9,1,8,8,7,7,8,9,2,7,8,1,3,4,7,4,2,8],4),([8,2,7,1,1,8,8,4,7,8,4,2,4,8,4,7,5,8,2,5],3),18915997018493966178611144352116000),
    (([8,9,9,2,9,9,2,5,1,6,4,1,7,4,8,8,3,9,6,9],1),([8,2,7,5,1,8,2,8,4,5,4,1,4,2,1,5,7,4,8,1],4),18923956513258886009581098574726400),
    (([9,4,3,2,2,2,3,9,7,8,6,3,2,9,3,6,4,2,8,6],4),([8,4,8,8,7,5,4,1,2,2,1,1,1,8,2,5,4,5,4,7],2),19724639263409857105734978317713400),
    (([1,2,1,4,2,5,1,4,7,8,1,5,5,7,1,7,8,8,8,8,8],2),([9,3,1,2,1,2,6,4,7,3,6,2,7,7,5,8,1,9,1,3],3),24234355301703008506666061423324920),
    (([1,2,1,4,2,5,2,2,7,7,1,7,1,7,5,7,1,7,4,7,4],4),([9,3,1,2,1,2,9,7,3,2,1,8,2,9,8,5,1,9,9,8],1),24234355504772253677812858214468920),
    (([1,2,1,7,7,8,7,2,8,8,5,7,7,4,8,1,5,5,7,8,1],4),([9,3,2,3,3,2,8,8,8,4,5,7,8,2,3,6,2,4,4,8],2),24243978333432253693321110507818920),
    (([1,5,7,7,7,5,1,2,8,8,4,2,5,1,6,4,7,7,3,7,6],3),([1,2,1,2,1,7,1,5,7,8,4,2,2,2,4,7,7,4,2,4,7],1),30289694695856439833138875765124420),
    (([1,5,7,8,1,4,2,2,4,7,2,1,4,2,2,5,1,2,7,8,7],4),([1,2,2,2,9,2,7,3,4,3,1,9,1,7,9,5,1,2,1,6,2],1),30321003858715622780856934939571920)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_53 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 30321166838972590448348318361563920≤n ∧ n≤53088815526992496085616409120091720 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,5,7,8,1,5,4,4,1,5,2,5,2,2,2,5,8,8,7,1,5],3),([1,2,2,2,9,6,5,2,8,4,3,4,6,6,7,7,2,7,8,3,1],1),30321166838972590448348318361563920),
    (([1,5,7,8,5,4,8,2,1,5,5,4,7,1,2,7,5,4,5,7,8],2),([1,2,2,6,4,7,5,4,9,7,4,1,7,2,1,1,7,7,7,1,3],3),30338119618473920864001376005563920),
    (([1,5,9,4,6,4,1,7,4,4,9,8,3,3,2,2,8,3,9,8,8],4),([1,2,7,8,1,4,4,8,4,1,4,2,2,8,2,7,8,8,4,5,7],2),31015050209811987610197116923477220),
    (([1,5,9,4,6,4,3,3,4,9,8,8,4,6,7,2,9,8,4,7,6],3),([1,2,7,8,1,4,8,5,2,8,2,1,7,8,2,7,8,4,1,1,2],3),31015083423306398859476746942101860),
    (([1,5,9,4,6,4,7,2,5,9,3,3,1,1,6,6,1,2,2,1,7],2),([1,2,7,8,1,7,1,1,2,5,7,4,2,7,8,2,1,2,7,1,1],1),31015300686591836779148101158219620),
    (([1,8,4,1,4,7,5,8,1,5,8,7,1,5,4,4,5,1,8,7,1],1),([1,5,9,2,8,4,4,6,7,6,4,4,3,7,8,3,2,8,4,6,7],3),38695699522184921575777434564586420),
    (([1,9,6,3,6,1,5,2,3,3,2,2,4,2,8,2,4,3,9,9,7],1),([1,7,4,5,4,1,2,8,8,4,1,2,1,5,5,5,5,1,8,4,1],2),43867973360709129730563995445592400),
    (([2,1,1,2,4,4,7,5,7,1,5,4,8,7,1,5,5,2,8,8,2],3),([1,7,9,4,3,4,7,7,8,9,1,5,6,7,6,2,2,7,7,7,7],2),46905494614009973703841021647593920),
    (([2,4,1,1,1,1,8,8,1,2,4,2,7,2,4,7,2,8,5,2,4],1),([1,9,2,7,4,3,6,2,1,2,4,4,8,4,1,9,5,6,4,7,1],3),53088542948571110268975119393493640),
    (([2,4,1,1,1,1,8,8,1,2,4,2,7,7,2,2,5,5,7,8,7],4),([1,9,2,7,4,3,6,2,1,2,4,4,8,4,3,1,9,2,8,5,7],4),53088542948571118760740585131446920),
    (([2,4,1,1,1,1,8,8,1,2,4,2,7,7,2,8,1,7,4,2,5],3),([1,9,2,7,4,3,6,2,1,2,4,4,8,4,3,2,2,9,2,9,8],0),53088542948571118839488710699160200),
    (([2,4,1,1,1,2,2,1,7,7,1,2,4,2,2,5,7,1,8,7,4],1),([1,9,2,7,4,3,6,2,5,1,8,7,1,5,9,2,4,8,1,6,4],1),53088543262887129008311047742925800),
    (([2,4,1,1,4,1,7,1,1,5,1,8,7,7,8,2,2,7,8,8,4],4),([1,9,2,7,4,4,6,5,1,1,8,1,9,6,7,3,7,3,9,3,1],1),53088815526992494747815543660302920),
    (([2,4,1,1,4,1,7,1,1,5,1,8,7,8,2,1,4,2,7,7,2],2),([1,9,2,7,4,4,6,5,1,1,8,1,9,6,7,4,1,3,6,5,2],1),53088815526992496056978652108041800),
    (([2,4,1,1,4,1,7,1,1,5,1,8,7,8,2,4,7,1,5,4,2],3),([1,9,2,7,4,4,6,5,1,1,8,1,9,6,7,4,1,7,2,6,6],1),53088815526992496085616409120091720)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_54 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 53088815610346447093775892348041800≤n ∧ n≤602370046976776724547381375889612900 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,4,1,1,4,1,7,4,1,1,8,5,1,7,2,2,4,2,7,7,2],2),([1,9,2,7,4,4,6,5,1,9,3,1,5,7,3,6,4,4,3,9,1],2),53088815610346447093775892348041800),
    (([2,4,2,5,1,1,4,7,2,8,2,5,8,8,8,8,1,4,2,7,8],3),([1,9,3,1,3,1,2,2,9,8,1,8,2,8,2,2,5,8,2,8,3],4),53220870247052063116230746188529320),
    (([2,5,5,7,7,2,5,4,1,5,5,5,1,2,2,4,4,5,1,5,1],1),([2,1,2,3,7,4,5,4,7,1,4,9,1,7,9,8,6,2,6,4,1],2),58665360857086229880138303188813920),
    (([2,5,5,7,7,5,1,5,4,7,4,2,4,8,7,1,5,5,4,5,7],4),([2,1,2,4,4,2,2,5,7,8,3,4,3,8,1,4,9,4,6,4,7],3),58667994073014871674195874529438920),
    (([2,5,5,8,2,7,8,2,4,5,2,7,7,8,8,8,2,4,5,1,5],3),([2,1,3,1,4,5,4,9,9,7,8,6,7,2,8,3,3,9,8,7,3],3),58717223407211777122929550257488920),
    (([2,5,5,8,2,8,1,4,5,4,4,7,7,7,5,8,5,4,2,8,2],2),([2,1,3,1,5,8,4,2,9,8,9,7,7,9,6,8,8,7,9,7,2],3),58717488389036996040304905745088920),
    (([2,5,7,6,6,3,3,4,8,1,6,7,4,2,6,1,8,2,7,4,6],2),([2,2,1,1,5,5,8,2,8,2,2,7,2,1,7,7,7,7,7,1,5],0),59919638901441366657154239947167400),
    (([2,5,8,4,4,1,8,1,2,1,8,2,5,2,5,1,2,5,1,1,5],3),([2,2,5,4,9,1,8,6,4,3,1,2,3,6,9,4,6,2,4,7,4],3),60550486793471971518260224702838920),
    (([2,8,5,7,4,4,8,2,7,7,7,2,8,4,1,2,2,8,8,2,2],2),([2,6,1,7,5,8,6,4,8,6,7,7,7,9,6,9,5,3,5,6,4],1),78043264911374370088050409627425400),
    (([2,8,5,7,4,8,5,1,5,2,1,7,8,2,2,7,5,5,7,7,2],2),([2,6,1,7,7,6,4,8,1,1,1,3,5,9,8,4,4,9,1,3,3],3),78049249460382246029623601235788920),
    (([4,4,4,2,7,8,5,4,7,7,7,2,4,1,4,4,2,8,8,2,2],2),([3,8,6,5,3,9,7,6,1,7,6,1,6,8,7,8,7,6,5,3,5],2),176350967526070910232923625276487900),
    (([4,4,4,8,8,2,7,8,1,7,7,2,2,7,4,5,1,8,8,2,2],2),([3,8,6,7,3,6,1,7,5,4,8,5,5,6,4,1,1,2,6,6,3],4),176854290979453291327021244448487900),
    (([5,8,1,8,5,8,2,4,4,2,2,5,1,2,5,7,7,1,8,7,1],1),([5,2,9,4,2,7,6,8,6,8,7,8,8,1,9,3,1,9,6,3,9],2),328057040365519314637723714642711420),
    (([7,7,5,1,1,4,4,4,7,1,7,1,2,8,1,1,4,2,2,8,2],3),([6,8,8,2,4,1,2,1,3,5,6,1,9,4,7,1,2,8,9,4,2],2),592044739710999922878761167282142260),
    (([7,7,8,2,8,2,7,4,5,4,4,8,2,7,2,1,2,8,8,2,2],2),([6,8,9,9,2,4,6,1,2,9,7,7,7,5,5,6,8,6,4,7,5],1),602370046976776724547381375889612900)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_55 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 673886862329779903993544878735154420≤n ∧ n≤677539829085939050925568477695670420 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([8,1,4,9,7,6,7,3,7,2,9,4,8,5,2,8,5,7,8,6,5],3),([7,4,7,2,1,4,1,5,1,2,7,4,4,1,1,7,8,4,4,1,7],1),673886862329779903993544878735154420),
    (([8,1,4,9,7,6,7,8,6,5,1,2,2,2,9,7,4,6,6,9,9],2),([7,4,7,2,1,4,7,8,5,2,8,5,7,2,5,4,2,4,4,2,4],4),673887001448298022978123994677670900),
    (([8,2,1,2,5,4,5,4,1,1,8,7,4,1,5,4,1,1,2,7,7],4),([7,4,8,4,5,6,8,3,3,1,2,1,4,4,7,9,8,7,7,3,2],1),677133804912684642464810142171286420),
    (([8,2,1,2,5,4,5,4,1,7,5,4,2,2,8,8,5,5,8,8,5],2),([7,4,8,4,5,6,8,3,3,1,4,2,9,2,9,7,9,4,4,9,4],3),677133804921295636485466796575126420),
    (([8,2,1,6,6,1,7,4,9,3,3,3,5,7,7,2,3,6,8,9,4],1),([7,4,8,4,7,4,5,2,4,1,2,1,5,4,5,7,7,5,5,1,4],1),677197036955365392417816039756554900),
    (([8,2,1,6,6,6,8,4,6,2,3,2,3,7,2,3,2,3,7,2,1],1),([7,4,8,4,7,4,7,8,1,2,2,1,7,8,7,8,8,4,2,7,7],1),677198369451545741275469890582050452),
    (([8,2,1,6,6,7,7,2,7,5,7,4,8,6,8,9,9,2,7,6,6],3),([7,4,8,4,7,4,8,5,2,8,7,8,5,7,1,8,1,4,7,4,1],1),677198760906214773145279853724286100),
    (([8,2,1,6,9,8,7,1,1,1,4,5,1,9,2,8,6,5,4,6,7],1),([7,4,8,4,7,7,4,1,1,1,5,4,4,8,7,4,7,1,1,8,1],4),677211846736882201800782415261408020),
    (([8,2,1,6,9,8,7,1,3,2,9,6,2,2,8,7,1,3,5,4,6],1),([7,4,8,4,7,7,4,1,1,8,7,2,4,2,4,8,4,5,5,8,2],0),677211846948991310702203281672794900),
    (([8,2,2,1,7,1,7,7,4,5,7,8,2,4,2,2,4,4,5,8,2],2),([7,4,8,4,9,7,6,1,9,6,2,6,2,2,1,5,9,2,9,6,3],2),677314820458672204511223051998489620),
    (([8,2,2,1,7,7,2,5,7,8,1,4,2,4,1,4,2,1,1,7,8],3),([7,4,8,4,9,7,6,7,5,8,2,8,9,7,2,1,6,2,7,1,3],4),677315403176875019021108093188098580),
    (([8,2,2,1,7,8,1,4,4,7,5,7,7,4,1,2,8,1,8,7,7],1),([7,4,8,4,9,7,6,8,5,7,9,6,7,3,3,2,8,5,7,6,8],1),677315594094627685307253338565121300),
    (([8,2,2,8,1,7,5,9,6,4,9,4,4,9,6,6,9,3,1,6,2],3),([7,4,8,5,7,7,8,2,2,1,5,4,4,1,7,5,8,5,5,7,4],1),677539760822160508537307481415754900),
    (([8,2,2,8,1,7,8,1,1,5,1,5,7,1,7,4,5,5,1,8,5],2),([7,4,8,5,7,7,8,3,1,8,8,4,3,1,7,2,7,9,2,7,4],4),677539829080426697501406668025526420),
    (([8,2,2,8,1,7,8,1,1,7,5,2,4,2,1,4,8,8,8,5,5],3),([7,4,8,5,7,7,8,3,1,8,8,4,9,8,4,8,8,8,9,6,1],3),677539829085939050925568477695670420)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_56 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 677539829086980707719543345171249300≤n ∧ n≤1083584454530455834261953237905036920 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([8,2,2,8,1,7,8,1,1,7,7,8,2,1,2,1,2,4,5,7,1],1),([7,4,8,5,7,7,8,3,1,8,8,5,3,4,2,9,4,9,7,9,2],4),677539829086980707719543345171249300),
    (([8,2,2,8,5,1,5,7,8,5,5,7,5,2,1,4,8,7,4,1,2],3),([7,4,8,5,7,9,2,9,8,1,7,3,8,3,7,7,9,9,4,6,7],1),677553536036079052533134172191926420),
    (([8,2,4,2,5,4,7,7,4,7,1,4,7,2,8,4,2,8,8,2,2],2),([7,4,8,7,5,5,6,3,4,8,1,4,7,5,9,9,4,9,7,3,9],3),678251292054912165209757946673362900),
    (([8,4,1,1,2,2,7,8,7,5,8,4,7,7,2,2,5,2,4,7,2],3),([7,5,8,3,1,6,3,4,7,8,8,1,8,7,8,6,7,2,1,4,6],1),697740343749133702812256244694101620),
    (([8,4,1,5,4,8,7,2,7,7,7,2,4,5,7,7,8,5,4,7,2],3),([7,5,8,3,6,2,9,6,8,8,1,4,4,3,4,4,8,6,6,4,1],3),697829562643306247186267834492338420),
    (([8,4,2,1,2,3,2,6,7,6,9,2,7,4,3,1,7,8,2,5,4],2),([7,5,8,4,5,7,8,2,2,7,2,4,8,1,5,2,7,7,2,5,8],0),698106999550941190447587467710454900),
    (([8,4,2,1,2,3,4,1,4,7,3,4,5,9,6,1,6,7,4,3,6],2),([7,5,8,4,5,7,8,2,4,2,4,4,2,4,8,2,5,7,2,5,1],1),698107004061482642668125493710134900),
    (([8,4,2,1,3,2,3,3,7,7,8,8,7,2,3,1,3,1,3,7,5],2),([7,5,8,4,5,7,8,8,5,4,5,5,2,1,7,5,7,7,1,1,2],0),698107700869817702671137884434454900),
    (([8,4,2,1,3,3,1,4,2,5,8,2,8,8,7,1,4,2,6,3,6],2),([7,5,8,4,5,7,8,8,7,2,2,4,2,1,7,8,4,2,5,5,2],3),698107745794003368392684623524374900),
    (([8,4,2,2,5,4,1,8,7,4,2,5,1,2,5,8,5,5,8,8,5],2),([7,5,8,4,6,4,1,4,1,6,4,4,1,9,9,3,4,1,2,9,9],2),698130599732878230448028986262626420),
    (([8,4,2,2,5,4,1,8,7,4,2,5,2,8,1,2,1,5,8,4,2],3),([7,5,8,4,6,4,1,4,1,6,4,4,2,7,2,6,2,2,7,8,2],2),698130599732882490925234253481058420),
    (([8,4,2,2,5,4,1,8,7,4,2,5,5,2,1,8,5,5,8,8,5],2),([7,5,8,4,6,4,1,4,1,6,4,4,3,9,3,2,9,8,9,2,8],4),698130599732897667753800506262626420),
    (([8,4,2,2,5,4,2,2,8,1,1,8,4,7,5,1,8,8,7,8,4],4),([7,5,8,4,6,4,1,4,6,3,3,1,2,7,2,7,1,3,6,4,7],4),698130602526755460899155940357986420),
    (([8,4,2,4,1,5,7,7,2,8,7,2,7,2,8,4,2,8,8,2,2],2),([7,5,8,4,7,7,9,3,8,8,5,3,5,2,2,9,4,9,7,3,9],3),698204713953156304613959223235862900),
    (([1,1,8,7,2,2,5,8,4,7,2,1,8,1,5,2,1,5,4,1,4,2],2),([9,2,6,7,5,3,2,4,4,1,6,1,6,4,2,6,9,2,1,1,1],1),1083584454530455834261953237905036920)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_57 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 1090543447550314274917501326613592140≤n ∧ n≤1337977805083137489663466598690147900 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,2,1,4,1,4,8,7,7,2,2,2,5,4,2,8,4,1,1,2,8,2],2),([9,3,1,1,8,7,2,2,1,9,6,4,1,6,9,1,8,1,2,6,5],2),1090543447550314274917501326613592140),
    (([1,2,1,4,1,4,8,7,7,5,8,7,1,1,5,2,1,5,8,8,8,8],2),([9,3,1,1,8,7,2,2,7,3,5,3,7,1,9,2,3,2,9,8,7],2),1090543447766178901708940387006137420),
    (([1,2,1,4,1,4,8,7,7,5,8,8,8,4,8,4,1,7,2,2,8,1],1),([9,3,1,1,8,7,2,2,7,4,3,2,8,2,5,1,7,4,6,9,8],3),1090543447770364208649119591001621580),
    (([1,2,1,7,1,2,4,5,5,1,8,1,2,4,7,2,4,8,7,8,8,8],3),([9,3,1,9,7,6,2,2,7,1,8,5,3,2,4,2,1,7,1,2,3],4),1090886689264713975268688336426832220),
    (([1,2,4,7,5,4,8,7,4,2,1,2,4,8,7,7,4,2,8,8,2,2],2),([9,3,7,1,5,6,8,3,3,1,7,8,6,8,9,5,7,5,3,3,8],1),1098669654827579545437627418382737900),
    (([1,5,6,1,6,6,7,6,8,4,2,8,3,2,1,7,9,1,7,4,7,3],2),([1,1,4,1,2,1,2,7,8,8,5,7,5,7,8,1,7,2,5,2,4,1],2),1337886997620813980353532476101890900),
    (([1,5,6,1,6,6,8,1,7,3,8,2,1,6,4,9,2,6,2,7,3,8],2),([1,1,4,1,2,5,1,2,8,5,1,8,8,2,8,4,5,2,4,2,4,1],4),1337887560722708370493168952673818900),
    (([1,5,6,1,7,8,2,6,6,1,2,7,8,3,3,3,3,4,3,8,8,8],4),([1,1,4,2,2,7,1,7,4,7,1,1,8,4,2,1,4,8,2,5,2,4],2),1337947907604307943288198483402985620),
    (([1,5,6,1,8,4,6,4,7,1,2,8,2,1,4,1,3,9,8,3,7,1],1),([1,1,4,2,5,8,8,4,1,1,8,7,4,1,1,4,4,5,2,5,4,7],2),1337977804497860112446626443474275900),
    (([1,5,6,1,8,4,6,4,7,1,2,8,2,1,4,1,6,6,8,2,7,3],4),([1,1,4,2,5,8,8,4,1,1,8,7,4,1,1,4,8,1,1,1,1,4],2),1337977804497860113339561889997033020),
    (([1,5,6,1,8,4,6,4,7,1,2,8,2,3,6,6,4,4,8,8,4,3],1),([1,1,4,2,5,8,8,4,1,1,8,7,4,4,5,8,8,4,8,5,7,1],4),1337977804497867068559824294425955900),
    (([1,5,6,1,8,4,6,4,7,2,6,2,3,4,5,1,7,2,5,4,1,2],3),([1,1,4,2,5,8,8,4,1,7,2,2,4,2,4,7,7,4,8,4,7,8],3),1337977804858937049772995792752975420),
    (([1,5,6,1,8,4,6,4,7,2,6,2,3,8,4,9,9,9,6,6,4,7],3),([1,1,4,2,5,8,8,4,1,7,2,2,7,5,2,8,4,5,4,2,2,7],4),1337977804859026403481293016551267900),
    (([1,5,6,1,8,4,6,4,7,2,7,2,2,9,4,2,9,4,7,3,4,7],2),([1,1,4,2,5,8,8,4,1,7,7,5,5,1,5,1,4,5,2,5,1,7],4),1337977804918445740821548562740579900),
    (([1,5,6,1,8,4,6,4,7,2,9,4,8,9,9,2,8,9,2,2,6,8],3),([1,1,4,2,5,8,8,4,1,8,8,8,1,7,5,8,4,8,5,1,8,4],1),1337977805083137489663466598690147900)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_58 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 1349775043888829152116797640597594620≤n ∧ n≤1723032502769361807595222955371375000 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,5,6,8,9,6,5,7,1,7,7,1,8,1,9,4,6,2,6,7,2,6],3),([1,1,7,7,4,7,2,8,1,7,2,5,2,1,1,4,1,4,2,7,1,1],1),1349775043888829152116797640597594620),
    (([1,5,7,5,7,1,8,7,2,5,4,4,1,5,8,5,1,7,1,2,8,5],3),([1,1,9,4,6,3,7,2,2,4,1,7,2,6,8,5,6,1,9,2,9,9],3),1358161279420699006410717779363438920),
    (([1,6,8,6,4,8,8,9,5,1,2,1,3,9,6,2,8,7,7,3,8,7],2),([1,4,2,1,4,1,5,5,4,4,7,4,8,2,2,1,7,7,2,7,2,1],1),1510529574065129560155636771532548500),
    (([1,6,8,6,7,4,6,1,2,6,1,1,9,3,3,2,4,7,9,8,9,3],4),([1,4,2,4,8,2,7,2,1,1,4,2,8,1,7,1,4,7,2,8,1,2],0),1511489849577766247903161223845831700),
    (([1,6,8,6,7,4,6,1,2,6,1,2,4,7,7,4,3,1,8,4,1,1],4),([1,4,2,4,8,2,7,2,1,1,4,5,5,2,8,5,7,8,5,1,2,1],2),1511489849577983277776068354507514900),
    (([1,6,8,6,7,4,6,1,2,6,4,2,5,9,2,3,9,6,9,1,2,9],3),([1,4,2,4,8,2,7,2,1,4,8,8,5,1,5,1,4,7,2,2,1,5],0),1511489849686770328121133442914554900),
    (([1,6,8,6,7,4,6,1,2,6,4,2,6,3,2,3,1,5,8,1,6,8],1),([1,4,2,4,8,2,7,2,1,4,8,8,5,7,8,2,7,8,2,7,5,4],4),1511489849686867492498054026346337300),
    (([1,7,1,8,2,5,4,8,1,1,8,1,7,4,7,7,8,2,1,8,7,7],1),([1,4,6,8,3,6,1,5,2,4,3,2,9,1,5,8,2,8,4,1,6,9],4),1556449400858392643296275322381246300),
    (([1,7,6,9,4,2,8,7,8,4,2,8,4,1,2,8,7,5,8,9,1,6],3),([1,5,1,8,7,7,8,2,2,1,5,4,7,2,2,2,5,4,4,1,4,5],0),1626203655921778177169584100119642400),
    (([1,7,6,9,4,2,8,8,7,9,5,1,6,2,1,3,2,8,8,4,3,2],2),([1,5,1,8,7,7,8,5,1,2,1,4,8,1,2,1,5,1,8,5,4,5],3),1626204146209901953632014954978842400),
    (([1,7,6,9,4,4,5,8,3,7,7,2,7,3,1,6,1,3,1,8,2,1],3),([1,5,1,8,8,1,8,7,2,4,5,2,7,4,2,4,1,2,1,7,5,5],3),1626244076717893725458424041090302400),
    (([1,8,1,8,9,9,7,1,2,2,1,3,2,6,4,2,5,7,9,6,7,8],1),([1,5,8,5,1,2,2,2,1,5,4,8,7,1,1,8,5,1,7,4,4,8],0),1719788453697962594772639297818017400),
    (([1,8,2,3,1,6,1,8,2,4,9,3,6,9,7,5,1,4,9,7,6,2],1),([1,5,8,5,7,4,1,1,1,4,5,8,4,1,1,4,8,2,8,4,7,8],0),1721182337929965303622202263241317400),
    (([1,8,2,3,1,6,3,8,3,8,6,2,7,8,2,6,6,8,9,2,6,5],1),([1,5,8,5,7,4,1,4,7,4,5,2,8,8,8,1,4,2,5,5,8,8],0),1721182493507323163296757378178517400),
    (([1,8,2,5,8,1,7,1,4,8,4,7,7,8,8,1,1,2,1,1,7,8],2),([1,5,8,6,3,8,5,7,1,8,2,9,7,6,1,4,8,7,4,6,2,1],4),1723032502769361807595222955371375000)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_59 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 1726085227103337170888120670242245400≤n ∧ n≤10106441616306882775983299280797722400 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,8,2,8,5,1,4,8,9,6,4,3,2,4,8,1,1,7,6,3,7,4],2),([1,5,8,7,1,1,1,8,7,4,8,8,8,7,4,1,8,7,5,5,2,7],2),1726085227103337170888120670242245400),
    (([1,9,4,8,7,1,4,8,7,1,3,1,2,5,7,7,2,9,3,2,1,6],3),([1,7,1,2,7,4,5,5,2,4,7,7,2,8,5,1,4,8,4,2,2,4],1),1942928262441314491236499146085036400),
    (([4,1,8,7,4,2,8,7,4,5,5,8,4,1,5,8,2,8,7,1,4,5],2),([3,7,7,6,6,7,6,3,2,4,4,3,6,9,4,5,2,2,4,3,8,7],3),7393985666302114929952479253912853920),
    (([4,7,9,7,1,4,4,4,8,1,7,9,9,1,9,7,3,9,4,6,9,5],2),([4,4,1,2,2,4,8,8,7,1,7,5,8,7,5,8,4,7,4,7,4,1],1),9856187349650213546538875135916473600),
    (([4,8,2,7,7,8,6,7,1,8,1,4,2,8,4,3,9,8,1,3,7,5],3),([4,4,5,2,2,2,7,1,7,8,2,1,7,2,5,5,1,8,1,4,4,5],0),9960206292133117642720513497649642400),
    (([4,8,2,9,6,4,9,3,8,7,5,2,8,1,7,9,8,1,6,9,1,2],2),([4,4,5,5,2,4,8,4,2,7,7,7,1,4,4,2,7,5,5,5,2,4],2),9970632990189388930589468563636042400),
    (([4,8,4,1,2,1,4,8,8,4,4,1,4,4,4,4,2,4,4,2,4,5],2),([4,4,6,5,1,7,3,2,2,8,8,5,4,4,1,3,1,3,8,8,2,8],4),10024351237104358424344345344305312800),
    (([4,8,4,1,4,7,7,2,8,4,4,7,1,8,2,8,7,4,8,4,5,1],1),([4,4,6,5,2,7,5,2,2,6,4,8,2,4,4,4,8,6,1,3,5,6],4),10024584233594051728324058966798970400),
    (([4,8,4,1,4,7,7,7,4,8,5,4,2,1,4,1,7,8,2,8,2,2],2),([4,4,6,5,2,7,5,5,7,9,8,1,4,8,4,9,6,3,8,2,2,7],1),10024585638255454806104424216137850400),
    (([4,8,4,8,8,5,2,7,4,7,5,2,7,1,2,5,8,2,1,2,1,8],3),([4,4,7,1,7,2,4,7,9,6,2,5,8,2,1,1,8,7,2,6,6,9],3),10073129636822101084040604802504421920),
    (([4,8,5,4,8,7,1,7,4,1,4,2,7,2,1,7,8,4,4,8,2,2],2),([4,4,7,7,2,5,8,8,1,6,3,8,1,7,2,4,4,6,9,4,7,7],0),10106441577044461294422836537012250400),
    (([4,8,5,4,8,7,1,7,4,2,2,2,7,2,1,7,8,4,4,8,2,2],2),([4,4,7,7,2,5,8,8,1,6,6,4,1,7,2,4,4,6,9,4,7,7],0),10106441578305352269512456537012250400),
    (([4,8,5,4,8,7,1,7,4,8,2,1,7,4,8,8,7,1,2,2,5,7],1),([4,4,7,7,2,5,8,8,2,4,6,9,1,4,8,4,1,4,8,2,2,1],3),10106441615855438779815296531609708320),
    (([4,8,5,4,8,7,1,7,4,8,2,8,9,4,8,6,2,3,4,6,4,6],2),([4,4,7,7,2,5,8,8,2,4,7,4,7,4,4,5,8,5,4,2,2,1],4),10106441616229538336041121756905498400),
    (([4,8,5,4,8,7,1,7,4,8,2,9,8,3,8,7,8,2,4,6,4,4],2),([4,4,7,7,2,5,8,8,2,4,7,5,5,4,4,2,8,8,5,8,1,4],2),10106441616306882775983299280797722400)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_60 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 10106441651529794455780169313105413920≤n ∧ n≤12055682802997577495075741144848845560 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([4,8,5,4,8,7,1,7,5,4,5,8,2,4,7,2,1,2,5,4,1,5],2),([4,4,7,7,2,5,8,8,2,8,2,7,8,7,3,8,9,2,6,7,2,4],2),10106441651529794455780169313105413920),
    (([4,8,5,4,8,7,1,7,5,4,7,2,7,1,2,2,2,2,8,5,2,7],1),([4,4,7,7,2,5,8,8,2,8,4,2,9,3,8,8,4,1,9,4,4,7],2),10106441652784993451513771728725509920),
    (([4,8,5,4,8,7,1,7,5,4,8,2,4,4,7,1,2,5,2,8,7,8],3),([4,4,7,7,2,5,8,8,2,8,4,9,8,1,8,9,2,9,8,9,7,1],4),10106441653850591598119592966661637920),
    (([4,8,5,4,8,7,1,7,5,4,8,2,4,7,8,4,7,1,2,8,2,5],2),([4,4,7,7,2,5,8,8,2,8,4,9,8,2,9,6,1,8,2,7,1,4],4),10106441653852503769300810997736965920),
    (([4,8,5,4,8,7,1,7,5,4,8,2,5,1,5,4,8,7,2,8,2,1],4),([4,4,7,7,2,5,8,8,2,8,4,9,8,3,8,3,8,6,3,3,3,3],2),10106441653854634727660619464222213920),
    (([4,8,5,4,8,7,1,7,5,8,8,7,1,1,8,1,8,5,8,4,4,5],3),([4,4,7,7,2,5,8,8,3,4,4,3,7,9,2,8,8,1,3,2,2,6],1),10106441697326223776255377884246533920),
    (([4,8,5,4,8,7,1,7,5,8,8,7,1,1,8,1,8,7,7,8,5,5],2),([4,4,7,7,2,5,8,8,3,4,4,3,7,9,2,8,8,1,8,4,4,6],2),10106441697326223810915581951144453920),
    (([4,8,5,4,8,7,1,8,1,1,7,4,1,7,1,2,7,4,1,2,7,8],3),([4,4,7,7,2,5,8,8,6,4,5,7,4,7,7,3,5,8,8,4,1,3],3),10106442184235614258205110241095194400),
    (([4,8,5,4,8,7,1,8,1,8,7,8,1,8,4,7,5,8,8,8,8,1],4),([4,4,7,7,2,5,8,8,6,4,9,6,8,9,4,1,1,9,3,6,8,9],4),10106442196897677861116105285824517920),
    (([4,9,2,8,1,6,1,7,8,7,1,5,4,7,3,2,1,2,1,7,8,4],1),([4,5,8,5,7,5,4,4,5,7,8,1,8,2,2,1,2,4,8,2,1,8],3),10709110132018858182285016419687172400),
    (([4,9,3,4,2,6,9,6,1,7,8,4,8,7,6,5,2,6,3,3,1,5],1),([4,5,8,7,4,2,2,8,4,1,8,7,7,1,2,7,4,7,4,7,2,8],3),10730706516151686719837713909463737520),
    (([5,1,9,1,6,5,6,7,4,4,1,4,8,5,4,2,1,4,2,4,9,3],1),([4,7,1,1,4,4,2,7,1,1,8,1,2,7,5,2,7,8,1,4,1,7],1),11595170397207869311522781236445654420),
    (([5,2,4,1,5,8,2,1,1,2,8,4,7,1,5,7,8,2,8,1,2,5],3),([4,7,3,1,1,3,3,2,3,6,5,4,9,8,8,3,4,8,8,4,8,4],3),11649221423420218679454382050097636420),
    (([5,3,6,8,6,3,4,4,6,1,7,8,1,6,6,4,7,6,6,1,2,5],1),([4,7,7,4,8,1,5,7,2,2,2,7,8,8,2,1,8,7,4,7,2,8],3),11997692565442186853672646371607487520),
    (([5,3,7,9,1,3,1,7,4,8,7,6,8,4,6,1,6,8,3,3,6,2],2),([4,7,7,8,4,4,2,1,4,7,2,8,4,8,2,7,2,8,1,7,1,5],3),12055682802997577495075741144848845560)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_61 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 12497466394353091552759983883651718920≤n ∧ n≤49115035472242190422215494278533675400 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([5,4,8,4,1,2,8,2,8,1,8,5,2,4,1,4,2,5,2,7,7,5],2),([4,8,3,7,1,5,2,4,6,2,3,9,8,4,8,2,2,2,9,4,8,4],1),12497466394353091552759983883651718920),
    (([5,4,8,4,7,2,4,5,5,8,1,5,1,2,2,8,2,2,7,4,7,8],2),([4,8,3,7,6,5,1,8,2,8,2,6,6,3,1,1,3,9,2,9,7,8],2),12500911568901934071744528237641798920),
    (([5,4,9,1,1,7,6,3,6,8,3,8,4,1,8,4,9,6,9,4,8,4],1),([4,8,4,7,1,5,1,8,8,4,7,1,7,5,4,7,5,4,4,5,2,7],4),12568938233946279504632650640444047400),
    (([5,4,9,4,3,8,3,7,4,9,2,7,1,4,8,6,4,6,9,3,8,8],2),([4,8,4,8,2,5,4,7,5,5,7,2,8,5,8,7,4,4,7,4,4,2],3),12582183248133387127936662079439647400),
    (([5,4,9,4,7,4,9,8,7,4,4,7,6,8,3,9,2,4,6,2,8,1],3),([4,8,4,8,5,5,7,4,5,4,7,1,1,4,7,5,8,1,1,1,8,4],2),12585407833457348836451274807315487400),
    (([5,5,8,5,7,4,1,2,4,4,5,8,7,8,8,1,2,4,7,4,7,5],2),([4,8,8,6,7,7,6,1,6,2,3,6,8,9,5,4,6,3,6,3,6,3],1),13050870523641774021668507147948738920),
    (([5,7,5,2,4,4,8,2,2,8,8,2,7,8,4,1,5,8,7,1,4,5],2),([4,9,8,8,8,3,5,7,9,8,6,6,8,7,6,3,6,7,2,1,3,9],3),14120023763623081058817923810522228920),
    (([5,9,7,2,4,1,4,7,9,2,1,8,1,8,6,9,1,3,7,7,8,8],1),([5,5,7,2,1,2,2,1,4,2,5,8,1,5,7,1,1,4,4,8,1,4],1),16167766638081243580909919117892052400),
    (([1,2,2,1,1,4,4,7,8,4,7,7,5,7,8,4,4,2,2,8,8,2,2],2),([9,3,2,8,5,3,2,2,2,2,4,8,5,7,6,1,7,8,5,9,8,8],4),49114638037441045854773663915433675400),
    (([1,2,2,1,4,8,7,2,7,1,1,1,1,2,8,2,2,7,8,4,5,7,1],1),([9,3,2,8,5,8,4,2,7,1,1,2,6,2,5,9,2,6,9,6,8,4],4),49115035435352679675763574891670161800),
    (([1,2,2,1,4,8,7,2,7,1,1,1,2,1,4,4,4,1,4,7,4,2,5],3),([9,3,2,8,5,8,4,2,7,1,1,2,6,3,3,7,4,4,1,9,7,5],2),49115035435352687846190395838093560200),
    (([1,2,2,1,4,8,7,2,7,1,2,8,1,7,8,2,2,4,1,1,5,7,1],1),([9,3,2,8,5,8,4,2,7,1,2,2,7,2,9,1,8,7,5,6,8,2],2),49115035435391582567143412179373201800),
    (([1,2,2,1,4,8,7,2,7,1,2,8,2,5,8,8,5,4,4,1,1,5,4],4),([9,3,2,8,5,8,4,2,7,1,2,2,7,6,2,2,6,9,8,9,8,7],2),49115035435391725381433737000892438920),
    (([1,2,2,1,4,8,7,2,7,2,8,4,1,8,7,1,1,4,7,8,8,5,4],1),([9,3,2,8,5,8,4,2,7,2,2,5,8,4,3,4,8,8,8,2,3,5],4),49115035437137148639922968515560491400),
    (([1,2,2,1,4,8,7,2,8,2,7,7,5,4,4,1,4,4,7,8,8,2,2],2),([9,3,2,8,5,8,4,2,7,7,4,5,8,3,3,7,3,3,8,8,2,5],1),49115035472242190422215494278533675400)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_62 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 49115041298679801653777781606578475400≤n ∧ n≤147935880160593545075867092862983969400 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,2,2,1,4,8,8,4,7,2,2,2,5,8,2,7,7,7,8,2,8,2,2],2),([9,3,2,8,5,8,4,7,8,8,7,2,6,1,9,4,5,5,6,2,2,7],1),49115041298679801653777781606578475400),
    (([1,2,4,5,2,7,4,7,7,8,1,7,4,4,8,2,1,4,2,8,8,2,2],2),([9,3,6,7,5,8,7,7,1,2,9,1,8,7,9,5,6,8,4,7,4,5],2),49388656561192102004033585285146800400),
    (([1,2,8,1,1,8,4,8,7,1,5,7,8,7,7,2,8,1,2,8,8,2,2],2),([9,4,7,4,3,7,9,4,2,2,8,5,6,4,4,6,7,5,9,6,5,8],1),50366952526845776811752411027638050400),
    (([1,2,8,1,5,7,4,2,7,4,1,8,1,8,4,4,7,7,8,2,8,2,2],2),([9,4,7,4,5,5,8,8,2,8,2,3,8,9,3,7,5,2,6,2,2,7],1),50369111419639657756795198619687850400),
    (([1,5,8,1,2,1,7,1,5,5,7,7,5,4,8,5,1,2,7,1,8,7,4],1),([1,2,4,3,7,6,4,5,4,3,6,4,1,7,3,7,3,3,3,9,6,1,9],4),61706675031322881625127543211939226420),
    (([1,5,8,1,2,1,8,7,2,7,4,7,5,7,8,4,4,8,4,1,4,4,7],4),([1,2,4,3,7,6,4,6,7,8,2,1,5,7,9,3,6,3,9,3,2,2,4],3),61706679894089673700442076286956082420),
    (([1,5,8,1,2,1,8,7,2,7,4,8,8,1,4,8,8,7,8,5,8,4,8],2),([1,2,4,3,7,6,4,6,7,8,2,2,1,8,2,7,2,2,7,8,5,3,3],3),61706679894166457878502412977485772020),
    (([1,8,8,1,2,7,7,2,4,7,8,4,2,8,4,5,7,1,8,4,7,2,4],1),([1,6,6,5,1,7,7,2,8,4,8,9,8,2,2,8,6,3,1,7,2,9,2],1),82438614344201401523751706368281954860),
    (([1,8,8,1,2,7,7,2,4,7,8,4,2,8,5,1,2,1,7,8,8,2,2],2),([1,6,6,5,1,7,7,2,8,4,8,9,8,2,3,1,4,1,2,7,5,5,9],4),82438614344201577225093184031207737900),
    (([1,8,8,5,1,7,2,5,7,8,5,4,2,8,1,4,2,4,7,2,8,7,8],3),([1,6,6,7,7,2,1,5,6,2,4,7,3,4,6,2,2,1,3,4,3,9,6],2),82768617700224594138116798358816325420),
    (([1,9,9,1,1,6,4,1,7,4,2,6,4,6,7,7,7,1,9,6,5,4,7],2),([1,7,8,1,1,5,4,7,5,7,1,8,2,4,1,7,2,5,4,5,7,7,7],4),93104312780083042094523158245291387400),
    (([2,1,8,7,4,4,5,4,4,1,2,7,4,7,8,5,7,4,4,1,4,4,7],4),([1,7,9,9,8,8,7,8,5,9,4,1,2,4,1,6,8,1,4,2,3,6,3],1),96462499024874495021125562741092019920),
    (([2,5,5,7,4,1,7,4,2,4,2,8,1,8,5,8,2,8,8,7,1,4,5],2),([2,1,1,4,4,7,1,2,3,6,5,1,9,4,4,7,2,6,2,3,9,6,9],1),118736491038006806145181926327365978920),
    (([2,6,9,4,6,4,4,6,3,5,7,1,2,7,4,1,7,6,3,9,2,9,2],3),([2,4,5,1,8,7,1,4,4,7,5,4,7,4,4,8,2,5,4,1,2,4,8],0),136717434909606240840879146144931667400),
    (([2,7,8,1,8,2,9,2,4,7,7,5,1,4,8,2,6,8,9,4,3,6,3],1),([2,5,5,4,5,1,2,8,7,7,4,1,7,1,4,1,2,1,8,1,1,7,7],4),147935880160593545075867092862983969400)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_63 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 174320038706110105263020180551294987520≤n ∧ n≤4349775936277660855276028462039323031900 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,9,5,1,8,6,3,4,4,6,1,7,8,1,6,6,4,7,6,6,1,2,5],1),([2,7,2,7,4,8,1,5,7,2,2,2,7,8,8,2,1,8,7,4,7,2,8],3),174320038706110105263020180551294987520),
    (([3,2,1,7,6,3,6,3,1,4,8,1,4,5,9,3,7,8,6,8,3,2,7],1),([2,8,1,8,7,2,2,2,1,2,2,7,2,4,8,5,2,1,1,4,2,5,2],0),192100263996585787281728834924590814900),
    (([3,2,3,2,6,8,1,2,1,6,1,1,7,6,1,4,7,1,7,8,6,9,8],4),([2,8,2,5,4,8,1,2,7,1,1,1,8,1,4,1,4,5,5,7,4,8,1],4),192462261371410093320926290915676288900),
    (([3,2,3,2,6,8,1,2,1,6,1,7,7,3,5,2,2,9,8,2,7,1,7],1),([2,8,2,5,4,8,1,2,7,1,1,4,2,5,7,7,7,7,7,8,8,7,5],3),192462261371425240930881704860439168900),
    (([3,2,3,2,6,8,1,2,2,2,4,9,4,9,8,1,3,8,4,1,5,7,7],3),([2,8,2,5,4,8,1,2,7,2,4,1,1,1,8,5,1,2,8,7,1,2,4],4),192462261378451477091390863664035098500),
    (([4,1,1,1,8,4,2,8,7,7,2,8,5,8,8,7,5,7,2,8,7,2,8],3),([3,7,6,8,3,8,3,3,2,7,1,2,7,7,4,5,9,4,9,7,1,2,9],2),329771300828251448638203855972455933620),
    (([5,7,8,2,2,1,7,8,5,4,8,2,5,8,8,1,8,5,2,8,4,2,7],1),([5,1,7,1,1,1,4,8,4,3,4,1,8,7,4,1,1,9,6,7,8,1,2],1),650043684927484916543592798097075928920),
    (([6,4,1,6,2,1,5,4,7,7,6,3,2,2,9,1,3,6,6,1,4,7,8],3),([5,7,4,2,2,1,7,8,8,4,7,2,7,4,2,4,2,1,5,4,2,7,7],4),790140996977503345484386095705867015800),
    (([7,8,4,8,7,7,7,2,4,2,2,2,5,4,1,8,1,1,2,8,8,2,2],2),([6,9,6,7,3,2,2,6,5,4,4,4,8,5,4,2,2,8,5,9,9,4,6],1),1250191148360555670728902559985406800400),
    (([8,3,3,5,8,9,2,2,7,1,2,1,7,2,3,6,9,9,4,8,2,6,4],1),([7,5,4,1,2,4,7,2,7,2,5,7,4,2,1,4,1,2,5,1,7,7,5],3),1390062371429054423866654336455050249900),
    (([8,3,8,7,3,3,1,4,3,3,9,2,5,7,1,2,8,7,6,2,7,2,8],1),([7,5,7,2,7,4,4,5,2,5,1,1,2,2,1,7,2,4,8,1,8,7,2],3),1405589706066727707305161010811514013900),
    (([1,1,7,7,1,5,2,1,2,7,7,8,4,8,4,4,5,5,5,2,4,4,2,5],3),([9,2,3,1,7,4,6,6,3,8,5,8,8,4,7,7,7,1,4,6,4,4,6],2),2186441825341022082022300410076227226420),
    (([1,2,1,4,7,5,2,2,1,7,1,8,4,7,2,7,4,4,2,4,1,8,7,7],1),([9,3,1,4,1,3,8,5,5,4,8,4,8,2,7,1,7,9,4,3,6,8,1],1),2208442727589201598476097993351290871300),
    (([1,2,1,4,7,5,2,2,4,2,4,8,1,5,2,5,4,2,4,5,5,8,8,5],2),([9,3,1,4,1,3,8,5,8,3,2,3,3,3,4,4,4,1,7,2,7,4,9],4),2208442728384910461030868752274168876420),
    (([2,1,9,2,2,4,1,2,1,3,2,1,6,4,8,8,1,6,2,3,7,1,3,5],2),([1,8,1,7,1,1,5,1,7,2,4,1,5,2,1,5,4,2,4,8,7,1,7,7],4),4349775936277660855276028462039323031900)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_64 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 4349775956505731571214981366005982439900≤n ∧ n≤4355940521501843199414052013024842070300 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,1,9,2,2,4,1,5,8,6,4,1,7,2,6,4,9,3,4,9,6,7,7,7],2),([1,8,1,7,1,1,5,5,4,2,8,8,5,5,1,4,4,2,8,2,7,8,4,4],2),4349775956505731571214981366005982439900),
    (([2,1,9,2,2,4,1,8,9,4,7,8,2,7,1,7,6,9,5,7,2,4,6,7],2),([1,8,1,7,1,1,5,8,2,2,7,5,2,2,8,7,2,1,4,2,7,2,7,7],2),4349775991147231692493535439932926305500),
    (([2,1,9,3,1,3,7,4,4,3,5,3,2,1,7,2,2,8,4,7,1,3,6,3],2),([1,8,1,7,7,5,2,1,4,1,7,1,2,5,1,2,4,5,1,1,8,5,2,4],4),4350590000104553380213370811777129059900),
    (([2,1,9,3,1,3,7,4,4,8,8,6,2,5,5,7,8,2,1,2,8,4,6,7],3),([1,8,1,7,7,5,2,1,4,8,1,4,2,4,8,7,2,7,4,7,4,7,2,8],3),4350590001612895074039208357715518425020),
    (([2,1,9,6,1,2,6,5,1,4,7,2,2,1,7,4,7,2,1,1,8,7,8,4],1),([1,8,2,1,7,7,8,1,2,5,5,5,1,1,5,8,1,1,7,7,4,2,7,4],2),4355598175680300212652866905055449709900),
    (([2,1,9,6,3,7,4,4,4,8,7,3,3,1,2,4,4,4,5,6,3,7,9,8],3),([1,8,2,2,2,7,1,2,2,2,8,2,4,5,7,7,4,1,8,5,2,1,8,5],3),4355844726814656506605225351124412203900),
    (([2,1,9,6,3,7,4,5,4,6,1,2,8,4,5,7,8,2,1,2,8,4,6,7],3),([1,8,2,2,2,7,2,5,4,1,4,7,2,4,8,7,2,7,4,7,4,7,2,8],3),4355844933567227658011529367481143425020),
    (([2,1,9,6,4,1,7,8,1,2,1,1,3,5,2,2,8,9,2,8,3,8,7,8],1),([1,8,2,2,4,2,8,4,2,7,1,1,2,5,7,4,7,8,1,2,4,1,1,2],3),4355932748737627929960313001036003976860),
    (([2,1,9,6,4,1,7,8,1,2,1,3,1,6,5,2,4,8,3,6,5,1,6,9],3),([1,8,2,2,4,2,8,4,2,7,1,2,1,8,1,2,4,1,7,8,8,4,5,7],2),4355932748737824269482791891643395352220),
    (([2,1,9,6,4,1,7,8,1,2,1,4,4,9,4,4,8,4,2,1,2,5,2,1],2),([1,8,2,2,4,2,8,4,2,7,1,2,8,4,8,1,7,8,7,7,5,1,5,8],0),4355932748738078103332442049180552799900),
    (([2,1,9,6,4,1,7,8,1,2,3,1,7,5,3,7,7,3,7,6,9,3,1,6],4),([1,8,2,2,4,2,8,4,2,7,2,1,7,7,1,5,4,8,7,7,4,7,2,8],3),4355932748746730906696748432703805925020),
    (([2,1,9,6,4,1,7,8,1,2,3,1,7,5,3,7,8,9,7,7,3,3,7,8],4),([1,8,2,2,4,2,8,4,2,7,2,1,7,7,1,5,8,4,7,7,4,7,2,8],3),4355932748746730917499642995135805925020),
    (([2,1,9,6,4,1,7,8,1,2,3,1,7,8,1,3,1,2,7,1,2,1,5,6],2),([1,8,2,2,4,2,8,4,2,7,2,1,7,8,5,4,1,1,7,1,8,1,1,2],3),4355932748746743014445407175082211976860),
    (([2,1,9,6,4,1,7,8,1,2,3,1,7,8,3,6,5,6,8,7,9,9,3,6],3),([1,8,2,2,4,2,8,4,2,7,2,1,7,8,5,7,7,4,2,2,5,5,2,7],2),4355932748746743511582144395992243807900),
    (([2,1,9,6,4,2,7,8,4,3,5,1,1,2,2,9,2,2,4,1,1,8,3,4],1),([1,8,2,2,4,4,4,1,5,7,1,1,2,4,5,1,4,1,8,7,2,7,7,1],4),4355940521501843199414052013024842070300)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_65 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 4358130970279907724992467339938874479020≤n ∧ n≤4609507200071077391635151497284762557900 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,1,9,7,1,7,2,1,5,7,2,1,6,5,8,2,9,3,1,9,2,4,1,8],1),([1,8,2,4,1,4,7,1,1,1,4,2,1,7,7,5,1,7,7,2,1,7,8,7],1),4358130970279907724992467339938874479020),
    (([2,2,1,3,2,8,1,3,6,8,2,7,2,4,6,4,9,1,3,2,1,5,7,4],3),([1,8,2,8,2,1,5,4,1,8,4,5,2,2,5,2,5,4,1,4,1,2,8,8],0),4368410201058268171389159564624241829900),
    (([2,2,1,3,2,8,1,3,6,8,3,7,3,8,3,2,8,9,8,4,5,1,4,9],2),([1,8,2,8,2,1,5,4,1,8,4,7,8,1,2,4,4,8,8,8,1,8,4,2],3),4368410201062571854054402120269621045260),
    (([2,2,1,3,2,8,3,2,8,4,8,7,3,3,6,3,4,5,2,3,4,8,7,7],2),([1,8,2,8,2,1,5,7,5,2,5,2,1,8,8,4,2,1,8,5,7,2,2,5],0),4368410350556443898313677095077913829900),
    (([2,2,1,3,2,9,5,4,8,4,4,2,2,2,8,9,1,3,2,9,3,1,9,3],3),([1,8,2,8,2,2,1,1,5,4,8,1,2,8,5,4,2,2,8,4,2,1,4,2],3),4368412997232638524014839990136489490700),
    (([2,2,1,4,6,7,2,5,6,1,8,4,3,8,2,6,7,8,2,9,7,2,7,1],2),([1,8,2,8,4,1,1,4,5,1,1,1,5,2,8,2,1,7,8,2,7,8,5,8],3),4368821604093130174948267843396528757900),
    (([2,2,1,4,6,7,2,5,6,1,8,4,7,8,6,2,6,2,1,7,2,1,3,7],3),([1,8,2,8,4,1,1,4,5,1,2,2,1,4,8,8,2,2,1,1,2,5,1,2],0),4368821604093956102422045576565545589900),
    (([2,2,1,4,6,9,4,4,8,3,8,7,4,3,3,7,8,2,4,5,4,3,3,1],1),([1,8,2,8,4,2,8,7,4,8,1,7,1,2,2,7,1,8,5,8,4,8,7,5],0),4368839320910970011585631865221924149900),
    (([2,2,1,4,6,9,4,4,8,3,8,7,4,4,7,4,2,6,9,5,9,5,3,4],3),([1,8,2,8,4,2,8,7,4,8,1,7,1,7,5,1,4,7,1,7,4,7,2,8],3),4368839320911204803250985187771199675020),
    (([2,2,1,4,7,9,4,5,4,3,4,7,4,3,3,8,4,5,1,2,8,4,6,7],3),([1,8,2,8,4,5,2,1,2,4,4,7,2,2,7,7,2,7,4,7,4,7,2,8],3),4368895682916425843097825550328799675020),
    (([2,2,1,4,7,9,4,5,4,3,4,7,4,7,2,5,6,2,6,7,3,8,1,8],1),([1,8,2,8,4,5,2,1,2,4,4,7,4,8,4,7,1,2,4,2,8,1,4,7],1),4368895682916756255149110128637781230220),
    (([2,2,1,5,1,5,4,4,7,5,1,2,5,2,4,5,1,1,8,4,8,5,1,1],4),([1,8,2,8,4,8,6,5,1,2,1,8,3,1,1,4,2,7,2,4,2,1,7,1],3),4369048067889951196396843242734796001420),
    (([2,2,2,1,1,5,4,7,4,1,8,7,2,4,8,5,4,8,4,1,1,1,5,4],4),([1,8,2,9,2,9,6,7,4,1,1,7,3,8,4,4,2,7,4,2,4,6,9,5],2),4372293050791662777115751445841197751420),
    (([2,2,8,8,2,2,1,7,2,7,1,7,5,1,7,1,1,8,2,4,4,5,8,2],2),([1,8,6,3,3,3,4,7,4,2,6,7,1,5,6,2,7,2,9,3,9,3,3,7],3),4505905305633669557561246030507657864620),
    (([2,3,4,8,3,6,6,4,9,2,7,4,7,1,4,7,5,8,2,6,7,3,6,1],2),([1,8,7,8,1,2,8,7,8,4,7,5,8,1,7,1,1,2,4,2,5,5,2,7],2),4609507200071077391635151497284762557900)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_66 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 4610140314585477273316985559537193028300≤n ∧ n≤111064072645328925362650839201266671213420 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,3,4,8,5,3,8,2,7,2,2,1,7,7,3,1,1,1,2,1,8,4,8,8],2),([1,8,7,8,2,8,1,7,4,4,8,4,2,8,7,1,5,5,7,2,2,7,2,7],1),4610140314585477273316985559537193028300),
    (([2,3,6,1,1,4,4,4,1,2,8,9,6,1,7,5,9,8,2,1,1,4,4,6],1),([1,8,8,4,5,1,1,1,7,5,7,1,4,8,2,1,2,1,4,7,7,2,7,7],2),4649865978568140841545001163032941930500),
    (([2,3,6,1,1,4,4,4,4,4,4,2,1,8,9,5,1,1,7,7,6,7,9,1],3),([1,8,8,4,5,1,1,1,8,7,7,1,4,1,8,1,5,2,1,1,8,8,5,2],3),4649865980457277690909758307153952336900),
    (([2,3,6,1,1,4,4,7,6,2,3,4,2,3,8,6,7,6,1,7,3,5,5,7],1),([1,8,8,4,5,1,1,4,4,8,2,2,7,2,4,4,7,4,2,2,8,1,4,7],1),4649866035088713996601272865143628105220),
    (([2,3,6,1,1,4,5,8,6,4,1,1,4,4,7,2,1,7,8,3,6,3,9,9],1),([1,8,8,4,5,1,1,8,2,8,4,8,7,8,1,8,1,7,7,2,8,1,5,8],3),4649866231025745627209364617933780202500),
    (([2,3,6,1,4,8,3,3,5,1,4,2,2,5,3,5,1,4,6,3,3,1,2,1],3),([1,8,8,4,5,4,8,1,8,4,1,1,4,2,2,2,1,2,8,2,4,2,7,4],4),4650021695240919886596955731979604348420),
    (([2,3,6,4,5,3,4,1,3,4,7,8,7,4,2,4,9,4,7,4,6,9,2,3],3),([1,8,8,5,1,2,1,8,5,4,8,4,7,1,7,8,5,1,7,4,1,2,4,8],0),4655642151164417821121874403923330104900),
    (([7,9,4,1,3,9,9,1,4,4,5,7,8,1,2,7,3,4,7,6,8,8,7,2],2),([7,2,5,1,7,5,2,7,4,4,2,4,1,7,8,1,2,5,4,1,5,5,1,4],1),58764491192077293424463487484198459679900),
    (([7,9,4,4,6,2,7,5,4,4,3,4,2,6,6,8,1,7,9,6,9,2,1,8],1),([7,2,5,7,2,7,5,7,4,8,8,8,8,1,2,7,5,2,1,1,1,1,5,5],3),58806719711181689837154007954190468429900),
    (([7,9,5,2,6,1,3,7,4,7,8,1,8,4,6,3,6,4,6,2,8,6,3,2],2),([7,2,7,7,8,8,7,2,4,5,7,4,1,5,5,8,7,2,1,8,2,5,1,5],0),59038868268170101175228654303452261642400),
    (([9,3,4,7,7,2,5,8,4,8,2,3,7,1,8,4,3,1,1,3,1,1,6,9],2),([8,4,4,1,8,7,8,7,1,2,8,7,1,1,1,1,8,4,5,5,2,5,4,4],4),79730092388323130252234581997386384412900),
    (([9,3,4,7,7,2,5,8,4,8,2,3,7,1,8,4,3,1,2,4,2,6,9,6],2),([8,4,4,1,8,7,8,7,1,2,8,7,1,1,1,1,8,5,2,8,1,4,2,4],1),79730092388323130252478002310871649226980),
    (([1,2,1,7,5,7,8,1,1,5,2,8,5,4,1,4,8,4,4,5,7,2,5,2,4],1),([9,3,2,1,7,4,2,6,6,4,2,2,6,6,8,2,4,7,3,2,3,5,6,4],1),99411201172460531696281699624609468838920),
    (([1,4,2,2,2,7,4,5,5,2,4,5,2,7,5,8,2,2,5,5,5,2,2,8,4],4),([9,7,6,1,9,2,2,2,6,7,1,8,2,1,8,8,1,9,2,2,1,5,4,8],3),110125572024118092735080023355431824751420),
    (([1,4,4,1,7,5,5,1,7,8,2,7,7,4,8,2,8,7,4,7,2,8,2,7,5],3),([9,7,7,8,9,8,7,4,8,5,4,2,4,2,6,4,3,7,1,9,2,4,2,4],1),111064072645328925362650839201266671213420)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_67 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 192364911420946771439033038709172561675400≤n ∧ n≤6394932398360437582032453866244101233484920 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,1,1,5,7,2,2,1,4,4,1,8,7,2,4,1,7,8,2,7,8,8,8,2,2],2),([1,7,9,4,4,4,7,4,1,9,6,1,2,5,7,4,8,6,1,5,3,2,1,8,5],2),192364911420946771439033038709172561675400),
    (([2,1,1,5,7,2,2,1,4,4,7,8,8,2,7,8,8,7,1,2,7,2,8,1,2],3),([1,7,9,4,4,4,7,4,1,9,6,1,8,7,3,4,9,7,8,2,1,4,3,9,9],0),192364911421264976754634381511228223896200),
    (([2,1,2,7,1,5,7,4,4,1,4,8,8,5,8,4,1,4,8,7,8,8,8,8,1],4),([1,7,9,4,8,1,6,1,6,8,8,8,6,6,8,1,3,5,3,2,8,2,7,3,2],2),192520882771161228261441967745510805767920),
    (([2,7,8,8,8,5,1,7,2,7,5,4,1,5,2,2,7,2,8,1,1,1,2,2,7],1),([2,5,6,6,6,2,1,3,7,4,6,7,7,6,1,4,8,3,3,1,2,8,8,9,4],3),303387544367150941942282002758603686259920),
    (([4,1,4,8,1,7,1,4,7,8,8,1,8,8,7,8,5,2,4,2,5,1,8,5,1],4),([3,7,6,9,5,7,8,3,4,1,2,2,1,7,1,2,2,3,4,6,4,3,3,6,3],3),669380040774430666808412994847663895361420),
    (([4,1,4,8,1,7,1,5,4,7,5,2,5,8,8,4,7,2,1,4,2,1,2,1,8],3),([3,7,6,9,5,7,8,3,4,2,1,2,2,1,2,7,8,2,9,7,2,8,3,2,8],4),669380041359666147112550450600875996609420),
    (([1,1,7,5,5,8,8,1,5,1,1,1,8,1,7,2,7,4,7,4,4,2,8,4,5,4],4),([9,2,1,3,3,5,2,6,1,6,7,4,4,6,1,7,3,2,3,4,1,4,1,6,7],2),4424416556513650314609501924818457739501420),
    (([1,5,5,8,8,4,2,1,1,2,1,4,5,8,1,1,2,7,1,1,2,5,8,4,7,2],3),([1,1,1,7,6,9,8,3,8,4,2,4,2,1,5,2,7,6,3,4,1,2,4,1,7,7],1),5471739925776516646008152021336958869828920),
    (([1,5,6,1,7,1,4,1,6,3,8,2,3,7,2,6,7,7,1,3,1,4,7,7,2,9],3),([1,1,4,1,7,5,2,2,5,1,2,8,2,5,2,1,7,8,2,7,7,8,1,2,2,4],1),5486285420633512898552550901136092486598900),
    (([1,5,6,1,7,1,4,1,7,8,4,8,1,8,1,7,8,8,6,3,2,4,1,1,6,6],2),([1,1,4,1,7,5,2,2,7,4,1,1,1,4,2,4,5,4,2,4,8,1,7,8,7,4],2),5486285422758223636718533068797646781056500),
    (([1,5,6,1,7,1,4,4,8,7,8,4,1,9,4,4,6,9,6,2,2,4,4,7,9,6],1),([1,1,4,1,7,5,2,7,4,2,4,4,8,5,2,7,4,5,4,7,2,2,2,2,5,2],3),5486285502823241580222887305006126456874900),
    (([1,5,6,2,7,8,8,3,4,3,2,2,8,1,8,7,1,1,9,4,6,9,7,2,4,6],3),([1,1,4,5,4,1,7,2,2,5,1,8,5,8,8,4,7,7,5,5,2,8,8,2,4,5],0),5488673133555782379555562074137426021954900),
    (([1,7,2,5,4,1,7,8,1,4,7,7,8,5,7,1,7,2,5,8,4,4,1,5,2,7],1),([1,4,6,9,4,7,4,8,2,1,2,7,7,7,3,2,6,4,3,8,9,4,6,2,9,5],2),6394932398360396366598638325720624815948920),
    (([1,7,2,5,4,1,7,8,1,4,7,7,8,5,7,2,2,8,1,8,4,5,4,4,4,8],3),([1,4,6,9,4,7,4,8,2,1,2,7,7,7,3,2,8,1,6,7,3,5,3,7,7,2],1),6394932398360396734518256405785165194060920),
    (([1,7,2,5,4,1,7,8,1,4,7,7,8,5,8,7,5,2,4,1,1,8,4,2,4,2],2),([1,4,6,9,4,7,4,8,2,1,2,7,7,7,4,5,8,1,3,8,9,3,8,7,8,1],2),6394932398360437582032453866244101233484920)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_68 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 6394971286474709964687062998992411160223320≤n ∧ n≤38074586561555068069051146962996340214410400 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,7,2,5,4,4,4,2,8,8,4,7,4,7,1,4,2,5,2,7,4,4,1,4,7,4],1),([1,4,6,9,4,7,6,7,8,8,3,7,5,6,6,2,8,6,2,4,8,1,7,1,6,7],1),6394971286474709964687062998992411160223320),
    (([2,1,4,8,4,7,7,8,7,1,1,2,8,7,1,2,4,5,2,1,1,2,8,8,2,2],2),([1,7,9,6,4,8,1,6,4,7,1,5,7,1,2,8,9,3,1,7,6,4,2,9,3,2],0),8691685907938353231804273192323433992737900),
    (([2,4,4,7,7,7,1,1,2,1,5,2,7,7,5,1,4,5,8,1,2,4,4,2,8,8],3),([1,9,4,6,9,7,1,7,2,7,7,1,2,6,5,8,4,1,1,3,8,4,7,3,8,4],1),9934985089734073975443003933417039293149420),
    (([4,7,1,1,7,9,6,7,4,4,8,5,2,1,6,1,1,1,8,6,1,1,2,2,1,8],3),([4,2,1,1,7,7,1,2,2,5,2,4,7,2,7,2,8,2,5,7,1,2,4,8,4,1],4),38038558657912384590231433940833908061973600),
    (([4,7,1,1,7,9,7,6,7,4,8,1,2,4,6,1,7,5,8,1,5,7,5,2,8,7],1),([4,2,1,1,7,7,7,1,8,5,8,1,8,7,1,1,8,4,2,8,4,7,1,4,7,7],2),38038563980945618287578393617248153263219920),
    (([4,7,1,1,7,9,7,6,7,4,8,1,2,4,6,1,7,5,8,3,4,8,8,2,4,7],3),([4,2,1,1,7,7,7,1,8,5,8,1,8,7,1,1,8,4,5,4,1,2,7,7,7,4],4),38038563980945618287701288085480528975701200),
    (([4,7,1,1,7,9,7,6,7,4,8,2,4,8,1,6,2,5,6,4,1,3,9,6,9,4],3),([4,2,1,1,7,7,7,1,8,5,8,7,1,7,8,1,8,5,8,2,4,8,8,4,5,2],3),38038563981008093414667604806174526034056400),
    (([4,7,1,1,7,9,7,7,3,3,2,2,2,4,5,7,1,7,1,1,8,3,8,1,7,7],2),([4,2,1,1,7,7,7,5,8,5,7,1,5,1,2,1,4,5,4,1,1,5,2,1,5,7],4),38038564479019492285472939927118014907142400),
    (([4,7,1,1,7,9,7,7,7,5,8,2,1,2,3,6,7,7,1,2,2,6,8,3,2,8],1),([4,2,1,1,7,7,7,7,7,4,7,7,1,2,5,7,1,7,2,5,2,2,2,7,7,5],3),38038564915368227295751809192337649529478400),
    (([4,7,1,1,7,9,7,7,8,4,7,1,5,4,6,2,7,8,1,4,2,4,4,1,4,3],1),([4,2,1,1,7,7,7,8,1,4,1,1,1,2,7,4,4,4,5,8,8,1,4,8,8,4],1),38038565055184359556068870352675920215650640),
    (([4,7,1,1,7,9,7,7,8,7,9,4,1,8,7,4,8,5,9,6,1,8,7,7,8,1],1),([4,2,1,1,7,7,7,8,5,4,4,2,7,7,7,5,7,4,8,2,5,8,1,5,1,1],1),38038565129162736784238654080375964960872400),
    (([4,7,1,2,5,8,1,1,5,7,1,2,2,1,8,4,1,2,4,8,8,8,2,4,1,7],1),([4,2,1,3,3,6,7,7,1,6,1,9,4,1,1,1,8,6,8,4,4,5,6,1,7,4],2),38039846130120955725689988552926952565946320),
    (([4,7,1,4,7,3,3,3,1,5,4,1,1,1,9,8,6,2,4,6,2,4,6,1,6,8],1),([4,2,1,7,1,1,4,4,5,5,7,1,1,8,5,2,2,7,2,5,7,1,8,5,2,2],3),38048166750516103838010745184679507421942400),
    (([4,7,1,8,1,2,4,4,1,4,2,2,7,7,7,8,8,1,1,4,5,2,1,8,2,2],2),([4,2,2,6,4,8,1,1,2,3,2,5,1,7,4,7,4,7,3,4,1,7,9,2,1,7],0),38074586561555068068429977439059475712650400),
    (([4,7,1,8,1,2,4,4,1,4,2,2,7,7,7,8,8,1,8,8,4,1,2,4,5,1],1),([4,2,2,6,4,8,1,1,2,3,2,5,1,7,4,7,4,8,7,1,8,9,6,7,1,2],0),38074586561555068069051146962996340214410400)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_69 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 38074586561764736145418072596653454557813920≤n ∧ n≤47548991502382008814994411224813763690339900 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([4,7,1,8,1,2,4,4,1,5,5,5,7,8,5,4,2,2,2,8,5,5,4,2,7,2],2),([4,2,2,6,4,8,1,1,2,4,7,3,6,6,7,2,1,8,1,6,9,7,5,1,8,2],3),38074586561764736145418072596653454557813920),
    (([4,7,1,8,1,2,4,4,1,8,8,8,7,2,2,5,4,7,4,7,5,8,8,2,1,1],1),([4,2,2,6,4,8,1,1,2,8,4,3,4,6,5,1,7,4,6,2,2,7,4,6,7,3],2),38074586562685358249723398727265842943298720),
    (([4,7,1,8,1,2,4,4,1,8,8,8,7,2,7,5,5,2,2,2,5,1,4,4,1,8],2),([4,2,2,6,4,8,1,1,2,8,4,3,4,7,7,5,7,3,3,4,4,2,3,4,4,2],4),38074586562685391704054304665136105523317920),
    (([4,7,1,8,1,2,4,4,2,4,7,2,4,5,2,1,8,5,2,2,1,8,2,4,1,7],1),([4,2,2,6,4,8,1,1,3,4,1,9,8,4,1,8,6,4,1,1,1,4,7,5,6,2],1),38074586563771197932707119853350165247196320),
    (([4,7,1,8,1,2,4,4,2,4,7,2,4,5,4,1,8,2,1,5,2,8,1,7,4,8],3),([4,2,2,6,4,8,1,1,3,4,1,9,8,4,4,4,8,4,7,4,6,5,6,8,9,1],4),38074586563771200405890179669174561587625120),
    (([4,7,1,8,1,2,4,5,8,8,1,8,1,7,1,2,4,7,7,4,7,2,2,4,8,2],2),([4,2,2,6,4,8,1,3,4,8,8,5,1,7,7,6,9,1,2,6,9,4,6,1,9,1],2),38074586718627978651583019171623085488819360),
    (([4,7,1,8,1,2,4,5,8,8,1,8,1,7,1,4,1,8,5,2,1,1,1,1,5,4],4),([4,2,2,6,4,8,1,3,4,8,8,5,1,7,7,6,9,4,7,1,3,6,4,9,9,4],4),38074586718627978754270984468829212061813920),
    (([4,7,1,8,1,2,4,5,8,8,1,8,2,7,7,2,2,7,1,1,4,2,1,8,2,2],2),([4,2,2,6,4,8,1,3,4,8,8,5,2,2,3,5,2,2,1,8,9,1,4,2,5,8],1),38074586718628437830692657710098833792650400),
    (([4,7,1,8,2,1,7,1,1,4,8,4,5,8,8,1,5,5,5,8,1,8,4,1,2,8],3),([4,2,2,6,5,3,2,1,2,6,4,6,2,4,4,1,8,4,6,8,2,4,4,6,4,8],4),38074818451076060586160649069088951352853920),
    (([4,7,4,7,1,1,2,4,1,7,5,8,7,7,2,7,8,1,8,8,8,1,4,2,8,4],1),([4,2,7,4,3,8,3,1,7,5,8,2,1,4,6,7,2,3,2,1,7,6,8,7,4,6],4),38503208758492738041614356172138783083738240),
    (([4,7,4,7,1,1,2,4,4,7,4,1,2,7,8,8,1,1,7,2,5,8,8,7,4,5],3),([4,2,7,4,3,8,3,1,7,8,1,1,8,9,7,5,1,2,2,7,6,2,8,4,9,9],4),38503208770361090804784394789751103052923520),
    (([4,7,4,7,1,1,2,4,4,7,4,1,2,7,8,8,1,1,7,2,8,4,1,8,5,7],4),([4,2,7,4,3,8,3,1,7,8,1,1,8,9,7,5,1,2,2,7,6,6,1,6,3,3],4),38503208770361090804784893501590608121774720),
    (([4,7,4,7,1,1,2,4,4,8,7,4,5,2,2,1,4,4,2,5,5,8,2,4,1,8],2),([4,2,7,4,3,8,3,1,7,8,5,1,3,1,8,3,6,4,7,2,6,8,9,1,9,2],3),38503208771778408938380395142994202190817920),
    (([5,1,9,2,2,8,2,7,4,2,7,4,7,3,8,1,7,4,1,1,1,1,4,5,5,2],1),([4,7,1,2,2,7,1,8,4,7,1,2,8,1,1,1,7,2,8,2,4,7,5,7,8,7],4),47548991502381948012731268681412647521615420),
    (([5,1,9,2,2,8,2,7,4,2,7,4,7,4,3,1,3,6,6,7,6,3,8,1,1,6],3),([4,7,1,2,2,7,1,8,4,7,1,2,8,5,7,5,7,7,4,8,4,7,5,5,7,4],2),47548991502382008814994411224813763690339900)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_70 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 47769098396251955015034087122979404843266420≤n ∧ n≤5732030373062214813840468844662671610286079900 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([5,2,4,1,5,8,5,7,8,7,2,1,1,2,7,2,7,7,1,5,2,2,4,4,1,4],1),([4,7,3,1,1,4,5,8,9,1,8,4,2,7,3,3,7,2,7,1,9,4,7,7,8,4],2),47769098396251955015034087122979404843266420),
    (([5,2,4,1,7,1,5,7,1,1,4,5,1,4,8,4,4,5,5,1,1,1,1,2,1,5],2),([4,7,3,1,3,2,4,3,1,2,3,1,6,6,7,2,9,8,1,4,4,5,4,7,9,7],3),47769418836892291667375741901071993069626420),
    (([5,2,4,7,8,7,5,4,7,4,8,4,2,8,5,8,1,2,1,7,8,2,2,5,7,2],3),([4,7,3,4,9,8,8,3,7,2,8,6,6,4,8,5,2,7,2,4,8,4,6,1,6,7],3),47817344668816919202557226019371467325406420),
    (([6,5,7,4,2,2,8,7,8,7,7,2,3,6,9,6,1,8,7,7,1,6,8,9,1,7],1),([5,8,1,7,8,2,1,7,7,1,8,4,1,5,4,1,4,1,4,7,1,7,4,7,7,4],4),75658062621912177374049663662600494459138700),
    (([8,2,9,4,2,3,1,2,7,5,2,1,8,8,1,3,3,4,8,7,3,2,8,6,8,2],2),([7,5,2,1,4,2,7,2,5,7,1,5,1,8,7,1,8,1,8,2,5,1,8,5,2,4],2),126207512291329399292338907036513733651667400),
    (([8,6,4,4,8,7,3,1,1,4,8,6,2,5,2,7,8,7,2,7,8,7,2,2,9,3],1),([7,7,4,7,2,4,2,5,2,4,8,1,5,2,1,2,1,8,8,4,8,1,7,5,1,7],1),136287252110970668385703955048044836169195400),
    (([1,2,1,8,4,1,4,1,5,2,7,8,8,4,2,8,7,1,5,1,2,2,1,1,1,5,4],4),([9,3,2,4,8,4,3,1,2,1,6,4,3,3,7,5,8,4,2,3,8,1,1,9,4,4],2),201333356316596400206462209792054715130563920),
    (([1,2,1,8,4,1,4,1,5,7,2,2,5,7,5,2,8,1,2,4,1,4,7,7,4,1,7],4),([9,3,2,4,8,4,3,1,2,7,3,1,2,7,4,4,1,5,3,3,4,8,9,4,2,7],2),201333356322786379690340656754362662747203920),
    (([1,2,1,8,4,2,1,2,2,8,5,7,8,8,8,8,5,4,8,5,8,1,5,8,1,5,4],1),([9,3,2,4,8,4,6,4,6,7,1,8,4,2,8,1,4,7,2,4,5,6,1,9,2,9],3),201333414238925974706683043098941608852963920),
    (([1,5,7,5,4,4,1,1,8,7,4,4,7,4,1,5,2,2,7,2,8,1,1,1,2,2,7],1),([1,1,9,2,8,5,7,9,2,7,3,8,7,6,1,1,1,4,8,3,3,1,2,8,8,9,4],3),250499171944134701121643808127410703295634920),
    (([1,7,8,5,8,2,1,2,1,1,2,7,1,1,2,7,1,7,7,7,7,8,7,7,7,7,8],3),([1,5,5,7,1,1,8,6,3,3,7,9,7,2,1,3,2,2,4,4,6,8,1,7,1,6,2],2),306981878263825283485444519677489435641371600),
    (([2,4,2,1,2,4,8,4,2,7,7,7,2,1,1,1,5,4,8,7,2,4,5,1,4,4,7],4),([1,9,2,9,5,1,7,2,4,4,1,9,2,4,8,8,7,8,1,8,4,4,4,8,4,4,9],2),441596562026886605123863295817687425459519920),
    (([2,5,7,1,2,1,8,5,4,7,4,8,2,8,2,4,2,1,4,1,7,5,7,7,2,4,2],2),([2,1,8,9,1,6,2,2,4,4,2,5,7,2,7,7,8,3,3,7,4,2,9,1,8,6,2],2),495038931863642340744785904057733603957859920),
    (([8,3,6,7,3,8,4,2,8,8,2,1,9,2,4,1,8,1,8,5,2,7,4,3,4,2,1],2),([7,5,5,8,8,2,8,1,2,8,1,2,8,4,7,8,5,1,4,8,2,4,5,5,7,1,4],1),5732030373062214808098388614864947240570879900),
    (([8,3,6,7,3,8,4,2,8,8,2,1,9,2,4,1,8,7,9,7,1,2,3,5,3,8,3],2),([7,5,5,8,8,2,8,1,2,8,1,2,8,4,7,8,5,4,2,2,7,5,5,4,4,4,5],3),5732030373062214813840468844662671610286079900)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_71 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 5732033806868782782280554288793697392202879900≤n ∧ n≤928111115730694600830179074029547745330193578920 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([8,3,6,7,3,8,5,7,1,6,7,6,8,4,4,1,2,4,8,2,2,2,3,3,4,9,4],1),([7,5,5,8,8,2,8,8,5,2,1,7,8,8,5,2,8,8,4,7,1,4,4,2,5,2,1],2),5732033806868782782280554288793697392202879900),
    (([1,1,5,7,2,7,4,2,2,5,5,1,8,5,2,7,8,4,2,2,4,2,1,4,2,8,2,1],4),([9,1,3,4,4,7,4,5,1,2,4,8,7,1,8,7,2,4,4,4,9,9,4,7,9,7,6],2),8914838048294125762280311181331719082159713920),
    (([1,1,7,8,8,1,8,5,2,4,1,4,4,4,7,7,1,4,2,5,2,7,4,4,1,4,7,4],1),([9,2,4,4,8,1,5,4,2,7,3,3,6,9,7,8,7,8,6,2,4,8,1,7,1,6,7],1),8973741362346427563394917370673139261746160820),
    (([1,1,7,8,8,1,8,7,7,2,2,2,1,8,7,1,7,5,4,1,2,8,1,1,7,4,4,5],2),([9,2,4,4,8,1,8,2,6,1,2,7,9,7,6,6,7,7,6,4,5,3,2,9,4,3,6],4),8973742538437748696539510502146012707237053620),
    (([1,1,7,8,8,2,4,4,5,7,4,4,8,4,1,1,7,2,4,2,2,2,8,8,4,2,1,7],1),([9,2,4,4,8,3,7,7,8,4,1,4,4,5,9,7,8,1,7,2,2,7,7,1,2,1,5],3),8973754667346100674031615900255124048730392500),
    (([1,4,4,4,7,5,8,7,1,4,4,5,1,1,2,8,8,8,1,2,5,1,5,4,2,4,2,7],1),([9,7,8,1,6,3,7,5,1,1,4,2,8,4,8,1,6,3,8,7,9,7,2,2,3,8,2],3),10132198239966124985686079654483679048007178920),
    (([1,4,4,4,8,7,2,1,7,1,8,8,4,7,4,8,8,2,7,5,2,2,7,7,8,1,8,1],1),([9,7,8,2,3,8,6,8,1,4,2,7,3,8,2,4,4,4,4,2,3,4,5,6,8,7,9],4),10133369055135633748302249007604870757411811240),
    (([1,5,7,1,2,1,4,9,3,6,7,4,6,2,3,1,8,7,4,1,3,8,2,3,2,1,7,2],3),([1,1,8,5,2,5,8,7,2,2,5,8,2,2,1,5,5,2,1,7,7,7,2,7,8,5,5,7],1),11236840208263387072366311805779808099151017400),
    (([1,4,2,1,2,7,1,5,8,7,2,4,1,8,1,1,8,8,1,4,4,4,2,2,5,5,5,5,5],2),([9,7,6,1,1,6,6,2,9,3,7,1,2,1,5,1,1,4,3,2,3,4,8,8,1,8,7,9],4),451547899094356768259182752864396152774971501420),
    (([1,5,7,8,1,4,8,4,2,4,5,5,1,2,5,8,8,5,8,2,8,8,1,8,1,8,1,2,2],2),([1,2,2,2,9,4,9,8,3,2,8,4,2,2,5,4,7,8,8,6,8,8,1,2,2,7,2,6,9],3),509852955881486051525554897253323471413940463920),
    (([1,5,7,8,5,2,1,7,7,4,1,5,1,1,4,8,4,1,7,2,8,4,8,5,4,8,1,8,2],2),([1,2,2,6,1,5,6,4,7,1,7,7,4,8,2,9,9,6,8,2,2,1,4,8,8,9,9,6,4],3),510117154996667087232291016088909071282762043920),
    (([2,1,2,1,4,7,5,2,8,1,2,2,2,8,8,7,4,8,7,4,8,4,7,8,1,4,5,4,5],3),([1,7,9,4,6,4,8,2,8,1,9,8,4,9,1,5,2,7,6,7,1,2,1,6,8,4,1,8,2],3),789098818090737150740930642307918824471473937920),
    (([2,1,2,1,4,7,5,2,8,7,4,8,4,7,5,5,1,4,2,5,1,7,2,8,4,8,1,8,2],2),([1,7,9,4,6,4,8,2,8,2,3,2,6,3,7,8,7,1,1,4,3,5,8,6,8,2,4,3,9],1),789098818193778000594675806084951326341355793920),
    (([2,4,7,5,7,8,1,1,7,1,1,7,1,2,1,4,4,1,7,4,5,2,2,2,1,5,7,8,1],4),([1,9,6,7,7,8,3,7,2,1,5,1,4,2,4,7,1,9,4,1,4,7,2,6,3,4,3,4,1],3),928111115730694600830179067653776034031387818920),
    (([2,4,7,5,7,8,1,1,7,1,1,7,1,2,1,4,4,1,7,4,5,2,4,4,5,5,4,1,2],2),([1,9,6,7,7,8,3,7,2,1,5,1,4,2,4,7,1,9,4,1,4,7,2,6,4,8,4,1,2],4),928111115730694600830179074029547745330193578920)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_72 :
    ∃ T : Finset ℕ, T.card=15 ∧ ∀ n ∈ T, 936114336452222406576130643855385001894430978920≤n ∧ n≤3291647361285303545845199407028781295161141696421100 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([2,4,8,2,2,5,1,7,5,1,1,2,1,1,2,8,7,1,4,8,8,4,5,5,4,4,1,2,8],3),([1,9,7,4,4,3,9,1,1,1,4,8,8,8,5,9,2,1,1,8,1,1,8,8,4,6,8,8,3],1),936114336452222406576130643855385001894430978920),
    (([4,4,8,4,1,4,8,2,5,4,7,4,5,8,2,1,1,8,1,2,5,8,8,4,1,8,4,5,1],4),([3,8,8,3,4,6,1,6,1,2,8,6,8,2,9,8,6,8,8,1,1,7,3,1,5,3,4,7,3],4),3035852422326918772532298329606501418678369151420),
    (([4,4,8,8,1,5,4,4,5,7,7,2,8,5,8,2,4,2,1,4,4,2,7,1,2,2,4,8,1],1),([3,8,8,6,2,6,6,6,8,9,4,5,2,1,8,8,3,1,6,2,2,2,7,2,4,7,8,3,3],2),3047916125098998188050767349900714955429355775420),
    (([4,5,4,5,1,1,1,8,7,2,4,2,1,1,5,4,2,5,8,7,2,4,7,4,4,5,4,2,1],1),([3,8,9,8,3,2,1,6,1,2,1,8,7,8,1,1,7,6,4,3,1,7,5,9,6,4,1,9,4],1),3111461810462061032818995388669036225327081651420),
    (([1,1,7,7,1,4,8,8,5,2,5,1,1,8,7,7,4,7,4,1,5,2,2,4,4,5,5,2,1,5],3),([9,2,3,1,7,2,7,8,6,2,7,2,8,2,2,4,7,4,4,1,4,7,6,9,2,6,5,6,7],4),18155695105351580144205990158858295465048878063920),
    (([1,1,8,1,5,2,2,7,5,8,2,8,7,2,2,7,4,4,1,1,7,5,2,1,1,1,1,2,2,7],1),([9,2,5,3,8,7,2,1,8,2,1,3,7,9,7,4,2,8,2,1,6,1,3,9,1,1,4,4,4],3),18188349105361582948265334962532147255636576884920),
    (([1,2,1,4,1,5,2,7,4,4,7,5,5,1,8,1,4,7,5,7,2,4,7,7,1,7,1,5,2,1],1),([9,3,1,1,8,7,5,7,6,1,7,1,2,2,1,8,4,2,2,2,6,7,4,3,6,7,6,1,6],3),18337625839321090804986160167948812992648941601420),
    (([1,1,5,8,1,8,8,4,7,1,1,2,8,7,8,1,7,5,5,8,1,8,5,4,2,4,4,2,8,2,5],3),([9,1,4,3,9,1,2,7,8,8,8,1,4,4,4,4,6,4,4,4,4,2,1,3,4,6,8,4,2,5],2),812660265150897455723314269813808284151264877926420),
    (([1,5,8,1,6,7,8,9,1,4,1,2,1,4,8,8,1,1,2,7,4,3,7,1,4,3,6,1,1,9,6],3),([1,2,4,4,2,4,7,2,7,8,2,5,1,1,7,8,4,2,5,5,5,2,2,2,7,2,2,8,1,5,7],1),1037740211307148686500715368203700794073841664754900),
    (([1,5,8,1,7,2,2,8,4,8,1,1,4,8,4,5,2,7,2,2,7,2,7,2,2,2,8,1,2,2,4],4),([1,2,4,4,3,6,2,1,1,8,1,8,1,1,6,6,8,4,4,9,2,7,7,4,9,2,1,4,8,5,8],2),1037760683446397279059251613521851433742242395986420),
    (([1,5,8,1,7,2,8,2,4,1,2,5,2,2,7,1,2,5,8,7,4,2,2,1,1,5,7,8,5,5,1],1),([1,2,4,4,3,6,7,2,1,2,1,1,8,6,8,3,6,3,6,7,7,2,1,5,8,3,7,7,2,9,7],1),1037762063346397277754330159449052694101711209626420),
    (([1,5,8,1,7,2,8,2,4,5,7,5,4,4,2,1,5,8,4,2,7,7,1,2,1,7,2,8,7,1,7],1),([1,2,4,4,3,6,7,2,2,1,4,8,8,2,7,3,3,2,7,4,4,6,1,6,6,3,1,5,9,8,3],2),1037762063813381388385990178762695733400288986266420),
    (([1,5,8,1,7,2,8,2,4,5,7,5,4,4,2,2,2,7,7,1,4,2,1,4,1,5,4,8,1,8,2],2),([1,2,4,4,3,6,7,2,2,1,4,8,8,2,7,3,9,2,7,4,1,1,3,5,3,2,3,9,7,9,8],3),1037762063813381408520751943514057425167660926106420),
    (([1,5,8,1,8,3,1,4,3,2,4,8,1,6,2,7,4,2,9,1,1,7,7,2,8,9,2,2,3,2,4],3),([1,2,4,4,5,5,7,2,1,8,1,1,2,2,4,4,5,2,7,1,8,8,4,7,5,1,1,7,4,4,2],3),1037817398279772139458456135334151194664405494334900),
    (([3,2,7,9,4,1,9,8,8,4,2,2,8,8,1,1,4,8,3,2,4,3,1,6,7,1,6,1,5,3,4],1),([2,8,4,8,4,2,7,4,8,1,8,1,2,4,2,2,4,2,7,8,7,1,4,4,4,1,1,5,1,7,5],3),3291647361285303545845199407028781295161141696421100)] (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 6500 in
private theorem witness_block_73 :
    ∃ T : Finset ℕ, T.card=4 ∧ ∀ n ∈ T, 46077807376837966347292241491449091013203034673854900≤n ∧ n≤74122730443541037135201517117483282080933412280249900 ∧ n∈a352346Set :=
  certified_chunk _ _ _ [
    (([1,5,7,1,1,4,4,8,3,1,1,6,6,1,4,9,4,9,4,8,1,4,1,1,4,1,4,8,6,7,2,6],3),([1,1,8,5,2,1,1,2,2,2,4,8,2,5,7,1,1,4,1,5,2,2,4,2,7,4,1,7,1,2,4,8],0),46077807376837966347292241491449091013203034673854900),
    (([2,1,9,3,8,4,4,6,7,5,2,4,7,2,4,1,7,1,1,1,4,2,2,4,7,9,3,7,4,8,7,3],2),([1,8,1,8,1,1,7,1,4,1,2,5,7,4,1,1,7,8,1,4,8,5,5,5,1,8,7,4,8,1,5,7],1),73169326680524606699042163683432511915325233617879900),
    (([2,2,2,7,2,1,8,7,8,2,4,2,5,4,4,1,2,4,4,7,1,4,7,1,2,2,1,4,8,1,2,8],2),([1,8,3,1,1,6,8,3,4,1,1,7,7,2,7,4,1,4,6,4,1,6,6,6,4,4,8,4,1,7,4,8],0),73586647244353830311750992318116081363538221816075100),
    (([2,2,4,9,7,2,6,8,7,2,1,2,8,4,5,7,4,1,7,1,6,3,2,9,6,6,3,2,8,1,3,1],3),([1,8,4,1,8,2,5,1,8,2,4,5,4,4,7,7,5,1,2,1,2,1,7,4,7,2,5,2,2,4,1,7],4),74122730443541037135201517117483282080933412280249900)] (by decide +kernel) (by decide +kernel)

private theorem witness_union_74 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 26≤n ∧ n≤5355218900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 26≤2353700) (by decide : 2353700<2859460) (by decide : 2859460≤5355218900) witness_block_0 witness_block_1

private theorem witness_union_75 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 5857281500≤n ∧ n≤679148834708 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 5857281500≤178139569120) (by decide : 178139569120<218246846740) (by decide : 218246846740≤679148834708) witness_block_2 witness_block_3

private theorem witness_union_76 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 680623768820≤n ∧ n≤103123720322120 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 680623768820≤15386784636260) (by decide : 15386784636260<15391267980500) (by decide : 15391267980500≤103123720322120) witness_block_4 witness_block_5

private theorem witness_union_77 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 291803401145900≤n ∧ n≤870861088154920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 291803401145900≤583352898652420) (by decide : 583352898652420<680249254174360) (by decide : 680249254174360≤870861088154920) witness_block_6 witness_block_7

private theorem witness_union_78 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 873119486799520≤n ∧ n≤25261174064199400 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 873119486799520≤9761839477216900) (by decide : 9761839477216900<15820954945120780) (by decide : 15820954945120780≤25261174064199400) witness_block_8 witness_block_9

private theorem witness_union_79 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 34791914841397900≤n ∧ n≤188328362662472420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 34791914841397900≤167860058387304400) (by decide : 167860058387304400<168166993748382380) (by decide : 168166993748382380≤188328362662472420) witness_block_10 witness_block_11

private theorem witness_union_80 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 267378351711111020≤n ∧ n≤9430094779280318920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 267378351711111020≤1392268994749948120) (by decide : 1392268994749948120<1561916239281804400) (by decide : 1561916239281804400≤9430094779280318920) witness_block_12 witness_block_13

private theorem witness_union_81 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 11465741592220802600≤n ∧ n≤1004242667091207510400 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 11465741592220802600≤48609514251668541220) (by decide : 48609514251668541220<422823610080475977400) (by decide : 422823610080475977400≤1004242667091207510400) witness_block_14 witness_block_15

private theorem witness_union_82 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 1004285512141896342400≤n ∧ n≤1803189061310759379920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 1004285512141896342400≤1425404260852318933360) (by decide : 1425404260852318933360<1443990780236644198720) (by decide : 1443990780236644198720≤1803189061310759379920) witness_block_16 witness_block_17

private theorem witness_union_83 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 1803189061471071699920≤n ∧ n≤5442298099765917586400 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 1803189061471071699920≤2790892894895340899920) (by decide : 2790892894895340899920<3310802144871854904232) (by decide : 3310802144871854904232≤5442298099765917586400) witness_block_18 witness_block_19

private theorem witness_union_84 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 5450816127434573896400≤n ∧ n≤89684183026257464282420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 5450816127434573896400≤23858571042442047808640) (by decide : 23858571042442047808640<23899366172071640007200) (by decide : 23899366172071640007200≤89684183026257464282420) witness_block_20 witness_block_21

private theorem witness_union_85 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 89839475103861900122420≤n ∧ n≤694007840958969225601420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 89839475103861900122420≤102956865626997549097400) (by decide : 102956865626997549097400<103585824784581738757720) (by decide : 103585824784581738757720≤694007840958969225601420) witness_block_22 witness_block_23

private theorem witness_union_86 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 694372017747257670376420≤n ∧ n≤4660579416840962166946060 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 694372017747257670376420≤3671378131841190117334420) (by decide : 3671378131841190117334420<3671647453253257065622420) (by decide : 3671647453253257065622420≤4660579416840962166946060) witness_block_24 witness_block_25

private theorem witness_union_87 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 4738572704017740997009420≤n ∧ n≤11421999332884656468347420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 4738572704017740997009420≤7991945823850570543459592) (by decide : 7991945823850570543459592<8012458864227228885403400) (by decide : 8012458864227228885403400≤11421999332884656468347420) witness_block_26 witness_block_27

private theorem witness_union_88 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 11421999416605100708507420≤n ∧ n≤95069690026491749610604300 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 11421999416605100708507420≤22873394741664329186626420) (by decide : 22873394741664329186626420<38882469366568481080076120) (by decide : 38882469366568481080076120≤95069690026491749610604300) witness_block_28 witness_block_29

private theorem witness_union_89 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 95069737810477603796977420≤n ∧ n≤235015281689705642087657120 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 95069737810477603796977420≤160688744386773279007433920) (by decide : 160688744386773279007433920<162963965890217806500722420) (by decide : 162963965890217806500722420≤235015281689705642087657120) witness_block_30 witness_block_31

private theorem witness_union_90 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 258393046425542627043008900≤n ∧ n≤262283037815955805044175420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 258393046425542627043008900≤260301334534562509460853820) (by decide : 260301334534562509460853820<260301699573924018858538300) (by decide : 260301699573924018858538300≤262283037815955805044175420) witness_block_32 witness_block_33

private theorem witness_union_91 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 262283184570771334007997820≤n ∧ n≤271448349912440588834654420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 262283184570771334007997820≤263552922723294168823027100) (by decide : 263552922723294168823027100<263552922723295119678297500) (by decide : 263552922723295119678297500≤271448349912440588834654420) witness_block_34 witness_block_35

private theorem witness_union_92 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 271492828723236751499685620≤n ∧ n≤5150225055016383331305085580 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 271492828723236751499685620≤1845646719089385394210395800) (by decide : 1845646719089385394210395800<1845646737917748560183797400) (by decide : 1845646737917748560183797400≤5150225055016383331305085580) witness_block_36 witness_block_37

private theorem witness_union_93 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 5817962877026907029004383920≤n ∧ n≤14629594782227873302878089920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 5817962877026907029004383920≤8817748522085445182312799620) (by decide : 8817748522085445182312799620<9595658687132951572617722500) (by decide : 9595658687132951572617722500≤14629594782227873302878089920) witness_block_38 witness_block_39

private theorem witness_union_94 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 14630168592548308597026911920≤n ∧ n≤263407936968584941626538448920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 14630168592548308597026911920≤78283000818857204036798373200) (by decide : 78283000818857204036798373200<78283327705120500599821523920) (by decide : 78283327705120500599821523920≤263407936968584941626538448920) witness_block_40 witness_block_41

private theorem witness_union_95 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 263408986221192563916851312920≤n ∧ n≤386007665827750896226612154420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 263408986221192563916851312920≤326450553314415882198909374900) (by decide : 326450553314415882198909374900<331096034284798511613006001420) (by decide : 331096034284798511613006001420≤386007665827750896226612154420) witness_block_42 witness_block_43

private theorem witness_union_96 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 386027297532230304785331322420≤n ∧ n≤2297409704216174560631015003920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 386027297532230304785331322420≤2262267302182310396138897381200) (by decide : 2262267302182310396138897381200<2262267324339535663377616701520) (by decide : 2262267324339535663377616701520≤2297409704216174560631015003920) witness_block_44 witness_block_45

private theorem witness_union_97 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 2297525223513116794264594763920≤n ∧ n≤7031987816696336048954752216640 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 2297525223513116794264594763920≤2833329961001526059794019610620) (by decide : 2833329961001526059794019610620<2833710027231839552603252879420) (by decide : 2833710027231839552603252879420≤7031987816696336048954752216640) witness_block_46 witness_block_47

private theorem witness_union_98 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 7054734904970561324450619969620≤n ∧ n≤29439946377536901656231956748920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 7054734904970561324450619969620≤11973112626277096986224885927920) (by decide : 11973112626277096986224885927920<11978520927950649160111526349640) (by decide : 11978520927950649160111526349640≤29439946377536901656231956748920) witness_block_48 witness_block_49

private theorem witness_union_99 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 29441437512820521066978563534920≤n ∧ n≤8715718455545951703952185759239900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 29441437512820521066978563534920≤192670580314091182637359524967400) (by decide : 192670580314091182637359524967400<196458207596264561187634876159400) (by decide : 196458207596264561187634876159400≤8715718455545951703952185759239900) witness_block_50 witness_block_51

private theorem witness_union_100 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 15199049988692681535522910107358400≤n ∧ n≤53088815526992496085616409120091720 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 15199049988692681535522910107358400≤30321003858715622780856934939571920) (by decide : 30321003858715622780856934939571920<30321166838972590448348318361563920) (by decide : 30321166838972590448348318361563920≤53088815526992496085616409120091720) witness_block_52 witness_block_53

private theorem witness_union_101 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 53088815610346447093775892348041800≤n ∧ n≤677539829085939050925568477695670420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 53088815610346447093775892348041800≤602370046976776724547381375889612900) (by decide : 602370046976776724547381375889612900<673886862329779903993544878735154420) (by decide : 673886862329779903993544878735154420≤677539829085939050925568477695670420) witness_block_54 witness_block_55

private theorem witness_union_102 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 677539829086980707719543345171249300≤n ∧ n≤1337977805083137489663466598690147900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 677539829086980707719543345171249300≤1083584454530455834261953237905036920) (by decide : 1083584454530455834261953237905036920<1090543447550314274917501326613592140) (by decide : 1090543447550314274917501326613592140≤1337977805083137489663466598690147900) witness_block_56 witness_block_57

private theorem witness_union_103 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 1349775043888829152116797640597594620≤n ∧ n≤10106441616306882775983299280797722400 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 1349775043888829152116797640597594620≤1723032502769361807595222955371375000) (by decide : 1723032502769361807595222955371375000<1726085227103337170888120670242245400) (by decide : 1726085227103337170888120670242245400≤10106441616306882775983299280797722400) witness_block_58 witness_block_59

private theorem witness_union_104 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 10106441651529794455780169313105413920≤n ∧ n≤49115035472242190422215494278533675400 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 10106441651529794455780169313105413920≤12055682802997577495075741144848845560) (by decide : 12055682802997577495075741144848845560<12497466394353091552759983883651718920) (by decide : 12497466394353091552759983883651718920≤49115035472242190422215494278533675400) witness_block_60 witness_block_61

private theorem witness_union_105 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 49115041298679801653777781606578475400≤n ∧ n≤4349775936277660855276028462039323031900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 49115041298679801653777781606578475400≤147935880160593545075867092862983969400) (by decide : 147935880160593545075867092862983969400<174320038706110105263020180551294987520) (by decide : 174320038706110105263020180551294987520≤4349775936277660855276028462039323031900) witness_block_62 witness_block_63

private theorem witness_union_106 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 4349775956505731571214981366005982439900≤n ∧ n≤4609507200071077391635151497284762557900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 4349775956505731571214981366005982439900≤4355940521501843199414052013024842070300) (by decide : 4355940521501843199414052013024842070300<4358130970279907724992467339938874479020) (by decide : 4358130970279907724992467339938874479020≤4609507200071077391635151497284762557900) witness_block_64 witness_block_65

private theorem witness_union_107 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 4610140314585477273316985559537193028300≤n ∧ n≤6394932398360437582032453866244101233484920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 4610140314585477273316985559537193028300≤111064072645328925362650839201266671213420) (by decide : 111064072645328925362650839201266671213420<192364911420946771439033038709172561675400) (by decide : 192364911420946771439033038709172561675400≤6394932398360437582032453866244101233484920) witness_block_66 witness_block_67

private theorem witness_union_108 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 6394971286474709964687062998992411160223320≤n ∧ n≤47548991502382008814994411224813763690339900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 6394971286474709964687062998992411160223320≤38074586561555068069051146962996340214410400) (by decide : 38074586561555068069051146962996340214410400<38074586561764736145418072596653454557813920) (by decide : 38074586561764736145418072596653454557813920≤47548991502382008814994411224813763690339900) witness_block_68 witness_block_69

private theorem witness_union_109 :
    ∃ T : Finset ℕ, T.card=30 ∧ ∀ n ∈ T, 47769098396251955015034087122979404843266420≤n ∧ n≤928111115730694600830179074029547745330193578920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 47769098396251955015034087122979404843266420≤5732030373062214813840468844662671610286079900) (by decide : 5732030373062214813840468844662671610286079900<5732033806868782782280554288793697392202879900) (by decide : 5732033806868782782280554288793697392202879900≤928111115730694600830179074029547745330193578920) witness_block_70 witness_block_71

private theorem witness_union_110 :
    ∃ T : Finset ℕ, T.card=19 ∧ ∀ n ∈ T, 936114336452222406576130643855385001894430978920≤n ∧ n≤74122730443541037135201517117483282080933412280249900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 936114336452222406576130643855385001894430978920≤3291647361285303545845199407028781295161141696421100) (by decide : 3291647361285303545845199407028781295161141696421100<46077807376837966347292241491449091013203034673854900) (by decide : 46077807376837966347292241491449091013203034673854900≤74122730443541037135201517117483282080933412280249900) witness_block_72 witness_block_73

private theorem witness_union_111 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 26≤n ∧ n≤679148834708 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 26≤5355218900) (by decide : 5355218900<5857281500) (by decide : 5857281500≤679148834708) witness_union_74 witness_union_75

private theorem witness_union_112 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 680623768820≤n ∧ n≤870861088154920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 680623768820≤103123720322120) (by decide : 103123720322120<291803401145900) (by decide : 291803401145900≤870861088154920) witness_union_76 witness_union_77

private theorem witness_union_113 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 873119486799520≤n ∧ n≤188328362662472420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 873119486799520≤25261174064199400) (by decide : 25261174064199400<34791914841397900) (by decide : 34791914841397900≤188328362662472420) witness_union_78 witness_union_79

private theorem witness_union_114 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 267378351711111020≤n ∧ n≤1004242667091207510400 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 267378351711111020≤9430094779280318920) (by decide : 9430094779280318920<11465741592220802600) (by decide : 11465741592220802600≤1004242667091207510400) witness_union_80 witness_union_81

private theorem witness_union_115 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 1004285512141896342400≤n ∧ n≤5442298099765917586400 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 1004285512141896342400≤1803189061310759379920) (by decide : 1803189061310759379920<1803189061471071699920) (by decide : 1803189061471071699920≤5442298099765917586400) witness_union_82 witness_union_83

private theorem witness_union_116 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 5450816127434573896400≤n ∧ n≤694007840958969225601420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 5450816127434573896400≤89684183026257464282420) (by decide : 89684183026257464282420<89839475103861900122420) (by decide : 89839475103861900122420≤694007840958969225601420) witness_union_84 witness_union_85

private theorem witness_union_117 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 694372017747257670376420≤n ∧ n≤11421999332884656468347420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 694372017747257670376420≤4660579416840962166946060) (by decide : 4660579416840962166946060<4738572704017740997009420) (by decide : 4738572704017740997009420≤11421999332884656468347420) witness_union_86 witness_union_87

private theorem witness_union_118 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 11421999416605100708507420≤n ∧ n≤235015281689705642087657120 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 11421999416605100708507420≤95069690026491749610604300) (by decide : 95069690026491749610604300<95069737810477603796977420) (by decide : 95069737810477603796977420≤235015281689705642087657120) witness_union_88 witness_union_89

private theorem witness_union_119 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 258393046425542627043008900≤n ∧ n≤271448349912440588834654420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 258393046425542627043008900≤262283037815955805044175420) (by decide : 262283037815955805044175420<262283184570771334007997820) (by decide : 262283184570771334007997820≤271448349912440588834654420) witness_union_90 witness_union_91

private theorem witness_union_120 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 271492828723236751499685620≤n ∧ n≤14629594782227873302878089920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 271492828723236751499685620≤5150225055016383331305085580) (by decide : 5150225055016383331305085580<5817962877026907029004383920) (by decide : 5817962877026907029004383920≤14629594782227873302878089920) witness_union_92 witness_union_93

private theorem witness_union_121 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 14630168592548308597026911920≤n ∧ n≤386007665827750896226612154420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 14630168592548308597026911920≤263407936968584941626538448920) (by decide : 263407936968584941626538448920<263408986221192563916851312920) (by decide : 263408986221192563916851312920≤386007665827750896226612154420) witness_union_94 witness_union_95

private theorem witness_union_122 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 386027297532230304785331322420≤n ∧ n≤7031987816696336048954752216640 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 386027297532230304785331322420≤2297409704216174560631015003920) (by decide : 2297409704216174560631015003920<2297525223513116794264594763920) (by decide : 2297525223513116794264594763920≤7031987816696336048954752216640) witness_union_96 witness_union_97

private theorem witness_union_123 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 7054734904970561324450619969620≤n ∧ n≤8715718455545951703952185759239900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 7054734904970561324450619969620≤29439946377536901656231956748920) (by decide : 29439946377536901656231956748920<29441437512820521066978563534920) (by decide : 29441437512820521066978563534920≤8715718455545951703952185759239900) witness_union_98 witness_union_99

private theorem witness_union_124 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 15199049988692681535522910107358400≤n ∧ n≤677539829085939050925568477695670420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 15199049988692681535522910107358400≤53088815526992496085616409120091720) (by decide : 53088815526992496085616409120091720<53088815610346447093775892348041800) (by decide : 53088815610346447093775892348041800≤677539829085939050925568477695670420) witness_union_100 witness_union_101

private theorem witness_union_125 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 677539829086980707719543345171249300≤n ∧ n≤10106441616306882775983299280797722400 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 677539829086980707719543345171249300≤1337977805083137489663466598690147900) (by decide : 1337977805083137489663466598690147900<1349775043888829152116797640597594620) (by decide : 1349775043888829152116797640597594620≤10106441616306882775983299280797722400) witness_union_102 witness_union_103

private theorem witness_union_126 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 10106441651529794455780169313105413920≤n ∧ n≤4349775936277660855276028462039323031900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 10106441651529794455780169313105413920≤49115035472242190422215494278533675400) (by decide : 49115035472242190422215494278533675400<49115041298679801653777781606578475400) (by decide : 49115041298679801653777781606578475400≤4349775936277660855276028462039323031900) witness_union_104 witness_union_105

private theorem witness_union_127 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 4349775956505731571214981366005982439900≤n ∧ n≤6394932398360437582032453866244101233484920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 4349775956505731571214981366005982439900≤4609507200071077391635151497284762557900) (by decide : 4609507200071077391635151497284762557900<4610140314585477273316985559537193028300) (by decide : 4610140314585477273316985559537193028300≤6394932398360437582032453866244101233484920) witness_union_106 witness_union_107

private theorem witness_union_128 :
    ∃ T : Finset ℕ, T.card=60 ∧ ∀ n ∈ T, 6394971286474709964687062998992411160223320≤n ∧ n≤928111115730694600830179074029547745330193578920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 6394971286474709964687062998992411160223320≤47548991502382008814994411224813763690339900) (by decide : 47548991502382008814994411224813763690339900<47769098396251955015034087122979404843266420) (by decide : 47769098396251955015034087122979404843266420≤928111115730694600830179074029547745330193578920) witness_union_108 witness_union_109

private theorem witness_union_129 :
    ∃ T : Finset ℕ, T.card=120 ∧ ∀ n ∈ T, 26≤n ∧ n≤870861088154920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 26≤679148834708) (by decide : 679148834708<680623768820) (by decide : 680623768820≤870861088154920) witness_union_111 witness_union_112

private theorem witness_union_130 :
    ∃ T : Finset ℕ, T.card=120 ∧ ∀ n ∈ T, 873119486799520≤n ∧ n≤1004242667091207510400 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 873119486799520≤188328362662472420) (by decide : 188328362662472420<267378351711111020) (by decide : 267378351711111020≤1004242667091207510400) witness_union_113 witness_union_114

private theorem witness_union_131 :
    ∃ T : Finset ℕ, T.card=120 ∧ ∀ n ∈ T, 1004285512141896342400≤n ∧ n≤694007840958969225601420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 1004285512141896342400≤5442298099765917586400) (by decide : 5442298099765917586400<5450816127434573896400) (by decide : 5450816127434573896400≤694007840958969225601420) witness_union_115 witness_union_116

private theorem witness_union_132 :
    ∃ T : Finset ℕ, T.card=120 ∧ ∀ n ∈ T, 694372017747257670376420≤n ∧ n≤235015281689705642087657120 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 694372017747257670376420≤11421999332884656468347420) (by decide : 11421999332884656468347420<11421999416605100708507420) (by decide : 11421999416605100708507420≤235015281689705642087657120) witness_union_117 witness_union_118

private theorem witness_union_133 :
    ∃ T : Finset ℕ, T.card=120 ∧ ∀ n ∈ T, 258393046425542627043008900≤n ∧ n≤14629594782227873302878089920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 258393046425542627043008900≤271448349912440588834654420) (by decide : 271448349912440588834654420<271492828723236751499685620) (by decide : 271492828723236751499685620≤14629594782227873302878089920) witness_union_119 witness_union_120

private theorem witness_union_134 :
    ∃ T : Finset ℕ, T.card=120 ∧ ∀ n ∈ T, 14630168592548308597026911920≤n ∧ n≤7031987816696336048954752216640 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 14630168592548308597026911920≤386007665827750896226612154420) (by decide : 386007665827750896226612154420<386027297532230304785331322420) (by decide : 386027297532230304785331322420≤7031987816696336048954752216640) witness_union_121 witness_union_122

private theorem witness_union_135 :
    ∃ T : Finset ℕ, T.card=120 ∧ ∀ n ∈ T, 7054734904970561324450619969620≤n ∧ n≤677539829085939050925568477695670420 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 7054734904970561324450619969620≤8715718455545951703952185759239900) (by decide : 8715718455545951703952185759239900<15199049988692681535522910107358400) (by decide : 15199049988692681535522910107358400≤677539829085939050925568477695670420) witness_union_123 witness_union_124

private theorem witness_union_136 :
    ∃ T : Finset ℕ, T.card=120 ∧ ∀ n ∈ T, 677539829086980707719543345171249300≤n ∧ n≤4349775936277660855276028462039323031900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 677539829086980707719543345171249300≤10106441616306882775983299280797722400) (by decide : 10106441616306882775983299280797722400<10106441651529794455780169313105413920) (by decide : 10106441651529794455780169313105413920≤4349775936277660855276028462039323031900) witness_union_125 witness_union_126

private theorem witness_union_137 :
    ∃ T : Finset ℕ, T.card=120 ∧ ∀ n ∈ T, 4349775956505731571214981366005982439900≤n ∧ n≤928111115730694600830179074029547745330193578920 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 4349775956505731571214981366005982439900≤6394932398360437582032453866244101233484920) (by decide : 6394932398360437582032453866244101233484920<6394971286474709964687062998992411160223320) (by decide : 6394971286474709964687062998992411160223320≤928111115730694600830179074029547745330193578920) witness_union_127 witness_union_128

private theorem witness_union_138 :
    ∃ T : Finset ℕ, T.card=240 ∧ ∀ n ∈ T, 26≤n ∧ n≤1004242667091207510400 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 26≤870861088154920) (by decide : 870861088154920<873119486799520) (by decide : 873119486799520≤1004242667091207510400) witness_union_129 witness_union_130

private theorem witness_union_139 :
    ∃ T : Finset ℕ, T.card=240 ∧ ∀ n ∈ T, 1004285512141896342400≤n ∧ n≤235015281689705642087657120 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 1004285512141896342400≤694007840958969225601420) (by decide : 694007840958969225601420<694372017747257670376420) (by decide : 694372017747257670376420≤235015281689705642087657120) witness_union_131 witness_union_132

private theorem witness_union_140 :
    ∃ T : Finset ℕ, T.card=240 ∧ ∀ n ∈ T, 258393046425542627043008900≤n ∧ n≤7031987816696336048954752216640 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 258393046425542627043008900≤14629594782227873302878089920) (by decide : 14629594782227873302878089920<14630168592548308597026911920) (by decide : 14630168592548308597026911920≤7031987816696336048954752216640) witness_union_133 witness_union_134

private theorem witness_union_141 :
    ∃ T : Finset ℕ, T.card=240 ∧ ∀ n ∈ T, 7054734904970561324450619969620≤n ∧ n≤4349775936277660855276028462039323031900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 7054734904970561324450619969620≤677539829085939050925568477695670420) (by decide : 677539829085939050925568477695670420<677539829086980707719543345171249300) (by decide : 677539829086980707719543345171249300≤4349775936277660855276028462039323031900) witness_union_135 witness_union_136

private theorem witness_union_142 :
    ∃ T : Finset ℕ, T.card=139 ∧ ∀ n ∈ T, 4349775956505731571214981366005982439900≤n ∧ n≤74122730443541037135201517117483282080933412280249900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 4349775956505731571214981366005982439900≤928111115730694600830179074029547745330193578920) (by decide : 928111115730694600830179074029547745330193578920<936114336452222406576130643855385001894430978920) (by decide : 936114336452222406576130643855385001894430978920≤74122730443541037135201517117483282080933412280249900) witness_union_137 witness_union_110

private theorem witness_union_143 :
    ∃ T : Finset ℕ, T.card=480 ∧ ∀ n ∈ T, 26≤n ∧ n≤235015281689705642087657120 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 26≤1004242667091207510400) (by decide : 1004242667091207510400<1004285512141896342400) (by decide : 1004285512141896342400≤235015281689705642087657120) witness_union_138 witness_union_139

private theorem witness_union_144 :
    ∃ T : Finset ℕ, T.card=480 ∧ ∀ n ∈ T, 258393046425542627043008900≤n ∧ n≤4349775936277660855276028462039323031900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 258393046425542627043008900≤7031987816696336048954752216640) (by decide : 7031987816696336048954752216640<7054734904970561324450619969620) (by decide : 7054734904970561324450619969620≤4349775936277660855276028462039323031900) witness_union_140 witness_union_141

private theorem witness_union_145 :
    ∃ T : Finset ℕ, T.card=960 ∧ ∀ n ∈ T, 26≤n ∧ n≤4349775936277660855276028462039323031900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 26≤235015281689705642087657120) (by decide : 235015281689705642087657120<258393046425542627043008900) (by decide : 258393046425542627043008900≤4349775936277660855276028462039323031900) witness_union_143 witness_union_144

private theorem witness_union_146 :
    ∃ T : Finset ℕ, T.card=1099 ∧ ∀ n ∈ T, 26≤n ∧ n≤74122730443541037135201517117483282080933412280249900 ∧ n∈a352346Set :=
  join_witness_sets (by decide : 26≤4349775936277660855276028462039323031900) (by decide : 4349775936277660855276028462039323031900<4349775956505731571214981366005982439900) (by decide : 4349775956505731571214981366005982439900≤74122730443541037135201517117483282080933412280249900) witness_union_145 witness_union_142

/-- A certified set of 1099 distinct common values, including the 205 entries in the published table. -/
theorem certified_common_values :
    ∃ T : Finset ℕ, T.card=1099 ∧ ∀ n ∈ T, 26≤n ∧ n≤74122730443541037135201517117483282080933412280249900 ∧ n∈a352346Set := witness_union_146

end Digit352

namespace Digit352
open OMA.S_oeis_a352346 Finset

/-- The largest listed witness, with its two explicit positive indices. -/
theorem large_witness :
    a061078 112486343606422870858164831640658 = 74122730443541037135201517117483282080933412280249900 ∧
    a061077 92091259122723875606087362612089 = 74122730443541037135201517117483282080933412280249900 := by
  have e := read_decimal_word [2,2,4,9,7,2,6,8,7,2,1,2,8,4,5,7,4,1,7,1,6,3,2,9,6,6,3,2,8,1,3,1] (by decide) 0
  change 3706136522177051856760075855874164018416441908961871 = ∑ j ∈ range 22497268721284574171632966328131, digitProd j ∧ 142717047841751040 = digitProd 22497268721284574171632966328131 at e
  have o := read_decimal_word [1,8,4,1,8,2,5,1,8,2,4,5,4,4,7,7,5,1,2,1,2,1,7,4,7,2,5,2,2,4,1,7] (by decide) 0
  change 2964909217741641485408060684699331281432698607613196 = ∑ j ∈ range 18418251824544775121217472522417, digitProd j ∧ 2819746693120000 = digitProd 18418251824544775121217472522417 at o
  constructor
  · rw [show 112486343606422870858164831640658=5*22497268721284574171632966328131+3 by decide, even_block _ _ (by decide), ←e.1, ←e.2]
  · rw [show 92091259122723875606087362612089=5*18418251824544775121217472522417+4 by decide, odd_block _ _ (by decide), ←o.1, ←o.2]
    decide

end Digit352

namespace Digit352
open Finset

/-- Finite Fourier inversion for the intersection of two sets of integer
representatives, separating the trivial character. -/
theorem fourier_intersection_complex (M : ℕ) [NeZero M] (A B : Finset ℕ)
    (hA : A ⊆ range M) (hB : B ⊆ range M) :
    (M:ℂ)*(A∩B).card = (A.card:ℂ)*B.card +
      ∑ h ∈ (univ : Finset (ZMod M)).erase 0,
        (∑ a ∈ A, ZMod.stdAddChar ((a : ZMod M)*h)) *
        (∑ b ∈ B, ZMod.stdAddChar (-((b : ZMod M)*h))) := by
  classical
  let W := fun (h : ZMod M) =>
    (∑ a ∈ A, ZMod.stdAddChar ((a : ZMod M)*h)) *
    (∑ b ∈ B, ZMod.stdAddChar (-((b : ZMod M)*h)))
  have orth (a b : ℕ) (ha : a ∈ A) (hb : b ∈ B) :
      (∑ h : ZMod M, ZMod.stdAddChar ((a : ZMod M)*h) *
        ZMod.stdAddChar (-((b : ZMod M)*h))) = if a=b then (M:ℂ) else 0 := by
    simp_rw [← AddChar.map_add_eq_mul,← sub_eq_add_neg,← sub_mul]
    by_cases eq : a=b
    · simp [eq,ZMod.card]
    · rw [if_neg eq]
      have hn : (a:ZMod M)-(b:ZMod M) ≠ 0 := by
        intro e
        have he := congrArg ZMod.val (sub_eq_zero.mp e)
        exact eq (by simpa [ZMod.val_natCast,Nat.mod_eq_of_lt (mem_range.mp (hA ha)),
          Nat.mod_eq_of_lt (mem_range.mp (hB hb))] using he)
      exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar M hn)
  have all_freq : ∑ h : ZMod M, W h = (M:ℂ)*(A∩B).card := by
    calc
      ∑ h : ZMod M, W h = ∑ a ∈ A, ∑ b ∈ B, ∑ h : ZMod M,
          ZMod.stdAddChar ((a : ZMod M)*h)*ZMod.stdAddChar (-((b : ZMod M)*h)) := by
        simp only [W,sum_mul]
        simp only [mul_sum]
        rw [sum_comm]
        apply sum_congr rfl
        intro a ha
        rw [sum_comm]
      _ = ∑ a ∈ A, ∑ b ∈ B, if a=b then (M:ℂ) else 0 := by
        exact sum_congr rfl fun a ha => sum_congr rfl fun b hb => orth a b ha hb
      _ = (M:ℂ)*(A∩B).card := by
        simp only [sum_ite_eq]
        rw [←sum_filter,filter_mem_eq_inter,sum_const,nsmul_eq_mul,mul_comm]
  have hz : W 0 = (A.card:ℂ)*B.card := by simp [W,AddChar.map_zero_eq_one]
  change (M:ℂ)*(A∩B).card = (A.card:ℂ)*B.card+∑ h ∈ univ.erase 0, W h
  rw [← all_freq, ← hz, add_comm, sum_erase_add _ _ (mem_univ (0:ZMod M))]

/-- The real-valued identity used to estimate correlations over frequency sets. -/
theorem fourier_intersection (M : ℕ) [NeZero M] (A B : Finset ℕ)
    (hA : A ⊆ range M) (hB : B ⊆ range M) :
    (M:ℝ)*(A∩B).card = (A.card:ℝ)*B.card +
      ∑ h ∈ (univ : Finset (ZMod M)).erase 0,
        ((∑ a ∈ A, ZMod.stdAddChar ((a : ZMod M)*h)) *
         (∑ b ∈ B, ZMod.stdAddChar (-((b : ZMod M)*h)))).re := by
  have e := congrArg Complex.re (fourier_intersection_complex M A B hA hB)
  simpa only [Complex.add_re, Complex.re_sum, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, zero_mul, sub_zero] using e

end Digit352

namespace Digit352
open OMA.S_oeis_a352346 Finset

/-- A common value can be detected in a finite initial window without
aliasing. Infinitude is equivalent to a positive correlation in some
such window above each prescribed threshold. -/
theorem infinite_iff_positive_fourier :
    let E (t N : ℕ) := ((Icc 1 N).image a061078).filter (fun v => t<v)
    let O (t N : ℕ) := ((Icc 1 N).image a061077).filter (fun v => t<v)
    let M (N : ℕ) := max (a061078 N) (a061077 N)+1
    let F (t N : ℕ) := ((E t N).card:ℝ)*(O t N).card +
      ∑ h ∈ (univ : Finset (ZMod (M N))).erase 0,
        ((∑ a ∈ E t N, ZMod.stdAddChar ((a:ZMod (M N))*h)) *
         (∑ b ∈ O t N, ZMod.stdAddChar (-((b:ZMod (M N))*h)))).re
    a352346Set.Infinite ↔ ∀ t : ℕ, ∃ N : ℕ, 0 < F t N := by
  intro E O M F
  have mono (f : ℕ → ℕ) {i N : ℕ} (hi : i≤N) :
      ∑ j ∈ Icc 1 i, f j ≤ ∑ j ∈ Icc 1 N, f j :=
    sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right hi) (by intros; omega)
  have range_bound (t N : ℕ) (f : ℕ → ℕ) (hf : Monotone f) (hN : f N < M N) :
      ((Icc 1 N).image f).filter (fun v => t<v) ⊆ range (M N) := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp (mem_filter.mp hv).1
    exact mem_range.mpr ((hf (mem_Icc.mp hi).2).trans_lt hN)
  have window (t N : ℕ) : 0<F t N ↔ (E t N ∩ O t N).Nonempty := by
    have he : E t N ⊆ range (M N) := range_bound t N a061078
      (fun _ _ h => mono _ h) (Nat.lt_succ_of_le (le_max_left _ _))
    have ho : O t N ⊆ range (M N) := range_bound t N a061077
      (fun _ _ h => mono _ h) (Nat.lt_succ_of_le (le_max_right _ _))
    have hh := fourier_intersection (M N) (E t N) (O t N) he ho
    change (M N:ℝ)*(E t N ∩ O t N).card = F t N at hh
    have hpos : (0:ℝ)<M N := by exact_mod_cast Nat.succ_pos _
    rw [←hh,mul_pos_iff_of_pos_left hpos,Nat.cast_pos,Finset.card_pos]
  rw [Set.infinite_iff_exists_gt]
  constructor
  · intro h t
    obtain ⟨v,⟨⟨i,hi,ei⟩,⟨j,hj,oj⟩⟩,hv⟩ := h t
    refine ⟨max i j, (window _ _).mpr ⟨v, mem_inter.mpr ⟨?_,?_⟩⟩⟩
    · exact mem_filter.mpr ⟨mem_image.mpr ⟨i,mem_Icc.mpr ⟨hi,le_max_left _ _⟩,ei⟩,hv⟩
    · exact mem_filter.mpr ⟨mem_image.mpr ⟨j,mem_Icc.mpr ⟨hj,le_max_right _ _⟩,oj⟩,hv⟩
  · intro h t
    obtain ⟨N,hN⟩ := h t
    obtain ⟨v,hv⟩ := (window t N).mp hN
    obtain ⟨hi,hj⟩ := mem_inter.mp hv
    obtain ⟨i,hi',ei⟩ := mem_image.mp (mem_filter.mp hi).1
    obtain ⟨j,hj',oj⟩ := mem_image.mp (mem_filter.mp hj).1
    exact ⟨v,⟨⟨i,(mem_Icc.mp hi').1,ei⟩,⟨j,(mem_Icc.mp hj').1,oj⟩⟩,(mem_filter.mp hi).2⟩

end Digit352

namespace Digit352
open OMA.S_oeis_a352346 Finset

/-- A first solution of size at most 5·10^m has cumulative value strictly
below the chosen modulus. This is the archimedean part of the lifting test. -/
theorem odd_below_modulus {j m : ℕ} (hj : j ≤ 5*10^m) : a061077 j < 2^(6*(m+1)) := by
  have mono : Monotone a061077 := by
    intro x y h
    exact sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right h) (by intros; omega)
  have h := mono hj
  rw [(complete_blocks _).2] at h
  have p := prefix_power_ten m
  have hu : a061077 j < 45^(m+1) := by omega
  rw [pow_mul]
  exact hu.trans_le (Nat.pow_le_pow_left (by decide : 45≤2^6) (m+1))

end Digit352

namespace OMA.R_oeis_a352346_R1
open OMA.S_oeis_a352346 Digit352

/-- Every dyadic residue has a positive odd-index summatory preimage. -/
def H1 : Prop :=
  ∀ k r : ℕ, ∃ j : ℕ, 0 < j ∧ a061077 j ≡ r [MOD 2^k]

/-- Arbitrarily large even-side values have a short least odd-side
preimage for infinitely many dyadic precisions. A short preimage has
index at most 5·10^m at precision 6(m+1) bits. -/
def H2 : Prop :=
  ∀ B : ℕ, ∃ i : ℕ, 0 < i ∧ B < a061078 i ∧ ∀ m₀ : ℕ, ∃ m ≥ m₀,
    sInf {j : ℕ | 0 < j ∧ a061077 j ≡ a061078 i [MOD 2^(6*(m+1))]} ≤ 5*10^m

/-- The modular solvability step already follows from positive decimal repunits. -/
theorem odd_lifts_proved : H1 := odd_residue_exists

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a352346.main := by
  intro hres hshort
  apply Set.infinite_iff_exists_gt.mpr
  intro B
  obtain ⟨i,ipos,hB,hm⟩ := hshort B
  obtain ⟨m,hmi,hsmall⟩ := hm (a061078 i)
  let S := {j : ℕ | 0 < j ∧ a061077 j ≡ a061078 i [MOD 2^(6*(m+1))]}
  have nonempty : S.Nonempty := hres (6*(m+1)) (a061078 i)
  obtain ⟨jpos,hmod⟩ := Nat.sInf_mem nonempty
  have oddlt := odd_below_modulus hsmall
  have evenlt : a061078 i < 2^(6*(m+1)) :=
    hmi.trans_lt (((Nat.lt_two_pow_self : m < 2^m)).trans_le (Nat.pow_le_pow_right (by decide) (by omega)))
  change a061077 (sInf S) % _ = a061078 i % _ at hmod
  rw [Nat.mod_eq_of_lt oddlt, Nat.mod_eq_of_lt evenlt] at hmod
  exact ⟨a061078 i,⟨⟨i,ipos,rfl⟩,⟨sInf S,jpos,hmod⟩⟩,hB⟩

/-- The least-preimage height condition is also necessary. Every actual
odd-side witness bounds the least modular preimage at all precisions. -/
theorem height_of_infinite (h : a352346Set.Infinite) : H2 := by
  intro B
  obtain ⟨v,⟨⟨i,hi,he⟩,⟨j,hj,ho⟩⟩,hv⟩ := Set.infinite_iff_exists_gt.mp h B
  refine ⟨i,hi,he.symm ▸ hv,?_⟩
  intro m₀
  let m := max m₀ j
  refine ⟨m,le_max_left _ _,?_⟩
  have hn : j ∈ {n : ℕ | 0 < n ∧ a061077 n ≡ a061078 i [MOD 2^(6*(m+1))]} :=
    ⟨hj,by rw [ho,he]⟩
  apply (Nat.sInf_le hn).trans
  have small := ((Nat.lt_two_pow_self : m < 2^m)).le.trans (Nat.pow_le_pow_left (by decide : 2≤10) m)
  have jm : j ≤ m := le_max_right _ _
  omega

/-- With the dyadic orbit proved above, exactly the height condition remains. -/
theorem infinite_iff_height : a352346Set.Infinite ↔ H2 :=
  ⟨height_of_infinite, main odd_lifts_proved⟩

end OMA.R_oeis_a352346_R1
