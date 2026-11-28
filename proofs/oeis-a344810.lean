import OMAStatements.S_oeis_a344810

-- Credit: @Aryan-Poonacha
-- Any sufficiently large integer has arbitrarily many positive six-square representations.
namespace SixSquares
open OMA.S_oeis_a344810

def weight (s : Multiset ℕ) := (s.map (· ^ 2)).sum

def valid (k m : ℕ) (s : Multiset ℕ) : Prop :=
  s.card = k ∧ (∀ x ∈ s, 0 < x) ∧ weight s = m

def put (x : ℕ) : Multiset ℕ ↪ Multiset ℕ :=
  ⟨fun s => x ::ₘ s, fun _ _ h => (Multiset.cons_inj_right _).mp h⟩

/-- Enumerate a representation in order of largest root first. -/
def enum : ℕ → ℕ → ℕ → Finset (Multiset ℕ)
  | 0, m, _ => if m = 0 then {0} else ∅
  | k+1, m, b =>
    (Finset.Icc 1 (min b (Nat.sqrt m))).biUnion fun x =>
      (enum k (m-x^2) x).map (put x)

theorem in_enum (k m b : ℕ) (s : Multiset ℕ) :
    s ∈ enum k m b ↔ valid k m s ∧ ∀ x ∈ s, x ≤ b := by
  induction k generalizing m b s with
  | zero =>
    by_cases hs : s = 0
    · subst s; by_cases hm : m = 0 <;> (simp [hm,enum,valid,weight]; try omega)
    · by_cases hm : m = 0 <;> simp [hm,hs,enum,valid]
  | succ k ih =>
    constructor
    · intro e
      obtain ⟨x,hx,h⟩ := Finset.mem_biUnion.mp e
      obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp h
      obtain ⟨⟨hk,hp,hw⟩, hb⟩ := (ih _ _ _).mp hs
      obtain ⟨hx₁,hx₂⟩ := Finset.mem_Icc.mp hx
      have x2 := Nat.le_sqrt.mp (le_min_iff.mp hx₂).2
      rw [← sq] at x2
      change valid (k+1) m (x ::ₘ s) ∧ ∀ y ∈ x ::ₘ s, y ≤ b
      simp only [valid,Multiset.card_cons,Multiset.mem_cons,forall_eq_or_imp,weight,
        Multiset.map_cons,Multiset.sum_cons]
      change (s.map (· ^ 2)).sum = _ at hw
      exact ⟨⟨by omega,⟨by omega,hp⟩,by omega⟩,(le_min_iff.mp hx₂).1,
        fun i hi => (hb i hi).trans (le_min_iff.mp hx₂).1⟩
    · rintro ⟨⟨hk,hp,hw⟩,hb⟩
      have hne : s.toFinset.Nonempty := by
        simpa using (Multiset.card_pos.mp (show 0 < s.card by omega))
      let x := s.toFinset.max' hne
      have hx : x ∈ s := Multiset.mem_toFinset.mp (Finset.max'_mem _ _)
      let t := s.erase x
      have ht : x ::ₘ t = s := Multiset.cons_erase hx
      have hc := congrArg Multiset.card ht
      have hw' := congrArg weight ht
      simp only [Multiset.card_cons,hk] at hc
      simp only [weight,Multiset.map_cons,Multiset.sum_cons] at hw'
      change x^2 + weight t = weight s at hw'
      have htx (y) (hy : y ∈ t) : y ∈ s :=
        Multiset.mem_of_le (Multiset.erase_le _ _) hy
      have xmax (y) (hy : y ∈ t) : y ≤ x :=
        Finset.le_max' _ y (Multiset.mem_toFinset.mpr (htx y hy))
      apply Finset.mem_biUnion.mpr
      refine ⟨x,Finset.mem_Icc.mpr ⟨hp x hx,le_min (hb x hx) (Nat.le_sqrt.mpr (by rw [← sq]; omega))⟩,?_⟩
      apply Finset.mem_map.mpr
      exact ⟨t,(ih _ _ _).mpr ⟨⟨by omega,fun y hy => hp y (htx y hy),by omega⟩,xmax⟩,ht⟩

theorem root_bound {k m : ℕ} {s : Multiset ℕ} (h : valid k m s) (x : ℕ) (hx : x ∈ s) :
    x ≤ Nat.sqrt m := by
  apply Nat.le_sqrt.mpr
  rw [← sq]
  have e := congrArg weight (Multiset.cons_erase hx)
  simp only [weight,Multiset.map_cons,Multiset.sum_cons] at e
  change x^2 + weight (s.erase x) = weight s at e
  have := h.2.2
  omega

def allReps (k m : ℕ) := enum k m (Nat.sqrt m)

theorem in_all (k m : ℕ) (s : Multiset ℕ) : s ∈ allReps k m ↔ valid k m s := by
  rw [allReps,in_enum]
  exact ⟨And.left,fun h => ⟨h,root_bound h⟩⟩

theorem count_eq (m : ℕ) : r m = (allReps 6 m).card := by
  let e : {s : Multiset ℕ // valid 6 m s} ≃ (allReps 6 m) :=
    Equiv.subtypeEquivRight fun s => (in_all 6 m s).symm
  exact (Nat.card_congr e).trans (Nat.card_eq_finsetCard _)

theorem weight_add (s t : Multiset ℕ) : weight (s+t) = weight s + weight t := by
  simp [weight]
theorem weight_cons (x : ℕ) (s : Multiset ℕ) : weight (x ::ₘ s) = x^2 + weight s := by simp [weight]

theorem weight_pos_filter (s : Multiset ℕ) : weight (s.filter (0 < ·)) = weight s := by
  induction s using Multiset.induction_on with
  | empty => rfl
  | cons x s ih =>
    by_cases hx : x = 0
    · simp [hx,weight_cons,ih]
    · simp [Nat.pos_of_ne_zero hx,weight_cons,ih]

theorem padding (k : ℕ) (hk : 1 ≤ k ∧ k ≤ 4) : ∃ s : Multiset ℕ, valid (5-k) 169 s := by
  obtain ⟨h₁,h₂⟩ := hk
  interval_cases k
  · exact ⟨{1,2,8,10}, by norm_num [valid,weight]⟩
  · exact ⟨{3,4,12}, by norm_num [valid,weight]⟩
  · exact ⟨{5,12}, by norm_num [valid,weight]⟩
  · exact ⟨{13}, by norm_num [valid,weight]⟩

theorem marker (m j : ℕ) (hj : 0 < j) (hm : j^2 + 169 < m) :
    ∃ s ∈ allReps 6 m, j ∈ s := by
  obtain ⟨a,b,c,d,e⟩ := Nat.sum_four_squares (m-j^2-169)
  let s : Multiset ℕ := {a,b,c,d}
  let t := s.filter (0 < ·)
  have h₁ : weight t = m-j^2-169 := by
    rw [show weight t = weight s from weight_pos_filter _]
    simpa [s,weight,add_assoc] using e
  have h₂ : 1 ≤ t.card := by
    by_contra! h
    have he : t = 0 := Multiset.card_eq_zero.mp (by omega)
    rw [he] at h₁
    change 0 = _ at h₁
    omega
  have h₃ : t.card ≤ 4 := (Multiset.card_le_card (Multiset.filter_le _ _)).trans_eq
    (show s.card = 4 by simp [s])
  obtain ⟨u,hu₁,hu₂,hu₃⟩ := padding t.card ⟨h₂,h₃⟩
  refine ⟨j ::ₘ (t+u),(in_all _ _ _).mpr ?_,Multiset.mem_cons_self _ _⟩
  simp only [valid,Multiset.card_cons,Multiset.card_add,Multiset.mem_cons,Multiset.mem_add,
    forall_eq_or_imp,weight_cons,weight_add]
  refine ⟨by omega,⟨hj,fun x hx => ?_⟩,by omega⟩
  rcases hx with ht | hu
  · exact (Multiset.mem_filter.mp ht).2
  · exact hu₂ x hu

theorem many (q m : ℕ) (hm : (6*q+1)^2 + 169 < m) : q < r m := by
  let f (s : Multiset ℕ) := s.toFinset
  have sub : Finset.Icc 1 (6*q+1) ⊆ (allReps 6 m).biUnion f := by
    intro j hj
    obtain ⟨h₁,h₂⟩ := Finset.mem_Icc.mp hj
    have hsq : j^2 ≤ (6*q+1)^2 := Nat.pow_le_pow_left h₂ 2
    obtain ⟨s,hs,hj⟩ := marker m j h₁ (by omega)
    exact Finset.mem_biUnion.mpr ⟨s,hs,Multiset.mem_toFinset.mpr hj⟩
  have h := (Finset.card_le_card sub).trans (Finset.card_biUnion_le_card_mul _ f 6 (fun s hs =>
    (Multiset.toFinset_card_le _).trans_eq ((in_all _ _ _).mp hs).1))
  rw [← count_eq] at h
  simp only [Nat.card_Icc] at h
  omega

theorem large (m : ℕ) (hm : 3195 ≤ m) : 6 ≤ r m := many 5 m (by norm_num; omega)

def sumTo (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t+1 => sumTo f t + f (t+1)

theorem sumTo_eq (f : ℕ → ℕ) (n : ℕ) : sumTo f n = ∑ x ∈ Finset.Icc 1 n, f x := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih =>
    rw [sumTo,ih,Finset.sum_Icc_succ_top (by omega)]

theorem weight_le {s : Multiset ℕ} {b : ℕ} (h : ∀ x ∈ s, x ≤ b) :
    weight s ≤ s.card * b^2 := by
  have e := (s.map (·^2)).sum_le_card_nsmul (b^2) (fun x hx => by
    obtain ⟨y,hy,rfl⟩ := Multiset.mem_map.mp hx
    exact Nat.pow_le_pow_left (h _ hy) 2)
  simpa [weight] using e

/-- Count the same largest-root decomposition without retaining any multisets. -/
def num : ℕ → ℕ → ℕ → ℕ
  | 0, m, _ => if m = 0 then 1 else 0
  | k+1, m, b => if (k+1)*b^2 < m then 0 else
      sumTo (fun x => num k (m-x^2) x) (min b (Nat.sqrt m))

theorem enum_card (k m b : ℕ) : (enum k m b).card = num k m b := by
  induction k generalizing m b with
  | zero => by_cases h : m = 0 <;> simp [num,enum,h]
  | succ k ih =>
    by_cases impossible : (k+1)*b^2 < m
    · rw [num,if_pos impossible,Finset.card_eq_zero,Finset.eq_empty_iff_forall_notMem]
      intro s hs
      obtain ⟨⟨hc,_,hw⟩,hb⟩ := (in_enum _ _ _ _).mp hs
      have e := weight_le hb
      rw [hc,hw] at e
      omega
    rw [enum,num,if_neg impossible,sumTo_eq,Finset.card_biUnion]
    · simp_rw [Finset.card_map,ih]
    · intro x _ y _ hxy
      apply Finset.disjoint_left.mpr
      intro v hx hy
      obtain ⟨s,hs,ex⟩ := Finset.mem_map.mp hx
      obtain ⟨t,ht,ey⟩ := Finset.mem_map.mp hy
      change x ::ₘ s = v at ex
      change y ::ₘ t = v at ey
      have h (z : ℕ) (u : Multiset ℕ) (hu : u ∈ enum k (m-z^2) z) (eu : z ::ₘ u = v) :
          ∀ i ∈ v, i ≤ z := by
        rw [← eu]
        simpa only [Multiset.mem_cons,forall_eq_or_imp,le_refl,true_and] using
          ((in_enum _ _ _ _).mp hu).2
      apply hxy
      exact le_antisymm (h y t ht ey x (ex ▸ Multiset.mem_cons_self _ _))
        (h x s hs ex y (ey ▸ Multiset.mem_cons_self _ _))

def early (m : ℕ) : Prop :=
  m ∈ [54,57,60,62,65,68,69,71,72,75,76,77,78,80,81,83,84,86,87,88,89,90] ∨ 92 ≤ m
instance (m : ℕ) : Decidable (early m) := by unfold early; infer_instance

theorem five_to_six (c j : ℕ) (hj : 0 < j) :
    (allReps 5 c).card ≤ (allReps 6 (c+j^2)).card := by
  rw [← Finset.card_map (put j) (s := allReps 5 c)]
  apply Finset.card_le_card
  intro s hs
  obtain ⟨t,ht,rfl⟩ := Finset.mem_map.mp hs
  obtain ⟨hc,hp,hw⟩ := (in_all _ _ _).mp ht
  apply (in_all _ _ _).mpr
  change valid 6 (c+j^2) (j ::ₘ t)
  simp only [valid,Multiset.card_cons,Multiset.mem_cons,forall_eq_or_imp,weight_cons,hc,hw]
  exact ⟨True.intro,⟨hj,hp⟩,Nat.add_comm _ _⟩

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem small_cert : ∀ i : Fin 227, (6 ≤ num 6 i (Nat.sqrt i)) ↔ early i := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
theorem five_cert : ∀ i : Fin 109, 6 ≤ num 5 (226+i.val) (Nat.sqrt (226+i.val)) := by
  decide +kernel

theorem classify (m : ℕ) : m ∈ S ↔ early m := by
  change (6 ≤ r m) ↔ _
  by_cases hsmall : m < 227
  · rw [count_eq,allReps,enum_card]
    exact small_cert ⟨m,hsmall⟩
  have he : early m := Or.inr (by omega)
  refine iff_of_true ?_ he
  by_cases hlarge : 3195 ≤ m
  · exact large m hlarge
  let j := Nat.sqrt (m-226)
  have hj : 0 < j := Nat.sqrt_pos.mpr (by omega)
  have hj' : j < 55 := Nat.sqrt_lt.mpr (by omega)
  have hlow : j^2 ≤ m-226 := Nat.sqrt_le' _
  have hhigh : m-226 ≤ j^2 + j + j := by simpa only [Nat.pow_two] using Nat.sqrt_le_add (m-226)
  let c := m-j^2
  have hc : 226 ≤ c ∧ c ≤ 334 := by dsimp [c]; omega
  have hh := five_cert ⟨c-226,by omega⟩
  change 6 ≤ num 5 (226+(c-226)) (Nat.sqrt (226+(c-226))) at hh
  rw [show 226+(c-226) = c by omega, ← enum_card] at hh
  have hv := hh.trans (five_to_six c j hj)
  rw [count_eq,show m = c+j^2 by dsimp [c];omega]
  exact hv

def model (n : ℕ) : ℕ := if n < 23 then
  [0,54,57,60,62,65,68,69,71,72,75,76,77,78,80,81,83,84,86,87,88,89,90].getD n 0 else n+69

theorem count_tail (t : ℕ) : Nat.count early (92+t) = 22+t := by
  induction t with
  | zero => decide +kernel
  | succ t ih =>
    have he : early (92+t) := Or.inr (by omega)
    rw [show 92+t.succ = (92+t)+1 by omega,Nat.count_succ,if_pos he,ih]
    omega

theorem a_model (n : ℕ) (hn : 0 < n) : a n = model n := by
  have ep : (fun z => z ∈ S) = early := funext fun z => propext (classify z)
  rw [a,ep]
  have hspec : early (model n) ∧ Nat.count early (model n) = n-1 := by
    by_cases h : n < 23
    · have hv : ∀ i : Fin 22, early (model (i.val+1)) ∧ Nat.count early (model (i.val+1)) = i.val := by decide +kernel
      simpa only [show n-1+1 = n by omega] using hv ⟨n-1,by omega⟩
    · have he : model n = 92+(n-23) := by simp [model,h]; omega
      rw [he,count_tail]
      exact ⟨Or.inr (by omega),by omega⟩
  rw [← hspec.2,Nat.nth_count hspec.1]

theorem recurrence (n : ℕ) (hn : 25 ≤ n) :
    (a n : ℤ) = 2*a (n-1) - a (n-2) := by
  simp (disch := omega) only [a_model,model,if_neg]
  omega

open PowerSeries

theorem generating_function : PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (PowerSeries.X - 1) ^ 2 =
      PowerSeries.X * (-PowerSeries.X ^ 23 + PowerSeries.X ^ 22 - PowerSeries.X ^ 18
        + PowerSeries.X ^ 17 - PowerSeries.X ^ 16 + PowerSeries.X ^ 15
        - PowerSeries.X ^ 14 + PowerSeries.X ^ 13 - 2 * PowerSeries.X ^ 10
        + 2 * PowerSeries.X ^ 9 - PowerSeries.X ^ 8 + PowerSeries.X ^ 7
        - 2 * PowerSeries.X ^ 6 + PowerSeries.X ^ 4 - PowerSeries.X ^ 3
        - 51 * PowerSeries.X + 54) := by
  let A := PowerSeries.mk (fun n => (model n : ℚ))
  have eqA : PowerSeries.mk (fun n => if n=0 then (0:ℚ) else a n) = A := by
    ext n
    simp only [A,coeff_mk]
    by_cases hn : n=0
    · subst n; rfl
    · simp [hn,a_model n (Nat.pos_of_ne_zero hn)]
  rw [eqA]
  have hL : A*(X-1)^2 = A - C ((2 : ℕ) : ℚ)*(A*X^1) + A*X^2 := by
    simp only [map_natCast]; ring
  have hR : (PowerSeries.X * (-PowerSeries.X ^ 23 + PowerSeries.X ^ 22 - PowerSeries.X ^ 18
        + PowerSeries.X ^ 17 - PowerSeries.X ^ 16 + PowerSeries.X ^ 15
        - PowerSeries.X ^ 14 + PowerSeries.X ^ 13 - 2 * PowerSeries.X ^ 10
        + 2 * PowerSeries.X ^ 9 - PowerSeries.X ^ 8 + PowerSeries.X ^ 7
        - 2 * PowerSeries.X ^ 6 + PowerSeries.X ^ 4 - PowerSeries.X ^ 3
        - 51 * PowerSeries.X + 54) : PowerSeries ℚ) =
      C ((54 : ℕ) : ℚ)*X^1 - C ((51 : ℕ) : ℚ)*X^2 - C ((1 : ℕ) : ℚ)*X^4 + C ((1 : ℕ) : ℚ)*X^5 - C ((2 : ℕ) : ℚ)*X^7 + C ((1 : ℕ) : ℚ)*X^8 - C ((1 : ℕ) : ℚ)*X^9 + C ((2 : ℕ) : ℚ)*X^10 - C ((2 : ℕ) : ℚ)*X^11 + C ((1 : ℕ) : ℚ)*X^14 - C ((1 : ℕ) : ℚ)*X^15 + C ((1 : ℕ) : ℚ)*X^16 - C ((1 : ℕ) : ℚ)*X^17 + C ((1 : ℕ) : ℚ)*X^18 - C ((1 : ℕ) : ℚ)*X^19 + C ((1 : ℕ) : ℚ)*X^23 - C ((1 : ℕ) : ℚ)*X^24 := by
    simp only [map_natCast]; ring
  rw [hL,hR]
  ext k
  simp only [map_add,map_sub,coeff_C_mul_X_pow]
  simp only [coeff_C_mul,coeff_mul_X_pow',A,coeff_mk]
  by_cases hk : k ≤ 24
  · interval_cases k <;> norm_num [model,List.getD]
  · simp (disch := omega) only [if_pos,if_neg,model]
    push_cast [Nat.cast_sub (show 1 ≤ k by omega), Nat.cast_sub (show 2 ≤ k by omega)]
    ring
end SixSquares

theorem OMA.solution : type_of% @OMA.S_oeis_a344810.main :=
  ⟨SixSquares.recurrence, SixSquares.generating_function⟩
