import FormalConjectures.ErdosProblems.«186»
import Mathlib

/-!
The lower certificate uses a centered integer parabola. The upper certificate
only has to find an averaging subset in a primitive, translated configuration
of exactly a power of two points. The logarithmic limit follows from these
finite formulations.
-/

open Finset Filter Topology
namespace OMA.R_Erdos186_erdos_186_R1

/-- Explicit centered-parabola lower certificate at every integer scale. -/
def H1 : Prop := ∀ k : ℕ, 2 * k + 1 ≤
  Erdos186.F ((k * (2 * k + 1) + 1) * k ^ 2 + 2 * k + 1)

/-- At sufficiently large dyadic cardinalities, every short, primitive set
of the given size with both endpoints present contains a subset mean. -/
def H2 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ j : ℕ in atTop, ∀ D : ℕ,
    (1 / 4 + ε) * Real.log (D + 1 : ℕ) < Real.log (2 ^ j : ℕ) →
    ∀ P : Finset ℕ, P ⊆ Icc 0 D → 0 ∈ P → D ∈ P → P.gcd id = 1 →
      P.card = 2 ^ j → ∃ a ∈ P, ∃ T ⊆ P.erase a,
        2 ≤ T.card ∧ ∑ x ∈ T, x = T.card * a

/-- The sum of any selected first-coordinate deviations from a pivot in
[0,2k] has absolute value at most the triangular number k(2k+1). -/
theorem discrepancy (k j : ℕ) (hj : j ≤ 2*k) (T : Finset ℕ) (hT : T ⊆ range (2*k+1)) :
    |(∑ i ∈ T, (i : ℤ)) - (T.card : ℤ) * j| ≤ (k : ℤ) * (2*k+1) := by
  have hs := sum_range_id_mul_two (2*k+1)
  have hs' : (∑ i ∈ range (2*k+1), i) = k * (2*k+1) := by
    simp only [Nat.add_sub_cancel] at hs
    nlinarith only [hs]
  have hfull : (∑ i ∈ range (2*k+1), (i : ℤ)) = (k : ℤ)*(2*k+1) := by
    simpa only [Nat.cast_sum, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] using
      congrArg (fun n : ℕ => (n : ℤ)) hs'
  have hm : (∑ i ∈ T, (i : ℤ)) ≤ (k : ℤ)*(2*k+1) := by
    rw [← hfull]
    exact sum_le_sum_of_subset_of_nonneg hT (by intros; positivity)
  have hr : (∑ i ∈ T, ((2:ℤ)*k-i)) ≤ ∑ i ∈ range (2*k+1), ((2:ℤ)*k-i) := by
    apply sum_le_sum_of_subset_of_nonneg hT
    intro i hi _
    have hh : i ≤ 2*k := by have := mem_range.mp hi; omega
    exact sub_nonneg.mpr (by exact_mod_cast hh)
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul, card_range, hfull,
    Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat] at hr
  have hj' : (j : ℤ) ≤ 2*k := by exact_mod_cast hj
  rw [abs_le]
  constructor
  · nlinarith only [hr, mul_nonneg (Nat.cast_nonneg T.card : (0:ℤ) ≤ T.card)
        (sub_nonneg.mpr hj')]
  · nlinarith only [hm, mul_nonneg (Nat.cast_nonneg T.card : (0:ℤ) ≤ T.card)
        (Nat.cast_nonneg j : (0:ℤ) ≤ j)]

/-- The high digit is the square of the centered index. Equality of averages
first forces the linear moment modulo the base and then forces zero variance. -/
theorem centered_lower : H1 := by
  intro k
  let B : ℤ := (k : ℤ)*(2*k+1)+1
  let q (i : ℕ) := ((i:ℤ)-k)^2
  let f (i : ℕ) := (B * q i + i + 1).toNat
  have hB : 0 < B := by dsimp [B]; positivity
  have hcoef (i : ℕ) : (f i : ℤ) = B * q i + i + 1 := by
    apply Int.toNat_of_nonneg
    have : 0 ≤ q i := sq_nonneg _
    positivity
  let I := range (2*k+1)
  have hinj : Set.InjOn f (I : Set ℕ) := by
    intro i hi j hj h
    have hij : i ≤ 2*k := by have := mem_range.mp hi; omega
    have hjj : j ≤ 2*k := by have := mem_range.mp hj; omega
    have he := congrArg (fun n : ℕ => (n:ℤ)) h
    rw [hcoef, hcoef] at he
    have hd : B ∣ (i : ℤ) - j := ⟨q j-q i, by linear_combination he⟩
    have hbase : (2:ℤ)*k < B := by
      dsimp [B]
      by_cases hk : k = 0
      · simp [hk]
      · have hk' : (1:ℤ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
        nlinarith [mul_nonneg (Nat.cast_nonneg k : (0:ℤ) ≤ k) (sub_nonneg.mpr hk')]
    have hi' : (i:ℤ) ≤ 2*k := by exact_mod_cast hij
    have hj' : (j:ℤ) ≤ 2*k := by exact_mod_cast hjj
    have hz := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by linarith [Nat.cast_nonneg i (α:=ℤ)], by linarith [Nat.cast_nonneg j (α:=ℤ)]⟩)
    exact_mod_cast sub_eq_zero.mp hz
  have good : Erdos186.NonAveraging (I.image f) := by
    intro a ha U hU hu heq
    obtain ⟨j,hj,rfl⟩ := mem_image.mp ha
    have hsub : U ⊆ I.image f := fun x hx => (mem_erase.mp (hU hx)).2
    obtain ⟨T,hT,rfl⟩ := subset_image_iff.mp hsub
    have hct : (T.image f).card = T.card := card_image_of_injOn (hinj.mono hT)
    rw [hct] at hu heq
    rw [sum_image (fun _ hx _ hy he => hinj (hT hx) (hT hy) he)] at heq
    have he : (∑ i ∈ T, (f i : ℤ)) = (T.card : ℤ) * f j := by exact_mod_cast heq
    simp only [hcoef, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one] at he
    have hj' : j ≤ 2*k := by have := mem_range.mp hj; omega
    have hd : B ∣ (∑ i ∈ T, (i : ℤ)) - (T.card : ℤ)*j :=
      ⟨(T.card : ℤ)*q j - ∑ i ∈ T, q i, by linear_combination he⟩
    have hzero := Int.eq_zero_of_abs_lt_dvd hd
      (lt_of_le_of_lt (discrepancy k j hj' T hT) (by dsimp [B]; omega))
    have hlin := sub_eq_zero.mp hzero
    have hquad : (∑ i ∈ T, q i) = (T.card : ℤ)*q j := by
      apply mul_left_cancel₀ (ne_of_gt hB)
      linear_combination he - hlin
    have hvar : ∑ i ∈ T, ((i:ℤ)-j)^2 = 0 := by
      calc
        _ = ∑ i ∈ T, (q i + (2*(k:ℤ)-2*(j:ℤ))*i + ((j:ℤ)^2-(k:ℤ)^2)) := by
          apply sum_congr rfl
          intro i _
          dsimp [q]
          ring
        _ = 0 := by
          rw [sum_add_distrib, sum_add_distrib, ← mul_sum, hlin, hquad, sum_const, nsmul_eq_mul]
          dsimp [q]
          ring
    obtain ⟨i,hi⟩ := card_pos.mp (show 0 < T.card by omega)
    have hz := (sum_eq_zero_iff_of_nonneg (s:=T)
      (fun x _ => sq_nonneg ((x:ℤ)-j))).mp hvar i hi
    have hij : i = j := by exact_mod_cast sub_eq_zero.mp (by simpa using hz : (i:ℤ)-j=0)
    exact (mem_erase.mp (hU (mem_image_of_mem f hi))).1 (congrArg f hij)
  have hinterval : I.image f ⊆ Icc 1 ((k*(2*k+1)+1)*k^2+2*k+1) := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hx
    have hix : i ≤ 2*k := by have := mem_range.mp hi; omega
    have hi' : (i:ℤ) ≤ 2*k := by exact_mod_cast hix
    have hq : q i ≤ (k:ℤ)^2 := by
      dsimp [q]
      nlinarith only [mul_nonneg (Nat.cast_nonneg i : (0:ℤ) ≤ i) (sub_nonneg.mpr hi')]
    have hp : 1 ≤ (f i : ℤ) := by
      rw [hcoef]
      linarith [mul_nonneg hB.le (sq_nonneg ((i:ℤ)-k) : 0 ≤ q i), (Nat.cast_nonneg i : (0:ℤ) ≤ i)]
    have hl : (f i : ℤ) ≤ ((k:ℤ)*(2*k+1)+1)*k^2+2*k+1 := by
      rw [hcoef]
      dsimp [B] at *
      nlinarith only [mul_le_mul_of_nonneg_left hq hB.le, hi']
    exact mem_Icc.mpr ⟨by exact_mod_cast hp, by exact_mod_cast hl⟩
  have hc := Erdos186.card_le_F hinterval good
  simpa only [card_image_of_injOn hinj, I, card_range] using hc

/-- Positive integral dilations and translations transport a forbidden mean
back into the ambient set. Only containment of the image is required. -/
theorem affine_normalized_good {A P : Finset ℕ} (good : Erdos186.NonAveraging A)
    {g m : ℕ} (hg : 0 < g) (hmap : ∀ x ∈ P, g*x+m ∈ A) :
    Erdos186.NonAveraging P := by
  let e (x : ℕ) := g*x+m
  have inj : Function.Injective e := by
    intro x y h
    change g*x+m=g*y+m at h
    exact Nat.mul_left_cancel hg (Nat.add_right_cancel h)
  intro a ha U hU hu eq
  have sub : U.image e ⊆ A.erase (e a) := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    have hx' := mem_erase.mp (hU hx)
    exact mem_erase.mpr ⟨fun h => hx'.1 (inj h), hmap x hx'.2⟩
  apply good (e a) (hmap a ha) (U.image e) sub (by simpa [card_image_of_injective _ inj] using hu)
  rw [sum_image (fun _ _ _ _ h => inj h), card_image_of_injective _ inj]
  dsimp [e]
  rw [sum_add_distrib, ← mul_sum, eq, sum_const, nsmul_eq_mul]
  simp only [Nat.cast_id]
  ring

/-- Translate a set of at least two points by its minimum, then divide by the
gcd of all differences. This preserves cardinality and non-averaging. -/
theorem primitive_model {A : Finset ℕ} {N : ℕ} (hA : A ⊆ Icc 1 N)
    (good : Erdos186.NonAveraging A) (hcard : 2 ≤ A.card) :
    ∃ (D : ℕ) (P : Finset ℕ), D+1 ≤ N ∧ P ⊆ Icc 0 D ∧ 0 ∈ P ∧ D ∈ P ∧
      P.gcd id = 1 ∧ P.card = A.card ∧ Erdos186.NonAveraging P := by
  have hn : A.Nonempty := card_pos.mp (by omega)
  let m := A.min' hn
  have hm : m ∈ A := min'_mem _ _
  let b (x : ℕ) := x-m
  obtain ⟨y,hy,hby⟩ : ∃ y ∈ A, b y ≠ 0 := by
    by_contra! hall
    have hs : A ⊆ {m} := by
      intro x hx
      have hh := hall x hx
      have hle : m ≤ x := min'_le _ _ hx
      simp only [mem_singleton]
      dsimp [b] at hh
      omega
    have hc := card_le_card hs
    simp only [card_singleton] at hc
    omega
  let g := A.gcd b
  have hg : 0 < g := Nat.pos_of_ne_zero (fun h => hby (gcd_eq_zero_iff.mp h y hy))
  let f (x : ℕ) := b x / g
  have recov (x : ℕ) (hx : x ∈ A) : g*f x+m = x := by
    dsimp [f]
    rw [Nat.mul_div_cancel' (gcd_dvd hx)]
    exact Nat.sub_add_cancel (min'_le _ _ hx)
  have hinj : Set.InjOn f (A : Set ℕ) := by
    intro x hx z hz eq
    rw [← recov x hx, ← recov z hz, eq]
  let P := A.image f
  have hp : P.Nonempty := hn.image f
  let D := P.max' hp
  have hD : D ∈ P := max'_mem _ _
  have hDN : D+1 ≤ N := by
    obtain ⟨x,hx,he⟩ := mem_image.mp hD
    have hle : f x ≤ x-m := Nat.div_le_self _ _
    have ha := mem_Icc.mp (hA hx)
    have hlow := (mem_Icc.mp (hA hm)).1
    omega
  refine ⟨D,P,hDN,(fun x hx => mem_Icc.mpr ⟨Nat.zero_le _, le_max' _ _ hx⟩),
    ?_,hD,?_,card_image_of_injOn hinj,?_⟩
  · exact mem_image.mpr ⟨m,hm, by simp [f,b]⟩
  · dsimp [P]
    rw [gcd_image]
    exact gcd_div_eq_one hy hby
  · apply affine_normalized_good good hg (m:=m)
    intro z hz
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hz
    simpa only [recov x hx] using hx

/-- The extremum is attained by a finite set, and increases with the interval. -/
theorem attain (N : ℕ) : ∃ A ⊆ Icc 1 N, Erdos186.NonAveraging A ∧
    A.card = Erdos186.F N := by
  obtain ⟨A,hA,he⟩ := exists_mem_eq_sup
    (((Icc 1 N).powerset).filter Erdos186.NonAveraging)
    ⟨∅, by simp [Erdos186.NonAveraging]⟩ Finset.card
  simp only [mem_filter, mem_powerset] at hA
  exact ⟨A,hA.1,hA.2,he.symm⟩

theorem monoF : Monotone Erdos186.F := by
  intro M N h
  obtain ⟨A,hA,ha,he⟩ := attain M
  rw [← he]
  exact Erdos186.card_le_F (hA.trans (Icc_subset_Icc_right h)) ha

/-- The finite lower witness gives both eventual unboundedness and a uniform
one-sided logarithmic estimate, by applying it at the current extremum. -/
theorem lower_log (h : H1) {N : ℕ} (hN : 1 ≤ N) :
    Real.log N ≤ Real.log 7 + 4 * Real.log (Erdos186.F N) := by
  let k := Erdos186.F N
  have hk : 1 ≤ k := by
    have h0 := (h 0).trans (monoF (show (0*(2*0+1)+1)*0^2+2*0+1 ≤ N by omega))
    simpa [k] using h0
  have hsmall : N < (k*(2*k+1)+1)*k^2+2*k+1 := by
    by_contra! hl
    have := (h k).trans (monoF hl)
    change 2*k+1 ≤ k at this
    omega
  have hbound : N ≤ 7*k^4 := by
    have ha : 1 ≤ k^4 := Nat.one_le_pow _ _ hk
    have hb : k ≤ k^4 := by simpa using (Nat.pow_le_pow_right hk (by decide : 1 ≤ 4))
    have hc : k^2 ≤ k^4 := Nat.pow_le_pow_right hk (by decide)
    have hd : k^3 ≤ k^4 := Nat.pow_le_pow_right hk (by decide)
    nlinarith only [hsmall,ha,hb,hc,hd]
  have hl := Real.log_le_log (show 0 < (N:ℝ) by exact_mod_cast hN) (by exact_mod_cast hbound :
    (N:ℝ) ≤ 7*(k:ℝ)^4)
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hl
  simpa [k] using hl

/-- Only dyadic cardinalities are needed. Selecting the largest power of two
below the extremum costs at most log 2 on the logarithmic scale. -/
theorem dyadic_upper (h₁ : H1) (h₂ : H2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      Real.log (Erdos186.F N) ≤ (1 / 4 + ε) * Real.log N + Real.log 2 := by
  obtain ⟨J,hJ⟩ := eventually_atTop.mp (h₂ ε hε)
  let K := 2^(J+1)
  filter_upwards [eventually_ge_atTop ((K*(2*K+1)+1)*K^2+2*K+1)] with N hN
  let m := Erdos186.F N
  let j := Nat.log 2 m
  have hg : 2*K+1 ≤ m := (h₁ K).trans (monoF hN)
  have hK : K ≤ m := by omega
  have hj : J+1 ≤ j := by
    have h := Nat.log_mono_right (b:=2) hK
    simpa [K,j,Nat.log_pow (by decide : 1 < 2)] using h
  have hm : 0 < m := by omega
  have hk : 2^j ≤ m := Nat.pow_log_le_self _ hm.ne'
  have hkt : 2 ≤ 2^j := by
    simpa using (Nat.pow_le_pow_right (by decide : 1 ≤ 2) (show 1 ≤ j by omega))
  obtain ⟨A,hA,good,hcard⟩ := attain N
  obtain ⟨S,hS,hSsize⟩ := exists_subset_card_eq (s:=A) (n:=2^j) (hcard ▸ hk)
  have hsGood : Erdos186.NonAveraging S := by
    intro a ha T hT hn
    exact good a (hS ha) T (hT.trans (erase_subset_erase _ hS)) hn
  obtain ⟨D,P,hDN,hP,h0,hmax,hprim,hcount,hgood⟩ :=
    primitive_model (hS.trans hA) hsGood (by omega)
  have hcount' : P.card = 2^j := hcount.trans hSsize
  have hcrit : Real.log (2^j : ℕ) ≤ (1/4 + ε) * Real.log (D+1 : ℕ) := by
    by_contra! hshort
    obtain ⟨a,ha,T,hT,hn,heq⟩ := hJ j (by omega) D hshort P hP h0 hmax hprim hcount'
    exact hgood a ha T hT hn heq
  have hcrit' : Real.log (2^j : ℕ) ≤ (1/4 + ε) * Real.log N :=
    hcrit.trans (mul_le_mul_of_nonneg_left (Real.log_le_log (by positivity)
      (by exact_mod_cast hDN)) (by positivity))
  have hpow : m < 2^j*2 := by simpa [j,pow_succ] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) m
  have upper := Real.log_le_log (show 0 < (m:ℝ) by exact_mod_cast hm)
    (by exact_mod_cast hpow.le : (m:ℝ) ≤ (2^j : ℕ)* (2:ℝ))
  rw [Real.log_mul (by positivity) (by norm_num)] at upper
  exact upper.trans (by linarith only [hcrit'])

set_option maxRecDepth 100000 in
set_option maxHeartbeats 6000000 in
/-- A Boolean certificate covering every selection of at least eight points
in [0,16] by one of 62 forbidden averages. -/
theorem cover_sixteen (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : Bool) :
    (b0.toNat + b1.toNat + b2.toNat + b3.toNat + b4.toNat + b5.toNat + b6.toNat + b7.toNat + b8.toNat + b9.toNat + b10.toNat + b11.toNat + b12.toNat + b13.toNat + b14.toNat + b15.toNat + b16.toNat ≥ 8) →
    ((b0 && b1 && b2) ||
      (b3 && b4 && b5) ||
      (b6 && b7 && b8) ||
      (b9 && b10 && b11) ||
      (b12 && b13 && b14) ||
      (b14 && b15 && b16) ||
      (b9 && b12 && b15) ||
      (b10 && b13 && b16) ||
      (b1 && b6 && b11) ||
      (b0 && b4 && b8) ||
      (b2 && b5 && b8) ||
      (b3 && b7 && b11) ||
      (b2 && b4 && b6) ||
      (b5 && b7 && b9) ||
      (b0 && b3 && b6) ||
      (b1 && b4 && b7) ||
      (b5 && b10 && b15) ||
      (b8 && b12 && b16) ||
      (b11 && b13 && b15) ||
      (b10 && b12 && b14) ||
      (b3 && b8 && b13) ||
      (b2 && b9 && b16) ||
      (b0 && b7 && b14) ||
      (b1 && b5 && b9) ||
      (b1 && b2 && b3) ||
      (b2 && b7 && b12) ||
      (b4 && b9 && b14) ||
      (b0 && b6 && b12) ||
      (b8 && b11 && b14) ||
      (b1 && b8 && b15) ||
      (b7 && b10 && b13) ||
      (b4 && b10 && b16) ||
      (b11 && b12 && b13) ||
      (b6 && b10 && b14) ||
      (b6 && b11 && b16) ||
      (b1 && b3 && b5) ||
      (b3 && b9 && b15) ||
      (b0 && b2 && b4) ||
      (b5 && b12 && b15 && b16) ||
      (b1 && b7 && b13) ||
      (b5 && b9 && b13) ||
      (b0 && b1 && b4 && b11) ||
      (b1 && b4 && b6 && b13) ||
      (b8 && b9 && b10) ||
      (b10 && b11 && b12) ||
      (b5 && b6 && b7) ||
      (b0 && b8 && b16) ||
      (b3 && b11 && b14 && b16) ||
      (b3 && b6 && b7 && b12) ||
      (b0 && b1 && b3 && b4 && b12) ||
      (b2 && b5 && b6 && b11) ||
      (b5 && b10 && b11 && b14) ||
      (b1 && b2 && b5 && b12) ||
      (b0 && b3 && b5 && b12) ||
      (b0 && b7 && b9 && b12) ||
      (b2 && b8 && b14) ||
      (b0 && b6 && b7 && b15) ||
      (b4 && b11 && b13 && b16) ||
      (b0 && b2 && b3 && b7) ||
      (b0 && b3 && b7 && b12 && b13) ||
      (b3 && b10 && b13 && b14) ||
      (b0 && b3 && b7 && b10 && b15)) = true := by
  cases b0 <;> cases b1 <;> cases b2 <;> cases b3 <;>
    decide +revert +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 2400000 in
/-- Eight non-averaging points need diameter at least seventeen; the bound
is attained by a concrete set. -/
theorem eight_point_threshold :
    (∀ P : Finset ℕ, P ⊆ range 17 → Erdos186.NonAveraging P → P.card ≤ 7) ∧
    Erdos186.NonAveraging {0,1,3,4,13,14,16,17} := by
  constructor
  · intro P hP good
    by_contra! hcard
    have avoid (W : Finset ℕ) (bad : ¬ Erdos186.NonAveraging W) : ¬ W ⊆ P := by
      intro hw
      apply bad
      intro a ha T hT hn
      exact good a (hw ha) T (hT.trans (erase_subset_erase _ hw)) hn
    have hlen : (∑ i ∈ range 17, if i ∈ P then 1 else 0 : ℕ) = P.card := by
      rw [sum_boole]
      have hf : (range 17).filter (· ∈ P) = P := by
        ext i
        exact ⟨fun hi => (mem_filter.mp hi).2, fun hi => mem_filter.mpr ⟨hP hi,hi⟩⟩
      simp [hf]
    have hpop : 8 ≤ (decide (0 ∈ P)).toNat+(decide (1 ∈ P)).toNat+(decide (2 ∈ P)).toNat+(decide (3 ∈ P)).toNat+(decide (4 ∈ P)).toNat+(decide (5 ∈ P)).toNat+(decide (6 ∈ P)).toNat+(decide (7 ∈ P)).toNat+(decide (8 ∈ P)).toNat+(decide (9 ∈ P)).toNat+(decide (10 ∈ P)).toNat+(decide (11 ∈ P)).toNat+(decide (12 ∈ P)).toNat+(decide (13 ∈ P)).toNat+(decide (14 ∈ P)).toNat+(decide (15 ∈ P)).toNat+(decide (16 ∈ P)).toNat := by
      have he : (decide (0 ∈ P)).toNat+(decide (1 ∈ P)).toNat+(decide (2 ∈ P)).toNat+(decide (3 ∈ P)).toNat+(decide (4 ∈ P)).toNat+(decide (5 ∈ P)).toNat+(decide (6 ∈ P)).toNat+(decide (7 ∈ P)).toNat+(decide (8 ∈ P)).toNat+(decide (9 ∈ P)).toNat+(decide (10 ∈ P)).toNat+(decide (11 ∈ P)).toNat+(decide (12 ∈ P)).toNat+(decide (13 ∈ P)).toNat+(decide (14 ∈ P)).toNat+(decide (15 ∈ P)).toNat+(decide (16 ∈ P)).toNat = P.card := by
        have bit (x : ℕ) : (decide (x ∈ P)).toNat = (if x ∈ P then 1 else 0) := by
          by_cases hx : x ∈ P <;> simp [hx]
        simp only [bit]
        rw [sum_range_succ (n := 16)] at hlen
        rw [sum_range_succ (n := 15)] at hlen
        rw [sum_range_succ (n := 14)] at hlen
        rw [sum_range_succ (n := 13)] at hlen
        rw [sum_range_succ (n := 12)] at hlen
        rw [sum_range_succ (n := 11)] at hlen
        rw [sum_range_succ (n := 10)] at hlen
        rw [sum_range_succ (n := 9)] at hlen
        rw [sum_range_succ (n := 8)] at hlen
        rw [sum_range_succ (n := 7)] at hlen
        rw [sum_range_succ (n := 6)] at hlen
        rw [sum_range_succ (n := 5)] at hlen
        rw [sum_range_succ (n := 4)] at hlen
        rw [sum_range_succ (n := 3)] at hlen
        rw [sum_range_succ (n := 2)] at hlen
        rw [sum_range_succ (n := 1)] at hlen
        rw [sum_range_succ (n := 0)] at hlen
        simpa only [sum_range_zero, zero_add] using hlen
      omega
    have covered := cover_sixteen (decide (0 ∈ P)) (decide (1 ∈ P)) (decide (2 ∈ P)) (decide (3 ∈ P)) (decide (4 ∈ P)) (decide (5 ∈ P)) (decide (6 ∈ P)) (decide (7 ∈ P)) (decide (8 ∈ P)) (decide (9 ∈ P)) (decide (10 ∈ P)) (decide (11 ∈ P)) (decide (12 ∈ P)) (decide (13 ∈ P)) (decide (14 ∈ P)) (decide (15 ∈ P)) (decide (16 ∈ P)) hpop
    have c0 := avoid {0,1,2} (by decide)
    have c1 := avoid {3,4,5} (by decide)
    have c2 := avoid {6,7,8} (by decide)
    have c3 := avoid {9,10,11} (by decide)
    have c4 := avoid {12,13,14} (by decide)
    have c5 := avoid {14,15,16} (by decide)
    have c6 := avoid {9,12,15} (by decide)
    have c7 := avoid {10,13,16} (by decide)
    have c8 := avoid {1,6,11} (by decide)
    have c9 := avoid {0,4,8} (by decide)
    have c10 := avoid {2,5,8} (by decide)
    have c11 := avoid {3,7,11} (by decide)
    have c12 := avoid {2,4,6} (by decide)
    have c13 := avoid {5,7,9} (by decide)
    have c14 := avoid {0,3,6} (by decide)
    have c15 := avoid {1,4,7} (by decide)
    have c16 := avoid {5,10,15} (by decide)
    have c17 := avoid {8,12,16} (by decide)
    have c18 := avoid {11,13,15} (by decide)
    have c19 := avoid {10,12,14} (by decide)
    have c20 := avoid {3,8,13} (by decide)
    have c21 := avoid {2,9,16} (by decide)
    have c22 := avoid {0,7,14} (by decide)
    have c23 := avoid {1,5,9} (by decide)
    have c24 := avoid {1,2,3} (by decide)
    have c25 := avoid {2,7,12} (by decide)
    have c26 := avoid {4,9,14} (by decide)
    have c27 := avoid {0,6,12} (by decide)
    have c28 := avoid {8,11,14} (by decide)
    have c29 := avoid {1,8,15} (by decide)
    have c30 := avoid {7,10,13} (by decide)
    have c31 := avoid {4,10,16} (by decide)
    have c32 := avoid {11,12,13} (by decide)
    have c33 := avoid {6,10,14} (by decide)
    have c34 := avoid {6,11,16} (by decide)
    have c35 := avoid {1,3,5} (by decide)
    have c36 := avoid {3,9,15} (by decide)
    have c37 := avoid {0,2,4} (by decide)
    have c38 := avoid {5,12,15,16} (by decide)
    have c39 := avoid {1,7,13} (by decide)
    have c40 := avoid {5,9,13} (by decide)
    have c41 := avoid {0,1,4,11} (by decide)
    have c42 := avoid {1,4,6,13} (by decide)
    have c43 := avoid {8,9,10} (by decide)
    have c44 := avoid {10,11,12} (by decide)
    have c45 := avoid {5,6,7} (by decide)
    have c46 := avoid {0,8,16} (by decide)
    have c47 := avoid {3,11,14,16} (by decide)
    have c48 := avoid {3,6,7,12} (by decide)
    have c49 := avoid {0,1,3,4,12} (by decide)
    have c50 := avoid {2,5,6,11} (by decide)
    have c51 := avoid {5,10,11,14} (by decide)
    have c52 := avoid {1,2,5,12} (by decide)
    have c53 := avoid {0,3,5,12} (by decide)
    have c54 := avoid {0,7,9,12} (by decide)
    have c55 := avoid {2,8,14} (by decide)
    have c56 := avoid {0,6,7,15} (by decide)
    have c57 := avoid {4,11,13,16} (by decide)
    have c58 := avoid {0,2,3,7} (by decide)
    have c59 := avoid {0,3,7,12,13} (by decide)
    have c60 := avoid {3,10,13,14} (by decide)
    have c61 := avoid {0,3,7,10,15} (by decide)
    simp only [insert_subset_iff, singleton_subset_iff] at c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31 c32 c33 c34 c35 c36 c37 c38 c39 c40 c41 c42 c43 c44 c45 c46 c47 c48 c49 c50 c51 c52 c53 c54 c55 c56 c57 c58 c59 c60 c61
    simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, and_assoc] at covered
    simp only [c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17, c18, c19, c20, c21, c22, c23, c24, c25, c26, c27, c28, c29, c30, c31, c32, c33, c34, c35, c36, c37, c38, c39, c40, c41, c42, c43, c44, c45, c46, c47, c48, c49, c50, c51, c52, c53, c54, c55, c56, c57, c58, c59, c60, c61, or_false] at covered
  · decide +kernel

theorem main : H1 → H2 → type_of% @Erdos186.erdos_186 := by
  intro h₁ h₂
  apply Metric.tendsto_nhds.mpr
  intro ε he
  have hlog : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [dyadic_upper h₁ h₂ (ε:=ε/2) (by positivity),
    hlog.eventually_gt_atTop (2*Real.log 2 / ε),
    hlog.eventually_gt_atTop (Real.log 7 / ε), eventually_ge_atTop 2] with N hu hc hd hN
  have hl := lower_log h₁ (show 1 ≤ N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hc' := (div_lt_iff₀ he).mp hc
  have hd' := (div_lt_iff₀ he).mp hd
  rw [Real.dist_eq, abs_lt]
  constructor
  · have hh : 1/4 - ε < Real.log (Erdos186.F N) / Real.log N := by
      apply (lt_div_iff₀ hL).mpr
      nlinarith only [hl,hd',mul_pos he hL]
    linarith only [hh]
  · have hh : Real.log (Erdos186.F N) / Real.log N < 1/4 + ε := by
      apply (div_lt_iff₀ hL).mpr
      nlinarith only [hu,hc']
    linarith only [hh]

end OMA.R_Erdos186_erdos_186_R1
