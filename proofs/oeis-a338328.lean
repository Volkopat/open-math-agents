import OMAStatements.S_oeis_a338328
import Mathlib

/-!
# Coefficients of Hanna's diagonal power series modulo four

Paul D. Hanna's OEIS A338328, published October 24, 2020, determines a
power series A by a different diagonal equation in each degree. We prove
existence and uniqueness over the integers and identify its reduction mod 4
as X+C(X²), where C=X+C² is the shifted Catalan series. Its sparse support
follows directly from binary expansions. For prior Catalan congruences see
Eu, Liu and Yeh, https://doi.org/10.1016/j.ejc.2007.06.019.
Source for the diagonal conditions and the two conjectures:
https://oeis.org/A338328.
-/

namespace Res338
open PowerSeries

/-- Over an arbitrary commutative ring, the first disagreement of two unit-constant
series is multiplied by the exponent on taking powers. -/
theorem first_difference {R : Type*} [CommRing R] {U V : PowerSeries R} (n k : ℕ)
    (hU : constantCoeff U=1) (hV : constantCoeff V=1)
    (h : ∀ j, j<n → coeff j U=coeff j V) :
    coeff n (U^k)-coeff n (V^k) = (k:R)*(coeff n U-coeff n V) := by
  obtain ⟨F,hF⟩ := (X_pow_dvd_iff (φ:=U-V) (n:=n)).mpr (by
    intro j hj; rw [map_sub,h j hj,sub_self])
  let G := ∑ i ∈ Finset.range k, U^i*V^(k-1-i)
  have hG : constantCoeff G=(k:R) := by simp [G,hU,hV]
  have shift (T : PowerSeries R) : coeff n (X^n*T)=constantCoeff T := by
    simpa only [zero_add,coeff_zero_eq_constantCoeff_apply] using coeff_X_pow_mul T n 0
  rw [← map_sub,← map_sub,← geom_sum₂_mul]
  change coeff n (G*(U-V)) = _
  rw [hF,show G*(X^n*F)=X^n*(G*F) by ring,shift,shift,map_mul,hG]

/-- The diagonal conditions determine the series in every coefficient ring in
which multiplication by each defining exponent is injective. -/
theorem unique_of_regular {R : Type*} [CommRing R] {P Q : PowerSeries R}
    (hP0 : coeff 0 P=0) (hQ0 : coeff 0 Q=0)
    (hP : ∀ n : ℕ, 0<n → coeff n ((1+(n:PowerSeries R)*X-P)^(2*n-1))=0)
    (hQ : ∀ n : ℕ, 0<n → coeff n ((1+(n:PowerSeries R)*X-Q)^(2*n-1))=0)
    (hu : ∀ n : ℕ, 0<n → ∀ z : R, ((2*n-1 : ℕ):R)*z=0 → z=0) : P=Q := by
  rw [coeff_zero_eq_constantCoeff_apply] at hP0 hQ0
  ext n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simpa only [coeff_zero_eq_constantCoeff_apply] using hP0.trans hQ0.symm
    · have diff := first_difference (U:=1+(n:PowerSeries R)*X-P)
          (V:=1+(n:PowerSeries R)*X-Q) n (2*n-1)
          (by simp [hP0])
          (by simp [hQ0])
          (by intro j hj; simp only [map_sub,ih j hj])
      rw [hP n hn,hQ n hn,sub_self] at diff
      have z := hu n hn _ diff.symm
      simp only [map_sub] at z
      linear_combination -z

theorem unique {R : Type*} [CommRing R] {P Q : PowerSeries R}
    (hP0 : coeff 0 P=0) (hQ0 : coeff 0 Q=0)
    (hP : ∀ n : ℕ, 0<n → coeff n ((1+(n:PowerSeries R)*X-P)^(2*n-1))=0)
    (hQ : ∀ n : ℕ, 0<n → coeff n ((1+(n:PowerSeries R)*X-Q)^(2*n-1))=0)
    (hu : ∀ n : ℕ, 0<n → IsUnit ((2*n-1 : ℕ):R)) : P=Q := by
  apply unique_of_regular hP0 hQ0 hP hQ
  intro n hn z hz
  apply (hu n hn).mul_left_cancel
  simpa using hz

theorem odd_unit_four (n : ℕ) (hn : 0<n) : IsUnit ((2*n-1 : ℕ):ZMod 4) := by
  rw [ZMod.isUnit_iff_coprime]
  change Nat.Coprime _ (2^2)
  rw [Nat.coprime_pow_right_iff (by decide : 0<2),Nat.coprime_comm,Nat.Prime.coprime_iff_not_dvd Nat.prime_two]
  omega

theorem map_conditions {A : PowerSeries ℤ}
    (hA : ∀ n : ℕ, 0<n → coeff n ((1+(n:PowerSeries ℤ)*X-A)^(2*n-1))=0)
    (q n : ℕ) (hn : 0<n) :
    coeff n ((1+(n:PowerSeries (ZMod q))*X-A.map (Int.castRingHom (ZMod q)))^(2*n-1))=0 := by
  have h := congrArg (Int.castRingHom (ZMod q)) (hA n hn)
  rw [← coeff_map] at h
  simpa using h

end Res338

namespace Res338
open PowerSeries

/-- The formal power rule ensures that solving each integral coefficient
equation involves exact division by the odd exponent. -/
theorem diagonal_divides (U : PowerSeries ℤ) (n : ℕ) (hn : 0<n) :
    ((2*n-1 : ℕ) : ℤ) ∣ coeff n (U^(2*n-1)) := by
  let k := 2*n-1
  have hk : (k:ℤ) = 2*(n:ℤ)-1 := by dsimp [k]; omega
  have hc : IsCoprime (k:ℤ) (n:ℤ) := ⟨-1,2,by rw [hk]; ring⟩
  apply hc.dvd_of_dvd_mul_right
  refine ⟨coeff (n-1) (U^(k-1)*derivative ℤ U), ?_⟩
  have d := congrArg (coeff (n-1)) (derivative_pow U k)
  rw [coeff_derivative,show n-1+1=n by omega] at d
  rw [mul_assoc,show (k:PowerSeries ℤ)=C (k:ℤ) by simp,coeff_C_mul] at d
  have hc' : ((n-1:ℕ):ℤ)+1=n := by omega
  simpa only [hc',k] using d

noncomputable def integralCoeff (n : ℕ) : ℤ :=
  if hn : n=0 then 0 else
  let T : PowerSeries ℤ := mk fun j => if _h : j<n then integralCoeff j else 0
  coeff n ((1+(n:PowerSeries ℤ)*X-T)^(2*n-1)) / ((2*n-1 : ℕ):ℤ)
termination_by n

private theorem integral_zero : integralCoeff 0=0 := by rw [integralCoeff]; simp

/-- The defining equations have exactly one solution over the integers. -/
theorem exists_unique_integral : ∃! A : PowerSeries ℤ,
    coeff 0 A=0 ∧ ∀ n : ℕ, 0<n → coeff n ((1+(n:PowerSeries ℤ)*X-A)^(2*n-1))=0 := by
  let A : PowerSeries ℤ := mk integralCoeff
  have hA0 : coeff 0 A=0 := by simpa [A] using integral_zero
  have hA (n : ℕ) (hn : 0<n) :
      coeff n ((1+(n:PowerSeries ℤ)*X-A)^(2*n-1))=0 := by
    let T : PowerSeries ℤ := mk fun j => if j<n then integralCoeff j else 0
    let U : PowerSeries ℤ := 1+(n:PowerSeries ℤ)*X-A
    let V : PowerSeries ℤ := 1+(n:PowerSeries ℤ)*X-T
    let k := 2*n-1
    have hd : (k:ℤ) ∣ coeff n (V^k) := diagonal_divides V n hn
    have hrec : integralCoeff n = coeff n (V^k) / (k:ℤ) := by
      rw [integralCoeff,dif_neg hn.ne']; simp only [dite_eq_ite]; rfl
    have hz : constantCoeff A=0 := by simpa only [coeff_zero_eq_constantCoeff_apply] using hA0
    have ht : constantCoeff T=0 := by simp [T,hn,integral_zero]
    have h := first_difference (U:=U) (V:=V) n k (by simp [U,hz]) (by simp [V,ht])
      (by intro j hj; simp [U,V,A,T,hj])
    have diff : coeff n U-coeff n V = - integralCoeff n := by
      simp [U,V,A,T]
    rw [diff,hrec,mul_neg,Int.mul_ediv_cancel' hd] at h
    change coeff n (U^k)=0
    omega
  refine ⟨A,⟨hA0,hA⟩,?_⟩
  rintro B ⟨hB0,hB⟩
  apply unique_of_regular hB0 hA0 hB hA
  intro n hn z hz
  rcases mul_eq_zero.mp hz with h | h
  · omega
  · exact h

end Res338

namespace Res338
open PowerSeries
open scoped Classical

theorem pow_pair_sorted {i j k l : ℕ} (hij : i≤j) (hkl : k≤l)
    (he : 2^i+2^j = 2^k+2^l) : i=k ∧ j=l := by
  have sep {a b c d : ℕ} (hab : a≤b) (hbd : b<d) : 2^a+2^b < 2^c+2^d := by
    have h₁ := Nat.pow_le_pow_right (by decide : 0<2) hab
    have h₂ := Nat.pow_le_pow_right (by decide : 0<2) (show b+1≤d by omega)
    rw [pow_succ] at h₂
    have h₃ : 0<2^c := by positivity
    omega
  have h : j=l := by
    rcases lt_trichotomy j l with hj|hj|hj
    · have := sep (c:=k) hij hj; omega
    · exact hj
    · have := sep (c:=i) hkl hj; omega
  subst l
  exact ⟨Nat.pow_right_injective (by decide : 2≤2) (Nat.add_right_cancel he),rfl⟩

theorem pow_ne_sum {i j k : ℕ} (hij : i<j) : 2^k ≠ 2^i+2^j := by
  intro h
  cases k with
  | zero =>
    have : 0<2^i := by positivity
    have : 0<2^j := by positivity
    simp only [pow_zero] at h
    omega
  | succ k =>
    have hh : 2^k+2^k=2^i+2^j := by simpa only [pow_succ, Nat.mul_two] using h
    obtain ⟨h₁,h₂⟩ := pow_pair_sorted le_rfl hij.le hh
    omega

theorem pow_pair_any {a b i j : ℕ} (hij : i≤j)
    (he : 2^a+2^b=2^i+2^j) : (a=i ∧ b=j) ∨ (a=j ∧ b=i) := by
  rcases le_total a b with hab|hab
  · exact Or.inl (pow_pair_sorted hab hij he)
  · have h := pow_pair_sorted hab hij (by rwa [add_comm (2^b) (2^a)])
    exact Or.inr ⟨h.2,h.1⟩

theorem power_decomposition_count (n : ℕ) :
    ((Finset.HasAntidiagonal.antidiagonal n).filter fun z : ℕ × ℕ =>
      (∃ i : ℕ, z.1=2^i) ∧ (∃ j : ℕ, z.2=2^j)).card + (if n=1 then 1 else 0) =
      if (∃ k : ℕ, n=2^k) then 1 else if (∃ i j : ℕ, i<j ∧ n=2^i+2^j) then 2 else 0 := by
  classical
  let S := (Finset.HasAntidiagonal.antidiagonal n).filter fun z : ℕ × ℕ =>
      (∃ i : ℕ, z.1=2^i) ∧ (∃ j : ℕ, z.2=2^j)
  have mem (u v : ℕ) : (u,v)∈S ↔ u+v=n ∧ (∃ i : ℕ, u=2^i) ∧ (∃ j : ℕ, v=2^j) := by
    simp [S, Finset.HasAntidiagonal.mem_antidiagonal]
  have pair {i j : ℕ} (hij : i≤j) (h : n=2^i+2^j) :
      S = {(2^i,2^j),(2^j,2^i)} := by
    ext ⟨u,v⟩
    rw [mem,Finset.mem_insert,Finset.mem_singleton]
    constructor
    · rintro ⟨huv,⟨a,rfl⟩,⟨b,rfl⟩⟩
      rcases pow_pair_any hij (huv.trans h) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp
    · rintro (he|he) <;> rcases Prod.mk.inj he with ⟨rfl,rfl⟩
      · exact ⟨h.symm,⟨i,rfl⟩,⟨j,rfl⟩⟩
      · exact ⟨by rw [add_comm,h],⟨j,rfl⟩,⟨i,rfl⟩⟩
  change S.card + _ = _
  by_cases hp : ∃ k : ℕ, n=2^k
  · rw [if_pos hp]
    obtain ⟨k,hk⟩ := hp
    cases k with
    | zero =>
      have hn : n=1 := by simpa using hk
      have he : S=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        rintro ⟨_,_⟩ hs
        obtain ⟨h,⟨i,rfl⟩,⟨j,rfl⟩⟩ := (mem _ _).mp hs
        have : 0<2^i := by positivity
        have : 0<2^j := by positivity
        omega
      simp [he,hn]
    | succ k =>
      have h : n=2^k+2^k := by simpa only [pow_succ, Nat.mul_two] using hk
      have : n≠1 := by
        have : 0<2^k := by positivity
        omega
      simp [pair le_rfl h,this]
  · rw [if_neg hp]
    have hn : n≠1 := fun h => hp ⟨0,by simpa using h⟩
    rw [if_neg hn,add_zero]
    by_cases hq : ∃ i j : ℕ, i<j ∧ n=2^i+2^j
    · rw [if_pos hq]
      obtain ⟨i,j,hij,h⟩ := hq
      have hne : ((2:ℕ)^i, (2:ℕ)^j) ≠ (2^j,2^i) := by
        intro he
        exact hij.ne (Nat.pow_right_injective (by decide : 2≤2) (Prod.mk.inj he).1)
      simp [pair hij.le h,hne]
    · rw [if_neg hq]
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨_,_⟩ hs
      obtain ⟨h,⟨i,rfl⟩,⟨j,rfl⟩⟩ := (mem _ _).mp hs
      rcases lt_trichotomy i j with hij|rfl|hji
      · exact hq ⟨i,j,hij,h.symm⟩
      · exact hp ⟨i+1,by simpa only [pow_succ,Nat.mul_two] using h.symm⟩
      · exact hq ⟨j,i,hji,by rw [←h,add_comm]⟩

/-- The shifted Catalan series modulo four, constructed directly from its binary support. -/
theorem catalan_model : ∃ C : PowerSeries (ZMod 4), C=X+C^2 ∧
    ∀ n : ℕ, coeff n C = if (∃ k : ℕ, n=2^k) then 1 else
      if (∃ i j : ℕ, i<j ∧ n=2^i+2^j) then 2 else 0 := by
  classical
  let P (n : ℕ) := ∃ k : ℕ, n=2^k
  let Q (n : ℕ) := ∃ i j : ℕ, i<j ∧ n=2^i+2^j
  let D := PowerSeries.mk (fun n => if P n then (1:ZMod 4) else 0)
  let E := PowerSeries.mk (fun n => if Q n then (1:ZMod 4) else 0)
  let C := D+E+E
  have hc (n : ℕ) : coeff n C = if P n then 1 else if Q n then 2 else 0 := by
    simp only [C,D,E,map_add,coeff_mk]
    by_cases isP : P n
    · have notQ : ¬Q n := by
        obtain ⟨k,hk⟩ := isP
        rintro ⟨i,j,hij,h⟩
        exact pow_ne_sum hij (hk.symm.trans h)
      simp [isP,notQ]
    · by_cases isQ : Q n <;> simp [isP,isQ]
      decide
  have c4 : (4 : PowerSeries (ZMod 4))=0 := by
    calc (4 : PowerSeries (ZMod 4)) = PowerSeries.C ((4:ℕ):ZMod 4) := (map_natCast _ 4).symm
         _ = 0 := by rw [show ((4:ℕ):ZMod 4)=0 by decide, map_zero]
  have csq : C^2 = D^2 := by
    calc C^2 = D^2+4*(D*E+E^2) := by dsimp only [C]; ring
         _ = D^2 := by rw [c4,zero_mul,add_zero]
  refine ⟨C,?_,hc⟩
  ext n
  rw [hc n,csq,map_add,coeff_X,pow_two,coeff_mul]
  let S := (Finset.HasAntidiagonal.antidiagonal n).filter fun z : ℕ × ℕ => P z.1 ∧ P z.2
  have cnt : ∑ z ∈ Finset.HasAntidiagonal.antidiagonal n, coeff z.1 D*coeff z.2 D = (S.card:ZMod 4) := by
    calc _ = ∑ z ∈ Finset.HasAntidiagonal.antidiagonal n, if P z.1 ∧ P z.2 then (1:ZMod 4) else 0 := by
               apply Finset.sum_congr rfl
               intro z hz
               by_cases h₁ : P z.1 <;> by_cases h₂ : P z.2 <;> simp [D,h₁,h₂]
         _ = _ := by rw [←Finset.sum_filter]; simp [S]
  rw [cnt]
  have hcount : S.card+(if n=1 then 1 else 0) = if P n then 1 else if Q n then 2 else 0 :=
    power_decomposition_count n
  have hh := congrArg (fun v : ℕ => (v:ZMod 4)) hcount.symm
  by_cases hp : P n <;> by_cases hq : Q n
  all_goals
    simp only [hp,hq,if_true,if_false] at hh ⊢
    by_cases hn : n=1 <;>
      simpa only [hn,if_true,if_false,Nat.cast_zero,Nat.cast_one,Nat.cast_add,
        Nat.cast_ofNat,add_comm] using hh

end Res338

namespace Res338
open PowerSeries
variable {R : Type*} [CommRing R]

lemma odd_support_one (d : ℕ) (hd : d % 2 = 1) :
    coeff d (1 : PowerSeries R) = 0 := by
  rw [coeff_one, if_neg (by omega)]

lemma odd_support_sub {P Q : PowerSeries R}
    (hP : ∀ d : ℕ, d % 2 = 1 → coeff d P = 0)
    (hQ : ∀ d : ℕ, d % 2 = 1 → coeff d Q = 0)
    (d : ℕ) (hd : d % 2 = 1) : coeff d (P-Q) = 0 := by
  simp [hP d hd, hQ d hd]

lemma odd_support_mul {P Q : PowerSeries R}
    (hP : ∀ d : ℕ, d % 2 = 1 → coeff d P = 0)
    (hQ : ∀ d : ℕ, d % 2 = 1 → coeff d Q = 0)
    (d : ℕ) (hd : d % 2 = 1) : coeff d (P*Q) = 0 := by
  rw [coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rcases (show ij.1 % 2 = 1 ∨ ij.2 % 2 = 1 by omega) with h | h
  · simp [hP _ h]
  · simp [hQ _ h]

lemma odd_support_pow {P : PowerSeries R}
    (hP : ∀ d : ℕ, d % 2 = 1 → coeff d P = 0) (k : ℕ) :
    ∀ d : ℕ, d % 2 = 1 → coeff d (P^k) = 0 := by
  induction k with
  | zero => simpa only [pow_zero] using (odd_support_one (R := R))
  | succ k ih => simpa only [pow_succ] using odd_support_mul ih hP

end Res338

namespace Res338
open PowerSeries
open Finset.HasAntidiagonal

lemma four_series : (4 : PowerSeries (ZMod 4)) = 0 := by
  simpa only [map_ofNat, map_zero] using (congrArg (PowerSeries.C (R := ZMod 4)) (show (4 : ZMod 4) = 0 by decide))

lemma square_add_twoX4 (P : PowerSeries (ZMod 4)) :
    (P + 2*X)^2 = P^2 := by
  calc
    _ = P^2 + 4*(P*X + X^2) := by ring
    _ = P^2 := by rw [four_series]; ring

lemma twice_coeff_square {P : PowerSeries (ZMod 4)}
    (hP : ∀ d : ℕ, d%2=1 → coeff d P=0) (m : ℕ) (hm : m%4=2) :
    2 * coeff m (P^2) = 0 := by
  let f (ij : ℕ × ℕ) : ZMod 4 :=
    if ij.1 < ij.2 then coeff ij.1 P * coeff ij.2 P else 0
  have split : ∀ ij ∈ antidiagonal m,
      coeff ij.1 P * coeff ij.2 P = f ij + f ij.swap := by
    rintro ⟨i,j⟩ hij
    have hh : i+j=m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rcases lt_trichotomy i j with h | h | h
    · simp [f,h,h.asymm]
    · subst j
      have ho : i%2=1 := by omega
      simp [f,hP i ho]
    · simp [f,h,h.asymm,mul_comm]
  rw [pow_two,coeff_mul,Finset.sum_congr rfl split,Finset.sum_add_distrib,
    Finset.Nat.sum_antidiagonal_swap (f := f)]
  generalize (∑ ij ∈ antidiagonal m, f ij) = z
  fin_cases z <;> decide

lemma odd_diagonal (H : PowerSeries (ZMod 4))
    (hEven : ∀ d : ℕ, d%2=1 → coeff d H=0) (n : ℕ) (hn : n%2=1) :
    coeff n ((1+(n:PowerSeries (ZMod 4))*X-(X+H))^(2*n-1))=0 := by
  let B : PowerSeries (ZMod 4) := 1-H
  have hB : ∀ d : ℕ, d%2=1 → coeff d B=0 := odd_support_sub odd_support_one hEven
  by_cases hm : n%4=1
  · have hcast : (n : PowerSeries (ZMod 4))=1 := by
      calc
        _ = ((4*(n/4)+1 : ℕ) : PowerSeries (ZMod 4)) := by congr 1; omega
        _ = 1 := by push_cast; rw [four_series]; ring
    have he : 1+(n:PowerSeries (ZMod 4))*X-(X+H)=B := by rw [hcast]; dsimp [B]; ring
    rw [he]
    exact odd_support_pow hB _ n hn
  · have hm3 : n%4=3 := by omega
    have hcast : (n : PowerSeries (ZMod 4))=3 := by
      calc
        _ = ((4*(n/4)+3 : ℕ) : PowerSeries (ZMod 4)) := by congr 1; omega
        _ = 3 := by push_cast; rw [four_series]; ring
    have he : 1+(n:PowerSeries (ZMod 4))*X-(X+H)=B+2*X := by rw [hcast]; dsimp [B]; ring
    have hp : 2*n-1=2*(n-1)+1 := by omega
    have expand : (B+2*X)^(2*n-1)=B^(2*n-1)+X*(B^(n-1))^2+X*(B^(n-1))^2 := by
      rw [hp, pow_succ _ (2*(n-1)), pow_succ B (2*(n-1)), pow_mul, square_add_twoX4, pow_mul B, ← pow_mul, Nat.mul_comm 2 (n-1), pow_mul]
      ring
    rw [he,expand,map_add,map_add,odd_support_pow hB _ n hn,zero_add]
    have succ : n=n-1+1 := by omega
    have shift : coeff n (X*(B^(n-1))^2) = coeff (n-1) ((B^(n-1))^2) := by
      conv_lhs => arg 1; rw [succ]
      exact coeff_succ_X_mul _ _
    rw [shift,← two_mul]
    exact twice_coeff_square (odd_support_pow hB _) _ (by omega)

end Res338

namespace Res338
open PowerSeries

/-- The divided differences of the roots of T²−T+X² are polynomials of degree
strictly smaller than their index, by the second-order root recurrence. -/
theorem divided_difference_cutoff {R : Type*} [CommRing R] (B H : PowerSeries R)
    (s : B + H = 1) (p : B*H = X^2) (n : ℕ) :
    ∃ F : PowerSeries R, (B-H)*F = B^n-H^n ∧ ∀ d ≥ n, coeff d F = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => exact ⟨0, by simp, by simp⟩
  | one =>
    refine ⟨1, by simp, fun d hd => ?_⟩
    rw [coeff_one,if_neg (by omega)]
  | more n h₀ h₁ =>
    obtain ⟨U,hU,cU⟩ := h₀
    obtain ⟨V,hV,cV⟩ := h₁
    refine ⟨V-X^2*U,?_,fun d hd => ?_⟩
    · calc
        (B-H)*(V-X^2*U) = (B+H)*((B-H)*V) - (B*H)*((B-H)*U) := by rw [s,p]; ring
        _ = B^(n+2)-H^(n+2) := by rw [hV,hU]; ring
    · rw [map_sub,coeff_X_pow_mul',if_pos (by omega),cV d (by omega),cU _ (by omega),sub_zero]

theorem even_diagonal_aux (H : PowerSeries (ZMod 4)) (hH : H=X^2+H^2)
    (h0 : coeff 0 H=0) (h1 : coeff 1 H=0)
    (hB : ∀ e d : ℕ, d%2=1 → coeff d ((1-H)^e)=0)
    (n : ℕ) (hn : 0<n) (he : n%2=0) :
    coeff n ((1+(n:PowerSeries (ZMod 4))*X-(X+H))^(2*n-1))=0 := by
  let B := 1-H
  have s : B+H=1 := by dsimp [B]; ring
  have p : B*H=X^2 := by dsimp [B]; linear_combination hH
  have p' : B^2+X^2=B := by linear_combination B*s + p.symm
  have four : (4:PowerSeries (ZMod 4))=0 := by
    simpa only [map_ofNat,map_zero] using congrArg (C (R := ZMod 4)) (show (4:ZMod 4)=0 by decide)
  obtain ⟨k,hk⟩ : ∃ k : ℕ, n=2*k+2 := ⟨n/2-1,by omega⟩
  let u : ZMod 4 := 2*k+1
  let U : PowerSeries (ZMod 4) := C u
  have hu : U^2=1 := by
    change (C u)^2=1
    rw [← map_pow]
    have z : ∀ i : ZMod 4, (2*i+1)^2=1 := by decide
    rw [z k,map_one]
  have hcast : 1+(n:PowerSeries (ZMod 4))*X-(X+H) = B+U*X := by
    rw [hk]
    simp only [B,U,u,map_add,map_mul,map_natCast,map_one,map_ofNat,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  let V := 1+2*(U*X)
  have vsq : V^2=1 := by
    dsimp [V]
    linear_combination ((U*X)+(U*X)^2)*four
  have sq : (B+U*X)^2=B*V := by
    dsimp [V]
    linear_combination p' + X^2*hu
  have ve : V^(n-1)=V := by
    rw [show n-1=2*k+1 by omega,pow_succ,pow_mul,vsq,one_pow,one_mul]
  have bpow : B^(n-1)*B=B^n := by rw [← pow_succ,show n-1+1=n by omega]
  have expr : (B+U*X)^(2*n-1) = B^n*(1+2*H) +
        (B^(n-1)*C u + B^n*C (2*u))*X := by
    rw [show 2*n-1=2*(n-1)+1 by omega,pow_succ,pow_mul,sq,mul_pow,ve]
    simp only [map_mul,map_ofNat]
    dsimp only [V]
    change B^(n-1)*(1+2*(U*X))*(B+U*X) =
      B^n*(1+2*H)+(B^(n-1)*U+B^n*(2*U))*X
    rw [← bpow]
    linear_combination (2*B^(n-1)*X^2)*hu - (2*B^(n-1))*p
  obtain ⟨F,hF,cut⟩ := divided_difference_cutoff B H s p n
  have inv : (B-H)*(1+2*H)=1 := by
    dsimp [B]
    linear_combination -H^2*four
  have decomp : B^n*(1+2*H) = F+H^n*(1+2*H) := by
    linear_combination (1+2*H)*hF.symm + F*inv
  have dv : X^2 ∣ H := X_pow_dvd_iff.mpr (fun d hd => by
    interval_cases d <;> assumption)
  obtain ⟨J,hJ⟩ := dv
  have tail : coeff n (H^n*(1+2*H)) = 0 := by
    have hw : H^n = X^(2*n)*J^n := by conv_lhs => rw [hJ,mul_pow,← pow_mul]
    rw [hw,mul_assoc,coeff_X_pow_mul',if_neg (by omega)]
  rw [hcast,expr,map_add,decomp,map_add,cut n le_rfl,tail,zero_add,zero_add]
  obtain ⟨d,hd⟩ : ∃ d, n=d+1 := ⟨n-1,by omega⟩
  rw [hd,coeff_succ_mul_X,map_add,coeff_mul_C,coeff_mul_C]
  have hodd : d%2=1 := by omega
  rw [show coeff d (B^(d+1-1))=0 from hB _ _ hodd,
      show coeff d (B^(d+1))=0 from hB _ _ hodd,zero_mul,zero_mul,add_zero]

end Res338

namespace Res338
open PowerSeries

theorem even_diagonal (H : PowerSeries (ZMod 4)) (hH : H=X^2+H^2)
    (h0 : coeff 0 H=0) (hEven : ∀ d : ℕ, d%2=1 → coeff d H=0)
    (n : ℕ) (hn : 0<n) (he : n%2=0) :
    coeff n ((1+(n:PowerSeries (ZMod 4))*X-(X+H))^(2*n-1))=0 :=
  even_diagonal_aux H hH h0 (hEven 1 rfl)
    (odd_support_pow (odd_support_sub odd_support_one hEven)) n hn he

end Res338

namespace Res338
open PowerSeries
open scoped Classical

private theorem double_power (m : ℕ) :
    (∃ k : ℕ, 2*m=2^k) ↔ ∃ k : ℕ, m=2^k := by
  constructor
  · rintro ⟨k,h⟩
    cases k with
    | zero => simp at h
    | succ k => exact ⟨k,by rw [pow_succ] at h; omega⟩
  · rintro ⟨k,rfl⟩
    exact ⟨k+1, by rw [pow_succ,Nat.mul_comm]⟩

private theorem odd_power (n : ℕ) (hn : n%2=1) :
    (∃ k : ℕ, n=2^k) ↔ n=1 := by
  constructor
  · rintro ⟨k,rfl⟩
    cases k with
    | zero => rfl
    | succ k => rw [pow_succ] at hn; omega
  · rintro rfl
    exact ⟨0,rfl⟩

private theorem residue_tests (z : ℤ) (p q : Prop) (disj : p → ¬q)
    (h : (z : ZMod 4) = if p then 1 else if q then 2 else 0) :
    (Odd z ↔ p) ∧ (z ≡ 2 [ZMOD 4] ↔ q) := by
  classical
  have modcast (j : ℤ) (e : (z:ZMod 4)=(j:ZMod 4)) : z%4=j%4 :=
    (ZMod.intCast_eq_intCast_iff' z j 4).mp e
  rw [Int.odd_iff,Int.ModEq]
  by_cases hp : p
  · have hq := disj hp
    simp [hp,hq] at h ⊢
    have hz := modcast 1 (by simpa using h)
    omega
  · by_cases hq : q
    · simp [hp,hq] at h ⊢
      have hz := modcast 2 (by simpa using h)
      omega
    · simp [hp,hq] at h ⊢
      have hz := modcast 0 (by simpa using h)
      omega

/-- Expand the Catalan model at X² and supply the exceptional first term X. -/
theorem transport {A : PowerSeries ℤ} {F : PowerSeries (ZMod 4)}
    (hF : ∀ m : ℕ, coeff m F =
      if (∃ k : ℕ, m=2^k) then 1 else
      if (∃ i j : ℕ, i<j ∧ m=2^i+2^j) then 2 else 0)
    (hd : ∀ {i j k : ℕ}, i<j → 2^k ≠ 2^i+2^j)
    (hModel : A.map (Int.castRingHom (ZMod 4)) = X+expand 2 (by decide) F)
    (n : ℕ) :
    (Odd (coeff n A) ↔ ∃ k : ℕ, n=2^k) ∧
    (coeff n A ≡ 2 [ZMOD 4] ↔ ∃ i j : ℕ, i<j ∧ n=2*(2^i+2^j)) := by
  classical
  have atn := congrArg (coeff n) hModel
  simp only [coeff_map,map_add,coeff_X] at atn
  change ((coeff n A : ℤ) : ZMod 4) = _ at atn
  apply residue_tests
  · rintro ⟨k,hk⟩ ⟨i,j,hij,hn⟩
    have hp := (double_power (2^i+2^j)).mp ⟨k,hn.symm.trans hk⟩
    obtain ⟨l,hl⟩ := hp
    exact hd hij hl.symm
  · by_cases he : 2 ∣ n
    · obtain ⟨m,rfl⟩ := he
      rw [coeff_expand_mul,hF] at atn
      have hq : (∃ i j : ℕ, i<j ∧ 2*m=2*(2^i+2^j)) ↔
        (∃ i j : ℕ, i<j ∧ m=2^i+2^j) := by simp
      simp only [if_neg (by omega : 2*m≠1),zero_add] at atn
      simp only [double_power,hq]
      split_ifs at * <;> assumption
    · have ho : n%2=1 := by omega
      have hq : ¬∃ i j : ℕ, i<j ∧ n=2*(2^i+2^j) := by
        rintro ⟨i,j,_,h⟩; exact he ⟨_,h⟩
      rw [coeff_expand_of_not_dvd _ _ _ he,add_zero] at atn
      simpa [odd_power n ho,hq] using atn

end Res338

open PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a338328.main := by
  classical
  intro A hA0 hA n _
  obtain ⟨F,hF,hc⟩ := Res338.catalan_model
  let H := expand 2 (by decide) F
  have hH : H=X^2+H^2 := by
    have hx : expand 2 (by decide) (X : PowerSeries (ZMod 4))=X^2 := PowerSeries.expand_X 2 (by decide)
    simpa only [map_add, map_pow,hx,H] using congrArg (expand 2 (by decide)) hF
  have h0F : coeff 0 F=0 := by
    rw [hc]
    have h1 : ¬∃ k : ℕ, 0=2^k := by
      rintro ⟨k,h⟩
      exact (Nat.pow_pos (by decide : 0<2)).ne h
    have h2 : ¬∃ i j : ℕ, i<j ∧ 0=2^i+2^j := by
      rintro ⟨i,j,_,h⟩
      exact (show 0 < (2^i+2^j : ℕ) by positivity).ne h
    simp [h1,h2]
  have h0 : coeff 0 H=0 := by simpa [H,coeff_zero_eq_constantCoeff_apply] using h0F
  have he (d : ℕ) (hd : d%2=1) : coeff d H=0 :=
    coeff_expand_of_not_dvd 2 (by decide) F (by omega)
  refine Res338.transport hc Res338.pow_ne_sum ?_ n
  change A.map (Int.castRingHom (ZMod 4))=X+H
  apply Res338.unique
  · simp [coeff_map,hA0]
  · rw [map_add,coeff_X,h0]; decide
  · exact fun m hm => Res338.map_conditions hA 4 m hm
  · intro m hm
    rcases Nat.mod_two_eq_zero_or_one m with hm'|hm'
    · exact Res338.even_diagonal H hH h0 he m hm hm'
    · exact Res338.odd_diagonal H he m hm'
  · exact Res338.odd_unit_four
