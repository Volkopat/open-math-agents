import OMAReductions.R_BealConjecture_beal_conjecture_R2
import Mathlib

-- Credit: @ubuwaits

/-!
# Power-of-two gaps and the exponents three and twenty-three

Reduce both odd-base exponents to four or an odd prime. In the two mixed
orientations with exponents three and twenty-three, change signs to put
the power of two on the right. The cubic descent bounds its exponent.
For a square odd summand, factorization in ℤ[√−2] and the Gaussian integers
forces 6 ∣ k, 3 ∣ b and a prime output exponent congruent to 7 modulo 8.
Pell equations at indices 7 and 23 force this prime above 30. The remaining
case produces a nondegenerate Lucas pair with the prime-index term −1.
The signed cubic descent also rules out a cube and a square in either order
among the two odd terms, including powers present in the bases themselves.
The large-index theorem of Bilu, Hanrot and Voutier (2001, Theorem 1.4)
would exclude this case, as in Arif and Abu Muriefah (2001).
The odd-k square classification is due to J. H. E. Cohn (1992). Maohua Le
(Chinese Science Bulletin 42 (1997), 1515–1517) excluded the residual
even-k square case. The restrictions used here are proved below.
-/

namespace OMA.R_BealConjecture_beal_conjecture_R2_H2_R1

open OMA.R_BealConjecture_beal_conjecture_R2

/-- The other normalized pairs, with restrictions on a square in the odd summand. -/
def H1 : Prop :=
  ∀ {b c p r k : ℕ}, b%2=1 → c%2=1 → b.Coprime c → p.Coprime r →
    (p=4 ∨ (p.Prime ∧ 2<p)) → (r=4 ∨ (r.Prime ∧ 2<r)) → 2<k →
    (k%2=1 ∨ r%2=1) → ((Odd p ∧ ¬IsSquare b) ∨ (6 ∣ k ∧ r.Prime ∧ 30 < r ∧ r%8=7 ∧ 3 ∣ b ∧
      ∃ P : ℤ, ∃ U : ℕ → ℤ, 1<(c:ℤ) ∧ IsCoprime P (c:ℤ) ∧
        (¬(c:ℤ)∣P^2) ∧ P^2<4*(c:ℤ) ∧ U 0=0 ∧ U 1=1 ∧
        (∀ j, U (j+2)=P*U (j+1)-(c:ℤ)*U j) ∧ U r= -1)) →
    (∀ d u : ℕ, b^p=d^3 → c^r≠u^2) → (∀ u d : ℕ, b^p=u^2 → c^r≠d^3) →
    (p≠3 ∨ r≠23) → (p≠23 ∨ r≠3) → 2^k+b^p ≠ c^r

/-- The two generalized Fermat equations with a repeated exponent. -/
def H2 : Prop :=
  ∀ {X Y Z : ℤ}, X≠0 → Y≠0 → Z≠0 → IsCoprime X Y →
    X^3+Y^3 ≠ Z^23 ∧ X^23+Y^23 ≠ Z^3

/-- The residual coefficient-two equation at a positive power of eight. -/
def H3 : Prop :=
  ∀ {Y Z : ℤ} {t : ℕ}, 0<t → Odd Y → Odd Z → 2*((2:ℤ)^(3*t))^23 + Y^23 ≠ Z^3

/-- Signed cubic descent at a 23rd power and at a square. The latter gives
all odd representations by a signed cube and a square above exponent two. -/
def H4 : Prop :=
  ∀ {a b : ℤ} {k : ℕ},
    (IsCoprime a b → a^3+b^23=(2:ℤ)^k → 3 ∣ k ∨ 23 ∣ k ∨ k%69=1) ∧
    (Odd a → Odd b → 2<k → a^3+b^2=(2:ℤ)^k →
      (a=7 ∧ b.natAbs=13 ∧ k=9) ∨ (a= -1 ∧ b.natAbs=3 ∧ k=3) ∨ (a= -17 ∧ b.natAbs=71 ∧ k=7))

namespace BealQuadratic

open Zsqrtd

private theorem rounded_square (a : ℤ) (m : ℕ) (hm : 0 < m) :
    4*(a-(m:ℤ)*a.bdiv m)^2 ≤ (m:ℤ)^2 := by
  rw [←Int.bmod_eq_self_sub_mul_bdiv]
  have lo := Int.le_bmod (x:=a) hm
  have hi := Int.bmod_le (x:=a) hm
  have h₁ : 0 ≤ (m:ℤ) - 2*a.bmod m := by omega
  have h₂ : 0 ≤ (m:ℤ) + 2*a.bmod m := by omega
  nlinarith only [mul_nonneg h₁ h₂]

private theorem division (x y : Zsqrtd (-2)) (hy : y≠0) :
    ∃ q : Zsqrtd (-2), (x-y*q).norm < y.norm := by
  let m := y.norm.natAbs
  have hm : (m:ℤ)=y.norm := Int.natAbs_of_nonneg (norm_nonneg (by decide) y)
  have hp : 0 < y.norm := lt_of_le_of_ne (norm_nonneg (by decide) y)
    (Ne.symm <| mt (norm_eq_zero_iff (by decide) y).mp hy)
  have hmp : 0 < m := by omega
  let e := x*star y
  let q : Zsqrtd (-2) := ⟨e.re.bdiv m,e.im.bdiv m⟩
  refine ⟨q,?_⟩
  have hf : (x-y*q)*star y=e-(y.norm:Zsqrtd (-2))*q := by
    dsimp only [e]; rw [norm_eq_mul_conj]; ring
  have h := congrArg Zsqrtd.norm hf
  rw [norm_mul,norm_conj] at h
  have rb := rounded_square e.re m hmp
  have ib := rounded_square e.im m hmp
  rw [hm] at rb ib
  have h' : (e-(y.norm:Zsqrtd (-2))*q).norm =
      (e.re-y.norm*e.re.bdiv m)^2+2*(e.im-y.norm*e.im.bdiv m)^2 := by
    simp [norm_def,q]; ring
  rw [h'] at h
  apply (mul_lt_mul_iff_of_pos_right hp).mp
  nlinarith only [h,rb,ib,sq_pos_of_pos hp]

private theorem units {v : Zsqrtd (-2)} (hu : IsUnit v) : v=1 ∨ v= -1 := by
  have h := (norm_eq_one_iff' (by decide) v).mpr hu
  rw [norm_def] at h
  have hi : v.im=0 := by
    by_contra e
    have ha : 0 < v.im^2 := sq_pos_of_ne_zero e
    nlinarith [sq_nonneg v.re]
  rw [hi] at h
  have hr : v.re=1 ∨ v.re= -1 := by
    have : (v.re-1)*(v.re+1)=0 := by nlinarith
    rcases mul_eq_zero.mp this with h|h <;> omega
  rcases hr with h|h
  · exact Or.inl (by ext <;> simp [h,hi])
  · exact Or.inr (by ext <;> simp [h,hi])

/-- An odd power with coprime conjugate factors splits into actual powers. -/
theorem factor {x y : ℤ} {t n : ℕ} (hy : Odd y) (hn : Odd n)
    (h : x^2+(2:ℤ)^(2*t+1)=y^n) :
    ∃ w : Zsqrtd (-2), w^n=⟨x,(2:ℤ)^t⟩ := by
  let _ : EuclideanDomain (Zsqrtd (-2)) := by
    let q (x y : Zsqrtd (-2)) := if h : y=0 then 0 else (division x y h).choose
    exact {
      quotient := q
      quotient_zero := fun _ => dif_pos rfl
      remainder := fun x y => x-y*q x y
      quotient_mul_add_remainder_eq := fun _ _ => by ring
      r := fun x y => x.norm.natAbs < y.norm.natAbs
      r_wellFounded := (measure fun x : Zsqrtd (-2) => x.norm.natAbs).wf
      remainder_lt := by
        intro x y hy
        have h := (division x y hy).choose_spec
        simp only [q,dif_neg hy]
        apply Int.ofNat_lt.mp
        simpa only [Int.natAbs_of_nonneg (Zsqrtd.norm_nonneg (by decide : (-2:ℤ) ≤ 0) _)] using h
      mul_left_not_lt := by
        intro x y hy
        rw [Zsqrtd.norm_mul,Int.natAbs_mul]
        have hz : 0<y.norm.natAbs := by
          apply Nat.pos_of_ne_zero
          exact fun h => hy ((norm_eq_zero_iff (by decide) y).mp (Int.natAbs_eq_zero.mp h))
        exact not_lt_of_ge (by simpa using Nat.mul_le_mul_left x.norm.natAbs hz) }
  let _ := IsBezout.toGCDDomain (Zsqrtd (-2))
  let z : Zsqrtd (-2) := ⟨x,(2:ℤ)^t⟩
  have ep : (2:ℤ)^(2*t+1)=2*((2:ℤ)^t)^2 := by rw [pow_succ,Nat.mul_comm 2 t,pow_mul]; ring
  have hnorm : z.norm=y^n := by
    simp only [norm_def,z]
    rw [ep] at h
    linear_combination h
  have hp : z*star z=(y:Zsqrtd (-2))^n := by rw [←norm_eq_mul_conj,hnorm,Int.cast_pow]
  have hd : (z-star z)*(⟨0,-1⟩:Zsqrtd (-2)) = (2:Zsqrtd (-2))^(t+2) := by
    calc
      _ = (↑((2:ℤ)^(t+2)) : Zsqrtd (-2)) := by
        apply Zsqrtd.ext <;> simp only [re_mul,im_mul,re_sub,im_sub,re_star,im_star,re_intCast,im_intCast,z]
        · rw [pow_add]; ring
        · ring
      _ = _ := by push_cast; rfl
  have yc : IsCoprime y (2:ℤ) := by
    apply IsCoprime.symm
    apply Int.prime_two.irreducible.coprime_iff_not_dvd.mpr
    exact fun h₂ => (Int.not_even_iff_odd.mpr hy) (even_iff_two_dvd.mpr h₂)
  have hc : IsCoprime ((y:Zsqrtd (-2))^n) ((2:Zsqrtd (-2))^(t+2)) := by
    have hm := (yc.pow_left (m:=n)).pow_right (n:=t+2)
    simpa using hm.map (Int.castRingHom (Zsqrtd (-2)))
  have rel : IsRelPrime z (star z) := by
    intro a ha hb
    apply hc.isRelPrime
    · rw [←hp]; exact ha.trans (dvd_mul_right _ _)
    · rw [←hd]; exact (dvd_sub ha hb).trans (dvd_mul_right _ _)
  obtain ⟨w,v,hv⟩ := exists_associated_pow_of_mul_eq_pow (gcd_isUnit_iff_isRelPrime.mpr rel) hp
  rcases units v.isUnit with hu|hu
  · exact ⟨w,by simpa [hu] using hv⟩
  · exact ⟨-w,by simpa [hu,hn.neg_pow] using hv⟩

/-- The coefficient of the square root factors out of the imaginary coordinate of every power. -/
theorem scale_power {d : ℤ} (w : Zsqrtd d) (n : ℕ) :
    let z : Zsqrtd (d*w.im^2) := ⟨w.re,1⟩
    (w^n).re=(z^n).re ∧ (w^n).im=w.im*(z^n).im := by
  intro z
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [pow_succ,re_mul,im_mul,ih.1,ih.2,z]
    constructor <;> ring

/-- The coefficient before rescaling is odd for odd powers. -/
theorem coefficient_odd {d u : ℤ} (hd : Even d) (hu : Odd u) {n : ℕ} (hn : Odd n) :
    ((⟨u,1⟩ : Zsqrtd d)^n).im % 2 = 1 := by
  let z : Zsqrtd d := ⟨u,1⟩
  obtain ⟨j,rfl⟩ := hn
  have hd' : d%2=0 := Int.even_iff.mp hd
  have hu' : u%2=1 := Int.odd_iff.mp hu
  have hsq₁ : (z^2).re%2=1 := by
    simp only [pow_two,re_mul,z]
    simp [Int.add_emod,Int.mul_emod,hd',hu']
  have hsq₂ : (z^2).im%2=0 := by
    simp only [pow_two,im_mul,z]; omega
  change (z^(2*j+1)).im%2=1
  induction j with
  | zero => simp [z]
  | succ j ih =>
    rw [show 2*(j+1)+1=(2*j+1)+2 by omega,pow_add,im_mul,Int.add_emod]
    simp only [Int.mul_emod _ (z^2).im,Int.mul_emod _ (z^2).re,hsq₁,hsq₂,ih]
    norm_num

private theorem odd_pow_mod_three (a : ZMod 3) {n : ℕ} (hn : Odd n) : a^n=a := by
  obtain ⟨j,rfl⟩ := hn
  have h : ∀ u : ZMod 3, u^3=u := by decide +kernel
  induction j with
  | zero => simp
  | succ j ih =>
    rw [show 2*(j+1)+1=(2*j+1)+2 by omega,pow_add,ih]
    convert h a using 1
    ring

/-- Modulo three the two roots of T²+2 are +1 and −1. Odd powers fix both images. -/
theorem im_pow_mod_three (w : Zsqrtd (-2)) {n : ℕ} (hn : Odd n) :
    ((w^n).im : ZMod 3)=(w.im : ZMod 3) := by
  have eval (r : ZMod 3) (hr : r*r=((-2:ℤ):ZMod 3)) :
      ((w^n).re:ZMod 3)+(w^n).im*r = (w.re:ZMod 3)+w.im*r := by
    let f := Zsqrtd.lift (R:=ZMod 3) (d:=-2) ⟨r,hr⟩
    exact (f.map_pow w n).trans (odd_pow_mod_three (f w) hn)
  have plus := eval 1 (by decide)
  have minus := eval (-1) (by decide)
  apply mul_left_cancel₀ (by decide : (2:ZMod 3)≠0)
  linear_combination plus-minus

/-- At the power 2^(j+1), the real coordinate is 1 modulo 2^(j+2)
and the imaginary coordinate is exactly 2^(j+1) times an odd integer. -/
private theorem doubled (D u : ℤ) (hu : Odd u) (j : ℕ) :
    let z : Zsqrtd (4*D) := ⟨u,1⟩
    let h : ℤ := 2^(j+1)
    ∃ A B : ℤ, (z^(2^(j+1))).re=1+2*h*A ∧ (z^(2^(j+1))).im=h*(2*B+1) := by
  intro z
  induction j with
  | zero =>
    obtain ⟨v,hv⟩ := hu
    refine ⟨v^2+v+D,v,?_,?_⟩ <;> norm_num [pow_two,z,hv] <;> ring
  | succ j ih =>
    obtain ⟨A,B,ha,hb⟩ := ih
    let h : ℤ := 2^(j+1)
    refine ⟨A+h*A^2+D*h*(2*B+1)^2, B+h*A*(2*B+1),?_,?_⟩ <;>
      rw [show (2:ℕ)^(j+1+1)=2^(j+1)+2^(j+1) by rw [pow_succ]; omega,pow_add] <;>
      simp only [re_mul,im_mul,ha,hb,pow_succ (2:ℤ) (j+1),h] <;> ring

/-- Raising the preceding pair to an odd power preserves the odd multiplier
of its imaginary coordinate. The formula below also covers even multipliers. -/
private theorem multiples {D h : ℤ} (w : Zsqrtd (4*D)) {A B : ℤ}
    (ha : w.re=1+2*h*A) (hb : w.im=h*(2*B+1)) (m : ℕ) :
    ∃ C E : ℤ, (w^m).re=1+2*h*C ∧ (w^m).im=h*((m:ℤ)+2*E) := by
  induction m with
  | zero => exact ⟨0,0,by simp,by simp⟩
  | succ m ih =>
    obtain ⟨C,E,hc,he⟩ := ih
    refine ⟨C+A+2*h*C*A+2*D*h*(m+2*E)*(2*B+1),
      E+B+h*C*(2*B+1)+h*A*(m+2*E),?_,?_⟩ <;>
      simp only [pow_succ,re_mul,im_mul,hc,he,ha,hb,Nat.cast_succ] <;> ring

/-- The normalized imaginary coordinate cannot come back to one at any odd power above one. -/
theorem coefficient_ne_one {d u : ℤ} (hd : 4 ∣ d) (hu : Odd u) {n : ℕ}
    (hn : Odd n) (hn' : 1<n) : ((⟨u,1⟩ : Zsqrtd d)^n).im ≠ 1 := by
  obtain ⟨D,rfl⟩ := hd
  let z : Zsqrtd (4*D) := ⟨u,1⟩
  obtain ⟨l,hl⟩ := hn
  have hl' : l≠0 := by omega
  obtain ⟨j,m,hm,hj⟩ := Nat.exists_eq_two_pow_mul_odd hl'
  have nn : n=2^(j+1)*m+1 := by rw [hl,hj,pow_succ]; ring
  let h : ℤ := 2^(j+1)
  have hnz : h≠0 := by dsimp [h]; positivity
  obtain ⟨A,B,ha,hb⟩ := doubled D u hu j
  obtain ⟨C,E,hc,he⟩ := multiples (w:=z^(2^(j+1))) ha hb m
  change (z^n).im≠1
  rw [nn,pow_succ,pow_mul,im_mul,hc,he]
  change (1+2*h*C)*1+h*((m:ℤ)+2*E)*u ≠ 1
  intro eqn
  have heq : h*(2*C+((m:ℤ)+2*E)*u)=0 := by linear_combination eqn
  have zero := (mul_eq_zero.mp heq).resolve_left hnz
  obtain ⟨v,hv⟩ := hu
  obtain ⟨s,hs⟩ := hm
  have hms : (m:ℤ) = 2*s+1 := by exact_mod_cast hs
  rw [hv,hms] at zero
  have bad : 2*(C+((s:ℤ)+E)+v+(2:ℤ)*v*((s:ℤ)+E))+1=0 := by linear_combination zero
  omega

/-- No square of an odd integer plus an odd power of two above two is an odd power
with exponent greater than one. The bases are unrestricted in size. -/
theorem odd_exponents {x y : ℤ} {k n : ℕ} (hx : Odd x) (hy : Odd y)
    (hk : Odd k) (hk' : 2<k) (hn : Odd n) (hn' : 1<n) :
    x^2+(2:ℤ)^k ≠ y^n := by
  rintro eqn
  obtain ⟨t,ht⟩ := hk
  rw [ht] at eqn
  have htp : 0<t := by omega
  obtain ⟨w,hw⟩ := factor hy hn eqn
  have hre := congrArg Zsqrtd.re hw
  have him := congrArg Zsqrtd.im hw
  change (w^n).re=x at hre
  change (w^n).im=(2:ℤ)^t at him
  have oddreal : Odd w.re := by
    rcases Int.even_or_odd w.re with he|ho
    · obtain ⟨m,hm⟩ := he
      obtain ⟨j,hj⟩ := hn
      rw [hj,pow_succ,re_mul,hm] at hre
      obtain ⟨v,hv⟩ := hx
      rw [hv] at hre
      have impossible : 2*((w^(2*j)).re*m-(w^(2*j)).im*w.im-v)=1 := by linear_combination hre
      omega
    · exact ho
  let z : Zsqrtd (-2*w.im^2) := ⟨w.re,1⟩
  let q := (z^n).im
  have hqodd : Odd q := Int.odd_iff.mpr
    (coefficient_odd (show Even (-2*w.im^2) from ⟨-w.im^2,by ring⟩) oddreal hn)
  have hprod : w.im*q=(2:ℤ)^t := (scale_power w n).2.symm.trans him
  have cop : IsCoprime (2:ℤ) q :=
    Int.prime_two.irreducible.coprime_iff_not_dvd.mpr
      (fun d => (Int.not_even_iff_odd.mpr hqodd) (even_iff_two_dvd.mpr d))
  have hunit : IsUnit q :=
    (cop.pow_left (m:=t)).symm.isUnit_of_dvd ⟨w.im,hprod.symm.trans (mul_comm _ _)⟩
  have conf := im_pow_mod_three w hn
  rw [him] at conf
  have hplus : q=1 := by
    rcases Int.isUnit_iff.mp hunit with h|h
    · exact h
    · rw [h,mul_neg_one] at hprod
      have hneg : w.im = -(2:ℤ)^t := by omega
      rw [hneg] at conf
      push_cast at conf
      have hh : ∀ u : ZMod 3, u = -u → u=0 := by decide +kernel
      exact False.elim ((pow_ne_zero t (by decide : (2:ZMod 3)≠0)) (hh _ conf))
  rw [hplus,mul_one] at hprod
  have evenim : Even w.im := by
    rw [hprod]
    exact Even.pow_of_ne_zero (by decide : Even (2:ℤ)) htp.ne'
  obtain ⟨v,hv⟩ := evenim
  have hd : 4 ∣ -2*w.im^2 := ⟨-2*v^2,by rw [hv]; ring⟩
  exact coefficient_ne_one hd oddreal hn hn' hplus

/-- Odd squares separated by a power of two have smaller factor two in their
difference-of-squares factorization. -/
theorem square_difference {U V k : ℕ} (hU : U%2=1) (hV : V%2=1)
    (h : V^2+2^k=U^2) : U=V+2 ∧ U+V=2^(k-1) := by
  have hlt : V<U := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    have hpos := Nat.two_pow_pos k
    omega
  let d := U-V
  let e := U+V
  have hd : 0<d := by dsimp [d]; omega
  have hd₀ : d%2=0 := by dsimp [d]; omega
  have he₀ : e%2=0 := by dsimp [e]; omega
  have hs : d+e=2*U := by dsimp [d,e]; omega
  have hv : U=V+d := by dsimp [d]; omega
  have hprod : d*e=2^k := by dsimp [e]; rw [hv] at h ⊢; nlinarith
  obtain ⟨i,_,hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (show d∣2^k from ⟨e,hprod.symm⟩)
  obtain ⟨j,_,hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show e∣2^k from ⟨d,hprod.symm.trans (Nat.mul_comm _ _)⟩)
  have ipos : i≠0 := by rintro rfl; simp_all
  have jpos : j≠0 := by rintro rfl; simp_all
  have dij : d≤e := by dsimp [d,e]; omega
  have hd₂ : d=2 := by
    by_contra hne
    have i₂ : 2 ≤ i := by by_contra! h'; interval_cases i <;> simp_all
    have dd : 4 ≤ d := hi ▸ (Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) i₂)
    have j₂ : 2 ≤ j := by by_contra! h'; interval_cases j <;> norm_num at hj <;> omega
    have h4d : 4 ∣ d := hi ▸ pow_dvd_pow 2 i₂
    have h4e : 4 ∣ e := hj ▸ pow_dvd_pow 2 j₂
    omega
  have hk : k=1+j := by
    apply Nat.pow_right_injective (by decide : 1<(2:ℕ))
    change (2:ℕ)^k=2^(1+j)
    rw [←hprod,hd₂,hj,pow_add,pow_one]
  exact ⟨by omega,by change e=2^(k-1); rw [hk,show 1+j-1=j by omega,hj]⟩

theorem quartic {x y k : ℕ} (hx : x%2=1) (hy : y%2=1) (hk : 2<k)
    (h : x^2+2^k=y^4) : x=7 ∧ y=3 ∧ k=5 := by
  have hU : (y^2)%2=1 := by rw [Nat.pow_mod,hy]
  have he : x^2+2^k=(y^2)^2 := by rw [←pow_mul]; exact h
  obtain ⟨h₁,h₂⟩ := square_difference hU hx he
  have exp : (2:ℕ)^(k-1)=2*2^(k-2) := by
    rw [show k-1=(k-2)+1 by omega,pow_succ,Nat.mul_comm]
  rw [exp] at h₂
  have he' : 1^2 + 2^(k-2)=y^2 := by norm_num; omega
  obtain ⟨h₃,_⟩ := square_difference hy (by decide : 1%2=1) he'
  have hy₃ : y=3 := h₃
  have hx₇ : x=7 := by rw [hy₃] at h₁; norm_num at h₁; omega
  refine ⟨hx₇,hy₃,?_⟩
  rw [hx₇,hy₃] at h
  apply Nat.pow_right_injective (by decide : 1<(2:ℕ))
  norm_num at h ⊢
  omega

/-- In the Gaussian integers modulo three, a unit to the seventh power is its
inverse. If its imaginary coordinate flips sign, the real coordinate is zero. -/
theorem gaussian_mod_three (w : GaussianInt) {n : ℕ} (hn : n%8=7)
    (hu : (w.im:ZMod 3)≠0) (he : ((w^n).im:ZMod 3)= -(w.im:ZMod 3)) :
    (w.re:ZMod 3)=0 ∧ ((w^n).re:ZMod 3)=0 := by
  let mul (a b : ZMod 3 × ZMod 3) := (a.1*b.1+(-1)*a.2*b.2,a.1*b.2+a.2*b.1)
  let pow (v : ZMod 3 × ZMod 3) (k : ℕ) : ZMod 3 × ZMod 3 :=
    Nat.rec (motive := fun _ => ZMod 3 × ZMod 3) (1,0) (fun _ s => mul s v) k
  let v : ZMod 3 × ZMod 3 := (w.re,w.im)
  have reduction (k : ℕ) : (((w^k).re:ZMod 3),((w^k).im:ZMod 3))=pow v k := by
    induction k with
    | zero => simp [pow]
    | succ k ih =>
      simpa only [pow_succ,re_mul,im_mul,Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_one,
        pow,mul,v,Nat.rec_add_one] using congrArg (fun s => mul s v) ih
  have table : ∀ a b : ZMod 3, b≠0 →
      pow (a,b) 8=(1,0) ∧ ((pow (a,b) 7).2= -b → a=0 ∧ (pow (a,b) 7).1=0) := by
    dsimp only [pow,mul]
    decide +kernel
  obtain ⟨h8,h7⟩ := table (w.re:ZMod 3) (w.im:ZMod 3) hu
  have re8 := congrArg Prod.fst ((reduction 8).trans h8)
  have im8 := congrArg Prod.snd ((reduction 8).trans h8)
  change ((w^8).re:ZMod 3)=1 at re8
  change ((w^8).im:ZMod 3)=0 at im8
  have cycle (j : ℕ) : ((w^(8*j+7)).re:ZMod 3)=((w^7).re:ZMod 3) ∧
      ((w^(8*j+7)).im:ZMod 3)=((w^7).im:ZMod 3) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show 8*(j+1)+7=(8*j+7)+8 by omega,pow_add]
      simp only [re_mul,im_mul,Int.cast_add,Int.cast_mul,re8,im8,mul_one,mul_zero,
        add_zero,zero_add,ih.1,ih.2,and_self]
  obtain ⟨reN,imN⟩ := cycle (n/8)
  rw [show 8*(n/8)+7=n by omega] at reN imN
  have seven_re := congrArg Prod.fst (reduction 7)
  have seven_im := congrArg Prod.snd (reduction 7)
  obtain ⟨ha,hb⟩ := h7 (seven_im.symm.trans (imN.symm.trans he))
  exact ⟨ha,reN.trans (seven_re.trans hb)⟩

/-- Repeated cubing of a principal unit preserves its first nonzero
coefficient at three. The identity holds in every commutative ring. -/
private theorem principal_unit_cube {R : Type*} [CommRing R] (a : R) (j : ℕ) :
    ∃ e : R, (1+3*a)^(3^j)=1+3^(j+1)*(a+3*e) := by
  induction j with
  | zero => exact ⟨0,by simp⟩
  | succ j ih =>
    obtain ⟨e,he⟩ := ih
    let A := a+3*e
    refine ⟨e+3^j*A^2+(3^j)^2*A^3,?_⟩
    rw [pow_succ (3:ℕ) j,pow_mul,he,pow_succ (3:R) (j+1),pow_succ (3:R) j]
    dsimp [A]; ring

private theorem principal_unit_multiple {R : Type*} [CommRing R] (a h e : R) (m : ℕ) :
    ∃ f : R, (1+3*h*(a+3*e))^m=1+3*h*((m:R)*a+3*f) := by
  induction m with
  | zero => exact ⟨0,by simp⟩
  | succ m ih =>
    obtain ⟨f,hf⟩ := ih
    refine ⟨f+e+h*(m*a+3*f)*(a+3*e),?_⟩
    rw [pow_succ,hf,Nat.cast_succ]; ring

/-- If the normalized imaginary coordinate equals minus one, reduction at
three forces the shift exponent t itself to be divisible by three. -/
theorem three_dvd_half_shift {u : ℤ} {n t : ℕ} (hu : 3 ∣ u) (hn : n%8=7)
    (coef : ((⟨u,1⟩ : Zsqrtd (-(4:ℤ)^t))^n).im= -1) : 3 ∣ t := by
  obtain ⟨v,hv⟩ := hu
  let d := -(4:ℤ)^t
  let z : Zsqrtd d := ⟨u,1⟩
  have four (k : ℕ) : ∃ T : ℤ, (4:ℤ)^k=1+3*((k:ℤ)+3*T) := by
    induction k with
    | zero => exact ⟨0,by simp⟩
    | succ k ih =>
      obtain ⟨T,hT⟩ := ih
      exact ⟨k+4*T,by rw [pow_succ,hT,Nat.cast_succ]; ring⟩
  obtain ⟨T,hT⟩ := four t
  let A : Zsqrtd d := ⟨(t:ℤ)+3*(T-v^2),-2*v⟩
  have base : -(z^2)=1+3*A := by
    apply Zsqrtd.ext <;>
      simp [pow_two,z,d,A,Zsqrtd.re_mul,Zsqrtd.im_mul,hv,hT] <;> ring
  let s := n/2
  have ns : n=2*s+1 := by dsimp [s]; omega
  have so : Odd s := Nat.odd_iff.mpr (by dsimp [s]; omega)
  obtain ⟨j,m,hm,hs⟩ := Nat.exists_eq_pow_mul_and_not_dvd (show s≠0 by dsimp [s]; omega) 3 (by decide)
  obtain ⟨e,he⟩ := principal_unit_cube A j
  obtain ⟨f,hf⟩ := principal_unit_multiple A (3^j) e m
  have power : (-(z^2))^s = 1+3*(3:Zsqrtd d)^j*((m:Zsqrtd d)*A+3*f) := by
    rw [base,hs,pow_mul,he,pow_succ (3:Zsqrtd d) j,mul_comm ((3:Zsqrtd d)^j) 3,hf]
  have imag : (((-(z^2))^s)*z).im=1 := by
    rw [so.neg_pow,←pow_mul,neg_mul,←pow_succ,←ns]
    change -(z^n).im=1
    change (z^n).im= -1 at coef
    omega
  rw [power] at imag
  have scal : (3:Zsqrtd d)^j=(((3:ℤ)^j:ℤ):Zsqrtd d) := by push_cast; rfl
  have sr : ((3:Zsqrtd d)^j).re=(3:ℤ)^j := by rw [scal]; rfl
  have si : ((3:Zsqrtd d)^j).im=0 := by rw [scal]; rfl
  simp [Zsqrtd.im_mul,Zsqrtd.re_mul,z,A,hv,sr,si] at imag
  have prod : (3*(3:ℤ)^j)*((m:ℤ)*((t:ℤ)+3*(T-v^2))+3*f.re+
      ((m:ℤ)*(-2*v)+3*f.im)*(3*v))=0 := by linear_combination imag
  have zero := (mul_eq_zero.mp prod).resolve_left (by positivity)
  have dvd : (3:ℤ) ∣ (m:ℤ)*(t:ℤ) :=
    ⟨-((m:ℤ)*(T-v^2)+f.re+((m:ℤ)*(-2*v)+3*f.im)*v),by linear_combination zero⟩
  have natdvd : 3 ∣ m*t := by exact_mod_cast dvd
  exact (Nat.prime_three.dvd_mul.mp natdvd).resolve_left hm

private theorem gaussian_unit_fourth {v : GaussianInt} (hu : IsUnit v) : v^4=1 := by
  obtain ⟨a,b⟩ := v
  have h := (norm_eq_one_iff' (by decide) (⟨a,b⟩:GaussianInt)).mpr hu
  change a*a - (-1)*b*b=1 at h
  have ha : -1≤a ∧ a≤1 := by constructor <;> nlinarith [sq_nonneg b]
  have hb : -1≤b ∧ b≤1 := by constructor <;> nlinarith [sq_nonneg a]
  obtain ⟨ha₁,ha₂⟩ := ha
  obtain ⟨hb₁,hb₂⟩ := hb
  interval_cases a <;> interval_cases b <;> norm_num at h <;> decide

private theorem gaussian_factor {x y : ℤ} {t n : ℕ} (hy : Odd y) (hn : Odd n)
    (h : x^2+(2:ℤ)^(2*t)=y^n) : ∃ w : GaussianInt, w^n=⟨x,(2:ℤ)^t⟩ := by
  let _ := IsBezout.toGCDDomain GaussianInt
  let z : GaussianInt := ⟨x,(2:ℤ)^t⟩
  have hnorm : z.norm=y^n := by
    simp only [norm_def,z]
    rw [Nat.mul_comm 2 t,pow_mul] at h
    linear_combination h
  have hp : z*star z=(y:GaussianInt)^n := by rw [←norm_eq_mul_conj,hnorm,Int.cast_pow]
  have hd : (z-star z)*(⟨0,-1⟩:GaussianInt)=(2:GaussianInt)^(t+1) := by
    calc
      _ = (↑((2:ℤ)^(t+1)) : GaussianInt) := by
        apply Zsqrtd.ext <;> simp only [re_mul,im_mul,re_sub,im_sub,re_star,im_star,re_intCast,im_intCast,z]
        · rw [pow_succ]; ring
        · ring
      _ = _ := by push_cast; rfl
  have yc : IsCoprime y (2:ℤ) := by
    apply IsCoprime.symm
    apply Int.prime_two.irreducible.coprime_iff_not_dvd.mpr
    exact fun d => (Int.not_even_iff_odd.mpr hy) (even_iff_two_dvd.mpr d)
  have hc : IsCoprime ((y:GaussianInt)^n) ((2:GaussianInt)^(t+1)) := by
    simpa using ((yc.pow_left (m:=n)).pow_right (n:=t+1)).map (Int.castRingHom GaussianInt)
  have rel : IsRelPrime z (star z) := by
    intro a ha hb
    apply hc.isRelPrime
    · rw [←hp]; exact ha.trans (dvd_mul_right _ _)
    · rw [←hd]; exact (dvd_sub ha hb).trans (dvd_mul_right _ _)
  obtain ⟨w,v,hv⟩ := exists_associated_pow_of_mul_eq_pow (gcd_isUnit_iff_isRelPrime.mpr rel) hp
  obtain ⟨j,hj⟩ := hn
  have v4 := gaussian_unit_fourth v.isUnit
  have inv : ((v:GaussianInt)^n)^n=(v:GaussianInt) := by
    rw [←pow_mul,show n*n=4*(j*j+j)+1 by rw [hj]; ring,pow_succ,pow_mul,v4,one_pow,one_mul]
  exact ⟨w*(v:GaussianInt)^n,by simpa only [mul_pow,inv] using hv⟩

private theorem gaussian_parity (w : GaussianInt) {n : ℕ} (hn : Odd n)
    (hr : ((w^n).re:ZMod 2)=1) (hi : ((w^n).im:ZMod 2)=0) :
    Odd w.re ∧ Even w.im := by
  let f := Zsqrtd.lift (R:=ZMod 2) (d:=-1) ⟨1,by decide⟩
  have h := f.map_pow w n
  change ((w^n).re:ZMod 2)+(w^n).im*1=((w.re:ZMod 2)+w.im*1)^n at h
  rw [hr,hi] at h
  have hne : (w.re:ZMod 2)+w.im≠0 := by
    intro e
    simp only [mul_one] at h
    rw [e,zero_pow (show n≠0 by obtain ⟨j,hj⟩ := hn; omega)] at h
    norm_num at h
  have square : ((w^2).re:ZMod 2)=1 ∧ ((w^2).im:ZMod 2)=0 := by
    have table : ∀ a b : ZMod 2, a+b≠0 → a*a + (-1)*b*b=1 ∧ a*b+b*a=0 := by decide +kernel
    simpa only [pow_two,re_mul,im_mul,Int.cast_add,Int.cast_mul,Int.cast_neg,Int.cast_one] using
      table (w.re:ZMod 2) (w.im:ZMod 2) hne
  have cycle (j : ℕ) : ((w^(2*j+1)).re:ZMod 2)=w.re ∧ ((w^(2*j+1)).im:ZMod 2)=w.im := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [show 2*(j+1)+1=(2*j+1)+2 by omega,pow_add]
      simp only [re_mul,im_mul,Int.cast_add,Int.cast_mul,ih.1,ih.2,square.1,square.2,
        mul_one,mul_zero,add_zero,zero_add,and_self]
  obtain ⟨j,hj⟩ := hn
  obtain ⟨h₁,h₂⟩ := cycle j
  rw [←hj,hr] at h₁
  rw [←hj,hi] at h₂
  constructor
  · apply Int.odd_iff.mpr
    exact (ZMod.intCast_eq_intCast_iff' w.re 1 2).mp (by simpa using h₁.symm)
  · apply Int.even_iff.mpr
    exact (ZMod.intCast_eq_intCast_iff' w.im 0 2).mp (by simpa using h₂.symm)

private theorem coefficient_mod_eight {d u : ℤ} (hd : 8 ∣ d) (hu : Odd u) {n : ℕ} (hn : Odd n) :
    (((⟨u,1⟩ : Zsqrtd d)^n).im : ZMod 8)=n := by
  let z : Zsqrtd d := ⟨u,1⟩
  have dz : (d:ZMod 8)=0 := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mpr hd
  have real_part (k : ℕ) : ((z^k).re:ZMod 8)=(u:ZMod 8)^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ,re_mul]
      push_cast
      rw [dz,ih,pow_succ]
      simp [z]
  have imag_part (k : ℕ) : ((z^(k+1)).im:ZMod 8)=((k:ZMod 8)+1)*(u:ZMod 8)^k := by
    induction k with
    | zero => simp [z]
    | succ k ih =>
      rw [pow_succ z (k+1),im_mul]; push_cast
      rw [real_part,ih,pow_succ]
      simp only [z,Int.cast_one,mul_one]
      ring
  have u2 : (u:ZMod 8)^2=1 := by
    obtain ⟨v,hv⟩ := hu
    have tab : ∀ s : ZMod 8, (2*s+1)^2=1 := by decide +kernel
    rw [hv]; push_cast; exact tab _
  obtain ⟨j,rfl⟩ := hn
  change ((z^(2*j+1)).im:ZMod 8)=_
  rw [imag_part,pow_mul,u2,one_pow,mul_one]
  push_cast
  rfl

/-- For an even shift exponent at least four, an odd exponent above one is seven
modulo eight. Three divides both the base of the square and the half-exponent. -/
theorem gaussian_witness {x y : ℤ} {t n : ℕ} (hx : Odd x) (hy : Odd y) (ht : 2≤t)
    (hn : Odd n) (hn' : 1<n) (h : x^2+(2:ℤ)^(2*t)=y^n) : n%8=7 ∧ 3∣x ∧ 3∣t ∧
      ∃ u : ℤ, Odd u ∧ 3∣u ∧ y=u^2+(2^t)^2 ∧
        ((⟨u,1⟩ : Zsqrtd (-((2:ℤ)^t)^2))^n).im= -1 := by
  obtain ⟨w,hw⟩ := gaussian_factor hy hn h
  have hr := congrArg Zsqrtd.re hw
  have hi := congrArg Zsqrtd.im hw
  change (w^n).re=x at hr
  change (w^n).im=(2:ℤ)^t at hi
  have hp : ((w^n).re:ZMod 2)=1 := by
    rw [hr]
    apply (ZMod.intCast_eq_intCast_iff' x 1 2).mpr
    simpa using Int.odd_iff.mp hx
  have hq : ((w^n).im:ZMod 2)=0 := by
    rw [hi]; push_cast; rw [show (2:ZMod 2)=0 by decide,zero_pow (by omega : t≠0)]
  obtain ⟨hou,hev⟩ := gaussian_parity w hn hp hq
  let d := -1*w.im^2
  let z : Zsqrtd d := ⟨w.re,1⟩
  let q := (z^n).im
  obtain ⟨v,hv⟩ := hev
  have dd : Even d := ⟨-2*v^2,by dsimp [d]; rw [hv]; ring⟩
  have oq : Odd q := Int.odd_iff.mpr (coefficient_odd dd hou hn)
  have prod : w.im*q=(2:ℤ)^t := (scale_power w n).2.symm.trans hi
  have cp : IsCoprime (2:ℤ) q := Int.prime_two.irreducible.coprime_iff_not_dvd.mpr
    (fun e => (Int.not_even_iff_odd.mpr oq) (even_iff_two_dvd.mpr e))
  have unit := (cp.pow_left (m:=t)).symm.isUnit_of_dvd (show q ∣ (2:ℤ)^t from
    ⟨w.im,prod.symm.trans (mul_comm _ _)⟩)
  have four : 4 ∣ d := ⟨-v^2,by dsimp [d]; rw [hv]; ring⟩
  have neg := (Int.isUnit_iff.mp unit).resolve_left (coefficient_ne_one four hou hn hn')
  rw [neg,mul_neg_one] at prod
  have vi : w.im= -(2:ℤ)^t := by omega
  obtain ⟨s,hs⟩ := (show (4:ℤ) ∣ (2:ℤ)^t from pow_dvd_pow 2 ht)
  have eight : 8 ∣ d := ⟨-2*s^2,by dsimp [d]; rw [vi,hs]; ring⟩
  have mod8 := coefficient_mod_eight eight hou hn
  change (q:ZMod 8)=(n:ZMod 8) at mod8
  rw [neg] at mod8
  have value := congrArg ZMod.val mod8
  have rem : n%8=7 := by
    simpa only [ZMod.val_natCast,show ((-1:ℤ):ZMod 8).val=7 by decide] using value.symm
  have hu : (w.im:ZMod 3)≠0 := by
    rw [vi]; push_cast
    exact neg_ne_zero.mpr (pow_ne_zero _ (by decide))
  have conj := gaussian_mod_three w rem hu (by rw [hi,vi]; push_cast; simp)
  have xu : (3:ℤ) ∣ x := by
    rw [←hr]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp conj.2
  have step : (4:ℤ)^t=((2:ℤ)^t)^2 := by rw [←pow_mul,Nat.mul_comm t 2,pow_mul]; norm_num
  have dd' : d= -(4:ℤ)^t := by dsimp [d]; rw [vi,step]; ring
  change ((⟨w.re,1⟩ : Zsqrtd d)^n).im= -1 at neg
  rw [dd'] at neg
  have du := (ZMod.intCast_zmod_eq_zero_iff_dvd ..).mp conj.1
  have hnrm : (w.norm)^n=y^n := by
    have eq := congrArg Zsqrtd.norm hw
    change Zsqrtd.normMonoidHom (w^n)=_ at eq
    rw [map_pow] at eq
    change w.norm^n=x*x-(-1)*((2:ℤ)^t)*((2:ℤ)^t) at eq
    rw [Nat.mul_comm 2 t,pow_mul] at h
    linear_combination eq + h
  have nr : w.norm=y := (hn.strictMono_pow.injective hnrm)
  refine ⟨rem,xu,three_dvd_half_shift du rem neg,w.re,hou,du,?_,by rwa [←step]⟩
  rw [←nr,Zsqrtd.norm_def,vi]; ring

/-- The exponent and the power of two are restricted by the Gaussian coefficient. -/
theorem gaussian_exponent {x y : ℤ} {t n : ℕ} (hx : Odd x) (hy : Odd y) (ht : 2≤t)
    (hn : Odd n) (hn' : 1<n) (h : x^2+(2:ℤ)^(2*t)=y^n) : n%8=7 ∧ 3∣x ∧ 3∣t := by
  obtain ⟨rem,xu,dt,_⟩ := gaussian_witness hx hy ht hn hn' h
  exact ⟨rem,xu,dt⟩

/-- For odd y, the odd part of y^j - 1 contains the geometric quotient
when j is odd. The quotient exceeds one once j exceeds one. -/
private theorem odd_power_neighbor {y j : ℕ} (hy : y%2=1) (hy' : 1<y)
    (hj : Odd j) (hj' : 1<j) (a : ℕ) : y^j ≠ 2^a+1 := by
  obtain ⟨b,hb⟩ := hj
  let d := y-1
  have yd : y=d+1 := by dsimp [d]; omega
  have factor (i : ℕ) : ∃ q : ℕ, y^(2*i+1)=d*q+1 ∧ q%2=1 ∧ (0 < i → 1 < q) := by
    induction i with
    | zero => exact ⟨1,by simpa using yd,by decide,by omega⟩
    | succ i ih =>
      obtain ⟨q,h,hq,_⟩ := ih
      refine ⟨q*y^2+(y+1),?_,?_,by omega⟩
      · rw [show 2*(i+1)+1=(2*i+1)+2 by omega,pow_add,h]
        rw [yd]; ring
      · rw [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,hq,hy,Nat.add_mod y 1 2,hy]
  obtain ⟨q,hfac,hodd,hlarge⟩ := factor b
  intro eqn
  rw [hb,hfac] at eqn
  have hp : d*q=2^a := by omega
  obtain ⟨j,_,h⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show q∣2^a from ⟨d,hp.symm.trans (Nat.mul_comm _ _)⟩)
  have hq := hlarge (by omega)
  cases j with
  | zero => simp_all
  | succ j => rw [h,pow_succ,Nat.mul_mod_left] at hodd; contradiction

/-- If the exponent of the right side is even, the only possibility for k>2 and n>2
is 7² + 2⁵ = 3⁴. -/
private theorem even_exponent {x y k n : ℕ} (hx : x%2=1) (hy : y%2=1)
    (hk : 2<k) (hn : 2<n) (he : Even n) (h : x^2+2^k=y^n) :
    x=7 ∧ y=3 ∧ k=5 ∧ n=4 := by
  by_cases hfour : 4 ∣ n
  · obtain ⟨j,hj⟩ := hfour
    have hY : (y^j)%2=1 := by rw [Nat.pow_mod,hy,one_pow]; decide
    have hh : x^2+2^k=(y^j)^4 := by rw [←pow_mul,Nat.mul_comm j 4,←hj]; exact h
    obtain ⟨h₁,h₂,h₃⟩ := quartic hx hY hk hh
    have hp := (Nat.Prime.pow_eq_iff (by decide : Nat.Prime 3)).mp h₂
    exact ⟨h₁,hp.1,h₃,by omega⟩
  obtain ⟨j,hj⟩ := he
  have hY : (y^j)%2=1 := by rw [Nat.pow_mod,hy,one_pow]; decide
  have hh : x^2+2^k=(y^j)^2 := by rw [←pow_mul,show j*2=n by omega]; exact h
  obtain ⟨h₁,h₂⟩ := square_difference hY hx hh
  have exp : (2:ℕ)^(k-1)=2*2^(k-2) := by
    rw [show k-1=(k-2)+1 by omega,pow_succ,Nat.mul_comm]
  rw [exp] at h₂
  have hp := Nat.two_pow_pos (k-2)
  have ygt : 1<y := by
    by_contra! e
    have y1 : y=1 := by omega
    rw [y1,one_pow] at h₁; omega
  exact (odd_power_neighbor hy ygt (Nat.odd_iff.mpr (by omega)) (by omega : 1<j)
    (k-2) (by omega)).elim

/-- For k,n>2, a solution with odd bases is the exceptional quartic or has
6 ∣ k, prime exponent n congruent to seven modulo eight, and 3 ∣ x. -/
theorem classify_square_shift {x y k n : ℕ} (hx : x%2=1) (hy : y%2=1)
    (hk : 2<k) (hn : 2<n) (h : x^2+2^k=y^n) :
    (x=7 ∧ y=3 ∧ k=5 ∧ n=4) ∨ (6 ∣ k ∧ n.Prime ∧ n%8=7 ∧ 3 ∣ x) := by
  rcases Nat.even_or_odd n with ne|no
  · exact Or.inl (even_exponent hx hy hk hn ne h)
  rcases Nat.even_or_odd k with ke|ko
  · right
    obtain ⟨t,ht⟩ := ke
    have hk' : k=2*t := by omega
    have rem (m j : ℕ) (hm : 1 < m) (he : n=m*j) : m%8=7 ∧ 3 ∣ x ∧ 3 ∣ t := by
      have om : Odd m := by
        have o := Nat.odd_iff.mp no
        rw [he,Nat.mul_mod] at o
        apply Nat.odd_iff.mpr
        by_contra hne
        have v : m%2=0 := by omega
        simp [v] at o
      have hY : (y^j)%2=1 := by rw [Nat.pow_mod,hy,one_pow]; decide
      have eqn : x^2+2^(2*t)=(y^j)^m := by rw [←hk',←pow_mul,Nat.mul_comm j m,←he]; exact h
      have ⟨rm,dx,dt⟩ := gaussian_exponent (x:=(x:ℤ)) (y:=((y^j:ℕ):ℤ)) (t:=t)
        (by exact_mod_cast Nat.odd_iff.mpr hx)
        (by exact_mod_cast Nat.odd_iff.mpr hY) (by omega) om hm (by exact_mod_cast eqn)
      exact ⟨rm,by exact_mod_cast dx,dt⟩
    have ⟨rn,dx,dt⟩ := rem n 1 (by omega) (by simp)
    refine ⟨by omega,?_,rn,dx⟩
    by_contra np
    obtain ⟨a,b,ha,hb,hprod⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega)).mp np
    have a' : 1<a := by by_contra! he; interval_cases a <;> simp_all
    have b' : 1<b := by by_contra! he; interval_cases b <;> simp_all
    have ra := (rem a b a' hprod.symm).1
    have rb := (rem b a b' (hprod.symm.trans (Nat.mul_comm _ _))).1
    rw [←hprod,Nat.mul_mod,ra,rb] at rn
    contradiction
  · exact False.elim (odd_exponents (x:=(x:ℤ)) (y:=(y:ℤ)) (by exact_mod_cast Nat.odd_iff.mpr hx)
      (by exact_mod_cast Nat.odd_iff.mpr hy) ko hk no (by omega) (by exact_mod_cast h))

section

open Pell Pell.Solution₁

private theorem pell_real_recurrence {d : ℤ} (g : Pell.Solution₁ d) (n : ℕ) :
    (g^(n+2)).x = 2*g.x*(g^(n+1)).x-(g^n).x := by
  rw [pow_succ g (n+1),pow_succ g n]
  simp only [x_mul,y_mul]
  linear_combination -(g^n).x*g.prop

/-- The first coordinate of every even power is odd. At every odd power
it is the first coordinate of the generator times an odd integer. -/
private theorem pell_real_parity {d : ℤ} (g : Pell.Solution₁ d) (k : ℕ) :
    Odd (g^(2*k)).x ∧ ∃ j : ℤ, Odd j ∧ (g^(2*k+1)).x=g.x*j := by
  induction k with
  | zero => exact ⟨by simp,1,by decide,by simp⟩
  | succ k ih =>
    obtain ⟨⟨v,hv⟩,j,⟨s,hs⟩,hj⟩ := ih
    rw [show 2*(k+1)=2*k+2 by omega]
    constructor
    · refine ⟨g.x*(g^(2*k+1)).x-v-1,?_⟩
      rw [pell_real_recurrence,hv]; ring
    · refine ⟨2*(g^(2*k+2)).x-j,⟨(g^(2*k+2)).x-s-1,by rw [hs]; ring⟩,?_⟩
      rw [show 2*k+2+1=2*k+1+2 by omega,pell_real_recurrence,hj]
      ring

/-- A power of two dividing the first coordinate of a Pell solution divides
the first coordinate of the fundamental solution (Le, Lemma 3). -/
theorem pell_two_dvd_fundamental {d X Y : ℤ} {g : Pell.Solution₁ d} (fund : Pell.IsFundamental g)
    {t : ℕ} (eqn : X^2-d*Y^2=1) (divides : (2:ℤ)^t∣X) : (2:ℤ)^t∣g.x := by
  rcases t with _|t
  · simp
  let a : Pell.Solution₁ d := Pell.Solution₁.mk |X| |Y| (by simpa only [sq_abs] using eqn)
  have apos : 0<a.x := by
    change 0 < |X|
    apply abs_pos.mpr
    rintro rfl
    have := mul_nonneg fund.d_pos.le (sq_nonneg Y)
    norm_num at eqn
    omega
  obtain ⟨n,en⟩ := fund.eq_pow_of_nonneg apos (show 0≤a.y from abs_nonneg _)
  have dvd : (2:ℤ)^(t+1)∣(g^n).x := by
    rw [←en]
    exact (dvd_abs _ _).mpr divides
  have parity := pell_real_parity g (n/2)
  by_cases even : n%2=0
  · have e : 2*(n/2)=n := by omega
    rw [e] at parity
    exact ((Int.not_even_iff_odd.mpr parity.1)
      (even_iff_two_dvd.mpr ((dvd_pow_self (2:ℤ) (by omega : t+1≠0)).trans dvd))).elim
  · obtain ⟨j,jo,eq⟩ := parity.2
    rw [show 2*(n/2)+1=n by omega] at eq
    rw [eq] at dvd
    have cp : IsCoprime (2:ℤ) j := Int.prime_two.irreducible.coprime_iff_not_dvd.mpr
      (fun h => (Int.not_even_iff_odd.mpr jo) (even_iff_two_dvd.mpr h))
    exact (cp.pow_left (m:=t+1)).dvd_of_dvd_mul_right dvd

private theorem fundamental_from_residues {d : ℤ} {X Y m : ℕ} [NeZero m]
    (eqn : (X:ℤ)^2-d*(Y:ℤ)^2=1) (hx : 1<X) (hy : 0<Y)
    (test : ∀ i : Fin X, ∀ y : ZMod m, 1 < i.val →
      (i.val:ZMod m)^2-(d:ZMod m)*y^2≠1) :
    Pell.IsFundamental (Pell.Solution₁.mk X Y eqn) := by
  refine ⟨by change (1:ℤ)<(X:ℤ); exact_mod_cast hx,by change (0:ℤ)<(Y:ℤ); exact_mod_cast hy,?_⟩
  intro b hb
  change (X:ℤ)≤b.x
  by_contra! small
  let i : Fin X := ⟨b.x.toNat,by omega⟩
  have hi : 1 < i.val := by change 1 < b.x.toNat; omega
  have ei : (i.val:ℤ)=b.x := Int.toNat_of_nonneg (by omega)
  have em := congrArg (fun z : ℤ => (z:ZMod m)) b.prop
  push_cast at em
  have eic := congrArg (fun z : ℤ => (z:ZMod m)) ei
  push_cast at eic
  exact test i _ hi (eic ▸ em)

theorem pell_seven_no_sixteen {X Y : ℤ} (e : X^2-7*Y^2=1) : ¬(16:ℤ)∣X := by
  let g : Pell.Solution₁ 7 := Pell.Solution₁.mk 8 3 (by decide)
  have fund : Pell.IsFundamental g := fundamental_from_residues (X:=8) (Y:=3) (m:=21)
    (by decide) (by decide) (by decide) (by decide +kernel)
  intro h
  have bad := pell_two_dvd_fundamental (g:=g) fund (t:=4) e h
  exact (by decide : ¬(2:ℤ)^4∣8) bad

theorem pell_twenty_three_no_sixteen {X Y : ℤ} (e : X^2-23*Y^2=1) : ¬(16:ℤ)∣X := by
  let g : Pell.Solution₁ 23 := Pell.Solution₁.mk 24 5 (by decide)
  have fund : Pell.IsFundamental g := fundamental_from_residues (X:=24) (Y:=5) (m:=184)
    (by decide) (by decide) (by decide) (by decide +kernel)
  intro h
  have bad := pell_two_dvd_fundamental (g:=g) fund (t:=4) e h
  exact (by decide : ¬(2:ℤ)^4∣24) bad

end

/-- The two explicit Gauss factorizations for the small prime exponents
congruent to seven modulo eight. -/
private theorem small_gauss_forms (u v : ℤ) :
    ((⟨u,1⟩ : Zsqrtd (-(v^2)))^7).im =
      7*(-u^3 - u*v^2)^2-(v*(7*u^2 - v^2))^2 ∧
    ((⟨u,1⟩ : Zsqrtd (-(v^2)))^23).im =
      23*(u^11 + 65*u^9*v^2 - 70*u^7*v^4 - 78*u^5*v^6 + 53*u^3*v^8 - 3*u*v^10)^2-(v*(-69*u^10 - 437*u^8*v^2 + 1150*u^6*v^4 - 506*u^4*v^6 + 23*u^2*v^8 - v^10))^2 := by
  let z : Zsqrtd (-(v^2)) := ⟨u,1⟩
  have h2 : z^2 = ⟨u^2 - v^2, 2*u⟩ := by
    calc
      z^2=z^1*z^1 := pow_add z 1 1
      _=_ := by
        rw [pow_one]
        apply Zsqrtd.ext <;> simp only [z,re_mul,im_mul] <;> ring
  have h3 : z^3 = ⟨u^3 - 3*u*v^2, 3*u^2 - v^2⟩ := by
    calc
      z^3=z^2*z^1 := pow_add z 2 1
      _=_ := by
        rw [h2,pow_one]
        apply Zsqrtd.ext <;> simp only [z,re_mul,im_mul] <;> ring
  have h4 : z^4 = ⟨u^4 - 6*u^2*v^2 + v^4, 4*u^3 - 4*u*v^2⟩ := by
    calc
      z^4=z^2*z^2 := pow_add z 2 2
      _=_ := by
        rw [h2]
        apply Zsqrtd.ext <;> simp only [re_mul,im_mul] <;> ring
  have h7 : z^7 = ⟨u^7 - 21*u^5*v^2 + 35*u^3*v^4 - 7*u*v^6, 7*u^6 - 35*u^4*v^2 + 21*u^2*v^4 - v^6⟩ := by
    calc
      z^7=z^4*z^3 := pow_add z 4 3
      _=_ := by
        rw [h4,h3]
        apply Zsqrtd.ext <;> simp only [re_mul,im_mul] <;> ring
  have h8 : z^8 = ⟨u^8 - 28*u^6*v^2 + 70*u^4*v^4 - 28*u^2*v^6 + v^8, 8*u^7 - 56*u^5*v^2 + 56*u^3*v^4 - 8*u*v^6⟩ := by
    calc
      z^8=z^4*z^4 := pow_add z 4 4
      _=_ := by
        rw [h4]
        apply Zsqrtd.ext <;> simp only [re_mul,im_mul] <;> ring
  have h16 : z^16 = ⟨u^16 - 120*u^14*v^2 + 1820*u^12*v^4 - 8008*u^10*v^6 + 12870*u^8*v^8 - 8008*u^6*v^10 + 1820*u^4*v^12 - 120*u^2*v^14 + v^16, 16*u^15 - 560*u^13*v^2 + 4368*u^11*v^4 - 11440*u^9*v^6 + 11440*u^7*v^8 - 4368*u^5*v^10 + 560*u^3*v^12 - 16*u*v^14⟩ := by
    calc
      z^16=z^8*z^8 := pow_add z 8 8
      _=_ := by
        rw [h8]
        apply Zsqrtd.ext <;> simp only [re_mul,im_mul] <;> ring
  constructor
  · change (z^7).im=_
    rw [h7]
    change 7*u^6 - 35*u^4*v^2 + 21*u^2*v^4 - v^6=_
    ring
  · change (z^23).im=_
    rw [show z^23=z^16*z^7 from pow_add z 16 7,h16,h7,im_mul]
    ring

/-- The Lucas coefficient cannot equal minus one at indices seven or
twenty-three for a shift 2^t with positive t divisible by three. -/
theorem exclude_small_lucas {u : ℤ} {n t : ℕ} (ht : 2≤t) (dt : 3∣t)
    (cases : n=7 ∨ n=23) (h : ((⟨u,1⟩ : Zsqrtd (-((2:ℤ)^t)^2))^n).im= -1) : False := by
  let v : ℤ := 2^t
  obtain ⟨seven,twentyThree⟩ := small_gauss_forms u v
  rcases cases with rfl|rfl
  · have eqn : 7*(-u^3 - u*v^2)^2-(v*(7*u^2 - v^2))^2 = -1 := seven.symm.trans h
    have pell : (v*(7*u^2 - v^2))^2-7*(-u^3 - u*v^2)^2=1 := by linarith only [eqn]
    have three : t=3 := by
      by_contra other
      have even : (16:ℤ)∣v := pow_dvd_pow (2:ℤ) (by omega : 4≤t)
      exact pell_seven_no_sixteen pell (even.trans (dvd_mul_right _ _))
    have shift : v=8 := by dsimp [v]; rw [three]; norm_num
    rw [shift] at eqn
    have modEq := congrArg (fun z : ℤ => (z:ZMod 11)) eqn
    push_cast at modEq
    have table : ∀ u : ZMod 11, 7*(-u^3 - u*8^2)^2-(8*(7*u^2 - 8^2))^2 ≠ -1 := by decide +kernel
    exact table _ modEq
  · have eqn : 23*(u^11 + 65*u^9*v^2 - 70*u^7*v^4 - 78*u^5*v^6 + 53*u^3*v^8 - 3*u*v^10)^2-(v*(-69*u^10 - 437*u^8*v^2 + 1150*u^6*v^4 - 506*u^4*v^6 + 23*u^2*v^8 - v^10))^2 = -1 := twentyThree.symm.trans h
    have pell : (v*(-69*u^10 - 437*u^8*v^2 + 1150*u^6*v^4 - 506*u^4*v^6 + 23*u^2*v^8 - v^10))^2-23*(u^11 + 65*u^9*v^2 - 70*u^7*v^4 - 78*u^5*v^6 + 53*u^3*v^8 - 3*u*v^10)^2=1 := by linarith only [eqn]
    have three : t=3 := by
      by_contra other
      have even : (16:ℤ)∣v := pow_dvd_pow (2:ℤ) (by omega : 4≤t)
      exact pell_twenty_three_no_sixteen pell (even.trans (dvd_mul_right _ _))
    have shift : v=8 := by dsimp [v]; rw [three]; norm_num
    rw [shift] at eqn
    have modEq := congrArg (fun z : ℤ => (z:ZMod 13)) eqn
    push_cast at modEq
    have table : ∀ u : ZMod 13, 23*(u^11 + 65*u^9*8^2 - 70*u^7*8^4 - 78*u^5*8^6 + 53*u^3*8^8 - 3*u*8^10)^2-(8*(-69*u^10 - 437*u^8*8^2 + 1150*u^6*8^4 - 506*u^4*8^6 + 23*u^2*8^8 - 8^10))^2 ≠ -1 := by decide +kernel
    exact table _ modEq

/-- The imaginary coordinate, after division by the original imaginary
coordinate, is the Lucas sequence with parameters 2u and u²+v². -/
theorem gaussian_lucas_recurrence (u v : ℤ) (j : ℕ) :
    let z : Zsqrtd (-(v^2)) := ⟨u,1⟩
    (z^(j+2)).im=2*u*(z^(j+1)).im-(u^2+v^2)*(z^j).im := by
  intro z
  rw [pow_succ z (j+1),pow_succ z j]
  simp only [im_mul,re_mul,z]
  ring

/-- An even-shift solution outside the known quartic would give a
nondegenerate integral Lucas sequence whose prime-index term is minus one
at an index above the Bilu–Hanrot–Voutier threshold. -/
theorem square_lucas_obstruction {x y k n : ℕ} (hx : x%2=1) (hy : y%2=1)
    (hk : 2<k) (hn : 2<n) (h : x^2+2^k=y^n) :
    (x=7 ∧ y=3 ∧ k=5 ∧ n=4) ∨
    (6∣k ∧ n.Prime ∧ 30<n ∧ n%8=7 ∧ 3∣x ∧
      ∃ P : ℤ, ∃ U : ℕ → ℤ, 1<(y:ℤ) ∧ IsCoprime P (y:ℤ) ∧
        (¬(y:ℤ)∣P^2) ∧ P^2<4*(y:ℤ) ∧ U 0=0 ∧ U 1=1 ∧
        (∀ j, U (j+2)=P*U (j+1)-(y:ℤ)*U j) ∧ U n= -1) := by
  rcases classify_square_shift hx hy hk hn h with ex|⟨d6,prime,rem,dx⟩
  · exact Or.inl ex
  right
  obtain ⟨l,hl⟩ := d6
  let t := 3*l
  have shift : k=2*t := by dsimp [t]; omega
  have ht : 2≤t := by omega
  have on : Odd n := Nat.odd_iff.mpr (by omega)
  have eqn : (x:ℤ)^2+(2:ℤ)^(2*t)=(y:ℤ)^n := by
    rw [←shift]
    exact_mod_cast h
  obtain ⟨_,_,dt,u,uo,_,ey,co⟩ := gaussian_witness (by exact_mod_cast Nat.odd_iff.mpr hx)
    (by exact_mod_cast Nat.odd_iff.mpr hy) ht on (by omega) eqn
  have large : 30<n := by
    by_contra! bound
    have n15 : n≠15 := by rintro rfl; norm_num at prime
    exact exclude_small_lucas ht dt (by omega) co
  let v : ℤ := 2^t
  let z : Zsqrtd (-(v^2)) := ⟨u,1⟩
  let U (j : ℕ) := (z^j).im
  have cop_two : IsCoprime u (2:ℤ) := by
    obtain ⟨a,e⟩ := uo
    exact ⟨1,-a,by rw [e]; ring⟩
  obtain ⟨a,b,comb⟩ := (cop_two.pow_right (n:=t)).pow_right (n:=2)
  have uc : IsCoprime u (y:ℤ) := ⟨a-b*u,b,by rw [ey]; linear_combination comb⟩
  have oy : Odd (y:ℤ) := by exact_mod_cast Nat.odd_iff.mpr hy
  have cp₂ : IsCoprime (2:ℤ) (y:ℤ) := Int.prime_two.irreducible.coprime_iff_not_dvd.mpr
    (fun q => (Int.not_even_iff_odd.mpr oy) (even_iff_two_dvd.mpr q))
  have cp := cp₂.mul_left uc
  have big : 4≤v := by
    change (2:ℤ)^2≤(2:ℤ)^t
    exact pow_le_pow_right₀ (by decide) ht
  change (y:ℤ)=u^2+v^2 at ey
  have ygt : 1<(y:ℤ) := by nlinarith [sq_nonneg u,sq_nonneg (v-2)]
  have no : ¬(y:ℤ)∣(2*u)^2 := by
    intro dvd
    have un := (cp.pow_left (m:=2)).symm.isUnit_of_dvd dvd
    rcases Int.isUnit_iff.mp un with e|e <;> omega
  refine ⟨⟨l,hl⟩,prime,large,rem,dx,2*u,U,ygt,cp,no,?_,rfl,by simp [U,z],?_,co⟩
  · nlinarith [sq_nonneg (v-2)]
  · intro j
    rw [ey]
    exact gaussian_lucas_recurrence u v j

/-- Classification for every odd-base equation with k,n>2 and n≤30. -/
theorem classify_square_through_thirty {x y k n : ℕ} (hx : x%2=1) (hy : y%2=1)
    (hk : 2<k) (hn : 2<n) (bound : n≤30) (h : x^2+2^k=y^n) :
    x=7 ∧ y=3 ∧ k=5 ∧ n=4 := by
  rcases square_lucas_obstruction hx hy hk hn h with ex|⟨_,_,large,_⟩
  · exact ex
  · omega

/-- The large-index prime-divisor conclusion of Bilu–Hanrot–Voutier in its
integer-recurrence formulation suffices for the remaining square case. -/
theorem classify_square_from_lucas_divisors
    (divisor : ∀ {P Q : ℤ} {U : ℕ → ℤ} {p : ℕ}, 1<Q → IsCoprime P Q →
      (¬Q∣P^2) → P^2<4*Q → p.Prime → 30<p → U 0=0 → U 1=1 →
      (∀ j, U (j+2)=P*U (j+1)-Q*U j) → ∃ l : ℕ, l.Prime ∧ (l:ℤ)∣U p)
    {x y k n : ℕ} (hx : x%2=1) (hy : y%2=1)
    (hk : 2<k) (hn : 2<n) (h : x^2+2^k=y^n) : x=7 ∧ y=3 ∧ k=5 ∧ n=4 := by
  rcases square_lucas_obstruction hx hy hk hn h with ex|⟨_,prime,large,_,_,P,U,big,cop,no,disc,h₀,h₁,rec,unit⟩
  · exact ex
  · obtain ⟨l,lp,ld⟩ := divisor big cop no disc prime large h₀ h₁ rec
    rw [unit,dvd_neg] at ld
    exact ((Nat.prime_iff_prime_int.mp lp).not_dvd_one ld).elim

section

open Polynomial

/-- A root-of-unity quotient would make P²/Q a rational algebraic integer,
forcing Q to divide P². -/
private theorem lucas_quotient_nonperiodic {P Q : ℤ} {a b : ℂ}
    (big : 1<Q) (nd : ¬Q∣P^2) (hs : a+b=(P:ℂ)) (hp : a*b=(Q:ℂ))
    {m : ℕ} (hm : 0 < m) : (a/b)^m≠1 := by
  intro root
  have q0 : (Q:ℂ)≠0 := by exact_mod_cast (by omega : Q≠0)
  have prod0 : a*b≠0 := hp ▸ q0
  obtain ⟨a0,b0⟩ := mul_ne_zero_iff.mp prod0
  have ir : IsIntegral ℤ (a/b) := .of_pow hm (root ▸ isIntegral_one)
  have back : (b/a)^m=1 := by rw [←inv_div,inv_pow,root,inv_one]
  have ib : IsIntegral ℤ (b/a) := .of_pow hm (back ▸ isIntegral_one)
  have two : IsIntegral ℤ (2:ℂ) := isIntegral_algebraMap (R:=ℤ) (x:=2)
  have eqn : a/b+b/a+2=(P:ℂ)^2/(Q:ℂ) := by
    rw [←hs,←hp]
    field_simp
    ring
  have ip : IsIntegral ℤ ((P:ℂ)^2/(Q:ℂ)) := eqn ▸ (ir.add ib).add two
  have rat : (∃ q : ℚ, (P:ℂ)^2/(Q:ℂ)=(q:ℂ)) :=
    ⟨(P:ℚ)^2/(Q:ℚ),by push_cast; rfl⟩
  obtain ⟨k,he⟩ := ip.exists_int_iff_exists_rat.mp rat
  have prod := (div_eq_iff q0).mp he
  exact nd ⟨k,by exact_mod_cast (prod.trans (mul_comm _ _))⟩

private theorem lucas_complex_terms {P Q : ℤ} {a b : ℂ} {U : ℕ → ℤ}
    (hs : a+b=(P:ℂ)) (hp : a*b=(Q:ℂ)) (h₀ : U 0=0) (h₁ : U 1=1)
    (rec : ∀ j, U (j+2)=P*U (j+1)-Q*U j) (j : ℕ) :
    a^j-b^j=(a-b)*(U j:ℂ) := by
  induction j using Nat.twoStepInduction with
  | zero => simp [h₀]
  | one => simp [h₁]
  | more j ih ih' =>
    rw [rec]
    push_cast
    calc
      _ = (a+b)*(a^(j+1)-b^(j+1))-(a*b)*(a^j-b^j) := by
        rw [pow_succ a (j+1),pow_succ b (j+1),pow_succ a j,pow_succ b j]
        ring
      _ = _ := by rw [ih',ih,hs,hp]; ring

/-- A complex Lucas pair with the integer recurrence parameters. -/
private theorem complex_lucas_pair {P Q : ℤ} (big : 1<Q) (nd : ¬Q∣P^2) :
    ∃ a b : ℂ, IsIntegral ℤ a ∧ IsIntegral ℤ b ∧ a+b=(P:ℂ) ∧ a*b=(Q:ℂ) ∧
      (∀ m : ℕ, 0 < m → (a/b)^m≠1) ∧ a≠b := by
  obtain ⟨d,hd⟩ := IsAlgClosed.exists_pow_nat_eq ((P:ℂ)^2-4*(Q:ℂ)) (by decide : 0<2)
  let a := ((P:ℂ)+d)/2
  let b := ((P:ℂ)-d)/2
  have hs : a+b=(P:ℂ) := by dsimp [a,b]; ring
  have hp : a*b=(Q:ℂ) := by dsimp [a,b]; linear_combination -hd/4
  have integral (w : ℂ) (root : w^2-(P:ℂ)*w+(Q:ℂ)=0) : IsIntegral ℤ w :=
    ⟨X^2-C P*X+C Q,(isMonicOfDegree_sub_add_two P Q).monic,by
      change eval₂ (Int.castRingHom ℂ) w (X^2-C P*X+C Q)=0
      simpa only [eval₂_add,eval₂_sub,eval₂_pow,eval₂_mul,eval₂_X,eval₂_C,Int.coe_castRingHom] using root⟩
  have ia := integral a (by rw [←hs,←hp]; ring)
  have ib := integral b (by rw [←hs,←hp]; ring)
  have nonperiodic (m : ℕ) (hm : 0 < m) := lucas_quotient_nonperiodic big nd hs hp hm
  refine ⟨a,b,ia,ib,hs,hp,nonperiodic,?_⟩
  intro e
  have b0 : b≠0 := by
    intro zero
    rw [zero,mul_zero] at hp
    have q0 : Q=0 := by exact_mod_cast hp.symm
    omega
  exact nonperiodic 1 (by decide) (by rw [e,div_self b0,one_pow])

/-- The prime-divisor conclusion for complex Lucas pairs, stated with the
standard quotient of powers, implies the full odd-base square classification. -/
theorem classify_square_from_lucas_pairs
    (divisor : ∀ {a b : ℂ} {P Q : ℤ} {p : ℕ}, IsIntegral ℤ a → IsIntegral ℤ b →
      a+b=(P:ℂ) → a*b=(Q:ℂ) → P≠0 → Q≠0 → IsCoprime P Q →
      (∀ m : ℕ, 0 < m → (a/b)^m≠1) → p.Prime → 30<p →
      ∃ l : ℕ, l.Prime ∧ ∃ c : ℤ, (a^p-b^p)/(a-b)=(l:ℂ)*(c:ℂ))
    {x y k n : ℕ} (hx : x%2=1) (hy : y%2=1)
    (hk : 2<k) (hn : 2<n) (h : x^2+2^k=y^n) : x=7 ∧ y=3 ∧ k=5 ∧ n=4 := by
  apply classify_square_from_lucas_divisors _ hx hy hk hn h
  intro P Q U p big cop nd _ hp large h₀ h₁ rec
  obtain ⟨a,b,ia,ib,hs,prod,np,hab⟩ := complex_lucas_pair big nd
  have p0 : P≠0 := by rintro rfl; simp at nd
  obtain ⟨l,prime,c,hc⟩ := divisor ia ib hs prod p0 (by omega) cop np hp large
  have hu : (a^p-b^p)/(a-b)=(U p:ℂ) := (div_eq_iff (sub_ne_zero.mpr hab)).mpr
    ((lucas_complex_terms hs prod h₀ h₁ rec p).trans (mul_comm _ _))
  exact ⟨l,prime,c,by exact_mod_cast hu.symm.trans hc⟩

end

/-- A square odd summand would give a Lucas term equal to minus one at a prime index above thirty. -/
theorem square_summand_lucas_restriction {b c p r k : ℕ} (hb : b%2=1) (hc : c%2=1)
    (hp : 2<p) (hr : 2<r) (hk : 2<k) (h : 2^k+b^p=c^r) :
    (Odd p ∧ ¬IsSquare b) ∨ (6 ∣ k ∧ r.Prime ∧ 30 < r ∧ r%8=7 ∧ 3 ∣ b ∧
      ∃ P : ℤ, ∃ U : ℕ → ℤ, 1<(c:ℤ) ∧ IsCoprime P (c:ℤ) ∧
        (¬(c:ℤ)∣P^2) ∧ P^2<4*(c:ℤ) ∧ U 0=0 ∧ U 1=1 ∧
        (∀ j, U (j+2)=P*U (j+1)-(c:ℤ)*U j) ∧ U r= -1) := by
  have on_square (u j : ℕ) (hj : 1<j) (hu : u%2=1) (he : (u^j)^2=b^p) :
      6 ∣ k ∧ r.Prime ∧ 30 < r ∧ r%8=7 ∧ 3 ∣ b ∧
      ∃ P : ℤ, ∃ U : ℕ → ℤ, 1<(c:ℤ) ∧ IsCoprime P (c:ℤ) ∧
        (¬(c:ℤ)∣P^2) ∧ P^2<4*(c:ℤ) ∧ U 0=0 ∧ U 1=1 ∧
        (∀ j, U (j+2)=P*U (j+1)-(c:ℤ)*U j) ∧ U r= -1 := by
    have hodd : (u^j)%2=1 := by rw [Nat.pow_mod,hu,one_pow]; decide
    have hh : (u^j)^2+2^k=c^r := by rw [he,Nat.add_comm]; exact h
    rcases square_lucas_obstruction hodd hc hk hr hh with ex|⟨d6,prime,large,rem,dx,witness⟩
    · have := (Nat.Prime.pow_eq_iff (by decide : Nat.Prime 7)).mp ex.1
      omega
    · have dvd : 3 ∣ b^p := he ▸ dx.trans (dvd_pow_self (u^j) (by decide : 2≠0))
      exact ⟨d6,prime,large,rem,Nat.prime_three.dvd_of_dvd_pow dvd,witness⟩
  rcases Nat.even_or_odd p with pe|po
  · obtain ⟨j,hj⟩ := pe
    exact Or.inr (on_square b j (by omega) hb (by rw [←pow_mul,hj]; congr 1; omega))
  by_cases sq : IsSquare b
  · obtain ⟨u,hu⟩ := sq
    have uo : u%2=1 := by
      rw [hu,Nat.mul_mod] at hb
      by_contra hno
      have e : u%2=0 := by omega
      simp [e] at hb
    exact Or.inr (on_square u p (by omega) uo (by rw [hu,mul_pow,pow_two]))
  · exact Or.inl ⟨po,sq⟩

/-- A square in the odd summand forces a multiple of six on two, a prime
congruent to seven modulo eight on the output, and a base divisible by three. -/
theorem square_summand_restriction {b c p r k : ℕ} (hb : b%2=1) (hc : c%2=1)
    (hp : 2<p) (hr : 2<r) (hk : 2<k) (h : 2^k+b^p=c^r) :
    (Odd p ∧ ¬IsSquare b) ∨ (6 ∣ k ∧ r.Prime ∧ r%8=7 ∧ 3 ∣ b) := by
  rcases square_summand_lucas_restriction hb hc hp hr hk h with ans|⟨d6,prime,_,rem,divides,_⟩
  · exact Or.inl ans
  · exact Or.inr ⟨d6,prime,rem,divides⟩

end BealQuadratic

section

private theorem exponent_factor {n : ℕ} (hn : 2<n) :
    ∃ p u : ℕ, n=u*p ∧ (p=4 ∨ (p.Prime ∧ 2<p)) := by
  by_cases h4 : 4 ∣ n
  · obtain ⟨u,hu⟩ := h4
    exact ⟨4,u,by omega, Or.inl rfl⟩
  let m := if 2 ∣ n then n/2 else n
  have hm : 1 < m := by dsimp [m]; split <;> omega
  have hm2 : ¬2 ∣ m := by dsimp [m]; split <;> omega
  have hmn : m ∣ n := by
    dsimp [m]; split
    · exact ⟨2,by omega⟩
    · exact dvd_refl _
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd hm.ne'
  obtain ⟨u,hu⟩ := hd.trans hmn
  refine ⟨p,u,hu.trans (Nat.mul_comm _ _),Or.inr ⟨hp,?_⟩⟩
  have hp2 : p≠2 := by rintro rfl; exact hm2 hd
  have := hp.two_le
  omega

private theorem bases_coprime {b c p r k : ℕ} (hb : b%2=1) (hp : 0<p) (hr : 0<r)
    (h : 2^k+b^p=c^r) : b.Coprime c := by
  apply Nat.coprime_of_dvd
  intro l hl hb' hc'
  have hx : l ∣ b^p := hb'.trans (dvd_pow_self _ hp.ne')
  have hz : l ∣ c^r := hc'.trans (dvd_pow_self _ hr.ne')
  have h₂ : l ∣ 2^k := (Nat.dvd_add_iff_left hx).mpr (h ▸ hz)
  have hl₂ := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow h₂)
  subst l
  omega

private theorem square_gap {b c p r k : ℕ} (hb : b%2=1) (hc : c%2=1)
    (hp : 2<p) (hk : 2<k) (cop : p.Coprime r) (eqn : 2^k+b^p=c^r) :
    k%2=1 ∨ r%2=1 := by
  by_contra! h
  let v := 2^(k/2)
  let u := c^(r/2)
  have hv : v%2=0 := by
    dsimp [v]; rw [Nat.pow_mod]; simp [Nat.zero_pow (show 0<k/2 by omega)]
  have hu : u%2=1 := BealTwoPower.odd_pow hc _
  have he : v^2+b^p=u^2 := by
    dsimp only [v,u]; rw [←pow_mul,←pow_mul,show k/2*2=k by omega,show r/2*2=r by omega]
    exact eqn
  have hlt : v<u := by
    apply (Nat.pow_lt_pow_iff_left (by decide : 2≠0)).mp
    have := Nat.pow_pos (n:=p) (show 0<b by omega)
    omega
  let d := u-v
  let e := u+v
  have hde : e=d+2^(k/2+1) := by dsimp only [e,d]; rw [pow_succ]; change u+v=u-v+v*2; omega
  have hd : d%2=1 := by dsimp [d]; omega
  have hprod : d*e=b^p := by
    have hu' : u = d+v := by dsimp [d]; omega
    dsimp only [e]; rw [hu'] at he ⊢; nlinarith
  have hcop : d.Coprime e := by
    apply Nat.coprime_of_dvd
    intro l hl hld hle
    have hv' : l ∣ 2^(k/2+1) := (Nat.dvd_add_iff_right hld).mpr (hde ▸ hle)
    have hl₂ := (Nat.prime_dvd_prime_iff_eq hl Nat.prime_two).mp (hl.dvd_of_dvd_pow hv')
    subst l
    omega
  obtain ⟨s,hs⟩ := exists_eq_pow_of_mul_eq_pow
    (gcd_isUnit_iff_isRelPrime.mpr (Nat.coprime_iff_isRelPrime.mp hcop)) hprod
  obtain ⟨t,ht⟩ := exists_eq_pow_of_mul_eq_pow
    (gcd_isUnit_iff_isRelPrime.mpr (Nat.coprime_iff_isRelPrime.mp hcop.symm)) ((Nat.mul_comm _ _).trans hprod)
  have heodd : e%2=1 := by dsimp [e]; omega
  have hsp : s%2=1 := by rw [hs,BealTwoPower.parity_pow (by omega : 0<p)] at hd; exact hd
  have htp : t%2=1 := by rw [ht,BealTwoPower.parity_pow (by omega : 0<p)] at heodd; exact heodd
  have hodd : p%2=1 := by
    by_contra hne
    have := Nat.dvd_gcd (show 2 ∣ p by omega) (show 2 ∣ r by omega)
    change p.gcd r = 1 at cop
    omega
  have hst : s<t := by
    apply lt_of_not_ge
    intro hle
    have := Nat.pow_le_pow_left hle p
    have := Nat.two_pow_pos (k/2+1)
    omega
  apply BealPartial.odd_power_difference htp hsp hst (by omega) hodd (k/2+1)
  rw [←hs,←ht,hde,Nat.add_sub_cancel_left]

/-- At k = 69t + 1, writing the right side as twice the 23rd power of 2^(3t)
gives the coefficient-two equation. The two divisibility cases give equal exponents. -/
private theorem mixed (repeated : H2) (weighted : H3) (sieve : H4) {a b : ℤ} {k : ℕ}
    (ha : Odd a) (hb : Odd b) (hc : IsCoprime a b) (hk : 2<k) :
    a^3+b^23 ≠ (2:ℤ)^k := by
  intro he
  have cop₂ (x : ℤ) (hx : Odd x) (m : ℕ) : IsCoprime ((2:ℤ)^m) (-x) := by
    apply IsCoprime.pow_left
    apply Int.prime_two.irreducible.coprime_iff_not_dvd.mpr
    exact fun h => (Int.not_even_iff_odd.mpr hx.neg) (even_iff_two_dvd.mpr h)
  have han : a≠0 := by rintro rfl; simp at ha
  have hbn : b≠0 := by rintro rfl; simp at hb
  rcases (sieve (a:=a) (b:=b) (k:=k)).1 hc he with h | h | h
  · obtain ⟨m,rfl⟩ := h
    have hh := (repeated (X:=2^m) (Y:=-a) (Z:=b) (by positivity) (neg_ne_zero.mpr han) hbn (cop₂ a ha m)).1
    apply hh
    rw [←pow_mul,Nat.mul_comm m 3]
    linear_combination -he
  · obtain ⟨m,rfl⟩ := h
    have hh := (repeated (X:=2^m) (Y:=-b) (Z:=a) (by positivity) (neg_ne_zero.mpr hbn) han (cop₂ b hb m)).2
    apply hh
    rw [←pow_mul,Nat.mul_comm m 23]
    linear_combination -he
  · let t := k/69
    have ht : 0<t := by dsimp [t]; omega
    apply weighted (t:=t) (Y:=-b) (Z:=a) ht hb.neg ha
    have he' : (2:ℤ)^k = 2*((2:ℤ)^(3*t))^23 := by
      rw [show k = (3*t)*23+1 by dsimp [t]; omega,pow_succ,pow_mul,mul_comm]
    rw [he'] at he
    linear_combination -he

end

private theorem prime_square_not_high_power {v c r : ℕ} (hv : v.Prime) (hr : 2<r) : c^r≠v^2 := by
  intro h
  have dv : c∣v^2 := h ▸ dvd_pow_self _ (by omega)
  obtain ⟨j,_,cj⟩ := (Nat.dvd_prime_pow hv).mp dv
  rw [cj,←pow_mul] at h
  have jr := (Nat.pow_right_inj hv.one_lt).mp h
  by_cases zero : j=0
  · rw [zero] at jr; omega
  have bound := Nat.mul_le_mul_right r (show 1≤j by omega)
  omega

private theorem pow_parity {b n : ℕ} (hn : 0<n) : b^n%2=b%2 := by
  rw [Nat.pow_mod]
  rcases Nat.mod_two_eq_zero_or_one b with e|e <;> rw [e] <;> simp [hn.ne']

/-- For a dyadic summand, the other two terms cannot be respectively
a cube and a square in either order, even if their displayed exponents
are odd primes and the powers occur in the bases. -/
private theorem mixed_power_restrictions (sieve : H4) {b c p r k : ℕ} (hb : b%2=1) (hc : c%2=1)
    (hr : 2<r) (hk : 2<k) (eqn : 2^k+b^p=c^r) :
    (∀ d u : ℕ, b^p=d^3 → c^r≠u^2) ∧ (∀ u d : ℕ, b^p=u^2 → c^r≠d^3) := by
  have bp : b^p%2=1 := by rw [Nat.pow_mod,hb]; simp
  have cr : c^r%2=1 := by rw [Nat.pow_mod,hc]; simp
  constructor
  · intro d u cube square
    rw [cube,pow_parity (by decide : 0<3)] at bp
    rw [square,pow_parity (by decide : 0<2)] at cr
    rw [cube,square,Nat.add_comm] at eqn
    have zo : Odd (-(d:ℤ)) := (show Odd (d:ℤ) by exact_mod_cast (Nat.odd_iff.mpr bp)).neg
    have uo : Odd (u:ℤ) := by exact_mod_cast (Nat.odd_iff.mpr cr)
    have base : (d:ℤ)^3+(2:ℤ)^k=(u:ℤ)^2 := by exact_mod_cast eqn
    have signed : (-(d:ℤ))^3+(u:ℤ)^2=(2:ℤ)^k := by linarith
    rcases (sieve (a:= -(d:ℤ)) (b:=(u:ℤ)) (k:=k)).2 zo uo hk signed with ⟨bad,_,_⟩|⟨_,eu,_⟩|⟨_,eu,_⟩
    · omega
    · have ue : u=3 := by simpa using eu
      rw [ue] at square
      exact prime_square_not_high_power (by decide : Nat.Prime 3) hr square
    · have ue : u=71 := by simpa using eu
      rw [ue] at square
      exact prime_square_not_high_power (by decide : Nat.Prime 71) hr square
  · intro u d square cube
    rw [square,pow_parity (by decide : 0<2)] at bp
    rw [cube,pow_parity (by decide : 0<3)] at cr
    rw [square,cube,Nat.add_comm] at eqn
    have := BealQuadratic.classify_square_through_thirty bp cr hk (by decide : 2<3) (by decide) eqn
    omega

theorem main : H1 → H2 → H3 → H4 → OMA.R_BealConjecture_beal_conjecture_R2.H2 := by
  intro rest repeated weighted sieve b c y z k hb hc hy hz hk cop h
  obtain ⟨p,u,hy',hp⟩ := exponent_factor hy
  obtain ⟨r,v,hz',hr⟩ := exponent_factor hz
  have hp' : 2<p := hp.elim (fun e => by omega) And.right
  have hr' : 2<r := hr.elim (fun e => by omega) And.right
  change y.Coprime z at cop
  have hd₁ : p ∣ y := ⟨u,hy'.trans (Nat.mul_comm _ _)⟩
  have hd₂ : r ∣ z := ⟨v,hz'.trans (Nat.mul_comm _ _)⟩
  have hpr := Nat.Coprime.coprime_dvd_right hd₂ (Nat.Coprime.coprime_dvd_left hd₁ cop)
  rw [hy',hz',pow_mul,pow_mul] at h
  have hbo := BealTwoPower.odd_pow hb u
  have hco := BealTwoPower.odd_pow hc v
  have hbase := bases_coprime hbo (by omega : 0<p) (by omega : 0<r) h
  have hor := square_gap hbo hco hp' hk hpr h
  have hbz : Odd ((b^u:ℕ):ℤ) := by exact_mod_cast (Nat.odd_iff.mpr hbo)
  have hcz : Odd ((c^v:ℕ):ℤ) := by exact_mod_cast (Nat.odd_iff.mpr hco)
  let B : ℤ := ((b^u:ℕ):ℤ)
  let C : ℤ := ((c^v:ℕ):ℤ)
  have he : (2:ℤ)^k+B^p=C^r := by dsimp only [B,C]; exact_mod_cast h
  have hBC : IsCoprime B C := hbase.isCoprime
  by_cases h₁ : p=3 ∧ r=23
  · obtain ⟨rfl,rfl⟩ := h₁
    apply mixed repeated weighted sieve hbz.neg hcz (hBC.neg_left) hk (a := -B) (b := C)
    linear_combination -he
  by_cases h₂ : p=23 ∧ r=3
  · obtain ⟨rfl,rfl⟩ := h₂
    apply mixed repeated weighted sieve hcz hbz.neg hBC.symm.neg_right hk (a := C) (b := -B)
    linear_combination -he
  have restrictions := mixed_power_restrictions sieve hbo hco hr' hk h
  exact rest hbo hco hbase hpr hp hr hk hor
    (BealQuadratic.square_summand_lucas_restriction hbo hco hp' hr' hk h)
    restrictions.1 restrictions.2 (by omega) (by omega) h

end OMA.R_BealConjecture_beal_conjecture_R2_H2_R1

