import OMAReductions.R_BealConjecture_beal_conjecture_R1_H2_R2
import Mathlib

/-!
# Output bases of primitive quartic sums

For a primitive solution of a⁴+b⁴=cᵖ, Gaussian factorization gives
a²+i b²=(u+i v)ᵖ. Each coordinate of the root, in absolute value, is
a square or p times a square. At most one coordinate contains p.
The two hypotheses retain only the resulting shapes of c. Lebesgue's
square-plus-one argument excludes a unit input. See V.-A. Lebesgue (1850),
https://www.numdam.org/item/NAM_1850_1_9__178_0/.

The coprimality argument for the Gaussian factors extends the cubic
argument of @ubuwaits in the parent reduction. This special signature is
covered in the literature by Bennett, Ellenberg and Ng, The Diophantine
equation A⁴+2^δ B²=Cⁿ. No theorem from that paper is assumed here.
-/

namespace OMA.R_BealConjecture_beal_conjecture_R1_H2_R2_H2_R1

def H1 : Prop :=
  ∀ {a b s t p : ℕ}, 1<a → 1<b → 0<s → 0<t → a.Coprime b →
    s.Coprime t → p.Prime → 5≤p → (p%4=1 ∨ 5 ∣ a*b) → a^4+b^4 ≠ (s^4+t^4)^p

def H2 : Prop :=
  ∀ {a b s t p : ℕ}, 1<a → 1<b → 0<s → 0<t → a.Coprime b →
    s.Coprime t → p.Prime → 5≤p → p ∣ a*b → ¬p ∣ t →
    (p%4=1 ∨ 5 ∣ a*b) → a^4+b^4 ≠ (p^2*s^4+t^4)^p

namespace QuarticOutput

open Zsqrtd

private theorem fourth_of_unit (e : GaussianIntˣ) : (e:GaussianInt)^4=1 := by
  have prove (v : GaussianInt) (h : IsUnit v) : v^4=1 := by
    obtain ⟨a,b⟩ := v
    have n := (norm_eq_one_iff' (by decide) (⟨a,b⟩:GaussianInt)).mpr h
    change a*a-(-1)*b*b=1 at n
    have al : -1≤a := by nlinarith [sq_nonneg b]
    have ar : a≤1 := by nlinarith [sq_nonneg b]
    have bl : -1≤b := by nlinarith [sq_nonneg a]
    have br : b≤1 := by nlinarith [sq_nonneg a]
    interval_cases a <;> interval_cases b <;> norm_num at n <;> decide
  exact prove e e.isUnit

private theorem gaussian_root {a b c p : ℕ} (cop : a.Coprime b) (hp : Odd p)
    (bound : 2≤p) (eq : a^4+b^4=c^p) :
    ∃ w : GaussianInt, w^p=⟨(a:ℤ)^2,(b:ℤ)^2⟩ ∧ c=w.re.natAbs^2+w.im.natAbs^2 := by
  let _ := IsBezout.toGCDDomain GaussianInt
  let z : GaussianInt := ⟨(a:ℤ)^2,(b:ℤ)^2⟩
  have co : c%2=1 := by
    by_contra! even
    have dvd : 2 ∣ c := by omega
    have four : 4 ∣ c^p := (pow_dvd_pow_of_dvd dvd 2).trans (pow_dvd_pow c bound)
    have zero : (a:ZMod 4)^4+(b:ZMod 4)^4=0 := by
      exact_mod_cast (show ((a^4+b^4:ℕ):ZMod 4)=0 by
        rw [eq]; exact (ZMod.natCast_eq_zero_iff _ _).mpr four)
    have tab : ∀ x y : ZMod 4, x^4+y^4=0 → x.val%2=0 ∧ y.val%2=0 := by decide +kernel
    have bad := tab _ _ zero
    simp only [ZMod.val_natCast,Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 4)] at bad
    exact Nat.prime_two.not_dvd_one (cop.gcd_eq_one ▸ Nat.dvd_gcd
      (Nat.dvd_of_mod_eq_zero bad.1) (Nat.dvd_of_mod_eq_zero bad.2))
  have cp : IsCoprime ((a:ℤ)^2) ((b:ℤ)^2) := (cop.isCoprime.pow_left).pow_right
  have co2 : IsCoprime ((c:GaussianInt)^p) (2:GaussianInt) := by
    have hc := (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr co)).isCoprime
    simpa using (hc.pow_left (m:=p)).map (Int.castRingHom GaussianInt)
  have norm : z.norm=(c:ℤ)^p := by
    have e : (a:ℤ)^4+(b:ℤ)^4=(c:ℤ)^p := by exact_mod_cast eq
    simp only [norm_def,z]
    linear_combination e
  have fac : z*star z=(c:GaussianInt)^p := by rw [←norm_eq_mul_conj,norm,Int.cast_pow]; rfl
  have sum : z+star z=2*(a:GaussianInt)^2 := by
    apply Zsqrtd.ext <;> simp [z,re_mul,im_mul,pow_two]
    ring
  have diff : (z-star z)*(⟨0,-1⟩:GaussianInt)=2*(b:GaussianInt)^2 := by
    apply Zsqrtd.ext <;> simp [z,re_mul,im_mul,pow_two]
    ring
  have rel : IsRelPrime z (star z) := by
    intro d dz ds
    apply co2.isRelPrime
    · rw [←fac]; exact dz.trans (dvd_mul_right _ _)
    · have da : d ∣ 2*(a:GaussianInt)^2 := sum ▸ dvd_add dz ds
      have db : d ∣ 2*(b:GaussianInt)^2 := diff ▸ (dvd_sub dz ds).trans (dvd_mul_right _ _)
      have cpG : IsCoprime ((a:GaussianInt)^2) ((b:GaussianInt)^2) := by
        simpa using cp.map (Int.castRingHom GaussianInt)
      obtain ⟨u,v,e⟩ := cpG
      have two : (2:GaussianInt)=u*(2*(a:GaussianInt)^2)+v*(2*(b:GaussianInt)^2) := by
        linear_combination -2*e
      rw [two]
      exact dvd_add (dvd_mul_of_dvd_right da _) (dvd_mul_of_dvd_right db _)
  obtain ⟨d,e,he⟩ := exists_associated_pow_of_mul_eq_pow (gcd_isUnit_iff_isRelPrime.mpr rel) fac
  let w := d*(e:GaussianInt)^p
  have eroot : ((e:GaussianInt)^p)^p=e := by
    obtain ⟨k,rfl⟩ := hp
    rw [←pow_mul,show (2*k+1)*(2*k+1)=4*(k*k+k)+1 by ring,pow_succ,pow_mul,
      fourth_of_unit,one_pow,one_mul]
  have power : w^p=z := by simpa only [w,mul_pow,eroot] using he
  have norms : w.norm^p=(c:ℤ)^p := by
    change (normMonoidHom w)^p=_
    rw [←map_pow,power]
    exact norm
  have nats := congrArg Int.natAbs norms
  simp only [Int.natAbs_pow,Int.natAbs_natCast] at nats
  refine ⟨w,power,?_⟩
  rw [←Nat.pow_left_injective (by omega : p≠0) nats, GaussianInt.natAbs_norm_eq, sq, sq]

private theorem first_order {R : Type*} [CommRing R] (x y : R) (n : ℕ) :
    ∃ d : R, (x+y)^(n+1)=x^(n+1)+(n+1:R)*x^n*y+y^2*d := by
  induction n with
  | zero => exact ⟨0,by simp⟩
  | succ n ih =>
    obtain ⟨d,hd⟩ := ih
    refine ⟨(n+1:R)*x^n+(x+y)*d,?_⟩
    rw [pow_succ (x+y) (n+1),hd]
    push_cast
    ring

private theorem coordinate_factors (w : GaussianInt) (k : ℕ) :
    ∃ l m : ℤ,
      (w^(2*k+1)).re=w.re*((2*k+1:ℤ)*(-w.im^2)^k+w.re*l) ∧
      (w^(2*k+1)).im=w.im*((2*k+1:ℤ)*w.re^(2*k)+w.im*m) := by
  let x : GaussianInt := (w.re:GaussianInt)
  let y : GaussianInt := ⟨0,w.im⟩
  have decomp : x+y=w := by apply Zsqrtd.ext <;> simp [x,y]
  have ysq : y^2=((-w.im^2:ℤ):GaussianInt) := by
    apply Zsqrtd.ext <;> simp [y,sq,re_mul,im_mul]
  have yp : y^(2*k)=(((-w.im^2)^k:ℤ):GaussianInt) := by rw [pow_mul,ysq,Int.cast_pow]
  obtain ⟨l,hl⟩ := first_order y x (2*k)
  obtain ⟨m,hm⟩ := first_order x y (2*k)
  rw [add_comm y x,decomp,pow_succ y,yp] at hl
  rw [decomp,ysq] at hm
  refine ⟨l.re,-m.im,?_,?_⟩
  · have e := congrArg Zsqrtd.re hl
    simp only [x,y,←Int.cast_pow, re_add,im_add,re_one,im_one,re_mul,im_mul,re_natCast,im_natCast,
      re_intCast,im_intCast] at e
    push_cast at e
    linear_combination e
  · have e := congrArg Zsqrtd.im hm
    simp only [x,y,←Int.cast_pow, im_add,re_add,re_one,im_one,im_mul,re_mul,re_natCast,im_natCast,
      re_intCast,im_intCast] at e
    push_cast at e
    linear_combination e

private theorem mul_coords (a b c d : ℤ) :
    Zsqrtd.mk (d := -1) a b * Zsqrtd.mk (d := -1) c d = Zsqrtd.mk (d := -1) (a*c-b*d) (a*d+b*c) := by
  apply Zsqrtd.ext <;> dsimp
  ring

/-- Squaring doubles the scale of the first nonzero real correction. Its
coefficient stays odd, which prevents cancellation in the last multiplication. -/
private theorem even_power_shape (h : ℤ) (k : ℕ) (hk : 0 < k) :
    ∃ s a b : ℤ, 0 < s ∧ (Zsqrtd.mk (d := -1) 1 (2*h))^(2*k) =
      Zsqrtd.mk (d := -1) (1+4*s*h^2*(2*a+1)) (4*s*h*b) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases one : k=1
    · subst k
      refine ⟨1,-1,1,by decide,?_⟩
      rw [show 2*1=2 by decide,sq (Zsqrtd.mk (d := -1) 1 (2*h)),mul_coords]
      apply Zsqrtd.ext <;> dsimp <;> ring
    · let m := k/2
      have hm : 0 < m := by dsimp [m]; omega
      obtain ⟨s,a,b,hs,old⟩ := ih m (by dsimp [m]; omega) hm
      let A := a+s*(h^2*(2*a+1)^2-b^2)
      let B := b*(1+4*s*h^2*(2*a+1))
      have dbl : (Zsqrtd.mk (d := -1) 1 (2*h))^(2*(2*m)) =
          Zsqrtd.mk (d := -1) (1+4*(2*s)*h^2*(2*A+1)) (4*(2*s)*h*B) := by
        rw [show 2*(2*m)=(2*m)*2 by omega,pow_mul,old,sq,mul_coords]
        dsimp [A,B]
        congr 1 <;> ring
      have halves : k=2*m ∨ k=2*m+1 := by dsimp [m]; omega
      rcases halves with eq | eq
      · exact ⟨2*s,A,B,by omega,eq ▸ dbl⟩
      · refine ⟨1,s*(2*A+1)*(1-4*h^2)-1-4*s*B,
            1+8*s*h^2*(2*A+1)+2*s*B*(1-4*h^2),by decide,?_⟩
        rw [show 2*k=2*(2*m)+2 by omega,pow_add,dbl,sq (Zsqrtd.mk (d := -1) 1 (2*h)),mul_coords,mul_coords]
        congr 1 <;> ring

private theorem odd_power_real {h : ℤ} (hh : h ≠ 0) {k : ℕ} (hk : 0 < k) :
    let w := (Zsqrtd.mk (d := -1) 1 (2*h))^(2*k+1)
    w.re ≠ 1 ∧ w.re ≠ -1 := by
  obtain ⟨s,a,b,hs,shape⟩ := even_power_shape h k hk
  rw [pow_succ,shape,mul_coords]
  dsimp
  have hn : 2*a+1-2*b ≠ 0 := by omega
  have realpart : (1+4*s*h^2*(2*a+1))*1-4*s*h*b*(2*h) =
      1+4*(s*h^2*(2*a+1-2*b)) := by ring
  rw [realpart]
  have : s*h^2*(2*a+1-2*b) ≠ 0 := mul_ne_zero (mul_ne_zero (by omega) (pow_ne_zero _ hh)) hn
  omega

private theorem even_of_square_plus_one {x y n : ℕ} (hn : 2 ≤ n) (eq : x^2+1=y^n) :
    Even x := by
  obtain ⟨t,xt | xt⟩ := Nat.even_or_odd' x
  · exact ⟨t,by omega⟩
  · subst x
    have form : (2*t+1)^2+1=4*(t^2+t)+2 := by ring
    have ey : Even y := (Nat.even_pow' (by omega : n ≠ 0)).mp
      ⟨2*(t^2+t)+1,by omega⟩
    have two : 2 ∣ y := even_iff_two_dvd.mp ey
    have four : 4 ∣ y^n := (pow_dvd_pow_of_dvd two 2).trans (pow_dvd_pow y hn)
    omega

/-- The 2-adic argument of Lebesgue excludes a unit input. The Gaussian
root is the same one used for the two output forms above. -/
private theorem unit_left {b c p : ℕ} (hb : 0<b) (prime : p.Prime) (bound : 5≤p)
    (eq : 1^4+b^4=c^p) : False := by
  let x := b^2
  have hx : 0<x := Nat.pow_pos hb
  have h : x^2+1=c^p := by dsimp [x]; linear_combination eq
  have ex := even_of_square_plus_one (by omega) h
  have odd := prime.odd_of_ne_two (by omega)
  obtain ⟨z,power,_⟩ := gaussian_root (a:=1) (by simp) odd (by omega) eq
  obtain ⟨k,pk⟩ := odd
  have hk : 0<k := by omega
  have hz : z^(2*k+1)=Zsqrtd.mk (d := -1) 1 (x:ℤ) := by
    simpa [pk,x] using power
  obtain ⟨l,_,re,_⟩ := coordinate_factors z k
  rw [hz] at re
  have div : z.re ∣ 1 := ⟨_,re⟩
  have signs := Int.isUnit_iff.mp (isUnit_of_dvd_one div)
  have norm : z.norm^(2*k+1) = 1+(x:ℤ)^2 := by
    change (Zsqrtd.normMonoidHom z)^(2*k+1) = _
    rw [←map_pow,hz]
    change 1*1-(-1:ℤ)*(x:ℤ)*(x:ℤ) = _
    ring
  have normOdd : Odd z.norm := (Int.odd_pow' (by omega : 2*k+1 ≠ 0)).mp (by
    obtain ⟨j,hj⟩ := ex
    rw [norm,hj]
    exact ⟨2*(j:ℤ)^2,by push_cast; ring⟩)
  have eb : Even z.im := by
    obtain ⟨j,even | odd⟩ := Int.even_or_odd' z.im
    · exact ⟨j,by omega⟩
    · obtain ⟨t,ht⟩ := normOdd
      change z.re*z.re-(-1)*z.im*z.im=2*t+1 at ht
      rcases signs with unit | unit <;> rw [unit,odd] at ht <;> ring_nf at ht <;> omega
  obtain ⟨h,hh⟩ := eb
  have him : z.im=2*h := by omega
  have hne : h ≠ 0 := by
    rintro rfl
    have zeq : z=(z.re:GaussianInt) := Zsqrtd.ext (by simp) (by simp [him])
    have bad := congrArg Zsqrtd.im hz
    rw [zeq,←Int.cast_pow,Zsqrtd.im_intCast] at bad
    change 0=(x:ℤ) at bad
    omega
  rcases signs with pos | neg
  · have zeq : z=Zsqrtd.mk (d := -1) 1 (2*h) := Zsqrtd.ext pos him
    exact (odd_power_real hne hk).1 (by rw [←zeq,hz])
  · have zeq : -z=Zsqrtd.mk (d := -1) 1 (2*(-h)) :=
      Zsqrtd.ext (by change -z.re=1; omega) (by change -z.im=2*(-h); omega)
    apply (odd_power_real (neg_ne_zero.mpr hne) hk).2
    rw [←zeq,(show Odd (2*k+1) from ⟨k,rfl⟩).neg_pow,hz]
    rfl

private theorem small_gcd {x f j l : ℤ} {p : ℕ} (cop : x.natAbs.Coprime j.natAbs)
    (eq : f=(p:ℤ)*j+x*l) : x.natAbs.gcd f.natAbs ∣ p := by
  let d := x.gcd f
  have first : (d:ℤ) ∣ x := Int.gcd_dvd_left _ _
  have second : (d:ℤ) ∣ f := Int.gcd_dvd_right _ _
  have product : (d:ℤ) ∣ (p:ℤ)*j := by
    rw [show (p:ℤ)*j=f-x*l by linarith]
    exact dvd_sub second (dvd_mul_of_dvd_left first _)
  have natural : d ∣ p*j.natAbs := by
    simpa [Int.natAbs_mul] using Int.natAbs_dvd_natAbs.mpr product
  exact (cop.coprime_dvd_left (Nat.gcd_dvd_left _ _)).dvd_of_dvd_mul_right natural

private theorem square_factor {u f a : ℕ} (hu : 0<u) (eq : u*f=a^2) :
    ∃ r : ℕ, 0<r ∧ u=u.gcd f*r^2 := by
  let d := u.gcd f
  have du : d ∣ u := Nat.gcd_dvd_left _ _
  have df : d ∣ f := Nat.gcd_dvd_right _ _
  have dp : 0<d := Nat.gcd_pos_of_pos_left _ hu
  have da : d ∣ a := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp
    (by rw [←eq,pow_two]; exact mul_dvd_mul du df)
  have cu := Nat.div_mul_cancel du
  have cf := Nat.div_mul_cancel df
  have ca := Nat.div_mul_cancel da
  have reduced : (u/d)*(f/d)=(a/d)^2 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (n:=2) dp)
    calc
      (u/d)*(f/d)*d^2 = (u/d*d)*(f/d*d) := by ring
      _ = a^2 := by rw [cu,cf,eq]
      _ = (a/d)^2*d^2 := by rw [←mul_pow,ca]
  have cop : (u/d).Coprime (f/d) := Nat.coprime_div_gcd_div_gcd dp
  obtain ⟨r,hr⟩ := exists_eq_pow_of_mul_eq_pow
    (gcd_isUnit_iff_isRelPrime.mpr (Nat.coprime_iff_isRelPrime.mp cop)) reduced
  have form : u=d*r^2 := by rw [←hr,Nat.mul_comm,cu]
  refine ⟨r,?_,form⟩
  by_contra! zero
  simp [show r=0 by omega] at form
  omega

/-- The two coordinates of the Gaussian root have disjoint prime support.
Each is a square times a divisor of p, so the exceptional factor p occurs
in at most one of them. -/
theorem output_shapes {a b c p : ℕ} (ha : 0<a) (hb : 0<b) (cop : a.Coprime b)
    (prime : p.Prime) (hp : 5≤p) (eq : a^4+b^4=c^p) :
    ∃ s t : ℕ, 0<s ∧ 0<t ∧ s.Coprime t ∧
      (c=s^4+t^4 ∨ (c=p^2*s^4+t^4 ∧ p ∣ a*b ∧ ¬p ∣ t)) := by
  have odd := prime.odd_of_ne_two (by omega)
  obtain ⟨w,power,norm⟩ := gaussian_root cop odd (by omega) eq
  obtain ⟨k,pk⟩ := odd
  obtain ⟨l,m,re,im⟩ := coordinate_factors w k
  rw [←pk,power] at re im
  let u := w.re
  let v := w.im
  let f := (p:ℤ)*(-v^2)^k+u*l
  let g := (p:ℤ)*u^(2*k)+v*m
  have pkz : (p:ℤ)=2*(k:ℤ)+1 := by exact_mod_cast pk
  have rr : (a:ℤ)^2=u*f := by simpa only [u,v,f,pkz] using re
  have ii : (b:ℤ)^2=v*g := by simpa only [u,v,g,pkz] using im
  have ab : u.natAbs*f.natAbs=a^2 := by simpa [Int.natAbs_mul] using congrArg Int.natAbs rr.symm
  have bb : v.natAbs*g.natAbs=b^2 := by simpa [Int.natAbs_mul] using congrArg Int.natAbs ii.symm
  have ud : u.natAbs ∣ a^2 := ⟨_,ab.symm⟩
  have vd : v.natAbs ∣ b^2 := ⟨_,bb.symm⟩
  have uv : u.natAbs.Coprime v.natAbs := ((cop.pow_left 2).pow_right 2).coprime_dvd_left ud
    |>.coprime_dvd_right vd
  have up : 0<u.natAbs := by
    by_contra! h
    simp [show u.natAbs=0 by omega] at ab
    exact (Nat.pow_pos (n:=2) ha).ne ab
  have vp : 0<v.natAbs := by
    by_contra! h
    simp [show v.natAbs=0 by omega] at bb
    exact (Nat.pow_pos (n:=2) hb).ne bb
  have df : u.natAbs.gcd f.natAbs ∣ p := small_gcd (p:=p) (j:=(-v^2)^k)
    (by simpa using (uv.pow_right 2).pow_right k) rfl
  have dg : v.natAbs.gcd g.natAbs ∣ p := small_gcd (p:=p) (j:=u^(2*k))
    (by simpa using uv.symm.pow_right (2*k)) rfl
  obtain ⟨s,hs,us⟩ := square_factor up ab
  obtain ⟨t,ht,vt⟩ := square_factor vp bb
  have su : s ∣ u.natAbs := us ▸ (dvd_pow_self s (by decide : 2≠0)).trans (dvd_mul_left _ _)
  have tv : t ∣ v.natAbs := vt ▸ (dvd_pow_self t (by decide : 2≠0)).trans (dvd_mul_left _ _)
  have st := (uv.coprime_dvd_left su).coprime_dvd_right tv
  have apart {x y : ℕ} (xy : x.Coprime y) (d : p ∣ x) : ¬p ∣ y := fun hy =>
    prime.not_dvd_one (xy.gcd_eq_one ▸ Nat.dvd_gcd d hy)
  change c=u.natAbs^2+v.natAbs^2 at norm
  rw [us,vt] at norm
  rcases (Nat.dvd_prime prime).mp df with h | h <;>
    rcases (Nat.dvd_prime prime).mp dg with j | j <;> rw [h,j] at norm
  · exact ⟨s,t,hs,ht,st,Or.inl (by linear_combination norm)⟩
  · rw [j] at vt
    have pv : p ∣ v.natAbs := ⟨_,vt⟩
    exact ⟨t,s,ht,hs,st.symm,Or.inr ⟨by linear_combination norm,
      dvd_mul_of_dvd_right (prime.dvd_of_dvd_pow (pv.trans vd)) _,
      fun bad => apart uv.symm pv (bad.trans su)⟩⟩
  · rw [h] at us
    have pu : p ∣ u.natAbs := ⟨_,us⟩
    exact ⟨s,t,hs,ht,st,Or.inr ⟨by linear_combination norm,
      dvd_mul_of_dvd_left (prime.dvd_of_dvd_pow (pu.trans ud)) _,
      fun bad => apart uv pu (bad.trans tv)⟩⟩
  · rw [h] at us
    rw [j] at vt
    exact (prime.not_dvd_one (uv.gcd_eq_one ▸ Nat.dvd_gcd
      (show p ∣ u.natAbs from ⟨_,us⟩) (show p ∣ v.natAbs from ⟨_,vt⟩))).elim

/-- In a primitive solution, an exponent 3 modulo 4 forces one of the
quartic bases to be divisible by five. The output shape excludes residue 3,
which the equation modulo five on its own would allow. -/
theorem five_test {a b c p : ℕ} (odd : Odd p) (eq : a^4+b^4=c^p)
    (shape : ∃ s t : ℕ, c=s^4+t^4 ∨ c=p^2*s^4+t^4) : p%4=1 ∨ 5 ∣ a*b := by
  by_contra! missing
  obtain ⟨s,t,h⟩ := shape
  have sqshape : ∃ r : ℕ, c=r^2+t^4 := by
    rcases h with e|e
    · exact ⟨s^2,by linear_combination e⟩
    · exact ⟨p*s^2,by linear_combination e⟩
  obtain ⟨r,hr⟩ := sqshape
  have eq5 : (a:ZMod 5)^4+(b:ZMod 5)^4=(c:ZMod 5)^p := by
    simpa using congrArg (fun n : ℕ => (n:ZMod 5)) eq
  have h5 : (c:ZMod 5)=(r:ZMod 5)^2+(t:ZMod 5)^4 := by
    simpa using congrArg (fun n : ℕ => (n:ZMod 5)) hr
  have nonzero : (a:ZMod 5)*(b:ZMod 5) ≠ 0 := by
    rw [←Nat.cast_mul]
    exact fun bad => missing.2 ((ZMod.natCast_eq_zero_iff _ _).mp bad)
  have sum2 : (c:ZMod 5)^p=2 := eq5.symm.trans (by
    have table : ∀ x y : ZMod 5, x*y≠0 → x^4+y^4=2 := by decide +kernel
    exact table _ _ nonzero)
  obtain ⟨k,hk⟩ := odd
  have cp : (c:ZMod 5)≠0 := by
    rintro z
    rw [z,zero_pow (by omega : p≠0)] at sum2
    exact (by decide : (0:ZMod 5)≠2) sum2
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  have four : (c:ZMod 5)^4=1 := ZMod.pow_card_sub_one_eq_one cp
  have pk : p=4*(p/4)+3 := by omega
  rw [pk,pow_add,pow_mul,four,one_pow,one_mul] at sum2
  have impossible : ∀ x y : ZMod 5, (x^2+y^4)^3≠2 := by decide +kernel
  exact impossible _ _ (h5 ▸ sum2)

/-- A prime output base surviving the eighth-power order test and the
modulo-five test is still excluded by the two norm forms. -/
theorem output_241 {a b p : ℕ} (ha : 0<a) (hb : 0<b) (cop : a.Coprime b)
    (prime : p.Prime) (hp : 5≤p) : a^4+b^4 ≠ 241^p := by
  intro e
  obtain ⟨s,t,hs,ht,_,h⟩ := output_shapes ha hb cop prime hp e
  have small {n : ℕ} (bound : n^4≤241) : n<4 := by
    by_contra! big
    have := Nat.pow_le_pow_left big 4
    omega
  rcases h with eq | ⟨eq,_,_⟩
  · have sl := small (n:=s) (by omega)
    have tl := small (n:=t) (by omega)
    interval_cases s <;> interval_cases t <;> norm_num at eq
  · have tl := small (n:=t) (by omega)
    have only : s=1 := by
      by_contra! h
      have large := Nat.mul_le_mul (Nat.pow_le_pow_left hp 2)
        (Nat.pow_le_pow_left (show 2 ≤ s by omega) 4)
      omega
    subst s
    simp only [one_pow,mul_one] at eq
    have pl : p≤15 := by
      by_contra! big
      have : 256 ≤ p^2 := Nat.pow_le_pow_left (show 16 ≤ p by omega) 2
      omega
    have finite : ∀ q : Fin 16, ∀ j : Fin 4, q.val.Prime → q.val^2+j.val^4≠241 := by decide +kernel
    exact finite ⟨p,by omega⟩ ⟨t,tl⟩ prime eq.symm

end QuarticOutput

theorem main : H1 → H2 → OMA.R_BealConjecture_beal_conjecture_R1_H2_R2.H2 := by
  intro plain weighted p a b c prime hp ha hb _ cop eq
  have aLarge : 1<a := by
    by_contra! small
    exact QuarticOutput.unit_left hb prime hp (by simpa [show a=1 by omega] using eq)
  have bLarge : 1<b := by
    by_contra! small
    exact QuarticOutput.unit_left ha prime hp (by simpa [show b=1 by omega,add_comm] using eq)
  obtain ⟨s,t,hs,ht,st,h⟩ := QuarticOutput.output_shapes ha hb cop prime hp eq
  have five := QuarticOutput.five_test (prime.odd_of_ne_two (by omega)) eq
    ⟨s,t,h.imp_right And.left⟩
  rcases h with h|⟨h,dvd,away⟩
  · exact plain aLarge bLarge hs ht cop st prime hp five (h ▸ eq)
  · exact weighted aLarge bLarge hs ht cop st prime hp dvd away five (h ▸ eq)

end OMA.R_BealConjecture_beal_conjecture_R1_H2_R2_H2_R1
