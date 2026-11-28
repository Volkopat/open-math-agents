import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1_H2_R1
import Mathlib

namespace TunnellComponentFibers
end TunnellComponentFibers
namespace TunnellFricke
end TunnellFricke
namespace TunnellHalfFourier
end TunnellHalfFourier
namespace TunnellHalfPairing
end TunnellHalfPairing
namespace TunnellLocalFourier
end TunnellLocalFourier
namespace TunnellRankinIntegral
end TunnellRankinIntegral
namespace TunnellRootPolynomial
end TunnellRootPolynomial
namespace TunnellTwistCharacter
end TunnellTwistCharacter

/- TunnellIdealHNF -/
section
namespace TunnellIdealHNF
abbrev R (n : ℕ) := Zsqrtd (-(n:ℤ))
structure Data (n : ℕ) where
  c : ℕ
  a : ℕ
  b : ℕ
  pos_c : 0<c
  pos_a : 0<a
  lt_b : b<a
  divides : (a:ℤ)∣(b:ℤ)^2+n
def ideal {n : ℕ} (s : Data n) : Ideal (R n) where
  carrier := {x | (s.c:ℤ)∣x.im ∧ (s.c:ℤ)*s.a∣x.re-s.b*x.im}
  zero_mem' := by simp
  add_mem' := by
    rintro x y ⟨hx,hx'⟩ ⟨hy,hy'⟩
    refine ⟨dvd_add hx hy,?_⟩
    change _ ∣ x.re+y.re-_* (x.im+y.im)
    rw [show x.re+y.re-(s.b:ℤ)*(x.im+y.im)=(x.re-s.b*x.im)+(y.re-s.b*y.im) by ring]
    exact dvd_add hx' hy'
  smul_mem' := by
    rintro x y ⟨⟨u,hu⟩,⟨t,ht⟩⟩
    obtain ⟨C,hC⟩ := s.divides
    change _ ∣ (x*y).im ∧ _ ∣ (x*y).re - _ * (x*y).im
    rw [Zsqrtd.re_mul,Zsqrtd.im_mul]
    constructor
    · exact ⟨x.re*u+(s.a*t+s.b*u)*x.im,by linear_combination (x.re+s.b*x.im)*hu+x.im*ht⟩
    · exact ⟨(x.re-s.b*x.im)*t-x.im*C*u,by linear_combination (x.re-s.b*x.im)*ht-
        x.im*((s.b:ℤ)^2+n)*hu-x.im*(s.c:ℤ)*u*hC⟩
lemma mem_ideal {n : ℕ} (s : Data n) (x : R n) : x∈ideal s ↔
    (s.c:ℤ)∣x.im ∧ (s.c:ℤ)*s.a∣x.re-s.b*x.im := Iff.rfl
lemma real_slice {n : ℕ} (s : Data n) (x : ℤ) : (⟨x,0⟩:R n)∈ideal s ↔ (s.c:ℤ)*s.a∣x := by simp [mem_ideal]
lemma lift_basis {n : ℕ} (s : Data n) : (⟨s.c*s.b,s.c⟩:R n)∈ideal s := by simp [mem_ideal,mul_comm]
lemma real_basis {n : ℕ} (s : Data n) : (⟨s.c*s.a,0⟩:R n)∈ideal s := (real_slice _ _).mpr dvd_rfl
lemma positive_generator (S : Ideal ℤ) {x : ℤ} (hx : x∈S) (hx0 : x≠0) :
    ∃ c : ℕ, 0<c ∧ ∀ y : ℤ, y∈S ↔ (c:ℤ)∣y := by
  let a := Submodule.IsPrincipal.generator S
  have h (y : ℤ) : y∈S ↔ a∣y := Submodule.IsPrincipal.mem_iff_generator_dvd S
  have h0 : a≠0 := by intro he; have := (h x).mp hx; simp [he,hx0] at this
  exact ⟨a.natAbs,Int.natAbs_pos.mpr h0,fun y => (h y).trans Int.natAbs_dvd.symm⟩
def imHom (n : ℕ) : R n →+ ℤ where
  toFun := Zsqrtd.im
  map_zero' := rfl
  map_add' _ _ := rfl
lemma cast_int {n : ℕ} (a : ℤ) : (a:R n)=⟨a,0⟩ := rfl
lemma normal_form {n : ℕ} (hn : 0<n) {I : Ideal (R n)} (hI : I≠⊥) :
    ∃ s : Data n, I=ideal s := by
  obtain ⟨z,hz,hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  have hnorm : (z.norm:R n)∈I := by rw [Zsqrtd.norm_eq_mul_conj]; exact I.mul_mem_right _ hz
  have hnorm0 : z.norm≠0 := by
    intro h; apply hz0
    change z.re*z.re- -(n:ℤ)*z.im*z.im=0 at h
    have ha : z.im=0 := by
      by_contra ha
      have hsq : 0<z.im*z.im := mul_self_pos.mpr ha
      have e := mul_pos (show 0<(n:ℤ) by exact_mod_cast hn) hsq
      nlinarith [mul_self_nonneg z.re]
    have hb : z.re=0 := by rw [ha] at h; simpa using h
    exact Zsqrtd.ext hb ha
  let S := I.comap (Int.castRingHom (R n))
  obtain ⟨A,hA,real_iff⟩ := positive_generator S hnorm hnorm0
  change ∀ y : ℤ, (y:R n)∈I ↔ (A:ℤ)∣y at real_iff
  have hR := (real_iff A).mpr dvd_rfl
  let T := (I.toAddSubgroup.map (imHom n)).toIntSubmodule
  have hT : ∀ y : ℤ, y∈T ↔ ∃ x∈I, x.im=y := fun _ => Iff.rfl
  have hroot (x : R n) (h : x∈I) : x.re∈T := (hT _).mpr ⟨Zsqrtd.sqrtd*x,I.mul_mem_left _ h,by simp [Zsqrtd.im_mul]⟩
  obtain ⟨c,hc,imag_iff⟩ := positive_generator T (hroot _ hR) (show ((A:R n).re:ℤ)≠0 by simpa using hA.ne')
  have ca : (c:ℤ)∣A := (imag_iff _).mp (hroot _ hR)
  obtain ⟨a,haa⟩ := (Int.natCast_dvd_natCast.mp ca)
  have hap : 0<a := by by_contra! h; have := Nat.eq_zero_of_le_zero h; simp [this] at haa; omega
  have eA : (A:ℤ)=c*a := by exact_mod_cast haa
  obtain ⟨v,hv,he⟩ := (hT _).mp ((imag_iff c).mpr dvd_rfl)
  obtain ⟨b₀,hb₀⟩ := (imag_iff v.re).mp (hroot v hv)
  let b := b₀%(a:ℤ)
  have hbpos : 0≤b := Int.emod_nonneg _ (by exact_mod_cast hap.ne')
  have hblt : b<(a:ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hap)
  have hlin : (⟨c*b,c⟩:R n)∈I := by
    have hh := I.sub_mem hv (I.mul_mem_left ((b₀/(a:ℤ):ℤ):R n) hR)
    convert hh using 1
    apply Zsqrtd.ext
    · simp only [Zsqrtd.re_sub,Zsqrtd.re_mul,cast_int,mul_zero,add_zero]
      change (c:ℤ)*b = v.re - b₀/a*A
      rw [eA,hb₀]
      dsimp [b]
      linear_combination (c:ℤ)*(Int.emod_add_mul_ediv b₀ a)
    · simp only [Zsqrtd.im_sub,Zsqrtd.im_mul,cast_int,mul_zero,zero_mul,zero_add,sub_zero]; exact he.symm
  have mem (x : R n) : x∈I ↔ (c:ℤ)∣x.im ∧ (A:ℤ)∣x.re-b*x.im := by
    constructor
    · intro hx
      obtain ⟨t,ht⟩ := (imag_iff x.im).mp ((hT _).mpr ⟨x,hx,rfl⟩)
      refine ⟨⟨t,ht⟩,(real_iff _).mp ?_⟩
      have hh := I.sub_mem hx (I.mul_mem_left (t:R n) hlin)
      convert hh using 1; apply Zsqrtd.ext
      · change x.re-b*x.im=x.re-(t*(c*b)+ -(n:ℤ)*0*c); rw [ht]; ring
      · change (0:ℤ)=x.im-(t*c+0*(c*b)); rw [ht]; ring
    · rintro ⟨⟨t,ht⟩,hA'⟩
      have hh := I.add_mem ((real_iff _).mpr hA') (I.mul_mem_left (t:R n) hlin)
      convert hh using 1; apply Zsqrtd.ext
      · change x.re=x.re-b*x.im+(t*(c*b)+ -(n:ℤ)*0*c); rw [ht]; ring
      · change x.im=0+(t*c+0*(c*b)); rw [ht]; ring
  have hmultiple := ((mem _).mp (I.mul_mem_left Zsqrtd.sqrtd hlin)).2
  rw [Zsqrtd.re_mul,Zsqrtd.im_mul] at hmultiple
  simp only [Zsqrtd.re_sqrtd,Zsqrtd.im_sqrtd,zero_mul,mul_one,one_mul,zero_add] at hmultiple
  obtain ⟨t,ht⟩ := hmultiple
  have e : (b^2+(n:ℤ))=(a:ℤ)*(-t) := by
    apply mul_left_cancel₀ (show (c:ℤ)≠0 by exact_mod_cast hc.ne')
    rw [eA] at ht
    linear_combination -ht
  let s : Data n := ⟨c,a,b.toNat,hc,hap,by omega,by exact ⟨-t,by simpa [Int.toNat_of_nonneg hbpos] using e⟩⟩
  refine ⟨s,?_⟩
  ext x
  rw [mem,mem_ideal]
  change _ ↔ (c:ℤ)∣x.im ∧ (c:ℤ)*a∣x.re-b.toNat*x.im
  rw [←eA,Int.toNat_of_nonneg hbpos]
lemma ideal_ne_bot {n : ℕ} (s : Data n) : ideal s≠⊥ := by
  intro h
  have he := real_basis s
  rw [h] at he
  have hh := congrArg Zsqrtd.re (show (⟨(s.c:ℤ)*s.a,0⟩:R n)=0 from he)
  change (s.c:ℤ)*s.a=0 at hh
  exact (mul_ne_zero (by exact_mod_cast s.pos_c.ne') (by exact_mod_cast s.pos_a.ne')) hh
lemma ideal_injective {n : ℕ} : Function.Injective (@ideal n) := by
  intro s t h
  have mono {s t : Data n} (h : ideal s ≤ ideal t) : t.c∣s.c ∧ t.c*t.a∣s.c*s.a ∧ (t.c:ℤ)*t.a∣s.c*s.b-t.b*s.c := by
    have e := (mem_ideal _ _).mp (h (lift_basis s))
    have e' := (real_slice _ _).mp (h (real_basis s))
    exact ⟨Int.natCast_dvd_natCast.mp (show (t.c:ℤ)∣(s.c:ℤ) from e.1),by exact_mod_cast e',e.2⟩
  obtain ⟨c₁,a₁,b₁⟩ := mono h.le
  obtain ⟨c₂,a₂,_⟩ := mono h.ge
  have c := Nat.dvd_antisymm c₂ c₁
  have ca := Nat.dvd_antisymm a₂ a₁
  have a : s.a=t.a := by rw [←c] at ca; exact Nat.eq_of_mul_eq_mul_left s.pos_c ca
  rw [←c,←a] at b₁
  obtain ⟨k,hk⟩ := b₁
  have he : (s.b:ℤ)-(t.b:ℤ)=s.a*k := by
    apply mul_left_cancel₀ (show (s.c:ℤ)≠0 by exact_mod_cast s.pos_c.ne')
    linear_combination hk
  have hm : (t.b:ℤ) ≡ (s.b:ℤ) [ZMOD s.a] := Int.modEq_iff_dvd.mpr ⟨k,he⟩
  have eb : t.b=s.b := by
    change (t.b:ℤ)%s.a=(s.b:ℤ)%s.a at hm
    rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast a ▸ t.lt_b),Int.emod_eq_of_lt (by positivity) (by exact_mod_cast s.lt_b)] at hm
    exact_mod_cast hm
  cases s; cases t; dsimp only at c a eb; congr; exact eb.symm
def residues {n : ℕ} (s : Data n) : R n →+ (ZMod s.c × ZMod (s.c*s.a)) where
  toFun x := (x.im,(x.re:ZMod (s.c*s.a))-s.b*x.im)
  map_zero' := by simp
  map_add' x y := by simp [mul_add]; abel
lemma residues_surj {n : ℕ} (s : Data n) : Function.Surjective (residues s) := by
  rintro ⟨u,t⟩
  letI : NeZero s.c := ⟨s.pos_c.ne'⟩
  letI : NeZero (s.c*s.a) := ⟨mul_ne_zero s.pos_c.ne' s.pos_a.ne'⟩
  exact ⟨⟨(t.val:ℤ)+s.b*u.val,u.val⟩,by simp [residues]⟩
lemma residues_ker {n : ℕ} (s : Data n) : (residues s).ker=(ideal s).toAddSubgroup := by
  ext x
  change ((x.im:ZMod s.c),(x.re:ZMod (s.c*s.a))-s.b*x.im)=(0,0) ↔ _
  simp only [Prod.mk.injEq,mem_ideal,ZMod.intCast_zmod_eq_zero_iff_dvd]
  have he : ((x.re:ZMod (s.c*s.a))-s.b*x.im) = ((x.re-s.b*x.im:ℤ):ZMod (s.c*s.a)) := by push_cast; rfl
  rw [he,ZMod.intCast_zmod_eq_zero_iff_dvd,Nat.cast_mul]
  rfl
theorem quotient_card {n : ℕ} (s : Data n) : Nat.card (R n ⧸ ideal s)=s.c^2*s.a := by
  letI : NeZero s.c := ⟨s.pos_c.ne'⟩
  letI : NeZero (s.c*s.a) := ⟨mul_ne_zero s.pos_c.ne' s.pos_a.ne'⟩
  let e := (AddSubgroup.quotientEquivOfEq (residues_ker s).symm).trans (QuotientAddGroup.quotientKerEquivOfSurjective (residues s) (residues_surj s)).toEquiv
  have h := Nat.card_congr e
  change Nat.card (R n ⧸ ideal s)=_ at h
  simpa [Nat.card_prod,Nat.card_zmod,pow_two,mul_assoc] using h
end TunnellIdealHNF
end


/- TunnellIdealInverse -/
section
namespace TunnellIdealHNF
def conjugate {n : ℕ} (I : Ideal (R n)) := I.comap (starRingEnd _)
lemma mem_conjugate {n : ℕ} (I : Ideal (R n)) (x : R n) : x∈conjugate I ↔ star x∈I := Iff.rfl
def idx {n : ℕ} (s : Data n) : ℕ := s.c^2*s.a
lemma basis_expansion {n : ℕ} (s : Data n) {x : R n} (hx : x∈ideal s) :
    ∃ u v : ℤ, x=⟨s.c*(s.a*u+s.b*v),s.c*v⟩ := by
  obtain ⟨⟨v,hv⟩,⟨u,hu⟩⟩ := (mem_ideal s x).mp hx
  exact ⟨u,v,Zsqrtd.ext (by dsimp only; linear_combination hu+(s.b:ℤ)*hv) hv⟩
lemma primitive_coeffs {n : ℕ} (hn : Squarefree n) (h₂ : n%4=2) (s : Data n) {C : ℤ}
    (hC : (s.b:ℤ)^2+n=s.a*C) : ∃ x y z : ℤ, (s.a:ℤ)*x+(2*s.b)*y+C*z=1 := by
  let a : ℤ := s.a
  let b : ℤ := s.b
  let g := Int.gcd a (2*b)
  let h := Int.gcd (g:ℤ) C
  have h₁ : (h:ℤ) ∣ a := (Int.gcd_dvd_left (g:ℤ) C).trans (Int.gcd_dvd_left a (2*b))
  have h₂' : (h:ℤ) ∣ 2*b := (Int.gcd_dvd_left (g:ℤ) C).trans (Int.gcd_dvd_right a (2*b))
  have h₃ : (h:ℤ) ∣ C := Int.gcd_dvd_right (g:ℤ) C
  have hh : h=1 := by
    by_contra e
    obtain ⟨p,hp,hp'⟩ := Nat.exists_prime_and_dvd e
    have hpz := Int.natCast_dvd_natCast.mpr hp'
    obtain ⟨A,hA⟩ := hpz.trans h₁
    obtain ⟨D,hD⟩ := hpz.trans h₃
    change b^2+n=a*C at hC
    by_cases hp2 : p=2
    · subst p
      have he : (b:ZMod 4)^2+2=0 := by
        have hh := congrArg (fun t:ℤ => (t:ZMod 4)) hC
        rw [hA,hD] at hh; push_cast at hh
        have hn₂ : (n:ZMod 4)=2 := by apply ZMod.val_injective 4; rw [ZMod.val_natCast,h₂]; decide
        rw [hn₂] at hh
        calc _=2*(A:ZMod 4)*(2*(D:ZMod 4)) := hh
             _=(4:ZMod 4)*(A*D) := by ring
             _=0 := by rw [show (4:ZMod 4)=0 by decide,zero_mul]
      exact (show ∀ z : ZMod 4, z^2+2≠0 by decide) _ he
    · have hpn : ¬(p:ℤ)∣2 := by
        intro h; have ht : p∣2 := by exact_mod_cast h
        rcases (Nat.dvd_prime Nat.prime_two).mp ht with h|h
        · exact hp.ne_one h
        · exact hp2 h
      obtain ⟨B,hB⟩ := ((Nat.prime_iff_prime_int.mp hp).dvd_mul.mp (hpz.trans h₂')).resolve_left hpn
      have he : (p:ℤ)*p∣n := ⟨A*D-B^2,by rw [hA,hD,hB] at hC; linear_combination hC⟩
      have ht : p*p∣n := by exact_mod_cast he
      exact hp.ne_one (Nat.isUnit_iff.mp (hn p ht))
  have hf := Int.gcd_eq_gcd_ab a (2*b)
  have hf' := Int.gcd_eq_gcd_ab (g:ℤ) C
  change (g:ℤ)=_ at hf
  change (h:ℤ)=_ at hf'
  rw [hh] at hf'; norm_cast at hf'
  refine ⟨Int.gcdA a (2*b)*Int.gcdA (g:ℤ) C,Int.gcdB a (2*b)*Int.gcdA (g:ℤ) C,Int.gcdB (g:ℤ) C,?_⟩
  change a*_+(2*b)*_+C*_=1
  linear_combination -hf' - Int.gcdA (g:ℤ) C*hf
theorem times_conj {n : ℕ} (hn : Squarefree n) (h₂ : n%4=2) (s : Data n) :
    ideal s*conjugate (ideal s)=Ideal.span {((idx s:ℕ):R n)} := by
  let N : ℤ := idx s
  have Ne : N=(s.c:ℤ)^2*s.a := by simp [N,idx]
  obtain ⟨C,hC⟩ := s.divides
  let P := ideal s*conjugate (ideal s)
  change P=Ideal.span {(N:R n)}
  apply le_antisymm
  · apply Ideal.mul_le.mpr
    intro x hx y hy
    obtain ⟨u,v,hx'⟩ := basis_expansion s hx
    obtain ⟨t,w,hy'⟩ := basis_expansion s ((mem_conjugate _ _).mp hy)
    apply Ideal.mem_span_singleton.mpr
    refine ⟨⟨s.a*u*t+s.b*(u*w+v*t)+C*v*w,v*t-u*w⟩,?_⟩
    have e : y=star (⟨s.c*(s.a*t+s.b*w),s.c*w⟩:R n) := by rw [←hy',star_star]
    rw [hx',e]
    apply Zsqrtd.ext <;> simp only [Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.re_star,Zsqrtd.im_star,cast_int,Ne]
    · linear_combination (s.c:ℤ)^2*v*w*hC
    · ring
  · rw [Ideal.span_singleton_le_iff_mem]
    let g : R n := ⟨s.c*s.a,0⟩
    let u : R n := ⟨s.c*s.b,s.c⟩
    have g₁ : g∈ideal s := real_basis s
    have u₁ : u∈ideal s := lift_basis s
    have g₂ : g∈conjugate (ideal s) := by apply (mem_conjugate _ _).mpr; simpa [g,Zsqrtd.star_mk] using g₁
    have u₂ : star u∈conjugate (ideal s) := (mem_conjugate _ _).mpr (by simpa using u₁)
    have hA : ((N*(s.a:ℤ):ℤ):R n)∈P := by
      have hh : g*g=((N*(s.a:ℤ):ℤ):R n) := by
        change g*g=⟨N*(s.a:ℤ),0⟩
        apply Zsqrtd.ext <;> simp only [g,Ne,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring
      rw [←hh]; exact Ideal.mul_mem_mul g₁ g₂
    have hB : ((N*(2*s.b:ℤ):ℤ):R n)∈P := by
      have hh : u*g+g*star u=((N*(2*s.b:ℤ):ℤ):R n) := by
        change u*g+g*star u=⟨N*(2*s.b:ℤ),0⟩
        apply Zsqrtd.ext <;> simp only [g,u,Ne,Zsqrtd.re_add,Zsqrtd.im_add,Zsqrtd.re_mul,Zsqrtd.im_mul,Zsqrtd.star_mk] <;> ring
      rw [←hh]; exact P.add_mem (Ideal.mul_mem_mul u₁ g₂) (Ideal.mul_mem_mul g₁ u₂)
    have hD : ((N*C:ℤ):R n)∈P := by
      have hh : u*star u=((N*C:ℤ):R n) := by
        rw [←Zsqrtd.norm_eq_mul_conj]; congr 1
        dsimp [u,Zsqrtd.norm]; rw [Ne]; linear_combination (s.c:ℤ)^2*hC
      rw [←hh]; exact Ideal.mul_mem_mul u₁ u₂
    obtain ⟨x,y,z,h⟩ := primitive_coeffs hn h₂ s hC
    have hh := P.add_mem (P.add_mem (P.mul_mem_left (x:R n) hA) (P.mul_mem_left (y:R n) hB)) (P.mul_mem_left (z:R n) hD)
    have he : N=x*(N*s.a)+y*(N*(2*s.b))+z*(N*C) := by linear_combination -N*h
    simpa only [←Int.cast_mul,←Int.cast_add,←he] using hh
end TunnellIdealHNF
end


/- TunnellHurwitzFour -/
section
namespace TunnellHurwitzFour
open Finset
abbrev H (R : Type*) := R × R × R × R
def prod {R : Type*} [CommRing R] (x y : H R) : H R :=
  let (a,b,c,d) := x
  let (u,v,w,t) := y
  (a*u-b*v-c*w-d*t-b*w+c*v-b*t-d*w,
   a*v+b*u-b*w+c*v+d*v+c*t-d*w,
   a*w+c*u-b*w+c*v-b*t+d*v+c*t,
   a*t+d*u+2*b*w-2*c*v+b*t-d*v-c*t+d*w+d*t)
def nr {R : Type*} [CommRing R] (x : H R) : R :=
  let (a,b,c,d) := x
  a^2+b^2+c^2+d^2+(a+b+c)*d
def ham (x : H ℚ) : Quaternion ℚ :=
  let (a,b,c,d) := x
  ⟨a+d/2,b+d/2,c+d/2,d/2⟩
lemma ham_prod (x y : H ℚ) : ham (prod x y)=ham x * ham y := by
  obtain ⟨a,b,c,d⟩ := x
  obtain ⟨u,v,w,t⟩ := y
  apply QuaternionAlgebra.ext
  · rw [Quaternion.re_mul]; dsimp [ham,prod]; ring
  · rw [Quaternion.imI_mul]; dsimp [ham,prod]; ring
  · rw [Quaternion.imJ_mul]; dsimp [ham,prod]; ring
  · rw [Quaternion.imK_mul]; dsimp [ham,prod]; ring
lemma ham_norm (x : H ℚ) : Quaternion.normSq (ham x) = nr x := by
  rw [Quaternion.normSq_def']; dsimp [ham,nr]; ring
abbrev Z4 := ZMod 4
abbrev H4 := H Z4
def units : Finset H4 := univ.filter (fun x => (nr x).val%2=1)
def lipschitz : Finset H4 :=
  {(1,0,0,0),(-1,0,0,0),(0,1,0,0),(0,-1,0,0),(0,0,1,0),(0,0,-1,0),(-1,-1,-1,2),(1,1,1,-2)}
def globalUnits : Finset H4 :=
  let S : Finset Z4 := {0,-1}
  let T : Finset Z4 := {0,1}
  lipschitz ∪ (S ×ˢ (S ×ˢ (S ×ˢ {1}))) ∪ (T ×ˢ (T ×ˢ (T ×ˢ {-1})))
def orderUnits : Finset H4 := (({1,-1}:Finset Z4) ×ˢ (univ : Finset Z4)).image (fun ab => (ab.1,ab.2,ab.2,0))
def orbit (x : H4) : Finset H4 := (globalUnits ×ˢ orderUnits).image fun ab => prod (prod ab.1 x) ab.2
def e : H4 := (1,0,0,0)
def tau : H4 := (1,0,2,0)
lemma global_units_card : globalUnits.card=24 := by decide
private def decodeOrbit (n:ℕ) : H4 := (n,((n/4:ℕ):Z4),((n/16:ℕ):Z4),((n/64:ℕ):Z4))
private def leftOrbit (i:Fin 24) : H4 := decodeOrbit ((#[1,3,4,12,16,48,191,149,64,112,76,124,67,115,79,127,192,208,196,212,193,209,197,213] : Array ℕ)[i.val]!)
private def rightOrbit (i:Fin 8) : H4 := decodeOrbit ((#[1,21,41,61,3,23,43,63] : Array ℕ)[i.val]!)
private def witnessOrbit (x:H4) : ℕ :=
  (#[0,12,0,8,28,0,222,0,0,206,0,202,24,0,218,0,44,0,236,0,0,15,0,11,42,0,234,0,0,207,0,203,0,204,0,200,26,0,216,0,0,14,0,10,30,0,220,0,40,0,232,0,0,205,0,201,46,0,238,0,0,13,0,9,132,341,365,164,165,368,150,345,171,166,320,343,148,159,167,180,377,174,330,135,346,137,179,376,328,321,379,362,373,378,158,139,367,354,134,145,336,347,353,370,322,147,169,352,355,182,338,157,140,133,189,172,177,190,344,333,191,360,142,323,156,335,375,188,0,251,0,253,43,0,233,0,0,57,0,63,45,0,239,0,217,0,25,0,0,56,0,62,221,0,29,0,0,248,0,254,0,59,0,61,47,0,237,0,0,249,0,255,41,0,235,0,223,0,31,0,0,250,0,252,219,0,27,0,0,58,0,60,128,160,363,339,144,176,161,153,173,337,324,162,163,351,146,372,136,168,187,131,152,184,369,329,185,325,138,364,183,331,348,186,361,151,130,358,357,155,342,178,326,356,175,149,340,374,359,349,383,129,334,170,371,141,154,382,332,366,381,327,350,380,181,143] : Array ℕ)[x.1.val+4*x.2.1.val+16*x.2.2.1.val+64*x.2.2.2.val]!
def sideOrbit (x:H4) : Bool := decide (192≤witnessOrbit x)
def repOrbit (s:Bool) : H4 := if s then tau else e
private def leftIndex (x:H4) : Fin 24 := ⟨witnessOrbit x/8%24,Nat.mod_lt _ (by decide)⟩
private def rightIndex (x:H4) : Fin 8 := ⟨witnessOrbit x%8,Nat.mod_lt _ (by decide)⟩

private lemma leftOrbit_image : Finset.univ.image leftOrbit=globalUnits := by decide
private lemma rightOrbit_image : Finset.univ.image rightOrbit=orderUnits := by decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private lemma orbit_certificate : ∀ x:H4,(nr x).val%2=1 →
    prod (prod (leftOrbit (leftIndex x)) (repOrbit (sideOrbit x))) (rightOrbit (rightIndex x))=x := by decide

private def orbitCheck (i:Fin 24) := ∀ (j:Fin 8) (s:Bool),
    let x := prod (prod (leftOrbit i) (repOrbit s)) (rightOrbit j)
    (nr x).val%2=1 ∧ sideOrbit x=s
set_option maxRecDepth 10000 in
private lemma checkOrbit0 : orbitCheck 0 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit1 : orbitCheck 1 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit2 : orbitCheck 2 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit3 : orbitCheck 3 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit4 : orbitCheck 4 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit5 : orbitCheck 5 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit6 : orbitCheck 6 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit7 : orbitCheck 7 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit8 : orbitCheck 8 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit9 : orbitCheck 9 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit10 : orbitCheck 10 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit11 : orbitCheck 11 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit12 : orbitCheck 12 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit13 : orbitCheck 13 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit14 : orbitCheck 14 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit15 : orbitCheck 15 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit16 : orbitCheck 16 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit17 : orbitCheck 17 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit18 : orbitCheck 18 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit19 : orbitCheck 19 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit20 : orbitCheck 20 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit21 : orbitCheck 21 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit22 : orbitCheck 22 := by unfold orbitCheck; decide
set_option maxRecDepth 10000 in
private lemma checkOrbit23 : orbitCheck 23 := by unfold orbitCheck; decide
private lemma orbit_disjoint_certificate (i:Fin 24) : orbitCheck i := by
  fin_cases i
  · exact checkOrbit0
  · exact checkOrbit1
  · exact checkOrbit2
  · exact checkOrbit3
  · exact checkOrbit4
  · exact checkOrbit5
  · exact checkOrbit6
  · exact checkOrbit7
  · exact checkOrbit8
  · exact checkOrbit9
  · exact checkOrbit10
  · exact checkOrbit11
  · exact checkOrbit12
  · exact checkOrbit13
  · exact checkOrbit14
  · exact checkOrbit15
  · exact checkOrbit16
  · exact checkOrbit17
  · exact checkOrbit18
  · exact checkOrbit19
  · exact checkOrbit20
  · exact checkOrbit21
  · exact checkOrbit22
  · exact checkOrbit23

lemma orbit_iff (s:Bool) (x:H4) : x∈orbit (repOrbit s) ↔ x∈units ∧ sideOrbit x=s := by
  constructor
  · intro h
    obtain ⟨⟨u,v⟩,huv,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hu,hv⟩ := Finset.mem_product.mp huv
    rw [←leftOrbit_image] at hu
    rw [←rightOrbit_image] at hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
    have he := orbit_disjoint_certificate i j s
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,he.1⟩,he.2⟩
  · rintro ⟨hu,hs⟩
    have he := orbit_certificate x (Finset.mem_filter.mp hu).2
    rw [hs] at he
    apply Finset.mem_image.mpr
    refine ⟨(leftOrbit (leftIndex x),rightOrbit (rightIndex x)),Finset.mem_product.mpr ⟨?_,?_⟩,he⟩
    · rw [←leftOrbit_image]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · rw [←rightOrbit_image]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)

lemma two_orbits : orbit e ∪ orbit tau=units ∧ Disjoint (orbit e) (orbit tau) := by
  have h (x:H4) := orbit_iff false x
  have k (x:H4) := orbit_iff true x
  change (∀ x:H4,x∈orbit e ↔ x∈units ∧ sideOrbit x=false) at h
  change (∀ x:H4,x∈orbit tau ↔ x∈units ∧ sideOrbit x=true) at k
  constructor
  · ext x; rw [Finset.mem_union,h,k]; cases sideOrbit x <;> simp
  · apply Finset.disjoint_left.mpr; intro x hx hy
    exact Bool.false_ne_true (((h x).mp hx).2.symm.trans ((k x).mp hy).2)
def modFour (x : H ℤ) : H4 := (x.1,x.2.1,x.2.2.1,x.2.2.2)
lemma modFour_mul (x y : H ℤ) : modFour (prod x y)=prod (modFour x) (modFour y) := by
  obtain ⟨a,b,c,d⟩ := x
  obtain ⟨q,r,s,t⟩ := y
  simp [modFour,prod]
noncomputable def box : Finset (H ℤ) :=
  let I := Icc (-2:ℤ) 2
  I ×ˢ (I ×ˢ (I ×ˢ I))
lemma norm_one_mem (x : H ℤ) (hx : nr x=1) : x∈box := by
  obtain ⟨a,b,c,d⟩ := x
  change a^2+b^2+c^2+d^2+(a+b+c)*d=1 at hx
  have he : (2*a+d)^2+(2*b+d)^2+(2*c+d)^2+d^2=4 := by linear_combination 4*hx
  have bound (z : ℤ) (h : z^2≤4) : -2≤z ∧ z≤2 := by
    constructor <;> by_contra! hh <;> nlinarith
  have ha := bound (2*a+d) (by nlinarith [sq_nonneg (2*b+d),sq_nonneg (2*c+d),sq_nonneg d])
  have hb := bound (2*b+d) (by nlinarith [sq_nonneg (2*a+d),sq_nonneg (2*c+d),sq_nonneg d])
  have hc := bound (2*c+d) (by nlinarith [sq_nonneg (2*a+d),sq_nonneg (2*b+d),sq_nonneg d])
  have hd := bound d (by nlinarith [sq_nonneg (2*a+d),sq_nonneg (2*b+d),sq_nonneg (2*c+d)])
  simp [box]
  omega
set_option maxRecDepth 10000 in
lemma global_units_image : ((box.filter (fun x => nr x=1)).image modFour)=globalUnits := by decide
lemma global_iff (a : H4) : a∈globalUnits ↔ ∃ x : H ℤ, nr x=1 ∧ modFour x=a := by
  rw [←global_units_image,mem_image]
  exact ⟨fun ⟨v,hv,he⟩ => ⟨v,(mem_filter.mp hv).2,he⟩,
    fun ⟨v,hv,he⟩ => ⟨v,mem_filter.mpr ⟨norm_one_mem v hv,hv⟩,he⟩⟩
end TunnellHurwitzFour
end


/- TunnellHurwitzOrder -/
section
namespace TunnellHurwitz
open TunnellHurwitzFour Quaternion
abbrev Q := Quaternion ℚ
def hamZ (x : H ℤ) : Q := ham ((x.1:ℚ),(x.2.1:ℚ),(x.2.2.1:ℚ),(x.2.2.2:ℚ))
lemma hamZ_mul (x y : H ℤ) : hamZ (prod x y) = hamZ x * hamZ y := by
  unfold hamZ
  rw [←ham_prod]
  congr 1
  rcases x with ⟨a,b,c,d⟩
  rcases y with ⟨e,f,g,h⟩
  simp [prod]
lemma hamZ_add (x y : H ℤ) : hamZ (x+y)=hamZ x+hamZ y := by
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_add,Quaternion.imI_add,Quaternion.imJ_add,Quaternion.imK_add] <;> simp [hamZ,ham,add_div] <;> ring
lemma hamZ_neg (x : H ℤ) : hamZ (-x)=-(hamZ x) := by
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg] <;> simp [hamZ,ham] <;> ring
def order : Subring Q where
  carrier := Set.range hamZ
  zero_mem' := ⟨0,by apply QuaternionAlgebra.ext <;> norm_num [hamZ,ham]⟩
  one_mem' := ⟨(1,0,0,0),by apply QuaternionAlgebra.ext <;> norm_num [hamZ,ham]⟩
  add_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨a+b,hamZ_add a b⟩
  neg_mem' := by rintro _ ⟨a,rfl⟩; exact ⟨-a,hamZ_neg _⟩
  mul_mem' := by rintro _ _ ⟨a,rfl⟩ ⟨b,rfl⟩; exact ⟨prod a b,hamZ_mul _ _⟩
lemma integer_coords (a b c d : ℤ) : (⟨a,b,c,d⟩:Q)∈order := by
  refine ⟨(a-d,b-d,c-d,2*d),?_⟩
  apply QuaternionAlgebra.ext <;> dsimp [hamZ,ham] <;> push_cast <;> ring
lemma half_mem : (⟨1/2,1/2,1/2,1/2⟩:Q)∈order := by
  refine ⟨(0,0,0,1),?_⟩
  apply QuaternionAlgebra.ext <;> norm_num [hamZ,ham]
lemma norm_int {q : Q} (hq : q∈order) : ∃ n : ℕ, normSq q=n := by
  obtain ⟨⟨a,b,c,d⟩,rfl⟩ := hq
  let N := nr (a,b,c,d)
  have hh : normSq (hamZ (a,b,c,d))=(N:ℚ) := by simp [hamZ,ham_norm,N,nr]
  have hN : 0≤N := by exact_mod_cast (hh ▸ normSq_nonneg : 0≤(N:ℚ))
  refine ⟨N.toNat,hh.trans ?_⟩
  exact_mod_cast (Int.toNat_of_nonneg hN).symm
 
lemma approximate (q : Q) : ∃ r∈order, normSq (q-r)<1 := by
  let r : Q := ⟨round q.re,round q.imI,round q.imJ,round q.imK⟩
  have hr : r∈order := integer_coords _ _ _ _
  by_cases h : normSq (q-r)<1
  · exact ⟨r,hr,h⟩
  let err (t : ℚ) := t-round t
  have bound (t : ℚ) : err t ^ 2 ≤ 1/4 := by
    have hl := round_le_add_half t
    have hh := sub_half_lt_round t
    dsimp [err]
    nlinarith [mul_nonneg (show 0≤t-round t+1/2 by linarith) (show 0≤1/2-(t-round t) by linarith)]
  have eqn (t : ℚ) (ht : 1/4 ≤ err t^2) : err t = -1/2 := by
    have he := le_antisymm (bound t) ht
    have hlt : err t<1/2 := by dsimp [err]; linarith [sub_half_lt_round t]
    have hf : (err t-1/2)*(err t+1/2)=0 := by nlinarith
    rcases mul_eq_zero.mp hf with ha|ha <;> linarith
  have he : ¬err q.re^2+err q.imI^2+err q.imJ^2+err q.imK^2<1 := by
    rw [normSq_def'] at h
    exact h
  have a := eqn q.re (by linarith [bound q.imI,bound q.imJ,bound q.imK])
  have b := eqn q.imI (by linarith [bound q.re,bound q.imJ,bound q.imK])
  have c := eqn q.imJ (by linarith [bound q.re,bound q.imI,bound q.imK])
  have d := eqn q.imK (by linarith [bound q.re,bound q.imI,bound q.imJ])
  let u : Q := ⟨1/2,1/2,1/2,1/2⟩
  have heq : q=r-u := by
    dsimp only [err] at a b c d
    apply QuaternionAlgebra.ext
    · change q.re=(round q.re:ℚ)-1/2; linarith
    · change q.imI=(round q.imI:ℚ)-1/2; linarith
    · change q.imJ=(round q.imJ:ℚ)-1/2; linarith
    · change q.imK=(round q.imK:ℚ)-1/2; linarith
  refine ⟨q,?_,by simp⟩
  rw [heq]
  exact order.sub_mem hr half_mem
 
theorem integral_class_number_one (S : Set Q) (hin : S⊆order)
    (hsub : ∀ a∈S, ∀ b∈S, a-b∈S) (hmul : ∀ a∈S, ∀ b∈order, a*b∈S)
    (hne : ∃ a∈S, a≠0) :
    ∃ a∈S, a≠0 ∧ S={x | ∃ b∈order, x=a*b} := by
  classical
  let P (n : ℕ) := ∃ a∈S, a≠0 ∧ normSq a = n
  obtain ⟨q,hq,hq0⟩ := hne
  obtain ⟨n,hn⟩ := norm_int (hin hq)
  have hP : ∃ n, P n := ⟨n,q,hq,hq0,hn⟩
  obtain ⟨a,ha,ha0,han⟩ := Nat.find_spec hP
  refine ⟨a,ha,ha0,Set.ext fun x => ⟨?_,?_⟩⟩
  · intro hx
    obtain ⟨r,hr,ht⟩ := approximate (a⁻¹*x)
    have hv : x-a*r∈S := hsub x hx _ (hmul a ha r hr)
    have he : x-a*r=a*(a⁻¹*x-r) := by rw [mul_sub,←mul_assoc,mul_inv_cancel₀ ha0,one_mul]
    have ha' : 0<normSq a := lt_of_le_of_ne normSq_nonneg (normSq_ne_zero.mpr ha0).symm
    have hlt : normSq (x-a*r)<normSq a := by
      rw [he,map_mul]; simpa using mul_lt_mul_of_pos_left ht ha'
    have hzero : x-a*r=0 := by
      by_contra h0
      obtain ⟨k,hk⟩ := norm_int (hin hv)
      have hmin := Nat.find_min' hP (show P k from ⟨x-a*r,hv,h0,hk⟩)
      rw [hk,han] at hlt
      exact (not_lt_of_ge hmin) (by exact_mod_cast hlt)
    exact ⟨r,hr,sub_eq_zero.mp hzero⟩
  · rintro ⟨r,hr,rfl⟩; exact hmul a ha r hr
end TunnellHurwitz
end


/- TunnellShell -/
section
namespace TunnellShell
open OMA.R_CongruentNumber_Tunnell_even_R1 CongruentNumber Finset
open scoped PowerSeries.WithPiTopology
abbrev Triple := ℤ × ℤ × ℤ
def normSq (v : Triple) : ℤ := v.1^2+v.2.1^2+v.2.2^2
def shell (N : ℕ) : Finset Triple :=
  let I := Finset.Icc (-(N:ℤ)-1) (N+1:ℤ)
  (I ×ˢ (I ×ˢ I)).filter (fun v => normSq v=N)
@[simp] lemma mem_shell {N : ℕ} {v : Triple} : v ∈ shell N ↔ normSq v=N := by
  obtain ⟨x,y,z⟩ := v
  simp only [shell,Finset.mem_filter,Finset.mem_product,Finset.mem_Icc]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  change x^2+y^2+z^2=(N:ℤ) at h
  have hbound (a:ℤ) (ha:a^2≤N) : -(N:ℤ)-1 ≤ a ∧ a ≤ N+1 :=
    ⟨by nlinarith [sq_nonneg (a+1)],by nlinarith [sq_nonneg (a-1)]⟩
  exact ⟨hbound x (by nlinarith [sq_nonneg y,sq_nonneg z]), hbound y (by nlinarith [sq_nonneg x,sq_nonneg z]),
    hbound z (by nlinarith [sq_nonneg x,sq_nonneg y])⟩
def admissible (v : Triple) : Prop := Odd v.1 ∧ Odd v.2.1 ∧ v.2.2%4=0
instance (v : Triple) : Decidable (admissible v) := by unfold admissible; infer_instance
def coordWeight (v : Triple) : ℤ := if admissible v then ((v.2.2/4).negOnePow : ℤ) else 0
def rot (v : Triple) : Triple := (v.2.1,v.2.2,v.1)
def weight (v : Triple) : ℤ := coordWeight v + coordWeight (rot v) + coordWeight (rot (rot v))
lemma rotation_sum (N : ℕ) (f : Triple → ℤ) :
    ∑ v ∈ shell N, f (rot v) = ∑ v ∈ shell N, f v := by
  apply sum_nbij' rot (fun v => rot (rot v))
  · rintro ⟨x,y,z⟩ h
    simp only [mem_shell,normSq,rot] at h ⊢
    linarith
  · rintro ⟨x,y,z⟩ h
    simp only [mem_shell,normSq,rot] at h ⊢
    linarith
  all_goals intro v _; rfl
lemma sum_weight (N : ℕ) : ∑ v ∈ shell N, weight v = 3*∑ v ∈ shell N, coordWeight v := by
  change ∑ v ∈ _, (coordWeight v+coordWeight (rot v)+coordWeight (rot (rot v))) = _
  simp only [sum_add_distrib]
  rw [rotation_sum N (fun v => coordWeight (rot v)),rotation_sum N coordWeight]
  ring
def slice (N : ℕ) (P : ℤ → Prop) : Set Triple :=
  {v | (v ∈ shell N ∧ admissible v) ∧ P (v.2.2/4)}
lemma sum_coordWeight (N : ℕ) : ∑ v ∈ shell N, coordWeight v =
    (slice N Even).ncard - ((slice N Odd).ncard : ℤ) := by
  calc
    _ = ∑ v ∈ shell N, if v∈shell N ∧ admissible v then ((v.2.2 / 4).negOnePow : ℤ) else 0 := by
      apply sum_congr rfl; intro v hv; simp [coordWeight,hv]
    _ = _ := sum_sign_eq_ncard (shell N) _ _ (fun _ h => h.1)
lemma slice_card {m : ℕ} (hm : m%4=1) (P : ℤ → Prop) :
    (slice (2*m) P).ncard = 2* {v ∈ D (2*m) | P v.2.2}.ncard := by
  let S := slice (2*m) P
  let good := {v ∈ S | v.1%4 = v.2.1%4}
  let bad := {v ∈ S | v.1%4 ≠ v.2.1%4}
  have hf : S.Finite := (shell (2*m)).finite_toSet.subset (fun _ h => h.1.1)
  have hsplit : S = good ∪ bad := by ext v; simp [good,bad]; tauto
  have hdis : Disjoint good bad := Set.disjoint_left.mpr (fun _ hu hv => hv.2 hu.2)
  have hpair : bad.ncard = good.ncard := by
    apply Set.ncard_congr (fun v _ => (-v.1,v.2.1,v.2.2))
    · rintro ⟨x,y,z⟩ ⟨⟨⟨hs,hx,hy,hz⟩,hp⟩,hne⟩
      have hx' := Int.odd_iff.mp hx
      have hy' := Int.odd_iff.mp hy
      exact ⟨⟨⟨by simpa [normSq] using hs,by simpa using hx,hy,hz⟩,hp⟩,by dsimp at hne hx' hy' ⊢; omega⟩
    · rintro ⟨x,y,z⟩ ⟨x',y',z'⟩ _ _ h; simpa using h
    · rintro ⟨x,y,z⟩ ⟨⟨⟨hs,hx,hy,hz⟩,hp⟩,he⟩
      have hx' := Int.odd_iff.mp hx
      exact ⟨(-x,y,z),⟨⟨⟨by simpa [normSq] using hs,by simpa using hx,hy,hz⟩,hp⟩,by dsimp at he hx' ⊢; omega⟩,by simp⟩
  have count : {v ∈ D (2*m) | P v.2.2}.ncard = good.ncard := by
    apply Set.ncard_congr (fun v _ => (v.2.1+2*v.1,v.2.1-2*v.1,4*v.2.2))
    · rintro ⟨r,a,t⟩ ⟨hd,hp⟩
      have ha := y_residues (n:=2*m) (by omega) hd
      have ha' : Odd a := Int.odd_iff.mpr (by omega)
      change ((2*m:ℕ):ℤ)=8*r^2+2*a^2+16*t^2 at hd
      refine ⟨⟨⟨mem_shell.mpr ?_,Int.odd_iff.mpr (by change (a+2*r)%2=1; omega),Int.odd_iff.mpr (by change (a-2*r)%2=1; omega),by dsimp; omega⟩,?_⟩,by dsimp; omega⟩
      · dsimp [normSq]; push_cast at hd; linear_combination -hd
      · simpa using hp
    · rintro ⟨r,a,t⟩ ⟨r',a',t'⟩ h h' he
      simp only [Prod.mk.injEq] at he ⊢
      exact ⟨by omega,by omega,by omega⟩
    · rintro ⟨x,y,z⟩ ⟨⟨⟨hs,hx,hy,hz⟩,hp⟩,he⟩
      have hx' := Int.odd_iff.mp hx
      have hy' := Int.odd_iff.mp hy
      change x%4=y%4 at he
      change z%4=0 at hz
      let r := (x-y)/4
      let a := (x+y)/2
      let t := z/4
      have h1 : a+2*r=x := by dsimp [a,r]; omega
      have h2 : a-2*r=y := by dsimp [a,r]; omega
      have h3 : 4*t=z := by dsimp [t]; omega
      refine ⟨(r,a,t),⟨?_,hp⟩,by simp [h1,h2,h3]⟩
      have hs' := mem_shell.mp hs
      change x^2+y^2+z^2=((2*m:ℕ):ℤ) at hs'
      rw [← h1,← h2,← h3] at hs'
      change ((2*m:ℕ):ℤ)=8*r^2+2*a^2+16*t^2
      linear_combination -hs'
  change S.ncard = _
  rw [hsplit,Set.ncard_union_eq hdis (hf.subset (Set.sep_subset _ _)) (hf.subset (Set.sep_subset _ _)), hpair, ←count]
  omega
noncomputable def b (m : ℕ) : ℤ :=
  let X : PowerSeries ℤ := PowerSeries.X
  PowerSeries.coeff m (X * (∏' k : ℕ, (1-X^(8*(k+1)))) * (∏' k : ℕ, (1-X^(16*(k+1)))) *
    (1+2*∑' k : ℕ, X^(4*(k+1)^2)))
lemma b_zero {m : ℕ} (hm : m%4≠1) : b m=0 := by
  have empty (P : ℤ→Prop) :
      {t : Triple | 1 + 8*pentagonal t.1 + 16*pentagonal t.2.1 + 4*t.2.2.natAbs^2=m ∧
        P (t.1+t.2.1)} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro t ht
    have h := ht.1
    omega
  rw [b,← FourierSeries.finite_eq_infinite, coefficient_count,empty Even,empty Odd]
  simp
lemma odd_square_mod8 (x : ℤ) (hx : Odd x) : x^2%8=1 := by
  have h := Int.odd_iff.mp hx
  have h0 := Int.emod_nonneg x (by decide : (8:ℤ) ≠ 0)
  have h8 := Int.emod_lt_of_pos x (by decide : (0:ℤ) < 8)
  rw [sq,Int.mul_emod]
  interval_cases he : x%8 <;> omega
lemma admissible_residue {m : ℕ} {v : Triple} (hv : v∈shell (2*m)) (ha : admissible v) : m%4=1 := by
  rcases v with ⟨x,y,z⟩
  obtain ⟨hx,hy,hz⟩ := ha
  change z%4=0 at hz
  have h1 := odd_square_mod8 x hx
  have h2 := odd_square_mod8 y hy
  have hz' : z=4*(z/4) := by omega
  have h3 : z^2%8=0 := by
    rw [show z^2 = 8*(2*(z/4)^2) by nth_rw 1 [hz']; ring]
    simp
  have he := mem_shell.mp hv
  change x^2+y^2+z^2=((2*m:ℕ):ℤ) at he
  push_cast at he
  omega
theorem sum_weight_eq_twelve (m : ℕ) : (∑ v ∈ shell (2*m),weight v) = 12*b m := by
  rw [sum_weight]
  by_cases hm : m%4=1
  · rw [sum_coordWeight, slice_card hm Even, slice_card hm Odd]
    have hn : (2*m)%8=2 := by omega
    have hb := signed_theta_expansion (2*m) hn
    dsimp only at hb
    simp only [Nat.mul_div_cancel_left _ (by decide : 0<2)] at hb
    rw [FourierSeries.finite_eq_infinite] at hb
    change b m = _ at hb
    have hE := sign_pairing hn (finite_D (2*m)) Even
    have hO := sign_pairing hn (finite_D (2*m)) Odd
    omega
  · have hz : (∑ v ∈ shell (2*m), coordWeight v) = 0 := by
      apply sum_eq_zero
      intro v hv
      exact if_neg (fun ha => hm (admissible_residue hv ha))
    rw [hz,b_zero hm]
    ring
end TunnellShell
end


/- TunnellHurwitzEmbeddings -/
section
namespace TunnellHurwitz
open Quaternion TunnellShell
def pure (v : Triple) : Q := ⟨0,v.1,v.2.1,v.2.2⟩
lemma pure_mem (v : Triple) : pure v∈order := integer_coords 0 _ _ _
lemma pure_injective : Function.Injective pure := by
  intro v w h
  have hi := congrArg QuaternionAlgebra.imI h
  have hj := congrArg QuaternionAlgebra.imJ h
  have hk := congrArg QuaternionAlgebra.imK h
  dsimp [pure] at hi hj hk
  exact Prod.ext (by exact_mod_cast hi) (Prod.ext (by exact_mod_cast hj) (by exact_mod_cast hk))
lemma trace_zero_integral {q : Q} (hq : q∈order) (hr : q.re=0) : ∃ v, q=pure v := by
  obtain ⟨⟨a,b,c,d⟩,rfl⟩ := hq
  change (a:ℚ)+d/2=0 at hr
  refine ⟨(b-a,c-a,-a),?_⟩
  apply QuaternionAlgebra.ext <;> dsimp [hamZ,TunnellHurwitzFour.ham,pure] <;> push_cast <;> linarith
lemma pure_norm (v : Triple) : Quaternion.normSq (pure v)=(TunnellShell.normSq v:ℚ) := by
  rw [Quaternion.normSq_def']
  simp [pure,TunnellShell.normSq]
def quadraticValue (d : ℕ) (v : Triple) (z : Zsqrtd (-(d:ℤ))) : Q :=
  ⟨z.re,z.im*v.1,z.im*v.2.1,z.im*v.2.2⟩
def embed (d : ℕ) (v : Triple) (hv : v∈shell d) : Zsqrtd (-(d:ℤ)) →+* Q where
  toFun := quadraticValue d v
  map_one' := by
    apply QuaternionAlgebra.ext <;> dsimp [quadraticValue] <;> simp
  map_zero' := by
    apply QuaternionAlgebra.ext <;> dsimp [quadraticValue] <;> simp
  map_add' x y := by
    apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_add,Quaternion.imI_add,Quaternion.imJ_add,Quaternion.imK_add]
    all_goals dsimp [quadraticValue]; push_cast; ring
  map_mul' x y := by
    have hn := mem_shell.mp hv
    change _^2+_^2+_^2=(d:ℤ) at hn
    have hq : (v.1:ℚ)^2+(v.2.1:ℚ)^2+(v.2.2:ℚ)^2=d := by exact_mod_cast hn
    apply QuaternionAlgebra.ext
    · rw [Quaternion.re_mul]
      dsimp [quadraticValue]; push_cast
      linear_combination (x.im:ℚ)*y.im*hq
    · rw [Quaternion.imI_mul]; dsimp [quadraticValue]; push_cast; ring
    · rw [Quaternion.imJ_mul]; dsimp [quadraticValue]; push_cast; ring
    · rw [Quaternion.imK_mul]; dsimp [quadraticValue]; push_cast; ring
lemma embed_root (d : ℕ) (v : Triple) (hv : v∈shell d) : embed d v hv Zsqrtd.sqrtd=pure v := by
  change quadraticValue d v _=_
  apply QuaternionAlgebra.ext <;> simp [quadraticValue,pure]
lemma embed_integral (d : ℕ) (v : Triple) (hv : v∈shell d) (z) : embed d v hv z ∈ order := by
  have he : embed d v hv z = (⟨z.re,(z.im*v.1:ℤ),(z.im*v.2.1:ℤ),(z.im*v.2.2:ℤ)⟩ : Q) := by
    change quadraticValue d v z=_
    apply QuaternionAlgebra.ext <;> simp [quadraticValue]
  rw [he]
  exact integer_coords _ _ _ _
lemma negative_root {d : ℕ} (hd : 0<d) (q : Q) (h : q*q= -(d:Q)) :
    q.re=0 ∧ Quaternion.normSq q=d := by
  have h₀ := congrArg QuaternionAlgebra.re h
  have h₁ := congrArg QuaternionAlgebra.imI h
  have h₂ := congrArg QuaternionAlgebra.imJ h
  have h₃ := congrArg QuaternionAlgebra.imK h
  simp only [Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,
    Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg,
    Quaternion.re_natCast,Quaternion.imI_natCast,Quaternion.imJ_natCast,Quaternion.imK_natCast,neg_zero] at h₀ h₁ h₂ h₃
  have hr : q.re=0 := by
    by_contra hr
    have hI : q.imI=0 := (mul_eq_zero.mp (show q.re*q.imI=0 by nlinarith [h₁])).resolve_left hr
    have hJ : q.imJ=0 := (mul_eq_zero.mp (show q.re*q.imJ=0 by nlinarith [h₂])).resolve_left hr
    have hK : q.imK=0 := (mul_eq_zero.mp (show q.re*q.imK=0 by nlinarith [h₃])).resolve_left hr
    rw [hI,hJ,hK] at h₀
    have hp : (0:ℚ)<d := by exact_mod_cast hd
    nlinarith [sq_nonneg q.re]
  exact ⟨hr,by rw [normSq_def',hr]; rw [hr] at h₀; nlinarith⟩
end TunnellHurwitz
end


/- TunnellHurwitzOptimal -/
section
namespace TunnellHurwitz
open Quaternion TunnellShell TunnellHurwitzFour
lemma primitive {n : ℕ} (hs : Squarefree n) {v : Triple} (hv : v∈shell n) :
    ∃ a b c : ℤ, v.1*a+v.2.1*b+v.2.2*c=1 := by
  obtain ⟨x,y,z⟩ := v
  let g := Int.gcd x y
  let h := Int.gcd (g:ℤ) z
  have hg (u : ℤ) (hu : (g:ℤ) ∣ u) : (h:ℤ) ∣ u := (Int.gcd_dvd_left (g:ℤ) z).trans hu
  obtain ⟨a,ha⟩ := hg x (Int.gcd_dvd_left x y)
  obtain ⟨b,hb⟩ := hg y (Int.gcd_dvd_right x y)
  obtain ⟨c,hc⟩ := Int.gcd_dvd_right (g:ℤ) z
  have hn := mem_shell.mp hv
  change x^2+y^2+z^2=(n:ℤ) at hn
  have hdiv : (h:ℤ)*(h:ℤ) ∣ n := by
    refine ⟨a^2+b^2+c^2,?_⟩
    rw [←hn,ha,hb,hc]; ring
  have hd : h*h ∣ n := by exact_mod_cast hdiv
  have h1 := Nat.isUnit_iff.mp (hs h hd)
  let u := Int.gcdA (g:ℤ) z
  let w := Int.gcdB (g:ℤ) z
  refine ⟨Int.gcdA x y*u,Int.gcdB x y*u,w,?_⟩
  have hg' := Int.gcd_eq_gcd_ab x y
  have hh := Int.gcd_eq_gcd_ab (g:ℤ) z
  change (g:ℤ)=_ at hg'
  change (h:ℤ)=g*u+z*w at hh
  dsimp only
  rw [h1] at hh
  norm_cast at hh
  linear_combination -hh - u*hg'
def evalRat (v : Triple) (a b : ℚ) : Q := ⟨a,b*v.1,b*v.2.1,b*v.2.2⟩
lemma eval_norm {n : ℕ} {v : Triple} (hv : v∈shell n) (a b : ℚ) :
    normSq (evalRat v a b)=a^2+n*b^2 := by
  have h := mem_shell.mp hv
  change v.1^2+v.2.1^2+v.2.2^2=(n:ℤ) at h
  have hh : (v.1:ℚ)^2+(v.2.1:ℚ)^2+(v.2.2:ℚ)^2=n := by exact_mod_cast h
  rw [normSq_def']; dsimp [evalRat]; linear_combination b^2*hh
lemma doubled_coords {q : Q} (hq : q∈order) :
    ∃ A B C D : ℤ, (A:ℚ)=2*q.re ∧ (B:ℚ)=2*q.imI ∧ (C:ℚ)=2*q.imJ ∧ (D:ℚ)=2*q.imK := by
  obtain ⟨⟨a,b,c,d⟩,rfl⟩ := hq
  refine ⟨2*a+d,2*b+d,2*c+d,d,?_⟩
  refine ⟨?_,?_,?_,?_⟩ <;> dsimp [hamZ,ham] <;> push_cast <;> ring
lemma optimal {n : ℕ} (hs : Squarefree n) (h2 : n%4=2) {v : Triple} (hv : v∈shell n) (a b : ℚ) :
    evalRat v a b∈order ↔ (∃ x : ℤ, a=x) ∧ (∃ y : ℤ, b=y) := by
  constructor
  · intro h
    obtain ⟨i,j,k,hi⟩ := primitive hs hv
    obtain ⟨A,B,C,D,hA,hB,hC,hD⟩ := doubled_coords h
    dsimp only [evalRat] at hA hB hC hD
    let E := i*B+j*C+k*D
    have hE : (E:ℚ)=2*b := by
      have hi' : (v.1:ℚ)*i+(v.2.1:ℚ)*j+(v.2.2:ℚ)*k=1 := by exact_mod_cast hi
      dsimp [E]; push_cast
      linear_combination (i:ℚ)*hB+(j:ℚ)*hC+(k:ℚ)*hD+2*b*hi'
    obtain ⟨N,hN⟩ := norm_int h
    rw [eval_norm hv] at hN
    have eqn : A^2+(n:ℤ)*E^2=4*(N:ℤ) := by
      have ee : (A:ℚ)^2+(n:ℚ)*(E:ℚ)^2=4*N := by
        rw [hA,hE]; linear_combination 4*hN
      exact_mod_cast ee
    have chk : ∀ x y : ZMod 4, x^2+2*y^2=0 → x.val%2=0 ∧ y.val%2=0 := by decide
    have hn : (n:ZMod 4)=2 := by apply ZMod.val_injective 4; rw [ZMod.val_natCast,h2]; decide
    have heq := congrArg (fun u:ℤ => (u:ZMod 4)) eqn
    push_cast at heq
    rw [hn] at heq
    have hh := chk (A:ZMod 4) (E:ZMod 4) (by simpa only [show (4:ZMod 4)=0 by decide,zero_mul] using heq)
    have hAv := ZMod.val_intCast (n:=4) A
    have hEv := ZMod.val_intCast (n:=4) E
    have ha : (A/2:ℤ)*2=A := by omega
    have hb : (E/2:ℤ)*2=E := by omega
    refine ⟨⟨A/2,?_⟩,⟨E/2,?_⟩⟩
    · have h' : ((A/2:ℤ):ℚ)*2=A := by exact_mod_cast ha
      linarith
    · have h' : ((E/2:ℤ):ℚ)*2=E := by exact_mod_cast hb
      linarith
  · rintro ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩
    exact embed_integral n v hv ⟨a,b⟩
lemma centralizer {n : ℕ} (hs : Squarefree n) {v : Triple} (hv : v∈shell n) (q : Q)
    (h : q*pure v=pure v*q) : ∃ b : ℚ, q=evalRat v q.re b := by
  obtain ⟨i,j,k,hi⟩ := primitive hs hv
  have hi' : (v.1:ℚ)*i+(v.2.1:ℚ)*j+(v.2.2:ℚ)*k=1 := by exact_mod_cast hi
  have e₁ := congrArg QuaternionAlgebra.imI h
  have e₂ := congrArg QuaternionAlgebra.imJ h
  have e₃ := congrArg QuaternionAlgebra.imK h
  rw [Quaternion.imI_mul,Quaternion.imI_mul] at e₁
  rw [Quaternion.imJ_mul,Quaternion.imJ_mul] at e₂
  rw [Quaternion.imK_mul,Quaternion.imK_mul] at e₃
  dsimp [pure] at e₁ e₂ e₃
  refine ⟨i*q.imI+j*q.imJ+k*q.imK,?_⟩
  apply QuaternionAlgebra.ext
  · rfl
  · dsimp [evalRat]; linear_combination -q.imI*hi'+(j:ℚ)/2*e₃-(k:ℚ)/2*e₂
  · dsimp [evalRat]; linear_combination -q.imJ*hi'-(i:ℚ)/2*e₃+(k:ℚ)/2*e₁
  · dsimp [evalRat]; linear_combination -q.imK*hi'+(i:ℚ)/2*e₂-(j:ℚ)/2*e₁
lemma integral_centralizer {n : ℕ} (hs : Squarefree n) (h2 : n%4=2) {v : Triple}
    (hv : v∈shell n) {q : Q} (hq : q∈order) (h : q*pure v=pure v*q) :
    ∃ z, q=embed n v hv z := by
  obtain ⟨b,hb⟩ := centralizer hs hv q h
  have hl : evalRat v q.re b ∈ order := hb ▸ hq
  obtain ⟨⟨x,hx⟩,⟨y,hy⟩⟩ := (optimal hs h2 hv q.re b).mp hl
  refine ⟨⟨x,y⟩,?_⟩
  calc q = evalRat v q.re b := hb
       _ = _ := by rw [hx,hy]; rfl
end TunnellHurwitz
end


/- TunnellToricIntertwiners -/
section
namespace TunnellHurwitz
open TunnellShell Quaternion
lemma pure_square {n : ℕ} {v : Triple} (hv : v∈shell n) : pure v*pure v=-(n:Q) := by
  have h := congrArg (embed n v hv) (Zsqrtd.dmuld (d:=-(n:ℤ)))
  simpa only [map_mul,embed_root,map_intCast,map_neg,map_natCast,Int.cast_neg,Int.cast_natCast] using h
lemma intertwine {n : ℕ} (v w : Triple) (hv : v∈shell n) (hw : w∈shell n) :
    ∃ q∈order, q≠0 ∧ pure w*q=q*pure v := by
  by_cases h : pure w+pure v=0
  · have hw' : pure w= -pure v := eq_neg_of_add_eq_zero_left h
    obtain ⟨a,b,c⟩ := v
    by_cases hab : a=0 ∧ b=0
    · obtain ⟨rfl,rfl⟩ := hab
      let q : Q := pure (1,0,0)
      refine ⟨q,pure_mem _,fun he => ?_,?_⟩
      · have t := congrArg QuaternionAlgebra.imI he
        norm_num [q,pure] at t
      · rw [hw',neg_mul]
        apply QuaternionAlgebra.ext <;>
          simp only [Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg,
          Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul]
        all_goals simp [pure,q]
    · let q : Q := pure (-b,a,0)
      refine ⟨q,pure_mem _,fun he => ?_,?_⟩
      · apply hab
        have h1 := congrArg QuaternionAlgebra.imI he
        have h2 := congrArg QuaternionAlgebra.imJ he
        simp [q,pure] at h1 h2
        exact ⟨h2,h1⟩
      · rw [hw',neg_mul]
        apply QuaternionAlgebra.ext <;>
          simp only [Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg,
          Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul]
        all_goals simp [pure,q] <;> ring
  · exact ⟨pure w+pure v,order.add_mem (pure_mem _) (pure_mem _),h,
      by rw [mul_add,add_mul,pure_square hw,pure_square hv,add_comm]⟩
def intertwiner (v w : Triple) : AddSubgroup Q where
  carrier := {q | q∈order ∧ pure w*q=q*pure v}
  zero_mem' := by simp
  add_mem' := by
    rintro a b ⟨ha,hea⟩ ⟨hb,heb⟩
    exact ⟨order.add_mem ha hb,by rw [mul_add,add_mul,hea,heb]⟩
  neg_mem' := by rintro a ⟨ha,he⟩; exact ⟨order.neg_mem ha,by rw [mul_neg,neg_mul,he]⟩
lemma intertwiner_comp {u v w : Triple} {a b : Q} (ha : a∈intertwiner v w) (hb : b∈intertwiner u v) :
    a*b∈intertwiner u w := by
  exact ⟨order.mul_mem ha.1 hb.1,by rw [←mul_assoc,ha.2,mul_assoc,hb.2,mul_assoc]⟩
end TunnellHurwitz
end


/- TunnellQuaternionSplit -/
section
namespace TunnellQuaternion
open Matrix Quaternion
variable {K : Type*} [Field K]
def matrixOf (a b : K) (x : Quaternion K) : Matrix (Fin 2) (Fin 2) K :=
  !![x.re + a*x.imJ + b*x.imK, x.imI+b*x.imJ-a*x.imK;
     -x.imI+b*x.imJ-a*x.imK, x.re-a*x.imJ-b*x.imK]
def splitHom (a b : K) (hab : a^2+b^2 = -1) : Quaternion K →+* Matrix (Fin 2) (Fin 2) K where
  toFun := matrixOf a b
  map_zero' := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf]
  map_one' := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf]
  map_add' x y := by ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf] <;> ring
  map_mul' x y := by
    have hb : b^2= -1-a^2 := by linear_combination hab
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [matrixOf,Matrix.mul_apply,Fin.sum_univ_two] <;> ring_nf <;> rw [hb] <;> ring
lemma split_det (a b : K) (hab : a^2+b^2 = -1) (x : Quaternion K) :
    (splitHom a b hab x).det = normSq x := by
  change (matrixOf a b x).det = _
  simp [Matrix.det_fin_two,matrixOf,normSq_def']
  linear_combination -(x.imJ^2+x.imK^2)*hab
lemma split_trace (a b : K) (hab : a^2+b^2 = -1) (x : Quaternion K) :
    (splitHom a b hab x).trace = 2*x.re := by
  change (matrixOf a b x).trace = _
  simp [Matrix.trace_fin_two,matrixOf]
  ring
lemma split_star (a b : K) (hab : a^2+b^2 = -1) (x : Quaternion K) :
    splitHom a b hab (star x) = (splitHom a b hab x).adjugate := by
  change matrixOf a b (star x) = (matrixOf a b x).adjugate
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [matrixOf] <;> ring
def quaternionOf (a b : K) (m : Matrix (Fin 2) (Fin 2) K) : Quaternion K :=
  ⟨(m 0 0+m 1 1)/2,(m 0 1-m 1 0)/2,
    -(a*(m 0 0-m 1 1) + b*(m 0 1+m 1 0))/2,
    -(b*(m 0 0-m 1 1) - a*(m 0 1+m 1 0))/2⟩
lemma split_iso (a b : K) (hab : a^2+b^2 = -1) (htwo : (2:K) ≠ 0) :
    Function.Bijective (splitHom a b hab) := by
  have hb : b^2 = -1-a^2 := by linear_combination hab
  have left : Function.LeftInverse (quaternionOf a b) (splitHom a b hab) := by
    intro x
    change quaternionOf a b (matrixOf a b x) = x
    ext <;> dsimp [matrixOf,quaternionOf] <;> field_simp <;> ring_nf <;> rw [hb] <;> ring
  have right : Function.RightInverse (quaternionOf a b) (splitHom a b hab) := by
    intro M
    change matrixOf a b (quaternionOf a b M) = M
    ext i j
    fin_cases i <;> fin_cases j <;> dsimp [matrixOf,quaternionOf] <;> field_simp <;> ring_nf <;> rw [hb] <;> ring
  exact ⟨left.injective,right.surjective⟩
lemma exists_splitting (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    ∃ a b : ZMod p, a^2+b^2 = -1 ∧ (2:ZMod p) ≠ 0 := by
  obtain ⟨a,b,ha,hb,h⟩ := Nat.sq_add_sq_zmodEq p (-1)
  refine ⟨a,b,?_,?_⟩
  · exact_mod_cast ((ZMod.intCast_eq_intCast_iff _ _ _).mpr h)
  · intro he
    have hh := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using he)
    have := (Nat.dvd_prime Nat.prime_two).mp hh
    have := (Fact.out : p.Prime).ne_one
    tauto
end TunnellQuaternion
end


/- TunnellQuaternionLine -/
section
namespace TunnellQuaternion
open Matrix
variable {K : Type*} [Field K]
abbrev M2 (K : Type*) := Matrix (Fin 2) (Fin 2) K
abbrev V2 (K : Type*) := Fin 2 → K
def inLine (l : Option K) (M : M2 K) : Prop :=
  match l with
  | none => ∀ j, M 0 j = 0
  | some r => ∀ j, M 1 j = r*M 0 j
def direction (l : Option K) : V2 K := match l with
  | none => ![0,1]
  | some r => ![1,r]
def rowOf (l : Option K) (M : M2 K) : V2 K := match l with
  | none => M 1
  | some _ => M 0
lemma line_factored {l : Option K} {M : M2 K} (h : inLine l M) :
    vecMulVec (direction l) (rowOf l M) = M := by
  ext i j
  cases l <;> fin_cases i <;> fin_cases j <;> simp_all [inLine,rowOf,direction,vecMulVec]
lemma line_mul {l : Option K} {M : M2 K} (h : inLine l M) (B : M2 K) :
    inLine l (M*B) := by
  cases l with
  | none => change ∀ j, M 0 j = 0 at h; intro j; simp [Matrix.mul_apply,h]
  | some r =>
    intro j
    change ∀ j, M 1 j=r*M 0 j at h
    simp [Matrix.mul_apply,h,mul_assoc,mul_add]
lemma line_smul {l : Option K} {M : M2 K} (h : inLine l M) (t : K) :
    inLine l (t • M) := by
  cases l with
  | none => change ∀ j, M 0 j = 0 at h; intro j; simp [h]
  | some r => intro j; change ∀ j, M 1 j = r*M 0 j at h; simp [h,mul_left_comm]
lemma det_line {l : Option K} {M : M2 K} (h : inLine l M) : M.det=0 := by
  cases l <;> simp_all [inLine, Matrix.det_fin_two] <;> ring
lemma line_unique (M : M2 K) (h : M≠0) (hd : M.det=0) : ∃! l, inLine l M := by
  by_cases h0 : ∀ j, M 0 j=0
  · refine ⟨none,h0,?_⟩
    rintro (_|r) he
    · rfl
    · change ∀ j, M 1 j=r*M 0 j at he; exfalso; apply h; ext i j; fin_cases i <;> simp [h0,he]
  · obtain ⟨j,hj⟩ := not_forall.mp h0
    refine ⟨some (M 1 j/M 0 j),?_,?_⟩
    · intro k
      rw [div_mul_eq_mul_div,eq_div_iff hj]
      rw [Matrix.det_fin_two] at hd
      fin_cases j <;> fin_cases k
      · rfl
      · change M 1 1 * M 0 0 = M 1 0 * M 0 1; linear_combination hd
      · change M 1 0 * M 0 1 = M 1 1 * M 0 0; linear_combination -hd
      · rfl
    · rintro (_|r) he
      · exact False.elim (hj (he j))
      · congr 1
        exact (eq_div_iff hj).mpr (he j).symm
lemma adj_mul_zero_iff {l : Option K} {A : M2 K} (hA : A≠0)
    (hdl : inLine l A) (B : M2 K) : A.adjugate * B = 0 ↔ inLine l B := by
  by_cases hr : rowOf l A = 0
  · have := line_factored hdl
    rw [hr, Matrix.vecMulVec_zero] at this
    exact False.elim (hA this.symm)
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hr
  rw [Matrix.adjugate_fin_two]
  cases l with
  | none =>
    change ∀ j, A 0 j=0 at hdl
    change A 1 i ≠ 0 at hi
    constructor
    · intro h j
      have h₀ := congrArg (fun M:M2 K => M 0 j) h
      have h₁ := congrArg (fun M:M2 K => M 1 j) h
      simp [Matrix.mul_apply,Fin.sum_univ_two,hdl] at h₀ h₁
      fin_cases i <;> grind
    · intro h; change ∀ j, B 0 j=0 at h; ext i j; fin_cases i <;> simp [Matrix.mul_apply,Fin.sum_univ_two,hdl,h]
  | some r =>
    change ∀ j, A 1 j=r*A 0 j at hdl
    change A 0 i ≠ 0 at hi
    constructor
    · intro h j
      have h₀ := congrArg (fun M:M2 K => M 0 j) h
      have h₁ := congrArg (fun M:M2 K => M 1 j) h
      simp [Matrix.mul_apply,Fin.sum_univ_two,hdl] at h₀ h₁
      fin_cases i
      · apply mul_left_cancel₀ hi
        change A 0 0 * B 1 j = A 0 0 * (r*B 0 j)
        linear_combination h₁
      · apply mul_left_cancel₀ hi
        change A 0 1 * B 1 j = A 0 1 * (r*B 0 j)
        linear_combination -h₀
    · intro h; change ∀ j, B 1 j=r*B 0 j at h
      ext i j; fin_cases i <;> simp [Matrix.mul_apply,Fin.sum_univ_two,hdl,h] <;> ring
end TunnellQuaternion
end


/- TunnellQuaternionLift -/
section
namespace TunnellQuaternion
open Quaternion
def redFun (p : ℕ) (q : Quaternion ℤ) : Quaternion (ZMod p) := ⟨q.re,q.imI,q.imJ,q.imK⟩
def red (p : ℕ) : Quaternion ℤ →+* Quaternion (ZMod p) where
  toFun := redFun p
  map_add' x y := by apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_add,Quaternion.imI_add,Quaternion.imJ_add,Quaternion.imK_add] <;> simp [redFun]
  map_mul' x y := by
    apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul] <;> simp [redFun]
  map_zero' := by ext <;> simp [redFun]
  map_one' := by ext <;> simp [redFun]
lemma red_apply (p : ℕ) (x : Quaternion ℤ) : red p x = redFun p x := rfl
lemma red_star (p : ℕ) (x : Quaternion ℤ) : red p (star x) = star (red p x) := by
  change redFun p (star x) = star (redFun p x)
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star] <;> simp [redFun]
lemma red_norm (p : ℕ) (x : Quaternion ℤ) : ((normSq x:ℤ) : ZMod p) = normSq (red p x) := by
  rw [normSq_def',normSq_def']
  simp [red_apply,redFun]
lemma red_smul (p : ℕ) (t : ℤ) (x : Quaternion ℤ) :
    red p (t • x) = (t:ZMod p) • red p x := by
  change redFun p (t • x) = (t:ZMod p) • redFun p x
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_smul,Quaternion.imI_smul,Quaternion.imJ_smul,Quaternion.imK_smul] <;> simp [redFun,smul_eq_mul]
lemma norm_smul (t : ℤ) (x : Quaternion ℤ) : normSq (t • x) = t^2*normSq x := by
  rw [← coe_mul_eq_smul, map_mul, normSq_coe]
lemma div_iff (m : ℕ) (q : Quaternion ℤ) : red m q = 0 ↔ ∃ v : Quaternion ℤ, q = (m:ℤ) • v := by
  constructor
  · intro h
    have hd (a : ℤ) (ha : (a:ZMod m)=0) : a=(m:ℤ)*(a/m) :=
      (Int.mul_ediv_cancel' (ZMod.intCast_zmod_eq_zero_iff_dvd a m |>.mp ha)).symm
    refine ⟨⟨q.re/m,q.imI/m,q.imJ/m,q.imK/m⟩,?_⟩
    cases q with | mk a b c d =>
      exact QuaternionAlgebra.ext (hd a (congrArg (fun q : Quaternion (ZMod m) => q.re) h)) (hd b (congrArg (fun q : Quaternion (ZMod m) => q.imI) h))
        (hd c (congrArg (fun q : Quaternion (ZMod m) => q.imJ) h)) (hd d (congrArg (fun q : Quaternion (ZMod m) => q.imK) h))
  · rintro ⟨v,rfl⟩
    rw [red_smul]; simp
def lift (m : ℕ) (x : Quaternion (ZMod m)) : Quaternion ℤ :=
  ⟨x.re.valMinAbs,x.imI.valMinAbs,x.imJ.valMinAbs,x.imK.valMinAbs⟩
@[simp] lemma red_lift (m : ℕ) (x : Quaternion (ZMod m)) : red m (lift m x)=x := by
  change redFun m (lift m x)=x
  apply QuaternionAlgebra.ext <;> dsimp only [redFun,lift] <;> simp
lemma norm_lift_lt {m : ℕ} [NeZero m] (hm : Odd m) (x : Quaternion (ZMod m)) :
    normSq (lift m x) < (m:ℤ)^2 := by
  have hn : 0<(m:ℤ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne m))
  have h (a : ZMod m) : 4*a.valMinAbs^2 < (m:ℤ)^2 := by
    obtain ⟨hl,hu⟩ := a.valMinAbs_mem_Ioc
    have hm' := hm
    rcases hm' with ⟨k,hk⟩
    have hu2 : a.valMinAbs*2 < (m:ℤ) := by omega
    nlinarith [mul_pos (sub_pos.mpr hu2) (by linarith [hl] : 0<(m:ℤ)+a.valMinAbs*2)]
  rw [normSq_def']
  dsimp only [lift]
  linarith [h x.re,h x.imI,h x.imJ,h x.imK]
lemma even_descent (x : Quaternion ℤ) (h : Even (normSq x)) :
    ∃ r : Quaternion ℤ, normSq r=2 ∧ red 2 (x*r)=0 := by
  let i : Quaternion ℤ := ⟨1,1,0,0⟩
  let j : Quaternion ℤ := ⟨1,0,1,0⟩
  let k : Quaternion ℤ := ⟨1,0,0,1⟩
  have ee : normSq (red 2 x)=0 := by rw [←red_norm]; exact h.intCast_zmod_two
  letI : DecidableEq (Quaternion (ZMod 2)) := (Quaternion.equivProd _).decidableEq
  have claim : ∀ w : Quaternion (ZMod 2), normSq w=0 →
      w*red 2 i=0 ∨ w*red 2 j=0 ∨ w*red 2 k=0 := by
    intro ⟨a,b,c,d⟩
    revert a b c d
    decide
  rcases claim _ ee with h|h|h
  · exact ⟨i,by decide, by simpa using h⟩
  · exact ⟨j,by decide, by simpa using h⟩
  · exact ⟨k,by decide, by simpa using h⟩
theorem find_generator {p : ℕ} (hp : p.Prime) (ho : p ≠ 2) (S : Set (Quaternion (ZMod p)))
    (hS : ∀ a ∈ S, ∀ b, a*b ∈ S)
    (hSc : ∀ (r : ZMod p) a, a ∈ S → r • a ∈ S)
    (hzero : ∀ a ∈ S, normSq a=0) (hne : ∃ a ∈ S, a≠0) :
    ∃ q : Quaternion ℤ, normSq q = p ∧ red p q ∈ S := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hodd := hp.odd_of_ne_two ho
  have initial : ∃ m : ℕ, 0 < m ∧ m < p ∧ ∃ x : Quaternion ℤ, normSq x = (m:ℤ)*p ∧ red p x ∈ S := by
    obtain ⟨a,ha,ha0⟩ := hne
    let x := lift p a
    have hr : red p x = a := red_lift p a
    have hd : (p:ℤ) ∣ normSq x := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      (by rw [red_norm,hr,hzero _ ha])
    obtain ⟨v,hv⟩ := hd
    have hx : 0 < normSq x := (normSq_nonneg (a:=x)).lt_of_ne' (normSq_ne_zero.mpr
      (fun he => ha0 (by rw [←hr,he,map_zero])))
    have hpos : 0 < v := pos_of_mul_pos_right (hv ▸ hx) (by positivity : (0:ℤ) ≤ p)
    have hlt := norm_lift_lt hodd a
    change normSq x < (p:ℤ)^2 at hlt
    refine ⟨v.toNat,by omega,?_,x,?_,hr ▸ ha⟩
    · rw [hv,sq] at hlt
      have := lt_of_mul_lt_mul_left hlt (by positivity : (0:ℤ) ≤ p)
      omega
    · rw [Int.toNat_of_nonneg hpos.le,hv,mul_comm]
  obtain ⟨m,⟨hm0,hmp,x,hx,hxs⟩,minimal⟩ := Nat.findX initial
  by_cases hm1 : m=1
  · subst m; exact ⟨x,by simpa using hx,hxs⟩
  have hm : 1 < m := by omega
  have hp0 : (0:ℤ) < p := by exact_mod_cast hp.pos
  have hm0' : (0:ℤ) < m := by exact_mod_cast hm0
  have preserve {d : ℕ} (hd : 0 < d) (hdp : d < p) {r y : Quaternion ℤ}
      (hy : x*r = (d:ℤ) • y) : red p y ∈ S := by
    have hd0 : (d:ZMod p)≠0 := fun hh =>
      have hh' := (ZMod.natCast_eq_zero_iff _ _).mp hh
      (Nat.not_dvd_of_pos_of_lt hd hdp) hh'
    have hs := hS _ hxs (red p r)
    rw [←map_mul,hy,red_smul] at hs
    have := hSc ((d:ZMod p)⁻¹) _ hs
    simpa [smul_smul,hd0] using this
  exfalso
  by_cases he : Even m
  · obtain ⟨u,hu⟩ := he
    have hx2 : Even (normSq x) := by rw [hx]; exact (by exact_mod_cast (show Even m from ⟨u,hu⟩) : Even (m:ℤ)).mul_right _
    obtain ⟨r,hr,hr0⟩ := even_descent x hx2
    obtain ⟨y,hy⟩ := (div_iff 2 _).mp hr0
    have hnorm := congrArg normSq hy
    rw [map_mul,hx,hr,norm_smul] at hnorm
    have hu' : (m:ℤ)=u+u := by exact_mod_cast hu
    refine minimal u (by omega) ⟨by omega,by omega,y,?_,preserve (d:=2) (by decide) (by omega) hy⟩
    norm_num at hnorm
    nlinarith [congrArg (fun k:ℤ => k*p) hu']
  · have hmOdd := Nat.not_even_iff_odd.mp he
    letI : NeZero m := ⟨hm0.ne'⟩
    let r := lift m (red m x)
    have hr : red m r = red m x := red_lift m _
    have hm_norm : ((normSq x:ℤ):ZMod m)=0 := by simp [hx]
    have hd : (m:ℤ) ∣ normSq r := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (by
      rw [red_norm,hr,←red_norm]; exact hm_norm)
    obtain ⟨u,hu⟩ := hd
    have hr0 : r≠0 := by
      intro hz
      have hz' : red m x=0 := by rw [←hr,hz,map_zero]
      obtain ⟨w,hw⟩ := (div_iff m x).mp hz'
      rw [hw,norm_smul] at hx
      have hdiv : (m:ℤ) ∣ p := ⟨normSq w,by
        apply mul_left_cancel₀ hm0'.ne' (b := (p:ℤ))
        nlinarith [hx]⟩
      have hdvd : m ∣ p := by exact_mod_cast hdiv
      rcases (Nat.dvd_prime hp).mp hdvd with ee|ee <;> omega
    have hupos : 0 < u := pos_of_mul_pos_right (hu ▸ (normSq_nonneg (a:=r)).lt_of_ne' (normSq_ne_zero.mpr hr0)) hm0'.le
    have hless := norm_lift_lt hmOdd (red m x)
    change normSq r < (m:ℤ)^2 at hless
    rw [hu,sq] at hless
    have huLt := lt_of_mul_lt_mul_left hless hm0'.le
    have hz : red m (x*star r)=0 := by
      rw [map_mul,red_star,hr,self_mul_star,←red_norm,hm_norm,coe_zero]
    obtain ⟨y,hy⟩ := (div_iff m _).mp hz
    have hnorm := congrArg normSq hy
    rw [map_mul,normSq_star,norm_smul,hx,hu] at hnorm
    refine minimal u.toNat (by omega) ⟨by omega,by omega,y,?_,preserve hm0 hmp hy⟩
    rw [Int.toNat_of_nonneg hupos.le]
    apply mul_left_cancel₀ (pow_ne_zero 2 hm0'.ne') (b := normSq y)
    linear_combination -hnorm
end TunnellQuaternion
end


/- TunnellQuaternionModel -/
section
namespace TunnellQuaternion
open Matrix Quaternion
variable {p : ℕ} [Fact p.Prime]
structure Model (p : ℕ) where
  f : Quaternion (ZMod p) ≃+* M2 (ZMod p)
  det (x) : (f x).det=normSq x
  trace (x) : (f x).trace=2*x.re
  bar (x) : f (star x) = (f x).adjugate
  smul (t : ZMod p) (x) : f (t • x)=t • f x
noncomputable def localModel (hp : p≠2) : Model p := Classical.choice <| by
  classical
  obtain ⟨a,b,hab,h2⟩ := exists_splitting p hp
  refine ⟨?_⟩
  exact ⟨RingEquiv.ofBijective (splitHom a b hab) (split_iso a b hab h2),split_det a b hab,
    split_trace a b hab,split_star a b hab,fun t x => by
      change matrixOf a b (t • x) = t • matrixOf a b x
      ext i j; fin_cases i <;> fin_cases j <;> simp [matrixOf] <;> ring⟩
variable (M : Model p)
def residue : Quaternion ℤ →+* M2 (ZMod p) := M.f.toRingHom.comp (red p)
lemma residue_zero (x : Quaternion ℤ) : residue M x = 0 ↔ red p x = 0 :=
  M.f.map_eq_zero_iff
lemma residue_star (x : Quaternion ℤ) : residue M (star x) = (residue M x).adjugate := by
  change M.f (red p (star x)) = _
  rw [red_star,M.bar]
  rfl
lemma residue_det (x : Quaternion ℤ) : (residue M x).det = (normSq x : ℤ) :=
  (M.det _).trans (red_norm p x).symm
lemma norm_prime_nonzero {x : Quaternion ℤ} (hx : normSq x = p) : residue M x ≠ 0 := by
  intro h
  obtain ⟨v,hv⟩ := (div_iff p x).mp ((residue_zero M x).mp h)
  have pp := Fact.out (p:=p.Prime)
  have hh := congrArg normSq hv
  rw [hx,norm_smul,pow_two,mul_assoc] at hh
  have eq := mul_left_cancel₀ (by exact_mod_cast pp.ne_zero : (p:ℤ)≠0)
    (show (p:ℤ)*1=p*((p:ℤ)*normSq v) by simpa using hh)
  have hd : (p:ℤ) ∣ 1 := ⟨_,eq⟩
  have hdn : p ∣ 1 := by exact_mod_cast hd
  exact pp.not_dvd_one hdn
lemma exists_at_line (hp : p≠2) (l : Option (ZMod p)) :
    ∃ x : Quaternion ℤ, normSq x = p ∧ inLine l (residue M x) := by
  let S := {a : Quaternion (ZMod p) | inLine l (M.f a)}
  apply find_generator Fact.out hp S
  · intro a ha b; change inLine l (M.f (a*b)); rw [map_mul]; exact line_mul ha _
  · intro r a ha; change inLine l (M.f (r • a)); rw [M.smul]; exact line_smul ha _
  · intro a ha; rw [←M.det]; exact det_line ha
  · let B : M2 (ZMod p) := vecMulVec (direction l) ![1,0]
    refine ⟨M.f.symm B,?_,?_⟩
    · change inLine l (M.f (M.f.symm B))
      rw [M.f.apply_symm_apply]
      cases l <;> intro j <;> fin_cases j <;> simp [B,vecMulVec,direction]
    · intro h
      have := congrArg M.f h
      rw [M.f.apply_symm_apply,map_zero] at this
      cases l with
      | none => simpa [B,vecMulVec,direction] using congrArg (fun m:M2 (ZMod p) => m 1 0) this
      | some r => simpa [B,vecMulVec,direction] using congrArg (fun m:M2 (ZMod p) => m 0 0) this
lemma scalar_cancel (d : ℤ) (hd : d≠0) {x y : Quaternion ℤ} (h : d • x = d • y) : x=y := by
  apply QuaternionAlgebra.ext
  all_goals
    first
    | exact mul_left_cancel₀ hd (congrArg (fun x:Quaternion ℤ => x.re) h)
    | exact mul_left_cancel₀ hd (congrArg (fun x:Quaternion ℤ => x.imI) h)
    | exact mul_left_cancel₀ hd (congrArg (fun x:Quaternion ℤ => x.imJ) h)
    | exact mul_left_cancel₀ hd (congrArg (fun x:Quaternion ℤ => x.imK) h)
lemma divide_left {q w : Quaternion ℤ} (hq : normSq q=p) {l : Option (ZMod p)}
    (hl : inLine l (residue M q)) (hw : inLine l (residue M w)) :
    ∃ x, w=q*x := by
  have hz := (adj_mul_zero_iff (norm_prime_nonzero M hq) hl (residue M w)).mpr hw
  rw [←residue_star,←map_mul,residue_zero] at hz
  obtain ⟨x,hx⟩ := (div_iff p _).mp hz
  refine ⟨x,?_⟩
  apply scalar_cancel (p:ℤ) (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have he := congrArg (q*·) hx
  simpa only [←mul_assoc,self_mul_star,hq,coe_mul_eq_smul,Algebra.mul_smul_comm] using he
lemma same_line_iff {q w : Quaternion ℤ} (hq : normSq q=p) (hw : normSq w=p)
    {l : Option (ZMod p)} (hl : inLine l (residue M q)) :
    inLine l (residue M w) ↔ ∃ u : Quaternion ℤ, normSq u=1 ∧ w=q*u := by
  constructor
  · intro hh
    obtain ⟨u,hu⟩ := divide_left M hq hl hh
    have h := hw
    rw [hu,map_mul,hq] at h
    refine ⟨u,?_,hu⟩
    apply mul_left_cancel₀ (by exact_mod_cast (Fact.out:p.Prime).ne_zero : (p:ℤ)≠0)
    simpa using h
  · rintro ⟨u,_,rfl⟩; rw [map_mul]; exact line_mul hl _
end TunnellQuaternion
end


/- TunnellQuaternionOrbit -/
section
namespace TunnellQuaternion
open Finset Quaternion TunnellShell
abbrev QInt := Quaternion ℤ
lemma normSq_mk (a b c d : ℤ) : Quaternion.normSq (⟨a,b,c,d⟩:QInt) = a^2+b^2+c^2+d^2 := Quaternion.normSq_def' _
abbrev coordsEquiv := Quaternion.equivProd ℤ
def quatShell (N : ℕ) : Finset QInt :=
  let I := Icc (-(N:ℤ)) (N:ℤ)
  ((I ×ˢ (I ×ˢ (I ×ˢ I))).map coordsEquiv.symm.toEmbedding).filter (fun q => Quaternion.normSq q=N)
@[simp] lemma mem_quatShell {q : QInt} {N : ℕ} : q ∈ quatShell N ↔ Quaternion.normSq q=N := by
  simp only [quatShell,mem_filter,mem_map_equiv]
  refine ⟨And.right,fun hn => ⟨?_,hn⟩⟩
  rw [Quaternion.normSq_def'] at hn
  obtain ⟨a,b,c,d⟩ := q
  change a^2+b^2+c^2+d^2 = (N:ℤ) at hn
  simp only [mem_product,mem_Icc]
  change (- (N:ℤ) ≤ a ∧ a ≤ N) ∧ (- (N:ℤ) ≤ b ∧ b ≤ N) ∧
    (- (N:ℤ) ≤ c ∧ c ≤ N) ∧ - (N:ℤ) ≤ d ∧ d ≤ N
  have hb (x : ℤ) (h : x^2 ≤ N) : -(N:ℤ) ≤ x ∧ x ≤ N := by
    constructor <;> by_contra! he
    · have := mul_nonneg_of_nonpos_of_nonpos (by omega : x ≤ 0) (by omega : x+1 ≤ 0)
      nlinarith
    · have := mul_nonneg (by omega : 0 ≤ x) (by omega : 0 ≤ x-1)
      nlinarith
  exact ⟨hb _ (by nlinarith [sq_nonneg b,sq_nonneg c,sq_nonneg d]),
    hb _ (by nlinarith [sq_nonneg a,sq_nonneg c,sq_nonneg d]),
    hb _ (by nlinarith [sq_nonneg a,sq_nonneg b,sq_nonneg d]),
    hb _ (by nlinarith [sq_nonneg a,sq_nonneg b,sq_nonneg c])⟩
def pure (v : Triple) : QInt := ⟨0,v.1,v.2.1,v.2.2⟩
def vec (q : QInt) : Triple := (q.imI,q.imJ,q.imK)
def rotate (q : QInt) (v : Triple) : Triple := vec (q*pure v*star q)
lemma rotate_apply (a b c d x y z : ℤ) :
    rotate ⟨a,b,c,d⟩ (x,y,z) =
      ((a^2+b^2-c^2-d^2)*x+2*(b*c-a*d)*y+2*(b*d+a*c)*z,
       2*(b*c+a*d)*x+(a^2-b^2+c^2-d^2)*y+2*(c*d-a*b)*z,
       2*(b*d-a*c)*x+2*(c*d+a*b)*y+(a^2-b^2-c^2+d^2)*z) := by
  suffices h : ∀ (q : QInt) (v : Triple), rotate q v =
      ((q.re^2+q.imI^2-q.imJ^2-q.imK^2)*v.1+2*(q.imI*q.imJ-q.re*q.imK)*v.2.1+2*(q.imI*q.imK+q.re*q.imJ)*v.2.2,
       2*(q.imI*q.imJ+q.re*q.imK)*v.1+(q.re^2-q.imI^2+q.imJ^2-q.imK^2)*v.2.1+2*(q.imJ*q.imK-q.re*q.imI)*v.2.2,
       2*(q.imI*q.imK-q.re*q.imJ)*v.1+2*(q.imJ*q.imK+q.re*q.imI)*v.2.1+(q.re^2-q.imI^2-q.imJ^2+q.imK^2)*v.2.2) from h _ _
  intro q v
  ext <;> simp only [rotate,vec,Quaternion.re_mul, Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul, Quaternion.re_star, Quaternion.imI_star, Quaternion.imJ_star, Quaternion.imK_star] <;> simp [pure] <;> ring
def lastWeight (z : ℤ) : ℤ := if z%8=0 then 1 else if z%8=4 then -1 else 0
lemma coordWeight_eq (x y z : ℤ) : coordWeight (x,y,z) =
    if Odd x ∧ Odd y then lastWeight z else 0 := by
  by_cases hx : Odd x <;> by_cases hy : Odd y <;> simp [coordWeight,admissible,hx,hy,lastWeight]
  split_ifs with h h' h''
  all_goals first
    | (rw [Int.negOnePow_even _ (Int.even_iff.mpr (by omega))]; rfl)
    | (rw [Int.negOnePow_odd _ (Int.odd_iff.mpr (by omega))]; rfl)
    | omega
lemma lastWeight_neg (z : ℤ) : lastWeight (-z) = lastWeight z := by
  unfold lastWeight
  split_ifs <;> omega
lemma lastWeight_congr {a b : ℤ} (h : a ≡ b [ZMOD 8]) : lastWeight a = lastWeight b := by
  simp only [lastWeight,show a%8=b%8 from h]
lemma lastWeight_add_four (z k : ℤ) : lastWeight (z+4*k) = (k.negOnePow:ℤ)*lastWeight z := by
  obtain ⟨r,hr|hr⟩ := Int.even_or_odd' k <;> subst k
  · rw [Int.negOnePow_two_mul]
    simp only [Units.val_one,one_mul]
    apply lastWeight_congr
    exact Int.modEq_iff_dvd.mpr ⟨-r,by ring⟩
  · rw [Int.negOnePow_two_mul_add_one]
    simp only [Units.val_neg,Units.val_one,neg_one_mul,lastWeight]
    split_ifs <;> omega
end TunnellQuaternion
end


/- TunnellShellFibers -/
section
namespace TunnellShellFibers
open Finset TunnellShell
def divisible (p : ℕ) (v : Triple) : Prop := (p:ℤ) ∣ v.1 ∧ (p:ℤ) ∣ v.2.1 ∧ (p:ℤ) ∣ v.2.2
end TunnellShellFibers
end


/- TunnellQuaternionIncidence -/
section
namespace TunnellQuaternion
open Quaternion Finset TunnellShell
lemma norm_pure (v : Triple) : Quaternion.normSq (pure v)=TunnellShell.normSq v := by
  rw [Quaternion.normSq_def']
  change (0:ℤ)^2+v.1^2+v.2.1^2+v.2.2^2=_
  simp [TunnellShell.normSq]
variable {p : ℕ} [Fact p.Prime] (M : Model p)
lemma residue_trace (w : QInt) : (residue M w).trace=2*(w.re:ZMod p) :=
  M.trace _
lemma residue_pure_zero (v : Triple) :
    residue M (pure v)=0 ↔ TunnellShellFibers.divisible p v := by
  rw [residue_zero]
  constructor
  · intro h
    refine ⟨(ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrArg QuaternionAlgebra.imI h),
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrArg QuaternionAlgebra.imJ h),
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrArg QuaternionAlgebra.imK h)⟩
  · rintro ⟨a,b,c⟩
    apply QuaternionAlgebra.ext
    · exact Int.cast_zero
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr a
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr b
    · exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr c
end TunnellQuaternion
end


/- TunnellToricOddLocal -/
section
namespace TunnellToricLocal
open Matrix TunnellQuaternion
variable {K : Type*} [Field K]
def cyclicBasis (x y : K) (A : M2 K) : M2 K :=
  !![x,A 0 0*x+A 0 1*y;y,A 1 0*x+A 1 1*y]
lemma cyclic_exists (A : M2 K) (h2 : (2:K)≠0) (hn : A≠0) (ht : A.trace=0) :
    ∃ x y : K, (cyclicBasis x y A).det ≠ 0 := by
  by_contra! h
  have h1 := h 1 0
  have h2' := h 0 1
  have h3 := h 1 1
  simp only [cyclicBasis,det_fin_two,of_apply,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_fin_one,one_mul,mul_one,zero_mul,mul_zero,zero_add,add_zero,sub_zero,zero_sub,neg_eq_zero] at h1 h2' h3
  have htt : A 0 0+A 1 1=0 := by simpa [Matrix.trace,Fin.sum_univ_two] using ht
  have hd : A 0 0=0 := (mul_eq_zero.mp (show 2*A 0 0=0 by linear_combination htt - h3 - h2' + h1)).resolve_left h2
  apply hn
  ext i j
  fin_cases i <;> fin_cases j <;> simp_all
lemma cyclic_action (A : M2 K) (ht : A.trace=0) (x y : K) :
    A*cyclicBasis x y A = cyclicBasis x y A*!![0,-A.det;1,0] := by
  have htt : A 0 0+A 1 1=0 := by simpa [Matrix.trace,Fin.sum_univ_two] using ht
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [cyclicBasis,det_fin_two,mul_apply,Fin.sum_univ_two]
  all_goals first | linear_combination (A 0 0*x+A 0 1*y)*htt | linear_combination (A 1 0*x+A 1 1*y)*htt
lemma matrix_intertwiner (V W : M2 K) (h2 : (2:K)≠0) (hv : V≠0) (hw : W≠0)
    (htv : V.trace=0) (htw : W.trace=0) (hd : V.det=W.det) :
    ∃ S : M2 K, (W*S+S*V).det≠0 := by
  obtain ⟨x,y,hb⟩ := cyclic_exists V h2 hv htv
  obtain ⟨u,v,hc⟩ := cyclic_exists W h2 hw htw
  let B := cyclicBasis x y V
  let C := cyclicBasis u v W
  let J : M2 K := !![0,-V.det;1,0]
  let T : M2 K := !![0,1;0,0]
  have heB : V*B=B*J := cyclic_action V htv _ _
  have heC : W*C=C*J := by simpa [C,J,hd] using cyclic_action W htw u v
  have hIB : J*B⁻¹=B⁻¹*V := by
    have hu := (isUnit_iff_ne_zero.mpr hb : IsUnit B.det)
    calc J*B⁻¹ = B⁻¹*(B*J)*B⁻¹ := by simp [←mul_assoc,Matrix.nonsing_inv_mul B hu]
         _ = _ := by rw [←heB]; simp [mul_assoc,Matrix.mul_nonsing_inv B hu]
  have hJT : J*T+T*J=1 := by ext i j; fin_cases i <;> fin_cases j <;> simp [J,T,mul_apply,Fin.sum_univ_two]
  refine ⟨C*T*B⁻¹,?_⟩
  have h : W*(C*T*B⁻¹)+C*T*B⁻¹*V=C*B⁻¹ := by
    calc _=C*(J*T+T*J)*B⁻¹ := by
           rw [mul_add,add_mul]
           simp only [mul_assoc]
           rw [←hIB]
           simp only [←mul_assoc,heC]
         _=_ := by rw [hJT,mul_one]
  rw [h,det_mul,det_nonsing_inv,Ring.inverse_eq_inv]
  exact mul_ne_zero hc (inv_ne_zero hb)
variable {p : ℕ} [Fact p.Prime]
lemma residue_surj (M : Model p) (S : M2 (ZMod p)) :
    residue M (lift p (M.f.symm S))=S := by
  change M.f (red p (lift p (M.f.symm S)))=S
  rw [red_lift,M.f.apply_symm_apply]
lemma residue_nonzero (M : Model p) {n : ℕ} (hs : Squarefree n) {v : TunnellShell.Triple}
    (hv : v∈TunnellShell.shell n) : residue M (TunnellQuaternion.pure v)≠0 := by
  intro hz
  obtain ⟨hx,hy,hz⟩ := (residue_pure_zero M v).mp hz
  obtain ⟨a,b,c,he⟩ := TunnellHurwitz.primitive hs hv
  have hdiv : (p:ℤ)∣1 := he ▸ dvd_add (dvd_add (dvd_mul_of_dvd_left hx a) (dvd_mul_of_dvd_left hy b)) (dvd_mul_of_dvd_left hz c)
  exact (Fact.out : p.Prime).not_dvd_one (by exact_mod_cast hdiv)
lemma coprime_intertwiner (hp : p≠2) {n : ℕ} (hs : Squarefree n) (v w : TunnellShell.Triple)
    (hv : v∈TunnellShell.shell n) (hw : w∈TunnellShell.shell n) :
    ∃ q : Quaternion ℤ, TunnellQuaternion.pure w*q=q*TunnellQuaternion.pure v ∧ ¬ (p:ℤ) ∣ Quaternion.normSq q := by
  let M := localModel hp
  let V := residue M (TunnellQuaternion.pure v)
  let W := residue M (TunnellQuaternion.pure w)
  have ht (u : TunnellShell.Triple) : (residue M (TunnellQuaternion.pure u)).trace=0 := by
    rw [residue_trace]; simp [TunnellQuaternion.pure]
  have hd : V.det=W.det := by
    change (residue M _).det=(residue M _).det
    rw [residue_det,residue_det,norm_pure,norm_pure,TunnellShell.mem_shell.mp hv,TunnellShell.mem_shell.mp hw]
  have h2 : (2:ZMod p)≠0 := by
    intro hh
    have hp2 : p∣2 := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using hh)
    exact hp ((Nat.dvd_prime Nat.prime_two).mp hp2 |>.resolve_left (Fact.out : p.Prime).ne_one)
  obtain ⟨S,hS⟩ := matrix_intertwiner V W h2 (residue_nonzero M hs hv) (residue_nonzero M hs hw) (ht v) (ht w) hd
  let s := lift p (M.f.symm S)
  let q := TunnellQuaternion.pure w*s+s*TunnellQuaternion.pure v
  have he (u : TunnellShell.Triple) (hu : u∈TunnellShell.shell n) : TunnellQuaternion.pure u*TunnellQuaternion.pure u=-(n:Quaternion ℤ) := by
    have hm : star (TunnellQuaternion.pure u) = -TunnellQuaternion.pure u := by
      apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg,
        Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star] <;> simp [TunnellQuaternion.pure]
    have hn := Quaternion.self_mul_star (TunnellQuaternion.pure u)
    rw [hm,mul_neg,norm_pure,TunnellShell.mem_shell.mp hu] at hn
    simpa only [neg_neg,Quaternion.coe_natCast] using congrArg Neg.neg hn
  refine ⟨q,?_,?_⟩
  · dsimp only [q]
    rw [mul_add,add_mul,←mul_assoc,he w hw,mul_assoc s,he v hv,mul_assoc,neg_mul,mul_neg]
    rw [Nat.cast_comm,add_comm]
  · intro h
    apply hS
    have hq : residue M q=W*S+S*V := by simp only [q,map_add,map_mul,s,residue_surj,W,V]
    rw [←hq,residue_det]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h
end TunnellToricLocal
end


/- TunnellToricTwoLocal -/
section
namespace TunnellToricLocal
open TunnellHurwitz TunnellHurwitzFour TunnellShell Quaternion
def modTwo (u : H ℤ) : H (ZMod 2) := (u.1,u.2.1,u.2.2.1,u.2.2.2)
lemma modTwo_prod (x y : H ℤ) : modTwo (prod x y)=prod (modTwo x) (modTwo y) := by
  rcases x with ⟨a,b,c,d⟩; rcases y with ⟨e,f,g,h⟩
  simp [modTwo,prod]
lemma modTwo_nr (x : H ℤ) : ((nr x:ℤ):ZMod 2)=nr (modTwo x) := by
  rcases x with ⟨a,b,c,d⟩
  simp [modTwo,nr]
lemma norm_raw (u : H ℤ) : Quaternion.normSq (hamZ u)=((nr u:ℤ):ℚ) := by simp [hamZ,ham_norm,nr]
lemma half_integral {a b : Q} (ha : a∈order) (hb : b∈order) {A B : ℕ} (hA : Quaternion.normSq a=A)
    (hB : Quaternion.normSq b=B) (heA : Even A) (heB : Even B) : ∃ r∈order, a*b=(2:ℚ) • r := by
  obtain ⟨u,rfl⟩ := ha; obtain ⟨v,rfl⟩ := hb
  have ht : ∀ x y : H (ZMod 2), nr x=0 → nr y=0 → prod x y=0 := by decide
  have hz (u : H ℤ) (N : ℕ) (hh : Quaternion.normSq (hamZ u)=N) (he : Even N) : nr (modTwo u)=0 := by
    rw [norm_raw] at hh
    have hn : nr u=(N:ℤ) := by exact_mod_cast hh
    rw [←modTwo_nr,hn]; exact_mod_cast (ZMod.natCast_eq_zero_iff N 2).mpr he.two_dvd
  have h := ht _ _ (hz u A hA heA) (hz v B hB heB)
  rw [←modTwo_prod] at h
  rw [←hamZ_mul]
  generalize prod u v=z at *
  obtain ⟨a,b,c,d⟩ := z
  have hh (x : ℤ) (hx : (x:ZMod 2)=0) : x=2*(x/2) :=
    (Int.mul_ediv_cancel' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hx)).symm
  have ha := hh a (congrArg Prod.fst h)
  have hb := hh b (congrArg (fun x : H (ZMod 2) => x.2.1) h)
  have hc := hh c (congrArg (fun x : H (ZMod 2) => x.2.2.1) h)
  have hd := hh d (congrArg (fun x : H (ZMod 2) => x.2.2.2) h)
  let w : H ℤ := (a/2,b/2,c/2,d/2)
  refine ⟨hamZ w,⟨w,rfl⟩,?_⟩
  change hamZ (a,b,c,d) = (2:ℚ) • hamZ w
  have hvec : (a,b,c,d)=w+w := by apply Prod.ext <;> simp [w,Prod.ext_iff] <;> omega
  rw [hvec,hamZ_add,←two_smul ℚ]
theorem odd_intertwiner {n : ℕ} (hn : n%4=2) (v w : Triple) (hv : v∈shell n) (hw : w∈shell n) :
    ∃ q∈intertwiner v w, ∃ N : ℕ, Quaternion.normSq q=N ∧ Odd N := by
  classical
  let P (k : ℕ) := ∃ q∈intertwiner v w, ∃ N : ℕ, 0<N ∧ Quaternion.normSq q=N ∧ padicValNat 2 N=k
  obtain ⟨q,hq,hne,hi⟩ := intertwine v w hv hw
  obtain ⟨N,hN⟩ := norm_int hq
  have hNz : N≠0 := by rintro rfl; exact hne (Quaternion.normSq_eq_zero.mp (by simpa using hN))
  have hEx : ∃ k, P k := ⟨_,q,⟨hq,hi⟩,N,Nat.pos_of_ne_zero hNz,hN,rfl⟩
  obtain ⟨r,hr,m,hm,hnr,hval⟩ := Nat.find_spec hEx
  refine ⟨r,hr,m,hnr,?_⟩
  by_contra hodd
  obtain ⟨t,ht,htr⟩ := half_integral hr.1 (pure_mem v) hnr
    (by rw [pure_norm,TunnellShell.mem_shell.mp hv]; simp) (Nat.not_odd_iff_even.mp hodd)
    (Nat.even_iff.mpr (by omega : n%2=0))
  have he : t∈intertwiner v w := by
    refine ⟨ht,?_⟩
    apply smul_right_injective Q (by norm_num : (2:ℚ)≠0)
    change (2:ℚ) • (TunnellHurwitz.pure w*t)=(2:ℚ) • (t*TunnellHurwitz.pure v)
    calc _ = TunnellHurwitz.pure w * ((2:ℚ) • t) := (Algebra.mul_smul_comm _ _ _).symm
         _ = ((2:ℚ) • t)*TunnellHurwitz.pure v := by rw [←htr,←mul_assoc,hr.2]
         _ = _ := smul_mul_assoc _ _ _
  obtain ⟨T,hT⟩ := norm_int ht
  have hprod := congrArg Quaternion.normSq htr
  rw [map_mul,hnr,pure_norm,TunnellShell.mem_shell.mp hv,←Quaternion.coe_mul_eq_smul,map_mul,Quaternion.normSq_coe,hT] at hprod
  have heN : m*n=4*T := by exact_mod_cast (show (m:ℚ)*n=4*T by push_cast at hprod; linarith)
  have hTp : 0<T := Nat.pos_of_ne_zero (by rintro rfl; simp at heN; omega)
  have hval' := congrArg (padicValNat 2) heN
  let K := n/2
  have hnK : n=2*K := by dsimp [K]; omega
  have hK : 0<K := by dsimp [K]; omega
  have hK₂ : ¬2∣K := by dsimp [K]; omega
  rw [hnK,padicValNat.mul (by omega) (by positivity),padicValNat.mul (by decide) hK.ne',
    padicValNat.mul (by decide) hTp.ne',padicValNat.eq_zero_of_not_dvd hK₂,
    padicValNat_self,show padicValNat 2 4=2 by rw [show 4=2*2 by decide,padicValNat.mul (by decide) (by decide),padicValNat_self]] at hval'
  have hle := Nat.find_min' hEx (show P (padicValNat 2 T) from ⟨t,he,T,hTp,hT,rfl⟩)
  omega
end TunnellToricLocal
end


/- TunnellIdealGroupoid -/
section
namespace TunnellToricLocal
open TunnellHurwitz TunnellHurwitzFour TunnellShell Quaternion
def rat (a : Quaternion ℤ) : Q := ⟨a.re,a.imI,a.imJ,a.imK⟩
lemma rat_mul (a b : Quaternion ℤ) : rat (a*b)=rat a*rat b := by
  apply QuaternionAlgebra.ext
  all_goals
    first | rw [Quaternion.re_mul] | rw [Quaternion.imI_mul] | rw [Quaternion.imJ_mul] | rw [Quaternion.imK_mul]
    dsimp only [rat]
    simp only [Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,Int.cast_sub,Int.cast_mul,Int.cast_add]
lemma rat_norm (a : Quaternion ℤ) : Quaternion.normSq (rat a)=((Quaternion.normSq a:ℤ):ℚ) := by
  rw [Quaternion.normSq_def',Quaternion.normSq_def']; simp [rat]
lemma local_prime (p n : ℕ) (hp : p.Prime) (hn : Squarefree n) (h2 : n%4=2)
    (v w : Triple) (hv : v∈shell n) (hw : w∈shell n) :
    ∃ q∈intertwiner v w, ∃ N : ℤ, Quaternion.normSq q=(N:ℚ) ∧ ¬(p:ℤ)∣N := by
  by_cases hp2 : p=2
  · subst p
    obtain ⟨q,hq,N,hN,ho⟩ := odd_intertwiner h2 v w hv hw
    exact ⟨q,hq,N,by simpa using hN,by exact_mod_cast (Nat.not_even_iff_odd.mpr ho : ¬Even N) ∘ (fun h : (2:ℕ)∣N => even_iff_two_dvd.mpr h)⟩
  · letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨q,he,hd⟩ := coprime_intertwiner hp2 hn v w hv hw
    refine ⟨rat q,⟨integer_coords _ _ _ _,?_⟩,_,rat_norm _,hd⟩
    have h := congrArg rat he
    simp only [rat_mul] at h
    exact h
def norms (v w : Triple) : Set ℤ := {N | ∃ q∈intertwiner v w, Quaternion.normSq q=(N:ℚ)}
lemma norm_ideal_top {n : ℕ} (hn : Squarefree n) (h2 : n%4=2)
    (v w : Triple) (hv : v∈shell n) (hw : w∈shell n) : Ideal.span (norms v w)=⊤ := by
  let I := Ideal.span (norms v w)
  let g := Submodule.IsPrincipal.generator I
  suffices h : IsUnit g from I.eq_top_of_isUnit_mem (Submodule.IsPrincipal.generator_mem I) h
  by_contra h
  have hg : g.natAbs ≠ 1 := by intro hh; exact h (by simpa [Int.isUnit_iff_natAbs_eq] using hh)
  obtain ⟨p,hp,hd⟩ := Nat.exists_prime_and_dvd hg
  obtain ⟨q,hq,N,hN,he⟩ := local_prime p n hp hn h2 v w hv hw
  have him : N∈I := Ideal.subset_span (show N∈norms v w from ⟨q,hq,hN⟩)
  exact he ((Int.natCast_dvd.mpr hd).trans ((Submodule.IsPrincipal.mem_iff_generator_dvd I).mp him))
lemma star_order {q : Q} (hq : q∈order) : star q∈order := by
  obtain ⟨⟨a,b,c,d⟩,rfl⟩ := hq
  refine ⟨(a+d,-b,-c,-d),?_⟩
  apply QuaternionAlgebra.ext
  all_goals simp only [Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star] <;> simp [hamZ,ham] <;> ring
lemma pure_star (v : Triple) : star (TunnellHurwitz.pure v)= -TunnellHurwitz.pure v := by
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg,
    Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star] <;> simp [TunnellHurwitz.pure]
lemma star_intertwines {v w : Triple} {q : Q} (hq : q∈intertwiner v w) : star q∈intertwiner w v := by
  have he := congrArg star hq.2
  simp only [star_mul,pure_star,mul_neg,neg_mul,neg_inj] at he
  exact ⟨star_order hq.1,he.symm⟩
def idealProd (A B : AddSubgroup Q) : Submodule ℤ Q := Submodule.span ℤ {x | ∃ a∈A, ∃ b∈B, x=a*b}
lemma idealProd_mem {A B : AddSubgroup Q} {a b : Q} (ha : a∈A) (hb : b∈B) :
    a*b∈idealProd A B := Submodule.subset_span ⟨a,ha,b,hb,rfl⟩
lemma idealProd_one {n : ℕ} (hn : Squarefree n) (h2 : n%4=2)
    (v w : Triple) (hv : v∈shell n) (hw : w∈shell n) : (1:Q)∈idealProd (intertwiner w v) (intertwiner v w) := by
  let f : ℤ →ₗ[ℤ] Q := (Int.castRingHom Q).toAddMonoidHom.toIntLinearMap
  let I := idealProd (intertwiner w v) (intertwiner v w)
  have hle : Ideal.span (norms v w) ≤ I.comap f := by
    apply Submodule.span_le.mpr
    rintro N ⟨q,hq,hn⟩
    change (N:Q)∈I
    have he : star q*q=(N:Q) := by rw [star_mul_self,hn]; rfl
    rw [←he]
    exact idealProd_mem (star_intertwines hq) hq
  have h := hle (show (1:ℤ) ∈ Ideal.span (norms v w) by rw [norm_ideal_top hn h2 v w hv hw]; exact Submodule.mem_top)
  change ((1:ℤ):Q)∈I at h
  simpa using h
lemma compose_ideals {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) (u v w : Triple)
    (hu : u∈shell n) (hv : v∈shell n) :
    idealProd (intertwiner v w) (intertwiner u v)=(intertwiner u w).toIntSubmodule := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨a,ha,b,hb,rfl⟩
    exact intertwiner_comp ha hb
  · intro x hx
    let f : Q →ₗ[ℤ] Q := (AddMonoidHom.mulLeft x).toIntLinearMap
    let I := idealProd (intertwiner v w) (intertwiner u v)
    have hle : idealProd (intertwiner v u) (intertwiner u v) ≤ I.comap f := by
      apply Submodule.span_le.mpr
      rintro _ ⟨a,ha,b,hb,rfl⟩
      change x*(a*b)∈I
      rw [←mul_assoc]
      exact idealProd_mem (intertwiner_comp hx ha) hb
    have he := hle (idealProd_one hn h2 u v hu hv)
    change x*1∈I at he
    simpa using he
end TunnellToricLocal
end


/- TunnellTestVector -/
section
namespace TunnellTestVector
open TunnellShell Finset
open scoped Classical
def first (v : Triple) : Triple := (v.1+2*v.2.1,v.1-2*v.2.1,8*v.2.2)
def second (v : Triple) : Triple := (2*v.1+2*v.2.1+v.2.2,-2*v.1+2*v.2.1+v.2.2,-4*v.2.2)
lemma first_iff (v : Triple) : v∈Set.range first ↔ v.1%4=v.2.1%4 ∧ v.2.2%8=0 := by
  obtain ⟨x,y,z⟩ := v
  constructor
  · rintro ⟨⟨a,b,c⟩,h⟩
    simp [first,Prod.ext_iff] at h
    dsimp only
    omega
  · rintro ⟨h,hz⟩
    dsimp only at h hz
    exact ⟨((x+y)/2,(x-y)/4,z/8),by apply Prod.ext <;> simp [first,Prod.ext_iff] <;> omega⟩
lemma second_iff (v : Triple) : v∈Set.range second ↔ v.1%4=v.2.1%4 ∧
    v.2.2%4=0 ∧ (v.1+v.2.1+2*(v.2.2/4))%4=0 := by
  obtain ⟨x,y,z⟩ := v
  constructor
  · rintro ⟨⟨a,b,c⟩,h⟩
    simp [second,Prod.ext_iff] at h
    dsimp only
    omega
  · rintro ⟨h,hz,hs⟩
    dsimp only at h hz hs
    exact ⟨((x-y)/4,(x+y+2*(z/4))/4,-(z/4)),by
      apply Prod.ext <;> simp [second,Prod.ext_iff] <;> omega⟩
def same (v : Triple) : Prop := v.1%4=v.2.1%4
def positive (v : Triple) : Prop := Odd v.1 ∧ Odd v.2.1 ∧ v.2.2%8=0
def negative (v : Triple) : Prop := Odd v.1 ∧ Odd v.2.1 ∧ v.2.2%8=4
lemma odd_coordinates {d : ℕ} (hd : Odd d) {v : Triple} (hv : v∈shell (2*d)) (hz : Even v.2.2) :
    Odd v.1 ∧ Odd v.2.1 := by
  have hn := mem_shell.mp hv
  change v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ) at hn
  obtain ⟨k,hk⟩ := hd
  obtain ⟨c,hz⟩ := hz
  have hq := congrArg (fun a:ℤ => (a:ZMod 4)) hn
  push_cast at hq
  rw [hk,hz] at hq
  push_cast at hq
  have hc : ∀ x y z k : ZMod 4, x^2+y^2+(z+z)^2=2*(2*k+1) → x.val%2=1 ∧ y.val%2=1 := by decide
  obtain ⟨hx,hy⟩ := hc _ _ _ _ hq
  have hxv := ZMod.val_intCast (n:=4) v.1
  have hyv := ZMod.val_intCast (n:=4) v.2.1
  rw [Int.odd_iff,Int.odd_iff]
  omega
lemma on_shell {d : ℕ} (hd : Odd d) {v : Triple} (hv : v∈shell (2*d)) :
    (v∈Set.range first ↔ same v ∧ positive v) ∧ (v∈Set.range second ↔ same v ∧ negative v) := by
  rw [first_iff,second_iff]
  change (_ ↔ _ ∧ (Odd v.1 ∧ Odd v.2.1 ∧ _)) ∧ (_ ↔ _ ∧ (Odd v.1 ∧ Odd v.2.1 ∧ _))
  have ho (h : v.2.2%4=0) := odd_coordinates hd hv (Int.even_iff.mpr (by omega : v.2.2%2=0))
  constructor
  · exact ⟨fun ⟨h,hz⟩ => ⟨h,(ho (by omega)).1,(ho (by omega)).2,hz⟩,fun h => ⟨h.1,h.2.2.2⟩⟩
  · change (_ ↔ v.1%4=v.2.1%4 ∧ _)
    constructor
    · rintro ⟨h,hz,hs⟩
      obtain ⟨hx,hy⟩ := ho hz
      refine ⟨h,hx,hy,?_⟩
      have := Int.odd_iff.mp hx
      omega
    · rintro ⟨h,hx,hy,hz⟩
      have := Int.odd_iff.mp hx
      exact ⟨h,by omega,by omega⟩
def flip (v : Triple) : Triple := (v.1,-v.2.1,v.2.2)
lemma flip_shell {v : Triple} {n : ℕ} (hv : v∈shell n) : flip v∈shell n := by
  simpa [mem_shell,normSq,flip] using hv
lemma half_card (n : ℕ) (P : Triple → Prop) (hP : ∀ v, P (flip v) ↔ P v)
    (hod : ∀ v, P v → Odd v.1 ∧ Odd v.2.1) :
    ((shell n).filter P).card = 2*((shell n).filter (fun v => same v ∧ P v)).card := by
  let S := (shell n).filter P
  have hh : (S.filter (fun v => ¬same v)).card = (S.filter same).card := by
    apply card_nbij' flip flip
    · intro v h
      obtain ⟨hS,hs⟩ := mem_filter.mp h
      obtain ⟨hv,hp⟩ := mem_filter.mp hS
      obtain ⟨hx,hy⟩ := hod v hp
      simp only [Int.odd_iff] at hx hy
      change ¬v.1%4=v.2.1%4 at hs
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨flip_shell hv,(hP v).mpr hp⟩,
        by change v.1%4=(-v.2.1)%4; omega⟩
    · intro v h
      obtain ⟨hS,hs⟩ := mem_filter.mp h
      obtain ⟨hv,hp⟩ := mem_filter.mp hS
      obtain ⟨hx,hy⟩ := hod v hp
      simp only [Int.odd_iff] at hx hy
      change v.1%4=v.2.1%4 at hs
      exact mem_filter.mpr ⟨mem_filter.mpr ⟨flip_shell hv,(hP v).mpr hp⟩,
        by change ¬v.1%4=(-v.2.1)%4; omega⟩
    all_goals intro v _; simp [flip]
  have he := card_filter_add_card_filter_not (s:=S) same
  rw [hh] at he
  simpa [S,filter_filter,and_comm,two_mul] using he.symm
lemma coordinate (v : Triple) : coordWeight v = (if positive v then 1 else 0) - (if negative v then 1 else 0) := by
  obtain ⟨x,y,z⟩ := v
  dsimp only [coordWeight,admissible,positive,negative]
  by_cases hx : Odd x <;> by_cases hy : Odd y <;> simp only [hx,hy,true_and,false_and,ite_false,sub_zero]
  split_ifs <;> first
    | rw [Int.negOnePow_even _ (Int.even_iff.mpr (by omega))]; rfl
    | rw [Int.negOnePow_odd _ (Int.odd_iff.mpr (by omega))]; rfl
    | omega
theorem signed_shell (d : ℕ) (hd : Odd d) :
    (((shell (2*d)).filter (fun v => v∈Set.range first)).card:ℤ) -
      ((shell (2*d)).filter (fun v => v∈Set.range second)).card = 2*b d := by
  let S := shell (2*d)
  have h1 : S.filter (fun v => v∈Set.range first) = S.filter (fun v => same v ∧ positive v) :=
    filter_congr (fun _ hv => (on_shell hd hv).1)
  have h2 : S.filter (fun v => v∈Set.range second) = S.filter (fun v => same v ∧ negative v) :=
    filter_congr (fun _ hv => (on_shell hd hv).2)
  have hf := half_card (2*d) positive (fun _ => by simp [positive,flip]) (fun _ h => ⟨h.1,h.2.1⟩)
  have hg := half_card (2*d) negative (fun _ => by simp [negative,flip]) (fun _ h => ⟨h.1,h.2.1⟩)
  have hc := sum_weight_eq_twelve d
  rw [sum_weight] at hc
  simp_rw [coordinate] at hc
  simp only [sum_sub_distrib,sum_boole] at hc
  change ((S.filter (fun v => v∈Set.range first)).card:ℤ)-_=_
  rw [h1,h2]
  dsimp only [S] at *
  rw [show ((shell (2*d)).filter (fun x => positive x)).card = _ from hf,
    show ((shell (2*d)).filter (fun x => negative x)).card = _ from hg] at hc
  push_cast at hc
  omega
end TunnellTestVector
end


/- TunnellToricOrbits -/
section
namespace TunnellToric
open TunnellShell TunnellHurwitz TunnellHurwitzFour Finset Quaternion
def cyc (k : Fin 3) (v : Triple) : Triple := ![v,rot v,rot (rot v)] k
def signs (s : Fin 4) (v : Triple) : Triple :=
  ![v, (v.1,-v.2.1,-v.2.2),(-v.1,v.2.1,-v.2.2),(-v.1,-v.2.1,v.2.2)] s
def move (k : Fin 3) (s : Fin 4) (v : Triple) : Triple := signs s (cyc k v)
def basis (i : Fin 3) : Triple := ![(1,0,0),(0,1,0),(0,0,1)] i
def act (q : Q) (v : Triple) : Q := q*pure v*star q
def lin (v : Triple) (a b c : Q) : Q := (v.1:ℚ) • a+(v.2.1:ℚ) • b+(v.2.2:ℚ) • c
lemma pure_lin (v : Triple) : pure v=lin v (pure (basis 0)) (pure (basis 1)) (pure (basis 2)) := by
  apply QuaternionAlgebra.ext
  · change 0=(v.1:ℚ)*0+v.2.1*0+v.2.2*0; ring
  · change (v.1:ℚ)=(v.1:ℚ)*1+v.2.1*0+v.2.2*0; ring
  · change (v.2.1:ℚ)=(v.1:ℚ)*0+v.2.1*1+v.2.2*0; ring
  · change (v.2.2:ℚ)=(v.1:ℚ)*0+v.2.1*0+v.2.2*1; ring
lemma move_lin (k : Fin 3) (s : Fin 4) (v : Triple) :
    pure (move k s v)=lin v (pure (move k s (basis 0))) (pure (move k s (basis 1))) (pure (move k s (basis 2))) := by
  unfold lin
  apply QuaternionAlgebra.ext
  all_goals
    simp only [Quaternion.re_add,Quaternion.imI_add,Quaternion.imJ_add,Quaternion.imK_add,
      Quaternion.re_smul,Quaternion.imI_smul,Quaternion.imJ_smul,Quaternion.imK_smul]
    fin_cases k <;> fin_cases s <;> simp [TunnellHurwitz.pure,move,cyc,rot,signs,basis]
lemma act_lin (q : Q) (v : Triple) :
    act q v=lin v (act q (basis 0)) (act q (basis 1)) (act q (basis 2)) := by
  unfold act
  rw [pure_lin v]
  simp only [lin,mul_add,add_mul,Algebra.mul_smul_comm,smul_mul_assoc]
local instance : DecidableEq Q := (Quaternion.equivProd ℚ).decidableEq
noncomputable def integralUnits : Finset (H ℤ) := (Icc (-2:ℤ) 2 ×ˢ (Icc (-2:ℤ) 2 ×ˢ (Icc (-2:ℤ) 2 ×ˢ Icc (-2:ℤ) 2))).filter fun u => nr u = 1
def twice (u : H ℤ) : Quaternion ℤ := ⟨2*u.1+u.2.2.2,2*u.2.1+u.2.2.2,2*u.2.2.1+u.2.2.2,u.2.2.2⟩
def rot4 (u : H ℤ) (v : Triple) : Triple := TunnellQuaternion.rotate (twice u) v
lemma rot4_eq (u : H ℤ) (v : Triple) : pure (rot4 u v)=(4:ℚ) • act (hamZ u) v := by
  obtain ⟨a,b,c,d⟩ := u
  obtain ⟨x,y,z⟩ := v
  unfold rot4 twice
  rw [TunnellQuaternion.rotate_apply]
  apply QuaternionAlgebra.ext
  all_goals
    simp only [Quaternion.re_smul,Quaternion.imI_smul,Quaternion.imJ_smul,Quaternion.imK_smul,
      act,Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,
      Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star]
    dsimp [TunnellHurwitz.pure,hamZ,ham]
    push_cast
    ring
lemma pure_four (v : Triple) : pure ((4:ℤ) • v)=(4:ℚ) • pure v := by
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_smul,Quaternion.imI_smul,Quaternion.imJ_smul,Quaternion.imK_smul] <;> simp [TunnellHurwitz.pure]
def agrees (u : H ℤ) (k : Fin 3) (s : Fin 4) : Prop := ∀ i : Fin 3, rot4 u (basis i) = (4:ℤ) • move k s (basis i)
instance (u k s) : Decidable (agrees u k s) := by unfold agrees; infer_instance
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma rotations_table : (∀ u ∈ integralUnits, ∃ (k:Fin 3) (s:Fin 4), agrees u k s) ∧
    (∀ (k:Fin 3) (s:Fin 4), ∃ u ∈ integralUnits, agrees u k s) := by
  decide
lemma agrees_all {u k s} (h : agrees u k s) (v : Triple) : act (hamZ u) v = pure (move k s v) := by
  have hi (i : Fin 3) : act (hamZ u) (basis i)=pure (move k s (basis i)) := by
    have he := congrArg TunnellHurwitz.pure (h i)
    rw [rot4_eq,pure_four] at he
    exact (smul_right_injective Q (by norm_num : (4:ℚ)≠0)) he
  rw [act_lin,move_lin,hi 0,hi 1,hi 2]
lemma mem_units (u : H ℤ) : u∈integralUnits ↔ nr u=1 := by
  exact ⟨fun h => (mem_filter.mp h).2,fun h => mem_filter.mpr ⟨norm_one_mem u h,h⟩⟩
lemma norm_ham (u : H ℤ) : Quaternion.normSq (hamZ u)=((nr u:ℤ):ℚ) := by simp [hamZ,ham_norm,nr]
lemma conjugate_iff (v w : Triple) :
    (∃ q∈order, Quaternion.normSq q=1 ∧ act q v=pure w) ↔ ∃ k s, move k s v=w := by
  constructor
  · rintro ⟨_,⟨u,rfl⟩,hn,hq⟩
    rw [norm_ham] at hn
    obtain ⟨k,s,h⟩ := rotations_table.1 u ((mem_units u).mpr (by exact_mod_cast hn))
    exact ⟨k,s,pure_injective ((agrees_all h v).symm.trans hq)⟩
  · rintro ⟨k,s,rfl⟩
    obtain ⟨u,hu,h⟩ := rotations_table.2 k s
    exact ⟨hamZ u,⟨u,rfl⟩,by rw [norm_ham,(mem_units u).mp hu]; simp,agrees_all h v⟩
end TunnellToric
end


/- TunnellToricPeriod -/
section
namespace TunnellToric
open TunnellShell TunnellHurwitz Finset
open scoped Classical
def isRep (v : Triple) : Prop := Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2 ∧ 0<v.1 ∧ 0<v.2.1
noncomputable def representatives (n : ℕ) : Finset Triple := (shell n).filter isRep
def test (v : Triple) : ℤ := if v.2.2%8=0 then 1 else if v.2.2%8=4 then -1 else 0
lemma parity_type {n : ℕ} (hn : n%4=2) {v : Triple} (hv : v∈shell n) :
    (Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2) ∨ (Odd v.2.1 ∧ Odd v.2.2 ∧ Even v.1) ∨
    (Odd v.2.2 ∧ Odd v.1 ∧ Even v.2.1) := by
  have small : ∀ a b c : ZMod 4, a^2+b^2+c^2=2 →
      (a.val%2=1 ∧ b.val%2=1 ∧ c.val%2=0) ∨ (b.val%2=1 ∧ c.val%2=1 ∧ a.val%2=0) ∨
        (c.val%2=1 ∧ a.val%2=1 ∧ b.val%2=0) := by decide
  have hn' : (n:ZMod 4)=2 := by apply ZMod.val_injective 4; rw [ZMod.val_natCast,hn]; decide
  have he := congrArg (fun t:ℤ => (t:ZMod 4)) (mem_shell.mp hv)
  simp only [normSq,Int.cast_add,Int.cast_pow,Int.cast_natCast,hn'] at he
  have hh := small _ _ _ he
  have ha := ZMod.val_intCast (n:=4) v.1
  have hb := ZMod.val_intCast (n:=4) v.2.1
  have hc := ZMod.val_intCast (n:=4) v.2.2
  simp only [Int.odd_iff,Int.even_iff]
  omega
lemma sign_section {v : Triple} (h : Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2) : ∃ s, isRep (signs s v) := by
  obtain ⟨a,b,c⟩ := v
  change Odd a ∧ Odd b ∧ Even c at h
  have ha := Int.odd_iff.mp h.1
  have hb := Int.odd_iff.mp h.2.1
  by_cases hA : 0<a <;> by_cases hB : 0<b
  · exact ⟨0,by simpa [isRep,signs] using And.intro h.1 ⟨h.2.1,h.2.2,hA,hB⟩⟩
  · exact ⟨1,by simp [isRep,signs,h.1,h.2.1,h.2.2,hA]; omega⟩
  · exact ⟨2,by simp [isRep,signs,h.1,h.2.1,h.2.2,hB]; omega⟩
  · exact ⟨3,by simp [isRep,signs,h.1,h.2.1,h.2.2]; omega⟩
lemma exists_rep {n : ℕ} (hn : n%4=2) {v : Triple} (hv : v∈shell n) :
    ∃ k s, isRep (move k s v) := by
  rcases parity_type hn hv with h|h|h
  · exact ⟨0,sign_section h⟩
  · exact ⟨1,sign_section h⟩
  · exact ⟨2,sign_section h⟩
lemma represents_once {v : Triple} (hv : isRep v) (k : Fin 3) (s : Fin 4) :
    isRep (move k s v) ↔ k=0 ∧ s=0 := by
  rcases v with ⟨a,b,c⟩
  obtain ⟨ha,hb,hc,hp,hq⟩ := hv
  dsimp only at ha hb hc hp hq
  have hca : ¬Odd c := Int.not_odd_iff_even.mpr hc
  fin_cases k <;> fin_cases s <;> simp [isRep,move,cyc,signs,rot,ha,hb,hc,hp,hq,hca] <;> omega
lemma move_shell (k : Fin 3) (s : Fin 4) {n : ℕ} {v : Triple} (hv : v∈shell n) : move k s v∈shell n := by
  rw [mem_shell] at hv ⊢
  obtain ⟨a,b,c⟩ := v
  fin_cases k <;> fin_cases s <;> simp [normSq,move,cyc,signs,rot] at * <;> linarith
lemma rep_unique {n : ℕ} {v w : Triple} (hv : v∈representatives n) (hw : w∈representatives n)
    (he : ∃ q∈order, Quaternion.normSq q=1 ∧ act q v=pure w) : v=w := by
  obtain ⟨k,s,h⟩ := (conjugate_iff v w).mp he
  have hm : isRep (move k s v) := h ▸ (mem_filter.mp hw).2
  obtain ⟨rfl,rfl⟩ := (represents_once (mem_filter.mp hv).2 k s).mp hm
  exact h
lemma rep_exists {n : ℕ} (hn : n%4=2) {v : Triple} (hv : v∈shell n) :
    ∃ w∈representatives n, ∃ q∈order, Quaternion.normSq q=1 ∧ act q v=pure w := by
  obtain ⟨k,s,he⟩ := exists_rep hn hv
  exact ⟨move k s v,mem_filter.mpr ⟨move_shell k s hv,he⟩,
    (conjugate_iff v _).mpr ⟨k,s,rfl⟩⟩
noncomputable def oddSlice (n : ℕ) : Finset Triple := (shell n).filter (fun v => Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2)
lemma coord_at {v : Triple} (h : Odd v.1 ∧ Odd v.2.1) : coordWeight v=test v := by
  rw [TunnellTestVector.coordinate]
  simp only [TunnellTestVector.positive,TunnellTestVector.negative,h.1,h.2,true_and,test]
  split_ifs <;> omega
lemma weighted_section (n : ℕ) :
    (∑ v ∈ shell n,coordWeight v)=4*∑ w∈representatives n, test w := by
  have h : (∑ v∈shell n, coordWeight v) = ∑ v∈oddSlice n,coordWeight v := by
    rw [oddSlice,sum_filter]
    apply sum_congr rfl
    intro v _
    split_ifs with h
    · rfl
    · apply if_neg
      intro hv
      obtain ⟨hx,hy,hz⟩ := hv
      exact h ⟨hx,hy,Int.even_iff.mpr (by omega)⟩
  rw [h]
  let K := (univ : Finset (Fin 4)) ×ˢ representatives n
  have he : (∑ t∈K,coordWeight (signs t.1 t.2)) = ∑ v∈oddSlice n,coordWeight v := by
    apply sum_nbij (fun t : Fin 4 × Triple => signs t.1 t.2)
    · rintro ⟨s,w⟩ ht
      obtain ⟨hn,hw⟩ := mem_filter.mp (mem_product.mp ht).2
      obtain ⟨hx,hy,hz,_,_⟩ := hw
      exact mem_filter.mpr ⟨move_shell 0 s hn,by fin_cases s <;> simp [signs,hx,hy,hz]⟩
    · rintro ⟨s,⟨x,y,z⟩⟩ ht ⟨s',⟨x',y',z'⟩⟩ ht' hh
      obtain ⟨_,_,_,hx,hy⟩ := (mem_filter.mp (mem_product.mp ht).2).2
      obtain ⟨_,_,_,hx',hy'⟩ := (mem_filter.mp (mem_product.mp ht').2).2
      dsimp only at hx hy hx' hy'
      fin_cases s <;> fin_cases s' <;> simp [signs,Prod.ext_iff] at hh ⊢ <;> omega
    · intro v hv
      obtain ⟨hn,h⟩ := mem_filter.mp hv
      obtain ⟨s,hs⟩ := sign_section h
      refine ⟨(s,signs s v),mem_product.mpr ⟨mem_univ _,mem_filter.mpr ⟨move_shell 0 s hn,hs⟩⟩,?_⟩
      fin_cases s <;> simp [signs]
    · exact fun _ _ => rfl
  rw [←he]
  have summand (s : Fin 4) {w : Triple} (hw : w∈representatives n) :
      coordWeight (signs s w)=test w := by
    obtain ⟨hx,hy,_,_,_⟩ := (mem_filter.mp hw).2
    rw [coord_at (by fin_cases s <;> simp [signs,hx,hy])]
    fin_cases s <;> simp [test,signs] <;> split_ifs <;> omega
  change (∑ t∈(univ : Finset (Fin 4)) ×ˢ representatives n,_) = _
  rw [sum_product]
  have ha (s : Fin 4) : (∑ w ∈ representatives n,coordWeight (signs s w))=∑ w∈representatives n,test w :=
    sum_congr rfl (fun _ hw => summand s hw)
  simp [ha]
theorem signed_embedding_sum (d : ℕ) : ∑ w ∈ representatives (2*d),test w=TunnellShell.b d := by
  have he := sum_weight_eq_twelve d
  rw [sum_weight,weighted_section] at he
  linarith
end TunnellToric
end


/- TunnellToricIdealClass -/
section
namespace TunnellToricClass
open TunnellShell TunnellHurwitz TunnellToricLocal
open scoped Pointwise
abbrev Lattice := Submodule ℤ Q
abbrev O : Lattice := order.toAddSubgroup.toIntSubmodule
abbrev J (v w : Triple) : Lattice := (intertwiner v w).toIntSubmodule
abbrev line (a : Q) : Lattice := Submodule.span ℤ {a}
def C (v : Triple) : Lattice := LinearMap.ker ((AddMonoidHom.mulLeft (TunnellHurwitz.pure v)).toIntLinearMap - (AddMonoidHom.mulRight (TunnellHurwitz.pure v)).toIntLinearMap)
lemma mem_C {v : Triple} {a : Q} : a∈C v ↔ TunnellHurwitz.pure v*a=a*TunnellHurwitz.pure v := sub_eq_zero
lemma mem_J {v w : Triple} {a : Q} : a∈J v w ↔ a∈O ∧ TunnellHurwitz.pure w*a=a*TunnellHurwitz.pure v := Iff.rfl
lemma order_commutant (v : Triple) : O ⊓ C v = J v v := by ext x; rw [Submodule.mem_inf,mem_C,mem_J]
lemma one_O : (1:Q)∈O := order.one_mem
lemma one_J (v : Triple) : (1:Q)∈J v v := ⟨one_O,by simp⟩
lemma mul_O : O*O=O := by
  apply le_antisymm (Submodule.mul_le.mpr fun _ ha _ hb => order.mul_mem ha hb)
  intro a ha; simpa using Submodule.mul_mem_mul ha one_O
lemma mul_C (v : Triple) : C v * C v ≤ C v := by
  apply Submodule.mul_le.mpr
  intro a ha b hb
  apply mem_C.mpr
  rw [←mul_assoc,mem_C.mp ha,mul_assoc,mem_C.mp hb,mul_assoc]
lemma central_comm {n : ℕ} (hn : Squarefree n) {v : Triple} (hv : v∈shell n) {a b : Q} (ha : a∈C v) (hb : b∈C v) : a*b=b*a := by
  obtain ⟨r,er⟩ := centralizer hn hv a (mem_C.mp ha).symm
  obtain ⟨s,es⟩ := centralizer hn hv b (mem_C.mp hb).symm
  conv_lhs => rw [er,es]
  conv_rhs => rw [es,er]
  apply QuaternionAlgebra.ext
  all_goals first | rw [Quaternion.re_mul,Quaternion.re_mul] | rw [Quaternion.imI_mul,Quaternion.imI_mul] | rw [Quaternion.imJ_mul,Quaternion.imJ_mul] | rw [Quaternion.imK_mul,Quaternion.imK_mul]
  all_goals dsimp only [evalRat]; ring
lemma ideals_comm {n : ℕ} (hn : Squarefree n) {v : Triple} (hv : v∈shell n) {A B : Lattice} (ha : A≤C v) (hb : B≤C v) : A*B=B*A := by
  apply le_antisymm <;> apply Submodule.mul_le.mpr
  · intro a h₁ b h₂; rw [central_comm hn hv (ha h₁) (hb h₂)]; exact Submodule.mul_mem_mul h₂ h₁
  · intro a h₁ b h₂; rw [central_comm hn hv (hb h₁) (ha h₂)]; exact Submodule.mul_mem_mul h₂ h₁
lemma J_comp {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {u v w : Triple} (hu : u∈shell n) (hv : v∈shell n) : J v w * J u v = J u w := by
  refine Eq.trans ?_ (compose_ideals hn h2 u v w hu hv)
  apply le_antisymm (Submodule.mul_le.mpr fun _ ha _ hb => idealProd_mem ha hb)
  apply Submodule.span_le.mpr
  rintro _ ⟨a,ha,b,hb,rfl⟩
  exact Submodule.mul_mem_mul ha hb
lemma J_extends {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {u v : Triple} (hu : u∈shell n) (hv : v∈shell n) : J u v*O=O := by
  have h₁ : 1 ≤ J u v*J v u := by rw [J_comp hn h2 hv hu]; exact Submodule.one_le.mpr (one_J v)
  have h₂ : 1 ≤ J u v*O := h₁.trans (mul_le_mul_right (show J v u ≤ O from fun _ h => h.1) _)
  apply le_antisymm
  · exact (mul_le_mul_left (show J u v ≤ O from fun _ h => h.1) _).trans mul_O.le
  · calc O = 1*O := (one_mul _).symm
         _ ≤ (J u v*O)*O := mul_le_mul_left h₂ _
         _ = _ := by rw [mul_assoc,mul_O]
 
lemma contract {v : Triple} {A B : Lattice} (hA : A≤C v) (hB : B≤C v)
    (hAB : A*B=J v v) (hBA : B*A=J v v) (hR : A*J v v=A) : A*O ⊓ C v=A := by
  let D := A*O ⊓ C v
  have hBD : B*D ≤ J v v := by
    rw [←order_commutant]
    apply le_inf
    · calc B*D ≤ B*(A*O) := mul_le_mul_right inf_le_left _
           _ = J v v*O := by rw [←mul_assoc,hBA]
           _ ≤ O*O := mul_le_mul_left (show J v v ≤ O from fun _ h => h.1) _
           _ = O := mul_O
    · exact (mul_le_mul' hB (show D≤C v from inf_le_right)).trans (mul_C v)
  apply le_antisymm
  · calc D = 1*D := (one_mul _).symm
         _ ≤ J v v*D := mul_le_mul_left (Submodule.one_le.mpr (one_J v)) _
         _ = A*(B*D) := by rw [←mul_assoc,hAB]
         _ ≤ A*J v v := mul_le_mul_right hBD _
         _ = A := hR
  · apply le_inf _ hA
    intro a ha; simpa using Submodule.mul_mem_mul ha one_O
lemma principal_extension {A : Lattice} (ha : A≤O) (hne : A≠⊥) :
    ∃ a∈A*O, a≠0 ∧ A*O=line a*O := by
  let D := A*O
  have hm : D*O=D := by change (A*O)*O=A*O; rw [mul_assoc,mul_O]
  have hi : D≤O := (mul_le_mul_left ha _).trans mul_O.le
  obtain ⟨b,hb,hb0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨a,h₁,h₂,h₃⟩ := integral_class_number_one (D:Set Q) hi
    (fun x hx y hy => D.sub_mem hx hy)
    (fun x hx y hy => hm ▸ Submodule.mul_mem_mul hx (show y∈O from hy))
    ⟨b,by simpa using Submodule.mul_mem_mul hb one_O,hb0⟩
  refine ⟨a,h₁,h₂,?_⟩
  ext x
  change x∈(D:Set Q) ↔ _
  rw [h₃,Submodule.mem_span_singleton_mul]
  constructor <;> rintro ⟨z,hz,h⟩ <;> exact ⟨z,hz,h.symm⟩
lemma J_right {u v : Triple} {a : Q} (ha : a≠0) (he : TunnellHurwitz.pure v*a=a*TunnellHurwitz.pure u) :
    line a*O ⊓ C v = line a*J v u := by
  ext x
  simp only [Submodule.mem_inf,Submodule.mem_span_singleton_mul,mem_C]
  constructor
  · rintro ⟨⟨y,hy,rfl⟩,hh⟩
    refine ⟨y,⟨hy,mul_left_cancel₀ ha ?_⟩,rfl⟩
    rw [←mul_assoc,←he,mul_assoc,hh,mul_assoc]
  · rintro ⟨y,hy,rfl⟩
    refine ⟨⟨y,hy.1,rfl⟩,?_⟩
    rw [←mul_assoc,he,mul_assoc,hy.2,mul_assoc]
 

lemma classify_ideal {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v : Triple} (hv : v∈shell n)
    {A B : Lattice} (ha : A≤O) (hA : A≤C v) (hB : B≤C v) (hAB : A*B=J v v) (hR : A*J v v=A) :
    ∃ w∈shell n, ∃ a∈J w v, a≠0 ∧ A=line a*J v w := by
  have hBA := (ideals_comm hs hv hB hA).trans hAB
  have hh := contract hA hB hAB hBA hR
  have hne : A≠⊥ := by
    rintro rfl; rw [Submodule.bot_mul] at hAB
    have h₁ := one_J v; rw [←hAB] at h₁; exact one_ne_zero h₁
  obtain ⟨a,haD,ha0,he⟩ := principal_extension ha hne
  have hO : a∈O := (mul_le_mul_left ha _).trans mul_O.le haD
  have hco : J v v ≤ C v := fun _ h => mem_C.mpr h.2
  have hra : J v v*A=A := (ideals_comm hs hv hco hA).trans hR
  have hp : TunnellHurwitz.pure v∈J v v := ⟨pure_mem _,rfl⟩
  have hm := Submodule.mul_mem_mul hp haD
  rw [←mul_assoc,hra,he,Submodule.mem_span_singleton_mul] at hm
  obtain ⟨t,ht,heq⟩ := hm
  have ht2 : t*t= -(n:Q) := by
    apply mul_left_cancel₀ ha0
    calc a*(t*t)=(TunnellHurwitz.pure v*TunnellHurwitz.pure v)*a := by rw [←mul_assoc,heq,mul_assoc,heq,←mul_assoc]
         _=a* -(n:Q) := by rw [pure_square hv,neg_mul,mul_neg,Nat.cast_comm]
  obtain ⟨hr,hN⟩ := negative_root (show 0<n by omega) t ht2
  obtain ⟨w,rfl⟩ := trace_zero_integral ht hr
  have hw : w∈shell n := by rw [mem_shell]; rw [pure_norm] at hN; exact_mod_cast hN
  exact ⟨w,hw,a,⟨hO,heq.symm⟩,ha0,by rw [←hh,he,J_right ha0 heq.symm]⟩
lemma line_mul (a b : Q) : line a * line b = line (a*b) := by rw [line,line,Submodule.span_mul_span,Set.singleton_mul_singleton]
lemma line_one : line 1=1 := (Submodule.one_eq_span).symm
lemma two_sided_inverse {a : Q} (ha : a≠0) : line a⁻¹*line a=1 := by rw [line_mul,inv_mul_cancel₀ ha,line_one]
 
def isIdeal (v : Triple) (A : Lattice) : Prop :=
  A≤O ∧ A≤C v ∧ A*J v v=A ∧ ∃ B≤C v, A*B=J v v
lemma from_embedding {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v w : Triple}
    (hv : v∈shell n) (hw : w∈shell n) {a : Q} (ha : a∈J w v) (ha0 : a≠0) :
    isIdeal v (line a*J v w) := by
  let A := line a*J v w
  let B := J w v*line a⁻¹
  have hi : A ≤ O := by
    intro z hz; obtain ⟨q,hq,rfl⟩ := Submodule.mem_span_singleton_mul.mp hz
    exact order.mul_mem ha.1 hq.1
  have hA : A≤C v := by change line a*J v w≤_; rw [←J_right ha0 ha.2]; exact inf_le_right
  have hB : B≤C v := by
    intro z hz; obtain ⟨q,hq,rfl⟩ := Submodule.mem_mul_span_singleton.mp hz
    apply mem_C.mpr
    apply mul_right_cancel₀ ha0
    calc (TunnellHurwitz.pure v * (q*a⁻¹))*a = TunnellHurwitz.pure v*q := by simp [mul_assoc,ha0]
         _=q*TunnellHurwitz.pure w := hq.2
         _=(q*a⁻¹*TunnellHurwitz.pure v)*a := by rw [mul_assoc,ha.2]; simp [mul_assoc,ha0]
  have hBA : B*A=J v v := by
    change (J w v*line a⁻¹)*(line a*J v w)=_
    rw [mul_assoc,←mul_assoc (line a⁻¹),two_sided_inverse ha0,one_mul,J_comp hs hn hv hw]
  refine ⟨hi,hA,?_,B,hB,(ideals_comm hs hv hA hB).trans hBA⟩
  rw [mul_assoc,J_comp hs hn hv hv]
end TunnellToricClass
end


/- TunnellIdealTorsor -/
section
namespace TunnellToricClass
open TunnellShell TunnellHurwitz TunnellToricLocal TunnellToric
open scoped Pointwise
lemma line_O {q : Q} (hq : q∈O) (hq' : q⁻¹∈O) (h0 : q≠0) : line q*O=O := by
  apply le_antisymm
  · intro z hz; obtain ⟨x,hx,rfl⟩ := Submodule.mem_span_singleton_mul.mp hz
    exact order.mul_mem hq hx
  · intro x hx; exact Submodule.mem_span_singleton_mul.mpr ⟨q⁻¹*x,order.mul_mem hq' hx,by simp [h0]⟩
lemma line_O_equal {a b : Q} (_ha : a≠0) (hb : b≠0) (h : line a*O=line b*O) :
    ∃ q∈O, Quaternion.normSq q=1 ∧ a=b*q := by
  have owned (t : Q) : t∈line t*O := Submodule.mem_span_singleton_mul.mpr ⟨1,one_O,mul_one _⟩
  obtain ⟨q,hq,e₁⟩ := Submodule.mem_span_singleton_mul.mp (h ▸ owned a)
  obtain ⟨r,hr,e₂⟩ := Submodule.mem_span_singleton_mul.mp (h.symm ▸ owned b)
  have e : q*r=1 := mul_left_cancel₀ hb (by rw [←mul_assoc,e₁,e₂,mul_one])
  obtain ⟨N,hN⟩ := norm_int hq
  obtain ⟨M,hM⟩ := norm_int hr
  have hn := congrArg Quaternion.normSq e
  rw [map_mul,map_one,hN,hM] at hn
  have hnm : N*M=1 := by exact_mod_cast hn
  rw [Nat.eq_one_of_dvd_one (show N∣1 from ⟨M,hnm.symm⟩)] at hN
  exact ⟨q,hq,by simpa using hN,e₁.symm⟩
lemma inv_eq_star_of_unit {q : Q} (hq : Quaternion.normSq q=1) : q⁻¹=star q := by
  have hq0 : q≠0 := by intro h; simp [h] at hq
  apply mul_right_cancel₀ hq0
  rw [inv_mul_cancel₀ hq0,Quaternion.star_mul_self,hq,Quaternion.coe_one]
lemma unit_frame {n : ℕ} (hn : n%4=2) {v w : Triple} (hw : w∈shell n)
    {a : Q} (ha : a∈J w v) (h0 : a≠0) :
    ∃ z∈representatives n, ∃ b∈J z v, b≠0 ∧ line a*J v w=line b*J v z := by
  obtain ⟨z,hz,q,hq,hN,hact⟩ := rep_exists hn hw
  have hq0 : q≠0 := by intro h; simp [h] at hN
  have hi : q⁻¹∈O := inv_eq_star_of_unit hN ▸ star_order hq
  have he' : (TunnellHurwitz.pure) z=q*(TunnellHurwitz.pure) w*q⁻¹ := hact.symm.trans (by rw [inv_eq_star_of_unit hN]; rfl)
  have he : (TunnellHurwitz.pure) v*(a*q⁻¹)=(a*q⁻¹)*(TunnellHurwitz.pure) z := by
    rw [←mul_assoc,ha.2,he']; simp [mul_assoc,hq0]
  have hqO : line q⁻¹*O=O := line_O hi (by rw [inv_inv]; exact hq) (inv_ne_zero hq0)
  have heO : line (a*q⁻¹)*O=line a*O := by rw [←line_mul,mul_assoc,hqO]
  refine ⟨z,hz,a*q⁻¹,⟨order.mul_mem ha.1 hi,he⟩,mul_ne_zero h0 (inv_ne_zero hq0),?_⟩
  rw [←J_right h0 ha.2,←J_right (mul_ne_zero h0 (inv_ne_zero hq0)) he,heO]
lemma classify_rep {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v : Triple} (hv : v∈shell n)
    {A : Lattice} (h : isIdeal v A) :
    ∃ w∈representatives n, ∃ a∈J w v, a≠0 ∧ A=line a*J v w := by
  obtain ⟨ho,hA,hR,B,hB,hAB⟩ := h
  obtain ⟨w,hw,a,ha,h₀,e⟩ := classify_ideal hs hn hv ho hA hB hAB hR
  obtain ⟨z,hz,b,hb,hb0,hh⟩ := unit_frame hn hw ha h₀
  exact ⟨z,hz,b,hb,hb0,e.trans hh⟩
def homothetic (v : Triple) (A B : Lattice) : Prop := ∃ c∈C v, c≠0 ∧ line c*A=B
lemma frame_unique {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v w z : Triple} (hv : v∈shell n)
    (hw : w∈representatives n) (hz : z∈representatives n) {a b : Q} (ha : a∈J w v) (hb : b∈J z v)
    (ha0 : a≠0) (hb0 : b≠0) :
    homothetic v (line a*J v w) (line b*J v z) ↔ w=z := by
  classical
  constructor
  · rintro ⟨c,hc,hc0,he⟩
    have e := congrArg (fun I:Lattice => I*O) he
    change (line c*(line a*J v w))*O=(line b*J v z)*O at e
    rw [←mul_assoc (line c), line_mul] at e
    rw [mul_assoc,J_extends hs hn hv (Finset.mem_filter.mp hw).1,mul_assoc,J_extends hs hn hv (Finset.mem_filter.mp hz).1] at e
    obtain ⟨q,hq,hnq,e'⟩ := line_O_equal (mul_ne_zero hc0 ha0) hb0 e
    have hq0 : q≠0 := by intro h; simp [h] at hnq
    have ht : q*(TunnellHurwitz.pure) w=(TunnellHurwitz.pure) z*q := by
      apply mul_left_cancel₀ hb0
      calc b*(q*(TunnellHurwitz.pure) w)=(c*a)*(TunnellHurwitz.pure) w := by rw [←mul_assoc,←e']
           _=(TunnellHurwitz.pure) v*(c*a) := by rw [←mul_assoc ((TunnellHurwitz.pure) v),mem_C.mp hc,mul_assoc c ((TunnellHurwitz.pure) v),ha.2,mul_assoc]
           _=b*((TunnellHurwitz.pure) z*q) := by rw [e',←mul_assoc,hb.2,mul_assoc]
    apply rep_unique hw hz
    refine ⟨q,hq,hnq,?_⟩
    change q*(TunnellHurwitz.pure) w*star q=(TunnellHurwitz.pure) z
    rw [ht,←inv_eq_star_of_unit hnq,mul_assoc,mul_inv_cancel₀ hq0,mul_one]
  · rintro rfl
    refine ⟨b*a⁻¹,mem_C.mpr ?_,mul_ne_zero hb0 (inv_ne_zero ha0),?_⟩
    · apply mul_right_cancel₀ ha0
      calc ((TunnellHurwitz.pure) v*(b*a⁻¹))*a=(TunnellHurwitz.pure) v*b := by simp [mul_assoc,ha0]
           _=b*(TunnellHurwitz.pure) w := hb.2
           _=(b*a⁻¹*(TunnellHurwitz.pure) v)*a := by rw [mul_assoc,ha.2]; simp [mul_assoc,ha0]
    · rw [←mul_assoc,line_mul,mul_assoc,inv_mul_cancel₀ ha0,mul_one]
abbrev IntegralIdeal (v : Triple) := {A : Lattice // isIdeal v A}
def idealSetoid (v : Triple) : Setoid (IntegralIdeal v) where
  r A B := homothetic v A.val B.val
  iseqv := {
    refl := fun _ => ⟨1,mem_C.mpr (by simp),one_ne_zero,by rw [line_one,one_mul]⟩
    symm := by
      rintro A B ⟨c,hc,h₀,he⟩
      refine ⟨c⁻¹,mem_C.mpr ((show Commute ((TunnellHurwitz.pure) v) c from mem_C.mp hc).inv_right₀),inv_ne_zero h₀,?_⟩
      rw [←he,←mul_assoc,two_sided_inverse h₀,one_mul]
    trans := by
      rintro A B D ⟨c,hc,hc₀,he⟩ ⟨d,hd,hd₀,he'⟩
      refine ⟨d*c,(mul_C v) (Submodule.mul_mem_mul hd hc),mul_ne_zero hd₀ hc₀,?_⟩
      rw [←line_mul,mul_assoc,he,he'] }
abbrev ProperIdealClass (v : Triple) := Quotient (idealSetoid v)
noncomputable def representative {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v : Triple}
    (hv : v∈shell n) (A : IntegralIdeal v) : ↥(representatives n) :=
  ⟨(classify_rep hs hn hv A.property).choose,(classify_rep hs hn hv A.property).choose_spec.1⟩
lemma representative_frame {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v : Triple}
    (hv : v∈shell n) (A : IntegralIdeal v) :
    ∃ a∈J (representative hs hn hv A).val v, a≠0 ∧ A.val=line a*J v (representative hs hn hv A).val :=
  (classify_rep hs hn hv A.property).choose_spec.2
lemma class_iff_same_rep {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v : Triple}
    (hv : v∈shell n) (A B : IntegralIdeal v) : homothetic v A B ↔ representative hs hn hv A=representative hs hn hv B := by
  obtain ⟨a,ha,h₀,he⟩ := representative_frame hs hn hv A
  obtain ⟨b,hb,h₁,he'⟩ := representative_frame hs hn hv B
  exact (show homothetic v A B ↔ (representative hs hn hv A).val=(representative hs hn hv B).val by
    conv_lhs => rw [he,he']
    exact frame_unique hs hn hv (representative hs hn hv A).property (representative hs hn hv B).property ha hb h₀ h₁).trans Subtype.ext_iff.symm
 
noncomputable def idealEquiv {n : ℕ} (hs : Squarefree n) (hn : n%4=2) {v : Triple}
    (hv : v∈shell n) : ProperIdealClass v ≃ ↥(representatives n) := by
  classical
  let f : ProperIdealClass v → ↥(representatives n) := Quotient.lift (representative hs hn hv)
    (fun a b h => (class_iff_same_rep hs hn hv a b).mp h)
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b
    induction a using Quotient.inductionOn with | _ A =>
      induction b using Quotient.inductionOn with | _ B =>
        intro h
        exact Quotient.sound ((class_iff_same_rep hs hn hv A B).mpr h)
  · intro w
    have hw := (Finset.mem_filter.mp w.property).1
    obtain ⟨a,ha,ha0,he⟩ := intertwine w.val v hw hv
    have haJ : a∈J w.val v := ⟨ha,he⟩
    let A : IntegralIdeal v := ⟨line a*J v w.val,from_embedding hs hn hv hw haJ ha0⟩
    refine ⟨Quotient.mk (idealSetoid v) A,Subtype.ext ?_⟩
    obtain ⟨b,hb,hb0,he'⟩ := representative_frame hs hn hv A
    apply (frame_unique hs hn hv (representative hs hn hv A).property w.property hb haJ hb0 ha0).mp
    rw [←he']; exact (idealSetoid v).refl A
theorem sum_class_representatives {d : ℕ} {T : Type*} [Fintype T] (e : T ≃ ↥(representatives (2*d))) :
    (∑ c : T, test (e c).val)=TunnellShell.b d := by
  calc (∑ c : T, test (e c).val)=∑ w : ↥(representatives (2*d)),test w.val :=
         e.sum_comp (fun w : ↥(representatives (2*d)) => test w.val)
       _=∑ w ∈ representatives (2*d),test w := Finset.sum_coe_sort _ _
       _=TunnellShell.b d := signed_embedding_sum d
end TunnellToricClass
end


/- TunnellEmbeddedIdeals -/
section
namespace TunnellEmbeddedIdeals
open TunnellIdealHNF TunnellShell TunnellHurwitz TunnellToricClass
def image {n : ℕ} {v : Triple} (hv : v∈shell n) (I : Ideal (TunnellIdealHNF.R n)) : Lattice :=
  I.toAddSubgroup.toIntSubmodule.map ((embed n v hv).toAddMonoidHom.toIntLinearMap)
lemma mem_image {n : ℕ} {v : Triple} (hv : v∈shell n) {I : Ideal (TunnellIdealHNF.R n)} {q : Q} :
    q∈image hv I ↔ ∃ z∈I, embed n v hv z=q := Iff.rfl
lemma embed_inj {n : ℕ} {v : Triple} (hn : Squarefree n) (hv : v∈shell n) : Function.Injective (embed n v hv) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  obtain ⟨x,y,z,he⟩ := primitive hn hv
  have e₁ := congrArg QuaternionAlgebra.re h
  have e₂ := congrArg QuaternionAlgebra.imI h
  have e₃ := congrArg QuaternionAlgebra.imJ h
  have e₄ := congrArg QuaternionAlgebra.imK h
  change (a:ℚ)=c at e₁
  change (b:ℚ)*v.1=d*v.1 at e₂
  change (b:ℚ)*v.2.1=d*v.2.1 at e₃
  change (b:ℚ)*v.2.2=d*v.2.2 at e₄
  apply Zsqrtd.ext (by exact_mod_cast e₁)
  have h' : (v.1:ℚ)*x+v.2.1*y+v.2.2*z=1 := by exact_mod_cast he
  have H : (b:ℚ)=d := by linear_combination x*e₂+y*e₃+z*e₄-(b-d)*h'
  exact_mod_cast H
lemma image_injective {n : ℕ} {v : Triple} (hn : Squarefree n) (hv : v∈shell n) : Function.Injective (image hv) := by
  intro I K he; ext z
  have h (J : Ideal _) : (embed n v hv z)∈image hv J ↔ z∈J := by
    constructor
    · rintro ⟨y,hy,ey⟩; exact embed_inj hn hv ey ▸ hy
    · intro hz; exact ⟨z,hz,rfl⟩
  rw [←h,he,h]
lemma image_order {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n) :
    image hv ⊤=J v v := by
  ext q
  constructor
  · rw [mem_image]; rintro ⟨z,_,rfl⟩
    exact ⟨embed_integral _ _ _ _,by rw [←embed_root n v hv,←map_mul,←map_mul,mul_comm]⟩
  · rintro ⟨hq,he⟩; obtain ⟨z,ez⟩ := integral_centralizer hn h2 hv hq he.symm
    exact ⟨z,Submodule.mem_top,ez.symm⟩
lemma image_mul {n : ℕ} {v : Triple} (hv : v∈shell n) (A B : Ideal (R n)) :
    image hv (A*B)=image hv A*image hv B := by
  apply le_antisymm
  · intro q hq; obtain ⟨z,hz,rfl⟩ := (mem_image _).mp hq
    apply Submodule.mul_induction_on (C := fun a => embed n v hv a ∈ image hv A*image hv B) hz
    · intro a ha b hb
      rw [map_mul]
      exact Submodule.mul_mem_mul ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    · intro a b ha hb
      rw [map_add]; exact add_mem ha hb
  · apply Submodule.mul_le.mpr
    intro x hx y hy
    obtain ⟨a,ha,rfl⟩ := (mem_image _).mp hx
    obtain ⟨b,hb,rfl⟩ := (mem_image _).mp hy
    exact ⟨a*b,Ideal.mul_mem_mul ha hb,map_mul (embed n v hv) a b⟩
lemma image_principal {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n) (a : R n) :
    image hv (Ideal.span {a})=line (embed n v hv a)*J v v := by
  rw [←image_order hn h2 hv]
  ext q
  constructor
  · rintro ⟨z,hz,rfl⟩; obtain ⟨b,rfl⟩ := Ideal.mem_span_singleton.mp hz
    exact Submodule.mem_span_singleton_mul.mpr ⟨_,⟨b,Submodule.mem_top,rfl⟩,(map_mul ..).symm⟩
  · intro h
    obtain ⟨t,ht,rfl⟩ := Submodule.mem_span_singleton_mul.mp h
    obtain ⟨b,_,rfl⟩ := (mem_image _).mp ht
    exact ⟨a*b,Ideal.mem_span_singleton.mpr (dvd_mul_right _ _),map_mul (embed n v hv) a b⟩
lemma center_image {n : ℕ} {v : Triple} (hv : v∈shell n) (I : Ideal (R n)) : image hv I≤C v := by
  intro q hq; obtain ⟨a,_,rfl⟩ := (mem_image _).mp hq; apply mem_C.mpr; rw [←embed_root n v hv,←map_mul,←map_mul,mul_comm]
lemma image_isIdeal {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n) (I : Ideal (R n)) (hI : I≠⊥) :
    isIdeal v (image hv I) := by
  obtain ⟨s,rfl⟩ := normal_form (show 0<n by omega) hI
  let N : Q := idx s
  have hN : N≠0 := by intro h; have H := congrArg QuaternionAlgebra.re h; change ((idx s:ℕ):ℚ)=0 at H; exact (show idx s≠0 from mul_ne_zero (pow_ne_zero _ s.pos_c.ne') s.pos_a.ne') (by exact_mod_cast H)
  have his : ∀ x : Q, x*N=N*x := fun x => (Nat.cast_comm (idx s) x).symm
  have hN' : N⁻¹∈C v := mem_C.mpr (show Commute ((TunnellHurwitz.pure) v) N from his _).inv_right₀
  let K := image hv (conjugate (ideal s))*line N⁻¹
  have hline : line N⁻¹ ≤ C v := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hN')
  have hK : K≤C v := (mul_le_mul' (center_image hv _) hline).trans (mul_C v)
  refine ⟨fun q hq => by obtain ⟨x,_,rfl⟩ := (mem_image _).mp hq; exact embed_integral _ _ _ _,center_image hv _,?_,K,hK,?_⟩
  · rw [←image_order hn h2 hv,←image_mul,Ideal.mul_top]
  · change image hv (ideal s)*(image hv (conjugate (ideal s))*line N⁻¹)=_
    rw [←mul_assoc,←image_mul,times_conj hn h2,image_principal hn h2 hv,map_natCast]
    change line N * J v v * line N⁻¹ = _
    rw [mul_assoc,ideals_comm hn hv (show J v v ≤ C v from fun _ h => mem_C.mpr h.2) hline,
      ←mul_assoc,line_mul,mul_inv_cancel₀ hN,line_one,one_mul]
def preimage {n : ℕ} {v : Triple} (hv : v∈shell n) (A : IntegralIdeal v) : Ideal (R n) where
  carrier := {x | embed n v hv x∈A.val}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy; change embed n v hv (x+y)∈A.val; rw [map_add]; exact A.val.add_mem hx hy
  smul_mem' := by
    intro x y hy
    have hx : embed n v hv x∈J v v := ⟨embed_integral _ _ _ _,by rw [←embed_root n v hv,←map_mul,←map_mul,mul_comm]⟩
    change embed n v hv (x*y)∈A.val
    rw [mul_comm,map_mul,←A.property.2.2.1]
    exact Submodule.mul_mem_mul hy hx
lemma image_preimage {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n) (A : IntegralIdeal v) :
    image hv (preimage hv A)=A.val := by
  ext q; constructor
  · rintro ⟨a,ha,rfl⟩; exact ha
  · intro hq
    obtain ⟨z,he⟩ := integral_centralizer hn h2 hv (A.property.1 hq) (mem_C.mp (A.property.2.1 hq)).symm
    refine (mem_image _).mpr ⟨z,?_,he.symm⟩
    change embed n v hv z∈A.val; rwa [←he]
lemma preimage_ne_bot {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n) (A : IntegralIdeal v) :
    preimage hv A≠⊥ := by
  intro h
  have he := image_preimage hn h2 hv A
  rw [h] at he
  have hbot : image hv ⊥=⊥ := by apply le_antisymm _ bot_le; rintro _ ⟨x,hx,rfl⟩; rw [show x=0 from hx,map_zero]; exact Submodule.zero_mem _
  obtain ⟨B,_,hB⟩ := A.property.2.2.2
  rw [←he,hbot,Submodule.bot_mul] at hB
  have h₁ := one_J v; rw [←hB] at h₁
  exact one_ne_zero h₁
noncomputable def integralEquiv {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n) :
    {I : Ideal (R n) // I≠⊥} ≃ IntegralIdeal v where
  toFun I := ⟨image hv I.val,image_isIdeal hn h2 hv I.val I.property⟩
  invFun A := ⟨preimage hv A,preimage_ne_bot hn h2 hv A⟩
  left_inv I := Subtype.ext (image_injective hn hv (image_preimage hn h2 hv _))
  right_inv A := Subtype.ext (image_preimage hn h2 hv A)
end TunnellEmbeddedIdeals
end


/- TunnellQuadraticIdealNorm -/
section
namespace TunnellIdealHNF
noncomputable def normI {n : ℕ} (I : Ideal (R n)) := Nat.card (R n ⧸ I)
def principal {n : ℕ} (x : R n) := Ideal.span {x}
lemma normI_positive {n : ℕ} (hn : 0<n) (I : Ideal (R n)) (hI : I≠⊥) : 0<normI I := by
  obtain ⟨s,rfl⟩ := normal_form hn hI
  rw [normI,quotient_card]; exact mul_pos (pow_pos s.pos_c _) s.pos_a
lemma int_pos_mem {n : ℕ} (hn : 0<n) (I : Ideal (R n)) (hI : I≠⊥) : ∃ A : ℕ, 0<A ∧ (A:R n)∈I := by
  obtain ⟨s,rfl⟩ := normal_form hn hI
  exact ⟨s.c*s.a,mul_pos s.pos_c s.pos_a,by
    have he : ((s.c*s.a:ℕ):R n)=⟨(s.c:ℤ)*s.a,0⟩ := by
      change (⟨((s.c*s.a:ℕ):ℤ),0⟩ : R n)=_; rw [Nat.cast_mul]
    rw [he]; exact real_basis s⟩
lemma mul_ne_bot {n : ℕ} (hn : 0<n) {I J : Ideal (R n)} (hI : I≠⊥) (hJ : J≠⊥) : I*J≠⊥ := by
  obtain ⟨a,ha,hi⟩ := int_pos_mem hn I hI; obtain ⟨b,hb,hj⟩ := int_pos_mem hn J hJ
  intro h; have hh := Ideal.mul_mem_mul hi hj; rw [h,←Nat.cast_mul] at hh
  exact Nat.cast_ne_zero.mpr (mul_ne_zero ha.ne' hb.ne') (show ((a*b:ℕ):R n)=0 from hh)
lemma conj_mem {n : ℕ} (I : Ideal (R n)) {x : R n} (h : x∈I) : star x∈conjugate I := by simpa [mem_conjugate] using h
lemma conjugate_mul {n : ℕ} (I J : Ideal (R n)) : conjugate (I*J)=conjugate I*conjugate J := by
  apply le_antisymm
  · intro x hx
    change star x∈I*J at hx
    have h (y : R n) (hy : y∈I*J) : star y∈conjugate I*conjugate J := by
      apply Submodule.mul_induction_on (C := fun y => star y∈conjugate I*conjugate J) hy
      · intro a ha b hb; rw [star_mul']; exact Ideal.mul_mem_mul (conj_mem _ ha) (conj_mem _ hb)
      · intro a b ha hb; rw [star_add]; exact add_mem ha hb
    simpa using h (star x) hx
  · apply Ideal.mul_le.mpr
    intro a ha b hb; change star (a*b)∈I*J
    rw [star_mul']; exact Ideal.mul_mem_mul ha hb
lemma norm_conjugate {n : ℕ} (hn : Squarefree n) (h₂ : n%4=2) (I : Ideal (R n)) (hI : I≠⊥) :
    I*conjugate I=principal (normI I:R n) := by
  obtain ⟨s,rfl⟩ := normal_form (show 0<n by omega) hI
  rw [normI,quotient_card]; exact times_conj hn h₂ s
lemma principal_injective_nat {n a b : ℕ} (h : principal (a:R n)=principal b) : a=b := by
  have mono {x y : ℕ} (h : principal (x:R n) ≤ principal y) : y∣x := by
    obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp (h (Ideal.mem_span_singleton_self _))
    have he := congrArg Zsqrtd.re hz
    change (x:ℤ)=y*z.re+ -(n:ℤ)*0*z.im at he
    exact Int.natCast_dvd_natCast.mp ⟨z.re,by simpa using he⟩
  exact Nat.dvd_antisymm (mono h.ge) (mono h.le)
lemma principal_mul {n : ℕ} (x y : R n) : principal (x*y)=principal x*principal y := (Ideal.span_singleton_mul_span_singleton x y).symm
lemma normI_mul {n : ℕ} (hn : Squarefree n) (h₂ : n%4=2) {I J : Ideal (R n)} (hI : I≠⊥) (hJ : J≠⊥) :
    normI (I*J)=normI I*normI J := by
  apply principal_injective_nat (n:=n)
  rw [←norm_conjugate hn h₂ _ (mul_ne_bot (by omega) hI hJ),Nat.cast_mul,principal_mul,←norm_conjugate hn h₂ _ hI,
    ←norm_conjugate hn h₂ _ hJ,conjugate_mul]; ac_rfl
lemma principal_star {n : ℕ} (x : R n) : conjugate (principal x)=principal (star x) := by
  ext y
  change star y∈Ideal.span {x} ↔ _
  change star y∈Ideal.span {x} ↔ y∈Ideal.span {star x}
  rw [Ideal.mem_span_singleton,Ideal.mem_span_singleton]
  constructor
  · rintro ⟨z,he⟩; exact ⟨star z,by rw [←star_mul',←he,star_star]⟩
  · rintro ⟨z,rfl⟩; exact ⟨star z,by rw [star_mul',star_star]⟩
lemma positive_norm {n : ℕ} (hn : 0<n) {z : R n} (hz : z≠0) : 0<z.norm := by
  change 0<z.re*z.re- -(n:ℤ)*z.im*z.im
  by_cases h : z.im=0
  · have he : z.re≠0 := fun he => hz (Zsqrtd.ext he h)
    rw [h]; simpa using mul_self_pos.mpr he
  · nlinarith [mul_self_nonneg z.re,mul_pos (show 0<(n:ℤ) by exact_mod_cast hn) (mul_self_pos.mpr h)]
lemma normI_principal {n : ℕ} (hn : Squarefree n) (h₂ : n%4=2) {x : R n} (hx : x≠0) :
    normI (principal x)=x.norm.toNat := by
  have hI : principal x≠⊥ := fun h => hx (by have H : x∈principal x := Ideal.mem_span_singleton_self x; rwa [h] at H)
  apply principal_injective_nat (n:=n)
  rw [←norm_conjugate hn h₂ _ hI,principal_star,←principal_mul,←Zsqrtd.norm_eq_mul_conj]
  congr 1
  rw [←Int.cast_natCast (R:=R n),Int.toNat_of_nonneg (positive_norm (by omega) hx).le]
end TunnellIdealHNF
end


/- TunnellIdealDivisorCount -/
section
namespace TunnellIdealHNF
open Finset
def roots (n a : ℕ) : Finset ℕ := (range a).filter (fun b => (a:ℤ)∣(b:ℤ)^2+n)
noncomputable def divisors (m : ℕ) : Finset ℕ := m.divisors.filter (fun a => IsSquare (m/a))
abbrev indexed (n m : ℕ) := {s : Data n // s.c^2*s.a=m}
abbrev finiteRoot (n m : ℕ) := ↥((divisors m).sigma (roots n))
lemma quotient_by_a {n m : ℕ} (s : indexed n m) : m/s.val.a=s.val.c^2 := by
  exact (congrArg (·/s.val.a) s.property.symm).trans (Nat.mul_div_cancel _ s.val.pos_a)
noncomputable def divisorEquiv {n m : ℕ} (hm : 0 < m) : indexed n m ≃ finiteRoot n m := by
  classical
  let f : indexed n m → finiteRoot n m := fun s => ⟨⟨s.val.a,s.val.b⟩,mem_sigma.mpr ⟨mem_filter.mpr
    ⟨Nat.mem_divisors.mpr ⟨⟨s.val.c^2,s.property.symm.trans (mul_comm _ _)⟩,hm.ne'⟩,
      ⟨s.val.c,by rw [quotient_by_a s,pow_two]⟩⟩,mem_filter.mpr ⟨mem_range.mpr s.val.lt_b,s.val.divides⟩⟩⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro s t h
    have ha : s.val.a=t.val.a := congrArg (fun x : finiteRoot n m => x.val.fst) h
    have hb : s.val.b=t.val.b := congrArg (fun x : finiteRoot n m => x.val.snd) h
    have hc : s.val.c^2=t.val.c^2 := by rw [←quotient_by_a s,←quotient_by_a t,ha]
    have hc' : s.val.c=t.val.c := by nlinarith
    apply Subtype.ext
    cases s with | mk S _ =>
      cases t with | mk T _ =>
        cases S; cases T; dsimp only at ha hb hc'; congr
  · rintro ⟨⟨a,b⟩,h⟩
    obtain ⟨ha,hb⟩ := mem_sigma.mp h
    obtain ⟨hdiv,c,hc⟩ := mem_filter.mp ha
    have ha0 : 0<a := Nat.pos_of_mem_divisors hdiv
    have hd : a∣m := Nat.dvd_of_mem_divisors hdiv
    have he : c^2*a=m := by rw [pow_two,←hc,Nat.div_mul_cancel hd]
    have hc0 : 0<c := by by_contra! h; have := Nat.eq_zero_of_le_zero h; simp [this] at he; omega
    obtain ⟨hb',hbn⟩ := mem_filter.mp hb
    exact ⟨⟨⟨c,a,b,hc0,ha0,mem_range.mp hb',hbn⟩,he⟩,rfl⟩
abbrev NormIdeals (n m : ℕ) := {I : Ideal (R n) // I≠⊥ ∧ Nat.card (R n ⧸ I)=m}
noncomputable def indexedEquiv {n m : ℕ} (hn : 0<n) : indexed n m ≃ NormIdeals n m := by
  let f : indexed n m → NormIdeals n m := fun s => ⟨ideal s.val,ideal_ne_bot _,(quotient_card _).trans s.property⟩
  refine Equiv.ofBijective f ⟨fun _ _ h => Subtype.ext (ideal_injective (congrArg Subtype.val h)),?_⟩
  rintro ⟨I,hI,hm⟩
  obtain ⟨s,rfl⟩ := normal_form hn hI
  exact ⟨⟨s,(quotient_card _).symm.trans hm⟩,rfl⟩
theorem ideal_count {n m : ℕ} (hn : 0<n) (hm : 0 < m) :
    Nat.card (NormIdeals n m)=∑ a∈divisors m,(roots n a).card := by
  classical
  have e : NormIdeals n m ≃ finiteRoot n m := (indexedEquiv hn).symm.trans (divisorEquiv hm)
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_coe,card_sigma]
 
theorem roots_zmod (n a : ℕ) (ha : 0<a) : letI : NeZero a := ⟨ha.ne'⟩
    (roots n a).card=((univ : Finset (ZMod a)).filter (fun x => x^2= -(n:ZMod a))).card := by
  letI : NeZero a := ⟨ha.ne'⟩
  apply card_nbij' (fun b:ℕ => (b:ZMod a)) (fun x:ZMod a => x.val)
  · intro b hb; obtain ⟨_,h⟩ := mem_filter.mp hb
    apply mem_filter.mpr; refine ⟨mem_univ _,?_⟩
    have e := (ZMod.intCast_zmod_eq_zero_iff_dvd _ a).mpr h
    push_cast at e; exact eq_neg_of_add_eq_zero_left e
  · intro z hz; refine mem_filter.mpr ⟨mem_range.mpr (ZMod.val_lt z),?_⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ a).mp
    push_cast; rw [ZMod.natCast_zmod_val,(mem_filter.mp hz).2,neg_add_cancel]
  · intro b hb; change (b:ZMod a).val=b; rw [ZMod.val_natCast,Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp hb).1)]
  · intro x _; exact ZMod.natCast_zmod_val _
end TunnellIdealHNF
end


/- TunnellCMLComplete -/
section
namespace TunnellGaussian
open GaussianInt
end TunnellGaussian
namespace TunnellGaussian
open GaussianInt Finset
end TunnellGaussian
namespace TunnellCoates
open WeierstrassCurve WeierstrassCurve.Affine
end TunnellCoates
namespace TunnellSplit
open Finset
open scoped ComplexConjugate
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
end TunnellSplit
namespace TunnellInert
open Finset Polynomial
end TunnellInert
namespace TunnellSplitMass
open Finset TunnellGaussian
end TunnellSplitMass
namespace TunnellJacobiFiniteBridge
open Polynomial Finset
lemma exponent_eq (k : ℕ) : 1+8*(k+1).choose 2 = (2*k+1)^2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith
end TunnellJacobiFiniteBridge
namespace TunnellEtaLattice
open Finset TunnellGaussian
end TunnellEtaLattice
namespace TunnellQBin
open Polynomial Finset
variable {R : Type*} [CommRing R]
def choose (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, _+1 => 0
  | _+1, 0 => 1
  | n+1, k+1 => choose q n (k+1) + q^(n-k)*choose q n k
def fac (q : R) (n : ℕ) : R := ∏ i ∈ range n, (1-q^(i+1))
lemma choose_zero (q : R) (n : ℕ) : choose q n 0 = 1 := by cases n <;> rfl
lemma choose_above (q : R) {n k : ℕ} (h : n < k) : choose q n k = 0 := by
  induction n generalizing k with
  | zero => cases k <;> first | rfl | omega
  | succ n ih =>
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [choose, ih (by omega), ih (by omega), mul_zero, add_zero]
lemma choose_self (q : R) (n : ℕ) : choose q n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [choose, choose_above _ (by omega), Nat.sub_self, pow_zero, one_mul, ih, zero_add]
lemma fac_succ (q : R) (n : ℕ) : fac q (n+1) = fac q n * (1-q^(n+1)) := prod_range_succ ..
theorem factorial_formula (q : R) (n k : ℕ) (hk : k ≤ n) :
    choose q n k * fac q k * fac q (n-k) = fac q n := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k=0 := Nat.eq_zero_of_le_zero hk
    simp [choose,fac]
  | succ n ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [choose_zero,fac]
    obtain ⟨l,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk0.ne'
    by_cases h : l=n
    · subst l; simp [choose_self,fac]
    have hl : l+1 ≤ n := by omega
    have ha := ih (l+1) hl
    have hb := ih l (by omega)
    have step : n - l = n - (l+1) + 1 := by omega
    have ep : n-l + (l+1) = n+1 := by omega
    rw [choose, Nat.succ_sub_succ_eq_sub]
    calc
      _ = (choose q n (l+1)*fac q (l+1)*fac q (n-(l+1))) * (1-q^(n-l)) +
          q^(n-l) * (choose q n l*fac q l*fac q (n-l)) * (1-q^(l+1)) := by
          have hfac : fac q (n-l) = fac q (n-(l+1))*(1-q^(n-l)) := by
            simpa only [← step] using fac_succ q (n-(l+1))
          rw [hfac,fac_succ q l]
          ring
      _ = _ := by rw [ha,hb,fac_succ,← ep,pow_add]; ring
noncomputable def product (q : R) (n : ℕ) : R[X] :=
  ∏ i ∈ range n, (1 + C (q^i) * X)
lemma product_coeff (q : R) (n k : ℕ) :
    (product q n).coeff k = q^(k.choose 2)*choose q n k := by
  induction n generalizing k with
  | zero =>
    cases k <;> simp [product,choose,Polynomial.coeff_one]
  | succ n ih =>
    have e : product q (n+1) = product q n + C (q^n)*(product q n*X) := by
      rw [product,prod_range_succ]
      change product q n*(1+C (q^n)*X) = _
      ring
    rw [e,coeff_add,coeff_C_mul]
    cases k with
    | zero => simp [choose_zero,ih]
    | succ k =>
      rw [Polynomial.coeff_mul_X,ih,ih,choose]
      by_cases h : k ≤ n
      · have htri : (k+1).choose 2 = k.choose 2 + k := by rw [Nat.choose_succ_succ]; simp [add_comm]
        have hexp : n + k.choose 2 = (k+1).choose 2 + (n-k) := by omega
        rw [mul_add]
        congr 1
        rw [← mul_assoc,← pow_add,hexp,pow_add,mul_assoc]
      · rw [choose_above _ (by omega : n < k)]
        simp
theorem expansion (q : R) (n : ℕ) :
    (∏ j ∈ range n, (1 + C (q^j)*X)) =
      ∑ k ∈ range (n+1), C (q^(k.choose 2)*choose q n k) * X^k := by
  ext k
  change (product q n).coeff k = _
  rw [product_coeff, finsetSum_coeff]
  simp only [coeff_C_mul,coeff_X_pow,mul_ite,mul_one,mul_zero]
  by_cases hk : k < n+1
  · simp [hk]
  · simp [hk, choose_above q (show n < k by omega)]
lemma fac_unit (q : R) (hq : IsNilpotent q) (n : ℕ) : IsUnit (fac q n) := by
  induction n with
  | zero => simp [fac]
  | succ n ih =>
    rw [fac_succ]
    exact ih.mul ((hq.pow_of_pos (by omega : n+1 ≠ 0)).isUnit_one_sub)
lemma fac_stable (q : R) {d : ℕ} (hq : q^(d+1) = 0) {n : ℕ} (hn : d ≤ n) :
    fac q n = fac q d := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc,fac_succ,show d+k+1 = d+1+k by omega,pow_add,hq,zero_mul,
      sub_zero,mul_one,ih (by omega)]
theorem choose_stable (q : R) {d : ℕ} (hq : q^(d+1) = 0) (n k : ℕ)
    (hk : k ≤ n) (hd : d ≤ k) (ht : d ≤ n-k) : choose q n k * fac q d = 1 := by
  apply (fac_unit q ⟨_,hq⟩ d).mul_left_injective
  have h := factorial_formula q n k hk
  rw [fac_stable q hq hd,fac_stable q hq ht,fac_stable q hq (hd.trans hk)] at h
  simpa only [one_mul] using h
theorem map_choose {S : Type*} [CommRing S] (f : R →+* S) (q : R) (n k : ℕ) :
    f (choose q n k) = choose (f q) n k := by
  induction n generalizing k with
  | zero => cases k <;> simp [choose]
  | succ n ih => cases k <;> simp [choose,ih]
theorem expansion_eval (q t : R) (n : ℕ) :
    (∏ j ∈ range n, (1 + q^j*t)) =
      ∑ k ∈ range (n+1), (q^(k.choose 2)*choose q n k)*t^k := by
  have h := congrArg (Polynomial.evalRingHom t) (expansion q n)
  simpa only [map_prod,map_sum,map_add,map_one,map_mul,map_pow,coe_evalRingHom,eval_C,eval_X] using h
end TunnellQBin
namespace TunnellBalanced
open Finset
variable {K : Type*} [Field K]
private lemma normalizer (t : K) (N : ℕ) :
    ∏ i ∈ range N, (-t^(2*i+1)) = (-1 : K)^N * t^(N^2) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [prod_range_succ, ih, show (n+1)^2 = n^2 + (2*n+1) by ring, pow_add, pow_succ (-1 : K)]
    ring
private lemma product_side (t : K) (ht : t ≠ 0) (N : ℕ) :
    ((-1 : K)^N * t^(N^2)) *
        (∏ j ∈ range (2*N), (1+(t^2)^j * (-t^(1-2*(N:ℤ))))) =
      ∏ i ∈ range N, (1-t^(2*i+1))^2 := by
  let F (j : ℕ) := 1 - t^(2*(j:ℤ)+1-2*(N:ℤ))
  have he (j : ℕ) : 1+(t^2)^j*(-t^(1-2*(N:ℤ))) = F j := by
    dsimp [F]
    rw [← pow_mul, ← zpow_natCast t (2*j), mul_neg, ← zpow_add₀ ht, ← sub_eq_add_neg]
    congr 2
    push_cast
    ring
  have hs : (∏ j ∈ range (2*N), F j) =
      (∏ j ∈ range N, F (N-1-j)) * ∏ j ∈ range N, F (N+j) := by
    rw [Finset.prod_range_reflect, ←prod_range_add, two_mul]
  simp only [he]
  rw [hs, ←normalizer, ←mul_assoc, ←prod_mul_distrib, ←prod_mul_distrib]
  apply prod_congr rfl
  intro i hi
  have hi' := mem_range.mp hi
  have hneg : (2*((N-1-i:ℕ):ℤ)+1-2*(N:ℤ)) = -((2*i+1:ℕ):ℤ) := by omega
  have hpos : (2*((N+i:ℕ):ℤ)+1-2*(N:ℤ)) = ((2*i+1:ℕ):ℤ) := by omega
  dsimp only [F]
  rw [hneg, hpos, zpow_neg, zpow_natCast]
  field_simp
  ring
private lemma triangular (k : ℕ) : 2*k.choose 2 + k = k^2 := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    nlinarith
private lemma power_side (t : K) (ht : t ≠ 0) (N k : ℕ) :
    t^(N^2) * (t^2)^k.choose 2 * (t^(1-2*(N:ℤ)))^k
      = t^(((k:ℤ)-(N:ℤ)).natAbs^2) := by
  rw [← pow_mul, ← zpow_natCast t (N^2), ← zpow_natCast t (2*k.choose 2),
      ← zpow_natCast (t^(1-2*(N:ℤ))) k, ← zpow_mul, ← zpow_add₀ ht, ← zpow_add₀ ht,
      ← zpow_natCast t (((k:ℤ)-(N:ℤ)).natAbs^2)]
  congr 1
  push_cast
  rw [sq_abs]
  have h : (2:ℤ)*(k.choose 2:ℕ) + (k:ℤ) = (k:ℤ)^2 := by exact_mod_cast triangular k
  linarith only [h]
private theorem balanced_field (t : K) (ht : t ≠ 0) (N : ℕ) :
    (∏ i ∈ range N, (1-t^(2*i+1))^2) =
    ∑ k ∈ range (2*N+1), ((Int.negOnePow ((k:ℤ)-(N:ℤ)) : ℤ) : K) *
        t ^ (((k:ℤ)-(N:ℤ)).natAbs ^ 2) * TunnellQBin.choose (t^2) (2*N) k := by
  rw [←product_side t ht N, TunnellQBin.expansion_eval, Finset.mul_sum]
  apply sum_congr rfl
  intro k hk
  have hs : ((Int.negOnePow ((k:ℤ)-(N:ℤ)) : ℤ) : K) =
      (-1:K)^k * (-1:K)^N := by
    rw [Int.negOnePow_sub, Units.val_mul, Int.cast_mul, Int.cast_negOnePow_natCast,
      Int.cast_negOnePow_natCast]
  rw [hs, ← power_side t ht, neg_eq_neg_one_mul (t^(1-2*(N:ℤ))), mul_pow]
  ring
open Polynomial in
theorem balanced {R : Type*} [CommRing R] (t : R) (N : ℕ) :
    (∏ i ∈ range N, (1-t^(2*i+1))^2) =
    ∑ k ∈ range (2*N+1), ((Int.negOnePow ((k:ℤ)-(N:ℤ)) : ℤ) : R) *
        t ^ (((k:ℤ)-(N:ℤ)).natAbs^2) * TunnellQBin.choose (t^2) (2*N) k := by
  let x : ℤ[X] := X
  let f := algebraMap ℤ[X] (FractionRing ℤ[X])
  have hf : Function.Injective f := IsFractionRing.injective _ _
  have hx : f x ≠ 0 := by
    rw [← map_zero f]
    exact fun h ↦ Polynomial.X_ne_zero (hf h)
  have hpoly : (∏ i ∈ range N, (1-x^(2*i+1))^2) =
      ∑ k ∈ range (2*N+1), ((Int.negOnePow ((k:ℤ)-(N:ℤ)) : ℤ) : ℤ[X]) *
        x ^ (((k:ℤ)-(N:ℤ)).natAbs^2) * TunnellQBin.choose (x^2) (2*N) k := by
    apply hf
    simpa only [map_prod, map_sum, map_pow, map_sub, map_one, map_mul, map_intCast,
      TunnellQBin.map_choose] using balanced_field (f x) hx N
  let g := Polynomial.eval₂RingHom (Int.castRingHom R) t
  have hxt : g x = t := by simp [g,x]
  simpa only [map_prod, map_sum, map_pow, map_sub, map_one, map_mul, map_intCast,
    TunnellQBin.map_choose,hxt] using congrArg g hpoly
end TunnellBalanced
namespace TunnellCubicFinite
open Finset Polynomial TunnellQBin
open LaurentPolynomial hiding C
abbrev L := LaurentPolynomial ℤ
noncomputable abbrev q : L := T 1
lemma fac_ne (n : ℕ) : fac q n ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j hj he
  have e : (1 : ℤ[X]) = X^(j+1) := by
    apply Polynomial.toLaurent_injective
    simpa only [map_one,map_pow,toLaurent_X,q] using sub_eq_zero.mp he
  have c := congrArg (fun p : ℤ[X] => p.coeff 0) e
  simp at c
lemma choose_symm (m k : ℕ) (hk : k ≤ m) :
    choose q m k = choose q m (m-k) := by
  have a := factorial_formula q m k hk
  have b := factorial_formula q m (m-k) (by omega)
  rw [Nat.sub_sub_self hk, mul_right_comm] at b
  exact mul_right_cancel₀ (fac_ne k) (mul_right_cancel₀ (fac_ne (m-k)) (a.trans b.symm))
lemma double_choose (m : ℕ) : 2*(m.choose 2 : ℤ) = (m:ℤ)*(m-1:ℤ) := by
  induction m with
  | zero => norm_num
  | succ m ih =>
    rw [Nat.choose_succ_succ, Nat.choose_one_right]
    push_cast
    nlinarith
end TunnellCubicFinite
namespace TunnellCubicFinite
open Polynomial Finset TunnellQBin
end TunnellCubicFinite
namespace TunnellTruncated
open TunnellQBin Polynomial Finset
variable {R : Type*} [CommRing R]
lemma triangle_ge (k : ℕ) : k ≤ (k+1).choose 2 := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.choose_succ_succ,Nat.choose_one_right]; omega
lemma map_fac {S : Type*} [CommRing S] (f : R →+* S) (q : R) (n : ℕ) :
    f (fac q n) = fac (f q) n := by simp [fac]
lemma poly_fac (s n : ℕ) :
    fac ((X : ℤ[X])^s) n = ∏ t ∈ Icc 1 n, (1-X^(s*t)) := by
  induction n with
  | zero => simp [fac]
  | succ n ih =>
    rw [fac_succ,ih,prod_Icc_succ_top (by omega : 1 ≤ n+1),← pow_mul]
noncomputable def trunc (d : ℕ) := AdjoinRoot.mk ((X : ℤ[X])^(d+1))
lemma nilpotent_trunc (d : ℕ) : (trunc d X)^(d+1)=0 := by
  rw [← map_pow]
  exact AdjoinRoot.mk_self
lemma trunc_pow (d s : ℕ) (hs : s ≠ 0) : (trunc d (X^s))^(d+1)=0 := by
  rw [map_pow,← pow_mul,mul_comm,pow_mul,nilpotent_trunc,zero_pow hs]
lemma fac_even_odd (t : R) (N : ℕ) :
    fac t (2*N) = fac (t^2) N * (∏ i ∈ range N, (1-t^(2*i+1))) := by
  induction N with
  | zero => simp [fac]
  | succ n ih =>
    rw [show 2*(n+1) = 2*n+1+1 by omega,fac_succ,fac_succ,ih,fac_succ,prod_range_succ,
      ← pow_mul,show 2*(n+1) = 2*n+1+1 by omega]
    ring
lemma centered_sum (N : ℕ) (f : ℤ → R) :
    ∑ k ∈ range (2*N+1), f ((k:ℤ)-(N:ℤ)) = ∑ j ∈ Icc (-(N:ℤ)) (N:ℤ), f j := by
  apply sum_bij (fun (k : ℕ) _ => (k:ℤ)-(N:ℤ))
  · intro k hk
    simp only [mem_range] at hk
    rw [mem_Icc]; omega
  · intro k _ l _ he; omega
  · intro j hj
    rw [mem_Icc] at hj
    refine ⟨(j+N).toNat,mem_range.mpr (by omega),by omega⟩
  · intro _ _; rfl
theorem theta_stabilized (t : R) (d N : ℕ) (hN : 2*d ≤ N) (ht : t^(d+1)=0)
    (h : (∏ i ∈ range N, (1-t^(2*i+1))^2) = ∑ k ∈ range (2*N+1),
      (((((k:ℤ)-(N:ℤ)).negOnePow : ℤ) : R) * t^(((k:ℤ)-(N:ℤ)).natAbs^2)) *
        choose (t^2) (2*N) k) :
    fac t d ^ 2 = (∑ j ∈ Icc (-(d:ℤ)) (d:ℤ),
      ((j.negOnePow : ℤ) : R) * t^(j.natAbs^2)) * fac (t^2) d := by
  let f (j : ℤ) := ((j.negOnePow : ℤ) : R) * t^(j.natAbs^2)
  change fac t d ^ 2 = (∑ j ∈ Icc (-(d:ℤ)) (d:ℤ), f j) * fac (t^2) d
  have hq : (t^2)^(d+1)=0 := by rw [← pow_mul,mul_comm,pow_mul,ht,zero_pow (by decide : 2≠0)]
  have htail (j : ℤ) (hj : ¬ j ∈ Icc (-(d:ℤ)) (d:ℤ)) : f j = 0 := by
    have habs := Int.natAbs_eq j
    simp only [mem_Icc,not_and_or,not_le] at hj
    have hjd : d+1 ≤ j.natAbs := by omega
    have hd : d+1 ≤ j.natAbs^2 := by nlinarith [Nat.le_mul_self j.natAbs]
    simp [f,pow_eq_zero_of_le hd ht]
  have hside : fac t d ^ 2 = (∏ i ∈ range N, (1-t^(2*i+1))^2) * fac (t^2) d ^ 2 := by
    have hfac := fac_even_odd t N
    rw [fac_stable t ht (n:=2*N) (by omega),fac_stable (t^2) hq (n:=N) (by omega)] at hfac
    rw [hfac,prod_pow]; ring
  rw [hside,h,pow_two (fac (t^2) d),← mul_assoc]
  congr 1
  rw [sum_mul]
  calc
    _ = ∑ k ∈ range (2*N+1), f ((k:ℤ)-(N:ℤ)) := by
      apply sum_congr rfl
      intro k hk
      change f ((k:ℤ)-N) * _ * _ = _
      by_cases hj : ((k:ℤ)-N) ∈ Icc (-(d:ℤ)) (d:ℤ)
      · rw [mem_Icc] at hj
        rw [mul_assoc,choose_stable (t^2) hq _ _ (by omega) (by omega) (by omega),mul_one]
      · rw [htail _ hj,zero_mul,zero_mul]
    _ = _ := by
      rw [centered_sum]
      symm
      apply sum_subset (fun j hj => ?_) (fun j _ hj => htail j hj)
      simp only [mem_Icc] at hj ⊢
      omega
end TunnellTruncated
namespace TunnellArithmetic
open Polynomial Finset TunnellGaussian TunnellEtaLattice
end TunnellArithmetic
namespace TunnellCMLSeries
open Finset TunnellGaussian
end TunnellCMLSeries
namespace TunnellCMLSeries
open TunnellGaussian OMA.R_CongruentNumber_Tunnell_even_R1 Finset
end TunnellCMLSeries
end


/- TunnellRankinCoeff -/
section
namespace TunnellRankin
open Finset TunnellCMLSeries TunnellGaussian
def negWeight (d m : ℕ) : ℤ := if Odd m then jacobiSym (-((2*d:ℕ):ℤ)) m else 0
lemma negWeight_one (d : ℕ) : negWeight d 1=1 := by simp [negWeight]
lemma negWeight_mul (d a b : ℕ) : negWeight d (a*b)=negWeight d a*negWeight d b := by
  by_cases ha : Odd a <;> by_cases hb : Odd b <;> simp [negWeight,Nat.odd_mul,ha,hb]
  exact jacobiSym.mul_right' _ (fun h => by simp [h] at ha) (fun h => by simp [h] at hb)
lemma negWeight_pow (d a k : ℕ) : negWeight d (a^k)=(negWeight d a)^k := by
  induction k with
  | zero => simp [negWeight_one]
  | succ k ih => rw [pow_succ,negWeight_mul,ih,pow_succ]
def chi (d : ℕ) : ArithmeticFunction ℤ := ⟨negWeight d,by simp [negWeight]⟩
lemma chi_mult (d : ℕ) : (chi d).IsMultiplicative :=
  ⟨negWeight_one d,fun _ => negWeight_mul d _ _⟩
def idealCoeff (d m : ℕ) : ℤ := ∑ e∈m.divisors,negWeight d e
lemma idealCoeff_mul (d : ℕ) {a b : ℕ} (h : a.Coprime b) :
    idealCoeff d (a*b)=idealCoeff d a*idealCoeff d b := by
  let z := (ArithmeticFunction.zeta : ArithmeticFunction ℤ)
  have he (m : ℕ) : (chi d*z) m = idealCoeff d m := by
    rw [show z=(ArithmeticFunction.zeta : ArithmeticFunction ℤ) by rfl,ArithmeticFunction.coe_mul_zeta_apply]
    rfl
  rw [←he,←he,←he]
  exact ((chi_mult d).mul ArithmeticFunction.isMultiplicative_zeta.natCast).map_mul_of_coprime h
lemma idealCoeff_one (d : ℕ) : idealCoeff d 1=1 := by simp [idealCoeff,negWeight_one]
lemma idealCoeff_prime_pow (d p k : ℕ) (hp : p.Prime) :
    idealCoeff d (p^k)=∑ j∈range (k+1),(negWeight d p)^j := by
  rw [idealCoeff,Nat.sum_divisors_prime_pow hp]
  simp_rw [negWeight_pow]
end TunnellRankin
end


/- TunnellRankinRoots -/
section
namespace TunnellRankin
open Finset
private abbrev rootSet (d a : ℕ) := {x : ZMod a // x^2 = -((2*d:ℕ) : ZMod a)}
noncomputable def rho (d a : ℕ) : ℕ := if a = 0 then 0 else Nat.card (rootSet d a)
lemma rho_eq_card (d a : ℕ) [NeZero a] : rho d a =
    Fintype.card {x : ZMod a // x^2 = -((2*d:ℕ) : ZMod a)} := by
  simp only [rho,if_neg (NeZero.ne a),Nat.card_eq_fintype_card]
lemma rho_zero (d : ℕ) : rho d 0 = 0 := by simp [rho]
lemma rho_one (d : ℕ) : rho d 1 = 1 := by
  rw [rho_eq_card]
  have : Unique (rootSet d 1) := ⟨⟨⟨0,Subsingleton.elim _ _⟩⟩,fun _ => Subsingleton.elim _ _⟩
  exact Fintype.card_unique
lemma rho_mul (d : ℕ) {a b : ℕ} (h : a.Coprime b) :
    rho d (a*b) = rho d a * rho d b := by
  classical
  rcases eq_or_ne a 0 with rfl|ha
  · simp [rho_zero]
  rcases eq_or_ne b 0 with rfl|hb
  · simp [rho_zero]
  let : NeZero a := ⟨ha⟩
  let : NeZero b := ⟨hb⟩
  let e := ZMod.chineseRemainder h
  have he (x : ZMod (a*b)) : x^2 = -((2*d:ℕ):ZMod (a*b)) ↔
      (e x).1^2 = -((2*d:ℕ):ZMod a) ∧ (e x).2^2 = -((2*d:ℕ):ZMod b) := by
    rw [← e.injective.eq_iff, map_pow,map_neg,map_natCast,Prod.ext_iff]
    rfl
  let E : rootSet d (a*b) ≃ rootSet d a × rootSet d b := {
    toFun := fun x => (⟨(e x.val).1,((he _).mp x.property).1⟩,⟨(e x.val).2,((he _).mp x.property).2⟩)
    invFun := fun x => ⟨e.symm (x.1.val,x.2.val),(he _).mpr (by simp [x.1.property,x.2.property])⟩
    left_inv := fun _ => Subtype.ext (by simp)
    right_inv := fun _ => Prod.ext (Subtype.ext (by simp)) (Subtype.ext (by simp)) }
  simp only [rho_eq_card,← Fintype.card_prod]
  exact Fintype.card_congr E
private theorem roots_lift {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (hk : ∀ x, f x = 0 → x^2 = 0)
    (n : R) (hn : IsUnit n) (h₂ : IsUnit (2:R)) :
    Function.Bijective (fun x : {x:R // x^2=n} => (⟨f x,by rw [← map_pow,x.property]⟩ : {x:S // x^2=f n})) := by
  have liftUnit (x : R) (h : IsUnit (f x)) : IsUnit x := by
    obtain ⟨s,hs⟩ := isUnit_iff_exists_inv.mp h
    obtain ⟨t,rfl⟩ := hf s
    have he := hk (1-x*t) (by simp [hs])
    exact isUnit_iff_exists_inv.mpr ⟨t*(2-x*t),by linear_combination -he⟩
  have rootUnit (x : {x:S // x^2=f n}) : IsUnit x.val :=
    (isUnit_pow_iff (by decide : 2 ≠ 0)).mp (x.property ▸ hn.map f)
  constructor
  · intro x y hxy
    have h : f x.val = f y.val := congrArg Subtype.val hxy
    have hu : IsUnit (x.val+y.val) := liftUnit _ (by
      rw [map_add,←h,←two_mul]
      exact (by simpa only [map_ofNat] using h₂.map f : IsUnit (2:S)).mul
        (rootUnit ⟨f x.val,by rw [←map_pow,x.property]⟩))
    obtain ⟨t,ht⟩ := isUnit_iff_exists_inv.mp hu
    apply Subtype.ext
    linear_combination t*(x.property - y.property) - (x.val-y.val)*ht
  · intro x
    obtain ⟨y,hy⟩ := hf x.val
    have hu : IsUnit (2*y) := h₂.mul (liftUnit _ (hy ▸ rootUnit x))
    obtain ⟨t,ht⟩ := isUnit_iff_exists_inv.mp hu
    have hε : f (y^2-n) = 0 := by simp [hy,x.property]
    have hε₂ := hk _ hε
    refine ⟨⟨y-(y^2-n)*t,?_⟩,Subtype.ext ?_⟩
    · linear_combination t^2*hε₂ - (y^2-n)*ht
    · simpa [hε] using (show f (y-(y^2-n)*t) = x.val by rw [map_sub,map_mul,hε,zero_mul,sub_zero,hy])
lemma rho_good_lift {d p k : ℕ} (hp : p.Prime) (hn : ¬ p ∣ 2*d) (hk : 0 < k) :
    rho d (p^(k+1)) = rho d (p^k) := by
  let : Fact p.Prime := ⟨hp⟩
  let f := ZMod.castHom (pow_dvd_pow p (show k ≤ k+1 by omega)) (ZMod (p^k))
  have ker (x : ZMod (p^(k+1))) (hx : f x = 0) : x^2=0 := by
    rw [←ZMod.natCast_zmod_val x,map_natCast,ZMod.natCast_eq_zero_iff] at hx
    rw [←ZMod.natCast_zmod_val x,←Nat.cast_pow,ZMod.natCast_eq_zero_iff]
    exact dvd_trans (pow_dvd_pow p (show k+1 ≤ k*2 by omega))
      (by simpa [pow_mul] using pow_dvd_pow_of_dvd hx 2)
  have hu := (ZMod.isUnit_natCast_iff_not_dvd_pow (a:=2*d) hp (by omega : 0<k+1)).mpr hn
  have h₂ := (ZMod.isUnit_natCast_iff_not_dvd_pow (a:=2) hp (by omega : 0<k+1)).mpr
    (fun h => hn (dvd_mul_of_dvd_left h d))
  have h := roots_lift f (ZMod.ringHom_surjective f) ker _ hu.neg (by simpa using h₂)
  have e := Equiv.ofBijective _ h
  simpa only [rho_eq_card,map_neg,map_natCast] using Fintype.card_congr e
lemma rho_good_pow {d p : ℕ} (hp : p.Prime) (hn : ¬p ∣ 2*d) (k : ℕ) :
    rho d (p^(k+1)) = rho d p := by
  induction k with
  | zero => simp
  | succ k ih => exact (rho_good_lift hp hn (Nat.succ_pos _)).trans ih
lemma rho_ramified_prime {d p : ℕ} (hp : p.Prime) (h : p ∣ 2*d) : rho d p = 1 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [rho_eq_card]
  have hn := (ZMod.natCast_eq_zero_iff _ _).mpr h
  have : Unique (rootSet d p) := {
    default := ⟨0,by simp [hn]⟩
    uniq := fun x => Subtype.ext (by
      have hzero : x.val^2 = 0 := by simpa [hn] using x.property
      exact (pow_eq_zero_iff (by decide : 2≠0)).mp hzero) }
  exact Fintype.card_unique
lemma rho_ramified_pow {d p : ℕ} (hp : p.Prime) (hn : p ∣ 2*d)
    (hs : Squarefree (2*d)) (k : ℕ) : rho d (p^(k+2)) = 0 := by
  let : Fact p.Prime := ⟨hp⟩
  rw [rho_eq_card,Fintype.card_eq_zero_iff]
  refine ⟨fun x => ?_⟩
  have hx : p^(k+2) ∣ x.val.val^2+2*d := (ZMod.natCast_eq_zero_iff _ _).mp (by
    push_cast
    simpa only [ZMod.natCast_zmod_val,Nat.cast_mul,Nat.cast_ofNat] using (add_eq_zero_iff_eq_neg.mpr x.property))
  have h2 : p^2 ∣ x.val.val^2+2*d := dvd_trans (pow_dvd_pow p (by omega : 2≤k+2)) hx
  have h1 : p ∣ x.val.val^2 := (Nat.dvd_add_iff_left hn).mpr
    ((dvd_pow_self p (by decide : 2≠0)).trans h2)
  have hx2 := pow_dvd_pow_of_dvd (hp.dvd_of_dvd_pow h1) 2
  exact (Nat.squarefree_iff_prime_squarefree.mp hs p hp) (by
    simpa [sq] using (Nat.dvd_add_iff_right hx2).mpr h2)
lemma rho_prime (d p : ℕ) (hp : p.Prime) :
    (rho d p : ℤ) = 1+negWeight d p := by
  let : Fact p.Prime := ⟨hp⟩
  rcases eq_or_ne p 2 with rfl|h₂
  · simp [rho_ramified_prime Nat.prime_two (dvd_mul_right 2 d),negWeight]
  have ho := hp.odd_of_ne_two h₂
  rw [negWeight,if_pos ho,←jacobiSym.legendreSym.to_jacobiSym,add_comm,rho_eq_card]
  simpa [Fintype.card_subtype] using legendreSym.card_sqrts p h₂ (-((2*d:ℕ):ℤ))
end TunnellRankin
end


/- TunnellRankinHNF -/
section
namespace TunnellRankin
open Finset
private def squareIndicator : ArithmeticFunction ℤ :=
  ⟨fun m => if m ≠ 0 ∧ IsSquare m then 1 else 0,by simp⟩
private lemma coprime_square_iff {a b : ℕ} (hc : a.Coprime b) :
    IsSquare (a*b) ↔ IsSquare a ∧ IsSquare b := by
  have left {x y : ℕ} (hh : x.Coprime y) (hs : IsSquare (x*y)) : IsSquare x := by
    obtain ⟨r,hr⟩ := hs
    obtain ⟨t,ht⟩ := exists_eq_pow_of_mul_eq_pow
      (by change IsUnit (x.gcd y); rw [hh.gcd_eq_one]; simp : IsUnit (gcd x y))
      (by simpa [sq] using hr : x*y=r^2)
    exact ⟨t,by simpa [sq] using ht⟩
  exact ⟨fun h => ⟨left hc h,left hc.symm (mul_comm a b ▸ h)⟩,fun h => h.1.mul h.2⟩
private lemma squareIndicator_mult : squareIndicator.IsMultiplicative := by
  refine ⟨by simp [squareIndicator],?_⟩
  intro a b h
  simp only [squareIndicator,ArithmeticFunction.coe_mk,mul_ne_zero_iff,coprime_square_iff h]
  split_ifs <;> simp_all
private noncomputable def rootFun (d : ℕ) : ArithmeticFunction ℤ :=
  ⟨fun m => (rho d m:ℤ),by simp [rho_zero]⟩
private lemma rootFun_mult (d : ℕ) : (rootFun d).IsMultiplicative :=
  ⟨by simp [rootFun,rho_one],fun h => by simp [rootFun,rho_mul _ h]⟩
private lemma square_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) :
    IsSquare (p^j) ↔ Even j := by
  constructor
  · rintro ⟨b,hb⟩
    rw [←sq] at hb
    have hv := congrArg (fun n : ℕ => n.factorization p) hb
    change (p^j).factorization p = (b^2).factorization p at hv
    rw [Nat.factorization_pow_self hp,Nat.factorization_pow] at hv
    simp only [Finsupp.smul_apply,smul_eq_mul] at hv
    exact ⟨b.factorization p,by omega⟩
  · rintro ⟨k,rfl⟩
    exact ⟨p^k,pow_add p k k⟩
private noncomputable def localRoots (d p k : ℕ) : ℤ :=
  ∑ j ∈ range (k+1),if Even j then (rho d (p^(k-j)):ℤ) else 0
private lemma convolution_pow (d p k : ℕ) (hp : p.Prime) :
    (rootFun d*squareIndicator) (p^k)=localRoots d p k := by
  rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal' (fun x y => rootFun d x*squareIndicator y),
    Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro j hj
  have hjk : j≤k := by simpa using hj
  simp [squareIndicator,rootFun, Nat.pow_div hjk hp.pos,hp.ne_zero,square_prime_pow hp,
    mul_ite]
private lemma localRoots_step (d p k : ℕ) :
    localRoots d p (k+2) = (rho d (p^(k+2)):ℤ) + localRoots d p k := by
  unfold localRoots
  rw [sum_range_succ',sum_range_succ']
  simp only [Even.zero,if_true,Nat.sub_zero,zero_add,Nat.not_even_one,if_false,add_zero]
  rw [add_comm]
  congr 1
  apply sum_congr rfl
  intro j hj
  simp [Nat.even_add]
private lemma negWeight_zero_iff (d p : ℕ) (hp : p.Prime) :
    negWeight d p=0 ↔ p ∣ 2*d := by
  rcases eq_or_ne p 2 with rfl|h₂
  · simp [negWeight]
  let : Fact p.Prime := ⟨hp⟩
  rw [negWeight,if_pos (hp.odd_of_ne_two h₂),←jacobiSym.legendreSym.to_jacobiSym,legendreSym.eq_zero_iff]
  simp only [Int.cast_neg,Int.cast_natCast,neg_eq_zero,ZMod.natCast_eq_zero_iff]
private lemma localRoots_eq (d p k : ℕ) (hp : p.Prime) (hs : Squarefree (2*d)) :
    localRoots d p k = ∑ j ∈ range (k+1),(negWeight d p)^j := by
  induction k using Nat.twoStepInduction with
  | zero =>
    change (∑ j ∈ range 1, if Even j then (rho d (p^(0-j)):ℤ) else 0)=_
    rw [sum_range_one,sum_range_one]
    simp [rho_one]
  | one => simp [localRoots,sum_range_succ,rho_prime d p hp,add_comm]
  | more k ih _ =>
    rw [localRoots_step,ih,sum_range_succ (n:=k+2),sum_range_succ (n:=k+1)]
    suffices h : (rho d (p^(k+2)):ℤ) = (negWeight d p)^(k+1) * (1+negWeight d p) by
      rw [h,pow_succ (negWeight d p) (k+1)]
      ring
    by_cases hz : p∣2*d
    · simp [rho_ramified_pow hp hz hs,(negWeight_zero_iff d p hp).mpr hz]
    have hne := mt (negWeight_zero_iff d p hp).mp hz
    have ht : negWeight d p=0 ∨ negWeight d p=1 ∨ negWeight d p= -1 := by
      unfold negWeight
      split
      · exact jacobiSym.trichotomy _ _
      · simp
    rw [rho_good_pow hp hz (k+1),rho_prime d p hp]
    rcases ht with h|h|h <;> simp_all
theorem idealCoeff_eq_roots (d m : ℕ) (hs : Squarefree (2*d)) :
    idealCoeff d m = ∑ a ∈ m.divisors, if IsSquare (m/a) then (rho d a:ℤ) else 0 := by
  let F : ArithmeticFunction ℤ := ⟨idealCoeff d,by simp [idealCoeff]⟩
  have hF : F.IsMultiplicative := ⟨idealCoeff_one d,idealCoeff_mul d⟩
  have he : F=rootFun d*squareIndicator := (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers
    F hF _ ((rootFun_mult d).mul squareIndicator_mult)).mpr (fun p k hp => by
      change idealCoeff d (p^k)=_
      rw [idealCoeff_prime_pow d p k hp,convolution_pow d p k hp,localRoots_eq d p k hp hs])
  change F m=_
  rw [he,ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun x y => rootFun d x*squareIndicator y)]
  apply sum_congr rfl
  intro a ha
  obtain ⟨hdiv,hm⟩ := Nat.mem_divisors.mp ha
  have hq : 0 < m / a := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdiv)
    (Nat.pos_of_dvd_of_pos hdiv (Nat.pos_of_ne_zero hm))
  simp [rootFun,squareIndicator,hq.ne',mul_ite]
end TunnellRankin
end


/- TunnellRankinIdealCount -/
section
namespace TunnellIdealHNF
open Finset TunnellRankin
theorem rankin_ideal_count (d m : ℕ) (hs : Squarefree (2*d)) (hm : 0 < m) :
    idealCoeff d m=(Nat.card (NormIdeals (2*d) m):ℤ) := by
  have hn : 0<2*d := Nat.pos_of_ne_zero hs.ne_zero
  rw [idealCoeff_eq_roots _ _ hs,ideal_count hn hm,divisors,sum_filter]
  push_cast
  apply sum_congr rfl
  intro a ha
  have hap := Nat.pos_of_mem_divisors ha
  letI : NeZero a := ⟨hap.ne'⟩
  have h : (roots (2*d) a).card=rho d a := by
    rw [roots_zmod _ _ hap,rho_eq_card,Fintype.card_subtype]
  split <;> simp_all
end TunnellIdealHNF
end


/- TunnellIdealGenerators -/
section
namespace TunnellIdealGenerators
open TunnellIdealHNF TunnellShell TunnellHurwitz TunnellToricClass TunnellEmbeddedIdeals
noncomputable section
lemma domain {n : ℕ} (hn : 0<n) : IsDomain (R n) := by
  letI : NoZeroDivisors (R n) := ⟨by
    intro x y h
    by_contra! hxy
    have hN := congrArg Zsqrtd.norm h
    rw [Zsqrtd.norm_mul,Zsqrtd.norm_zero] at hN
    exact (mul_pos (positive_norm hn hxy.1) (positive_norm hn hxy.2)).ne' hN⟩
  exact NoZeroDivisors.to_isDomain _
lemma unit_sign {n : ℕ} (hn : 2≤n) (u : (R n)ˣ) : (u:R n)=1 ∨ (u:R n)= -1 := by
  have h := (Zsqrtd.norm_eq_one_iff' (d:= -(n:ℤ)) (by omega) u.val).mpr u.isUnit
  change u.val.re*u.val.re- -(n:ℤ)*u.val.im*u.val.im=1 at h
  have h0 : u.val.im=0 := by
    by_contra hn0
    have hi : 1≤u.val.im*u.val.im := mul_self_pos.mpr hn0
    nlinarith [mul_le_mul_of_nonneg_left hi (show 0≤(n:ℤ) by omega),mul_self_nonneg u.val.re]
  rw [h0] at h
  have he : (u.val.re-1)*(u.val.re+1)=0 := by nlinarith
  rcases mul_eq_zero.mp he with h|h
  · exact Or.inl (Zsqrtd.ext (by change u.val.re=1; omega) h0)
  · exact Or.inr (Zsqrtd.ext (by change u.val.re= -1; omega) (by simpa using h0))
lemma generator_sign {n : ℕ} (hn : 2≤n) {x y : R n} (h : principal x=principal y) :
    y=x ∨ y= -x := by
  letI := domain (show 0<n by omega)
  obtain ⟨u,hu⟩ := Ideal.span_singleton_eq_span_singleton.mp h
  rcases unit_sign hn u with h|h <;> simp [h] at hu <;> exact (by tauto)
def divide {n : ℕ} (I : Ideal (R n)) (x : R n) : Ideal (R n) :=
  (principal x*conjugate I).colon {(normI I:R n)}
lemma mul_right_cancel_ideal {n : ℕ} (hn : Squarefree n) (h2 : n%4=2)
    {I A B : Ideal (R n)} (hI : I≠⊥) (h : A*I=B*I) : A=B := by
  letI := domain (show 0<n by omega)
  apply (Ideal.span_singleton_mul_left_inj (Nat.cast_ne_zero.mpr (normI_positive (by omega) I hI).ne')).mp
  change A*principal (normI I:R n)=B*principal (normI I:R n)
  rw [←norm_conjugate hn h2 I hI,←mul_assoc,←mul_assoc,h]
lemma divide_mul {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {I : Ideal (R n)} (hI : I≠⊥) {x : R n} (hx : x∈I) :
    divide I x*I=principal x := by
  letI := domain (show 0<n by omega)
  let P := principal x*conjugate I
  let N : R n := normI I
  have hp0 : principal x≤I := by rw [principal,Ideal.span_singleton_le_iff_mem]; exact hx
  have hp : P≤principal N := (mul_le_mul_left hp0 _).trans_eq (norm_conjugate hn h2 I hI)
  have hP : divide I x*principal N = P := by
    ext t
    rw [principal,Ideal.mem_mul_span_singleton]
    constructor
    · rintro ⟨y,hy,rfl⟩
      exact Submodule.mem_colon_singleton.mp hy
    · intro ht
      obtain ⟨y,hy⟩ := Ideal.mem_span_singleton.mp (hp ht)
      exact ⟨y,Submodule.mem_colon_singleton.mpr (show y*N∈P by rwa [mul_comm,←hy]),(mul_comm _ _).trans hy.symm⟩
  have hN : N≠0 := Nat.cast_ne_zero.mpr (normI_positive (by omega) I hI).ne'
  apply (Ideal.span_singleton_mul_left_inj hN).mp
  change divide I x*I*principal N=principal x*principal N
  calc
    _ = (divide I x*principal N)*I := by ac_rfl
    _ = principal x*(I*conjugate I) := by rw [hP]; dsimp [P]; ac_rfl
    _ = _ := by rw [norm_conjugate hn h2 I hI]
lemma image_principal_mul {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n)
    (x : R n) (I : Ideal (R n)) : image hv (principal x * I) = line (embed n v hv x)*image hv I := by
  rw [image_mul,principal,image_principal hn h2 hv, mul_assoc,←image_order hn h2 hv,←image_mul,Ideal.top_mul]
theorem inverse_class_iff {n : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n)
    {I B : Ideal (R n)} (hI : I≠⊥) :
    homothetic v (image hv (conjugate I)) (image hv B) ↔ ∃ x : R n, x≠0 ∧ B*I=principal x := by
  let N : Q := normI I
  have hN : N≠0 := by
    intro h
    have H := congrArg QuaternionAlgebra.re h
    change ((normI I:ℕ):ℚ)=0 at H
    exact (normI_positive (by omega) I hI).ne' (by exact_mod_cast H)
  have hNc : N∈C v := mem_C.mpr (Nat.cast_comm (normI I) _).symm
  constructor
  · rintro ⟨c,_,hc,e⟩
    have h : image hv (B*I)=line (c*N)*J v v := by
      rw [image_mul,←e,mul_assoc,←image_mul,mul_comm (conjugate I),norm_conjugate hn h2 I hI,principal,image_principal hn h2 hv,map_natCast,←mul_assoc,line_mul]
    have hm : c*N ∈ image hv (B*I) := by
      rw [h]; exact Submodule.mem_span_singleton_mul.mpr ⟨1,one_J v,mul_one _⟩
    obtain ⟨x,_,ex⟩ := (mem_image _).mp hm
    refine ⟨x,fun H => (mul_ne_zero hc hN) (by simpa [H] using ex.symm),image_injective hn hv ?_⟩
    rw [h,principal,image_principal hn h2 hv,ex]
  · rintro ⟨x,hx,e⟩
    let X := embed n v hv x
    have hX : X≠0 := fun h => hx (embed_inj hn hv (h.trans (map_zero _).symm))
    have hXc : X∈C v := center_image hv (principal x) ⟨x,Ideal.mem_span_singleton_self _,rfl⟩
    have he : line N*image hv B = line X*image hv (conjugate I) := by
      have H : principal (normI I:R n)*B = principal x*conjugate I := by
        rw [←norm_conjugate hn h2 I hI,←e]; ac_rfl
      have H' := congrArg (image hv) H
      rw [image_principal_mul hn h2 hv,image_principal_mul hn h2 hv,map_natCast] at H'
      exact H'
    refine ⟨N⁻¹*X,(mul_C v) (Submodule.mul_mem_mul (mem_C.mpr ((show Commute _ N from mem_C.mp hNc).inv_right₀)) hXc),
      mul_ne_zero (inv_ne_zero hN) hX,?_⟩
    rw [←line_mul,mul_assoc,←he,←mul_assoc,two_sided_inverse hN,one_mul]
end
end TunnellIdealGenerators
end


/- TunnellIdealRepresentations -/
section
namespace TunnellIdealGenerators
open TunnellIdealHNF TunnellShell TunnellHurwitz TunnellToricClass TunnellEmbeddedIdeals
noncomputable section
abbrev Representations {n : ℕ} (I : Ideal (R n)) (m : ℕ) := {x : R n // x∈I ∧ x≠0 ∧ x.norm.toNat=m*normI I}
abbrev InverseClass {n : ℕ} {v : Triple} (hv : v∈shell n) (I : Ideal (R n)) (m : ℕ) :=
  {B : NormIdeals n m // homothetic v (image hv (conjugate I)) (image hv B.val)}
variable {n m : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n)
  {I : Ideal (R n)} (hI : I≠⊥)
def gen (b : InverseClass hv I m) : R n := ((inverse_class_iff hn h2 hv hI).mp b.property).choose
lemma gen_spec (b : InverseClass hv I m) :
    gen hn h2 hv hI b≠0 ∧ b.val.val*I=principal (gen hn h2 hv hI b) :=
  ((inverse_class_iff hn h2 hv hI).mp b.property).choose_spec
def mkRep (b : InverseClass hv I m) : Representations I m := ⟨gen hn h2 hv hI b,by
  obtain ⟨h₀,he⟩ := gen_spec hn h2 hv hI b
  refine ⟨Ideal.mul_le_right (I:=b.val.val) (J:=I) (he.symm ▸ Ideal.mem_span_singleton_self _),h₀,?_⟩
  rw [←normI_principal hn h2 h₀,←he,normI_mul hn h2 b.val.property.1 hI,show normI b.val.val=m from b.val.property.2]⟩
def repNeg (x : Representations I m) : Representations I m :=
  ⟨-x.val,I.neg_mem x.property.1,neg_ne_zero.mpr x.property.2.1,by simpa only [Zsqrtd.norm_neg] using x.property.2.2⟩
def pick (s : Bool) (b : InverseClass hv I m) : Representations I m :=
  if s then mkRep hn h2 hv hI b else repNeg (mkRep hn h2 hv hI b)
lemma pick_principal (s : Bool) (b : InverseClass hv I m) :
    principal (pick hn h2 hv hI s b).val=b.val.val*I := by
  have he := (gen_spec hn h2 hv hI b).2.symm
  cases s
  · exact (Ideal.span_singleton_neg _).trans he
  · exact he
def repIdeal (x : Representations I m) : InverseClass hv I m := by
  have he := divide_mul hn h2 hI x.property.1
  have hB : divide I x.val≠⊥ := by
    intro e; rw [e,Ideal.bot_mul] at he
    have h : x.val∈principal x.val := Ideal.mem_span_singleton_self _
    rw [←he] at h
    exact x.property.2.1 h
  have hnorm : normI (divide I x.val)*normI I=m*normI I := by
    rw [←normI_mul hn h2 hB hI,he,normI_principal hn h2 x.property.2.1,x.property.2.2]
  exact ⟨⟨divide I x.val,hB,Nat.mul_right_cancel (normI_positive (by omega) I hI) hnorm⟩,
    (inverse_class_iff hn h2 hv hI).mpr ⟨_,x.property.2.1,he⟩⟩
lemma neg_ne_self {x : R n} (hx : x≠0) : -x≠x := by
  intro e; apply hx; apply Zsqrtd.ext
  · have h := congrArg Zsqrtd.re e; change -x.re=x.re at h; change x.re=0; omega
  · have h := congrArg Zsqrtd.im e; change -x.im=x.im at h; change x.im=0; omega
def repEquiv : Bool × InverseClass hv I m ≃ Representations I m := by
  let f (t : Bool × InverseClass hv I m) := pick hn h2 hv hI t.1 t.2
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · rintro ⟨s,b⟩ ⟨s',b'⟩ h
    have he := congrArg (fun x : Representations I m => principal x.val) h
    change principal (pick hn h2 hv hI s b).val=principal (pick hn h2 hv hI s' b').val at he
    rw [pick_principal,pick_principal] at he
    have eb : b=b' := Subtype.ext (Subtype.ext (mul_right_cancel_ideal hn h2 hI he))
    subst b'
    have ex := congrArg Subtype.val h
    obtain hs | hs := Bool.dichotomy s
    all_goals obtain hs' | hs' := Bool.dichotomy s'
    all_goals subst s; subst s'
    · rfl
    · exact False.elim (neg_ne_self (gen_spec hn h2 hv hI b).1 ex)
    · exact False.elim (neg_ne_self (gen_spec hn h2 hv hI b).1 ex.symm)
    · rfl
  · intro x
    let b := repIdeal hn h2 hv hI x
    have he : principal (gen hn h2 hv hI b)=principal x.val :=
      (gen_spec hn h2 hv hI b).2.symm.trans (divide_mul hn h2 hI x.property.1)
    rcases generator_sign (by omega) he with h|h
    · exact ⟨(true,b),Subtype.ext h.symm⟩
    · exact ⟨(false,b),Subtype.ext h.symm⟩
include hn h2 hI in
theorem classwise_count : Nat.card (Representations I m)=2*Nat.card (InverseClass hv I m) := by
  rw [←Nat.card_congr (repEquiv hn h2 hv hI),Nat.card_prod]
  simp
end
end TunnellIdealGenerators
end


/- TunnellClassThetaCount -/
section
namespace TunnellClassThetaCount
open TunnellHurwitz TunnellToricLocal TunnellToric TunnellIdealHNF TunnellShell TunnellToricClass TunnellEmbeddedIdeals TunnellIdealGenerators
noncomputable section
variable {n m : ℕ} {v : Triple} (hn : Squarefree n) (h2 : n%4=2) (hv : v∈shell n)
def liftClass (c : ProperIdealClass v) : Ideal (R n) := conjugate (preimage hv c.out)
def classOf (B : NormIdeals n m) : ProperIdealClass v :=
  Quotient.mk _ (integralEquiv hn h2 hv ⟨B.val,B.property.1⟩)
lemma conj_invol (I : Ideal (R n)) : conjugate (conjugate I)=I := by
  ext x; simp only [mem_conjugate,star_star]
lemma conj_ne_bot {I : Ideal (R n)} (hI : I≠⊥) : conjugate I≠⊥ := by
  intro h; apply hI; rw [←conj_invol I,h]; ext t; simp [mem_conjugate]
include hn h2 in
lemma lift_ne_bot (c : ProperIdealClass v) : liftClass hv c≠⊥ :=
  conj_ne_bot (preimage_ne_bot hn h2 hv c.out)
lemma fiber_iff (c : ProperIdealClass v) (B : NormIdeals n m) :
    homothetic v (image hv (conjugate (liftClass hv c))) (image hv B.val) ↔ classOf hn h2 hv B=c := by
  rw [liftClass,conj_invol,image_preimage hn h2 hv]
  calc
    _ ↔ Quotient.mk (idealSetoid v) c.out=classOf hn h2 hv B := Quotient.eq.symm
    _ ↔ _ := by rw [Quotient.out_eq,eq_comm]
def fiberEquiv (c : ProperIdealClass v) :
    InverseClass hv (liftClass hv c) m ≃ {B : NormIdeals n m // classOf hn h2 hv B=c} :=
  Equiv.subtypeEquivRight (fiber_iff hn h2 hv c)
theorem total_count (hm : 0 < m) :
    letI := Fintype.ofEquiv ↥(representatives n) (idealEquiv hn h2 hv).symm
    (∑ c : ProperIdealClass v, Nat.card (Representations (liftClass hv c) m))=2*Nat.card (NormIdeals n m) := by
  classical
  letI := Fintype.ofEquiv ↥(representatives n) (idealEquiv hn h2 hv).symm
  letI : Fintype (NormIdeals n m) := Fintype.ofEquiv (finiteRoot n m) ((divisorEquiv hm).symm.trans (indexedEquiv (by omega)))
  calc
    _=∑ c : ProperIdealClass v, 2*Nat.card {B : NormIdeals n m // classOf hn h2 hv B=c} := by
      apply Finset.sum_congr rfl
      intro c _
      rw [classwise_count hn h2 hv (lift_ne_bot hn h2 hv c),Nat.card_congr (fiberEquiv hn h2 hv c)]
    _=_ := by
      rw [←Finset.mul_sum,←Nat.card_sigma,Nat.card_congr (Equiv.sigmaFiberEquiv (classOf hn h2 hv : NormIdeals n m → _))]
end
end TunnellClassThetaCount
end


/- TunnellIdealTheta -/
section
namespace TunnellIdealTheta
open Complex Finset Real
open scoped Classical
noncomputable section
def shift (u z : ℂ) : ℂ := Complex.exp (π*I*u^2*z)*jacobiTheta₂ (u*z) z
lemma shift_hasSum (u z : ℂ) (hz : 0 < z.im) :
    HasSum (fun k : ℤ => Complex.exp (π*I*((k:ℂ)+u)^2*z)) (shift u z) := by
  apply ((hasSum_jacobiTheta₂_term (u*z) hz).mul_left _).congr_fun
  intro k
  rw [jacobiTheta₂_term,←Complex.exp_add]
  congr 1
  ring
def theta (n a : ℕ) [NeZero a] (b : ℤ) (z : ℂ) : ℂ :=
  ∑ r : ZMod a, shift ((b:ℂ)*r.val/a) (2*a*z)*shift ((r.val:ℂ)/a) (2*n*a*z)
def term (n a : ℕ) (z : ℂ) (uv : ℤ×ℤ) : ℂ :=
  Complex.exp (2*π*I*z*((n:ℂ)*(uv.1:ℂ)^2+(uv.2:ℂ)^2)/a)
def admitted (a : ℕ) (b : ℤ) (uv : ℤ×ℤ) : Prop :=
  (uv.2:ZMod a)=(b:ZMod a)*(uv.1:ZMod a)
private lemma product_sum {f g : ℤ→ℂ} {A B : ℂ} (hf : HasSum f A) (hg : HasSum g B) :
    HasSum (fun v : ℤ×ℤ => f v.1*g v.2) (A*B) :=
  hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)
private lemma refine_residue {a : ℕ} [NeZero a] (r u : ℤ)
    (h : (u:ZMod a)=(r:ZMod a)) : ∃ k:ℤ, (a:ℤ)*k+r=u := by
  obtain ⟨k,hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub r u a).mp h.symm
  exact ⟨k,by omega⟩
theorem theta_hasSum (n a : ℕ) [NeZero n] [NeZero a] (b : ℤ) {z : ℂ} (hz : 0 < z.im) :
    HasSum (fun uv : ℤ×ℤ => if admitted a b uv then term n a z uv else 0) (theta n a b z) := by
  classical
  have ha : (a:ℂ)≠0 := by exact_mod_cast NeZero.ne a
  have hap : (0:ℝ)<a := Nat.cast_pos.mpr (NeZero.pos a)
  have hnp : (0:ℝ)<n := Nat.cast_pos.mpr (NeZero.pos n)
  let cls (r : ZMod a) (uv : ℤ×ℤ) := if (uv.1:ZMod a)=r ∧ (uv.2:ZMod a)=(b:ZMod a)*r then term n a z uv else 0
  have hsum (r : ZMod a) : HasSum (cls r) (shift ((b:ℂ)*r.val/a) (2*a*z)*shift ((r.val:ℂ)/a) (2*n*a*z)) := by
    let e (v : ℤ×ℤ) : ℤ×ℤ := (a*v.2+r.val,a*v.1+b*r.val)
    have hi : Function.Injective e := by
      rintro ⟨x,y⟩ ⟨x',y'⟩ h
      have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      dsimp only [e] at h1 h2
      have hac : (a:ℤ)≠0 := by exact_mod_cast NeZero.ne a
      exact Prod.ext (mul_left_cancel₀ hac (add_right_cancel h2)) (mul_left_cancel₀ hac (add_right_cancel h1))
    apply (hi.hasSum_iff ?_).mp
    · have H := product_sum (shift_hasSum ((b:ℂ)*r.val/a) (2*a*z)
          (by simpa [Complex.mul_im] using (show (0:ℝ)<2*a*z.im by positivity)))
        (shift_hasSum ((r.val:ℂ)/a) (2*n*a*z)
          (by simpa [Complex.mul_im] using (show (0:ℝ)<2*n*a*z.im by positivity)))
      apply H.congr_fun
      rintro ⟨x,y⟩
      simp only [Function.comp_apply,e,cls,Int.cast_add,Int.cast_mul,Int.cast_natCast,
        ZMod.natCast_self,zero_mul,zero_add,ZMod.natCast_zmod_val,and_self,ite_true]
      simp only [term,Int.cast_add,Int.cast_mul,Int.cast_natCast,←Complex.exp_add]
      congr 1
      field_simp
      ring
    · rintro ⟨u,v⟩ h
      unfold cls
      split_ifs with hc
      · exfalso; apply h
        obtain ⟨y,hy⟩ := refine_residue (a:=a) r.val u (by simpa using hc.1)
        obtain ⟨x,hx⟩ := refine_residue (a:=a) (b*r.val) v (by simpa using hc.2)
        exact ⟨(x,y),Prod.ext hy hx⟩
      · rfl
  apply (hasSum_sum (s:=univ) (fun r _ => hsum r)).congr_fun
  rintro ⟨u,v⟩
  dsimp only [cls,admitted]
  rw [sum_eq_single (u:ZMod a)]
  · by_cases h : (v:ZMod a)=(b:ZMod a)*(u:ZMod a) <;> simp [h]
  · intro s _ h; simp [Ne.symm h]
  · simp
end
end TunnellIdealTheta
end


/- TunnellIdealThetaExpansion -/
section
namespace TunnellIdealThetaExpansion
open TunnellIdealGenerators TunnellIdealHNF TunnellIdealTheta TunnellClassThetaCount
open TunnellShell TunnellToricClass TunnellToric Complex
open scoped Classical
noncomputable section
variable {n : ℕ}
def normTerm (I : Ideal (R n)) (z : ℂ) (x : I) :=
  Complex.exp (2*Real.pi*Complex.I*z*((x.val.norm:ℤ):ℂ)/normI I)
lemma admit_iff (s : Data n) (u : ℤ×ℤ) :
    admitted s.a (s.b:ℤ) u ↔ (s.a:ℤ)∣u.2-s.b*u.1 := by
  unfold admitted
  rw [← Int.cast_mul, ZMod.intCast_eq_intCast_iff_dvd_sub,dvd_sub_comm]
def point (s : Data n) (u : ℤ×ℤ) : R n := ⟨(s.c:ℤ)*u.2,(s.c:ℤ)*u.1⟩
lemma point_mem (s : Data n) {u : ℤ×ℤ} (hu : admitted s.a (s.b:ℤ) u) : point s u∈ideal s := by
  obtain ⟨t,ht⟩ := (admit_iff s u).mp hu
  refine (mem_ideal s _).mpr ⟨⟨u.1,rfl⟩,⟨t,?_⟩⟩
  dsimp only [point]; linear_combination s.c*ht
def pointEquiv (s : Data n) : {u : ℤ×ℤ // admitted s.a (s.b:ℤ) u} ≃ ideal s := by
  let f (u : {u : ℤ×ℤ // admitted s.a (s.b:ℤ) u}) : ideal s := ⟨point s u.val,point_mem s u.property⟩
  refine Equiv.ofBijective f ⟨?_,?_⟩
  · intro a b e
    have e₁ := congrArg (fun t : ideal s => t.val.re) e
    have e₂ := congrArg (fun t : ideal s => t.val.im) e
    have hc : (s.c:ℤ)≠0 := by exact_mod_cast s.pos_c.ne'
    exact Subtype.ext (Prod.ext (mul_left_cancel₀ hc e₂) (mul_left_cancel₀ hc e₁))
  · rintro ⟨x,hx⟩
    obtain ⟨u,v,e⟩ := basis_expansion s hx
    refine ⟨⟨(v,s.a*u+s.b*v),(admit_iff s _).mpr ⟨u,by dsimp only; ring⟩⟩,Subtype.ext ?_⟩
    exact e.symm
lemma point_term (s : Data n) (z : ℂ) (u : {u : ℤ×ℤ // admitted s.a (s.b:ℤ) u}) :
    normTerm (ideal s) z (pointEquiv s u)=term n s.a z u.val := by
  have hc : (s.c:ℂ)≠0 := by exact_mod_cast s.pos_c.ne'
  have ha : (s.a:ℂ)≠0 := by exact_mod_cast s.pos_a.ne'
  rw [normTerm,term,normI,quotient_card]
  change Complex.exp (_ * (((s.c:ℤ)*u.val.2*((s.c:ℤ)*u.val.2) - -(n:ℤ)*((s.c:ℤ)*u.val.1)*((s.c:ℤ)*u.val.1):ℤ) : ℂ)/ _) = _
  congr 1
  push_cast
  field_simp
  ring
theorem hnf_hasSum (s : Data n) (hn : 0<n) {z : ℂ} (hz : 0<z.im) :
    letI : NeZero s.a := ⟨s.pos_a.ne'⟩
    HasSum (normTerm (ideal s) z) (theta n s.a s.b z) := by
  letI : NeZero s.a := ⟨s.pos_a.ne'⟩
  letI : NeZero n := ⟨hn.ne'⟩
  have h := theta_hasSum n s.a (s.b:ℤ) hz
  apply (pointEquiv s).hasSum_iff.mp
  apply HasSum.congr_fun _ (fun u => point_term s z u)
  apply (hasSum_subtype_iff_indicator (f:=term n s.a z) (s:={u : ℤ×ℤ | admitted s.a (s.b:ℤ) u})).mpr
  exact h
def valence {I : Ideal (R n)} (x : I) := x.val.norm.toNat/normI I
lemma norm_valence (hn : Squarefree n) (h2 : n%4=2) {I : Ideal (R n)} (hI : I≠⊥) (x : I) :
    x.val.norm.toNat=valence x*normI I := by
  have hpos := normI_positive (by omega) I hI
  by_cases hx : x.val=0
  · simp [valence,hx,Zsqrtd.norm_zero]
  · have he := divide_mul hn h2 hI x.property
    have hB : divide I x.val≠⊥ := by
      intro e; rw [e,Ideal.bot_mul] at he
      have H : x.val∈principal x.val := Ideal.mem_span_singleton_self _
      rw [←he] at H
      exact hx H
    have eq : x.val.norm.toNat=normI (divide I x.val)*normI I := by
      rw [←normI_principal hn h2 hx,←he,normI_mul hn h2 hB hI]
    simp [valence,eq,Nat.mul_div_cancel _ hpos]
end
end TunnellIdealThetaExpansion
end


/- TunnellRankinUnfold -/
section
namespace TunnellRankin
open Complex Set Function ModularForm TunnellCMLSeries MeasureTheory AddCircle
open UpperHalfPlane hiding I
open scoped ComplexConjugate
noncomputable def theta (d : ℕ) (z : ℍ) : ℂ :=
  ∑' m : ℕ,(idealCoeff d m:ℂ)*Periodic.qParam 1 z^m
end TunnellRankin
end


/- TunnellClassThetaExpansion -/
section
namespace TunnellClassThetaExpansion
open TunnellIdealGenerators TunnellIdealHNF TunnellIdealTheta TunnellClassThetaCount TunnellIdealThetaExpansion
open TunnellShell TunnellToricClass TunnellToric Complex
open scoped Classical
noncomputable section
variable {n : ℕ} {I : Ideal (R n)} (hn : Squarefree n) (h2 : n%4=2) (hI : I≠⊥)
def thetaI (I : Ideal (R n)) (z : ℂ) : ℂ := ∑' x : I, normTerm I z x
lemma thetaI_hasSum (hn' : 0<n) (hI : I≠⊥) {z : ℂ} (hz : 0<z.im) :
    HasSum (normTerm I z) (thetaI I z) := by
  obtain ⟨s,rfl⟩ := normal_form hn' hI
  exact (hnf_hasSum s hn' hz).summable.hasSum
include hn h2 hI in
lemma valence_zero (x : I) : valence x=0 ↔ x.val=0 := by
  constructor
  · intro h; by_contra e
    have eq := norm_valence hn h2 hI x
    rw [h,zero_mul] at eq
    have H := positive_norm (by omega) e
    omega
  · intro h; simp [valence,h,Zsqrtd.norm_zero]
def finiteRep (m : ℕ) (hm : 0 < m) {v : Triple} (hv : v∈shell n) : Finite (Representations I m) := by
  letI := Fintype.ofEquiv (finiteRoot n m) ((divisorEquiv hm).symm.trans (indexedEquiv (by omega)))
  exact Finite.of_equiv _ (repEquiv hn h2 hv hI)
def fiberRep {m : ℕ} (hm : 0 < m) : {x : I // valence x=m} ≃ Representations I m where
  toFun u := ⟨u.val.val,u.val.property,fun e => hm.ne' (u.property.symm.trans ((valence_zero hn h2 hI _).mpr e)),
    (norm_valence hn h2 hI u.val).trans (by rw [u.property])⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,by
    change x.val.norm.toNat/normI I=m
    rw [x.property.2.2,Nat.mul_div_cancel _ (normI_positive (by omega) I hI)]⟩
  left_inv _ := rfl
  right_inv _ := rfl
def fiberZero : {x : I // valence x=0} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨0,(valence_zero hn h2 hI _).mpr rfl⟩
  left_inv x := Subtype.ext (Subtype.ext (((valence_zero hn h2 hI x.val).mp x.property).symm))
  right_inv _ := rfl
def thetaCoeff (I : Ideal (R n)) (m : ℕ) := if m=0 then 1 else Nat.card (Representations I m)
include hn h2 hI in
lemma normTerm_fiber {m : ℕ} {z : ℂ} (x : {x : I // valence x=m}) :
    normTerm I z x.val = (Function.Periodic.qParam 1 z)^m := by
  have H := norm_valence hn h2 hI x.val
  rw [x.property] at H
  have e : x.val.val.norm=(m:ℤ)*normI I := by
    have H' : (x.val.val.norm.toNat:ℤ)=(m:ℤ)*normI I := by exact_mod_cast H
    rwa [Int.toNat_of_nonneg (Zsqrtd.norm_nonneg (by omega) _)] at H'
  have hN : (normI I:ℂ)≠0 := by exact_mod_cast (normI_positive (by omega) I hI).ne'
  rw [normTerm,e,Function.Periodic.qParam,←Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp <;> ring
include hn h2 hI in
theorem thetaI_expansion {v : Triple} (hv : v∈shell n) {z : ℂ} (hz : 0<z.im) :
    HasSum (fun m : ℕ => (thetaCoeff I m:ℂ)*(Function.Periodic.qParam 1 z)^m) (thetaI I z) := by
  have H := ((Equiv.sigmaFiberEquiv (@valence n I)).hasSum_iff).mpr (thetaI_hasSum (by omega) hI hz)
  apply H.sigma
  intro m
  let F := {x : I // valence x=m}
  have Hf : Finite F := by
    by_cases hm : m=0
    · subst m; exact Finite.of_equiv Unit (fiberZero hn h2 hI).symm
    · letI := finiteRep hn h2 hI m (Nat.pos_of_ne_zero hm) hv
      exact Finite.of_equiv _ (fiberRep hn h2 hI (Nat.pos_of_ne_zero hm)).symm
  letI := Fintype.ofFinite F
  have hc : Nat.card F=thetaCoeff I m := by
    by_cases hm : m=0
    · subst m; rw [Nat.card_congr (fiberZero hn h2 hI)]; simp [thetaCoeff]
    · simpa [thetaCoeff,hm] using Nat.card_congr (fiberRep hn h2 hI (Nat.pos_of_ne_zero hm))
  have hfin := hasSum_fintype (fun _ : F => (Function.Periodic.qParam 1 z)^m)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card,hc] at hfin
  exact hfin.congr_fun (fun x => normTerm_fiber hn h2 hI x)
end
end TunnellClassThetaExpansion
end


/- TunnellFullClassTheta -/
section
namespace TunnellFullClassTheta
open TunnellShell TunnellToricClass TunnellToric TunnellClassThetaCount TunnellClassThetaExpansion
open TunnellRankin TunnellIdealHNF Complex Finset
open scoped Classical UpperHalfPlane
noncomputable section
variable {d : ℕ} {v : Triple} (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hv : v∈shell (2*d))
def classFintype : Fintype (ProperIdealClass v) := Fintype.ofEquiv ↥(representatives (2*d)) (idealEquiv hn h2 hv).symm
def full (z : ℍ) : ℂ := by
  letI := classFintype hn h2 hv
  exact ∑ c : ProperIdealClass v, thetaI (liftClass hv c) z
theorem full_expansion (z : ℍ) : letI := classFintype hn h2 hv
    full hn h2 hv z= (Fintype.card (ProperIdealClass v):ℂ)+2*TunnellRankin.theta d z := by
  classical
  letI := classFintype hn h2 hv
  let q := Function.Periodic.qParam 1 (z:ℂ)
  let h : ℂ := Fintype.card (ProperIdealClass v)
  have H := hasSum_sum (s:=univ) (fun (c : ProperIdealClass v) _ => thetaI_expansion hn h2 (lift_ne_bot hn h2 hv c) hv z.im_pos)
  have H' : HasSum (fun m : ℕ => (if m=0 then h else 2*(idealCoeff d m:ℂ))*q^m) (full hn h2 hv z) := by
    apply H.congr_fun
    intro m
    change (if m=0 then h else 2*(idealCoeff d m:ℂ))*q^m = ∑ c : ProperIdealClass v, (thetaCoeff (liftClass hv c) m:ℂ)*q^m
    rw [←sum_mul]; congr 1
    by_cases hm : m=0
    · subst m; simp [h,thetaCoeff]
    · rw [if_neg hm,rankin_ideal_count d m hn (Nat.pos_of_ne_zero hm)]
      simp only [thetaCoeff,hm,if_false,←Nat.cast_sum,Int.cast_natCast]
      exact_mod_cast (total_count hn h2 hv (Nat.pos_of_ne_zero hm)).symm
  have h0 : HasSum (fun m : ℕ => if m=0 then h else 0) h := by simpa using (hasSum_ite_eq (0:ℕ) h)
  have A : HasSum (fun m : ℕ => 2*((idealCoeff d m:ℂ)*q^m)) (full hn h2 hv z-h) := by
    apply (H'.sub h0).congr_fun
    intro m; by_cases hm : m=0
    · subst m; simp [idealCoeff]
    · simp [hm,mul_assoc]
  have e := A.tsum_eq
  rw [tsum_mul_left] at e
  change 2*TunnellRankin.theta d z=full hn h2 hv z-h at e
  change _=h+_
  linear_combination -e
end
end TunnellFullClassTheta
end


/- TunnellFrameNorm -/
section
namespace TunnellFrameNorm
open TunnellIdealHNF TunnellHurwitz TunnellToricClass TunnellShell TunnellEmbeddedIdeals TunnellToricLocal
open TunnellIdealThetaExpansion
noncomputable section
lemma norm_embed {n : ℕ} {v : Triple} (hv : v∈shell n) (x : R n) :
    Quaternion.normSq (embed n v hv x)=(x.norm:ℚ) := by
  have H := TunnellShell.mem_shell.mp hv
  have h : (v.1:ℚ)^2+v.2.1^2+v.2.2^2=(n:ℚ) := by exact_mod_cast H
  rw [Quaternion.normSq_def']
  change (x.re:ℚ)^2+((x.im:ℚ)*v.1)^2+((x.im:ℚ)*v.2.1)^2+((x.im:ℚ)*v.2.2)^2=((x.re*x.re- -(n:ℤ)*x.im*x.im:ℤ):ℚ)
  push_cast
  linear_combination (x.im:ℚ)^2*h
lemma ideal_norm_gcd {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {I : Ideal (R n)} (hI : I≠⊥)
    (g : ℤ) (h : ∀ x∈I, g∣Zsqrtd.norm x) : g∣(normI I:ℤ) := by
  obtain ⟨s,rfl⟩ := normal_form (by omega) hI
  obtain ⟨C,hC⟩ := s.divides
  obtain ⟨A,B,D,e⟩ := primitive_coeffs hn h2 s hC
  let N : ℤ := (s.c:ℤ)^2*s.a
  let u : R n := ⟨s.c*s.a,0⟩
  let t : R n := ⟨s.c*s.b,s.c⟩
  have hu : u∈ideal s := real_basis s
  have ht : t∈ideal s := lift_basis s
  have h₁ : u.norm=N*s.a := by dsimp [u,N,Zsqrtd.norm]; ring
  have h₂ : t.norm=N*C := by dsimp [t,N,Zsqrtd.norm]; linear_combination (s.c:ℤ)^2*hC
  have h₃ : (u+t).norm-u.norm-t.norm=N*(2*s.b) := by dsimp [t,u,N,Zsqrtd.norm]; ring
  have ha := h u hu
  have hc := h t ht
  have hb := dvd_sub (dvd_sub (h _ ((ideal s).add_mem hu ht)) ha) hc
  rw [h₁] at ha; rw [h₂] at hc; rw [h₃] at hb
  obtain ⟨a,ha⟩ := ha; obtain ⟨b,hb⟩ := hb; obtain ⟨c,hc⟩ := hc
  refine ⟨a*A+b*B+c*D,?_⟩
  rw [normI,quotient_card]; push_cast
  change N=_
  linear_combination -N*e+A*ha+B*hb+D*hc
theorem frame_norm {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {v w : Triple} (hv : v∈shell n) (hw : w∈shell n)
    {I : Ideal (R n)} (hI : I≠⊥) {a : Q} (ha : a∈J w v) (e : image hv I=line a*J v w) :
    Quaternion.normSq a=(normI I:ℚ) := by
  obtain ⟨g,hg⟩ := norm_int ha.1
  have hgN : (g:ℤ)∣(normI I:ℤ) := by
    apply ideal_norm_gcd hn h2 hI
    intro x hx
    have hm : embed n v hv x∈line a*J v w := e ▸ ⟨x,hx,rfl⟩
    obtain ⟨q,hq,eq⟩ := Submodule.mem_span_singleton_mul.mp hm
    obtain ⟨k,hk⟩ := norm_int (show q∈J v w from hq).1
    have E := congrArg Quaternion.normSq eq
    rw [map_mul,hg,hk,norm_embed hv] at E
    exact ⟨k,by exact_mod_cast E.symm⟩
  have hNg : (normI I:ℤ)∣(g:ℤ) := by
    let S : Ideal ℤ := (Ideal.span {(normI I:ℤ)}).colon {(g:ℤ)}
    have hle : Ideal.span (norms v w)≤S := by
      apply Ideal.span_le.mpr
      rintro k ⟨q,hq,hk⟩
      obtain ⟨x,hx,eq⟩ := (mem_image hv).mp (e.symm ▸ Submodule.mem_span_singleton_mul.mpr ⟨q,hq,rfl⟩ : a*q∈image hv I)
      have E := congrArg Quaternion.normSq eq
      rw [norm_embed,map_mul,hg,hk] at E
      have hZ : x.norm=(g:ℤ)*k := by exact_mod_cast E
      have H := norm_valence hn h2 hI (⟨x,hx⟩:I)
      change x.norm.toNat=_ at H
      have hcast : x.norm=((valence (⟨x,hx⟩:I):ℕ):ℤ)*normI I := by
        rw [←Int.toNat_of_nonneg (Zsqrtd.norm_nonneg (by omega) x)]
        exact_mod_cast H
      apply Submodule.mem_colon_singleton.mpr
      apply Ideal.mem_span_singleton.mpr
      exact ⟨_,(mul_comm _ _).trans (hZ.symm.trans (hcast.trans (mul_comm _ _)))⟩
    rw [norm_ideal_top hn h2 v w hv hw] at hle
    have H : (1:ℤ)∈S := hle (Submodule.mem_top)
    have H' := Ideal.mem_span_singleton.mp (Submodule.mem_colon_singleton.mp H)
    simpa using H'
  rw [hg]
  exact_mod_cast Nat.dvd_antisymm (Int.natCast_dvd_natCast.mp hgN) (Int.natCast_dvd_natCast.mp hNg)
end
end TunnellFrameNorm
end


/- TunnellIntertwinerTheta -/
section
namespace TunnellIntertwinerTheta
open TunnellIdealHNF TunnellHurwitz TunnellToricClass TunnellShell TunnellEmbeddedIdeals TunnellToricLocal
open TunnellClassThetaExpansion TunnellIdealThetaExpansion TunnellClassThetaCount TunnellToric TunnellFrameNorm
open scoped Classical UpperHalfPlane
noncomputable section
variable {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {v w : Triple} (hv : v∈shell n) (hw : w∈shell n)
  {I : Ideal (R n)} (hI : I≠⊥) {a : Q} (ha : a∈J w v) (h0 : a≠0) (e : image hv I=line a*J v w)
def frameEquiv : I ≃ J v w := by
  let f (x : I) : J v w := ⟨a⁻¹*(embed n v hv x.val),by
    have h : embed n v hv x.val∈line a*J v w := e ▸ ⟨_,x.property,rfl⟩
    obtain ⟨q,hq,he⟩ := Submodule.mem_span_singleton_mul.mp h
    rw [←he,←mul_assoc,inv_mul_cancel₀ h0,one_mul]; exact hq⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    exact Subtype.ext (embed_inj hn hv (mul_left_cancel₀ (inv_ne_zero h0) (congrArg Subtype.val h)))
  · rintro ⟨q,hq⟩
    obtain ⟨x,hx,ex⟩ := (mem_image hv).mp (e.symm ▸ Submodule.mem_span_singleton_mul.mpr ⟨q,hq,rfl⟩ : a*q∈image hv I)
    refine ⟨⟨x,hx⟩,Subtype.ext ?_⟩
    change a⁻¹*(embed n v hv x)=q; rw [ex,←mul_assoc,inv_mul_cancel₀ h0,one_mul]
def jterm (z : ℂ) (q : Q) := Complex.exp (2*Real.pi*Complex.I*z*((Quaternion.normSq q:ℚ):ℂ))
def jtheta (v w : Triple) (z : ℂ) := ∑' q : J v w, jterm z q.val
include hn hv h2 hw hI ha h0 e in
theorem frame_theta (z : ℂ) : thetaI I z=jtheta v w z := by
  have hN := frame_norm hn h2 hv hw hI ha e
  have hN' : (normI I:ℂ)≠0 := by exact_mod_cast (normI_positive (by omega) I hI).ne'
  let E := frameEquiv hn hv h0 e
  rw [jtheta,←E.tsum_eq (fun q => jterm z q.val),thetaI]
  apply tsum_congr
  intro x
  have he : a*(E x).val=embed n v hv x.val := by
    change a*(a⁻¹*_)=_; rw [←mul_assoc,mul_inv_cancel₀ h0,one_mul]
  have hnorm := congrArg Quaternion.normSq he
  rw [map_mul,norm_embed hv,hN] at hnorm
  have hh : (normI I:ℂ)*((Quaternion.normSq (E x).val:ℚ):ℂ)=(x.val.norm:ℂ) := by exact_mod_cast hnorm
  rw [normTerm,jterm,←hh]; congr 1; field_simp
lemma conj_norm {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {I : Ideal (R n)} (hI : I≠⊥) :
    normI (conjugate I)=normI I := by
  apply principal_injective_nat (n:=n)
  rw [←norm_conjugate hn h2 _ (conj_ne_bot hI),conj_invol, mul_comm, norm_conjugate hn h2 I hI]
def conjEquiv (I : Ideal (R n)) : (conjugate I) ≃ I where
  toFun x := ⟨star x.val,x.property⟩
  invFun x := ⟨star x.val,conj_mem _ x.property⟩
  left_inv x := Subtype.ext (star_star _)
  right_inv x := Subtype.ext (star_star _)
include hn h2 hI in
lemma conj_theta (z : ℂ) : thetaI (conjugate I) z=thetaI I z := by
  rw [thetaI,thetaI,←(conjEquiv I).tsum_eq (normTerm I z)]
  apply tsum_congr
  intro x
  simp only [normTerm,conj_norm hn h2 hI,conjEquiv,Equiv.coe_fn_mk,Zsqrtd.norm_conj]
theorem full_by_embeddings {d : ℕ} (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {v : Triple} (hv : v∈shell (2*d)) (z : ℍ) :
    TunnellFullClassTheta.full hn h2 hv z=∑ w : ↥(representatives (2*d)), jtheta v w.val z := by
  letI := TunnellFullClassTheta.classFintype hn h2 hv
  let E := idealEquiv hn h2 hv
  rw [TunnellFullClassTheta.full,← E.sum_comp (fun w => jtheta v w.val z)]
  apply Finset.sum_congr rfl
  intro c _
  have hc : E c=representative hn h2 hv c.out := by
    conv_lhs => rw [←Quotient.out_eq c]
    rfl
  rw [hc,liftClass,conj_theta hn h2 (preimage_ne_bot hn h2 hv c.out)]
  obtain ⟨a,ha,h0,e⟩ := representative_frame hn h2 hv c.out
  exact frame_theta hn h2 hv (Finset.mem_filter.mp (representative hn h2 hv c.out).property).1 (preimage_ne_bot hn h2 hv c.out) ha h0
    ((image_preimage hn h2 hv c.out).trans e) z
end
end TunnellIntertwinerTheta
end


/- TunnellCMGluing -/
section
namespace TunnellCMGluing
open TunnellHurwitz TunnellToricClass TunnellShell
abbrev R (v : Triple) := J v v
def anti (v : Triple) : Lattice :=
  LinearMap.ker ((AddMonoidHom.mulLeft ((TunnellHurwitz.pure) v)).toIntLinearMap+(AddMonoidHom.mulRight ((TunnellHurwitz.pure) v)).toIntLinearMap)
lemma mem_anti {v : Triple} {a : Q} : a∈anti v ↔ (TunnellHurwitz.pure) v*a= -(a*(TunnellHurwitz.pure) v) := add_eq_zero_iff_eq_neg
lemma C_anti (v : Triple) : C v*anti v ≤ anti v := by
  apply Submodule.mul_le.mpr; intro a ha b hb; apply mem_anti.mpr
  rw [←mul_assoc,mem_C.mp ha,mul_assoc,mem_anti.mp hb,mul_neg,mul_assoc]
lemma anti_C (v : Triple) : anti v*C v ≤ anti v := by
  apply Submodule.mul_le.mpr; intro a ha b hb; apply mem_anti.mpr
  rw [←mul_assoc,mem_anti.mp ha,neg_mul,mul_assoc,mem_C.mp hb,mul_assoc]
lemma ROR (v : Triple) : R v*O*R v≤O := by
  have hr : R v≤O := fun _ h => h.1
  calc R v*O*R v ≤ O*O*O := mul_le_mul' (mul_le_mul_left hr _) hr
       _ = O := by rw [mul_O,mul_O]
 

lemma transport {v : Triple} {A A' B B' W : Lattice}
    (hA : A≤C v) (hA' : A'≤C v) (hB : B≤C v) (hB' : B'≤C v)
    (h₁ : A*A'=R v) (h₂ : A'*A=R v) (h₃ : B*B'=R v) (h₄ : B'*B=R v)
    (hLW : C v*W≤W) (hWR : W*C v≤W) :
    A*O*B ⊓ W=A*(O ⊓ W)*B := by
  let D := A*O*B ⊓ W
  have hU (X Y : Lattice) (hX : X≤C v) (hY : Y≤C v) (P : Lattice) (hP : P≤W) : X*P*Y≤W :=
    (mul_le_mul' ((mul_le_mul' hX hP).trans hLW) hY).trans hWR
  have hT : A'*D*B'≤O ⊓ W := by
    refine le_inf ?_ (hU _ _ hA' hB' D inf_le_right)
    calc A'*D*B' ≤ A'*(A*O*B)*B' := mul_le_mul_left (mul_le_mul_right inf_le_left _) _
         _ = (A'*A)*O*(B*B') := by simp only [mul_assoc]
         _ ≤ O := by rw [h₂,h₃]; exact ROR v
  have hR : (1:Lattice)≤R v := Submodule.one_le.mpr (one_J v)
  apply le_antisymm
  · calc D = 1*D*1 := by rw [one_mul,mul_one]
         _ ≤ R v*D*R v := mul_le_mul' (mul_le_mul_left hR _) hR
         _ = A*(A'*D*B')*B := by calc R v*D*R v=(A*A')*D*(B'*B) := congrArg₂ (·*·) (congrArg (·*D) h₁.symm) h₄.symm
                       _=_ := by simp only [mul_assoc]
         _ ≤ A*(O ⊓ W)*B := mul_le_mul_left (mul_le_mul_right hT _) _
  · exact le_inf (mul_le_mul_left (mul_le_mul_right inf_le_left _) _) (hU _ _ hA hB _ inf_le_right)
lemma anti_order (v : Triple) : O ⊓ anti v = J v (-v) := by
  have he : (TunnellHurwitz.pure) (-v)= -(TunnellHurwitz.pure) v := by apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg] <;> simp [TunnellHurwitz.pure]
  ext x
  simp only [Submodule.mem_inf,mem_anti,mem_J,he,neg_mul,neg_eq_iff_eq_neg]
lemma inter_components {v : Triple} {A A' B B' : Lattice}
    (hA : A≤C v) (hA' : A'≤C v) (hB : B≤C v) (hB' : B'≤C v)
    (h₁ : A*A'=R v) (h₂ : A'*A=R v) (h₃ : B*B'=R v) (h₄ : B'*B=R v) (hs : A*R v=A) :
    A*O*B ⊓ C v=A*B ∧ A*O*B ⊓ anti v=A*J v (-v)*B := by
  constructor
  · rw [transport hA hA' hB hB' h₁ h₂ h₃ h₄ (mul_C v) (mul_C v),order_commutant,hs]
  · rw [transport hA hA' hB hB' h₁ h₂ h₃ h₄ (C_anti v) (anti_C v),anti_order]
lemma integral_projectors {n : ℕ} {v : Triple} (hv : v∈shell n) {D : Lattice}
    (hD : R v*D*R v≤D) {x : Q} (hx : x∈D) :
    ∃ l∈D ⊓ C v, ∃ r∈D ⊓ anti v, ((2*n:ℕ):Q)*x=l+r := by
  let V := (TunnellHurwitz.pure) v
  have hV : V∈R v := ⟨pure_mem v,rfl⟩
  have ht : V*x*V∈D := hD (Submodule.mul_mem_mul (Submodule.mul_mem_mul hV hx) hV)
  have hnx : (n:Q)*x∈D := by simpa only [zsmul_eq_mul,Int.cast_natCast] using D.smul_mem (n:ℤ) hx
  have hsq : V*V= -(n:Q) := pure_square hv
  have L : V*(V*x*V)= -((n:Q)*x*V) := by rw [←mul_assoc,←mul_assoc,hsq,neg_mul,neg_mul]
  have R : (V*x*V)*V= -((n:Q)*V*x) := by rw [mul_assoc (V*x),hsq,mul_neg,←Nat.cast_comm n (V*x),←mul_assoc]
  have hl : V*((n:Q)*x)=(n:Q)*V*x := by rw [←mul_assoc,Nat.commute_cast]
  refine ⟨(n:Q)*x-V*x*V,⟨D.sub_mem hnx ht,mem_C.mpr ?_⟩,(n:Q)*x+V*x*V,⟨D.add_mem hnx ht,mem_anti.mpr ?_⟩,?_⟩
  · change V*(_-_) = (_-_)*V; rw [mul_sub,sub_mul,L,R,hl]; abel
  · change V*(_+_) = -(( _+_)*V); rw [mul_add,add_mul,L,R,hl]; abel
  · push_cast; noncomm_ring
end TunnellCMGluing
end


/- TunnellProperClassGroup -/
section
namespace TunnellProperClassGroup
open TunnellIdealHNF TunnellIdealGenerators TunnellClassThetaCount TunnellToricClass TunnellShell TunnellEmbeddedIdeals TunnellHurwitz
noncomputable section
variable {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {v : Triple} (hv : v∈shell n)
def cls {I : Ideal (R n)} (hI : I≠⊥) : ProperIdealClass v :=
  Quotient.mk _ (integralEquiv hn h2 hv ⟨I,hI⟩)
lemma cls_congr {I B : Ideal (R n)} {hI : I≠⊥} {hB : B≠⊥} (e : I=B) : cls hn h2 hv hI=cls hn h2 hv hB := by cases e; rfl
lemma cls_eq {I B : Ideal (R n)} (hI : I≠⊥) (hB : B≠⊥) :
    cls hn h2 hv hI=cls hn h2 hv hB ↔ homothetic v (image hv I) (image hv B) := Quotient.eq
lemma exists_rep (c : ProperIdealClass v) : ∃ (I : Ideal (R n)) (hI : I≠⊥), cls hn h2 hv hI=c := by
  refine ⟨preimage hv c.out,preimage_ne_bot hn h2 hv c.out,?_⟩
  calc _=Quotient.mk (idealSetoid v) c.out := congrArg (Quotient.mk (idealSetoid v)) (Subtype.ext (image_preimage hn h2 hv c.out))
       _=_ := Quotient.out_eq _
def mulI (A B : IntegralIdeal v) : IntegralIdeal v :=
  integralEquiv hn h2 hv ⟨preimage hv A*preimage hv B,mul_ne_bot (by omega) (preimage_ne_bot hn h2 hv A) (preimage_ne_bot hn h2 hv B)⟩
lemma val_mulI (A B : IntegralIdeal v) : (mulI hn h2 hv A B).val=A.val*B.val := by
  change image hv (preimage hv A*preimage hv B)=_
  rw [image_mul,image_preimage hn h2 hv A,image_preimage hn h2 hv B]
def mul : ProperIdealClass v → ProperIdealClass v → ProperIdealClass v :=
  Quotient.map₂ (mulI hn h2 hv) (by
    rintro A A' ⟨s,hs,hs₀,e⟩ B B' ⟨t,ht,ht₀,e'⟩
    change homothetic v (mulI hn h2 hv A B).val (mulI hn h2 hv A' B').val
    rw [val_mulI,val_mulI,←e,←e']
    refine ⟨s*t,(mul_C v) (Submodule.mul_mem_mul hs ht),mul_ne_zero hs₀ ht₀,?_⟩
    have ht' : line t≤C v := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ht)
    calc line (s*t)*(A.val*B.val)=line s*(line t*A.val)*B.val := by rw [←line_mul]; simp only [mul_assoc]
         _= _ := by rw [ideals_comm hn hv ht' A.property.2.1]; simp only [mul_assoc])
lemma cls_mul {I B : Ideal (R n)} (hI : I≠⊥) (hB : B≠⊥) :
    mul hn h2 hv (cls hn h2 hv hI) (cls hn h2 hv hB)=cls hn h2 hv (mul_ne_bot (by omega) hI hB) := by
  apply congrArg (Quotient.mk (idealSetoid v)); apply Subtype.ext
  rw [val_mulI]
  exact (image_mul hv I B).symm
def one : ProperIdealClass v := cls hn h2 hv (I:=⊤) top_ne_bot
lemma cls_principal {x : R n} (hx : x≠0) (hi : principal x≠⊥) : cls hn h2 hv hi=one hn h2 hv := by
  symm; apply (cls_eq ..).mpr
  refine ⟨embed n v hv x,center_image hv (principal x) ⟨x,Ideal.mem_span_singleton_self _,rfl⟩,?_,?_⟩
  · exact fun h => hx (embed_inj hn hv (h.trans (map_zero _).symm))
  · rw [principal,image_principal hn h2 hv,image_order hn h2 hv]
def inv (c : ProperIdealClass v) : ProperIdealClass v := cls hn h2 hv (conj_ne_bot (preimage_ne_bot hn h2 hv c.out))
lemma inv_mul (c : ProperIdealClass v) : mul hn h2 hv (inv hn h2 hv c) c=one hn h2 hv := by
  let A := preimage hv c.out
  have hA : A≠⊥ := preimage_ne_bot hn h2 hv c.out
  have e : cls hn h2 hv hA=c := by
    calc _ = Quotient.mk (idealSetoid v) c.out := congrArg _ (Subtype.ext (image_preimage hn h2 hv c.out))
         _ = _ := Quotient.out_eq _
  change mul hn h2 hv (cls hn h2 hv (conj_ne_bot hA)) c=_
  rw [←e,cls_mul]
  have hN : (normI A:R n)≠0 := Nat.cast_ne_zero.mpr (normI_positive (by omega) A hA).ne'
  have he : conjugate A*A=principal (normI A:R n) := (mul_comm ..).trans (norm_conjugate hn h2 A hA)
  have hi : principal (normI A:R n)≠⊥ := he ▸ mul_ne_bot (by omega) (conj_ne_bot hA) hA
  exact (cls_congr hn h2 hv he).trans (cls_principal hn h2 hv hN hi)
def group : CommGroup (ProperIdealClass v) where
  mul := mul hn h2 hv
  one := one hn h2 hv
  inv := inv hn h2 hv
  mul_assoc := by
    intro a b c
    change mul hn h2 hv (mul hn h2 hv a b) c=mul hn h2 hv a (mul hn h2 hv b c)
    obtain ⟨A,hA,rfl⟩ := exists_rep hn h2 hv a
    obtain ⟨B,hB,rfl⟩ := exists_rep hn h2 hv b
    obtain ⟨C,hC,rfl⟩ := exists_rep hn h2 hv c
    simp only [cls_mul]; exact cls_congr _ _ _ (mul_assoc ..)
  one_mul := by
    intro a; obtain ⟨A,hA,rfl⟩ := exists_rep hn h2 hv a
    change mul hn h2 hv (one hn h2 hv) (cls hn h2 hv hA)=_
    rw [one,cls_mul]; exact cls_congr _ _ _ (Ideal.top_mul _)
  mul_one := by
    intro a; obtain ⟨A,hA,rfl⟩ := exists_rep hn h2 hv a
    change mul hn h2 hv (cls hn h2 hv hA) (one hn h2 hv)=_
    rw [one,cls_mul]; exact cls_congr _ _ _ (Ideal.mul_top _)
  mul_comm := by
    intro a b
    change mul hn h2 hv a b=mul hn h2 hv b a
    obtain ⟨A,hA,rfl⟩ := exists_rep hn h2 hv a
    obtain ⟨B,hB,rfl⟩ := exists_rep hn h2 hv b
    simp only [cls_mul]; exact cls_congr _ _ _ (mul_comm ..)
  inv_mul_cancel := inv_mul hn h2 hv
end
end TunnellProperClassGroup
end


/- TunnellAmbiguousClass -/
section
namespace TunnellAmbiguousClass
open TunnellIdealHNF TunnellIdealGenerators TunnellClassThetaCount TunnellToricClass TunnellShell TunnellEmbeddedIdeals TunnellHurwitz TunnellProperClassGroup
noncomputable section
variable {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {v : Triple} (hv : v∈shell n)
lemma nonzero_principal {x : R n} (hx : x≠0) : principal x≠⊥ := by
  intro h; have e : x∈principal x := Ideal.mem_span_singleton_self _; rw [h] at e; exact hx e
include hn h2 in
lemma cross_mult {I B : Ideal (R n)} (hI : I≠⊥) (h : homothetic v (image hv I) (image hv B)) :
    ∃ m : ℕ, 0 < m ∧ ∃ x : R n, x≠0 ∧ principal x*I=principal (m:R n)*B := by
  obtain ⟨c,_,hc,e⟩ := h
  obtain ⟨m,hm,hM⟩ := int_pos_mem (by omega) I hI
  have hm' : (m:Q)≠0 := by intro h; have H:=congrArg QuaternionAlgebra.re h; change (m:ℚ)=0 at H; exact hm.ne' (by exact_mod_cast H)
  have hq : c*(m:Q)∈image hv B := by
    rw [←e]; exact Submodule.mem_span_singleton_mul.mpr ⟨_,⟨(m:R n),hM,map_natCast (embed n v hv) m⟩,rfl⟩
  obtain ⟨x,_,eq⟩ := (mem_image hv).mp hq
  refine ⟨m,hm,x,fun H => (mul_ne_zero hc hm') (by simpa [H] using eq.symm),image_injective hn hv ?_⟩
  rw [image_principal_mul hn h2 hv,image_principal_mul hn h2 hv,map_natCast,eq,←e,←mul_assoc,line_mul,Nat.cast_comm]
lemma scalar_class {I : Ideal (R n)} (hI : I≠⊥) {z : R n} (hz : z≠0) :
    cls hn h2 hv (mul_ne_bot (by omega) (nonzero_principal hz) hI)=cls hn h2 hv hI := by
  symm; apply (cls_eq ..).mpr
  refine ⟨embed n v hv z,center_image hv (principal z) ⟨z,Ideal.mem_span_singleton_self _,rfl⟩,?_,?_⟩
  · exact fun e => hz (embed_inj hn hv (e.trans (map_zero _).symm))
  · exact (image_principal_mul hn h2 hv z I).symm
theorem stable_rep {I : Ideal (R n)} (hI : I≠⊥)
    (h : cls hn h2 hv hI=cls hn h2 hv (conj_ne_bot hI)) :
    ∃ (B : Ideal (R n)) (hB : B≠⊥), conjugate B=B ∧ cls hn h2 hv hB=cls hn h2 hv hI := by
  obtain ⟨m,hm,x,hx,e⟩ := cross_mult hn h2 hv hI ((cls_eq ..).mp h)
  letI := domain (show 0<n by omega)
  have hm' : (m:R n)≠0 := Nat.cast_ne_zero.mpr hm.ne'
  have hN := congrArg normI e
  rw [normI_mul hn h2 (nonzero_principal hx) hI,normI_mul hn h2 (nonzero_principal hm') (conj_ne_bot hI),
    TunnellIntertwinerTheta.conj_norm hn h2 hI,normI_principal hn h2 hx,normI_principal hn h2 hm'] at hN
  have h' := Nat.mul_right_cancel (normI_positive (by omega) I hI) hN
  have hnorm : x.norm=((m:R n)).norm := by
    have h₁ := positive_norm (by omega) hx; have h₂ := positive_norm (by omega) hm'; omega
  have he : star x*x=(m:R n)*m := by
    rw [mul_comm (star x),←Zsqrtd.norm_eq_mul_conj,hnorm,Zsqrtd.norm_eq_mul_conj,star_natCast]
  by_cases hx' : x= -(m:R n)
  · rw [hx',principal,Ideal.span_singleton_neg] at e
    refine ⟨I,hI,?_,rfl⟩; exact ((Ideal.span_singleton_mul_right_inj hm').mp e).symm
  · let z : R n := x+m
    have hz : z≠0 := by simpa [z,add_eq_zero_iff_eq_neg] using hx'
    have hh : star z*x=(m:R n)*z := by rw [show star z=star x+m by simp [z],add_mul,he]; dsimp [z]; ring
    let B := principal z*I
    refine ⟨B,mul_ne_bot (by omega) (nonzero_principal hz) hI,?_,scalar_class hn h2 hv hI hz⟩
    apply (Ideal.span_singleton_mul_right_inj hm').mp
    change principal (m:R n)*conjugate (principal z*I)=principal (m:R n)*(principal z*I)
    calc _=principal (star z)*(principal (m:R n)*conjugate I) := by rw [conjugate_mul,principal_star]; ac_rfl
         _=principal (star z*x)*I := by rw [←e,principal_mul,mul_assoc]
         _=_ := by rw [hh,principal_mul,mul_assoc]
theorem stable_hnf {n : ℕ} (h2 : n%4=2) (s : Data n) (h : conjugate (ideal s)=ideal s) :
    s.b=0 ∧ s.a∣n := by
  have H := conj_mem _ (lift_basis s)
  rw [h] at H
  obtain ⟨k,hk⟩ := ((mem_ideal s _).mp H).2
  change (s.c:ℤ)*s.b-s.b*(-(s.c:ℤ))=s.c*s.a*k at hk
  have hc : (s.c:ℤ)≠0 := by exact_mod_cast s.pos_c.ne'
  have e : (2:ℤ)*s.b=s.a*k := mul_left_cancel₀ hc (by linear_combination hk)
  have hpos : (0:ℤ)<s.a := by exact_mod_cast s.pos_a
  have hlt : (s.b:ℤ)<s.a := by exact_mod_cast s.lt_b
  have hk0 : 0≤k := nonneg_of_mul_nonneg_right (by rw [←e]; positivity) hpos
  have hk2 : k<2 := by by_contra! hh; nlinarith [mul_le_mul_of_nonneg_left hh hpos.le]
  obtain ⟨C,hC⟩ := s.divides
  have hb : s.b=0 := by
    rcases (show k=0 ∨ k=1 by omega) with rfl|rfl
    · simp at e; exact e
    · simp only [mul_one] at e
      have hc := congrArg (fun x:ℤ => (x:ZMod 4)) hC
      push_cast at hc
      have hn4 : (n:ZMod 4)=2 := by apply ZMod.val_injective 4; rw [ZMod.val_natCast,h2]; decide
      have he' := congrArg (fun x:ℤ => (x:ZMod 4)) e
      push_cast at he'
      rw [hn4,←he'] at hc
      exact False.elim ((show ∀ x y:ZMod 4, x^2+2≠2*x*y by decide) _ _ hc)
  refine ⟨hb,Int.natCast_dvd_natCast.mp ⟨C,?_⟩⟩
  simpa [hb] using hC
end
end TunnellAmbiguousClass
end


/- TunnellGenusCharacter -/
section
namespace TunnellGenusCharacter
open TunnellIdealHNF TunnellIdealGenerators TunnellClassThetaCount TunnellToricClass TunnellShell TunnellEmbeddedIdeals
open TunnellFrameNorm TunnellProperClassGroup TunnellIdealThetaExpansion TunnellAmbiguousClass
noncomputable section
variable {n p : ℕ} [hpFact : Fact p.Prime] (hn : Squarefree n) (h2 : n%4=2)
include hn h2 in
lemma norm_valZ {I : Ideal (R n)} (hI : I≠⊥) (x : I) : x.val.norm=(valence x:ℤ)*normI I := by
  have h : (x.val.norm.toNat:ℤ)=(valence x:ℤ)*normI I := by exact_mod_cast norm_valence hn h2 hI x
  rwa [Int.toNat_of_nonneg (Zsqrtd.norm_nonneg (by omega) x.val)] at h
include hn h2 hpFact in
lemma good_exists {I : Ideal (R n)} (hI : I≠⊥) : ∃ x:I, (valence x:(ZMod p))≠0 := by
  by_contra! e
  have hNI := normI_positive (by omega) I hI
  have H := ideal_norm_gcd hn h2 hI ((p:ℤ)*normI I) (by
    intro x hx; let t : I := ⟨x,hx⟩
    obtain ⟨k,hk⟩ := (ZMod.natCast_eq_zero_iff (valence t) p).mp (e t)
    refine ⟨k,?_⟩
    have H := norm_valZ hn h2 hI t
    change x.norm=_ at H
    rw [H,hk,Nat.cast_mul]; ring)
  have e' : p*normI I∣normI I := Int.natCast_dvd_natCast.mp (by simpa using H)
  have hp := (Fact.out : p.Prime).one_lt
  exact (Nat.not_lt_of_ge (Nat.le_of_dvd hNI e')) (by nlinarith)
def good {I : Ideal (R n)} (hI : I≠⊥) : I := (good_exists (p:=p) hn h2 hI).choose
lemma good_nonzero {I : Ideal (R n)} (hI : I≠⊥) : (valence (good (p:=p) hn h2 hI):(ZMod p))≠0 := (good_exists hn h2 hI).choose_spec
def charI {I : Ideal (R n)} (hI : I≠⊥) := (quadraticChar (ZMod p)) (valence (good (p:=p) hn h2 hI):(ZMod p))
lemma norm_square (hp : p∣n) (x : R n) : (x.norm:(ZMod p))=(x.re:(ZMod p))^2 := by
  have h := (ZMod.natCast_eq_zero_iff n p).mpr hp
  change ((x.re*x.re- -(n:ℤ)*x.im*x.im:ℤ):(ZMod p))=_
  push_cast; rw [h]; ring
include hn h2 in
lemma independent (hp : p∣n) {I : Ideal (R n)} (hI : I≠⊥) (x y : I) (hx : (valence x:(ZMod p))≠0) (hy : (valence y:(ZMod p))≠0) :
    (quadraticChar (ZMod p)) (valence x:(ZMod p))=(quadraticChar (ZMod p)) (valence y:(ZMod p)) := by
  have hxy := Ideal.mul_mem_mul x.property (conj_mem I y.property)
  rw [norm_conjugate hn h2 I hI] at hxy
  obtain ⟨z,hz⟩ := Ideal.mem_span_singleton.mp hxy
  have H := congrArg Zsqrtd.norm hz
  simp only [Zsqrtd.norm_mul,Zsqrtd.norm_conj] at H
  have hN : ((normI I:R n)).norm=(normI I:ℤ)^2 := by
    change (normI I:ℤ)*normI I- -(n:ℤ)*0*0=_; ring
  rw [norm_valZ hn h2 hI x,norm_valZ hn h2 hI y,hN] at H
  have hn0 : (normI I:ℤ)≠0 := by exact_mod_cast (normI_positive (by omega) I hI).ne'
  have eq : (valence x:ℤ)*valence y=z.norm := mul_left_cancel₀ (pow_ne_zero 2 hn0) (by linear_combination H)
  have e : (valence x:(ZMod p))*(valence y:(ZMod p))=(z.re:(ZMod p))^2 := by
    rw [←norm_square hp z]; exact_mod_cast congrArg (fun w:ℤ => (w:(ZMod p))) eq
  have hc : (quadraticChar (ZMod p)) (valence x:(ZMod p))*(quadraticChar (ZMod p)) (valence y:(ZMod p))=1 := by
    rw [←map_mul,e,quadraticChar_sq_one' (fun he => (mul_ne_zero hx hy) (by simpa [he] using e))]
  rcases quadraticChar_dichotomy hx with h|h <;> rcases quadraticChar_dichotomy hy with h'|h' <;> rw [h,h'] at hc ⊢ <;> norm_num at *
lemma charI_eq (hp : p∣n) {I : Ideal (R n)} (hI : I≠⊥) (x : I) (hx : (valence x:(ZMod p))≠0) :
    charI (p:=p) hn h2 hI=(quadraticChar (ZMod p)) (valence x:(ZMod p)) := independent hn h2 hp hI _ _ (good_nonzero hn h2 hI) hx
include hn h2 in
lemma val_mul {A B : Ideal (R n)} (hA : A≠⊥) (hB : B≠⊥) (x : A) (y : B) :
    valence (⟨x.val*y.val,Ideal.mul_mem_mul x.property y.property⟩:A*B)=valence x*valence y := by
  let z : A*B := ⟨x.val*y.val,Ideal.mul_mem_mul x.property y.property⟩
  have hz := norm_valZ hn h2 (mul_ne_bot (by omega) hA hB) z
  change (x.val*y.val).norm=_ at hz
  rw [Zsqrtd.norm_mul,norm_valZ hn h2 hA x,norm_valZ hn h2 hB y,normI_mul hn h2 hA hB,Nat.cast_mul] at hz
  have hN : (normI A:ℤ)*normI B≠0 := by exact_mod_cast (mul_ne_zero (normI_positive (by omega) A hA).ne' (normI_positive (by omega) B hB).ne')
  exact_mod_cast (show (valence z:ℤ)=(valence x:ℤ)*valence y from mul_right_cancel₀ hN (by linear_combination -hz))
lemma charI_mul (hp : p∣n) {A B : Ideal (R n)} (hA : A≠⊥) (hB : B≠⊥) :
    charI (p:=p) hn h2 (mul_ne_bot (by omega) hA hB)=charI (p:=p) hn h2 hA*charI (p:=p) hn h2 hB := by
  let x := good (p:=p) hn h2 hA
  let y := good (p:=p) hn h2 hB
  let z : A*B := ⟨x.val*y.val,Ideal.mul_mem_mul x.property y.property⟩
  have H : (valence z:(ZMod p))=(valence x:(ZMod p))*(valence y:(ZMod p)) := by rw [←Nat.cast_mul]; exact congrArg (fun k:ℕ => (k:(ZMod p))) (val_mul hn h2 hA hB x y)
  rw [charI_eq hn h2 hp _ z (H ▸ mul_ne_zero (good_nonzero hn h2 hA) (good_nonzero hn h2 hB)),H,map_mul]
  rfl
lemma charI_principal (hp : p∣n) {x : R n} (hx : x≠0) :
    charI (p:=p) hn h2 (nonzero_principal hx)=1 := by
  let z : principal x := ⟨x,Ideal.mem_span_singleton_self _⟩
  have hz : valence z=1 := by
    change x.norm.toNat/normI (principal x)=1
    rw [←normI_principal hn h2 hx,Nat.div_self (normI_positive (by omega) _ (nonzero_principal hx))]
  rw [charI_eq hn h2 hp _ z (by rw [hz,Nat.cast_one]; exact one_ne_zero),hz,Nat.cast_one,map_one]
lemma charI_congr {v : Triple} (hv : v∈shell n) (hp : p∣n) {A B : Ideal (R n)} (hA : A≠⊥) (hB : B≠⊥)
    (h : cls hn h2 hv hA=cls hn h2 hv hB) : charI (p:=p) hn h2 hA=charI (p:=p) hn h2 hB := by
  obtain ⟨m,hm,x,hx,e⟩ := cross_mult hn h2 hv hA ((cls_eq ..).mp h)
  have hM : (m:R n)≠0 := Nat.cast_ne_zero.mpr hm.ne'
  have he : charI (p:=p) hn h2 (mul_ne_bot (by omega) (nonzero_principal hx) hA)=
      charI (p:=p) hn h2 (mul_ne_bot (by omega) (nonzero_principal hM) hB) := by
    have eq {P Q : Ideal (R n)} {hP:P≠⊥} {hQ:Q≠⊥} (H : P=Q) : charI (p:=p) hn h2 hP=charI (p:=p) hn h2 hQ := by cases H; rfl
    exact eq e
  have H := (charI_mul (p:=p) hn h2 hp (nonzero_principal hx) hA).symm.trans (he.trans (charI_mul hn h2 hp (nonzero_principal hM) hB))
  simpa only [charI_principal hn h2 hp hx,charI_principal hn h2 hp hM,one_mul] using H
end
end TunnellGenusCharacter
end


/- TunnellSelling -/
section
namespace TunnellSelling
structure W where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
abbrev V := ℤ × ℤ × ℤ × ℤ
def energy (p : W) (u : V) : ℤ :=
  let (x,y,z,t) := u
  p.a*(x-y)^2+p.b*(x-z)^2+p.c*(x-t)^2+p.d*(y-z)^2+p.e*(y-t)^2+p.f*(z-t)^2
def mass (p : W) := p.a+p.b+p.c+p.d+p.e+p.f
def det (p : W) : ℤ :=
  p.a*p.b*p.c+p.a*p.b*p.e+p.a*p.b*p.f+p.a*p.c*p.d
  +p.a*p.c*p.f+p.a*p.d*p.e+p.a*p.d*p.f+p.a*p.e*p.f
  +p.b*p.c*p.d+p.b*p.c*p.e+p.b*p.d*p.e+p.b*p.d*p.f
  +p.b*p.e*p.f+p.c*p.d*p.e+p.c*p.d*p.f+p.c*p.e*p.f
def psd (p : W) : Prop := ∀ u, 0≤energy p u
lemma mass_nonneg {p : W} (h : psd p) : 0≤ mass p := by
  obtain ⟨a,b,c,d,e,f⟩ := p
  have A := h (1,0,0,0); have B := h (0,1,0,0); have C := h (0,0,1,0); have D := h (0,0,0,1)
  norm_num [energy,mass] at *
  omega
def swapW (i : Fin 6) (p : W) : W :=
  ![⟨p.a,p.b,p.c,p.d,p.e,p.f⟩,
    ⟨p.b,p.a,p.c,p.d,p.f,p.e⟩,
    ⟨p.c,p.b,p.a,p.f,p.e,p.d⟩,
    ⟨p.d,p.b,p.f,p.a,p.e,p.c⟩,
    ⟨p.e,p.f,p.c,p.d,p.a,p.b⟩,
    ⟨p.f,p.b,p.d,p.c,p.e,p.a⟩] i
def swapV (i : Fin 6) (u : V) : V :=
  let (x,y,z,t) := u
  ![(x,y,z,t), (x,z,y,t), (x,t,z,y), (z,y,x,t), (t,y,z,x), (z,t,x,y)] i
lemma swap_energy (i : Fin 6) (p : W) (u : V) : energy (swapW i p) (swapV i u)=energy p u := by
  obtain ⟨a,b,c,d,e,f⟩ := p
  obtain ⟨x,y,z,t⟩ := u
  fin_cases i <;> dsimp [swapW,swapV,energy] <;> ring
lemma swap_vv (i : Fin 6) (u : V) : swapV i (swapV i u)=u := by
  obtain ⟨x,y,z,t⟩ := u; fin_cases i <;> rfl
lemma swap_det (i : Fin 6) (p : W) : det (swapW i p)=det p := by
  obtain ⟨a,b,c,d,e,f⟩ := p; fin_cases i <;> dsimp [det,swapW] <;> ring
lemma swap_mass (i : Fin 6) (p : W) : mass (swapW i p)=mass p := by
  obtain ⟨a,b,c,d,e,f⟩ := p; fin_cases i <;> dsimp [mass,swapW] <;> ring
def reduceW (p : W) : W := ⟨-p.a,p.a+p.c,p.a+p.b,p.d+p.a,p.e+p.a,p.f-p.a⟩
def reduceV (u : V) : V := (u.2.2.1+u.2.2.2-u.1,u.2.1,u.2.2.1,u.2.2.2)
lemma reduce_energy (p : W) (u : V) : energy (reduceW p) (reduceV u) = energy p u := by
  obtain ⟨a,b,c,d,e,f⟩ := p; obtain ⟨x,y,z,t⟩ := u; dsimp [energy,reduceW,reduceV]; ring
lemma reduce_vv (u : V) : reduceV (reduceV u)=u := by
  obtain ⟨x,y,z,t⟩ := u; simp [reduceV]
lemma reduce_det (p : W) : det (reduceW p)=det p := by
  obtain ⟨a,b,c,d,e,f⟩ := p; dsimp [det,reduceW]; ring
lemma reduce_mass (p : W) : mass (reduceW p)=mass p+p.a := by dsimp [mass,reduceW]; ring
def nonnegative (p : W) := 0≤p.a ∧ 0≤p.b ∧ 0≤p.c ∧ 0≤p.d ∧ 0≤p.e ∧ 0≤p.f
lemma reduce_to_nonnegative {p : W} (hp : psd p) (hd : det p=1) {N : ℤ} (u : V) (hu : energy p u=N) :
    ∃ q, nonnegative q ∧ det q=1 ∧ ∃ t, energy q t=N := by
  classical
  let P (m : ℕ) := ∃ q, psd q ∧ det q=1 ∧ (∃ t, energy q t=N) ∧ mass q=(m:ℤ)
  have he : ∃ m, P m := ⟨(mass p).toNat,p,hp,hd,⟨u,hu⟩,(Int.toNat_of_nonneg (mass_nonneg hp)).symm⟩
  obtain ⟨q,hq,hdet,⟨t,ht⟩,hm⟩ := Nat.find_spec he
  refine ⟨q,?_,hdet,t,ht⟩
  have good (i : Fin 6) : 0≤(swapW i q).a := by
    by_contra! hn
    let r := swapW i q
    have h₁ : psd r := fun x => by
      have e := swap_energy i q (swapV i x); rw [swap_vv] at e
      rw [show energy r x=_ from e]; exact hq _
    have h₂ : psd (reduceW r) := fun x => by
      have e := reduce_energy r (reduceV x); rw [reduce_vv] at e
      rw [e]; exact h₁ _
    have hr : P (mass (reduceW r)).toNat := ⟨reduceW r,h₂,(reduce_det r).trans ((swap_det i q).trans hdet),
      ⟨reduceV (swapV i t),(reduce_energy r _).trans ((swap_energy i q t).trans ht)⟩,
      (Int.toNat_of_nonneg (mass_nonneg h₂)).symm⟩
    have hmin := Nat.find_min' he hr
    have hmass := reduce_mass r
    have heq : mass r=mass q := swap_mass i q
    change r.a<0 at hn
    have hcast : (Nat.find he:ℤ) ≤ ((mass (reduceW r)).toNat:ℤ) := by exact_mod_cast hmin
    have hnon := mass_nonneg h₂
    omega
  exact ⟨good 0,good 1,good 2,good 3,good 4,good 5⟩
lemma triple_one {a b c : ℤ} (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (h : a*b*c=1) :
    a=1 ∧ b=1 ∧ c=1 := by
  have e₁ := Int.eq_one_or_neg_one_of_mul_eq_one (show a*(b*c)=1 by simpa [mul_assoc] using h)
  have e₂ := Int.eq_one_or_neg_one_of_mul_eq_one (show b*(a*c)=1 by simpa [mul_assoc,mul_left_comm,mul_comm] using h)
  have e₃ := Int.eq_one_or_neg_one_of_mul_eq_one (show c*(a*b)=1 by simpa [mul_assoc,mul_left_comm,mul_comm] using h)
  omega
lemma three_sq {p : W} (h : nonnegative p) (hd : det p=1) (u : V) :
    ∃ x y z : ℤ, energy p u=x^2+y^2+z^2 := by
  obtain ⟨a,b,c,d,e,f⟩ := p
  obtain ⟨ha,hb,hc,hd',he,hf⟩ := h
  dsimp only at ha hb hc hd' he hf
  dsimp only [det] at hd
  obtain ⟨w,x,y,z⟩ := u
  have t0 := mul_nonneg (mul_nonneg ha hb) hc
  have t1 := mul_nonneg (mul_nonneg ha hb) he
  have t2 := mul_nonneg (mul_nonneg ha hb) hf
  have t3 := mul_nonneg (mul_nonneg ha hc) hd'
  have t4 := mul_nonneg (mul_nonneg ha hc) hf
  have t5 := mul_nonneg (mul_nonneg ha hd') he
  have t6 := mul_nonneg (mul_nonneg ha hd') hf
  have t7 := mul_nonneg (mul_nonneg ha he) hf
  have t8 := mul_nonneg (mul_nonneg hb hc) hd'
  have t9 := mul_nonneg (mul_nonneg hb hc) he
  have t10 := mul_nonneg (mul_nonneg hb hd') he
  have t11 := mul_nonneg (mul_nonneg hb hd') hf
  have t12 := mul_nonneg (mul_nonneg hb he) hf
  have t13 := mul_nonneg (mul_nonneg hc hd') he
  have t14 := mul_nonneg (mul_nonneg hc hd') hf
  have t15 := mul_nonneg (mul_nonneg hc he) hf
  have hone : a*b*c=1 ∨ a*b*e=1 ∨ a*b*f=1 ∨ a*c*d=1 ∨ a*c*f=1 ∨ a*d*e=1 ∨ a*d*f=1 ∨ a*e*f=1 ∨ b*c*d=1 ∨ b*c*e=1 ∨ b*d*e=1 ∨ b*d*f=1 ∨ b*e*f=1 ∨ c*d*e=1 ∨ c*d*f=1 ∨ c*e*f=1 := by omega
  rcases hone with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h
  · have z0 : a*c*d=0 := by omega
    have z1 : a*b*e=0 := by omega
    have z2 : a*b*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha hb hc h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,w-y,w-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*c=0 := by omega
    have z1 : a*d*e=0 := by omega
    have z2 : a*b*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha hb he h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,w-y,x-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*c=0 := by omega
    have z1 : a*d*f=0 := by omega
    have z2 : a*b*e=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha hb hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,w-y,y-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*c=0 := by omega
    have z1 : a*d*e=0 := by omega
    have z2 : a*c*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha hc hd' h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,w-z,x-y,by dsimp [energy]; ring⟩
  · have z0 : a*b*c=0 := by omega
    have z1 : a*c*d=0 := by omega
    have z2 : a*e*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha hc hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,w-z,y-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*e=0 := by omega
    have z1 : a*c*d=0 := by omega
    have z2 : a*d*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha hd' he h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,x-y,x-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*f=0 := by omega
    have z1 : a*c*d=0 := by omega
    have z2 : a*d*e=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha hd' hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,x-y,y-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*e=0 := by omega
    have z1 : a*c*f=0 := by omega
    have z2 : a*d*e=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one ha he hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-x,x-z,y-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*c=0 := by omega
    have z1 : b*c*e=0 := by omega
    have z2 : b*d*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hb hc hd' h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-y,w-z,x-y,by dsimp [energy]; ring⟩
  · have z0 : a*b*c=0 := by omega
    have z1 : b*c*d=0 := by omega
    have z2 : b*e*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hb hc he h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-y,w-z,x-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*e=0 := by omega
    have z1 : b*c*d=0 := by omega
    have z2 : b*d*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hb hd' he h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-y,x-y,x-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*f=0 := by omega
    have z1 : b*c*d=0 := by omega
    have z2 : b*d*e=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hb hd' hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-y,x-y,y-z,by dsimp [energy]; ring⟩
  · have z0 : a*b*e=0 := by omega
    have z1 : b*c*e=0 := by omega
    have z2 : b*d*e=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hb he hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-y,x-z,y-z,by dsimp [energy]; ring⟩
  · have z0 : a*c*d=0 := by omega
    have z1 : b*c*d=0 := by omega
    have z2 : c*d*f=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hc hd' he h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-z,x-y,x-z,by dsimp [energy]; ring⟩
  · have z0 : a*c*d=0 := by omega
    have z1 : b*c*d=0 := by omega
    have z2 : c*d*e=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hc hd' hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-z,x-y,y-z,by dsimp [energy]; ring⟩
  · have z0 : a*c*f=0 := by omega
    have z1 : b*c*e=0 := by omega
    have z2 : c*d*e=0 := by omega
    obtain ⟨rfl,rfl,rfl⟩ := triple_one hc he hf h
    simp only [mul_one,one_mul] at z0 z1 z2
    subst_vars
    exact ⟨w-z,x-z,y-z,by dsimp [energy]; ring⟩
theorem three_squares {p : W} (hp : psd p) (hd : det p=1) (u : V) :
    ∃ x y z : ℤ, energy p u=x^2+y^2+z^2 := by
  obtain ⟨q,hq,hd',w,he⟩ := reduce_to_nonnegative hp hd u rfl
  exact he ▸ three_sq hq hd' w
end TunnellSelling
end


/- TunnellThreeSquares -/
section
namespace TunnellThreeSquares
open TunnellSelling TunnellShell
 
lemma auxiliary_prime (d : ℕ) (hd : d%4=1) :
    ∃ p b A C : ℤ, 0<p ∧ A*(2*d)=p+1 ∧ p*C=b^2+2*d := by
  have hpos : 0<d := by omega
  let a : ℤ := 2*d-1
  have hbez : IsCoprime a (8*d:ℤ) := by
    refine ⟨a,-(((d:ℤ)-1)/2),?_⟩
    have he : ((d:ℤ)-1)/2*2=(d:ℤ)-1 := by omega
    dsimp [a]
    linear_combination -4*(d:ℤ)*he
  obtain ⟨p,hpgt,hp,hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq (8*d) (q:=8*d) (a:=a) (by omega) (by simpa using hbez)
  letI : Fact p.Prime := ⟨hp⟩
  have hmd : (p:ℤ) ≡ -1 [ZMOD (d:ℤ)] := by
    apply (hmod.of_dvd (by exact_mod_cast (dvd_mul_left d 8))).trans
    apply Int.modEq_iff_dvd.mpr
    exact ⟨-2,by dsimp [a]; ring⟩
  have h8 : p%8=1 := by
    have he : (p:ℤ) ≡ a [ZMOD 8] := hmod.of_dvd (by exact_mod_cast (dvd_mul_right 8 d))
    change (p:ℤ)%8=a%8 at he
    dsimp only [a] at he; omega
  have hop : Odd p := Nat.odd_iff.mpr (by omega)
  have hod : Odd d := Nat.odd_iff.mpr (by omega)
  have hnn : ((-2*(d:ℤ)):ZMod p)≠0 := by
    have he : ((2*d:ℕ):ZMod p)≠0 := by
      intro he
      have ht := (ZMod.natCast_eq_zero_iff _ _).mp he
      exact (not_le_of_gt (show 2*d<p by omega)) (Nat.le_of_dvd (by positivity) ht)
    push_cast at he ⊢
    simpa using he
  have hsym : legendreSym p (-2*d)=1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym,jacobiSym.mul_left,jacobiSym.at_neg_two hop,
      ZMod.χ₈'_nat_eq_if_mod_eight,h8,jacobiSym.quadratic_reciprocity_one_mod_four hd hop,
      jacobiSym.mod_left' hmd,jacobiSym.at_neg_one hod,ZMod.χ₄_nat_one_mod_four hd]
    simp [show p%2≠0 by omega]
  obtain ⟨u,hu⟩ := (legendreSym.eq_one_iff p (a:=-2*(d:ℤ)) (by simpa using hnn)).mp hsym
  have hq : (p:ℤ) ∣ ((u.val:ℤ)^2+2*d) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [ZMod.natCast_zmod_val]
    push_cast at hu
    linear_combination -hu
  obtain ⟨C,hC⟩ := hq
  obtain ⟨t,ht⟩ := hmod.dvd
  push_cast at ht
  refine ⟨p,u.val,1-4*t,C,by exact_mod_cast hp.pos,?_,hC.symm⟩
  dsimp only [a] at ht
  linear_combination ht
def coefficients (p b A C : ℤ) : W :=
  ⟨0,-1,A+1,-b,p+b,C+b+1⟩
lemma form_eval (p b A C : ℤ) (u : V) :
    energy (coefficients p b A C) u=
      A*(u.1-u.2.2.2)^2+p*(u.2.1-u.2.2.2)^2+C*(u.2.2.1-u.2.2.2)^2+
      2*(u.1-u.2.2.2)*(u.2.2.1-u.2.2.2)+2*b*(u.2.1-u.2.2.2)*(u.2.2.1-u.2.2.2) := by
  obtain ⟨x,y,z,t⟩ := u
  dsimp [coefficients,energy]; ring
 
theorem shell_nonempty (d : ℕ) (hd : d%4=1) : (shell (2*d)).Nonempty := by
  obtain ⟨p,b,A,C,hp,hA,hC⟩ := auxiliary_prime d hd
  let n : ℤ := 2*d
  have hn : 0<n := by dsimp [n]; omega
  change A*n=p+1 at hA
  change p*C=b^2+n at hC
  let q := coefficients p b A C
  have hdet : det q=1 := by
    dsimp [q,coefficients,det]
    linear_combination A*hC+hA
  have hpos : psd q := by
    rintro ⟨x,y,z,t⟩
    let X := x-t
    let Y := y-t
    let Z := z-t
    have hQ := form_eval p b A C (x,y,z,t)
    change energy q (x,y,z,t)=A*X^2+p*Y^2+C*Z^2+2*X*Z+2*b*Y*Z at hQ
    have hv : p*n*energy q (x,y,z,t)=(p*X+n*Z)^2+n*(p*Y+b*Z)^2+p*X^2 := by
      rw [hQ]
      linear_combination p*X^2*hA+n*Z^2*hC
    have hpn : 0<p*n := mul_pos hp hn
    exact nonneg_of_mul_nonneg_right (show 0≤p*n*energy q (x,y,z,t) by rw [hv]; positivity) hpn
  have hre : energy q (n,b,-p,0)=n := by
    rw [form_eval]
    dsimp only; ring_nf
    linear_combination n*hA+p*hC
  obtain ⟨x,y,z,h⟩ := three_squares hpos hdet (n,b,-p,0)
  exact ⟨(x,y,z),mem_shell.mpr (by change x^2+y^2+z^2=(↑(2*d:ℕ):ℤ); rw [←h,hre]; simp [n])⟩
end TunnellThreeSquares
end


/- TunnellGenusPrimes -/
section
namespace TunnellGenusPrimes
open Finset
noncomputable section
def eps (b : Bool) : ℤ := if b then -1 else 1
lemma local_value {p : ℕ} (hp : p.Prime) (h2 : p≠2) (b : Bool) :
    ∃ a : ℕ, ¬p∣a ∧ jacobiSym (a:ℤ) p=eps b := by
  letI : Fact p.Prime := ⟨hp⟩
  cases b
  · exact ⟨1,hp.not_dvd_one,by simp [eps]⟩
  · obtain ⟨u,hu⟩ := quadraticChar_exists_neg_one' (F:=ZMod p) (by simpa only [ZMod.ringChar_zmod_n] using h2)
    refine ⟨u.val.val,fun H => u.ne_zero ((ZMod.natCast_zmod_val u.val).symm.trans ((ZMod.natCast_eq_zero_iff _ p).mpr H)),?_⟩
    rw [←jacobiSym.legendreSym.to_jacobiSym p]
    change quadraticChar (ZMod p) (((u.val.val:ℤ):ZMod p))= -1
    simpa only [Int.cast_natCast,ZMod.natCast_zmod_val] using hu
lemma prescribe {d : ℕ} (hd : d%4=1) (f : ↥d.primeFactors→Bool) :
    ∃ a : ℕ, a.Coprime d ∧ ∀ p : ↥d.primeFactors, jacobiSym (a:ℤ) p.val=eps (f p) := by
  classical
  have prime (p : ↥d.primeFactors) := Nat.prime_of_mem_primeFactors p.property
  have odd (p : ↥d.primeFactors) : p.val≠2 := by intro h; have k:=Nat.dvd_of_mem_primeFactors p.property; rw [h] at k; omega
  choose r hr hs using fun p : ↥d.primeFactors => local_value (prime p) (odd p) (f p)
  let s (p : ↥d.primeFactors) := p.val
  have hpair : Set.Pairwise (univ : Finset ↥d.primeFactors) (fun a b => Nat.Coprime (s a) (s b)) := by
    intro i _ j _ e; exact (Nat.coprime_primes (prime i) (prime j)).mpr (fun h => e (Subtype.ext h))
  let A := Nat.chineseRemainderOfFinset r s univ (fun p _ => (prime p).ne_zero) hpair
  have he (p : ↥d.primeFactors) : A.val ≡ r p [MOD p.val] := A.property p (mem_univ _)
  refine ⟨A.val,?_ ,?_⟩
  · apply Nat.coprime_of_dvd
    intro p hp ha hd'
    let i : ↥d.primeFactors := ⟨p,Nat.mem_primeFactors.mpr ⟨hp,hd',by omega⟩⟩
    apply hr i
    exact Nat.modEq_zero_iff_dvd.mp ((he i).symm.trans (Nat.modEq_zero_iff_dvd.mpr ha))
  · intro p
    rw [←hs p]
    exact jacobiSym.mod_left' (by exact_mod_cast he p)
lemma gcd_congr {a b c : ℕ} (h : a≡b [MOD c]) : a.gcd c=b.gcd c := by
  rw [Nat.gcd_comm a c,Nat.gcd_comm b c,Nat.gcd_rec c a,Nat.gcd_rec c b,h]
theorem split_prime {d : ℕ} (hd : d%4=1) (f : ↥d.primeFactors→Bool) :
    ∃ q u : ℕ, q.Prime ∧ 2*d<q ∧ u<q ∧ (q:ℤ)∣(u:ℤ)^2+2*d ∧
      ∀ p : ↥d.primeFactors, jacobiSym (q:ℤ) p.val=eps (f p) := by
  obtain ⟨r,hr,hs⟩ := prescribe hd f
  let a : ℕ := if jacobiSym (r:ℤ) d=1 then 1 else 5
  have h8 : a.Coprime 8 := by dsimp [a]; split <;> decide
  have hd8 : Nat.Coprime 8 d := (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr (by omega))).pow_left 3
  obtain ⟨A,hA8,hAd⟩ := Nat.chineseRemainder hd8 a r
  have hc8 : A.Coprime 8 := (gcd_congr hA8).trans h8
  have hcd : A.Coprime d := (gcd_congr hAd).trans hr
  have hc := hc8.mul_right hcd
  obtain ⟨q,hqgt,hq,hmod⟩ := Nat.forall_exists_prime_gt_and_zmodEq (2*d) (q:=8*d) (a:=(A:ℤ)) (by omega) (by exact_mod_cast hc.isCoprime)
  letI : Fact q.Prime := ⟨hq⟩
  have hqd : q ≡ r [MOD d] := (show q ≡ A [MOD d] by exact_mod_cast hmod.of_dvd (show (d:ℤ) ∣ ((8*d:ℕ):ℤ) by exact_mod_cast dvd_mul_left d 8)).trans hAd
  have hq8 : q ≡ a [MOD 8] := (show q ≡ A [MOD 8] by exact_mod_cast hmod.of_dvd (show (8:ℤ) ∣ ((8*d:ℕ):ℤ) by exact_mod_cast dvd_mul_right 8 d)).trans hA8
  have hmod8 : q%8=a := by change q%8=a%8 at hq8; rw [hq8]; dsimp [a]; split <;> decide
  have ho : Odd q := Nat.odd_iff.mpr (by dsimp [a] at hmod8; split at hmod8 <;> omega)
  have hnn : ((-2*(d:ℤ)):ZMod q)≠0 := by
    have he : ((2*d:ℕ):ZMod q)≠0 := by
      intro he; exact (not_le_of_gt hqgt) (Nat.le_of_dvd (by omega) ((ZMod.natCast_eq_zero_iff _ q).mp he))
    push_cast at he ⊢; simpa using he
  have jval := jacobiSym.eq_one_or_neg_one (a:=(r:ℤ)) (b:=d) (by simpa using hr.gcd_eq_one)
  have hj : legendreSym q (-2*d)=1 := by
    rw [jacobiSym.legendreSym.to_jacobiSym,jacobiSym.mul_left,jacobiSym.at_neg_two ho,ZMod.χ₈'_nat_eq_if_mod_eight,
      hmod8,jacobiSym.quadratic_reciprocity_one_mod_four hd ho,jacobiSym.mod_left' (show (q:ℤ)%d=r%d by exact_mod_cast hqd)]
    rcases jval with h|h <;> simp [a,h,Nat.odd_iff.mp ho]
  obtain ⟨u,hu⟩ := (legendreSym.eq_one_iff q (a:=-2*(d:ℤ)) (by simpa using hnn)).mp hj
  refine ⟨q,u.val,hq,hqgt,ZMod.val_lt _,?_,?_⟩
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
    push_cast; rw [ZMod.natCast_zmod_val]; push_cast at hu; linear_combination -hu
  · intro p; rw [←hs p]
    exact jacobiSym.mod_left' (by exact_mod_cast hqd.of_dvd (Nat.dvd_of_mem_primeFactors p.property))
end
end TunnellGenusPrimes
end


/- TunnellRamifiedClasses -/
section
namespace TunnellRamifiedClasses
open TunnellIdealHNF TunnellIdealGenerators TunnellClassThetaCount TunnellToricClass TunnellShell TunnellEmbeddedIdeals
open TunnellProperClassGroup TunnellAmbiguousClass
noncomputable section
def ram (n a : ℕ) : Ideal (R n) := principal (a:R n) ⊔ principal Zsqrtd.sqrtd
lemma root_ne_zero (n : ℕ) : (Zsqrtd.sqrtd:R n)≠0 := by intro h; exact one_ne_zero (congrArg Zsqrtd.im h : (1:ℤ)=0)
lemma ram_ne_bot (n a : ℕ) : ram n a≠⊥ := by
  intro h; have he : principal (Zsqrtd.sqrtd:R n) ≤ ram n a := le_sup_right
  rw [h] at he
  exact nonzero_principal (root_ne_zero n) (le_bot_iff.mp he)
lemma hnf_eq {n : ℕ} (s : Data n) (hb : s.b=0) : ideal s = principal (s.c:R n)*ram n s.a := by
  rw [ram,Ideal.mul_sup,←principal_mul,←principal_mul]
  let x : R n := ⟨s.c*s.a,0⟩
  let y : R n := ⟨0,s.c⟩
  have ex : (s.c:R n)*s.a=x := by change (⟨s.c,0⟩:R n)*⟨s.a,0⟩=x; apply Zsqrtd.ext <;> simp [x,Zsqrtd.re_mul,Zsqrtd.im_mul]
  have ey : (s.c:R n)*Zsqrtd.sqrtd=y := by change (⟨s.c,0⟩:R n)*⟨0,1⟩=y; apply Zsqrtd.ext <;> simp [y,Zsqrtd.re_mul,Zsqrtd.im_mul]
  rw [ex,ey]
  apply le_antisymm
  · intro z hz
    obtain ⟨u,v,e⟩ := basis_expansion s hz
    have q : z=(u:R n)*x+(v:R n)*y := by
      rw [e,hb]; apply Zsqrtd.ext <;> simp [x,y,Zsqrtd.re_add,Zsqrtd.im_add,Zsqrtd.re_mul,Zsqrtd.im_mul] <;> ring
    rw [q]
    apply add_mem
    · exact (show principal x≤principal x ⊔ principal y from le_sup_left) (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self x))
    · exact (show principal y≤principal x ⊔ principal y from le_sup_right) (Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self y))
  · apply sup_le
    · rw [principal,Ideal.span_singleton_le_iff_mem]; exact real_basis s
    · rw [principal,Ideal.span_singleton_le_iff_mem]
      simpa only [hb,Nat.cast_zero,mul_zero] using lift_basis s
lemma complement {n a b : ℕ} (e : n=a*b) :
    principal (Zsqrtd.sqrtd:R n)*ram n a=principal (a:R n)*ram n b := by
  rw [ram,ram,Ideal.mul_sup,Ideal.mul_sup,←principal_mul,←principal_mul,←principal_mul,←principal_mul]
  have he : (Zsqrtd.sqrtd:R n)*Zsqrtd.sqrtd= -((a:R n)*(b:R n)) := by
    rw [←Nat.cast_mul,←e]; apply Zsqrtd.ext <;> simp [Zsqrtd.re_mul,Zsqrtd.im_mul]
  rw [he,mul_comm (Zsqrtd.sqrtd:R n)]; simp only [principal,Ideal.span_singleton_neg,sup_comm]
variable {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {v : Triple} (hv : v∈shell n)
theorem inv_cls {I : Ideal (R n)} (hI : I≠⊥) : letI := group hn h2 hv
    (cls hn h2 hv hI)⁻¹=cls hn h2 hv (conj_ne_bot hI) := by
  letI := group hn h2 hv
  have he : conjugate I*I=principal (normI I:R n) := (mul_comm ..).trans (norm_conjugate hn h2 I hI)
  have hc : cls hn h2 hv (conj_ne_bot hI)*cls hn h2 hv hI=1 := by
    change mul hn h2 hv _ _=one hn h2 hv
    rw [cls_mul]
    have hN : (normI I:R n)≠0 := Nat.cast_ne_zero.mpr (normI_positive (by omega) I hI).ne'
    exact (cls_congr hn h2 hv he).trans (cls_principal hn h2 hv hN (nonzero_principal hN))
  exact (eq_inv_of_mul_eq_one_left hc).symm
theorem ram_classes_cover {d : ℕ} (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {v : Triple} (hv : v∈shell (2*d))
    (c : ProperIdealClass v) : letI := group hn h2 hv
    c⁻¹=c → ∃ a∈d.divisors, c=cls hn h2 hv (ram_ne_bot (2*d) a) := by
  letI := group hn h2 hv
  obtain ⟨I,hI,rfl⟩ := TunnellProperClassGroup.exists_rep hn h2 hv c
  rw [inv_cls hn h2 hv hI]; intro e
  obtain ⟨B,hB,hstable,e⟩ := stable_rep hn h2 hv hI e.symm
  obtain ⟨s,rfl⟩ := normal_form (by omega) hB
  obtain ⟨hb,ha⟩ := stable_hnf h2 s hstable
  have hc : (s.c:R (2*d))≠0 := Nat.cast_ne_zero.mpr s.pos_c.ne'
  have e' : cls hn h2 hv hI=cls hn h2 hv (ram_ne_bot (2*d) s.a) :=
    e.symm.trans ((cls_congr hn h2 hv (hnf_eq s hb)).trans (scalar_class hn h2 hv (ram_ne_bot _ _) hc))
  by_cases hodd : Odd s.a
  · have hc := Nat.coprime_two_right.mpr hodd
    exact ⟨s.a,Nat.mem_divisors.mpr ⟨hc.dvd_of_dvd_mul_left ha,by omega⟩,e'⟩
  · obtain ⟨k,hk⟩ := (even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd))
    obtain ⟨b,he⟩ := ha
    have he' : d=k*b := by rw [hk,mul_assoc] at he; omega
    have hA : (s.a:R (2*d))≠0 := Nat.cast_ne_zero.mpr s.pos_a.ne'
    refine ⟨b,Nat.mem_divisors.mpr ⟨⟨k,he'.trans (mul_comm _ _)⟩,by omega⟩,e'.trans ?_⟩
    exact (scalar_class hn h2 hv (ram_ne_bot _ _) (root_ne_zero _)).symm.trans
      ((cls_congr hn h2 hv (complement he)).trans (scalar_class hn h2 hv (ram_ne_bot _ _) hA))
end
end TunnellRamifiedClasses
end


/- TunnellGenusMap -/
section
namespace TunnellGenusMap
open TunnellIdealHNF TunnellIdealGenerators TunnellClassThetaCount TunnellToricClass TunnellShell TunnellEmbeddedIdeals
open TunnellProperClassGroup TunnellAmbiguousClass TunnellGenusCharacter TunnellGenusPrimes TunnellIdealThetaExpansion
noncomputable section
variable {n p : ℕ} [hpFact : Fact p.Prime] (hn : Squarefree n) (h2 : n%4=2) {v : Triple} (hv : v∈shell n)
def charClass (c : ProperIdealClass v) : ℤ := charI (p:=p) hn h2 (preimage_ne_bot hn h2 hv c.out)
lemma charClass_cls (hp : p∣n) {I : Ideal (R n)} (hI : I≠⊥) : charClass (p:=p) hn h2 hv (cls hn h2 hv hI)=charI (p:=p) hn h2 hI := by
  apply charI_congr hn h2 hv hp
  let c := cls hn h2 hv hI
  calc _=Quotient.mk (idealSetoid v) c.out := congrArg _ (Subtype.ext (image_preimage hn h2 hv c.out))
       _=_ := Quotient.out_eq _
def charHom (hp : p∣n) : letI := group hn h2 hv
    ProperIdealClass v →* ℤ := by
  letI := group hn h2 hv
  refine { toFun := charClass (p:=p) hn h2 hv, map_one' := ?_, map_mul' := ?_ }
  · have e : (1:ProperIdealClass v)=cls hn h2 hv (nonzero_principal (one_ne_zero : (1:R n)≠0)) := (cls_principal hn h2 hv one_ne_zero (nonzero_principal one_ne_zero)).symm
    rw [e,charClass_cls hn h2 hv hp,charI_principal hn h2 hp one_ne_zero]
  · intro a b
    obtain ⟨A,hA,rfl⟩ := TunnellProperClassGroup.exists_rep hn h2 hv a
    obtain ⟨B,hB,rfl⟩ := TunnellProperClassGroup.exists_rep hn h2 hv b
    change charClass (p:=p) hn h2 hv (mul hn h2 hv _ _)=_
    rw [cls_mul,charClass_cls hn h2 hv hp,charClass_cls hn h2 hv hp,charClass_cls hn h2 hv hp,charI_mul hn h2 hp]
variable {d : ℕ} (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {v : Triple} (hv : v∈shell (2*d))
def genus : letI := group hn h2 hv
    ProperIdealClass v →* (↥d.primeFactors → ℤˣ) := by
  letI := group hn h2 hv
  letI (p : ↥d.primeFactors) : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
  exact MonoidHom.pi (fun p : ↥d.primeFactors =>
    (charHom (p:=p.val) hn h2 hv ((Nat.dvd_of_mem_primeFactors p.property).trans (dvd_mul_left d 2))).toHomUnits)
lemma genus_eval {I : Ideal (R (2*d))} (hI : I≠⊥) (p : ↥d.primeFactors) :
    letI : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
    ((genus hn h2 hv (cls hn h2 hv hI) p:ℤˣ):ℤ)=charI (p:=p.val) hn h2 hI := by
  letI : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
  exact charClass_cls hn h2 hv ((Nat.dvd_of_mem_primeFactors p.property).trans (dvd_mul_left d 2)) hI
theorem genus_surj (hd : d%4=1) : Function.Surjective (genus hn h2 hv) := by
  intro f
  let s (p : ↥d.primeFactors) : Bool := decide ((f p:ℤ) = -1)
  have hs (p : ↥d.primeFactors) : eps (s p)=(f p:ℤ) := by
    unfold eps s
    rcases Int.eq_one_or_neg_one_of_mul_eq_one (f p).val_inv with h|h <;> rw [h] <;> decide
  obtain ⟨q,u,hq,hq',hu,he,hf⟩ := split_prime hd s
  let S : Data (2*d) := ⟨1,q,u,one_pos,hq.pos,hu,by simpa using he⟩
  let I := ideal S
  let z : I := ⟨(q:R (2*d)),by change (⟨(q:ℤ),0⟩:R (2*d))∈ideal S; simpa only [S,Nat.cast_one,one_mul] using real_basis S⟩
  have hI := ideal_ne_bot S
  have hZ : valence z=q := by
    have e : normI I=q := by rw [normI,quotient_card]; simp [S]
    change ((q:R (2*d))).norm.toNat/normI I=q
    have eq : (q:R (2*d)).norm=(q:ℤ)*q := by change (q:ℤ)*q- -(↑(2*d):ℤ)*0*0=_; ring
    rw [eq,e,←Nat.cast_mul,Int.toNat_natCast,Nat.mul_div_cancel _ hq.pos]
  refine ⟨cls hn h2 hv hI,?_⟩
  funext p; apply Units.ext
  letI : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
  have hp : p.val∣d := Nat.dvd_of_mem_primeFactors p.property
  have hnp : p.val∣2*d := hp.trans (dvd_mul_left _ _)
  have he : (valence z:ZMod p.val)≠0 := by
    intro hh
    have h := (ZMod.natCast_eq_zero_iff q p.val).mp (by simpa only [hZ] using hh)
    have h' := ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.val.Prime) hq).mp h)
    have e := Nat.le_of_dvd (show 0<d by omega) hp
    omega
  rw [genus_eval,charI_eq hn h2 hnp hI z he,hZ,←hs,←hf]
  rw [←jacobiSym.legendreSym.to_jacobiSym,legendreSym,Int.cast_natCast]
end
end TunnellGenusMap
end


/- TunnellPrincipalGenus -/
section
namespace TunnellPrincipalGenus
open TunnellProperClassGroup TunnellGenusMap TunnellRamifiedClasses TunnellToricClass TunnellToric TunnellShell
noncomputable section
variable {d : ℕ} (hsq : Squarefree d) (hn : Squarefree (2*d)) (hd : d%4=1) (h2 : (2*d)%4=2) {v : Triple} (hv : v∈shell (2*d))
include hsq in
lemma divisor_card : d.divisors.card=2^d.primeFactors.card := by
  rw [Nat.card_divisors hsq.ne_zero]
  calc _=∏ _p∈d.primeFactors, 2 := by
         apply Finset.prod_congr rfl
         intro p hp; rw [Nat.factorization_eq_one_of_squarefree hsq (Nat.prime_of_mem_primeFactors hp) (Nat.dvd_of_mem_primeFactors hp)]
       _=_ := Finset.prod_const _
include hsq in
lemma bound_two_torsion : letI := group hn h2 hv
    Nat.card (powMonoidHom (α:=ProperIdealClass v) 2).ker ≤ 2^d.primeFactors.card := by
  letI := group hn h2 hv
  let P := powMonoidHom (α:=ProperIdealClass v) 2
  letI := Fintype.ofEquiv ↥(representatives (2*d)) (idealEquiv hn h2 hv).symm
  have cover (x : P.ker) : ∃ a : ↥d.divisors, x.val=cls hn h2 hv (ram_ne_bot (2*d) a.val) := by
    have H : x.val*x.val=1 := by simpa only [P,powMonoidHom_apply,pow_two] using MonoidHom.mem_ker.mp x.property
    obtain ⟨a,ha,e⟩ := ram_classes_cover hn h2 hv x.val (eq_inv_of_mul_eq_one_left H).symm
    exact ⟨⟨a,ha⟩,e⟩
  choose f hf using cover
  have hi : Function.Injective f := by intro x y h; exact Subtype.ext ((hf x).trans (h ▸ (hf y).symm))
  exact (Nat.card_le_card_of_injective f hi).trans_eq ((Nat.card_eq_finsetCard _).trans (divisor_card hsq))
lemma units_sq (a : ℤˣ) : a^2=1 := by
  apply Units.ext
  rcases Int.eq_one_or_neg_one_of_mul_eq_one a.val_inv with h|h <;> simp [h]
theorem finite_group_argument {G H : Type*} [CommGroup G] [Group H] [Finite G] [Finite H]
    (Γ : G →* H) (honto : Function.Surjective Γ) (hH : ∀ x:H, x^2=1)
    (hbd : Nat.card (powMonoidHom (α:=G) 2).ker ≤ Nat.card H) :
    (powMonoidHom (α:=G) 2).range=Γ.ker ∧ Nat.card (powMonoidHom (α:=G) 2).ker=Nat.card H := by
  let P := powMonoidHom (α:=G) 2
  have hle : P.range≤Γ.ker := by
    rintro _ ⟨x,rfl⟩
    change Γ (x^2)=1
    rw [map_pow,hH]
  have hΓ : Nat.card Γ.ker*Nat.card H=Nat.card G := by
    have e := Γ.ker.card_mul_index
    rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr honto,Nat.card_congr (Subgroup.topEquiv.toEquiv)] at e
    exact e
  have hP : Nat.card P.ker*Nat.card P.range=Nat.card G := by rw [←Subgroup.index_ker]; exact P.ker.card_mul_index
  have hcard : Nat.card Γ.ker≤Nat.card P.range := by
    apply le_of_mul_le_mul_right (a:=Nat.card H) _ Nat.card_pos
    rw [hΓ,←hP,mul_comm _ (Nat.card H)]
    exact Nat.mul_le_mul_right _ hbd
  have he : P.range=Γ.ker := SetLike.ext' (Set.eq_of_subset_of_ncard_le hle (by simpa only [←Nat.card_coe_set_eq,SetLike.coe_sort_coe] using hcard))
  refine ⟨he,?_⟩
  rw [he] at hP
  apply Nat.mul_right_cancel (Nat.card_pos (α:=Γ.ker))
  exact hP.trans (hΓ.symm.trans (mul_comm ..))
include hsq hd in
theorem principal_genus : letI := group hn h2 hv
    (powMonoidHom (α:=ProperIdealClass v) 2).range=(genus hn h2 hv).ker ∧
    Nat.card (powMonoidHom (α:=ProperIdealClass v) 2).ker=2^d.primeFactors.card := by
  letI := group hn h2 hv
  letI := Fintype.ofEquiv ↥(representatives (2*d)) (idealEquiv hn h2 hv).symm
  have hH : Nat.card (↥d.primeFactors → ℤˣ)=2^d.primeFactors.card := by
    rw [Nat.card_fun,Nat.card_eq_fintype_card (α:=ℤˣ),Fintype.card_units_int,Nat.card_eq_finsetCard]
  rw [←hH]
  exact finite_group_argument (genus hn h2 hv) (genus_surj hn h2 hv hd) (fun f => funext fun p => units_sq (f p))
    ((bound_two_torsion hsq hn h2 hv).trans_eq hH.symm)
end
end TunnellPrincipalGenus
end


/- TunnellPairComponents -/
section
namespace TunnellPairComponents
open TunnellShell TunnellHurwitz TunnellIdealHNF TunnellEmbeddedIdeals TunnellToricClass TunnellToricLocal
open TunnellClassThetaCount TunnellFrameNorm TunnellIntertwinerTheta TunnellIdealGenerators
noncomputable section
lemma pure_neg (v : Triple) : (TunnellHurwitz.pure) (-v)= -(TunnellHurwitz.pure) v := by
  apply QuaternionAlgebra.ext <;> simp only [Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg] <;> simp [TunnellHurwitz.pure]
lemma J_neg (s t : Triple) : J (-s) (-t)=J s t := by
  ext q; simp only [mem_J,pure_neg,neg_mul,mul_neg,neg_inj]
lemma J_opposite (s t : Triple) : J (-s) t=J s (-t) := by rw [←J_neg (-s) t,neg_neg]
lemma shell_neg {n : ℕ} {v : Triple} (hv : v∈shell n) : -v∈shell n := by
  rw [mem_shell] at hv ⊢; simpa [TunnellShell.normSq] using hv
lemma embed_star {n : ℕ} {v : Triple} (hv : v∈shell n) (x : R n) :
    embed n v hv (star x)=star (embed n v hv x) := by
  apply QuaternionAlgebra.ext
  all_goals first | rw [Quaternion.re_star] | rw [Quaternion.imI_star] | rw [Quaternion.imJ_star] | rw [Quaternion.imK_star]
  all_goals change _=_
  · rfl
  all_goals change ((-x.im:ℤ):ℚ)*_= -((x.im:ℚ)*_); push_cast; ring
lemma image_conj_star {n : ℕ} {v : Triple} (hv : v∈shell n) (A : Ideal (R n)) (q : Q) :
    q∈image hv (conjugate A) ↔ star q∈image hv A := by
  constructor
  · rintro ⟨x,hx,rfl⟩; exact ⟨star x,hx,embed_star hv x⟩
  · rintro ⟨x,hx,e⟩; change embed n v hv x=star q at e
    exact ⟨star x,conj_mem A hx,by change embed n v hv (star x)=q; rw [embed_star,e,star_star]⟩
lemma conj_frame {n : ℕ} {v w : Triple} (hv : v∈shell n) {A : Ideal (R n)} {a : Q}
    (e : image hv A=line a*J v w) : image hv (conjugate A)=J w v*line (star a) := by
  ext q; rw [image_conj_star,e]
  constructor
  · intro h; obtain ⟨z,hz,he⟩ := Submodule.mem_span_singleton_mul.mp h
    exact Submodule.mem_mul_span_singleton.mpr ⟨star z,star_intertwines hz,by rw [←star_mul,he,star_star]⟩
  · intro h; obtain ⟨z,hz,rfl⟩ := Submodule.mem_mul_span_singleton.mp h
    exact Submodule.mem_span_singleton_mul.mpr ⟨star z,star_intertwines hz,by rw [star_mul,star_star]⟩
lemma embed_expand {n : ℕ} {v : Triple} (hv : v∈shell n) (x : R n) :
    embed n v hv x=(x.re:Q)+(x.im:Q)*(TunnellHurwitz.pure) v := by
  apply QuaternionAlgebra.ext
  all_goals simp only [Quaternion.re_add,Quaternion.imI_add,Quaternion.imJ_add,Quaternion.imK_add,
    Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,Quaternion.re_intCast,Quaternion.imI_intCast,Quaternion.imJ_intCast,Quaternion.imK_intCast]
  all_goals change _=_; dsimp [TunnellHurwitz.pure]; simp <;> rfl
lemma anti_scalar {n : ℕ} {v : Triple} (hv : v∈shell n) {u : Q}
    (hu : (TunnellHurwitz.pure) v*u= -(u*(TunnellHurwitz.pure) v)) (B : Ideal (R n)) : line u*image hv B=image hv (conjugate B)*line u := by
  have he (x : R n) : u*(embed n v hv x)=embed n v hv (star x)*u := by
    rw [embed_expand hv,embed_expand hv,Zsqrtd.re_star,Zsqrtd.im_star,Int.cast_neg,mul_add,add_mul,←mul_assoc,
      ←Int.cast_comm x.re u,←Int.cast_comm x.im u,neg_mul,neg_mul]
    rw [mul_assoc (x.im:Q),mul_assoc (x.im:Q),hu,mul_neg,neg_neg]
  ext q
  constructor
  · intro h; obtain ⟨y,hy,rfl⟩ := Submodule.mem_span_singleton_mul.mp h; obtain ⟨x,hx,rfl⟩ := (mem_image _).mp hy
    exact Submodule.mem_mul_span_singleton.mpr ⟨_,⟨star x,conj_mem _ hx,rfl⟩,(he x).symm⟩
  · intro h; obtain ⟨y,hy,rfl⟩ := Submodule.mem_mul_span_singleton.mp h; obtain ⟨x,hx,rfl⟩ := (mem_image _).mp hy
    exact Submodule.mem_span_singleton_mul.mpr ⟨_,⟨star x,hx,rfl⟩,by change u*embed n v hv (star x)=embed n v hv x*u; rw [he,star_star]⟩
end
end TunnellPairComponents
end


/- TunnellAntiGenus -/
section
namespace TunnellAntiGenus
open TunnellShell TunnellToricLocal TunnellHurwitz TunnellToricClass TunnellQuaternion Matrix
open TunnellHurwitzFour
noncomputable section
lemma anti_det {K : Type*} [Field K] (h2 : (2:K)≠0) (V X : M2 K)
    (hn : V≠0) (ht : V.trace=0) (hd : V.det=0) (e : V*X= -(X*V)) : ∃ r : K, X.det= -r^2 := by
  obtain ⟨x,y,hB⟩ := cyclic_exists V h2 hn ht
  let B := cyclicBasis x y V
  let D : M2 K := !![0,0;1,0]
  let Y := B⁻¹*X*B
  have hD : V*B=B*D := by simpa [D,hd] using cyclic_action V ht x y
  have hu : IsUnit B.det := isUnit_iff_ne_zero.mpr hB
  have hIB : D*B⁻¹=B⁻¹*V := by
    calc _=B⁻¹*(B*D)*B⁻¹ := by simp [←mul_assoc,Matrix.nonsing_inv_mul B hu]
         _=_ := by rw [←hD]; simp [mul_assoc,Matrix.mul_nonsing_inv B hu]
  have hy : D*Y= -(Y*D) := by
    dsimp only [Y]
    rw [←mul_assoc,←mul_assoc,hIB,mul_assoc B⁻¹,e,mul_neg,neg_mul]
    simp only [mul_assoc]; rw [hD]
  have e₀ := congrArg (fun t:M2 K => t 0 0) hy
  have e₁ := congrArg (fun t:M2 K => t 1 0) hy
  simp only [D,mul_apply,Fin.sum_univ_two,of_apply,cons_val_zero,cons_val_one,cons_val_fin_one,zero_mul,mul_zero,one_mul,mul_one,zero_add,add_zero,Matrix.neg_apply,zero_eq_neg] at e₀ e₁
  have hdet : Y.det=X.det := by dsimp only [Y]; rw [det_mul,det_mul,det_nonsing_inv,Ring.inverse_eq_inv]; field_simp [hu.ne_zero]
  refine ⟨Y 0 0,?_⟩
  have hy0 : Y 0 1=0 := by simpa using e₀
  rw [←hdet,det_fin_two,hy0]; linear_combination (Y 0 0)*e₁
lemma rat_injective : Function.Injective rat := by
  intro x y e; apply QuaternionAlgebra.ext
  · exact_mod_cast (show ((x.re:ℤ):ℚ)=y.re from congrArg QuaternionAlgebra.re e)
  · exact_mod_cast (show ((x.imI:ℤ):ℚ)=y.imI from congrArg QuaternionAlgebra.imI e)
  · exact_mod_cast (show ((x.imJ:ℤ):ℚ)=y.imJ from congrArg QuaternionAlgebra.imJ e)
  · exact_mod_cast (show ((x.imK:ℤ):ℚ)=y.imK from congrArg QuaternionAlgebra.imK e)
def twice (q : H ℤ) : Quaternion ℤ :=
  ⟨2*q.1+q.2.2.2,2*q.2.1+q.2.2.2,2*q.2.2.1+q.2.2.2,q.2.2.2⟩
lemma twice_rat (q : H ℤ) : rat (twice q)=2*hamZ q := by
  rw [two_mul]; apply QuaternionAlgebra.ext
  all_goals simp only [Quaternion.re_add,Quaternion.imI_add,Quaternion.imJ_add,Quaternion.imK_add] <;> dsimp [twice,rat,hamZ,ham] <;> push_cast <;> ring
lemma rat_neg (x : Quaternion ℤ) : rat (-x)= -(rat x) := by
  apply QuaternionAlgebra.ext
  all_goals simp only [Quaternion.re_neg,Quaternion.imI_neg,Quaternion.imJ_neg,Quaternion.imK_neg] <;> dsimp [rat] <;> simp
lemma anti_char {p n : ℕ} [Fact p.Prime] (hp2 : p≠2) (hn : Squarefree n) (hp : p∣n)
    {v : Triple} (hv : v∈shell n) {q : H ℤ} (e : TunnellHurwitz.pure v*hamZ q= -(hamZ q*TunnellHurwitz.pure v))
    (hq : ((nr q:ℤ):ZMod p)≠0) :
    quadraticChar (ZMod p) ((nr q:ℤ):ZMod p)=quadraticChar (ZMod p) (-1) := by
  let M := localModel hp2
  let V := residue M (TunnellQuaternion.pure v)
  let X := residue M (twice q)
  have hV : V.trace=0 := by rw [residue_trace]; simp [TunnellQuaternion.pure]
  have hD : V.det=0 := by rw [residue_det,norm_pure,mem_shell.mp hv,Int.cast_natCast,ZMod.natCast_eq_zero_iff]; exact hp
  have h2 : (2:ZMod p)≠0 := by
    intro h; have ht := (ZMod.natCast_eq_zero_iff 2 p).mp (by simpa using h)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out:p.Prime) Nat.prime_two).mp ht)
  have hqZ : TunnellQuaternion.pure v*twice q= -(twice q*TunnellQuaternion.pure v) := by
    apply rat_injective; rw [rat_mul,rat_neg,rat_mul,twice_rat]
    have h : rat (TunnellQuaternion.pure v)=TunnellHurwitz.pure v := rfl
    rw [h]; noncomm_ring [e]
  have hX : V*X= -(X*V) := by simpa only [map_mul,map_neg,V,X] using congrArg (residue M) hqZ
  obtain ⟨r,hr⟩ := anti_det h2 V X (residue_nonzero M hn hv) hV hD hX
  have hZ : Quaternion.normSq (twice q)=4*nr q := by
    rw [Quaternion.normSq_def']; dsimp [twice,nr]; ring
  rw [show X.det=((Quaternion.normSq (twice q):ℤ):ZMod p) from residue_det _ _,hZ,Int.cast_mul,Int.cast_ofNat] at hr
  have h4 : (4:ZMod p)≠0 := by simpa only [show (4:ZMod p)=2^2 by norm_num] using pow_ne_zero 2 h2
  have hr0 : r≠0 := fun h => (mul_ne_zero h4 hq) (by simpa [h] using hr)
  have he := congrArg (quadraticChar (ZMod p)) hr
  rw [show (4:ZMod p)=2^2 by norm_num,map_mul,quadraticChar_sq_one' h2,one_mul,←neg_one_mul,map_mul,quadraticChar_sq_one' hr0,mul_one] at he
  exact he
end
end TunnellAntiGenus
end


/- TunnellReferenceGenus -/
section
namespace TunnellReferenceGenus
open TunnellShell TunnellHurwitz TunnellIdealHNF TunnellEmbeddedIdeals TunnellToricClass TunnellToricLocal
open TunnellClassThetaCount TunnellFrameNorm TunnellIntertwinerTheta TunnellIdealGenerators TunnellPairComponents
open TunnellProperClassGroup TunnellGenusMap TunnellGenusCharacter TunnellIdealThetaExpansion TunnellToric
noncomputable section
theorem reference {d : ℕ} (hn : Squarefree (2*d)) (hd : d%4=1) (h2 : (2*d)%4=2) {v : Triple} (hv : v∈shell (2*d)) :
    ∃ (C : Ideal (R (2*d))) (hC : C≠⊥) (a : Q), a≠0 ∧ a∈J (-v) v ∧
      image hv C=line a*J v (-v) ∧
      ∀ p : ↥d.primeFactors, letI : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
      ((genus hn h2 hv (cls hn h2 hv hC) p:ℤˣ):ℤ)=quadraticChar (ZMod p.val) (-1) := by
  have hw := shell_neg hv
  obtain ⟨a,ha,h0,e⟩ := intertwine (-v) v hw hv
  have hA : a∈J (-v) v := ⟨ha,e⟩
  let A : IntegralIdeal v := ⟨line a*J v (-v),from_embedding hn h2 hv hw hA h0⟩
  let C := preimage hv A
  have hC : C≠⊥ := preimage_ne_bot hn h2 hv _
  have H : image hv C=line a*J v (-v) := image_preimage hn h2 hv A
  refine ⟨C,hC,a,h0,hA,H,?_⟩
  intro p
  letI : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
  have hpd := Nat.dvd_of_mem_primeFactors p.property
  have hp2 : p.val≠2 := by intro e; rw [e] at hpd; omega
  let x := good (p:=p.val) hn h2 hC
  have hx : (valence x:ZMod p.val)≠0 := good_nonzero hn h2 hC
  have xmem : embed (2*d) v hv x.val∈line a*J v (-v) := H ▸ ⟨x.val,x.property,rfl⟩
  obtain ⟨q,hq,he⟩ := Submodule.mem_span_singleton_mul.mp xmem
  obtain ⟨q,rfl⟩ := (show q∈J v (-v) from hq).1
  have hanti := (show hamZ q∈J v (-v) from hq).2
  rw [pure_neg,neg_mul] at hanti
  have ee := congrArg Quaternion.normSq he
  rw [map_mul,norm_ham,frame_norm hn h2 hv hw hC hA H,norm_embed hv,norm_valZ hn h2 hC x] at ee
  have eZ : (normI C:ℤ)*TunnellHurwitzFour.nr q=valence x*(normI C:ℤ) := by exact_mod_cast ee
  have eq : (TunnellHurwitzFour.nr q:ℤ)=valence x := by
    rw [mul_comm (valence x:ℤ)] at eZ
    exact mul_left_cancel₀ (show (normI C:ℤ)≠0 by exact_mod_cast (normI_positive (by omega) C hC).ne') eZ
  have hq0 : ((TunnellHurwitzFour.nr q:ℤ):ZMod p.val)≠0 := by simpa only [eq,Int.cast_natCast] using hx
  rw [genus_eval,charI_eq hn h2 (hpd.trans (dvd_mul_left d 2)) hC x hx]
  simpa only [eq,Int.cast_natCast] using TunnellAntiGenus.anti_char hp2 hn (hpd.trans (dvd_mul_left d 2)) hv (neg_eq_iff_eq_neg.mp hanti) hq0
end
end TunnellReferenceGenus
end


/- TunnellRamifiedPlane -/
section
namespace TunnellRamifiedPlane
open Finset ZMod
noncomputable section
variable {p : ℕ} [Fact p.Prime]
def form (a t : (ZMod p)) (v : (ZMod p)×(ZMod p)) := a*(v.1^2-t*v.2^2)
end
end TunnellRamifiedPlane
end


/- TunnellOddDiscriminant -/
section
namespace TunnellOddDiscriminant
open TunnellIdealHNF TunnellIdealGenerators TunnellGenusCharacter TunnellIdealThetaExpansion
noncomputable section
variable {n p : ℕ} [Fact p.Prime]
def quad {K : Type*} [CommRing K] (A B C : K) (x : K×K) := A*x.1^2+2*B*x.1*x.2+C*x.2^2
def pairing {K : Type*} [CommRing K] (A B C : K) (x : K×K) := (A*x.1+B*x.2,B*x.1+C*x.2)
lemma radical {A B C : (ZMod p)} (ha : A≠0) (h : A*C-B^2=0) (x : (ZMod p)×(ZMod p)) :
    pairing A B C x=0 ↔ ∃ r:(ZMod p), x=(-B*r,A*r) := by
  constructor
  · intro e; have e₁ := congrArg Prod.fst e
    change A*x.1+B*x.2=0 at e₁
    refine ⟨x.2/A,Prod.ext ?_ ?_⟩
    · dsimp only; field_simp; linear_combination e₁
    · dsimp only; field_simp
  · rintro ⟨r,rfl⟩; apply Prod.ext <;> dsimp [pairing]
    · ring
    · linear_combination r*h
lemma quotient_nonzero (hn : Squarefree n) (hp : p∣n) : ((n/p:ℕ):(ZMod p))≠0 := by
  intro e; have he := (ZMod.natCast_eq_zero_iff _ _).mp e
  have hh : p*p∣n := by
    have hmul := Nat.mul_dvd_mul_left p he
    rwa [Nat.mul_div_cancel' hp] at hmul
  exact (Fact.out:p.Prime).ne_one (Nat.isUnit_iff.mp (hn p hh))
theorem plane_parameter (hn : Squarefree n) (hp : p∣n) (hp2 : p≠2) {A D : (ZMod p)} (ha : A≠0) (hd : D≠0) :
    let a := ((n/p:ℕ):(ZMod p))*A
    let t := -(4:(ZMod p))*D/A
    a≠0 ∧ t≠0 ∧ (quadraticChar (ZMod p)) t=(quadraticChar (ZMod p)) (-1)*(quadraticChar (ZMod p)) D*(quadraticChar (ZMod p)) A ∧
    ∀ v:(ZMod p)×(ZMod p), TunnellRamifiedPlane.form a t v=((n/p:ℕ):(ZMod p))*(A*v.1^2+4*D*v.2^2) := by
  have h₂ : (2:(ZMod p))≠0 := by
    intro e; exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out:p.Prime) Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp e))
  have h₄ : (4:(ZMod p))≠0 := by simpa only [show (4:(ZMod p))=2^2 by norm_num] using pow_ne_zero 2 h₂
  refine ⟨mul_ne_zero (quotient_nonzero hn hp) ha,div_ne_zero (mul_ne_zero (neg_ne_zero.mpr h₄) hd) ha,?_,?_⟩
  · change (quadraticChar (ZMod p)) (-4*D/A)=_
    rw [div_eq_mul_inv,show -(4:(ZMod p))=(-1)*2^2 by ring,map_mul,map_mul,map_mul,quadraticChar_sq_one' h₂,mul_one]
    have hinv : (quadraticChar (ZMod p)) A⁻¹=(quadraticChar (ZMod p)) A := by
      have h := quadraticChar_sq_one ha
      have e : (quadraticChar (ZMod p)) A*(quadraticChar (ZMod p)) A⁻¹=1 := by rw [←map_mul,mul_inv_cancel₀ ha,map_one]
      have hc : (quadraticChar (ZMod p)) A ≠ 0 := fun h₀ => ha (quadraticChar_eq_zero_iff.mp h₀)
      apply mul_left_cancel₀ hc
      rw [e,←pow_two,h]
    rw [hinv]
  · intro v; dsimp only [TunnellRamifiedPlane.form]; field_simp; ring
end
end TunnellOddDiscriminant
end


/- TunnellRamifiedLines -/
section
namespace TunnellRamifiedLines
open Finset
noncomputable section
variable {F : Type*} [Field F]
lemma unique_slope (h2 : (2:F)≠0) {t : F} {x : F×F} (hx : x≠0) (hQ : x.1^2=t*x.2^2) :
    let r := x.1/x.2
    r^2=t ∧ ∀ y : F×F, y.1^2=t*y.2^2 → (x.1+y.1)^2=t*(x.2+y.2)^2 → y.1=r*y.2 := by
  have h : x.2≠0 := by
    intro hz; rw [hz,zero_pow (by decide),mul_zero] at hQ
    exact hx (Prod.ext (sq_eq_zero_iff.mp hQ) hz)
  constructor
  · rw [div_pow,hQ,mul_div_cancel_right₀ _ (pow_ne_zero _ h)]
  · intro y hy hxy
    have e : (2:F)*(x.1*y.1-t*x.2*y.2)=0 := by linear_combination hxy - hQ - hy
    have ez := (mul_eq_zero.mp e).resolve_left h2
    field_simp
    apply sub_eq_zero.mp
    apply sq_eq_zero_iff.mp
    linear_combination x.2^2*hy + y.2^2*hQ - (2*x.2*y.2)*ez
variable {d : ℕ}
abbrev P (d : ℕ) := ↥d.primeFactors
abbrev Packet (d : ℕ) := (p : P d) → ZMod p.val × ZMod p.val
private instance prime (p : P d) : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
lemma selector (r : (p : P d) → ZMod p.val) : ∃ a : ℕ, ∀ p : P d, (a:ZMod p.val)=r p := by
  classical
  have hpair : Set.Pairwise (univ : Finset (P d)) (fun a b : P d => Nat.Coprime a.val b.val) := by
    intro i _ j _ e; exact (Nat.coprime_primes (prime i).out (prime j).out).mpr (fun h => e (Subtype.ext h))
  let A := Nat.chineseRemainderOfFinset (fun p : P d => (r p).val) Subtype.val univ (fun p _ => (prime p).out.ne_zero) hpair
  refine ⟨A.val,fun p => ?_⟩
  have e := A.property p (mem_univ p)
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr e |>.trans (ZMod.natCast_zmod_val _)
lemma independent (S : AddSubgroup (Packet d)) (x : Packet d)
    (hx : ∀ p : P d, ∃ y∈S, y p=x p) : x∈S := by
  classical
  choose y hy e using hx
  have he (p : P d) : ∃ a : ℕ, ∀ q : P d, (a:ZMod q.val)=if q=p then 1 else 0 :=
    selector (fun q => if q=p then 1 else 0)
  choose a ha using he
  have h : (∑ p, a p • y p)=x := by
    funext q; rw [Finset.sum_apply]; simp only [Pi.smul_apply]
    rw [Finset.sum_eq_single q]
    · apply Prod.ext <;> simp [nsmul_eq_mul,ha,e]
    · intro b _ hb; apply Prod.ext <;> simp [nsmul_eq_mul,ha,Ne.symm hb]
    · simp
  exact h ▸ S.sum_mem (fun p _ => S.nsmul_mem (hy p) _)
def linePacket (r : (p : P d) → ZMod p.val) : AddSubgroup (Packet d) where
  carrier := {x | ∀ p, (x p).1=r p*(x p).2}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy p; change (x p).1+(y p).1=r p*((x p).2+(y p).2); rw [hx p,hy p,mul_add]
  neg_mem' := by intro x hx p; change -(x p).1=r p*(-(x p).2); rw [hx p,mul_neg]
theorem classification (hd : Odd d) (S : AddSubgroup (Packet d)) (t : (p : P d) → ZMod p.val)
    (hQ : ∀ x∈S, ∀ p : P d, (x p).1^2=t p*(x p).2^2)
    (hS : ∀ p : P d, ∃ x∈S, x p≠0) :
    ∃ r : (p : P d) → ZMod p.val, (∀ p, r p^2=t p) ∧ S=linePacket r := by
  classical
  choose u hu h0 using hS
  let r (p : P d) := (u p p).1/(u p p).2
  have h2 (p : P d) : (2:ZMod p.val)≠0 := by
    intro hh; have e := (Nat.prime_dvd_prime_iff_eq (prime p).out Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p.val).mp hh)
    have hv := Nat.dvd_of_mem_primeFactors p.property; rw [e] at hv; exact (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr hv)
  have hsl (p : P d) := unique_slope (h2 p) (h0 p) (hQ _ (hu p) p)
  have he (x : Packet d) (hx : x∈S) (p : P d) : (x p).1=r p*(x p).2 :=
    (hsl p).2 _ (hQ x hx p) (hQ (u p+x) (S.add_mem (hu p) hx) p)
  refine ⟨r,fun p => (hsl p).1,le_antisymm (fun x hx p => he x hx p) ?_⟩
  intro x hx; apply independent S x; intro p
  have h₂ : (u p p).2≠0 := by intro ez; apply h0 p; exact Prod.ext (by rw [he _ (hu p) p,ez,mul_zero]; rfl) ez
  let m := ((x p).2/(u p p).2).val
  refine ⟨m • u p,S.nsmul_mem (hu p) m,?_⟩
  have em : (m:ZMod p.val)=(x p).2/(u p p).2 := ZMod.natCast_zmod_val _
  apply Prod.ext
  · change m • (u p p).1=(x p).1; rw [nsmul_eq_mul,em,he _ (hu p) p,hx p]; field_simp
  · change m • (u p p).2=(x p).2; rw [nsmul_eq_mul,em,div_mul_cancel₀ _ h₂]
end
end TunnellRamifiedLines
end


/- TunnellAllRamifiedLines -/
section
namespace TunnellAllRamifiedLines
open TunnellRamifiedLines
noncomputable section
variable {d : ℕ}
private instance prime (p : P d) : Fact p.val.Prime := ⟨Nat.prime_of_mem_primeFactors p.property⟩
def signed (r : (p : P d) → ZMod p.val) (e : P d → Bool) (p : P d) := if e p then -(r p) else r p
theorem exhaustive (hs : Squarefree d) (hd : Odd d) (t : (p : P d) → ZMod p.val) (ht : ∀ p, t p≠0)
    (S : ↥d.divisors → AddSubgroup (Packet d)) (hi : Function.Injective S)
    (hQ : ∀ a x, x∈S a → ∀ p : P d, (x p).1^2=t p*(x p).2^2)
    (hS : ∀ a (p : P d), ∃ x∈S a, x p≠0) :
    ∃ r : (p : P d) → ZMod p.val, (∀ p, r p^2=t p) ∧
      ∃ E : ↥d.divisors ≃ (P d → Bool), ∀ a, S a=linePacket (signed r (E a)) := by
  classical
  choose f hf he using fun a => classification hd (S a) t (hQ a) (hS a)
  let one : ↥d.divisors := ⟨1,Nat.mem_divisors.mpr ⟨one_dvd _,hs.ne_zero⟩⟩
  let r := f one
  let g (a : ↥d.divisors) (p : P d) := decide (f a p≠r p)
  have hg (a : ↥d.divisors) : f a=signed r (g a) := by
    funext p
    have h : (f a p)^2=(r p)^2 := (hf a p).trans (hf one p).symm
    have e := sq_eq_sq_iff_eq_or_eq_neg.mp h
    rcases e with e|e
    · simp [signed,g,e]
    · by_cases h' : f a p=r p
      · simp [signed,g,h']
      · simp [signed,g,h',e]
  have H (a : ↥d.divisors) : S a=linePacket (signed r (g a)) := (he a).trans (congrArg linePacket (hg a))
  have hI : Function.Injective g := by intro a b e; apply hi; rw [H a,H b,e]
  have hc : Fintype.card ↥d.divisors=Fintype.card (P d→Bool) := by
    rw [Fintype.card_coe,TunnellPrincipalGenus.divisor_card hs,Fintype.card_fun,Fintype.card_bool,Fintype.card_coe]
  have hB := (Fintype.bijective_iff_injective_and_card g).mpr ⟨hI,hc⟩
  exact ⟨r,hf one,Equiv.ofBijective g hB,H⟩
end
end TunnellAllRamifiedLines
end


/- TunnellRamifiedSwitch -/
section
namespace TunnellRamifiedSwitch
open TunnellShell TunnellHurwitz TunnellToricClass TunnellToricLocal TunnellEmbeddedIdeals TunnellRamifiedClasses
open TunnellIdealHNF TunnellQuaternion
noncomputable section
lemma middle_matrix {F : Type*} [Field F] {V : M2 F} (hV : V≠0) :
    ∃ X : M2 F, V*X*V≠0 := by
  classical
  obtain ⟨i,j,hh⟩ : ∃ i j, V i j≠0 := by by_contra! h; exact hV (Matrix.ext h)
  refine ⟨Matrix.single j i 1,?_⟩
  intro he
  have e := congrArg (fun M : M2 F => M i j) he
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply,Fin.sum_univ_two,Matrix.single] at e <;> aesop
lemma middle_nonzero {n p : ℕ} [Fact p.Prime] (hp : p≠2) (hn : Squarefree n) {v : Triple} (hv : v∈shell n) :
    ∃ x : Quaternion ℤ, red p (TunnellQuaternion.pure v*x*TunnellQuaternion.pure v)≠0 := by
  let M := localModel hp
  obtain ⟨X,h⟩ := middle_matrix (residue_nonzero M hn hv)
  refine ⟨lift p (M.f.symm X),?_⟩
  intro e; apply h
  rw [←residue_surj M X,←map_mul,←map_mul,residue_zero]; exact e
def glue {n : ℕ} {v : Triple} (hv : v∈shell n) (a : ℕ) : Lattice :=
  line (a:Q)⁻¹*(image hv (ram n a)*O*image hv (ram n a))
lemma nat_nonzero {a : ℕ} (h : a≠0) : (a:Q)≠0 := by
  intro e; have hh := congrArg QuaternionAlgebra.re e; exact h (by exact_mod_cast (hh : (a:ℚ)=0))
lemma clear_denom {n : ℕ} {v : Triple} (hv : v∈shell n) {a : ℕ} (ha : a≠0) {x : Q} (hx : x∈glue hv a) :
    (a:Q)*x∈O := by
  obtain ⟨y,hy,rfl⟩ := Submodule.mem_span_singleton_mul.mp hx
  rw [←mul_assoc,mul_inv_cancel₀ (nat_nonzero ha),one_mul]
  have hi : image hv (ram n a) ≤ O := by rintro _ ⟨z,_,rfl⟩; exact embed_integral n v hv z
  have hle : image hv (ram n a)*O*image hv (ram n a) ≤ O*O*O := mul_le_mul' (mul_le_mul_left hi O) hi
  rw [mul_O,mul_O] at hle
  exact hle hy
lemma contains_middle {n : ℕ} {v : Triple} (hv : v∈shell n) (a : ℕ) (x : Quaternion ℤ) :
    (a:Q)⁻¹*rat (TunnellQuaternion.pure v*x*TunnellQuaternion.pure v)∈glue hv a := by
  have h : TunnellHurwitz.pure v∈image hv (ram n a) :=
    ⟨Zsqrtd.sqrtd, (show principal (Zsqrtd.sqrtd:R n) ≤ ram n a from le_sup_right)
      (Ideal.mem_span_singleton_self _),embed_root n v hv⟩
  have hx : rat x∈O := integer_coords _ _ _ _
  apply Submodule.mem_span_singleton_mul.mpr
  refine ⟨_,Submodule.mul_mem_mul (Submodule.mul_mem_mul h hx) h,?_⟩
  simp only [rat_mul]; rfl
lemma double_rat {x : Q} (hx : x∈O) : ∃ y : Quaternion ℤ, (2:Q)*x=rat y := by
  obtain ⟨a,b,c,d,ha,hb,hc,hd⟩ := doubled_coords hx
  refine ⟨⟨a,b,c,d⟩,?_⟩
  rw [two_mul]; apply QuaternionAlgebra.ext
  all_goals dsimp only [Quaternion.re_add,Quaternion.imI_add,Quaternion.imJ_add,Quaternion.imK_add,rat]; linarith
lemma rat_injective : Function.Injective rat := by
  intro x y h; apply QuaternionAlgebra.ext
  · have e := congrArg QuaternionAlgebra.re h; change (x.re:ℚ)=y.re at e; exact_mod_cast e
  · have e := congrArg QuaternionAlgebra.imI h; change (x.imI:ℚ)=y.imI at e; exact_mod_cast e
  · have e := congrArg QuaternionAlgebra.imJ h; change (x.imJ:ℚ)=y.imJ at e; exact_mod_cast e
  · have e := congrArg QuaternionAlgebra.imK h; change (x.imK:ℚ)=y.imK at e; exact_mod_cast e
lemma rat_smul (a : ℤ) (x : Quaternion ℤ) : rat (a • x)=(a:Q)*rat x := by
  rw [zsmul_eq_mul,rat_mul]; rfl
lemma only_if_prime {n p a b : ℕ} [Fact p.Prime] (hp : p≠2) (hn : Squarefree n) {v : Triple} (hv : v∈shell n)
    (ha : a≠0) (hb : b≠0) (hd : p∣a) (e : glue hv a ≤ glue hv b) : p∣b := by
  obtain ⟨x,hx⟩ := middle_nonzero hp hn hv
  let z := TunnellQuaternion.pure v*x*TunnellQuaternion.pure v
  obtain ⟨y,ey⟩ := double_rat (clear_denom hv hb (e (contains_middle hv a x)))
  change 2*((b:Q)*((a:Q)⁻¹*rat z))=rat y at ey
  have H : rat (((2*b:ℕ):ℤ) • z)=rat ((a:ℤ) • y) := by
    rw [rat_smul,rat_smul,←ey]; push_cast
    have hc := Nat.cast_comm a (b:Q)
    have hcancel : (a:Q)*((a:Q)⁻¹*rat z)=rat z := by rw [←mul_assoc,mul_inv_cancel₀ (nat_nonzero ha),one_mul]
    have hs (q : Q) : (a:Q)*(2*((b:Q)*q))=2*((b:Q)*((a:Q)*q)) := by
      rw [←mul_assoc,Nat.cast_comm a (2:Q),mul_assoc,←mul_assoc (a:Q),hc,mul_assoc (b:Q)]
    rw [hs,hcancel,mul_assoc]
  have he := congrArg (red p) (rat_injective H)
  rw [red_smul,red_smul] at he; push_cast at he
  rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd,zero_smul] at he
  have h2 : (2:ZMod p)≠0 := by
    intro h; exact hp ((Nat.prime_dvd_prime_iff_eq (Fact.out:p.Prime) Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp h))
  exact (ZMod.natCast_eq_zero_iff _ _).mp ((mul_eq_zero.mp ((smul_eq_zero.mp he).resolve_right hx)).resolve_left h2)
theorem injective {d : ℕ} (hs : Squarefree d) (hn : Squarefree (2*d)) (hd : Odd d) {v : Triple} (hv : v∈shell (2*d)) :
    Function.Injective (fun a : ↥d.divisors => glue hv a.val) := by
  intro a b he
  obtain ⟨ha,hd0⟩ := Nat.mem_divisors.mp a.property
  obtain ⟨hb,_⟩ := Nat.mem_divisors.mp b.property
  have sa := hs.squarefree_of_dvd ha
  have sb := hs.squarefree_of_dvd hb
  have hp (p : ℕ) (h : p.Prime) (hh : p∣d) : p≠2 := by rintro rfl; exact (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr hh)
  have eq : a.val.primeFactors=b.val.primeFactors := by
    ext p; rw [Nat.mem_primeFactors,Nat.mem_primeFactors]
    constructor
    · rintro ⟨hh,had,_⟩; letI : Fact p.Prime := ⟨hh⟩
      exact ⟨hh,only_if_prime (hp p hh (had.trans ha)) hn hv sa.ne_zero sb.ne_zero had he.le,sb.ne_zero⟩
    · rintro ⟨hh,hbd,_⟩; letI : Fact p.Prime := ⟨hh⟩
      exact ⟨hh,only_if_prime (hp p hh (hbd.trans hb)) hn hv sb.ne_zero sa.ne_zero hbd he.ge,sa.ne_zero⟩
  apply Subtype.ext
  rw [←Nat.prod_primeFactors_of_squarefree sa,←Nat.prod_primeFactors_of_squarefree sb,eq]
end
end TunnellRamifiedSwitch
end


/- TunnellSwitchComponents -/
section
namespace TunnellSwitchComponents
open TunnellShell TunnellHurwitz TunnellToricClass TunnellToricLocal TunnellEmbeddedIdeals TunnellRamifiedClasses
open TunnellIdealHNF TunnellPairComponents TunnellCMGluing TunnellRamifiedSwitch TunnellIdealGenerators
noncomputable section
def ramData {n a : ℕ} (ha : 0<a) (h : a∣n) : Data n :=
  ⟨1,a,0,by decide,ha,ha,by simpa using (show (a:ℤ)∣n by exact_mod_cast h)⟩
lemma ram_as_hnf {n a : ℕ} (ha : 0<a) (h : a∣n) : ram n a=ideal (ramData ha h) := by
  simpa [ramData,principal] using (hnf_eq (ramData ha h) rfl).symm
lemma ram_conj {n a : ℕ} (ha : 0<a) (h : a∣n) : conjugate (ram n a)=ram n a := by
  rw [ram_as_hnf ha h]; ext z; change star z∈ideal (ramData ha h) ↔ _
  simp [mem_ideal,ramData]
lemma ram_norm {n a : ℕ} (ha : 0<a) (h : a∣n) : normI (ram n a)=a := by
  rw [ram_as_hnf ha h]; simpa [normI,ramData] using quotient_card (ramData ha h)
lemma ram_square {n a : ℕ} (hn : Squarefree n) (h2 : n%4=2) (ha : 0<a) (h : a∣n) :
    ram n a*ram n a=principal (a:TunnellIdealHNF.R n) := by
  simpa only [ram_conj ha h,ram_norm ha h] using norm_conjugate hn h2 (ram n a) (ram_ne_bot n a)
lemma line_central (u : Q) (hu : ∀ x:Q, u*x=x*u) (L : Lattice) : line u*L=L*line u := by
  ext q; rw [Submodule.mem_span_singleton_mul,Submodule.mem_mul_span_singleton]
  exact exists_congr fun x => and_congr_right fun _ => by rw [hu x]
lemma scalar_inf (u : Q) (hu : u≠0) (D W : Lattice) (h₁ : line u*W≤W) (h₂ : line u⁻¹*W≤W) :
    line u*D ⊓ W=line u*(D ⊓ W) := by
  ext q; simp only [Submodule.mem_inf,Submodule.mem_span_singleton_mul]
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hW⟩
    refine ⟨x,⟨hx,?_⟩,rfl⟩
    have h := h₂ (Submodule.mem_span_singleton_mul.mpr ⟨u*x,hW,rfl⟩)
    simpa only [←mul_assoc,inv_mul_cancel₀ hu,one_mul] using h
  · rintro ⟨x,⟨hx,hW⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,h₁ (Submodule.mem_span_singleton_mul.mpr ⟨x,hW,rfl⟩)⟩
lemma scalar_C {v : Triple} (a : ℕ) : line (a:Q)≤C v := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr (mem_C.mpr (Nat.cast_comm a _).symm))
lemma invscalar_C {v : Triple} (a : ℕ) : line (a:Q)⁻¹≤C v := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr
    (mem_C.mpr (show Commute ((TunnellHurwitz.pure) v) (a:Q) from (Nat.cast_comm a _).symm).inv_right₀))
lemma anti_ideal (J : Lattice) {n : ℕ} {v : Triple} (hv : v∈shell n) (hJ : J≤anti v) (I : Ideal (TunnellIdealHNF.R n)) :
    J*image hv I=image hv (conjugate I)*J := by
  have e (x : Q) (hx : x∈J) := anti_scalar hv (mem_anti.mp (hJ hx)) I
  apply le_antisymm
  · apply Submodule.mul_le.mpr
    intro x hx y hy
    have he : x*y∈line x*image hv I := Submodule.mem_span_singleton_mul.mpr ⟨y,hy,rfl⟩
    rw [e x hx] at he
    exact mul_le_mul_right (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) _ he
  · apply Submodule.mul_le.mpr
    intro y hy x hx
    have he : y*x∈image hv (conjugate I)*line x := Submodule.mem_mul_span_singleton.mpr ⟨y,hy,rfl⟩
    rw [←e x hx] at he
    exact mul_le_mul_left (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hx)) _ he
theorem fixed_components {n a : ℕ} (hn : Squarefree n) (h2 : n%4=2) {v : Triple} (hv : v∈shell n)
    (ha : 0<a) (hd : a∣n) :
    glue hv a ⊓ C v=J v v ∧ glue hv a ⊓ anti v=J v (-v) := by
  let I := image hv (ram n a)
  let U := line (a:Q)⁻¹
  have hu := nat_nonzero ha.ne'
  have hU : U≤C v := invscalar_C _
  have hI : I≤C v := center_image hv _
  have hII : I*I=line (a:Q)*J v v := by
    change image hv _*image hv _=_
    rw [←image_mul,ram_square hn h2 ha hd,principal,image_principal hn h2 hv,map_natCast]
  have hU₁ : U*line (a:Q)=1 := two_sided_inverse hu
  have hRI : I*J v v=I := by rw [←image_order hn h2 hv,←image_mul,Ideal.mul_top]
  let K := U*I
  have hK : K≤C v := (mul_le_mul' hU hI).trans (mul_C v)
  have hKI : K*I=J v v := by change U*I*I=_; rw [mul_assoc,hII,←mul_assoc,hU₁,one_mul]
  have hIK := (ideals_comm hn hv hI hK).trans hKI
  obtain ⟨e₁,e₂⟩ := inter_components hI hK hI hK hIK hKI hIK hKI hRI
  have s₁ := scalar_inf (a:Q)⁻¹ (inv_ne_zero hu) (I*O*I) (C v)
    ((mul_le_mul_left hU _).trans (mul_C v)) (by rw [inv_inv]; exact (mul_le_mul_left (scalar_C a) _).trans (mul_C v))
  have s₂ := scalar_inf (a:Q)⁻¹ (inv_ne_zero hu) (I*O*I) (anti v)
    ((mul_le_mul_left hU _).trans (C_anti v)) (by rw [inv_inv]; exact (mul_le_mul_left (scalar_C a) _).trans (C_anti v))
  change U*(I*O*I) ⊓ C v=_ ∧ U*(I*O*I) ⊓ anti v=_
  rw [s₁,s₂,e₁,e₂]
  have hanti : J v (-v)≤anti v := by rw [←anti_order]; exact inf_le_right
  have hcomm : J v (-v)*I=I*J v (-v) := by simpa only [ram_conj ha hd] using anti_ideal (J v (-v)) hv hanti (ram n a)
  have hR : J v v*J v (-v)=J v (-v) := by rw [←J_opposite,J_comp hn h2 (shell_neg hv) hv,J_opposite]
  constructor
  · exact (mul_assoc ..).symm.trans hKI
  · change U*(I*J v (-v)*I)=_
    rw [mul_assoc I,hcomm,←mul_assoc I,←mul_assoc U,←mul_assoc U,hKI,hR]
end
end TunnellSwitchComponents
end


/- TunnellFilteredGlue -/
section
namespace TunnellFilteredGlue
open TunnellShell TunnellHurwitz TunnellToricClass TunnellToricLocal TunnellEmbeddedIdeals TunnellRamifiedClasses
open TunnellIdealHNF TunnellPairComponents TunnellCMGluing TunnellRamifiedSwitch TunnellSwitchComponents
noncomputable section
def binary (v : Triple) : Lattice := J v v ⊔ line 2*J v (-v)
def filt (d : ℕ) (v : Triple) (D : Lattice) : Lattice :=
  D ⊓ (binary v).comap ((AddMonoidHom.mulLeft (d:Q)).toIntLinearMap)
lemma mem_filt (d : ℕ) (v : Triple) (D : Lattice) (x : Q) :
    x∈filt d v D ↔ x∈D ∧ (d:Q)*x∈binary v := Iff.rfl
lemma stable {n a : ℕ} (hn : Squarefree n) (h2 : n%4=2) {v : Triple} (hv : v∈shell n) :
    J v v*glue hv a*J v v=glue hv a := by
  let I := image hv (ram n a)
  let U := line (a:Q)⁻¹
  have he : I*J v v=I := by rw [←image_order hn h2 hv,←image_mul,Ideal.mul_top]
  have he' : J v v*I=I := by rw [←image_order hn h2 hv,←image_mul,Ideal.top_mul]
  have hc : J v v*U=U*J v v := ideals_comm hn hv (fun _ h => mem_C.mpr h.2) (invscalar_C a)
  change J v v*(U*(I*O*I))*J v v=_
  calc _=U*((J v v*I)*O*(I*J v v)) := by rw [←mul_assoc (J v v),hc]; simp only [mul_assoc]
       _=_ := by rw [he,he']; rfl
lemma eight_mem {d a : ℕ} (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {v : Triple} (hv : v∈shell (2*d))
    (ha : 0<a) (had : a∣2*d) {x : Q} (hx : x∈glue hv a) : (8:Q)*x∈filt d v (glue hv a) := by
  obtain ⟨l,hl,r,hr,e⟩ := integral_projectors hv (stable hn h2 hv).le hx
  have hc := fixed_components hn h2 hv ha had
  rw [hc.1] at hl; rw [hc.2] at hr
  have el : 2*l∈J v v := by simpa only [zsmul_eq_mul,Int.cast_ofNat] using (J v v).smul_mem (2:ℤ) hl
  have er : 2*r∈line 2*J v (-v) := Submodule.mem_span_singleton_mul.mpr ⟨r,hr,rfl⟩
  have e' : (d:Q)*(8*x)=2*l+2*r := by
    calc _=2*(((2*(2*d):ℕ):Q)*x) := by push_cast; noncomm_ring
         _=_ := by rw [e,mul_add]
  rw [mem_filt]; constructor
  · simpa only [zsmul_eq_mul,Int.cast_ofNat] using (glue hv a).smul_mem (8:ℤ) hx
  · rw [e']; exact Submodule.add_mem_sup el er
lemma contains_scalar {n a : ℕ} {v : Triple} (hv : v∈shell n) (ha : a≠0) {x : Q} (hx : x∈O) : (a:Q)*x∈glue hv a := by
  have h : (a:Q)∈image hv (ram n a) := ⟨a,(show principal (a:TunnellIdealHNF.R n) ≤ ram n a from le_sup_left)
    (Ideal.mem_span_singleton_self _),map_natCast (embed n v hv) a⟩
  apply Submodule.mem_span_singleton_mul.mpr
  refine ⟨_,Submodule.mul_mem_mul (Submodule.mul_mem_mul h hx) h,?_⟩
  rw [←mul_assoc,←mul_assoc,inv_mul_cancel₀ (nat_nonzero ha),one_mul,Nat.cast_comm a]
lemma recover {d a b : ℕ} (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {v : Triple} (hv : v∈shell (2*d))
    (ha : 0<a) (hb : 0<b) (had : a∣2*d) (hab : Odd (a*b))
    (h : filt d v (glue hv a) ≤ filt d v (glue hv b)) : glue hv a ≤ glue hv b := by
  obtain ⟨u,w,eh⟩ := ((Nat.coprime_two_right.mpr hab).pow_right 3 : Nat.Coprime (a*b) 8).isCoprime
  intro x hx
  have h8 := (h (eight_mem hn h2 hv ha had hx)).1
  have h₁ := contains_scalar hv hb.ne' (clear_denom hv ha.ne' hx)
  have e : (u:ℤ)*(a*b)+w*8=1 := by exact_mod_cast eh
  have e' := congrArg (fun k:ℤ => (k:Q)) e
  push_cast at e'
  have eQ : x=(u:Q)*((b:Q)*((a:Q)*x))+(w:Q)*(8*x) := by
    calc x=(((u:Q)*(a*b)+w*8)*x) := by rw [e',one_mul]
         _=_ := by rw [Nat.cast_comm a (b:Q)]; noncomm_ring
  rw [eQ]
  exact (glue hv b).add_mem (by simpa only [zsmul_eq_mul] using (glue hv b).smul_mem u h₁)
    (by simpa only [zsmul_eq_mul] using (glue hv b).smul_mem w h8)
theorem injective {d : ℕ} (hs : Squarefree d) (hn : Squarefree (2*d)) (hd : Odd d) (h2 : (2*d)%4=2)
    {v : Triple} (hv : v∈shell (2*d)) : Function.Injective (fun a : ↥d.divisors => filt d v (glue hv a.val)) := by
  intro a b e
  obtain ⟨ha,h0⟩ := Nat.mem_divisors.mp a.property
  obtain ⟨hb,_⟩ := Nat.mem_divisors.mp b.property
  have ha0 := Nat.pos_of_dvd_of_pos ha (Nat.pos_of_ne_zero h0)
  have hb0 := Nat.pos_of_dvd_of_pos hb (Nat.pos_of_ne_zero h0)
  have hO {k : ℕ} (hk : k∣d) : Odd k := Nat.not_even_iff_odd.mp fun hh => (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr ((even_iff_two_dvd.mp hh).trans hk))
  apply TunnellRamifiedSwitch.injective hs hn hd hv
  exact le_antisymm (recover hn h2 hv ha0 hb0 (ha.trans (dvd_mul_left ..)) ((hO ha).mul (hO hb)) e.le)
    (recover hn h2 hv hb0 ha0 (hb.trans (dvd_mul_left ..)) ((hO hb).mul (hO ha)) e.ge)
end
end TunnellFilteredGlue
end


/- TunnellIdealGluings -/
section
namespace TunnellIdealGluings
open TunnellShell TunnellHurwitz TunnellToricClass TunnellToricLocal TunnellEmbeddedIdeals TunnellRamifiedClasses
open TunnellIdealHNF TunnellPairComponents TunnellCMGluing TunnellRamifiedSwitch TunnellSwitchComponents TunnellFilteredGlue
noncomputable section
def bimod (v : Triple) (D : Lattice) := J v v*D*J v v=D
lemma bimod_iff {v : Triple} {D : Lattice} : bimod v D ↔ J v v*D*J v v≤D := by
  refine ⟨fun h => h.le,fun h => le_antisymm h ?_⟩
  have hR : 1≤J v v := Submodule.one_le.mpr (one_J v)
  calc D=1*D*1 := by rw [one_mul,mul_one]
       _≤_ := mul_le_mul' (mul_le_mul_left hR D) hR
lemma bimod_inf {v : Triple} {D E : Lattice} (hd : bimod v D) (he : bimod v E) : bimod v (D ⊓ E) := by
  apply bimod_iff.mpr; apply le_inf
  · exact (mul_le_mul_left (mul_le_mul_right inf_le_left _) _).trans hd.le
  · exact (mul_le_mul_left (mul_le_mul_right inf_le_right _) _).trans he.le
lemma bimod_sup {v : Triple} {D E : Lattice} (hd : bimod v D) (he : bimod v E) : bimod v (D ⊔ E) := by
  change _=_; rw [Submodule.mul_sup,Submodule.sup_mul,hd,he]
lemma bimod_scalar {v : Triple} {D : Lattice} (hd : bimod v D) (u : Q) (hu : ∀ q:Q,u*q=q*u) : bimod v (line u*D) := by
  unfold bimod
  rw [←mul_assoc,←line_central u hu (J v v)]
  simpa only [mul_assoc] using congrArg (line u*·) hd
lemma cutoff {d : ℕ} (hd : d≠0) (v : Triple) (D : Lattice) :
    filt d v D=D ⊓ line (d:Q)⁻¹*binary v := by
  ext x; rw [mem_filt,Submodule.mem_inf,Submodule.mem_span_singleton_mul]
  apply and_congr_right; intro _
  constructor
  · intro h; exact ⟨(d:Q)*x,h,by rw [←mul_assoc,inv_mul_cancel₀ (nat_nonzero hd),one_mul]⟩
  · rintro ⟨y,hy,rfl⟩; rw [←mul_assoc,mul_inv_cancel₀ (nat_nonzero hd),one_mul]; exact hy
lemma binary_stable {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {v : Triple} (hv : v∈shell n) :
    bimod v (binary v) := by
  have hr : bimod v (J v v) := by unfold bimod; rw [J_comp hn h2 hv hv,J_comp hn h2 hv hv]
  have he : J v v*J v (-v)=J v (-v) := by rw [←J_opposite,J_comp hn h2 (shell_neg hv) hv,J_opposite]
  have hs : bimod v (J v (-v)) := by unfold bimod; rw [he,J_comp hn h2 hv hv]
  exact bimod_sup hr (bimod_scalar hs 2 (fun q => by noncomm_ring))
lemma filt_stable {d : ℕ} (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {v : Triple} (hv : v∈shell (2*d)) {D : Lattice} (hD : bimod v D) :
    bimod v (filt d v D) := by
  rw [cutoff (by omega)]
  exact bimod_inf hD (bimod_scalar (binary_stable hn h2 hv) _ (fun q => (show Commute (d:Q) q from Nat.cast_comm d q).inv_left₀))
def sandwich {n : ℕ} {v : Triple} (hv : v∈shell n) (A B : Ideal (TunnellIdealHNF.R n)) (D : Lattice) :=
  image hv A*D*image hv B
lemma cancel {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {v : Triple} (hv : v∈shell n) {A B : Ideal (TunnellIdealHNF.R n)}
    (hA : A≠⊥) (hB : B≠⊥) {D E : Lattice} (hD : bimod v D) (hE : bimod v E)
    (eq : sandwich hv A B D=sandwich hv A B E) : D=E := by
  obtain ⟨A',hA',eA⟩ := (image_isIdeal hn h2 hv A hA).2.2.2
  obtain ⟨B',_,eB⟩ := (image_isIdeal hn h2 hv B hB).2.2.2
  have eA' := (ideals_comm hn hv hA' (center_image hv A)).trans eA
  have tr (L : Lattice) : A'*sandwich hv A B L*B'=J v v*L*J v v := by
    calc _=(A'*image hv A)*L*(image hv B*B') := by simp only [sandwich,mul_assoc]
         _=_ := by rw [eA',eB]
  exact hD.symm.trans ((tr D).symm.trans ((congrArg (fun L => A'*L*B') eq).trans ((tr E).trans hE)))
theorem distinct {d : ℕ} (hs : Squarefree d) (hn : Squarefree (2*d)) (hd : Odd d) (h2 : (2*d)%4=2) {v : Triple} (hv : v∈shell (2*d))
    {A B : Ideal (TunnellIdealHNF.R (2*d))} (hA : A≠⊥) (hB : B≠⊥) :
    Function.Injective (fun a : ↥d.divisors => sandwich hv A B (filt d v (glue hv a.val))) := by
  intro a b he
  apply TunnellFilteredGlue.injective hs hn hd h2 hv
  exact cancel hn h2 hv hA hB (filt_stable hn h2 hv (stable hn h2 hv)) (filt_stable hn h2 hv (stable hn h2 hv)) he
theorem base_change {n : ℕ} {v : Triple} (hv : v∈shell n) (a : ℕ) (A B : Ideal (TunnellIdealHNF.R n)) :
    sandwich hv A B (glue hv a)=line (a:Q)⁻¹*sandwich hv (A*ram n a) (ram n a*B) O := by
  have hc (q : Q) : (a:Q)⁻¹*q=q*(a:Q)⁻¹ := (show Commute (a:Q) q from Nat.cast_comm a q).inv_left₀
  unfold sandwich glue; rw [image_mul,image_mul]
  rw [←mul_assoc (image hv A),←line_central _ hc (image hv A)]
  simp only [mul_assoc]
lemma O_extends {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {v s : Triple} (hv : v∈shell n) (hs : s∈shell n) :
    O*J v s=O := by
  have hle : (1:Lattice)≤J s v*J v s := by rw [J_comp hn h2 hv hs]; exact Submodule.one_le.mpr (one_J _)
  have hle' : (1:Lattice)≤O*J v s := hle.trans (mul_le_mul_left (show J s v≤O from fun _ h => h.1) _)
  apply le_antisymm ((mul_le_mul_right (show J v s≤O from fun _ h => h.1) _).trans mul_O.le)
  calc O=O*1 := (mul_one _).symm
       _≤O*(O*J v s) := mul_le_mul_right hle' _
       _=_ := by rw [←mul_assoc,mul_O]
theorem framed {n : ℕ} (hn : Squarefree n) (h2 : n%4=2) {v s t : Triple} (hv : v∈shell n) (hs : s∈shell n) (ht : t∈shell n)
    {A B : Ideal (TunnellIdealHNF.R n)} {a b : Q} (eB : image hv B=line b*J v t) (eA : image hv A=line a*J v s) :
    sandwich hv B (conjugate A) O=line b*O*line (star a) := by
  unfold sandwich; rw [eB,conj_frame hv eA,mul_assoc (line b) (J v t),J_extends hn h2 hv ht]
  calc _=line b*(O*J s v)*line (star a) := by simp only [mul_assoc]
       _=_ := by rw [O_extends hn h2 hs hv]
end
end TunnellIdealGluings
end


/- TunnellTwoProjection -/
section
namespace TunnellTwoProjection
open TunnellHurwitz TunnellToricClass TunnellShell TunnellToricLocal
noncomputable section
def filt (d : ℕ) (v w : Triple) (q : Q) := (2*(d:Q))*q+(TunnellHurwitz.pure) w*q*(TunnellHurwitz.pure) v
def admits (d : ℕ) (v w : Triple) (q : Q) := ∃ x∈J v w, ∃ y∈O,
    (TunnellHurwitz.pure) w*y= -(y*(TunnellHurwitz.pure) v) ∧ (d:Q)*q=x+2*y
lemma squares {d : ℕ} {v : Triple} (hv : v∈shell (2*d)) : (TunnellHurwitz.pure) v*(TunnellHurwitz.pure) v= -(2*(d:Q)) := by simpa using pure_square hv
lemma filt_left {d : ℕ} {v w : Triple} (hw : w∈shell (2*d)) (q : Q) :
    (TunnellHurwitz.pure) w*filt d v w q=(d:Q)*((TunnellHurwitz.pure) w*q-q*(TunnellHurwitz.pure) v)*2 := by
  have h₁ : (TunnellHurwitz.pure) w*((2*(d:Q))*q)=(2*(d:Q))*((TunnellHurwitz.pure) w*q) := by rw [←mul_assoc,show (2*(d:Q))=((2*d:ℕ):Q) by push_cast; rfl,Nat.commute_cast,mul_assoc]
  have h₂ : (TunnellHurwitz.pure) w*((TunnellHurwitz.pure) w*q*(TunnellHurwitz.pure) v)= -(2*(d:Q))*q*(TunnellHurwitz.pure) v := by rw [←mul_assoc,←mul_assoc,squares hw]
  rw [filt,mul_add,h₁,h₂]; noncomm_ring
lemma filt_anti {d : ℕ} {v w : Triple} (hv : v∈shell (2*d)) (hw : w∈shell (2*d)) (q : Q) :
    (TunnellHurwitz.pure) w*filt d v w q= -(filt d v w q*(TunnellHurwitz.pure) v) := by
  have h₃ : ((TunnellHurwitz.pure) w*q*(TunnellHurwitz.pure) v)*(TunnellHurwitz.pure) v = -((2*(d:Q))*((TunnellHurwitz.pure) w*q)) := by
    rw [mul_assoc ((TunnellHurwitz.pure) w*q),squares hv,mul_neg,show (2*(d:Q))=((2*d:ℕ):Q) by push_cast; rfl,Nat.commute_cast]
  rw [filt_left hw,filt,add_mul,h₃]; noncomm_ring
theorem admits_iff {d : ℕ} {v w : Triple} (hv : v∈shell (2*d)) (hw : w∈shell (2*d))
    (hd : 0<d) {q : Q} (hq : q∈O) : admits d v w q ↔ ∃ b∈O, filt d v w q=8*b := by
  have hdq : (d:Q)≠0 := by intro e; have H:=congrArg QuaternionAlgebra.re e; change (d:ℚ)=0 at H; exact hd.ne' (by exact_mod_cast H)
  constructor
  · rintro ⟨x,hx,y,hy,ey,e⟩
    refine ⟨y,hy,mul_left_cancel₀ hdq ?_⟩
    have hd' (r : Q) : (d:Q)*r=r*d := Nat.cast_comm d r
    have hx' : ((TunnellHurwitz.pure) w*x)*(TunnellHurwitz.pure) v = -((2*(d:Q))*x) := by
      rw [hx.2,mul_assoc,squares hv,mul_neg,show 2*(d:Q)=((2*d:ℕ):Q) by push_cast; rfl,Nat.commute_cast]
    have hy' : ((TunnellHurwitz.pure) w*y)*(TunnellHurwitz.pure) v = (2*(d:Q))*y := by
      rw [ey,neg_mul,mul_assoc,squares hv,mul_neg,neg_neg,show 2*(d:Q)=((2*d:ℕ):Q) by push_cast; rfl,Nat.commute_cast]
    calc (d:Q)*filt d v w q=(2*(d:Q))*((d:Q)*q)+(TunnellHurwitz.pure) w*((d:Q)*q)*(TunnellHurwitz.pure) v := by
           rw [filt,mul_add]; congr 1
           · noncomm_ring
           · rw [←mul_assoc,←mul_assoc,hd' ((TunnellHurwitz.pure) w),mul_assoc, mul_assoc]; simp only [mul_assoc]
         _=(d:Q)*(8*y) := by rw [e]; noncomm_ring [hx',hy']
  · rintro ⟨b,hb,e⟩
    have h8 : (8:Q)≠0 := by intro he; have H:=congrArg QuaternionAlgebra.re he; change (8:ℚ)=0 at H; norm_num at H
    have h2 : (2:Q)≠0 := by intro he; have H:=congrArg QuaternionAlgebra.re he; change (2:ℚ)=0 at H; norm_num at H
    have hC (k : ℕ) (s t : Q) : s*((k:Q)*t)=(k:Q)*(s*t) := by rw [←mul_assoc,Nat.commute_cast,mul_assoc]
    have hc8 (s t : Q) : s*(8*t)=8*(s*t) := by noncomm_ring
    have hc2 (s t : Q) : s*(2*t)=2*(s*t) := by noncomm_ring
    have hb' := filt_anti hv hw q
    rw [e,hc8, mul_assoc,←mul_neg] at hb'
    have ha := mul_left_cancel₀ h8 hb'
    have hF := filt_left hw (v:=v) q
    rw [e,hc8] at hF
    have hF' : (2:Q)*(4*((TunnellHurwitz.pure) w*b))=2*((d:Q)*((TunnellHurwitz.pure) w*q-q*(TunnellHurwitz.pure) v)) := by calc
      _=8*((TunnellHurwitz.pure) w*b) := by noncomm_ring
      _=_ := by rw [hF]; noncomm_ring
    have hD := mul_left_cancel₀ h2 hF'
    let x := (d:Q)*q-2*b
    have hx : x∈O := O.sub_mem (by simpa only [zsmul_eq_mul,Int.cast_natCast] using O.smul_mem (d:ℤ) hq) (by simpa only [zsmul_eq_mul,Int.cast_ofNat] using O.smul_mem (2:ℤ) hb)
    refine ⟨x,⟨hx,?_⟩,b,hb,ha,by dsimp [x]; abel⟩
    change (TunnellHurwitz.pure) w*((d:Q)*q-2*b)=((d:Q)*q-2*b)*(TunnellHurwitz.pure) v
    rw [mul_sub,sub_mul,hC,hc2,mul_assoc,mul_assoc]
    have h := congrArg (fun t:Q => t+(d:Q)*(q*(TunnellHurwitz.pure) v)) hD
    rw [mul_sub,sub_add_cancel] at h
    rw [←h,ha]; noncomm_ring
end
end TunnellTwoProjection
end


/- TunnellOddGlueCoordinates -/
section
namespace TunnellOddGlueCoordinates
open TunnellOddDiscriminant
noncomputable section
variable {p : ℕ} [Fact p.Prime]
def redPair (x : ℤ×ℤ) : (ZMod p)×(ZMod p) := (x.1,x.2)
def coord (A : ℤ) (x : ℤ×ℤ) : (ZMod p) := (x.2:(ZMod p))/(A:(ZMod p))
lemma coordinates {A B C n : ℤ} (hdet : A*C-B^2=n) (hn : (p:ℤ)∣n) (ha : (A:(ZMod p))≠0) (x : ℤ×ℤ)
    (hx : pairing (A:(ZMod p)) B C (redPair x)=0) :
    let r := coord (p:=p) A x
    ∃ u v : ℤ, x.1= -B*(r.val:ℤ)+(p:ℤ)*u ∧ x.2=A*(r.val:ℤ)+(p:ℤ)*v := by
  have h : (A:(ZMod p))*(C:(ZMod p))-(B:(ZMod p))^2=0 := by
    have e := congrArg (fun z:ℤ => (z:(ZMod p))) hdet; push_cast at e; rw [e]; exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hn
  obtain ⟨r,hr⟩ := (radical ha h (redPair x)).mp hx
  have he₂ := congrArg Prod.snd hr
  change (x.2:(ZMod p))=A*r at he₂
  have he : coord (p:=p) A x=r := by unfold coord; rw [he₂]; field_simp
  dsimp only; rw [he]
  have e₁ : ((-B*(r.val:ℤ):ℤ):(ZMod p))=x.1 := by
    push_cast; rw [ZMod.natCast_zmod_val]; exact (congrArg Prod.fst hr).symm
  have e₂ : ((A*(r.val:ℤ):ℤ):(ZMod p))=x.2 := by push_cast; rw [ZMod.natCast_zmod_val]; exact he₂.symm
  obtain ⟨u,hu⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp e₁
  obtain ⟨v,hv⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp e₂
  exact ⟨u,v,by linarith,by linarith⟩
lemma residue {A B C n : ℤ} (hdet : A*C-B^2=n) (hn : (p:ℤ)∣n) (ha : (A:(ZMod p))≠0) (x : ℤ×ℤ)
    (hx : pairing (A:(ZMod p)) B C (redPair x)=0) :
    ∃ k : ℤ, quad A B C x=A*n*((coord (p:=p) A x).val:ℤ)^2+(p:ℤ)^2*k := by
  let r := (coord (p:=p) A x).val
  obtain ⟨u,v,eu,ev⟩ := coordinates hdet hn ha x hx
  change x.1= -B*(r:ℤ)+p*u at eu
  change x.2=A*(r:ℤ)+p*v at ev
  obtain ⟨m,hm⟩ := hn
  refine ⟨quad A B C (u,v)+2*m*r*v,?_⟩
  unfold quad; rw [eu,ev]; change _=A*n*(r:ℤ)^2+_
  linear_combination (A*(r:ℤ)^2+2*(p:ℤ)*r*v)*hdet+2*(p:ℤ)*r*v*hm
lemma square_condition {A B C D E G : ℤ} {n : ℕ} (hAC : A*C-B^2=n) (hDG : D*G-E^2=n)
    (hn : Squarefree n) (hp : p∣n) (hA : (A:(ZMod p))≠0) (hD : (D:(ZMod p))≠0) (x y : ℤ×ℤ)
    (hx : pairing (A:(ZMod p)) B C (redPair x)=0) (hy : pairing (D:(ZMod p)) E G (redPair y)=0)
    (hQ : (p:ℤ)^2 ∣ quad A B C x+4*quad D E G y) :
    (coord (p:=p) A x)^2=(-(4:(ZMod p))*D/A)*(coord (p:=p) D y)^2 := by
  obtain ⟨k,hk⟩ := residue hAC (by exact_mod_cast hp) hA x hx
  obtain ⟨l,hl⟩ := residue hDG (by exact_mod_cast hp) hD y hy
  obtain ⟨m,hm⟩ := hQ
  let r := (coord (p:=p) A x).val
  let s := (coord (p:=p) D y).val
  have en : (n:ℤ)=(p:ℤ)*(n/p:ℕ) := by exact_mod_cast (Nat.mul_div_cancel' hp).symm
  have e : ((n/p:ℕ):ℤ)*(A*(r:ℤ)^2+4*D*(s:ℤ)^2)=(p:ℤ)*(m-k-4*l) := by
    apply mul_left_cancel₀ (a:=(p:ℤ)) (by exact_mod_cast (Fact.out:p.Prime).ne_zero)
    dsimp only [r,s]; rw [hk,hl,en] at hm; linear_combination hm
  have e' := congrArg (fun z:ℤ => (z:(ZMod p))) e
  simp only [Int.cast_mul,Int.cast_add,Int.cast_ofNat,Int.cast_sub,Int.cast_pow,Int.cast_natCast] at e'; rw [ZMod.natCast_self,zero_mul] at e'
  dsimp only [r,s] at e'; rw [ZMod.natCast_zmod_val,ZMod.natCast_zmod_val] at e'
  have h := (mul_eq_zero.mp e').resolve_left (quotient_nonzero hn hp)
  field_simp
  linear_combination h
lemma radical_of_values {A B C : ℤ} (a d : ℕ) (hd : d≠0) (h : p∣d) (hu : ((2*a:ℕ):(ZMod p))≠0)
    (x : ℤ×ℤ) (hr : ∀ y:ℤ×ℤ, (d:ℤ)^2∣(a:ℤ)*(quad A B C (x+(d:ℤ) • y)-quad A B C x)) :
    pairing (A:(ZMod p)) B C (redPair x)=0 := by
  have e₁ := hr (1,0)
  have e₂ := hr (0,1)
  obtain ⟨u,eu⟩ := e₁; obtain ⟨v,ev⟩ := e₂
  change (a:ℤ)*(A*(x.1+d*1)^2+2*B*(x.1+d*1)*(x.2+d*0)+C*(x.2+d*0)^2-quad A B C x)=_ at eu
  change (a:ℤ)*(A*(x.1+d*0)^2+2*B*(x.1+d*0)*(x.2+d*1)+C*(x.2+d*1)^2-quad A B C x)=_ at ev
  have ex : (2*a:ℤ)*(A*x.1+B*x.2)=(d:ℤ)*(u-a*A) := by
    apply mul_left_cancel₀ (a:=(d:ℤ)) (by exact_mod_cast hd); unfold quad at eu; linear_combination eu
  have ey : (2*a:ℤ)*(B*x.1+C*x.2)=(d:ℤ)*(v-a*C) := by
    apply mul_left_cancel₀ (a:=(d:ℤ)) (by exact_mod_cast hd); unfold quad at ev; linear_combination ev
  have ez := (ZMod.natCast_eq_zero_iff _ _).mpr h
  have ef := congrArg (fun z:ℤ => (z:(ZMod p))) ex; have eg := congrArg (fun z:ℤ => (z:(ZMod p))) ey
  push_cast at hu ef eg; rw [ez,zero_mul] at ef eg
  exact Prod.ext ((mul_eq_zero.mp ef).resolve_left hu) ((mul_eq_zero.mp eg).resolve_left hu)
end
end TunnellOddGlueCoordinates
end


/- TunnellGlueMaximal -/
section
namespace TunnellGlueMaximal
open TunnellHurwitz TunnellToricClass TunnellShell TunnellToricLocal TunnellQuaternion TunnellPairComponents
open TunnellTwoProjection TunnellRamifiedSwitch TunnellIdealGluings
noncomputable section
lemma middle_two {F : Type*} [Field F] {V W : M2 F} (hv : V≠0) (hw : W≠0) :
    ∃ X : M2 F, W*X*V≠0 := by
  classical
  obtain ⟨i,j,hij⟩ : ∃ i j, W i j≠0 := by by_contra! h; exact hw (Matrix.ext h)
  obtain ⟨k,l,hkl⟩ : ∃ k l, V k l≠0 := by by_contra! h; exact hv (Matrix.ext h)
  refine ⟨Matrix.single j k 1,fun he => ?_⟩
  have e := congrArg (fun M:M2 F => M i l) he
  have h : (W*(Matrix.single j k 1:M2 F)*V) i l=W i j*V k l := by
    rw [Matrix.mul_apply,Finset.sum_eq_single k]
    · rw [Matrix.mul_single_apply_same]; simp
    · intro a _ ha; rw [Matrix.mul_single_apply_of_ne 1 j k i a ha W]; simp
    · simp
  exact (mul_ne_zero hij hkl) (h.symm.trans e)
def pairL (s t : Triple) : Lattice := J s t ⊔ line 2*J (-s) t
lemma middle_of_mem {n : ℕ} {s t : Triple} (hs : s∈shell n) {x : Q} (hx : x∈pairL s t) :
    ∃ y∈O, (TunnellHurwitz.pure) t*x*(TunnellHurwitz.pure) s=(n:Q)*y := by
  obtain ⟨u,hu,z,hz,rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨v,hv,rfl⟩ := Submodule.mem_span_singleton_mul.mp hz
  have he : (TunnellHurwitz.pure) t*v= -(v*(TunnellHurwitz.pure) s) := by simpa [pure_neg] using hv.2
  have e₁ : (TunnellHurwitz.pure) t*u*(TunnellHurwitz.pure) s= -(n:Q)*u := by rw [hu.2,mul_assoc,pure_square hs,mul_neg,←Nat.cast_comm n u,neg_mul]
  have e₂ : (TunnellHurwitz.pure) t*v*(TunnellHurwitz.pure) s=(n:Q)*v := by rw [he,neg_mul,mul_assoc,pure_square hs,mul_neg,neg_neg,←Nat.cast_comm n v]
  have hz : 2*v∈O := by simpa only [zsmul_eq_mul,Int.cast_ofNat] using O.smul_mem (2:ℤ) hv.1
  refine ⟨-u+2*v,O.add_mem (O.neg_mem hu.1) hz,?_⟩
  calc _=(TunnellHurwitz.pure) t*u*(TunnellHurwitz.pure) s+2*((TunnellHurwitz.pure) t*v*(TunnellHurwitz.pure) s) := by noncomm_ring
       _=_ := by rw [e₁,e₂]; noncomm_ring
lemma reduction_forces {p b n : ℕ} [Fact p.Prime] (hp2 : p≠2) (hb : ¬p∣b) (hp : p∣n) {x : Quaternion ℤ}
    (y : Q) (hy : y∈O) (e : (b:Q)*rat x=(n:Q)*y) : red p x=0 := by
  obtain ⟨z,ez⟩ := double_rat hy
  have he : rat (((2*b:ℕ):ℤ) • x)=rat ((n:ℤ) • z) := by
    rw [rat_smul,rat_smul,←ez]; push_cast
    calc _=2*((b:Q)*rat x) := by noncomm_ring
         _=_ := by rw [e]; noncomm_ring
  have hh := congrArg (red p) (rat_injective he); rw [red_smul,red_smul] at hh; push_cast at hh
  rw [(ZMod.natCast_eq_zero_iff _ _).mpr hp,zero_smul] at hh
  have h2 : (2:ZMod p)≠0 := by intro h; exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out:p.Prime) Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 p).mp h))
  exact (smul_eq_zero.mp hh).resolve_left (mul_ne_zero h2 ((ZMod.natCast_eq_zero_iff _ _).not.mpr hb))
theorem nonzero {d p : ℕ} [Fact p.Prime] (hp : p∣d) (hp2 : p≠2) (hn : Squarefree (2*d)) (hd : 0<d)
    {s t : Triple} (hs : s∈shell (2*d)) (ht : t∈shell (2*d)) :
    ∃ q∈O, admits d s t q ∧ ((d/p:ℕ):Q)*q∉pairL s t := by
  let M := localModel hp2
  obtain ⟨X,hX⟩ := middle_two (residue_nonzero M hn hs) (residue_nonzero M hn ht)
  let z := lift p (M.f.symm X)
  let m := TunnellQuaternion.pure t*z*TunnellQuaternion.pure s
  have hm : red p m≠0 := by
    intro he; apply hX; rw [←residue_surj M X,←map_mul,←map_mul,residue_zero]; exact he
  have hz : rat z∈O := integer_coords _ _ _ _
  have h8 : 8*rat z∈O := by simpa only [zsmul_eq_mul,Int.cast_ofNat] using O.smul_mem (8:ℤ) hz
  refine ⟨8*rat z,h8,(admits_iff hs ht hd h8).mpr ?_,?_⟩
  · refine ⟨filt d s t (rat z),O.add_mem ?_ (order.mul_mem (order.mul_mem (pure_mem t) hz) (pure_mem s)),?_⟩
    · change 2*(d:Q)*rat z∈O
      simpa only [zsmul_eq_mul,Int.cast_mul,Int.cast_ofNat,Int.cast_natCast] using O.smul_mem (2*(d:ℤ)) hz
    · unfold filt; noncomm_ring
  · intro he
    obtain ⟨y,hy,ey⟩ := middle_of_mem hs he
    have H : (((d/p)*8:ℕ):Q)*rat m=((2*d:ℕ):Q)*y := by
      rw [←ey]; simp only [Nat.cast_mul,Nat.cast_ofNat,m,rat_mul]
      change ((d/p:ℕ):Q)*8*((TunnellHurwitz.pure) t*rat z*(TunnellHurwitz.pure) s)=(TunnellHurwitz.pure) t*(((d/p:ℕ):Q)*(8*rat z))*(TunnellHurwitz.pure) s
      rw [←mul_assoc ((TunnellHurwitz.pure) t) ((d/p:ℕ):Q),←Nat.cast_comm (d/p) ((TunnellHurwitz.pure) t)]
      noncomm_ring
    apply hm (reduction_forces hp2 (fun h => ?_) (hp.trans (dvd_mul_left ..)) y hy H)
    rcases (Fact.out:p.Prime).dvd_mul.mp h with e|e
    · exact TunnellOddDiscriminant.quotient_nonzero (Squarefree.squarefree_of_dvd (dvd_mul_left d 2) hn) hp ((ZMod.natCast_eq_zero_iff _ _).mpr e)
    · have he := (Fact.out:p.Prime).dvd_of_dvd_pow (n:=3) (show p∣2^3 from e)
      exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out:p.Prime) Nat.prime_two).mp he)
end
end TunnellGlueMaximal
end


/- TunnellIdealFormBasis -/
section
namespace TunnellIdealFormBasis
open TunnellIdealHNF TunnellOddDiscriminant TunnellIdealThetaExpansion TunnellGenusCharacter
noncomputable section
variable {n p : ℕ}
def basisPoint (s : Data n) (x : ℤ×ℤ) : R n := ⟨s.c*(s.a*x.1+s.b*x.2),s.c*x.2⟩
lemma basis_mem (s : Data n) (x : ℤ×ℤ) : basisPoint s x∈ideal s := by
  apply (mem_ideal _ _).mpr
  exact ⟨⟨x.2,rfl⟩,⟨x.1,by dsimp [basisPoint]; ring⟩⟩
def basisHom (s : Data n) : (ℤ×ℤ) →+ ideal s where
  toFun x := ⟨basisPoint s x,basis_mem s x⟩
  map_zero' := Subtype.ext (Zsqrtd.ext (by simp [basisPoint]) (by simp [basisPoint]))
  map_add' x y := by apply Subtype.ext; apply Zsqrtd.ext <;> dsimp [basisPoint] <;> ring
def basis (s : Data n) : (ℤ×ℤ) ≃+ ideal s := by
  apply AddEquiv.ofBijective (basisHom s)
  refine ⟨?_,?_⟩
  · intro x y e
    have ex := congrArg (fun w : ideal s => w.val.re) e
    have ey := congrArg (fun w : ideal s => w.val.im) e
    change (s.c:ℤ)*(s.a*x.1+s.b*x.2)=s.c*(s.a*y.1+s.b*y.2) at ex
    change (s.c:ℤ)*x.2=s.c*y.2 at ey
    have hc : (s.c:ℤ)≠0 := by exact_mod_cast s.pos_c.ne'
    have ha : (s.a:ℤ)≠0 := by exact_mod_cast s.pos_a.ne'
    have hy := mul_left_cancel₀ hc ey
    rw [hy] at ex
    exact Prod.ext (mul_left_cancel₀ ha (add_right_cancel (mul_left_cancel₀ hc ex))) hy
  · rintro ⟨x,hx⟩; obtain ⟨u,v,e⟩ := basis_expansion s hx; exact ⟨(u,v),Subtype.ext e.symm⟩
lemma basis_norm (s : Data n) (C : ℤ) (hC : (s.b:ℤ)^2+n=s.a*C) (x : ℤ×ℤ) :
    (basis s x).val.norm=(normI (ideal s):ℤ)*quad (s.a:ℤ) s.b C x := by
  rw [normI,quotient_card]; change (s.c:ℤ)*(s.a*x.1+s.b*x.2)*(s.c*(s.a*x.1+s.b*x.2))- -(n:ℤ)*(s.c*x.2)*(s.c*x.2)=_
  unfold quad; push_cast; linear_combination (s.c:ℤ)^2*x.2^2*hC
structure LocalBasis (p : ℕ) [Fact p.Prime] (I : Ideal (R n)) where
  A : ℤ
  B : ℤ
  C : ℤ
  det : A*C-B^2=n
  unit : (A:ZMod p)≠0
  basis : (ℤ×ℤ) ≃+ I
  norm : ∀ x, (basis x).val.norm=(normI I:ℤ)*quad A B C x
variable [Fact p.Prime]
end
end TunnellIdealFormBasis
end


/- TunnellBinaryPairModel -/
section
namespace TunnellBinaryPairModel
open TunnellShell TunnellHurwitz TunnellToricClass TunnellToricLocal TunnellEmbeddedIdeals
open TunnellIdealHNF TunnellPairComponents TunnellCMGluing TunnellSwitchComponents TunnellIdealGluings
open TunnellFrameNorm TunnellIntertwinerTheta
noncomputable section
lemma pure_nonzero {n : ℕ} (hn : n≠0) {v : Triple} (hv : v∈shell n) : (TunnellHurwitz.pure) v≠0 := by
  intro e; have h := pure_square hv; rw [e,zero_mul] at h
  exact TunnellRamifiedSwitch.nat_nonzero hn (neg_eq_zero.mp h.symm)
lemma re_comm (x y : Q) : (x*y).re=(y*x).re := by rw [Quaternion.re_mul,Quaternion.re_mul]; ring
lemma anti_re {n : ℕ} (hn : n≠0) {v : Triple} (hv : v∈shell n) {x : Q} (hx : x∈anti v) : x.re=0 := by
  have hu := pure_nonzero hn hv
  have H : (TunnellHurwitz.pure) v*x*((TunnellHurwitz.pure) v)⁻¹= -x := by rw [mem_anti.mp hx,neg_mul,mul_assoc,mul_inv_cancel₀ hu,mul_one]
  have e := congrArg QuaternionAlgebra.re H
  rw [re_comm,←mul_assoc,inv_mul_cancel₀ hu,one_mul,Quaternion.re_neg] at e
  linarith
lemma anti_star {v : Triple} {y : Q} (hy : y∈anti v) : star y∈anti v := by
  have h := congrArg star (mem_anti.mp hy)
  simp only [star_mul,pure_star,star_neg,mul_neg,neg_mul,neg_neg] at h
  exact mem_anti.mpr h.symm
lemma orthogonal {n : ℕ} (hn : n≠0) {v : Triple} (hv : v∈shell n) {x y : Q} (hx : x∈C v) (hy : y∈anti v) :
    Quaternion.normSq (x+y)=Quaternion.normSq x+Quaternion.normSq y := by
  rw [Quaternion.normSq_add,anti_re hn hv ((C_anti v) (Submodule.mul_mem_mul hx (anti_star hy))),mul_zero,add_zero]
lemma disjoint {n : ℕ} (hn : n≠0) {v : Triple} (hv : v∈shell n) : Disjoint (C v) (anti v) := by
  rw [Submodule.disjoint_def]
  intro x hx hy
  have e := (mem_C.mp hx).symm.trans (mem_anti.mp hy)
  have e' : (2:Q)*(x*(TunnellHurwitz.pure) v)=0 := by rw [two_mul,add_eq_zero_iff_eq_neg]; exact e
  have h₂ : (2:Q)≠0 := TunnellRamifiedSwitch.nat_nonzero (a:=2) (by decide)
  exact (mul_eq_zero.mp ((mul_eq_zero.mp e').resolve_left h₂)).resolve_right (pure_nonzero hn hv)
variable {n : ℕ} {v : Triple} (hv : v∈shell n)
def plusI (B A : Ideal (TunnellIdealHNF.R n)) := B*conjugate A
def minusI (B A C₀ : Ideal (TunnellIdealHNF.R n)) := conjugate B*C₀*conjugate A
def eval (u : Q) (I J : Ideal (TunnellIdealHNF.R n)) : (I×J) →+ Q where
  toFun x := embed n v hv x.1.val+2*(u⁻¹*embed n v hv x.2.val)
  map_zero' := by simp
  map_add' x y := by change embed n v hv (_+_)+2*(u⁻¹*embed n v hv (_+_))=_; rw [map_add,map_add,mul_add,mul_add]; abel
lemma scale_anti {u : Q} (hu : (TunnellHurwitz.pure) v*u= -(u*(TunnellHurwitz.pure) v)) (hu0 : u≠0) {q : Q} (hq : q∈C v) :
    u⁻¹*q∈anti v := by
  apply mem_anti.mpr
  apply mul_left_cancel₀ hu0
  have he : u*(TunnellHurwitz.pure) v= -((TunnellHurwitz.pure) v*u) := by rw [hu,neg_neg]
  rw [←mul_assoc u,he,neg_mul,mul_assoc ((TunnellHurwitz.pure) v),←mul_assoc u,mul_inv_cancel₀ hu0,one_mul,
    mul_neg,←mul_assoc u,←mul_assoc u,mul_inv_cancel₀ hu0,one_mul,mem_C.mp hq]
lemma injective (hn : Squarefree n) (h0 : n≠0) {u : Q} (hu : (TunnellHurwitz.pure) v*u= -(u*(TunnellHurwitz.pure) v)) (hu0 : u≠0) (I J : Ideal (TunnellIdealHNF.R n)) :
    Function.Injective (eval hv u I J) := by
  apply (AddMonoidHom.ker_eq_bot_iff _).mp
  apply le_antisymm _ bot_le
  intro x hx
  have he : embed n v hv x.1.val= -(2*(u⁻¹*embed n v hv x.2.val)) := add_eq_zero_iff_eq_neg.mp hx
  have hc (L : Ideal (TunnellIdealHNF.R n)) (w:L) : embed n v hv w.val∈C v := center_image hv L ⟨_,w.property,rfl⟩
  have hanti := scale_anti hu hu0 (hc J x.2)
  have hright : -(2*(u⁻¹*embed n v hv x.2.val))∈anti v := (anti v).neg_mem (by simpa only [zsmul_eq_mul,Int.cast_ofNat] using (anti v).smul_mem (2:ℤ) hanti)
  have z := (Submodule.disjoint_def.mp (disjoint h0 hv)) _ (hc I x.1) (he ▸ hright)
  have z₂ : embed n v hv x.2.val=0 := by
    rw [z,zero_eq_neg] at he
    exact (mul_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (TunnellRamifiedSwitch.nat_nonzero (a:=2) (by decide)))).resolve_left (inv_ne_zero hu0)
  exact Prod.ext (Subtype.ext (embed_inj hn hv (z.trans (map_zero _).symm))) (Subtype.ext (embed_inj hn hv (z₂.trans (map_zero _).symm)))
lemma components (hn : Squarefree n) (h2 : n%4=2) {u : Q} (hu : (TunnellHurwitz.pure) v*u= -(u*(TunnellHurwitz.pure) v)) (hu0 : u≠0)
    {C₀ : Ideal (TunnellIdealHNF.R n)} (ec : image hv C₀=line u*J v (-v)) (B A : Ideal (TunnellIdealHNF.R n)) :
    sandwich hv B (conjugate A) (J v v)=image hv (plusI B A) ∧
    sandwich hv B (conjugate A) (J v (-v))=line u⁻¹*image hv (minusI B A C₀) := by
  have H : image hv B*J v v=image hv B := by rw [←image_order hn h2 hv,←image_mul,Ideal.mul_top]
  constructor
  · rw [plusI,image_mul,sandwich,H]
  · unfold minusI sandwich
    rw [image_mul,image_mul,ec,←mul_assoc (image hv (conjugate B)),←anti_scalar hv hu B]
    calc _=line u⁻¹*line u*(image hv B*J v (-v)*image hv (conjugate A)) := by rw [two_sided_inverse hu0,one_mul]
         _=_ := by simp only [mul_assoc]
theorem range_eq (hn : Squarefree n) (h2 : n%4=2) {u : Q} (hu : (TunnellHurwitz.pure) v*u= -(u*(TunnellHurwitz.pure) v)) (hu0 : u≠0)
    {C₀ : Ideal (TunnellIdealHNF.R n)} (ec : image hv C₀=line u*J v (-v)) (B A : Ideal (TunnellIdealHNF.R n)) :
    (eval hv u (plusI B A) (minusI B A C₀)).range.toIntSubmodule=sandwich hv B (conjugate A) (TunnellFilteredGlue.binary v) := by
  obtain ⟨e₁,e₂⟩ := components hv hn h2 hu hu0 ec B A
  have e₃ : sandwich hv B (conjugate A) (line 2*J v (-v))=line 2*sandwich hv B (conjugate A) (J v (-v)) := by
    unfold sandwich; rw [←mul_assoc (image hv B),←line_central (2:Q) (fun q => by noncomm_ring)]; simp only [mul_assoc]
  have e₄ : sandwich hv B (conjugate A) (TunnellFilteredGlue.binary v)=image hv (plusI B A) ⊔ line 2*(line u⁻¹*image hv (minusI B A C₀)) := by
    unfold TunnellFilteredGlue.binary sandwich at *; rw [Submodule.mul_sup,Submodule.sup_mul,e₁,e₃,e₂]
  rw [e₄]; ext q; constructor
  · rintro ⟨x,rfl⟩
    exact Submodule.add_mem_sup ⟨_,x.1.property,rfl⟩ (Submodule.mem_span_singleton_mul.mpr ⟨_,Submodule.mem_span_singleton_mul.mpr ⟨_,⟨_,x.2.property,rfl⟩,rfl⟩,rfl⟩)
  · intro h; obtain ⟨x,⟨j,hj,rfl⟩,y,hy,rfl⟩ := Submodule.mem_sup.mp h
    obtain ⟨w,hw,ew⟩ := Submodule.mem_span_singleton_mul.mp hy
    change w∈line u⁻¹*image hv (minusI B A C₀) at hw
    obtain ⟨z,hz,ez⟩ := Submodule.mem_span_singleton_mul.mp hw
    obtain ⟨k,hk,ek⟩ := (mem_image hv).mp hz
    refine ⟨(⟨j,hj⟩,⟨k,hk⟩),?_⟩
    change embed n v hv j+2*(u⁻¹*embed n v hv k)=_; rw [ek,ez,ew]; rfl
end
end TunnellBinaryPairModel
end


/- TunnellFramedGlue -/
section
namespace TunnellFramedGlue
open TunnellHurwitz TunnellToricClass TunnellShell TunnellToricLocal TunnellPairComponents TunnellRamifiedSwitch
open TunnellIdealGluings TunnellSwitchComponents TunnellFilteredGlue TunnellGlueMaximal TunnellEmbeddedIdeals
open TunnellIdealHNF TunnellRamifiedClasses TunnellCMGluing
noncomputable section
variable {n : ℕ} {v : Triple} (hv : v∈shell n)
lemma inf_twist (hn : Squarefree n) (h2 : n%4=2) {A B : Ideal (TunnellIdealHNF.R n)} (hA : A≠⊥) (hB : B≠⊥)
    {D E : Lattice} (hD : bimod v D) (hE : bimod v E) :
    sandwich hv A B (D ⊓ E)=sandwich hv A B D ⊓ sandwich hv A B E := by
  obtain ⟨A',hA',eA⟩ := (image_isIdeal hn h2 hv A hA).2.2.2
  obtain ⟨B',hB',eB⟩ := (image_isIdeal hn h2 hv B hB).2.2.2
  have eA' := (ideals_comm hn hv hA' (center_image hv A)).trans eA
  have eB' := (ideals_comm hn hv hB' (center_image hv B)).trans eB
  have tr (X : Lattice) (hX : bimod v X) : A'*sandwich hv A B X*B'=X := by
    calc _=(A'*image hv A)*X*(image hv B*B') := by simp only [sandwich,mul_assoc]
         _=_ := by rw [eA',eB,hX]
  let Y := sandwich hv A B D ⊓ sandwich hv A B E
  have hb : A'*Y*B'≤D ⊓ E := le_inf ((mul_le_mul_left (mul_le_mul_right inf_le_left _) _).trans_eq (tr D hD))
      ((mul_le_mul_left (mul_le_mul_right inf_le_right _) _).trans_eq (tr E hE))
  refine le_antisymm (le_inf (mul_le_mul_left (mul_le_mul_right inf_le_left _) _) (mul_le_mul_left (mul_le_mul_right inf_le_right _) _)) ?_
  have hR : 1≤J v v := Submodule.one_le.mpr (one_J v)
  calc Y=1*Y*1 := by rw [one_mul,mul_one]
       _≤J v v*Y*J v v := mul_le_mul' (mul_le_mul_left hR _) hR
       _=sandwich hv A B (A'*Y*B') := by
         calc _=(image hv A*A')*Y*(B'*image hv B) := by rw [eA,eB']
              _=_ := by simp only [sandwich,mul_assoc]
       _≤_ := mul_le_mul_left (mul_le_mul_right hb _) _
lemma scalar_twist (A B : Ideal (TunnellIdealHNF.R n)) (u : Q) (hu : ∀ q:Q,u*q=q*u) (D : Lattice) :
    sandwich hv A B (line u*D)=line u*sandwich hv A B D := by
  unfold sandwich; rw [←mul_assoc (image hv A),←line_central u hu]; simp only [mul_assoc]
lemma frame {a b : Q} {A B : Ideal (TunnellIdealHNF.R n)} {s t : Triple} (hn : Squarefree n) (h2 : n%4=2) (hs : s∈shell n)
    (eA : image hv A=line a*J v s) (eB : image hv B=line b*J v t) :
    sandwich hv B (conjugate A) (binary v)=line b*pairL s t*line (star a) := by
  have one (L : Lattice) : sandwich hv B (conjugate A) L=line b*(J v t*L*J s v)*line (star a) := by
    simp only [sandwich,eB,conj_frame hv eA,mul_assoc]
  have e₁ : J v t*J v v*J s v=J s t := by rw [J_comp hn h2 hv hv,J_comp hn h2 hs hv]
  have h₁ : J v t*J v (-v)=J (-v) t := by rw [←J_opposite,J_comp hn h2 (shell_neg hv) hv]
  have h₂ : J (-v) t*J s v=J (-s) t := by rw [←J_neg s v,J_comp hn h2 (shell_neg hs) (shell_neg hv)]
  have H (L : Lattice) : line b*(line 2*L)*line (star a)=line 2*(line b*L*line (star a)) := by
    rw [←mul_assoc (line b),←line_central (2:Q) (fun q => by noncomm_ring)]; simp only [mul_assoc]
  have hdist (D E : Lattice) : sandwich hv B (conjugate A) (D ⊔ E)=sandwich hv B (conjugate A) D ⊔ sandwich hv B (conjugate A) E := by
    unfold sandwich; rw [Submodule.mul_sup,Submodule.sup_mul]
  unfold binary pairL
  rw [hdist,scalar_twist hv _ _ (2:Q) (fun q => by noncomm_ring),one,one,e₁,h₁,h₂,Submodule.mul_sup,Submodule.sup_mul,H]
lemma ram_pass {a : ℕ} (hn : Squarefree n) (h2 : n%4=2) (ha : 0<a) (hd : a∣n) :
    image hv (ram n a)*binary v*image hv (ram n a)=line (a:Q)*binary v := by
  let I := image hv (ram n a)
  have hI := center_image hv (ram n a)
  have Rleft : J v v*I=I := by rw [←image_order hn h2 hv,←image_mul,Ideal.top_mul]
  have Rright : I*J v v=I := by rw [←image_order hn h2 hv,←image_mul,Ideal.mul_top]
  have hanti : J v (-v)≤anti v := by rw [←anti_order]; exact inf_le_right
  have hcomm : J v (-v)*I=I*J v (-v) := by simpa only [ram_conj ha hd] using anti_ideal (J v (-v)) hv hanti (ram n a)
  have ec : binary v*I=I*binary v := by
    unfold binary; rw [Submodule.sup_mul,Submodule.mul_sup,Rleft,Rright,mul_assoc,hcomm,←mul_assoc,←mul_assoc I (line 2),line_central (2:Q) (fun q => by noncomm_ring) I]
  have hII : I*I=line (a:Q)*J v v := by rw [←image_mul,ram_square hn h2 ha hd,principal,image_principal hn h2 hv,map_natCast]
  have hact : J v v*binary v=binary v := by
    have hR : 1≤J v v := Submodule.one_le.mpr (one_J v)
    have e := binary_stable hn h2 hv
    apply le_antisymm
    · calc J v v*binary v=J v v*binary v*1 := (mul_one _).symm
           _≤_ := (mul_le_mul_right hR _).trans e.le
    · simpa only [one_mul] using mul_le_mul_left hR (binary v)
  change I*binary v*I=_
  rw [mul_assoc,ec,←mul_assoc,hII,mul_assoc,hact]
lemma ram_binary {a : ℕ} (hn : Squarefree n) (h2 : n%4=2) (ha : 0<a) (hd : a∣n) (B A : Ideal (TunnellIdealHNF.R n)) :
    sandwich hv (B*ram n a) (conjugate (A*ram n a)) (binary v)=line (a:Q)*sandwich hv B (conjugate A) (binary v) := by
  have h : sandwich hv (B*ram n a) (conjugate (A*ram n a)) (binary v)=sandwich hv B (conjugate A) (image hv (ram n a)*binary v*image hv (ram n a)) := by
    rw [conjugate_mul,ram_conj ha hd,mul_comm (conjugate A)]; simp only [sandwich,image_mul,mul_assoc]
  rw [h,ram_pass hv hn h2 ha hd,scalar_twist hv _ _ _ (Nat.cast_comm a)]
lemma ram_full {a : ℕ} (ha : 0<a) (hd : a∣n) (B A : Ideal (TunnellIdealHNF.R n)) :
    sandwich hv B (conjugate A) (glue hv a)=line (a:Q)⁻¹*sandwich hv (B*ram n a) (conjugate (A*ram n a)) O := by
  rw [base_change,conjugate_mul,ram_conj ha hd,mul_comm (conjugate A)]
end
end TunnellFramedGlue
end


/- TunnellGluePacket -/
section
namespace TunnellGluePacket
open TunnellIdealHNF TunnellIdealFormBasis TunnellOddDiscriminant TunnellOddGlueCoordinates TunnellRamifiedLines
noncomputable section
variable {n d : ℕ} {p : ℕ} [Fact p.Prime] {I J : Ideal (R n)}
def coordinate (L : LocalBasis p I) : I →+ ZMod p where
  toFun x := coord L.A (L.basis.symm x)
  map_zero' := by simp [coord]
  map_add' x y := by simp [coord,add_div]
def admissible (L : LocalBasis p I) (x : I) :=
  pairing (L.A:ZMod p) L.B L.C (redPair (L.basis.symm x))=0
lemma red_zero (x : ℤ×ℤ) : redPair (p:=p) x=0 ↔ ∃ y : ℤ×ℤ, x=(p:ℤ) • y := by
  constructor
  · intro h
    obtain ⟨u,hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x.1 p).mp (congrArg Prod.fst h)
    obtain ⟨v,hv⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd x.2 p).mp (congrArg Prod.snd h)
    exact ⟨(u,v),Prod.ext hu hv⟩
  · rintro ⟨⟨u,v⟩,rfl⟩; apply Prod.ext <;> simp [redPair,zsmul_eq_mul]
lemma no_coordinate (hp : p∣n) (L : LocalBasis p I) {x : I} (hx : admissible L x) :
    coordinate L x=0 ↔ ∃ y : I, x=(p:ℤ) • y := by
  have hr : (L.A:ZMod p)*(L.C:ZMod p)-(L.B:ZMod p)^2=0 := by
    have e := congrArg (fun x:ℤ => (x:ZMod p)) L.det; push_cast at e; rw [e]; exact (ZMod.natCast_eq_zero_iff _ _).mpr hp
  obtain ⟨r,er⟩ := (radical L.unit hr _).mp hx
  have e : coordinate L x=r := by
    change ((L.basis.symm x).2:ZMod p)/(L.A:ZMod p)=r
    have H := congrArg Prod.snd er
    change ((L.basis.symm x).2:ZMod p)=(L.A:ZMod p)*r at H
    rw [H]; field_simp [L.unit]
  constructor
  · intro he
    rw [←e,he] at er
    obtain ⟨y,hy⟩ := (red_zero (p:=p) _).mp (by change redPair (p:=p) (L.basis.symm x)=(0,0); simpa using er)
    exact ⟨L.basis y,by rw [←map_zsmul,←hy,L.basis.apply_symm_apply]⟩
  · rintro ⟨y,rfl⟩; rw [map_zsmul,zsmul_eq_mul,Int.cast_natCast,ZMod.natCast_self,zero_mul]
lemma admissible_sub (L : LocalBasis p I) {x y : I} (hx : admissible L x) (hy : admissible L y) : admissible L (x-y) := by
  apply Prod.ext
  · have ex := congrArg Prod.fst hx; have ey := congrArg Prod.fst hy
    change _=0; unfold pairing redPair; rw [map_sub]; simp only [Prod.fst_sub,Prod.snd_sub,Int.cast_sub]
    change (L.A:ZMod p)*(_-_)+(L.B:ZMod p)*(_-_)=0
    change (L.A:ZMod p)*_+(L.B:ZMod p)*_=0 at ex ey; dsimp only [redPair] at ex ey; linear_combination ex - ey
  · have ex := congrArg Prod.snd hx; have ey := congrArg Prod.snd hy
    change _=0; unfold pairing redPair; rw [map_sub]; simp only [Prod.fst_sub,Prod.snd_sub,Int.cast_sub]
    change (L.B:ZMod p)*(_-_)+(L.C:ZMod p)*(_-_)=0
    change (L.B:ZMod p)*_+(L.C:ZMod p)*_=0 at ex ey; dsimp only [redPair] at ex ey; linear_combination ex - ey
private instance prime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
lemma int_dvd (hs : Squarefree d) {z : ℤ} (h : ∀ i : P d, (i.val:ℤ)∣z) : (d:ℤ)∣z := by
  rw [←Nat.prod_primeFactors_of_squarefree hs,Nat.cast_prod]
  apply Finset.prod_dvd_of_coprime
  · intro p hp q hq hpq
    exact ((Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).mpr hpq).isCoprime
  · intro p hp; exact h ⟨p,hp⟩
lemma ideal_dvd (hs : Squarefree d) (hn : 0<n) (hI : I≠⊥) {x : I} (h : ∀ i : P d, ∃ y : I, x=(i.val:ℤ) • y) :
    ∃ y : I, x=(d:ℤ) • y := by
  obtain ⟨s,rfl⟩ := normal_form hn hI
  let E := basis s
  have H (i : P d) : ∃ y : ℤ×ℤ, E.symm x=(i.val:ℤ) • y := by
    obtain ⟨y,hy⟩ := h i
    exact ⟨E.symm y,by rw [hy,map_zsmul]⟩
  obtain ⟨u,hu⟩ := int_dvd hs (z:=(E.symm x).1) (fun i => by obtain ⟨y,hy⟩ := H i; exact ⟨y.1,congrArg Prod.fst hy⟩)
  obtain ⟨v,hv⟩ := int_dvd hs (z:=(E.symm x).2) (fun i => by obtain ⟨y,hy⟩ := H i; exact ⟨y.2,congrArg Prod.snd hy⟩)
  have he : E.symm x=(d:ℤ) • (u,v) := Prod.ext hu hv
  exact ⟨E (u,v),by rw [←map_zsmul,←he,E.apply_symm_apply]⟩
variable (U : (i : P d) → LocalBasis i.val I) (V : (i : P d) → LocalBasis i.val J)
def packet : (I×J) →+ Packet d where
  toFun x i := (coordinate (U i) x.1,coordinate (V i) x.2)
  map_zero' := by funext i; simp
  map_add' x y := by funext i; simp
def good (x : I×J) := ∀ i : P d, admissible (U i) x.1 ∧ admissible (V i) x.2
theorem distinguish (hs : Squarefree d) (hn : 0<n) (hd : d∣n) (hI : I≠⊥) (hJ : J≠⊥) {S T : AddSubgroup (I×J)}
    (hS : ∀ x∈S, good U V x) (hT : ∀ x∈T, good U V x) (hD : ∀ y:I×J, (d:ℤ) • y∈T)
    (he : S.map (packet U V)≤T.map (packet U V)) : S≤T := by
  intro x hx
  obtain ⟨y,hy,ey⟩ := he (show packet U V x∈S.map (packet U V) from ⟨x,hx,rfl⟩)
  have H (i : P d) := congrFun ey i
  have hδ (i : P d) := (Nat.dvd_of_mem_primeFactors i.property).trans hd
  have h₁ := ideal_dvd hs hn hI (x:=x.1-y.1) (fun i => (no_coordinate (hδ i) (U i) (admissible_sub _ (hS x hx i).1 (hT y hy i).1)).mp (by rw [map_sub]; exact sub_eq_zero.mpr (congrArg Prod.fst (H i)).symm))
  have h₂ := ideal_dvd hs hn hJ (x:=x.2-y.2) (fun i => (no_coordinate (hδ i) (V i) (admissible_sub _ (hS x hx i).2 (hT y hy i).2)).mp (by rw [map_sub]; exact sub_eq_zero.mpr (congrArg Prod.snd (H i)).symm))
  obtain ⟨u,eu⟩ := h₁; obtain ⟨v,ev⟩ := h₂
  have e : x-y=(d:ℤ) • (u,v) := Prod.ext eu ev
  have hxy : x-y∈T := e ▸ hD (u,v)
  simpa only [sub_add_cancel] using T.add_mem hxy hy
end
end TunnellGluePacket
end


/- TunnellIntegralPacket -/
section
namespace TunnellIntegralPacket
open TunnellIdealHNF TunnellOddDiscriminant TunnellOddGlueCoordinates TunnellRamifiedLines
open TunnellIdealFormBasis TunnellGluePacket TunnellIdealThetaExpansion TunnellGenusCharacter
noncomputable section
variable {d : ℕ} {I J : Ideal (R (2*d))}
private instance prime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
def value (x : I×J) : ℤ := (valence x.1:ℤ)+4*(valence x.2:ℤ)
lemma chart_value {p : ℕ} [Fact p.Prime] (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥)
    (L : LocalBasis p I) (x : I) : (valence x:ℤ)=quad L.A L.B L.C (L.basis.symm x) := by
  have e := L.norm (L.basis.symm x)
  rw [L.basis.apply_symm_apply,norm_valZ hn h2 hI,mul_comm] at e
  exact mul_left_cancel₀ (show (normI I:ℤ)≠0 by exact_mod_cast (normI_positive (by omega) I hI).ne') e
variable (U : (i : P d) → LocalBasis i.val I) (V : (i : P d) → LocalBasis i.val J)
lemma valid (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥) (hJ : J≠⊥) (hd : Odd d)
    (X : AddSubgroup (I×J)) (hD : ∀ y : I×J, (d:ℤ) • y∈X) (hN : ∀ x∈X, (d:ℤ)^2∣value x)
    {x : I×J} (hx : x∈X) : good U V x := by
  intro i
  have hp := Nat.dvd_of_mem_primeFactors i.property
  have hodd : i.val≠2 := by intro h; rw [h] at hp; exact (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr hp)
  have hu : (2:ZMod i.val)≠0 := by
    intro ee; exact hodd ((Nat.prime_dvd_prime_iff_eq (prime i).out Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 i.val).mp ee))
  have he (z : I×J) := congrArg₂ (fun (a b : ℤ) => a+4*b) (chart_value hn h2 hI (U i) z.1) (chart_value hn h2 hJ (V i) z.2)
  have addD (y : I×J) := dvd_sub (hN (x+(d:ℤ) • y) (X.add_mem hx (hD y))) (hN x hx)
  constructor
  · apply radical_of_values 1 d (by omega) hp (by simpa using hu)
    intro y; have h := addD ((U i).basis y,0)
    change (d:ℤ)^2 ∣ ((valence _ :ℤ)+4*_)-((valence _ :ℤ)+4*_) at h
    change (d:ℤ)^2 ∣ value (x+(d:ℤ) • ((U i).basis y,0))-value x at h
    rw [show value (x+(d:ℤ) • ((U i).basis y,0))=_ from he _,show value x=_ from he x] at h
    simpa [map_add,map_zsmul] using h
  · apply radical_of_values 4 d (by omega) hp (by simpa [show (8:ZMod i.val)=2^3 by norm_num] using pow_ne_zero 3 hu)
    intro y; have h := addD (0,(V i).basis y)
    rw [show value (x+(d:ℤ) • (0,(V i).basis y))=_ from he _,show value x=_ from he x] at h
    simpa only [Prod.fst_add,Prod.snd_add,Prod.smul_fst,Prod.smul_snd,smul_zero,add_zero,map_add,map_zsmul,
      AddEquiv.symm_apply_apply,Nat.cast_ofNat,mul_sub,add_sub_add_left_eq_sub] using h
def parameter (i : P d) := -(4:ZMod i.val)*(V i).A/(U i).A
theorem trace (hs : Squarefree d) (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥) (hJ : J≠⊥) (hd : Odd d)
    (X : ↥d.divisors → AddSubgroup (I×J)) (hi : Function.Injective X)
    (hD : ∀ a (y : I×J), (d:ℤ) • y∈X a) (hN : ∀ a x, x∈X a → (d:ℤ)^2∣value x)
    (hmax : ∀ a (i : P d), ∃ x∈X a, ¬∃ y : I×J, x=(i.val:ℤ) • y) :
    ∃ r : (i : P d) → ZMod i.val, (∀ i, r i^2=parameter U V i) ∧
      ∃ E : ↥d.divisors ≃ (P d → Bool), ∀ a, (X a).map (packet U V)=linePacket (TunnellAllRamifiedLines.signed r (E a)) := by
  classical
  let S a := (X a).map (packet U V)
  have hgood a x := valid U V hn h2 hI hJ hd (X a) (hD a) (hN a) (x:=x)
  have hin : Function.Injective S := by
    intro a b e; apply hi
    exact le_antisymm (distinguish U V hs (by omega) (dvd_mul_left ..) hI hJ (hgood a) (hgood b) (hD b) e.le)
      (distinguish U V hs (by omega) (dvd_mul_left ..) hI hJ (hgood b) (hgood a) (hD a) e.ge)
  have hpd (i : P d) := (Nat.dvd_of_mem_primeFactors i.property).trans (dvd_mul_left d 2)
  have hxQ a (x : Packet d) (hx : x∈S a) (i : P d) : (x i).1^2=parameter U V i*(x i).2^2 := by
    obtain ⟨z,hz,rfl⟩ := hx
    have hh := hgood a z hz i
    apply square_condition (U i).det (V i).det hn (hpd i) (U i).unit (V i).unit _ _ hh.1 hh.2
    rw [←chart_value hn h2 hI,←chart_value hn h2 hJ]
    exact (pow_dvd_pow_of_dvd (by exact_mod_cast Nat.dvd_of_mem_primeFactors i.property : (i.val:ℤ)∣d) 2).trans (hN a z hz)
  have hnon a (i : P d) : ∃ x∈S a, x i≠0 := by
    obtain ⟨x,hx,hnx⟩ := hmax a i
    refine ⟨_,⟨x,hx,rfl⟩,fun he => hnx ?_⟩
    obtain ⟨u,eu⟩ := (no_coordinate (hpd i) (U i) (hgood a x hx i).1).mp (congrArg Prod.fst he)
    obtain ⟨v,ev⟩ := (no_coordinate (hpd i) (V i) (hgood a x hx i).2).mp (congrArg Prod.snd he)
    exact ⟨(u,v),Prod.ext eu ev⟩
  apply TunnellAllRamifiedLines.exhaustive hs hd (parameter U V) _ S hin hxQ hnon
  intro i
  have hp := Nat.dvd_of_mem_primeFactors i.property
  have hu : (2:ZMod i.val)≠0 := by
    intro e; have eq := (Nat.prime_dvd_prime_iff_eq (prime i).out Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff 2 i.val).mp e)
    rw [eq] at hp; exact (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr hp)
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by simpa [show (4:ZMod i.val)=2^2 by norm_num] using pow_ne_zero 2 hu)) (V i).unit) (U i).unit
end
end TunnellIntegralPacket
end


/- TunnellGlueIsometry -/
section
namespace TunnellGlueIsometry
open TunnellHurwitz TunnellToricClass TunnellShell TunnellToricLocal TunnellPairComponents TunnellRamifiedSwitch
open TunnellIdealGluings TunnellSwitchComponents TunnellFilteredGlue TunnellGlueMaximal TunnellEmbeddedIdeals
open TunnellIdealHNF TunnellRamifiedClasses TunnellFramedGlue TunnellTwoProjection TunnellBinaryPairModel
open TunnellClassThetaCount TunnellFrameNorm TunnellIntertwinerTheta TunnellIdealThetaExpansion TunnellGenusCharacter
noncomputable section
def action (b c : Q) (x : Q) := b*x*c
def transport (b c : Q) (D : Lattice) := line b*D*line c
lemma mem_transport {b c x : Q} {D : Lattice} : x∈transport b c D ↔ ∃ y∈D, action b c y=x := by
  rw [transport,Submodule.mem_mul_span_singleton]
  constructor
  · rintro ⟨j,hj,rfl⟩; obtain ⟨y,hy,rfl⟩ := Submodule.mem_span_singleton_mul.mp hj; exact ⟨y,hy,rfl⟩
  · rintro ⟨y,hy,rfl⟩; exact ⟨_,Submodule.mem_span_singleton_mul.mpr ⟨_,hy,rfl⟩,rfl⟩
lemma action_inj {b c : Q} (hb : b≠0) (hc : c≠0) : Function.Injective (action b c) :=
  fun _ _ e => mul_left_cancel₀ hb (mul_right_cancel₀ hc e)
lemma action_mem {b c : Q} (hb : b≠0) (hc : c≠0) (D : Lattice) (x : Q) : action b c x∈transport b c D ↔ x∈D := by
  rw [mem_transport]; exact ⟨fun ⟨y,hy,e⟩ => (action_inj hb hc e) ▸ hy,fun h => ⟨_,h,rfl⟩⟩
lemma action_nat (b c : Q) (k : ℕ) (x : Q) : (k:Q)*action b c x=action b c ((k:Q)*x) := by
  unfold action; rw [←mul_assoc,←mul_assoc,Nat.cast_comm k b,mul_assoc b]
lemma transport_scale {a : ℕ} (b c : Q) (D : Lattice) : line (a:Q)⁻¹*transport b c D=transport ((a:Q)⁻¹*b) c D := by
  unfold transport; rw [←mul_assoc,←mul_assoc,line_mul]
lemma admits_mem (d : ℕ) (s t : Triple) (q : Q) : admits d s t q ↔ (d:Q)*q∈pairL s t := by
  constructor
  · rintro ⟨x,hx,y,hy,ha,e⟩
    rw [e]; exact Submodule.add_mem_sup hx (Submodule.mem_span_singleton_mul.mpr ⟨y,⟨hy,by simpa [pure_neg] using ha⟩,rfl⟩)
  · intro he; obtain ⟨x,hx,z,hz,e⟩ := Submodule.mem_sup.mp he
    obtain ⟨y,hy,rfl⟩ := Submodule.mem_span_singleton_mul.mp hz
    exact ⟨x,hx,y,hy.1,by simpa [pure_neg] using hy.2,e.symm⟩
variable {d : ℕ} {v : Triple} (hv : v∈shell (2*d))
def rep (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {I : Ideal (TunnellIdealHNF.R (2*d))} (hI : I≠⊥) :=
  representative hn h2 hv ⟨image hv I,image_isIdeal hn h2 hv I hI⟩
theorem frames (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {A B : Ideal (TunnellIdealHNF.R (2*d))} (hA : A≠⊥) (hB : B≠⊥)
    {r : ℕ} (hr : 0<r) (hd : r∣2*d) :
    let hA' := mul_ne_bot (by omega : 0<2*d) hA (ram_ne_bot (2*d) r)
    let hB' := mul_ne_bot (by omega : 0<2*d) hB (ram_ne_bot (2*d) r)
    let s := (rep hv hn h2 hA').val
    let t := (rep hv hn h2 hB').val
    ∃ b c : Q, b≠0 ∧ c≠0 ∧
      Quaternion.normSq b*Quaternion.normSq c=(normI B:ℚ)*normI A ∧
      sandwich hv B (conjugate A) (glue hv r)=transport b c O ∧
      sandwich hv B (conjugate A) (binary v)=transport b c (pairL s t) := by
  classical
  dsimp only
  let A' := A*ram (2*d) r; let B' := B*ram (2*d) r
  have ha0 : A'≠⊥ := mul_ne_bot (by omega) hA (ram_ne_bot _ _)
  have hb0 : B'≠⊥ := mul_ne_bot (by omega) hB (ram_ne_bot _ _)
  let s := rep hv hn h2 ha0; let t := rep hv hn h2 hb0
  have hs := (Finset.mem_filter.mp s.property).1; have ht := (Finset.mem_filter.mp t.property).1
  obtain ⟨c,hc,hc0,ec⟩ := representative_frame hn h2 hv ⟨image hv A',image_isIdeal hn h2 hv A' ha0⟩
  obtain ⟨b,hb,hb0',eb⟩ := representative_frame hn h2 hv ⟨image hv B',image_isIdeal hn h2 hv B' hb0⟩
  change image hv A'=line c*J v s.val at ec; change image hv B'=line b*J v t.val at eb
  have hfull := framed hn h2 hv hs ht eb ec
  have hL := frame hv hn h2 hs ec eb
  have ea := nat_nonzero hr.ne'
  have eC : star c≠0 := by simpa using hc0
  refine ⟨(r:Q)⁻¹*b,star c,mul_ne_zero (inv_ne_zero ea) hb0',eC,?_,?_,?_⟩
  · have nB := frame_norm hn h2 hv ht hb0 hb eb
    have nA := frame_norm hn h2 hv hs ha0 hc ec
    rw [show normI B'=normI B*r by dsimp only [B']; rw [normI_mul hn h2 hB (ram_ne_bot _ _),ram_norm hr hd]] at nB
    rw [show normI A'=normI A*r by dsimp only [A']; rw [normI_mul hn h2 hA (ram_ne_bot _ _),ram_norm hr hd]] at nA
    rw [map_mul,map_inv₀,Quaternion.normSq_star,nB,nA]
    have e : Quaternion.normSq (r:Q)=(r:ℚ)^2 := by simpa only [Quaternion.coe_natCast] using Quaternion.normSq_coe (r:ℚ)
    rw [e]; push_cast; field_simp
  · rw [ram_full hv hr hd B A,hfull,←transport_scale]; rfl
  · have h := ram_binary hv hn h2 hr hd B A
    change sandwich hv B' (conjugate A') (binary v)=_ at h
    have e : line (r:Q)⁻¹*(line (r:Q)*sandwich hv B (conjugate A) (binary v))=sandwich hv B (conjugate A) (binary v) := by
      rw [←mul_assoc,two_sided_inverse ea,one_mul]
    rw [←e,←h,hL]; exact transport_scale ..
theorem filtered (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {A B : Ideal (TunnellIdealHNF.R (2*d))} (hA : A≠⊥) (hB : B≠⊥) (r : ℕ) (q : Q) :
    q∈sandwich hv B (conjugate A) (TunnellFilteredGlue.filt d v (glue hv r)) ↔
      q∈sandwich hv B (conjugate A) (glue hv r) ∧ (d:Q)*q∈sandwich hv B (conjugate A) (binary v) := by
  have hd : d≠0 := by omega
  have hw : bimod v (line (d:Q)⁻¹*binary v) := bimod_scalar (binary_stable hn h2 hv) _
    (fun q => (show Commute (d:Q) q from Nat.cast_comm d q).inv_left₀)
  rw [cutoff hd,inf_twist hv hn h2 hB (conj_ne_bot hA) (stable hn h2 hv) hw,
    scalar_twist hv _ _ _ (fun q => (show Commute (d:Q) q from Nat.cast_comm d q).inv_left₀),Submodule.mem_inf,Submodule.mem_span_singleton_mul]
  apply and_congr_right; intro _
  constructor
  · rintro ⟨y,hy,rfl⟩; rw [←mul_assoc,mul_inv_cancel₀ (nat_nonzero hd),one_mul]; exact hy
  · intro h; exact ⟨_,h,by rw [←mul_assoc,inv_mul_cancel₀ (nat_nonzero hd),one_mul]⟩
end
end TunnellGlueIsometry
end


/- TunnellGlueNorms -/
section
namespace TunnellGlueNorms
open TunnellShell TunnellHurwitz TunnellToricClass TunnellToricLocal TunnellEmbeddedIdeals
open TunnellIdealHNF TunnellPairComponents TunnellCMGluing TunnellSwitchComponents TunnellIdealGluings TunnellBinaryPairModel
open TunnellFrameNorm TunnellIntertwinerTheta TunnellGlueIsometry TunnellGenusCharacter TunnellClassThetaCount TunnellIdealThetaExpansion
noncomputable section
variable {d : ℕ} {v : Triple} (hv : v∈shell (2*d))
lemma norm_plusI (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {A B : Ideal (TunnellIdealHNF.R (2*d))} (hA : A≠⊥) (hB : B≠⊥) :
    normI (plusI B A)=normI B*normI A := by rw [plusI,normI_mul hn h2 hB (conj_ne_bot hA),conj_norm hn h2 hA]
lemma norm_minusI (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {A B C₀ : Ideal (TunnellIdealHNF.R (2*d))} (hA : A≠⊥) (hB : B≠⊥) (hC : C₀≠⊥) :
    normI (minusI B A C₀)=normI B*normI C₀*normI A := by
  rw [minusI,normI_mul hn h2 (mul_ne_bot (by omega) (conj_ne_bot hB) hC) (conj_ne_bot hA),
    normI_mul hn h2 (conj_ne_bot hB) hC,conj_norm hn h2 hA,conj_norm hn h2 hB]
theorem eval_norm (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {A B C₀ : Ideal (TunnellIdealHNF.R (2*d))} (hA : A≠⊥) (hB : B≠⊥) (hC : C₀≠⊥)
    {u : Q} (hu : u∈J (-v) v) (hu0 : u≠0) (ec : image hv C₀=line u*J v (-v)) (x : (plusI B A)×(minusI B A C₀)) :
    Quaternion.normSq (eval hv u _ _ x)=(normI B:ℚ)*normI A*(TunnellIntegralPacket.value x:ℤ) := by
  have nC := frame_norm hn h2 hv (shell_neg hv) hC hu ec
  have hc0 : (normI C₀:ℚ)≠0 := by exact_mod_cast (normI_positive (by omega) C₀ hC).ne'
  have hu' : (TunnellHurwitz.pure) v*u= -(u*(TunnellHurwitz.pure) v) := by simpa [pure_neg] using hu.2
  have hc (L : Ideal (TunnellIdealHNF.R (2*d))) (y : L) : embed (2*d) v hv y.val∈C v := center_image hv L ⟨_,y.property,rfl⟩
  have hright := scale_anti hu' hu0 (hc _ x.2)
  have hright' : 2*(u⁻¹*embed (2*d) v hv x.2.val)∈anti v := by simpa only [zsmul_eq_mul,Int.cast_ofNat] using (anti v).smul_mem (2:ℤ) hright
  change Quaternion.normSq (embed _ _ hv x.1.val+2*(u⁻¹*embed _ _ hv x.2.val))=_
  have n2 : Quaternion.normSq (2:Q)=4 := by
    have e (k : ℕ) : Quaternion.normSq (k:Q)=(k:ℚ)^2 := by simpa only [Quaternion.coe_natCast] using Quaternion.normSq_coe (k:ℚ)
    exact (e 2).trans (by norm_num)
  have hI : plusI B A≠⊥ := mul_ne_bot (by omega) hB (conj_ne_bot hA)
  have hJ : minusI B A C₀≠⊥ := mul_ne_bot (by omega) (mul_ne_bot (by omega) (conj_ne_bot hB) hC) (conj_ne_bot hA)
  rw [orthogonal (by omega) hv (hc _ x.1) hright',map_mul,map_mul,map_inv₀,n2,nC,norm_embed,norm_embed,
    norm_valZ hn h2 hI,norm_valZ hn h2 hJ,norm_plusI hn h2 hA hB,norm_minusI hn h2 hA hB hC]
  unfold TunnellIntegralPacket.value; push_cast; field_simp <;> ring
lemma act_norm (b c : Q) (N : ℚ) (hn : Quaternion.normSq b*Quaternion.normSq c=N) (x : Q) :
    Quaternion.normSq (action b c x)=N*Quaternion.normSq x := by
  unfold action; rw [map_mul,map_mul,←hn]; ring
end
end TunnellGlueNorms
end


/- TunnellGeometricPacket -/
section
namespace TunnellGeometricPacket
open TunnellShell TunnellHurwitz TunnellToricClass TunnellToricLocal TunnellEmbeddedIdeals
open TunnellIdealHNF TunnellPairComponents TunnellSwitchComponents TunnellIdealGluings TunnellBinaryPairModel
open TunnellFrameNorm TunnellIntertwinerTheta TunnellGlueIsometry TunnellGenusCharacter TunnellClassThetaCount TunnellIdealThetaExpansion
open TunnellRamifiedSwitch TunnellFilteredGlue TunnellGlueMaximal TunnellRamifiedClasses TunnellGlueNorms TunnellIntegralPacket
open TunnellIdealFormBasis TunnellRamifiedLines TunnellGluePacket TunnellFramedGlue
noncomputable section
variable {M : Type*} [AddCommGroup M]
def numerator (d : ℕ) (e : M →+ Q) (D : Lattice) : AddSubgroup M :=
  (line (d:Q)*D).toAddSubgroup.comap e
lemma mem_num (d : ℕ) (e : M →+ Q) (D : Lattice) (x : M) :
    x∈numerator d e D ↔ ∃ q∈D, (d:Q)*q=e x := Submodule.mem_span_singleton_mul
lemma range_in (d : ℕ) {e : M →+ Q} {D L : Lattice} (he : e.range.toIntSubmodule=L) (hle : L≤D) (x : M) :
    (d:ℤ) • x∈numerator d e D := by
  rw [mem_num,map_zsmul,zsmul_eq_mul,Int.cast_natCast]
  exact ⟨e x,hle (he ▸ (show e x∈e.range.toIntSubmodule from ⟨x,rfl⟩)),rfl⟩
lemma pairL_le (s t : Triple) : pairL s t≤O := by
  apply sup_le (fun _ h => h.1)
  intro x hx; obtain ⟨y,hy,rfl⟩ := Submodule.mem_span_singleton_mul.mp hx
  simpa only [zsmul_eq_mul,Int.cast_ofNat] using O.smul_mem (2:ℤ) hy.1
lemma recover {d : ℕ} (hd : d≠0) {e : M →+ Q} {D D' K K' L : Lattice} (eL : e.range.toIntSubmodule=L)
    (hK : ∀ q, q∈K ↔ q∈D ∧ (d:Q)*q∈L) (hK' : ∀ q, q∈K' ↔ q∈D' ∧ (d:Q)*q∈L)
    (h : numerator d e D ≤ numerator d e D') : K≤K' := by
  intro q hq; obtain ⟨hx,hy⟩ := (hK _).mp hq
  obtain ⟨x,ex⟩ : ∃ x, e x=(d:Q)*q := by rw [←eL] at hy; exact hy
  obtain ⟨q',hq',eq⟩ := (mem_num _ _ _ _).mp (h ((mem_num _ _ _ _).mpr ⟨q,hx,ex.symm⟩))
  exact (hK' _).mpr ⟨(mul_left_cancel₀ (nat_nonzero hd) (eq.trans ex)) ▸ hq',hy⟩
lemma maximal {d p : ℕ} [Fact p.Prime] (hp : p∣d) (hp2 : p≠2) (hn : Squarefree (2*d)) (hd : 0<d)
    {s t : Triple} (hs : s∈shell (2*d)) (ht : t∈shell (2*d)) {e : M →+ Q} {D L : Lattice} (eL : e.range.toIntSubmodule=L)
    {b c : Q} (hb : b≠0) (hc : c≠0) (hD : D=transport b c O) (hL : L=transport b c (pairL s t)) :
    ∃ x∈numerator d e D, ¬∃ y:M, x=(p:ℤ) • y := by
  obtain ⟨q,hq,ha,h₀⟩ := nonzero hp hp2 hn hd hs ht
  have hq' : action b c q∈D := hD ▸ (action_mem hb hc O q).mpr hq
  have hqL : (d:Q)*action b c q∈L := by rw [hL,action_nat,action_mem hb hc]; exact (admits_mem ..).mp ha
  obtain ⟨x,ex⟩ : ∃ x, e x=(d:Q)*action b c q := by rw [←eL] at hqL; exact hqL
  refine ⟨x,(mem_num _ _ _ _).mpr ⟨_,hq',ex.symm⟩,?_⟩
  rintro ⟨y,rfl⟩
  rw [map_zsmul,zsmul_eq_mul,Int.cast_natCast] at ex
  have hdv : (d:Q)=(p:Q)*((d/p:ℕ):Q) := by rw [←Nat.cast_mul,Nat.mul_div_cancel' hp]
  rw [hdv,mul_assoc] at ex
  have her := mul_left_cancel₀ (nat_nonzero (Fact.out:p.Prime).ne_zero) ex
  have hmem : e y∈L := eL ▸ (show e y∈e.range.toIntSubmodule from ⟨y,rfl⟩)
  rw [her,action_nat,hL,action_mem hb hc] at hmem
  exact h₀ hmem
variable {d : ℕ} {v : Triple} (hv : v∈shell (2*d))
private instance prime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
def orders (A B : Ideal (TunnellIdealHNF.R (2*d))) (r : ↥d.divisors) := sandwich hv B (conjugate A) (glue hv r.val)
def gluing (u : Q) (A B C₀ : Ideal (TunnellIdealHNF.R (2*d))) (r : ↥d.divisors) := numerator d (eval hv u (plusI B A) (minusI B A C₀)) (orders hv A B r)
theorem properties (hs : Squarefree d) (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hodd : Odd d)
    {A B C₀ : Ideal (TunnellIdealHNF.R (2*d))} (hA : A≠⊥) (hB : B≠⊥) (hC : C₀≠⊥)
    {u : Q} (hu : u∈J (-v) v) (hu0 : u≠0) (ec : image hv C₀=line u*J v (-v))
    : let X := gluing hv u A B C₀
      Function.Injective X ∧ (∀ r (y : (plusI B A)×(minusI B A C₀)), (d:ℤ) • y∈X r) ∧
      (∀ r x, x∈X r → (d:ℤ)^2∣value x) ∧ (∀ r (i : P d), ∃ x∈X r, ¬∃ y : (plusI B A)×(minusI B A C₀), x=(i.val:ℤ) • y) := by
  classical
  let e := eval hv u (plusI B A) (minusI B A C₀)
  let L := sandwich hv B (conjugate A) (binary v)
  let D := orders hv A B
  let X := gluing hv u A B C₀
  let K (r : ↥d.divisors) := sandwich hv B (conjugate A) (TunnellFilteredGlue.filt d v (glue hv r.val))
  have h₀ : 0<d := by omega
  have hI : plusI B A≠⊥ := mul_ne_bot (by omega) hB (conj_ne_bot hA)
  have hJ : minusI B A C₀≠⊥ := mul_ne_bot (by omega) (mul_ne_bot (by omega) (conj_ne_bot hB) hC) (conj_ne_bot hA)
  have eL : e.range.toIntSubmodule=L := range_eq hv hn h2 (by simpa [pure_neg] using hu.2) hu0 ec B A
  have hK (r : ↥d.divisors) (q : Q) : q∈K r ↔ q∈D r ∧ (d:Q)*q∈L := filtered hv hn h2 hA hB r.val q
  have hi : Function.Injective X := by
    intro a b eq; apply distinct hs hn hodd h2 hv hB (conj_ne_bot hA)
    exact le_antisymm (recover h₀.ne' eL (hK a) (hK b) eq.le) (recover h₀.ne' eL (hK b) (hK a) eq.ge)
  have F (r : ↥d.divisors) : ∃ s∈shell (2*d), ∃ t∈shell (2*d), ∃ b c : Q, b≠0 ∧ c≠0 ∧
      Quaternion.normSq b*Quaternion.normSq c=(normI B:ℚ)*normI A ∧ D r=transport b c O ∧ L=transport b c (pairL s t) := by
    obtain ⟨hr,hd0⟩ := Nat.mem_divisors.mp r.property
    obtain ⟨b,c,hb,hc,hnr,hD,hL⟩ := frames hv hn h2 hA hB (Nat.pos_of_dvd_of_pos hr h₀) (hr.trans (dvd_mul_left ..))
    refine ⟨_,(Finset.mem_filter.mp (rep hv hn h2 (mul_ne_bot (by omega) hA (ram_ne_bot _ r.val))).property).1,
      _,(Finset.mem_filter.mp (rep hv hn h2 (mul_ne_bot (by omega) hB (ram_ne_bot _ r.val))).property).1,b,c,hb,hc,hnr,hD,hL⟩
  refine ⟨hi,?_,?_,?_⟩
  · intro r x; obtain ⟨s,_,t,_,b,c,hb,hc,_,hD,hL⟩ := F r
    apply range_in d eL _ x
    change L≤D r; rw [hL,hD]; exact mul_le_mul_left (mul_le_mul_right (pairL_le s t) _) _
  · intro r x hx; obtain ⟨s,_,t,_,b,c,hb,hc,hNr,hD,_⟩ := F r
    obtain ⟨q,hq,eq⟩ := (mem_num d e (D r) x).mp hx
    obtain ⟨y,hy,rfl⟩ := mem_transport.mp (hD ▸ hq)
    obtain ⟨k,hk⟩ := norm_int hy
    have ee := congrArg Quaternion.normSq eq
    rw [map_mul,act_norm b c _ hNr,hk,eval_norm hv hn h2 hA hB hC hu hu0 ec] at ee
    have eN : Quaternion.normSq (d:Q)=(d:ℚ)^2 := by simpa only [Quaternion.coe_natCast] using Quaternion.normSq_coe (d:ℚ)
    rw [eN] at ee
    have hp : (normI B:ℚ)*normI A≠0 := mul_ne_zero (by exact_mod_cast (normI_positive (by omega) B hB).ne') (by exact_mod_cast (normI_positive (by omega) A hA).ne')
    refine ⟨k,?_⟩
    have h : (value x:ℚ)=(d:ℚ)^2*k := by apply mul_left_cancel₀ hp; linear_combination -ee
    exact_mod_cast h
  · intro r i; obtain ⟨s,hs',t,ht',b,c,hb,hc,_,hD,hL⟩ := F r
    have hp := Nat.dvd_of_mem_primeFactors i.property
    have hp2 : i.val≠2 := by intro he; rw [he] at hp; exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hp)
    exact maximal hp hp2 hn h₀ hs' ht' eL hb hc hD hL
theorem geometric (hs : Squarefree d) (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hodd : Odd d)
    {A B C₀ : Ideal (TunnellIdealHNF.R (2*d))} (hA : A≠⊥) (hB : B≠⊥) (hC : C₀≠⊥)
    {u : Q} (hu : u∈J (-v) v) (hu0 : u≠0) (ec : image hv C₀=line u*J v (-v))
    (U : (i : P d) → LocalBasis i.val (plusI B A)) (V : (i : P d) → LocalBasis i.val (minusI B A C₀)) :
    ∃ z : (i : P d) → ZMod i.val, (∀ i, z i^2=parameter U V i) ∧
      ∃ E : ↥d.divisors ≃ (P d → Bool), ∀ r, (gluing hv u A B C₀ r).map (packet U V)=linePacket (TunnellAllRamifiedLines.signed z (E r)) := by
  obtain ⟨hi,hD,hN,hmax⟩ := properties hv hs hn h2 hodd hA hB hC hu hu0 ec
  exact TunnellIntegralPacket.trace U V hs hn h2 (mul_ne_bot (by omega) hB (conj_ne_bot hA))
    (mul_ne_bot (by omega) (mul_ne_bot (by omega) (conj_ne_bot hB) hC) (conj_ne_bot hA)) hodd _ hi hD hN hmax
end
end TunnellGeometricPacket
end


/- TunnellQuaternionUnits -/
section
namespace TunnellQuaternion
open TunnellShell Finset Quaternion
def leftUnit (j : Fin 4) (q : QInt) : QInt := ![q,
  ⟨-q.imI,q.re,-q.imK,q.imJ⟩,⟨-q.imJ,q.imK,q.re,-q.imI⟩,⟨-q.imK,-q.imJ,q.imI,q.re⟩] j
def unitEquiv (j : Fin 4) : QInt ≃ QInt where
  toFun := leftUnit j
  invFun q := if j=0 then q else -(leftUnit j q)
  left_inv q := by
    fin_cases j
    · rfl
    all_goals
      apply QuaternionAlgebra.ext
      all_goals exact neg_neg _
  right_inv q := by
    fin_cases j
    · rfl
    all_goals
      apply QuaternionAlgebra.ext
      all_goals exact neg_neg _
lemma norm_unit (j : Fin 4) (q : QInt) : Quaternion.normSq (leftUnit j q) = Quaternion.normSq q := by
  simp only [Quaternion.normSq_def']
  fin_cases j <;> simp [leftUnit] <;> ring
lemma sum_unit (p : ℕ) (j : Fin 4) (f : QInt → ℤ) :
    ∑ q ∈ quatShell p, f (leftUnit j q) = ∑ q ∈ quatShell p, f q := by
  apply sum_nbij' (unitEquiv j) (unitEquiv j).symm
  · intro x hx; simpa only [mem_quatShell,norm_unit,unitEquiv,Equiv.coe_fn_mk] using hx
  · intro x hx
    rw [mem_quatShell] at hx ⊢
    rw [←norm_unit j]
    exact (congrArg Quaternion.normSq ((unitEquiv j).apply_symm_apply x)).trans hx
  · exact fun x _ => (unitEquiv j).symm_apply_apply x
  · exact fun x _ => (unitEquiv j).apply_symm_apply x
  · exact fun _ _ => rfl
lemma coordWeight_unit (j : Fin 4) (q : QInt) (v : Triple) :
    coordWeight (rotate (leftUnit j q) v) = coordWeight (rotate q v) := by
  obtain ⟨a,b,c,d⟩ := q
  obtain ⟨x,y,z⟩ := v
  let R := rotate (⟨a,b,c,d⟩:QInt) (x,y,z)
  have co (u v w : ℤ) (e₁ e₂ e₃ : ℤ) (h₁ : e₁=1 ∨ e₁ = -1) (h₂ : e₂=1 ∨ e₂ = -1)
      (h₃ : e₃=1 ∨ e₃ = -1) :
      coordWeight (e₁*u,e₂*v,e₃*w) = coordWeight (u,v,w) := by
    rcases h₁ with rfl|rfl <;> rcases h₂ with rfl|rfl <;> rcases h₃ with rfl|rfl <;>
      simp [coordWeight_eq,lastWeight_neg]
  have hi : rotate (leftUnit j ⟨a,b,c,d⟩) (x,y,z) =
      (![1,1,-1,-1] j*R.1, ![1,-1,1,-1] j*R.2.1, ![1,-1,-1,1] j*R.2.2) := by
    fin_cases j <;> simp [leftUnit,R,rotate_apply] <;> ring_nf <;> simp
  rw [hi]
  apply co <;> fin_cases j <;> decide
lemma sq_mod_four (z : ℤ) : z^2 ≡ z%2 [ZMOD 4] := by
  obtain ⟨r,hr|hr⟩ := Int.even_or_odd' z <;> subst z
  · change _%4 = _%4
    ring_nf
    omega
  · change _%4 = _%4
    ring_nf
    omega
lemma parity_count (p : ℕ) (hp : Odd p) {q : QInt} (hq : q ∈ quatShell p) :
    q.re%2+q.imI%2+q.imJ%2+q.imK%2 = (p%4:ℕ) := by
  have h := (((sq_mod_four q.re).add (sq_mod_four q.imI)).add (sq_mod_four q.imJ)).add (sq_mod_four q.imK)
  rw [←Quaternion.normSq_def', mem_quatShell.mp hq] at h
  have hn := Nat.odd_iff.mp hp
  change (p:ℤ)%4 = _ %4 at h
  omega
theorem four_sections (p : ℕ) (hp : Odd p) (v : Triple) :
    ∑ q ∈ quatShell p, coordWeight (rotate q v) =
       4 * ∑ q ∈ quatShell p,
         if q.re%2 = (if p%4=1 then 1 else 0) then coordWeight (rotate q v) else 0 := by
  let e : ℤ := if p%4=1 then 1 else 0
  let F (q : QInt) := coordWeight (rotate q v)
  let w (q : QInt) := if q.re%2=e then F q else 0
  have hc (q : QInt) (hq : q ∈ quatShell p) : F q = ∑ i : Fin 4, w (leftUnit i q) := by
    simp only [w,F,coordWeight_unit]
    rw [Fin.sum_univ_four]
    simp [leftUnit,Int.neg_emod_two]
    have h := parity_count p hp hq
    have ho := Nat.odd_iff.mp hp
    simp only [e] at *
    split_ifs at * <;> omega
  change ∑ q ∈ quatShell p, F q = 4 * ∑ q ∈ quatShell p, w q
  rw [sum_congr rfl hc,sum_comm]
  simp only [sum_unit,Finset.sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul, Nat.cast_ofNat]
end TunnellQuaternion
end


/- TunnellQuaternionResidue -/
section
namespace TunnellQuaternion
open TunnellShell Quaternion
lemma split_coord (k r s t : ℤ) (v : Triple) :
    coordWeight (rotate ⟨2*k+1,2*r,2*s,2*t⟩ v) = ((r+s).negOnePow:ℤ)*coordWeight v := by
  obtain ⟨x,y,z⟩ := v
  rw [rotate_apply,coordWeight_eq,coordWeight_eq]
  have hxy :
      (Odd (((2*k+1)^2+(2*r)^2-(2*s)^2-(2*t)^2)*x+2*((2*r)*(2*s)-(2*k+1)*(2*t))*y+
        2*((2*r)*(2*t)+(2*k+1)*(2*s))*z) ∧
       Odd (2*((2*r)*(2*s)+(2*k+1)*(2*t))*x+((2*k+1)^2-(2*r)^2+(2*s)^2-(2*t)^2)*y+
        2*((2*s)*(2*t)-(2*k+1)*(2*r))*z)) ↔ Odd x ∧ Odd y := by
    simp only [Int.odd_iff]
    ring_nf
    omega
  simp only [hxy]
  split_ifs with h
  · obtain ⟨⟨i,rfl⟩,⟨j,rfl⟩⟩ := h
    obtain ⟨l,hl|hl⟩ := Int.even_or_odd' z <;> subst z
    · rw [←lastWeight_add_four]
      apply lastWeight_congr
      change _ % 8 = _ % 8
      ring_nf
      omega
    · simp only [lastWeight]
      split_ifs <;> ring_nf at * <;> omega
  · ring
lemma inert_coord (k r s t : ℤ) (v : Triple) :
    coordWeight (rotate ⟨2*k,-(2*r+1),2*s+1,2*t+1⟩ v) =
      -coordWeight (rotate ⟨2*k,2*r+1,2*s+1,2*t+1⟩ v) := by
  obtain ⟨x,y,z⟩ := v
  simp only [rotate_apply,coordWeight_eq,Int.odd_iff]
  split_ifs with h h' h'
  · obtain ⟨i,hi|hi⟩ := Int.even_or_odd' x
    · subst x
      ring_nf at h
      omega
    · subst x
      have hc (w : ℤ) : lastWeight (w+4) = -lastWeight w := by
        simpa using lastWeight_add_four w 1
      rw [←hc]
      apply lastWeight_congr
      change _ % 8 = _ % 8
      ring_nf
      omega
  · ring_nf at h h'
    omega
  · ring_nf at h h'
    omega
  · simp
end TunnellQuaternion
end


/- TunnellToricLocalSign -/
section
namespace TunnellToricSign
open TunnellHurwitzFour TunnellHurwitz TunnellToric TunnellShell
abbrev Z8 := ZMod 8
abbrev Vec (R : Type*) := R × R × R
def rotate {R : Type*} [CommRing R] (q : H R) (v : Vec R) : Vec R :=
  let (a,b,c,d) := q
  let (x,y,z) := v
  let l := (a+b+c)*d+d^2
  ((a^2+b^2-c^2+(a+b-c)*d)*x+(2*b*c+(b+c-a)*d)*y+(2*a*c+l)*z,
   (2*b*c+l)*x+(a^2-b^2+c^2+(a-b+c)*d)*y+(-2*a*b+(c-a-b)*d)*z,
   (-2*a*c+(b-a-c)*d)*x+(2*a*b+l)*y+(a^2-b^2-c^2+(a-b-c)*d)*z)
lemma rotate_eq (q : H ℤ) (v : Triple) : TunnellHurwitz.pure (rotate q v)=act (hamZ q) v := by
  obtain ⟨a,b,c,d⟩ := q
  obtain ⟨x,y,z⟩ := v
  apply QuaternionAlgebra.ext
  all_goals simp only [act,Quaternion.re_mul,Quaternion.imI_mul,Quaternion.imJ_mul,Quaternion.imK_mul,
    Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star]
  all_goals dsimp [rotate,TunnellHurwitz.pure,hamZ,ham]; push_cast; ring
def color (v : Vec Z8) : ℤ :=
  let a := if v.1.val%2=0 then v.1 else if v.2.1.val%2=0 then v.2.1 else v.2.2
  if a=0 then 1 else if a=4 then -1 else 0
def lift4 (q : H4) : H Z8 := (q.1.val,q.2.1.val,q.2.2.1.val,q.2.2.2.val)
def fast (q : H4) : ℤ := color (rotate (lift4 q) (1,1,0))
def character (q : H4) : ℤ := if q∈orbit e then 1 else -1
set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
def orbitScalar (q:H4) : ℤ := if (nr q).val%2=1 ∧ sideOrbit q=false then 1 else -1

lemma characterOrbit (q:H4) : character q=orbitScalar q := by
  have h := orbit_iff false q
  change q∈orbit e ↔ q∈units ∧ sideOrbit q=false at h
  simp only [units,Finset.mem_filter,Finset.mem_univ,true_and] at h
  simp only [character,h,orbitScalar]

private abbrev caseFast (a b:Z4) := ∀ c d:Z4,
    let q:H4 := (a,b,c,d)
    (nr q).val%2=1 → fast q=orbitScalar q
set_option maxRecDepth 10000 in
private lemma caseFast00 : caseFast 0 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast01 : caseFast 0 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast02 : caseFast 0 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast03 : caseFast 0 3 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast10 : caseFast 1 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast11 : caseFast 1 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast12 : caseFast 1 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast13 : caseFast 1 3 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast20 : caseFast 2 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast21 : caseFast 2 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast22 : caseFast 2 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast23 : caseFast 2 3 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast30 : caseFast 3 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast31 : caseFast 3 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast32 : caseFast 3 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseFast33 : caseFast 3 3 := by decide
lemma character_table : ∀ q ∈ units, fast q=character q := by
  simp only [characterOrbit,units,Finset.mem_filter,Finset.mem_univ,true_and]
  rintro ⟨a,b,c,d⟩
  fin_cases a <;> fin_cases b
  · exact caseFast00 c d
  · exact caseFast01 c d
  · exact caseFast02 c d
  · exact caseFast03 c d
  · exact caseFast10 c d
  · exact caseFast11 c d
  · exact caseFast12 c d
  · exact caseFast13 c d
  · exact caseFast20 c d
  · exact caseFast21 c d
  · exact caseFast22 c d
  · exact caseFast23 c d
  · exact caseFast30 c d
  · exact caseFast31 c d
  · exact caseFast32 c d
  · exact caseFast33 c d

set_option maxRecDepth 10000 in
set_option maxHeartbeats 30000000 in
private abbrev caseRotation (a b:Z4) := ∀ c d:Z4,
    let q:H4 := (a,b,c,d)
    (nr q).val%2=1 → ∀ x:Z8, x.val%2=1 → ∀ k l:ZMod 2, color (rotate (lift4 q) (x,x+4*(k.val:Z8),4*(l.val:Z8)))=fast q*(if l=0 then 1 else -1)
set_option maxRecDepth 10000 in
private lemma caseRotation00 : caseRotation 0 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation01 : caseRotation 0 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation02 : caseRotation 0 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation03 : caseRotation 0 3 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation10 : caseRotation 1 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation11 : caseRotation 1 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation12 : caseRotation 1 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation13 : caseRotation 1 3 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation20 : caseRotation 2 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation21 : caseRotation 2 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation22 : caseRotation 2 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation23 : caseRotation 2 3 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation30 : caseRotation 3 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation31 : caseRotation 3 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation32 : caseRotation 3 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseRotation33 : caseRotation 3 3 := by decide
lemma table : ∀ q ∈ units, ∀ x : Z8, x.val%2=1 → ∀ k l : ZMod 2,
    color (rotate (lift4 q) (x,x+4*(k.val:Z8),4*(l.val:Z8)))=fast q * (if l=0 then 1 else -1) := by
  simp only [units,Finset.mem_filter,Finset.mem_univ,true_and]
  rintro ⟨a,b,c,d⟩
  fin_cases a <;> fin_cases b
  · exact caseRotation00 c d
  · exact caseRotation01 c d
  · exact caseRotation02 c d
  · exact caseRotation03 c d
  · exact caseRotation10 c d
  · exact caseRotation11 c d
  · exact caseRotation12 c d
  · exact caseRotation13 c d
  · exact caseRotation20 c d
  · exact caseRotation21 c d
  · exact caseRotation22 c d
  · exact caseRotation23 c d
  · exact caseRotation30 c d
  · exact caseRotation31 c d
  · exact caseRotation32 c d
  · exact caseRotation33 c d

def shift4 (q u : H Z8) : H Z8 := (q.1+4*u.1,q.2.1+4*u.2.1,q.2.2.1+4*u.2.2.1,q.2.2.2+4*u.2.2.2)
lemma periodic (q u : H Z8) (x k l : Z8) :
    rotate (shift4 q u) (x,x+4*k,4*l)=rotate q (x,x+4*k,4*l) := by
  obtain ⟨a,b,c,d⟩ := q
  obtain ⟨A,B,C,D⟩ := u
  change rotate (a+4*A,b+4*B,c+4*C,d+4*D) (x,x+4*k,4*l)=_
  simp only [rotate,Prod.mk.injEq]
  have e8 : (8:Z8)=0 := by decide
  have e16 : (16:Z8)=0 := by decide
  have e32 : (32:Z8)=0 := by decide
  have e64 : (64:Z8)=0 := by decide
  have e128 : (128:Z8)=0 := by decide
  refine ⟨?_,?_,?_⟩ <;> rw [←sub_eq_zero] <;> ring_nf <;> simp [e8,e16,e32,e64,e128]
def redVec (v : Triple) : Vec Z8 := (v.1,v.2.1,v.2.2)
def redH (q : H ℤ) : H Z8 := (q.1,q.2.1,q.2.2.1,q.2.2.2)
lemma red_rot (q : H ℤ) (v : Triple) : redVec (rotate q v)=rotate (redH q) (redVec v) := by
  obtain ⟨a,b,c,d⟩ := q
  obtain ⟨x,y,z⟩ := v
  simp [redVec, redH, rotate]
lemma redH_shift (q : H ℤ) : ∃ u, redH q=shift4 (lift4 (modFour q)) u := by
  have e (a : ℤ) : (a:Z8)=((a:Z4).val:Z8)+4*((a/4:ℤ):Z8) := by
    have hh := ZMod.val_intCast (n:=4) a
    have he : a=(((a:Z4).val:ℕ):ℤ)+4*(a/4) := by omega
    exact_mod_cast congrArg (fun z:ℤ => (z:Z8)) he
  exact ⟨(↑(q.1/4:ℤ),↑(q.2.1/4:ℤ),↑(q.2.2.1/4:ℤ),↑(q.2.2.2/4:ℤ)),
    Prod.ext (e _) (Prod.ext (e _) (Prod.ext (e _) (e _)))⟩
lemma red4 (k : ℤ) : 4*(k:Z8)=4*((k:ZMod 2).val:Z8) := by
  have hh := ZMod.val_intCast (n:=2) k
  have he : 4*k=4*(((k:ZMod 2).val:ℕ):ℤ)+8*(k/2) := by omega
  have ht := congrArg (fun z:ℤ => (z:Z8)) he
  push_cast at ht
  simpa [show (8:Z8)=0 by decide] using ht
lemma odd_units (q : H ℤ) (hn : Odd (nr q)) : modFour q ∈ units := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  have h : (nr (modFour q))=((nr q:ℤ):Z4) := by obtain ⟨a,b,c,d⟩ := q; simp [nr,modFour]
  rw [h]
  have hh := ZMod.val_intCast (n:=4) (nr q)
  have he := Int.odd_iff.mp hn
  omega
lemma color_rotate {v : Triple} (hx : Odd v.1) (hy : v.2.1%4=v.1%4) (hz : 4∣v.2.2)
    {q : H ℤ} (hq : Odd (nr q)) :
    color (redVec (rotate q v))=character (modFour q)*color (redVec v) := by
  obtain ⟨x,y,z⟩ := v
  change y%4=x%4 at hy
  change (4:ℤ)∣z at hz
  obtain ⟨l,rfl⟩ := hz
  have hk : ∃ k : ℤ, y=x+4*k := ⟨(y-x)/4,by omega⟩
  obtain ⟨k,rfl⟩ := hk
  have hq4 := odd_units q hq
  have hv8 : (x:Z8).val%2=1 := by
    have h := ZMod.val_intCast (n:=8) x
    have e := Int.odd_iff.mp hx; dsimp only at e; omega
  have hh : redVec (x,x+4*k,4*l)=((x:Z8),x+4*(k:Z8),4*(l:Z8)) := by simp [redVec]
  have term := table (modFour q) hq4 (x:Z8) hv8 (k:ZMod 2) (l:ZMod 2)
  rw [red_rot,hh]
  obtain ⟨u,hu⟩ := redH_shift q
  rw [hu,periodic, red4 k,red4 l,←character_table _ hq4,term]
  congr 1
  have e : ∀ x : Z8, x.val%2=1 → ∀ k l : ZMod 2, (if l=0 then (1:ℤ) else -1)=color (x,x+4*(k.val:Z8),4*(l.val:Z8)) := by decide
  exact e _ hv8 _ _
lemma smul_rotate {v w : Triple} {q : H ℤ}
    (h : TunnellHurwitz.pure w * hamZ q = hamZ q * TunnellHurwitz.pure v) : rotate q v=(nr q) • w := by
  apply TunnellHurwitz.pure_injective
  rw [rotate_eq,act,←h,mul_assoc,Quaternion.self_mul_star,Quaternion.mul_coe_eq_smul,norm_ham]
  apply QuaternionAlgebra.ext <;>
    simp only [Quaternion.re_smul,Quaternion.imI_smul,Quaternion.imJ_smul,Quaternion.imK_smul] <;>
    simp [TunnellHurwitz.pure]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma scale_table : ∀ t : Z8, t.val%2=1 → ∀ v : Vec Z8, color (t*v.1,t*v.2.1,t*v.2.2)=color v := by decide
theorem character_of_intertwiner {v w : Triple} (hx : Odd v.1) (hy : v.2.1%4=v.1%4)
    (hz : 4∣v.2.2) {q : H ℤ} (hq : Odd (nr q))
    (h : TunnellHurwitz.pure w*hamZ q=hamZ q*TunnellHurwitz.pure v) :
    color (redVec w)=character (modFour q)*color (redVec v) := by
  have he := color_rotate hx hy hz hq
  rw [smul_rotate h] at he
  have hh : redVec (nr q • w)=(((nr q:ℤ):Z8)*(w.1:Z8),((nr q:ℤ):Z8)*(w.2.1:Z8),((nr q:ℤ):Z8)*(w.2.2:Z8)) := by simp [redVec]
  rw [hh] at he
  exact (scale_table ((nr q:ℤ):Z8) (by have t := ZMod.val_intCast (n:=8) (nr q); have e := Int.odd_iff.mp hq; omega) (redVec w)).symm.trans he
end TunnellToricSign
end


/- TunnellQuaternionClasses -/
section
namespace TunnellQuaternion
open Finset Quaternion
variable {p : ℕ} [Fact p.Prime] (M : Model p)
lemma unique_class {q : QInt} (hq : normSq q=p) : ∃! l, inLine l (residue M q) := by
  apply line_unique _ (norm_prime_nonzero M hq)
  rw [residue_det,hq]
  simp
noncomputable def classOf (q : QInt) : Option (ZMod p) :=
  if h : normSq q = p then (unique_class M h).exists.choose else none
lemma class_eq_iff {q : QInt} (hq : normSq q=p) (l : Option (ZMod p)) :
    classOf M q=l ↔ inLine l (residue M q) := by
  rw [classOf,dif_pos hq]
  have h := (unique_class M hq).exists.choose_spec
  constructor
  · rintro rfl
    exact h
  · exact fun h' => (unique_class M hq).unique h h'
lemma quatShell_one_card : (quatShell 1).card = 8 := by decide
lemma fiber_class_card (hp : p≠2) (l : Option (ZMod p)) :
    ((quatShell p).filter (fun q => classOf M q = l)).card = 8 := by
  classical
  obtain ⟨q,hq,hl⟩ := exists_at_line M hp l
  rw [←quatShell_one_card]
  symm
  apply card_nbij (fun u => q*u)
  · intro u hu
    have hu' := mem_quatShell.mp hu
    have hqu : normSq (q*u)=p := by rw [map_mul,hq,hu']; simp
    refine mem_filter.mpr ⟨mem_quatShell.mpr hqu,(class_eq_iff M hqu l).mpr ?_⟩
    rw [map_mul]
    exact line_mul hl _
  · intro u hu v hv h
    apply scalar_cancel (p:ℤ) (by exact_mod_cast (Fact.out:p.Prime).ne_zero)
    have he := congrArg (star q * ·) h
    simpa only [←mul_assoc,star_mul_self,hq,coe_mul_eq_smul] using he
  · intro w hw
    obtain ⟨hn,he⟩ := mem_filter.mp hw
    have hn' := mem_quatShell.mp hn
    obtain ⟨u,hu,hw⟩ := (same_line_iff M hq hn' hl).mp ((class_eq_iff M hn' l).mp he)
    exact ⟨u,mem_quatShell.mpr hu,hw.symm⟩
lemma card_class_mem (hp : p≠2) (L : Finset (Option (ZMod p))) :
    ((quatShell p).filter (fun q => classOf M q ∈ L)).card = 8*L.card := by
  classical
  have h := Finset.sum_fiberwise_eq_sum_filter (quatShell p) L (classOf M) (fun _ => (1:ℕ))
  simp only [sum_const,nsmul_eq_mul,mul_one] at h
  simpa [fiber_class_card M hp,mul_comm] using h.symm
end TunnellQuaternion
end


/- TunnellJacobiOdd -/
section
namespace TunnellQuaternion
open Finset Quaternion
open scoped Classical
noncomputable section
lemma quat_left_cancel {q u v : QInt} (hq : normSq q≠0) (h : q*u=q*v) : u=v := by
  apply scalar_cancel (normSq q) hq
  have he := congrArg (star q * ·) h
  simpa only [←mul_assoc, star_mul_self,coe_mul_eq_smul] using he
lemma count_left_factors {α : Type*} [DecidableEq α] (D : Finset α) (q : α→QInt) {d : ℕ}
    (hd : d≠0) (hq : ∀ a ∈ D, normSq (q a)=d) (n : ℕ) :
    D.card*(quatShell n).card = ∑ w ∈ quatShell (d*n),
      (D.filter (fun a => ∃ u : QInt, w=q a*u)).card := by
  classical
  let S := D ×ˢ quatShell n
  let f (a : α × QInt) := q a.1 * a.2
  have h : (S:Set _).MapsTo f (quatShell (d*n)) := by
    rintro ⟨a,u⟩ h
    obtain ⟨ha,hu⟩ := mem_product.mp h
    exact mem_quatShell.mpr (by simp [f,hq a ha,mem_quatShell.mp hu])
  rw [←card_product,card_eq_sum_card_fiberwise h]
  apply sum_congr rfl
  intro w hw
  apply card_nbij Prod.fst
  · rintro ⟨a,u⟩ h
    obtain ⟨hu,hf⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨(mem_product.mp hu).1,u,hf.symm⟩
  · rintro ⟨a,u⟩ hu ⟨b,v⟩ hv he
    change a=b at he
    subst b
    obtain ⟨hau,hw'⟩ := mem_filter.mp hu
    have ha := (mem_product.mp hau).1
    exact Prod.ext rfl (quat_left_cancel (by rw [hq a ha]; exact_mod_cast hd) (hw'.trans (mem_filter.mp hv).2.symm))
  · intro a ha
    obtain ⟨ha',u,rfl⟩ := mem_filter.mp ha
    have hw' := mem_quatShell.mp hw
    rw [map_mul,hq a ha',Nat.cast_mul] at hw'
    have hu := mul_left_cancel₀ (by exact_mod_cast hd : (d:ℤ)≠0) hw'
    exact ⟨(a,u),mem_filter.mpr ⟨mem_product.mpr ⟨ha',mem_quatShell.mpr hu⟩,rfl⟩,rfl⟩
lemma quatShell_prime_card {p : ℕ} [Fact p.Prime] (hp : p≠2) : (quatShell p).card=8*(p+1) := by
  simpa using card_class_mem (localModel hp) hp univ
lemma odd_factors_card {p : ℕ} [Fact p.Prime] (hp : p≠2) (n : ℕ) (w : QInt)
    (hw : w∈quatShell (p*n)) :
    ((quatShell p).filter (fun q => ∃ u : QInt, w=q*u)).card =
      if red p w=0 then 8*(p+1) else 8 := by
  classical
  let M := localModel hp
  have hdet : (residue M w).det=0 := by
    rw [residue_det,mem_quatShell.mp hw]
    simp
  split_ifs with h
  · have hw0 := (residue_zero M w).mpr h
    have hall : ∀ q ∈ quatShell p, ∃ u : QInt, w=q*u := by
      intro q hq
      have hqn := mem_quatShell.mp hq
      apply divide_left M hqn ((class_eq_iff M hqn _).mp rfl)
      rw [hw0]
      cases classOf M q <;> simp [inLine]
    simpa [filter_eq_self.mpr hall] using quatShell_prime_card hp
  · obtain ⟨l,hl,hu⟩ := line_unique _ (fun he => h ((residue_zero M w).mp he)) hdet
    rw [←fiber_class_card M hp l]
    congr 1
    apply filter_congr
    intro q hq
    have hqn := mem_quatShell.mp hq
    constructor
    · rintro ⟨u,rfl⟩
      apply hu
      rw [map_mul]
      exact line_mul ((class_eq_iff M hqn _).mp rfl) _
    · intro hq'
      exact divide_left M hqn ((class_eq_iff M hqn l).mp hq') hl
lemma imprimitive_quat_card {p : ℕ} (hp : p≠0) (n : ℕ) :
    ((quatShell (p*n)).filter (fun w => red p w=0)).card =
      if p∣n then (quatShell (n/p)).card else 0 := by
  classical
  split_ifs with h
  · symm
    apply card_nbij (fun u => (p:ℤ) • u)
    · intro u hu
      apply mem_filter.mpr ⟨mem_quatShell.mpr ?_,by rw [red_smul]; simp⟩
      rw [norm_smul,mem_quatShell.mp hu,pow_two,mul_assoc,←Nat.cast_mul, Nat.mul_div_cancel' h]
      simp
    · intro u _ v _ huv
      exact scalar_cancel p (by exact_mod_cast hp) huv
    · intro w hw
      obtain ⟨hn,hred⟩ := mem_filter.mp hw
      obtain ⟨u,rfl⟩ := (div_iff p w).mp hred
      refine ⟨u, mem_quatShell.mpr ?_,rfl⟩
      have hh := mem_quatShell.mp hn
      rw [norm_smul,Nat.cast_mul,←Nat.mul_div_cancel' h] at hh
      simp only [Nat.cast_mul] at hh
      apply mul_left_cancel₀ (pow_ne_zero 2 (by exact_mod_cast hp : (p:ℤ)≠0))
      simpa [pow_two,mul_assoc] using hh
  · apply card_eq_zero.mpr
    apply eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨hn,hred⟩ := mem_filter.mp hw
    obtain ⟨u,rfl⟩ := (div_iff p w).mp hred
    have hh := mem_quatShell.mp hn
    rw [norm_smul,pow_two,mul_assoc,Nat.cast_mul] at hh
    have e := mul_left_cancel₀ (by exact_mod_cast hp : (p:ℤ)≠0) hh
    exact h (by exact_mod_cast (show (p:ℤ)∣(n:ℤ) from ⟨_, e.symm⟩))
theorem quatShell_odd_recurrence {p : ℕ} [Fact p.Prime] (hp : p≠2) (n : ℕ) :
    (p+1)*(quatShell n).card = (quatShell (p*n)).card +
      (if p∣n then p*(quatShell (n/p)).card else 0) := by
  classical
  have h := count_left_factors (quatShell p) id (Fact.out:p.Prime).ne_zero (fun q hq => mem_quatShell.mp hq) n
  change _ = ∑ w ∈ quatShell (p*n), ((quatShell p).filter (fun q => ∃ u : QInt, w=q*u)).card at h
  rw [sum_congr rfl (odd_factors_card hp n),quatShell_prime_card hp] at h
  have split (w : QInt) : (if red p w=0 then 8*(p+1) else 8) = 8 + (if red p w=0 then 8*p else 0) := by
    split_ifs <;> omega
  simp_rw [split] at h
  rw [sum_add_distrib,←sum_filter,sum_const,sum_const,imprimitive_quat_card (Fact.out:p.Prime).ne_zero] at h
  simp only [nsmul_eq_mul] at h
  split_ifs at h ⊢ <;> nlinarith
end
end TunnellQuaternion
end


/- TunnellJacobiTwo -/
section
namespace TunnellQuaternion
open Finset Quaternion
def dyadic (i : Fin 3) : QInt := ![⟨1,1,0,0⟩,⟨1,0,1,0⟩,⟨1,0,0,1⟩] i
lemma norm_dyadic (i : Fin 3) : normSq (dyadic i)=2 := by fin_cases i <;> decide
lemma dyadic_dvd_iff (i : Fin 3) (w : QInt) :
    (∃ u : QInt, w=dyadic i*u) ↔ red 2 (star (dyadic i)*w)=0 := by
  rw [div_iff]
  constructor
  · rintro ⟨u,rfl⟩
    exact ⟨u,by rw [←mul_assoc,star_mul_self,norm_dyadic,coe_mul_eq_smul]; rfl⟩
  · rintro ⟨u,hu⟩
    refine ⟨u,scalar_cancel 2 (by decide) ?_⟩
    have hh := congrArg (dyadic i * ·) hu
    simpa only [←mul_assoc,self_mul_star,norm_dyadic,coe_mul_eq_smul,Algebra.mul_smul_comm, Nat.cast_ofNat] using hh
def reduceFour (w : Quaternion (ZMod 4)) : Quaternion (ZMod 2) :=
  let f := ZMod.castHom (by decide : 2∣4) (ZMod 2)
  ⟨f w.re,f w.imI,f w.imJ,f w.imK⟩
lemma reduceFour_red (w : QInt) : reduceFour (red 4 w)=red 2 w := by
  change reduceFour (redFun 4 w)=redFun 2 w
  apply QuaternionAlgebra.ext <;> simp [reduceFour,redFun]
instance finiteQuatDecEq {n : ℕ} : DecidableEq (Quaternion (ZMod n)) :=
  (Quaternion.equivProd _).decidableEq
def dyadicCount (w : Quaternion (ZMod 4)) : ℕ :=
  (univ.filter (fun i : Fin 3 => red 2 (star (dyadic i))*reduceFour w=0)).card
lemma dyadic_table (w : Quaternion (ZMod 4)) :
    (normSq w=0 → dyadicCount w=3) ∧ (normSq w=2 → dyadicCount w=1) := by
  obtain ⟨a,b,c,d⟩ := w
  revert a b c d
  decide
open scoped Classical in
theorem quatShell_two_recurrence (n : ℕ) :
    (quatShell (2*n)).card = if Even n then (quatShell n).card else 3*(quatShell n).card := by
  classical
  have h := count_left_factors (univ : Finset (Fin 3)) dyadic (d:=2) (by decide)
    (fun i _ => norm_dyadic i) n
  simp only [card_univ,Fintype.card_fin] at h
  have hf (w : QInt) (hw : w∈quatShell (2*n)) :
      (univ.filter (fun i : Fin 3 => ∃ u : QInt, w=dyadic i*u)).card = if Even n then 3 else 1 := by
    have hq := dyadic_table (red 4 w)
    rw [←red_norm,mem_quatShell.mp hw] at hq
    have heq : (univ.filter (fun i : Fin 3 => ∃ u : QInt, w=dyadic i*u)).card = dyadicCount (red 4 w) := by
      unfold dyadicCount
      congr 1
      apply filter_congr
      intro i _
      rw [dyadic_dvd_iff,map_mul,reduceFour_red]
    rw [heq]
    split_ifs with he
    · apply hq.1
      rcases he with ⟨t,ht⟩
      rw [ht]
      push_cast
      have hz : (4:ZMod 4)=0 := by decide
      linear_combination (t:ZMod 4)*hz
    · apply hq.2
      obtain ⟨t,ht⟩ := Nat.not_even_iff_odd.mp he
      rw [ht]
      push_cast
      have hz : (4:ZMod 4)=0 := by decide
      linear_combination (t:ZMod 4)*hz
  rw [sum_congr rfl hf,sum_const] at h
  split_ifs at h ⊢ <;> simp_all <;> omega
end TunnellQuaternion
end


/- TunnellJacobiFourSquares -/
section
namespace TunnellQuaternion
open Finset Quaternion
open scoped Pointwise
def divisorWeight (d : ℕ) : ℕ := if 4∣d then 0 else d
def fourDivSum (n : ℕ) : ℕ := ∑ d ∈ n.divisors, divisorWeight d
lemma divisorWeight_mul {a b : ℕ} (h : a.Coprime b) :
    divisorWeight (a*b) = divisorWeight a*divisorWeight b := by
  have hodd : ¬(2∣a ∧ 2∣b) := by
    rintro ⟨ha,hb⟩
    have hc := Nat.dvd_gcd ha hb
    rw [h.gcd_eq_one] at hc
    omega
  have hd : 4∣a*b ↔ 4∣a ∨ 4∣b := by
    simp only [Nat.dvd_iff_mod_eq_zero] at hodd ⊢
    rw [Nat.mul_mod]
    have ha := Nat.mod_lt a (by decide : 0<4)
    have hb := Nat.mod_lt b (by decide : 0<4)
    interval_cases ha' : a%4 <;> interval_cases hb' : b%4 <;> omega
  unfold divisorWeight
  simp only [hd]
  split_ifs <;> simp_all
lemma fourDivSum_mul {a b : ℕ} (h : a.Coprime b) :
    fourDivSum (a*b) = fourDivSum a * fourDivSum b := by
  unfold fourDivSum
  rw [Nat.divisors_mul,Finset.mul_def,Finset.sum_image h.mul_injOn_divisors]
  calc
    _ = ∑ v ∈ a.divisors ×ˢ b.divisors, divisorWeight v.1 * divisorWeight v.2 := by
      apply sum_congr rfl
      intro v hv
      obtain ⟨hm,hn⟩ := mem_product.mp hv
      exact divisorWeight_mul ((h.coprime_dvd_left (Nat.mem_divisors.mp hm).1).coprime_dvd_right (Nat.mem_divisors.mp hn).1)
    _ = _ := by rw [sum_product]; simp only [←mul_sum,←sum_mul]
lemma oddDivSum_pow {p : ℕ} (h : p.Prime) (hp : p≠2) (r : ℕ) :
    fourDivSum (p^r) = ∑ i ∈ range (r+1), p^i := by
  rw [fourDivSum,Nat.sum_divisors_prime_pow h]
  apply sum_congr rfl
  intro i _
  apply if_neg
  intro hd
  have he := dvd_trans (by decide : 2∣4) hd
  exact (Nat.not_even_iff_odd.mpr ((h.odd_of_ne_two hp).pow (n:=i))) (even_iff_two_dvd.mpr he)
lemma evenDivSum_pow {r : ℕ} (hr : 0<r) : fourDivSum (2^r)=3 := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  rw [fourDivSum,Nat.sum_divisors_prime_pow Nat.prime_two]
  clear hr
  induction r with
  | zero => decide
  | succ r ih =>
    rw [sum_range_succ,ih]
    have hd : 4∣2^(r+2) := by rw [pow_add]; exact dvd_mul_left _ _
    simp [divisorWeight,hd]
lemma quatShell_odd_pow_mul {p : ℕ} (h : p.Prime) (hp : p≠2) (m : ℕ) (hm : ¬p∣m) (r : ℕ) :
    (quatShell (p^r*m)).card = (∑ i ∈ range (r+1),p^i) * (quatShell m).card := by
  let : Fact p.Prime := ⟨h⟩
  induction r using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have hh := quatShell_odd_recurrence hp m
    simpa [sum_range_succ,hm,Nat.add_comm] using hh.symm
  | more r hr hr' =>
    have hd : p∣p^(r+1)*m := by rw [pow_succ]; exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
    have hdiv : p^(r+1)*m/p=p^r*m := by
      rw [pow_succ',mul_assoc,Nat.mul_div_cancel_left _ h.pos]
    have hh := quatShell_odd_recurrence hp (p^(r+1)*m)
    rw [if_pos hd,hdiv,hr,hr'] at hh
    have he : p*(p^(r+1)*m)=p^(r+2)*m := by rw [pow_succ' p (r+1),mul_assoc]
    rw [he] at hh
    simp only [sum_range_succ, pow_succ] at hh ⊢
    nlinarith
lemma quatShell_two_pow_mul (m : ℕ) (hm : ¬2∣m) {r : ℕ} (hr : 0<r) :
    (quatShell (2^r*m)).card = 3*(quatShell m).card := by
  obtain ⟨r,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
  clear hr
  induction r with
  | zero => simpa [even_iff_two_dvd,hm] using quatShell_two_recurrence m
  | succ r ih =>
    have he : Even (2^(r+1)*m) := even_two.pow_of_ne_zero (by omega) |>.mul_right _
    rw [pow_succ' 2 (r+1),mul_assoc,quatShell_two_recurrence,if_pos he,ih]
theorem quatShell_card_divisors {n : ℕ} (hn : n≠0) :
    (quatShell n).card = 8 * ∑ d ∈ n.divisors with ¬4∣d, d := by
  suffices h : ∀ m : ℕ, m≠0 → (quatShell m).card = 8*fourDivSum m by
    rw [h n hn,fourDivSum,sum_filter]
    simp [divisorWeight]
  apply Nat.recOnPrimePow
  · simp
  · intro _
    simpa [fourDivSum,divisorWeight] using quatShell_one_card
  · intro m p r h hm hr ih hne
    have hm0 : m≠0 := by rintro rfl; simp at hm
    rw [fourDivSum_mul ((h.coprime_iff_not_dvd.mpr hm).pow_left r)]
    by_cases hp : p=2
    · subst p
      rw [quatShell_two_pow_mul m hm hr,evenDivSum_pow hr,ih hm0]
      ring
    · rw [quatShell_odd_pow_mul h hp m hm r,oddDivSum_pow h hp r,ih hm0]
      ring
end TunnellQuaternion
end


/- TunnellQuaternionToricSum -/
section
namespace TunnellToricSign
open TunnellHurwitzFour TunnellHurwitz TunnellToric TunnellShell TunnellToricClass TunnellToricLocal
open scoped Classical
 
def LocalGenerator (v w : Triple) (q : H ℤ) : Prop :=
  Odd (nr q) ∧ TunnellHurwitz.pure w*hamZ q=hamZ q*TunnellHurwitz.pure v
lemma local_generator_exists {n : ℕ} (hn : n%4=2) {v w : Triple} (hv : v∈shell n) (hw : w∈shell n) :
    ∃ q, LocalGenerator v w q := by
  obtain ⟨t,ht,N,hN,hodd⟩ := odd_intertwiner hn v w hv hw
  obtain ⟨q,hq⟩ := ht.1
  have h := ht.2
  rw [←hq,norm_ham] at hN
  rw [←hq] at h
  have hN' : nr q=(N:ℤ) := by exact_mod_cast hN
  exact ⟨q,by rw [LocalGenerator,hN']; exact ⟨by exact_mod_cast hodd,h⟩⟩
lemma sign_rep {n : ℕ} {w : Triple} (hw : w∈representatives n) :
    color (redVec w)=test w := by
  obtain ⟨ha,hb,_,_,_⟩ := (Finset.mem_filter.mp hw).2
  have hA := ZMod.val_intCast (n:=8) w.1
  have hB := ZMod.val_intCast (n:=8) w.2.1
  have hC := ZMod.val_intCast (n:=8) w.2.2
  have hx := Int.odd_iff.mp ha
  have hy := Int.odd_iff.mp hb
  have hx' : (w.1:Z8).val%2≠0 := by omega
  have hy' : (w.2.1:Z8).val%2≠0 := by omega
  have h0 : (w.2.2:Z8)=0 ↔ w.2.2%8=0 := by rw [←(ZMod.val_injective 8).eq_iff]; change _=0 ↔ _; omega
  have h4 : (w.2.2:Z8)=4 ↔ w.2.2%8=4 := by rw [←(ZMod.val_injective 8).eq_iff]; change _=4 ↔ _; omega
  simp only [color,redVec,hx',hy',if_false,h0,h4,test]
lemma aligned_base {n : ℕ} (hn : n%8=2) {t : Triple} (ht : t∈shell n) :
    ∃ v∈shell n, Odd v.1 ∧ v.2.1%4=v.1%4 ∧ 4∣v.2.2 := by
  obtain ⟨w,hw,_⟩ := rep_exists (show n%4=2 by omega) ht
  obtain ⟨hh,hR⟩ := Finset.mem_filter.mp hw
  obtain ⟨ha,hb,hc,_,_⟩ := hR
  have chk : ∀ x y z : Z8, x.val%2=1 → y.val%2=1 → x^2+y^2+z^2=2 → z.val%4=0 := by decide
  have he := congrArg (fun z:ℤ => (z:Z8)) (mem_shell.mp hh)
  simp only [TunnellShell.normSq,Int.cast_add,Int.cast_pow,Int.cast_natCast] at he
  have hnt : (n:Z8)=2 := by apply ZMod.val_injective; rw [ZMod.val_natCast,hn]; decide
  rw [hnt] at he
  have hx := Int.odd_iff.mp ha
  have hy := Int.odd_iff.mp hb
  have hA := ZMod.val_intCast (n:=8) w.1
  have hB := ZMod.val_intCast (n:=8) w.2.1
  have hC := ZMod.val_intCast (n:=8) w.2.2
  have hz := chk _ _ _ (by omega) (by omega) he
  have hfour : 4∣w.2.2 := by omega
  by_cases h : w.2.1%4=w.1%4
  · exact ⟨w,hh,ha,h,hfour⟩
  · refine ⟨move 0 1 w,move_shell 0 1 hh,?_⟩
    change Odd w.1 ∧ (-w.2.1)%4=w.1%4 ∧ 4∣-w.2.2
    exact ⟨ha,by omega,dvd_neg.mpr hfour⟩
lemma aligned_sign {v : Triple} (hx : Odd v.1) (hy : v.2.1%4=v.1%4) (hz : 4∣v.2.2) :
    color (redVec v)^2=1 := by
  have chk : ∀ x y z:Z8, x.val%2=1 → x.val%4=y.val%4 → z.val%4=0 → color (x,y,z)^2=1 := by decide
  have ha := ZMod.val_intCast (n:=8) v.1
  have hb := ZMod.val_intCast (n:=8) v.2.1
  have hc := ZMod.val_intCast (n:=8) v.2.2
  have e := Int.odd_iff.mp hx
  exact chk _ _ _ (by omega) (by omega) (by omega)
end TunnellToricSign
end


/- TunnellRamifiedTwoTable -/
section
namespace TunnellRamifiedTwoTable
open TunnellHurwitzFour TunnellToricSign
open scoped Classical
abbrev Z8 := ZMod 8
def V {R : Type*} [CommRing R] (x y z : R) : H R := (-z,x-z,y-z,2*z)
def proj {R : Type*} [CommRing R] (v : H R) (q : H R) : H R := 2 • q+prod (prod v q) v
def four (x : Z8) : Z4 := (x.val:Z4)
def coeff (x : Z8) (k l : ZMod 2) : Z8 := if k=l then 6 else 2
lemma linear_proj {R : Type*} [CommRing R] (s : H R) (a b c d : R) :
    proj s (a,b,c,d)=a • proj s (1,0,0,0)+b • proj s (0,1,0,0)+c • proj s (0,0,1,0)+d • proj s (0,0,0,1) := by
  rcases s with ⟨s,t,u,v⟩
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  all_goals dsimp [proj,prod]; simp only [two_nsmul,smul_eq_mul]; ring
set_option maxRecDepth 10000 in
set_option maxHeartbeats 3000000 in
lemma basis_table : ∀ x : Z8, x.val%2=1 → ∀ k l : ZMod 2,
    let A := proj (V x (x+4*(k.val:Z8)) (4*(l.val:Z8)))
    A (1,0,0,0)=0 ∧ A (0,1,0,0)=(0,2,6,0) ∧ A (0,0,1,0)=(0,6,2,0) ∧
    A (0,0,0,1)=(6,coeff x k l,coeff x k l,4) := by decide
set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma scalar_table : ∀ (b c d : Z8) (k : ZMod 2),
    ((6*d,2*b+6*c+(if k=0 then 6 else 2)*d,6*b+2*c+(if k=0 then 6 else 2)*d,4*d):H Z8)=0 ↔
    four b=four c ∧ four d=0 := by decide
theorem kernel (q : H Z8) (x : Z8) (hx : x.val%2=1) (k l : ZMod 2) :
    proj (V x (x+4*(k.val:Z8)) (4*(l.val:Z8))) q=0 ↔ four q.2.1=four q.2.2.1 ∧ four q.2.2.2=0 := by
  rcases q with ⟨a,b,c,d⟩
  obtain ⟨h₀,h₁,h₂,h₃⟩ := basis_table x hx k l
  rw [linear_proj,h₀,h₁,h₂,h₃]
  let e : ZMod 2 := if k=l then 0 else 1
  have h : coeff x k l=(if e=0 then 6 else 2) := by by_cases r : k=l <;> simp [e,coeff,r]
  rw [h]
  have he := scalar_table b c d e
  convert he using 2 <;> simp [smul_eq_mul] <;> ring <;> decide
end TunnellRamifiedTwoTable
end


/- TunnellRamifiedTwoOrder -/
section
namespace TunnellRamifiedTwoOrder
open TunnellToricSign TunnellHurwitzFour TunnellHurwitz TunnellShell TunnellToricClass TunnellTwoProjection
open TunnellRamifiedTwoTable
noncomputable section
lemma ham_injective : Function.Injective hamZ := by
  rintro ⟨a,b,c,d⟩ ⟨e,f,g,h⟩ eq
  have h₁ := congrArg QuaternionAlgebra.re eq
  have h₂ := congrArg QuaternionAlgebra.imI eq
  have h₃ := congrArg QuaternionAlgebra.imJ eq
  have h₄ := congrArg QuaternionAlgebra.imK eq
  dsimp [hamZ,ham] at h₁ h₂ h₃ h₄
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> dsimp only
  · exact_mod_cast (show (a:ℚ)=e by linarith)
  · exact_mod_cast (show (b:ℚ)=f by linarith)
  · exact_mod_cast (show (c:ℚ)=g by linarith)
  · exact_mod_cast (show (d:ℚ)=h by linarith)
lemma ham_smul (m : ℕ) (q : H ℤ) : hamZ (m • q)=(m:Q)*hamZ q := by
  induction m with
  | zero => rw [zero_smul,Nat.cast_zero,zero_mul]; ext <;> simp [hamZ,ham] <;> rfl
  | succ m ih => rw [succ_nsmul,hamZ_add,ih,Nat.cast_succ,add_mul,one_mul]
lemma eight_divisible (q : H ℤ) : (∃ b∈O, hamZ q=8*b) ↔ redH q=0 := by
  constructor
  · rintro ⟨_,⟨b,rfl⟩,e⟩
    have he : q=8 • b := ham_injective (e.trans (ham_smul 8 b).symm)
    rw [he]; rcases b with ⟨a,b,c,d⟩; simp [redH,nsmul_eq_mul,show (8:TunnellToricSign.Z8)=0 by decide]
  · rcases q with ⟨a,b,c,d⟩
    intro h
    change ((a:TunnellToricSign.Z8),(b:TunnellToricSign.Z8),(c:TunnellToricSign.Z8),(d:TunnellToricSign.Z8))=(0,0,0,0) at h
    simp only [Prod.mk.injEq,ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    obtain ⟨a',ha⟩ := h.1
    obtain ⟨b',hb⟩ := h.2.1
    obtain ⟨c',hc⟩ := h.2.2.1
    obtain ⟨d',hd⟩ := h.2.2.2
    let s : H ℤ := (a',b',c',d')
    refine ⟨hamZ s,⟨s,rfl⟩,?_⟩
    rw [←show ((8:ℕ):Q)*hamZ s=8*hamZ s by rfl,←ham_smul]
    congr 1
    exact Prod.ext (by simpa [s,nsmul_eq_mul] using ha) (Prod.ext (by simpa [s,nsmul_eq_mul] using hb)
      (Prod.ext (by simpa [s,nsmul_eq_mul] using hc) (by simpa [s,nsmul_eq_mul] using hd)))
lemma ham_V (v : Triple) : hamZ (V v.1 v.2.1 v.2.2)=TunnellHurwitz.pure v := by
  ext <;> dsimp [hamZ,ham,V,TunnellHurwitz.pure] <;> push_cast <;> ring
lemma red_proj (d : ℕ) (hd : d%4=1) (v : Triple) (q : H ℤ) :
    (∃ b∈O, filt d v v (hamZ q)=8*b) ↔
      proj (V (v.1:TunnellToricSign.Z8) (v.2.1:TunnellToricSign.Z8) (v.2.2:TunnellToricSign.Z8)) (redH q)=0 := by
  let s := V v.1 v.2.1 v.2.2
  have hq : filt d v v (hamZ q)=hamZ ((2*d) • q+prod (prod s q) s) := by
    rw [hamZ_add,hamZ_mul,hamZ_mul,ham_smul,show hamZ s=_ from ham_V v]; push_cast; rfl
  rw [hq,eight_divisible]
  have h₂ : ((2*d:ℕ):TunnellToricSign.Z8)=2 := by apply ZMod.val_injective 8; rw [ZMod.val_natCast]; change (2*d)%8=2; omega
  rcases v with ⟨a,b,c⟩; rcases q with ⟨x,y,z,t⟩
  have eq : redH ((2*d) • (x,y,z,t)+prod (prod s (x,y,z,t)) s)=proj (V (a:TunnellToricSign.Z8) b c) (redH (x,y,z,t)) := by
    have red_prod (u t : H ℤ) : redH (prod u t)=prod (redH u) (redH t) := by
      rcases u with ⟨i,j,k,l⟩; rcases t with ⟨i',j',k',l'⟩; simp [redH,prod]
    have red_add (u t : H ℤ) : redH (u+t)=redH u+redH t := by rcases u with ⟨i,j,k,l⟩; rcases t with ⟨i',j',k',l'⟩; simp [redH]
    have red_scale (m : ℕ) (t : H ℤ) : redH (m • t)=((m:TunnellToricSign.Z8) • redH t) := by
      rcases t with ⟨w,x,y,z⟩; simp [redH,nsmul_eq_mul,smul_eq_mul]
    rw [red_add,red_scale,h₂,red_prod,red_prod]
    have hs : redH s=V (a:TunnellToricSign.Z8) b c := by simp [redH,s,V]
    rw [hs,proj]
    congr 1
    simp [two_nsmul,two_smul]
  rw [eq]
lemma four_int (a : ℤ) : four (a:TunnellToricSign.Z8)=(a:Z4) := by
  apply ZMod.val_injective 4
  simp [four,ZMod.val_natCast,ZMod.val_intCast]
theorem order_criterion {d : ℕ} (hd : d%4=1) {v : Triple} (hv : v∈shell (2*d))
    (hx : Odd v.1) (hy : v.2.1%4=v.1%4) (hz : 4∣v.2.2) (q : H ℤ) :
    admits d v v (hamZ q) ↔ (modFour q).2.1=(modFour q).2.2.1 ∧ (modFour q).2.2.2=0 := by
  rw [admits_iff hv hv (by omega) (show hamZ q∈O from ⟨q,rfl⟩),red_proj d hd]
  obtain ⟨x,y,z⟩ := v
  change y%4=x%4 at hy
  change (4:ℤ)∣z at hz
  obtain ⟨l,rfl⟩ := hz
  obtain ⟨k,rfl⟩ : ∃k:ℤ,y=x+4*k := ⟨(y-x)/4,by omega⟩
  have hx' : (x:TunnellToricSign.Z8).val%2=1 := by
    have h := ZMod.val_intCast (n:=8) x
    have h' := Int.odd_iff.mp hx; dsimp only at h'; omega
  dsimp only
  push_cast
  rw [red4 k,red4 l,kernel _ _ hx']
  exact and_congr ((congrArg₂ Eq (four_int _) (four_int _)).to_iff) ((congrArg (·=0) (four_int _)).to_iff)
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem unit_criterion {d : ℕ} (hd : d%4=1) {v : Triple} (hv : v∈shell (2*d))
    (hx : Odd v.1) (hy : v.2.1%4=v.1%4) (hz : 4∣v.2.2) {q : H ℤ} (hq : Odd (nr q)) :
    admits d v v (hamZ q) ↔ modFour q∈orderUnits := by
  rw [order_criterion hd hv hx hy hz]
  exact (show ∀ t∈units,t.2.1=t.2.2.1 ∧ t.2.2.2=0 ↔ t∈orderUnits by decide) (modFour q) (odd_units q hq)
end
end TunnellRamifiedTwoOrder
end


/- TunnellTwoProjectionTransport -/
section
namespace TunnellTwoProjectionTransport
open TunnellHurwitz TunnellToricClass TunnellShell TunnellToricLocal TunnellTwoProjection
open TunnellToric TunnellHurwitzFour TunnellToricSign TunnellRamifiedTwoOrder
noncomputable section
def eight (q : Q) := ∃ b∈O, q=8*b
lemma eight_transport {q a b : Q} (h : eight q) (ha : a∈O) (hb : b∈O) : eight (a*q*b) := by
  obtain ⟨y,hy,rfl⟩ := h
  exact ⟨a*y*b,order.mul_mem (order.mul_mem ha hy) hb,by noncomm_ring⟩
lemma eight_cancel {q : Q} (hq : q∈O) (M : ℕ) (hM : Odd M) (h : eight ((M:Q)*q)) : eight q := by
  obtain ⟨u,v,he⟩ := (show Nat.Coprime M 8 from (Nat.coprime_two_right.mpr hM).pow_right 3).isCoprime
  obtain ⟨b,hb,eb⟩ := h
  have eZ : u*(M:ℤ)+v*8=1 := he
  have eQ := congrArg (fun x:ℤ => (x:Q)) eZ
  push_cast at eQ
  have hU : (u:Q)*b∈O := by simpa only [zsmul_eq_mul] using O.smul_mem u hb
  have hV : (v:Q)*q∈O := by simpa only [zsmul_eq_mul] using O.smul_mem v hq
  refine ⟨(u:Q)*b+(v:Q)*q,O.add_mem hU hV,?_⟩
  calc q=(((u:Q)*M+v*8)*q) := by rw [eQ,one_mul]
       _=8*((u:Q)*b+(v:Q)*q) := by rw [add_mul,mul_assoc,eb]; noncomm_ring
lemma filt_transport {d : ℕ} {v s t : Triple} {a b : Q} (ha : a∈J v s) (hb : b∈J v t) (q : Q) :
    filt d v v (star a*q*b)=star a*filt d t s q*b := by
  have ha' := (star_intertwines ha).2
  let N : Q := (2*d:ℕ)
  have hN (z : Q) : N*z=z*N := Nat.cast_comm (2*d) z
  have h₁ : N*(star a*q*b)=star a*(N*q)*b := by rw [←mul_assoc N,←mul_assoc N,hN (star a)]; simp only [mul_assoc]
  have h₂ : ((TunnellHurwitz.pure) v*(star a*q*b))*(TunnellHurwitz.pure) v = star a*((TunnellHurwitz.pure) s*q*(TunnellHurwitz.pure) t)*b := by
    rw [←mul_assoc ((TunnellHurwitz.pure) v),←mul_assoc ((TunnellHurwitz.pure) v),ha',mul_assoc (star a) ((TunnellHurwitz.pure) s),mul_assoc (star a),mul_assoc (star a),mul_assoc ((TunnellHurwitz.pure) s*q),←hb.2]
    simp only [mul_assoc]
  change (2*(d:Q))*(star a*q*b)+_=star a*((2*(d:Q))*q+_)*b
  rw [show (2*(d:Q))=N by dsimp only [N]; push_cast; rfl, mul_add, add_mul,h₁,h₂]
def bar {R : Type*} [CommRing R] (q : H R) : H R := (q.1+q.2.2.2,-q.2.1,-q.2.2.1,-q.2.2.2)
lemma ham_bar (a : H ℤ) : hamZ (bar a)=star (hamZ a) := by
  apply QuaternionAlgebra.ext
  all_goals simp only [Quaternion.re_star,Quaternion.imI_star,Quaternion.imJ_star,Quaternion.imK_star] <;> dsimp [hamZ,bar,ham] <;> push_cast <;> ring
lemma eight_pair_iff {s t : Q} (hs : s∈O) (ht : t∈O) (a b : ℕ) (ha : Odd a) (hb : Odd b)
    (hsa : Quaternion.normSq s=a) (htb : Quaternion.normSq t=b) {x : Q} (hx : x∈O) :
    eight (star s*x*t) ↔ eight x := by
  constructor
  · intro h
    have he := eight_transport h hs (star_order ht)
    have eq : s*(star s*x*t)*star t=((a*b:ℕ):Q)*x := by
      rw [←mul_assoc s,←mul_assoc s,Quaternion.self_mul_star,hsa,mul_assoc,Quaternion.self_mul_star,htb]
      simp only [Quaternion.coe_natCast,Nat.cast_mul,mul_assoc]
      rw [Nat.cast_comm b x]
    exact eight_cancel hx _ (ha.mul hb) (eq ▸ he)
  · intro h; exact eight_transport h (star_order hs) ht
theorem pair_criterion {d : ℕ} (hd : d%4=1) {v s t : Triple} (hv : v∈shell (2*d)) (hs : s∈shell (2*d)) (ht : t∈shell (2*d))
    (hx : Odd v.1) (hy : v.2.1%4=v.1%4) (hz : 4∣v.2.2) {a b : H ℤ} (ha : LocalGenerator v s a) (hb : LocalGenerator v t b)
    {q : H ℤ} (hq : Odd (nr q)) :
    admits d t s (hamZ q) ↔ modFour (prod (prod (bar a) q) b)∈orderUnits := by
  let Q' := prod (prod (bar a) q) b
  have he : hamZ Q'=star (hamZ a)*hamZ q*hamZ b := by dsimp [Q']; rw [hamZ_mul,hamZ_mul,ham_bar]
  have hJA : hamZ a∈J v s := ⟨⟨a,rfl⟩,ha.2⟩
  have hJB : hamZ b∈J v t := ⟨⟨b,rfl⟩,hb.2⟩
  have hq' : Odd (nr Q') := by
    have norm_bar : nr (bar a)=nr a := by rcases a with ⟨x,y,z,t⟩; dsimp [nr,bar]; ring
    have nr_prod (x y : H ℤ) : nr (prod x y)=nr x*nr y := by
      have H := congrArg Quaternion.normSq (hamZ_mul x y); rw [map_mul,norm_ham,norm_ham,norm_ham] at H; exact_mod_cast H
    dsimp [Q']; rw [nr_prod,nr_prod,norm_bar]; exact (ha.1.mul hq).mul hb.1
  rw [←unit_criterion hd hv hx hy hz hq',admits_iff ht hs (by omega) (show hamZ q∈O from ⟨q,rfl⟩),
    admits_iff hv hv (by omega) (show hamZ Q'∈O from ⟨Q',rfl⟩),he,filt_transport hJA hJB]
  obtain ⟨M,hM⟩ := norm_int hJA.1; obtain ⟨N,hN⟩ := norm_int hJB.1
  have hMa : nr a=(M:ℤ) := by rw [norm_ham] at hM; exact_mod_cast hM
  have hNb : nr b=(N:ℤ) := by rw [norm_ham] at hN; exact_mod_cast hN
  have hMo := ha.1; rw [hMa] at hMo
  have hNo := hb.1; rw [hNb] at hNo
  apply (eight_pair_iff hJA.1 hJB.1 M N (by exact_mod_cast hMo) (by exact_mod_cast hNo) hM hN _).symm
  apply order.add_mem
  · have hqO : hamZ q∈O := ⟨q,rfl⟩
    change (2*(d:Q))*hamZ q∈O
    simpa only [zsmul_eq_mul,Int.natCast_mul,Int.cast_mul,Int.cast_natCast,Nat.cast_mul,Nat.cast_ofNat,Int.cast_ofNat] using O.smul_mem ((2*d:ℕ):ℤ) hqO
  · exact order.mul_mem (order.mul_mem (pure_mem s) ⟨q,rfl⟩) (pure_mem t)
end
end TunnellTwoProjectionTransport
end


/- TunnellJoinedGeometric -/
section
namespace TunnellTriangular
open Polynomial Finset TunnellQBin
open LaurentPolynomial hiding C
open TunnellCubicFinite
variable {R : Type*} [CommRing R]
def plusFac (u : R) (n : ℕ) := ∏ j ∈ range n, (1+u^(j+1))
lemma odd_product (n : ℕ) :
    T ((n+1).choose 2:ℤ) * ∏ j ∈ range (2*n+1), (1+q^j*T (-(n:ℤ))) =
    2*(plusFac q n)^2 := by
  have he (j : ℕ) : 1+q^j*T (-(n:ℤ)) = 1+T ((j:ℤ)-n) := by
    simp only [q,T_pow,mul_one,←T_add,sub_eq_add_neg]
  have hs : (∏ j ∈ range (2*n+1), (1+(T ((j:ℤ)-n):L))) =
       (∏ j ∈ range n, (1+T (-(j+1:ℕ):ℤ))) * 2 * plusFac q n := by
    let f (j : ℕ) : L := 1+T ((j:ℤ)-n)
    change (∏ j ∈ range (2*n+1), f j) = _
    rw [show 2*n+1 = n+1+n by omega,prod_range_add,prod_range_succ,←prod_range_reflect f n]
    have hleft : (∏ x ∈ range n, f (n-1-x)) = ∏ j ∈ range n, (1+T (-(j+1:ℕ):ℤ)) := by
      apply prod_congr rfl
      intro i hi
      have := mem_range.mp hi
      dsimp [f]
      congr 2
      omega
    have hright : (∏ j ∈ range n, f (n+1+j)) = plusFac q n := by
      apply prod_congr rfl
      intro i hi
      simp only [f,q,T_pow,mul_one]
      congr 2
      omega
    rw [hleft,hright,show f n = 2 by simp [f]; ring]
  have hmul (N : ℕ) : T ((N+1).choose 2 : ℤ) *
        (∏ j ∈ range N, (1+(T (-(j+1:ℕ):ℤ):L))) = plusFac q N := by
    induction N with
    | zero => simp [plusFac]
    | succ N ih =>
      have hc : ((N+1+1).choose 2:ℤ) = ((N+1).choose 2:ℤ)+(N+1:ℕ) := by
        rw [Nat.choose_succ_succ,Nat.choose_one_right]
        push_cast; ring
      rw [hc,T_add,prod_range_succ,mul_mul_mul_comm,ih,show plusFac q (N+1) = plusFac q N * (1+q^(N+1)) by exact prod_range_succ ..]
      congr 1
      simp only [mul_add,mul_one,←T_add,add_neg_cancel,T_zero,q,T_pow]
      ring
  simp_rw [he]
  rw [hs]
  linear_combination 2*plusFac q n*hmul n
lemma triangular_laurent (n : ℕ) : plusFac q n ^ 2 =
    ∑ k ∈ range (n+1), q^((k+1).choose 2)*TunnellQBin.choose q (2*n+1) (n+1+k) := by
  let f (r : ℕ) : L := T ((n+1).choose 2:ℤ) *
      ((q^(r.choose 2)*TunnellQBin.choose q (2*n+1) r)*(T (-(n:ℤ)))^r)
  have hclean (r : ℕ) : f r = T (((n+1).choose 2:ℤ)+(r.choose 2:ℤ)-(n:ℤ)*r) *
      TunnellQBin.choose q (2*n+1) r := by
    simp only [f,q,T_pow,mul_one,sub_eq_add_neg,T_add]
    ring_nf
  have hpair (k : ℕ) (hk : k≤n) : f (n-k)+f (n+1+k) =
      2*(q^((k+1).choose 2)*TunnellQBin.choose q (2*n+1) (n+1+k)) := by
    have hc := choose_symm (2*n+1) (n-k) (by omega)
    rw [show 2*n+1-(n-k)=n+1+k by omega] at hc
    have hsub : ((n-k:ℕ):ℤ) = (n:ℤ)-k := Nat.cast_sub hk
    have hL : ((n+1).choose 2:ℤ) + ((n-k).choose 2:ℤ) - n*(n-k:ℕ) = ((k+1).choose 2:ℤ) := by
      have a := double_choose (n+1)
      have b := double_choose (n-k)
      have c := double_choose (k+1)
      rw [hsub] at b ⊢
      push_cast at a c
      nlinarith
    have hR : ((n+1).choose 2:ℤ) + ((n+1+k).choose 2:ℤ) - n*(n+1+k:ℕ) = ((k+1).choose 2:ℤ) := by
      have a := double_choose (n+1)
      have b := double_choose (n+1+k)
      have c := double_choose (k+1)
      push_cast at a b c ⊢
      nlinarith
    rw [hclean,hclean,hL,hR,hc]
    simp only [q,T_pow,mul_one]
    ring
  have ht : (2:L) ≠ 0 := fun e => (show (2:ℤ[X]) ≠ 0 by norm_num) (Polynomial.toLaurent_injective (by simpa only [map_ofNat,map_zero] using e))
  apply mul_left_cancel₀ ht
  rw [←odd_product n,expansion_eval,mul_sum,mul_sum]
  change (∑ r ∈ range (2*n+1+1), f r) = _
  rw [show 2*n+1+1=(n+1)+(n+1) by omega,sum_range_add,←sum_range_reflect f (n+1),←sum_add_distrib]
  apply sum_congr rfl
  intro k hk
  simpa only [Nat.add_sub_cancel] using hpair k (by have := mem_range.mp hk; omega)
theorem triangular (u : R) (n : ℕ) : plusFac u n ^ 2 =
    ∑ k ∈ range (n+1), u^((k+1).choose 2)*TunnellQBin.choose u (2*n+1) (n+1+k) := by
  have hp : plusFac (X:ℤ[X]) n ^ 2 =
      ∑ k ∈ range (n+1), X^((k+1).choose 2)*TunnellQBin.choose (X:ℤ[X]) (2*n+1) (n+1+k) := by
    apply Polynomial.toLaurent_injective
    simpa only [plusFac,map_pow,map_prod,map_add,map_one,map_sum,map_mul,map_choose,toLaurent_X]
      using triangular_laurent n
  let g := Polynomial.eval₂RingHom (Int.castRingHom R) u
  have hx : g X = u := by simp [g]
  simpa only [plusFac,map_pow,map_prod,map_add,map_one,map_sum,map_mul,map_choose,hx] using congrArg g hp
end TunnellTriangular
namespace TunnellQuaternionTheta
open Finset TunnellQBin TunnellTruncated TunnellTriangular
variable {R : Type*} [CommRing R]
lemma nil_pow {u : R} {d : ℕ} (hu : u^(d+1) = 0) {k : ℕ} (hk : k ≠ 0) :
    (u^k)^(d+1)=0 := by rw [←pow_mul,mul_comm,pow_mul,hu,zero_pow hk]
lemma plus_times_fac (u : R) (d : ℕ) : plusFac u d * fac u d = fac (u^2) d := by
  rw [plusFac,fac,fac,←prod_mul_distrib]
  apply prod_congr rfl
  intro i _
  rw [←pow_mul, mul_comm, pow_mul]
  ring
lemma triangular_sum {u : R} {d : ℕ} (hu : u^(d+1)=0) :
    (∑ k ∈ range (d+1), u^((k+1).choose 2)) * fac u d = fac (u^2) d ^ 2 := by
  let N := 2*d
  have hN : d ≤ N := by dsimp [N]; omega
  have hp : plusFac u N = plusFac u d := by
    apply (fac_unit u ⟨_,hu⟩ d).mul_left_injective
    change plusFac u N * fac u d = plusFac u d * fac u d
    calc plusFac u N * fac u d = plusFac u N * fac u N := by rw [fac_stable u hu hN]
         _ = _ := by rw [plus_times_fac,plus_times_fac,fac_stable (u^2) (nil_pow hu (by decide)) hN]
  have h := triangular u N
  rw [hp] at h
  have hs := congrArg (· * fac u d) h
  rw [sum_mul] at hs
  have hr (k : ℕ) (hk : k ≤ d) :
      u^((k+1).choose 2)*choose u (2*N+1) (N+1+k)*fac u d = u^((k+1).choose 2) := by
    rw [mul_assoc,choose_stable u hu _ _ (by dsimp [N]; omega) (by dsimp [N]; omega)
      (by dsimp [N]; omega),mul_one]
  have htail (k : ℕ) (hk : k ∉ range (d+1)) : u^((k+1).choose 2) = 0 := by
    have := triangle_ge k
    rw [mem_range] at hk
    exact pow_eq_zero_of_le (by omega) hu
  have ht : (∑ k ∈ range (N+1), u^((k+1).choose 2)*choose u (2*N+1) (N+1+k)*fac u d)
      = ∑ k ∈ range (d+1), u^((k+1).choose 2) := by
    rw [sum_subset (s₁:=range (d+1)) (s₂:=range (N+1)) (range_mono (by omega))
      (fun k _ hk => htail k hk)]
    apply sum_congr rfl
    intro k hk
    by_cases hk' : k ≤ d
    · exact hr k hk'
    · rw [htail k (by simpa using hk')]; ring
  rw [←ht,←hs,←plus_times_fac]
  ring
lemma fac_neg_product {t : R} {d : ℕ} (ht : t^(d+1)=0) :
    fac t d * fac (-t) d * fac (t^4) d = fac (t^2) d ^ 3 := by
  have he (s : R) (hs : s^(d+1)=0) : fac s d =
       fac (s^2) d * ∏ i ∈ range d, (1-s^(2*i+1)) := by
    simpa only [fac_stable s hs (show d ≤ 2*d by omega)] using fac_even_odd s d
  let u := t^2
  let A := ∏ i ∈ range d, (1-t^(2*i+1))
  let B := ∏ i ∈ range d, (1-(-t)^(2*i+1))
  have hAB : A*B = ∏ i ∈ range d, (1-u^(2*i+1)) := by
    rw [show A*B = ∏ i ∈ range d, (1-t^(2*i+1))*(1-(-t)^(2*i+1)) by exact prod_mul_distrib.symm]
    apply prod_congr rfl
    intro i _
    rw [Odd.neg_pow (show Odd (2*i+1) from ⟨i,rfl⟩)]
    rw [show u^(2*i+1) = (t^(2*i+1))^2 by dsimp [u]; rw [←pow_mul,mul_comm,pow_mul]]
    ring
  have hplus : fac t d = fac u d * A := he _ ht
  have hminus : fac (-t) d = fac u d * B := by
    simpa only [neg_sq] using he (-t) (by rw [neg_eq_neg_one_mul t,mul_pow,ht,mul_zero])
  have hdouble : fac u d = fac (t^4) d * (A*B) := by
    rw [hAB,←show u^2 = t^4 by dsimp [u]; rw [←pow_mul]]
    exact he _ (nil_pow ht (by decide))
  rw [hplus,hminus,hdouble]
  ring
lemma unsign (t : R) (j : ℤ) : ((j.negOnePow:ℤ):R)*(-t)^j.natAbs^2 = t^j.natAbs^2 := by
  rw [Int.coe_negOnePow,neg_eq_neg_one_mul t,mul_pow,←mul_assoc,←pow_add]
  have he (k : ℕ) : Even (k+k^2) := by
    obtain ⟨l,rfl|rfl⟩ := Nat.even_or_odd' k
    · exact ⟨l+2*l^2,by ring⟩
    · exact ⟨2*l^2+3*l+1,by ring⟩
  rw [(he _).neg_one_pow,one_mul]
theorem eta_four_factors (t : R) (d : ℕ) (ht : t^(d+1)=0) :
    (∑ k ∈ range (d+1), (t^2)^((k+1).choose 2)) *
      (∑ j ∈ Icc (-(d:ℤ)) (d:ℤ), ((j.negOnePow:ℤ):R)*t^(j.natAbs^2))^2 *
      (∑ j ∈ Icc (-(d:ℤ)) (d:ℤ), t^(j.natAbs^2)) = fac t d ^ 2 * fac (t^2) d ^ 2 := by
  let A := ∑ k ∈ range (d+1), (t^2)^((k+1).choose 2)
  let B := ∑ j ∈ Icc (-(d:ℤ)) (d:ℤ), ((j.negOnePow:ℤ):R)*t^(j.natAbs^2)
  let C := ∑ j ∈ Icc (-(d:ℤ)) (d:ℤ), t^(j.natAbs^2)
  let E := fac (t^2) d
  have ha : A*E = fac (t^4) d ^ 2 := by
    simpa only [A,E,← pow_mul] using triangular_sum (nil_pow ht (k:=2) (by decide))
  have he (u : R) (hu : u^(d+1)=0) := theta_stabilized u d (2*d) (by omega) hu (TunnellBalanced.balanced u (2*d))
  have hb : B*E = fac t d ^ 2 := (he t ht).symm
  have hc : C*E = fac (-t) d ^ 2 := by
    simpa only [unsign,neg_sq] using (he (-t) (by rw [neg_eq_neg_one_mul t,mul_pow,ht,mul_zero])).symm
  have hu : IsUnit E := fac_unit _ ⟨d+1,nil_pow ht (by decide)⟩ d
  have htr : A*B*C = E^3 := by
    apply (hu.pow 3).mul_left_injective
    calc A*B*C*E^3 = (A*E)*(B*E)*(C*E) := by ring
         _ = (fac t d * fac (-t) d * fac (t^4) d)^2 := by rw [ha,hb,hc]; ring
         _ = E^3*E^3 := by rw [fac_neg_product ht]; ring
  calc A*B^2*C = (A*B*C)*B := by ring
       _ = (B*E)*E^2 := by rw [htr]; ring
       _ = _ := by rw [hb]
end TunnellQuaternionTheta
namespace TunnellQuaternionTheta
open Polynomial Finset TunnellQBin TunnellTruncated
theorem shell_coefficient (d : ℕ) :
    (X * ∏ i ∈ Icc 1 d, ((1-(X:ℤ[X])^(4*i))^2*(1-X^(8*i))^2)).coeff d =
      ∑ k ∈ range (d+1), ∑ r ∈ Icc (-(d:ℤ)) (d:ℤ), ∑ s ∈ Icc (-(d:ℤ)) (d:ℤ),
        ∑ t ∈ Icc (-(d:ℤ)) (d:ℤ),
          if (2*k+1)^2 + 4*(r.natAbs^2+s.natAbs^2+t.natAbs^2) = d
          then ((r+s).negOnePow:ℤ) else 0 := by
  let I := Icc (-(d:ℤ)) (d:ℤ)
  let u : ℤ[X] := X^4
  let a (k : ℕ) : ℤ[X] := (u^2)^((k+1).choose 2)
  let b (j : ℤ) : ℤ[X] := ((j.negOnePow:ℤ):ℤ[X]) * u^(j.natAbs^2)
  let c (j : ℤ) : ℤ[X] := u^(j.natAbs^2)
  let A := ∑ k ∈ range (d+1), a k
  let B := ∑ j ∈ I, b j
  let C₀ := ∑ j ∈ I, c j
  have hdiv : X^(d+1) ∣
      (X * ∏ i ∈ Icc 1 d, ((1-(X:ℤ[X])^(4*i))^2*(1-X^(8*i))^2)) - X*A*B^2*C₀ := by
    have hbase : (∏ i ∈ Icc 1 d, ((1-(X:ℤ[X])^(4*i))^2*(1-X^(8*i))^2)) =
        fac u d ^ 2 * fac (u^2) d ^ 2 := by
      simp only [prod_mul_distrib,prod_pow,u,←pow_mul,poly_fac]
    rw [hbase]
    apply (AdjoinRoot.mk_eq_mk).mp
    change trunc d _ = trunc d _
    have he := eta_four_factors (trunc d u) d (trunc_pow d 4 (by decide))
    simp only [A,B,C₀,a,b,c,I,map_mul,map_pow,map_fac,map_sum,map_intCast]
    rw [←he]
    ring
  have he := (X_pow_dvd_iff.mp hdiv) d (by omega)
  rw [coeff_sub,sub_eq_zero] at he
  rw [he]
  have hmono (k : ℕ) (r s t : ℤ) :
      (X*a k*b r*b s*c t).coeff d =
        if (2*k+1)^2+4*(r.natAbs^2+s.natAbs^2+t.natAbs^2)=d
        then ((r+s).negOnePow:ℤ) else 0 := by
    have hh : X*a k*b r*b s*c t =
        C ((r+s).negOnePow:ℤ) * X^((2*k+1)^2+4*(r.natAbs^2+s.natAbs^2+t.natAbs^2)) := by
      have hcast (z : ℤ) : Polynomial.C z = (z:ℤ[X]) := by
        simpa only [Int.cast_id] using (map_intCast (Polynomial.C : ℤ →+* ℤ[X]) z)
      rw [←TunnellJacobiFiniteBridge.exponent_eq k]
      simp only [a,b,c,u,Int.negOnePow_add,Units.val_mul, Int.cast_mul,pow_add,pow_mul,pow_one,hcast]
      ring
    rw [hh,coeff_C_mul_X_pow]
    split_ifs <;> first | rfl | contradiction | (exfalso; solve_by_elim [Eq.symm])
  have hsum : X*A*B^2*C₀ =
      ∑ k ∈ range (d+1), ∑ r ∈ I, ∑ s ∈ I, ∑ t ∈ I, X*a k*b r*b s*c t := by
    simp only [←Finset.sum_mul,←Finset.mul_sum, A,B,C₀,sq]
    ring
  rw [hsum]
  simp only [I,finsetSum_coeff,hmono]
end TunnellQuaternionTheta
namespace TunnellQuaternion
open Finset Quaternion TunnellShell Polynomial
abbrev Parameter := ℕ × ℤ × ℤ × ℤ
def paramNorm (u : Parameter) : ℕ := (2*u.1+1)^2+
  4*(u.2.1.natAbs^2+u.2.2.1.natAbs^2+u.2.2.2.natAbs^2)
def encode (u : Parameter) : QInt := ⟨2*(u.1:ℤ)+1,2*u.2.1,2*u.2.2.1,2*u.2.2.2⟩
def decode (q : QInt) : Parameter := (q.re.toNat/2,q.imI/2,q.imJ/2,q.imK/2)
def oddParams (p : ℕ) : Finset Parameter :=
  let I := Icc (-(p:ℤ)) (p:ℤ)
  ((range (p+1)) ×ˢ I ×ˢ I ×ˢ I).filter (fun u => paramNorm u=p)
lemma mem_oddParams {p : ℕ} {u : Parameter} : u ∈ oddParams p ↔ paramNorm u=p := by
  simp only [oddParams,mem_filter,mem_product,mem_range,mem_Icc]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  obtain ⟨k,r,s,t⟩ := u
  change (2*k+1)^2+4*(r.natAbs^2+s.natAbs^2+t.natAbs^2)=p at h
  have hh (z : ℤ) (hz : z.natAbs^2 ≤ p) : -(p:ℤ) ≤ z ∧ z ≤ p := by
    have := Nat.le_mul_self z.natAbs
    have := Int.natAbs_eq z
    rw [sq] at hz
    omega
  exact ⟨by nlinarith,hh r (by omega),hh s (by omega),hh t (by omega)⟩
lemma encode_norm (u : Parameter) : Quaternion.normSq (encode u) = (paramNorm u:ℤ) := by
  rw [Quaternion.normSq_def' (encode u)]
  rcases u with ⟨k,r,s,t⟩
  simp only [encode,paramNorm,Nat.cast_add,Nat.cast_mul,Nat.cast_one,
    Nat.cast_pow,Nat.cast_ofNat,Int.natAbs_sq]
  ring
lemma encode_decode {p : ℕ} {q : QInt} (hp : p%4=1) (hq : q ∈ quatShell p)
    (h₁ : q.re%2=1) (h₂ : 0 < q.re) : encode (decode q) = q := by
  have h := parity_count p (Nat.odd_iff.mpr (by omega)) hq
  rw [hp] at h
  ext <;> simp only [encode,decode] <;> omega
lemma decode_encode (u : Parameter) : decode (encode u) = u := by
  rcases u with ⟨k,r,s,t⟩
  ext <;> simp [decode,encode] <;> omega
def sign (u : Parameter) : ℤ := ((u.2.1+u.2.2.1).negOnePow:ℤ)
lemma eta_as_params (p : ℕ) :
    (X * ∏ i ∈ Icc 1 p, ((1-(X:ℤ[X])^(4*i))^2*(1-X^(8*i))^2)).coeff p =
      ∑ u ∈ oddParams p, sign u := by
  rw [TunnellQuaternionTheta.shell_coefficient,oddParams,sum_filter]
  simp only [sum_product,paramNorm,sign]
  rfl
lemma positive_section (p : ℕ) (hp : p%4=1) (v : Triple) :
    ∑ q ∈ quatShell p, (if q.re%2=1 ∧ 0<q.re then coordWeight (rotate q v) else 0) =
      (∑ u ∈ oddParams p, sign u)*coordWeight v := by
  rw [←sum_filter,sum_mul]
  symm
  apply sum_nbij' encode decode
  · intro u hu
    simp only [mem_filter,mem_quatShell,encode_norm,mem_oddParams.mp hu,true_and]
    change (2*(u.1:ℤ)+1)%2 = 1 ∧ 0<2*(u.1:ℤ)+1
    omega
  · intro q hq
    obtain ⟨h₁,h₂,h₃⟩ := mem_filter.mp hq
    rw [mem_oddParams, ←Nat.cast_inj (R:=ℤ),←encode_norm,encode_decode hp h₁ h₂ h₃,mem_quatShell.mp h₁]
  · exact fun u _ => decode_encode u
  · intro q hq
    obtain ⟨h₁,h₂,h₃⟩ := mem_filter.mp hq
    exact encode_decode hp h₁ h₂ h₃
  · intro u _
    exact (split_coord (u.1:ℤ) u.2.1 u.2.2.1 u.2.2.2 v).symm
lemma sum_neg (p : ℕ) (f : QInt → ℤ) : ∑ q ∈ quatShell p, f (-q) = ∑ q ∈ quatShell p, f q := by
  apply sum_nbij' Neg.neg Neg.neg
  · intro q h; simpa only [mem_quatShell,Quaternion.normSq_neg] using h
  · intro q h; simpa only [mem_quatShell,Quaternion.normSq_neg] using h
  · exact fun _ _ => neg_neg _
  · exact fun _ _ => neg_neg _
  · exact fun _ _ => rfl
lemma odd_section (p : ℕ) (v : Triple) :
    ∑ q ∈ quatShell p, (if q.re%2=1 then coordWeight (rotate q v) else 0) =
      2 * ∑ q ∈ quatShell p, (if q.re%2=1 ∧ 0<q.re then coordWeight (rotate q v) else 0) := by
  let f (q : QInt) := if q.re%2=1 ∧ 0<q.re then coordWeight (rotate q v) else 0
  have h (q : QInt) : (if q.re%2=1 then coordWeight (rotate q v) else 0) = f q + f (-q) := by
    have hr : rotate (-q) v = rotate q v := by simp [rotate]
    simp only [f,Quaternion.re_neg,hr,Int.neg_emod_two]
    split_ifs <;> omega
  simp_rw [h,sum_add_distrib,sum_neg]
  ring
def flipI (q : QInt) : QInt := ⟨q.re,-q.imI,q.imJ,q.imK⟩
lemma even_section (p : ℕ) (hp : p%4=3) (v : Triple) :
    ∑ q ∈ quatShell p, (if q.re%2=0 then coordWeight (rotate q v) else 0) = 0 := by
  let f (q : QInt) := if q.re%2=0 then coordWeight (rotate q v) else 0
  have hf (q : QInt) : Quaternion.normSq (flipI q) = Quaternion.normSq q := by
    rw [Quaternion.normSq_def' (flipI q),Quaternion.normSq_def' q]
    simp [flipI]
  have he : ∑ q ∈ quatShell p, f (flipI q) = ∑ q ∈ quatShell p, f q := by
    apply sum_nbij' flipI flipI
    · intro q h; simpa only [mem_quatShell,hf] using h
    · intro q h; simpa only [mem_quatShell,hf] using h
    · intro q _; ext <;> simp [flipI]
    · intro q _; ext <;> simp [flipI]
    · exact fun _ _ => rfl
  have hs (q : QInt) (hq : q ∈ quatShell p) : f (flipI q) = - f q := by
    have h := parity_count p (Nat.odd_iff.mpr (by omega)) hq
    rw [hp] at h
    by_cases ha : q.re%2=0
    · obtain ⟨a,b,c,d⟩ := q
      change a%2=0 at ha
      change a%2+b%2+c%2+d%2=(3:ℤ) at h
      simp only [f,flipI,if_pos ha]
      obtain ⟨k,rfl⟩ : ∃ k, a=2*k := ⟨a/2,by omega⟩
      obtain ⟨r,rfl⟩ : ∃ r, b=2*r+1 := ⟨b/2,by omega⟩
      obtain ⟨s,rfl⟩ : ∃ s, c=2*s+1 := ⟨c/2,by omega⟩
      obtain ⟨t,rfl⟩ : ∃ t, d=2*t+1 := ⟨d/2,by omega⟩
      exact inert_coord k r s t v
    · simp only [f,flipI,if_neg ha,neg_zero]
  rw [sum_congr rfl hs,sum_neg_distrib] at he
  change ∑ q ∈ quatShell p, f q = 0
  omega
noncomputable abbrev etaCoeff (p : ℕ) : ℤ :=
  (X * ∏ i ∈ Icc 1 p, ((1-(X:ℤ[X])^(4*i))^2*(1-X^(8*i))^2)).coeff p
lemma coord_average (p : ℕ) (hp : Odd p) (v : Triple) :
    ∑ q ∈ quatShell p, coordWeight (rotate q v) = 8*etaCoeff p*coordWeight v := by
  rw [four_sections p hp]
  by_cases h : p%4=1
  · simp only [h,if_true]
    rw [odd_section,positive_section p h,←eta_as_params]
    ring
  · have h3 : p%4=3 := by have ho := Nat.odd_iff.mp hp; omega
    simp only [h,if_false,even_section p h3,mul_zero]
    have hn : oddParams p = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro u hu
      have hq : encode u ∈ quatShell p := by rw [mem_quatShell,encode_norm,mem_oddParams.mp hu]
      have hh := parity_count p hp hq
      rw [h3] at hh
      simp only [encode] at hh
      omega
    rw [etaCoeff,eta_as_params,hn,sum_empty]
    ring
def cycleQ (q : QInt) : QInt := ⟨q.re,q.imJ,q.imK,q.imI⟩
lemma cycle_rotate (q : QInt) (v : Triple) : rot (rotate q v) = rotate (cycleQ q) (rot v) := by
  obtain ⟨a,b,c,d⟩ := q
  obtain ⟨x,y,z⟩ := v
  simp only [cycleQ,rot,rotate_apply]
  ext <;> ring
lemma sum_cycle (p : ℕ) (f : QInt → ℤ) : ∑ q ∈ quatShell p, f (cycleQ q) = ∑ q ∈ quatShell p, f q := by
  have h (q : QInt) : Quaternion.normSq (cycleQ q) = Quaternion.normSq q := by
    rw [Quaternion.normSq_def' (cycleQ q),Quaternion.normSq_def' q]
    simp only [cycleQ]
    ring
  apply sum_nbij' cycleQ (fun q => cycleQ (cycleQ q))
  · intro q hq; simpa only [mem_quatShell,h] using hq
  · intro q hq; simpa only [mem_quatShell,h] using hq
  · exact fun q _ => rfl
  · exact fun q _ => rfl
  · exact fun q _ => rfl
theorem raw_eigenvalue (p : ℕ) (hp : Odd p) (v : Triple) :
    ∑ q ∈ quatShell p, weight (rotate q v) = 8 * etaCoeff p * weight v := by
  simp only [weight,Finset.sum_add_distrib,cycle_rotate]
  rw [sum_cycle p (fun q => coordWeight (rotate q (rot v))),
    sum_cycle p (fun q => coordWeight (rotate (cycleQ q) (rot (rot v)))),
    sum_cycle p (fun q => coordWeight (rotate q (rot (rot v))))]
  simp only [coord_average p hp,mul_add]
end TunnellQuaternion
namespace TunnellBrandt
open TunnellHurwitzFour TunnellToricSign TunnellShell TunnellQuaternion Finset
def integral (q : QInt) : H ℤ := (q.re-q.imK,q.imI-q.imK,q.imJ-q.imK,2*q.imK)
lemma integral_norm (q : QInt) : nr (integral q)=Quaternion.normSq q := by
  obtain ⟨a,b,c,d⟩ := q; dsimp [integral,nr]; rw [normSq_mk]; ring
lemma integral_injective : Function.Injective integral := by
  rintro ⟨a,b,c,d⟩ ⟨e,f,g,h⟩ he
  simp only [integral,Prod.mk.injEq] at he
  apply QuaternionAlgebra.ext <;> dsimp only <;> omega
lemma even_integral (x : H ℤ) : Even x.2.2.2 ↔ ∃ q, integral q=x := by
  obtain ⟨a,b,c,d⟩ := x
  constructor
  · rintro ⟨k,hk⟩
    change d=k+k at hk
    exact ⟨⟨a+k,b+k,c+k,k⟩,by simp [integral,Prod.ext_iff]; omega⟩
  · rintro ⟨q,hq⟩; have he := congrArg (fun z:H ℤ => z.2.2.2) hq
    exact ⟨q.imK,by dsimp [integral] at he; dsimp; omega⟩
def U {R : Type*} [CommRing R] (i : Fin 3) : H R := ![(1,0,0,0),(0,0,0,1),(-1,0,0,1)] i
def V {R : Type*} [CommRing R] (i : Fin 3) : H R := ![(1,0,0,0),(1,0,0,-1),(0,0,0,-1)] i
lemma cancel_U {R : Type*} [CommRing R] (i : Fin 3) (x : H R) : prod (V i) (prod (U i) x)=x := by
  obtain ⟨a,b,c,d⟩ := x; fin_cases i <;> simp [prod,U,V,Prod.ext_iff] <;> ring_nf <;> simp
lemma cancel_V {R : Type*} [CommRing R] (i : Fin 3) (x : H R) : prod (U i) (prod (V i) x)=x := by
  obtain ⟨a,b,c,d⟩ := x; fin_cases i <;> simp [prod,U,V,Prod.ext_iff] <;> ring_nf <;> simp
lemma norm_U {R : Type*} [CommRing R] (i : Fin 3) (x : H R) : nr (prod (U i) x)=nr x := by
  obtain ⟨a,b,c,d⟩ := x; fin_cases i <;> dsimp [U,prod,nr] <;> ring
def red2 (x : H ℤ) : H (ZMod 2) := (x.1,x.2.1,x.2.2.1,x.2.2.2)
lemma uniqueness_table : ∀ x : H (ZMod 2), nr x=1 → ∃ i:Fin 3, (prod (V i) x).2.2.2=0 ∧ ∀ j:Fin 3, (prod (V j) x).2.2.2=0 → j=i := by decide
lemma unique_copy {x : H ℤ} (h : Odd (nr x)) : ∃! i:Fin 3, Even (prod (V i) x).2.2.2 := by
  have hn : nr (red2 x)=((nr x:ℤ):ZMod 2) := by obtain ⟨a,b,c,d⟩ := x; simp [red2,nr]
  have heq : ((nr x:ℤ):ZMod 2)=1 := by
    apply ZMod.val_injective; have H := ZMod.val_intCast (n:=2) (nr x); have e := Int.odd_iff.mp h; change _=1; omega
  rw [heq] at hn
  obtain ⟨i,hi,hu⟩ := uniqueness_table (red2 x) hn
  have he (j : Fin 3) : (prod (V j) (red2 x)).2.2.2=0 ↔ Even (prod (V j) x).2.2.2 := by
    have e : (prod (V j) (red2 x)).2.2.2=(((prod (V j) x).2.2.2:ℤ):ZMod 2) := by
      have rem : ∀ a b : ZMod 2, a-b=a+b := by decide
      obtain ⟨a,b,c,d⟩ := x; fin_cases j <;> simp [prod,red2,V,rem]
    rw [e,ZMod.intCast_zmod_eq_zero_iff_dvd,even_iff_two_dvd]; rfl
  exact ⟨i,(he i).mp hi,fun j hj => hu j ((he j).mpr hj)⟩
def encode (p : Fin 3 × QInt) : H ℤ := prod (U p.1) (integral p.2)
def normShell (m : ℕ) : Finset (H ℤ) := (univ ×ˢ quatShell m).image encode
lemma mem_normShell {m : ℕ} (hm : Odd m) (q : H ℤ) : q∈normShell m ↔ nr q=(m:ℤ) := by
  constructor
  · rintro h; obtain ⟨⟨i,r⟩,hp,rfl⟩ := mem_image.mp h
    exact (norm_U i _).trans ((integral_norm r).trans (mem_quatShell.mp (mem_product.mp hp).2))
  · intro h
    obtain ⟨i,hi,_⟩ := unique_copy (h ▸ (by exact_mod_cast hm : Odd (m:ℤ)))
    obtain ⟨r,hr⟩ := (even_integral _).mp hi
    have he : encode (i,r)=q := by rw [encode,hr,cancel_V]
    have heq : Quaternion.normSq r=(m:ℤ) := by rw [←integral_norm,←h,←he]; exact (norm_U i _).symm
    exact mem_image.mpr ⟨(i,r),mem_product.mpr ⟨mem_univ _,mem_quatShell.mpr heq⟩,he⟩
lemma encode_inj {m : ℕ} (hm : Odd m) : Set.InjOn encode ((univ ×ˢ quatShell m : Finset (Fin 3 × QInt)):Set _) := by
  rintro ⟨i,q⟩ hq ⟨j,r⟩ hr he
  have hnorm : nr (encode (i,q))=m := (norm_U i _).trans ((integral_norm q).trans (mem_quatShell.mp (mem_product.mp hq).2))
  have hodd : Odd (nr (encode (i,q))) := by rw [hnorm]; exact_mod_cast hm
  obtain ⟨k,hk,hu⟩ := unique_copy hodd
  have hside (i : Fin 3) (q : QInt) : Even (prod (V i) (encode (i,q))).2.2.2 := by
    rw [encode,cancel_U]; exact (even_integral _).mpr ⟨q,rfl⟩
  have hi := hu i (hside i q)
  have hj := hu j (he ▸ hside j r)
  obtain rfl : i=j := hi.trans hj.symm
  have e := congrArg (prod (V i)) he
  change prod (V i) (prod (U i) (integral q))=prod (V i) (prod (U i) (integral r)) at e
  rw [cancel_U,cancel_U] at e
  rw [integral_injective e]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private abbrev caseUnits (a b:Z4) := ∀ c d:Z4,
    let q:H4 := (a,b,c,d)
    (nr q).val%2=1 → ∀ i:Fin 3, orbitScalar (prod (U i) q)=orbitScalar q
set_option maxRecDepth 10000 in
private lemma caseUnits00 : caseUnits 0 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits01 : caseUnits 0 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits02 : caseUnits 0 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits03 : caseUnits 0 3 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits10 : caseUnits 1 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits11 : caseUnits 1 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits12 : caseUnits 1 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits13 : caseUnits 1 3 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits20 : caseUnits 2 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits21 : caseUnits 2 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits22 : caseUnits 2 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits23 : caseUnits 2 3 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits30 : caseUnits 3 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits31 : caseUnits 3 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits32 : caseUnits 3 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseUnits33 : caseUnits 3 3 := by decide
lemma char_U_table : ∀ q ∈ units, ∀ i : Fin 3, character (prod (U i) q)=character q := by
  simp only [characterOrbit,units,Finset.mem_filter,Finset.mem_univ,true_and]
  rintro ⟨a,b,c,d⟩
  fin_cases a <;> fin_cases b
  · exact caseUnits00 c d
  · exact caseUnits01 c d
  · exact caseUnits02 c d
  · exact caseUnits03 c d
  · exact caseUnits10 c d
  · exact caseUnits11 c d
  · exact caseUnits12 c d
  · exact caseUnits13 c d
  · exact caseUnits20 c d
  · exact caseUnits21 c d
  · exact caseUnits22 c d
  · exact caseUnits23 c d
  · exact caseUnits30 c d
  · exact caseUnits31 c d
  · exact caseUnits32 c d
  · exact caseUnits33 c d

lemma char_U {q : H ℤ} (hq : Odd (nr q)) (i : Fin 3) : character (modFour (prod (U i) q))=character (modFour q) := by
  rw [modFour_mul]
  have he : modFour (U i)=U i := by fin_cases i <;> rfl
  rw [he]; exact char_U_table _ (odd_units q hq) i
lemma integral_rot (q : QInt) (v : Triple) : TunnellToricSign.rotate (integral q) v=TunnellQuaternion.rotate q v := by
  obtain ⟨a,b,c,d⟩ := q; obtain ⟨x,y,z⟩ := v
  rw [rotate_apply]
  simp only [integral,TunnellToricSign.rotate,Prod.mk.injEq]
  exact ⟨by ring,by ring,by ring⟩
lemma weight_color {v : Triple} (hx : Odd v.1) (hy : Odd v.2.1) (hz : Even v.2.2) : weight v=color (redVec v) := by
  obtain ⟨x,y,z⟩ := v
  change Odd x at hx; change Odd y at hy; change Even z at hz
  have hA := ZMod.val_intCast (n:=8) x
  have hB := ZMod.val_intCast (n:=8) y
  have hC := ZMod.val_intCast (n:=8) z
  have eA := Int.odd_iff.mp hx
  have eB := Int.odd_iff.mp hy
  have hx' : (x:Z8).val%2≠0 := by omega
  have hy' : (y:Z8).val%2≠0 := by omega
  have h0 : (z:Z8)=0 ↔ z%8=0 := by rw [←(ZMod.val_injective 8).eq_iff]; change _=0 ↔ _; omega
  have h4 : (z:Z8)=4 ↔ z%8=4 := by rw [←(ZMod.val_injective 8).eq_iff]; change _=4 ↔ _; omega
  simp [weight,rot,coordWeight_eq,Int.not_odd_iff_even.mpr hz,hx,hy,color,redVec,hx',hy',h0,h4,lastWeight]
lemma integral_char {q : QInt} (hq : Odd (Quaternion.normSq q)) :
    character (modFour (integral q))=weight (TunnellQuaternion.rotate q (1,1,0)) := by
  have hc := color_rotate (v:=(1,1,0)) (by decide) (by decide) (by decide) (q:=integral q) (by rwa [integral_norm])
  rw [integral_rot,show color (redVec (1,1,0))=1 by decide,mul_one] at hc
  rw [←hc]
  apply Eq.symm
  apply weight_color
  all_goals obtain ⟨a,b,c,d⟩ := q; rw [normSq_mk] at hq; rw [rotate_apply]; dsimp only
  · obtain ⟨k,h⟩ := hq; exact ⟨k-c^2-d^2+b*c-a*d,by linear_combination h⟩
  · obtain ⟨k,h⟩ := hq; exact ⟨k-b^2-d^2+b*c+a*d,by linear_combination h⟩
  · exact ⟨b*d-a*c+c*d+a*b,by ring⟩
theorem signed_lipschitz {m : ℕ} (hm : Odd m) :
    ∑ q∈quatShell m, character (modFour (integral q))=8*etaCoeff m := by
  calc (∑ q∈quatShell m, character (modFour (integral q))) = ∑ q∈quatShell m,weight (TunnellQuaternion.rotate q (1,1,0)) := by
         apply sum_congr rfl; intro q hq
         exact integral_char (by rw [mem_quatShell.mp hq]; exact_mod_cast hm)
       _ = _ := by rw [raw_eigenvalue m hm,show weight (1,1,0)=1 by decide,mul_one]
theorem signed_hurwitz {m : ℕ} (hm : Odd m) : ∑ q∈normShell m,character (modFour q)=24*etaCoeff m := by
  rw [normShell,sum_image (encode_inj hm),sum_product]
  have h (i : Fin 3) : (∑ q ∈ quatShell m,character (modFour (encode (i,q))))=8*etaCoeff m := by
    rw [←signed_lipschitz hm]
    apply sum_congr rfl; intro q hq
    apply char_U
    rw [integral_norm,mem_quatShell.mp hq]; exact_mod_cast hm
  simp only [h,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; ring
theorem hurwitz_card {m : ℕ} (hm : Odd m) : (normShell m).card=24*∑ d∈m.divisors,d := by
  rw [normShell,card_image_of_injOn (encode_inj hm),card_product,card_univ,Fintype.card_fin,
    quatShell_card_divisors (show m≠0 by rintro rfl; simp at hm)]
  have he : (m.divisors.filter fun d => ¬4∣d)=m.divisors := by
    apply filter_true_of_mem
    intro d hd h4
    have he : (2:ℕ)∣m := (show (2:ℕ)∣4 by decide).trans (h4.trans (Nat.dvd_of_mem_divisors hd))
    exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr he)
  rw [he]; ring
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
private abbrev caseSwap (a b:Z4) := ∀ c d:Z4,
    let q:H4 := (a,b,c,d)
    (nr q).val%2=1 → orbitScalar (prod q tau)= -orbitScalar q
set_option maxRecDepth 10000 in
private lemma caseSwap00 : caseSwap 0 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap01 : caseSwap 0 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap02 : caseSwap 0 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap03 : caseSwap 0 3 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap10 : caseSwap 1 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap11 : caseSwap 1 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap12 : caseSwap 1 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap13 : caseSwap 1 3 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap20 : caseSwap 2 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap21 : caseSwap 2 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap22 : caseSwap 2 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap23 : caseSwap 2 3 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap30 : caseSwap 3 0 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap31 : caseSwap 3 1 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap32 : caseSwap 3 2 := by decide
set_option maxRecDepth 10000 in
private lemma caseSwap33 : caseSwap 3 3 := by decide
lemma swap_character : ∀ q ∈ units, character (prod q tau)= -character q := by
  simp only [characterOrbit,units,Finset.mem_filter,Finset.mem_univ,true_and]
  rintro ⟨a,b,c,d⟩
  fin_cases a <;> fin_cases b
  · exact caseSwap00 c d
  · exact caseSwap01 c d
  · exact caseSwap02 c d
  · exact caseSwap03 c d
  · exact caseSwap10 c d
  · exact caseSwap11 c d
  · exact caseSwap12 c d
  · exact caseSwap13 c d
  · exact caseSwap20 c d
  · exact caseSwap21 c d
  · exact caseSwap22 c d
  · exact caseSwap23 c d
  · exact caseSwap30 c d
  · exact caseSwap31 c d
  · exact caseSwap32 c d
  · exact caseSwap33 c d

end TunnellBrandt
namespace TunnellBrandt
open TunnellHurwitzFour TunnellToricSign TunnellShell TunnellQuaternion Finset
open scoped Classical
def sign : Bool → ℤ | true => -1 | false => 1
def label (q : H4) : Bool → ℤ | true => character (prod q tau) | false => character q
def count (m : ℕ) (i j : Bool) : ℕ := ((normShell m).filter (fun q => label (modFour q) i=sign j)).card
 
def entry (m : ℕ) (i j : Bool) : ℚ := (count m i j)/24
lemma count_eq {m : ℕ} (hm : Odd m) (i j : Bool) :
    2*(count m i j:ℤ)=24*(∑ d∈m.divisors,(d:ℤ))+24*sign i*sign j*etaCoeff m := by
  let S := normShell m
  let P := fun q : H ℤ => label (modFour q) i=sign j
  have hc : (count m i j:ℤ)=∑ q∈S, if P q then 1 else 0 := by
    rw [←sum_filter]; simp [count,S,P]
  have ht (q : H ℤ) (hq : q∈S) : 2*(if P q then (1:ℤ) else 0)=1+sign i*sign j*character (modFour q) := by
    have hodd : Odd (nr q) := by rw [(mem_normShell hm q).mp hq]; exact_mod_cast hm
    have hτ := swap_character _ (odd_units q hodd)
    have hv : label (modFour q) i=sign i*character (modFour q) := by
      cases i
      · exact (one_mul (character (modFour q))).symm
      · exact hτ.trans (neg_one_mul (character (modFour q))).symm
    have hsign (i : Bool) : sign i=1 ∨ sign i= -1 := by cases i <;> decide
    have hchar : character (modFour q)=1 ∨ character (modFour q)= -1 := by unfold character; split <;> simp
    have ident (u v t : ℤ) (hu : u=1 ∨ u= -1) (hv : v=1 ∨ v= -1) (ht : t=1 ∨ t= -1) :
        2*(if u*t=v then (1:ℤ) else 0)=1+u*v*t := by
      rcases hu with rfl|rfl <;> rcases hv with rfl|rfl <;> rcases ht with rfl|rfl <;> decide
    change 2*(if label (modFour q) i=sign j then (1:ℤ) else 0)=_
    rw [hv]
    exact ident _ _ _ (hsign i) (hsign j) hchar
  have he : ((S.card:ℕ):ℤ)=24*∑ d∈m.divisors,(d:ℤ) := by
    change ((normShell m).card:ℤ)=_
    rw [hurwitz_card hm]; push_cast; rfl
  rw [hc,mul_sum,sum_congr rfl ht,sum_add_distrib,←mul_sum,signed_hurwitz hm]
  simp only [sum_const,nsmul_eq_mul,mul_one]; rw [he]; ring
theorem entry_eq {m : ℕ} (hm : Odd m) (i j : Bool) :
    2*entry m i j=(∑ d∈m.divisors,(d:ℚ))+(sign i:ℚ)*(sign j:ℚ)*(etaCoeff m:ℚ) := by
  have h := congrArg (fun t:ℤ => (t:ℚ)) (count_eq hm i j)
  push_cast at h
  unfold entry
  linear_combination h / 24
theorem cm_height {m : ℕ} (hm : Odd m) {T : Type*} [Fintype T] (c : T → Bool) :
    2*(∑ a:T,∑ b:T,entry m (c a) (c b)) =
      (Fintype.card T:ℚ)^2*(∑ d∈m.divisors,(d:ℚ))+
      (∑ a:T,(sign (c a):ℚ))^2*(etaCoeff m:ℚ) := by
  let σ : ℚ := ∑ d∈m.divisors,(d:ℚ)
  let f : T → ℚ := fun a => sign (c a)
  change 2*(∑ a:T,∑ b:T,entry m (c a) (c b)) = (Fintype.card T:ℚ)^2*σ+(∑ a:T,f a)^2*(etaCoeff m:ℚ)
  have he (a b : T) : 2*entry m (c a) (c b)=σ+f a*(f b*(etaCoeff m:ℚ)) := by rw [entry_eq hm]; dsimp [σ,f]; ring
  simp only [mul_sum,he,sum_add_distrib,sum_const,card_univ,nsmul_eq_mul]
  simp_rw [←mul_sum]
  simp only [←sum_mul]
  ring
def which (q : H4) : Bool := if q∈orbit e then false else true
lemma sign_which (q : H4) : sign (which q)=character q := by
  unfold which character
  split <;> rfl
end TunnellBrandt
namespace TunnellBrandtDoubleCoset
open TunnellBrandt TunnellHurwitzFour TunnellTwoProjectionTransport TunnellRamifiedTwoOrder TunnellHurwitz TunnellToricSign TunnellToric
open Finset
noncomputable section
def rep : Bool → H4 | true => tau | false => e
def indicator (s x t : H4) : ℕ := if prod (prod (bar s) x) t∈orderUnits then 1 else 0
def raw (m : ℕ) (s t : H4) := ∑ q∈normShell m,indicator s (modFour q) t
lemma hmul_assoc {R : Type*} [CommRing R] (s t u : H R) : prod (prod s t) u=prod s (prod t u) := by
  rcases s with ⟨a,b,c,d⟩; rcases t with ⟨e,f,g,h⟩; rcases u with ⟨i,j,k,l⟩
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)); all_goals dsimp [prod]; ring
lemma bar_mul {R : Type*} [CommRing R] (s t : H R) : bar (prod s t)=prod (bar t) (bar s) := by
  rcases s with ⟨a,b,c,d⟩; rcases t with ⟨e,f,g,h⟩
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)); all_goals dsimp [bar,prod]; ring
lemma red_bar (q : H ℤ) : modFour (bar q)=bar (modFour q) := by simp [modFour,bar]
lemma one_mul4 (q : H4) : prod e q=q := by rcases q with ⟨a,b,c,d⟩; simp [e,prod]
lemma mul_one4 (q : H4) : prod q e=q := by rcases q with ⟨a,b,c,d⟩; simp [e,prod]
set_option maxRecDepth 10000 in
lemma order_closed : ∀ a ∈ orderUnits, ∀ b ∈ orderUnits, prod a b ∈ orderUnits := by decide
set_option maxRecDepth 10000 in
lemma order_inverse : ∀ a ∈ orderUnits, ∃ b∈orderUnits, prod a b=e ∧ prod b a=e := by decide
set_option maxRecDepth 10000 in
lemma order_bar : ∀ a∈orderUnits, bar a∈orderUnits := by decide
lemma coset_action (u : H4) (hu : u∈orderUnits) (x : H4) :
    (prod (bar u) x∈orderUnits ↔ x∈orderUnits) ∧ (prod x u∈orderUnits ↔ x∈orderUnits) := by
  obtain ⟨v,hv,e,_⟩ := order_inverse u hu
  obtain ⟨w,hw,_,e'⟩ := order_inverse (bar u) (order_bar u hu)
  constructor
  · refine ⟨fun h => ?_,order_closed _ (order_bar u hu) _⟩
    have H := order_closed _ hw _ h
    rwa [←hmul_assoc,e',one_mul4] at H
  · refine ⟨fun h => ?_,fun h => order_closed _ h _ hu⟩
    have H := order_closed _ h _ hv
    rwa [hmul_assoc,e,mul_one4] at H
lemma iso (s x t a b u v : H4) (hu : u∈orderUnits) (hv : v∈orderUnits) :
    indicator (prod (prod a s) u) x (prod (prod b t) v) = indicator s (prod (prod (bar a) x) b) t := by
  unfold indicator
  have e : prod (prod (bar (prod (prod a s) u)) x) (prod (prod b t) v)=
      prod (bar u) (prod (prod (prod (bar s) (prod (prod (bar a) x) b)) t) v) := by
    simp only [bar_mul,hmul_assoc]
  simp only [e,(coset_action _ hu _).1,(coset_action _ hv _).2]
lemma orbit_rep {s : H4} (hs : s∈units) : ∃ a ∈ globalUnits, ∃ u∈orderUnits, prod (prod a (rep (which s))) u=s := by
  have he : s∈orbit (rep (which s)) := by
    by_cases h : s∈orbit e
    · simpa [which,h,rep] using h
    · have h' : s∈orbit tau := (mem_union.mp (two_orbits.1.symm ▸ hs)).resolve_left h
      simpa [which,h,rep] using h'
  obtain ⟨⟨a,u⟩,hu,e⟩ := mem_image.mp he
  exact ⟨a,(mem_product.mp hu).1,u,(mem_product.mp hu).2,e⟩
lemma nr_prod (x y : H ℤ) : nr (prod x y)=nr x*nr y := by
  have H := congrArg Quaternion.normSq (hamZ_mul x y)
  rw [map_mul,norm_ham,norm_ham,norm_ham] at H
  exact_mod_cast H
lemma nr_bar (x : H ℤ) : nr (bar x)=nr x := by rcases x with ⟨a,b,c,d⟩; dsimp [nr,bar]; ring
lemma bcancel {u : H ℤ} (hu : nr u=1) (x : H ℤ) : prod (bar u) (prod u x)=x ∧ prod (prod x u) (bar u)=x := by
  have e : Quaternion.normSq (hamZ u)=1 := by rw [norm_ham,hu]; norm_num
  constructor <;> apply ham_injective
  · rw [hamZ_mul,hamZ_mul,ham_bar,←mul_assoc,Quaternion.star_mul_self,e,Quaternion.coe_one,one_mul]
  · rw [hamZ_mul,hamZ_mul,ham_bar,mul_assoc,Quaternion.self_mul_star,e,Quaternion.coe_one,mul_one]
lemma bar_bar {R : Type*} [CommRing R] (q : H R) : bar (bar q)=q := by rcases q with ⟨a,b,c,d⟩; simp [bar]
lemma sum_unit {m : ℕ} (hm : Odd m) {u : H ℤ} (hu : nr u=1) (f : H4→ℕ) :
    (∑ q∈normShell m,f (prod (modFour u) (modFour q)))=(∑ q∈normShell m,f (modFour q)) ∧
    (∑ q∈normShell m,f (prod (modFour q) (modFour u)))=(∑ q∈normShell m,f (modFour q)) := by
  have h₁ := (nr_bar u).trans hu
  constructor
  · apply sum_nbij' (prod u) (prod (bar u))
    · intro q hq; rw [mem_normShell hm,nr_prod,hu,one_mul]; exact (mem_normShell hm q).mp hq
    · intro q hq; rw [mem_normShell hm,nr_prod,h₁,one_mul]; exact (mem_normShell hm q).mp hq
    · exact fun q _ => (bcancel hu q).1
    · intro q _; simpa only [bar_bar] using (bcancel h₁ q).1
    · intro q _; rw [modFour_mul]
  · apply sum_nbij' (fun q=>prod q u) (fun q=>prod q (bar u))
    · intro q hq; rw [mem_normShell hm,nr_prod,hu,mul_one]; exact (mem_normShell hm q).mp hq
    · intro q hq; rw [mem_normShell hm,nr_prod,h₁,mul_one]; exact (mem_normShell hm q).mp hq
    · exact fun q _ => (bcancel hu q).2
    · intro q _; simpa only [bar_bar] using (bcancel h₁ q).2
    · intro q _; rw [modFour_mul]
lemma raw_reps {m : ℕ} (hm : Odd m) {s t : H4} (hs : s∈units) (ht : t∈units) :
    raw m s t=raw m (rep (which s)) (rep (which t)) := by
  obtain ⟨a,ha,u,hu,ea⟩ := orbit_rep hs
  obtain ⟨b,hb,v,hv,eb⟩ := orbit_rep ht
  obtain ⟨A,hA,rfl⟩ := (global_iff a).mp ha
  obtain ⟨B,hB,rfl⟩ := (global_iff b).mp hb
  unfold raw
  conv_lhs => rw [←ea,←eb]
  simp_rw [iso _ _ _ _ _ _ _ hu hv,hmul_assoc (bar (modFour A))]
  have h₁ := (sum_unit hm hB (fun x => indicator (rep (which s)) (prod (bar (modFour A)) x) (rep (which t)))).2
  have h₂ := (sum_unit hm ((nr_bar A).trans hA) (fun x => indicator (rep (which s)) x (rep (which t)))).1
  rw [red_bar] at h₂
  exact h₁.trans h₂
lemma global_prod {a b : H4} (ha : a∈globalUnits) (hb : b∈globalUnits) : prod a b∈globalUnits := by
  obtain ⟨A,hA,rfl⟩ := (global_iff a).mp ha; obtain ⟨B,hB,rfl⟩ := (global_iff b).mp hb
  exact (global_iff _).mpr ⟨prod A B,by rw [nr_prod,hA,hB,one_mul],modFour_mul _ _⟩
lemma global_right {a : H4} (ha : a∈globalUnits) (f : H4→ℕ) :
    (∑ h∈globalUnits, f (prod h a))=∑ h∈globalUnits,f h := by
  obtain ⟨A,hA,rfl⟩ := (global_iff a).mp ha
  have hb : modFour (bar A)∈globalUnits := (global_iff _).mpr ⟨_,(nr_bar A).trans hA,rfl⟩
  apply sum_nbij' (fun h=>prod h (modFour A)) (fun h=>prod h (modFour (bar A)))
  · exact fun _ ht => global_prod ht ha
  · exact fun _ ht => global_prod ht hb
  · intro h hh; obtain ⟨C,_,rfl⟩ := (global_iff _).mp hh
    rw [←modFour_mul,←modFour_mul,(bcancel hA C).2]
  · intro h hh; obtain ⟨C,_,rfl⟩ := (global_iff _).mp hh
    have he := (bcancel ((nr_bar A).trans hA) C).2; rw [bar_bar] at he
    rw [←modFour_mul,←modFour_mul,he]
  · simp
lemma rep_e {R : Type*} [CommRing R] (x : H R) : prod x (1,0,0,0)=x := by rcases x with ⟨a,b,c,d⟩; simp [prod]
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma average_table (s t : Bool) (x : H4) (hx : x∈units) :
    (∑ h∈globalUnits, indicator (rep s) (prod h x) (rep t))=if label x t=sign s then 2 else 0 := by
  let z := prod x (rep t)
  have hZ : z∈units := by
    have he (u : H4) (hu : u∈units) : prod u tau∈units := by
      have H : nr (prod u tau)=nr u := by
        rcases u with ⟨a,b,c,d⟩
        rw [←sub_eq_zero]; dsimp [nr,prod,tau]; ring_nf; simp [show (4:Z4)=0 by decide,show (8:Z4)=0 by decide]
      exact mem_filter.mpr ⟨mem_univ _,H ▸ (mem_filter.mp hu).2⟩
    cases t
    · simpa [z,rep,e,rep_e] using hx
    · exact he _ hx
  have hlabel : label x t=character z := by cases t <;> simp [label,z,rep,e,rep_e]
  rw [hlabel,←sign_which]
  obtain ⟨a,ha,u,hu,ez⟩ := orbit_rep hZ
  let k := which z
  let F (h : H4) := if prod (bar (rep s)) (prod h (rep k))∈orderUnits then 1 else 0
  have he (h : H4) : indicator (rep s) (prod h x) (rep t)=F (prod h a) := by
    unfold indicator F
    have hh : prod (prod (bar (rep s)) (prod h x)) (rep t) = prod (prod (bar (rep s)) (prod (prod h a) (rep k))) u := by
      calc _ = prod (bar (rep s)) (prod h z) := by simp only [z,hmul_assoc]
           _ = _ := by rw [←ez]; simp only [hmul_assoc,k]
    simp only [hh,(coset_action u hu _).2]
  simp_rw [he]
  rw [global_right ha]
  change (∑ h∈globalUnits,if prod (bar (rep s)) (prod h (rep k))∈orderUnits then 1 else 0)=if sign k=sign s then 2 else 0
  cases s <;> cases k <;> decide +kernel
theorem raw_eq {m : ℕ} (hm : Odd m) {s t : H4} (hs : s∈units) (ht : t∈units) :
    (raw m s t:ℚ)=2*entry m (which t) (which s) := by
  rw [raw_reps hm hs ht]
  let i := which s
  let j := which t
  have h := calc
    24*raw m (rep i) (rep j)=∑ a∈globalUnits, ∑ q∈normShell m, indicator (rep i) (prod a (modFour q)) (rep j) := by
      have e (a : H4) (ha : a∈globalUnits) : (∑ q∈normShell m, indicator (rep i) (prod a (modFour q)) (rep j))=raw m (rep i) (rep j) := by
        obtain ⟨b,hb,rfl⟩ := (global_iff a).mp ha
        exact (sum_unit hm hb (fun x => indicator (rep i) x (rep j))).1
      rw [sum_congr rfl e,sum_const,global_units_card,nsmul_eq_mul]; norm_num
    _=2*count m j i := by
      rw [sum_comm,count,card_filter,mul_sum]
      apply sum_congr rfl
      intro q hq
      have ho : Odd (nr q) := by rw [(mem_normShell hm q).mp hq]; exact_mod_cast hm
      rw [average_table _ _ _ (odd_units q ho)]; split <;> simp
  change (raw m (rep i) (rep j):ℚ)=2*((count m j i:ℚ)/24)
  have H := congrArg (fun x:ℕ => (x:ℚ)) h
  push_cast at H
  linarith
end
end TunnellBrandtDoubleCoset
namespace TunnellDyadicGluing
open TunnellQuaternion TunnellHurwitzFour TunnellToricSign TunnellToric TunnellShell TunnellToricClass TunnellBrandt TunnellBrandtDoubleCoset
open TunnellTwoProjection TunnellTwoProjectionTransport TunnellHurwitz
noncomputable section
open scoped Classical
def geom (d m : ℕ) (s t : Triple) := ((normShell m).filter fun q => admits d t s (hamZ q)).card
theorem geom_entry {d m : ℕ} (hd : d%4=1) (hm : Odd m) {v s t : Triple} (hv : v∈shell (2*d))
    (hs : s∈shell (2*d)) (ht : t∈shell (2*d)) (hx : Odd v.1) (hy : v.2.1%4=v.1%4) (hz : 4∣v.2.2)
    {a b : H ℤ} (ha : LocalGenerator v s a) (hb : LocalGenerator v t b) :
    (geom d m s t:ℚ)=2*entry m (which (modFour b)) (which (modFour a)) := by
  have h : geom d m s t=raw m (modFour a) (modFour b) := by
    rw [geom,Finset.card_filter,raw]
    apply Finset.sum_congr rfl
    intro q hq
    have ho : Odd (nr q) := by rw [(mem_normShell hm q).mp hq]; exact_mod_cast hm
    have e := pair_criterion hd hv hs ht hx hy hz ha hb ho
    simp only [modFour_mul,red_bar] at e
    simp only [indicator,e]
  rw [h,raw_eq hm (odd_units a ha.1) (odd_units b hb.1)]
theorem geom_height (d : ℕ) (hsq : Squarefree d) (hd : d%4=1) {m : ℕ} (hm : Odd m) :
    (∑ a : ↥(representatives (2*d)), ∑ b : ↥(representatives (2*d)), (geom d m a.val b.val:ℚ)) =
    (Fintype.card ↥(representatives (2*d)):ℚ)^2*(∑ k∈m.divisors,(k:ℚ))+
      (TunnellShell.b d:ℚ)^2*(etaCoeff m:ℚ) := by
  obtain ⟨t,ht⟩ := TunnellThreeSquares.shell_nonempty d hd
  obtain ⟨v,hv,hx,hy,hz⟩ := aligned_base (show (2*d)%8=2 by omega) ht
  have hco : Nat.Coprime 2 d := Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
  have hs : Squarefree (2*d) := (Nat.squarefree_mul hco).mpr ⟨Nat.prime_two.squarefree,hsq⟩
  have h₂ : (2*d)%4=2 := by omega
  have H (a : ↥(representatives (2*d))) := local_generator_exists h₂ hv (Finset.mem_filter.mp a.property).1
  choose g hg using H
  let c (a : ↥(representatives (2*d))) := which (modFour (g a))
  have he (a b : ↥(representatives (2*d))) : (geom d m a.val b.val:ℚ)=2*entry m (c b) (c a) :=
    geom_entry hd hm hv (Finset.mem_filter.mp a.property).1 (Finset.mem_filter.mp b.property).1 hx hy hz (hg a) (hg b)
  have hc (a : ↥(representatives (2*d))) : sign (c a)=color (redVec v)*test a.val := by
    have ho := character_of_intertwiner hx hy hz (hg a).1 (hg a).2
    rw [sign_rep a.property] at ho
    change sign (which _)=_
    rw [sign_which,ho]
    linear_combination -character (modFour (g a))*(aligned_sign hx hy hz)
  have HP : (∑ a,sign (c a))^2=(TunnellShell.b d)^2 := by
    simp_rw [hc]
    rw [←Finset.mul_sum,show (∑ a : ↥(representatives (2*d)),test a.val)=TunnellShell.b d from
      sum_class_representatives (d:=d) (Equiv.refl _),mul_pow,aligned_sign hx hy hz,one_mul]
  have H := congrArg (fun x:ℤ => (x:ℚ)) HP
  push_cast at H
  simp_rw [he]
  rw [Finset.sum_comm]; simp only [←Finset.mul_sum]
  rw [cm_height hm c,H]
end
end TunnellDyadicGluing
end


/- TunnellGeometricCoefficient -/
section
namespace TunnellGeometricCoefficient
open TunnellShell TunnellHurwitz TunnellToricClass TunnellToricLocal TunnellEmbeddedIdeals
open TunnellIdealHNF TunnellPairComponents TunnellIdealGluings TunnellBinaryPairModel TunnellFrameNorm
open TunnellGlueIsometry TunnellClassThetaCount TunnellRamifiedSwitch TunnellFilteredGlue TunnellGlueMaximal TunnellRamifiedClasses
open TunnellGlueNorms TunnellIntegralPacket TunnellGeometricPacket TunnellTwoProjection TunnellDyadicGluing
open TunnellBrandt TunnellHurwitzFour TunnellRamifiedTwoOrder TunnellToric
noncomputable section
def HShell (d m : ℕ) (s t : Triple) := {q : Q // q∈O ∧ admits d s t q ∧ Quaternion.normSq q=(m:ℚ)}
lemma geom_card {d m : ℕ} (hm : Odd m) (s t : Triple) : Nat.card (HShell d m s t)=geom d m t s := by
  classical
  let F := (normShell m).filter fun q => admits d s t (hamZ q)
  let f (x : ↥F) : HShell d m s t := ⟨hamZ x.val,⟨x.val,rfl⟩,(Finset.mem_filter.mp x.property).2,
    by rw [norm_ham,(mem_normShell hm _).mp (Finset.mem_filter.mp x.property).1]; simp⟩
  have hI : Function.Injective f := by intro x y e; apply Subtype.ext; exact ham_injective (congrArg Subtype.val e)
  have hS : Function.Surjective f := by
    rintro ⟨q,⟨x,rfl⟩,ha,hN⟩
    rw [norm_ham] at hN
    exact ⟨⟨x,Finset.mem_filter.mpr ⟨(mem_normShell hm x).mpr (by exact_mod_cast hN),ha⟩⟩,rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hI,hS⟩)).symm.trans (Nat.card_eq_finsetCard F)
variable {M : Type*} [AddCommGroup M]
def SubShell (d m : ℕ) (X : AddSubgroup M) (V : M→ℤ) := {x:M // x∈X ∧ V x=(d:ℤ)^2*m}
lemma shell_bij (d m : ℕ) (hd : d≠0) (N : ℚ) (hN : N≠0)
    (e : M→+ Q) (hi : Function.Injective e) (V : M→ℤ) (hn : ∀ x, Quaternion.normSq (e x)=N*(V x:ℚ)) {s t : Triple}
    {D L : Lattice} (eL : e.range.toIntSubmodule=L) {b c : Q} (hb : b≠0) (hc : c≠0)
    (hnr : Quaternion.normSq b*Quaternion.normSq c=N) (hD : D=transport b c O) (hL : L=transport b c (pairL s t)) :
    Nonempty (SubShell d m (numerator d e D) V ≃ HShell d m s t) := by
  classical
  have hd' : (d:ℚ)^2≠0 := pow_ne_zero _ (by exact_mod_cast hd)
  have same {x : M} {q:Q} (eq : (d:Q)*action b c q=e x) : V x=(d:ℤ)^2*m ↔ Quaternion.normSq q=(m:ℚ) := by
    have he := congrArg Quaternion.normSq eq
    have hdQ : Quaternion.normSq (d:Q)=(d:ℚ)^2 := by simpa only [Quaternion.coe_natCast] using Quaternion.normSq_coe (d:ℚ)
    rw [map_mul,act_norm b c _ hnr,hdQ,hn] at he
    have e' : (d:ℚ)^2*Quaternion.normSq q=(V x:ℚ) := by apply mul_left_cancel₀ hN; linear_combination he
    constructor
    · intro h; rw [h] at e'; push_cast at e'; exact mul_left_cancel₀ hd' e'
    · intro h; rw [h] at e'; exact_mod_cast e'.symm
  have F (x : SubShell d m (numerator d e D) V) : ∃ q : HShell d m s t, (d:Q)*action b c q.val=e x.val := by
    obtain ⟨w,hw,ew⟩ := (mem_num d e D x.val).mp x.property.1
    obtain ⟨y,hy,rfl⟩ := mem_transport.mp (hD ▸ hw)
    have hz : (d:Q)*action b c y∈L := ew ▸ (eL ▸ (show e x.val∈e.range.toIntSubmodule from ⟨x.val,rfl⟩))
    rw [hL,action_nat,action_mem hb hc] at hz
    exact ⟨⟨y,hy,(admits_mem ..).mpr hz,(same ew).mp x.property.2⟩,ew⟩
  choose f hf using F
  have fi : Function.Injective f := by
    intro x y he; apply Subtype.ext; apply hi; rw [←hf x,←hf y,he]
  have fs : Function.Surjective f := by
    intro q
    have hq : (d:Q)*action b c q.val∈L := by rw [hL,action_nat,action_mem hb hc]; exact (admits_mem ..).mp q.property.2.1
    obtain ⟨x,ex⟩ : ∃ x, e x=(d:Q)*action b c q.val := by rw [←eL] at hq; exact hq
    have hqD : action b c q.val∈D := hD ▸ (action_mem hb hc O q.val).mpr q.property.1
    let X : SubShell d m (numerator d e D) V := ⟨x,(mem_num d e D x).mpr ⟨_,hqD,ex.symm⟩,(same ex.symm).mpr q.property.2.2⟩
    refine ⟨X,Subtype.ext (action_inj hb hc (mul_left_cancel₀ (nat_nonzero hd) ((hf X).trans ex)))⟩
  exact ⟨Equiv.ofBijective f ⟨fi,fs⟩⟩
theorem coeff {d m : ℕ} (hm : Odd m) (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {v : Triple} (hv : v∈shell (2*d))
    {A B C₀ : Ideal (R (2*d))} (hA : A≠⊥) (hB : B≠⊥) (hC : C₀≠⊥) {u : Q} (hu : u∈J (-v) v) (hu0 : u≠0)
    (ec : image hv C₀=line u*J v (-v)) (r : ↥d.divisors) :
    let hA' := mul_ne_bot (by omega : 0<2*d) hA (ram_ne_bot (2*d) r.val)
    let hB' := mul_ne_bot (by omega : 0<2*d) hB (ram_ne_bot (2*d) r.val)
    Nat.card (SubShell d m (gluing hv u A B C₀ r) value)=geom d m (TunnellGlueIsometry.rep hv hn h2 hB').val (TunnellGlueIsometry.rep hv hn h2 hA').val := by
  classical
  obtain ⟨hr,h₀⟩ := Nat.mem_divisors.mp r.property
  obtain ⟨b,c,hb,hc,hNr,hD,hL⟩ := frames hv hn h2 hA hB (Nat.pos_of_dvd_of_pos hr (by omega)) (hr.trans (dvd_mul_left ..))
  have hi := injective hv hn (by omega) (by simpa [pure_neg] using hu.2) hu0 (plusI B A) (minusI B A C₀)
  have N : (normI B:ℚ)*normI A≠0 := mul_ne_zero (by exact_mod_cast (normI_positive (by omega) B hB).ne') (by exact_mod_cast (normI_positive (by omega) A hA).ne')
  obtain ⟨E⟩ := shell_bij d m (by omega) _ N _ hi _ (eval_norm hv hn h2 hA hB hC hu hu0 ec) (range_eq hv hn h2 (by simpa [pure_neg] using hu.2) hu0 ec B A) hb hc hNr hD hL
  exact (Nat.card_congr E).trans (geom_card hm _ _)
end
end TunnellGeometricCoefficient
end


/- TunnellRamifiedFrameFiber -/
section
namespace TunnellRamifiedFrameFiber
open TunnellIdealHNF TunnellToricClass TunnellToric TunnellShell TunnellRamifiedClasses TunnellProperClassGroup
open TunnellPrincipalGenus TunnellSwitchComponents TunnellComponentFibers TunnellBinaryPairModel TunnellClassThetaCount
noncomputable section
variable {G : Type*} [CommGroup G]
def pairMap (C : G) (a : G×G) := (a.2/a.1,C/(a.1*a.2))
def pairFiber (C : G) (a : G×G) :
    (powMonoidHom (α:=G) 2).ker ≃ {b : G×G // pairMap C b=pairMap C a} := by
  let f (k : (powMonoidHom (α:=G) 2).ker) := (a.1*k.val,a.2*k.val)
  have h (k : (powMonoidHom (α:=G) 2).ker) : pairMap C (f k)=pairMap C a := by
    have hh : k.val^2=1 := k.property
    apply Prod.ext
    · change (a.2*k.val)/(a.1*k.val)=a.2/a.1; simp
    · change C/((a.1*k.val)*(a.2*k.val))=C/(a.1*a.2)
      rw [show (a.1*k.val)*(a.2*k.val)=(a.1*a.2)*k.val^2 by rw [pow_two]; ac_rfl,hh,mul_one]
  refine Equiv.ofBijective (fun k => ⟨f k,h k⟩) ⟨?_,?_⟩
  · intro k l e
    exact Subtype.ext (mul_left_cancel (congrArg (fun x : {b : G×G // _} => x.val.1) e))
  · rintro ⟨b,e⟩
    have e₁ := congrArg Prod.fst e; have e₂ := congrArg Prod.snd e
    change b.2/b.1=a.2/a.1 at e₁
    change C/(b.1*b.2)=C/(a.1*a.2) at e₂
    have hb : b.1*b.2=a.1*a.2 := div_right_inj.mp e₂
    let k := b.1/a.1
    have h₁ : a.1*k=b.1 := by simp [k]
    have h₂ : a.2*k=b.2 := by
      change a.2*(b.1/a.1)=b.2
      calc _=(a.2/a.1)*b.1 := by simp only [div_eq_mul_inv]; ac_rfl
           _=_ := by rw [←e₁,div_mul_cancel]
    have hk : k^2=1 := by
      apply mul_left_cancel (a:=a.1*a.2)
      calc (a.1*a.2)*k^2=(a.1*k)*(a.2*k) := by rw [pow_two]; ac_rfl
           _=_ := by rw [h₁,h₂,hb,mul_one]
    exact ⟨⟨k,hk⟩,Subtype.ext (Prod.ext h₁ h₂)⟩
variable {d : ℕ} (hs : Squarefree d) (hn : Squarefree (2*d)) (hd : d%4=1) (h2 : (2*d)%4=2) {v : Triple} (hv : v∈shell (2*d))
def ramK (a : ↥d.divisors) : letI := group hn h2 hv
    (powMonoidHom (α:=ProperIdealClass v) 2).ker := by
  letI := group hn h2 hv
  refine ⟨cls hn h2 hv (ram_ne_bot _ a.val),?_⟩
  have ⟨ha,h0⟩ := Nat.mem_divisors.mp a.property
  have h := ram_square hn h2 (Nat.pos_of_dvd_of_pos ha (Nat.pos_of_ne_zero h0)) (ha.trans (dvd_mul_left ..))
  change (cls hn h2 hv (ram_ne_bot _ a.val))^2=1
  rw [pow_two]
  change mul hn h2 hv _ _=one hn h2 hv
  have hne : (a.val:R (2*d))≠0 := Nat.cast_ne_zero.mpr (Nat.pos_of_dvd_of_pos ha (Nat.pos_of_ne_zero h0)).ne'
  rw [cls_mul]; exact (cls_congr hn h2 hv h).trans (cls_principal hn h2 hv hne (by rw [←h]; exact mul_ne_bot (by omega) (ram_ne_bot _ _) (ram_ne_bot _ _)))
def ambigEquiv (hs : Squarefree d) (hd : d%4=1) : letI := group hn h2 hv
    ↥d.divisors ≃ (powMonoidHom (α:=ProperIdealClass v) 2).ker := by
  letI := group hn h2 hv
  classical
  letI := Fintype.ofEquiv ↥(representatives (2*d)) (idealEquiv hn h2 hv).symm
  have ho : Function.Surjective (ramK hn hd h2 hv) := by
    rintro ⟨c,hc⟩; change c^2=1 at hc; rw [pow_two] at hc
    obtain ⟨a,ha,e⟩ := ram_classes_cover hn h2 hv c (eq_inv_of_mul_eq_one_left hc).symm
    exact ⟨⟨a,ha⟩,Subtype.ext e.symm⟩
  have hcard : Fintype.card ↥d.divisors=Fintype.card (powMonoidHom (α:=ProperIdealClass v) 2).ker := by
    rw [Fintype.card_coe,divisor_card hs,←Nat.card_eq_fintype_card,(principal_genus hs hn hd h2 hv).2]
  exact Equiv.ofBijective (ramK hn hd h2 hv) ((Fintype.bijective_iff_surjective_and_card _).mpr ⟨ho,hcard⟩)
def frameEquiv (hs : Squarefree d) (hd : d%4=1) (C : ProperIdealClass v) (a : ProperIdealClass v×ProperIdealClass v) : letI := group hn h2 hv
    ↥d.divisors ≃ {b : ProperIdealClass v×ProperIdealClass v // pairMap C b=pairMap C a} := by
  letI := group hn h2 hv
  exact (ambigEquiv hn h2 hv hs hd).trans (pairFiber C a)
theorem frame_apply (C : ProperIdealClass v) (a : ProperIdealClass v×ProperIdealClass v) (r : ↥d.divisors) : letI := group hn h2 hv
    (frameEquiv hn h2 hv hs hd C a r).val=(a.1*cls hn h2 hv (ram_ne_bot _ r.val),a.2*cls hn h2 hv (ram_ne_bot _ r.val)) := by
  letI := group hn h2 hv; rfl
theorem classes {A B C : Ideal (R (2*d))} (hA : A≠⊥) (hB : B≠⊥) (hC : C≠⊥) : letI := group hn h2 hv
    pairMap (cls hn h2 hv hC) (cls hn h2 hv hA,cls hn h2 hv hB)=
      (cls hn h2 hv (mul_ne_bot (by omega) hB (conj_ne_bot hA)),cls hn h2 hv (mul_ne_bot (by omega) (mul_ne_bot (by omega) (conj_ne_bot hB) hC) (conj_ne_bot hA))) := by
  letI := group hn h2 hv
  have hm {I J : Ideal (R (2*d))} (hI : I≠⊥) (hJ : J≠⊥) : cls hn h2 hv hI*cls hn h2 hv hJ=cls hn h2 hv (mul_ne_bot (by omega) hI hJ) := cls_mul hn h2 hv hI hJ
  apply Prod.ext
  · change cls hn h2 hv hB/cls hn h2 hv hA=_
    rw [div_eq_mul_inv,inv_cls,hm]
  · change cls hn h2 hv hC/(cls hn h2 hv hA*cls hn h2 hv hB)=_
    rw [div_eq_mul_inv,mul_inv_rev,inv_cls,inv_cls]
    calc _=(cls hn h2 hv (conj_ne_bot hB)*cls hn h2 hv hC)*cls hn h2 hv (conj_ne_bot hA) := by ac_rfl
         _=_ := by rw [hm,hm]
end
end TunnellRamifiedFrameFiber
end


/- TunnellLineCoefficient -/
section
namespace TunnellLineCoefficient
open TunnellIdealHNF TunnellIdealFormBasis TunnellOddGlueCoordinates TunnellRamifiedLines TunnellGluePacket TunnellIntegralPacket
open TunnellGeometricPacket TunnellGeometricCoefficient TunnellShell TunnellHurwitz TunnellToricClass TunnellToricLocal
open TunnellBinaryPairModel TunnellClassThetaCount TunnellEmbeddedIdeals TunnellRamifiedClasses TunnellGlueIsometry
open TunnellRamifiedFrameFiber TunnellDyadicGluing TunnellToric TunnellProperClassGroup
open scoped Classical
noncomputable section
variable {d : ℕ} {I J : Ideal (R (2*d))}
private instance prime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
variable (U : (i : P d) → LocalBasis i.val I) (V : (i : P d) → LocalBasis i.val J)
def lineShell (m : ℕ) (r : (i : P d) → ZMod i.val) :=
  {x : I×J // good U V x ∧ packet U V x∈linePacket r ∧ value x=(d:ℤ)^2*m}
lemma recovered (hs : Squarefree d) (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥) (hJ : J≠⊥) (hodd : Odd d)
    (X : AddSubgroup (I×J)) (hD : ∀ y : I×J, (d:ℤ) • y∈X) (hN : ∀ x∈X, (d:ℤ)^2∣value x)
    (r : (i : P d) → ZMod i.val) (he : X.map (packet U V)=linePacket r) (x : I×J) :
    x∈X ↔ good U V x ∧ packet U V x∈linePacket r := by
  have hgood x hx := valid U V hn h2 hI hJ hodd X hD hN (x:=x) hx
  constructor
  · intro hx; exact ⟨hgood x hx,he ▸ (show packet U V x∈X.map (packet U V) from ⟨x,hx,rfl⟩)⟩
  · rintro ⟨hg,hx⟩; rw [←he] at hx
    obtain ⟨y,hy,ey⟩ := hx
    have hδ (i : P d) := (Nat.dvd_of_mem_primeFactors i.property).trans (dvd_mul_left d 2)
    have H (i : P d) := congrFun ey i
    obtain ⟨u,eu⟩ := ideal_dvd hs (by omega) hI (x:=x.1-y.1) (fun i => (no_coordinate (hδ i) (U i) (admissible_sub _ (hg i).1 (hgood y hy i).1)).mp (by rw [map_sub]; exact sub_eq_zero.mpr (congrArg Prod.fst (H i)).symm))
    obtain ⟨v,ev⟩ := ideal_dvd hs (by omega) hJ (x:=x.2-y.2) (fun i => (no_coordinate (hδ i) (V i) (admissible_sub _ (hg i).2 (hgood y hy i).2)).mp (by rw [map_sub]; exact sub_eq_zero.mpr (congrArg Prod.snd (H i)).symm))
    have e : x-y=(d:ℤ) • (u,v) := Prod.ext eu ev
    have hxy : x-y∈X := e ▸ hD (u,v)
    simpa only [sub_add_cancel] using X.add_mem hxy hy
variable {v : Triple} (hv : v∈shell (2*d))
lemma rep_cls (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {I : Ideal (R (2*d))} (hI : I≠⊥) :
    TunnellGlueIsometry.rep hv hn h2 hI=idealEquiv hn h2 hv (cls hn h2 hv hI) := rfl
theorem odd_coefficient {m : ℕ} (hm : Odd m) (hs : Squarefree d) (hn : Squarefree (2*d)) (hd : d%4=1) (h2 : (2*d)%4=2)
    {A B C₀ : Ideal (R (2*d))} (hA : A≠⊥) (hB : B≠⊥) (hC : C₀≠⊥) {u : Q} (hu : u∈TunnellToricClass.J (-v) v) (hu0 : u≠0)
    (ec : image hv C₀=line u*TunnellToricClass.J v (-v))
    (U : (i : P d) → LocalBasis i.val (plusI B A)) (V : (i : P d) → LocalBasis i.val (minusI B A C₀)) :
    letI := group hn h2 hv
    letI := TunnellFullClassTheta.classFintype hn h2 hv
    let a := (cls hn h2 hv hA,cls hn h2 hv hB)
    let C := cls hn h2 hv hC
    ∃ z : (i : P d) → ZMod i.val, (∀ i, z i^2=parameter U V i) ∧
      ∑ e : P d→Bool, Nat.card (lineShell U V m (TunnellAllRamifiedLines.signed z e)) =
      ∑ q : {b : ProperIdealClass v×ProperIdealClass v // pairMap C b=pairMap C a},
        geom d m (idealEquiv hn h2 hv q.val.2).val (idealEquiv hn h2 hv q.val.1).val := by
  classical
  letI := group hn h2 hv
  letI := TunnellFullClassTheta.classFintype hn h2 hv
  let a := (cls hn h2 hv hA,cls hn h2 hv hB)
  let C := cls hn h2 hv hC
  let X := gluing hv u A B C₀
  have hodd : Odd d := Nat.odd_iff.mpr (by omega)
  obtain ⟨_,hD,hN,_⟩ := properties hv hs hn h2 hodd hA hB hC hu hu0 ec
  obtain ⟨z,hz,E,he⟩ := geometric hv hs hn h2 hodd hA hB hC hu hu0 ec U V
  let F := frameEquiv hn h2 hv hs hd C a
  have hI : plusI B A≠⊥ := mul_ne_bot (by omega) hB (conj_ne_bot hA)
  have hJ : minusI B A C₀≠⊥ := mul_ne_bot (by omega) (mul_ne_bot (by omega) (conj_ne_bot hB) hC) (conj_ne_bot hA)
  have hm' (r : ↥d.divisors) := recovered U V hs hn h2 hI hJ hodd (X r) (hD r) (hN r) _ (he r)
  let f (e : P d→Bool) := Nat.card (lineShell U V m (TunnellAllRamifiedLines.signed z e))
  let g (q : {b : ProperIdealClass v×ProperIdealClass v // pairMap C b=pairMap C a}) := geom d m (idealEquiv hn h2 hv q.val.2).val (idealEquiv hn h2 hv q.val.1).val
  refine ⟨z,hz,?_⟩; change ∑ e, f e=∑ q, g q
  rw [←E.sum_comp f,←F.sum_comp g]
  apply Finset.sum_congr rfl; intro r _
  have eq : f (E r)=Nat.card (SubShell d m (X r) value) := by
    apply Nat.card_congr
    apply Equiv.subtypeEquivRight
    intro x; change (good U V x ∧ _ ∧ _) ↔ _ ∧ _
    rw [hm' r x]; exact and_assoc.symm
  rw [eq,show Nat.card (SubShell d m (X r) value)=_ from coeff hm hn h2 hv hA hB hC hu hu0 ec r]
  change _=geom d m (idealEquiv hn h2 hv (F r).val.2).val (idealEquiv hn h2 hv (F r).val.1).val
  have ef := frame_apply hs hn hd h2 hv C a r
  change (F r).val=(cls hn h2 hv hA*cls hn h2 hv (ram_ne_bot _ r.val),cls hn h2 hv hB*cls hn h2 hv (ram_ne_bot _ r.val)) at ef
  have hm {I : Ideal (R (2*d))} (hI : I≠⊥) : cls hn h2 hv hI*cls hn h2 hv (ram_ne_bot _ r.val)=cls hn h2 hv (mul_ne_bot (by omega) hI (ram_ne_bot _ r.val)) := cls_mul hn h2 hv hI (ram_ne_bot _ r.val)
  rw [ef,rep_cls,rep_cls]; dsimp only; rw [hm,hm]
end
end TunnellLineCoefficient
end


/- TunnellUniformBasis -/
section
namespace TunnellUniformBasis
open TunnellIdealHNF TunnellIdealFormBasis TunnellOddDiscriminant TunnellRamifiedLines TunnellIdealThetaExpansion TunnellGenusCharacter
noncomputable section
variable {d : ℕ}
private instance prime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
structure Basis (d : ℕ) (I : Ideal (R (2*d))) where
  a : ℕ
  b : ℤ
  c : ℤ
  pos : 0<a
  cop : a.Coprime d
  det : (a:ℤ)*c-b^2=2*d
  basis : (ℤ×ℤ) ≃+ I
  norm : ∀ x, (basis x).val.norm=(normI I:ℤ)*quad (a:ℤ) b c x
def shear (t : ℤ) : (ℤ×ℤ) ≃+ (ℤ×ℤ) where
  toFun x := (x.1,t*x.1+x.2)
  invFun x := (x.1,x.2-t*x.1)
  left_inv x := Prod.ext rfl (by dsimp; ring)
  right_inv x := Prod.ext rfl (by dsimp; ring)
  map_add' x y := Prod.ext rfl (by dsimp; ring)
theorem exists_basis (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {I : Ideal (R (2*d))} (hI : I≠⊥) : Nonempty (Basis d I) := by
  classical
  obtain ⟨s,rfl⟩ := normal_form (by omega) hI
  obtain ⟨C,hC⟩ := s.divides
  let A : ℤ := s.a; let B : ℤ := s.b
  have det : A*C-B^2=2*d := by dsimp [A,B]; push_cast at hC; linear_combination -hC
  have hpr := primitive_coeffs hn h2 s hC
  let ε (i : P d) : ZMod i.val := if (A:ZMod i.val)=0 then 1 else 0
  obtain ⟨t,ht⟩ := selector ε
  let K : ℤ := A+2*B*t+C*(t:ℤ)^2
  let L : ℤ := B+C*t
  have hunit (i : P d) : (K:ZMod i.val)≠0 := by
    have hi := Nat.dvd_of_mem_primeFactors i.property
    have hmod : (2:ZMod i.val)*d=0 := by rw [(ZMod.natCast_eq_zero_iff _ _).mpr hi,mul_zero]
    have he := congrArg (fun z:ℤ => (z:ZMod i.val)) det; push_cast at he
    rw [hmod] at he
    dsimp only [K]; push_cast; rw [ht]
    by_cases hA : (A:ZMod i.val)=0
    · have hB : (B:ZMod i.val)=0 := by rw [hA,zero_mul,zero_sub,neg_eq_zero] at he; exact sq_eq_zero_iff.mp he
      have hCu : (C:ZMod i.val)≠0 := by
        rintro hz; obtain ⟨u,v,w,e⟩ := hpr
        have hh := congrArg (fun z:ℤ => (z:ZMod i.val)) e
        push_cast at hh; have hA' : (s.a:ZMod i.val)=0 := by simpa only [A,Int.cast_natCast] using hA
        have hB' : (s.b:ZMod i.val)=0 := by simpa only [B,Int.cast_natCast] using hB
        simp [hA',hB',hz] at hh
      simpa [ε,hA,hB] using hCu
    · simpa [ε,hA] using hA
  have hA : 0<A := by dsimp [A]; exact_mod_cast s.pos_a
  have hn0 : (0:ℤ)<2*d := by omega
  have hK : 0<K := by
    by_cases ht : t=0
    · simpa [K,ht] using hA
    have hpos := mul_pos hn0 (sq_pos_of_ne_zero (by exact_mod_cast ht : (t:ℤ)≠0))
    have e : A*K=(A+B*t)^2+(2*d:ℤ)*(t:ℤ)^2 := by dsimp only [K]; linear_combination (t:ℤ)^2*det
    exact pos_of_mul_pos_right (e ▸ add_pos_of_nonneg_of_pos (sq_nonneg _) hpos) hA.le
  have hnat : (K.toNat:ℤ)=K := Int.toNat_of_nonneg hK.le
  have cop : K.toNat.Coprime d := by
    apply Nat.coprime_of_dvd; intro p hp ha hd
    let i : P d := ⟨p,Nat.mem_primeFactors.mpr ⟨hp,hd,by omega⟩⟩
    apply hunit i
    have e : ((K.toNat:ℤ):ZMod i.val)=0 := by
      rw [Int.cast_natCast]; exact (ZMod.natCast_eq_zero_iff _ _).mpr ha
    rwa [hnat] at e
  refine ⟨⟨K.toNat,L,C,by omega,cop,?_,(shear t).trans (TunnellIdealFormBasis.basis s),?_⟩⟩
  · rw [hnat]; dsimp only [K,L]; linear_combination det
  · intro x; change ((TunnellIdealFormBasis.basis s) ((shear t) x)).val.norm=_
    rw [basis_norm s C hC,hnat]; congr 1
    dsimp [quad,shear,K,L,A,B]; ring
def Basis.atPrime {I : Ideal (R (2*d))} (L : Basis d I) (i : P d) : LocalBasis i.val I where
  A := L.a
  B := L.b
  C := L.c
  det := by simpa only [Nat.cast_mul,Nat.cast_ofNat] using L.det
  unit := by
    rw [Int.cast_natCast]; intro e
    have hp := (ZMod.natCast_eq_zero_iff _ _).mp e
    exact (prime i).out.not_dvd_one (L.cop ▸ Nat.dvd_gcd hp (Nat.dvd_of_mem_primeFactors i.property))
  basis := L.basis
  norm := L.norm
theorem character {I : Ideal (R (2*d))} (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥) (L : Basis d I) (i : P d) :
    charI (p:=i.val) hn h2 hI=quadraticChar (ZMod i.val) (L.a:ZMod i.val) := by
  let x := L.basis (1,0)
  have he : (valence x:ℤ)=L.a := by
    simpa [x,Basis.atPrime,quad] using TunnellIntegralPacket.chart_value hn h2 hI (L.atPrime i) x
  have hx : (valence x:ZMod i.val)=L.a := by exact_mod_cast congrArg (fun z:ℤ => (z:ZMod i.val)) he
  have hu : (L.a:ZMod i.val)≠0 := by simpa [Basis.atPrime] using (L.atPrime i).unit
  exact (charI_eq hn h2 ((Nat.dvd_of_mem_primeFactors i.property).trans (dvd_mul_left ..)) hI x (hx ▸ hu)).trans (congrArg _ hx)
end
end TunnellUniformBasis
end


/- TunnellTraceChoices -/
section
namespace TunnellTraceChoices
open TunnellIdealHNF TunnellIdealFormBasis TunnellRamifiedLines TunnellGluePacket TunnellIntegralPacket TunnellLineCoefficient
open TunnellAllRamifiedLines TunnellUniformBasis TunnellGeometricPacket TunnellGeometricCoefficient TunnellShell TunnellHurwitz TunnellToricClass TunnellToricLocal
open TunnellBinaryPairModel TunnellClassThetaCount TunnellEmbeddedIdeals TunnellRamifiedClasses TunnellGlueIsometry
open TunnellRamifiedFrameFiber TunnellDyadicGluing TunnellToric TunnellProperClassGroup TunnellGenusMap TunnellPrincipalGenus
open scoped Classical
noncomputable section
variable {d : ℕ}
private instance prime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
def Roots (t : (i : P d) → ZMod i.val) := {z : (i : P d) → ZMod i.val // ∀ i, z i^2=t i}
instance root_fintype (t : (i : P d) → ZMod i.val) : Fintype (Roots t) := inferInstanceAs (Fintype (Subtype _))
def signs (hd : Odd d) (t : (i : P d) → ZMod i.val) (ht : ∀ i, t i≠0) {z : (i : P d) → ZMod i.val} (hz : ∀ i, z i^2=t i) :
    (P d → Bool) ≃ Roots t := by
  classical
  let f (e : P d→Bool) : Roots t := ⟨signed z e,by intro i; dsimp [signed]; split <;> simp [hz]⟩
  have hne (i : P d) : -(z i)≠z i := by
    intro he
    have hh : (2:ZMod i.val)*z i=0 := by rw [two_mul,add_eq_zero_iff_eq_neg]; exact he.symm
    rcases mul_eq_zero.mp hh with h|h
    · have e := (Nat.prime_dvd_prime_iff_eq (prime i).out Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff _ _).mp h)
      have H := Nat.dvd_of_mem_primeFactors i.property; rw [e] at H; exact (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr H)
    · apply ht i; rw [←hz i,h,zero_pow (by decide)]
  apply Equiv.ofBijective f
  constructor
  · intro a b he; funext i
    have h := congrArg (fun w : Roots t => w.val i) he
    change (if a i then -(z i) else z i)=(if b i then -(z i) else z i) at h
    have hh := hne i
    cases ha : a i <;> cases hb : b i <;> simp [ha,hb] at h ⊢ <;> first | exact hh h | exact hh h.symm
  · intro w
    let e (i : P d) := decide (w.val i≠z i)
    refine ⟨e,Subtype.ext (funext fun i => ?_)⟩
    have H := sq_eq_sq_iff_eq_or_eq_neg.mp ((w.property i).trans (hz i).symm)
    rcases H with H|H <;> simp [f,signed,e,H,hne i]
variable {I J : Ideal (R (2*d))}
def weight (U : (i : P d) → LocalBasis i.val I) (V : (i : P d) → LocalBasis i.val J) (m : ℕ) :=
  ∑ r : Roots (parameter U V), Nat.card (lineShell U V m r.val)
lemma weight_eq (hd : Odd d) (U : (i : P d) → LocalBasis i.val I) (V : (i : P d) → LocalBasis i.val J)
    (m : ℕ) {z : (i : P d) → ZMod i.val} (hz : ∀ i, z i^2=parameter U V i) :
    weight U V m=∑ e:P d→Bool, Nat.card (lineShell U V m (signed z e)) := by
  have ht (i : P d) : parameter U V i≠0 := by
    have hu : (2:ZMod i.val)≠0 := by
      intro h; have e := (Nat.prime_dvd_prime_iff_eq (prime i).out Nat.prime_two).mp ((ZMod.natCast_eq_zero_iff _ _).mp h)
      have H := Nat.dvd_of_mem_primeFactors i.property; rw [e] at H; exact (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr H)
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (by simpa only [show (4:ZMod i.val)=2^2 by norm_num] using pow_ne_zero 2 hu)) (V i).unit) (U i).unit
  exact ((signs hd _ ht hz).sum_comp (fun r => Nat.card (lineShell U V m r.val))).symm
lemma inv_sign (u : ℤˣ) : u⁻¹=u := by apply inv_eq_of_mul_eq_one_right; simpa only [←pow_two] using units_sq u
variable (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) {v : Triple} (hv : v∈shell (2*d))
lemma compatible (hs : Squarefree d) (hd : d%4=1) {C : ProperIdealClass v}
    (eC : ∀ i : P d, ((genus hn h2 hv C i:ℤˣ):ℤ)=quadraticChar (ZMod i.val) (-1))
    (hI : I≠⊥) (hJ : J≠⊥) (U : TunnellUniformBasis.Basis d I) (V : TunnellUniformBasis.Basis d J) :
    letI := group hn h2 hv
    Nonempty (Roots (parameter U.atPrime V.atPrime)) → ∃ a : ProperIdealClass v×ProperIdealClass v,
      pairMap C a=(cls hn h2 hv hI,cls hn h2 hv hJ) := by
  letI := group hn h2 hv
  let s := cls hn h2 hv hI; let t := cls hn h2 hv hJ
  let Γ := genus hn h2 hv
  rintro ⟨r⟩
  have hγ : Γ (C/(s*t))=1 := by
    funext i; apply Units.ext
    have hp := Nat.dvd_of_mem_primeFactors i.property
    have hodd : i.val≠2 := by intro e; rw [e] at hp; omega
    let A := ((U.atPrime i).A:ZMod i.val); let D := ((V.atPrime i).A:ZMod i.val)
    have pp := TunnellOddDiscriminant.plane_parameter hn (hp.trans (dvd_mul_left d 2)) hodd (U.atPrime i).unit (V.atPrime i).unit
    have ec := pp.2.2.1
    change quadraticChar (ZMod i.val) (parameter U.atPrime V.atPrime i)=_ at ec
    have hr : IsSquare (parameter U.atPrime V.atPrime i) := ⟨r.val i,by rw [←r.property i,pow_two]⟩
    have et : quadraticChar (ZMod i.val) (parameter U.atPrime V.atPrime i)=1 := (quadraticChar_one_iff_isSquare pp.2.1).mpr hr
    rw [et] at ec
    have hU := TunnellUniformBasis.character hn h2 hI U i; have hV := TunnellUniformBasis.character hn h2 hJ V i
    have hU' : ((Γ s i:ℤˣ):ℤ)=quadraticChar (ZMod i.val) ((U.atPrime i).A:ZMod i.val) := (genus_eval hn h2 hv hI i).trans (by simpa [TunnellUniformBasis.Basis.atPrime] using hU)
    have hV' : ((Γ t i:ℤˣ):ℤ)=quadraticChar (ZMod i.val) ((V.atPrime i).A:ZMod i.val) := (genus_eval hn h2 hv hJ i).trans (by simpa [TunnellUniformBasis.Basis.atPrime] using hV)
    rw [←eC i,←hU',←hV'] at ec
    change ((Γ (C/(s*t)) i:ℤˣ):ℤ)=1
    rw [map_div,map_mul,Pi.div_apply,Pi.mul_apply,div_eq_mul_inv,inv_sign,Units.val_mul,Units.val_mul]; linear_combination -ec
  have he : C/(s*t)∈(powMonoidHom (α:=ProperIdealClass v) 2).range := (principal_genus hs hn hd h2 hv).1 ▸ hγ
  obtain ⟨a,ha⟩ := he; change a^2=C/(s*t) at ha
  refine ⟨(a,s*a),Prod.ext ?_ ?_⟩
  · change s*a/a=s; simp
  · change C/(a*(s*a))=t
    apply (div_eq_iff_eq_mul).mpr
    calc C=(C/(s*t))*(s*t) := (div_mul_cancel ..).symm
         _=t*(a*(s*a)) := by rw [←ha,pow_two]; ac_rfl
end
end TunnellTraceChoices
end


/- TunnellRectangularClasses -/
section
namespace TunnellRectangularClasses
open TunnellIdealHNF TunnellUniformBasis TunnellOddDiscriminant TunnellOddGlueCoordinates TunnellRamifiedLines TunnellGluePacket
open TunnellIntegralPacket
noncomputable section
variable {d : ℕ}
private instance prime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
def reduce (i : P d) : ZMod d →+* ZMod i.val := ZMod.castHom (Nat.dvd_of_mem_primeFactors i.property) _
lemma red_ext (hs : Squarefree d) {r s : ZMod d} (h : ∀ i : P d, reduce i r=reduce i s) : r=s := by
  obtain ⟨a,rfl⟩ := ZMod.intCast_surjective r
  obtain ⟨b,rfl⟩ := ZMod.intCast_surjective s
  apply (ZMod.intCast_eq_intCast_iff_dvd_sub a b d).mpr (int_dvd hs fun i => ?_)
  have hi := h i; rw [map_intCast,map_intCast] at hi
  exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hi
def redEquiv (hs : Squarefree d) : ZMod d ≃ ((i : P d) → ZMod i.val) := by
  apply Equiv.ofBijective (fun s i => reduce i s)
  constructor
  · intro a b h; exact red_ext hs (congrFun h)
  · intro r; obtain ⟨k,hk⟩ := selector r; exact ⟨k,funext fun i => (map_natCast (reduce i) k).trans (hk i)⟩
def selected (a : ℕ) (b : ℤ) (s : ZMod d) (x : ℤ×ℤ) :=
  (x.1:ZMod d)= -(b:ZMod d)*s ∧ (x.2:ZMod d)=(a:ZMod d)*s
lemma selected_iff (hs : Squarefree d) {I : Ideal (R (2*d))} (L : TunnellUniformBasis.Basis d I) (s : ZMod d) (x : I) :
    selected L.a L.b s (L.basis.symm x) ↔ ∀ i : P d, admissible (L.atPrime i) x ∧ coordinate (L.atPrime i) x=reduce i s := by
  let y := L.basis.symm x
  have det (i : P d) : (L.a:ZMod i.val)*(L.c:ZMod i.val)-(L.b:ZMod i.val)^2=0 := by
    have e := congrArg (fun z:ℤ => (z:ZMod i.val)) L.det; push_cast at e; rw [e,(ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mem_primeFactors i.property),mul_zero]
  have unit (i : P d) : (L.a:ZMod i.val)≠0 := by simpa [Basis.atPrime] using (L.atPrime i).unit
  have adm (i : P d) : admissible (L.atPrime i) x ↔ pairing (L.a:ZMod i.val) L.b L.c (redPair y)=0 := by simp [admissible,Basis.atPrime,y]
  have cor (i : P d) : coordinate (L.atPrime i) x=(y.2:ZMod i.val)/(L.a:ZMod i.val) := by simp [coordinate,coord,Basis.atPrime,y]
  constructor
  · rintro ⟨h₁,h₂⟩ i
    have e₁ := congrArg (reduce i) h₁; have e₂ := congrArg (reduce i) h₂
    simp only [map_intCast,map_mul,map_neg,map_natCast] at e₁ e₂
    have e : redPair (p:=i.val) y=(-(L.b:ZMod i.val)*reduce i s,(L.a:ZMod i.val)*reduce i s) := Prod.ext e₁ e₂
    constructor
    · rw [adm]
      exact (radical (unit i) (det i) _).mpr ⟨_,e⟩
    · rw [cor]; change (y.2:ZMod i.val)=_ at e₂; rw [e₂]; field_simp [unit]
  · intro h
    have H (i : P d) : redPair (p:=i.val) y=(-(L.b:ZMod i.val)*reduce i s,(L.a:ZMod i.val)*reduce i s) := by
      have ha := (adm i).mp (h i).1
      obtain ⟨r,hr⟩ := (radical (unit i) (det i) _).mp ha
      have e₂ := congrArg Prod.snd hr; change (y.2:ZMod i.val)=(L.a:ZMod i.val)*r at e₂
      have hc := (h i).2; rw [cor] at hc
      rw [e₂,mul_div_cancel_left₀ _ (unit i)] at hc; rwa [←hc]
    refine ⟨red_ext hs (fun i => ?_),red_ext hs (fun i => ?_)⟩
    · simp only [map_intCast,map_mul,map_neg]; exact congrArg Prod.fst (H i)
    · simp only [map_intCast,map_mul,map_natCast]; exact congrArg Prod.snd (H i)
end
end TunnellRectangularClasses
end


/- TunnellRankOnePacket -/
section
namespace TunnellRankOnePacket
open Complex Finset Real TunnellIdealTheta
open scoped Classical
noncomputable section
def packet (D : ℕ) [NeZero D] (r : ZMod D) (z : ℂ) : ℂ :=
  shift ((r.val:ℂ)/D) ((D:ℂ)*z)
def kernel (D : ℕ) (z : ℂ) (u : ℤ) := Complex.exp (π*I*(u:ℂ)^2*z/D)
lemma packet_hasSum {D : ℕ} [NeZero D] (r : ZMod D) {z : ℂ} (hz : 0<z.im) :
    HasSum (fun l : ℤ => kernel D z (D*l+r.val)) (packet D r z) := by
  have hD : (D:ℂ)≠0 := by exact_mod_cast NeZero.ne D
  have hp : (0:ℝ)<D := Nat.cast_pos.mpr (NeZero.pos D)
  apply (shift_hasSum ((r.val:ℂ)/D) ((D:ℂ)*z) (by simpa [Complex.mul_im] using (mul_pos hp hz))).congr_fun
  intro l
  unfold kernel
  congr 1
  push_cast
  field_simp
lemma class_hasSum {D : ℕ} [NeZero D] (r : ZMod D) {z : ℂ} (hz : 0<z.im) :
    HasSum (fun n : ℤ => if (n:ZMod D)=r then kernel D z n else 0) (packet D r z) := by
  let e (l : ℤ) := (D:ℤ)*l+r.val
  have hD : (D:ℤ)≠0 := by exact_mod_cast NeZero.ne D
  have hi : Function.Injective e := fun a b h => mul_left_cancel₀ hD (add_right_cancel h)
  apply (hi.hasSum_iff ?_).mp
  · apply (packet_hasSum r hz).congr_fun
    intro l
    simp [Function.comp_def,e]
  · intro n hn
    split_ifs with h
    · exfalso
      apply hn
      obtain ⟨l,hl⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (r.val:ℤ) n D).mp (by simpa using h.symm)
      exact ⟨l,by dsimp [e]; omega⟩
    · rfl
end
end TunnellRankOnePacket
end


/- TunnellRectangularIdeal -/
section
namespace TunnellRectangularIdeal
open TunnellRankOnePacket TunnellIdealHNF TunnellUniformBasis TunnellIdealFormBasis TunnellOddDiscriminant
open TunnellClassThetaExpansion TunnellIdealThetaExpansion Finset
open scoped Classical
noncomputable section
lemma offset_sum {D : ℕ} [NeZero D] (r : ℤ) {z : ℂ} (hz : 0<z.im) :
    HasSum (fun l:ℤ => kernel D z ((D:ℤ)*l+r)) (TunnellRankOnePacket.packet D (r:ZMod D) z) := by
  let f (l : ℤ) := (D:ℤ)*l+r
  have hi : Function.Injective f := fun _ _ e => mul_left_cancel₀ (by exact_mod_cast (NeZero.ne D) : (D:ℤ)≠0) (add_right_cancel e)
  have h := class_hasSum (r:ZMod D) hz
  have ht : HasSum (fun l => if ((f l):ZMod D)=(r:ZMod D) then kernel D z (f l) else 0) (TunnellRankOnePacket.packet D (r:ZMod D) z) := by
    apply (hi.hasSum_iff ?_).mpr h
    intro n hn
    split_ifs with e
    · exfalso; apply hn
      obtain ⟨k,hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub r n D).mp e.symm
      exact ⟨k,by dsimp [f]; omega⟩
    · rfl
  simpa [f] using ht
def rect (d a κ : ℕ) [NeZero d] [NeZero a] [NeZero κ] (b s : ℤ) (z : ℂ) :=
  ∑ i : ZMod a,
    TunnellRankOnePacket.packet (2*κ*a) ((2*(κ:ℤ)*b*i.val:ℤ):ZMod (2*κ*a)) z *
    TunnellRankOnePacket.packet (2*κ*a*(2*d)) (((2*(κ:ℤ)*(2*(d:ℤ))*i.val+4*κ*a*s):ℤ):ZMod (2*κ*a*(2*d))) z
def term (d a κ : ℕ) (b s : ℤ) (z : ℂ) (x : ℤ×ℤ) :=
  Complex.exp (2*Real.pi*Complex.I*z*κ*((a*x.1+b*x.2:ℤ)^2+(2*(d:ℂ))*((x.2:ℂ)+(a:ℂ)*s/d)^2)/a)
private lemma product_sum {X Y : Type*} {f : X→ℂ} {g : Y→ℂ} {x y : ℂ} (hf : HasSum f x) (hg : HasSum g y) :
    HasSum (fun z:X×Y => f z.1*g z.2) (x*y) := hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)
set_option maxHeartbeats 600000 in
theorem translated (d a κ : ℕ) [NeZero d] [NeZero a] [NeZero κ] (b s : ℤ) {z : ℂ} (hz : 0<z.im) :
    HasSum (term d a κ b s z) (rect d a κ b s z) := by
  classical
  let weight (i : ZMod a) (x : ℤ×ℤ) := if (x.2:ZMod a)=i then term d a κ b s z x else 0
  unfold rect
  have hterm (i : ZMod a) : HasSum (weight i)
      (TunnellRankOnePacket.packet (2*κ*a) ((2*(κ:ℤ)*b*i.val:ℤ):ZMod (2*κ*a)) z *
      TunnellRankOnePacket.packet (2*κ*a*(2*d)) (((2*(κ:ℤ)*(2*(d:ℤ))*i.val+4*κ*a*s):ℤ):ZMod (2*κ*a*(2*d))) z) := by
    let f (l : ℤ×ℤ) := (l.1-b*l.2,(a:ℤ)*l.2+i.val)
    have hi : Function.Injective f := by
      intro l k e
      have he := congrArg Prod.snd e
      have hk := mul_left_cancel₀ (by exact_mod_cast (NeZero.ne a) : (a:ℤ)≠0) (add_right_cancel he)
      have hr := congrArg Prod.fst e; change l.1-b*l.2=k.1-b*k.2 at hr
      exact Prod.ext (by rw [hk] at hr; exact sub_left_inj.mp hr) hk
    apply (hi.hasSum_iff ?_).mp
    · have h₁ := offset_sum (D:=2*κ*a) (2*(κ:ℤ)*b*i.val) hz
      have h₂ := offset_sum (D:=2*κ*a*(2*d)) (2*(κ:ℤ)*(2*(d:ℤ))*i.val+4*κ*a*s) hz
      have H := product_sum h₁ h₂
      apply H.congr_fun
      rintro ⟨l,k⟩
      simp only [Function.comp_apply,f,weight,Int.cast_add,Int.cast_mul,Int.cast_natCast,ZMod.natCast_self,zero_mul,zero_add,ZMod.natCast_zmod_val,ite_true]
      simp only [term,kernel,←Complex.exp_add]
      congr 1; push_cast
      have ha : (a:ℂ)≠0 := by exact_mod_cast NeZero.ne a
      have hd : (d:ℂ)≠0 := by exact_mod_cast NeZero.ne d
      have hk : (κ:ℂ)≠0 := by exact_mod_cast NeZero.ne κ
      field_simp; ring
    · rintro ⟨x,y⟩ he
      unfold weight
      split_ifs with h
      · exfalso; apply he
        obtain ⟨k,hk⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub (i.val:ℤ) y a).mp (by simpa using h.symm)
        exact ⟨(x+b*k,k),Prod.ext (by dsimp [f]; ring) (by dsimp [f]; omega)⟩
      · rfl
  apply (hasSum_sum (s:=univ) (fun i _ => hterm i)).congr_fun
  intro x; simp [weight]
lemma unshifted {d κ : ℕ} [NeZero d] [NeZero κ] {I : Ideal (R (2*d))} (L : TunnellUniformBasis.Basis d I)
    (hI : I≠⊥) {z : ℂ} (hz : 0<z.im) :
    letI : NeZero L.a := ⟨L.pos.ne'⟩
    rect d L.a κ L.b 0 z=thetaI I ((κ:ℂ)*z) := by
  letI : NeZero L.a := ⟨L.pos.ne'⟩
  have ha : (L.a:ℂ)≠0 := by exact_mod_cast L.pos.ne'
  have hN : (normI I:ℂ)≠0 := by exact_mod_cast (normI_positive (by have h := NeZero.pos d; omega) I hI).ne'
  rw [←(translated d L.a κ L.b 0 hz).tsum_eq,thetaI,←L.basis.toEquiv.tsum_eq (normTerm I ((κ:ℂ)*z))]
  apply tsum_congr; intro x
  unfold term normTerm
  change _=Complex.exp (_*(κ*z)*(↑((L.basis x).val.norm):ℂ)/normI I)
  rw [L.norm]; dsimp [quad]
  congr 1; push_cast; simp only [Int.cast_zero,mul_zero,zero_div,add_zero]
  have he := congrArg (fun v:ℤ => (v:ℂ)) L.det; push_cast at he
  field_simp
  linear_combination -(κ:ℂ)*z*(x.2:ℂ)^2*he
end
end TunnellRectangularIdeal
end


/- TunnellRectangularNumerator -/
section
namespace TunnellRectangularNumerator
open TunnellIdealHNF TunnellUniformBasis TunnellOddDiscriminant TunnellOddGlueCoordinates TunnellRamifiedLines TunnellGluePacket
open TunnellIntegralPacket TunnellRectangularClasses TunnellRectangularIdeal TunnellIdealThetaExpansion TunnellIdealFormBasis
open scoped Classical
noncomputable section
variable {d : ℕ}
def shifted (a : ℕ) (b s : ℤ) (x : ℤ×ℤ) := (-b*s+(d:ℤ)*x.1,(a:ℤ)*s+d*x.2)
lemma injective_shift (hd : d≠0) (a : ℕ) (b s : ℤ) : Function.Injective (shifted (d:=d) a b s) := by
  rintro ⟨w,x⟩ ⟨y,z⟩ he; have h₁ := congrArg Prod.fst he; have h₂ := congrArg Prod.snd he
  have h : (d:ℤ)≠0 := by exact_mod_cast hd
  exact Prod.ext (mul_left_cancel₀ h (add_left_cancel h₁)) (mul_left_cancel₀ h (add_left_cancel h₂))
lemma selected_range (a : ℕ) (b s : ℤ) (x : ℤ×ℤ) :
    selected a b (s:ZMod d) x ↔ x∈Set.range (shifted (d:=d) a b s) := by
  constructor
  · rintro ⟨h₁,h₂⟩
    have e₁ : ((-b*s:ℤ):ZMod d)=x.1 := by push_cast; exact h₁.symm
    have e₂ : (((a:ℤ)*s:ℤ):ZMod d)=x.2 := by push_cast; exact h₂.symm
    obtain ⟨u,hu⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp e₁
    obtain ⟨v,hv⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp e₂
    exact ⟨(u,v),Prod.ext (by dsimp [shifted]; omega) (by dsimp [shifted]; omega)⟩
  · rintro ⟨⟨u,v⟩,rfl⟩; simp [selected,shifted]
def elementTerm {I : Ideal (R (2*d))} (κ : ℕ) (z : ℂ) (x : I) :=
  Complex.exp (2*Real.pi*Complex.I*z*κ*(valence x:ℂ)/(d:ℂ)^2)
lemma term_eq {I : Ideal (R (2*d))} (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥) (L : TunnellUniformBasis.Basis d I)
    (κ : ℕ) (s : ℤ) (z : ℂ) (x : ℤ×ℤ) :
    elementTerm κ z (L.basis (shifted (d:=d) L.a L.b s x))=term d L.a κ L.b s z x := by
  let i := L.basis (shifted (d:=d) L.a L.b s x)
  have he := L.norm (shifted (d:=d) L.a L.b s x)
  rw [TunnellGenusCharacter.norm_valZ hn h2 hI] at he
  have hv : (valence i:ℤ)=quad (L.a:ℤ) L.b L.c (shifted (d:=d) L.a L.b s x) := by
    rw [mul_comm] at he
    exact mul_left_cancel₀ (by exact_mod_cast (normI_positive (by omega) I hI).ne' : (normI I:ℤ)≠0) he
  have hv' := congrArg (fun t:ℤ => (t:ℂ)) hv; simp only [quad,shifted] at hv'; push_cast at hv'
  have det := congrArg (fun t:ℤ => (t:ℂ)) L.det; push_cast at det
  unfold elementTerm term; congr 1
  change 2*Real.pi*Complex.I*z*κ*(valence i:ℂ)/(d:ℂ)^2=_
  rw [hv']; push_cast
  have hd : (d:ℂ)≠0 := by exact_mod_cast (show d≠0 by omega)
  have ha : (L.a:ℂ)≠0 := by exact_mod_cast L.pos.ne'
  field_simp
  linear_combination (κ:ℂ)*z*((L.a:ℂ)*s+d*x.2)^2*det
theorem coset {I : Ideal (R (2*d))} (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥)
    (L : TunnellUniformBasis.Basis d I) (κ : ℕ) [NeZero κ] (s : ZMod d) {z : ℂ} (hz : 0<z.im) :
    letI : NeZero d := ⟨by omega⟩
    letI : NeZero L.a := ⟨L.pos.ne'⟩
    HasSum (fun x : I => if selected L.a L.b s (L.basis.symm x) then elementTerm κ z x else 0) (rect d L.a κ L.b s.val z) := by
  classical
  letI : NeZero d := ⟨by omega⟩
  letI : NeZero L.a := ⟨L.pos.ne'⟩
  apply L.basis.toEquiv.hasSum_iff.mp
  apply ((injective_shift (NeZero.ne d) L.a L.b (s.val:ℤ)).hasSum_iff ?_).mp
  · apply (translated d L.a κ L.b s.val hz).congr_fun
    intro x
    have he : selected L.a L.b s (shifted (d:=d) L.a L.b s.val x) := by
      have H := (selected_range (d:=d) L.a L.b s.val (shifted (d:=d) L.a L.b s.val x)).mpr ⟨x,rfl⟩
      simpa using H
    change (if selected L.a L.b s (L.basis.symm (L.basis (shifted (d:=d) L.a L.b s.val x))) then elementTerm κ z (L.basis (shifted (d:=d) L.a L.b s.val x)) else 0)=_
    rw [L.basis.symm_apply_apply,if_pos he]
    exact term_eq hn h2 hI L κ s.val z x
  · intro x hx; simp only [Function.comp_apply,AddEquiv.coe_toEquiv,AddEquiv.symm_apply_apply]
    apply if_neg; intro he; apply hx; apply (selected_range _ _ _ _).mp
    simpa using he
end
end TunnellRectangularNumerator
end


/- TunnellLineIntegral -/
section
namespace TunnellLineIntegral
open TunnellIdealHNF TunnellUniformBasis TunnellOddDiscriminant TunnellOddGlueCoordinates TunnellRamifiedLines TunnellGluePacket
open TunnellIntegralPacket TunnellRectangularClasses TunnellRectangularNumerator TunnellIdealThetaExpansion TunnellIdealFormBasis TunnellTraceChoices
noncomputable section
variable {d : ℕ} {I J : Ideal (R (2*d))}
private instance prime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
def canonical (hs : Squarefree d) (L : TunnellUniformBasis.Basis d I) (x : I) : ZMod d :=
  (redEquiv hs).symm (fun i => coordinate (L.atPrime i) x)
lemma can_apply (hs : Squarefree d) (L : TunnellUniformBasis.Basis d I) (x : I) (i : P d) :
    reduce i (canonical hs L x)=coordinate (L.atPrime i) x := congrFun ((redEquiv hs).apply_symm_apply _) i
lemma selected_can (hs : Squarefree d) (L : TunnellUniformBasis.Basis d I) (x : I) (s : ZMod d) :
    selected L.a L.b s (L.basis.symm x) ↔ s=canonical hs L x ∧ ∀ i : P d, admissible (L.atPrime i) x := by
  rw [selected_iff hs]; constructor
  · intro h; refine ⟨red_ext hs (fun i => ?_),fun i => (h i).1⟩
    exact ((h i).2).symm.trans (can_apply hs L x i).symm
  · rintro ⟨rfl,h⟩ i; exact ⟨h i,(can_apply hs L x i).symm⟩
lemma shift_value (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥) (L : TunnellUniformBasis.Basis d I)
    (s : ℤ) (w : ℤ×ℤ) :
    (valence (L.basis (shifted (d:=d) L.a L.b s w)):ℤ)=
      (2*(d:ℤ))*L.a*s^2+(d:ℤ)^2*(quad (L.a:ℤ) L.b L.c w+4*s*w.2) := by
  let x := shifted (d:=d) L.a L.b s w
  have h := L.norm x; rw [TunnellGenusCharacter.norm_valZ hn h2 hI,mul_comm] at h
  have e := mul_left_cancel₀ (by exact_mod_cast (normI_positive (by omega) I hI).ne' : (normI I:ℤ)≠0) h
  change (valence (L.basis x):ℤ)=_
  rw [e]; dsimp [shifted,quad,x]; linear_combination ((L.a:ℤ)*s^2+2*(d:ℤ)*s*w.2)*L.det
def aligned (r : (i : P d) → ZMod i.val) (w : ZMod d×ZMod d) := ∀ i:P d, reduce i w.1=r i*reduce i w.2
lemma integral (hs : Squarefree d) (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥) (hJ : J≠⊥)
    (U : TunnellUniformBasis.Basis d I) (V : TunnellUniformBasis.Basis d J) (r : Roots (parameter U.atPrime V.atPrime))
    {x : I×J} (hg : good U.atPrime V.atPrime x) (hl : packet U.atPrime V.atPrime x∈linePacket r.val) :
    (d:ℤ)^2∣value x := by
  letI : NeZero d := ⟨hs.ne_zero⟩
  let s := canonical hs U x.1; let t := canonical hs V x.2
  have hs' : selected U.a U.b ((s.val:ℤ):ZMod d) (U.basis.symm x.1) := by
    rw [Int.cast_natCast,ZMod.natCast_zmod_val,selected_can hs]; exact ⟨rfl,fun i => (hg i).1⟩
  have ht' : selected V.a V.b ((t.val:ℤ):ZMod d) (V.basis.symm x.2) := by
    rw [Int.cast_natCast,ZMod.natCast_zmod_val,selected_can hs]; exact ⟨rfl,fun i => (hg i).2⟩
  obtain ⟨w,ew⟩ := (selected_range ..).mp hs'
  obtain ⟨z,ez⟩ := (selected_range ..).mp ht'
  have e₁ := shift_value hn h2 hI U s.val w; have e₂ := shift_value hn h2 hJ V t.val z
  rw [ew,U.basis.apply_symm_apply] at e₁
  rw [ez,V.basis.apply_symm_apply] at e₂
  have hT : (d:ℤ)∣(U.a:ℤ)*(s.val:ℤ)^2+4*V.a*(t.val:ℤ)^2 := by
    apply int_dvd hs; intro i
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
    have hsl := hl i
    change coordinate (U.atPrime i) x.1=r.val i*coordinate (V.atPrime i) x.2 at hsl
    have es : ((s.val:ℕ):ZMod i.val)=coordinate (U.atPrime i) x.1 := by
      have e : reduce i ((s.val:ℕ):ZMod d)=coordinate (U.atPrime i) x.1 := by rw [ZMod.natCast_zmod_val]; exact can_apply .. 
      rwa [map_natCast] at e
    have et : ((t.val:ℕ):ZMod i.val)=coordinate (V.atPrime i) x.2 := by
      have e : reduce i ((t.val:ℕ):ZMod d)=coordinate (V.atPrime i) x.2 := by rw [ZMod.natCast_zmod_val]; exact can_apply ..
      rwa [map_natCast] at e
    have hU : (U.a:ZMod i.val)≠0 := by simpa [Basis.atPrime] using (U.atPrime i).unit
    have hf : r.val i^2= -(4:ZMod i.val)*V.a/U.a := by simpa [parameter,Basis.atPrime] using r.property i
    push_cast; rw [es,et,hsl,mul_pow,hf]; field_simp; ring
  obtain ⟨k,hk⟩ := hT
  refine ⟨2*k+quad (U.a:ℤ) U.b U.c w+4*s.val*w.2+4*(quad (V.a:ℤ) V.b V.c z+4*t.val*z.2),?_⟩
  unfold value; rw [e₁,e₂]; linear_combination (2*(d:ℤ))*hk
end
end TunnellLineIntegral
end


/- TunnellAnalyticLine -/
section
namespace TunnellAnalyticLine
open TunnellIdealHNF TunnellUniformBasis TunnellRamifiedLines TunnellGluePacket TunnellIntegralPacket
open TunnellRectangularClasses TunnellRectangularNumerator TunnellIdealThetaExpansion TunnellIdealFormBasis TunnellTraceChoices
open TunnellRectangularIdeal TunnellLineIntegral
open scoped Classical
noncomputable section
variable {d : ℕ} {I J : Ideal (R (2*d))}
def theta [NeZero d] (U : TunnellUniformBasis.Basis d I) (V : TunnellUniformBasis.Basis d J) (r : (i : P d) → ZMod i.val) (z : ℂ) :=
  letI : NeZero U.a := ⟨U.pos.ne'⟩
  letI : NeZero V.a := ⟨V.pos.ne'⟩
  ∑ w : ZMod d×ZMod d, if aligned r w then rect d U.a 1 U.b w.1.val z*rect d V.a 4 V.b w.2.val z else 0
def trace [NeZero d] (U : TunnellUniformBasis.Basis d I) (V : TunnellUniformBasis.Basis d J) (z : ℂ) :=
  ∑ r : Roots (parameter U.atPrime V.atPrime), theta U V r.val z
def elem (z : ℂ) (x : I×J) := Complex.exp (2*Real.pi*Complex.I*z*(value x:ℂ)/(d:ℂ)^2)
lemma product_value (x : I×J) (z : ℂ) : elementTerm 1 z x.1*elementTerm 4 z x.2=elem z x := by
  unfold elementTerm elem value
  rw [←Complex.exp_add]
  congr 1; push_cast; ring
def condition (U : TunnellUniformBasis.Basis d I) (V : TunnellUniformBasis.Basis d J) (r : (i : P d) → ZMod i.val) (x : I×J) :=
  good U.atPrime V.atPrime x ∧ packet U.atPrime V.atPrime x∈linePacket r
private lemma product_sum {X Y : Type*} {f : X→ℂ} {g : Y→ℂ} {x y : ℂ} (hf : HasSum f x) (hg : HasSum g y) :
    HasSum (fun z:X×Y => f z.1*g z.2) (x*y) := hf.mul hg (summable_mul_of_summable_norm hf.summable.norm hg.summable.norm)
theorem line_sum [NeZero d] (hs : Squarefree d) (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥) (hJ : J≠⊥)
    (U : TunnellUniformBasis.Basis d I) (V : TunnellUniformBasis.Basis d J) (r : (i : P d) → ZMod i.val) {z : ℂ} (hz : 0<z.im) :
    HasSum (fun x : I×J => if condition U V r x then elem z x else 0) (theta U V r z) := by
  classical
  letI : NeZero U.a := ⟨U.pos.ne'⟩
  letI : NeZero V.a := ⟨V.pos.ne'⟩
  let f (w : ZMod d×ZMod d) (x : I×J) := if aligned r w ∧ selected U.a U.b w.1 (U.basis.symm x.1) ∧ selected V.a V.b w.2 (V.basis.symm x.2) then elem z x else 0
  have HH (w : ZMod d×ZMod d) : HasSum (f w) (if aligned r w then rect d U.a 1 U.b w.1.val z*rect d V.a 4 V.b w.2.val z else 0) := by
    by_cases h : aligned r w
    · rw [if_pos h]
      have hU := coset hn h2 hI U 1 w.1 hz
      have hV := coset hn h2 hJ V 4 w.2 hz
      apply (product_sum hU hV).congr_fun
      intro x
      by_cases H : selected U.a U.b w.1 (U.basis.symm x.1) <;> by_cases H' : selected V.a V.b w.2 (V.basis.symm x.2) <;> simp [f,h,H,H',product_value]
    · simpa only [f,h,false_and,ite_false] using (hasSum_zero (β:=I×J) (α:=ℂ))
  apply (hasSum_sum (s:=Finset.univ) (fun w _ => HH w)).congr_fun
  intro x
  let w := (canonical hs U x.1,canonical hs V x.2)
  have ha : aligned r w ↔ packet U.atPrime V.atPrime x∈linePacket r := by
    change (∀ i, reduce i (canonical hs U x.1)=r i*reduce i (canonical hs V x.2)) ↔ ∀ i, coordinate (U.atPrime i) x.1=r i*coordinate (V.atPrime i) x.2
    simp_rw [can_apply]
  rw [Finset.sum_eq_single w]
  · by_cases h : condition U V r x
    · have h₁ := (selected_can hs U x.1 w.1).mpr ⟨rfl,fun i => (h.1 i).1⟩
      have h₂ := (selected_can hs V x.2 w.2).mpr ⟨rfl,fun i => (h.1 i).2⟩
      simp [f,h,ha.mpr h.2,h₁,h₂]
    · have he : ¬(aligned r w ∧ selected U.a U.b w.1 (U.basis.symm x.1) ∧ selected V.a V.b w.2 (V.basis.symm x.2)) := by
        rintro ⟨ha',hU,hV⟩; apply h; exact ⟨fun i => ⟨((selected_can hs U _ _).mp hU).2 i,((selected_can hs V _ _).mp hV).2 i⟩,ha.mp ha'⟩
      simp [f,h,he]
  · intro t _ ht; apply if_neg
    rintro ⟨_,hU,hV⟩; exact ht (Prod.ext ((selected_can hs U _ _).mp hU).1 ((selected_can hs V _ _).mp hV).1)
  · simp
end
end TunnellAnalyticLine
end


/- TunnellPlaneDensity -/
section
namespace TunnellLineDensity
open TunnellRamifiedPlane Finset
open scoped Classical
noncomputable section
variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
abbrev RootsAt (t : K) (x : K×K) := {r:K // r^2=t ∧ x.1=r*x.2}
def density (t : K) (x : K×K) := Nat.card (RootsAt t x)
end
end TunnellLineDensity
end


/- TunnellLineDensity -/
section
namespace TunnellLineDensity
open TunnellRamifiedPlane TunnellRamifiedLines TunnellTraceChoices TunnellRectangularClasses Finset
open scoped Classical
noncomputable section
variable {d : ℕ}
private instance prime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
def fibers (t : (i : P d) → ZMod i.val) (x : Packet d) :
    {r : Roots t // ∀ i, (x i).1=r.val i*(x i).2} ≃ ((i:P d) → RootsAt (t i) (x i)) where
  toFun r i := ⟨r.val.val i,r.val.property i,r.property i⟩
  invFun r := ⟨⟨fun i => (r i).val,fun i => (r i).property.1⟩,fun i => (r i).property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
theorem factor [NeZero d] (t : (i : P d) → ZMod i.val) (f : ZMod d×ZMod d → ℂ) :
    (∑ r : Roots t, ∑ w : ZMod d×ZMod d, if ∀ i:P d, reduce i w.1=r.val i*reduce i w.2 then f w else 0)=
      ∑ w : ZMod d×ZMod d, (∏ i : P d, (density (t i) (reduce i w.1,reduce i w.2):ℂ))*f w := by
  classical
  rw [sum_comm]; apply sum_congr rfl
  intro w _
  let x (i : P d) := (reduce i w.1,reduce i w.2)
  let R := {r : Roots t // ∀ i, (x i).1=r.val i*(x i).2}
  have e : Nat.card R=∏ i:P d, density (t i) (x i) := by rw [Nat.card_congr (fibers t x),Nat.card_pi]; rfl
  have h : (∑ r : Roots t, if ∀ i:P d, reduce i w.1=r.val i*reduce i w.2 then f w else 0)=(Nat.card R:ℂ)*f w := by
    rw [←sum_filter,sum_const,nsmul_eq_mul]
    congr 1
    rw [Nat.card_eq_fintype_card]; congr 1; exact (Fintype.card_subtype _).symm
  rw [h,e,Nat.cast_prod]
end
end TunnellLineDensity
end


/- TunnellDensityTrace -/
section
namespace TunnellDensityTrace
open TunnellRamifiedLines TunnellRectangularClasses TunnellLineDensity TunnellGluePacket
open TunnellIntegralPacket TunnellAnalyticLine TunnellIdealHNF TunnellUniformBasis TunnellRectangularIdeal
open scoped Classical
noncomputable section
variable {d : ℕ}
private instance prime (i : P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
end
end TunnellDensityTrace
end


/- TunnellOddTraceHeight -/
section
namespace TunnellOddTraceHeight
open TunnellIdealHNF TunnellIdealFormBasis TunnellRamifiedLines TunnellIntegralPacket TunnellLineCoefficient
open TunnellTraceChoices TunnellUniformBasis TunnellShell TunnellHurwitz TunnellToricClass TunnellToricLocal
open TunnellBinaryPairModel TunnellClassThetaCount TunnellEmbeddedIdeals TunnellRamifiedFrameFiber TunnellDyadicGluing
open TunnellToric TunnellProperClassGroup TunnellClassThetaExpansion TunnellIntertwinerTheta TunnellGlueIsometry
open scoped Classical UpperHalfPlane
noncomputable section
variable {d : ℕ} {v : Triple} (hs : Squarefree d) (hn : Squarefree (2*d)) (hd : d%4=1) (h2 : (2*d)%4=2) (hv : v∈shell (2*d))
structure Data (d : ℕ) where
  I : Ideal (TunnellIdealHNF.R (2*d))
  J : Ideal (TunnellIdealHNF.R (2*d))
  hI : I≠⊥
  hJ : J≠⊥
  U : TunnellUniformBasis.Basis d I
  V : TunnellUniformBasis.Basis d J
include hs hd in
lemma per_class (a : (ProperIdealClass v)×(ProperIdealClass v)) {C₀ : Ideal (TunnellIdealHNF.R (2*d))} (hC : C₀≠⊥) {u : Q} (hu : u∈J (-v) v) (hu0 : u≠0) (ec : image hv C₀=line u*J v (-v))
    (eC : ∀ i : P d, letI : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
      ((TunnellGenusMap.genus hn h2 hv (cls hn h2 hv hC) i:ℤˣ):ℤ)=quadraticChar (ZMod i.val) (-1)) :
    letI := group hn h2 hv
    letI := TunnellFullClassTheta.classFintype hn h2 hv
    ∃ D : Data d, (cls hn h2 hv D.hI,cls hn h2 hv D.hJ)=a ∧
      ∀ m : ℕ, Odd m → weight D.U.atPrime D.V.atPrime m=
        ∑ q : {b : (ProperIdealClass v)×(ProperIdealClass v) // pairMap (cls hn h2 hv hC) b=a},
          geom d m (idealEquiv hn h2 hv q.val.2).val (idealEquiv hn h2 hv q.val.1).val := by
  classical
  letI := group hn h2 hv
  letI := TunnellFullClassTheta.classFintype hn h2 hv
  let C := cls hn h2 hv hC
  by_cases H : ∃ b : (ProperIdealClass v)×(ProperIdealClass v), pairMap C b=a
  · obtain ⟨⟨s,t⟩,rfl⟩ := H
    obtain ⟨A,hA,rfl⟩ := TunnellProperClassGroup.exists_rep hn h2 hv s
    obtain ⟨B,hB,rfl⟩ := TunnellProperClassGroup.exists_rep hn h2 hv t
    have hI : plusI B A≠⊥ := mul_ne_bot (by omega) hB (conj_ne_bot hA)
    have hJ : minusI B A C₀≠⊥ := mul_ne_bot (by omega) (mul_ne_bot (by omega) (conj_ne_bot hB) hC) (conj_ne_bot hA)
    obtain ⟨U⟩ := TunnellUniformBasis.exists_basis hn h2 hI
    obtain ⟨V⟩ := TunnellUniformBasis.exists_basis hn h2 hJ
    refine ⟨⟨_,_,hI,hJ,U,V⟩,(classes hn hd h2 hv hA hB hC).symm,?_⟩
    intro m hm
    obtain ⟨z,hz,he⟩ := odd_coefficient hv hm hs hn hd h2 hA hB hC hu hu0 ec U.atPrime V.atPrime
    exact (weight_eq (Nat.odd_iff.mpr (by omega)) U.atPrime V.atPrime m hz).trans he
  · obtain ⟨I,hI,eI⟩ := TunnellProperClassGroup.exists_rep hn h2 hv a.1
    obtain ⟨J,hJ,eJ⟩ := TunnellProperClassGroup.exists_rep hn h2 hv a.2
    obtain ⟨U⟩ := TunnellUniformBasis.exists_basis hn h2 hI
    obtain ⟨V⟩ := TunnellUniformBasis.exists_basis hn h2 hJ
    have hE : IsEmpty (Roots (parameter U.atPrime V.atPrime)) := ⟨fun r => H (by
      obtain ⟨b,hb⟩ := compatible hn h2 hv hs hd eC hI hJ U V ⟨r⟩
      exact ⟨b,hb.trans (Prod.ext eI eJ)⟩)⟩
    have hF : IsEmpty {b : (ProperIdealClass v)×(ProperIdealClass v) // pairMap C b=a} := ⟨fun x => H ⟨x.val,x.property⟩⟩
    letI := hE; letI := hF
    exact ⟨⟨I,J,hI,hJ,U,V⟩,Prod.ext eI eJ,fun m _ => by change weight U.atPrime V.atPrime m=∑ q : {b : (ProperIdealClass v)×(ProperIdealClass v) // pairMap C b=a}, _; simp [TunnellTraceChoices.weight]⟩
lemma theta_class {I : Ideal (TunnellIdealHNF.R (2*d))} (hI : I≠⊥) (z : ℂ) :
    thetaI I z=jtheta v (idealEquiv hn h2 hv (cls hn h2 hv hI)).val z := by
  classical
  obtain ⟨a,ha,h0,e⟩ := representative_frame hn h2 hv ⟨image hv I,image_isIdeal hn h2 hv I hI⟩
  exact frame_theta hn h2 hv (Finset.mem_filter.mp (TunnellGlueIsometry.rep hv hn h2 hI).property).1 hI ha h0 e z
include hs hd in
theorem total :
    letI := group hn h2 hv
    letI := TunnellFullClassTheta.classFintype hn h2 hv
    ∃ D : (ProperIdealClass v)×(ProperIdealClass v) → Data d,
      (∀ z w : ℍ, TunnellFullClassTheta.full hn h2 hv z*TunnellFullClassTheta.full hn h2 hv w=
        ∑ a, thetaI (D a).I z*thetaI (D a).J w) ∧
      ∀ m : ℕ, Odd m →
        (∑ a : (ProperIdealClass v)×(ProperIdealClass v), (weight (D a).U.atPrime (D a).V.atPrime m:ℚ)) =
        (Fintype.card ↥(representatives (2*d)):ℚ)^2*(∑ k∈m.divisors,(k:ℚ))+
          (TunnellShell.b d:ℚ)^2*(TunnellQuaternion.etaCoeff m:ℚ) := by
  classical
  letI := group hn h2 hv
  letI := TunnellFullClassTheta.classFintype hn h2 hv
  let E := idealEquiv hn h2 hv
  obtain ⟨C₀,hC,u,hu0,hu,ec,eC⟩ := TunnellReferenceGenus.reference hn hd h2 hv
  choose D hD hcoef using fun a : (ProperIdealClass v)×(ProperIdealClass v) => per_class hs hn hd h2 hv a hC hu hu0 ec eC
  refine ⟨D,?_,?_⟩
  · intro z w
    have h (a : (ProperIdealClass v)×(ProperIdealClass v)) : thetaI (D a).I z*thetaI (D a).J w=jtheta v (E a.1).val z*jtheta v (E a.2).val w := by
      rw [theta_class hn h2 hv (D a).hI,theta_class hn h2 hv (D a).hJ]
      have h := hD a; rw [show cls hn h2 hv (D a).hI=a.1 from congrArg Prod.fst h,show cls hn h2 hv (D a).hJ=a.2 from congrArg Prod.snd h]
    simp_rw [h]; rw [full_by_embeddings hn h2 hv z,full_by_embeddings hn h2 hv w,←E.sum_comp (fun s => jtheta v s.val z),
      ←E.sum_comp (fun s => jtheta v s.val w),Fintype.sum_prod_type,Finset.sum_mul]
    simp only [Finset.mul_sum]
  · intro m hm
    let f (a : (ProperIdealClass v)×(ProperIdealClass v)) := geom d m (E a.2).val (E a.1).val
    let W := pairMap (cls hn h2 hv hC)
    have he : ∑ a : (ProperIdealClass v)×(ProperIdealClass v), weight (D a).U.atPrime (D a).V.atPrime m=∑ a : (ProperIdealClass v)×(ProperIdealClass v), f a := by
      simp_rw [fun a => hcoef a m hm]
      have H := (Equiv.sigmaFiberEquiv W).sum_comp f
      rw [Fintype.sum_sigma] at H
      exact H
    have eq := congrArg (fun n:ℕ => (n:ℚ)) he
    push_cast at eq
    rw [eq,Fintype.sum_prod_type]
    change (∑ a : (ProperIdealClass v), ∑ b : (ProperIdealClass v), (geom d m (E b).val (E a).val:ℚ))=_
    rw [Finset.sum_comm]
    have h := geom_height d hs hd hm
    rw [←E.sum_comp (fun a => ∑ b : ↥(representatives (2*d)), (geom d m a.val b.val:ℚ))] at h
    refine Eq.trans (Finset.sum_congr rfl fun a _ => E.sum_comp (fun b => (geom d m (E a).val b.val:ℚ))) h
end
end TunnellOddTraceHeight
end


/- TunnellTraceDegree -/
section
namespace TunnellTraceSeries
open TunnellIdealHNF TunnellUniformBasis TunnellRamifiedLines TunnellGluePacket TunnellIntegralPacket TunnellTraceChoices
open TunnellRectangularClasses TunnellRectangularNumerator TunnellIdealThetaExpansion TunnellClassThetaExpansion
open TunnellRectangularIdeal TunnellLineIntegral TunnellAnalyticLine TunnellLineCoefficient
open scoped Classical UpperHalfPlane
noncomputable section
variable {d : ℕ} {I J : Ideal (R (2*d))}
def degree (x : I×J) := (valence x.1+4*valence x.2)/d^2
lemma value_eq (hs : Squarefree d) (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥) (hJ : J≠⊥)
    (U : TunnellUniformBasis.Basis d I) (V : TunnellUniformBasis.Basis d J) (r : Roots (parameter U.atPrime V.atPrime))
    (x : {x:I×J // condition U V r.val x}) : value x.val=(d:ℤ)^2*degree x.val := by
  have h := integral hs hn h2 hI hJ U V r x.property.1 x.property.2
  have hd : d^2∣valence x.val.1+4*valence x.val.2 := by unfold value at h; exact_mod_cast h
  change (valence x.val.1:ℤ)+4*valence x.val.2=_
  exact_mod_cast (Nat.mul_div_cancel' hd).symm
lemma q_degree (hs : Squarefree d) (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥) (hJ : J≠⊥)
    (U : TunnellUniformBasis.Basis d I) (V : TunnellUniformBasis.Basis d J) (r : Roots (parameter U.atPrime V.atPrime))
    (x : {x:I×J // condition U V r.val x}) (z : ℂ) : elem z x.val=(Function.Periodic.qParam 1 z)^degree x.val := by
  unfold elem Function.Periodic.qParam; rw [value_eq hs hn h2 hI hJ U V r x,←Complex.exp_nat_mul]
  congr 1; push_cast
  have hd : (d:ℂ)≠0 := by exact_mod_cast hs.ne_zero
  field_simp <;> ring
end
end TunnellTraceSeries
end


/- TunnellTraceSeries -/
section
namespace TunnellTraceSeries
open TunnellIdealHNF TunnellUniformBasis TunnellRamifiedLines TunnellGluePacket TunnellIntegralPacket TunnellTraceChoices
open TunnellRectangularClasses TunnellRectangularNumerator TunnellIdealThetaExpansion TunnellClassThetaExpansion
open TunnellRectangularIdeal TunnellLineIntegral TunnellAnalyticLine TunnellLineCoefficient
open scoped Classical UpperHalfPlane
noncomputable section
variable {d : ℕ} {I J : Ideal (R (2*d))}
def shell_equiv (hs : Squarefree d) (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥) (hJ : J≠⊥)
    (U : TunnellUniformBasis.Basis d I) (V : TunnellUniformBasis.Basis d J) (r : Roots (parameter U.atPrime V.atPrime)) (m : ℕ) :
    {x : {x : I×J // condition U V r.val x} // degree x.val=m} ≃ lineShell U.atPrime V.atPrime m r.val := by
  let X := {x : I×J // condition U V r.val x}
  let f (x : {x : X // degree x.val=m}) : lineShell U.atPrime V.atPrime m r.val :=
    ⟨x.val.val,x.val.property.1,x.val.property.2,(value_eq hs hn h2 hI hJ U V r x.val).trans (congrArg (fun k:ℕ => (d:ℤ)^2*k) x.property)⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h; apply Subtype.ext; apply Subtype.ext
    exact congrArg (fun z : lineShell U.atPrime V.atPrime m r.val => z.val) h
  · rintro ⟨x,hg,hl,he⟩
    let y : X := ⟨x,hg,hl⟩
    have h := (value_eq hs hn h2 hI hJ U V r y).symm.trans he
    have hd : (d:ℤ)^2≠0 := pow_ne_zero _ (by exact_mod_cast hs.ne_zero)
    exact ⟨⟨y,by exact_mod_cast mul_left_cancel₀ hd h⟩,rfl⟩
theorem line_expansion [NeZero d] (hs : Squarefree d) (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥) (hJ : J≠⊥)
    (U : TunnellUniformBasis.Basis d I) (V : TunnellUniformBasis.Basis d J) (r : Roots (parameter U.atPrime V.atPrime)) {z : ℂ} (hz : 0<z.im) :
    HasSum (fun m : ℕ => (Nat.card (lineShell U.atPrime V.atPrime m r.val):ℂ)*(Function.Periodic.qParam 1 z)^m) (theta U V r.val z) := by
  classical
  let X := {x : I×J // condition U V r.val x}
  let g (x : X) := degree x.val
  let q := Function.Periodic.qParam 1 z
  have h : HasSum (fun x:X => elem z x.val) (theta U V r.val z) := by
    apply (hasSum_subtype_iff_indicator (f:=elem z) (s:={x:I×J | condition U V r.val x})).mpr
    exact line_sum hs hn h2 hI hJ U V r.val hz
  have H := ((Equiv.sigmaFiberEquiv g).hasSum_iff).mpr h
  apply H.sigma
  intro m
  let F := {x : X // g x=m}
  have hF (x:F) : elem z x.val.val=q^m := (q_degree hs hn h2 hI hJ U V r x.val z).trans (congrArg (q^·) x.property)
  have hf : Finite F := by
    have hconstant : Summable (fun _ : F => q^m) := (h.summable.comp_injective (i:=fun x:F => x.val) Subtype.val_injective).congr hF
    have hq : q≠0 := Complex.exp_ne_zero _
    exact Finite.of_summable_const (norm_pos_iff.mpr (pow_ne_zero m hq)) hconstant.norm
  letI := Fintype.ofFinite F
  have hfin := hasSum_fintype (fun _ : F => q^m)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card] at hfin
  rw [←Nat.card_congr (shell_equiv hs hn h2 hI hJ U V r m)]
  exact hfin.congr_fun hF
theorem trace_expansion [NeZero d] (hs : Squarefree d) (hn : Squarefree (2*d)) (h2 : (2*d)%4=2) (hI : I≠⊥) (hJ : J≠⊥)
    (U : TunnellUniformBasis.Basis d I) (V : TunnellUniformBasis.Basis d J) {z : ℂ} (hz : 0<z.im) :
    HasSum (fun m : ℕ => (weight U.atPrime V.atPrime m:ℂ)*(Function.Periodic.qParam 1 z)^m) (trace U V z) := by
  have H := hasSum_sum (s:=Finset.univ) fun (r : Roots (parameter U.atPrime V.atPrime)) _ => line_expansion hs hn h2 hI hJ U V r hz
  apply H.congr_fun
  intro m
  simp only [weight,Nat.cast_sum,Finset.sum_mul]
end
end TunnellTraceSeries
end


/- TunnellTraceHeight -/
section
namespace TunnellTraceHeight
open TunnellShell TunnellToric TunnellToricClass TunnellProperClassGroup TunnellOddTraceHeight TunnellTraceChoices TunnellAnalyticLine TunnellRectangularIdeal
open scoped UpperHalfPlane Classical
noncomputable section
variable {d : ℕ}
def base [NeZero d] (D : Data d) (z : ℂ) :=
  letI : NeZero D.U.a := ⟨D.U.pos.ne'⟩
  letI : NeZero D.V.a := ⟨D.V.pos.ne'⟩
  rect d D.U.a 1 D.U.b 0 z*rect d D.V.a 4 D.V.b 0 z
def traced [NeZero d] (D : Data d) (z : ℂ) := TunnellAnalyticLine.trace D.U D.V z
def coeff (D : Data d) (m : ℕ) := TunnellTraceChoices.weight D.U.atPrime D.V.atPrime m
theorem exact [NeZero d] (hs : Squarefree d) (hn : Squarefree (2*d)) (hd : d%4=1) (h2 : (2*d)%4=2) {v : Triple} (hv : v∈shell (2*d)) :
    letI := TunnellFullClassTheta.classFintype hn h2 hv
    ∃ D : ProperIdealClass v×ProperIdealClass v → Data d,
      (∀ z w:ℍ, (w:ℂ)=4*(z:ℂ) → TunnellFullClassTheta.full hn h2 hv z*TunnellFullClassTheta.full hn h2 hv w=∑ a, base (D a) z) ∧
      (∀ z:ℍ, HasSum (fun m : ℕ => ((∑ a, coeff (D a) m:ℕ):ℂ)*(Function.Periodic.qParam 1 z)^m) (∑ a, traced (D a) z)) ∧
      ∀ m, Odd m → ((∑ a, coeff (D a) m:ℕ):ℚ)=
        (Fintype.card ↥(representatives (2*d)):ℚ)^2*(∑ k∈m.divisors,(k:ℚ))+
          (TunnellShell.b d:ℚ)^2*(TunnellQuaternion.etaCoeff m:ℚ) := by
  classical
  letI := TunnellFullClassTheta.classFintype hn h2 hv
  obtain ⟨D,h,he⟩ := total hs hn hd h2 hv
  refine ⟨D,?_,?_,?_⟩
  · intro z w ew; rw [h z w]; apply Finset.sum_congr rfl; intro a _
    letI : NeZero (D a).U.a := ⟨(D a).U.pos.ne'⟩
    letI : NeZero (D a).V.a := ⟨(D a).V.pos.ne'⟩
    change _=rect d (D a).U.a 1 (D a).U.b 0 z*rect d (D a).V.a 4 (D a).V.b 0 z
    rw [unshifted (D a).U (D a).hI z.im_pos,unshifted (D a).V (D a).hJ z.im_pos,ew]; simp
  · intro z
    have H := hasSum_sum (s:=Finset.univ) fun a _ => TunnellTraceSeries.trace_expansion hs hn h2 (D a).hI (D a).hJ (D a).U (D a).V z.im_pos
    apply H.congr_fun; intro m; simp only [coeff,Nat.cast_sum,Finset.sum_mul]
  · intro m hm; rw [Nat.cast_sum]; exact he m hm
end
end TunnellTraceHeight
end


/- TunnellRankinLambert -/
section
namespace TunnellRankinCotangent
open Complex Finset TunnellRankin UpperHalfPlane
noncomputable section
def multiple (a : ℕ+) (z : ℍ) : ℍ :=
  ⟨(a.val:ℂ)*(z:ℂ), by simpa [Complex.mul_im] using z.im_pos⟩
end
end TunnellRankinCotangent
end


/- TunnellWaldspurgerLocal -/
section
namespace TunnellWaldspurgerLocal
open Finset TunnellLocalFourier
noncomputable def localPeriod (d : ℕ) : ℤ :=
  open scoped Classical in
  (((TunnellShell.shell (2*d)).filter (fun v=>v∈Set.range TunnellTestVector.first)).card:ℤ)-
    ((TunnellShell.shell (2*d)).filter (fun v=>v∈Set.range TunnellTestVector.second)).card
end TunnellWaldspurgerLocal
end


/- TunnellSignedFinite -/
section
namespace TunnellFiniteSymbols
open Finset Polynomial TunnellRootPolynomial TunnellTwistCharacter TunnellWaldspurgerLocal
 
def shellPeriod (d : ℕ) : ℤ :=
  (((TunnellShell.shell (2*d)).filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%8=0)).card:ℤ)-
  ((TunnellShell.shell (2*d)).filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%4=0 ∧
    (v.1+v.2.1+2*(v.2.2/4))%4=0)).card
lemma shellPeriod_eq (d : ℕ) : shellPeriod d=localPeriod d := by
  classical
  simp only [shellPeriod,localPeriod,TunnellTestVector.first_iff,TunnellTestVector.second_iff]
end TunnellFiniteSymbols
end


/- TunnellWindingTraceSource -/
section
namespace TunnellWindingTrace
open TunnellShell TunnellToric TunnellToricClass TunnellProperClassGroup TunnellOddTraceHeight TunnellRankinIntegral
open TunnellFiniteSymbols TunnellFricke TunnellHalfFourier TunnellHalfPairing TunnellRankinCotangent
open scoped UpperHalfPlane Classical
noncomputable section
def mass (d : ℕ) := Fintype.card ↥(representatives (2*d))
def sigma (m : ℕ) : ℂ := ∑ k∈m.divisors,(k:ℂ)
def cuspCoeff (m : ℕ) : ℂ := (TunnellQuaternion.etaCoeff m:ℂ)
end
end TunnellWindingTrace
end


/- TunnellPublicMoment -/
section
namespace SignedSquarePublic
open Polynomial Finset MatrixGroups ModularGroup CongruenceSubgroup MeasureTheory
open scoped UpperHalfPlane Classical ComplexConjugate
noncomputable section
def mass (d : ℕ) : ℕ :=
    let b := Icc (-((2*d:ℕ):ℤ)-1) (((2*d:ℕ):ℤ)+1)
    let s := (b ×ˢ (b ×ˢ b)).filter (fun v => v.1^2+v.2.1^2+v.2.2^2=((2*d:ℕ):ℤ))
    (s.filter (fun v => Odd v.1 ∧ Odd v.2.1 ∧ Even v.2.2 ∧ 0<v.1 ∧ 0<v.2.1)).card
def theta (d : ℕ) (z : ℂ) := (mass d:ℂ) + 2*∑' m : ℕ,
    (∑ e ∈ m.divisors, ((if Odd e then jacobiSym (-((2*d:ℕ):ℤ)) e else 0 : ℤ):ℂ))*Function.Periodic.qParam 1 z^m
lemma mass_eq (d : ℕ) : mass d=TunnellWindingTrace.mass d := by
  classical
  rw [TunnellWindingTrace.mass,Fintype.card_coe]
  apply congrArg Finset.card
  ext v
  simp only [TunnellToric.representatives,TunnellShell.shell,mem_filter]
  rfl
theorem theta_eq {d : ℕ} {v : TunnellShell.Triple} (hn : Squarefree (2*d)) (hd : d%4=1) (hv : v∈TunnellShell.shell (2*d)) (z : ℍ) :
    theta d z=TunnellFullClassTheta.full hn (by omega) hv z := by
  letI := TunnellFullClassTheta.classFintype hn (by omega) hv
  have hcard := Fintype.card_congr (TunnellToricClass.idealEquiv hn (by omega) hv)
  rw [TunnellFullClassTheta.full_expansion,hcard]
  simp only [theta,mass_eq,TunnellWindingTrace.mass,TunnellRankin.theta,TunnellRankin.idealCoeff,TunnellRankin.negWeight,Int.cast_sum]
end
end SignedSquarePublic
end


/- TunnellPublicRectangle -/
section
namespace TunnellPublicRectangle
open Finset Polynomial MeasureTheory MatrixGroups ModularGroup CongruenceSubgroup
open scoped UpperHalfPlane Classical ComplexConjugate
noncomputable section
def R (d a k:ℕ) (b u:ℤ) (z:ℂ) := ∑' x:ℤ×ℤ,
    Complex.exp (2*Real.pi*Complex.I*z*k*((a*x.1+b*x.2:ℤ)^2+(2*(d:ℂ))*((x.2:ℂ)+(a:ℂ)*u/d)^2)/a)
def K (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) (u v:ℤ) (z:ℂ) := R d i.1 1 i.2.1 u z*R d i.2.2.1 4 i.2.2.2 v z
def T (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) (z:ℂ) := ∑' w:ZMod d×ZMod d,
    (∏ p:↥d.primeFactors, (Nat.card {t:ZMod p.val // (i.1:ZMod p.val)*t^2= -4*i.2.2.1 ∧
      (w.1.val:ZMod p.val)=t*w.2.val}:ℂ))*K d i w.1.val w.2.val z
def G (d:ℕ) (i:ℕ×ℤ×ℕ×ℤ) := 0 < i.1 ∧ 0 < i.2.2.1 ∧ i.1.Coprime d ∧ i.2.2.1.Coprime d
open TunnellTraceHeight TunnellOddTraceHeight TunnellRamifiedLines TunnellAnalyticLine
open TunnellIntegralPacket TunnellLineDensity TunnellRectangularClasses TunnellRectangularIdeal
open TunnellTraceChoices TunnellLineIntegral TunnellUniformBasis
def form {d:ℕ} (D:Data d) := (D.U.a,D.U.b,D.V.a,D.V.b)
theorem good {d:ℕ} (D:Data d) : G d (form D) := ⟨D.U.pos,D.V.pos,D.U.cop,D.V.cop⟩
theorem R_eq {d a k:ℕ} [NeZero d] [NeZero a] [NeZero k] (b u:ℤ) (z:ℍ) :
    R d a k b u z=rect d a k b u z := (translated d a k b u z.im_pos).tsum_eq
theorem base_eq {d:ℕ} [NeZero d] (D:Data d) (z:ℍ) : K d (form D) 0 0 z=base D z := by
  letI : NeZero D.U.a := ⟨D.U.pos.ne'⟩
  letI : NeZero D.V.a := ⟨D.V.pos.ne'⟩
  change R d D.U.a 1 D.U.b 0 z*R d D.V.a 4 D.V.b 0 z=_
  rw [R_eq,R_eq]; rfl
def rootCount (p a c:ℕ) (x y:ZMod p) :=
  Nat.card {t:ZMod p // (a:ZMod p)*t^2= -4*c ∧ x=t*y}
theorem count_eq {p a c:ℕ} [Fact p.Prime] (ha:(a:ZMod p)≠0) (x y:ZMod p) :
    rootCount p a c x y=density (-(4:ZMod p)*c/a) (x,y) := by
  unfold rootCount density RootsAt
  apply Nat.card_congr
  apply Equiv.subtypeEquivRight
  intro t
  apply and_congr_left; intro _
  rw [eq_div_iff ha,mul_comm (t^2)]
theorem reduce_val {d:ℕ} [NeZero d] (i:P d) (w:ZMod d) :
    (w.val:ZMod i.val)=reduce i w := by
  have e := congrArg (reduce i) (ZMod.natCast_zmod_val w)
  simpa only [map_natCast] using e
theorem traced_eq {d:ℕ} [NeZero d] (D:Data d) (z:ℍ) : T d (form D) z=traced D z := by
  classical
  letI : NeZero D.U.a := ⟨D.U.pos.ne'⟩
  letI : NeZero D.V.a := ⟨D.V.pos.ne'⟩
  letI (i:P d) : Fact i.val.Prime := ⟨Nat.prime_of_mem_primeFactors i.property⟩
  let f (w:ZMod d×ZMod d) := rect d D.U.a 1 D.U.b w.1.val z*rect d D.V.a 4 D.V.b w.2.val z
  have he : traced D z=∑ r : Roots (parameter D.U.atPrime D.V.atPrime), ∑ w : ZMod d×ZMod d,
      if ∀ i:P d, reduce i w.1=r.val i*reduce i w.2 then f w else 0 := by
    unfold traced TunnellAnalyticLine.trace TunnellAnalyticLine.theta
    apply sum_congr rfl; intro r _
    apply sum_congr rfl; intro w _
    unfold aligned
    split_ifs <;> rfl
  rw [he,TunnellLineDensity.factor,T,tsum_fintype]
  apply sum_congr rfl; intro w _
  change (∏ i:P d,(rootCount i.val D.U.a D.V.a (w.1.val:ZMod i.val) (w.2.val:ZMod i.val):ℂ))*
    (R d D.U.a 1 D.U.b w.1.val z*R d D.V.a 4 D.V.b w.2.val z)=_
  rw [R_eq,R_eq]
  congr 1
  apply prod_congr rfl; intro i _
  rw [reduce_val,reduce_val,count_eq (a:=D.U.a) (by simpa [Basis.atPrime] using (D.U.atPrime i).unit)]
  simp only [parameter,Basis.atPrime,Int.cast_natCast]
end
end TunnellPublicRectangle
end


/- TunnellPublicGeometric -/
section
namespace TunnellPublicGeometric
open Finset Polynomial MeasureTheory MatrixGroups ModularGroup CongruenceSubgroup
open scoped UpperHalfPlane Classical ComplexConjugate
open TunnellPublicRectangle TunnellShell TunnellToricClass TunnellTraceHeight TunnellWindingTrace
open SignedSquarePublic TunnellFiniteSymbols TunnellRankinCotangent TunnellHalfFourier
noncomputable section
theorem result : OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1_H2_R1.H1 := by
  classical
  refine ⟨sigma,fun m => cuspCoeff m/4,?_⟩
  intro d hs hd
  letI : NeZero d := ⟨by omega⟩
  have hn : Squarefree (2*d) := (Nat.squarefree_mul (Nat.odd_iff.mpr (by omega) : Odd d).coprime_two_left).mpr ⟨Nat.prime_two.squarefree,hs⟩
  obtain ⟨v,hv⟩ := TunnellThreeSquares.shell_nonempty d hd
  letI := TunnellFullClassTheta.classFintype hn (by omega) hv
  let C := ProperIdealClass v×ProperIdealClass v
  obtain ⟨D,hD,hF,ha⟩ := TunnellTraceHeight.exact hs hn hd (by omega) hv
  let E := (Fintype.equivFin C).symm
  let a (m:ℕ) := ((∑ x:C,coeff (D x) m:ℕ):ℂ)
  refine ⟨Fintype.card C,fun i => form (D (E i)),a,fun i => good _,?_,?_,?_⟩
  · intro z
    change SignedSquarePublic.theta d z*SignedSquarePublic.theta d (4*(z:ℂ))=_
    have hh := theta_eq hn hd hv (multiple 4 z)
    change SignedSquarePublic.theta d (4*(z:ℂ))=_ at hh
    rw [theta_eq hn hd hv,hh,hD z (multiple 4 z) rfl]
    change _=∑ i,K d (form (D (E i))) 0 0 z
    simp_rw [base_eq]
    exact (E.sum_comp (fun x => base (D x) z)).symm
  · intro z
    change HasSum _ (∑ i,T d (form (D (E i))) z)
    simp_rw [traced_eq]
    rw [E.sum_comp (fun x => traced (D x) z)]
    exact hF z
  · intro m hm
    change a m=(SignedSquarePublic.mass d:ℂ)^2*sigma m+(shellPeriod d:ℂ)^2*(cuspCoeff m/4)
    rw [mass_eq,shellPeriod_eq,show TunnellWaldspurgerLocal.localPeriod d=2*TunnellShell.b d from TunnellTestVector.signed_shell d (Nat.odd_iff.mpr (by omega))]
    have he := congrArg (fun t:ℚ => (t:ℂ)) (ha m hm)
    dsimp only [a]; unfold TunnellWindingTrace.mass sigma cuspCoeff
    push_cast at he ⊢
    linear_combination he
end
end TunnellPublicGeometric
end


theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1_H2_R1.H1 := TunnellPublicGeometric.result
