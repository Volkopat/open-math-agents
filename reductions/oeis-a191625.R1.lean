import OMAStatements.S_oeis_a191625
import Mathlib
namespace OMA.R_oeis_a191625_R1
open PowerSeries OMA.S_oeis_a191625

lemma resultant {S : Type*} [CommRing S] (u a b c d e g : S)
    (h : a*u^2+b*u+c=0) (j : d*u^2+e*u+g=0) :
    a*(a*g-d*c)^2 - b*(a*g-d*c)*(a*e-d*b)+c*(a*e-d*b)^2=0 := by
  let E := a*e-d*b
  let F := a*g-d*c
  have lin : E*u+F=0 := by dsimp [E,F]; linear_combination a*j-d*h
  change a*F^2-b*F*E+c*E^2=0
  linear_combination E^2*h+(a*(F-E*u)-b*E)*lin

def H1 : Prop := let t : PowerSeries ℤ := X
  ∃ u : PowerSeries ℤ, constantCoeff u = 0 ∧ t*u^2 + (-t^3-t^2+t-1)*u + t = 0

def H2 : Prop := let t : PowerSeries ℤ := X
  let f := PowerSeries.mk count
  ∀ u : PowerSeries ℤ, constantCoeff u = 0 → t*u^2 + (-t^3-t^2+t-1)*u + t = 0 →
    (f+1)*(1-t*u)*(2*t-u)-2*(1-t^2)*(1-t)*u=0

lemma algebraic (h1 : H1) (h2 : H2) :
    let t : PowerSeries ℤ := X
    let f := PowerSeries.mk count
    (2*t^4-2*t^3-2*t^2+t)*f^2+(-2*t^4+4*t^3-6*t+2)*f-2*t^3+2*t^2+t-2=0 := by
  let t : PowerSeries ℤ := X
  let f := PowerSeries.mk count
  obtain ⟨u,h0,hu⟩ := h1
  have w := h2 u h0 hu
  change t*u^2+(-t^3-t^2+t-1)*u+t=0 at hu
  change (f+1)*(1-t*u)*(2*t-u)-2*(1-t^2)*(1-t)*u=0 at w
  have w' : (t*(f+1))*u^2+(-(f+1)*(1+2*t^2)-2*(1-t^2)*(1-t))*u+2*t*(f+1)=0 := by linear_combination w
  have d := resultant u _ _ _ _ _ _ hu w'
  let r := (2*t^4-2*t^3-2*t^2+t)*f^2+(-2*t^4+4*t^3-6*t+2)*f-2*t^3+2*t^2+t-2
  have prod : (t^3*(t-1)*(t+1))*r=0 := by dsimp [r]; linear_combination d
  have minus : t-1≠0 := by intro h; have z := congrArg (constantCoeff (R:=ℤ)) h; norm_num [t] at z
  have plus : t+1≠0 := by intro h; have z := congrArg (constantCoeff (R:=ℤ)) h; norm_num [t] at z
  exact (mul_eq_zero.mp prod).resolve_left (mul_ne_zero (mul_ne_zero (pow_ne_zero _ X_ne_zero) minus) plus)

lemma differential (h1 : H1) (h2 : H2) :
    let t : PowerSeries ℤ := X
    let f := PowerSeries.mk count
    t*(t-1)*(t+1)*(t^2+1)*(t^2+2*t-1)*(2*t^3-2*t^2-2*t+1)*(derivative ℤ f) +
      (2*t^8+7*t^6-6*t^5-3*t^4+18*t^3-3*t^2-4*t+1)*f =
       2*t^8-5*t^6-14*t^5+5*t^4+6*t^3-7*t^2+1 := by
  let t : PowerSeries ℤ := X
  let f := PowerSeries.mk count
  let a := 2*t^4-2*t^3-2*t^2+t
  let b := -2*t^4+4*t^3-6*t+2
  let c := -2*t^3+2*t^2+t-2
  let p := (t-1)*(t+1)*(t^2+1)*(t^2+2*t-1)*(2*t^3-2*t^2-2*t+1)
  let v := 2*t^8+7*t^6-6*t^5-3*t^4+18*t^3-3*t^2-4*t+1
  let w := 2*t^8-5*t^6-14*t^5+5*t^4+6*t^3-7*t^2+1
  have r : a*f^2+b*f+c=0 := by dsimp [a,b,c,t,f]; linear_combination algebraic h1 h2
  have rd := congrArg (derivative ℤ) r
  dsimp only [a,b,c] at rd
  have dt : derivative ℤ t = 1 := derivative_X
  have d2 : derivative ℤ (2:PowerSeries ℤ)=0 := (derivative ℤ).map_natCast 2
  have d4 : derivative ℤ (4:PowerSeries ℤ)=0 := (derivative ℤ).map_natCast 4
  have d6 : derivative ℤ (6:PowerSeries ℤ)=0 := (derivative ℤ).map_natCast 6
  simp only [map_add,map_sub,map_neg,Derivation.leibniz,Derivation.leibniz_pow,dt,
    d2,d4,d6,Derivation.map_one_eq_zero,map_zero,smul_eq_mul] at rd
  have mult : (2*a*f+b)*(t*p*(derivative ℤ f)+v*f-w)=0 := by
    dsimp only [a,b,c,p,v,w] at *
    norm_num at rd
    linear_combination t*((t-1)*(t+1)*(t^2+1)*(t^2+2*t-1)*(2*t^3-2*t^2-2*t+1))*rd +
      (-8*t^9-6*t^8+24*t^7+15*t^6-10*t^5+5*t^4+12*t^3-7*t^2-2*t+1)*r
  have non : 2*a*f+b ≠ 0 := by
    intro h
    have z := congrArg (constantCoeff (R:=ℤ)) h
    norm_num [a,b,t] at z
    have two : constantCoeff (2:PowerSeries ℤ)=(2:ℤ) := map_natCast _ 2
    rw [two] at z
    omega
  have e := sub_eq_zero.mp ((mul_eq_zero.mp mult).resolve_left non)
  dsimp [p,v,w,t,f] at e
  linear_combination e
lemma auxiliary_exists : H1 := by
  let t : PowerSeries ℤ := X
  let phi (u : PowerSeries ℤ) := u^2+(1-t-t^2)*u+1
  let step (m : ℕ) : (∀ k, k < m → ℤ) → ℤ := match m with
    | 0 => fun _ => 0
    | n+1 => fun h => coeff n (phi (PowerSeries.mk (fun k => if hk : k < n+1 then h k hk else 0)))
  let w (n : ℕ) : ℤ := Nat.strongRecOn n step
  have recw (n : ℕ) : w n = step n (fun k _ => w k) := Nat.strongRecOn_eq step n
  let u := PowerSeries.mk w
  have zero : constantCoeff u = 0 := by
    rw [←coeff_zero_eq_constantCoeff_apply]
    exact (coeff_mk 0 w).trans (recw 0)
  refine ⟨u,zero,?_⟩
  have fixed : u = t*phi u := by
    ext j
    cases j with
    | zero => simp [coeff_zero_eq_constantCoeff_apply,zero,t]
    | succ n =>
      let v := PowerSeries.mk (fun k => if k < n+1 then w k else 0)
      have trunc : t^(n+1) ∣ u-v := by
        apply X_pow_dvd_iff.mpr
        intro k hk
        simp [u,v,Nat.lt_succ_iff.mp hk]
      have lift : t^(n+1) ∣ phi u-phi v := by
        rw [show phi u-phi v=(u-v)*(u+v+1-t-t^2) by dsimp [phi]; ring]
        exact dvd_mul_of_dvd_left trunc _
      have hc := X_pow_dvd_iff.mp lift n (Nat.lt_succ_self _)
      rw [map_sub,sub_eq_zero] at hc
      have val : w (n+1) = coeff n (phi v) := recw (n+1)
      change coeff (n+1) (PowerSeries.mk w) = coeff (n+1) (X*phi u)
      rw [coeff_mk,←pow_one (X : PowerSeries ℤ),coeff_X_pow_mul]
      exact val.trans hc.symm
  change t*u^2+(-t^3-t^2+t-1)*u+t=0
  dsimp [phi] at fixed
  linear_combination -fixed

lemma auxiliary_unique (u v : PowerSeries ℤ)
    (hu : X*u^2+(-X^3-X^2+X-1)*u+X=0)
    (hv : X*v^2+(-X^3-X^2+X-1)*v+X=0) : u=v := by
  let t : PowerSeries ℤ := X
  have iterate : u-v = t*(u-v)*(u+v+1-t-t^2) := by
    dsimp [t]; linear_combination hv - hu
  have divisible (n : ℕ) : t^n ∣ u-v := by
    induction n with
    | zero => simp
    | succ n ih =>
      obtain ⟨c,hc⟩ := ih
      refine ⟨c*(u+v+1-t-t^2),?_⟩
      calc
        u-v = t*(u-v)*(u+v+1-t-t^2) := iterate
        _ = t^(n+1)*(c*(u+v+1-t-t^2)) := by rw [hc,pow_succ]; ring
  ext n
  have h := X_pow_dvd_iff.mp (divisible (n+1)) n (Nat.lt_succ_self _)
  exact sub_eq_zero.mp (by simpa using h)
lemma extract (j : ℕ) : coeff j (X*derivative ℤ (PowerSeries.mk count)) = (j:ℤ)*count j := by
  cases j with
  | zero => simp [coeff_zero_eq_constantCoeff_apply]
  | succ j =>
    rw [←pow_one (X : PowerSeries ℤ),coeff_X_pow_mul,coeff_derivative,coeff_mk]
    push_cast
    ring

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a191625.main := by
  intro h1 h2 n hn
  let t : PowerSeries ℤ := X
  let f := PowerSeries.mk count
  let g := t*derivative ℤ f
  have eqn : (1 • (t^0*g)) -(4 • (t^1*g)) +(1 • (t^2*g)) +(8 • (t^3*g)) -(3 • (t^4*g)) +(2 • (t^5*g)) -(1 • (t^6*g)) -(8 • (t^7*g)) +(2 • (t^8*g)) +(2 • (t^9*g)) +(1 • (t^0*f)) -(4 • (t^1*f)) -(3 • (t^2*f)) +(18 • (t^3*f)) -(3 • (t^4*f)) -(6 • (t^5*f)) +(7 • (t^6*f)) +(2 • (t^8*f)) = (1 • (t^0)) -(7 • (t^2)) +(6 • (t^3)) +(5 • (t^4)) -(14 • (t^5)) -(5 • (t^6)) +(2 • (t^8)) := by
    dsimp only [g,f,t]
    simp only [nsmul_eq_mul]
    linear_combination differential h1 h2
  have hc := congrArg (coeff (R:=ℤ) n) eqn
  simp only [map_add,map_sub,map_neg,map_nsmul] at hc
  simp (disch := omega) only [t, coeff_X_pow_mul',coeff_X_pow,if_pos,if_neg] at hc
  simp (disch := omega) only [f,g,t,extract,coeff_mk,Nat.cast_sub,nsmul_eq_mul,Nat.sub_zero,
    Nat.cast_ofNat,Nat.cast_zero] at hc
  linear_combination hc
end OMA.R_oeis_a191625_R1
