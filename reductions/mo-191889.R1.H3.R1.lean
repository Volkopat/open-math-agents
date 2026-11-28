import OMAReductions.R_mo_191889_R1
import Mathlib

/-!
# The large squarefree parameter in the powerful fourth-power census

Write the sum as b³k². Every prime of k is 1 modulo 8. We prove Lucas's
theorem for arbitrary coprime positive x and y by
factoring their fourth-power sum in the Gaussian integers. For the resulting
quartic z² + 3u⁴ = v⁴ a primitive solution splits as v² = a² + 3c²,
u² = 2ac. Reducing (v+a)/c yields a new solution whose positive
fourth-power coordinate is strictly smaller.

For 17, 41, and every admissible cofactor from 73 through 289, the Gaussian
factorization B³W² gives two binary cubic forms with square values. Primitivity
forces the coordinates of W to be coprime, including when its norm is 17².
Signs, conjugation and exchange of the two square coordinates give one chart per
cofactor. Congruences modulo 16 and 9 locate these charts in classes modulo 48.
The bit tables below check the signed parameter boxes in strips of 256 rows.
The remaining cofactors are at least 313, with b ≤ 31589416817. A further sieve retains 378 residue classes for b modulo 30160 for each possible k. The two
subproblems distinguish k = 313 from k ≥ 337. Both supply a rational right
triangle of area 2b.

Chad Mazzola formalized Lucas's theorem using a different descent in Beal
reduction #9630. The reduced-slope proof here also
gives the auxiliary quartic for arbitrary positive u, including imprimitive inputs.
The prime-order and parity arguments below are adapted from ZedingZhang’s parent
reduction in #8603. The cube theorem and congruent-number sieve are used by
Noam D. Elkies and Gaurav Goel, *On powerful integers expressible as sums of
two coprime fourth powers*, sections 2 and 4.
https://antsmath.org/ANTSXV/papers/ANTS-XV_elkies-goel.pdf
-/

namespace OMA.R_mo_191889_R1_H3_R1

/-- Cofactor 313 is the first possibility after the finite exclusions. -/
def H1 : Prop :=
  ∀ b x y : ℕ, 10000 < b → b ≤ 31589416817 → Squarefree b →
    (∀ p ∈ b.primeFactors, p % 8 = 1) →
    (b%16=1 ∧ (b^3*313^2)%5 ∈ [1,2] ∧ (b^3*313^2)%13 ∈ [1,2,3,4,5,6,9,10,12] ∧
      (b^3*313^2)%29 ∈ [1,2,3,7,8,10,11,12,14,15,16,17,18,19,20,21,23,24,25,26,27]) →
    (∃ a d c : ℚ, 0 < a ∧ 0 < d ∧ 0 < c ∧ a^2+d^2=c^2 ∧ a*d=4*(b:ℚ)) →
    0 < x → x < y → y ≤ 1325648472 → x.Coprime y →
    x^4+y^4=b^3*313^2 → b^3*313^2 < 3088257489493360278725196965477359217 → False

/-- Above cofactor 313 the next possibilities are 337 and then at least 353. -/
def H2 : Prop :=
  ∀ b k x y : ℕ, 10000 < b → b ≤ 30071232849 → Squarefree b →
    (∀ p ∈ b.primeFactors, p % 8 = 1) → 337 ≤ k →
    (∀ p ∈ k.primeFactors, p % 8 = 1) → (29155558369 < b → k=337) →
    (b%16=1 ∧ (b^3*k^2)%5 ∈ [1,2] ∧ (b^3*k^2)%13 ∈ [1,2,3,4,5,6,9,10,12] ∧
      (b^3*k^2)%29 ∈ [1,2,3,7,8,10,11,12,14,15,16,17,18,19,20,21,23,24,25,26,27]) →
    (∃ a d c : ℚ, 0 < a ∧ 0 < d ∧ 0 < c ∧ a^2+d^2=c^2 ∧ a*d=4*(b:ℚ)) →
    0 < x → x < y → y ≤ 1325648472 → x.Coprime y →
    x^4+y^4=b^3*k^2 → b^3*k^2 < 3088257489493360278725196965477359217 → False

section Arithmetic

private theorem not_four {x y : ℕ} (hc : x.Coprime y) : ¬ 4 ∣ x^4+y^4 := by
  intro h
  have tab : ∀ i j : Fin 4, (i.val^4+j.val^4)%4 = 0 →
      i.val%2 = 0 ∧ j.val%2 = 0 := by decide
  have congr := ((Nat.mod_modEq x 4).pow 4).add ((Nat.mod_modEq y 4).pow 4)
  have h0 : ((x%4)^4+(y%4)^4)%4 = 0 := congr.trans h.modEq_zero_nat
  obtain ⟨hx,hy⟩ := tab ⟨x%4, Nat.mod_lt _ (by decide)⟩ ⟨y%4, Nat.mod_lt _ (by decide)⟩ h0
  change (x%4)%2 = 0 at hx
  change (y%4)%2 = 0 at hy
  rw [Nat.mod_mod_of_dvd x (by decide : 2 ∣ 4)] at hx
  rw [Nat.mod_mod_of_dvd y (by decide : 2 ∣ 4)] at hy
  have hd := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero hx) (Nat.dvd_of_mod_eq_zero hy)
  rw [show x.gcd y = 1 from hc] at hd
  norm_num at hd

private theorem prime_residue {x y p : ℕ} (hc : x.Coprime y) (hp : p.Prime)
    (hne : p ≠ 2) (hd : p ∣ x^4+y^4) : p%8 = 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have hz := (ZMod.natCast_eq_zero_iff (x^4+y^4) p).mpr hd
  push_cast at hz
  have hy : (y : ZMod p) ≠ 0 := by
    intro hy
    have hx : (x : ZMod p) = 0 := by simpa [hy] using hz
    have gd := Nat.dvd_gcd ((ZMod.natCast_eq_zero_iff x p).mp hx)
      ((ZMod.natCast_eq_zero_iff y p).mp hy)
    rw [show x.gcd y = 1 from hc] at gd
    exact hp.not_dvd_one gd
  let u := (x : ZMod p) / y
  have hu4 : u^4 = -1 := by
    change ((x : ZMod p) / y)^4 = -1
    rw [div_pow,div_eq_iff (pow_ne_zero _ hy)]
    linear_combination hz
  have hu8 : u^8 = 1 := by rw [show 8 = 4*2 by decide,pow_mul,hu4]; norm_num
  have hnot : u^4 ≠ 1 := by
    rw [hu4]
    intro he
    have htwo : (2 : ZMod p) = 0 := by linear_combination -he
    have hle := Nat.le_of_dvd (by decide : 0 < 2) ((ZMod.natCast_eq_zero_iff 2 p).mp htwo)
    have := hp.two_le
    omega
  have hd8 := orderOf_dvd_of_pow_eq_one hu8
  have hd4 : ¬ orderOf u ∣ 4 := fun h => hnot (orderOf_dvd_iff_pow_eq_one.mp h)
  have order : orderOf u = 8 := by
    have le := Nat.le_of_dvd (by decide : 0 < 8) hd8
    generalize hh : orderOf u = m at *
    interval_cases m <;> norm_num at *
  have une : u ≠ 0 := by intro h; simp [h] at hu8
  have div := ZMod.orderOf_dvd_card_sub_one une
  rw [order] at div
  obtain ⟨j,hj⟩ := div
  have := hp.two_le
  omega

/-- The Pythagorean triple for U = x⁴+y⁴ and V = 2x²y² supplies a triangle
of area 2b after division by xyz(y⁴−x⁴). -/
theorem triangle_of_quartic {x y z b : ℚ} (hx : 0<x) (hxy : x<y) (hz : 0<z)
    (he : x^4+y^4=b*z^2) :
    ∃ a d c : ℚ, 0<a ∧ 0<d ∧ 0<c ∧ a^2+d^2=c^2 ∧ a*d=4*b := by
  let u := x^4+y^4
  let v := 2*x^2*y^2
  let w := y^4-x^4
  let t := x*y*z
  have hy := hx.trans hxy
  have hu : 0<u := by dsimp [u]; positivity
  have hv : 0<v := by dsimp [v]; positivity
  have hw : 0<w := sub_pos.mpr (pow_lt_pow_left₀ hxy hx.le (by decide : 4≠0))
  have ht : 0<t := by dsimp [t]; positivity
  have rel : w^2=u^2-v^2 := by dsimp [u,v,w]; ring
  have size : 2*u*v=4*b*t^2 := by dsimp [u,v,t]; rw [he]; ring
  refine ⟨w^2/(t*w), (2*u*v)/(t*w), (u^2+v^2)/(t*w), by positivity,
    by positivity, by positivity, ?_, ?_⟩
  · rw [div_pow,div_pow,div_pow,←add_div]
    apply congrArg (fun q : ℚ => q/(t*w)^2)
    rw [rel]; ring
  · rw [size]
    field_simp [ht.ne',hw.ne']

private theorem gunit_fourth (u : GaussianIntˣ) : (u:GaussianInt)^4=1 := by
  have h := (Zsqrtd.norm_eq_one_iff' (show (-1:ℤ)≤0 by decide) (u:GaussianInt)).mpr u.isUnit
  generalize eq : (u:GaussianInt)=v at h ⊢
  obtain ⟨a,b⟩ := v
  change a*a-(-1)*b*b=1 at h
  have al : -1≤a := by by_contra! e; nlinarith [sq_nonneg b, mul_nonneg (show 0≤ -a-2 by omega) (show 0≤ -a+2 by omega)]
  have ah : a≤1 := by by_contra! e; nlinarith [sq_nonneg b, mul_nonneg (show 0≤ a-2 by omega) (show 0≤ a+2 by omega)]
  have bl : -1≤b := by by_contra! e; nlinarith [sq_nonneg a, mul_nonneg (show 0≤ -b-2 by omega) (show 0≤ -b+2 by omega)]
  have bh : b≤1 := by by_contra! e; nlinarith [sq_nonneg a, mul_nonneg (show 0≤ b-2 by omega) (show 0≤ b+2 by omega)]
  interval_cases a <;> interval_cases b <;> norm_num at h <;> decide

private theorem quartic_coprime {x y b z : ℕ} (hc : x.Coprime y) (hb : Odd b)
    (he : x^4+y^4=b*z^2) :
    let a : GaussianInt := ⟨(x:ℤ)^2,(y:ℤ)^2⟩
    IsCoprime a (star a) := by
  let a : GaussianInt := ⟨(x:ℤ)^2,(y:ℤ)^2⟩
  let i : GaussianInt := ⟨0,1⟩
  change IsCoprime a (star a)
  have hz : Odd z := by
    rcases Nat.even_or_odd z with ev|od
    · have h4 : 2^2 ∣ z^2 := pow_dvd_pow_of_dvd (even_iff_two_dvd.mp ev) 2
      exact (not_four hc (he ▸ dvd_mul_of_dvd_right h4 b)).elim
    · exact od
  have plus : a+star a=2*(x:GaussianInt)^2 := by
    ext <;> simp [a,star,pow_two]
    ring
  have minus : (-i)*(a-star a)=2*(y:GaussianInt)^2 := by
    ext <;> simp [a,i,star,pow_two]
    ring
  have prod : a*star a=((b*z^2:ℕ):GaussianInt) := by
    rw [← he,Zsqrtd.natCast_val]
    ext <;> simp [a,star] <;> ring
  have cps := ((hc.pow_left 2).pow_right 2).isCoprime.map (Int.castRingHom GaussianInt)
  have oddN := Nat.coprime_two_left.mpr (hb.mul (hz.pow (n:=2)))
  have cp2 := oddN.isCoprime.map (Int.castRingHom GaussianInt)
  simp only [Int.coe_castRingHom, Nat.cast_pow, Int.cast_pow, Int.cast_natCast] at cps
  change IsCoprime (2:GaussianInt) ((b*z^2:ℕ):GaussianInt) at cp2
  apply IsRelPrime.isCoprime
  intro d da dc
  have dx := plus ▸ dvd_add da dc
  have dy := minus ▸ dvd_mul_of_dvd_right (dvd_sub da dc) (-i)
  have d2 : d ∣ 2 := by
    obtain ⟨j,k,eq⟩ := cps
    have ds := dvd_add (dvd_mul_of_dvd_left dx j) (dvd_mul_of_dvd_left dy k)
    convert ds using 1
    linear_combination -2*eq
  exact cp2.isRelPrime d2 (prod ▸ dvd_mul_of_dvd_left da _)

private theorem quartic_norm (x y : ℕ) :
    (⟨(x:ℤ)^2,(y:ℤ)^2⟩ : GaussianInt).norm = ((x^4+y^4 : ℕ):ℤ) := by
  simp [Zsqrtd.norm]
  ring

/-- A scalar square in a primitive Gaussian norm can be removed as a Gaussian square. -/
private theorem strip_norm_square {a : GaussianInt} {b z : ℕ}
    (cp : IsCoprime a (star a)) (hz : 0<z) (he : a.norm=(b:ℤ)*(z:ℤ)^2) :
    ∃ B W : GaussianInt, a=B*W^2 ∧ B.norm=b ∧ W.norm=z := by
  have prod : a*star a=(b:GaussianInt)*(z:GaussianInt)^2 := by
    rw [← Zsqrtd.norm_eq_mul_conj, he]
    push_cast
    rfl
  have scalar : (z:GaussianInt)^2 ∣ a*star a := prod ▸ dvd_mul_left _ _
  obtain ⟨d,e,da,ec,hde⟩ := exists_dvd_and_dvd_of_dvd_mul
    ((dvd_pow_self (z:GaussianInt) (by decide : 2≠0)).trans scalar)
  have sd : star d ∣ star a := map_dvd (starRingEnd GaussianInt) da
  have se : star e ∣ a := by
    have h := map_dvd (starRingEnd GaussianInt) ec
    simpa only [starRingEnd_apply,star_star] using h
  have rev : (z:GaussianInt)=star e*star d := by
    simpa only [star_natCast,star_mul] using congrArg star hde
  have cpd := cp.of_isCoprime_of_dvd_left da
  have cpe := cp.of_isCoprime_of_dvd_left se
  have dse : d ∣ star e :=
    (cpd.of_isCoprime_of_dvd_right sd).dvd_of_dvd_mul_right
      (rev ▸ hde.symm ▸ dvd_mul_right d e)
  have sed : star e ∣ d :=
    (cpe.of_isCoprime_of_dvd_right ec).dvd_of_dvd_mul_right
      (hde ▸ rev.symm ▸ dvd_mul_right (star e) (star d))
  have en : d.norm=e.norm := by
    simpa using Zsqrtd.norm_eq_of_associated (by decide : (-1:ℤ)≤0)
      (associated_of_dvd_dvd dse sed)
  have normZ := congrArg Zsqrtd.norm hde
  rw [Zsqrtd.norm_natCast,Zsqrtd.norm_mul,←en] at normZ
  have dn : d.norm=(z:ℤ) := (sq_eq_sq₀ (GaussianInt.norm_nonneg d) (by positivity)).mp
    (by simpa [pow_two] using normZ.symm)
  have d2 : d^2 ∣ a := cpd.pow_left.dvd_of_dvd_mul_right
    ((pow_dvd_pow_of_dvd (hde ▸ dvd_mul_right d e) 2).trans scalar)
  obtain ⟨B,hab⟩ := d2
  have n := congrArg Zsqrtd.norm hab
  simp only [Zsqrtd.norm_mul,pow_two,dn,he] at n
  have bn : B.norm=(b:ℤ) := by
    have zz : (z:ℤ)*(z:ℤ)≠0 := by positivity
    exact mul_right_cancel₀ zz (by linear_combination -n)
  exact ⟨B,d,hab.trans (mul_comm _ _),bn,dn⟩

private theorem cube_of_norm {a : GaussianInt} {b : ℕ} (hc : IsCoprime a (star a))
    (hn : a.norm=(b:ℤ)^3) : ∃ B : GaussianInt, a=B^3 ∧ B.norm=b := by
  have prod : a*star a=(b:GaussianInt)^3 := by
    rw [← Zsqrtd.norm_eq_mul_conj,hn]
    push_cast
    rfl
  obtain ⟨d,⟨u,hu⟩⟩ := exists_associated_pow_of_mul_eq_pow' hc prod
  let B := d*(u:GaussianInt)^3
  have cube : a=B^3 := by
    rw [←hu]
    dsimp [B]
    rw [mul_pow]
    have e := gunit_fourth u
    calc d^3*(u:GaussianInt) = d^3*(((u:GaussianInt)^4)^2*(u:GaussianInt)) := by rw [e]; ring
         _ = d^3*((u:GaussianInt)^3)^3 := by ring
  refine ⟨B,cube,(Odd.strictMono_pow (by decide : Odd 3)).injective ?_⟩
  rw [← hn,cube]
  simp [pow_succ]

/-- The condition b ∣ z gives the stronger factorization with Gaussian exponents 3 and 2. -/
private theorem powerful_descent {b k x y : ℕ} (hb : Odd b) (hk : 0<k) (hc : x.Coprime y)
    (he : x^4+y^4=b^3*k^2) :
    ∃ B W : GaussianInt, (⟨(x:ℤ)^2,(y:ℤ)^2⟩ : GaussianInt)=B^3*W^2 ∧
      B.norm=b ∧ W.norm=k := by
  let a : GaussianInt := ⟨(x:ℤ)^2,(y:ℤ)^2⟩
  have cp : IsCoprime a (star a) :=
    quartic_coprime hc hb (he.trans (by ring : b^3*k^2=b*(b*k)^2))
  have hn : a.norm=((b^3:ℕ):ℤ)*(k:ℤ)^2 := by
    rw [quartic_norm,he]
    push_cast
    rfl
  obtain ⟨D,W,eq,dn,wn⟩ := strip_norm_square cp hk hn
  have da : D ∣ a := eq ▸ dvd_mul_right _ _
  have dc : star D ∣ star a := map_dvd (starRingEnd GaussianInt) da
  obtain ⟨B,cube,bn⟩ := cube_of_norm
    ((cp.of_isCoprime_of_dvd_left da).of_isCoprime_of_dvd_right dc) (by simpa using dn)
  exact ⟨B,W,eq.trans (by rw [cube]),bn,wn⟩

private theorem gaussian_cube {x y b : ℕ} (hc : x.Coprime y) (hodd : Odd b)
    (he : x^4+y^4=b^3) :
    ∃ m n : ℤ, (x:ℤ)^2=m*(m^2-3*n^2) ∧ (y:ℤ)^2=n*(3*m^2-n^2) ∧
      m^2+n^2=(b:ℤ) := by
  obtain ⟨B,fac,hn⟩ := cube_of_norm
    (quartic_coprime (z:=b) hc hodd (he.trans (by ring))) (by rw [quartic_norm,he]; push_cast; rfl)
  obtain ⟨m,n⟩ := B
  have ex := congrArg Zsqrtd.re fac
  have ey := congrArg Zsqrtd.im fac
  simp [pow_succ] at ex ey
  refine ⟨m,n,by linear_combination ex,by linear_combination ey,?_⟩
  simpa [Zsqrtd.norm,pow_two] using hn

private theorem square_class {m c X : ℕ} (hm : 0 < m) (he : m*c=X^2) (hd : m.gcd c ∣ 3) :
    ∃ u : ℕ, m=u^2 ∨ m=3*u^2 := by
  let g := m.gcd c
  have hp : 0 < g := Nat.gcd_pos_of_pos_left c hm
  have dm := Nat.gcd_dvd_left m c
  have dc := Nat.gcd_dvd_right m c
  have mm : m/g*g=m := Nat.div_mul_cancel dm
  have cc : c/g*g=c := Nat.div_mul_cancel dc
  have dvd : g^2 ∣ X^2 := by rw [←he,pow_two]; exact Nat.mul_dvd_mul dm dc
  obtain ⟨v,hv⟩ := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp dvd
  have eq : m/g*(c/g)=v^2 := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < g^2 from pow_pos hp _)
    calc m/g*(c/g)*g^2 = (m/g*g)*(c/g*g) := by ring
         _ = X^2 := by rw [mm,cc,he]
         _ = v^2*g^2 := by rw [hv];ring
  have cp : (m/g).Coprime (c/g) := Nat.coprime_div_gcd_div_gcd hp
  obtain ⟨u,hu⟩ := exists_eq_pow_of_mul_eq_pow
    (show IsUnit (gcd (m/g) (c/g)) by change IsUnit ((m/g).gcd (c/g)); rw [cp]; exact isUnit_one) eq
  have gor : g=1 ∨ g=3 := (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hd
  rw [hu] at mm
  exact ⟨u, gor.elim (fun e => Or.inl (by simpa [e] using mm.symm))
    (fun e => Or.inr (by simpa [e,Nat.mul_comm] using mm.symm))⟩

private theorem coefficient {m n : ℤ} (cp : m.natAbs.Coprime n.natAbs) :
    m.natAbs.gcd (m^2-3*n^2).natAbs ∣ 3 := by
  let g := m.natAbs.gcd (m^2-3*n^2).natAbs
  have gm : g ∣ m.natAbs := Nat.gcd_dvd_left _ _
  have gf : g ∣ (m^2-3*n^2).natAbs := Nat.gcd_dvd_right _ _
  have mg : (g:ℤ) ∣ m := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr gm)
  have fg : (g:ℤ) ∣ m^2-3*n^2 := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr gf)
  have d : (g:ℤ) ∣ 3*n^2 := by
    have sub := dvd_sub (dvd_pow mg (by decide : 2≠0)) fg
    simpa only [sub_sub_cancel] using sub
  have dn : g ∣ 3*n.natAbs^2 := by
    have h := Int.dvd_natAbs.mpr d
    simpa only [Int.natAbs_mul,Int.natAbs_pow,show (3 : ℤ).natAbs = 3 by decide, Nat.cast_mul,
      Nat.cast_pow,Nat.cast_ofNat] using (Int.natCast_dvd_natCast.mp h)
  have cg : g.Coprime (n.natAbs^2) := (cp.coprime_dvd_left gm).pow_right 2
  exact cg.dvd_of_dvd_mul_right dn

private theorem coordinates_coprime {x y : ℕ} {m n : ℤ} (hc : x.Coprime y)
    (ex : (x:ℤ)^2=m*(m^2-3*n^2)) (ey : (y:ℤ)^2=n*(3*m^2-n^2)) :
    m.natAbs.Coprime n.natAbs := by
  apply Nat.coprime_of_dvd
  intro p pr pm pn
  have hx := congrArg Int.natAbs ex
  have hy := congrArg Int.natAbs ey
  simp only [Int.natAbs_pow,Int.natAbs_mul,Int.natAbs_natCast] at hx hy
  have px := pr.dvd_of_dvd_pow (show p ∣ x^2 by rw [hx]; exact dvd_mul_of_dvd_left pm _)
  have py := pr.dvd_of_dvd_pow (show p ∣ y^2 by rw [hy]; exact dvd_mul_of_dvd_left pn _)
  exact (Nat.not_coprime_of_dvd_of_dvd pr.one_lt px py) hc

/-- Squaring a natural absolute value recovers the original integer square. -/
private theorem absSquare (a : ℤ) : (a.natAbs:ℤ)^2=a^2 := by
  rw [Int.natCast_natAbs,←abs_pow,abs_of_nonneg (sq_nonneg _)]

private theorem smaller_square {A B X : ℕ} (h : A≤B)
    (he : X^2=A*((A:ℤ)^2-3*(B:ℤ)^2).natAbs) :
    X^2=A*(3*B^2-A^2) := by
  have le : A^2≤3*B^2 := by have := Nat.pow_le_pow_left h 2; omega
  have e : (A:ℤ)^2-3*(B:ℤ)^2 = -((3*B^2-A^2 : ℕ):ℤ) := by
    rw [Nat.cast_sub le];push_cast;ring
  simpa only [e,Int.natAbs_neg,Int.natAbs_natCast] using he

/-- The prime 3 has odd valuation in three times a nonzero square. -/
private theorem not_three_square_sum {a b c : ℕ} (hc : 0<c) (h : a^2+b^2=3*c^2) : False := by
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hn : 3*c^2≠0 := by positivity
  have hm : 3 ∈ (3*c^2).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨by decide,dvd_mul_right _ _,hn⟩
  have even := Nat.eq_sq_add_sq_iff.mp ⟨a,b,h.symm⟩ 3 hm (by decide)
  rw [padicValNat.mul (by decide) (by positivity),padicValNat.pow (p:=3) c 2,
    padicValNat_self] at even
  rcases even with ⟨q,hq⟩
  omega

private theorem unscale {X d c : ℕ} (hd : 0<d) (h : X^2=d^2*c) : ∃ w : ℕ, w^2=c := by
  have dvd : d^2 ∣ X^2 := h ▸ dvd_mul_right _ _
  obtain ⟨w,eq⟩ := (Nat.pow_dvd_pow_iff (by decide : 2≠0)).mp dvd
  rw [eq,mul_pow] at h
  exact ⟨w,Nat.eq_of_mul_eq_mul_left (pow_pos hd 2) h⟩

/-- Congruences modulo 16 and 9 control parity and the prime 3. -/
private theorem primitive_residues {u v z : ℕ} (cp : u.Coprime v)
    (he : z^2+3*u^4=v^4) : u%2=0 ∧ v%2=1 ∧ z%2=1 ∧ ¬3∣v := by
  have red (p : ℕ) : ((z%p)^2+3*(u%p)^4)%p=(v%p)^4%p := by
    have h := ((Nat.mod_modEq z p).pow 2).add (((Nat.mod_modEq u p).pow 4).mul_left 3)
    exact h.trans (he ▸ ((Nat.mod_modEq v p).pow 4).symm)
  have tab : ∀ i j k : Fin 16, (i.val^2+3*j.val^4)%16=k.val^4%16 →
      j.val%2=0 ∧ i.val%2=k.val%2 := by decide +kernel
  have h := tab ⟨z%16,Nat.mod_lt _ (by decide)⟩ ⟨u%16,Nat.mod_lt _ (by decide)⟩
    ⟨v%16,Nat.mod_lt _ (by decide)⟩ (red 16)
  change (u%16)%2=0 ∧ (z%16)%2=(v%16)%2 at h
  simp only [Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 16)] at h
  have vo : v%2=1 := by
    by_contra hn
    exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1<2)
      (Nat.dvd_of_mod_eq_zero h.1) (Nat.dvd_of_mod_eq_zero (by omega))) cp
  refine ⟨h.1,vo,h.2.trans vo,?_⟩
  intro dv
  have t : ∀ i j k : Fin 9, (i.val^2+3*j.val^4)%9=k.val^4%9 →
      k.val%3=0 → j.val%3=0 := by decide +kernel
  have e := t ⟨z%9,Nat.mod_lt _ (by decide)⟩ ⟨u%9,Nat.mod_lt _ (by decide)⟩
    ⟨v%9,Nat.mod_lt _ (by decide)⟩ (red 9)
  change (v%9)%3=0 → (u%9)%3=0 at e
  simp only [Nat.mod_mod_of_dvd _ (by decide : 3 ∣ 9)] at e
  exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1<3)
    (Nat.dvd_of_mod_eq_zero (e (Nat.mod_eq_zero_of_dvd dv))) dv) cp

private theorem square_pair {a b t : ℕ} (hab : a.Coprime b) (he : a*b=t^2) :
    ∃ m n : ℕ, a=m^2 ∧ b=n^2 := by
  have first {x y : ℕ} (hc : x.Coprime y) (h : x*y=t^2) : ∃ s : ℕ, x=s^2 := by
    exact exists_eq_pow_of_mul_eq_pow
      (show IsUnit (gcd x y) by change IsUnit (x.gcd y); rw [hc]; exact isUnit_one) h
  obtain ⟨m,hm⟩ := first hab he
  obtain ⟨n,hn⟩ := first hab.symm ((mul_comm b a).trans he)
  exact ⟨m,n,hm,hn⟩

/-- Split (v²+z)/2 and (v²-z)/2 into one square and three times a square. -/
private theorem split_quartic {u v z : ℕ} (up : 0<u) (cp : u.Coprime v)
    (he : z^2+3*u^4=v^4) :
    ∃ a c : ℕ, 0<a ∧ 0<c ∧ v^2=a^2+3*c^2 ∧ u^2=2*a*c := by
  obtain ⟨ue,vo,zo,h3⟩ := primitive_residues cp he
  obtain ⟨h,uh⟩ := Nat.dvd_of_mod_eq_zero ue
  have zv : z<v^2 := by
    by_contra! hn
    have le := Nat.pow_le_pow_left hn 2
    rw [show (v^2)^2=v^4 by ring] at le
    have := pow_pos up 4
    omega
  have vodd : v^2%2=1 := by rw [Nat.pow_mod,vo]
  let F := (v^2+z)/2
  let G := (v^2-z)/2
  have sum : F+G=v^2 := by dsimp [F,G]; omega
  have diff : G+z=F := by dsimp [F,G]; omega
  have gp : 0<G := by dsimp [G]; omega
  have fp : 0<F := by omega
  have prod : F*G=3*(2*h^2)^2 := by
    have hq : (F+G)^2=z^2+3*(2*h)^4 := by rw [sum,←uh,he]; ring
    rw [←diff] at hq ⊢
    nlinarith only [hq]
  have cop : F.Coprime G := by
    apply Nat.coprime_of_dvd
    intro p pr df dg
    have dv : p∣v := pr.dvd_of_dvd_pow (sum ▸ dvd_add df dg)
    have dz : p∣z := (Nat.dvd_add_iff_right dg).mpr (diff ▸ df)
    have d3 : p∣3*u^4 := (Nat.dvd_add_iff_right (dvd_pow dz (by decide : 2≠0))).mpr
      (he ▸ dvd_pow dv (by decide : 4≠0))
    rcases pr.dvd_mul.mp d3 with q|q
    · have e := (Nat.prime_dvd_prime_iff_eq pr (by decide : Nat.Prime 3)).mp q
      exact h3 (e ▸ dv)
    · exact (Nat.not_coprime_of_dvd_of_dvd pr.one_lt (pr.dvd_of_dvd_pow q) dv) cp
  have split (A B : ℕ) (ap : 0<A) (bp : 0<B) (ab : A.Coprime B)
      (su : A+B=v^2) (mul : A*B=3*(2*h^2)^2) (d : 3∣B) :
      ∃ a c : ℕ, 0<a ∧ 0<c ∧ v^2=a^2+3*c^2 ∧ u^2=2*a*c := by
    obtain ⟨D,bd⟩ := d
    have ac := ab.coprime_dvd_right (bd ▸ dvd_mul_left D 3)
    have sq : A*D=(2*h^2)^2 := by rw [bd] at mul; nlinarith only [mul]
    obtain ⟨a,c,aa,cc⟩ := square_pair ac sq
    have eq : a*c=2*h^2 := (sq_eq_sq₀ (by positivity) (by positivity)).mp (by
      rw [mul_pow,←aa,←cc]; exact sq)
    refine ⟨a,c,by by_contra! hn; simp [aa,show a=0 by omega] at ap,
      by by_contra! hn; simp [bd,cc,show c=0 by omega] at bp,?_,?_⟩
    · rw [←su,aa,bd,cc]
    · rw [uh,show 2*a*c=2*(a*c) by ring,eq]; ring
  have d : 3∣F*G := prod ▸ dvd_mul_right _ _
  rcases (show Nat.Prime 3 by decide).dvd_mul.mp d with f|g
  · exact split G F gp fp cop.symm ((add_comm G F).trans sum) ((mul_comm G F).trans prod) f
  · exact split F G fp gp cop sum prod g

/-- Reduce the slope (v+a)/c to A/B. Its denominator is a square. The
numerator must also be a square because the other square class would make
three times a nonzero square a sum of two squares. -/
private theorem descend_slope {u v a c : ℕ} (ap : 0<a) (cp : 0<c)
    (vv : v^2=a^2+3*c^2) (uu : u^2=2*a*c) :
    ∃ s t w : ℕ, 0<t ∧ t.Coprime s ∧ s<v ∧ w^2+3*t^4=s^4 := by
  let p := v+a
  let g := p.gcd c
  let A := p/g
  let B := c/g
  have pp : 0<p := by dsimp [p]; omega
  have gp : 0<g := Nat.gcd_pos_of_pos_left c pp
  have dp : g∣p := Nat.gcd_dvd_left p c
  have dc : g∣c := Nat.gcd_dvd_right p c
  have ga : g*A=p := Nat.mul_div_cancel' dp
  have gb : g*B=c := Nat.mul_div_cancel' dc
  have AP : 0<A := Nat.div_pos (Nat.le_of_dvd pp dp) gp
  have BP : 0<B := Nat.div_pos (Nat.le_of_dvd cp dc) gp
  have ab : A.Coprime B := Nat.coprime_div_gcd_div_gcd gp
  have ident : (g*A)^2=3*(g*B)^2+2*a*p := by
    rw [ga,gb]; dsimp only [p]; nlinarith only [vv]
  have ge : 3*B^2 ≤ A^2 := by
    by_contra! lt
    have neg := Nat.mul_lt_mul_of_pos_left lt (pow_pos gp 2)
    nlinarith only [neg,ident,Nat.zero_le (2*a*p)]
  let D := A^2-3*B^2
  have sub : 3*B^2+D=A^2 := Nat.add_sub_of_le ge
  have gd : g^2*D=2*a*p := by
    have eq := congrArg (fun n => g^2*n) sub
    nlinarith only [eq,ident]
  have raw : (u*p)^2=(g^2)^2*(A*B*D) := by
    calc (u*p)^2 = (2*a*p)*(p*c) := by rw [mul_pow,uu]; ring
         _ = (g^2*D)*((g*A)*(g*B)) := by rw [gd,ga,gb]
         _ = _ := by ring
  obtain ⟨w,hw⟩ := unscale (pow_pos gp 2) raw
  have bd : B.Coprime D := by
    apply Nat.coprime_of_dvd
    intro l pr lb ld
    have h : l∣A^2 := sub ▸ dvd_add (dvd_mul_of_dvd_right (dvd_pow lb (by decide : 2≠0)) 3) ld
    exact (Nat.not_coprime_of_dvd_of_dvd pr.one_lt (pr.dvd_of_dvd_pow h) lb) ab
  obtain ⟨t,w',tb,hw'⟩ := square_pair (ab.symm.mul_right bd)
    (show B*(A*D)=w^2 by rw [hw]; ring)
  have tp : 0<t := by by_contra! hn; simp [tb,show t=0 by omega] at BP
  have gcd3 : A.gcd D ∣ 3 := by
    let d := A.gcd D
    have da : d∣A := Nat.gcd_dvd_left _ _
    have dd : d∣D := Nat.gcd_dvd_right _ _
    have d3 : d∣3*B^2 := (Nat.dvd_add_iff_left dd).mpr (sub ▸ dvd_pow da (by decide : 2≠0))
    exact ((ab.coprime_dvd_left da).pow_right 2).dvd_of_dvd_mul_right d3
  obtain ⟨s,hs|hs⟩ := square_class AP hw' gcd3
  · have sp : 0<s := by by_contra! hn; simp [hs,show s=0 by omega] at AP
    obtain ⟨w0,eq⟩ := unscale sp (show w'^2=s^2*D by rw [←hw',hs])
    have av : a<v := by
      by_contra! va
      have bad := Nat.pow_le_pow_left va 2
      have pos := pow_pos cp 2
      omega
    have below : s<v := by
      have bound : A≤p := Nat.div_le_self _ _
      change A≤v+a at bound
      by_contra! vs
      have square := Nat.pow_le_pow_left vs 2
      have tw : 2≤v := by omega
      have two := Nat.mul_le_mul_right v tw
      rw [←pow_two] at two
      omega
    have cop : t.Coprime s := ab.symm.coprime_dvd_left
      (tb ▸ dvd_pow_self t (by decide : 2≠0)) |>.coprime_dvd_right
      (hs ▸ dvd_pow_self s (by decide : 2≠0))
    refine ⟨s,t,w0,tp,cop,below,?_⟩
    rw [hs,tb] at sub
    rw [eq]
    nlinarith only [sub]
  · have sp : 0<s := by by_contra! hn; simp [hs,show s=0 by omega] at AP
    have Dform : D=3*(3*s^4-t^4) := by
      dsimp only [D]; rw [hs,tb,Nat.mul_sub]; congr 1 <;> ring
    obtain ⟨j,eq⟩ := unscale (show 0<3*s by positivity)
      (show w'^2=(3*s)^2*(3*s^4-t^4) by rw [←hw',hs,Dform]; ring)
    have small : t^4 ≤ 3*s^4 := by rw [hs,tb] at ge; nlinarith only [ge]
    have add := Nat.sub_add_cancel small
    exact (not_three_square_sum (pow_pos sp 2)
      (show j^2+(t^2)^2=3*(s^2)^2 by rw [eq]; nlinarith only [add])).elim

private theorem no_primitive_quartic (v : ℕ) :
    ∀ u z : ℕ, 0<u → u.Coprime v → z^2+3*u^4=v^4 → False := by
  induction v using Nat.strong_induction_on with
  | h v ih =>
    intro u z up cp he
    obtain ⟨a,c,ap,cpos,vv,uu⟩ := split_quartic up cp he
    obtain ⟨s,t,w,tp,cop,lt,eq⟩ := descend_slope ap cpos vv uu
    exact ih s lt t w tp cop eq

/-- Infinite descent excludes z² + 3u⁴ = v⁴ for every positive u. -/
theorem quartic_three {u v z : ℕ} (up : 0<u) (he : z^2+3*u^4=v^4) : False := by
  let g := u.gcd v
  let U := u/g
  let V := v/g
  have gp : 0<g := Nat.gcd_pos_of_pos_left _ up
  have du : g∣u := Nat.gcd_dvd_left _ _
  have gu : g*U=u := Nat.mul_div_cancel' du
  have gv : g*V=v := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
  have eq : z^2+g^4*(3*U^4)=g^4*V^4 := by
    rw [←gu,←gv] at he
    nlinarith only [he]
  have le : 3*U^4≤V^4 := by
    by_contra! h
    have lt := Nat.mul_lt_mul_of_pos_left h (pow_pos gp 4)
    omega
  have sq : z^2=(g^2)^2*(V^4-3*U^4) := by
    rw [show (g^2)^2=g^4 by ring,Nat.mul_sub]; omega
  obtain ⟨w,hw⟩ := unscale (pow_pos gp 2) sq
  exact no_primitive_quartic V U w (Nat.div_pos (Nat.le_of_dvd up du) gp)
    (Nat.coprime_div_gcd_div_gcd gp) (by omega)

/-- If the smaller Gaussian coordinate is a square, the local obstruction at
3 suffices. If it is three times a square, coprimality makes the other
coordinate a square, giving precisely Z² + 3u⁴ = v⁴. -/
private theorem small_magnitude {u v s t X : ℕ} (up : 0<u)
    (vp : 0<v) (ss : s=1 ∨ s=3) (tt : t=1 ∨ t=3)
    (cp : (s*u^2).Coprime (t*v^2)) (le : s*u^2 ≤ t*v^2)
    (h : X^2=(s*u^2)*(3*(t*v^2)^2-(s*u^2)^2)) : False := by
  rcases ss with rfl|rfl
  · simp only [one_mul] at h le
    obtain ⟨w,hw⟩ := unscale up h
    have posT : 0<t := by omega
    have posN : 0<t*v^2 := by positivity
    have ll : (u^2)^2≤3*(t*v^2)^2 := by have := Nat.pow_le_pow_left le 2; omega
    exact not_three_square_sum posN (show w^2+(u^2)^2=3*(t*v^2)^2 by omega)
  · rcases tt with rfl|rfl
    · simp only [one_mul] at h le
      have f : 3*(v^2)^2-(3*u^2)^2 = 3*(v^4-3*u^4) := by
        rw [Nat.mul_sub]
        congr 1 <;> ring
      have hx : X^2=(3*u)^2*(v^4-3*u^4) := by rw [h,f];ring
      obtain ⟨w,hw⟩ := unscale (show 0<3*u by positivity) hx
      have ll := Nat.pow_le_pow_left le 2
      have u4 : (3*u^2)^2 = 9*u^4 := by ring
      have v4 : (v^2)^2=v^4 := by ring
      rw [u4,v4] at ll
      exact quartic_three up (show w^2+3*u^4=v^4 by omega)
    · exact (Nat.not_coprime_of_dvd_of_dvd (by decide : 1<3) (dvd_mul_right _ _) (dvd_mul_right _ _)) cp

/-- The Gaussian cube descent excludes every odd cube. -/
private theorem cube_excluded_odd {b x y : ℕ}
    (hodd : Odd b) (hx : 0<x) (hy : 0<y) (hc : x.Coprime y) (he : x^4+y^4=b^3) : False := by
  obtain ⟨m,n,ex,ey,_⟩ := gaussian_cube hc hodd he
  let A := m.natAbs
  let B := n.natAbs
  have xx : x^2=A*(m^2-3*n^2).natAbs := by
    simpa only [A,Int.natAbs_pow,Int.natAbs_natCast,Int.natAbs_mul] using congrArg Int.natAbs ex
  have yy : y^2=B*(n^2-3*m^2).natAbs := by
    have e : (n^2-3*m^2).natAbs=(3*m^2-n^2).natAbs := by rw [←neg_sub (3*m^2) (n^2),Int.natAbs_neg]
    simpa only [B,e,Int.natAbs_pow,Int.natAbs_natCast,Int.natAbs_mul] using congrArg Int.natAbs ey
  have ap : 0<A := by
    by_contra! h
    have ha : A=0 := by omega
    simp [ha] at xx
    omega
  have bp : 0<B := by
    by_contra! h
    have hn : B=0 := by omega
    simp [hn] at yy
    omega
  have cp := coordinates_coprime hc ex ey
  obtain ⟨u,hu⟩ := square_class ap xx.symm (coefficient cp)
  obtain ⟨v,hv⟩ := square_class bp yy.symm (coefficient cp.symm)
  have pos {M t : ℕ} (h : M=t^2 ∨ M=3*t^2) (hM : 0<M) : 0<t := by
    by_contra! small
    have z : t=0 := by omega
    simp [z] at h
    omega
  have up := pos hu ap
  have vp := pos hv bp
  have repr {M t : ℕ} (h : M=t^2 ∨ M=3*t^2) :
      ∃ s : ℕ, (s=1 ∨ s=3) ∧ M=s*t^2 := by
    rcases h with e|e
    · exact ⟨1,Or.inl rfl,by simpa using e⟩
    · exact ⟨3,Or.inr rfl,e⟩
  obtain ⟨s,ss,es⟩ := repr hu
  obtain ⟨t,tt,et⟩ := repr hv
  rw [←absSquare m,←absSquare n] at xx yy
  rcases le_total A B with le|le
  · have e := smaller_square le xx
    rw [es,et] at e le
    exact small_magnitude up vp ss tt (by rwa [←es,←et]) le e
  · have e := smaller_square le yy
    rw [es,et] at e le
    exact small_magnitude vp up tt ss (by rw [←es,←et]; exact cp.symm) le e

/-- Lucas's theorem. A sum of two coprime positive fourth powers cannot be a cube. -/
theorem lucas_no_cubes {b x y : ℕ} (hx : 0<x) (hy : 0<y)
    (hc : x.Coprime y) (he : x^4+y^4=b^3) : False := by
  rcases Nat.even_or_odd b with even|odd
  · have h2 : 2 ∣ b := even_iff_two_dvd.mp even
    have d4 : 4 ∣ b^3 := (pow_dvd_pow_of_dvd h2 2).trans (pow_dvd_pow b (by decide : 2≤3))
    exact not_four hc (he ▸ d4)
  · exact cube_excluded_odd odd hx hy hc he

/-- The specialization used in the original bounded census. -/
theorem bounded_lucas {b x y : ℕ} (_hb : b≤1456256357804) (hx : 0<x) (hy : 0<y)
    (hc : x.Coprime y) (he : x^4+y^4=b^3) : False :=
  lucas_no_cubes hx hy hc he

/-- There is just one Gaussian cubic chart for cofactor 17 if the two square
coordinates may be interchanged. Its signed parameters have norm b. -/
theorem gaussian_seventeen {b x y : ℕ} (hb : Odd b) (hc : x.Coprime y)
    (he : x^4+y^4=b^3*17^2) :
    ∃ m n X Y : ℤ, m^2+n^2=(b:ℤ) ∧
      ((X=(x:ℤ) ∧ Y=(y:ℤ)) ∨ (X=(y:ℤ) ∧ Y=(x:ℤ))) ∧
      X^2= -15*(m^3-3*m*n^2)-8*(3*m^2*n-n^3) ∧
      Y^2= 8*(m^3-3*m*n^2)-15*(3*m^2*n-n^3) := by
  obtain ⟨⟨m,n⟩,⟨e,f⟩,fac,bn,wn⟩ := powerful_descent hb (by decide : 0<17) hc he
  have ex := congrArg Zsqrtd.re fac
  have ey := congrArg Zsqrtd.im fac
  simp [pow_succ] at ex ey
  have norm : m^2+n^2=(b:ℤ) := by simpa [Zsqrtd.norm,pow_two] using bn
  have qr : e^2+f^2=17 := by simpa [Zsqrtd.norm,pow_two] using wn
  have lim {c d : ℤ} (eq : c^2+d^2=17) : -4≤c ∧ c≤4 := by
    constructor
    · by_contra! h
      nlinarith [sq_nonneg d,mul_nonneg (show 0≤ -c-5 by omega) (show 0≤ -c+5 by omega)]
    · by_contra! h
      nlinarith [sq_nonneg d,mul_nonneg (show 0≤c-5 by omega) (show 0≤c+5 by omega)]
  have ec := lim qr
  have fc := lim (by rw [add_comm]; exact qr : f^2+e^2=17)
  have cases : (e=-4 ∧ f=-1) ∨ (e=-4 ∧ f=1) ∨ (e=-1 ∧ f=-4) ∨ (e=-1 ∧ f=4) ∨ (e=1 ∧ f=-4) ∨ (e=1 ∧ f=4) ∨ (e=4 ∧ f=-1) ∨ (e=4 ∧ f=1) := by
    obtain ⟨_,_⟩ := ec
    obtain ⟨_,_⟩ := fc
    interval_cases e <;> interval_cases f <;> norm_num at *
  rcases cases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · refine ⟨n,m,y,x,by linear_combination norm,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ey
    · linear_combination ex
  · refine ⟨(-m),(-n),x,y,by linear_combination norm,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ex
    · linear_combination ey
  · refine ⟨m,n,x,y,by linear_combination norm,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ex
    · linear_combination ey
  · refine ⟨(-n),(-m),y,x,by linear_combination norm,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ey
    · linear_combination ex
  · refine ⟨(-n),(-m),y,x,by linear_combination norm,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ey
    · linear_combination ex
  · refine ⟨m,n,x,y,by linear_combination norm,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ex
    · linear_combination ey
  · refine ⟨(-m),(-n),x,y,by linear_combination norm,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ex
    · linear_combination ey
  · refine ⟨n,m,y,x,by linear_combination norm,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ey
    · linear_combination ex

set_option maxRecDepth 20000 in
/-- A primitive point on the cubic chart lies in eight signed lattice classes
modulo 48, and its norm lies in six classes modulo 3120. -/
private theorem chart_residues {b : ℕ} {m n X Y : ℤ} (odd : b%2=1)
    (d3 : b%3≠0) (d5 : b%5≠0) (d13 : b%13≠0) (bn : m^2+n^2=(b:ℤ))
    (ex : X^2= -15*(m^3-3*m*n^2)-8*(3*m^2*n-n^3))
    (ey : Y^2=8*(m^3-3*m*n^2)-15*(3*m^2*n-n^3)) :
    b%3120 ∈ [17,257,1169,1889,2129,2417] ∧
      (m%48,n%48) ∈ [(8,23),(8,47),(17,8),(17,20),(41,8),(41,20),(44,23),(44,47)] := by
  let chart (p : ℕ) (a c : ZMod p) : Prop :=
    (∃ X : ZMod p, X^2=-15*(a^3-3*a*c^2)-8*(3*a^2*c-c^3)) ∧
    (∃ Y : ZMod p, Y^2=8*(a^3-3*a*c^2)-15*(3*a^2*c-c^3))
  have point (p : ℕ) : chart p m n := by
    refine ⟨⟨(X : ZMod p),?_⟩,⟨(Y : ZMod p),?_⟩⟩
    · simpa using congrArg (fun z : ℤ => (z : ZMod p)) ex
    · simpa using congrArg (fun z : ℤ => (z : ZMod p)) ey
  have hn (p : ℕ) : (m : ZMod p)^2+(n : ZMod p)^2=(b : ZMod p) := by
    simpa using congrArg (fun z : ℤ => (z : ZMod p)) bn
  have t16 : ∀ a c : ZMod 16, chart 16 a c → (a^2+c^2).val%2=1 →
      (a^2+c^2).val=1 ∧ ((a.val:ℤ),(c.val:ℤ)) ∈ [(1,4),(1,8),(8,7),(8,15),(9,4),(9,8),(12,7),(12,15)] := by
    unfold chart
    decide +kernel
  have s16 := t16 _ _ (point 16)
  simp only [hn,ZMod.val_natCast,ZMod.val_intCast] at s16
  obtain ⟨b16,m16⟩ := s16 (by omega)
  have t9 : ∀ a c : ZMod 9, chart 9 a c → (a^2+c^2).val%3≠0 →
      (a^2+c^2).val%3=2 ∧ (a.val:ℤ)%3=2 ∧ (c.val:ℤ)%3=2 := by
    unfold chart
    decide +kernel
  have s9 := t9 _ _ (point 9)
  simp only [hn,ZMod.val_natCast,ZMod.val_intCast] at s9
  obtain ⟨b3,m3,n3⟩ := s9 (by omega)
  have t5 : ∀ a c : ZMod 5, chart 5 a c → (a^2+c^2).val≠0 →
      (a^2+c^2).val ∈ [2,4] := by
    unfold chart
    decide +kernel
  have s5 := t5 _ _ (point 5)
  simp only [hn,ZMod.val_natCast] at s5
  have b5 := s5 d5
  have t13 : ∀ a c : ZMod 13, chart 13 a c → (a^2+c^2).val≠0 →
      (a^2+c^2).val ∈ [4,10,12] := by
    unfold chart
    decide +kernel
  have s13 := t13 _ _ (point 13)
  simp only [hn,ZMod.val_natCast] at s13
  have b13 := s13 d13
  constructor
  · have all : ∀ i : Fin 3120, i.val%16=1 → i.val%3=2 →
        i.val%5 ∈ [2,4] → i.val%13 ∈ [4,10,12] → i.val ∈ [17,257,1169,1889,2129,2417] := by decide +kernel
    apply all ⟨b%3120,Nat.mod_lt _ (by decide)⟩ <;>
      simp only [Nat.mod_mod_of_dvd _ (by decide : 16∣3120),
        Nat.mod_mod_of_dvd _ (by decide : 3∣3120),Nat.mod_mod_of_dvd _ (by decide : 5∣3120),
        Nat.mod_mod_of_dvd _ (by decide : 13∣3120)]
    · exact b16
    · omega
    · exact b5
    · exact b13
  · have tab : ∀ a c : Fin 48, a.val%3=2 → c.val%3=2 →
        (((a.val:ℤ)%16),((c.val:ℤ)%16)) ∈ [(1,4),(1,8),(8,7),(8,15),(9,4),(9,8),(12,7),(12,15)] →
        ((a.val:ℤ),(c.val:ℤ)) ∈ [(8,23),(8,47),(17,8),(17,20),(41,8),(41,20),(44,23),(44,47)] := by decide +kernel
    have lift (t : ℤ) : ((t%48).toNat:ℤ)=t%48 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
    have take (t : ℤ) : (t%48).toNat < 48 := by have := lift t; omega
    have h := tab ⟨_,take m⟩ ⟨_,take n⟩
    simp only [lift] at h
    apply h
    · have := lift m; omega
    · have := lift n; omega
    · simpa only [Nat.cast_ofNat,Int.emod_emod_of_dvd _ (by decide : (16:ℤ)∣48)] using m16

/-- There is just one Gaussian cubic chart for cofactor 41 if the two square
coordinates may be interchanged. Its signed parameters have norm b. -/
theorem gaussian_fortyone {b x y : ℕ} (hb : Odd b) (hc : x.Coprime y)
    (he : x^4+y^4=b^3*41^2) :
    ∃ m n X Y : ℤ, m^2+n^2=(b:ℤ) ∧
      ((X=(x:ℤ) ∧ Y=(y:ℤ)) ∨ (X=(y:ℤ) ∧ Y=(x:ℤ))) ∧
      X^2= 9*(m^3-3*m*n^2)-40*(3*m^2*n-n^3) ∧
      Y^2= 40*(m^3-3*m*n^2)-(-9)*(3*m^2*n-n^3) := by
  obtain ⟨⟨m,n⟩,⟨e,f⟩,fac,bn,wn⟩ := powerful_descent hb (by decide : 0<41) hc he
  have ex := congrArg Zsqrtd.re fac
  have ey := congrArg Zsqrtd.im fac
  simp [pow_succ] at ex ey
  have norm : m^2+n^2=(b:ℤ) := by simpa [Zsqrtd.norm,pow_two] using bn
  have qr : e^2+f^2=41 := by simpa [Zsqrtd.norm,pow_two] using wn
  have lim {c d : ℤ} (eq : c^2+d^2=41) : -6≤c ∧ c≤6 := by
    constructor
    · by_contra! h
      nlinarith [sq_nonneg d,mul_nonneg (show 0≤ -c-7 by omega) (show 0≤ -c+7 by omega)]
    · by_contra! h
      nlinarith [sq_nonneg d,mul_nonneg (show 0≤c-7 by omega) (show 0≤c+7 by omega)]
  have ec := lim qr
  have fc := lim (by rw [add_comm]; exact qr : f^2+e^2=41)
  have cases : (e=-5 ∧ f=-4) ∨ (e=-5 ∧ f=4) ∨ (e=-4 ∧ f=-5) ∨ (e=-4 ∧ f=5) ∨ (e=4 ∧ f=-5) ∨ (e=4 ∧ f=5) ∨ (e=5 ∧ f=-4) ∨ (e=5 ∧ f=4) := by
    have table : ∀ i j : Fin 13, ((i.val:ℤ)-6)^2+((j.val:ℤ)-6)^2=41 →
        ((i.val:ℤ)-6,(j.val:ℤ)-6) ∈ [(-5,-4),(-5,4),(-4,-5),(-4,5),(4,-5),(4,5),(5,-4),(5,4)] := by
      decide +kernel
    let I : Fin 13 := ⟨(e+6).toNat,by omega⟩
    let J : Fin 13 := ⟨(f+6).toNat,by omega⟩
    have ie : (I.val:ℤ)-6=e := by dsimp [I];omega
    have jf : (J.val:ℤ)-6=f := by dsimp [J];omega
    have h := table I J (by simpa only [ie,jf] using qr)
    simpa only [ie,jf,List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] using h
  rcases cases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · refine ⟨m,n,x,y,by linear_combination norm,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ex
    · linear_combination ey
  · refine ⟨(-n),(-m),y,x,by linear_combination norm,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ey
    · linear_combination ex
  · refine ⟨n,m,y,x,by linear_combination norm,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ey
    · linear_combination ex
  · refine ⟨(-m),(-n),x,y,by linear_combination norm,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ex
    · linear_combination ey
  · refine ⟨(-m),(-n),x,y,by linear_combination norm,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ex
    · linear_combination ey
  · refine ⟨n,m,y,x,by linear_combination norm,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ey
    · linear_combination ex
  · refine ⟨(-n),(-m),y,x,by linear_combination norm,Or.inr ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ey
    · linear_combination ex
  · refine ⟨m,n,x,y,by linear_combination norm,Or.inl ⟨rfl,rfl⟩,?_,?_⟩
    · linear_combination ex
    · linear_combination ey

set_option maxRecDepth 20000 in
/-- The cofactor-41 chart meets only these 24 residue pairs modulo 48. -/
private theorem fortyone_classes {b : ℕ} {m n X Y : ℤ} (odd : b%2=1) (d3 : b%3≠0)
    (bn : m^2+n^2=(b:ℤ))
    (ex : X^2=9*(m^3-3*m*n^2)-40*(3*m^2*n-n^3))
    (ey : Y^2=40*(m^3-3*m*n^2)-(-9)*(3*m^2*n-n^3)) :
    (m%48,n%48) ∈ [(1,4),(1,24),(1,36),(1,40),(9,4),(9,40),(12,7),(12,31),(24,7),(24,31),(25,4),(25,24),(25,36),(25,40),(28,7),(28,15),(28,31),(28,39),(33,4),(33,40),(40,7),(40,15),(40,31),(40,39)] := by
  let chart (p : ℕ) (a c : ZMod p) : Prop :=
    (∃ X : ZMod p, X^2=9*(a^3-3*a*c^2)-40*(3*a^2*c-c^3)) ∧
    (∃ Y : ZMod p, Y^2=40*(a^3-3*a*c^2)-(-9)*(3*a^2*c-c^3))
  have point (p : ℕ) : chart p m n := by
    refine ⟨⟨(X : ZMod p),?_⟩,⟨(Y : ZMod p),?_⟩⟩
    · simpa using congrArg (fun z : ℤ => (z : ZMod p)) ex
    · simpa using congrArg (fun z : ℤ => (z : ZMod p)) ey
  have hn (p : ℕ) : (m : ZMod p)^2+(n : ZMod p)^2=(b : ZMod p) := by
    simpa using congrArg (fun z : ℤ => (z : ZMod p)) bn
  have t16 : ∀ a c : ZMod 16, chart 16 a c → (a^2+c^2).val%2=1 →
      ((a.val:ℤ),(c.val:ℤ)) ∈ [(1,4),(1,8),(8,7),(8,15),(9,4),(9,8),(12,7),(12,15)] := by unfold chart; decide +kernel
  have s16 := t16 _ _ (point 16)
  simp only [hn,ZMod.val_natCast,ZMod.val_intCast] at s16
  have m16 := s16 (by omega)
  have t9 : ∀ a c : ZMod 9, chart 9 a c → (a^2+c^2).val%3≠0 →
      ((a.val:ℤ)%3,(c.val:ℤ)%3) ∈ [(0,1),(1,0),(1,1)] := by unfold chart; decide +kernel
  have s9 := t9 _ _ (point 9)
  simp only [hn,ZMod.val_natCast,ZMod.val_intCast] at s9
  have m3 := s9 (by omega)
  have tab : ∀ a c : Fin 48, ((a.val:ℤ)%16,(c.val:ℤ)%16) ∈ [(1,4),(1,8),(8,7),(8,15),(9,4),(9,8),(12,7),(12,15)] →
      ((a.val:ℤ)%3,(c.val:ℤ)%3) ∈ [(0,1),(1,0),(1,1)] → ((a.val:ℤ),(c.val:ℤ)) ∈ [(1,4),(1,24),(1,36),(1,40),(9,4),(9,40),(12,7),(12,31),(24,7),(24,31),(25,4),(25,24),(25,36),(25,40),(28,7),(28,15),(28,31),(28,39),(33,4),(33,40),(40,7),(40,15),(40,31),(40,39)] := by decide +kernel
  have lift (t : ℤ) : ((t%48).toNat:ℤ)=t%48 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have take (t : ℤ) : (t%48).toNat < 48 := by have := lift t; omega
  have h := tab ⟨_,take m⟩ ⟨_,take n⟩
  simp only [lift] at h
  apply h
  · simpa only [Nat.cast_ofNat,Int.emod_emod_of_dvd _ (by decide : (16:ℤ)∣48)] using m16
  · simpa only [Nat.cast_ofNat,Int.emod_emod_of_dvd _ (by decide : (3:ℤ)∣48),
      Int.emod_emod_of_dvd _ (by decide : (3:ℤ)∣9)] using m3

/-- Doubling a bit pattern preserves every residue from the first period. -/
private theorem extend_bits (p : ℕ) (seed : ℕ) (k i : ℕ) (hi : i<p*2^k)
    (hit : seed.testBit (i%p)=true) :
    (Nat.rec (motive:=fun _ => ℕ) seed (fun k w => w ||| (w <<< (p*2^k))) k).testBit i=true := by
  induction k generalizing i with
  | zero => simpa [Nat.mod_eq_of_lt (by simpa using hi : i<p)] using hit
  | succ k ih =>
    simp only [Nat.testBit_or,Bool.or_eq_true]
    by_cases h : i<p*2^k
    · exact Or.inl (ih i h hit)
    · right
      rw [Nat.testBit_shiftLeft,Bool.and_eq_true]
      refine ⟨by simp;omega,ih _ ?_ ?_⟩
      · have eq : p*2^(k+1)=p*2^k+p*2^k := by ring
        omega
      · have eq : (i-p*2^k)%p=i%p := by
          calc (i-p*2^k)%p = (i-p*2^k+p*2^k)%p := (Nat.add_mul_mod_self_left _ _ _).symm
               _ = i%p := by rw [Nat.sub_add_cancel (by omega)]
        rwa [eq]

/-- Pack one full row period. The bit index is width times row plus column. -/
private theorem period_bit (w : ℕ) (f : ℕ → ℕ) (n i j : ℕ) (hi : i<n) (hj : j<w)
    (h : (f i).testBit j=true) :
    (Nat.rec (motive:=fun _ => ℕ) 0 (fun r v => v ||| (((f r) &&& ((1<<<w)-1)) <<< (w*r))) n).testBit
      (w*i+j)=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [Nat.testBit_or,Bool.or_eq_true]
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with lt|rfl
    · exact Or.inl (ih lt)
    · right
      have clip : ((1<<<w)-1).testBit j=true := by
        simpa only [Nat.shiftLeft_eq,one_mul,Nat.testBit_two_pow_sub_one] using decide_eq_true hj
      rw [Nat.testBit_shiftLeft,Bool.and_eq_true]
      exact ⟨decide_eq_true (by omega),by rw [show w*i+j-w*i=j by omega,Nat.testBit_and,h,clip];rfl⟩

private theorem sheet_bit (w p k : ℕ) (f : ℕ → ℕ) (i j : ℕ) (hi : i<p*2^k) (hj : j<w)
    (h : (f (i%p)).testBit j=true) :
    let base := Nat.rec (motive:=fun _ => ℕ) 0 (fun r v => v ||| (((f r) &&& ((1<<<w)-1)) <<< (w*r))) p
    (Nat.rec (motive:=fun _ => ℕ) base (fun h v => v ||| (v <<< ((w*p)*2^h))) k).testBit (w*i+j)=true := by
  intro base
  have hp : 0<p := by by_contra! e; simp [show p=0 by omega] at hi
  have bound (t N : ℕ) (lt : t<N) : w*t+j<w*N := calc
    w*t+j < w*t+w := Nat.add_lt_add_left hj _
    _ = w*(t+1) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ lt
  have eq : (w*i+j)%(w*p)=w*(i%p)+j := by
    have de : w*i+j = (w*(i%p)+j)+(w*p)*(i/p) := by
      calc w*i+j = w*(i%p+p*(i/p))+j := by rw [Nat.mod_add_div]
           _ = _ := by ring
    rw [de,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (bound _ _ (Nat.mod_lt _ hp))]
  apply extend_bits
  · simpa only [Nat.mul_assoc] using bound _ _ hi
  · rw [eq]; exact period_bit w f p _ j (Nat.mod_lt _ hp) hj h

/-- A row containing every column except possibly one needs a single
residue check. For any other row, check every column omitted by its mask. -/
private theorem sparse_row_covers (p row j : ℕ) (pass : ℕ → Bool) (hj : j<p) (hit : pass j=true) :
    let clip := (1<<<p)-1
    let missing := (clip-row).log2
    let entry (c : ℕ) := row.testBit c || !(pass c)
    (if (row ||| (1<<<missing)) == clip then entry missing else (List.range p).all entry) = true →
      row.testBit j=true := by
  intro clip missing entry ok
  by_cases eq : (row ||| (1<<<missing))=clip
  · rw [if_pos (beq_iff_eq.mpr eq)] at ok
    by_cases same : j=missing
    · subst j
      simpa only [entry,hit,Bool.not_true,Bool.or_false] using ok
    · have full : clip.testBit j=true := by
        simpa only [clip,Nat.shiftLeft_eq,one_mul,Nat.testBit_two_pow_sub_one] using decide_eq_true hj
      have other : ((1:ℕ)<<<missing).testBit j=false := by
        simp [Nat.shiftLeft_eq,Ne.symm same]
      simpa only [←eq,Nat.testBit_or,other,Bool.or_false] using full
  · rw [if_neg (fun e => eq (beq_iff_eq.mp e))] at ok
    have t := List.all_eq_true.mp ok j (List.mem_range.mpr hj)
    simpa only [entry,hit,Bool.not_true,Bool.or_false] using t

/-- Check the two cubics modulo each prime. The rectangular certificate intersects
periodic masks in strips of 256 rows and requires each intersection to be zero. -/
private theorem grid_sieve (realNeg cross : ℤ) (width origin height : ℕ) (classes : List (ℤ × ℤ))
    (gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ)) :
    let F (m n : ℤ) := (-realNeg)*(m^3-3*m*n^2)-cross*(3*m^2*n-n^3)
    let G (m n : ℤ) := cross*(m^3-3*m*n^2)-realNeg*(3*m^2*n-n^3)
    let res (a : ℤ) (p : ℕ) := (a%(p:ℤ)).toNat
    let seed (code p i : ℕ) := (code >>> (p*i)) &&& ((1 <<< p)-1)
    let valid (g : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :=
      let (p,inv,k,v,sq,code) := g
      decide (1<p ∧ width+p≤p*2^k ∧ height+p≤p*2^v ∧ (48*inv)%p=1) &&
      (List.range p).all (fun z => sq.testBit (z^2%p)) &&
      (List.range p).all (fun i =>
        let row := seed code p i
        let clip := (1<<<p)-1
        let missing := (clip-row).log2
        let entry (j : ℕ) :=
          let a := res (F i (48*(j:ℤ))) p
          let b := res (G i (48*(j:ℤ))) p
          row.testBit j || !(decide (a≠0 ∨ b≠0) && sq.testBit a && sq.testBit b)
        if (row ||| (1<<<missing)) == clip then entry missing else (List.range p).all entry)
    let sheets (c : ℤ × ℤ) := gates.map (fun g =>
      let (p,inv,k,v,_,code) := g
      let wave (i : ℕ) :=
        let s := seed code p (res (48*(i:ℤ)+c.1-origin) p)
        (Nat.rec (motive:=fun _ => ℕ) s (fun h t => t ||| (t <<< (p*2^h))) k) >>> res ((c.2-origin)*inv) p
      let base := Nat.rec (motive:=fun _ => ℕ) 0 (fun r t => t ||| ((wave r &&& ((1<<<width)-1)) <<< (width*r))) p
      (p,Nat.rec (motive:=fun _ => ℕ) base (fun h t => t ||| (t <<< ((width*p)*2^h))) v))
    let plane (c : ℤ × ℤ) (lo : ℕ) := (sheets c).foldl (fun bits g =>
      bits &&& (g.2 >>> (width*(lo%g.1)))) ((1 <<< (width*height))-1)
    0<height → gates.all valid=true →
    (∀ c ∈ classes, (List.range (width/height+1)).all (fun t => plane c (height*t) == 0)=true) →
    ∀ m n X Y : ℤ, X.natAbs.Coprime Y.natAbs →
    X^2=F m n → Y^2=G m n → ∀ c ∈ classes, ∀ i j : ℕ, i<width → j<width →
    m=48*(i:ℤ)+c.1-origin → n=48*(j:ℤ)+c.2-origin → False := by
  intro F G res seed valid sheets plane tall good empty m n X Y cop ex ey c cm i j hi hj me ne
  have reduced (a : ℤ) {p : ℕ} (hp : 0<p) : (res a p : ℤ)=a%(p:ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by exact_mod_cast hp.ne'))
  have small (a : ℤ) {p : ℕ} (hp : 0<p) : res a p<p := by
    have := reduced a hp
    have := Int.emod_lt_of_pos a (by exact_mod_cast hp : (0:ℤ)<p)
    omega
  have congr (a : ℤ) {p : ℕ} (hp : 0<p) : (res a p : ℤ) ≡ a [ZMOD (p:ℤ)] := by
    rw [reduced a hp]; exact Int.mod_modEq _ _
  let lo := height*(i/height)
  let r := i%height
  have split : r+lo=i := Nat.mod_add_div _ _
  have rh : r<height := Nat.mod_lt _ tall
  have hit : ∀ g ∈ sheets c, (g.2 >>> (width*(lo%g.1))).testBit (width*r+j)=true := by
    intro g member
    obtain ⟨⟨p,inv,k,v,sq,code⟩,mem,rfl⟩ := List.mem_map.mp member
    have test := List.all_eq_true.mp good _ mem
    change (decide (1<p ∧ width+p≤p*2^k ∧ height+p≤p*2^v ∧ (48*inv)%p=1) && _ && _)=true at test
    simp only [Bool.and_eq_true,decide_eq_true_eq] at test
    obtain ⟨⟨⟨pp,cover,vcover,inverse⟩,quadratic⟩,table⟩ := test
    have hp : 0<p := by omega
    let off := res ((c.2-origin)*inv) p
    let col := (j+off)%p
    have shift : (48:ℤ)*(inv:ℤ) ≡ 1 [ZMOD (p:ℤ)] :=
      Int.natCast_modEq_iff.mpr (show 48*inv ≡ 1 [MOD p] from inverse.trans (Nat.mod_eq_of_lt pp).symm)
    have left : (res m p : ℤ) ≡ m [ZMOD (p:ℤ)] := congr _ hp
    have right : 48*(col:ℤ) ≡ n [ZMOD (p:ℤ)] := by
      have base : (col:ℤ) ≡ (j:ℤ)+(off:ℤ) [ZMOD (p:ℤ)] :=
        Int.natCast_modEq_iff.mpr (Nat.mod_modEq _ _)
      have s := (congr ((c.2-origin)*inv) hp).mul_left 48
      have t := shift.mul_left (c.2-origin)
      have o : (48:ℤ)*off ≡ c.2-origin [ZMOD (p:ℤ)] := by
        calc (48:ℤ)*off ≡ 48*((c.2-origin)*inv) [ZMOD (p:ℤ)] := s
             _ = (c.2-origin)*(48*inv) := by ring
             _ ≡ (c.2-origin)*1 [ZMOD (p:ℤ)] := t
             _ = c.2-origin := by ring
      calc (48:ℤ)*col ≡ 48*((j:ℤ)+off) [ZMOD (p:ℤ)] := base.mul_left 48
           _ = 48*(j:ℤ)+48*off := by ring
           _ ≡ 48*(j:ℤ)+(c.2-origin) [ZMOD (p:ℤ)] := o.add_left _
           _ = n := by rw [ne];ring
    have u := (left.pow 3).sub (((left.mul (right.pow 2)).mul_left 3))
    have vcong := (((left.pow 2).mul right).mul_left 3).sub (right.pow 3)
    have f : F (res m p) (48*(col:ℤ)) ≡ F m n [ZMOD (p:ℤ)] := by
      dsimp only [F]; convert (u.mul_left (-realNeg)).sub (vcong.mul_left cross) using 1 <;> ring
    have g' : G (res m p) (48*(col:ℤ)) ≡ G m n [ZMOD (p:ℤ)] := by
      dsimp only [G]; convert (u.mul_left cross).sub (vcong.mul_left realNeg) using 1 <;> ring
    have sqhit (Z : ℤ) {a : ℤ} (he : a ≡ Z^2 [ZMOD (p:ℤ)]) : sq.testBit (res a p)=true := by
      have h := List.all_eq_true.mp quadratic (res Z p) (List.mem_range.mpr (small Z hp))
      have eq : (res Z p)^2%p=res a p := by
        have w := ((congr Z hp).pow 2).trans he.symm
        dsimp only [Int.ModEq] at w
        apply Int.natCast_inj.mp
        simpa only [Int.natCast_mod,Nat.cast_pow,reduced a hp] using w
      simpa only [eq] using h
    rw [←ex] at f
    rw [←ey] at g'
    have nonzero : res (F (res m p) (48*(col:ℤ))) p≠0 ∨
        res (G (res m p) (48*(col:ℤ))) p≠0 := by
      by_contra! h
      have div {a Z : ℤ} (hz : res a p=0) (e : a ≡ Z^2 [ZMOD (p:ℤ)]) : p∣Z.natAbs^2 := by
        have z : a%(p:ℤ)=0 := by rw [←reduced a hp,hz];rfl
        have d : (p:ℤ) ∣ Z^2 := Int.dvd_of_emod_eq_zero (Eq.trans (show Z^2%(p:ℤ)=a%(p:ℤ) from e.symm) z)
        have dn := Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr d)
        simpa only [Int.natAbs_pow] using dn
      exact (Nat.not_coprime_of_dvd_of_dvd pp (div h.1 f) (div h.2 g')) ((cop.pow_left 2).pow_right 2)
    let pass (j : ℕ) :=
      let a := res (F (res m p) (48*(j:ℤ))) p
      let b := res (G (res m p) (48*(j:ℤ))) p
      decide (a≠0 ∨ b≠0) && sq.testBit a && sq.testBit b
    have actual : pass col=true := by
      simp only [pass,nonzero,decide_true,sqhit X f,sqhit Y g',Bool.true_and]
    have cell := sparse_row_covers p (seed code p (res m p)) col pass (Nat.mod_lt _ hp) actual
      (List.all_eq_true.mp table _ (List.mem_range.mpr (small m hp)))
    let wave (t : ℕ) := (Nat.rec (motive:=fun _ => ℕ) (seed code p (res (48*(t:ℤ)+c.1-origin) p))
      (fun h w => w ||| (w <<< (p*2^h))) k) >>> off
    have index : (lo%p+r)%p=i%p := by rw [Nat.mod_add_mod, Nat.add_comm lo r,split]
    have hitrow : (wave ((lo%p+r)%p)).testBit j=true := by
      have cong : (48:ℤ)*(i%p:ℕ)+c.1-origin ≡ m [ZMOD (p:ℤ)] := by
        rw [me]
        exact (((Int.natCast_modEq_iff.mpr (Nat.mod_modEq i p)).mul_left 48).add_right c.1).sub_right _
      have same : res (48*(i%p:ℕ)+c.1-origin) p=res m p := congrArg Int.toNat cong
      dsimp only [wave]
      rw [index,same,Nat.testBit_shiftRight]
      apply extend_bits
      · have := small ((c.2-origin)*inv) hp
        dsimp only [off];omega
      · simpa only [col,Nat.add_comm] using cell
    have lim : lo%p+r < p*2^v := by have := Nat.mod_lt lo hp;omega
    have b := sheet_bit width p v wave (lo%p+r) j lim hj hitrow
    rw [Nat.testBit_shiftRight,show width*(lo%p)+(width*r+j)=width*(lo%p+r)+j by ring]
    exact b
  have all (gs : List (ℕ × ℕ)) (v : ℕ) (hv : v.testBit (width*r+j)=true)
      (h : ∀ g ∈ gs, (g.2 >>> (width*(lo%g.1))).testBit (width*r+j)=true) :
      (gs.foldl (fun bits g => bits &&& (g.2 >>> (width*(lo%g.1)))) v).testBit (width*r+j)=true := by
    induction gs generalizing v with
    | nil => exact hv
    | cons g gs ih =>
      apply ih
      · simp only [Nat.testBit_and,hv,h _ List.mem_cons_self,Bool.true_and]
      · exact fun g hg => h g (List.mem_cons_of_mem _ hg)
  have pos : width*r+j<width*height := calc
    width*r+j < width*r+width := Nat.add_lt_add_left hj _
    _ = width*(r+1) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ rh
  have alive : (plane c lo).testBit (width*r+j)=true := all _ _
    (by simpa only [Nat.shiftLeft_eq,one_mul,Nat.testBit_two_pow_sub_one] using decide_eq_true pos) hit
  have cleared := List.all_eq_true.mp (empty c cm) (i/height)
    (List.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hi.le)))
  rw [beq_iff_eq.mp cleared] at alive
  simp at alive

set_option maxRecDepth 16000 in
private theorem zero_seventeen_grid :
    ∀ m n X Y : ℤ, X.natAbs.Coprime Y.natAbs →
    X^2= -15*(m^3-3*m*n^2)-8*(3*m^2*n-n^3) →
    Y^2= 8*(m^3-3*m*n^2)-15*(3*m^2*n-n^3) →
    ∀ c ∈ ([(8,23),(8,47),(17,8),(17,20),(41,8),(41,20),(44,23),(44,47)] : List (ℤ × ℤ)), ∀ i j : ℕ, i<19556 → j<19556 →
    m=48*(i:ℤ)+c.1-469344 → n=48*(j:ℤ)+c.2-469344 → False := by
  let gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
    (5,2,12,6,0x13,0xc08592),
    (7,6,12,6,0x17,0x18a122450368),
    (11,3,11,5,0x23b,0x1254105433c39140800240063404000),
    (13,3,11,5,0x161b,0x1212000d028c300010008004002618a0500064249e4),
    (17,11,11,5,0x1a317,0x1a0b973a0c173a74162e74e82e5ce8105cf9d050b9d3a0b973a14173e74102e74e82e5ce8),
    (19,2,11,4,0x30af3,0x2581130241460440a1905220e804065408b0411809055804a018c030921108401e034900720930408888530af2),
    (23,12,10,4,0x5335f,0x166666b1e1e3707e0e5ab56900000ff003f02004199ce646d9b6100002810081557aa91cf38800c009000096b4b58020404b6db400240110002210008402100800000),
    (29,26,10,4,0x13d122f3,0x20201422e4142180451ad420048308000a2200440702000822830d04662404300a4020d9e84c00e70a21382016204004591c889c4d10410234000e42287380190bcd82012c06101213105861a20800207011002228000860900205ac5100c21413a614020213d122f2),
    (31,11,10,4,0x121d47b7,0x1268911818494e042380220196a104913b206400607400085802978c11c6481d38100310f4d0400c00120d81400152000a6484231caa00860400b5a09215161404005d1054280866301c9805d1048048810c0d20028a4030881400198829508291a0a08204c12821018262701419024044840142280000000),
    (37,27,10,3,0x165e211e9b,0xe4233131c406004e00c27e05690a35c423e801520812019600000c8c0faa51c088c1001113f080c0cba22929c96c3949870a52c9a98512401121023134040020cc02144100ee9a045951814100803201948800800894c02600804140e54d102cba80411420198200101646204244032450cac9a52870c94e1b49ca4a22e9818087c44400418981c52af81098000034c0240825420be211d6284b503f210039003015c646621389a1dee164),
    (41,6,9,3,0x1b382b50737,0xa011a8203031020042d1481280199a014842298084283b22000410a0e1b2028289b102220264b0042018028008f4860310015149c47083002e00e29300188248125c03908112125041ac82485380010d061005400a0d660050202b9815010b506110050089c0d81c880500443056840540cea02050033582801500430584000e509209ac10524244084e01d2409208c0064a3803a00608711c94540046030978800a00c0210069320222046c8a0a026c382841000226e0a1080ca2109402ccc00a40945a100204606020ac40280000000000),
    (43,26,9,3,0x35883a3ee53,0x1b01400687442214a0040905200c8414011a3b46040300004085d225c40841298a26420240100008182092c8d2884263069944710005c15a0a040970060301409847102d808a5213200db10806169a2c11c201cc8198248818150b2d080a0011151e08052200032206002840e20c513001c44640204217210110524738610331c02042c4b1c0640108103d40788248008000180412c11006010524840181003c41004a09835125208204202a81822a20081000311d400114542450b030d0a21581474022043108000817816b4e4910240400581049120ba023b008b45500c29080c000000000000),
    (47,1,9,3,0x4351b2753df,0xc600601402200509c00021041026404a00c0000110241c50694914244481009220414202008320430d080020800a8140e602100009188164918488b8c9080195242010800c904112c0502a5c682040802c00863110858a351204000222402060106006803108054140648411f0100ba4921c0e00920811000ec0400604540f0c99094053722212410042821800140c090a2001881032658ac42504000424034400628100ba882012405c0601ca52303a5022d0950c111010602120920300e897104800e00140a20805544637010088d01884001000128c808be9040900123c162083031c9443a410421d28005400fa9c4006a290108005244a9804598003e803831a10e808ca10b438ac3120211800000000000),
    (53,21,9,3,0x12dd703303aed3,0x51aa2e9084130218180022200c00080aa180810881c06092ec8580202e000824148a06664f0428422e06561300ca000c9000562010a20138619d130a10c64d4488347cc0642240429a000110a0808698860b608850782d480881800002018161d512e130070018b176504442bcc2181640004a070840243201012400421200a088942020011640404800a008849210a004005a800c0010410c931f8408a10888397c12e810080a400070200a28020700012808040ba41f4e0888428810fc64984104001800ad00100284249088028009010134400202148882802421001240402612010870290001340c219ea1110537468c00700643a455c340c0200000c088095a0f05088368308cb080828440002ca1012213019f16089159318428645cc30e40228402350004980029806435303a210a1079333028941208003a0200d09ba48301c0884080c2a80800180222000c0c20641084ba2ac500000000000000),
    (59,16,9,3,0x22b62183e7b92bb,0x1728e12f8000102c204a0400a26980184d12cf0024a09d8113081090a8ba916739420228884203a0804c030c00518142c5302ac9a0a016240805004073301e6a410817041483400084030703100001440cce4138208188358b450058488a0080282204a018011886b038a10cc0c9013961b80420e3202e701d0902888684010a4000b9328060445a0229d64058bc01a8812d1806200471a32b0885c48a41120a286c78000986c21a8800a2c014628000111048b158081d85448168c58bc430208000d6d0ad10d4302069692641b08a1006487c003c6d49084870001042600c4b0204040a445212080c9010820100590000990918200085840e0432480e22d4180b0552cc042511489b82282810342215000154402604082903940061180100141902800100882f07500816143588a683044084889800240512200448046a000911224062114c2998805293204887458404b1a308006806d4002c2099b20346a00520a1185c1d859010c469c030005402100ac81c9812085355010c298504080149449831c10052e040240308030c90010a0ce1808c0012104e2090a0101dc412054044151c5ac03081200820000000000000000),
    (61,14,9,3,0x1713e6940a59f23b,0x1180c8285a2c7254158fc90b071c66119117240a275431163b05600b0b1245130b015f014261c4079417323692d66633673c8194548398862c17f0005f53538510143505d016b4b34e8d5a0126360b2f966480e1038fc00d22951215b5bd0043512040a8baf0222a60188a51030ab5b220d9020407c1b0ce414700688d9a7f00cd1c16289607bb15172068cd38c2dc20421db006204492b2c8de15a58d50984a420e1a6c64184a2561b83ca9c1520c399681202396dfe1051524f230b584100630a28b1d33f91710f04110fb840505ca06ca916c98d4a02322ad7c455d81178e86994446ab6ab1114cb0b8f440dd511f5aa26202958c9b44a9b029d05010ef84410784744fe65c68a286300410d6862792545043fdb4e20240b4ce182541ca9e0ec352290c131b2c3821290c8558d2d43d89a6a491023006dc21021da18e598b0274546ef0348a341c59807f2cd88b0071413986c1f010204d8226d6a86045288c032a2207ae8a81024561005ed6d42454a25801f8e043809334fa683632402d58b96696b405d056140450e5657d0007f41a308ce09514c09e73663335a4b6267414f011c321407d4068645124686803506e3446157228127444c4331c706849f8d415271a2d0a0980c4000000000000000),
    (67,7,9,3,0x359c281ba27ebc653,0x42200401286862ccd001300510b41490410900c5c0024501122250428324436002ad34080805850008626429808030c4022ca10409610a50c8010cb00240640480b0041c20085441003398c002206f01260b310c130680380411428020188001e09ca00605098e20200828310004a010018368314d8922082828360c5032c104090c10124e86c15801000053c215d000581411484a0a1100620939100e87010d1450031c1422000002864339008d014cac00071421310c09b18152802028344c11885502104e032503c360107284c00020c68c0001102533252940000918132116a0034840948c0030c405412e00cad000212502613090028612012019800d92008221251a03a11400408820a2210802ad330014408a42081335400446018e82182100344306201b3600a3808228046206804a69048c494000151581082a2282212800ce3800ba022402e80ce98002402068548d048110040cc518001e0620050a00000c87a0804ab828001603100c8805408806702143001028c04140023016a201747828c04a08201e41000040047700c891b0ac28004035024002848d0a0f500802500038c00083441608981228412011484120510482902308c22a20005865614022828c0805064290785442208074254360220a048004003341b60cc400401008d31811c804401a29124249426900306d0c41022835301422030c01002ca0e280542468008310208361022881268121162a0290042b8282980a00ca40984103002009331614100000000000000000),
    (71,37,9,3,0x1164729716b1d977f,0x4104024881346100001083881a008410404407210150004080482001204805c048014c12624082000950006010001d042100093102001b431ac11041d0a0a80009240010c82810408a0849018081022104348c9000400e000020842360469468a48180000021d38090060904070910b90609c10080814d10ad816650140c048008052100a244408028204324108048205d4090262801b810a0406400c0124307100a00600420140441001805106a5041000109045b16098c2809080e20c81a24271c20014214e41223a83220a9c2a0002080000e0030202806660000203063a0900a1520e901800e0100e0020a9022002268a0408b1a59810810ba040000211441211008d2009040220248c0280818d01516541018128248008460041483e0802a2074188890420e02315110a2e68922100890a050a96001284400920816900140000826311c0808150902004488001c0803138008c0594949c00b22088148009101004854186c80218a68220120e12812314521902082040d62200310024208560e80f84201503040400340082062820312a62112d61201010c15e54186a410404461500444002a0004300c138502108004020f00040004420016928622801088004c76e09c87442a618000e41a5028c0e6104040c180025422218002560011828222815008d998202684b648e4a0108049025410000238014040010245c48818008020c09c00127b922484218108004253040219580a025c200400aeb068d0008cc08a48890995802aa50001c0d421000160090e40041848a01794808604d4222312400fdc00e02022887c008817003018e2c18890848076022e1a60a1042c0e007044b4c063040c812220ca01164729716b1d977e)]
  apply grid_sieve 15 8 19556 469344 256 [(8,23),(8,47),(17,8),(17,20),(41,8),(41,20),(44,23),(44,47)] gates (by decide)
  · simp only [gates,List.all_cons,List.all_nil,Bool.and_eq_true]
    repeat' apply And.intro
    all_goals decide +kernel
  · intro c hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel


/-- The entire cofactor-17 range below the census cutoff is impossible. -/
theorem no_cofactor_seventeen {b x y : ℕ} (bound : b≤220261480241)
    (cop : x.Coprime y) (he : x^4+y^4=b^3*17^2) : False := by
  have odd : Odd b := by
    rcases Nat.even_or_odd b with h|h
    · have d := even_iff_two_dvd.mp h
      have q : 4∣b^3 := (pow_dvd_pow_of_dvd d 2).trans (pow_dvd_pow b (by decide : 2≤3))
      exact (not_four cop (he ▸ dvd_mul_of_dvd_left q _)).elim
    · exact h
  have unit (p : ℕ) (hp : p.Prime) (two : p≠2) (bad : p%8≠1) : b%p≠0 := by
    intro h
    have d := dvd_pow (Nat.dvd_of_mod_eq_zero h) (by decide : 3≠0)
    exact bad (prime_residue cop hp two (he ▸ dvd_mul_of_dvd_left d _))
  obtain ⟨m,n,X,Y,bn,orient,ex,ey⟩ := gaussian_seventeen odd cop he
  have xy : X.natAbs.Coprime Y.natAbs := by
    rcases orient with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simpa using cop
    · simpa using cop.symm
  obtain ⟨_,hit⟩ := chart_residues (Nat.odd_iff.mp odd)
    (unit 3 (by decide) (by decide) (by decide)) (unit 5 (by decide) (by decide) (by decide))
    (unit 13 (by decide) (by decide) (by decide)) bn ex ey
  have box {a c : ℤ} (hn : a^2+c^2=(b:ℤ)) :
      -469320≤a ∧ a≤469320 := by
    have bb : (b:ℤ)≤220261480241 := by exact_mod_cast bound
    constructor
    · by_contra! h
      nlinarith [sq_nonneg c,mul_nonneg (show 0≤ -a-469321 by omega) (show 0≤ -a+469321 by omega)]
    · by_contra! h
      nlinarith [sq_nonneg c,mul_nonneg (show 0≤a-469321 by omega) (show 0≤a+469321 by omega)]
  have index (a : ℤ) (h : -469320≤a ∧ a≤469320) :
      ∃ i : ℕ, i<19556 ∧ a=48*(i:ℤ)+a%48-469344 := by
    let i := ((a+469344)/48).toNat
    have e : (i:ℤ)=(a+469344)/48 := Int.toNat_of_nonneg (by omega)
    exact ⟨i,by omega,by omega⟩
  obtain ⟨i,hi,mi⟩ := index m (box bn)
  obtain ⟨j,hj,nj⟩ := index n (box (by rw [add_comm];exact bn : n^2+m^2=(b:ℤ)))
  exact zero_seventeen_grid m n X Y xy ex ey (m%48,n%48) hit i j hi hj mi nj

set_option maxRecDepth 16000 in
private theorem zero_fortyone_grid :
    ∀ m n X Y : ℤ, X.natAbs.Coprime Y.natAbs →
    X^2= 9*(m^3-3*m*n^2)-40*(3*m^2*n-n^3) →
    Y^2= 40*(m^3-3*m*n^2)-(-9)*(3*m^2*n-n^3) →
    ∀ c ∈ ([(1,4),(1,24),(1,36),(1,40),(9,4),(9,40),(12,7),(12,31),(24,7),(24,31),(25,4),(25,24),(25,36),(25,40),(28,7),(28,15),(28,31),(28,39),(33,4),(33,40),(40,7),(40,15),(40,31),(40,39)] : List (ℤ × ℤ)), ∀ i j : ℕ, i<14584 → j<14584 →
    m=48*(i:ℤ)+c.1-350016 → n=48*(j:ℤ)+c.2-350016 → False := by
  let gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
    (5,2,12,6,0x13,0x19482c),
    (7,6,12,6,0x17,0x18144890a3016),
    (11,3,11,5,0x23b,0x1112101c030950088006501210245c4),
    (13,3,11,5,0x161b,0x149200040021e046223103c0001000a49000361a),
    (17,11,10,5,0x1a317,0xd69034c5002a294c84060222000381386530e40e00022203010994a2a00519604b580000),
    (19,2,10,4,0x30af3,0x10b81040b108c8c04444a301848810858212a044381031120216025c0483802151388105102401a8b010930af2),
    (23,12,10,4,0x5335f,0x74200a15102004d0c4811315200128803823102090c280201b0911048201680442e000882c840701504140432051060180a6802000c981092100a8090e20017acca0),
    (29,26,9,4,0x13d122f3,0xa29b12408060c102201188130979c1708241a462a4703402b00c330000a8d39021c50001318001020c02288a63a0289448000009148a02e3288a2018204000c6400051c204e58a8000661806a0160712a312c1208741cf486408c4022041830081246ca2800000000),
    (31,11,9,4,0x121d47b7,0x8c0310002c0d0014b00d290288450104204208138c72080918900080cc0404a00052108120424099990380b87407a019805e020c101034992c128400850309990c4104c82008a00510300480302a8615470a0c143929819494a88454ab00000d1e40009e9a224459c008400cd40902b6087384180000000),
    (37,27,9,3,0x165e211e9b,0x11050020613d0c290bc3001120054482a5000208cd2cd4c489a75d023100480095216ef60400b0021141004c6100184b0300085045028203864d0c9464881fd1130d86310fc0101c084824e38c60e8d542922a362a24a1558b8318e39009081c0411f84630d86445fc089314985930c020a05105080060690c0043190041442006821037bb424480090046a05d72c891959a5988000052a0915002440069e84a185e030200504765e211e9a),
    (41,6,9,3,0x1b382b50737,0x1a95f1904c7f1904c7d4a84c7d4af8cbd4af8c8262f8c8263ea58263ea57c63ea57c641317c64131f524131f52be31f52be3209abe32098fab2098fa95f18fa95f190495f1904c7d1904c7d4af8c7d4af8c834af8c8263e8c8263ea57a63ea57c642a57c64131fc64131f52b131f52be32752be32098fe32098fa94098fa95f19fa95f1904c5f1904c7d4904c7d4af8c7d4af8c826af8c8263ea48263ea57c63ea57c641257c64131f564131f52be31f52be32092be32098fa32098fa95f98fa95f190295f1904c7f1904c7d4ae4c7d4af8c8),
    (43,26,9,3,0x35883a3ee53,0x4c822100249230521007890330094351001609300b1b10009258260103a001610d640a0411901027a2811a26c42440800801600da800c404180e028278a42401390000208ec012c0103803280014e90020848a462008028a80810d1480b88061286405524807730510421428100a9014a04264554801805188a284012022088838401094524220408b10970df06001880940a110361924a03053140c90d0271408e54a21000040402840fa8a0800a30965e2171048103c28d1002820860184110900236942218474204060c041ba014061120380cc0440c2480414301808286119180000000000),
    (47,1,9,3,0x4351b2753df,0x30040603b680a0502a29a2002248b436082224620b30200388641c5042288068e106044c0d0a101840426869016042251210c8a8000ad48c01c1402c1352008c42e40c00a144900850c4036b210d000f1080034429210b22090049e401d0820888865c0842c312324006440c4513080280044f910d608407c401098820450212d40902803828e10047610885814b148021980690800429b2088c08a8c1125042b80d120018442a09700a0820590328604190d06844424aa490000b8408048a8ad4120600e08e8408619b8401020c2128658050a8ba0408025081c9092807002218025322a082ee080803892e004254843bc0840108031484570103409c04204823882040418bc461002e102246a7bcae4d8ac20),
    (53,21,9,3,0x12dd703303aed3,0x582030010003b9000412df3404b0c890de2201000800040458a2e191a0329484482400000047208260c00000034650674314911102094002018201800080100c2218820408008220c538515d008344244002000a051bb022850392300800004c02280e122000203040304500000300c1048721a193e80755407a00a1120174c90b0452159c2040b49ca106a21028cb03a8088c080d1b5a1842220060041020013023008801181ac80d02743617205809ac0c000880620640020410030022211c2d6c580818880ae0698a0422b0429c9681021cd42510684997402442802f0155700be4c2c2709001806000005106010602000224380a20190000088624e050a206e85028002001123160805d450e508220800810208c221804008000c020c020014822444494617305216000000183208271000000120d1094a602c4c3828d101000080140223d84898690167da410004ea0004006020d02d228fccfc512c),
    (59,16,8,3,0x22b62183e7b92bb,0x4000241a6002220cd14969181040840600029060260040520c4280020086004024201a00300e643518019c020060862042510004813c41909a0c104000615a8000241488a6006cc01c25062a20c040f430160022045108080080791a3583120102c8204a4a032704ce020004042408524008801092001210180018114084ca0ed894804202000a8b01108004805100000806e0434404448020204088800a81000468051c560044963084e22009918097408007202100e10001620820004149040408209061100408240088510c04000248025416100350402006b432a13a0868041cc209889c8320c00470c84509257800a628332414040501bd0000c040802073024050c80200a0809428426ec0520110aa2e00990b80060802f04406869b081c50ef20450201130850000000988700002a7462325520129549a084303a38200c132009c04050242258020040024a04c8000c091142b0f05400a6001c150a04000038400018a0005808115cd00831a0a090140841100098a8cc258640880844400a08005a00324160b5030a820304d106112114b42850422c034172a108184800000a18900464140914cda5d49de7c1846d44),
    (61,14,8,3,0x1713e6940a59f23b,0x143020a81030a000103402000a002c15450c29002008012c3400084d18000012054800025501401100002994041402820030422460000004212b004406051442841000254040b0184000000714600c24210001400ca404090c0482008418010304d1020b024008260c0202050510c00004515050451010441d0008000080293400981000011114065020200580e000148682828408410212142011a320088010008022640110306801109006110218010102110412160010009030283816000000680240011e104410a11461400080122041400980500c02a000080460c44008020912400550012448200801118310080002a0180500c8014102240080014314428411043c4001200b000000340e0a0604800400342410442040400c2044300484400b060440132200800400880262c402142420410810a0a0b094000380d00202053014444000040c80164a00800008005c11040451050545100001845050202018320801206820459060400c1080209018481012980140004212180314700000010c06810152000410a114503011006a42100000031221060020a0141014ca000044014055200009502400000c590800161a400802004a1851541a002800201604000286040a820614000000000000000),
    (67,7,8,3,0x359c281ba27ebc653,0x503801c080444a11044023022790024968228c26440020351d601212008ca115200098074a20c05044a6a097105810000e004027a12c0980001a38065ce0160028220a001112414991a140378000450020b208802834302088902d8980022920a901e221b198c5091204c280048808802109cd081112c000081cee01040031e42842401005084008a4031284411c02c049020c4820c5682040e5d001a005040088e580390a060c2128001861821420c9049109204483010920c1240129049203098107a20001809810d2850802200c41a0090ac0024007a200c002851a540c8420a9184004c02b0a9113231532540018a0400040109183600a31d08a620384180096429dc00a8802110052d342a030460600883030214371208c20042890264010750142088600c02c60841004c0060020000a9ec3a1431d0422080248a4a06000842682a48421121111c20082c04501040198168705094508a9a232e000060ca0490c4ae000208d80420be122400f1020c0a3c8116084c084803ab740200904068190900828800d5143484a04820800274f00126109a120a08220252282220205cc1980085c159850000f12c291001d00c510a81ce100455040a0950b8081c48060808405100b815104006444090241044428452448c6135022050680612448418e80a0488c00086320610882d004542145506c400012b07268140c4040054b20001a010068074a608348400030ba10c0040938201197002035088207420110a481a8a00c816040a80000000000000000),
    (71,37,8,3,0x1164729716b1d977f,0x4704081081d040020810bd80180040030060050849100042920a80010845514280014a0e024002066900004a000019026092412320485101a2580501103b88022100401099330102880c430002820e025e20841000000c22108068820852217e209020820801c3028614038601420594200555704019810081c406b3824c00002c0741828040408024a4838280100838882b094431009d0004426002503a0505160400408020a430441154040068120300944204461d010024a3c8c20214caea0600609102e0341008173a09a8068042240a40880020a42005080812a030a5c8160001188c889b0a000ea002920002452010a809414a2382a01c24040028210740a8041ad800a0022004410500286e4420b445182012a042200410c40461259206aa04284420c80d42c0c00465a8c980b00420e519221102088012b2041c80002200193830940840310116003208029008200d200078d10c31451a21019310029000208692147480800c1e059010840012183603f9200610980a002390026a72040a04011a506100084c436208002481012004de82a7102181c4021725086407414c40221c4020300405303c19011002004008240064108622001380006704c09300aa06b04491f06029342020aa8c04c25090420b504502648200005446084240682400300cd25b990488230246e00262410a3058102440014002215204900a980020811424101a0730a39462001003465140080050890f1c0b2850027a09081300228c481c9064042938882042cd034204000904c428188040314d81624434140a3236010c13610c084066a41a4a214008b804285040085b18a6605c33402c8a24818042506b4880e5820210800000000000000000)]
  apply grid_sieve (-9) 40 14584 350016 256 [(1,4),(1,24),(1,36),(1,40),(9,4),(9,40),(12,7),(12,31),(24,7),(24,31),(25,4),(25,24),(25,36),(25,40),(28,7),(28,15),(28,31),(28,39),(33,4),(33,40),(40,7),(40,15),(40,31),(40,39)] gates (by decide)
  · simp only [gates,List.all_cons,List.all_nil,Bool.and_eq_true]
    repeat' apply And.intro
    all_goals decide +kernel
  · intro c hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel


/-- The entire cofactor-41 range below the census cutoff is impossible. -/
theorem no_cofactor_fortyone {b x y : ℕ} (bound : b≤122475323887)
    (cop : x.Coprime y) (he : x^4+y^4=b^3*41^2) : False := by
  have odd : Odd b := by
    rcases Nat.even_or_odd b with h|h
    · have d := even_iff_two_dvd.mp h
      have q : 4∣b^3 := (pow_dvd_pow_of_dvd d 2).trans (pow_dvd_pow b (by decide : 2≤3))
      exact (not_four cop (he ▸ dvd_mul_of_dvd_left q _)).elim
    · exact h
  have unit (p : ℕ) (hp : p.Prime) (two : p≠2) (bad : p%8≠1) : b%p≠0 := by
    intro h
    have d := dvd_pow (Nat.dvd_of_mod_eq_zero h) (by decide : 3≠0)
    exact bad (prime_residue cop hp two (he ▸ dvd_mul_of_dvd_left d _))
  obtain ⟨m,n,X,Y,bn,orient,ex,ey⟩ := gaussian_fortyone odd cop he
  have xy : X.natAbs.Coprime Y.natAbs := by
    rcases orient with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · simpa using cop
    · simpa using cop.symm
  have hit := fortyone_classes (Nat.odd_iff.mp odd) (unit 3 (by decide) (by decide) (by decide)) bn ex ey
  have box {a c : ℤ} (hn : a^2+c^2=(b:ℤ)) :
      -349964≤a ∧ a≤349964 := by
    have bb : (b:ℤ)≤122475323887 := by exact_mod_cast bound
    constructor
    · by_contra! h
      nlinarith [sq_nonneg c,mul_nonneg (show 0≤ -a-349965 by omega) (show 0≤ -a+349965 by omega)]
    · by_contra! h
      nlinarith [sq_nonneg c,mul_nonneg (show 0≤a-349965 by omega) (show 0≤a+349965 by omega)]
  have index (a : ℤ) (h : -349964≤a ∧ a≤349964) :
      ∃ i : ℕ, i<14584 ∧ a=48*(i:ℤ)+a%48-350016 := by
    let i := ((a+350016)/48).toNat
    have e : (i:ℤ)=(a+350016)/48 := Int.toNat_of_nonneg (by omega)
    exact ⟨i,by omega,by omega⟩
  obtain ⟨i,hi,mi⟩ := index m (box bn)
  obtain ⟨j,hj,nj⟩ := index n (box (by rw [add_comm];exact bn : n^2+m^2=(b:ℤ)))
  exact zero_fortyone_grid m n X Y xy ex ey (m%48,n%48) hit i j hi hj mi nj

/-- Each coordinate is smaller in magnitude than a strict bound for the Euclidean norm. -/
private theorem signed_coordinate {u v h : ℤ} (hp : 0<h) (small : u^2+v^2<h^2) :
    -h<u ∧ u<h := by
  constructor
  · by_contra! he
    nlinarith [sq_nonneg v,mul_nonneg (show 0≤ -u-h by omega) (show 0≤ -u+h by omega)]
  · by_contra! he
    nlinarith [sq_nonneg v,mul_nonneg (show 0≤u-h by omega) (show 0≤u+h by omega)]

/-- A common divisor of the coordinates of W would divide the two square
coordinates of B³W². This also removes the axial representations at k=17². -/
private theorem multiplier_primitive {e f u v : ℤ} {x y : ℕ} (hc : x.Coprime y)
    (xx : (x:ℤ)^2=(e^2-f^2)*u-(2*e*f)*v) (yy : (y:ℤ)^2=(2*e*f)*u+(e^2-f^2)*v) :
    e.natAbs.Coprime f.natAbs := by
  apply Nat.coprime_of_dvd
  intro p hp de df
  obtain ⟨a,ea⟩ := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr de)
  obtain ⟨c,fc⟩ := Int.dvd_natAbs.mp (Int.natCast_dvd_natCast.mpr df)
  have dx : (p:ℤ) ∣ (x:ℤ)^2 :=
    ⟨(p:ℤ)*((a^2-c^2)*u-2*a*c*v),by rw [xx,ea,fc];ring⟩
  have dy : (p:ℤ) ∣ (y:ℤ)^2 :=
    ⟨(p:ℤ)*(2*a*c*u+(a^2-c^2)*v),by rw [yy,ea,fc];ring⟩
  have x2 : p∣x^2 := by exact_mod_cast dx
  have y2 : p∣y^2 := by exact_mod_cast dy
  exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt (hp.dvd_of_dvd_pow x2) (hp.dvd_of_dvd_pow y2)) hc

/-- The four sign and conjugation choices for W² give one chart, after
rotating B and, when needed, interchanging x and y. -/
private theorem fixed_cubic_chart (k h : ℕ) (A D : ℤ) (pos : 0<k) (hp : 0<h)
    (bound : (k:ℤ)<(h:ℤ)^2)
    (forms : ∀ i j : Fin (2*h+1), let e := (i.val:ℤ)-h; let f := (j.val:ℤ)-h
      e^2+f^2=(k:ℤ) → e.natAbs.Coprime f.natAbs →
      (e^2-f^2,2*e*f) ∈ [(-A,D),(A,-D),(-A,-D),(A,D)])
    {b x y : ℕ} (odd : Odd b) (hc : x.Coprime y) (he : x^4+y^4=b^3*k^2) :
    ∃ m n X Y : ℤ, m^2+n^2=(b:ℤ) ∧ X.natAbs.Coprime Y.natAbs ∧
      X^2=(-A)*(m^3-3*m*n^2)-D*(3*m^2*n-n^3) ∧
      Y^2=D*(m^3-3*m*n^2)-A*(3*m^2*n-n^3) := by
  obtain ⟨⟨m,n⟩,⟨e,f⟩,fac,bn,wn⟩ := powerful_descent odd pos hc he
  have ex := congrArg Zsqrtd.re fac
  have ey := congrArg Zsqrtd.im fac
  simp [pow_succ] at ex ey
  have xx : (x:ℤ)^2=(e^2-f^2)*(m^3-3*m*n^2)-(2*e*f)*(3*m^2*n-n^3) := by linear_combination ex
  have yy : (y:ℤ)^2=(2*e*f)*(m^3-3*m*n^2)+(e^2-f^2)*(3*m^2*n-n^3) := by linear_combination ey
  have norm : m^2+n^2=(b:ℤ) := by simpa [Zsqrtd.norm,pow_two] using bn
  have qr : e^2+f^2=(k:ℤ) := by simpa [Zsqrtd.norm,pow_two] using wn
  have boundE := signed_coordinate (by exact_mod_cast hp) (qr ▸ bound)
  have boundF := signed_coordinate (u:=f) (v:=e) (h:=(h:ℤ)) (by exact_mod_cast hp) (by rw [add_comm,qr]; exact bound)
  let i : Fin (2*h+1) := ⟨(e+h).toNat,by omega⟩
  let j : Fin (2*h+1) := ⟨(f+h).toNat,by omega⟩
  have ei : (i.val:ℤ)-h=e := by dsimp [i];omega
  have fj : (j.val:ℤ)-h=f := by dsimp [j];omega
  have choices := forms i j
  dsimp only at choices
  rw [ei,fj] at choices
  have candidates := choices qr (multiplier_primitive hc xx yy)
  simp only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at candidates
  rcases candidates with ⟨er,fr⟩|⟨er,fr⟩|⟨er,fr⟩|⟨er,fr⟩ <;> rw [er,fr] at xx yy
  · exact ⟨m,n,x,y,norm,by simpa using hc,xx,by linear_combination yy⟩
  · exact ⟨-m,-n,x,y,by linear_combination norm,by simpa using hc,
      by linear_combination xx,by linear_combination yy⟩
  · exact ⟨-n,-m,y,x,by linear_combination norm,by simpa using hc.symm,
      by linear_combination yy,by linear_combination xx⟩
  · exact ⟨n,m,y,x,by linear_combination norm,by simpa using hc.symm,
      by linear_combination yy,by linear_combination xx⟩

/-- The separate square tests modulo 16 and 9 give the chart classes modulo 48. -/
private theorem cubic_classes (A D : ℤ) (c16 c3 classes : List (ℤ × ℤ)) :
    let point (p : ℕ) (a c : ZMod p) : Prop :=
      (∃ X : ZMod p, X^2=(-A:ZMod p)*(a^3-3*a*c^2)-(D:ZMod p)*(3*a^2*c-c^3)) ∧
      (∃ Y : ZMod p, Y^2=(D:ZMod p)*(a^3-3*a*c^2)-(A:ZMod p)*(3*a^2*c-c^3))
    (∀ a c : ZMod 16, point 16 a c → (a^2+c^2).val%2=1 → ((a.val:ℤ),(c.val:ℤ)) ∈ c16) →
    (∀ a c : ZMod 9, point 9 a c → (a^2+c^2).val%3≠0 → ((a.val:ℤ)%3,(c.val:ℤ)%3) ∈ c3) →
    (∀ a c : Fin 48, ((a.val:ℤ)%16,(c.val:ℤ)%16) ∈ c16 → ((a.val:ℤ)%3,(c.val:ℤ)%3) ∈ c3 →
      ((a.val:ℤ),(c.val:ℤ)) ∈ classes) →
    ∀ {b : ℕ} {m n X Y : ℤ}, b%2=1 → b%3≠0 → m^2+n^2=(b:ℤ) →
      X^2=(-A)*(m^3-3*m*n^2)-D*(3*m^2*n-n^3) →
      Y^2=D*(m^3-3*m*n^2)-A*(3*m^2*n-n^3) → (m%48,n%48) ∈ classes := by
  intro point t16 t9 crt b m n X Y odd d3 bn ex ey
  have P (p : ℕ) : point p m n := by
    refine ⟨⟨(X:ZMod p),?_⟩,⟨(Y:ZMod p),?_⟩⟩
    · simpa using congrArg (fun z : ℤ => (z:ZMod p)) ex
    · simpa using congrArg (fun z : ℤ => (z:ZMod p)) ey
  have hn (p : ℕ) : (m:ZMod p)^2+(n:ZMod p)^2=(b:ZMod p) := by
    simpa using congrArg (fun z : ℤ => (z:ZMod p)) bn
  have h16 := t16 _ _ (P 16)
  have h9 := t9 _ _ (P 9)
  simp only [hn,ZMod.val_natCast,ZMod.val_intCast,Nat.cast_ofNat] at h16 h9
  have r16 := h16 (by omega)
  have r3 := h9 (by omega)
  have lift (t : ℤ) : ((t%48).toNat:ℤ)=t%48 := Int.toNat_of_nonneg (Int.emod_nonneg _ (by decide))
  have take (t : ℤ) : (t%48).toNat<48 := by have := lift t;omega
  have t := crt ⟨_,take m⟩ ⟨_,take n⟩
  simp only [lift] at t
  apply t
  · simpa only [Int.emod_emod_of_dvd _ (by decide : (16:ℤ)∣48)] using r16
  · simpa only [Int.emod_emod_of_dvd _ (by decide : (3:ℤ)∣48),
      Int.emod_emod_of_dvd _ (by decide : (3:ℤ)∣9)] using r3

/-- An empty signed Gaussian grid excludes the entire stated norm range. -/
private theorem exclude_fixed_cofactor (k B h width origin : ℕ) (A D : ℤ) (classes : List (ℤ × ℤ))
    (dims : 0<k ∧ 0<h ∧ (k:ℤ)<(h:ℤ)^2 ∧ 0<origin ∧ (B:ℤ)<(origin:ℤ)^2 ∧ (origin:ℤ)%48=0 ∧
      2*(origin:ℤ)=48*(width:ℤ))
    (forms : ∀ i j : Fin (2*h+1), let e := (i.val:ℤ)-h; let f := (j.val:ℤ)-h
      e^2+f^2=(k:ℤ) → e.natAbs.Coprime f.natAbs →
      (e^2-f^2,2*e*f) ∈ [(-A,D),(A,-D),(-A,-D),(A,D)])
    (residues : ∀ {b : ℕ} {m n X Y : ℤ}, b%2=1 → b%3≠0 → m^2+n^2=(b:ℤ) →
      X^2=(-A)*(m^3-3*m*n^2)-D*(3*m^2*n-n^3) →
      Y^2=D*(m^3-3*m*n^2)-A*(3*m^2*n-n^3) → (m%48,n%48) ∈ classes)
    (grid : ∀ m n X Y : ℤ, X.natAbs.Coprime Y.natAbs →
      X^2=(-A)*(m^3-3*m*n^2)-D*(3*m^2*n-n^3) →
      Y^2=D*(m^3-3*m*n^2)-A*(3*m^2*n-n^3) → ∀ c ∈ classes, ∀ i j : ℕ, i<width → j<width →
      m=48*(i:ℤ)+c.1-origin → n=48*(j:ℤ)+c.2-origin → False)
    {b x y : ℕ} (bound : b≤B) (cop : x.Coprime y) (he : x^4+y^4=b^3*k^2) : False := by
  obtain ⟨kp,hp,kh,op,bo,omod,wide⟩ := dims
  have odd : Odd b := by
    rcases Nat.even_or_odd b with ev|od
    · have d := even_iff_two_dvd.mp ev
      have q : 4∣b^3 := (pow_dvd_pow_of_dvd d 2).trans (pow_dvd_pow b (by decide : 2≤3))
      exact (not_four cop (he ▸ dvd_mul_of_dvd_left q _)).elim
    · exact od
  have unit : b%3≠0 := by
    intro z
    have d := dvd_pow (Nat.dvd_of_mod_eq_zero z) (by decide : 3≠0)
    exact (by decide : 3%8≠1) (prime_residue cop (by decide : Nat.Prime 3) (by decide)
      (he ▸ dvd_mul_of_dvd_left d _))
  obtain ⟨m,n,X,Y,bn,xy,ex,ey⟩ := fixed_cubic_chart k h A D kp hp kh forms odd cop he
  have cs := residues (Nat.odd_iff.mp odd) unit bn ex ey
  have bb : (b:ℤ)<(origin:ℤ)^2 := lt_of_le_of_lt (by exact_mod_cast bound) bo
  have index (v : ℤ) (hv : -(origin:ℤ)<v ∧ v<(origin:ℤ)) :
      ∃ i : ℕ, i<width ∧ v=48*(i:ℤ)+v%48-origin := by
    let i := ((v+origin)/48).toNat
    have vi : (i:ℤ)=(v+origin)/48 := Int.toNat_of_nonneg (by omega)
    exact ⟨i,by omega,by omega⟩
  obtain ⟨i,hi,mi⟩ := index m (signed_coordinate (by exact_mod_cast op) (bn ▸ bb))
  obtain ⟨j,hj,nj⟩ := index n (signed_coordinate (v:=m) (h:=(origin:ℤ)) (by exact_mod_cast op)
    (by rw [add_comm,bn];exact bb))
  exact grid m n X Y xy ex ey (m%48,n%48) cs i j hi hj mi nj

set_option maxRecDepth 16000 in
/-- Exclude the full cofactor-73 range using W=8+3i. -/
theorem no_cofactor_73 {b x y : ℕ} (bound : b≤83372455837) (cop : x.Coprime y)
    (he : x^4+y^4=b^3*73^2) : False := by
  let classes : List (ℤ × ℤ) := [(7,20),(7,32),(16,17),(16,41),(28,17),(28,41),(31,20),(31,32)]
  refine exclude_fixed_cofactor 73 83372455837 9 12032 288768 (-55) 48 classes
    (by decide +kernel) (by decide +kernel) ?_ ?_ bound cop he
  · apply cubic_classes (-55) 48 [(0,1),(0,9),(7,0),(7,4),(12,1),(12,9),(15,0),(15,4)] [(1,2)] classes <;> decide +kernel
  · let gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
      (5,2,12,6,0x13,0xc08592),
      (7,6,11,6,0x17,0x40bc039ad00),
      (11,3,11,5,0x23b,0x1090959507011210ea63c262185ca3a),
      (13,3,10,5,0x161b,0x149200040021e046223103c0001000a49000361a),
      (17,11,10,5,0x1a317,0xd69034c5002a294c84060222000381386530e40e00022203010994a2a00519604b580000),
      (19,2,10,4,0x30af3,0x1808480351288127102010a889070012e04042c81888887010950210b0c24409460602222119082058217030af2),
      (23,12,10,4,0x5335f,0xb050008c504c0022808c0421d0450520240c20b68004842242084095c60123300130816801200728938811448204168461806026814106098b60086509602800000),
      (29,26,9,4,0x13d122f3,0x20201422e4142180451ad420048308000a2200440702000822830d04662404300a4020d9e84c00e70a21382016204004591c889c4d10410234000e42287380190bcd82012c06101213105861a20800207011002228000860900205ac5100c21413a614020213d122f2),
      (31,11,9,4,0x121d47b7,0x4200a1143204808c131380a82504203050410252a105232000cc4148061102069001450091021cc02e88210cc6038e882a142c280800ad0490a810c08016118e55000014c90c0a000a91800241a87a68203a702006608e32400b0052f0303a00067640c804b50824847004402c24a70224d1223000000000),
      (37,27,9,3,0x165e211e9b,0x430301090005200002405280d0000240218c40000410a001000006140c01470008080082015440004141411041442002804a6048009181430000220000400202840008a000001a2001340040202040001210041004240001020201001640022c000002880010a0200100002200006140c48009032900a0021141044141410001154020800808007140181430000040028410000118c20120000580a5012000025000484060610000000000),
      (41,6,9,3,0x1b382b50737,0x1651c2138004586e054010033404400440cd805158b005aa50c00080941440800c10211440408949cf049262a40623348802c5100060180164800980810608024208830020094884b04202042048824a83a90d0480020412618410f03028d00002841436c18908848c1b61400a000058a0e078410c320102000905a4ae0a92088021020210690894802006088212008304080c80093400c03000c51a00896623012a3249079c94881001442041800811414808041852ad0068d4500d98100011016600c01503b0d1000e421c535b382b50736),
      (43,26,9,3,0x35883a3ee53,0x23e00c22a04420008c8d20216104110ace03004111761900440282a2824c2408c82b80020880423064034030100c98784601c94012cf1c4009212180ac01028610128a074094a8a123080cc38044846c11102d9120266484432a01400102a40f200a14cc002414930600110008301d21d60a2020081e069d2000523945010a418600ab00a1c2c0a066208120036840120a180b8802410085c448041212a304028010c0064846dc422cb0000000890502532c3800620402216020561544a37204402980712042018050890cc2882280c29084249b8228020008dd4842e550206200200000000000),
      (47,1,9,3,0x4351b2753df,0x1220a3c6d40aa90e2c88442219541c9280ac6461085c06403401c0a4806c21c331102350600094bec2701cb8140b082a081b211c3800271820015c006301201136d084815207882090015092718836aa280220109a90401115880172c56090cac24e2882864480e803e02020d01054300200041589ec34921d8822108200148582800d2860808914d982401ae120298c5e6400408c80618208408f9c80668723426005164050406091056480090041c4c0b8000444858b9368488a0044800400c4e6492a526470002648a03080146a341012ea00ba8588360a0004800c88538e00088402a308008ca020aa52c480280404f8a5304306030281d200201188600ca002318904101c004a0020512460800000000000),
      (53,21,8,3,0x12dd703303aed3,0x422e41c4824220a4c02c24000080910c0025021788e10816000e8082001066420521006232083f41601a533080608800140500c08e823a685409a00ac04042e443901220c520d020f00800029c016120400a4136741c480182402408888465c0962441044509162286451400908860f2c006c1400088909400041050a80c00031401102d2620002808504370400b0008810e04848212000451063aa260b000a00c0833c588402505301440008001140650520508d1e608180280068322ae3044100024209090384088006801076105080a0002325a0440146000180a85041000148488800141b005a783088480145130a23448511041123481d3108088120120c0095c17364128010043401ca000081782058251822404e113a10101a802c8150b2e2098818050140009830086652c03417e082623004210213304002082b80034084388e42052001844808000121a019286212091c13a2112dd703303aed2),
      (59,16,8,3,0x22b62183e7b92bb,0x90289a08425c82010c61580408200102b15490188220828632816880840528d80c805060bc0008a190224003c8410802c20854dc200880214808000ca18a010aa0b0204438242211010000017418111d0084a8410828087c1920a200221248028829023045020091044113a3002c20089040ec14928246822136344000b346010900800256e0034040030586408c0ba10010700b34028005453120454a50c1700020900005091416487513c000808400100404206781a683808048c093080b098218624028ac00113d045282070038810102909ac20690840446004444009046206046803101158020d040000c24c20490d000c006802c5020483aa1084449804800a02008c031a695173a0202000a002462091000822416005603018084200a40128c80050286c8508cc942000108186042068082004840082601d1400200462a0a8848226018018069d431245047014220100440608080035e8084300807263a0800f1426411082a041022c00110b4641c05084ca2400200a19601a4100191901c4e0012080028980914084a011085094030000e0284d018205000c4586a64803048009010902008729022b62183e7b92ba),
      (61,14,8,3,0x1713e6940a59f23b,0x40028050000c092408048014827b001040004098200000010102a0c0000820000840000144301888460124a2606262076308103004804204236b02b00480002108004040920936230c0610338006482d00a500090200001041100040010250020080400001070400002020040808410010001810100008110000800a53dc253004291808b12203220280002480002101040000242080200000de09807e008400000a080500202011110006232279b08642800308760802801005020040001a80007b41118c0000050302000500209144023c884c840e24607481040a9122911380162014023400e444a244a81040970312381099089e20114482005000206050000018c4416f0000ac00010020500400a00837086000a13086cf226230004444020200500828000010803f00c83d80000200821200001040420000920000a022602246880c4a1006521de52800800044080004040c000400410808100202000010704000010080200520400100044104000020480052805a093000e604301862364824810100084200009006a06b6210210090060408637023230322924031088c061140000108000208000182a040400000020c81000104006f2094009008124818000500a001000000000000000000)]
    apply grid_sieve (-55) 48 12032 288768 256 classes gates (by decide)
    · simp only [gates,List.all_cons,List.all_nil,Bool.and_eq_true]
      repeat' apply And.intro
      all_goals decide +kernel
    · intro c hc
      simp only [classes,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 16000 in
/-- Exclude the full cofactor-89 range using W=8+5i. -/
theorem no_cofactor_89 {b x y : ℕ} (bound : b≤73054083499) (cop : x.Coprime y)
    (he : x^4+y^4=b^3*89^2) : False := by
  let classes : List (ℤ × ℤ) := [(23,20),(23,32),(32,17),(32,41),(44,17),(44,41),(47,20),(47,32)]
  refine exclude_fixed_cofactor 89 73054083499 10 11262 270288 (-39) 80 classes
    (by decide +kernel) (by decide +kernel) ?_ ?_ bound cop he
  · apply cubic_classes (-39) 80 [(0,1),(0,9),(7,0),(7,4),(12,1),(12,9),(15,0),(15,4)] [(2,2)] classes <;> decide +kernel
  · let gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
      (5,2,12,6,0x13,0x19482c),
      (7,6,11,6,0x17,0x18144890a3016),
      (11,3,11,5,0x23b,0x888210384300a8446000288489023a),
      (13,3,10,5,0x161b,0x16da204dcebc3d0031088846007e1eb9d1026db49e4),
      (17,11,10,5,0x1a317,0x480200460c1c1080a315d00bc8c4c204010209189e805d462a0840c183900200901a316),
      (19,2,10,4,0x30af3,0x61bc0cd44e5220002000a001000204ab98280401518d840409074f21b95419797c51009000a0011c8d80000),
      (23,12,9,4,0x5335f,0x142102019000405044800150084f089008061286104088000709082ac042a860406100008c82340b1192420120301e48080a8020915483226808085e22300e7acca0),
      (29,26,9,4,0x13d122f3,0x404401a128871947060159006a020010d0282920420408036000a351a4802068437891101348838860206ec08825049840971474810c90520881bb020308e0896404448f610b020092c562800360081021024a0a058400202b004d4030714c708a42c0110100000000),
      (31,11,9,4,0x121d47b7,0x2020005804000ca5082a8370003822000403093320428e90004288a00202041014088002803085b325101d07242a2293a032c902202007d124294402000c2797001c0120211001a408000284600d40353459c5850498463d21590237060c2012020443876a1644a712410204110d06a3421d532180000000),
      (37,27,9,3,0x165e211e9b,0xe3233109c007200602c25a81f90817c423ac40120412a1130000069c0e2957c0888800831374c0c043e3693949442943864a7248a19593431021220130400202cc0208a100ca9a205975004020a07001129804900ca4400702820100774d022ca88042882019a0200106402242046364d4c289272930e14a11494e4b63e1018197446080088981f54a3814b000006442a41024031ae211f4084fc0ad212030027005c846626389a1dee164),
      (41,6,9,3,0x1b382b50737,0x1cdc00ece1007e3c7e009000120002280aaf550160d6b035ac1240000002401004080203988891119e6a314a3159029ce739408011002200010400020800018006000020400204000050028001d0d090b0ba0021021000271381c8e480101202000a83b0dc152541d86e0a900202404001389c0e47240042042000e86848585d000a00500001020010200003000c00008200010400022004400014e739ca04d4629462b3cc444888cf0200810040120000001201ad606b58340557aa80b2000240004003f1e3f00439b801d9c24c7d4af8c8),
      (43,26,9,3,0x35883a3ee53,0x280d020324501a61208071801c8c042c204b81a0006187851000b2400cc50042c11461803a0c18408822710c4006082648086a22006c2c1114008320558a8228009c00410c8c00210c1c928920c2a002900d48c8003280829524024412d270900405991800c8888c1302a0890180144234411a3484844e5004080c11043c800a820a0810940b6501605504442a180d009496e20298000058b90100b000202a78c61c160000325112c0223149388550052001298011992205441008e19442013240269d020007820ae4480080aa50458009280140886a0a031c2804486122c18049100000000000),
      (47,1,8,3,0x4351b2753df,0x80002002941c4002208804aa2844100004903020000c263803904068c5840440101821900200804a83000528060a0228008a100c05400a256908b046e4c2802a209000b01200a42260643415a10008262002ba800b00196a000a0033044210588048800604c000284048585407384c099a2080642681108218000a4230145632521293105c42c08041820000676000080a402618068c1488b01083940008160b0200004221c9874aa800054440a08a677830274010580282804c0802201620ce34a009203140400990218454e88402305800082098020416004a93e0193800645002c4384c414b4c060a608480e9412e80a1010040260c01862ac0a4a88e0782099200978ce1208209ac49072900000000000000),
      (53,21,8,3,0x12dd703303aed3,0xa049ec7000da00004580100016840016120000a5972caa8288400000840c04012969be0343010482806289e2c0ca08000908a022024622b004a64f03d2258c2518084081220e8358f10010480a8200289061c91d10a20010500142880c75808133111510cc20d0d4c09450063fa0c380221001a4420000800a0011a10015800028030200a0000804a410250100300242012b00022020004a68c41520468c4d00e42482b454c0104062000890848800230104059516a09213805918b10254118a2900020220006a402120060040520412900800028020600a0000d40042c400280080002112c0042600e182fe3005148195858219845444664080d71008a14005040062845c49c304880020a8090400578d60b8224081080c5218d225e079329006a231002202884800092981a3c8a300a0904061603ecb0a4010181080020108a0aa9a74c2800024340010b4000400d100042d80071bc90292dd703303aed2),
      (59,16,8,3,0x22b62183e7b92bb,0x2c505800160e302218448144c046429082d2043400860223819e24501002a00a618600854b8108011a3207010021611cac6840058421842a55200138a050002a001e8e0012e2403410c0084042d1211316010d0892c40d220c8a1a20420d401009871002b2c820402c28891043428cc800412489048d418e20260461008b200813d04204c0d914010c00c8b042090d61a8200281288093810516803250082c402b3043820408024166ad5162204410c020c000605e07001b0228d300033a11038092002084961c80c860448104c8c48c066816402030677c0044200910000901d28d2c88085251c80414840420404722c40c1600536110870224110c0c2394030288100191c06363021e603820300c202142218586c8404042d4610228005600059128088a640c8aa110004c8d410289028120614d8010050862320d98042006a140283e950102518a4288800e80968514058021002a0409280de2e0640a140a019182724480004e409081842ca09d00450520056242480a25b809400901640a41944006290641020b80c9308902020e1210078242608ac041c6114044002d1a811a34400810104aa8ac29022b62183e7b92ba),
      (61,14,8,3,0x1713e6940a59f23b,0x2821450008200010401189590b000000aa200008001444080c04180804102440022089000083c2444208240300108400480841818d091009c0009019080000020c3085081200064150e3000400090194c012421000803024042404248012400880024104008600001c0308050040400c0202d82000043800000f0a5800a8000244225002c4400500c4002120000014948400508142800002a84e00044c009840814050200020180e0866008048980006681005804000e0800400a04402025404193880088402081010448081200410042b00c221300020410e892290000ac0020820005d80dd0002082001a80004a248b8410200064221806a10040002408091040408a01088008e4c101120201102801000a3800100d0040b30000c8900803308300c020002050140c10c801910003908a00000a140850010949400000242009180500111a005221120000a800d285800000e1000020da020180101005008601c00003080104120008801240092101210120600801421240194c04800100063854130002008508618200000284c048001c8044858c0c1080900108400601208211121a0800048822001120410080c1018081114000800022a808000684d48c401000002080051420a3713e6940a59f23a)]
    apply grid_sieve (-39) 80 11262 270288 256 classes gates (by decide)
    · simp only [gates,List.all_cons,List.all_nil,Bool.and_eq_true]
      repeat' apply And.intro
      all_goals decide +kernel
    · intro c hc
      simp only [classes,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 16000 in
/-- Exclude the full cofactor-97 range using W=9+4i. -/
theorem no_cofactor_97 {b x y : ℕ} (bound : b≤68980024602) (cop : x.Coprime y)
    (he : x^4+y^4=b^3*97^2) : False := by
  let classes : List (ℤ × ℤ) := [(8,7),(8,15),(8,31),(8,39),(9,4),(9,40),(12,7),(12,31),(17,4),(17,24),(17,36),(17,40),(24,7),(24,31),(33,4),(33,40),(41,4),(41,24),(41,36),(41,40),(44,7),(44,15),(44,31),(44,39)]
  refine exclude_fixed_cofactor 97 68980024602 10 10944 262656 (-65) 72 classes
    (by decide +kernel) (by decide +kernel) ?_ ?_ bound cop he
  · apply cubic_classes (-65) 72 [(1,4),(1,8),(8,7),(8,15),(9,4),(9,8),(12,7),(12,15)] [(0,1),(2,0),(2,1)] classes <;> decide +kernel
  · let gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
      (5,2,12,6,0x13,0xc08592),
      (7,6,11,6,0x17,0x16b3017804080),
      (11,3,10,5,0x23b,0xa4c2042b0f289c40400008c6480000),
      (13,3,10,5,0x161b,0x16da204dcebc3d0031088846007e1eb9d1026db49e4),
      (17,11,10,5,0x1a317,0x25aca32c150013294180804440700261c89c3200701110080c14a6400541a629ad200000),
      (19,2,10,4,0x30af3,0x4c449474681a240060011c0610d020142e30a0206c25421041ba0a0cf01026e22e122081220282611b200000),
      (23,12,9,4,0x5335f,0xe01888f420202c898255120802a02024f0180900849311a058826200010c040c2a8406a82121c000220410c290c0201221e42015000244140400130081085005335e),
      (29,26,9,4,0x13d122f3,0x12365140306010262011021e90c8109043a0e25462583500b03800cc300272c540000a3842000632144030410171944001229144a2400114c74041060114263000210e28000151a7200619800e0680560d23152382e104840984bc20440232040306014536240000000),
      (31,11,9,4,0x121d47b7,0x4058410a0180091c88601c0440021c20101c20b5040e822086020001210a90450101004a80301a941c408453b201043a9a00e04024000518d4c00802324a909821900901185244008000012c44e08119a01ec491000a20d3ae29211044023280320b20540d270034056081009410cc1a02899296de2b848),
      (37,27,9,3,0x165e211e9b,0x14343c10d00256b80425052d8d0414a60218cd0010431ae09051a46151c11670819380886815548254141c550415520b680ca615840b18943481c26400150078a970048a093005ae0073422642823418232341414162620c1620a1322167003ad006482890074a8f0054001321c096148c6810d432980b68255410551c14152095540b0880e4c0873441c54312c50483ac610400598c2032941058da5052100eb52005841e1614000000000),
      (41,6,9,3,0x1b382b50737,0x100d0c32280428216601400896700148e0b10018849b19020018a801010cd2448020f81081500b160490f4160004412514050e0302290601891902828c2021c456401042eb0008121090150868a80ce4008304600b07210401544084d306c0402940049846a440112b10c90014a0101b06590811540104270680310608013980a8b085404842408006ba104013511c20218a0a04c48c0304a2060385014524110003417849034680540840f820091259840400a8c00204c6c908c0046838940073488014033420a100a261858040000000000),
      (43,26,8,3,0x35883a3ee53,0x24c040b014780412196023420313801880016074812d0008a1e18108028cc00985c018628823910440860c6410600230d8011158404c10028883430510546a8111308200390524e0c210009400543049130004c4ac024024a941014024392d20813001899a024150320c444c42280180948484b1620803010200a73054004f0822d0290810504882a81a0292900b01854200065011da4d00809d1a018c7950100024c000068394a31100d22004a00aa11c9266200652007100822a05009320108a61e00040b9600400489d41c9001a20a544158440a00612201438c06248060d12100000000000),
      (47,1,8,3,0x4351b2753df,0x40280600630210000e42801005202640820e0902200000c2242892960a4a08112402040c204c10040454004100042c00084067028086249a04624a98010931d1124c004201091a540a03488240d004081058451a1088c6119110000812296006080604000a0a804230050080f8821272401c0e124962037000881024c3c0a881808444eca0290906105080209004509030280146993020460a4200020a422020518008b01a024804115d7031294e0180830a90b440a541210182022008e91700c04d140a001c00400ec622aa0110084602c44011013148000831200240825f938c0c1046832e108209708a395f002a0014042025158001a20195224a16307005f0006d085310170862101230d470800000000000),
      (53,21,8,3,0x12dd703303aed3,0x62c89803809481115214280ca40088a0be004089223908800804a500311281d082408410a2852a0011202010b850a524805090a100019128d42081114440309101388640600440272140480509129004f000a08308ec0021059404c00c30b851000180180049006984c00ac050242094850d1055000da1080831a12061b0801402724307840830928050128ca8000369881ea0c0221a048020700803438a2282418121004028908900179cf40048848a01404240c120a228e16008070200802c220182bc08cb60000a98a40500a4860810f0612720140086c30242c6080842d8005504585094c2120501a80190cb0049000c00c000450e8618011014d042001b8c6082800790048448500901427301100301308e4044860111444082158a44c000408485009252851e84020244002a50a28410812081c0a4460052902800884e224880003e82888012980a1425444094c0e00c89a300012dd703303aed2),
      (59,16,8,3,0x22b62183e7b92bb,0x124409600280404e6080230520207c182c05004001439102900d0c830022d010200444080ecc04e800232c9400180a00f20106813041508622ba00021a0041826248042c40462109544820240271144060e003520808323102408420c5a0e242129034c6890080242410800210b20b0805400400b81c741c1080210808a422d008045424ca0083508090b500107101c0006221220040133688420841100123961020488868209166242088b58206400504408848100952019424180103016188a02a011b88004034c08621300000ca8800c2980304816043c6540508801581411c00124c186c390c0005840441c02481a8408b208766012208090300420691968008140210240954100ebd04a0012422061c003982441601440d212223094600020258130ca140d001082084f0840e11282a510010b80040119a898094a0500260c018eb214008a442005082d48201081311048800224d698281c00826800204d10528a8040810203167480106828e806011c00012c40838184164860010ac440a9122014400705010a0182f10a2803ea4008040872405a81c10c900288825106001098415888284ae019002000000000000000),
      (97,95,7,2,0x1eb628b476067981b8b451b5f,0x1037168a36bdeb628b4760679628b476067981b8b451b5ef5b8b451b5ef5b145a3b033cc0c5a3b033cc0dc5a28daf7ad8ba28daf7ad8a2d1d819e606e21d819e606e2d146d7bd6c516c6d7bd6c5168ec0cf303716880cf3037168a36bdeb628b476bdeb628b476067981b8b451b7981b8b451b5ef5b145a3b0375b145a3b033cc0dc5a28daf40dc5a28daf7ad8a2d1d819e78a2d1d819e606e2d146d7bd6e2d146d7bd6c5168ec0cf303168ec0cf3037168a36bdeb62a8a36bdeb628b476067981b8a76067981b8b451b5ef5b145a1b5ef5b145a3b033cc0dc5a2833cc0dc5a28daf7ad8a2d1daf7ad8a2d1d819e606e2d146de606e2d146d7bd6c5168ec0cd6c5168ec0cf3037168a36bd837168a36bdeb628b4760679a28b476067981b8b451b5ef5b8b451b5ef5b145a3b033cc0d5a3b033cc0dc5a28daf7ad8a228daf7ad8a2d1d819e606e2dd819e606e2d146d7bd6c51686d7bd6c5168ec0cf3037168a0cf3037168a36bdeb628b4763deb628b476067981b8b451b7981b8b451b5ef5b145a3b0335b145a3b033cc0dc5a28daf70dc5a28daf7ad8a2d1d819e60a2d1d819e606e2d146d7bd6e2d146d7bd6c5168ec0cf303768ec0cf3037168a36bdeb6288a36bdeb628b476067981b8b76067981b8b451b5ef5b145a1b5ef5b145a3b033cc0dc5a2833cc0dc5a28daf7ad8a2d1d8f7ad8a2d1d819e606e2d146d6606e2d146d7bd6c5168ec0cd6c5168ec0cf3037168a36bde37168a36bdeb628b4760679828b476067981b8b451b5ef5b0b451b5ef5b145a3b033cc0dda3b033cc0dc5a28daf7ad8a228daf7ad8a2d1d819e606e2dd819e606e2d146d7bd6c5168ed7bd6c5168ec0cf3037168a0cf3037168a36bdeb628b4761deb628b476067981b8b451b5981b8b451b5ef5b145a3b033db145a3b033cc0dc5a28daf78dc5a28daf7ad8a2d1d819e60a2d1d819e606e2d146d7bd6c2d146d7bd6c5168ec0cf303768ec0cf3037168a36bdeb6288a36bdeb628b476067981b8b56067981b8b451b5ef5b145a3b5ef5b145a3b033cc0dc5a28b3cc0dc5a28daf7ad8a2d1d837ad8a2d1d819e606e2d146d6606e2d146d7bd6c5168ec0cf6c5168ec0cf3037168a36bdeb7168a36bdeb628b4760679828b476067981b8b451b5ef5b0b451b5ef5b145a3b033cc0dca3b033cc0dc5a28daf7ad8a2a8daf7ad8a2d1d819e606e2d1819e606e2d146d7bd6c5168ed7bd6c5168ec0cf3037168a3cf3037168a36bdeb628b47605eb628b476067981b8b451b5d81b8b451b5ef5b145a3b033db145a3b033cc0dc5a28daf7adc5a28daf7ad8a2d1d819e6022d1d819e606e2d146d7bd6c6d146d7bd6c5168ec0cf303708ec0cf3037168a36bdeb628ba36bdeb628b476067981b8b46067981b8b451b5ef5b145a3b5ef5b145a3b033cc0dc5a28d3cc0dc5a28daf7ad8a2d1d817ad8a2d1d819e606e2d146d7e06e2d146d7bd6c5168ec0cf2c5168ec0cf3037168a36bdeb7168a36bdeb628b4760679818b476067981b8b451b5ef5b13451b5ef5b145a3b033cc0dc63b033cc0dc5a28daf7ad8a2c8daf7ad8a2d1d819e606e2d1819e606e2d146d7bd6c5168ed7bd6c5168ec0cf3037168a34f3037168a36bdeb628b47607eb628b476067981b8b451b5e),
      (101,40,7,2,0x1391b7f0d30552a832c3fb6273,0x187098804000189a01a24108000830876d840c0150870081a2209006001490580e015081f3a2a44300954700006004510140881180100042de0900281052a088e510812224914800400181044ed0000380383018680c8853408808f0981046a120403994640a305830050882094021980010808426985092b2b1020409a040da0881314321000a81aa02ca20004197a22a00a2347090a821401340c680240040010521462182400951001c48002030027600108d21d2221a80a00716a280c2849184028ac40010201070041a5890ce08020280416040008a648501a2ca102010012c06b0002da06834011008240090a18201041206c0202829818ca8000800540042da0a8062410a2082a000c80005019091a39004884620950309822008108010811850904d422c04080680184280022501521381c82002080c800480942aa0a867020081e11248860915c084a80c825102e00092b6006cc87504021309aa020008321a0a258818013a4b812005019010a84260245501041240400861224350226c23000c4000012b608a700302804230c644881001040118100169d8008a30605850000107200341222a4f8330484aa5204c4d71021046004603604221449090040c400b00440818052a380001210084110ec43169b4890061702c0200152025223c40a00108138481a4d10952890101f082342800c10e4840101b0209424a12a0a8c0626c3400010c108175e4c01a0a285000018948e500100b2004b005b0a06ca440c081216b806820118aa062200210018000c1b6800900689a8010b320960d0910a0001410b006111ca00044404e08c0a98b080128213c1808355002048238112030000e08a030982884c90092b838400c82260a4128322098010e0ea48049908a0c86028838000602440e2090200556080c1e420a400868ca818839011100029c443006841400028448583482668400ac8b004800b6c18000c00420022302a8c4020b00eb42408181129b0286d0069002680400538948c000050a282c0193d74084184000161b23018a82a4292148206c0401093841800a162087c04048a5484592c090e4084002811e2252025400201a0743004896cb4611b84410804240000e2a500c081100680118100484914221036031003104204759190252a9090660f92a22416002704000050d030628800dcb40040c40104004089131862100a0600728836a4000011800621b2205612243080101241040551203210a8404c0500240e92e400c08d2282c260800202ac864201057099b0036a48003a04520980a9081d44830892443c08020730a82aa148090009808200209c0e42540522000a10c00b008101a215904850c40840084080220c860548231089004e2c484c05000098002a08228412300a82da100150008000a98c0ca0a0201b024104020c2848012080440160b02da0006b01a4004020429a2c05093288001034100a0200839848d2c10070402040011a8a010c490a180a2b4700280ac2225c25884003720060200091c0045480120c23142504001001200b1816401420a84871622802a22f4c1000229a02ac0a80042614640882d8102c8102046a6a4850cb2108084000cc20148208850060d06281314ce010242b1040c878808816508980b0c060e00e00005b91040c00100094492224084538882a5040a00483da1000400c408814045100300007154806112a2e7c08540380d04940030048222c0807085401810db70860800084122c02c8c0001008c870c0000000000000000000000000)]
    apply grid_sieve (-65) 72 10944 262656 256 classes gates (by decide)
    · simp only [gates,List.all_cons,List.all_nil,Bool.and_eq_true]
      repeat' apply And.intro
      all_goals decide +kernel
    · intro c hc
      simp only [classes,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 16000 in
/-- Exclude the full cofactor-113 range using W=8+7i. -/
theorem no_cofactor_113 {b x y : ℕ} (bound : b≤62304422101) (cop : x.Coprime y)
    (he : x^4+y^4=b^3*113^2) : False := by
  let classes : List (ℤ × ℤ) := [(7,4),(7,16),(16,1),(16,25),(28,1),(28,25),(31,4),(31,16)]
  refine exclude_fixed_cofactor 113 62304422101 11 10402 249648 (-15) 112 classes
    (by decide +kernel) (by decide +kernel) ?_ ?_ bound cop he
  · apply cubic_classes (-15) 112 [(0,1),(0,9),(7,0),(7,4),(12,1),(12,9),(15,0),(15,4)] [(1,1)] classes <;> decide +kernel
  · let gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
      (5,2,12,6,0x13,0xc08592),
      (7,6,11,6,0x17,0x1118211504496),
      (11,3,10,5,0x23b,0x1224228000c442a0184381082225c4),
      (13,3,10,5,0x161b,0x1212000d028c300010008004002618a0500064249e4),
      (17,11,10,5,0x1a317,0xd69034c5002a294c84060222000381386530e40e00022203010994a2a00519604b580000),
      (19,2,10,4,0x30af3,0x81a409032206286140844a08805c02a60083449018806a8180524300d08849e008092c041381020ca84444f50c),
      (23,12,9,4,0x5335f,0x8420402401a0202180004a7a110840204e164604008220e000495c42691430210083110005c0b144449a83002038125900054082ea908491347e0211c4381000000),
      (29,26,9,4,0x13d122f3,0x1600880898e11486a0183884056008502c200042049401b0040a58ac500858100408891ec47044b23760406082904408e902194c204b881104a08301037626910711bc488810040d08051a8d281006c014902100021a05080350108e0c02b094438c880880340000000),
      (31,11,9,4,0x121d47b7,0x4058410a0180091c88601c0440021c20101c20b5040e822086020001210a90450101004a80301a941c408453b201043a9a00e04024000518d4c00802324a909821900901185244008000012c44e08119a01ec491000a20d3ae29211044023280320b20540d270034056081009410cc1a02899296de2b848),
      (37,27,9,3,0x165e211e9b,0x1004000060290429020100012004048220000000002c94c08823140231000000810160d004001002110000440100100b0100001005020001060d0004400003d0130804110d80000c0048006204606011021222222224204403031023000900180000d84410086405e0000110005830400020500400004068040040110000442004001005834040800000462014620881949a000000000220901002400040204a104a0300001004000000000),
      (41,6,8,3,0x1b382b50737,0x7210e29a802a0761a2000880b3005a8a01b30200c2956803402282901008a21020c004f39291020118095192488a340112cc1a0060180060810190013044109004121129004008108101083495c1524110081000482dc0f08218640500002c505091836c2800a1b60c484051a000050930c2087819a0900040824412541d486084040840801004a442410048411064004c04083000c03002c99a44016288924c5480c402044a4e78001820422880404a0a205600b54a1802066c028ac0066808800a2c3702a00aca38427001b382b50736),
      (43,26,8,3,0x35883a3ee53,0x1000e40820a52a005ce20064011483b604021008ca148d58a60102060010512044aa46e2004b0c1654014482200401c080c0d0042010448002486006261360b20c000480a090040030aa20400808988022200a1240803080088014a02a0a05c7810878c05a28d0d0a5c801000a049218021cb0c8408c21140816000520020415008002e0400600eb44028a525320140366584c5081619210444c1a98d80f1802c80008207200650534a089300531140e19990ce26e000108c28090002f200001020b28a810d220201110218800084ec3b2420008859020d4080081020b40e20b80635883a3ee52),
      (47,1,8,3,0x4351b2753df,0x231d026000020e050151000080800d02524488d480110002dc6084100a28c00248820848d0805800081040c0d1104002210522a1000c51d01422453000201dd10c60700200241204821909c818e05100402044083412e2042980908058004c2030032080820626018010a2023082a26000d81303591402002619801105a8a880842c4402a08d025214001708008821100030c9a48030e82402882028c0c001405c00130104042834007d10922a4205180241d0a06482244148a04100d149d400400810528600250601ca12a0030a4004a014049a468800008800640622060f108c4909c0a0828002d9e0810b1c121840131a00a4a00000a228c429180321201164484d6862000a1426503038800604351b2753de),
      (53,21,8,3,0x12dd703303aed3,0x141100190c8018483013584207084203c80aa4e0031841400011644454a700383000030c8403408c084100412085558b0150042b2014c002030015100b0a1802000ce408008806050692042002fa98019a340080800186d020051a4432010222008910c980002804602a01920347000019881035b251004a30ea002912133b480842a0c01818681321212804389003406e9081590d2128c220a900008a00930602500820411082ca0a8910e80b8448a829a08041020805203064802880004a83218a42584d4084bb0160048e100a4242640b0c0c0182a108096e64244a002b8629004526d60408c80000716024c02a03100a0000c98448802220402e112c500205b080008080162cc20cafa0021024a05030088008139800200c286804540060200194226a10054068d450824100410818816010986000460e0072951111440001410c601392a809e0210870210d6406090800984c0044142d228fccfc512c),
      (59,16,8,3,0x22b62183e7b92bb,0x2d6018409004103b88240a80882a38908271048500800021419c301180102012018401864a928930638200a5a808614c2820400159039302410a6a34e018002a01080230b83b0b20218ccd901a35002905000d00da8005840443a2c20258d18698533100a52640d00048891203108480a2440089008d41822042444c000ea0102c286b1148c814000804417872800c2300200280aa20130204148050502068442a00166021288a44dc1901c45a830160aa100042c20702190200b2000132123290904064808410018960408081488484243800082130200c90f80078da81034b49320d8450001ada15a21a8640b462c5e21810609162b0103b0a8d1600a314000088000130d8435100024520890514363c4008e34656110bc5e00d440968c03c088b40453ac80a008520005c99401ce03a1205110d09cb0dc021071901d6071421981920341102500c008c428a00b0911401007209c1040c41ac50e0620000288199820a41a000420180e6603cd482102d0500b1204028020a302858a605592101d0402601860122ce7284045110ec089840848545d309a259e0049412102502005134c02e51c25f0000205800000000000000),
      (71,37,8,3,0x1164729716b1d977f,0xa81b50012c081020026c402145910200010020860080732904110494d01200040110914018b26088802300108a868260940800c08003841004849a3a600410491051808124808880508010224c4cc04020014247841400c06253000930290e814028446014402c1420411011cc11600340f0200825e212a30a00104860025013003094080c012010c30920112160410320507218823c02420839086828010800e0c0a01231c04100000c008801102c101f4024ab3120601019140631852a2000c905022ea001c2e1802081024238109c0201181080030800700137a00089000389507a810314002108900d5004230122c026115404810c64000000802b918ca80c1402802499002105281450e95180004a4108208304008182508f019a8c580941410080229201a0250602b90017300608214b1006440e3006204005c1204004908560000200d12502d4a850084480010418008b7401242244828080522800c040aa89102463804d014121800a0410c445a5818c041010482280c504602014052960910cc4060c8c1480008804589004f4440200215084567c09c8481201890010120405c0a100c170004282005041043c211000878ae200001520200e0803026c9d00890ba220008542c1990014124301034201942a0884010842438000d320b404509401e120a00458200494290b191000258804644800b282a080a0282260002c462a210a00e18841104190000640800c9261432116a0a02010a7010110110876491181604c0080c4c062c6190004a0420d80302a80417430ca00201009094941cc40d0116000431208885920a00a88a5044b040223e480041192a24c3ac000d000031d278080140a480c017ee9b8d68e94e26880)]
    apply grid_sieve (-15) 112 10402 249648 256 classes gates (by decide)
    · simp only [gates,List.all_cons,List.all_nil,Bool.and_eq_true]
      repeat' apply And.intro
      all_goals decide +kernel
    · intro c hc
      simp only [classes,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 16000 in
/-- Exclude the full cofactor-137 range using W=11+4i. -/
theorem no_cofactor_137 {b x y : ℕ} (bound : b≤54797085010) (cop : x.Coprime y)
    (he : x^4+y^4=b^3*137^2) : False := by
  let classes : List (ℤ × ℤ) := [(1,4),(1,40),(25,4),(25,40),(28,7),(28,31),(40,7),(40,31)]
  refine exclude_fixed_cofactor 137 54797085010 12 9754 234096 (-105) 88 classes
    (by decide +kernel) (by decide +kernel) ?_ ?_ bound cop he
  · apply cubic_classes (-105) 88 [(1,4),(1,8),(8,7),(8,15),(9,4),(9,8),(12,7),(12,15)] [(1,1)] classes <;> decide +kernel
  · let gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
      (5,2,11,6,0x13,0xc08592),
      (7,6,11,6,0x17,0x88605a00c8e8),
      (11,3,10,5,0x23b,0x2e4436134c6876243802a04ae1223a),
      (13,3,10,5,0x161b,0x149200040021e046223103c0001000a49000361a),
      (17,11,10,5,0x1a317,0x480200460c1c1080a315d00bc8c4c204010209189e805d462a0840c183900200901a316),
      (19,2,10,4,0x30af3,0x8e46c1400004802f8a2a0cbe4372c83a708080a8c6d008055cc10040900080400111000a89cade064000c00000),
      (23,12,9,4,0x5335f,0x142102019000405044800150084f089008061286104088000709082ac042a860406100008c82340b1192420120301e48080a8020915483226808085e22300e7acca0),
      (29,26,9,4,0x13d122f3,0x1600880898e11486a0183884056008502c200042049401b0040a58ac500858100408891ec47044b23760406082904408e902194c204b881104a08301037626910711bc488810040d08051a8d281006c014902100021a05080350108e0c02b094438c880880340000000),
      (31,11,9,4,0x121d47b7,0x10ea990e21a0d469208102042c894e30221c3b418402402c811b83308c7a42ce2c2825a806a688014230000348100009010884f2e003a20100060fa24852481101005274065e8392151b664a20201401840202811050010102200085119902147400806120001c110a105506e02000650404000b00000000),
      (37,27,9,3,0x165e211e9b,0x948408704c42804c9583a5040702a410486101d4f90201f4084418c8a1a2101506c1a071228212d288040289842a50096b0008a3280c44080321d1336e05c024484b36430467041c204189998048364d8c098080c818d9360900ccc8e1021c107210613669091201d03b6645c2600a11180a6288006b48052a10c8a01008a5a420824702c1b1540422c2818c110817c0204f95c243090412a0701052e0549900a11d0708109489a1dee164),
      (41,6,8,3,0x1b382b50737,0x100d0c32280428216601400896700148e0b10018849b19020018a801010cd2448020f81081500b160490f4160004412514050e0302290601891902828c2021c456401042eb0008121090150868a80ce4008304600b07210401544084d306c0402940049846a440112b10c90014a0101b06590811540104270680310608013980a8b085404842408006ba104013511c20218a0a04c48c0304a2060385014524110003417849034680540840f820091259840400a8c00204c6c908c0046838940073488014033420a100a261858040000000000),
      (43,26,8,3,0x35883a3ee53,0x2e1600280de408014a110028213004a000818b716224ba1020000865208408e988024042644d24106040000c642114b168002388a65e9020505a83640a03018005101b408e24236c0132128834596860106604ce010f4d0a8181126a22001404200044a0107808500181131800c8a304761081009888624a088084f00e330218726038d2342040af02042000010012411e220d20806002124a080600208f002060248ac1905215501081041081004544182000ae2300040d0a242a298a06a1142c2108c2044028b5a07a0400802024089267412248206aa2d100dc4040c04250c0200000000000),
      (47,1,8,3,0x4351b2753df,0x500102892306312082038008c430065001160503a4004027c5298218300a58900500808400465010551c001108054600240064429c1750b106c142351a080975004c9140610032495293238008900080189cc5c9b424450081700008890b240048020e240a080c1220ab91a130028b20811f3900cd020464030c106405318bcc800a6cc1200d70001a50c10112841000a42c15869243b104400100020ac4f04041a020a874322407401f12195849c5100ac400b962b04021352080238c41b55140110412002a124b684240a903c800c6024022600138c1000ac54103642387380e5c0a0584a0c001297d85610e1988811806803814900e3230842e032432a839250155487164422102441478da81000000000000),
      (53,21,8,3,0x12dd703303aed3,0x85408920001108bc90898a42300c1951a826aa001400a040e04804a0921b02ea90c898004800500002288c00400e051a0416f441844091802086080110a98400c000006122820112021a0e4a1009d498440188018080a661e000bc9080e08000601024810020c2d11001401004208904201e921150d08d421207008cfa4a934a068430199a11406f450442d064a100292ea5c4442c1172840470240004004c08f22080008080f78811a0484a290902c408f7808080008227881900100012071010a7441a1111d2ba4a00429305a110517b01442ccc0610b02964a92f98807024215885854424bc02104882100401400445a182004092040300008380849e8003c3328080c008c0110c95c80429382c20244020a2430000018010ca844008308200c48110c117b4102c50380100188a2000050009000c8984aba06c248290090381028014002ab20ac54c18062128c8849e8844000248815080000000000000),
      (59,16,8,3,0x22b62183e7b92bb,0x8089800a08022618c40218083551282000023062133041ca0002412201020d0028604a08007610f504405020c0b20003434100003120691020de060200c406c024242415a0043849222e3505058010e82144200324422840120135028100be24227026a002228d808e1002e500002852040011142140825000008801b2a4879c480230202a006201a0329000044102000d185045000060d828004801a0481001c0680c101d05780c105024199c938080168828a00110c084013300420044058002201802613024542400014514010800010054260a8980c0423047b0a0e6d0c8095840401a242223984810a2480bb9c1002041eb00906a30416808414200884812120468c4038020004518019a81314054114c3889122482980808659300b859285640021412d20218160800428a0602e10e0c90904b045aa2c10940213382811016908860000020436c023900080a06280854011954230053521610043008c108400440800996004a222845920100b6282000084c3502185a83a2a600021820682820080a402aa46030204920728d2062223814851200030a018a793a0a080d0404800ca02448145f01029800000000000000),
      (61,14,8,3,0x1713e6940a59f23b,0x41c90200044a02490225002406400210015082124022020820a400001c64290a801240202200c23211000180880118830909008402240b40948000004aa101400030023006440080410298200740021008c08280418084b001281110a00018020640601080068080348900282030302a8200080262080a60820652195002000004006a4200880980810180280556800009085060042001c012001c03300602064000087224400406600b3180400000800844208060914010264183810100b610005001608006288208021024011820010e90044801a008001001c08d00004688448c00222200189108b100005881c004000802c0091004b840020c4012042008208a3000834005000436804040e0c13204014483008211080080000100c66803301001122708000130203006601c002401c00210030508480000b5500a00c04080c80880212b0010000020054c2530208328082320080020aa0606020a0048960080b00084030130200c000284440a40069080c100a0818804200170020ca0410080113006200600014042a9000000948168122010804848608c400880c000442621802202012400a84a131c000012820820220124208540042001301200522049202910002049c100000000000000000)]
    apply grid_sieve (-105) 88 9754 234096 256 classes gates (by decide)
    · simp only [gates,List.all_cons,List.all_nil,Bool.and_eq_true]
      repeat' apply And.intro
      all_goals decide +kernel
    · intro c hc
      simp only [classes,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 16000 in
/-- Exclude the full cofactor-193 range using W=12+7i. -/
theorem no_cofactor_193 {b x y : ℕ} (bound : b≤43604665749) (cop : x.Coprime y)
    (he : x^4+y^4=b^3*193^2) : False := by
  let classes : List (ℤ × ℤ) := [(8,1),(8,25),(20,1),(20,25),(23,28),(23,40),(47,28),(47,40)]
  refine exclude_fixed_cofactor 193 43604665749 14 8702 208848 (-95) 168 classes
    (by decide +kernel) (by decide +kernel) ?_ ?_ bound cop he
  · apply cubic_classes (-95) 168 [(4,1),(4,9),(7,8),(7,12),(8,1),(8,9),(15,8),(15,12)] [(2,1)] classes <;> decide +kernel
  · let gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
      (5,2,11,6,0x13,0xc08592),
      (7,6,11,6,0x17,0x1118211504496),
      (11,3,10,5,0x23b,0x48109014c00220152180701091123a),
      (13,3,10,5,0x161b,0x149200040021e046223103c0001000a49000361a),
      (17,11,10,5,0x1a317,0x25aca32c150013294180804440700261c89c3200701110080c14a6400541a629ad200000),
      (19,2,9,4,0x30af3,0x2a8214110b20114a091a0602a1020844641016004f20160864902910206144823080313838404c4080053cf50c),
      (23,12,9,4,0x5335f,0x710008150120849080019305340120c030219028a0828020380811059221700402d00888240403614861404620414401c2a4002240898009a190a8810e84017acca0),
      (29,26,9,4,0x13d122f3,0x1600880898e11486a0183884056008502c200042049401b0040a58ac500858100408891ec47044b23760406082904408e902194c204b881104a08301037626910711bc488810040d08051a8d281006c014902100021a05080350108e0c02b094438c880880340000000),
      (31,11,9,4,0x121d47b7,0x821a0202400601438061138e1000880438080405c082b404061044542120008080a208300548002382958013728840595c208090081c32b18a00931004018419095062024020100224a88d20000598810702248de05cb045008221251c014c4020a8134132c00e4b002041a81833082925264501121d47b6),
      (37,27,8,3,0x165e211e9b,0x2c20f0b0a4201d6a40082c6d282b318406529d6308200286258a0900439a20e28161101c98a0a904aaaaa820aa38194c05b412918d021a80990e04b0951e00a80324144803ace0075a00b10509910282c4c4180c1191a0a044c85046802d70039ae0091412600a803c548690384c80ac2058c4a416d0194c0e2a820aaaaa904a828c9c044340a3822ce1004828d230a00208635ca53010c66a0a5b1a08012b5c02128687821a0000000000),
      (41,6,8,3,0x1b382b50737,0xa011a8203031020042d1481280199a014842298084283b22000410a0e1b2028289b102220264b0042018028008f4860310015149c47083002e00e29300188248125c03908112125041ac82485380010d061005400a0d660050202b9815010b506110050089c0d81c880500443056840540cea02050033582801500430584000e509209ac10524244084e01d2409208c0064a3803a00608711c94540046030978800a00c0210069320222046c8a0a026c382841000226e0a1080ca2109402ccc00a40945a100204606020ac40280000000000),
      (43,26,8,3,0x35883a3ee53,0x1a50032c02a88820110c4004100060c14114346121a82070081014210e8068325540000a0a08409240100450303e420a91416442c25446748209a10a0045020204b554108c18200745069c41213f08a0064403a86925100b11391c400000e9980031018000844c881202400002419f0d018061000c30412325902990bac4a50202075c88148030200400603c21241042010125050020040800880199188008c2080220c7c018a4090082481200221502040815c0005200099e019210a16020ac9b8022003801a0026080e22b30002428424229870e42091c8880112cd0100942940035883a3ee52),
      (47,1,8,3,0x4351b2753df,0x8c741000738840501f92a120212e424c90cab082330083420060481001c20c2924d438263a408204acc6c50060068db40a84050b802400801400b85040024540120c28d806e11200024084506416054c322844080201004d5a14501b20290302a92d840945188066e0100210203602100498000062a2805818b29c021908980000804012005981a4005a2e40d0471288128a4904200808841d7090e248022c38039602310001000c80b850108040082c821002a0010b11e683101320104510040605822da00c4460010280840d111a1b2b4040848d217c488000028e010204901c030400110000104b4222018820100234a4628231e800210004612050a401410040640044010290c00018a0a104800000000000),
      (53,21,8,3,0x12dd703303aed3,0x248176c2800013648418092002425101118c0221000c18d80c80a4c848100b0320230411018448ca04c413a2040440044854014a9420a01c0c310614820c4120183298801488a0482d480116005b4000300a201c81630181b810074081100181070382f1cb1000088212105caa0054021b4680021b8000280882a022a8080842a45215080b4a0020a02842184801828a18140d0c0021012d0824031c422903900b04000c1650a4005a4061214243012d001281341800106804e04a211c6012095a4042001858140c28a0c0090c210a028200296808542512a108080aa202a0880a0000ec2000b1682015002a9d04242088000469c7a0e07040c004488170040ec0c023409c02280602016d003440094a09028894008ca60c02411820943046181c028234a94015091000101022e41190298910c04410624260680409099080980d8c1800522018c44045212002480c1093600000a1b740922d228fccfc512c),
      (59,16,8,3,0x22b62183e7b92bb,0xc7068001a0a3409880c8a048861161002c204b410940202891e60711012a1006186500542038131620042070021635388684000012a9508610869780054000a051c8c20b0091d2001c68c8848b4202100112c08d2442c200802b04204585130104d3500238640142c20891143402c482449208004cd008620640471828c81082f20401340d13003080289b050010561ac24108168a081c9011480335008d04029305668240102041c2100c2088111a2acd800e07a06000302217300032c51038692104004901cc4c820488184c04c040268166031202240108800fb9801134b14b8090008084a0804e2928468302344e2020420910384221b2801140c029c4303081031b180e260020404300c041c067808084d8686110a06a001440862b42c0994440522680082b1320008855106ca1812050245019b04c4610a00805f0500a1580108011142518a4080a80680a285a405c07b0149020540084260140a140981d102720001224e418802e414d08604250124246a004a0a09a02400a4076902609460022982510244324c07410264241e008487040880a218e080d440022c588158b4000250d45548202045d49de7c1846d44),
      (61,14,8,3,0x1713e6940a59f23b,0x1040028a10510000d09a918802008a0004000115404082010182030103040002441100089800c024104222432c606084048008410980900039008900428430c10000012000c70a82600042109200ca6024000202420240c010020900044009200490c0380000610020d0100c0080802807000001c2000041b0890000540069422300a00223400a404a4a0000012100540000142810a002086400c88001c840180400040a028180064480401984187000201a0081660901008814008005402110011c9820200120404882020440c844300d42008000251245c2081001ba0004104003500560010410002ec0040821d12452000080215806110980102020890102400a020c9c40044201100080140880404a3340802c0200070c10cc010091300040a0281000100c0509c000898013080002840a14000015004240000029290928016220028062214b001500004884c1000021c00000700a00808018040582004300000e01849002480110004820040181202120210012032980248421000320a8718002000000418610a10248804e000480c8410800901083031a61222104120180088800441120001060406020c040208101544000100028882008c4ac858000050428a001040003713e6940a59f23a)]
    apply grid_sieve (-95) 168 8702 208848 256 classes gates (by decide)
    · simp only [gates,List.all_cons,List.all_nil,Bool.and_eq_true]
      repeat' apply And.intro
      all_goals decide +kernel
    · intro c hc
      simp only [classes,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 16000 in
/-- Exclude the full cofactor-233 range using W=13+8i. -/
theorem no_cofactor_233 {b x y : ℕ} (bound : b≤38459227242) (cop : x.Coprime y)
    (he : x^4+y^4=b^3*233^2) : False := by
  let classes : List (ℤ × ℤ) := [(1,16),(1,28),(4,7),(4,31),(16,7),(16,31),(25,16),(25,28)]
  refine exclude_fixed_cofactor 233 38459227242 16 8172 196128 (-105) 208 classes
    (by decide +kernel) (by decide +kernel) ?_ ?_ bound cop he
  · apply cubic_classes (-105) 208 [(0,7),(0,15),(1,0),(1,12),(4,7),(4,15),(9,0),(9,12)] [(1,1)] classes <;> decide +kernel
  · let gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
      (5,2,11,6,0x13,0xc08592),
      (7,6,11,6,0x17,0x2608a42c2216),
      (11,3,10,5,0x23b,0x1254105433c39140800240063404000),
      (13,3,10,5,0x161b,0x121cf32014182bf46f637b17e80c1402e79824361a),
      (17,11,9,5,0x1a317,0xd69034c5002a294c84060222000381386530e40e00022203010994a2a00519604b580000),
      (19,2,9,4,0x30af3,0x320078a4858162800938800421808040b31d0804054a90d020851417480f311d90448741204241405362100000),
      (23,12,9,4,0x5335f,0xa0d0028c4044003280c40420b84501282504303480058424422a4084c4806332003001681138012811c911048a02168241806102816546418261006d01a42800000),
      (29,26,9,4,0x13d122f3,0x81a8d2484000e20840c8200e91a18e2a2d00405488f243b4122600025040d594888006210c0228401906101c26c088428b00000068a10881b21c04304c010a20184230008894d581052000322416e127889501005a2a38c2c4b80209810823800109258ac080000000),
      (31,11,9,4,0x121d47b7,0x70041484158820184042e460031140e0834290423a081a0a0805198088052a504910440260851d8c1401402405e613826041004c80e0d10844684008c26201c488a89180184b20200350200c94aa003261994050890206d0a808ae1a014411001f0548049118e02c00003a5062c6148219090a6000000000),
      (37,27,8,3,0x165e211e9b,0x8384084a4a93201423838082970086120825401027cae131822102faa0211614048e0583620452d210454219140240035a4028223014c51322e1300522403a07688309b34842043820e5048066647019031b26b26c604c071333009073820e10200966c8608b702e0122500643a266519406220a012d600120144c21510425a5100360d0389114344202a7a04220c643a9f20403520824308074a080e062140264ad290810e089a1dee164),
      (41,6,8,3,0x1b382b50737,0x30105620148b4200408c166600520490194421280001137050804d8705082110236450504200d26404bc400500608a8008c06100304388e4800c94700740e92049046a48488109c284904d6080860b08001d9ac1400a8019d4040a002182b4202a3039100a0088028044e062a0216a0c200281015cc00a80141acdc000868308083590490a1c84089092b1049024b8170071498009388e1060043018800a8830050011e9013258021050513620442085070d90085076440000a42114c0490250033341881002168940235040600000000000),
      (43,26,8,3,0x35883a3ee53,0x8229b10ba3031808002000141000c0202b0e008b68c080481808022444732d0620804400110a000110081012a38f1906004a4c861bb34e1d66600000008254100e8a5c2d008a90091d4e68018e0a8326e02bcb01526495904426dc140a0000009004200222080204c108001115005e1b4800408c00a03cb8e41a0085a0458072cc0f4064e12aa001010048112000800064012000a10090302004004040003084405a1032986863050000208004108004a01000c100003280de29c4c06c4418af41000900138003c94c15228804000d0140086a02a65aa16d0ce8c024020448000144a77c5c11ac),
      (47,1,8,3,0x4351b2753df,0x801c6002af044002237a940a2a60924012529aa2208c0420014000298b860c441482499c1240010b0f04616c440c0608108e0e0784000221b022a044200614a0209c20521830a02441403c4001508126902aa0804800834c08181429145b50482841c506006a010ae058161000a04c40a2800206260212c240109aca1098260002460112c040408241f006803374901008484c0006b81801121003364811320b3180422320410c4a026004006002986848209200801a026081c809b2100c206400a91900b848844901800a14888480223e4408b0152044168540231409280824908380400402440e420a000830a910060004018470a63c8980024108224e010041420a8102610090381408010904000000000000),
      (53,21,8,3,0x12dd703303aed3,0x248176c2800013648418092002425101118c0221000c18d80c80a4c848100b0320230411018448ca04c413a2040440044854014a9420a01c0c310614820c4120183298801488a0482d480116005b4000300a201c81630181b810074081100181070382f1cb1000088212105caa0054021b4680021b8000280882a022a8080842a45215080b4a0020a02842184801828a18140d0c0021012d0824031c422903900b04000c1650a4005a4061214243012d001281341800106804e04a211c6012095a4042001858140c28a0c0090c210a028200296808542512a108080aa202a0880a0000ec2000b1682015002a9d04242088000469c7a0e07040c004488170040ec0c023409c02280602016d003440094a09028894008ca60c02411820943046181c028234a94015091000101022e41190298910c04410624260680409099080980d8c1800522018c44045212002480c1093600000a1b740922d228fccfc512c),
      (59,16,8,3,0x22b62183e7b92bb,0x802320a048a66d210309000001431428211601a0b95009a20c22422968520b05a818541018880141000b4006546612c32044042120281082200130408ae680418d050708000314000b03000e0a8502000012228561e0a8014200125026400060080a04844b00401d1c1006099004ea40252a9341086038000153a31192a2610a00000013140e2877902281001005e0880d0d3605517004c85c003285084dd80a402220286401005040400180810040e6059920a020280de808a124af0014c5044e4190600238647410d0083984131a82010035a195080049004a82c200041200442886020808104120c220080b104100020a481000e404201c2002711004c8c04ba00a38ac00892c61044400540800234068808890040408402880000403702400151602210008265076c4a40210024203000302281429200440084900099c04000808480816410252501938100f2346b062400b0011022884040a0c54418081e860a44530036600e108000c2b50000482409e20c84d060800c10c4084a200007321a8c00ce010c008048403400620290621400100480c000520c04c00668a4b48c08204080004834c004445d49de7c1846d44),
      (61,14,8,3,0x1713e6940a59f23b,0x1d202084d8302024009c0000020110056410a8482428111c750408413082081095492122434100000042052400104001000000264008020002014004441514688c0405014210910000000800944009800006000025240c490e100284a01c038254d8010a2b40090a0c0b40050303430305505034448034451c2400004400001880181800100000860100000555a2a8108680b2870801c21c046012010000100080831a440001bc68100880000100482000101081021800160498302814181808042000400201115454810441c8222402000000010034000029002404200001800201001804100c00402000c000021012004a000016004000000020122209c11040951544402001000210080c0c140a060c9034000c204084040002090040000088040b1ec000112c608080040000402403101c21c00870a680b0840aa2d55000004030800004000c0c008c0000110000121c511600911605055060616060500168182848016a28400d9520e01c0290a00438491812520000300000c801148008000000448421405010188b1454111001402000200801320000004001040012502100000041612242495484082086410810571c440a12090a84135004402000001c801202060d9082025c000000000000000)]
    apply grid_sieve (-105) 208 8172 196128 256 classes gates (by decide)
    · simp only [gates,List.all_cons,List.all_nil,Bool.and_eq_true]
      repeat' apply And.intro
      all_goals decide +kernel
    · intro c hc
      simp only [classes,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 16000 in
/-- Exclude the full cofactor-241 range using W=15+4i. -/
theorem no_cofactor_241 {b x y : ℕ} (bound : b≤37603344435) (cop : x.Coprime y)
    (he : x^4+y^4=b^3*241^2) : False := by
  let classes : List (ℤ × ℤ) := [(8,7),(8,31),(17,4),(17,40),(41,4),(41,40),(44,7),(44,31)]
  refine exclude_fixed_cofactor 241 37603344435 16 8080 193920 (-209) 120 classes
    (by decide +kernel) (by decide +kernel) ?_ ?_ bound cop he
  · apply cubic_classes (-209) 120 [(1,4),(1,8),(8,7),(8,15),(9,4),(9,8),(12,7),(12,15)] [(2,1)] classes <;> decide +kernel
  · let gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
      (5,2,11,6,0x13,0x19482c),
      (7,6,11,6,0x17,0x18a122450368),
      (11,3,10,5,0x23b,0x747084878cae149101c151525215c4),
      (13,3,10,5,0x161b,0x149200040021e046223103c0001000a49000361a),
      (17,11,9,5,0x1a317,0xd69034c5002a294c84060222000381386530e40e00022203010994a2a00519604b580000),
      (19,2,9,4,0x30af3,0x2a8214110b20114a091a0602a1020844641016004f20160864902910206144823080313838404c4080053cf50c),
      (23,12,9,4,0x5335f,0x1118071010bc191340122a900540103c90100901823248411a0580011902030808550c841560000e10820440c250c4480420109e24000a080a0900c800284207acca0),
      (29,26,9,4,0x13d122f3,0x530b809010881205180020995240a406e09580a268c96b004548300280828b04712202020001a408000ac059681c0130020222202006001c0b4f01a8000812c000202022431068a0a0a0060851006b498b2280d483b01281254c92000c502408840080e8652c2edd0c),
      (31,11,9,4,0x121d47b7,0x885004244048130d01c8c820108290640820a0f1282152023300050221804a280096061022402c11740327018cc2028541170004050d950920b4a0040c220aa7188024ca000950005036090006204165e118010397024c71063d2803400005c0c404c09b912410ad20088038a40e5243031122c900000000),
      (37,27,8,3,0x165e211e9b,0x1004000060290429020100012004048220000000002c94c08823140231000000810160d004001002110000440100100b0100001005020001060d0004400003d0130804110d80000c0048006204606011021222222224204403031023000900180000d84410086405e0000110005830400020500400004068040040110000442004001005834040800000462014620881949a000000000220901002400040204a104a0300001004000000000),
      (41,6,8,3,0x1b382b50737,0xbd28210c200211d46904d40e006001a8880b20d4101c2b480a04144e0011498048049000739210384aaa0488c04622c8205424040024e9192a0400448030030528c86410582084a0221c800882008543f12084c410500c313139000823a08304240701099c01cc8407012106082e208004e464618050411908247e150802088009c220290820d0413098a506006009100102a4c4b92001012150209a2310188902aa90e0424e70004900900c9440039141028096a1c04158268088ac003003815904b15c4200218420a5e8000000000000),
      (43,26,8,3,0x35883a3ee53,0x280d020324501a61208071801c8c042c204b81a0006187851000b2400cc50042c11461803a0c18408822710c4006082648086a22006c2c1114008320558a8228009c00410c8c00210c1c928920c2a002900d48c8003280829524024412d270900405991800c8888c1302a0890180144234411a3484844e5004080c11043c800a820a0810940b6501605504442a180d009496e20298000058b90100b000202a78c61c160000325112c0223149388550052001298011992205441008e19442013240269d020007820ae4480080aa50458009280140886a0a031c2804486122c18049100000000000),
      (47,1,8,3,0x4351b2753df,0x11400213378020183928aa04024034174c2a0862023621d28464184000298008e98280490d0a0409c044602ca1604204524148b8151a4481014100149712402c02e61e002204903042842722210490071a81275028200942832109e000d0830a889046004883033a4120205c05930811181449810d3084038549000820910433d00022b0b00ae00045616015c0410488219ea6108070a920088c0a24c0864040b80b261002441819d20a1061511208c1419084f000624ea05040129108248038d41206085084e401730f00110200292e248058a8d224080a08408a4829170022301650b020921a140813814c00474c143a508c830800150431011b10080480682e980100c1c945500228004266f7bcae4d8ac20),
      (53,21,8,3,0x12dd703303aed3,0xd12080290448281261000454518928944a0010541470c30040071014822124084bc0b06c040206008a21c011c0212ca00029600522d00280630270004163804382042408022441364010b40848242c21064489806088b2024148400c1e440262602044080000c86320cc00000047a39460380390800f4084644159881004c30010a142c2208030164350152523000824432a2052a000b810c44108a28c0450025458a850008000bc20019a12a42cc0021e800480050a8d1520051018a2884110840e8002a5022a6112080062525405613406008221a142840061900408cd41131081780084e00e0714e2f10000001982630980000811020323201134180109412026c88300c89130401a1209081684113641122008121020e100e3410007206300a0058250034a00029b4201c401c228803020101b0681a908124220940670010061871405040029148a48c515100043240e09104a00824592dd703303aed2),
      (59,16,8,3,0x22b62183e7b92bb,0x10180c107904890c0544295809400010108812a4d00ad164cc2043180062160800143894b84451086194004012b91411000810b54c0000818509485914008051862b0600413006249104038001540a09030485048060256a429800c0001016e8020a0822224802500814588a268491408905508364112007706284484244006405190182061b0430000481a6b24201257620041a88a09e0108345052201b00235a8088b100810f00020a4403c041098003042580351d20200f1005350608000f93130030e2c009181a101138270a0242592118a0c0885c880400464015062480400c6084802146130060c0020008a9e200025040d01100a07400480020c9a2318041b1506120e70100471390020800dc0020320140b0820810201612092080a4124c028c0043040002c880a11a1275008c00420e01462048220802214b000200151c2a080c32980310185444701208038009d85a0500601011230a472830a0070140700a8822480f9026241008081158a000a401414b07903212a9326020000038884042382098c04a0802948852011044012319000a0004900420d2168812094820520ab4011180003070b8000000000000000)]
    apply grid_sieve (-209) 120 8080 193920 256 classes gates (by decide)
    · simp only [gates,List.all_cons,List.all_nil,Bool.and_eq_true]
      repeat' apply And.intro
      all_goals decide +kernel
    · intro c hc
      simp only [classes,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 16000 in
/-- Exclude the full cofactor-257 range using W=16+1i. -/
theorem no_cofactor_257 {b x y : ℕ} (bound : b≤36025975739) (cop : x.Coprime y)
    (he : x^4+y^4=b^3*257^2) : False := by
  let classes : List (ℤ × ℤ) := [(23,20),(23,32),(32,17),(32,41),(44,17),(44,41),(47,20),(47,32)]
  refine exclude_fixed_cofactor 257 36025975739 17 7910 189840 (-255) 32 classes
    (by decide +kernel) (by decide +kernel) ?_ ?_ bound cop he
  · apply cubic_classes (-255) 32 [(0,1),(0,9),(7,0),(7,4),(12,1),(12,9),(15,0),(15,4)] [(2,2)] classes <;> decide +kernel
  · let gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
      (5,2,11,6,0x13,0xc08592),
      (7,6,11,6,0x17,0x18a122450368),
      (11,3,10,5,0x23b,0xa4c2042b0f289c40400008c6480000),
      (13,3,10,5,0x161b,0x1212000d028c300010008004002618a0500064249e4),
      (17,11,9,5,0x1a317,0x10cc368168210059a20480081010020a652532920040408009002cd10420340b619865ce8),
      (19,2,9,4,0x30af3,0x16271400a001200147d3d30553b09e5c1304041631540402033ab408001000a0008000884e456607b4c00000000),
      (23,12,9,4,0x5335f,0xa0d0028c4044003280c40420b84501282504303480058424422a4084c4806332003001681138012811c911048a02168241806102816546418261006d01a42800000),
      (29,26,9,4,0x13d122f3,0x9082202c909c501d188290148052000901b0d090020020a02c2d7104804802a023a6006a441d8c0a124ce04140a00a36c402a2a011b6280281410399242818dc112b0032e202a0090090475a1a02820020048586c0480025009404a08c5c051c849a02208480000000),
      (31,11,9,4,0x121d47b7,0xc848530058c29040001d283231c058182a4024a882200384570d00040da150ca02844940064c3010064a56404006a48c00c24038911520046131a21088d002640706704c08201202f30b18280280130428ca092208c044029514100a3211d040d0106852080188a0708085c8c0ac4100ce00829080000000),
      (37,27,8,3,0x165e211e9b,0x14343c10d00256b80425052d8d0414a60218cd0010431ae09051a46151c11670819380886815548254141c550415520b680ca615840b18943481c26400150078a970048a093005ae0073422642823418232341414162620c1620a1322167003ad006482890074a8f0054001321c096148c6810d432980b68255410551c14152095540b0880e4c0873441c54312c50483ac610400598c2032941058da5052100eb52005841e1614000000000),
      (41,6,8,3,0x1b382b50737,0x1cdc00ece1007e3c7e009000120002280aaf550160d6b035ac1240000002401004080203988891119e6a314a3159029ce739408011002200010400020800018006000020400204000050028001d0d090b0ba0021021000271381c8e480101202000a83b0dc152541d86e0a900202404001389c0e47240042042000e86848585d000a00500001020010200003000c00008200010400022004400014e739ca04d4629462b3cc444888cf0200810040120000001201ad606b58340557aa80b2000240004003f1e3f00439b801d9c24c7d4af8c8),
      (43,26,8,3,0x35883a3ee53,0x4029a410882084158083a00062152e480e18028c080853002292c1022510250258008a542825c0022382c052000a41430048800554a14012063420268c240a40488a050410508004bc00296498000006a0c843114401320064060400e00730682240160cd04229c2027050004902281b00a080618915088626320004380080c304280220431892426a0c1020428800bd1852170c040a0c048802271a04e88120890910624801205213744800028961980c262830096080008502d488607014032000c25a882223001403e00819a8108400e820280616044584c020123910124072035883a3ee52),
      (47,1,8,3,0x4351b2753df,0x300a389027802580024ea54400f912580a020c3b6208880000810c408e1208a05563010e0d60081246060070256515c08008862698280800602b010282005088298c8a42c40080041004980c807400d31c0a00008801b222021c8a08958951405c201c11700a420a20e04062048404400e4002628002464a0103530108846024022499008012004368584044300e12320d4c000820b00128232421123804a88295b8002241900a5000c00000a282424200a0d5000140002421d8e064050800882229130110a811d4a08102500403152202443a144160d21442083008140c080c800000f018020a56300000c81002010c2004901698c682800c22000c4a0102484012182502002002a41041c3000004351b2753de),
      (53,21,8,3,0x12dd703303aed3,0x85408920001108bc90898a42300c1951a826aa001400a040e04804a0921b02ea90c898004800500002288c00400e051a0416f441844091802086080110a98400c000006122820112021a0e4a1009d498440188018080a661e000bc9080e08000601024810020c2d11001401004208904201e921150d08d421207008cfa4a934a068430199a11406f450442d064a100292ea5c4442c1172840470240004004c08f22080008080f78811a0484a290902c408f7808080008227881900100012071010a7441a1111d2ba4a00429305a110517b01442ccc0610b02964a92f98807024215885854424bc02104882100401400445a182004092040300008380849e8003c3328080c008c0110c95c80429382c20244020a2430000018010ca844008308200c48110c117b4102c50380100188a2000050009000c8984aba06c248290090381028014002ab20ac54c18062128c8849e8844000248815080000000000000),
      (59,16,8,3,0x22b62183e7b92bb,0x4000241a6002220cd14969181040840600029060260040520c4280020086004024201a00300e643518019c020060862042510004813c41909a0c104000615a8000241488a6006cc01c25062a20c040f430160022045108080080791a3583120102c8204a4a032704ce020004042408524008801092001210180018114084ca0ed894804202000a8b01108004805100000806e0434404448020204088800a81000468051c560044963084e22009918097408007202100e10001620820004149040408209061100408240088510c04000248025416100350402006b432a13a0868041cc209889c8320c00470c84509257800a628332414040501bd0000c040802073024050c80200a0809428426ec0520110aa2e00990b80060802f04406869b081c50ef20450201130850000000988700002a7462325520129549a084303a38200c132009c04050242258020040024a04c8000c091142b0f05400a6001c150a04000038400018a0005808115cd00831a0a090140841100098a8cc258640880844400a08005a00324160b5030a820304d106112114b42850422c034172a108184800000a18900464140914cda5d49de7c1846d44),
      (257,166,5,1,0x1a3579d9ee0a9a1fa6b052324e205bbe31f76811c931283597e16541de6e7ab17,0x1fffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffefffffffffffffffffffffbfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff7ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe)]
    apply grid_sieve (-255) 32 7910 189840 256 classes gates (by decide)
    · simp only [gates,List.all_cons,List.all_nil,Bool.and_eq_true]
      repeat' apply And.intro
      all_goals decide +kernel
    · intro c hc
      simp only [classes,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 16000 in
/-- Exclude the full cofactor-281 range using W=16+5i. -/
theorem no_cofactor_281 {b x y : ℕ} (bound : b≤33944307615) (cop : x.Coprime y)
    (he : x^4+y^4=b^3*281^2) : False := by
  let classes : List (ℤ × ℤ) := [(7,4),(7,16),(16,1),(16,25),(28,1),(28,25),(31,4),(31,16)]
  refine exclude_fixed_cofactor 281 33944307615 17 7678 184272 (-231) 160 classes
    (by decide +kernel) (by decide +kernel) ?_ ?_ bound cop he
  · apply cubic_classes (-231) 160 [(0,1),(0,9),(7,0),(7,4),(12,1),(12,9),(15,0),(15,4)] [(1,1)] classes <;> decide +kernel
  · let gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
      (5,2,11,6,0x13,0x19482c),
      (7,6,11,6,0x17,0x2608a42c2216),
      (11,3,10,5,0x23b,0x747084878cae149101c151525215c4),
      (13,3,10,5,0x161b,0x149200040021e046223103c0001000a49000361a),
      (17,11,9,5,0x1a317,0x480200460c1c1080a315d00bc8c4c204010209189e805d462a0840c183900200901a316),
      (19,2,9,4,0x30af3,0x4c449474681a240060011c0610d020142e30a0206c25421041ba0a0cf01026e22e122081220282611b200000),
      (23,12,9,4,0x5335f,0x10cb102380d2521500042dc04a858499841013520228b81c441a2018e05824a0b0495100c703888301145c2026a424cc200950b00216e4a42a011c068219627acca0),
      (29,26,9,4,0x13d122f3,0x9082202c909c501d188290148052000901b0d090020020a02c2d7104804802a023a6006a441d8c0a124ce04140a00a36c402a2a011b6280281410399242818dc112b0032e202a0090090475a1a02820020048586c0480025009404a08c5c051c849a02208480000000),
      (31,11,8,4,0x121d47b7,0xca121308250c68414b80010680e3112402541b001104580b0ea202a16c081221405330c9800a252600815800809a43003126a2247000c8620052c4421140e026405040c8390cf40480500506351420c8044112414a9402203314020a2b020b8801285820e0511801c4e8404100823504250401c80000000),
      (37,27,8,3,0x165e211e9b,0x2830f280b1201d2248280869283d118c1612bc2b00240202358a8100421ca0e2c120520c9828a90426baa8262a108d4404b4961485023aa09c0e0c80919a0098033400082388e103da0270040991888240c4194c11812088c4c81007002de04389e2080016600c802cc48098381c80ae2050943496901158842a320aaeb2104a8a2c98250240a3829c210840a8d6202012006a1ca43418c45e0a4b080a89225c024280a7860a365e211e9a),
      (41,6,8,3,0x1b382b50737,0x100d0c32280428216601400896700148e0b10018849b19020018a801010cd2448020f81081500b160490f4160004412514050e0302290601891902828c2021c456401042eb0008121090150868a80ce4008304600b07210401544084d306c0402940049846a440112b10c90014a0101b06590811540104270680310608013980a8b085404842408006ba104013511c20218a0a04c48c0304a2060385014524110003417849034680540840f820091259840400a8c00204c6c908c0046838940073488014033420a100a261858040000000000),
      (43,26,8,3,0x35883a3ee53,0xa0589224020020d4c9a00e00410da18181c9004a049c413800222400581e008e40a4981300524408c085c30013900532206a05600144322826010811e60440c0221ce608002261200640e0000ac1025a410804a0535058541500c02144820429880052d503031192089a00608460414a18702081205c922044500a64c6c80222010d6922000118884880843c06a210904310800c01ed2704106c201611455200818a8590000aa4212238401a0d490810155609024202c883041d82043082288a048100b008a2d4020e2c0e08111408e0829d0c402031810c0512084c03512004b8080000000000),
      (47,1,8,3,0x4351b2753df,0xc50508248008802052185200a0802030420008c240a52314118f4000310402004680000825a11120380608002200147008102491a42f8910008d0d95a02040020501081a2c116d0062230208a20080c088f34188099004200540021680840200416400200190170e1c01cb01188ae121c49004482100404420c8e25102514952002d17206800802400b30210c844c00004500b03165380024c000031500420406c042a28c4033700a0605525b0812d0a280d901488100402009b20b02a619142400048108a0906146c037080a080048a8021200400a005f6815080a1706362803003464c748104095810614926a1c0400c0902003d5841198041a0425c849921820280fc9509118e82000e71000000000000),
      (53,21,8,3,0x12dd703303aed3,0x1604183624102520a0040d1055530093400502501901704c9003059e842021024018821464884301488000014caea0c0403521202c08884419863104102a0e000786660031c230300040c00e40a92908a20100a2a3841006625105049303e0200034068100194c9a6100401a045a2440a0560444910f000464528092881080425c2045c40ae0211400487024011d880858240014b003896090a1441a2c100830627021210220846504015b01406d401053108220424207230608041a2c1142848348e0069400120d0808dc4012070900144203a811d1021d21008408a480a513100078449110350281122d102c0100432c994c0040b016000203e06490504523300410e2a2804022884a4a8138018100060621c6003330f000382a04104630cc1108881a024256010182ba99400000894061089314208c0120420210bcd060049907404c05205001648065550458100282520412360c103400000000000000),
      (59,16,8,3,0x22b62183e7b92bb,0x1728e12f8000102c204a0400a26980184d12cf0024a09d8113081090a8ba916739420228884203a0804c030c00518142c5302ac9a0a016240805004073301e6a410817041483400084030703100001440cce4138208188358b450058488a0080282204a018011886b038a10cc0c9013961b80420e3202e701d0902888684010a4000b9328060445a0229d64058bc01a8812d1806200471a32b0885c48a41120a286c78000986c21a8800a2c014628000111048b158081d85448168c58bc430208000d6d0ad10d4302069692641b08a1006487c003c6d49084870001042600c4b0204040a445212080c9010820100590000990918200085840e0432480e22d4180b0552cc042511489b82282810342215000154402604082903940061180100141902800100882f07500816143588a683044084889800240512200448046a000911224062114c2998805293204887458404b1a308006806d4002c2099b20346a00520a1185c1d859010c469c030005402100ac81c9812085355010c298504080149449831c10052e040240308030c90010a0ce1808c0012104e2090a0101dc412054044151c5ac03081200820000000000000000),
      (61,14,7,3,0x1713e6940a59f23b,0x8c00004820818304c01680320111000a002c4c00034000042214400238009089000686100008444244016011048210044018812908996894e000000100802ac58000000820041208ccc100880014289042a0023220a48c000800880010102c80308018081302180a001405000290601090802280000848100e10032d04a40080c000c4044042198840041484501202040040011400050ac088c021806400c40840d0000140984017680259800004000169104820420104301088280008908380482d808006000282400008a082631e0038400201021000109b810819000044004c0c81c88089c09819001100004c0840ec840004204020010e003c63208288000120a000300080da0900e08488000a0884061040210209044b4000100000cd200b74010c81400005810811801300c2018881a8500014400100102024051094100108cc210110118001808012905a6004380409080000a20084840304a000501400280c2064080c0086009a04040008800800189282262002a1048a1400088041998824100208000000d1aa008040000003948b4c884a408c011004209044034011211108000430b0004884800e200114221000016000191a00280044402600b4019060c082090000188000000000000000)]
    apply grid_sieve (-231) 160 7678 184272 256 classes gates (by decide)
    · simp only [gates,List.all_cons,List.all_nil,Bool.and_eq_true]
      repeat' apply And.intro
      all_goals decide +kernel
    · intro c hc
      simp only [classes,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

set_option maxRecDepth 16000 in
/-- Exclude the full cofactor-289 range using W=15+8i. -/
theorem no_cofactor_289 {b x y : ℕ} (bound : b≤33314958192) (cop : x.Coprime y)
    (he : x^4+y^4=b^3*289^2) : False := by
  let classes : List (ℤ × ℤ) := [(17,16),(17,28),(20,7),(20,31),(32,7),(32,31),(41,16),(41,28)]
  refine exclude_fixed_cofactor 289 33314958192 18 7606 182544 (-161) 240 classes
    (by decide +kernel) (by decide +kernel) ?_ ?_ bound cop he
  · apply cubic_classes (-161) 240 [(0,7),(0,15),(1,0),(1,12),(4,7),(4,15),(9,0),(9,12)] [(2,1)] classes <;> decide +kernel
  · let gates : List (ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) := [
      (5,2,11,6,0x13,0x19482c),
      (7,6,11,6,0x17,0x88605a00c8e8),
      (11,3,10,5,0x23b,0x888210384300a8446000288489023a),
      (13,3,10,5,0x161b,0x1212000d028c300010008004002618a0500064249e4),
      (17,11,9,5,0x1a317,0x741705cef3a0a82e6b9d0741705ceb3a0a82e7b9d0741705ce93a0b82e739d0741725ce8),
      (19,2,9,4,0x30af3,0x1808480351288127102010a889070012e04042c81888887010950210b0c24409460602222119082058217030af2),
      (23,12,9,4,0x5335f,0x1180865214a090133192601228391038281d0750041049603c04ea4c0848827022540a05115598015040cf018218aa52030000d782c22cc4430465820924ac07acca0),
      (29,26,9,4,0x13d122f3,0x101104240a39093250462e04a012803602400040090b0d0141001208eb50150048560065c40c6e08a073248540140a0540236c1b62015028140150926702883b1811d30035090054056b8824004140586848010001203600a402903a310526484e28121044040000000),
      (31,11,8,4,0x121d47b7,0x128200e601046a0e2742020c0a230020942c105604171018a0105152804406208920a62841900a802831a19e80900820641c81c04c809622108a190c400b511238008600624ac00404d4a4c0103864c005244280a6150b60400161d4418008822e4804a83034071888297000241286340194242600000000),
      (37,27,8,3,0x165e211e9b,0x8384084a4a93201423838082970086120825401027cae131822102faa0211614048e0583620452d210454219140240035a4028223014c51322e1300522403a07688309b34842043820e5048066647019031b26b26c604c071333009073820e10200966c8608b702e0122500643a266519406220a012d600120144c21510425a5100360d0389114344202a7a04220c643a9f20403520824308074a080e062140264ad290810e089a1dee164),
      (41,6,8,3,0x1b382b50737,0x7210e29a802a0761a2000880b3005a8a01b30200c2956803402282901008a21020c004f39291020118095192488a340112cc1a0060180060810190013044109004121129004008108101083495c1524110081000482dc0f08218640500002c505091836c2800a1b60c484051a000050930c2087819a0900040824412541d486084040840801004a442410048411064004c04083000c03002c99a44016288924c5480c402044a4e78001820422880404a0a205600b54a1802066c028ac0066808800a2c3702a00aca38427001b382b50736),
      (43,26,8,3,0x35883a3ee53,0x6b301014042032060540c24214102146089101251490448034710120918420c4007810f41001080006259c44411854282c2020015347006a10040a0520b08063001068045c60412081104f2e82412030008421e007040e52a3020004e4600183016c0a411080b04c24100448c4520001702db404200102682260144816a100e8010188123210bc0284029042a0a20c0b008864440491010025522a801818690203070384084300203640236000243a1229090230440aa08321260c20c0120694048a132048106080226dc002528043620041211228250502014364501008a28e2104a77c5c11ac),
      (47,1,8,3,0x4351b2753df,0x110809186a385a10a6202e10b183802f8003344032a449420210128ac00072be005400297084104b845271818208d078900120412fe2026290001000423016220001d8c45540228a05000e002011d22e01809a09080c1011006152168814b81894a700c07404900822ba81028c004580484000414844a34c9810230408a120605000308284010480889d9405213261e05440c04406e00110201200e070924ba0101f10424e050540211802c00c100c0804888000409148a3421118c220680204082c34a814069104926002100848530021263a2243124d023124001080ce0502a002080021618409820080850408920102044851252c14f0481100000600a404c8104108000721400880500c00c60000000000000),
      (53,21,8,3,0x12dd703303aed3,0x1604183624102520a0040d1055530093400502501901704c9003059e842021024018821464884301488000014caea0c0403521202c08884419863104102a0e000786660031c230300040c00e40a92908a20100a2a3841006625105049303e0200034068100194c9a6100401a045a2440a0560444910f000464528092881080425c2045c40ae0211400487024011d880858240014b003896090a1441a2c100830627021210220846504015b01406d401053108220424207230608041a2c1142848348e0069400120d0808dc4012070900144203a811d1021d21008408a480a513100078449110350281122d102c0100432c994c0040b016000203e06490504523300410e2a2804022884a4a8138018100060621c6003330f000382a04104630cc1108881a024256010182ba99400000894061089314208c0120420210bcd060049907404c05205001648065550458100282520412360c103400000000000000),
      (59,16,8,3,0x22b62183e7b92bb,0x408082554561480005a35023468800456020e308a022041c24200f0484c8105c064984481148328800c520c812dc04a00480b20a0a400ac4849014840c216504e802304e48900009c8117032050a0500c84200540812501bc07404b428a02c02a0204a3148511002100350a0141f40200a10c4641b3014481409030a6c115422000991a82002c8940445320685a8c2045000ac0a110c2c36420203cc0704060184040800c8e031b1810218184728060510029b0884381120840808e4588182c42928e4020a4202001203a51a5910033be002210048809180cd02c80406406430224082646701240041092c381146980019d08818000c0bc0e00366a8b11022086010870408100482cd41928041620159802510127020a2d0210486b0d4100141b22802180191605900409e8210262831c404c08c20166400209244824680585112208685004c3880159641019143440841a8020086844962069100108085a242262c7000971201a08627140a00054003d2c210c2152a90000042c23958d0801c084008d190380854014c30c010a90111c0cf122808052105a40868010d10c2240a260232058a0b0002c1c6022b62183e7b92ba),
      (109,25,7,2,0x1752639f4e85b003685cbe7192bb,0x1659408142a8842512a048b00000004084808740001000ac8029da91458541e018e401028200305041a584f0360c580d0d0108004090013134240170188009245144401448b2980840000220846b04820a040180140e2084c2434b0a021208c80000180024a882a243212530430234404d12a40411460013584048800120080411c5430806cca0090342c2c0101305100c00811080b0088c36000407cb000c8f0480022410800014a08247050c0440b011a80484481000d0a0464308098064310d0075095401080404061111c8c80516588004a0de44010008c4807101008090914c108c89580010a24209108a11230000e200c01900800014060c50c1421a20103289060046818e904504108a521c021000c212804a00150e0012ac8d1a8610c041bc209105050822188228461342c0bc95000918008000001340a04144205040356101100a4001c306122001202a1946c0220606432161e00260033b00940010115041808d0641c48021422c1191808898200d5210290110a40da3002884a141d20050800c2aa8051a802280122902d818aa080012a044001041003d36403d04000804cc150a01210302092290080b18056a0000b85200c2c600aa40000ca500002c2812a44410f00204c0216c2400104131938c00c059000085941d00b242927c0c1b0480000204a054005821c6608100081823080105c383200a8043108f505c8090002200015003100808b6000087044eaa583200213080010480608a910180806094480040900c1330246806224000cc2200c548402801b1180012eaa420218800b122214200d0924486000170c4088060678080000b18308036100600444d045980a1082094b184e08a848328201410021764230004000c184c404052400240204080451001ccadd1380a9310262000a094b180281042b18448806421100010061905b002c600d02849c0710688148000220440139084083872000910020802b020492016e09804014630060080014f3802a042018912201005804200002100d004022448c02102a00e7940008030063140100c83b402490206a00820044800270e081084e401102200009408b04701c90a058031a006d04c300400044213008910c6a1040a00c694828002320464a80e45da99c00451008102012001250101190c18001000621374200414020a6090a88390c69482084280cd1059110030043600860c68000080f3030088118740003091248580214222468008c20212aba4000c46c00a010951802219800122300b120664180481000914830080c044a88300904000864200260d2ab9107080003688080460054000220004809d0578846100a80260e1d04008620c0800408331c20d00150290200000906c181f24a126805c14d080004d018018e4c6410400121b4201902007841112a40a1a0000529800012a8031a180250e80002b500c680804a24820604240285419900800105e01365e004104001102a400082a8c0da04a2400a200ac500aaa1800850025c142908a0062d81284404a042558020c8880c4c41a21420091c1305880c10544040014806e60032003c3426130302201b14c2a024002243061c00128044043560105021141028164000000800c4800549e81a164310a208c2208505044821ec1018430ac589aa4003854002900a4218004201c252884105104b8c0b1003048a604022c2141851830140000804c01802380006244288448212284000d489884194484808040470091880040113d8290008d34500989c44430101008401548570058461300c8086131028580040910900ac40681101850712082940000841220009078980069f010003618880680844080180450640401a1a160480299b0086151c4100802400089010d640031441012a459011620610652426122a08a92000c000009882420286961219082381400c0102820906b1082200001080ca689140111451248008c074012164640048100084058580d18360790d2c105060020a040138c03c150d144adca009a8004000170809081000000068902a452108aa140814d34000000000000000000000000000)]
    apply grid_sieve (-161) 240 7606 182544 256 classes gates (by decide)
    · simp only [gates,List.all_cons,List.all_nil,Bool.and_eq_true]
      repeat' apply And.intro
      all_goals decide +kernel
    · intro c hc
      simp only [classes,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide +kernel

end Arithmetic

/-- Unconditional bounds on b and the cofactor k, independently of both
remaining census hypotheses. -/
theorem parameter_bounds {b z x y : ℕ} (bhi : b≤1456256357804)
    (hx : 0<x) (hy : 0<y) (hc : x.Coprime y) (hz : b∣z)
    (hsum : x^4+y^4=b*z^2) (hsmall : b*z^2<3088257489493360278725196965477359217) :
    ∃ k, z=b*k ∧ 17≤k ∧ (∀ p ∈ k.primeFactors, p%8=1) ∧ b≤220261480241 ∧
      (k ≠ 17 → 41≤k ∧ b≤122475323887) ∧ (k ≠ 17 → k ≠ 41 → b≤83372455837) := by
  obtain ⟨k,hk⟩ := hz
  have kp : 0<k := by
    by_contra! h
    have k0 : k=0 := by omega
    rw [hk,k0] at hsum
    simp at hsum
    omega
  have rewriteN : b*z^2=b^3*k^2 := by rw [hk];ring
  have eqn := hsum.trans rewriteN
  rw [rewriteN] at hsmall
  have kres (p : ℕ) (hp : p ∈ k.primeFactors) : p%8=1 := by
    obtain ⟨pr,dvd,_⟩ := Nat.mem_primeFactors.mp hp
    have pz : p ∣ z := hk ▸ dvd_mul_of_dvd_right dvd b
    have ps : p ∣ x^4+y^4 := hsum ▸ dvd_mul_of_dvd_right (dvd_pow pz (by decide : 2≠0)) b
    apply prime_residue hc pr _ ps
    rintro rfl
    have four : 2^2 ∣ z^2 := pow_dvd_pow_of_dvd pz 2
    exact not_four hc (hsum ▸ dvd_mul_of_dvd_right four b)
  have tiers : k=1 ∨ k=17 ∨ k=41 ∨ 73≤k := by
    by_cases h : k<73
    · have tab : ∀ i : Fin 73, (0 < (i : ℕ)) → (∀ p ∈ (i : ℕ).primeFactors, p % 8 = 1) →
          (i : ℕ) = 1 ∨ (i : ℕ) = 17 ∨ (i : ℕ) = 41 := by decide +kernel
      have small : k = 1 ∨ k = 17 ∨ k = 41 := tab ⟨k,h⟩ kp kres
      exact small.imp_right (fun h => h.imp_right Or.inl)
    · omega
  have notOne : k ≠ 1 := by
    intro k1
    exact bounded_lucas bhi hx hy hc (by simpa [k1] using eqn)
  have k17 : 17≤k := by omega
  have upper {B K : ℕ} (hK : K≤k) (cut : 3088257489493360278725196965477359217 ≤
      (B+1)^3*K^2) : b≤B := by
    by_contra! h
    have lower := Nat.mul_le_mul (Nat.pow_le_pow_left (show B+1≤b by omega) 3)
      (Nat.pow_le_pow_left hK 2)
    omega
  refine ⟨k,hk,k17,kres,upper k17 (by decide),?_,?_⟩
  · intro ne
    have k41 : 41≤k := by omega
    exact ⟨k41,upper k41 (by decide)⟩
  · intro no17 no41
    have k73 : 73≤k := by omega
    exact upper k73 (by decide)

/-- After the cofactor-17 certificate, 41 is the smallest remaining cofactor.
All higher cofactors give a second, stricter bound on b. -/
theorem parameter_bounds_after_seventeen {b z x y : ℕ} (bhi : b≤1456256357804)
    (hx : 0<x) (hy : 0<y) (hc : x.Coprime y) (hz : b∣z)
    (hsum : x^4+y^4=b*z^2) (hsmall : b*z^2<3088257489493360278725196965477359217) :
    ∃ k, z=b*k ∧ 41≤k ∧ (∀ p ∈ k.primeFactors, p%8=1) ∧ b≤122475323887 ∧
      (k≠41 → 73≤k ∧ b≤83372455837) := by
  obtain ⟨k,hk,_,kres,small,h41,h73⟩ := parameter_bounds bhi hx hy hc hz hsum hsmall
  have no17 : k≠17 := by
    rintro rfl
    apply no_cofactor_seventeen small hc
    rw [hsum,hk];ring
  obtain ⟨k41,upper⟩ := h41 no17
  refine ⟨k,hk,k41,kres,upper,fun d => ⟨?_,h73 no17 d⟩⟩
  by_contra! h
  have tab : ∀ i : Fin 73, (41 ≤ (i : ℕ)) →
      (∀ p ∈ (i : ℕ).primeFactors, p % 8 = 1) → (i : ℕ) = 41 := by decide +kernel
  exact d (tab ⟨k,h⟩ k41 kres)

/-- The two verified Gaussian charts force k ≥ 73. The next prime
cofactors give the upper bounds for each remaining stratum. -/
theorem parameter_bounds_after_fortyone {b z x y : ℕ} (bhi : b≤1456256357804)
    (hx : 0<x) (hy : 0<y) (hc : x.Coprime y) (hz : b∣z)
    (hsum : x^4+y^4=b*z^2) (hsmall : b*z^2<3088257489493360278725196965477359217) :
    ∃ k, z=b*k ∧ 73≤k ∧ (∀ p ∈ k.primeFactors, p%8=1) ∧ b≤83372455837 ∧
      (k≠73 → 89≤k ∧ b≤73054083499) ∧ (k≠73 → k≠89 → b≤68980024602) := by
  obtain ⟨k,hk,_,kres,bound,next⟩ := parameter_bounds_after_seventeen bhi hx hy hc hz hsum hsmall
  have changeN : b*z^2=b^3*k^2 := by rw [hk];ring
  have no41 : k≠41 := by
    rintro rfl
    exact no_cofactor_fortyone bound hc (hsum.trans changeN)
  obtain ⟨k73,cap⟩ := next no41
  have cases : k=73 ∨ k=89 ∨ 97≤k := by
    by_cases lt : k<97
    · have tab : ∀ i : Fin 97, (73 ≤ (i : ℕ)) → (∀ p ∈ (i : ℕ).primeFactors, p%8=1) →
          (i : ℕ)=73 ∨ (i : ℕ)=89 := by decide +kernel
      exact (tab ⟨k,lt⟩ k73 kres).imp_right Or.inl
    · omega
  rw [changeN] at hsmall
  have upper {B K : ℕ} (le : K≤k) (cut : 3088257489493360278725196965477359217 ≤ (B+1)^3*K^2) :
      b≤B := by
    by_contra! h
    have mul := Nat.mul_le_mul (Nat.pow_le_pow_left (show B+1≤b by omega) 3) (Nat.pow_le_pow_left le 2)
    omega
  refine ⟨k,hk,k73,kres,cap,fun d => ⟨by omega,upper (K:=89) (by omega) (by decide)⟩,?_⟩
  exact fun no73 no89 => upper (K:=97) (by omega) (by decide)

/-- For every remaining cofactor the norm must be 1 modulo 16. Three
quartic residue tests restrict it further at 5, 13, and 29. -/
theorem cofactor_residues {b k x y : ℕ} (kp : 0<k) (cop : x.Coprime y)
    (pr : ∀ p ∈ k.primeFactors, p%8=1) (he : x^4+y^4=b^3*k^2) :
    b%16=1 ∧ (b^3*k^2)%5 ∈ [1,2] ∧ (b^3*k^2)%13 ∈ [1,2,3,4,5,6,9,10,12] ∧
      (b^3*k^2)%29 ∈ [1,2,3,7,8,10,11,12,14,15,16,17,18,19,20,21,23,24,25,26,27] := by
  have list_prod (l : List ℕ) : (∀ p ∈ l, p%8=1) → l.prod%8=1 := by
    induction l with
    | nil => decide
    | cons p l ih =>
      intro mem
      have a := mem p List.mem_cons_self
      have c := ih (fun q h => mem q (List.mem_cons_of_mem _ h))
      rw [List.prod_cons,Nat.mul_mod,a,c]
  have k8 : k%8=1 := by
    rw [←Nat.prod_primeFactorsList kp.ne']
    apply list_prod
    intro p h
    exact pr p (List.mem_toFinset.mpr h)
  have b2 : b%2=1 := by
    by_contra! h
    have d : 2∣b := Nat.dvd_of_mod_eq_zero (by omega)
    have four : 4∣b^3 := (pow_dvd_pow_of_dvd d 2).trans (pow_dvd_pow b (by decide : 2≤3))
    exact not_four cop (he ▸ dvd_mul_of_dvd_left four _)
  have cast (p : ℕ) : (x:ZMod p)^4+(y:ZMod p)^4=((b^3*k^2:ℕ):ZMod p) := by
    simpa using congrArg (fun n : ℕ => (n:ZMod p)) he
  have test16 : ∀ a c : ZMod 16, a.val%2=1 → c.val%8=1 → ∀ i j : ZMod 16,
      i^4+j^4=a^3*c^2 → a.val=1 := by decide +kernel
  have s := test16 (b:ZMod 16) (k:ZMod 16)
  simp only [ZMod.val_natCast] at s
  have r16 := s (by omega) (by omega) (x:ZMod 16) (y:ZMod 16) (by simpa using cast 16)
  have gate (p : ℕ) (vals : List ℕ) (hp : 1<p) (ok : ∀ i j : ZMod p,
      (i≠0 ∨ j≠0) → (i^4+j^4).val ∈ vals) : (b^3*k^2)%p ∈ vals := by
    have nz : (x:ZMod p)≠0 ∨ (y:ZMod p)≠0 := by
      by_contra! eq
      exact (Nat.not_coprime_of_dvd_of_dvd hp ((ZMod.natCast_eq_zero_iff _ _).mp eq.1)
        ((ZMod.natCast_eq_zero_iff _ _).mp eq.2)) cop
    have h := ok (x:ZMod p) (y:ZMod p) nz
    rwa [cast p,ZMod.val_natCast] at h
  exact ⟨r16,gate 5 _ (by decide) (by decide +kernel),gate 13 _ (by decide) (by decide +kernel),
    gate 29 _ (by decide) (by decide +kernel)⟩

/-- For each nonzero cofactor residue there are 2, 9, and 21 admitted
norm residues at 5, 13, and 29. Together with b ≡ 1 modulo 16 these give
378 classes modulo 30160 by the Chinese remainder theorem. -/
theorem cofactor_residue_counts (k : ℕ) (kp : 0<k) (pr : ∀ p ∈ k.primeFactors, p%8=1) :
    ((List.range 5).filter (fun i => decide ((i^3*(k%5)^2)%5 ∈ [1,2]))).length=2 ∧
    ((List.range 13).filter (fun i => decide ((i^3*(k%13)^2)%13 ∈ [1,2,3,4,5,6,9,10,12]))).length=9 ∧
    ((List.range 29).filter (fun i => decide ((i^3*(k%29)^2)%29 ∈
      [1,2,3,7,8,10,11,12,14,15,16,17,18,19,20,21,23,24,25,26,27]))).length=21 := by
  have unit (p : ℕ) (prime : p.Prime) (bad : p%8≠1) : k%p≠0 := fun z =>
    bad (pr p (Nat.mem_primeFactors.mpr ⟨prime,Nat.dvd_of_mod_eq_zero z,kp.ne'⟩))
  have h5 := unit 5 (by decide) (by decide)
  have h13 := unit 13 (by decide) (by decide)
  have h29 := unit 29 (by decide) (by decide)
  have a : ∀ j : Fin 5, j.val≠0 →
      ((List.range 5).filter (fun i => decide ((i^3*j.val^2)%5 ∈ [1,2]))).length=2 := by decide +kernel
  have c : ∀ j : Fin 13, j.val≠0 →
      ((List.range 13).filter (fun i => decide ((i^3*j.val^2)%13 ∈ [1,2,3,4,5,6,9,10,12]))).length=9 := by decide +kernel
  have e : ∀ j : Fin 29, j.val≠0 → ((List.range 29).filter (fun i => decide ((i^3*j.val^2)%29 ∈
      [1,2,3,7,8,10,11,12,14,15,16,17,18,19,20,21,23,24,25,26,27]))).length=21 := by decide +kernel
  exact ⟨a ⟨_,Nat.mod_lt k (by decide)⟩ h5,c ⟨_,Nat.mod_lt k (by decide)⟩ h13,
    e ⟨_,Nat.mod_lt k (by decide)⟩ h29⟩

private theorem census_cap {b k B K : ℕ} (small : b^3*k^2<3088257489493360278725196965477359217)
    (le : K≤k) (cut : 3088257489493360278725196965477359217 ≤ (B+1)^3*K^2) : b≤B := by
  by_contra! h
  have lower := Nat.mul_le_mul (Nat.pow_le_pow_left (show B+1≤b by omega) 3) (Nat.pow_le_pow_left le 2)
  omega

/-- Check the small gap at the top of a cofactor's size bound against a
necessary condition P. Larger cofactors already have the sharper bound. -/
private theorem filtered_cap {b k K B S : ℕ} {P : ℕ → ℕ → Prop}
    (small : b^3*k^2<3088257489493360278725196965477359217) (le : K≤k) (hit : P b k)
    (coarse : 3088257489493360278725196965477359217≤(B+1)^3*K^2)
    (next : 3088257489493360278725196965477359217≤(S+1)^3*(K+1)^2)
    (gap : ∀ i : Fin (B-S), ¬P (S+1+i.val) K) : b≤S := by
  by_cases eq : k=K
  · subst k
    have old := census_cap small le coarse
    by_contra! h
    let i : Fin (B-S) := ⟨b-(S+1),by omega⟩
    have atB : S+1+i.val=b := by dsimp [i];omega
    exact gap i (by rw [atB];exact hit)
  · exact census_cap small (K:=K+1) (by omega) next

/-- The stated cutoff entails the full checked b-bound for each listed cofactor. -/
theorem small_cofactors_excluded {b k x y : ℕ}
    (known : k ∈ [73,89,97,113,137,193,233,241,257,281,289]) (cop : x.Coprime y)
    (eqn : x^4+y^4=b^3*k^2) (small : b^3*k^2<3088257489493360278725196965477359217) : False := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at known
  rcases known with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact no_cofactor_73 (census_cap small (le_refl 73) (by decide)) cop eqn
  · exact no_cofactor_89 (census_cap small (le_refl 89) (by decide)) cop eqn
  · exact no_cofactor_97 (census_cap small (le_refl 97) (by decide)) cop eqn
  · exact no_cofactor_113 (census_cap small (le_refl 113) (by decide)) cop eqn
  · exact no_cofactor_137 (census_cap small (le_refl 137) (by decide)) cop eqn
  · exact no_cofactor_193 (census_cap small (le_refl 193) (by decide)) cop eqn
  · exact no_cofactor_233 (census_cap small (le_refl 233) (by decide)) cop eqn
  · exact no_cofactor_241 (census_cap small (le_refl 241) (by decide)) cop eqn
  · exact no_cofactor_257 (census_cap small (le_refl 257) (by decide)) cop eqn
  · exact no_cofactor_281 (census_cap small (le_refl 281) (by decide)) cop eqn
  · exact no_cofactor_289 (census_cap small (le_refl 289) (by decide)) cop eqn

set_option maxRecDepth 16000 in
/-- Every remaining candidate in the large-parameter census has cofactor
at least 313. The next two cofactor thresholds sharpen the norm bound. -/
theorem parameter_bounds_after_small_cofactors {b z x y : ℕ} (bhi : b≤1456256357804)
    (hx : 0<x) (hy : 0<y) (hc : x.Coprime y) (hz : b∣z)
    (hsum : x^4+y^4=b*z^2) (hsmall : b*z^2<3088257489493360278725196965477359217) :
    ∃ k, z=b*k ∧ 313≤k ∧ (∀ p ∈ k.primeFactors, p%8=1) ∧ b≤31589416817 ∧
      (b%16=1 ∧ (b^3*k^2)%5 ∈ [1,2] ∧ (b^3*k^2)%13 ∈ [1,2,3,4,5,6,9,10,12] ∧
      (b^3*k^2)%29 ∈ [1,2,3,7,8,10,11,12,14,15,16,17,18,19,20,21,23,24,25,26,27]) ∧
      (k≠313 → 337≤k ∧ b≤30071232849) ∧ (k≠313 → k≠337 → b≤29155558369) := by
  obtain ⟨k,hk,k73,kres,_⟩ := parameter_bounds_after_fortyone bhi hx hy hc hz hsum hsmall
  have product : b*z^2=b^3*k^2 := by rw [hk];ring
  rw [product] at hsmall hsum
  have tiers : k=313 ∨ k=337 ∨ 353≤k := by
    by_cases lt : k<353
    · have tab : ∀ i : Fin 353, (73 ≤ (i : ℕ)) → (∀ p ∈ (i : ℕ).primeFactors, p%8=1) →
          (i : ℕ) ∈ [73,89,97,113,137,193,233,241,257,281,289] ∨ (i : ℕ)=313 ∨ (i : ℕ)=337 := by decide +kernel
      rcases tab ⟨k,lt⟩ k73 kres with h|h|h
      · exact (small_cofactors_excluded h hc hsum hsmall).elim
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · omega
  let P (b k : ℕ) : Prop := b%16=1 ∧ (b^3*k^2)%5 ∈ [1,2] ∧ (b^3*k^2)%13 ∈ [1,2,3,4,5,6,9,10,12] ∧
      (b^3*k^2)%29 ∈ [1,2,3,7,8,10,11,12,14,15,16,17,18,19,20,21,23,24,25,26,27]
  have localConditions : P b k := cofactor_residues (by omega) hc kres hsum
  have cap313 (le : 313≤k) : b≤31589416817 := filtered_cap (P:=P) (B:=31589416896)
    hsmall le localConditions (by decide) (by decide) (by decide +kernel)
  have cap337 (le : 337≤k) : b≤30071232849 := filtered_cap (P:=P) (B:=30071232873)
    hsmall le localConditions (by decide) (by decide) (by decide +kernel)
  have cap353 (le : 353≤k) : b≤29155558369 := filtered_cap (P:=P) (B:=29155558436)
    hsmall le localConditions (by decide) (by decide) (by decide +kernel)
  exact ⟨k,hk,by omega,kres,cap313 (by omega),localConditions,
    fun h => ⟨by omega,cap337 (by omega)⟩,fun h t => cap353 (by omega)⟩

theorem main : H1 → H2 → OMA.R_mo_191889_R1.H3 := by
  intro first rest b z x y blo bhi sq primes hz hx hxy hy hc he cut
  have zp : 0<z := by
    by_contra! h
    have e : z=0 := by omega
    simp [e] at he
    omega
  have strict : x<y := by
    by_contra! h
    have e : x=y := by omega
    have one : x=1 := by simpa [←e] using hc
    have two : 2=b*z^2 := by simpa [←e,one] using he
    have le : b≤b*z^2 := by simpa using Nat.mul_le_mul_left b (show 1≤z^2 from pow_pos zp _)
    omega
  obtain ⟨k,hk,_,kres,upper,filters,h337,h353⟩ :=
    parameter_bounds_after_small_cofactors bhi hx (hx.trans strict) hc hz he cut
  have tri := triangle_of_quartic (x := (x:ℚ)) (y := (y:ℚ)) (z := (z:ℚ)) (b := (b:ℚ))
    (by exact_mod_cast hx) (by exact_mod_cast strict) (by exact_mod_cast zp) (by exact_mod_cast he)
  have val : b*z^2=b^3*k^2 := by rw [hk];ring
  rw [val] at he cut
  by_cases d : k=313
  · subst k
    exact first b x y blo upper sq primes filters tri hx strict hy hc he cut
  · obtain ⟨k337,smaller⟩ := h337 d
    exact rest b k x y blo smaller sq primes k337 kres
      (fun high => by by_contra no337; exact (Nat.not_lt_of_ge (h353 d no337)) high)
      filters tri hx strict hy hc he cut

end OMA.R_mo_191889_R1_H3_R1
