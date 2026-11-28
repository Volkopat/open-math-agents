import OMAReductions.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Data.Nat.Prime.Factorial

/-!
Under a strict counterexample every element of the primitive family divides
lcm(1,...,n-1). For any prime n<p<2n, reduction is injective on the family.
Pairing opposite residues forces *two* different multiples of one pair
(u,p-u), with p/2<u<n: there are more opposite pairs than possible u.

This is the pigeonhole step behind Lemma 2.1 of Balasubramanian and
Soundararajan, Acta Arith. 75 (1996), 1–40. The strict inequality gives
one extra pair. The residual finite divisor problem is restricted to
families containing this forced configuration. The two outer cases p=2n−1 and
p=2n−3 are excluded outright, the latter by a product bound on two cross gcds.
-/

namespace OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H1_R1

open Finset Filter

/-- A prime just below twice the family size (a classical short-interval bound). -/
def H1 : Prop := ∀ᶠ n : ℕ in atTop, ∃ p : ℕ, p.Prime ∧ n<p ∧ p<2*n ∧ (2*n-p)^4<n^3

/-- A family of divisors containing the four forced multiples cannot have n
elements with all reduced numerators below n, for these near-doubling primes. -/
def H2 : Prop := ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, p.Prime → n<p → p+3<2*n →
  (2*n-p)^4<n^3 → ∀ A ⊆ (Nat.lcmUpto (n-1)).divisors,
  (∀ a ∈ A, ∀ b ∈ A, a/a.gcd b<n) → ∀ u d e : ℕ,
  p/2<u → u<n → 0<d → d<e →
  u*d∈A → (p-u)*d∈A → u*e∈A → (p-u)*e∈A → A.card<n

section Proof

private theorem normalized {A : Finset ℕ} {n : ℕ} (h0 : 0∉A) (hg : A.gcd id=1)
    (small : ∀ a ∈ A, ∀ b ∈ A, a/a.gcd b<n) :
    A ⊆ (Nat.lcmUpto (n-1)).divisors := by
  let L := Nat.lcmUpto (n-1)
  intro a ha
  have ha0 : 0<a := Nat.pos_of_ne_zero (by rintro rfl; exact h0 ha)
  have hL : a ∣ A.gcd (fun b => L*b) := by
    apply Finset.dvd_gcd; intro b hb
    let d := a.gcd b
    have ha' : a/d*d=a := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
    have hb' : b/d*d=b := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
    have hapos : 0<a/d := by by_contra! h; rw [Nat.eq_zero_of_le_zero h,zero_mul] at ha'; omega
    have had : a/d ∣ L := Finset.dvd_lcm (f:=id) (s:=Icc 1 (n-1))
      (b:=a/d) (mem_Icc.mpr ⟨hapos,by have := small a ha b hb; change a/d<n at this; omega⟩)
    obtain ⟨k,hk⟩ := had
    refine ⟨k*(b/d),?_⟩
    calc L*b = (a/d*k)*(b/d*d) := by rw [← hk,hb']
         _ = (a/d*d)*(k*(b/d)) := by ring
         _ = _ := by rw [ha']
  change a ∣ A.gcd (fun b => L*id b) at hL
  rw [Finset.gcd_mul_left,hg,mul_one] at hL
  exact Nat.mem_divisors.mpr ⟨by simpa [L] using hL,Nat.lcmUpto_ne_zero _⟩

private theorem no_prime {n p a : ℕ} (hp : p.Prime) (hnp : n<p)
    (ha : a ∈ (Nat.lcmUpto (n-1)).divisors) : ¬ p ∣ a := by
  have hfac : Nat.lcmUpto (n-1) ∣ (n-1).factorial :=
    Finset.lcm_dvd (fun k hk => Nat.dvd_factorial (mem_Icc.mp hk).1 (mem_Icc.mp hk).2)
  intro h
  have hz := hp.dvd_factorial.mp ((h.trans (Nat.mem_divisors.mp ha).1).trans hfac)
  omega

private theorem distinct_mod {n p : ℕ} (hp : p.Prime) (hnp : n<p) (A : Finset ℕ)
    (hdiv : A ⊆ (Nat.lcmUpto (n-1)).divisors)
    (small : ∀ a ∈ A, ∀ b ∈ A, a/a.gcd b<n) :
    Set.InjOn (fun a => a%p) (A:Set ℕ) := by
  let _ : Fact p.Prime := ⟨hp⟩
  intro a ha b hb hab
  let d := a.gcd b
  have hd : ¬ p ∣ d := fun h => no_prime hp hnp (hdiv ha) (h.trans (Nat.gcd_dvd_left _ _))
  have hd' : (d:ZMod p)≠0 := fun h => hd ((ZMod.natCast_eq_zero_iff _ _).mp h)
  have hda : a/d*d=a := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hdb : b/d*d=b := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have hcast : (a:ZMod p)=(b:ZMod p) := by
    apply ZMod.val_injective p; simpa [ZMod.val_natCast] using hab
  have hcancel : ((a/d:ℕ):ZMod p)=((b/d:ℕ):ZMod p) := by
    apply mul_right_cancel₀ hd'
    rw [← Nat.cast_mul,← Nat.cast_mul,hda,hdb]; exact hcast
  have ax : a/d<p := (small _ ha _ hb).trans hnp
  have bx : b/d<p := by simpa [d,Nat.gcd_comm] using (small _ hb _ ha).trans hnp
  have eq : a/d=b/d := by
    simpa [ZMod.val_natCast,Nat.mod_eq_of_lt ax,Nat.mod_eq_of_lt bx] using congrArg ZMod.val hcancel
  rw [← hda,eq,hdb]

private theorem pair_shape {n p t a b : ℕ} (hp : p.Prime) (hnp : n<p) (hodd : Odd p)
    (hlo : t≤p/2) (hres : a%p=t) (hopp : b%p=p-t) (hap : ¬ p ∣ a)
    (hsmall : a/a.gcd b<n) (hsmall' : b/b.gcd a<n) :
    ∃ u d : ℕ, p/2<u ∧ u<n ∧ 0<d ∧
      ((u*d=a ∧ (p-u)*d=b) ∨ (u*d=b ∧ (p-u)*d=a)) := by
  let d := a.gcd b
  let x := a/d
  let y := b/d
  have hx : x*d=a := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have hy : y*d=b := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have hdx : x<n := hsmall
  have hdy : y<n := by simpa [y,d,Nat.gcd_comm] using hsmall'
  have ha : 0<a := Nat.pos_of_ne_zero (by rintro rfl; exact hap (dvd_zero _))
  have hd : 0<d := Nat.gcd_pos_of_pos_left _ ha
  have hxp : 0<x := by by_contra! h; rw [Nat.eq_zero_of_le_zero h,zero_mul] at hx; omega
  have hab : p ∣ a+b := Nat.dvd_of_mod_eq_zero (by rw [Nat.add_mod,hres,hopp,
    Nat.add_sub_of_le (by omega : t≤p),Nat.mod_self])
  have hsum : p ∣ (x+y)*d := by rwa [add_mul,hx,hy]
  have hxy : p ∣ x+y := (hp.dvd_mul.mp hsum).resolve_right
    (fun h => hap (h.trans (Nat.gcd_dvd_left _ _)))
  have hval : x+y=p := by
    obtain ⟨k,hk⟩ := hxy
    by_cases h2 : 2≤k
    · have := Nat.mul_le_mul_left p h2; omega
    · interval_cases k <;> simp_all
  obtain ⟨z,hz⟩ := hodd
  rcases le_total y x with h | h
  · exact ⟨x,d,by omega,hdx,hd,Or.inl ⟨hx,by rwa [show p-x=y by omega]⟩⟩
  · exact ⟨y,d,by omega,hdy,hd,Or.inr ⟨hy,by rwa [show p-y=x by omega]⟩⟩

private theorem repeated {n p : ℕ} (_hn : 3≤n) (hp : p.Prime) (hnp : n<p) (hp2n : p<2*n)
    (A : Finset ℕ) (hc : A.card=n) (hdiv : A ⊆ (Nat.lcmUpto (n-1)).divisors)
    (small : ∀ a ∈ A, ∀ b ∈ A, a/a.gcd b<n) :
    ∃ u d e : ℕ, p/2<u ∧ u<n ∧ 0<d ∧ d<e ∧
      u*d∈A ∧ (p-u)*d∈A ∧ u*e∈A ∧ (p-u)*e∈A := by
  classical
  let U := A.image (fun a => a%p)
  let V := U.filter (fun t => t≤p/2)
  let H := U.filter (fun t => ¬t≤p/2)
  let W := H.image (fun t => p-t)
  let C := V∩W
  have hu : U.card=n := (card_image_of_injOn (distinct_mod hp hnp A hdiv small)).trans hc
  have hr {r} (h : r∈U) : 0<r ∧ r<p := by
    obtain ⟨a,ha,rfl⟩ := mem_image.mp h
    exact ⟨Nat.pos_of_ne_zero (fun h => no_prime hp hnp (hdiv ha) (Nat.dvd_of_mod_eq_zero h)),Nat.mod_lt _ hp.pos⟩
  have hwc : W.card=H.card := by
    apply card_image_of_injOn; intro i hi j hj he
    have hi' := hr (mem_filter.mp hi).1
    have hj' := hr (mem_filter.mp hj).1
    change p-i=p-j at he; omega
  have hsplit : V.card+H.card=n := (card_filter_add_card_filter_not (s:=U) (fun t => t≤p/2)).trans hu
  have hsub : V∪W ⊆ Icc 1 (p/2) := by
    intro t ht
    rcases mem_union.mp ht with h | h
    · exact mem_Icc.mpr ⟨(hr (mem_filter.mp h).1).1,(mem_filter.mp h).2⟩
    · obtain ⟨r,hr',rfl⟩ := mem_image.mp h
      obtain ⟨hU,hh⟩ := mem_filter.mp hr'
      have hs := hr hU; exact mem_Icc.mpr ⟨by omega,by omega⟩
  have huc := card_le_card hsub
  rw [Nat.card_Icc] at huc
  have hcw := card_inter_add_card_union V W
  change C.card+_=_ at hcw
  have more : (Ico (p/2+1) n).card<C.card := by rw [Nat.card_Ico]; omega
  have hrep (t) (ht : t∈C) : ∃ u d : ℕ, p/2<u ∧ u<n ∧ 0<d ∧
      u*d∈A ∧ (p-u)*d∈A ∧ t=min ((u*d)%p) (((p-u)*d)%p) := by
    obtain ⟨hV,hW⟩ := mem_inter.mp ht
    obtain ⟨hU,htlo⟩ := mem_filter.mp hV
    obtain ⟨a,ha,har⟩ := mem_image.mp hU
    obtain ⟨r,hH,hrt⟩ := mem_image.mp hW
    obtain ⟨hU',_⟩ := mem_filter.mp hH
    obtain ⟨b,hb,hbr⟩ := mem_image.mp hU'
    have hu' := hr (mem_filter.mp hH).1
    have hbr' : b%p=p-t := by omega
    obtain ⟨u,d,hu₁,hu₂,hd,hpair⟩ := pair_shape hp hnp (hp.odd_of_ne_two (by omega))
      htlo har hbr' (no_prime hp hnp (hdiv ha)) (small _ ha _ hb) (small _ hb _ ha)
    rcases hpair with ⟨h1,h2⟩ | ⟨h1,h2⟩
    · refine ⟨u,d,hu₁,hu₂,hd,h1 ▸ ha,h2 ▸ hb,?_⟩
      rw [h1,h2,har,hbr',min_eq_left (by omega)]
    · refine ⟨u,d,hu₁,hu₂,hd,h1 ▸ hb,h2 ▸ ha,?_⟩
      rw [h1,h2,hbr',har,min_eq_right (by omega)]
  choose! u d h using hrep
  obtain ⟨i,hi,j,hj,hne,he⟩ := exists_ne_map_eq_of_card_lt_of_maps_to more
    (f:=u) (fun t ht => mem_Ico.mpr ⟨(h t ht).1,(h t ht).2.1⟩)
  obtain ⟨hui,hun,hdi,hai,hbi,hei⟩ := h i hi
  obtain ⟨_,_,hdj,haj,hbj,hej⟩ := h j hj
  rw [← he] at haj hbj hej
  have hdiff : d i ≠ d j := by intro h; exact hne (by rw [hei,h,← hej])
  rcases lt_or_gt_of_ne hdiff with hlt | hlt
  · exact ⟨_,_,_,hui,hun,hdi,hlt,hai,hbi,haj,hbj⟩
  · exact ⟨_,_,_,hui,hun,hdj,hlt,haj,hbj,hai,hbi⟩


/-- Consecutive multipliers at the top of the reduced-numerator range cannot
occur at two scales. The two cross gcds have product dividing s*t. -/
private theorem consecutive {A : Finset ℕ} {v d e : ℕ} (hv : 0<v)
    (hd : 0<d) (hde : d<e)
    (small : ∀ a ∈ A, ∀ b ∈ A, a/a.gcd b<v+2)
    (hud : (v+1)*d∈A) (hvd : v*d∈A)
    (hue : (v+1)*e∈A) (hve : v*e∈A) : False := by
  let u := v+1
  let g := e.gcd d
  let s := e/g
  let t := d/g
  have hg : 0<g := Nat.gcd_pos_of_pos_right _ hd
  have hsg : s*g=e := Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)
  have htg : t*g=d := Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)
  have ht : 0<t := Nat.pos_of_ne_zero (fun hz => hd.ne' (by simpa [hz] using htg.symm))
  have hts : t<s := by
    exact Nat.lt_of_mul_lt_mul_right (show t*g < s*g by rwa [htg,hsg])
  have hs : 0<s := by omega
  have hcop : s.Coprime t := Nat.coprime_div_gcd_div_gcd hg
  have hu : 0<u := Nat.succ_pos _
  have cross {x y : ℕ} (hx : x*g∈A) (hy : y*g∈A) : x≤u*x.gcd y := by
    have h : (x*g)/((x*g).gcd (y*g))≤u := by have := small _ hx _ hy; dsimp [u]; omega
    have hm := Nat.mul_le_mul_right ((x*g).gcd (y*g)) h
    rw [Nat.div_mul_cancel (Nat.gcd_dvd_left _ _),Nat.gcd_mul_right,← Nat.mul_assoc] at hm
    exact Nat.le_of_mul_le_mul_right hm hg
  have hus : u*s*g∈A := by rw [Nat.mul_assoc,hsg]; exact hue
  have hut : u*t*g∈A := by rw [Nat.mul_assoc,htg]; exact hud
  have hvs : v*s*g∈A := by rw [Nat.mul_assoc,hsg]; exact hve
  have hvt : v*t*g∈A := by rw [Nat.mul_assoc,htg]; exact hvd
  let X := (u*s).gcd (v*t)
  let Y := (u*t).gcd (v*s)
  have hX : s≤X := Nat.le_of_mul_le_mul_left (cross hus hvt) hu
  have hY : t≤Y := Nat.le_of_mul_le_mul_left (cross hut hvs) hu
  have hvs' : v*s≤u*Y := by simpa [Y,Nat.gcd_comm] using cross hvs hut
  have hx : X*Y ∣ u^2*(s*t) := by
    simpa only [pow_two,mul_mul_mul_comm] using
      (Nat.mul_dvd_mul (Nat.gcd_dvd_left (u*s) (v*t)) (Nat.gcd_dvd_left (u*t) (v*s)))
  have hy : X*Y ∣ v^2*(s*t) := by
    have hh := Nat.mul_dvd_mul (Nat.gcd_dvd_right (u*s) (v*t)) (Nat.gcd_dvd_right (u*t) (v*s))
    convert hh using 1 <;> ring
  have huv : u.Coprime v := by show (v+1).gcd v=1; rw [Nat.add_comm]; simp
  have hp : (u^2).gcd (v^2)=1 := (huv.pow_left 2).pow_right 2
  have hxy := Nat.dvd_gcd hx hy
  rw [Nat.gcd_mul_right,hp,one_mul] at hxy
  have hle := Nat.le_of_dvd (Nat.mul_pos hs ht) hxy
  have heX : X=s := by
    by_contra! h
    have h' : s<X := by omega
    exact (not_lt_of_ge hle) (calc s*t < X*t := Nat.mul_lt_mul_of_pos_right h' ht
                                 _ ≤ X*Y := Nat.mul_le_mul_left _ hY)
  have heY : Y=t := by
    rw [heX] at hle
    exact le_antisymm (Nat.le_of_mul_le_mul_left hle hs) hY
  have hsv : s ∣ v := hcop.dvd_of_dvd_mul_right (heX ▸ Nat.gcd_dvd_right (u*s) (v*t))
  have hbound := Nat.le_of_dvd hv hsv
  rw [heY] at hvs'
  change v*s≤(v+1)*t at hvs'
  have hstep := Nat.mul_le_mul_left v (show t+1 ≤ s by omega)
  rw [Nat.mul_add,Nat.mul_one] at hstep
  rw [Nat.add_mul,Nat.one_mul] at hvs'
  omega

theorem main : H1 → H2 → OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1.H1 := by
  intro primes obstruction
  filter_upwards [primes,obstruction,eventually_ge_atTop 3] with n hp ho hn
  intro A hc h0 hg
  by_contra! h
  have small (a) (ha:a∈A) (b) (hb:b∈A) : a/a.gcd b<n := h a ha b hb
  have hdiv := normalized h0 hg small
  obtain ⟨p,pp,hp₁,hp₂,hgap⟩ := hp
  obtain ⟨u,d,e,hu,hu',hd,hde,ha,hb,ha',hb'⟩ := repeated hn pp hp₁ hp₂ A hc hdiv small
  by_cases hwide : p+3<2*n
  · have hs := ho p pp hp₁ hwide hgap A hdiv small u d e hu hu' hd hde ha hb ha' hb'
    omega
  · obtain ⟨k,hk⟩ := pp.odd_of_ne_two (by omega)
    let v := p-u
    have hv : 0<v := by dsimp [v]; omega
    have huv : u=v+1 := by dsimp [v]; omega
    have hnv : n=v+2 := by dsimp [v]; omega
    rw [huv] at ha ha'
    rw [hnv] at small
    exact consecutive hv hd hde small ha hb ha' hb'

end Proof

end OMA.R_Erdos402_erdos_402_variants_szegedy_zaharescu_weak_R1_H1_R1
