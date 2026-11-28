import OMAStatements.S_mo_366273
import Mathlib
namespace OMA.R_mo_366273_R1
open Finset Polynomial
open scoped Pointwise

lemma cubic_fiber {K : Type} [Field K] [Fintype K] [DecidableEq K] (a : K) :
    (univ.filter fun t : K => t^3-3*t=a).card ≤ 3 := by
  let f : K[X] := X^3-C 3*X-C a
  have deg : f.natDegree=3 := by dsimp [f]; compute_degree!
  have nz : f ≠ 0 := by intro h; simp [h] at deg
  apply le_trans _ deg.le
  apply card_le_degree_of_subset_roots
  intro t ht
  rw [mem_roots nz]
  have hv := (mem_filter.mp ht).2
  simpa [IsRoot,f] using sub_eq_zero.mpr hv

lemma three_sum {p : ℕ} (hp : p.Prime) (large : 5 ≤ p) (target : ZMod p) :
    ∃ x y z : ZMod p, x^3-3*x+(y^3-3*y)+(z^3-3*z)=target := by
  let _ : Fact p.Prime := ⟨hp⟩
  let h := fun t : ZMod p => t^3-3*t
  let S : Finset (ZMod p) := univ.image h
  let fibers := fun a : ZMod p => (univ.filter fun t => h t=a).card
  have bound (a : ZMod p) : fibers a ≤ 3 := cubic_fiber a
  have two (a : ZMod p) (w : a=2 ∨ a= -2) : fibers a ≤ 2 := by
    rcases w with rfl|rfl
    · have sub : (univ.filter fun t => h t=2) ⊆ ({2,-1} : Finset (ZMod p)) := by
        intro t ht
        have eqn := (mem_filter.mp ht).2
        change t^3-3*t=2 at eqn
        have zero : (t-2)*(t+1)^2=0 := by linear_combination eqn
        rcases mul_eq_zero.mp zero with hz|hz
        · simp [sub_eq_zero.mp hz]
        · have heq : t = -1 := by linear_combination (eq_zero_of_pow_eq_zero hz)
          simp [heq]
      exact (card_le_card sub).trans (card_le_two)
    · have sub : (univ.filter fun t => h t= -2) ⊆ ({-2,1} : Finset (ZMod p)) := by
        intro t ht
        have eqn := (mem_filter.mp ht).2
        change t^3-3*t= -2 at eqn
        have zero : (t+2)*(t-1)^2=0 := by linear_combination eqn
        rcases mul_eq_zero.mp zero with hz|hz
        · have ht' : t = -2 := by linear_combination hz
          simp [ht']
        · have heq : t = 1 := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hz)
          simp [heq]
      exact (card_le_card sub).trans (card_le_two)
  have h4 : (4 : ZMod p) ≠ 0 := by
    change ((4 : ℕ) : ZMod p) ≠ 0
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  have ne : (2 : ZMod p) ≠ -2 := by intro hh; apply h4; linear_combination hh
  have pm : (2 : ZMod p) ∈ S := mem_image.mpr ⟨2,mem_univ _,by dsimp [h]; ring⟩
  have nm : (-2 : ZMod p) ∈ S := mem_image.mpr ⟨-2,mem_univ _,by dsimp [h]; ring⟩
  have total : p=∑ a ∈ S,fibers a := by
    have hh := card_eq_sum_card_fiberwise (s := (univ : Finset (ZMod p))) (t:=S) (f:=h)
      (fun x hx => mem_image_of_mem h hx)
    simpa [fibers,ZMod.card] using hh
  have nmem := mem_erase.mpr ⟨ne.symm,nm⟩
  have sum1 := sum_erase_add S fibers pm
  have sum2 := sum_erase_add (S.erase 2) fibers nmem
  have cb := sum_le_sum (s:=((S.erase 2).erase (-2))) (fun a _ => bound a)
  simp only [sum_const,nsmul_eq_mul,card_erase_of_mem nmem,card_erase_of_mem pm] at cb
  have possible := two 2 (Or.inl rfl)
  have negative := two (-2) (Or.inr rfl)
  have atLeast : 2 ≤ S.card := by
    have sub : ({2,-2} : Finset (ZMod p)) ⊆ S := by
      intro a ha
      simp only [mem_insert,mem_singleton] at ha
      exact ha.elim (fun e => e.symm ▸ pm) (fun e => e.symm ▸ nm)
    simpa [ne] using card_le_card sub
  have cc : S.card - 1 - 1 + 2 = S.card := by omega
  have size : p+2 ≤ 3*S.card := by
    simp only [Nat.cast_id] at cb
    omega
  have non : S.Nonempty := ⟨_,pm⟩
  have b1 := ZMod.cauchy_davenport hp non non
  have b2 := ZMod.cauchy_davenport hp (non.add non) non
  have cardall : (S+S+S).card = Fintype.card (ZMod p) := by
    rw [ZMod.card]
    have up := card_le_univ (S+S+S)
    rw [ZMod.card] at up
    omega
  have ht : target ∈ S+S+S := (Finset.eq_univ_of_card _ cardall).symm ▸ mem_univ _
  obtain ⟨u,hu,w,hw,e⟩ := mem_add.mp ht
  obtain ⟨a,ha,b,hb,rfl⟩ := mem_add.mp hu
  obtain ⟨x,_,rfl⟩ := mem_image.mp ha
  obtain ⟨y,_,rfl⟩ := mem_image.mp hb
  obtain ⟨z,_,rfl⟩ := mem_image.mp hw
  exact ⟨x,y,z,e⟩

lemma prime_solution {p : ℕ} (hp : p.Prime) (n : ℤ) (even : Even n) :
    ∃ x y z : ZMod p, (n:ZMod p) = x^2*(x-1)+y^2*(y-1)+z^2*(z-1) ∧ x*(3*x-2) ≠ 0 := by
  by_cases h2 : p=2
  · subst p
    obtain ⟨k,rfl⟩ := even
    refine ⟨1,0,0,?_,by decide⟩
    push_cast
    have char2 : (2:ZMod 2)=0 := by decide
    linear_combination (k:ZMod 2)*char2
  by_cases h3 : p=3
  · subst p
    have test : ∀ a : ZMod 3, ∃ x y z : ZMod 3,
        a=x^2*(x-1)+y^2*(y-1)+z^2*(z-1) ∧ x*(3*x-2) ≠ 0 := by decide +kernel
    exact test _
  let _ : Fact p.Prime := ⟨hp⟩
  have large : 5 ≤ p := by
    have hh := hp.two_le
    have hf : p ≠ 4 := fun he => (by decide : ¬Nat.Prime 4) (he ▸ hp)
    omega
  have hthree : (3:ZMod p) ≠ 0 := by
    change ((3:ℕ):ZMod p) ≠ 0
    rw [Ne,ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (by decide) (by omega)
  obtain ⟨a,b,c,he⟩ := three_sum hp large (27*(n:ZMod p)+6)
  let u := (a+1)/3
  let v := (b+1)/3
  let w := (c+1)/3
  have eqn : (n:ZMod p) = u^2*(u-1)+v^2*(v-1)+w^2*(w-1) := by
    dsimp [u,v,w]
    field_simp
    linear_combination -he
  by_cases good : u*(3*u-2) = 0
  · rcases mul_eq_zero.mp good with first|second
    · refine ⟨1,v,w,?_,by ring_nf; exact one_ne_zero⟩
      simpa [first] using eqn
    · refine ⟨-(1/3),v,w,?_,?_⟩
      · have uu : u=2/3 := by apply (eq_div_iff hthree).mpr; linear_combination second
        rw [uu] at eqn
        convert eqn using 1 <;> field_simp <;> ring
      · field_simp
        simp only [neg_ne_zero,div_ne_zero_iff]
        constructor
        · intro hh; apply hthree; linear_combination -hh
        · exact hthree
  · exact ⟨u,v,w,eqn,good⟩

lemma solutions_prime_powers {p : ℕ} (hp : p.Prime) (n : ℤ) (even : Even n) (k : ℕ) :
    ∃ x y z : ℤ, (p:ℤ)^(k+1) ∣ x^2*(x-1)+y^2*(y-1)+z^2*(z-1)-n ∧
      ¬(p:ℤ) ∣ x*(3*x-2) := by
  let _ : Fact p.Prime := ⟨hp⟩
  induction k with
  | zero =>
    obtain ⟨a,b,c,eqn,nz⟩ := prime_solution hp n even
    refine ⟨(a.cast:ℤ),(b.cast:ℤ),(c.cast:ℤ),?_,?_⟩
    · rw [zero_add,pow_one,←ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simpa [ZMod.intCast_zmod_cast] using sub_eq_zero.mpr eqn.symm
    · rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      simpa [ZMod.intCast_zmod_cast] using nz
  | succ k ih =>
    obtain ⟨x,y,z,⟨c,eqn⟩,nz⟩ := ih
    let P : ℤ := (p:ℤ)^(k+1)
    let D := x*(3*x-2)
    have nz' : (D:ZMod p) ≠ 0 := by
      rw [Ne,ZMod.intCast_zmod_eq_zero_iff_dvd]
      exact nz
    let t : ℤ := ((-(c:ZMod p)/(D:ZMod p)).cast:ℤ)
    have small : (p:ℤ) ∣ c+D*t := by
      rw [←ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      dsimp [t]
      rw [ZMod.intCast_zmod_cast]
      field_simp
      ring
    obtain ⟨j,hj⟩ := small
    let Q : ℤ := (p:ℤ)^k
    have hP : P=(p:ℤ)*Q := by dsimp [P,Q]; ring
    refine ⟨x+P*t,y,z,?_,?_⟩
    · refine ⟨j+Q*t^2*(3*x-1+P*t),?_⟩
      change x^2*(x-1)+y^2*(y-1)+z^2*(z-1)-n=P*c at eqn
      change c+x*(3*x-2)*t=(p:ℤ)*j at hj
      rw [pow_succ]
      change _ = P*(p:ℤ)*_
      linear_combination eqn + P*hj + P*t^2*(3*x-1+P*t)*hP
    · intro hdvd
      apply nz
      have mult : (p:ℤ) ∣ (x+P*t)*(3*(x+P*t)-2) - x*(3*x-2) := by
        refine ⟨Q*t*(6*x-2+3*P*t),?_⟩
        rw [hP]
        ring
      exact (dvd_sub hdvd mult) |> fun hh => by simpa only [sub_sub_cancel] using hh

open OMA.S_mo_366273
def H1 : Prop := ∀ n : ℤ, Even n → ∀ m : ℕ, 0 < m → ∃ x y z : ZMod m,
    (n : ZMod m)=x^2*(x-1)+y^2*(y-1)+z^2*(z-1)

lemma everywhere : H1 := by
  intro n he m
  induction m using Nat.recOnPosPrimePosCoprime with
  | zero => omega
  | one => intro _; exact ⟨0,0,0,Subsingleton.elim _ _⟩
  | prime_pow p e hp hpos =>
    intro _
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hpos.ne'
    obtain ⟨x,y,z,div,_⟩ := solutions_prime_powers hp n he k
    refine ⟨x,y,z,?_⟩
    have hz : ((x^2*(x-1)+y^2*(y-1)+z^2*(z-1)-n : ℤ) : ZMod (p^(k+1)))=0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by simpa using div)
    push_cast at hz
    exact (sub_eq_zero.mp hz).symm
  | coprime a b ha hb co ia ib =>
    intro _
    obtain ⟨xa,ya,za,ea⟩ := ia (by omega)
    obtain ⟨xb,yb,zb,eb⟩ := ib (by omega)
    let E := ZMod.chineseRemainder co
    refine ⟨E.symm (xa,xb), E.symm (ya,yb), E.symm (za,zb), E.injective ?_⟩
    simp only [map_intCast,map_add,map_mul,map_pow,map_sub,map_one,RingEquiv.apply_symm_apply]
    exact Prod.ext ea eb

def H2 : Prop := ∀ n : ℤ, Even n →
    (∀ m : ℕ, 0 < m → ∃ x y z : ZMod m, (n:ZMod m)=x^2*(x-1)+y^2*(y-1)+z^2*(z-1)) →
    ∃ z t d : ℤ, t%3=1 ∧ Even ((t+2)/3-d) ∧ 108*(n-g z)+16=t*(t^2-12+27*d^2)

lemma divisor_criterion {n z t d : ℤ} (res : t%3=1) (par : Even ((t+2)/3-d))
    (eqn : 108*(n-g z)+16=t*(t^2-12+27*d^2)) : ∃ x y : ℤ, n=g x+g y+g z := by
  let s := (t+2)/3
  have ht : t=3*s-2 := by dsimp [s]; omega
  obtain ⟨k,hk⟩ := par
  change s-d=k+k at hk
  have hd : d=s-2*k := by omega
  rw [ht,hd] at eqn
  refine ⟨k,s-k,?_⟩
  unfold g at *
  nlinarith only [eqn]

lemma necessary_certificate {n x y z : ℤ} (h : n=g x+g y+g z) :
    ∃ t d : ℤ, t%3=1 ∧ Even ((t+2)/3-d) ∧ 108*(n-g z)+16=t*(t^2-12+27*d^2) := by
  refine ⟨3*(x+y)-2,y-x,by omega,⟨x,by omega⟩,?_⟩
  rw [h]
  unfold g
  ring

theorem main : H1 → H2 → type_of% @OMA.S_mo_366273.main := by
  intro hloc hglobal n he
  obtain ⟨z,t,d,res,par,eqn⟩ := hglobal n he (hloc n he)
  obtain ⟨x,y,h⟩ := divisor_criterion res par eqn
  exact ⟨x,y,z,h⟩
end OMA.R_mo_366273_R1
