import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1
import Mathlib

/-!

For a least odd-order counterexample, the product of the two nonidentity matching
shifts belongs to no normal subgroup of index three. Such a subgroup gives either
a smaller action containing both shifts, or three disjoint types of two-edge paths
that subdivide a smaller matching graph. Coincident compressed shifts give a square.
Consequently the product generates every finite 3-group quotient.

In a nilpotent counterexample the Sylow 3-subgroup is such a quotient and is cyclic.
The fourth lower central subgroup maps trivially to it. The projection kernel has
order prime to three, so a nontrivial fourth lower central term has a prime divisor
at least five. The other branch retains the index-three restriction.

The cubic branch is due to @JamesSlash (PR 592). The normalized matching and
regular reductions are PRs 5246 and 5820. We reuse the odd-order parent, PR 6558,
for its cycle parameterization, central-commutator and low-class results.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1_H1_R1
open SimpleGraph
open scoped commutatorElement

/-- Nilpotent odd group with a prime at least five in its fourth lower central subgroup. -/
def H1 : Prop :=
  ∀ (A : Type) [Group A] [Fintype A] (a b : A),
    Subgroup.closure ({a,b} : Set A) = ⊤ →
    a ≠ 1 → b ≠ 1 → a ≠ b → ¬ (Commute a ⁅a,b⁆ ∧ Commute b ⁅a,b⁆) →
    ¬ IsPGroup 2 ((⊤ : Subgroup A).lowerCentralSeries 3) → Odd (Nat.card A) →
    Group.IsNilpotent A →
    (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ Nat.card ((⊤ : Subgroup A).lowerCentralSeries 3)) →
    (∀ (N : Subgroup A), N.Normal → N.index = 3 → a*b ∉ N) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))

/-- Nonnilpotent odd group surviving every normal index-three descent. -/
def H2 : Prop :=
  ∀ (A : Type) [Group A] [Fintype A] (a b : A),
    Subgroup.closure ({a,b} : Set A) = ⊤ →
    a ≠ 1 → b ≠ 1 → a ≠ b → ¬ (Commute a ⁅a,b⁆ ∧ Commute b ⁅a,b⁆) →
    ¬ IsPGroup 2 ((⊤ : Subgroup A).lowerCentralSeries 3) → Odd (Nat.card A) →
    ¬ Group.IsNilpotent A →
    (∀ (N : Subgroup A), N.Normal → N.index = 3 → a*b ∉ N) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))

open OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1.HaarTwoQuotient (adj_mod cycle_from_period)

theorem subdivided_cycle {X E A : Type*} (B : SimpleGraph X) (G : SimpleGraph (Bool × A))
    (vertex : X ↪ A) (middle : E ↪ A) (l r : E → X)
    (covers : ∀ x y,B.Adj x y → ∃ z,(x=l z ∧ y=r z) ∨ (x=r z ∧ y=l z))
    (hl : ∀ z,G.Adj (false,vertex (l z)) (true,middle z))
    (hr : ∀ z,G.Adj (false,vertex (r z)) (true,middle z))
    {n : ℕ} (hn : 3≤n) (cycle : cycleGraph n ⊑ B) : cycleGraph (2*n) ⊑ G := by
  classical
  obtain ⟨f⟩ := cycle
  let idx (k : ℕ) : Fin n := ⟨k%n,Nat.mod_lt _ (by omega)⟩
  let next (i : Fin n) := idx (i.val+1)
  have succIdx (k : ℕ) : next (idx k)=idx (k+1) := by
    apply Fin.ext
    exact Nat.mod_add_mod k n 1
  have e (i : Fin n) := covers (f i) (f (next i))
    (f.toHom.map_adj ((adj_mod (by omega) i (next i)).mpr (.inl rfl)))
  choose z hz using e
  have step (i : Fin n) : G.Adj (false,vertex (f i)) (true,middle (z i)) ∧
      G.Adj (false,vertex (f (next i))) (true,middle (z i)) := by
    rcases hz i with ⟨e,e'⟩|⟨e,e'⟩ <;> rw [e,e'] <;>
      first | exact ⟨hl _,hr _⟩ | exact ⟨hr _,hl _⟩
  have inc (i : Fin n) : (next i).val=i.val+1 ∨ (next i).val=0 ∧ i.val+1=n := by
    by_cases hi : i.val+1<n
    · exact .inl (Nat.mod_eq_of_lt hi)
    · have h : i.val+1=n := by omega
      exact .inr ⟨by simp [next,idx,h],h⟩
  have notflip (i : Fin n) : next (next i) ≠ i := by
    intro eq
    have ev := congrArg Fin.val eq
    rcases inc i with h|h <;> rcases inc (next i) with t|t <;> omega
  have zi : Function.Injective z := by
    intro i j eq
    have x := hz i
    have y := hz j
    rw [eq] at x
    have alt : f i=f j ∨ (f (next i)=f j ∧ f (next j)=f i) := by grind
    rcases alt with same|⟨sj,si⟩
    · exact f.injective same
    · have e1 := f.injective sj
      have e2 := f.injective si
      exact (notflip i ((congrArg next e1).trans e2)).elim
  let p (k : ℕ) : Bool × A := if k%2=0 then (false,vertex (f (idx (k/2)))) else
    (true,middle (z (idx (k/2))))
  apply cycle_from_period G (2*n) (by omega) p
  · intro k
    by_cases ke : k%2=0
    · have ne : (k+1)%2≠0 := by omega
      simpa [p,ke,ne,show (k+1)/2=k/2 by omega] using (step (idx (k/2))).1
    · have even : (k+1)%2=0 := by omega
      simpa [p,ke,even,show (k+1)/2=k/2+1 by omega,succIdx] using (step (idx (k/2))).2.symm
  · simp [p,idx]
  · intro i j hi hj eq
    have house (i j : ℕ) (hi : i<2*n) (hj : j<2*n) (eq : idx (i/2)=idx (j/2)) : i/2=j/2 := by
      simpa [idx,Nat.mod_eq_of_lt (show i/2<n by omega),Nat.mod_eq_of_lt (show j/2<n by omega)]
        using congrArg Fin.val eq
    by_cases ei : i%2=0 <;> by_cases ej : j%2=0 <;> simp [p,ei,ej] at eq
    · have := house _ _ hi hj (f.injective eq)
      omega
    · have := house _ _ hi hj (zi eq)
      omega


theorem square {A : Type*} (G : SimpleGraph (Bool × A)) (x y v w : A) (xy : x≠y) (vw : v≠w)
    (xv : G.Adj (false,x) (true,v)) (xw : G.Adj (false,x) (true,w))
    (yv : G.Adj (false,y) (true,v)) (yw : G.Adj (false,y) (true,w)) : cycleGraph 4 ⊑ G := by
  let p : Fin 4 → Bool × A := ![(false,x),(true,v),(false,y),(true,w)]
  have inj : Function.Injective p := by
    intro i j eq
    fin_cases i <;> fin_cases j <;> simp_all [p]
  have map (i j : Fin 4) (adj : (cycleGraph 4).Adj i j) : G.Adj (p i) (p j) := by
    fin_cases i <;> fin_cases j <;> first
      | exact xv | exact xv.symm | exact xw | exact xw.symm | exact yv | exact yv.symm
      | exact yw | exact yw.symm | exact False.elim (by revert adj; decide)
  exact ⟨⟨⟨p,fun h => map _ _ h⟩,inj⟩⟩

theorem maximal_card {A : Type*} [Group A] [Finite A] (pgrp : IsPGroup 3 A)
    (M : Subgroup A) [M.Normal] (max : IsCoatom M) : Nat.card (A ⧸ M)=3 := by
  classical
  let f := QuotientGroup.mk' M
  have proper : M≠⊤ := max.1
  have nontrivial : Nontrivial (A ⧸ M) := by
    obtain ⟨x,h⟩ := SetLike.exists_not_mem_of_ne_top M proper
    exact ⟨f x,1,fun eq => h ((QuotientGroup.eq_one_iff x).mp eq)⟩
  have pg := pgrp.to_quotient M
  have dv : 3 ∣ Nat.card (A ⧸ M) := (pg.card_eq_or_dvd).resolve_left
    (ne_of_gt (Finite.one_lt_card_iff_nontrivial.mpr nontrivial))
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' 3 dv
  let C := Subgroup.zpowers x
  let J := C.comap f
  have le : M ≤ J := by
    intro z hz
    change f z ∈ C
    have id : f z=1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [id]; exact C.one_mem
  have top : J=⊤ := by
    apply max.2
    apply lt_of_le_of_ne le
    intro eq
    obtain ⟨z,hz⟩ := QuotientGroup.mk_surjective x
    have mem : z ∈ J := by
      change f z ∈ C
      change f z=x at hz
      rw [hz]; exact Subgroup.mem_zpowers x
    have val := (QuotientGroup.eq_one_iff z).mpr (eq ▸ mem)
    have xeq : x=1 := hz ▸ val
    simp [xeq] at hx
  have ctop : C=⊤ := by
    apply Subgroup.comap_injective (f := f) QuotientGroup.mk_surjective
    simpa [J] using top
  exact (orderOf_eq_card_of_zpowers_eq_top ctop).symm.trans hx

private theorem sylow_three_projection {A : Type} [Group A] [Finite A] [Group.IsNilpotent A]
    (divides : 3 ∣ Nat.card A) (P : Sylow 3 A) :
    ∃ f : A →* P, Function.Surjective f ∧ ¬ 3 ∣ Nat.card f.ker := by
  classical
  let i : (Nat.card A).primeFactors :=
    ⟨3, Nat.mem_primeFactors.mpr ⟨by decide, divides, Nat.card_pos.ne'⟩⟩
  let e := Sylow.directProductOfNormal (G:=A) (fun _ => inferInstance)
  let f₁ := Pi.evalMonoidHom (fun j : (Nat.card A).primeFactors => ∀ R : Sylow j A, R) i
  let f₂ := Pi.evalMonoidHom (fun R : Sylow 3 A => R) P
  let f : A →* P := f₂.comp (f₁.comp e.symm.toMonoidHom)
  have fs : Function.Surjective f := by
    intro x
    refine ⟨e (Pi.mulSingle i (Pi.mulSingle P x)), ?_⟩
    simp [f, f₁, f₂, Pi.evalMonoidHom]
  refine ⟨f,fs,?_⟩
  have index : f.ker.index = Nat.card P := by
    rw [Subgroup.index_ker,MonoidHom.range_eq_top.mpr fs,Subgroup.card_top]
  have cards : Nat.card P * Nat.card f.ker = Nat.card P * P.index := by
    rw [← index,Subgroup.index_mul_card, index,Subgroup.card_mul_index]
  have eq := Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α:=P)) cards
  exact eq ▸ P.not_dvd_index

/-- Avoiding index-three subgroups forces the product to generate every 3-group quotient. -/
theorem generate_quotient {A P : Type} [Group A] [Group P] [Finite P]
    (f : A →* P) (surj : Function.Surjective f) (pg : IsPGroup 3 P) (z : A)
    (avoid : ∀ (N : Subgroup A), N.Normal → N.index=3 → z ∉ N) :
    Subgroup.zpowers (f z) = ⊤ := by
  classical
  by_contra proper
  obtain ⟨M,max,contain⟩ := (eq_top_or_exists_le_coatom (Subgroup.zpowers (f z))).resolve_left proper
  let : M.Normal := ((Group.isNilpotent_of_finite_tfae (G:=P)).out 0 2 rfl rfl).mp pg.isNilpotent M max
  let g := (QuotientGroup.mk' M).comp f
  have gs : Function.Surjective g := QuotientGroup.mk_surjective.comp surj
  have idx : g.ker.index = 3 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr gs, Subgroup.card_top, maximal_card pg M max]
  exact avoid g.ker inferInstance idx
    (show g z = 1 from (QuotientGroup.eq_one_iff _).mpr (contain (Subgroup.mem_zpowers _)))

/-- For a nilpotent group of odd order, avoidance forces a large prime in a
nontrivial fourth lower central subgroup. -/
theorem large_prime {A : Type} [Group A] [Finite A] [Group.IsNilpotent A] (z : A)
    (odd : Odd (Nat.card A)) (four : ¬ IsPGroup 2 ((⊤ : Subgroup A).lowerCentralSeries 3))
    (avoid : ∀ (N : Subgroup A), N.Normal → N.index=3 → z ∉ N) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ Nat.card ((⊤ : Subgroup A).lowerCentralSeries 3) := by
  classical
  let D := (⊤ : Subgroup A).lowerCentralSeries 3
  have bot : D ≠ ⊥ := by
    intro h
    apply four
    change IsPGroup 2 D
    rw [h]
    exact IsPGroup.of_bot
  by_contra missing
  have three : IsPGroup 3 D := by
    apply (isPGroup_iff_primeFactors_card_subset (by decide : 3 ≠ 0)).mpr
    intro p hp
    have pr := Nat.prime_of_mem_primeFactors hp
    have dvd := Nat.dvd_of_mem_primeFactors hp
    have high : p < 5 := by by_contra! h; exact missing ⟨p,pr,h,dvd⟩
    have not2 : p ≠ 2 := by
      rintro rfl
      exact Nat.not_even_iff_odd.mpr odd (even_iff_two_dvd.mpr (dvd.trans D.card_subgroup_dvd_card))
    have low := pr.two_le
    have ne4 : p ≠ 4 := by rintro rfl; norm_num at pr
    have eq : p=3 := by omega
    subst p
    exact Nat.mem_primeFactors.mpr ⟨by decide,by decide,by decide⟩
  obtain ⟨x,hx,hne⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr bot)
  have dx : 3 ∣ orderOf x := by
    simpa only [Subgroup.orderOf_mk] using
      three.dvd_orderOf (g:=(⟨x,hx⟩ : D)) (fun h => hne (congrArg Subtype.val h))
  let P : Sylow 3 A := default
  obtain ⟨f,fs,coprime⟩ := sylow_three_projection (dx.trans (orderOf_dvd_natCard x)) P
  have gen := generate_quotient f fs P.isPGroup' z avoid
  let : IsCyclic P := ⟨f z, fun y => Subgroup.mem_zpowers_iff.mp
    (show y ∈ Subgroup.zpowers (f z) from gen ▸ Subgroup.mem_top y)⟩
  have one : (⊤ : Subgroup P).lowerCentralSeries 1 = ⊥ :=
    Subgroup.lowerCentralSeries_one_eq_bot_iff.mpr inferInstance
  have trivial : (⊤ : Subgroup P).lowerCentralSeries 3 ≤ ⊥ := by
    rw [← one]; exact (⊤ : Subgroup P).lowerCentralSeries_antitone (by decide)
  have mapped : D.map f ≤ (⊤ : Subgroup P).lowerCentralSeries 3 := by
    rw [show D = (⊤ : Subgroup A).lowerCentralSeries 3 from rfl, Subgroup.map_lowerCentralSeries]
    exact Subgroup.lowerCentralSeries_mono 3 le_top
  have id : f x = 1 := trivial (mapped (Subgroup.mem_map_of_mem f hx))
  exact coprime (dvd_trans dx (f.ker.orderOf_dvd_natCard (show x ∈ f.ker from id)))

set_option maxHeartbeats 4000000 in
theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1.H1 := by
  classical
  intro nilCase otherCase
  let graph {A : Type} [Mul A] (a b : A) :=
    SimpleGraph.fromRel (fun u v : Bool × A => u.1=false ∧ v.1=true ∧
      (v.2=u.2 ∨ v.2=u.2*a ∨ v.2=u.2*b))
  let good {A : Type} [Mul A] (a b : A) := ∃ k : ℕ,2≤k ∧ cycleGraph (2^k) ⊑ graph a b
  let left {A : Type} [Mul A] (a b : A) :=
    SimpleGraph.fromRel (fun u v : Bool × A => u.1=false ∧ v.1=true ∧
      (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))
  have flip {A : Type} [Group A] (a b : A) : Nonempty (graph a b ≃g left a b) := by
    let e : (Bool × A) ≃ (Bool × A) := {
      toFun z := (!z.1,z.2⁻¹), invFun z := (!z.1,z.2⁻¹)
      left_inv := by rintro ⟨s,x⟩; simp
      right_inv := by rintro ⟨s,x⟩; simp }
    have rot (x y c : A) : x⁻¹ = c*y⁻¹ ↔ y=x*c := by
      constructor
      · intro h
        calc y = x*(x⁻¹*y) := by group
             _ = x*c := by rw [h]; group
      · rintro rfl; simp
    refine ⟨⟨e, ?_⟩⟩
    rintro ⟨s,x⟩ ⟨t,y⟩
    cases s <;> cases t <;> simp [e,graph,left,SimpleGraph.fromRel,rot] <;> tauto

  have compress {A Q : Type} [Group A] [Group Q] (f : A →* Q) (a b : A)
      (nonid : f a≠1) (three : (f a)^3=1) (inv : f b=(f a)⁻¹)
      (recurse : ∀ x y : f.ker,x≠1 → y≠1 → x≠y → good x y) : good a b := by
    classical
    let G := graph a b
    let S : Fin 3 → A := ![a,1,b]
    let T : Fin 3 → A := ![1,b,a]
    let d : f.ker := ⟨b⁻¹*a⁻¹,by simp [MonoidHom.mem_ker,inv]⟩
    let e : f.ker := ⟨b*(a⁻¹*a⁻¹),by
      have ti : (f a)⁻¹^3=1 := by simpa only [inv_pow,inv_one] using congrArg Inv.inv three
      simpa [MonoidHom.mem_ker,inv,pow_succ,mul_assoc] using ti⟩
    let D : Fin 3 → f.ker := ![1,d,e]
    have tr : ∀ i : Fin 3,(D i:A)*a*T i=S i := by
      intro i
      fin_cases i <;> simp [S,T,D,d,e,mul_assoc]
    have distinct : f a≠(f a)⁻¹ := by
      intro eq
      have sq : f a*f a=1 := by simpa only [mul_inv_cancel] using congrArg (fun u => f a*u) eq
      exact nonid (by simpa [pow_succ,sq] using three)
    have si : Function.Injective (fun i => f (S i)) := by
      intro i j eq
      fin_cases i <;> fin_cases j <;> simp_all [S]
    let v : (Bool × f.ker) ↪ A := {
      toFun z := if z.1 then (z.2:A)*a else z.2
      inj' := by
        rintro ⟨s,x⟩ ⟨t,y⟩ eq
        have fx : f (x:A)=1 := x.property
        have fy : f (y:A)=1 := y.property
        cases s <;> cases t
        · exact Prod.ext rfl (Subtype.ext eq)
        · change (x:A)=(y:A)*a at eq
          exact (nonid (by simpa [fx,fy] using (congrArg f eq).symm)).elim
        · change (x:A)*a=(y:A) at eq
          exact (nonid (by simpa [fx,fy] using congrArg f eq)).elim
        · exact Prod.ext rfl (Subtype.ext (mul_right_cancel eq)) }
    let m : (f.ker × Fin 3) ↪ A := {
      toFun z := (z.1:A)*S z.2
      inj' := by
        rintro ⟨x,i⟩ ⟨y,j⟩ eq
        have fx : f (x:A)=1 := x.property
        have fy : f (y:A)=1 := y.property
        change (x:A)*S i=(y:A)*S j at eq
        have ij : i=j := si (by simpa [fx,fy] using congrArg f eq)
        subst j
        exact Prod.ext (Subtype.ext (mul_right_cancel eq)) rfl }
    let l (z : f.ker × Fin 3) := (false,z.1)
    let r (z : f.ker × Fin 3) := (true,z.1*D z.2)
    have shiftAdj (x : A) (i : Fin 3) : G.Adj (false,x) (true,x*S i) := by
      refine ⟨by simp,Or.inl ⟨rfl,rfl,?_⟩⟩
      fin_cases i
      · exact .inr (.inl rfl)
      · exact .inl (mul_one _)
      · exact .inr (.inr rfl)
    have hl (z : f.ker × Fin 3) : G.Adj (false,v (l z)) (true,m z) := shiftAdj _ _
    have hr (z : f.ker × Fin 3) : G.Adj (false,v (r z)) (true,m z) := by
      obtain ⟨x,i⟩ := z
      change G.Adj (false,((x:A)*D i)*a) (true,(x:A)*S i)
      have h : ∀ t : Fin 3,G.Adj (false,((x:A)*D i)*a) (true,(((x:A)*D i)*a)*T t) := by
        intro t
        fin_cases t
        · exact shiftAdj _ 1
        · exact shiftAdj _ 2
        · exact shiftAdj _ 0
      simpa only [mul_assoc,←mul_assoc (D i:A) a,tr] using h i
    by_cases di : Function.Injective D
    · have sep : d≠1 ∧ e≠1 ∧ d≠e := by
        refine ⟨fun h => ?_,fun h => ?_,fun h => ?_⟩
        · exact (by decide : (1:Fin 3)≠0) (di (show D 1=D 0 from h))
        · exact (by decide : (2:Fin 3)≠0) (di (show D 2=D 0 from h))
        · exact (by decide : (1:Fin 3)≠2) (di (show D 1=D 2 from h))
      obtain ⟨k,hk,cyc⟩ := recurse d e sep.1 sep.2.1 sep.2.2
      let B := graph d e
      have cases' (u w : Bool × f.ker) (h : u.1=false ∧ w.1=true ∧
          (w.2=u.2 ∨ w.2=u.2*d ∨ w.2=u.2*e)) : ∃ z,u=l z ∧ w=r z := by
        obtain ⟨x,y⟩ := u
        obtain ⟨x',y'⟩ := w
        obtain ⟨rfl,rfl,h|h|h⟩ := h
        · exact ⟨(y,0),rfl,Prod.ext rfl (by simpa [r,D] using h)⟩
        · exact ⟨(y,1),rfl,Prod.ext rfl h⟩
        · exact ⟨(y,2),rfl,Prod.ext rfl h⟩
      have covers (u w : Bool × f.ker) (edge : B.Adj u w) :
          ∃ z,(u=l z ∧ w=r z) ∨ (u=r z ∧ w=l z) := by
        rcases edge.2 with h|h
        · obtain ⟨z,h⟩ := cases' u w h
          exact ⟨z,.inl h⟩
        · obtain ⟨z,h,h'⟩ := cases' w u h
          exact ⟨z,.inr ⟨h',h⟩⟩
      have size : 3≤2^k := by have := Nat.pow_le_pow_right (by decide : 0<2) hk; omega
      refine ⟨k+1,by omega,?_⟩
      rw [pow_succ,Nat.mul_comm]
      exact subdivided_cycle B G v m l r covers hl hr size cyc
    · rw [Function.Injective] at di
      push Not at di
      obtain ⟨i,j,eq,ne⟩ := di
      let x : f.ker × Fin 3 := (1,i)
      let y : f.ker × Fin 3 := (1,j)
      have rr : r x=r y := by simp [r,x,y,eq]
      have vl : v (l x)≠v (r x) := fun h => Bool.false_ne_true (congrArg Prod.fst (v.injective h))
      have mm : m x≠m y := fun h => ne (congrArg Prod.snd (m.injective h))
      exact ⟨2,by decide,square G _ _ _ _ vl mm (hl x) (hl y) (hr x) (rr ▸ hr y)⟩
  have monotone {U A : Type} [Group U] [Group A] (f : U →* A) (inj : Function.Injective f)
      (a b : U) (h : good a b) : good (f a) (f b) := by
    obtain ⟨k,hk,cyc⟩ := h
    let u : (Bool × U) ↪ (Bool × A) := (Function.Embedding.refl Bool).prodMap ⟨f,inj⟩
    refine ⟨k,hk,cyc.trans (isContained_iff_exists_le_comap.mpr ⟨u,?_⟩)⟩
    intro v w edge
    have dir (v w : Bool × U) (s : v.1=false) (t : w.1=true)
        (h : w.2=v.2 ∨ w.2=v.2*a ∨ w.2=v.2*b) :
        (u v).1=false ∧ (u w).1=true ∧
          ((u w).2=(u v).2 ∨ (u w).2=(u v).2*f a ∨ (u w).2=(u v).2*f b) := by
      refine ⟨s,t,?_⟩
      rcases h with h|h|h
      · exact .inl (congrArg f h)
      · exact .inr (.inl ((congrArg f h).trans (map_mul f _ _)))
      · exact .inr (.inr ((congrArg f h).trans (map_mul f _ _)))
    refine ⟨fun eq => edge.ne (u.injective eq),?_⟩
    rcases edge.2 with ⟨s,t,h⟩|⟨s,t,h⟩
    · exact .inl (dir v w s t h)
    · exact .inr (dir w v s t h)
  have solve (n : ℕ) : ∀ (A : Type) [Group A] [Fintype A] (a b : A),
      Nat.card A = n → Odd (Nat.card A) → a ≠ 1 → b ≠ 1 → a ≠ b → good a b := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A _ _ a b size odd ha hb hab
      have smaller (H : Subgroup A) (proper : H ≠ ⊤) (x y : H)
          (hx : x ≠ 1) (hy : y ≠ 1) (hxy : x ≠ y) : good x y := by
        have small : Nat.card H < n := by
          rw [← size]
          exact lt_of_le_of_ne H.card_le_card_group (fun e => proper (H.card_eq_iff_eq_top.mp e))
        exact ih _ small H x y rfl (odd.of_dvd_nat H.card_subgroup_dvd_card) hx hy hxy
      have inside (H : Subgroup A) (proper : H ≠ ⊤) (am : a ∈ H) (bm : b ∈ H) : good a b := by
        let x : H := ⟨a,am⟩
        let y : H := ⟨b,bm⟩
        exact monotone H.subtype Subtype.coe_injective x y
          (smaller H proper x y (fun h => ha (congrArg Subtype.val h))
            (fun h => hb (congrArg Subtype.val h)) (fun h => hab (congrArg Subtype.val h)))
      by_cases generated : Subgroup.closure ({a,b} : Set A) ≠ ⊤
      · exact inside _ generated (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))
      push Not at generated
      let L := left a b
      have h0 (x : A) : L.Adj (false,x) (true,x) := ⟨by simp,.inl ⟨rfl,rfl,.inl rfl⟩⟩
      have h1 (x : A) : L.Adj (false,x) (true,a*x) := ⟨by simp,.inl ⟨rfl,rfl,.inr (.inl rfl)⟩⟩
      have h2 (x : A) : L.Adj (false,x) (true,b*x) := ⟨by simp,.inl ⟨rfl,rfl,.inr (.inr rfl)⟩⟩
      have convert (w : ∃ k : ℕ,2≤k ∧ cycleGraph (2^k) ⊑ L) : good a b := by
        obtain ⟨k,hk,h⟩ := w
        exact ⟨k,hk,h.trans (flip a b).some.symm.isContained⟩
      by_cases central : Commute a ⁅a,b⁆ ∧ Commute b ⁅a,b⁆
      · exact convert (OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1.central_left a b ⟨ha,hb,hab⟩ central.1 central.2 L h0 h1 h2)
      by_cases four : IsPGroup 2 ((⊤ : Subgroup A).lowerCentralSeries 3)
      · have core (N : Subgroup A) (_ : N.Normal) (two : IsPGroup 2 N) : N=⊥ := by
          by_contra nontrivial
          obtain ⟨x,hx,hne⟩ := SetLike.exists_of_lt (bot_lt_iff_ne_bot.mpr nontrivial)
          have dx : 2 ∣ orderOf x := by
            simpa only [Subgroup.orderOf_mk] using
              two.dvd_orderOf (g:=(⟨x,hx⟩ : N)) (fun h => hne (congrArg Subtype.val h))
          exact Nat.not_even_iff_odd.mpr odd (even_iff_two_dvd.mpr (dx.trans (orderOf_dvd_natCard x)))
        exact convert ⟨5,by decide,OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1.low_class_left a b central core four L h0 h1 h2⟩
      by_contra bad
      have avoid (N : Subgroup A) (normal : N.Normal) (idx : N.index=3) : a*b ∉ N := by
        intro ab
        have proper : N ≠ ⊤ := by intro h; simp [h] at idx
        by_cases am : a ∈ N
        · exact bad (inside N proper am (by simpa using N.mul_mem (N.inv_mem am) ab))
        let f := QuotientGroup.mk' N
        have fa : f a ≠ 1 := fun e => am ((QuotientGroup.eq_one_iff a).mp e)
        have fb : f b = (f a)⁻¹ := eq_inv_of_mul_eq_one_right
          ((map_mul f a b).symm.trans ((QuotientGroup.eq_one_iff _).mpr ab))
        have card : Nat.card (A ⧸ N) = 3 := N.index_eq_card.symm.trans idx
        have order : (f a)^3=1 := card ▸ (pow_card_eq_one' (x:=f a))
        have properKer : f.ker ≠ ⊤ := by rwa [QuotientGroup.ker_mk']
        exact bad (compress f a b fa order fb (smaller f.ker properKer))
      by_cases nil : Group.IsNilpotent A
      · exact bad (convert (nilCase A a b generated ha hb hab central four odd nil
          (large_prime (a*b) odd four avoid) avoid))
      · exact bad (convert (otherCase A a b generated ha hb hab central four odd nil avoid))
  intro A _ _ a b _ ha hb hab _ _ odd
  obtain ⟨k,hk,cyc⟩ := solve _ A a b rfl odd ha hb hab
  exact ⟨k,hk,cyc.trans (flip a b).some.isContained⟩

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H1_R1_H1_R1
