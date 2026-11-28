import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R2
import Mathlib

/-!
# Dyadic cycles by descent through finite 3-groups

A finite group of odd order that embeds in P × K, with P of order 3^n
and K of nilpotency class at most two, satisfies the three-matching case
of Erdős 64. The pure 3-group case takes K trivial.

The subdivision, order-three compression and maximal-subgroup arguments
are adapted from @mejiasd3v's PR 7326. Here the induction is on the order
of P, retains the auxiliary class-two factor throughout, and bounds the
cycle exponent. The local commutation results come from PRs 5246 and 7828.
The other branch uses PR 16895's two-coset construction to eliminate all
normal subgroups of index three and class at most two.
-/

namespace OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R2_H1_R1

open SimpleGraph
open scoped commutatorElement

/-- Nilpotent groups with a prime at least five in the third lower central subgroup. -/
def H1 : Prop :=
  ∀ (A : Type) [Group A] [Fintype A] (a b : A),
    Subgroup.closure ({a,b} : Set A) = ⊤ → a ≠ 1 → b ≠ 1 → a ≠ b → Odd (Nat.card A) →
    (∀ N : Subgroup A, N.Normal → IsMulCommutative N → N.index ≠ 11) →
    (∃ x y : commutator A, x * y ≠ y * x) →
    (∀ N : Subgroup A, N.Normal → N ≠ ⊤ →
      (∀ u ∈ N, ∀ v ∈ N, ∀ w ∈ N, Commute ⁅u,v⁆ w) → a ∉ N ∧ b ∉ N ∧ a⁻¹*b ∉ N) →
    (∀ N : Subgroup A, N.Normal →
      (∀ u ∈ N, ∀ v ∈ N, ∀ w ∈ N, Commute ⁅u,v⁆ w) → N.index ≠ 3) →
    Group.IsNilpotent A →
    (∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ Nat.card ((⊤ : Subgroup A).lowerCentralSeries 2)) →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ (SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2)))

/-- Nonnilpotent groups without a normal subgroup of index three and class at most two. -/
def H2 : Prop :=
  ∀ (A : Type) [Group A] [Fintype A] (a b : A),
    Subgroup.closure ({a,b} : Set A) = ⊤ → a ≠ 1 → b ≠ 1 → a ≠ b → Odd (Nat.card A) →
    (∀ N : Subgroup A, N.Normal → IsMulCommutative N → N.index ≠ 11) →
    (∃ x y : commutator A, x * y ≠ y * x) →
    (∀ N : Subgroup A, N.Normal → N ≠ ⊤ →
      (∀ u ∈ N, ∀ v ∈ N, ∀ w ∈ N, Commute ⁅u,v⁆ w) → a ∉ N ∧ b ∉ N ∧ a⁻¹*b ∉ N) →
    (∀ N : Subgroup A, N.Normal →
      (∀ u ∈ N, ∀ v ∈ N, ∀ w ∈ N, Commute ⁅u,v⁆ w) → N.index ≠ 3) →
    ¬ Group.IsNilpotent A →
    ∃ k : ℕ, 2 ≤ k ∧ cycleGraph (2^k) ⊑ (SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2)))

open OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2 (adj_mod cycle_from_period)

/-- Lift each edge of an embedded cycle through its own intermediate vertex. -/
private theorem subdivided_cycle {X E A : Type*} (B : SimpleGraph X) (G : SimpleGraph (Bool × A))
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


private theorem square {A : Type*} (G : SimpleGraph (Bool × A)) (x y v w : A) (xy : x≠y) (vw : v≠w)
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

/-- A short cycle for two right shifts when one commutes with its conjugate. -/
private theorem short_right {K : Type*} [Group K] [Finite K]
    (odd : Odd (Nat.card K)) (d e : K) (sep : d ≠ 1 ∧ e ≠ 1 ∧ d ≠ e)
    (localComm : Commute d (e*d*e⁻¹)) (B : SimpleGraph (Bool × K))
    (idEdge : ∀ x, B.Adj (false,x) (true,x))
    (dEdge : ∀ x, B.Adj (false,x) (true,x*d))
    (eEdge : ∀ x, B.Adj (false,x) (true,x*e)) :
    cycleGraph 4 ⊑ B ∨ cycleGraph 8 ⊑ B ∨ cycleGraph 16 ⊑ B := by
  by_cases comm : Commute d e
  · let p := Equiv.mulRight d
    let q := Equiv.mulRight e
    have separate (x : K) : p x ≠ x ∧ q x ≠ x ∧ p x ≠ q x := by simpa [p,q] using sep
    have squareAt (x : K) : p (q x) = q (p x) := by
      change x*e*d = x*d*e
      rw [mul_assoc,comm.symm.eq,← mul_assoc]
    exact OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.LocalCommutation.near0
      B p q separate idEdge dEdge eEdge 1 (squareAt _) (squareAt _) (squareAt _) (squareAt _)
  exact .inr (HaarOddRectangle.regular_right odd d e comm localComm B idEdge dEdge eEdge)


/-- Colliding routes make a square. Otherwise lifting a cycle costs one in its exponent. -/
private theorem compress {A Q : Type*} [Group A] [Group Q]
    (f : A →* Q) (a b : A) (nonid : f a ≠ 1) (three : (f a)^3 = 1) (inv : f b = (f a)⁻¹)
    (budget : ℕ) (enough : 2 ≤ budget)
    (recurse : ∀ d e : f.ker, (d ≠ 1 ∧ e ≠ 1 ∧ d ≠ e) → ∀ R : SimpleGraph (Bool × f.ker),
      (∀ x,R.Adj (false,x) (true,x)) → (∀ x,R.Adj (false,x) (true,x*d)) →
      (∀ x,R.Adj (false,x) (true,x*e)) →
      ∃ k : ℕ, 2 ≤ k ∧ k ≤ budget ∧ cycleGraph (2^k) ⊑ R) :
    ∀ R : SimpleGraph (Bool × A),
      (∀ x,R.Adj (false,x) (true,x)) → (∀ x,R.Adj (false,x) (true,x*a)) →
      (∀ x,R.Adj (false,x) (true,x*b)) →
      ∃ k : ℕ, 2 ≤ k ∧ k ≤ budget+1 ∧ cycleGraph (2^k) ⊑ R := by
  intro G h0 ha hb
  classical
  -- Route i from x to (x * D i) * a through x * S i.
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
    fin_cases i <;> fin_cases j <;> first
      | rfl
      | solve | simp [S,inv,nonid,nonid.symm,distinct,distinct.symm] at eq
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
  -- Distinct route types use distinct quotient cosets for their middle vertices.
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
    fin_cases i
    · exact ha x
    · simpa [S] using h0 x
    · exact hb x
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
    let B := SimpleGraph.fromRel (fun u v : Bool × f.ker =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=u.2*d ∨ v.2=u.2*e))
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
    have edge (x y : f.ker) (h : y=x ∨ y=x*d ∨ y=x*e) : B.Adj (false,x) (true,y) :=
      ⟨by simp,.inl ⟨rfl,rfl,h⟩⟩
    obtain ⟨k,hk,upper,cyc⟩ := recurse d e sep B (fun x => edge x x (.inl rfl))
      (fun x => edge x _ (.inr (.inl rfl))) (fun x => edge x _ (.inr (.inr rfl)))
    have size : 3 ≤ 2^k := by have := Nat.pow_le_pow_right (by decide : 0 < 2) hk; omega
    refine ⟨k+1,by omega,by omega,?_⟩
    rw [pow_succ,Nat.mul_comm]
    exact subdivided_cycle B G v m l r covers hl hr size cyc
  · -- Coincident compressed shifts give two different routes with the same ends.
    rw [Function.Injective] at di
    push Not at di
    obtain ⟨i,j,eq,ne⟩ := di
    let x : f.ker × Fin 3 := (1,i)
    let y : f.ker × Fin 3 := (1,j)
    have rr : r x=r y := by simp [r,x,y,eq]
    have vl : v (l x)≠v (r x) := fun h => Bool.false_ne_true (congrArg Prod.fst (v.injective h))
    have mm : m x≠m y := fun h => ne (congrArg Prod.snd (m.injective h))
    exact ⟨2,by decide,by omega,square G _ _ _ _ vl mm (hl x) (hl y) (hr x) (rr ▸ hr y)⟩

private theorem maximal_card {A : Type*} [Group A] [Finite A] (pgrp : IsPGroup 3 A)
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

private theorem small_commute {P : Type*} [Group P] [Finite P] {n : ℕ}
    (size : Nat.card P = 3^n) (small : n ≤ 2) (a b : P) : Commute a b := by
  interval_cases n
  · have sub : Subsingleton P := (Nat.card_eq_one_iff_unique.mp (by simpa using size)).1
    exact Subsingleton.elim _ _
  · let := isCyclic_of_card_dvd_prime (p := 3) (by simpa using size.dvd)
    exact (IsCyclic.commGroup (α := P)).mul_comm a b
  · let := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) size
    exact mul_comm' a b

/-- Factoring out the nontrivial center leaves a group of order at most nine. -/
private theorem small_central {P : Type*} [Group P] [Finite P] {n : ℕ}
    (size : Nat.card P = 3^n) (small : n ≤ 3) (a b z : P) : Commute ⁅a,b⁆ z := by
  by_cases trivial : n = 0
  · exact small_commute size (by omega) _ _
  obtain ⟨c,hc,centerSize⟩ := IsPGroup.card_center_eq_prime_pow size (by omega)
  let Z := Subgroup.center P
  let f := QuotientGroup.mk' Z
  obtain ⟨q,quotSize⟩ := IsPGroup.iff_card.mp ((IsPGroup.of_card size).to_quotient Z)
  have sum : c+q=n := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 3)
    change 3^(c+q) = 3^n
    rw [pow_add, ← centerSize, ← quotSize, ← Z.index_eq_card, Z.card_mul_index,size]
  have pair := small_commute quotSize (by omega) (f a) (f b)
  have mem : ⁅a,b⁆ ∈ Z := (QuotientGroup.eq_one_iff _).mp (show f ⁅a,b⁆ = 1 by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]; exact pair)
  exact (Subgroup.mem_center_iff.mp mem z).symm

private theorem central_projections {P A K : Type*} [Group P] [Group A] [Finite A] [Group K]
    (n : ℕ) (odd : Odd (Nat.card A)) (π : A →* P) (ρ : A →* K)
    (joint : ∀ {x y : A}, π x = π y → ρ x = ρ y → x=y)
    (classTwo : ∀ x y z : K, Commute ⁅x,y⁆ z)
    (a b : A) (sep : a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b) (pc : Commute ⁅π b,π a⁆ (π a)) :
    ∀ R : SimpleGraph (Bool × A),
      (∀ x,R.Adj (false,x) (true,x)) → (∀ x,R.Adj (false,x) (true,x*a)) →
      (∀ x,R.Adj (false,x) (true,x*b)) →
      ∃ k : ℕ, 2 ≤ k ∧ k ≤ max 4 (n+1) ∧ cycleGraph (2^k) ⊑ R := by
  intro G h0 ha hb
  have central : Commute ⁅b,a⁆ a := by
    apply joint
    · simpa only [map_mul,map_commutatorElement] using pc.eq
    · simpa only [map_mul,map_commutatorElement] using (classTwo (ρ b) (ρ a) (ρ a)).eq
  have rewriteConj : b*a*b⁻¹ = ⁅b,a⁆*a := by simp [commutatorElement_def,mul_assoc]
  have lc : Commute a (b*a*b⁻¹) := rewriteConj ▸ central.symm.mul_right (.refl _)
  rcases short_right odd a b sep lc G h0 ha hb with h | h | h
  · exact ⟨2,by decide,by omega,h⟩
  · exact ⟨3,by decide,by omega,h⟩
  · exact ⟨4,by decide,by omega,h⟩

private theorem descend (n : ℕ) {P A K : Type*} [Group P] [Finite P] [Group A] [Finite A] [Group K]
    (size : Nat.card P = 3^n) (odd : Odd (Nat.card A)) (π : A →* P) (ρ : A →* K)
    (joint : ∀ {x y : A}, π x = π y → ρ x = ρ y → x=y)
    (classTwo : ∀ x y z : K, Commute ⁅x,y⁆ z)
    (a b : A) (sep : a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b) : ∀ R : SimpleGraph (Bool × A),
      (∀ x,R.Adj (false,x) (true,x)) → (∀ x,R.Adj (false,x) (true,x*a)) →
      (∀ x,R.Adj (false,x) (true,x*b)) →
      ∃ k : ℕ, 2 ≤ k ∧ k ≤ max 4 (n+1) ∧ cycleGraph (2^k) ⊑ R := by
  induction n generalizing P A with
  | zero =>
    exact central_projections 0 odd π ρ joint classTwo a b sep (small_central size (by decide) _ _ _)
  | succ n ih =>
    by_cases pc : Commute ⁅π b,π a⁆ (π a)
    · exact central_projections (n+1) odd π ρ joint classTwo a b sep pc
    have large : 3 ≤ n := by
      by_contra! small
      exact pc (small_central size (by omega) _ _ _)
    have stepBudget : max 4 (n+1+1) = max 4 (n+1) + 1 := by omega
    have pgrp : IsPGroup 3 P := IsPGroup.of_card size
    have proper : Subgroup.zpowers (π (a*b)) ≠ ⊤ := by
      intro top
      let : IsCyclic P := ⟨π (a*b),fun x => Subgroup.mem_zpowers_iff.mp
        (show x ∈ Subgroup.zpowers (π (a*b)) from top ▸ Subgroup.mem_top x)⟩
      exact pc ((IsCyclic.commGroup (α := P)).mul_comm _ _)
    obtain ⟨M,maximal,contain⟩ := (eq_top_or_exists_le_coatom _).resolve_left proper
    let : M.Normal := ((Group.isNilpotent_of_finite_tfae (G:=P)).out 0 2 rfl rfl).mp pgrp.isNilpotent M maximal
    have three := maximal_card pgrp M maximal
    have idx : M.index = 3 := three
    have smaller : Nat.card M = 3^n := by
      have eq := M.card_mul_index
      rw [idx,size,pow_succ] at eq
      omega
    let f := (QuotientGroup.mk' M).comp π
    have mem (x : f.ker) : π (x:A) ∈ M := (QuotientGroup.eq_one_iff _).mp x.property
    let π' : f.ker →* M := (π.comp f.ker.subtype).codRestrict M mem
    have subOdd := odd.of_dvd_nat f.ker.card_subgroup_dvd_card
    have run (d e : f.ker) (s : d ≠ 1 ∧ e ≠ 1 ∧ d ≠ e) : ∀ R : SimpleGraph (Bool × f.ker),
        (∀ x,R.Adj (false,x) (true,x)) → (∀ x,R.Adj (false,x) (true,x*d)) →
        (∀ x,R.Adj (false,x) (true,x*e)) →
        ∃ k : ℕ, 2 ≤ k ∧ k ≤ max 4 (n+1) ∧ cycleGraph (2^k) ⊑ R :=
      ih smaller subOdd π' (ρ.comp f.ker.subtype)
        (fun hp hk => Subtype.ext (joint (congrArg Subtype.val hp) hk)) d e s
    have inv : f b = (f a)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      rw [←map_mul]
      exact (QuotientGroup.eq_one_iff _).mpr (contain (Subgroup.mem_zpowers _))
    by_cases fa : f a = 1
    · have fb : f b = 1 := by simp [inv,fa]
      let d : f.ker := ⟨a,fa⟩
      let e : f.ker := ⟨b,fb⟩
      have separate : d ≠ 1 ∧ e ≠ 1 ∧ d ≠ e :=
        ⟨fun h => sep.1 (congrArg Subtype.val h),fun h => sep.2.1 (congrArg Subtype.val h),
          fun h => sep.2.2 (congrArg Subtype.val h)⟩
      intro G h0 ha hb
      let embed : (Bool × f.ker) ↪ (Bool × A) :=
        (Function.Embedding.refl Bool).prodMap ⟨Subtype.val,Subtype.coe_injective⟩
      obtain ⟨k,low,high,cyc⟩ := run d e separate (G.comap embed)
        (fun x => h0 x) (fun x => ha x) (fun x => hb x)
      exact ⟨k,low,by rw [stepBudget]; omega,cyc.trans ⟨(SimpleGraph.Embedding.comap embed G).toCopy⟩⟩
    · rw [stepBudget]
      exact compress f a b fa (three ▸ pow_card_eq_one') inv (max 4 (n+1))
        (by omega) run

/-- The maps to P and K identify A with a subgroup of their product. Only P
enters the bound on the cycle length. The graph may contain additional edges. -/
theorem class_two_factor {P A K : Type*} [Group P] [Finite P] [Group A] [Finite A] [Group K]
    (n : ℕ) (size : Nat.card P = 3^n) (odd : Odd (Nat.card A)) (π : A →* P) (ρ : A →* K)
    (joint : ∀ {x y : A}, π x = π y → ρ x = ρ y → x=y)
    (classTwo : ∀ x y z : K, Commute ⁅x,y⁆ z)
    (a b : A) (sep : a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b)
    (G : SimpleGraph (Bool × A)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,a*x)) (hb : ∀ x,G.Adj (false,x) (true,b*x)) :
    ∃ k : ℕ, 2 ≤ k ∧ k ≤ max 4 (n+1) ∧ cycleGraph (2^k) ⊑ G := by
  let flip : (Bool × A) ↪ (Bool × A) := {
    toFun x := (!x.1,x.2⁻¹)
    inj' := by
      rintro ⟨i,x⟩ ⟨j,y⟩ h
      exact Prod.ext (by simpa using congrArg Prod.fst h) (inv_injective (congrArg Prod.snd h)) }
  have reverseEdge (u : A) (edge : ∀ x,G.Adj (false,x) (true,u*x)) (x : A) :
      (G.comap flip).Adj (false,x) (true,x*u) := by
    change G.Adj (true,x⁻¹) (false,(x*u)⁻¹)
    simpa [mul_assoc] using (edge ((x*u)⁻¹)).symm
  obtain ⟨k,low,upper,cyc⟩ := descend n size odd π ρ joint classTwo a b sep (G.comap flip)
    (fun x => (h0 x⁻¹).symm) (reverseEdge a ha) (reverseEdge b hb)
  exact ⟨k,low,upper,cyc.trans ⟨(SimpleGraph.Embedding.comap flip G).toCopy⟩⟩

/-- Every three-matching graph of a group of order 3^n contains a simple
cycle of length 2^k with 2 ≤ k ≤ max 4 (n+1). -/
theorem three_group {A : Type*} [Group A] [Finite A] (n : ℕ) (size : Nat.card A = 3^n)
    (a b : A) (sep : a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b)
    (G : SimpleGraph (Bool × A)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,a*x)) (hb : ∀ x,G.Adj (false,x) (true,b*x)) :
    ∃ k : ℕ, 2 ≤ k ∧ k ≤ max 4 (n+1) ∧ cycleGraph (2^k) ⊑ G :=
  class_two_factor n size (size ▸ (show Odd 3 by decide).pow) (MonoidHom.id A) (1 : A →* Unit)
    (fun h _ => h) (fun _ _ _ => Subsingleton.elim _ _) a b sep G h0 ha hb

private theorem sylow_three_projection {A : Type*} [Group A] [Finite A] [Group.IsNilpotent A]
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

/-- For an odd-order nilpotent group it suffices that its third lower central
subgroup γ₃(A) be a 3-group. The exponent bound uses only the Sylow 3-subgroup. -/
theorem nilpotent_third_term {A : Type*} [Group A] [Finite A] [Group.IsNilpotent A]
    (odd : Odd (Nat.card A)) (third : IsPGroup 3 ((⊤ : Subgroup A).lowerCentralSeries 2))
    (P : Sylow 3 A) (n : ℕ) (size : Nat.card P = 3^n)
    (a b : A) (sep : a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b)
    (G : SimpleGraph (Bool × A)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,a*x)) (hb : ∀ x,G.Adj (false,x) (true,b*x)) :
    ∃ k : ℕ, 2 ≤ k ∧ k ≤ max 4 (n+1) ∧ cycleGraph (2^k) ⊑ G := by
  classical
  obtain ⟨π,hπ⟩ : ∃ π : A →* P, ¬ 3 ∣ Nat.card π.ker := by
    by_cases dv : 3 ∣ Nat.card A
    · obtain ⟨f,_,hf⟩ := sylow_three_projection dv P
      exact ⟨f,hf⟩
    · exact ⟨1,fun h => dv (h.trans (1 : A →* P).ker.card_subgroup_dvd_card)⟩
  let D := (⊤ : Subgroup A).lowerCentralSeries 2
  let ρ := QuotientGroup.mk' D
  have classTwo (x y z : A ⧸ D) : Commute ⁅x,y⁆ z := by
    obtain ⟨u,rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨v,rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨w,rfl⟩ := QuotientGroup.mk_surjective z
    apply commutatorElement_eq_one_iff_commute.mp
    change ⁅⁅ρ u,ρ v⁆,ρ w⁆ = 1
    rw [←map_commutatorElement, ←map_commutatorElement]
    apply (QuotientGroup.eq_one_iff _).mpr
    exact Subgroup.commutator_mem_commutator
      (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)) (Subgroup.mem_top _)
  have joint {x y : A} (hp : π x = π y) (hq : ρ x = ρ y) : x=y := by
    by_contra ne
    let w := x⁻¹*y
    have wd : w ∈ D := (QuotientGroup.eq_one_iff _).mp (show ρ w = 1 by simp [w,hq])
    have wk : w ∈ π.ker := show π w = 1 by simp [w,hp]
    have nonid : (⟨w,wd⟩ : D) ≠ 1 := fun h => ne (inv_mul_eq_one.mp (congrArg Subtype.val h))
    have div : 3 ∣ orderOf w := by
      simpa only [Subgroup.orderOf_mk] using third.dvd_orderOf (g := (⟨w,wd⟩ : D)) nonid
    exact hπ (div.trans (π.ker.orderOf_dvd_natCard wk))
  exact class_two_factor n size odd π ρ joint classTwo a b sep G h0 ha hb

private theorem inverse_of_card_three {Q : Type*} [Group Q] [Finite Q] (card : Nat.card Q = 3)
    (x y : Q) (hx : x ≠ 1) (hy : y ≠ 1) (hne : x ≠ y) : y = x⁻¹ := by
  classical
  let := Fintype.ofFinite Q
  have cube : x^3 = 1 := card ▸ pow_card_eq_one' (x := x)
  have diff : x ≠ x⁻¹ := by
    intro eq
    have sq : x*x=1 := by simpa only [mul_inv_cancel] using congrArg (fun u => x*u) eq
    exact hx (by simpa [pow_succ,sq] using cube)
  by_contra missing
  have four := Finset.card_le_univ ({y,x,x⁻¹,1} : Finset Q)
  simp [Finset.card_insert_of_notMem, missing, hne.symm, diff, hx, hy,
    ← Nat.card_eq_fintype_card, card] at four

private theorem transport_short {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (embed : G ⊑ H) (small : (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨
      cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G)) : (cycleGraph 4 ⊑ H ∨ cycleGraph 8 ⊑ H ∨
      cycleGraph 16 ⊑ H ∨ cycleGraph 32 ⊑ H) := by
  rcases small with h | h | h | h
  · exact .inl (h.trans embed)
  · exact .inr (.inl (h.trans embed))
  · exact .inr (.inr (.inl (h.trans embed)))
  · exact .inr (.inr (.inr (h.trans embed)))

/-- Swap the two parts and invert the group coordinate to turn right shifts into left shifts. -/
private theorem right_to_left {A : Type*} [Group A] (a b : A)
    (right : ∀ R : SimpleGraph (Bool × A), (∀ x,R.Adj (false,x) (true,x)) →
      (∀ x,R.Adj (false,x) (true,x*a)) → (∀ x,R.Adj (false,x) (true,x*b)) → (cycleGraph 4 ⊑ R ∨ cycleGraph 8 ⊑ R ∨
      cycleGraph 16 ⊑ R ∨ cycleGraph 32 ⊑ R))
    (G : SimpleGraph (Bool × A)) (idEdge : ∀ x,G.Adj (false,x) (true,x))
    (aEdge : ∀ x,G.Adj (false,x) (true,a*x)) (bEdge : ∀ x,G.Adj (false,x) (true,b*x)) :
    (cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨
      cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G) := by
  let flip : (Bool × A) ↪ (Bool × A) := {
    toFun x := (!x.1,x.2⁻¹)
    inj' := by
      rintro ⟨i,x⟩ ⟨j,y⟩ h
      exact Prod.ext (by simpa using congrArg Prod.fst h) (inv_injective (congrArg Prod.snd h)) }
  have reverseEdge (u : A) (edge : ∀ x,G.Adj (false,x) (true,u*x)) (x : A) :
      (G.comap flip).Adj (false,x) (true,x*u) := by
    change G.Adj (true,x⁻¹) (false,(x*u)⁻¹)
    simpa [mul_assoc] using (edge ((x*u)⁻¹)).symm
  exact transport_short ⟨(SimpleGraph.Embedding.comap flip G).toCopy⟩
    (right (G.comap flip) (fun x => (idEdge x⁻¹).symm) (reverseEdge a aEdge) (reverseEdge b bEdge))

/-- A class-two normal subgroup of index three with three distinct shift cosets
forces a simple cycle of length 4, 8, 16 or 32. Extra edges in G are allowed. -/
theorem distinct_cosets_short {A : Type*} [Group A] [Finite A] (odd : Odd (Nat.card A))
    (N : Subgroup A) [N.Normal] (indexThree : N.index=3)
    (classTwo : ∀ u ∈ N, ∀ v ∈ N, ∀ w ∈ N, Commute ⁅u,v⁆ w)
    (a b : A) (an : a ∉ N) (bn : b ∉ N) (abn : a⁻¹*b ∉ N)
    (G : SimpleGraph (Bool × A)) (idEdge : ∀ x,G.Adj (false,x) (true,x))
    (aEdge : ∀ x,G.Adj (false,x) (true,a*x)) (bEdge : ∀ x,G.Adj (false,x) (true,b*x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  let f := QuotientGroup.mk' N
  have card : Nat.card (A ⧸ N) = 3 := indexThree
  have fa : f a ≠ 1 := fun h => an ((QuotientGroup.eq_one_iff a).mp h)
  have fb : f b ≠ 1 := fun h => bn ((QuotientGroup.eq_one_iff b).mp h)
  have distinct : f a ≠ f b := by
    intro eq
    exact abn ((QuotientGroup.eq_one_iff _).mp (show f (a⁻¹*b) = 1 by simp [eq]))
  have inv := inverse_of_card_three card (f a) (f b) fa fb distinct
  have central (x y z : f.ker) : Commute ⁅x,y⁆ z := by
    apply (Subtype.coe_injective : Function.Injective (fun t : f.ker => (t:A)))
    have inside (u : f.ker) : (u:A) ∈ N := (QuotientGroup.eq_one_iff _).mp u.property
    exact (classTwo _ (inside x) _ (inside y) _ (inside z)).eq
  apply right_to_left a b _ G idEdge aEdge bEdge
  intro R h0 ha hb
  have recurse (d e : f.ker) (sep : d ≠ 1 ∧ e ≠ 1 ∧ d ≠ e) (B : SimpleGraph (Bool × f.ker))
      (z : ∀ x,B.Adj (false,x) (true,x)) (s : ∀ x,B.Adj (false,x) (true,x*d))
      (t : ∀ x,B.Adj (false,x) (true,x*e)) : ∃ k : ℕ, 2 ≤ k ∧ k ≤ 4 ∧ cycleGraph (2^k) ⊑ B := by
    have conjugate : e*d*e⁻¹ = ⁅e,d⁆*d := by simp [commutatorElement_def,mul_assoc]
    have lc : Commute d (e*d*e⁻¹) := conjugate ▸ (central e d d).symm.mul_right (.refl d)
    rcases short_right (odd.of_dvd_nat f.ker.card_subgroup_dvd_card) d e sep lc B z s t with h | h | h
    · exact ⟨2,by decide,by decide,h⟩
    · exact ⟨3,by decide,by decide,h⟩
    · exact ⟨4,by decide,by decide,h⟩
  obtain ⟨k,hk,upper,h⟩ := compress f a b fa (card ▸ pow_card_eq_one') inv 4 (by decide)
    recurse R h0 ha hb
  interval_cases k
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr (.inl h))
  · exact .inr (.inr (.inr h))

open OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R2
  (change_labels odd_classTwo_noncommuting)

/-- For every triple of distinct matching shifts in an odd-order group with a
class-two normal subgroup of index three, some simple cycle has dyadic length at most 32. -/
theorem index_three_short {A : Type*} [Group A] [Finite A] (odd : Odd (Nat.card A))
    (N : Subgroup A) [N.Normal] (indexThree : N.index=3)
    (classTwo : ∀ u ∈ N, ∀ v ∈ N, ∀ w ∈ N, Commute ⁅u,v⁆ w)
    (a b : A) (ha : a ≠ 1) (hb : b ≠ 1) (hab : a ≠ b) :
    let G := SimpleGraph.fromRel (fun u v : Bool × A =>
      u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  let graph (s t : A) := SimpleGraph.fromRel (fun u v : Bool × A =>
    u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=s*u.2 ∨ v.2=t*u.2))
  change (cycleGraph 4 ⊑ (graph a b) ∨ cycleGraph 8 ⊑ (graph a b) ∨
      cycleGraph 16 ⊑ (graph a b) ∨ cycleGraph 32 ⊑ (graph a b))
  have edge (s t x y : A) (label : y=x ∨ y=s*x ∨ y=t*x) :
      (graph s t).Adj (false,x) (true,y) := ⟨by simp,.inl ⟨rfl,rfl,label⟩⟩
  have repeated (s t : A) (sep : s ≠ 1 ∧ t ≠ 1 ∧ s ≠ t) (hs : s ∈ N) :
      (cycleGraph 4 ⊑ (graph s t) ∨ cycleGraph 8 ⊑ (graph s t) ∨
      cycleGraph 16 ⊑ (graph s t) ∨ cycleGraph 32 ⊑ (graph s t)) := by
    by_cases comm : Commute (t⁻¹*s*t) s
    · apply right_to_left s t _ (graph s t)
        (fun x => edge s t x x (.inl rfl)) (fun x => edge s t x _ (.inr (.inl rfl)))
        (fun x => edge s t x _ (.inr (.inr rfl)))
      intro R h0 h1 h2
      have conjugate := comm.map (MulAut.conj t).toMonoidHom
      have localComm : Commute s (t*s*t⁻¹) := by simpa [MulAut.conj_apply,mul_assoc] using conjugate
      rcases short_right odd s t sep localComm R h0 h1 h2 with h | h | h
      · exact .inl h
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
    · have outside : t ∉ N := by
        intro ht
        apply comm
        have rewriteConjugate : t⁻¹*s*t = ⁅t⁻¹,s⁆*s := by simp [commutatorElement_def,mul_assoc]
        exact rewriteConjugate ▸ (classTwo _ (N.inv_mem ht) _ hs _ hs).mul_left (.refl s)
      exact .inr (.inr (.inr (odd_classTwo_noncommuting odd N classTwo s t hs outside comm)))
  by_cases an : a ∈ N
  · exact repeated a b ⟨ha,hb,hab⟩ an
  by_cases bn : b ∈ N
  · exact transport_short (change_labels a b 1 b a (by
      intro d hd; rcases hd with rfl | rfl | rfl <;> simp)) (repeated b a ⟨hb,ha,hab.symm⟩ bn)
  by_cases same : a⁻¹*b ∈ N
  · have sep : a⁻¹*b ≠ 1 ∧ a⁻¹ ≠ 1 ∧ a⁻¹*b ≠ a⁻¹ := by simp [inv_mul_eq_one, hab, hb, ha]
    exact transport_short (change_labels a b a (a⁻¹*b) a⁻¹ (by
      intro d hd; rcases hd with rfl | rfl | rfl <;> simp [← mul_assoc]))
      (repeated _ _ sep same)
  exact distinct_cosets_short odd N indexThree classTwo a b an bn same (graph a b)
    (fun x => edge a b x x (.inl rfl)) (fun x => edge a b x _ (.inr (.inl rfl)))
    (fun x => edge a b x _ (.inr (.inr rfl)))

/-- An odd-order group of order divisible by no prime above three is a 3-group. -/
private theorem large_prime_of_not_three {A : Type*} [Group A] [Finite A]
    (odd : Odd (Nat.card A)) (notThree : ¬ IsPGroup 3 A) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ p ∣ Nat.card A := by
  by_contra missing
  apply notThree
  apply (isPGroup_iff_primeFactors_card_subset (by decide : 3 ≠ 0)).mpr
  intro p hp
  have prime := Nat.prime_of_mem_primeFactors hp
  have divides := Nat.dvd_of_mem_primeFactors hp
  have low := prime.two_le
  have upper : p < 5 := by by_contra! h; exact missing ⟨p,prime,h,divides⟩
  have notTwo : p ≠ 2 := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr odd (even_iff_two_dvd.mpr divides)
  have notFour : p ≠ 4 := by rintro rfl; norm_num at prime
  have eq : p=3 := by omega
  simpa using eq

theorem main : H1 → H2 → OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R2.H1 := by
  intro nilCase otherCase A _ _ a b generated ha hb hab odd eleven derived separated
  by_cases none : ∀ N : Subgroup A, N.Normal →
      (∀ u ∈ N, ∀ v ∈ N, ∀ w ∈ N, Commute ⁅u,v⁆ w) → N.index ≠ 3
  · by_cases nil : Group.IsNilpotent A
    · let _ : Group.IsNilpotent A := nil
      let D := (⊤ : Subgroup A).lowerCentralSeries 2
      by_cases three : IsPGroup 3 D
      · let P : Sylow 3 A := default
        obtain ⟨n,size⟩ := IsPGroup.iff_card.mp P.isPGroup'
        let G := SimpleGraph.fromRel (fun u v : Bool × A =>
          u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=a*u.2 ∨ v.2=b*u.2))
        have edge (x y : A) (label : y=x ∨ y=a*x ∨ y=b*x) :
            G.Adj (false,x) (true,y) := ⟨by simp,.inl ⟨rfl,rfl,label⟩⟩
        obtain ⟨k,hk,_,cyc⟩ := nilpotent_third_term odd three P n size a b ⟨ha,hb,hab⟩ G
          (fun x => edge x x (.inl rfl)) (fun x => edge x _ (.inr (.inl rfl)))
          (fun x => edge x _ (.inr (.inr rfl)))
        exact ⟨k,hk,cyc⟩
      · exact nilCase A a b generated ha hb hab odd eleven derived separated none nil
          (large_prime_of_not_three (odd.of_dvd_nat D.card_subgroup_dvd_card) three)
    · exact otherCase A a b generated ha hb hab odd eleven derived separated none nil
  · push Not at none
    obtain ⟨N,normal,classTwo,indexThree⟩ := none
    let _ : N.Normal := normal
    rcases index_three_short odd N indexThree classTwo a b ha hb hab with h | h | h | h
    · exact ⟨2,by decide,h⟩
    · exact ⟨3,by decide,h⟩
    · exact ⟨4,by decide,h⟩
    · exact ⟨5,by decide,h⟩

end OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R2_H1_R1_H2_R1_H2_R2_H1_R1
