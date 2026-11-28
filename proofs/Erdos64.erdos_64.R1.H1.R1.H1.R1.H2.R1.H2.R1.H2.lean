import OMAReductions.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H2_R1
import Mathlib

/-!
# Power-of-two cycles for an abelian normal subgroup of index eleven

The matching formulation of Erdős and Gyárfás's question uses earlier reductions by
JamesSlash (PR 592) and the authors of PRs 5246 and 5820. PRs 7828 and 8157
treat regular actions and stabilizers contained in the abelian subgroup, respectively.
On each remaining orbit the subgroup acts transitively, giving two affine matchings
on a finite abelian group. Their linear parts lie in one cyclic group of order eleven.
The proof splits according to the order of the image of the generator minus the identity.
The resulting simple cycle has length 4, 8, 16 or 32.
-/

section
universe u
namespace NonfreeEleven

/-- For a prime-order quotient, a point stabilizer is either in the kernel or projects onto the quotient. -/
theorem stabilizer_dichotomy {A Q X : Type*} [Group A] [Group Q] [MulAction A X]
    [Fact (Nat.card Q).Prime] (f : A →* Q) (x : X) :
    (∀ g : A, g • x = x → f g = 1) ∨
    (∀ q : Q, ∃ g : A, g • x = x ∧ f g = q) := by
  let H := MulAction.stabilizer A x
  rcases (H.map f).eq_bot_or_eq_top_of_prime_card with h|h
  · left
    intro g hg
    have mem : f g ∈ H.map f := ⟨g,hg,rfl⟩
    rwa [h,Subgroup.mem_bot] at mem
  · right
    intro q
    have mem : q ∈ H.map f := h ▸ Subgroup.mem_top q
    exact mem

/-- A stabilizer projecting onto the quotient makes the kernel transitive on this orbit. -/
theorem orbit_eq_kernel_orbit {A Q X : Type*} [Group A] [Group Q] [MulAction A X]
    (f : A →* Q) (x : X) (covers : ∀ q : Q, ∃ g : A, g • x=x ∧ f g=q) :
    MulAction.orbit A x = MulAction.orbit f.ker x := by
  ext y
  constructor
  · rintro ⟨g,rfl⟩
    obtain ⟨s,hs,hf⟩ := covers (f g)
    let n : f.ker := ⟨g*s⁻¹,by simp [MonoidHom.mem_ker,hf]⟩
    refine ⟨n,?_⟩
    change (g*s⁻¹) • x = g • x
    have hi := inv_smul_smul s x
    rw [hs] at hi
    rw [mul_smul,hi]
  · rintro ⟨n,rfl⟩
    exact ⟨(n:A),rfl⟩

/-- On an orbit with a surjective stabilizer, an abelian kernel is the translation group
in additive coordinates. The linear parts of all group elements factor through the quotient. -/
theorem affine_orbit_coordinates {A : Type u} {Q X : Type*} [Group A] [Group Q] [MulAction A X]
    (f : A →* Q) (comm : ∀ a b : f.ker, a*b=b*a) (x : X)
    (covers : ∀ q : Q, ∃ g : A, g • x=x ∧ f g=q) :
    ∃ (V : Type u) (_ : AddCommGroup V) (e : V ↪ X) (L : Q →* Multiplicative (AddAut V)) (c : A → V),
      Set.range e = MulAction.orbit A x ∧ e 0=x ∧
      (∀ g z, g • e z = e ((L (f g)).toAdd z + c g)) ∧
      (∀ v : V, ∃ n : f.ker, ∀ z, (n:A) • e z=e (v+z)) ∧
      (∀ q : Q, ∃ g : A, f g=q ∧ c g=0) ∧ Nat.card V ∣ Nat.card f.ker := by
  classical
  let _ : CommGroup f.ker := { (inferInstance : Group f.ker) with mul_comm := comm }
  let H := MulAction.stabilizer f.ker x
  let D := f.ker ⧸ H
  let V := Additive D
  let s := fun q => (covers q).choose
  have sx (q : Q) : s q • x=x := (covers q).choose_spec.1
  have sf (q : Q) : f (s q)=q := (covers q).choose_spec.2
  have sxinv (q : Q) : (s q)⁻¹ • x=x := by
    calc (s q)⁻¹ • x = (s q)⁻¹ • (s q • x) := congrArg (fun y => (s q)⁻¹ • y) (sx q).symm
         _ = x := inv_smul_smul _ _
  let C (q : Q) : MulAut f.ker := MulAut.conjNormal (s q)
  have stable (q : Q) : H.map (C q).toMonoidHom = H := by
    ext a
    constructor
    · rintro ⟨b,hb,rfl⟩
      change ((s q)*(b:A)*(s q)⁻¹) • x=x
      change (b:A) • x=x at hb
      simp only [mul_smul,sxinv,hb,sx]
    · intro ha
      refine ⟨(C q).symm a,?_,(C q).apply_symm_apply a⟩
      change (((MulAut.conjNormal (s q) : MulAut f.ker).symm a : f.ker):A) • x=x
      rw [MulAut.conjNormal_symm_apply]
      change (a:A) • x=x at ha
      simp only [mul_smul,sx,ha,sxinv]
  let K (q : Q) : AddAut V := MulEquiv.toAdditive (QuotientGroup.congr H H (C q) (stable q))
  let n (g : A) : f.ker := ⟨g*(s (f g))⁻¹,by simp [MonoidHom.mem_ker,sf]⟩
  let c (g : A) : V := Additive.ofMul (QuotientGroup.mk' H (n g))
  let e : V ↪ X := ⟨fun v => MulAction.ofQuotientStabilizer f.ker x v.toMul,
    fun _ _ h => congrArg Additive.ofMul (MulAction.injective_ofQuotientStabilizer f.ker x h)⟩
  have act (g : A) (z : V) : g • e z=e (K (f g) z+c g) := by
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective H z.toMul
    obtain rfl : z=Additive.ofMul (QuotientGroup.mk' H a) := congrArg Additive.ofMul ha.symm
    change g • ((a:A) • x) = MulAction.ofQuotientStabilizer f.ker x
      ((QuotientGroup.mk' H (C (f g) a))*(QuotientGroup.mk' H (n g)))
    rw [← map_mul, comm (C (f g) a) (n g)]
    change g • ((a:A) • x) = ((g*(s (f g))⁻¹)*((s (f g))*(a:A)*(s (f g))⁻¹)) • x
    simp only [mul_smul,sxinv,inv_smul_smul]
  have compose (g h : A) (z : V) :
      K (f (g*h)) z + c (g*h) = K (f g) (K (f h) z) + (K (f g) (c h) + c g) := by
    apply e.injective
    rw [← act,mul_smul,act h,act g,(K (f g)).map_add,add_assoc]
  have const (g h : A) : c (g*h) = K (f g) (c h)+c g := by simpa using compose g h 0
  have mult (q r : Q) : K (q*r)=K q+K r := by
    apply AddEquiv.ext
    intro z
    change K (q*r) z = K q (K r z)
    have h := compose (s q) (s r) z
    rw [const,map_mul,sf,sf] at h
    exact add_right_cancel (a := K (q*r) z) h
  let L : Q →* Multiplicative (AddAut V) := MonoidHom.mk' (fun q => Multiplicative.ofAdd (K q)) mult
  have origin : e 0=x := one_smul f.ker x
  refine ⟨V,inferInstance,e,L,c,?_,origin,act,?_,?_,H.card_quotient_dvd_card⟩
  · rw [orbit_eq_kernel_orbit f x covers]
    ext y
    constructor
    · rintro ⟨z,rfl⟩
      exact MulAction.ofQuotientStabilizer_mem_orbit f.ker x z.toMul
    · rintro ⟨a,rfl⟩
      exact ⟨Additive.ofMul (QuotientGroup.mk' H a),rfl⟩
  · intro v
    obtain ⟨a,ha⟩ := QuotientGroup.mk'_surjective H v.toMul
    refine ⟨a,fun z => ?_⟩
    obtain ⟨b,hb⟩ := QuotientGroup.mk'_surjective H z.toMul
    change (a:A) • MulAction.ofQuotientStabilizer f.ker x z.toMul =
      MulAction.ofQuotientStabilizer f.ker x (v.toMul*z.toMul)
    rw [← ha,← hb,← map_mul]
    exact (mul_smul a b x).symm
  · intro q
    refine ⟨s q,sf q,e.injective ?_⟩
    have h := act (s q) 0
    rw [origin,sx,map_zero,zero_add] at h
    exact h.symm.trans origin.symm

/-- The faithful permutation image on the orbit consists of precisely the affine maps with
linear part in the image of the quotient. This identifies the action even if the original
group acts on this orbit with a nontrivial kernel. -/
theorem affine_orbit_permutation_image {A : Type u} {Q X : Type*} [Group A] [Group Q]
    [MulAction A X] (f : A →* Q) (comm : ∀ a b : f.ker, a*b=b*a) (x : X)
    (covers : ∀ q : Q, ∃ g : A, g • x=x ∧ f g=q) :
    ∃ (V : Type u) (_ : AddCommGroup V) (e : V ↪ X) (L : Q →* Multiplicative (AddAut V))
      (ρ : A →* Equiv.Perm V) (c : A → V),
      Set.range e = MulAction.orbit A x ∧ Nat.card V ∣ Nat.card f.ker ∧
      (∀ g z, g • e z=e (ρ g z)) ∧ (∀ g z, ρ g z=(L (f g)).toAdd z+c g) ∧
      ∀ h : Equiv.Perm V, h ∈ ρ.range ↔ ∃ (q : Q) (b : V), ∀ z, h z=(L q).toAdd z+b := by
  classical
  obtain ⟨V,inst,e,L,c,range,_,act,trans,pure,card⟩ := affine_orbit_coordinates f comm x covers
  let F (g : A) : Equiv.Perm V := (L (f g)).toAdd.toEquiv.trans (Equiv.addRight (c g))
  have equivariant (g : A) (z : V) : g • e z=e (F g z) := act g z
  have mult (g h : A) : F (g*h)=F g*F h := by
    ext z
    apply e.injective
    change e (F (g*h) z)=e (F g (F h z))
    rw [← equivariant,← equivariant,← equivariant,mul_smul]
  let ρ := MonoidHom.mk' F mult
  refine ⟨V,inst,e,L,ρ,c,range,card,equivariant,fun _ _ => rfl,?_⟩
  intro h
  constructor
  · rintro ⟨g,rfl⟩
    exact ⟨f g,c g,fun _ => rfl⟩
  · rintro ⟨q,b,description⟩
    obtain ⟨n,translate⟩ := trans b
    obtain ⟨g,hg,hc⟩ := pure q
    refine ⟨(n:A)*g,?_⟩
    ext z
    apply e.injective
    change e (F ((n:A)*g) z)=e (h z)
    rw [← equivariant,mul_smul,act g,hg,hc,add_zero,translate,description,add_comm]

end NonfreeEleven
end

section
/- # Separating regular cycle vertices in a finite action by affine maps -/

namespace NonfreeEleven

/-- An injective evaluation point on two separate lists, using unordered pairs. -/
theorem exists_separating_point {A X Y : Type*} [Fintype X]
    (eval : A → X → Y) (B : ℕ)
    (small : ∀ g h : A,g≠h → {x : X | eval g x=eval h x}.ncard≤B)
    (left right : Finset A)
    (room : (left.card.choose 2+right.card.choose 2)*B<Fintype.card X) :
    ∃ x : X, Set.InjOn (fun g => eval g x) (left : Set A) ∧
      Set.InjOn (fun g => eval g x) (right : Set A) := by
  classical
  let bad (p : Finset A) : Finset X := Finset.univ.filter (fun x => ¬Set.InjOn (fun g => eval g x) (p : Set A))
  have count (p : Finset A) (hp : p.card=2) : (bad p).card≤B := by
    obtain ⟨g,h,ne,rfl⟩ := Finset.card_eq_two.mp hp
    have incl : (bad {g,h} : Set X) ⊆ {x : X | eval g x=eval h x} := by
      intro x hx
      by_contra no
      have inj : Set.InjOn (fun k => eval k x) (({g,h} : Finset A) : Set A) := by
        intro k hk l hl eq
        simp only [Finset.mem_coe,Finset.mem_insert,Finset.mem_singleton] at hk hl
        rcases hk with rfl|rfl <;> rcases hl with rfl|rfl <;> first | rfl | exact (no eq).elim | exact (no eq.symm).elim
      exact (Finset.mem_filter.mp hx).2 inj
    rw [←Set.ncard_coe_finset]
    exact (Set.ncard_le_ncard incl).trans (small g h ne)
  let allbad (s : Finset A) : Finset X := (s.powersetCard 2).biUnion bad
  have total (s : Finset A) : (allbad s).card ≤ s.card.choose 2*B := by
    calc
      (allbad s).card ≤ ∑ p ∈ s.powersetCard 2,(bad p).card := Finset.card_biUnion_le
      _ ≤ ∑ _p ∈ s.powersetCard 2,B := Finset.sum_le_sum fun p hp => count p (Finset.mem_powersetCard.mp hp).2
      _ = _ := by simp
  have bound : (allbad left ∪ allbad right).card<Fintype.card X := by
    calc
      _ ≤ (allbad left).card+(allbad right).card := Finset.card_union_le _ _
      _ ≤ left.card.choose 2*B+right.card.choose 2*B := Nat.add_le_add (total _) (total _)
      _ < _ := by rwa [←Nat.add_mul]
  obtain ⟨x,hx⟩ : ∃ x : X,x ∉ allbad left ∪ allbad right := by
    by_contra! h
    have eq : allbad left ∪ allbad right=Finset.univ := Finset.eq_univ_of_forall h
    simp [eq] at bound
  have safe (s : Finset A) (ok : x ∉ allbad s) : Set.InjOn (fun g => eval g x) (s : Set A) := by
    intro g hg h hh eq
    by_contra ne
    apply ok
    apply Finset.mem_biUnion.mpr
    refine ⟨{g,h},Finset.mem_powersetCard.mpr ⟨?_,Finset.card_eq_two.mpr ⟨g,h,ne,rfl⟩⟩,?_⟩
    · apply Finset.insert_subset hg (Finset.singleton_subset_iff.mpr hh)
    · apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,fun inj => ne (inj (by simp) (by simp) eq)⟩
  exact ⟨x,safe left (fun h => hx (Finset.mem_union_left _ h)),safe right (fun h => hx (Finset.mem_union_right _ h))⟩

/-- Equalities between two affine transformations on a finite abelian group have no more
solutions than the equalizer of their linear parts. -/
theorem affine_fiber_bound {V : Type*} [AddCommGroup V] [Fintype V]
    (S T : V →+ V) (a b : V) :
    {x : V | S x+a=T x+b}.ncard ≤ {u : V | S u=T u}.ncard := by
  classical
  by_cases nonempty : ∃ x : V,S x+a=T x+b
  · obtain ⟨x,hx⟩ := nonempty
    apply Set.ncard_le_ncard_of_injOn (fun y : V => y-x)
    · intro y hy
      change S (y-x)=T (y-x)
      change S y+a=T y+b at hy
      rw [map_sub,map_sub]
      linear_combination (norm := abel) hy-hx
    · exact (sub_left_injective).injOn
  · have empty : {x : V | S x+a=T x+b}=∅ := by
      ext x; simpa using (not_exists.mp nonempty x)
    simp [empty]

open SimpleGraph

/-- A cycle of length at most 32 in the bipartite regular graph descends at a suitable
evaluation point if every coincidence between distinct actions occupies less than one
240th of the finite space. There are at most 120 unordered vertex pairs on either side. -/
theorem transfer_short_cycle {A X : Type*} [Fintype X]
    (eval : A → X → X) (B : ℕ)
    (small : ∀ g h : A,g≠h → {x : X | eval g x=eval h x}.ncard≤B)
    (room : 240*B<Fintype.card X)
    (R : SimpleGraph (Bool × A)) (G : SimpleGraph (Bool × X))
    (bip : ∀ u v,R.Adj u v → u.1≠v.1)
    (edge : ∀ u v,R.Adj u v → ∀ x : X,G.Adj (u.1,eval u.2 x) (v.1,eval v.2 x))
    (n : ℕ) (hn : n=4 ∨ n=8 ∨ n=16 ∨ n=32) (cycle : cycleGraph n ⊑ R) :
    cycleGraph n ⊑ G := by
  classical
  obtain ⟨w⟩ := cycle
  have pair : ∀ i j : Fin n,i.val/2=j.val/2 → i≠j → (cycleGraph n).Adj i j := by
    rcases hn with rfl|rfl|rfl|rfl <;> decide
  have limit : n≤32 := by omega
  let color (b : Bool) := Finset.univ.filter (fun i : Fin n => (w i).1=b)
  let labels (b : Bool) := (color b).image (fun i => (w i).2)
  have size (b : Bool) : (labels b).card≤16 := by
    let number (i : color b) : Fin 16 := ⟨i.val.val/2,by have h := i.val.isLt; omega⟩
    have inj : Function.Injective number := by
      intro i j eq
      have same : i.val.val/2=j.val.val/2 := congrArg Fin.val eq
      apply Subtype.ext
      by_contra ne
      have opp := bip _ _ (w.toHom.map_rel' (pair _ _ same ne))
      exact opp ((Finset.mem_filter.mp i.property).2.trans (Finset.mem_filter.mp j.property).2.symm)
    exact Finset.card_image_le.trans (by simpa using Fintype.card_le_of_injective number inj)
  have capacity : ((labels false).card.choose 2+(labels true).card.choose 2)*B<Fintype.card X := by
    have c (b : Bool) : (labels b).card.choose 2≤120 :=
      (Nat.choose_le_choose 2 (size b)).trans (by decide)
    exact (Nat.mul_le_mul_right B (Nat.add_le_add (c false) (c true))).trans_lt room
  obtain ⟨x,safeLeft,safeRight⟩ := exists_separating_point eval B small (labels false) (labels true) capacity
  have safe (b : Bool) : Set.InjOn (fun g => eval g x) (labels b : Set A) := by
    cases b
    · exact safeLeft
    · exact safeRight
  have mem (i : Fin n) : (w i).2 ∈ labels (w i).1 := by
    exact Finset.mem_image.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩,rfl⟩
  refine ⟨⟨⟨fun i => ((w i).1,eval (w i).2 x),fun {i j} e => edge _ _ (w.toHom.map_rel' e) x⟩,?_⟩⟩
  intro i j eq
  have sides : (w i).1=(w j).1 := congrArg (fun z : Bool × X => z.1) eq
  exact w.injective (Prod.ext sides (safe (w i).1 (mem i) (sides ▸ mem j) (congrArg Prod.snd eq)))

/-- For a prime-order linear action all unequal affine maps have at most one coset
of the common fixed subgroup as their coincidence set. -/
theorem prime_affine_collision {V Q : Type*} [AddCommGroup V] [Fintype V]
    [Group Q] [DistribMulAction Q V] (prime : (Nat.card Q).Prime)
    (g h : Q × V) (ne : g ≠ h) :
    {x : V | g.1 • x+g.2=h.1 • x+h.2}.ncard ≤
      {u : V | ∀ k : Q,k • u=u}.ncard := by
  classical
  by_cases parts : g.1=h.1
  · have none : {x : V | g.1 • x+g.2=h.1 • x+h.2}=∅ := by
      ext x
      simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
      intro eq
      rw [parts] at eq
      exact ne (Prod.ext parts (add_left_cancel eq))
    simp [none]
  let T (k : Q) : V →+ V := { toFun := fun v => k • v, map_zero' := smul_zero _, map_add' := smul_add _ }
  apply (affine_fiber_bound (T g.1) (T h.1) g.2 h.2).trans
  apply Set.ncard_le_ncard (ht := Set.toFinite _)
  intro u eq
  change g.1 • u=h.1 • u at eq
  let H := MulAction.stabilizer Q u
  have mem : h.1⁻¹*g.1 ∈ H := by
    change (h.1⁻¹*g.1) • u=u
    rw [mul_smul,eq,inv_smul_smul]
  let _ : Fact (Nat.card Q).Prime := ⟨prime⟩
  have top : H=⊤ := H.eq_bot_or_eq_top_of_prime_card.resolve_left (by
    intro bot
    rw [bot,Subgroup.mem_bot] at mem
    exact parts (inv_mul_eq_one.mp mem).symm)
  intro k
  have m : k∈H := top ▸ Subgroup.mem_top k
  exact m

/-- A finite affine action with prime-order linear quotient preserves any regular
power-of-two cycle of length ≤32 on at least one evaluation orbit when its fixed
subgroup has index greater than 240. -/
theorem prime_affine_transfer {V Q : Type*} [AddCommGroup V] [Fintype V]
    [Group Q] [DistribMulAction Q V] (prime : (Nat.card Q).Prime)
    (room : 240*{u : V | ∀ k : Q,k • u=u}.ncard<Fintype.card V)
    (R : SimpleGraph (Bool × (Q × V))) (G : SimpleGraph (Bool × V))
    (bip : ∀ u v,R.Adj u v → u.1≠v.1)
    (edge : ∀ u v,R.Adj u v → ∀ x : V,G.Adj (u.1,u.2.1 • x+u.2.2) (v.1,v.2.1 • x+v.2.2))
    (n : ℕ) (hn : n=4 ∨ n=8 ∨ n=16 ∨ n=32) (cycle : cycleGraph n ⊑ R) :
    cycleGraph n ⊑ G :=
  transfer_short_cycle (fun (g : Q × V) x => g.1 • x+g.2) _
    (prime_affine_collision prime) room R G bip edge n hn cycle

end NonfreeEleven
end

section
/- # The large fixed-subgroup index case of the index-eleven matching problem -/

namespace NonfreeEleven
open SimpleGraph

/-- Three normalized affine matchings on a finite abelian group with an order-eleven
linear action contain a power-of-two cycle when the common fixed subgroup has index
above 240. Distinctness is required only for the affine group elements. -/
theorem large_affine_eleven_cycle {V : Type*} [AddCommGroup V] [Fintype V]
    [DistribMulAction (Multiplicative (ZMod 11)) V]
    (room : 240*{x : V | ∀ k : Multiplicative (ZMod 11),k • x=x}.ncard<Fintype.card V)
    (p q : Multiplicative (ZMod 11) × V) (moving : p.1≠1 ∨ q.1≠1)
    (separate : p≠(1,0) ∧ q≠(1,0) ∧ p≠q) (G : SimpleGraph (Bool × V))
    (idEdge : ∀ x,G.Adj (false,x) (true,x))
    (pEdge : ∀ x,G.Adj (false,x) (true,p.1 • x+p.2))
    (qEdge : ∀ x,G.Adj (false,x) (true,q.1 • x+q.2)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  classical
  let Q := Multiplicative (ZMod 11)
  let φ : Q →* MulAut (Multiplicative V) := {
    toFun := fun k => AddEquiv.toMultiplicative {
      toFun := fun z : V => k • z, invFun := fun z => k⁻¹ • z,
      left_inv := inv_smul_smul k, right_inv := smul_inv_smul k,
      map_add' := smul_add k }
    map_one' := by ext z; exact one_smul _ z.toAdd
    map_mul' := by intro g h; ext z; exact mul_smul g h z.toAdd }
  let A := SemidirectProduct (Multiplicative V) Q φ
  let f : A →* Q := SemidirectProduct.rightHom
  have onto : Function.Surjective f := SemidirectProduct.rightHom_surjective
  have comm (g h : f.ker) : g*h=h*g := by
    apply Subtype.ext
    apply SemidirectProduct.ext
    · change (g:A).left * φ (g:A).right (h:A).left = (h:A).left * φ (h:A).right (g:A).left
      have hg : (g:A).right=1 := g.property
      have hh : (h:A).right=1 := h.property
      rw [hg,hh,map_one,MulAut.one_apply,MulAut.one_apply,mul_comm]
    · change (g:A).right*(h:A).right=(h:A).right*(g:A).right
      exact mul_comm _ _
  let _ : MulAction A (Q × V) := {
    smul := fun g y => (g.right*y.1,g.left.toAdd+g.right • y.2)
    one_smul := by intro y; change (1*y.1,0+(1:Q) • y.2)=y; simp
    mul_smul := by
      intro g h y
      apply Prod.ext
      · exact mul_assoc _ _ _
      · change (g.left.toAdd+g.right • h.left.toAdd)+(g.right*h.right) • y.2 =
          g.left.toAdd+g.right • (h.left.toAdd+h.right • y.2)
        rw [mul_smul,smul_add,add_assoc] }
  let elt (y : Q × V) : A := ⟨Multiplicative.ofAdd y.2,y.1⟩
  have inj : Function.Injective elt := by
    intro y z eq
    exact Prod.ext (congrArg SemidirectProduct.right eq)
      (congrArg (fun g : A => g.left.toAdd) eq)
  have cancel {a b : A} {y : Q × V} (h : a • y=b • y) : a=b :=
    mul_right_cancel (show a*elt y=b*elt y from congrArg elt h)
  have sep (y : Q × V) : elt p • y≠y ∧ elt q • y≠y ∧ elt p • y≠elt q • y := by
    have id (r : Q × V) (h : elt r • y=y) : r=(1,0) :=
      inj (cancel (b := 1) (h.trans (one_smul A y).symm))
    exact ⟨fun h => separate.1 (id p h),fun h => separate.2.1 (id q h),
      fun h => separate.2.2 (inj (cancel h))⟩
  let ev (g : Q × V) (x : V) := g.1 • x+g.2
  let R : SimpleGraph (Bool × (Q × V)) := {
    Adj := fun u v => u.1≠v.1 ∧ ∀ x,G.Adj (u.1,ev u.2 x) (v.1,ev v.2 x)
    symm := ⟨fun _ _ h => ⟨h.1.symm,fun x => (h.2 x).symm⟩⟩
    loopless := ⟨fun _ h => h.1 rfl⟩ }
  have comp (r y : Q × V) (x : V) : ev (elt r • y) x=r.1 • ev y x+r.2 := by
    change (r.1*y.1) • x + (r.2+r.1 • y.2) = r.1 • (y.1 • x+y.2)+r.2
    rw [mul_smul,smul_add]; abel
  have edge (r : Q × V) (h : ∀ x : V,G.Adj (false,x) (true,r.1 • x+r.2)) (y : Q × V) :
      R.Adj (false,y) (true,elt r • y) :=
    ⟨(by decide : false ≠ true),fun x => (comp r y x).symm ▸ h (ev y x)⟩
  have regular := index_eleven_orbit f onto comm ((1,0) : Q × V)
    (fun g h => by have hg : g=1 := cancel (h.trans (one_smul A _).symm); rw [hg,map_one])
    (elt p) (elt q) moving sep R (fun y => ⟨(by decide : false ≠ true),fun x => idEdge (ev y x)⟩)
    (edge p pEdge) (edge q qEdge)
  have prime : (Nat.card Q).Prime := by change (Nat.card (ZMod 11)).Prime; simp; decide
  have transfer (n : ℕ) (hn : n=4 ∨ n=8 ∨ n=16 ∨ n=32) (h : cycleGraph n ⊑ R) :
      cycleGraph n ⊑ G :=
    prime_affine_transfer prime room R G (fun _ _ e => e.1) (fun _ _ e => e.2) n hn h
  rcases regular with h|h|h|h
  · exact Or.inl (transfer 4 (by decide) h)
  · exact Or.inr (Or.inl (transfer 8 (by decide) h))
  · exact Or.inr (Or.inr (Or.inl (transfer 16 (by decide) h)))
  · exact Or.inr (Or.inr (Or.inr (transfer 32 (by decide) h)))

end NonfreeEleven
end

section
/- # Fixed and moving coordinates of a finite abelian group under a periodic automorphism -/

namespace NonfreeEleven

/-- A fixed element in the image of T−1 is killed by every period of T. -/
theorem fixed_image_torsion {V : Type*} [AddCommGroup V] (T : V →+ V) (n : ℕ)
    (period : ∀ x : V,T^[n] x=x) (y : V)
    (image : y∈(T-AddMonoidHom.id V).range) (fixed : T y=y) : n • y=0 := by
  obtain ⟨v,hv⟩ := image
  change T v-v=y at hv
  have step : T v=v+y := by linear_combination (norm := abel) hv
  have telescopes (k : ℕ) : T^[k] v=v+k • y := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply',ih,map_add,map_nsmul,step,fixed,add_nsmul]
      simp [add_assoc,add_left_comm,add_comm]
  have z := (telescopes n).symm.trans (period v)
  simpa using z

/-- If the moving subgroup has size coprime to the period, addition identifies the
fixed subgroup times the moving subgroup with the entire finite abelian group. -/
theorem fixed_image_product {V : Type*} [AddCommGroup V] [Finite V] (T : V →+ V) (n : ℕ)
    (period : ∀ x : V,T^[n] x=x) (cop : Nat.Coprime n (Nat.card (T-AddMonoidHom.id V).range)) :
    ∃ E : (T-AddMonoidHom.id V).ker × (T-AddMonoidHom.id V).range ≃+ V,
      ∀ p,E p=(p.1:V)+(p.2:V) := by
  classical
  let D := T-AddMonoidHom.id V
  have disjoint (y : V) (image : y ∈ D.range) (fixed : D y=0) : y=0 := by
    have ny := fixed_image_torsion T n period y image (sub_eq_zero.mp fixed)
    let m : D.range := ⟨y,image⟩
    have kill : n • m=0 := Subtype.ext ny
    have one : addOrderOf m=1 := Nat.eq_one_of_dvd_coprimes cop
      (addOrderOf_dvd_iff_nsmul_eq_zero.mpr kill) (addOrderOf_dvd_natCard m)
    exact congrArg (fun z : D.range => (z:V)) (AddMonoid.addOrderOf_eq_one_iff.mp one)
  let step (m : D.range) : D.range := ⟨D m, m, rfl⟩
  have inj : Function.Injective step := by
    intro m k eq
    have val : D (m:V)=D (k:V) := congrArg (fun z : D.range => (z:V)) eq
    apply Subtype.ext
    exact sub_eq_zero.mp (disjoint ((m:V)-(k:V)) (D.range.sub_mem m.property k.property)
      (by rw [map_sub,val,sub_self]))
  have surj := Finite.surjective_of_injective inj
  let sum : D.ker × D.range →+ V := {
    toFun p := (p.1:V)+(p.2:V)
    map_zero' := by simp
    map_add' := by rintro ⟨u,m⟩ ⟨v,k⟩; change ((u:V)+v)+((m:V)+k)=_; change _=((u:V)+m)+((v:V)+k); abel }
  have onto : Function.Surjective sum := by
    intro x
    obtain ⟨m,eq⟩ := surj (⟨D x,x,rfl⟩ : D.range)
    have h : D (m:V)=D x := congrArg (fun z : D.range => (z:V)) eq
    have mem : x-(m:V) ∈ D.ker := by change D (x-(m:V))=0; rw [map_sub,h,sub_self]
    exact ⟨(⟨_,mem⟩,m),sub_add_cancel _ _⟩
  have one : Function.Injective sum := by
    rintro ⟨u,m⟩ ⟨v,k⟩ eq
    change (u:V)+(m:V)=(v:V)+(k:V) at eq
    have du : D (u:V)=0 := u.property
    have dv : D (v:V)=0 := v.property
    have e := congrArg D eq
    rw [map_add,map_add,du,dv,zero_add,zero_add] at e
    have mm : m=k := inj (Subtype.ext e)
    subst k
    exact Prod.ext (Subtype.ext (add_right_cancel eq)) rfl
  exact ⟨AddEquiv.ofBijective sum ⟨one,onto⟩,fun _ => rfl⟩

end NonfreeEleven
end

section
/- # Orders of small moving subgroups for an automorphism of order eleven -/
namespace NonfreeEleven

/-- Away from eleven, the order of every Sylow subgroup is one modulo eleven. -/
theorem moving_sylow_order {M : Type*} [CommGroup M] [Fintype M]
    (T : MulAut M) (period : T^11=1) (fixed : ∀ x : M, T x=x → x^11=1)
    (p : ℕ) (hp : p.Prime) (away : p≠11) :
    p^(Nat.card M).factorization p ≡ 1 [MOD 11] := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let P : Sylow p M := Classical.choice Sylow.nonempty
  let _ : P.1.Characteristic := P.characteristic_of_normal (Subgroup.normal_of_isMulCommutative _)
  let φ := (MulAut.toPerm P.1).comp (MulAut.characteristic P.1)
  let t := φ T
  have ts : t^11^1=1 := by
    change (φ T)^11^1=1
    rw [pow_one,← map_pow,period,map_one]
  have fp : t.supportᶜ = {1} := by
    ext m
    simp only [Finset.mem_compl,Equiv.Perm.mem_support,not_not,Finset.mem_singleton]
    constructor
    · intro eq
      have fixM : T (m:M)=(m:M) := congrArg (fun a : P.1 => (a:M)) eq
      have p11 : m^11=1 := Subtype.ext (fixed _ fixM)
      have cop : (p^(Nat.card M).factorization p).Coprime 11 := by
        simpa using Nat.coprime_pow_primes ((Nat.card M).factorization p) 1 hp (by decide : Nat.Prime 11) away
      have fac := orderOf_dvd_natCard m
      rw [P.card_eq_multiplicity] at fac
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes cop fac
        (orderOf_dvd_iff_pow_eq_one.mpr p11))
    · rintro rfl
      exact map_one ((MulAut.characteristic P.1) T)
  have congr := (Equiv.Perm.card_compl_support_modEq ts).symm
  rw [fp,Finset.card_singleton,← Nat.card_eq_fintype_card,P.card_eq_multiplicity] at congr
  exact congr

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
/-- The possible orders of a moving subgroup of size at most 240. -/
theorem small_moving_orders {M : Type*} [CommGroup M] [Fintype M]
    (T : MulAut M) (period : T^11=1) (fixed : ∀ x : M, T x=x → x^11=1)
    (size : Nat.card M ≤ 240) :
    Nat.card M ∈ ([1,11,23,67,89,121,199] : List ℕ) := by
  let rows : List (ℕ × ℕ × ℕ) := [
    (2,0,0),(2,0,1),(2,1,1),(3,1,1),(2,2,1),(5,1,1),(2,1,3),(7,1,1),
    (2,3,1),(3,2,1),(2,1,5),(2,0,11),(2,2,3),(13,1,1),(2,1,7),(3,1,5),
    (2,4,1),(17,1,1),(2,1,9),(19,1,1),(2,2,5),(3,1,7),(2,1,11),(2,0,23),
    (2,3,3),(5,2,1),(2,1,13),(3,3,1),(2,2,7),(29,1,1),(2,1,15),(31,1,1),
    (2,5,1),(3,1,11),(2,1,17),(5,1,7),(2,2,9),(37,1,1),(2,1,19),(3,1,13),
    (2,3,5),(41,1,1),(2,1,21),(43,1,1),(2,2,11),(3,2,5),(2,1,23),(47,1,1),
    (2,4,3),(7,2,1),(2,1,25),(3,1,17),(2,2,13),(53,1,1),(2,1,27),(5,1,11),
    (2,3,7),(3,1,19),(2,1,29),(59,1,1),(2,2,15),(61,1,1),(2,1,31),(3,2,7),
    (2,6,1),(5,1,13),(2,1,33),(2,0,67),(2,2,17),(3,1,23),(2,1,35),(71,1,1),
    (2,3,9),(73,1,1),(2,1,37),(3,1,25),(2,2,19),(7,1,11),(2,1,39),(79,1,1),
    (2,4,5),(3,4,1),(2,1,41),(83,1,1),(2,2,21),(5,1,17),(2,1,43),(3,1,29),
    (2,3,11),(2,0,89),(2,1,45),(7,1,13),(2,2,23),(3,1,31),(2,1,47),(5,1,19),
    (2,5,3),(97,1,1),(2,1,49),(3,2,11),(2,2,25),(101,1,1),(2,1,51),(103,1,1),
    (2,3,13),(3,1,35),(2,1,53),(107,1,1),(2,2,27),(109,1,1),(2,1,55),(3,1,37),
    (2,4,7),(113,1,1),(2,1,57),(5,1,23),(2,2,29),(3,2,13),(2,1,59),(7,1,17),
    (2,3,15),(2,0,121),(2,1,61),(3,1,41),(2,2,31),(5,3,1),(2,1,63),(127,1,1),
    (2,7,1),(3,1,43),(2,1,65),(131,1,1),(2,2,33),(7,1,19),(2,1,67),(3,3,5),
    (2,3,17),(137,1,1),(2,1,69),(139,1,1),(2,2,35),(3,1,47),(2,1,71),(13,1,11),
    (2,4,9),(5,1,29),(2,1,73),(3,1,49),(2,2,37),(149,1,1),(2,1,75),(151,1,1),
    (2,3,19),(3,2,17),(2,1,77),(5,1,31),(2,2,39),(157,1,1),(2,1,79),(3,1,53),
    (2,5,5),(7,1,23),(2,1,81),(163,1,1),(2,2,41),(3,1,55),(2,1,83),(167,1,1),
    (2,3,21),(13,2,1),(2,1,85),(3,2,19),(2,2,43),(173,1,1),(2,1,87),(5,2,7),
    (2,4,11),(3,1,59),(2,1,89),(179,1,1),(2,2,45),(181,1,1),(2,1,91),(3,1,61),
    (2,3,23),(5,1,37),(2,1,93),(17,1,11),(2,2,47),(3,3,7),(2,1,95),(191,1,1),
    (2,6,3),(193,1,1),(2,1,97),(3,1,65),(2,2,49),(197,1,1),(2,1,99),(2,0,199),
    (2,3,25),(3,1,67),(2,1,101),(7,1,29),(2,2,51),(5,1,41),(2,1,103),(3,2,23),
    (2,4,13),(19,1,11),(2,1,105),(211,1,1),(2,2,53),(3,1,71),(2,1,107),(5,1,43),
    (2,3,27),(7,1,31),(2,1,109),(3,1,73),(2,2,55),(13,1,17),(2,1,111),(223,1,1),
    (2,5,7),(3,2,25),(2,1,113),(227,1,1),(2,2,57),(229,1,1),(2,1,115),(3,1,77),
    (2,3,29),(233,1,1),(2,1,117),(5,1,47),(2,2,59),(3,1,79),(2,1,119),(239,1,1),
    (2,4,15)]
  have verified : ∀ i : Fin 241,
      i.val ∈ ([0,1,11,23,67,89,121,199] : List ℕ) ∨
      let z := rows[i.val]!
      z.1.Prime ∧ z.1≠11 ∧ i.val=z.1^z.2.1*z.2.2 ∧
      z.2.2≠0 ∧ ¬ z.1 ∣ z.2.2 ∧ z.1^z.2.1%11≠1 := by
    dsimp only [rows]
    decide
  let i : Fin 241 := ⟨Nat.card M,by omega⟩
  rcases verified i with good|bad
  · exact (List.mem_cons.mp good).resolve_left (Nat.card_pos.ne' : Nat.card M ≠ 0)
  · let z := rows[i.val]!
    change z.1.Prime ∧ z.1≠11 ∧ Nat.card M=z.1^z.2.1*z.2.2 ∧
      z.2.2≠0 ∧ ¬ z.1 ∣ z.2.2 ∧ z.1^z.2.1%11≠1 at bad
    obtain ⟨hp,away,eqn,nonzero,nd,notmod⟩ := bad
    have fk : (Nat.card M).factorization z.1=z.2.1 := by
      rw [eqn,Nat.factorization_mul (pow_ne_zero _ hp.ne_zero) nonzero]
      simp only [Finsupp.add_apply,hp.factorization_pow,Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd nd,add_zero]
    have congr := moving_sylow_order T period fixed z.1 hp away
    rw [fk] at congr
    exact (notmod congr).elim

set_option maxHeartbeats 800000 in
/-- Small moving subgroups in finite abelian actions of period eleven. -/
theorem affine_small_moving_orders {V : Type*} [AddCommGroup V] [Finite V]
    (T : V →+ V) (period : ∀ x : V,T^[11] x=x)
    (size : Nat.card (T-AddMonoidHom.id V).range ≤ 240) :
    Nat.card (T-AddMonoidHom.id V).range ∈ ([1,11,23,67,89,121,199] : List ℕ) := by
  classical
  let D := T-AddMonoidHom.id V
  let M := D.range
  let _ : Fintype M := Fintype.ofFinite _
  let step : M →+ M := {
    toFun y := ⟨T y,by
      obtain ⟨v,h⟩ := y.property
      refine ⟨T v,?_⟩
      rw [← h]
      change T (T v)-T v=T (T v-v)
      rw [map_sub]⟩
    map_zero' := Subtype.ext (map_zero T)
    map_add' := fun x y => Subtype.ext (map_add T _ _) }
  have sem : Function.Semiconj (fun x : M => (x:V)) step T := fun _ => rfl
  have cyclic (x : M) : step^[11] x=x := Subtype.ext ((sem.iterate_right 11 x).trans (period _))
  have inj : Function.Injective step := by
    intro x y h
    calc x = step^[11] x := (cyclic x).symm
         _ = step^[11] y := by simpa only [Function.iterate_succ_apply] using congrArg (fun z => step^[10] z) h
         _ = y := cyclic y
  let e := (AddEquiv.ofBijective step ⟨inj,Finite.surjective_of_injective inj⟩).toMultiplicative
  let project (m : Multiplicative M) : M := m.toAdd
  have conv (k : ℕ) (m : Multiplicative M) : project ((e^k) m)=step^[k] (project m) := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ',Function.iterate_succ_apply']
      change step (project ((e^k) m))=step (step^[k] (project m))
      rw [ih]
  have ep : e^11=1 := by
    apply MulEquiv.ext
    intro m
    exact congrArg Multiplicative.ofAdd ((conv 11 m).trans (cyclic _))
  have fixed (m : Multiplicative M) (h : e m=m) : m^11=1 := by
    have he : T (project m:V)=(project m:V) := congrArg (fun z : Multiplicative M => ((project z):V)) h
    change 11 • project m=0
    apply Subtype.ext
    exact fixed_image_torsion T 11 period (project m:V) (project m).property he
  have card : Nat.card (Multiplicative M)=Nat.card M := Nat.card_congr Multiplicative.toAdd
  have order := small_moving_orders (M := Multiplicative M) e ep fixed (card ▸ size)
  rwa [card] at order


end NonfreeEleven
end

section
/-
# Balanced alternating walks for four affine prime fields

The certificate uses base-three digits in chronological order. Two consecutive
digits stand for a forward label and an inverse label. The two vertex lists
contain the departure point of every forward and inverse step respectively.
The endpoint after the final inverse step is stored separately. Source walks
from the Left to Solve affine-path computation, verified by Codex, gpt-6.2-astra.
-/

namespace NonfreeEleven.SmallField

abbrev Label := Fin 3
abbrev Word := List (Label × Label)

def forward {R : Type*} [Ring R] (a b : R) (k : Label) (x : R) : R :=
  if k = 0 then x else if k = 1 then a*x else b*x+1

def backward {R : Type*} [Ring R] (ia ib : R) (k : Label) (y : R) : R :=
  if k = 0 then y else if k = 1 then ia*y else ib*(y-1)

structure Trace (R : Type*) where
  left : List R
  right : List R
  endpoint : R

def trace {R : Type*} (f g : Label → R → R) (x : R) : Word → Trace R
  | [] => ⟨[], [], x⟩
  | (i,j)::rest =>
    let y := f i x
    let r := trace f g (g j y) rest
    ⟨x::r.left, y::r.right, r.endpoint⟩

theorem trace_lengths {R : Type*} (f g : Label → R → R) (x : R) (w : Word) :
    (trace f g x w).left.length = w.length ∧ (trace f g x w).right.length = w.length := by
  induction w generalizing x with
  | nil => simp [trace]
  | cons ij w ih =>
    rcases ij with ⟨i,j⟩
    obtain ⟨hl,hr⟩ := ih (g j (f i x))
    simp [trace,hl,hr]

/-- Both sides have distinct vertices before the final return. Every label has
the same number of forward and inverse occurrences. -/
def BalancedCycle {R : Type*} (f g : Label → R → R) (x : R) (w : Word) : Prop :=
  let r := trace f g x w
  (2*w.length = 16 ∨ 2*w.length = 32) ∧
    (∀ k : Label, (w.map Prod.fst).count k = (w.map Prod.snd).count k) ∧
    r.endpoint = x ∧ r.left.Nodup ∧ r.right.Nodup

instance {R : Type*} [DecidableEq R] (f g : Label → R → R) (x : R) (w : Word) :
    Decidable (BalancedCycle f g x w) := by unfold BalancedCycle; infer_instance

def decode : ℕ → ℕ → Word
  | 0, _ => []
  | k+1, n => (Fin.ofNat 3 n, Fin.ofNat 3 (n/3)) :: decode k (n/9)

private abbrev Seed := ℕ × ℕ × ℕ
private abbrev Table := List (ℕ × List (ℕ × Seed))

private def record (t : Table) (a b : ℕ) : Seed :=
  ((t.lookup a).bind (fun row => row.lookup b)).getD (0,0,0)

private def check (q : ℕ) (t : Table) (a b : ZMod q) : Bool :=
  let (z,k,c) := record t a.val b.val
  decide (BalancedCycle (forward a b) (backward (a^10) (b^10)) (z : ZMod q) (decode k c))

private theorem inverse_tenth {R : Type*} [Field R] {a : R} (h : a^11=1) : a^10=a⁻¹ := by
  have ha : a ≠ 0 := fun eq => by simp [eq] at h
  apply (mul_right_cancel₀ ha)
  simpa [← pow_succ, inv_mul_cancel₀ ha] using h

/-- A positive certificate uses the actual inverse transformations over the field. -/
private theorem of_check (q : ℕ) [Fact q.Prime] (t : Table) (a b : ZMod q)
    (ha : a^11=1) (hb : b^11=1) (good : check q t a b = true) :
    ∃ z w, BalancedCycle (forward a b) (backward a⁻¹ b⁻¹) z w := by
  obtain ⟨u,j,n,hr⟩ : ∃ u j n, record t a.val b.val = (u,j,n) := ⟨_,_,_,rfl⟩
  exact ⟨(u : ZMod q), decode j n, by
    simpa [check,hr,inverse_tenth ha,inverse_tenth hb] using good⟩

private def Covered (q : ℕ) (t : Table) : Prop :=
  ∀ a : ZMod q, a^11=1 → a≠1 → ∀ b : ZMod q, b^11=1 → check q t a b = true

-- Each entry gives b, the starting point, the number of label pairs and their base-nine code.
private def t23 : Table := [
  (2,[(1,2,8,34695840),(2,3,8,24904308),(3,1,8,37327260),(4,1,8,37333848),(6,2,8,34440420),(8,1,8,34846716),(9,2,8,37274772),(12,1,8,37631172),(13,1,8,34164372),(16,1,8,25083948),(18,6,8,37631172)]),
  (3,[(1,1,8,34695840),(2,2,8,37333848),(3,5,8,26676156),(4,2,8,24589308),(6,1,8,34846716),(8,1,8,24549996),(9,1,8,34164372),(12,1,8,24847428),(13,5,8,36998796),(16,1,8,37631172),(18,1,8,34400244)]),
  (4,[(1,1,8,34695840),(2,1,8,37327260),(3,1,8,31484640),(4,1,8,26676156),(6,0,16,1354290152916624),(8,1,8,34440420),(9,4,8,36998796),(12,2,8,24576564),(13,0,16,1084881144613028),(16,0,16,1591893963421404),(18,0,16,451811549748920)]),
  (6,[(1,1,8,34695840),(2,1,8,37327260),(3,1,8,25083948),(4,0,16,1058370621868544),(6,1,8,26676156),(8,1,8,31458720),(9,0,16,1617650328080608),(12,3,8,34440420),(13,0,16,490054536750740),(16,0,16,1470685836058764),(18,1,8,34851108)]),
  (8,[(1,5,8,34695840),(2,1,8,24549996),(3,1,8,24847428),(4,1,8,34164372),(6,3,8,34400244),(8,1,8,26676156),(9,2,8,24589308),(12,3,8,31487592),(13,2,8,37097544),(16,2,8,25973724),(18,2,8,34846716)]),
  (9,[(1,4,8,25083948),(2,2,8,32846016),(3,1,8,32196144),(4,3,8,36998796),(6,0,16,467067717015404),(8,1,8,31484640),(9,1,8,37327260),(12,1,8,34440420),(13,0,16,467082228335852),(16,1,8,34873068),(18,1,8,24576564)]),
  (12,[(1,3,8,32570400),(2,1,8,25285260),(3,2,8,37327260),(4,1,8,25083948),(6,3,8,37097544),(8,1,8,24576564),(9,3,8,37097544),(12,2,8,26676156),(13,1,8,34440420),(16,1,8,37274772),(18,2,8,25048956)]),
  (13,[(1,3,8,25083948),(2,1,8,25108032),(3,2,8,25285260),(4,0,16,1116362306981660),(6,0,16,1354324841587500),(8,1,8,34440420),(9,0,16,1107651228766076),(12,7,8,37097544),(13,1,8,37327260),(16,3,8,24576564),(18,1,8,37629228)]),
  (16,[(1,3,8,34440420),(2,2,8,25107384),(3,1,8,25083948),(4,0,16,532312603772612),(6,0,16,1153479901828964),(8,1,8,37631172),(9,1,8,26702436),(12,3,8,32846016),(13,1,8,37327260),(16,1,8,24576564),(18,0,16,1491341708853052)]),
  (18,[(1,2,8,34440420),(2,1,8,25083948),(3,3,8,31458720),(4,0,16,1320697186905148),(6,1,8,34851108),(8,2,8,32193552),(9,1,8,37327260),(12,2,8,25108032),(13,1,8,37629228),(16,0,16,1320806377018788),(18,1,8,24576564)])]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 50000 in
private theorem c23 : Covered 23 t23 := by unfold Covered; decide +kernel

private def t67 : Table := [
  (9,[(1,1,8,34695840),(9,1,8,26676156),(14,1,8,25081104),(15,1,8,37355556),(22,1,8,37629228),(24,1,8,31458720),(25,0,16,529390831131776),(40,1,8,25108032),(59,1,8,34851108),(62,0,16,493478932065176),(64,0,16,1496818283909424)]),
  (14,[(1,1,8,34695840),(9,1,8,34846716),(14,1,8,26676156),(15,1,8,24589308),(22,1,8,24549996),(24,0,16,497560148820452),(25,1,8,34164372),(40,0,16,1058510163398324),(59,1,8,34400244),(62,0,16,1080630328035584),(64,0,16,1118102816382368)]),
  (15,[(1,1,8,34695840),(9,1,8,34873068),(14,1,8,31484640),(15,1,8,26676156),(22,0,16,1592231038410652),(24,1,8,32196144),(25,1,8,36998796),(40,0,16,1115515800557048),(59,0,16,1069773832965308),(62,1,8,32846016),(64,1,8,26702436)]),
  (22,[(1,1,8,37097544),(9,1,8,37629228),(14,1,8,24845232),(15,0,16,1115529722567840),(22,1,8,25285260),(24,0,16,1493648658270240),(25,0,16,1148417284728872),(40,0,16,494641729796024),(59,1,8,34873068),(62,1,8,25108032),(64,0,16,451712047712612)]),
  (24,[(1,1,8,34695840),(9,1,8,34400244),(14,0,16,1068674529709676),(15,1,8,34164372),(22,0,16,1107632027362028),(24,1,8,26676156),(25,1,8,24589308),(40,0,16,1069762396163924),(59,1,8,34846716),(62,0,16,1595269429585828),(64,2,8,24847428)]),
  (25,[(1,1,8,34695840),(9,0,16,1148194151133368),(14,1,8,32196144),(15,1,8,36998796),(22,0,16,460586113043396),(24,1,8,31484640),(25,1,8,26676156),(40,0,16,1157057083812656),(59,0,16,467353805254088),(62,0,16,1359215675091456),(64,1,8,31662516)]),
  (40,[(1,3,8,34695840),(9,2,8,25048956),(14,0,16,530911258336616),(15,0,16,535982250170540),(22,0,16,1492678946183704),(24,0,16,1415481749595168),(25,0,16,496758205019972),(40,3,8,26676156),(59,0,16,1069157128742804),(62,0,16,1415137904667700),(64,1,8,37274772)]),
  (59,[(1,1,8,34695840),(9,1,8,34851108),(14,1,8,31458720),(15,0,16,461891332678748),(22,1,8,31465308),(24,2,8,32193552),(25,0,16,1114427876080268),(40,0,16,451712052141284),(59,1,8,26676156),(62,0,16,1072033461115796),(64,0,16,440250843028928)]),
  (62,[(1,3,8,34695840),(9,0,16,489945010677536),(14,0,16,1088653290006404),(15,1,8,37274772),(22,1,8,25048956),(24,0,16,1056770262816980),(25,0,16,1355831930623272),(40,0,16,1107649408576520),(59,0,16,1115529921837536),(62,3,8,26676156),(64,0,16,489556459266464)]),
  (64,[(1,1,8,34695840),(9,0,16,535320364540448),(14,0,16,1088259602030348),(15,1,8,26702436),(22,0,16,1500382922300152),(24,1,8,25081104),(25,1,8,37355556),(40,1,8,32846016),(59,0,16,1147116373915700),(62,0,16,441273002652776),(64,2,8,37631172)])]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 50000 in
private theorem c67 : Covered 67 t67 := by unfold Covered; decide +kernel

private def t89 : Table := [
  (2,[(1,2,8,34695840),(2,3,8,24904308),(4,0,16,451721386908920),(8,1,8,31487592),(16,1,8,25973724),(32,0,16,498731376484676),(39,0,16,1469927677455448),(45,0,16,1592786205618648),(64,0,16,500143889269004),(67,1,8,25973724),(78,1,8,31487592)]),
  (4,[(1,1,8,34695840),(2,0,16,1114410700274576),(4,1,8,26676156),(8,1,8,37097544),(16,1,8,37274772),(32,0,16,496721657684516),(39,0,16,439236719497544),(45,1,8,25285260),(64,0,16,450923580385076),(67,1,8,25048956),(78,0,16,1496068094506380)]),
  (8,[(1,1,8,34695840),(2,1,8,24576564),(4,1,8,34440420),(8,1,8,26676156),(16,1,8,25083948),(32,0,16,1355167528981224),(39,0,16,534839963137976),(45,1,8,37327260),(64,0,16,454347999619652),(67,0,16,1493129248392796),(78,0,16,1469844949609708)]),
  (16,[(1,1,8,34695840),(2,1,8,37631172),(4,1,8,32846016),(8,2,8,25107384),(16,1,8,26676156),(32,0,16,497132694910316),(39,0,16,1148301768359768),(45,0,16,464087031926576),(64,0,16,1490153345754316),(67,0,16,1069617293356196),(78,0,16,1606812377014680)]),
  (32,[(1,1,8,34695840),(2,0,16,497853071895920),(4,0,16,1069479586053452),(8,0,16,1355555702540860),(16,0,16,1070797462833344),(32,1,8,26676156),(39,0,16,1495583877019624),(45,0,16,1607082408103704),(64,0,16,1470215919283288),(67,0,16,539546512516544),(78,0,16,1412308901269140)]),
  (39,[(1,1,8,34695840),(2,0,16,1069479630228668),(4,0,16,532325986073660),(8,0,16,437684256747176),(16,0,16,1313069375121612),(32,0,16,1389795955910116),(39,1,8,26676156),(45,2,8,25285260),(64,0,16,1317196972175992),(67,1,8,37629228),(78,1,8,37097544)]),
  (45,[(1,3,8,32570400),(2,0,16,1056905639742488),(4,1,8,25088340),(8,1,8,37333848),(16,0,16,1412606630175432),(32,0,16,451817984807348),(39,1,8,25088340),(45,2,8,26676156),(64,0,16,467383536461480),(67,0,16,1592702455833556),(78,1,8,37333848)]),
  (64,[(1,1,8,34695840),(2,0,16,452960180672864),(4,0,16,1317427708977960),(8,0,16,1608032591837484),(16,0,16,1085027588249636),(32,0,16,1321450461928464),(39,0,16,466183750864556),(45,0,16,1058369386622060),(64,1,8,26676156),(67,0,16,460756254648884),(78,0,16,1318165816012648)]),
  (67,[(1,1,8,34695840),(2,2,8,37631172),(4,1,8,37274772),(8,0,16,1068646618427384),(16,0,16,497566181735408),(32,0,16,1401621562745916),(39,1,8,25048956),(45,0,16,1079974851296360),(64,0,16,1389910447381128),(67,1,8,26676156),(78,1,8,25107384)]),
  (78,[(1,1,8,34695840),(2,1,8,24576564),(4,0,16,1085027204020316),(8,0,16,1115557832075900),(16,0,16,1470692963006872),(32,0,16,1470692194835632),(39,1,8,34440420),(45,1,8,37327260),(64,0,16,489085662373184),(67,1,8,25083948),(78,1,8,26676156)])]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 50000 in
private theorem c89 : Covered 89 t89 := by unfold Covered; decide +kernel

private def t199 : Table := [
  (18,[(1,1,8,34695840),(18,1,8,26676156),(61,1,8,34853304),(62,1,8,32552904),(63,0,16,1363071683687280),(103,1,8,26681988),(114,0,16,497712051212828),(121,1,8,34469004),(125,0,16,1115245327465580),(139,0,16,500410805025740),(188,0,16,1500754782304564)]),
  (61,[(1,1,8,24847428),(18,1,8,31460916),(61,3,8,34846716),(62,2,8,31460916),(63,1,8,34164372),(103,1,8,31460916),(114,1,8,31460916),(121,2,8,31460916),(125,1,8,31460916),(139,1,8,31460916),(188,1,8,31460916)]),
  (62,[(1,2,8,24549996),(18,1,8,34141692),(61,2,8,34400244),(62,2,8,34164372),(63,1,8,34141692),(103,1,8,34141692),(114,1,8,34141692),(121,1,8,34141692),(125,1,8,24847428),(139,1,8,34846716),(188,1,8,34141692)]),
  (63,[(1,1,8,34695840),(18,0,16,454630361544788),(61,1,8,34853304),(62,1,8,32552904),(63,1,8,26676156),(103,0,16,1355303127143004),(114,0,16,1467152723179032),(121,0,16,490241031825740),(125,1,8,31662516),(139,0,16,1496100378478660),(188,0,16,1107742415734280)]),
  (103,[(1,1,8,34695840),(18,1,8,34469004),(61,1,8,34853304),(62,1,8,32552904),(63,0,16,440240959699448),(103,1,8,26676156),(114,1,8,26681988),(121,0,16,460570846693448),(125,0,16,1146879268494284),(139,0,16,1385952469920636),(188,0,16,460441649673164)]),
  (114,[(1,1,8,34695840),(18,0,16,1355869530146140),(61,1,8,34853304),(62,1,8,32552904),(63,0,16,1118057461584500),(103,1,8,34469004),(114,1,8,26676156),(121,0,16,489839910779612),(125,0,16,1386051588991348),(139,0,16,1072032286435304),(188,1,8,26681988)]),
  (121,[(1,1,8,34695840),(18,1,8,26681988),(61,2,8,34853304),(62,1,8,32552904),(63,0,16,1317320152796184),(103,0,16,1493601014112252),(114,0,16,1355822659162140),(121,1,8,26676156),(125,0,16,1607105087867832),(139,1,8,34873068),(188,0,16,1116406264949744)]),
  (125,[(1,1,8,34695840),(18,0,16,1078248848822060),(61,1,8,34853304),(62,1,8,32552904),(63,1,8,37355556),(103,0,16,1604657924320264),(114,0,16,500384506070804),(121,0,16,498940934903420),(125,1,8,26676156),(139,0,16,439065870007640),(188,1,8,34469004)]),
  (139,[(1,1,8,34695840),(18,0,16,1152555717096500),(61,2,8,34853304),(62,2,8,32552904),(63,0,16,1148289430424468),(103,0,16,454675855580264),(114,0,16,497856082301444),(121,1,8,26681988),(125,0,16,1398766123217176),(139,1,8,26676156),(188,0,16,497572048571672)]),
  (188,[(1,1,8,34695840),(18,0,16,452088791580476),(61,1,8,34853304),(62,1,8,32552904),(63,0,16,1618487156949496),(103,0,16,536011511007728),(114,1,8,34469004),(121,0,16,452976442671584),(125,1,8,26681988),(139,0,16,1412312448171940),(188,1,8,26676156)])]

set_option maxHeartbeats 5000000 in
set_option maxRecDepth 50000 in
private theorem c199 : Covered 199 t199 := by unfold Covered; decide +kernel


set_option maxRecDepth 5000 in
/-- Every normalized scalar pair has a balanced simple alternating walk
of length 16 or 32. This theorem concerns the four listed prime fields. -/
theorem normalized (q : ℕ) (hq : q=23 ∨ q=67 ∨ q=89 ∨ q=199)
    (a b : ZMod q) (ha : orderOf a = 11) (hb : b^11=1) :
    ∃ z w, BalancedCycle (forward a b) (backward a⁻¹ b⁻¹) z w := by
  have pa : a^11=1 := ha ▸ pow_orderOf_eq_one a
  have ne : a≠1 := by rintro rfl; simp at ha
  rcases hq with rfl|rfl|rfl|rfl
  · let : Fact (Nat.Prime 23) := ⟨by decide⟩
    exact of_check 23 t23 a b pa hb (c23 a pa ne b hb)
  · let : Fact (Nat.Prime 67) := ⟨by decide⟩
    exact of_check 67 t67 a b pa hb (c67 a pa ne b hb)
  · let : Fact (Nat.Prime 89) := ⟨by decide⟩
    exact of_check 89 t89 a b pa hb (c89 a pa ne b hb)
  · let : Fact (Nat.Prime 199) := ⟨by decide⟩
    exact of_check 199 t199 a b pa hb (c199 a pa ne b hb)

end NonfreeEleven.SmallField
end

section
/- A balanced, vertex-simple alternating word lifts through independent constant translations
in an arbitrary abelian group. Codex, gpt-6.2-astra. -/

namespace NonfreeEleven.SmallField

open SimpleGraph

variable {F X : Type*} [AddCommGroup F]

def addForward (d : Label → F) (f : Label → X → X) (k : Label) (v : F × X) : F × X :=
  (v.1+d k,f k v.2)

def addBackward (d : Label → F) (g : Label → X → X) (k : Label) (v : F × X) : F × X :=
  (v.1-d k,g k v.2)

private theorem trace_translation (d : Label → F) (f g : Label → X → X)
    (u : F) (x : X) (w : Word) :
    let r := trace (addForward d f) (addBackward d g) (u,x) w
    let s := trace f g x w
    r.left.map Prod.snd = s.left ∧ r.right.map Prod.snd = s.right ∧
      r.endpoint.2 = s.endpoint ∧
      r.endpoint.1 = u + ((w.map Prod.fst).map d).sum - ((w.map Prod.snd).map d).sum := by
  induction w generalizing u x with
  | nil => simp [trace]
  | cons ij w ih =>
    rcases ij with ⟨i,j⟩
    obtain ⟨hl,hr,he,hu⟩ := ih (u+d i-d j) (g j (f i x))
    dsimp only [trace,addForward,addBackward]
    refine ⟨congrArg (List.cons x) hl, congrArg (List.cons (f i x)) hr, he, ?_⟩
    rw [hu]
    simp
    abel

/-- Label balance closes the first coordinate. Projection preserves simplicity. -/
theorem lift_balanced (d : Label → F) (f g : Label → X → X) (u : F) {x : X} {w : Word}
    (h : BalancedCycle f g x w) :
    BalancedCycle (addForward d f) (addBackward d g) (u,x) w := by
  obtain ⟨len,bal,stop,left,right⟩ := h
  obtain ⟨hl,hr,he,hu⟩ := trace_translation d f g u x w
  have same := ((List.perm_iff_count.mpr bal).map d).sum_eq
  refine ⟨len,bal,Prod.ext ?_ (he.trans stop),List.Nodup.of_map Prod.snd (hl ▸ left),
    List.Nodup.of_map Prod.snd (hr ▸ right)⟩
  rw [same] at hu
  simpa using hu

private def vertices (f g : Label → X → X) (x : X) : Word → List (Bool × X)
  | [] => []
  | (i,j)::w => (false,x)::(true,f i x)::vertices f g (g j (f i x)) w

private theorem mem_vertices (f g : Label → X → X) (x z : X) (w : Word) :
    ((false,z) ∈ vertices f g x w ↔ z ∈ (trace f g x w).left) ∧
    ((true,z) ∈ vertices f g x w ↔ z ∈ (trace f g x w).right) := by
  induction w generalizing x with
  | nil => simp [vertices,trace]
  | cons ij w ih =>
    rcases ij with ⟨i,j⟩
    obtain ⟨hl,hr⟩ := ih (g j (f i x))
    simp [vertices,trace,hl,hr]

private theorem nodup_vertices (f g : Label → X → X) (x : X) (w : Word)
    (left : (trace f g x w).left.Nodup) (right : (trace f g x w).right.Nodup) :
    (vertices f g x w).Nodup := by
  induction w generalizing x with
  | nil => simp [vertices]
  | cons ij w ih =>
    rcases ij with ⟨i,j⟩
    obtain ⟨hl,ls⟩ := List.nodup_cons.mp left
    obtain ⟨hr,rs⟩ := List.nodup_cons.mp right
    exact List.nodup_cons.mpr ⟨by
      intro hm
      rcases List.mem_cons.mp hm with hit|later
      · exact Bool.noConfusion (congrArg Prod.fst hit)
      · exact hl ((mem_vertices f g _ _ w).1.mp later),
      List.nodup_cons.mpr ⟨fun hx => hr ((mem_vertices f g _ _ w).2.mp hx),ih _ ls rs⟩⟩

section Walk
variable (f g : Label → X → X) (G : SimpleGraph (Bool × X))
  (edge : ∀ k x, G.Adj (false,x) (true,f k x))
  (inv : ∀ k x, f k (g k x) = x)

private def asWalk (x : X) : (w : Word) →
    G.Walk (false,x) (false,(trace f g x w).endpoint)
  | [] => .nil
  | (i,j)::w => .cons (edge i x) (.cons
      (show G.Adj (true,f i x) (false,g j (f i x)) by
        simpa only [inv] using (edge j (g j (f i x))).symm)
      (asWalk (g j (f i x)) w))

private theorem asWalk_info (x : X) (w : Word) :
    let p := asWalk f g G edge inv x w
    p.length = 2*w.length ∧ p.support = vertices f g x w ++ [(false,(trace f g x w).endpoint)] := by
  induction w generalizing x with
  | nil => simp [asWalk,vertices,trace]
  | cons ij w ih =>
    rcases ij with ⟨i,j⟩
    obtain ⟨hl,hs⟩ := ih (g j (f i x))
    simp [asWalk,vertices,trace,hl,hs,Nat.mul_add]

include edge inv in
/-- Convert a balanced alternating word to actual containment of the ordinary cycle graph. -/
theorem graph_of_balanced (x : X) (w : Word) (ok : BalancedCycle f g x w) :
    cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  obtain ⟨size,_,closed,left,right⟩ := ok
  let p := asWalk f g G edge inv x w
  let c := p.copy rfl (congrArg (Prod.mk false) closed)
  obtain ⟨len,supp⟩ := asWalk_info f g G edge inv x w
  have length : c.length = 2*w.length := by simpa [c,p] using len
  have large : 3 ≤ c.length := by omega
  have nn : ¬c.Nil := fun h => by have := h.length_eq_zero; omega
  have distinct : c.support.dropLast.Nodup := by
    dsimp [c,p]
    rw [Walk.support_copy,supp]
    simpa using nodup_vertices f g x w left right
  have cycle : c.IsCycle := Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨by
    rw [Walk.isPath_def,c.support_tail_of_not_nil nn]
    exact c.tail_support_perm_dropLast_support.nodup_iff.mpr distinct,large⟩
  rcases size with h|h
  · exact Or.inl ((cycleGraph_isContained_iff (by decide)).mpr ⟨_,c,cycle,length.trans h⟩)
  · exact Or.inr ((cycleGraph_isContained_iff (by decide)).mpr ⟨_,c,cycle,length.trans h⟩)
end Walk

set_option maxRecDepth 5000 in
/-- The normalized small-field cycles survive arbitrary independent label translations
on an abelian coordinate. The graph may have additional edges. -/
theorem separated (q : ℕ) (hq : q=23 ∨ q=67 ∨ q=89 ∨ q=199)
    (a b : ZMod q) (ha : orderOf a=11) (hb : b^11=1)
    (d : Label → F) (G : SimpleGraph (Bool × (F × ZMod q)))
    (edge : ∀ k x, G.Adj (false,x) (true,addForward d (forward a b) k x)) :
    cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  obtain ⟨x,w,ok⟩ := normalized q hq a b ha hb
  let prime : Fact q.Prime := ⟨by rcases hq with rfl|rfl|rfl|rfl <;> decide⟩
  have pa : a^11=1 := ha ▸ pow_orderOf_eq_one a
  have na : a≠0 := fun h => by simp [h] at pa
  have nb : b≠0 := fun h => by simp [h] at hb
  apply graph_of_balanced (addForward d (forward a b)) (addBackward d (backward a⁻¹ b⁻¹)) G edge
    _ (0,x) w (lift_balanced d _ _ 0 ok)
  rintro k ⟨v,z⟩
  apply Prod.ext
  · simp [addForward,addBackward]
  · change forward a b k (backward a⁻¹ b⁻¹ k z) = z
    by_cases h : k=0
    · simp [h,forward,backward]
    by_cases h' : k=1 <;> simp [h,h',forward,backward,na,nb]

end NonfreeEleven.SmallField
end

section
/- # Nilpotence of the displacement operator on the 121-element moving subgroup -/
namespace NonfreeEleven

private theorem fixed_card_congr {A : Type*} [AddCommGroup A] [Finite A]
    (U : A →+ A) (period : ∀ x : A,U^[11] x=x) :
    Nat.card A ≡ Nat.card (U-AddMonoidHom.id A).ker [MOD 11] := by
  classical
  let _ := Fintype.ofFinite A
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let u : Function.End A := fun x => U x
  have ep : u^11^1=1 := by
    rw [pow_one]
    funext x
    exact period x
  let e : u.fixedPoints ≃ (U-AddMonoidHom.id A).ker := {
    toFun y := ⟨y.val,sub_eq_zero.mpr y.property⟩
    invFun y := ⟨y.val,sub_eq_zero.mp y.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [← Nat.card_congr e,Nat.card_eq_fintype_card,Nat.card_eq_fintype_card]
  exact Equiv.Perm.card_fixedPoints_modEq ep

private theorem displacement_zero_small {A : Type*} [AddCommGroup A] [Finite A]
    (U : A →+ A) (period : ∀ x : A,U^[11] x=x) (size : Nat.card A=1 ∨ Nat.card A=11) :
    ∀ x : A, U x=x := by
  let D := U-AddMonoidHom.id A
  have prod : Nat.card D.ker*Nat.card D.range=Nat.card A := by
    rw [← AddSubgroup.index_ker,D.ker.card_mul_index]
  have cong := fixed_card_congr U period
  change Nat.card A%11=Nat.card D.ker%11 at cong
  have hk : 0<Nat.card D.ker := Nat.card_pos
  have hr : 0<Nat.card D.range := Nat.card_pos
  have one : Nat.card D.range=1 := by
    rcases size with sz|sz
    · rw [sz] at prod
      exact Nat.eq_one_of_mul_eq_one_left prod
    · rw [sz] at prod cong
      have div : Nat.card D.range ∣ 11 := ⟨Nat.card D.ker,by simpa only [Nat.mul_comm] using prod.symm⟩
      rcases (Nat.dvd_prime (by decide : Nat.Prime 11)).mp div with good|bad
      · exact good
      · rw [bad] at prod
        omega
  let _ : Subsingleton D.range := (Nat.card_eq_one_iff_unique.mp one).1
  intro x
  have z : D.rangeRestrict x=0 := Subsingleton.elim _ _
  exact sub_eq_zero.mp (congrArg (fun a : D.range => (a:A)) z)

/-- On a finite abelian group of order eleven squared, every period-eleven
endomorphism satisfies (U−1)²=0. -/
theorem displacement_sq_of_121 {A : Type*} [AddCommGroup A] [Finite A]
    (U : A →+ A) (period : ∀ x : A,U^[11] x=x) (size : Nat.card A=121) :
    ∀ x : A,U (U x-x)=U x-x := by
  let D := U-AddMonoidHom.id A
  let M := D.range
  let S : M →+ M := {
    toFun y := ⟨U y,by
      obtain ⟨x,h⟩ := y.property
      refine ⟨U x,?_⟩
      rw [← h]
      exact (map_sub U (U x) x).symm⟩
    map_zero' := Subtype.ext (map_zero U)
    map_add' := fun x y => Subtype.ext (map_add U _ _) }
  have sem : Function.Semiconj (fun x : M => (x:A)) S U := fun _ => rfl
  have sp (x : M) : S^[11] x=x := Subtype.ext ((sem.iterate_right 11 x).trans (period _))
  have prod : Nat.card D.ker*Nat.card M=121 := by
    change Nat.card D.ker*Nat.card D.range=121
    rw [← AddSubgroup.index_ker,D.ker.card_mul_index,size]
  have div : Nat.card M ∣ 11^2 := ⟨Nat.card D.ker,by rw [Nat.mul_comm]; exact prod.symm⟩
  have cong := fixed_card_congr U period
  change Nat.card A%11=Nat.card D.ker%11 at cong
  rw [size] at cong
  obtain ⟨k,hk,eq⟩ := (Nat.dvd_prime_pow (by decide : Nat.Prime 11)).mp div
  have small : Nat.card M=1 ∨ Nat.card M=11 := by
    interval_cases k
    · exact Or.inl eq
    · exact Or.inr eq
    · rw [eq] at prod
      have equal : Nat.card D.ker*121=1*121 := prod
      have one := Nat.eq_of_mul_eq_mul_right (by decide : 0<121) equal
      rw [one] at cong
      contradiction
  intro x
  exact congrArg (fun z : M => (z:A)) (displacement_zero_small S sp small (D.rangeRestrict x))

/-- In a moving subgroup of size 121 all elements are killed by eleven,
and (T−1) cubed vanishes on the entire abelian group. -/
theorem moving_121_exponent {V : Type*} [AddCommGroup V] [Finite V]
    (T : V →+ V) (period : ∀ x : V,T^[11] x=x)
    (size : Nat.card (T-AddMonoidHom.id V).range=121) (x : V) :
    11 • (T x-x)=0 ∧ T (T (T x-x)-(T x-x))=T (T x-x)-(T x-x) := by
  let D := T-AddMonoidHom.id V
  let M := D.range
  let S : M →+ M := {
    toFun y := ⟨T y,by
      obtain ⟨v,h⟩ := y.property
      refine ⟨T v,?_⟩
      rw [← h]
      exact (map_sub T (T v) v).symm⟩
    map_zero' := Subtype.ext (map_zero T)
    map_add' := fun u v => Subtype.ext (map_add T _ _) }
  have sem : Function.Semiconj (fun z : M => (z:V)) S T := fun _ => rfl
  have sp (z : M) : S^[11] z=z := Subtype.ext ((sem.iterate_right 11 z).trans (period _))
  let b : V := T x-x
  let c : V := T b-b
  have tc : T c=c := congrArg (fun z : M => (z:V))
    (displacement_sq_of_121 S sp size (D.rangeRestrict x))
  have tx : T x=x+b := by dsimp [b]; abel
  have tb : T b=b+c := by dsimp [c]; abel
  have orbit (n : ℕ) : T^[n] x=x+n • b+n.choose 2 • c := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply',ih,map_add,map_add,map_nsmul,map_nsmul,tx,tb,tc]
      rw [Nat.choose_succ_succ,Nat.choose_one_right,add_nsmul,add_nsmul,nsmul_add]
      simp only [one_nsmul]
      abel
  have linear (n : ℕ) : T^[n] b=b+n • c := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply',ih,map_add,tb,map_nsmul,tc,add_nsmul,one_nsmul]
      abel
  have cc : 11 • c=0 := by
    have he := (linear 11).symm.trans (period b)
    exact add_left_cancel (he.trans (add_zero b).symm)
  have c55 : 55 • c=0 := by
    rw [show 55=11*5 by decide,mul_nsmul,cc,nsmul_zero]
  have bb := (orbit 11).symm.trans (period x)
  rw [show Nat.choose 11 2=55 by decide,c55,add_zero] at bb
  exact ⟨add_left_cancel (bb.trans (add_zero x).symm),tc⟩


end NonfreeEleven
end

section
/- # A 32-letter identity in every group of nilpotency class at most three

The Hall coordinate collection and the lower-central-series argument below are from the
earlier ClassThreeRegular proof. The word 01010102101201012010121021202012 was recorded
by the class-three search as its positive projection to class two. Its reversed signed
product acts on the left along the matching walk. Codex, gpt-6.2-astra.
-/

namespace NonfreeEleven.ClassThreeWord
open SimpleGraph

/-- Hall coordinates for the integral free two-generator group of nilpotency class three.
The normal form is b^y a^x c^z d^u e^v, with ab=bac, ca=acd and cb=bce. -/
structure Hall where
  x : ℤ
  y : ℤ
  z : ℤ
  u : ℤ
  v : ℤ
  deriving DecidableEq, Repr

/-- Equality in Hall coordinates is coordinatewise. -/
theorem Hall.ext {a b : Hall} (hx : a.x=b.x) (hy : a.y=b.y) (hz : a.z=b.z)
    (hu : a.u=b.u) (hv : a.v=b.v) : a=b := by
  cases a
  cases b
  simp_all

def tri (n : ℤ) := n*(n-1)/2
lemma twice_tri (n : ℤ) : 2*tri n = n*(n-1) := by
  have dv : 2 ∣ n*(n-1) := by
    rcases Int.even_or_odd n with ⟨a,ha⟩ | ⟨a,ha⟩
    · exact ⟨a*(n-1),by rw [ha]; ring⟩
    · exact ⟨n*a,by rw [ha]; ring⟩
  exact Int.mul_ediv_cancel' dv

lemma tri_add (m n : ℤ) : tri (m+n) = tri m + tri n + m*n := by
  nlinarith only [twice_tri (m+n),twice_tri m,twice_tri n]

lemma tri_neg (n : ℤ) : tri (-n) = tri n + n := by
  nlinarith only [twice_tri (-n),twice_tri n]

instance hMul : Mul Hall := ⟨fun g h =>
  ⟨g.x+h.x,g.y+h.y,g.z+h.z+g.x*h.y,
    g.u+h.u+h.y*tri g.x+h.x*(g.z+g.x*h.y),
    g.v+h.v+h.y*g.z+g.x*tri h.y⟩⟩

instance hOne : One Hall := ⟨⟨0,0,0,0,0⟩⟩
instance hInv : Inv Hall := ⟨fun g =>
  ⟨-g.x,-g.y,-g.z+g.x*g.y,
   -g.u+g.y*tri g.x+g.x*(g.z-g.x*g.y),
   -g.v+g.y*g.z-g.x*tri (-g.y)⟩⟩

lemma mul_mk (g h : Hall) : g*h =
  ⟨g.x+h.x,g.y+h.y,g.z+h.z+g.x*h.y,
    g.u+h.u+h.y*tri g.x+h.x*(g.z+g.x*h.y),
    g.v+h.v+h.y*g.z+g.x*tri h.y⟩ := rfl
lemma one_mk : (1 : Hall) = ⟨0,0,0,0,0⟩ := rfl
lemma inv_mk (g : Hall) : g⁻¹ =
  ⟨-g.x,-g.y,-g.z+g.x*g.y,
   -g.u+g.y*tri g.x+g.x*(g.z-g.x*g.y),
   -g.v+g.y*g.z-g.x*tri (-g.y)⟩ := rfl

lemma tri_zero : tri 0 = 0 := rfl
instance : Group Hall where
  mul := (·*·)
  one := 1
  inv := Inv.inv
  mul_assoc g h k := by apply Hall.ext <;> simp only [mul_mk,tri_add] <;> ring
  one_mul g := by apply Hall.ext <;> simp [mul_mk,one_mk,tri_zero]
  mul_one g := by apply Hall.ext <;> simp [mul_mk,one_mk,tri_zero]
  inv_mul_cancel g := by
    apply Hall.ext <;> simp [mul_mk,inv_mk,one_mk,tri_neg]
    all_goals nlinarith only [congrArg (fun q : ℤ => g.y*q) (twice_tri g.x),
      congrArg (fun q : ℤ => g.x*q) (twice_tri g.y)]

def X : Hall := ⟨1,0,0,0,0⟩
def Y : Hall := ⟨0,1,0,0,0⟩
def C : Hall := ⟨0,0,1,0,0⟩
def D : Hall := ⟨0,0,0,1,0⟩
def E : Hall := ⟨0,0,0,0,1⟩

variable {A : Type*} [Group A] (φ : Hall →* A)

lemma tri_succ (n : ℤ) : tri (n+1) = tri n+n := by
  rw [tri_add]; change tri n+0+n*1=tri n+n; ring

lemma collect_class_two (a b c : A) (ab : a*b = b*a*c) (ac : Commute a c) (bc : Commute b c)
    (x y : ℤ) : a^x*b^y = b^y*a^x*c^(x*y) := by
  have hr : SemiconjBy b (a*c) a := by simpa only [SemiconjBy,mul_assoc] using ab.symm
  have hh := (hr.zpow_right x).eq.symm
  rw [ac.mul_zpow] at hh
  have hx : SemiconjBy (a^x) b (b*c^x) := by
    change a^x*b = b*c^x*a^x
    rw [hh,mul_assoc,(ac.zpow_zpow x x).symm.eq]
  have hy := (hx.zpow_right y).eq
  rw [(bc.zpow_right x).mul_zpow, ← zpow_mul] at hy
  calc
    a^x*b^y = b^y*c^(x*y)*a^x := hy
    _ = b^y*a^x*c^(x*y) := by rw [mul_assoc,(ac.zpow_zpow x (x*y)).symm.eq,mul_assoc]

lemma collect_a_power_b (a b c d : A) (ab : a*b=b*a*c) (ca : c*a=a*c*d)
    (dc : ∀ t : A, Commute d t) (n : ℤ) :
    a^n*b = b*a^n*c^n*d^tri n := by
  have shift (i : ℤ) : c^i*a=a*c^i*d^i := by
    simpa using collect_class_two c a d ca (dc c).symm (dc a).symm i 1
  have step (i : ℤ) :
      a^(i+1)*b = b*a^(i+1)*c^(i+1)*d^tri (i+1) ↔
      a^i*b = b*a^i*c^i*d^tri i := by
    have left : a^(i+1)*b=(a^i*b)*(a*c) := by
      rw [zpow_add_one,mul_assoc,ab]
      simp only [mul_assoc]
    have right : b*a^(i+1)*c^(i+1)*d^tri (i+1) = (b*a^i*c^i*d^tri i)*(a*c) := by
      have c1 := ((dc (a*c)).zpow_left (tri i)).eq
      have c2 := ((dc c).zpow_left i).eq
      symm
      calc
        _ = (b*a^i)*(c^i*a)*c*d^tri i := by
          simpa only [mul_assoc] using congrArg (fun t => b*a^i*c^i*t) c1
        _ = (b*a^i)*(a*c^i*d^i)*c*d^tri i := by rw [shift i]
        _ = b*a^(i+1)*c^(i+1)*d^tri (i+1) := by
          rw [zpow_add_one,zpow_add_one,tri_succ,add_comm (tri i),zpow_add]
          simpa only [mul_assoc] using congrArg (fun t => b*a^i*a*c^i*t*d^tri i) c2
    rw [left,right,mul_left_inj]
  induction n using Int.induction_on with
  | zero => simp [tri_zero]
  | succ k ih => exact (step _).mpr ih
  | pred k ih =>
    apply (step _).mp
    simpa using ih

def evalFn (a b c d e : A) (g : Hall) :=
  b^g.y * a^g.x * c^g.z * (d^g.u*e^g.v)

lemma axisHall (x y z u v : ℤ) (h : (x,y,z,u,v)=(1,0,0,0,0) ∨
    (x,y,z,u,v)=(0,1,0,0,0) ∨ (x,y,z,u,v)=(0,0,1,0,0) ∨
    (x,y,z,u,v)=(0,0,0,1,0) ∨ (x,y,z,u,v)=(0,0,0,0,1)) (n : ℤ) :
    (⟨x,y,z,u,v⟩ : Hall)^n = ⟨n*x,n*y,n*z,n*u,n*v⟩ := by
  let f (k : ℤ) : Hall := ⟨k*x,k*y,k*z,k*u,k*v⟩
  have f1 : f 1 = ⟨x,y,z,u,v⟩ := by simp [f]
  have adds (i j : ℤ) : f (i+j)=f i*f j := by
    rcases h with h|h|h|h|h <;> simp only [Prod.mk.injEq] at h <;>
      obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := h <;>
      apply Hall.ext <;> simp [f,mul_mk,tri_zero]
  let F : Multiplicative ℤ →* Hall := {
    toFun t := f t.toAdd
    map_one' := by simp [f,one_mk]
    map_mul' := fun i j => adds _ _ }
  have eq := map_zpow F (Multiplicative.ofAdd 1) n
  change f (n • (1:ℤ)) = (f 1)^n at eq
  simpa [f] using eq.symm


lemma factors (g : Hall) : Y^g.y*X^g.x*C^g.z*D^g.u*E^g.v=g := by
  have hx := axisHall 1 0 0 0 0 (by decide) g.x
  have hy := axisHall 0 1 0 0 0 (by decide) g.y
  have hz := axisHall 0 0 1 0 0 (by decide) g.z
  have hu := axisHall 0 0 0 1 0 (by decide) g.u
  have hv := axisHall 0 0 0 0 1 (by decide) g.v
  unfold X Y C D E
  rw [hx,hy,hz,hu,hv]
  apply Hall.ext <;> simp [mul_mk,tri_zero]

lemma telescope {F : Hall → A} (s : Hall) (q : A) (move : ∀ g,F (g*s)=F g*q)
    (g : Hall) (n : ℤ) : F (g*s^n)=F g*q^n := by
  have step (k : ℤ) : F (g*s^(k+1))=F g*q^(k+1) ↔ F (g*s^k)=F g*q^k := by
    rw [zpow_add_one,zpow_add_one,←mul_assoc,move,←mul_assoc,mul_left_inj]
  induction n using Int.induction_on with
  | zero => simp
  | succ k ih => exact (step _).mpr ih
  | pred k ih => apply (step _).mp; simpa using ih

lemma central_slide (d : A) (hd : ∀ x, Commute d x) (k : ℤ) (s t : A) :
    d^k*(s*t)=s*(d^k*t) := by rw [←mul_assoc,((hd s).zpow_left k).eq,mul_assoc]

lemma extend_letters (a b c d e : A)
    (ab : a*b=b*a*c) (ca : c*a=a*c*d) (cb : c*b=b*c*e)
    (hd : ∀ t : A, Commute d t) (he : ∀ t : A, Commute e t) :
    ∀ g : Hall,
      evalFn a b c d e (g*X) = evalFn a b c d e g*a ∧
      evalFn a b c d e (g*Y) = evalFn a b c d e g*b ∧
      evalFn a b c d e (g*C) = evalFn a b c d e g*c ∧
      evalFn a b c d e (g*D) = evalFn a b c d e g*d ∧
      evalFn a b c d e (g*E) = evalFn a b c d e g*e := by
  intro g
  let tail := d^g.u*e^g.v
  have tc (t : A) : Commute tail t :=
    ((hd t).zpow_left g.u).mul_left ((he t).zpow_left g.v)
  have shiftA : c^g.z*a=a*c^g.z*d^g.z := by
    simpa using collect_class_two c a d ca (hd c).symm (hd a).symm g.z 1
  have shiftB : c^g.z*b=b*c^g.z*e^g.z := by
    simpa using collect_class_two c b e cb (he c).symm (he b).symm g.z 1
  have right (t : A) : evalFn a b c d e g*t=b^g.y*a^g.x*(c^g.z*t)*tail := by
    simpa only [evalFn,tail,mul_assoc] using congrArg (fun w => b^g.y*a^g.x*c^g.z*w) (tc t).eq
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [right,shiftA]
    simp [evalFn,X,mul_mk,tri_zero,zpow_add,tail,mul_assoc]
    rw [(Commute.zpow_zpow_self d g.z g.u).left_comm]
  · rw [right,shiftB]
    have hb := collect_a_power_b a b c d ab ca hd g.x
    have h2 : b^g.y*a^g.x*(b*c^g.z*e^g.z)*tail =
        b^g.y*(b*a^g.x*c^g.x*d^tri g.x)*c^g.z*e^g.z*tail := by
      rw [←hb]; simp only [mul_assoc]
    rw [h2]
    have zz : g.z+g.x=g.x+g.z := add_comm _ _
    have uu : g.u+tri g.x=tri g.x+g.u := add_comm _ _
    have vv : g.v+g.z=g.z+g.v := add_comm _ _
    simp [evalFn,Y,mul_mk,show tri 1=0 from rfl,zz,uu,vv,zpow_add,tail,mul_assoc]
    rw [central_slide d hd (tri g.x) (c^g.z), central_slide e he g.z (d^g.u)]
  · rw [right]
    simp [evalFn,C,mul_mk,tri_zero,zpow_add_one,tail,mul_assoc]
  · change _ = b^g.y*a^g.x*c^g.z*(d^g.u*e^g.v)*d
    simp [evalFn,D,mul_mk,tri_zero,zpow_add_one,mul_assoc,((he d).zpow_left g.v).eq]
  · simp [evalFn,E,mul_mk,tri_zero,zpow_add_one,mul_assoc]

def toGroup (a b c d e : A)
    (ab : a*b=b*a*c) (ca : c*a=a*c*d) (cb : c*b=b*c*e)
    (hd : ∀ t : A, Commute d t) (he : ∀ t : A, Commute e t) : Hall →* A where
  toFun := evalFn a b c d e
  map_one' := by simp [evalFn,one_mk]
  map_mul' g h := by
    let F := evalFn a b c d e
    have letters := extend_letters a b c d e ab ca cb hd he
    have letters' (u : Hall) : F (u*X)=F u*a ∧ F (u*Y)=F u*b ∧ F (u*C)=F u*c ∧
        F (u*D)=F u*d ∧ F (u*E)=F u*e := letters u
    have eq := congrArg (fun w => g*w) (factors h)
    change F (g*h)=F g * _
    rw [←eq]
    simp only [←mul_assoc]
    rw [telescope E e (fun u => (letters' u).2.2.2.2),telescope D d (fun u => (letters' u).2.2.2.1),
      telescope C c (fun u => (letters' u).2.2.1),telescope X a (fun u => (letters' u).1),
      telescope Y b (fun u => (letters' u).2.1)]
    simp [F,evalFn,mul_assoc]

open scoped commutatorElement

/-- The left-action product of the signed nonidentity steps of the displayed word. -/
theorem class_three_closed {A : Type*} [Group A] [Group.IsNilpotent A]
    (classBound : Group.nilpotencyClass A ≤ 3) (a b : A) :
    b⁻¹*a*b*b*a⁻¹*b*a*b⁻¹*a*a*b*a⁻¹*a⁻¹*b⁻¹*a*a*b⁻¹*a⁻¹*a⁻¹*a⁻¹=1 := by
  let c := ⁅a⁻¹,b⁻¹⁆
  let d := ⁅c⁻¹,a⁻¹⁆
  let e := ⁅c⁻¹,b⁻¹⁆
  have c1 : c ∈ (⊤ : Subgroup A).lowerCentralSeries 1 :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have bottom : (⊤ : Subgroup A).lowerCentralSeries 3=⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr classBound
  have center : (⊤ : Subgroup A).lowerCentralSeries 2 ≤ Subgroup.center A :=
    Subgroup.commutator_top_right_eq_bot_iff_le_center.mp bottom
  have third (v : A) (x : A) : Commute ⁅c⁻¹,v⁻¹⁆ x :=
    (Subgroup.mem_center_iff.mp (center (Subgroup.commutator_mem_commutator
      (((⊤ : Subgroup A).lowerCentralSeries 1).inv_mem c1) (Subgroup.mem_top _))) x).symm
  have ab : a*b=b*a*c := by dsimp [c,commutatorElement_def]; group
  have ca : c*a=a*c*d := by dsimp only [d,commutatorElement_def]; group
  have cb : c*b=b*c*e := by dsimp only [e,commutatorElement_def]; group
  let F := toGroup a b c d e ab ca cb (third a) (third b)
  have fa : F X=a := by simp [F,toGroup,evalFn,X]
  have fb : F Y=b := by simp [F,toGroup,evalFn,Y]
  have close : Y⁻¹*X*Y*Y*X⁻¹*Y*X*Y⁻¹*X*X*Y*X⁻¹*X⁻¹*Y⁻¹*X*X*Y⁻¹*X⁻¹*X⁻¹*X⁻¹=1 := by decide
  simpa only [map_mul,map_inv,map_one,fa,fb] using congrArg F close

end NonfreeEleven.ClassThreeWord
end

section
/- # A simple projection of the class-three 32-edge word over the field of eleven elements

The word is 01010102101201012010121021202012, with identity, a and b labeled 0, 1 and 2.
The point at each of the 32 times lives on one of the two sides according to its parity.
The packed witness table uses seven bits per point to hold x+11y in zero-based residues.
Codex, gpt-6.2-astra.
-/

namespace NonfreeEleven.Projected

def direction : Fin 12 → ZMod 11 × ZMod 11 := ![(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(0,1)]
def word : Fin 32 → Fin 3 := ![0,1,0,1,0,1,0,2,1,0,1,2,0,1,0,1,2,0,1,0,1,2,1,0,2,1,2,0,2,0,1,2]

def step (i j u v : ZMod 11) (c : Fin 3) (z : ZMod 11 × ZMod 11) : ZMod 11 × ZMod 11 :=
  (z.1+(![0,u,v] : Fin 3 → ZMod 11) c, z.2+(![0,i,j] : Fin 3 → ZMod 11) c*z.1)

/-- Positions indexed by a cyclic word, alternating between its two sides. -/
def SimplePath (i j u v : ZMod 11) (z : Fin 32 → ZMod 11 × ZMod 11) : Prop :=
  (∀ p q : Fin 32,p.val%2=q.val%2 → z p=z q → p=q) ∧
  ∀ k : Fin 32,if k.val%2=0 then z (k+1)=step i j u v (word k) (z k)
    else z k=step i j u v (word k) (z (k+1))

private def packed : Fin 12 → Fin 12 → ℕ := ![
  ![0,1575538120584609953895303776966257952779810490006108495556423828230,605339280439530725172782013509037018979267721460798770171733164032,799379149684301687916989865095135366195737295901261055827024101376,993419018929072650661197727055821874435465658530151856762295500800,1187458888173843613405405589016565947639688191259722550846454841344,1381498757424459098064469128368951239360197284687716673045863415808,1575538626669230060808676990329637747901865758245850970589025878016,1963617352989535917678619949445600334359556229390340300041262989441,1963618365158771986296922737860621260656222969117716797676310577152,799378441136317237808403549615066914615248591873882318841195184644,1170873566770992104608143599156656229637297981467668773040907633156],
  ![10133207365735946828604713889353973965520422305725262350729033990660,0,605328145954618947856433106173105727205465494116160213731456139264,5857683845614437642734312256269325346867688449690727190805870264578,993420131996017161924485199769465702383639678901762588972994084864,1187460001308757167789469745537084821027133245909066439720316518400,1381499870621501321647296640697970283268266660023066505024786219008,1575539739934241324749129663760758347011336661790776276521792651264,1769579609246981330614114219902913008403131014555760822111632179200,7215963031899372136364041638719973763109985274837271482911566676355,2157659347872415714401075956780385686448302645067459595140942086144,10511323076113846227065778733914023897875031077987748461463542710788],
  ![19473657988547719344343544658734684102433263248237671221132659180036,3910652725107112550247320100624724952887866427155807170970078266118,0,799369129008062260879867115213509426885411312034983224800117604352,993421245798894766181546572914999846271665986601186273130583506944,1187461115179558187246042094032641413418071413751923531238556909568,1381500983818543542445385508970033247349845468291010669720604327936,1575540853199252588667995215840329571141605674084666107180425232384,1769580722579916012495642270036018688442920969278816721222983041024,1963620591960625058718251977850030542862039731147732142934142042112,2157660461341288482524157395276427672490302898104095281486001160192,19651111017994037343757373664066900220272926136201877439019975197188],
  ![3328521780158483594949198738292945591254759166740078444226708685316,17720666535161588015087880878518770897033690043267419129028935795462,605330372558405264837275645406149819978663203283318171838833836032,0,993410111455670195949214510396704835528596296308836929816012079104,1187462228308676992866207108307492786807164106912570411811164471296,1381502097757313605022734541272464885180036385408579246635740381184,1575541967205946069207836779238035327089961853718536063563711463424,1769581835912896316772132983218319735694492508928355887157562654720,1963621705361528780957405199459825939428430113198035527887208398848,2157661574810206873042201496821031811436569251201097033817600114688,3505985944287780127119523417799680978576426291903089227749861376516],
  ![12468310835507547477000553606904236963952634192183846025176712397316,6245767328893682053562558237731241848350596391782078402614908797702,9939158285860624341113743477775054725977433020511653672611265642625,10133198154635498006619115058457324215210360756997049171897292423297,0,1187451094033421462970083052498005347086191307992629488309235957760,1381503210960150574606309662768413099055657945495962149495744315392,1575543080470957333126872308650455050034845190146104975220697022464,1769582949245830998653661033351425415734282463651411786268913516544,1963622818762478131117824139901700254951471969054270965213630382080,9375280637921241507295421500776791867741480574497965014563761946753,12645773886173720367416733327112035712326369040744249362281842098692],
  ![21808761459061002206597208844150388356842821445606268174427946926596,20055781138948157518424706136977465435697408298178592303345287938822,12274271776104557289969114527468053231897929224969187888472579375233,799372468740921758301343318200815372924825940157649895189607956480,993412338319697559942682647890365583650781274981007283881949609984,0,13251105068568103360681672945808081525840032391077876149466897055873,1575544193741763345831224124327243148840728200291588638459220541440,1769584063320539147472393487057899807165890544418461280867270868992,21420681719897701482450479617338998478486580717091697214713742410244,2157663801747952403762061307655639124062868054595287443901260316672,21986223395516620115032482657996698916507655133579454679096520622596],
  ![5663637498087730290203946023286776763381262347099752145947146502660,8580869686006061196340050788404920216418119310062921048748211684102,605333712829085477438663506373867759032403161076827348589982597120,799373582475830319437627997165514578572145538398435840600171692032,14997465005653569420350042876277420038499360432355169442714949255297,1187453321039136036810549590555192207153336136437632558539523571712,0,1575533059596651153412584337302176016912861094877211889228514148352,1769585176653519451749054177572421085614115663952463286352187047936,16168338167299716309976317014549696862005872065220180199130317979777,2157664915216825169121991213072942780376026670777700546209321926656,5841098321810362901136366790414300699432286285656687746784269976068],
  ![14803426553436748547118773817123573564566919069018802035254843851268,22390883496066331407181529142424778989553178908333196120606077207302,605334826496070620612285697658359187264140292214975246939858485248,799374695474805787580138775697690253368253568633952828156302147584,993414565189474047541765764543504743125032373233406651698719834112,1187454434168254842430884571788932186253667367613091472540141174784,1381494303882927250385183932694588871450468809399479885364604518400,0,1769574042582125426078563152199361820111148927104950818265761136640,1963626158965234925756549502815873844716563074231614297959431487488,2157666028685697934481921118489618168769302572817061458461547905024,14980886263696348763850126484128023496905462454095353802688596034052],
  ![24143877176248521060094453043050957211029581700350009878215505920516,10915984289792676324834990232616955344611587800790275434541204226822,605335940168804890176431479118173712385635934050631362831540633600,799375809209714348716423454662389458713651196980902824959046664192,993415678256418558805053237257148570771284423719900404180188479488,19861731856949220502248426731150206919852706782962386293887032361089,1381495417085764219947341910171207940939698118323899286406583107584,20249811595036838318848473663540035830575639909386065857602421522561,0,1963615024956015191658197374947075938509074179210234942967473586176,18715734601071663275993265281853351712728917846616189972568350916737,24321335773039202886307761618884762897525234662407322095275608392196],
  ![7798091647806700136091531016086703479921754186940606587986393874948,24725998099847106164517436824757027484618223870302086123823698133766,12662356170932971212064017750694171062858227337214640410018436432259,21808765608437621352212572781656316288235591503270371619016011677825,22002805478288182073257468995778249728032255445951942819135323373697,17720660563236073243588044032931072228592343510169480980054612361474,1381496530282806440767017889421488655118907571810723831960830296064,22584925086362344319560345348094851743523986381135211108181980741761,1769576269248086037394696111642069030035618158400853502213818236928,0,16556421347019841922249263807633409646003407623850070561996995805442,8176210698591263455790669739984220254950729054998967559610646675972],
  ![17138542271360200490846470426793003853957741531526179488530288787972,13251098894315178921187006556275422344719643593972359986688663077638,21808766823471610781584792194715109924340555026299833128584795111682,799378035943598378016806043885396928771888305202968943166539251712,993417905126195049167287886989026060276299128729077273520364666880,24531958837850695399136516439948796110809874814325024784278890741889,22584926300926959099043058790151553294571916568919626922108433187074,1575537513404218796889641460917218024956982421818282058932040318976,1769577382581020719276224161775179656463040883838255443227433058304,1963617251757868264057769526624785757495130487039011563289012682752,0,17315998641213136786361506302770419978226630020290276984828122644996],
  ![10187924340766157899882415838537468024820649692027048223400611856900,15494998128110647275621957887456900300237600147674580926434172289798,422909652640812261869551425922465946792276114271563172550421938176,635192596101346701599445537038200854656780118898574374601773711360,847475539561926769250605377360607789794592921948185908765987602432,1059758483022506836901765217683072289896900039066091459345285021696,3819435735024121244635811270847091892808156894691008300921919635585,1484324369943625492275661508139944934050477877985565663883300077568,4244001621945239899758511967387715597868028951178840820674042265729,4686809570639516514099666302967885692129718481715332491297178009858,7428245975363623178187064893916548419543268062678476104801724694915,0]]

private def packedPoint (r s : Fin 12) (k : Fin 32) : ZMod 11 × ZMod 11 :=
  let code := (packed r s >>> (7*k.val))%128
  ((code%11 : ℕ),(code/11 : ℕ))

set_option maxRecDepth 5000 in
set_option maxHeartbeats 20000000 in
private theorem table_valid (r : Fin 12) :
    ∀ s : Fin 12, r≠s → SimplePath (direction r).1 (direction r).2 (direction s).1 (direction s).2 (packedPoint r s) := by
  fin_cases r <;> unfold SimplePath <;> decide

/-- Every ordered pair of different projective directions admits the projected simple cycle. -/
theorem projected_normalized (r s : Fin 12) (ne : r≠s) :
    ∃ z : Fin 32 → ZMod 11 × ZMod 11, SimplePath (direction r).1 (direction r).2 (direction s).1 (direction s).2 z :=
  ⟨packedPoint r s,table_valid r s ne⟩

/-- Reinsert arbitrary nonzero scalar multiples of the two projective directions. -/
theorem projective_scaling
    (good : ∀ r s : Fin 12,r≠s → ∃ z : Fin 32 → ZMod 11 × ZMod 11,
      SimplePath (direction r).1 (direction r).2 (direction s).1 (direction s).2 z)
    (i j u v : ZMod 11) (det : i*v≠j*u) :
    ∃ z : Fin 32 → ZMod 11 × ZMod 11,SimplePath i j u v z := by
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  have directions : ∀ x y : ZMod 11,x≠0 ∨ y≠0 →
      ∃ n : Fin 12, ∃ k : ZMod 11,k≠0 ∧ x=k*(direction n).1 ∧ y=k*(direction n).2 := by decide
  have ij : i≠0 ∨ j≠0 := by by_contra! h; exact det (by simp [h.1,h.2])
  have uv : u≠0 ∨ v≠0 := by by_contra! h; exact det (by simp [h.1,h.2])
  obtain ⟨r,A,nA,hi,hj⟩ := directions i j ij
  obtain ⟨s,B,nB,hu,hv⟩ := directions u v uv
  have ne : r≠s := by
    rintro rfl
    apply det
    rw [hi,hj,hu,hv]
    ring
  obtain ⟨z,inz,walk⟩ := good r s ne
  let φ (w : ZMod 11 × ZMod 11) : ZMod 11 × ZMod 11 := (B*w.1,(A*B)*w.2)
  have inj : Function.Injective φ := by
    intro x y e
    exact Prod.ext (mul_left_cancel₀ nB (congrArg Prod.fst e))
      (mul_left_cancel₀ (mul_ne_zero nA nB) (congrArg Prod.snd e))
  have transform (c : Fin 3) (w : ZMod 11 × ZMod 11) :
      φ (step (direction r).1 (direction r).2 (direction s).1 (direction s).2 c w)=step i j u v c (φ w) := by
    rw [hi,hj,hu,hv]
    fin_cases c <;> apply Prod.ext <;> dsimp [φ,step] <;> ring
  refine ⟨fun k => φ (z k),fun p q h e => inz p q h (inj e),?_⟩
  intro k
  have h := walk k
  split <;> rename_i e <;> simp only [e,ite_true,ite_false] at h <;> exact (congrArg φ h).trans (transform _ _)

/-- The two additive constants in the vertical coordinates can be arbitrary. -/
theorem affine_constants (i j u v a b : ZMod 11) (det : i*v≠j*u)
    (good : ∃ z : Fin 32 → ZMod 11 × ZMod 11,SimplePath i j u v z) :
    let advance (c : Fin 3) (z : ZMod 11 × ZMod 11) :=
      (z.1+(![0,u,v] : Fin 3 → ZMod 11) c,
       z.2+(![0,i,j] : Fin 3 → ZMod 11) c*z.1+(![0,a,b] : Fin 3 → ZMod 11) c)
    ∃ z : Fin 32 → ZMod 11 × ZMod 11,
      (∀ p q : Fin 32,p.val%2=q.val%2 → z p=z q → p=q) ∧
      ∀ k : Fin 32,if k.val%2=0 then z (k+1)=advance (word k) (z k)
        else z k=advance (word k) (z (k+1)) := by
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  intro advance
  obtain ⟨z,inz,walk⟩ := good
  let H := i*v-j*u
  have nz : H≠0 := sub_ne_zero.mpr det
  let α := (b*u-a*v)/H
  let β := (i*b-j*a)/H
  have one : β*u=i*α+a := by
    dsimp only [α,β]
    field_simp [nz]
    dsimp only [H]; ring
  have two : β*v=j*α+b := by
    dsimp only [α,β]
    field_simp [nz]
    dsimp only [H]; ring
  let φ (w : ZMod 11 × ZMod 11) : ZMod 11 × ZMod 11 := (w.1+α,w.2+β*w.1)
  have inj : Function.Injective φ := by
    intro x y e
    have first : x.1=y.1 := add_right_cancel (congrArg Prod.fst e)
    have second : x.2+β*x.1=y.2+β*y.1 := congrArg Prod.snd e
    rw [first] at second
    exact Prod.ext first (add_right_cancel second)
  have transform (c : Fin 3) (w : ZMod 11 × ZMod 11) :
      φ (step i j u v c w)=advance c (φ w) := by
    fin_cases c <;> apply Prod.ext <;> dsimp [φ,step,advance]
    all_goals first | solve | ring | solve | linear_combination one | solve | linear_combination two
  refine ⟨fun k => φ (z k),fun p q h e => inz p q h (inj e),?_⟩
  intro k
  have h := walk k
  split <;> rename_i e <;> simp only [e,ite_true,ite_false] at h <;> exact (congrArg φ h).trans (transform _ _)


/-- For any invertible slope matrix and any additive vertical constants, the fixed
32-letter word has a closed trajectory with distinct vertices on either side. -/
theorem projected_simple (i j u v a b : ZMod 11) (det : i*v≠j*u) :
    let advance (c : Fin 3) (z : ZMod 11 × ZMod 11) :=
      (z.1+(![0,u,v] : Fin 3 → ZMod 11) c,
       z.2+(![0,i,j] : Fin 3 → ZMod 11) c*z.1+(![0,a,b] : Fin 3 → ZMod 11) c)
    ∃ z : Fin 32 → ZMod 11 × ZMod 11,
      (∀ p q : Fin 32,p.val%2=q.val%2 → z p=z q → p=q) ∧
      ∀ k : Fin 32,if k.val%2=0 then z (k+1)=advance (word k) (z k)
        else z k=advance (word k) (z (k+1)) :=
  affine_constants i j u v a b det (projective_scaling projected_normalized i j u v det)

end NonfreeEleven.Projected
end

section
/- # Lifting the projected 32-letter word through a class-three action -/

namespace NonfreeEleven.Projected
open SimpleGraph

/-- A class-three action admitting the indicated affine-plane quotient has a simple
32-cycle in its matching graph. The action upstairs need not be free. -/
theorem class_three_plane_lift {K X : Type*} [Group K] [Group.IsNilpotent K] [MulAction K X]
    (cls : Group.nilpotencyClass K ≤ 3) (a b : K) (i j u v s t : ZMod 11)
    (det : i*v≠j*u) (π : X → ZMod 11 × ZMod 11) (onto : Function.Surjective π)
    (pa : ∀ x : X, π (a • x)=((π x).1+u,(π x).2+i*(π x).1+s))
    (pb : ∀ x : X, π (b • x)=((π x).1+v,(π x).2+j*(π x).1+t))
    (G : SimpleGraph (Bool × X)) (h0 : ∀ x,G.Adj (false,x) (true,x))
    (ha : ∀ x,G.Adj (false,x) (true,a • x)) (hb : ∀ x,G.Adj (false,x) (true,b • x)) :
    cycleGraph 32 ⊑ G := by
  classical
  let S : Fin 3 → K := ![1,a,b]
  let advance (c : Fin 3) (z : ZMod 11 × ZMod 11) :=
    (z.1+(![0,u,v] : Fin 3 → ZMod 11) c,
      z.2+(![0,i,j] : Fin 3 → ZMod 11) c*z.1+(![0,s,t] : Fin 3 → ZMod 11) c)
  have projection (c : Fin 3) (x : X) : π (S c • x)=advance c (π x) := by
    fin_cases c
    · simp [advance,S]
    · exact pa _
    · exact pb _
  have reversible (c : Fin 3) : Function.Injective (advance c) := by
    intro x y eq
    have first : x.1=y.1 := add_right_cancel (congrArg Prod.fst eq)
    have second := congrArg (fun z : ZMod 11 × ZMod 11 => z.2) eq
    change x.2+(![0,i,j] : Fin 3 → ZMod 11) c*x.1+(![0,s,t] : Fin 3 → ZMod 11) c =
      y.2+(![0,i,j] : Fin 3 → ZMod 11) c*y.1+(![0,s,t] : Fin 3 → ZMod 11) c at second
    rw [first] at second
    exact Prod.ext first (add_right_cancel (add_right_cancel second))
  obtain ⟨z,distinct,zedge⟩ := projected_simple i j u v s t det
  obtain ⟨x,hx⟩ := onto (z 0)
  let atom (k : ℕ) := S (word ⟨k%32,Nat.mod_lt _ (by decide)⟩)
  let pathProduct (n : ℕ) : K := Nat.rec 1 (fun k g => (if k%2=0 then atom k else (atom k)⁻¹)*g) n
  have close : pathProduct 32=1 := by
    change (b⁻¹*(a*((1:K)⁻¹*(b*((1:K)⁻¹*(b*(a⁻¹*(b*((1:K)⁻¹*(a*(b⁻¹*(a*((1:K)⁻¹*(a*((1:K)⁻¹*(b*(a⁻¹*((1:K)*(a⁻¹*((1:K)*(b⁻¹*(a*((1:K)⁻¹*(a*(b⁻¹*((1:K)*(a⁻¹*((1:K)*(a⁻¹*((1:K)*(a⁻¹*((1:K)*(1:K)))))))))))))))))))))))))))))))))=1
    simpa only [inv_one,one_mul,mul_one,mul_assoc] using NonfreeEleven.ClassThreeWord.class_three_closed cls a b
  let pos (k : Fin 32) := pathProduct k.val • x
  have cyclic (k : Fin 32) : pathProduct (k+1).val=pathProduct (k.val+1) := by
    by_cases last : k=31
    · subst k; change 1=pathProduct 32; exact close.symm
    · have sm : k.val+1<32 := by have max := k.isLt; have ne : k.val≠31 := fun h => last (Fin.ext h); omega
      exact congrArg pathProduct (show (k.val+1)%32=k.val+1 from Nat.mod_eq_of_lt sm)
  have walk (k : Fin 32) : if k.val%2=0 then pos (k+1)=S (word k) • pos k
      else pos k=S (word k) • pos (k+1) := by
    have label : atom k.val=S (word k) :=
      congrArg (fun l => S (word l)) (Fin.ext (Nat.mod_eq_of_lt k.isLt))
    change if k.val%2=0 then pathProduct (k+1).val • x=S (word k) • (pathProduct k.val • x)
      else pathProduct k.val • x=S (word k) • (pathProduct (k+1).val • x)
    rw [cyclic]
    change if k.val%2=0 then ((if k.val%2=0 then atom k.val else (atom k.val)⁻¹)*pathProduct k.val) • x=_
      else _=S (word k) • (((if k.val%2=0 then atom k.val else (atom k.val)⁻¹)*pathProduct k.val) • x)
    rw [label]
    split <;> simp [mul_smul]
  have track (k : Fin 32) : π (pos k)=z k := by
    induction k using Fin.induction with
    | zero => simpa [pos,pathProduct] using hx
    | succ k ih =>
      have nxt : (k.castSucc+1 : Fin 32)=k.succ := by fin_cases k <;> decide
      have xh := walk k.castSucc
      have zh := zedge k.castSucc
      change (if k.castSucc.val%2=0 then z (k.castSucc+1)=advance (word k.castSucc) (z k.castSucc)
        else z k.castSucc=advance (word k.castSucc) (z (k.castSucc+1))) at zh
      rw [nxt] at xh zh
      by_cases even : k.castSucc.val%2=0
      · simp only [even,ite_true] at xh zh
        exact (congrArg π xh).trans ((projection _ _).trans ((congrArg (advance _) ih).trans zh.symm))
      · simp only [even,ite_false] at xh zh
        apply reversible (word k.castSucc)
        exact (projection _ _).symm.trans ((congrArg π xh).symm.trans (ih.trans zh))
  let side (k : Fin 32) : Bool := decide (k.val%2=1)
  have same : ∀ l k : Fin 32,side l=side k → l.val%2=k.val%2 := by dsimp only [side]; decide
  have direction : ∀ k : Fin 32,if k.val%2=0 then side k=false ∧ side (k+1)=true
      else side k=true ∧ side (k+1)=false := by dsimp only [side]; decide
  let f (k : Fin 32) := (side k,pos k)
  have inj : Function.Injective f := by
    intro l k eq
    exact distinct _ _ (same _ _ (congrArg Prod.fst eq))
      ((track _).symm.trans ((congrArg π (congrArg Prod.snd eq)).trans (track _)))
  have label (c : Fin 3) (y : X) : G.Adj (false,y) (true,S c • y) := by
    fin_cases c
    · simpa [S] using h0 y
    · exact ha _
    · exact hb _
  have stepEdge (k : Fin 32) : G.Adj (f k) (f (k+1)) := by
    have e := walk k
    have d := direction k
    change G.Adj (side k,pos k) (side (k+1),pos (k+1))
    by_cases even : k.val%2=0
    · simp only [even,ite_true] at d e
      rw [d.1,d.2,e]; exact label _ _
    · simp only [even,ite_false] at d e
      rw [d.1,d.2,e]; exact (label _ _).symm
  refine ⟨⟨⟨f,?_⟩,inj⟩⟩
  intro l k e
  rcases cycleGraph_adj.mp e with h|h
  · have same : l=k+1 := by simpa [add_comm] using (sub_eq_iff_eq_add.mp h)
    rw [same]; exact (stepEdge _).symm
  · have same : k=l+1 := by simpa [add_comm] using (sub_eq_iff_eq_add.mp h)
    rw [same]; exact stepEdge _

end NonfreeEleven.Projected
end

section
/- # Lower central series of an affine group with a cyclic linear part -/

namespace NonfreeEleven.AffineClass
open scoped commutatorElement
variable {V Q : Type*} [AddCommGroup V] [CommGroup Q]

abbrev Aff (L : Q →* Multiplicative (AddAut V)) :=
  SemidirectProduct (Multiplicative V) Q ((MulAutMultiplicative V).symm.toMonoidHom.comp L)

abbrev act (L : Q →* Multiplicative (AddAut V)) (q : Q) : AddMonoid.End V :=
  (L q).toAdd.toAddMonoidHom

/-- The natural affine action of the semidirect product on the translation group. -/
def permAction (L : Q →* Multiplicative (AddAut V)) : Aff L →* Equiv.Perm V where
  toFun g := (L g.right).toAdd.toEquiv.trans (Equiv.addRight g.left.toAdd)
  map_one' := by apply Equiv.ext; intro (x : V); change act L 1 x+0=x; simp only [act,map_one,add_zero]; rfl
  map_mul' g h := by
    apply Equiv.ext
    intro (x : V)
    change act L (g.right*h.right) x+(g.left.toAdd+act L g.right h.left.toAdd) =
      act L g.right (act L h.right x+h.left.toAdd)+g.left.toAdd
    have comp : act L (g.right*h.right) x=act L g.right (act L h.right x) := by
      simp only [act,map_mul]; rfl
    calc
      _ = act L g.right (act L h.right x)+(g.left.toAdd+act L g.right h.left.toAdd) :=
        congrArg (fun v : V => v+(g.left.toAdd+act L g.right h.left.toAdd)) comp
      _ = (act L g.right (act L h.right x)+act L g.right h.left.toAdd)+g.left.toAdd := by abel
      _ = _ := congrArg (fun v : V => v+g.left.toAdd)
        ((act L g.right).map_add (act L h.right x) h.left.toAdd).symm

@[simp] theorem permAction_apply (L : Q →* Multiplicative (AddAut V)) (g : Aff L) (x : V) :
    permAction L g x=act L g.right x+g.left.toAdd := rfl

def tr (L : Q →* Multiplicative (AddAut V)) (x : V) : Aff L :=
  SemidirectProduct.inl (Multiplicative.ofAdd x)

/-- The commutator of two affine transformations is a translation. -/
theorem affine_comm (L : Q →* Multiplicative (AddAut V)) (g h : Aff L) :
    ⁅g,h⁆=tr L ((act L g.right h.left.toAdd-h.left.toAdd)-
      (act L h.right g.left.toAdd-g.left.toAdd)) := by
  apply (mul_right_cancel (b := h*g))
  have cancel : ⁅g,h⁆*(h*g)=g*h := by rw [commutatorElement_def]; group
  rw [cancel]
  apply SemidirectProduct.ext
  · change g.left.toAdd+act L g.right h.left.toAdd = _+act L 1 (h.left.toAdd+act L h.right g.left.toAdd)
    simp only [act,map_one]; change _=_+(h.left.toAdd+act L h.right g.left.toAdd)
    change _ = ((act L g.right h.left.toAdd-h.left.toAdd) -
      (act L h.right g.left.toAdd-g.left.toAdd)) + (h.left.toAdd+act L h.right g.left.toAdd)
    abel
  · change g.right*h.right=1*(h.right*g.right)
    rw [one_mul,mul_comm]

private theorem iterated_difference (T : AddMonoid.End V) (k m : ℕ) (x : V) :
    ∃ y : V, (T^m) (((T-1)^k) x) - ((T-1)^k) x = ((T-1)^(k+1)) y := by
  let D := T-1
  change ∃ y,(T^m) ((D^k) x)-(D^k) x=(D^(k+1)) y
  have commute : Commute T D := by change T*(T-1)=(T-1)*T; noncomm_ring
  have ck (v : V) : T ((D^k) v)=(D^k) (T v) :=
    DFunLike.congr_fun (commute.pow_right k).eq v
  induction m generalizing x with
  | zero => exact ⟨0,by simp⟩
  | succ m ih =>
    obtain ⟨y,hy⟩ := ih (T x)
    refine ⟨y+x,?_⟩
    rw [pow_succ T]
    change (T^m) (T ((D^k) x))-(D^k) x=(D^(k+1)) (y+x)
    rw [ck,map_add,← hy,← ck]
    have step : (D^(k+1)) x = T ((D^k) x) - (D^k) x := by rw [pow_succ']; rfl
    rw [step]; abel

/-- Positive powers of the selected linear part account for every cyclic quotient element.
The kth lower-central subgroup, for k≥1, consists of translations by elements of im (T−1)^k. -/
theorem affine_lower_central_range (L : Q →* Multiplicative (AddAut V)) (t : Q)
    (powers : ∀ q : Q, ∃ m : ℕ, t^m=q) (k : ℕ) {g : Aff L}
    (hg : g∈(⊤ : Subgroup (Aff L)).lowerCentralSeries (k+1)) :
    ∃ x : V, tr L (((act L t-1)^(k+1)) x)=g := by
  let T := act L t
  let D := T-1
  let K (k : ℕ) : Subgroup (Aff L) :=
    (SemidirectProduct.inl.comp (AddMonoidHom.toMultiplicative (D^k))).range
  have pow_act (m : ℕ) : act L (t^m)=T^m := by
    induction m with
    | zero => simp [act]; rfl
    | succ m ih => rw [pow_succ,pow_succ T,← ih]; apply AddMonoidHom.ext; intro x; simp only [act,map_mul]; rfl
  have diff (q : Q) (r : ℕ) (x : V) : ∃ y, act L q ((D^r) x) - (D^r) x = (D^(r+1)) y := by
    obtain ⟨m,rfl⟩ := powers q
    rw [pow_act]
    exact iterated_difference T r m x
  have bound (n : ℕ) : (⊤ : Subgroup (Aff L)).lowerCentralSeries (n+1) ≤ K (n+1) := by
    induction n with
    | zero =>
      apply Subgroup.commutator_le.mpr
      intro a _ b _
      obtain ⟨x,hx⟩ := diff a.right 0 b.left.toAdd
      obtain ⟨y,hy⟩ := diff b.right 0 a.left.toAdd
      change act L a.right b.left.toAdd-b.left.toAdd = D x at hx
      change act L b.right a.left.toAdd-a.left.toAdd = D y at hy
      refine ⟨Multiplicative.ofAdd (x-y),?_⟩
      change tr L (D (x-y))=⁅a,b⁆
      rw [affine_comm,map_sub,hx,hy]
    | succ n ih =>
      apply Subgroup.commutator_le.mpr
      intro a ha b _
      obtain ⟨v,hv⟩ := ih ha
      change tr L ((D^(n+1)) v.toAdd)=a at hv
      subst a
      obtain ⟨y,hy⟩ := diff b.right (n+1) v.toAdd
      refine ⟨Multiplicative.ofAdd (-y),?_⟩
      change tr L ((D^(n+1+1)) (-y))=⁅tr L ((D^(n+1)) v.toAdd),b⁆
      rw [affine_comm,map_neg]
      change tr L (-(D^(n+1+1)) y)=tr L ((act L 1 b.left.toAdd-b.left.toAdd)-_)
      rw [← hy]
      simp only [act,map_one]; change _=tr L ((b.left.toAdd-b.left.toAdd)-_)
      rw [sub_self,zero_sub]
      rfl
  obtain ⟨x,h⟩ := bound k hg
  exact ⟨x.toAdd,h⟩

/-- Vanishing of a positive power of T−1 bounds the nilpotency class of the whole affine group. -/
theorem affine_lower_central_bound (L : Q →* Multiplicative (AddAut V)) (t : Q)
    (powers : ∀ q : Q, ∃ m : ℕ, t^m=q) (k : ℕ)
    (nil : ∀ x : V,((act L t-1)^(k+1)) x=0) :
    Group.IsNilpotent (Aff L) ∧ Group.nilpotencyClass (Aff L) ≤ k+1 := by
  have bot : (⊤ : Subgroup (Aff L)).lowerCentralSeries (k+1)=⊥ := by
    apply bot_unique
    intro g hg
    obtain ⟨x,rfl⟩ := affine_lower_central_range L t powers k hg
    rw [nil]
    exact Subgroup.one_mem _
  let _ : Group.IsNilpotent (Aff L) := Subgroup.nilpotent_iff_lowerCentralSeries.mpr ⟨_,bot⟩
  exact ⟨inferInstance,Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mp bot⟩

end NonfreeEleven.AffineClass
end

section
/- # Affine plane coordinates for an order-121 moving subgroup
Codex, gpt-6.2-astra. -/

namespace NonfreeEleven

/-- Every iterated displacement belongs to the range of the first displacement. -/
private theorem iterate_sub_mem {V : Type*} [AddCommGroup V] (T : V →+ V)
    (n : ℕ) (z : V) : T^[n] z-z∈(T-AddMonoidHom.id V).range := by
  let D := T-AddMonoidHom.id V
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    have h := D.range.add_mem (show D (T^[n] z)∈D.range from ⟨_,rfl⟩) ih
    change (T (T^[n] z)-T^[n] z)+(T^[n] z-z)∈D.range at h
    simpa only [sub_add_sub_cancel] using h

/-- A nontrivial square-zero endomorphism on an elementary group of order 121
has coordinates in which it sends (x,y) to (0,x). -/
private theorem shear_coordinates {M : Type*} [AddCommGroup M] [Finite M]
    (card : Nat.card M=121) (torsion : ∀ z : M, 11 • z=0) (E : M →+ M)
    (nil : ∀ z : M,E (E z)=0) (e : M) (nonzero : E e≠0) :
    ∃ C : M ≃+ (ZMod 11 × ZMod 11),∀ z,C (E z)=(0,(C z).1) := by
  classical
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let _ : Module (ZMod 11) M := AddCommGroup.zmodModule torsion
  let f := E e
  let B : (ZMod 11 × ZMod 11) →+ M := {
    toFun z := z.1 • e+z.2 • f
    map_zero' := by simp
    map_add' := by intro x y; simp only [Prod.fst_add,Prod.snd_add,add_smul]; abel }
  have kill : ∀ z : ZMod 11 × ZMod 11,B z=0 → z=0 := by
    rintro ⟨r,s⟩ h
    change r • e+s • f=0 at h
    have h' := congrArg E h
    simp only [map_add,ZMod.map_smul,show E f=0 from nil e,smul_zero,add_zero,map_zero] at h'
    have hr := (smul_eq_zero.mp h').resolve_right nonzero
    rw [hr,zero_smul,zero_add] at h
    exact Prod.ext hr ((smul_eq_zero.mp h).resolve_right nonzero)
  have inject : Function.Injective B := by
    intro z w h
    exact sub_eq_zero.mp (kill (z-w) (by rw [map_sub,h,sub_self]))
  let _ := Fintype.ofFinite M
  have eqcard : Fintype.card (ZMod 11 × ZMod 11)=Fintype.card M := by
    rw [← Nat.card_eq_fintype_card (α:=M),card,Fintype.card_prod,ZMod.card]
  let F := AddEquiv.ofBijective B ((Fintype.bijective_iff_injective_and_card B).mpr ⟨inject,eqcard⟩)
  refine ⟨F.symm,?_⟩
  intro z
  obtain ⟨⟨r,s⟩,rfl⟩ := F.surjective z
  rw [F.symm_apply_apply]
  apply F.injective
  rw [F.apply_symm_apply]
  change E (r • e+s • f)=0 • e+r • f
  simp only [map_add,ZMod.map_smul,show E f=0 from nil e,smul_zero,add_zero,zero_smul,zero_add]
  rfl

/-- For two affine maps with linear parts powers of T, either their commutator
translation is T-fixed, or the moving quotient is a shear plane with independent
slope and horizontal-shift vectors. -/
theorem moving_121_plane_or_fixed {V : Type*} [AddCommGroup V] [Finite V]
    (T : V →+ V) (period : ∀ z : V,T^[11] z=z)
    (size : Nat.card (T-AddMonoidHom.id V).range=121)
    (i j : ℕ) (P Q : V) :
    let c := (T^[i] Q-Q)-(T^[j] P-P)
    T c=c ∨ ∃ π : V →+ (ZMod 11 × ZMod 11), Function.Surjective π ∧
      (i : ZMod 11)*(π Q).1≠(j : ZMod 11)*(π P).1 ∧
      ∀ (k : ℕ) (A z : V),π (T^[k] z+A)=
        ((π z).1+(π A).1,(π z).2+(k : ZMod 11)*(π z).1+(π A).2) := by
  classical
  intro c
  by_cases fixed : T c=c
  · exact Or.inl fixed
  right
  let D := T-AddMonoidHom.id V
  let M := D.range
  let E : M →+ M := D.rangeRestrict.comp D.range.subtype
  have exp (z : M) : 11 • z=0 := by
    obtain ⟨x,hx⟩ := z.property
    apply Subtype.ext
    change 11 • (z:V)=0
    rw [←hx]
    exact (moving_121_exponent T period size x).1
  have nil (z : M) : E (E z)=0 := by
    obtain ⟨x,hx⟩ := z.property
    apply Subtype.ext
    change T (T z-z)-(T z-z)=0
    rw [←hx]
    exact sub_eq_zero.mpr (moving_121_exponent T period size x).2
  let e : M := ⟨c,D.range.sub_mem (iterate_sub_mem T i Q) (iterate_sub_mem T j P)⟩
  have ne : E e≠0 := by
    intro eq
    apply fixed
    exact sub_eq_zero.mp (congrArg (fun z : M => (z:V)) eq)
  obtain ⟨C,hC⟩ := shear_coordinates size exp E nil e ne
  let π : V →+ (ZMod 11 × ZMod 11) := C.toAddMonoidHom.comp D.rangeRestrict
  have transform (z : V) : π (T z)=((π z).1,(π z).2+(π z).1) := by
    have d : D.rangeRestrict (T z)=D.rangeRestrict z+E (D.rangeRestrict z) := by
      apply Subtype.ext
      change T (T z)-T z=(T z-z)+(T (T z-z)-(T z-z))
      rw [map_sub]; abel
    change C (D.rangeRestrict (T z))=_
    rw [d,map_add,hC]
    exact Prod.ext (add_zero _) rfl
  have iter (k : ℕ) (z : V) : π (T^[k] z)=((π z).1,(π z).2+(k : ZMod 11)*(π z).1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply',transform,ih]
      apply Prod.ext
      · rfl
      · change (π z).2 + (k : ZMod 11)*(π z).1 + (π z).1=(π z).2 + ((k+1 : ℕ) : ZMod 11)*(π z).1
        rw [Nat.cast_succ]; ring
  have nonzero : π c≠0 := by
    intro eq
    apply ne
    apply C.injective
    rw [map_zero]
    change C (E e)=0 at eq
    exact eq
  have det : (i : ZMod 11)*(π Q).1≠(j : ZMod 11)*(π P).1 := by
    intro eq
    apply nonzero
    dsimp only [c]
    rw [map_sub,map_sub,map_sub,iter,iter]
    apply Prod.ext
    · simp
    · simpa using sub_eq_zero.mpr eq
  refine ⟨π,C.surjective.comp D.rangeRestrict_surjective,det,?_⟩
  intro k A z
  rw [map_add,iter]
  rfl

/-- For a moving subgroup of size at most 11, all iterated displacements are fixed
by a period-eleven operator. Thus the commutator translation of any two affine
powers is fixed as well. -/
theorem small_moving_commutator_fixed {V : Type*} [AddCommGroup V] [Finite V]
    (T : V →+ V) (period : ∀ z : V,T^[11] z=z)
    (size : Nat.card (T-AddMonoidHom.id V).range≤11) (i j : ℕ) (P Q : V) :
    let c := (T^[i] Q-Q)-(T^[j] P-P)
    T c=c := by
  classical
  let D := T-AddMonoidHom.id V
  let M := D.range
  let S : M →+ M := {
    toFun z := ⟨T z,by
      obtain ⟨x,hx⟩ := z.property
      exact ⟨T x,by rw [←hx]; exact (map_sub T (T x) x).symm⟩⟩
    map_zero' := Subtype.ext (map_zero T)
    map_add' := fun x y => Subtype.ext (map_add T _ _) }
  let _ := Fintype.ofFinite M
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let f : Function.End M := fun z => S z
  have sem : Function.Semiconj (fun z : M => (z:V)) S T := fun _ => rfl
  have ep : f^11^1=1 := by
    rw [pow_one]; funext z
    exact Subtype.ext ((sem.iterate_right 11 z).trans (period _))
  have cong := Equiv.Perm.card_fixedPoints_modEq ep
  let F := Function.fixedPoints f
  let _ : Nonempty F := ⟨⟨0,map_zero S⟩⟩
  have pos : 0<Nat.card F := Nat.card_pos
  have le : Nat.card F≤Nat.card M := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card] at cong
  change Nat.card M%11=Nat.card F%11 at cong
  change Nat.card M≤11 at size
  have eqcard : Nat.card F=Nat.card M := by omega
  have allfixed : F=Set.univ := F.eq_univ_iff_ncard.mpr eqcard
  intro c
  let e : M := ⟨c,D.range.sub_mem (iterate_sub_mem T i Q) (iterate_sub_mem T j P)⟩
  have mem : e∈F := allfixed ▸ Set.mem_univ e
  exact congrArg (fun z : M => (z:V)) (show f e=e from mem)

end NonfreeEleven
end

section
/- # The 32-cycle in the noncentral order-121 affine case
Codex, gpt-6.2-astra. -/

namespace NonfreeEleven
open AffineClass SimpleGraph

/-- The action of a natural power is the corresponding iterate of the generator. -/
theorem affine_generator_iterate {Q V : Type*} [CommGroup Q] [AddCommGroup V]
    (L : Q →* Multiplicative (AddAut V)) (t : Q) (k : ℕ) (z : V) :
    act L (t^k) z=(act L t)^[k] z := by
  let T := act L t
  induction k with
  | zero => simp [act]; rfl
  | succ k ih =>
    rw [pow_succ',Function.iterate_succ_apply']
    change (L (t*t^k)).toAdd z=T ((act L t)^[k] z)
    rw [map_mul,← ih]; rfl

/-- If the moving subgroup has at most eleven elements, every affine commutator
is a fixed translation. -/
theorem small_affine_commutator_fixed {Q V : Type*} [CommGroup Q] [AddCommGroup V]
    [Finite V] (L : Q →* Multiplicative (AddAut V)) (t : Q)
    (powers : ∀ q : Q, ∃ m : ℕ,t^m=q)
    (period : ∀ z : V,(act L t)^[11] z=z)
    (size : Nat.card (act L t-1 : AddMonoid.End V).range≤11)
    (p q : Q) (P R : V) :
    let c := (act L p R-R)-(act L q P-P)
    act L t c=c := by
  obtain ⟨i,rfl⟩ := powers p
  obtain ⟨j,rfl⟩ := powers q
  dsimp only
  rw [affine_generator_iterate L t i,affine_generator_iterate L t j]
  exact small_moving_commutator_fixed (act L t) period size i j P R

/-- An affine matching graph whose moving group has order 121 contains a 32-cycle
whenever the commutator displacement is not fixed by the generator of the linear parts. -/
theorem moving_121_affine_cycle_or_fixed {Q V : Type*} [CommGroup Q] [AddCommGroup V]
    [Finite V] (L : Q →* Multiplicative (AddAut V)) (t : Q)
    (powers : ∀ q : Q, ∃ m : ℕ,t^m=q)
    (period : ∀ z : V,(act L t)^[11] z=z)
    (size : Nat.card (act L t-1 : AddMonoid.End V).range=121)
    (p q : Q) (P R : V) (G : SimpleGraph (Bool × V))
    (idEdge : ∀ z,G.Adj (false,z) (true,z))
    (pEdge : ∀ z,G.Adj (false,z) (true,act L p z+P))
    (qEdge : ∀ z,G.Adj (false,z) (true,act L q z+R)) :
    let c := (act L p R-R)-(act L q P-P)
    act L t c=c ∨ cycleGraph 32 ⊑ G := by
  classical
  let T := act L t
  have power := affine_generator_iterate L t
  obtain ⟨i,rfl⟩ := powers p
  obtain ⟨j,rfl⟩ := powers q
  intro c
  rcases moving_121_plane_or_fixed T period size i j P R with fixed|⟨π,onto,det,hπ⟩
  · left
    change T c=c
    dsimp only [c]; rw [power,power]; exact fixed
  right
  have nil (x : V) : ((T-1 : AddMonoid.End V)^(3 : ℕ)) x=0 := by
    change T (T (T x-x)-(T x-x))-(T (T x-x)-(T x-x))=0
    exact sub_eq_zero.mpr (moving_121_exponent T period size x).2
  obtain ⟨inst,cls⟩ := affine_lower_central_bound L t powers 2 nil
  let _ : Group.IsNilpotent (Aff L) := inst
  let _ : MulAction (Aff L) V := MulAction.compHom V (permAction L)
  let a : Aff L := ⟨Multiplicative.ofAdd P,t^i⟩
  let b : Aff L := ⟨Multiplicative.ofAdd R,t^j⟩
  have fa (z : V) : a • z=act L (t^i) z+P := permAction_apply L a z
  have fb (z : V) : b • z=act L (t^j) z+R := permAction_apply L b z
  apply Projected.class_three_plane_lift cls a b i j (π P).1 (π R).1 (π P).2 (π R).2 det π onto
  · intro z; rw [fa,power]; exact hπ i P z
  · intro z; rw [fb,power]; exact hπ j R z
  · exact idEdge
  · intro z; rw [fa]; exact pEdge z
  · intro z; rw [fb]; exact qEdge z

end NonfreeEleven
end

section
/- # Fixed affine commutators and short cycles for an order-eleven linear action -/

namespace NonfreeEleven.AffineClass
open SimpleGraph
open scoped commutatorElement

/-- Periodicity makes every power of an endomorphism invertible. -/
def periodicPerm {V : Type*} (T : V → V) (period : ∀ x,T^[11] x=x) : Equiv.Perm V where
  toFun := T
  invFun := T^[10]
  left_inv x := by simpa only [Function.iterate_succ_apply] using period x
  right_inv x := by simpa only [Function.iterate_succ_apply'] using period x

/-- A generator-fixed translation commutator gives a simple cycle of length 4, 8 or 16.
The linear parts of the two matching maps may be arbitrary powers of T. -/
theorem fixed_commutator_short {V : Type*} [AddCommGroup V] (T : V →+ V)
    (period : ∀ x,T^[11] x=x) (i j : ℕ) (P Q : V)
    (fixed : T ((T^[i] Q-Q)-(T^[j] P-P))=(T^[i] Q-Q)-(T^[j] P-P))
    (separate : ∀ z : V,T^[i] z+P≠z ∧ T^[j] z+Q≠z ∧ T^[i] z+P≠T^[j] z+Q)
    (G : SimpleGraph (Bool × V)) (idEdge : ∀ z,G.Adj (false,z) (true,z))
    (pEdge : ∀ z,G.Adj (false,z) (true,T^[i] z+P))
    (qEdge : ∀ z,G.Adj (false,z) (true,T^[j] z+Q)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  let R := periodicPerm T period
  let p := (R^i).trans (Equiv.addRight P)
  let q := (R^j).trans (Equiv.addRight Q)
  let c := (T^[i] Q-Q)-(T^[j] P-P)
  let s := Equiv.addRight c
  have pp (x : V) : p x=T^[i] x+P := rfl
  have qq (x : V) : q x=T^[j] x+Q := rfl
  have plus (k : ℕ) (x y : V) : T^[k] (x+y)=T^[k] x+T^[k] y := by
    induction k with
    | zero => rfl
    | succ k ih => simp only [Function.iterate_succ_apply',ih,map_add]
  have commute (x : V) : T^[i] (T^[j] x)=T^[j] (T^[i] x) := by
    rw [←Function.iterate_add_apply,←Function.iterate_add_apply,Nat.add_comm]
  have origin : ⁅p,q⁆=s := by
    apply (mul_right_cancel (b := q*p))
    have eq : ⁅p,q⁆*(q*p)=p*q := by rw [commutatorElement_def]; group
    rw [eq]
    apply Equiv.ext
    intro x
    change p (q x)=q (p x)+c
    rw [pp,qq,qq,pp,plus,plus,commute]
    dsimp only [c]; abel
  have stable (k : ℕ) : T^[k] c=c := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply',ih]; exact fixed
  apply OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1.classTwoPerm_short G p q separate idEdge pEdge qEdge
  · rw [origin]
    apply Equiv.ext
    intro x
    change p (x+c)=p x+c
    rw [pp,pp,plus,stable]; abel
  · rw [origin]
    apply Equiv.ext
    intro x
    change q (x+c)=q x+c
    rw [qq,qq,plus,stable]; abel

/-- The canonical order-eleven generator covers the entire cyclic linear quotient by positive powers. -/
theorem eleven_powers (q : Multiplicative (ZMod 11)) :
    ∃ m : ℕ, (Multiplicative.ofAdd (1 : ZMod 11))^m=q := by
  refine ⟨q.toAdd.val,Multiplicative.toAdd.injective ?_⟩
  change q.toAdd.val • (1 : ZMod 11)=q.toAdd
  simp

/-- Square-zero displacement fixes every commutator vector of the two affine generators. -/
theorem fixed_of_square_zero {V : Type*} [AddCommGroup V] (T : V →+ V)
    (nil : ∀ x,T (T x-x)=T x-x) (i j : ℕ) (P Q : V) :
    T ((T^[i] Q-Q)-(T^[j] P-P))=(T^[i] Q-Q)-(T^[j] P-P) := by
  have fixes (n : ℕ) (x : V) : T (T^[n] x-x)=T^[n] x-x := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      have split : T (T^[n] x)-x=(T (T^[n] x)-T^[n] x)+(T^[n] x-x) := by abel
      rw [split,map_add,nil,ih]
  rw [map_sub,fixes,fixes]

/-- A fixed commutator yields a short cycle on the original affine space without
assuming that the point stabilizers are trivial. -/
theorem fixed_linear_short {V Q : Type*} [AddCommGroup V] [CommGroup Q]
    (L : Q →* Multiplicative (AddAut V)) (t : Q) (powers : ∀ q : Q, ∃ m : ℕ,t^m=q)
    (period : ∀ z : V,(act L t)^[11] z=z) (p q : Q) (P R : V)
    (fixed : act L t ((act L p R-R)-(act L q P-P))=(act L p R-R)-(act L q P-P))
    (sep : ∀ z : V,act L p z+P≠z ∧ act L q z+R≠z ∧ act L p z+P≠act L q z+R)
    (G : SimpleGraph (Bool × V)) (idEdge : ∀ z,G.Adj (false,z) (true,z))
    (pEdge : ∀ z,G.Adj (false,z) (true,act L p z+P))
    (qEdge : ∀ z,G.Adj (false,z) (true,act L q z+R)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G := by
  have iter (m : ℕ) (z : V) : act L (t^m) z=(act L t)^[m] z := by
    let T := act L t
    induction m with
    | zero => simp [act]; rfl
    | succ m ih =>
      rw [pow_succ',Function.iterate_succ_apply']
      change (L (t*t^m)).toAdd z=T ((act L t)^[m] z)
      rw [map_mul,← ih]; rfl
  obtain ⟨i,rfl⟩ := powers p
  obtain ⟨j,rfl⟩ := powers q
  simp only [iter] at sep pEdge qEdge fixed
  exact fixed_commutator_short (act L t) period i j P R fixed sep G idEdge pEdge qEdge

/-- The class-three identity used by the plane certificate holds on the full affine group. -/
theorem affine_word_closed {V Q : Type*} [AddCommGroup V] [CommGroup Q]
    (L : Q →* Multiplicative (AddAut V)) (t : Q) (powers : ∀ q : Q, ∃ m : ℕ, t^m=q)
    (nil : ∀ x : V,((act L t-1 : AddMonoid.End V)^(3 : ℕ)) x=0) (a b : Aff L) :
    b⁻¹*a*b*b*a⁻¹*b*a*b⁻¹*a*a*b*a⁻¹*a⁻¹*b⁻¹*a*a*b⁻¹*a⁻¹*a⁻¹*a⁻¹=1 := by
  obtain ⟨inst,bound⟩ := affine_lower_central_bound L t powers 2 nil
  exact ClassThreeWord.class_three_closed bound a b

end NonfreeEleven.AffineClass
end

section
/- # Short cycles in the cyclic and order-121 moving cases
Codex, gpt-6.2-astra. -/

namespace NonfreeEleven
open AffineClass SimpleGraph

/-- A fixed-point-free matching triple from an affine action of period eleven
has a power-of-two cycle of length at most 32 whenever its moving subgroup has
order at most eleven or exactly 121. -/
theorem small_or_121_affine_short {Q V : Type*} [CommGroup Q] [AddCommGroup V]
    [Finite V] (L : Q →* Multiplicative (AddAut V)) (t : Q)
    (powers : ∀ q : Q, ∃ m : ℕ,t^m=q) (period : ∀ z : V,(act L t)^[11] z=z)
    (size : Nat.card (act L t-1 : AddMonoid.End V).range≤11 ∨
      Nat.card (act L t-1 : AddMonoid.End V).range=121)
    (p q : Q) (P R : V)
    (sep : ∀ z : V,act L p z+P≠z ∧ act L q z+R≠z ∧ act L p z+P≠act L q z+R)
    (G : SimpleGraph (Bool × V)) (idEdge : ∀ z,G.Adj (false,z) (true,z))
    (pEdge : ∀ z,G.Adj (false,z) (true,act L p z+P))
    (qEdge : ∀ z,G.Adj (false,z) (true,act L q z+R)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  have alt : act L t ((act L p R-R)-(act L q P-P))=(act L p R-R)-(act L q P-P) ∨
      cycleGraph 32 ⊑ G := by
    rcases size with small|plane
    · exact Or.inl (small_affine_commutator_fixed L t powers period small p q P R)
    · exact moving_121_affine_cycle_or_fixed L t powers period plane p q P R G idEdge pEdge qEdge
  rcases alt with fixed|long
  · rcases fixed_linear_short L t powers period p q P R fixed sep G idEdge pEdge qEdge with h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inr (Or.inr long))

end NonfreeEleven
end

section
/- # Action form of the fixed-commutator cycle theorem -/

namespace NonfreeEleven.AffineClass
open SimpleGraph

/-- The homomorphism to additive automorphisms associated with a distributive group action. -/
def actionLinear (Q V : Type*) [Group Q] [AddCommGroup V] [DistribMulAction Q V] :
    Q →* Multiplicative (AddAut V) where
  toFun k := Multiplicative.ofAdd {
    toFun := fun z : V => k • z, invFun := fun z => k⁻¹ • z,
    left_inv := inv_smul_smul k, right_inv := smul_inv_smul k,
    map_add' := smul_add k }
  map_one' := by apply Multiplicative.toAdd.injective; apply AddEquiv.ext; intro z; exact one_smul _ z
  map_mul' g h := by
    apply Multiplicative.toAdd.injective
    apply AddEquiv.ext
    intro z
    exact mul_smul g h z

/-- The action of one in Z/11Z, written as an additive endomorphism, has period eleven. -/
theorem eleven_action_period {V : Type*} [AddCommGroup V] [DistribMulAction (Multiplicative (ZMod 11)) V]
    (x : V) : (act (actionLinear (Multiplicative (ZMod 11)) V) (Multiplicative.ofAdd 1))^[11] x=x := by
  let t := Multiplicative.ofAdd (1 : ZMod 11)
  let L := actionLinear (Multiplicative (ZMod 11)) V
  have powers (n : ℕ) : (act L t)^[n] x=t^n • x := by
    induction n with
    | zero => simp
    | succ n ih => rw [Function.iterate_succ_apply',ih,pow_succ',mul_smul]; rfl
  have per : t^11=1 := by decide
  rw [powers 11,per,one_smul]

/-- A fixed commutator gives a short cycle for the same normalized orbit matchings as the
large fixed-subgroup index theorem. -/
theorem fixed_eleven_action_cycle {V : Type*} [AddCommGroup V]
    [DistribMulAction (Multiplicative (ZMod 11)) V] (p q : Multiplicative (ZMod 11) × V)
    (fixed : (Multiplicative.ofAdd (1 : ZMod 11)) • ((p.1 • q.2-q.2)-(q.1 • p.2-p.2))=
      (p.1 • q.2-q.2)-(q.1 • p.2-p.2))
    (sep : ∀ x : V,p.1 • x+p.2≠x ∧ q.1 • x+q.2≠x ∧ p.1 • x+p.2≠q.1 • x+q.2)
    (G : SimpleGraph (Bool × V)) (idEdge : ∀ z,G.Adj (false,z) (true,z))
    (pEdge : ∀ z,G.Adj (false,z) (true,p.1 • z+p.2))
    (qEdge : ∀ z,G.Adj (false,z) (true,q.1 • z+q.2)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G :=
  fixed_linear_short (actionLinear _ V) (Multiplicative.ofAdd 1) eleven_powers eleven_action_period
    p.1 q.1 p.2 q.2 fixed sep G idEdge pEdge qEdge

end NonfreeEleven.AffineClass
end

section
/- # Small moving groups for a standard action of the cyclic group of order eleven
Codex, gpt-6.2-astra. -/

namespace NonfreeEleven
open AffineClass SimpleGraph

/-- The order-one, order-eleven and order-121 alternatives collectively give the asserted
power-of-two cycle for the standard C11 action on an affine orbit. -/
theorem small_or_121_action_short {V : Type*} [AddCommGroup V] [Finite V]
    [DistribMulAction (Multiplicative (ZMod 11)) V]
    (size : let D : AddMonoid.End V := act (actionLinear (Multiplicative (ZMod 11)) V) (Multiplicative.ofAdd 1)-1;
      Nat.card D.range≤11 ∨ Nat.card D.range=121)
    (i j : Multiplicative (ZMod 11)) (P R : V)
    (sep : ∀ z : V,i • z+P≠z ∧ j • z+R≠z ∧ i • z+P≠j • z+R)
    (G : SimpleGraph (Bool × V)) (idEdge : ∀ z,G.Adj (false,z) (true,z))
    (pEdge : ∀ z,G.Adj (false,z) (true,i • z+P))
    (qEdge : ∀ z,G.Adj (false,z) (true,j • z+R)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G :=
  small_or_121_affine_short (actionLinear _ V) (Multiplicative.ofAdd 1)
    eleven_powers eleven_action_period size i j P R sep G idEdge pEdge qEdge

end NonfreeEleven
end

section
/- Scalar coordinates for a prime-order moving subgroup of a periodic additive map. -/
namespace NonfreeEleven.PrimeNormal

universe u

private theorem scalar_action {q : ℕ} [NeZero q] (h : ZMod q →+ ZMod q) (z : ZMod q) :
    h z=h 1*z := by
  calc
    h z = h (z.val • (1 : ZMod q)) := by simp [nsmul_eq_mul]
    _ = _ := by rw [map_nsmul]; simp [nsmul_eq_mul,mul_comm]

set_option maxRecDepth 5000 in
/-- Splitting into the fixed kernel and the field identifies the action of T with
multiplication by a scalar of order eleven, simultaneously for all of its powers. -/
theorem coordinates {V : Type u} [AddCommGroup V] [Finite V] (T : V →+ V)
    (period : ∀ x : V, T^[11] x=x) (q : ℕ) (hq : q=23 ∨ q=67 ∨ q=89 ∨ q=199)
    (card : Nat.card (T-AddMonoidHom.id V).range=q) :
    ∃ (C : (T-AddMonoidHom.id V).ker × ZMod q ≃+ V) (a : ZMod q),
      orderOf a=11 ∧ ∀ (j : ℕ) h z, T^[j] (C (h,z)) = C (h,a^j*z) := by
  classical
  let : Fact q.Prime := ⟨by rcases hq with rfl|rfl|rfl|rfl <;> decide⟩
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  let D := T-AddMonoidHom.id V
  let M := D.range
  let F := D.ker
  have cop : Nat.Coprime 11 (Nat.card D.range) := by
    rw [card]; rcases hq with rfl|rfl|rfl|rfl <;> decide
  obtain ⟨E,hE⟩ := NonfreeEleven.fixed_image_product T 11 period cop
  have cyclic : IsAddCyclic M := isAddCyclic_of_card_dvd_prime (p:=q) (by rw [show Nat.card ↥M=q from card])
  let e : ZMod q ≃+ M := (ZMod.ringEquivCongr card.symm).toAddEquiv.trans (zmodAddCyclicAddEquiv cyclic)
  have stay (m : M) : T (m:V) ∈ M := by
    obtain ⟨v,hv⟩ := m.property
    refine ⟨T v,?_⟩
    change T (T v)-T v = T (m:V)
    change T v-v=(m:V) at hv
    rw [←hv,map_sub]
  let S : M →+ M := {
    toFun m := ⟨T m,stay m⟩
    map_zero' := Subtype.ext (map_zero T)
    map_add' x y := Subtype.ext (map_add T (x:V) (y:V)) }
  let phi := e.symm.toAddMonoidHom.comp (S.comp e.toAddMonoidHom)
  let a := phi 1
  have move (z : ZMod q) : T (e z : V) = e (a*z) := by
    have h := congrArg e (scalar_action phi z)
    change e (e.symm (S (e z))) = e (a*z) at h
    rw [e.apply_symm_apply] at h
    exact congrArg (fun t : M => (t:V)) h
  have iter (k : ℕ) (z : ZMod q) : T^[k] (e z : V) = e (a^k*z) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply',ih,move,pow_succ']
      ring_nf
  have pow : a^11=1 := by
    apply e.injective
    apply Subtype.ext
    simpa using (iter 11 1).symm.trans (period (e 1))
  have nontriv : a≠1 := by
    intro eq
    have fixed : T (e 1 : V) = (e 1 : V) := by simpa [eq] using move 1
    have kill := NonfreeEleven.fixed_image_torsion T 11 period (e 1) (e 1).property fixed
    have ec : e (11 • (1 : ZMod q))=e 0 := by
      rw [map_nsmul,map_zero]; exact Subtype.ext kill
    have bad : (11 : ZMod q) = 0 := by simpa [nsmul_eq_mul] using e.injective ec
    have nz (n : ℕ) (hn : n=23 ∨ n=67 ∨ n=89 ∨ n=199) : (11 : ZMod n) ≠ 0 := by
      rcases hn with rfl|rfl|rfl|rfl <;> decide
    exact nz q hq bad
  let C := ((AddEquiv.refl F).prodCongr e).trans E
  have hC (h : F) (z : ZMod q) : C (h,z)=(h:V)+(e z:V) := hE _
  have fixed (h : F) : T (h:V)=h := sub_eq_zero.mp h.property
  refine ⟨C,a,orderOf_eq_prime pow nontriv,?_⟩
  intro j h z
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply',ih,hC,hC,map_add,fixed,move,pow_succ',mul_assoc]

end NonfreeEleven.PrimeNormal
end

section
/- Conjugation of two affine matchings to the normalized small-field certificate.
The commuting case uses the earlier Haar-transfer theorem of the matching reduction. -/
namespace NonfreeEleven.PrimeNormal

open SimpleGraph SmallField

abbrev Short {X : Type*} (G : SimpleGraph X) : Prop :=
  cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G

set_option maxRecDepth 5000 in
/-- A chart with two constant translations on an abelian factor and arbitrary affine
offsets on the prime field suffices. It is enough for the three matchings to be
distinct at one point. The ambient graph may contain further edges. -/
theorem affine_chart {F V X : Type*} [AddCommGroup F] (q : ℕ)
    (hq : q=23 ∨ q=67 ∨ q=89 ∨ q=199) (a b c e : ZMod q)
    (ha : orderOf a=11) (hb : b^11=1)
    (C : F × ZMod q ≃ V) (P Q : Equiv.Perm V) (u v : F)
    (pchart : ∀ h z, P (C (h,z)) = C (h+u,a*z+c))
    (qchart : ∀ h z, Q (C (h,z)) = C (h+v,b*z+e))
    (z₀ : V) (sepP : P z₀≠z₀) (sepQ : Q z₀≠z₀) (sepPQ : P z₀≠Q z₀)
    (G : SimpleGraph X) (ι : (Bool × V) ↪ X)
    (edge₀ : ∀ x, G.Adj (ι (false,x)) (ι (true,x)))
    (edgeP : ∀ x, G.Adj (ι (false,x)) (ι (true,P x)))
    (edgeQ : ∀ x, G.Adj (ι (false,x)) (ι (true,Q x))) : Short G := by
  classical
  let : Fact q.Prime := ⟨by rcases hq with rfl|rfl|rfl|rfl <;> decide⟩
  have ne : a≠1 := by intro h; simp [h] at ha
  let r := c/(1-a)
  have fixr : a*r+c=r := by
    dsimp [r]
    field_simp [sub_ne_zero.mpr (Ne.symm ne)]
    ring
  let s := b*r+e-r
  by_cases h : s=0
  · have ec : e=r-b*r := by dsimp [s] at h; linear_combination h
    have cc : c=r-a*r := by linear_combination fixr
    have comm : Commute P Q := by
      ext x
      obtain ⟨⟨h,z⟩,rfl⟩ := C.surjective x
      change P (Q (C (h,z))) = Q (P (C (h,z)))
      rw [qchart,pchart,pchart,qchart]
      apply congrArg C
      apply Prod.ext
      · dsimp; abel
      · dsimp; rw [ec,cc]; ring
    rcases OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.HaarTransfer.commuting_matchings
      G P Q comm z₀ sepP sepQ sepPQ ι edge₀ edgeP edgeQ with h4|h8|h16
    · exact Or.inl h4
    · exact Or.inr (Or.inl h8)
    · exact Or.inr (Or.inr (Or.inl h16))
  · let B : (F × ZMod q) ↪ V :=
      ⟨fun z => C (z.1,r+s*z.2), by
        rintro ⟨k,z⟩ ⟨l,w⟩ eq
        have g := C.injective eq
        have e₁ : k=l := congrArg Prod.fst g
        have e₂ : r+s*z=r+s*w := congrArg Prod.snd g
        exact Prod.ext e₁ (mul_left_cancel₀ h (add_left_cancel e₂))⟩
    let J := ((Function.Embedding.refl Bool).prodMap B).trans ι
    let d : Label → F := ![0,u,v]
    have pmap (t : F) (z : ZMod q) : B (t+u,a*z)=P (B (t,z)) := by
      change C (t+u,r+s*(a*z))=P (C (t,r+s*z))
      rw [pchart]
      apply congrArg C
      apply Prod.ext
      · rfl
      · dsimp; linear_combination -fixr
    have qmap (t : F) (z : ZMod q) : B (t+v,b*z+1)=Q (B (t,z)) := by
      change C (t+v,r+s*(b*z+1))=Q (C (t,r+s*z))
      rw [qchart]
      apply congrArg C
      apply Prod.ext
      · rfl
      · dsimp [s]; ring
    have edges : ∀ k x, (G.comap J).Adj (false,x) (true,addForward d (forward a b) k x) := by
      rintro k ⟨t,z⟩
      fin_cases k
      · change G.Adj (ι (false,B (t,z))) (ι (true,B (t+0,z)))
        simpa using edge₀ (B (t,z))
      · change G.Adj (ι (false,B (t,z))) (ι (true,B (t+u,a*z)))
        rw [pmap]; exact edgeP _
      · change G.Adj (ι (false,B (t,z))) (ι (true,B (t+v,b*z+1)))
        rw [qmap]; exact edgeQ _
    have incl : G.comap J ⊑ G := isContained_iff_exists_le_comap.mpr ⟨J,le_rfl⟩
    rcases separated q hq a b ha hb d (G.comap J) edges with s16|s32
    · exact Or.inr (Or.inr (Or.inl (s16.trans incl)))
    · exact Or.inr (Or.inr (Or.inr (s32.trans incl)))

end NonfreeEleven.PrimeNormal
end

section
/-
# Prime-order moving subgroup for two affine matchings

The action on the moving coordinate is determined from the periodic additive operator.
The fixed coordinate may have any cardinality allowed by the finite ambient group.
The proof combines the fixed/moving splitting, affine normalization, the four finite
word certificates, and the Haar-transfer theorem for commuting matchings.
Codex, gpt-6.2-astra.
-/
namespace NonfreeEleven.PrimeNormal

open SimpleGraph

set_option maxRecDepth 5000 in
/-- The two linear components may be any powers of T, including identity powers.
The three graph matchings are assumed distinct at just one common vertex. -/
theorem cycles {V X : Type*} [AddCommGroup V] [Finite V] (T : V →+ V)
    (period : ∀ v : V, T^[11] v=v) (q : ℕ) (hq : q=23 ∨ q=67 ∨ q=89 ∨ q=199)
    (card : Nat.card (T-AddMonoidHom.id V).range=q)
    (i j : ℕ) (P Q : Equiv.Perm V) (c e : V)
    (hP : ∀ v, P v=T^[i] v+c) (hQ : ∀ v, Q v=T^[j] v+e)
    (z₀ : V) (sepP : P z₀≠z₀) (sepQ : Q z₀≠z₀) (sepPQ : P z₀≠Q z₀)
    (G : SimpleGraph X) (ι : (Bool × V) ↪ X)
    (edge₀ : ∀ v, G.Adj (ι (false,v)) (ι (true,v)))
    (edgeP : ∀ v, G.Adj (ι (false,v)) (ι (true,P v)))
    (edgeQ : ∀ v, G.Adj (ι (false,v)) (ι (true,Q v))) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  classical
  let : Fact (Nat.Prime 11) := ⟨by decide⟩
  obtain ⟨C,a,order,diagonal⟩ := coordinates T period q hq card
  let u := C.symm c
  let v := C.symm e
  have pc (h z) : P (C (h,z))=C (h+u.1,a^i*z+u.2) := by
    calc
      _ = C (h,a^i*z)+c := by rw [hP,diagonal]
      _ = C ((h,a^i*z)+u) := by rw [map_add]; simp [u]
      _ = _ := rfl
  have qc (h z) : Q (C (h,z))=C (h+v.1,a^j*z+v.2) := by
    calc
      _ = C (h,a^j*z)+e := by rw [hQ,diagonal]
      _ = C ((h,a^j*z)+v) := by rw [map_add]; simp [v]
      _ = _ := rfl
  have periodA : a^11=1 := order ▸ pow_orderOf_eq_one a
  have power (k : ℕ) : (a^k)^11=1 := by
    rw [←pow_mul,Nat.mul_comm,pow_mul,periodA,one_pow]
  by_cases hi : a^i=1
  · by_cases hj : a^j=1
    · have comm : Commute P Q := by
        ext y
        obtain ⟨⟨h,z⟩,rfl⟩ := C.surjective y
        change P (Q (C (h,z)))=Q (P (C (h,z)))
        rw [qc,pc,pc,qc]
        simp only [hi,hj,one_mul]
        apply congrArg C
        apply Prod.ext <;> dsimp <;> abel
      rcases OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1.HaarTransfer.commuting_matchings
        G P Q comm z₀ sepP sepQ sepPQ ι edge₀ edgeP edgeQ with h4|h8|h16
      · exact Or.inl h4
      · exact Or.inr (Or.inl h8)
      · exact Or.inr (Or.inr (Or.inl h16))
    · exact affine_chart q hq (a^j) (a^i) v.2 u.2 (orderOf_eq_prime (power _) hj)
        (power _) C.toEquiv Q P v.1 u.1 qc pc z₀ sepQ sepP (Ne.symm sepPQ) G ι edge₀ edgeQ edgeP
  · exact affine_chart q hq (a^i) (a^j) u.2 v.2 (orderOf_eq_prime (power _) hi)
      (power _) C.toEquiv P Q u.1 v.1 pc qc z₀ sepP sepQ sepPQ G ι edge₀ edgeP edgeQ

end NonfreeEleven.PrimeNormal
end

section
/- Direct cyclic-action interface for the prime moving-coordinate theorem. -/
namespace NonfreeEleven.PrimeNormal

open SimpleGraph
abbrev Eleven := Multiplicative (ZMod 11)

variable {V : Type*} [AddCommGroup V] [DistribMulAction Eleven V]

/-- The additive map induced by the standard generator of the cyclic linear quotient. -/
def generator : V →+ V where
  toFun x := Multiplicative.ofAdd (1 : ZMod 11) • x
  map_zero' := smul_zero _
  map_add' := smul_add _

private theorem generator_power (k : ℕ) :
    Multiplicative.ofAdd (1 : ZMod 11)^k = Multiplicative.ofAdd (k : ZMod 11) := by
  apply Multiplicative.toAdd.injective
  simp [nsmul_eq_mul]

theorem generator_iterate (k : ℕ) (x : V) :
    (generator (V:=V))^[k] x = Multiplicative.ofAdd (k : ZMod 11) • x := by
  change ((Multiplicative.ofAdd (1 : ZMod 11)) • ·)^[k] x = _
  rw [smul_iterate_apply,generator_power]

theorem generator_period (x : V) : (generator (V:=V))^[11] x=x := by
  rw [generator_iterate]
  rw [show ((11 : ℕ) : ZMod 11) = 0 by decide]
  exact one_smul Eleven x

theorem exponent_action (k : Eleven) (x : V) : (generator (V:=V))^[k.toAdd.val] x = k • x := by
  rw [generator_iterate,ZMod.natCast_zmod_val]
  rfl

/-- Direct interface for a cyclic group action and two of its actual linear components. -/
theorem cycles_of_action {X : Type*} [Finite V] (q : ℕ)
    (hq : q=23 ∨ q=67 ∨ q=89 ∨ q=199)
    (card : Nat.card ((generator (V:=V))-AddMonoidHom.id V).range=q)
    (i j : Eleven) (P Q : Equiv.Perm V) (c e : V)
    (hP : ∀ v, P v=i • v+c) (hQ : ∀ v, Q v=j • v+e)
    (z₀ : V) (sepP : P z₀≠z₀) (sepQ : Q z₀≠z₀) (sepPQ : P z₀≠Q z₀)
    (G : SimpleGraph X) (ι : (Bool × V) ↪ X)
    (edge₀ : ∀ v, G.Adj (ι (false,v)) (ι (true,v)))
    (edgeP : ∀ v, G.Adj (ι (false,v)) (ι (true,P v)))
    (edgeQ : ∀ v, G.Adj (ι (false,v)) (ι (true,Q v))) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G :=
  cycles generator generator_period q hq card i.toAdd.val j.toAdd.val P Q c e
    (fun v => (hP v).trans (congrArg (·+c) (exponent_action i v).symm))
    (fun v => (hQ v).trans (congrArg (·+e) (exponent_action j v).symm))
    z₀ sepP sepQ sepPQ G ι edge₀ edgeP edgeQ

end NonfreeEleven.PrimeNormal
end

section
/- # Applying an affine cycle theorem to the exact nonfree index-eleven step -/
namespace NonfreeEleven
open SimpleGraph

/-- The finite affine form of the three-matching cycle assertion. -/
def AffineShort : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Fintype V]
      [DistribMulAction (Multiplicative (ZMod 11)) V]
      (i j : Multiplicative (ZMod 11)) (P Q : V),
      (∀ v : V, i • v+P≠v ∧ j • v+Q≠v ∧ i • v+P≠j • v+Q) →
      ∀ G : SimpleGraph (Bool × V), (∀ v,G.Adj (false,v) (true,v)) →
      (∀ v,G.Adj (false,v) (true,i • v+P)) → (∀ v,G.Adj (false,v) (true,j • v+Q)) →
      cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G

/-- The finite affine case suffices for every orbit of a three-matching action
whose generated group has an abelian normal subgroup of index eleven. -/
theorem from_affine_cycles
    (solve : AffineShort)
    {A X : Type} [Group A] [MulAction A X] [Finite X]
    (f : A →* Multiplicative (ZMod 11)) (onto : Function.Surjective f)
    (abelian : ∀ g h : f.ker,g*h=h*g) (x : X) (a b : A) (moving : f a≠1 ∨ f b≠1)
    (sep : ∀ y : X,a • y≠y ∧ b • y≠y ∧ a • y≠b • y)
    (G : SimpleGraph (Bool × X)) (idEdge : ∀ y,G.Adj (false,y) (true,y))
    (aEdge : ∀ y,G.Adj (false,y) (true,a • y)) (bEdge : ∀ y,G.Adj (false,y) (true,b • y)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  classical
  let _ : Fact (Nat.card (Multiplicative (ZMod 11))).Prime := ⟨by
    have h : Nat.card (Multiplicative (ZMod 11))=11 := by change Nat.card (ZMod 11)=11; simp
    rw [h]; decide⟩
  rcases stabilizer_dichotomy f x with contained|covers
  · exact index_eleven_orbit f onto abelian x contained a b moving sep G idEdge aEdge bEdge
  obtain ⟨V,inst,e,L,c,_,_,act,_,_,_⟩ := affine_orbit_coordinates f abelian x covers
  let C := Multiplicative (ZMod 11)
  let _ : Finite V := Finite.of_injective e e.injective
  let _ : Fintype V := Fintype.ofFinite V
  let _ : DistribMulAction C V := {
    smul := fun k v => (L k).toAdd v
    one_smul := by intro v; change (L 1).toAdd v=v; rw [map_one]; rfl
    mul_smul := by intro i j v; change (L (i*j)).toAdd v=(L i).toAdd ((L j).toAdd v); rw [map_mul]; rfl
    smul_add := fun k v w => map_add _ _ _
    smul_zero := fun k => map_zero _ }
  let ι : (Bool × V) ↪ (Bool × X) := (Function.Embedding.refl Bool).prodMap e
  have act' (g : A) (v : V) : g • e v=e (f g • v+c g) := act g v
  have se (v : V) : f a • v+c a≠v ∧ f b • v+c b≠v ∧ f a • v+c a≠f b • v+c b := by
    have hh := sep (e v)
    rw [act',act'] at hh
    exact ⟨fun h => hh.1 (congrArg e h),fun h => hh.2.1 (congrArg e h),
      fun h => hh.2.2 (congrArg e h)⟩
  have edges (g : A) (h : ∀ y,G.Adj (false,y) (true,g • y)) (v : V) :
      (G.comap ι).Adj (false,v) (true,f g • v+c g) := by
    change G.Adj (false,e v) (true,e (f g • v+c g))
    rw [← act']
    exact h _
  have localCycle := solve V (f a) (f b) (c a) (c b) se (G.comap ι)
    (fun v => idEdge (e v)) (edges a aEdge) (edges b bEdge)
  have embed : G.comap ι ⊑ G := isContained_iff_exists_le_comap.mpr ⟨ι,le_rfl⟩
  exact localCycle.imp (fun h => h.trans embed)
    (fun h => h.imp (fun hh => hh.trans embed) (fun r => r.imp (fun h => h.trans embed) (fun h => h.trans embed)))
end NonfreeEleven
end

section
/- # Power-of-two cycles in finite abelian-by-eleven affine matching actions -/

namespace NonfreeEleven
open SimpleGraph

/-- Every finite affine action with cyclic linear quotient of order eleven has a short
power-of-two cycle when its three matching neighbors are distinct at each point. -/
theorem affine_short_complete : AffineShort := by
  classical
  intro V _ _ _ i j P Q sep G idEdge pEdge qEdge
  let C := Multiplicative (ZMod 11)
  let t : C := Multiplicative.ofAdd (1 : ZMod 11)
  let T := PrimeNormal.generator (V := V)
  let D := T-AddMonoidHom.id V
  let m := Nat.card D.range
  have period (x : V) : T^[11] x=x := PrimeNormal.generator_period x
  by_cases both : i=1 ∧ j=1
  · obtain ⟨rfl,rfl⟩ := both
    have ht := AffineClass.fixed_eleven_action_cycle (1,P) (1,Q)
      (by simp) sep G idEdge pEdge qEdge
    exact ht.imp id (fun h => h.imp id Or.inl)
  have moving : i≠1 ∨ j≠1 := by tauto
  by_cases small : m≤240
  · have options := affine_small_moving_orders T period small
    change m ∈ ([1,11,23,67,89,121,199] : List ℕ) at options
    by_cases smallPlane : m≤11 ∨ m=121
    · exact small_or_121_action_short smallPlane i j P Q sep G idEdge pEdge qEdge
    have primeCase : m=23 ∨ m=67 ∨ m=89 ∨ m=199 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at options
      omega
    let p := (MulAction.toPermHom C V i).trans (Equiv.addRight P)
    let q := (MulAction.toPermHom C V j).trans (Equiv.addRight Q)
    exact PrimeNormal.cycles_of_action m primeCase rfl i j p q P Q (fun _ => rfl) (fun _ => rfl)
      0 (sep 0).1 (sep 0).2.1 (sep 0).2.2 G (Function.Embedding.refl _) idEdge pEdge qEdge
  · have subset : {x : V | ∀ g : C,g • x=x} ⊆ (D.ker : Set V) := by
      intro x hx
      change T x-x=0
      exact sub_eq_zero.mpr (hx t)
    have count : {x : V | ∀ g : C,g • x=x}.ncard≤Nat.card D.ker := Set.ncard_le_ncard subset
    have product : Nat.card D.ker*m=Fintype.card V := by
      rw [← Nat.card_eq_fintype_card]
      change Nat.card D.ker*Nat.card D.range=Nat.card V
      rw [← AddSubgroup.index_ker,D.ker.card_mul_index]
    have room : 240*{x : V | ∀ g : C,g • x=x}.ncard<Fintype.card V := by
      calc
        _ ≤ Nat.card D.ker*240 := by rw [Nat.mul_comm]; exact Nat.mul_le_mul_right _ count
        _ < Nat.card D.ker*m := Nat.mul_lt_mul_of_pos_left (Nat.lt_of_not_ge small) Nat.card_pos
        _ = _ := product
    have at0 := sep 0
    simp only [smul_zero,zero_add] at at0
    have distinct : (i,P)≠((1,0) : C × V) ∧ (j,Q)≠((1,0) : C × V) ∧ (i,P)≠(j,Q) :=
      ⟨fun h => at0.1 (congrArg Prod.snd h),fun h => at0.2.1 (congrArg Prod.snd h),
        fun h => at0.2.2 (congrArg Prod.snd h)⟩
    exact large_affine_eleven_cycle room (i,P) (j,Q) moving distinct G idEdge pEdge qEdge
end NonfreeEleven
end

section
/- # Short cycles from two permutations with an abelian normal subgroup of index eleven
Codex, gpt-6.2-astra. -/

namespace NonfreeEleven
open SimpleGraph

/-- If the permutations defining a separated matching triple generate a group with
an abelian normal subgroup of index eleven, every graph containing these three
matchings has a cycle of length 4, 8, 16 or 32. -/
theorem index_eleven_matching_cycle {X : Type} [Finite X] [Nonempty X]
    (p q : Equiv.Perm X) (sep : ∀ x : X,p x≠x ∧ q x≠x ∧ p x≠q x)
    (index_eleven : ∃ N : Subgroup (Subgroup.closure ({p,q} : Set (Equiv.Perm X))),
      N.Normal ∧ IsMulCommutative N ∧ N.index=11)
    (G : SimpleGraph (Bool × X))
    (idEdge : ∀ x,G.Adj (false,x) (true,x))
    (pEdge : ∀ x,G.Adj (false,x) (true,p x))
    (qEdge : ∀ x,G.Adj (false,x) (true,q x)) :
    cycleGraph 4 ⊑ G ∨ cycleGraph 8 ⊑ G ∨ cycleGraph 16 ⊑ G ∨ cycleGraph 32 ⊑ G := by
  classical
  obtain ⟨N,normal,comm,idx⟩ := index_eleven
  let K := Subgroup.closure ({p,q} : Set (Equiv.Perm X))
  let x : X := Classical.choice inferInstance
  have card : Nat.card (K ⧸ N)=11 := N.index_eq_card.symm.trans idx
  have zcard : Nat.card (Multiplicative (ZMod 11))=11 := by change Nat.card (ZMod 11)=11; simp
  let _ : Fact (Nat.Prime 11) := ⟨by decide⟩
  let e := mulEquivOfPrimeCardEq card zcard
  let f := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have onto : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective N)
  have ker : f.ker=N := (MonoidHom.ker_comp_of_injective _ _ e.injective).trans (QuotientGroup.ker_mk' _)
  have abelian (g h : f.ker) : g*h=h*g := by
    have hg : (g : K) ∈ N := ker ▸ g.property
    have hh : (h : K) ∈ N := ker ▸ h.property
    apply Subtype.ext
    exact congrArg (fun z : N => (z:K)) (comm.is_comm.comm (⟨g,hg⟩ : N) (⟨h,hh⟩ : N))
  let a : K := ⟨p,Subgroup.subset_closure (by simp)⟩
  let b : K := ⟨q,Subgroup.subset_closure (by simp)⟩
  have gen : Subgroup.closure ({a,b} : Set K)=⊤ := by
    apply Subgroup.map_injective (f := K.subtype) Subtype.coe_injective
    rw [MonoidHom.map_closure,←MonoidHom.range_eq_map,Subgroup.subtype_range,Set.image_pair]
    rfl
  have moving : f a≠1 ∨ f b≠1 := by
    by_contra! trivial
    have hle : Subgroup.closure ({a,b} : Set K) ≤ f.ker :=
      (Subgroup.closure_le f.ker).mpr (by
        intro c hc
        rcases hc with h|h
        · exact h ▸ trivial.1
        · exact (Set.mem_singleton_iff.mp h) ▸ trivial.2)
    rw [gen,ker] at hle
    have nt : N=⊤ := top_unique hle
    rw [nt,Subgroup.index_top] at idx
    contradiction
  exact from_affine_cycles affine_short_complete f onto abelian x a b moving sep
    G idEdge pEdge qEdge

end NonfreeEleven
end

section
open SimpleGraph

/-- The complementary stabilizer step of the index-eleven reduction. -/
theorem OMA.solution : OMA.R_Erdos64_erdos_64_R1_H1_R1_H1_R1_H2_R1_H2_R1.H2 := by
  intro X _ _ p q sep _ _ _ N normal comm idx _
  let G := SimpleGraph.fromRel (fun u v : Bool × X =>
    u.1=false ∧ v.1=true ∧ (v.2=u.2 ∨ v.2=p u.2 ∨ v.2=q u.2))
  obtain h|h|h|h := NonfreeEleven.index_eleven_matching_cycle p q sep ⟨N,normal,comm,idx⟩ G
    (fun y => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inl rfl⟩⟩)
    (fun y => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inl rfl)⟩⟩)
    (fun y => ⟨by simp,Or.inl ⟨rfl,rfl,Or.inr (Or.inr rfl)⟩⟩)
  · exact ⟨2,by decide,h⟩
  · exact ⟨3,by decide,h⟩
  · exact ⟨4,by decide,h⟩
  · exact ⟨5,by decide,h⟩
end
