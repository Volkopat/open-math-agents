import OMAStatements.S_mo_144090

/-!
# A finite nilpotent counterexample to generation by the penultimate Engel complement

The group is UT(6,2), the upper unitriangular group over the two-element field.
Its successive commutators lose a superdiagonal at every step. At the fourth step
only the top-right entry can remain. The second through fourth first-superdiagonal
entries of every non-left-4-Engel element must be equal.
-/

namespace OMA.S_mo_144090
namespace UT6

/-- The entries strictly above the diagonal of a binary upper unitriangular matrix. -/
structure U where
  a01 : ZMod 2
  a12 : ZMod 2
  a23 : ZMod 2
  a34 : ZMod 2
  a45 : ZMod 2
  a02 : ZMod 2
  a13 : ZMod 2
  a24 : ZMod 2
  a35 : ZMod 2
  a03 : ZMod 2
  a14 : ZMod 2
  a25 : ZMod 2
  a04 : ZMod 2
  a15 : ZMod 2
  a05 : ZMod 2
  deriving DecidableEq

private theorem U.ext_coords {x y : U}
    (h01 : x.a01 = y.a01) (h12 : x.a12 = y.a12) (h23 : x.a23 = y.a23) (h34 : x.a34 = y.a34) (h45 : x.a45 = y.a45) (h02 : x.a02 = y.a02) (h13 : x.a13 = y.a13) (h24 : x.a24 = y.a24) (h35 : x.a35 = y.a35) (h03 : x.a03 = y.a03) (h14 : x.a14 = y.a14) (h25 : x.a25 = y.a25) (h04 : x.a04 = y.a04) (h15 : x.a15 = y.a15) (h05 : x.a05 = y.a05) : x=y := by
  cases x; cases y; simp_all

private def ident : U := ⟨0,0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩

private def prod (x y : U) : U where
  a01 := x.a01 + y.a01
  a12 := x.a12 + y.a12
  a23 := x.a23 + y.a23
  a34 := x.a34 + y.a34
  a45 := x.a45 + y.a45
  a02 := x.a02 + y.a02 + x.a01*y.a12
  a13 := x.a13 + y.a13 + x.a12*y.a23
  a24 := x.a24 + y.a24 + x.a23*y.a34
  a35 := x.a35 + y.a35 + x.a34*y.a45
  a03 := x.a03 + y.a03 + x.a01*y.a13 + x.a02*y.a23
  a14 := x.a14 + y.a14 + x.a12*y.a24 + x.a13*y.a34
  a25 := x.a25 + y.a25 + x.a23*y.a35 + x.a24*y.a45
  a04 := x.a04 + y.a04 + x.a01*y.a14 + x.a02*y.a24 + x.a03*y.a34
  a15 := x.a15 + y.a15 + x.a12*y.a25 + x.a13*y.a35 + x.a14*y.a45
  a05 := x.a05 + y.a05 + x.a01*y.a15 + x.a02*y.a25 + x.a03*y.a35 + x.a04*y.a45

private def inv (x : U) : U :=
  let z01 := -x.a01
  let z12 := -x.a12
  let z23 := -x.a23
  let z34 := -x.a34
  let z45 := -x.a45
  let z02 := -x.a02 - z01*x.a12
  let z13 := -x.a13 - z12*x.a23
  let z24 := -x.a24 - z23*x.a34
  let z35 := -x.a35 - z34*x.a45
  let z03 := -x.a03 - z01*x.a13 - z02*x.a23
  let z14 := -x.a14 - z12*x.a24 - z13*x.a34
  let z25 := -x.a25 - z23*x.a35 - z24*x.a45
  let z04 := -x.a04 - z01*x.a14 - z02*x.a24 - z03*x.a34
  let z15 := -x.a15 - z12*x.a25 - z13*x.a35 - z14*x.a45
  let z05 := -x.a05 - z01*x.a15 - z02*x.a25 - z03*x.a35 - z04*x.a45
  ⟨z01,z12,z23,z34,z45,z02,z13,z24,z35,z03,z14,z25,z04,z15,z05⟩

instance : Group U where
  one := ident
  mul := prod
  inv := inv
  mul_assoc a b c := by change prod (prod a b) c = prod a (prod b c); apply U.ext_coords <;> dsimp only [prod] <;> ring
  one_mul a := by change prod ident a = a; apply U.ext_coords <;> simp [prod,ident]
  mul_one a := by change prod a ident = a; apply U.ext_coords <;> simp [prod,ident]
  inv_mul_cancel a := by change prod (inv a) a = ident; apply U.ext_coords <;> dsimp only [prod,inv,ident] <;> ring

private def coords : U ≃ (Fin 15 → ZMod 2) :=
    ⟨fun u => ![u.a01,u.a12,u.a23,u.a34,u.a45,u.a02,u.a13,u.a24,u.a35,u.a03,u.a14,u.a25,u.a04,u.a15,u.a05],
     fun f => ⟨f 0,f 1,f 2,f 3,f 4,f 5,f 6,f 7,f 8,f 9,f 10,f 11,f 12,f 13,f 14⟩,fun _ => rfl,fun f => by funext i; fin_cases i <;> rfl⟩

instance : Fintype U := Fintype.ofEquiv _ coords.symm

private theorem card_U : Nat.card U = 2^15 := by
  rw [Nat.card_congr coords, Nat.card_fun]
  norm_num

private theorem nil_U : Group.IsNilpotent U :=
  (show IsPGroup 2 U from isPGroup_iff_card_dvd_pow.mpr ⟨15,by rw [card_U]⟩).isNilpotent

private theorem relation (x y : U) (n : ℕ) :
    prod (prod y (comm x y n)) (comm x y (n+1)) = prod (comm x y n) y := by
  change (y*comm x y n)*((comm x y n)⁻¹*y⁻¹*comm x y n*y) = comm x y n * y
  group

/-- Compare the (i,j) entries of (y*a)*c = a*y. Each entry of c is determined by
the entries below that superdiagonal. -/
private theorem entries (a y c : U) (e : prod (prod y a) c = prod a y) :
    c.a01 = 0 ∧
    c.a12 = 0 ∧
    c.a23 = 0 ∧
    c.a34 = 0 ∧
    c.a45 = 0 ∧
    c.a02 = (a.a01*y.a12-y.a01*a.a12-(prod y a).a01*c.a12) ∧
    c.a13 = (a.a12*y.a23-y.a12*a.a23-(prod y a).a12*c.a23) ∧
    c.a24 = (a.a23*y.a34-y.a23*a.a34-(prod y a).a23*c.a34) ∧
    c.a35 = (a.a34*y.a45-y.a34*a.a45-(prod y a).a34*c.a45) ∧
    c.a03 = (a.a01*y.a13-y.a01*a.a13-(prod y a).a01*c.a13) + (a.a02*y.a23-y.a02*a.a23-(prod y a).a02*c.a23) ∧
    c.a14 = (a.a12*y.a24-y.a12*a.a24-(prod y a).a12*c.a24) + (a.a13*y.a34-y.a13*a.a34-(prod y a).a13*c.a34) ∧
    c.a25 = (a.a23*y.a35-y.a23*a.a35-(prod y a).a23*c.a35) + (a.a24*y.a45-y.a24*a.a45-(prod y a).a24*c.a45) ∧
    c.a04 = (a.a01*y.a14-y.a01*a.a14-(prod y a).a01*c.a14) + (a.a02*y.a24-y.a02*a.a24-(prod y a).a02*c.a24) + (a.a03*y.a34-y.a03*a.a34-(prod y a).a03*c.a34) ∧
    c.a15 = (a.a12*y.a25-y.a12*a.a25-(prod y a).a12*c.a25) + (a.a13*y.a35-y.a13*a.a35-(prod y a).a13*c.a35) + (a.a14*y.a45-y.a14*a.a45-(prod y a).a14*c.a45) ∧
    c.a05 = (a.a01*y.a15-y.a01*a.a15-(prod y a).a01*c.a15) + (a.a02*y.a25-y.a02*a.a25-(prod y a).a02*c.a25) + (a.a03*y.a35-y.a03*a.a35-(prod y a).a03*c.a35) + (a.a04*y.a45-y.a04*a.a45-(prod y a).a04*c.a45) := by
  have e01 := congrArg U.a01 e
  have e12 := congrArg U.a12 e
  have e23 := congrArg U.a23 e
  have e34 := congrArg U.a34 e
  have e45 := congrArg U.a45 e
  have e02 := congrArg U.a02 e
  have e13 := congrArg U.a13 e
  have e24 := congrArg U.a24 e
  have e35 := congrArg U.a35 e
  have e03 := congrArg U.a03 e
  have e14 := congrArg U.a14 e
  have e25 := congrArg U.a25 e
  have e04 := congrArg U.a04 e
  have e15 := congrArg U.a15 e
  have e05 := congrArg U.a05 e
  dsimp only [prod] at e01 e12 e23 e34 e45 e02 e13 e24 e35 e03 e14 e25 e04 e15 e05 ⊢
  exact ⟨by linear_combination e01,
    by linear_combination e12,
    by linear_combination e23,
    by linear_combination e34,
    by linear_combination e45,
    by linear_combination e02,
    by linear_combination e13,
    by linear_combination e24,
    by linear_combination e35,
    by linear_combination e03,
    by linear_combination e14,
    by linear_combination e25,
    by linear_combination e04,
    by linear_combination e15,
    by linear_combination e05⟩

private theorem layer1 (a y c : U)
    (e : prod (prod y a) c = prod a y) :
    c.a01=0 ∧
    c.a12=0 ∧
    c.a23=0 ∧
    c.a34=0 ∧
    c.a45=0 ∧
    c.a02=a.a01*y.a12-y.a01*a.a12 ∧
    c.a13=a.a12*y.a23-y.a12*a.a23 ∧
    c.a24=a.a23*y.a34-y.a23*a.a34 ∧
    c.a35=a.a34*y.a45-y.a34*a.a45 := by
  obtain ⟨r01,r12,r23,r34,r45,r02,r13,r24,r35,_⟩ := entries a y c e
  simp [r01, r12, r23, r34, r45, r02, r13, r24, r35, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

private theorem layer2 (a y c : U)
    (p : a.a01=0 ∧ a.a12=0 ∧ a.a23=0 ∧ a.a34=0 ∧ a.a45=0)
    (e : prod (prod y a) c = prod a y) :
    c.a01=0 ∧
    c.a12=0 ∧
    c.a23=0 ∧
    c.a34=0 ∧
    c.a45=0 ∧
    c.a02=0 ∧
    c.a13=0 ∧
    c.a24=0 ∧
    c.a35=0 ∧
    c.a03=a.a02*y.a23-y.a01*a.a13 ∧
    c.a14=a.a13*y.a34-y.a12*a.a24 ∧
    c.a25=a.a24*y.a45-y.a23*a.a35 := by
  obtain ⟨p01,p12,p23,p34,p45⟩ := p
  obtain ⟨r01,r12,r23,r34,r45,r02,r13,r24,r35,r03,r14,r25,_⟩ := entries a y c e
  simp [r01, r12, r23, r34, r45, r02, r13, r24, r35, r03, r14, r25, p01, p12, p23, p34, p45, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

private theorem layer3 (a y c : U)
    (p : a.a01=0 ∧ a.a12=0 ∧ a.a23=0 ∧ a.a34=0 ∧ a.a45=0 ∧ a.a02=0 ∧ a.a13=0 ∧ a.a24=0 ∧ a.a35=0)
    (e : prod (prod y a) c = prod a y) :
    c.a01=0 ∧
    c.a12=0 ∧
    c.a23=0 ∧
    c.a34=0 ∧
    c.a45=0 ∧
    c.a02=0 ∧
    c.a13=0 ∧
    c.a24=0 ∧
    c.a35=0 ∧
    c.a03=0 ∧
    c.a14=0 ∧
    c.a25=0 ∧
    c.a04=a.a03*y.a34-y.a01*a.a14 ∧
    c.a15=a.a14*y.a45-y.a12*a.a25 := by
  obtain ⟨p01,p12,p23,p34,p45,p02,p13,p24,p35⟩ := p
  obtain ⟨r01,r12,r23,r34,r45,r02,r13,r24,r35,r03,r14,r25,r04,r15,_⟩ := entries a y c e
  simp [r01, r12, r23, r34, r45, r02, r13, r24, r35, r03, r14, r25, r04, r15, p01, p12, p23, p34, p45, p02, p13, p24, p35, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

private theorem layer4 (a y c : U)
    (p : a.a01=0 ∧ a.a12=0 ∧ a.a23=0 ∧ a.a34=0 ∧ a.a45=0 ∧ a.a02=0 ∧ a.a13=0 ∧ a.a24=0 ∧ a.a35=0 ∧ a.a03=0 ∧ a.a14=0 ∧ a.a25=0)
    (e : prod (prod y a) c = prod a y) :
    c.a01=0 ∧
    c.a12=0 ∧
    c.a23=0 ∧
    c.a34=0 ∧
    c.a45=0 ∧
    c.a02=0 ∧
    c.a13=0 ∧
    c.a24=0 ∧
    c.a35=0 ∧
    c.a03=0 ∧
    c.a14=0 ∧
    c.a25=0 ∧
    c.a04=0 ∧
    c.a15=0 ∧
    c.a05=a.a04*y.a45-y.a01*a.a15 := by
  obtain ⟨p01,p12,p23,p34,p45,p02,p13,p24,p35,p03,p14,p25⟩ := p
  obtain ⟨r01,r12,r23,r34,r45,r02,r13,r24,r35,r03,r14,r25,r04,r15,r05⟩ := entries a y c e
  simp [r01, r12, r23, r34, r45, r02, r13, r24, r35, r03, r14, r25, r04, r15, r05, p01, p12, p23, p34, p45, p02, p13, p24, p35, p03, p14, p25, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

private theorem layer5 (a y c : U)
    (p : a.a01=0 ∧ a.a12=0 ∧ a.a23=0 ∧ a.a34=0 ∧ a.a45=0 ∧ a.a02=0 ∧ a.a13=0 ∧ a.a24=0 ∧ a.a35=0 ∧ a.a03=0 ∧ a.a14=0 ∧ a.a25=0 ∧ a.a04=0 ∧ a.a15=0)
    (e : prod (prod y a) c = prod a y) :
    c.a01=0 ∧
    c.a12=0 ∧
    c.a23=0 ∧
    c.a34=0 ∧
    c.a45=0 ∧
    c.a02=0 ∧
    c.a13=0 ∧
    c.a24=0 ∧
    c.a35=0 ∧
    c.a03=0 ∧
    c.a14=0 ∧
    c.a25=0 ∧
    c.a04=0 ∧
    c.a15=0 ∧
    c.a05=0 := by
  obtain ⟨p01,p12,p23,p34,p45,p02,p13,p24,p35,p03,p14,p25,p04,p15⟩ := p
  obtain ⟨r01,r12,r23,r34,r45,r02,r13,r24,r35,r03,r14,r25,r04,r15,r05⟩ := entries a y c e
  simp [r01, r12, r23, r34, r45, r02, r13, r24, r35, r03, r14, r25, r04, r15, r05, p01, p12, p23, p34, p45, p02, p13, p24, p35, p03, p14, p25, p04, p15, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

private theorem fourth (x y : U) :
    (comm x y 4).a01=0 ∧ (comm x y 4).a12=0 ∧ (comm x y 4).a23=0 ∧ (comm x y 4).a34=0 ∧ (comm x y 4).a45=0 ∧ (comm x y 4).a02=0 ∧ (comm x y 4).a13=0 ∧ (comm x y 4).a24=0 ∧ (comm x y 4).a35=0 ∧ (comm x y 4).a03=0 ∧ (comm x y 4).a14=0 ∧ (comm x y 4).a25=0 ∧ (comm x y 4).a04=0 ∧ (comm x y 4).a15=0 ∧
    (comm x y 4).a05 = x.a01*y.a12*y.a23*y.a34*y.a45 + y.a01*y.a12*y.a23*y.a34*x.a45 := by
  obtain ⟨q101,q112,q123,q134,q145,q102,q113,q124,q135⟩ := layer1 x y _ (relation x y 0)
  obtain ⟨q201,q212,q223,q234,q245,q202,q213,q224,q235,q203,q214,q225⟩ := layer2 _ y _ ⟨q101,q112,q123,q134,q145⟩ (relation x y 1)
  obtain ⟨q301,q312,q323,q334,q345,q302,q313,q324,q335,q303,q314,q325,q304,q315⟩ := layer3 _ y _ ⟨q201,q212,q223,q234,q245,q202,q213,q224,q235⟩ (relation x y 2)
  obtain ⟨q401,q412,q423,q434,q445,q402,q413,q424,q435,q403,q414,q425,q404,q415,q405⟩ := layer4 _ y _ ⟨q301,q312,q323,q334,q345,q302,q313,q324,q335,q303,q314,q325⟩ (relation x y 3)
  refine ⟨q401,q412,q423,q434,q445,q402,q413,q424,q435,q403,q414,q425,q404,q415,?_⟩
  rw [q405]
  rw [q304,q315]
  rw [q203,q214,q225]
  rw [q102,q113,q124,q135]
  ring_nf
  simp only [show (4 : ZMod 2)=0 by decide, show (6 : ZMod 2)=0 by decide, mul_zero, sub_zero, add_zero]

private theorem fifth (x y : U) : comm x y 5 = 1 := by
  obtain ⟨p01,p12,p23,p34,p45,p02,p13,p24,p35,p03,p14,p25,p04,p15,_⟩ := fourth x y
  obtain ⟨q01,q12,q23,q34,q45,q02,q13,q24,q35,q03,q14,q25,q04,q15,q05⟩ := layer5 _ y _ ⟨p01,p12,p23,p34,p45,p02,p13,p24,p35,p03,p14,p25,p04,p15⟩ (relation x y 4)
  exact U.ext_coords q01 q12 q23 q34 q45 q02 q13 q24 q35 q03 q14 q25 q04 q15 q05

private def middle : Subgroup U where
  carrier := {u | u.a12 = u.a23 ∧ u.a23 = u.a34}
  one_mem' := ⟨rfl,rfl⟩
  mul_mem' := by
    intro x y hx hy
    exact ⟨congrArg₂ (·+·) hx.1 hy.1,congrArg₂ (·+·) hx.2 hy.2⟩
  inv_mem' := by
    intro x hx
    exact ⟨congrArg Neg.neg hx.1,congrArg Neg.neg hx.2⟩

private theorem zero_mid (a b c : ZMod 2) (h : ¬ (a=b ∧ b=c)) : a*b*c=0 := by
  revert a b c
  decide

private theorem four_trivial {y : U} (hy : y ∉ middle) (x : U) : comm x y 4=1 := by
  obtain ⟨p01,p12,p23,p34,p45,p02,p13,p24,p35,p03,p14,p25,p04,p15,e⟩ := fourth x y
  apply U.ext_coords p01 p12 p23 p34 p45 p02 p13 p24 p35 p03 p14 p25 p04 p15
  change (comm x y 4).a05 = 0
  rw [e]
  linear_combination (x.a01*y.a45+y.a01*x.a45) * zero_mid _ _ _ hy

private def witnessX : U := ⟨1,0,1,0,0,0,0,0,0,0,0,0,0,0,0⟩
private def witnessY : U := ⟨1,1,1,1,1,0,0,0,0,0,0,0,0,0,0⟩
private def outside : U := ⟨0,1,0,0,0,0,0,0,0,0,0,0,0,0,0⟩

private theorem fourth_nontrivial : comm witnessX witnessY 4 ≠ 1 := by
  intro h
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,e⟩ := fourth witnessX witnessY
  rw [h] at e
  exact (by decide : ¬ ((1:U).a05 = witnessX.a01*witnessY.a12*witnessY.a23*witnessY.a34*witnessY.a45+witnessY.a01*witnessY.a12*witnessY.a23*witnessY.a34*witnessX.a45)) e

private lemma stable (x y : U) {m : ℕ} (hm : comm x y m=1) (r : ℕ) :
    comm x y (m+r)=1 := by
  induction r with
  | zero => exact hm
  | succ r ih => change (comm x y (m+r))⁻¹*y⁻¹*(comm x y (m+r))*y=1; rw [ih]; simp

theorem counterexample :
    Group.IsNilpotent U ∧ leftEngel U 5 = Set.univ ∧
    (∀ m : ℕ, 0 < m → m < 5 → leftEngel U m ≠ Set.univ) ∧
    Subgroup.closure (leftEngel U 4)ᶜ ≠ ⊤ := by
  refine ⟨nil_U,Set.eq_univ_iff_forall.mpr (fun y x => fifth x y),?_,?_⟩
  · intro m _ hm hall
    have he := Set.eq_univ_iff_forall.mp hall witnessY
    have h4 := stable witnessX witnessY (he witnessX) (4-m)
    exact fourth_nontrivial (by rwa [show m+(4-m)=4 by omega] at h4)
  · have inc : Subgroup.closure (leftEngel U 4)ᶜ ≤ middle := by
      rw [Subgroup.closure_le]
      intro y hy
      by_contra hout
      exact hy (fun x => four_trivial hout x)
    intro hall
    have hv := inc (show outside ∈ Subgroup.closure (leftEngel U 4)ᶜ by rw [hall]; trivial)
    exact (by decide : (1:ZMod 2) ≠ 0) hv.1

/-- Restricting to two explicit matrices still gives a counterexample. -/
def pairGroup : Subgroup U := Subgroup.closure {witnessX,witnessY}

private theorem pair_map (x y : pairGroup) (n : ℕ) :
    ((comm (G := pairGroup) x y n : pairGroup) : U) = comm (x:U) (y:U) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [comm, Subgroup.coe_mul, Subgroup.coe_inv, ih]

theorem pair_counterexample :
    Group.IsNilpotent pairGroup ∧ leftEngel pairGroup 5 = Set.univ ∧
    (∀ m : ℕ, 0 < m → m < 5 → leftEngel pairGroup m ≠ Set.univ) ∧
    Subgroup.closure (leftEngel pairGroup 4)ᶜ ≠ ⊤ := by
  let : Group.IsNilpotent U := nil_U
  let x : pairGroup := ⟨witnessX,Subgroup.subset_closure (by simp)⟩
  let y : pairGroup := ⟨witnessY,Subgroup.subset_closure (by simp)⟩
  refine ⟨inferInstance,Set.eq_univ_iff_forall.mpr (fun y x => Subtype.ext ((pair_map x y 5).trans (fifth _ _))),?_,?_⟩
  · intro m _ hm hall
    have hxy : comm x y m = 1 := (Set.eq_univ_iff_forall.mp hall y) x
    have he : comm witnessX witnessY m = 1 :=
      (pair_map x y m).symm.trans (congrArg (fun v : pairGroup => (v : U)) hxy)
    have h4 := stable witnessX witnessY he (4-m)
    exact fourth_nontrivial (by rwa [show m+(4-m)=4 by omega] at h4)
  · have inc : Subgroup.closure (leftEngel pairGroup 4)ᶜ ≤ middle.comap pairGroup.subtype := by
      rw [Subgroup.closure_le]
      intro y hy
      by_contra hout
      exact hy (fun x => Subtype.ext ((pair_map x y 4).trans (four_trivial hout x)))
    intro hall
    have hv := inc (show x ∈ Subgroup.closure (leftEngel pairGroup 4)ᶜ by rw [hall]; trivial)
    exact (by decide : (0:ZMod 2) ≠ 1) hv.1

end UT6
end OMA.S_mo_144090

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_144090.main) := by
  intro h
  obtain ⟨hnil,hall,hmin,hgen⟩ := OMA.S_mo_144090.UT6.counterexample
  let : Group.IsNilpotent OMA.S_mo_144090.UT6.U := hnil
  exact hgen (h OMA.S_mo_144090.UT6.U 5 (by decide) hall hmin)
