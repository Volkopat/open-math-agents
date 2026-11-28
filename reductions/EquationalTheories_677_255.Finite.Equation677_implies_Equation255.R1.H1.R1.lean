import OMAReductions.R_EquationalTheories_677_255_Finite_Equation677_implies_Equation255_R1
/-!
A regular group quotient of the action by left translations forces all columns
of a congruence-simple E677 magma to be injective. This excludes nilpotent row
groups and reduces the problem to two permutation-group questions.
Credit: @AlfredMelson.
-/
namespace OMA.R_EquationalTheories_677_255_Finite_Equation677_implies_Equation255_R1_H1_R1
open EquationalTheories_677_255 OMA.R_EquationalTheories_677_255_Finite_Equation677_implies_Equation255_R1

/-- Primitive permutation case. The permutations labelling the points generate
the action. A nonnormal maximal stabilizer rules out regular primitive actions. -/
def H1 : Prop :=
  ∀ (X K : Type) [Finite X] [Group K] [Finite K] [MulAction K X]
    [FaithfulSMul K X] [MulAction.IsPreprimitive K X] (o : X) (L : X → K),
    Subgroup.closure (Set.range L) = ⊤ →
    ¬ (MulAction.stabilizer K o).Normal →
    (∀ x y : X, L y • (L x • (L (L y • x) • y)) = x) →
    ∀ x : X, L (L (L x • x) • x) • x = x

/-- Imprimitive permutation case. The stabilizer of a point is strictly smaller
than the stabilizer of a maximal block and normally generates the whole row
group. It suffices to find any proper multiplication congruence in a bad model. -/
def H2 : Prop :=
  ∀ (G K : Type) [Magma G] [Finite G] [Group K] [Finite K] [MulAction K G]
    [FaithfulSMul K G] (L : G → K), Subgroup.closure (Set.range L) = ⊤ →
    (∀ y x, L y • x = y ◇ x) → Equation677 G →
    ∀ (o : G) (M : Subgroup K), IsCoatom M → ¬ M.Normal →
    MulAction.stabilizer K o < M →
    Subgroup.normalClosure (MulAction.stabilizer K o : Set K) = ⊤ →
    3 ≤ M.index → 2 ≤ (MulAction.stabilizer K o).relIndex M →
    (MulAction.stabilizer K o).relIndex M * M.index = Nat.card G →
    ¬ Equation255 G →
    ∃ r : Setoid G, r ≠ ⊥ ∧ r ≠ ⊤ ∧
      ∀ a b c d, r.r a c → r.r b d → r.r (a ◇ b) (c ◇ d)

variable {G : Type} [Magma G] {A : Type*} [Group A]

theorem multiplier {π g : G → A} (h : Equation677 G)
    (action : ∀ y x, π (y ◇ x) = g y * π x) (y x : G) :
    g (y ◇ x) = (g x)⁻¹ * (g y)⁻¹ * π x * (π y)⁻¹ := by
  have he := congrArg π (h x y)
  simp only [action] at he
  calc g (y ◇ x) = (g x)⁻¹ * (g y)⁻¹ * (g y * (g x * (g (y ◇ x) * π y))) * (π y)⁻¹ := by group
       _ = _ := by rw [←he]

theorem coordinates {π g : G → A} (h : Equation677 G) (action : ∀ y x, π (y ◇ x) = g y * π x) :
    ∀ a b c d, (π a,g a) = (π c,g c) → (π b,g b) = (π d,g d) →
      (π (a ◇ b),g (a ◇ b)) = (π (c ◇ d),g (c ◇ d)) := by
  intro a b c d h1 h2
  obtain ⟨ac,ac'⟩ := Prod.mk.inj h1
  obtain ⟨bd,bd'⟩ := Prod.mk.inj h2
  simp only [action,multiplier h action,ac,ac',bd,bd']

theorem collision {π g : G → A} (h : Equation677 G) (action : ∀ y x, π (y ◇ x) = g y * π x)
    {a b x : G} (he : a ◇ x = b ◇ x) : (π a,g a) = (π b,g b) := by
  have h1 := congrArg π he
  simp only [action, mul_right_cancel_iff] at h1
  have h2 := congrArg g he
  simp only [multiplier h action,h1,mul_left_cancel_iff, inv_inj] at h2
  exact Prod.ext h2 h1

theorem regular_factor {π g : G → A} (h : Equation677 G) (action : ∀ y x, π (y ◇ x) = g y * π x)
    (simple : ∀ r : Setoid G, (∀ a b c d, r.r a c → r.r b d → r.r (a ◇ b) (c ◇ d)) →
      r = ⊥ ∨ r = ⊤) (nonconstant : ∃ a b, π a ≠ π b) :
    ∀ x : G, Function.Injective (fun a : G => a ◇ x) := by
  let r := Setoid.ker fun a : G => (π a,g a)
  rcases simple r (coordinates h action) with trivial | total
  · intro x a b he
    have hr : r.r a b := collision h action he
    rw [trivial] at hr
    exact hr
  · obtain ⟨a,b,hab⟩ := nonconstant
    have hr : r.r a b := by rw [total]; trivial
    exact False.elim (hab (congrArg Prod.fst hr))
section GroupAction
variable {K : Type*} [Group K] [MulAction K G]

theorem transitive_rows (h : Equation677 G) (L : G → K) (act : ∀ y x, L y • x = y ◇ x)
    (y x : G) : ∃ t : K, t • y = x := by
  refine ⟨L y * L x * L (y ◇ x),?_⟩
  simpa only [mul_smul, act] using (h x y).symm

theorem columns_of_normal_factor (h : Equation677 G) (L : G → K) (act : ∀ y x, L y • x = y ◇ x)
    (simple : ∀ r : Setoid G, (∀ a b c d, r.r a c → r.r b d → r.r (a ◇ b) (c ◇ d)) →
      r = ⊥ ∨ r = ⊤)
    (o : G) (N : Subgroup K) [N.Normal] (proper : N ≠ ⊤) (stab : MulAction.stabilizer K o ≤ N) :
    ∀ x : G, Function.Injective (fun a : G => a ◇ x) := by
  classical
  choose lift hl using transitive_rows h L act o
  let f := QuotientGroup.mk' N
  let π (x : G) := f (lift x)
  have canonical (t : K) : π (t • o) = f t := by
    have rel : (lift (t • o))⁻¹ * t ∈ MulAction.stabilizer K o := by
      rw [MulAction.mem_stabilizer_iff,mul_smul,inv_smul_eq_iff]
      exact (hl _).symm
    have eq : f ((lift (t • o))⁻¹ * t) = 1 := (QuotientGroup.eq_one_iff _).mpr (stab rel)
    rw [map_mul,map_inv,inv_mul_eq_one] at eq
    exact eq
  apply regular_factor (π := π) (g := fun y => f (L y)) h _ simple
  · obtain ⟨t,ht⟩ : ∃ t : K, t ∉ N := by
      by_contra! all
      exact proper (top_unique fun t _ => all t)
    refine ⟨t • o,(1 : K) • o,?_⟩
    simp only [canonical,map_one]
    exact fun e => ht ((QuotientGroup.eq_one_iff t).mp e)
  · intro y x
    rw [←act, ←hl x, ←mul_smul, canonical, map_mul, canonical]

theorem columns_of_nilpotent [Finite K] [Group.IsNilpotent K]
    (h : Equation677 G) (L : G → K) (act : ∀ y x, L y • x = y ◇ x)
    (simple : ∀ r : Setoid G, (∀ a b c d, r.r a c → r.r b d → r.r (a ◇ b) (c ◇ d)) →
      r = ⊥ ∨ r = ⊤) : ∀ x : G, Function.Injective (fun a : G => a ◇ x) := by
  intro o
  rcases eq_top_or_exists_le_coatom (MulAction.stabilizer K o) with ht | ⟨N,hm,hs⟩
  · intro a b _
    have fixed (x : G) : o = x := by
      obtain ⟨t,e⟩ := transitive_rows h L act o x
      have mem : t ∈ MulAction.stabilizer K o := ht ▸ Subgroup.mem_top t
      exact ((MulAction.mem_stabilizer_iff.mp mem).symm.trans e)
    exact (fixed a).symm.trans (fixed b)
  · have : N.Normal := Group.isNilpotent_of_finite_tfae.out 0 2 rfl rfl |>.mp inferInstance N hm
    exact columns_of_normal_factor h L act simple o N hm.1 hs o

end GroupAction
/-- A column collision forces the stabilizer to normally generate the group. -/
lemma stabilizer_generates {K : Type} [Group K] [MulAction K G]
    (h : Equation677 G) (L : G → K) (act : ∀ y x, L y • x = y ◇ x)
    (simple : ∀ r : Setoid G, (∀ a b c d, r.r a c → r.r b d → r.r (a ◇ b) (c ◇ d)) →
      r = ⊥ ∨ r = ⊤)
    (meet : ¬∀ a b x : G, a ◇ x = b ◇ x → ∀ z, a ◇ z = b ◇ z) (o : G) :
    Subgroup.normalClosure (MulAction.stabilizer K o : Set K) = ⊤ := by
  by_contra proper
  apply meet
  intro a b x eq z
  have he := columns_of_normal_factor h L act simple o _ proper Subgroup.subset_normalClosure x eq
  rw [he]

/-- The maximal blocks in the imprimitive case have at least two elements,
there are at least three blocks, and the two indices multiply to the order
of the magma. -/
lemma block_sizes {K : Type} [Group K] [Finite K] [MulAction K G]
    (h : Equation677 G) (L : G → K) (act : ∀ y x, L y • x = y ◇ x)
    (o : G) {M : Subgroup K} (hn : ¬ M.Normal) (hs : MulAction.stabilizer K o < M) :
    3 ≤ M.index ∧ 2 ≤ (MulAction.stabilizer K o).relIndex M ∧
      (MulAction.stabilizer K o).relIndex M * M.index = Nat.card G := by
  have h0 : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : M.index ≠ 1 := fun e => hn (M.normal_of_index_eq_one e)
  have h2 : M.index ≠ 2 := fun e => hn (M.normal_of_index_eq_two e)
  have r0 : (MulAction.stabilizer K o).relIndex M ≠ 0 := Subgroup.index_ne_zero_of_finite
  have r1 : (MulAction.stabilizer K o).relIndex M ≠ 1 := fun e => hs.not_ge (Subgroup.relIndex_eq_one.mp e)
  refine ⟨by omega,by omega,?_⟩
  rw [Subgroup.relIndex_mul_index hs.le,Subgroup.index_eq_card]
  apply Nat.card_congr (Equiv.ofBijective (MulAction.ofQuotientStabilizer K o) _)
  refine ⟨MulAction.injective_ofQuotientStabilizer K o,?_⟩
  intro x
  obtain ⟨t,ht⟩ := transitive_rows h L act o x
  exact ⟨QuotientGroup.mk t, ht⟩

theorem main : H1 → H2 →
    OMA.R_EquationalTheories_677_255_Finite_Equation677_implies_Equation255_R1.H1 := by
  classical
  intro primitive blocks G _ _ law simple meet
  by_contra bad
  obtain ⟨o,ho⟩ := not_forall.mp bad
  let row (a : G) : Equiv.Perm G :=
    Equiv.ofBijective (fun x => a ◇ x) ⟨left_injective law a,left_surjective law a⟩
  let K := Subgroup.closure (Set.range row)
  let L (a : G) : K := ⟨row a, Subgroup.subset_closure ⟨a,rfl⟩⟩
  have act (y x : G) : L y • x = y ◇ x := rfl
  have gen : Subgroup.closure (Set.range L) = ⊤ := by
    have im := MonoidHom.map_closure K.subtype (Set.range L)
    have image : K.subtype '' Set.range L = Set.range row := by
      rw [←Set.range_comp]
      rfl
    rw [image] at im
    exact (Subgroup.map_injective K.subtype_injective) (im.trans (by rw [←MonoidHom.range_eq_map, Subgroup.range_subtype]))
  let : MulAction.IsPretransitive K G := ⟨transitive_rows law L act⟩
  have ng := stabilizer_generates law L act simple meet o
  have stabNe : MulAction.stabilizer K o ≠ ⊤ := by
    intro ht
    have fixed (x : G) : x = o := by
      obtain ⟨t,e⟩ := transitive_rows law L act o x
      have mem : t ∈ MulAction.stabilizer K o := ht ▸ Subgroup.mem_top t
      exact e.symm.trans (MulAction.mem_stabilizer_iff.mp mem)
    exact ho (fixed _).symm
  obtain ⟨M,hm,hs⟩ := (eq_top_or_exists_le_coatom (MulAction.stabilizer K o)).resolve_left stabNe
  have nonnormal : ¬ M.Normal := by
    intro normal
    have le := Subgroup.normalClosure_le_normal hs
    rw [ng] at le
    exact hm.1 (top_unique le)
  rcases eq_or_lt_of_le hs with eq | lt
  · have : Nontrivial G := ⟨⟨_,_,ho⟩⟩
    have : MulAction.IsPreprimitive K G :=
      (MulAction.isCoatom_stabilizer_iff_preprimitive K o).mp (eq ▸ hm)
    apply ho
    symm
    exact primitive G K o L gen (eq ▸ nonnormal) (fun x y => (law x y).symm) o
  · obtain ⟨degree,fibre,card⟩ := block_sizes law L act o nonnormal lt
    obtain ⟨r,bot,top,cong⟩ := blocks G K L gen act law o M hm nonnormal lt ng degree fibre card bad
    exact (simple r cong).elim bot top

end OMA.R_EquationalTheories_677_255_Finite_Equation677_implies_Equation255_R1_H1_R1
