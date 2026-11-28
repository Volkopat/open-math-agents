import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1_H1_R1_H2_R1_H2_R1
import Mathlib.GroupTheory.Frattini

-- Reduction Erdos1160.erdos_1160.variants.sum.R1.H1.R1.H2.R1.H2.R1.H1.R1 of step Erdos1160.erdos_1160.variants.sum.R1.H1.R1.H2.R1.H2.R1.H1
-- Credit: @TheLittleOne1234

/- H1, H2 and H3 below are, word for word, the hypotheses H1, H2 and H3 of the merged reduction
Erdos1160.erdos_1160.variants.sum.R3.H2.R2.H1.R1 (by @michelzerasafadaum-gif), and each of them
already has a merged proof: proofs/Erdos1160.erdos_1160.variants.sum.R3.H2.R2.H1.R1.H1.lean,
...H2.lean and ...H3.lean. The lemmas card_out, classes_finite, card_le_three_subtypes and
total_moment are copied from that reduction file. The new part is main: the moment over the
chosen representatives equals the moment over Quotient.out (isomorphic groups have
isomorphic automorphism groups), and 2^(8*b^2) <= 2^(9*b^2). -/
open CategoryTheory Filter Erdos1160
open scoped commutatorElement
namespace OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H1_R1_H2_R1_H2_R1_H1_R1

def H1 : Prop := ∀ t : ℕ, ∃ C : ℕ, ∀ b : ℕ,
  let X := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = 2^b}
  let U := (x : X) × (Fin t → MulAut (x.property.choose : FiniteGrp.{0}))
  Nat.card {u : U // 
    let G : FiniteGrp.{0} := u.1.property.choose
    let d := Nat.log 2 (frattini G).index
    let strip := 1000*(2*b-3*d) ≤ 2*d ∧ 1000*(3*d-2*b) ≤ 2*d
    let F := Subgroup.closure (Set.range fun x : G => x*x)
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    strip ∧ K=⊥}^27 * 2^(9*b^2) ≤ 2^(2*b^3+6*t*b^2+C*(b+1))

def H2 : Prop := ∀ t : ℕ, ∃ C : ℕ, ∀ b : ℕ,
  let X := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = 2^b}
  let U := (x : X) × (Fin t → MulAut (x.property.choose : FiniteGrp.{0}))
  Nat.card {u : U // 
    let G : FiniteGrp.{0} := u.1.property.choose
    let d := Nat.log 2 (frattini G).index
    let strip := 1000*(2*b-3*d) ≤ 2*d ∧ 1000*(3*d-2*b) ≤ 2*d
    let F := Subgroup.closure (Set.range fun x : G => x*x)
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    strip ∧ K≠⊥ ∧ 2^(192*((t+1)*1000)) * Nat.card K ≤ Nat.card F}^27 * 2^(9*b^2) ≤ 2^(2*b^3+6*t*b^2+C*(b+1))

def H3 : Prop := ∀ t : ℕ, ∃ C : ℕ, ∀ b : ℕ,
  let X := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = 2^b}
  let U := (x : X) × (Fin t → MulAut (x.property.choose : FiniteGrp.{0}))
  Nat.card {u : U // 
    let G : FiniteGrp.{0} := u.1.property.choose
    let d := Nat.log 2 (frattini G).index
    let strip := 1000*(2*b-3*d) ≤ 2*d ∧ 1000*(3*d-2*b) ≤ 2*d
    let F := Subgroup.closure (Set.range fun x : G => x*x)
    let K := Subgroup.closure (Set.range (fun x : F => x.val*x.val) ∪
      Set.range (fun z : F × G => ⁅z.1.val,z.2⁆))
    ¬strip ∨ Nat.card F < 2^(192*((t+1)*1000)) * Nat.card K}^27 * 2^(9*b^2) ≤ 2^(2*b^3+6*t*b^2+C*(b+1))

theorem nonempty_mulEquiv_of_iso {X Y : FiniteGrp.{0}} (i : X ≅ Y) : Nonempty (X ≃* Y) :=
  ⟨Iso.groupIsoToMulEquiv ((inducedFunctor FiniteGrp.toGrp).mapIso i)⟩

/-- The chosen representative of a class of groups of order `n` has order `n`. -/
theorem card_out {n : ℕ} {x : Quotient (isIsomorphicSetoid FiniteGrp.{0})}
    (hx : x ∈ Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n}) :
    Nat.card (Quotient.out x : FiniteGrp.{0}) = n := by
  obtain ⟨G, hG, rfl⟩ := hx
  have h : Nonempty (Quotient.out (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) G) ≅ G) :=
    Quotient.mk_out (s := isIsomorphicSetoid FiniteGrp.{0}) G
  obtain ⟨i⟩ := h
  obtain ⟨e⟩ := nonempty_mulEquiv_of_iso i
  rw [Nat.card_congr e.toEquiv]
  exact hG

/-- There are finitely many classes of groups of order `n`: transporting the multiplication of a
representative to `Fin n` gives a table, and classes with equal tables are equal. -/
theorem classes_finite (n : ℕ) :
    (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = n}).Finite := by
  classical
  set S := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = n} with hS
  let e : ∀ x : S, (Quotient.out x.1 : FiniteGrp.{0}) ≃ Fin n := fun x =>
    (Finite.equivFin _).trans (finCongr (card_out x.2))
  let tab : S → Fin n → Fin n → Fin n := fun x a b => e x ((e x).symm a * (e x).symm b)
  have hinj : Function.Injective tab := by
    intro x y hxy
    let f : (Quotient.out x.1 : FiniteGrp.{0}) ≃* (Quotient.out y.1 : FiniteGrp.{0}) :=
      { toEquiv := (e x).trans (e y).symm
        map_mul' := fun a b => by
          have h := congrFun (congrFun hxy (e x a)) (e x b)
          simp only [tab, Equiv.symm_apply_apply] at h
          show (e y).symm (e x (a * b)) = (e y).symm (e x a) * (e y).symm (e x b)
          rw [h, Equiv.symm_apply_apply] }
    apply Subtype.ext
    calc x.1 = Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (Quotient.out x.1) :=
          (Quotient.out_eq _).symm
      _ = Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (Quotient.out y.1) :=
          Quotient.sound ⟨InducedCategory.isoMk (MulEquiv.toGrpIso
            (X := (Quotient.out x.1).toGrp) (Y := (Quotient.out y.1).toGrp) f)⟩
      _ = y.1 := Quotient.out_eq _
  have : Finite S := Finite.of_injective tab hinj
  exact Set.toFinite S

theorem card_le_three_subtypes {U : Type*} [Finite U] (A B D : U → Prop)
    (cover : ∀ u, A u ∨ B u ∨ D u) :
    Nat.card U ≤ Nat.card {u // A u} + Nat.card {u // B u} + Nat.card {u // D u} := by
  classical
  let label (u : U) : ({u // A u} ⊕ {u // B u}) ⊕ {u // D u} :=
    if ha : A u then .inl (.inl ⟨u,ha⟩) else if hb : B u then .inl (.inr ⟨u,hb⟩)
    else .inr ⟨u,(cover u).resolve_left ha |>.resolve_left hb⟩
  let forget : ({u // A u} ⊕ {u // B u}) ⊕ {u // D u} → U :=
    Sum.elim (Sum.elim Subtype.val Subtype.val) Subtype.val
  have hf : Function.LeftInverse forget label := by
    intro u
    dsimp [label]
    split_ifs <;> rfl
  simpa only [Nat.card_sum] using Nat.card_le_card_of_injective label hf.injective

theorem total_moment (h1 : H1) (h2 : H2) (h3 : H3) : ∀ t : ℕ, ∃ C : ℕ, ∀ b : ℕ,
    Nat.card (Σ x : (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^b}), (Fin t → MulAut (x.property.choose : FiniteGrp.{0}))) ^ 27
      * 2^(9*b^2) ≤ 2^(2*b^3+6*t*b^2+C*(b+1)) := by
  classical
  intro t
  obtain ⟨C₁,h₁⟩ := h1 t
  obtain ⟨C₂,h₂⟩ := h2 t
  obtain ⟨C₃,h₃⟩ := h3 t
  let C := max (max C₁ C₂) C₃
  refine ⟨C+54, fun b => ?_⟩
  let X := Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
    {G : FiniteGrp.{0} | Nat.card G = 2^b}
  let G (x : X) : FiniteGrp.{0} := x.property.choose
  let U := (x : X) × (Fin t → MulAut (G x))
  let strip (u : U) := let d := Nat.log 2 (frattini (G u.1)).index
    1000*(2*b-3*d) ≤ 2*d ∧ 1000*(3*d-2*b) ≤ 2*d
  let F (x : X) := Subgroup.closure (Set.range fun v : G x => v*v)
  let K (x : X) := Subgroup.closure (Set.range (fun v : F x => v.val*v.val) ∪
    Set.range (fun z : F x × G x => ⁅z.1.val,z.2⁆))
  let w (u : U) := 2^(192*((t+1)*1000)) * Nat.card (K u.1)
  let A (u : U) := strip u ∧ K u.1 = ⊥
  let B (u : U) := strip u ∧ K u.1 ≠ ⊥ ∧ w u ≤ Nat.card (F u.1)
  let D (u : U) := ¬strip u ∨ Nat.card (F u.1) < w u
  let W := 2^(2*b^3+6*t*b^2+C*(b+1))
  let I₁ := Nat.card {u : U // A u}
  let I₂ := Nat.card {u : U // B u}
  let I₃ := Nat.card {u : U // D u}
  let M := max (max I₁ I₂) I₃
  letI : Finite X := classes_finite (2^b) |>.to_subtype
  letI (Y : FiniteGrp.{0}) : Finite (MulAut Y) :=
    Finite.of_injective (fun f : MulAut Y => (f : Y → Y)) DFunLike.coe_injective
  have cover : Nat.card U ≤ 4*M := by
    have bound := card_le_three_subtypes A B D (by
      intro u
      dsimp only [A,B,D]
      by_cases hs : strip u
      · by_cases hk : K u.1 = ⊥
        · exact .inl ⟨hs,hk⟩
        · by_cases hw : w u ≤ Nat.card (F u.1)
          · exact .inr (.inl ⟨hs,hk,hw⟩)
          · exact .inr (.inr (.inr (Nat.lt_of_not_ge hw)))
      · exact .inr (.inr (.inl hs)))
    change Nat.card U ≤ I₁ + I₂ + I₃ at bound
    dsimp only [M]; omega
  have raise (L : ℕ) (hl : L ≤ C) : 2^(2*b^3+6*t*b^2+L*(b+1)) ≤ W :=
    Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left (Nat.mul_le_mul_right _ hl) _)
  have cap : M^27 * 2^(9*b^2) ≤ W := by
    have ha : I₁^27 * 2^(9*b^2) ≤ W := (h₁ b).trans (raise _ ((le_max_left ..).trans (le_max_left ..)))
    have hb : I₂^27 * 2^(9*b^2) ≤ W := (h₂ b).trans (raise _ ((le_max_right ..).trans (le_max_left ..)))
    have hd : I₃^27 * 2^(9*b^2) ≤ W := (h₃ b).trans (raise _ (le_max_right ..))
    have hf : M=I₁ ∨ M=I₂ ∨ M=I₃ := by dsimp only [M]; omega
    rcases hf with e|e|e <;> rw [e] <;> assumption

  apply (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left cover 27)).trans
  rw [mul_pow,show (4:ℕ)^27=2^54 by decide, Nat.mul_assoc]
  apply (Nat.mul_le_mul_left (2^54) cap).trans
  dsimp only [W]
  rw [←pow_add]
  exact Nat.pow_le_pow_right (by decide) (by nlinarith only [Nat.zero_le b])

theorem moment_out_eq (t b : ℕ) :
    Nat.card (Σ x : (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2 ^ b}),
      (Fin t → MulAut (Quotient.out x.1 : FiniteGrp.{0}))) =
    Nat.card (Σ x : (Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) ''
      {G : FiniteGrp.{0} | Nat.card G = 2^b}), (Fin t → MulAut (x.property.choose : FiniteGrp.{0}))) := by
  apply Nat.card_congr
  refine Equiv.sigmaCongrRight fun x => Equiv.arrowCongr (Equiv.refl _) ?_
  have hx : Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (Quotient.out x.1 : FiniteGrp.{0}) =
      Quotient.mk (isIsomorphicSetoid FiniteGrp.{0}) (x.property.choose : FiniteGrp.{0}) :=
    (Quotient.out_eq _).trans x.property.choose_spec.2.symm
  exact (MulAut.congr (Classical.choice
    (nonempty_mulEquiv_of_iso (Classical.choice (Quotient.exact hx))))).toEquiv

theorem main : H1 → H2 → H3 → OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H1_R1_H2_R1_H2_R1.H1 := by
  intro h1 h2 h3 t
  obtain ⟨C, hC⟩ := total_moment h1 h2 h3 t
  refine ⟨C, fun b => ?_⟩
  rw [moment_out_eq t b]
  refine le_trans ?_ (hC b)
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by nlinarith only [sq_nonneg b]))

end OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H1_R1_H2_R1_H2_R1_H1_R1
