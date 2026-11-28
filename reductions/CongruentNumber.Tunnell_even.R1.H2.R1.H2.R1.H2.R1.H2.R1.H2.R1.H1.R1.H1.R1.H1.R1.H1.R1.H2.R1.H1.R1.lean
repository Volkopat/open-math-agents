import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1
import Mathlib


/-! The abelian reciprocity map from automorphisms to norm classes is an isomorphism once it is injective and the norm index divides the relative degree. -/

namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1_H1_R1

section

open scoped Classical

def H1 : Prop :=
  (
∀ (G : ProfiniteGrp) (A : Rep ℤ G),
  let S := ClosedSubgroup G
  let U := fun H : S => H.toSubgroup
  let T : S := ⟨⊤,isClosed_univ⟩
  let M := fun H J : S => (U J).subgroupOf (U H)
  letI : Module ℤ A.V := A.hV2
  let B := fun H : S => (Representation.invariants (A.ρ.comp (U H).subtype)).toAddSubgroup
  let tr := fun (H J : S) (b : A.V) => ∑ᶠ q : U H ⧸ M H J, A.ρ q.out.val b
  let Z := (Int.castRingHom (∀ n : ℕ+, ZMod (n : ℕ))).range.topologicalClosure
  ∀ (d : G →* Multiplicative Z) (v : B T →+ Z), let e := fun H : S => ((U H).map d).index
  Continuous d → Function.Surjective d → (∀ m : ℤ, (m : Z) ∈ v.range) →
  (∀ (n : ℕ+) (x : B T), (v x).val n = 0 → ∃ y : B T, (n : ℕ) • v y = v x) →
  (∀ (H : S) [(U H).FiniteIndex] (z : Z),
    (∃ (a : B T) (b : B H), tr T H b.val = a.val ∧ v a = z) ↔ ∃ a, e H • v a = z) →
  (∀ (H J : S) [(U H).FiniteIndex], J ≤ H → ∀ [(M H J).Normal] [Fintype (U H ⧸ M H J)]
    [IsCyclic (U H ⧸ M H J)], let P := (Rep.res (U H).subtype A).quotientToInvariants (M H J)
    Nat.card (tateCohomology P 0) = Nat.card (U H ⧸ M H J) ∧ Subsingleton (tateCohomology P (-1))) →
  ∀ (H J : S) [(U H).FiniteIndex], J ≤ H → ∀ [(M H J).Normal] [Fintype (U H ⧸ M H J)],
    let Q := U H ⧸ M H J
    let l := QuotientGroup.mk' (M H J ⊓ (d.comp (U H).subtype).ker)
    ∀ W : AddSubgroup (B H), (∀ x, x ∈ W ↔ ∃ b : B J, tr H J b.val = x.val) →
    ∃ r : Additive Q →+ B H ⧸ W, ∀ (t : U H) (n : ℕ+) (F : S) (b : B F) (a : B T) (x : B H),
      (d t.val).toAdd = e H • ((n : ℕ) : Z) →
      U F = (((Subgroup.zpowers (l t)).topologicalClosure.comap l).map (U H).subtype) →
      tr T F b.val = a.val → v a = (e F : Z) → tr H F b.val = x.val →
      r (Additive.ofMul (t : Q)) = x
)

end

section

open scoped Classical

def H2 : Prop :=
  (
∀ (G : ProfiniteGrp) (A : Rep ℤ G),
  let S := ClosedSubgroup G
  let U := fun H : S => H.toSubgroup
  let T : S := ⟨⊤,isClosed_univ⟩
  let M := fun H J : S => (U J).subgroupOf (U H)
  letI : Module ℤ A.V := A.hV2
  let B := fun H : S => (Representation.invariants (A.ρ.comp (U H).subtype)).toAddSubgroup
  let tr := fun (H J : S) (b : A.V) => ∑ᶠ q : U H ⧸ M H J, A.ρ q.out.val b
  let Z := (Int.castRingHom (∀ n : ℕ+, ZMod (n : ℕ))).range.topologicalClosure
  ∀ (d : G →* Multiplicative Z) (v : B T →+ Z), let e := fun H : S => ((U H).map d).index
  Continuous d → Function.Surjective d → (∀ m : ℤ, (m : Z) ∈ v.range) →
  (∀ (n : ℕ+) (x : B T), (v x).val n = 0 → ∃ y : B T, (n : ℕ) • v y = v x) →
  (∀ (H : S) [(U H).FiniteIndex] (z : Z),
    (∃ (a : B T) (b : B H), tr T H b.val = a.val ∧ v a = z) ↔ ∃ a, e H • v a = z) →
  let P := {p : S × S // (U p.1).FiniteIndex ∧ p.2 ≤ p.1 ∧ (M p.1 p.2).Normal ∧ Finite (U p.1 ⧸ M p.1 p.2)}
  let H (p : P) := p.val.1
  let J (p : P) := p.val.2
  letI (p : P) : (M (H p) (J p)).Normal := p.property.2.2.1
  let Q := fun p : P => U (H p) ⧸ M (H p) (J p)
  let W := fun p : P => AddSubgroup.closure {x : B (H p) | ∃ b : B (J p), tr (H p) (J p) b.val = x.val}
  (∀ p : P, ∀ [Fintype (Q p)] [IsCyclic (Q p)],
    let C := (Rep.res (U (H p)).subtype A).quotientToInvariants (M (H p) (J p))
    Nat.card (tateCohomology C 0) = Nat.card (Q p) ∧ Subsingleton (tateCohomology C (-1))) →
  ∀ r : ∀ p : P, Additive (Q p) →+ B (H p) ⧸ W p,
  (∀ (p : P) (t : U (H p)) (n : ℕ+) (F : S) (b : B F) (a : B T) (x : B (H p)),
    let l := QuotientGroup.mk' (M (H p) (J p) ⊓ (d.comp (U (H p)).subtype).ker)
    (d t.val).toAdd = e (H p) • ((n : ℕ) : Z) →
    U F = (((Subgroup.zpowers (l t)).topologicalClosure.comap l).map (U (H p)).subtype) →
    tr T F b.val = a.val → v a = (e F : Z) → tr (H p) F b.val = x.val →
    r p (Additive.ofMul (t : Q p)) = x) →
  ∀ p : P, IsCyclic (Q p) → Function.Injective (r p)
)

end

section

open scoped Classical

def H3 : Prop :=
  (
∀ (G: ProfiniteGrp.{0}) (A: Rep.{0} ℤ G),
  let S := ClosedSubgroup G
  let U := fun H: S => H.toSubgroup
  let T: S := ⟨⊤,isClosed_univ⟩
  let M := fun H J: S => (U J).subgroupOf (U H)
  letI: Module ℤ A.V := A.hV2
  let B := fun H: S => (Representation.invariants (A.ρ.comp (U H).subtype)).toAddSubgroup
  let tr := fun (H J: S) (b: A.V) => ∑ᶠ q: U H ⧸ M H J, A.ρ q.out.val b
  let Z := (Int.castRingHom (∀ n: ℕ+, ZMod (n: ℕ))).range.topologicalClosure
  ∀ (d: G →* Multiplicative Z) (v: B T →+ Z), let e := fun H: S => ((U H).map d).index
  Continuous d → Function.Surjective d → (∀ m: ℤ, (m: Z) ∈ v.range) →
  (∀ (n: ℕ+) (x: B T), (v x).val n = 0 → ∃ y: B T, (n: ℕ) • v y = v x) →
  (∀ (H: S) [(U H).FiniteIndex] (z: Z),
    (∃ (a: B T) (b: B H), tr T H b.val = a.val ∧ v a = z) ↔ ∃ a, e H • v a = z) →
  let P := {p: S × S // (U p.1).FiniteIndex ∧ p.2 ≤ p.1 ∧ (M p.1 p.2).Normal ∧ Finite (U p.1 ⧸ M p.1 p.2)}
  let H (p: P) := p.val.1
  let J (p: P) := p.val.2
  letI (p: P): (M (H p) (J p)).Normal := p.property.2.2.1
  let Q (p: P) := U (H p) ⧸ M (H p) (J p)
  let W (p: P) := AddSubgroup.closure {x: B (H p) | ∃ b: B (J p), tr (H p) (J p) b.val = x.val}
  ∀ r: ∀ p, Additive (Q p) →+ B (H p) ⧸ W p,
  (∀ p (t: U (H p)) (n: ℕ+) (F: S) (b: B F) (a: B T) (x: B (H p)),
    let l := QuotientGroup.mk' (M (H p) (J p) ⊓ (d.comp (U (H p)).subtype).ker)
    (d t.val).toAdd = e (H p) • ((n: ℕ): Z) →
    U F = (((Subgroup.zpowers (l t)).topologicalClosure.comap l).map (U (H p)).subtype) →
    tr T F b.val = a.val → v a = (e F: Z) → tr (H p) F b.val = x.val →
    r p (Additive.ofMul (t: Q p)) = x) →
  (∀ p, IsCyclic (Q p) → Function.Injective (r p)) →
  ∀ p, IsMulCommutative (Q p) → Function.Injective (r p) ∧
    ∀ s ∈ Subgroup.normalizer (H p: Set G) ⊓ Subgroup.normalizer (J p: Set G),
    ∀ (a b: U (H p)) (x y: B (H p)), b.val = s*a.val*s⁻¹ → y.val = A.ρ s x.val →
    r p (Additive.ofMul (a: Q p)) = x → r p (Additive.ofMul (b: Q p)) = y
)

end

section

open scoped Classical IsMulCommutative

def H4 : Prop :=
  (
∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] (A : Rep ℤ G),
  let S := ClosedSubgroup G
  let U := fun H : S => H.toSubgroup
  letI : Module ℤ A.V := A.hV2
  let B := fun H : S => (Representation.invariants (A.ρ.comp (U H).subtype)).toAddSubgroup
  let M := fun H J : S => (U J).subgroupOf (U H)
  (∀ (H J : S) [(U H).FiniteIndex], J ≤ H → ∀ [(M H J).Normal] [Fintype (U H ⧸ M H J)]
    [IsCyclic (U H ⧸ M H J)], let P := (Rep.res (U H).subtype A).quotientToInvariants (M H J)
    Nat.card (tateCohomology P 0) = Nat.card (U H ⧸ M H J) ∧ Subsingleton (tateCohomology P (-1))) →
  ∀ (H J : S) [(U H).FiniteIndex], J ≤ H → ∀ [(M H J).Normal] [Fintype (U H ⧸ M H J)]
    [IsMulCommutative (U H ⧸ M H J)], let Q := U H ⧸ M H J
    ∃ W : AddSubgroup (B H), (∀ x, x ∈ W ↔ ∃ b : B J, ∑ᶠ q : Q, A.ρ q.out.val b.val = x.val) ∧
      W.index ∣ Nat.card Q
)

end

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1_H1_R1

section
open NumberField IsDedekindDomain
open scoped NumberField Classical
open scoped Classical IsMulCommutative

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1_H2_R1_H1_R1
open scoped Classical IsMulCommutative



theorem deriveNormalizerReciprocityIndex : (
∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] (A : Rep ℤ G),
  let S := ClosedSubgroup G
  let T : S := ⟨⊤, isClosed_univ⟩
  let U := fun H : S => H.toSubgroup
  letI : Module ℤ A.V := A.hV2
  let B := fun H : S => (Representation.invariants (A.ρ.comp (U H).subtype)).toAddSubgroup
  let M := fun H J : S => (U J).subgroupOf (U H)
  let N := fun (H J : S) (a : A.V) =>
    ∃ b : B J, ∑ᶠ q : U H ⧸ M H J, A.ρ q.out.val b.val = a
  let R := ∀ n : ℕ+, ZMod (n : ℕ)
  let Z := (Int.castRingHom R).range.topologicalClosure
  ∀ (d : G →* Multiplicative Z) (v : B T →+ Z),
  Continuous d → Function.Surjective d →
  (∀ m : ℤ, (m : Z) ∈ v.range) →
  (∀ (n : ℕ+) (x : B T), (v x).val n = 0 → ∃ y : B T, (n : ℕ) • v y = v x) →
  (∀ (H : S) [(U H).FiniteIndex] (z : Z),
    (∃ a : B T, N T H a ∧ v a = z) ↔ ∃ a, ((U H).map d).index • v a = z) →
  (∀ (H J : S) [(U H).FiniteIndex], J ≤ H → ∀ [(M H J).Normal] [Fintype (U H ⧸ M H J)]
    [IsCyclic (U H ⧸ M H J)],
    let P := (Rep.res (U H).subtype A).quotientToInvariants (M H J)
    Nat.card (tateCohomology P 0) = Nat.card (U H ⧸ M H J) ∧
      Subsingleton (tateCohomology P (-1))) →
  ∀ (H J : S) [(U H).FiniteIndex], J ≤ H → ∀ [(M H J).Normal] [Fintype (U H ⧸ M H J)]
    [IsMulCommutative (U H ⧸ M H J)],
    let Q := U H ⧸ M H J
    ∀ W : AddSubgroup (B H), (∀ x, x ∈ W ↔ N H J x.val) →
    ∃ j : Additive Q →+ B H ⧸ W, Function.Injective j ∧
      ∀ s : G, (U H).map (MulAut.conj s) = U H → (U J).map (MulAut.conj s) = U J →
        ∀ (x y : B H) (a b : U H), y.val = A.ρ s x.val → b.val = s * a.val * s⁻¹ →
        j (Additive.ofMul (a : Q)) = x → j (Additive.ofMul (b : Q)) = y
) → (
∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] (A : Rep ℤ G),
  let S := ClosedSubgroup G
  let U := fun H : S => H.toSubgroup
  letI : Module ℤ A.V := A.hV2
  let B := fun H : S => (Representation.invariants (A.ρ.comp (U H).subtype)).toAddSubgroup
  let M := fun H J : S => (U J).subgroupOf (U H)
  (∀ (H J : S) [(U H).FiniteIndex], J ≤ H → ∀ [(M H J).Normal] [Fintype (U H ⧸ M H J)]
    [IsCyclic (U H ⧸ M H J)], let P := (Rep.res (U H).subtype A).quotientToInvariants (M H J)
    Nat.card (tateCohomology P 0) = Nat.card (U H ⧸ M H J) ∧ Subsingleton (tateCohomology P (-1))) →
  ∀ (H J : S) [(U H).FiniteIndex], J ≤ H → ∀ [(M H J).Normal] [Fintype (U H ⧸ M H J)]
    [IsMulCommutative (U H ⧸ M H J)], let Q := U H ⧸ M H J
    ∃ W : AddSubgroup (B H), (∀ x, x ∈ W ↔ ∃ b : B J, ∑ᶠ q : Q, A.ρ q.out.val b.val = x.val) ∧
      W.index ∣ Nat.card Q
) → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1.H1 := by
  intro injective bound
  intro G _ _ _ _ _ _ A
  dsimp only
  intro d v hd hs vi vd vr cf H J hH hJ hnorm hfin hcomm
  let U := fun K : ClosedSubgroup G => K.toSubgroup
  letI : Module ℤ A.V := A.hV2
  let B := fun K : ClosedSubgroup G => (Representation.invariants (A.ρ.comp (U K).subtype)).toAddSubgroup
  let Q := U H ⧸ (U J).subgroupOf (U H)
  obtain ⟨W,hW,dvd⟩ := bound G A cf H J hJ
  obtain ⟨j,hj,conj⟩ := injective G A d v hd hs vi vd vr cf H J hJ W hW
  have hp : 0 < Nat.card Q := Nat.card_pos
  haveI : Finite (B H ⧸ W) := Nat.finite_of_card_ne_zero (ne_zero_of_dvd_ne_zero hp.ne' dvd)
  have hle : Nat.card (B H ⧸ W) ≤ Nat.card (Additive Q) := Nat.le_of_dvd hp dvd
  let e := AddEquiv.ofBijective j (hj.bijective_of_nat_card_le hle)
  let f := e.symm.toAddMonoidHom.comp (QuotientAddGroup.mk' W)
  refine ⟨f,e.symm.surjective.comp (QuotientAddGroup.mk'_surjective W),?_,?_⟩
  · intro x
    change e.symm (QuotientAddGroup.mk x) = 0 ↔ _
    rw [e.symm.map_eq_zero_iff,QuotientAddGroup.eq_zero_iff]
    exact hW x
  · intro s hH hJ x y a b hy hb hx
    have hax : j (Additive.ofMul (a : Q)) = QuotientAddGroup.mk x := by
      exact ((congrArg e hx).symm.trans (e.apply_symm_apply _))
    exact (congrArg e.symm (conj s hH hJ x y a b hy hb hax)).symm.trans (e.symm_apply_apply _)

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1_H2_R1_H1_R1

end

section
open scoped Classical IsMulCommutative
open scoped Classical

 
namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1_H2_R1_H1_R1_H1_R1
open scoped Classical




theorem deriveNormalizedFrobeniusReciprocity : (
∀ (G : ProfiniteGrp) (A : Rep ℤ G),
  let S := ClosedSubgroup G
  let U := fun H : S => H.toSubgroup
  let T : S := ⟨⊤,isClosed_univ⟩
  let M := fun H J : S => (U J).subgroupOf (U H)
  letI : Module ℤ A.V := A.hV2
  let B := fun H : S => (Representation.invariants (A.ρ.comp (U H).subtype)).toAddSubgroup
  let tr := fun (H J : S) (b : A.V) => ∑ᶠ q : U H ⧸ M H J, A.ρ q.out.val b
  let Z := (Int.castRingHom (∀ n : ℕ+, ZMod (n : ℕ))).range.topologicalClosure
  ∀ (d : G →* Multiplicative Z) (v : B T →+ Z), let e := fun H : S => ((U H).map d).index
  Continuous d → Function.Surjective d → (∀ m : ℤ, (m : Z) ∈ v.range) →
  (∀ (n : ℕ+) (x : B T), (v x).val n = 0 → ∃ y : B T, (n : ℕ) • v y = v x) →
  (∀ (H : S) [(U H).FiniteIndex] (z : Z),
    (∃ (a : B T) (b : B H), tr T H b.val = a.val ∧ v a = z) ↔ ∃ a, e H • v a = z) →
  (∀ (H J : S) [(U H).FiniteIndex], J ≤ H → ∀ [(M H J).Normal] [Fintype (U H ⧸ M H J)]
    [IsCyclic (U H ⧸ M H J)], let P := (Rep.res (U H).subtype A).quotientToInvariants (M H J)
    Nat.card (tateCohomology P 0) = Nat.card (U H ⧸ M H J) ∧ Subsingleton (tateCohomology P (-1))) →
  ∀ (H J : S) [(U H).FiniteIndex], J ≤ H → ∀ [(M H J).Normal] [Fintype (U H ⧸ M H J)],
    let Q := U H ⧸ M H J
    let l := QuotientGroup.mk' (M H J ⊓ (d.comp (U H).subtype).ker)
    ∀ W : AddSubgroup (B H), (∀ x, x ∈ W ↔ ∃ b : B J, tr H J b.val = x.val) →
    ∃ r : Additive Q →+ B H ⧸ W, ∀ (t : U H) (n : ℕ+) (F : S) (b : B F) (a : B T) (x : B H),
      (d t.val).toAdd = e H • ((n : ℕ) : Z) →
      U F = (((Subgroup.zpowers (l t)).topologicalClosure.comap l).map (U H).subtype) →
      tr T F b.val = a.val → v a = (e F : Z) → tr H F b.val = x.val →
      r (Additive.ofMul (t : Q)) = x
) → (
∀ (G : ProfiniteGrp) (A : Rep ℤ G),
  let S := ClosedSubgroup G
  let U := fun H : S => H.toSubgroup
  let T : S := ⟨⊤,isClosed_univ⟩
  let M := fun H J : S => (U J).subgroupOf (U H)
  letI : Module ℤ A.V := A.hV2
  let B := fun H : S => (Representation.invariants (A.ρ.comp (U H).subtype)).toAddSubgroup
  let tr := fun (H J : S) (b : A.V) => ∑ᶠ q : U H ⧸ M H J, A.ρ q.out.val b
  let Z := (Int.castRingHom (∀ n : ℕ+, ZMod (n : ℕ))).range.topologicalClosure
  ∀ (d : G →* Multiplicative Z) (v : B T →+ Z), let e := fun H : S => ((U H).map d).index
  Continuous d → Function.Surjective d → (∀ m : ℤ, (m : Z) ∈ v.range) →
  (∀ (n : ℕ+) (x : B T), (v x).val n = 0 → ∃ y : B T, (n : ℕ) • v y = v x) →
  (∀ (H : S) [(U H).FiniteIndex] (z : Z),
    (∃ (a : B T) (b : B H), tr T H b.val = a.val ∧ v a = z) ↔ ∃ a, e H • v a = z) →
  let P := {p : S × S // (U p.1).FiniteIndex ∧ p.2 ≤ p.1 ∧ (M p.1 p.2).Normal ∧ Finite (U p.1 ⧸ M p.1 p.2)}
  let H (p : P) := p.val.1
  let J (p : P) := p.val.2
  letI (p : P) : (M (H p) (J p)).Normal := p.property.2.2.1
  let Q := fun p : P => U (H p) ⧸ M (H p) (J p)
  let W := fun p : P => AddSubgroup.closure {x : B (H p) | ∃ b : B (J p), tr (H p) (J p) b.val = x.val}
  (∀ p : P, ∀ [Fintype (Q p)] [IsCyclic (Q p)],
    let C := (Rep.res (U (H p)).subtype A).quotientToInvariants (M (H p) (J p))
    Nat.card (tateCohomology C 0) = Nat.card (Q p) ∧ Subsingleton (tateCohomology C (-1))) →
  ∀ r : ∀ p : P, Additive (Q p) →+ B (H p) ⧸ W p,
  (∀ (p : P) (t : U (H p)) (n : ℕ+) (F : S) (b : B F) (a : B T) (x : B (H p)),
    let l := QuotientGroup.mk' (M (H p) (J p) ⊓ (d.comp (U (H p)).subtype).ker)
    (d t.val).toAdd = e (H p) • ((n : ℕ) : Z) →
    U F = (((Subgroup.zpowers (l t)).topologicalClosure.comap l).map (U (H p)).subtype) →
    tr T F b.val = a.val → v a = (e F : Z) → tr (H p) F b.val = x.val →
    r p (Additive.ofMul (t : Q p)) = x) →
  ∀ p : P, IsCyclic (Q p) → Function.Injective (r p)
) → (
∀ (G : ProfiniteGrp.{0}) (A : Rep.{0} ℤ G),
  let S := ClosedSubgroup G
  let U := fun H : S => H.toSubgroup
  let T : S := ⟨⊤,isClosed_univ⟩
  let M := fun H J : S => (U J).subgroupOf (U H)
  letI : Module ℤ A.V := A.hV2
  let B := fun H : S => (Representation.invariants (A.ρ.comp (U H).subtype)).toAddSubgroup
  let tr := fun (H J : S) (b : A.V) => ∑ᶠ q : U H ⧸ M H J, A.ρ q.out.val b
  let Z := (Int.castRingHom (∀ n : ℕ+, ZMod (n : ℕ))).range.topologicalClosure
  ∀ (d : G →* Multiplicative Z) (v : B T →+ Z), let e := fun H : S => ((U H).map d).index
  Continuous d → Function.Surjective d → (∀ m : ℤ, (m : Z) ∈ v.range) →
  (∀ (n : ℕ+) (x : B T), (v x).val n = 0 → ∃ y : B T, (n : ℕ) • v y = v x) →
  (∀ (H : S) [(U H).FiniteIndex] (z : Z),
    (∃ (a : B T) (b : B H), tr T H b.val = a.val ∧ v a = z) ↔ ∃ a, e H • v a = z) →
  let P := {p : S × S // (U p.1).FiniteIndex ∧ p.2 ≤ p.1 ∧ (M p.1 p.2).Normal ∧ Finite (U p.1 ⧸ M p.1 p.2)}
  let H (p : P) := p.val.1
  let J (p : P) := p.val.2
  letI (p : P) : (M (H p) (J p)).Normal := p.property.2.2.1
  let Q (p : P) := U (H p) ⧸ M (H p) (J p)
  let W (p : P) := AddSubgroup.closure {x : B (H p) | ∃ b : B (J p), tr (H p) (J p) b.val = x.val}
  ∀ r : ∀ p, Additive (Q p) →+ B (H p) ⧸ W p,
  (∀ p (t : U (H p)) (n : ℕ+) (F : S) (b : B F) (a : B T) (x : B (H p)),
    let l := QuotientGroup.mk' (M (H p) (J p) ⊓ (d.comp (U (H p)).subtype).ker)
    (d t.val).toAdd = e (H p) • ((n : ℕ) : Z) →
    U F = (((Subgroup.zpowers (l t)).topologicalClosure.comap l).map (U (H p)).subtype) →
    tr T F b.val = a.val → v a = (e F : Z) → tr (H p) F b.val = x.val →
    r p (Additive.ofMul (t : Q p)) = x) →
  (∀ p, IsCyclic (Q p) → Function.Injective (r p)) →
  ∀ p, IsMulCommutative (Q p) → Function.Injective (r p) ∧
    ∀ s ∈ Subgroup.normalizer (H p : Set G) ⊓ Subgroup.normalizer (J p : Set G),
    ∀ (a b : U (H p)) (x y : B (H p)), b.val = s*a.val*s⁻¹ → y.val = A.ρ s x.val →
    r p (Additive.ofMul (a : Q p)) = x → r p (Additive.ofMul (b : Q p)) = y
) → (
∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] (A : Rep ℤ G),
  let S := ClosedSubgroup G
  let T : S := ⟨⊤, isClosed_univ⟩
  let U := fun H : S => H.toSubgroup
  letI : Module ℤ A.V := A.hV2
  let B := fun H : S => (Representation.invariants (A.ρ.comp (U H).subtype)).toAddSubgroup
  let M := fun H J : S => (U J).subgroupOf (U H)
  let N := fun (H J : S) (a : A.V) =>
    ∃ b : B J, ∑ᶠ q : U H ⧸ M H J, A.ρ q.out.val b.val = a
  let R := ∀ n : ℕ+, ZMod (n : ℕ)
  let Z := (Int.castRingHom R).range.topologicalClosure
  ∀ (d : G →* Multiplicative Z) (v : B T →+ Z),
  Continuous d → Function.Surjective d →
  (∀ m : ℤ, (m : Z) ∈ v.range) →
  (∀ (n : ℕ+) (x : B T), (v x).val n = 0 → ∃ y : B T, (n : ℕ) • v y = v x) →
  (∀ (H : S) [(U H).FiniteIndex] (z : Z),
    (∃ a : B T, N T H a ∧ v a = z) ↔ ∃ a, ((U H).map d).index • v a = z) →
  (∀ (H J : S) [(U H).FiniteIndex], J ≤ H → ∀ [(M H J).Normal] [Fintype (U H ⧸ M H J)]
    [IsCyclic (U H ⧸ M H J)],
    let P := (Rep.res (U H).subtype A).quotientToInvariants (M H J)
    Nat.card (tateCohomology P 0) = Nat.card (U H ⧸ M H J) ∧
      Subsingleton (tateCohomology P (-1))) →
  ∀ (H J : S) [(U H).FiniteIndex], J ≤ H → ∀ [(M H J).Normal] [Fintype (U H ⧸ M H J)]
    [IsMulCommutative (U H ⧸ M H J)],
    let Q := U H ⧸ M H J
    ∀ W : AddSubgroup (B H), (∀ x, x ∈ W ↔ N H J x.val) →
    ∃ j : Additive Q →+ B H ⧸ W, Function.Injective j ∧
      ∀ s : G, (U H).map (MulAut.conj s) = U H → (U J).map (MulAut.conj s) = U J →
        ∀ (x y : B H) (a b : U H), y.val = A.ρ s x.val → b.val = s * a.val * s⁻¹ →
        j (Additive.ofMul (a : Q)) = x → j (Additive.ofMul (b : Q)) = y
) := by
  intro evaluation cyclic descent
  intro G _ _ _ _ _ _ A
  dsimp only
  intro d v cd ds vi vd vr cf
  let U := fun h : ClosedSubgroup G => h.toSubgroup
  let M := fun h j : ClosedSubgroup G => (U j).subgroupOf (U h)
  letI : Module ℤ A.V := A.hV2
  let B := fun h : ClosedSubgroup G => (Representation.invariants (A.ρ.comp (U h).subtype)).toAddSubgroup
  let tr := fun (h j : ClosedSubgroup G) (b : A.V) => ∑ᶠ q : U h ⧸ M h j, A.ρ q.out.val b
  let P := {p : ClosedSubgroup G × ClosedSubgroup G //
      (U p.1).FiniteIndex ∧ p.2 ≤ p.1 ∧ (M p.1 p.2).Normal ∧ Finite (U p.1 ⧸ M p.1 p.2)}
  let H (p : P) := p.val.1
  let J (p : P) := p.val.2
  letI (p : P) : (M (H p) (J p)).Normal := p.property.2.2.1
  letI (p : P) : Fintype (U (H p) ⧸ M (H p) (J p)) := @Fintype.ofFinite _ p.property.2.2.2
  letI (p : P) : (U (H p)).FiniteIndex := p.property.1
  let Q (p : P) := U (H p) ⧸ M (H p) (J p)
  let W (p : P) := AddSubgroup.closure {x : B (H p) | ∃ b : B (J p), tr (H p) (J p) b.val = x.val}
  have mem (p : P) (x : B (H p)) :
      x ∈ W p ↔ ∃ b : B (J p), tr (H p) (J p) b.val = x.val := by
    let f : A.V →ₗ[ℤ] A.V := ∑ q : Q p, A.ρ q.out.val
    have eq (b : A.V) : f b = tr (H p) (J p) b := by
      simp only [f,tr,finsum_eq_sum_of_fintype,LinearMap.sum_apply]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext q
      simp
    let D := ((f.toAddMonoidHom.comp (B (J p)).subtype).range.comap (B (H p)).subtype)
    have hD (a : B (H p)) : a ∈ D ↔ ∃ b : B (J p), tr (H p) (J p) b.val = a.val := by
      change (∃ b : B (J p), f b.val = a.val) ↔ _
      simp only [eq]
    have he : W p = D := by
      change AddSubgroup.closure _ = D
      rw [show {a : B (H p) | ∃ b : B (J p), tr (H p) (J p) b.val = a.val} = (D : Set _) from
        Set.ext fun a => (hD a).symm, AddSubgroup.closure_eq]
    exact he ▸ hD x
  let T : ClosedSubgroup G := ⟨⊤,isClosed_univ⟩
  let Z := (Int.castRingHom (∀ n : ℕ+, ZMod (n : ℕ))).range.topologicalClosure
  have hn (H : ClosedSubgroup G) [(U H).FiniteIndex] (z : Z) :
      (∃ (a : B T) (b : B H), tr T H b.val = a.val ∧ v a = z) ↔ ∃ a, ((U H).map d).index • v a = z := by
    constructor
    · rintro ⟨a,b,ha,he⟩
      exact (vr H z).mp ⟨a,⟨b,ha⟩,he⟩
    · intro hz
      obtain ⟨a,⟨b,ha⟩,he⟩ := (vr H z).mpr hz
      exact ⟨a,b,ha,he⟩
  let ev := evaluation (ProfiniteGrp.of G) A d v cd ds vi vd hn cf
  let normed (p : P) := ev (H p) (J p) p.property.2.1 (W p) (mem p)
  let r (p : P) : Additive (Q p) →+ B (H p) ⧸ W p := Classical.choose (normed p)
  have normalized := fun p => Classical.choose_spec (normed p)
  have hc := cyclic (ProfiniteGrp.of G) A d v cd ds vi vd hn
    (fun p _ _ => cf (H p) (J p) p.property.2.1) r normalized
  have good := descent (ProfiniteGrp.of G) A d v cd ds vi vd hn r normalized hc
  intro h j finite le normal card comm w hw
  let p : P := ⟨⟨h,j⟩,finite,le,normal,@Finite.of_fintype _ card⟩
  have hW : W p = w := AddSubgroup.ext fun x => (mem p x).trans (hw x).symm
  subst w
  refine ⟨r p,(good p comm).1,?_⟩
  intro s sh sj x y a b hxy hab hx
  exact (good p comm).2 s ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr sh,
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr sj⟩ a b x y hab hxy hx

end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1_H2_R1_H1_R1_H1_R1

end

namespace OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1_H1_R1
theorem main : H1 → H2 → H3 → H4 → OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1.H1 :=
  fun v1 v2 v3 v4 =>
    (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1_H2_R1_H1_R1.deriveNormalizerReciprocityIndex (OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1_H2_R1_H1_R1_H1_R1.deriveNormalizedFrobeniusReciprocity v1 v2 v3) v4)
end OMA.R_CongruentNumber_Tunnell_even_R1_H2_R1_H2_R1_H2_R1_H2_R1_H2_R1_H1_R1_H1_R1_H1_R1_H1_R1_H2_R1_H1_R1
