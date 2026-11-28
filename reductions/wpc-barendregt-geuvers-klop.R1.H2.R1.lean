import OMAReductions.R_wpc_barendregt_geuvers_klop_R1
/- Adapted from OpenAI openai/math, commit 3344da59991ed94f9ba711217b29c1d760badfa6, lean/OAI/Computability/TypeSystem, Apache-2.0. -/
namespace OMA.R_wpc_barendregt_geuvers_klop_R1_H2_R1
open OMA.S_wpc_barendregt_geuvers_klop

def H1 : Prop := ∀ n (P : Specification (Fin n)), SystemWeaklyNormalizing P →
  let V := Set (Fin n)
  let F := fun (i : V) => i.Nonempty ∧ ∃ Γ t, ValidContext P Γ ∧ Normal t ∧ i = {s | HasType P Γ t (.sort s)}
  let T := fun (i j k : V) => F i ∧ F j ∧ F k ∧ k = {c | ∃ a ∈ i, ∃ b ∈ j, P.rule a b c}
  let E := fun (i k : V) (p : Bool) => if p then ∃ j, T i j k else (F i ∧ F k ∧ k ⊂ i) ∨ ∃ j, T j i k
  let Path := fun (e : V → V → Bool → Prop) (i j : V) (b : Bool) =>
    ∀ R : V → V → Bool → Prop, (∀ x, R x x false) → (∀ x y z p q, e x y p → R y z q → R x z (p.xor q)) → R i j b
  let Cmp := fun e (C : Set V) => ∃ r ∈ C, ∀ v, v ∈ C ↔ (∃ b, Path e r v b) ∧ ∃ b, Path e v r b
  ¬ (∃ C, Cmp E C ∧ (∃ i ∈ C, Path E i i true) ∧ (∃ i ∈ C, ∃ j ∈ C, ∃ k ∈ C, T i j k)) → ∀ Γ f a D E, HasType P Γ f (.pi D E) → HasType P Γ a D → StronglyNormalizing f → StronglyNormalizing a → StronglyNormalizing (.app f a)

def H2 : Prop := ∀ n (P : Specification (Fin n)), SystemWeaklyNormalizing P →
  let V := Set (Fin n)
  let F := fun (i : V) => i.Nonempty ∧ ∃ Γ t, ValidContext P Γ ∧ Normal t ∧ i = {s | HasType P Γ t (.sort s)}
  let T := fun (i j k : V) => F i ∧ F j ∧ F k ∧ k = {c | ∃ a ∈ i, ∃ b ∈ j, P.rule a b c}
  let E := fun (i k : V) (p : Bool) => if p then ∃ j, T i j k else (F i ∧ F k ∧ k ⊂ i) ∨ ∃ j, T j i k
  let Path := fun (e : V → V → Bool → Prop) (i j : V) (b : Bool) =>
    ∀ R : V → V → Bool → Prop, (∀ x, R x x false) → (∀ x y z p q, e x y p → R y z q → R x z (p.xor q)) → R i j b
  let Cmp := fun e (C : Set V) => ∃ r ∈ C, ∀ v, v ∈ C ↔ (∃ b, Path e r v b) ∧ ∃ b, Path e v r b
  let A := fun s => {t | P.sortAxioms s t}
  let Pos := Relation.ReflTransGen (fun i j => E i j false)
  let L := fun (C : Set V) i => ∃ s, {s} ∈ C ∧ (A s).Nonempty ∧ Pos (A s) i
  let G := fun C i k (b : Bool) => L C i ∧ L C k ∧ (if b then ∃ j, L C j ∧ T i j k else E i k false)
  let D := fun (C : Set V) i => L C i ∧ ∃ j ∈ C, ∃ k ∈ C, T i j k
  (∃ C, Cmp E C ∧ (∃ i ∈ C, Path E i i true) ∧ (∃ i ∈ C, ∃ j ∈ C, ∃ k ∈ C, T i j k)) → ¬ (∃ C, Cmp E C ∧ (∃ i ∈ C, Path E i i true) ∧ (∃ i ∈ C, ∃ j ∈ C, ∃ k ∈ C, T i j k) ∧
    ∃ U, Cmp (G C) U ∧ (∀ i ∈ U, ∀ b, ∃ d, D C d ∧ Path (G C) i d b) ∧
    (∃ i ∈ U, ∃ k ∈ U, G C i k true) ∧ ∃ i j k s, T i j k ∧ j ∈ U ∧ k ∈ U ∧ {s} ∈ U ∧ (A s).Nonempty ∧ Pos (A s) i) → ∀ Γ f a D E, HasType P Γ f (.pi D E) → HasType P Γ a D → StronglyNormalizing f → StronglyNormalizing a → StronglyNormalizing (.app f a)

def H3 : Prop := ∀ n (P : Specification (Fin n)), SystemWeaklyNormalizing P →
  let V := Set (Fin n)
  let F := fun (i : V) => i.Nonempty ∧ ∃ Γ t, ValidContext P Γ ∧ Normal t ∧ i = {s | HasType P Γ t (.sort s)}
  let T := fun (i j k : V) => F i ∧ F j ∧ F k ∧ k = {c | ∃ a ∈ i, ∃ b ∈ j, P.rule a b c}
  let E := fun (i k : V) (p : Bool) => if p then ∃ j, T i j k else (F i ∧ F k ∧ k ⊂ i) ∨ ∃ j, T j i k
  let Path := fun (e : V → V → Bool → Prop) (i j : V) (b : Bool) =>
    ∀ R : V → V → Bool → Prop, (∀ x, R x x false) → (∀ x y z p q, e x y p → R y z q → R x z (p.xor q)) → R i j b
  let Cmp := fun e (C : Set V) => ∃ r ∈ C, ∀ v, v ∈ C ↔ (∃ b, Path e r v b) ∧ ∃ b, Path e v r b
  let A := fun s => {t | P.sortAxioms s t}
  let Pos := Relation.ReflTransGen (fun i j => E i j false)
  let L := fun (C : Set V) i => ∃ s, {s} ∈ C ∧ (A s).Nonempty ∧ Pos (A s) i
  let G := fun C i k (b : Bool) => L C i ∧ L C k ∧ (if b then ∃ j, L C j ∧ T i j k else E i k false)
  let D := fun (C : Set V) i => L C i ∧ ∃ j ∈ C, ∃ k ∈ C, T i j k
  ¬ (∃ C, Cmp E C ∧ (∃ i ∈ C, Path E i i true) ∧ (∃ i ∈ C, ∃ j ∈ C, ∃ k ∈ C, T i j k) ∧
    ∃ U, Cmp (G C) U ∧ (∀ i ∈ U, ∀ b, ∃ d, D C d ∧ Path (G C) i d b) ∧
    (∃ i ∈ U, ∃ k ∈ U, G C i k true) ∧ ∃ i j k s, T i j k ∧ j ∈ U ∧ k ∈ U ∧ {s} ∈ U ∧ (A s).Nonempty ∧ Pos (A s) i)

theorem main : H1 → H2 → H3 → OMA.R_wpc_barendregt_geuvers_klop_R1.H2 := by
  intro regular mixed exclude n P hw
  classical
  exact Classical.byCases (fun h => mixed n P hw h (exclude n P hw)) (fun h => regular n P hw h)
end OMA.R_wpc_barendregt_geuvers_klop_R1_H2_R1
