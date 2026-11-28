import Mathlib.ModelTheory.ElementaryMaps
import Mathlib.SetTheory.ZFC.VonNeumann

/-! # Can one take roots of rank-into-rank embeddings infinitely many times?
Joseph Van Name, https://mathoverflow.net/questions/221720 (2015).
Proposed formalization by LDJAI. Elementarity has its first-order meaning for
membership on the actual von Neumann hierarchy. -/
open FirstOrder FirstOrder.Language

namespace OMA.S_mo_221720

inductive SetRel : ℕ → Type
  | mem : SetRel 2

def setLang : FirstOrder.Language := ⟨fun _ => Empty, SetRel⟩

abbrev VSet (lam : Ordinal.{0}) := {x : ZFSet.{0} // x.rank < lam}

instance (lam : Ordinal.{0}) : setLang.Structure (VSet lam) where
  funMap f := nomatch f
  RelMap | .mem => fun x => (x 0).val ∈ (x 1).val

/-- The graph pairs of a map whose ranks are below θ. Their union across all
θ below a limit rank is the full graph. -/
noncomputable def graphAt {lam : Ordinal.{0}} (f : VSet lam → VSet lam) (θ : Ordinal.{0}) :
    ZFSet.{0} :=
  (ZFSet.vonNeumann θ).sep (fun z => ∃ x : VSet lam, z = ZFSet.pair x.val (f x).val)

/-- Laver application takes the union of images of bounded pieces of the
graph and reads off its unique value. The default totalizes the definition on
arbitrary maps whose graph union fails to define a unique value. -/
noncomputable def app {lam : Ordinal.{0}} (f g : VSet lam → VSet lam) (x : VSet lam) : VSet lam := by
  classical
  have hbound (θ : Ordinal.{0}) : (graphAt g θ).rank ≤ θ :=
    (ZFSet.rank_mono ZFSet.sep_subset).trans_eq (ZFSet.rank_vonNeumann θ)
  let R (y : VSet lam) := ∃ θ : Ordinal.{0}, ∃ h : θ < lam,
    ZFSet.pair x.val y.val ∈ (f ⟨graphAt g θ, (hbound θ).trans_lt h⟩).val
  exact if h : ∃! y, R y then h.choose else x

inductive UnaryTerm
  | var
  | ap (left right : UnaryTerm)
  | comp (left right : UnaryTerm)

noncomputable def UnaryTerm.eval {lam : Ordinal.{0}}
    (t : UnaryTerm) (j : VSet lam → VSet lam) : VSet lam → VSet lam :=
  match t with
  | .var => j
  | .ap a b => app (a.eval j) (b.eval j)
  | .comp a b => a.eval j ∘ b.eval j

def RootChain (lam : Ordinal.{0}) (t : ℕ → UnaryTerm) : Prop :=
  ∃ J : ℕ → VSet lam ↪ₑ[setLang] VSet lam,
    (∀ n, ∃ x, J n x ≠ x) ∧
    ∀ n, (J n : VSet lam → VSet lam) =
      app ((t n).eval (J (n+1))) (J (n+1))

/-- Relative possibility at a cardinal means that a nontrivial self-embedding
already exists at a cardinal height. The first clause asks for equivalence of
existence, across all cardinal heights. The other two clauses ask for
nonexistence at every cardinal height, including the single-term variant. -/
theorem main :
  ((∃ (c : Cardinal.{0}) (j : VSet c.ord ↪ₑ[setLang] VSet c.ord), ∃ x, j x ≠ x) ↔
    ∃ (c : Cardinal.{0}) (t : ℕ → UnaryTerm), RootChain c.ord t) ∧
  (∀ (c : Cardinal.{0}) (t : ℕ → UnaryTerm), (Set.range t).Finite → ¬ RootChain c.ord t) ∧
  (∀ (c : Cardinal.{0}) (t : UnaryTerm), ¬ RootChain c.ord (fun _ => t)) := by
  sorry

end OMA.S_mo_221720
