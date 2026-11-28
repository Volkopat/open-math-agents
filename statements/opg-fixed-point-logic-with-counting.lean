import Mathlib

namespace OMA.S_opg_fixed_point_logic_with_counting

inductive VariableSort
  | vertex
  | number

/-- A typed de Bruijn index into a context. -/
inductive Position {α : Type} (a : α) : List α → Type
  | here {tail : List α} : Position a (a :: tail)
  | there {b : α} {tail : List α} : Position a tail → Position a (b :: tail)

/-- A heterogeneous tuple, used for both assignments and argument lists. -/
def Tuple {α : Type} (Value : α → Type) : List α → Type
  | [] => Unit
  | a :: tail => Value a × Tuple Value tail

def Tuple.get {α : Type} {Value : α → Type} {a : α} {ctx : List α} :
    Position a ctx → Tuple Value ctx → Value a
  | .here, env => env.1
  | .there i, env => Tuple.get i env.2

def Tuple.append {α : Type} {Value : α → Type} {tail : List α} :
    (head : List α) → Tuple Value head → Tuple Value tail → Tuple Value (head ++ tail)
  | [], _, ys => ys
  | _ :: rest, xs, ys => (xs.1, Tuple.append rest xs.2 ys)

def Tuple.select {α : Type} {Value : α → Type} {ctx : List α} :
    (sorts : List α) → Tuple (fun a => Position a ctx) sorts →
      Tuple Value ctx → Tuple Value sorts
  | [], _, _ => ()
  | _ :: tail, args, env => (Tuple.get args.1 env, Tuple.select tail args.2 env)

/-- Fixed-point logic with counting over the vocabulary of unordered simple graphs.
The second context lists the tuple sorts of the in-scope relation variables. -/
inductive Formula : List VariableSort → List (List VariableSort) → Type
  | equal {Γ : List VariableSort} {Δ : List (List VariableSort)} {s : VariableSort}
      (x y : Position s Γ) : Formula Γ Δ
  | edge {Γ : List VariableSort} {Δ : List (List VariableSort)}
      (x y : Position .vertex Γ) : Formula Γ Δ
  | numberLE {Γ : List VariableSort} {Δ : List (List VariableSort)}
      (x y : Position .number Γ) : Formula Γ Δ
  | relation {Γ sorts : List VariableSort} {Δ : List (List VariableSort)}
      (r : Position sorts Δ) (args : Tuple (fun s => Position s Γ) sorts) : Formula Γ Δ
  | neg {Γ : List VariableSort} {Δ : List (List VariableSort)}
      (body : Formula Γ Δ) : Formula Γ Δ
  | conj {Γ : List VariableSort} {Δ : List (List VariableSort)}
      (left right : Formula Γ Δ) : Formula Γ Δ
  | existsVar {Γ : List VariableSort} {Δ : List (List VariableSort)} (s : VariableSort)
      (body : Formula (s :: Γ) Δ) : Formula Γ Δ
  | countEq {Γ : List VariableSort} {Δ : List (List VariableSort)}
      (value : Position .number Γ) (body : Formula (.vertex :: Γ) Δ) : Formula Γ Δ
  | ifp {Γ sorts : List VariableSort} {Δ : List (List VariableSort)}
      (body : Formula (sorts ++ Γ) (sorts :: Δ))
      (args : Tuple (fun s => Position s Γ) sorts) : Formula Γ Δ

def Value (n : ℕ) : VariableSort → Type
  | .vertex => Fin n
  | .number => Fin (n + 1)

abbrev Assignment (n : ℕ) (sorts : List VariableSort) := Tuple (Value n) sorts

abbrev RelationAssignment (n : ℕ) (Δ : List (List VariableSort)) :=
  Tuple (fun sorts => Set (Assignment n sorts)) Δ

/-- Inflationary iteration starts from the empty relation. Every strict stage
adds a tuple, and there are at most (n+1)^arity tuples of the given sorts. -/
def Holds {n : ℕ} (G : SimpleGraph (Fin n)) :
    {Γ : List VariableSort} → {Δ : List (List VariableSort)} →
      Formula Γ Δ → Assignment n Γ → RelationAssignment n Δ → Prop
  | _, _, .equal x y, env, _ => Tuple.get x env = Tuple.get y env
  | _, _, .edge x y, env, _ => G.Adj (Tuple.get (Value := Value n) x env) (Tuple.get (Value := Value n) y env)
  | _, _, .numberLE x y, env, _ =>
      (Tuple.get (Value := Value n) x env).val ≤ (Tuple.get (Value := Value n) y env).val
  | _, _, .relation r args, env, rels =>
      Tuple.select _ args env ∈ Tuple.get r rels
  | _, _, .neg body, env, rels => ¬ Holds G body env rels
  | _, _, .conj left right, env, rels => Holds G left env rels ∧ Holds G right env rels
  | _, _, .existsVar s body, env, rels =>
      ∃ x : Value n s, Holds G body (x, env) rels
  | _, _, .countEq value body, env, rels =>
      Nat.card {x : Fin n // Holds G body (x, env) rels} =
        (Tuple.get (Value := Value n) value env).val
  | _, _, @Formula.ifp _ sorts _ body args, env, rels =>
      let step (r : Set (Assignment n sorts)) : Set (Assignment n sorts) :=
        r ∪ {t | Holds G body (Tuple.append sorts t env) (r, rels)}
      Tuple.select sorts args env ∈ (step^[((n + 1) ^ sorts.length)]) ∅

/-- The first OPG question: perfect matching in finite unordered graphs
is expressible by a single sentence of fixed-point logic with counting. -/
theorem main :
    ∃ φ : Formula [] [], ∀ n : ℕ, ∀ G : SimpleGraph (Fin n),
      Holds G φ () () ↔ ∃ M : G.Subgraph, M.IsPerfectMatching := by
  sorry

end OMA.S_opg_fixed_point_logic_with_counting
