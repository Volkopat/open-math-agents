import Mathlib

namespace OMA.S_opg_complexity_of_the_h_factor_problem

open scoped BigOperators

abbrev Alphabet := Computability.Γ'
abbrev CNF := List (List (ℕ × Bool))

def encodeNat (n : ℕ) : List Alphabet :=
  (Computability.encodeNat n).map Computability.Γ'.bit ++ [.comma]

def encodeList {α : Type} (encode : α → List Alphabet) (xs : List α) : List Alphabet :=
  encodeNat xs.length ++ xs.flatMap encode

def encodeCNF (formula : CNF) : List Alphabet :=
  encodeList (encodeList (fun lit => encodeNat lit.1 ++ [.bit lit.2])) formula

def Satisfiable (formula : CNF) : Prop :=
  ∃ assignment : ℕ → Bool,
    ∀ clause ∈ formula, ∃ literal ∈ clause, assignment literal.1 = literal.2

/-- A finite simple graph represented by its Boolean adjacency matrix. -/
structure GraphInput where
  order : ℕ
  adjacency : Fin order → Fin order → Bool
  symmetric : ∀ u v, adjacency u v = adjacency v u
  loopless : ∀ v, ¬ adjacency v v

def GraphInput.graph (G : GraphInput) : SimpleGraph (Fin G.order) :=
  SimpleGraph.mk' ⟨G.adjacency, G.symmetric, G.loopless⟩

def encodeGraph (G : GraphInput) : List Alphabet :=
  encodeNat G.order ++
    (List.ofFn fun u : Fin G.order =>
      List.ofFn fun v : Fin G.order => Computability.Γ'.bit (G.adjacency u v)).flatten

/-- A partition of the whole vertex set into copies of H as subgraphs. -/
def HasFactor {V : Type} (H : SimpleGraph V) (G : GraphInput) : Prop :=
  ∃ (t : ℕ) (label : Fin t × V ≃ Fin G.order),
    ∀ j u v, H.Adj u v → G.graph.Adj (label (j, u)) (label (j, v))

/-- A polynomial-time many-one reduction from CNF satisfiability whose outputs
satisfy the minimum-degree promise on both yes and no instances. -/
def DenseFactorNPHard {V : Type} (H : SimpleGraph V) (c : ℝ) : Prop :=
  ∃ reduce : CNF → GraphInput,
    Nonempty (Turing.TM2ComputableInPolyTime encodeCNF encodeGraph reduce) ∧
      ∀ formula,
        let G := reduce formula
        0 < G.order ∧
        (∀ v, c * (G.order : ℝ) ≤ ((G.graph.neighborSet v).ncard : ℝ)) ∧
        (Satisfiable formula ↔ HasFactor H G)

/-- The critical chromatic number for a complete multipartite graph with
nonempty parts listed in increasing order of size. -/
noncomputable def criticalChromaticNumber {r : ℕ} (size : Fin (r + 2) → ℕ) : ℝ :=
  let order : ℝ := (∑ i, size i : ℕ)
  ((r : ℝ) + 1) * order / (order - (size 0 : ℝ))

/-- The positive minimum-degree fractions in Kühn and Osthus, Theorem 3.1. -/
theorem main :
    ∀ (r : ℕ) (size : Fin (r + 2) → ℕ),
      (∀ i, 0 < size i) → Monotone size →
      ((1 ≤ r ∧ ∀ i, size i = 1) ∨ 2 ≤ size 1) →
      ∀ c : ℝ, 0 < c → c < 1 - (criticalChromaticNumber size)⁻¹ →
        DenseFactorNPHard
          (SimpleGraph.completeMultipartiteGraph fun i : Fin (r + 2) => Fin (size i)) c := by
  sorry

end OMA.S_opg_complexity_of_the_h_factor_problem
