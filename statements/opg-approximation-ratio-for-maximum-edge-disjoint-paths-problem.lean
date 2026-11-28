import Mathlib

namespace OMA.S_opg_approximation_ratio_for_maximum_edge_disjoint_paths_problem

abbrev Alphabet := Computability.Γ'

structure Input where
  vertices : ℕ
  adj : Fin vertices → Fin vertices → Bool
  demands : List (Fin vertices × Fin vertices)

/-- The graph admits a plane straight-line embedding, allowing incident edges
to meet at their common endpoint. -/
def PlanarSimple (I : Input) : Prop :=
  (∀ a, I.adj a a = false) ∧ (∀ a b, I.adj a b = I.adj b a) ∧
    ∃ p : Fin I.vertices → ℝ × ℝ, Function.Injective p ∧
      (∀ a b v, I.adj a b = true → v ≠ a → v ≠ b →
        p v ∉ segment ℝ (p a) (p b)) ∧
      ∀ a b c d, I.adj a b = true → I.adj c d = true →
        ¬ ((a = c ∧ b = d) ∨ (a = d ∧ b = c)) →
        ∀ x ∈ segment ℝ (p a) (p b), x ∈ segment ℝ (p c) (p d) →
          ∃ v, (v = a ∨ v = b) ∧ (v = c ∨ v = d) ∧ p v = x

abbrev Routing := List (ℕ × List ℕ)

def consecutive (path : List ℕ) : List (ℕ × ℕ) :=
  path.zip path.tail

def undirectedEdges (path : List ℕ) : Finset (ℕ × ℕ) :=
  ((consecutive path).map (fun e => (min e.1 e.2, max e.1 e.2))).toFinset

/-- Each routed demand is used at most once and receives a simple path.
Path pairs may share vertices, with edge capacity one. -/
def Feasible (I : Input) (R : Routing) : Prop :=
  (R.map Prod.fst).Nodup ∧
    (∀ r ∈ R, ∃ s t : Fin I.vertices,
      I.demands[r.1]? = some (s, t) ∧ r.2.head? = some s.val ∧
      r.2.getLast? = some t.val ∧ r.2.Nodup ∧
      ∀ e ∈ consecutive r.2, ∃ a b : Fin I.vertices,
        e = (a.val, b.val) ∧ I.adj a b = true) ∧
    ∀ r ∈ R, ∀ q ∈ R, r.1 ≠ q.1 →
      Disjoint (undirectedEdges r.2) (undirectedEdges q.2)

def encodeNat (n : ℕ) : List Alphabet :=
  (Computability.encodeNat n).map Computability.Γ'.bit ++ [.comma]

def encodeList {α : Type} (encode : α → List Alphabet) (xs : List α) : List Alphabet :=
  encodeNat xs.length ++ xs.flatMap encode

def encodeInput (I : Input) : List Alphabet :=
  encodeNat I.vertices ++
    (List.ofFn fun a : Fin I.vertices =>
      List.ofFn fun b : Fin I.vertices => Computability.Γ'.bit (I.adj a b)).flatten ++
    encodeList (fun e => encodeNat e.1.val ++ encodeNat e.2.val) I.demands

def encodeRouting (R : Routing) : List Alphabet :=
  encodeList (fun r => encodeNat r.1 ++ encodeList encodeNat r.2) R

abbrev CNF := List (List (ℕ × Bool))

def encodeCNF (φ : CNF) : List Alphabet :=
  encodeList (encodeList (fun lit => encodeNat lit.1 ++ [Computability.Γ'.bit lit.2])) φ

def Satisfiable (φ : CNF) : Prop :=
  ∃ valuation : ℕ → Bool, ∀ clause ∈ φ, ∃ lit ∈ clause, valuation lit.1 = lit.2

/-- A deterministic SAT machine with a bound of the form L raised to O(log L). -/
def HasQuasipolynomialSAT : Prop :=
  ∃ (answer : CNF → Bool)
    (machine : Turing.TM2ComputableAux Alphabet Bool) (C : ℕ), 0 < C ∧
    ∀ φ : CNF,
      let word := encodeCNF φ
      let size := word.length + 2
      (answer φ = true ↔ Satisfiable φ) ∧
      Nonempty (Turing.TM2OutputsInTime machine.tm
        (word.map machine.inputAlphabet.symm) (some ([answer φ].map machine.outputAlphabet.symm))
        (size ^ (C * (Nat.log 2 size + 1))))

def HasApproximation (c : ℝ) : Prop :=
  ∃ answer : Input → Routing,
    Nonempty (Turing.TM2ComputableInPolyTime encodeInput encodeRouting answer) ∧
    ∀ I : Input, 2 ≤ I.vertices → PlanarSimple I →
      (∀ e ∈ I.demands, e.1 ≠ e.2) →
      Feasible I (answer I) ∧
      ∀ alternative : Routing, Feasible I alternative →
        (alternative.length : ℝ) ≤
          Real.rpow 2 (c * Real.sqrt (Real.log (I.vertices : ℝ))) * (answer I).length

/-- The Chuzhoy–Kim–Nimavat inapproximability bound for planar edge-disjoint paths. -/
theorem main :
    ∃ c : ℝ, 0 < c ∧ (HasApproximation c → HasQuasipolynomialSAT) := by
  sorry

end OMA.S_opg_approximation_ratio_for_maximum_edge_disjoint_paths_problem
