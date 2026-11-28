import Mathlib

namespace OMA.S_opg_approximation_ratio_for_k_outerplanar_graphs

structure RoutingInput where
  order : ℕ
  adjacency : Fin order → Fin order → Bool
  symmetric : ∀ u v, adjacency u v = adjacency v u
  loopless : ∀ v, ¬ adjacency v v
  demands : List (Fin order × Fin order)
  distinctTerminals : ∀ d ∈ demands, d.1 ≠ d.2

def RoutingInput.graph (I : RoutingInput) : SimpleGraph (Fin I.order) :=
  SimpleGraph.mk' ⟨I.adjacency, I.symmetric, I.loopless⟩

def HasTreewidthAtMost (I : RoutingInput) (r : ℕ) : Prop :=
  ∃ (m : ℕ) (T : SimpleGraph (Fin m)) (bag : Fin m → Finset (Fin I.order)),
    T.IsTree ∧ (∀ t, (bag t).card ≤ r + 1) ∧
      (∀ v, ∃ t, v ∈ bag t) ∧
      (∀ u v, I.graph.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
      ∀ v, (T.induce {t | v ∈ bag t}).Connected

/-- Both orientations represent the same undirected edge. -/
def pathEdges (path : List ℕ) : Set (ℕ × ℕ) :=
  {e | e ∈ path.zip path.tail ∨ e.swap ∈ path.zip path.tail}

def RoutesDemand (I : RoutingInput) (path : List ℕ) : Prop :=
  path.Nodup ∧
  (∀ (a b : ℕ), (a, b) ∈ path.zip path.tail →
    ∃ u v : Fin I.order, u.val = a ∧ v.val = b ∧ I.graph.Adj u v) ∧
  ∃ d ∈ I.demands, path.head? = some d.1.val ∧ path.getLast? = some d.2.val

def Feasible (I : RoutingInput) (paths : List (List ℕ)) : Prop :=
  (∀ path ∈ paths, RoutesDemand I path) ∧
    paths.Pairwise (fun p q => Disjoint (pathEdges p) (pathEdges q))

abbrev Alphabet := Computability.Γ'

def encodeNat (n : ℕ) : List Alphabet :=
  (Computability.encodeNat n).map Computability.Γ'.bit ++ [.comma]

def encodeInput (I : RoutingInput) : List Alphabet :=
  encodeNat I.order ++
    (List.ofFn fun u : Fin I.order =>
      List.ofFn fun v : Fin I.order => Computability.Γ'.bit (I.adjacency u v)).flatten ++
    encodeNat I.demands.length ++
    I.demands.flatMap (fun d => encodeNat d.1.val ++ encodeNat d.2.val)

def encodePaths (paths : List (List ℕ)) : List Alphabet :=
  encodeNat paths.length ++ paths.flatMap (fun p => encodeNat p.length ++ p.flatMap encodeNat)

/-- Maximum edge-disjoint paths has a polynomial-time constant-factor
approximation at each fixed bound on the treewidth. -/
theorem main :
    ∀ r : ℕ, ∃ (C : ℕ) (route : RoutingInput → List (List ℕ)),
      0 < C ∧ Nonempty (Turing.TM2ComputableInPolyTime encodeInput encodePaths route) ∧
        ∀ I : RoutingInput, HasTreewidthAtMost I r →
          Feasible I (route I) ∧
            ∀ paths : List (List ℕ), Feasible I paths →
              paths.length ≤ C * (route I).length := by
  sorry

end OMA.S_opg_approximation_ratio_for_k_outerplanar_graphs
