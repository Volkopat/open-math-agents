import Mathlib

namespace OMA.S_opg_ptas_for_feedback_arc_set_in_tournaments

abbrev Input := Σ n : ℕ, Fin n → Fin n → Bool

abbrev Tolerance := {ε : ℚ // 0 < ε}

/-- A tournament is an orientation of the complete simple graph. -/
def IsTournament (input : Input) : Prop :=
  (∀ v, input.2 v v = false) ∧
    (∀ u v, u ≠ v → input.2 u v = !(input.2 v u))

/-- The backward arcs of a ranking form a feedback arc set. -/
def cost {n : ℕ} (adj : Fin n → Fin n → Bool) (ranking : Equiv.Perm (Fin n)) : ℕ :=
  ((Finset.univ : Finset (Fin n × Fin n)).filter
    (fun e => adj e.1 e.2 = true ∧ ranking e.2 < ranking e.1)).card

/-- A binary integer field followed by a separator. -/
def encodeNatural (n : ℕ) : List Computability.Γ' :=
  (Computability.encodeNat n).map Computability.Γ'.bit ++ [.comma]

/-- The rational accuracy, vertex count, and adjacency matrix in row order. -/
def encodeInput (ε : Tolerance) (input : Input) : List Computability.Γ' :=
  encodeNatural ε.val.num.natAbs ++ encodeNatural ε.val.den ++ encodeNatural input.1 ++
    (List.ofFn fun v : Fin input.1 =>
      List.ofFn fun w : Fin input.1 => Computability.Γ'.bit (input.2 v w)).flatten

/-- A uniform deterministic polynomial-time approximation scheme for tournament
feedback arc sets. The polynomial bound may depend on the requested accuracy. -/
theorem main :
    ∃ (machine : Turing.TM2ComputableAux Computability.Γ' Computability.Γ')
      (answer : Tolerance → Input → List ℕ),
      ∀ ε : Tolerance, ∃ bound : Polynomial ℕ,
        ∀ input : Input,
          let word := encodeInput ε input
          let result := (answer ε input).flatMap encodeNatural
          Nonempty (Turing.TM2OutputsInTime machine.tm
            (word.map machine.inputAlphabet.symm) (some (result.map machine.outputAlphabet.symm))
            (bound.eval word.length)) ∧
          (IsTournament input →
            ∃ ranking : Equiv.Perm (Fin input.1),
              answer ε input = List.ofFn (fun v : Fin input.1 => (ranking v).val) ∧
                ∀ optimumCandidate : Equiv.Perm (Fin input.1),
                  (cost input.2 ranking : ℚ) ≤ (1 + ε.val) * cost input.2 optimumCandidate) := by
  sorry

end OMA.S_opg_ptas_for_feedback_arc_set_in_tournaments
