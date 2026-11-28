import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

namespace OMA.S_wpc_one_way_functions

/-- The inverter receives the unary input length, the function value, and its coin tape.
The separators are distinguished from both bit symbols. -/
def encodeInverterInput (input : ℕ × List Bool × List Bool) : List (Option Bool) :=
  List.replicate input.1 (some true) ++ [none] ++ input.2.1.map some ++ [none] ++
    input.2.2.map some

/-- Success probability over an independent uniform input and uniform coin tape.
Success means that the inverter returns any preimage of the supplied value. -/
noncomputable def inversionProbability (f : List Bool → List Bool)
    (invert : ℕ × List Bool × List Bool → List Bool) (n coins : ℕ) : ℚ := by
  classical
  let successful := Finset.univ.filter (fun sample : (Fin n → Bool) × (Fin coins → Bool) =>
    let y := f (List.ofFn sample.1)
    f (invert (n, y, List.ofFn sample.2)) = y)
  exact (successful.card : ℚ) / (2 : ℚ) ^ (n + coins)

/-- There exists a polynomial-time function on binary strings whose inversion
probability is negligible for every uniform probabilistic polynomial-time inverter. -/
theorem main :
    ∃ f : List Bool → List Bool,
      Nonempty (Turing.TM2ComputableInPolyTime id id f) ∧
        ∀ (invert : ℕ × List Bool × List Bool → List Bool) (coins : Polynomial ℕ),
          Nonempty (Turing.TM2ComputableInPolyTime encodeInverterInput id invert) →
            ∀ k : ℕ, ∃ N : ℕ, 0 < N ∧
              ∀ n : ℕ, N ≤ n →
                inversionProbability f invert n (coins.eval n) < 1 / (n : ℚ) ^ k := by
  sorry

end OMA.S_wpc_one_way_functions
