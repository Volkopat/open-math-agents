import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval

namespace OMA.S_mo_507835

/-- Integer vectors in the coordinate box and on the specified sum layer. -/
noncomputable def latticeLayer (n N : ℕ) (total : ℤ) : Finset (Fin n → ℤ) :=
  (Fintype.piFinset fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ)).filter
    (fun v => (∑ i : Fin n, v i) = total)

/-- The set obtained by adding the signed coordinate step once in each direction. -/
def shiftedNeighbors {n : ℕ} (v : Fin n → ℤ) (sign : ℤ) : Finset (Fin n → ℤ) :=
  Finset.univ.image fun i : Fin n => fun j => v j + if j = i then sign else 0

/-- The stronger proposed upper bound for the average number of selected neighbors. -/
theorem main :
    ∀ (n : ℕ), 0 < n →
      ∀ ε : ℝ, 0 < ε →
        ∃ N₀ : ℕ, 0 < N₀ ∧
          ∀ N : ℕ, N₀ ≤ N →
            let minusLayer := latticeLayer n N 1
            let plusLayer := latticeLayer n N (-1)
            ∀ (Rminus Rplus : (Fin n → ℤ) → Finset (Fin n → ℤ)),
              (∀ v ∈ minusLayer, Rminus v ⊆ shiftedNeighbors v (-1)) →
              (∀ w ∈ plusLayer, Rplus w ⊆ shiftedNeighbors w 1) →
              (∀ v ∈ minusLayer, ∀ w ∈ plusLayer, (Rminus v ∩ Rplus w).card ≤ 1) →
                let total := (∑ v ∈ minusLayer, (Rminus v).card) +
                  (∑ w ∈ plusLayer, (Rplus w).card)
                (total : ℝ) / ((n : ℝ) * minusLayer.card) ≤ 1 + (Real.sqrt n)⁻¹ + ε := by
  sorry

end OMA.S_mo_507835
