import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Perm
import Mathlib.Topology.Instances.Real.Lemmas

/-! Source: https://mathoverflow.net/questions/101886 -/

open Filter
open scoped Topology

namespace OMA.S_mo_101886

def middleLayer (n : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ : Finset (Fin n)).powersetCard ((n + 1) / 2)

def largestUnion {n : ℕ} (F : Finset (Finset (Fin n))) : ℕ :=
  (Finset.univ : Finset (Equiv.Perm (Fin n))).sup fun p =>
    (F ∪ F.image (fun s => s.image p)).card

noncomputable def minMaxUnion (n k : ℕ) : ℕ :=
  sInf {v : ℕ | ∃ F ∈ (middleLayer n).powersetCard k, v = largestUnion F}

/-- The middle-layer minimax union size, at half density, approaches
three quarters of that layer after normalization. -/
theorem main :
    Tendsto (fun n : ℕ =>
      (minMaxUnion n ((middleLayer n).card / 2) : ℝ) / ((middleLayer n).card : ℝ))
      atTop (𝓝 (3 / 4 : ℝ)) := by
  sorry

end OMA.S_mo_101886
