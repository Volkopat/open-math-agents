import Mathlib

/-!
# Prescribing the second eigenvector with a symmetric rank-one update

Source: Vedarun, https://mathoverflow.net/questions/66524 (CC BY-SA 3.0).
Credit: @connoranderson. Igor Rivin discussed perturbations preserving an
existing eigenvector. The questioner specified the second-smallest eigenvalue
and signed symmetric rank-one perturbations. The result applies to any
real symmetric input, including weighted graph Laplacians.

For a prescribed unit vector v, let α be its Rayleigh quotient. At every
target t different from α, the update is unique. The number of original
eigenvalues strictly below t falls by one precisely when α < t, and
the number strictly above t falls by one precisely when t < α. These
counts decide whether t occupies the second position, including ties.

At t = α a solution requires Av = tv. The allowable directions are then
orthogonal to v, and the scalar secular polynomial, computed from A and
the update direction, gives the exact ordering test.
-/
namespace OMA.S_mo_66524
open Matrix Polynomial Finset
abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

noncomputable def update {n : ℕ} (c : ℝ) (u : Vec n) : Mat n := c • vecMulVec u u
noncomputable def ray {n : ℕ} (A : Mat n) (v : Vec n) : ℝ := v ⬝ᵥ (A *ᵥ v)
noncomputable def residual {n : ℕ} (A : Mat n) (v : Vec n) (t : ℝ) : Vec n :=
  t • v - A *ᵥ v

noncomputable def below {n : ℕ} (A : Mat n) (t : ℝ) : ℕ :=
  (A.charpoly.roots.filter (fun s => s < t)).card
noncomputable def above {n : ℕ} (A : Mat n) (t : ℝ) : ℕ :=
  (A.charpoly.roots.filter (fun s => t < s)).card

/-- The position test permits ties, with all real roots counted with multiplicity. -/
def secondRoot (p : ℝ[X]) (t : ℝ) : Prop :=
  (p.roots.filter (fun s => s < t)).card ≤ 1 ∧ 2 ≤ (p.roots.filter (fun s => s ≤ t)).card

noncomputable def secular {n : ℕ} (A : Mat n) (c : ℝ) (u : Vec n) : ℝ[X] :=
  A.charpoly - C c * ((fun i => C (u i)) ⬝ᵥ (A.charmatrix.adjugate *ᵥ (fun i => C (u i))))

theorem main :
    (∀ {n : ℕ} (A H : Mat n) (v : Vec n) (t : ℝ),
      A.IsSymm → H.IsSymm → H.rank = 1 → v ⬝ᵥ v = 1 →
      ((A+H) *ᵥ v = t • v ∧ secondRoot (A+H).charpoly t ↔
        (t ≠ ray A v ∧ H = update (t-ray A v)⁻¹ (residual A v t) ∧
          below A t ≤ 1 + (if ray A v < t then 1 else 0) ∧
          above A t + 2 ≤ n + (if t < ray A v then 1 else 0)) ∨
        (t = ray A v ∧ A *ᵥ v = t • v ∧ ∃ c : ℝ, ∃ u : Vec n,
          c ≠ 0 ∧ u ≠ 0 ∧ u ⬝ᵥ v = 0 ∧ H = update c u ∧ secondRoot (secular A c u) t))) ∧
    (∀ {n : ℕ} (A : Mat n) (v : Vec n) (t : ℝ), A.IsSymm → v ⬝ᵥ v = 1 → t ≠ ray A v →
      let B := A + update (t-ray A v)⁻¹ (residual A v t)
      (update (t-ray A v)⁻¹ (residual A v t)).rank = 1 ∧ B *ᵥ v = t • v ∧
      below A t = below B t + (if ray A v < t then 1 else 0) ∧
      above A t = above B t + (if t < ray A v then 1 else 0)) := by
  sorry

end OMA.S_mo_66524
