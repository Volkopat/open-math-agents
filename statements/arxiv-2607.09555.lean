import Mathlib

namespace OMA.S_arxiv_2607_09555

/-- Inter-layer Lennard-Jones interaction floor kernel `κ(d) = -v̄(d)` from
arXiv:2607.09555 (eq. (4)): `κ(0) = 0`, `κ(1) = κ(2) = 1`, and
`κ(d) = 2 (d - 1)^{-6} - (d - 1)^{-12}` for `d ≥ 3`. -/
noncomputable def kappa (d : ℕ) : ℝ :=
  if d = 0 then 0
  else if d ≤ 2 then 1
  else 2 / ((d - 1 : ℕ) : ℝ) ^ 6 - 1 / ((d - 1 : ℕ) : ℝ) ^ 12

/-- Convergent lattice constant `σ₀ = ∑_{d ≥ 1} κ(d)`. -/
noncomputable def sigma0 : ℝ :=
  ∑' d : ℕ, kappa d

/-- Certified global minimum energy of the 5-atom Lennard-Jones cluster (`V₅*`). -/
noncomputable def V5star : ℝ := -9103852 / 1000000

/-- Certified global minimum energy of the 6-atom Lennard-Jones cluster (`V₆*`). -/
noncomputable def V6star : ℝ := -12712062 / 1000000

/-- Kuznetsov–Sahinidis intra-layer energy lower bound `f_KS(n) = -n(n - 1)/2`. -/
noncomputable def fKS (n : ℕ) : ℝ :=
  -((n * (n - 1) : ℕ) : ℝ) / 2

/-- Certified refined intra-layer energy lower bound `f_ref(n)` from arXiv:2607.09555 (eq. (7)). -/
noncomputable def fRef (n : ℕ) : ℝ :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => -1
  | 3 => -3
  | 4 => -6
  | 5 => V5star
  | 6 => V6star
  | m => ((m * (m - 1) : ℕ) : ℝ) / 30 * V6star

/-- Exact asymptotic penalty parameter `α = 1/2 + V₆* / 30`. -/
noncomputable def alphaConst : ℝ :=
  1 / 2 + V6star / 30

/-- Exact asymptotic layer-gain constant `θ = (1 - 2α/3)^{-1/2} - 1`. -/
noncomputable def thetaConst : ℝ :=
  (Real.sqrt (1 - 2 * alphaConst / 3))⁻¹ - 1

/-- A valid layer population profile of `N` atoms across `D` consecutive nonempty layers. -/
def IsValidProfile (N D : ℕ) (p : Fin D → ℕ) : Prop :=
  (∀ k : Fin D, 1 ≤ p k) ∧ (∑ k : Fin D, p k = N)

/-- Layer-bound energy functional `E_LB(p)` for a given intra-layer bound `f`. -/
noncomputable def layerEnergy (f : ℕ → ℝ) {D : ℕ} (p : Fin D → ℕ) : ℝ :=
  (∑ k : Fin D, f (p k)) -
  ∑ i : Fin D, ∑ j ∈ Finset.univ.filter (fun j : Fin D => i.val < j.val),
    kappa (j.val - i.val) * (p i : ℝ) * (p j : ℝ)

/-- Minimum layer-bound energy over all valid profiles of `N` atoms in `D` layers. -/
noncomputable def minLayerEnergy (f : ℕ → ℝ) (N D : ℕ) : ℝ :=
  sInf { E : ℝ | ∃ p : Fin D → ℕ, IsValidProfile N D p ∧ layerEnergy f p = E }

/-- Layer-span threshold `ρ(N)`: the largest `D ∈ {1, ..., N}` whose minimum
layer-bound energy does not exceed the putative upper bound `V_put(N) = -u(N) * N`. -/
noncomputable def rhoLayer (f : ℕ → ℝ) (u : ℕ → ℝ) (N : ℕ) : ℕ :=
  sSup { D : ℕ | 1 ≤ D ∧ D ≤ N ∧ minLayerEnergy f N D ≤ -(u N) * (N : ℝ) }

/-- Asymptotic form of the Kuznetsov–Sahinidis diameter bound and the certified refinement
gain (Theorem 2 and Corollary 2 of arXiv:2607.09555):
under `σ₀ < u_min ≤ u(N) ≤ u_max`, the KS surplus satisfies
`N - ρ_KS(N) = √(2 (u(N) - σ₀) N) + O(1)`, and the refinement gain satisfies
`ρ_KS(N) - ρ_ref(N) = θ √(2 (u(N) - σ₀) N) + O(1)`. -/
theorem main :
    ∀ (u : ℕ → ℝ) (u_min u_max : ℝ),
      sigma0 < u_min →
      (∀ N : ℕ, 1 ≤ N → u_min ≤ u N ∧ u N ≤ u_max) →
      (∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |((N : ℝ) - (rhoLayer fKS u N : ℝ)) -
          Real.sqrt (2 * (u N - sigma0) * (N : ℝ))| ≤ C) ∧
      (∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
        |((rhoLayer fKS u N : ℝ) - (rhoLayer fRef u N : ℝ)) -
          thetaConst * Real.sqrt (2 * (u N - sigma0) * (N : ℝ))| ≤ C) := by sorry

end OMA.S_arxiv_2607_09555
