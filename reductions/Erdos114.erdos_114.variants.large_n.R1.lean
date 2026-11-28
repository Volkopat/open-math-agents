import FormalConjectures.ErdosProblems.«114»

-- Reduction Erdos114.erdos_114.variants.large_n.R1 of Erdős Problem 114 — large n
-- Credit: @luciusacarr
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_Erdos114_erdos_114_variants_large_n_R1

open Polynomial Filter Erdos114

-- Normalization and maximizer existence (Tao, Proposition 1.2).
def H1 : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∃ q : ℂ[X],
    q.Monic ∧ q.natDegree = n ∧ q.coeff (n - 1) = 0 ∧
    (q.eval 0).im = 0 ∧ (q.eval 0).re ≤ 0 ∧
    IsConnected (lemniscate q) ∧
    (∀ z : ℂ, q.derivative.eval z = 0 → z ∈ lemniscate q) ∧
    (∀ p : ℂ[X], p.Monic → p.natDegree = n →
      lemniscateLength p ≤ lemniscateLength q)

-- Rigidity of normalized maximizers in high degree.
def H2 : Prop :=
  ∀ᶠ n : ℕ in atTop, ∀ q : ℂ[X],
    q.Monic → q.natDegree = n → q.coeff (n - 1) = 0 →
    (q.eval 0).im = 0 → (q.eval 0).re ≤ 0 →
    IsConnected (lemniscate q) →
    (∀ z : ℂ, q.derivative.eval z = 0 → z ∈ lemniscate q) →
    (∀ p : ℂ[X], p.Monic → p.natDegree = n →
      lemniscateLength p ≤ lemniscateLength q) →
    q = X ^ n - 1

theorem main : H1 → H2 → type_of% @Erdos114.erdos_114.variants.large_n := by
  intro hExist hRigid
  change ∀ᶠ n : ℕ in atTop, ∀ p : ℂ[X], p.Monic → p.natDegree = n →
    lemniscateLength p ≤ lemniscateLength (X ^ n - 1)
  have hPositive : ∀ᶠ n : ℕ in atTop, 1 ≤ n := eventually_ge_atTop 1
  filter_upwards [hRigid, hPositive] with n hRigidAt hn
  intro p hp hdeg
  obtain ⟨q, hq, hqn, hcoeff, him, hre, hconn, hcrit, hmax⟩ := hExist n hn
  have heq := hRigidAt q hq hqn hcoeff him hre hconn hcrit hmax
  simpa only [heq] using hmax p hp hdeg

end OMA.R_Erdos114_erdos_114_variants_large_n_R1
