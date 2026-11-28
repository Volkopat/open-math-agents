import Mathlib

/-!
# Minimax quadratic forms for bands of consecutive diagonals

Source: Kurisuto Asutora, https://mathoverflow.net/questions/254125 (CC BY-SA 4.0).
Contribution by @connoranderson.

For the original interval of N indices, the coefficient q is a feasible normalized
maximum exactly when each of the first M quadratic forms is at most q N m.
Summing over the bands counts the squared sums in sliding windows. A nonuniform
vector with spikes spaced M coordinates apart supplies the matching limit.
-/

namespace OMA.S_mo_254125
open Finset
/-- Exactly the index pairs at ordinary distance less than the band width. -/
def near (m i j : ℕ) : Prop := max i j < min i j + m
instance (m i j : ℕ) : Decidable (near m i j) := by unfold near; infer_instance

def band (N m : ℕ) (x : ℕ → ℝ) : ℝ := ∑ i ∈ range N, ∑ j ∈ range N,
  if near m i j then x i*x j else 0

def meets (N M : ℕ) (q : ℝ) (x : ℕ → ℝ) : Prop :=
  (∀ i < N, 0 ≤ x i) ∧ (∑ i ∈ range N, x i)=N ∧
    ∀ m : ℕ, 1 ≤ m → m ≤ M → band N m x ≤ q*N*m

def feasible (N M : ℕ) (q : ℝ) : Prop := ∃ x, meets N M q x

noncomputable def optimum (N M : ℕ) : ℝ := sInf {q | feasible N M q}


def spikes (N M : ℕ) : Finset ℕ := (range ((N-1)/M+1)).image (fun j => j*M)
noncomputable def profile (N M : ℕ) (i : ℕ) : ℝ :=
  let K : ℝ := (spikes N M).card
  let r := Real.sqrt (K/(N+K))
  1-r + (N/K*r)*(if i∈spikes N M then 1 else 0)

theorem main :
    (∀ N M : ℕ, 0 < N → 0 < M →
      (2*(M:ℝ)/(M+1))*((N:ℝ)/(N+((M:ℝ)-1))) ≤ optimum N M ∧
      optimum N M ≤ 2*(M:ℝ)/(M+1) ∧
      meets N M (2*(M:ℝ)/(M+1)) (profile N M)) ∧
    (∀ M : ℕ, 0 < M → Filter.Tendsto (fun N : ℕ => optimum N M)
      Filter.atTop (nhds (2*(M:ℝ)/(M+1)))) ∧
    (Filter.Tendsto (fun M : ℕ => 2*(M:ℝ)/(M+1)) Filter.atTop (nhds 2)) ∧
    (∀ B : ℕ → ℕ, Filter.Tendsto B Filter.atTop Filter.atTop →
      Filter.Tendsto (fun N : ℕ => optimum N (B N)) Filter.atTop (nhds 2)) ∧
    (∀ (M : ℕ), 0 < M → ∀ (q : ℕ → ℝ) (x : ℕ → ℕ → ℝ),
      (∀ N, 0 < N → meets N M (q N) (x N)) →
      Filter.Tendsto q Filter.atTop (nhds (2*(M:ℝ)/(M+1))) →
      Filter.Tendsto (fun N : ℕ => (∑ i ∈ range N, (x N i)^2)/(N:ℝ))
        Filter.atTop (nhds (2*(M:ℝ)/(M+1)))) ∧
    (∀ k M : ℕ, 0 < k → 2 ≤ M →
      profile (k*M) M 0 - profile (k*M) M 1 = (M:ℝ)/Real.sqrt (M+1)) := by
  sorry

end OMA.S_mo_254125
