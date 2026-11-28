import Mathlib

/-!
# The maximum coefficient for nonattacking kings on a torus

An independent set is a placement of indistinguishable kings. Two distinct
squares attack if their coordinates are each at distance at most one. On
the torus, zero and n-1 are also neighbors in each coordinate. The degree-k
coefficient of the independence polynomial counts placements of exactly k
kings. Its maximum is A394697 for n ≥ 3, the published offset.

OEIS A247413 is defined as lim A063443(n)^(1/n²), where A063443(n)
counts all placements on the ordinary (n-1)-by-(n-1) square. The assertion
below says both normalized sequences converge to the same real number.
It includes existence of the ordinary-board limit, so needs no assumption
about that limit. Values at the finitely many small boards do not affect it.
Source: https://oeis.org/A394697
Comparison sequences: https://oeis.org/A247413 and https://oeis.org/A063443
Formalization: @KoaOkano
-/

namespace OMA.S_oeis_a394697
open Filter Topology Finset

abbrev Square := ℕ × ℕ
abbrev Placement := Finset Square

def cells (n : ℕ) := (range n) ×ˢ (range n)

def near (wrap : Bool) (n i j : ℕ) : Prop :=
  (i ≤ j+1 ∧ j ≤ i+1) ∨ (wrap = true ∧ ((i=0 ∧ j+1=n) ∨ (j=0 ∧ i+1=n)))

def independent (wrap : Bool) (n : ℕ) (s : Placement) : Prop :=
  ∀ x ∈ s, ∀ y ∈ s, near wrap n x.1 y.1 → near wrap n x.2 y.2 → x=y

noncomputable def boards (wrap : Bool) (n : ℕ) : Finset Placement := by
  classical
  exact (cells n).powerset.filter (independent wrap n)

noncomputable def ordinary (n : ℕ) : ℕ := (boards false n).card

noncomputable def coefficient (n k : ℕ) : ℕ :=
  ((boards true n).filter (fun s => s.card=k)).card

noncomputable def peak (n : ℕ) : ℕ := (range (n^2+1)).sup (coefficient n)

theorem main : ∃ c : ℝ,
    Tendsto (fun n : ℕ => (ordinary (n-1):ℝ)^(1/(n:ℝ)^2)) atTop (𝓝 c) ∧
    Tendsto (fun n : ℕ => (peak n:ℝ)^(1/(n:ℝ)^2)) atTop (𝓝 c) := by
  sorry

end OMA.S_oeis_a394697
