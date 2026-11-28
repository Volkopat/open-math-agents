import OMAStatements.S_arxiv_1902_03207
import Mathlib
-- Credit: @my-other-github-account
-- Adapted from OpenAI openai/math@3344da59991ed94f9ba711217b29c1d760badfa6 (Apache-2.0).
open Set MeasureTheory ProbabilityTheory OMA.S_arxiv_1902_03207
open scoped Classical
namespace OMA.R_arxiv_1902_03207_R1

-- Finite-size obstruction to approximate transverse moves.
def H1 : Prop := ∀ V E : Type, ∀ ends : E → Sym2 V,
  let graph := fun ω : Set E => SimpleGraph.fromEdgeSet (ends '' ω)
  let full := graph Set.univ
  let pc := sInf {p : unitInterval | 0 < (setBernoulli (Set.univ : Set E) p)
    {ω | ∃ v : V, {w | (graph ω).Reachable v w}.Infinite}}
  let ball := fun y : V => Nat.rec (motive := fun _ => Set V) ({y} : Set V) (fun _ B => B ∪ ⋃ v ∈ B, full.neighborSet v)
  full.Connected → (∀ v : V, {i : E | v ∈ ends i}.Finite) →
  (∃ S : Set V, S.Finite ∧ ∀ v, ∃ u ∈ S, ∃ f : V ≃ V, ∃ g : E ≃ E,
    (∀ i, ends (g i) = Sym2.map f (ends i)) ∧ f u = v) →
  0 < (pc : ℝ) → (pc : ℝ) < 1 →
  (∀ e η : ℝ, 0 < e → e < 1/10 → 0 < η → η < 1/10 →
    ∃ m : ℕ, ∀ ρ : ℝ, 0 < ρ → ∃ t z : V → ℝ, ∃ p : unitInterval,
    (pc : ℝ)/2 ≤ p ∧ p < pc ∧
    (∀ ⦃u v⦄, full.Adj u v → |t u - t v| ≤ ρ) ∧
    (∀ ⦃u v⦄, full.Adj u v → |z u - z v| ≤ ρ) ∧
    ∀ y s, |s| = 1 → 1-η ≤ (setBernoulli (Set.univ : Set E) p).real
      {ω | ∃ a ∈ ball y m, ∃ b, ∃ w : (graph ω).Walk a b,
        (∀ x ∈ w.support, |t x - t y| ≤ 100 ∧ |z x - z y| ≤ 100) ∧
        |t b - (t y+1)| ≤ e/4 ∧ |z b - (z y+s)| ≤ e/4}) → False

-- Peierls upper bound on the critical threshold.
def H2 : Prop := ∀ d : ℕ, 2 ≤ d → OMA.S_arxiv_1902_03207.critical d < 1

-- Geometric extraction of a graph supporting transverse moves.
def H3 : Prop := ∀ d : ℕ, 2 ≤ d → critical d < 1 → 0 < theta d (critical d) →
  ∃ (V E : Type) (ends : E → Sym2 V),
  let graph := fun ω : Set E => SimpleGraph.fromEdgeSet (ends '' ω)
  let full := graph Set.univ
  let pc := sInf {p : unitInterval | 0 < (setBernoulli (Set.univ : Set E) p)
    {ω | ∃ v : V, {w | (graph ω).Reachable v w}.Infinite}}
  let ball := fun y : V => Nat.rec (motive := fun _ => Set V) ({y} : Set V) (fun _ B => B ∪ ⋃ v ∈ B, full.neighborSet v)
  full.Connected ∧ (∀ v : V, {i : E | v ∈ ends i}.Finite) ∧
  (∃ S : Set V, S.Finite ∧ ∀ v, ∃ u ∈ S, ∃ f : V ≃ V, ∃ g : E ≃ E,
    (∀ i, ends (g i) = Sym2.map f (ends i)) ∧ f u = v) ∧
  0 < (pc : ℝ) ∧ (pc : ℝ) < 1 ∧
  (∀ e η : ℝ, 0 < e → e < 1/10 → 0 < η → η < 1/10 →
    ∃ m : ℕ, ∀ ρ : ℝ, 0 < ρ → ∃ t z : V → ℝ, ∃ p : unitInterval,
    (pc : ℝ)/2 ≤ p ∧ p < pc ∧
    (∀ ⦃u v⦄, full.Adj u v → |t u - t v| ≤ ρ) ∧
    (∀ ⦃u v⦄, full.Adj u v → |z u - z v| ≤ ρ) ∧
    ∀ y s, |s| = 1 → 1-η ≤ (setBernoulli (Set.univ : Set E) p).real
      {ω | ∃ a ∈ ball y m, ∃ b, ∃ w : (graph ω).Walk a b,
        (∀ x ∈ w.support, |t x - t y| ≤ 100 ∧ |z x - z y| ≤ 100) ∧
        |t b - (t y+1)| ≤ e/4 ∧ |z b - (z y+s)| ≤ e/4})

theorem main : H1 → H2 → H3 → type_of% @OMA.S_arxiv_1902_03207.main := by
  intro h1 h2 h3 d hd
  by_contra hn
  obtain ⟨V,E,f,hc,hl,hq,hp,hp1,hm⟩ := h3 d hd (h2 d hd) (pos_iff_ne_zero.mpr hn)
  exact h1 V E f hc hl hq hp hp1 hm
end OMA.R_arxiv_1902_03207_R1
