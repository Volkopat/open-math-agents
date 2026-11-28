import FormalConjectures.Arxiv.«2501.03234».ArithmeticSumS
import Mathlib.Tactic

/-!
Independent reduction of the theta-sum eventual-growth conjecture4.4. It does
not prove4.4 or4.3's explicit cutoff. H1 andH2 separate continuous growth and a
FIXED-depth grid limit; H3 is the remaining OPEN uniform arithmetic overshoot
estimate for a growing range t^2<=p. The hypotheses contain explicit recursors because reductions permit
only H definitions. No hypothesis uses an upstream unproved theorem.

Context: Berndt, Bhat, Meyer, Xie, Zaharescu, An Arithmetic Sum Associated with
the Classical Theta Function, Results in Mathematics81:25(2026),
DOI10.1007/s00025-025-02584-2 (refereed); Alessandro Lageler, Continued fractions
and Hardy sums, DOI10.1007/s12188-024-00283-3 (refereed). Related ECF-recurrence
site work: @sebastianbachmaier PR#6138. All proof code independently authored.
-/
namespace OMA.R_Arxiv_2501_03234_conjecture_4_4_R1
noncomputable section
open Filter Topology MeasureTheory

/-- The real signed even-CF prefixes have unbounded integral means. This is a
substantial analytic step, proved independently by a logarithmic cone subsolution. -/
def H1 : Prop :=
  let E : ℕ → ℝ → ℝ := Nat.rec (fun _ => 0) (fun _ f x =>
    let r := x⁻¹-2*(⌊x⁻¹/2⌋₊ : ℕ)
    if x=0 then 0 else if r<1 then 1-f r else 1+f (2-r))
  ∀ B : ℝ, ∃ t : ℕ, B < ∫ x in (0 : ℝ)..1, E t x

/-- For each FIXED fuel, the normalized even-grid mean converges to half the
real integral. This provides no effective cutoff or growing-fuel uniformity. -/
def H2 : Prop :=
  let A : ℕ → ℕ → ℕ → ℤ := Nat.rec (fun _ _ => 0) (fun _ f a b =>
    if a=0 then 0 else 1-if b%(2*a)<a then f (b%(2*a)) a else -f (2*a-b%(2*a)) a)
  let E : ℕ → ℝ → ℝ := Nat.rec (fun _ => 0) (fun _ f x =>
    let r := x⁻¹-2*(⌊x⁻¹/2⌋₊ : ℕ)
    if x=0 then 0 else if r<1 then 1-f r else 1+f (2-r))
  ∀ t : ℕ, Tendsto
    (fun m : ℕ => ((∑ a ∈ (Finset.Ico 1 (2*m+1)).filter Even, A t a (2*m+1) : ℤ) : ℝ)/((2*m+1 : ℕ) : ℝ))
    atTop (𝓝 ((1/2)*(∫ x in (0 : ℝ)..1, E t x)))

/-- OPEN uniform linear bound on prefix overshoot above the final prime sum.
A linear bound on total negative depth variation would suffice, but is unproved.
Only depths t^2<=p are required. This remains OPEN pointwise arithmetic;
the root stays open and no uniform total-negative-mass bound is assumed. -/
def H3 : Prop :=
  let A : ℕ → ℕ → ℕ → ℤ := Nat.rec (fun _ _ => 0) (fun _ f a b =>
    if a=0 then 0 else 1-if b%(2*a)<a then f (b%(2*a)) a else -f (2*a-b%(2*a)) a)
  ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℕ, p.Prime → Odd p → ∀ t : ℕ, t*t ≤ p →
    ((∑ a ∈ (Finset.Ico 1 p).filter Even, A t a p : ℤ) : ℝ) ≤
      (Arxiv.«2501.03234».S p : ℝ)+C*(p : ℝ)

theorem main : H1 → H2 → H3 → type_of% @Arxiv.«2501.03234».conjecture_4_4 := by
  intro h1 h2 h3
  dsimp only [H1] at h1
  dsimp only [H2] at h2
  dsimp only [H3] at h3
  intro n
  rcases h3 with ⟨C,hC,hTail⟩
  rcases h1 (2*((n : ℝ)+C+2)) with ⟨t,ht⟩
  have hEv := (h2 t).eventually (lt_mem_nhds (show (n : ℝ)+C+1 < _ by linarith))
  rcases Filter.eventually_atTop.mp hEv with ⟨M,hM⟩
  apply Filter.eventually_atTop.mpr
  refine ⟨max (2*M+1) (t*t+6),?_⟩
  intro p hlarge hprim hodd
  have hpm : 2*M+1 ≤ p := le_trans (le_max_left _ _) hlarge
  have hpt : t*t+6 ≤ p := le_trans (le_max_right _ _) hlarge
  have hpmod := Nat.odd_iff.mp hodd
  have heq : 2*(p/2)+1=p := by omega
  have hpre := hM (p/2) (by omega)
  rw [heq] at hpre
  have htcut : t*t ≤ p := by omega
  have hupper := hTail p hprim hodd t htcut
  have hpR : (0 : ℝ) < p := by exact_mod_cast hprim.pos
  have hprod := (lt_div_iff₀ hpR).mp hpre
  have hlast : (n : ℝ)*(p : ℝ) < (Arxiv.«2501.03234».S p : ℝ) := by nlinarith
  exact_mod_cast hlast
end
end OMA.R_Arxiv_2501_03234_conjecture_4_4_R1
