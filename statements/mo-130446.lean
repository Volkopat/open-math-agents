import Mathlib

/-!
# Exact laws for close pairs and isolated particles in a bounded window

Source: https://mathoverflow.net/questions/130446 (LHoward, CC BY-SA 3.0).
Credit: @connoranderson

A uniform configuration of n independently placed particles is uniform volume on the
Cartesian power of the sampling window. The window can be a solid ball, rectangular
box or solid circular cylinder. The bounding cube truncates the numerical grid; take
its integer half-width larger than every window dimension to sample the whole window.

The two distributions are distinct. Binomial inversion gives each probability as a
signed finite sum of intersection probabilities. The lattice formulas below compute
all of them by deterministic finite counts converging to the exact probabilities,
including distance ties for either choice of weak inequality. No independence between
edges, sphere-packing test, or unknown intersection integral enters the formula.
-/
namespace OMA.S_mo_130446
open MeasureTheory Finset Filter
open scoped Topology ENNReal
noncomputable section
abbrev P := Fin 3 → ℝ

noncomputable def eu (x : P) : ℝ := ‖(WithLp.toLp 2 x : EuclideanSpace ℝ (Fin 3))‖

def xy (x : P) : P := fun i => if i.val < 2 then x i else 0

inductive Window
  | ball (r : ℝ)
  | box (a : P)
  | cylinder (r h : ℝ)

noncomputable def score : Window → P → ℝ
  | .ball r, x => eu x - r
  | .box a, x => max (|x 0|-a 0) (max (|x 1|-a 1) (|x 2|-a 2))
  | .cylinder r h, x => max (eu (xy x)-r) (|x 2|-h)
abbrev X (n : ℕ) := (Fin n × Fin 3) → ℝ
abbrev Edge (n : ℕ) := {e : Fin n × Fin n // e.1 < e.2}
def point {n : ℕ} (x : X n) (i : Fin n) : P := fun j => x (i,j)
def cube (n K : ℕ) : Set (X n) := Set.univ.pi fun _ => Set.Ico (-(K:ℝ)) K
def domain (n K : ℕ) (w : Window) : Set (X n) :=
  {x | x∈cube n K ∧ ∀ i, score w (point x i)≤0}
def edgeScore {n : ℕ} (near : Bool) (d : ℝ) (e : Edge n) (x : X n) : ℝ :=
  let a := eu (point x e.val.1-point x e.val.2)
  if near then a-d else d-a
def incident {n : ℕ} (i : Fin n) : Finset (Edge n) :=
  univ.filter fun e => e.val.1=i ∨ e.val.2=i
def events {n : ℕ} {ι : Type*} (near : Bool) (d : ℝ) (p : ι → Finset (Edge n))
    (i : ι) : Set (X n) := {x | ∀ e∈p i, edgeScore near d e x≤0}
def countAt {ι Ω : Type*} [Fintype ι] (A : ι → Set Ω) (x : Ω) : ℕ := by
  classical exact (univ.filter fun i => x∈A i).card
def law {n : ℕ} {ι : Type*} [Fintype ι] (K : ℕ) (w : Window) (A : ι → Set (X n))
    (k : ℕ) : ℝ :=
  (volume.restrict (domain n K w)).real {x | countAt A x=k} / volume.real (domain n K w)
def mesh (m : ℕ) : ℝ := ((m:ℝ)+1)⁻¹
abbrev Grid (n K m : ℕ) := (Fin n × Fin 3) → Fin (2*K*(m+1))
def low {K m : ℕ} (j : Fin (2*K*(m+1))) : ℝ := j.val * mesh m-K
def corner {n K m : ℕ} (g : Grid n K m) : X n := fun i => low (g i)
def admissible {n : ℕ} {ι : Type*} (w : Window) (near : Bool) (d : ℝ)
    (p : ι → Finset (Edge n)) (s : Finset ι) (err : ℝ) (x : X n) : Prop :=
  (∀ i, score w (point x i) ≤ err) ∧ ∀ a ∈ s, ∀ e ∈ p a, edgeScore near d e x ≤ err
def moment {n : ℕ} {ι : Type*} (K : ℕ) (w : Window) (near : Bool) (d : ℝ)
    (p : ι → Finset (Edge n)) (s : Finset ι) (m : ℕ) : ℝ := by
  classical exact ((univ.filter fun g : Grid n K m =>
    admissible w near d p s (6*mesh m) (corner g)).card:ℝ) * mesh m^(3*n)
def mass (n K : ℕ) (w : Window) (m : ℕ) : ℝ :=
  moment (n:=n) K w true 0 (fun e : Edge n => {e}) ∅ m
def formula {n : ℕ} {ι : Type*} [Fintype ι] (K : ℕ) (w : Window) (near : Bool) (d : ℝ)
    (p : ι → Finset (Edge n)) (k m : ℕ) : ℝ :=
  (∑ s ∈ (univ : Finset ι).powerset,
    ((-1:ℝ)^(s.card-k)*(s.card.choose k:ℝ))*moment K w near d p s m) / mass n K w m
theorem main : ∀ (n K : ℕ) (w : Window) (d : ℝ) (k : ℕ),
    0 < volume.real (domain n K w) →
    Tendsto (formula K w true d (fun e : Edge n => {e}) k) atTop
      (𝓝 (law K w (events true d (fun e : Edge n => {e})) k)) ∧
    Tendsto (formula K w false d (incident (n:=n)) k) atTop
      (𝓝 (law K w (events false d (incident (n:=n))) k)) := by
  sorry
end
end OMA.S_mo_130446
