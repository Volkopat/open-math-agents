import Mathlib

/-!
# Erdős Problem 1040

Source: https://www.erdosproblems.com/1040
Credit: @mgv27

Let $F\subseteq \mathbb{C}$ be a closed infinite set, and let $\mu(F)$ be the infimum of
\[\lvert \{ z: \lvert f(z)\rvert < 1\}\rvert,\]
as $f$ ranges over all polynomials of the shape $\prod (z-z_i)$ with $z_i\in F$.
Is $\mu(F)$ determined by the transfinite diameter of $F$? In particular, is $\mu(F)=0$
whenever the transfinite diameter of $F$ is $\geq 1$?

Formalization notes:
* `main` states the second ("in particular") question. The first question has been answered
  negatively (Aletheia [Fe26], quoted on the source page: two sets of transfinite diameter `0`
  with `μ(F₁) ≥ π/4` and `μ(F₂)` arbitrarily small), so it is not stated here.
* `|·|` of a set is planar Lebesgue measure, `MeasureTheory.volume` on `ℂ`.
* The polynomials `∏ (z - z_i)` are indexed by nonempty finite multisets of points of `F`
  (repetition allowed, degree `≥ 1`). The empty product `f = 1` is excluded: it would give the
  empty set and make `μ(F) = 0` trivially.
* `μ(F) = 0` is spelled out as: for every `ε > 0` some such `f` has `|{|f| < 1}| < ε`.
* The transfinite diameter is `ρ(F) = lim_n d_n` with
  `d_n = sup_{z_1,…,z_n ∈ F} (∏_{i<j} |z_i - z_j|)^{1/binom(n,2)}` (definition quoted on the
  page). The sequence `d_n` is non-increasing (Fekete), so `ρ(F) ≥ 1` iff `d_n ≥ 1` for all
  `n ≥ 2`; we use this form, which also covers unbounded `F` (where `d_n = ∞`). `d_n ≥ 1` is
  written as: for every `0 ≤ c < 1` there are `z_1, …, z_n ∈ F` with
  `∏_{i<j} |z_i - z_j| ≥ c ^ binom(n,2)`, avoiding real-valued suprema.
* Known (source page): yes if `F` is a line segment or a disc; if `ρ(F) < 1` the set
  `{|f| < 1}` always contains a disc of radius `≫_F 1`.
-/

namespace OMA.S_erdos_1040

open MeasureTheory

/-- The `n`-th diameter of `F` is at least `1`: for every `0 ≤ c < 1` there are points
`z_1, …, z_n ∈ F` with `∏_{i<j} |z_i - z_j| ≥ c ^ binom(n,2)`. -/
def DiamAtLeastOne (F : Set ℂ) (n : ℕ) : Prop :=
  ∀ c : ℝ, 0 ≤ c → c < 1 → ∃ z : Fin n → ℂ, (∀ i, z i ∈ F) ∧
    c ^ n.choose 2 ≤ ∏ i : Fin n, ∏ j : Fin n, if i < j then ‖z i - z j‖ else 1

/-- The transfinite diameter of `F` is at least `1` (equivalently, every `d_n ≥ 1`). -/
def TransfiniteDiamGeOne (F : Set ℂ) : Prop :=
  ∀ n : ℕ, 2 ≤ n → DiamAtLeastOne F n

/-- `μ(F) = 0`: for every `ε > 0` there is a nonempty multiset `s` of points of `F` such that
the set `{z : |∏_{w ∈ s} (z - w)| < 1}` has Lebesgue measure less than `ε`. -/
def MuZero (F : Set ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ s : Multiset ℂ, s ≠ 0 ∧ (∀ w ∈ s, w ∈ F) ∧
    volume {z : ℂ | ‖(s.map (fun w => z - w)).prod‖ < 1} < ENNReal.ofReal ε

/-- Erdős Problem 1040: if `F ⊆ ℂ` is closed and infinite with transfinite diameter `≥ 1`,
is `μ(F) = 0`? -/
theorem main : ∀ F : Set ℂ, IsClosed F → F.Infinite → TransfiniteDiamGeOne F → MuZero F := by
  sorry

end OMA.S_erdos_1040
