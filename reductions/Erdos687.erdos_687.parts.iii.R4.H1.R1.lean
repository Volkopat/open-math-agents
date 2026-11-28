import OMAReductions.R_Erdos687_erdos_687_parts_iii_R4
import Mathlib

-- Reduction Erdos687.erdos_687.parts.iii.R3.H1.R2 of step Erdos687.erdos_687.parts.iii.R3.H1
-- Credit: @LordMike
-- Port of reductions/Erdos687.erdos_687.parts.iii.R3.H1.R2.lean by its author onto the identical hypothesis statement Erdos687.erdos_687.parts.iii.R4.H1.

/-!
# Short prime gaps `(p - n)^3 ≤ n^2` via the second-difference explicit formula for `ψ₁`

Splits `Erdos687.erdos_687.parts.iii.R3.H1` (`∀ᶠ n, ∃ p prime, n < p ∧ (p - n)^3 ≤ n^2`)
at scale `h n = ⌊n^(33/50)⌋₊ / 2` into three decoupled components:

* `H1`: Unconditional explicit formula for `ψ₁(n) = ∑_{k < n} Λ(k) (n - k)` up to a bounded
  error `≤ 2` after subtracting `n^2 / 2`, the regularized zero sum `F(n)` over nontrivial zeros
  of `ξ(s) = s (s - 1) completedRiemannZeta₀ s + 1`, and an affine term `b n + c`.
* `H2`: One-sided second-difference lower bound `-(h n)^2 / 2 ≤ Δ²_{h n} F(n + 1)` eventually.
* `H3`: Prime extraction: `(h n)^2 / 4 < Δ²_{h n} ψ₁(n + 1)` implies a prime `p ∈ (n, n + 2 h n]`
  satisfying `(p - n)^3 ≤ n^2`.

Taking the second difference cancels `b n + c`, yields `h^2` from `n^2 / 2`, and absorbs the
bounded error `≤ 8` into `h^2 / 4` once `h ≥ 6`.
-/

open Filter
noncomputable section
namespace OMA.R_Erdos687_erdos_687_parts_iii_R4_H1_R1

def H1 : Prop := ∃ b c : ℝ, ∀ n : ℕ, 1 ≤ n →
  |(fun n : ℕ => ∑ k ∈ Finset.range n,
  (ArithmeticFunction.vonMangoldt k : ℝ) * ((n : ℝ) - k)) n - (n : ℝ)^2/2 - (fun n : ℕ => Complex.re (∑' z : {s : ℂ // (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) s = 0},
  (analyticOrderNatAt (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) (z : ℂ) : ℂ) * ((n : ℂ) *
    ((1 - 1 / (n : ℂ)) / (2 - (z : ℂ)) -
     ((n : ℂ) ^ (z : ℂ) / ((z : ℂ) * ((z : ℂ) + 1)) -
      1 / (z : ℂ) + (n : ℂ) ^ (-1 : ℂ) / (1 + (z : ℂ))))))) n - (b*n + c)| ≤ 2
def H2 : Prop := ∀ᶠ n : ℕ in atTop,
  -((fun n : ℕ => ⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ / 2) n : ℝ)^2/2 ≤ (fun (f : ℕ → ℝ) (a h : ℕ) =>
  f (a + 2*h) - 2 * f (a+h) + f a) (fun n : ℕ => Complex.re (∑' z : {s : ℂ // (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) s = 0},
  (analyticOrderNatAt (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) (z : ℂ) : ℂ) * ((n : ℂ) *
    ((1 - 1 / (n : ℂ)) / (2 - (z : ℂ)) -
     ((n : ℂ) ^ (z : ℂ) / ((z : ℂ) * ((z : ℂ) + 1)) -
      1 / (z : ℂ) + (n : ℂ) ^ (-1 : ℂ) / (1 + (z : ℂ))))))) (n+1) ((fun n : ℕ => ⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ / 2) n)
def H3 : Prop := ∀ᶠ n : ℕ in atTop,
  ((fun n : ℕ => ⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ / 2) n : ℝ)^2/4 < (fun (f : ℕ → ℝ) (a h : ℕ) =>
  f (a + 2*h) - 2 * f (a+h) + f a) (fun n : ℕ => ∑ k ∈ Finset.range n,
  (ArithmeticFunction.vonMangoldt k : ℝ) * ((n : ℝ) - k)) (n+1) ((fun n : ℕ => ⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ / 2) n) →
  ∃ p : ℕ, p.Prime ∧ n < p ∧ (p-n)^3 ≤ n^2

theorem main : H1 → H2 → H3 → OMA.R_Erdos687_erdos_687_parts_iii_R4.H1 := by
  rintro ⟨b,c,hF⟩ hZ hP
  have ht := ((tendsto_rpow_atTop (by norm_num : (0:ℝ) < 33/50)).comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop (12 : ℝ))
  filter_upwards [hZ, hP, ht] with n hn hp hg
  change 12 ≤ (n : ℝ) ^ (33/50 : ℝ) at hg
  have hf : 12 ≤ ⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ := (Nat.le_floor_iff (by positivity)).2 (by simpa using hg)
  let h := (fun n : ℕ => ⌊(n : ℝ) ^ (33/50 : ℝ)⌋₊ / 2) n
  have hh : 6 ≤ h := by dsimp [h]; omega
  have hr : (6:ℝ) ≤ h := by exact_mod_cast hh
  let a := n+1
  obtain ⟨L, _⟩ := abs_le.mp (hF (a+2*h) (by dsimp [a]; omega))
  obtain ⟨_, U⟩ := abs_le.mp (hF (a+h) (by dsimp [a]; omega))
  obtain ⟨L', _⟩ := abs_le.mp (hF a (by dsimp [a]; omega))
  apply hp
  change -(h:ℝ)^2/2 ≤ (fun n : ℕ => Complex.re (∑' z : {s : ℂ // (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) s = 0},
  (analyticOrderNatAt (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) (z : ℂ) : ℂ) * ((n : ℂ) *
    ((1 - 1 / (n : ℂ)) / (2 - (z : ℂ)) -
     ((n : ℂ) ^ (z : ℂ) / ((z : ℂ) * ((z : ℂ) + 1)) -
      1 / (z : ℂ) + (n : ℂ) ^ (-1 : ℂ) / (1 + (z : ℂ))))))) (a+2*h)-2*(fun n : ℕ => Complex.re (∑' z : {s : ℂ // (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) s = 0},
  (analyticOrderNatAt (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) (z : ℂ) : ℂ) * ((n : ℂ) *
    ((1 - 1 / (n : ℂ)) / (2 - (z : ℂ)) -
     ((n : ℂ) ^ (z : ℂ) / ((z : ℂ) * ((z : ℂ) + 1)) -
      1 / (z : ℂ) + (n : ℂ) ^ (-1 : ℂ) / (1 + (z : ℂ))))))) (a+h)+(fun n : ℕ => Complex.re (∑' z : {s : ℂ // (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) s = 0},
  (analyticOrderNatAt (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) (z : ℂ) : ℂ) * ((n : ℂ) *
    ((1 - 1 / (n : ℂ)) / (2 - (z : ℂ)) -
     ((n : ℂ) ^ (z : ℂ) / ((z : ℂ) * ((z : ℂ) + 1)) -
      1 / (z : ℂ) + (n : ℂ) ^ (-1 : ℂ) / (1 + (z : ℂ))))))) a at hn
  change (h:ℝ)^2/4 < (fun n : ℕ => ∑ k ∈ Finset.range n,
  (ArithmeticFunction.vonMangoldt k : ℝ) * ((n : ℝ) - k)) (a+2*h)-2*(fun n : ℕ => ∑ k ∈ Finset.range n,
  (ArithmeticFunction.vonMangoldt k : ℝ) * ((n : ℝ) - k)) (a+h)+(fun n : ℕ => ∑ k ∈ Finset.range n,
  (ArithmeticFunction.vonMangoldt k : ℝ) * ((n : ℝ) - k)) a
  -- Keep the spectral sums opaque during the real polynomial calculation.
  generalize (fun n : ℕ => Complex.re (∑' z : {s : ℂ // (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) s = 0},
  (analyticOrderNatAt (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) (z : ℂ) : ℂ) * ((n : ℂ) *
    ((1 - 1 / (n : ℂ)) / (2 - (z : ℂ)) -
     ((n : ℂ) ^ (z : ℂ) / ((z : ℂ) * ((z : ℂ) + 1)) -
      1 / (z : ℂ) + (n : ℂ) ^ (-1 : ℂ) / (1 + (z : ℂ))))))) (a+2*h) = f₂ at *; generalize (fun n : ℕ => Complex.re (∑' z : {s : ℂ // (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) s = 0},
  (analyticOrderNatAt (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) (z : ℂ) : ℂ) * ((n : ℂ) *
    ((1 - 1 / (n : ℂ)) / (2 - (z : ℂ)) -
     ((n : ℂ) ^ (z : ℂ) / ((z : ℂ) * ((z : ℂ) + 1)) -
      1 / (z : ℂ) + (n : ℂ) ^ (-1 : ℂ) / (1 + (z : ℂ))))))) (a+h) = f₁ at *; generalize (fun n : ℕ => Complex.re (∑' z : {s : ℂ // (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) s = 0},
  (analyticOrderNatAt (fun s : ℂ => s * (s - 1) * completedRiemannZeta₀ s + 1) (z : ℂ) : ℂ) * ((n : ℂ) *
    ((1 - 1 / (n : ℂ)) / (2 - (z : ℂ)) -
     ((n : ℂ) ^ (z : ℂ) / ((z : ℂ) * ((z : ℂ) + 1)) -
      1 / (z : ℂ) + (n : ℂ) ^ (-1 : ℂ) / (1 + (z : ℂ))))))) a = f₀ at *
  generalize (fun n : ℕ => ∑ k ∈ Finset.range n,
  (ArithmeticFunction.vonMangoldt k : ℝ) * ((n : ℝ) - k)) (a+2*h) = g₂ at *; generalize (fun n : ℕ => ∑ k ∈ Finset.range n,
  (ArithmeticFunction.vonMangoldt k : ℝ) * ((n : ℝ) - k)) (a+h) = g₁ at *; generalize (fun n : ℕ => ∑ k ∈ Finset.range n,
  (ArithmeticFunction.vonMangoldt k : ℝ) * ((n : ℝ) - k)) a = g₀ at *
  push_cast at L U L'
  nlinarith [sq_nonneg ((h:ℝ)-6)]
end OMA.R_Erdos687_erdos_687_parts_iii_R4_H1_R1
end
