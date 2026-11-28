import Mathlib

/-!
# Recovering a point configuration from its projected power sums

Source: user45183, https://mathoverflow.net/questions/218321 (CC BY-SA 3.0).
Credit: @connoranderson.

More than N(n−1) directions in linear general position suffice to recover
N points in real n-space with their multiplicities. Distinct parameters on
the moment curve furnish such directions. Consequently the data determine
every mixed moment. In dimension three, the directions (1,t,t²) satisfy
the nonzero homogeneous quadratic relation v₀v₂−v₁² = 0, so the source’s
quadratic spanning condition fails even with arbitrarily many directions.
-/

namespace OMA.S_mo_218321

abbrev Point (n : ℕ) := Fin n → ℝ

def project {n : ℕ} (v x : Point n) := ∑ i, v i*x i

def generalPosition {n M : ℕ} (v : Fin M → Point n) : Prop := by
  classical
  exact ∀ z : Point n, z ≠ 0 → (Finset.univ.filter (fun j => project (v j) z=0)).card ≤ n-1

theorem main : (∀ (n N M : ℕ) (v : Fin M → Point n), N*(n-1) < M → generalPosition v →
    ∀ x y : Fin N → Point n,
      (∀ j (k : ℕ), 1 ≤ k → k ≤ N →
        (∑ i, (project (v j) (x i))^k) = ∑ i, (project (v j) (y i))^k) →
      ((Finset.univ : Finset (Fin N)).val.map x = Finset.univ.val.map y) ∧
      ∀ α : Fin n → ℕ, (∑ i, ∏ t, (x i t)^(α t)) = ∑ i, ∏ t, (y i t)^(α t)) ∧
    (∀ (n M : ℕ) (t : Fin M → ℝ), Function.Injective t →
      generalPosition (fun j (k : Fin n) => (t j)^k.val)) := by
  sorry

end OMA.S_mo_218321
