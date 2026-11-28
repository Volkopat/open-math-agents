import Mathlib

/-!
# Counting extensions of prescribed edge colours

Source: https://mathoverflow.net/questions/472523
Credit: @Mapika

Yuhang Bai asks whether the number of proper edge colourings divided by the
number extending an extendible prescription on s edges is at least (c k)^s.
He asks about an absolute c, also allowing an asymptotic assertion, and suggests
the hypothesis k ≥ 6m/7. Both versions are addressed below. A finite simple
graph on n vertices is represented by a finite set E of two-element vertex
sets. Colours are labelled; T chooses the edges on which colours are prescribed.
-/

namespace OMA.S_mo_472523

def Proper {n k : ℕ} {E : Finset (Finset (Fin n))} (f : E → Fin k) : Prop :=
  ∀ e e' : E, e ≠ e' → ¬ Disjoint e.val e'.val → f e ≠ f e'

noncomputable def total {n : ℕ} (E : Finset (Finset (Fin n))) (k : ℕ) : ℕ :=
  Nat.card {f : E → Fin k // Proper f}

noncomputable def extensions {n k : ℕ} {E : Finset (Finset (Fin n))}
    (T : Finset E) (p : T → Fin k) : ℕ :=
  Nat.card {f : E → Fin k // Proper f ∧ ∀ e : T, f e.val = p e}

/-- The hypothesis H selects the pairs (edge count, palette size) under
consideration. Multiplication clears the positive denominator. -/
def ExtensionBound (c : ℝ) (H : ℕ → ℕ → Prop) : Prop :=
  ∀ (n k : ℕ) (E : Finset (Finset (Fin n))), (∀ e ∈ E, e.card = 2) →
    H E.card k → ∀ (T : Finset E) (p : T → Fin k), 0 < extensions T p →
      (c * (k : ℝ)) ^ T.card * (extensions T p : ℝ) ≤ (total E k : ℝ)

theorem main :
    (∃ c : ℝ, 0 < c ∧ ExtensionBound c (fun m k => 6 * m ≤ 7 * k)) ∧
    ¬ (∃ (c : ℝ) (m₀ : ℕ), 0 < c ∧ ExtensionBound c (fun m _ => m₀ ≤ m)) := by
  sorry

end OMA.S_mo_472523
