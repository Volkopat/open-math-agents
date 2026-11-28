import Mathlib

/-!
# OEIS A022493: Fishburn numbers (continued fraction generating function)

Source: https://oeis.org/A022493
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

The Fishburn number `a(n)` is the number of nonisomorphic interval orders
on `n` unlabeled points.

Conjecture: The ordinary generating function of `a(n)` is `Q(0)`, where
`Q(k) = 1 + (1 - (1-x)^(2k+1)) / (1 - (1 - (1-x)^(2k+2)) / (1 - (1-x)^(2k+2) + 1/Q(k+1)))`
as a formal continued fraction in `ℚ[[x]]`.
-/

namespace OMA.S_oeis_a022493

def IsIntervalOrder {n : ℕ} (r : Fin n → Fin n → Prop) : Prop :=
  (∀ x, ¬ r x x) ∧
  (∀ x y z, r x y → r y z → r x z) ∧
  (∀ a b c d, r a b → r c d → r a d ∨ r c b)

def intervalOrderSetoid (n : ℕ) : Setoid { r : Fin n → Fin n → Prop // IsIntervalOrder r } where
  r r₁ r₂ := ∃ e : Equiv.Perm (Fin n), ∀ x y, r₁.val x y ↔ r₂.val (e x) (e y)
  iseqv :=
    ⟨fun _ => ⟨Equiv.refl _, fun _ _ => Iff.rfl⟩,
     fun ⟨e, h⟩ => ⟨e.symm, fun x y => by simpa using (h (e.symm x) (e.symm y)).symm⟩,
     fun ⟨e₁, h₁⟩ ⟨e₂, h₂⟩ => ⟨e₁.trans e₂, fun x y => (h₁ x y).trans (h₂ (e₁ x) (e₁ y))⟩⟩

noncomputable def fishburn (n : ℕ) : ℕ :=
  Nat.card (Quotient (intervalOrderSetoid n))

noncomputable def cfQ (k : ℕ) : ℕ → PowerSeries ℚ
  | 0 => 1
  | m + 1 =>
    let u := (1 : PowerSeries ℚ) - PowerSeries.X
    let a := 1 - u ^ (2 * k + 1)
    let b := 1 - u ^ (2 * k + 2)
    1 + a * Ring.inverse (1 - b * Ring.inverse (b + Ring.inverse (cfQ (k + 1) m)))

theorem main :
    ∀ n : ℕ, ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
      PowerSeries.coeff n (cfQ 0 m) = (fishburn n : ℚ) := by
  sorry

end OMA.S_oeis_a022493
