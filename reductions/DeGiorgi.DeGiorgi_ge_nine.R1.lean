import FormalConjectures.Paper.DeGiorgi

/-!
Reduction `DeGiorgi.DeGiorgi_ge_nine.R1` of the counterexample to De Giorgi's conjecture
in dimensions `n >= 9` (del Pino-Kowalczyk-Wei, Annals of Mathematics 2011).
Credit: @B221393 (incorporating the successor-dimension lift roadmap noted by @rpinho in #53718).

- `H1`: Base counterexample in dimension 9 (del Pino-Kowalczyk-Wei 2011).
- `H2`: Cylindrical dimension-lifting step from dimension `m >= 9` to `m + 1` (extending a
  counterexample `u : R^m -> R` independently of the last coordinate via projection).
- `main`: Proves `DeGiorgi.DeGiorgi_ge_nine` for all `n >= 9` by induction on `n` via
  `Nat.le_induction`, handling arbitrary `[NeZero n]` instances by subsingleton elimination.
-/

namespace OMA.R_DeGiorgi_DeGiorgi_ge_nine_R1

/-- Base case (del Pino-Kowalczyk-Wei 2011): De Giorgi's conclusion fails in dimension 9. -/
def H1 : Prop :=
  ¬ DeGiorgi.DeGiorgi_conclusion 9

/-- Cylindrical dimension-lifting step: a counterexample to De Giorgi's conjecture in
dimension `m >= 9` lifts to a counterexample in dimension `m + 1`. -/
def H2 : Prop :=
  ∀ (m : ℕ) [NeZero m], 9 ≤ m →
    ¬ DeGiorgi.DeGiorgi_conclusion m → ¬ DeGiorgi.DeGiorgi_conclusion (m + 1)

theorem main : H1 → H2 → type_of% @DeGiorgi.DeGiorgi_ge_nine := by
  intro h1 h2 n inst hn
  have haux : ∀ d : ℕ, ∀ [NeZero (9 + d)], ¬ DeGiorgi.DeGiorgi_conclusion (9 + d) := by
    intro d
    induction d with
    | zero =>
      intro inst0
      have heq : inst0 = (inferInstance : NeZero 9) := Subsingleton.elim _ _
      rw [heq]
      exact h1
    | succ k ih =>
      intro instk
      haveI : NeZero (9 + k) := ⟨by omega⟩
      have heq : instk = (inferInstance : NeZero (9 + k + 1)) := Subsingleton.elim _ _
      rw [heq]
      exact h2 (9 + k) (by omega) ih
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact haux d

end OMA.R_DeGiorgi_DeGiorgi_ge_nine_R1
