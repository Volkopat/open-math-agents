import Mathlib

namespace OMA.S_oeis_a227056

def lexRow3 (a0 a1 a2 b0 b1 b2 : Fin 2) : Prop :=
  a0 < b0 ∨ (a0 = b0 ∧ (a1 < b1 ∨ (a1 = b1 ∧ a2 ≤ b2)))

def lexCol (m : ℕ) (f g : Fin m → Fin 2) : Prop :=
  f = g ∨ ∃ r : Fin m, (∀ j : Fin m, j.1 < r.1 → f j = g j) ∧ f r < g r

def isLexValid (m : ℕ) (M : Fin m → Fin 3 → Fin 2) : Prop :=
  (∀ r : Fin (m - 1), lexRow3 (M ⟨r.1, by omega⟩ 0) (M ⟨r.1, by omega⟩ 1) (M ⟨r.1, by omega⟩ 2)
                              (M ⟨r.1 + 1, by omega⟩ 0) (M ⟨r.1 + 1, by omega⟩ 1) (M ⟨r.1 + 1, by omega⟩ 2)) ∧
  lexCol m (fun r => M r 0) (fun r => M r 1) ∧
  lexCol m (fun r => M r 1) (fun r => M r 2)

def subVal (a b c d : Fin 2) : ℤ :=
  ((a.1 : ℤ) + (d.1 : ℤ)) - ((b.1 : ℤ) + (c.1 : ℤ))

def isValid (n : ℕ) (A : Fin n → Fin 2 → ℤ) : Prop :=
  ∃ M : Fin (n + 1) → Fin 3 → Fin 2,
    isLexValid (n + 1) M ∧
    ∀ r : Fin n, ∀ c : Fin 2,
      A r c = subVal (M ⟨r.1, by omega⟩ ⟨c.1, by omega⟩) (M ⟨r.1, by omega⟩ ⟨c.1 + 1, by omega⟩)
                     (M ⟨r.1 + 1, by omega⟩ ⟨c.1, by omega⟩) (M ⟨r.1 + 1, by omega⟩ ⟨c.1 + 1, by omega⟩)

noncomputable def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Nat.card {A : Fin n → Fin 2 → ℤ // isValid n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 8 =
      PowerSeries.X * (10 - 40 * PowerSeries.X + 84 * PowerSeries.X ^ 2 - 103 * PowerSeries.X ^ 3 + 77 * PowerSeries.X ^ 4 - 35 * PowerSeries.X ^ 5 + 9 * PowerSeries.X ^ 6 - PowerSeries.X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 8 * (a (n - 1) : ℤ) - 28 * (a (n - 2) : ℤ) + 56 * (a (n - 3) : ℤ) - 70 * (a (n - 4) : ℤ) + 56 * (a (n - 5) : ℤ) - 28 * (a (n - 6) : ℤ) + 8 * (a (n - 7) : ℤ) - (a (n - 8) : ℤ) := by
  sorry

end OMA.S_oeis_a227056
