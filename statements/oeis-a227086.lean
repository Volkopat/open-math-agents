import Mathlib

namespace OMA.S_oeis_a227086

def lexRow4 (a0 a1 a2 a3 b0 b1 b2 b3 : Fin 2) : Prop :=
  a0 < b0 ∨ (a0 = b0 ∧ (a1 < b1 ∨ (a1 = b1 ∧ (a2 < b2 ∨ (a2 = b2 ∧ a3 ≤ b3)))))

def lexCol (m : ℕ) (f g : Fin m → Fin 2) : Prop :=
  f = g ∨ ∃ r : Fin m, (∀ j : Fin m, j.1 < r.1 → f j = g j) ∧ f r < g r

def isLexValid (m : ℕ) (M : Fin m → Fin 4 → Fin 2) : Prop :=
  (∀ r : Fin (m - 1), lexRow4 (M ⟨r.1, by omega⟩ 0) (M ⟨r.1, by omega⟩ 1) (M ⟨r.1, by omega⟩ 2) (M ⟨r.1, by omega⟩ 3)
                              (M ⟨r.1 + 1, by omega⟩ 0) (M ⟨r.1 + 1, by omega⟩ 1) (M ⟨r.1 + 1, by omega⟩ 2) (M ⟨r.1 + 1, by omega⟩ 3)) ∧
  lexCol m (fun r => M r 0) (fun r => M r 1) ∧
  lexCol m (fun r => M r 1) (fun r => M r 2) ∧
  lexCol m (fun r => M r 2) (fun r => M r 3)

def subVal (a b c d : Fin 2) : Fin 2 :=
  if (2 * a.1 + b.1 < 2 * c.1 + d.1) ∧ (2 * a.1 + c.1 < 2 * b.1 + d.1) then 1 else 0

def isValid (n : ℕ) (A : Fin n → Fin 3 → Fin 2) : Prop :=
  ∃ M : Fin (n + 1) → Fin 4 → Fin 2,
    isLexValid (n + 1) M ∧
    ∀ r : Fin n, ∀ c : Fin 3,
      A r c = subVal (M ⟨r.1, by omega⟩ ⟨c.1, by omega⟩) (M ⟨r.1, by omega⟩ ⟨c.1 + 1, by omega⟩)
                     (M ⟨r.1 + 1, by omega⟩ ⟨c.1, by omega⟩) (M ⟨r.1 + 1, by omega⟩ ⟨c.1 + 1, by omega⟩)

instance (n : ℕ) (A : Fin n → Fin 3 → Fin 2) : Decidable (isValid n A) := by
  unfold isValid isLexValid lexRow4 lexCol subVal
  infer_instance

def a (n : ℕ) : ℕ :=
  if n = 0 then 0 else Fintype.card {A : Fin n → Fin 3 → Fin 2 // isValid n A}

theorem main :
    (PowerSeries.mk fun n => (a n : ℚ)) * (1 - PowerSeries.X) ^ 12 =
      PowerSeries.X * (7 - 55 * PowerSeries.X + 213 * PowerSeries.X ^ 2 - 512 * PowerSeries.X ^ 3 + 837 * PowerSeries.X ^ 4 - 964 * PowerSeries.X ^ 5 + 794 * PowerSeries.X ^ 6 - 468 * PowerSeries.X ^ 7 + 197 * PowerSeries.X ^ 8 - 58 * PowerSeries.X ^ 9 + 11 * PowerSeries.X ^ 10 - PowerSeries.X ^ 11) ∧
    ∀ n : ℕ, 12 < n → (a n : ℤ) = 12 * (a (n - 1) : ℤ) - 66 * (a (n - 2) : ℤ) + 220 * (a (n - 3) : ℤ) - 495 * (a (n - 4) : ℤ) + 792 * (a (n - 5) : ℤ) - 924 * (a (n - 6) : ℤ) + 792 * (a (n - 7) : ℤ) - 495 * (a (n - 8) : ℤ) + 220 * (a (n - 9) : ℤ) - 66 * (a (n - 10) : ℤ) + 12 * (a (n - 11) : ℤ) - (a (n - 12) : ℤ) := by
  sorry

end OMA.S_oeis_a227086
