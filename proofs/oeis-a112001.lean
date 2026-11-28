import OMAStatements.S_oeis_a112001

-- Problem: A112001: One fourth of fourth column (k=3) of triangle A111999.
-- Upstream: formal-conjectures statements/oeis-a112001.lean:0 (declaration OMA.S_oeis_a112001.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: by induction on the column recurrences, 3 T(m+1,1) = 2m T(m+1,0),
-- 9 T(m+2,2) = -(m+1) m (4m+5) T(m+1,0) and 405 T(m+3,3) = -2(m+1) m (20m^2+75m+67) T(m+2,0);
-- with T(m+2,0) = -(2m+3) T(m+1,0) the conjectured recurrence is a linear combination of these.

namespace P1A112001

open OMA.S_oeis_a112001

theorem e0 (m : ℕ) : T (m + 2) 0 = -(2 * ((m : ℤ) + 2) - 1) * T (m + 1) 0 := rfl

theorem es (m k : ℕ) : T (m + 2) (k + 1) =
    if m + 2 < k + 2 then 0
    else -(2 * ((m : ℤ) + 2) - ((k : ℤ) + 1) - 1) * (T (m + 1) (k + 1) + T (m + 1) k) := rfl

theorem e1 (m : ℕ) : T (m + 2) 1 = -(2 * (m : ℤ) + 2) * (T (m + 1) 1 + T (m + 1) 0) := by
  have h := es m 0
  rw [if_neg (show ¬ (m + 2 < 0 + 2) by omega), show (0 + 1 : ℕ) = 1 from rfl] at h
  rw [h]
  push_cast
  ring

theorem e2 (m : ℕ) (hm : 1 ≤ m) :
    T (m + 2) 2 = -(2 * (m : ℤ) + 1) * (T (m + 1) 2 + T (m + 1) 1) := by
  have h := es m 1
  rw [if_neg (show ¬ (m + 2 < 1 + 2) by omega), show (1 + 1 : ℕ) = 2 from rfl] at h
  rw [h]
  push_cast
  ring

theorem e3 (m : ℕ) (hm : 2 ≤ m) :
    T (m + 2) 3 = -(2 * (m : ℤ)) * (T (m + 1) 3 + T (m + 1) 2) := by
  have h := es m 2
  rw [if_neg (show ¬ (m + 2 < 2 + 2) by omega), show (2 + 1 : ℕ) = 3 from rfl] at h
  rw [h]
  push_cast
  ring

theorem L1 (m : ℕ) : 3 * T (m + 1) 1 = 2 * (m : ℤ) * T (m + 1) 0 := by
  induction m with
  | zero =>
    simp [show T 1 1 = 0 from rfl]
  | succ j ih =>
    rw [show j + 1 + 1 = j + 2 by omega]
    have h1 := e1 j
    have h0 := e0 j
    push_cast
    linear_combination 3 * h1 - (2 * (j : ℤ) + 2) * ih - (2 * (j : ℤ) + 2) * h0

theorem L2 (m : ℕ) :
    9 * T (m + 2) 2 = -((m : ℤ) + 1) * (m : ℤ) * (4 * (m : ℤ) + 5) * T (m + 1) 0 := by
  induction m with
  | zero =>
    simp [show T 2 2 = 0 from rfl]
  | succ j ih =>
    rw [show j + 1 + 2 = j + 3 by omega, show j + 1 + 1 = j + 2 by omega]
    have h2 := e2 (j + 1) (by omega)
    rw [show j + 1 + 2 = j + 3 by omega, show j + 1 + 1 = j + 2 by omega] at h2
    have l1 := L1 (j + 1)
    rw [show j + 1 + 1 = j + 2 by omega] at l1
    have h0 := e0 j
    push_cast at h2 l1 ⊢
    linear_combination 9 * h2 - (2 * (j : ℤ) + 3) * ih - 3 * (2 * (j : ℤ) + 3) * l1
      + ((j : ℤ) + 1) * (j : ℤ) * (4 * (j : ℤ) + 5) * h0

theorem L3 (m : ℕ) :
    405 * T (m + 3) 3 = -2 * ((m : ℤ) + 1) * (m : ℤ)
      * (20 * (m : ℤ) ^ 2 + 75 * (m : ℤ) + 67) * T (m + 2) 0 := by
  induction m with
  | zero =>
    simp [show T 3 3 = 0 from rfl]
  | succ j ih =>
    rw [show j + 1 + 3 = j + 4 by omega, show j + 1 + 2 = j + 3 by omega]
    have h3 := e3 (j + 2) (by omega)
    rw [show j + 2 + 2 = j + 4 by omega, show j + 2 + 1 = j + 3 by omega] at h3
    have l2 := L2 (j + 1)
    rw [show j + 1 + 2 = j + 3 by omega, show j + 1 + 1 = j + 2 by omega] at l2
    have h0 := e0 (j + 1)
    rw [show j + 1 + 2 = j + 3 by omega, show j + 1 + 1 = j + 2 by omega] at h0
    push_cast at h3 l2 h0 ⊢
    linear_combination 405 * h3 - (2 * (j : ℤ) + 4) * ih - 45 * (2 * (j : ℤ) + 4) * l2
      + 2 * ((j : ℤ) + 2) * ((j : ℤ) + 1) * (20 * (j : ℤ) ^ 2 + 115 * (j : ℤ) + 162) * h0

end P1A112001

open OMA.S_oeis_a112001 P1A112001 in
theorem OMA.solution : type_of% @OMA.S_oeis_a112001.main := by
  intro n hn
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
  rw [show j + 1 - 1 = j by omega]
  have qb' := L3 (j + 2)
  rw [show j + 2 + 3 = j + 5 by omega, show j + 2 + 2 = j + 4 by omega] at qb'
  have qa' := L3 (j + 1)
  rw [show j + 1 + 3 = j + 4 by omega, show j + 1 + 2 = j + 3 by omega] at qa'
  have q0' := e0 (j + 2)
  rw [show j + 2 + 2 = j + 4 by omega, show j + 2 + 1 = j + 3 by omega] at q0'
  have qb := congrArg (Int.cast : ℤ → ℚ) qb'
  have qa := congrArg (Int.cast : ℤ → ℚ) qa'
  have q0 := congrArg (Int.cast : ℤ → ℚ) q0'
  push_cast at qb qa q0
  unfold a
  rw [show j + 1 + 4 = j + 5 by omega]
  push_cast
  linear_combination (1 / 1620 : ℚ) *
    (((j : ℚ) + 1) * (20 * ((j : ℚ) + 1) ^ 2 + 75 * ((j : ℚ) + 1) + 67) * qb
      + (2 * (j : ℚ) + 7) * ((j : ℚ) + 3) * (20 * ((j : ℚ) + 2) ^ 2 + 75 * ((j : ℚ) + 2) + 67) * qa
      - 2 * ((j : ℚ) + 1) * ((j : ℚ) + 2) * ((j : ℚ) + 3)
        * (20 * ((j : ℚ) + 1) ^ 2 + 75 * ((j : ℚ) + 1) + 67)
        * (20 * ((j : ℚ) + 2) ^ 2 + 75 * ((j : ℚ) + 2) + 67) * q0)
