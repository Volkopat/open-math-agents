import OMAStatements.S_oeis_a007062
import Mathlib

/-!
Proof of Kurkov's conjecture: A007062(n) = A057030(n - 1) + 1 for n ≥ 2, and A007062(1) = 1.

By induction on `m`: `PSA m (i + 1) = PSB m i + 1` for every position `i ≥ 1`. The step holds because, on positions
`≥ 2`, P(m) of A007062 is P(m) of A057030 shifted by one position (`step`). Then `a007062 (k + 1) = PSA (k + 1) (k + 1)
= PSB (k + 1) k + 1 = PSB k k + 1 = a057030 k + 1`, since P(k + 1) of A057030 fixes position `k`.
The stabilisation lemmas `PSA_stable` and `PSB_stable` prove the limit claim of the statement's Conventions.
-/

namespace OMA.A007062Proof

open OMA.S_oeis_a007062

/-- One step of the induction: the shifted relation passes through P(n) of both entries. -/
theorem step (n : ℕ) (hn : 1 ≤ n) (s t : ℕ → ℕ) (h : ∀ i, 1 ≤ i → s (i + 1) = t i + 1) :
    ∀ i, 1 ≤ i → PA n s (i + 1) = PB n t i + 1 := by
  intro i hi
  unfold PA PB
  by_cases h1 : i + 1 ≤ n
  · rw [if_pos h1, if_pos (by omega : i < n)]
    exact h i hi
  · rw [if_neg h1, if_neg (by omega : ¬ i < n)]
    have e1 : i + 1 - n - 1 = i - n := by omega
    have hr : (i - n) % n < n := Nat.mod_lt _ (by omega)
    rw [e1]
    have e2 : n + n * ((i - n) / n) + (n - (i - n) % n)
        = (n - 1 + n * ((i - n) / n) + (n - (i - n) % n)) + 1 := by omega
    rw [e2]
    exact h _ (by omega)

/-- The main invariant: `PS(m)` of A007062 at position `i + 1` is `PS(m)` of A057030 at position `i`, plus one. -/
theorem shift : ∀ m i : ℕ, 1 ≤ i → PSA m (i + 1) = PSB m i + 1
  | 0, _, _ => rfl
  | 1, _, _ => rfl
  | m + 2, i, hi => by
      show PA (m + 2) (PSA (m + 1)) (i + 1) = PB (m + 2) (PSB (m + 1)) i + 1
      exact step (m + 2) (by omega) (PSA (m + 1)) (PSB (m + 1)) (fun j hj => shift (m + 1) j hj) i hi

/-- P(k + 1) of A007062 fixes positions `≤ k + 1`. -/
theorem PSA_succ (k i : ℕ) (hi : i ≤ k + 1) : PSA (k + 1) i = PSA k i := by
  rcases k with _ | m
  · rfl
  · show PA (m + 2) (PSA (m + 1)) i = PSA (m + 1) i
    have h : i ≤ m + 2 := by omega
    unfold PA
    rw [if_pos h]

/-- P(k + 1) of A057030 fixes positions `≤ k`. -/
theorem PSB_succ (k i : ℕ) (hi : i ≤ k) : PSB (k + 1) i = PSB k i := by
  rcases k with _ | m
  · rfl
  · show PB (m + 2) (PSB (m + 1)) i = PSB (m + 1) i
    have h : i < m + 2 := by omega
    unfold PB
    rw [if_pos h]

/-- Stabilisation for A007062: `PS(m)` at position `j` equals `a007062 j` for all `m ≥ j`. -/
theorem PSA_stable (j m : ℕ) (hj : j ≤ m) : PSA m j = a007062 j := by
  induction m, hj using Nat.le_induction with
  | base => rfl
  | succ m hjm ih => rw [PSA_succ m j (by omega), ih]

/-- Stabilisation for A057030: `PS(m)` at position `j` equals `a057030 j` for all `m ≥ j`. -/
theorem PSB_stable (j m : ℕ) (hj : j ≤ m) : PSB m j = a057030 j := by
  induction m, hj using Nat.le_induction with
  | base => rfl
  | succ m hjm ih => rw [PSB_succ m j hjm, ih]

end OMA.A007062Proof

open OMA.S_oeis_a007062 OMA.A007062Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a007062.main := by
  refine ⟨rfl, ?_⟩
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  show PSA (k + 1) (k + 1) = PSB (k + 1 - 1) (k + 1 - 1) + 1
  rw [Nat.add_sub_cancel, shift (k + 1) k hk, PSB_succ k k le_rfl]
