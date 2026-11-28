import OMAStatements.S_oeis_a365658
import Mathlib

namespace OMA.A365658Proof

open OMA.S_oeis_a365658

/-- All of `P 0, ..., P (m - 1)` hold. -/
def checkAll (P : ℕ → Bool) : ℕ → Bool
  | 0 => true
  | m + 1 => P m && checkAll P m

theorem checkAll_true (P : ℕ → Bool) : ∀ m, checkAll P m = true → ∀ p, p < m → P p = true
  | 0, _, p, hp => absurd hp (Nat.not_lt_zero p)
  | m + 1, h, p, hp => by
    have h1 : P m = true ∧ checkAll P m = true := by simpa [checkAll] using h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hp with hp' | hp'
    · exact checkAll_true P m h1.2 p hp'
    · rw [hp']; exact h1.1

/-- The partition of `60` with the parts `l`, when `l` lists positive numbers with sum `60` (otherwise the
partition with the single part `60`). -/
def mk (l : List ℕ) : Nat.Partition 60 :=
  if h : (∀ i ∈ l, 0 < i) ∧ l.sum = 60 then
    ⟨(l : Multiset ℕ), fun hi => h.1 _ (Multiset.mem_coe.mp hi), by rw [Multiset.sum_coe]; exact h.2⟩
  else Nat.Partition.indiscrete 60

/-- Entry `k` (from `0`) lists the parts of a partition of `60` with exactly `k + 1` distinct nonempty subsums. -/
def wit : List (List ℕ) :=
  [[60], [30, 30], [59, 1], [30, 15, 15], [58, 1, 1], [30, 29, 1], [57, 2, 1], [29, 29, 1, 1], [56, 2, 1, 1],
    [30, 28, 1, 1], [55, 3, 1, 1], [30, 15, 14, 1], [54, 3, 2, 1], [30, 27, 2, 1], [53, 4, 2, 1],
    [30, 14, 14, 1, 1], [52, 4, 2, 1, 1], [30, 26, 2, 1, 1], [51, 5, 2, 1, 1], [30, 15, 13, 1, 1],
    [50, 5, 3, 1, 1], [30, 25, 3, 1, 1], [49, 6, 3, 1, 1], [30, 14, 13, 2, 1], [48, 6, 3, 2, 1],
    [30, 24, 3, 2, 1], [47, 7, 3, 2, 1], [30, 15, 12, 2, 1], [46, 7, 4, 2, 1], [30, 23, 4, 2, 1],
    [45, 8, 4, 2, 1], [30, 14, 12, 2, 1, 1], [44, 8, 4, 2, 1, 1], [30, 22, 4, 2, 1, 1], [43, 9, 4, 2, 1, 1],
    [30, 15, 11, 2, 1, 1], [42, 9, 5, 2, 1, 1], [30, 21, 5, 2, 1, 1], [41, 10, 5, 2, 1, 1],
    [30, 14, 11, 3, 1, 1], [40, 10, 5, 3, 1, 1], [30, 20, 5, 3, 1, 1], [39, 11, 5, 3, 1, 1],
    [30, 15, 10, 3, 1, 1], [38, 11, 6, 3, 1, 1], [30, 19, 6, 3, 1, 1], [37, 12, 6, 3, 1, 1],
    [30, 14, 10, 3, 2, 1], [36, 12, 6, 3, 2, 1], [30, 18, 6, 3, 2, 1], [35, 13, 6, 3, 2, 1],
    [30, 15, 9, 3, 2, 1], [34, 13, 7, 3, 2, 1], [30, 17, 7, 3, 2, 1], [33, 14, 7, 3, 2, 1],
    [30, 14, 9, 4, 2, 1], [32, 14, 7, 4, 2, 1], [30, 16, 7, 4, 2, 1], [31, 15, 7, 4, 2, 1],
    [30, 15, 8, 4, 2, 1]]

/-- Kernel computation: entry `k` of `wit` is a partition of `60` (so `mk` keeps it) with exactly `k + 1`
distinct nonempty subsums, for every `k < 60`. -/
theorem wit_check :
    checkAll (fun k => decide (((wit.getD k []).all (fun i => decide (0 < i))) = true ∧ (wit.getD k []).sum = 60) &&
      decide ((subsums (mk (wit.getD k []))).card = k + 1)) 60 = true := by
  decide +kernel

/-- Row `60` of the triangle is strictly positive. -/
theorem row60 : ∀ k : ℕ, 1 ≤ k → k ≤ 60 → 0 < T 60 k := by
  intro k hk1 hk2
  have h0 := checkAll_true _ 60 wit_check (k - 1) (by omega)
  simp only [Bool.and_eq_true] at h0
  have h : (subsums (mk (wit.getD (k - 1) []))).card = k - 1 + 1 := of_decide_eq_true h0.2
  rw [Nat.sub_add_cancel hk1] at h
  unfold T
  exact Finset.card_pos.mpr ⟨_, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩

/-- `60` has the `8` unitary divisors `1, 3, 4, 5, 12, 15, 20, 60`. -/
theorem udc60 : unitaryDivisorCount 60 = 8 := by
  decide +kernel

end OMA.A365658Proof

/-- The conjecture fails at `n = 60`: row `60` is strictly positive (one witness partition for each `k = 1, ..., 60`),
but `60` has `8` unitary divisors and `8` does not divide `60`. -/
theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a365658.main) := by
  intro h
  have h8 := (h 60 (by norm_num)).mp OMA.A365658Proof.row60
  rw [OMA.A365658Proof.udc60] at h8
  exact absurd h8 (by decide)
