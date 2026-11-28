import OMAStatements.S_oeis_a399155
import Mathlib

-- Original Lean proof: @justusklocke-cloud.

namespace A399155
open OMA.S_oeis_a399155

lemma gpf_spec (n : ℕ) (hn : 2 ≤ n) :
    (greatestPrimeFactor n).Prime ∧ greatestPrimeFactor n ∣ n := by
  have hne : n.primeFactorsList ≠ [] := (Nat.primeFactorsList_ne_nil n).2 (by omega)
  have hmem : greatestPrimeFactor n ∈ n.primeFactorsList := by
    unfold greatestPrimeFactor
    rw [if_neg (by omega), List.getLastI_eq_getLast?_getD, List.getLast?_eq_some_getLast hne]
    simp only [Option.getD_some]
    exact List.getLast_mem hne
  exact (Nat.mem_primeFactorsList (by omega)).1 hmem

lemma sub_ne_one (n q : ℕ) (hq : q.Prime) (hd : q ∣ n) : n - q ≠ 1 := by
  intro e
  exact hq.not_dvd_one (e ▸ Nat.dvd_sub hd (dvd_refl q))

lemma largest_le (fuel : ℕ) : ∀ n, n ≠ 1 → steps greatestPrimeFactor fuel n ≤ n / 2 := by
  induction fuel with
  | zero =>
    intro n _
    rw [steps]
    exact Nat.zero_le _
  | succ f ih =>
    intro n hn
    rw [steps]
    split_ifs with h0
    · exact Nat.zero_le _
    · have hn2 : 2 ≤ n := by omega
      obtain ⟨hp, hd⟩ := gpf_spec n hn2
      have hq2 := hp.two_le
      have h5 := ih _ (sub_ne_one n _ hp hd)
      omega

lemma smallest_even (fuel : ℕ) : ∀ n, 2 ∣ n → steps Nat.minFac fuel n = min fuel (n / 2) := by
  induction fuel with
  | zero => simp [steps]
  | succ f ih =>
    intro n he
    rw [steps]
    split_ifs with h0
    · simp [h0]
    · rw [(Nat.minFac_eq_two_iff n).2 he, ih (n - 2) (by omega)]
      omega

end A399155

open A399155 OMA.S_oeis_a399155 in
theorem OMA.solution : type_of% @OMA.S_oeis_a399155.main := by
  intro n hn
  unfold largestSteps smallestSteps
  by_cases he : 2 ∣ n
  · rw [smallest_even n n he]
    have h := largest_le n n (by omega)
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [steps, if_neg (show m + 1 ≠ 0 by omega)]
    obtain ⟨hp, hd⟩ := gpf_spec (m + 1) hn
    have hq := Nat.minFac_le_of_dvd hp.two_le hd
    have hpodd : ¬ 2 ∣ Nat.minFac (m + 1) := fun h => he (dvd_trans h (Nat.minFac_dvd _))
    have h := largest_le m _ (sub_ne_one _ _ hp hd)
    rw [smallest_even m (m + 1 - Nat.minFac (m + 1)) (by omega)]
    omega
