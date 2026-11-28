import OMAStatements.S_oeis_a127800
import Mathlib

namespace InverseTriangleRowSums

open OMA.S_oeis_a127800

private theorem row_sums (r : ℕ → Rat) (h : rowEquations r) :
    r 0 = 1 ∧ ∀ n : ℕ, 0 < n →
      ((∃ k : ℕ, n + 1 = 2 ^ k) → r n = 2) ∧
      ((¬ ∃ k : ℕ, n + 1 = 2 ^ k) → r n = 0) := by
  have h0 : r 0 = 1 := by simpa [prefixSum] using h 0
  have hprefix (t : ℕ) (ht : 2 ≤ t) :
      prefixSum r t = prefixSum r (t / 2) + 2 := by
    have he : t - 1 + 1 = t := by omega
    have hh := h (t - 1)
    rw [he, if_neg (by omega)] at hh
    linarith
  have hdiff (t : ℕ) (ht : 0 < t) :
      r (t - 1) = prefixSum r t - prefixSum r (t - 1) := by
    have he : t - 1 + 1 = t := by omega
    have hh : prefixSum r (t - 1 + 1) = prefixSum r (t - 1) + r (t - 1) := rfl
    rw [he] at hh
    linarith
  let P (t : ℕ) := ∃ k : ℕ, t = 2 ^ k
  have hall (t : ℕ) : 2 ≤ t →
      (P t → r (t - 1) = 2) ∧ (¬ P t → r (t - 1) = 0) := by
    induction t using Nat.strong_induction_on with
    | h t ih =>
      intro ht
      by_cases ht2 : t = 2
      · subst t
        have hv : r (2 - 1) = 2 := by
          rw [hdiff 2 (by decide), hprefix 2 (by decide)]
          norm_num
        exact ⟨fun _ => hv, fun hnot => (hnot ⟨1, by decide⟩).elim⟩
      by_cases heven : t % 2 = 0
      · let k := t / 2
        have hk : 2 ≤ k := by dsimp [k]; omega
        have hkt : k < t := by dsimp [k]; omega
        have hhalf : (t - 1) / 2 = k - 1 := by dsimp [k]; omega
        have hdouble : t = 2 * k := by dsimp [k]; omega
        have hrs : r (t - 1) = r (k - 1) := by
          rw [hdiff t (by omega), hprefix t ht, hprefix (t - 1) (by omega),
            hhalf, hdiff k (by omega)]
          change prefixSum r k + 2 - (prefixSum r (k - 1) + 2) =
            prefixSum r k - prefixSum r (k - 1)
          ring
        have hpow : P t ↔ P k := by
          constructor
          · rintro ⟨j, hj⟩
            cases j with
            | zero => simp at hj; omega
            | succ j =>
              rw [pow_succ] at hj
              exact ⟨j, by omega⟩
          · rintro ⟨j, hj⟩
            exact ⟨j + 1, by rw [pow_succ, ← hj]; omega⟩
        exact ⟨fun hp => hrs.trans ((ih k hkt hk).1 (hpow.mp hp)),
          fun hp => hrs.trans ((ih k hkt hk).2 (mt hpow.mpr hp))⟩
      · have hhalf : (t - 1) / 2 = t / 2 := by omega
        have hrs : r (t - 1) = 0 := by
          rw [hdiff t (by omega), hprefix t ht, hprefix (t - 1) (by omega),
            hhalf, sub_self]
        have hnpow : ¬ P t := by
          rintro ⟨j, hj⟩
          cases j with
          | zero => simp at hj; omega
          | succ j => rw [pow_succ] at hj; omega
        exact ⟨fun hp => (hnpow hp).elim, fun _ => hrs⟩
  refine ⟨h0, fun n hn => ?_⟩
  simpa [P] using hall (n + 1) (by omega)

end InverseTriangleRowSums

theorem OMA.solution : type_of% @OMA.S_oeis_a127800.main :=
  InverseTriangleRowSums.row_sums