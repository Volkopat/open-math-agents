import OMAStatements.S_oeis_a309616

-- Sela Fried, Proof of a recurrence for A309616, https://oeis.org/A309616/a309616.pdf.
-- Consecutive even and odd inputs have the same half, so their representation counts agree.
-- The difference between adjacent five-term sums leaves the two endpoints.
namespace OMA.A309616

open S_oeis_a309616

lemma count_window (m : ℕ) :
    representations m =
      ∑ t ∈ Finset.Icc (m / 2 - 4) (m / 2), representations t := by
  cases m with
  | zero => simp [representations]
  | succ m =>
    rw [representations]
    apply Finset.sum_congr rfl
    intro t ht
    have hle := (Finset.mem_Icc.mp ht).2
    have hlt : t < m + 1 := by omega
    simp [hlt]

lemma count_at_half (m : ℕ) : a ((m + 2) / 2) = representations m := by
  unfold a
  rw [count_window, count_window m]
  rw [show 2 * ((m + 2) / 2 - 1) / 2 = m / 2 by omega]

lemma five_terms (k : ℕ) : a (k + 5) =
    ∑ t ∈ Finset.Icc k (k + 4), representations t := by
  unfold a
  rw [count_window, show 2 * (k + 5 - 1) / 2 = k + 4 by omega]
  simp

lemma slide (k : ℕ) : a (k + 6) + representations k =
    a (k + 5) + representations (k + 5) := by
  rw [show k + 6 = (k + 1) + 5 by omega, five_terms (k + 1), five_terms k]
  rw [Finset.sum_Icc_succ_top (a := k + 1) (b := k + 4) (by omega) representations]
  rw [← Finset.insert_Icc_succ_left_eq_Icc (a := k) (b := k + 4) (by omega)]
  rw [Finset.sum_insert (by simp)]
  ac_rfl

end OMA.A309616

open OMA.S_oeis_a309616 OMA.A309616

theorem OMA.solution : type_of% @OMA.S_oeis_a309616.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  rw [show k + 6 - 1 = k + 5 by omega, show k + 6 + 1 = (k + 5) + 2 by omega,
    show k + 6 - 5 + 1 = k + 2 by omega, count_at_half (k + 5), count_at_half k]
  have h := slide k
  omega
