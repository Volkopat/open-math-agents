import OMAStatements.S_oeis_a265283

namespace OMA.A265283Proof
open OMA.S_oeis_a265283

def P (n : ℕ) (i : ℤ) : Bool :=
  if -(n : ℤ) ≤ i ∧ i ≤ n ∧ ((n : ℤ) ≤ i + 1 ∨ (n : ℤ) ≤ 1 - i ∨ i % 2 = 1) then true else false

theorem ca_eq (n : ℕ) : ∀ i, ca n i = P n i := by
  induction n with
  | zero => intro i; simp only [ca, P]; split_ifs <;> simp <;> omega
  | succ n ih =>
    intro i
    simp only [ca, ih, rule94, P]
    push_cast
    split_ifs <;> first | rfl | (exfalso; omega)

theorem F (n : ℕ) (hn : 2 ≤ n) : ∀ m, m ≤ 2 * n + 1 →
    ∑ k ∈ Finset.range m, (if ca n ((k : ℤ) - n) = true then 1 else 0) =
      min m 2 + (if 2 ≤ m then (min m (2 * n - 1) + n % 2) / 2 - 1 else 0) + (m - min m (2 * n - 1)) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
    intro hm
    rw [Finset.sum_range_succ, ih (by omega), ca_eq, P]
    split_ifs <;> simp_all <;> omega

theorem conj : ∀ n : ℕ, 1 < n → 2 * (a n : ℤ) = 5 - (-1) ^ n + 2 * n := by
  intro n hn
  rw [a, Finset.card_filter, F n hn _ le_rfl]
  rcases Nat.even_or_odd n with h | h
  · rw [h.neg_one_pow]
    obtain ⟨r, rfl⟩ := h
    split_ifs <;> push_cast <;> omega
  · rw [h.neg_one_pow]
    obtain ⟨r, rfl⟩ := h
    split_ifs <;> push_cast <;> omega

end OMA.A265283Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a265283.main := OMA.A265283Proof.conj
