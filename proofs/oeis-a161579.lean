import OMAStatements.S_oeis_a161579

-- Problem: A161579: Positions n such that A010060(n) = A010060(n+3).
-- Upstream: formal-conjectures statements/oeis-a161579.lean:0 (declaration OMA.S_oeis_a161579.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Proof idea: t(2i) + t(2i+1) = 1. For odd k let W(j) = t(j) for odd j and W(j) = t(j+k-1) for
-- even j (the sign of the window sum of (-1)^t over [j, j+k-1], in 0/1 form). Then
-- W(j+1) + W(j) + t(j) + t(j+k) is even (A), and if t(j) = t(j+k) then W(j) + j + 1 + t(j) is
-- even (B). Between consecutive solutions n < m, W flips at every j with n < j < m and not at n,
-- so W(m) + W(n) + (m-n-1) is even; with (B) at n and m this makes t(m) + t(n) odd.

namespace S02A161579

open OMA.S_oeis_a161579

def W (k j : ℕ) : ℕ := if j % 2 = 1 then A010060 j else A010060 (j + k - 1)

theorem t_lt (n : ℕ) : A010060 n < 2 := Nat.mod_lt _ (by norm_num)

theorem pair (i : ℕ) : A010060 (2 * i) + A010060 (2 * i + 1) = 1 := by
  have e1 : Nat.digits 2 (2 * i + 1) = (2 * i + 1) % 2 :: Nat.digits 2 ((2 * i + 1) / 2) :=
    Nat.digits_def' (by norm_num) (by omega)
  have h1 : Nat.digits 2 (2 * i + 1) = 1 :: Nat.digits 2 i := by
    rw [e1, show (2 * i + 1) % 2 = 1 by omega, show (2 * i + 1) / 2 = i by omega]
  have h0 : (Nat.digits 2 (2 * i)).sum = (Nat.digits 2 i).sum := by
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      simp
    · have e0 : Nat.digits 2 (2 * i) = (2 * i) % 2 :: Nat.digits 2 ((2 * i) / 2) :=
        Nat.digits_def' (by norm_num) (by omega)
      rw [e0, show (2 * i) % 2 = 0 by omega, show (2 * i) / 2 = i by omega, List.sum_cons,
        zero_add]
  unfold A010060
  rw [h1, h0, List.sum_cons]
  omega

theorem factA (k j : ℕ) (hk : k % 2 = 1) :
    (W k (j + 1) + W k j + A010060 j + A010060 (j + k)) % 2 = 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, k = 2 * r + 1 := ⟨k / 2, by omega⟩
  obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega⟩
  · have e1 : W (2 * r + 1) (2 * i + 1) = A010060 (2 * i + 1) := by
      unfold W
      rw [if_pos (show (2 * i + 1) % 2 = 1 by omega)]
    have e2 : W (2 * r + 1) (2 * i) = A010060 (2 * (i + r)) := by
      unfold W
      rw [if_neg (show ¬ ((2 * i) % 2 = 1) by omega),
        show 2 * i + (2 * r + 1) - 1 = 2 * (i + r) by omega]
    have p1 := pair i
    have p2 := pair (i + r)
    rw [show 2 * (i + r) + 1 = 2 * i + (2 * r + 1) by ring] at p2
    rw [e1, e2]
    omega
  · have e1 : W (2 * r + 1) (2 * i + 1 + 1) = A010060 (2 * i + 1 + (2 * r + 1)) := by
      unfold W
      rw [if_neg (show ¬ ((2 * i + 1 + 1) % 2 = 1) by omega),
        show 2 * i + 1 + 1 + (2 * r + 1) - 1 = 2 * i + 1 + (2 * r + 1) by omega]
    have e2 : W (2 * r + 1) (2 * i + 1) = A010060 (2 * i + 1) := by
      unfold W
      rw [if_pos (show (2 * i + 1) % 2 = 1 by omega)]
    rw [e1, e2]
    omega

theorem factB (k j : ℕ) (hk : k % 2 = 1) (h : A010060 j = A010060 (j + k)) :
    (W k j + j + 1 + A010060 j) % 2 = 0 := by
  obtain ⟨r, rfl⟩ : ∃ r, k = 2 * r + 1 := ⟨k / 2, by omega⟩
  obtain ⟨i, rfl | rfl⟩ : ∃ i, j = 2 * i ∨ j = 2 * i + 1 := ⟨j / 2, by omega⟩
  · have e2 : W (2 * r + 1) (2 * i) = A010060 (2 * (i + r)) := by
      unfold W
      rw [if_neg (show ¬ ((2 * i) % 2 = 1) by omega),
        show 2 * i + (2 * r + 1) - 1 = 2 * (i + r) by omega]
    have p2 := pair (i + r)
    rw [show 2 * (i + r) + 1 = 2 * i + (2 * r + 1) by ring] at p2
    rw [e2]
    omega
  · have e2 : W (2 * r + 1) (2 * i + 1) = A010060 (2 * i + 1) := by
      unfold W
      rw [if_pos (show (2 * i + 1) % 2 = 1 by omega)]
    rw [e2]
    omega

theorem chain (k n m : ℕ) (hk : k % 2 = 1) (hn : A010060 n = A010060 (n + k))
    (hgap : ∀ j : ℕ, n < j → j < m → A010060 j ≠ A010060 (j + k)) :
    ∀ d : ℕ, n + 1 + d ≤ m → (W k (n + 1 + d) + W k n + d) % 2 = 0 := by
  intro d
  induction d with
  | zero =>
    intro _
    have hA := factA k n hk
    show (W k (n + 1) + W k n + 0) % 2 = 0
    omega
  | succ d ih =>
    intro hd
    have ih' := ih (by omega)
    have hA := factA k (n + 1 + d) hk
    have hne := hgap (n + 1 + d) (by omega) (by omega)
    have l1 := t_lt (n + 1 + d)
    have l2 := t_lt (n + 1 + d + k)
    show (W k (n + 1 + d + 1) + W k n + (d + 1)) % 2 = 0
    omega

theorem main' (k : ℕ) (hk : k % 2 = 1) (n m : ℕ) (hnm : n < m)
    (hn : A010060 n = A010060 (n + k)) (hm : A010060 m = A010060 (m + k))
    (hgap : ∀ j : ℕ, n < j → j < m → A010060 j ≠ A010060 (j + k)) :
    A010060 m ≠ A010060 n := by
  have hc := chain k n m hk hn hgap (m - n - 1) (by omega)
  rw [show n + 1 + (m - n - 1) = m by omega] at hc
  have hBm := factB k m hk hm
  have hBn := factB k n hk hn
  have l1 := t_lt m
  have l2 := t_lt n
  omega

end S02A161579

open OMA.S_oeis_a161579 S02A161579 in
theorem OMA.solution : type_of% @OMA.S_oeis_a161579.main := by
  intro k hk n m hnm hn hm hgap
  exact main' k hk n m hnm hn hm hgap
