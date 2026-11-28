import OMAStatements.S_oeis_a327565
import Mathlib

namespace OMA.A327565Proof

open OMA.S_oeis_a327565

/-- The pile of the set that gives at the next transfer after `k` transfers. -/
def orb (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => 2 * n - orb n k / 2

theorem orb_zero (n : ℕ) : orb n 0 = n := rfl

theorem orb_succ (n k : ℕ) : orb n (k + 1) = 2 * n - orb n k / 2 := rfl

theorem orb_le (n k : ℕ) : orb n k ≤ 2 * n := by
  cases k with
  | zero => rw [orb_zero]; omega
  | succ k => rw [orb_succ]; omega

theorem orb_ge (n k : ℕ) : n ≤ orb n k := by
  cases k with
  | zero => exact le_of_eq (orb_zero n).symm
  | succ k => rw [orb_succ]; have := orb_le n k; omega

theorem orb_lt (n k : ℕ) (hn : 2 ≤ n) : orb n k < 2 * n := by
  cases k with
  | zero => rw [orb_zero]; omega
  | succ k => rw [orb_succ]; have := orb_ge n k; omega

theorem orb_gt (n k : ℕ) (hn : 2 ≤ n) : n < orb n (k + 1) := by
  rw [orb_succ]; have := orb_lt n k hn; omega

theorem transfer_even (k A B : ℕ) (hk : k % 2 = 0) :
    transfer k (A, B) = (A - (A + 1) / 2, B + (A + 1) / 2) := by
  unfold transfer
  exact if_pos hk

theorem transfer_odd (k A B : ℕ) (hk : k % 2 = 1) :
    transfer k (A, B) = (A + (B + 1) / 2, B - (B + 1) / 2) := by
  have hk' : ¬ (k % 2 = 0) := by omega
  unfold transfer
  exact if_neg hk'

theorem state_eq (n k : ℕ) :
    state n k = if k % 2 = 0 then (orb n k, 2 * n - orb n k) else (2 * n - orb n k, orb n k) := by
  induction k with
  | zero =>
    have h0 : (0 : ℕ) % 2 = 0 := rfl
    show (n, n) = _
    rw [if_pos h0, orb_zero, Prod.mk.injEq]
    constructor <;> omega
  | succ k ih =>
    have hle := orb_le n k
    show transfer k (state n k) = _
    rw [ih, orb_succ]
    rcases Nat.mod_two_eq_zero_or_one k with hk | hk
    · have hk' : ¬ ((k + 1) % 2 = 0) := by omega
      rw [if_pos hk, transfer_even k _ _ hk, if_neg hk', Prod.mk.injEq]
      constructor <;> omega
    · have hk0 : ¬ (k % 2 = 0) := by omega
      have hk' : (k + 1) % 2 = 0 := by omega
      rw [if_neg hk0, transfer_odd k _ _ hk, if_pos hk', Prod.mk.injEq]
      constructor <;> omega

theorem orb_of_state (n k j : ℕ) (h : state n k = state n j) :
    (k % 2 = j % 2 ∧ orb n k = orb n j) ∨ orb n k + orb n j = 2 * n := by
  have hk := orb_le n k
  have hj := orb_le n j
  rw [state_eq, state_eq] at h
  rcases Nat.mod_two_eq_zero_or_one k with h1 | h1 <;>
    rcases Nat.mod_two_eq_zero_or_one j with h2 | h2
  · rw [if_pos h1, if_pos h2, Prod.mk.injEq] at h
    exact Or.inl ⟨by omega, h.1⟩
  · have h2' : ¬ (j % 2 = 0) := by omega
    rw [if_pos h1, if_neg h2', Prod.mk.injEq] at h
    exact Or.inr (by omega)
  · have h1' : ¬ (k % 2 = 0) := by omega
    rw [if_neg h1', if_pos h2, Prod.mk.injEq] at h
    exact Or.inr (by omega)
  · have h1' : ¬ (k % 2 = 0) := by omega
    have h2' : ¬ (j % 2 = 0) := by omega
    rw [if_neg h1', if_neg h2', Prod.mk.injEq] at h
    exact Or.inl ⟨by omega, h.2⟩

/-- One transfer maps the zone `-2L ≤ 3x - 4n ≤ 2L + 1` into the zone `-L ≤ 3x - 4n ≤ L + 1`. -/
theorem zone_step (n x L : ℕ) (hx : x ≤ 2 * n) (h1 : 4 * n ≤ 3 * x + 2 * L)
    (h2 : 3 * x ≤ 4 * n + 2 * L + 1) :
    4 * n ≤ 3 * (2 * n - x / 2) + L ∧ 3 * (2 * n - x / 2) ≤ 4 * n + L + 1 := by
  constructor <;> omega

/-- In the terminal zone `-1 ≤ 3x - 4n ≤ 2`, two transfers return the same pile. -/
theorem cyc (n x : ℕ) (hx : x ≤ 2 * n) (h1 : 4 * n ≤ 3 * x + 1) (h2 : 3 * x ≤ 4 * n + 2) :
    2 * n - (2 * n - x / 2) / 2 = x := by
  omega

theorem zone_iter (n : ℕ) : ∀ s k : ℕ, 4 * n ≤ 3 * orb n k + 2 ^ s →
    3 * orb n k ≤ 4 * n + 2 ^ s + 1 →
    4 * n ≤ 3 * orb n (k + s) + 1 ∧ 3 * orb n (k + s) ≤ 4 * n + 2 := by
  intro s
  induction s with
  | zero =>
    intro k h1 h2
    rw [pow_zero] at h1 h2
    rw [Nat.add_zero]
    constructor <;> omega
  | succ s ih =>
    intro k h1 h2
    have hp : 2 ^ (s + 1) = 2 * 2 ^ s := by ring
    rw [hp] at h1 h2
    have hs : 4 * n ≤ 3 * orb n (k + 1) + 2 ^ s ∧ 3 * orb n (k + 1) ≤ 4 * n + 2 ^ s + 1 := by
      rw [orb_succ]
      exact zone_step n (orb n k) (2 ^ s) (orb_le n k) h1 h2
    have h := ih (k + 1) hs.1 hs.2
    rw [show k + 1 + s = k + (s + 1) by omega] at h
    exact h

theorem inC (n s : ℕ) (hn : n ≤ 2 ^ s) :
    4 * n ≤ 3 * orb n s + 1 ∧ 3 * orb n s ≤ 4 * n + 2 := by
  have h := zone_iter n s 0 (by rw [orb_zero]; omega) (by rw [orb_zero]; omega)
  rw [Nat.zero_add] at h
  exact h

/-- The set whose least element is `a n`. -/
def repSet (n : ℕ) : Set ℕ := {k : ℕ | 1 ≤ k ∧ ∃ j < k, state n k = state n j}

theorem a_eq (n : ℕ) : a n = sInf (repSet n) := rfl

theorem mem_repSet (n s : ℕ) (hn : n ≤ 2 ^ s) : s + 2 ∈ repSet n := by
  have hz := inC n s hn
  have hc : orb n (s + 2) = orb n s := by
    show 2 * n - orb n (s + 1) / 2 = orb n s
    rw [orb_succ]
    exact cyc n (orb n s) (orb_le n s) hz.1 hz.2
  have hp : (s + 2) % 2 = s % 2 := by omega
  have hst : state n (s + 2) = state n s := by
    rw [state_eq, state_eq, hc, hp]
  show 1 ≤ s + 2 ∧ ∃ j < s + 2, state n (s + 2) = state n j
  exact ⟨by omega, s, by omega, hst⟩

theorem a_le (n s : ℕ) (hn : n ≤ 2 ^ s) : a n ≤ s + 2 := by
  rw [a_eq]
  exact Nat.sInf_le (mem_repSet n s hn)

/-- The exact orbit for `n = 2^t + 1`: after `k ≤ t` transfers, `3x - 4n = -(2^(t-k) + 1)` for even `k` and
`2^(t-k) + 2` for odd `k`. -/
theorem orb_exact (t : ℕ) : ∀ k u : ℕ, k + u = t →
    (k % 2 = 0 → 3 * orb (2 ^ t + 1) k + 2 ^ u + 1 = 4 * (2 ^ t + 1)) ∧
    (k % 2 = 1 → 3 * orb (2 ^ t + 1) k = 4 * (2 ^ t + 1) + 2 ^ u + 2) := by
  intro k
  induction k with
  | zero =>
    intro u hu
    have hut : u = t := by omega
    subst hut
    rw [orb_zero]
    exact ⟨fun _ => by omega, fun h => by omega⟩
  | succ k ih =>
    intro u hu
    have h := ih (u + 1) (by omega)
    have hp : 2 ^ (u + 1) = 2 * 2 ^ u := by ring
    rw [hp] at h
    have hle := orb_le (2 ^ t + 1) k
    rw [orb_succ]
    refine ⟨fun hk => ?_, fun hk => ?_⟩
    · have e := h.2 (by omega)
      omega
    · have e := h.1 (by omega)
      omega

theorem no_rep (t k j : ℕ) (hk1 : 1 ≤ k) (hjk : j < k) (hk : k ≤ t + 2)
    (hst : state (2 ^ t + 1) k = state (2 ^ t + 1) j) : False := by
  have hT : 0 < 2 ^ t := pow_pos (by norm_num) t
  have hN : 2 ≤ 2 ^ t + 1 := by omega
  rcases orb_of_state _ _ _ hst with ⟨hpar, heq⟩ | hsum
  · have hj : j + 2 ≤ k := by omega
    obtain ⟨uj, huj⟩ : ∃ u, j + u = t := ⟨t - j, by omega⟩
    have Ej := orb_exact t j uj huj
    have hpj : 0 < 2 ^ uj := pow_pos (by norm_num) uj
    by_cases hkt : k ≤ t
    · obtain ⟨uk, huk⟩ : ∃ u, k + u = t := ⟨t - k, by omega⟩
      have Ek := orb_exact t k uk huk
      have hpk : 0 < 2 ^ uk := pow_pos (by norm_num) uk
      have hu : uk + 1 ≤ uj := by omega
      have hmono : 2 ^ (uk + 1) ≤ 2 ^ uj := Nat.pow_le_pow_right (by norm_num) hu
      rw [pow_succ] at hmono
      rcases Nat.mod_two_eq_zero_or_one j with h0 | h0
      · have e1 := Ej.1 h0
        have e2 := Ek.1 (by omega)
        omega
      · have e1 := Ej.2 h0
        have e2 := Ek.2 (by omega)
        omega
    · have hpow : 2 ^ t + 1 ≤ 2 ^ k := by
        have h' : 2 ^ (t + 1) ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        rw [pow_succ] at h'
        omega
      have hkC := inC (2 ^ t + 1) k hpow
      rcases Nat.mod_two_eq_zero_or_one j with h0 | h0
      · have e1 := Ej.1 h0
        omega
      · have e1 := Ej.2 h0
        omega
  · have h1 : 2 ^ t + 1 < orb (2 ^ t + 1) k := by
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      exact orb_gt _ k' hN
    have h2 := orb_ge (2 ^ t + 1) j
    omega

theorem a_first (t : ℕ) : a (2 ^ t + 1) = t + 3 := by
  have hT : 0 < 2 ^ t := pow_pos (by norm_num) t
  have hle1 : 2 ^ t + 1 ≤ 2 ^ (t + 1) := by rw [pow_succ]; omega
  have hup := a_le (2 ^ t + 1) (t + 1) hle1
  have hlow : t + 3 ≤ a (2 ^ t + 1) := by
    by_contra hlt
    have hmem : a (2 ^ t + 1) ∈ repSet (2 ^ t + 1) := by
      rw [a_eq]
      exact Nat.sInf_mem ⟨_, mem_repSet _ _ hle1⟩
    obtain ⟨hk1, j, hjk, hst⟩ := hmem
    exact no_rep t _ j hk1 hjk (by omega) hst
  omega

end OMA.A327565Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a327565.main := by
  intro m hm
  obtain ⟨t, rfl⟩ : ∃ t, m = t + 3 := ⟨m - 3, by omega⟩
  have ht : t + 3 - 3 = t := by omega
  rw [ht]
  refine ⟨OMA.A327565Proof.a_first t, fun n _ hn2 => ?_⟩
  have := OMA.A327565Proof.a_le n t (by omega)
  omega
