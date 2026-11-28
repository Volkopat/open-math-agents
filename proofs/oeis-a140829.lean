import OMAStatements.S_oeis_a140829

namespace OMA.P_oeis_a140829

open OMA.S_oeis_a140829

lemma ceil_eqN {p d c : ℕ} (hc : c ≠ 0) (hd : 0 < d) (h1 : (c - 1) * d < p)
    (h2 : p ≤ c * d) : ⌈(p : ℚ) / d⌉₊ = c := by
  have hd' : (0 : ℚ) < d := by exact_mod_cast hd
  rw [Nat.ceil_eq_iff hc, lt_div_iff₀ hd', div_le_iff₀ hd']
  exact ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩

lemma step {n d c : ℕ} (hn : a n = d) (hc : c ≠ 0) (hd : 0 < d)
    (h1 : (c - 1) * d < Nat.fib (n + 1)) (h2 : Nat.fib (n + 1) ≤ c * d) : a (n + 1) = c := by
  show ⌈(Nat.fib (n + 1) : ℚ) / (a n : ℚ)⌉₊ = c
  rw [hn]
  exact ceil_eqN hc hd h1 h2

lemma vals : a 8 = 5 ∧ a 9 = 7 ∧ a 10 = 8 ∧ a 11 = 12 := by
  have h0 : a 0 = 1 := rfl
  have h1 : a 1 = 1 := step h0 (by norm_num) (by norm_num) (by decide) (by decide)
  have h2 : a 2 = 1 := step h1 (by norm_num) (by norm_num) (by decide) (by decide)
  have h3 : a 3 = 2 := step h2 (by norm_num) (by norm_num) (by decide) (by decide)
  have h4 : a 4 = 2 := step h3 (by norm_num) (by norm_num) (by decide) (by decide)
  have h5 : a 5 = 3 := step h4 (by norm_num) (by norm_num) (by decide) (by decide)
  have h6 : a 6 = 3 := step h5 (by norm_num) (by norm_num) (by decide) (by decide)
  have h7 : a 7 = 5 := step h6 (by norm_num) (by norm_num) (by decide) (by decide)
  have h8 : a 8 = 5 := step h7 (by norm_num) (by norm_num) (by decide) (by decide)
  have h9 : a 9 = 7 := step h8 (by norm_num) (by norm_num) (by decide) (by decide)
  have h10 : a 10 = 8 := step h9 (by norm_num) (by norm_num) (by decide) (by decide)
  have h11 : a 11 = 12 := step h10 (by norm_num) (by norm_num) (by decide) (by decide)
  exact ⟨h8, h9, h10, h11⟩

lemma cassini (k : ℕ) : ((Nat.fib (k + 1) : ℤ) ^ 2 - Nat.fib k * Nat.fib (k + 1) -
    (Nat.fib k : ℤ) ^ 2 = 1) ∨ ((Nat.fib (k + 1) : ℤ) ^ 2 - Nat.fib k * Nat.fib (k + 1) -
    (Nat.fib k : ℤ) ^ 2 = -1) := by
  induction k with
  | zero => left; simp
  | succ k ih =>
    have e : ((Nat.fib (k + 1 + 1) : ℤ) ^ 2 - Nat.fib (k + 1) * Nat.fib (k + 1 + 1) -
        (Nat.fib (k + 1) : ℤ) ^ 2) = -((Nat.fib (k + 1) : ℤ) ^ 2 -
        Nat.fib k * Nat.fib (k + 1) - (Nat.fib k : ℤ) ^ 2) := by
      rw [Nat.fib_add_two]; push_cast; ring
    rw [e]
    rcases ih with h | h
    · right; rw [h]
    · left; rw [h]; norm_num

lemma fib_even (k : ℕ) : Nat.fib (2 * k + 6) =
    Nat.fib (k + 3) * Nat.fib (k + 2) + Nat.fib (k + 4) * Nat.fib (k + 3) := by
  rw [show 2 * k + 6 = (k + 3) + (k + 2) + 1 by ring, Nat.fib_add]

lemma fib_odd (k : ℕ) : Nat.fib (2 * k + 7) =
    Nat.fib (k + 3) * Nat.fib (k + 3) + Nat.fib (k + 4) * Nat.fib (k + 4) := by
  rw [show 2 * k + 7 = (k + 3) + (k + 3) + 1 by ring, Nat.fib_add]

/-- The closed forms: `a(2k+4) = L(k+1) + 1` and `a(2k+5) = F(k+4) - 1`. -/
lemma closed (k : ℕ) (hk : 3 ≤ k) : a (2 * k + 4) = 2 * Nat.fib k + Nat.fib (k + 1) + 1 ∧
    a (2 * k + 5) + 1 = 2 * Nat.fib k + 3 * Nat.fib (k + 1) := by
  induction k, hk using Nat.le_induction with
  | base =>
    obtain ⟨-, -, h10, h11⟩ := vals
    refine ⟨?_, ?_⟩
    · rw [show 2 * 3 + 4 = 10 by rfl, h10]; decide
    · rw [show 2 * 3 + 5 = 11 by rfl, h11]; decide
  | succ k hk ih =>
    obtain ⟨_, hO⟩ := ih
    have hx2 : 2 ≤ Nat.fib k := by
      have h := Nat.fib_mono hk
      have h3 : Nat.fib 3 = 2 := by decide
      omega
    have hk1 : Nat.fib k + 1 ≤ Nat.fib (k + 1) := by
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      rw [Nat.fib_add_two]
      have : 1 ≤ Nat.fib j := Nat.fib_pos.mpr (by omega)
      omega
    have hC := cassini k
    have f2 : Nat.fib (k + 2) = Nat.fib k + Nat.fib (k + 1) := Nat.fib_add_two
    have f3 : Nat.fib (k + 3) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
    have f4 : Nat.fib (k + 4) = Nat.fib (k + 2) + Nat.fib (k + 3) := Nat.fib_add_two
    have hfe := fib_even k
    have hfo := fib_odd k
    -- the even term
    have hE : a (2 * (k + 1) + 4) = 2 * Nat.fib (k + 1) + Nat.fib (k + 1 + 1) + 1 := by
      rw [show 2 * (k + 1) + 4 = (2 * k + 5) + 1 by ring]
      apply step rfl (by omega) (by omega)
      · rw [show 2 * k + 5 + 1 = 2 * k + 6 by ring, hfe, f4, f3, f2]
        simp only [Nat.add_sub_cancel]
        zify
        have hO' : (a (2 * k + 5) : ℤ) = 2 * Nat.fib k + 3 * Nat.fib (k + 1) - 1 := by
          have := congrArg (Nat.cast : ℕ → ℤ) hO; push_cast at this; linarith
        rw [hO']
        rcases hC with h | h <;> nlinarith
      · rw [show 2 * k + 5 + 1 = 2 * k + 6 by ring, hfe, f4, f3, f2]
        zify
        have hO' : (a (2 * k + 5) : ℤ) = 2 * Nat.fib k + 3 * Nat.fib (k + 1) - 1 := by
          have := congrArg (Nat.cast : ℕ → ℤ) hO; push_cast at this; linarith
        rw [hO']
        rcases hC with h | h <;> nlinarith
    refine ⟨hE, ?_⟩
    -- the odd term
    have hO2 : a (2 * (k + 1) + 5) = 2 * Nat.fib (k + 1) + 3 * Nat.fib (k + 1 + 1) - 1 := by
      rw [show 2 * (k + 1) + 5 = (2 * (k + 1) + 4) + 1 by ring]
      apply step hE (by omega) (by omega)
      · rw [show 2 * (k + 1) + 4 + 1 = 2 * k + 7 by ring, hfo, f4, f3, f2]
        zify [show 1 ≤ 2 * Nat.fib (k + 1) + 3 * (Nat.fib k + Nat.fib (k + 1)) by omega,
          show 1 ≤ 2 * Nat.fib (k + 1) + 3 * (Nat.fib k + Nat.fib (k + 1)) - 1 by omega]
        have hx2' : (2 : ℤ) ≤ Nat.fib k := by exact_mod_cast hx2
        have hk1' : (Nat.fib k : ℤ) + 1 ≤ Nat.fib (k + 1) := by exact_mod_cast hk1
        rcases hC with h | h <;> linarith
      · rw [show 2 * (k + 1) + 4 + 1 = 2 * k + 7 by ring, hfo, f4, f3, f2]
        zify [show 1 ≤ 2 * Nat.fib (k + 1) + 3 * (Nat.fib k + Nat.fib (k + 1)) by omega]
        have hx2' : (2 : ℤ) ≤ Nat.fib k := by exact_mod_cast hx2
        have hk1' : (Nat.fib k : ℤ) + 1 ≤ Nat.fib (k + 1) := by exact_mod_cast hk1
        rcases hC with h | h <;> linarith
    rw [hO2]
    have : 1 ≤ Nat.fib (k + 1) := by omega
    omega

lemma closedZ (k : ℕ) (hk : 2 ≤ k) :
    (a (2 * k + 4) : ℤ) = 2 * Nat.fib k + Nat.fib (k + 1) + 1 ∧
    (a (2 * k + 5) : ℤ) = 2 * Nat.fib k + 3 * Nat.fib (k + 1) - 1 := by
  rcases Nat.lt_or_ge k 3 with h | h
  · obtain rfl : k = 2 := by omega
    obtain ⟨h8, h9, -, -⟩ := vals
    refine ⟨?_, ?_⟩
    · rw [show 2 * 2 + 4 = 8 by rfl, h8]
      have e1 : Nat.fib 2 = 1 := by decide
      have e2 : Nat.fib 3 = 2 := by decide
      rw [e1, e2]; norm_num
    · rw [show 2 * 2 + 5 = 9 by rfl, h9]
      have e1 : Nat.fib 2 = 1 := by decide
      have e2 : Nat.fib 3 = 2 := by decide
      rw [e1, e2]; norm_num
  obtain ⟨h1, h2⟩ := closed k h
  refine ⟨by rw [h1]; push_cast; ring, ?_⟩
  have := congrArg (Nat.cast : ℕ → ℤ) h2
  push_cast at this
  linarith

end OMA.P_oeis_a140829

theorem OMA.solution : type_of% @OMA.S_oeis_a140829.main := by
  intro n hn
  have F : ∀ t : ℕ, (Nat.fib (t + 2) : ℤ) = Nat.fib t + Nat.fib (t + 1) := fun t => by
    rw [Nat.fib_add_two]; push_cast; ring
  have C := OMA.P_oeis_a140829.closedZ
  rcases Nat.even_or_odd' n with ⟨j, rfl | rfl⟩
  · obtain ⟨t, rfl⟩ : ∃ t, j = t + 7 := ⟨j - 7, by omega⟩
    rw [show 2 * (t + 7) - 1 = 2 * (t + 4) + 5 by omega,
      show 2 * (t + 7) - 2 = 2 * (t + 4) + 4 by omega,
      show 2 * (t + 7) - 3 = 2 * (t + 3) + 5 by omega,
      show 2 * (t + 7) - 4 = 2 * (t + 3) + 4 by omega,
      show 2 * (t + 7) - 5 = 2 * (t + 2) + 5 by omega,
      show 2 * (t + 7) = 2 * (t + 5) + 4 by omega,
      (C (t + 5) (by omega)).1, (C (t + 4) (by omega)).1, (C (t + 4) (by omega)).2,
      (C (t + 3) (by omega)).1, (C (t + 3) (by omega)).2, (C (t + 2) (by omega)).2]
    have f3 := F (t + 1); have f4 := F (t + 2); have f5 := F (t + 3); have f6 := F (t + 4)
    linarith
  · obtain ⟨t, rfl⟩ : ∃ t, j = t + 6 := ⟨j - 6, by omega⟩
    rw [show 2 * (t + 6) + 1 - 1 = 2 * (t + 4) + 4 by omega,
      show 2 * (t + 6) + 1 - 2 = 2 * (t + 3) + 5 by omega,
      show 2 * (t + 6) + 1 - 3 = 2 * (t + 3) + 4 by omega,
      show 2 * (t + 6) + 1 - 4 = 2 * (t + 2) + 5 by omega,
      show 2 * (t + 6) + 1 - 5 = 2 * (t + 2) + 4 by omega,
      show 2 * (t + 6) + 1 = 2 * (t + 4) + 5 by omega,
      (C (t + 4) (by omega)).1, (C (t + 4) (by omega)).2, (C (t + 3) (by omega)).1,
      (C (t + 3) (by omega)).2, (C (t + 2) (by omega)).1, (C (t + 2) (by omega)).2]
    have f3 := F (t + 1); have f4 := F (t + 2); have f5 := F (t + 3)
    linarith
