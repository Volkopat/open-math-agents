import OMAStatements.S_oeis_a115792

namespace OMA.P115792

open OMA.S_oeis_a115792

lemma T_rec (n : ℕ) : T (n + 3) = T (n + 2) + T (n + 1) + T n := by rw [T]

lemma T_pos (n : ℕ) : 1 ≤ T (n + 2) := by
  induction n with
  | zero => simp [T]
  | succ n ih =>
    have h := T_rec n
    have e : n + 1 + 2 = n + 3 := by ring
    rw [e]; omega

lemma ceil_eq (k : ℤ) (hk : 1 ≤ k) :
    ⌈((k : ℚ) - 1) ^ 2 / (4 * (k : ℚ))⌉ = (k + 2) / 4 := by
  have h1 : 4 * ((k + 2) / 4) ≤ k + 2 := by omega
  have h2 : k + 2 < 4 * ((k + 2) / 4) + 4 := by omega
  generalize (k + 2) / 4 = m at h1 h2
  have hkq : (0 : ℚ) < 4 * (k : ℚ) := by
    have : (1 : ℚ) ≤ (k : ℚ) := by exact_mod_cast hk
    linarith
  rw [Int.ceil_eq_iff]
  constructor
  · rw [lt_div_iff₀ hkq]
    have : (m - 1) * (4 * k) < (k - 1) ^ 2 := by nlinarith
    exact_mod_cast this
  · rw [div_le_iff₀ hkq]
    have : (k - 1) ^ 2 ≤ m * (4 * k) := by nlinarith
    exact_mod_cast this

/-- The closed form `floor((T(n) + 2) / 4)` of the ceiling. -/
def c (n : ℕ) : ℤ := ((T n : ℤ) + 2) / 4

lemma a_eq (n : ℕ) : a (n + 2) = c (n + 2) := by
  have h := ceil_eq (T (n + 2) : ℤ) (by exact_mod_cast T_pos n)
  simp only [Int.cast_natCast] at h
  unfold a c
  exact h

lemma per (n : ℕ) : T (n + 8) % 4 = T n % 4 ∧ T (n + 9) % 4 = T (n + 1) % 4 ∧
    T (n + 10) % 4 = T (n + 2) % 4 := by
  induction n with
  | zero => simp [T]
  | succ n ih =>
    obtain ⟨h0, h1, h2⟩ := ih
    have r0 : T (n + 3) = T (n + 2) + T (n + 1) + T n := T_rec n
    have r8 : T (n + 11) = T (n + 10) + T (n + 9) + T (n + 8) := T_rec (n + 8)
    have e1 : n + 1 + 8 = n + 9 := by ring
    have e2 : n + 1 + 9 = n + 10 := by ring
    have e3 : n + 1 + 10 = n + 11 := by ring
    have e4 : n + 1 + 1 = n + 2 := by ring
    have e5 : n + 1 + 2 = n + 3 := by ring
    rw [e1, e2, e3, e4, e5]
    refine ⟨h1, h2, ?_⟩
    omega

lemma c_shift (x y : ℕ) (h : y % 4 = x % 4) :
    ((y : ℤ) + 2) / 4 = ((x : ℤ) + 2) / 4 + ((y : ℤ) - x) / 4 := by
  omega

lemma u_per (n : ℕ) :
    c (n + 11) - c (n + 10) - c (n + 9) - c (n + 8) = c (n + 3) - c (n + 2) - c (n + 1) - c n := by
  obtain ⟨h0, h1, h2⟩ := per n
  have r0 : T (n + 3) = T (n + 2) + T (n + 1) + T n := T_rec n
  have r8 : T (n + 11) = T (n + 10) + T (n + 9) + T (n + 8) := T_rec (n + 8)
  have h3 : T (n + 11) % 4 = T (n + 3) % 4 := by omega
  have k0 := c_shift _ _ h0
  have k1 := c_shift _ _ h1
  have k2 := c_shift _ _ h2
  have k3 := c_shift _ _ h3
  have d0 : 4 * (((T (n + 8) : ℤ) - T n) / 4) = (T (n + 8) : ℤ) - T n := by omega
  have d1 : 4 * (((T (n + 9) : ℤ) - T (n + 1)) / 4) = (T (n + 9) : ℤ) - T (n + 1) := by omega
  have d2 : 4 * (((T (n + 10) : ℤ) - T (n + 2)) / 4) = (T (n + 10) : ℤ) - T (n + 2) := by omega
  have d3 : 4 * (((T (n + 11) : ℤ) - T (n + 3)) / 4) = (T (n + 11) : ℤ) - T (n + 3) := by omega
  have r0' : (T (n + 3) : ℤ) = T (n + 2) + T (n + 1) + T n := by exact_mod_cast r0
  have r8' : (T (n + 11) : ℤ) = T (n + 10) + T (n + 9) + T (n + 8) := by exact_mod_cast r8
  unfold c
  linarith

lemma window (n : ℕ) :
    c (n + 10) - c (n + 8) - 2 * c (n + 7) - 2 * c (n + 6) - 2 * c (n + 5) - 2 * c (n + 4)
      - 2 * c (n + 3) - 3 * c (n + 2) - 2 * c (n + 1) - c n = 0 := by
  induction n with
  | zero => simp [c, T]
  | succ n ih =>
    have h := u_per n
    have e1 : n + 1 + 10 = n + 11 := by ring
    have e2 : n + 1 + 8 = n + 9 := by ring
    have e3 : n + 1 + 7 = n + 8 := by ring
    have e4 : n + 1 + 6 = n + 7 := by ring
    have e5 : n + 1 + 5 = n + 6 := by ring
    have e6 : n + 1 + 4 = n + 5 := by ring
    have e7 : n + 1 + 3 = n + 4 := by ring
    have e8 : n + 1 + 2 = n + 3 := by ring
    have e9 : n + 1 + 1 = n + 2 := by ring
    rw [e1, e2, e3, e4, e5, e6, e7, e8, e9]
    linarith

end OMA.P115792

open OMA.S_oeis_a115792 OMA.P115792 in
theorem OMA.solution : type_of% @OMA.S_oeis_a115792.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 12 := ⟨n - 12, by omega⟩
  have i0 : k + 12 = (k + 10) + 2 := by ring
  have i2 : k + 12 - 2 = (k + 8) + 2 := by omega
  have i3 : k + 12 - 3 = (k + 7) + 2 := by omega
  have i4 : k + 12 - 4 = (k + 6) + 2 := by omega
  have i5 : k + 12 - 5 = (k + 5) + 2 := by omega
  have i6 : k + 12 - 6 = (k + 4) + 2 := by omega
  have i7 : k + 12 - 7 = (k + 3) + 2 := by omega
  have i8 : k + 12 - 8 = (k + 2) + 2 := by omega
  have i9 : k + 12 - 9 = (k + 1) + 2 := by omega
  have i10 : k + 12 - 10 = k + 2 := by omega
  rw [i2, i3, i4, i5, i6, i7, i8, i9, i10, i0]
  simp only [a_eq]
  have w := window (k + 2)
  simp only [Nat.add_assoc, Nat.reduceAdd] at w ⊢
  linarith
