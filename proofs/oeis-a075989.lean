import OMAStatements.S_oeis_a075989

namespace OMA.P_oeis_a075989

open OMA.S_oeis_a075989

lemma fract_eq (n k : ℕ) (hk : 0 < k) :
    Int.fract ((n : ℚ) / k) = ((n % k : ℕ) : ℚ) / k := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  rw [Int.fract_eq_iff]
  refine ⟨by positivity, ?_, ?_⟩
  · rw [div_lt_one hkq]; exact_mod_cast Nat.mod_lt n hk
  · refine ⟨((n / k : ℕ) : ℤ), ?_⟩
    have h := Nat.div_add_mod n k
    have h' : (n : ℚ) = k * (n / k : ℕ) + (n % k : ℕ) := by exact_mod_cast h.symm
    rw [Int.cast_natCast, h']; field_simp; ring

lemma cond_a (n k : ℕ) (hk : 0 < k) :
    (1 : ℚ) / 2 ≤ Int.fract ((n : ℚ) / k) ↔ k ≤ 2 * (n % k) := by
  have hkq : (0 : ℚ) < k := by exact_mod_cast hk
  rw [fract_eq n k hk, le_div_iff₀ hkq]
  constructor
  · intro h; have : (k : ℚ) ≤ 2 * (n % k : ℕ) := by linarith
    exact_mod_cast this
  · intro h; have : (k : ℚ) ≤ 2 * (n % k : ℕ) := by exact_mod_cast h
    linarith

lemma two_mod (k d : ℕ) (hd : 0 < d) :
    (2 * k) % d ≠ 2 * (k % d) ↔ d ≤ 2 * (k % d) := by
  have hr := Nat.mod_lt k hd
  have e : (2 * k) % d = (2 * (k % d)) % d := by
    conv_lhs => rw [← Nat.div_add_mod k d]
    rw [show 2 * (d * (k / d) + k % d) = 2 * (k % d) + d * (2 * (k / d)) by ring,
      Nat.add_mul_mod_self_left]
  rw [e]
  constructor
  · intro h; by_contra h'; push Not at h'
    exact h (Nat.mod_eq_of_lt h')
  · intro h
    rw [Nat.mod_eq_sub_mod h, Nat.mod_eq_of_lt (by omega)]
    omega

lemma key_nat (k d : ℕ) (hd : 0 < d) :
    (k + d + k) % d ≠ (k + d) % d + k % d ↔ d ≤ 2 * ((k + d) % d) := by
  rw [show k + d + k = 2 * k + d by ring, Nat.add_mod_right, Nat.add_mod_right,
    show k % d + k % d = 2 * (k % d) by ring]
  exact two_mod k d hd

lemma cond_f (n k : ℕ) (hk : k < n) :
    f n k = if n - k ≤ 2 * (n % (n - k)) then 1 else 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, n = k + d := ⟨n - k, by omega⟩
  have hd : 0 < d := by omega
  have e : k + d - k = d := by omega
  rw [e]
  have h2 : |((k + d : ℕ) : ℤ) - (k : ℤ)| = ((d : ℕ) : ℤ) := by
    push_cast; rw [show (k : ℤ) + d - k = d by ring]; exact abs_of_nonneg (by positivity)
  have h3 : ((k + d : ℕ) : ℤ) + (k : ℤ) = ((k + d + k : ℕ) : ℤ) := by push_cast; ring
  unfold f
  rw [h2, h3]
  simp only [← Int.natCast_mod]
  have hc : (((k + d + k) % d : ℕ) : ℤ) ≠ (((k + d) % d : ℕ) : ℤ) + ((k % d : ℕ) : ℤ) ↔
      d ≤ 2 * ((k + d) % d) := by
    rw [← key_nat k d hd]
    simp only [ne_eq, ← Nat.cast_add, Nat.cast_inj]
  simp only [hc]

lemma a_eq (n : ℕ) :
    a n = ((Finset.Icc 1 n).filter (fun k : ℕ => k ≤ 2 * (n % k))).card := by
  unfold a
  congr 1
  apply Finset.filter_congr
  intro k hk
  exact cond_a n k (by simp at hk; omega)

end OMA.P_oeis_a075989

theorem OMA.solution : type_of% @OMA.S_oeis_a075989.main := by
  intro n hn
  rw [OMA.P_oeis_a075989.a_eq, Finset.card_filter]
  rw [Finset.sum_congr rfl (fun k hk => OMA.P_oeis_a075989.cond_f n k (by simp at hk; omega))]
  have hI : Finset.Icc 1 n = insert n (Finset.Ico 1 n) := by
    ext x; simp; omega
  rw [hI, Finset.sum_insert (by simp), Nat.mod_self]
  simp only [show ¬ n ≤ 2 * 0 by omega, if_false, zero_add]
  apply Finset.sum_nbij' (fun k => n - k) (fun k => n - k)
  · intro x hx; simp at hx ⊢; omega
  · intro x hx; simp at hx ⊢; omega
  · intro x hx; simp at hx; omega
  · intro x hx; simp at hx; omega
  · intro x hx; simp at hx
    rw [show n - (n - x) = x by omega]
