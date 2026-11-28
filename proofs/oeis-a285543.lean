import OMAStatements.S_oeis_a285543

namespace OMA.S_oeis_a285543_Proof

open OMA.S_oeis_a285543 PowerSeries

private lemma step_s0 (c : Bool) :
    Nat.testBit 35 (c.toNat + 2 * (false.toNat + false.toNat + false.toNat + false.toNat)) = true := by
  cases c <;> decide

private lemma step_s4 (c : Bool) :
    Nat.testBit 35 (c.toNat + 2 * (true.toNat + true.toNat + true.toNat + true.toNat)) = false := by
  cases c <;> decide

private lemma step_c0_iff (a b c d : Bool) :
    Nat.testBit 35 (false.toNat + 2 * (a.toNat + b.toNat + c.toNat + d.toNat)) = true ↔
      a = false ∧ b = false ∧ c = false ∧ d = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> decide

private lemma step_c1_ge3 (a b c d : Bool) (h : 3 ≤ a.toNat + b.toNat + c.toNat + d.toNat) :
    Nat.testBit 35 (true.toNat + 2 * (a.toNat + b.toNat + c.toNat + d.toNat)) = false := by
  cases a <;> cases b <;> cases c <;> cases d <;> first | exact absurd h (by decide) | decide

private lemma step_c1_s0 :
    Nat.testBit 35 (true.toNat + 2 * (false.toNat + false.toNat + false.toNat + false.toNat)) = true := by
  decide

private lemma step_c1_s2 :
    Nat.testBit 35 (true.toNat + 2 * (false.toNat + true.toNat + false.toNat + true.toNat)) = true := by
  decide

private lemma state_parity : ∀ k : ℕ,
    (∀ x y : ℤ, (x + y) % 2 = 1 → state (2 * k) x y = false) ∧
    (∀ x y : ℤ, (x + y) % 2 = 0 → state (2 * k + 1) x y = true)
  | 0 => by
    have h0 : ∀ x y : ℤ, (x + y) % 2 = 1 → state 0 x y = false := by
      intro x y hxy
      simp only [state, decide_eq_false_iff_not]
      omega
    refine ⟨h0, fun x y hxy => ?_⟩
    show step (state 0) x y = true
    unfold step
    rw [h0 (x - 1) y (by omega), h0 (x + 1) y (by omega),
        h0 x (y - 1) (by omega), h0 x (y + 1) (by omega)]
    exact step_s0 _
  | k + 1 => by
    obtain ⟨_, ih1⟩ := state_parity k
    have heven : ∀ x y : ℤ, (x + y) % 2 = 1 → state (2 * (k + 1)) x y = false := by
      intro x y hxy
      have hstep : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [hstep, state]
      unfold step
      rw [ih1 (x - 1) y (by omega), ih1 (x + 1) y (by omega),
          ih1 x (y - 1) (by omega), ih1 x (y + 1) (by omega)]
      exact step_s4 _
    refine ⟨heven, fun x y hxy => ?_⟩
    rw [state]
    unfold step
    rw [heven (x - 1) y (by omega), heven (x + 1) y (by omega),
        heven x (y - 1) (by omega), heven x (y + 1) (by omega)]
    exact step_s0 _

private lemma state_odd_eq_true_iff (k : ℕ) (u v : ℤ) (huv : (u + v) % 2 = 1) :
    state (2 * k + 1) u v = true ↔
      state (2 * k) (u - 1) v = false ∧
      state (2 * k) (u + 1) v = false ∧
      state (2 * k) u (v - 1) = false ∧
      state (2 * k) u (v + 1) = false := by
  rw [state]
  unfold step
  rw [(state_parity k).1 u v huv]
  exact step_c0_iff _ _ _ _

private lemma state_odd_eq_false_of_neighbor (k : ℕ) (u v : ℤ) (huv : (u + v) % 2 = 1)
    (h : state (2 * k) (u - 1) v = true ∨ state (2 * k) (u + 1) v = true ∨
         state (2 * k) u (v - 1) = true ∨ state (2 * k) u (v + 1) = true) :
    state (2 * k + 1) u v = false := by
  cases hv : state (2 * k + 1) u v
  · rfl
  · exfalso
    obtain ⟨h1, h2, h3, h4⟩ := (state_odd_eq_true_iff k u v huv).mp hv
    rcases h with h | h | h | h
    · exact Bool.noConfusion (h1.symm.trans h)
    · exact Bool.noConfusion (h2.symm.trans h)
    · exact Bool.noConfusion (h3.symm.trans h)
    · exact Bool.noConfusion (h4.symm.trans h)

private lemma state_even_persist (k : ℕ) (x y : ℤ) (h : state (2 * k) x y = true) :
    state (2 * (k + 1)) x y = true := by
  have hxy : (x + y) % 2 = 0 := by
    by_contra hne
    have h1 : (x + y) % 2 = 1 := by omega
    have hf := (state_parity k).1 x y h1
    exact Bool.noConfusion (hf.symm.trans h)
  have hn1 : state (2 * k + 1) (x - 1) y = false :=
    state_odd_eq_false_of_neighbor k (x - 1) y (by omega)
      (Or.inr (Or.inl (by simp only [sub_add_cancel]; exact h)))
  have hn2 : state (2 * k + 1) (x + 1) y = false :=
    state_odd_eq_false_of_neighbor k (x + 1) y (by omega)
      (Or.inl (by simp only [add_sub_cancel_right]; exact h))
  have hn3 : state (2 * k + 1) x (y - 1) = false :=
    state_odd_eq_false_of_neighbor k x (y - 1) (by omega)
      (Or.inr (Or.inr (Or.inr (by simp only [sub_add_cancel]; exact h))))
  have hn4 : state (2 * k + 1) x (y + 1) = false :=
    state_odd_eq_false_of_neighbor k x (y + 1) (by omega)
      (Or.inr (Or.inr (Or.inl (by simp only [add_sub_cancel_right]; exact h))))
  have hc : state (2 * k + 1) x y = true := (state_parity k).2 x y hxy
  have hstep : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
  rw [hstep, state]
  unfold step
  rw [hc, hn1, hn2, hn3, hn4]
  exact step_c1_s0

private lemma state_even_persist_le {k m : ℕ} (hkm : k ≤ m) (x y : ℤ)
    (h : state (2 * k) x y = true) : state (2 * m) x y = true := by
  induction hkm with
  | refl => exact h
  | step _ ih => exact state_even_persist _ x y ih

private lemma state_even_bound : ∀ (k : ℕ) (x y : ℤ),
    state (2 * k) x y = true → -(k : ℤ) ≤ x ∧ x ≤ k ∧ -(k : ℤ) ≤ y ∧ y ≤ k
  | 0, x, y, h => by
    simp only [Nat.mul_zero, state, decide_eq_true_eq] at h
    omega
  | k + 1, x, y, h => by
    have hxy : (x + y) % 2 = 0 := by
      by_contra hne
      have h1 : (x + y) % 2 = 1 := by omega
      have hf := (state_parity (k + 1)).1 x y h1
      exact Bool.noConfusion (hf.symm.trans h)
    have hfalse : ∀ a b : ℤ, ¬(-(k : ℤ) ≤ a ∧ a ≤ k ∧ -(k : ℤ) ≤ b ∧ b ≤ k) →
        state (2 * k) a b = false := by
      intro a b hout
      cases hv : state (2 * k) a b
      · rfl
      · exact absurd (state_even_bound k a b hv) hout
    have hodd_true : ∀ u v : ℤ, (u + v) % 2 = 1 →
        (u ≥ (k : ℤ) + 2 ∨ u ≤ -((k : ℤ) + 2) ∨ v ≥ (k : ℤ) + 2 ∨ v ≤ -((k : ℤ) + 2)) →
        state (2 * k + 1) u v = true := by
      intro u v huv hout
      rw [state_odd_eq_true_iff k u v huv]
      refine ⟨hfalse _ _ (by omega), hfalse _ _ (by omega),
              hfalse _ _ (by omega), hfalse _ _ (by omega)⟩
    have hc : state (2 * k + 1) x y = true := (state_parity k).2 x y hxy
    have hstep : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [hstep, state] at h
    unfold step at h
    rw [hc] at h
    by_contra hout
    have hcases : x ≥ (k : ℤ) + 2 ∨ x ≤ -((k : ℤ) + 2) ∨
        y ≥ (k : ℤ) + 2 ∨ y ≤ -((k : ℤ) + 2) := by
      push_cast at hout
      omega
    have hge3 : 3 ≤ (state (2 * k + 1) (x - 1) y).toNat + (state (2 * k + 1) (x + 1) y).toNat +
        (state (2 * k + 1) x (y - 1)).toNat + (state (2 * k + 1) x (y + 1)).toNat := by
      rcases hcases with hx | hx | hy | hy
      · rw [hodd_true (x + 1) y (by omega) (by omega),
            hodd_true x (y - 1) (by omega) (by omega),
            hodd_true x (y + 1) (by omega) (by omega)]
        simp only [Bool.toNat_true]
        omega
      · rw [hodd_true (x - 1) y (by omega) (by omega),
            hodd_true x (y - 1) (by omega) (by omega),
            hodd_true x (y + 1) (by omega) (by omega)]
        simp only [Bool.toNat_true]
        omega
      · rw [hodd_true (x - 1) y (by omega) (by omega),
            hodd_true (x + 1) y (by omega) (by omega),
            hodd_true x (y + 1) (by omega) (by omega)]
        simp only [Bool.toNat_true]
        omega
      · rw [hodd_true (x - 1) y (by omega) (by omega),
            hodd_true (x + 1) y (by omega) (by omega),
            hodd_true x (y - 1) (by omega) (by omega)]
        simp only [Bool.toNat_true]
        omega
    have hbot := step_c1_ge3 _ _ _ _ hge3
    rw [hbot] at h
    exact Bool.noConfusion h

private lemma state_even_corner : ∀ k : ℕ, state (2 * k) (k : ℤ) (k : ℤ) = true
  | 0 => by simp only [Nat.mul_zero, Nat.cast_zero, state]; decide
  | k + 1 => by
    have ih := state_even_corner k
    have hfalse : ∀ x y : ℤ, ¬(-(k : ℤ) ≤ x ∧ x ≤ k ∧ -(k : ℤ) ≤ y ∧ y ≤ k) →
        state (2 * k) x y = false := by
      intro x y hout
      cases hv : state (2 * k) x y
      · rfl
      · exact absurd (state_even_bound k x y hv) hout
    have hn1 : state (2 * k + 1) (((k : ℤ) + 1) - 1) ((k : ℤ) + 1) = false :=
      state_odd_eq_false_of_neighbor k _ _ (by omega)
        (Or.inr (Or.inr (Or.inl (by simp only [add_sub_cancel_right]; exact ih))))
    have hn2 : state (2 * k + 1) (((k : ℤ) + 1) + 1) ((k : ℤ) + 1) = true := by
      rw [state_odd_eq_true_iff k _ _ (by omega)]
      refine ⟨hfalse _ _ (by omega), hfalse _ _ (by omega),
              hfalse _ _ (by omega), hfalse _ _ (by omega)⟩
    have hn3 : state (2 * k + 1) ((k : ℤ) + 1) (((k : ℤ) + 1) - 1) = false :=
      state_odd_eq_false_of_neighbor k _ _ (by omega)
        (Or.inl (by simp only [add_sub_cancel_right]; exact ih))
    have hn4 : state (2 * k + 1) ((k : ℤ) + 1) (((k : ℤ) + 1) + 1) = true := by
      rw [state_odd_eq_true_iff k _ _ (by omega)]
      refine ⟨hfalse _ _ (by omega), hfalse _ _ (by omega),
              hfalse _ _ (by omega), hfalse _ _ (by omega)⟩
    have hc : state (2 * k + 1) ((k : ℤ) + 1) ((k : ℤ) + 1) = true :=
      (state_parity k).2 _ _ (by omega)
    have hstep : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [hstep, state]
    unfold step
    push_cast
    rw [hc, hn1, hn2, hn3, hn4]
    exact step_c1_s2

private lemma sum_pow_two_rev (m : ℕ) :
    ∑ i ∈ Finset.range (m + 1), 2 ^ (m - i) = 2 ^ (m + 1) - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    have hsplit : ∑ i ∈ Finset.range (m + 1), 2 ^ (m + 1 - i) =
        2 * ∑ i ∈ Finset.range (m + 1), 2 ^ (m - i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have him : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      have hsub : m + 1 - i = (m - i) + 1 := by omega
      rw [hsub, pow_succ']
    rw [hsplit, ih]
    simp only [Nat.sub_self, pow_zero]
    rw [pow_succ' 2 (m + 1)]
    have hpos : 1 ≤ 2 ^ (m + 1) := Nat.one_le_pow _ _ (by decide)
    omega

private lemma a_odd (k : ℕ) : a (2 * k + 1) = 2 ^ (2 * k + 2) - 1 := by
  unfold a
  have hterm : ∀ i ∈ Finset.range (2 * k + 1 + 1),
      (state (2 * k + 1) (i : ℤ) (i : ℤ)).toNat * 2 ^ (2 * k + 1 - i) =
        2 ^ (2 * k + 1 - i) := by
    intro i _
    rw [(state_parity k).2 (i : ℤ) (i : ℤ) (by omega)]
    simp only [Bool.toNat_true, one_mul]
  rw [Finset.sum_congr rfl hterm]
  exact sum_pow_two_rev (2 * k + 1)

private lemma a_even (k : ℕ) : a (2 * k) = 2 ^ (2 * k + 1) - 2 ^ k := by
  unfold a
  have hsub : ∑ i ∈ Finset.range (k + 1),
      (state (2 * k) (i : ℤ) (i : ℤ)).toNat * 2 ^ (2 * k - i) =
      ∑ i ∈ Finset.range (2 * k + 1),
      (state (2 * k) (i : ℤ) (i : ℤ)).toNat * 2 ^ (2 * k - i) := by
    refine Finset.sum_subset (Finset.range_mono (by omega)) fun i hi hni => ?_
    have hik : k < i := by
      simp only [Finset.mem_range] at hi hni
      omega
    have hf : state (2 * k) (i : ℤ) (i : ℤ) = false := by
      cases hv : state (2 * k) (i : ℤ) (i : ℤ)
      · rfl
      · have hb := state_even_bound k (i : ℤ) (i : ℤ) hv
        omega
    rw [hf]
    simp only [Bool.toNat_false, zero_mul]
  rw [← hsub]
  have hterm : ∀ i ∈ Finset.range (k + 1),
      (state (2 * k) (i : ℤ) (i : ℤ)).toNat * 2 ^ (2 * k - i) =
        2 ^ k * 2 ^ (k - i) := by
    intro i hi
    have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have ht : state (2 * k) (i : ℤ) (i : ℤ) = true :=
      state_even_persist_le hik (i : ℤ) (i : ℤ) (state_even_corner i)
    rw [ht]
    simp only [Bool.toNat_true, one_mul]
    have hadd : 2 * k - i = k + (k - i) := by omega
    rw [hadd, pow_add]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, sum_pow_two_rev k, Nat.mul_sub,
      ← pow_add, mul_one]
  have hexp : k + (k + 1) = 2 * k + 1 := by omega
  rw [hexp]

private lemma a_even_int (k : ℕ) : (a (2 * k) : ℤ) = 2 ^ (2 * k + 1) - 2 ^ k := by
  rw [a_even k, Nat.cast_sub (Nat.pow_le_pow_right (by decide) (by omega))]
  push_cast
  rfl

private lemma a_odd_int (k : ℕ) : (a (2 * k + 1) : ℤ) = 2 ^ (2 * k + 2) - 1 := by
  rw [a_odd k, Nat.cast_sub (Nat.one_le_pow _ _ (by decide))]
  push_cast
  rfl

private lemma closed_form (n : ℕ) :
    (a n : ℤ) = (-1 + (-1 : ℤ) ^ n + 2 ^ (2 + n) - 2 ^ (n / 2) * (1 + (-1) ^ n)) / 2 := by
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [a_even_int k]
    have hneg : (-1 : ℤ) ^ (2 * k) = 1 := by
      rw [pow_mul]
      norm_num
    have hdiv : 2 * k / 2 = k := Nat.mul_div_right k (by decide)
    have hpow : (2 : ℤ) ^ (2 + 2 * k) = 2 * (2 : ℤ) ^ (2 * k + 1) := by
      have : 2 + 2 * k = (2 * k + 1) + 1 := by omega
      rw [this, pow_succ']
    rw [hneg, hdiv, hpow]
    omega
  · rw [a_odd_int k]
    have hneg : (-1 : ℤ) ^ (2 * k + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    have hpow : (2 : ℤ) ^ (2 + (2 * k + 1)) = 2 * (2 : ℤ) ^ (2 * k + 2) := by
      have : 2 + (2 * k + 1) = (2 * k + 2) + 1 := by omega
      rw [this, pow_succ']
    rw [hneg, hpow]
    simp only [add_neg_cancel, mul_zero, sub_zero]
    omega

private lemma a_rec (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 2 * a (n - 1) + 3 * a (n - 2) - 6 * a (n - 3) - 2 * a (n - 4) + 4 * a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
  · have h0 : 2 * k + 5 = 2 * (k + 2) + 1 := by omega
    have h1 : 2 * k + 5 - 1 = 2 * (k + 2) := by omega
    have h2 : 2 * k + 5 - 2 = 2 * (k + 1) + 1 := by omega
    have h3 : 2 * k + 5 - 3 = 2 * (k + 1) := by omega
    have h4 : 2 * k + 5 - 4 = 2 * k + 1 := by omega
    have h5 : 2 * k + 5 - 5 = 2 * k := by omega
    rw [h1, h2, h3, h4, h5, h0,
        a_odd_int (k + 2), a_even_int (k + 2), a_odd_int (k + 1),
        a_even_int (k + 1), a_odd_int k, a_even_int k]
    have e6 : 2 * (k + 2) + 2 = 2 * k + 6 := by omega
    have e5 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    have e4 : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
    have e3 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    rw [e6, e5, e4, e3]
    simp only [pow_add]
    ring
  · have h0 : 2 * k + 1 + 5 = 2 * (k + 3) := by omega
    have h1 : 2 * k + 1 + 5 - 1 = 2 * (k + 2) + 1 := by omega
    have h2 : 2 * k + 1 + 5 - 2 = 2 * (k + 2) := by omega
    have h3 : 2 * k + 1 + 5 - 3 = 2 * (k + 1) + 1 := by omega
    have h4 : 2 * k + 1 + 5 - 4 = 2 * (k + 1) := by omega
    have h5 : 2 * k + 1 + 5 - 5 = 2 * k + 1 := by omega
    rw [h1, h2, h3, h4, h5, h0,
        a_even_int (k + 3), a_odd_int (k + 2), a_even_int (k + 2),
        a_odd_int (k + 1), a_even_int (k + 1), a_odd_int k]
    have e7 : 2 * (k + 3) + 1 = 2 * k + 7 := by omega
    have e6 : 2 * (k + 2) + 2 = 2 * k + 6 := by omega
    have e5 : 2 * (k + 2) + 1 = 2 * k + 5 := by omega
    have e4 : 2 * (k + 1) + 2 = 2 * k + 4 := by omega
    have e3 : 2 * (k + 1) + 1 = 2 * k + 3 := by omega
    rw [e7, e6, e5, e4, e3]
    simp only [pow_add]
    ring

private lemma gf_eq :
    PowerSeries.mk (fun n => (a n : ℤ)) *
      ((1 - X) * (1 + X) * (1 - 2 * X) * (1 - 2 * X ^ 2)) =
      1 + X - 3 * X ^ 2 := by
  set A : PowerSeries ℤ := PowerSeries.mk (fun n => (a n : ℤ))
  have hmul : A * ((1 - X) * (1 + X) * (1 - 2 * X) * (1 - 2 * X ^ 2)) =
      A - C 2 * (X * A) - C 3 * (X * (X * A)) + C 6 * (X * (X * (X * A))) +
        C 2 * (X * (X * (X * (X * A)))) - C 4 * (X * (X * (X * (X * (X * A))))) := by
    simp only [map_ofNat]
    ring
  have hrhs : (1 + X - 3 * X ^ 2 : PowerSeries ℤ) = 1 + X - C 3 * X ^ 2 := by
    simp only [map_ofNat]
  rw [hmul, hrhs]
  have ha0 : (a 0 : ℤ) = 1 := by simpa using a_even_int 0
  have ha1 : (a 1 : ℤ) = 3 := by simpa using a_odd_int 0
  have ha2 : (a 2 : ℤ) = 6 := by simpa using a_even_int 1
  have ha3 : (a 3 : ℤ) = 15 := by simpa using a_odd_int 1
  have ha4 : (a 4 : ℤ) = 28 := by simpa using a_even_int 2
  ext n
  rcases n with _ | _ | _ | _ | _ | m
  · simp only [map_sub, map_add, coeff_C_mul, coeff_zero_X_mul, coeff_one, coeff_X, coeff_X_pow,
      A, coeff_mk, ha0]
    norm_num
  · simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_one,
      coeff_X, coeff_X_pow, A, coeff_mk, Nat.reduceAdd, ha0, ha1]
    norm_num
  · simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_one,
      coeff_X, coeff_X_pow, A, coeff_mk, Nat.reduceAdd, ha0, ha1, ha2]
    norm_num
  · simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_one,
      coeff_X, coeff_X_pow, A, coeff_mk, Nat.reduceAdd, ha0, ha1, ha2, ha3]
    norm_num
  · simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_one,
      coeff_X, coeff_X_pow, A, coeff_mk, Nat.reduceAdd, ha0, ha1, ha2, ha3, ha4]
    norm_num
  · simp only [map_sub, map_add, coeff_C_mul, coeff_succ_X_mul, coeff_one, coeff_X, coeff_X_pow,
      A, coeff_mk]
    have h0 : m + 1 + 1 + 1 + 1 + 1 ≠ 0 := by omega
    have h1 : m + 1 + 1 + 1 + 1 + 1 ≠ 1 := by omega
    have h2 : m + 1 + 1 + 1 + 1 + 1 ≠ 2 := by omega
    simp only [h0, h1, h2, ↓reduceIte]
    have hrec := a_rec (m + 5) (by omega)
    have s0 : m + 1 + 1 + 1 + 1 + 1 = m + 5 := by omega
    have s1 : m + 1 + 1 + 1 + 1 = m + 4 := by omega
    have s2 : m + 1 + 1 + 1 = m + 3 := by omega
    have s3 : m + 1 + 1 = m + 2 := by omega
    have s4 : m + 5 - 1 = m + 4 := by omega
    have s5 : m + 5 - 2 = m + 3 := by omega
    have s6 : m + 5 - 3 = m + 2 := by omega
    have s7 : m + 5 - 4 = m + 1 := by omega
    have s8 : m + 5 - 5 = m := by omega
    rw [s0, s1, s2, s3]
    rw [s4, s5, s6, s7, s8] at hrec
    linarith

end OMA.S_oeis_a285543_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a285543.main :=
  ⟨OMA.S_oeis_a285543_Proof.gf_eq,
   OMA.S_oeis_a285543_Proof.closed_form,
   OMA.S_oeis_a285543_Proof.a_rec⟩
