import OMAStatements.S_oeis_a071055
import Mathlib

open OMA.S_oeis_a071055

private def P : ℕ → ℤ → Bool
  | 0, x => decide (x = 0)
  | t + 1, x => xor (P t (x - 1)) (P t (x + 1))

private lemma P_supp (t : ℕ) (x : ℤ) (h : P t x = true) :
    -(t : ℤ) ≤ x ∧ x ≤ t ∧ (x + t) % 2 = 0 := by
  induction t generalizing x with
  | zero => simp [P] at h; subst h; simp
  | succ t ih =>
    simp only [P] at h
    rcases hx : P t (x - 1) with _ | _ <;> rcases hy : P t (x + 1) with _ | _ <;> rw [hx, hy] at h
    · simp at h
    · have := ih _ hy; push_cast; omega
    · have := ih _ hx; push_cast; omega
    · simp at h

private lemma P_f (t : ℕ) (x : ℤ) (h : ¬ (-(t : ℤ) ≤ x ∧ x ≤ t ∧ (x + t) % 2 = 0)) : P t x = false := by
  by_contra h'
  exact h (P_supp t x (by simpa using h'))

private lemma P_edge (t : ℕ) : P t t = true ∧ P t (-(t : ℤ)) = true := by
  induction t with
  | zero => simp [P]
  | succ t ih =>
    simp only [P]
    push_cast
    rw [show (t : ℤ) + 1 - 1 = t by ring, P_f t ((t : ℤ) + 1 + 1) (by omega),
      show -((t : ℤ) + 1) + 1 = -(t : ℤ) by ring, P_f t (-((t : ℤ) + 1) - 1) (by omega), ih.1, ih.2]
    simp

private lemma par_add (a b : ℕ) : decide ((a + b) % 2 = 1) = xor (decide (a % 2 = 1)) (decide (b % 2 = 1)) := by
  rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;> rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;>
    simp [Nat.add_mod, ha, hb]

private lemma P_choose (t k : ℕ) (hk : k ≤ t) :
    P t (2 * (k : ℤ) - t) = decide (t.choose k % 2 = 1) := by
  induction t generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp [P]
  | succ t ih =>
    simp only [P]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · have h1 : P t (2 * ((0 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) - 1) = false := P_f _ _ (by push_cast; omega)
      have h2 : 2 * ((0 : ℕ) : ℤ) - ((t + 1 : ℕ) : ℤ) + 1 = 2 * ((0 : ℕ) : ℤ) - t := by push_cast; ring
      rw [h1, h2, ih 0 (by omega)]
      simp
    · rcases Nat.lt_or_ge t k with hkt | hkt
      · obtain rfl : k = t + 1 := by omega
        push_cast
        rw [show 2 * ((t : ℤ) + 1) - (t + 1) - 1 = 2 * (t : ℤ) - t by ring, ih t le_rfl,
          P_f t _ (by omega)]
        simp
      · obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        push_cast
        rw [show 2 * ((j : ℤ) + 1) - (t + 1) - 1 = 2 * (j : ℤ) - t by ring,
          show 2 * ((j : ℤ) + 1) - (t + 1) + 1 = 2 * ((j + 1 : ℕ) : ℤ) - t by push_cast; ring,
          ih j (by omega), ih (j + 1) hkt, Nat.choose_succ_succ', par_add]

private def live (t : ℕ) (i : ℤ) : Prop :=
  (-(t : ℤ) ≤ i ∧ i ≤ t) ∧ ((i + t) % 2 = 0 ∨ P t (i - 1) = P t (i + 1))

private lemma table (l c r : Bool) :
    rule182 l c r = true ↔ ((l = true ∧ c = true ∧ r = true) ∨ (l = true ∧ c = false) ∨
      (l = false ∧ c = true ∧ r = false) ∨ (l = false ∧ c = false ∧ r = true)) := by
  cases l <;> cases c <;> cases r <;> decide

set_option maxHeartbeats 4000000 in
private lemma state_iff (t : ℕ) (i : ℤ) : state t i = true ↔ live t i := by
  induction t generalizing i with
  | zero => simp [state, live, P]; omega
  | succ t ih =>
    rw [state, table]
    simp only [Bool.eq_false_iff, ne_eq, ih]
    unfold live
    simp only [P]
    push_cast
    rw [show i - 1 - 1 = i - 2 by ring, show i + 1 + 1 = i + 2 by ring, show i - 1 + 1 = i by ring,
      show i + 1 - 1 = i by ring]
    have s1 := P_supp t (i - 2)
    have s2 := P_supp t (i - 1)
    have s3 := P_supp t i
    have s4 := P_supp t (i + 1)
    have s5 := P_supp t (i + 2)
    have e := P_edge t
    have e1 : (i - 2 = t ∨ i - 2 = -(t : ℤ)) → P t (i - 2) = true := by
      rintro (h | h) <;> rw [h]; exacts [e.1, e.2]
    have e3 : (i = t ∨ i = -(t : ℤ)) → P t i = true := by
      rintro (h | h) <;> rw [h]; exacts [e.1, e.2]
    have e5 : (i + 2 = t ∨ i + 2 = -(t : ℤ)) → P t (i + 2) = true := by
      rintro (h | h) <;> rw [h]; exacts [e.1, e.2]
    have e2 : (i - 1 = t ∨ i - 1 = -(t : ℤ)) → P t (i - 1) = true := by
      rintro (h | h) <;> rw [h]; exacts [e.1, e.2]
    have e4 : (i + 1 = t ∨ i + 1 = -(t : ℤ)) → P t (i + 1) = true := by
      rintro (h | h) <;> rw [h]; exacts [e.1, e.2]
    have m1 : (i - 1 - 1 + t) % 2 = (i + t) % 2 := by omega
    have m2 : (i + 1 + t) % 2 = (i - 1 + t) % 2 := by omega
    revert s1 s2 s3 s4 s5 e1 e2 e3 e4 e5
    cases P t (i - 2) <;> cases P t (i - 1) <;> cases P t i <;> cases P t (i + 1) <;>
      cases P t (i + 2) <;> simp <;> omega

private lemma lucN (a b r s : ℕ) (hr : r < 2) (hs : s < 2) :
    (2 * a + r).choose (2 * b + s) % 2 = (r.choose s * a.choose b) % 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (p := 2) (n := 2 * a + r) (k := 2 * b + s)
  rw [show (2 * a + r) % 2 = r by omega, show (2 * b + s) % 2 = s by omega,
    show (2 * a + r) / 2 = a by omega, show (2 * b + s) / 2 = b by omega] at h
  exact h

private lemma luc10 (t j : ℕ) : (2 * t + 1).choose (2 * j) % 2 = t.choose j % 2 := by
  have := lucN t j 1 0 (by norm_num) (by norm_num); simpa using this
private lemma luc11 (t j : ℕ) : (2 * t + 1).choose (2 * j + 1) % 2 = t.choose j % 2 := by
  have := lucN t j 1 1 (by norm_num) (by norm_num); simpa using this
private lemma luc00 (t j : ℕ) : (2 * t).choose (2 * j) % 2 = t.choose j % 2 := by
  have := lucN t j 0 0 (by norm_num) (by norm_num); simpa using this
private lemma luc01 (t j : ℕ) : (2 * t).choose (2 * j + 1) % 2 = 0 := by
  have := lucN t j 0 1 (by norm_num) (by norm_num); simpa using this

private lemma sum2 (m : ℕ) (f : ℕ → ℕ) :
    ∑ j ∈ Finset.range (2 * m), f j = ∑ k ∈ Finset.range m, (f (2 * k) + f (2 * k + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ]
    ring

private def cc (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, (if n.choose k % 2 = n.choose (k + 1) % 2 then 0 else 1)

private def O (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), (if n.choose k % 2 = 1 then 1 else 0)

private lemma a_eq (n : ℕ) : a n = cc n := by
  unfold a cc
  rw [Finset.card_filter, Finset.sum_range_succ, sum2]
  have f_even : ∀ k : ℕ, k ≤ n → state n (((2 * k : ℕ) : ℤ) - n) = true := by
    intro k hk; rw [state_iff]; unfold live; push_cast; omega
  rw [f_even n le_rfl]
  simp only [Bool.true_eq_false, if_false, add_zero]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Finset.mem_range] at hk
  rw [f_even k hk.le]
  simp only [Bool.true_eq_false, if_false, zero_add]
  have hl : state n (((2 * k + 1 : ℕ) : ℤ) - n) = true ↔
      P n (2 * (k : ℤ) - n) = P n (2 * ((k + 1 : ℕ) : ℤ) - n) := by
    rw [state_iff]; unfold live; push_cast
    rw [show 2 * (k : ℤ) + 1 - n - 1 = 2 * k - n by ring, show 2 * (k : ℤ) + 1 - n + 1 = 2 * (k + 1) - n by ring]
    constructor
    · rintro ⟨-, h | h⟩
      · omega
      · exact h
    · intro h; exact ⟨by omega, Or.inr h⟩
  rw [P_choose n k hk.le, P_choose n (k + 1) hk] at hl
  by_cases hs : state n (((2 * k + 1 : ℕ) : ℤ) - n) = true
  · have := hl.1 hs
    have hs' : state n (2 * (k : ℤ) + 1 - n) = true := by push_cast at hs; exact hs
    rw [if_neg (by simp [hs']), if_pos]
    rcases Nat.mod_two_eq_zero_or_one (n.choose k) with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one (n.choose (k + 1)) with h2 | h2 <;> simp_all
  · have hn : ¬ (decide (n.choose k % 2 = 1) = decide (n.choose (k + 1) % 2 = 1)) := fun h => hs (hl.2 h)
    have hs' : ¬ state n (2 * (k : ℤ) + 1 - n) = true := by push_cast at hs; exact hs
    rw [if_pos (by simpa using hs'), if_neg]
    rcases Nat.mod_two_eq_zero_or_one (n.choose k) with h1 | h1 <;>
      rcases Nat.mod_two_eq_zero_or_one (n.choose (k + 1)) with h2 | h2 <;> simp_all

private lemma cc_odd (t : ℕ) : cc (2 * t + 1) = cc t := by
  unfold cc
  rw [Finset.sum_range_succ, sum2]
  rw [show 2 * t + 1 = 2 * t + 1 from rfl, luc10 t t,
    show 2 * t + 1 = 2 * t + 1 from rfl, luc11 t t, if_pos rfl, add_zero]
  apply Finset.sum_congr rfl
  intro j _
  rw [luc10, luc11, if_pos rfl, zero_add, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, luc10]

private lemma O_low (t : ℕ) : O t = ∑ j ∈ Finset.range t, (if t.choose j % 2 = 1 then 1 else 0) + 1 := by
  unfold O; rw [Finset.sum_range_succ, Nat.choose_self]; simp

private lemma O_high (t : ℕ) : O t = ∑ j ∈ Finset.range t, (if t.choose (j + 1) % 2 = 1 then 1 else 0) + 1 := by
  unfold O; rw [Finset.sum_range_succ', Nat.choose_zero_right]; simp

private lemma cc_even (t : ℕ) : cc (2 * t) + 2 = 2 * O t := by
  have h1 := O_low t
  have h2 := O_high t
  have : cc (2 * t) = ∑ j ∈ Finset.range t, (if t.choose j % 2 = 1 then 1 else 0) +
      ∑ j ∈ Finset.range t, (if t.choose (j + 1) % 2 = 1 then 1 else 0) := by
    unfold cc
    rw [sum2, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [luc00, luc01, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, luc00]
    congr 1
    · rcases Nat.mod_two_eq_zero_or_one (t.choose j) with h | h <;> simp [h]
    · rcases Nat.mod_two_eq_zero_or_one (t.choose (j + 1)) with h | h <;> simp [h]
  omega

private lemma O_succ (t : ℕ) : O (t + 1) = cc t + 2 := by
  unfold O cc
  rw [Finset.sum_range_succ', Finset.sum_range_succ, Nat.choose_self, Nat.choose_zero_right]
  have key : ∑ i ∈ Finset.range t, (if (t + 1).choose (i + 1) % 2 = 1 then 1 else 0) =
      ∑ k ∈ Finset.range t, (if t.choose k % 2 = t.choose (k + 1) % 2 then 0 else 1) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [Nat.choose_succ_succ', Nat.add_mod]
    rcases Nat.mod_two_eq_zero_or_one (t.choose j) with h | h <;>
      rcases Nat.mod_two_eq_zero_or_one (t.choose (j + 1)) with h' | h' <;> simp [h, h']
  rw [key]
  simp

private lemma O_even (t : ℕ) : O (2 * t) = O t := by
  rw [O_low (2 * t), sum2, O_low t]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [luc00, luc01]
  simp

private lemma O_odd (t : ℕ) : O (2 * t + 1) = 2 * O t := by
  unfold O
  rw [show 2 * t + 1 + 1 = 2 * (t + 1) by ring, sum2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [luc10, luc11]
  ring

private lemma pext_odd (x m : ℕ) : pext x (2 * m + 1) = x % 2 + 2 * pext (x / 2) m := by
  rw [pext, if_pos (by omega), show (2 * m + 1) / 2 = m by omega]

private lemma pext_even (x m : ℕ) (hm : 0 < m) : pext x (2 * m) = pext (x / 2) m := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * m = k + 1 := ⟨2 * m - 1, by omega⟩
  rw [hk, pext, if_neg (by omega), show (k + 1) / 2 = m by omega]

private lemma b_odd (m : ℕ) : b (2 * m + 1) = 2 * b m + 2 - (if m = 0 then 2 else 0) := by
  rw [b, if_neg (by omega), show (2 * m + 1) / 2 = m by omega]

private lemma b_even (m : ℕ) (hm : 0 < m) : b (2 * m) = b m := by
  obtain ⟨k, hk⟩ : ∃ k, 2 * m = k + 1 := ⟨2 * m - 1, by omega⟩
  rw [hk, b, if_pos (by omega), show (k + 1) / 2 = m by omega]

private lemma pextt (t : ℕ) : pext t t + 1 = O t := by
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    rcases Nat.even_or_odd' t with ⟨u, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos u with rfl | hu
      · simp [pext, O]; decide
      · rw [pext_even _ _ hu, show 2 * u / 2 = u by omega, O_even, ih u (by omega)]
    · rw [pext_odd, show (2 * u + 1) / 2 = u by omega, O_odd, ← ih u (by omega)]
      omega

private lemma b_eq (n : ℕ) : cc n = b (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
    · rcases Nat.eq_zero_or_pos t with rfl | ht
      · simp [cc, b]
      · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
        have h1 := cc_even (s + 1)
        have h2 := O_succ s
        have h3 := ih s (by omega)
        rw [b_odd, if_neg (by omega)]
        omega
    · rw [cc_odd, ih t (by omega), show 2 * t + 1 + 1 = 2 * (t + 1) by ring, b_even _ (by omega)]

private lemma pext_eq (n : ℕ) : cc n = pext n (n + 1) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.even_or_odd' n with ⟨t, rfl | rfl⟩
    · rw [pext_odd, show 2 * t / 2 = t by omega]
      have h1 := cc_even t
      have h2 := pextt t
      omega
    · rw [cc_odd, ih t (by omega), show 2 * t + 1 + 1 = 2 * (t + 1) by ring, pext_even _ _ (by omega),
        show (2 * t + 1) / 2 = t by omega]

theorem OMA.solution : type_of% @OMA.S_oeis_a071055.main :=
  ⟨fun n => by rw [a_eq, b_eq], fun n => by rw [a_eq, pext_eq]⟩
