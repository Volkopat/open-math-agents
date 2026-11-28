import OMAStatements.S_oeis_a238714

-- Problem: A238714: Final divisor of A238529(n).
-- Upstream: formal-conjectures statements/oeis-a238714.lean:0 (declaration OMA.S_oeis_a238714.main)
-- Credit: @agchua (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.
-- Idea: 2 <= sopfr r <= r for r >= 2, and r^3 <= 3^(sopfr r) (from p^3 <= 3^p). So every step
-- of the loop lowers the remainder, and the final divisor is sopfr(r) for some r >= 2 with
-- r mod sopfr(r) <= 1; sopfr(r) = 6 forces r <= 9, hence r = 8 or 9, where r mod 6 is 2 or 3.
-- Conversely a(p) = p for a prime p, a(4) = 4, and for a composite m other than 4 and 6,
-- sopfr(m) <= m - 2, so r = m * u with sopfr(u) = m - sopfr(m) (u a product of 2s and a 3)
-- has sopfr(r) = m and r mod m = 0, hence a(r) = m.

namespace H03A238714

open OMA.S_oeis_a238714

theorem cube_le (p : ℕ) : p ^ 3 ≤ 3 ^ p := by
  induction p with
  | zero => norm_num
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with h | h
    · interval_cases k <;> norm_num
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      have e : 3 * (j + 3) ^ 3 = (j + 3 + 1) ^ 3 + (2 * j ^ 3 + 15 * j ^ 2 + 33 * j + 17) := by
        ring
      have h1 : (j + 3 + 1) ^ 3 ≤ 3 * (j + 3) ^ 3 := by
        rw [e]
        exact Nat.le_add_right _ _
      calc (j + 3 + 1) ^ 3 ≤ 3 * (j + 3) ^ 3 := h1
        _ ≤ 3 * 3 ^ (j + 3) := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ (j + 3 + 1) := by ring

theorem list_cube (L : List ℕ) : L.prod ^ 3 ≤ 3 ^ L.sum := by
  induction L with
  | nil => simp
  | cons p L ih =>
    rw [List.prod_cons, List.sum_cons, mul_pow, pow_add (3 : ℕ) p L.sum]
    exact Nat.mul_le_mul (cube_le p) ih

theorem cube_sopfr (c : ℕ) : c ^ 3 ≤ 3 ^ sopfr c := by
  rcases Nat.eq_zero_or_pos c with h | h
  · subst h
    norm_num
  · have e := Nat.prod_primeFactorsList (by omega : c ≠ 0)
    have l := list_cube (Nat.primeFactorsList c)
    rw [e] at l
    exact l

theorem sopfr_two_le (p : ℕ) (hp : 2 ≤ p) : 2 ≤ sopfr p := by
  rcases Nat.lt_or_ge (sopfr p) 2 with h | h
  · exfalso
    have h1 := cube_sopfr p
    have h2 : 3 ^ sopfr p ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp 3
    have h6 : 2 ^ 3 ≤ 3 ^ 1 := le_trans h3 (le_trans h1 h2)
    norm_num at h6
  · exact h

theorem sopfr_prime (p : ℕ) (hp : p.Prime) : sopfr p = p := by
  show (Nat.primeFactorsList p).sum = p
  rw [Nat.primeFactorsList_prime hp, List.sum_singleton]

theorem sopfr_mul (x y : ℕ) (hx : x ≠ 0) (hy : y ≠ 0) : sopfr (x * y) = sopfr x + sopfr y := by
  show (Nat.primeFactorsList (x * y)).sum =
    (Nat.primeFactorsList x).sum + (Nat.primeFactorsList y).sum
  rw [(Nat.perm_primeFactorsList_mul hx hy).sum_eq, List.sum_append]

theorem sopfr_23 (i j : ℕ) : sopfr (2 ^ i * 3 ^ j) = 2 * i + 3 * j := by
  have h := Nat.perm_primeFactorsList_mul (pow_ne_zero i (by norm_num : (2 : ℕ) ≠ 0))
    (pow_ne_zero j (by norm_num : (3 : ℕ) ≠ 0))
  show (Nat.primeFactorsList (2 ^ i * 3 ^ j)).sum = 2 * i + 3 * j
  rw [h.sum_eq, List.sum_append, Nat.prime_two.primeFactorsList_pow,
    Nat.prime_three.primeFactorsList_pow, List.sum_replicate_nat, List.sum_replicate_nat]
  ring

theorem list_sum_le (L : List ℕ) (h : ∀ x ∈ L, 2 ≤ x) :
    L.sum ≤ L.prod ∧ 1 ≤ L.prod ∧ (L.prod = 1 → L.sum = 0) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    have hx : 2 ≤ x := h x (by simp)
    obtain ⟨h1, h2, h3⟩ := ih (fun y hy => h y (by simp [hy]))
    rw [List.sum_cons, List.prod_cons]
    obtain ⟨x', rfl⟩ : ∃ x', x = x' + 2 := ⟨x - 2, by omega⟩
    rcases Nat.lt_or_ge L.prod 2 with hP | hP
    · have hP1 : L.prod = 1 := by omega
      have hS : L.sum = 0 := h3 hP1
      rw [hP1, hS]
      refine ⟨by omega, by omega, fun _ => by omega⟩
    · obtain ⟨P', hP'⟩ : ∃ P', L.prod = P' + 2 := ⟨L.prod - 2, by omega⟩
      have e2 : (x' + 2) * (P' + 2) = x' * P' + 2 * x' + 2 * P' + 4 := by ring
      rw [hP', e2]
      refine ⟨by omega, by omega, fun _ => by omega⟩

theorem sopfr_le (c : ℕ) (hc : 1 ≤ c) : sopfr c ≤ c := by
  have h := list_sum_le (Nat.primeFactorsList c)
    (fun x hx => (Nat.prime_of_mem_primeFactorsList hx).two_le)
  have e := Nat.prod_primeFactorsList (by omega : c ≠ 0)
  rw [e] at h
  exact h.1

theorem six (p : ℕ) (hs : sopfr p = 6) (hm : p % 6 ≤ 1) : False := by
  have h1 := cube_sopfr p
  rw [hs] at h1
  have h9 : p ≤ 9 := by
    rcases Nat.lt_or_ge p 10 with h | h
    · omega
    · exfalso
      have h2 : 10 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left h 3
      have h3 : 10 ^ 3 ≤ 3 ^ 6 := le_trans h2 h1
      norm_num at h3
  have hp : p = 0 ∨ p = 1 ∨ p = 6 ∨ p = 7 := by omega
  rcases hp with rfl | rfl | rfl | rfl
  · simp [sopfr] at hs
  · simp [sopfr] at hs
  · have e : sopfr (2 ^ 1 * 3 ^ 1) = 2 * 1 + 3 * 1 := sopfr_23 1 1
    norm_num at e
    omega
  · have e : sopfr 7 = 7 := sopfr_prime 7 (by norm_num)
    omega

theorem final_ok (p l : ℕ) (hp : 2 ≤ p) (hl : l = sopfr p) (hr : p % l ≤ 1) :
    2 ≤ l ∧ l ≠ 6 := by
  subst hl
  constructor
  · exact sopfr_two_le p hp
  · intro h6
    rw [h6] at hr
    exact six p h6 hr

theorem G (f : ℕ) : ∀ r l : ℕ, r ≤ f → (∃ p, 2 ≤ p ∧ l = sopfr p ∧ r = p % l) →
    2 ≤ finalDiv f r l ∧ finalDiv f r l ≠ 6 := by
  induction f with
  | zero =>
    intro r l hr hex
    obtain ⟨p, hp, hl, hrl⟩ := hex
    have e : finalDiv 0 r l = l := rfl
    rw [e]
    exact final_ok p l hp hl (by omega)
  | succ f ih =>
    intro r l hr hex
    obtain ⟨p, hp, hl, hrl⟩ := hex
    by_cases h1 : r ≤ 1
    · have e : finalDiv (f + 1) r l = l := by
        show (if r ≤ 1 then l else finalDiv f (r % sopfr r) (sopfr r)) = l
        rw [if_pos h1]
      rw [e]
      exact final_ok p l hp hl (by omega)
    · have e : finalDiv (f + 1) r l = finalDiv f (r % sopfr r) (sopfr r) := by
        show (if r ≤ 1 then l else finalDiv f (r % sopfr r) (sopfr r)) = _
        rw [if_neg h1]
      rw [e]
      have hs2 := sopfr_two_le r (by omega)
      have hsl := sopfr_le r (by omega)
      have hlt := Nat.mod_lt r (by omega : sopfr r > 0)
      exact ih (r % sopfr r) (sopfr r) (by omega) ⟨r, by omega, rfl, rfl⟩

theorem exists_sopfr (d : ℕ) (hd : 2 ≤ d) : ∃ u, u ≠ 0 ∧ sopfr u = d := by
  obtain ⟨t, ht | ht⟩ : ∃ t, d = 2 * t ∨ d = 2 * t + 1 := ⟨d / 2, by omega⟩
  · refine ⟨2 ^ t * 3 ^ 0, by positivity, ?_⟩
    rw [sopfr_23]
    omega
  · obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    refine ⟨2 ^ s * 3 ^ 1, by positivity, ?_⟩
    rw [sopfr_23]
    omega

theorem composite_gap (m : ℕ) (hm : 2 ≤ m) (hp : ¬ m.Prime) (h4 : m ≠ 4) (h6 : m ≠ 6) :
    sopfr m + 2 ≤ m := by
  have hq : (Nat.minFac m).Prime := Nat.minFac_prime (by omega)
  have hq2 := hq.two_le
  obtain ⟨b, hb⟩ := Nat.minFac_dvd m
  have hsq := Nat.minFac_sq_le_self (by omega : 0 < m) hp
  have hb0 : b ≠ 0 := by
    rintro rfl
    omega
  have hsum : sopfr (Nat.minFac m * b) = Nat.minFac m + sopfr b := by
    rw [sopfr_mul (Nat.minFac m) b (by omega) hb0, sopfr_prime _ hq]
  rw [← hb] at hsum
  have hbl := sopfr_le b (by omega)
  have hqb : Nat.minFac m ≤ b := by
    have h2 : Nat.minFac m * Nat.minFac m ≤ Nat.minFac m * b := by
      rw [← pow_two, ← hb]
      exact hsq
    exact Nat.le_of_mul_le_mul_left h2 (by omega)
  obtain ⟨q', hq'⟩ : ∃ q', Nat.minFac m = q' + 2 := ⟨Nat.minFac m - 2, by omega⟩
  obtain ⟨b', hb'⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
  have e : Nat.minFac m * b = q' * b' + 2 * q' + 2 * b' + 4 := by
    rw [hq', hb']
    ring
  rcases Nat.eq_zero_or_pos q' with h0 | h0
  · subst h0
    omega
  · omega

theorem exists_r (m : ℕ) (hm : 2 ≤ m) (h6 : m ≠ 6) :
    ∃ r, 2 ≤ r ∧ sopfr r = m ∧ r % m ≤ 1 := by
  by_cases hp : m.Prime
  · exact ⟨m, hm, sopfr_prime m hp, by simp⟩
  · by_cases h4 : m = 4
    · subst h4
      refine ⟨2 ^ 2 * 3 ^ 0, by norm_num, ?_, by norm_num⟩
      exact (sopfr_23 2 0).trans (by norm_num)
    · have hg := composite_gap m hm hp h4 h6
      obtain ⟨u, hu0, hu⟩ := exists_sopfr (m - sopfr m) (by omega)
      refine ⟨m * u, ?_, ?_, ?_⟩
      · have h1 : 1 ≤ u := Nat.pos_of_ne_zero hu0
        have h2 := Nat.mul_le_mul hm h1
        omega
      · rw [sopfr_mul m u (by omega) hu0, hu]
        omega
      · simp

end H03A238714

open OMA.S_oeis_a238714 H03A238714 in
theorem OMA.solution : type_of% @OMA.S_oeis_a238714.main := by
  intro m
  constructor
  · rintro ⟨n, hn, hnm⟩
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    have e : a (k + 1) = finalDiv k ((k + 1) % sopfr (k + 1)) (sopfr (k + 1)) := by
      show (if k + 1 ≤ 1 then 0 else finalDiv k ((k + 1) % sopfr (k + 1)) (sopfr (k + 1))) = _
      rw [if_neg (show ¬ (k + 1 ≤ 1) by omega)]
    rw [e] at hnm
    have hs2 := sopfr_two_le (k + 1) hn
    have hsl := sopfr_le (k + 1) (by omega)
    have hlt := Nat.mod_lt (k + 1) (by omega : sopfr (k + 1) > 0)
    have hG := G k ((k + 1) % sopfr (k + 1)) (sopfr (k + 1)) (by omega) ⟨k + 1, hn, rfl, rfl⟩
    rw [hnm] at hG
    exact hG
  · rintro ⟨hm, h6⟩
    obtain ⟨r, hr, hs, hmod⟩ := exists_r m hm h6
    refine ⟨r, hr, ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, r = j + 2 := ⟨r - 2, by omega⟩
    show (if j + 2 ≤ 1 then 0 else
      finalDiv (j + 1) ((j + 2) % sopfr (j + 2)) (sopfr (j + 2))) = m
    rw [if_neg (show ¬ (j + 2 ≤ 1) by omega), hs]
    show (if (j + 2) % m ≤ 1 then m else
      finalDiv j ((j + 2) % m % sopfr ((j + 2) % m)) (sopfr ((j + 2) % m))) = m
    rw [if_pos hmod]
