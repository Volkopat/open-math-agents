import OMAReductions.R_GoldbachConjecture_goldbach_R1

-- Goldbach's conjecture for even n with 2 < n <= 10000.
-- isP is a trial-division primality test proved sound against Nat.Prime (tdiv_spec); gold searches for a prime
-- p with n - p prime; goldAll runs the search over a block of consecutive even numbers, and the kernel
-- evaluates ten blocks of 500 (decide +kernel).
-- A verified numerical range only, tiny compared with the published verification up to 4 * 10^18; not progress
-- on the conjecture.

namespace OMA.PS

/-- Trial division with fuel: `q` has no divisor `m` with `d ≤ m` and `m * m ≤ q`. -/
def tdiv : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, d, q => if q < d * d then true else if q % d = 0 then false else tdiv f (d + 1) q

theorem tdiv_spec : ∀ (f d q : ℕ), tdiv f d q = true → 2 ≤ q →
    (∀ m, 2 ≤ m → m < d → ¬ m ∣ q) → q.Prime := by
  intro f
  induction f with
  | zero =>
    intro d q h
    simp [tdiv] at h
  | succ f ih =>
    intro d q h hq hm
    rw [tdiv] at h
    split_ifs at h with h1 h2
    · rw [Nat.prime_def_le_sqrt]
      refine ⟨hq, fun m hm1 hm2 => hm m hm1 ?_⟩
      have h3 : m * m ≤ q := Nat.le_sqrt.mp hm2
      by_contra hc
      have hc' : d ≤ m := Nat.le_of_not_lt hc
      have h4 : d * d ≤ m * m := Nat.mul_le_mul hc' hc'
      omega
    · refine ih (d + 1) q h hq (fun m hm1 hm2 => ?_)
      rcases Nat.lt_succ_iff_lt_or_eq.mp hm2 with hlt | rfl
      · exact hm m hm1 hlt
      · intro hdvd
        exact h2 (Nat.mod_eq_zero_of_dvd hdvd)

/-- A kernel-friendly primality test. -/
def isP (q : ℕ) : Bool := decide (2 ≤ q) && tdiv q 2 q

theorem isP_spec (q : ℕ) (h : isP q = true) : q.Prime := by
  rw [isP, Bool.and_eq_true, decide_eq_true_eq] at h
  exact tdiv_spec q 2 q h.2 h.1 (fun m h1 h2 => by omega)

end OMA.PS

namespace OMA.Gold

open OMA.PS

/-- Search for a prime `p' ≥ p` (within fuel) with `n - p'` prime. -/
def gold : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, p, n => (decide (p ≤ n) && isP p && isP (n - p)) || gold f (p + 1) n

theorem gold_spec : ∀ (f p n : ℕ), gold f p n = true → ∃ a b, a.Prime ∧ b.Prime ∧ n = a + b := by
  intro f
  induction f with
  | zero =>
    intro p n h
    simp [gold] at h
  | succ f ih =>
    intro p n h
    rw [gold, Bool.or_eq_true] at h
    rcases h with h | h
    · rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨p, n - p, isP_spec p h.1.2, isP_spec (n - p) h.2, by omega⟩
    · exact ih (p + 1) n h

/-- All of `n, n + 2, ..., n + 2 (c - 1)` pass the search. -/
def goldAll : ℕ → ℕ → Bool
  | 0, _ => true
  | c + 1, n => gold 400 2 n && goldAll c (n + 2)

theorem goldAll_spec : ∀ (c n : ℕ), goldAll c n = true → ∀ i, i < c →
    ∃ a b, a.Prime ∧ b.Prime ∧ n + 2 * i = a + b := by
  intro c
  induction c with
  | zero =>
    intro n _ i hi
    omega
  | succ c ih =>
    intro n h i hi
    rw [goldAll, Bool.and_eq_true] at h
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · exact gold_spec 400 2 n h.1
    · obtain ⟨a, b, ha, hb, hab⟩ := ih (n + 2) h.2 (i - 1) (by omega)
      exact ⟨a, b, ha, hb, by omega⟩

set_option maxRecDepth 100000 in
theorem t0 : goldAll 500 4 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t1 : goldAll 500 1004 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t2 : goldAll 500 2004 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t3 : goldAll 500 3004 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t4 : goldAll 500 4004 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t5 : goldAll 500 5004 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t6 : goldAll 500 6004 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t7 : goldAll 500 7004 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t8 : goldAll 500 8004 = true := by decide +kernel
set_option maxRecDepth 100000 in
theorem t9 : goldAll 499 9004 = true := by decide +kernel

theorem range (n : ℕ) (h2 : 2 < n) (he : Even n) (hN : n ≤ 10000) :
    ∃ a b, a.Prime ∧ b.Prime ∧ n = a + b := by
  obtain ⟨m, hm⟩ := he
  have hi : ∃ i, n = 4 + 2 * i := ⟨m - 2, by omega⟩
  obtain ⟨i, rfl⟩ := hi
  by_cases g0 : i < 500
  · obtain ⟨a, b, ha, hb, hab⟩ := goldAll_spec _ _ t0 (i - 0) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g1 : i < 1000
  · obtain ⟨a, b, ha, hb, hab⟩ := goldAll_spec _ _ t1 (i - 500) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g2 : i < 1500
  · obtain ⟨a, b, ha, hb, hab⟩ := goldAll_spec _ _ t2 (i - 1000) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g3 : i < 2000
  · obtain ⟨a, b, ha, hb, hab⟩ := goldAll_spec _ _ t3 (i - 1500) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g4 : i < 2500
  · obtain ⟨a, b, ha, hb, hab⟩ := goldAll_spec _ _ t4 (i - 2000) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g5 : i < 3000
  · obtain ⟨a, b, ha, hb, hab⟩ := goldAll_spec _ _ t5 (i - 2500) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g6 : i < 3500
  · obtain ⟨a, b, ha, hb, hab⟩ := goldAll_spec _ _ t6 (i - 3000) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g7 : i < 4000
  · obtain ⟨a, b, ha, hb, hab⟩ := goldAll_spec _ _ t7 (i - 3500) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  by_cases g8 : i < 4500
  · obtain ⟨a, b, ha, hb, hab⟩ := goldAll_spec _ _ t8 (i - 4000) (by omega)
    exact ⟨a, b, ha, hb, by omega⟩
  obtain ⟨a, b, ha, hb, hab⟩ := goldAll_spec _ _ t9 (i - 4500) (by omega)
  exact ⟨a, b, ha, hb, by omega⟩

end OMA.Gold

theorem OMA.solution : OMA.R_GoldbachConjecture_goldbach_R1.H1 := by
  intro n hn he hN
  obtain ⟨a, b, ha, hb, hab⟩ := OMA.Gold.range n hn he hN
  exact ⟨a, b, Nat.prime_iff.mp ha, Nat.prime_iff.mp hb, hab⟩
