import OMAStatements.S_oeis_a153772
import Mathlib

namespace A153772H

open OMA.S_oeis_a153772

def Dp (m d : ℕ) : Prop := collatz^[d] m = 1 ∧ ∀ k < d, collatz^[k] m ≠ 1

theorem collatz_even (m : ℕ) : collatz (2 * m) = m := by
  unfold collatz
  rw [if_pos (by omega)]
  omega

theorem collatz_odd (m : ℕ) (h : m % 2 = 1) : collatz m = 3 * m + 1 := by
  unfold collatz
  rw [if_neg (by omega)]

theorem Dp_zero (m : ℕ) : Dp m 0 ↔ m = 1 := by
  simp [Dp]

theorem Dp_succ (m d : ℕ) : Dp m (d + 1) ↔ m ≠ 1 ∧ Dp (collatz m) d := by
  unfold Dp
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun h => h2 0 (Nat.succ_pos _) (by simpa using h), ?_, ?_⟩
    · rwa [Function.iterate_succ_apply] at h1
    · intro k hk
      have := h2 (k + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this
  · rintro ⟨h0, h1, h2⟩
    refine ⟨by rwa [Function.iterate_succ_apply], ?_⟩
    intro k hk
    rcases k with _ | k
    · simpa using h0
    · rw [Function.iterate_succ_apply]
      exact h2 k (by omega)

theorem Dp_pow (t : ℕ) : Dp (2 ^ t) t := by
  induction t with
  | zero => simp [Dp_zero]
  | succ t ih =>
    rw [Dp_succ]
    refine ⟨?_, ?_⟩
    · rw [pow_succ]; omega
    · rw [pow_succ, mul_comm, collatz_even]; exact ih

theorem Dp_double (m d : ℕ) (h : Dp m d) : Dp (2 * m) (d + 1) := by
  rw [Dp_succ]
  exact ⟨by omega, by rw [collatz_even]; exact h⟩

theorem Dp_odd (m d : ℕ) (hm : m % 2 = 1) (h1 : m ≠ 1) (h : Dp (3 * m + 1) d) :
    Dp m (d + 1) := by
  rw [Dp_succ]
  exact ⟨h1, by rw [collatz_odd m hm]; exact h⟩

theorem Dp_Q (d : ℕ) : ∀ m : ℕ, Dp m d →
    m = 2 ^ d ∨ (∃ i : ℕ, 6 * m + 2 ^ (i + 1) = 2 ^ d) ∨ 36 * m + 4 ≤ 2 ^ d := by
  induction d with
  | zero =>
    intro m hm
    left
    rw [Dp_zero] at hm
    simp [hm]
  | succ d ih =>
    intro m hm
    rw [Dp_succ] at hm
    obtain ⟨hm1, hm2⟩ := hm
    have hp : 2 ^ (d + 1) = 2 ^ d * 2 := pow_succ 2 d
    rcases Nat.mod_two_eq_zero_or_one m with he | ho
    · have hc : collatz m = m / 2 := by
        have : m = 2 * (m / 2) := by omega
        rw [this, collatz_even]; omega
      rw [hc] at hm2
      rcases ih (m / 2) hm2 with h | ⟨i, hi⟩ | h
      · left; omega
      · right; left
        refine ⟨i + 1, ?_⟩
        rw [pow_succ 2 (i + 1)]
        omega
      · right; right; omega
    · rw [collatz_odd m ho] at hm2
      rcases ih (3 * m + 1) hm2 with h | ⟨i, hi⟩ | h
      · right; left
        exact ⟨0, by simp only [zero_add, pow_one]; omega⟩
      · right; right
        have h2 : 6 * (3 * m + 1) ≤ 2 ^ d := Nat.le.intro hi
        omega
      · right; right; omega

theorem pow_mod3 (k : ℕ) : 2 ^ (2 * k + 4) % 3 = 1 := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have : 2 ^ (2 * (k + 1) + 4) = 4 * 2 ^ (2 * k + 4) := by
      rw [show 2 * (k + 1) + 4 = (2 * k + 4) + 2 by ring, pow_add]; ring
    omega

theorem mem_S_iff (m d : ℕ) : m ∈ S (d + 1) ↔ 1 ≤ m ∧ Dp m d := by
  simp [S, OrbitLength, Dp]

theorem main_even (k : ℕ) : ∃ m : ℕ, (m : ℤ) = a (2 * k + 6) ∧ m ∈ S (2 * k + 6 + 2) ∧
    {x : ℕ | x ∈ S (2 * k + 6 + 2) ∧ m < x}.ncard = 2 := by
  have hmod := pow_mod3 k
  obtain ⟨u, hu⟩ : ∃ u, 3 * u + 1 = 2 ^ (2 * k + 4) := ⟨2 ^ (2 * k + 4) / 3, by
    have h := Nat.div_add_mod (2 ^ (2 * k + 4)) 3
    rw [hmod] at h
    exact h⟩
  have h16 : 2 ^ (2 * k + 4) = 16 * 2 ^ (2 * k) := by rw [pow_add]; ring
  have hpos : 0 < 2 ^ (2 * k) := pow_pos (by norm_num) _
  have hu5 : 5 ≤ u := by omega
  have huodd : u % 2 = 1 := by omega
  have h6 : 2 ^ (2 * k + 6) = 12 * u + 4 := by
    rw [show 2 * k + 6 = (2 * k + 4) + 2 by ring, pow_add, ← hu]; ring
  have h7 : 2 ^ (2 * k + 7) = 24 * u + 8 := by
    rw [show 2 * k + 7 = (2 * k + 4) + 3 by ring, pow_add, ← hu]; ring
  have Du : Dp u (2 * k + 5) := by
    apply Dp_odd u _ huodd (by omega)
    rw [hu]; exact Dp_pow _
  have D3 : Dp (4 * u) (2 * k + 7) := by
    have := Dp_double _ _ (Dp_double _ _ Du)
    rw [show 2 * (2 * u) = 4 * u by ring] at this
    exact this
  have D2 : Dp (4 * u + 1) (2 * k + 7) := by
    apply Dp_odd _ _ (by omega) (by omega)
    rw [show 3 * (4 * u + 1) + 1 = 12 * u + 4 by ring, ← h6]; exact Dp_pow _
  have D1 : Dp (24 * u + 8) (2 * k + 7) := by
    rw [← h7]; exact Dp_pow _
  have hL : 2 * k + 6 + 2 = (2 * k + 7) + 1 := by ring
  refine ⟨4 * u, ?_, ?_, ?_⟩
  · have hX : (2 : ℤ) ^ (2 * k + 6) = 12 * (u : ℤ) + 4 := by exact_mod_cast h6
    have hn : ((-1 : ℤ)) ^ (2 * k + 6) = 1 := Even.neg_one_pow ⟨k + 3, by ring⟩
    simp only [a]
    rw [hX, hn]
    push_cast
    omega
  · rw [hL, mem_S_iff]; exact ⟨by omega, D3⟩
  · have hset : {x : ℕ | x ∈ S (2 * k + 6 + 2) ∧ 4 * u < x} = {24 * u + 8, 4 * u + 1} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [hL, mem_S_iff]
      constructor
      · rintro ⟨⟨_, hx⟩, hlt⟩
        rcases Dp_Q _ x hx with h | ⟨i, hi⟩ | h
        · left; omega
        · right
          have : 0 < 2 ^ (i + 1) := pow_pos (by norm_num) _
          omega
        · exfalso; omega
      · rintro (rfl | rfl)
        · exact ⟨⟨by omega, D1⟩, by omega⟩
        · exact ⟨⟨by omega, D2⟩, by omega⟩
    rw [hset]
    exact Set.ncard_pair (by omega)

theorem main_odd (k : ℕ) : ∃ m : ℕ, (m : ℤ) = a (2 * k + 7) ∧ m ∈ S (2 * k + 7 + 2) ∧
    {x : ℕ | x ∈ S (2 * k + 7 + 2) ∧ m < x}.ncard = 2 := by
  have hmod := pow_mod3 k
  obtain ⟨u, hu⟩ : ∃ u, 3 * u + 1 = 2 ^ (2 * k + 4) := ⟨2 ^ (2 * k + 4) / 3, by
    have h := Nat.div_add_mod (2 ^ (2 * k + 4)) 3
    rw [hmod] at h
    exact h⟩
  have h16 : 2 ^ (2 * k + 4) = 16 * 2 ^ (2 * k) := by rw [pow_add]; ring
  have hpos : 0 < 2 ^ (2 * k) := pow_pos (by norm_num) _
  have hu5 : 5 ≤ u := by omega
  have huodd : u % 2 = 1 := by omega
  have h6 : 2 ^ (2 * k + 6) = 12 * u + 4 := by
    rw [show 2 * k + 6 = (2 * k + 4) + 2 by ring, pow_add, ← hu]; ring
  have h7 : 2 ^ (2 * k + 7) = 24 * u + 8 := by
    rw [show 2 * k + 7 = (2 * k + 4) + 3 by ring, pow_add, ← hu]; ring
  have h8 : 2 ^ (2 * k + 8) = 48 * u + 16 := by
    rw [show 2 * k + 8 = (2 * k + 4) + 4 by ring, pow_add, ← hu]; ring
  have Du : Dp u (2 * k + 5) := by
    apply Dp_odd u _ huodd (by omega)
    rw [hu]; exact Dp_pow _
  have D4 : Dp (4 * u) (2 * k + 7) := by
    have := Dp_double _ _ (Dp_double _ _ Du)
    rw [show 2 * (2 * u) = 4 * u by ring] at this
    exact this
  have D3 : Dp (8 * u) (2 * k + 8) := by
    have := Dp_double _ _ D4
    rw [show 2 * (4 * u) = 8 * u by ring] at this
    exact this
  have D41 : Dp (4 * u + 1) (2 * k + 7) := by
    apply Dp_odd _ _ (by omega) (by omega)
    rw [show 3 * (4 * u + 1) + 1 = 12 * u + 4 by ring, ← h6]; exact Dp_pow _
  have D2 : Dp (8 * u + 2) (2 * k + 8) := by
    have := Dp_double _ _ D41
    rw [show 2 * (4 * u + 1) = 8 * u + 2 by ring] at this
    exact this
  have D1 : Dp (48 * u + 16) (2 * k + 8) := by
    rw [← h8]; exact Dp_pow _
  have hL : 2 * k + 7 + 2 = (2 * k + 8) + 1 := by ring
  refine ⟨8 * u, ?_, ?_, ?_⟩
  · have hX : (2 : ℤ) ^ (2 * k + 7) = 24 * (u : ℤ) + 8 := by exact_mod_cast h7
    have hn : ((-1 : ℤ)) ^ (2 * k + 7) = -1 := Odd.neg_one_pow ⟨k + 3, by ring⟩
    simp only [a]
    rw [hX, hn]
    push_cast
    omega
  · rw [hL, mem_S_iff]; exact ⟨by omega, D3⟩
  · have hset : {x : ℕ | x ∈ S (2 * k + 7 + 2) ∧ 8 * u < x} = {48 * u + 16, 8 * u + 2} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
      rw [hL, mem_S_iff]
      constructor
      · rintro ⟨⟨_, hx⟩, hlt⟩
        rcases Dp_Q _ x hx with h | ⟨i, hi⟩ | h
        · left; omega
        · right
          have hp1 : 2 ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
          have key : 2 ^ i = 1 ∨ 2 ^ i = 2 ∨ ∃ w, 2 ^ i = 4 * w := by
            rcases i with _ | _ | j
            · left; norm_num
            · right; left; norm_num
            · right; right; exact ⟨2 ^ j, by ring⟩
          rcases key with h1 | h2 | ⟨w, hw⟩ <;> omega
        · exfalso; omega
      · rintro (rfl | rfl)
        · exact ⟨⟨by omega, D1⟩, by omega⟩
        · exact ⟨⟨by omega, D2⟩, by omega⟩
    rw [hset]
    exact Set.ncard_pair (by omega)

end A153772H

theorem OMA.solution : type_of% @OMA.S_oeis_a153772.main := by
  intro n hn
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 6 ∨ n = 2 * k + 7 := ⟨(n - 6) / 2, by omega⟩
  · exact A153772H.main_even k
  · exact A153772H.main_odd k
