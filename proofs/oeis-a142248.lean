import OMAStatements.S_oeis_a142248

-- Problem: A142248 (Wu's recurrence for the odd numbers in A138123).
-- A138123(n) is L((n+1)/2) for odd n, plus (-1)^((n+1)/3+1) when 3 | n+1; so its odd values are 1
-- and w(k) = L(k) - [3 | k] for k >= 2, which increase for k >= 3 (w(2) = w(3) = 3). Hence
-- a(n) = w(n+1) for n >= 2, and the Lucas recurrence plus the 3-periodicity give the recurrence.
-- Credit: @bnb9001

namespace OMA_A142248_Proof

open OMA.S_oeis_a142248

open Finset

theorem T_eq (n m : ℕ) (hm1 : 1 ≤ m) (hmn : m ≤ n) :
    T (n + 1 - m) m = (if 2 * m = n + 1 then (L m : ℤ) else 0) +
      (if 3 * m = 2 * (n + 1) then (-1) ^ (n + 1 - m + 1) else 0) := by
  unfold T
  by_cases h1 : 2 * m = n + 1
  · have e : m = n + 1 - m := by omega
    rw [if_pos e, if_pos h1, if_neg (by omega : ¬ 3 * m = 2 * (n + 1)), ← e, add_zero]
  · rw [if_neg (by omega : ¬ m = n + 1 - m), if_neg h1, zero_add]
    by_cases h2 : 3 * m = 2 * (n + 1)
    · rw [if_pos (by omega : m = 2 * (n + 1 - m)), if_pos h2]
    · rw [if_neg (by omega : ¬ m = 2 * (n + 1 - m)), if_neg h2]

theorem A_eq (n : ℕ) : A138123 n =
    (if (n + 1) % 2 = 0 then (L ((n + 1) / 2) : ℤ) else 0) +
      (if (n + 1) % 3 = 0 then (-1) ^ ((n + 1) / 3 + 1) else 0) := by
  unfold A138123
  rw [Finset.sum_congr rfl (fun m hm => T_eq n m (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hm).2),
    Finset.sum_add_distrib]
  congr 1
  · split_ifs with h
    · rw [Finset.sum_eq_single ((n + 1) / 2)]
      · rw [if_pos (by omega)]
      · intro b _ hb; rw [if_neg (by omega)]
      · intro hn; exfalso; apply hn; rw [Finset.mem_Icc]; omega
    · apply Finset.sum_eq_zero; intro m _; rw [if_neg (by omega)]
  · split_ifs with h
    · rw [Finset.sum_eq_single (2 * (n + 1) / 3)]
      · rw [if_pos (by omega)]; congr 1; omega
      · intro b _ hb; rw [if_neg (by omega)]
      · intro hn; exfalso; apply hn; rw [Finset.mem_Icc]; omega
    · apply Finset.sum_eq_zero; intro m _; rw [if_neg (by omega)]

theorem L_rec (k : ℕ) (hk : 1 ≤ k) : L (k + 2) = L (k + 1) + L k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  show Nat.fib (j + 4) + Nat.fib (j + 2) = (Nat.fib (j + 3) + Nat.fib (j + 1)) + (Nat.fib (j + 2) + Nat.fib j)
  rw [show j + 4 = (j + 2) + 2 by ring, Nat.fib_add_two, show j + 2 + 1 = j + 3 by ring,
    show j + 2 = j + 2 from rfl, Nat.fib_add_two (n := j)]
  ring

theorem L_two_le (k : ℕ) (hk : 2 ≤ k) : 2 ≤ L k := by
  unfold L
  have : Nat.fib 3 ≤ Nat.fib (k + 1) := Nat.fib_mono (by omega)
  have h3 : Nat.fib 3 = 2 := by decide
  omega

theorem L_one : L 1 = 1 := by decide

theorem L_mod (k : ℕ) (hk : 1 ≤ k) : L k % 2 = if k % 3 = 0 then 0 else 1 := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    rcases (show k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k by omega) with h | h | h | h
    · subst h; decide
    · subst h; decide
    · subst h; decide
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
      have e : L (j + 3) = 2 * L (j + 1) + L j := by
        rw [show j + 3 = (j + 1) + 2 by ring, L_rec (j + 1) (by omega), show j + 1 + 1 = j + 2 by ring,
          L_rec j (by omega)]
        ring
      rw [e, show (j + 3) % 3 = j % 3 by omega, ← ih j (by omega) (by omega)]
      omega

/-- the values `w(k) = L(k) - [3 | k]` -/
def w (k : ℕ) : ℕ := L k - if k % 3 = 0 then 1 else 0

theorem w_cast (k : ℕ) (hk : 1 ≤ k) :
    (w k : ℤ) = (L k : ℤ) - (if k % 3 = 0 then 1 else 0) := by
  unfold w
  have : 1 ≤ L k := by
    rcases (show k = 1 ∨ 2 ≤ k by omega) with h | h
    · subst h; decide
    · have := L_two_le k h; omega
  split_ifs
  · push_cast [Nat.cast_sub this]; ring
  · simp

theorem w_odd (k : ℕ) (hk : 1 ≤ k) : Odd (w k) := by
  have hm := L_mod k hk
  have : 1 ≤ L k := by
    rcases (show k = 1 ∨ 2 ≤ k by omega) with h | h
    · subst h; decide
    · have := L_two_le k h; omega
  rw [Nat.odd_iff]; unfold w
  split_ifs at hm ⊢ <;> omega

theorem neg_one_pow_odd (n : ℕ) (h2 : (n + 1) % 2 = 0) (h3 : (n + 1) % 3 = 0) :
    ((-1 : ℤ)) ^ ((n + 1) / 3 + 1) = -1 := by
  rw [show (n + 1) / 3 + 1 = 2 * ((n + 1) / 6) + 1 by omega, pow_succ, pow_mul]; norm_num

theorem isTerm_iff (v : ℕ) : IsTerm v ↔ v = 1 ∨ ∃ k, 2 ≤ k ∧ v = w k := by
  constructor
  · rintro ⟨hodd, n, hn, hA⟩
    rw [A_eq] at hA
    by_cases h2 : (n + 1) % 2 = 0
    · rw [if_pos h2] at hA
      set k := (n + 1) / 2 with hk
      have hk1 : 1 ≤ k := by omega
      have hv : v = w k := by
        have := w_cast k hk1
        by_cases h3 : (n + 1) % 3 = 0
        · rw [if_pos h3, neg_one_pow_odd n h2 h3] at hA
          rw [if_pos (by omega : k % 3 = 0)] at this
          omega
        · rw [if_neg h3] at hA
          rw [if_neg (by omega : ¬ k % 3 = 0)] at this
          omega
      rcases (show k = 1 ∨ 2 ≤ k by omega) with h | h
      · left; rw [hv, h]; decide
      · exact Or.inr ⟨k, h, hv⟩
    · rw [if_neg h2, zero_add] at hA
      left
      split_ifs at hA with h3
      · rcases neg_one_pow_eq_or ℤ ((n + 1) / 3 + 1) with h | h
        · rw [h] at hA; exact_mod_cast hA.symm
        · rw [h] at hA; omega
      · have : v = 0 := by exact_mod_cast hA.symm
        rw [this] at hodd; exact absurd hodd (by decide)
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · refine ⟨by decide, 1, le_rfl, ?_⟩
      rw [A_eq]; norm_num [L_one]
    · refine ⟨w_odd k (by omega), 2 * k - 1, by omega, ?_⟩
      rw [A_eq, show 2 * k - 1 + 1 = 2 * k by omega, if_pos (by omega),
        show 2 * k / 2 = k by omega, w_cast k (by omega)]
      by_cases h3 : k % 3 = 0
      · rw [if_pos (by omega : 2 * k % 3 = 0), if_pos h3,
          show 2 * k / 3 + 1 = 2 * (k / 3) + 1 by omega, pow_succ, pow_mul]
        norm_num; ring
      · rw [if_neg (by omega : ¬ 2 * k % 3 = 0), if_neg h3]; ring

/-- the terms in increasing order -/
def g : ℕ → ℕ
  | 0 => 1
  | j + 1 => w (j + 3)

theorem g_strictMono : StrictMono g := by
  apply strictMono_nat_of_lt_succ
  intro j
  rcases j with _ | j
  · show 1 < w 3; decide
  · show w (j + 3) < w (j + 4)
    have e := L_rec (j + 2) (by omega)
    rw [show j + 2 + 2 = j + 4 by ring, show j + 2 + 1 = j + 3 by ring] at e
    have h2 := L_two_le (j + 2) (by omega)
    unfold w
    split_ifs <;> omega

theorem isTerm_iff_range (v : ℕ) : IsTerm v ↔ ∃ j, g j = v := by
  rw [isTerm_iff]
  constructor
  · rintro (rfl | ⟨k, hk, rfl⟩)
    · exact ⟨0, rfl⟩
    · rcases (show k = 2 ∨ 3 ≤ k by omega) with h | h
      · subst h; exact ⟨1, by decide⟩
      · exact ⟨k - 2, by
          obtain ⟨j, rfl⟩ : ∃ j, k = j + 3 := ⟨k - 3, by omega⟩
          rw [show j + 3 - 2 = j + 1 by omega]; rfl⟩
  · rintro ⟨j, rfl⟩
    rcases j with _ | j
    · left; rfl
    · right; exact ⟨j + 3, by omega, rfl⟩

theorem nth_eq (j : ℕ) : Nat.nth IsTerm j = g j := by
  classical
  have hp : IsTerm (g j) := (isTerm_iff_range _).mpr ⟨j, rfl⟩
  have hc : Nat.count IsTerm (g j) = j := by
    rw [Nat.count_eq_card_filter_range]
    have : (range (g j)).filter IsTerm = (range j).image g := by
      ext v
      simp only [mem_filter, mem_range, mem_image]
      constructor
      · rintro ⟨hv, ht⟩
        obtain ⟨i, rfl⟩ := (isTerm_iff_range v).mp ht
        exact ⟨i, g_strictMono.lt_iff_lt.mp hv, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨g_strictMono hi, (isTerm_iff_range _).mpr ⟨i, rfl⟩⟩
    rw [this, card_image_of_injective _ g_strictMono.injective, card_range]
  have := Nat.nth_count hp
  rwa [hc] at this

theorem a_eq (n : ℕ) (hn : 2 ≤ n) : a n = w (n + 1) := by
  unfold a
  rw [nth_eq]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  rw [show j + 2 - 1 = j + 1 by omega]
  rfl

theorem stmt' : ∀ n : ℕ, 6 < n →
    (a n : ℤ) = a (n - 1) + a (n - 2) + a (n - 3) - a (n - 4) - a (n - 5) := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 7 := ⟨n - 7, by omega⟩
  rw [show m + 7 - 1 = m + 6 by omega, show m + 7 - 2 = m + 5 by omega,
    show m + 7 - 3 = m + 4 by omega, show m + 7 - 4 = m + 3 by omega,
    show m + 7 - 5 = m + 2 by omega]
  rw [a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega), a_eq _ (by omega),
    a_eq _ (by omega)]
  rw [w_cast _ (by omega), w_cast _ (by omega), w_cast _ (by omega), w_cast _ (by omega),
    w_cast _ (by omega), w_cast _ (by omega)]
  have e1 := L_rec (m + 6) (by omega)
  have e2 := L_rec (m + 3) (by omega)
  rw [show m + 6 + 2 = m + 7 + 1 by ring, show m + 6 + 1 = m + 6 + 1 from rfl] at e1
  rw [show (m + 7 + 1) % 3 = (m + 4 + 1) % 3 by omega, show (m + 6 + 1) % 3 = (m + 3 + 1) % 3 by omega,
    show (m + 5 + 1) % 3 = (m + 2 + 1) % 3 by omega]
  have c1 : ((L (m + 7 + 1) : ℕ) : ℤ) = L (m + 6 + 1) + L (m + 5 + 1) := by
    rw [show m + 7 + 1 = m + 6 + 2 by ring, L_rec (m + 6) (by omega)]; push_cast; ring_nf
  have c2 : ((L (m + 4 + 1) : ℕ) : ℤ) = L (m + 3 + 1) + L (m + 2 + 1) := by
    rw [show m + 4 + 1 = m + 3 + 2 by ring, L_rec (m + 3) (by omega)]; push_cast; ring_nf
  rw [c1, c2]
  ring

end OMA_A142248_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a142248.main := OMA_A142248_Proof.stmt'
