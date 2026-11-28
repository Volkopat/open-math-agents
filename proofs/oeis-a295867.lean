import OMAStatements.S_oeis_a295867

-- Problem: A295867, Colin Barker's order-16 recurrence.
-- Credit: @ShoQo
-- Proof: with b(n) = A000217(n) A007494(n), b(2j) = 3 j^2 (2j+1) and b(2j+1) = (j+1)(2j+1)(3j+2),
-- so b is strictly increasing and 3 ∣ b(n) exactly when n ≢ 1 (mod 6). Hence the terms are
-- a(m) = b(h(m)) with h(m) = 6⌊m/5⌋ + (0, 2, 3, 4, 5)[m mod 5], by the
-- uniqueness of `Nat.nth` as the strictly increasing enumeration. For each residue s, a(5q + s)
-- is an explicit cubic in q, and the recurrence is checked residue by residue.

open OMA.S_oeis_a295867

namespace OMA_A295867_Proof

def b (n : ℕ) : ℕ := A000217 n * A007494 n

def H (s : ℕ) : ℕ := if s = 0 then 0 else s + 1

def h (m : ℕ) : ℕ := 6 * (m / 5) + H (m % 5)

lemma b_even (j : ℕ) : b (2 * j) = 3 * j * j * (2 * j + 1) := by
  have h1 : A000217 (2 * j) = j * (2 * j + 1) := by
    unfold A000217
    rw [show 2 * j * (2 * j + 1) = 2 * (j * (2 * j + 1)) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have h2 : A007494 (2 * j) = 3 * j := by unfold A007494; omega
  rw [b, h1, h2]; ring

lemma b_odd (j : ℕ) : b (2 * j + 1) = (j + 1) * (2 * j + 1) * (3 * j + 2) := by
  have h1 : A000217 (2 * j + 1) = (j + 1) * (2 * j + 1) := by
    unfold A000217
    rw [show (2 * j + 1) * (2 * j + 1 + 1) = 2 * ((j + 1) * (2 * j + 1)) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have h2 : A007494 (2 * j + 1) = 3 * j + 2 := by unfold A007494; omega
  rw [b, h1, h2]

lemma b_strictMono : StrictMono b := by
  apply strictMono_nat_of_lt_succ
  intro n
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [b_even, b_odd]; nlinarith
  · rw [b_odd, show 2 * j + 1 + 1 = 2 * (j + 1) by ring, b_even]; nlinarith

lemma three_dvd_b (n : ℕ) : 3 ∣ b n ↔ n % 6 ≠ 1 := by
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [b_even]
    exact ⟨fun _ => by omega, fun _ => ⟨j * j * (2 * j + 1), by ring⟩⟩
  · rw [b_odd]
    have p3 : Nat.Prime 3 := by norm_num
    constructor
    · intro hd
      rcases (p3.dvd_mul.1 hd) with hd | hd
      · rcases (p3.dvd_mul.1 hd) with hd | hd <;> omega
      · omega
    · intro hn
      have hj : j % 3 = 2 ∨ j % 3 = 1 := by omega
      have : 3 ∣ (j + 1) ∨ 3 ∣ (2 * j + 1) := by
        rcases hj with hj | hj
        · exact Or.inl (Nat.dvd_of_mod_eq_zero (by omega))
        · exact Or.inr (Nat.dvd_of_mod_eq_zero (by omega))
      rcases this with hd | hd
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_right hd _) _
      · exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hd _) _

lemma h_succ_lt (m : ℕ) : h m < h (m + 1) := by
  unfold h H; split_ifs <;> omega

lemma h_strictMono : StrictMono h := strictMono_nat_of_lt_succ h_succ_lt

lemma h_range (n : ℕ) : n % 6 ≠ 1 ↔ ∃ m, h m = n := by
  constructor
  · intro h1
    refine ⟨5 * (n / 6) + (if n % 6 = 0 then 0 else n % 6 - 1), ?_⟩
    unfold h H; split_ifs <;> omega
  · rintro ⟨m, rfl⟩
    unfold h H; split_ifs <;> omega

/-- The enumeration. -/
def g (k : ℕ) : ℕ := b (h k)

lemma g_strictMono : StrictMono g := fun _ _ hxy => b_strictMono (h_strictMono hxy)

lemma P_iff (x : ℕ) : P x ↔ ∃ k, g k = x := by
  constructor
  · rintro ⟨hx3, n, rfl⟩
    have hb : b n = A000217 n * A007494 n := rfl
    rw [← hb] at hx3 ⊢
    obtain ⟨m, rfl⟩ := (h_range n).1 ((three_dvd_b n).1 hx3)
    exact ⟨m, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(three_dvd_b _).2 ((h_range (h k)).2 ⟨k, rfl⟩), h k, rfl⟩

lemma P_infinite : (Set.ofPred P).Infinite := by
  have : Set.ofPred P = Set.range g := by
    ext x; exact (P_iff x).trans (by simp [Set.mem_range])
  rw [this]
  exact Set.infinite_range_of_injective g_strictMono.injective

lemma a_eq (k : ℕ) : a k = b (h k) := by
  have hdom : ∀ n : ℕ, n ∈ { n : ℕ | ∀ hf : Set.Finite (Set.ofPred P), n < hf.toFinset.card } :=
    fun n hf => absurd hf P_infinite
  refine (Nat.eq_nth_of_strictMonoOn_of_mapsTo_of_surjOn g ?_ ?_ ?_ (hdom k)).symm
  · intro x hx
    obtain ⟨k, rfl⟩ := (P_iff x).1 hx
    exact ⟨k, hdom k, rfl⟩
  · intro k _
    exact (P_iff _).2 ⟨k, rfl⟩
  · intro x _ y _ hxy
    exact g_strictMono hxy

/-- a(5q + s) as an explicit cubic in q. -/
def V (q s : ℕ) : ℤ :=
  if s = 0 then 27 * q * q * (6 * q + 1)
  else if s = 1 then 3 * (3 * q + 1) * (3 * q + 1) * (6 * q + 3)
  else if s = 2 then (3 * q + 2) * (6 * q + 3) * (9 * q + 5)
  else if s = 3 then 3 * (3 * q + 2) * (3 * q + 2) * (6 * q + 5)
  else (3 * q + 3) * (6 * q + 5) * (9 * q + 8)

lemma aV (q s : ℕ) (hs : s < 5) : (a (5 * q + s) : ℤ) = V q s := by
  rw [a_eq]
  have hh : h (5 * q + s) = 6 * q + H s := by
    unfold h; congr 2 <;> omega
  rw [hh]
  interval_cases s <;> simp only [H, V] <;> norm_num
  · rw [show 6 * q = 2 * (3 * q) by ring, b_even]; push_cast; ring
  · rw [show 6 * q + 2 = 2 * (3 * q + 1) by ring, b_even]; push_cast; ring
  · rw [show 6 * q + 3 = 2 * (3 * q + 1) + 1 by ring, b_odd]; push_cast; ring
  · rw [show 6 * q + 4 = 2 * (3 * q + 2) by ring, b_even]; push_cast; ring
  · rw [show 6 * q + 5 = 2 * (3 * q + 2) + 1 by ring, b_odd]; push_cast; ring

end OMA_A295867_Proof

open OMA_A295867_Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a295867.main := by
  intro n hn
  obtain ⟨j, s, hs, hjs⟩ : ∃ j s, s < 5 ∧ n = 5 * j + s + 16 :=
    ⟨(n - 16) / 5, (n - 16) % 5, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases s
  · -- n ≡ 1 (mod 5)
    have e0 : n = 5 * (j + 3) + 1 := by omega
    have e1 : n - 1 = 5 * (j + 3) + 0 := by omega
    have e5 : n - 5 = 5 * (j + 2) + 1 := by omega
    have e6 : n - 6 = 5 * (j + 2) + 0 := by omega
    have e10 : n - 10 = 5 * (j + 1) + 1 := by omega
    have e11 : n - 11 = 5 * (j + 1) + 0 := by omega
    have e15 : n - 15 = 5 * (j + 0) + 1 := by omega
    have e16 : n - 16 = 5 * (j + 0) + 0 := by omega
    rw [e1, e5, e6, e10, e11, e15, e16, e0]
    rw [aV (j + 3) 1 (by norm_num), aV (j + 3) 0 (by norm_num), aV (j + 2) 1 (by norm_num), aV (j + 2) 0 (by norm_num), aV (j + 1) 1 (by norm_num), aV (j + 1) 0 (by norm_num), aV (j + 0) 1 (by norm_num), aV (j + 0) 0 (by norm_num)]
    simp only [V]; push_cast; ring
  · -- n ≡ 2 (mod 5)
    have e0 : n = 5 * (j + 3) + 2 := by omega
    have e1 : n - 1 = 5 * (j + 3) + 1 := by omega
    have e5 : n - 5 = 5 * (j + 2) + 2 := by omega
    have e6 : n - 6 = 5 * (j + 2) + 1 := by omega
    have e10 : n - 10 = 5 * (j + 1) + 2 := by omega
    have e11 : n - 11 = 5 * (j + 1) + 1 := by omega
    have e15 : n - 15 = 5 * (j + 0) + 2 := by omega
    have e16 : n - 16 = 5 * (j + 0) + 1 := by omega
    rw [e1, e5, e6, e10, e11, e15, e16, e0]
    rw [aV (j + 3) 2 (by norm_num), aV (j + 3) 1 (by norm_num), aV (j + 2) 2 (by norm_num), aV (j + 2) 1 (by norm_num), aV (j + 1) 2 (by norm_num), aV (j + 1) 1 (by norm_num), aV (j + 0) 2 (by norm_num), aV (j + 0) 1 (by norm_num)]
    simp only [V]; push_cast; ring
  · -- n ≡ 3 (mod 5)
    have e0 : n = 5 * (j + 3) + 3 := by omega
    have e1 : n - 1 = 5 * (j + 3) + 2 := by omega
    have e5 : n - 5 = 5 * (j + 2) + 3 := by omega
    have e6 : n - 6 = 5 * (j + 2) + 2 := by omega
    have e10 : n - 10 = 5 * (j + 1) + 3 := by omega
    have e11 : n - 11 = 5 * (j + 1) + 2 := by omega
    have e15 : n - 15 = 5 * (j + 0) + 3 := by omega
    have e16 : n - 16 = 5 * (j + 0) + 2 := by omega
    rw [e1, e5, e6, e10, e11, e15, e16, e0]
    rw [aV (j + 3) 3 (by norm_num), aV (j + 3) 2 (by norm_num), aV (j + 2) 3 (by norm_num), aV (j + 2) 2 (by norm_num), aV (j + 1) 3 (by norm_num), aV (j + 1) 2 (by norm_num), aV (j + 0) 3 (by norm_num), aV (j + 0) 2 (by norm_num)]
    simp only [V]; push_cast; ring
  · -- n ≡ 4 (mod 5)
    have e0 : n = 5 * (j + 3) + 4 := by omega
    have e1 : n - 1 = 5 * (j + 3) + 3 := by omega
    have e5 : n - 5 = 5 * (j + 2) + 4 := by omega
    have e6 : n - 6 = 5 * (j + 2) + 3 := by omega
    have e10 : n - 10 = 5 * (j + 1) + 4 := by omega
    have e11 : n - 11 = 5 * (j + 1) + 3 := by omega
    have e15 : n - 15 = 5 * (j + 0) + 4 := by omega
    have e16 : n - 16 = 5 * (j + 0) + 3 := by omega
    rw [e1, e5, e6, e10, e11, e15, e16, e0]
    rw [aV (j + 3) 4 (by norm_num), aV (j + 3) 3 (by norm_num), aV (j + 2) 4 (by norm_num), aV (j + 2) 3 (by norm_num), aV (j + 1) 4 (by norm_num), aV (j + 1) 3 (by norm_num), aV (j + 0) 4 (by norm_num), aV (j + 0) 3 (by norm_num)]
    simp only [V]; push_cast; ring
  · -- n ≡ 0 (mod 5)
    have e0 : n = 5 * (j + 4) + 0 := by omega
    have e1 : n - 1 = 5 * (j + 3) + 4 := by omega
    have e5 : n - 5 = 5 * (j + 3) + 0 := by omega
    have e6 : n - 6 = 5 * (j + 2) + 4 := by omega
    have e10 : n - 10 = 5 * (j + 2) + 0 := by omega
    have e11 : n - 11 = 5 * (j + 1) + 4 := by omega
    have e15 : n - 15 = 5 * (j + 1) + 0 := by omega
    have e16 : n - 16 = 5 * (j + 0) + 4 := by omega
    rw [e1, e5, e6, e10, e11, e15, e16, e0]
    rw [aV (j + 4) 0 (by norm_num), aV (j + 3) 4 (by norm_num), aV (j + 3) 0 (by norm_num), aV (j + 2) 4 (by norm_num), aV (j + 2) 0 (by norm_num), aV (j + 1) 4 (by norm_num), aV (j + 1) 0 (by norm_num), aV (j + 0) 4 (by norm_num)]
    simp only [V]; push_cast; ring
