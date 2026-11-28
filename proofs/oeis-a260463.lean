import OMAStatements.S_oeis_a260463
import Mathlib

namespace OMA.A260463Proof

open OMA.S_oeis_a260463

/-! General facts, for any exponent `e ≥ 1`. -/

lemma lt_ten_pow (t : ℕ) : t < 10 ^ t := by
  induction t with
  | zero => norm_num
  | succ t ih => rw [pow_succ]; omega

lemma succ_pow_le (y d : ℕ) : (y + 1) ^ (d + 1) ≤ y ^ (d + 1) + (d + 1) * (y + 1) ^ d := by
  induction d with
  | zero => first | simp | norm_num | omega
  | succ d ih =>
    have e1 : (y + 1) ^ (d + 1 + 1) = (y + 1) ^ (d + 1) * (y + 1) := pow_succ _ _
    have e2 : y ^ (d + 1 + 1) = y ^ (d + 1) * y := pow_succ _ _
    have e3 : (y + 1) ^ (d + 1) = (y + 1) ^ d * (y + 1) := pow_succ _ _
    have h2 : y ^ (d + 1) ≤ (y + 1) ^ (d + 1) := Nat.pow_le_pow_left (by omega) _
    have h5 : (y + 1) ^ (d + 1) * (y + 1) ≤ (y ^ (d + 1) + (d + 1) * (y + 1) ^ d) * (y + 1) :=
      Nat.mul_le_mul ih (le_refl _)
    have h6 : (y ^ (d + 1) + (d + 1) * (y + 1) ^ d) * (y + 1) =
        y ^ (d + 1) * y + y ^ (d + 1) + (d + 1) * ((y + 1) ^ d * (y + 1)) := by ring
    rw [← e3] at h6
    have h7 : (d + 1 + 1) * (y + 1) ^ (d + 1) = (d + 1) * (y + 1) ^ (d + 1) + (y + 1) ^ (d + 1) := by ring
    rw [e1, e2, h7]
    first | omega | linarith | nlinarith [h5, h6, h2]

lemma pow_lt_succ_pow (k d : ℕ) : k ^ (d + 1) < (k + 1) ^ (d + 1) := by
  have h1 : k ^ d ≤ (k + 1) ^ d := Nat.pow_le_pow_left (by omega) d
  have h2 : 0 < (k + 1) ^ d := pow_pos (by omega) d
  have e1 : (k + 1) ^ (d + 1) = (k + 1) ^ d * k + (k + 1) ^ d := by ring
  have e2 : k ^ (d + 1) = k ^ d * k := pow_succ k d
  have h3 : k ^ d * k ≤ (k + 1) ^ d * k := Nat.mul_le_mul h1 (le_refl k)
  rw [e1, e2]
  omega

lemma pow_le_cancel (e m k : ℕ) (he : 1 ≤ e) (h : m ^ e ≤ k ^ e) : m ≤ k := by
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  by_contra hlt
  have h1 := pow_lt_succ_pow k d
  have h2 : (k + 1) ^ (d + 1) ≤ m ^ (d + 1) := Nat.pow_le_pow_left (by omega) (d + 1)
  omega

/-- Some `x ≥ 1` has `x ^ e` beginning with `n`: take `x` least with `n * c ^ e ≤ x ^ e`, `c = 10 ^ t` large. -/
lemma exists_root (e n : ℕ) (he : 1 ≤ e) (hn : 1 ≤ n) : ∃ x, 1 ≤ x ∧ Begins n (x ^ e) := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d, e = d + 1 := ⟨e - 1, by omega⟩
  have hn0 : 0 < n := by omega
  obtain ⟨t, ht⟩ : ∃ t, (d + 1) * n ^ d < 10 ^ t := ⟨_, lt_ten_pow _⟩
  obtain ⟨c, hct, hcpow⟩ : ∃ c, (d + 1) * n ^ d < c ∧ c ^ (d + 1) = 10 ^ (t * (d + 1)) :=
    ⟨10 ^ t, ht, by rw [pow_mul]⟩
  have hpos : 0 < (d + 1) * n ^ d := Nat.mul_pos (by omega) (pow_pos hn0 d)
  have hc0 : 0 < c := by omega
  have hcpos : 0 < c ^ (d + 1) := pow_pos hc0 _
  have hwit : n * c ^ (d + 1) ≤ (n * c) ^ (d + 1) := by
    rw [mul_pow]
    have h1 : n ≤ n ^ (d + 1) := by
      have e : n ^ (d + 1) = n ^ d * n := pow_succ n d
      have h2 : 1 ≤ n ^ d := by have := pow_pos hn0 d; omega
      have h3 : 1 * n ≤ n ^ d * n := Nat.mul_le_mul h2 (le_refl n)
      rw [e]; omega
    exact Nat.mul_le_mul h1 (le_refl _)
  have hP : ∃ x, n * c ^ (d + 1) ≤ x ^ (d + 1) := ⟨n * c, hwit⟩
  obtain ⟨x, hx, hxle, hxmin⟩ : ∃ x, n * c ^ (d + 1) ≤ x ^ (d + 1) ∧ x ≤ n * c ∧
      ∀ y, y < x → ¬ (n * c ^ (d + 1) ≤ y ^ (d + 1)) :=
    ⟨Nat.find hP, Nat.find_spec hP, Nat.find_min' hP hwit, fun y hy => Nat.find_min hP hy⟩
  have hx0 : x ≠ 0 := by
    rintro rfl
    have hz : (0 : ℕ) ^ (d + 1) = 0 := by first | rfl | simp
    rw [hz] at hx
    have : 0 < n * c ^ (d + 1) := Nat.mul_pos hn0 hcpos
    omega
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have hy : ¬ (n * c ^ (d + 1) ≤ y ^ (d + 1)) := hxmin y (by omega)
  have key := succ_pow_le y d
  have h3 : (y + 1) ^ d ≤ (n * c) ^ d := Nat.pow_le_pow_left hxle d
  have h4 : (d + 1) * (n * c) ^ d ≤ c ^ (d + 1) := by
    have e1 : (d + 1) * (n * c) ^ d = ((d + 1) * n ^ d) * c ^ d := by rw [mul_pow]; ring
    have e2 : c ^ (d + 1) = c * c ^ d := by ring
    rw [e1, e2]
    exact Nat.mul_le_mul hct.le (le_refl _)
  have h5 : (d + 1) * (y + 1) ^ d ≤ (d + 1) * (n * c) ^ d := Nat.mul_le_mul (le_refl _) h3
  refine ⟨y + 1, by omega, ?_⟩
  refine ⟨t * (d + 1), ?_, ?_⟩
  · rw [← hcpow]; exact hx
  · rw [← hcpow]
    have e3 : (n + 1) * c ^ (d + 1) = n * c ^ (d + 1) + c ^ (d + 1) := by ring
    rw [e3]
    first | omega | linarith

lemma begins_mul_ten_pow (n x u : ℕ) (h : Begins n x) : Begins n (x * 10 ^ u) := by
  obtain ⟨j, h1, h2⟩ := h
  refine ⟨j + u, ?_, ?_⟩
  · rw [pow_add, ← mul_assoc]; exact Nat.mul_le_mul h1 (le_refl _)
  · rw [pow_add, ← mul_assoc]
    have h3 : 0 < 10 ^ u := by positivity
    first | exact Nat.mul_lt_mul_of_pos_right h2 h3 | nlinarith

/-- Arbitrarily large `k` have `k ^ e` beginning with `n`. -/
lemma exists_large (e n B : ℕ) (he : 1 ≤ e) (hn : 1 ≤ n) : ∃ k, B < k ∧ Begins n (k ^ e) := by
  obtain ⟨x, hx1, hx⟩ := exists_root e n he hn
  refine ⟨x * 10 ^ B, ?_, ?_⟩
  · have h1 := lt_ten_pow B
    have h2 : 1 * 10 ^ B ≤ x * 10 ^ B := Nat.mul_le_mul hx1 (le_refl _)
    omega
  · rw [mul_pow, ← pow_mul]
    exact begins_mul_ten_pow n (x ^ e) (B * e) hx

lemma le_sum_of_mem' (L : List ℕ) (x : ℕ) (h : x ∈ L) : x ≤ L.sum := by
  induction L with
  | nil => simp at h
  | cons b L ih =>
    rw [List.sum_cons]
    rcases List.mem_cons.mp h with h | h
    · omega
    · have := ih h; omega

lemma exists_fresh (e : ℕ) (he : 1 ≤ e) (L : List ℕ) (n : ℕ) (hn : 1 ≤ n) :
    ∃ k, k ∉ L ∧ Begins n (k ^ e) := by
  obtain ⟨k, hk, hb⟩ := exists_large e n L.sum he hn
  refine ⟨k, fun hm => ?_, hb⟩
  have := le_sum_of_mem' L k hm
  omega

/-! The greedy sequence of the statement (exponent 2). -/

lemma pre_succ (n : ℕ) :
    pre (n + 1) = pre n ++ [sInf {k : ℕ | k ∉ pre n ∧ Begins (n + 1) (k ^ 2)}] := by
  first | rfl | simp [pre] | rw [pre]

lemma spec_mem (n : ℕ) :
    sInf {k : ℕ | k ∉ pre n ∧ Begins (n + 1) (k ^ 2)} ∈ {k : ℕ | k ∉ pre n ∧ Begins (n + 1) (k ^ 2)} := by
  apply Nat.sInf_mem
  obtain ⟨k, hk1, hk2⟩ := exists_fresh 2 (by norm_num) (pre n) (n + 1) (by omega)
  first | exact ⟨k, hk1, hk2⟩ | exact ⟨k, by simp only [Set.mem_setOf_eq]; exact ⟨hk1, hk2⟩⟩

lemma a_succ (n : ℕ) : a (n + 1) = sInf {k : ℕ | k ∉ pre n ∧ Begins (n + 1) (k ^ 2)} := by
  show (pre (n + 1)).getLastD 0 = _
  rw [pre_succ]
  first | simp | (rw [List.getLastD_eq_getLast?, List.getLast?_concat]; rfl) | exact List.getLastD_concat _ _ _

lemma a_spec (n : ℕ) : a (n + 1) ∉ pre n ∧ Begins (n + 1) (a (n + 1) ^ 2) := by
  rw [a_succ]
  exact spec_mem n

lemma a_le_of (n k : ℕ) (hk : k ∉ pre n) (hb : Begins (n + 1) (k ^ 2)) : a (n + 1) ≤ k := by
  rw [a_succ]
  apply Nat.sInf_le
  first | exact ⟨hk, hb⟩ | (simp only [Set.mem_setOf_eq]; exact ⟨hk, hb⟩)

lemma mem_pre_add (i t x : ℕ) (h : x ∈ pre i) : x ∈ pre (i + t) := by
  induction t with
  | zero => exact h
  | succ t ih =>
    rw [← Nat.add_assoc, pre_succ]
    exact List.mem_append.mpr (Or.inl ih)

lemma a_mem_pre (n : ℕ) : a (n + 1) ∈ pre (n + 1) := by
  rw [a_succ, pre_succ]
  exact List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))

lemma exists_of_mem_pre (n x : ℕ) (h : x ∈ pre n) : ∃ i, 1 ≤ i ∧ i ≤ n ∧ a i = x := by
  induction n with
  | zero =>
    have h0 : pre 0 = [] := by first | rfl | simp [pre]
    rw [h0] at h
    simp at h
  | succ n ih =>
    rw [pre_succ] at h
    rcases List.mem_append.mp h with h | h
    · obtain ⟨i, h1, h2, h3⟩ := ih h
      exact ⟨i, h1, by omega, h3⟩
    · have h' := List.mem_singleton.mp h
      exact ⟨n + 1, by omega, le_refl _, by rw [a_succ, h']⟩

lemma a_pos (m : ℕ) : 1 ≤ a (m + 1) := by
  obtain ⟨_, j, h1, _⟩ := a_spec m
  rcases Nat.eq_zero_or_pos (a (m + 1)) with h0 | h0
  · rw [h0] at h1
    have h2 : (0 : ℕ) ^ 2 = 0 := by norm_num
    rw [h2] at h1
    have h3 : 0 < (m + 1) * 10 ^ j := by positivity
    omega
  · exact h0

lemma a_ne_of_lt (i j : ℕ) (hi : 1 ≤ i) (h : i < j) : a i ≠ a j := by
  obtain ⟨m, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  intro heq
  have hmem := mem_pre_add (i' + 1) (m - (i' + 1)) _ (a_mem_pre i')
  have h2 : i' + 1 + (m - (i' + 1)) = m := by omega
  rw [h2, heq] at hmem
  exact (a_spec m).1 hmem

/-- `m` is a term by index `m ^ 2`: the least `k` whose square begins with `m ^ 2` is `m`. -/
lemma mem_pre_pow (m : ℕ) (hm : 1 ≤ m) : m ∈ pre (m ^ 2) := by
  obtain ⟨N, hN⟩ : ∃ N, m ^ 2 = N + 1 :=
    ⟨m ^ 2 - 1, by have := pow_pos (show 0 < m by omega) 2; omega⟩
  rw [hN]
  by_cases h : m ∈ pre N
  · exact mem_pre_add N 1 m h
  · have hb : Begins (N + 1) (m ^ 2) := by
      refine ⟨0, ?_, ?_⟩ <;> simp only [pow_zero, mul_one] <;> omega
    have hle : a (N + 1) ≤ m := a_le_of N m h hb
    obtain ⟨_, j, h1, _⟩ := a_spec N
    have h3 : m ^ 2 ≤ a (N + 1) ^ 2 := by
      have h4 : 1 ≤ 10 ^ j := by have := pow_pos (show (0 : ℕ) < 10 by norm_num) j; omega
      have h5 : (N + 1) * 1 ≤ (N + 1) * 10 ^ j := Nat.mul_le_mul (le_refl _) h4
      omega
    have hge : m ≤ a (N + 1) := pow_le_cancel 2 m (a (N + 1)) (by norm_num) h3
    have heq : a (N + 1) = m := le_antisymm hle hge
    rw [← heq]
    exact a_mem_pre N

lemma full_claim :
    (∀ n, 1 ≤ n → 1 ≤ a n) ∧ (∀ i j, 1 ≤ i → 1 ≤ j → a i = a j → i = j) ∧
      (∀ m, 1 ≤ m → ∃ n, 1 ≤ n ∧ a n = m) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact a_pos m
  · intro i j hi hj hij
    rcases lt_trichotomy i j with h | h | h
    · exact absurd hij (a_ne_of_lt i j hi h)
    · exact h
    · exact absurd hij.symm (a_ne_of_lt j i hj h)
  · intro m hm
    obtain ⟨i, h1, _, h3⟩ := exists_of_mem_pre (m ^ 2) m (mem_pre_pow m hm)
    exact ⟨i, h1, h3⟩

end OMA.A260463Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a260463.main := by
  exact OMA.A260463Proof.full_claim
