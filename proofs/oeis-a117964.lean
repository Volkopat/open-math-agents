import OMAStatements.S_oeis_a117964
import Mathlib

-- Proof route. Step 1 (Lucas mod 3): w u = C(2u,u) satisfies w(3j) = w j, w(3j+1) = 2 w j and 3 | w(3j+2)
-- (mod 3), so the sums of w over k < 3q and over k < 3q+2 vanish mod 3, and the sum over k < 3q+1 is w q mod 3;
-- hence m is in A081601 iff 3 | m and 3 does not divide w(m/3). Step 2: L(j/3) is odd iff 3 does not divide j,
-- so a(n) is the parity of c n, the number of pairs (N,K) with N + K = n and 3 not dividing C(N,K); Lucas on the
-- last base-3 digits gives c n = E n 0 + E n 1 + 2 E n 2 + E n 3 + E n 4 with E n t = c((n-t)/3) when t <= n and
-- 3 | n - t, and strong induction gives c n odd iff n mod 18 is 0, 1, 6 or 7 and 3 does not divide w(n/18).

namespace OMA.A117964Proof

open Finset

lemma lucas3 (N K : ℕ) :
    N.choose K % 3 = ((N % 3).choose (K % 3) * (N / 3).choose (K / 3)) % 3 := by
  have h : N.choose K ≡ (N % 3).choose (K % 3) * (N / 3).choose (K / 3) [MOD 3] :=
    Choose.choose_modEq_choose_mod_mul_choose_div_nat
  exact h

lemma dvd3_choose (N K : ℕ) :
    3 ∣ N.choose K ↔ 3 ∣ (N % 3).choose (K % 3) ∨ 3 ∣ (N / 3).choose (K / 3) := by
  rw [Nat.dvd_iff_mod_eq_zero, lucas3, ← Nat.dvd_iff_mod_eq_zero]
  exact Nat.prime_three.dvd_mul

-- Step 1: central binomial coefficients mod 3.

def w (u : ℕ) : ℕ := (2 * u).choose u

lemma cb0 (j : ℕ) : w (3 * j) % 3 = w j % 3 := by
  unfold w
  rw [lucas3, show 2 * (3 * j) % 3 = 0 by omega, show 3 * j % 3 = 0 by omega,
    show 2 * (3 * j) / 3 = 2 * j by omega, show 3 * j / 3 = j by omega]
  simp

lemma cb1 (j : ℕ) : w (3 * j + 1) % 3 = (2 * w j) % 3 := by
  unfold w
  rw [lucas3, show 2 * (3 * j + 1) % 3 = 2 by omega, show (3 * j + 1) % 3 = 1 by omega,
    show 2 * (3 * j + 1) / 3 = 2 * j by omega, show (3 * j + 1) / 3 = j by omega]
  simp

lemma cb2 (j : ℕ) : 3 ∣ w (3 * j + 2) := by
  unfold w
  rw [dvd3_choose, show 2 * (3 * j + 2) % 3 = 1 by omega, show (3 * j + 2) % 3 = 2 by omega]
  left
  decide

lemma F_mod (q : ℕ) : (∑ k ∈ range (3 * q), w k) % 3 = 0 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 3 * (q + 1) = 3 * q + 1 + 1 + 1 by ring, sum_range_succ, sum_range_succ,
      sum_range_succ, show 3 * q + 1 + 1 = 3 * q + 2 by ring]
    have h0 := cb0 q
    have h1 := cb1 q
    have h2 := cb2 q
    omega

lemma A1 (m : ℕ) : OMA.S_oeis_a117964.inA081601 m ↔ m % 3 = 0 ∧ ¬ 3 ∣ w (m / 3) := by
  unfold OMA.S_oeis_a117964.inA081601
  show ¬ 3 ∣ ∑ k ∈ range (m + 1), w k ↔ _
  rcases (by omega : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2) with h | h | h
  · obtain ⟨t, rfl⟩ : ∃ t, m = 3 * t := ⟨m / 3, by omega⟩
    rw [sum_range_succ, show 3 * t / 3 = t by omega]
    have h0 := F_mod t
    have h1 := cb0 t
    omega
  · obtain ⟨t, rfl⟩ : ∃ t, m = 3 * t + 1 := ⟨m / 3, by omega⟩
    rw [sum_range_succ, sum_range_succ, show (3 * t + 1) / 3 = t by omega]
    have h0 := F_mod t
    have h1 := cb0 t
    have h2 := cb1 t
    omega
  · obtain ⟨t, rfl⟩ : ∃ t, m = 3 * t + 2 := ⟨m / 3, by omega⟩
    rw [show 3 * t + 2 + 1 = 3 * (t + 1) by ring]
    have h0 := F_mod (t + 1)
    omega

lemma Zrec (j i : ℕ) (hi : i < 3) : ¬ 3 ∣ w (3 * j + i) ↔ i ≤ 1 ∧ ¬ 3 ∣ w j := by
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2) with rfl | rfl | rfl
  · rw [Nat.add_zero]
    have h0 := cb0 j
    omega
  · have h1 := cb1 j
    omega
  · have h2 := cb2 j
    omega

-- Step 2: the parity count.

def G (N K : ℕ) : ℕ := if 3 ∣ N.choose K then 0 else 1

lemma G_mul (N K : ℕ) : G N K = G (N % 3) (K % 3) * G (N / 3) (K / 3) := by
  by_cases h1 : 3 ∣ (N % 3).choose (K % 3) <;> by_cases h2 : 3 ∣ (N / 3).choose (K / 3) <;>
    simp [G, dvd3_choose N K, h1, h2]

def box (B n : ℕ) : ℕ := ∑ N ∈ range B, ∑ K ∈ range B, if N + K = n then G N K else 0

lemma box_eq (B n : ℕ) (h : n < B) : box B n = box (n + 1) n := by
  have hs : range (n + 1) ⊆ range B := range_subset_range.mpr (by omega)
  unfold box
  symm
  calc (∑ N ∈ range (n + 1), ∑ K ∈ range (n + 1), if N + K = n then G N K else 0)
      = ∑ N ∈ range B, ∑ K ∈ range (n + 1), (if N + K = n then G N K else 0) := by
        apply sum_subset hs
        intro N _ hN
        rw [mem_range] at hN
        apply sum_eq_zero
        intro K _
        rw [if_neg (show ¬ (N + K = n) by omega)]
    _ = ∑ N ∈ range B, ∑ K ∈ range B, (if N + K = n then G N K else 0) := by
        refine sum_congr rfl fun N _ => ?_
        apply sum_subset hs
        intro K _ hK
        rw [mem_range] at hK
        rw [if_neg (show ¬ (N + K = n) by omega)]

lemma box_self (n : ℕ) : box (n + 1) n = ∑ k ∈ range (n / 2 + 1), G (n - k) k := by
  unfold box
  rw [sum_comm]
  have inner : ∀ K ∈ range (n + 1),
      (∑ N ∈ range (n + 1), if N + K = n then G N K else 0) = G (n - K) K := by
    intro K hK
    rw [mem_range] at hK
    rw [sum_eq_single (n - K)]
    · rw [if_pos (show n - K + K = n by omega)]
    · intro N _ hN
      rw [if_neg (show ¬ (N + K = n) by omega)]
    · intro h
      exact absurd (mem_range.mpr (show n - K < n + 1 by omega)) h
  rw [sum_congr rfl inner]
  symm
  apply sum_subset (range_subset_range.mpr (by omega))
  intro K hK hK'
  rw [mem_range] at hK hK'
  unfold G
  rw [Nat.choose_eq_zero_of_lt (show n - K < K by omega), if_pos (dvd_zero 3)]

lemma sum_range_mul3 (h : ℕ → ℕ) (M : ℕ) :
    ∑ N ∈ range (3 * M), h N = ∑ N' ∈ range M, ∑ a ∈ range 3, h (3 * N' + a) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, show 3 * (M + 1) = 3 * M + 3 by ring, sum_range_add, ih]

def D (M n t : ℕ) : ℕ :=
  ∑ N ∈ range M, ∑ K ∈ range M, if 3 * (N + K) + t = n then G N K else 0

lemma term3 (n N' a K' b : ℕ) (ha : a < 3) (hb : b < 3) :
    (if 3 * N' + a + (3 * K' + b) = n then G (3 * N' + a) (3 * K' + b) else 0) =
      G a b * (if 3 * (N' + K') + (a + b) = n then G N' K' else 0) := by
  rw [G_mul (3 * N' + a) (3 * K' + b), show (3 * N' + a) % 3 = a by omega,
    show (3 * N' + a) / 3 = N' by omega, show (3 * K' + b) % 3 = b by omega,
    show (3 * K' + b) / 3 = K' by omega]
  by_cases hc : 3 * (N' + K') + (a + b) = n
  · rw [if_pos (show 3 * N' + a + (3 * K' + b) = n by omega), if_pos hc]
  · rw [if_neg (show ¬ (3 * N' + a + (3 * K' + b) = n) by omega), if_neg hc, mul_zero]

lemma box3 (M n : ℕ) :
    box (3 * M) n = ∑ a ∈ range 3, ∑ b ∈ range 3, G a b * D M n (a + b) := by
  calc box (3 * M) n
      = ∑ N' ∈ range M, ∑ a ∈ range 3, ∑ K' ∈ range M, ∑ b ∈ range 3,
          (if 3 * N' + a + (3 * K' + b) = n then G (3 * N' + a) (3 * K' + b) else 0) := by
        unfold box
        rw [sum_range_mul3]
        refine sum_congr rfl fun N' _ => sum_congr rfl fun a _ => ?_
        rw [sum_range_mul3]
    _ = ∑ N' ∈ range M, ∑ a ∈ range 3, ∑ K' ∈ range M, ∑ b ∈ range 3,
          G a b * (if 3 * (N' + K') + (a + b) = n then G N' K' else 0) := by
        refine sum_congr rfl fun N' _ => sum_congr rfl fun a ha => sum_congr rfl fun K' _ =>
          sum_congr rfl fun b hb => ?_
        exact term3 n N' a K' b (mem_range.mp ha) (mem_range.mp hb)
    _ = ∑ a ∈ range 3, ∑ N' ∈ range M, ∑ K' ∈ range M, ∑ b ∈ range 3,
          G a b * (if 3 * (N' + K') + (a + b) = n then G N' K' else 0) := sum_comm
    _ = ∑ a ∈ range 3, ∑ N' ∈ range M, ∑ b ∈ range 3, ∑ K' ∈ range M,
          G a b * (if 3 * (N' + K') + (a + b) = n then G N' K' else 0) := by
        refine sum_congr rfl fun a _ => sum_congr rfl fun N' _ => ?_
        exact sum_comm
    _ = ∑ a ∈ range 3, ∑ b ∈ range 3, ∑ N' ∈ range M, ∑ K' ∈ range M,
          G a b * (if 3 * (N' + K') + (a + b) = n then G N' K' else 0) := by
        refine sum_congr rfl fun a _ => ?_
        exact sum_comm
    _ = ∑ a ∈ range 3, ∑ b ∈ range 3, G a b * D M n (a + b) := by
        refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
        unfold D
        rw [mul_sum]
        refine sum_congr rfl fun N' _ => ?_
        rw [mul_sum]

lemma D_eq (M n t : ℕ) :
    D M n t = if t ≤ n ∧ (n - t) % 3 = 0 then box M ((n - t) / 3) else 0 := by
  unfold D box
  split_ifs with h
  · refine sum_congr rfl fun N _ => sum_congr rfl fun K _ => ?_
    by_cases hc : N + K = (n - t) / 3
    · rw [if_pos (show 3 * (N + K) + t = n by omega), if_pos hc]
    · rw [if_neg (show ¬ (3 * (N + K) + t = n) by omega), if_neg hc]
  · refine sum_eq_zero fun N _ => sum_eq_zero fun K _ => ?_
    rw [if_neg (show ¬ (3 * (N + K) + t = n) by omega)]

def c (n : ℕ) : ℕ := box (n + 1) n

def E (n t : ℕ) : ℕ := if t ≤ n ∧ (n - t) % 3 = 0 then c ((n - t) / 3) else 0

lemma G00 : G 0 0 = 1 := by decide
lemma G01 : G 0 1 = 0 := by decide
lemma G02 : G 0 2 = 0 := by decide
lemma G10 : G 1 0 = 1 := by decide
lemma G11 : G 1 1 = 1 := by decide
lemma G12 : G 1 2 = 0 := by decide
lemma G20 : G 2 0 = 1 := by decide
lemma G21 : G 2 1 = 1 := by decide
lemma G22 : G 2 2 = 1 := by decide

lemma c_rec (n : ℕ) : c n = E n 0 + E n 1 + E n 2 + E n 2 + E n 3 + E n 4 := by
  have h1 : c n = box (3 * (n + 1)) n := (box_eq (3 * (n + 1)) n (by omega)).symm
  have hD : ∀ t, D (n + 1) n t = E n t := by
    intro t
    rw [D_eq]
    unfold E
    split_ifs with h
    · unfold c
      exact box_eq (n + 1) _ (by omega)
    · rfl
  rw [h1, box3]
  simp only [hD, sum_range_succ, sum_range_zero, zero_add, G00, G01, G02, G10, G11, G12, G20,
    G21, G22, one_mul, zero_mul, add_zero, Nat.reduceAdd]
  omega

def J (x : ℕ) : Prop := x / 2 % 3 = 0 ∧ ¬ 3 ∣ w (x / 6)

lemma J_iff (x : ℕ) :
    J x ↔ (x % 18 = 0 ∨ x % 18 = 1 ∨ x % 18 = 6 ∨ x % 18 = 7) ∧ ¬ 3 ∣ w (x / 18) := by
  unfold J
  have e : x / 6 = 3 * (x / 18) + x / 6 % 3 := by omega
  rw [e, Zrec (x / 18) (x / 6 % 3) (by omega)]
  omega

lemma J_div3 (n t : ℕ) (ht : t ≤ n) (h3 : (n - t) % 3 = 0) (ht4 : t ≤ 4) :
    J ((n - t) / 3) ↔ ((n - t) % 18 = 0 ∨ (n - t) % 18 = 3) ∧ ¬ 3 ∣ w (n / 18) := by
  unfold J
  have key : (n - t) % 18 = 0 ∨ (n - t) % 18 = 3 → (n - t) / 3 / 6 = n / 18 := by omega
  constructor
  · rintro ⟨h1, h2⟩
    have h' : (n - t) % 18 = 0 ∨ (n - t) % 18 = 3 := by omega
    rw [key h'] at h2
    exact ⟨h', h2⟩
  · rintro ⟨h1, h2⟩
    rw [← key h1] at h2
    exact ⟨by omega, h2⟩

lemma E_mod (n t : ℕ) (ht4 : t ≤ 4) (hn : 0 < n) (ih : ∀ m, m < n → (c m % 2 = 1 ↔ J m)) :
    E n t % 2 = 1 ↔ (t ≤ n ∧ (n % 18 = t ∨ n % 18 = t + 3)) ∧ ¬ 3 ∣ w (n / 18) := by
  unfold E
  by_cases h1 : t ≤ n ∧ (n - t) % 3 = 0
  · rw [if_pos h1, ih ((n - t) / 3) (by omega), J_div3 n t h1.1 h1.2 ht4]
    omega
  · rw [if_neg h1]
    omega

lemma c_mod (n : ℕ) : c n % 2 = 1 ↔ J n := by
  refine Nat.strong_induction_on n ?_
  intro n ih
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : c 0 = 1 := by decide
    rw [h0]
    unfold J
    decide
  · rw [c_rec n, J_iff n]
    have h0 := E_mod n 0 (by norm_num) hn ih
    have h1 := E_mod n 1 (by norm_num) hn ih
    have h3 := E_mod n 3 (by norm_num) hn ih
    have h4 := E_mod n 4 (by norm_num) hn ih
    clear ih
    generalize E n 0 = e0 at h0 ⊢
    generalize E n 1 = e1 at h1 ⊢
    generalize E n 2 = e2
    generalize E n 3 = e3 at h3 ⊢
    generalize E n 4 = e4 at h4 ⊢
    generalize w (n / 18) = z at h0 h1 h3 h4 ⊢
    obtain ⟨r, hr, hlt⟩ : ∃ r, n % 18 = r ∧ r < 18 := ⟨_, rfl, Nat.mod_lt _ (by norm_num)⟩
    by_cases hz : 3 ∣ z
    · simp only [hz, not_true_eq_false, and_false, iff_false] at h0 h1 h3 h4 ⊢
      omega
    · simp only [hz, not_false_eq_true, and_true] at h0 h1 h3 h4 ⊢
      interval_cases r <;> omega

-- The Legendre symbol mod 2, and the main equivalence.

lemma leg_mod2 (x : ℕ) :
    legendreSym 3 (x : ℤ) % 2 = (((if 3 ∣ x then 0 else 1 : ℕ)) : ℤ) % 2 := by
  by_cases h : 3 ∣ x
  · have h0 : legendreSym 3 (x : ℤ) = 0 := by
      rw [legendreSym.eq_zero_iff, Int.cast_natCast, ZMod.natCast_eq_zero_iff]
      exact h
    rw [h0, if_pos h]
    norm_num
  · have h0 : ((x : ℤ) : ZMod 3) ≠ 0 := by
      rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
      exact h
    rw [if_neg h]
    rcases legendreSym.eq_one_or_neg_one 3 h0 with h1 | h1 <;> rw [h1] <;> norm_num

lemma a_eq (n : ℕ) : OMA.S_oeis_a117964.a n = ((c n : ℕ) : ℤ) % 2 := by
  have hc : ((c n : ℕ) : ℤ) = ∑ k ∈ range (n / 2 + 1), ((G (n - k) k : ℕ) : ℤ) := by
    rw [c, box_self, Nat.cast_sum]
  rw [hc]
  unfold OMA.S_oeis_a117964.a OMA.S_oeis_a117964.A117963
  calc (∑ k ∈ range (n / 2 + 1), legendreSym 3 ((n - k).choose k : ℤ)) % 2
      = (∑ k ∈ range (n / 2 + 1), legendreSym 3 ((n - k).choose k : ℤ) % 2) % 2 :=
        Finset.sum_int_mod _ _ _
    _ = (∑ k ∈ range (n / 2 + 1), ((G (n - k) k : ℕ) : ℤ) % 2) % 2 := by
        rw [sum_congr rfl fun k _ => leg_mod2 ((n - k).choose k)]
        rfl
    _ = (∑ k ∈ range (n / 2 + 1), ((G (n - k) k : ℕ) : ℤ)) % 2 :=
        (Finset.sum_int_mod _ _ _).symm

lemma hR (n : ℕ) :
    (∃ m : ℕ, OMA.S_oeis_a117964.inA081601 m ∧ (n = 2 * m ∨ n = 2 * m + 1)) ↔ J n := by
  constructor
  · rintro ⟨m, hm, hn⟩
    rw [A1] at hm
    have e1 : n / 2 = m := by omega
    have e2 : n / 6 = m / 3 := by omega
    unfold J
    rw [e1, e2]
    exact hm
  · intro h
    unfold J at h
    refine ⟨n / 2, ?_, by omega⟩
    rw [A1, show n / 2 / 3 = n / 6 by omega]
    exact h

end OMA.A117964Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a117964.main := by
  intro n
  rw [OMA.A117964Proof.a_eq, OMA.A117964Proof.hR, ← OMA.A117964Proof.c_mod n]
  omega
