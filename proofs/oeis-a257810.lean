import OMAStatements.S_oeis_a257810
import Mathlib

namespace OMA.S_oeis_a257810

/-- digit-sum mirror with fuel -/
def s2f : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => (n % 100) ^ 2 + s2f f (n / 100)

lemma s2_rec (n : ℕ) : s2 n = (n % 100) ^ 2 + s2 (n / 100) := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · simp [s2]
  · unfold s2
    rw [Nat.digits_def' (by norm_num) h]
    simp

lemma s2_zero : s2 0 = 0 := by simp [s2]

lemma s2_eq_s2f : ∀ k n, n < 100 ^ k → s2 n = s2f k n
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this; simp [s2f, s2_zero]
  | k + 1, n, h => by
    rw [s2_rec, s2f, s2_eq_s2f k (n / 100)]
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]
    simpa [pow_succ] using h

lemma s2_bound : ∀ n, s2 n ≤ 9801 * (Nat.log 100 n + 1) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 100 with h | h
    · have hq : n / 100 = 0 := Nat.div_eq_of_lt h
      rw [s2_rec, hq, s2_zero]
      have : (n % 100) ^ 2 ≤ 9801 := by
        have h99 : n % 100 ≤ 99 := by omega
        calc (n % 100) ^ 2 ≤ 99 ^ 2 := Nat.pow_le_pow_left h99 2
          _ = 9801 := by norm_num
      omega
    · have hq : n / 100 < n := Nat.div_lt_self (by omega) (by norm_num)
      have hl : Nat.log 100 n = Nat.log 100 (n / 100) + 1 := by
        rw [Nat.log_div_base] ; have := Nat.log_pos (b := 100) (n := n) (by norm_num) h; omega
      have h1 := ih _ hq
      have h98 : (n % 100) ^ 2 ≤ 9801 := by
        have h99 : n % 100 ≤ 99 := by omega
        calc (n % 100) ^ 2 ≤ 99 ^ 2 := Nat.pow_le_pow_left h99 2
          _ = 9801 := by norm_num
      rw [s2_rec, hl]
      have : 9801 * (Nat.log 100 (n / 100) + 1 + 1) = 9801 * (Nat.log 100 (n / 100) + 1) + 9801 := by ring
      omega

lemma pow_big : ∀ L, 3 ≤ L → 9801 * (L + 1) < 100 ^ L := by
  intro L hL
  induction L, hL using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    rw [pow_succ]; nlinarith

lemma s2_lt (n : ℕ) (hn : 30000 ≤ n) : s2 n < n := by
  have hL : 2 ≤ Nat.log 100 n := by
    apply Nat.le_log_of_pow_le (by norm_num); omega
  have hb := s2_bound n
  have hp : 100 ^ Nat.log 100 n ≤ n := Nat.pow_log_le_self 100 (by omega)
  rcases Nat.eq_or_lt_of_le hL with h | h
  · rw [← h] at hb; omega
  · have := pow_big (Nat.log 100 n) (by omega)
    omega

lemma s2_small (n : ℕ) (hn : n < 30000) : s2 n < 30000 := by
  have hb := s2_bound n
  have hl3 : Nat.log 100 n < 3 := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · exact Nat.log_lt_of_lt_pow (by omega) (by norm_num; omega)
  have : Nat.log 100 n + 1 ≤ 3 := by omega
  calc s2 n ≤ 9801 * (Nat.log 100 n + 1) := hb
    _ ≤ 9801 * 3 := Nat.mul_le_mul_left _ this
    _ < 30000 := by norm_num

lemma iter_small (x : ℕ) (hx : x < 30000) : ∀ j, s2^[j] x < 30000
  | 0 => by simpa using hx
  | j + 1 => by
    rw [Function.iterate_succ_apply']
    exact s2_small _ (iter_small x hx j)

lemma reach_small : ∀ n, ∃ k, s2^[k] n < 30000 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases Nat.lt_or_ge n 30000 with h | h
    · exact ⟨0, by simpa using h⟩
    · obtain ⟨k, hk⟩ := ih _ (s2_lt n h)
      exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

lemma dec_iter : ∀ m n, 30000 ≤ n → s2^[m + 1] n < n
  | 0, n, h => by simpa using s2_lt n h
  | m + 1, n, h => by
    rw [Function.iterate_succ_apply]
    rcases Nat.lt_or_ge (s2 n) 30000 with h2 | h2
    · have := iter_small (s2 n) h2 (m + 1)
      omega
    · have := dec_iter m (s2 n) h2
      have := s2_lt n h
      omega

/-- computable mirror -/
def s2m (n : ℕ) : ℕ := s2f 6 n

def cs : List (List ℕ) :=
[[3869, 6205],
 [5965, 7706],
 [3460, 4756, 5345, 4834],
 [1781, 6850, 7124, 5617, 3425],
 [3770, 6269, 8605, 7421, 5917],
 [4973, 7730, 6829, 5465, 7141, 6722],
 [1268, 4768, 6833, 5713, 3418, 1480, 6596, 13441, 2838, 2228],
 [1946, 2477, 6505, 4250, 4264, 5860, 6964, 8857, 10993, 8731, 8530, 8125, 7186, 12437],
 [37, 1369, 4930, 3301, 1090, 8200, 6724, 5065, 6725, 5114, 2797, 10138, 1446, 2312, 673, 5365, 7034, 6056, 6736, 5785, 10474, 5493, 11565, 4451, 4537, 3394, 9925, 10426, 693, 8685, 14621, 2558, 3989, 9442, 10600],
 [41, 1681, 6817, 4913, 2570, 5525, 3650, 3796, 10585, 7251, 7785, 13154, 3878, 7528, 6409, 4177, 7610, 5876, 9140, 9881, 16165, 7947, 8450, 9556, 12161, 4163, 5650, 5636, 4432, 2960, 4441, 3617, 1585, 7450, 7976, 12017, 690, 8136, 7857, 9333, 9738, 10853, 2874, 6260, 7444, 7412, 5620, 3536, 2521, 1066, 4456, 5072, 7684, 12832, 1809, 405]]

def mask : ℕ := 0x2000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000020000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000000020000000000000000000000000000000000000000000000000000000000000010002000000000000000000000000000400000000000400000000000000000000000000000000000000000000000000000000000000000000000400000000000000000000000000000000000000000000000000002000000000020000000000000000000000000000000000040000000000000000000000000000000000000000000010000000000000000000000000000400000000000000000000000000200000000000000000000000000000000000000000000000100000000000000000000000000000000000000000000000000000000000000000000002000000000000000000000000000000080000000000200000000000000000002000000000000000000400000000000000000004000000000000000000000000000000000000000000000000000000000000010000000000000001002000000000000000000000000000000000000100000008000000000000000000000200000000000000000200000000000004000004000010000000000000000004000000000000000000010000000000000000000410000020100000000000000000000000000000000000000008000000000000000400000000002000100000000000000000000004000000000000000010000000000000000000000000000400022002000000000000000000010034000000000000000000000000000000100000000000000000000002000000000000000000000002000000000000000000000000000000000020100000000000002000000000000000000000000000000000000100000000000000000000002000000000002000000000100010000000000000000002000000000000000002000000000000000400100012000000000000000000000020000000200000020000000000000000000000002000020000000000000000000000000000000000000000000000000000000004000000000102000000000000000000000020000000000400020000000000000000000400000000000000010010000000000000000000000000000000000000000000000000000002000000000000000000010802010000000000000000000000000000000000000000010004000000000000000002000800000000000000000000000000000000000000000020000000000000000000000000004020000000000000000010000004000000000000000000000000000004000000020000000000000000000100000000000000000010000000020400000400000000000000000000002000000000000000000000000000000000000000000000000000000000000000000000000000000000000100000000000000000000040000000040000000002000000000000000000000000000000000000000000000000000000004004000000002000000000020000000000000000000000000000000000000000100000000000000000000100000000000000000000000000000000000000000000000000000000000000000000004000000000000000000000000000000000200000020000000000000000000000002000000000000000000000002000000000000000000000000010000000040000000000000000002000000000000000000000000100000000000000000000000000000000000000000000400000400000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000240002000000000000000000000000000000000000000000000000000000000000000000200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000022000000000

def inC (x : ℕ) : Bool := mask.testBit x || s2m x == x

def reachF : ℕ → ℕ → Bool
  | 0, x => inC x
  | f + 1, x => inC x || reachF f (s2m x)


lemma s2_eq_m (n : ℕ) (h : n < 30000) : s2 n = s2m n := s2_eq_s2f 6 n (by norm_num; omega)

lemma cyc_ok : ∀ c ∈ cs, c ≠ [] ∧ c.Nodup ∧ c.map s2m = c.rotate 1 := by decide +kernel

lemma flat_nodup : cs.flatten.Nodup := by decide +kernel

lemma len_ok : cs.map List.length = [2, 2, 4, 5, 5, 6, 10, 14, 35, 56] := by decide +kernel

lemma closed_ok : ∀ x ∈ cs.flatten, s2m x ∈ cs.flatten := by decide +kernel

lemma flat_small : ∀ x ∈ cs.flatten, x < 30000 := by decide +kernel

set_option maxHeartbeats 0 in
lemma mask_chk : (List.range 30000).all (fun x => !mask.testBit x || cs.flatten.contains x) = true := by
  decide +kernel

def chunk (k : ℕ) : Bool := (List.range 1000).all (fun i => reachF 100 (k * 1000 + i))

lemma chunk0 : chunk 0 = true := by decide +kernel

lemma chunk1 : chunk 1 = true := by decide +kernel

lemma chunk2 : chunk 2 = true := by decide +kernel

lemma chunk3 : chunk 3 = true := by decide +kernel

lemma chunk4 : chunk 4 = true := by decide +kernel

lemma chunk5 : chunk 5 = true := by decide +kernel

lemma chunk6 : chunk 6 = true := by decide +kernel

lemma chunk7 : chunk 7 = true := by decide +kernel

lemma chunk8 : chunk 8 = true := by decide +kernel

lemma chunk9 : chunk 9 = true := by decide +kernel

lemma chunk10 : chunk 10 = true := by decide +kernel

lemma chunk11 : chunk 11 = true := by decide +kernel

lemma chunk12 : chunk 12 = true := by decide +kernel

lemma chunk13 : chunk 13 = true := by decide +kernel

lemma chunk14 : chunk 14 = true := by decide +kernel

lemma chunk15 : chunk 15 = true := by decide +kernel

lemma chunk16 : chunk 16 = true := by decide +kernel

lemma chunk17 : chunk 17 = true := by decide +kernel

lemma chunk18 : chunk 18 = true := by decide +kernel

lemma chunk19 : chunk 19 = true := by decide +kernel

lemma chunk20 : chunk 20 = true := by decide +kernel

lemma chunk21 : chunk 21 = true := by decide +kernel

lemma chunk22 : chunk 22 = true := by decide +kernel

lemma chunk23 : chunk 23 = true := by decide +kernel

lemma chunk24 : chunk 24 = true := by decide +kernel

lemma chunk25 : chunk 25 = true := by decide +kernel

lemma chunk26 : chunk 26 = true := by decide +kernel

lemma chunk27 : chunk 27 = true := by decide +kernel

lemma chunk28 : chunk 28 = true := by decide +kernel

lemma chunk29 : chunk 29 = true := by decide +kernel

lemma chunks (k : ℕ) (hk : k < 30) : chunk k = true := by
  interval_cases k
  · exact chunk0
  · exact chunk1
  · exact chunk2
  · exact chunk3
  · exact chunk4
  · exact chunk5
  · exact chunk6
  · exact chunk7
  · exact chunk8
  · exact chunk9
  · exact chunk10
  · exact chunk11
  · exact chunk12
  · exact chunk13
  · exact chunk14
  · exact chunk15
  · exact chunk16
  · exact chunk17
  · exact chunk18
  · exact chunk19
  · exact chunk20
  · exact chunk21
  · exact chunk22
  · exact chunk23
  · exact chunk24
  · exact chunk25
  · exact chunk26
  · exact chunk27
  · exact chunk28
  · exact chunk29

lemma reach_ok (n : ℕ) (hn : n < 30000) : reachF 100 n = true := by
  have h1 := chunks (n / 1000) (by omega)
  have h2 := List.all_eq_true.mp h1 (n % 1000) (List.mem_range.mpr (by omega))
  have : n / 1000 * 1000 + n % 1000 = n := by omega
  rwa [this] at h2

lemma mask_flat (x : ℕ) (hx : x < 30000) (h : mask.testBit x = true) : x ∈ cs.flatten := by
  have := List.all_eq_true.mp mask_chk x (List.mem_range.mpr hx)
  simpa [h] using this

lemma closed_s2 (x : ℕ) (hx : x ∈ cs.flatten) : s2 x ∈ cs.flatten := by
  rw [s2_eq_m x (flat_small x hx)]; exact closed_ok x hx

lemma reachF_spec : ∀ f x, x < 30000 → reachF f x = true → ∃ t, inC (s2^[t] x) = true
  | 0, x, _, h => ⟨0, by simpa [reachF] using h⟩
  | f + 1, x, hx, h => by
    by_cases hc : inC x = true
    · exact ⟨0, by simpa using hc⟩
    · have h' : reachF f (s2m x) = true := by
        simp only [reachF, hc] at h
        simpa using h
      rw [← s2_eq_m x hx] at h'
      obtain ⟨t, ht⟩ := reachF_spec f (s2 x) (s2_small x hx) h'
      exact ⟨t + 1, by rw [Function.iterate_succ_apply]; exact ht⟩

lemma evper (n : ℕ) : ∃ k m, 0 < m ∧ s2^[k + m] n = s2^[k] n := by
  obtain ⟨k, hk⟩ := reach_small n
  have hf : (Set.Iio 30000 : Set ℕ).Finite := Set.finite_Iio _
  obtain ⟨a, b, hab, h⟩ := Set.Finite.exists_lt_map_eq_of_forall_mem
    (f := fun i => s2^[i] (s2^[k] n)) (t := Set.Iio 30000) (fun i => iter_small _ hk i) hf
  refine ⟨k + a, b - a, by omega, ?_⟩
  have e1 : s2^[k + a + (b - a)] n = s2^[b] (s2^[k] n) := by
    rw [show k + a + (b - a) = b + k by omega, Function.iterate_add_apply]
  have e2 : s2^[k + a] n = s2^[a] (s2^[k] n) := by
    rw [add_comm, Function.iterate_add_apply]
  rw [e1, e2]; exact h.symm

lemma periodic_small (n m : ℕ) (hm : 0 < m) (h : s2^[m] n = n) : n < 30000 := by
  by_contra hn
  push_neg at hn
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  have := dec_iter m' n hn
  omega

lemma last_part (n : ℕ) (hp : ∃ m, 0 < m ∧ s2^[m] n = n) (hne : s2 n ≠ n) : n ∈ cs.flatten := by
  obtain ⟨m, hm, hmn⟩ := hp
  have hn := periodic_small n m hm hmn
  have hr := reach_ok n hn
  obtain ⟨t, ht⟩ := reachF_spec 100 n hn hr
  have hy : s2^[t] n < 30000 := iter_small n hn t
  have hper : Function.IsPeriodicPt s2 (m * (t + 1)) n :=
    (show Function.IsPeriodicPt s2 m n from hmn).mul_const (t + 1)
  have hnn : s2^[m * (t + 1) - t] (s2^[t] n) = n := by
    have htm : t ≤ m * (t + 1) := by nlinarith
    rw [← Function.iterate_add_apply, show m * (t + 1) - t + t = m * (t + 1) by omega]
    exact hper
  simp only [inC, Bool.or_eq_true, beq_iff_eq] at ht
  rcases ht with hmk | hfix
  · have hmem := mask_flat _ hy hmk
    have hcl : ∀ a, s2^[a] (s2^[t] n) ∈ cs.flatten := by
      intro a
      induction a with
      | zero => simpa using hmem
      | succ a ih => rw [Function.iterate_succ_apply']; exact closed_s2 _ ih
    rw [← hnn]; exact hcl _
  · exfalso
    have hfix' : s2 (s2^[t] n) = s2^[t] n := by rw [s2_eq_m _ hy]; exact hfix
    have : s2^[m * (t + 1) - t] (s2^[t] n) = s2^[t] n := Function.iterate_fixed hfix' _
    rw [this] at hnn
    rw [hnn] at hfix'
    exact hne hfix'

end OMA.S_oeis_a257810

theorem OMA.solution : type_of% @OMA.S_oeis_a257810.main := by
  refine ⟨OMA.S_oeis_a257810.evper, OMA.S_oeis_a257810.cs, OMA.S_oeis_a257810.len_ok, ?_,
    OMA.S_oeis_a257810.flat_nodup, ?_⟩
  · intro c hc
    obtain ⟨h1, h2, h3⟩ := OMA.S_oeis_a257810.cyc_ok c hc
    refine ⟨h1, h2, ?_⟩
    rw [← h3]
    apply List.map_congr_left
    intro x hx
    exact OMA.S_oeis_a257810.s2_eq_m x
      (OMA.S_oeis_a257810.flat_small x (List.mem_flatten.mpr ⟨c, hc, hx⟩))
  · intro n hp hne
    exact OMA.S_oeis_a257810.last_part n hp hne
