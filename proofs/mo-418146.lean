import OMAStatements.S_mo_418146
import Mathlib

namespace JosephusRank

open OMA.S_mo_418146

private theorem round (k x : ℕ) :
    ((x : ℤ) - (k : ℤ) - ((x % k : ℕ) : ℤ)).natAbs =
      k * (((x / k : ℕ) : ℤ) - 1).natAbs := by
  rw [← Int.natAbs_natCast k, ← Int.natAbs_mul]
  congr 1
  have h := Nat.div_add_mod x k
  exact_mod_cast (show (x : ℤ) - (k : ℤ) - ((x % k : ℕ) : ℤ) =
      (k : ℤ) * (((x / k : ℕ) : ℤ) - 1) by
    push_cast at h ⊢
    linarith [h])

private theorem abs_sub_one (x : ℕ) (hx : 1 ≤ x) :
    (((x : ℤ) - 1).natAbs) = x - 1 := by
  simpa using congrArg Int.natAbs (Int.ofNat_sub hx).symm

private theorem b_next (q x : ℕ) :
    b (q + 1) x = (q + 1) * (((b q x / (q + 1) : ℕ) : ℤ) - 1).natAbs :=
  round (q + 1) (b q x)

private theorem shifted_quotient (k r : ℕ) (hk : k ≤ r) :
    k * (r - k) / (k + 1) = r - r / (k + 1) - k := by
  by_cases hkr : r = k
  · subst r
    simp [Nat.div_eq_of_lt (show k < k + 1 by omega)]
  let q := r / (k + 1)
  let m := r % (k + 1)
  have hm : m < k + 1 := Nat.mod_lt _ (by omega)
  have hq : 0 < q := Nat.div_pos (by omega) (by omega)
  have hr : (k + 1) * q + m = r := Nat.div_add_mod r (k + 1)
  have hmul : k ≤ k * q := by simpa using Nat.mul_le_mul_left k (show 1 ≤ q by omega)
  have hbound : k + q ≤ r := by
    rw [Nat.add_mul, one_mul] at hr
    omega
  have heq : k * (r - k) = (k - m) + (k + 1) * (r - q - k) := by
    have hrk : r - k + k = r := Nat.sub_add_cancel hk
    have hrqk : r - q - k + k + q = r := by omega
    have hkm : k - m + m = k := Nat.sub_add_cancel (by omega)
    zify at hr hrk hrqk hkm ⊢
    linarith [congrArg (fun x : ℤ => (k : ℤ) * x) hrk,
      congrArg (fun x : ℤ => ((k : ℤ) + 1) * x) hrqk]
  rw [heq, Nat.add_mul_div_left _ _ (by omega : 0 < k + 1),
    Nat.div_eq_of_lt (show k - m < k + 1 by omega), zero_add]

private theorem prev_quotient (k r : ℕ) (hr : k < r) :
    (r - 1) / (k + 1) =
      if r % (k + 1) = 0 then r / (k + 1) - 1 else r / (k + 1) := by
  let q := r / (k + 1)
  let m := r % (k + 1)
  change (r - 1) / (k + 1) = if m = 0 then q - 1 else q
  have hm : m < k + 1 := Nat.mod_lt _ (by omega)
  have hq : 0 < q := Nat.div_pos (by omega) (by omega)
  have hd : (k + 1) * q + m = r := Nat.div_add_mod r (k + 1)
  split_ifs with hm0
  · have hmul : (k + 1) * (q - 1) + (k + 1) = (k + 1) * q := by
      rw [← Nat.mul_succ]
      congr 1
      omega
    have heq : r - 1 = k + (k + 1) * (q - 1) := by omega
    rw [heq, Nat.add_mul_div_left _ _ (by omega : 0 < k + 1),
      Nat.div_eq_of_lt (by omega : k < k + 1), zero_add]
  · have heq : r - 1 = (m - 1) + (k + 1) * q := by omega
    rw [heq, Nat.add_mul_div_left _ _ (by omega : 0 < k + 1),
      Nat.div_eq_of_lt (show m - 1 < k + 1 by omega), zero_add]

private def State (n k : ℕ) : Prop :=
  let r := sieveRank (k - 1) n
  k ≤ r ∧ b k n = k * (r - k) ∧
    b k (n - 1) = if r = k then k else k * (r - k - 1)

private theorem state_one (n : ℕ) (hn : 0 < n) : State n 1 := by
  simp only [State, Nat.sub_self, sieveRank, one_mul, b, Nat.zero_add, Nat.mod_one, Nat.cast_one, Nat.cast_zero, sub_zero]
  refine ⟨hn, abs_sub_one n hn, ?_⟩
  split_ifs with h
  · subst n
    decide
  · rw [abs_sub_one _ (by omega)]

private theorem rank_le (n k : ℕ) : sieveRank k n ≤ n := by
  induction k with
  | zero => simp [sieveRank]
  | succ k ih =>
    simp only [sieveRank]
    split
    · exact Nat.zero_le n
    · exact (Nat.sub_le _ _).trans ih

private theorem sieve_next (n k : ℕ) (hk : 0 < k) :
    let r := sieveRank (k - 1) n
    sieveRank k n = if r % (k + 1) = 0 then 0 else r - r / (k + 1) := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hk)
  simp [sieveRank]

private theorem rank_freeze (n k : ℕ) (h : sieveRank (k - 1) n = k)
    (hk : 0 < k) : ∀ r : ℕ, k - 1 ≤ r → sieveRank r n = k := by
  suffices H : ∀ j : ℕ, sieveRank (k - 1 + j) n = k by
    intro r hr
    simpa [Nat.add_sub_of_le hr] using H (r - (k - 1))
  intro j
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [Nat.add_succ, sieveRank, ih]
    have hlt : k < k - 1 + j + 2 := by omega
    simp [Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt, Nat.ne_of_gt hk]

private theorem rank_bound (k r : ℕ) (hr : k < r) (hm : r % (k + 1) ≠ 0) :
    k + 1 ≤ r - r / (k + 1) := by
  let q := r / (k + 1)
  have hq : 1 ≤ q := Nat.div_pos (by omega) (by omega)
  have hmul : k ≤ k * q := by simpa using Nat.mul_le_mul_left k hq
  have hd : (k + 1) * q + r % (k + 1) = r := Nat.div_add_mod r (k + 1)
  rw [Nat.add_mul, one_mul] at hd
  change k + 1 ≤ r - q
  omega

private theorem transition (n k : ℕ) (hk : 0 < k) (hs : State n k) :
    let r := sieveRank (k - 1) n
    if r = k ∨ r % (k + 1) = 0 then b (k + 1) n = b (k + 1) (n - 1)
    else b (k + 1) n ≠ b (k + 1) (n - 1) ∧ State n (k + 1) := by
  let r := sieveRank (k - 1) n
  change k ≤ r ∧ b k n = k * (r - k) ∧
    b k (n - 1) = (if r = k then k else k * (r - k - 1)) at hs
  rcases hs with ⟨hle, ha, hb⟩
  change if r = k ∨ r % (k + 1) = 0 then b (k + 1) n = b (k + 1) (n - 1)
    else b (k + 1) n ≠ b (k + 1) (n - 1) ∧ State n (k + 1)
  rw [b_next, b_next, ha, hb]
  by_cases he : r = k
  · simp [he, Nat.div_eq_of_lt (show k < k + 1 by omega)]
  · have hlt : k < r := by omega
    simp only [he, false_or, if_false]
    rw [shifted_quotient k r hle,
      show r - k - 1 = r - 1 - k by omega, shifted_quotient k (r - 1) (by omega),
      prev_quotient k r hlt]
    by_cases hm : r % (k + 1) = 0
    · simp only [hm, if_pos]
      have hq : 0 < r / (k + 1) := Nat.div_pos (by omega) (by omega)
      rw [show r - 1 - (r / (k + 1) - 1) - k = r - r / (k + 1) - k by omega]
    · let s := r - r / (k + 1)
      have hs : k + 1 ≤ s := rank_bound k r hlt hm
      have hq : r / (k + 1) < r := Nat.div_lt_self (by omega) (by omega)
      simp only [hm, if_false]
      rw [show r - r / (k + 1) - k = s - k by rfl,
        show r - 1 - r / (k + 1) - k = s - k - 1 by dsimp [s]; omega,
        abs_sub_one _ (by omega)]
      have hnext : sieveRank k n = s := by
        simpa only [r, s, hm, if_false] using sieve_next n k hk
      have hmain : b (k + 1) n = (k + 1) * (s - k - 1) := by
        rw [b_next, ha, shifted_quotient k r hle, abs_sub_one _ (by change 1 ≤ s - k; omega)]
      have hprev : b (k + 1) (n - 1) = (k + 1) * (((s - k - 1 : ℕ) : ℤ) - 1).natAbs := by
        rw [b_next, hb, if_neg he, show r - k - 1 = r - 1 - k by omega,
          shifted_quotient k (r - 1) (by omega), prev_quotient k r hlt, if_neg hm]
        congr 4
        dsimp [s]
        omega
      unfold State
      rw [Nat.add_sub_cancel, hnext, hmain, hprev]
      dsimp only
      by_cases hsmall : s = k + 1
      · simp [hsmall]
      · rw [abs_sub_one _ (by omega), if_neg hsmall]
        refine ⟨?_, hs, ?_, ?_⟩
        · intro heq
          have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < k + 1) heq
          omega
        · congr 1
        · congr 1

private theorem state_of_distinct (n k : ℕ) (hn : 0 < n) (hk : 0 < k)
    (hd : ∀ j ≤ k, b j n ≠ b j (n - 1)) : State n k := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hk0 : k = 0
    · simpa [hk0] using state_one n hn
    · have hi := ih (Nat.pos_of_ne_zero hk0) (fun j hj => hd j (by omega))
      have ht := transition n k (by omega) hi
      dsimp only at ht
      split at ht
      · exact False.elim (hd (k + 1) (by omega) ht)
      · exact ht.2

theorem result : type_of% @main := by
  intro n hn
  have he : ∃ q, b q n = b q (n - 1) := by
    by_contra! h
    have hs := state_of_distinct n (n + 1) hn (by omega) (fun j _ => h j)
    have hle := rank_le n n
    have hge : n + 1 ≤ sieveRank n n := by simpa [State] using hs.1
    omega
  let q := Nat.find he
  have hq : b q n = b q (n - 1) := Nat.find_spec he
  have hm : ∀ j < q, b j n ≠ b j (n - 1) := fun j hj => Nat.find_min he hj
  have hd0 : b 0 n ≠ b 0 (n - 1) := by simp [b]; omega
  have hd1 : b 1 n ≠ b 1 (n - 1) := by
    have hs := state_one n hn
    simp only [State, Nat.sub_self, sieveRank, one_mul] at hs
    rw [hs.2.1, hs.2.2]
    split <;> omega
  have hq2 : 2 ≤ q := by
    by_contra! h
    have h' : q = 0 ∨ q = 1 := by omega
    rcases h' with h' | h'
    · exact hd0 (h' ▸ hq)
    · exact hd1 (h' ▸ hq)
  refine ⟨q, by omega, hq, hm, ?_⟩
  let k := q - 1
  have hk : 0 < k := by omega
  have hqk : k + 1 = q := by omega
  have hs := state_of_distinct n k hn hk (fun j hj => hm j (by omega))
  have ht := transition n k hk hs
  let r := sieveRank (k - 1) n
  change k ≤ r ∧ b k n = k * (r - k) ∧
    b k (n - 1) = (if r = k then k else k * (r - k - 1)) at hs
  change (if r = k ∨ r % (k + 1) = 0 then b (k + 1) n = b (k + 1) (n - 1)
    else b (k + 1) n ≠ b (k + 1) (n - 1) ∧ State n (k + 1)) at ht
  have hterm : r = k ∨ r % (k + 1) = 0 := by
    by_contra h
    rw [if_neg h] at ht
    exact ht.1 (hqk.symm ▸ hq)
  rcases hs with ⟨hle, ha, hb⟩
  dsimp only
  change (0 < (b k n : ℤ) - b k (n - 1) →
    sieveRank (((b k n : ℤ) - b k (n - 1)).toNat - 1) n ≠ 0 ∧
      sieveRank ((b k n : ℤ) - b k (n - 1)).toNat n = 0) ∧
    ((b k n : ℤ) - b k (n - 1) < 0 →
      ∃ s, ∀ t, s ≤ t → sieveRank t n = ((b k n : ℤ) - b k (n - 1)).natAbs)
  rcases hterm with hr | hz
  · have hsgn : (b k n : ℤ) - b k (n - 1) = -(k : ℤ) := by simp [ha, hb, hr]
    rw [hsgn]
    constructor
    · omega
    · intro _
      exact ⟨k - 1, by simpa using rank_freeze n k hr hk⟩
  · have hr : k < r := by
      by_contra! h
      have he : r = k := by omega
      rw [he, Nat.mod_eq_of_lt (by omega : k < k + 1)] at hz
      omega
    have hsgn : (b k n : ℤ) - b k (n - 1) = (k : ℤ) := by
      rw [ha, hb, if_neg (ne_of_gt hr)]
      have he : r - k - 1 + 1 = r - k := by omega
      rw [← he, mul_add, mul_one]
      push_cast
      ring
    rw [hsgn]
    constructor
    · intro _
      simp only [Int.toNat_natCast]
      refine ⟨by change r ≠ 0; omega, ?_⟩
      simpa only [r, hz, if_pos] using sieve_next n k hk
    · omega

end JosephusRank

theorem OMA.solution : type_of% @OMA.S_mo_418146.main :=
  JosephusRank.result