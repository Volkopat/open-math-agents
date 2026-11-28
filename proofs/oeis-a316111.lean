import OMAStatements.S_oeis_a316111
import Mathlib

-- Problem: OEIS A316111, conjecture of Ordowski: each term k = a(n) (the smallest k > 1 with
-- gcd(k, n^k - n) = 1, for n > 1) is a term of A121707 (k^3 | Sum_{j=1..k-1} j^k), and k is an
-- anti-Carmichael number (p - 1 does not divide k - 1 for every prime p that divides k).
-- Statement: statements/oeis-a316111.lean (declaration OMA.S_oeis_a316111.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let k > 1 and b > 1 with gcd(k, b^k - b) = 1 (the minimality of k is not necessary).
-- The number b^k - b = b (b^(k-1) - 1) is even, thus k is odd, k >= 3, gcd(k, b) = 1 and
-- gcd(k, b^(k-1) - 1) = 1.
-- Step 1. Let S = Sum_{x in Z/kZ} x^(k-1). The map x -> b x is a permutation of Z/kZ, thus
-- S = b^(k-1) S. The element b^(k-1) - 1 is a unit of Z/kZ, thus S = 0.
-- Step 2. For an odd k and an integer j, the binomial theorem gives
-- (k - j)^k + j^k == k^2 j^(k-1) (mod k^3), because k divides C(k, 2).
-- Step 3. Let T = Sum_{j=1..k-1} j^k. The map j -> k - j gives
-- 2 T == k^2 Sum_{j=1..k-1} j^(k-1) == 0 (mod k^3). The number k is odd, thus k^3 divides T.
-- Anti-Carmichael. If a prime p divides k and p - 1 divides k - 1, then b^k == b (mod p) by
-- Fermat, thus p divides gcd(k, b^k - b) = 1, which is not possible.

namespace OMA.A316111

open Finset

lemma sum_Icc_eq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k = ∑ j ∈ range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

lemma zmod_sum (n m b : ℕ) [NeZero n] (hb : 0 < b) (h2 : Nat.Coprime b n)
    (hc : Nat.Coprime (b ^ m - 1) n) : ∑ x : ZMod n, x ^ m = 0 := by
  have hu : ((ZMod.unitOfCoprime b h2 : (ZMod n)ˣ) : ZMod n) = b := by
    rw [ZMod.coe_unitOfCoprime]
  have h1 : ∑ x : ZMod n, (((ZMod.unitOfCoprime b h2 : (ZMod n)ˣ) : ZMod n) * x) ^ m
      = ∑ x : ZMod n, x ^ m :=
    Equiv.sum_comp (Units.mulLeft (ZMod.unitOfCoprime b h2)) (fun x => x ^ m)
  simp only [mul_pow, ← mul_sum, hu] at h1
  have hv : ((ZMod.unitOfCoprime (b ^ m - 1) hc : (ZMod n)ˣ) : ZMod n) = (b : ZMod n) ^ m - 1 := by
    rw [ZMod.coe_unitOfCoprime, Nat.cast_sub (Nat.one_le_pow _ _ hb)]; push_cast; ring
  have h3 : ((ZMod.unitOfCoprime (b ^ m - 1) hc : (ZMod n)ˣ) : ZMod n) * ∑ x : ZMod n, x ^ m
      = 0 := by
    rw [hv]; linear_combination h1
  exact (Units.mul_right_eq_zero _).1 h3

lemma range_sum_zmod (n : ℕ) [NeZero n] (f : ZMod n → ZMod n) :
    ∑ k ∈ range n, f (k : ZMod n) = ∑ x : ZMod n, f x := by
  symm
  apply Finset.sum_bij (fun x _ => x.val)
  · intro x _; exact mem_range.2 (ZMod.val_lt x)
  · intro x _ y _ h; exact ZMod.val_injective n h
  · intro k hk; exact ⟨(k : ZMod n), mem_univ _, ZMod.val_natCast_of_lt (mem_range.1 hk)⟩
  · intro x _; rw [ZMod.natCast_zmod_val]

lemma term (n : ℕ) (hodd : Odd n) (hn : 3 ≤ n) (k : ℤ) :
    (n : ℤ) ^ 3 ∣ ((n : ℤ) - k) ^ n + k ^ n - (n : ℤ) ^ 2 * k ^ (n - 1) := by
  obtain ⟨t, ht⟩ := hodd
  have hch : (n.choose 2 : ℤ) = n * t := by
    have h : n.choose 2 = n * t := by
      rw [Nat.choose_two_right, ht]
      have : (2 * t + 1) * (2 * t + 1 - 1) = 2 * ((2 * t + 1) * t) := by
        rw [Nat.add_sub_cancel]; ring
      rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    exact_mod_cast h
  have h := add_pow (n : ℤ) (-k) n
  have hsplit : ∑ j ∈ range (n + 1), (n : ℤ) ^ j * (-k) ^ (n - j) * (n.choose j : ℤ)
      = (∑ i ∈ range (n - 2),
          (n : ℤ) ^ (i + 3) * (-k) ^ (n - (i + 3)) * (n.choose (i + 3) : ℤ))
        + (n : ℤ) ^ 2 * (-k) ^ (n - 2) * (n.choose 2 : ℤ) + (n : ℤ) * (-k) ^ (n - 1) * n
        + (-k) ^ n := by
    have e : n + 1 = (n - 2) + 1 + 1 + 1 := by omega
    rw [e, sum_range_succ', sum_range_succ', sum_range_succ']
    simp
  rw [hsplit] at h
  have hR : (n : ℤ) ^ 3 ∣ ∑ i ∈ range (n - 2),
      (n : ℤ) ^ (i + 3) * (-k) ^ (n - (i + 3)) * (n.choose (i + 3) : ℤ) :=
    dvd_sum (fun i _ => Dvd.dvd.mul_right (Dvd.dvd.mul_right (pow_dvd_pow _ (by omega)) _) _)
  obtain ⟨c, hc⟩ := hR
  have e1 : (-k) ^ n = -k ^ n := Odd.neg_pow ⟨t, ht⟩ k
  have e2 : (-k) ^ (n - 1) = k ^ (n - 1) := Even.neg_pow ⟨t, by omega⟩ k
  have e3 : (n : ℤ) - k = n + -k := by ring
  rw [e3, h, hc, hch, e1, e2]
  exact ⟨c + (-k) ^ (n - 2) * t, by ring⟩

theorem cube_dvd (n b : ℕ) (hn : 1 < n) (hb : 1 < b) (hg : Nat.gcd n (b ^ n - b) = 1) :
    n ^ 3 ∣ ∑ k ∈ Icc 1 (n - 1), k ^ n := by
  have e2n : b ^ n - b = b * (b ^ (n - 1) - 1) := by
    have : b ^ n = b * b ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this, Nat.mul_sub, mul_one]
  have hle : b ≤ b ^ n := Nat.le_self_pow (by omega) b
  have hodd : Odd n := by
    by_contra h
    rw [Nat.not_odd_iff_even] at h
    have h2 : 2 ∣ n := h.two_dvd
    have h3 : 2 ∣ b ^ n - b := by
      apply Even.two_dvd
      rw [Nat.even_sub hle, Nat.even_pow]
      constructor
      · intro h'; exact h'.1
      · intro h'; exact ⟨h', by omega⟩
    have := Nat.dvd_gcd h2 h3
    rw [hg] at this; omega
  have h3 : 3 ≤ n := by obtain ⟨t, ht⟩ := hodd; omega
  have hne : NeZero n := ⟨by omega⟩
  have h2c : Nat.Coprime 2 n := Nat.coprime_two_left.2 hodd
  rw [e2n] at hg
  have hbc : Nat.Coprime b n := (Nat.Coprime.coprime_mul_right_right hg).symm
  have hc : Nat.Coprime (b ^ (n - 1) - 1) n :=
    (Nat.Coprime.coprime_mul_left_right hg).symm
  have hS : (n : ℤ) ∣ ∑ k ∈ range n, (k : ℤ) ^ (n - 1) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).1
    push_cast
    rw [range_sum_zmod n (fun x => x ^ (n - 1))]
    exact zmod_sum n (n - 1) b (by omega) hbc hc
  rw [sum_Icc_eq_range]
  have hrefl := sum_range_reflect (fun j => (j + 1) ^ n) (n - 1)
  have a1 : ∑ j ∈ range (n - 1), ((n : ℤ) - ((j : ℤ) + 1)) ^ n
      = ((∑ j ∈ range (n - 1), (j + 1) ^ n : ℕ) : ℤ) := by
    rw [← hrefl]; push_cast
    apply sum_congr rfl
    intro j hj
    have hj' := mem_range.1 hj
    have e : n - 1 - 1 - j + 1 = n - (j + 1) := by omega
    have e' : ((n - 1 - 1 - j : ℕ) : ℤ) + 1 = (n : ℤ) - ((j : ℤ) + 1) := by
      have := congrArg (fun x : ℕ => (x : ℤ)) e
      simp only [Nat.cast_add, Nat.cast_one] at this
      rw [this, Nat.cast_sub (by omega)]; push_cast; ring
    rw [e']
  have a3 : ∑ k ∈ range n, (k : ℤ) ^ (n - 1)
      = ∑ j ∈ range (n - 1), ((j : ℤ) + 1) ^ (n - 1) := by
    have e : n = (n - 1) + 1 := by omega
    conv_lhs => rw [e, sum_range_succ']
    have : ((0 : ℕ) : ℤ) ^ (n - 1 + 1 - 1) = 0 := by
      rw [Nat.cast_zero]; exact zero_pow (by omega)
    rw [this, add_zero]
    apply sum_congr rfl
    intro j _
    push_cast
    congr 1
  have h2T : (n : ℤ) ^ 3 ∣ 2 * ((∑ j ∈ range (n - 1), (j + 1) ^ n : ℕ) : ℤ) := by
    have e : 2 * ((∑ j ∈ range (n - 1), (j + 1) ^ n : ℕ) : ℤ)
        = ∑ j ∈ range (n - 1), (((n : ℤ) - ((j : ℤ) + 1)) ^ n + ((j : ℤ) + 1) ^ n
            - (n : ℤ) ^ 2 * ((j : ℤ) + 1) ^ (n - 1))
          + (n : ℤ) ^ 2 * ∑ k ∈ range n, (k : ℤ) ^ (n - 1) := by
      rw [sum_sub_distrib, sum_add_distrib, ← mul_sum, a1, a3]
      push_cast; ring
    rw [e]
    apply dvd_add
    · exact dvd_sum (fun j _ => term n hodd h3 _)
    · obtain ⟨s, hs⟩ := hS
      rw [hs]; exact ⟨s, by ring⟩
  have hcop : IsCoprime (((n ^ 3 : ℕ) : ℤ)) ((2 : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 (Nat.Coprime.pow_left 3 h2c.symm)
  have h4 : ((n ^ 3 : ℕ) : ℤ) ∣ ((2 : ℕ) : ℤ) * ((∑ j ∈ range (n - 1), (j + 1) ^ n : ℕ) : ℤ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat]; exact h2T
  exact Int.natCast_dvd_natCast.1 (hcop.dvd_of_dvd_mul_left h4)

lemma anti (n k p : ℕ) (hn : 1 < n) (hk : 1 < k) (hg : Nat.gcd k (n ^ k - n) = 1)
    (hp : p.Prime) (hpk : p ∣ k) : ¬ (p - 1 ∣ k - 1) := by
  rintro ⟨j, hj⟩
  have hfp : Fact p.Prime := ⟨hp⟩
  have hle : n ≤ n ^ k := Nat.le_self_pow (by omega) n
  have hpow : (n : ZMod p) ^ k = n := by
    by_cases h0 : (n : ZMod p) = 0
    · rw [h0, zero_pow (by omega)]
    · have e : k = (p - 1) * j + 1 := by omega
      rw [e, pow_succ, pow_mul, ZMod.pow_card_sub_one_eq_one h0, one_pow, one_mul]
  have hd : p ∣ n ^ k - n := by
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hle]
    push_cast; rw [hpow]; ring
  have := Nat.dvd_gcd hpk hd
  rw [hg] at this
  exact hp.one_lt.ne' (Nat.dvd_one.1 this)

theorem main' (n k : ℕ) (hn : 1 < n)
    (h : IsLeast {k : ℕ | 1 < k ∧ Nat.gcd k (n ^ k - n) = 1} k) :
    (1 < k ∧ k ^ 3 ∣ ∑ j ∈ Icc 1 (k - 1), j ^ k) ∧
    ∀ p : ℕ, p.Prime → p ∣ k → ¬ (p - 1 ∣ k - 1) := by
  obtain ⟨hk, hg⟩ := h.1
  exact ⟨⟨hk, cube_dvd k n hk hn hg⟩, fun p hp hpk => anti n k p hn hk hg hp hpk⟩

end OMA.A316111

theorem OMA.solution : type_of% @OMA.S_oeis_a316111.main :=
  fun n k hn h => OMA.A316111.main' n k hn h
