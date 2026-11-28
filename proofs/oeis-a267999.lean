import OMAStatements.S_oeis_a267999
import Mathlib

-- Problem: OEIS A267999, conjecture of Ordowski and Israel: A267999 is a subsequence of
-- A121707, that is, each n > 1 with gcd(n, 2^n - 2) = 1 satisfies n^3 | Sum_{k=1..n-1} k^n.
-- Statement: statements/oeis-a267999.lean (declaration OMA.S_oeis_a267999.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. The number n is odd, because 2 divides 2^n - 2. Thus n >= 3 and
-- gcd(n, 2^(n-1) - 1) = 1.
-- Step 1. Let S = Sum_{x in Z/nZ} x^(n-1). The map x -> 2 x is a permutation of Z/nZ, thus
-- S = 2^(n-1) S. The element 2^(n-1) - 1 is a unit of Z/nZ, thus S = 0. So n divides
-- Sum_{k=0..n-1} k^(n-1).
-- Step 2. For an odd n and an integer k, the binomial theorem gives
-- (n - k)^n + k^n == n^2 k^(n-1) (mod n^3), because n divides C(n, 2).
-- Step 3. Let T = Sum_{k=1..n-1} k^n. The map k -> n - k gives
-- 2 T = Sum_{k=1..n-1} (k^n + (n - k)^n) == n^2 Sum_{k=1..n-1} k^(n-1) == 0 (mod n^3) by
-- steps 2 and 1. The number n is odd, thus n^3 divides T.

namespace OMA.A267999

open Finset

lemma sum_Icc_eq_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ k ∈ Icc 1 n, f k = ∑ j ∈ range n, f (j + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]

lemma zmod_sum (n m : ℕ) [NeZero n] (h2 : Nat.Coprime 2 n) (hc : Nat.Coprime (2 ^ m - 1) n) :
    ∑ x : ZMod n, x ^ m = 0 := by
  have hu : ((ZMod.unitOfCoprime 2 h2 : (ZMod n)ˣ) : ZMod n) = 2 := by
    rw [ZMod.coe_unitOfCoprime]; norm_num
  have h1 : ∑ x : ZMod n, (((ZMod.unitOfCoprime 2 h2 : (ZMod n)ˣ) : ZMod n) * x) ^ m
      = ∑ x : ZMod n, x ^ m :=
    Equiv.sum_comp (Units.mulLeft (ZMod.unitOfCoprime 2 h2)) (fun x => x ^ m)
  simp only [mul_pow, ← mul_sum, hu] at h1
  have hv : ((ZMod.unitOfCoprime (2 ^ m - 1) hc : (ZMod n)ˣ) : ZMod n) = 2 ^ m - 1 := by
    rw [ZMod.coe_unitOfCoprime, Nat.cast_sub Nat.one_le_two_pow]; norm_num
  have h3 : ((ZMod.unitOfCoprime (2 ^ m - 1) hc : (ZMod n)ˣ) : ZMod n) * ∑ x : ZMod n, x ^ m
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

theorem main' (n : ℕ) (hn : 1 < n) (hg : Nat.gcd n (2 ^ n - 2) = 1) :
    n ^ 3 ∣ ∑ k ∈ Icc 1 (n - 1), k ^ n := by
  have e2n : 2 ^ n - 2 = 2 * (2 ^ (n - 1) - 1) := by
    have : 2 ^ n = 2 * 2 ^ (n - 1) := by rw [← pow_succ']; congr 1; omega
    rw [this, Nat.mul_sub, mul_one]
  have hodd : Odd n := by
    by_contra h
    rw [Nat.not_odd_iff_even] at h
    have h2 : 2 ∣ n := h.two_dvd
    have h3 : 2 ∣ 2 ^ n - 2 := by rw [e2n]; exact Dvd.intro _ rfl
    have := Nat.dvd_gcd h2 h3
    rw [hg] at this; omega
  have h3 : 3 ≤ n := by obtain ⟨t, ht⟩ := hodd; omega
  have hne : NeZero n := ⟨by omega⟩
  have h2c : Nat.Coprime 2 n := Nat.coprime_two_left.2 hodd
  have hc : Nat.Coprime (2 ^ (n - 1) - 1) n := by
    rw [e2n] at hg
    exact (Nat.Coprime.coprime_mul_left_right hg).symm
  have hS : (n : ℤ) ∣ ∑ k ∈ range n, (k : ℤ) ^ (n - 1) := by
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ n).1
    push_cast
    rw [range_sum_zmod n (fun x => x ^ (n - 1))]
    exact zmod_sum n (n - 1) h2c hc
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

end OMA.A267999

theorem OMA.solution : type_of% @OMA.S_oeis_a267999.main :=
  fun n hn hg => OMA.A267999.main' n hn hg
