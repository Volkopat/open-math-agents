import OMAStatements.S_mo_440995
import Mathlib

-- Problem: mo-440995, for a prime p = 1 (mod 4) the sum of all a in [0, p] at which the
-- sequence a^2 mod p descends equals 7 (p^2 - 1) / 24.
-- Based on @ivillar (#10578), with the main proof by @caa1982 (#22625) also inspected.
-- Finite equivalence and sum APIs shorten the residue bookkeeping.
--
-- Write r(a) = a^2 mod p, D(a) = [r(a+1) < r(a)], E(a) = [p <= 2a+1]. For a < p one has
-- r(a+1) - r(a) = 2a + 1 - p (D(a) + E(a)). Summation by parts gives
-- sum_{a<p} a (r(a+1) - r(a)) = - sum_{a<p} r(a) = - p (p - 1) / 2, the last step because
-- multiplication by a square root of -1 pairs each nonzero residue r with p - r. Solving for
-- sum a D(a) and evaluating the elementary sums with p = 4m + 1 gives 7 m (2m + 1) / 3.

namespace MO440995

lemma step (p a : ℕ) (hp : 0 < p) (ha : a < p) :
    (((a + 1) ^ 2 % p : ℕ) : ℤ) - ((a ^ 2 % p : ℕ) : ℤ)
      = 2 * (a : ℤ) + 1 - (p : ℤ) * ((if (a + 1) ^ 2 % p < a ^ 2 % p then (1 : ℤ) else 0)
          + (if p ≤ 2 * a + 1 then (1 : ℤ) else 0)) := by
  have h1 : (a + 1) ^ 2 % p = (a ^ 2 % p + (2 * a + 1)) % p := by
    have e : (a + 1) ^ 2 = a ^ 2 + (2 * a + 1) := by ring
    rw [e, Nat.mod_add_mod]
  have hr0 : a ^ 2 % p < p := Nat.mod_lt _ hp
  obtain ⟨r0, hr0def⟩ : ∃ r0, r0 = a ^ 2 % p := ⟨_, rfl⟩
  rw [h1, ← hr0def]
  rw [← hr0def] at hr0
  by_cases c1 : r0 + (2 * a + 1) < p
  · rw [Nat.mod_eq_of_lt c1]
    split_ifs <;> omega
  · by_cases c2 : r0 + (2 * a + 1) < 2 * p
    · have e : (r0 + (2 * a + 1)) % p = r0 + (2 * a + 1) - p := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
      rw [e]
      split_ifs <;> omega
    · have e : (r0 + (2 * a + 1)) % p = r0 + (2 * a + 1) - 2 * p := by
        rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_sub_mod (by omega),
          Nat.mod_eq_of_lt (by omega)]
        omega
      rw [e]
      split_ifs <;> omega

lemma sum_sq_mod (p : ℕ) (hp : p.Prime) (hp4 : p % 4 = 1) :
    2 * ∑ a ∈ Finset.range p, (a ^ 2 % p) = p * (p - 1) := by
  have hfact : Fact p.Prime := ⟨hp⟩
  have h1 : ∑ a ∈ Finset.range p, (a ^ 2 % p) = ∑ x : ZMod p, (x ^ 2).val := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact (Fintype.sum_equiv (ZMod.finEquiv p).toEquiv _ _ fun a => by
      change a.val ^ 2 % p = (((ZMod.finEquiv p) a) ^ 2).val
      cases p with
      | zero => exact (hp.ne_zero rfl).elim
      | succ p => simp only [sq]; rfl)
  obtain ⟨i, hi⟩ : ∃ i : ZMod p, i ^ 2 = -1 := by
    have hsq : IsSquare (-1 : ZMod p) := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega)
    obtain ⟨i, hi⟩ := hsq
    exact ⟨i, by rw [hi, sq]⟩
  have hi0 : i ≠ 0 := by rintro rfl; simp at hi
  have h2 : ∑ x : ZMod p, (x ^ 2).val = ∑ x : ZMod p, (-(x ^ 2)).val := by
    rw [← Equiv.sum_comp (Equiv.mulLeft₀ i hi0) (fun x : ZMod p => (x ^ 2).val)]
    refine Finset.sum_congr rfl fun x _ => ?_
    show ((i * x) ^ 2).val = (-(x ^ 2)).val
    rw [mul_pow, hi, neg_one_mul]
  have hterm : ∀ x : ZMod p, (x ^ 2).val + (-(x ^ 2)).val = if x = 0 then 0 else p := by
    intro x
    rw [ZMod.neg_val]
    by_cases hx : x = 0
    · simp [hx]
    · have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
      rw [if_neg hx2, if_neg hx]
      have h := ZMod.val_lt (x ^ 2)
      omega
  have h3 : ∑ x : ZMod p, ((x ^ 2).val + (-(x ^ 2)).val) = p * (p - 1) := by
    simp [hterm, Finset.sum_ite, Finset.filter_ne', Nat.mul_comm]
  calc 2 * ∑ a ∈ Finset.range p, (a ^ 2 % p)
      = ∑ x : ZMod p, (x ^ 2).val + ∑ x : ZMod p, (x ^ 2).val := by rw [h1, two_mul]
    _ = ∑ x : ZMod p, (x ^ 2).val + ∑ x : ZMod p, (-(x ^ 2)).val := by rw [← h2]
    _ = p * (p - 1) := by rw [← Finset.sum_add_distrib, h3]

lemma abel (f : ℕ → ℤ) (n : ℕ) :
    ∑ a ∈ Finset.range n, (a : ℤ) * (f (a + 1) - f a)
      = n * f n - ∑ a ∈ Finset.range n, f (a + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    push_cast
    ring

lemma sum_poly (n : ℕ) :
    6 * ∑ a ∈ Finset.range n, (a : ℤ) * (2 * a + 1) = n * (n - 1) * (4 * n + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    push_cast
    ring

lemma sum_E (m : ℕ) : ∀ n : ℕ, 2 * m ≤ n →
    2 * ∑ a ∈ Finset.range n, (a : ℤ) * (if 4 * m + 1 ≤ 2 * a + 1 then (1 : ℤ) else 0)
      = n * (n - 1) - 2 * m * (2 * m - 1) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    have h0 : ∑ a ∈ Finset.range (2 * m),
        (a : ℤ) * (if 4 * m + 1 ≤ 2 * a + 1 then (1 : ℤ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro a ha
      rw [Finset.mem_range] at ha
      rw [if_neg (by omega), mul_zero]
    rw [h0]
    push_cast
    ring
  | succ n hn ih =>
    rw [Finset.sum_range_succ, mul_add, ih, if_pos (by omega)]
    push_cast
    ring

end MO440995

theorem OMA.solution : type_of% @OMA.S_mo_440995.main := by
  intro p hp hp4
  obtain ⟨m, hm⟩ : ∃ m, p = 4 * m + 1 := ⟨p / 4, by omega⟩
  have hpos : 0 < p := hp.pos
  -- the descent sum as a sum over range p
  have hdesc : ((∑ n ∈ OMA.S_mo_440995.descentSet p, n : ℕ) : ℤ)
      = ∑ a ∈ Finset.range p,
          (a : ℤ) * (if (a + 1) ^ 2 % p < a ^ 2 % p then (1 : ℤ) else 0) := by
    unfold OMA.S_mo_440995.descentSet
    rw [Finset.sum_filter, Finset.sum_range_succ]
    have hlast : ¬ ((p + 1) ^ 2 % p < p ^ 2 % p) := by
      have e : p ^ 2 % p = 0 := by rw [sq]; exact Nat.mul_mod_right p p
      rw [e]
      exact Nat.not_lt_zero _
    rw [if_neg hlast, add_zero]
    push_cast
    refine Finset.sum_congr rfl fun a _ => ?_
    split_ifs <;> simp
  -- summation by parts
  have hab := MO440995.abel (fun a => ((a ^ 2 % p : ℕ) : ℤ)) p
  have hpp : p ^ 2 % p = 0 := by rw [sq]; exact Nat.mul_mod_right p p
  have hshift : ∑ a ∈ Finset.range p, (((a + 1) ^ 2 % p : ℕ) : ℤ)
      = ∑ a ∈ Finset.range p, ((a ^ 2 % p : ℕ) : ℤ) := by
    have h1 := Finset.sum_range_succ (fun a => ((a ^ 2 % p : ℕ) : ℤ)) p
    have h2 := Finset.sum_range_succ' (fun a => ((a ^ 2 % p : ℕ) : ℤ)) p
    simp only [hpp] at h1
    rw [h1] at h2
    simpa using h2.symm
  have hsq := MO440995.sum_sq_mod p hp hp4
  have hsq' : 2 * ∑ a ∈ Finset.range p, ((a ^ 2 % p : ℕ) : ℤ) = (p : ℤ) * (p - 1) := by
    zify [hp.one_lt.le] at hsq
    exact hsq
  have hstep : ∑ a ∈ Finset.range p,
      (a : ℤ) * ((((a + 1) ^ 2 % p : ℕ) : ℤ) - ((a ^ 2 % p : ℕ) : ℤ))
      = ∑ a ∈ Finset.range p, (a : ℤ) * (2 * a + 1)
        - p * ∑ a ∈ Finset.range p,
            (a : ℤ) * (if (a + 1) ^ 2 % p < a ^ 2 % p then (1 : ℤ) else 0)
        - p * ∑ a ∈ Finset.range p,
            (a : ℤ) * (if p ≤ 2 * a + 1 then (1 : ℤ) else 0) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [MO440995.step p a hpos (Finset.mem_range.mp ha)]
    ring
  have hpoly := MO440995.sum_poly p
  have hE := MO440995.sum_E m p (by omega)
  simp only [hpp, Nat.cast_zero, mul_zero] at hab
  rw [hshift] at hab
  rw [hstep] at hab
  -- solve for the descent sum
  have hpZ : (p : ℤ) = 4 * m + 1 := by exact_mod_cast hm
  have hE' : 2 * ∑ a ∈ Finset.range p,
      (a : ℤ) * (if p ≤ 2 * a + 1 then (1 : ℤ) else 0)
      = (p : ℤ) * (p - 1) - 2 * m * (2 * m - 1) := by
    have h := hE
    rw [← hm] at h
    exact h
  have key : (p : ℤ) * (6 * ∑ a ∈ Finset.range p,
      (a : ℤ) * (if (a + 1) ^ 2 % p < a ^ 2 % p then (1 : ℤ) else 0))
      = (p : ℤ) * (14 * m * (2 * m + 1)) := by
    rw [hpZ] at hpoly hE' hsq' hab ⊢
    linear_combination (-6) * hab + hpoly + (-3 * (4 * (m : ℤ) + 1)) * hE' + 3 * hsq'
  have hp0 : (p : ℤ) ≠ 0 := by positivity
  have key2 := mul_left_cancel₀ hp0 key
  have hZ : ((∑ n ∈ OMA.S_mo_440995.descentSet p, n : ℕ) : ℤ) * 6
      = 14 * (m : ℤ) * (2 * m + 1) := by
    rw [hdesc]
    linarith [key2]
  have hQ : ((∑ n ∈ OMA.S_mo_440995.descentSet p, n : ℕ) : ℚ) * 6
      = 14 * (m : ℚ) * (2 * m + 1) := by
    exact_mod_cast hZ
  have hpQ : (p : ℚ) = 4 * m + 1 := by exact_mod_cast hm
  rw [hpQ]
  linear_combination (1 / 6 : ℚ) * hQ
