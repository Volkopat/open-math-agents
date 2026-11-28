import OMAStatements.S_oeis_a242736
import Mathlib

-- Problem: OEIS A242736, a(n) = number of pairs 0 <= a <= b <= (p-1)/2 with
-- a^2 + b^2 = -1 (mod p), p the n-th prime. Conjecture: the sequence is nondecreasing.
-- Statement: statements/oeis-a242736.lean (declaration OMA.S_oeis_a242736.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. Let p be an odd prime, h = (p-1)/2, chi the quadratic character of F = Z/p, and
-- K(x, y) = 1 if x^2 + y^2 = -1 in F, and 0 otherwise.
-- * The number of (x, y) in F^2 with y^2 - x^2 = 1 is p - 1 (change of variables
--   u = y - x, v = y + x, u v = 1). The number of y with y^2 = c is chi(c) + 1, so the sum of
--   chi(1 + x^2) over x is -1, and the sum T of K over F^2 is p - chi(-1) (lemma Tcount).
-- * Folding (lemma fold): for an even function G on F, the sum of G is
--   G(0) + 2 (G(1) + ... + G(h)). With A = sum of K(i, j) over 1 <= i, j <= h,
--   Z = sum of K(0, j) and E = sum of K(i, i) over 1 <= i, j <= h, this gives T = 4 A + 4 Z,
--   2 Z = chi(-1) + 1 and 2 E = chi(-2) + 1.
-- * The count c of the statement has 2 c = (A + 2 Z) + E (pairs with a <= b, pairs with
--   b <= a, and the diagonal). Thus 8 c = p + 4 + chi(-1) + 2 chi(-2), and the values of
--   chi(-1), chi(-2) by p mod 8 give c = floor((p + 7)/8) = ceiling(p/8).
-- The count for p = 2 is 0, and floor((p + 7)/8) is nondecreasing in p.

namespace OMA.A242736

open OMA.S_oeis_a242736 Finset

section
variable {p : ℕ} [hp : Fact p.Prime]

/-- The indicator of `x^2 + y^2 = -1`. -/
def K (x y : ZMod p) : ℤ := if x ^ 2 + y ^ 2 = -1 then 1 else 0

lemma K_comm (x y : ZMod p) : K x y = K y x := by
  unfold K
  rw [add_comm]

lemma K_neg_right (x y : ZMod p) : K x (-y) = K x y := by
  unfold K
  rw [neg_sq]

lemma K_neg_left (x y : ZMod p) : K (-x) y = K x y := by
  unfold K
  rw [neg_sq]

lemma K_zero_zero : K (0 : ZMod p) 0 = 0 := by
  unfold K
  rw [if_neg]
  intro h
  rw [zero_pow two_ne_zero, add_zero, zero_eq_neg] at h
  exact one_ne_zero h

lemma ringChar_ne (hp2 : p ≠ 2) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  exact hp2

lemma two_ne (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)

lemma sqcount (hp2 : p ≠ 2) (c : ZMod p) :
    (∑ y : ZMod p, if y ^ 2 = c then (1 : ℤ) else 0) = quadraticChar (ZMod p) c + 1 := by
  rw [Finset.sum_boole, ← quadraticChar_card_sqrts (ringChar_ne hp2) c]
  congr 2
  ext y
  simp

/-- The linear change of variables `(x, y) ↦ (y - x, y + x)`. -/
def lin (hp2 : p ≠ 2) : ZMod p × ZMod p ≃ ZMod p × ZMod p where
  toFun z := (z.2 - z.1, z.2 + z.1)
  invFun w := ((w.2 - w.1) / 2, (w.1 + w.2) / 2)
  left_inv z := by
    have h2 := two_ne hp2
    ext <;> simp <;> field_simp <;> ring
  right_inv w := by
    have h2 := two_ne hp2
    ext <;> simp <;> field_simp <;> ring

lemma hyper (hp2 : p ≠ 2) :
    (∑ x : ZMod p, ∑ y : ZMod p, if y ^ 2 = 1 + x ^ 2 then (1 : ℤ) else 0) = (p : ℤ) - 1 := by
  have e1 : (∑ x : ZMod p, ∑ y : ZMod p, if y ^ 2 = 1 + x ^ 2 then (1 : ℤ) else 0)
      = ∑ z : ZMod p × ZMod p, if (lin hp2 z).1 * (lin hp2 z).2 = 1 then (1 : ℤ) else 0 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have : (y ^ 2 = 1 + x ^ 2) ↔ ((y - x) * (y + x) = 1) := by
      constructor <;> intro h <;> linear_combination h
    show (if y ^ 2 = 1 + x ^ 2 then (1 : ℤ) else 0) = if (y - x) * (y + x) = 1 then 1 else 0
    by_cases hc : y ^ 2 = 1 + x ^ 2
    · rw [if_pos hc, if_pos (this.mp hc)]
    · rw [if_neg hc, if_neg (fun h => hc (this.mpr h))]
  rw [e1, Equiv.sum_comp (lin hp2) (fun w : ZMod p × ZMod p => if w.1 * w.2 = 1 then (1 : ℤ) else 0),
    Fintype.sum_prod_type]
  have e2 : ∀ u : ZMod p, (∑ v : ZMod p, if u * v = 1 then (1 : ℤ) else 0)
      = if u = 0 then 0 else 1 := by
    intro u
    by_cases hu : u = 0
    · simp [hu]
    · rw [if_neg hu]
      have : ∀ v : ZMod p, (u * v = 1) ↔ (v = u⁻¹) := by
        intro v
        constructor
        · intro h
          field_simp
          linear_combination h
        · intro h
          rw [h]
          exact mul_inv_cancel₀ hu
      simp only [this]
      simp
  simp only [e2]
  rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.sum_const, Finset.filter_ne',
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]
  have := hp.out.pos
  simp
  omega

lemma charsum (hp2 : p ≠ 2) : ∑ x : ZMod p, quadraticChar (ZMod p) (1 + x ^ 2) = -1 := by
  have h := hyper hp2
  simp only [sqcount hp2] at h
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul,
    mul_one] at h
  linarith

lemma Tcount (hp2 : p ≠ 2) :
    (∑ x : ZMod p, ∑ y : ZMod p, K x y) = (p : ℤ) - quadraticChar (ZMod p) (-1) := by
  have e : ∀ x : ZMod p, (∑ y : ZMod p, K x y)
      = quadraticChar (ZMod p) (-1) * quadraticChar (ZMod p) (1 + x ^ 2) + 1 := by
    intro x
    have h1 : ∀ y : ZMod p, K x y = if y ^ 2 = -1 * (1 + x ^ 2) then (1 : ℤ) else 0 := by
      intro y
      unfold K
      have : (x ^ 2 + y ^ 2 = -1) ↔ (y ^ 2 = -1 * (1 + x ^ 2)) := by
        constructor <;> intro h <;> linear_combination h
      simp only [this]
    simp only [h1]
    rw [sqcount hp2, map_mul]
  simp only [e]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, charsum hp2, Finset.sum_const, Finset.card_univ,
    ZMod.card, nsmul_eq_mul, mul_one]
  ring

/-- Folding a sum of an even function over `ZMod p`, `p = 2h + 1`. -/
lemma fold (h : ℕ) (hph : p = 2 * h + 1) (G : ZMod p → ℤ) (hG : ∀ x, G (-x) = G x) :
    ∑ x : ZMod p, G x = G 0 + 2 * ∑ k ∈ range h, G ((k + 1 : ℕ) : ZMod p) := by
  have hne : NeZero p := ⟨hp.out.ne_zero⟩
  have s1 : ∑ x : ZMod p, G x = ∑ k ∈ range p, G (k : ZMod p) := by
    refine Finset.sum_nbij' (fun x => x.val) (fun k => (k : ZMod p)) ?_ ?_ ?_ ?_ ?_
    · intro x _
      exact Finset.mem_range.mpr (ZMod.val_lt x)
    · intro k _
      exact Finset.mem_univ _
    · intro x _
      exact ZMod.natCast_zmod_val x
    · intro k hk
      exact ZMod.val_cast_of_lt (Finset.mem_range.mp hk)
    · intro x _
      rw [ZMod.natCast_zmod_val]
  have s2 : ∑ k ∈ range p, G (k : ZMod p)
      = (∑ k ∈ range h, G ((k + 1 : ℕ) : ZMod p))
        + (∑ k ∈ range h, G ((h + k + 1 : ℕ) : ZMod p)) + G 0 := by
    have hp' : p = (h + h) + 1 := by omega
    rw [show range p = range (h + h + 1) from by rw [hp'], Finset.sum_range_succ',
      Finset.sum_range_add, Nat.cast_zero]
  have s3 : ∑ k ∈ range h, G ((h + k + 1 : ℕ) : ZMod p)
      = ∑ k ∈ range h, G ((k + 1 : ℕ) : ZMod p) := by
    rw [← Finset.sum_range_reflect]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' := Finset.mem_range.mp hj
    have e : h + (h - 1 - j) + 1 = p - (j + 1) := by omega
    have hle : j + 1 ≤ p := by omega
    rw [e, Nat.cast_sub hle, ZMod.natCast_self, zero_sub, hG]
  rw [s1, s2, s3]
  ring

/-- The main count in terms of quadratic characters. -/
lemma eight_cnt (hp2 : p ≠ 2) :
    8 * (cnt p : ℤ) = (p : ℤ) + 4 + quadraticChar (ZMod p) (-1)
      + 2 * quadraticChar (ZMod p) (-2) := by
  obtain ⟨h, hph⟩ : ∃ h, p = 2 * h + 1 := by
    rcases hp.out.eq_two_or_odd with h2 | ho
    · exact absurd h2 hp2
    · exact ⟨p / 2, by omega⟩
  have hh : (p - 1) / 2 = h := by omega
  -- the three partial sums
  set A : ℤ := ∑ i ∈ range h, ∑ j ∈ range h, K ((i + 1 : ℕ) : ZMod p) ((j + 1 : ℕ) : ZMod p) with hA
  set Zs : ℤ := ∑ j ∈ range h, K (0 : ZMod p) ((j + 1 : ℕ) : ZMod p) with hZs
  set Es : ℤ := ∑ i ∈ range h, K ((i + 1 : ℕ) : ZMod p) ((i + 1 : ℕ) : ZMod p) with hEs
  have k00 := K_zero_zero (p := p)
  -- the full count
  have hT : (∑ x : ZMod p, ∑ y : ZMod p, K x y) = 4 * A + 4 * Zs := by
    have inner : ∀ x : ZMod p, (∑ y : ZMod p, K x y)
        = K x 0 + 2 * ∑ j ∈ range h, K x ((j + 1 : ℕ) : ZMod p) :=
      fun x => fold h hph (K x) (K_neg_right x)
    simp only [inner]
    rw [fold h hph (fun x => K x 0 + 2 * ∑ j ∈ range h, K x ((j + 1 : ℕ) : ZMod p))
      (fun x => by simp only [K_neg_left])]
    have e1 : ∑ k ∈ range h, (K ((k + 1 : ℕ) : ZMod p) 0
        + 2 * ∑ j ∈ range h, K ((k + 1 : ℕ) : ZMod p) ((j + 1 : ℕ) : ZMod p)) = Zs + 2 * A := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hZs, hA]
      congr 1
      exact Finset.sum_congr rfl fun k _ => K_comm _ _
    rw [e1, k00, ← hZs]
    ring
  have hZ : 2 * Zs = quadraticChar (ZMod p) (-1) + 1 := by
    have h1 := fold h hph (K 0) (K_neg_right 0)
    rw [k00, ← hZs] at h1
    have h2 : (∑ y : ZMod p, K 0 y) = quadraticChar (ZMod p) (-1) + 1 := by
      rw [← sqcount hp2]
      refine Finset.sum_congr rfl fun y _ => ?_
      unfold K
      simp
    linarith
  have hE : 2 * Es = quadraticChar (ZMod p) (-2) + 1 := by
    have h1 := fold h hph (fun x => K x x) (fun x => by rw [K_neg_left, K_neg_right])
    simp only [k00] at h1
    rw [← hEs] at h1
    have h2 : (∑ x : ZMod p, K x x) = quadraticChar (ZMod p) (-2) + 1 := by
      rw [← sqcount hp2 (-2),
        ← Equiv.sum_comp (Equiv.mulLeft₀ (2 : ZMod p) (two_ne hp2))
          (fun z : ZMod p => if z ^ 2 = -2 then (1 : ℤ) else 0)]
      refine Finset.sum_congr rfl fun x _ => ?_
      unfold K
      have h2 := two_ne (p := p) hp2
      have : (x ^ 2 + x ^ 2 = -1) ↔ ((2 * x) ^ 2 = -2) := by
        constructor
        · intro h
          linear_combination 2 * h
        · intro h
          apply mul_left_cancel₀ h2
          linear_combination h
      show (if x ^ 2 + x ^ 2 = -1 then (1 : ℤ) else 0) = if (2 * x) ^ 2 = -2 then 1 else 0
      by_cases hc : x ^ 2 + x ^ 2 = -1
      · rw [if_pos hc, if_pos (this.mp hc)]
      · rw [if_neg hc, if_neg (fun h => hc (this.mpr h))]
    linarith
  -- the count of the statement
  have hc : (cnt p : ℤ) = ∑ a ∈ range (h + 1), ∑ b ∈ range (h + 1),
      (if a ≤ b then K (a : ZMod p) (b : ZMod p) else 0) := by
    unfold cnt
    rw [hh, Finset.card_filter, Nat.cast_sum, Finset.sum_product]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    have hd : (p ∣ a ^ 2 + b ^ 2 + 1) ↔ ((a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = -1) := by
      rw [← ZMod.natCast_eq_zero_iff]
      push_cast
      constructor <;> intro h <;> linear_combination h
    unfold K
    by_cases hab : a ≤ b <;> by_cases hk : (a : ZMod p) ^ 2 + (b : ZMod p) ^ 2 = -1 <;>
      simp [hab, hk, hd]
  have hsym : (∑ a ∈ range (h + 1), ∑ b ∈ range (h + 1),
      (if a ≤ b then K (a : ZMod p) (b : ZMod p) else 0))
      = ∑ a ∈ range (h + 1), ∑ b ∈ range (h + 1),
        (if b ≤ a then K (a : ZMod p) (b : ZMod p) else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [K_comm]
  have h2c : 2 * (cnt p : ℤ) = (∑ a ∈ range (h + 1), ∑ b ∈ range (h + 1),
      K (a : ZMod p) (b : ZMod p)) + ∑ a ∈ range (h + 1), K (a : ZMod p) (a : ZMod p) := by
    have e : 2 * (cnt p : ℤ) = (cnt p : ℤ) + (cnt p : ℤ) := by ring
    rw [e]
    nth_rewrite 2 [hc]
    rw [hsym, hc, ← Finset.sum_add_distrib]
    have e2 : ∀ a ∈ range (h + 1), K (a : ZMod p) (a : ZMod p)
        = ∑ b ∈ range (h + 1), (if a = b then K (a : ZMod p) (b : ZMod p) else 0) := by
      intro a ha
      rw [Finset.sum_ite_eq, if_pos ha]
    rw [Finset.sum_congr rfl e2, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rcases lt_trichotomy a b with hlt | heq | hgt
    · rw [if_pos hlt.le, if_neg (by omega), if_neg (by omega)]
    · subst heq
      simp
    · rw [if_neg (by omega), if_pos hgt.le, if_neg (by omega)]
      ring
  have hS : (∑ a ∈ range (h + 1), ∑ b ∈ range (h + 1), K (a : ZMod p) (b : ZMod p))
      = A + 2 * Zs := by
    rw [Finset.sum_range_succ']
    have e1 : ∀ a : ℕ, (∑ b ∈ range (h + 1), K (a : ZMod p) (b : ZMod p))
        = (∑ j ∈ range h, K (a : ZMod p) ((j + 1 : ℕ) : ZMod p)) + K (a : ZMod p) 0 := by
      intro a
      rw [Finset.sum_range_succ']
      simp
    simp only [e1]
    rw [Finset.sum_add_distrib]
    have e2 : ∑ i ∈ range h, K ((i + 1 : ℕ) : ZMod p) 0 = Zs := by
      rw [hZs]
      exact Finset.sum_congr rfl fun k _ => K_comm _ _
    rw [e2, ← hA]
    simp only [Nat.cast_zero]
    rw [k00, ← hZs]
    ring
  have hD : (∑ a ∈ range (h + 1), K (a : ZMod p) (a : ZMod p)) = Es := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero]
    rw [k00, ← hEs, add_zero]
  have hTc := Tcount (p := p) hp2
  rw [hS, hD] at h2c
  linarith

lemma cnt_eq (hp2 : p ≠ 2) : cnt p = (p + 7) / 8 := by
  have h := eight_cnt (p := p) hp2
  have hodd : p % 2 = 1 := by
    rcases hp.out.eq_two_or_odd with h2 | ho
    · exact absurd h2 hp2
    · exact ho
  have e4 : ZMod.χ₄ (p : ZMod 4) = if p % 4 = 1 then 1 else -1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four, if_neg (by omega : ¬ p % 2 = 0)]
  have e8 : ZMod.χ₈' (p : ZMod 8) = if p % 8 = 1 ∨ p % 8 = 3 then 1 else -1 := by
    rw [ZMod.χ₈'_nat_eq_if_mod_eight, if_neg (by omega : ¬ p % 2 = 0)]
  rw [quadraticChar_neg_one (ringChar_ne hp2), quadraticChar_neg_two (ringChar_ne hp2), ZMod.card,
    e4, e8] at h
  have h8 : p % 8 = 1 ∨ p % 8 = 3 ∨ p % 8 = 5 ∨ p % 8 = 7 := by omega
  rcases h8 with h8 | h8 | h8 | h8
  · rw [if_pos (by omega : p % 4 = 1), if_pos (by omega : p % 8 = 1 ∨ p % 8 = 3)] at h
    omega
  · rw [if_neg (by omega : ¬ p % 4 = 1), if_pos (by omega : p % 8 = 1 ∨ p % 8 = 3)] at h
    omega
  · rw [if_pos (by omega : p % 4 = 1), if_neg (by omega : ¬ (p % 8 = 1 ∨ p % 8 = 3))] at h
    omega
  · rw [if_neg (by omega : ¬ p % 4 = 1), if_neg (by omega : ¬ (p % 8 = 1 ∨ p % 8 = 3))] at h
    omega

end

lemma cnt_two : cnt 2 = 0 := by decide

theorem result (n : ℕ) (hn : 1 ≤ n) : a n ≤ a (n + 1) := by
  unfold a
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have hlt : Nat.nth Nat.Prime (n - 1) < Nat.nth Nat.Prime (n + 1 - 1) :=
    Nat.nth_strictMono hinf (by omega)
  have hp := Nat.prime_nth_prime (n - 1)
  have hq := Nat.prime_nth_prime (n + 1 - 1)
  generalize Nat.nth Nat.Prime (n - 1) = p at *
  generalize Nat.nth Nat.Prime (n + 1 - 1) = q at *
  have hq2 : q ≠ 2 := by
    have := hp.two_le
    omega
  have hFq : Fact q.Prime := ⟨hq⟩
  rw [cnt_eq (p := q) hq2]
  by_cases hp2 : p = 2
  · rw [hp2, cnt_two]
    exact Nat.zero_le _
  · have hFp : Fact p.Prime := ⟨hp⟩
    rw [cnt_eq (p := p) hp2]
    omega

end OMA.A242736

theorem OMA.solution : type_of% @OMA.S_oeis_a242736.main :=
  fun n hn => OMA.A242736.result n hn
