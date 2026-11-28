import OMAStatements.S_oeis_a273147
import Mathlib
/-!
Proof of the conjectures of the statement oeis-a273147 (OEIS A273147), Rule 597.

Method: stage t of the automaton is described exactly by a set of cells depending only on
d = |x| + |y| (a condition on d ≤ t and on d mod 4); one step of the rule maps the description at
t to the one at t + 1 (a case split on the five cells of the neighbourhood, closed by omega).
The square is then summed ring by ring (the ring d = k has 4k cells), which gives a quadratic
count on each residue class of t mod 4; every conjecture then reduces to polynomial identities
on the four residue classes.
-/

namespace OMA.CA_a273147

open OMA.S_oeis_a273147 PowerSeries
def nxt (code : ℕ) (g : ℤ → ℤ → Bool) : ℤ → ℤ → Bool := fun i j =>
  code.testBit ((g i j).toNat + 2 * ((g (i + 1) j).toNat + (g (i - 1) j).toNat +
    (g i (j + 1)).toNat + (g i (j - 1)).toNat))

theorem cell_succ (code t : ℕ) : cell code (t + 1) = nxt code (cell code t) := by
  funext i j
  rfl

/-- A sum over the rows `i < 2t+1` of a function of `|i - t|`. -/
theorem symsum (t : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.range (2 * t + 1), f ((t - i) + (i - t)) =
      f 0 + 2 * ∑ k ∈ Finset.range t, f (k + 1) := by
  rw [show 2 * t + 1 = (t + 1) + t by ring, Finset.sum_range_add, Finset.sum_range_succ]
  have h1 : ∑ x ∈ Finset.range t, f ((t - x) + (x - t)) = ∑ k ∈ Finset.range t, f (k + 1) := by
    rw [← Finset.sum_range_reflect (fun k => f (k + 1)) t]
    refine Finset.sum_congr rfl (fun x hx => ?_)
    have := Finset.mem_range.mp hx
    congr 1
    omega
  have h2 : ∑ x ∈ Finset.range t, f ((t - (t + 1 + x)) + (t + 1 + x - t)) =
      ∑ k ∈ Finset.range t, f (k + 1) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    congr 1
    omega
  rw [h1, h2, show (t - t) + (t - t) = 0 by omega]
  ring

theorem dbl' (h : ℕ → ℕ) (n : ℕ) :
    ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range (n - 1 - a), h (a + b + 2) =
      ∑ k ∈ Finset.range n, k * h (k + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, show n + 1 - 1 - n = 0 by omega,
      Finset.sum_range_zero, add_zero]
    have e : ∀ a ∈ Finset.range n, ∑ b ∈ Finset.range (n + 1 - 1 - a), h (a + b + 2) =
        ∑ b ∈ Finset.range (n - 1 - a), h (a + b + 2) + h (n + 1) := by
      intro a ha
      have := Finset.mem_range.mp ha
      rw [show n + 1 - 1 - a = (n - 1 - a) + 1 by omega, Finset.sum_range_succ,
        show a + (n - 1 - a) + 2 = n + 1 by omega]
    rw [Finset.sum_congr rfl e, Finset.sum_add_distrib, ih, Finset.sum_const, Finset.card_range,
      smul_eq_mul]

theorem dbl (g : ℕ → ℕ) (n : ℕ) (hg : ∀ k, n < k → g k = 0) :
    ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, g (a + 1 + (b + 1)) =
      ∑ k ∈ Finset.range n, k * g (k + 1) := by
  rw [← dbl' g n]
  refine Finset.sum_congr rfl (fun a ha => ?_)
  have := Finset.mem_range.mp ha
  rw [show n = (n - 1 - a) + (a + 1) by omega, Finset.sum_range_add]
  rw [show n - 1 - a + (a + 1) - 1 - a = n - 1 - a by omega]
  have hz : ∑ x ∈ Finset.range (a + 1), g (a + 1 + (n - 1 - a + x + 1)) = 0 :=
    Finset.sum_eq_zero (fun x _ => hg _ (by omega))
  rw [hz, add_zero]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  congr 1
  omega

/-- Sum over the square `[-t, t]²` (index coordinates) of a weight depending on `|x| + |y|`
that vanishes outside the diamond `|x| + |y| ≤ t`. -/
theorem ringsum0 (t : ℕ) (g : ℕ → ℕ) (hg : ∀ k, t < k → g k = 0) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      g (((t - i) + (i - t)) + ((t - j) + (j - t))) =
      g 0 + ∑ k ∈ Finset.range t, 4 * (k + 1) * g (k + 1) := by
  have hin : ∀ a : ℕ, ∑ j ∈ Finset.range (2 * t + 1), g (a + ((t - j) + (j - t))) =
      g a + 2 * ∑ b ∈ Finset.range t, g (a + (b + 1)) := fun a => symsum t (fun e => g (a + e))
  rw [Finset.sum_congr rfl (fun i _ => hin ((t - i) + (i - t)))]
  rw [symsum t (fun a => g a + 2 * ∑ b ∈ Finset.range t, g (a + (b + 1)))]
  simp only [zero_add, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [dbl g t hg]
  have e : ∑ k ∈ Finset.range t, 4 * (k + 1) * g (k + 1) =
      4 * ∑ k ∈ Finset.range t, g (k + 1) + 4 * ∑ k ∈ Finset.range t, k * g (k + 1) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  rw [e]
  ring

theorem sum4 (t : ℕ) : ∑ k ∈ Finset.range t, 4 * (k + 1) = 2 * t ^ 2 + 2 * t := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- The same for a weight that is the constant `c` outside the diamond. -/
theorem ringsum (t : ℕ) (w : ℕ → ℕ) (c : ℕ) (hw : ∀ k, t < k → w k = c) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      w (((t - i) + (i - t)) + ((t - j) + (j - t))) =
      w 0 + ∑ k ∈ Finset.range t, 4 * (k + 1) * w (k + 1) + c * (2 * t ^ 2 + 2 * t) := by
  have split : ∀ k, w k = (if k ≤ t then w k else 0) + c * (if k ≤ t then 0 else 1) := by
    intro k
    by_cases hk : k ≤ t
    · simp [hk]
    · simp [hk, hw k (by omega)]
  have h1 := ringsum0 t (fun k => if k ≤ t then w k else 0) (fun k hk => by simp; omega)
  have h2 := ringsum0 t (fun k => if k ≤ t then 1 else 0) (fun k hk => by simp; omega)
  have hall : ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      ((if ((t - i) + (i - t)) + ((t - j) + (j - t)) ≤ t then 1 else 0) +
       (if ((t - i) + (i - t)) + ((t - j) + (j - t)) ≤ t then 0 else 1)) = (2 * t + 1) ^ 2 := by
    have : ∀ k : ℕ, ((if k ≤ t then 1 else 0) + (if k ≤ t then 0 else 1) : ℕ) = 1 := by
      intro k; split_ifs <;> rfl
    simp only [this, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    ring
  simp only [Finset.sum_add_distrib] at hall
  rw [h2] at hall
  have hs : ∑ k ∈ Finset.range t, 4 * (k + 1) * (if k + 1 ≤ t then 1 else 0) =
      ∑ k ∈ Finset.range t, 4 * (k + 1) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have := Finset.mem_range.mp hk
    simp [show k + 1 ≤ t by omega]
  have hg := sum4 t
  simp only [hs, hg, show (0 : ℕ) ≤ t from Nat.zero_le t, if_true] at hall
  have h3 : ∑ k ∈ Finset.range t, 4 * (k + 1) * (if k + 1 ≤ t then w (k + 1) else 0) =
      ∑ k ∈ Finset.range t, 4 * (k + 1) * w (k + 1) := by
    refine Finset.sum_congr rfl (fun k hk => ?_)
    have := Finset.mem_range.mp hk
    simp [show k + 1 ≤ t by omega]
  simp only [h3, Nat.zero_le, if_true] at h1
  conv_lhs => enter [2, i, 2, j]; rw [split]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1]
  have hout : ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if ((t - i) + (i - t)) + ((t - j) + (j - t)) ≤ t then 0 else 1) = 2 * t ^ 2 + 2 * t := by
    have : (2 * t + 1) ^ 2 = (2 * t ^ 2 + 2 * t + 1) + (2 * t ^ 2 + 2 * t) := by ring
    omega
  rw [hout]

/-- Turning a cell sum into a sum of a weight of `|x| + |y|`. -/
theorem to_ring (t : ℕ) (G : ℤ → ℤ → Bool) (w : ℕ → ℕ)
    (hG : ∀ x y : ℤ, (if G x y = true then 1 else 0) = w (x.natAbs + y.natAbs)) :
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      (if G ((i : ℤ) - t) ((j : ℤ) - t) = true then 1 else 0) =
    ∑ i ∈ Finset.range (2 * t + 1), ∑ j ∈ Finset.range (2 * t + 1),
      w (((t - i) + (i - t)) + ((t - j) + (j - t))) := by
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  rw [hG]
  congr 1
  omega

theorem uper (u : ℕ → ℕ) (hu : ∀ k, u (k + 4) = u k) (q s : ℕ) : u (4 * q + s) = u s := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 4 * (q + 1) + s = (4 * q + s) + 4 by ring, hu, ih]

theorem persum (u : ℕ → ℕ) (hu : ∀ k, u (k + 4) = u k) (q : ℕ) :
    ∑ k ∈ Finset.range (4 * q), ((4 * (k + 1) * u (k + 1) : ℕ) : ℚ) =
      4 * ((u 1 : ℚ) * (2 * (q : ℚ) ^ 2 - q) + (u 2 : ℚ) * (2 * (q : ℚ) ^ 2) +
        (u 3 : ℚ) * (2 * (q : ℚ) ^ 2 + q) + (u 4 : ℚ) * (2 * (q : ℚ) ^ 2 + 2 * q)) := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 4 * (q + 1) = 4 * q + 1 + 1 + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp only [add_assoc, Nat.reduceAdd]
    rw [uper u hu q 1, uper u hu q 2, uper u hu q 3, uper u hu q 4]
    push_cast
    ring

theorem persum1 (u : ℕ → ℕ) (hu : ∀ k, u (k + 4) = u k) (q : ℕ) :
    ∑ k ∈ Finset.range (4 * q + 1), ((4 * (k + 1) * u (k + 1) : ℕ) : ℚ) =
      4 * ((u 1 : ℚ) * (2 * (q : ℚ) ^ 2 - q) + (u 2 : ℚ) * (2 * (q : ℚ) ^ 2) +
        (u 3 : ℚ) * (2 * (q : ℚ) ^ 2 + q) + (u 4 : ℚ) * (2 * (q : ℚ) ^ 2 + 2 * q)) +
      4 * (4 * (q : ℚ) + 1) * (u 1 : ℚ) := by
  rw [Finset.sum_range_succ, persum u hu q, uper u hu q 1]
  push_cast
  ring

theorem persum2 (u : ℕ → ℕ) (hu : ∀ k, u (k + 4) = u k) (q : ℕ) :
    ∑ k ∈ Finset.range (4 * q + 2), ((4 * (k + 1) * u (k + 1) : ℕ) : ℚ) =
      4 * ((u 1 : ℚ) * (2 * (q : ℚ) ^ 2 - q) + (u 2 : ℚ) * (2 * (q : ℚ) ^ 2) +
        (u 3 : ℚ) * (2 * (q : ℚ) ^ 2 + q) + (u 4 : ℚ) * (2 * (q : ℚ) ^ 2 + 2 * q)) +
      4 * (4 * (q : ℚ) + 1) * (u 1 : ℚ) + 4 * (4 * (q : ℚ) + 2) * (u 2 : ℚ) := by
  rw [Finset.sum_range_succ, persum1 u hu q, show 4 * q + 1 + 1 = 4 * q + 2 by ring, uper u hu q 2]
  push_cast
  ring

theorem persum3 (u : ℕ → ℕ) (hu : ∀ k, u (k + 4) = u k) (q : ℕ) :
    ∑ k ∈ Finset.range (4 * q + 3), ((4 * (k + 1) * u (k + 1) : ℕ) : ℚ) =
      4 * ((u 1 : ℚ) * (2 * (q : ℚ) ^ 2 - q) + (u 2 : ℚ) * (2 * (q : ℚ) ^ 2) +
        (u 3 : ℚ) * (2 * (q : ℚ) ^ 2 + q) + (u 4 : ℚ) * (2 * (q : ℚ) ^ 2 + 2 * q)) +
      4 * (4 * (q : ℚ) + 1) * (u 1 : ℚ) + 4 * (4 * (q : ℚ) + 2) * (u 2 : ℚ) +
      4 * (4 * (q : ℚ) + 3) * (u 3 : ℚ) := by
  rw [Finset.sum_range_succ, persum2 u hu q, show 4 * q + 2 + 1 = 4 * q + 3 by ring, uper u hu q 3]
  push_cast
  ring

/-- Stage `t ≥ 1` of Rule 597: the complement of stage `t - 1` of Rule 342 (cells with
`d = |x| + |y| ≤ t - 1` such that `d ≡ t - 1 (mod 4)` when `t - 1` is even, and `d ≢ t (mod 4)` when
`t - 1` is odd). -/
abbrev P (t d : ℕ) : Prop := (t = 0 ∧ d = 0) ∨ (1 ≤ t ∧ ¬(d ≤ t - 1 ∧ (((t - 1) % 2 = 0 ∧ d % 4 = (t - 1) % 4) ∨ ((t - 1) % 2 = 1 ∧ d % 4 ≠ t % 4))))

def F (t : ℕ) (x y : ℤ) : Bool := decide (P t (x.natAbs + y.natAbs))


theorem stA (t d : ℕ) (hd : 1 ≤ d) (n : ℕ) (hn : n = 2 * (decide (P t (d + 1))).toNat + 2 * (decide (P t (d - 1))).toNat) :
    Nat.testBit 597 ((decide (P t d)).toNat + 2 * n) = decide (P (t + 1) d) := by
  subst hn
  cases h0 : decide (P t d) <;> cases h1 : decide (P t (d + 1)) <;> cases h2 : decide (P t (d - 1)) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
      Nat.testBit_eq_decide_div_mod_eq] at h0 h1 h2 ⊢ <;>
    norm_num <;> (try unfold P at *) <;> omega

theorem stB (t d : ℕ) (hd : 1 ≤ d) (n : ℕ) (hn : n = 3 * (decide (P t (d + 1))).toNat + (decide (P t (d - 1))).toNat) :
    Nat.testBit 597 ((decide (P t d)).toNat + 2 * n) = decide (P (t + 1) d) := by
  subst hn
  cases h0 : decide (P t d) <;> cases h1 : decide (P t (d + 1)) <;> cases h2 : decide (P t (d - 1)) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
      Nat.testBit_eq_decide_div_mod_eq] at h0 h1 h2 ⊢ <;>
    norm_num <;> (try unfold P at *) <;> omega

theorem stC (t d : ℕ) (hd : d = 0) (n : ℕ) (hn : n = 4 * (decide (P t (d + 1))).toNat) :
    Nat.testBit 597 ((decide (P t d)).toNat + 2 * n) = decide (P (t + 1) d) := by
  subst hn
  cases h0 : decide (P t d) <;> cases h1 : decide (P t (d + 1)) <;> 
    simp only [decide_eq_true_eq, decide_eq_false_iff_not, Bool.toNat_true, Bool.toNat_false,
      Nat.testBit_eq_decide_div_mod_eq] at h0 h1 ⊢ <;>
    norm_num <;> (try unfold P at *) <;> omega

theorem stepF (t : ℕ) (x y : ℤ) : nxt 597 (F t) x y = F (t + 1) x y := by
  simp only [nxt, F]
  rcases lt_trichotomy x 0 with hx | hx | hx <;> rcases lt_trichotomy y 0 with hy | hy | hy
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega]
    exact stA t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega]
    exact stB t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega]
    exact stA t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega]
    exact stB t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega]
    exact stC t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega]
    exact stB t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs - 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega]
    exact stA t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs + 1 by omega]
    exact stB t _ (by omega) _ (by omega)
  · rw [show (x + 1).natAbs + y.natAbs = x.natAbs + y.natAbs + 1 by omega, show (x - 1).natAbs + y.natAbs = x.natAbs + y.natAbs - 1 by omega, show x.natAbs + (y + 1).natAbs = x.natAbs + y.natAbs + 1 by omega, show x.natAbs + (y - 1).natAbs = x.natAbs + y.natAbs - 1 by omega]
    exact stA t _ (by omega) _ (by omega)

theorem cellF (t : ℕ) : cell 597 t = F t := by
  induction t with
  | zero =>
    funext x y
    show decide (x = 0 ∧ y = 0) = F 0 x y
    unfold F
    congr 1
    apply propext
    unfold P
    constructor
    · rintro ⟨rfl, rfl⟩
      decide
    · intro h
      omega
  | succ t ih =>
    rw [cell_succ, ih]
    funext x y
    exact stepF t x y

def wt (t k : ℕ) : ℕ := if P t k then 1 else 0

def U0 (k : ℕ) : ℕ := if k % 4 = 0 then 1 else 0

theorem U0per (k : ℕ) : U0 (k + 4) = U0 k := by
  simp only [U0]
  split_ifs <;> omega

theorem cR0 (q : ℕ) (hq : 1 ≤ q) : (onCount 597 (4 * q) : ℚ) = (1 : ℚ) * (q : ℚ) ^ 0 + (16 : ℚ) * (q : ℚ) ^ 1 + (40 : ℚ) * (q : ℚ) ^ 2 := by
  have h1 : onCount 597 (4 * q) = ∑ i ∈ Finset.range (2 * (4 * q) + 1),
      ∑ j ∈ Finset.range (2 * (4 * q) + 1),
      wt (4 * q) ((((4 * q) - i) + (i - (4 * q))) + (((4 * q) - j) + (j - (4 * q)))) := by
    simp only [onCount, cellF]
    exact to_ring _ _ _ (fun x y => by simp only [F, wt, decide_eq_true_eq])
  rw [ringsum (4 * q) (wt (4 * q)) 1 (fun k hk => by unfold wt; split_ifs <;> (try unfold P at *) <;> omega)] at h1
  have h2 : ∀ k ∈ Finset.range (4 * q), 4 * (k + 1) * wt (4 * q) (k + 1) = 4 * (k + 1) * U0 (k + 1) := by
    intro k hk
    have := Finset.mem_range.mp hk
    unfold wt U0
    split_ifs <;> (try unfold P at *) <;> omega
  rw [Finset.sum_congr rfl h2] at h1
  have h0 : wt (4 * q) 0 = 1 := by
    unfold wt
    split_ifs <;> (try unfold P at *) <;> omega
  rw [h0] at h1
  rw [h1, Nat.cast_add, Nat.cast_add, Nat.cast_sum, persum U0 U0per q]
  push_cast
  simp only [U0]
  norm_num
  try ring

def U1 (k : ℕ) : ℕ := if k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 then 1 else 0

theorem U1per (k : ℕ) : U1 (k + 4) = U1 k := by
  simp only [U1]
  split_ifs <;> omega

theorem cR1 (q : ℕ) : (onCount 597 (4 * q + 1) : ℚ) = (8 : ℚ) * (q : ℚ) ^ 0 + (40 : ℚ) * (q : ℚ) ^ 1 + (56 : ℚ) * (q : ℚ) ^ 2 := by
  have h1 : onCount 597 (4 * q + 1) = ∑ i ∈ Finset.range (2 * (4 * q + 1) + 1),
      ∑ j ∈ Finset.range (2 * (4 * q + 1) + 1),
      wt (4 * q + 1) ((((4 * q + 1) - i) + (i - (4 * q + 1))) + (((4 * q + 1) - j) + (j - (4 * q + 1)))) := by
    simp only [onCount, cellF]
    exact to_ring _ _ _ (fun x y => by simp only [F, wt, decide_eq_true_eq])
  rw [ringsum (4 * q + 1) (wt (4 * q + 1)) 1 (fun k hk => by unfold wt; split_ifs <;> (try unfold P at *) <;> omega)] at h1
  have h2 : ∀ k ∈ Finset.range (4 * q + 1), 4 * (k + 1) * wt (4 * q + 1) (k + 1) = 4 * (k + 1) * U1 (k + 1) := by
    intro k hk
    have := Finset.mem_range.mp hk
    unfold wt U1
    split_ifs <;> (try unfold P at *) <;> omega
  rw [Finset.sum_congr rfl h2] at h1
  have h0 : wt (4 * q + 1) 0 = 0 := by
    unfold wt
    split_ifs <;> (try unfold P at *) <;> omega
  rw [h0] at h1
  rw [h1, Nat.cast_add, Nat.cast_add, Nat.cast_sum, persum1 U1 U1per q]
  push_cast
  simp only [U1]
  norm_num
  try ring

def U2 (k : ℕ) : ℕ := if k % 4 = 2 then 1 else 0

theorem U2per (k : ℕ) : U2 (k + 4) = U2 k := by
  simp only [U2]
  split_ifs <;> omega

theorem cR2 (q : ℕ) : (onCount 597 (4 * q + 2) : ℚ) = (20 : ℚ) * (q : ℚ) ^ 0 + (56 : ℚ) * (q : ℚ) ^ 1 + (40 : ℚ) * (q : ℚ) ^ 2 := by
  have h1 : onCount 597 (4 * q + 2) = ∑ i ∈ Finset.range (2 * (4 * q + 2) + 1),
      ∑ j ∈ Finset.range (2 * (4 * q + 2) + 1),
      wt (4 * q + 2) ((((4 * q + 2) - i) + (i - (4 * q + 2))) + (((4 * q + 2) - j) + (j - (4 * q + 2)))) := by
    simp only [onCount, cellF]
    exact to_ring _ _ _ (fun x y => by simp only [F, wt, decide_eq_true_eq])
  rw [ringsum (4 * q + 2) (wt (4 * q + 2)) 1 (fun k hk => by unfold wt; split_ifs <;> (try unfold P at *) <;> omega)] at h1
  have h2 : ∀ k ∈ Finset.range (4 * q + 2), 4 * (k + 1) * wt (4 * q + 2) (k + 1) = 4 * (k + 1) * U2 (k + 1) := by
    intro k hk
    have := Finset.mem_range.mp hk
    unfold wt U2
    split_ifs <;> (try unfold P at *) <;> omega
  rw [Finset.sum_congr rfl h2] at h1
  have h0 : wt (4 * q + 2) 0 = 0 := by
    unfold wt
    split_ifs <;> (try unfold P at *) <;> omega
  rw [h0] at h1
  rw [h1, Nat.cast_add, Nat.cast_add, Nat.cast_sum, persum2 U2 U2per q]
  push_cast
  simp only [U2]
  norm_num
  try ring

def U3 (k : ℕ) : ℕ := if k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 3 then 1 else 0

theorem U3per (k : ℕ) : U3 (k + 4) = U3 k := by
  simp only [U3]
  split_ifs <;> omega

theorem cR3 (q : ℕ) : (onCount 597 (4 * q + 3) : ℚ) = (41 : ℚ) * (q : ℚ) ^ 0 + (96 : ℚ) * (q : ℚ) ^ 1 + (56 : ℚ) * (q : ℚ) ^ 2 := by
  have h1 : onCount 597 (4 * q + 3) = ∑ i ∈ Finset.range (2 * (4 * q + 3) + 1),
      ∑ j ∈ Finset.range (2 * (4 * q + 3) + 1),
      wt (4 * q + 3) ((((4 * q + 3) - i) + (i - (4 * q + 3))) + (((4 * q + 3) - j) + (j - (4 * q + 3)))) := by
    simp only [onCount, cellF]
    exact to_ring _ _ _ (fun x y => by simp only [F, wt, decide_eq_true_eq])
  rw [ringsum (4 * q + 3) (wt (4 * q + 3)) 1 (fun k hk => by unfold wt; split_ifs <;> (try unfold P at *) <;> omega)] at h1
  have h2 : ∀ k ∈ Finset.range (4 * q + 3), 4 * (k + 1) * wt (4 * q + 3) (k + 1) = 4 * (k + 1) * U3 (k + 1) := by
    intro k hk
    have := Finset.mem_range.mp hk
    unfold wt U3
    split_ifs <;> (try unfold P at *) <;> omega
  rw [Finset.sum_congr rfl h2] at h1
  have h0 : wt (4 * q + 3) 0 = 1 := by
    unfold wt
    split_ifs <;> (try unfold P at *) <;> omega
  rw [h0] at h1
  rw [h1, Nat.cast_add, Nat.cast_add, Nat.cast_sum, persum3 U3 U3per q]
  push_cast
  simp only [U3]
  norm_num
  try ring

theorem cV0 : (onCount 597 0 : ℚ) = 1 := by
  have h : onCount 597 0 = ∑ i ∈ Finset.range (2 * 0 + 1), ∑ j ∈ Finset.range (2 * 0 + 1),
      wt 0 (((0 - i) + (i - 0)) + ((0 - j) + (j - 0))) := by
    simp only [onCount, cellF]
    exact to_ring _ _ _ (fun x y => by simp only [F, wt, decide_eq_true_eq])
  rw [ringsum 0 (wt 0) 0 (fun k hk => by unfold wt; split_ifs <;> (try unfold P at *) <;> omega)] at h
  have h0 : wt 0 0 = 1 := by simp [wt, P]
  rw [h0, Finset.sum_range_zero, zero_mul, add_zero, add_zero] at h
  rw [h]
  norm_num

theorem cV1 : (onCount 597 1 : ℚ) = 8 := by
  have h := cR1 0
  rw [show (4 * 0 + 1 : ℕ) = 1 by norm_num] at h
  rw [h]
  norm_num

theorem cV2 : (onCount 597 2 : ℚ) = 20 := by
  have h := cR2 0
  rw [show (4 * 0 + 2 : ℕ) = 2 by norm_num] at h
  rw [h]
  norm_num

theorem cV3 : (onCount 597 3 : ℚ) = 41 := by
  have h := cR3 0
  rw [show (4 * 0 + 3 : ℕ) = 3 by norm_num] at h
  rw [h]
  norm_num

theorem cV4 : (onCount 597 4 : ℚ) = 57 := by
  have h := cR0 1 (by norm_num)
  rw [show (4 * 1 : ℕ) = 4 by norm_num] at h
  rw [h]
  norm_num

theorem cV5 : (onCount 597 5 : ℚ) = 104 := by
  have h := cR1 1
  rw [show (4 * 1 + 1 : ℕ) = 5 by norm_num] at h
  rw [h]
  norm_num

theorem cV6 : (onCount 597 6 : ℚ) = 116 := by
  have h := cR2 1
  rw [show (4 * 1 + 2 : ℕ) = 6 by norm_num] at h
  rw [h]
  norm_num

theorem cV7 : (onCount 597 7 : ℚ) = 193 := by
  have h := cR3 1
  rw [show (4 * 1 + 3 : ℕ) = 7 by norm_num] at h
  rw [h]
  norm_num

theorem cV8 : (onCount 597 8 : ℚ) = 193 := by
  have h := cR0 2 (by norm_num)
  rw [show (4 * 2 : ℕ) = 8 by norm_num] at h
  rw [h]
  norm_num

theorem cV9 : (onCount 597 9 : ℚ) = 312 := by
  have h := cR1 2
  rw [show (4 * 2 + 1 : ℕ) = 9 by norm_num] at h
  rw [h]
  norm_num

theorem cV10 : (onCount 597 10 : ℚ) = 292 := by
  have h := cR2 2
  rw [show (4 * 2 + 2 : ℕ) = 10 by norm_num] at h
  rw [h]
  norm_num

theorem cV11 : (onCount 597 11 : ℚ) = 457 := by
  have h := cR3 2
  rw [show (4 * 2 + 3 : ℕ) = 11 by norm_num] at h
  rw [h]
  norm_num

theorem cV12 : (onCount 597 12 : ℚ) = 409 := by
  have h := cR0 3 (by norm_num)
  rw [show (4 * 3 : ℕ) = 12 by norm_num] at h
  rw [h]
  norm_num

theorem cV13 : (onCount 597 13 : ℚ) = 632 := by
  have h := cR1 3
  rw [show (4 * 3 + 1 : ℕ) = 13 by norm_num] at h
  rw [h]
  norm_num

theorem cV14 : (onCount 597 14 : ℚ) = 548 := by
  have h := cR2 3
  rw [show (4 * 3 + 2 : ℕ) = 14 by norm_num] at h
  rw [h]
  norm_num

theorem cV15 : (onCount 597 15 : ℚ) = 833 := by
  have h := cR3 3
  rw [show (4 * 3 + 3 : ℕ) = 15 by norm_num] at h
  rw [h]
  norm_num

theorem cV16 : (onCount 597 16 : ℚ) = 705 := by
  have h := cR0 4 (by norm_num)
  rw [show (4 * 4 : ℕ) = 16 by norm_num] at h
  rw [h]
  norm_num

theorem cV17 : (onCount 597 17 : ℚ) = 1064 := by
  have h := cR1 4
  rw [show (4 * 4 + 1 : ℕ) = 17 by norm_num] at h
  rw [h]
  norm_num

theorem cV18 : (onCount 597 18 : ℚ) = 884 := by
  have h := cR2 4
  rw [show (4 * 4 + 2 : ℕ) = 18 by norm_num] at h
  rw [h]
  norm_num

theorem cV19 : (onCount 597 19 : ℚ) = 1321 := by
  have h := cR3 4
  rw [show (4 * 4 + 3 : ℕ) = 19 by norm_num] at h
  rw [h]
  norm_num

theorem cV20 : (onCount 597 20 : ℚ) = 1081 := by
  have h := cR0 5 (by norm_num)
  rw [show (4 * 5 : ℕ) = 20 by norm_num] at h
  rw [h]
  norm_num

theorem cV21 : (onCount 597 21 : ℚ) = 1608 := by
  have h := cR1 5
  rw [show (4 * 5 + 1 : ℕ) = 21 by norm_num] at h
  rw [h]
  norm_num

theorem cV22 : (onCount 597 22 : ℚ) = 1300 := by
  have h := cR2 5
  rw [show (4 * 5 + 2 : ℕ) = 22 by norm_num] at h
  rw [h]
  norm_num

theorem cV23 : (onCount 597 23 : ℚ) = 1921 := by
  have h := cR3 5
  rw [show (4 * 5 + 3 : ℕ) = 23 by norm_num] at h
  rw [h]
  norm_num

theorem cV24 : (onCount 597 24 : ℚ) = 1537 := by
  have h := cR0 6 (by norm_num)
  rw [show (4 * 6 : ℕ) = 24 by norm_num] at h
  rw [h]
  norm_num

theorem cV25 : (onCount 597 25 : ℚ) = 2264 := by
  have h := cR1 6
  rw [show (4 * 6 + 1 : ℕ) = 25 by norm_num] at h
  rw [h]
  norm_num

theorem cV26 : (onCount 597 26 : ℚ) = 1796 := by
  have h := cR2 6
  rw [show (4 * 6 + 2 : ℕ) = 26 by norm_num] at h
  rw [h]
  norm_num

theorem cV27 : (onCount 597 27 : ℚ) = 2633 := by
  have h := cR3 6
  rw [show (4 * 6 + 3 : ℕ) = 27 by norm_num] at h
  rw [h]
  norm_num

theorem cV28 : (onCount 597 28 : ℚ) = 2073 := by
  have h := cR0 7 (by norm_num)
  rw [show (4 * 7 : ℕ) = 28 by norm_num] at h
  rw [h]
  norm_num

theorem cV29 : (onCount 597 29 : ℚ) = 3032 := by
  have h := cR1 7
  rw [show (4 * 7 + 1 : ℕ) = 29 by norm_num] at h
  rw [h]
  norm_num

theorem cV30 : (onCount 597 30 : ℚ) = 2372 := by
  have h := cR2 7
  rw [show (4 * 7 + 2 : ℕ) = 30 by norm_num] at h
  rw [h]
  norm_num

theorem cV31 : (onCount 597 31 : ℚ) = 3457 := by
  have h := cR3 7
  rw [show (4 * 7 + 3 : ℕ) = 31 by norm_num] at h
  rw [h]
  norm_num

theorem cV32 : (onCount 597 32 : ℚ) = 2689 := by
  have h := cR0 8 (by norm_num)
  rw [show (4 * 8 : ℕ) = 32 by norm_num] at h
  rw [h]
  norm_num

theorem cV33 : (onCount 597 33 : ℚ) = 3912 := by
  have h := cR1 8
  rw [show (4 * 8 + 1 : ℕ) = 33 by norm_num] at h
  rw [h]
  norm_num

theorem cV34 : (onCount 597 34 : ℚ) = 3028 := by
  have h := cR2 8
  rw [show (4 * 8 + 2 : ℕ) = 34 by norm_num] at h
  rw [h]
  norm_num

theorem cV35 : (onCount 597 35 : ℚ) = 4393 := by
  have h := cR3 8
  rw [show (4 * 8 + 3 : ℕ) = 35 by norm_num] at h
  rw [h]
  norm_num

theorem cV36 : (onCount 597 36 : ℚ) = 3385 := by
  have h := cR0 9 (by norm_num)
  rw [show (4 * 9 : ℕ) = 36 by norm_num] at h
  rw [h]
  norm_num

theorem cV37 : (onCount 597 37 : ℚ) = 4904 := by
  have h := cR1 9
  rw [show (4 * 9 + 1 : ℕ) = 37 by norm_num] at h
  rw [h]
  norm_num

theorem cV38 : (onCount 597 38 : ℚ) = 3764 := by
  have h := cR2 9
  rw [show (4 * 9 + 2 : ℕ) = 38 by norm_num] at h
  rw [h]
  norm_num

theorem cV39 : (onCount 597 39 : ℚ) = 5441 := by
  have h := cR3 9
  rw [show (4 * 9 + 3 : ℕ) = 39 by norm_num] at h
  rw [h]
  norm_num

theorem cV40 : (onCount 597 40 : ℚ) = 4161 := by
  have h := cR0 10 (by norm_num)
  rw [show (4 * 10 : ℕ) = 40 by norm_num] at h
  rw [h]
  norm_num

theorem cV41 : (onCount 597 41 : ℚ) = 6008 := by
  have h := cR1 10
  rw [show (4 * 10 + 1 : ℕ) = 41 by norm_num] at h
  rw [h]
  norm_num

theorem aV0 : (a 0 : ℚ) = 7 := by
  simp only [a]
  push_cast
  rw [cV1, cV0]
  norm_num

theorem aV1 : (a 1 : ℚ) = 12 := by
  simp only [a]
  push_cast
  rw [cV2, cV1]
  norm_num

theorem aV2 : (a 2 : ℚ) = 21 := by
  simp only [a]
  push_cast
  rw [cV3, cV2]
  norm_num

theorem aV3 : (a 3 : ℚ) = 16 := by
  simp only [a]
  push_cast
  rw [cV4, cV3]
  norm_num

theorem aV4 : (a 4 : ℚ) = 47 := by
  simp only [a]
  push_cast
  rw [cV5, cV4]
  norm_num

theorem aV5 : (a 5 : ℚ) = 12 := by
  simp only [a]
  push_cast
  rw [cV6, cV5]
  norm_num

theorem aV6 : (a 6 : ℚ) = 77 := by
  simp only [a]
  push_cast
  rw [cV7, cV6]
  norm_num

theorem aV7 : (a 7 : ℚ) = 0 := by
  simp only [a]
  push_cast
  rw [cV8, cV7]
  norm_num

theorem aV8 : (a 8 : ℚ) = 119 := by
  simp only [a]
  push_cast
  rw [cV9, cV8]
  norm_num

theorem aV9 : (a 9 : ℚ) = -20 := by
  simp only [a]
  push_cast
  rw [cV10, cV9]
  norm_num

theorem aV10 : (a 10 : ℚ) = 165 := by
  simp only [a]
  push_cast
  rw [cV11, cV10]
  norm_num

theorem aV11 : (a 11 : ℚ) = -48 := by
  simp only [a]
  push_cast
  rw [cV12, cV11]
  norm_num

theorem aV12 : (a 12 : ℚ) = 223 := by
  simp only [a]
  push_cast
  rw [cV13, cV12]
  norm_num

theorem aV13 : (a 13 : ℚ) = -84 := by
  simp only [a]
  push_cast
  rw [cV14, cV13]
  norm_num

theorem aV14 : (a 14 : ℚ) = 285 := by
  simp only [a]
  push_cast
  rw [cV15, cV14]
  norm_num

theorem aV15 : (a 15 : ℚ) = -128 := by
  simp only [a]
  push_cast
  rw [cV16, cV15]
  norm_num

theorem aV16 : (a 16 : ℚ) = 359 := by
  simp only [a]
  push_cast
  rw [cV17, cV16]
  norm_num

theorem aV17 : (a 17 : ℚ) = -180 := by
  simp only [a]
  push_cast
  rw [cV18, cV17]
  norm_num

theorem aV18 : (a 18 : ℚ) = 437 := by
  simp only [a]
  push_cast
  rw [cV19, cV18]
  norm_num

theorem aV19 : (a 19 : ℚ) = -240 := by
  simp only [a]
  push_cast
  rw [cV20, cV19]
  norm_num

theorem aV20 : (a 20 : ℚ) = 527 := by
  simp only [a]
  push_cast
  rw [cV21, cV20]
  norm_num

theorem aV21 : (a 21 : ℚ) = -308 := by
  simp only [a]
  push_cast
  rw [cV22, cV21]
  norm_num

theorem aV22 : (a 22 : ℚ) = 621 := by
  simp only [a]
  push_cast
  rw [cV23, cV22]
  norm_num

theorem aV23 : (a 23 : ℚ) = -384 := by
  simp only [a]
  push_cast
  rw [cV24, cV23]
  norm_num

theorem aV24 : (a 24 : ℚ) = 727 := by
  simp only [a]
  push_cast
  rw [cV25, cV24]
  norm_num

theorem aV25 : (a 25 : ℚ) = -468 := by
  simp only [a]
  push_cast
  rw [cV26, cV25]
  norm_num

theorem aV26 : (a 26 : ℚ) = 837 := by
  simp only [a]
  push_cast
  rw [cV27, cV26]
  norm_num

theorem aV27 : (a 27 : ℚ) = -560 := by
  simp only [a]
  push_cast
  rw [cV28, cV27]
  norm_num

theorem aV28 : (a 28 : ℚ) = 959 := by
  simp only [a]
  push_cast
  rw [cV29, cV28]
  norm_num

theorem aV29 : (a 29 : ℚ) = -660 := by
  simp only [a]
  push_cast
  rw [cV30, cV29]
  norm_num

theorem aV30 : (a 30 : ℚ) = 1085 := by
  simp only [a]
  push_cast
  rw [cV31, cV30]
  norm_num

theorem aV31 : (a 31 : ℚ) = -768 := by
  simp only [a]
  push_cast
  rw [cV32, cV31]
  norm_num

theorem aV32 : (a 32 : ℚ) = 1223 := by
  simp only [a]
  push_cast
  rw [cV33, cV32]
  norm_num

theorem aV33 : (a 33 : ℚ) = -884 := by
  simp only [a]
  push_cast
  rw [cV34, cV33]
  norm_num

theorem aV34 : (a 34 : ℚ) = 1365 := by
  simp only [a]
  push_cast
  rw [cV35, cV34]
  norm_num

theorem aV35 : (a 35 : ℚ) = -1008 := by
  simp only [a]
  push_cast
  rw [cV36, cV35]
  norm_num

theorem aV36 : (a 36 : ℚ) = 1519 := by
  simp only [a]
  push_cast
  rw [cV37, cV36]
  norm_num

theorem aV37 : (a 37 : ℚ) = -1140 := by
  simp only [a]
  push_cast
  rw [cV38, cV37]
  norm_num

theorem aV38 : (a 38 : ℚ) = 1677 := by
  simp only [a]
  push_cast
  rw [cV39, cV38]
  norm_num

theorem aV39 : (a 39 : ℚ) = -1280 := by
  simp only [a]
  push_cast
  rw [cV40, cV39]
  norm_num

theorem aV40 : (a 40 : ℚ) = 1847 := by
  simp only [a]
  push_cast
  rw [cV41, cV40]
  norm_num

theorem aR0 (q : ℕ) (hq : 1 ≤ q) : (a (4 * q) : ℚ) = (7 : ℚ) * (q : ℚ) ^ 0 + (24 : ℚ) * (q : ℚ) ^ 1 + (16 : ℚ) * (q : ℚ) ^ 2 := by
  simp only [a]
  
  push_cast
  rw [cR1 q, cR0 q (by omega)]
  push_cast
  ring

theorem aR1 (q : ℕ) (hq : 1 ≤ q) : (a (4 * q + 1) : ℚ) = (12 : ℚ) * (q : ℚ) ^ 0 + (16 : ℚ) * (q : ℚ) ^ 1 + (-16 : ℚ) * (q : ℚ) ^ 2 := by
  simp only [a]
  rw [show 4 * q + 1 + 1 = 4 * q + 2 by ring]
  push_cast
  rw [cR2 q, cR1 q]
  push_cast
  ring

theorem aR2 (q : ℕ) (hq : 1 ≤ q) : (a (4 * q + 2) : ℚ) = (21 : ℚ) * (q : ℚ) ^ 0 + (40 : ℚ) * (q : ℚ) ^ 1 + (16 : ℚ) * (q : ℚ) ^ 2 := by
  simp only [a]
  rw [show 4 * q + 2 + 1 = 4 * q + 3 by ring]
  push_cast
  rw [cR3 q, cR2 q]
  push_cast
  ring

theorem aR3 (q : ℕ) (hq : 1 ≤ q) : (a (4 * q + 3) : ℚ) = (16 : ℚ) * (q : ℚ) ^ 0 + (-16 : ℚ) * (q : ℚ) ^ 2 := by
  simp only [a]
  rw [show 4 * q + 3 + 1 = 4 * (q + 1) by ring]
  push_cast
  rw [cR0 (q + 1) (by omega), cR3 q]
  push_cast
  ring

theorem recD (n : ℕ) (hn : 12 ≤ n) : ((1 : ℚ)) * (a n : ℚ) + ((1 : ℚ)) * (a (n - 1) : ℚ) + ((-1 : ℚ)) * (a (n - 2) : ℚ) + ((-1 : ℚ)) * (a (n - 3) : ℚ) + ((-1 : ℚ)) * (a (n - 4) : ℚ) + ((-1 : ℚ)) * (a (n - 5) : ℚ) + ((1 : ℚ)) * (a (n - 6) : ℚ) + ((1 : ℚ)) * (a (n - 7) : ℚ) = 0 := by
  have hs : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  rcases hs with hs | hs | hs | hs
  · obtain ⟨q, rfl⟩ : ∃ q, n = 4 * q + 12 := ⟨(n - 12) / 4, by omega⟩
    rw [show 4 * q + 12 - 1 = 4 * (q + 2) + 3 by omega]
    rw [show 4 * q + 12 - 2 = 4 * (q + 2) + 2 by omega]
    rw [show 4 * q + 12 - 3 = 4 * (q + 2) + 1 by omega]
    rw [show 4 * q + 12 - 4 = 4 * (q + 2) by omega]
    rw [show 4 * q + 12 - 5 = 4 * (q + 1) + 3 by omega]
    rw [show 4 * q + 12 - 6 = 4 * (q + 1) + 2 by omega]
    rw [show 4 * q + 12 - 7 = 4 * (q + 1) + 1 by omega]
    rw [show 4 * q + 12 = 4 * (q + 3) by omega]
    rw [aR1 (q + 1) (by omega), aR2 (q + 1) (by omega), aR3 (q + 1) (by omega), aR0 (q + 2) (by omega), aR1 (q + 2) (by omega), aR2 (q + 2) (by omega), aR3 (q + 2) (by omega), aR0 (q + 3) (by omega)]
    push_cast
    ring
  · obtain ⟨q, rfl⟩ : ∃ q, n = 4 * q + 13 := ⟨(n - 13) / 4, by omega⟩
    rw [show 4 * q + 13 - 1 = 4 * (q + 3) by omega]
    rw [show 4 * q + 13 - 2 = 4 * (q + 2) + 3 by omega]
    rw [show 4 * q + 13 - 3 = 4 * (q + 2) + 2 by omega]
    rw [show 4 * q + 13 - 4 = 4 * (q + 2) + 1 by omega]
    rw [show 4 * q + 13 - 5 = 4 * (q + 2) by omega]
    rw [show 4 * q + 13 - 6 = 4 * (q + 1) + 3 by omega]
    rw [show 4 * q + 13 - 7 = 4 * (q + 1) + 2 by omega]
    rw [show 4 * q + 13 = 4 * (q + 3) + 1 by omega]
    rw [aR2 (q + 1) (by omega), aR3 (q + 1) (by omega), aR0 (q + 2) (by omega), aR1 (q + 2) (by omega), aR2 (q + 2) (by omega), aR3 (q + 2) (by omega), aR0 (q + 3) (by omega), aR1 (q + 3) (by omega)]
    push_cast
    ring
  · obtain ⟨q, rfl⟩ : ∃ q, n = 4 * q + 14 := ⟨(n - 14) / 4, by omega⟩
    rw [show 4 * q + 14 - 1 = 4 * (q + 3) + 1 by omega]
    rw [show 4 * q + 14 - 2 = 4 * (q + 3) by omega]
    rw [show 4 * q + 14 - 3 = 4 * (q + 2) + 3 by omega]
    rw [show 4 * q + 14 - 4 = 4 * (q + 2) + 2 by omega]
    rw [show 4 * q + 14 - 5 = 4 * (q + 2) + 1 by omega]
    rw [show 4 * q + 14 - 6 = 4 * (q + 2) by omega]
    rw [show 4 * q + 14 - 7 = 4 * (q + 1) + 3 by omega]
    rw [show 4 * q + 14 = 4 * (q + 3) + 2 by omega]
    rw [aR3 (q + 1) (by omega), aR0 (q + 2) (by omega), aR1 (q + 2) (by omega), aR2 (q + 2) (by omega), aR3 (q + 2) (by omega), aR0 (q + 3) (by omega), aR1 (q + 3) (by omega), aR2 (q + 3) (by omega)]
    push_cast
    ring
  · obtain ⟨q, rfl⟩ : ∃ q, n = 4 * q + 15 := ⟨(n - 15) / 4, by omega⟩
    rw [show 4 * q + 15 - 1 = 4 * (q + 3) + 2 by omega]
    rw [show 4 * q + 15 - 2 = 4 * (q + 3) + 1 by omega]
    rw [show 4 * q + 15 - 3 = 4 * (q + 3) by omega]
    rw [show 4 * q + 15 - 4 = 4 * (q + 2) + 3 by omega]
    rw [show 4 * q + 15 - 5 = 4 * (q + 2) + 2 by omega]
    rw [show 4 * q + 15 - 6 = 4 * (q + 2) + 1 by omega]
    rw [show 4 * q + 15 - 7 = 4 * (q + 2) by omega]
    rw [show 4 * q + 15 = 4 * (q + 3) + 3 by omega]
    rw [aR0 (q + 2) (by omega), aR1 (q + 2) (by omega), aR2 (q + 2) (by omega), aR3 (q + 2) (by omega), aR0 (q + 3) (by omega), aR1 (q + 3) (by omega), aR2 (q + 3) (by omega), aR3 (q + 3) (by omega)]
    push_cast
    ring

end OMA.CA_a273147

open OMA.CA_a273147 OMA.S_oeis_a273147 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a273147.main := by
  refine ⟨?_, ?_⟩
  · intro n hn0
    rcases Nat.lt_or_ge n 12 with h | h
    · interval_cases n <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18, aV19, aV20, aV21, aV22, aV23, aV24, aV25, aV26, aV27, aV28, aV29, aV30, aV31, aV32, aV33, aV34, aV35, aV36, aV37, aV38, aV39, aV40]
    · have := recD n h
      linarith
  · have hL : mk (fun n => (a n : ℚ)) * ((1 - X) ^ 2 * (1 + X) ^ 3 * (1 + X ^ 2) : PowerSeries ℚ) = mk (fun n => (a n : ℚ)) + X ^ 1 * mk (fun n => (a n : ℚ)) - X ^ 2 * mk (fun n => (a n : ℚ)) - X ^ 3 * mk (fun n => (a n : ℚ)) - X ^ 4 * mk (fun n => (a n : ℚ)) - X ^ 5 * mk (fun n => (a n : ℚ)) + X ^ 6 * mk (fun n => (a n : ℚ)) + X ^ 7 * mk (fun n => (a n : ℚ)) := by
      try simp only [map_ofNat]
      ring
    have hR : (7 + 19 * X + 26 * X ^ 2 + 18 * X ^ 3 + 23 * X ^ 4 + 3 * X ^ 5 : PowerSeries ℚ) = C 7 + C 19 * X ^ 1 + C 26 * X ^ 2 + C 18 * X ^ 3 + C 23 * X ^ 4 + C 3 * X ^ 5 := by
      try simp only [map_ofNat]
      ring
    rw [hL, hR]
    ext k
    simp only [map_add, map_sub, map_neg, coeff_C_mul, coeff_X_pow_mul', coeff_mk, coeff_X_pow, coeff_one, coeff_C]
    rcases Nat.lt_or_ge k 12 with h | h
    · interval_cases k <;> norm_num [aV0, aV1, aV2, aV3, aV4, aV5, aV6, aV7, aV8, aV9, aV10, aV11, aV12, aV13, aV14, aV15, aV16, aV17, aV18, aV19, aV20, aV21, aV22, aV23, aV24, aV25, aV26, aV27, aV28, aV29, aV30, aV31, aV32, aV33, aV34, aV35, aV36, aV37, aV38, aV39, aV40]
    · have := recD k (by omega)
      rw [if_pos (show 1 ≤ k by omega)]
      rw [if_pos (show 2 ≤ k by omega)]
      rw [if_pos (show 3 ≤ k by omega)]
      rw [if_pos (show 4 ≤ k by omega)]
      rw [if_pos (show 5 ≤ k by omega)]
      rw [if_pos (show 6 ≤ k by omega)]
      rw [if_pos (show 7 ≤ k by omega)]
      rw [if_neg (show k ≠ 0 by omega)]
      rw [if_neg (show k ≠ 1 by omega)]
      rw [if_neg (show k ≠ 2 by omega)]
      rw [if_neg (show k ≠ 3 by omega)]
      rw [if_neg (show k ≠ 4 by omega)]
      rw [if_neg (show k ≠ 5 by omega)]
      linarith
