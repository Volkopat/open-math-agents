import OMAStatements.S_oeis_a353138
import Mathlib

/-!
# A353138: the only fixed points of `term` are 1 and 4624

A fixed point `n` with `L` digits satisfies `10^(L-1) ≤ n ≤ L * L^9`, so `L ≤ 11`.
The value `term n = ∑_j c_j L^j` only depends on the digit counts `c_j`, so it suffices to check
every count vector `(c_0, …, c_9)` with `∑ c_j = L` for `L ≤ 11`, which the kernel does.
Large cases are split on the leading counts so that each kernel check stays small.
-/

namespace W2A353138

open OMA.S_oeis_a353138

/-- Decimal digits with fuel. -/
def dg : ℕ → ℕ → List ℕ
  | 0, _ => []
  | f + 1, n => if n = 0 then [] else n % 10 :: dg f (n / 10)

/-- `∑ L ^ d` over the last `f` decimal digits `d` of `n` (leading zeros included). -/
def ps (L : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | f + 1, n => Nat.add (Nat.pow L (n % 10)) (ps L f (n / 10))

/-- Leaf test: if `t` has `L` digits and is a fixed point, then it is 1 or 4624. -/
def Q (L t : ℕ) : Bool :=
  Nat.blt t (Nat.pow 10 (L - 1)) || Nat.ble (Nat.pow 10 L) t || !Nat.beq (ps L L t) t ||
    Nat.beq t 1 || Nat.beq t 4624

/-- `lp f n` holds iff `f c` holds for every `c ≤ n`. -/
def lp (f : ℕ → Bool) : ℕ → Bool
  | 0 => f 0
  | n + 1 => f (n + 1) && lp f n

theorem lp_iff (f : ℕ → Bool) : ∀ n, lp f n = true ↔ ∀ c, c ≤ n → f c = true
  | 0 => by simp [lp]
  | n + 1 => by
    rw [lp, Bool.and_eq_true, lp_iff f n]
    constructor
    · rintro ⟨h1, h2⟩ c hc
      rcases Nat.lt_or_ge c (n + 1) with h | h
      · exact h2 c (by omega)
      · rw [show c = n + 1 by omega]
        exact h1
    · intro h
      exact ⟨h _ le_rfl, fun c hc => h c (by omega)⟩

/-- Enumerate the counts `c_k, …, c_0` with sum `r`. A branch is skipped once every value
`S + ∑_{j ≤ k} c_j L^j ≤ S + r L^k` it can still reach lies outside `[10^(L-1), 10^L)`. -/
def go (L : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, r, S => Q L (S + r)
  | k + 1, r, S =>
    Nat.blt (Nat.add S (Nat.mul r (Nat.pow L (k + 1)))) (Nat.pow 10 (L - 1)) ||
      Nat.ble (Nat.pow 10 L) S ||
      lp (fun c => go L k (r - c) (Nat.add S (Nat.mul c (Nat.pow L (k + 1))))) r

theorem go_split (L k r S : ℕ)
    (h : ∀ c, c ≤ r → go L k (r - c) (S + c * L ^ (k + 1)) = true) : go L (k + 1) r S = true := by
  simp only [go, Bool.or_eq_true, lp_iff]
  exact Or.inr h

theorem chk1 : go 1 9 1 0 = true := by decide +kernel

theorem chk2 : go 2 9 2 0 = true := by decide +kernel

theorem chk3 : go 3 9 3 0 = true := by decide +kernel

theorem chk4 : go 4 9 4 0 = true := by decide +kernel

theorem chk5 : go 5 9 5 0 = true := by decide +kernel

theorem chk6 : go 6 9 6 0 = true := by decide +kernel

theorem chk7 : go 7 9 7 0 = true := by decide +kernel

theorem chk8 : go 8 9 8 0 = true := by decide +kernel

theorem chk9_0 : go 9 8 9 0 = true := by decide +kernel

theorem chk9_1 : go 9 8 8 387420489 = true := by decide +kernel

theorem chk9_2 : go 9 8 7 774840978 = true := by decide +kernel

theorem chk9_3 : go 9 8 6 1162261467 = true := by decide +kernel

theorem chk9_4 : go 9 8 5 1549681956 = true := by decide +kernel

theorem chk9_5 : go 9 8 4 1937102445 = true := by decide +kernel

theorem chk9_6 : go 9 8 3 2324522934 = true := by decide +kernel

theorem chk9_7 : go 9 8 2 2711943423 = true := by decide +kernel

theorem chk9_8 : go 9 8 1 3099363912 = true := by decide +kernel

theorem chk9_9 : go 9 8 0 3486784401 = true := by decide +kernel

theorem chk9 : go 9 9 9 0 = true := by
  refine go_split 9 8 9 0 fun c hc => ?_
  interval_cases c
  · exact chk9_0
  · exact chk9_1
  · exact chk9_2
  · exact chk9_3
  · exact chk9_4
  · exact chk9_5
  · exact chk9_6
  · exact chk9_7
  · exact chk9_8
  · exact chk9_9

theorem chk10_0 : go 10 8 10 0 = true := by decide +kernel

theorem chk10_1_0 : go 10 7 9 1000000000 = true := by decide +kernel

theorem chk10_1_1 : go 10 7 8 1100000000 = true := by decide +kernel

theorem chk10_1_2 : go 10 7 7 1200000000 = true := by decide +kernel

theorem chk10_1_3 : go 10 7 6 1300000000 = true := by decide +kernel

theorem chk10_1_4 : go 10 7 5 1400000000 = true := by decide +kernel

theorem chk10_1_5 : go 10 7 4 1500000000 = true := by decide +kernel

theorem chk10_1_6 : go 10 7 3 1600000000 = true := by decide +kernel

theorem chk10_1_7 : go 10 7 2 1700000000 = true := by decide +kernel

theorem chk10_1_8 : go 10 7 1 1800000000 = true := by decide +kernel

theorem chk10_1_9 : go 10 7 0 1900000000 = true := by decide +kernel

theorem chk10_1 : go 10 8 9 1000000000 = true := by
  refine go_split 10 7 9 1000000000 fun c hc => ?_
  interval_cases c
  · exact chk10_1_0
  · exact chk10_1_1
  · exact chk10_1_2
  · exact chk10_1_3
  · exact chk10_1_4
  · exact chk10_1_5
  · exact chk10_1_6
  · exact chk10_1_7
  · exact chk10_1_8
  · exact chk10_1_9

theorem chk10_2 : go 10 8 8 2000000000 = true := by decide +kernel

theorem chk10_3 : go 10 8 7 3000000000 = true := by decide +kernel

theorem chk10_4 : go 10 8 6 4000000000 = true := by decide +kernel

theorem chk10_5 : go 10 8 5 5000000000 = true := by decide +kernel

theorem chk10_6 : go 10 8 4 6000000000 = true := by decide +kernel

theorem chk10_7 : go 10 8 3 7000000000 = true := by decide +kernel

theorem chk10_8 : go 10 8 2 8000000000 = true := by decide +kernel

theorem chk10_9 : go 10 8 1 9000000000 = true := by decide +kernel

theorem chk10_10 : go 10 8 0 10000000000 = true := by decide +kernel

theorem chk10 : go 10 9 10 0 = true := by
  refine go_split 10 8 10 0 fun c hc => ?_
  interval_cases c
  · exact chk10_0
  · exact chk10_1
  · exact chk10_2
  · exact chk10_3
  · exact chk10_4
  · exact chk10_5
  · exact chk10_6
  · exact chk10_7
  · exact chk10_8
  · exact chk10_9
  · exact chk10_10

theorem chk11 : go 11 9 11 0 = true := by decide +kernel

theorem chk (L : ℕ) (h1 : 1 ≤ L) (h2 : L ≤ 11) : go L 9 L 0 = true := by
  interval_cases L
  · exact chk1
  · exact chk2
  · exact chk3
  · exact chk4
  · exact chk5
  · exact chk6
  · exact chk7
  · exact chk8
  · exact chk9
  · exact chk10
  · exact chk11

theorem Q_out (L t : ℕ) (h : t < 10 ^ (L - 1) ∨ 10 ^ L ≤ t) : Q L t = true := by
  unfold Q
  simp only [Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.pow_eq]
  rcases h with h | h
  · exact Or.inl (Or.inl (Or.inl (Or.inl h)))
  · exact Or.inl (Or.inl (Or.inl (Or.inr h)))

theorem ps_eq (L : ℕ) : ∀ f n, n < 10 ^ f →
    ps L f n = ((Nat.digits 10 n).map (L ^ ·)).sum + (f - (Nat.digits 10 n).length)
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this
    simp [ps]
  | f + 1, n, h => by
    have h' : n / 10 < 10 ^ f := Nat.div_lt_of_lt_mul (by rw [pow_succ'] at h; exact h)
    have hl : (Nat.digits 10 (n / 10)).length ≤ f := by
      exact (Nat.digits_length_le_iff (by norm_num) _).2 h'
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ps, ps_eq L f 0 (by positivity)]
      omega
    · rw [ps, ps_eq L f (n / 10) h', Nat.digits_def' (by norm_num) hn]
      simp only [Nat.add_eq, Nat.pow_eq, List.map_cons, List.sum_cons, List.length_cons]
      omega

theorem go_sound (L : ℕ) (hL : 1 ≤ L) : ∀ k r S, go L k r S = true → ∀ c : ℕ → ℕ,
    ∑ j ∈ Finset.range (k + 1), c j = r →
      Q L (S + ∑ j ∈ Finset.range (k + 1), c j * L ^ j) = true
  | 0, r, S, h, c, hc => by
    have e1 : ∑ j ∈ Finset.range (0 + 1), c j * L ^ j = c 0 := by simp
    have e2 : ∑ j ∈ Finset.range (0 + 1), c j = c 0 := by simp
    rw [e1]
    rw [e2] at hc
    rw [hc]
    simpa only [go] using h
  | k + 1, r, S, h, c, hc => by
    have hb : ∑ j ∈ Finset.range (k + 1 + 1), c j * L ^ j ≤ r * L ^ (k + 1) := by
      rw [← hc, Finset.sum_mul]
      apply Finset.sum_le_sum
      intro j hj
      rw [Finset.mem_range] at hj
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hL (by omega))
    simp only [go, Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.add_eq, Nat.mul_eq, Nat.pow_eq] at h
    rcases h with (h | h) | h
    · exact Q_out L _ (Or.inl (by omega))
    · exact Q_out L _ (Or.inr (by omega))
    rw [Finset.sum_range_succ] at hc ⊢
    rw [lp_iff] at h
    have h1 := h (c (k + 1)) (by omega)
    have h2 := go_sound L hL k (r - c (k + 1)) (S + c (k + 1) * L ^ (k + 1)) h1 c (by omega)
    rw [show S + (∑ j ∈ Finset.range (k + 1), c j * L ^ j + c (k + 1) * L ^ (k + 1)) =
      S + c (k + 1) * L ^ (k + 1) + ∑ j ∈ Finset.range (k + 1), c j * L ^ j by ring]
    exact h2

theorem dg_eq : ∀ f n, n < 10 ^ f → dg f n = Nat.digits 10 n
  | 0, n, h => by
    have : n = 0 := by simpa using h
    subst this
    simp [dg]
  | f + 1, n, h => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [dg]
    · rw [dg, if_neg hn.ne', Nat.digits_def' (by norm_num) hn,
        dg_eq f (n / 10) (Nat.div_lt_of_lt_mul (by rw [pow_succ'] at h; exact h))]

theorem bound (L : ℕ) (h : 12 ≤ L) : 10 * L ^ 10 < 10 ^ L := by
  induction L, h using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have h1 : (m + 1) ^ 10 * 12 ^ 10 ≤ 13 ^ 10 * m ^ 10 := by
      rw [← mul_pow, ← mul_pow]
      exact Nat.pow_le_pow_left (by omega) 10
    have h3 : (m + 1) ^ 10 ≤ 10 * m ^ 10 := by
      have h2 : (13 : ℕ) ^ 10 * m ^ 10 ≤ 10 * m ^ 10 * 12 ^ 10 := by
        have : (13 : ℕ) ^ 10 ≤ 10 * 12 ^ 10 := by norm_num
        nlinarith [Nat.zero_le (m ^ 10)]
      exact Nat.le_of_mul_le_mul_right (h1.trans h2) (by norm_num)
    have e : (10 : ℕ) ^ (m + 1) = 10 ^ m * 10 := pow_succ 10 m
    rw [e]
    linarith

theorem sum_count (D : List ℕ) (hD : ∀ d ∈ D, d < 10) (g : ℕ → ℕ) :
    (D.map g).sum = ∑ j ∈ Finset.range 10, D.count j * g j := by
  rw [Finset.sum_list_map_count]
  simp only [smul_eq_mul]
  apply Finset.sum_subset
  · intro x hx
    rw [List.mem_toFinset] at hx
    exact Finset.mem_range.2 (hD x hx)
  · intro x _ hx
    rw [List.mem_toFinset] at hx
    rw [List.count_eq_zero_of_not_mem hx, zero_mul]

theorem key (n : ℕ) (hn : 0 < n) (h : term n = n) : n = 1 ∨ n = 4624 := by
  set D := Nat.digits 10 n with hD
  set L := D.length with hLdef
  have hlt : ∀ d ∈ D, d < 10 := fun d hd => Nat.digits_lt_base (by norm_num) hd
  have hterm : term n = (D.map (L ^ ·)).sum := rfl
  have hn1 : n < 10 ^ L := Nat.lt_base_pow_length_digits (by norm_num)
  have hn2 : 10 ^ L ≤ 10 * n := Nat.base_pow_length_digits_le 10 n (by norm_num) hn.ne'
  have hL0 : 1 ≤ L := by
    by_contra hc
    have : L = 0 := by omega
    rw [this, pow_zero] at hn1
    omega
  have hup : (D.map (L ^ ·)).sum ≤ L * L ^ 9 := by
    have := List.sum_le_card_nsmul (D.map (L ^ ·)) (L ^ 9) (by
      intro x hx
      rw [List.mem_map] at hx
      obtain ⟨d, hd, rfl⟩ := hx
      exact Nat.pow_le_pow_right hL0 (by have := hlt d hd; omega))
    simpa using this
  have hL : L ≤ 11 := by
    by_contra hc
    have hb := bound L (by omega)
    have : L * L ^ 9 = L ^ 10 := by ring
    rw [hterm] at h
    linarith
  have hc : ∑ j ∈ Finset.range 10, D.count j = L := by
    have := sum_count D hlt (fun _ => 1)
    simpa using this.symm
  have hval : n = ∑ j ∈ Finset.range 10, D.count j * L ^ j := by
    rw [← sum_count D hlt, ← hterm, h]
  have hQ := go_sound L hL0 9 L 0 (chk L hL0 hL) (fun j => D.count j) hc
  rw [zero_add, ← hval] at hQ
  have hps : ps L L n = n := by
    rw [ps_eq L L n hn1, ← hD, ← hLdef, Nat.sub_self, add_zero, ← hterm, h]
  unfold Q at hQ
  rw [hps] at hQ
  simp only [Bool.or_eq_true, Nat.blt_eq, Nat.ble_eq, Nat.pow_eq, Nat.beq_refl, Bool.not_true,
    Bool.false_eq_true, or_false, Nat.beq_eq] at hQ
  have hlow : 10 ^ (L - 1) ≤ n := by
    have : 10 ^ L = 10 * 10 ^ (L - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    omega
  rcases hQ with ((h1 | h1) | h1) | h1
  · omega
  · omega
  · exact Or.inl h1
  · exact Or.inr h1

end W2A353138

theorem OMA.solution : type_of% @OMA.S_oeis_a353138.main := by
  intro n hn
  constructor
  · exact W2A353138.key n hn
  · rintro (rfl | rfl)
    · rw [OMA.S_oeis_a353138.term, ← W2A353138.dg_eq 1 1 (by norm_num)]
      rfl
    · rw [OMA.S_oeis_a353138.term, ← W2A353138.dg_eq 4 4624 (by norm_num)]
      rfl
