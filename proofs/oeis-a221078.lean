import OMAStatements.S_oeis_a221078

/-!
Proof sketch. Work in `ZMod p`. With `D n j = j! * S(n, j)`: `D n j = 0` for `j > n`,
`p ∣ D n j` for `j ≥ p`, and `D (n + t) j = D n j` mod `p` by Fermat when `n ≥ 1` and
`x ^ t = 1` for every nonzero `x`. Only `1 ≤ m ≤ p - 1` contributes to `a n` mod `p`, and the
inner sum of `tanPowCoeff m n` may be extended to `j ∈ [m, p - 1]`. Each extended term is
`t`-periodic, and the sign `(-1)^((n - m) / 2)` is unchanged when `4 ∣ t`.
Take `t = p - 1` if `p % 4 = 1`, and `t = 2 * (p - 1)` if `p % 4 = 3`.
-/

namespace R221078
open OMA.S_oeis_a221078 Finset

def S2 : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | _ + 1, 0 => 0
  | 0, _ + 1 => 0
  | n + 1, j + 1 => (j + 1) * S2 n (j + 1) + S2 n j

theorem s_zero : ∀ n j : ℕ, n < j → S2 n j = 0 := by
  intro n
  induction n with
  | zero =>
    intro j hj
    obtain ⟨j, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    simp [S2]
  | succ n ih =>
    intro j hj
    obtain ⟨j, rfl⟩ : ∃ m, j = m + 1 := ⟨j - 1, by omega⟩
    simp [S2, ih (j + 1) (by omega), ih j (by omega)]

def E (n j : ℕ) : ℤ := ∑ i ∈ range (j + 1), (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n

theorem E_succ (n j : ℕ) : E (n + 1) (j + 1) = ((j : ℤ) + 1) * (E n (j + 1) + E n j) := by
  have h2 : E n j = ∑ i ∈ range (j + 1 + 1),
      (-1 : ℤ) ^ (j + i) * (j.choose i : ℤ) * (i : ℤ) ^ n := by
    rw [E, sum_range_succ _ (j + 1)]
    simp
  rw [h2, E, E, ← sum_add_distrib, mul_sum]
  refine sum_congr rfl (fun i hi => ?_)
  have hi' : i ≤ j + 1 := by simp at hi; omega
  have h' : ((j.choose i * (j + 1) : ℕ) : ℤ) = (((j + 1).choose i * (j + 1 - i) : ℕ) : ℤ) := by
    rw [Nat.choose_mul_succ_eq]
  push_cast [Nat.cast_sub hi'] at h'
  have hs : (-1 : ℤ) ^ (j + 1 + i) = -(-1) ^ (j + i) := by
    rw [show j + 1 + i = (j + i) + 1 by omega, pow_succ]
    ring
  rw [hs]
  linear_combination (-((-1 : ℤ) ^ (j + i) * (i : ℤ) ^ n)) * h'

theorem formula : ∀ n j : ℕ, (j.factorial : ℤ) * (S2 n j : ℤ) = E n j := by
  intro n
  induction n with
  | zero =>
    intro j
    cases j with
    | zero => simp [E, S2]
    | succ j =>
      have h : E 0 (j + 1) = (-1) ^ (j + 1) *
          ∑ i ∈ range (j + 1 + 1), ((-1 : ℤ) ^ i * ((j + 1).choose i : ℤ)) := by
        rw [E, mul_sum]
        refine sum_congr rfl (fun i _ => ?_)
        rw [pow_add (-1 : ℤ) (j + 1) i]
        ring
      rw [h, Int.alternating_sum_range_choose_of_ne (by omega)]
      simp [S2]
  | succ n ih =>
    intro j
    cases j with
    | zero => simp [E, S2]
    | succ j =>
      rw [E_succ, ← ih (j + 1), ← ih j]
      simp only [S2, Nat.factorial_succ]
      push_cast
      ring

theorem D_eq (n j : ℕ) : stirling2Fact n j = E n j := by
  unfold stirling2Fact E
  refine sum_congr rfl (fun r hr => ?_)
  have hr' : r ≤ j := by simp only [mem_range] at hr; omega
  rw [show j + r = (j - r) + 2 * r by omega, pow_add, pow_mul, neg_one_sq, one_pow, mul_one]

theorem D_zero (n j : ℕ) (h : n < j) : stirling2Fact n j = 0 := by
  rw [D_eq, ← formula, s_zero n j h]
  simp

theorem D_dvd (p n j : ℕ) (hp : p.Prime) (h : p ≤ j) : (p : ℤ) ∣ stirling2Fact n j := by
  rw [D_eq, ← formula]
  exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 (Nat.dvd_factorial hp.pos h)) _

theorem fermatT {p : ℕ} (x : ZMod p) (n t : ℕ) (hn : 1 ≤ n)
    (hT : ∀ y : ZMod p, y ≠ 0 → y ^ t = 1) : x ^ (n + t) = x ^ n := by
  by_cases hx : x = 0
  · rw [hx, zero_pow (show n + t ≠ 0 by omega), zero_pow (show n ≠ 0 by omega)]
  · rw [pow_add, hT x hx, mul_one]

theorem Dc_zero {p : ℕ} (n j : ℕ) (h : n < j) : ((stirling2Fact n j : ℤ) : ZMod p) = 0 := by
  rw [D_zero n j h, Int.cast_zero]

theorem Dc_shift {p : ℕ} (n j t : ℕ) (hn : 1 ≤ n) (hT : ∀ y : ZMod p, y ≠ 0 → y ^ t = 1) :
    ((stirling2Fact (n + t) j : ℤ) : ZMod p) = ((stirling2Fact n j : ℤ) : ZMod p) := by
  unfold stirling2Fact
  push_cast
  refine sum_congr rfl (fun r _ => ?_)
  rw [fermatT _ n t hn hT]

def w (m n j : ℕ) : ℤ :=
  (-1 : ℤ) ^ (j - m) * (Nat.choose (j - 1) (m - 1) : ℤ) * 2 ^ (n - j) * stirling2Fact n j

def Ex (p m n : ℕ) : ZMod p := ∑ j ∈ Icc m (p - 1), ((w m n j : ℤ) : ZMod p)

theorem tan_eq (m n : ℕ) (hm : m ≠ 0) : tanPowCoeff m n =
    if n < m ∨ (n - m) % 2 ≠ 0 then 0
    else (-1 : ℤ) ^ ((n - m) / 2) * ∑ j ∈ Icc m n, w m n j := by
  unfold tanPowCoeff w
  rw [if_neg hm]

theorem ext_eq (p m n : ℕ) (hp : p.Prime) (hm : m < p) :
    ((∑ j ∈ Icc m n, w m n j : ℤ) : ZMod p) = Ex p m n := by
  rw [Int.cast_sum]
  have h1 : ∑ j ∈ Icc m n, ((w m n j : ℤ) : ZMod p) =
      ∑ j ∈ Icc m (n + p), ((w m n j : ℤ) : ZMod p) := by
    refine sum_subset (Icc_subset_Icc_right (show n ≤ n + p by omega)) (fun j hj hj' => ?_)
    simp only [mem_Icc] at hj
    have hnj : n < j := by
      by_contra hc
      exact hj' (mem_Icc.2 ⟨hj.1, by omega⟩)
    rw [w, D_zero n j hnj, mul_zero, Int.cast_zero]
  have h2 : ∑ j ∈ Icc m (p - 1), ((w m n j : ℤ) : ZMod p) =
      ∑ j ∈ Icc m (n + p), ((w m n j : ℤ) : ZMod p) := by
    refine sum_subset (Icc_subset_Icc_right (show p - 1 ≤ n + p by omega))
      (fun j hj hj' => ?_)
    simp only [mem_Icc] at hj
    have hpj : p ≤ j := by
      by_contra hc
      exact hj' (mem_Icc.2 ⟨hj.1, by omega⟩)
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, w]
    exact (D_dvd p n j hp hpj).mul_left _
  rw [h1, Ex, h2]

theorem Ex_zero (p m n : ℕ) (h : n < m) : Ex p m n = 0 := by
  unfold Ex
  refine sum_eq_zero (fun j hj => ?_)
  simp only [mem_Icc] at hj
  rw [w, D_zero n j (by omega), mul_zero, Int.cast_zero]

theorem Ex_shift (p m n t : ℕ) (hn : 1 ≤ n) (hT : ∀ y : ZMod p, y ≠ 0 → y ^ t = 1)
    (h2 : (2 : ZMod p) ≠ 0) : Ex p m (n + t) = Ex p m n := by
  unfold Ex
  refine sum_congr rfl (fun j _ => ?_)
  unfold w
  push_cast
  rw [Dc_shift n j t hn hT]
  by_cases hjn : j ≤ n
  · rw [show n + t - j = (n - j) + t by omega, pow_add, hT 2 h2, mul_one]
  · rw [Dc_zero n j (by omega)]
    simp only [mul_zero]

theorem tan_zero (p m n : ℕ) (hp : p.Prime) (hmp : p ≤ m) :
    ((tanPowCoeff m n : ℤ) : ZMod p) = 0 := by
  have hm0 : m ≠ 0 := by have := hp.two_le; omega
  rw [tan_eq m n hm0]
  split_ifs
  · exact Int.cast_zero
  · have hs : ∑ j ∈ Icc m n, ((w m n j : ℤ) : ZMod p) = 0 := by
      refine sum_eq_zero (fun j hj => ?_)
      simp only [mem_Icc] at hj
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd, w]
      exact (D_dvd p n j hp (by omega)).mul_left _
    rw [Int.cast_mul, Int.cast_sum, hs, mul_zero]

theorem tan_shift (p m n t : ℕ) (hp : p.Prime) (hm1 : 1 ≤ m) (hmp : m < p) (hn : 1 ≤ n)
    (ht4 : t % 4 = 0) (hT : ∀ y : ZMod p, y ≠ 0 → y ^ t = 1) (h2 : (2 : ZMod p) ≠ 0) :
    ((tanPowCoeff m (n + t) : ℤ) : ZMod p) = ((tanPowCoeff m n : ℤ) : ZMod p) := by
  have hm0 : m ≠ 0 := by omega
  rw [tan_eq m (n + t) hm0, tan_eq m n hm0]
  by_cases h1 : n < m ∨ (n - m) % 2 ≠ 0
  · rw [if_pos h1]
    by_cases h3 : n + t < m ∨ (n + t - m) % 2 ≠ 0
    · rw [if_pos h3]
    · have hnm : n < m := by omega
      rw [if_neg h3, Int.cast_mul, ext_eq p m (n + t) hp hmp, Ex_shift p m n t hn hT h2,
        Ex_zero p m n hnm, mul_zero, Int.cast_zero]
  · have h3 : ¬(n + t < m ∨ (n + t - m) % 2 ≠ 0) := by omega
    rw [if_neg h1, if_neg h3, Int.cast_mul, Int.cast_mul, ext_eq p m (n + t) hp hmp,
      ext_eq p m n hp hmp, Ex_shift p m n t hn hT h2,
      show (n + t - m) / 2 = (n - m) / 2 + 2 * (t / 4) by omega, pow_add, pow_mul, neg_one_sq,
      one_pow, mul_one]

theorem a_red (p n : ℕ) (hp : p.Prime) (hn : 1 ≤ n) :
    ((a n : ℤ) : ZMod p) =
      ∑ m ∈ Icc 1 (p - 1), (((m : ℤ) ^ n * tanPowCoeff m n : ℤ) : ZMod p) := by
  have hp2 := hp.two_le
  have h1 : ((a n : ℤ) : ZMod p) =
      ∑ m ∈ range (n + p), (((m : ℤ) ^ n * tanPowCoeff m n : ℤ) : ZMod p) := by
    unfold a
    rw [Int.cast_sum]
    refine sum_subset (range_subset_range.2 (show n + 1 ≤ n + p by omega))
      (fun m hm hm' => ?_)
    simp only [mem_range] at hm'
    have h0 : tanPowCoeff m n = 0 := by
      unfold tanPowCoeff
      rw [if_neg (show m ≠ 0 by omega), if_pos (Or.inl (show n < m by omega))]
    rw [h0, mul_zero, Int.cast_zero]
  have h2 : ∑ m ∈ Icc 1 (p - 1), (((m : ℤ) ^ n * tanPowCoeff m n : ℤ) : ZMod p) =
      ∑ m ∈ range (n + p), (((m : ℤ) ^ n * tanPowCoeff m n : ℤ) : ZMod p) := by
    refine sum_subset (fun m hm => ?_) (fun m hm hm' => ?_)
    · simp only [mem_Icc] at hm
      simp only [mem_range]
      omega
    · by_cases h0 : m = 0
      · subst h0
        rw [Nat.cast_zero, zero_pow (show n ≠ 0 by omega), zero_mul, Int.cast_zero]
      · have hmp : p ≤ m := by
          by_contra hc
          exact hm' (mem_Icc.2 ⟨by omega, by omega⟩)
        rw [Int.cast_mul, tan_zero p m n hp hmp, mul_zero]
  rw [h1, h2]

theorem main_gen (p n t : ℕ) (hp : p.Prime) (hn : 1 ≤ n) (ht4 : t % 4 = 0)
    (hT : ∀ y : ZMod p, y ≠ 0 → y ^ t = 1) (h2 : (2 : ZMod p) ≠ 0) :
    a (n + t) ≡ a n [ZMOD p] := by
  rw [← ZMod.intCast_eq_intCast_iff, a_red p (n + t) hp (by omega), a_red p n hp hn]
  refine sum_congr rfl (fun m hm => ?_)
  simp only [mem_Icc] at hm
  rw [Int.cast_mul, Int.cast_mul, tan_shift p m n t hp hm.1 (by omega) hn ht4 hT h2,
    Int.cast_pow, Int.cast_pow, fermatT _ n t hn hT]

theorem two_ne (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) : (2 : ZMod p) ≠ 0 := by
  intro h
  have h' : ((2 : ℤ) : ZMod p) = 0 := by exact_mod_cast h
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h'
  have h3 := Int.le_of_dvd (by norm_num) h'
  have h4 := hp.two_le
  omega

end R221078

theorem OMA.solution : type_of% @OMA.S_oeis_a221078.main := by
  constructor
  · intro p n hp hp4 hn
    have := Fact.mk hp
    exact R221078.main_gen p n (p - 1) hp hn (by omega)
      (fun y hy => ZMod.pow_card_sub_one_eq_one hy) (R221078.two_ne p hp (by omega))
  · intro p n hp hp4 hn
    have := Fact.mk hp
    refine R221078.main_gen p n (2 * (p - 1)) hp hn (by omega) (fun y hy => ?_)
      (R221078.two_ne p hp (by omega))
    rw [mul_comm, pow_mul, ZMod.pow_card_sub_one_eq_one hy, one_pow]
