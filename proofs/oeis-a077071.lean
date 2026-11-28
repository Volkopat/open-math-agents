import OMAStatements.S_oeis_a077071
import Mathlib

namespace OMA.A077071Proof

open OMA.S_oeis_a077071

/-! Part A: the Legendre side, `a m = m (m + 1) + 2 * Σ_{k ≤ m} v_2(k!)`. -/

/-- The `2`-adic valuation of `t!`. -/
def vf (t : ℕ) : ℕ := padicValNat 2 t.factorial

/-- `V n = Σ_{k < n} v_2(k!)`. -/
def V (n : ℕ) : ℕ := ∑ k ∈ Finset.range n, vf k

theorem vf_double (t : ℕ) : vf (2 * t) = vf t + t := by
  unfold vf
  exact padicValNat_factorial_mul (p := 2) t

theorem vf_double_add_one (t : ℕ) : vf (2 * t + 1) = vf (2 * t) := by
  unfold vf
  exact padicValNat_factorial_mul_add (p := 2) (n := 1) t (by norm_num)

theorem den_val (q : ℚ) (e : ℕ) (h : padicValRat 2 q = -(e : ℤ)) : padicValNat 2 q.den = e := by
  rw [padicValRat_def, padicValInt] at h
  by_cases hd : padicValNat 2 q.den = 0
  · rw [hd] at h ⊢
    omega
  · have h2d : 2 ∣ q.den := dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr hd)
    have h2n : ¬ 2 ∣ q.num.natAbs := by
      intro h2n
      have hg := Nat.dvd_gcd h2n h2d
      rw [q.reduced.gcd_eq_one] at hg
      omega
    rw [padicValNat.eq_zero_of_not_dvd h2n] at h
    omega

theorem coeff_val (m k : ℕ) :
    padicValRat 2 (legendreCoeff m k) = -((m + vf (m - k) + vf k : ℕ) : ℤ) := by
  have hN0 : (2 * m + 2 * k).factorial ≠ 0 := Nat.factorial_ne_zero _
  have hD0 : 2 ^ (2 * m) * (m - k).factorial * (m + k).factorial * (2 * k).factorial ≠ 0 := by
    positivity
  have e : legendreCoeff m k = (-1) ^ (m - k) * (((2 * m + 2 * k).factorial : ℕ) : ℚ) /
      (((2 ^ (2 * m) * (m - k).factorial * (m + k).factorial * (2 * k).factorial : ℕ)) : ℚ) := by
    rw [legendreCoeff]
    push_cast
    ring
  have hvN : padicValNat 2 (2 * m + 2 * k).factorial = vf (m + k) + (m + k) := by
    rw [show 2 * m + 2 * k = 2 * (m + k) by ring]
    exact vf_double (m + k)
  have hvD : padicValNat 2 (2 ^ (2 * m) * (m - k).factorial * (m + k).factorial * (2 * k).factorial)
      = 2 * m + vf (m - k) + vf (m + k) + (vf k + k) := by
    have h2k := vf_double k
    unfold vf at h2k ⊢
    rw [padicValNat.mul, padicValNat.mul, padicValNat.mul, padicValNat.prime_pow]
    · omega
    all_goals positivity
  have hq1 : ((-1 : ℚ) ^ (m - k)) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hq2 : (((2 * m + 2 * k).factorial : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hN0
  have hq3 : (((2 ^ (2 * m) * (m - k).factorial * (m + k).factorial * (2 * k).factorial : ℕ)) : ℚ)
      ≠ 0 := by exact_mod_cast hD0
  rw [e, padicValRat.div (mul_ne_zero hq1 hq2) hq3, padicValRat.mul hq1 hq2, padicValRat.pow,
    padicValRat.neg, padicValRat.one, padicValRat.of_nat, padicValRat.of_nat, hvN, hvD]
  push_cast
  ring

theorem T_eq (m k : ℕ) : T m k = m + vf (m - k) + vf k := by
  unfold T
  exact den_val _ _ (coeff_val m k)

theorem a_eq (m : ℕ) : a m = m * (m + 1) + 2 * V (m + 1) := by
  unfold a V
  simp only [T_eq]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul]
  have hr : ∑ k ∈ Finset.range (m + 1), vf (m - k) = ∑ k ∈ Finset.range (m + 1), vf k := by
    have := Finset.sum_range_reflect vf (m + 1)
    simpa using this
  rw [hr]
  ring

/-- `V (2g) + g = 2 V(g) + g^2` and `V (2g+1) = V g + V (g+1) + g^2`. -/
theorem V_par (g : ℕ) :
    V (2 * g) + g = V g + V g + g * g ∧ V (2 * g + 1) = V g + V (g + 1) + g * g := by
  induction g with
  | zero => simp [V]
  | succ g ih =>
    obtain ⟨h1, h2⟩ := ih
    have e1 : V (2 * (g + 1)) = V (2 * g + 1) + vf (2 * g + 1) := by
      rw [show 2 * (g + 1) = 2 * g + 1 + 1 by ring]
      exact Finset.sum_range_succ _ _
    have e2 : V (2 * (g + 1) + 1) = V (2 * (g + 1)) + vf (2 * (g + 1)) :=
      Finset.sum_range_succ _ _
    have e3 : V (g + 1) = V g + vf g := Finset.sum_range_succ _ _
    have e4 : V (g + 1 + 1) = V (g + 1) + vf (g + 1) := Finset.sum_range_succ _ _
    have f1 : vf (2 * g + 1) = vf g + g := by rw [vf_double_add_one, vf_double]
    have f2 : vf (2 * (g + 1)) = vf (g + 1) + (g + 1) := vf_double (g + 1)
    have i1 : V (2 * (g + 1)) + (g + 1) = V (g + 1) + V (g + 1) + (g + 1) * (g + 1) := by
      rw [e1, h2, f1, e3]
      ring
    refine ⟨i1, ?_⟩
    rw [e2, f2, e4]
    linarith

theorem V_rec (b h c : ℕ) (hh : h = (b + 2) / 2) (hc : c = b + 2 - h) :
    V (b + 2) + h = V h + V c + h * c := by
  rcases Nat.even_or_odd' (b + 2) with ⟨g, hg | hg⟩
  · have e1 : h = g := by omega
    have e2 : c = g := by omega
    rw [hg, e1, e2]
    exact (V_par g).1
  · have e1 : h = g := by omega
    have e2 : c = g + 1 := by omega
    rw [hg, e1, e2, (V_par g).2]
    ring

/-! Part B: the phase counts `C k b`. -/

/-- `C k b`: the number of steps that clear the boxes `0..k` when boxes `< k` are empty and box `k`
holds `b` balls (`L2` of the plan, `0`-indexed; box `0` is the wall). -/
def C : ℕ → ℕ → ℕ
  | _, 0 => 0
  | _, 1 => 1
  | 0, b + 2 => C 0 (b + 2 - (b + 2) / 2) + 1
  | k + 1, b + 2 => C (k + 1) (b + 2 - (b + 2) / 2) + C k ((b + 2) / 2) + 1
termination_by _ b => b

theorem C_zero (k : ℕ) : C k 0 = 0 := by
  simp only [C]

theorem C_one (k : ℕ) : C k 1 = 1 := by
  simp only [C]

theorem C_wall (b : ℕ) (hb : 2 ≤ b) : C 0 b = C 0 (b - b / 2) + 1 := by
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
  simp only [C]

theorem C_succ (k b : ℕ) (hb : 2 ≤ b) :
    C (k + 1) b = C (k + 1) (b - b / 2) + C k (b / 2) + 1 := by
  obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
  simp only [C]

/-- Far from the wall, `C k b = 2 b - 1`. -/
theorem C_small (b : ℕ) : ∀ k, 1 ≤ b → b ≤ k + 1 → C k b = 2 * b - 1 := by
  refine Nat.strong_induction_on b ?_
  intro b ih k hb1 hbk
  by_cases hb : b = 1
  · subst hb
    simp [C_one]
  · obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [C_succ k b (by omega), ih (b - b / 2) (by omega) (k + 1) (by omega) (by omega),
      ih (b / 2) (by omega) k (by omega) (by omega)]
    omega

/-- `Q b K = Σ_{k < K} C k b`. -/
def Q (b K : ℕ) : ℕ := ∑ k ∈ Finset.range K, C k b

theorem tail (b : ℕ) (hb : 1 ≤ b) (d : ℕ) :
    Q b (b - 1 + d) = Q b (b - 1) + d * (2 * b - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have e : Q b (b - 1 + (d + 1)) = Q b (b - 1 + d) + C (b - 1 + d) b := by
      rw [show b - 1 + (d + 1) = (b - 1 + d) + 1 by omega]
      exact Finset.sum_range_succ _ _
    rw [e, ih, C_small b (b - 1 + d) hb (by omega)]
    ring

theorem E_rec (b : ℕ) :
    Q (b + 2) (b + 1) = (b + 1) + Q ((b + 2) / 2) b + Q (b + 2 - (b + 2) / 2) (b + 1) := by
  unfold Q
  rw [Finset.sum_range_succ', Finset.sum_range_succ', C_wall (b + 2) (by omega)]
  have hs : ∀ k ∈ Finset.range b, C (k + 1) (b + 2) =
      C (k + 1) (b + 2 - (b + 2) / 2) + C k ((b + 2) / 2) + 1 :=
    fun k _ => C_succ k (b + 2) (by omega)
  rw [Finset.sum_congr rfl hs, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_range, smul_eq_mul, mul_one]
  omega

theorem E_rec' (b h c : ℕ) (hh : h = (b + 2) / 2) (hc : c = b + 2 - h) :
    Q (b + 2) (b + 1) = (b + 1) + Q h b + Q c (b + 1) := by
  subst hh
  subst hc
  exact E_rec b

/-- The total: `Σ_{k < b - 1} C k b = b (b - 1) + 2 V b`. -/
theorem E_closed (b : ℕ) : Q b (b - 1) = b * (b - 1) + 2 * V b := by
  refine Nat.strong_induction_on b ?_
  intro b ih
  rcases Nat.lt_or_ge b 2 with hb | hb
  · interval_cases b <;> simp [Q, V, vf]
  · obtain ⟨b, rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
    obtain ⟨h, hh⟩ : ∃ h, h = (b + 2) / 2 := ⟨_, rfl⟩
    obtain ⟨c, hc⟩ : ∃ c, c = b + 2 - h := ⟨_, rfl⟩
    have hE := E_rec' b h c hh hc
    have h1 : 1 ≤ h := by omega
    have c1 : 1 ≤ c := by omega
    have h2 : 1 ≤ 2 * h := by omega
    have c2 : 1 ≤ 2 * c := by omega
    have hhb : h ≤ b + 1 := by omega
    have hsum : h + c = b + 2 := by omega
    have th := tail h h1 (b + 1 - h)
    rw [show h - 1 + (b + 1 - h) = b by omega] at th
    have tc := tail c c1 h
    rw [show c - 1 + h = b + 1 by omega] at tc
    have ihh := ih h (by omega)
    have ihc := ih c (by omega)
    have hV := V_rec b h c hh hc
    show Q (b + 2) (b + 1) = (b + 2) * (b + 1) + 2 * V (b + 2)
    zify [h1, c1, h2, c2, hhb] at hE th tc ihh ihc hV hsum ⊢
    linear_combination hE + th + tc + ihh + ihc - 2 * hV + ((b : ℤ) + 1 - h + c) * hsum

theorem a_eq_E (n : ℕ) (hn : 1 ≤ n) : a (n - 1) = ∑ k ∈ Finset.range (n - 1), C k n := by
  have h1 := a_eq (n - 1)
  have h2 := E_closed n
  rw [show n - 1 + 1 = n by omega] at h1
  unfold Q at h2
  rw [h1, h2, Nat.mul_comm (n - 1) n]

/-! Part C: the process. -/

theorem find_eq {n k : ℕ} {c : ℕ → ℕ} (hlow : ∀ i < k, c i = 0) (hk : c k ≠ 0) (hkn : k < n)
    (h : ∃ j, j < n ∧ c j ≠ 0) : Nat.find h = k := by
  rw [Nat.find_eq_iff]
  exact ⟨⟨hkn, hk⟩, fun j hj hcj => hcj.2 (hlow j hj)⟩

theorem step_one {n k : ℕ} {c : ℕ → ℕ} (hlow : ∀ i < k, c i = 0) (hk : c k = 1)
    (hkn : k + 1 < n) :
    step n c = fun i => if i = k then 0 else if i = k + 1 then c i + 1 else c i := by
  have h : ∃ j, j < n ∧ c j ≠ 0 := ⟨k, by omega, by omega⟩
  have hf : Nat.find h = k := find_eq hlow (by omega) (by omega) h
  rw [step, dif_pos h]
  simp only [hf, hkn, hk, ↓reduceIte]

theorem step_wall {n : ℕ} {c : ℕ → ℕ} (hk : 2 ≤ c 0) (hkn : 1 < n) :
    step n c = fun i => if i = 0 then c 0 - c 0 / 2 else if i = 1 then c i + c 0 / 2 else c i := by
  have h : ∃ j, j < n ∧ c j ≠ 0 := ⟨0, by omega, by omega⟩
  have hf : Nat.find h = 0 :=
    find_eq (k := 0) (fun i hi => absurd hi (Nat.not_lt_zero i)) (by omega) (by omega) h
  have hne : c 0 ≠ 1 := by omega
  have hkn' : 0 + 1 < n := by omega
  rw [step, dif_pos h]
  simp only [hf, hkn', hne, ↓reduceIte]

theorem step_mid {n k : ℕ} {c : ℕ → ℕ} (hlow : ∀ i < k, c i = 0) (hk : 2 ≤ c k) (hk0 : k ≠ 0)
    (hkn : k + 1 < n) :
    step n c = fun i => if i = k then c k - 2 * (c k / 2)
      else if i = k + 1 ∨ i + 1 = k then c i + c k / 2 else c i := by
  have h : ∃ j, j < n ∧ c j ≠ 0 := ⟨k, by omega, by omega⟩
  have hf : Nat.find h = k := find_eq hlow (by omega) (by omega) h
  have hne : c k ≠ 1 := by omega
  rw [step, dif_pos h]
  simp only [hf, hkn, hne, hk0, ↓reduceIte]

/-- Emptying the boxes `0..k` into box `k + 1`. -/
def shift (k : ℕ) (c : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i ≤ k then 0 else if i = k + 1 then c i + c k else c i

theorem shift_apply (k : ℕ) (c : ℕ → ℕ) (i : ℕ) :
    shift k c i = if i ≤ k then 0 else if i = k + 1 then c i + c k else c i := rfl

theorem low_at {k : ℕ} {c : ℕ → ℕ} (hlow : ∀ i < k, c i = 0) (i : ℕ) : ¬ i < k ∨ c i = 0 := by
  by_cases h : i < k
  · exact Or.inr (hlow i h)
  · exact Or.inl h

theorem congr_at (c : ℕ → ℕ) (i j : ℕ) : i ≠ j ∨ c i = c j := by
  by_cases h : i = j
  · exact Or.inr (by rw [h])
  · exact Or.inl h

/-- Locality (`L1`): from boxes `< k` empty and `b` balls in box `k`, after `C k b` steps the boxes
`0..k` are empty and the `b` balls were added to box `k + 1`; before that some box `≤ k` is
nonempty. -/
theorem L1 (n : ℕ) (b : ℕ) : ∀ (k : ℕ) (c : ℕ → ℕ), (∀ i < k, c i = 0) → c k = b → k + 1 < n →
    (step n)^[C k b] c = shift k c ∧ ∀ t < C k b, ∃ i ≤ k, (step n)^[t] c i ≠ 0 := by
  refine Nat.strong_induction_on b ?_
  intro b ih k c hlow hkb hkn
  by_cases hb0 : b = 0
  · subst hb0
    rw [C_zero]
    refine ⟨?_, fun t ht => absurd ht (Nat.not_lt_zero t)⟩
    rw [Function.iterate_zero_apply]
    funext i
    have h1 := low_at hlow i
    have h2 := congr_at c i k
    rw [shift_apply k c i]
    split_ifs <;> omega
  by_cases hb1 : b = 1
  · subst hb1
    rw [C_one]
    have hs := step_one hlow hkb hkn
    have hc : ∀ i, step n c i = if i = k then 0 else if i = k + 1 then c i + 1 else c i :=
      fun i => congrFun hs i
    refine ⟨?_, fun t ht => ⟨k, le_rfl, ?_⟩⟩
    · rw [Function.iterate_one]
      funext i
      have h1 := low_at hlow i
      have h2 := congr_at c i k
      rw [hc i, shift_apply k c i]
      split_ifs <;> omega
    · have ht0 : t = 0 := by omega
      subst ht0
      rw [Function.iterate_zero_apply]
      omega
  have hb2 : 2 ≤ b := by omega
  rcases k with _ | k
  · -- the wall: box 0
    have hs := step_wall (n := n) (c := c) (by omega) (by omega)
    have hc : ∀ i, step n c i =
        if i = 0 then c 0 - c 0 / 2 else if i = 1 then c i + c 0 / 2 else c i :=
      fun i => congrFun hs i
    have hc0 : step n c 0 = b - b / 2 := by
      rw [hc 0]
      split_ifs <;> omega
    obtain ⟨hA, hA'⟩ := ih (b - b / 2) (by omega) 0 (step n c)
      (fun i hi => absurd hi (Nat.not_lt_zero i)) hc0 (by omega)
    rw [C_wall b hb2]
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_add_apply, Function.iterate_one, hA]
      funext i
      rw [shift_apply 0 (step n c) i, shift_apply 0 c i, hc i, hc0]
      split_ifs <;> omega
    · intro t ht
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · subst h0
        exact ⟨0, le_rfl, by rw [Function.iterate_zero_apply]; omega⟩
      · obtain ⟨i, hi, hne⟩ := hA' (t - 1) (by omega)
        refine ⟨i, hi, ?_⟩
        rw [show t = (t - 1) + 1 by omega, Function.iterate_add_apply, Function.iterate_one]
        exact hne
  · -- an inner box k + 1
    have hs := step_mid (n := n) (k := k + 1) (c := c) hlow (by omega) (by omega) hkn
    have hc : ∀ i, step n c i = if i = k + 1 then c (k + 1) - 2 * (c (k + 1) / 2)
        else if i = k + 1 + 1 ∨ i + 1 = k + 1 then c i + c (k + 1) / 2 else c i :=
      fun i => congrFun hs i
    have hck : c k = 0 := hlow k (by omega)
    have hstepk : step n c k = b / 2 := by
      rw [hc k]
      split_ifs <;> omega
    have hstepk1 : step n c (k + 1) = b - 2 * (b / 2) := by
      rw [hc (k + 1)]
      split_ifs <;> omega
    obtain ⟨hA, hA'⟩ := ih (b / 2) (by omega) k (step n c)
      (fun i hi => by
        have := hlow i (by omega)
        rw [hc i]
        split_ifs <;> omega)
      hstepk (by omega)
    have hB0 : shift k (step n c) (k + 1) = b - b / 2 := by
      rw [shift_apply, hstepk1, hstepk]
      split_ifs <;> omega
    obtain ⟨hB, hB'⟩ := ih (b - b / 2) (by omega) (k + 1) (shift k (step n c))
      (fun i hi => by
        rw [shift_apply]
        split_ifs <;> omega)
      hB0 hkn
    rw [C_succ k b hb2]
    refine ⟨?_, ?_⟩
    · rw [Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one, hA, hB]
      funext i
      rw [shift_apply (k + 1) (shift k (step n c)) i, hB0, shift_apply k (step n c) i,
        shift_apply (k + 1) c i, hc i, hstepk]
      split_ifs <;> omega
    · intro t ht
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · subst h0
        exact ⟨k + 1, le_rfl, by rw [Function.iterate_zero_apply]; omega⟩
      · by_cases ht1 : t < C k (b / 2) + 1
        · obtain ⟨i, hi, hne⟩ := hA' (t - 1) (by omega)
          refine ⟨i, by omega, ?_⟩
          rw [show t = (t - 1) + 1 by omega, Function.iterate_add_apply, Function.iterate_one]
          exact hne
        · obtain ⟨i, hi, hne⟩ := hB' (t - (C k (b / 2) + 1)) (by omega)
          refine ⟨i, hi, ?_⟩
          rw [show t = (t - (C k (b / 2) + 1)) + C k (b / 2) + 1 by omega,
            Function.iterate_add_apply, Function.iterate_add_apply, Function.iterate_one, hA]
          exact hne

/-- All `n` balls in box `m`. -/
def conf (n m i : ℕ) : ℕ := if i = m then n else 0

/-- `L3`: after the phases `0..m-1` all balls are in box `m`, and the target was not met before. -/
theorem phases (n : ℕ) (hn : 1 ≤ n) (m : ℕ) : m ≤ n - 1 →
    (step n)^[∑ k ∈ Finset.range m, C k n] (start n) = conf n m ∧
      ∀ t < ∑ k ∈ Finset.range m, C k n, (step n)^[t] (start n) ≠ target n := by
  induction m with
  | zero =>
    intro _
    refine ⟨?_, fun t ht => absurd ht (by simp)⟩
    rw [Finset.sum_range_zero, Function.iterate_zero_apply]
    funext i
    rfl
  | succ m ih =>
    intro hm
    obtain ⟨h1, h2⟩ := ih (by omega)
    have hlowm : ∀ i < m, conf n m i = 0 := fun i hi => by
      rw [conf]
      split_ifs <;> omega
    have hmm : conf n m m = n := by simp [conf]
    obtain ⟨hA, hA'⟩ := L1 n n m (conf n m) hlowm hmm (by omega)
    rw [Finset.sum_range_succ]
    refine ⟨?_, ?_⟩
    · rw [Nat.add_comm (∑ k ∈ Finset.range m, C k n) (C m n), Function.iterate_add_apply, h1, hA]
      funext i
      simp only [shift_apply, conf]
      split_ifs <;> omega
    · intro t ht heq
      by_cases ht' : t < ∑ k ∈ Finset.range m, C k n
      · exact h2 t ht' heq
      · obtain ⟨i, hi, hne⟩ := hA' (t - ∑ k ∈ Finset.range m, C k n) (by omega)
        apply hne
        rw [show t = (t - ∑ k ∈ Finset.range m, C k n) + ∑ k ∈ Finset.range m, C k n by omega,
          Function.iterate_add_apply, h1] at heq
        rw [heq]
        simp only [target]
        split_ifs <;> omega

end OMA.A077071Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a077071.main := by
  intro n hn
  rw [OMA.A077071Proof.a_eq_E n hn]
  exact OMA.A077071Proof.phases n hn (n - 1) le_rfl
