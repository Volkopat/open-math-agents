import OMAReductions.R_Erdos39_erdos_39_R2

-- Step Erdos39.erdos_39.R2.H2: hypothesis H2 of reduction Erdos39.erdos_39.R2
-- Credit: @nnkostov
-- H2 := ∃ (E : ℕ → ℕ) (h : ℕ → ℕ),     (∀ r ≥ 1, ∃ J, ∀ j ≥ J, (h j) ^ r ≤ 2 ^ j) ∧     (∀ a b u v, E a + E b = E u + E v →       a + b = u + v ∧         ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨          (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u))) ∧     ∀ j, ∀ a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), 1 ≤ E a ∧ E a ≤ 2 ^ j * h j

/-!
# Sub-exponential additive dyadic-label code (`Erdos39.erdos_39.R2.H2`)

We construct an explicit injective additive code `E : ℕ → ℕ` and a sub-exponential
bound `h : ℕ → ℕ` such that `E a + E b = E u + E v` uniquely determines both the sum
`a + b = u + v` and the unordered multiset `{Nat.log 2 a, Nat.log 2 b}`, while
`1 ≤ E a ≤ 2 ^ j * h j` holds for all `a ∈ [2 ^ j, 2 ^ (j + 1))` and `(h j) ^ r ≤ 2 ^ j`
for all `r ≥ 1` and sufficiently large `j`.

The construction slices `a` at triangular bit positions `tri k = k * (k + 1) / 2` into
`(k + 1)`-bit chunks `aChunk a k`, interleaves the bits of `Nat.log 2 a` (at even indices)
and `(Nat.log 2 a) ^ 2` (at odd indices) in higher bit positions of digit `k`, and places
digit `k` at base-2 offset `bpos k = tri k + 3 * k`. Because adjacent digits have `k + 4`
bit headroom and `digit a k + digit b k < 2 ^ (k + 4)`, additions of two codes are
completely carry-free at every level.
-/

namespace OMA.Erdos39R2H2

open Finset

/- Section 1: Triangular numbers and digit bit offsets -/

private def tri : ℕ → ℕ
  | 0 => 0
  | k + 1 => tri k + (k + 1)

private lemma two_mul_tri (k : ℕ) : 2 * tri k = k * (k + 1) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [tri]
    nlinarith

private lemma tri_mono : Monotone tri := by
  intro a b hab
  induction hab with
  | refl => exact le_rfl
  | step h ih => exact ih.trans (Nat.le_add_right _ _)

private lemma le_tri (k : ℕ) : k ≤ tri k := by
  induction k with
  | zero => exact le_rfl
  | succ k ih =>
    simp only [tri]
    omega

private def bpos (k : ℕ) : ℕ := tri k + 3 * k

private lemma bpos_succ (k : ℕ) : bpos (k + 1) = bpos k + (k + 4) := by
  simp only [bpos, tri]
  omega

private lemma two_mul_bpos (k : ℕ) : 2 * bpos k = k ^ 2 + 7 * k := by
  have h := two_mul_tri k
  simp only [bpos]
  nlinarith

/- Section 2: Bit chunks, logarithmic bit extraction, and mixed-radix digits -/

private def aChunk (a k : ℕ) : ℕ := (a / 2 ^ tri k) % 2 ^ (k + 1)

private lemma aChunk_lt (a k : ℕ) : aChunk a k < 2 ^ (k + 1) :=
  Nat.mod_lt _ (pow_pos (by decide) _)

private lemma aChunk_eq_zero_of_lt {a k : ℕ} (ha : a < 2 ^ tri k) : aChunk a k = 0 := by
  simp only [aChunk, Nat.div_eq_of_lt ha, Nat.zero_mod]

private lemma sum_aChunk_eq_mod (a N : ℕ) :
    ∑ k ∈ Finset.range N, aChunk a k * 2 ^ tri k = a % 2 ^ tri N := by
  induction N with
  | zero =>
    simp [tri, Nat.mod_one]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have htri : tri (N + 1) = tri N + (N + 1) := rfl
    rw [htri, pow_add]
    have hpow_pos : 0 < 2 ^ tri N * 2 ^ (N + 1) :=
      mul_pos (pow_pos (by decide) _) (pow_pos (by decide) _)
    let q := a / 2 ^ tri N
    let r := a % 2 ^ tri N
    have ha_decomp : a = r + (q % 2 ^ (N + 1)) * 2 ^ tri N +
        (2 ^ tri N * 2 ^ (N + 1)) * (q / 2 ^ (N + 1)) := by
      have h1 : 2 ^ tri N * q + r = a := Nat.div_add_mod a (2 ^ tri N)
      have h2 : 2 ^ (N + 1) * (q / 2 ^ (N + 1)) + q % 2 ^ (N + 1) = q :=
        Nat.div_add_mod q (2 ^ (N + 1))
      calc
        a = 2 ^ tri N * q + r := h1.symm
        _ = 2 ^ tri N * (2 ^ (N + 1) * (q / 2 ^ (N + 1)) + q % 2 ^ (N + 1)) + r := by rw [h2]
        _ = r + (q % 2 ^ (N + 1)) * 2 ^ tri N +
              (2 ^ tri N * 2 ^ (N + 1)) * (q / 2 ^ (N + 1)) := by ring
    have hr_lt : r < 2 ^ tri N := Nat.mod_lt _ (pow_pos (by decide) _)
    have hq_le : q % 2 ^ (N + 1) + 1 ≤ 2 ^ (N + 1) :=
      Nat.lt_iff_add_one_le.mp (Nat.mod_lt _ (pow_pos (by decide) _))
    have hrem_lt : r + (q % 2 ^ (N + 1)) * 2 ^ tri N < 2 ^ tri N * 2 ^ (N + 1) := by
      calc
        r + (q % 2 ^ (N + 1)) * 2 ^ tri N
            < 2 ^ tri N + (q % 2 ^ (N + 1)) * 2 ^ tri N := Nat.add_lt_add_right hr_lt _
        _ = (q % 2 ^ (N + 1) + 1) * 2 ^ tri N := by ring
        _ ≤ 2 ^ (N + 1) * 2 ^ tri N := Nat.mul_le_mul_right _ hq_le
        _ = 2 ^ tri N * 2 ^ (N + 1) := by ring
    conv_rhs => rw [ha_decomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt]
    rfl

private lemma sum_aChunk_eq {a N : ℕ} (ha : a < 2 ^ tri N) :
    ∑ k ∈ Finset.range N, aChunk a k * 2 ^ tri k = a := by
  rw [sum_aChunk_eq_mod, Nat.mod_eq_of_lt ha]

private def bitAt (x m : ℕ) : ℕ := (x / 2 ^ m) % 2

private lemma bitAt_le_one (x m : ℕ) : bitAt x m ≤ 1 :=
  Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))

private lemma bitAt_eq_zero_of_lt {x m : ℕ} (hx : x < 2 ^ m) : bitAt x m = 0 := by
  simp only [bitAt, Nat.div_eq_of_lt hx, Nat.zero_mod]

private lemma sum_bitAt_eq_mod (x M : ℕ) :
    ∑ m ∈ Finset.range M, bitAt x m * 2 ^ m = x % 2 ^ M := by
  induction M with
  | zero =>
    simp [Nat.mod_one]
  | succ M ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    let q := x / 2 ^ M
    let r := x % 2 ^ M
    have hx_decomp : x = r + (q % 2) * 2 ^ M + (2 ^ M * 2) * (q / 2) := by
      have h1 : 2 ^ M * q + r = x := Nat.div_add_mod x (2 ^ M)
      have h2 : 2 * (q / 2) + q % 2 = q := Nat.div_add_mod q 2
      calc
        x = 2 ^ M * q + r := h1.symm
        _ = 2 ^ M * (2 * (q / 2) + q % 2) + r := by rw [h2]
        _ = r + (q % 2) * 2 ^ M + (2 ^ M * 2) * (q / 2) := by ring
    have hr_lt : r < 2 ^ M := Nat.mod_lt _ (pow_pos (by decide) _)
    have hq_le : q % 2 + 1 ≤ 2 := Nat.lt_iff_add_one_le.mp (Nat.mod_lt _ (by decide))
    have hrem_lt : r + (q % 2) * 2 ^ M < 2 ^ M * 2 := by
      calc
        r + (q % 2) * 2 ^ M < 2 ^ M + (q % 2) * 2 ^ M := Nat.add_lt_add_right hr_lt _
        _ = (q % 2 + 1) * 2 ^ M := by ring
        _ ≤ 2 * 2 ^ M := Nat.mul_le_mul_right _ hq_le
        _ = 2 ^ M * 2 := by ring
    conv_rhs => rw [hx_decomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hrem_lt]
    rfl

private lemma sum_bitAt_eq {x M : ℕ} (hx : x < 2 ^ M) :
    ∑ m ∈ Finset.range M, bitAt x m * 2 ^ m = x := by
  rw [sum_bitAt_eq_mod, Nat.mod_eq_of_lt hx]

private def bBit (a k : ℕ) : ℕ :=
  if k % 2 = 0 then bitAt (Nat.log 2 a) (k / 2) else bitAt ((Nat.log 2 a) ^ 2) (k / 2)

private lemma bBit_le_one (a k : ℕ) : bBit a k ≤ 1 := by
  unfold bBit
  split_ifs <;> exact bitAt_le_one _ _

private lemma bBit_even (a m : ℕ) : bBit a (2 * m) = bitAt (Nat.log 2 a) m := by
  simp [bBit]

private lemma bBit_odd (a m : ℕ) : bBit a (2 * m + 1) = bitAt ((Nat.log 2 a) ^ 2) m := by
  have hdiv : (2 * m + 1) / 2 = m := by omega
  simp [bBit, hdiv]

private lemma bBit_eq_zero_of_gt {a k : ℕ} (hsq : (Nat.log 2 a) ^ 2 < 2 ^ (k / 2)) :
    bBit a k = 0 := by
  have hj : Nat.log 2 a < 2 ^ (k / 2) :=
    lt_of_le_of_lt (Nat.le_self_pow (by decide : 2 ≠ 0) _) hsq
  unfold bBit
  split_ifs
  · exact bitAt_eq_zero_of_lt hj
  · exact bitAt_eq_zero_of_lt hsq

private lemma sq_lt_two_pow_add_three (j : ℕ) : j ^ 2 < 2 ^ (j + 3) := by
  induction j with
  | zero => decide
  | succ j ih =>
    rcases le_or_gt 3 j with hj3 | hj3
    · have h2j1 : 2 * j + 1 < 2 ^ (j + 3) := by
        have h1 : 2 * j + 1 ≤ j ^ 2 := by nlinarith
        exact lt_of_le_of_lt h1 ih
      calc
        (j + 1) ^ 2 = j ^ 2 + (2 * j + 1) := by ring
        _ < 2 ^ (j + 3) + 2 ^ (j + 3) := Nat.add_lt_add ih h2j1
        _ = 2 ^ (j + 1 + 3) := by rw [show j + 1 + 3 = (j + 3) + 1 by omega, pow_succ]; ring
    · interval_cases j <;> decide

private def digit (a k : ℕ) : ℕ := aChunk a k + bBit a k * 2 ^ (k + 2)

private lemma digit_sum_lt (a b k : ℕ) : digit a k + digit b k < 2 ^ (k + 4) := by
  have ha := aChunk_lt a k
  have hb := aChunk_lt b k
  have hba := bBit_le_one a k
  have hbb := bBit_le_one b k
  have h2k1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_add]; ring
  have h2k2 : 2 ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
  have h2k4 : 2 ^ (k + 4) = 16 * 2 ^ k := by rw [pow_add]; ring
  have hbb_le : (bBit a k + bBit b k) * 2 ^ (k + 2) ≤ 2 * 2 ^ (k + 2) :=
    Nat.mul_le_mul_right _ (by omega)
  have hdig : digit a k + digit b k =
      (aChunk a k + aChunk b k) + (bBit a k + bBit b k) * 2 ^ (k + 2) := by
    simp only [digit]; ring
  omega

private lemma digit_zero (k : ℕ) : digit 0 k = 0 := by
  simp [digit, aChunk, bBit, bitAt]

private lemma digit_eq_zero_of_ge {a k : ℕ} (hk : 2 * (Nat.log 2 a + 1) + 4 ≤ k) :
    digit a k = 0 := by
  rcases eq_or_ne a 0 with rfl | ha0
  · exact digit_zero k
  · have halog : a < 2 ^ (Nat.log 2 a + 1) := Nat.lt_pow_succ_log_self (by decide) a
    have hk_tri : Nat.log 2 a + 1 ≤ tri k := by
      have h1 : Nat.log 2 a + 1 ≤ k := by omega
      exact h1.trans (le_tri k)
    have ha_lt_tri : a < 2 ^ tri k :=
      lt_of_lt_of_le halog (Nat.pow_le_pow_right (by decide) hk_tri)
    have hc0 : aChunk a k = 0 := aChunk_eq_zero_of_lt ha_lt_tri
    have hk2 : Nat.log 2 a + 3 ≤ k / 2 := by omega
    have hsq_lt : (Nat.log 2 a) ^ 2 < 2 ^ (k / 2) :=
      lt_of_lt_of_le (sq_lt_two_pow_add_three (Nat.log 2 a))
        (Nat.pow_le_pow_right (by decide) hk2)
    have hb0 : bBit a k = 0 := bBit_eq_zero_of_gt hsq_lt
    simp [digit, hc0, hb0]

private def E (a : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (2 * (Nat.log 2 a + 1) + 4), digit a k * 2 ^ bpos k

private lemma E_zero : E 0 = 0 := by
  simp [E, digit_zero]

private lemma E_eq_sum {a N : ℕ} (hN : 2 * (Nat.log 2 a + 1) + 4 ≤ N) :
    E a = ∑ k ∈ Finset.range N, digit a k * 2 ^ bpos k := by
  unfold E
  refine Finset.sum_subset (Finset.range_mono hN) ?_
  intro k _ hk_not
  have hk_ge : 2 * (Nat.log 2 a + 1) + 4 ≤ k := by
    rw [Finset.mem_range, not_lt] at hk_not
    exact hk_not
  rw [digit_eq_zero_of_ge hk_ge, zero_mul]

/- Section 3: Mixed-radix uniqueness and additive pair-sum recovery -/

private lemma sum_bpos_lt (c : ℕ → ℕ) (N : ℕ) (hc : ∀ k < N, c k < 2 ^ (k + 4)) :
    ∑ k ∈ Finset.range N, c k * 2 ^ bpos k < 2 ^ bpos N := by
  induction N with
  | zero =>
    simp [bpos, tri]
  | succ N ih =>
    rw [Finset.sum_range_succ]
    have hprev := ih (fun k hk => hc k (Nat.lt_succ_of_lt hk))
    have hcN : c N + 1 ≤ 2 ^ (N + 4) := Nat.lt_iff_add_one_le.mp (hc N (Nat.lt_succ_self N))
    calc
      (∑ k ∈ Finset.range N, c k * 2 ^ bpos k) + c N * 2 ^ bpos N
          < 2 ^ bpos N + c N * 2 ^ bpos N := Nat.add_lt_add_right hprev _
      _ = (c N + 1) * 2 ^ bpos N := by ring
      _ ≤ 2 ^ (N + 4) * 2 ^ bpos N := Nat.mul_le_mul_right _ hcN
      _ = 2 ^ bpos (N + 1) := by rw [bpos_succ, pow_add]; ring

private lemma split_mod_eq {x₁ y₁ x₂ y₂ M : ℕ} (hx₁ : x₁ < M) (hx₂ : x₂ < M)
    (h : x₁ + y₁ * M = x₂ + y₂ * M) : x₁ = x₂ ∧ y₁ = y₂ := by
  have hmod1 : (x₁ + y₁ * M) % M = x₁ := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx₁]
  have hmod2 : (x₂ + y₂ * M) % M = x₂ := by
    rw [Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hx₂]
  have hx : x₁ = x₂ := hmod1 ▸ hmod2 ▸ congrArg (· % M) h
  have hyM : y₁ * M = y₂ * M := by omega
  have hMpos : 0 < M := lt_of_le_of_lt (Nat.zero_le x₁) hx₁
  exact ⟨hx, Nat.eq_of_mul_eq_mul_right hMpos hyM⟩

private lemma sum_bpos_inj (c d : ℕ → ℕ) (N : ℕ)
    (hc : ∀ k < N, c k < 2 ^ (k + 4)) (hd : ∀ k < N, d k < 2 ^ (k + 4))
    (heq : ∑ k ∈ Finset.range N, c k * 2 ^ bpos k =
      ∑ k ∈ Finset.range N, d k * 2 ^ bpos k) :
    ∀ k < N, c k = d k := by
  induction N with
  | zero =>
    intro k hk
    omega
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at heq
    have hc_prev := sum_bpos_lt c N (fun k hk => hc k (Nat.lt_succ_of_lt hk))
    have hd_prev := sum_bpos_lt d N (fun k hk => hd k (Nat.lt_succ_of_lt hk))
    obtain ⟨hsum_eq, hN_eq⟩ := split_mod_eq hc_prev hd_prev heq
    have hlt_eq := ih (fun k hk => hc k (Nat.lt_succ_of_lt hk))
      (fun k hk => hd k (Nat.lt_succ_of_lt hk)) hsum_eq
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | rfl
    · exact hlt_eq k h
    · exact hN_eq

private lemma unordered_pair_eq_of_sum_and_sq {x y z w : ℕ}
    (hs : x + y = z + w) (hsq : x ^ 2 + y ^ 2 = z ^ 2 + w ^ 2) :
    (x = z ∧ y = w) ∨ (x = w ∧ y = z) := by
  have hsZ : (x : ℤ) + y = z + w := by exact_mod_cast hs
  have hsqZ : (x : ℤ) ^ 2 + y ^ 2 = z ^ 2 + w ^ 2 := by exact_mod_cast hsq
  have hprod : ((x : ℤ) - z) * ((x : ℤ) - w) = 0 := by
    have h2 : 2 * (((x : ℤ) - z) * ((x : ℤ) - w)) = 0 := by
      calc
        2 * (((x : ℤ) - z) * ((x : ℤ) - w))
            = ((x : ℤ) ^ 2 + y ^ 2 - (z ^ 2 + w ^ 2)) +
              ((z + w) ^ 2 - (x + y) ^ 2) + 2 * x * ((x + y) - (z + w)) := by ring
        _ = 0 := by rw [hsZ, hsqZ]; ring
    omega
  rcases mul_eq_zero.mp hprod with hxz | hxw
  · have hxzN : x = z := by omega
    left
    exact ⟨hxzN, by omega⟩
  · have hxwN : x = w := by omega
    right
    exact ⟨hxwN, by omega⟩

private lemma E_pair_sum_recovery (a b u v : ℕ) (hE : E a + E b = E u + E v) :
    a + b = u + v ∧
      ((Nat.log 2 a = Nat.log 2 u ∧ Nat.log 2 b = Nat.log 2 v) ∨
       (Nat.log 2 a = Nat.log 2 v ∧ Nat.log 2 b = Nat.log 2 u)) := by
  let ja := Nat.log 2 a
  let jb := Nat.log 2 b
  let ju := Nat.log 2 u
  let jv := Nat.log 2 v
  let M := max (max ja jb) (max ju jv) + 3
  let N := 2 * M
  have hMa : 2 * (ja + 1) + 4 ≤ N := by dsimp [N, M]; omega
  have hMb : 2 * (jb + 1) + 4 ≤ N := by dsimp [N, M]; omega
  have hMu : 2 * (ju + 1) + 4 ≤ N := by dsimp [N, M]; omega
  have hMv : 2 * (jv + 1) + 4 ≤ N := by dsimp [N, M]; omega
  have hEab : ∑ k ∈ Finset.range N, (digit a k + digit b k) * 2 ^ bpos k =
      ∑ k ∈ Finset.range N, (digit u k + digit v k) * 2 ^ bpos k := by
    simp only [Nat.add_mul, Finset.sum_add_distrib]
    rw [← E_eq_sum hMa, ← E_eq_sum hMb, ← E_eq_sum hMu, ← E_eq_sum hMv]
    exact hE
  have hdigits : ∀ k < N, digit a k + digit b k = digit u k + digit v k :=
    sum_bpos_inj (fun k => digit a k + digit b k) (fun k => digit u k + digit v k) N
      (fun k _ => digit_sum_lt a b k) (fun k _ => digit_sum_lt u v k) hEab
  have hchunk_eq : ∀ k < N, aChunk a k + aChunk b k = aChunk u k + aChunk v k := by
    intro k hk
    have h1 : aChunk a k + aChunk b k < 2 ^ (k + 2) := by
      have ha := aChunk_lt a k
      have hb := aChunk_lt b k
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      omega
    have h2 : aChunk u k + aChunk v k < 2 ^ (k + 2) := by
      have hu := aChunk_lt u k
      have hv := aChunk_lt v k
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      omega
    have hsplit : (aChunk a k + aChunk b k) + (bBit a k + bBit b k) * 2 ^ (k + 2) =
        (aChunk u k + aChunk v k) + (bBit u k + bBit v k) * 2 ^ (k + 2) := by
      have hk_eq := hdigits k hk
      simp only [digit] at hk_eq
      linarith
    exact (split_mod_eq h1 h2 hsplit).1
  have hbbit_eq : ∀ k < N, bBit a k + bBit b k = bBit u k + bBit v k := by
    intro k hk
    have h1 : aChunk a k + aChunk b k < 2 ^ (k + 2) := by
      have ha := aChunk_lt a k
      have hb := aChunk_lt b k
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      omega
    have h2 : aChunk u k + aChunk v k < 2 ^ (k + 2) := by
      have hu := aChunk_lt u k
      have hv := aChunk_lt v k
      rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
      omega
    have hsplit : (aChunk a k + aChunk b k) + (bBit a k + bBit b k) * 2 ^ (k + 2) =
        (aChunk u k + aChunk v k) + (bBit u k + bBit v k) * 2 ^ (k + 2) := by
      have hk_eq := hdigits k hk
      simp only [digit] at hk_eq
      linarith
    exact (split_mod_eq h1 h2 hsplit).2
  have hlt_tri : ∀ x, Nat.log 2 x + 3 ≤ M → x < 2 ^ tri N := by
    intro x hx
    rcases eq_or_ne x 0 with rfl | hx0
    · exact pow_pos (by decide) _
    · have h1 : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by decide) x
      have h2 : Nat.log 2 x + 1 ≤ tri N := by
        have : Nat.log 2 x + 1 ≤ N := by dsimp [N]; omega
        exact this.trans (le_tri N)
      exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h2)
  have hsum_ab : a + b = u + v := by
    have ha := sum_aChunk_eq (hlt_tri a (by dsimp [M, ja]; omega))
    have hb := sum_aChunk_eq (hlt_tri b (by dsimp [M, jb]; omega))
    have hu := sum_aChunk_eq (hlt_tri u (by dsimp [M, ju]; omega))
    have hv := sum_aChunk_eq (hlt_tri v (by dsimp [M, jv]; omega))
    calc
      a + b = (∑ k ∈ Finset.range N, aChunk a k * 2 ^ tri k) +
                ∑ k ∈ Finset.range N, aChunk b k * 2 ^ tri k := by rw [ha, hb]
      _ = ∑ k ∈ Finset.range N, (aChunk a k + aChunk b k) * 2 ^ tri k := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
      _ = ∑ k ∈ Finset.range N, (aChunk u k + aChunk v k) * 2 ^ tri k := by
            refine Finset.sum_congr rfl fun k hk => ?_
            rw [hchunk_eq k (Finset.mem_range.mp hk)]
      _ = (∑ k ∈ Finset.range N, aChunk u k * 2 ^ tri k) +
            ∑ k ∈ Finset.range N, aChunk v k * 2 ^ tri k := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun k _ => ?_
            ring
      _ = u + v := by rw [hu, hv]
  have hsq_lt_M : ∀ x, Nat.log 2 x + 3 ≤ M → (Nat.log 2 x) ^ 2 < 2 ^ M := by
    intro x hx
    exact lt_of_lt_of_le (sq_lt_two_pow_add_three (Nat.log 2 x))
      (Nat.pow_le_pow_right (by decide) hx)
  have hj_lt_M : ∀ x, Nat.log 2 x + 3 ≤ M → Nat.log 2 x < 2 ^ M := by
    intro x hx
    exact lt_of_le_of_lt (Nat.le_self_pow (by decide : 2 ≠ 0) _) (hsq_lt_M x hx)
  have hlog_sum : ja + jb = ju + jv := by
    have ha := sum_bitAt_eq (hj_lt_M a (by dsimp [M, ja]; omega))
    have hb := sum_bitAt_eq (hj_lt_M b (by dsimp [M, jb]; omega))
    have hu := sum_bitAt_eq (hj_lt_M u (by dsimp [M, ju]; omega))
    have hv := sum_bitAt_eq (hj_lt_M v (by dsimp [M, jv]; omega))
    calc
      ja + jb = (∑ m ∈ Finset.range M, bBit a (2 * m) * 2 ^ m) +
                  ∑ m ∈ Finset.range M, bBit b (2 * m) * 2 ^ m := by
            simp only [bBit_even]; rw [ha, hb]
      _ = ∑ m ∈ Finset.range M, (bBit a (2 * m) + bBit b (2 * m)) * 2 ^ m := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
      _ = ∑ m ∈ Finset.range M, (bBit u (2 * m) + bBit v (2 * m)) * 2 ^ m := by
            refine Finset.sum_congr rfl fun m hm => ?_
            have hmN : 2 * m < N := by dsimp [N]; rw [Finset.mem_range] at hm; omega
            rw [hbbit_eq (2 * m) hmN]
      _ = (∑ m ∈ Finset.range M, bBit u (2 * m) * 2 ^ m) +
            ∑ m ∈ Finset.range M, bBit v (2 * m) * 2 ^ m := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
      _ = ju + jv := by simp only [bBit_even]; rw [hu, hv]
  have hlog_sq_sum : ja ^ 2 + jb ^ 2 = ju ^ 2 + jv ^ 2 := by
    have ha := sum_bitAt_eq (hsq_lt_M a (by dsimp [M, ja]; omega))
    have hb := sum_bitAt_eq (hsq_lt_M b (by dsimp [M, jb]; omega))
    have hu := sum_bitAt_eq (hsq_lt_M u (by dsimp [M, ju]; omega))
    have hv := sum_bitAt_eq (hsq_lt_M v (by dsimp [M, jv]; omega))
    calc
      ja ^ 2 + jb ^ 2 = (∑ m ∈ Finset.range M, bBit a (2 * m + 1) * 2 ^ m) +
                          ∑ m ∈ Finset.range M, bBit b (2 * m + 1) * 2 ^ m := by
            simp only [bBit_odd]; rw [ha, hb]
      _ = ∑ m ∈ Finset.range M, (bBit a (2 * m + 1) + bBit b (2 * m + 1)) * 2 ^ m := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
      _ = ∑ m ∈ Finset.range M, (bBit u (2 * m + 1) + bBit v (2 * m + 1)) * 2 ^ m := by
            refine Finset.sum_congr rfl fun m hm => ?_
            have hmN : 2 * m + 1 < N := by dsimp [N]; rw [Finset.mem_range] at hm; omega
            rw [hbbit_eq (2 * m + 1) hmN]
      _ = (∑ m ∈ Finset.range M, bBit u (2 * m + 1) * 2 ^ m) +
            ∑ m ∈ Finset.range M, bBit v (2 * m + 1) * 2 ^ m := by
            rw [← Finset.sum_add_distrib]
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
      _ = ju ^ 2 + jv ^ 2 := by simp only [bBit_odd]; rw [hu, hv]
  exact ⟨hsum_ab, unordered_pair_eq_of_sum_and_sq hlog_sum hlog_sq_sum⟩

/- Section 4: Size bounds and sub-exponential growth of `h` -/

private def hExp (j : ℕ) : ℕ :=
  max (3 * (Nat.sqrt (2 * j) + 1) + 1) (bpos (4 * Nat.log 2 j + 4)) + 1

private def h (j : ℕ) : ℕ := 2 ^ hExp j

private lemma E_pos_of_pos {a : ℕ} (ha : 1 ≤ a) : 1 ≤ E a := by
  by_contra! hlt
  have hE0 : E a = 0 := by omega
  have hsum := E_pair_sum_recovery a 0 0 0 (by simp [hE0, E_zero])
  omega

private lemma E_A_sum_le (j a : ℕ) (ha_hi : a < 2 ^ (j + 1)) :
    ∑ k ∈ Finset.range (2 * (j + 1) + 4), (aChunk a k * 2 ^ tri k) * 2 ^ (3 * k) ≤
      2 ^ j * 2 ^ (3 * (Nat.sqrt (2 * j) + 1) + 1) := by
  let N := 2 * (j + 1) + 4
  let k₀ := Nat.sqrt (2 * j) + 1
  have hk₀_tri : j + 1 ≤ tri k₀ := by
    have hs : 2 * j < k₀ * (k₀ + 1) := by
      have h1 : 2 * j < (Nat.sqrt (2 * j) + 1) * (Nat.sqrt (2 * j) + 1) :=
        Nat.lt_succ_sqrt (2 * j)
      have h2 : 2 * j < k₀ * k₀ := h1
      have h3 : k₀ * k₀ ≤ k₀ * (k₀ + 1) := Nat.mul_le_mul_left k₀ (Nat.le_succ k₀)
      omega
    have htri := two_mul_tri k₀
    omega
  have ha_lt_tri : a < 2 ^ tri k₀ :=
    lt_of_lt_of_le ha_hi (Nat.pow_le_pow_right (by decide) hk₀_tri)
  have hA_zero : ∀ k, k₀ ≤ k → aChunk a k = 0 := by
    intro k hk
    exact aChunk_eq_zero_of_lt
      (lt_of_lt_of_le ha_lt_tri (Nat.pow_le_pow_right (by decide) (tri_mono hk)))
  have hk₀_le_N : k₀ ≤ N := by
    have hsq : Nat.sqrt (2 * j) ≤ 2 * j := Nat.sqrt_le_self (2 * j)
    dsimp [k₀, N]
    omega
  have hsub : ∑ k ∈ Finset.range N, (aChunk a k * 2 ^ tri k) * 2 ^ (3 * k) =
      ∑ k ∈ Finset.range k₀, (aChunk a k * 2 ^ tri k) * 2 ^ (3 * k) := by
    refine (Finset.sum_subset (Finset.range_mono hk₀_le_N) ?_).symm
    intro k _ hk_not
    rw [Finset.mem_range, not_lt] at hk_not
    rw [hA_zero k hk_not, zero_mul, zero_mul]
  rw [hsub]
  calc
    ∑ k ∈ Finset.range k₀, (aChunk a k * 2 ^ tri k) * 2 ^ (3 * k)
        ≤ ∑ k ∈ Finset.range k₀, (aChunk a k * 2 ^ tri k) * 2 ^ (3 * k₀) := by
          refine Finset.sum_le_sum fun k hk => ?_
          exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide)
            (by rw [Finset.mem_range] at hk; omega))
    _ = (∑ k ∈ Finset.range k₀, aChunk a k * 2 ^ tri k) * 2 ^ (3 * k₀) := by
          rw [← Finset.sum_mul]
    _ = a * 2 ^ (3 * k₀) := by rw [sum_aChunk_eq ha_lt_tri]
    _ ≤ 2 ^ (j + 1) * 2 ^ (3 * k₀) := Nat.mul_le_mul_right _ ha_hi.le
    _ = 2 ^ j * 2 ^ (3 * k₀ + 1) := by rw [pow_succ, pow_succ]; ring

private lemma E_B_sum_le (j a : ℕ) (hlog : Nat.log 2 a = j) :
    ∑ k ∈ Finset.range (2 * (j + 1) + 4), (bBit a k * 2 ^ (k + 2)) * 2 ^ bpos k ≤
      2 ^ j * 2 ^ bpos (4 * Nat.log 2 j + 4) := by
  let N := 2 * (j + 1) + 4
  let K_B := 4 * Nat.log 2 j + 4
  have hB_zero : ∀ k, K_B ≤ k → bBit a k = 0 := by
    intro k hk
    have hsq_lt : (Nat.log 2 a) ^ 2 < 2 ^ (k / 2) := by
      rw [hlog]
      rcases eq_or_ne j 0 with rfl | hj0
      · simp [pow_pos]
      · have hj_lt : j < 2 ^ (Nat.log 2 j + 1) := Nat.lt_pow_succ_log_self (by decide) j
        have h1 : j ^ 2 < 2 ^ (2 * Nat.log 2 j + 2) := by
          calc
            j ^ 2 < (2 ^ (Nat.log 2 j + 1)) ^ 2 := Nat.pow_lt_pow_left hj_lt (by decide)
            _ = 2 ^ (2 * Nat.log 2 j + 2) := by rw [← pow_mul]; congr 1; ring
        have h2 : 2 * Nat.log 2 j + 2 ≤ k / 2 := by dsimp [K_B] at hk; omega
        exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h2)
    exact bBit_eq_zero_of_gt hsq_lt
  let M_B := max N K_B
  have h1 : ∑ k ∈ Finset.range N, (bBit a k * 2 ^ (k + 2)) * 2 ^ bpos k =
      ∑ k ∈ Finset.range M_B, (bBit a k * 2 ^ (k + 2)) * 2 ^ bpos k := by
    refine Finset.sum_subset (Finset.range_mono (le_max_left _ _)) ?_
    intro k _ hk_not
    rw [Finset.mem_range, not_lt] at hk_not
    have hle1 : 2 * (Nat.log 2 a + 1) + 4 ≤ k := by simp only [hlog]; exact hk_not
    have hle2 : Nat.log 2 a + 3 ≤ k / 2 := by omega
    have hsq : (Nat.log 2 a) ^ 2 < 2 ^ (k / 2) :=
      lt_of_lt_of_le (sq_lt_two_pow_add_three _) (Nat.pow_le_pow_right (by decide) hle2)
    rw [bBit_eq_zero_of_gt hsq, zero_mul, zero_mul]
  have h2 : ∑ k ∈ Finset.range M_B, (bBit a k * 2 ^ (k + 2)) * 2 ^ bpos k =
      ∑ k ∈ Finset.range K_B, (bBit a k * 2 ^ (k + 2)) * 2 ^ bpos k := by
    refine (Finset.sum_subset (Finset.range_mono (le_max_right _ _)) ?_).symm
    intro k _ hk_not
    rw [Finset.mem_range, not_lt] at hk_not
    rw [hB_zero k hk_not, zero_mul, zero_mul]
  have hlt_KB : ∑ k ∈ Finset.range K_B, (bBit a k * 2 ^ (k + 2)) * 2 ^ bpos k < 2 ^ bpos K_B := by
    refine sum_bpos_lt (fun k => bBit a k * 2 ^ (k + 2)) K_B fun k _ => ?_
    have hb1 : bBit a k ≤ 1 := bBit_le_one a k
    have hmul : bBit a k * 2 ^ (k + 2) ≤ 2 ^ (k + 2) :=
      (Nat.mul_le_mul_right (2 ^ (k + 2)) hb1).trans_eq (one_mul _)
    have hpow_lt : 2 ^ (k + 2) < 2 ^ (k + 4) := Nat.pow_lt_pow_right (by decide) (by omega)
    exact lt_of_le_of_lt hmul hpow_lt
  have hle_j : 2 ^ bpos K_B ≤ 2 ^ j * 2 ^ bpos K_B :=
    Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
  rw [h1, h2]
  exact hlt_KB.le.trans hle_j

private lemma E_bounds (j a : ℕ) (ha : a ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1))) :
    1 ≤ E a ∧ E a ≤ 2 ^ j * h j := by
  rw [Finset.mem_Ico] at ha
  obtain ⟨ha_lo, ha_hi⟩ := ha
  have ha1 : 1 ≤ a := (Nat.one_le_pow j 2 (by decide)).trans ha_lo
  refine ⟨E_pos_of_pos ha1, ?_⟩
  have hlog : Nat.log 2 a = j := Nat.log_eq_of_pow_le_of_lt_pow ha_lo ha_hi
  have hE_eq : E a = ∑ k ∈ Finset.range (2 * (j + 1) + 4), digit a k * 2 ^ bpos k := by
    rw [E_eq_sum (a := a) (N := 2 * (j + 1) + 4) (by simp only [hlog]; exact le_rfl)]
  have hdecomp : E a =
      (∑ k ∈ Finset.range (2 * (j + 1) + 4), (aChunk a k * 2 ^ tri k) * 2 ^ (3 * k)) +
      (∑ k ∈ Finset.range (2 * (j + 1) + 4), (bBit a k * 2 ^ (k + 2)) * 2 ^ bpos k) := by
    rw [hE_eq, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [digit, bpos, pow_add]
    ring
  have hA_sum := E_A_sum_le j a ha_hi
  have hB_sum := E_B_sum_le j a hlog
  let e := max (3 * (Nat.sqrt (2 * j) + 1) + 1) (bpos (4 * Nat.log 2 j + 4))
  have hA_le : 2 ^ j * 2 ^ (3 * (Nat.sqrt (2 * j) + 1) + 1) ≤ 2 ^ j * 2 ^ e :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (le_max_left _ _))
  have hB_le : 2 ^ j * 2 ^ bpos (4 * Nat.log 2 j + 4) ≤ 2 ^ j * 2 ^ e :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (le_max_right _ _))
  have hstep1 : E a ≤ 2 ^ j * 2 ^ (3 * (Nat.sqrt (2 * j) + 1) + 1) +
      2 ^ j * 2 ^ bpos (4 * Nat.log 2 j + 4) := by
    rw [hdecomp]
    exact Nat.add_le_add hA_sum hB_sum
  have hstep2 : 2 ^ j * 2 ^ (3 * (Nat.sqrt (2 * j) + 1) + 1) +
      2 ^ j * 2 ^ bpos (4 * Nat.log 2 j + 4) ≤ 2 ^ j * 2 ^ e + 2 ^ j * 2 ^ e :=
    Nat.add_le_add hA_le hB_le
  have hstep3 : 2 ^ j * 2 ^ e + 2 ^ j * 2 ^ e = 2 ^ j * h j := by
    have hpow : h j = 2 * 2 ^ e := by
      show 2 ^ (e + 1) = 2 * 2 ^ e
      rw [pow_succ, mul_comm]
    rw [hpow]
    ring
  exact (hstep1.trans hstep2).trans_eq hstep3

private lemma pow4_le_two_pow (m : ℕ) (hm : 16 ≤ m) : m ^ 4 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hm2 : 256 ≤ m ^ 2 := by nlinarith
    have hm3 : 4096 ≤ m ^ 3 := by nlinarith
    have h1 : 16 * m ^ 3 ≤ m ^ 4 := (Nat.mul_le_mul_right (m ^ 3) hm).trans_eq (by ring)
    have h2 : 256 * m ^ 2 ≤ m ^ 4 := (Nat.mul_le_mul_right (m ^ 2) hm2).trans_eq (by ring)
    have h3 : 4096 * m ≤ m ^ 4 := (Nat.mul_le_mul_right m hm3).trans_eq (by ring)
    have hstep : (m + 1) ^ 4 ≤ 2 * m ^ 4 := by
      have hexp : (m + 1) ^ 4 = m ^ 4 + 4 * m ^ 3 + 6 * m ^ 2 + 4 * m + 1 := by ring
      omega
    calc
      (m + 1) ^ 4 ≤ 2 * m ^ 4 := hstep
      _ ≤ 2 * 2 ^ m := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (m + 1) := by rw [pow_succ]; ring

private lemma h_subexp : ∀ r ≥ 1, ∃ J, ∀ j ≥ J, (h j) ^ r ≤ 2 ^ j := by
  intro r hr
  refine ⟨max (2 ^ 16) (1024 * r ^ 2), fun j hj => ?_⟩
  have hj16 : 2 ^ 16 ≤ j := (le_max_left _ _).trans hj
  have hjR : 1024 * r ^ 2 ≤ j := (le_max_right _ _).trans hj
  have hj_pos : 0 < j := lt_of_lt_of_le (by norm_num) hj16
  suffices hexp : r * hExp j ≤ j by
    rw [h, ← pow_mul, mul_comm (hExp j) r]
    exact Nat.pow_le_pow_right (by decide) hexp
  have hb1 : r * (3 * (Nat.sqrt (2 * j) + 1) + 2) ≤ j := by
    let s := Nat.sqrt (2 * j)
    have hs2 : s ^ 2 ≤ 2 * j := by simpa only [sq] using Nat.sqrt_le (2 * j)
    have hsq : (3 * r * s + 5 * r) ^ 2 ≤ j ^ 2 := by
      have hExpand : (3 * r * s + 5 * r) ^ 2 ≤ 18 * r ^ 2 * s ^ 2 + 50 * r ^ 2 := by
        nlinarith [sq_nonneg ((3 : ℤ) * r * s - 5 * r)]
      have h18 : 18 * r ^ 2 * s ^ 2 ≤ 36 * r ^ 2 * j := by nlinarith
      have h50 : 50 * r ^ 2 ≤ r ^ 2 * j := by
        have : 50 ≤ j := le_trans (by norm_num) hj16
        nlinarith
      have hsum : 36 * r ^ 2 * j + r ^ 2 * j ≤ j * j := by nlinarith
      have hjj : j * j = j ^ 2 := by ring
      omega
    have hle : 3 * r * s + 5 * r ≤ j := by
      by_contra! hgt
      have : j ^ 2 < (3 * r * s + 5 * r) ^ 2 := Nat.pow_lt_pow_left hgt (by decide)
      omega
    calc
      r * (3 * (Nat.sqrt (2 * j) + 1) + 2) = 3 * r * s + 5 * r := by dsimp [s]; ring
      _ ≤ j := hle
  have hb2 : r * (bpos (4 * Nat.log 2 j + 4) + 1) ≤ j := by
    let L := Nat.log 2 j
    have hL16 : 16 ≤ L := by
      have hlog16 : 16 = Nat.log 2 (2 ^ 16) := by
        rw [Nat.log_pow (by decide : 1 < 2) 16]
      rw [hlog16]
      exact Nat.log_mono_right hj16
    have hL4 : L ^ 4 ≤ j :=
      (pow4_le_two_pow L hL16).trans (Nat.pow_log_le_self 2 hj_pos.ne')
    have hbpos_2 : 2 * (bpos (4 * L + 4) + 1) = 16 * L ^ 2 + 60 * L + 46 := by
      have := two_mul_bpos (4 * L + 4)
      nlinarith
    have hbpos_le : bpos (4 * L + 4) + 1 ≤ 32 * L ^ 2 := by
      have h60 : 60 * L + 46 ≤ 48 * L ^ 2 := by nlinarith
      omega
    have hsq : (r * (bpos (4 * L + 4) + 1)) ^ 2 ≤ j ^ 2 := by
      have h1 : r * (bpos (4 * L + 4) + 1) ≤ 32 * r * L ^ 2 := by
        calc
          r * (bpos (4 * L + 4) + 1) ≤ r * (32 * L ^ 2) := Nat.mul_le_mul_left r hbpos_le
          _ = 32 * r * L ^ 2 := by ring
      have h2 : (r * (bpos (4 * L + 4) + 1)) ^ 2 ≤ (32 * r * L ^ 2) ^ 2 :=
        Nat.pow_le_pow_left h1 2
      have h3 : (32 * r * L ^ 2) ^ 2 = 1024 * r ^ 2 * L ^ 4 := by ring
      have h4 : 1024 * r ^ 2 * L ^ 4 ≤ 1024 * r ^ 2 * j := Nat.mul_le_mul_left _ hL4
      have h5 : 1024 * r ^ 2 * j ≤ j * j := Nat.mul_le_mul_right j hjR
      have hjj : j * j = j ^ 2 := by ring
      omega
    by_contra! hgt
    have : j ^ 2 < (r * (bpos (4 * L + 4) + 1)) ^ 2 := Nat.pow_lt_pow_left hgt (by decide)
    omega
  rw [hExp]
  rcases le_total (3 * (Nat.sqrt (2 * j) + 1) + 1) (bpos (4 * Nat.log 2 j + 4)) with hle | hle
  · simpa [max_eq_right hle] using hb2
  · simpa [max_eq_left hle] using hb1

private lemma main_proof : OMA.R_Erdos39_erdos_39_R2.H2 :=
  ⟨E, h, h_subexp, E_pair_sum_recovery, E_bounds⟩

end OMA.Erdos39R2H2

theorem OMA.solution : OMA.R_Erdos39_erdos_39_R2.H2 := OMA.Erdos39R2H2.main_proof
