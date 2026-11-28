import OMAStatements.S_oeis_a267452

namespace Ours_oeis_a267452

def ruleOut (left center right : Bool) : Bool :=
  (131 : ℕ).testBit (4 * left.toNat + 2 * center.toNat + right.toNat)


def cell : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | n + 1, i => ruleOut (cell n (i - 1)) (cell n i) (cell n (i + 1))


def rowOn (t : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * t + 1), if cell t ((j : ℤ) - t) then 1 else 0


def a (n : ℕ) : ℤ :=
  ∑ t ∈ Finset.range (n + 1), rowOn t

end Ours_oeis_a267452

namespace ProofA267452

open Ours_oeis_a267452
open PowerSeries

def s12 (z : ℤ) : Prop :=
  z % 12 = 0 ∨ z % 12 = 3 ∨ z % 12 = 4 ∨ z % 12 = 5 ∨ z % 12 = 10

def liveBulk (n i : ℤ) : Prop :=
  i < -n ∨ n < i ∨
    (n - 2 ≤ i ∧ i < n ∧ n % 2 = 0) ∨
    (-n ≤ i ∧ i ≤ 0 ∧ i < n - 2 ∧ (n + i) % 3 = 0) ∨
    (1 ≤ i ∧ i < n - 2 ∧ s12 (8 * n + i))

def live : ℕ → ℤ → Prop
  | 0, i => i = 0
  | 1, i => i ≠ 0 ∧ i ≠ 1
  | 2, i => i ≠ -1 ∧ i ≠ 0 ∧ i ≠ 2
  | m + 3, i => liveBulk ((m : ℤ) + 3) i

def liveDec : ℕ → ℤ → Bool
  | 0, i => decide (i = 0)
  | 1, i => decide (i ≠ 0 ∧ i ≠ 1)
  | 2, i => decide (i ≠ -1 ∧ i ≠ 0 ∧ i ≠ 2)
  | m + 3, i =>
    let n : ℤ := (m : ℤ) + 3
    decide (i < -n ∨ n < i ∨
      (n - 2 ≤ i ∧ i < n ∧ n % 2 = 0) ∨
      (-n ≤ i ∧ i ≤ 0 ∧ i < n - 2 ∧ (n + i) % 3 = 0) ∨
      (1 ≤ i ∧ i < n - 2 ∧
        ((8 * n + i) % 12 = 0 ∨ (8 * n + i) % 12 = 3 ∨
         (8 * n + i) % 12 = 4 ∨ (8 * n + i) % 12 = 5 ∨ (8 * n + i) % 12 = 10)))

lemma liveDec_iff (n : ℕ) (i : ℤ) : liveDec n i = true ↔ live n i := by
  match n with
  | 0 | 1 | 2 => simp [liveDec, live]
  | m + 3 => simp [liveDec, live, liveBulk, s12]

lemma rule131_table (l c r : Bool) :
    ruleOut l c r = true ↔
      ((¬l = true) ∧ (¬c = true)) ∨ (l = true ∧ c = true ∧ r = true) := by
  cases l <;> cases c <;> cases r <;> decide

lemma liveBulk_lt (K x : ℤ) (_hK : 3 ≤ K) (hx : x < -K) :
    liveBulk K x ↔ True := by
  simp [liveBulk, hx]

lemma liveBulk_neg (K x : ℤ) (hK : 3 ≤ K) (hx1 : -K ≤ x) (hx2 : x ≤ 0) :
    liveBulk K x ↔ (K + x) % 3 = 0 := by
  unfold liveBulk
  simp [show ¬(x < -K) by omega, show ¬(K < x) by omega, show ¬(K - 2 ≤ x) by omega,
        hx1, hx2, show x < K - 2 by omega, show ¬(1 ≤ x) by omega]

lemma liveBulk_pos (K x : ℤ) (hK : 3 ≤ K) (hx1 : 1 ≤ x) (hx2 : x < K - 2) :
    liveBulk K x ↔ s12 (8 * K + x) := by
  unfold liveBulk
  simp [show ¬(x < -K) by omega, show ¬(K < x) by omega, show ¬(K - 2 ≤ x) by omega,
        show ¬(x ≤ 0) by omega, hx1, hx2]

lemma liveBulk_tip (K x : ℤ) (hK : 3 ≤ K) (hx1 : K - 2 ≤ x) (hx2 : x < K) :
    liveBulk K x ↔ K % 2 = 0 := by
  unfold liveBulk
  simp [show ¬(x < -K) by omega, show ¬(K < x) by omega, hx1, hx2,
        show ¬(x < K - 2) by omega]

lemma liveBulk_gt (K x : ℤ) (hK : 3 ≤ K) (_hx : K ≤ x) :
    liveBulk K x ↔ K < x := by
  unfold liveBulk
  simp [show ¬(x < -K) by omega, show ¬(x < K) by omega, show ¬(x < K - 2) by omega]

lemma mod3_step (z : ℤ) :
    (((¬(z - 1) % 3 = 0) ∧ (¬z % 3 = 0)) ∨
      ((z - 1) % 3 = 0 ∧ z % 3 = 0 ∧ (z + 1) % 3 = 0)) ↔
      (z + 1) % 3 = 0 := by
  omega

lemma s12_step (z : ℤ) :
    (((¬s12 (z - 1)) ∧ (¬s12 z)) ∨
      (s12 (z - 1) ∧ s12 z ∧ s12 (z + 1))) ↔ s12 (z + 8) := by
  rcases (show z % 12 = 0 ∨ z % 12 = 1 ∨ z % 12 = 2 ∨ z % 12 = 3 ∨
      z % 12 = 4 ∨ z % 12 = 5 ∨ z % 12 = 6 ∨ z % 12 = 7 ∨
      z % 12 = 8 ∨ z % 12 = 9 ∨ z % 12 = 10 ∨ z % 12 = 11 by omega) with
    h | h | h | h | h | h | h | h | h | h | h | h <;>
    (dsimp [s12]; omega)

lemma live_step (n : ℕ) (i : ℤ) :
    (((¬live n (i - 1)) ∧ (¬live n i)) ∨
      (live n (i - 1) ∧ live n i ∧ live n (i + 1))) ↔ live (n + 1) i := by
  match n with
  | 0 | 1 => dsimp [live]; omega
  | 2 => change _ ↔ live (0 + 3) i; dsimp [live, liveBulk, s12]; omega
  | 3 =>
    by_cases hi1 : i ≤ -5
    · change _ ↔ live (1 + 3) i; dsimp [live]
      rw [liveBulk_lt _ (i - 1) (by omega) (by omega), liveBulk_lt _ i (by omega) (by omega),
          liveBulk_lt _ (i + 1) (by omega) (by omega), liveBulk_lt _ i (by omega) (by omega)]
      simp
    · by_cases hi2 : 5 ≤ i
      · change _ ↔ live (1 + 3) i; dsimp [live]
        rw [liveBulk_gt _ (i - 1) (by omega) (by omega), liveBulk_gt _ i (by omega) (by omega),
            liveBulk_gt _ (i + 1) (by omega) (by omega), liveBulk_gt _ i (by omega) (by omega)]
        omega
      · rcases (show i = -4 ∨ i = -3 ∨ i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (simp only [← liveDec_iff]; decide)
  | 4 =>
    by_cases hi1 : i ≤ -6
    · change _ ↔ live (2 + 3) i; dsimp [live]
      rw [liveBulk_lt _ (i - 1) (by omega) (by omega), liveBulk_lt _ i (by omega) (by omega),
          liveBulk_lt _ (i + 1) (by omega) (by omega), liveBulk_lt _ i (by omega) (by omega)]
      simp
    · by_cases hi2 : 6 ≤ i
      · change _ ↔ live (2 + 3) i; dsimp [live]
        rw [liveBulk_gt _ (i - 1) (by omega) (by omega), liveBulk_gt _ i (by omega) (by omega),
            liveBulk_gt _ (i + 1) (by omega) (by omega), liveBulk_gt _ i (by omega) (by omega)]
        omega
      · rcases (show i = -5 ∨ i = -4 ∨ i = -3 ∨ i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 by omega) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          (simp only [← liveDec_iff]; decide)
  | m + 5 =>
    change (((¬liveBulk (((m + 2 : ℕ) : ℤ) + 3) (i - 1)) ∧ (¬liveBulk (((m + 2 : ℕ) : ℤ) + 3) i)) ∨
      (liveBulk (((m + 2 : ℕ) : ℤ) + 3) (i - 1) ∧ liveBulk (((m + 2 : ℕ) : ℤ) + 3) i ∧
       liveBulk (((m + 2 : ℕ) : ℤ) + 3) (i + 1))) ↔
      liveBulk (((m + 3 : ℕ) : ℤ) + 3) i
    have hA : (((m + 2 : ℕ) : ℤ) + 3) = (m : ℤ) + 5 := by omega
    have hB : (((m + 3 : ℕ) : ℤ) + 3) = ((m : ℤ) + 5) + 1 := by omega
    rw [hA, hB]
    generalize hN : (m : ℤ) + 5 = N
    have hN5 : 5 ≤ N := by omega
    clear hA hB hN m
    by_cases c1 : i ≤ -N - 2
    · rw [liveBulk_lt N (i - 1) (by omega) (by omega), liveBulk_lt N i (by omega) (by omega),
          liveBulk_lt N (i + 1) (by omega) (by omega), liveBulk_lt (N + 1) i (by omega) (by omega)]
      simp
    · by_cases c2 : i = -N - 1
      · rw [liveBulk_lt N (i - 1) (by omega) (by omega), liveBulk_lt N i (by omega) (by omega),
            liveBulk_neg N (i + 1) (by omega) (by omega) (by omega),
            liveBulk_neg (N + 1) i (by omega) (by omega) (by omega)]
        simp; omega
      · by_cases c3 : i = -N
        · rw [liveBulk_lt N (i - 1) (by omega) (by omega),
              liveBulk_neg N i (by omega) (by omega) (by omega),
              liveBulk_neg N (i + 1) (by omega) (by omega) (by omega),
              liveBulk_neg (N + 1) i (by omega) (by omega) (by omega)]
          omega
        · by_cases c4 : i ≤ -1
          · rw [liveBulk_neg N (i - 1) (by omega) (by omega) (by omega),
                liveBulk_neg N i (by omega) (by omega) (by omega),
                liveBulk_neg N (i + 1) (by omega) (by omega) (by omega),
                liveBulk_neg (N + 1) i (by omega) (by omega) (by omega)]
            simpa [show N + (i - 1) = (N + i) - 1 by ring,
                   show N + (i + 1) = (N + i) + 1 by ring,
                   show N + 1 + i = (N + i) + 1 by ring] using mod3_step (N + i)
          · by_cases c5 : i = 0
            · rw [liveBulk_neg N (i - 1) (by omega) (by omega) (by omega),
                  liveBulk_neg N i (by omega) (by omega) (by omega),
                  liveBulk_pos N (i + 1) (by omega) (by omega) (by omega),
                  liveBulk_neg (N + 1) i (by omega) (by omega) (by omega)]
              subst c5
              rcases (show N % 12 = 0 ∨ N % 12 = 1 ∨ N % 12 = 2 ∨ N % 12 = 3 ∨
                  N % 12 = 4 ∨ N % 12 = 5 ∨ N % 12 = 6 ∨ N % 12 = 7 ∨
                  N % 12 = 8 ∨ N % 12 = 9 ∨ N % 12 = 10 ∨ N % 12 = 11 by omega) with
                h | h | h | h | h | h | h | h | h | h | h | h <;> (dsimp [s12]; omega)
            · by_cases c6 : i = 1
              · rw [liveBulk_neg N (i - 1) (by omega) (by omega) (by omega),
                    liveBulk_pos N i (by omega) (by omega) (by omega),
                    liveBulk_pos N (i + 1) (by omega) (by omega) (by omega),
                    liveBulk_pos (N + 1) i (by omega) (by omega) (by omega)]
                subst c6
                rcases (show N % 12 = 0 ∨ N % 12 = 1 ∨ N % 12 = 2 ∨ N % 12 = 3 ∨
                    N % 12 = 4 ∨ N % 12 = 5 ∨ N % 12 = 6 ∨ N % 12 = 7 ∨
                    N % 12 = 8 ∨ N % 12 = 9 ∨ N % 12 = 10 ∨ N % 12 = 11 by omega) with
                  h | h | h | h | h | h | h | h | h | h | h | h <;> (dsimp [s12]; omega)
              · by_cases c7 : i ≤ N - 4
                · rw [liveBulk_pos N (i - 1) (by omega) (by omega) (by omega),
                      liveBulk_pos N i (by omega) (by omega) (by omega),
                      liveBulk_pos N (i + 1) (by omega) (by omega) (by omega),
                      liveBulk_pos (N + 1) i (by omega) (by omega) (by omega)]
                  simpa [show 8 * N + (i - 1) = (8 * N + i) - 1 by ring,
                         show 8 * N + (i + 1) = (8 * N + i) + 1 by ring,
                         show 8 * (N + 1) + i = (8 * N + i) + 8 by ring] using s12_step (8 * N + i)
                · by_cases c8 : i = N - 3
                  · rw [liveBulk_pos N (i - 1) (by omega) (by omega) (by omega),
                        liveBulk_pos N i (by omega) (by omega) (by omega),
                        liveBulk_tip N (i + 1) (by omega) (by omega) (by omega),
                        liveBulk_pos (N + 1) i (by omega) (by omega) (by omega)]
                    subst c8
                    rcases (show N % 12 = 0 ∨ N % 12 = 1 ∨ N % 12 = 2 ∨ N % 12 = 3 ∨
                        N % 12 = 4 ∨ N % 12 = 5 ∨ N % 12 = 6 ∨ N % 12 = 7 ∨
                        N % 12 = 8 ∨ N % 12 = 9 ∨ N % 12 = 10 ∨ N % 12 = 11 by omega) with
                      h | h | h | h | h | h | h | h | h | h | h | h <;> (dsimp [s12]; omega)
                  · by_cases c9 : i = N - 2
                    · rw [liveBulk_pos N (i - 1) (by omega) (by omega) (by omega),
                          liveBulk_tip N i (by omega) (by omega) (by omega),
                          liveBulk_tip N (i + 1) (by omega) (by omega) (by omega),
                          liveBulk_pos (N + 1) i (by omega) (by omega) (by omega)]
                      subst c9
                      rcases (show N % 12 = 0 ∨ N % 12 = 1 ∨ N % 12 = 2 ∨ N % 12 = 3 ∨
                          N % 12 = 4 ∨ N % 12 = 5 ∨ N % 12 = 6 ∨ N % 12 = 7 ∨
                          N % 12 = 8 ∨ N % 12 = 9 ∨ N % 12 = 10 ∨ N % 12 = 11 by omega) with
                        h | h | h | h | h | h | h | h | h | h | h | h <;> (dsimp [s12]; omega)
                    · by_cases c10 : i = N - 1
                      · rw [liveBulk_tip N (i - 1) (by omega) (by omega) (by omega),
                            liveBulk_tip N i (by omega) (by omega) (by omega),
                            liveBulk_gt N (i + 1) (by omega) (by omega),
                            liveBulk_tip (N + 1) i (by omega) (by omega) (by omega)]
                        omega
                      · by_cases c11 : i = N
                        · rw [liveBulk_tip N (i - 1) (by omega) (by omega) (by omega),
                              liveBulk_gt N i (by omega) (by omega),
                              liveBulk_gt N (i + 1) (by omega) (by omega),
                              liveBulk_tip (N + 1) i (by omega) (by omega) (by omega)]
                          omega
                        · by_cases c12 : i = N + 1
                          · rw [liveBulk_gt N (i - 1) (by omega) (by omega),
                                liveBulk_gt N i (by omega) (by omega),
                                liveBulk_gt N (i + 1) (by omega) (by omega),
                                liveBulk_gt (N + 1) i (by omega) (by omega)]
                            omega
                          · rw [liveBulk_gt N (i - 1) (by omega) (by omega),
                                liveBulk_gt N i (by omega) (by omega),
                                liveBulk_gt N (i + 1) (by omega) (by omega),
                                liveBulk_gt (N + 1) i (by omega) (by omega)]
                            omega

lemma cell_iff_live (n : ℕ) (i : ℤ) : cell n i = true ↔ live n i := by
  induction n generalizing i with
  | zero => simp [cell, live]
  | succ n ih =>
    rw [cell, rule131_table, ih, ih, ih]
    exact live_step n i

lemma cell_eq_liveDec (n : ℕ) (i : ℤ) : cell n i = liveDec n i :=
  Bool.eq_iff_iff.mpr ((cell_iff_live n i).trans (liveDec_iff n i).symm)

def fastRowOn (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (2 * n + 1), if liveDec n ((j : ℤ) - n) then 1 else 0

lemma rowOn_eq_fastRowOn (n : ℕ) : rowOn n = fastRowOn n := by
  unfold rowOn fastRowOn; simp only [cell_eq_liveDec]

def stepDelta (r : ℕ) : ℤ :=
  if r = 3 then 4 else if r = 1 then 3 else 1

lemma bval_true {k : ℕ} {x : ℤ} (h : live k x) :
    (if liveDec k x then (1 : ℤ) else 0) = 1 :=
  if_pos ((liveDec_iff k x).mpr h)

lemma bval_false {k : ℕ} {x : ℤ} (h : ¬live k x) :
    (if liveDec k x then (1 : ℤ) else 0) = 0 :=
  if_neg fun ht => h ((liveDec_iff k x).mp ht)

lemma fastRowOn_step_three_ge (m : ℕ) :
    fastRowOn (m + 6) = fastRowOn (m + 3) + stepDelta ((m + 3) % 4) := by
  let n := m + 3
  change fastRowOn (n + 3) = fastRowOn n + stepDelta (n % 4)
  unfold fastRowOn
  rw [show 2 * (n + 3) + 1 = (3 + (2 * n - 2)) + 6 by dsimp [n]; omega,
      Finset.sum_range_add, Finset.sum_range_add,
      show 2 * n + 1 = (2 * n - 2) + 3 by dsimp [n]; omega,
      Finset.sum_range_add]
  have hhead : ∑ j ∈ Finset.range 3,
      (if liveDec (n + 3) ((j : ℤ) - ((n + 3 : ℕ) : ℤ)) then (1 : ℤ) else 0) = 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [bval_true (show live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n]; omega),
        bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n]; omega),
        bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n]; omega)]
    norm_num
  have hmid : ∑ r ∈ Finset.range (2 * n - 2),
      (if liveDec (n + 3) (((3 + r : ℕ) : ℤ) - ((n + 3 : ℕ) : ℤ)) then (1 : ℤ) else 0) =
      ∑ r ∈ Finset.range (2 * n - 2), (if liveDec n ((r : ℤ) - n) then 1 else 0) := by
    apply Finset.sum_congr rfl; intro r hr
    have hr' := Finset.mem_range.mp hr
    have heq : liveDec (n + 3) (((3 + r : ℕ) : ℤ) - ((n + 3 : ℕ) : ℤ)) = liveDec n ((r : ℤ) - n) := by
      apply Bool.eq_iff_iff.mpr
      rw [liveDec_iff, liveDec_iff]
      change live ((m + 3) + 3) _ ↔ live (m + 3) _
      dsimp [live, liveBulk, s12, n] at hr' ⊢; omega
    rw [heq]
  have hsuf : (∑ s ∈ Finset.range 6,
      if liveDec (n + 3) ((((3 + (2 * n - 2) + s : ℕ) : ℤ)) - ((n + 3 : ℕ) : ℤ)) then (1 : ℤ) else 0) -
      (∑ t ∈ Finset.range 3,
      if liveDec n ((((2 * n - 2 + t : ℕ) : ℤ)) - n) then (1 : ℤ) else 0) =
      stepDelta (n % 4) - 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    rcases (show n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 by omega) with h4 | h4 | h4 | h4
    · rw [h4, show stepDelta 0 = 1 from rfl]
      rw [bval_true (show live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_true (show live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_true (show live (m + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_true (show live (m + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live (m + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega)]
      norm_num
    · rw [h4, show stepDelta 1 = 3 from rfl]
      rw [bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_true (show live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_true (show live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live (m + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live (m + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live (m + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega)]
      norm_num
    · rw [h4, show stepDelta 2 = 1 from rfl]
      rw [bval_true (show live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_true (show live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_true (show live (m + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_true (show live (m + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live (m + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega)]
      norm_num
    · rw [h4, show stepDelta 3 = 4 from rfl]
      rw [bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_true (show live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_true (show live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_true (show live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live ((m + 3) + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live (m + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live (m + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega),
          bval_false (show ¬live (m + 3) _ by dsimp [live, liveBulk, s12, n] at h4 ⊢; omega)]
      norm_num
  rw [hhead, hmid]
  linarith [hsuf]

lemma rowOn_step_three (n : ℕ) : rowOn (n + 3) = rowOn n + stepDelta (n % 4) := by
  simp only [rowOn_eq_fastRowOn]
  match n with
  | 0 | 1 | 2 => decide
  | m + 3 => exact fastRowOn_step_three_ge m

lemma a_succ (n : ℕ) : a (n + 1) = a n + rowOn (n + 1) := by
  unfold a; rw [Finset.sum_range_succ]

lemma recurrence (n : ℕ) (hn : 7 < n) :
    a n = a (n - 1) + a (n - 3) - a (n - 5) - a (n - 7) + a (n - 8) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 8 := ⟨n - 8, by omega⟩
  simp only [show m + 8 - 1 = m + 7 by omega, show m + 8 - 3 = m + 5 by omega,
    show m + 8 - 5 = m + 3 by omega, show m + 8 - 7 = m + 1 by omega, show m + 8 - 8 = m by omega]
  have d7 := a_succ (m + 7)
  have d4 := a_succ (m + 4)
  have d3 := a_succ (m + 3)
  have d0 := a_succ m
  rw [show (m + 7) + 1 = m + 8 by omega] at d7
  rw [show (m + 4) + 1 = m + 5 by omega] at d4
  rw [show (m + 3) + 1 = m + 4 by omega] at d3
  have r1 := rowOn_step_three (m + 5)
  have r0 := rowOn_step_three (m + 1)
  rw [show (m + 5) + 3 = m + 8 by omega, show (m + 5) % 4 = (m + 1) % 4 by omega] at r1
  rw [show (m + 1) + 3 = m + 4 by omega] at r0
  linarith

lemma initials :
    a 0 = 1 ∧ a 1 = 2 ∧ a 2 = 4 ∧ a 3 = 6 ∧ a 4 = 10 ∧ a 5 = 13 ∧ a 6 = 19 ∧ a 7 = 24 := by
  have r0 : rowOn 0 = 1 := by rw [rowOn_eq_fastRowOn]; decide
  have r1 : rowOn 1 = 1 := by rw [rowOn_eq_fastRowOn]; decide
  have r2 : rowOn 2 = 2 := by rw [rowOn_eq_fastRowOn]; decide
  have r3 : rowOn 3 = 2 := by rw [rowOn_eq_fastRowOn]; decide
  have r4 : rowOn 4 = 4 := by rw [rowOn_eq_fastRowOn]; decide
  have r5 : rowOn 5 = 3 := by rw [rowOn_eq_fastRowOn]; decide
  have r6 : rowOn 6 = 6 := by rw [rowOn_eq_fastRowOn]; decide
  have r7 : rowOn 7 = 5 := by rw [rowOn_eq_fastRowOn]; decide
  have h0 : a 0 = 1 := by decide
  have h1 : a 1 = 2 := by rw [a_succ 0, h0, r1]; norm_num
  have h2 : a 2 = 4 := by rw [a_succ 1, h1, r2]; norm_num
  have h3 : a 3 = 6 := by rw [a_succ 2, h2, r3]; norm_num
  have h4 : a 4 = 10 := by rw [a_succ 3, h3, r4]; norm_num
  have h5 : a 5 = 13 := by rw [a_succ 4, h4, r5]; norm_num
  have h6 : a 6 = 19 := by rw [a_succ 5, h5, r6]; norm_num
  have h7 : a 7 = 24 := by rw [a_succ 6, h6, r7]; norm_num
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩

lemma generating :
    PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2)) =
      1 + X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 + 2 * X ^ 6 := by
  let F : PowerSeries ℚ := PowerSeries.mk (fun n => (a n : ℚ))
  change F * _ = _
  have hprod : F * ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2)) =
      F - F * X ^ 1 - F * X ^ 3 + F * X ^ 5 + F * X ^ 7 - F * X ^ 8 := by ring
  have hrhs : (1 + X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 + 2 * X ^ 6 : PowerSeries ℚ) =
      1 + X ^ 1 * C 1 + X ^ 2 * C 2 + X ^ 3 * C 1 + X ^ 4 * C 2 + X ^ 6 * C 2 := by
    simp only [map_ofNat, map_one]; ring
  rw [hprod, hrhs]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_X_pow_mul', coeff_one, F, coeff_mk]
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := initials
  rcases n with _ | _ | _ | _ | _ | _ | _ | _ | m
  · simp [coeff_C, h0]
  · simp [coeff_C, h0, h1]; try norm_num
  · simp [coeff_C, h1, h2]; try norm_num
  · simp [coeff_C, h0, h2, h3]; try norm_num
  · simp [coeff_C, h1, h3, h4]; try norm_num
  · simp [coeff_C, h0, h2, h4, h5]; try norm_num
  · simp [coeff_C, h1, h3, h5, h6]; try norm_num
  · simp [coeff_C, h0, h2, h4, h6, h7]; try norm_num
  · simp only [show m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 = m + 8 by ring]
    have hr : (a (m + 8) : ℚ) =
        (a (m + 7) : ℚ) + (a (m + 5) : ℚ) - (a (m + 3) : ℚ) - (a (m + 1) : ℚ) + (a m : ℚ) := by
      simpa [show m + 8 - 1 = m + 7 by omega, show m + 8 - 3 = m + 5 by omega,
             show m + 8 - 5 = m + 3 by omega, show m + 8 - 7 = m + 1 by omega,
             show m + 8 - 8 = m by omega] using
        (show (a (m + 8) : ℚ) = (a (m + 8 - 1) : ℚ) + (a (m + 8 - 3) : ℚ) -
            (a (m + 8 - 5) : ℚ) - (a (m + 8 - 7) : ℚ) + (a (m + 8 - 8) : ℚ) from by
          exact_mod_cast recurrence (m + 8) (by omega))
    simp [coeff_C]
    linarith

end ProofA267452

open Ours_oeis_a267452
open PowerSeries in
lemma old_result :
    (∀ n : ℕ, 7 < n →
      a n = a (n - 1) + a (n - 3) - a (n - 5) - a (n - 7) + a (n - 8)) ∧
    (PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - X) ^ 3 * (1 + X) * (1 + X ^ 2) * (1 + X + X ^ 2)) =
      1 + X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 + 2 * X ^ 6) :=
  ⟨ProofA267452.recurrence, ProofA267452.generating⟩

namespace Ours_oeis_a267452

lemma cell_eq (n : ℕ) (i : ℤ) : OMA.S_oeis_a267452.cell 131 n i = cell n i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp only [OMA.S_oeis_a267452.cell, cell, ih] <;> rfl

lemma sequence_eq (n : ℕ) : OMA.S_oeis_a267452.a n = a n := by
  simp only [OMA.S_oeis_a267452.a, a, rowOn, OMA.S_oeis_a267452.onCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, cell_eq]

end Ours_oeis_a267452

theorem OMA.solution : type_of% @OMA.S_oeis_a267452.main := by
  simp only [sequence_eq, Int.cast_natCast, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_ofNat] 
  exact ⟨by
    intro n h
    first | exact old_result.1 n h | exact_mod_cast old_result.1 n h, old_result.2⟩
