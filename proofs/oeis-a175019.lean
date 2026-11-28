import OMAStatements.S_oeis_a175019

/-!
# Proof of `oeis-a175019`

Proves Chai Wah Wu's four occurrence conjectures for OEIS A175019 (`a i = 2 * half i + 1`
where `half 0 = half 1 = 0`, `half (n + 2) = half (n + 2 - (2 * half n + 1)) + 1`).

1. For every `m ≥ 2` and `0 ≤ r ≤ 2 * m`, `half (m * m + r)` equals an explicit 3-branch
   sawtooth formula `Hblk m r`, proved by strong induction on `m * m + r` (base `i < 25`
   by `decide +kernel`).
2. For `n ≥ 2`, `Hblk m r = n` holds only for `m ∈ {n - 1, n, n + 1, n + 2}` on explicit
   arithmetic progressions of step 4, giving the exact finite set `posFinset n` of cardinality
   `2 * n + 2`, least element `(n - 1) ^ 2 + 2`, and greatest element `(n + 3) ^ 2 - 8`.
3. `n = 0` (`{0, 1}`) and `n = 1` (`{2, 4, 5, 8}`) are verified directly.
-/

namespace OMA.A175019Proof

open OMA.S_oeis_a175019 Finset

private def Hblk (m r : ℕ) : ℕ :=
  if r = 2 * m - 3 then m - 1
  else if r < 2 * m - 3 then
    if m % 2 = 1 then m - 2 + (r + 1) % 4 else m + 1 - (r + 2) % 4
  else
    if m % 2 = 1 then m - 1 + (r - (2 * m - 2)) else m + 1 - (r - (2 * m - 2))

private lemma half_small :
    half 0 = 0 ∧ half 1 = 0 ∧ half 2 = 1 ∧ half 3 = 2 ∧
    ∀ i ∈ Finset.Ico 4 25, half i = Hblk (Nat.sqrt i) (i - Nat.sqrt i * Nat.sqrt i) := by
  decide +kernel

private lemma sqrt_unique {m r i : ℕ} (hi : i = m * m + r) (hr : r ≤ 2 * m) :
    Nat.sqrt i = m := by
  rw [hi]
  apply le_antisymm
  · exact Nat.le_of_lt_succ (Nat.sqrt_lt'.mpr (by nlinarith))
  · exact Nat.le_sqrt.mpr (by omega)

set_option maxHeartbeats 800000 in
private lemma Hblk_step_aux {m r : ℕ} (hm : 5 ≤ m) (hr : r ≤ 2 * m) :
    let prev := if 2 ≤ r then Hblk m (r - 2) else Hblk (m - 1) (2 * m - 3 + r)
    let j := m * m + r - (2 * prev + 1)
    let mj :=
      if m * m ≤ j then m
      else if (m - 1) * (m - 1) ≤ j then m - 1
      else m - 2
    2 ≤ mj ∧ mj * mj ≤ j ∧ j ≤ mj * mj + 2 * mj ∧
    Hblk mj (j - mj * mj) + 1 = Hblk m r := by
  -- Split on m % 2 and region of r!
  have hsq1 : (m - 1) * (m - 1) + (2 * m - 1) = m * m := by
    have : (m - 1) * (m - 1) + 2 * (m - 1) + 1 = m * m := by
      have hm1 : (m - 1) + 1 = m := by omega
      nlinarith
    omega
  have hsq2 : (m - 2) * (m - 2) + (2 * m - 3) = (m - 1) * (m - 1) := by
    have : (m - 2) * (m - 2) + 2 * (m - 2) + 1 = (m - 1) * (m - 1) := by
      have hm2 : (m - 2) + 1 = m - 1 := by omega
      nlinarith
    omega
  have hm_par : m % 2 = 0 ∨ m % 2 = 1 := by omega
  rcases hm_par with hmev | hmod
  · -- m even: m ≥ 6!
    have hm6 : 6 ≤ m := by omega
    by_cases hr2 : r < 2
    · -- r = 0 or r = 1
      interval_cases r
      · -- r = 0: prev = Hblk (m-1) (2m-3) = m-1 (odd m-1, r'=2(m-1)-1 = 2m-3 > 2(m-1)-3 = 2m-5 -> m-2+1 = m-1)
        dsimp only
        have hif : (if 2 ≤ 0 then Hblk m (0 - 2) else Hblk (m - 1) (2 * m - 3 + 0)) =
            Hblk (m - 1) (2 * m - 3) := by simp
        rw [hif]
        have hp : Hblk (m - 1) (2 * m - 3) = m - 1 := by
          unfold Hblk
          have h1 : (m - 1) % 2 = 1 := by omega
          simp [h1, show 2 * m - 3 ≠ 2 * (m - 1) - 3 by omega,
            show ¬ 2 * m - 3 < 2 * (m - 1) - 3 by omega]
          omega
        rw [hp]
        have hj : m * m + 0 - (2 * (m - 1) + 1) = (m - 1) * (m - 1) := by omega
        rw [hj]
        have hlt : ¬ m * m ≤ (m - 1) * (m - 1) := by omega
        simp only [hlt, le_refl, ↓reduceIte, Nat.sub_self]
        refine ⟨by omega, trivial, by omega, ?_⟩
        unfold Hblk
        have h1 : (m - 1) % 2 = 1 := by omega
        simp [hmev, h1, show (0 : ℕ) ≠ 2 * (m - 1) - 3 by omega,
          show 0 < 2 * (m - 1) - 3 by omega, show (0 : ℕ) ≠ 2 * m - 3 by omega,
          show 0 < 2 * m - 3 by omega]
        omega
      · -- r = 1: prev = Hblk (m-1) (2m-2) = m (odd m-1)
        dsimp only
        have hif : (if 2 ≤ 1 then Hblk m (1 - 2) else Hblk (m - 1) (2 * m - 3 + 1)) =
            Hblk (m - 1) (2 * m - 3 + 1) := if_neg (by omega)
        rw [hif]
        have hp : Hblk (m - 1) (2 * m - 3 + 1) = m := by
          unfold Hblk
          have h1 : (m - 1) % 2 = 1 := by omega
          simp [h1, show 2 * m - 3 + 1 ≠ 2 * (m - 1) - 3 by omega,
            show ¬ 2 * m - 3 + 1 < 2 * (m - 1) - 3 by omega]
          omega
        rw [hp]
        have hj : m * m + 1 - (2 * m + 1) = (m - 1) * (m - 1) - 1 := by omega
        have hj2 : m * m + 1 - (2 * m + 1) = (m - 2) * (m - 2) + (2 * m - 4) := by omega
        rw [hj2]
        have h1 : ¬ m * m ≤ (m - 2) * (m - 2) + (2 * m - 4) := by omega
        have h2 : ¬ (m - 1) * (m - 1) ≤ (m - 2) * (m - 2) + (2 * m - 4) := by omega
        simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
        refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
        unfold Hblk
        have hev2 : (m - 2) % 2 = 0 := by omega
        simp [hmev, hev2, show 2 * m - 4 ≠ 2 * (m - 2) - 3 by omega,
          show ¬ 2 * m - 4 < 2 * (m - 2) - 3 by omega,
          show (1 : ℕ) ≠ 2 * m - 3 by omega, show 1 < 2 * m - 3 by omega]
        omega
    · -- r ≥ 2, m even
      by_cases hr_mid : r < 2 * m - 3
      · -- 2 ≤ r < 2m - 3: split on r % 4!
        dsimp only
        have hif : (if 2 ≤ r then Hblk m (r - 2) else Hblk (m - 1) (2 * m - 3 + r)) = Hblk m (r - 2) :=
          if_pos (by omega)
        rw [hif]
        have hp : Hblk m (r - 2) = m + 1 - r % 4 := by
          unfold Hblk
          simp only [hmev, show r - 2 ≠ 2 * m - 3 by omega, show r - 2 < 2 * m - 3 by omega,
            show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
          have : (r - 2 + 2) % 4 = r % 4 := by omega
          rw [this]
        rw [hp]
        rcases (show r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 by omega) with h4 | h4 | h4 | h4
        · -- r % 4 = 0: prev = m + 1, j = (m-1)^2 + (r - 4) (note r ≥ 4 since r ≥ 2 and r % 4 = 0!)
          have hr4 : 4 ≤ r := by omega
          have hj : m * m + r - (2 * (m + 1 - 0) + 1) = (m - 1) * (m - 1) + (r - 4) := by omega
          rw [h4, hj]
          have h1 : ¬ m * m ≤ (m - 1) * (m - 1) + (r - 4) := by omega
          have h2 : (m - 1) * (m - 1) ≤ (m - 1) * (m - 1) + (r - 4) := by omega
          simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          have hmod1 : (m - 1) % 2 = 1 := by omega
          simp [hmev, hmod1, show r - 4 ≠ 2 * (m - 1) - 3 by omega,
            show r - 4 < 2 * (m - 1) - 3 by omega, show r ≠ 2 * m - 3 by omega, hr_mid,
            show (r - 4 + 1) % 4 = 1 by omega, show (r + 2) % 4 = 2 by omega]
          omega
        · -- r % 4 = 1: prev = m, j = (m-1)^2 + (r - 2) (note r ≥ 5!)
          have hr5 : 5 ≤ r := by omega
          have hj : m * m + r - (2 * (m + 1 - 1) + 1) = (m - 1) * (m - 1) + (r - 2) := by omega
          rw [h4, hj]
          have h1 : ¬ m * m ≤ (m - 1) * (m - 1) + (r - 2) := by omega
          have h2 : (m - 1) * (m - 1) ≤ (m - 1) * (m - 1) + (r - 2) := by omega
          simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          have hmod1 : (m - 1) % 2 = 1 := by omega
          have hne : r - 2 ≠ 2 * (m - 1) - 3 := by omega
          have hlt : r - 2 < 2 * (m - 1) - 3 := by omega
          simp [hmev, hmod1, hne, hlt, show r ≠ 2 * m - 3 by omega, hr_mid,
            show (r - 2 + 1) % 4 = 0 by omega, show (r + 2) % 4 = 3 by omega]
          omega
        · -- r % 4 = 2: prev = m - 1, j = (m-1)^2 + r
          have hj : m * m + r - (2 * (m + 1 - 2) + 1) = (m - 1) * (m - 1) + r := by omega
          rw [h4, hj]
          have h1 : ¬ m * m ≤ (m - 1) * (m - 1) + r := by omega
          have h2 : (m - 1) * (m - 1) ≤ (m - 1) * (m - 1) + r := by omega
          simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          have hmod1 : (m - 1) % 2 = 1 := by omega
          -- Notice r < 2m - 3 and r % 4 = 2 and m even => 2m - 3 % 4 = 1 (if m%4=2) or 3 (if m%4=0)
          -- What if r = 2m - 4? No, 2m-4 is even! Wait: could r = 2(m-1) - 3 = 2m - 5? No, r even, 2m-5 odd!
          -- Could r > 2m - 5? Only if r = 2m - 4!
          by_cases htop : r < 2 * (m - 1) - 3
          · simp [hmev, hmod1, show r ≠ 2 * (m - 1) - 3 by omega, htop,
              show r ≠ 2 * m - 3 by omega, hr_mid,
              show (r + 1) % 4 = 3 by omega, show (r + 2) % 4 = 0 by omega]
            omega
          · have hreq : r = 2 * m - 4 := by omega
            simp [hmev, hmod1, hreq, show 2 * m - 4 ≠ 2 * (m - 1) - 3 by omega,
              show ¬ 2 * m - 4 < 2 * (m - 1) - 3 by omega,
              show 2 * m - 4 ≠ 2 * m - 3 by omega, show 2 * m - 4 < 2 * m - 3 by omega,
              show (2 * m - 4 + 2) % 4 = 0 by omega]
            omega
        · -- r % 4 = 3: prev = m - 2, j = (m-1)^2 + (r + 2)
          -- Note r ≤ 2m - 5 (since r < 2m-3 and r odd -> r ≤ 2m - 5!)
          have hrle : r ≤ 2 * m - 5 := by omega
          have hj : m * m + r - (2 * (m + 1 - 3) + 1) = (m - 1) * (m - 1) + (r + 2) := by omega
          rw [h4, hj]
          have h1 : ¬ m * m ≤ (m - 1) * (m - 1) + (r + 2) := by omega
          have h2 : (m - 1) * (m - 1) ≤ (m - 1) * (m - 1) + (r + 2) := by omega
          simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          have hmod1 : (m - 1) % 2 = 1 := by omega
          by_cases htop : r + 2 < 2 * (m - 1) - 3
          · simp [hmev, hmod1, show r + 2 ≠ 2 * (m - 1) - 3 by omega, htop,
              show r ≠ 2 * m - 3 by omega, hr_mid,
              show (r + 2 + 1) % 4 = 2 by omega, show (r + 2) % 4 = 1 by omega]
            omega
          · have hreq : r = 2 * m - 5 ∨ r = 2 * m - 7 := by omega
            rcases hreq with rfl | rfl
            · simp [hmev, hmod1, show 2 * m - 5 + 2 ≠ 2 * (m - 1) - 3 by omega,
                show ¬ 2 * m - 5 + 2 < 2 * (m - 1) - 3 by omega,
                show 2 * m - 5 ≠ 2 * m - 3 by omega, show 2 * m - 5 < 2 * m - 3 by omega,
                show (2 * m - 5 + 2) % 4 = 1 by omega]
              omega
            · simp [hmev, show 2 * m - 7 + 2 = 2 * (m - 1) - 3 by omega,
                show 2 * m - 7 ≠ 2 * m - 3 by omega, show 2 * m - 7 < 2 * m - 3 by omega]
              omega
      · -- r ∈ {2m-3, 2m-2, 2m-1, 2m}, m even
        have hrc : r = 2 * m - 3 ∨ r = 2 * m - 2 ∨ r = 2 * m - 1 ∨ r = 2 * m := by omega
        rcases hrc with rfl | rfl | rfl | rfl
        · -- r = 2m - 3: prev = Hblk m (2m - 5) = m + 1 - (2m - 3) % 4
          dsimp only
          have hif : (if 2 ≤ 2 * m - 3 then Hblk m (2 * m - 3 - 2) else Hblk (m - 1) (2 * m - 3 + (2 * m - 3))) =
              Hblk m (2 * m - 3 - 2) := if_pos (by omega)
          rw [hif]
          have hp : Hblk m (2 * m - 3 - 2) = m + 1 - (2 * m - 3) % 4 := by
            unfold Hblk
            simp only [hmev, show 2 * m - 3 - 2 ≠ 2 * m - 3 by omega,
              show 2 * m - 3 - 2 < 2 * m - 3 by omega, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
            congr 1; omega
          rw [hp]
          have hmod : (2 * m - 3) % 4 = 1 := by omega
          rw [hmod]
          have hj : m * m + (2 * m - 3) - (2 * (m + 1 - 1) + 1) = (m - 1) * (m - 1) + (2 * m - 5) := by omega
          rw [hj]
          have h1 : ¬ m * m ≤ (m - 1) * (m - 1) + (2 * m - 5) := by omega
          have h2 : (m - 1) * (m - 1) ≤ (m - 1) * (m - 1) + (2 * m - 5) := by omega
          simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          simp [show 2 * m - 5 = 2 * (m - 1) - 3 by omega]
          omega
        · -- r = 2m - 2: prev = Hblk m (2m - 4) = m + 1 - 2 = m - 1 (since m even => 2m % 4 = 0 => (2m-2)%4=2)
          dsimp only
          have hif : (if 2 ≤ 2 * m - 2 then Hblk m (2 * m - 2 - 2) else Hblk (m - 1) (2 * m - 3 + (2 * m - 2))) =
              Hblk m (2 * m - 2 - 2) := if_pos (by omega)
          rw [hif]
          have hp : Hblk m (2 * m - 2 - 2) = m - 1 := by
            unfold Hblk
            simp only [hmev, show 2 * m - 2 - 2 ≠ 2 * m - 3 by omega,
              show 2 * m - 2 - 2 < 2 * m - 3 by omega, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
            have : (2 * m - 2 - 2 + 2) % 4 = 2 := by omega
            rw [this]; omega
          rw [hp]
          have hj : m * m + (2 * m - 2) - (2 * (m - 1) + 1) = (m - 1) * (m - 1) + (2 * m - 2) := by omega
          rw [hj]
          have h1 : ¬ m * m ≤ (m - 1) * (m - 1) + (2 * m - 2) := by omega
          have h2 : (m - 1) * (m - 1) ≤ (m - 1) * (m - 1) + (2 * m - 2) := by omega
          simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          have hmod1 : (m - 1) % 2 = 1 := by omega
          simp [hmev, hmod1, show 2 * m - 2 ≠ 2 * (m - 1) - 3 by omega,
            show ¬ 2 * m - 2 < 2 * (m - 1) - 3 by omega,
            show 2 * m - 2 ≠ 2 * m - 3 by omega, show ¬ 2 * m - 2 < 2 * m - 3 by omega]
          omega
        · -- r = 2m - 1: prev = Hblk m (2m - 3) = m - 1
          dsimp only
          have hif : (if 2 ≤ 2 * m - 1 then Hblk m (2 * m - 1 - 2) else Hblk (m - 1) (2 * m - 3 + (2 * m - 1))) =
              Hblk m (2 * m - 1 - 2) := if_pos (by omega)
          rw [hif]
          have hp : Hblk m (2 * m - 1 - 2) = m - 1 := by
            unfold Hblk; simp [show 2 * m - 1 - 2 = 2 * m - 3 by omega]
          rw [hp]
          have hj : m * m + (2 * m - 1) - (2 * (m - 1) + 1) = m * m := by
            rw [Nat.add_sub_assoc (by omega)]; simp [show 2 * m - 1 - (2 * (m - 1) + 1) = 0 by omega]
          rw [hj]
          simp only [le_refl, ↓reduceIte, Nat.sub_self]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          simp [hmev, show (0 : ℕ) ≠ 2 * m - 3 by omega, show 0 < 2 * m - 3 by omega,
            show 2 * m - 1 ≠ 2 * m - 3 by omega, show ¬ 2 * m - 1 < 2 * m - 3 by omega]
          omega
        · -- r = 2m: prev = Hblk m (2m - 2) = m + 1
          dsimp only
          have hif : (if 2 ≤ 2 * m then Hblk m (2 * m - 2) else Hblk (m - 1) (2 * m - 3 + 2 * m)) =
              Hblk m (2 * m - 2) := if_pos (by omega)
          rw [hif]
          have hp : Hblk m (2 * m - 2) = m + 1 := by
            unfold Hblk
            simp [hmev, show 2 * m - 2 ≠ 2 * m - 3 by omega, show ¬ 2 * m - 2 < 2 * m - 3 by omega]
          rw [hp]
          have hj : m * m + 2 * m - (2 * (m + 1) + 1) = (m - 1) * (m - 1) + (2 * m - 4) := by omega
          rw [hj]
          have h1 : ¬ m * m ≤ (m - 1) * (m - 1) + (2 * m - 4) := by omega
          have h2 : (m - 1) * (m - 1) ≤ (m - 1) * (m - 1) + (2 * m - 4) := by omega
          simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          have hmod1 : (m - 1) % 2 = 1 := by omega
          simp [hmev, hmod1, show 2 * m - 4 ≠ 2 * (m - 1) - 3 by omega,
            show ¬ 2 * m - 4 < 2 * (m - 1) - 3 by omega,
            show 2 * m ≠ 2 * m - 3 by omega, show ¬ 2 * m < 2 * m - 3 by omega]
          omega
  · -- m odd: m ≥ 5!
    by_cases hr2 : r < 2
    · interval_cases r
      · -- r = 0: prev = Hblk (m-1) (2m-3) = m - 1 (even m-1, r'=2m-3 = 2(m-1)-1 -> m-1)
        dsimp only
        have hif : (if 2 ≤ 0 then Hblk m (0 - 2) else Hblk (m - 1) (2 * m - 3 + 0)) =
            Hblk (m - 1) (2 * m - 3) := by simp
        rw [hif]
        have hp : Hblk (m - 1) (2 * m - 3) = m - 1 := by
          unfold Hblk
          have h1 : (m - 1) % 2 = 0 := by omega
          simp [h1, show 2 * m - 3 ≠ 2 * (m - 1) - 3 by omega,
            show ¬ 2 * m - 3 < 2 * (m - 1) - 3 by omega]
          omega
        rw [hp]
        have hj : m * m + 0 - (2 * (m - 1) + 1) = (m - 1) * (m - 1) := by omega
        rw [hj]
        have hlt : ¬ m * m ≤ (m - 1) * (m - 1) := by omega
        simp only [hlt, le_refl, ↓reduceIte, Nat.sub_self]
        refine ⟨by omega, trivial, by omega, ?_⟩
        unfold Hblk
        have h1 : (m - 1) % 2 = 0 := by omega
        simp [hmod, h1, show (0 : ℕ) ≠ 2 * (m - 1) - 3 by omega,
          show 0 < 2 * (m - 1) - 3 by omega, show (0 : ℕ) ≠ 2 * m - 3 by omega,
          show 0 < 2 * m - 3 by omega]
        omega
      · -- r = 1: prev = Hblk (m-1) (2m-2) = m - 2 (even m-1)
        dsimp only
        have hif : (if 2 ≤ 1 then Hblk m (1 - 2) else Hblk (m - 1) (2 * m - 3 + 1)) =
            Hblk (m - 1) (2 * m - 3 + 1) := if_neg (by omega)
        rw [hif]
        have hp : Hblk (m - 1) (2 * m - 3 + 1) = m - 2 := by
          unfold Hblk
          have h1 : (m - 1) % 2 = 0 := by omega
          simp [h1, show 2 * m - 3 + 1 ≠ 2 * (m - 1) - 3 by omega,
            show ¬ 2 * m - 3 + 1 < 2 * (m - 1) - 3 by omega]
          omega
        rw [hp]
        have hj : m * m + 1 - (2 * (m - 2) + 1) = (m - 1) * (m - 1) + 3 := by omega
        rw [hj]
        have h1 : ¬ m * m ≤ (m - 1) * (m - 1) + 3 := by omega
        have h2 : (m - 1) * (m - 1) ≤ (m - 1) * (m - 1) + 3 := by omega
        simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
        refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
        unfold Hblk
        have h1 : (m - 1) % 2 = 0 := by omega
        simp [hmod, h1, show (3 : ℕ) ≠ 2 * (m - 1) - 3 by omega,
          show 3 < 2 * (m - 1) - 3 by omega, show (1 : ℕ) ≠ 2 * m - 3 by omega,
          show 1 < 2 * m - 3 by omega]
        omega
    · -- r ≥ 2, m odd
      by_cases hr_mid : r < 2 * m - 3
      · dsimp only
        have hif : (if 2 ≤ r then Hblk m (r - 2) else Hblk (m - 1) (2 * m - 3 + r)) = Hblk m (r - 2) :=
          if_pos (by omega)
        rw [hif]
        have hp : Hblk m (r - 2) = m - 2 + (r + 3) % 4 := by
          unfold Hblk
          simp only [hmod, show r - 2 ≠ 2 * m - 3 by omega, show r - 2 < 2 * m - 3 by omega, ↓reduceIte]
          have : (r - 2 + 1) % 4 = (r + 3) % 4 := by omega
          rw [this]
        rw [hp]
        rcases (show r % 4 = 0 ∨ r % 4 = 1 ∨ r % 4 = 2 ∨ r % 4 = 3 by omega) with h4 | h4 | h4 | h4
        · -- r % 4 = 0: prev = m + 1, j = (m-1)^2 + (r - 4)
          have hr4 : 4 ≤ r := by omega
          have h3 : (r + 3) % 4 = 3 := by omega
          have hj : m * m + r - (2 * (m - 2 + 3) + 1) = (m - 1) * (m - 1) + (r - 4) := by
            rw [← hsq1]; omega
          rw [h3, hj]
          have h1 : ¬ m * m ≤ (m - 1) * (m - 1) + (r - 4) := by omega
          have h2 : (m - 1) * (m - 1) ≤ (m - 1) * (m - 1) + (r - 4) := by omega
          simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          have hev1 : (m - 1) % 2 = 0 := by omega
          simp [hmod, hev1, show r - 4 ≠ 2 * (m - 1) - 3 by omega,
            show r - 4 < 2 * (m - 1) - 3 by omega, show r ≠ 2 * m - 3 by omega, hr_mid,
            show (r - 4 + 2) % 4 = 2 by omega, show (r + 1) % 4 = 1 by omega]
          omega
        · -- r % 4 = 1: prev = m - 2, j = (m-1)^2 + (r + 2)
          have h3 : (r + 3) % 4 = 0 := by omega
          have hrle : r ≤ 2 * m - 5 := by omega
          have hj : m * m + r - (2 * (m - 2 + 0) + 1) = (m - 1) * (m - 1) + (r + 2) := by
            rw [← hsq1]; omega
          rw [h3, hj]
          have h1 : ¬ m * m ≤ (m - 1) * (m - 1) + (r + 2) := by omega
          have h2 : (m - 1) * (m - 1) ≤ (m - 1) * (m - 1) + (r + 2) := by omega
          simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          have hev1 : (m - 1) % 2 = 0 := by omega
          by_cases htop : r + 2 < 2 * (m - 1) - 3
          · simp [hmod, hev1, show r + 2 ≠ 2 * (m - 1) - 3 by omega, htop,
              show r ≠ 2 * m - 3 by omega, hr_mid,
              show (r + 2 + 2) % 4 = 1 by omega, show (r + 1) % 4 = 2 by omega]
            omega
          · have hreq : r = 2 * m - 5 ∨ r = 2 * m - 7 := by omega
            rcases hreq with rfl | rfl
            · simp [hmod, hev1, show 2 * m - 5 + 2 ≠ 2 * (m - 1) - 3 by omega,
                show ¬ 2 * m - 5 + 2 < 2 * (m - 1) - 3 by omega,
                show 2 * m - 5 ≠ 2 * m - 3 by omega, show 2 * m - 5 < 2 * m - 3 by omega,
                show (2 * m - 5 + 1) % 4 = 2 by omega]
              omega
            · simp [hmod, show 2 * m - 7 + 2 = 2 * (m - 1) - 3 by omega,
                show 2 * m - 7 ≠ 2 * m - 3 by omega, show 2 * m - 7 < 2 * m - 3 by omega,
                show (2 * m - 7 + 1) % 4 = 2 by omega]
              omega
        · -- r % 4 = 2: prev = m - 1, j = (m-1)^2 + r
          have h3 : (r + 3) % 4 = 1 := by omega
          have hj : m * m + r - (2 * (m - 2 + 1) + 1) = (m - 1) * (m - 1) + r := by
            rw [← hsq1]; omega
          rw [h3, hj]
          have h1 : ¬ m * m ≤ (m - 1) * (m - 1) + r := by omega
          have h2 : (m - 1) * (m - 1) ≤ (m - 1) * (m - 1) + r := by omega
          simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          have hev1 : (m - 1) % 2 = 0 := by omega
          by_cases htop : r < 2 * (m - 1) - 3
          · simp [hmod, hev1, show r ≠ 2 * (m - 1) - 3 by omega, htop,
              show r ≠ 2 * m - 3 by omega, hr_mid,
              show (r + 2) % 4 = 0 by omega, show (r + 1) % 4 = 3 by omega]
            omega
          · have hreq : r = 2 * m - 4 := by omega
            simp [hmod, hev1, hreq, show 2 * m - 4 ≠ 2 * (m - 1) - 3 by omega,
              show ¬ 2 * m - 4 < 2 * (m - 1) - 3 by omega,
              show 2 * m - 4 ≠ 2 * m - 3 by omega, show 2 * m - 4 < 2 * m - 3 by omega,
              show (2 * m - 4 + 1) % 4 = 3 by omega]
            omega
        · -- r % 4 = 3: prev = m, j = (m-1)^2 + (r - 2)
          have h3 : (r + 3) % 4 = 2 := by omega
          have hj : m * m + r - (2 * (m - 2 + 2) + 1) = (m - 1) * (m - 1) + (r - 2) := by
            rw [← hsq1]; omega
          rw [h3, hj]
          have h1 : ¬ m * m ≤ (m - 1) * (m - 1) + (r - 2) := by omega
          have h2 : (m - 1) * (m - 1) ≤ (m - 1) * (m - 1) + (r - 2) := by omega
          simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          have hev1 : (m - 1) % 2 = 0 := by omega
          simp [hmod, hev1, show r - 2 ≠ 2 * (m - 1) - 3 by omega,
            show r - 2 < 2 * (m - 1) - 3 by omega, show r ≠ 2 * m - 3 by omega, hr_mid,
            show (r - 2 + 2) % 4 = 3 by omega, show (r + 1) % 4 = 0 by omega]
          omega
      · -- r ∈ {2m-3, 2m-2, 2m-1, 2m}, m odd
        have hrc : r = 2 * m - 3 ∨ r = 2 * m - 2 ∨ r = 2 * m - 1 ∨ r = 2 * m := by omega
        rcases hrc with rfl | rfl | rfl | rfl
        · -- r = 2m - 3: prev = Hblk m (2m - 5) = m (since m odd => 2m % 4 = 2 => (2m-4)%4 = 2 => m-2+2 = m)
          dsimp only
          have hif : (if 2 ≤ 2 * m - 3 then Hblk m (2 * m - 3 - 2) else Hblk (m - 1) (2 * m - 3 + (2 * m - 3))) =
              Hblk m (2 * m - 3 - 2) := if_pos (by omega)
          rw [hif]
          have hp : Hblk m (2 * m - 3 - 2) = m := by
            unfold Hblk
            simp only [hmod, show 2 * m - 3 - 2 ≠ 2 * m - 3 by omega,
              show 2 * m - 3 - 2 < 2 * m - 3 by omega, ↓reduceIte]
            have : (2 * m - 3 - 2 + 1) % 4 = 2 := by omega
            rw [this]; omega
          rw [hp]
          have hj : m * m + (2 * m - 3) - (2 * m + 1) = (m - 1) * (m - 1) + (2 * m - 5) := by
            rw [← hsq1]; omega
          rw [hj]
          have h1 : ¬ m * m ≤ (m - 1) * (m - 1) + (2 * m - 5) := by omega
          have h2 : (m - 1) * (m - 1) ≤ (m - 1) * (m - 1) + (2 * m - 5) := by omega
          simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          simp [show 2 * m - 5 = 2 * (m - 1) - 3 by omega]
          omega
        · -- r = 2m - 2: prev = Hblk m (2m - 4) = m + 1 (since m odd => (2m-3)%4 = 3 => m-2+3 = m+1)
          dsimp only
          have hif : (if 2 ≤ 2 * m - 2 then Hblk m (2 * m - 2 - 2) else Hblk (m - 1) (2 * m - 3 + (2 * m - 2))) =
              Hblk m (2 * m - 2 - 2) := if_pos (by omega)
          rw [hif]
          have hp : Hblk m (2 * m - 2 - 2) = m + 1 := by
            unfold Hblk
            simp only [hmod, show 2 * m - 2 - 2 ≠ 2 * m - 3 by omega,
              show 2 * m - 2 - 2 < 2 * m - 3 by omega, ↓reduceIte]
            have : (2 * m - 2 - 2 + 1) % 4 = 3 := by omega
            rw [this]; omega
          rw [hp]
          have hj : m * m + (2 * m - 2) - (2 * (m + 1) + 1) = (m - 1) * (m - 1) + (2 * m - 6) := by
            rw [← hsq1]; omega
          rw [hj]
          have h1 : ¬ m * m ≤ (m - 1) * (m - 1) + (2 * m - 6) := by omega
          have h2 : (m - 1) * (m - 1) ≤ (m - 1) * (m - 1) + (2 * m - 6) := by omega
          simp only [h1, h2, ↓reduceIte, Nat.add_sub_cancel_left]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          have hev1 : (m - 1) % 2 = 0 := by omega
          simp [hmod, hev1, show 2 * m - 6 ≠ 2 * (m - 1) - 3 by omega,
            show 2 * m - 6 < 2 * (m - 1) - 3 by omega,
            show 2 * m - 2 ≠ 2 * m - 3 by omega, show ¬ 2 * m - 2 < 2 * m - 3 by omega,
            show (2 * m - 6 + 2) % 4 = 2 by omega]
          omega
        · -- r = 2m - 1: prev = Hblk m (2m - 3) = m - 1
          dsimp only
          have hif : (if 2 ≤ 2 * m - 1 then Hblk m (2 * m - 1 - 2) else Hblk (m - 1) (2 * m - 3 + (2 * m - 1))) =
              Hblk m (2 * m - 1 - 2) := if_pos (by omega)
          rw [hif]
          have hp : Hblk m (2 * m - 1 - 2) = m - 1 := by
            unfold Hblk; simp [show 2 * m - 1 - 2 = 2 * m - 3 by omega]
          rw [hp]
          have hj : m * m + (2 * m - 1) - (2 * (m - 1) + 1) = m * m := by
            rw [Nat.add_sub_assoc (by omega)]; simp [show 2 * m - 1 - (2 * (m - 1) + 1) = 0 by omega]
          rw [hj]
          simp only [le_refl, ↓reduceIte, Nat.sub_self]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          simp [hmod, show (0 : ℕ) ≠ 2 * m - 3 by omega, show 0 < 2 * m - 3 by omega,
            show 2 * m - 1 ≠ 2 * m - 3 by omega, show ¬ 2 * m - 1 < 2 * m - 3 by omega]
          omega
        · -- r = 2m: prev = Hblk m (2m - 2) = m - 1
          dsimp only
          have hif : (if 2 ≤ 2 * m then Hblk m (2 * m - 2) else Hblk (m - 1) (2 * m - 3 + 2 * m)) =
              Hblk m (2 * m - 2) := if_pos (by omega)
          rw [hif]
          have hp : Hblk m (2 * m - 2) = m - 1 := by
            unfold Hblk
            simp [hmod, show 2 * m - 2 ≠ 2 * m - 3 by omega, show ¬ 2 * m - 2 < 2 * m - 3 by omega]
          rw [hp]
          have hj : m * m + 2 * m - (2 * (m - 1) + 1) = m * m + 1 := by
            rw [Nat.add_sub_assoc (by omega)]; congr 1; omega
          rw [hj]
          simp only [show m * m ≤ m * m + 1 by omega, ↓reduceIte, Nat.add_sub_cancel_left]
          refine ⟨by omega, by first | trivial | omega, by omega, ?_⟩
          unfold Hblk
          simp [hmod, show (1 : ℕ) ≠ 2 * m - 3 by omega, show 1 < 2 * m - 3 by omega,
            show 2 * m ≠ 2 * m - 3 by omega, show ¬ 2 * m < 2 * m - 3 by omega]
          omega

private lemma half_eq_Hblk : ∀ i : ℕ, 4 ≤ i →
    half i = Hblk (Nat.sqrt i) (i - Nat.sqrt i * Nat.sqrt i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi4
    by_cases h25 : i < 25
    · exact half_small.2.2.2.2 i (Finset.mem_Ico.mpr ⟨hi4, h25⟩)
    · set m := Nat.sqrt i
      set r := i - m * m
      have hm5 : 5 ≤ m := Nat.le_sqrt.mpr (by omega)
      have hsq_le : m * m ≤ i := Nat.sqrt_le i
      have hlt_sq : i < m * m + 2 * m + 1 := by have := Nat.lt_succ_sqrt i; nlinarith
      have hr : r ≤ 2 * m := by omega
      have hi_eq : i = m * m + r := by omega
      have hprev_eq : half (i - 2) =
          if 2 ≤ r then Hblk m (r - 2) else Hblk (m - 1) (2 * m - 3 + r) := by
        rw [ih (i - 2) (by omega) (by omega)]
        by_cases hr2 : 2 ≤ r
        · rw [if_pos hr2]
          have hsq : Nat.sqrt (i - 2) = m := sqrt_unique (r := r - 2) (by omega) (by omega)
          rw [hsq, show i - 2 - m * m = r - 2 by omega]
        · rw [if_neg hr2]
          have hm1 : 1 ≤ m := by omega
          have h2m : 1 ≤ 2 * m := by omega
          have hsq1 : (m - 1) * (m - 1) + (2 * m - 1) = m * m := by zify [hm1, h2m]; ring
          have hsq : Nat.sqrt (i - 2) = m - 1 :=
            sqrt_unique (r := 2 * m - 3 + r) (by omega) (by omega)
          rw [hsq, show i - 2 - (m - 1) * (m - 1) = 2 * m - 3 + r by omega]
      have hstep := Hblk_step_aux hm5 hr
      dsimp only at hstep
      rcases hstep with ⟨hmj2, hmj_le, hmj_hi, hH_eq⟩
      set prev := if 2 ≤ r then Hblk m (r - 2) else Hblk (m - 1) (2 * m - 3 + r)
      set j := m * m + r - (2 * prev + 1)
      set mj := if m * m ≤ j then m else if (m - 1) * (m - 1) ≤ j then m - 1 else m - 2
      have hi2 : i = (i - 2) + 2 := by omega
      have hhalf_unfold : half i = half (i - (2 * half (i - 2) + 1)) + 1 := by
        conv_lhs => rw [hi2, half]
        simp [show i - 2 + 2 = i by omega]
      rw [hhalf_unfold, hprev_eq]
      have hj_eq : i - (2 * prev + 1) = j := by rw [hi_eq]
      rw [hj_eq]
      have hj4 : 4 ≤ j := by nlinarith
      have hj_lt : j < i := by
        have hpos : 0 < 2 * prev + 1 := by omega
        omega
      rw [ih j hj_lt hj4]
      have hsqj : Nat.sqrt j = mj := sqrt_unique (r := j - mj * mj) (by omega) (by omega)
      rw [hsqj]
      exact hH_eq

private lemma Hblk_bounds {m r : ℕ} (hm : 2 ≤ m) (hr : r ≤ 2 * m) :
    m - 2 ≤ Hblk m r ∧ Hblk m r ≤ m + 1 := by
  unfold Hblk
  split_ifs <;> omega

private lemma Hblk_eq_iff {m r n : ℕ} (hm : 2 ≤ m) (hr : r ≤ 2 * m) :
    Hblk m r = n → m = n - 1 ∨ m = n ∨ m = n + 1 ∨ m = n + 2 := by
  intro h
  have := Hblk_bounds hm hr
  omega

-- Explicit Finset of all positions where half i = n (for n ≥ 2)
private def posFinset (n : ℕ) : Finset ℕ :=
  (Finset.range ((n + 3) ^ 2)).filter (fun i => half i = n)

private lemma mem_positions_iff (n i : ℕ) : i ∈ positions n ↔ half i = n := by
  unfold positions a
  change 2 * half i + 1 = 2 * n + 1 ↔ half i = n
  omega

private lemma half_gt_of_ge {n i : ℕ} (hn : 2 ≤ n) (hi : (n + 3) ^ 2 - 7 ≤ i) : n < half i := by
  have h7 : 7 ≤ (n + 3) ^ 2 := by nlinarith
  have hi4 : 4 ≤ i := by zify [h7] at hn hi ⊢; nlinarith
  rw [half_eq_Hblk i hi4]
  set m := Nat.sqrt i
  set r := i - m * m
  have hsq_le : m * m ≤ i := Nat.sqrt_le i
  have hlt_sq : i < m * m + 2 * m + 1 := by have := Nat.lt_succ_sqrt i; nlinarith
  have hr : r ≤ 2 * m := by omega
  by_cases hm_gt : n + 3 ≤ m
  · have := Hblk_bounds (show 2 ≤ m by omega) hr
    omega
  · have hm_eq : m = n + 2 := by
      have h1 : (n + 2) * (n + 2) ≤ i := by zify [h7] at hn hi ⊢; nlinarith
      have h2 : n + 2 ≤ m := Nat.le_sqrt.mpr h1
      omega
    have hr_ge : 2 * m - 6 ≤ r := by
      have hm6 : 6 ≤ 2 * m := by omega
      have hsq_eq : m * m = (n + 2) * (n + 2) := by rw [hm_eq]
      have hi_lo : (n + 2) * (n + 2) + (2 * m - 6) ≤ i := by
        zify [h7, hm6] at hn hi hm_eq ⊢; nlinarith
      omega
    unfold Hblk
    split_ifs with h1 h2 h3 h4
    · omega
    · have : (r + 1) % 4 ≠ 0 := by omega
      omega
    · have : (r + 2) % 4 ≠ 3 := by omega
      omega
    · omega
    · omega

private lemma half_lt_of_lt {n i : ℕ} (hn : 2 ≤ n) (hi : i < (n - 1) ^ 2 + 2) : half i < n := by
  by_cases hi4 : i < 4
  · interval_cases i
    · rw [half_small.1]; omega
    · rw [half_small.2.1]; omega
    · rw [half_small.2.2.1]; omega
    · rw [half_small.2.2.2.1]
      by_cases hn2 : n = 2
      · subst hn2; norm_num at hi
      · omega
  · rw [half_eq_Hblk i (by omega)]
    set m := Nat.sqrt i
    set r := i - m * m
    have hsq_le : m * m ≤ i := Nat.sqrt_le i
    have hlt_sq : i < m * m + 2 * m + 1 := by have := Nat.lt_succ_sqrt i; nlinarith
    have hr : r ≤ 2 * m := by omega
    have hm2 : 2 ≤ m := Nat.le_sqrt.mpr (by omega)
    by_cases hm_lt : m ≤ n - 2
    · have := Hblk_bounds hm2 hr
      omega
    · have hn1 : 1 ≤ n := by omega
      have hlt : i < n * n := by zify [hn1] at hn hi ⊢; nlinarith
      have hm_lt_n : m < n := Nat.sqrt_lt'.mpr (by simpa [sq] using hlt)
      have hm_eq : m = n - 1 := by omega
      have hsq_eq : m * m = (n - 1) ^ 2 := by rw [hm_eq, sq]
      have hr2 : r < 2 := by omega
      have hm2 : 2 ≤ m := Nat.le_sqrt.mpr (by omega)
      unfold Hblk
      split_ifs with h1 h2 h3 h4
      · omega
      · have : (r + 1) % 4 ≤ 2 := by omega
        omega
      · have : 2 ≤ (r + 2) % 4 := by omega
        omega
      · omega
      · omega

private lemma half_at_min {n : ℕ} (hn : 2 ≤ n) : half ((n - 1) ^ 2 + 2) = n := by
  by_cases hn2 : n = 2
  · subst hn2; exact half_small.2.2.2.1
  · have hn1 : 1 ≤ n := by omega
    have hn3 : 3 ≤ n := by omega
    have hi4 : 4 ≤ (n - 1) ^ 2 + 2 := by zify [hn1] at hn3 ⊢; nlinarith
    rw [half_eq_Hblk _ hi4]
    have hsq : Nat.sqrt ((n - 1) ^ 2 + 2) = n - 1 :=
      sqrt_unique (r := 2) (by ring) (by omega)
    have hsub : (n - 1) ^ 2 + 2 - (n - 1) * (n - 1) = 2 := by rw [sq]; omega
    rw [hsq, hsub]
    unfold Hblk
    split_ifs <;> omega

private lemma half_at_max {n : ℕ} (hn : 2 ≤ n) : half ((n + 3) ^ 2 - 8) = n := by
  have h8 : 8 ≤ (n + 3) ^ 2 := by nlinarith
  have hi4 : 4 ≤ (n + 3) ^ 2 - 8 := by zify [h8] at hn ⊢; nlinarith
  rw [half_eq_Hblk _ hi4]
  have h2n3 : 3 ≤ 2 * n := by omega
  have heq_sq : (n + 3) ^ 2 - 8 = (n + 2) * (n + 2) + (2 * n - 3) := by
    zify [h8, h2n3]; ring
  have hsq : Nat.sqrt ((n + 3) ^ 2 - 8) = n + 2 :=
    sqrt_unique (r := 2 * n - 3) heq_sq (by omega)
  have hsub : (n + 3) ^ 2 - 8 - (n + 2) * (n + 2) = 2 * n - 3 := by rw [heq_sq]; omega
  rw [hsq, hsub]
  unfold Hblk
  have hlt : 2 * n - 3 < 2 * (n + 2) - 3 := by omega
  have hne : 2 * n - 3 ≠ 2 * (n + 2) - 3 := by omega
  simp only [hne, hlt, ↓reduceIte]
  split_ifs with hmod
  · have : (2 * n - 3 + 1) % 4 = 0 := by omega
    omega
  · have : (2 * n - 3 + 2) % 4 = 3 := by omega
    omega

private lemma block_count_eq (m d : ℕ) (hm : 2 ≤ m) (hd : d ≤ 3) :
    ((Finset.range (2 * m + 1)).filter (fun r => Hblk m r = m + d - 2)).card =
      if d = 0 then (m - 2) / 2
      else if d = 1 then m / 2 + 2
      else if d = 2 then (m + 1) / 2
      else (m + 1) / 2 := by
  -- Induction on m by steps of 2! Base cases m = 2, 3 by decide!
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hm4 : m < 4
    · interval_cases m <;> interval_cases d <;> decide +kernel
    · have hih := ih (m - 2) (by omega) (by omega)
      -- Compare range (2*m + 1) vs range (2*(m-2) + 1): split off the 4 elements
      -- r ∈ {2m-7, 2m-6, 2m-5, 2m-4} inside [0, 2m-4) and shift the last 4 elements [2m-3, 2m]!
      -- Specifically:
      --   for r < 2m - 7: Hblk m r = Hblk (m-2) r + 2
      --   for r ∈ [2m-7, 2m-4]: 4 consecutive elements of the sawtooth -> each d ∈ {0,1,2,3} hits ONCE!
      --   for r ∈ [2m-3, 2m]: Hblk m r = Hblk (m-2) (r - 4) + 2!
      have hsplit : ∀ k : ℕ, 4 ≤ k →
          ((Finset.range (2 * k + 1)).filter (fun r => Hblk k r = k + d - 2)).card =
            ((Finset.range (2 * (k - 2) - 3)).filter (fun r => Hblk k r = k + d - 2)).card +
            ((Finset.Ico (2 * (k - 2) - 3) (2 * k - 3)).filter (fun r => Hblk k r = k + d - 2)).card +
            ((Finset.Ico (2 * k - 3) (2 * k + 1)).filter (fun r => Hblk k r = k + d - 2)).card := by
        intro k hk
        have h1 : Finset.range (2 * k + 1) =
            Finset.range (2 * (k - 2) - 3) ∪
            Finset.Ico (2 * (k - 2) - 3) (2 * k - 3) ∪
            Finset.Ico (2 * k - 3) (2 * k + 1) := by
          ext r; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
        rw [h1, Finset.filter_union, Finset.filter_union, Finset.card_union_of_disjoint,
          Finset.card_union_of_disjoint]
        · rw [Finset.disjoint_left]; intro r ha hb
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at ha hb; omega
        · rw [Finset.disjoint_left]; intro r ha hb
          simp only [Finset.mem_filter, Finset.mem_union, Finset.mem_range, Finset.mem_Ico] at ha hb; omega
      have hsplit2 : ((Finset.range (2 * (m - 2) + 1)).filter (fun r => Hblk (m - 2) r = (m - 2) + d - 2)).card =
          ((Finset.range (2 * (m - 2) - 3)).filter (fun r => Hblk (m - 2) r = (m - 2) + d - 2)).card +
          ((Finset.Ico (2 * (m - 2) - 3) (2 * (m - 2) + 1)).filter
            (fun r => Hblk (m - 2) r = (m - 2) + d - 2)).card := by
        have h1 : Finset.range (2 * (m - 2) + 1) =
            Finset.range (2 * (m - 2) - 3) ∪ Finset.Ico (2 * (m - 2) - 3) (2 * (m - 2) + 1) := by
          ext r; simp only [Finset.mem_union, Finset.mem_range, Finset.mem_Ico]; omega
        rw [h1, Finset.filter_union, Finset.card_union_of_disjoint]
        rw [Finset.disjoint_left]; intro r ha hb
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at ha hb; omega
      have hpart1 : ((Finset.range (2 * (m - 2) - 3)).filter (fun r => Hblk m r = m + d - 2)).card =
          ((Finset.range (2 * (m - 2) - 3)).filter (fun r => Hblk (m - 2) r = (m - 2) + d - 2)).card := by
        congr 1; ext r
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor <;> rintro ⟨hr, heq⟩ <;> refine ⟨hr, ?_⟩ <;>
          (unfold Hblk at heq ⊢;
           have hpar : (m - 2) % 2 = m % 2 := by omega
           simp only [hpar, show r ≠ 2 * m - 3 by omega, show r < 2 * m - 3 by omega,
             show r ≠ 2 * (m - 2) - 3 by omega, show r < 2 * (m - 2) - 3 by omega, ↓reduceIte] at heq ⊢;
           split_ifs at heq ⊢ <;> omega)
      have hpart3 : ((Finset.Ico (2 * m - 3) (2 * m + 1)).filter (fun r => Hblk m r = m + d - 2)).card =
          ((Finset.Ico (2 * (m - 2) - 3) (2 * (m - 2) + 1)).filter
            (fun r => Hblk (m - 2) r = (m - 2) + d - 2)).card := by
        refine Finset.card_bij (fun r _ => r - 4) ?_ ?_ ?_
        · intro r hr
          simp only [Finset.mem_filter, Finset.mem_Ico] at hr ⊢
          refine ⟨by omega, ?_⟩
          have heq := hr.2
          unfold Hblk at heq ⊢
          have hpar : (m - 2) % 2 = m % 2 := by omega
          by_cases h0 : r = 2 * m - 3
          · simp only [h0, show 2 * m - 3 - 4 = 2 * (m - 2) - 3 by omega, ↓reduceIte] at heq ⊢; omega
          · simp only [hpar, h0, show ¬ r < 2 * m - 3 by omega,
              show r - 4 ≠ 2 * (m - 2) - 3 by omega, show ¬ r - 4 < 2 * (m - 2) - 3 by omega,
              ↓reduceIte] at heq ⊢
            split_ifs at heq ⊢ <;> omega
        · intro r₁ hr₁ r₂ hr₂ heq
          simp only [Finset.mem_filter, Finset.mem_Ico] at hr₁ hr₂; omega
        · intro r hr
          simp only [Finset.mem_filter, Finset.mem_Ico] at hr
          refine ⟨r + 4, ?_, by omega⟩
          simp only [Finset.mem_filter, Finset.mem_Ico]
          refine ⟨by omega, ?_⟩
          have heq := hr.2
          unfold Hblk at heq ⊢
          have hpar : (m - 2) % 2 = m % 2 := by omega
          by_cases h0 : r = 2 * (m - 2) - 3
          · simp only [h0, show 2 * (m - 2) - 3 + 4 = 2 * m - 3 by omega, ↓reduceIte] at heq ⊢; omega
          · simp only [hpar, h0, show ¬ r < 2 * (m - 2) - 3 by omega,
              show r + 4 ≠ 2 * m - 3 by omega, show ¬ r + 4 < 2 * m - 3 by omega,
              ↓reduceIte] at heq ⊢
            split_ifs at heq ⊢ <;> omega
      have hpart2 : ((Finset.Ico (2 * (m - 2) - 3) (2 * m - 3)).filter
          (fun r => Hblk m r = m + d - 2)).card = 1 := by
        rw [Finset.card_eq_one]
        have hmem_iff : ∀ r, r ∈ (Finset.Ico (2 * (m - 2) - 3) (2 * m - 3)).filter
            (fun r => Hblk m r = m + d - 2) ↔
            (2 * m - 7 ≤ r ∧ r < 2 * m - 3) ∧
            (if m % 2 = 1 then m - 2 + (r + 1) % 4 else m + 1 - (r + 2) % 4) = m + d - 2 := by
          intro r
          simp only [Finset.mem_filter, Finset.mem_Ico]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩
            refine ⟨⟨by omega, h2⟩, ?_⟩
            unfold Hblk at h3
            simp only [show r ≠ 2 * m - 3 by omega, h2, ↓reduceIte] at h3
            exact h3
          · rintro ⟨⟨h1, h2⟩, h3⟩
            refine ⟨⟨by omega, h2⟩, ?_⟩
            unfold Hblk
            simp only [show r ≠ 2 * m - 3 by omega, h2, ↓reduceIte]
            exact h3
        rcases (show m % 2 = 0 ∨ m % 2 = 1 by omega) with hpar | hpar
        · refine ⟨if d = 0 then 2 * m - 7 else if d = 1 then 2 * m - 4
            else if d = 2 then 2 * m - 5 else 2 * m - 6, ?_⟩
          ext r
          rw [hmem_iff, Finset.mem_singleton]
          simp only [hpar, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
          split_ifs <;> omega
        · refine ⟨if d = 0 then 2 * m - 7 else if d = 1 then 2 * m - 6
            else if d = 2 then 2 * m - 5 else 2 * m - 4, ?_⟩
          ext r
          rw [hmem_iff, Finset.mem_singleton]
          simp only [hpar, ↓reduceIte]
          split_ifs <;> omega
      rw [hsplit m (by omega), hpart1, hpart2, hpart3]
      rw [hsplit2] at hih
      split_ifs at hih ⊢ <;> omega

private lemma positions_eq_posFinset {n : ℕ} (hn : 2 ≤ n) :
    positions n = (posFinset n : Set ℕ) := by
  ext i
  rw [mem_positions_iff, Finset.mem_coe, posFinset, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro h
    refine ⟨?_, h⟩
    by_contra hge
    have := half_gt_of_ge hn (by omega : (n + 3) ^ 2 - 7 ≤ i)
    omega
  · exact And.right

private lemma posFinset_card {n : ℕ} (hn : 2 ≤ n) : (posFinset n).card = 2 * n + 2 := by
  by_cases hn3 : n = 2
  · subst hn3; decide +kernel
  · -- For n ≥ 3, all elements of posFinset n lie in blocks m ∈ {n-1, n, n+1, n+2}, all ≥ 2!
    have hn1 : 1 ≤ n := by omega
    have hn3' : 3 ≤ n := by omega
    have hdisj : posFinset n =
        ((Finset.range (2 * (n - 1) + 1)).filter (fun r => Hblk (n - 1) r = n)).image
          (fun r => (n - 1) * (n - 1) + r) ∪
        ((Finset.range (2 * n + 1)).filter (fun r => Hblk n r = n)).image
          (fun r => n * n + r) ∪
        ((Finset.range (2 * (n + 1) + 1)).filter (fun r => Hblk (n + 1) r = n)).image
          (fun r => (n + 1) * (n + 1) + r) ∪
        ((Finset.range (2 * (n + 2) + 1)).filter (fun r => Hblk (n + 2) r = n)).image
          (fun r => (n + 2) * (n + 2) + r) := by
      ext i
      simp only [posFinset, Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_image]
      constructor
      · rintro ⟨hlt, hhalf⟩
        have hge4 : 4 ≤ i := by
          by_contra hlt4
          have hsq4 : 4 ≤ (n - 1) ^ 2 := by zify [hn1] at hn3' ⊢; nlinarith
          have := half_lt_of_lt hn (by omega : i < (n - 1) ^ 2 + 2)
          omega
        rw [half_eq_Hblk i hge4] at hhalf
        set m := Nat.sqrt i
        set r := i - m * m
        have hsq_le : m * m ≤ i := Nat.sqrt_le i
        have hlt_sq : i < m * m + 2 * m + 1 := by have := Nat.lt_succ_sqrt i; nlinarith
        have hr : r ≤ 2 * m := by omega
        have hm2 : 2 ≤ m := Nat.le_sqrt.mpr hge4
        rcases Hblk_eq_iff hm2 hr hhalf with hm_eq | hm_eq | hm_eq | hm_eq
        · left; left; left; exact ⟨r, ⟨by omega, hm_eq ▸ hhalf⟩, by rw [← hm_eq]; omega⟩
        · left; left; right; exact ⟨r, ⟨by omega, hm_eq ▸ hhalf⟩, by rw [← hm_eq]; omega⟩
        · left; right; exact ⟨r, ⟨by omega, hm_eq ▸ hhalf⟩, by rw [← hm_eq]; omega⟩
        · right; exact ⟨r, ⟨by omega, hm_eq ▸ hhalf⟩, by rw [← hm_eq]; omega⟩
      · rintro (((⟨r, ⟨hr, hH⟩, rfl⟩ | ⟨r, ⟨hr, hH⟩, rfl⟩) | ⟨r, ⟨hr, hH⟩, rfl⟩) | ⟨r, ⟨hr, hH⟩, rfl⟩)
        · have hge4 : 4 ≤ (n - 1) * (n - 1) + r := by zify [hn1] at hn3' ⊢; nlinarith
          refine ⟨by zify [hn1] at hn3' hr ⊢; nlinarith, ?_⟩
          rw [half_eq_Hblk _ hge4, sqrt_unique rfl (by omega), Nat.add_sub_cancel_left]
          exact hH
        · have hge4 : 4 ≤ n * n + r := by nlinarith
          refine ⟨by nlinarith, ?_⟩
          rw [half_eq_Hblk _ hge4, sqrt_unique rfl (by omega), Nat.add_sub_cancel_left]
          exact hH
        · have hge4 : 4 ≤ (n + 1) * (n + 1) + r := by nlinarith
          refine ⟨by nlinarith, ?_⟩
          rw [half_eq_Hblk _ hge4, sqrt_unique rfl (by omega), Nat.add_sub_cancel_left]
          exact hH
        · have hge4 : 4 ≤ (n + 2) * (n + 2) + r := by nlinarith
          refine ⟨by nlinarith, ?_⟩
          rw [half_eq_Hblk _ hge4, sqrt_unique rfl (by omega), Nat.add_sub_cancel_left]
          exact hH
    rw [hdisj, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint,
      Finset.card_union_of_disjoint]
    · rw [Finset.card_image_of_injective _ (fun _ _ h => by omega),
        Finset.card_image_of_injective _ (fun _ _ h => by omega),
        Finset.card_image_of_injective _ (fun _ _ h => by omega),
        Finset.card_image_of_injective _ (fun _ _ h => by omega)]
      have c0 := block_count_eq (n - 1) 3 (by omega) (by decide)
      have c1 := block_count_eq n 2 (by omega) (by decide)
      have c2 := block_count_eq (n + 1) 1 (by omega) (by decide)
      have c3 := block_count_eq (n + 2) 0 (by omega) (by decide)
      rw [show (n - 1) + 3 - 2 = n by omega] at c0
      rw [show n + 2 - 2 = n by omega] at c1
      rw [show (n + 1) + 1 - 2 = n by omega] at c2
      rw [show (n + 2) + 0 - 2 = n by omega] at c3
      simp only [show (3 : ℕ) ≠ 0 by decide, show (3 : ℕ) ≠ 1 by decide,
        show (3 : ℕ) ≠ 2 by decide, show (2 : ℕ) ≠ 0 by decide, show (2 : ℕ) ≠ 1 by decide,
        show (1 : ℕ) ≠ 0 by decide, ↓reduceIte] at c0 c1 c2 c3
      rw [c0, c1, c2, c3]
      omega
    · rw [Finset.disjoint_left]; intro i ha hb
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_range] at ha hb
      rcases ha with ⟨r₁, ⟨h1, _⟩, rfl⟩; rcases hb with ⟨r₂, ⟨h2, _⟩, heq⟩
      have hn1 : 1 ≤ n := by omega
      zify [hn1] at heq h1 h2; nlinarith
    · rw [Finset.disjoint_left]; intro i ha hb
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at ha hb
      rcases hb with ⟨r₂, ⟨h2, _⟩, rfl⟩
      have hn1 : 1 ≤ n := by omega
      rcases ha with ⟨r₁, ⟨h1, _⟩, heq⟩ | ⟨r₁, ⟨h1, _⟩, heq⟩ <;> (zify [hn1] at heq h1 h2; nlinarith)
    · rw [Finset.disjoint_left]; intro i ha hb
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at ha hb
      rcases hb with ⟨r₂, ⟨h2, _⟩, rfl⟩
      have hn1 : 1 ≤ n := by omega
      rcases ha with (⟨r₁, ⟨h1, _⟩, heq⟩ | ⟨r₁, ⟨h1, _⟩, heq⟩) | ⟨r₁, ⟨h1, _⟩, heq⟩ <;>
        (zify [hn1] at heq h1 h2; nlinarith)

private lemma positions_zero : positions 0 = ({0, 1} : Finset ℕ) := by
  ext i
  rw [mem_positions_iff, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    by_cases h9 : i < 9
    · interval_cases i <;> first | (simp; done) | (revert h; decide +kernel)
    · rw [half_eq_Hblk i (by omega)] at h
      set m := Nat.sqrt i
      have hm3 : 3 ≤ m := Nat.le_sqrt.mpr (by omega)
      have hle : m * m ≤ i := Nat.sqrt_le i
      have hlt : i < (m + 1) * (m + 1) := Nat.lt_succ_sqrt i
      have hlt' : i < m * m + 2 * m + 1 := by nlinarith
      have hr : i - m * m ≤ 2 * m := by omega
      have := Hblk_bounds (by omega) hr
      omega
  · rintro (rfl | rfl) <;> decide +kernel

private lemma positions_one : positions 1 = ({2, 4, 5, 8} : Finset ℕ) := by
  ext i
  rw [mem_positions_iff, Finset.mem_coe]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro h
    by_cases h16 : i < 16
    · interval_cases i <;> first | (simp; done) | (revert h; decide +kernel)
    · rw [half_eq_Hblk i (by omega)] at h
      set m := Nat.sqrt i
      have hm4 : 4 ≤ m := Nat.le_sqrt.mpr (by omega)
      have hle : m * m ≤ i := Nat.sqrt_le i
      have hlt : i < (m + 1) * (m + 1) := Nat.lt_succ_sqrt i
      have hlt' : i < m * m + 2 * m + 1 := by nlinarith
      have hr : i - m * m ≤ 2 * m := by omega
      have := Hblk_bounds (by omega) hr
      omega
  · rintro (rfl | rfl | rfl | rfl) <;> decide +kernel

theorem result : type_of% @OMA.S_oeis_a175019.main := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    rcases n with _ | _ | n
    · exact ⟨0, by rw [positions_zero]; simp⟩
    · exact ⟨2, by rw [positions_one]; simp⟩
    · exact ⟨(n + 2 - 1) ^ 2 + 2, (mem_positions_iff _ _).mpr (half_at_min (by omega))⟩
  · intro n
    rcases n with _ | _ | n
    · rw [positions_zero, Set.encard_coe_eq_coe_finsetCard]; decide
    · rw [positions_one, Set.encard_coe_eq_coe_finsetCard]; decide
    · rw [positions_eq_posFinset (by omega), Set.encard_coe_eq_coe_finsetCard,
        posFinset_card (by omega)]
  · intro n
    rcases n with _ | _ | n
    · rw [positions_zero]
      exact ⟨by simp, fun x hx => by simp at hx; omega⟩
    · rw [positions_one]
      exact ⟨by simp, fun x hx => by simp at hx; omega⟩
    · refine ⟨(mem_positions_iff _ _).mpr (half_at_max (by omega)), fun i hi => ?_⟩
      rw [mem_positions_iff] at hi
      by_contra hgt
      have hge : (n + 1 + 1 + 3) ^ 2 - 7 ≤ i := by omega
      have := half_gt_of_ge (n := n + 1 + 1) (by omega) hge
      omega
  · intro n hn
    rcases n with _ | _ | n
    · omega
    · rw [positions_one]
      exact ⟨by simp, fun x hx => by simp at hx; omega⟩
    · refine ⟨(mem_positions_iff _ _).mpr (half_at_min (by omega)), fun i hi => ?_⟩
      rw [mem_positions_iff] at hi
      by_contra hlt
      have hlt' : i < (n + 1 + 1 - 1) ^ 2 + 2 := by omega
      have := half_lt_of_lt (n := n + 1 + 1) (by omega) hlt'
      omega

end OMA.A175019Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a175019.main := OMA.A175019Proof.result
