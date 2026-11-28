import OMAReductions.R_Erdos686_erdos_686_R1_H2_R1

private abbrev pellBase (n : ℕ) : 1 < 2 * n + 3 := by omega

private theorem discriminant (n : ℕ) :
    (2 * n + 3) * (2 * n + 3) - 1 = 4 * (n + 1) * (n + 2) := by
  have : (2 * n + 3) * (2 * n + 3) = 4 * (n + 1) * (n + 2) + 1 := by ring
  omega

-- The two entries track consecutive second coordinates of Pell solutions.
private theorem orbit (n j : ℕ) :
    (fun z : ℤ × ℤ => (2 * (2 * (n : ℤ) + 3) * z.1 - z.2, z.1))^[j] (1, 0) =
      (Pell.yz (pellBase n) (j + 1), Pell.yz (pellBase n) j) := by
  induction j with
  | zero => simp [Pell.yz]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, Pell.yz_succ_succ]
    push_cast
    rfl

private theorem xOdd (n k : ℕ) : Pell.xn (pellBase n) k % 2 = 1 := by
  induction k using Nat.twoStepInduction with
  | zero => rw [Pell.xn_zero]
  | one => rw [Pell.xn_one]; omega
  | more k h₀ _ =>
    have h := Pell.xn_succ_succ (pellBase n) k
    rw [mul_assoc] at h
    omega

private theorem indexPositive {n j : ℕ} (ha : 2 ≤ Pell.yn (pellBase n) (j + 1)) :
    1 ≤ j := by
  cases j with
  | zero => rw [Pell.yn_one] at ha; omega
  | succ => omega

theorem OMA.solution : OMA.R_Erdos686_erdos_686_R1_H2_R1.H1 := by
  intro a ha
  constructor
  · rintro ⟨n, m, _, h⟩
    have he : (2 * m + 3) * (2 * m + 3) = 1 + 4 * (n + 1) * (n + 2) * a * a := by
      nlinarith only [h]
    obtain ⟨k, _, hy⟩ := Pell.eq_pell (pellBase n) (x := 2 * m + 3) (y := a)
      (show (2 * m + 3) * (2 * m + 3) - ((2 * n + 3) * (2 * n + 3) - 1) * a * a = 1 by
        rw [discriminant]; omega)
    cases k with
    | zero => simp at hy; omega
    | succ j =>
      have hj := indexPositive (n := n) (j := j) (hy ▸ ha)
      have htwo : Pell.yn (pellBase n) 2 = 2 * (2 * n + 3) := by
        simpa only [Nat.zero_add, Pell.yn_zero, Pell.yn_one, add_zero, mul_one]
          using Pell.yn_succ_succ (pellBase n) 0
      have hmono := (Pell.strictMono_y (pellBase n)).monotone (show 2 ≤ j + 1 by omega)
      have hindex := Pell.yn_ge_n (pellBase n) (j + 1)
      refine ⟨n, by omega, j, by omega, ?_⟩
      rw [orbit]
      change (Pell.yn (pellBase n) (j + 1) : ℤ) = (a : ℤ)
      exact_mod_cast hy.symm
  · rintro ⟨n, _, j, _, h⟩
    rw [orbit] at h
    change (Pell.yn (pellBase n) (j + 1) : ℤ) = (a : ℤ) at h
    have hy : Pell.yn (pellBase n) (j + 1) = a := by exact_mod_cast h
    have hj := indexPositive (n := n) (j := j) (hy.symm ▸ ha)
    let x := Pell.xn (pellBase n) (j + 1)
    have htwo : Pell.xn (pellBase n) 2 + 1 = 2 * (2 * n + 3) * (2 * n + 3) := by
      simpa only [Nat.zero_add, Pell.xn_zero, Pell.xn_one] using Pell.xn_succ_succ (pellBase n) 0
    have hx₂ : Pell.xn (pellBase n) 2 ≤ x :=
      (Pell.strictMono_x (pellBase n)).monotone (show 2 ≤ j + 1 by omega)
    have hxlo : 2 * n + 7 ≤ x := by nlinarith only [htwo, hx₂, Nat.zero_le n, Nat.zero_le (n * n)]
    have hodd : x % 2 = 1 := xOdd n (j + 1)
    let m := (x - 3) / 2
    have hm : 2 * m + 3 = x := by dsimp [m]; omega
    have hp : x * x - ((2 * n + 3) * (2 * n + 3) - 1) *
        Pell.yn (pellBase n) (j + 1) * Pell.yn (pellBase n) (j + 1) = 1 :=
      Pell.pell_eq (pellBase n) (j + 1)
    rw [discriminant, hy, ← hm] at hp
    have he : (2 * m + 3) * (2 * m + 3) = 1 + 4 * (n + 1) * (n + 2) * a * a := by omega
    exact ⟨n, m, by omega, by nlinarith only [he]⟩
