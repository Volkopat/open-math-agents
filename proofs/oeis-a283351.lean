import OMAStatements.S_oeis_a283351
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace OMA.A283351

open OMA.S_oeis_a283351 PowerSeries

private abbrev p (t : ℕ) (x y : ℤ) := cell 619 t x y

private theorem step (t : ℕ) (x y : ℤ) : p (t + 1) x y =
    Nat.testBit 619 ((p t x y).toNat + 2 * ((p t (x + 1) y).toNat +
      (p t (x - 1) y).toNat + (p t x (y + 1)).toNat + (p t x (y - 1)).toNat)) := rfl

private theorem x_symm (t : ℕ) (x y : ℤ) : p t (-x) y = p t x y := by
  induction t generalizing x y with
  | zero => simp [p, cell]
  | succ t ih =>
    rw [step, step]
    rw [show -x + 1 = -(x - 1) by omega, show -x - 1 = -(x + 1) by omega]
    simp only [ih]
    congr 2
    omega

private theorem y_symm (t : ℕ) (x y : ℤ) : p t x (-y) = p t x y := by
  induction t generalizing x y with
  | zero => simp [p, cell]
  | succ t ih =>
    rw [step, step]
    rw [show -y + 1 = -(y - 1) by omega, show -y - 1 = -(y + 1) by omega]
    simp only [ih]
    congr 2
    omega

private theorem abs_step (x : ℤ) (e : ℤ) (he : |e| ≤ 1) : |x| ≤ |x + e| + 1 := by
  have h := abs_sub_le (x + e) 0 e
  simp only [sub_zero, zero_sub, abs_neg, add_sub_cancel_right] at h
  omega

private theorem exterior (t : ℕ) (ht : 1 ≤ t) (x y : ℤ)
    (h : (t : ℤ) < |x| + |y|) : p t x y = true := by
  induction t generalizing x y with
  | zero => omega
  | succ t ih =>
    by_cases ht0 : t = 0
    · subst t
      have miss (u v : ℤ) (hu : |x| ≤ |u| + 1) (hv : |y| ≤ |v| + 1)
          (hnear : u = x ∨ v = y) : ¬ (u = 0 ∧ v = 0) := by
        rintro ⟨rfl, rfl⟩
        simp only [abs_zero] at hu hv
        rcases hnear with hx | hy
        · simp [← hx] at h
          omega
        · simp [← hy] at h
          omega
      have hx₁ : |x| ≤ |x + 1| + 1 := abs_step x 1 (by decide)
      have hx₂ : |x| ≤ |x - 1| + 1 := abs_step x (-1) (by decide)
      have hy₁ : |y| ≤ |y + 1| + 1 := abs_step y 1 (by decide)
      have hy₂ : |y| ≤ |y - 1| + 1 := abs_step y (-1) (by decide)
      simp [p, cell, miss x y (by omega) (by omega) (Or.inl rfl),
        miss (x + 1) y hx₁ (by omega) (Or.inr rfl),
        miss (x - 1) y hx₂ (by omega) (Or.inr rfl),
        miss x (y + 1) (by omega) hy₁ (Or.inl rfl),
        miss x (y - 1) (by omega) hy₂ (Or.inl rfl)]
    · have ht' : 1 ≤ t := by omega
      have hx₁ : |x| ≤ |x + 1| + 1 := abs_step x 1 (by decide)
      have hx₂ : |x| ≤ |x - 1| + 1 := abs_step x (-1) (by decide)
      have hy₁ : |y| ≤ |y + 1| + 1 := abs_step y 1 (by decide)
      have hy₂ : |y| ≤ |y - 1| + 1 := abs_step y (-1) (by decide)
      rw [step]
      rw [ih ht' x y (by omega), ih ht' (x + 1) y (by omega),
        ih ht' (x - 1) y (by omega), ih ht' x (y + 1) (by omega), ih ht' x (y - 1) (by omega)]
      decide

private theorem update_axis (t : ℕ) (x : ℤ) : p (t + 1) x 0 =
    Nat.testBit 619 ((p t x 0).toNat + 2 * ((p t (x + 1) 0).toNat +
      (p t (x - 1) 0).toNat + (p t x 1).toNat + (p t x 1).toNat)) := by
  rw [step]
  simp only [zero_add, zero_sub]
  rw [y_symm t x 1]

private def axis (t : ℕ) (x : ℤ) : Bool :=
  decide (x ≠ (t : ℤ) ∧ (t % 2 = 1 ∨ x ≠ (t : ℤ) - 1))

private theorem pattern (t : ℕ) (ht : 2 ≤ t) :
    (∀ x : ℤ, 0 ≤ x → p t x 0 = axis t x) ∧
    p t ((t : ℤ) - 1) 1 = decide (t % 2 = 0) ∧
    p t ((t : ℤ) - 2) 1 = decide (t % 2 = 1) := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases small : t = 1
    · subst t
      refine ⟨?_, by decide, by decide⟩
      intro x hx
      by_cases xx : 2 < x
      · rw [exterior 2 (by omega) x 0 (by simpa [abs_of_nonneg hx] using xx)]
        simp [axis, show x ≠ 2 by omega, show x ≠ 1 by omega]
      · have cases : x = 0 ∨ x = 1 ∨ x = 2 := by omega
        rcases cases with h | h | h <;> subst x <;> decide
    · obtain ⟨main, edge, near⟩ := ih (by omega)
      have ext (x y : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hhh : (t : ℤ) < x + y) : p t x y = true :=
        exterior t (by omega) x y (by simpa only [abs_of_nonneg hx, abs_of_nonneg hy] using hhh)
      have e0 : t % 2 = 0 ∨ t % 2 = 1 := by omega
      have ea : (t + 1) % 2 = 1 ↔ t % 2 = 0 := by omega
      have eb : (t + 1) % 2 = 0 ↔ t % 2 = 1 := by omega
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        by_cases outside : (t : ℤ) + 1 < x
        · rw [exterior (t+1) (by omega) x 0 (by simp [abs_of_nonneg hx]; omega)]
          simp [axis, show x ≠ (t : ℤ) + 1 by omega, show x ≠ (t : ℤ) by omega]
        rw [update_axis, main _ hx, main _ (by omega)]
        have left : p t (x - 1) 0 = axis t |x - 1| := by
          by_cases h : 1 ≤ x
          · rw [abs_of_nonneg (by omega), main _ (by omega)]
          · have hzero : x = 0 := by omega
            simpa [hzero] using (x_symm t 1 0).trans (main 1 (by omega))
        rw [left]
        have hcases : x = (t : ℤ) + 1 ∨ x = (t : ℤ) ∨ x = (t : ℤ) - 1 ∨ x = (t : ℤ) - 2 ∨ x < (t : ℤ) - 2 := by omega
        rcases hcases with h | h | h | h | h
        · rw [h, ext _ 1 (by omega) (by omega) (by omega)]
          simp [axis, show (t : ℤ) + 1 - 1 = t by omega,
            show (t : ℤ) + 1 + 1 ≠ t by omega, show (t : ℤ) + 1 + 1 ≠ (t : ℤ) - 1 by omega,
            show (t : ℤ) + 1 ≠ (t : ℤ) - 1 by omega]
          decide
        · rw [h, ext _ 1 (by omega) (by omega) (by omega)]
          rcases e0 with e | e <;>
            simp [axis, e, ea, abs_of_nonneg (show 0 ≤ (t : ℤ) - 1 by omega),
              show (t : ℤ) + 1 ≠ t by omega, show (t : ℤ) + 1 ≠ (t : ℤ) - 1 by omega] <;> decide
        · rw [h, edge]
          rcases e0 with e | e <;>
            simp [axis, e, ea, abs_of_nonneg (show 0 ≤ (t : ℤ) - 1 - 1 by omega),
              show (t : ℤ) - 1 + 1 = t by omega, show (t : ℤ) - 1 - 1 ≠ t by omega,
              show (t : ℤ) - 1 - 1 ≠ (t : ℤ) - 1 by omega, show (t : ℤ) - 1 ≠ (t : ℤ) + 1 by omega] <;> decide
        · rw [h, near]
          by_cases tz : t = 2
          · subst t
            decide
          · rcases e0 with e | e <;>
              simp [axis, e, ea, abs_of_nonneg (show 0 ≤ (t : ℤ) - 2 - 1 by omega),
                show (t : ℤ) - 2 + 1 = (t : ℤ) - 1 by omega,
                show (t : ℤ) - 2 - 1 ≠ (t : ℤ) - 1 by omega, show (t : ℤ) - 2 - 1 ≠ t by omega,
                show (t : ℤ) - 2 ≠ (t : ℤ) + 1 by omega] <;> decide
        · have l₁ : |x - 1| ≠ (t : ℤ) := by
            by_cases h' : 1 ≤ x
            · rw [abs_of_nonneg (by omega)]; omega
            · rw [abs_of_nonpos (by omega)]; omega
          have l₂ : |x - 1| ≠ (t : ℤ) - 1 := by
            by_cases h' : 1 ≤ x
            · rw [abs_of_nonneg (by omega)]; omega
            · rw [abs_of_nonpos (by omega)]; omega
          cases p t x 1 <;> simp [axis, l₁, l₂,
            show x ≠ (t : ℤ) by omega, show x ≠ (t : ℤ) - 1 by omega,
            show x + 1 ≠ (t : ℤ) by omega, show x + 1 ≠ (t : ℤ) - 1 by omega,
            show x ≠ (t : ℤ) + 1 by omega] <;> decide
      · rw [show (↑(t+1) : ℤ) - 1 = t by omega]
        rw [step, ext t 1 (by omega) (by omega) (by omega), ext ((t : ℤ) + 1) 1 (by omega) (by omega) (by omega), edge,
          ext t (1+1) (by omega) (by omega) (by omega), show (1:ℤ)-1=0 by decide, main _ (by omega)]
        rcases e0 with e | e <;> simp [axis, e, eb] <;> decide
      · rw [show (↑(t+1) : ℤ) - 2 = (t : ℤ) - 1 by omega]
        rw [step, edge, show (t : ℤ) - 1 + 1 = t by omega, ext t 1 (by omega) (by omega) (by omega),
          show (t : ℤ) - 1 - 1 = (t : ℤ) - 2 by omega, near,
          ext ((t : ℤ)-1) (1+1) (by omega) (by omega) (by omega), show (1:ℤ)-1=0 by decide, main _ (by omega)]
        rcases e0 with e | e <;> simp [axis, e, ea] <;> decide

private theorem repunit (n : ℕ) (hn : 2 ≤ n) :
    (a n : ℚ) = ((10 : ℚ) ^ (if n % 2 = 0 then n - 1 else n) - 1) / 9 := by
  let m := if n % 2 = 0 then n - 1 else n
  have hm : m ≤ n + 1 := by dsimp [m]; split <;> omega
  have hsum : a n = ∑ k ∈ Finset.range m, (10 : ℤ) ^ k := by
    unfold a
    let F : ℕ → ℤ := fun k => if cell 619 n ((k : ℤ) - n) 0 then (10 : ℤ) ^ (n - k) else 0
    change ∑ k ∈ Finset.range (n + 1), F k = _
    rw [← Finset.sum_range_reflect F (n + 1)]
    calc
      _ = ∑ k ∈ Finset.range (n + 1), if k < m then (10 : ℤ) ^ k else 0 := by
        apply Finset.sum_congr rfl
        intro k hk
        have hkn : k ≤ n := by simpa using Finset.mem_range.mp hk
        have eq : ((n - k : ℕ) : ℤ) - (n : ℤ) = -(k : ℤ) := by omega
        have sub : n - (n - k) = k := by omega
        dsimp [F]
        rw [eq, sub, show cell 619 n (-(k : ℤ)) 0 = p n k 0 from x_symm _ _ _, (pattern n hn).1 _ (by omega)]
        have eqcond : ((k : ℤ) ≠ (n : ℤ) ∧ (n % 2 = 1 ∨ (k : ℤ) ≠ (n : ℤ) - 1)) ↔ k < m := by
          dsimp [m]
          split <;> omega
        simp only [axis, decide_eq_true_eq, eqcond]
      _ = _ := by
        rw [← Finset.sum_filter]
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        omega
  rw [hsum, Int.cast_sum]
  push_cast
  have h := geom_sum_mul (10 : ℚ) m
  linarith

private theorem closed (n : ℕ) (hn : 1 ≤ n) :
    (a n : ℚ) = (-20 - 9 * (-10 : ℚ) ^ n + 11 * (10 : ℚ) ^ n) / 180 := by
  by_cases small : n = 1
  · subst n
    have ha : a 1 = 1 := by decide
    norm_num [ha]
  · rw [repunit n (by omega)]
    by_cases even : n % 2 = 0
    · have e : Even n := ⟨n / 2, by omega⟩
      rw [if_pos even, e.neg_pow]
      have h : (10 : ℚ) ^ n = (10 : ℚ) ^ (n - 1) * 10 := by
        rw [← pow_succ, show n - 1 + 1 = n by omega]
      rw [h]
      ring
    · have o : Odd n := ⟨n / 2, by omega⟩
      rw [if_neg even, o.neg_pow]
      ring

private theorem recurrence (n : ℕ) (hn : 4 ≤ n) :
    (a n : ℚ) = a (n - 1) + 100 * a (n - 2) - 100 * a (n - 3) := by
  rw [closed n (by omega), closed (n-1) (by omega), closed (n-2) (by omega), closed (n-3) (by omega)]
  have h₀ : n = (n - 3) + 3 := by omega
  have h₁ : n - 1 = (n - 3) + 2 := by omega
  have h₂ : n - 2 = (n - 3) + 1 := by omega
  have power (x : ℚ) : x ^ n = x ^ (n - 3) * x ^ 3 ∧
      x ^ (n - 1) = x ^ (n - 3) * x ^ 2 ∧ x ^ (n - 2) = x ^ (n - 3) * x :=
    ⟨by rw [← pow_add, ← h₀], by rw [← pow_add, ← h₁], by rw [← pow_succ, ← h₂]⟩
  obtain ⟨p₀,p₁,p₂⟩ := power 10
  obtain ⟨m₀,m₁,m₂⟩ := power (-10)
  rw [p₀,p₁,p₂,m₀,m₁,m₂]
  ring

private theorem series :
    PowerSeries.mk (fun n => (a n : ℚ)) *
      ((1 - PowerSeries.X) * (1 - 10 * PowerSeries.X) * (1 + 10 * PowerSeries.X) : PowerSeries ℚ) =
      1 - 100 * PowerSeries.X ^ 2 + 110 * PowerSeries.X ^ 3 := by
  let A : PowerSeries ℚ := mk (fun n => (a n : ℚ))
  change A * _ = _
  have expand : A * ((1-X)*(1-10*X)*(1+10*X)) = A - A*X - 100*(A*X^2) + 100*(A*X^3) := by ring
  rw [expand]
  ext n
  have mulC (c : ℚ) (P : PowerSeries ℚ) : coeff n (C c * P) = c * coeff n P := coeff_C_mul _ _ _
  have c100 : (100 : PowerSeries ℚ) = C (100 : ℚ) := by exact (map_ofNat C 100).symm
  have c110 : (110 : PowerSeries ℚ) = C (110 : ℚ) := by exact (map_ofNat C 110).symm
  have shift (d : ℕ) : coeff n (A * X ^ d) = if d ≤ n then (a (n - d) : ℚ) else 0 := by
    rw [coeff_mul_X_pow']
    split <;> simp [A]
  have ax : coeff n (A * X) = if 1 ≤ n then (a (n - 1) : ℚ) else 0 := by simpa using shift 1
  simp only [map_add, map_sub, c100, c110, mulC, ax, shift, coeff_X_pow, coeff_one, A, coeff_mk]
  by_cases h : 4 ≤ n
  · simp [show n ≠ 0 by omega, show n ≠ 2 by omega, show n ≠ 3 by omega,
      show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega]
    linarith [recurrence n h]
  · have h0 : a 0 = 1 := by decide
    have h1 : a 1 = 1 := by decide
    have h2 : a 2 = 1 := by decide
    have h3 : a 3 = 111 := by decide
    interval_cases n <;> norm_num [h0,h1,h2,h3]

end OMA.A283351

theorem OMA.solution : type_of% @OMA.S_oeis_a283351.main :=
  ⟨OMA.A283351.series, OMA.A283351.closed, OMA.A283351.recurrence⟩
