import OMAStatements.S_oeis_a269657
import Mathlib

open OMA.S_oeis_a269657


open PowerSeries

theorem rep_iff (w : Fin 4 → ℕ) : repeated w ↔ (w 0 = w 2 ∧ w 1 = w 3 ∧ w 1 = w 0 + 1) := by
  constructor
  · rintro ⟨i, j, hij, h1, h2, h3⟩
    fin_cases i <;> fin_cases j <;> simp_all <;> omega
  · rintro ⟨h1, h2, h3⟩
    exact ⟨0, 2, by decide, h1, h2, h3⟩

def gg (n : ℕ) (x : Fin n) : Fin 4 → Fin (n + 1) := ![x.castSucc, x.succ, x.castSucc, x.succ]

theorem gg_inj (n : ℕ) : Function.Injective (gg n) := by
  intro x y h
  have := congrFun h 0
  simpa [gg] using this

theorem bad_eq (n : ℕ) :
    (Finset.univ.filter fun v : Fin 4 → Fin (n + 1) => repeated (fun i => (v i : ℕ))) =
      Finset.univ.map ⟨gg n, gg_inj n⟩ := by
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
    Function.Embedding.coeFn_mk, rep_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hv1 := (v 1).isLt
    refine ⟨⟨v 0, by omega⟩, ?_⟩
    funext i
    fin_cases i <;> apply Fin.ext <;> simp [gg] <;> omega
  · rintro ⟨x, rfl⟩
    simp [gg]

theorem a_eq (n : ℕ) : a n = (n + 1) ^ 4 - n := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin 4 → Fin (n + 1))))
    (p := fun v : Fin 4 → Fin (n + 1) => repeated (fun i => (v i : ℕ)))
  rw [bad_eq, Finset.card_map, Finset.card_univ, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at h
  unfold a
  omega

theorem a_z (n : ℕ) : (a n : ℤ) = ((n : ℤ) + 1) ^ 4 - n := by
  rw [a_eq]
  have : n ≤ (n + 1) ^ 4 := by
    calc n ≤ n + 1 := Nat.le_succ n
      _ = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ (n + 1) ^ 4 := Nat.pow_le_pow_right (by omega) (by norm_num)
  push_cast [this]
  ring

theorem recur (n : ℕ) (hn : 4 < n) :
    (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  simp only [show m + 5 - 1 = m + 4 by omega, show m + 5 - 2 = m + 3 by omega,
    show m + 5 - 3 = m + 2 by omega, show m + 5 - 4 = m + 1 by omega, show m + 5 - 5 = m by omega,
    a_z]
  push_cast
  ring

theorem gf : mk (fun n => (a n : ℤ)) * (1 - X) ^ 5 =
      (1 + 10 * X + 14 * X ^ 2 - 2 * X ^ 3 + X ^ 4 : PowerSeries ℤ) := by
  set F : PowerSeries ℤ := mk (fun n => (a n : ℤ)) with hF
  have product : F * (1 - X) ^ 5 = F + (-5 : ℤ) • (F * X ^ 1) + (10 : ℤ) • (F * X ^ 2) +
      (-10 : ℤ) • (F * X ^ 3) + (5 : ℤ) • (F * X ^ 4) + (-1 : ℤ) • (F * X ^ 5) := by
    simp only [zsmul_eq_mul]; push_cast; ring
  have rhs : (1 + 10 * X + 14 * X ^ 2 - 2 * X ^ 3 + X ^ 4 : PowerSeries ℤ) =
      (1 : ℤ) • X ^ 0 + (10 : ℤ) • X ^ 1 + (14 : ℤ) • X ^ 2 + (-2 : ℤ) • X ^ 3 +
        (1 : ℤ) • X ^ 4 := by
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [product, rhs]
  ext n
  simp only [map_add, map_zsmul, coeff_mul_X_pow', hF, coeff_mk, coeff_X_pow, smul_eq_mul]
  by_cases h : 4 < n
  · have hr := recur n h
    simp only [show 1 ≤ n by omega, show 2 ≤ n by omega, show 3 ≤ n by omega,
      show 4 ≤ n by omega, show 5 ≤ n by omega, show n ≠ 0 by omega, show n ≠ 1 by omega,
      show n ≠ 2 by omega, show n ≠ 3 by omega, show n ≠ 4 by omega, if_true, if_false]
    linarith
  · interval_cases n <;> simp [a_z] <;> norm_num

theorem OMA.solution : type_of% @OMA.S_oeis_a269657.main :=
  ⟨gf, fun n hn => recur n (by omega)⟩
