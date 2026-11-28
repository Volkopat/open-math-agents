import OMAStatements.S_oeis_a068132
import Mathlib.Data.Nat.Factorization.PrimePow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

-- Credit: @jatin6
-- Schoenfield recorded the two exceptional targets and examples through
-- target index 18 in 2010: https://oeis.org/A068133
open OMA.S_oeis_a068132

private theorem twiceTri (n : ℕ) : tri n * 2 = n * (n + 1) :=
  Nat.div_mul_cancel (Nat.two_dvd_mul_add_one n)

private theorem triShift (n a : ℕ) :
    tri (n + 2 * a) = tri n + a * (2 * n + 1 + a * 2) := by
  have h := twiceTri (n + 2 * a)
  nlinarith [twiceTri n]

private theorem blockSum (x y k : ℕ) (hy : 0 < y) (hk : (Nat.digits 10 x).length ≤ k) :
    digitSum (x + 10 ^ k * y) = digitSum x + digitSum y := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  unfold digitSum
  rw [← Nat.digits_append_zeroes_append_digits (by decide : 1 < 10) hy]
  simp

private theorem ltTenPow (k : ℕ) : k < 10 ^ k := by
  induction k with
  | zero => decide
  | succ k ih => rw [pow_succ]; omega

-- Preserve a second digit sum so that the same construction can be iterated.
private def Good (t n : ℕ) : Prop :=
  digitSum (tri n) = tri t ∧ digitSum (2 * n + 1) = 2 * t + 1

private theorem extend (t n B : ℕ) (h : Good t n) :
    ∃ m : ℕ, B < tri m ∧ Good (t + 2) m := by
  let k := B + (Nat.digits 10 (tri n)).length + (Nat.digits 10 (2 * n + 1)).length
  have ht : (Nat.digits 10 (tri n)).length ≤ k := by dsimp [k]; omega
  have hd : (Nat.digits 10 (2 * n + 1)).length ≤ k := by dsimp [k]; omega
  have hb : B < 10 ^ k := by have := ltTenPow k; dsimp [k] at *; omega
  let a := 10 ^ k
  have hp : 0 < a := by dsimp [a]; positivity
  have ht' := triShift n a
  refine ⟨n + 2 * a, ?_, ?_, ?_⟩
  · have hle : a ≤ a * (2 * n + 1 + a * 2) :=
      Nat.le_mul_of_pos_right _ (by omega)
    change B < a at hb
    omega
  · rw [ht', blockSum _ _ k (by omega) ht, blockSum _ 2 k (by decide) hd, h.1, h.2]
    have two : digitSum 2 = 2 := by decide
    rw [two, show t + 2 = t + 2 * 1 by omega, triShift]
    omega
  · rw [show 2 * (n + 2 * a) + 1 = (2 * n + 1) + 10 ^ k * 4 by dsimp [a]; ring,
        blockSum _ 4 k (by decide) hd, h.2]
    have four : digitSum 4 = 4 := by decide
    omega

private theorem seed (t : ℕ) : ∃ n, Good t n := by
  induction t using Nat.twoStepInduction with
  | zero => exact ⟨0, by decide, by decide⟩
  | one => exact ⟨1, by decide, by decide⟩
  | more t ih _ =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨m, _, hm⟩ := extend t n 0 hn
    exact ⟨m, hm⟩

theorem OMA.A068132.allTargetsFromTwo (t B : ℕ) (ht : 2 ≤ t) :
    ∃ n : ℕ, B < tri n ∧ digitSum (tri n) = tri t := by
  obtain ⟨n, h⟩ := seed (t - 2)
  obtain ⟨m, hm, hgood⟩ := extend _ n B h
  exact ⟨m, hm, (Nat.sub_add_cancel ht) ▸ hgood.1⟩

private theorem ofDigitsZero (ds : List ℕ) (h : ds.sum = 0) :
    Nat.ofDigits 10 ds = 0 := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.sum_cons] at h
    simp [Nat.ofDigits, show d = 0 by omega, ih (by omega)]

private theorem ofDigitsOne (ds : List ℕ) (h : ds.sum = 1) :
    ∃ e : ℕ, Nat.ofDigits 10 ds = 10 ^ e := by
  induction ds with
  | nil => simp at h
  | cons d ds ih =>
    simp only [List.sum_cons] at h
    by_cases hd : d = 0
    · obtain ⟨e, he⟩ := ih (by omega)
      exact ⟨e + 1, by simp [Nat.ofDigits, hd, he, pow_succ']⟩
    · exact ⟨0, by simp [Nat.ofDigits, show d = 1 by omega, ofDigitsZero ds (by omega)]⟩

private theorem splitPowerBound (e : ℕ) : 2 * 2 ^ (e + 2) + 1 < 5 ^ (e + 2) := by
  induction e with
  | zero => decide
  | succ e ih =>
    rw [show e + 1 + 2 = (e + 2) + 1 by omega, pow_succ 2 (e + 2), pow_succ 5 (e + 2)]
    omega

private theorem smallTriangularPower (n e : ℕ) (h : tri n = 10 ^ e) : e ≤ 1 := by
  by_contra! hlarge
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 2 ≤ e)
  let k := j + 2
  change tri n = 10 ^ k at h
  have prod : n * (n + 1) = 5 ^ k * (2 * 2 ^ k) := by
    rw [← twiceTri, h, show (10 : ℕ) = 5 * 2 by decide, mul_pow]
    ring
  have hk : k ≠ 0 := by dsimp [k]; omega
  have hdiv : 5 ^ k ∣ n * (n + 1) := ⟨_, prod⟩
  have hc : n.Coprime (n + 1) := by simp
  have pp : IsPrimePow (5 ^ k) :=
    (isPrimePow_nat_iff _).mpr ⟨5, k, by decide, by omega, rfl⟩
  have hn : 0 < n := by
    by_contra! hzero
    have : n = 0 := by omega
    simp [this] at prod
  have bound : 5 ^ k ≤ n + 1 := by
    rcases (hc.isPrimePow_dvd_mul pp).mp hdiv with ha | ha
    · exact (Nat.le_of_dvd hn ha).trans (by omega)
    · exact Nat.le_of_dvd (by omega) ha
  have gap := splitPowerBound j
  change 2 * 2 ^ k + 1 < 5 ^ k at gap
  have strict := Nat.mul_lt_mul_of_pos_left (show 2 * 2 ^ k < n by omega)
    (show 0 < 5 ^ k by positivity)
  have weak := Nat.mul_le_mul_left n bound
  nlinarith

theorem OMA.A068132.digitSumOne (n : ℕ) (h : digitSum (tri n) = 1) :
    tri n = 1 ∨ tri n = 10 := by
  obtain ⟨e, he⟩ := ofDigitsOne (Nat.digits 10 (tri n)) h
  rw [Nat.ofDigits_digits] at he
  have le := smallTriangularPower n e he
  rcases (show e = 0 ∨ e = 1 by omega) with rfl | rfl <;> simp_all

theorem OMA.A068132.classification (t : ℕ) :
    (∀ B : ℕ, ∃ n : ℕ, B < tri n ∧ digitSum (tri n) = tri t) ↔ 2 ≤ t := by
  constructor
  · intro h
    obtain ⟨n, hlarge, hs⟩ := h 10
    by_contra! hsmall
    rcases (show t = 0 ∨ t = 1 by omega) with rfl | rfl
    · have hz := ofDigitsZero (Nat.digits 10 (tri n)) (show digitSum (tri n) = 0 from hs)
      rw [Nat.ofDigits_digits] at hz
      omega
    · rcases OMA.A068132.digitSumOne n hs with h | h <;> omega
  · intro ht B
    exact OMA.A068132.allTargetsFromTwo t B ht

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a068132.main) := by
  intro h
  have impossible := (OMA.A068132.classification 1).mp (h 1)
  omega
