import OMAStatements.S_oeis_a334509
import Mathlib

namespace OMA.Helpers_a334509
open OMA.S_oeis_a334509

lemma emod_of_eq (n x r q : ℤ) (h0 : 0 ≤ r) (h1 : r < n) (hx : x = r + n * q) : x % n = r := by
  subst hx; rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt h0 h1]

lemma emod_pred (n : ℤ) (hn : 0 < n) (x : ℤ) :
    (x - 1) % n = if x % n = 0 then n - 1 else x % n - 1 := by
  have h0 := Int.emod_nonneg x hn.ne'
  have h1 := Int.emod_lt_of_pos x hn
  have hx := (Int.emod_add_mul_ediv x n).symm
  split_ifs with h
  · exact emod_of_eq n _ _ (x / n - 1) (by omega) (by omega) (by rw [h] at hx; linear_combination hx)
  · exact emod_of_eq n _ _ (x / n) (by omega) (by omega) (by linear_combination hx)

lemma emod_succ (n : ℤ) (hn : 0 < n) (x : ℤ) :
    (x + 1) % n = if x % n = n - 1 then 0 else x % n + 1 := by
  have h0 := Int.emod_nonneg x hn.ne'
  have h1 := Int.emod_lt_of_pos x hn
  have hx := (Int.emod_add_mul_ediv x n).symm
  split_ifs with h
  · exact emod_of_eq n _ _ (x / n + 1) (by omega) (by omega) (by rw [h] at hx; linear_combination hx)
  · exact emod_of_eq n _ _ (x / n) (by omega) (by omega) (by linear_combination hx)

lemma row0 (n : ℕ) (x : ℤ) : row n 0 x ↔ x % n = 0 := by
  show -x % (n:ℤ) = 0 ↔ _
  rw [← Int.dvd_iff_emod_eq_zero, Int.dvd_neg, Int.dvd_iff_emod_eq_zero]

lemma step_char (n : ℕ) (hn : 0 < n) (t : ℕ) (P : ℤ → Prop) (h : ∀ x, row n t x ↔ P (x % n))
    (x : ℤ) : row n (t + 1) x ↔ localRule (P (if x % (n:ℤ) = 0 then (n:ℤ) - 1 else x % n - 1))
      (P (x % n)) (P (if x % (n:ℤ) = (n:ℤ) - 1 then 0 else x % n + 1)) := by
  show localRule (row n t (x - 1)) (row n t x) (row n t (x + 1)) ↔ _
  rw [h, h, h, emod_pred _ (by exact_mod_cast hn), emod_succ _ (by exact_mod_cast hn)]

lemma row1 (n : ℕ) (h7 : 7 ≤ n) (x : ℤ) : row n 1 x ↔ (2 ≤ x % n ∧ x % n ≤ n - 2) := by
  have hn : (0:ℤ) < n := by omega
  rw [step_char n (by omega) 0 (fun r => r = 0) (row0 n) x]
  have h0 := Int.emod_nonneg x hn.ne'
  have h1 := Int.emod_lt_of_pos x hn
  generalize x % (n:ℤ) = r at *
  unfold localRule; split_ifs <;> omega

lemma row2 (n : ℕ) (h7 : 7 ≤ n) (x : ℤ) : row n 2 x ↔ (x % n = 0 ∨ x % n = 2) := by
  have hn : (0:ℤ) < n := by omega
  rw [step_char n (by omega) 1 (fun r => 2 ≤ r ∧ r ≤ n - 2) (row1 n h7) x]
  have h0 := Int.emod_nonneg x hn.ne'
  have h1 := Int.emod_lt_of_pos x hn
  generalize x % (n:ℤ) = r at *
  unfold localRule; split_ifs <;> omega

lemma row3 (n : ℕ) (h7 : 7 ≤ n) (x : ℤ) : row n 3 x ↔ (x % n = 1 ∨ (4 ≤ x % n ∧ x % n ≤ n - 2)) := by
  have hn : (0:ℤ) < n := by omega
  rw [step_char n (by omega) 2 (fun r => r = 0 ∨ r = 2) (row2 n h7) x]
  have h0 := Int.emod_nonneg x hn.ne'
  have h1 := Int.emod_lt_of_pos x hn
  generalize x % (n:ℤ) = r at *
  unfold localRule; split_ifs <;> omega

lemma row4 (n : ℕ) (h7 : 7 ≤ n) (x : ℤ) : row n 4 x ↔ x % n = 4 := by
  have hn : (0:ℤ) < n := by omega
  rw [step_char n (by omega) 3 (fun r => r = 1 ∨ (4 ≤ r ∧ r ≤ n - 2)) (row3 n h7) x]
  have h0 := Int.emod_nonneg x hn.ne'
  have h1 := Int.emod_lt_of_pos x hn
  generalize x % (n:ℤ) = r at *
  unfold localRule; split_ifs <;> omega


lemma shift4 (n : ℕ) (h7 : 7 ≤ n) (t : ℕ) (x : ℤ) : row n (t + 4) x ↔ row n t (x - 4) := by
  induction t generalizing x with
  | zero =>
    rw [row4 n h7, row0, ← Int.dvd_iff_emod_eq_zero]
    constructor
    · intro h
      exact ⟨x / n, by have := Int.emod_add_mul_ediv x n; rw [h] at this; linear_combination -this⟩
    · rintro ⟨k, hk⟩
      exact emod_of_eq n x 4 k (by norm_num) (by omega) (by linear_combination hk)
  | succ t ih =>
    show localRule (row n (t + 4) (x - 1)) (row n (t + 4) x) (row n (t + 4) (x + 1)) ↔
      localRule (row n t (x - 4 - 1)) (row n t (x - 4)) (row n t (x - 4 + 1))
    rw [ih, ih, ih, show x - 1 - 4 = x - 4 - 1 by ring, show x + 1 - 4 = x - 4 + 1 by ring]

lemma shift4k (n : ℕ) (h7 : 7 ≤ n) (t k : ℕ) (x : ℤ) :
    row n (t + 4 * k) x ↔ row n t (x - 4 * k) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [show t + 4 * (k + 1) = (t + 4 * k) + 4 by ring, shift4 n h7, ih]
    push_cast; ring_nf

lemma perx (n : ℕ) (t : ℕ) (k : ℤ) (x : ℤ) : row n t (x + n * k) ↔ row n t x := by
  induction t generalizing x with
  | zero =>
    rw [row0, row0, ← Int.dvd_iff_emod_eq_zero, ← Int.dvd_iff_emod_eq_zero]
    exact dvd_add_left (dvd_mul_right _ _)
  | succ t ih =>
    show localRule (row n t (x + n * k - 1)) (row n t (x + n * k)) (row n t (x + n * k + 1)) ↔
      localRule (row n t (x - 1)) (row n t x) (row n t (x + 1))
    rw [show x + n * k - 1 = (x - 1) + n * k by ring, show x + n * k + 1 = (x + 1) + n * k by ring,
      ih, ih, ih]

lemma lcm_eq (n : ℕ) : n * (4 / Nat.gcd n 4) = Nat.lcm n 4 := by
  rw [Nat.lcm, Nat.mul_div_assoc _ (Nat.gcd_dvd_right n 4)]

lemma big (n : ℕ) (h7 : 7 ≤ n) : a n = n * (4 / Nat.gcd n 4) := by
  rw [lcm_eq]
  obtain ⟨m, hm⟩ : 4 ∣ Nat.lcm n 4 := Nat.dvd_lcm_right n 4
  obtain ⟨j, hj⟩ : n ∣ Nat.lcm n 4 := Nat.dvd_lcm_left n 4
  have hmem : Nat.lcm n 4 ∈ {p : ℕ | 0 < p ∧ EventualPeriod n p} := by
    refine ⟨Nat.lcm_pos (by omega) (by norm_num), 0, fun t _ => ?_⟩
    funext x
    apply propext
    rw [hm, shift4k n h7]
    have hmj : ((4 * m : ℕ) : ℤ) = ((n * j : ℕ) : ℤ) := by rw [← hm, ← hj]
    push_cast at hmj
    rw [hmj, show x - n * j = x + n * (-(j:ℤ)) by ring, perx]
  have hlow : ∀ p ∈ {p : ℕ | 0 < p ∧ EventualPeriod n p}, Nat.lcm n 4 ≤ p := by
    rintro p ⟨hp, T, hT⟩
    have hrow := fun x => congrFun (hT (0 + 4 * T + 4 * (p / 4) * 0) (by omega)) x
    have key : ∀ y : ℤ, row n (p % 4) y ↔ row n 0 (y + 4 * (p / 4 : ℕ)) := by
      intro y
      have := hrow (y + 4 * ((T + p / 4 : ℕ) : ℤ))
      rw [show 0 + 4 * T + 4 * (p / 4) * 0 + p = p % 4 + 4 * (T + p / 4) by omega,
        show 0 + 4 * T + 4 * (p / 4) * 0 = 0 + 4 * T by omega, shift4k n h7, shift4k n h7] at this
      rw [show y + 4 * ((T + p / 4 : ℕ) : ℤ) - 4 * ((T + p / 4 : ℕ) : ℤ) = y by ring] at this
      rw [this]; push_cast; ring_nf
    have hn : (0:ℤ) < n := by omega
    have dv : ∀ z : ℤ, row n 0 z ↔ (n:ℤ) ∣ z := fun z => by rw [row0, Int.dvd_iff_emod_eq_zero]
    have e : ∀ c : ℤ, 0 ≤ c → c < n → c % (n:ℤ) = c := fun c h0 h1 => Int.emod_eq_of_lt h0 h1
    set q : ℕ := p / 4 with hq
    have hlt : p % 4 < 4 := Nat.mod_lt _ (by norm_num)
    interval_cases hr : p % 4
    · have h0 := (key 0).1 ((row0 n 0).2 (by simp))
      rw [dv, zero_add] at h0
      have h0' : n ∣ 4 * q := by exact_mod_cast h0
      have : Nat.lcm n 4 ∣ 4 * q := Nat.lcm_dvd h0' (dvd_mul_right 4 q)
      have := Nat.le_of_dvd (by omega) this
      omega
    · have h2 := (key 2).1 ((row1 n h7 2).2 (by rw [e 2 (by norm_num) (by omega)]; omega))
      have h3 := (key 3).1 ((row1 n h7 3).2 (by rw [e 3 (by norm_num) (by omega)]; omega))
      rw [dv] at h2 h3
      have hd := dvd_sub h3 h2
      ring_nf at hd
      have := Int.le_of_dvd (by norm_num) hd
      omega
    · have h2 := (key 0).1 ((row2 n h7 0).2 (by simp))
      have h3 := (key 2).1 ((row2 n h7 2).2 (by rw [e 2 (by norm_num) (by omega)]; omega))
      rw [dv] at h2 h3
      have hd := dvd_sub h3 h2
      ring_nf at hd
      have := Int.le_of_dvd (by norm_num) hd
      omega
    · have h2 := (key 1).1 ((row3 n h7 1).2 (by rw [e 1 (by norm_num) (by omega)]; omega))
      have h3 := (key 4).1 ((row3 n h7 4).2 (by rw [e 4 (by norm_num) (by omega)]; omega))
      rw [dv] at h2 h3
      have hd := dvd_sub h3 h2
      ring_nf at hd
      have := Int.le_of_dvd (by norm_num) hd
      omega
  have hne : a n = sInf {p : ℕ | 0 < p ∧ EventualPeriod n p} := by simp [a]; omega
  rw [hne]
  exact le_antisymm (Nat.sInf_le hmem) (hlow _ (Nat.sInf_mem ⟨_, hmem⟩))

def ruleB (l c r : Bool) : Bool := (!l && !c && !r) || (!l && c && r) || (l && !c && r)

def stepL (n : ℕ) (s : List Bool) : List Bool :=
  (List.range n).map (fun i => ruleB (s.getD ((i + n - 1) % n) false) (s.getD i false)
    (s.getD ((i + 1) % n) false))

def iterL (n : ℕ) : ℕ → List Bool
  | 0 => (List.range n).map (fun i => decide (i = 0))
  | t + 1 => stepL n (iterL n t)

lemma len (n t : ℕ) : (iterL n t).length = n := by
  cases t <;> simp [iterL, stepL]

lemma ruleB_iff (a b c : Bool) : ruleB a b c = true ↔ localRule (a = true) (b = true) (c = true) := by
  cases a <;> cases b <;> cases c <;> simp [ruleB, localRule]

lemma getD_map_range (n k : ℕ) (f : ℕ → Bool) (hk : k < n) :
    ((List.range n).map f).getD k false = f k := by
  rw [List.getD_eq_getElem _ _ (by simpa using hk)]; simp

lemma sim (n : ℕ) (hn : 0 < n) (t : ℕ) (x : ℤ) :
    row n t x ↔ (iterL n t).getD (x % n).toNat false = true := by
  have hn' : (0:ℤ) < n := by exact_mod_cast hn
  induction t generalizing x with
  | zero =>
    have h0 := Int.emod_nonneg x hn'.ne'
    have h1 := Int.emod_lt_of_pos x hn'
    rw [row0]
    simp only [iterL]
    rw [List.getD_eq_getElem _ _ (by simp; omega)]
    simp only [List.getElem_map, List.getElem_range, decide_eq_true_eq]
    omega
  | succ t ih =>
    show localRule (row n t (x - 1)) (row n t x) (row n t (x + 1)) ↔ _
    simp only [ih]
    simp only [iterL, stepL]
    have h0 := Int.emod_nonneg x hn'.ne'
    have h1 := Int.emod_lt_of_pos x hn'
    rw [getD_map_range _ _ _ (by omega)]
    rw [ruleB_iff, emod_pred _ hn', emod_succ _ hn']
    have e1 : (if x % (n:ℤ) = 0 then (n:ℤ) - 1 else x % n - 1).toNat = ((x % n).toNat + n - 1) % n := by
      split_ifs with h
      · rw [h]; simp only [Int.toNat_zero, zero_add]; rw [Nat.mod_eq_of_lt (by omega)]; omega
      · rw [show (x % n).toNat + n - 1 = ((x % n).toNat - 1) + n by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]; omega
    have e2 : (if x % (n:ℤ) = (n:ℤ) - 1 then 0 else x % n + 1).toNat = ((x % n).toNat + 1) % n := by
      split_ifs with h
      · rw [show (x % n).toNat + 1 = n by omega, Nat.mod_self]; simp
      · rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [e1, e2]

lemma rowEq_of_list (n : ℕ) (hn : 0 < n) (t t' : ℕ) (h : iterL n t = iterL n t') :
    row n t = row n t' := by
  funext x; apply propext; rw [sim n hn, sim n hn, h]

lemma list_of_rowEq (n : ℕ) (hn : 0 < n) (t t' : ℕ) (h : row n t = row n t') :
    iterL n t = iterL n t' := by
  apply List.ext_getElem (by rw [len, len])
  intro i h1 h2
  have := congrFun h (i : ℤ)
  rw [sim n hn, sim n hn] at this
  have hi : i < n := by rw [len] at h1; exact h1
  rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast,
    List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h2] at this
  exact Bool.eq_iff_iff.mpr (Iff.of_eq this)

lemma periodic (n T0 p : ℕ) (hper : iterL n (T0 + p) = iterL n T0) (k j : ℕ) :
    iterL n (T0 + j + p * k) = iterL n (T0 + j) := by
  have h1 : ∀ j, iterL n (T0 + j + p) = iterL n (T0 + j) := by
    intro j
    induction j with
    | zero => simpa using hper
    | succ j ih =>
      rw [show T0 + (j + 1) + p = (T0 + j + p) + 1 by ring]
      show stepL n (iterL n (T0 + j + p)) = stepL n (iterL n (T0 + j))
      rw [ih]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show T0 + j + p * (k + 1) = T0 + (j + p * k) + p by ring, h1, ← add_assoc, ih]

lemma a_small (n T0 p : ℕ) (hn : 0 < n) (hp : 0 < p) (hper : iterL n (T0 + p) = iterL n T0)
    (hmin : ∀ p' < p, 0 < p' → iterL n (T0 + p') ≠ iterL n T0) : a n = p := by
  have hmem : p ∈ {p : ℕ | 0 < p ∧ EventualPeriod n p} := by
    refine ⟨hp, T0, fun t ht => rowEq_of_list n hn _ _ ?_⟩
    obtain ⟨j, rfl⟩ : ∃ j, t = T0 + j := ⟨t - T0, by omega⟩
    simpa using periodic n T0 p hper 1 j
  have hlow : ∀ p' ∈ {p : ℕ | 0 < p ∧ EventualPeriod n p}, p ≤ p' := by
    rintro p' ⟨hp', T, hT⟩
    by_contra hlt
    have := list_of_rowEq n hn _ _ (hT (T0 + 0 + p * T) (by nlinarith))
    rw [periodic n T0 p hper T 0, show T0 + 0 + p * T + p' = T0 + p' + p * T by ring,
      periodic n T0 p hper T p'] at this
    exact hmin p' (by omega) hp' (by simpa using this)
  have hne : a n = sInf {p : ℕ | 0 < p ∧ EventualPeriod n p} := by simp [a]; omega
  rw [hne]
  exact le_antisymm (Nat.sInf_le hmem) (hlow _ (Nat.sInf_mem ⟨_, hmem⟩))

lemma a1 : a 1 = 2 := a_small 1 0 2 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
lemma a2 : a 2 = 2 := a_small 2 0 2 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
lemma a3 : a 3 = 2 := a_small 3 1 2 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
lemma a4 : a 4 = 2 := a_small 4 0 2 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
lemma a5 : a 5 = 15 := a_small 5 0 15 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)
lemma a6 : a 6 = 2 := a_small 6 4 2 (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

end OMA.Helpers_a334509

open OMA.S_oeis_a334509 OMA.Helpers_a334509 in
theorem OMA.solution : type_of% @OMA.S_oeis_a334509.main := by
  have hrec : ∀ n : ℕ, 14 < n → (a n : ℤ) = 2 * (a (n - 4) : ℤ) - (a (n - 8) : ℤ) := by
    intro n hn
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
    rw [show k + 8 - 4 = k + 4 by omega, show k + 8 - 8 = k by omega,
      big _ (by omega), big _ (by omega), big _ (by omega),
      show k + 8 = (k + 4) + 4 by ring, Nat.gcd_add_self_left, Nat.gcd_add_self_left]
    push_cast; ring
  refine ⟨fun n hn => big n hn, hrec, ?_⟩
  intro X
  have hD : ((1:PowerSeries ℤ) - X) ^ 2 * (1 + X) ^ 2 * (1 + X ^ 2) ^ 2 = 1 - 2 * X ^ 4 + X ^ 8 := by ring
  rw [hD, show PowerSeries.mk (fun n => (a n : ℤ)) * (1 - 2 * X ^ 4 + X ^ 8) =
    PowerSeries.mk (fun n => (a n : ℤ)) - PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 4 -
      PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 4 + PowerSeries.mk (fun n => (a n : ℤ)) * X ^ 8 by ring]
  ext d
  simp only [X, map_add, map_sub, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]
  rcases (show d ≤ 14 ∨ 14 < d by omega) with hd | hd
  · have v0 : a 0 = 0 := by simp [a]
    have v7 : a 7 = 28 := by rw [big _ (by norm_num)]; norm_num
    have v8 : a 8 = 8 := by rw [big _ (by norm_num)]; norm_num
    have v9 : a 9 = 36 := by rw [big _ (by norm_num)]; norm_num
    have v10 : a 10 = 20 := by rw [big _ (by norm_num)]; norm_num
    have v11 : a 11 = 44 := by rw [big _ (by norm_num)]; norm_num
    have v12 : a 12 = 12 := by rw [big _ (by norm_num)]; norm_num
    have v13 : a 13 = 52 := by rw [big _ (by norm_num)]; norm_num
    have v14 : a 14 = 28 := by rw [big _ (by norm_num)]; norm_num
    interval_cases d <;> simp [numeratorCoeffs, v0, a1, a2, a3, a4, a5, a6, v7, v8, v9, v10, v11, v12,
      v13, v14]
  · rw [if_pos (by omega), if_pos (by omega), hrec d hd,
      List.getD_eq_default _ _ (by simp [numeratorCoeffs]; omega)]
    ring
