import OMAStatements.S_oeis_a009101
import Mathlib

/-!
OEIS A009101: iterating f(x) = x + (product of the digits of x) always reaches a fixed point.

Suppose the orbit of n never reaches a fixed point. Since f(x) ≥ x, the orbit is then strictly
increasing, so it is unbounded. Let D = n + 23, so that n < 10^D, and look at the first time the
orbit reaches 10^D: x < 10^D ≤ y = f(x). The digit product of x is at most 9^D, and
9^D < 10^(D-1) because D ≥ 22. Hence 10^D ≤ y < 10^D + 10^(D-1), so the digit of y in position
D - 1 is 0, the digit product of y is 0, and y is a fixed point after all.
-/

namespace OMA.A009101

open OMA.S_oeis_a009101

lemma prod_le (l : List ℕ) (h : ∀ d ∈ l, d ≤ 9) : l.prod ≤ 9 ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, List.length_cons, pow_succ]
    have ha := h a (List.mem_cons_self ..)
    have hl := ih (fun d hd => h d (List.mem_cons_of_mem _ hd))
    calc a * l.prod ≤ 9 * 9 ^ l.length := Nat.mul_le_mul ha hl
      _ = 9 ^ l.length * 9 := Nat.mul_comm _ _

lemma digitProd_le (x D : ℕ) (hx : x < 10 ^ D) : digitProd x ≤ 9 ^ D := by
  unfold digitProd
  split_ifs with h
  · exact Nat.zero_le _
  · have hlen : (Nat.digits 10 x).length ≤ D := by
      rw [Nat.length_digits 10 x (by norm_num) h]
      have := Nat.log_lt_of_lt_pow h hx
      omega
    have hle : (Nat.digits 10 x).prod ≤ 9 ^ (Nat.digits 10 x).length := by
      apply prod_le
      intro d hd
      have := Nat.digits_lt_base (by norm_num : 1 < 10) hd
      omega
    exact hle.trans (Nat.pow_le_pow_right (by norm_num) hlen)

lemma zero_digit (y e : ℕ) (h1 : 10 ^ (e + 1) ≤ y) (h2 : y < 10 ^ (e + 1) + 10 ^ e) :
    digitProd y = 0 := by
  unfold digitProd
  have hpos : 0 < 10 ^ (e + 1) := by positivity
  have hy : y ≠ 0 := by omega
  rw [if_neg hy]
  apply List.prod_eq_zero
  have hdig : (Nat.digits 10 y).getD e 0 = y / 10 ^ e % 10 := Nat.getD_digits y e (by norm_num)
  have hval : y / 10 ^ e = 10 := by
    rw [pow_succ] at h1 h2
    apply Nat.div_eq_of_lt_le
    · omega
    · omega
  have hlen : e < (Nat.digits 10 y).length := by
    by_contra hle
    push_neg at hle
    have hlt := Nat.lt_base_pow_length_digits (b := 10) (m := y) (by norm_num)
    have hmono : 10 ^ (Nat.digits 10 y).length ≤ 10 ^ (e + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hmem : (Nat.digits 10 y).getD e 0 ∈ Nat.digits 10 y := by
    rw [List.getD_eq_getElem _ _ hlen]
    exact List.getElem_mem _
  rw [hdig, hval] at hmem
  simpa using hmem

lemma nine_lt (m : ℕ) (hm : 22 ≤ m) : 9 ^ (m + 1) < 10 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    rw [pow_succ 9 (m + 1), pow_succ 10 m]
    omega

end OMA.A009101

open OMA.S_oeis_a009101 OMA.A009101 in
theorem OMA.solution : type_of% @OMA.S_oeis_a009101.main := by
  intro n
  by_contra hcon
  push_neg at hcon
  have hstep : ∀ x, step x = x + digitProd x := fun x => rfl
  have hgrow : ∀ k, n + k ≤ step^[k] n := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h2 := hcon k
      rw [hstep] at h2 ⊢
      omega
  have hn : n < 10 ^ (n + 23) := by
    have h1 : n < 10 ^ n := Nat.lt_pow_self (by norm_num)
    have h2 : 10 ^ n ≤ 10 ^ (n + 23) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hex : ∃ k, 10 ^ (n + 23) ≤ step^[k] n :=
    ⟨10 ^ (n + 23), (Nat.le_add_left _ _).trans (hgrow _)⟩
  classical
  have hk := Nat.find_spec hex
  have hmin : ∀ m, m < Nat.find hex → ¬ 10 ^ (n + 23) ≤ step^[m] n :=
    fun m hm => Nat.find_min hex hm
  generalize Nat.find hex = k at hk hmin
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp only [Function.iterate_zero, id_eq] at hk
    omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hjlt : step^[j] n < 10 ^ (n + 23) := by
    have := hmin j (by omega)
    omega
  have hy : step^[j + 1] n = step^[j] n + digitProd (step^[j] n) := by
    rw [Function.iterate_succ_apply', hstep]
  have hprod := digitProd_le _ (n + 23) hjlt
  have h9 := nine_lt (n + 22) (by omega)
  have hfix : digitProd (step^[j + 1] n) = 0 := by
    apply zero_digit _ (n + 22)
    · exact hk
    · rw [hy]
      have e1 : 10 ^ (n + 23) = 10 * 10 ^ (n + 22) := by ring
      have e2 : 9 ^ (n + 23) = 9 * 9 ^ (n + 22) := by ring
      have e3 : 10 ^ (n + 22 + 1) = 10 * 10 ^ (n + 22) := by ring
      have e4 : 9 ^ (n + 22 + 1) = 9 * 9 ^ (n + 22) := by ring
      rw [e3]
      rw [e4] at h9
      rw [e1] at hjlt
      rw [e2] at hprod
      omega
  apply hcon (j + 1)
  rw [hstep, hfix]
  rfl
