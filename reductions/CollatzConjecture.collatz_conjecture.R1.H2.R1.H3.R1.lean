import OMAReductions.R_CollatzConjecture_collatz_conjecture_R1_H2_R1
import Mathlib

/-! Integer product and prefix relations for a finite Collatz parity word. -/

namespace OMA.CollatzParityWord

open Finset
open scoped BigOperators

theorem zero_counts (b : ℕ → Bool) :
    ((range 0).filter fun i => b i).card = 0 ∧
      ((range 0).filter fun i => ¬b i).card = 0 := by simp

theorem succ_counts (b : ℕ → Bool) (i : ℕ) :
    ((range (i + 1)).filter fun j => b j).card =
      ((range i).filter fun j => b j).card + (if b i then 1 else 0) ∧
    ((range (i + 1)).filter fun j => ¬b j).card =
      ((range i).filter fun j => ¬b j).card + (if b i then 0 else 1) := by
  cases h : b i <;> simp [Finset.range_add_one, Finset.filter_insert, h]

private theorem count_product (b : ℕ → Bool) (k a d : ℕ) :
    (∏ i ∈ range k, if b i then a else d) =
      a ^ ((range k).filter fun i => b i).card *
        d ^ ((range k).filter fun i => ¬b i).card := by
  classical
  rw [← Finset.prod_filter_mul_prod_filter_not (range k) (fun i => b i = true)
    (fun i => if b i then a else d)]
  congr 1
  · calc
      _ = ∏ _i ∈ (range k).filter (fun i => b i = true), a := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [(Finset.mem_filter.mp hi).2]
      _ = _ := by simp
  · calc
      _ = ∏ _i ∈ (range k).filter (fun i => ¬b i = true), d := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [(Finset.mem_filter.mp hi).2]
      _ = _ := by simp

/-- The full numerator and denominator encode every affine prefix. -/
theorem prefix_relation (x : ℕ → ℕ) (b : ℕ → Bool)
    (o e c : ℕ → ℕ) (k : ℕ) (h₀ : o 0 = 0 ∧ e 0 = 0 ∧ c 0 = 0)
    (hcount : ∀ i < k, o (i + 1) = o i + (if b i then 1 else 0) ∧
      e (i + 1) = e i + (if b i then 0 else 1) ∧
      c (i + 1) = if b i then 3 * c i + 2 ^ e i else c i)
    (hstep : ∀ i < k, (if b i then 1 else 2) * x (i + 1) =
      if b i then 3 * x i + 1 else x i) :
    ∀ i ≤ k, 2 ^ e i * x i = 3 ^ o i * x 0 + c i := by
  intro i hi
  induction i with
  | zero => simp [h₀.1, h₀.2.1, h₀.2.2]
  | succ i ih =>
    have hlt : i < k := by omega
    obtain ⟨ho, he, hc⟩ := hcount i hlt
    have hr := hstep i hlt
    have hold := ih (by omega)
    cases hb : b i
    · simp only [hb, Bool.false_eq_true, ↓reduceIte, add_zero] at ho he hc hr
      calc
        2 ^ e (i + 1) * x (i + 1) = 2 ^ e i * (2 * x (i + 1)) := by rw [he, pow_succ, mul_assoc]
        _ = 3 ^ o i * x 0 + c i := by rw [hr, hold]
        _ = 3 ^ o (i + 1) * x 0 + c (i + 1) := by rw [ho, hc]
    · simp only [hb, ↓reduceIte, add_zero, one_mul] at ho he hc hr
      calc
        2 ^ e (i + 1) * x (i + 1) = 3 * (2 ^ e i * x i) + 2 ^ e i := by
          rw [he, hr]
          ring
        _ = 3 ^ o (i + 1) * x 0 + c (i + 1) := by
          rw [hold, ho, hc, pow_succ]
          ring

/-- Integer corridor for the counts of even and odd transitions in a cycle
whose every state is at least the positive lower bound B. -/
theorem cycle_corridor (x : ℕ → ℕ) (b : ℕ → Bool) {k B : ℕ} (hk : 0 < k) (hB : 0 < B)
    (hx : ∀ i < k, B ≤ x i)
    (hb : b 0 = true) (hcycle : x k = x 0)
    (hstep : ∀ i < k, (if b i then 1 else 2) * x (i + 1) =
      if b i then 3 * x i + 1 else x i) :
    let o := ((range k).filter fun i => b i).card
    let e := ((range k).filter fun i => ¬b i).card
    0 < o ∧ (3 : ℕ) ^ o < 2 ^ e ∧ B ^ o * 2 ^ e ≤ (3 * B + 1) ^ o := by
  classical
  let o := ((range k).filter fun i => b i).card
  let e := ((range k).filter fun i => ¬b i).card
  let P := ∏ i ∈ range k, x i
  let W (i : ℕ) := if b i then 3 * x i + 1 else x i
  have hinit : 0 ∈ (range k).filter (fun i => b i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hb⟩
  have ho : 0 < o := Finset.card_pos.mpr ⟨0, hinit⟩
  have hP : 0 < P := Finset.prod_pos (fun i hi => by
    have := hx i (Finset.mem_range.mp hi)
    omega)
  have hshift : (∏ i ∈ range k, x (i + 1)) = P := by
    have hA : x 0 * (∏ i ∈ range k, x (i + 1)) = ∏ i ∈ range (k + 1), x i := by
      simpa only [mul_comm] using (Finset.prod_range_succ' x k).symm
    have hB : (∏ i ∈ range (k + 1), x i) = x 0 * P := by
      rw [Finset.prod_range_succ, hcycle]
      exact mul_comm _ _
    have ht := hA.trans hB
    exact Nat.eq_of_mul_eq_mul_left (by have := hx 0 hk; omega) ht
  have hprod : (∏ i ∈ range k, W i) = 2 ^ e * P := by
    calc
      _ = ∏ i ∈ range k, (if b i then 1 else 2) * x (i + 1) := by
        exact Finset.prod_congr rfl (fun i hi => (hstep i (Finset.mem_range.mp hi)).symm)
      _ = _ := by rw [Finset.prod_mul_distrib, count_product, one_pow, one_mul, hshift]
  have hlower :
      (∏ i ∈ range k, (if b i then 3 else 1) * x i) < ∏ i ∈ range k, W i := by
    apply Finset.prod_lt_prod
    · intro i hi
      have hx' := hx i (Finset.mem_range.mp hi)
      split <;> simp <;> omega
    · intro i hi
      cases h : b i <;> simp [W, h]
    · refine ⟨0, Finset.mem_range.mpr hk, ?_⟩
      simp [W, hb]
  rw [Finset.prod_mul_distrib, count_product, one_pow, mul_one, hprod] at hlower
  have hlo : 3 ^ o < 2 ^ e := Nat.lt_of_mul_lt_mul_right hlower
  have hupper :
      (∏ i ∈ range k, (if b i then B else 1) * W i) ≤
        ∏ i ∈ range k, (if b i then 3 * B + 1 else 1) * x i := by
    apply Finset.prod_le_prod'
    intro i hi
    have hx' := hx i (Finset.mem_range.mp hi)
    cases h : b i
    · simp [W, h]
    · simp only [W, h, ↓reduceIte]
      calc
        B * (3 * x i + 1) = 3 * B * x i + B := by ring
        _ ≤ 3 * B * x i + x i := Nat.add_le_add_left hx' _
        _ = (3 * B + 1) * x i := by ring
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, count_product, count_product] at hupper
  simp only [one_pow, mul_one] at hupper
  rw [hprod, ← mul_assoc] at hupper
  exact ⟨ho, hlo, Nat.le_of_mul_le_mul_right hupper hP⟩

end OMA.CollatzParityWord

open CollatzConjecture
open OMA.CollatzParityWord

namespace OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R1

/-- There are no powers in the required corridor with at most forty odd transitions. -/
def H1 : Prop :=
  ∀ o e : ℕ, 0 < o → o < 41 → (3 : ℕ) ^ o < 2 ^ e →
    (3001 : ℕ) ^ o < 1000 ^ o * 2 ^ e

/-- The residual obstruction is purely arithmetic. Each prefix has a
well-defined positive integer value with the required parity, and the final
prefix must return to the initial value. -/
def H2 : Prop :=
  ∀ (n k : ℕ) (b : ℕ → Bool) (o e c : ℕ → ℕ), 1000 ≤ n → n % 4 = 3 → 0 < k →
    41 ≤ o k → o 0 = 0 → e 0 = 0 → c 0 = 0 →
    (∀ i < k, o (i + 1) = o i + (if b i then 1 else 0) ∧
      e (i + 1) = e i + (if b i then 0 else 1) ∧
      c (i + 1) = if b i then 3 * c i + 2 ^ e i else c i) →
    (∀ i ≤ k, let z := 3 ^ o i * n + c i
      2 ^ e i ∣ z ∧ n ≤ z / 2 ^ e i) →
    (∀ i < k, b i = decide (((3 ^ o i * n + c i) / 2 ^ e i) % 2 = 1)) →
    (3 : ℕ) ^ o k < 2 ^ e k → n ^ o k * 2 ^ e k ≤ (3 * n + 1) ^ o k →
    2 ^ e k * n = 3 ^ o k * n + c k → False

theorem main : H1 → H2 → OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1.H3 := by
  intro hshort hlong n k hn hmod hk hcycle
  by_contra! hmin
  let x (i : ℕ) := collatzStep^[i] n
  let b (i : ℕ) : Bool := decide (x i % 2 = 1)
  let o (i : ℕ) := ((Finset.range i).filter fun j => b j).card
  let e (i : ℕ) := ((Finset.range i).filter fun j => ¬b j).card
  let c (i : ℕ) : ℕ := Nat.rec (motive := fun _ => ℕ) 0 (fun j cj => if b j then 3 * cj + 2 ^ e j else cj) i
  have hb0 : b 0 = true := by
    change decide (n % 2 = 1) = true
    simp only [decide_eq_true_eq]
    omega
  have hcount (i : ℕ) (_hi : i < k) :
      o (i + 1) = o i + (if b i then 1 else 0) ∧
        e (i + 1) = e i + (if b i then 0 else 1) ∧
        c (i + 1) = if b i then 3 * c i + 2 ^ e i else c i := by
    have h := succ_counts b i
    exact ⟨h.1, h.2, rfl⟩
  have hstep (i : ℕ) (_hi : i < k) :
      (if b i then 1 else 2) * x (i + 1) = if b i then 3 * x i + 1 else x i := by
    have hnext : x (i + 1) = collatzStep (x i) := by
      exact Function.iterate_succ_apply' collatzStep i n
    by_cases h : Even (x i)
    · have hb : b i = false := decide_eq_false_iff_not.mpr (by
        have he := Nat.even_iff.mp h
        omega)
      rw [hnext, collatzStep, if_pos h, hb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      have he := Nat.even_iff.mp h
      omega
    · have hb : b i = true := decide_eq_true_eq.mpr (by
        have ho := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp h)
        exact ho)
      simp only [hnext, collatzStep, if_neg h, hb, ↓reduceIte, one_mul]
  have h0 : o 0 = 0 ∧ e 0 = 0 ∧ c 0 = 0 := by
    exact ⟨(zero_counts b).1, (zero_counts b).2, rfl⟩
  have hX (i : ℕ) (_hi : i < k) : 1000 ≤ x i := hn.trans (hmin i)
  obtain ⟨hopos, hlow, hupp⟩ := cycle_corridor x b hk (by decide : 0 < 1000) hX hb0 hcycle hstep
  have hExactBound := (cycle_corridor x b hk (by omega : 0 < n)
    (fun i _ => hmin i) hb0 hcycle hstep).2.2
  have hlongCount : 41 ≤ o k := by
    by_contra! hsmall
    exact not_lt_of_ge hupp (hshort (o k) (e k) hopos hsmall hlow)
  have hPrefix (i : ℕ) (hi : i ≤ k) :
      2 ^ e i * x i = 3 ^ o i * n + c i := prefix_relation x b o e c k h0 hcount hstep i hi
  have hQuot (i : ℕ) (hi : i ≤ k) : (3 ^ o i * n + c i) / 2 ^ e i = x i := by
    rw [← hPrefix i hi, Nat.mul_div_cancel_left _ (pow_pos (by decide : 0 < (2 : ℕ)) _)]
  have hInt (i : ℕ) (hi : i ≤ k) : let z := 3 ^ o i * n + c i
      2 ^ e i ∣ z ∧ n ≤ z / 2 ^ e i := by
    dsimp only
    refine ⟨⟨x i, (hPrefix i hi).symm⟩, ?_⟩
    rw [hQuot i hi]
    exact hmin i
  have hParity (i : ℕ) (hi : i < k) : b i = decide (((3 ^ o i * n + c i) / 2 ^ e i) % 2 = 1) := by
    rw [hQuot i hi.le]
  have hReturn := hPrefix k le_rfl
  rw [show x k = n from hcycle] at hReturn
  exact hlong n k b o e c hn hmod hk hlongCount h0.1 h0.2.1 h0.2.2 hcount hInt hParity hlow hExactBound hReturn

end OMA.R_CollatzConjecture_collatz_conjecture_R1_H2_R1_H3_R1
