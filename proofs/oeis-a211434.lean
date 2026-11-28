import OMAStatements.S_oeis_a211434
import Mathlib

/-!
# A211434: triples (w,x,y) in {-n,...,n}^3 with w + 2x + 5y = 0

Write S(n) for {-n, ..., n}. For w and x in S(n), the equation w + 2x + 5y = 0 has a solution
y exactly when 5 divides w + 2x, and then y = -(w + 2x)/5 lies in S(n) because |w + 2x| ≤ 3n.
So a(n) = f(n), the number of pairs (w, x) in S(n)^2 with 5 dividing w + 2x.

Any five consecutive integers contain exactly one x with 5 | w + 2x (w fixed), and exactly one w
with 5 | w + 2x (x fixed). Since S(n+5) is S(n) plus five integers on each side, splitting the
inner sum and then the outer sum (with Fubini for the outer blocks) gives
f(n+5) = f(n) + 2 (2n+11) + 2 (2n+1) = f(n) + 8n + 24.
The recurrence of order 7 follows from that relation, and the g.f. follows from the recurrence
and the first seven terms 1, 1, 5, 9, 17, 25, 33 (the first five by kernel computation).
-/

namespace OMA.P211434

open OMA.S_oeis_a211434 PowerSeries

/-- The interval {-n, ..., n}. -/
noncomputable abbrev S (n : ℕ) : Finset ℤ := Finset.Icc (-(n : ℤ)) n

/-- The number of pairs (w, x) in S(n)^2 with 5 dividing w + 2x. -/
noncomputable def f (n : ℕ) : ℕ :=
  ∑ w ∈ S n, ∑ x ∈ S n, if 5 ∣ w + 2 * x then 1 else 0

lemma card_S (n : ℕ) : (S n).card = 2 * n + 1 := by
  simp only [S, Int.card_Icc]
  omega

/-- Five consecutive values of x contain exactly one with 5 | w + 2x. -/
lemma block_x (c w : ℤ) :
    (∑ x ∈ Finset.Ico c (c + 5), if 5 ∣ w + 2 * x then 1 else 0) = 1 := by
  rw [← Finset.card_filter, Finset.card_eq_one]
  refine ⟨c + (2 * w - c) % 5, ?_⟩
  ext x
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
  constructor
  · intro h
    omega
  · intro h
    omega

/-- Five consecutive values of w contain exactly one with 5 | w + 2x. -/
lemma block_w (c x : ℤ) :
    (∑ w ∈ Finset.Ico c (c + 5), if 5 ∣ w + 2 * x then 1 else 0) = 1 := by
  rw [← Finset.card_filter, Finset.card_eq_one]
  refine ⟨c + (-2 * x - c) % 5, ?_⟩
  ext w
  simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_singleton]
  constructor
  · intro h
    omega
  · intro h
    omega

/-- S(n+5) is S(n) with five integers added on each side. -/
lemma sum_split (n : ℕ) (g : ℤ → ℕ) :
    ∑ x ∈ S (n + 5), g x = ∑ x ∈ Finset.Ico (-(n : ℤ) - 5) (-(n : ℤ) - 5 + 5), g x
      + ∑ x ∈ S n, g x + ∑ x ∈ Finset.Ico ((n : ℤ) + 1) ((n : ℤ) + 1 + 5), g x := by
  have h1 : S (n + 5) = Finset.Ico (-(n : ℤ) - 5) (-(n : ℤ) - 5 + 5) ∪ S n
      ∪ Finset.Ico ((n : ℤ) + 1) ((n : ℤ) + 1 + 5) := by
    ext x
    simp only [S, Finset.mem_union, Finset.mem_Ico, Finset.mem_Icc]
    push_cast
    omega
  rw [h1, Finset.sum_union, Finset.sum_union]
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp only [S, Finset.mem_Ico, Finset.mem_Icc] at hx hy
    omega
  · rw [Finset.disjoint_left]
    intro x hx hy
    simp only [S, Finset.mem_union, Finset.mem_Ico, Finset.mem_Icc] at hx hy
    omega

/-- The key relation f(n+5) = f(n) + 8n + 24. -/
lemma step (n : ℕ) : f (n + 5) = f n + 8 * n + 24 := by
  have inner : ∀ w : ℤ, (∑ x ∈ S (n + 5), if 5 ∣ w + 2 * x then 1 else 0)
      = (∑ x ∈ S n, if 5 ∣ w + 2 * x then 1 else 0) + 2 := by
    intro w
    rw [sum_split n, block_x, block_x]
    ring
  have outer : ∀ c : ℤ,
      (∑ w ∈ Finset.Ico c (c + 5), ∑ x ∈ S n, if 5 ∣ w + 2 * x then 1 else 0) = 2 * n + 1 := by
    intro c
    rw [Finset.sum_comm]
    simp only [block_w, Finset.sum_const, card_S, smul_eq_mul, mul_one]
  unfold f
  simp only [inner]
  rw [Finset.sum_add_distrib, Finset.sum_const, card_S, smul_eq_mul, sum_split n, outer, outer]
  ring

/-- For w, x in S(n), the y in S(n) with w + 2x + 5y = 0 are counted by [5 | w + 2x]. -/
lemma inner_y (n : ℕ) (w x : ℤ) (hw : w ∈ S n) (hx : x ∈ S n) :
    (∑ y ∈ S n, if w + 2 * x + 5 * y = 0 then 1 else 0) = if 5 ∣ w + 2 * x then 1 else 0 := by
  simp only [S, Finset.mem_Icc] at hw hx
  by_cases h : 5 ∣ w + 2 * x
  · rw [if_pos h, ← Finset.card_filter, Finset.card_eq_one]
    refine ⟨-(w + 2 * x) / 5, ?_⟩
    ext y
    simp only [S, Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · intro h'
      omega
    · intro h'
      omega
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro y _
    rw [if_neg]
    intro h'
    apply h
    omega

/-- The triple count equals the pair count. -/
lemma a_eq_f (n : ℕ) : a n = f n := by
  unfold a f
  rw [Finset.card_filter, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro w hw
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  exact inner_y n w x hw hx

lemma f_small : f 0 = 1 ∧ f 1 = 1 ∧ f 2 = 5 ∧ f 3 = 9 ∧ f 4 = 17 :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The recurrence for n > 6, from f(n+5) = f(n) + 8n + 24. -/
lemma recur (n : ℕ) (hn : 6 < n) :
    (a n : ℤ) = 2 * a (n - 1) - a (n - 2) + a (n - 5) - 2 * a (n - 6) + a (n - 7) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  rw [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
    show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega,
    show k + 7 - 7 = k by omega]
  simp only [a_eq_f]
  have h1 : f (k + 7) = f (k + 2) + 8 * (k + 2) + 24 := step (k + 2)
  have h2 : f (k + 6) = f (k + 1) + 8 * (k + 1) + 24 := step (k + 1)
  have h3 : f (k + 5) = f k + 8 * k + 24 := step k
  omega

/-- The numerator of the g.f., with its coefficients written as constants. -/
lemma rhs_eq : (1 - X + 4 * X ^ 2 + 4 * X ^ 4 - X ^ 5 + X ^ 6 : PowerSeries ℤ) =
    C 1 - C 1 * X ^ 1 + C 4 * X ^ 2 + C 4 * X ^ 4 - C 1 * X ^ 5 + C 1 * X ^ 6 := by
  simp

/-- A sequence with these seven first terms and this recurrence has the stated g.f. -/
lemma gf_of (g : ℕ → ℤ) (h0 : g 0 = 1) (h1 : g 1 = 1) (h2 : g 2 = 5) (h3 : g 3 = 9)
    (h4 : g 4 = 17) (h5 : g 5 = 25) (h6 : g 6 = 33)
    (hr : ∀ j : ℕ, g (j + 7) = 2 * g (j + 6) - g (j + 5) + g (j + 2) - 2 * g (j + 1) + g j) :
    PowerSeries.mk g * ((1 - X) ^ 3 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) : PowerSeries ℤ) =
      1 - X + 4 * X ^ 2 + 4 * X ^ 4 - X ^ 5 + X ^ 6 := by
  have e : PowerSeries.mk g * ((1 - X) ^ 3 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) : PowerSeries ℤ)
      = PowerSeries.mk g - (PowerSeries.mk g * X ^ 1 + PowerSeries.mk g * X ^ 1)
        + PowerSeries.mk g * X ^ 2 - PowerSeries.mk g * X ^ 5
        + (PowerSeries.mk g * X ^ 6 + PowerSeries.mk g * X ^ 6) - PowerSeries.mk g * X ^ 7 := by
    ring
  rw [e, rhs_eq]
  ext m
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_mk, coeff_C]
  obtain hm | hm : m ≤ 6 ∨ 7 ≤ m := by omega
  · interval_cases m <;> simp [h0, h1, h2, h3, h4, h5, h6]
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 7 := ⟨m - 7, by omega⟩
    have := hr j
    simp only [show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 4 = j + 3 by omega, show j + 7 - 5 = j + 2 by omega,
      show j + 7 - 6 = j + 1 by omega, show j + 7 - 7 = j by omega]
    simp
    linarith

theorem sol : type_of% @OMA.S_oeis_a211434.main := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := f_small
  have h5 : f 5 = 25 := by
    have := step 0
    simp only [h0] at this
    simpa using this
  have h6 : f 6 = 33 := by
    have := step 1
    simp only [h1] at this
    simpa using this
  refine ⟨?_, recur⟩
  apply gf_of
  · simp [a_eq_f, h0]
  · simp [a_eq_f, h1]
  · simp [a_eq_f, h2]
  · simp [a_eq_f, h3]
  · simp [a_eq_f, h4]
  · simp [a_eq_f, h5]
  · simp [a_eq_f, h6]
  · intro j
    have := recur (j + 7) (by omega)
    simpa [show j + 7 - 1 = j + 6 by omega, show j + 7 - 2 = j + 5 by omega,
      show j + 7 - 5 = j + 2 by omega, show j + 7 - 6 = j + 1 by omega,
      show j + 7 - 7 = j by omega] using this

end OMA.P211434

theorem OMA.solution : type_of% @OMA.S_oeis_a211434.main := OMA.P211434.sol

