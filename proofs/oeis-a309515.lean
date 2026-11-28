import OMAStatements.S_oeis_a309515
import Mathlib

/-! # Even parts in partitions with exactly three parts

Mark an occurrence of an even part `m` and remove it. The remaining parts
form a sorted positive pair `x ≤ y` of sum `n-m`. Inserting `m` has one
possible position, plus an extra position for each of `x` and `y` equal to
`m`. Summing these weights gives a cubic in `n/2`, a quadratic in
`(n-1)/4`, and the equal-parts contribution when `6 ∣ n`. -/

open Finset OMA.S_oeis_a309515

private def p309ok (n x y z : ℕ) : Prop :=
  0 < x ∧ x ≤ y ∧ y ≤ z ∧ x+y+z=n

private instance (n x y z : ℕ) : Decidable (p309ok n x y z) := by
  unfold p309ok
  infer_instance

private lemma p309_last (n x y : ℕ) (P : ℕ → Prop) [DecidablePred P] (f : ℕ → ℕ) :
    (∑ z ∈ range (n+1), if x+y+z=n ∧ P z then f z else 0) =
    if x+y≤n ∧ P (n-x-y) then f (n-x-y) else 0 := by
  by_cases h : x+y≤n
  · have he (z : ℕ) : x+y+z=n ↔ n-x-y=z := by omega
    simp only [he, ite_and]
    rw [Finset.sum_ite_eq]
    simp [h, show n-x-y<n+1 by omega]
  · have he (z : ℕ) : ¬x+y+z=n := by omega
    simp [he, h]

private lemma p309_triples (n : ℕ) : a n =
    ∑ x ∈ range (n+1), ∑ y ∈ range (n+1), ∑ z ∈ range (n+1),
      if p309ok n x y z then evenPart x + evenPart y + evenPart z else 0 := by
  unfold a
  have outer : Icc 1 (n/3) = (range (n+1)).filter (fun x => 0 < x ∧ 3*x≤n) := by
    ext x
    simp only [mem_Icc, mem_filter, mem_range]
    omega
  rw [outer, sum_filter]
  apply sum_congr rfl
  intro x hx
  have hx' : x≤n := by simpa [Nat.lt_succ_iff] using hx
  have inner : Icc x ((n-x)/2) = (range (n+1)).filter (fun y => x≤y ∧ x+2*y≤n) := by
    ext y
    simp only [mem_Icc, mem_filter, mem_range]
    omega
  rw [inner, sum_filter]
  have distribute (P : Prop) [Decidable P] (f : ℕ → ℕ) :
      (if P then ∑ y ∈ range (n+1), f y else 0) = ∑ y ∈ range (n+1), if P then f y else 0 := by
    by_cases h : P <;> simp [h]
  rw [distribute]
  apply sum_congr rfl
  intro y hy
  have hh (z : ℕ) : p309ok n x y z ↔ x+y+z=n ∧ (0 < x ∧ x≤y ∧ y≤z) := by
    unfold p309ok
    tauto
  simp_rw [hh]
  rw [p309_last]
  rw [show n-y-x=n-x-y by omega]
  split_ifs <;> omega

private lemma p309_positions (n m x y : ℕ) :
    (if p309ok n m x y then 1 else 0) + (if p309ok n x m y then 1 else 0) +
      (if p309ok n x y m then 1 else 0) =
    (if m+x+y=n ∧ (0 < m ∧ 0 < x ∧ x≤y) then
        1 + (if x=m then 1 else 0) + (if y=m then 1 else 0) else 0) := by
  unfold p309ok
  grind

private def p309S (n : ℕ) (f : ℕ → ℕ → ℕ → ℕ) : ℕ :=
  ∑ x ∈ range (n+1), ∑ y ∈ range (n+1), ∑ z ∈ range (n+1), f x y z

private lemma p309_add (n : ℕ) (f g : ℕ → ℕ → ℕ → ℕ) :
    p309S n (fun x y z => f x y z + g x y z) = p309S n f + p309S n g := by
  simp only [p309S, sum_add_distrib]

private lemma p309_swap (n : ℕ) (f : ℕ → ℕ → ℕ → ℕ) :
    p309S n f = p309S n (fun y x z => f x y z) := by
  unfold p309S
  rw [sum_comm]

private lemma p309_rotate (n : ℕ) (f : ℕ → ℕ → ℕ → ℕ) :
    p309S n f = p309S n (fun z x y => f x y z) := by
  trans p309S n (fun x z y => f x y z)
  · apply sum_congr rfl
    intro x _
    rw [sum_comm]
  · exact p309_swap n _

private lemma p309_reindex (n : ℕ) : a n =
    ∑ m ∈ range (n+1), ∑ x ∈ range (n+1), ∑ y ∈ range (n+1), evenPart m *
      (if m+x+y=n ∧ (0 < m ∧ 0 < x ∧ x≤y) then
        1 + (if x=m then 1 else 0) + (if y=m then 1 else 0) else 0) := by
  let f (x y z : ℕ) := if p309ok n x y z then evenPart x else 0
  let g (x y z : ℕ) := if p309ok n x y z then evenPart y else 0
  let h (x y z : ℕ) := if p309ok n x y z then evenPart z else 0
  have start : a n = p309S n (fun x y z => (f x y z + g x y z) + h x y z) := by
    rw [p309_triples]
    apply congrArg (p309S n)
    funext x y z
    by_cases hp : p309ok n x y z <;> simp [f, g, h, hp]
  rw [start, p309_add, p309_add, p309_swap n g, p309_rotate n h, ← p309_add, ← p309_add]
  apply congrArg (p309S n)
  funext m x y
  rw [← p309_positions, Nat.mul_add, Nat.mul_add]
  dsimp only [f,g,h]
  by_cases hp : p309ok n m x y <;> by_cases hq : p309ok n x m y <;>
    by_cases hr : p309ok n x y m <;> simp [hp,hq,hr]

open Finset

private lemma p309_tail (n m : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
    (∑ x ∈ range (n+1), ∑ y ∈ range (n+1),
      if m+x+y=n ∧ (0 < m ∧ 0 < x ∧ x ≤ y) then
        1 + (if x=m then 1 else 0) + (if y=m then 1 else 0) else 0) =
    (n-m)/2 + (if 2*m < n then 1 else 0) + (if 3*m=n then 1 else 0) := by
  have he (x : ℕ) : m+x ≤ n ∧ (0 < m ∧ 0 < x ∧ x ≤ n-m-x) ↔
      1 ≤ x ∧ x ≤ (n-m)/2 := by omega
  have hs : (range (n+1)).filter (fun x => 1 ≤ x ∧ x ≤ (n-m)/2) =
      Icc 1 ((n-m)/2) := by
    ext x
    simp only [mem_filter, mem_range, mem_Icc]
    omega
  simp_rw [p309_last, he]
  rw [← sum_filter, hs]
  have hy (x : ℕ) (hx : x ∈ Icc 1 ((n-m)/2)) : n-m-x=m ↔ x=n-2*m ∧ 2*m ≤ n := by
    simp only [mem_Icc] at hx
    omega
  calc
    _ = ∑ x ∈ Icc 1 ((n-m)/2),
        (1 + (if x=m then 1 else 0) + (if x=n-2*m ∧ 2*m ≤ n then 1 else 0)) :=
      sum_congr rfl fun x hx => by simp only [hy _ hx]
    _ = _ := by
      simp only [sum_add_distrib, sum_const, Nat.card_Icc, Nat.add_sub_cancel,
        smul_eq_mul, mul_one, ite_and]
      simp only [Finset.sum_ite_eq', mem_Icc]
      split_ifs <;> omega

private theorem part309515_weighted_count (n : ℕ) : a n =
    ∑ m ∈ range (n+1), evenPart m * ((n-m)/2 +
      (if 2*m < n then 1 else 0) + (if 3*m=n then 1 else 0)) := by
  rw [p309_reindex]
  apply sum_congr rfl
  intro m hm
  simp_rw [← Finset.mul_sum]
  by_cases h : m=0
  · subst m
    simp [evenPart]
  · rw [p309_tail n m (by omega) (by simpa [Nat.lt_succ_iff] using hm)]

open OMA.S_oeis_a309515 Finset

private lemma part309515_even_sum (f : ℕ → ℕ) (n : ℕ) :
    (∑ m ∈ range (n+1), evenPart m * f m) = ∑ u ∈ range (n/2+1), 2*u * f (2*u) := by
  induction n with
  | zero => simp [evenPart]
  | succ n ih =>
    rw [sum_range_succ _ (n+1), ih]
    by_cases he : Even (n+1)
    · have hmod := Nat.even_iff.mp he
      rw [show (n+1)/2+1 = (n/2+1)+1 by omega, sum_range_succ _ (n/2+1), evenPart, if_pos he,
        show 2*(n/2+1) = n+1 by omega]
    · have hmod : ¬ (n+1)%2 = 0 := fun h => he (Nat.even_iff.mpr h)
      rw [show (n+1)/2+1 = n/2+1 by omega, evenPart, if_neg he, zero_mul, add_zero]

private lemma part309515_counts
    (h : ∀ n : ℕ, a n = ∑ m ∈ range (n+1), evenPart m *
      ((n-m)/2 + (if 2*m<n then 1 else 0) + (if 3*m=n then 1 else 0)))
    (n : ℕ) : a n = (∑ u ∈ range (n/2+1), 2*u*(n/2-u)) +
        (∑ u ∈ range ((n-1)/4+1), 2*u) + (if 6 ∣ n then n/3 else 0) := by
  rw [h, part309515_even_sum]
  by_cases hn : n = 0
  · simp [hn]
  have htrim : ((range (n/2+1)).filter fun u => 2*(2*u)<n) = range ((n-1)/4+1) := by
    ext u
    simp only [mem_filter, mem_range]
    omega
  have hdiag : (∑ u ∈ range (n/2+1), if 3*(2*u)=n then 2*u else 0) =
      (if 6 ∣ n then n/3 else 0) := by
    by_cases hd : 6 ∣ n
    · obtain ⟨v, rfl⟩ := hd
      simp only [dvd_mul_right, if_true]
      have he : ∀ u : ℕ, 3*(2*u)=6*v ↔ u=v := fun u => by omega
      simp [he, show v < 6*v/2+1 by omega]
      omega
    · have he : ∀ u : ℕ, 3*(2*u) ≠ n := fun u hu => hd ⟨u, by omega⟩
      simp [he, hd]
  have hhalf (u : ℕ) : (n-2*u)/2 = n/2-u := by omega
  simp_rw [Nat.mul_add, hhalf, mul_ite, mul_one, mul_zero, sum_add_distrib]
  rw [← sum_filter, htrim, hdiag]

open OMA.S_oeis_a309515 Finset

private lemma part309515_sum_double (m : ℕ) :
    (∑ u ∈ range (m+1), 2*u) = m*(m+1) := by
  rw [← mul_sum, mul_comm 2, sum_range_id_mul_two]
  simp [mul_comm]

private lemma part309515_cubic_sum (m : ℕ) :
    3 * (∑ u ∈ range (m+1), 2*u*(m-u)) + m = m^3 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hs : (∑ u ∈ range (m+1+1), 2*u*(m+1-u)) =
        (∑ u ∈ range (m+1), 2*u*(m-u)) + m*(m+1) := by
      rw [sum_range_succ, Nat.sub_self, mul_zero, add_zero, ← part309515_sum_double,
        ← sum_add_distrib]
      apply sum_congr rfl
      intro u hu
      have h := mem_range.mp hu
      rw [show m+1-u = m-u+1 by omega]
      ring
    rw [hs]
    nlinarith [ih]

private lemma part309515_closed
    (counts : ∀ n : ℕ, a n = (∑ u ∈ range (n/2+1), 2*u*(n/2-u)) +
        (∑ u ∈ range ((n-1)/4+1), 2*u) + (if 6 ∣ n then n/3 else 0))
    (n : ℕ) : 3*a n = (n/2)^3 - n/2 +
        3*(((n-1)/4)*(((n-1)/4)+1) + (if 6 ∣ n then n/3 else 0)) := by
  rw [counts, part309515_sum_double]
  have h := part309515_cubic_sum (n/2)
  omega

private lemma part309515_closed_int
    (counts : ∀ n : ℕ, a n = (∑ u ∈ range (n/2+1), 2*u*(n/2-u)) +
        (∑ u ∈ range ((n-1)/4+1), 2*u) + (if 6 ∣ n then n/3 else 0))
    (n : ℕ) : 3*(a n : ℤ) = ((n/2 : ℕ) : ℤ)^3 - ((n/2 : ℕ) : ℤ) +
        3*((((n-1)/4 : ℕ) : ℤ)*((((n-1)/4 : ℕ) : ℤ)+1) +
          (if 6 ∣ n then ((n/3 : ℕ) : ℤ) else 0)) := by
  have h := part309515_closed counts n
  have hle : n/2 ≤ (n/2)^3 := by have := part309515_cubic_sum (n/2); omega
  split_ifs at * <;> exact_mod_cast (Int.ofNat_inj.mpr h :
    ((3 * a n : ℕ) : ℤ) = _)

open OMA.S_oeis_a309515

set_option maxHeartbeats 5000000 in
private lemma part309515_rec
    (h : ∀ n : ℕ, 3*(a n : ℤ) = ((n/2 : ℕ) : ℤ)^3 - ((n/2 : ℕ) : ℤ) +
        3*((((n-1)/4 : ℕ) : ℤ)*((((n-1)/4 : ℕ) : ℤ)+1) +
          (if 6 ∣ n then ((n/3 : ℕ) : ℤ) else 0))) :
    ∀ n : ℕ, 18 < n →
      (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) + a (n - 4) - a (n - 5) + 3 * a (n - 6)
        - 3 * a (n - 7) + 2 * a (n - 8) - 2 * a (n - 9) - 2 * a (n - 10) + 2 * a (n - 11)
        - 3 * a (n - 12) + 3 * a (n - 13) - a (n - 14) + a (n - 15) + a (n - 16) - a (n - 17)
        + a (n - 18) - a (n - 19) := by
  let b (n : ℕ) : ℤ := ((n/2 : ℕ) : ℤ)^3 - ((n/2 : ℕ) : ℤ) +
        3*((((n-1)/4 : ℕ) : ℤ)*((((n-1)/4 : ℕ) : ℤ)+1) +
          (if 6 ∣ n then ((n/3 : ℕ) : ℤ) else 0))
  let R (u : ℕ → ℤ) (n : ℕ) := u n -
    (u (n-1) - u (n-2) + u (n-3) + u (n-4) - u (n-5) + 3*u (n-6) -
     3*u (n-7) + 2*u (n-8) - 2*u (n-9) - 2*u (n-10) + 2*u (n-11) -
     3*u (n-12) + 3*u (n-13) - u (n-14) + u (n-15) + u (n-16) -
     u (n-17) + u (n-18) - u (n-19))
  let P (k s : ℕ) : ℤ :=
    (6*(k:ℤ) + (s/2:ℕ))^3 - (6*(k:ℤ) + (s/2:ℕ)) +
      3*((3*(k:ℤ) + ((s-1)/4 : ℕ))*(3*(k:ℤ) + ((s-1)/4 : ℕ) + 1) +
        if 6 ∣ s then 4*(k:ℤ)+(s/3:ℕ) else 0)
  have block (k s : ℕ) (hs : 1 ≤ s) : b (12*k+s) = P k s := by
    dsimp only [b,P]
    simp only [show (12*k+s)/2 = 6*k+s/2 by omega,
        show (12*k+s-1)/4 = 3*k+(s-1)/4 by omega,
        show (12*k+s)/3 = 4*k+s/3 by omega,
        show (6 ∣ 12*k+s) ↔ 6 ∣ s by omega, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  have vanishes (k r : ℕ) (hr : r<12) : R b (12*k+(20+r)) = 0 := by
    dsimp only [R]
    have shift (i : ℕ) (hi : i ≤ 19) : 12*k+(20+r)-i = 12*k+(20+r-i) := by omega
    simp (disch := decide) only [shift]
    simp (disch := omega) only [block]
    interval_cases r <;> norm_num [P] <;> ring
  intro n hn
  have hz : R b n = 0 := by
    by_cases eq : n=19
    · subst n; norm_num [R,b]
    · have shape : n = 12*((n-20)/12)+(20+(n-20)%12) := by omega
      exact shape ▸ vanishes ((n-20)/12) ((n-20)%12) (Nat.mod_lt _ (by decide))
  have hx (m : ℕ) : 3*(a m : ℤ) = b m := h m
  have scale : 3*R (fun m => (a m : ℤ)) n = R b n := by
    dsimp only [R]
    linear_combination hx n - hx (n-1) + hx (n-2) - hx (n-3) - hx (n-4) + hx (n-5) -
      3 * hx (n-6) + 3 * hx (n-7) - 2 * hx (n-8) + 2 * hx (n-9) + 2 * hx (n-10) -
      2 * hx (n-11) + 3 * hx (n-12) - 3 * hx (n-13) + hx (n-14) - hx (n-15) -
      hx (n-16) + hx (n-17) - hx (n-18) + hx (n-19)
  rw [hz] at scale
  dsimp only [R] at scale
  omega

open OMA.S_oeis_a309515 PowerSeries

set_option maxRecDepth 10000 in
private lemma part309515_values : ∀ i : Fin 19,
    a i.val = ([0, 0, 0, 0, 2, 4, 12, 10, 22, 26, 46, 46, 80, 82, 124, 124, 180, 188, 266] : List ℕ).getD i.val 0 := by decide +kernel

set_option maxHeartbeats 3000000 in
private lemma part309515_gf
    (rec : ∀ n : ℕ, 18 < n →
      (a n : ℤ) = a (n - 1) - a (n - 2) + a (n - 3) + a (n - 4) - a (n - 5) + 3 * a (n - 6)
        - 3 * a (n - 7) + 2 * a (n - 8) - 2 * a (n - 9) - 2 * a (n - 10) + 2 * a (n - 11)
        - 3 * a (n - 12) + 3 * a (n - 13) - a (n - 14) + a (n - 15) + a (n - 16) - a (n - 17)
        + a (n - 18) - a (n - 19)) :
    (PowerSeries.mk (fun n => (a n : ℚ)) *
        ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 - X + X ^ 2) ^ 2 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2) =
      2 * X ^ 4 * (1 + X + 5 * X ^ 2 + 9 * X ^ 4 + 9 * X ^ 6 + 7 * X ^ 8 + 4 * X ^ 10 - X ^ 11
        + X ^ 12)) := by
  have recQ : ∀ n : ℕ, 18 < n →
      (a n : ℚ) = a (n - 1) - a (n - 2) + a (n - 3) + a (n - 4) - a (n - 5) + 3 * a (n - 6)
        - 3 * a (n - 7) + 2 * a (n - 8) - 2 * a (n - 9) - 2 * a (n - 10) + 2 * a (n - 11)
        - 3 * a (n - 12) + 3 * a (n - 13) - a (n - 14) + a (n - 15) + a (n - 16) - a (n - 17)
        + a (n - 18) - a (n - 19) := by
    intro n hn
    exact_mod_cast rec n hn
  let A := PowerSeries.mk (fun n => (a n : ℚ))
  have lhs : A * ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 - X + X ^ 2) ^ 2 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2) =
        A - A*X^1 + A*X^2 - A*X^3
        - A*X^4 + A*X^5 - C (3 : ℚ) * (A*X^6) + C (3 : ℚ) * (A*X^7)
        - C (2 : ℚ) * (A*X^8) + C (2 : ℚ) * (A*X^9) + C (2 : ℚ) * (A*X^10) - C (2 : ℚ) * (A*X^11)
        + C (3 : ℚ) * (A*X^12) - C (3 : ℚ) * (A*X^13) + A*X^14 - A*X^15
        - A*X^16 + A*X^17 - A*X^18 + A*X^19 := by
    norm_num [map_ofNat]
    ring
  have rhs : 2 * X ^ 4 * (1 + X + 5 * X ^ 2 + 9 * X ^ 4 + 9 * X ^ 6 + 7 * X ^ 8 + 4 * X ^ 10 - X ^ 11 + X ^ 12) =
        C (2 : ℚ) * (X^4) + C (2 : ℚ) * (X^5) + C (10 : ℚ) * (X^6) + C (18 : ℚ) * (X^8)
        + C (18 : ℚ) * (X^10) + C (14 : ℚ) * (X^12) + C (8 : ℚ) * (X^14) - C (2 : ℚ) * (X^15)
        + C (2 : ℚ) * (X^16) := by
    norm_num [map_ofNat]
    ring
  change A * ((1 - X) ^ 4 * (1 + X) ^ 3 * (1 - X + X ^ 2) ^ 2 * (1 + X ^ 2) ^ 2 * (1 + X + X ^ 2) ^ 2) = _
  rw [lhs, rhs]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_mul_X_pow', A, coeff_mk, coeff_C]
  by_cases hn : 18 < n
  · simp (disch := omega) only [if_pos, if_neg]
    linarith [recQ n hn]
  · have hv (k : ℕ) (hk : k < 19) :
        a k = ([0, 0, 0, 0, 2, 4, 12, 10, 22, 26, 46, 46, 80, 82, 124, 124, 180, 188, 266] : List ℕ).getD k 0 :=
      part309515_values ⟨k,hk⟩
    interval_cases n <;> norm_num [hv, List.getD]

theorem OMA.solution : type_of% @OMA.S_oeis_a309515.main := by
  have closed := part309515_closed_int (part309515_counts part309515_weighted_count)
  have recurrence := part309515_rec closed
  exact ⟨part309515_gf recurrence, recurrence⟩
