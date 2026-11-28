import OMAStatements.S_oeis_a154293
import Mathlib

/-!
# A154293: A193828 divided by 2, and the g.f.

Both sets reduce to the same condition: 48 j + 1 is a perfect square.
* T(m) = 6j iff (2m + 1)^2 = 48j + 1.
* 2(2j) = k(3k - 1) iff (6k - 1)^2 = 48j + 1; a square root s of 48j + 1 is 1 or 5 mod 6,
  which gives k = -(s - 1)/6 or k = (s + 1)/6.
So an even g is an even generalized pentagonal number iff g/2 is of the form T(m)/6, and no
odd g is counted. Hence count Q (2m) = count P m, and with `Nat.nth_count` and
`Nat.count_nth_of_infinite` the n-th term of Q is twice the n-th term of P.

For the g.f., the enumeration is given in closed form (Peter Bala's formulas, shifted by one):
c(4m) = m(12m+1), c(4m+1) = (3m+1)(4m+1), c(4m+2) = (3m+2)(4m+3), c(4m+3) = (m+1)(12m+11).
c is strictly increasing and its range is the set P (the root m of T(m) = 6x is 0, 3, 8 or 11
mod 12), so `Nat.nth P = c` by `StrictMono.range_inj`. The closed form satisfies the order 7
recurrence with signature (3, -5, 7, -7, 5, -3, 1), which is the g.f. identity read coefficient
by coefficient; the first eight coefficients are checked directly.
-/

namespace OMA.P154293

open OMA.S_oeis_a154293 PowerSeries

lemma tri_iff (j : ℕ) : IsTriangularSixth j ↔ ∃ s : ℕ, s ^ 2 = 48 * j + 1 := by
  constructor
  · rintro ⟨m, hm⟩
    refine ⟨2 * m + 1, ?_⟩
    unfold triangular at hm
    obtain ⟨r, hr⟩ := Nat.even_mul_succ_self m
    have h12 : m * (m + 1) = 12 * j := by omega
    calc (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
      _ = 48 * j + 1 := by rw [h12]; ring
  · rintro ⟨s, hs⟩
    obtain ⟨m, rfl⟩ : ∃ m, s = 2 * m + 1 := by
      rcases Nat.even_or_odd s with ⟨r, hr⟩ | ⟨r, hr⟩
      · exfalso
        subst hr
        have : (r + r) ^ 2 = 4 * (r * r) := by ring
        omega
      · exact ⟨r, hr⟩
    refine ⟨m, ?_⟩
    unfold triangular
    have h : (2 * m + 1) ^ 2 = 4 * (m * (m + 1)) + 1 := by ring
    have h12 : m * (m + 1) = 12 * j := by omega
    rw [h12]
    omega

lemma pent_iff (j : ℕ) : IsGenPentagonal (2 * j) ↔ ∃ s : ℕ, s ^ 2 = 48 * j + 1 := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨(6 * k - 1).natAbs, ?_⟩
    have h : ((6 * k - 1).natAbs : ℤ) ^ 2 = 48 * (j : ℤ) + 1 := by
      rw [Int.natAbs_sq]
      push_cast at hk
      linear_combination (-12 : ℤ) * hk
    exact_mod_cast h
  · rintro ⟨s, hs⟩
    have h1 : s ^ 2 % 6 = 1 := by rw [hs]; omega
    have h2 : s ^ 2 % 6 = (s % 6) ^ 2 % 6 := Nat.pow_mod s 2 6
    have h3 : s % 6 < 6 := Nat.mod_lt s (by norm_num)
    have h6 : s % 6 = 1 ∨ s % 6 = 5 := by
      interval_cases h : s % 6 <;> simp_all
    rcases h6 with h | h
    · obtain ⟨t, rfl⟩ : ∃ t, s = 6 * t + 1 := ⟨s / 6, by omega⟩
      have e : (6 * t + 1) ^ 2 = 36 * t ^ 2 + 12 * t + 1 := by ring
      have h4 : 3 * t ^ 2 + t = 4 * j := by omega
      refine ⟨-(t : ℤ), ?_⟩
      have h4' : (3 * (t : ℤ) ^ 2 + t) = 4 * j := by exact_mod_cast h4
      push_cast
      linear_combination (-1 : ℤ) * h4'
    · obtain ⟨t, rfl⟩ : ∃ t, s = 6 * t + 5 := ⟨s / 6, by omega⟩
      have e : (6 * t + 5) ^ 2 = 36 * t ^ 2 + 60 * t + 25 := by ring
      have h4 : 3 * t ^ 2 + 5 * t + 2 = 4 * j := by omega
      refine ⟨(t : ℤ) + 1, ?_⟩
      have h4' : (3 * (t : ℤ) ^ 2 + 5 * t + 2) = 4 * j := by exact_mod_cast h4
      push_cast
      linear_combination (-1 : ℤ) * h4'

lemma Q_even (j : ℕ) : (Even (2 * j) ∧ IsGenPentagonal (2 * j)) ↔ IsTriangularSixth j := by
  rw [tri_iff, ← pent_iff]
  simp

lemma Q_odd (j : ℕ) : ¬ (Even (2 * j + 1) ∧ IsGenPentagonal (2 * j + 1)) := by
  rintro ⟨h, -⟩
  rw [Nat.even_iff] at h
  omega

lemma P_infinite : (Set.ofPred IsTriangularSixth).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro x
  refine ⟨(x + 1) * (12 * (x + 1) + 1), ?_, ?_⟩
  · show IsTriangularSixth _
    refine ⟨12 * (x + 1), ?_⟩
    unfold triangular
    rw [show 12 * (x + 1) * (12 * (x + 1) + 1) = 2 * (6 * ((x + 1) * (12 * (x + 1) + 1))) by ring]
    omega
  · nlinarith

open Classical in
lemma count_eq (m : ℕ) :
    Nat.count (fun g => Even g ∧ IsGenPentagonal g) (2 * m) = Nat.count IsTriangularSixth m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Nat.count_succ, Nat.count_succ, Nat.count_succ, ih]
    have h1 := Q_even m
    have h2 := Q_odd m
    by_cases hm : IsTriangularSixth m
    · simp [hm, h1.mpr hm]
    · have : ¬ IsGenPentagonal (2 * m) := fun h => hm (h1.mp ⟨even_two_mul m, h⟩)
      simp [hm, this]

lemma nth_Q (k : ℕ) :
    Nat.nth (fun g => Even g ∧ IsGenPentagonal g) k = 2 * Nat.nth IsTriangularSixth k := by
  classical
  have hPx : IsTriangularSixth (Nat.nth IsTriangularSixth k) := Nat.nth_mem_of_infinite P_infinite k
  have hcx : Nat.count IsTriangularSixth (Nat.nth IsTriangularSixth k) = k :=
    Nat.count_nth_of_infinite P_infinite k
  have hQ := (Q_even (Nat.nth IsTriangularSixth k)).mpr hPx
  have h := Nat.nth_count (p := fun g => Even g ∧ IsGenPentagonal g) hQ
  rw [count_eq, hcx] at h
  exact h

theorem part1 : ∀ n : ℕ, 1 ≤ n → 2 * a n = b (n - 1) := by
  intro n _
  unfold a b
  rw [nth_Q]

/-- The closed form of A154293, shifted to start at index 0. -/
def c (k : ℕ) : ℕ :=
  if k % 4 = 0 then (k / 4) * (12 * (k / 4) + 1)
  else if k % 4 = 1 then (3 * (k / 4) + 1) * (4 * (k / 4) + 1)
  else if k % 4 = 2 then (3 * (k / 4) + 2) * (4 * (k / 4) + 3)
  else (k / 4 + 1) * (12 * (k / 4) + 11)

lemma c0 (m : ℕ) : c (4 * m) = m * (12 * m + 1) := by
  have h1 : 4 * m % 4 = 0 := by omega
  have h2 : 4 * m / 4 = m := by omega
  unfold c
  rw [h1, h2]
  simp

lemma c1 (m : ℕ) : c (4 * m + 1) = (3 * m + 1) * (4 * m + 1) := by
  have h1 : (4 * m + 1) % 4 = 1 := by omega
  have h2 : (4 * m + 1) / 4 = m := by omega
  unfold c
  rw [h1, h2]
  simp

lemma c2 (m : ℕ) : c (4 * m + 2) = (3 * m + 2) * (4 * m + 3) := by
  have h1 : (4 * m + 2) % 4 = 2 := by omega
  have h2 : (4 * m + 2) / 4 = m := by omega
  unfold c
  rw [h1, h2]
  simp

lemma c3 (m : ℕ) : c (4 * m + 3) = (m + 1) * (12 * m + 11) := by
  have h1 : (4 * m + 3) % 4 = 3 := by omega
  have h2 : (4 * m + 3) / 4 = m := by omega
  unfold c
  rw [h1, h2]
  simp

lemma c_strictMono : StrictMono c := by
  apply strictMono_nat_of_lt_succ
  intro k
  obtain ⟨m, rfl | rfl | rfl | rfl⟩ :
      ∃ m, k = 4 * m ∨ k = 4 * m + 1 ∨ k = 4 * m + 2 ∨ k = 4 * m + 3 := ⟨k / 4, by omega⟩
  · rw [c0, c1]; nlinarith
  · rw [c1, show 4 * m + 1 + 1 = 4 * m + 2 by ring, c2]; nlinarith
  · rw [c2, show 4 * m + 2 + 1 = 4 * m + 3 by ring, c3]; nlinarith
  · rw [c3, show 4 * m + 3 + 1 = 4 * (m + 1) by ring, c0]; nlinarith

lemma c_mem (k : ℕ) : IsTriangularSixth (c k) := by
  obtain ⟨m, rfl | rfl | rfl | rfl⟩ :
      ∃ m, k = 4 * m ∨ k = 4 * m + 1 ∨ k = 4 * m + 2 ∨ k = 4 * m + 3 := ⟨k / 4, by omega⟩
  · rw [c0]
    refine ⟨12 * m, ?_⟩
    unfold triangular
    rw [show 12 * m * (12 * m + 1) = 2 * (6 * (m * (12 * m + 1))) by ring]
    omega
  · rw [c1]
    refine ⟨12 * m + 3, ?_⟩
    unfold triangular
    rw [show (12 * m + 3) * (12 * m + 3 + 1) = 2 * (6 * ((3 * m + 1) * (4 * m + 1))) by ring]
    omega
  · rw [c2]
    refine ⟨12 * m + 8, ?_⟩
    unfold triangular
    rw [show (12 * m + 8) * (12 * m + 8 + 1) = 2 * (6 * ((3 * m + 2) * (4 * m + 3))) by ring]
    omega
  · rw [c3]
    refine ⟨12 * m + 11, ?_⟩
    unfold triangular
    rw [show (12 * m + 11) * (12 * m + 11 + 1) = 2 * (6 * ((m + 1) * (12 * m + 11))) by ring]
    omega

lemma mem_range_c (x : ℕ) (hx : IsTriangularSixth x) : ∃ k, c k = x := by
  obtain ⟨m, hm⟩ := hx
  unfold triangular at hm
  obtain ⟨r0, hr0⟩ := Nat.even_mul_succ_self m
  have h12 : m * (m + 1) = 12 * x := by omega
  obtain ⟨t, r, hr, rfl⟩ : ∃ t r, r < 12 ∧ m = 12 * t + r :=
    ⟨m / 12, m % 12, Nat.mod_lt _ (by norm_num), by omega⟩
  have key : (12 * t + r) * (12 * t + r + 1) = 144 * t ^ 2 + 12 * t * (2 * r + 1) + r * (r + 1) := by
    ring
  have e0 : t * (12 * t + 1) = 12 * t ^ 2 + t := by ring
  have e1 : (3 * t + 1) * (4 * t + 1) = 12 * t ^ 2 + 7 * t + 1 := by ring
  have e2 : (3 * t + 2) * (4 * t + 3) = 12 * t ^ 2 + 17 * t + 6 := by ring
  have e3 : (t + 1) * (12 * t + 11) = 12 * t ^ 2 + 23 * t + 11 := by ring
  clear hm hr0
  interval_cases r
  · exact ⟨4 * t, by rw [c0]; omega⟩
  · omega
  · omega
  · exact ⟨4 * t + 1, by rw [c1]; omega⟩
  · omega
  · omega
  · omega
  · omega
  · exact ⟨4 * t + 2, by rw [c2]; omega⟩
  · omega
  · omega
  · exact ⟨4 * t + 3, by rw [c3]; omega⟩

lemma nth_P_eq : Nat.nth IsTriangularSixth = c := by
  apply (StrictMono.range_inj (Nat.nth_strictMono P_infinite) c_strictMono).mp
  rw [Nat.range_nth_of_infinite P_infinite]
  ext x
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := mem_range_c x hx
    exact ⟨k, hk⟩
  · rintro ⟨k, rfl⟩
    exact c_mem k

lemma rec_c (j : ℕ) :
    (c (j + 7) : ℤ) - 3 * c (j + 6) + 5 * c (j + 5) - 7 * c (j + 4) + 7 * c (j + 3)
      - 5 * c (j + 2) + 3 * c (j + 1) - c j = 0 := by
  obtain ⟨m, rfl | rfl | rfl | rfl⟩ :
      ∃ m, j = 4 * m ∨ j = 4 * m + 1 ∨ j = 4 * m + 2 ∨ j = 4 * m + 3 := ⟨j / 4, by omega⟩
  · rw [show 4 * m + 7 = 4 * (m + 1) + 3 by ring, show 4 * m + 6 = 4 * (m + 1) + 2 by ring,
      show 4 * m + 5 = 4 * (m + 1) + 1 by ring, show 4 * m + 4 = 4 * (m + 1) by ring]
    simp only [c0, c1, c2, c3]
    push_cast
    ring
  · rw [show 4 * m + 1 + 7 = 4 * (m + 2) by ring, show 4 * m + 1 + 6 = 4 * (m + 1) + 3 by ring,
      show 4 * m + 1 + 5 = 4 * (m + 1) + 2 by ring, show 4 * m + 1 + 4 = 4 * (m + 1) + 1 by ring,
      show 4 * m + 1 + 3 = 4 * (m + 1) by ring, show 4 * m + 1 + 2 = 4 * m + 3 by ring,
      show 4 * m + 1 + 1 = 4 * m + 2 by ring]
    simp only [c0, c1, c2, c3]
    push_cast
    ring
  · rw [show 4 * m + 2 + 7 = 4 * (m + 2) + 1 by ring, show 4 * m + 2 + 6 = 4 * (m + 2) by ring,
      show 4 * m + 2 + 5 = 4 * (m + 1) + 3 by ring, show 4 * m + 2 + 4 = 4 * (m + 1) + 2 by ring,
      show 4 * m + 2 + 3 = 4 * (m + 1) + 1 by ring, show 4 * m + 2 + 2 = 4 * (m + 1) by ring,
      show 4 * m + 2 + 1 = 4 * m + 3 by ring]
    simp only [c0, c1, c2, c3]
    push_cast
    ring
  · rw [show 4 * m + 3 + 7 = 4 * (m + 2) + 2 by ring, show 4 * m + 3 + 6 = 4 * (m + 2) + 1 by ring,
      show 4 * m + 3 + 5 = 4 * (m + 2) by ring, show 4 * m + 3 + 4 = 4 * (m + 1) + 3 by ring,
      show 4 * m + 3 + 3 = 4 * (m + 1) + 2 by ring, show 4 * m + 3 + 2 = 4 * (m + 1) + 1 by ring,
      show 4 * m + 3 + 1 = 4 * (m + 1) by ring]
    simp only [c0, c1, c2, c3]
    push_cast
    ring

lemma coeff_gf (n : ℕ) : coeff n gf = if n = 0 then 0 else (c (n - 1) : ℤ) := by
  simp [gf, a, nth_P_eq]

lemma coeff_Xgf (i n : ℕ) (h : i < n) : coeff n (X ^ i * gf) = (c (n - 1 - i) : ℤ) := by
  rw [coeff_X_pow_mul', if_pos (by omega), coeff_gf, if_neg (by omega)]
  congr 2
  omega

lemma gf_id :
    (1 + X ^ 2) ^ 2 * (1 - X) ^ 3 * gf = X ^ 2 * (X ^ 2 - X + 1) * (X ^ 2 + 4 * X + 1) := by
  have hL : (1 + X ^ 2) ^ 2 * (1 - X) ^ 3 * gf = X ^ 0 * gf - C 3 * (X ^ 1 * gf)
      + C 5 * (X ^ 2 * gf) - C 7 * (X ^ 3 * gf) + C 7 * (X ^ 4 * gf) - C 5 * (X ^ 5 * gf)
      + C 3 * (X ^ 6 * gf) - X ^ 7 * gf := by
    simp only [map_ofNat]
    ring
  have hR : (X : PowerSeries ℤ) ^ 2 * (X ^ 2 - X + 1) * (X ^ 2 + 4 * X + 1)
      = X ^ 2 + C 3 * X ^ 3 - C 2 * X ^ 4 + C 3 * X ^ 5 + X ^ 6 := by
    simp only [map_ofNat]
    ring
  rw [hL, hR]
  ext n
  simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow]
  rcases lt_or_ge n 8 with hn | hn
  · interval_cases n <;> simp [coeff_X_pow_mul', coeff_gf, c]
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 8 := ⟨n - 8, by omega⟩
    rw [coeff_Xgf 0 _ (by omega), coeff_Xgf 1 _ (by omega), coeff_Xgf 2 _ (by omega),
      coeff_Xgf 3 _ (by omega), coeff_Xgf 4 _ (by omega), coeff_Xgf 5 _ (by omega),
      coeff_Xgf 6 _ (by omega), coeff_Xgf 7 _ (by omega)]
    have r := rec_c j
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega),
      if_neg (by omega)]
    have e0 : j + 8 - 1 - 0 = j + 7 := by omega
    have e1 : j + 8 - 1 - 1 = j + 6 := by omega
    have e2 : j + 8 - 1 - 2 = j + 5 := by omega
    have e3 : j + 8 - 1 - 3 = j + 4 := by omega
    have e4 : j + 8 - 1 - 4 = j + 3 := by omega
    have e5 : j + 8 - 1 - 5 = j + 2 := by omega
    have e6 : j + 8 - 1 - 6 = j + 1 := by omega
    have e7 : j + 8 - 1 - 7 = j := by omega
    rw [e0, e1, e2, e3, e4, e5, e6, e7]
    linear_combination r

theorem sol : type_of% @OMA.S_oeis_a154293.main := ⟨part1, gf_id⟩

end OMA.P154293

theorem OMA.solution : type_of% @OMA.S_oeis_a154293.main := OMA.P154293.sol

