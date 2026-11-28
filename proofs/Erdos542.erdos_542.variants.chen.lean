import FormalConjectures.ErdosProblems.«542»
import Mathlib

-- Problem: Erdos Problem 542, variant chen
-- Upstream: formal-conjectures FormalConjectures/ErdosProblems/542.lean:118 (declaration Erdos542.erdos_542.variants.chen)
-- Route: weighted packing. The multiples (at most n) of distinct members of A are disjoint.
-- Give m the weight G(floor(4n/m))/m for a fixed step function G (the list blocks below,
-- found by a linear program). The weight of the multiples of a is c(floor(4n/a))/a and the
-- total weight is c(4n), where c(M) = sum over blocks of g * (H(M/lo) - H(M/(hi+1))).
-- Then c(M) >= 10^7 for every M >= 4 and c(4n) < 10^7 * (1/3+1/4+1/5+1/7+1/11) for n > 172509.

namespace OMA.E542

open Finset

/-- The step function, as blocks (lo, hi, g): value g (scaled by 10^7) on lo..hi. -/
def blocks : List (ℕ × ℕ × ℕ) :=
  [(4, 4, 10000300), (5, 5, 10571746), (6, 7, 10000300), (8, 8, 5963454), (9, 9, 5000150),
   (10, 11, 4714428), (12, 14, 1666717), (15, 15, 1476235), (16, 17, 994583),
   (18, 19, 1666717), (24, 24, 1012273), (25, 26, 897983), (27, 27, 1219085),
   (40, 41, 463822), (42, 43, 545457), (48, 49, 156222), (50, 51, 213367),
   (60, 62, 306732), (63, 64, 444347), (65, 65, 400390), (66, 67, 452340),
   (84, 84, 33615), (88, 89, 185156), (90, 91, 216903), (112, 113, 117382),
   (114, 114, 147458), (115, 115, 122612), (140, 140, 90686), (141, 141, 115002),
   (142, 143, 61926), (144, 144, 95116), (145, 147, 75411), (232, 234, 22365),
   (235, 235, 10207)]

/-- Value of the step function of a block list at k. -/
def Gt (L : List (ℕ × ℕ × ℕ)) (k : ℕ) : ℕ :=
  (L.map fun b => if b.1 ≤ k ∧ k ≤ b.2.1 then b.2.2 else 0).sum

/-- Harmonic sum over the j with lo ≤ M / j ≤ hi. -/
noncomputable def bs (lo hi M : ℕ) : ℝ :=
  ∑ j ∈ Ioc (M / (hi + 1)) (M / lo), (1 : ℝ) / j

/-- The weight of the multiples of a, times a, as a function of M = 4 * n / a. -/
noncomputable def cR (L : List (ℕ × ℕ × ℕ)) (M : ℕ) : ℝ :=
  (L.map fun b => (b.2.2 : ℝ) * bs b.1 b.2.1 M).sum

/-- z = (y - x) / (y + x) for y = hi + 1 and x = lo. -/
def zq (lo hi : ℕ) : ℚ := ((hi : ℚ) + 1 - lo) / ((hi : ℚ) + 1 + lo)

/-- Rational lower bound for log ((hi + 1) / lo). -/
def lowQ (lo hi : ℕ) : ℚ := 2 * zq lo hi + 2 * zq lo hi ^ 3 / 3

/-- Rational upper bound for log ((hi + 1) / lo). -/
def upQ (lo hi : ℕ) : ℚ := 2 * zq lo hi + 2 * zq lo hi ^ 3 / (3 * (1 - zq lo hi ^ 2))

/-- Sum of D / j (natural division) over j in (a, a + c]. -/
def hs (D : ℕ) (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | c + 1 => D / (a + c + 1) + hs D a c

/-- Integer lower approximation of D * cR L M. -/
def cFl (D : ℕ) (L : List (ℕ × ℕ × ℕ)) (M : ℕ) : ℕ :=
  (L.map fun b => b.2.2 * hs D (M / (b.2.1 + 1)) (M / b.1 - M / (b.2.1 + 1))).sum

-- A. Packing and the weight identity

-- @@L packing
theorem packing (n : ℕ) (A : Finset ℕ) (w : ℕ → ℝ) (hsub : A ⊆ Icc 1 n)
    (hlcm : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b) (hw : ∀ m, 0 ≤ w m) :
    ∑ a ∈ A, ∑ j ∈ Icc 1 (n / a), w (a * j) ≤ ∑ m ∈ Icc 1 n, w m := by
  have h1 : ∑ a ∈ A, ∑ j ∈ Icc 1 (n / a), w (a * j)
      = ∑ x ∈ A.sigma (fun a => Icc 1 (n / a)), w (x.1 * x.2) := by
    rw [Finset.sum_sigma]
  have hinj : ∀ x ∈ A.sigma (fun a => Icc 1 (n / a)), ∀ y ∈ A.sigma (fun a => Icc 1 (n / a)),
      x.1 * x.2 = y.1 * y.2 → x = y := by
    rintro ⟨a, j⟩ hx ⟨a', j'⟩ hy hxy
    simp only [Finset.mem_sigma, Finset.mem_Icc] at hx hy
    obtain ⟨ha, hj1, hj2⟩ := hx
    have hjn0 : 1 ≤ j := hj1
    obtain ⟨ha', hj1', hj2'⟩ := hy
    have ha1 := Finset.mem_Icc.mp (hsub ha)
    have ha1' := Finset.mem_Icc.mp (hsub ha')
    simp only at hxy
    by_cases hne : a = a'
    · subst hne
      have hj : j = j' := Nat.eq_of_mul_eq_mul_left (by omega) hxy
      subst hj
      rfl
    · exfalso
      have hjn : j * a ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp hj2
      have hpos : 0 < a * j := Nat.mul_pos (by omega) (by omega)
      have d1 : a ∣ a * j := ⟨j, rfl⟩
      have d2 : a' ∣ a * j := ⟨j', hxy⟩
      have hle := Nat.le_of_dvd hpos (Nat.lcm_dvd d1 d2)
      have := hlcm a ha a' ha' hne
      rw [Nat.mul_comm] at hjn
      omega
  have h2 : ∑ x ∈ A.sigma (fun a => Icc 1 (n / a)), w (x.1 * x.2)
      = ∑ m ∈ (A.sigma (fun a => Icc 1 (n / a))).image (fun x => x.1 * x.2), w m :=
    (Finset.sum_image hinj).symm
  have hsubI : (A.sigma (fun a => Icc 1 (n / a))).image (fun x => x.1 * x.2) ⊆ Icc 1 n := by
    intro m hm
    rw [Finset.mem_image] at hm
    obtain ⟨⟨a, j⟩, hx, rfl⟩ := hm
    rw [Finset.mem_sigma] at hx
    obtain ⟨ha0, hj0⟩ := hx
    have ha : a ∈ A := ha0
    have hj : j ∈ Icc 1 (n / a) := hj0
    have ha1 := Finset.mem_Icc.mp (hsub ha)
    have hj' := Finset.mem_Icc.mp hj
    have hapos : 0 < a := ha1.1
    have hjn : j * a ≤ n := (Nat.le_div_iff_mul_le hapos).mp hj'.2
    have hj1 : 0 < j := hj'.1
    have hpos : 0 < a * j := Nat.mul_pos hapos hj1
    rw [Finset.mem_Icc]
    constructor
    · exact hpos
    · rw [Nat.mul_comm]; exact hjn
  rw [h1, h2]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubI (fun m _ _ => hw m)

-- @@L block_filter
theorem block_filter (lo hi M : ℕ) (hlo : 4 ≤ lo) (hle : lo ≤ hi) :
    ∑ j ∈ Icc 1 (M / 4), (if lo ≤ M / j ∧ M / j ≤ hi then (1 : ℝ) / j else 0) = bs lo hi M := by
  rw [← Finset.sum_filter]
  unfold bs
  congr 1
  ext j
  simp only [mem_filter, mem_Icc, mem_Ioc]
  rcases Nat.eq_zero_or_pos j with h0 | hj
  · subst h0; simp
  · have e1 : lo ≤ M / j ↔ lo * j ≤ M := Nat.le_div_iff_mul_le hj
    have e2 : j ≤ M / 4 ↔ j * 4 ≤ M := Nat.le_div_iff_mul_le (by omega)
    have e3 : j ≤ M / lo ↔ j * lo ≤ M := Nat.le_div_iff_mul_le (by omega)
    have e4 : M / (hi + 1) < j ↔ M < j * (hi + 1) := Nat.div_lt_iff_lt_mul (by omega)
    have e5 : M / j ≤ hi ↔ M < (hi + 1) * j := by
      rw [← Nat.lt_succ_iff]; exact Nat.div_lt_iff_lt_mul hj
    rw [e1, e2, e3, e4, e5]
    constructor
    · rintro ⟨⟨_, h4⟩, h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨hj, by nlinarith⟩, by nlinarith, by nlinarith⟩


-- @@L inner_sum
theorem inner_sum (L : List (ℕ × ℕ × ℕ)) (hL : ∀ b ∈ L, 4 ≤ b.1 ∧ b.1 ≤ b.2.1) (M : ℕ) :
    ∑ j ∈ Icc 1 (M / 4), ((Gt L (M / j) : ℕ) : ℝ) / j = cR L M := by
  induction L with
  | nil => simp [Gt, cR]
  | cons b L ih =>
    have hb : 4 ≤ b.1 ∧ b.1 ≤ b.2.1 := hL b (List.mem_cons_self ..)
    have hL' : ∀ c ∈ L, 4 ≤ c.1 ∧ c.1 ≤ c.2.1 := fun c hc => hL c (List.mem_cons_of_mem _ hc)
    have ih' := ih hL'
    have hG : ∀ k, Gt (b :: L) k = (if b.1 ≤ k ∧ k ≤ b.2.1 then b.2.2 else 0) + Gt L k := by
      intro k
      simp only [Gt, List.map_cons, List.sum_cons]
    have hc : cR (b :: L) M = (b.2.2 : ℝ) * bs b.1 b.2.1 M + cR L M := by
      simp only [cR, List.map_cons, List.sum_cons]
    have key : ∀ j ∈ Icc 1 (M / 4), ((Gt (b :: L) (M / j) : ℕ) : ℝ) / j
        = ((if b.1 ≤ M / j ∧ M / j ≤ b.2.1 then (b.2.2 : ℝ) else 0) * (1 / (j : ℝ)))
          + ((Gt L (M / j) : ℕ) : ℝ) / j := by
      intro j _
      rw [hG]
      split_ifs <;> push_cast <;> ring
    have hbf := block_filter b.1 b.2.1 M hb.1 hb.2
    have hsum : ∑ j ∈ Icc 1 (M / 4), ((if b.1 ≤ M / j ∧ M / j ≤ b.2.1 then (b.2.2 : ℝ) else 0)
        * (1 / (j : ℝ))) = (b.2.2 : ℝ) * bs b.1 b.2.1 M := by
      rw [← hbf, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      split_ifs <;> ring
    rw [hc, Finset.sum_congr rfl key, Finset.sum_add_distrib, hsum, ih']

-- @@L weight_sum
theorem weight_sum (L : List (ℕ × ℕ × ℕ)) (hL : ∀ b ∈ L, 4 ≤ b.1 ∧ b.1 ≤ b.2.1)
    (n a : ℕ) (ha : 1 ≤ a) :
    ∑ j ∈ Icc 1 (n / a), ((Gt L (4 * n / (a * j)) : ℕ) : ℝ) / ((a * j : ℕ) : ℝ)
      = (1 / (a : ℝ)) * cR L (4 * n / a) := by
  have h4 : 4 * n / a / 4 = n / a := by
    rw [Nat.div_div_eq_div_mul, Nat.mul_comm a 4, Nat.mul_div_mul_left _ _ (by norm_num : (0:ℕ) < 4)]
  have h := inner_sum L hL (4 * n / a)
  rw [h4] at h
  rw [← h, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 : (j : ℝ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hj).1
    exact_mod_cast (by omega : j ≠ 0)
  have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  rw [Nat.div_div_eq_div_mul]
  push_cast
  field_simp

-- B. Harmonic block sums against logarithms

-- @@L harm_lower
theorem harm_lower (a b : ℕ) (hab : a ≤ b) :
    Real.log (((b : ℝ) + 1) / ((a : ℝ) + 1)) ≤ ∑ j ∈ Ioc a b, (1 : ℝ) / j := by
  induction b, hab using Nat.le_induction with
  | base =>
    rw [Finset.Ioc_self, Finset.sum_empty, div_self (by positivity), Real.log_one]
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab]
    have hsplit : Real.log ((((b + 1 : ℕ) : ℝ) + 1) / ((a : ℝ) + 1)) =
        Real.log (((b : ℝ) + 1) / ((a : ℝ) + 1)) +
          Real.log ((((b + 1 : ℕ) : ℝ) + 1) / ((b : ℝ) + 1)) := by
      rw [← Real.log_mul (x := ((b : ℝ) + 1) / ((a : ℝ) + 1))
        (y := (((b + 1 : ℕ) : ℝ) + 1) / ((b : ℝ) + 1)) (by positivity) (by positivity)]
      congr 1
      have hb1 : (b : ℝ) + 1 ≠ 0 := by positivity
      have ha1 : (a : ℝ) + 1 ≠ 0 := by positivity
      push_cast
      field_simp
    have hstep : Real.log ((((b + 1 : ℕ) : ℝ) + 1) / ((b : ℝ) + 1)) ≤ 1 / ((b : ℝ) + 1) := by
      have h := Real.log_le_sub_one_of_pos
        (x := (((b + 1 : ℕ) : ℝ) + 1) / ((b : ℝ) + 1)) (by positivity)
      have e : (((b + 1 : ℕ) : ℝ) + 1) / ((b : ℝ) + 1) - 1 = 1 / ((b : ℝ) + 1) := by
        have hb1 : (b : ℝ) + 1 ≠ 0 := by positivity
        push_cast
        field_simp
        ring
      linarith
    have e2 : (1 : ℝ) / ((b + 1 : ℕ) : ℝ) = 1 / ((b : ℝ) + 1) := by push_cast; ring
    rw [hsplit]
    linarith

-- @@L harm_upper
theorem harm_upper (a b : ℕ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ∑ j ∈ Ioc a b, (1 : ℝ) / j ≤ Real.log ((b : ℝ) / (a : ℝ)) := by
  induction b, hab using Nat.le_induction with
  | base =>
    have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
    rw [Finset.Ioc_self, Finset.sum_empty, div_self ha0.ne', Real.log_one]
  | succ b hab ih =>
    rw [Finset.sum_Ioc_succ_top hab]
    have hb0 : (0 : ℝ) < b := Nat.cast_pos.mpr (by omega)
    have hsplit : Real.log (((b + 1 : ℕ) : ℝ) / (a : ℝ)) =
        Real.log ((b : ℝ) / (a : ℝ)) + Real.log (((b + 1 : ℕ) : ℝ) / (b : ℝ)) := by
      rw [← Real.log_mul (x := (b : ℝ) / (a : ℝ))
        (y := ((b + 1 : ℕ) : ℝ) / (b : ℝ)) (by positivity) (by positivity)]
      congr 1
      have ha0 : (0 : ℝ) < a := Nat.cast_pos.mpr (by omega)
      have hb1 : (b : ℝ) ≠ 0 := hb0.ne'
      have ha1 : (a : ℝ) ≠ 0 := ha0.ne'
      push_cast
      field_simp
    have hstep : 1 / (((b + 1 : ℕ)) : ℝ) ≤ Real.log (((b + 1 : ℕ) : ℝ) / (b : ℝ)) := by
      have h := Real.one_sub_inv_le_log_of_pos
        (x := ((b + 1 : ℕ) : ℝ) / (b : ℝ)) (by positivity)
      have e : 1 - (((b + 1 : ℕ) : ℝ) / (b : ℝ))⁻¹ = 1 / (((b + 1 : ℕ)) : ℝ) := by
        have hb1 : (b : ℝ) ≠ 0 := hb0.ne'
        rw [inv_div]
        push_cast
        field_simp
        ring
      linarith
    rw [hsplit]
    linarith

-- @@L bs_lower
theorem bs_lower (lo hi M : ℕ) (hlo : 1 ≤ lo) (hle : lo ≤ hi) (hM : 1 ≤ M) :
    Real.log (((hi : ℝ) + 1) / (lo : ℝ)) - ((hi : ℝ) + 1) / (M : ℝ) ≤ bs lo hi M := by
  unfold bs
  have hab : M / (hi + 1) ≤ M / lo := Nat.div_le_div_left (by omega) (by omega)
  have hh := harm_lower (M / (hi + 1)) (M / lo) hab
  refine le_trans ?_ hh
  have hm : (0:ℝ) < (M:ℝ) := by exact_mod_cast (show 0 < M by omega)
  have hx : (0:ℝ) < (lo:ℝ) := by exact_mod_cast (show 0 < lo by omega)
  have hy : (0:ℝ) < (hi:ℝ) + 1 := by positivity
  set A : ℕ := M / (hi + 1) with hA
  set B : ℕ := M / lo with hB
  have F1 : (M:ℝ) ≤ (lo:ℝ) * ((B:ℝ) + 1) := by
    have h1 : M < lo * (B + 1) := by
      have := Nat.div_add_mod M lo
      have := Nat.mod_lt M (show lo > 0 by omega)
      nlinarith
    exact_mod_cast h1.le
  have F2 : ((A:ℝ) + 1) * ((hi:ℝ) + 1) ≤ (M:ℝ) + ((hi:ℝ) + 1) := by
    have h2 : A * (hi + 1) ≤ M := Nat.div_mul_le_self M (hi + 1)
    have h3 : (A + 1) * (hi + 1) ≤ M + (hi + 1) := by nlinarith
    exact_mod_cast h3
  have hA1 : (0:ℝ) < (A:ℝ) + 1 := by positivity
  have hB1 : (0:ℝ) < (B:ℝ) + 1 := by positivity
  have hRle : ((hi:ℝ)+1)/(lo:ℝ) * ((M:ℝ)/((M:ℝ)+((hi:ℝ)+1))) ≤ ((B:ℝ)+1)/((A:ℝ)+1) := by
    rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hA1]
    nlinarith [mul_le_mul_of_nonneg_left F2 hm.le,
      mul_le_mul_of_nonneg_right F1 (show (0:ℝ) ≤ (M:ℝ) + ((hi:ℝ)+1) by positivity)]
  have hlog1 : Real.log (((hi:ℝ)+1)/(lo:ℝ) * ((M:ℝ)/((M:ℝ)+((hi:ℝ)+1))))
      = Real.log (((hi:ℝ)+1)/(lo:ℝ)) + Real.log ((M:ℝ)/((M:ℝ)+((hi:ℝ)+1))) :=
    Real.log_mul (by positivity) (by positivity)
  have hlog2 : Real.log ((M:ℝ)/((M:ℝ)+((hi:ℝ)+1)))
      = - Real.log (((M:ℝ)+((hi:ℝ)+1))/(M:ℝ)) := by
    rw [← Real.log_inv, inv_div]
  have hlog3 : Real.log (((M:ℝ)+((hi:ℝ)+1))/(M:ℝ)) ≤ ((hi:ℝ)+1)/(M:ℝ) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((M:ℝ)+((hi:ℝ)+1))/(M:ℝ) by positivity)
    have e : ((M:ℝ)+((hi:ℝ)+1))/(M:ℝ) - 1 = ((hi:ℝ)+1)/(M:ℝ) := by
      field_simp
      ring
    linarith
  have hmono := Real.log_le_log (by positivity) hRle
  linarith


-- @@L bs_upper
theorem bs_upper (lo hi M : ℕ) (hlo : 1 ≤ lo) (hle : lo ≤ hi) (hM : hi < M) :
    bs lo hi M ≤ Real.log (((hi : ℝ) + 1) / (lo : ℝ)) + (hi : ℝ) / ((M : ℝ) - (hi : ℝ)) := by
  unfold bs
  have hab : M / (hi + 1) ≤ M / lo := Nat.div_le_div_left (by omega) (by omega)
  have hA1 : 1 ≤ M / (hi + 1) := (Nat.le_div_iff_mul_le (by omega)).2 (by omega)
  have hh := harm_upper (M / (hi + 1)) (M / lo) hA1 hab
  refine le_trans hh ?_
  set A : ℕ := M / (hi + 1) with hA
  set B : ℕ := M / lo with hB
  have hx : (0:ℝ) < (lo:ℝ) := by exact_mod_cast (show 0 < lo by omega)
  have hAr : (1:ℝ) ≤ (A:ℝ) := by exact_mod_cast hA1
  have hApos : (0:ℝ) < (A:ℝ) := by linarith
  have hBpos : (0:ℝ) < (B:ℝ) := by
    have : 1 ≤ B := le_trans hA1 hab
    exact_mod_cast (show 0 < B by omega)
  have hhiR : (hi:ℝ) < (M:ℝ) := by exact_mod_cast hM
  have hm : (0:ℝ) < (M:ℝ) := by linarith [(Nat.cast_nonneg hi : (0:ℝ) ≤ hi)]
  have hmh : (0:ℝ) < (M:ℝ) - (hi:ℝ) := by linarith
  have F1 : (lo:ℝ) * (B:ℝ) ≤ (M:ℝ) := by
    have h1 : lo * B ≤ M := Nat.mul_div_le M lo
    exact_mod_cast h1
  have F2 : (M:ℝ) - (hi:ℝ) ≤ ((hi:ℝ) + 1) * (A:ℝ) := by
    have h1 : M ≤ (hi + 1) * A + hi := by
      have := Nat.div_add_mod M (hi + 1)
      have := Nat.mod_lt M (show hi + 1 > 0 by omega)
      nlinarith
    have h2 : (M:ℝ) ≤ ((hi:ℝ) + 1) * (A:ℝ) + (hi:ℝ) := by exact_mod_cast h1
    linarith
  have hBA : (B:ℝ) / (A:ℝ) ≤ ((hi:ℝ)+1)/(lo:ℝ) * ((M:ℝ)/((M:ℝ)-(hi:ℝ))) := by
    rw [div_mul_div_comm, div_le_div_iff₀ hApos (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right F1 hmh.le,
      mul_le_mul_of_nonneg_left F2 hm.le]
  have hlog1 : Real.log (((hi:ℝ)+1)/(lo:ℝ) * ((M:ℝ)/((M:ℝ)-(hi:ℝ))))
      = Real.log (((hi:ℝ)+1)/(lo:ℝ)) + Real.log ((M:ℝ)/((M:ℝ)-(hi:ℝ))) :=
    Real.log_mul (by positivity) (by positivity)
  have hlog2 : Real.log ((M:ℝ)/((M:ℝ)-(hi:ℝ))) ≤ (hi:ℝ)/((M:ℝ)-(hi:ℝ)) := by
    have h := Real.log_le_sub_one_of_pos (show (0:ℝ) < (M:ℝ)/((M:ℝ)-(hi:ℝ)) by positivity)
    have e : (M:ℝ)/((M:ℝ)-(hi:ℝ)) - 1 = (hi:ℝ)/((M:ℝ)-(hi:ℝ)) := by
      rw [div_sub_one hmh.ne']
      congr 1
      ring
    linarith
  have hmono := Real.log_le_log (div_pos hBpos hApos) hBA
  linarith

-- C. Rational bounds for logarithms

-- @@L log_lower
theorem log_lower (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    2 * z + 2 * z ^ 3 / 3 ≤ Real.log ((1 + z) / (1 - z)) := by
  have habs : |z| < 1 := by rw [abs_of_nonneg hz0]; exact hz1
  have hS := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hnn : ∀ i ∉ Finset.range 2,
      (0 : ℝ) ≤ (2 : ℝ) * (1 / (2 * (i : ℝ) + 1)) * z ^ (2 * i + 1) := fun i _ =>
    mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (pow_nonneg hz0 _)
  have h2 := sum_le_hasSum (Finset.range 2) hnn hS
  have hne1 : (1 + z) ≠ 0 := (by linarith : (0 : ℝ) < 1 + z).ne'
  have hne2 : (1 - z) ≠ 0 := (by linarith : (0 : ℝ) < 1 - z).ne'
  rw [Real.log_div hne1 hne2]
  norm_num [Finset.sum_range_succ] at h2
  linarith

-- @@L log_upper
theorem log_upper (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z < 1) :
    Real.log ((1 + z) / (1 - z)) ≤ 2 * z + 2 * z ^ 3 / (3 * (1 - z ^ 2)) := by
  have habs : |z| < 1 := by rw [abs_of_nonneg hz0]; exact hz1
  have hS := Real.hasSum_log_sub_log_of_abs_lt_one habs
  have hr0 : (0 : ℝ) ≤ z ^ 2 := by positivity
  have hr1 : z ^ 2 < 1 := by nlinarith
  have hG := (hasSum_geometric_of_lt_one hr0 hr1).mul_left ((2 / 3) * z)
  have hG2 := hG.add (hasSum_ite_eq (0 : ℕ) ((4 / 3) * z))
  have hle : ∀ k : ℕ, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * z ^ (2 * k + 1) ≤
      (2 / 3 * z) * (z ^ 2) ^ k + (if k = 0 then (4 / 3) * z else 0) := by
    intro k
    rcases k with _ | j
    · norm_num <;> linarith
    · have hp : 0 ≤ z * (z ^ 2) ^ (j + 1) := mul_nonneg hz0 (pow_nonneg (sq_nonneg z) _)
      have hc : (1 : ℝ) / (2 * ((j + 1 : ℕ) : ℝ) + 1) ≤ 1 / 3 := by
        apply one_div_le_one_div_of_le (by norm_num)
        push_cast
        have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
        linarith
      have hm := mul_le_mul_of_nonneg_right hc hp
      rw [if_neg (Nat.succ_ne_zero j), add_zero]
      have hpow : z ^ (2 * (j + 1) + 1) = z * (z ^ 2) ^ (j + 1) := by ring
      rw [hpow]
      nlinarith [hm]
  have key := hasSum_le hle hS hG2
  have hpos : (0 : ℝ) < 1 - z ^ 2 := by linarith
  have hne : (1 - z ^ 2) ≠ 0 := hpos.ne'
  have hval : (2 / 3 * z) * (1 - z ^ 2)⁻¹ + (4 / 3) * z
      = 2 * z + 2 * z ^ 3 / (3 * (1 - z ^ 2)) := by
    field_simp
    ring
  have hne1 : (1 + z) ≠ 0 := (by linarith : (0 : ℝ) < 1 + z).ne'
  have hne2 : (1 - z) ≠ 0 := (by linarith : (0 : ℝ) < 1 - z).ne'
  rw [Real.log_div hne1 hne2]
  linarith [key, hval]

-- @@L lowQ_le
theorem lowQ_le (lo hi : ℕ) (hlo : 1 ≤ lo) (hle : lo ≤ hi) :
    ((lowQ lo hi : ℚ) : ℝ) ≤ Real.log (((hi : ℝ) + 1) / (lo : ℝ)) := by
  have hlo' : (1 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hlo
  have hle' : (lo : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hle
  have hden : (0 : ℝ) < (hi : ℝ) + 1 + lo := by linarith
  have hne : (hi : ℝ) + 1 + lo ≠ 0 := hden.ne'
  have hlne : (lo : ℝ) ≠ 0 := by linarith
  have hz0 : (0 : ℝ) ≤ ((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo) :=
    div_nonneg (by linarith) hden.le
  have hz1 : ((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo) < 1 := by
    rw [div_lt_one hden]; linarith
  have hq : ((lowQ lo hi : ℚ) : ℝ) = 2 * (((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo))
      + 2 * (((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo)) ^ 3 / 3 := by
    simp only [lowQ, zq]; push_cast; ring
  have h1 : (1 : ℝ) - ((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo)
      = 2 * (lo : ℝ) / ((hi : ℝ) + 1 + lo) := by
    field_simp; ring
  have h2 : (1 : ℝ) + ((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo)
      = 2 * ((hi : ℝ) + 1) / ((hi : ℝ) + 1 + lo) := by
    field_simp; ring
  have hr : (1 + ((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo))
      / (1 - ((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo)) = ((hi : ℝ) + 1) / (lo : ℝ) := by
    rw [h1, h2]
    field_simp
  have key := log_lower (((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo)) hz0 hz1
  rw [hr] at key
  rw [hq]
  exact key

-- @@L le_upQ
theorem le_upQ (lo hi : ℕ) (hlo : 1 ≤ lo) (hle : lo ≤ hi) :
    Real.log (((hi : ℝ) + 1) / (lo : ℝ)) ≤ ((upQ lo hi : ℚ) : ℝ) := by
  have hlo' : (1 : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hlo
  have hle' : (lo : ℝ) ≤ (hi : ℝ) := by exact_mod_cast hle
  have hden : (0 : ℝ) < (hi : ℝ) + 1 + lo := by linarith
  have hne : (hi : ℝ) + 1 + lo ≠ 0 := hden.ne'
  have hlne : (lo : ℝ) ≠ 0 := by linarith
  have hz0 : (0 : ℝ) ≤ ((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo) :=
    div_nonneg (by linarith) hden.le
  have hz1 : ((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo) < 1 := by
    rw [div_lt_one hden]; linarith
  have hq : ((upQ lo hi : ℚ) : ℝ) = 2 * (((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo))
      + 2 * (((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo)) ^ 3
        / (3 * (1 - (((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo)) ^ 2)) := by
    simp only [upQ, zq]; push_cast; ring
  have h1 : (1 : ℝ) - ((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo)
      = 2 * (lo : ℝ) / ((hi : ℝ) + 1 + lo) := by
    field_simp; ring
  have h2 : (1 : ℝ) + ((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo)
      = 2 * ((hi : ℝ) + 1) / ((hi : ℝ) + 1 + lo) := by
    field_simp; ring
  have hr : (1 + ((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo))
      / (1 - ((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo)) = ((hi : ℝ) + 1) / (lo : ℝ) := by
    rw [h1, h2]
    field_simp
  have key := log_upper (((hi : ℝ) + 1 - lo) / ((hi : ℝ) + 1 + lo)) hz0 hz1
  rw [hr] at key
  rw [hq]
  exact key

-- T. The tail: large M

-- @@L tail_lower_gen
theorem tail_lower_gen (L : List (ℕ × ℕ × ℕ)) (hL : ∀ b ∈ L, 1 ≤ b.1 ∧ b.1 ≤ b.2.1)
    (M0 M : ℕ) (hM0 : 1 ≤ M0) (hM : M0 ≤ M) :
    (((L.map fun b => (b.2.2 : ℚ) * (lowQ b.1 b.2.1 - ((b.2.1 : ℚ) + 1) / (M0 : ℚ))).sum : ℚ) : ℝ)
      ≤ cR L M := by
  revert hL
  induction L with
  | nil =>
    intro _
    simp [cR]
  | cons b L ih =>
    intro hL
    obtain ⟨hb1, hb2⟩ := hL b (by simp)
    have hL' : ∀ c ∈ L, 1 ≤ c.1 ∧ c.1 ≤ c.2.1 := fun c hc => hL c (by simp [hc])
    have ih' := ih hL'
    have hg : (0 : ℝ) ≤ (b.2.2 : ℝ) := Nat.cast_nonneg _
    have hhi : (0 : ℝ) ≤ (b.2.1 : ℝ) := Nat.cast_nonneg _
    have hM0r : (1 : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hM0
    have hMr : (M0 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have h1 := lowQ_le b.1 b.2.1 hb1 hb2
    have h2 := bs_lower b.1 b.2.1 M hb1 hb2 (by omega)
    have h3 : ((b.2.1 : ℝ) + 1) / (M : ℝ) ≤ ((b.2.1 : ℝ) + 1) / (M0 : ℝ) := by
      apply div_le_div_of_nonneg_left <;> linarith
    have k : (((b.2.2 : ℚ) * (lowQ b.1 b.2.1 - ((b.2.1 : ℚ) + 1) / (M0 : ℚ)) : ℚ) : ℝ)
        ≤ (b.2.2 : ℝ) * bs b.1 b.2.1 M := by
      push_cast
      exact mul_le_mul_of_nonneg_left (by linarith) hg
    simp only [cR, List.map_cons, List.sum_cons, Rat.cast_add] at ih' ⊢
    linarith

-- @@L tail_upper_gen
theorem tail_upper_gen (L : List (ℕ × ℕ × ℕ)) (H : ℕ)
    (hL : ∀ b ∈ L, 1 ≤ b.1 ∧ b.1 ≤ b.2.1 ∧ b.2.1 ≤ H)
    (M1 M : ℕ) (hM1 : H < M1) (hM : M1 ≤ M) :
    cR L M ≤
      (((L.map fun b => (b.2.2 : ℚ) *
        (upQ b.1 b.2.1 + (b.2.1 : ℚ) / ((M1 : ℚ) - (H : ℚ)))).sum : ℚ) : ℝ) := by
  revert hL
  induction L with
  | nil =>
    intro _
    simp [cR]
  | cons b L ih =>
    intro hL
    obtain ⟨hb1, hb2, hb3⟩ := hL b (by simp)
    have hL' : ∀ c ∈ L, 1 ≤ c.1 ∧ c.1 ≤ c.2.1 ∧ c.2.1 ≤ H := fun c hc => hL c (by simp [hc])
    have ih' := ih hL'
    have hg : (0 : ℝ) ≤ (b.2.2 : ℝ) := Nat.cast_nonneg _
    have hhi : (0 : ℝ) ≤ (b.2.1 : ℝ) := Nat.cast_nonneg _
    have hHr : (b.2.1 : ℝ) ≤ (H : ℝ) := by exact_mod_cast hb3
    have hH1 : (H : ℝ) < (M1 : ℝ) := by exact_mod_cast hM1
    have hMr : (M1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have h1 := le_upQ b.1 b.2.1 hb1 hb2
    have h2 := bs_upper b.1 b.2.1 M hb1 hb2 (by omega)
    have h3 : (b.2.1 : ℝ) / ((M : ℝ) - (b.2.1 : ℝ)) ≤ (b.2.1 : ℝ) / ((M1 : ℝ) - (H : ℝ)) := by
      apply div_le_div_of_nonneg_left <;> linarith
    have k : (b.2.2 : ℝ) * bs b.1 b.2.1 M
        ≤ (((b.2.2 : ℚ) * (upQ b.1 b.2.1 + (b.2.1 : ℚ) / ((M1 : ℚ) - (H : ℚ))) : ℚ) : ℝ) := by
      push_cast
      exact mul_le_mul_of_nonneg_left (by linarith) hg
    simp only [cR, List.map_cons, List.sum_cons, Rat.cast_add] at ih' ⊢
    linarith

-- @@L num_lower
theorem num_lower :
    (10000000 : ℚ) ≤
      (blocks.map fun b => (b.2.2 : ℚ) *
        (lowQ b.1 b.2.1 - ((b.2.1 : ℚ) + 1) / ((5200 : ℕ) : ℚ))).sum := by
  decide +kernel


-- @@L num_upper
theorem num_upper :
    (blocks.map fun b => (b.2.2 : ℚ) *
        (upQ b.1 b.2.1 + (b.2.1 : ℚ) / (((690040 : ℕ) : ℚ) - ((235 : ℕ) : ℚ)))).sum
      < 10000000 * (1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  decide +kernel


-- F. The finite range

-- @@L hs_le
theorem hs_le (D a c : ℕ) :
    ((hs D a c : ℕ) : ℝ) ≤ (D : ℝ) * ∑ j ∈ Ioc a (a + c), (1 : ℝ) / j := by
  induction c with
  | zero => simp [hs]
  | succ c ih =>
    have e : a + (c + 1) = (a + c) + 1 := by omega
    have hh : hs D a (c + 1) = D / (a + c + 1) + hs D a c := rfl
    have hD : ((D / (a + c + 1) : ℕ) : ℝ) ≤ (D : ℝ) * (1 / ((a + c + 1 : ℕ) : ℝ)) := by
      rw [mul_one_div]
      exact Nat.cast_div_le
    rw [e, Finset.sum_Ioc_succ_top (by omega : a ≤ a + c), hh, Nat.cast_add, mul_add]
    linarith

-- @@L cFl_le
theorem cFl_le_aux1 (D g lo hi M : ℕ) (hlo : 1 ≤ lo) (hle : lo ≤ hi) :
    ((g * hs D (M / (hi + 1)) (M / lo - M / (hi + 1)) : ℕ) : ℝ)
      ≤ (D : ℝ) * ((g : ℝ) * bs lo hi M) := by
  have hab : M / (hi + 1) ≤ M / lo := Nat.div_le_div_left (by omega) (by omega)
  have hh := hs_le D (M / (hi + 1)) (M / lo - M / (hi + 1))
  have he : M / (hi + 1) + (M / lo - M / (hi + 1)) = M / lo := by omega
  rw [he] at hh
  rw [Nat.cast_mul]
  unfold bs
  have hg : (0 : ℝ) ≤ (g : ℝ) := Nat.cast_nonneg g
  calc (g : ℝ) * ((hs D (M / (hi + 1)) (M / lo - M / (hi + 1)) : ℕ) : ℝ)
      ≤ (g : ℝ) * ((D : ℝ) * ∑ j ∈ Ioc (M / (hi + 1)) (M / lo), (1 : ℝ) / j) :=
        mul_le_mul_of_nonneg_left hh hg
    _ = (D : ℝ) * ((g : ℝ) * ∑ j ∈ Ioc (M / (hi + 1)) (M / lo), (1 : ℝ) / j) := by ring

theorem cFl_le (D : ℕ) (L : List (ℕ × ℕ × ℕ)) (hL : ∀ b ∈ L, 1 ≤ b.1 ∧ b.1 ≤ b.2.1) (M : ℕ) :
    ((cFl D L M : ℕ) : ℝ) ≤ (D : ℝ) * cR L M := by
  induction L with
  | nil => simp [cFl, cR]
  | cons b L ih =>
    have hb := hL b (by simp)
    have ih' := ih (fun c hc => hL c (by simp [hc]))
    have h1 := cFl_le_aux1 D b.2.2 b.1 b.2.1 M hb.1 hb.2
    have e1 : cFl D (b :: L) M
        = b.2.2 * hs D (M / (b.2.1 + 1)) (M / b.1 - M / (b.2.1 + 1)) + cFl D L M := by
      simp [cFl]
    have e2 : cR (b :: L) M = (b.2.2 : ℝ) * bs b.1 b.2.1 M + cR L M := by
      simp [cR]
    rw [e1, e2, Nat.cast_add]
    linarith

-- @@L fast_table
/-- Prefix sum of D / j (natural division) over j in 1..x, as a plain Nat.rec. -/
def PR (D x : ℕ) : ℕ := Nat.rec 0 (fun n ih => D / (n + 1) + ih) x

theorem PR_eq (D x : ℕ) : PR D x = hs D 0 x := by
  induction x with
  | zero => rfl
  | succ x ih =>
    have e1 : hs D 0 (x + 1) = D / (x + 1) + hs D 0 x := by
      show D / (0 + x + 1) + hs D 0 x = _
      rw [Nat.zero_add]
    have e2 : PR D (x + 1) = D / (x + 1) + PR D x := rfl
    rw [e1, e2, ih]

theorem PR_mono (D : ℕ) {x y : ℕ} (h : x ≤ y) : PR D x ≤ PR D y := by
  induction y with
  | zero =>
    have : x = 0 := by omega
    subst this
    exact le_rfl
  | succ y ih =>
    rcases Nat.lt_or_ge x (y + 1) with h1 | h1
    · have h2 := ih (by omega)
      have e : PR D (y + 1) = D / (y + 1) + PR D y := rfl
      rw [e]
      exact le_trans h2 (Nat.le_add_left _ _)
    · have : x = y + 1 := by omega
      subst this
      exact le_rfl

theorem hs_add (D a c : ℕ) : hs D 0 (a + c) = hs D 0 a + hs D a c := by
  induction c with
  | zero => simp [hs]
  | succ c ih =>
    have e1 : hs D 0 (a + c + 1) = D / (a + c + 1) + hs D 0 (a + c) := by
      show D / (0 + (a + c) + 1) + hs D 0 (a + c) = _
      rw [Nat.zero_add]
    have e2 : hs D a (c + 1) = D / (a + c + 1) + hs D a c := rfl
    have e3 : a + (c + 1) = a + c + 1 := by omega
    rw [e3, e1, e2]
    omega

def cFr (D : ℕ) (L : List (ℕ × ℕ × ℕ)) (M : ℕ) : ℕ :=
  (L.map fun b => b.2.2 * (PR D (M / b.1) - PR D (M / (b.2.1 + 1)))).sum

theorem cFr_eq (D : ℕ) (L : List (ℕ × ℕ × ℕ)) (hL : ∀ b ∈ L, 1 ≤ b.1 ∧ b.1 ≤ b.2.1) (M : ℕ) :
    cFl D L M = cFr D L M := by
  induction L with
  | nil => simp [cFl, cFr]
  | cons b L ih =>
    have hb := hL b (by simp)
    have ih2 := ih (fun c hc => hL c (by simp [hc]))
    have h2 : M / (b.2.1 + 1) ≤ M / b.1 := Nat.div_le_div_left (by omega) (by omega)
    have e := hs_add D (M / (b.2.1 + 1)) (M / b.1 - M / (b.2.1 + 1))
    have e2 : M / (b.2.1 + 1) + (M / b.1 - M / (b.2.1 + 1)) = M / b.1 := by omega
    rw [e2] at e
    have p1 := PR_eq D (M / b.1)
    have p2 := PR_eq D (M / (b.2.1 + 1))
    have e3 : hs D (M / (b.2.1 + 1)) (M / b.1 - M / (b.2.1 + 1))
        = PR D (M / b.1) - PR D (M / (b.2.1 + 1)) := by omega
    simp only [cFl, cFr, List.map_cons, List.sum_cons] at ih2 ⊢
    rw [e3, ih2]

theorem blocks_ok : ∀ b ∈ blocks, 4 ≤ b.1 ∧ b.1 ≤ b.2.1 ∧ b.2.1 ≤ 235 := by
  decide

/-- Sum over the blocks of g * PR D (M / key b). -/
def sumK (D : ℕ) (L : List (ℕ × ℕ × ℕ)) (key : ℕ × ℕ × ℕ → ℕ) (M : ℕ) : ℕ :=
  (L.map fun b => b.2.2 * PR D (M / key b)).sum

/-- The new term of PR D (M / k) when M grows to M: D / (M / k) if k divides M, else 0. -/
def inc (D M k : ℕ) : ℕ := if M % k = 0 then D / (M / k) else 0

/-- The growth of sumK from M - 1 to M. -/
def upK (D : ℕ) (L : List (ℕ × ℕ × ℕ)) (key : ℕ × ℕ × ℕ → ℕ) (M : ℕ) : ℕ :=
  (L.map fun b => b.2.2 * inc D M (key b)).sum

theorem PR_succ_div (D M k : ℕ) : PR D ((M + 1) / k) = PR D (M / k) + inc D (M + 1) k := by
  unfold inc
  by_cases h : (M + 1) % k = 0
  · have hd : k ∣ M + 1 := Nat.dvd_of_mod_eq_zero h
    have e := Nat.succ_div_of_dvd hd
    have e2 : PR D (M / k + 1) = D / (M / k + 1) + PR D (M / k) := rfl
    rw [if_pos h, e, e2]
    omega
  · have hd : ¬ k ∣ M + 1 := fun hd => h (Nat.mod_eq_zero_of_dvd hd)
    rw [if_neg h, Nat.succ_div_of_not_dvd hd]
    rfl

theorem sumK_succ (D : ℕ) (L : List (ℕ × ℕ × ℕ)) (key : ℕ × ℕ × ℕ → ℕ) (M : ℕ) :
    sumK D L key (M + 1) = sumK D L key M + upK D L key (M + 1) := by
  induction L with
  | nil => simp [sumK, upK]
  | cons b L ih =>
    simp only [sumK, upK, List.map_cons, List.sum_cons] at ih ⊢
    rw [PR_succ_div, Nat.mul_add]
    omega

theorem sumK_zero (D : ℕ) (L : List (ℕ × ℕ × ℕ)) (key : ℕ × ℕ × ℕ → ℕ) :
    sumK D L key 0 = 0 := by
  induction L with
  | nil => simp [sumK]
  | cons b L ih =>
    simp only [sumK, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    simp [PR]

theorem cFr_add (D : ℕ) (L : List (ℕ × ℕ × ℕ)) (hL : ∀ b ∈ L, 1 ≤ b.1 ∧ b.1 ≤ b.2.1) (M : ℕ) :
    cFr D L M + sumK D L (fun b => b.2.1 + 1) M = sumK D L (fun b => b.1) M := by
  induction L with
  | nil => simp [cFr, sumK]
  | cons b L ih =>
    have hb := hL b (by simp)
    have ih2 := ih (fun c hc => hL c (by simp [hc]))
    have h2 : M / (b.2.1 + 1) ≤ M / b.1 := Nat.div_le_div_left (by omega) (by omega)
    have hle := PR_mono D h2
    have key : b.2.2 * (PR D (M / b.1) - PR D (M / (b.2.1 + 1)))
        + b.2.2 * PR D (M / (b.2.1 + 1)) = b.2.2 * PR D (M / b.1) := by
      rw [← Nat.mul_add, Nat.sub_add_cancel hle]
    simp only [cFr, sumK, List.map_cons, List.sum_cons] at ih2 ⊢
    omega

/-- Branch-free version of inc for D = 10^12, cheap in the kernel. -/
def incb (M k : ℕ) : ℕ := bif Nat.beq (M % k) 0 then 1000000000000 / (M / k) else 0

theorem incb_eq (M k : ℕ) : incb M k = inc 1000000000000 M k := by
  unfold incb inc
  cases hb : Nat.beq (M % k) 0
  · have h := Nat.ne_of_beq_eq_false hb
    rw [if_neg h]
    rfl
  · have h := Nat.eq_of_beq_eq_true hb
    rw [if_pos h]
    rfl

/-- The growth of the sum of g * PR D (M / lo), written out block by block. -/
def upA (M : ℕ) : ℕ :=
    10000300 * incb M 4 + (10571746 * incb M 5 + (10000300 * incb M 6 + (5963454 * incb M 8
     + (5000150 * incb M 9 + (4714428 * incb M 10 + (1666717 * incb M 12 + (1476235 * incb M 15
     + (994583 * incb M 16 + (1666717 * incb M 18 + (1012273 * incb M 24 + (897983 * incb M 25
     + (1219085 * incb M 27 + (463822 * incb M 40 + (545457 * incb M 42 + (156222 * incb M 48
     + (213367 * incb M 50 + (306732 * incb M 60 + (444347 * incb M 63 + (400390 * incb M 65
     + (452340 * incb M 66 + (33615 * incb M 84 + (185156 * incb M 88 + (216903 * incb M 90
     + (117382 * incb M 112 + (147458 * incb M 114 + (122612 * incb M 115 + (90686 * incb M 140
     + (115002 * incb M 141 + (61926 * incb M 142 + (95116 * incb M 144 + (75411 * incb M 145
     + (22365 * incb M 232 + (10207 * incb M 235)))))))))))))))))))))))))))))))))

/-- The growth of the sum of g * PR D (M / (hi + 1)), written out block by block. -/
def upB (M : ℕ) : ℕ :=
    10000300 * incb M 5 + (10571746 * incb M 6 + (10000300 * incb M 8 + (5963454 * incb M 9
     + (5000150 * incb M 10 + (4714428 * incb M 12 + (1666717 * incb M 15 + (1476235 * incb M 16
     + (994583 * incb M 18 + (1666717 * incb M 20 + (1012273 * incb M 25 + (897983 * incb M 27
     + (1219085 * incb M 28 + (463822 * incb M 42 + (545457 * incb M 44 + (156222 * incb M 50
     + (213367 * incb M 52 + (306732 * incb M 63 + (444347 * incb M 65 + (400390 * incb M 66
     + (452340 * incb M 68 + (33615 * incb M 85 + (185156 * incb M 90 + (216903 * incb M 92
     + (117382 * incb M 114 + (147458 * incb M 115 + (122612 * incb M 116 + (90686 * incb M 141
     + (115002 * incb M 142 + (61926 * incb M 144 + (95116 * incb M 145 + (75411 * incb M 148
     + (22365 * incb M 235 + (10207 * incb M 236)))))))))))))))))))))))))))))))))

theorem upA_eq (M : ℕ) : upA M = upK 1000000000000 blocks (fun b => b.1) M := by
  unfold upA upK blocks
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, incb_eq, Nat.add_zero]

theorem upB_eq (M : ℕ) : upB M = upK 1000000000000 blocks (fun b => b.2.1 + 1) M := by
  unfold upB upK blocks
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, incb_eq, Nat.add_zero]

/-- Ascending scan: the state holds the two sums at m; checks M = m + 1, m + 2, ... -/
def loopG (n m A B : ℕ) : Bool :=
  Nat.rec (fun _ _ _ => true)
    (fun _ ih m A B =>
      (Nat.ble (m + 1) 3 ||
        Nat.ble (10000000 * 1000000000000 + (B + upB (m + 1))) (A + upA (m + 1))) &&
      ih (m + 1) (A + upA (m + 1)) (B + upB (m + 1))) n m A B

theorem loopG_spec (n : ℕ) : ∀ m A B, loopG n m A B = true →
    A = sumK 1000000000000 blocks (fun b => b.1) m →
    B = sumK 1000000000000 blocks (fun b => b.2.1 + 1) m →
    ∀ j, j < n → (m + 1 + j < 4 ∨
      10000000 * 1000000000000 + sumK 1000000000000 blocks (fun b => b.2.1 + 1) (m + 1 + j)
        ≤ sumK 1000000000000 blocks (fun b => b.1) (m + 1 + j)) := by
  induction n with
  | zero => intro m A B _ _ _ j hj; omega
  | succ n ih =>
    intro m A B h hA hB j hj
    have h1 : ((Nat.ble (m + 1) 3 ||
        Nat.ble (10000000 * 1000000000000 + (B + upB (m + 1))) (A + upA (m + 1))) &&
      (loopG n (m + 1) (A + upA (m + 1)) (B + upB (m + 1)))) = true := h
    rw [Bool.and_eq_true] at h1
    have hA' : A + upA (m + 1) = sumK 1000000000000 blocks (fun b => b.1) (m + 1) := by
      rw [sumK_succ, hA, upA_eq]
    have hB' : B + upB (m + 1) = sumK 1000000000000 blocks (fun b => b.2.1 + 1) (m + 1) := by
      rw [sumK_succ, hB, upB_eq]
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · subst hj0
      have h2 := h1.1
      rw [Bool.or_eq_true] at h2
      rw [hA', hB'] at h2
      rcases h2 with h2 | h2
      · left; have := Nat.le_of_ble_eq_true h2; omega
      · right; have := Nat.le_of_ble_eq_true h2; simpa using this
    · have h3 := ih (m + 1) _ _ h1.2 hA' hB' (j - 1) (by omega)
      have e : m + 1 + 1 + (j - 1) = m + 1 + j := by omega
      rw [e] at h3
      exact h3

-- @@L finite_check
theorem finite_check_aux : loopG 5200 0 0 0 = true := by
  decide +kernel

theorem finite_check (M : ℕ) (h4 : 4 ≤ M) (hM : M ≤ 5200) :
    10000000 * 1000000000000 ≤ cFl 1000000000000 blocks M := by
  have h := loopG_spec 5200 0 0 0 finite_check_aux
    (sumK_zero _ _ _).symm (sumK_zero _ _ _).symm (M - 1) (by omega)
  have e : 0 + 1 + (M - 1) = M := by omega
  rw [e] at h
  have hL : ∀ b ∈ blocks, 1 ≤ b.1 ∧ b.1 ≤ b.2.1 := fun b hb =>
    ⟨by have := (blocks_ok b hb).1; omega, (blocks_ok b hb).2.1⟩
  have h2 := cFr_add 1000000000000 blocks hL M
  rw [cFr_eq 1000000000000 blocks hL M]
  rcases h with h | h
  · omega
  · omega

-- Assembly (proved)

theorem c_ge (M : ℕ) (h4 : 4 ≤ M) : (10000000 : ℝ) ≤ cR blocks M := by
  have hL : ∀ b ∈ blocks, 1 ≤ b.1 ∧ b.1 ≤ b.2.1 := fun b hb =>
    ⟨le_trans (by norm_num) (blocks_ok b hb).1, (blocks_ok b hb).2.1⟩
  rcases le_or_gt M 5200 with h | h
  · have h1 := finite_check M h4 h
    have h2 := cFl_le 1000000000000 blocks hL M
    have h3 : ((10000000 * 1000000000000 : ℕ) : ℝ) ≤ ((cFl 1000000000000 blocks M : ℕ) : ℝ) :=
      Nat.cast_le.mpr h1
    generalize ((cFl 1000000000000 blocks M : ℕ) : ℝ) = c at h2 h3
    generalize cR blocks M = x at h2
    norm_num at h2 h3
    linarith
  · have h1 := tail_lower_gen blocks hL 5200 M (by norm_num) h.le
    have h2 : ((10000000 : ℚ) : ℝ) ≤
        (((blocks.map fun b => (b.2.2 : ℚ) *
          (lowQ b.1 b.2.1 - ((b.2.1 : ℚ) + 1) / ((5200 : ℕ) : ℚ))).sum : ℚ) : ℝ) := by
      exact_mod_cast num_lower
    have h3 : ((10000000 : ℚ) : ℝ) = (10000000 : ℝ) := by norm_num
    linarith

theorem c_top (n : ℕ) (hn : 172509 < n) :
    cR blocks (4 * n) < 10000000 * (1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by
  have hL : ∀ b ∈ blocks, 1 ≤ b.1 ∧ b.1 ≤ b.2.1 ∧ b.2.1 ≤ 235 := fun b hb =>
    ⟨le_trans (by norm_num) (blocks_ok b hb).1, (blocks_ok b hb).2⟩
  have h1 := tail_upper_gen blocks 235 hL 690040 (4 * n) (by norm_num) (by omega)
  have h2 : ((((blocks.map fun b => (b.2.2 : ℚ) *
        (upQ b.1 b.2.1 + (b.2.1 : ℚ) / (((690040 : ℕ) : ℚ) - ((235 : ℕ) : ℚ)))).sum : ℚ)) : ℝ)
      < (((10000000 * (1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) : ℚ)) : ℝ) := by
    exact_mod_cast num_upper
  have h3 : (((10000000 * (1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) : ℚ)) : ℝ)
      = 10000000 * (1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11) := by norm_num
  linarith

theorem main (n : ℕ) (hn : 172509 < n) (A : Finset ℕ) (hsub : A ⊆ Icc 1 n)
    (hlcm : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → n < Nat.lcm a b) :
    ∑ a ∈ A, (1 : ℝ) / a < 1 / 3 + 1 / 4 + 1 / 5 + 1 / 7 + 1 / 11 := by
  have hL : ∀ b ∈ blocks, 4 ≤ b.1 ∧ b.1 ≤ b.2.1 := fun b hb =>
    ⟨(blocks_ok b hb).1, (blocks_ok b hb).2.1⟩
  have hpack := packing n A (fun m => ((Gt blocks (4 * n / m) : ℕ) : ℝ) / ((m : ℕ) : ℝ)) hsub hlcm
    (fun m => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hkey : ∀ a ∈ A, 10000000 * ((1 : ℝ) / a) ≤
      ∑ j ∈ Icc 1 (n / a), ((Gt blocks (4 * n / (a * j)) : ℕ) : ℝ) / ((a * j : ℕ) : ℝ) := by
    intro a ha
    have ha1 : 1 ≤ a ∧ a ≤ n := Finset.mem_Icc.mp (hsub ha)
    have hws := weight_sum blocks hL n a ha1.1
    have hM : 4 ≤ 4 * n / a := by
      rw [Nat.le_div_iff_mul_le (by omega)]
      omega
    have hc := c_ge (4 * n / a) hM
    have hpos : (0 : ℝ) ≤ 1 / (a : ℝ) := by positivity
    calc 10000000 * ((1 : ℝ) / a) = (1 / (a : ℝ)) * 10000000 := by ring
      _ ≤ (1 / (a : ℝ)) * cR blocks (4 * n / a) := mul_le_mul_of_nonneg_left hc hpos
      _ = _ := hws.symm
  have htot : ∑ m ∈ Icc 1 n, ((Gt blocks (4 * n / m) : ℕ) : ℝ) / ((m : ℕ) : ℝ)
      = cR blocks (4 * n) := by
    have hws := weight_sum blocks hL n 1 le_rfl
    simp only [Nat.div_one, one_mul, Nat.cast_one, div_one] at hws
    exact hws
  have h1 : 10000000 * ∑ a ∈ A, (1 : ℝ) / a ≤ cR blocks (4 * n) := by
    rw [Finset.mul_sum]
    calc ∑ a ∈ A, 10000000 * ((1 : ℝ) / a)
        ≤ ∑ a ∈ A, ∑ j ∈ Icc 1 (n / a),
            ((Gt blocks (4 * n / (a * j)) : ℕ) : ℝ) / ((a * j : ℕ) : ℝ) :=
          Finset.sum_le_sum hkey
      _ ≤ ∑ m ∈ Icc 1 n, ((Gt blocks (4 * n / m) : ℕ) : ℝ) / ((m : ℕ) : ℝ) := hpack
      _ = cR blocks (4 * n) := htot
  have h2 := c_top n hn
  linarith

end OMA.E542

-- @@L END
theorem OMA.solution : type_of% @Erdos542.erdos_542.variants.chen := by
  intro n hn A hA
  exact OMA.E542.main n hn A hA.1 (fun a ha b hb hab => hA.2 ha hb hab)
