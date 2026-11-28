import OMAStatements.S_oeis_a386830
import Mathlib

namespace OMA.T386830

open Finset OMA.S_oeis_a386830

/-- Shifting a factorial. -/
lemma fsh (E : ℕ) : ∀ j : ℕ, ((E + j).factorial : ℚ)
    = (∏ i ∈ Finset.range j, ((E : ℚ) + (i : ℚ) + 1)) * (E.factorial : ℚ)
  | 0 => by simp
  | j + 1 => by
    rw [show E + (j + 1) = (E + j) + 1 from rfl, Nat.factorial_succ, Finset.prod_range_succ]
    push_cast
    rw [fsh E j]
    ring

/-- The summand in factorial form, as a function of k and t = n - k. -/
noncomputable def Φ (k t : ℕ) : ℚ :=
  (3 : ℚ) ^ k * (2 : ℚ) ^ t * ((3 * k + 3 * t + 1).factorial : ℚ)
    / (((k).factorial : ℚ) * ((2 * k + 3 * t + 1).factorial : ℚ)) * ((2 * k + 3 * t).factorial : ℚ)
    / (((t).factorial : ℚ) * ((2 * k + 2 * t).factorial : ℚ))

/-- The summand of the sequence. -/
def F (n k : ℕ) : ℤ :=
  (3 : ℤ) ^ k * (2 : ℤ) ^ (n - k) * ((3 * n + 1).choose k : ℤ) * ((3 * n - k).choose (n - k) : ℤ)

lemma a_eq (n : ℕ) : a n = ∑ k ∈ Finset.range (n + 1), F n k := rfl

lemma F_eq (k t : ℕ) : (F (k + t) k : ℚ) = Φ k t := by
  have h1 : ((3 * (k + t) + 1).choose k : ℚ)
      = ((3 * k + 3 * t + 1).factorial : ℚ) / ((k.factorial : ℚ) * ((2 * k + 3 * t + 1).factorial : ℚ)) := by
    rw [Nat.cast_choose ℚ (by omega : k ≤ 3 * (k + t) + 1)]
    rw [show 3 * (k + t) + 1 - k = 2 * k + 3 * t + 1 from by omega,
      show 3 * (k + t) + 1 = 3 * k + 3 * t + 1 from by ring]
  have h2 : ((3 * (k + t) - k).choose (k + t - k) : ℚ)
      = ((2 * k + 3 * t).factorial : ℚ) / ((t.factorial : ℚ) * ((2 * k + 2 * t).factorial : ℚ)) := by
    rw [Nat.add_sub_cancel_left, show 3 * (k + t) - k = 2 * k + 3 * t from by omega]
    rw [Nat.cast_choose ℚ (by omega : t ≤ 2 * k + 3 * t)]
    rw [show 2 * k + 3 * t - t = 2 * k + 2 * t from by omega]
  unfold F Φ
  push_cast
  rw [h1, h2, Nat.add_sub_cancel_left]
  ring

/-- The certificate, as a rational function of x = m and y = k (with n = m + 2). -/
noncomputable def Rc (x y : ℚ) : ℚ :=
  (-17496 * x ^ 8 * y + 11664 * x ^ 7 * y ^ 2 - 163296 * x ^ 7 * y + 9720 * x ^ 6 * y ^ 3 + 54432 *
      x ^ 6 * y ^ 2 - 607014 * x ^ 6 * y - 12960 * x ^ 5 * y ^ 4 + 120528 * x ^ 5 * y ^ 3 -
      37584 * x ^ 5 * y ^ 2 - 1098198 * x ^ 5 * y + 5400 * x ^ 4 * y ^ 5 - 100224 * x ^ 4 * y ^
      4 + 542322 * x ^ 4 * y ^ 3 - 695034 * x ^ 4 * y ^ 2 - 837378 * x ^ 4 * y - 1008 * x ^ 3 *
      y ^ 6 + 29952 * x ^ 3 * y ^ 5 - 293904 * x ^ 3 * y ^ 4 + 1181556 * x ^ 3 * y ^ 3 - 1724940
      * x ^ 3 * y ^ 2 + 214326 * x ^ 3 * y + 72 * x ^ 2 * y ^ 7 - 3744 * x ^ 2 * y ^ 6 + 58686 *
      x ^ 2 * y ^ 5 - 404724 * x ^ 2 * y ^ 4 + 1328760 * x ^ 2 * y ^ 3 - 1923402 * x ^ 2 * y ^ 2
      + 838104 * x ^ 2 * y + 144 * x * y ^ 7 - 4192 * x * y ^ 6 + 46722 * x * y ^ 5 - 255604 * x
      * y ^ 4 + 723834 * x * y ^ 3 - 1007368 * x * y ^ 2 + 532248 * x * y + 54 * y ^ 7 - 1266 *
      y ^ 6 + 11786 * y ^ 5 - 55750 * y ^ 4 + 142816 * y ^ 3 - 192584 * y ^ 2 + 108384 * y)
    / ((3 * x + 5) * (3 * x + 7) * (3 * x - y + 6) * (3 * x - y + 5) * (3 * x - y + 4) * (3 * x - y + 3) * (3 * x - y + 2))

/-- The telescoping term. -/
noncomputable def Gf (m k : ℕ) : ℚ := Rc m k * Φ k (m + 2 - k)

lemma RcA (k t : ℕ) : Rc ((k : ℚ) + (t : ℚ)) ((k : ℚ) + 1)
    = (-4608 * (k : ℚ) ^ 9 - 46080 * (k : ℚ) ^ 8 * (t : ℚ) - 57600 * (k : ℚ) ^ 8 - 199296 * (k : ℚ) ^ 7
      * (t : ℚ) ^ 2 - 502272 * (k : ℚ) ^ 7 * (t : ℚ) - 303616 * (k : ℚ) ^ 7 - 486144 * (k : ℚ) ^
      6 * (t : ℚ) ^ 3 - 1859328 * (k : ℚ) ^ 6 * (t : ℚ) ^ 2 - 2267968 * (k : ℚ) ^ 6 * (t : ℚ) -
      877824 * (k : ℚ) ^ 6 - 730080 * (k : ℚ) ^ 5 * (t : ℚ) ^ 4 - 3788928 * (k : ℚ) ^ 5 * (t :
      ℚ) ^ 3 - 7024224 * (k : ℚ) ^ 5 * (t : ℚ) ^ 2 - 5486304 * (k : ℚ) ^ 5 * (t : ℚ) - 1512032 *
      (k : ℚ) ^ 5 - 689472 * (k : ℚ) ^ 4 * (t : ℚ) ^ 5 - 4599504 * (k : ℚ) ^ 4 * (t : ℚ) ^ 4 -
      11602080 * (k : ℚ) ^ 4 * (t : ℚ) ^ 3 - 13780656 * (k : ℚ) ^ 4 * (t : ℚ) ^ 2 - 7647568 * (k
      : ℚ) ^ 4 * (t : ℚ) - 1565040 * (k : ℚ) ^ 4 - 398520 * (k : ℚ) ^ 3 * (t : ℚ) ^ 6 - 3348864
      * (k : ℚ) ^ 3 * (t : ℚ) ^ 5 - 10915344 * (k : ℚ) ^ 3 * (t : ℚ) ^ 4 - 17669808 * (k : ℚ) ^
      3 * (t : ℚ) ^ 3 - 14881920 * (k : ℚ) ^ 3 * (t : ℚ) ^ 2 - 6084696 * (k : ℚ) ^ 3 * (t : ℚ) -
      911744 * (k : ℚ) ^ 3 - 128304 * (k : ℚ) ^ 2 * (t : ℚ) ^ 7 - 1386072 * (k : ℚ) ^ 2 * (t :
      ℚ) ^ 6 - 5751972 * (k : ℚ) ^ 2 * (t : ℚ) ^ 5 - 12076452 * (k : ℚ) ^ 2 * (t : ℚ) ^ 4 -
      13838940 * (k : ℚ) ^ 2 * (t : ℚ) ^ 3 - 8511108 * (k : ℚ) ^ 2 * (t : ℚ) ^ 2 - 2483872 * (k
      : ℚ) ^ 2 * (t : ℚ) - 228816 * (k : ℚ) ^ 2 - 17496 * (k : ℚ) * (t : ℚ) ^ 8 - 279936 * (k :
      ℚ) * (t : ℚ) ^ 7 - 1530414 * (k : ℚ) * (t : ℚ) ^ 6 - 4120794 * (k : ℚ) * (t : ℚ) ^ 5 -
      6115446 * (k : ℚ) * (t : ℚ) ^ 4 - 5062446 * (k : ℚ) * (t : ℚ) ^ 3 - 2151900 * (k : ℚ) * (t
      : ℚ) ^ 2 - 336432 * (k : ℚ) * (t : ℚ) + 16160 * (k : ℚ) - 17496 * (t : ℚ) ^ 8 - 151632 *
      (t : ℚ) ^ 7 - 542862 * (t : ℚ) ^ 6 - 1028214 * (t : ℚ) ^ 5 - 1084914 * (t : ℚ) ^ 4 -
      594018 * (t : ℚ) ^ 3 - 106248 * (t : ℚ) ^ 2 + 35784 * (t : ℚ) + 13440)
      / ((3 * (k : ℚ) + 3 * (t : ℚ) + 5) * (3 * (k : ℚ) + 3 * (t : ℚ) + 7) * (2 * (k : ℚ) + 3 * (t : ℚ) + 5) * (2 * (k : ℚ) + 3 * (t : ℚ) + 4) * (2 * (k : ℚ) + 3 * (t : ℚ) + 3) * (2 * (k : ℚ) + 3 * (t : ℚ) + 2) * (2 * (k : ℚ) + 3 * (t : ℚ) + 1)) := by
  have e : ((3 * ((k : ℚ) + (t : ℚ)) + 5) * (3 * ((k : ℚ) + (t : ℚ)) + 7) * (3 * ((k : ℚ) + (t : ℚ)) - ((k : ℚ) + 1) + 6) * (3 * ((k : ℚ) + (t : ℚ)) - ((k : ℚ) + 1) + 5) * (3 * ((k : ℚ) + (t : ℚ)) - ((k : ℚ) + 1) + 4) * (3 * ((k : ℚ) + (t : ℚ)) - ((k : ℚ) + 1) + 3) * (3 * ((k : ℚ) + (t : ℚ)) - ((k : ℚ) + 1) + 2) : ℚ) = (3 * (k : ℚ) + 3 * (t : ℚ) + 5) * (3 * (k : ℚ) + 3 * (t : ℚ) + 7) * (2 * (k : ℚ) + 3 * (t : ℚ) + 5) * (2 * (k : ℚ) + 3 * (t : ℚ) + 4) * (2 * (k : ℚ) + 3 * (t : ℚ) + 3) * (2 * (k : ℚ) + 3 * (t : ℚ) + 2) * (2 * (k : ℚ) + 3 * (t : ℚ) + 1) := by ring
  have hpos : ((3 * (k : ℚ) + 3 * (t : ℚ) + 5) * (3 * (k : ℚ) + 3 * (t : ℚ) + 7) * (2 * (k : ℚ) + 3 * (t : ℚ) + 5) * (2 * (k : ℚ) + 3 * (t : ℚ) + 4) * (2 * (k : ℚ) + 3 * (t : ℚ) + 3) * (2 * (k : ℚ) + 3 * (t : ℚ) + 2) * (2 * (k : ℚ) + 3 * (t : ℚ) + 1) : ℚ) ≠ 0 := by positivity
  have horig : ((3 * ((k : ℚ) + (t : ℚ)) + 5) * (3 * ((k : ℚ) + (t : ℚ)) + 7) * (3 * ((k : ℚ) + (t : ℚ)) - ((k : ℚ) + 1) + 6) * (3 * ((k : ℚ) + (t : ℚ)) - ((k : ℚ) + 1) + 5) * (3 * ((k : ℚ) + (t : ℚ)) - ((k : ℚ) + 1) + 4) * (3 * ((k : ℚ) + (t : ℚ)) - ((k : ℚ) + 1) + 3) * (3 * ((k : ℚ) + (t : ℚ)) - ((k : ℚ) + 1) + 2) : ℚ) ≠ 0 := by
    rw [e]
    exact hpos
  unfold Rc
  rw [div_eq_div_iff horig hpos]
  ring

lemma RcB (k t : ℕ) : Rc ((k : ℚ) + (t : ℚ)) (k : ℚ)
    = (-4608 * (k : ℚ) ^ 9 - 46080 * (k : ℚ) ^ 8 * (t : ℚ) - 62208 * (k : ℚ) ^ 8 - 199296 * (k : ℚ) ^ 7
      * (t : ℚ) ^ 2 - 532224 * (k : ℚ) ^ 7 * (t : ℚ) - 341632 * (k : ℚ) ^ 7 - 486144 * (k : ℚ) ^
      6 * (t : ℚ) ^ 3 - 1922688 * (k : ℚ) ^ 6 * (t : ℚ) ^ 2 - 2429248 * (k : ℚ) ^ 6 * (t : ℚ) -
      970944 * (k : ℚ) ^ 6 - 730080 * (k : ℚ) ^ 5 * (t : ℚ) ^ 4 - 3792384 * (k : ℚ) ^ 5 * (t :
      ℚ) ^ 3 - 7050144 * (k : ℚ) ^ 5 * (t : ℚ) ^ 2 - 5489184 * (k : ℚ) ^ 5 * (t : ℚ) - 1477376 *
      (k : ℚ) ^ 5 - 689472 * (k : ℚ) ^ 4 * (t : ℚ) ^ 5 - 4396464 * (k : ℚ) ^ 4 * (t : ℚ) ^ 4 -
      10640736 * (k : ℚ) ^ 4 * (t : ℚ) ^ 3 - 12012240 * (k : ℚ) ^ 4 * (t : ℚ) ^ 2 - 6122416 * (k
      : ℚ) ^ 4 * (t : ℚ) - 1040992 * (k : ℚ) ^ 4 - 398520 * (k : ℚ) ^ 3 * (t : ℚ) ^ 6 - 2982096
      * (k : ℚ) ^ 3 * (t : ℚ) ^ 5 - 8750808 * (k : ℚ) ^ 3 * (t : ℚ) ^ 4 - 12580560 * (k : ℚ) ^ 3
      * (t : ℚ) ^ 3 - 8870328 * (k : ℚ) ^ 3 * (t : ℚ) ^ 2 - 2479992 * (k : ℚ) ^ 3 * (t : ℚ) -
      26448 * (k : ℚ) ^ 3 - 128304 * (k : ℚ) ^ 2 * (t : ℚ) ^ 7 - 1088640 * (k : ℚ) ^ 2 * (t : ℚ)
      ^ 6 - 3679668 * (k : ℚ) ^ 2 * (t : ℚ) ^ 5 - 6186024 * (k : ℚ) ^ 2 * (t : ℚ) ^ 4 - 5074452
      * (k : ℚ) ^ 2 * (t : ℚ) ^ 3 - 1280424 * (k : ℚ) ^ 2 * (t : ℚ) ^ 2 + 668840 * (k : ℚ) ^ 2 *
      (t : ℚ) + 339664 * (k : ℚ) ^ 2 - 17496 * (k : ℚ) * (t : ℚ) ^ 8 - 163296 * (k : ℚ) * (t :
      ℚ) ^ 7 - 607014 * (k : ℚ) * (t : ℚ) ^ 6 - 1098198 * (k : ℚ) * (t : ℚ) ^ 5 - 837378 * (k :
      ℚ) * (t : ℚ) ^ 4 + 214326 * (k : ℚ) * (t : ℚ) ^ 3 + 838104 * (k : ℚ) * (t : ℚ) ^ 2 +
      532248 * (k : ℚ) * (t : ℚ) + 108384 * (k : ℚ))
      / ((3 * (k : ℚ) + 3 * (t : ℚ) + 5) * (3 * (k : ℚ) + 3 * (t : ℚ) + 7) * (2 * (k : ℚ) + 3 * (t : ℚ) + 6) * (2 * (k : ℚ) + 3 * (t : ℚ) + 5) * (2 * (k : ℚ) + 3 * (t : ℚ) + 4) * (2 * (k : ℚ) + 3 * (t : ℚ) + 3) * (2 * (k : ℚ) + 3 * (t : ℚ) + 2)) := by
  have e : ((3 * ((k : ℚ) + (t : ℚ)) + 5) * (3 * ((k : ℚ) + (t : ℚ)) + 7) * (3 * ((k : ℚ) + (t : ℚ)) - (k : ℚ) + 6) * (3 * ((k : ℚ) + (t : ℚ)) - (k : ℚ) + 5) * (3 * ((k : ℚ) + (t : ℚ)) - (k : ℚ) + 4) * (3 * ((k : ℚ) + (t : ℚ)) - (k : ℚ) + 3) * (3 * ((k : ℚ) + (t : ℚ)) - (k : ℚ) + 2) : ℚ) = (3 * (k : ℚ) + 3 * (t : ℚ) + 5) * (3 * (k : ℚ) + 3 * (t : ℚ) + 7) * (2 * (k : ℚ) + 3 * (t : ℚ) + 6) * (2 * (k : ℚ) + 3 * (t : ℚ) + 5) * (2 * (k : ℚ) + 3 * (t : ℚ) + 4) * (2 * (k : ℚ) + 3 * (t : ℚ) + 3) * (2 * (k : ℚ) + 3 * (t : ℚ) + 2) := by ring
  have hpos : ((3 * (k : ℚ) + 3 * (t : ℚ) + 5) * (3 * (k : ℚ) + 3 * (t : ℚ) + 7) * (2 * (k : ℚ) + 3 * (t : ℚ) + 6) * (2 * (k : ℚ) + 3 * (t : ℚ) + 5) * (2 * (k : ℚ) + 3 * (t : ℚ) + 4) * (2 * (k : ℚ) + 3 * (t : ℚ) + 3) * (2 * (k : ℚ) + 3 * (t : ℚ) + 2) : ℚ) ≠ 0 := by positivity
  have horig : ((3 * ((k : ℚ) + (t : ℚ)) + 5) * (3 * ((k : ℚ) + (t : ℚ)) + 7) * (3 * ((k : ℚ) + (t : ℚ)) - (k : ℚ) + 6) * (3 * ((k : ℚ) + (t : ℚ)) - (k : ℚ) + 5) * (3 * ((k : ℚ) + (t : ℚ)) - (k : ℚ) + 4) * (3 * ((k : ℚ) + (t : ℚ)) - (k : ℚ) + 3) * (3 * ((k : ℚ) + (t : ℚ)) - (k : ℚ) + 2) : ℚ) ≠ 0 := by
    rw [e]
    exact hpos
  unfold Rc
  rw [div_eq_div_iff horig hpos]
  ring

lemma interior_phi0 (k t : ℕ) : Φ (k) (t)
    = (3 : ℚ) ^ (k) * (2 : ℚ) ^ (t) * ((3 * k + 3 * t + 1).factorial : ℚ)
      / (((k).factorial : ℚ) * ((2 * k + 3 * t + 1).factorial : ℚ)) * ((2 * k + 3 * t).factorial : ℚ)
      / (((t).factorial : ℚ) * ((2 * k + 2 * t).factorial : ℚ)) := by
  unfold Φ
  rfl

lemma interior_phi1 (k t : ℕ) : Φ (k) (t + 1)
    = (3 : ℚ) ^ (k) * (2 : ℚ) ^ (t + 1) * ((3 * k + 3 * t + 1 + 3).factorial : ℚ)
      / (((k).factorial : ℚ) * ((2 * k + 3 * t + 4).factorial : ℚ)) * ((2 * k + 3 * t + 3).factorial : ℚ)
      / (((t + 1).factorial : ℚ) * ((2 * k + 2 * t + 2).factorial : ℚ)) := by
  unfold Φ
  have e0 : 3 * k + 3 * (t + 1) + 1 = 3 * k + 3 * t + 1 + 3 := by ring
  have e1 : 2 * k + 3 * (t + 1) + 1 = 2 * k + 3 * t + 4 := by ring
  have e2 : 2 * k + 3 * (t + 1) = 2 * k + 3 * t + 3 := by ring
  have e3 : 2 * k + 2 * (t + 1) = 2 * k + 2 * t + 2 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]

lemma interior_phi2 (k t : ℕ) : Φ (k) (t + 2)
    = (3 : ℚ) ^ (k) * (2 : ℚ) ^ (t + 2) * ((3 * k + 3 * t + 1 + 6).factorial : ℚ)
      / (((k).factorial : ℚ) * ((2 * k + 3 * t + 7).factorial : ℚ)) * ((2 * k + 3 * t + 6).factorial : ℚ)
      / (((t + 2).factorial : ℚ) * ((2 * k + 2 * t + 4).factorial : ℚ)) := by
  unfold Φ
  have e0 : 3 * k + 3 * (t + 2) + 1 = 3 * k + 3 * t + 1 + 6 := by ring
  have e1 : 2 * k + 3 * (t + 2) + 1 = 2 * k + 3 * t + 7 := by ring
  have e2 : 2 * k + 3 * (t + 2) = 2 * k + 3 * t + 6 := by ring
  have e3 : 2 * k + 2 * (t + 2) = 2 * k + 2 * t + 4 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]

lemma interior_phi3 (k t : ℕ) : Φ (k + 1) (t + 1)
    = (3 : ℚ) ^ (k + 1) * (2 : ℚ) ^ (t + 1) * ((3 * k + 3 * t + 1 + 6).factorial : ℚ)
      / (((k + 1).factorial : ℚ) * ((2 * k + 3 * t + 6).factorial : ℚ)) * ((2 * k + 3 * t + 5).factorial : ℚ)
      / (((t + 1).factorial : ℚ) * ((2 * k + 2 * t + 4).factorial : ℚ)) := by
  unfold Φ
  have e0 : 3 * (k + 1) + 3 * (t + 1) + 1 = 3 * k + 3 * t + 1 + 6 := by ring
  have e1 : 2 * (k + 1) + 3 * (t + 1) + 1 = 2 * k + 3 * t + 6 := by ring
  have e2 : 2 * (k + 1) + 3 * (t + 1) = 2 * k + 3 * t + 5 := by ring
  have e3 : 2 * (k + 1) + 2 * (t + 1) = 2 * k + 2 * t + 4 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]

set_option maxHeartbeats 4000000 in
lemma interior (k t : ℕ) :
    (3645 * (k : ℚ) ^ 2 + 7290 * (k : ℚ) * (t : ℚ) + 7290 * (k : ℚ) + 3645 * (t : ℚ) ^ 2 + 7290 * (t
      : ℚ) + 3240) * Φ k (t) + (-648 * (k : ℚ) ^ 2 - 1296 * (k : ℚ) * (t : ℚ) - 1350 * (k : ℚ) -
      648 * (t : ℚ) ^ 2 - 1350 * (t : ℚ) - 588) * Φ k (t + 1) + (16 * (k : ℚ) ^ 2 + 32 * (k : ℚ)
      * (t : ℚ) + 40 * (k : ℚ) + 16 * (t : ℚ) ^ 2 + 40 * (t : ℚ) + 16) * Φ k (t + 2)
    = (-4608 * (k : ℚ) ^ 9 - 46080 * (k : ℚ) ^ 8 * (t : ℚ) - 57600 * (k : ℚ) ^ 8 - 199296 * (k : ℚ) ^ 7
      * (t : ℚ) ^ 2 - 502272 * (k : ℚ) ^ 7 * (t : ℚ) - 303616 * (k : ℚ) ^ 7 - 486144 * (k : ℚ) ^
      6 * (t : ℚ) ^ 3 - 1859328 * (k : ℚ) ^ 6 * (t : ℚ) ^ 2 - 2267968 * (k : ℚ) ^ 6 * (t : ℚ) -
      877824 * (k : ℚ) ^ 6 - 730080 * (k : ℚ) ^ 5 * (t : ℚ) ^ 4 - 3788928 * (k : ℚ) ^ 5 * (t :
      ℚ) ^ 3 - 7024224 * (k : ℚ) ^ 5 * (t : ℚ) ^ 2 - 5486304 * (k : ℚ) ^ 5 * (t : ℚ) - 1512032 *
      (k : ℚ) ^ 5 - 689472 * (k : ℚ) ^ 4 * (t : ℚ) ^ 5 - 4599504 * (k : ℚ) ^ 4 * (t : ℚ) ^ 4 -
      11602080 * (k : ℚ) ^ 4 * (t : ℚ) ^ 3 - 13780656 * (k : ℚ) ^ 4 * (t : ℚ) ^ 2 - 7647568 * (k
      : ℚ) ^ 4 * (t : ℚ) - 1565040 * (k : ℚ) ^ 4 - 398520 * (k : ℚ) ^ 3 * (t : ℚ) ^ 6 - 3348864
      * (k : ℚ) ^ 3 * (t : ℚ) ^ 5 - 10915344 * (k : ℚ) ^ 3 * (t : ℚ) ^ 4 - 17669808 * (k : ℚ) ^
      3 * (t : ℚ) ^ 3 - 14881920 * (k : ℚ) ^ 3 * (t : ℚ) ^ 2 - 6084696 * (k : ℚ) ^ 3 * (t : ℚ) -
      911744 * (k : ℚ) ^ 3 - 128304 * (k : ℚ) ^ 2 * (t : ℚ) ^ 7 - 1386072 * (k : ℚ) ^ 2 * (t :
      ℚ) ^ 6 - 5751972 * (k : ℚ) ^ 2 * (t : ℚ) ^ 5 - 12076452 * (k : ℚ) ^ 2 * (t : ℚ) ^ 4 -
      13838940 * (k : ℚ) ^ 2 * (t : ℚ) ^ 3 - 8511108 * (k : ℚ) ^ 2 * (t : ℚ) ^ 2 - 2483872 * (k
      : ℚ) ^ 2 * (t : ℚ) - 228816 * (k : ℚ) ^ 2 - 17496 * (k : ℚ) * (t : ℚ) ^ 8 - 279936 * (k :
      ℚ) * (t : ℚ) ^ 7 - 1530414 * (k : ℚ) * (t : ℚ) ^ 6 - 4120794 * (k : ℚ) * (t : ℚ) ^ 5 -
      6115446 * (k : ℚ) * (t : ℚ) ^ 4 - 5062446 * (k : ℚ) * (t : ℚ) ^ 3 - 2151900 * (k : ℚ) * (t
      : ℚ) ^ 2 - 336432 * (k : ℚ) * (t : ℚ) + 16160 * (k : ℚ) - 17496 * (t : ℚ) ^ 8 - 151632 *
      (t : ℚ) ^ 7 - 542862 * (t : ℚ) ^ 6 - 1028214 * (t : ℚ) ^ 5 - 1084914 * (t : ℚ) ^ 4 -
      594018 * (t : ℚ) ^ 3 - 106248 * (t : ℚ) ^ 2 + 35784 * (t : ℚ) + 13440)
      / ((3 * (k : ℚ) + 3 * (t : ℚ) + 5) * (3 * (k : ℚ) + 3 * (t : ℚ) + 7) * (2 * (k : ℚ) + 3 * (t : ℚ) + 5) * (2 * (k : ℚ) + 3 * (t : ℚ) + 4) * (2 * (k : ℚ) + 3 * (t : ℚ) + 3) * (2 * (k : ℚ) + 3 * (t : ℚ) + 2) * (2 * (k : ℚ) + 3 * (t : ℚ) + 1)) * Φ (k + 1) (t + 1)
      - (-4608 * (k : ℚ) ^ 9 - 46080 * (k : ℚ) ^ 8 * (t : ℚ) - 62208 * (k : ℚ) ^ 8 - 199296 * (k : ℚ) ^ 7
      * (t : ℚ) ^ 2 - 532224 * (k : ℚ) ^ 7 * (t : ℚ) - 341632 * (k : ℚ) ^ 7 - 486144 * (k : ℚ) ^
      6 * (t : ℚ) ^ 3 - 1922688 * (k : ℚ) ^ 6 * (t : ℚ) ^ 2 - 2429248 * (k : ℚ) ^ 6 * (t : ℚ) -
      970944 * (k : ℚ) ^ 6 - 730080 * (k : ℚ) ^ 5 * (t : ℚ) ^ 4 - 3792384 * (k : ℚ) ^ 5 * (t :
      ℚ) ^ 3 - 7050144 * (k : ℚ) ^ 5 * (t : ℚ) ^ 2 - 5489184 * (k : ℚ) ^ 5 * (t : ℚ) - 1477376 *
      (k : ℚ) ^ 5 - 689472 * (k : ℚ) ^ 4 * (t : ℚ) ^ 5 - 4396464 * (k : ℚ) ^ 4 * (t : ℚ) ^ 4 -
      10640736 * (k : ℚ) ^ 4 * (t : ℚ) ^ 3 - 12012240 * (k : ℚ) ^ 4 * (t : ℚ) ^ 2 - 6122416 * (k
      : ℚ) ^ 4 * (t : ℚ) - 1040992 * (k : ℚ) ^ 4 - 398520 * (k : ℚ) ^ 3 * (t : ℚ) ^ 6 - 2982096
      * (k : ℚ) ^ 3 * (t : ℚ) ^ 5 - 8750808 * (k : ℚ) ^ 3 * (t : ℚ) ^ 4 - 12580560 * (k : ℚ) ^ 3
      * (t : ℚ) ^ 3 - 8870328 * (k : ℚ) ^ 3 * (t : ℚ) ^ 2 - 2479992 * (k : ℚ) ^ 3 * (t : ℚ) -
      26448 * (k : ℚ) ^ 3 - 128304 * (k : ℚ) ^ 2 * (t : ℚ) ^ 7 - 1088640 * (k : ℚ) ^ 2 * (t : ℚ)
      ^ 6 - 3679668 * (k : ℚ) ^ 2 * (t : ℚ) ^ 5 - 6186024 * (k : ℚ) ^ 2 * (t : ℚ) ^ 4 - 5074452
      * (k : ℚ) ^ 2 * (t : ℚ) ^ 3 - 1280424 * (k : ℚ) ^ 2 * (t : ℚ) ^ 2 + 668840 * (k : ℚ) ^ 2 *
      (t : ℚ) + 339664 * (k : ℚ) ^ 2 - 17496 * (k : ℚ) * (t : ℚ) ^ 8 - 163296 * (k : ℚ) * (t :
      ℚ) ^ 7 - 607014 * (k : ℚ) * (t : ℚ) ^ 6 - 1098198 * (k : ℚ) * (t : ℚ) ^ 5 - 837378 * (k :
      ℚ) * (t : ℚ) ^ 4 + 214326 * (k : ℚ) * (t : ℚ) ^ 3 + 838104 * (k : ℚ) * (t : ℚ) ^ 2 +
      532248 * (k : ℚ) * (t : ℚ) + 108384 * (k : ℚ))
      / ((3 * (k : ℚ) + 3 * (t : ℚ) + 5) * (3 * (k : ℚ) + 3 * (t : ℚ) + 7) * (2 * (k : ℚ) + 3 * (t : ℚ) + 6) * (2 * (k : ℚ) + 3 * (t : ℚ) + 5) * (2 * (k : ℚ) + 3 * (t : ℚ) + 4) * (2 * (k : ℚ) + 3 * (t : ℚ) + 3) * (2 * (k : ℚ) + 3 * (t : ℚ) + 2)) * Φ k (t + 2) := by
  have g0 : (((2 * k + 2 * t) + 2).factorial : ℚ) = (((2 * k + 2 * t : ℕ) : ℚ) + 2) * (((2 * k + 2 * t : ℕ) : ℚ) + 1) * (((2 * k + 2 * t).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * k + 2 * t) 2]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g1 : (((2 * k + 2 * t) + 4).factorial : ℚ) = (((2 * k + 2 * t : ℕ) : ℚ) + 4) * (((2 * k + 2 * t : ℕ) : ℚ) + 3) * (((2 * k + 2 * t : ℕ) : ℚ) + 2) * (((2 * k + 2 * t : ℕ) : ℚ) + 1) * (((2 * k + 2 * t).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * k + 2 * t) 4]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g2 : (((2 * k + 3 * t) + 1).factorial : ℚ) = (((2 * k + 3 * t : ℕ) : ℚ) + 1) * (((2 * k + 3 * t).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * k + 3 * t) 1]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g3 : (((2 * k + 3 * t) + 3).factorial : ℚ) = (((2 * k + 3 * t : ℕ) : ℚ) + 3) * (((2 * k + 3 * t : ℕ) : ℚ) + 2) * (((2 * k + 3 * t : ℕ) : ℚ) + 1) * (((2 * k + 3 * t).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * k + 3 * t) 3]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g4 : (((2 * k + 3 * t) + 4).factorial : ℚ) = (((2 * k + 3 * t : ℕ) : ℚ) + 4) * (((2 * k + 3 * t : ℕ) : ℚ) + 3) * (((2 * k + 3 * t : ℕ) : ℚ) + 2) * (((2 * k + 3 * t : ℕ) : ℚ) + 1) * (((2 * k + 3 * t).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * k + 3 * t) 4]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g5 : (((2 * k + 3 * t) + 5).factorial : ℚ) = (((2 * k + 3 * t : ℕ) : ℚ) + 5) * (((2 * k + 3 * t : ℕ) : ℚ) + 4) * (((2 * k + 3 * t : ℕ) : ℚ) + 3) * (((2 * k + 3 * t : ℕ) : ℚ) + 2) * (((2 * k + 3 * t : ℕ) : ℚ) + 1) * (((2 * k + 3 * t).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * k + 3 * t) 5]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g6 : (((2 * k + 3 * t) + 6).factorial : ℚ) = (((2 * k + 3 * t : ℕ) : ℚ) + 6) * (((2 * k + 3 * t : ℕ) : ℚ) + 5) * (((2 * k + 3 * t : ℕ) : ℚ) + 4) * (((2 * k + 3 * t : ℕ) : ℚ) + 3) * (((2 * k + 3 * t : ℕ) : ℚ) + 2) * (((2 * k + 3 * t : ℕ) : ℚ) + 1) * (((2 * k + 3 * t).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * k + 3 * t) 6]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g7 : (((2 * k + 3 * t) + 7).factorial : ℚ) = (((2 * k + 3 * t : ℕ) : ℚ) + 7) * (((2 * k + 3 * t : ℕ) : ℚ) + 6) * (((2 * k + 3 * t : ℕ) : ℚ) + 5) * (((2 * k + 3 * t : ℕ) : ℚ) + 4) * (((2 * k + 3 * t : ℕ) : ℚ) + 3) * (((2 * k + 3 * t : ℕ) : ℚ) + 2) * (((2 * k + 3 * t : ℕ) : ℚ) + 1) * (((2 * k + 3 * t).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * k + 3 * t) 7]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g8 : (((3 * k + 3 * t + 1) + 3).factorial : ℚ) = (((3 * k + 3 * t + 1 : ℕ) : ℚ) + 3) * (((3 * k + 3 * t + 1 : ℕ) : ℚ) + 2) * (((3 * k + 3 * t + 1 : ℕ) : ℚ) + 1) * (((3 * k + 3 * t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (3 * k + 3 * t + 1) 3]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g9 : (((3 * k + 3 * t + 1) + 6).factorial : ℚ) = (((3 * k + 3 * t + 1 : ℕ) : ℚ) + 6) * (((3 * k + 3 * t + 1 : ℕ) : ℚ) + 5) * (((3 * k + 3 * t + 1 : ℕ) : ℚ) + 4) * (((3 * k + 3 * t + 1 : ℕ) : ℚ) + 3) * (((3 * k + 3 * t + 1 : ℕ) : ℚ) + 2) * (((3 * k + 3 * t + 1 : ℕ) : ℚ) + 1) * (((3 * k + 3 * t + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (3 * k + 3 * t + 1) 6]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g10 : (((k) + 1).factorial : ℚ) = (((k : ℕ) : ℚ) + 1) * (((k).factorial : ℕ) : ℚ) := by
    rw [fsh (k) 1]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g11 : (((t) + 1).factorial : ℚ) = (((t : ℕ) : ℚ) + 1) * (((t).factorial : ℕ) : ℚ) := by
    rw [fsh (t) 1]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g12 : (((t) + 2).factorial : ℚ) = (((t : ℕ) : ℚ) + 2) * (((t : ℕ) : ℚ) + 1) * (((t).factorial : ℕ) : ℚ) := by
    rw [fsh (t) 2]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  rw [interior_phi0, interior_phi1, interior_phi2, interior_phi3]
  rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12]
  have hf0 : (((3 * k + 3 * t + 1).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf1 : (((2 * k + 3 * t).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : (((2 * k + 2 * t).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf3 : (((k).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf4 : (((t).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  push_cast
  field_simp
  ring

lemma RcM (m : ℕ) : Rc (m : ℚ) ((m : ℚ) + 1)
    = (-4608 * (m : ℚ) ^ 9 - 57600 * (m : ℚ) ^ 8 - 303616 * (m : ℚ) ^ 7 - 877824 * (m : ℚ) ^ 6 -
      1512032 * (m : ℚ) ^ 5 - 1565040 * (m : ℚ) ^ 4 - 911744 * (m : ℚ) ^ 3 - 228816 * (m : ℚ) ^
      2 + 16160 * (m : ℚ) + 13440)
      / ((3 * (m : ℚ) + 5) * (3 * (m : ℚ) + 7) * (2 * (m : ℚ) + 5) * (2 * (m : ℚ) + 4) * (2 * (m : ℚ) + 3) * (2 * (m : ℚ) + 2) * (2 * (m : ℚ) + 1)) := by
  have e : ((3 * (m : ℚ) + 5) * (3 * (m : ℚ) + 7) * (3 * (m : ℚ) - ((m : ℚ) + 1) + 6) * (3 * (m : ℚ) - ((m : ℚ) + 1) + 5) * (3 * (m : ℚ) - ((m : ℚ) + 1) + 4) * (3 * (m : ℚ) - ((m : ℚ) + 1) + 3) * (3 * (m : ℚ) - ((m : ℚ) + 1) + 2) : ℚ) = (3 * (m : ℚ) + 5) * (3 * (m : ℚ) + 7) * (2 * (m : ℚ) + 5) * (2 * (m : ℚ) + 4) * (2 * (m : ℚ) + 3) * (2 * (m : ℚ) + 2) * (2 * (m : ℚ) + 1) := by ring
  have hpos : ((3 * (m : ℚ) + 5) * (3 * (m : ℚ) + 7) * (2 * (m : ℚ) + 5) * (2 * (m : ℚ) + 4) * (2 * (m : ℚ) + 3) * (2 * (m : ℚ) + 2) * (2 * (m : ℚ) + 1) : ℚ) ≠ 0 := by positivity
  have horig : ((3 * (m : ℚ) + 5) * (3 * (m : ℚ) + 7) * (3 * (m : ℚ) - ((m : ℚ) + 1) + 6) * (3 * (m : ℚ) - ((m : ℚ) + 1) + 5) * (3 * (m : ℚ) - ((m : ℚ) + 1) + 4) * (3 * (m : ℚ) - ((m : ℚ) + 1) + 3) * (3 * (m : ℚ) - ((m : ℚ) + 1) + 2) : ℚ) ≠ 0 := by
    rw [e]
    exact hpos
  unfold Rc
  rw [div_eq_div_iff horig hpos]
  ring

lemma boundary_phi0 (m : ℕ) : Φ (m + 1) (1)
    = (3 : ℚ) ^ (m + 1) * (2 : ℚ) ^ (1) * ((3 * m + 4 + 3).factorial : ℚ)
      / (((m + 1).factorial : ℚ) * ((2 * m + 2 + 4).factorial : ℚ)) * ((2 * m + 2 + 3).factorial : ℚ)
      / ((1 : ℚ) * ((2 * m + 2 + 2).factorial : ℚ)) := by
  unfold Φ
  have e0 : 3 * (m + 1) + 3 * 1 + 1 = 3 * m + 4 + 3 := by ring
  have e1 : 2 * (m + 1) + 3 * 1 + 1 = 2 * m + 2 + 4 := by ring
  have e2 : 2 * (m + 1) + 3 * 1 = 2 * m + 2 + 3 := by ring
  have e3 : 2 * (m + 1) + 2 * 1 = 2 * m + 2 + 2 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  rw [show (1 : ℕ).factorial = 1 from rfl]
  push_cast
  ring

lemma boundary_phi1 (m : ℕ) : Φ (m + 1) (0)
    = (3 : ℚ) ^ (m + 1) * (2 : ℚ) ^ (0) * ((3 * m + 4).factorial : ℚ)
      / (((m + 1).factorial : ℚ) * ((2 * m + 2 + 1).factorial : ℚ)) * ((2 * m + 2).factorial : ℚ)
      / ((1 : ℚ) * ((2 * m + 2).factorial : ℚ)) := by
  unfold Φ
  have e0 : 3 * (m + 1) + 3 * 0 + 1 = 3 * m + 4 := by ring
  have e1 : 2 * (m + 1) + 3 * 0 + 1 = 2 * m + 2 + 1 := by ring
  have e2 : 2 * (m + 1) + 3 * 0 = 2 * m + 2 := by ring
  have e3 : 2 * (m + 1) + 2 * 0 = 2 * m + 2 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  rw [show (0 : ℕ).factorial = 1 from rfl]
  push_cast
  ring

lemma boundary_phi2 (m : ℕ) : Φ (m + 2) (0)
    = (3 : ℚ) ^ (m + 2) * (2 : ℚ) ^ (0) * ((3 * m + 4 + 3).factorial : ℚ)
      / (((m + 1 + 1).factorial : ℚ) * ((2 * m + 2 + 3).factorial : ℚ)) * ((2 * m + 2 + 2).factorial : ℚ)
      / ((1 : ℚ) * ((2 * m + 2 + 2).factorial : ℚ)) := by
  unfold Φ
  have e0 : 3 * (m + 2) + 3 * 0 + 1 = 3 * m + 4 + 3 := by ring
  have e1 : 2 * (m + 2) + 3 * 0 + 1 = 2 * m + 2 + 3 := by ring
  have e2 : 2 * (m + 2) + 3 * 0 = 2 * m + 2 + 2 := by ring
  have e3 : 2 * (m + 2) + 2 * 0 = 2 * m + 2 + 2 := by ring
  try rw [e0]
  try rw [e1]
  try rw [e2]
  try rw [e3]
  rw [show (0 : ℕ).factorial = 1 from rfl]
  push_cast
  ring

set_option maxHeartbeats 4000000 in
lemma boundary (m : ℕ) :
    (-4608 * (m : ℚ) ^ 9 - 57600 * (m : ℚ) ^ 8 - 303616 * (m : ℚ) ^ 7 - 877824 * (m : ℚ) ^ 6 -
      1512032 * (m : ℚ) ^ 5 - 1565040 * (m : ℚ) ^ 4 - 911744 * (m : ℚ) ^ 3 - 228816 * (m : ℚ) ^
      2 + 16160 * (m : ℚ) + 13440)
      / ((3 * (m : ℚ) + 5) * (3 * (m : ℚ) + 7) * (2 * (m : ℚ) + 5) * (2 * (m : ℚ) + 4) * (2 * (m : ℚ) + 3) * (2 * (m : ℚ) + 2) * (2 * (m : ℚ) + 1)) * Φ (m + 1) 1
      + ((-648 * (m : ℚ) ^ 2 - 1350 * (m : ℚ) - 588) * Φ (m + 1) 0 + (16 * (m : ℚ) ^ 2 + 40 * (m : ℚ) +
      16) * Φ (m + 1) 1 + (16 * (m : ℚ) ^ 2 + 40 * (m : ℚ) + 16) * Φ (m + 2) 0) = 0 := by
  have g0 : (((2 * m + 2) + 1).factorial : ℚ) = (((2 * m + 2 : ℕ) : ℚ) + 1) * (((2 * m + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * m + 2) 1]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g1 : (((2 * m + 2) + 2).factorial : ℚ) = (((2 * m + 2 : ℕ) : ℚ) + 2) * (((2 * m + 2 : ℕ) : ℚ) + 1) * (((2 * m + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * m + 2) 2]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g2 : (((2 * m + 2) + 3).factorial : ℚ) = (((2 * m + 2 : ℕ) : ℚ) + 3) * (((2 * m + 2 : ℕ) : ℚ) + 2) * (((2 * m + 2 : ℕ) : ℚ) + 1) * (((2 * m + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * m + 2) 3]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g3 : (((2 * m + 2) + 4).factorial : ℚ) = (((2 * m + 2 : ℕ) : ℚ) + 4) * (((2 * m + 2 : ℕ) : ℚ) + 3) * (((2 * m + 2 : ℕ) : ℚ) + 2) * (((2 * m + 2 : ℕ) : ℚ) + 1) * (((2 * m + 2).factorial : ℕ) : ℚ) := by
    rw [fsh (2 * m + 2) 4]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g4 : (((3 * m + 4) + 3).factorial : ℚ) = (((3 * m + 4 : ℕ) : ℚ) + 3) * (((3 * m + 4 : ℕ) : ℚ) + 2) * (((3 * m + 4 : ℕ) : ℚ) + 1) * (((3 * m + 4).factorial : ℕ) : ℚ) := by
    rw [fsh (3 * m + 4) 3]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  have g5 : (((m + 1) + 1).factorial : ℚ) = (((m + 1 : ℕ) : ℚ) + 1) * (((m + 1).factorial : ℕ) : ℚ) := by
    rw [fsh (m + 1) 1]
    simp only [Finset.prod_range_succ, Finset.prod_range_zero]
    push_cast
    ring
  rw [boundary_phi0, boundary_phi1, boundary_phi2]
  rw [g0, g1, g2, g3, g4, g5]
  have hf0 : (((3 * m + 4).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf1 : (((2 * m + 2).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hf2 : (((m + 1).factorial : ℕ) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  push_cast
  field_simp
  ring

lemma split0 (m : ℕ) : ((a m : ℤ) : ℚ)
    = ∑ k ∈ Finset.range (m + 1), Φ k (m - k + 0) := by
  have hmain : ∀ k ∈ Finset.range (m + 1), (F m k : ℚ) = Φ k (m - k + 0) := by
    intro k hk
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h := F_eq k (m - k + 0)
    rw [show k + (m - k + 0) = m from by omega] at h
    exact h
  rw [a_eq]
  push_cast
  exact Finset.sum_congr rfl hmain

lemma split1 (m : ℕ) : ((a (m + 1) : ℤ) : ℚ)
    = ∑ k ∈ Finset.range (m + 1), Φ k (m - k + 1) + (Φ (m + 1) 0) := by
  have hmain : ∀ k ∈ Finset.range (m + 1), (F (m + 1) k : ℚ) = Φ k (m - k + 1) := by
    intro k hk
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h := F_eq k (m - k + 1)
    rw [show k + (m - k + 1) = m + 1 from by omega] at h
    exact h
  have q1 : (F (m + 1) (m + 1 + 0) : ℚ) = Φ (m + 1) 0 := by
    have h := F_eq (m + 1) 0
    rw [show m + 1 + 0 = m + 1 from by ring] at h
    rw [show m + 1 + 0 = m + 1 from by ring]
    exact h
  rw [a_eq, show m + 1 + 1 = (m + 1) + 1 from by ring, Finset.sum_range_add]
  push_cast
  rw [Finset.sum_congr rfl hmain]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, q1]

lemma split2 (m : ℕ) : ((a (m + 2) : ℤ) : ℚ)
    = ∑ k ∈ Finset.range (m + 1), Φ k (m - k + 2) + (Φ (m + 1) 1 + Φ (m + 2) 0) := by
  have hmain : ∀ k ∈ Finset.range (m + 1), (F (m + 2) k : ℚ) = Φ k (m - k + 2) := by
    intro k hk
    have hk' : k ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have h := F_eq k (m - k + 2)
    rw [show k + (m - k + 2) = m + 2 from by omega] at h
    exact h
  have q1 : (F (m + 2) (m + 1 + 0) : ℚ) = Φ (m + 1) 1 := by
    have h := F_eq (m + 1) 1
    rw [show m + 1 + 1 = m + 2 from by ring] at h
    rw [show m + 1 + 0 = m + 1 from by ring]
    exact h
  have q2 : (F (m + 2) (m + 1 + 1) : ℚ) = Φ (m + 2) 0 := by
    have h := F_eq (m + 2) 0
    rw [show m + 2 + 0 = m + 2 from by ring] at h
    rw [show m + 1 + 1 = m + 2 from by ring]
    exact h
  rw [a_eq, show m + 2 + 1 = (m + 1) + 2 from by ring, Finset.sum_range_add]
  push_cast
  rw [Finset.sum_congr rfl hmain]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, q1, q2]


lemma step (m k : ℕ) (hk : k ≤ m) :
    (3645 * (m : ℚ) ^ 2 + 7290 * (m : ℚ) + 3240) * Φ k (m - k + 0) + (-648 * (m : ℚ) ^ 2 - 1350 * (m
      : ℚ) - 588) * Φ k (m - k + 1) + (16 * (m : ℚ) ^ 2 + 40 * (m : ℚ) + 16) * Φ k (m - k + 2)
    = Gf m (k + 1) - Gf m k := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  have h := interior k t
  unfold Gf
  rw [Nat.add_sub_cancel_left, show k + t + 2 - (k + 1) = t + 1 from by omega,
    show k + t + 2 - k = t + 2 from by omega]
  push_cast at h ⊢
  rw [RcA k t, RcB k t]
  linear_combination h

lemma Gf_zero (m : ℕ) : Gf m 0 = 0 := by
  unfold Gf Rc
  simp

lemma main_q (m : ℕ) :
    (3645 * (m : ℚ) ^ 2 + 7290 * (m : ℚ) + 3240) * ((a (m) : ℤ) : ℚ) + (-648 * (m : ℚ) ^ 2 - 1350 *
      (m : ℚ) - 588) * ((a (m + 1) : ℤ) : ℚ) + (16 * (m : ℚ) ^ 2 + 40 * (m : ℚ) + 16) * ((a (m +
      2) : ℤ) : ℚ) = 0 := by
  have hsum : ∑ k ∈ Finset.range (m + 1), ((3645 * (m : ℚ) ^ 2 + 7290 * (m : ℚ) + 3240) * Φ k (m - k + 0) + (-648 * (m : ℚ) ^ 2 - 1350 * (m : ℚ) - 588) * Φ k (m - k + 1) + (16 * (m : ℚ) ^ 2 + 40 * (m : ℚ) + 16) * Φ k (m - k + 2))
      = Gf m (m + 1) - Gf m 0 := by
    rw [← Finset.sum_range_sub (Gf m) (m + 1)]
    apply Finset.sum_congr rfl
    intro k hk
    exact step m k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))
  have hb := boundary m
  have hG : Gf m (m + 1) = Rc (m : ℚ) ((m : ℚ) + 1) * Φ (m + 1) 1 := by
    unfold Gf
    rw [show m + 2 - (m + 1) = 1 from by omega]
    push_cast
    ring
  rw [split0, split1, split2]
  have hdist : (3645 * (m : ℚ) ^ 2 + 7290 * (m : ℚ) + 3240) * ∑ k ∈ Finset.range (m + 1), Φ k (m - k + 0) +
      (-648 * (m : ℚ) ^ 2 - 1350 * (m : ℚ) - 588) * ∑ k ∈ Finset.range (m + 1), Φ k (m - k + 1)
      + (16 * (m : ℚ) ^ 2 + 40 * (m : ℚ) + 16) * ∑ k ∈ Finset.range (m + 1), Φ k (m - k + 2)
      = ∑ k ∈ Finset.range (m + 1), ((3645 * (m : ℚ) ^ 2 + 7290 * (m : ℚ) + 3240) * Φ k (m - k + 0) + (-648 * (m : ℚ) ^ 2 - 1350 * (m : ℚ) - 588) * Φ k (m - k + 1) + (16 * (m : ℚ) ^ 2 + 40 * (m : ℚ) + 16) * Φ k (m - k + 2)) := by
    simp only [Finset.mul_sum, Finset.sum_add_distrib]
  rw [Gf_zero, hG, RcM m] at hsum
  linear_combination hdist + hsum + hb

end OMA.T386830

theorem OMA.solution : type_of% @OMA.S_oeis_a386830.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have h := OMA.T386830.main_q m
  have t1 : m + 2 - 1 = m + 1 := by omega
  have t2 : m + 2 - 2 = m := by omega
  simp only [t1, t2]
  have hq : (((0 : ℤ) : ℚ)) = 0 := by norm_num
  apply Int.cast_injective (α := ℚ)
  push_cast
  linear_combination h
