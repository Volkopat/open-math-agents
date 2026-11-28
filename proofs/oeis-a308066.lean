import OMAStatements.S_oeis_a308066
import Mathlib

/-!
# A308066: Barker's recurrence

Write E(r), O(r) for the numbers of triangles x <= y <= z < x + y with perimeter r and all sides
even, resp. odd. Adding 1 to every side maps the all-odd triples of perimeter r with z <= x + y
(z = x + y is impossible for odd x, y, z) onto the all-even triangles of perimeter r + 3, and the
all-even triples with z <= x + y onto the all-odd triangles of perimeter r + 3 with smallest side
at least 2. The only all-odd triangle with smallest side 1 is (1, s, s) with s odd, i.e. r = 0
(mod 4); the degenerate all-even triples z = x + y exist only for r = 0 (mod 4) and number
floor(r/8). Hence E(r + 6) = E(r) + D8(r) + [r = 0 mod 4] with 8 D8(r) = r [r = 0 mod 8] +
(r - 4) [r = 4 mod 8], and Barker's operator applied to E is an explicit combination of these
relations and of the shift relations of the residue indicators mod 8 (computed over ℚ).
-/

namespace PA308066
theorem icc_range' (k X : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ Finset.Icc k X, f i = ∑ j ∈ Finset.range (X + 1 - k), f (k + j) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]

/-- Weighted sum over the partitions `j + i + (r - i - j)` of `r` with fixed smallest part `j`. -/
def I3 (w : ℕ → ℕ → ℕ → ℕ) (r j : ℕ) : ℕ :=
  ∑ u ∈ Finset.range ((r - j) / 2 + 1 - j), w j (j + u) (r - (j + u) - j)

/-- Weighted sum over the partitions of `r` into 3 parts, all at least `k`. -/
def H3 (w : ℕ → ℕ → ℕ → ℕ) (r k : ℕ) : ℕ :=
  ∑ s ∈ Finset.range (r / 3 + 1 - k), I3 w r (k + s)

theorem I3_shift (w : ℕ → ℕ → ℕ → ℕ) (r j : ℕ) :
    I3 w (r + 3) (j + 1) = I3 (fun x y z => w (x + 1) (y + 1) (z + 1)) r j := by
  unfold I3
  rw [show (r + 3 - (j + 1)) / 2 + 1 - (j + 1) = (r - j) / 2 + 1 - j by omega]
  refine Finset.sum_congr rfl fun u hu => ?_
  rw [Finset.mem_range] at hu
  rw [show r + 3 - (j + 1 + u) - (j + 1) = r - (j + u) - j + 1 by omega,
    show j + 1 + u = j + u + 1 by omega]

theorem H3_shift (w : ℕ → ℕ → ℕ → ℕ) (r k : ℕ) :
    H3 w (r + 3) (k + 1) = H3 (fun x y z => w (x + 1) (y + 1) (z + 1)) r k := by
  unfold H3
  rw [show (r + 3) / 3 + 1 - (k + 1) = r / 3 + 1 - k by omega]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show k + 1 + s = k + s + 1 by omega]
  exact I3_shift w r (k + s)

theorem H3_peel (w : ℕ → ℕ → ℕ → ℕ) (r : ℕ) :
    H3 w (r + 3) 1 = H3 (fun x y z => w (x + 1) (y + 1) (z + 1)) r 1 + I3 w (r + 3) 1 := by
  unfold H3
  rw [show (r + 3) / 3 + 1 - 1 = r / 3 + 1 - 1 + 1 by omega, Finset.sum_range_succ',
    Nat.add_zero]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [show 1 + (s + 1) = 1 + s + 1 by omega]
  exact I3_shift w r (1 + s)

theorem H3_congr (w w' : ℕ → ℕ → ℕ → ℕ) (r k : ℕ) (h : ∀ x y z, w x y z = w' x y z) :
    H3 w r k = H3 w' r k := by
  rw [show w = w' from funext fun x => funext fun y => funext fun z => h x y z]

theorem H3_add (f g : ℕ → ℕ → ℕ → ℕ) (r k : ℕ) :
    H3 (fun x y z => f x y z + g x y z) r k = H3 f r k + H3 g r k := by
  unfold H3 I3
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.sum_add_distrib]

def wE (x y z : ℕ) : ℕ := if x % 2 = 0 ∧ y % 2 = 0 ∧ z % 2 = 0 ∧ z < y + x then 1 else 0

def wO (x y z : ℕ) : ℕ := if x % 2 = 1 ∧ y % 2 = 1 ∧ z % 2 = 1 ∧ z < y + x then 1 else 0

def dE (x y z : ℕ) : ℕ := if x % 2 = 0 ∧ y % 2 = 0 ∧ z = y + x then 1 else 0

def E (r : ℕ) : ℕ := H3 wE r 1

def O (r : ℕ) : ℕ := H3 wO r 1

def D8 (r : ℕ) : ℕ := if r % 4 = 0 then r / 8 else 0

def J (j r : ℕ) : ℕ := if r % 8 = j then 1 else 0

theorem I3_dE (r j : ℕ) (hj : 1 ≤ j) :
    I3 dE r j = if r % 4 = 0 ∧ j % 2 = 0 ∧ 4 * j ≤ r then 1 else 0 := by
  unfold I3 dE
  split_ifs with h
  · rw [Finset.sum_eq_single (r / 2 - 2 * j)]
    · rw [if_pos (by omega)]
    · intro b hb hne
      rw [Finset.mem_range] at hb
      rw [if_neg (by omega)]
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_range]
      omega
  · refine Finset.sum_eq_zero fun u hu => ?_
    rw [Finset.mem_range] at hu
    rw [if_neg (by omega)]

theorem cnt8 (r K : ℕ) :
    ∑ s ∈ Finset.range K, (if r % 4 = 0 ∧ (1 + s) % 2 = 0 ∧ 4 * (1 + s) ≤ r then 1 else 0) =
      if r % 4 = 0 then min (K / 2) (r / 8) else 0 := by
  induction K with
  | zero => split_ifs <;> simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

theorem deg8 (r : ℕ) : H3 dE r 1 = D8 r := by
  unfold H3 D8
  rw [Finset.sum_congr rfl fun s _ => I3_dE r (1 + s) (by omega), cnt8]
  split_ifs <;> omega

theorem sliceE (r : ℕ) : I3 wE (r + 3) 1 = 0 := by
  unfold I3 wE
  exact Finset.sum_eq_zero fun u _ => if_neg (by omega)

theorem sliceO (r : ℕ) : I3 wO (r + 3) 1 = if r % 4 = 0 then 1 else 0 := by
  unfold I3 wO
  by_cases h : r % 2 = 0
  · rw [Finset.sum_eq_single (r / 2)]
    · split_ifs <;> omega
    · intro b hb hne
      rw [Finset.mem_range] at hb
      rw [if_neg (by omega)]
    · intro hn
      exfalso
      apply hn
      rw [Finset.mem_range]
      omega
  · rw [Finset.sum_eq_zero fun u hu => by rw [Finset.mem_range] at hu; rw [if_neg (by omega)],
      if_neg (by omega)]

theorem relE (r : ℕ) : E (r + 3) = O r := by
  unfold E O
  rw [H3_peel, H3_congr _ wO r 1 (fun x y z => by unfold wE wO; split_ifs <;> omega), sliceE,
    Nat.add_zero]

theorem relO (r : ℕ) : O (r + 3) = E r + D8 r + (if r % 4 = 0 then 1 else 0) := by
  unfold E O
  rw [H3_peel, H3_congr _ (fun x y z => wE x y z + dE x y z) r 1
    (fun x y z => by unfold wE wO dE; split_ifs <;> omega), H3_add, deg8, sliceO]

theorem relA (r : ℕ) : E (r + 6) = E r + D8 r + J 0 r + J 4 r := by
  rw [show r + 6 = r + 3 + 3 by omega, relE, relO]
  unfold J
  split_ifs <;> omega

theorem relD8 (r : ℕ) : 8 * D8 r + 4 * J 4 r = r * J 0 r + r * J 4 r := by
  unfold D8 J
  split_ifs <;> omega

theorem relU (r : ℕ) :
    J 0 r + J 1 r + J 2 r + J 3 r + J 4 r + J 5 r + J 6 r + J 7 r = 1 := by
  unfold J
  split_ifs <;> omega

theorem relS0 (r : ℕ) : J 0 (r + 1) = J 7 r := by
  unfold J
  split_ifs <;> omega

theorem relS1 (r : ℕ) : J 1 (r + 1) = J 0 r := by
  unfold J
  split_ifs <;> omega

theorem relS2 (r : ℕ) : J 2 (r + 1) = J 1 r := by
  unfold J
  split_ifs <;> omega

theorem relS3 (r : ℕ) : J 3 (r + 1) = J 2 r := by
  unfold J
  split_ifs <;> omega

theorem relS4 (r : ℕ) : J 4 (r + 1) = J 3 r := by
  unfold J
  split_ifs <;> omega

theorem relS5 (r : ℕ) : J 5 (r + 1) = J 4 r := by
  unfold J
  split_ifs <;> omega

theorem relS6 (r : ℕ) : J 6 (r + 1) = J 5 r := by
  unfold J
  split_ifs <;> omega

theorem relS7 (r : ℕ) : J 7 (r + 1) = J 6 r := by
  unfold J
  split_ifs <;> omega

theorem a_eq (n : ℕ) : OMA.S_oeis_a308066.a n = E n := by
  unfold OMA.S_oeis_a308066.a E H3
  rw [icc_range']
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold I3 wE
  rw [icc_range']

end PA308066

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a308066.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 18 := ⟨n - 18, by omega⟩
  simp only [show m + 18 - 4 = m + 14 by omega, show m + 18 - 6 = m + 12 by omega, show m + 18 - 8 = m +
    10 by omega, show m + 18 - 10 = m + 8 by omega, show m + 18 - 12 = m + 6 by omega, show m +
    18 - 14 = m + 4 by omega, show m + 18 - 18 = m by omega, PA308066.a_eq]
  qify
  have hA_0 : (PA308066.E (m + 6) : ℚ) = PA308066.E (m) + PA308066.D8 (m) + PA308066.J 0 (m) + PA308066.J 4 (m) := by
    exact_mod_cast PA308066.relA (m)
  have hA_4 : (PA308066.E (m + 10) : ℚ) = PA308066.E (m + 4) + PA308066.D8 (m + 4) + PA308066.J 0 (m + 4) + PA308066.J 4 (m + 4) := by
    exact_mod_cast PA308066.relA (m + 4)
  have hA_8 : (PA308066.E (m + 14) : ℚ) = PA308066.E (m + 8) + PA308066.D8 (m + 8) + PA308066.J 0 (m + 8) + PA308066.J 4 (m + 8) := by
    exact_mod_cast PA308066.relA (m + 8)
  have hA_12 : (PA308066.E (m + 18) : ℚ) = PA308066.E (m + 12) + PA308066.D8 (m + 12) + PA308066.J 0 (m + 12) + PA308066.J 4 (m + 12) := by
    exact_mod_cast PA308066.relA (m + 12)
  have hD8_0 : 8 * (PA308066.D8 (m) : ℚ) + 4 * PA308066.J 4 (m) = (m : ℚ) * PA308066.J 0 (m) + (m : ℚ) * PA308066.J 4 (m) := by
    exact_mod_cast PA308066.relD8 (m)
  have hD8_4 : 8 * (PA308066.D8 (m + 4) : ℚ) + 4 * PA308066.J 4 (m + 4) = ((m : ℚ) + 4) * PA308066.J 0 (m + 4) + ((m : ℚ) + 4) * PA308066.J 4 (m + 4) := by
    exact_mod_cast PA308066.relD8 (m + 4)
  have hD8_8 : 8 * (PA308066.D8 (m + 8) : ℚ) + 4 * PA308066.J 4 (m + 8) = ((m : ℚ) + 8) * PA308066.J 0 (m + 8) + ((m : ℚ) + 8) * PA308066.J 4 (m + 8) := by
    exact_mod_cast PA308066.relD8 (m + 8)
  have hD8_12 : 8 * (PA308066.D8 (m + 12) : ℚ) + 4 * PA308066.J 4 (m + 12) = ((m : ℚ) + 12) * PA308066.J 0 (m + 12) + ((m : ℚ) + 12) * PA308066.J 4 (m + 12) := by
    exact_mod_cast PA308066.relD8 (m + 12)
  have hS0_2 : (PA308066.J 0 (m + 3) : ℚ) = PA308066.J 7 (m + 2) := by
    exact_mod_cast PA308066.relS0 (m + 2)
  have hS0_3 : (PA308066.J 0 (m + 4) : ℚ) = PA308066.J 7 (m + 3) := by
    exact_mod_cast PA308066.relS0 (m + 3)
  have hS0_10 : (PA308066.J 0 (m + 11) : ℚ) = PA308066.J 7 (m + 10) := by
    exact_mod_cast PA308066.relS0 (m + 10)
  have hS0_11 : (PA308066.J 0 (m + 12) : ℚ) = PA308066.J 7 (m + 11) := by
    exact_mod_cast PA308066.relS0 (m + 11)
  have hS1_0 : (PA308066.J 1 (m + 1) : ℚ) = PA308066.J 0 (m) := by
    exact_mod_cast PA308066.relS1 (m)
  have hS1_2 : (PA308066.J 1 (m + 3) : ℚ) = PA308066.J 0 (m + 2) := by
    exact_mod_cast PA308066.relS1 (m + 2)
  have hS1_4 : (PA308066.J 1 (m + 5) : ℚ) = PA308066.J 0 (m + 4) := by
    exact_mod_cast PA308066.relS1 (m + 4)
  have hS1_8 : (PA308066.J 1 (m + 9) : ℚ) = PA308066.J 0 (m + 8) := by
    exact_mod_cast PA308066.relS1 (m + 8)
  have hS1_10 : (PA308066.J 1 (m + 11) : ℚ) = PA308066.J 0 (m + 10) := by
    exact_mod_cast PA308066.relS1 (m + 10)
  have hS2_1 : (PA308066.J 2 (m + 2) : ℚ) = PA308066.J 1 (m + 1) := by
    exact_mod_cast PA308066.relS2 (m + 1)
  have hS2_2 : (PA308066.J 2 (m + 3) : ℚ) = PA308066.J 1 (m + 2) := by
    exact_mod_cast PA308066.relS2 (m + 2)
  have hS2_5 : (PA308066.J 2 (m + 6) : ℚ) = PA308066.J 1 (m + 5) := by
    exact_mod_cast PA308066.relS2 (m + 5)
  have hS2_9 : (PA308066.J 2 (m + 10) : ℚ) = PA308066.J 1 (m + 9) := by
    exact_mod_cast PA308066.relS2 (m + 9)
  have hS2_10 : (PA308066.J 2 (m + 11) : ℚ) = PA308066.J 1 (m + 10) := by
    exact_mod_cast PA308066.relS2 (m + 10)
  have hS3_2 : (PA308066.J 3 (m + 3) : ℚ) = PA308066.J 2 (m + 2) := by
    exact_mod_cast PA308066.relS3 (m + 2)
  have hS3_6 : (PA308066.J 3 (m + 7) : ℚ) = PA308066.J 2 (m + 6) := by
    exact_mod_cast PA308066.relS3 (m + 6)
  have hS3_10 : (PA308066.J 3 (m + 11) : ℚ) = PA308066.J 2 (m + 10) := by
    exact_mod_cast PA308066.relS3 (m + 10)
  have hS4_2 : (PA308066.J 4 (m + 3) : ℚ) = PA308066.J 3 (m + 2) := by
    exact_mod_cast PA308066.relS4 (m + 2)
  have hS4_3 : (PA308066.J 4 (m + 4) : ℚ) = PA308066.J 3 (m + 3) := by
    exact_mod_cast PA308066.relS4 (m + 3)
  have hS4_7 : (PA308066.J 4 (m + 8) : ℚ) = PA308066.J 3 (m + 7) := by
    exact_mod_cast PA308066.relS4 (m + 7)
  have hS4_10 : (PA308066.J 4 (m + 11) : ℚ) = PA308066.J 3 (m + 10) := by
    exact_mod_cast PA308066.relS4 (m + 10)
  have hS4_11 : (PA308066.J 4 (m + 12) : ℚ) = PA308066.J 3 (m + 11) := by
    exact_mod_cast PA308066.relS4 (m + 11)
  have hS5_0 : (PA308066.J 5 (m + 1) : ℚ) = PA308066.J 4 (m) := by
    exact_mod_cast PA308066.relS5 (m)
  have hS5_2 : (PA308066.J 5 (m + 3) : ℚ) = PA308066.J 4 (m + 2) := by
    exact_mod_cast PA308066.relS5 (m + 2)
  have hS5_8 : (PA308066.J 5 (m + 9) : ℚ) = PA308066.J 4 (m + 8) := by
    exact_mod_cast PA308066.relS5 (m + 8)
  have hS5_10 : (PA308066.J 5 (m + 11) : ℚ) = PA308066.J 4 (m + 10) := by
    exact_mod_cast PA308066.relS5 (m + 10)
  have hS6_1 : (PA308066.J 6 (m + 2) : ℚ) = PA308066.J 5 (m + 1) := by
    exact_mod_cast PA308066.relS6 (m + 1)
  have hS6_2 : (PA308066.J 6 (m + 3) : ℚ) = PA308066.J 5 (m + 2) := by
    exact_mod_cast PA308066.relS6 (m + 2)
  have hS6_9 : (PA308066.J 6 (m + 10) : ℚ) = PA308066.J 5 (m + 9) := by
    exact_mod_cast PA308066.relS6 (m + 9)
  have hS6_10 : (PA308066.J 6 (m + 11) : ℚ) = PA308066.J 5 (m + 10) := by
    exact_mod_cast PA308066.relS6 (m + 10)
  have hU_2 : (PA308066.J 0 (m + 2) : ℚ) + PA308066.J 1 (m + 2) + PA308066.J 2 (m + 2) + PA308066.J 3 (m + 2) + PA308066.J 4 (m + 2) + PA308066.J 5 (m + 2) + PA308066.J 6 (m + 2) + PA308066.J 7 (m + 2) = 1 := by
    exact_mod_cast PA308066.relU (m + 2)
  have hU_3 : (PA308066.J 0 (m + 3) : ℚ) + PA308066.J 1 (m + 3) + PA308066.J 2 (m + 3) + PA308066.J 3 (m + 3) + PA308066.J 4 (m + 3) + PA308066.J 5 (m + 3) + PA308066.J 6 (m + 3) + PA308066.J 7 (m + 3) = 1 := by
    exact_mod_cast PA308066.relU (m + 3)
  have hU_10 : (PA308066.J 0 (m + 10) : ℚ) + PA308066.J 1 (m + 10) + PA308066.J 2 (m + 10) + PA308066.J 3 (m + 10) + PA308066.J 4 (m + 10) + PA308066.J 5 (m + 10) + PA308066.J 6 (m + 10) + PA308066.J 7 (m + 10) = 1 := by
    exact_mod_cast PA308066.relU (m + 10)
  have hU_11 : (PA308066.J 0 (m + 11) : ℚ) + PA308066.J 1 (m + 11) + PA308066.J 2 (m + 11) + PA308066.J 3 (m + 11) + PA308066.J 4 (m + 11) + PA308066.J 5 (m + 11) + PA308066.J 6 (m + 11) + PA308066.J 7 (m + 11) = 1 := by
    exact_mod_cast PA308066.relU (m + 11)
  linear_combination ((1 : ℚ)) * hA_0 + ((-1 : ℚ)) * hA_4 + ((-1 : ℚ)) * hA_8 + ((1 : ℚ)) * hA_12 + ((1 / 8 : ℚ))
    * hD8_0 + ((-1 / 8 : ℚ)) * hD8_4 + ((-1 / 8 : ℚ)) * hD8_8 + ((1 / 8 : ℚ)) * hD8_12 + ((1 / 2
    : ℚ) + (1 / 8 : ℚ) * (m : ℚ)) * hS0_2 + ((-1 / 2 : ℚ) + (-1 / 8 : ℚ) * (m : ℚ)) * hS0_3 +
    ((-5 / 2 : ℚ) + (-1 / 8 : ℚ) * (m : ℚ)) * hS0_10 + ((5 / 2 : ℚ) + (1 / 8 : ℚ) * (m : ℚ)) *
    hS0_11 + ((-1 : ℚ) + (-1 / 8 : ℚ) * (m : ℚ)) * hS1_0 + ((1 / 2 : ℚ) + (1 / 8 : ℚ) * (m : ℚ))
    * hS1_2 + ((1 : ℚ)) * hS1_4 + ((2 : ℚ) + (1 / 8 : ℚ) * (m : ℚ)) * hS1_8 + ((-5 / 2 : ℚ) +
    (-1 / 8 : ℚ) * (m : ℚ)) * hS1_10 + ((-1 : ℚ) + (-1 / 8 : ℚ) * (m : ℚ)) * hS2_1 + ((1 / 2 :
    ℚ) + (1 / 8 : ℚ) * (m : ℚ)) * hS2_2 + ((1 : ℚ)) * hS2_5 + ((2 : ℚ) + (1 / 8 : ℚ) * (m : ℚ))
    * hS2_9 + ((-5 / 2 : ℚ) + (-1 / 8 : ℚ) * (m : ℚ)) * hS2_10 + ((-1 / 2 : ℚ)) * hS3_2 + ((1 :
    ℚ)) * hS3_6 + ((-1 / 2 : ℚ)) * hS3_10 + ((1 / 2 : ℚ) + (1 / 8 : ℚ) * (m : ℚ)) * hS4_2 + ((-1
    : ℚ) + (-1 / 8 : ℚ) * (m : ℚ)) * hS4_3 + ((1 : ℚ)) * hS4_7 + ((-5 / 2 : ℚ) + (-1 / 8 : ℚ) *
    (m : ℚ)) * hS4_10 + ((2 : ℚ) + (1 / 8 : ℚ) * (m : ℚ)) * hS4_11 + ((-1 / 2 : ℚ) + (-1 / 8 :
    ℚ) * (m : ℚ)) * hS5_0 + ((1 / 2 : ℚ) + (1 / 8 : ℚ) * (m : ℚ)) * hS5_2 + ((5 / 2 : ℚ) + (1 /
    8 : ℚ) * (m : ℚ)) * hS5_8 + ((-5 / 2 : ℚ) + (-1 / 8 : ℚ) * (m : ℚ)) * hS5_10 + ((-1 / 2 : ℚ)
    + (-1 / 8 : ℚ) * (m : ℚ)) * hS6_1 + ((1 / 2 : ℚ) + (1 / 8 : ℚ) * (m : ℚ)) * hS6_2 + ((5 / 2
    : ℚ) + (1 / 8 : ℚ) * (m : ℚ)) * hS6_9 + ((-5 / 2 : ℚ) + (-1 / 8 : ℚ) * (m : ℚ)) * hS6_10 +
    ((1 / 2 : ℚ) + (1 / 8 : ℚ) * (m : ℚ)) * hU_2 + ((-1 / 2 : ℚ) + (-1 / 8 : ℚ) * (m : ℚ)) *
    hU_3 + ((-5 / 2 : ℚ) + (-1 / 8 : ℚ) * (m : ℚ)) * hU_10 + ((5 / 2 : ℚ) + (1 / 8 : ℚ) * (m :
    ℚ)) * hU_11
