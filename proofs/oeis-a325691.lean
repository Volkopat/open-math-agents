import OMAStatements.S_oeis_a325691
import Mathlib

/-!
# A325691: Barker's recurrence

Write C(r) for the number of partitions (x, y, z) of r into 3 parts with x <= y <= z <= x + y.
Adding 1 to every part maps the partitions of r with z <= x + y + 1 onto the partitions of r + 3
with smallest part at least 2 and z <= x + y; exactly one partition of r + 3 with smallest part 1
qualifies, (1, floor(r/2) + 1, ceil(r/2) + 1). The partitions with z = x + y + 1 exist only for odd
r and number floor((r - 1)/4) = DD(r). Hence C(r + 3) = C(r) + DD(r) + 1, DD(r + 4) = DD(r) + (r mod 2)
and r mod 2 has period 2, so Barker's operator (E^3 - 1)(E^2 - 1)(E^4 - 1) annihilates C.
-/

namespace PA325691

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

/-- The indicator that the largest part `z` is at most `y + x`. -/
def w (x y z : ℕ) : ℕ := if z ≤ y + x then 1 else 0

/-- The indicator of the near-degenerate partitions `z = x + y + 1`. -/
def w' (x y z : ℕ) : ℕ := if z = x + y + 1 then 1 else 0

def C (r : ℕ) : ℕ := H3 w r 1

def DD (r : ℕ) : ℕ := if r % 2 = 1 then (r - 1) / 4 else 0

def Par (r : ℕ) : ℕ := r % 2

theorem I3_deg (r j : ℕ) (hj : 1 ≤ j) :
    I3 w' r j = if r % 2 = 1 ∧ 4 * j + 1 ≤ r then 1 else 0 := by
  unfold I3 w'
  split_ifs with h
  · rw [Finset.sum_eq_single ((r - 4 * j - 1) / 2)]
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

theorem cnt (r K : ℕ) :
    ∑ s ∈ Finset.range K, (if 4 * (1 + s) + 1 ≤ r then 1 else 0) = min K ((r - 1) / 4) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

theorem deg_eq (r : ℕ) : H3 w' r 1 = DD r := by
  unfold H3 DD
  rw [Finset.sum_congr rfl fun s _ => I3_deg r (1 + s) (by omega)]
  by_cases hr : r % 2 = 1
  · simp only [hr, true_and]
    rw [cnt, if_pos trivial]
    omega
  · rw [if_neg hr]
    exact Finset.sum_eq_zero fun s _ => if_neg fun h => hr h.1

theorem slice (r : ℕ) : I3 w (r + 3) 1 = 1 := by
  unfold I3 w
  rw [Finset.sum_eq_single (r / 2)]
  · rw [if_pos (by omega)]
  · intro b hb hne
    rw [Finset.mem_range] at hb
    rw [if_neg (by omega)]
  · intro hn
    exfalso
    apply hn
    rw [Finset.mem_range]
    omega

theorem relC (r : ℕ) : C (r + 3) = C r + DD r + 1 := by
  unfold C
  rw [H3_peel, H3_congr _ (fun x y z => w x y z + w' x y z) r 1
    (fun x y z => by unfold w w'; split_ifs <;> omega), H3_add, deg_eq, slice]

theorem relD (r : ℕ) : DD (r + 4) = DD r + Par r := by
  unfold DD Par
  split_ifs <;> omega

theorem relP (r : ℕ) : Par (r + 2) = Par r := by
  unfold Par
  omega

theorem a_eq (n : ℕ) : OMA.S_oeis_a325691.a n = C n := by
  unfold OMA.S_oeis_a325691.a C H3
  rw [icc_range']
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold I3
  rw [icc_range']
  rfl

end PA325691

theorem OMA.solution : type_of% @OMA.S_oeis_a325691.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 9 := ⟨n - 9, by omega⟩
  simp only [show m + 9 - 2 = m + 7 by omega, show m + 9 - 3 = m + 6 by omega,
    show m + 9 - 4 = m + 5 by omega, show m + 9 - 5 = m + 4 by omega, show m + 9 - 6 = m + 3 by omega,
    show m + 9 - 7 = m + 2 by omega, show m + 9 - 9 = m by omega, PA325691.a_eq]
  have hRC_0 : (PA325691.C (m + 3) : ℤ) = PA325691.C m + PA325691.DD m + 1 := by
    exact_mod_cast PA325691.relC m
  have hRC_2 : (PA325691.C (m + 5) : ℤ) = PA325691.C (m + 2) + PA325691.DD (m + 2) + 1 := by
    exact_mod_cast PA325691.relC (m + 2)
  have hRC_4 : (PA325691.C (m + 7) : ℤ) = PA325691.C (m + 4) + PA325691.DD (m + 4) + 1 := by
    exact_mod_cast PA325691.relC (m + 4)
  have hRC_6 : (PA325691.C (m + 9) : ℤ) = PA325691.C (m + 6) + PA325691.DD (m + 6) + 1 := by
    exact_mod_cast PA325691.relC (m + 6)
  have hRD_0 : (PA325691.DD (m + 4) : ℤ) = PA325691.DD m + PA325691.Par m := by
    exact_mod_cast PA325691.relD m
  have hRD_2 : (PA325691.DD (m + 6) : ℤ) = PA325691.DD (m + 2) + PA325691.Par (m + 2) := by
    exact_mod_cast PA325691.relD (m + 2)
  have hRP_0 : (PA325691.Par (m + 2) : ℤ) = PA325691.Par m := by
    exact_mod_cast PA325691.relP m
  linear_combination hRC_0 - hRC_2 - hRC_4 + hRC_6 - hRD_0 + hRD_2 + hRP_0
