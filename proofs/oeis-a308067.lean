import OMAStatements.S_oeis_a308067
import Mathlib

/-!
# A308067: Barker's recurrence

Write TO(r), TE(r) for the numbers of triangles (x, y, z), x <= y <= z < x + y, with perimeter r
and odd, even longest side. Adding 1 to every side maps the triples of perimeter r with
z <= x + y onto the triangles of perimeter r + 3 with smallest side at least 2, flipping the parity
of the longest side; the degenerate triples z = x + y exist only for even r, number floor(r/4), and
have longest side r/2; the only triangle with smallest side 1 is (1, s, s) for r + 3 = 2s + 1.
Hence TO(r + 3) = TE(r) + DE(r) + [r + 3 = 3 mod 4] and TE(r + 3) = TO(r) + DO(r) + [r + 3 = 1 mod 4],
where DE(r) = r/4 if r = 0 mod 4 and DO(r) = floor(r/4) if r = 2 mod 4 (and 0 otherwise). Writing
4 DE(r) = r [r = 0 mod 4] and 4 DO(r) = (r - 2) [r = 2 mod 4], Barker's operator applied to the
sequence is an explicit combination of these relations and of the shift relations of the residue
indicators mod 4, with coefficients linear in n.
-/

namespace PA308067
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

/-- Triangle indicator times the parity of the largest side. -/
def wO (x y z : ℕ) : ℕ := if z < y + x then z % 2 else 0

def wE (x y z : ℕ) : ℕ := if z < y + x then (z + 1) % 2 else 0

/-- Degenerate triples `z = x + y`, weighted by `g z`. -/
def dg (g : ℕ → ℕ) (x y z : ℕ) : ℕ := if z = y + x then g z else 0

def TO (r : ℕ) : ℕ := H3 wO r 1

def TE (r : ℕ) : ℕ := H3 wE r 1

def DE (r : ℕ) : ℕ := if r % 4 = 0 then r / 4 else 0

def DO (r : ℕ) : ℕ := if r % 4 = 2 then r / 4 else 0

def Ind (j r : ℕ) : ℕ := if r % 4 = j then 1 else 0

theorem deg_I3 (g : ℕ → ℕ) (r j : ℕ) (hj : 1 ≤ j) :
    I3 (dg g) r j = if r % 2 = 0 ∧ 4 * j ≤ r then g (r / 2) else 0 := by
  unfold I3 dg
  split_ifs with h
  · rw [Finset.sum_eq_single (r / 2 - 2 * j)]
    · rw [if_pos (by omega), show r - (j + (r / 2 - 2 * j)) - j = r / 2 by omega]
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

theorem cnt4 (r K : ℕ) :
    ∑ s ∈ Finset.range K, (if 4 * (1 + s) ≤ r then 1 else 0) = min K (r / 4) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

theorem deg_H3 (g : ℕ → ℕ) (r : ℕ) :
    H3 (dg g) r 1 = if r % 2 = 0 then g (r / 2) * (r / 4) else 0 := by
  unfold H3
  rw [Finset.sum_congr rfl fun s _ => deg_I3 g r (1 + s) (by omega)]
  by_cases hr : r % 2 = 0
  · rw [if_pos hr]
    simp only [hr, true_and]
    rw [show (∑ s ∈ Finset.range (r / 3 + 1 - 1), if 4 * (1 + s) ≤ r then g (r / 2) else 0) =
        g (r / 2) * ∑ s ∈ Finset.range (r / 3 + 1 - 1), if 4 * (1 + s) ≤ r then 1 else 0 by
      rw [Finset.mul_sum]
      simp only [mul_ite, mul_one, mul_zero], cnt4]
    congr 1
    omega
  · rw [if_neg hr]
    exact Finset.sum_eq_zero fun s _ => if_neg fun h => hr h.1

theorem sliceO (r : ℕ) : I3 wO (r + 3) 1 = Ind 3 (r + 3) := by
  unfold I3 wO Ind
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

theorem sliceE (r : ℕ) : I3 wE (r + 3) 1 = Ind 1 (r + 3) := by
  unfold I3 wE Ind
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

theorem DE_eq (r : ℕ) : (if r % 2 = 0 then (r / 2 + 1) % 2 * (r / 4) else 0) = DE r := by
  unfold DE
  by_cases h0 : r % 4 = 0
  · rw [if_pos (by omega), if_pos h0, show (r / 2 + 1) % 2 = 1 by omega, one_mul]
  · by_cases h2 : r % 2 = 0
    · rw [if_pos h2, if_neg h0, show (r / 2 + 1) % 2 = 0 by omega, zero_mul]
    · rw [if_neg h2, if_neg h0]

theorem DO_eq (r : ℕ) : (if r % 2 = 0 then r / 2 % 2 * (r / 4) else 0) = DO r := by
  unfold DO
  by_cases h0 : r % 4 = 2
  · rw [if_pos (by omega), if_pos h0, show r / 2 % 2 = 1 by omega, one_mul]
  · by_cases h2 : r % 2 = 0
    · rw [if_pos h2, if_neg h0, show r / 2 % 2 = 0 by omega, zero_mul]
    · rw [if_neg h2, if_neg h0]

theorem relA (r : ℕ) : TO (r + 3) = TE r + DE r + Ind 3 (r + 3) := by
  unfold TO TE
  rw [H3_peel, H3_congr _ (fun x y z => wE x y z + dg (fun z => (z + 1) % 2) x y z) r 1
    (fun x y z => by unfold wO wE dg; beta_reduce; split_ifs <;> omega), H3_add, deg_H3, sliceO, DE_eq]

theorem relB (r : ℕ) : TE (r + 3) = TO r + DO r + Ind 1 (r + 3) := by
  unfold TO TE
  rw [H3_peel, H3_congr _ (fun x y z => wO x y z + dg (fun z => z % 2) x y z) r 1
    (fun x y z => by unfold wO wE dg; beta_reduce; split_ifs <;> omega), H3_add, deg_H3, sliceE, DO_eq]

theorem relDE (r : ℕ) : 4 * DE r = r * Ind 0 r := by
  unfold DE Ind
  split_ifs <;> omega

theorem relDO (r : ℕ) : 4 * DO r + 2 * Ind 2 r = r * Ind 2 r := by
  unfold DO Ind
  split_ifs <;> omega

theorem relS0 (r : ℕ) : Ind 0 (r + 1) = Ind 3 r := by
  unfold Ind
  split_ifs <;> omega

theorem relS1 (r : ℕ) : Ind 1 (r + 1) = Ind 0 r := by
  unfold Ind
  split_ifs <;> omega

theorem relS2 (r : ℕ) : Ind 2 (r + 1) = Ind 1 r := by
  unfold Ind
  split_ifs <;> omega

theorem relS3 (r : ℕ) : Ind 3 (r + 1) = Ind 2 r := by
  unfold Ind
  split_ifs <;> omega

theorem relU (r : ℕ) : Ind 0 r + Ind 1 r + Ind 2 r + Ind 3 r = 1 := by
  unfold Ind
  split_ifs <;> omega

theorem a_eq (n : ℕ) : OMA.S_oeis_a308067.a n = TO n := by
  unfold OMA.S_oeis_a308067.a TO H3
  rw [icc_range']
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold I3 wO
  rw [icc_range']

end PA308067

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a308067.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 13 := ⟨n - 13, by omega⟩
  simp only [show m + 13 - 1 = m + 12 by omega, show m + 13 - 2 = m + 11 by omega, show m + 13 - 3 = m +
    10 by omega, show m + 13 - 4 = m + 9 by omega, show m + 13 - 5 = m + 8 by omega, show m + 13
    - 6 = m + 7 by omega, show m + 13 - 7 = m + 6 by omega, show m + 13 - 8 = m + 5 by omega,
    show m + 13 - 9 = m + 4 by omega, show m + 13 - 10 = m + 3 by omega, show m + 13 - 11 = m +
    2 by omega, show m + 13 - 12 = m + 1 by omega, show m + 13 - 13 = m by omega, PA308067.a_eq]
  qify
  have hA_3 : (PA308067.TO (m + 6) : ℚ) = PA308067.TE (m + 3) + PA308067.DE (m + 3) + PA308067.Ind 3 (m + 6) := by
    exact_mod_cast PA308067.relA (m + 3)
  have hA_4 : (PA308067.TO (m + 7) : ℚ) = PA308067.TE (m + 4) + PA308067.DE (m + 4) + PA308067.Ind 3 (m + 7) := by
    exact_mod_cast PA308067.relA (m + 4)
  have hA_5 : (PA308067.TO (m + 8) : ℚ) = PA308067.TE (m + 5) + PA308067.DE (m + 5) + PA308067.Ind 3 (m + 8) := by
    exact_mod_cast PA308067.relA (m + 5)
  have hA_6 : (PA308067.TO (m + 9) : ℚ) = PA308067.TE (m + 6) + PA308067.DE (m + 6) + PA308067.Ind 3 (m + 9) := by
    exact_mod_cast PA308067.relA (m + 6)
  have hA_7 : (PA308067.TO (m + 10) : ℚ) = PA308067.TE (m + 7) + PA308067.DE (m + 7) + PA308067.Ind 3 (m + 10) := by
    exact_mod_cast PA308067.relA (m + 7)
  have hA_8 : (PA308067.TO (m + 11) : ℚ) = PA308067.TE (m + 8) + PA308067.DE (m + 8) + PA308067.Ind 3 (m + 11) := by
    exact_mod_cast PA308067.relA (m + 8)
  have hA_9 : (PA308067.TO (m + 12) : ℚ) = PA308067.TE (m + 9) + PA308067.DE (m + 9) + PA308067.Ind 3 (m + 12) := by
    exact_mod_cast PA308067.relA (m + 9)
  have hA_10 : (PA308067.TO (m + 13) : ℚ) = PA308067.TE (m + 10) + PA308067.DE (m + 10) + PA308067.Ind 3 (m + 13) := by
    exact_mod_cast PA308067.relA (m + 10)
  have hB_0 : (PA308067.TE (m + 3) : ℚ) = PA308067.TO (m) + PA308067.DO (m) + PA308067.Ind 1 (m + 3) := by
    exact_mod_cast PA308067.relB (m)
  have hB_1 : (PA308067.TE (m + 4) : ℚ) = PA308067.TO (m + 1) + PA308067.DO (m + 1) + PA308067.Ind 1 (m + 4) := by
    exact_mod_cast PA308067.relB (m + 1)
  have hB_2 : (PA308067.TE (m + 5) : ℚ) = PA308067.TO (m + 2) + PA308067.DO (m + 2) + PA308067.Ind 1 (m + 5) := by
    exact_mod_cast PA308067.relB (m + 2)
  have hB_3 : (PA308067.TE (m + 6) : ℚ) = PA308067.TO (m + 3) + PA308067.DO (m + 3) + PA308067.Ind 1 (m + 6) := by
    exact_mod_cast PA308067.relB (m + 3)
  have hB_4 : (PA308067.TE (m + 7) : ℚ) = PA308067.TO (m + 4) + PA308067.DO (m + 4) + PA308067.Ind 1 (m + 7) := by
    exact_mod_cast PA308067.relB (m + 4)
  have hB_5 : (PA308067.TE (m + 8) : ℚ) = PA308067.TO (m + 5) + PA308067.DO (m + 5) + PA308067.Ind 1 (m + 8) := by
    exact_mod_cast PA308067.relB (m + 5)
  have hB_6 : (PA308067.TE (m + 9) : ℚ) = PA308067.TO (m + 6) + PA308067.DO (m + 6) + PA308067.Ind 1 (m + 9) := by
    exact_mod_cast PA308067.relB (m + 6)
  have hB_7 : (PA308067.TE (m + 10) : ℚ) = PA308067.TO (m + 7) + PA308067.DO (m + 7) + PA308067.Ind 1 (m + 10) := by
    exact_mod_cast PA308067.relB (m + 7)
  have hDE_3 : 4 * (PA308067.DE (m + 3) : ℚ) = ((m : ℚ) + 3) * PA308067.Ind 0 (m + 3) := by
    exact_mod_cast PA308067.relDE (m + 3)
  have hDE_4 : 4 * (PA308067.DE (m + 4) : ℚ) = ((m : ℚ) + 4) * PA308067.Ind 0 (m + 4) := by
    exact_mod_cast PA308067.relDE (m + 4)
  have hDE_5 : 4 * (PA308067.DE (m + 5) : ℚ) = ((m : ℚ) + 5) * PA308067.Ind 0 (m + 5) := by
    exact_mod_cast PA308067.relDE (m + 5)
  have hDE_6 : 4 * (PA308067.DE (m + 6) : ℚ) = ((m : ℚ) + 6) * PA308067.Ind 0 (m + 6) := by
    exact_mod_cast PA308067.relDE (m + 6)
  have hDE_7 : 4 * (PA308067.DE (m + 7) : ℚ) = ((m : ℚ) + 7) * PA308067.Ind 0 (m + 7) := by
    exact_mod_cast PA308067.relDE (m + 7)
  have hDE_8 : 4 * (PA308067.DE (m + 8) : ℚ) = ((m : ℚ) + 8) * PA308067.Ind 0 (m + 8) := by
    exact_mod_cast PA308067.relDE (m + 8)
  have hDE_9 : 4 * (PA308067.DE (m + 9) : ℚ) = ((m : ℚ) + 9) * PA308067.Ind 0 (m + 9) := by
    exact_mod_cast PA308067.relDE (m + 9)
  have hDE_10 : 4 * (PA308067.DE (m + 10) : ℚ) = ((m : ℚ) + 10) * PA308067.Ind 0 (m + 10) := by
    exact_mod_cast PA308067.relDE (m + 10)
  have hDO_0 : 4 * (PA308067.DO (m) : ℚ) + 2 * PA308067.Ind 2 (m) = (m : ℚ) * PA308067.Ind 2 (m) := by
    exact_mod_cast PA308067.relDO (m)
  have hDO_1 : 4 * (PA308067.DO (m + 1) : ℚ) + 2 * PA308067.Ind 2 (m + 1) = ((m : ℚ) + 1) * PA308067.Ind 2 (m + 1) := by
    exact_mod_cast PA308067.relDO (m + 1)
  have hDO_2 : 4 * (PA308067.DO (m + 2) : ℚ) + 2 * PA308067.Ind 2 (m + 2) = ((m : ℚ) + 2) * PA308067.Ind 2 (m + 2) := by
    exact_mod_cast PA308067.relDO (m + 2)
  have hDO_3 : 4 * (PA308067.DO (m + 3) : ℚ) + 2 * PA308067.Ind 2 (m + 3) = ((m : ℚ) + 3) * PA308067.Ind 2 (m + 3) := by
    exact_mod_cast PA308067.relDO (m + 3)
  have hDO_4 : 4 * (PA308067.DO (m + 4) : ℚ) + 2 * PA308067.Ind 2 (m + 4) = ((m : ℚ) + 4) * PA308067.Ind 2 (m + 4) := by
    exact_mod_cast PA308067.relDO (m + 4)
  have hDO_5 : 4 * (PA308067.DO (m + 5) : ℚ) + 2 * PA308067.Ind 2 (m + 5) = ((m : ℚ) + 5) * PA308067.Ind 2 (m + 5) := by
    exact_mod_cast PA308067.relDO (m + 5)
  have hDO_6 : 4 * (PA308067.DO (m + 6) : ℚ) + 2 * PA308067.Ind 2 (m + 6) = ((m : ℚ) + 6) * PA308067.Ind 2 (m + 6) := by
    exact_mod_cast PA308067.relDO (m + 6)
  have hDO_7 : 4 * (PA308067.DO (m + 7) : ℚ) + 2 * PA308067.Ind 2 (m + 7) = ((m : ℚ) + 7) * PA308067.Ind 2 (m + 7) := by
    exact_mod_cast PA308067.relDO (m + 7)
  have hS0_1 : (PA308067.Ind 0 (m + 2) : ℚ) = PA308067.Ind 3 (m + 1) := by
    exact_mod_cast PA308067.relS0 (m + 1)
  have hS0_2 : (PA308067.Ind 0 (m + 3) : ℚ) = PA308067.Ind 3 (m + 2) := by
    exact_mod_cast PA308067.relS0 (m + 2)
  have hS0_3 : (PA308067.Ind 0 (m + 4) : ℚ) = PA308067.Ind 3 (m + 3) := by
    exact_mod_cast PA308067.relS0 (m + 3)
  have hS0_4 : (PA308067.Ind 0 (m + 5) : ℚ) = PA308067.Ind 3 (m + 4) := by
    exact_mod_cast PA308067.relS0 (m + 4)
  have hS0_6 : (PA308067.Ind 0 (m + 7) : ℚ) = PA308067.Ind 3 (m + 6) := by
    exact_mod_cast PA308067.relS0 (m + 6)
  have hS0_7 : (PA308067.Ind 0 (m + 8) : ℚ) = PA308067.Ind 3 (m + 7) := by
    exact_mod_cast PA308067.relS0 (m + 7)
  have hS0_8 : (PA308067.Ind 0 (m + 9) : ℚ) = PA308067.Ind 3 (m + 8) := by
    exact_mod_cast PA308067.relS0 (m + 8)
  have hS0_9 : (PA308067.Ind 0 (m + 10) : ℚ) = PA308067.Ind 3 (m + 9) := by
    exact_mod_cast PA308067.relS0 (m + 9)
  have hS1_2 : (PA308067.Ind 1 (m + 3) : ℚ) = PA308067.Ind 0 (m + 2) := by
    exact_mod_cast PA308067.relS1 (m + 2)
  have hS1_3 : (PA308067.Ind 1 (m + 4) : ℚ) = PA308067.Ind 0 (m + 3) := by
    exact_mod_cast PA308067.relS1 (m + 3)
  have hS1_4 : (PA308067.Ind 1 (m + 5) : ℚ) = PA308067.Ind 0 (m + 4) := by
    exact_mod_cast PA308067.relS1 (m + 4)
  have hS1_5 : (PA308067.Ind 1 (m + 6) : ℚ) = PA308067.Ind 0 (m + 5) := by
    exact_mod_cast PA308067.relS1 (m + 5)
  have hS1_6 : (PA308067.Ind 1 (m + 7) : ℚ) = PA308067.Ind 0 (m + 6) := by
    exact_mod_cast PA308067.relS1 (m + 6)
  have hS1_10 : (PA308067.Ind 1 (m + 11) : ℚ) = PA308067.Ind 0 (m + 10) := by
    exact_mod_cast PA308067.relS1 (m + 10)
  have hS2_3 : (PA308067.Ind 2 (m + 4) : ℚ) = PA308067.Ind 1 (m + 3) := by
    exact_mod_cast PA308067.relS2 (m + 3)
  have hS2_7 : (PA308067.Ind 2 (m + 8) : ℚ) = PA308067.Ind 1 (m + 7) := by
    exact_mod_cast PA308067.relS2 (m + 7)
  have hS2_8 : (PA308067.Ind 2 (m + 9) : ℚ) = PA308067.Ind 1 (m + 8) := by
    exact_mod_cast PA308067.relS2 (m + 8)
  have hS2_9 : (PA308067.Ind 2 (m + 10) : ℚ) = PA308067.Ind 1 (m + 9) := by
    exact_mod_cast PA308067.relS2 (m + 9)
  have hS2_10 : (PA308067.Ind 2 (m + 11) : ℚ) = PA308067.Ind 1 (m + 10) := by
    exact_mod_cast PA308067.relS2 (m + 10)
  have hS2_11 : (PA308067.Ind 2 (m + 12) : ℚ) = PA308067.Ind 1 (m + 11) := by
    exact_mod_cast PA308067.relS2 (m + 11)
  have hS3_0 : (PA308067.Ind 3 (m + 1) : ℚ) = PA308067.Ind 2 (m) := by
    exact_mod_cast PA308067.relS3 (m)
  have hS3_1 : (PA308067.Ind 3 (m + 2) : ℚ) = PA308067.Ind 2 (m + 1) := by
    exact_mod_cast PA308067.relS3 (m + 1)
  have hS3_2 : (PA308067.Ind 3 (m + 3) : ℚ) = PA308067.Ind 2 (m + 2) := by
    exact_mod_cast PA308067.relS3 (m + 2)
  have hS3_3 : (PA308067.Ind 3 (m + 4) : ℚ) = PA308067.Ind 2 (m + 3) := by
    exact_mod_cast PA308067.relS3 (m + 3)
  have hS3_5 : (PA308067.Ind 3 (m + 6) : ℚ) = PA308067.Ind 2 (m + 5) := by
    exact_mod_cast PA308067.relS3 (m + 5)
  have hS3_6 : (PA308067.Ind 3 (m + 7) : ℚ) = PA308067.Ind 2 (m + 6) := by
    exact_mod_cast PA308067.relS3 (m + 6)
  have hS3_7 : (PA308067.Ind 3 (m + 8) : ℚ) = PA308067.Ind 2 (m + 7) := by
    exact_mod_cast PA308067.relS3 (m + 7)
  have hS3_8 : (PA308067.Ind 3 (m + 9) : ℚ) = PA308067.Ind 2 (m + 8) := by
    exact_mod_cast PA308067.relS3 (m + 8)
  have hS3_9 : (PA308067.Ind 3 (m + 10) : ℚ) = PA308067.Ind 2 (m + 9) := by
    exact_mod_cast PA308067.relS3 (m + 9)
  have hS3_10 : (PA308067.Ind 3 (m + 11) : ℚ) = PA308067.Ind 2 (m + 10) := by
    exact_mod_cast PA308067.relS3 (m + 10)
  have hS3_11 : (PA308067.Ind 3 (m + 12) : ℚ) = PA308067.Ind 2 (m + 11) := by
    exact_mod_cast PA308067.relS3 (m + 11)
  have hS3_12 : (PA308067.Ind 3 (m + 13) : ℚ) = PA308067.Ind 2 (m + 12) := by
    exact_mod_cast PA308067.relS3 (m + 12)
  linear_combination ((1 : ℚ)) * hA_3 + ((-1 : ℚ)) * hA_4 + ((1 : ℚ)) * hA_5 + ((-1 : ℚ)) * hA_6 + ((-1 : ℚ)) *
    hA_7 + ((1 : ℚ)) * hA_8 + ((-1 : ℚ)) * hA_9 + ((1 : ℚ)) * hA_10 + ((1 : ℚ)) * hB_0 + ((-1 :
    ℚ)) * hB_1 + ((1 : ℚ)) * hB_2 + ((-1 : ℚ)) * hB_3 + ((-1 : ℚ)) * hB_4 + ((1 : ℚ)) * hB_5 +
    ((-1 : ℚ)) * hB_6 + ((1 : ℚ)) * hB_7 + ((1 / 4 : ℚ)) * hDE_3 + ((-1 / 4 : ℚ)) * hDE_4 + ((1
    / 4 : ℚ)) * hDE_5 + ((-1 / 4 : ℚ)) * hDE_6 + ((-1 / 4 : ℚ)) * hDE_7 + ((1 / 4 : ℚ)) * hDE_8
    + ((-1 / 4 : ℚ)) * hDE_9 + ((1 / 4 : ℚ)) * hDE_10 + ((1 / 4 : ℚ)) * hDO_0 + ((-1 / 4 : ℚ)) *
    hDO_1 + ((1 / 4 : ℚ)) * hDO_2 + ((-1 / 4 : ℚ)) * hDO_3 + ((-1 / 4 : ℚ)) * hDO_4 + ((1 / 4 :
    ℚ)) * hDO_5 + ((-1 / 4 : ℚ)) * hDO_6 + ((1 / 4 : ℚ)) * hDO_7 + ((1 / 2 : ℚ) + (-1 / 4 : ℚ) *
    (m : ℚ)) * hS0_1 + ((-1 / 4 : ℚ) + (1 / 4 : ℚ) * (m : ℚ)) * hS0_2 + ((-1 / 4 : ℚ) * (m : ℚ))
    * hS0_3 + ((1 / 4 : ℚ) + (1 / 4 : ℚ) * (m : ℚ)) * hS0_4 + ((-7 / 4 : ℚ) + (-1 / 4 : ℚ) * (m
    : ℚ)) * hS0_6 + ((2 : ℚ) + (1 / 4 : ℚ) * (m : ℚ)) * hS0_7 + ((-9 / 4 : ℚ) + (-1 / 4 : ℚ) *
    (m : ℚ)) * hS0_8 + ((7 / 2 : ℚ) + (1 / 4 : ℚ) * (m : ℚ)) * hS0_9 + ((1 / 2 : ℚ) + (-1 / 4 :
    ℚ) * (m : ℚ)) * hS1_2 + ((-1 : ℚ)) * hS1_3 + ((1 : ℚ)) * hS1_4 + ((-1 : ℚ)) * hS1_5 + ((3 /
    2 : ℚ) + (1 / 4 : ℚ) * (m : ℚ)) * hS1_6 + ((1 : ℚ)) * hS1_10 + ((-1 / 2 : ℚ) + (-1 / 4 : ℚ)
    * (m : ℚ)) * hS2_3 + ((5 / 2 : ℚ) + (1 / 4 : ℚ) * (m : ℚ)) * hS2_7 + ((-1 : ℚ)) * hS2_8 +
    ((1 : ℚ)) * hS2_9 + ((-1 : ℚ)) * hS2_10 + ((1 : ℚ)) * hS2_11 + ((1 / 2 : ℚ) + (-1 / 4 : ℚ) *
    (m : ℚ)) * hS3_0 + ((-1 / 4 : ℚ) + (1 / 4 : ℚ) * (m : ℚ)) * hS3_1 + ((-1 / 4 : ℚ) * (m : ℚ))
    * hS3_2 + ((1 / 4 : ℚ) + (1 / 4 : ℚ) * (m : ℚ)) * hS3_3 + ((-3 / 4 : ℚ) + (-1 / 4 : ℚ) * (m
    : ℚ)) * hS3_5 + ((1 : ℚ) + (1 / 4 : ℚ) * (m : ℚ)) * hS3_6 + ((-5 / 4 : ℚ) + (-1 / 4 : ℚ) *
    (m : ℚ)) * hS3_7 + ((5 / 2 : ℚ) + (1 / 4 : ℚ) * (m : ℚ)) * hS3_8 + ((-1 : ℚ)) * hS3_9 + ((1
    : ℚ)) * hS3_10 + ((-1 : ℚ)) * hS3_11 + ((1 : ℚ)) * hS3_12
