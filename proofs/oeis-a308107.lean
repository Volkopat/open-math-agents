import OMAStatements.S_oeis_a308107
import Mathlib

/-!
# A308107: Barker's recurrence

Write S(r), N(r) for the sum of the smallest sides and the number of the scalene triangles
x < y < z < x + y with perimeter r. Adding 1 to every side maps the triples of perimeter r with
x < y < z <= x + y onto the scalene triangles of perimeter r + 3 with smallest side at least 2,
and there is no scalene triangle with smallest side 1. The degenerate triples x < y, z = x + y
exist only for even r, with x = 1, ..., c, c = floor((r - 1)/4), so their number DN(r) and the sum
DS(r) of their smallest sides satisfy 4 DN(r) = (r - 4)[r = 0 mod 4] + (r - 2)[r = 2 mod 4] (r >= 1)
and 32 DS(r) = (r^2 - 4r)[r = 0 mod 4] + (r^2 - 4)[r = 2 mod 4]. Hence S(r + 3) = S(r) + N(r) +
DS(r) + DN(r) and N(r + 3) = N(r) + DN(r), and Barker's operator applied to S is an explicit
combination of these relations and of the shift relations of the residue indicators mod 4, with
coefficients quadratic in n (computed over ℚ).
-/

namespace PA308107
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

def ws (x y z : ℕ) : ℕ := if x < y ∧ y < z ∧ z < y + x then x else 0

def wn (x y z : ℕ) : ℕ := if x < y ∧ y < z ∧ z < y + x then 1 else 0

def ds (x y z : ℕ) : ℕ := if 0 < x ∧ x < y ∧ z = y + x then x else 0

def dn (x y z : ℕ) : ℕ := if 0 < x ∧ x < y ∧ z = y + x then 1 else 0

def S (r : ℕ) : ℕ := H3 ws r 1

def N (r : ℕ) : ℕ := H3 wn r 1

def DS (r : ℕ) : ℕ := H3 ds r 1

def DN (r : ℕ) : ℕ := H3 dn r 1

def Ind (j r : ℕ) : ℕ := if r % 4 = j then 1 else 0

theorem slice_zero (w : ℕ → ℕ → ℕ → ℕ) (r : ℕ)
    (h : ∀ y z, ¬ (1 < y ∧ y < z ∧ z < y + 1) → w 1 y z = 0) : I3 w (r + 3) 1 = 0 := by
  unfold I3
  exact Finset.sum_eq_zero fun u _ => h _ _ (by omega)

theorem relA (r : ℕ) : S (r + 3) = S r + N r + DS r + DN r := by
  unfold S N DS DN
  rw [H3_peel, H3_congr _ (fun x y z => ws x y z + wn x y z + (ds x y z + dn x y z)) r 1
    (fun x y z => by unfold ws wn ds dn; split_ifs <;> omega), H3_add, H3_add, H3_add,
    slice_zero ws r (fun y z h => by unfold ws; rw [if_neg (by omega)])]
  ring

theorem relB (r : ℕ) : N (r + 3) = N r + DN r := by
  unfold N DN
  rw [H3_peel, H3_congr _ (fun x y z => wn x y z + dn x y z) r 1
    (fun x y z => by unfold wn dn; split_ifs <;> omega), H3_add,
    slice_zero wn r (fun y z h => by unfold wn; rw [if_neg (by omega)])]
  ring

theorem I3_dn (r j : ℕ) (hj : 1 ≤ j) :
    I3 dn r j = if r % 2 = 0 ∧ 4 * j < r then 1 else 0 := by
  unfold I3 dn
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

theorem I3_ds (r j : ℕ) (hj : 1 ≤ j) :
    I3 ds r j = if r % 2 = 0 ∧ 4 * j < r then j else 0 := by
  unfold I3 ds
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

theorem cntN (r K : ℕ) :
    ∑ s ∈ Finset.range K, (if r % 2 = 0 ∧ 4 * (1 + s) < r then 1 else 0) =
      if r % 2 = 0 then min K ((r - 1) / 4) else 0 := by
  induction K with
  | zero => split_ifs <;> simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    split_ifs <;> omega

theorem cntS (r K : ℕ) :
    ∑ s ∈ Finset.range K, (if r % 2 = 0 ∧ 4 * (1 + s) < r then 1 + s else 0) =
      if r % 2 = 0 then ∑ s ∈ Finset.range (min K ((r - 1) / 4)), (1 + s) else 0 := by
  induction K with
  | zero => split_ifs <;> simp
  | succ K ih =>
    rw [Finset.sum_range_succ, ih]
    by_cases h0 : r % 2 = 0
    · by_cases h1 : 4 * (1 + K) < r
      · rw [if_pos h0, if_pos ⟨h0, h1⟩, if_pos h0, show min (K + 1) ((r - 1) / 4) = K + 1 by omega,
          show min K ((r - 1) / 4) = K by omega, Finset.sum_range_succ]
      · rw [if_pos h0, if_neg (fun h => h1 h.2), if_pos h0,
          show min (K + 1) ((r - 1) / 4) = min K ((r - 1) / 4) by omega, Nat.add_zero]
    · rw [if_neg h0, if_neg (fun h => h0 h.1), if_neg h0]

theorem gauss (c : ℕ) : 2 * ∑ s ∈ Finset.range c, (1 + s) = c * (c + 1) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    ring

theorem DN_eq (r : ℕ) : DN r = if r % 2 = 0 then (r - 1) / 4 else 0 := by
  unfold DN H3
  rw [Finset.sum_congr rfl fun s _ => I3_dn r (1 + s) (by omega), cntN]
  split_ifs <;> omega

theorem DS_eq (r : ℕ) :
    DS r = if r % 2 = 0 then ∑ s ∈ Finset.range ((r - 1) / 4), (1 + s) else 0 := by
  unfold DS H3
  rw [Finset.sum_congr rfl fun s _ => I3_ds r (1 + s) (by omega), cntS,
    show min (r / 3 + 1 - 1) ((r - 1) / 4) = (r - 1) / 4 by omega]

theorem relDN (r : ℕ) (hr : 1 ≤ r) :
    4 * DN r + 4 * Ind 0 r + 2 * Ind 2 r = r * Ind 0 r + r * Ind 2 r := by
  rw [DN_eq]
  unfold Ind
  split_ifs <;> omega

theorem relDS (r : ℕ) :
    32 * DS r + 4 * r * Ind 0 r + 4 * Ind 2 r = r * r * Ind 0 r + r * r * Ind 2 r := by
  have hg := gauss ((r - 1) / 4)
  rw [DS_eq]
  unfold Ind
  generalize ∑ s ∈ Finset.range ((r - 1) / 4), (1 + s) = G at hg ⊢
  obtain ⟨q, hq⟩ : ∃ q, q = r / 4 := ⟨_, rfl⟩
  by_cases h0 : r % 4 = 0
  · rw [if_pos (by omega), if_pos h0, if_neg (by omega)]
    rcases Nat.eq_zero_or_pos q with hq0 | hq0
    · have : r = 0 := by omega
      subst this
      simp at hg ⊢
      omega
    · have hc : (r - 1) / 4 + 1 = q := by omega
      have hr : r = 4 * q := by omega
      subst hr
      nlinarith [hg, hc]
  · by_cases h2 : r % 4 = 2
    · rw [if_pos (by omega), if_neg h0, if_pos h2]
      have hc : (r - 1) / 4 = q := by omega
      have hr : r = 4 * q + 2 := by omega
      rw [hc] at hg
      subst hr
      nlinarith [hg]
    · rw [if_neg (by omega), if_neg h0, if_neg h2]
      ring

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

theorem a_eq (n : ℕ) : OMA.S_oeis_a308107.a n = S n := by
  unfold OMA.S_oeis_a308107.a S H3
  rw [icc_range']
  refine Finset.sum_congr rfl fun s _ => ?_
  unfold I3 ws
  rw [icc_range']

end PA308107

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a308107.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 15 := ⟨n - 15, by omega⟩
  have hm : 1 ≤ m := by omega
  simp only [show m + 15 - 1 = m + 14 by omega, show m + 15 - 3 = m + 12 by omega, show m + 15 - 4 = m +
    11 by omega, show m + 15 - 5 = m + 10 by omega, show m + 15 - 6 = m + 9 by omega, show m +
    15 - 7 = m + 8 by omega, show m + 15 - 8 = m + 7 by omega, show m + 15 - 9 = m + 6 by omega,
    show m + 15 - 10 = m + 5 by omega, show m + 15 - 11 = m + 4 by omega, show m + 15 - 12 = m +
    3 by omega, show m + 15 - 14 = m + 1 by omega, show m + 15 - 15 = m by omega, PA308107.a_eq]
  qify
  have hA_0 : (PA308107.S (m + 3) : ℚ) = PA308107.S (m) + PA308107.N (m) + PA308107.DS (m) + PA308107.DN (m) := by
    exact_mod_cast PA308107.relA (m)
  have hA_1 : (PA308107.S (m + 4) : ℚ) = PA308107.S (m + 1) + PA308107.N (m + 1) + PA308107.DS (m + 1) + PA308107.DN (m + 1) := by
    exact_mod_cast PA308107.relA (m + 1)
  have hA_3 : (PA308107.S (m + 6) : ℚ) = PA308107.S (m + 3) + PA308107.N (m + 3) + PA308107.DS (m + 3) + PA308107.DN (m + 3) := by
    exact_mod_cast PA308107.relA (m + 3)
  have hA_4 : (PA308107.S (m + 7) : ℚ) = PA308107.S (m + 4) + PA308107.N (m + 4) + PA308107.DS (m + 4) + PA308107.DN (m + 4) := by
    exact_mod_cast PA308107.relA (m + 4)
  have hA_5 : (PA308107.S (m + 8) : ℚ) = PA308107.S (m + 5) + PA308107.N (m + 5) + PA308107.DS (m + 5) + PA308107.DN (m + 5) := by
    exact_mod_cast PA308107.relA (m + 5)
  have hA_7 : (PA308107.S (m + 10) : ℚ) = PA308107.S (m + 7) + PA308107.N (m + 7) + PA308107.DS (m + 7) + PA308107.DN (m + 7) := by
    exact_mod_cast PA308107.relA (m + 7)
  have hA_8 : (PA308107.S (m + 11) : ℚ) = PA308107.S (m + 8) + PA308107.N (m + 8) + PA308107.DS (m + 8) + PA308107.DN (m + 8) := by
    exact_mod_cast PA308107.relA (m + 8)
  have hA_9 : (PA308107.S (m + 12) : ℚ) = PA308107.S (m + 9) + PA308107.N (m + 9) + PA308107.DS (m + 9) + PA308107.DN (m + 9) := by
    exact_mod_cast PA308107.relA (m + 9)
  have hA_11 : (PA308107.S (m + 14) : ℚ) = PA308107.S (m + 11) + PA308107.N (m + 11) + PA308107.DS (m + 11) + PA308107.DN (m + 11) := by
    exact_mod_cast PA308107.relA (m + 11)
  have hA_12 : (PA308107.S (m + 15) : ℚ) = PA308107.S (m + 12) + PA308107.N (m + 12) + PA308107.DS (m + 12) + PA308107.DN (m + 12) := by
    exact_mod_cast PA308107.relA (m + 12)
  have hB_0 : (PA308107.N (m + 3) : ℚ) = PA308107.N (m) + PA308107.DN (m) := by
    exact_mod_cast PA308107.relB (m)
  have hB_1 : (PA308107.N (m + 4) : ℚ) = PA308107.N (m + 1) + PA308107.DN (m + 1) := by
    exact_mod_cast PA308107.relB (m + 1)
  have hB_4 : (PA308107.N (m + 7) : ℚ) = PA308107.N (m + 4) + PA308107.DN (m + 4) := by
    exact_mod_cast PA308107.relB (m + 4)
  have hB_5 : (PA308107.N (m + 8) : ℚ) = PA308107.N (m + 5) + PA308107.DN (m + 5) := by
    exact_mod_cast PA308107.relB (m + 5)
  have hB_8 : (PA308107.N (m + 11) : ℚ) = PA308107.N (m + 8) + PA308107.DN (m + 8) := by
    exact_mod_cast PA308107.relB (m + 8)
  have hB_9 : (PA308107.N (m + 12) : ℚ) = PA308107.N (m + 9) + PA308107.DN (m + 9) := by
    exact_mod_cast PA308107.relB (m + 9)
  have hDN_3 : 4 * (PA308107.DN (m + 3) : ℚ) + 4 * PA308107.Ind 0 (m + 3) + 2 * PA308107.Ind 2 (m + 3) = ((m : ℚ) + 3) * PA308107.Ind 0 (m + 3) + ((m : ℚ) + 3) * PA308107.Ind 2 (m + 3) := by
    exact_mod_cast PA308107.relDN (m + 3) (by omega)
  have hDN_4 : 4 * (PA308107.DN (m + 4) : ℚ) + 4 * PA308107.Ind 0 (m + 4) + 2 * PA308107.Ind 2 (m + 4) = ((m : ℚ) + 4) * PA308107.Ind 0 (m + 4) + ((m : ℚ) + 4) * PA308107.Ind 2 (m + 4) := by
    exact_mod_cast PA308107.relDN (m + 4) (by omega)
  have hDN_7 : 4 * (PA308107.DN (m + 7) : ℚ) + 4 * PA308107.Ind 0 (m + 7) + 2 * PA308107.Ind 2 (m + 7) = ((m : ℚ) + 7) * PA308107.Ind 0 (m + 7) + ((m : ℚ) + 7) * PA308107.Ind 2 (m + 7) := by
    exact_mod_cast PA308107.relDN (m + 7) (by omega)
  have hDN_8 : 4 * (PA308107.DN (m + 8) : ℚ) + 4 * PA308107.Ind 0 (m + 8) + 2 * PA308107.Ind 2 (m + 8) = ((m : ℚ) + 8) * PA308107.Ind 0 (m + 8) + ((m : ℚ) + 8) * PA308107.Ind 2 (m + 8) := by
    exact_mod_cast PA308107.relDN (m + 8) (by omega)
  have hDN_11 : 4 * (PA308107.DN (m + 11) : ℚ) + 4 * PA308107.Ind 0 (m + 11) + 2 * PA308107.Ind 2 (m + 11) = ((m : ℚ) + 11) * PA308107.Ind 0 (m + 11) + ((m : ℚ) + 11) * PA308107.Ind 2 (m + 11) := by
    exact_mod_cast PA308107.relDN (m + 11) (by omega)
  have hDN_12 : 4 * (PA308107.DN (m + 12) : ℚ) + 4 * PA308107.Ind 0 (m + 12) + 2 * PA308107.Ind 2 (m + 12) = ((m : ℚ) + 12) * PA308107.Ind 0 (m + 12) + ((m : ℚ) + 12) * PA308107.Ind 2 (m + 12) := by
    exact_mod_cast PA308107.relDN (m + 12) (by omega)
  have hDS_0 : 32 * (PA308107.DS (m) : ℚ) + 4 * (m : ℚ) * PA308107.Ind 0 (m) + 4 * PA308107.Ind 2 (m) = (m : ℚ) * (m : ℚ) * PA308107.Ind 0 (m) + (m : ℚ) * (m : ℚ) * PA308107.Ind 2 (m) := by
    exact_mod_cast PA308107.relDS (m)
  have hDS_1 : 32 * (PA308107.DS (m + 1) : ℚ) + 4 * ((m : ℚ) + 1) * PA308107.Ind 0 (m + 1) + 4 * PA308107.Ind 2 (m + 1) = ((m : ℚ) + 1) * ((m : ℚ) + 1) * PA308107.Ind 0 (m + 1) + ((m : ℚ) + 1) * ((m : ℚ) + 1) * PA308107.Ind 2 (m + 1) := by
    exact_mod_cast PA308107.relDS (m + 1)
  have hDS_3 : 32 * (PA308107.DS (m + 3) : ℚ) + 4 * ((m : ℚ) + 3) * PA308107.Ind 0 (m + 3) + 4 * PA308107.Ind 2 (m + 3) = ((m : ℚ) + 3) * ((m : ℚ) + 3) * PA308107.Ind 0 (m + 3) + ((m : ℚ) + 3) * ((m : ℚ) + 3) * PA308107.Ind 2 (m + 3) := by
    exact_mod_cast PA308107.relDS (m + 3)
  have hDS_4 : 32 * (PA308107.DS (m + 4) : ℚ) + 4 * ((m : ℚ) + 4) * PA308107.Ind 0 (m + 4) + 4 * PA308107.Ind 2 (m + 4) = ((m : ℚ) + 4) * ((m : ℚ) + 4) * PA308107.Ind 0 (m + 4) + ((m : ℚ) + 4) * ((m : ℚ) + 4) * PA308107.Ind 2 (m + 4) := by
    exact_mod_cast PA308107.relDS (m + 4)
  have hDS_5 : 32 * (PA308107.DS (m + 5) : ℚ) + 4 * ((m : ℚ) + 5) * PA308107.Ind 0 (m + 5) + 4 * PA308107.Ind 2 (m + 5) = ((m : ℚ) + 5) * ((m : ℚ) + 5) * PA308107.Ind 0 (m + 5) + ((m : ℚ) + 5) * ((m : ℚ) + 5) * PA308107.Ind 2 (m + 5) := by
    exact_mod_cast PA308107.relDS (m + 5)
  have hDS_7 : 32 * (PA308107.DS (m + 7) : ℚ) + 4 * ((m : ℚ) + 7) * PA308107.Ind 0 (m + 7) + 4 * PA308107.Ind 2 (m + 7) = ((m : ℚ) + 7) * ((m : ℚ) + 7) * PA308107.Ind 0 (m + 7) + ((m : ℚ) + 7) * ((m : ℚ) + 7) * PA308107.Ind 2 (m + 7) := by
    exact_mod_cast PA308107.relDS (m + 7)
  have hDS_8 : 32 * (PA308107.DS (m + 8) : ℚ) + 4 * ((m : ℚ) + 8) * PA308107.Ind 0 (m + 8) + 4 * PA308107.Ind 2 (m + 8) = ((m : ℚ) + 8) * ((m : ℚ) + 8) * PA308107.Ind 0 (m + 8) + ((m : ℚ) + 8) * ((m : ℚ) + 8) * PA308107.Ind 2 (m + 8) := by
    exact_mod_cast PA308107.relDS (m + 8)
  have hDS_9 : 32 * (PA308107.DS (m + 9) : ℚ) + 4 * ((m : ℚ) + 9) * PA308107.Ind 0 (m + 9) + 4 * PA308107.Ind 2 (m + 9) = ((m : ℚ) + 9) * ((m : ℚ) + 9) * PA308107.Ind 0 (m + 9) + ((m : ℚ) + 9) * ((m : ℚ) + 9) * PA308107.Ind 2 (m + 9) := by
    exact_mod_cast PA308107.relDS (m + 9)
  have hDS_11 : 32 * (PA308107.DS (m + 11) : ℚ) + 4 * ((m : ℚ) + 11) * PA308107.Ind 0 (m + 11) + 4 * PA308107.Ind 2 (m + 11) = ((m : ℚ) + 11) * ((m : ℚ) + 11) * PA308107.Ind 0 (m + 11) + ((m : ℚ) + 11) * ((m : ℚ) + 11) * PA308107.Ind 2 (m + 11) := by
    exact_mod_cast PA308107.relDS (m + 11)
  have hDS_12 : 32 * (PA308107.DS (m + 12) : ℚ) + 4 * ((m : ℚ) + 12) * PA308107.Ind 0 (m + 12) + 4 * PA308107.Ind 2 (m + 12) = ((m : ℚ) + 12) * ((m : ℚ) + 12) * PA308107.Ind 0 (m + 12) + ((m : ℚ) + 12) * ((m : ℚ) + 12) * PA308107.Ind 2 (m + 12) := by
    exact_mod_cast PA308107.relDS (m + 12)
  have hS0_1 : (PA308107.Ind 0 (m + 2) : ℚ) = PA308107.Ind 3 (m + 1) := by
    exact_mod_cast PA308107.relS0 (m + 1)
  have hS0_2 : (PA308107.Ind 0 (m + 3) : ℚ) = PA308107.Ind 3 (m + 2) := by
    exact_mod_cast PA308107.relS0 (m + 2)
  have hS0_3 : (PA308107.Ind 0 (m + 4) : ℚ) = PA308107.Ind 3 (m + 3) := by
    exact_mod_cast PA308107.relS0 (m + 3)
  have hS0_4 : (PA308107.Ind 0 (m + 5) : ℚ) = PA308107.Ind 3 (m + 4) := by
    exact_mod_cast PA308107.relS0 (m + 4)
  have hS0_5 : (PA308107.Ind 0 (m + 6) : ℚ) = PA308107.Ind 3 (m + 5) := by
    exact_mod_cast PA308107.relS0 (m + 5)
  have hS0_6 : (PA308107.Ind 0 (m + 7) : ℚ) = PA308107.Ind 3 (m + 6) := by
    exact_mod_cast PA308107.relS0 (m + 6)
  have hS0_7 : (PA308107.Ind 0 (m + 8) : ℚ) = PA308107.Ind 3 (m + 7) := by
    exact_mod_cast PA308107.relS0 (m + 7)
  have hS0_8 : (PA308107.Ind 0 (m + 9) : ℚ) = PA308107.Ind 3 (m + 8) := by
    exact_mod_cast PA308107.relS0 (m + 8)
  have hS0_9 : (PA308107.Ind 0 (m + 10) : ℚ) = PA308107.Ind 3 (m + 9) := by
    exact_mod_cast PA308107.relS0 (m + 9)
  have hS0_10 : (PA308107.Ind 0 (m + 11) : ℚ) = PA308107.Ind 3 (m + 10) := by
    exact_mod_cast PA308107.relS0 (m + 10)
  have hS0_11 : (PA308107.Ind 0 (m + 12) : ℚ) = PA308107.Ind 3 (m + 11) := by
    exact_mod_cast PA308107.relS0 (m + 11)
  have hS1_0 : (PA308107.Ind 1 (m + 1) : ℚ) = PA308107.Ind 0 (m) := by
    exact_mod_cast PA308107.relS1 (m)
  have hS1_1 : (PA308107.Ind 1 (m + 2) : ℚ) = PA308107.Ind 0 (m + 1) := by
    exact_mod_cast PA308107.relS1 (m + 1)
  have hS1_2 : (PA308107.Ind 1 (m + 3) : ℚ) = PA308107.Ind 0 (m + 2) := by
    exact_mod_cast PA308107.relS1 (m + 2)
  have hS1_3 : (PA308107.Ind 1 (m + 4) : ℚ) = PA308107.Ind 0 (m + 3) := by
    exact_mod_cast PA308107.relS1 (m + 3)
  have hS1_4 : (PA308107.Ind 1 (m + 5) : ℚ) = PA308107.Ind 0 (m + 4) := by
    exact_mod_cast PA308107.relS1 (m + 4)
  have hS1_5 : (PA308107.Ind 1 (m + 6) : ℚ) = PA308107.Ind 0 (m + 5) := by
    exact_mod_cast PA308107.relS1 (m + 5)
  have hS1_6 : (PA308107.Ind 1 (m + 7) : ℚ) = PA308107.Ind 0 (m + 6) := by
    exact_mod_cast PA308107.relS1 (m + 6)
  have hS1_7 : (PA308107.Ind 1 (m + 8) : ℚ) = PA308107.Ind 0 (m + 7) := by
    exact_mod_cast PA308107.relS1 (m + 7)
  have hS1_8 : (PA308107.Ind 1 (m + 9) : ℚ) = PA308107.Ind 0 (m + 8) := by
    exact_mod_cast PA308107.relS1 (m + 8)
  have hS1_9 : (PA308107.Ind 1 (m + 10) : ℚ) = PA308107.Ind 0 (m + 9) := by
    exact_mod_cast PA308107.relS1 (m + 9)
  have hS1_10 : (PA308107.Ind 1 (m + 11) : ℚ) = PA308107.Ind 0 (m + 10) := by
    exact_mod_cast PA308107.relS1 (m + 10)
  have hS2_1 : (PA308107.Ind 2 (m + 2) : ℚ) = PA308107.Ind 1 (m + 1) := by
    exact_mod_cast PA308107.relS2 (m + 1)
  have hS2_2 : (PA308107.Ind 2 (m + 3) : ℚ) = PA308107.Ind 1 (m + 2) := by
    exact_mod_cast PA308107.relS2 (m + 2)
  have hS2_3 : (PA308107.Ind 2 (m + 4) : ℚ) = PA308107.Ind 1 (m + 3) := by
    exact_mod_cast PA308107.relS2 (m + 3)
  have hS2_4 : (PA308107.Ind 2 (m + 5) : ℚ) = PA308107.Ind 1 (m + 4) := by
    exact_mod_cast PA308107.relS2 (m + 4)
  have hS2_5 : (PA308107.Ind 2 (m + 6) : ℚ) = PA308107.Ind 1 (m + 5) := by
    exact_mod_cast PA308107.relS2 (m + 5)
  have hS2_6 : (PA308107.Ind 2 (m + 7) : ℚ) = PA308107.Ind 1 (m + 6) := by
    exact_mod_cast PA308107.relS2 (m + 6)
  have hS2_7 : (PA308107.Ind 2 (m + 8) : ℚ) = PA308107.Ind 1 (m + 7) := by
    exact_mod_cast PA308107.relS2 (m + 7)
  have hS2_8 : (PA308107.Ind 2 (m + 9) : ℚ) = PA308107.Ind 1 (m + 8) := by
    exact_mod_cast PA308107.relS2 (m + 8)
  have hS2_9 : (PA308107.Ind 2 (m + 10) : ℚ) = PA308107.Ind 1 (m + 9) := by
    exact_mod_cast PA308107.relS2 (m + 9)
  have hS2_10 : (PA308107.Ind 2 (m + 11) : ℚ) = PA308107.Ind 1 (m + 10) := by
    exact_mod_cast PA308107.relS2 (m + 10)
  have hS2_11 : (PA308107.Ind 2 (m + 12) : ℚ) = PA308107.Ind 1 (m + 11) := by
    exact_mod_cast PA308107.relS2 (m + 11)
  have hS3_0 : (PA308107.Ind 3 (m + 1) : ℚ) = PA308107.Ind 2 (m) := by
    exact_mod_cast PA308107.relS3 (m)
  have hS3_1 : (PA308107.Ind 3 (m + 2) : ℚ) = PA308107.Ind 2 (m + 1) := by
    exact_mod_cast PA308107.relS3 (m + 1)
  have hS3_2 : (PA308107.Ind 3 (m + 3) : ℚ) = PA308107.Ind 2 (m + 2) := by
    exact_mod_cast PA308107.relS3 (m + 2)
  have hS3_3 : (PA308107.Ind 3 (m + 4) : ℚ) = PA308107.Ind 2 (m + 3) := by
    exact_mod_cast PA308107.relS3 (m + 3)
  have hS3_4 : (PA308107.Ind 3 (m + 5) : ℚ) = PA308107.Ind 2 (m + 4) := by
    exact_mod_cast PA308107.relS3 (m + 4)
  have hS3_5 : (PA308107.Ind 3 (m + 6) : ℚ) = PA308107.Ind 2 (m + 5) := by
    exact_mod_cast PA308107.relS3 (m + 5)
  have hS3_6 : (PA308107.Ind 3 (m + 7) : ℚ) = PA308107.Ind 2 (m + 6) := by
    exact_mod_cast PA308107.relS3 (m + 6)
  have hS3_7 : (PA308107.Ind 3 (m + 8) : ℚ) = PA308107.Ind 2 (m + 7) := by
    exact_mod_cast PA308107.relS3 (m + 7)
  have hS3_8 : (PA308107.Ind 3 (m + 9) : ℚ) = PA308107.Ind 2 (m + 8) := by
    exact_mod_cast PA308107.relS3 (m + 8)
  have hS3_9 : (PA308107.Ind 3 (m + 10) : ℚ) = PA308107.Ind 2 (m + 9) := by
    exact_mod_cast PA308107.relS3 (m + 9)
  have hS3_10 : (PA308107.Ind 3 (m + 11) : ℚ) = PA308107.Ind 2 (m + 10) := by
    exact_mod_cast PA308107.relS3 (m + 10)
  linear_combination ((-1 : ℚ)) * hA_0 + ((-1 : ℚ)) * hA_1 + ((1 : ℚ)) * hA_3 + ((3 : ℚ)) * hA_4 + ((2 : ℚ)) *
    hA_5 + ((-2 : ℚ)) * hA_7 + ((-3 : ℚ)) * hA_8 + ((-1 : ℚ)) * hA_9 + ((1 : ℚ)) * hA_11 + ((1 :
    ℚ)) * hA_12 + ((1 : ℚ)) * hB_0 + ((1 : ℚ)) * hB_1 + ((-2 : ℚ)) * hB_4 + ((-2 : ℚ)) * hB_5 +
    ((1 : ℚ)) * hB_8 + ((1 : ℚ)) * hB_9 + ((1 / 4 : ℚ)) * hDN_3 + ((1 / 4 : ℚ)) * hDN_4 + ((-1 /
    2 : ℚ)) * hDN_7 + ((-1 / 2 : ℚ)) * hDN_8 + ((1 / 4 : ℚ)) * hDN_11 + ((1 / 4 : ℚ)) * hDN_12 +
    ((-1 / 32 : ℚ)) * hDS_0 + ((-1 / 32 : ℚ)) * hDS_1 + ((1 / 32 : ℚ)) * hDS_3 + ((3 / 32 : ℚ))
    * hDS_4 + ((1 / 16 : ℚ)) * hDS_5 + ((-1 / 16 : ℚ)) * hDS_7 + ((-3 / 32 : ℚ)) * hDS_8 + ((-1
    / 32 : ℚ)) * hDS_9 + ((1 / 32 : ℚ)) * hDS_11 + ((1 / 32 : ℚ)) * hDS_12 + ((-1 / 8 : ℚ) + (1
    / 32 : ℚ) * (m : ℚ) ^ 2) * hS0_1 + ((-3 / 32 : ℚ) + (1 / 16 : ℚ) * (m : ℚ) + (1 / 32 : ℚ) *
    (m : ℚ) ^ 2) * hS0_2 + ((-1 / 8 : ℚ) * (m : ℚ) + (1 / 32 : ℚ) * (m : ℚ) ^ 2) * hS0_3 + ((-1
    / 2 : ℚ) + (-1 / 2 : ℚ) * (m : ℚ)) * hS0_4 + ((-7 / 4 : ℚ) + (-1 : ℚ) * (m : ℚ) + (-1 / 16 :
    ℚ) * (m : ℚ) ^ 2) * hS0_5 + ((-17 / 16 : ℚ) + (-7 / 8 : ℚ) * (m : ℚ) + (-1 / 16 : ℚ) * (m :
    ℚ) ^ 2) * hS0_6 + ((-3 / 4 : ℚ) * (m : ℚ) + (-1 / 16 : ℚ) * (m : ℚ) ^ 2) * hS0_7 + ((9 / 2 :
    ℚ) + (1 / 2 : ℚ) * (m : ℚ)) * hS0_8 + ((55 / 8 : ℚ) + (1 : ℚ) * (m : ℚ) + (1 / 32 : ℚ) * (m
    : ℚ) ^ 2) * hS0_9 + ((133 / 32 : ℚ) + (13 / 16 : ℚ) * (m : ℚ) + (1 / 32 : ℚ) * (m : ℚ) ^ 2)
    * hS0_10 + ((5 : ℚ) + (7 / 8 : ℚ) * (m : ℚ) + (1 / 32 : ℚ) * (m : ℚ) ^ 2) * hS0_11 + ((-1 /
    8 : ℚ) * (m : ℚ) + (1 / 32 : ℚ) * (m : ℚ) ^ 2) * hS1_0 + ((-3 / 32 : ℚ) + (-1 / 16 : ℚ) * (m
    : ℚ) + (1 / 32 : ℚ) * (m : ℚ) ^ 2) * hS1_1 + ((-1 / 8 : ℚ) + (1 / 32 : ℚ) * (m : ℚ) ^ 2) *
    hS1_2 + ((1 / 4 : ℚ) + (-1 / 4 : ℚ) * (m : ℚ)) * hS1_3 + ((-3 / 4 : ℚ) * (m : ℚ) + (-1 / 16
    : ℚ) * (m : ℚ) ^ 2) * hS1_4 + ((-13 / 16 : ℚ) + (-7 / 8 : ℚ) * (m : ℚ) + (-1 / 16 : ℚ) * (m
    : ℚ) ^ 2) * hS1_5 + ((-7 / 4 : ℚ) + (-1 : ℚ) * (m : ℚ) + (-1 / 16 : ℚ) * (m : ℚ) ^ 2) *
    hS1_6 + ((7 / 4 : ℚ) + (1 / 4 : ℚ) * (m : ℚ)) * hS1_7 + ((5 : ℚ) + (7 / 8 : ℚ) * (m : ℚ) +
    (1 / 32 : ℚ) * (m : ℚ) ^ 2) * hS1_8 + ((189 / 32 : ℚ) + (15 / 16 : ℚ) * (m : ℚ) + (1 / 32 :
    ℚ) * (m : ℚ) ^ 2) * hS1_9 + ((55 / 8 : ℚ) + (1 : ℚ) * (m : ℚ) + (1 / 32 : ℚ) * (m : ℚ) ^ 2)
    * hS1_10 + ((-1 / 8 : ℚ) * (m : ℚ) + (1 / 32 : ℚ) * (m : ℚ) ^ 2) * hS2_1 + ((-3 / 32 : ℚ) +
    (-1 / 16 : ℚ) * (m : ℚ) + (1 / 32 : ℚ) * (m : ℚ) ^ 2) * hS2_2 + ((-1 / 8 : ℚ) + (1 / 32 : ℚ)
    * (m : ℚ) ^ 2) * hS2_3 + ((1 / 4 : ℚ) + (-1 / 4 : ℚ) * (m : ℚ)) * hS2_4 + ((-3 / 4 : ℚ) * (m
    : ℚ) + (-1 / 16 : ℚ) * (m : ℚ) ^ 2) * hS2_5 + ((-13 / 16 : ℚ) + (-7 / 8 : ℚ) * (m : ℚ) + (-1
    / 16 : ℚ) * (m : ℚ) ^ 2) * hS2_6 + ((-7 / 4 : ℚ) + (-1 : ℚ) * (m : ℚ) + (-1 / 16 : ℚ) * (m :
    ℚ) ^ 2) * hS2_7 + ((7 / 4 : ℚ) + (1 / 4 : ℚ) * (m : ℚ)) * hS2_8 + ((5 : ℚ) + (7 / 8 : ℚ) *
    (m : ℚ) + (1 / 32 : ℚ) * (m : ℚ) ^ 2) * hS2_9 + ((189 / 32 : ℚ) + (15 / 16 : ℚ) * (m : ℚ) +
    (1 / 32 : ℚ) * (m : ℚ) ^ 2) * hS2_10 + ((55 / 8 : ℚ) + (1 : ℚ) * (m : ℚ) + (1 / 32 : ℚ) * (m
    : ℚ) ^ 2) * hS2_11 + ((-1 / 8 : ℚ) + (1 / 32 : ℚ) * (m : ℚ) ^ 2) * hS3_0 + ((-3 / 32 : ℚ) +
    (1 / 16 : ℚ) * (m : ℚ) + (1 / 32 : ℚ) * (m : ℚ) ^ 2) * hS3_1 + ((-1 / 8 : ℚ) * (m : ℚ) + (1
    / 32 : ℚ) * (m : ℚ) ^ 2) * hS3_2 + ((-1 / 2 : ℚ) + (-1 / 2 : ℚ) * (m : ℚ)) * hS3_3 + ((-7 /
    4 : ℚ) + (-1 : ℚ) * (m : ℚ) + (-1 / 16 : ℚ) * (m : ℚ) ^ 2) * hS3_4 + ((-17 / 16 : ℚ) + (-7 /
    8 : ℚ) * (m : ℚ) + (-1 / 16 : ℚ) * (m : ℚ) ^ 2) * hS3_5 + ((-3 / 4 : ℚ) * (m : ℚ) + (-1 / 16
    : ℚ) * (m : ℚ) ^ 2) * hS3_6 + ((9 / 2 : ℚ) + (1 / 2 : ℚ) * (m : ℚ)) * hS3_7 + ((55 / 8 : ℚ)
    + (1 : ℚ) * (m : ℚ) + (1 / 32 : ℚ) * (m : ℚ) ^ 2) * hS3_8 + ((133 / 32 : ℚ) + (13 / 16 : ℚ)
    * (m : ℚ) + (1 / 32 : ℚ) * (m : ℚ) ^ 2) * hS3_9 + ((5 : ℚ) + (7 / 8 : ℚ) * (m : ℚ) + (1 / 32
    : ℚ) * (m : ℚ) ^ 2) * hS3_10
