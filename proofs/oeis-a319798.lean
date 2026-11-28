import OMAStatements.S_oeis_a319798
import Mathlib

/-!
# OEIS A319798: for k >= 2, the least positive fixed point of the Kaprekar map in base 3k-1 is k*(3k-2)

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. Put M = k*(b-1) = k*(3k-2). (1) M = (k-1)*b + (2k-1) has the two digits k-1 < 2k-1 < b, so its image
is ((2k-1)*b + (k-1)) - ((k-1)*b + (2k-1)) = k*(b-1) = M. (2) Let 0 < m <= M be a fixed point. Since
M < b^2, m has at most two digits; a one-digit number maps to 0, so m has digits A (leading, >= 1)
and B, and its image is d*(b-1) with d = |A - B|. A fixed point has d >= 1, and m = d*(b-1) =
(d-1)*b + (b-d) with 1 <= d <= b-1; m >= b forces d >= 2, so the digits are A = d-1 and B = b-d. (3)
Then d = |A - B| = |2d - b - 1|. The case d = 2d - b - 1 gives d = b+1, impossible; the other gives
3d = b+1 = 3k, so d = k and m = M.
-/

open OMA.S_oeis_a319798

namespace OMA.A319798Proof

lemma digits_two (b m : ℕ) (hb : 2 ≤ b) (hm : b ≤ m) (hm2 : m < b * b) :
    Nat.digits b m = [m % b, m / b] := by
  have hqpos : 0 < m / b := Nat.div_pos hm (by omega)
  have hqlt : m / b < b := (Nat.div_lt_iff_lt_mul (by omega)).2 hm2
  rw [Nat.digits_def' (by omega) (by omega),
    Nat.digits_of_lt b (m / b) (by omega) hqlt]

lemma kaprekar_small (b m : ℕ) (hm : 0 < m) (hmb : m < b) :
    kaprekar b m = 0 := by
  simp [kaprekar, Nat.digits_of_lt b m (by omega) hmb, List.insertionSort]

lemma kaprekar_pair (b m lo hi : ℕ) (hb : 1 ≤ b)
    (hdigits : Nat.digits b m = [lo, hi]) :
    kaprekar b m = (max lo hi - min lo hi) * (b - 1) := by
  have hb1 : b - 1 + 1 = b := by omega
  unfold kaprekar
  rw [hdigits]
  by_cases h : lo ≤ hi
  · simp only [List.insertionSort, List.foldr_cons, List.foldr_nil,
      List.orderedInsert, h, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, Nat.ofDigits_cons,
      max_eq_right h, min_eq_left h]
    apply Nat.sub_eq_of_eq_add
    have hd : hi - lo + lo = hi := by omega
    nlinarith
  · have h' : hi ≤ lo := by omega
    simp only [List.insertionSort, List.foldr_cons, List.foldr_nil,
      List.orderedInsert, h, ↓reduceIte, List.reverse_cons, List.reverse_nil,
      List.nil_append, List.singleton_append, Nat.ofDigits_cons,
      max_eq_left h', min_eq_right h']
    apply Nat.sub_eq_of_eq_add
    have hd : lo - hi + hi = lo := by omega
    nlinarith

lemma fixed_two (b m : ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hm2 : m < b * b) (hfix : kaprekar b m = m) :
    ∃ d : ℕ, 3 * d = b + 1 ∧ m = d * (b - 1) := by
  have hmb : b ≤ m := by
    by_contra h
    have hz := kaprekar_small b m hm (by omega)
    omega
  let lo := m % b
  let hi := m / b
  let d := max lo hi - min lo hi
  have hlo : lo < b := Nat.mod_lt m (by omega)
  have hhi : hi < b := (Nat.div_lt_iff_lt_mul (by omega)).2 hm2
  have hprod : m = d * (b - 1) := by
    rw [← hfix]
    exact kaprekar_pair b m lo hi (by omega) (digits_two b m hb hmb hm2)
  have hdpos : 0 < d := by
    by_contra h
    have hz : d = 0 := by omega
    simp [hz] at hprod
    omega
  have hdlt : d < b :=
    lt_of_le_of_lt (Nat.sub_le _ _) (max_lt hlo hhi)
  have hdecomp : m = (d - 1) * b + (b - d) := by
    have hs1 : d - 1 + 1 = d := by omega
    have hs2 : b - d + d = b := by omega
    have hs3 : b - 1 + 1 = b := by omega
    nlinarith [hprod]
  have hq : hi = d - 1 := by
    dsimp [hi]
    have hrem : b - d < b := by omega
    apply Nat.div_eq_of_lt_le <;> nlinarith [hdecomp]
  have hr : lo = b - d := by
    have heq := Nat.mod_add_div m b
    change lo + b * hi = m at heq
    rw [hq] at heq
    nlinarith [hdecomp]
  refine ⟨d, ?_, hprod⟩
  have hdiff : d = max lo hi - min lo hi := rfl
  rw [hq, hr] at hdiff
  omega

lemma candidate_fixed (j : ℕ) :
    kaprekar (3 * j + 5) ((j + 2) * (3 * j + 4)) = (j + 2) * (3 * j + 4) := by
  have hlow : 3 * j + 5 ≤ (j + 2) * (3 * j + 4) := by nlinarith
  have hupp : (j + 2) * (3 * j + 4) < (3 * j + 5) * (3 * j + 5) := by
    nlinarith
  have hq : (j + 2) * (3 * j + 4) / (3 * j + 5) = j + 1 := by
    apply Nat.div_eq_of_lt_le <;> nlinarith
  have hr : (j + 2) * (3 * j + 4) % (3 * j + 5) = 2 * j + 3 := by
    rw [Nat.mod_eq_sub_mul_div, hq]
    apply Nat.sub_eq_of_eq_add
    ring
  have hdigits : Nat.digits (3 * j + 5) ((j + 2) * (3 * j + 4)) =
      [2 * j + 3, j + 1] := by
    rw [digits_two _ _ (by omega) hlow hupp, hq, hr]
  rw [kaprekar_pair _ _ _ _ (by omega) hdigits,
    max_eq_left (by omega), min_eq_right (by omega)]
  have hdiff : 2 * j + 3 - (j + 1) = j + 2 := by omega
  have hbase : 3 * j + 5 - 1 = 3 * j + 4 := by omega
  rw [hdiff, hbase]

lemma least_fixed (j : ℕ) :
    IsLeast {m : ℕ | 0 < m ∧ kaprekar (3 * j + 5) m = m}
      ((j + 2) * (3 * j + 4)) := by
  constructor
  · exact ⟨by positivity, candidate_fixed j⟩
  · intro m hm
    by_contra h
    have hlt : m < (j + 2) * (3 * j + 4) := by omega
    have hm2 : m < (3 * j + 5) * (3 * j + 5) := by nlinarith
    obtain ⟨d, hd, hprod⟩ := fixed_two (3 * j + 5) m (by omega) hm.1 hm2 hm.2
    have heq : d = j + 2 := by omega
    have hbase : 3 * j + 5 - 1 = 3 * j + 4 := by omega
    rw [heq, hbase] at hprod
    omega

end OMA.A319798Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a319798.main := by
  intro k hk
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, k = j + 2 := ⟨k - 2, by omega⟩
  have hb : 3 * (j + 2) - 1 = 3 * j + 5 := by omega
  have hc : 3 * (j + 2) - 2 = 3 * j + 4 := by omega
  rw [hb, hc]
  exact OMA.A319798Proof.least_fixed j
