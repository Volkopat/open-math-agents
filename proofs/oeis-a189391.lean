import OMAStatements.S_oeis_a189391
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Data.Fin.Rev

/-!
The number of rounds spent deleting the first bit of each run equals the
range of the associated walk with steps +1 and -1. The reflection identity
for its maximum turns the sum of the ranges into a binomially weighted sum.
The rearrangement inequality gives the same value for the least apex.
-/

namespace OMA.S_oeis_a189391

open Finset

private def step (b : Bool) : ℤ := if b then 1 else -1

private def peak : List Bool → ℤ
  | [] => 0
  | b :: w => max 0 (step b + peak w)

private def trough : List Bool → ℤ
  | [] => 0
  | b :: w => min 0 (step b + trough w)

private def endpoint : List Bool → ℤ
  | [] => 0
  | b :: w => step b + endpoint w

private theorem peak_nonneg (w : List Bool) : 0 ≤ peak w := by
  cases w <;> simp [peak]

private theorem trough_nonpos (w : List Bool) : trough w ≤ 0 := by
  cases w <;> simp [trough]

private theorem erase_extrema (b : Bool) (w : List Bool) :
    peak (b :: w) = peak (keepRepeats b w) + (if b then 1 else 0) ∧
    trough (b :: w) = trough (keepRepeats b w) - (if b then 0 else 1) := by
  induction w generalizing b with
  | nil => cases b <;> decide
  | cons c w ih =>
    have hi := ih c
    have hp := peak_nonneg (keepRepeats c w)
    have hl := trough_nonpos (keepRepeats c w)
    cases b <;> cases c <;>
      simp [keepRepeats, peak, trough, step] at hi ⊢ <;> omega

private theorem erase_length_le (b : Bool) (w : List Bool) :
    (keepRepeats b w).length ≤ w.length := by
  induction w generalizing b with
  | nil => simp [keepRepeats]
  | cons c w ih =>
    have h := ih c
    simp only [keepRepeats]
    split <;> simp only [List.length_cons] <;> omega

private theorem steps_eq_range (n : ℕ) (w : List Bool) (hw : w.length ≤ n) :
    steps n w = (peak w - trough w).toNat := by
  induction n generalizing w with
  | zero =>
    cases w <;> simp_all [steps, peak, trough]
  | succ n ih =>
    cases w with
    | nil => simp [steps, peak, trough]
    | cons b w =>
      have hn := erase_length_le b w
      have he := erase_extrema b w
      have hp := peak_nonneg (keepRepeats b w)
      have hl := trough_nonpos (keepRepeats b w)
      simp only [List.length_cons] at hw
      rw [steps, raboter, ih _ (by omega)]
      cases b <;> simp at he <;>
        omega

private theorem wordSum_add (n : ℕ) (f g : List Bool → ℕ) :
    wordSum n (fun w => f w + g w) = wordSum n f + wordSum n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih =>
    simp only [wordSum]
    rw [show (fun w => f (true :: w) + g (true :: w) + (f (false :: w) + g (false :: w))) =
        (fun w => (f (true :: w) + f (false :: w)) +
          (g (true :: w) + g (false :: w))) by funext w; omega]
    exact ih _ _

private theorem wordSum_flip (n : ℕ) (f : List Bool → ℕ) :
    wordSum n (fun w => f (w.map Bool.not)) = wordSum n f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    simp only [wordSum, List.map_cons]
    change wordSum n (fun w => f (false :: w.map Bool.not) + f (true :: w.map Bool.not)) = _
    simp only [add_comm (f (false :: _))]
    exact ih (fun w => f (true :: w) + f (false :: w))

private theorem peak_flip (w : List Bool) :
    peak (w.map Bool.not) = -trough w := by
  induction w with
  | nil => simp [peak, trough]
  | cons b w ih =>
    cases b <;> simp [peak, trough, step, ih] <;> omega

private theorem endpoint_flip (w : List Bool) :
    endpoint (w.map Bool.not) = -endpoint w := by
  induction w with
  | nil => simp [endpoint]
  | cons b w ih =>
    cases b <;> simp [endpoint, step, ih] <;> omega

private theorem sum_resistance (n : ℕ) :
    wordSum n resistance = 2 * wordSum n (fun w => (peak w).toNat) := by
  rw [show resistance = (fun w => (peak w).toNat + (peak (w.map Bool.not)).toNat) by
    funext w
    rw [resistance, steps_eq_range _ _ le_rfl, peak_flip]
    have hp := peak_nonneg w
    have ht := trough_nonpos w
    omega]
  rw [wordSum_add, wordSum_flip n (fun w => (peak w).toNat), two_mul]

private def peakSum (n : ℕ) (z : ℤ) : ℕ :=
  wordSum n (fun w => (peak w - z).toNat)

private def endpointSum (n : ℕ) (z : ℤ) : ℕ :=
  wordSum n (fun w => (endpoint w - z).toNat + (endpoint w - z - 1).toNat)

private theorem peak_step (n : ℕ) (z : ℤ) (hz : 0 ≤ z) :
    peakSum (n + 1) z = peakSum n (z - 1) + peakSum n (z + 1) := by
  unfold peakSum
  rw [wordSum, ← wordSum_add]
  congr 1
  funext w
  simp [peak, step]
  omega

private theorem endpoint_step (n : ℕ) (z : ℤ) :
    endpointSum (n + 1) z = endpointSum n (z - 1) + endpointSum n (z + 1) := by
  unfold endpointSum
  rw [wordSum, ← wordSum_add]
  congr 1
  funext w
  simp [endpoint, step]
  congr 2 <;> omega

private theorem peak_boundary (n : ℕ) :
    peakSum n (-1) = peakSum n 0 + wordSum n (fun _ => 1) := by
  unfold peakSum
  rw [← wordSum_add]
  congr 1
  funext w
  have hp := peak_nonneg w
  omega

private theorem endpoint_boundary (n : ℕ) :
    endpointSum n (-1) = endpointSum n 0 + wordSum n (fun _ => 1) := by
  let f (w : List Bool) := (endpoint w + 1).toNat + (endpoint w).toNat
  let g (w : List Bool) := (endpoint w).toNat + (endpoint w - 1).toNat
  unfold endpointSum
  have hf' : (fun w => (endpoint w - (-1)).toNat + (endpoint w - (-1) - 1).toNat) = f := by
    funext w
    dsimp [f]
    omega
  simp only [hf', sub_zero]
  change wordSum n f = wordSum n g + wordSum n (fun _ => 1)
  have hf : wordSum n (fun w => f w + f (w.map Bool.not)) =
      wordSum n f + wordSum n f := by rw [wordSum_add, wordSum_flip]
  have hg : wordSum n (fun w => g w + g (w.map Bool.not)) =
      wordSum n g + wordSum n g := by rw [wordSum_add, wordSum_flip]
  have he : (fun w => f w + f (w.map Bool.not)) =
      (fun w => (g w + g (w.map Bool.not)) + (1 + 1)) := by
    funext w
    dsimp [f, g]
    rw [endpoint_flip]
    omega
  rw [he, wordSum_add, wordSum_add n (fun _ => 1) (fun _ => 1), hg] at hf
  omega

private theorem reflect (n : ℕ) (z : ℤ) (hz : -1 ≤ z) :
    peakSum n z = endpointSum n z := by
  induction n generalizing z with
  | zero =>
    simp [peakSum, endpointSum, wordSum, peak, endpoint]
    omega
  | succ n ih =>
    have hn (x : ℤ) (hx : 0 ≤ x) : peakSum (n + 1) x = endpointSum (n + 1) x := by
      rw [peak_step n x hx, endpoint_step, ih _ (by omega), ih _ (by omega)]
    by_cases h : 0 ≤ z
    · exact hn _ h
    · have hz' : z = -1 := by omega
      rw [hz', peak_boundary, endpoint_boundary, hn 0 (by decide)]


private def heads : List Bool → ℕ
  | [] => 0
  | b :: w => heads w + (if b then 1 else 0)

private theorem endpoint_eq (w : List Bool) :
    endpoint w = 2 * (heads w : ℤ) - (w.length : ℤ) := by
  induction w with
  | nil => simp [endpoint, heads]
  | cons b w ih =>
    cases b <;> simp [endpoint, heads, step, ih] <;> omega

private theorem wordSum_congr_length (n : ℕ) (f g : List Bool → ℕ)
    (h : ∀ w, w.length = n → f w = g w) :
    wordSum n f = wordSum n g := by
  induction n generalizing f g with
  | zero => exact h [] rfl
  | succ n ih =>
    simp only [wordSum]
    apply ih
    intro w hw
    rw [h (true :: w) (by simp [hw]), h (false :: w) (by simp [hw])]

private theorem apex_eq_words (n : ℕ) (f : ℕ → ℕ) :
    apex n f = wordSum n (fun w => f (heads w)) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [apex, ih, wordSum]
    congr 1
    funext w
    simp [heads, add_comm]

private theorem apex_eq_range (n : ℕ) (f : ℕ → ℕ) :
    apex n f = ∑ i ∈ range (n+1), n.choose i * f i := by
  induction n generalizing f with
  | zero => simp [apex]
  | succ n ih =>
    rw [apex, ih]
    simp only [Nat.mul_add, sum_add_distrib]
    have hfirst :
        (∑ i ∈ range (n+1), n.choose i * f i) =
          f 0 + ∑ i ∈ range (n+1), n.choose (i+1) * f (i+1) := by
      rw [sum_range_succ', sum_range_succ]
      simp [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n), add_comm]
    rw [hfirst, add_assoc, ← sum_add_distrib]
    conv_rhs => rw [sum_range_succ']
    simp only [Nat.choose_zero_right, one_mul, ← Nat.add_mul]
    rw [add_comm (f 0)]
    congr 1
    apply sum_congr rfl
    intro i _
    rw [Nat.choose_succ_succ, add_comm]

private theorem apex_eq_fin (n : ℕ) (f : ℕ → ℕ) :
    apex n f = ∑ i : Fin (n+1), n.choose i.val * f i.val := by
  rw [apex_eq_range, Fin.sum_univ_eq_sum_range (fun i => n.choose i * f i)]

private def rank (n i : ℕ) : ℕ :=
  if 2 * i ≤ n then n - 2 * i else 2 * i - n - 1

private def rankFin (n : ℕ) (i : Fin (n+1)) : Fin (n+1) :=
  ⟨rank n i.val, by have hi := i.isLt; unfold rank; split <;> omega⟩

private theorem rankFin_injective (n : ℕ) : Function.Injective (rankFin n) := by
  intro i j hij
  have h := congrArg Fin.val hij
  apply Fin.ext
  change rank n i.val = rank n j.val at h
  unfold rank at h
  split at h <;> split at h <;> omega

private noncomputable def rankPerm (n : ℕ) : Equiv.Perm (Fin (n+1)) :=
  Equiv.ofBijective (rankFin n)
    ((Fintype.bijective_iff_injective_and_card _).2 ⟨rankFin_injective n, rfl⟩)

private theorem choose_mono_left_half (n a b : ℕ) (hab : a ≤ b) (hb : b ≤ n / 2) :
    n.choose a ≤ n.choose b := by
  induction b with
  | zero =>
    have : a = 0 := by omega
    simp [this]
  | succ b ih =>
    by_cases h : a = b + 1
    · simp [h]
    · exact (ih (by omega) (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

private theorem choose_near_center (n : ℕ) (i : Fin (n+1)) :
    n.choose i.val = n.choose (min i.val (n - i.val)) := by
  have hi := i.isLt
  by_cases h : i.val ≤ n - i.val
  · rw [min_eq_left h]
  · rw [min_eq_right (by omega), Nat.choose_symm (by omega)]

private theorem rank_antivary (n : ℕ) :
    Antivary (fun i : Fin (n+1) => n.choose i.val) (fun i => (rankPerm n i).val) := by
  intro i j h
  change rank n i.val < rank n j.val at h
  have hi := i.isLt
  have hj := j.isLt
  have hh : min j.val (n-j.val) ≤ min i.val (n-i.val) := by
    unfold rank at h
    split at h <;> split at h <;> omega
  change n.choose j.val ≤ n.choose i.val
  rw [choose_near_center n i, choose_near_center n j]
  exact choose_mono_left_half _ _ _ hh (by omega)


private def endpointWeight (n i : ℕ) : ℕ :=
  (2 * (i : ℤ) - n).toNat + (2 * (i : ℤ) - n - 1).toNat

private theorem score_eq_fin (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    score n σ = ∑ i : Fin (n+1), n.choose i.val * (σ i).val := by
  unfold score
  rw [apex_eq_fin]
  apply sum_congr rfl
  intro i _
  rw [dif_pos i.isLt]

private theorem endpointSum_eq_fin (n : ℕ) :
    endpointSum n 0 = ∑ i : Fin (n+1), n.choose i.val * endpointWeight n i.val := by
  rw [← apex_eq_fin, apex_eq_words]
  unfold endpointSum
  apply wordSum_congr_length
  intro w hw
  simp [endpoint_eq, endpointWeight, hw]

private theorem rev_val (n : ℕ) (i : Fin (n+1)) :
    i.rev.val = n - i.val := by
  change n+1 - (i.val+1) = n - i.val
  omega

private theorem sum_reflect_indices (n : ℕ) (f : Fin (n+1) → ℕ) :
    (∑ i : Fin (n+1), n.choose i.val * f i.rev) =
      ∑ i : Fin (n+1), n.choose i.val * f i := by
  calc
    _ = ∑ i : Fin (n+1), n.choose i.rev.val * f i.rev := by
      apply sum_congr rfl
      intro i _
      rw [rev_val, Nat.choose_symm (by have hi := i.isLt; omega)]
    _ = _ := Equiv.sum_comp (Fin.revPerm : Equiv.Perm (Fin (n+1))) (fun i => n.choose i.val * f i)

private theorem rank_pair (n : ℕ) (i : Fin (n+1)) :
    rank n i.val + rank n i.rev.val =
      endpointWeight n i.val + endpointWeight n i.rev.val := by
  have hi := i.isLt
  rw [rev_val]
  unfold rank endpointWeight
  split <;> split <;> omega

private theorem score_rank_eq_endpoint (n : ℕ) :
    score n (rankPerm n) = endpointSum n 0 := by
  rw [score_eq_fin, endpointSum_eq_fin]
  change (∑ i : Fin (n+1), n.choose i.val * rank n i.val) =
    ∑ i : Fin (n+1), n.choose i.val * endpointWeight n i.val
  have hpair :
      (∑ i : Fin (n+1), n.choose i.val * (rank n i.val + rank n i.rev.val)) =
        ∑ i : Fin (n+1), n.choose i.val * (endpointWeight n i.val + endpointWeight n i.rev.val) := by
    apply sum_congr rfl
    intro i _
    rw [rank_pair]
  simp only [Nat.mul_add, sum_add_distrib] at hpair
  rw [sum_reflect_indices n (fun i => rank n i.val),
    sum_reflect_indices n (fun i => endpointWeight n i.val)] at hpair
  omega

private theorem score_rank_min (n : ℕ) (σ : Equiv.Perm (Fin (n+1))) :
    score n (rankPerm n) ≤ score n σ := by
  simp only [score_eq_fin]
  have h := (rank_antivary n).sum_mul_le_sum_mul_comp_perm (σ := σ.trans (rankPerm n).symm)
  simpa using h

end OMA.S_oeis_a189391

open OMA.S_oeis_a189391 in
theorem OMA.solution : type_of% @OMA.S_oeis_a189391.main := by
  intro n
  have hvalue : wordSum n resistance = 2 * score n (rankPerm n) := by
    rw [sum_resistance, score_rank_eq_endpoint, ← reflect n 0 (by decide)]
    simp [peakSum]
  rw [hvalue]
  refine ⟨⟨rankPerm n, rfl⟩, ?_⟩
  rintro _ ⟨σ, rfl⟩
  exact Nat.mul_le_mul_left _ (score_rank_min n σ)
