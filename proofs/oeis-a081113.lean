import OMAStatements.S_oeis_a081113
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.LinearCombination

/-!
A walk of length m can start in m+1 minus its range many rows of an
(m+1)-by-(m+1) board. The reflection identity expresses the total range
through endpoint counts. An endpoint-weighted sum gives the recurrence for
the central endpoint counts and then for the number of king paths.
-/

namespace OMA.S_oeis_a081113

open Finset

private abbrev Walk : ℕ → Type
  | 0 => PUnit
  | m+1 => Fin 3 × Walk m

private instance walkFintype (m : ℕ) : Fintype (Walk m) := by
  induction m with
  | zero => exact inferInstanceAs (Fintype PUnit)
  | succ m ih =>
    letI : Fintype (Walk m) := ih
    exact inferInstanceAs (Fintype (Fin 3 × Walk m))

private def letter (b : Fin 3) : ℤ := (b.val : ℤ)-1

private theorem letter_bound (b : Fin 3) : |letter b| ≤ 1 := by
  have h := b.isLt
  exact abs_le.mpr ⟨by unfold letter; omega, by unfold letter; omega⟩

private def position : ∀ {m}, Walk m → ℕ → ℤ
  | 0, _, _ => 0
  | _+1, _, 0 => 0
  | _+1, w, k+1 => letter w.1 + position w.2 k

private def peak : ∀ {m}, Walk m → ℤ
  | 0, _ => 0
  | _+1, w => max 0 (letter w.1 + peak w.2)

private def trough : ∀ {m}, Walk m → ℤ
  | 0, _ => 0
  | _+1, w => min 0 (letter w.1 + trough w.2)

private def endpoint {m : ℕ} (w : Walk m) : ℤ := position w m

private theorem position_zero (m : ℕ) (w : Walk m) : position w 0 = 0 := by
  cases m <;> rfl

private theorem endpoint_succ (m : ℕ) (w : Walk (m+1)) :
    endpoint w = letter w.1 + endpoint w.2 := rfl

private theorem extrema_bounds (m : ℕ) (w : Walk m) (k : ℕ) :
    trough w ≤ position w k ∧ position w k ≤ peak w := by
  induction m generalizing k with
  | zero => simp [position, peak, trough]
  | succ m ih =>
    cases k with
    | zero => simp [position, peak, trough]
    | succ k =>
      have h := ih w.2 k
      simp only [position, peak, trough]
      omega

private theorem extrema_attained (m : ℕ) (w : Walk m) :
    (∃ i ≤ m, position w i = trough w) ∧ (∃ j ≤ m, position w j = peak w) := by
  induction m with
  | zero => exact ⟨⟨0, le_rfl, rfl⟩, ⟨0, le_rfl, rfl⟩⟩
  | succ m ih =>
    obtain ⟨⟨i, hi, ei⟩, ⟨j, hj, ej⟩⟩ := ih w.2
    constructor
    · by_cases h : 0 ≤ letter w.1 + trough w.2
      · exact ⟨0, Nat.zero_le _, by simp [position, trough, min_eq_left h]⟩
      · have hh : letter w.1 + trough w.2 ≤ 0 := by omega
        exact ⟨i+1, by omega, by simp [position, trough, ei, min_eq_right hh]⟩
    · by_cases h : letter w.1 + peak w.2 ≤ 0
      · exact ⟨0, Nat.zero_le _, by simp [position, peak, max_eq_left h]⟩
      · have hh : 0 ≤ letter w.1 + peak w.2 := by omega
        exact ⟨j+1, by omega, by simp [position, peak, ej, max_eq_right hh]⟩

private theorem adjacent_positions (m : ℕ) (w : Walk m) (k : ℕ) (hk : k < m) :
    |position w (k+1) - position w k| ≤ 1 := by
  induction m generalizing k with
  | zero => omega
  | succ m ih =>
    cases k with
    | zero => simpa [position, position_zero] using letter_bound w.1
    | succ k =>
      simpa [position, add_sub_add_left_eq_sub] using ih w.2 k (by omega)

private theorem span_bound (m : ℕ) (w : Walk m) :
    0 ≤ peak w - trough w ∧ peak w - trough w ≤ (m : ℤ) := by
  induction m with
  | zero => simp [peak, trough]
  | succ m ih =>
    have hb : -1 ≤ letter w.1 ∧ letter w.1 ≤ 1 := abs_le.mp (letter_bound w.1)
    have ht := extrema_bounds m w.2 0
    rw [position_zero] at ht
    have hi := ih w.2
    simp only [peak, trough, Nat.cast_succ]
    omega

private def readWalk (m : ℕ) (f : ℕ → ℤ)
    (h : ∀ k < m, |f (k+1)-f k| ≤ 1) : Walk m :=
  match m with
  | 0 => PUnit.unit
  | m+1 =>
    let d := f 1 - f 0 + 1
    let b : Fin 3 := ⟨d.toNat, by
      have hb := abs_le.mp (h 0 (by omega))
      simp only [Nat.zero_add] at hb
      change (f 1 - f 0 + 1).toNat < 3
      omega⟩
    (b, readWalk m (fun k => f (k+1)) (fun k hk => h (k+1) (by omega)))

private theorem read_positions (m : ℕ) (f : ℕ → ℤ)
    (h : ∀ k < m, |f (k+1)-f k| ≤ 1) (k : ℕ) (hk : k ≤ m) :
    position (readWalk m f h) k = f k - f 0 := by
  induction m generalizing f k with
  | zero =>
    have he : k = 0 := by omega
    simp [he, position]
  | succ m ih =>
    cases k with
    | zero => simp [position]
    | succ k =>
      have hb := abs_le.mp (h 0 (by omega))
      simp only [Nat.zero_add] at hb
      simp only [readWalk, position, letter]
      rw [ih _ _ k (by omega)]
      simp only [Nat.zero_add]
      omega

private theorem positions_injective (m : ℕ) (w v : Walk m)
    (h : ∀ k ≤ m, position w k = position v k) : w = v := by
  induction m with
  | zero => exact @Subsingleton.elim PUnit _ w v
  | succ m ih =>
    have hs := h 1 (by omega)
    simp only [position, position_zero, add_zero] at hs
    apply Prod.ext
    · apply Fin.ext
      unfold letter at hs
      omega
    · apply ih
      intro k hk
      have ht := h (k+1) (by omega)
      simp only [position] at ht
      omega


private def Board (m : ℕ) :=
  {c : Fin (m+1) → Fin (m+1) //
    ∀ i : Fin (m+1), ∀ h : i.val+1 < m+1,
      |((c ⟨i.val+1,h⟩).val : ℤ) - ((c i).val : ℤ)| ≤ 1}

private def span {m : ℕ} (w : Walk m) : ℕ := (peak w - trough w).toNat

private theorem cast_span {m : ℕ} (w : Walk m) :
    ((span w : ℕ) : ℤ) = peak w - trough w :=
  Int.toNat_of_nonneg (span_bound m w).1

private def Codes (m : ℕ) := Σ w : Walk m, Fin (m+1-span w)

private def start {m : ℕ} (p : Codes m) : ℤ := (p.2.val : ℤ) - trough p.1

private theorem code_bounds (m : ℕ) (p : Codes m) (k : ℕ) :
    0 ≤ start p + position p.1 k ∧ start p + position p.1 k < (m+1 : ℕ) := by
  have h := extrema_bounds m p.1 k
  have hs := p.2.isLt
  have hr := cast_span p.1
  have hm := span_bound m p.1
  unfold start
  omega

private def encode (m : ℕ) (p : Codes m) : Board m := by
  let col (i : Fin (m+1)) : Fin (m+1) :=
    ⟨(start p + position p.1 i.val).toNat, by
      have h := code_bounds m p i.val
      omega⟩
  refine ⟨col, ?_⟩
  intro i hi
  change |((start p + position p.1 (i.val+1)).toNat : ℤ) -
    ((start p + position p.1 i.val).toNat : ℤ)| ≤ 1
  rw [Int.toNat_of_nonneg (code_bounds m p (i.val+1)).1,
    Int.toNat_of_nonneg (code_bounds m p i.val).1, add_sub_add_left_eq_sub]
  exact adjacent_positions m p.1 i.val (by omega)

private theorem encoded_col (m : ℕ) (p : Codes m) (i : Fin (m+1)) :
    (((encode m p).val i).val : ℤ) = start p + position p.1 i.val :=
  Int.toNat_of_nonneg (code_bounds m p i.val).1

private theorem encode_injective (m : ℕ) : Function.Injective (encode m) := by
  intro p q h
  have he (k : ℕ) (hk : k ≤ m) : start p + position p.1 k = start q + position q.1 k := by
    have hc := congrArg (fun c : Board m => ((c.val ⟨k, by omega⟩).val : ℤ)) h
    simpa only [encoded_col] using hc
  have hs := he 0 (by omega)
  simp only [position_zero, add_zero] at hs
  have hw : p.1 = q.1 := by
    apply positions_injective
    intro k hk
    have h := he k hk
    omega
  rcases p with ⟨p, i⟩
  rcases q with ⟨q, j⟩
  change p=q at hw
  subst q
  have hv : i.val=j.val := by
    change (i.val : ℤ)-trough p=(j.val : ℤ)-trough p at hs
    omega
  rw [show i=j from Fin.ext hv]

private theorem encode_surjective (m : ℕ) : Function.Surjective (encode m) := by
  intro p
  let col (k : ℕ) : ℤ := if hk : k < m+1 then ((p.val ⟨k,hk⟩).val : ℤ) else 0
  have hc (k : ℕ) (hk : k ≤ m) : 0 ≤ col k ∧ col k < (m+1 : ℕ) := by
    unfold col
    rw [dif_pos (by omega)]
    have h := (p.val ⟨k, by omega⟩).isLt
    omega
  have hstep (k : ℕ) (hk : k < m) : |col (k+1)-col k| ≤ 1 := by
    unfold col
    rw [dif_pos (by omega), dif_pos (by omega)]
    have hsucc : k + 1 < m + 1 := by omega
    exact p.prop ⟨k, by omega⟩ hsucc
  let w := readWalk m col hstep
  have hp (k : ℕ) (hk : k ≤ m) : position w k = col k-col 0 :=
    read_positions m col hstep k hk
  obtain ⟨⟨i, hi, hmin⟩, ⟨j, hj, hmax⟩⟩ := extrema_attained m w
  have hmin' : 0 ≤ col 0 + trough w := by
    rw [← hmin, hp i hi]
    have h := hc i hi
    omega
  have hmax' : col 0 + peak w < (m+1 : ℕ) := by
    rw [← hmax, hp j hj]
    have h := hc j hj
    omega
  let s : Fin (m+1-span w) := ⟨(col 0 + trough w).toNat, by
    have hs := cast_span w
    have hb := span_bound m w
    omega⟩
  refine ⟨⟨w,s⟩, ?_⟩
  apply Subtype.ext
  funext k
  apply Fin.ext
  have hval := encoded_col m ⟨w,s⟩ k
  change (((encode m ⟨w,s⟩).val k).val : ℤ) =
    (((col 0 + trough w).toNat : ℤ) - trough w) + position w k.val at hval
  rw [Int.toNat_of_nonneg hmin', hp k.val (by have hk := k.isLt; omega)] at hval
  have he : col k.val = (p.val k).val := by
    unfold col
    rw [dif_pos k.isLt]
  rw [he] at hval
  omega

private theorem count_as_sum (m : ℕ) :
    a (m+1) = ∑ w : Walk m, (m+1-span w) := by
  have h := Nat.card_congr (Equiv.ofBijective (encode m) ⟨encode_injective m, encode_surjective m⟩)
  change Nat.card (Codes m) = a (m+1) at h
  rw [← h]
  change Nat.card (Σ w : Walk m, Fin (m+1-span w)) = _
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [Fintype.card_fin]


private noncomputable def total (m : ℕ) (f : Walk m → ℤ) : ℤ := ∑ w, f w

private theorem total_zero (f : Walk 0 → ℤ) : total 0 f = f PUnit.unit := by
  change (∑ w : PUnit, f w) = _
  simp

private theorem total_succ (m : ℕ) (f : Walk (m+1) → ℤ) :
    total (m+1) f =
      total m (fun w => f (⟨2,w⟩ : Fin 3 × Walk m)) +
      total m (fun w => f (⟨1,w⟩ : Fin 3 × Walk m)) +
      total m (fun w => f (⟨0,w⟩ : Fin 3 × Walk m)) := by
  change (∑ w : Fin 3 × Walk m, f w) = _
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change total m (fun w => f (⟨0,w⟩ : Fin 3 × Walk m)) +
    (total m (fun w => f (⟨1,w⟩ : Fin 3 × Walk m)) +
      total m (fun w => f (⟨2,w⟩ : Fin 3 × Walk m))) = _
  ring

private theorem total_add (m : ℕ) (f g : Walk m → ℤ) :
    total m (fun w => f w+g w) = total m f + total m g := Finset.sum_add_distrib

private theorem total_sub (m : ℕ) (f g : Walk m → ℤ) :
    total m (fun w => f w-g w) = total m f - total m g := by
  unfold total
  rw [Finset.sum_sub_distrib]

private theorem total_mul (m : ℕ) (r : ℤ) (f : Walk m → ℤ) :
    total m (fun w => r * f w) = r*total m f := (Finset.mul_sum _ _ _).symm

private theorem walk_card (m : ℕ) : Fintype.card (Walk m) = 3^m := by
  induction m with
  | zero => rfl
  | succ m ih =>
    change Fintype.card (Fin 3 × Walk m) = _
    rw [Fintype.card_prod, Fintype.card_fin, ih, pow_succ, mul_comm]

private theorem total_const (m : ℕ) (r : ℤ) : total m (fun _ => r) = (3:ℤ)^m*r := by
  simp [total, Finset.sum_const, walk_card, nsmul_eq_mul]

private theorem king_total (m : ℕ) :
    (a (m+1) : ℤ) = ((m : ℤ)+1)*3^m -
      total m (fun w => peak w - trough w) := by
  rw [count_as_sum, Nat.cast_sum]
  have h (w : Walk m) :
      ((m+1-span w : ℕ) : ℤ) = ((m : ℤ)+1) - (peak w - trough w) := by
    have hb := (span_bound m w).2
    have hs := cast_span w
    omega
  simp_rw [h]
  change total m (fun w => (m:ℤ)+1-(peak w-trough w)) = _
  rw [total_sub, total_const]
  ring

private def flip : (m : ℕ) → Equiv.Perm (Walk m)
  | 0 => Equiv.refl _
  | m+1 => Equiv.prodCongr Fin.revPerm (flip m)

private theorem letter_rev (b : Fin 3) : letter b.rev = -letter b := by
  have h := b.isLt
  change ((3-(b.val+1) : ℕ) : ℤ)-1 = -((b.val : ℤ)-1)
  omega

private theorem flip_extrema (m : ℕ) (w : Walk m) :
    peak (flip m w) = -trough w ∧ trough (flip m w) = -peak w := by
  induction m with
  | zero => simp [peak, trough]
  | succ m ih =>
    have h := ih w.2
    change max 0 (letter w.1.rev + peak (flip m w.2)) = -min 0 (letter w.1 + trough w.2) ∧
      min 0 (letter w.1.rev + trough (flip m w.2)) = -max 0 (letter w.1 + peak w.2)
    rw [letter_rev,h.1,h.2]
    omega

private theorem flip_endpoint (m : ℕ) (w : Walk m) : endpoint (flip m w) = -endpoint w := by
  induction m with
  | zero => simp [endpoint, position]
  | succ m ih =>
    change letter w.1.rev + endpoint (flip m w.2) = -(letter w.1 + endpoint w.2)
    rw [letter_rev, ih]
    ring

private theorem total_flip (m : ℕ) (f : Walk m → ℤ) :
    total m (fun w => f (flip m w)) = total m f := Equiv.sum_comp (flip m) f

private noncomputable def H (m : ℕ) (z : ℤ) : ℤ := total m (fun w => max 0 (peak w-z))

private noncomputable def E (m : ℕ) (z : ℤ) : ℤ :=
  total m (fun w => max 0 (endpoint w-z) + max 0 (endpoint w-z-1))

private theorem king_H (m : ℕ) :
    (a (m+1) : ℤ) = ((m : ℤ)+1)*3^m - 2*H m 0 := by
  rw [king_total]
  have h : total m (fun w => peak w-trough w) = 2*H m 0 := by
    have h' (w : Walk m) : peak w-trough w = max 0 (peak w-0) + max 0 (peak (flip m w)-0) := by
      rw [(flip_extrema m w).1]
      have hh := extrema_bounds m w 0
      rw [position_zero] at hh
      omega
    simp_rw [h']
    rw [total_add, total_flip m (fun w => max 0 (peak w-0)), H, two_mul]
  rw [h]

private theorem letter_zero : letter 0 = -1 := by decide
private theorem letter_one : letter 1 = 0 := by decide
private theorem letter_two : letter 2 = 1 := by decide

private theorem H_step (m : ℕ) (z : ℤ) (hz : 0 ≤ z) :
    H (m+1) z = H m (z-1)+H m z+H m (z+1) := by
  unfold H
  rw [total_succ]
  simp only [peak, letter_two, letter_one, letter_zero]
  have he (t b : ℤ) : max 0 (max 0 (b+t)-z) = max 0 (t-(z-b)) := by omega
  simp only [he, sub_zero, sub_neg_eq_add]

private theorem E_step (m : ℕ) (z : ℤ) :
    E (m+1) z = E m (z-1)+E m z+E m (z+1) := by
  unfold E
  rw [total_succ]
  simp only [endpoint_succ m, letter_two, letter_one, letter_zero, zero_add]
  have he (b : ℤ) :
      (fun w : Walk m => max 0 (b+endpoint w-z) + max 0 (b+endpoint w-z-1)) =
      (fun w : Walk m => max 0 (endpoint w-(z-b)) + max 0 (endpoint w-(z-b)-1)) := by
    funext w
    congr 1 <;> congr 1 <;> omega
  rw [he 1, he (-1), sub_neg_eq_add]


private theorem H_boundary (m : ℕ) :
    H m (-1)=H m 0+(3:ℤ)^m := by
  have h (w : Walk m) : max 0 (peak w-(-1)) = max 0 (peak w-0)+1 := by
    have hh := (extrema_bounds m w 0).2
    rw [position_zero] at hh
    omega
  unfold H
  simp_rw [h]
  rw [total_add, total_const, mul_one]

private theorem E_boundary (m : ℕ) :
    E m (-1)=E m 0+(3:ℤ)^m := by
  let f (w : Walk m) := max 0 (endpoint w-(-1)) + max 0 (endpoint w-(-1)-1)
  let g (w : Walk m) := max 0 (endpoint w-0) + max 0 (endpoint w-0-1)
  have hf : total m (fun w => f w+f (flip m w)) = E m (-1)+E m (-1) := by
    rw [total_add, total_flip m f]
    rfl
  have hg : total m (fun w => g w+g (flip m w)) = E m 0+E m 0 := by
    rw [total_add, total_flip m g]
    rfl
  have h : (fun w => f w+f (flip m w)) =
      (fun w => (g w+g (flip m w))+2) := by
    funext w
    dsimp [f,g]
    rw [flip_endpoint]
    omega
  rw [h, total_add, total_const, hg] at hf
  omega

private theorem reflection (m : ℕ) (z : ℤ) (hz : -1 ≤ z) :
    H m z=E m z := by
  induction m generalizing z with
  | zero =>
    unfold H E
    rw [total_zero, total_zero]
    simp [peak, endpoint, position]
    omega
  | succ m ih =>
    have h (t : ℤ) (ht : 0 ≤ t) : H (m+1) t=E (m+1) t := by
      rw [H_step m t ht, E_step, ih _ (by omega), ih _ (by omega), ih _ (by omega)]
    by_cases ht : 0 ≤ z
    · exact h z ht
    · rw [show z = -1 by omega, H_boundary, E_boundary, h 0 (by omega)]

private noncomputable def count (m : ℕ) (z : ℤ) : ℤ :=
    total m (fun w => if endpoint w=z then 1 else 0)

private theorem count_neg (m : ℕ) (z : ℤ) : count m (-z) = count m z := by
  have h := total_flip m (fun w => if endpoint w=z then 1 else 0)
  change total m (fun w => if endpoint (flip m w)=z then 1 else 0) = count m z at h
  simp_rw [flip_endpoint, neg_eq_iff_eq_neg] at h
  exact h

private theorem count_step (m : ℕ) (z : ℤ) :
    count (m+1) z = count m (z-1)+count m z+count m (z+1) := by
  unfold count
  rw [total_succ]
  simp only [endpoint_succ m, letter_two, letter_one, letter_zero, zero_add,
    show ∀ e : ℤ, 1+e=z ↔ e=z-1 by intro e; omega,
    show ∀ e : ℤ, -1+e=z ↔ e=z+1 by intro e; omega]

private noncomputable def W (m : ℕ) (g : ℤ → ℤ) : ℤ :=
    total m (fun w => endpoint w * g (endpoint w))

private theorem W_step (m : ℕ) (g : ℤ → ℤ) :
    W (m+1) g = W m (fun e => g (1+e)) + W m g + W m (fun e => g (-1+e)) +
      total m (fun w => g (1+endpoint w)-g (-1+endpoint w)) := by
  unfold W
  rw [total_succ]
  simp only [endpoint_succ m, letter_two, letter_one, letter_zero, zero_add]
  rw [show (fun w : Walk m => (1+endpoint w)*g (1+endpoint w)) =
    (fun w => endpoint w*g (1+endpoint w)+g (1+endpoint w)) by funext w; ring,
    show (fun w : Walk m => (-1+endpoint w)*g (-1+endpoint w)) =
    (fun w => endpoint w*g (-1+endpoint w)-g (-1+endpoint w)) by funext w; ring,
    total_add, total_sub, total_sub]
  ring

private theorem W_sum (m : ℕ) (g : ℤ → ℤ) :
    W (m+1) g = ((m : ℤ)+1)*
      total m (fun w => g (1+endpoint w)-g (-1+endpoint w)) := by
  induction m generalizing g with
  | zero =>
    rw [W_step]
    unfold W
    simp only [total_zero, endpoint, position, zero_mul, add_zero, zero_add,
      Nat.cast_zero, one_mul]
  | succ m ih =>
    rw [W_step (m+1), ih, ih, ih, total_succ]
    simp only [endpoint_succ m, letter_two, letter_one, letter_zero, zero_add, Nat.cast_succ]
    rw [show (fun w : Walk m => g (1+(-1+endpoint w))-g (-1+(-1+endpoint w))) =
      (fun w => g (-1+(1+endpoint w))-g (-1+(-1+endpoint w))) by
        funext w; congr 2; omega,
      show (fun w : Walk m => g (1+(1+endpoint w))-g (1+(-1+endpoint w))) =
      (fun w => g (1+(1+endpoint w))-g (-1+(1+endpoint w))) by
        funext w; congr 2; omega]
    ring


private def positive (s : ℤ) : ℤ := if 0<s then 1 else 0

private noncomputable def posCount (m : ℕ) : ℤ :=
  total m (fun w => positive (endpoint w))

private noncomputable def posSum (m : ℕ) : ℤ :=
  total m (fun w => max 0 (endpoint w))

private theorem positives (m : ℕ) : 2*posCount m = (3:ℤ)^m-count m 0 := by
  have h : (fun w : Walk m => positive (endpoint w) + positive (-endpoint w) +
      (if endpoint w=0 then 1 else 0)) = (fun _ => (1 : ℤ)) := by
    funext w
    unfold positive
    split <;> split <;> split <;> omega
  have hh := congrArg (total m) h
  have hs : total m (fun w => positive (-endpoint w)) = posCount m := by
    have ht := total_flip m (fun w => positive (endpoint w))
    simp_rw [flip_endpoint] at ht
    exact ht
  rw [total_add, total_add, hs, total_const, mul_one] at hh
  change posCount m + posCount m + count m 0 = _ at hh
  omega

private theorem E_zero (m : ℕ) :
    2*E m 0 = 4*posSum m - ((3:ℤ)^m-count m 0) := by
  unfold E
  have h : (fun w : Walk m => max 0 (endpoint w-0)+max 0 (endpoint w-0-1)) =
      (fun w => 2*max 0 (endpoint w)-positive (endpoint w)) := by
    funext w
    unfold positive
    split <;> omega
  rw [h, total_sub, total_mul]
  change 2*(2*posSum m-posCount m) = _
  have hh := positives m
  omega

private theorem pos_sum_step (m : ℕ) :
    posSum (m+1) = ((m : ℤ)+1)*(count m 0+count m 1) := by
  have h := W_sum m positive
  have hl : W (m+1) positive = posSum (m+1) := by
    unfold W posSum total
    apply sum_congr rfl
    intro w _
    dsimp only [positive]
    split <;> omega
  have hr : total m (fun w => positive (1+endpoint w)-positive (-1+endpoint w)) =
      count m 0+count m 1 := by
    unfold count
    rw [← total_add]
    unfold total
    apply sum_congr rfl
    intro w _
    dsimp only [positive]
    split <;> split <;> split <;> split <;> omega
  rw [hl,hr] at h
  exact h

private theorem one_count_weight (m : ℕ) :
    count (m+1) 1 = ((m : ℤ)+1)*(count m 0-count m 2) := by
  let g (e : ℤ) := if e=1 then (1:ℤ) else 0
  have h := W_sum m g
  have hl : W (m+1) g = count (m+1) 1 := by
    unfold W count total
    apply sum_congr rfl
    intro w _
    dsimp only [g]
    split <;> simp_all
  have hr : total m (fun w => g (1+endpoint w)-g (-1+endpoint w)) =
      count m 0-count m 2 := by
    unfold count
    rw [← total_sub]
    unfold total
    apply sum_congr rfl
    intro w _
    simp only [g, show ∀ e : ℤ, 1+e=1 ↔ e=0 by intro e; omega,
      show ∀ e : ℤ, -1+e=1 ↔ e=2 by intro e; omega]
  rw [hl,hr] at h
  exact h

private theorem central_step (m : ℕ) :
    count (m+1) 0 = count m 0+2*count m 1 := by
  rw [count_step, show (0:ℤ)-1 = -1 by decide, count_neg, zero_add]
  ring

private theorem central_rec (m : ℕ) :
    ((m : ℤ)+2)*count (m+2) 0 =
      (2*(m : ℤ)+3)*count (m+1) 0+3*((m : ℤ)+1)*count m 0 := by
  have hw := one_count_weight m
  have hs := count_step m 1
  simp only [sub_self, show (1:ℤ)+1=2 by decide] at hs
  have hc : ((m : ℤ)+2)*count (m+1) 1 =
      ((m : ℤ)+1)*(2*count m 0+count m 1) := by
    linear_combination hw + ((m:ℤ)+1)*hs
  have hb := central_step m
  have hb' := central_step (m+1)
  linear_combination ((m:ℤ)+2)*hb' + 2*hc - ((m:ℤ)+1)*hb

private theorem king_formula (m : ℕ) :
    (a (m+2) : ℤ) = ((m : ℤ)+3)*3^(m+1) -
      (2*(m : ℤ)+3)*count (m+1) 0 - 2*((m : ℤ)+1)*count m 0 := by
  have hk := king_H (m+1)
  rw [reflection (m+1) 0 (by decide)] at hk
  simp only [Nat.cast_add, Nat.cast_one] at hk
  have he := E_zero (m+1)
  have hp := pos_sum_step m
  have hc := central_step m
  linear_combination hk - he - 4*hp + 2*((m:ℤ)+1)*hc

private theorem starting_values :
    (a 1 : ℤ) = 1 ∧ (a 2 : ℤ) = 4 ∧ (a 3 : ℤ) = 17 ∧
      (a 4 : ℤ) = 68 ∧ (a 5 : ℤ) = 259 := by
  have ha := king_H 0
  have hb0 : count 0 0 = 1 := by simp [count, total_zero, endpoint, position]
  have hb1 : count 1 0 = 1 := by
    rw [central_step, hb0]
    simp [count, total_zero, endpoint, position]
  have h2 := central_rec 0
  have h3 := central_rec 1
  have h4 := central_rec 2
  have h2' : count 2 0 = 3 := by norm_num [hb0,hb1] at h2; omega
  have h3' : count 3 0 = 7 := by norm_num [h2',hb1] at h3; omega
  have h4' : count 4 0 = 19 := by norm_num [h3',h2'] at h4; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simpa [H,total_zero,peak] using ha
  · simpa [hb0,hb1] using king_formula 0
  · simpa [h2',hb1] using king_formula 1
  · simpa [h3',h2'] using king_formula 2
  · simpa [h4',h3'] using king_formula 3

private theorem king_rec (m : ℕ) :
    ((m : ℤ)+5) * (a (m+6) : ℤ) =
      27*((m : ℤ)+2)*(a (m+2) : ℤ)+27*(a (m+3) : ℤ) -
      9*(2*(m : ℤ)+9)*(a (m+4) : ℤ) + (8*(m : ℤ)+37)*(a (m+5) : ℤ) := by
  have hk0 := king_formula m
  have hk1 := king_formula (m+1)
  have hk2 := king_formula (m+2)
  have hk3 := king_formula (m+3)
  have hk4 := king_formula (m+4)
  have hr0 := central_rec m
  have hr1 := central_rec (m+1)
  have hr2 := central_rec (m+2)
  have hr3 := central_rec (m+3)
  simp only [Nat.add_assoc] at hk1 hk2 hk3 hk4 hr1 hr2 hr3
  rw [hk0,hk1,hk2,hk3,hk4]
  norm_num [Nat.cast_add, pow_add] at *
  linear_combination (-(2*(m:ℤ)+11))*hr3 + (10*(m:ℤ)+46)*hr2 -
    (6*(m:ℤ)+27)*hr1 - (18*(m:ℤ)+36)*hr0

end OMA.S_oeis_a081113

open OMA.S_oeis_a081113 in
theorem OMA.solution : type_of% @OMA.S_oeis_a081113.main := by
  intro n hn
  by_cases he : n=1
  · subst n
    obtain ⟨h1,h2,h3,h4,h5⟩ := starting_values
    norm_num [h1,h2,h3,h4,h5]
  · obtain ⟨m,rfl⟩ := Nat.exists_eq_add_of_le (show 2≤n by omega)
    have h := king_rec m
    simp only [Nat.add_comm 2 m, Nat.add_assoc, Nat.cast_add, Nat.cast_ofNat]
    linear_combination h
