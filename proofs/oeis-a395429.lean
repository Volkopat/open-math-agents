import OMAStatements.S_oeis_a395429
import Mathlib

open OMA.S_oeis_a395429

private theorem digit_bounds (x : ℕ) :
    leading x * 10 ^ Nat.log 10 x ≤ x ∧
      x < (leading x + 1) * 10 ^ Nat.log 10 x := by
  unfold leading
  exact ⟨Nat.div_mul_le_self _ _, (Nat.div_lt_iff_lt_mul (by positivity)).mp (Nat.lt_succ_self _)⟩

private theorem digit_lt_ten (x : ℕ) : leading x < 10 := by
  unfold leading
  apply (Nat.div_lt_iff_lt_mul (by positivity)).mpr
  simpa [pow_succ, Nat.mul_comm] using Nat.lt_pow_succ_log_self (by decide : 1 < 10) x

private theorem same_digit_bound {x y : ℕ} (hy : 0 < y) (h : leading x = leading y) :
    x * 10 ^ Nat.log 10 y < 2 * y * 10 ^ Nat.log 10 x := by
  let A := 10 ^ Nat.log 10 x
  let B := 10 ^ Nat.log 10 y
  have hB : 0 < B := by dsimp [B]; positivity
  have hl : 1 ≤ leading y := by
    unfold leading
    apply (Nat.le_div_iff_mul_le hB).mpr
    simpa [B] using Nat.pow_log_le_self 10 (ne_of_gt hy)
  have hub : x < (leading y + 1) * A := by
    simpa only [A, h] using (digit_bounds x).2
  have hcap : (leading y + 1) * B ≤ 2 * y := calc
    (leading y + 1) * B ≤ (2 * leading y) * B := Nat.mul_le_mul_right B (by omega)
    _ = 2 * (leading y * B) := by ring
    _ ≤ 2 * y := Nat.mul_le_mul_left 2 (digit_bounds y).1
  calc
    x * B < ((leading y + 1) * A) * B := Nat.mul_lt_mul_of_pos_right hub hB
    _ = ((leading y + 1) * B) * A := by ring
    _ ≤ (2 * y) * A := Nat.mul_le_mul_right A hcap

private theorem third_digit_changes {b c : ℕ} (hb : 0 < b) (hc : leading c = 3) :
    leading (b * c) ≠ leading b := by
  intro h
  let A := 10 ^ Nat.log 10 (b * c)
  let B := 10 ^ Nat.log 10 b
  let C := 10 ^ Nat.log 10 c
  have hc₁ : 3 * C ≤ c := by simpa only [C, hc] using (digit_bounds c).1
  have hc₂ : c < 4 * C := by simpa only [C, hc] using (digit_bounds c).2
  have hcp : 0 < c := (by positivity : 0 < 3 * C).trans_le hc₁
  have hB : 0 < B := by dsimp [B]; positivity
  have h₁ : c * B < 2 * A := by
    apply (Nat.mul_lt_mul_left hb).mp
    calc
      b * (c * B) = (b * c) * B := by ring
      _ < 2 * b * A := same_digit_bound hb h
      _ = b * (2 * A) := by ring
  have h₂ : A < 2 * (c * B) := by
    apply (Nat.mul_lt_mul_left hb).mp
    calc
      b * A < 2 * (b * c) * B := same_digit_bound (Nat.mul_pos hb hcp) h.symm
      _ = b * (2 * (c * B)) := by ring
  have hl : 3 * (B * C) ≤ c * B := calc
    3 * (B * C) = (3 * C) * B := by ring
    _ ≤ c * B := Nat.mul_le_mul_right B hc₁
  have hu : c * B < 4 * (B * C) := calc
    c * B < (4 * C) * B := Nat.mul_lt_mul_of_pos_right hc₂ hB
    _ = 4 * (B * C) := by ring
  let e := Nat.log 10 b + Nat.log 10 c
  have he : 10 ^ e = B * C := by simp [e, B, C, pow_add]
  have hlo : 10 ^ e < A := by omega
  have hhi : A < 10 ^ (e + 1) := by rw [pow_succ, he]; omega
  have hp : StrictMono (fun n : ℕ => (10 : ℕ) ^ n) :=
    pow_right_strictMono₀ (by decide : 1 < (10 : ℕ))
  have hh₁ : e < Nat.log 10 (b * c) := hp.lt_iff_lt.mp hlo
  have hh₂ : Nat.log 10 (b * c) < e + 1 := hp.lt_iff_lt.mp hhi
  omega

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a395429.main) := by
  rintro ⟨_, C, hC⟩
  let digits (i : Fin (10 ^ C + 1)) (k : Fin C) : Fin 10 :=
    ⟨leading ((k.val + 1) ^ i.val), digit_lt_ten _⟩
  have hcard : Fintype.card (Fin C → Fin 10) < Fintype.card (Fin (10 ^ C + 1)) := by simp
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt digits hcard
  have impossible {u v : Fin (10 ^ C + 1)} (h : u.val < v.val) :
      digits u ≠ digits v := by
    intro hs
    obtain ⟨k, hk₁, hk₂, hk₃⟩ := hC (v.val - u.val) (by omega) 3 (by omega) (by omega)
    let p : Fin C := ⟨k - 1, by omega⟩
    have hn := congrArg (fun w : Fin C → Fin 10 => (w p).val) hs
    change leading ((k - 1 + 1) ^ u.val) = leading ((k - 1 + 1) ^ v.val) at hn
    rw [show k - 1 + 1 = k by omega, show v.val = u.val + (v.val - u.val) by omega,
      pow_add] at hn
    exact third_digit_changes (pow_pos (by omega : 0 < k) _) hk₃ hn.symm
  have hne : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hne with h | h
  · exact impossible h heq
  · exact impossible h heq.symm