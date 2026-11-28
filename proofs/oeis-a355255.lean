import OMAStatements.S_oeis_a355255
import Mathlib.Data.Finset.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- Problem: A355255: Cyclic binary differences on necklaces.
-- Upstream: formal-conjectures statements/oeis-a355255.lean:0 (declaration OMA.S_oeis_a355255.main)
-- Credit: Daniel Whorlow (@draonbioetl)
-- Disproof of the second conjecture at n = 37:
-- For n = 37 (not a power of 2), count 37 = 87382 = 1 + (2^18 - 1) / 3, which is not a power of 2.

namespace OMA_A355255

open OMA.S_oeis_a355255 Finset

/-! ### Part 1: Rotation and Frobenius iterates of `step` on `Word 37` -/

private def rot (j : ZMod 37) (w : Word 37) : Word 37 :=
  fun i => w (i + j)

private lemma rot_zero (w : Word 37) : rot 0 w = w := by
  funext i; simp [rot]

private lemma rot_rot (j1 j2 : ZMod 37) (w : Word 37) :
    rot j1 (rot j2 w) = rot (j1 + j2) w := by
  funext i; simp [rot, add_assoc]

private lemma rot_step (j : ZMod 37) (w : Word 37) :
    rot j (step w) = step (rot j w) := by
  funext i
  simp only [rot, step]
  ring_nf

private lemma rot_step_iter (j : ZMod 37) (t : ℕ) (w : Word 37) :
    rot j (step^[t] w) = step^[t] (rot j w) := by
  induction t generalizing w with
  | zero => rfl
  | succ t ih =>
    simp only [Function.iterate_succ_apply']
    rw [rot_step, ih]

private lemma necklace_eq_iff (u v : Word 37) :
    necklace u = necklace v ↔ ∃ j : ZMod 37, u = rot j v := by
  constructor
  · intro h
    have hu : u ∈ necklace u := ⟨0, by funext i; simp⟩
    rw [h] at hu
    rcases hu with ⟨j, hj⟩
    exact ⟨j, hj.symm⟩
  · rintro ⟨j, rfl⟩
    ext w
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨k + j, by funext i; simp [rot, add_assoc]⟩
    · rintro ⟨k, rfl⟩
      exact ⟨k - j, by funext i; simp [rot, add_assoc]⟩

private def stepR (r : ZMod 37) (w : Word 37) : Word 37 :=
  fun i => w i + w (i - r)

private lemma zmod2_add_self (x : ZMod 2) : x + x = 0 := by
  fin_cases x <;> decide

private lemma zmod2_sub_eq_add (x y : ZMod 2) : x - y = x + y := by
  fin_cases x <;> fin_cases y <;> decide

private lemma step_eq_stepR_one (w : Word 37) : step w = stepR 1 w := by
  funext i
  exact zmod2_sub_eq_add _ _

private lemma stepR_stepR (r : ZMod 37) (w : Word 37) :
    stepR r (stepR r w) = stepR (2 * r) w := by
  funext i
  simp only [stepR]
  have hsub : i - r - r = i - 2 * r := by ring
  rw [hsub]
  calc
    w i + w (i - r) + (w (i - r) + w (i - 2 * r))
        = w i + (w (i - r) + w (i - r)) + w (i - 2 * r) := by ring
    _ = w i + 0 + w (i - 2 * r) := by rw [zmod2_add_self]
    _ = w i + w (i - 2 * r) := by rw [add_zero]

private lemma step_iter_two_pow (k : ℕ) (w : Word 37) :
    step^[2 ^ k] w = stepR ((2 : ZMod 37) ^ k) w := by
  induction k generalizing w with
  | zero =>
    simpa using step_eq_stepR_one w
  | succ k ih =>
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    rw [hpow, Function.iterate_add_apply, ih, ih, stepR_stepR, pow_succ']

/-! ### Part 2: Parity and Hamming-weight invariants -/

private def parity (w : Word 37) : ZMod 2 :=
  ∑ i : ZMod 37, w i

private lemma parity_rot (j : ZMod 37) (w : Word 37) :
    parity (rot j w) = parity w := by
  unfold parity rot
  exact Fintype.sum_equiv (Equiv.addRight j) _ _ (fun _ => rfl)

private lemma parity_oneBead : parity (oneBead 37) = 1 := by
  unfold parity oneBead
  rw [Finset.sum_eq_single (0 : ZMod 37)]
  · simp
  · intro k _ hk; simp [hk]
  · intro h; exact absurd (mem_univ 0) h

private lemma parity_step (w : Word 37) : parity (step w) = 0 := by
  unfold parity step
  rw [Finset.sum_sub_distrib]
  have hshift : ∑ i : ZMod 37, w (i - 1) = ∑ i : ZMod 37, w i :=
    Fintype.sum_equiv (Equiv.subRight (1 : ZMod 37)) _ _ (fun _ => rfl)
  rw [hshift, sub_self]

private lemma parity_step_iter_succ (t : ℕ) :
    parity (step^[t + 1] (oneBead 37)) = 0 := by
  rw [Function.iterate_succ_apply']
  exact parity_step _

private def weight (w : Word 37) : ℕ :=
  (univ.filter (fun i : ZMod 37 => w i = 1)).card

private lemma weight_rot (j : ZMod 37) (w : Word 37) :
    weight (rot j w) = weight w := by
  unfold weight rot
  refine Finset.card_bij (fun i _ => i + j) ?_ ?_ ?_
  · intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact hi
  · intro a _ b _ h
    exact add_right_cancel h
  · intro b hb
    refine ⟨b - j, ?_, by ring⟩
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    simpa [sub_add_cancel] using hb

/-! ### Part 3: Fast 37-bit Frobenius evaluator and kernel verification -/

private def mask37 : ℕ := (1 <<< 37) - 1

private def Bounded37 (a : ℕ) : Prop :=
  ∀ k : ℕ, 37 ≤ k → a.testBit k = false

private def rotL37 (a j : ℕ) : ℕ :=
  (((a <<< j) &&& mask37) ||| (a >>> (37 - j)))

private def xorRot (a r : ℕ) : ℕ :=
  a ^^^ rotL37 a r

/-- Evaluates `step^[e * 2^k] (oneBead 37)` as a 37-bit bitmask when `r = 2^k % 37` and `e < 2^fuel`. -/
private def evalPowGen : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | fuel + 1, r, e =>
    if e = 0 then 1
    else
      let prev := evalPowGen fuel ((2 * r) % 37) (e / 2)
      if e % 2 = 0 then prev else xorRot prev r

private def popcount37Aux (a : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => popcount37Aux a k + if a.testBit k then 1 else 0

private def popcount37 (a : ℕ) : ℕ := popcount37Aux a 37

private def decode (a : ℕ) : Word 37 :=
  fun i => if a.testBit i.val then 1 else 0

private lemma testBit_mask37 (k : ℕ) : mask37.testBit k = decide (k < 37) := by
  have hm : mask37 = 2 ^ 37 - 1 := by decide
  rw [hm, Nat.testBit_two_pow_sub_one]

private lemma bounded37_one : Bounded37 1 := by
  intro k hk
  have : (1 : ℕ) = 2 ^ 0 := rfl
  rw [this, Nat.testBit_two_pow]
  simp [show 0 ≠ k by omega]

private lemma bounded37_three : Bounded37 3 := by
  intro k hk
  have hlt : 3 < 2 ^ k := by
    calc
      3 < 2 ^ 2 := by decide
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) (by omega)
  exact Nat.testBit_lt_two_pow hlt

private lemma bounded37_rotL37 {a j : ℕ} (ha : Bounded37 a) : Bounded37 (rotL37 a j) := by
  intro k hk
  unfold rotL37
  rw [Nat.testBit_or, Nat.testBit_and, testBit_mask37, Nat.testBit_shiftRight]
  have h1 : decide (k < 37) = false := by simp; omega
  have h2 : a.testBit (37 - j + k) = false := ha _ (by omega)
  simp [h1, h2]

private lemma bounded37_xor {a b : ℕ} (ha : Bounded37 a) (hb : Bounded37 b) :
    Bounded37 (a ^^^ b) := by
  intro k hk
  rw [Nat.testBit_xor, ha k hk, hb k hk]
  rfl

private lemma bounded37_xorRot {a r : ℕ} (ha : Bounded37 a) : Bounded37 (xorRot a r) :=
  bounded37_xor ha (bounded37_rotL37 ha)

private lemma bounded37_evalPowGen (fuel r e : ℕ) : Bounded37 (evalPowGen fuel r e) := by
  induction fuel generalizing r e with
  | zero => exact bounded37_one
  | succ fuel ih =>
    rw [evalPowGen]
    split_ifs
    · exact bounded37_one
    · exact ih _ _
    · exact bounded37_xorRot (ih _ _)

private lemma testBit_rotL37 {a j k : ℕ} (ha : Bounded37 a) (hj : j < 37) (hk : k < 37) :
    (rotL37 a j).testBit k = a.testBit ((k + 37 - j) % 37) := by
  unfold rotL37
  rw [Nat.testBit_or, Nat.testBit_and, testBit_mask37, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  have hlt : decide (k < 37) = true := by simp [hk]
  rw [hlt, Bool.and_true]
  by_cases hjk : j ≤ k
  · have hge : 37 ≤ 37 - j + k := by omega
    have hr : a.testBit (37 - j + k) = false := ha _ hge
    have hmod : (k + 37 - j) % 37 = k - j := by omega
    simp [hjk, hr, hmod]
  · have hmod : (k + 37 - j) % 37 = 37 - j + k := by omega
    simp [show ¬ j ≤ k by omega, hmod]

private lemma zmod37_sub_val (i : ZMod 37) (j : ℕ) (hj : j < 37) :
    (i - (j : ZMod 37)).val = (i.val + 37 - j) % 37 := by
  have hi : i.val < 37 := ZMod.val_lt i
  have hcast : ((i.val + 37 - j : ℕ) : ZMod 37) = i - (j : ZMod 37) := by
    have hle : j ≤ i.val + 37 := by omega
    rw [Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_zmod_val]
    have h37 : ((37 : ℕ) : ZMod 37) = 0 := by decide
    rw [h37, add_zero]
  rw [← hcast, ZMod.val_natCast]

private lemma decode_rotL37 {a j : ℕ} (ha : Bounded37 a) (hj : j < 37) :
    decode (rotL37 a j) = rot (-(j : ZMod 37)) (decode a) := by
  funext i
  unfold decode rot
  have hi : i.val < 37 := ZMod.val_lt i
  rw [testBit_rotL37 ha hj hi, ← zmod37_sub_val i j hj, sub_eq_add_neg]

private lemma decode_one : decode 1 = oneBead 37 := by
  funext i
  unfold decode oneBead
  by_cases hi : i = 0
  · subst hi; simp
  · have hval : i.val ≠ 0 := by
      intro h0
      apply hi
      exact ZMod.val_injective 37 (by simpa using h0)
    have hbit : (1 : ℕ).testBit i.val = false := by
      have : (1 : ℕ) = 2 ^ 0 := rfl
      rw [this, Nat.testBit_two_pow]
      simp [Ne.symm hval]
    simp [hi, hbit]

private lemma bool_xor_to_zmod2 (x y : Bool) :
    (if (x ^^ y) then (1 : ZMod 2) else 0) =
    (if x then (1 : ZMod 2) else 0) + (if y then (1 : ZMod 2) else 0) := by
  cases x <;> cases y <;> decide

private lemma decode_xorRot {a r : ℕ} (ha : Bounded37 a) (hr : r < 37) :
    decode (xorRot a r) = stepR (r : ZMod 37) (decode a) := by
  funext i
  unfold decode xorRot stepR
  rw [Nat.testBit_xor, bool_xor_to_zmod2]
  have hrot := congrFun (decode_rotL37 ha hr) i
  simpa [decode, rot, sub_eq_add_neg] using congrArg ((if a.testBit i.val = true then (1 : ZMod 2) else 0) + ·) hrot

private lemma decode_evalPowGen (fuel k e : ℕ) (he : e < 2 ^ fuel) :
    decode (evalPowGen fuel (2 ^ k % 37) e) = step^[e * 2 ^ k] (oneBead 37) := by
  induction fuel generalizing k e with
  | zero =>
    have he0 : e = 0 := by simp at he; exact he
    subst he0
    simp [evalPowGen, decode_one]
  | succ fuel ih =>
    rw [evalPowGen]
    by_cases he0 : e = 0
    · subst he0
      simp [decode_one]
    · simp only [he0, ↓reduceIte]
      have hmod : (2 * (2 ^ k % 37)) % 37 = 2 ^ (k + 1) % 37 := by
        rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, pow_succ']
      have hlt : e / 2 < 2 ^ fuel := by
        rw [pow_succ] at he; omega
      have hprev : decode (evalPowGen fuel ((2 * (2 ^ k % 37)) % 37) (e / 2)) =
          step^[(e / 2) * 2 ^ (k + 1)] (oneBead 37) := by
        rw [hmod]
        exact ih (k + 1) (e / 2) hlt
      split_ifs with heven
      · rw [hprev]
        congr 1
        rw [pow_succ']
        have : e = 2 * (e / 2) := by omega
        calc
          (e / 2) * (2 * 2 ^ k) = (2 * (e / 2)) * 2 ^ k := by ring
          _ = e * 2 ^ k := by rw [← this]
      · have hb : Bounded37 (evalPowGen fuel ((2 * (2 ^ k % 37)) % 37) (e / 2)) :=
          bounded37_evalPowGen _ _ _
        have hlt37 : 2 ^ k % 37 < 37 := Nat.mod_lt _ (by decide)
        rw [decode_xorRot hb hlt37, hprev]
        have hcast : ((2 ^ k % 37 : ℕ) : ZMod 37) = (2 : ZMod 37) ^ k := by
          rw [ZMod.natCast_mod, Nat.cast_pow, Nat.cast_ofNat]
        rw [hcast, ← step_iter_two_pow, ← Function.iterate_add_apply]
        congr 1
        rw [pow_succ']
        have : e = 2 * (e / 2) + 1 := by omega
        calc
          2 ^ k + (e / 2) * (2 * 2 ^ k) = (2 * (e / 2) + 1) * 2 ^ k := by ring
          _ = e * 2 ^ k := by rw [← this]

private lemma weight_decode (a : ℕ) : weight (decode a) = popcount37 a := by
  unfold weight popcount37
  have haux : ∀ m : ℕ, m ≤ 37 →
      popcount37Aux a m = ((range m).filter (fun k => a.testBit k = true)).card := by
    intro m hm
    induction m with
    | zero => simp [popcount37Aux]
    | succ m ih =>
      rw [popcount37Aux, ih (by omega), range_add_one, filter_insert]
      have hnotmem : m ∉ (range m).filter (fun k => a.testBit k = true) := by
        simp
      by_cases hbit : a.testBit m = true
      · simp [hbit, card_insert_of_notMem hnotmem]
      · simp [hbit]
  rw [haux 37 (le_refl 37)]
  refine Finset.card_bij (fun (i : ZMod 37) _ => i.val) ?_ ?_ ?_
  · intro i hi
    have hi' : decode a i = 1 := (Finset.mem_filter.mp hi).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt i), ?_⟩
    by_contra hf
    have hbf : a.testBit i.val = false := by cases h : a.testBit i.val <;> simp_all
    simp [decode, hbf] at hi'
  · intro i1 _ i2 _ hEq
    exact ZMod.val_injective 37 hEq
  · intro k hk
    have hk' := Finset.mem_filter.mp hk
    have hklt : k < 37 := Finset.mem_range.mp hk'.1
    have hkbit : a.testBit k = true := hk'.2
    refine ⟨(k : ZMod 37), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
    · simp [decode, ZMod.val_natCast, Nat.mod_eq_of_lt hklt, hkbit]
    · rw [ZMod.val_natCast, Nat.mod_eq_of_lt hklt]

/-! ### Part 4: Instant kernel computations at `n = 37` and period = `87381` -/

private lemma eval_period : evalPowGen 18 1 87382 = rotL37 3 12 := by decide

private lemma popcount_gen : popcount37 3 = 2 := by decide
private lemma popcount_d1 : popcount37 (evalPowGen 18 1 29128) = 20 := by decide
private lemma popcount_d2 : popcount37 (evalPowGen 18 1 12484) = 18 := by decide
private lemma popcount_d3 : popcount37 (evalPowGen 18 1 4600) = 12 := by decide
private lemma popcount_d4 : popcount37 (evalPowGen 18 1 1198) = 18 := by decide

private abbrev W (t : ℕ) : Word 37 := step^[t] (oneBead 37)

private lemma W_eq_decode_eval (t : ℕ) (ht : t < 2 ^ 18) : W t = decode (evalPowGen 18 1 t) := by
  have h := decode_evalPowGen 18 0 t ht
  simpa [W] using h.symm

private lemma W_one_eq_decode_three : W 1 = decode 3 := by
  rw [W_eq_decode_eval 1 (by decide)]
  have h1 : evalPowGen 18 1 1 = 3 := by decide
  rw [h1]

private lemma W_period_base : W 87382 = rot (-(12 : ZMod 37)) (W 1) := by
  rw [W_eq_decode_eval 87382 (by decide), eval_period,
    decode_rotL37 bounded37_three (by decide), W_one_eq_decode_three]
  norm_cast

private lemma W_add_period (t : ℕ) (ht : 1 ≤ t) :
    W (t + 87381) = rot (-(12 : ZMod 37)) (W t) := by
  have hrew : t + 87381 = (t - 1) + 87382 := by omega
  rw [W, hrew, Function.iterate_add_apply]
  change step^[t - 1] (W 87382) = rot (-(12 : ZMod 37)) (W t)
  rw [W_period_base, ← rot_step_iter, W, ← Function.iterate_add_apply]
  congr 2; omega

private lemma W_add_mul_period (t m : ℕ) (ht : 1 ≤ t) :
    ∃ j : ZMod 37, W (t + 87381 * m) = rot j (W t) := by
  induction m with
  | zero =>
    exact ⟨0, by simp [rot_zero]⟩
  | succ m ih =>
    rcases ih with ⟨j, hj⟩
    have hrew : t + 87381 * (m + 1) = (t + 87381 * m) + 87381 := by ring
    rw [hrew, W_add_period _ (by omega), hj, rot_rot]
    exact ⟨_, rfl⟩

private def H : Set ℕ := {r : ℕ | ∃ j : ZMod 37, W (1 + r) = rot j (W 1)}

private lemma mem_H_period : 87381 ∈ H := ⟨-(12 : ZMod 37), W_period_base⟩

private lemma mem_H_add {a b : ℕ} (ha : a ∈ H) (hb : b ∈ H) : a + b ∈ H := by
  rcases ha with ⟨ja, hja⟩
  rcases hb with ⟨jb, hjb⟩
  refine ⟨ja + jb, ?_⟩
  have hrew : 1 + (a + b) = b + (1 + a) := by omega
  rw [W, hrew, Function.iterate_add_apply]
  change step^[b] (W (1 + a)) = rot (ja + jb) (W 1)
  rw [hja, ← rot_step_iter]
  have hrew2 : step^[b] (W 1) = W (1 + b) := by
    rw [W, W, ← Function.iterate_add_apply]; congr 1; omega
  rw [hrew2, hjb, rot_rot]

private lemma mem_H_mul {a : ℕ} (ha : a ∈ H) (k : ℕ) : k * a ∈ H := by
  induction k with
  | zero =>
    exact ⟨0, by simp [rot_zero]⟩
  | succ k ih =>
    rw [Nat.succ_mul]
    exact mem_H_add ih ha

private lemma mem_H_of_W_rot {s t : ℕ} (hs : 1 ≤ s) (hst : s ≤ t) {j : ZMod 37}
    (hEq : W t = rot j (W s)) : t - s ∈ H := by
  set k := 87381 * s + 1 - s
  have hks : k + s = 1 + 87381 * s := by omega
  have hkt : k + t = (1 + (t - s)) + 87381 * s := by omega
  have h1 : W (k + t) = rot j (W (k + s)) := by
    rw [W, Function.iterate_add_apply]
    change step^[k] (W t) = rot j (W (k + s))
    rw [hEq, ← rot_step_iter, W, ← Function.iterate_add_apply]
  rw [hkt, hks] at h1
  obtain ⟨j1, hj1⟩ := W_add_mul_period (1 + (t - s)) s (by omega)
  obtain ⟨j2, hj2⟩ := W_add_mul_period 1 s (le_refl 1)
  rw [hj1, hj2, rot_rot] at h1
  refine ⟨-j1 + (j + j2), ?_⟩
  have hcancel := congrArg (rot (-j1)) h1
  rw [rot_rot, neg_add_cancel, rot_zero, rot_rot] at hcancel
  exact hcancel

private lemma mem_H_sub {a b : ℕ} (ha : a ∈ H) (hb : b ∈ H) (hab : a ≤ b) : b - a ∈ H := by
  rcases ha with ⟨ja, hja⟩
  rcases hb with ⟨jb, hjb⟩
  have hEq : W (1 + b) = rot (jb - ja) (W (1 + a)) := by
    rw [hja, hjb, rot_rot]
    congr 1; ring
  have hsub := mem_H_of_W_rot (by omega : 1 ≤ 1 + a) (by omega : 1 + a ≤ 1 + b) hEq
  simpa [show (1 + b) - (1 + a) = b - a by omega] using hsub

private lemma mem_H_gcd (a b : ℕ) (ha : a ∈ H) (hb : b ∈ H) : Nat.gcd a b ∈ H := by
  induction hsum : a + b using Nat.strongRecOn generalizing a b with
  | ind n ih =>
    by_cases ha0 : a = 0
    · subst ha0; simpa using hb
    · by_cases hb0 : b = 0
      · subst hb0; simpa using ha
      · rcases le_total a b with hab | hba
        · have hgcd : Nat.gcd a b = Nat.gcd a (b - a) := by
            rw [Nat.gcd_comm a b, ← Nat.gcd_sub_self_left hab, Nat.gcd_comm]
          rw [hgcd]
          exact ih (a + (b - a)) (by omega) a (b - a) ha (mem_H_sub ha hb hab) rfl
        · have hgcd : Nat.gcd a b = Nat.gcd (a - b) b :=
            (Nat.gcd_sub_self_left hba).symm
          rw [hgcd]
          exact ih ((a - b) + b) (by omega) (a - b) b (mem_H_sub hb ha hba) hb rfl

private lemma not_mem_H_of_weight_ne {r : ℕ} (hw : weight (W (1 + r)) ≠ 2) : r ∉ H := by
  rintro ⟨j, hj⟩
  apply hw
  rw [hj, weight_rot, W_one_eq_decode_three, weight_decode, popcount_gen]

private lemma not_mem_H_d1 : 29127 ∉ H :=
  not_mem_H_of_weight_ne (by rw [show 1 + 29127 = 29128 by rfl, W_eq_decode_eval _ (by decide), weight_decode, popcount_d1]; decide)

private lemma not_mem_H_d2 : 12483 ∉ H :=
  not_mem_H_of_weight_ne (by rw [show 1 + 12483 = 12484 by rfl, W_eq_decode_eval _ (by decide), weight_decode, popcount_d2]; decide)

private lemma not_mem_H_d3 : 4599 ∉ H :=
  not_mem_H_of_weight_ne (by rw [show 1 + 4599 = 4600 by rfl, W_eq_decode_eval _ (by decide), weight_decode, popcount_d3]; decide)

private lemma not_mem_H_d4 : 1197 ∉ H :=
  not_mem_H_of_weight_ne (by rw [show 1 + 1197 = 1198 by rfl, W_eq_decode_eval _ (by decide), weight_decode, popcount_d4]; decide)

/-- Every proper divisor of `87381 = 3^2 * 7 * 19 * 73` divides one of the 4 maximal proper divisors. -/
private lemma proper_dvd_87381 {d : ℕ} (hd : d ∣ 87381) (hlt : d < 87381) :
    d ∣ 29127 ∨ d ∣ 12483 ∨ d ∣ 4599 ∨ d ∣ 1197 := by
  rcases hd with ⟨q, hq⟩
  have hq2 : 2 ≤ q := by
    by_contra hlt2
    have hcases : q = 0 ∨ q = 1 := by omega
    rcases hcases with rfl | rfl <;> omega
  have hpfac : q.minFac ∣ 87381 := dvd_trans (Nat.minFac_dvd q) ⟨d, by rw [mul_comm]; exact hq⟩
  have hp_prime : Nat.Prime q.minFac := Nat.minFac_prime (by omega)
  have h87 : 87381 = 3 * 3 * 7 * 19 * 73 := by decide
  rw [h87] at hpfac
  have hp_mem : q.minFac = 3 ∨ q.minFac = 7 ∨ q.minFac = 19 ∨ q.minFac = 73 := by
    have hdiv_prime : ∀ p : ℕ, Nat.Prime p → q.minFac ∣ p → q.minFac = p := by
      intro p hp hdp
      exact ((Nat.dvd_prime hp).mp hdp).resolve_left hp_prime.ne_one
    rcases hp_prime.dvd_mul.mp hpfac with h1 | h73
    · rcases hp_prime.dvd_mul.mp h1 with h2 | h19
      · rcases hp_prime.dvd_mul.mp h2 with h3 | h7
        · rcases hp_prime.dvd_mul.mp h3 with h3a | h3b
          · exact Or.inl (hdiv_prime 3 (by decide) h3a)
          · exact Or.inl (hdiv_prime 3 (by decide) h3b)
        · exact Or.inr (Or.inl (hdiv_prime 7 (by decide) h7))
      · exact Or.inr (Or.inr (Or.inl (hdiv_prime 19 (by decide) h19)))
    · exact Or.inr (Or.inr (Or.inr (hdiv_prime 73 (by decide) h73)))
  rcases Nat.minFac_dvd q with ⟨r, hr⟩
  rcases hp_mem with hp | hp | hp | hp
  · left; refine ⟨r, ?_⟩; rw [hr, hp] at hq; linarith
  · right; left; refine ⟨r, ?_⟩; rw [hr, hp] at hq; linarith
  · right; right; left; refine ⟨r, ?_⟩; rw [hr, hp] at hq; linarith
  · right; right; right; refine ⟨r, ?_⟩; rw [hr, hp] at hq; linarith

private lemma not_mem_H_lt {r : ℕ} (hr1 : 1 ≤ r) (hr2 : r < 87381) : r ∉ H := by
  intro hrH
  have hgcdH : Nat.gcd r 87381 ∈ H := mem_H_gcd r 87381 hrH mem_H_period
  have hd : Nat.gcd r 87381 ∣ 87381 := Nat.gcd_dvd_right r 87381
  have hlt : Nat.gcd r 87381 < 87381 := lt_of_le_of_lt (Nat.gcd_le_left 87381 (by omega)) hr2
  rcases proper_dvd_87381 hd hlt with h1 | h2 | h3 | h4
  · rcases h1 with ⟨k, hk⟩
    exact not_mem_H_d1 (hk ▸ (mul_comm _ k ▸ mem_H_mul hgcdH k))
  · rcases h2 with ⟨k, hk⟩
    exact not_mem_H_d2 (hk ▸ (mul_comm _ k ▸ mem_H_mul hgcdH k))
  · rcases h3 with ⟨k, hk⟩
    exact not_mem_H_d3 (hk ▸ (mul_comm _ k ▸ mem_H_mul hgcdH k))
  · rcases h4 with ⟨k, hk⟩
    exact not_mem_H_d4 (hk ▸ (mul_comm _ k ▸ mem_H_mul hgcdH k))

/-! ### Part 5: Exact necklace count `count 37 = 87382` and disproof -/

private lemma count_37_eq : count 37 = 87382 := by
  unfold count
  let f : Fin 87382 → Set.range (fun t : ℕ => necklace (W t)) :=
    fun t => ⟨necklace (W t.val), ⟨t.val, rfl⟩⟩
  have hbij : Function.Bijective f := by
    constructor
    · intro s t hEq
      have hneck : necklace (W s.val) = necklace (W t.val) := congrArg Subtype.val hEq
      rcases (necklace_eq_iff _ _).mp hneck with ⟨j, hj⟩
      by_contra hne
      have hval_ne : s.val ≠ t.val := fun h => hne (Fin.ext h)
      have hpar_zero_ne : ∀ u : ℕ, 1 ≤ u → ∀ j' : ZMod 37, W 0 ≠ rot j' (W u) := by
        intro u hu j' h0
        have hp := congrArg parity h0
        rw [parity_rot] at hp
        have hp0 : parity (W 0) = 1 := parity_oneBead
        have hpu : parity (W u) = 0 := by
          have : u = (u - 1) + 1 := by omega
          rw [this]; exact parity_step_iter_succ (u - 1)
        rw [hp0, hpu] at hp
        exact (by decide : (1 : ZMod 2) ≠ 0) hp
      by_cases hs0 : s.val = 0
      · exact hpar_zero_ne t.val (by omega) j (hs0 ▸ hj)
      · by_cases ht0 : t.val = 0
        · have hj' : W 0 = rot (-j) (W s.val) := by
            have := congrArg (rot (-j)) hj
            rw [rot_rot, neg_add_cancel, rot_zero] at this
            rw [← ht0]; exact this.symm
          exact hpar_zero_ne s.val (by omega) (-j) hj'
        · rcases lt_or_gt_of_ne hval_ne with hlt | hgt
          · have hj' : W t.val = rot (-j) (W s.val) := by
              have := congrArg (rot (-j)) hj
              rw [rot_rot, neg_add_cancel, rot_zero] at this
              exact this.symm
            have hH := mem_H_of_W_rot (by omega : 1 ≤ s.val) (by omega) hj'
            exact not_mem_H_lt (by omega) (by omega) hH
          · have hH := mem_H_of_W_rot (by omega : 1 ≤ t.val) (by omega) hj
            exact not_mem_H_lt (by omega) (by omega) hH
    · rintro ⟨S, t, rfl⟩
      by_cases ht0 : t = 0
      · subst ht0
        exact ⟨⟨0, by decide⟩, rfl⟩
      · set r := (t - 1) % 87381
        set q := (t - 1) / 87381
        have hrlt : r + 1 < 87382 := by
          have : r < 87381 := Nat.mod_lt _ (by decide)
          omega
        refine ⟨⟨r + 1, hrlt⟩, ?_⟩
        apply Subtype.ext
        change necklace (W (r + 1)) = necklace (W t)
        have ht_eq : t = (r + 1) + 87381 * q := by
          have hdiv := Nat.div_add_mod (t - 1) 87381
          omega
        obtain ⟨j, hj⟩ := W_add_mul_period (r + 1) q (by omega)
        rw [← ht_eq] at hj
        exact ((necklace_eq_iff _ _).mpr ⟨-j, by
          have := congrArg (rot (-j)) hj
          rw [rot_rot, neg_add_cancel, rot_zero] at this
          exact this.symm⟩)
  rw [← Nat.card_congr (Equiv.ofBijective f hbij)]
  simp

private lemma not_pow2_37 : ¬ ∃ j : ℕ, 37 = 2 ^ j := by
  rintro ⟨j, hj⟩
  have hlt : j < 6 := by
    by_contra hge
    have : 2 ^ 6 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hle : 2 ^ j ≤ 2 ^ 5 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

private lemma not_pow2_87382 : ¬ ∃ j : ℕ, 87382 = 2 ^ j := by
  rintro ⟨j, hj⟩
  have hlt : j < 17 := by
    by_contra hge
    have : 2 ^ 17 ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hle : 2 ^ j ≤ 2 ^ 16 := Nat.pow_le_pow_right (by omega) (by omega)
  omega

private lemma main_false : ¬ (
    (∀ m : ℕ, 1 < m → count (2 ^ m) = 2 ^ m + 1) ∧
    (∀ n : ℕ, 0 < n → (¬ ∃ j : ℕ, n = 2 ^ j) → ∃ j : ℕ, count n = 2 ^ j)) := by
  intro ⟨_, h2⟩
  have hpow := h2 37 (by decide) not_pow2_37
  rw [count_37_eq] at hpow
  exact not_pow2_87382 hpow

end OMA_A355255

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a355255.main) :=
  OMA_A355255.main_false
