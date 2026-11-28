import OMAStatements.S_oeis_a209649
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Order.Fin.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Tactic.NormNum
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-!
The vertical triple test and the conversion to a descending sequence of rows
are adapted from the earlier A208140 proof (commit 43e1d4751fb3b80ac147446edb92affa0c2f38a7).
The first row is unrestricted among the horizontally admissible rows. The
remaining rows form a weakly descending chain. A finite transfer operator
checks the contribution of every possible length of the underlying strict chain.
-/

namespace OMA.BinaryChains

variable {A B : Type*} [Preorder B] (f : A → B)

abbrev Chain (n : ℕ) := {g : Fin n → A // Antitone (f ∘ g)}
abbrev Tail (p : A) (n : ℕ) :=
  {g : Fin n → A // Antitone (f ∘ g) ∧ ∀ k, f (g k) ≤ f p}

def extend {n : ℕ} (p : A) (u : Tail f p n) : Chain f (n+1) :=
  ⟨Fin.cons p u.val, by
    intro i j hij
    cases i using Fin.cases <;> cases j using Fin.cases
    · exact le_rfl
    · exact u.property.2 _
    · exact False.elim (by simp at hij)
    · exact u.property.1 (Fin.succ_le_succ_iff.mp hij)⟩

def drop {n : ℕ} (u : Chain f (n+1)) : Tail f (u.val 0) n :=
  ⟨fun i => u.val i.succ, (fun _ _ h => u.property (Fin.succ_le_succ_iff.mpr h)),
    fun i => u.property (Fin.zero_le i.succ)⟩

def splitChain (n : ℕ) : Chain f (n+1) ≃ (p : A) × Tail f p n where
  toFun u := ⟨u.val 0, drop f u⟩
  invFun z := extend f z.1 z.2
  left_inv u := by
    apply Subtype.ext
    funext i
    cases i using Fin.cases <;> rfl
  right_inv z := by rcases z with ⟨p, ⟨u,h⟩⟩; rfl

def splitTail (p : A) (n : ℕ) : Tail f p (n+1) ≃
    (q : {q : A // f q ≤ f p}) × Tail f q.val n where
  toFun u := ⟨⟨u.val 0, u.property.2 0⟩, drop f ⟨u.val, u.property.1⟩⟩
  invFun z :=
    ⟨(extend f z.1.val z.2).val, (extend f z.1.val z.2).property, by
      intro i
      cases i using Fin.cases with
      | zero => exact z.1.property
      | succ k => exact (z.2.property.2 k).trans z.1.property⟩
  left_inv u := by
    apply Subtype.ext
    funext i
    cases i using Fin.cases <;> rfl
  right_inv z := by rcases z with ⟨⟨q,hq⟩,⟨u,hu⟩⟩; rfl

theorem tail_zero (p : A) : Nat.card (Tail f p 0) = 1 := by
  let e : Tail f p 0 ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨Fin.elim0, (fun i => i.elim0), fun i => i.elim0⟩
      left_inv := fun _ => Subtype.ext (funext fun i => i.elim0)
      right_inv := fun _ => rfl }
  simpa using Nat.card_congr e

theorem chain_zero : Nat.card (Chain f 0) = 1 := by
  let e : Chain f 0 ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨Fin.elim0, fun i => i.elim0⟩
      left_inv := fun _ => Subtype.ext (funext fun i => i.elim0)
      right_inv := fun _ => rfl }
  simpa using Nat.card_congr e

variable [Fintype A] [DecidableLE B]

def step : (A → ℕ) →ₗ[ℕ] (A → ℕ) where
  toFun g p := ∑ q : {q : A // f q ≤ f p}, g q.val
  map_add' g h := by funext p; exact Finset.sum_add_distrib
  map_smul' c g := by funext p; exact (Finset.mul_sum _ _ _).symm

theorem tail_succ (n : ℕ) :
    (fun p => Nat.card (Tail f p (n+1))) = step f (fun p => Nat.card (Tail f p n)) := by
  funext p
  exact (Nat.card_congr (splitTail f p n)).trans Nat.card_sigma

omit [DecidableLE B] in
theorem chain_card_succ (n : ℕ) : Nat.card (Chain f (n+1)) = ∑ p, Nat.card (Tail f p n) :=
  (Nat.card_congr (splitChain f n)).trans Nat.card_sigma

end OMA.BinaryChains

namespace OMA.S_oeis_a209649

open OMA.BinaryChains

private abbrev Row := Fin 7 → Fin 2
private abbrev Code := Fin 35

local instance : DecidableLE Row := fun a b => inferInstanceAs (Decidable (∀ j, a j ≤ b j))

private theorem scaled (n : ℕ) (v : Code → ℕ) (p : Code) : (n • v) p = n * v p :=
  nsmul_eq_mul n (v p)

private def readRow (r : Row) (j : ℕ) : ℕ := if hj : j < 7 then r ⟨j,hj⟩ else 0

private def horizontal (r : Row) : Bool := decide (∀ k : Fin 5, let j := k.val;
  (readRow r j, readRow r (j+1), readRow r (j+2)) ≠ (0,0,1) ∧
  (readRow r j, readRow r (j+1), readRow r (j+2)) ≠ (1,0,0))

/-- Binary masks for the admissible rows in increasing order. -/
private def masks : Array ℕ := #[0, 42, 43, 45, 46, 47, 53, 54, 55, 58, 59, 61, 62, 63, 85, 86, 87, 90, 91, 93, 94, 95, 106, 107, 109, 110, 111, 117, 118, 119, 122, 123, 125, 126, 127]
private def bits (c : Code) (j : Fin 7) : Fin 2 :=
  if (masks[c.val]!).testBit j.val then 1 else 0

private def encode (r : Row) : Code :=
  let word := ∑ j : Fin 7, (r j).val * 2^j.val
  Fin.ofNat 35 ((#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 0, 3, 4, 5, 0, 0, 0, 0, 0, 6, 7, 8, 0, 0, 9, 10, 0, 11, 12, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 14, 15, 16, 0, 0, 17, 18, 0, 19, 20, 21, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 22, 23, 0, 24, 25, 26, 0, 0, 0, 0, 0, 27, 28, 29, 0, 0, 30, 31, 0, 32, 33, 34] : Array ℕ)[word]!)

set_option maxRecDepth 10000 in
private theorem encode_bits : ∀ c, encode (bits c) = c := by decide +kernel
set_option maxRecDepth 10000 in
private theorem horiz_bits : ∀ c, horizontal (bits c) = true := by decide +kernel
set_option maxRecDepth 10000 in
private theorem bits_encode : ∀ r : Row, horizontal r = true → ∀ j, bits (encode r) j = r j := by
  decide +kernel
private theorem vertical_iff : ∀ p q r : Fin 2,
    (((p : ℕ), (q : ℕ), (r : ℕ)) ≠ (0,0,1) ∧
     ((p : ℕ), (q : ℕ), (r : ℕ)) ≠ (1,0,1)) ↔ r ≤ q := by decide

private theorem get_read {n : ℕ} (x : Fin n → Row) {i : ℕ} (hi : i < n) (j : ℕ) :
    get x i j = readRow (x ⟨i,hi⟩) j := by
  by_cases hj : j < 7 <;> simp [get, readRow, hi, hj]

private theorem avoids_iff {n : ℕ} (x : Fin (n+1) → Row) :
    avoids x = true ↔ (∀ i, horizontal (x i) = true) ∧
      ∀ j : Fin 7, Antitone (fun i : Fin n => x i.succ j) := by
  simp only [avoids, decide_eq_true_eq]
  constructor
  · rintro ⟨hh,hv⟩
    constructor
    · intro i
      unfold horizontal
      apply decide_eq_true
      intro j
      simpa only [get_read x i.isLt] using hh i.val i.isLt j.val j.isLt
    · intro j
      cases n with
      | zero => exact fun i => Fin.elim0 i
      | succ n =>
        apply Fin.antitone_iff_succ_le.mpr
        intro i
        have h := hv i.val (by omega) j.val j.isLt
        have h0 : i.val < n+1+1 := by omega
        have h1 : i.val+1 < n+1+1 := by omega
        have h2 : i.val+2 < n+1+1 := by omega
        simp only [get, dif_pos (And.intro h0 j.isLt), dif_pos (And.intro h1 j.isLt),
          dif_pos (And.intro h2 j.isLt), vertical_iff] at h
        convert h using 2 <;> congr 1
  · rintro ⟨hh,hv⟩
    constructor
    · intro i hi j hj
      have h := hh ⟨i,hi⟩
      simp only [horizontal, decide_eq_true_eq] at h
      simpa only [get_read x hi] using h ⟨j,hj⟩
    · intro i hi j hj
      have h0 : i < n+1 := by omega
      have h1 : i+1 < n+1 := by omega
      have h2 : i+2 < n+1 := by omega
      simp only [get, dif_pos (And.intro h0 hj), dif_pos (And.intro h1 hj),
        dif_pos (And.intro h2 hj), vertical_iff]
      exact hv ⟨j,hj⟩ (show (⟨i,by omega⟩ : Fin n) ≤ ⟨i+1,by omega⟩ from by simp)


private def pack {n : ℕ} (x : {x : Fin (n+1) → Row // avoids x = true}) :
    Code × Chain bits n := by
  have hh := ((avoids_iff x.val).mp x.property).1
  have hv := ((avoids_iff x.val).mp x.property).2
  refine ⟨encode (x.val 0), ⟨fun k => encode (x.val k.succ), ?_⟩⟩
  intro i k hik j
  change bits (encode _) j ≤ bits (encode _) j
  rw [bits_encode _ (hh _) j, bits_encode _ (hh _) j]
  exact hv j hik

private def unpack {n : ℕ} (p : Code × Chain bits n) :
    {x : Fin (n+1) → Row // avoids x = true} := by
  refine ⟨Fin.cons (bits p.1) (fun k => bits (p.2.val k)), (avoids_iff _).mpr ⟨?_, ?_⟩⟩
  · intro i
    refine Fin.cases ?_ (fun k => ?_) i <;> simpa using horiz_bits _
  · intro j i k hik
    exact p.2.property hik j

private def arrayEquiv (n : ℕ) : {x : Fin (n+1) → Row // avoids x = true} ≃
    Code × Chain bits n where
  toFun := pack
  invFun := unpack
  left_inv x := by
    apply Subtype.ext
    funext i j
    have hh := ((avoids_iff _).mp x.property).1
    refine Fin.cases ?_ (fun k => ?_) i
    · simpa [unpack, pack] using bits_encode _ (hh 0) j
    · simpa [unpack, pack] using bits_encode _ (hh k.succ) j
  right_inv p := by
    rcases p with ⟨c,g⟩
    apply Prod.ext
    · exact encode_bits c
    · apply Subtype.ext
      funext i
      exact encode_bits (g.val i)

private theorem count_by_chains (n : ℕ) : a (n+1) = ((35 * Nat.card (Chain bits n) : ℕ) : ℤ) := by
  classical
  unfold a
  congr 1
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card, Nat.card_congr (arrayEquiv n)]
  simp [Code]

theorem count_one : a 1 = 35 := by
  rw [count_by_chains 0, chain_zero]
  norm_num

private def b0 (c : Code) : ℕ := (#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1] : Array ℕ)[c.val]!

private def b1 (c : Code) : ℕ := (#[0, 1, 2, 1, 2, 5, 1, 1, 3, 2, 4, 3, 5, 13, 1, 1, 3, 1, 2, 2, 3, 8, 2, 4, 2, 4, 10, 3, 3, 9, 5, 10, 8, 13, 34] : Array ℕ)[c.val]!

private def b2 (c : Code) : ℕ := (#[0, 0, 1, 0, 1, 6, 0, 0, 2, 1, 5, 2, 6, 30, 0, 0, 2, 0, 1, 1, 2, 13, 1, 5, 1, 5, 23, 2, 2, 16, 6, 23, 13, 30, 137] : Array ℕ)[c.val]!

private def b3 (c : Code) : ℕ := (#[0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 2, 0, 2, 24, 0, 0, 0, 0, 0, 0, 0, 6, 0, 2, 0, 2, 20, 0, 0, 8, 2, 20, 6, 24, 200] : Array ℕ)[c.val]!

private def b4 (c : Code) : ℕ := (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 6, 0, 0, 0, 0, 6, 0, 6, 120] : Array ℕ)[c.val]!

private def b5 (c : Code) : ℕ := (#[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 24] : Array ℕ)[c.val]!

private theorem b_zero : (fun _ : Code => (1 : ℕ)) = b0 := by
  funext p; exact (by decide +kernel : ∀ p, 1 = b0 p) p

set_option maxRecDepth 15000 in
private theorem step_b0 : step bits b0 = b0 + b1 := by
  funext p; exact (by decide +kernel : ∀ p, step bits b0 p = (b0 + b1) p) p

set_option maxRecDepth 15000 in
private theorem step_b1 : step bits b1 = b1 + b2 := by
  funext p; exact (by decide +kernel : ∀ p, step bits b1 p = (b1 + b2) p) p

set_option maxRecDepth 15000 in
private theorem step_b2 : step bits b2 = b2 + b3 := by
  funext p; exact (by decide +kernel : ∀ p, step bits b2 p = (b2 + b3) p) p

set_option maxRecDepth 15000 in
private theorem step_b3 : step bits b3 = b3 + b4 := by
  funext p; exact (by decide +kernel : ∀ p, step bits b3 p = (b3 + b4) p) p

set_option maxRecDepth 15000 in
private theorem step_b4 : step bits b4 = b4 + b5 := by
  funext p; exact (by decide +kernel : ∀ p, step bits b4 p = (b4 + b5) p) p

set_option maxRecDepth 15000 in
private theorem step_b5 : step bits b5 = b5 := by
  funext p; exact (by decide +kernel : ∀ p, step bits b5 p = (b5) p) p

private theorem tails (n : ℕ) : (fun p => Nat.card (Tail bits p n)) = n.choose 0 • b0 + n.choose 1 • b1 + n.choose 2 • b2 + n.choose 3 • b3 + n.choose 4 • b4 + n.choose 5 • b5 := by
  induction n with
  | zero =>
    simpa only [Nat.choose_zero_right, Nat.choose_zero_succ, zero_smul, one_smul, add_zero,
      tail_zero] using b_zero
  | succ n ih =>
    rw [tail_succ, ih]
    simp only [map_add, map_smul, step_b0, step_b1, step_b2, step_b3, step_b4, step_b5]
    funext p
    simp only [Pi.add_apply, scaled, Nat.choose_succ_succ, Nat.choose_zero_right]
    ring

private theorem total_b0 : ∑ p, b0 p = 35 := by decide +kernel

private theorem total_b1 : ∑ p, b1 p = 171 := by decide +kernel

private theorem total_b2 : ∑ p, b2 p = 337 := by decide +kernel

private theorem total_b3 : ∑ p, b3 p = 320 := by decide +kernel

private theorem total_b4 : ∑ p, b4 p = 144 := by decide +kernel

private theorem total_b5 : ∑ p, b5 p = 24 := by decide +kernel

theorem count_tail (n : ℕ) : a (n+2) = (35 * (35 * n.choose 0 + 171 * n.choose 1 + 337 * n.choose 2 + 320 * n.choose 3 + 144 * n.choose 4 + 24 * n.choose 5) : ℕ) := by
  have h := congrArg (fun v : Code → ℕ => ∑ p, v p) (tails n)
  simp only [Pi.add_apply, scaled, Finset.sum_add_distrib,
    ← Finset.mul_sum, total_b0, total_b1, total_b2, total_b3, total_b4, total_b5] at h
  rw [count_by_chains (n+1), chain_card_succ, h]
  push_cast
  ring

end OMA.S_oeis_a209649

namespace OMA.S_oeis_a209649

open PowerSeries

/-- Falling factorial basis for the binomial expansion of the count. -/
private def falling (x : ℚ) : ℕ → ℚ
  | 0 => 1
  | k + 1 => falling x k * (x - k)

private theorem cast_choose_falling (n k : ℕ) :
    (n.choose k : ℚ) = falling n k / k.factorial := by
  rw [Nat.cast_choose_eq_descPochhammer_div ℚ]
  congr 1
  induction k with
  | zero => simp [falling]
  | succ k ih => rw [descPochhammer_succ_eval, ih, falling]

private def countPoly (x : ℚ) : ℚ := (-7*x - 315*x^2 + 70*x^3 + 420*x^4 + 42*x^5) / 6

private theorem poly_recurrence (n : ℕ) (hn : 7 ≤ n) :
    countPoly n = 6 * countPoly (n - 1 : ℕ) - 15 * countPoly (n - 2 : ℕ) + 20 * countPoly (n - 3 : ℕ) - 15 * countPoly (n - 4 : ℕ) + 6 * countPoly (n - 5 : ℕ) - countPoly (n - 6 : ℕ) := by
  simp only [countPoly, Nat.cast_sub (show 1 ≤ n by omega), Nat.cast_sub (show 2 ≤ n by omega), Nat.cast_sub (show 3 ≤ n by omega), Nat.cast_sub (show 4 ≤ n by omega), Nat.cast_sub (show 5 ≤ n by omega), Nat.cast_sub (show 6 ≤ n by omega), Nat.cast_ofNat]
  ring

theorem formulas_from_counts (a : ℕ → ℤ)
    (h₁ : a 1 = 35)
    (h₂ : ∀ n : ℕ, a (n + 2) = (35 * (35 * n.choose 0 + 171 * n.choose 1 + 337 * n.choose 2 + 320 * n.choose 3 + 144 * n.choose 4 + 24 * n.choose 5) : ℕ)) :
    (PowerSeries.mk (fun n => if n < 1 then 0 else (a n : ℚ)) * ((1 - X) ^ 6 : PowerSeries ℚ) = 35 * X * (1 + X) * (1 + 28 * X - 17 * X ^ 2)) ∧
    (∀ n : ℕ, 7 ≤ n → (a n : ℚ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) := by
  have ha (n : ℕ) (hn : 0 < n) : (a n : ℚ) = countPoly n := by
    cases n with
    | zero => omega
    | succ n =>
      cases n with
      | zero => rw [h₁]; norm_num [countPoly]
      | succ n =>
        rw [h₂ n]
        push_cast
        simp only [cast_choose_falling]
        norm_num [countPoly, falling, Nat.factorial]
        ring
  constructor
  · let F : PowerSeries ℚ := PowerSeries.mk fun n => if n < 1 then 0 else (a n : ℚ)
    change F * _ = _
    have lhs : F * (1-X)^6 = F - 6 • (F * X^1) + 15 • (F * X^2) - 20 • (F * X^3) + 15 • (F * X^4) - 6 • (F * X^5) + (F * X^6) := by
      simp only [nsmul_eq_mul]; ring
    have rhs : (35 * X * (1 + X) * (1 + 28 * X - 17 * X ^ 2) : PowerSeries ℚ) = 35 • X^1 + 1015 • X^2 + 385 • X^3 - 595 • X^4 := by
      simp only [nsmul_eq_mul]; ring
    have hv (n : ℕ) : (if n < 1 then 0 else (a n : ℚ)) =
        if n < 1 then 0 else countPoly n := by
      split <;> rename_i h
      · rfl
      · simpa [h] using ha n (by omega)
    rw [lhs, rhs]
    ext n
    simp only [map_add, map_sub, map_nsmul, coeff_mul_X_pow', coeff_X_pow,
      F, coeff_mk, hv]
    by_cases hn : 7 ≤ n
    · simp only [if_pos (show 1 ≤ n by omega), if_pos (show 2 ≤ n by omega), if_pos (show 3 ≤ n by omega), if_pos (show 4 ≤ n by omega), if_pos (show 5 ≤ n by omega), if_pos (show 6 ≤ n by omega),
        if_neg (show ¬ n < 1 by omega), if_neg (show ¬ n - 1 < 1 by omega), if_neg (show ¬ n - 2 < 1 by omega), if_neg (show ¬ n - 3 < 1 by omega), if_neg (show ¬ n - 4 < 1 by omega), if_neg (show ¬ n - 5 < 1 by omega), if_neg (show ¬ n - 6 < 1 by omega),
        if_neg (show n ≠ 1 by omega), if_neg (show n ≠ 2 by omega), if_neg (show n ≠ 3 by omega), if_neg (show n ≠ 4 by omega), nsmul_eq_mul]
      norm_num only [Nat.cast_ofNat, mul_zero, add_zero, sub_zero]
      linear_combination poly_recurrence n hn
    · interval_cases n <;> norm_num [countPoly]
  · intro n hn
    rw [ha n (by omega), ha (n - 1) (by omega), ha (n - 2) (by omega), ha (n - 3) (by omega), ha (n - 4) (by omega), ha (n - 5) (by omega), ha (n - 6) (by omega)]
    exact poly_recurrence n hn

end OMA.S_oeis_a209649

open OMA.S_oeis_a209649 in
theorem OMA.solution : type_of% @OMA.S_oeis_a209649.main :=
  formulas_from_counts a count_one count_tail
