import OMAStatements.S_oeis_a056921
import Mathlib
-- Credit: @mrsirrisrm

/-!
# Reduction of OEIS A056921 (Oliveri's conjecture): the even case is settled

Target: for `n ≥ 2`, `n ∣ a (n - 1)` iff `n = 5`.

Proved here unconditionally:
* For every odd modulus `m`: `a (n + 4 m) ≡ -a n (mod m)`, so `a` mod `m` has period `8 m`.
  Write `a (2k+1) = f (k+3)` and `a (2k) = f (k+3) - f (k+2)`, where `f 0 = 0`, `f 1 = 1`,
  `f (ν+1) = ν f ν - f (ν-1)` (the Bessel recurrence at 2). With step matrix
  `T x = !![x, -1; 1, 0]` one has `T (-x) = -(T x)ᵀ`. So reversing a product of steps and
  negating the indices transposes it. Over `ZMod m` (m odd), the full-period product
  `G = T (-1) ⋯ T (-(m-1))` is therefore symmetric. Then `P = T 0 * G` has trace 0 and
  determinant 1, and Cayley-Hamilton gives `P * P = -1`.
* `a (4 m - 1) ≡ -1 (mod m)` for odd `m`.
* No even `n ≥ 2` divides `a (n - 1)`.
  - `n ≡ 2 (mod 4)` and `8 ∣ n` follow from the period 32 of `a` mod 8.
  - `n = 4 m` with `m` odd and `m > 1`: `m ∣ a (4 m - 1)` contradicts the previous item.

Left open: `H1` (odd primes) and `H2` (odd composites).
Numerics, not used here: no prime `5 < p < 3000` divides `a (p - 1)`.
-/

open Matrix OMA.S_oeis_a056921

namespace OMA.R_oeis_a056921_R1

-- The prime case: no odd prime other than 5 divides a (p - 1).
def H1 : Prop := ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 5 → ¬ p ∣ OMA.S_oeis_a056921.a (p - 1)

-- The odd composite case: no odd composite n divides a (n - 1).
def H2 : Prop := ∀ n : ℕ, Odd n → 1 < n → ¬ n.Prime → ¬ n ∣ OMA.S_oeis_a056921.a (n - 1)

section Ring
variable {R : Type*} [CommRing R]

lemma T_neg (x : R) : (!![-x, -1; 1, 0] : Matrix (Fin 2) (Fin 2) R) = -(!![x, -1; 1, 0])ᵀ := by
  ext i j; fin_cases i <;> fin_cases j <;> simp

lemma sq_eq_neg_one (M : Matrix (Fin 2) (Fin 2) R) (ht : M.trace = 0) (hd : M.det = 1) :
    M * M = -1 := by
  rw [trace_fin_two] at ht
  rw [det_fin_two] at hd
  ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_two]
  · linear_combination M 0 0 * ht - hd
  · linear_combination M 0 1 * ht
  · linear_combination M 1 0 * ht
  · linear_combination M 1 1 * ht - hd

lemma exists_D (R : Type*) [CommRing R] : ∃ D : R → ℕ → Matrix (Fin 2) (Fin 2) R,
    (∀ x, D x 0 = 1) ∧ ∀ x m, D x (m + 1) = !![x, -1; 1, 0] * D (x - 1) m :=
  ⟨fun x m => Nat.rec (motive := fun _ => R → Matrix (Fin 2) (Fin 2) R) (fun _ => 1)
    (fun _ ih y => !![y, -1; 1, 0] * ih (y - 1)) m x, fun _ => rfl, fun _ _ => rfl⟩

lemma exists_f : ∃ f : ℕ → ℤ, f 0 = 0 ∧ f 1 = 1 ∧ ∀ n, f (n + 2) = (n + 1) * f (n + 1) - f n :=
  ⟨fun n => (Nat.rec (motive := fun _ => ℤ × ℤ) ((0 : ℤ), (1 : ℤ))
    (fun k q => (q.2, ((k : ℤ) + 1) * q.2 - q.1)) n).1, rfl, rfl, fun _ => rfl⟩

/- `D x m = T x * T (x-1) * ... * T (x-m+1)`. -/
variable (D : R → ℕ → Matrix (Fin 2) (Fin 2) R)
  (hD0 : ∀ x, D x 0 = 1) (hDs : ∀ x m, D x (m + 1) = !![x, -1; 1, 0] * D (x - 1) m)
include hD0 hDs

lemma det_D (x : R) (m : ℕ) : (D x m).det = 1 := by
  induction m generalizing x with
  | zero => simp [hD0]
  | succ m ih => rw [hDs, det_mul, ih]; simp [det_fin_two]

lemma D_succ_right (x : R) (m : ℕ) : D x (m + 1) = D x m * !![x - m, -1; 1, 0] := by
  induction m generalizing x with
  | zero => simp [hD0, hDs]
  | succ m ih =>
    rw [hDs, ih (x - 1), hDs x m, mul_assoc]
    congr 3; push_cast; ring

lemma D_add (x : R) (m n : ℕ) : D x (m + n) = D x m * D (x - m) n := by
  induction m generalizing x with
  | zero => simp [hD0]
  | succ m ih =>
    rw [Nat.succ_add, hDs, hDs, ih, mul_assoc,
      show x - 1 - (m : R) = x - ((m + 1 : ℕ) : R) by push_cast; ring]

/-- Reflection: reversing the product and negating the indices gives the transpose. -/
lemma D_neg (y : R) (m : ℕ) : D (-y) m = (-1 : R) ^ m • (D (y + m - 1) m)ᵀ := by
  induction m generalizing y with
  | zero => simp [hD0]
  | succ m ih =>
    rw [hDs, show -y - 1 = -(y + 1) by ring, ih, D_succ_right D hD0 hDs, T_neg, transpose_mul,
      show y + 1 + (m : R) - 1 = y + ((m + 1 : ℕ) : R) - 1 by push_cast; ring,
      show y + ((m + 1 : ℕ) : R) - 1 - (m : R) = y by push_cast; ring]
    rw [Matrix.mul_smul, neg_mul, pow_succ, mul_comm, ← smul_smul, neg_one_smul]
    exact smul_neg _ _

variable (f : ℕ → ℤ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
  (hf2 : ∀ n, f (n + 2) = (n + 1) * f (n + 1) - f n)
include hf0 hf1 hf2

lemma D_col (ν : ℕ) : (D (ν : R) ν) *ᵥ ![1, 0] = ![(f (ν + 1) : R), (f ν : R)] := by
  induction ν with
  | zero => ext i; fin_cases i <;> simp [hD0, hf0, hf1]
  | succ ν ih =>
    rw [hDs, ← mulVec_mulVec, show ((ν + 1 : ℕ) : R) - 1 = ν by push_cast; ring, ih]
    ext i; fin_cases i <;> simp [mulVec, dotProduct, Fin.sum_univ_two, hf2] <;> ring

end Ring

section Mod
variable {p : ℕ} (D : ZMod p → ℕ → Matrix (Fin 2) (Fin 2) (ZMod p))
  (hD0 : ∀ x, D x 0 = 1) (hDs : ∀ x m, D x (m + 1) = !![x, -1; 1, 0] * D (x - 1) m)
include hD0 hDs

lemma cast_pred (hp : 1 ≤ p) : ((p - 1 : ℕ) : ZMod p) = -1 := by
  rw [Nat.cast_sub hp, ZMod.natCast_self, Nat.cast_one, zero_sub]

/-- The key fact: the full-period product is symmetric (for odd `p`). -/
theorem G_symm (hp : Odd p) : (D (-1) (p - 1))ᵀ = D (-1) (p - 1) := by
  have h := D_neg D hD0 hDs (1 : ZMod p) (p - 1)
  rw [cast_pred D hD0 hDs hp.pos, show (1 : ZMod p) + -1 - 1 = -1 by ring,
    (Nat.Odd.sub_odd hp odd_one).neg_one_pow, one_smul] at h
  conv_rhs => rw [h]

/-- One full period of the step matrices squares to `-1`. -/
theorem period_sq (hp : Odd p) :
    (!![0, -1; 1, 0] * D (-1) (p - 1)) * (!![0, -1; 1, 0] * D (-1) (p - 1)) = -1 := by
  have h01 : D (-1) (p - 1) 0 1 = D (-1) (p - 1) 1 0 := by
    have := congrArg (fun M => M 1 0) (G_symm D hD0 hDs hp); simpa using this
  refine sq_eq_neg_one _ ?_ ?_
  · simp only [trace_fin_two, mul_apply, Fin.sum_univ_two]
    simp [h01]
  · rw [det_mul, det_D D hD0 hDs]; simp [det_fin_two]

lemma D_zero_p (hp : Odd p) : D (0 : ZMod p) p = !![0, -1; 1, 0] * D (-1) (p - 1) := by
  cases p with
  | zero => exact absurd hp (by decide)
  | succ k => rw [hDs, zero_sub, Nat.add_sub_cancel]

variable (f : ℕ → ℤ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
  (hf2 : ∀ n, f (n + 2) = (n + 1) * f (n + 1) - f n)
include hf0 hf1 hf2

/-- Antiperiod of `f` modulo any odd `p`. -/
theorem f_antiperiod (hp : Odd p) (ν : ℕ) : (f (ν + 2 * p) : ZMod p) = -(f ν : ZMod p) := by
  have hc := D_col D hD0 hDs f hf0 hf1 hf2 (ν + 2 * p)
  have hx : ((ν + 2 * p : ℕ) : ZMod p) = ν := by push_cast; rw [ZMod.natCast_self]; ring
  rw [hx, D_add D hD0 hDs, sub_self, two_mul, D_add D hD0 hDs, zero_sub, ZMod.natCast_self,
    neg_zero, D_zero_p D hD0 hDs hp, period_sq D hD0 hDs hp, mul_neg, mul_one, neg_mulVec,
    D_col D hD0 hDs f hf0 hf1 hf2] at hc
  have := congrFun hc 1
  rw [two_mul]; simpa using this.symm

end Mod

section Seq
variable (f : ℕ → ℤ) (hf0 : f 0 = 0) (hf1 : f 1 = 1)
  (hf2 : ∀ n, f (n + 2) = (n + 1) * f (n + 1) - f n)

lemma a_even (k : ℕ) : a (2 * k + 2) = (k + 1) * a (2 * k + 1) + a (2 * k) := by
  rw [a, if_pos (by omega), show (2 * k + 2) / 2 = k + 1 by omega]

lemma a_odd (k : ℕ) : a (2 * k + 3) = a (2 * k + 2) + a (2 * k + 1) := by
  rw [a, if_neg (by omega)]

include hf0 hf1 hf2

lemma f_two : f 2 = 1 := by rw [hf2 0]; simp [hf0, hf1]

lemma a_f (k : ℕ) : (a (2 * k) : ℤ) = f (k + 3) - f (k + 2) ∧ (a (2 * k + 1) : ℤ) = f (k + 3) := by
  have h2 := f_two f hf0 hf1 hf2
  induction k with
  | zero =>
    have h3 : f 3 = 1 := by rw [hf2 1, h2, hf1]; norm_num
    simp [a, h2, h3]
  | succ k ih =>
    obtain ⟨h0, h1⟩ := ih
    have e0 : (a (2 * (k + 1)) : ℤ) = f (k + 1 + 3) - f (k + 1 + 2) := by
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, a_even]; push_cast; rw [h0, h1]
      rw [show k + 1 + 3 = (k + 2) + 2 by ring, hf2 (k + 2)]; push_cast; ring_nf
    refine ⟨e0, ?_⟩
    rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring, a_odd]; push_cast
    rw [show 2 * k + 2 = 2 * (k + 1) by ring, e0, h1]
    simp only [show k + 1 + 2 = k + 3 by ring]; ring

/-- **Antiperiod:** for every odd `p`, `a (n + 4p) ≡ -a n (mod p)`; hence period `8p`. -/
theorem a_antiperiod {p : ℕ} (D : ZMod p → ℕ → Matrix (Fin 2) (Fin 2) (ZMod p))
    (hD0 : ∀ x, D x 0 = 1) (hDs : ∀ x m, D x (m + 1) = !![x, -1; 1, 0] * D (x - 1) m)
    (hp : Odd p) (n : ℕ) : (a (n + 4 * p) : ZMod p) = -(a n : ZMod p) := by
  have fa := f_antiperiod D hD0 hDs f hf0 hf1 hf2 hp
  obtain ⟨k, rfl | rfl⟩ := Nat.even_or_odd' n
  · have e1 := (a_f f hf0 hf1 hf2 k).1
    have e2 := (a_f f hf0 hf1 hf2 (k + 2 * p)).1
    rw [show 2 * (k + 2 * p) = 2 * k + 4 * p by ring] at e2
    have h2 := congrArg (Int.cast : ℤ → ZMod p) e2
    have h1 := congrArg (Int.cast : ℤ → ZMod p) e1
    push_cast at h1 h2
    rw [h2, h1, show k + 2 * p + 3 = (k + 3) + 2 * p by ring,
      show k + 2 * p + 2 = (k + 2) + 2 * p by ring, fa, fa]
    ring
  · have e1 := (a_f f hf0 hf1 hf2 k).2
    have e2 := (a_f f hf0 hf1 hf2 (k + 2 * p)).2
    rw [show 2 * (k + 2 * p) + 1 = 2 * k + 1 + 4 * p by ring] at e2
    have h2 := congrArg (Int.cast : ℤ → ZMod p) e2
    have h1 := congrArg (Int.cast : ℤ → ZMod p) e1
    push_cast at h1 h2
    rw [h2, h1, show k + 2 * p + 3 = (k + 3) + 2 * p by ring, fa]

/-- `a (4p - 1) ≡ -1 (mod p)` for odd `p`. -/
theorem a_four_p_sub_one {p : ℕ} (D : ZMod p → ℕ → Matrix (Fin 2) (Fin 2) (ZMod p))
    (hD0 : ∀ x, D x 0 = 1) (hDs : ∀ x m, D x (m + 1) = !![x, -1; 1, 0] * D (x - 1) m)
    (hp : Odd p) : (a (4 * p - 1) : ZMod p) = -1 := by
  have h2 := f_antiperiod D hD0 hDs f hf0 hf1 hf2 hp 2
  have e := (a_f f hf0 hf1 hf2 (2 * p - 1)).2
  obtain ⟨k, rfl⟩ := hp
  rw [show 2 * (2 * (2 * k + 1) - 1) + 1 = 4 * (2 * k + 1) - 1 by omega,
    show 2 * (2 * k + 1) - 1 + 3 = 2 + 2 * (2 * k + 1) by omega] at e
  have := congrArg (Int.cast : ℤ → ZMod (2 * k + 1)) e
  push_cast at this
  rw [this, h2, f_two f hf0 hf1 hf2]; simp

/-- Period 32 of `a` modulo 8, given that 16 steps multiply to the identity mod 8. -/
lemma a_period8 (D : ZMod 8 → ℕ → Matrix (Fin 2) (Fin 2) (ZMod 8))
    (hD0 : ∀ x, D x 0 = 1) (hDs : ∀ x m, D x (m + 1) = !![x, -1; 1, 0] * D (x - 1) m)
    (h16 : D 0 16 = 1) (k : ℕ) : (a (k + 32) : ZMod 8) = a k := by
  have fp : ∀ ν, (f (ν + 16) : ZMod 8) = f ν := by
    intro ν
    have hc := D_col D hD0 hDs f hf0 hf1 hf2 (ν + 16)
    have hx : ((ν + 16 : ℕ) : ZMod 8) = ν := by
      push_cast; rw [show (16 : ZMod 8) = 0 by decide, add_zero]
    rw [D_add D hD0 hDs, hx, sub_self, h16, mul_one, D_col D hD0 hDs f hf0 hf1 hf2] at hc
    have := congrFun hc 1
    simpa using this.symm
  obtain ⟨j, rfl | rfl⟩ := Nat.even_or_odd' k
  · have e1 := (a_f f hf0 hf1 hf2 j).1
    have e2 := (a_f f hf0 hf1 hf2 (j + 16)).1
    rw [show 2 * (j + 16) = 2 * j + 32 by ring] at e2
    have h2 := congrArg (Int.cast : ℤ → ZMod 8) e2
    have h1 := congrArg (Int.cast : ℤ → ZMod 8) e1
    push_cast at h1 h2
    rw [h2, h1, show j + 16 + 3 = (j + 3) + 16 by ring,
      show j + 16 + 2 = (j + 2) + 16 by ring, fp, fp]
  · have e1 := (a_f f hf0 hf1 hf2 j).2
    have e2 := (a_f f hf0 hf1 hf2 (j + 16)).2
    rw [show 2 * (j + 16) + 1 = 2 * j + 1 + 32 by ring] at e2
    have h2 := congrArg (Int.cast : ℤ → ZMod 8) e2
    have h1 := congrArg (Int.cast : ℤ → ZMod 8) e1
    push_cast at h1 h2
    rw [h2, h1, show j + 16 + 3 = (j + 3) + 16 by ring, fp]

end Seq

lemma a_small : ∀ k < 32, (k % 4 = 1 → a k % 2 = 1) ∧ (k % 8 = 7 → a k % 8 ≠ 0) := by
  decide

lemma a_mod8 (k : ℕ) : a k % 8 = a (k % 32) % 8 := by
  obtain ⟨f, hf0, hf1, hf2⟩ := exists_f
  obtain ⟨D, hD0, hDs, h16⟩ : ∃ D : ZMod 8 → ℕ → Matrix (Fin 2) (Fin 2) (ZMod 8),
      (∀ x, D x 0 = 1) ∧ (∀ x m, D x (m + 1) = !![x, -1; 1, 0] * D (x - 1) m) ∧ D 0 16 = 1 :=
    ⟨fun x m => Nat.rec (motive := fun _ => ZMod 8 → Matrix (Fin 2) (Fin 2) (ZMod 8))
      (fun _ => 1) (fun _ ih y => !![y, -1; 1, 0] * ih (y - 1)) m x,
      fun _ => rfl, fun _ _ => rfl, by decide⟩
  have per := a_period8 f hf0 hf1 hf2 D hD0 hDs h16
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    by_cases hk : k < 32
    · rw [Nat.mod_eq_of_lt hk]
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (not_lt.mp hk)
      have := per j
      rw [← ZMod.natCast_mod, ← ZMod.natCast_mod (a j)] at this
      have h := (ZMod.natCast_eq_natCast_iff' _ _ 8).mp this
      rw [Nat.mod_mod, Nat.mod_mod] at h
      rw [add_comm, h, ih j (by omega), Nat.add_mod_right]

/-- **No even `n ≥ 2` divides `a (n - 1)`.** -/
theorem even_not_dvd (n : ℕ) (h2 : 2 ≤ n) (he : Even n) : ¬ n ∣ a (n - 1) := by
  intro hd
  obtain ⟨r, hr⟩ := he
  have hs := a_small ((n - 1) % 32) (Nat.mod_lt _ (by norm_num))
  have hm := a_mod8 (n - 1)
  rcases (by omega : n % 4 = 2 ∨ n % 8 = 0 ∨ n % 8 = 4) with h | h | h
  · have h2d : 2 ∣ a (n - 1) := (Nat.dvd_of_mod_eq_zero (by omega)).trans hd
    have := hs.1 (by omega)
    omega
  · have h8 : 8 ∣ a (n - 1) := (Nat.dvd_of_mod_eq_zero h).trans hd
    have := hs.2 (by omega)
    omega
  · obtain ⟨m, rfl⟩ : 4 ∣ n := Nat.dvd_of_mod_eq_zero (by omega)
    have hmo : Odd m := by
      rcases Nat.even_or_odd m with ⟨s, rfl⟩ | ho
      · omega
      · exact ho
    by_cases hm1 : m = 1
    · subst hm1; revert hd; decide
    · have hmd : m ∣ a (4 * m - 1) := (Dvd.intro_left 4 rfl).trans hd
      obtain ⟨f, hf0, hf1, hf2⟩ := exists_f
      obtain ⟨D, hD0, hDs⟩ := exists_D (ZMod m)
      have h1 := a_four_p_sub_one f hf0 hf1 hf2 D hD0 hDs hmo
      rw [(ZMod.natCast_eq_zero_iff _ _).mpr hmd] at h1
      have h10 : (1 : ZMod m) = 0 := by linear_combination h1
      have hm2 : 1 < m := by rcases hmo with ⟨s, rfl⟩; omega
      have : Fact (1 < m) := ⟨hm2⟩
      exact one_ne_zero h10

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a056921.main := by
  intro h1 h2 n hn
  constructor
  · intro hd
    rcases Nat.even_or_odd n with he | ho
    · exact absurd hd (even_not_dvd n hn he)
    · by_contra h5
      by_cases hp : n.Prime
      · exact h1 n hp (by rintro rfl; exact absurd ho (by decide)) h5 hd
      · exact h2 n ho (by omega) hp hd
  · rintro rfl; decide

end OMA.R_oeis_a056921_R1
