import OMAStatements.S_oeis_a389524
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

-- Problem: A389524: Three identities for the triangle A389524.
-- Upstream: formal-conjectures statements/oeis-a389524.lean:0 (declaration OMA.S_oeis_a389524.main)
-- Credit: Daniel Whorlow (@draonbioetl)
-- Proof via a unified dual-number q-series functional equation over PowerSeries ℤ:
-- both g_m(v) = sum_{k>=1} (v q^m)^k G_k(q) and R_m(v) = sum_{k>=1} (v q^{m+1})^k (q;q)_{k-1}/(v q^{m+1};q)_k
-- satisfy (1 - v q^{m+1}) F_m + v q^{m+1} F_{m+1} = v q^{m+1} / (1 - v q^{m+1}) at v = 1 + eps (eps^2 = 0).
-- Component 1 yields Identity 1 (and Identity 3 by telescoping); component 2 yields Identity 2 via
-- the bijection (a, b, c, d) <-> (k, j, r, s) = (b, b - d, a - c, c).

namespace OMA_A389524

open OMA.S_oeis_a389524 Finset PowerSeries

/-! ### Part 1: Recurrence for `triangle` and reduction of Identity 3 to Identity 1 -/

private lemma triangle_zero_right (n : ℕ) : triangle n 0 = 0 := by
  rw [triangle]; simp

private lemma triangle_one_right (n : ℕ) : triangle n 1 = if n = 1 then 1 else 0 := by
  rw [triangle]; simp

private lemma triangle_eq_zero_of_lt {n k : ℕ} (h : n < k) : triangle n k = 0 := by
  rw [triangle]
  split_ifs <;> omega

private lemma triangle_zero_left (k : ℕ) : triangle 0 k = 0 := by
  cases k with
  | zero => exact triangle_zero_right 0
  | succ k => exact triangle_eq_zero_of_lt (Nat.succ_pos k)

private def colSum (n k : ℕ) : ℤ :=
  ∑ j ∈ range n, triangle (j + 1) k

private lemma colSum_succ (n k : ℕ) :
    colSum (n + 1) k = colSum n k + triangle (n + 1) k := by
  unfold colSum
  rw [sum_range_succ]

private lemma colSum_eq_of_ge {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    colSum n k = 1 + ∑ i ∈ range (k - 1), triangle (n - (i + 1)) (k - 1) := by
  have hn1 : n = (n - 1) + 1 := by omega
  have htri : triangle n k =
      1 + (∑ i : Fin (k - 1), triangle (n - (i.val + 1)) (k - 1)) -
      (∑ i : Fin (n - 1), triangle (i.val + 1) k) := by
    conv_lhs => rw [triangle]
    simp only [show k ≠ 0 by omega, show k ≠ 1 by omega, hkn, ↓reduceIte]
  have hcol : colSum n k = colSum (n - 1) k + triangle n k := by
    conv_lhs => rw [hn1, colSum_succ]
    rw [← hn1]
  have hsum1 : (∑ i : Fin (k - 1), triangle (n - (i.val + 1)) (k - 1)) =
      ∑ i ∈ range (k - 1), triangle (n - (i + 1)) (k - 1) :=
    Fin.sum_univ_eq_sum_range (fun i => triangle (n - (i + 1)) (k - 1)) (k - 1)
  have hsum2 : (∑ i : Fin (n - 1), triangle (i.val + 1) k) = colSum (n - 1) k :=
    Fin.sum_univ_eq_sum_range (fun i => triangle (i + 1) k) (n - 1)
  rw [hcol, htri, hsum1, hsum2]
  ring

private lemma colSum_eq_zero_of_lt {n k : ℕ} (h : n < k) : colSum n k = 0 := by
  unfold colSum
  refine Finset.sum_eq_zero fun j hj => ?_
  have hjlt : j < n := mem_range.mp hj
  exact triangle_eq_zero_of_lt (by omega)

private lemma triangle_diag (k : ℕ) (hk : 1 ≤ k) : triangle k k = k := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      rw [triangle_one_right]; simp
    | succ k =>
      have hge2 : 2 ≤ k + 2 := by omega
      have hcol := colSum_eq_of_ge hge2 (le_refl (k + 2))
      have hcol_prev : colSum (k + 1) (k + 2) = 0 := colSum_eq_zero_of_lt (by omega)
      have htri : triangle (k + 2) (k + 2) = colSum (k + 2) (k + 2) - colSum (k + 1) (k + 2) := by
        rw [colSum_succ]; ring
      rw [htri, hcol, hcol_prev, sub_zero]
      have hsum : ∑ i ∈ range (k + 2 - 1), triangle (k + 2 - (i + 1)) (k + 2 - 1) =
          triangle (k + 1) (k + 1) := by
        rw [Finset.sum_eq_single 0]
        · simp
        · intro i _ hi0
          exact triangle_eq_zero_of_lt (by omega)
        · intro h0
          have : 0 ∈ range (k + 2 - 1) := mem_range.mpr (by omega)
          exact absurd this h0
      rw [hsum, ih (by omega)]
      push_cast
      ring

private lemma triangle_rec_gt {n k : ℕ} (hk : 2 ≤ k) (hkn : k < n) :
    triangle n k = triangle (n - 1) (k - 1) - triangle (n - k) (k - 1) := by
  have hn1 : n = (n - 1) + 1 := by omega
  have hdiff : triangle n k = colSum n k - colSum (n - 1) k := by
    conv_rhs => rw [hn1, colSum_succ]
    rw [← hn1]; ring
  rw [hdiff, colSum_eq_of_ge hk (by omega), colSum_eq_of_ge hk (by omega)]
  set m := k - 1
  have hm1 : 1 ≤ m := by omega
  have hrm : range m = range ((m - 1) + 1) := by congr 1; omega
  have h1 : ∑ i ∈ range m, triangle (n - (i + 1)) m =
      triangle (n - 1) m + ∑ i ∈ range (m - 1), triangle (n - (i + 2)) m := by
    rw [hrm, sum_range_succ', zero_add, add_comm]
  have h2 : ∑ i ∈ range m, triangle (n - 1 - (i + 1)) m =
      (∑ i ∈ range (m - 1), triangle (n - (i + 2)) m) + triangle (n - k) m := by
    rw [hrm, sum_range_succ]
    congr 1
    · refine sum_congr rfl fun i _ => ?_
      congr 1; omega
    · congr 1; omega
  rw [h1, h2]
  ring

private lemma triangle_rec (n k : ℕ) (hk : 2 ≤ k) :
    triangle n k = (if n = k then 1 else 0) + triangle (n - 1) (k - 1) - triangle (n - k) (k - 1) := by
  by_cases hlt : n < k
  · have h1 : triangle n k = 0 := triangle_eq_zero_of_lt hlt
    have h2 : triangle (n - 1) (k - 1) = 0 := triangle_eq_zero_of_lt (by omega)
    have h3 : triangle (n - k) (k - 1) = 0 := by
      have : n - k = 0 := by omega
      rw [this]; exact triangle_zero_left _
    simp [h1, h2, h3, show n ≠ k by omega]
  · by_cases heq : n = k
    · subst heq
      have h1 : triangle n n = n := triangle_diag n (by omega)
      have h2 : triangle (n - 1) (n - 1) = (n - 1 : ℕ) := triangle_diag (n - 1) (by omega)
      have h3 : triangle (n - n) (n - 1) = 0 := by rw [Nat.sub_self]; exact triangle_zero_left _
      simp only [↓reduceIte, h1, h2, h3, sub_zero]
      have : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
      linarith
    · simp only [heq, ↓reduceIte, zero_add]
      exact triangle_rec_gt hk (by omega)

/-- Telescoping formula: for `m ≥ 1` and `k ≥ 1`,
`triangle (m + k) k = - ∑ j ∈ range (k - 1), triangle m (j + 1)`. -/
private lemma triangle_shift_eq_neg_sum (m : ℕ) (hm : 1 ≤ m) :
    ∀ k : ℕ, 1 ≤ k →
      triangle (m + k) k = - ∑ j ∈ range (k - 1), triangle m (j + 1) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      simp [triangle_one_right]; omega
    | succ k =>
      have hrec := triangle_rec_gt (n := m + (k + 2)) (k := k + 2) (by omega) (by omega)
      have hsub1 : m + (k + 2) - 1 = m + (k + 1) := by omega
      have hsub2 : m + (k + 2) - (k + 2) = m := by omega
      have hsub3 : k + 2 - 1 = k + 1 := by omega
      rw [hsub1, hsub2, hsub3] at hrec
      rw [hrec, ih (by omega), show k + 2 - 1 = (k + 1 - 1) + 1 by omega, sum_range_succ]
      have hidx : k + 1 - 1 + 1 = k + 1 := by omega
      rw [hidx]
      ring

private lemma identity3_of_identity1 (n : ℕ) (hn : 0 < n)
    (h1 : (∑ i ∈ range n, triangle n (i + 1)) = (n.divisors.card : ℤ)) :
    triangle (2 * n) n = (n : ℤ) - (n.divisors.card : ℤ) := by
  have hshift := triangle_shift_eq_neg_sum n (by omega) n (by omega)
  have h2n : 2 * n = n + n := by omega
  have hsplit : ∑ i ∈ range n, triangle n (i + 1) =
      (∑ i ∈ range (n - 1), triangle n (i + 1)) + triangle n n := by
    have hn1 : n = (n - 1) + 1 := by omega
    conv_lhs => rw [hn1, sum_range_succ, ← hn1]
  have hdiag : triangle n n = n := triangle_diag n (by omega)
  rw [h2n, hshift]
  linarith

/-! ### Part 2: Dual numbers `DualPS` over `PowerSeries ℤ` -/

private structure DualPS where
  fst : PowerSeries ℤ
  snd : PowerSeries ℤ

private lemma DualPS.ext {x y : DualPS} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y := by
  cases x; cases y; congr

private noncomputable instance : Zero DualPS := ⟨⟨0, 0⟩⟩
private noncomputable instance : One DualPS := ⟨⟨1, 0⟩⟩
private noncomputable instance : Add DualPS := ⟨fun x y => ⟨x.fst + y.fst, x.snd + y.snd⟩⟩
private noncomputable instance : Neg DualPS := ⟨fun x => ⟨-x.fst, -x.snd⟩⟩
private noncomputable instance : Sub DualPS := ⟨fun x y => ⟨x.fst - y.fst, x.snd - y.snd⟩⟩
private noncomputable instance : Mul DualPS := ⟨fun x y => ⟨x.fst * y.fst, x.fst * y.snd + x.snd * y.fst⟩⟩
private noncomputable instance : NatCast DualPS := ⟨fun n => ⟨n, 0⟩⟩
private noncomputable instance : IntCast DualPS := ⟨fun n => ⟨n, 0⟩⟩

private noncomputable instance : CommRing DualPS where
  add_assoc a b c := DualPS.ext (add_assoc _ _ _) (add_assoc _ _ _)
  zero_add a := DualPS.ext (zero_add _) (zero_add _)
  add_zero a := DualPS.ext (add_zero _) (add_zero _)
  add_comm a b := DualPS.ext (add_comm _ _) (add_comm _ _)
  nsmul := nsmulRec
  zsmul := zsmulRec
  neg_add_cancel a := DualPS.ext (neg_add_cancel _) (neg_add_cancel _)
  sub_eq_add_neg a b := DualPS.ext (sub_eq_add_neg _ _) (sub_eq_add_neg _ _)
  mul_assoc a b c := DualPS.ext (by change (a.fst * b.fst) * c.fst = a.fst * (b.fst * c.fst); ring)
    (by change (a.fst * b.fst) * c.snd + (a.fst * b.snd + a.snd * b.fst) * c.fst =
          a.fst * (b.fst * c.snd + b.snd * c.fst) + a.snd * (b.fst * c.fst); ring)
  one_mul a := DualPS.ext (by change 1 * a.fst = a.fst; ring)
    (by change 1 * a.snd + 0 * a.fst = a.snd; ring)
  mul_one a := DualPS.ext (by change a.fst * 1 = a.fst; ring)
    (by change a.fst * 0 + a.snd * 1 = a.snd; ring)
  left_distrib a b c := DualPS.ext (by change a.fst * (b.fst + c.fst) = a.fst * b.fst + a.fst * c.fst; ring)
    (by change a.fst * (b.snd + c.snd) + a.snd * (b.fst + c.fst) =
          (a.fst * b.snd + a.snd * b.fst) + (a.fst * c.snd + a.snd * c.fst); ring)
  right_distrib a b c := DualPS.ext (by change (a.fst + b.fst) * c.fst = a.fst * c.fst + b.fst * c.fst; ring)
    (by change (a.fst + b.fst) * c.snd + (a.snd + b.snd) * c.fst =
          (a.fst * c.snd + a.snd * c.fst) + (b.fst * c.snd + b.snd * c.fst); ring)
  zero_mul a := DualPS.ext (by change 0 * a.fst = 0; ring)
    (by change 0 * a.snd + 0 * a.fst = 0; ring)
  mul_zero a := DualPS.ext (by change a.fst * 0 = 0; ring)
    (by change a.fst * 0 + a.snd * 0 = 0; ring)
  mul_comm a b := DualPS.ext (by change a.fst * b.fst = b.fst * a.fst; ring)
    (by change a.fst * b.snd + a.snd * b.fst = b.fst * a.snd + b.snd * a.fst; ring)
  natCast_zero := DualPS.ext Nat.cast_zero rfl
  natCast_succ n := DualPS.ext (Nat.cast_succ n) (by change (0 : PowerSeries ℤ) = 0 + 0; simp)
  intCast_ofNat n := DualPS.ext (Int.cast_natCast n) rfl
  intCast_negSucc n := DualPS.ext (Int.cast_negSucc n) (by change (0 : PowerSeries ℤ) = -(0 : PowerSeries ℤ); simp)

private lemma DualPS.fst_zero : (0 : DualPS).fst = 0 := rfl
private lemma DualPS.snd_zero : (0 : DualPS).snd = 0 := rfl
private lemma DualPS.fst_one : (1 : DualPS).fst = 1 := rfl
private lemma DualPS.snd_one : (1 : DualPS).snd = 0 := rfl
private lemma DualPS.fst_add (x y : DualPS) : (x + y).fst = x.fst + y.fst := rfl
private lemma DualPS.snd_add (x y : DualPS) : (x + y).snd = x.snd + y.snd := rfl
private lemma DualPS.fst_sub (x y : DualPS) : (x - y).fst = x.fst - y.fst := rfl
private lemma DualPS.snd_sub (x y : DualPS) : (x - y).snd = x.snd - y.snd := rfl
private lemma DualPS.fst_neg (x : DualPS) : (-x).fst = -x.fst := rfl
private lemma DualPS.snd_neg (x : DualPS) : (-x).snd = -x.snd := rfl
private lemma DualPS.fst_mul (x y : DualPS) : (x * y).fst = x.fst * y.fst := rfl
private lemma DualPS.snd_mul (x y : DualPS) : (x * y).snd = x.fst * y.snd + x.snd * y.fst := rfl

private lemma DualPS.fst_sum {ι : Type*} (s : Finset ι) (f : ι → DualPS) :
    (∑ i ∈ s, f i).fst = ∑ i ∈ s, (f i).fst := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, DualPS.fst_add, ih]

private lemma DualPS.snd_sum {ι : Type*} (s : Finset ι) (f : ι → DualPS) :
    (∑ i ∈ s, f i).snd = ∑ i ∈ s, (f i).snd := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, DualPS.snd_add, ih]

private noncomputable def qD : DualPS := ⟨X, 0⟩
private noncomputable def vD : DualPS := ⟨1, 1⟩

private lemma qD_pow (k : ℕ) : qD ^ k = ⟨X ^ k, 0⟩ := by
  induction k with
  | zero => exact DualPS.ext (by simp [DualPS.fst_one]) rfl
  | succ k ih =>
    rw [pow_succ, ih]
    exact DualPS.ext (by simp [DualPS.fst_mul, qD, pow_succ])
      (by simp [DualPS.snd_mul, qD])

private lemma vD_pow (k : ℕ) : vD ^ k = ⟨1, (k : PowerSeries ℤ)⟩ := by
  induction k with
  | zero => exact DualPS.ext rfl (by simp [DualPS.snd_one])
  | succ k ih =>
    rw [pow_succ, ih]
    exact DualPS.ext (by simp [DualPS.fst_mul, vD])
      (by simp [DualPS.snd_mul, vD, add_comm])

private noncomputable def geomPS (j : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk (fun n => if j ∣ n then 1 else 0)

private lemma coeff_geomPS (j n : ℕ) :
    PowerSeries.coeff n (geomPS j) = if j ∣ n then 1 else 0 := by
  simp [geomPS]

private lemma one_sub_X_pow_mul_geomPS (j : ℕ) (hj : 1 ≤ j) :
    (1 - (X : PowerSeries ℤ) ^ j) * geomPS j = 1 := by
  rw [sub_mul, one_mul]
  ext n
  rw [map_sub, PowerSeries.coeff_X_pow_mul', coeff_geomPS, PowerSeries.coeff_one]
  by_cases hle : j ≤ n
  · simp only [hle, ↓reduceIte, coeff_geomPS]
    have hiff : j ∣ n - j ↔ j ∣ n := by
      constructor
      · rintro ⟨t, ht⟩; exact ⟨t + 1, by rw [mul_add, mul_one]; omega⟩
      · rintro ⟨t, ht⟩; exact ⟨t - 1, by rw [Nat.mul_sub, mul_one]; omega⟩
    have hn0 : n ≠ 0 := by omega
    simp [hiff, hn0]
  · simp only [hle, ↓reduceIte, sub_zero]
    by_cases hn0 : n = 0
    · subst hn0; simp
    · have hndvd : ¬ j ∣ n := fun hd => hle (Nat.le_of_dvd (by omega) hd)
      simp [hn0, hndvd]

private noncomputable def invVQ (j : ℕ) : DualPS :=
  ⟨geomPS j, X ^ j * (geomPS j) ^ 2⟩

private lemma one_sub_vD_mul_qD_pow_mul_invVQ (j : ℕ) (hj : 1 ≤ j) :
    (1 - vD * qD ^ j) * invVQ j = 1 := by
  have h1 : (1 - vD * qD ^ j).fst = 1 - X ^ j := by
    simp [DualPS.fst_sub, DualPS.fst_one, DualPS.fst_mul, vD, qD_pow]
  have h2 : (1 - vD * qD ^ j).snd = -X ^ j := by
    simp [DualPS.snd_sub, DualPS.snd_one, DualPS.snd_mul, vD, qD_pow]
  apply DualPS.ext
  · rw [DualPS.fst_mul, h1, invVQ, DualPS.fst_one]
    exact one_sub_X_pow_mul_geomPS j hj
  · rw [DualPS.snd_mul, h1, h2, invVQ, DualPS.snd_one]
    have hmul := one_sub_X_pow_mul_geomPS j hj
    calc
      (1 - X ^ j) * (X ^ j * geomPS j ^ 2) + -X ^ j * geomPS j
          = X ^ j * ((1 - X ^ j) * geomPS j) * geomPS j - X ^ j * geomPS j := by ring
      _ = X ^ j * 1 * geomPS j - X ^ j * geomPS j := by rw [hmul]
      _ = 0 := by ring

/-! ### Part 3: Order-of-vanishing helper and finite truncation identities -/

private def VanishesBelow (d : ℕ) (x : DualPS) : Prop :=
  ∀ r < d, PowerSeries.coeff r x.fst = 0 ∧ PowerSeries.coeff r x.snd = 0

private lemma vanishesBelow_zero_val (d : ℕ) : VanishesBelow d 0 := by
  intro r _
  simp [DualPS.fst_zero, DualPS.snd_zero]

private lemma vanishesBelow_zero (x : DualPS) : VanishesBelow 0 x := by
  intro r hr; omega

private lemma vanishesBelow_add {d : ℕ} {x y : DualPS}
    (hx : VanishesBelow d x) (hy : VanishesBelow d y) : VanishesBelow d (x + y) := by
  intro r hr
  simp [DualPS.fst_add, DualPS.snd_add, (hx r hr).1, (hx r hr).2, (hy r hr).1, (hy r hr).2]

private lemma vanishesBelow_sub {d : ℕ} {x y : DualPS}
    (hx : VanishesBelow d x) (hy : VanishesBelow d y) : VanishesBelow d (x - y) := by
  intro r hr
  simp [DualPS.fst_sub, DualPS.snd_sub, (hx r hr).1, (hx r hr).2, (hy r hr).1, (hy r hr).2]

private lemma vanishesBelow_mul_right {d : ℕ} {x : DualPS} (y : DualPS)
    (hx : VanishesBelow d x) : VanishesBelow d (x * y) := by
  intro r hr
  have hps : ∀ (p q : PowerSeries ℤ), (∀ t ≤ r, PowerSeries.coeff t p = 0) →
      PowerSeries.coeff r (p * q) = 0 := by
    intro p q hp
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun ab hab => ?_
    have ha : ab.1 ≤ r := by
      have := Finset.mem_antidiagonal.mp hab
      omega
    rw [hp ab.1 ha, zero_mul]
  constructor
  · rw [DualPS.fst_mul]
    exact hps x.fst y.fst (fun t ht => (hx t (by omega)).1)
  · rw [DualPS.snd_mul, map_add]
    rw [hps x.fst y.snd (fun t ht => (hx t (by omega)).1),
      hps x.snd y.fst (fun t ht => (hx t (by omega)).2), add_zero]

private lemma vanishesBelow_mul_add {d1 d2 : ℕ} {x y : DualPS}
    (hx : VanishesBelow d1 x) (hy : VanishesBelow d2 y) : VanishesBelow (d1 + d2) (x * y) := by
  intro r hr
  have hps : ∀ (p q : PowerSeries ℤ),
      (∀ t < d1, PowerSeries.coeff t p = 0) →
      (∀ t < d2, PowerSeries.coeff t q = 0) →
      PowerSeries.coeff r (p * q) = 0 := by
    intro p q hp hq
    rw [PowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun ab hab => ?_
    have hsum := Finset.mem_antidiagonal.mp hab
    by_cases h1 : ab.1 < d1
    · rw [hp ab.1 h1, zero_mul]
    · rw [hq ab.2 (by omega), mul_zero]
  constructor
  · rw [DualPS.fst_mul]
    exact hps x.fst y.fst (fun t ht => (hx t ht).1) (fun t ht => (hy t ht).1)
  · rw [DualPS.snd_mul, map_add]
    rw [hps x.fst y.snd (fun t ht => (hx t ht).1) (fun t ht => (hy t ht).2),
      hps x.snd y.fst (fun t ht => (hx t ht).2) (fun t ht => (hy t ht).1), add_zero]

private lemma vanishesBelow_qD_pow (d : ℕ) : VanishesBelow d (qD ^ d) := by
  intro r hr
  rw [qD_pow]
  simp [PowerSeries.coeff_X_pow, show r ≠ d by omega]

private lemma vanishesBelow_mono {d1 d2 : ℕ} {x : DualPS} (h : d1 ≤ d2)
    (hx : VanishesBelow d2 x) : VanishesBelow d1 x :=
  fun r hr => hx r (by omega)

private lemma vanishesBelow_vD_qD_pow (m k : ℕ) :
    VanishesBelow (k * (m + 1)) ((vD * qD ^ (m + 1)) ^ k) := by
  rw [mul_pow, ← pow_mul, mul_comm (vD ^ k)]
  have hrew : (m + 1) * k = k * (m + 1) := mul_comm _ _
  rw [hrew]
  exact vanishesBelow_mul_right (vD ^ k) (vanishesBelow_qD_pow _)

/-- Left family `G k` = generating series of column `k` of `triangle`. -/
private noncomputable def GD (k : ℕ) : DualPS :=
  ⟨PowerSeries.mk (fun n => triangle n k), 0⟩

private lemma GD_one : GD 1 = qD := by
  apply DualPS.ext
  · ext n
    simp [GD, qD, triangle_one_right, PowerSeries.coeff_X]
  · rfl

private lemma GD_rec (k : ℕ) (hk : 1 ≤ k) :
    GD (k + 1) = qD ^ (k + 1) + (qD - qD ^ (k + 1)) * GD k := by
  apply DualPS.ext
  · ext n
    rw [DualPS.fst_add, DualPS.fst_mul, DualPS.fst_sub, qD_pow]
    simp only [GD, qD, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_X_pow]
    rw [sub_mul, map_sub]
    have hX1 : PowerSeries.coeff n (X * PowerSeries.mk (fun m => triangle m k)) =
        if 1 ≤ n then triangle (n - 1) k else 0 := by
      simpa [pow_one, PowerSeries.coeff_mk] using
        PowerSeries.coeff_X_pow_mul' (R := ℤ) (p := PowerSeries.mk (fun m => triangle m k)) (n := 1) (d := n)
    have hXk : PowerSeries.coeff n (X ^ (k + 1) * PowerSeries.mk (fun m => triangle m k)) =
        if k + 1 ≤ n then triangle (n - (k + 1)) k else 0 := by
      simpa [PowerSeries.coeff_mk] using
        PowerSeries.coeff_X_pow_mul' (R := ℤ) (p := PowerSeries.mk (fun m => triangle m k)) (n := k + 1) (d := n)
    rw [hX1, hXk]
    have hrec := triangle_rec n (k + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hrec
    rw [hrec]
    by_cases hn0 : n = 0
    · subst hn0
      simp [triangle_zero_left]
    · have h1le : 1 ≤ n := by omega
      simp only [h1le, ↓reduceIte]
      by_cases hkle : k + 1 ≤ n
      · simp [hkle]; ring
      · have hsub0 : n - (k + 1) = 0 := by omega
        simp [hkle, hsub0, triangle_zero_left]
  · rw [DualPS.snd_add, DualPS.snd_mul, DualPS.snd_sub, qD_pow]
    simp [GD, qD]

private lemma vanishesBelow_GD (k : ℕ) : VanishesBelow k (GD k) := by
  intro r hr
  simp [GD, triangle_eq_zero_of_lt hr]

private noncomputable def gSum (m K : ℕ) : DualPS :=
  ∑ k ∈ range K, (vD * qD ^ m) ^ (k + 1) * GD (k + 1)

private lemma gSum_func_eq (m K : ℕ) :
    (1 - vD * qD ^ (m + 1)) * gSum m (K + 1) + (vD * qD ^ (m + 1)) * gSum (m + 1) K =
      (∑ k ∈ range (K + 1), (vD * qD ^ (m + 1)) ^ (k + 1)) -
        (vD * qD ^ (m + 1)) * ((vD * qD ^ m) ^ (K + 1) * GD (K + 1)) := by
  have hg_split : gSum m (K + 1) = gSum m K + (vD * qD ^ m) ^ (K + 1) * GD (K + 1) := by
    unfold gSum; rw [sum_range_succ]
  have hfirst : gSum m (K + 1) =
      vD * qD ^ (m + 1) + ∑ k ∈ range K, (vD * qD ^ m) ^ (k + 2) * GD (k + 2) := by
    unfold gSum
    rw [sum_range_succ', pow_one, GD_one, add_comm]
    congr 1
    rw [mul_assoc, ← pow_succ]
  have hmain : gSum m (K + 1) - (vD * qD ^ (m + 1)) * gSum m K + (vD * qD ^ (m + 1)) * gSum (m + 1) K =
      ∑ k ∈ range (K + 1), (vD * qD ^ (m + 1)) ^ (k + 1) := by
    rw [hfirst]
    unfold gSum
    rw [Finset.mul_sum, Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib, add_assoc,
      ← Finset.sum_add_distrib]
    conv_rhs => rw [sum_range_succ', pow_one, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hrec := GD_rec (k + 1) (by omega)
    rw [hrec]
    have hpow1 : (vD * qD ^ (m + 1)) * ((vD * qD ^ m) ^ (k + 1) * GD (k + 1)) =
        (vD * qD ^ m) ^ (k + 2) * (qD * GD (k + 1)) := by
      have : (vD * qD ^ (m + 1)) = (vD * qD ^ m) * qD := by rw [pow_succ]; ring
      rw [this, pow_succ]; ring
    have hpow2 : (vD * qD ^ (m + 1)) * ((vD * qD ^ (m + 1)) ^ (k + 1) * GD (k + 1)) =
        (vD * qD ^ m) ^ (k + 2) * (qD ^ (k + 2) * GD (k + 1)) := by
      have : vD * qD ^ (m + 1) = (vD * qD ^ m) * qD := by rw [pow_succ]; ring
      rw [this, mul_pow, pow_succ, pow_succ]; ring
    have hpow3 : (vD * qD ^ m) ^ (k + 2) * qD ^ (k + 2) = (vD * qD ^ (m + 1)) ^ (k + 2) := by
      have : vD * qD ^ (m + 1) = (vD * qD ^ m) * qD := by rw [pow_succ]; ring
      rw [this, mul_pow]; ring
    rw [hpow1, hpow2, ← hpow3]
    ring
  calc
    (1 - vD * qD ^ (m + 1)) * gSum m (K + 1) + (vD * qD ^ (m + 1)) * gSum (m + 1) K
        = gSum m (K + 1) - (vD * qD ^ (m + 1)) * (gSum m K + (vD * qD ^ m) ^ (K + 1) * GD (K + 1)) +
            (vD * qD ^ (m + 1)) * gSum (m + 1) K := by
          conv_lhs => rw [sub_mul, one_mul, hg_split]
          rw [← hg_split]
    _ = (gSum m (K + 1) - (vD * qD ^ (m + 1)) * gSum m K + (vD * qD ^ (m + 1)) * gSum (m + 1) K) -
          (vD * qD ^ (m + 1)) * ((vD * qD ^ m) ^ (K + 1) * GD (K + 1)) := by ring
    _ = (∑ k ∈ range (K + 1), (vD * qD ^ (m + 1)) ^ (k + 1)) -
          (vD * qD ^ (m + 1)) * ((vD * qD ^ m) ^ (K + 1) * GD (K + 1)) := by rw [hmain]

/-- Right family `R m K` using `pochQ` and `invPochVQ`. -/
private noncomputable def pochQ : ℕ → DualPS
  | 0 => 1
  | k + 1 => pochQ k * (1 - qD ^ (k + 1))

private noncomputable def invPochVQ (m : ℕ) : ℕ → DualPS
  | 0 => 1
  | k + 1 => invPochVQ m k * invVQ (m + 1 + k)

private lemma invPochVQ_shift (m k : ℕ) :
    (1 - vD * qD ^ (m + 1)) * invPochVQ m (k + 1) = invPochVQ (m + 1) k := by
  induction k with
  | zero =>
    simp only [invPochVQ, one_mul, add_zero]
    exact one_sub_vD_mul_qD_pow_mul_invVQ (m + 1) (by omega)
  | succ k ih =>
    conv_lhs => rw [invPochVQ]
    rw [← mul_assoc, ih]
    conv_rhs => rw [invPochVQ]
    congr 2; omega

private noncomputable def ED (m k : ℕ) : DualPS :=
  (vD * qD ^ (m + 1)) ^ k * pochQ k * invPochVQ m (k + 1)

private lemma ED_telescope (m k : ℕ) :
    ED m k - ED m (k + 1) =
      (vD * qD ^ (m + 1)) ^ k * pochQ k * invPochVQ (m + 1) (k + 1) := by
  unfold ED
  have hmul : invPochVQ m (k + 1) = (1 - vD * qD ^ (m + 1 + (k + 1))) * invPochVQ m (k + 2) := by
    conv_rhs => rw [invPochVQ]
    rw [mul_left_comm (1 - vD * qD ^ (m + 1 + (k + 1))) (invPochVQ m (k + 1)),
      one_sub_vD_mul_qD_pow_mul_invVQ (m + 1 + (k + 1)) (by omega), mul_one]
  have hcancel : (1 - vD * qD ^ (m + 1 + (k + 1))) - (vD * qD ^ (m + 1)) * (1 - qD ^ (k + 1)) =
      1 - vD * qD ^ (m + 1) := by
    have hpow : qD ^ (m + 1 + (k + 1)) = qD ^ (m + 1) * qD ^ (k + 1) := pow_add _ _ _
    rw [hpow]; ring
  calc
    (vD * qD ^ (m + 1)) ^ k * pochQ k * invPochVQ m (k + 1) -
        (vD * qD ^ (m + 1)) ^ (k + 1) * pochQ (k + 1) * invPochVQ m (k + 2)
        = (vD * qD ^ (m + 1)) ^ k * pochQ k * ((1 - vD * qD ^ (m + 1 + (k + 1))) * invPochVQ m (k + 2)) -
            (vD * qD ^ (m + 1)) ^ k * (vD * qD ^ (m + 1)) * (pochQ k * (1 - qD ^ (k + 1))) * invPochVQ m (k + 2) := by
          conv_lhs => rw [hmul]
          rw [pow_succ (vD * qD ^ (m + 1)) k, pochQ]
    _ = (vD * qD ^ (m + 1)) ^ k * pochQ k *
          (((1 - vD * qD ^ (m + 1 + (k + 1))) - (vD * qD ^ (m + 1)) * (1 - qD ^ (k + 1))) * invPochVQ m (k + 2)) := by
          ring
    _ = (vD * qD ^ (m + 1)) ^ k * pochQ k * ((1 - vD * qD ^ (m + 1)) * invPochVQ m (k + 2)) := by
          rw [hcancel]
    _ = (vD * qD ^ (m + 1)) ^ k * pochQ k * invPochVQ (m + 1) (k + 1) := by
          rw [invPochVQ_shift]

private noncomputable def rSum (m K : ℕ) : DualPS :=
  ∑ k ∈ range K, (vD * qD ^ (m + 1)) ^ (k + 1) * pochQ k * invPochVQ m (k + 1)

private lemma rSum_func_eq (m K : ℕ) :
    (1 - vD * qD ^ (m + 1)) * rSum m (K + 1) + (vD * qD ^ (m + 1)) * rSum (m + 1) K =
      (vD * qD ^ (m + 1)) * invVQ (m + 1) - (vD * qD ^ (m + 1)) ^ 2 * ED m K := by
  set u := vD * qD ^ (m + 1)
  have hr1 : (1 - u) * rSum m (K + 1) =
      u + ∑ k ∈ range K, u ^ (k + 2) * pochQ (k + 1) * invPochVQ (m + 1) (k + 1) := by
    unfold rSum
    rw [sum_range_succ', mul_add, Finset.mul_sum]
    have h0 : (1 - u) * (u ^ 1 * pochQ 0 * invPochVQ m 1) = u := by
      simp only [pow_one, pochQ, mul_one, invPochVQ, one_mul, add_zero]
      rw [mul_left_comm (1 - u) u (invVQ (m + 1))]
      have := one_sub_vD_mul_qD_pow_mul_invVQ (m + 1) (by omega)
      change u * ((1 - u) * invVQ (m + 1)) = u
      rw [this, mul_one]
    rw [add_comm, h0]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    have hsh := invPochVQ_shift m (k + 1)
    calc
      (1 - u) * (u ^ (k + 2) * pochQ (k + 1) * invPochVQ m (k + 2))
          = u ^ (k + 2) * pochQ (k + 1) * ((1 - u) * invPochVQ m (k + 2)) := by ring
      _ = u ^ (k + 2) * pochQ (k + 1) * invPochVQ (m + 1) (k + 1) := by rw [hsh]
  have hr2 : u * rSum (m + 1) K =
      ∑ k ∈ range K, u ^ (k + 2) * qD ^ (k + 1) * pochQ k * invPochVQ (m + 1) (k + 1) := by
    unfold rSum
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    have huq : vD * qD ^ (m + 1 + 1) = u * qD := by
      dsimp [u]; rw [pow_succ]; ring
    rw [huq, mul_pow, pow_succ]
    ring
  rw [hr1, hr2, add_assoc, ← Finset.sum_add_distrib]
  have hterm : ∀ k ∈ range K,
      u ^ (k + 2) * pochQ (k + 1) * invPochVQ (m + 1) (k + 1) +
        u ^ (k + 2) * qD ^ (k + 1) * pochQ k * invPochVQ (m + 1) (k + 1) =
      u ^ 2 * (ED m k - ED m (k + 1)) := by
    intro k _
    rw [ED_telescope m k, pochQ]
    have hpow : u ^ (k + 2) = u ^ 2 * u ^ k := by rw [← pow_add]; congr 1; omega
    rw [hpow]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
  have htele : ∑ k ∈ range K, (ED m k - ED m (k + 1)) = ED m 0 - ED m K := by
    clear hr1 hr2 hterm
    induction K with
    | zero => simp
    | succ K ih =>
      rw [sum_range_succ, ih]; ring
  rw [htele, mul_sub]
  have hE0 : ED m 0 = invVQ (m + 1) := by
    simp [ED, pochQ, invPochVQ]
  have hbase : u + u ^ 2 * invVQ (m + 1) = u * invVQ (m + 1) := by
    have h1 := one_sub_vD_mul_qD_pow_mul_invVQ (m + 1) (by omega)
    change (1 - u) * invVQ (m + 1) = 1 at h1
    calc
      u + u ^ 2 * invVQ (m + 1) = u * (1 + u * invVQ (m + 1)) := by ring
      _ = u * ((1 - u) * invVQ (m + 1) + u * invVQ (m + 1)) := by rw [h1]
      _ = u * invVQ (m + 1) := by ring
  rw [hE0, ← add_sub_assoc, hbase]

/-- Geometric series difference: `(v*q^(m+1)) * invVQ (m+1) - ∑_{k=1}^{K+1} (v*q^(m+1))^k` vanishes below `K + 2`. -/
private lemma geom_diff_vanishes (m K : ℕ) :
    VanishesBelow (K + 2)
      ((vD * qD ^ (m + 1)) * invVQ (m + 1) - ∑ k ∈ range (K + 1), (vD * qD ^ (m + 1)) ^ (k + 1)) := by
  set u := vD * qD ^ (m + 1)
  have hgeom : (1 - u) * (∑ k ∈ range (K + 1), u ^ (k + 1)) = u - u ^ (K + 2) := by
    induction K with
    | zero => simp [pow_two]; ring
    | succ K ih =>
      rw [sum_range_succ, mul_add, ih, pow_succ]
      ring
  have hinv : (1 - u) * invVQ (m + 1) = 1 := one_sub_vD_mul_qD_pow_mul_invVQ (m + 1) (by omega)
  have hEq : u * invVQ (m + 1) - ∑ k ∈ range (K + 1), u ^ (k + 1) = u ^ (K + 2) * invVQ (m + 1) := by
    have h1 : (1 - u) * (u * invVQ (m + 1) - ∑ k ∈ range (K + 1), u ^ (k + 1)) = u ^ (K + 2) := by
      rw [mul_sub, mul_left_comm (1 - u) u (invVQ (m + 1)), hinv, mul_one, hgeom]
      ring
    calc
      u * invVQ (m + 1) - ∑ k ∈ range (K + 1), u ^ (k + 1)
          = ((1 - u) * invVQ (m + 1)) * (u * invVQ (m + 1) - ∑ k ∈ range (K + 1), u ^ (k + 1)) := by
            rw [hinv, one_mul]
      _ = ((1 - u) * (u * invVQ (m + 1) - ∑ k ∈ range (K + 1), u ^ (k + 1))) * invVQ (m + 1) := by
            ring
      _ = u ^ (K + 2) * invVQ (m + 1) := by rw [h1]
  rw [hEq]
  have h1 := vanishesBelow_vD_qD_pow m (K + 2)
  have h2 := vanishesBelow_mono (show K + 2 ≤ (K + 2) * (m + 1) by nlinarith) h1
  exact vanishesBelow_mul_right (invVQ (m + 1)) h2

/-- Stability of `gSum` and `rSum` for `K ≥ d`. -/
private lemma gSum_stable (m d K : ℕ) (hK : d ≤ K) :
    VanishesBelow (d + 1) (gSum m K - gSum m d) := by
  induction K with
  | zero =>
    have hd : d = 0 := by omega
    subst hd; rw [sub_self]; exact vanishesBelow_zero_val _
  | succ K ih =>
    by_cases hEq : d = K + 1
    · subst hEq; rw [sub_self]; exact vanishesBelow_zero_val _
    · have hle : d ≤ K := by omega
      have hsplit : gSum m (K + 1) - gSum m d =
          (gSum m K - gSum m d) + (vD * qD ^ m) ^ (K + 1) * GD (K + 1) := by
        unfold gSum; rw [sum_range_succ]; ring
      rw [hsplit]
      refine vanishesBelow_add (ih hle) ?_
      have hG := vanishesBelow_mono (show d + 1 ≤ K + 1 by omega) (vanishesBelow_GD (K + 1))
      rw [mul_comm]
      exact vanishesBelow_mul_right _ hG

private lemma rSum_stable (m d K : ℕ) (hK : d ≤ K) :
    VanishesBelow (d + 1) (rSum m K - rSum m d) := by
  induction K with
  | zero =>
    have hd : d = 0 := by omega
    subst hd; rw [sub_self]; exact vanishesBelow_zero_val _
  | succ K ih =>
    by_cases hEq : d = K + 1
    · subst hEq; rw [sub_self]; exact vanishesBelow_zero_val _
    · have hle : d ≤ K := by omega
      have hsplit : rSum m (K + 1) - rSum m d =
          (rSum m K - rSum m d) + (vD * qD ^ (m + 1)) ^ (K + 1) * pochQ K * invPochVQ m (K + 1) := by
        unfold rSum; rw [sum_range_succ]; ring
      rw [hsplit]
      refine vanishesBelow_add (ih hle) ?_
      have hu := vanishesBelow_mono (show d + 1 ≤ (K + 1) * (m + 1) by nlinarith)
        (vanishesBelow_vD_qD_pow m (K + 1))
      exact vanishesBelow_mul_right _ (vanishesBelow_mul_right _ hu)

/-- Main uniqueness theorem: `gSum m n` and `rSum m n` agree on all coefficients up to `n`, for every `m`! -/
private lemma gSum_eq_rSum_below :
    ∀ n m : ℕ, VanishesBelow (n + 1) (gSum m n - rSum m n) := by
  intro n
  induction n with
  | zero =>
    intro m
    have h0 : gSum m 0 - rSum m 0 = 0 := by simp [gSum, rSum]
    rw [h0]; exact vanishesBelow_zero_val _
  | succ n ih =>
    intro m
    have hg := gSum_func_eq m (n + 1)
    have hr := rSum_func_eq m (n + 1)
    set u := vD * qD ^ (m + 1)
    have hdiff_eq :
        (1 - u) * (gSum m (n + 2) - rSum m (n + 2)) + u * (gSum (m + 1) (n + 1) - rSum (m + 1) (n + 1)) =
        (u ^ 2 * ED m (n + 1) - (u * invVQ (m + 1) - ∑ k ∈ range (n + 2), u ^ (k + 1))) -
          u * ((vD * qD ^ m) ^ (n + 2) * GD (n + 2)) := by
      calc
        (1 - u) * (gSum m (n + 2) - rSum m (n + 2)) + u * (gSum (m + 1) (n + 1) - rSum (m + 1) (n + 1))
            = ((1 - u) * gSum m (n + 2) + u * gSum (m + 1) (n + 1)) -
                ((1 - u) * rSum m (n + 2) + u * rSum (m + 1) (n + 1)) := by ring
        _ = ((∑ k ∈ range (n + 2), u ^ (k + 1)) - u * ((vD * qD ^ m) ^ (n + 2) * GD (n + 2))) -
              (u * invVQ (m + 1) - u ^ 2 * ED m (n + 1)) := by rw [hg, hr]
        _ = (u ^ 2 * ED m (n + 1) - (u * invVQ (m + 1) - ∑ k ∈ range (n + 2), u ^ (k + 1))) -
              u * ((vD * qD ^ m) ^ (n + 2) * GD (n + 2)) := by ring
    -- Show RHS of `hdiff_eq` vanishes below `n + 2`!
    have hrhs_van : VanishesBelow (n + 2)
        ((1 - u) * (gSum m (n + 2) - rSum m (n + 2)) +
          u * (gSum (m + 1) (n + 1) - rSum (m + 1) (n + 1))) := by
      rw [hdiff_eq]
      refine vanishesBelow_sub (vanishesBelow_sub ?_ ?_) ?_
      · -- `u ^ 2 * ED m (n + 1)` has factor `u ^ (n + 3)`
        have hE : u ^ 2 * ED m (n + 1) = u ^ (n + 3) * (pochQ (n + 1) * invPochVQ m (n + 2)) := by
          unfold ED
          have hpow : u ^ (n + 3) = u ^ 2 * u ^ (n + 1) := by
            rw [show n + 3 = 2 + (n + 1) by omega, pow_add]
          rw [hpow]; dsimp [u]; ring
        rw [hE]
        have hu := vanishesBelow_mono (show n + 2 ≤ (n + 3) * (m + 1) by nlinarith)
          (vanishesBelow_vD_qD_pow m (n + 3))
        exact vanishesBelow_mul_right _ hu
      · exact vanishesBelow_mono (show n + 2 ≤ n + 3 by omega) (geom_diff_vanishes m (n + 1))
      · have hG := vanishesBelow_GD (n + 2)
        have hrew : u * ((vD * qD ^ m) ^ (n + 2) * GD (n + 2)) =
            GD (n + 2) * (u * (vD * qD ^ m) ^ (n + 2)) := by ring
        rw [hrew]
        exact vanishesBelow_mul_right _ hG
    -- By IH + stability, both `gSum m (n + 2) - rSum m (n + 2)` and `gSum (m + 1) (n + 1) - rSum (m + 1) (n + 1)`
    -- vanish below `n + 1`!
    have hvan1 : VanishesBelow (n + 1) (gSum m (n + 2) - rSum m (n + 2)) := by
      have hrew : gSum m (n + 2) - rSum m (n + 2) =
          (gSum m (n + 2) - gSum m n) + ((gSum m n - rSum m n) - (rSum m (n + 2) - rSum m n)) := by ring
      rw [hrew]
      exact vanishesBelow_add (gSum_stable m n (n + 2) (by omega))
        (vanishesBelow_sub (ih m) (rSum_stable m n (n + 2) (by omega)))
    have hvan2 : VanishesBelow (n + 1) (gSum (m + 1) (n + 1) - rSum (m + 1) (n + 1)) := by
      have hrew : gSum (m + 1) (n + 1) - rSum (m + 1) (n + 1) =
          (gSum (m + 1) (n + 1) - gSum (m + 1) n) +
            ((gSum (m + 1) n - rSum (m + 1) n) - (rSum (m + 1) (n + 1) - rSum (m + 1) n)) := by ring
      rw [hrew]
      exact vanishesBelow_add (gSum_stable (m + 1) n (n + 1) (by omega))
        (vanishesBelow_sub (ih (m + 1)) (rSum_stable (m + 1) n (n + 1) (by omega)))
    -- Since `u` vanishes below `1`, `u * (...)` vanishes below `1 + (n + 1) = n + 2`!
    have hu1 : VanishesBelow 1 u := by
      have := vanishesBelow_vD_qD_pow m 1
      rw [pow_one, one_mul] at this
      exact vanishesBelow_mono (by omega) this
    have hu_van1 : VanishesBelow (n + 2) (u * (gSum m (n + 2) - rSum m (n + 2))) :=
      vanishesBelow_mono (by omega) (vanishesBelow_mul_add hu1 hvan1)
    have hu_van2 : VanishesBelow (n + 2) (u * (gSum (m + 1) (n + 1) - rSum (m + 1) (n + 1))) :=
      vanishesBelow_mono (by omega) (vanishesBelow_mul_add hu1 hvan2)
    -- Hence `gSum m (n + 2) - rSum m (n + 2)` vanishes below `n + 2`!
    have hvan_big : VanishesBelow (n + 2) (gSum m (n + 2) - rSum m (n + 2)) := by
      have hrew : gSum m (n + 2) - rSum m (n + 2) =
          ((1 - u) * (gSum m (n + 2) - rSum m (n + 2)) +
            u * (gSum (m + 1) (n + 1) - rSum (m + 1) (n + 1))) +
          (u * (gSum m (n + 2) - rSum m (n + 2)) -
            u * (gSum (m + 1) (n + 1) - rSum (m + 1) (n + 1))) := by ring
      rw [hrew]
      exact vanishesBelow_add hrhs_van (vanishesBelow_sub hu_van1 hu_van2)
    -- Transfer back from `n + 2` to `n + 1` via stability!
    have hback : gSum m (n + 1) - rSum m (n + 1) =
        (gSum m (n + 2) - rSum m (n + 2)) -
          ((gSum m (n + 2) - gSum m (n + 1)) - (rSum m (n + 2) - rSum m (n + 1))) := by ring
    rw [hback]
    exact vanishesBelow_sub hvan_big
      (vanishesBelow_sub (gSum_stable m (n + 1) (n + 2) (by omega))
        (rSum_stable m (n + 1) (n + 2) (by omega)))

/-! ### Part 4: Extract Identities 1, 2, 3 and bijection for `orphans` -/

private lemma poch_invPoch_zero (k : ℕ) :
    pochQ k * invPochVQ 0 k =
      ⟨1, ∑ j ∈ range k, X ^ (j + 1) * geomPS (j + 1)⟩ := by
  induction k with
  | zero =>
    simp only [pochQ, invPochVQ, mul_one, range_zero, sum_empty]
    exact DualPS.ext rfl rfl
  | succ k ih =>
    have hfac : (1 - qD ^ (k + 1)) * invVQ (k + 1) = ⟨1, X ^ (k + 1) * geomPS (k + 1)⟩ := by
      have h1 : (1 - qD ^ (k + 1)).fst = 1 - X ^ (k + 1) := by
        simp [DualPS.fst_sub, DualPS.fst_one, qD_pow]
      have h2 : (1 - qD ^ (k + 1)).snd = 0 := by
        simp [DualPS.snd_sub, DualPS.snd_one, qD_pow]
      apply DualPS.ext
      · rw [DualPS.fst_mul, h1, invVQ]
        exact one_sub_X_pow_mul_geomPS (k + 1) (by omega)
      · rw [DualPS.snd_mul, h1, h2, invVQ, zero_mul, add_zero]
        have hmul := one_sub_X_pow_mul_geomPS (k + 1) (by omega)
        calc
          (1 - X ^ (k + 1)) * (X ^ (k + 1) * geomPS (k + 1) ^ 2)
              = X ^ (k + 1) * ((1 - X ^ (k + 1)) * geomPS (k + 1)) * geomPS (k + 1) := by ring
          _ = X ^ (k + 1) * 1 * geomPS (k + 1) := by rw [hmul]
          _ = X ^ (k + 1) * geomPS (k + 1) := by ring
    have hrew : pochQ (k + 1) * invPochVQ 0 (k + 1) =
        (pochQ k * invPochVQ 0 k) * ((1 - qD ^ (k + 1)) * invVQ (k + 1)) := by
      rw [pochQ, invPochVQ]
      have : 0 + 1 + k = k + 1 := by omega
      rw [this]; ring
    rw [hrew, ih, hfac]
    apply DualPS.ext
    · simp [DualPS.fst_mul]
    · simp only [DualPS.snd_mul, one_mul, mul_one, sum_range_succ, add_comm]

private lemma rSum_zero_components (K : ℕ) :
    (rSum 0 K).fst = ∑ k ∈ range K, X ^ (k + 1) * geomPS (k + 1) ∧
    (rSum 0 K).snd = ∑ k ∈ range K, ∑ j ∈ range (k + 1), (X ^ (k + 1) * geomPS (k + 1)) * geomPS (j + 1) := by
  unfold rSum
  rw [DualPS.fst_sum, DualPS.snd_sum]
  have hterm : ∀ k : ℕ,
      (vD * qD ^ (0 + 1)) ^ (k + 1) * pochQ k * invPochVQ 0 (k + 1) =
      ⟨X ^ (k + 1) * geomPS (k + 1),
        ∑ j ∈ range (k + 1), (X ^ (k + 1) * geomPS (k + 1)) * geomPS (j + 1)⟩ := by
    intro k
    have hrew : (vD * qD ^ (0 + 1)) ^ (k + 1) * pochQ k * invPochVQ 0 (k + 1) =
        ((vD ^ (k + 1) * qD ^ (k + 1)) * invVQ (k + 1)) * (pochQ k * invPochVQ 0 k) := by
      rw [invPochVQ, zero_add, pow_one, mul_pow]
      have : 1 + k = k + 1 := by omega
      rw [this]; ring
    rw [hrew, poch_invPoch_zero k, vD_pow, qD_pow]
    have h1 : ((⟨1, ((k + 1 : ℕ) : PowerSeries ℤ)⟩ : DualPS) * ⟨X ^ (k + 1), 0⟩) =
        ⟨X ^ (k + 1), ((k + 1 : ℕ) : PowerSeries ℤ) * X ^ (k + 1)⟩ := by
      apply DualPS.ext <;> simp [DualPS.fst_mul, DualPS.snd_mul]
    rw [h1]
    have h2 : ((⟨X ^ (k + 1), ((k + 1 : ℕ) : PowerSeries ℤ) * X ^ (k + 1)⟩ : DualPS) * invVQ (k + 1)) =
        ⟨X ^ (k + 1) * geomPS (k + 1),
          X ^ (k + 1) * (X ^ (k + 1) * geomPS (k + 1) ^ 2) +
            ((k + 1 : ℕ) : PowerSeries ℤ) * X ^ (k + 1) * geomPS (k + 1)⟩ := by
      apply DualPS.ext <;> simp [DualPS.fst_mul, DualPS.snd_mul, invVQ]
    rw [h2]
    apply DualPS.ext
    · simp [DualPS.fst_mul]
    · simp only [DualPS.snd_mul, mul_one]
      have hgeom1 : ∀ r : ℕ, 1 ≤ r → 1 + X ^ r * geomPS r = geomPS r := by
        intro r hr
        have hmul := one_sub_X_pow_mul_geomPS r hr
        calc
          1 + X ^ r * geomPS r = (1 - X ^ r) * geomPS r + X ^ r * geomPS r := by rw [hmul]
          _ = geomPS r := by ring
      have hsum_geom : ∑ j ∈ range (k + 1), geomPS (j + 1) =
          ((k + 1 : ℕ) : PowerSeries ℤ) + X ^ (k + 1) * geomPS (k + 1) +
            ∑ j ∈ range k, X ^ (j + 1) * geomPS (j + 1) := by
        have hstep : ∑ j ∈ range (k + 1), geomPS (j + 1) =
            ∑ j ∈ range (k + 1), (1 + X ^ (j + 1) * geomPS (j + 1)) :=
          Finset.sum_congr rfl fun j _ => (hgeom1 (j + 1) (by omega)).symm
        rw [hstep, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          mul_one, sum_range_succ]
        ring
      rw [← Finset.mul_sum, hsum_geom]
      ring
  constructor
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm k]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm k]

private lemma gSum_zero_components (K : ℕ) :
    (gSum 0 K).fst = ∑ k ∈ range K, PowerSeries.mk (fun n => triangle n (k + 1)) ∧
    (gSum 0 K).snd = ∑ k ∈ range K, ((k + 1 : ℕ) : PowerSeries ℤ) * PowerSeries.mk (fun n => triangle n (k + 1)) := by
  unfold gSum
  rw [DualPS.fst_sum, DualPS.snd_sum]
  have hterm : ∀ k : ℕ, (vD * qD ^ 0) ^ (k + 1) * GD (k + 1) =
      ⟨PowerSeries.mk (fun n => triangle n (k + 1)),
        ((k + 1 : ℕ) : PowerSeries ℤ) * PowerSeries.mk (fun n => triangle n (k + 1))⟩ := by
    intro k
    rw [pow_zero, mul_one, vD_pow, GD]
    apply DualPS.ext <;> simp [DualPS.fst_mul, DualPS.snd_mul]
  constructor
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm k]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [hterm k]

private lemma identity1 (n : ℕ) (hn : 0 < n) :
    (∑ i ∈ range n, triangle n (i + 1)) = (n.divisors.card : ℤ) := by
  have hvan := (gSum_eq_rSum_below n 0 n (by omega)).1
  rw [DualPS.fst_sub, map_sub, sub_eq_zero] at hvan
  rw [(gSum_zero_components n).1, (rSum_zero_components n).1, map_sum, map_sum] at hvan
  have hlhs : ∑ k ∈ range n, PowerSeries.coeff n (PowerSeries.mk (fun m => triangle m (k + 1))) =
      ∑ i ∈ range n, triangle n (i + 1) := by
    refine Finset.sum_congr rfl fun k _ => by simp
  have hrhs : ∑ k ∈ range n, PowerSeries.coeff n (X ^ (k + 1) * geomPS (k + 1)) =
      (n.divisors.card : ℤ) := by
    have hterm : ∀ k ∈ range n,
        PowerSeries.coeff n (X ^ (k + 1) * geomPS (k + 1)) = if (k + 1) ∣ n then 1 else 0 := by
      intro k hk
      have hkle : k + 1 ≤ n := by have := mem_range.mp hk; omega
      rw [PowerSeries.coeff_X_pow_mul']
      simp only [hkle, ↓reduceIte, coeff_geomPS]
      have hiff : (k + 1) ∣ n - (k + 1) ↔ (k + 1) ∣ n := by
        constructor
        · rintro ⟨t, ht⟩; exact ⟨t + 1, by rw [mul_add, mul_one]; omega⟩
        · rintro ⟨t, ht⟩; exact ⟨t - 1, by rw [Nat.mul_sub, mul_one]; omega⟩
      simp [hiff]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    congr 1
    refine Finset.card_bij (fun k _ => k + 1) ?_ ?_ ?_
    · intro k hk
      have hk' := mem_filter.mp hk
      exact Nat.mem_divisors.mpr ⟨hk'.2, by omega⟩
    · intro a _ b _ h; omega
    · intro d hd
      have hd' := Nat.mem_divisors.mp hd
      have hdpos : 1 ≤ d := Nat.pos_of_dvd_of_pos hd'.1 hn
      have hdle : d ≤ n := Nat.le_of_dvd hn hd'.1
      refine ⟨d - 1, mem_filter.mpr ⟨mem_range.mpr (by omega), ?_⟩, by omega⟩
      simpa [show d - 1 + 1 = d by omega] using hd'.1
  rw [← hlhs, hvan, hrhs]

private lemma coeff_natCast_mul_ps (c : ℕ) (p : PowerSeries ℤ) (n : ℕ) :
    PowerSeries.coeff n ((c : PowerSeries ℤ) * p) = (c : ℤ) * PowerSeries.coeff n p := by
  have h : ((c : PowerSeries ℤ) * p) = (c : ℤ) • p := by
    rw [zsmul_eq_mul]; simp
  rw [h, map_zsmul, zsmul_eq_mul]
  simp

private lemma identity2 (n : ℕ) (_hn : 0 < n) :
    (∑ i ∈ range n, triangle n (n - i) * ((n - i : ℕ) : ℤ)) = (orphans n : ℤ) := by
  have hvan := (gSum_eq_rSum_below n 0 n (by omega)).2
  rw [DualPS.snd_sub, map_sub, sub_eq_zero] at hvan
  rw [(gSum_zero_components n).2, (rSum_zero_components n).2, map_sum, map_sum] at hvan
  -- Rewrite LHS sum by reflection `i ↦ n - 1 - i`
  have hlhs : ∑ k ∈ range n, PowerSeries.coeff n
        (((k + 1 : ℕ) : PowerSeries ℤ) * PowerSeries.mk (fun m => triangle m (k + 1))) =
      ∑ i ∈ range n, triangle n (n - i) * ((n - i : ℕ) : ℤ) := by
    have h1 : ∑ k ∈ range n, PowerSeries.coeff n
        (((k + 1 : ℕ) : PowerSeries ℤ) * PowerSeries.mk (fun m => triangle m (k + 1))) =
        ∑ k ∈ range n, triangle n (k + 1) * ((k + 1 : ℕ) : ℤ) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [coeff_natCast_mul_ps, PowerSeries.coeff_mk, mul_comm]
    rw [h1, ← Finset.sum_range_reflect (fun k => triangle n (k + 1) * ((k + 1 : ℕ) : ℤ)) n]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hilt : i < n := mem_range.mp hi
    have hidx : n - 1 - i + 1 = n - i := by omega
    rw [hidx]
  -- Evaluate RHS as cardinality of a finite set of quadruples `(k, j, r, s)`
  let Qset : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
    ((range n ×ˢ range n) ×ˢ (range n ×ˢ range (n + 1))).filter
      (fun x => x.1.2 ≤ x.1.1 ∧ (x.1.1 + 1) * (x.2.1 + 1) + (x.1.2 + 1) * x.2.2 = n)
  have hrhs : ∑ k ∈ range n, PowerSeries.coeff n
        (∑ j ∈ range (k + 1), (X ^ (k + 1) * geomPS (k + 1)) * geomPS (j + 1)) =
      (Qset.card : ℤ) := by
    have hpair : ∀ k ∈ range n, ∀ j ∈ range (k + 1),
        PowerSeries.coeff n ((X ^ (k + 1) * geomPS (k + 1)) * geomPS (j + 1)) =
        (((range n ×ˢ range (n + 1)).filter
          (fun rs => (k + 1) * (rs.1 + 1) + (j + 1) * rs.2 = n)).card : ℤ) := by
      intro k hk j hj
      have hklt : k < n := mem_range.mp hk
      rw [PowerSeries.coeff_mul]
      have hterm : ∀ ab ∈ Finset.antidiagonal n,
          PowerSeries.coeff ab.1 (X ^ (k + 1) * geomPS (k + 1)) * PowerSeries.coeff ab.2 (geomPS (j + 1)) =
          if (k + 1 ≤ ab.1 ∧ (k + 1) ∣ ab.1 ∧ (j + 1) ∣ ab.2) then 1 else 0 := by
        intro ab _
        rw [PowerSeries.coeff_X_pow_mul', coeff_geomPS]
        by_cases hle : k + 1 ≤ ab.1
        · simp only [hle, ↓reduceIte, coeff_geomPS, true_and]
          have hiff : (k + 1) ∣ ab.1 - (k + 1) ↔ (k + 1) ∣ ab.1 := by
            constructor
            · rintro ⟨t, ht⟩; exact ⟨t + 1, by rw [mul_add, mul_one]; omega⟩
            · rintro ⟨t, ht⟩; exact ⟨t - 1, by rw [Nat.mul_sub, mul_one]; omega⟩
          by_cases hd1 : (k + 1) ∣ ab.1 <;> by_cases hd2 : (j + 1) ∣ ab.2 <;> simp [hiff, hd1, hd2]
        · simp [hle]
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
      congr 1
      refine Finset.card_bij (fun ab _ => (ab.1 / (k + 1) - 1, ab.2 / (j + 1))) ?_ ?_ ?_
      · intro ab hab
        have hab' := mem_filter.mp hab
        have hsum := Finset.mem_antidiagonal.mp hab'.1
        rcases hab'.2 with ⟨hle, hd1, hd2⟩
        have hq1_pos : 1 ≤ ab.1 / (k + 1) := Nat.div_pos hle (by omega)
        have hq1_le : ab.1 / (k + 1) ≤ n := le_trans (Nat.div_le_self _ _) (by omega)
        have hq2_le : ab.2 / (j + 1) ≤ n := le_trans (Nat.div_le_self _ _) (by omega)
        refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩, ?_⟩
        have hm1 : (k + 1) * (ab.1 / (k + 1)) = ab.1 := Nat.mul_div_cancel' hd1
        have hm2 : (j + 1) * (ab.2 / (j + 1)) = ab.2 := Nat.mul_div_cancel' hd2
        have hsub : ab.1 / (k + 1) - 1 + 1 = ab.1 / (k + 1) := by omega
        rw [hsub, hm1, hm2, hsum]
      · intro ab1 h1 ab2 h2 hEq
        rcases (mem_filter.mp h1).2 with ⟨hle1, hd1a, hd1b⟩
        rcases (mem_filter.mp h2).2 with ⟨hle2, hd2a, hd2b⟩
        have hf1 : ab1.1 / (k + 1) - 1 = ab2.1 / (k + 1) - 1 := congrArg Prod.fst hEq
        have hf2 : ab1.2 / (j + 1) = ab2.2 / (j + 1) := congrArg Prod.snd hEq
        have hq1_pos : 1 ≤ ab1.1 / (k + 1) := Nat.div_pos hle1 (by omega)
        have hq2_pos : 1 ≤ ab2.1 / (k + 1) := Nat.div_pos hle2 (by omega)
        have hdiv1 : ab1.1 / (k + 1) = ab2.1 / (k + 1) := by omega
        apply Prod.ext
        · rw [← Nat.mul_div_cancel' hd1a, ← Nat.mul_div_cancel' hd2a, hdiv1]
        · rw [← Nat.mul_div_cancel' hd1b, ← Nat.mul_div_cancel' hd2b, hf2]
      · intro rs hrs
        have hrs' := mem_filter.mp hrs
        have hEq : (k + 1) * (rs.1 + 1) + (j + 1) * rs.2 = n := hrs'.2
        refine ⟨((k + 1) * (rs.1 + 1), (j + 1) * rs.2), ?_, ?_⟩
        · refine mem_filter.mpr ⟨Finset.mem_antidiagonal.mpr hEq, ?_, dvd_mul_right _ _, dvd_mul_right _ _⟩
          nlinarith
        · apply Prod.ext
          · simp [Nat.mul_div_right _ (Nat.succ_pos k)]
          · simp [Nat.mul_div_right _ (Nat.succ_pos j)]
    have hsum1 : ∑ k ∈ range n, PowerSeries.coeff n
        (∑ j ∈ range (k + 1), (X ^ (k + 1) * geomPS (k + 1)) * geomPS (j + 1)) =
        ∑ k ∈ range n, ∑ j ∈ range (k + 1),
          (((range n ×ˢ range (n + 1)).filter
            (fun rs => (k + 1) * (rs.1 + 1) + (j + 1) * rs.2 = n)).card : ℤ) := by
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [map_sum]
      exact Finset.sum_congr rfl fun j hj => hpair k hk j hj
    rw [hsum1]
    -- Collapse the triple sum into `Qset.card`
    have hnat : (∑ k ∈ range n, ∑ j ∈ range (k + 1),
        ((range n ×ˢ range (n + 1)).filter
          (fun rs => (k + 1) * (rs.1 + 1) + (j + 1) * rs.2 = n)).card) = Qset.card := by
      -- Express `Qset` as a disjoint union over `k ∈ range n` and `j ∈ range (k + 1)`
      have hcard_eq : Qset.card =
          ∑ kj ∈ (range n ×ˢ range n).filter (fun p => p.2 ≤ p.1),
            ((range n ×ˢ range (n + 1)).filter
              (fun rs => (kj.1 + 1) * (rs.1 + 1) + (kj.2 + 1) * rs.2 = n)).card := by
        rw [Finset.card_eq_sum_ones, Finset.sum_filter]
        rw [Finset.sum_product]
        have hstep : ∀ kj ∈ range n ×ˢ range n,
            (∑ rs ∈ range n ×ˢ range (n + 1),
              if kj.2 ≤ kj.1 ∧ (kj.1 + 1) * (rs.1 + 1) + (kj.2 + 1) * rs.2 = n then 1 else 0) =
            if kj.2 ≤ kj.1 then
              ((range n ×ˢ range (n + 1)).filter
                (fun rs => (kj.1 + 1) * (rs.1 + 1) + (kj.2 + 1) * rs.2 = n)).card
            else 0 := by
          intro kj _
          by_cases hle : kj.2 ≤ kj.1
          · simp [hle]
          · simp [hle]
        rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter]
      rw [hcard_eq, Finset.sum_filter, Finset.sum_product]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hklt : k < n := mem_range.mp hk
      have hfilt : (range n).filter (fun j => j ≤ k) = range (k + 1) := by
        ext j; simp only [mem_filter, mem_range]; omega
      rw [← Finset.sum_filter, hfilt]
    exact_mod_cast hnat
  -- Biject `Qset` with the subtype in `orphans n`!
  have horph : orphans n = Qset.card := by
    unfold orphans
    let φ : {t : ℕ × ℕ × ℕ × ℕ //
        t.2.2.1 < t.1 ∧ t.2.2.2 < t.2.1 ∧ t.1 * t.2.1 = n + t.2.2.1 * t.2.2.2} → Qset :=
      fun ⟨⟨a, b, c, d⟩, h1, h2, hEq⟩ =>
        ⟨((b - 1, b - d - 1), (a - c - 1, c)), by
          dsimp only at h1 h2 hEq
          have hb_pos : 1 ≤ b := by omega
          have hac_pos : 1 ≤ a - c := by omega
          have hbd_pos : 1 ≤ b - d := by omega
          have hmain : (b - 1 + 1) * (a - c - 1 + 1) + (b - d - 1 + 1) * c = n := by
            have he1 : b - 1 + 1 = b := by omega
            have he2 : a - c - 1 + 1 = a - c := by omega
            have he3 : b - d - 1 + 1 = b - d := by omega
            rw [he1, he2, he3]
            zify [show c ≤ a by omega, show d ≤ b by omega]
            have hEqZ : (a : ℤ) * b = n + c * d := by exact_mod_cast hEq
            linarith
          have hb_le : b ≤ n := by
            have h1' : b * (a - c) ≤ n := by
              have he1 : b - 1 + 1 = b := by omega
              have he2 : a - c - 1 + 1 = a - c := by omega
              rw [he1, he2] at hmain; omega
            nlinarith
          have hac_le : a - c ≤ n := by
            have h1' : b * (a - c) ≤ n := by
              have he1 : b - 1 + 1 = b := by omega
              have he2 : a - c - 1 + 1 = a - c := by omega
              rw [he1, he2] at hmain; omega
            nlinarith
          have hc_le : c ≤ n := by
            have h1' : (b - d) * c ≤ n := by
              have he3 : b - d - 1 + 1 = b - d := by omega
              rw [he3] at hmain; omega
            nlinarith
          refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by dsimp only; omega),
            mem_range.mpr (by dsimp only; omega)⟩, mem_product.mpr ⟨mem_range.mpr (by dsimp only; omega),
            mem_range.mpr (by dsimp only; omega)⟩⟩, ?_, hmain⟩
          dsimp only; omega⟩
    have hbij : Function.Bijective φ := by
      constructor
      · rintro ⟨⟨a1, b1, c1, d1⟩, h1a, h1b, h1e⟩ ⟨⟨a2, b2, c2, d2⟩, h2a, h2b, h2e⟩ hEq
        dsimp only at h1a h1b h1e h2a h2b h2e
        have hv := congrArg Subtype.val hEq
        dsimp only [φ] at hv
        have hb : b1 - 1 = b2 - 1 := congrArg (fun x => x.1.1) hv
        have hbd : b1 - d1 - 1 = b2 - d2 - 1 := congrArg (fun x => x.1.2) hv
        have hac : a1 - c1 - 1 = a2 - c2 - 1 := congrArg (fun x => x.2.1) hv
        have hc : c1 = c2 := congrArg (fun x => x.2.2) hv
        apply Subtype.ext
        have : b1 = b2 := by omega
        have : d1 = d2 := by omega
        have : a1 = a2 := by omega
        subst_vars; rfl
      · rintro ⟨⟨⟨k, j⟩, ⟨r, s⟩⟩, hmem⟩
        have hmem' := mem_filter.mp hmem
        rcases hmem'.2 with ⟨hjk, hEq⟩
        dsimp only at hjk hEq
        refine ⟨⟨(r + 1 + s, k + 1, s, k - j), ?_, ?_, ?_⟩, ?_⟩
        · dsimp only; omega
        · dsimp only; omega
        · dsimp only
          have hEqZ : ((k + 1 : ℕ) : ℤ) * (r + 1 : ℕ) + ((j + 1 : ℕ) : ℤ) * s = n := by
            exact_mod_cast hEq
          zify [hjk]
          push_cast at hEqZ
          linarith
        · apply Subtype.ext
          dsimp only [φ]
          congr 1 <;> (apply Prod.ext <;> omega)
    rw [Nat.card_congr (Equiv.ofBijective φ hbij), Nat.card_eq_fintype_card, Fintype.card_coe]
  rw [← hlhs, hvan, hrhs, horph]

private lemma main_proof : ∀ n : ℕ, 0 < n →
    (∑ i ∈ range n, triangle n (i + 1)) = (n.divisors.card : ℤ) ∧
    (∑ i ∈ range n, triangle n (n - i) * ((n - i : ℕ) : ℤ)) = (orphans n : ℤ) ∧
    triangle (2 * n) n = (n : ℤ) - (n.divisors.card : ℤ) := by
  intro n hn
  have h1 := identity1 n hn
  exact ⟨h1, identity2 n hn, identity3_of_identity1 n hn h1⟩

end OMA_A389524

theorem OMA.solution : type_of% @OMA.S_oeis_a389524.main :=
  OMA_A389524.main_proof
