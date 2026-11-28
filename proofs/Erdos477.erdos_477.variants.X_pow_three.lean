import FormalConjectures.ErdosProblems.«477»
import Mathlib

namespace OMA477

section sieve

open Finset
open ArithmeticFunction (vonMangoldt)





lemma sum_range_mul_eq (f : ℕ → ℤ) (l n : ℕ) :
    ∑ j ∈ range (l * n), f j = ∑ k ∈ range n, ∑ i ∈ range l, f (l * k + i) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, sum_range_add, ih, sum_range_succ]

lemma periodic_mul (g : ℤ → ℤ) (l : ℕ) (hper : ∀ m, g (m + l) = g m) (m : ℤ) (t : ℕ) :
    g (m + l * t) = g m := by
  induction t with
  | zero => simp
  | succ t ih =>
    have : m + (l : ℤ) * ((t + 1 : ℕ) : ℤ) = (m + l * t) + l := by push_cast; ring
    rw [this, hper, ih]

/-- A bounded function whose sums over `q` consecutive integers vanish has all its
interval sums bounded by `q`. -/
lemma abs_sum_le_of_complete_zero (f : ℤ → ℤ) (q : ℕ) (hq0 : 0 < q) (hbd : ∀ m, |f m| ≤ 1)
    (hzero : ∀ a : ℤ, ∑ j ∈ range q, f (a + j) = 0) :
    ∀ (X : ℕ) (a : ℤ), |∑ j ∈ range X, f (a + j)| ≤ q := by
  intro X
  induction X using Nat.strong_induction_on with
  | _ X ih =>
    intro a
    by_cases hX : X ≤ q
    · calc |∑ j ∈ range X, f (a + j)| ≤ ∑ j ∈ range X, |f (a + j)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j ∈ range X, (1 : ℤ) := sum_le_sum (fun j _ => hbd _)
        _ = X := by simp
        _ ≤ q := by exact_mod_cast hX
    · rw [not_le] at hX
      have hq : X = q + (X - q) := by omega
      rw [hq, sum_range_add, hzero a, zero_add]
      have h2 : ∑ x ∈ range (X - q), f (a + ((q + x : ℕ) : ℤ))
          = ∑ x ∈ range (X - q), f ((a + q) + x) := by
        refine sum_congr rfl (fun x _ => ?_)
        congr 1; push_cast; ring
      rw [h2]
      exact ih (X - q) (by omega) (a + q)

lemma sum_range_zmod (n : ℕ) [NeZero n] (φ : ZMod n → ℤ) :
    ∑ k ∈ range n, φ (k : ZMod n) = ∑ x : ZMod n, φ x := by
  refine sum_nbij' (fun k => (k : ZMod n)) (fun x => x.val) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact mem_univ _
  · intro x _; exact mem_range.mpr (ZMod.val_lt x)
  · intro a ha; exact ZMod.val_cast_of_lt (mem_range.mp ha)
  · intro x _; exact ZMod.natCast_zmod_val x
  · intro a _; rfl

/-- For `l` coprime to the period `n`, the points `b + l k`, `k < n`, form a complete system. -/
lemma sum_coprime_mul (h : ℤ → ℤ) (n l : ℕ) (hn : 0 < n) (hcop : Nat.Coprime l n)
    (hper : ∀ m, h (m + n) = h m) (b : ℤ) :
    ∑ k ∈ range n, h (b + l * k) = ∑ i ∈ range n, h (b + i) := by
  have : NeZero n := ⟨hn.ne'⟩
  let H : ZMod n → ℤ := fun x => h (b + x.val)
  have key : ∀ j : ℕ, h (b + j) = H (j : ZMod n) := by
    intro j
    simp only [H, ZMod.val_natCast]
    have hj : (j : ℤ) = ((j % n : ℕ) : ℤ) + n * ((j / n : ℕ) : ℤ) := by
      exact_mod_cast (Nat.mod_add_div j n).symm
    rw [hj, ← add_assoc, periodic_mul h n hper]
  have h1 : ∑ k ∈ range n, h (b + l * k) = ∑ k ∈ range n, H ((l : ZMod n) * (k : ZMod n)) := by
    refine sum_congr rfl (fun k _ => ?_)
    have := key (l * k)
    push_cast at this
    exact this
  have h2 : ∑ i ∈ range n, h (b + i) = ∑ i ∈ range n, H (i : ZMod n) :=
    sum_congr rfl (fun i _ => key i)
  rw [h1, h2, sum_range_zmod n (fun x => H ((l : ZMod n) * x)), sum_range_zmod n H]
  let u : (ZMod n)ˣ := ZMod.unitOfCoprime l hcop
  have hu : ((u : (ZMod n)ˣ) : ZMod n) = (l : ZMod n) := ZMod.coe_unitOfCoprime l hcop
  rw [← hu]
  exact Equiv.sum_comp (Units.mulLeft u) H

/-- Complete sums of a product of two periodic functions with coprime periods vanish as soon
as one of the two has vanishing complete sums. -/
lemma offdiag_complete_zero (g h : ℤ → ℤ) (l n : ℕ) (hn : 0 < n) (hcop : l.Coprime n)
    (hperg : ∀ m, g (m + l) = g m) (hperh : ∀ m, h (m + n) = h m)
    (hzero : ∀ a : ℤ, ∑ i ∈ range n, h (a + i) = 0) (a : ℤ) :
    ∑ j ∈ range (l * n), g (a + j) * h (a + j) = 0 := by
  rw [sum_range_mul_eq (fun j => g (a + j) * h (a + j)) l n, sum_comm]
  refine sum_eq_zero (fun i _ => ?_)
  have h1 : ∀ k ∈ range n, g (a + ((l * k + i : ℕ) : ℤ)) * h (a + ((l * k + i : ℕ) : ℤ))
      = g (a + i) * h ((a + i) + l * k) := by
    intro k _
    have e : a + ((l * k + i : ℕ) : ℤ) = (a + i) + l * k := by push_cast; ring
    rw [e, periodic_mul g l hperg]
  rw [sum_congr rfl h1, ← mul_sum, sum_coprime_mul h n l hn hcop hperh, hzero, mul_zero]

/-- If each block of `l` consecutive integers contains at most one zero of `f`, then an
interval of length `X` contains at most `X / l + 1` zeros. -/
lemma card_zero_le (f : ℤ → ℤ) (l : ℕ)
    (hroot : ∀ a : ℤ, ∑ i ∈ range l, (if f (a + i) = 0 then 1 else 0) ≤ 1) :
    ∀ (X : ℕ) (a : ℤ), l * ∑ j ∈ range X, (if f (a + j) = 0 then 1 else 0) ≤ X + l := by
  intro X
  induction X using Nat.strong_induction_on with
  | _ X ih =>
    intro a
    by_cases hX : X ≤ l
    · have : ∑ j ∈ range X, (if f (a + j) = 0 then 1 else 0)
          ≤ ∑ j ∈ range l, (if f (a + j) = 0 then 1 else 0) :=
        sum_le_sum_of_subset (range_mono hX)
      calc l * ∑ j ∈ range X, (if f (a + j) = 0 then 1 else 0) ≤ l * 1 :=
            Nat.mul_le_mul_left l (this.trans (hroot a))
        _ ≤ X + l := by omega
    · rw [not_le] at hX
      by_cases hl : l = 0
      · subst hl; simp
      have hq : X = l + (X - l) := by omega
      rw [hq, sum_range_add, Nat.mul_add]
      have h2 : ∑ x ∈ range (X - l), (if f (a + ((l + x : ℕ) : ℤ)) = 0 then 1 else 0)
          = ∑ x ∈ range (X - l), (if f ((a + l) + x) = 0 then 1 else 0) := by
        refine sum_congr rfl (fun x _ => ?_)
        have e : a + ((l + x : ℕ) : ℤ) = (a + l) + x := by push_cast; ring
        rw [e]
      rw [h2]
      have h3 := ih (X - l) (by omega) (a + l)
      have h4 := Nat.mul_le_mul_left l (hroot a)
      omega

/-- Abstract square sieve. `g l` is `l`-periodic, bounded by 1, has vanishing complete sums
and at most one zero per period; the periods are pairwise coprime. If on `B ⊆ [0, X)` the sum
of the `g l` equals `#P` minus the number of vanishing terms, then `B` is small. -/
theorem abstract_sieve (P : Finset ℕ) (g : ℕ → ℤ → ℤ) (lmin lmax : ℕ)
    (hmin : ∀ l ∈ P, lmin ≤ l) (hmax : ∀ l ∈ P, l ≤ lmax)
    (hpos : ∀ l ∈ P, 0 < l)
    (hcop : ∀ l ∈ P, ∀ l' ∈ P, l ≠ l' → Nat.Coprime l l')
    (hper : ∀ l ∈ P, ∀ m, g l (m + l) = g l m)
    (hbd : ∀ l ∈ P, ∀ m, |g l m| ≤ 1)
    (hzero : ∀ l ∈ P, ∀ a : ℤ, ∑ i ∈ range l, g l (a + i) = 0)
    (hroot : ∀ l ∈ P, ∀ a : ℤ, ∑ i ∈ range l, (if g l (a + i) = 0 then 1 else 0) ≤ 1)
    (a : ℤ) (X : ℕ) (B : Finset ℕ) (hB : B ⊆ range X)
    (hgood : ∀ j ∈ B, ∑ l ∈ P, g l (a + j)
      = (P.card : ℤ) - ((∑ l ∈ P, (if g l (a + j) = 0 then 1 else 0) : ℕ) : ℤ)) :
    lmin * P.card * B.card ≤ 2 * P.card * (X + lmax) + 4 * lmin * (X + P.card * lmax ^ 2) := by
  classical
  set Z : ℕ → ℕ := fun j => ∑ l ∈ P, (if g l (a + j) = 0 then 1 else 0) with hZ
  set N : ℕ → ℤ := fun j => ∑ l ∈ P, g l (a + j) with hN
  set B₁ := B.filter (fun j => P.card ≤ 2 * Z j) with hB₁
  set B₂ := B.filter (fun j => ¬ P.card ≤ 2 * Z j) with hB₂
  have hcard : B₁.card + B₂.card = B.card := card_filter_add_card_filter_not _
  -- Step 1
  have step1 : lmin * (P.card * B₁.card) ≤ 2 * (P.card * (X + lmax)) := by
    have h1 : P.card * B₁.card ≤ ∑ j ∈ range X, 2 * Z j := by
      calc P.card * B₁.card = ∑ _j ∈ B₁, P.card := by rw [sum_const, smul_eq_mul, mul_comm]
        _ ≤ ∑ j ∈ B₁, 2 * Z j := sum_le_sum (fun j hj => (mem_filter.mp hj).2)
        _ ≤ ∑ j ∈ range X, 2 * Z j :=
          sum_le_sum_of_subset ((filter_subset _ _).trans hB)
    have h2 : ∑ j ∈ range X, 2 * Z j
        = 2 * ∑ l ∈ P, ∑ j ∈ range X, (if g l (a + j) = 0 then 1 else 0) := by
      rw [← mul_sum, sum_comm]
    have h3 : lmin * ∑ l ∈ P, ∑ j ∈ range X, (if g l (a + j) = 0 then 1 else 0)
        ≤ P.card * (X + lmax) := by
      rw [mul_sum]
      calc ∑ l ∈ P, lmin * ∑ j ∈ range X, (if g l (a + j) = 0 then 1 else 0)
          ≤ ∑ _l ∈ P, (X + lmax) := by
            refine sum_le_sum (fun l hl => ?_)
            calc lmin * ∑ j ∈ range X, (if g l (a + j) = 0 then 1 else 0)
                ≤ l * ∑ j ∈ range X, (if g l (a + j) = 0 then 1 else 0) :=
                  Nat.mul_le_mul_right _ (hmin l hl)
              _ ≤ X + l := card_zero_le (g l) l (hroot l hl) X a
              _ ≤ X + lmax := Nat.add_le_add_left (hmax l hl) X
        _ = P.card * (X + lmax) := by rw [sum_const, smul_eq_mul]
    calc lmin * (P.card * B₁.card) ≤ lmin * ∑ j ∈ range X, 2 * Z j := Nat.mul_le_mul_left _ h1
      _ = 2 * (lmin * ∑ l ∈ P, ∑ j ∈ range X, (if g l (a + j) = 0 then 1 else 0)) := by
          rw [h2]; ring
      _ ≤ 2 * (P.card * (X + lmax)) := Nat.mul_le_mul_left _ h3
  -- Step 2
  have hsq : ∀ l ∈ P, ∀ m, g l m * g l m ≤ 1 := by
    intro l hl m
    have := hbd l hl m
    have h1 := abs_le.mp this
    nlinarith [h1.1, h1.2]
  have hpair : ∀ l ∈ P, ∀ l' ∈ P, ∑ j ∈ range X, g l (a + j) * g l' (a + j)
      ≤ (if l = l' then (X : ℤ) else 0) + (lmax : ℤ) ^ 2 := by
    intro l hl l' hl'
    by_cases hll : l = l'
    · subst hll
      rw [if_pos rfl]
      calc ∑ j ∈ range X, g l (a + j) * g l (a + j) ≤ ∑ _j ∈ range X, (1 : ℤ) :=
            sum_le_sum (fun j _ => hsq l hl _)
        _ = X := by simp
        _ ≤ (X : ℤ) + (lmax : ℤ) ^ 2 := by nlinarith [sq_nonneg (lmax : ℤ)]
    · rw [if_neg hll, zero_add]
      have hq0 : 0 < l * l' := Nat.mul_pos (hpos l hl) (hpos l' hl')
      have hb : ∀ m, |g l m * g l' m| ≤ 1 := by
        intro m
        rw [abs_mul]
        have h1 := hbd l hl m
        have h2 := hbd l' hl' m
        nlinarith [abs_nonneg (g l m), abs_nonneg (g l' m)]
      have hz : ∀ b : ℤ, ∑ j ∈ range (l * l'), g l (b + j) * g l' (b + j) = 0 := fun b =>
        offdiag_complete_zero (g l) (g l') l l' (hpos l' hl') (hcop l hl l' hl' hll)
          (hper l hl) (hper l' hl') (hzero l' hl') b
      have h3 := abs_sum_le_of_complete_zero (fun m => g l m * g l' m) (l * l') hq0 hb hz X a
      have h4 : ((l * l' : ℕ) : ℤ) ≤ (lmax : ℤ) ^ 2 := by
        have : l * l' ≤ lmax ^ 2 := by
          rw [pow_two]; exact Nat.mul_le_mul (hmax l hl) (hmax l' hl')
        exact_mod_cast this
      exact (le_abs_self _).trans (h3.trans h4)
  have hN2 : ∑ j ∈ range X, N j ^ 2 ≤ (P.card : ℤ) * X + (P.card : ℤ) ^ 2 * (lmax : ℤ) ^ 2 := by
    have e : ∑ j ∈ range X, N j ^ 2
        = ∑ l ∈ P, ∑ l' ∈ P, ∑ j ∈ range X, g l (a + j) * g l' (a + j) := by
      simp only [hN, pow_two, sum_mul_sum]
      rw [sum_comm]
      refine sum_congr rfl (fun l _ => ?_)
      rw [sum_comm]
    rw [e]
    calc ∑ l ∈ P, ∑ l' ∈ P, ∑ j ∈ range X, g l (a + j) * g l' (a + j)
        ≤ ∑ l ∈ P, ∑ l' ∈ P, ((if l = l' then (X : ℤ) else 0) + (lmax : ℤ) ^ 2) :=
          sum_le_sum (fun l hl => sum_le_sum (fun l' hl' => hpair l hl l' hl'))
      _ = ∑ l ∈ P, ((X : ℤ) + P.card * (lmax : ℤ) ^ 2) := by
          refine sum_congr rfl (fun l hl => ?_)
          rw [sum_add_distrib, sum_ite_eq, if_pos hl, sum_const, nsmul_eq_mul]
      _ = (P.card : ℤ) * X + (P.card : ℤ) ^ 2 * (lmax : ℤ) ^ 2 := by
          rw [sum_const, nsmul_eq_mul]; ring
  have step2z : (P.card : ℤ) ^ 2 * B₂.card
      ≤ 4 * ((P.card : ℤ) * X + (P.card : ℤ) ^ 2 * (lmax : ℤ) ^ 2) := by
    have h1 : ∀ j ∈ B₂, (P.card : ℤ) ^ 2 ≤ 4 * N j ^ 2 := by
      intro j hj
      obtain ⟨hjB, hjlt⟩ := mem_filter.mp hj
      have hg := hgood j hjB
      have hlt : (2 * Z j : ℤ) < P.card := by
        rw [not_le] at hjlt; exact_mod_cast hjlt
      have hNj : N j = (P.card : ℤ) - (Z j : ℤ) := hg
      have hZ0 : (0 : ℤ) ≤ Z j := Int.natCast_nonneg _
      nlinarith
    calc (P.card : ℤ) ^ 2 * B₂.card = ∑ _j ∈ B₂, (P.card : ℤ) ^ 2 := by
          rw [sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ j ∈ B₂, 4 * N j ^ 2 := sum_le_sum h1
      _ ≤ ∑ j ∈ range X, 4 * N j ^ 2 :=
          sum_le_sum_of_subset_of_nonneg ((filter_subset _ _).trans hB)
            (fun j _ _ => by positivity)
      _ = 4 * ∑ j ∈ range X, N j ^ 2 := by rw [mul_sum]
      _ ≤ 4 * ((P.card : ℤ) * X + (P.card : ℤ) ^ 2 * (lmax : ℤ) ^ 2) :=
          mul_le_mul_of_nonneg_left hN2 (by norm_num)
  have step2 : P.card * B₂.card ≤ 4 * (X + P.card * lmax ^ 2) := by
    by_cases hP : P.card = 0
    · simp [hP]
    have hPpos : (0 : ℤ) < P.card := by exact_mod_cast Nat.pos_of_ne_zero hP
    have : (P.card : ℤ) * ((P.card : ℤ) * B₂.card)
        ≤ (P.card : ℤ) * (4 * ((X : ℤ) + (P.card : ℤ) * (lmax : ℤ) ^ 2)) := by
      calc (P.card : ℤ) * ((P.card : ℤ) * B₂.card) = (P.card : ℤ) ^ 2 * B₂.card := by ring
        _ ≤ 4 * ((P.card : ℤ) * X + (P.card : ℤ) ^ 2 * (lmax : ℤ) ^ 2) := step2z
        _ = (P.card : ℤ) * (4 * ((X : ℤ) + (P.card : ℤ) * (lmax : ℤ) ^ 2)) := by ring
    have h5 := le_of_mul_le_mul_left this hPpos
    exact_mod_cast h5
  calc lmin * P.card * B.card = lmin * (P.card * B₁.card) + lmin * (P.card * B₂.card) := by
        rw [← hcard]; ring
    _ ≤ 2 * (P.card * (X + lmax)) + lmin * (4 * (X + P.card * lmax ^ 2)) :=
        Nat.add_le_add step1 (Nat.mul_le_mul_left _ step2)
    _ = 2 * P.card * (X + lmax) + 4 * lmin * (X + P.card * lmax ^ 2) := by ring

/-- Lemma 1 of PROOF.md: for a prime `l ≡ 2 (mod 3)`, `l ≥ 5`, the map
`a ↦ 3 (4 e (c - a^3) / b - b^2)` is a bijection of `ZMod l`. -/
lemma phi_bijective (l : ℕ) [hl : Fact l.Prime] (hl3 : l % 3 = 2) (hl5 : 5 ≤ l)
    (c e b : ZMod l) (he : e ≠ 0) (hb : b ≠ 0) :
    Function.Bijective (fun a : ZMod l => 3 * (4 * e * (c - a ^ 3) * b⁻¹ - b ^ 2)) := by
  have key : ∀ x : ZMod l, x ^ (3 * (2 * (l / 3) + 1)) = x := by
    intro x
    have h1 : 3 * (2 * (l / 3) + 1) = l + (l - 1) := by have := hl.out.two_le; omega
    have h2 : x * x ^ (l - 1) = x ^ l := by rw [← pow_succ', Nat.sub_add_cancel hl.out.one_le]
    rw [h1, pow_add, ZMod.pow_card, h2, ZMod.pow_card]
  have h2 : (2 : ZMod l) ≠ 0 := by
    intro h
    have : (l : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 l).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h3 : (3 : ZMod l) ≠ 0 := by
    intro h
    have : (l : ℕ) ∣ 3 := (ZMod.natCast_eq_zero_iff 3 l).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h4 : (4 : ZMod l) ≠ 0 := by
    have : (4 : ZMod l) = 2 * 2 := by norm_num
    rw [this]; exact mul_ne_zero h2 h2
  apply Finite.injective_iff_bijective.mp
  intro a a' h
  simp only at h
  have hcube : a ^ 3 = a' ^ 3 := by
    have h5 := mul_left_cancel₀ h3 h
    have h6 : 4 * e * (c - a ^ 3) * b⁻¹ = 4 * e * (c - a' ^ 3) * b⁻¹ := by linear_combination h5
    have h7 := mul_right_cancel₀ (inv_ne_zero hb) h6
    have h8 := mul_left_cancel₀ (mul_ne_zero h4 he) h7
    linear_combination -h8
  rw [← key a, ← key a', pow_mul, pow_mul, hcube]


/-- The polynomial `F(m) = 3 (4 e (c - t^3)/d - d^2)` with `t = r + d m`, written with
`κ = (c - r^3)/d` so that it has integer coefficients. -/
def Fint (d r κ e : ℤ) (m : ℤ) : ℤ :=
  3 * (4 * e * (κ - 3 * r ^ 2 * m - 3 * r * d * m ^ 2 - d ^ 2 * m ^ 3) - d ^ 2)

lemma Fint_cast (l : ℕ) (d r κ e m : ℤ) :
    ((Fint d r κ e m : ℤ) : ZMod l) = 3 * (4 * (e : ZMod l) * ((κ : ZMod l)
      - 3 * (r : ZMod l) ^ 2 * (m : ZMod l) - 3 * (r : ZMod l) * (d : ZMod l) * (m : ZMod l) ^ 2
      - (d : ZMod l) ^ 2 * (m : ZMod l) ^ 3) - (d : ZMod l) ^ 2) := by
  simp only [Fint]; push_cast; ring

/-- Reduction of `F` modulo a prime `l ≡ 2 (mod 3)` not dividing `6c` is a bijection of `ZMod l`,
whether or not `l` divides `d`. -/
lemma Fbar_bijective (l : ℕ) [hl : Fact l.Prime] (hl3 : l % 3 = 2) (hl5 : 5 ≤ l)
    (c d r κ e : ZMod l) (hc : c = r ^ 3 + d * κ) (hc0 : c ≠ 0) (he : e ^ 2 = 1) :
    Function.Bijective (fun x : ZMod l =>
      3 * (4 * e * (κ - 3 * r ^ 2 * x - 3 * r * d * x ^ 2 - d ^ 2 * x ^ 3) - d ^ 2)) := by
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at he
  have h2 : (2 : ZMod l) ≠ 0 := by
    intro h
    have : (l : ℕ) ∣ 2 := (ZMod.natCast_eq_zero_iff 2 l).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have h3 : (3 : ZMod l) ≠ 0 := by
    intro h
    have : (l : ℕ) ∣ 3 := (ZMod.natCast_eq_zero_iff 3 l).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  by_cases hd : d = 0
  · subst hd
    have hr : r ≠ 0 := by
      rintro rfl
      apply hc0
      rw [hc]; ring
    apply Finite.injective_iff_bijective.mp
    intro x y h
    simp only at h
    have key : (2 * 2 * 3 * 3 * e * r ^ 2) * (x - y) = 0 := by linear_combination (-1 : ZMod l) * h
    rcases mul_eq_zero.mp key with h' | h'
    · exact absurd h' (by
        have := pow_ne_zero 2 hr
        simp only [mul_eq_zero, not_or]
        exact ⟨⟨⟨⟨⟨h2, h2⟩, h3⟩, h3⟩, he0⟩, this⟩)
    · exact sub_eq_zero.mp h'
  · have hφ := phi_bijective l hl3 hl5 c e d he0 hd
    have haff : Function.Bijective (fun x : ZMod l => r + d * x) := by
      apply Finite.injective_iff_bijective.mp
      intro x y h
      simp only at h
      exact mul_left_cancel₀ hd (add_left_cancel h)
    have hcomp : (fun x : ZMod l =>
        3 * (4 * e * (κ - 3 * r ^ 2 * x - 3 * r * d * x ^ 2 - d ^ 2 * x ^ 3) - d ^ 2))
        = (fun a : ZMod l => 3 * (4 * e * (c - a ^ 3) * d⁻¹ - d ^ 2)) ∘ (fun x => r + d * x) := by
      funext x
      simp only [Function.comp]
      have e1 : c - (r + d * x) ^ 3 = d * (κ - 3 * r ^ 2 * x - 3 * r * d * x ^ 2 - d ^ 2 * x ^ 3) := by
        rw [hc]; ring
      rw [e1, show 4 * e * (d * (κ - 3 * r ^ 2 * x - 3 * r * d * x ^ 2 - d ^ 2 * x ^ 3)) * d⁻¹
        = 4 * e * (κ - 3 * r ^ 2 * x - 3 * r * d * x ^ 2 - d ^ 2 * x ^ 3) * (d * d⁻¹) by ring,
        mul_inv_cancel₀ hd, mul_one]
    rw [hcomp]
    exact hφ.comp haff


/-- The sieve weight: Legendre symbol of `F(m)` modulo `l` (zero when `l` is not prime). -/
noncomputable def gsym (d r κ e : ℤ) (l : ℕ) (m : ℤ) : ℤ :=
  if h : l.Prime then @legendreSym l ⟨h⟩ (Fint d r κ e m) else 0

/-- `F` reduced modulo `l`. -/
def Fbar (l : ℕ) (d r κ e : ℤ) (x : ZMod l) : ZMod l :=
  3 * (4 * (e : ZMod l) * ((κ : ZMod l) - 3 * (r : ZMod l) ^ 2 * x
    - 3 * (r : ZMod l) * (d : ZMod l) * x ^ 2 - (d : ZMod l) ^ 2 * x ^ 3) - (d : ZMod l) ^ 2)

lemma gsym_eq (l : ℕ) [hl : Fact l.Prime] (d r κ e m : ℤ) :
    gsym d r κ e l m = quadraticChar (ZMod l) (Fbar l d r κ e (m : ZMod l)) := by
  unfold gsym
  rw [dif_pos hl.out]
  unfold legendreSym Fbar
  rw [Fint_cast]

lemma quadraticChar_abs_le (l : ℕ) [Fact l.Prime] (y : ZMod l) :
    |(quadraticChar (ZMod l) y : ℤ)| ≤ 1 := by
  by_cases hy : y = 0
  · subst hy; simp
  · rcases quadraticChar_dichotomy hy with h | h <;> rw [h] <;> simp

section props

variable (l : ℕ) [hl : Fact l.Prime] (c d r κ e : ℤ)

include hl in
lemma gsym_per (m : ℤ) : gsym d r κ e l (m + l) = gsym d r κ e l m := by
  rw [gsym_eq, gsym_eq]
  congr 2
  push_cast
  simp

include hl in
lemma gsym_bd (m : ℤ) : |gsym d r κ e l m| ≤ 1 := by
  rw [gsym_eq]; exact quadraticChar_abs_le l _

include hl in
lemma gsym_zero (hl3 : l % 3 = 2) (hl5 : 5 ≤ l) (hκ : c - r ^ 3 = d * κ) (he : e ^ 2 = 1)
    (hc : ¬ (l : ℤ) ∣ c) (a : ℤ) : ∑ i ∈ range l, gsym d r κ e l (a + i) = 0 := by
  have : NeZero l := ⟨hl.out.ne_zero⟩
  have hbij : Function.Bijective (Fbar l d r κ e) := by
    have hc' : (c : ZMod l) = (r : ZMod l) ^ 3 + (d : ZMod l) * (κ : ZMod l) := by
      have : c = r ^ 3 + d * κ := by linarith
      rw [this]; push_cast; ring
    have hc0 : (c : ZMod l) ≠ 0 := fun h => hc ((ZMod.intCast_zmod_eq_zero_iff_dvd c l).mp h)
    have he' : (e : ZMod l) ^ 2 = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod l) he
      push_cast at this
      exact this
    exact Fbar_bijective l hl3 hl5 (c : ZMod l) d r κ e hc' hc0 he'
  have h1 : ∑ i ∈ range l, gsym d r κ e l (a + i)
      = ∑ i ∈ range l, (quadraticChar (ZMod l) (Fbar l d r κ e ((a : ZMod l) + (i : ZMod l))) : ℤ) := by
    refine sum_congr rfl (fun i _ => ?_)
    rw [gsym_eq]
    push_cast
    rfl
  rw [h1, sum_range_zmod l (fun x => (quadraticChar (ZMod l) (Fbar l d r κ e ((a : ZMod l) + x)) : ℤ))]
  have e1 : ∑ x : ZMod l, (quadraticChar (ZMod l) (Fbar l d r κ e ((a : ZMod l) + x)) : ℤ)
      = ∑ x : ZMod l, (quadraticChar (ZMod l) (Fbar l d r κ e x) : ℤ) :=
    Equiv.sum_comp (Equiv.addLeft (a : ZMod l))
      (fun x => (quadraticChar (ZMod l) (Fbar l d r κ e x) : ℤ))
  have e2 : ∑ x : ZMod l, (quadraticChar (ZMod l) (Fbar l d r κ e x) : ℤ)
      = ∑ y : ZMod l, (quadraticChar (ZMod l) y : ℤ) :=
    Equiv.sum_comp (Equiv.ofBijective (Fbar l d r κ e) hbij)
      (fun y => (quadraticChar (ZMod l) y : ℤ))
  rw [e1, e2]
  apply quadraticChar_sum_zero
  rw [ZMod.ringChar_zmod_n]
  omega

include hl in
lemma gsym_root (hl3 : l % 3 = 2) (hl5 : 5 ≤ l) (hκ : c - r ^ 3 = d * κ) (he : e ^ 2 = 1)
    (hc : ¬ (l : ℤ) ∣ c) (a : ℤ) :
    ∑ i ∈ range l, (if gsym d r κ e l (a + i) = 0 then 1 else 0) ≤ 1 := by
  have hbij : Function.Bijective (Fbar l d r κ e) := by
    have hc' : (c : ZMod l) = (r : ZMod l) ^ 3 + (d : ZMod l) * (κ : ZMod l) := by
      have : c = r ^ 3 + d * κ := by linarith
      rw [this]; push_cast; ring
    have hc0 : (c : ZMod l) ≠ 0 := fun h => hc ((ZMod.intCast_zmod_eq_zero_iff_dvd c l).mp h)
    have he' : (e : ZMod l) ^ 2 = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod l) he
      push_cast at this
      exact this
    exact Fbar_bijective l hl3 hl5 (c : ZMod l) d r κ e hc' hc0 he'
  rw [sum_boole]
  simp only [Nat.cast_id]
  apply card_le_one.mpr
  intro i hi j hj
  obtain ⟨hi1, hi2⟩ := mem_filter.mp hi
  obtain ⟨hj1, hj2⟩ := mem_filter.mp hj
  rw [gsym_eq, quadraticChar_eq_zero_iff] at hi2 hj2
  have h := hbij.1 (hi2.trans hj2.symm)
  push_cast at h
  have h' : ((i : ℕ) : ZMod l) = ((j : ℕ) : ZMod l) := add_left_cancel h
  have := (ZMod.natCast_eq_natCast_iff' i j l).mp h'
  rwa [Nat.mod_eq_of_lt (mem_range.mp hi1), Nat.mod_eq_of_lt (mem_range.mp hj1)] at this

include hl in
/-- On a square value the weight is `0` or `1`. -/
lemma gsym_square (m s : ℤ) (h : Fint d r κ e m = 9 * s ^ 2) :
    gsym d r κ e l m = 1 - (if gsym d r κ e l m = 0 then 1 else 0) := by
  have hg : gsym d r κ e l m = legendreSym l ((3 * s) ^ 2) := by
    unfold gsym
    rw [dif_pos hl.out, h]
    congr 1; ring
  by_cases h0 : ((3 * s : ℤ) : ZMod l) = 0
  · have : gsym d r κ e l m = 0 := by
      rw [hg, legendreSym.eq_zero_iff]
      push_cast at h0 ⊢
      rw [h0]; ring
    rw [if_pos this, this]; ring
  · have : gsym d r κ e l m = 1 := by rw [hg]; exact legendreSym.sq_one' l h0
    rw [this]; simp

end props

/-- Square sieve for the polynomial `F` (Lemma 2 of PROOF.md, uniform form): among `X`
consecutive integers `m`, those with `F(m) = 9 s^2` are few. -/
theorem square_sieve (c d r κ e : ℤ) (hκ : c - r ^ 3 = d * κ) (he : e ^ 2 = 1)
    (P : Finset ℕ) (lmin lmax : ℕ) (hmin : ∀ l ∈ P, lmin ≤ l) (hmax : ∀ l ∈ P, l ≤ lmax)
    (hP : ∀ l ∈ P, l.Prime ∧ l % 3 = 2 ∧ 5 ≤ l ∧ ¬ (l : ℤ) ∣ c)
    (a : ℤ) (X : ℕ) (B : Finset ℕ) (hB : B ⊆ range X)
    (hbad : ∀ j ∈ B, ∃ s : ℤ, Fint d r κ e (a + j) = 9 * s ^ 2) :
    lmin * P.card * B.card ≤ 2 * P.card * (X + lmax) + 4 * lmin * (X + P.card * lmax ^ 2) := by
  refine abstract_sieve P (gsym d r κ e) lmin lmax hmin hmax ?_ ?_ ?_ ?_ ?_ ?_ a X B hB ?_
  · intro l hl; exact (hP l hl).1.pos
  · intro l hl l' hl' hne
    exact (Nat.coprime_primes (hP l hl).1 (hP l' hl').1).mpr hne
  · intro l hl m
    have : Fact l.Prime := ⟨(hP l hl).1⟩
    exact gsym_per l d r κ e m
  · intro l hl m
    have : Fact l.Prime := ⟨(hP l hl).1⟩
    exact gsym_bd l d r κ e m
  · intro l hl b
    have : Fact l.Prime := ⟨(hP l hl).1⟩
    exact gsym_zero l c d r κ e (hP l hl).2.1 (hP l hl).2.2.1 hκ he (hP l hl).2.2.2 b
  · intro l hl b
    have : Fact l.Prime := ⟨(hP l hl).1⟩
    exact gsym_root l c d r κ e (hP l hl).2.1 (hP l hl).2.2.1 hκ he (hP l hl).2.2.2 b
  · intro j hj
    obtain ⟨s, hs⟩ := hbad j hj
    have h1 : ∀ l ∈ P, gsym d r κ e l (a + j)
        = 1 - (if gsym d r κ e l (a + j) = 0 then 1 else 0) := by
      intro l hl
      have : Fact l.Prime := ⟨(hP l hl).1⟩
      exact gsym_square l d r κ e (a + j) s hs
    rw [sum_congr rfl h1, sum_sub_distrib]
    simp



/-- Quantitative supply of primes `≡ 2 (mod 3)`: for some exponent `n`, every interval
`(Λ, Λ^n]` with `Λ` large contains at least `Λ` of them. -/
def PrimesQuant : Prop :=
  ∃ n : ℕ, ∃ Λ₀ : ℕ, ∀ Λ : ℕ, Λ₀ ≤ Λ →
    Λ ≤ ((Finset.Ioc Λ (Λ ^ n)).filter (fun l => l.Prime ∧ l % 3 = 2)).card

/-- Lemma 2 of PROOF.md in its final uniform form: among `X` consecutive integers `m`, at most
`(6 X + 6 Λ^(2n+1)) / Λ` have `F(m) = 9 s^2`, for every large `Λ`. -/
theorem small_bound (hQ : PrimesQuant) (c : ℤ) (hc : c ≠ 0) :
    ∃ n Λ₀ : ℕ, ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ d r κ e : ℤ, c - r ^ 3 = d * κ → e ^ 2 = 1 →
      ∀ (a : ℤ) (X : ℕ) (B : Finset ℕ), B ⊆ range X →
        (∀ j ∈ B, ∃ s : ℤ, Fint d r κ e (a + j) = 9 * s ^ 2) →
        Λ * B.card ≤ 6 * X + 6 * Λ ^ (2 * n + 1) := by
  obtain ⟨n, Λ₀, hQ⟩ := hQ
  refine ⟨n, max Λ₀ (max 5 c.natAbs), ?_⟩
  intro Λ hΛ d r κ e hκ he a X B hB hbad
  have hΛ0 : Λ₀ ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛ5 : 5 ≤ Λ := ((le_max_left _ _).trans (le_max_right _ _)).trans hΛ
  have hΛc : c.natAbs ≤ Λ := ((le_max_right _ _).trans (le_max_right _ _)).trans hΛ
  set P := (Finset.Ioc Λ (Λ ^ n)).filter (fun l => l.Prime ∧ l % 3 = 2) with hPdef
  have hPcard : Λ ≤ P.card := hQ Λ hΛ0
  have hmem : ∀ l ∈ P, Λ < l ∧ l ≤ Λ ^ n ∧ l.Prime ∧ l % 3 = 2 := by
    intro l hl
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hl
    obtain ⟨h3, h4⟩ := Finset.mem_Ioc.mp h1
    exact ⟨h3, h4, h2.1, h2.2⟩
  have hP : ∀ l ∈ P, l.Prime ∧ l % 3 = 2 ∧ 5 ≤ l ∧ ¬ (l : ℤ) ∣ c := by
    intro l hl
    obtain ⟨h1, _, h3, h4⟩ := hmem l hl
    refine ⟨h3, h4, by omega, ?_⟩
    intro hdvd
    have h5 : l ∣ c.natAbs := Int.natCast_dvd.mp hdvd
    have h6 := Nat.le_of_dvd (Int.natAbs_pos.mpr hc) h5
    omega
  have key := square_sieve c d r κ e hκ he P Λ (Λ ^ n)
    (fun l hl => (hmem l hl).1.le) (fun l hl => (hmem l hl).2.1) hP a X B hB hbad
  have hPpos : 0 < P.card := by omega
  have hΛ1 : 1 ≤ Λ := by omega
  have hpow : Λ ^ n ≤ Λ ^ (2 * n + 1) := Nat.pow_le_pow_right hΛ1 (by omega)
  have hpow2 : Λ * (Λ ^ n) ^ 2 = Λ ^ (2 * n + 1) := by ring
  have h1 : P.card * (Λ * B.card) ≤ P.card * (6 * X + 6 * Λ ^ (2 * n + 1)) := by
    calc P.card * (Λ * B.card) = Λ * P.card * B.card := by ring
      _ ≤ 2 * P.card * (X + Λ ^ n) + 4 * Λ * (X + P.card * (Λ ^ n) ^ 2) := key
      _ = 2 * P.card * X + 2 * P.card * Λ ^ n + 4 * (Λ * X) + 4 * P.card * (Λ * (Λ ^ n) ^ 2) := by
          ring
      _ ≤ 2 * P.card * X + 2 * P.card * Λ ^ (2 * n + 1) + 4 * (P.card * X)
            + 4 * P.card * Λ ^ (2 * n + 1) := by
          rw [hpow2]
          have a1 : 2 * P.card * Λ ^ n ≤ 2 * P.card * Λ ^ (2 * n + 1) :=
            Nat.mul_le_mul_left _ hpow
          have a2 : 4 * (Λ * X) ≤ 4 * (P.card * X) :=
            Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hPcard)
          omega
      _ = P.card * (6 * X + 6 * Λ ^ (2 * n + 1)) := by ring
  exact Nat.le_of_mul_le_mul_left h1 hPpos





/-- Chebyshev's constant: `ψ(x) ≤ c0 x`. -/
noncomputable def c0 : ℝ := Real.log 4 + 4

lemma c0_pos : 0 < c0 := by
  have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
  unfold c0; linarith

lemma psi_range_le (M : ℕ) : ∑ k ∈ range M, vonMangoldt k ≤ c0 * M := by
  have h1 : ∑ k ∈ range M, vonMangoldt k ≤ Chebyshev.psi (M : ℝ) := by
    rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      simp only [mem_range] at hk
      simp only [mem_Icc]
      omega
    · intro _ _ _; exact ArithmeticFunction.vonMangoldt_nonneg
  exact h1.trans (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg M))

lemma psi_range_nonneg (M : ℕ) : 0 ≤ ∑ k ∈ range M, vonMangoldt k :=
  sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)

/-- Discrete partial summation against `ψ(x) ≤ c0 x`. -/
lemma abel_ineq (a : ℕ → ℝ) (ha : Antitone a) (ha0 : ∀ n, 0 ≤ a n) (K : ℕ) :
    ∀ M, K ≤ M → ∑ n ∈ Ico K M, vonMangoldt n * a n
      ≤ c0 * (K * a K + ∑ n ∈ Ico K M, a n) := by
  have inv : ∀ M, K ≤ M →
      (c0 * M - ∑ k ∈ range M, vonMangoldt k + ∑ k ∈ range K, vonMangoldt k) * a M
        ≤ c0 * (K * a K + ∑ n ∈ Ico K M, a n) - ∑ n ∈ Ico K M, vonMangoldt n * a n := by
    intro M hM
    induction M, hM using Nat.le_induction with
    | base =>
      simp only [Ico_self, sum_empty, add_zero, sub_zero]
      ring_nf
      exact le_refl _
    | succ M hM ih =>
      rw [sum_Ico_succ_top hM, sum_Ico_succ_top hM, sum_range_succ]
      have hcoef : 0 ≤ c0 * ((M + 1 : ℕ) : ℝ)
          - (∑ k ∈ range M, vonMangoldt k + vonMangoldt M) + ∑ k ∈ range K, vonMangoldt k := by
        have h1 := psi_range_le (M + 1)
        rw [sum_range_succ] at h1
        have h2 := psi_range_nonneg K
        linarith
      have hmono : a (M + 1) ≤ a M := ha (Nat.le_succ M)
      have step := mul_le_mul_of_nonneg_left hmono hcoef
      push_cast at step ⊢
      nlinarith [ih, step]
  intro M hM
  have h := inv M hM
  have hcoef : 0 ≤ c0 * M - ∑ k ∈ range M, vonMangoldt k + ∑ k ∈ range K, vonMangoldt k := by
    have h1 := psi_range_le M
    have h2 := psi_range_nonneg K
    linarith
  have := mul_nonneg hcoef (ha0 M)
  linarith

lemma sum_inv_le (M : ℕ) : ∑ n ∈ Ico 1 M, ((n : ℝ))⁻¹ ≤ 1 + Real.log M := by
  have h1 : ∑ n ∈ Ico 1 M, ((n : ℝ))⁻¹ ≤ ∑ n ∈ Icc 1 M, ((n : ℝ))⁻¹ := by
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [mem_Ico] at hn
      simp only [mem_Icc]
      omega
    · intro _ _ _; positivity
  have h2 : ((harmonic M : ℚ) : ℝ) = ∑ n ∈ Icc 1 M, ((n : ℝ))⁻¹ := by
    rw [harmonic_eq_sum_Icc]; push_cast; rfl
  rw [← h2] at h1
  exact h1.trans (harmonic_le_one_add_log M)

lemma sum_rpow_tail (s : ℝ) (hs : 1 < s) (K M : ℕ) (hK : 1 ≤ K) (hKM : K ≤ M) :
    ∑ n ∈ Ico (K + 1) (M + 1), (n : ℝ) ^ (-s) ≤ (K : ℝ) ^ (1 - s) / (s - 1) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc (K : ℝ) M) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (hK0.trans_le hx.1) hxy (by linarith)
  have h1 := AntitoneOn.sum_le_integral_Ico hKM hanti
  have h2 : ∑ n ∈ Ico (K + 1) (M + 1), (n : ℝ) ^ (-s)
      = ∑ i ∈ Ico K M, ((i + 1 : ℕ) : ℝ) ^ (-s) :=
    (Finset.sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ (-s)) K M 1).symm
  rw [h2]
  refine h1.trans ?_
  have hnot : (0 : ℝ) ∉ Set.uIcc (K : ℝ) M := by
    rw [Set.uIcc_of_le (by exact_mod_cast hKM)]
    intro h0
    linarith [h0.1]
  rw [integral_rpow (Or.inr ⟨by linarith, hnot⟩)]
  have hM0 : (0 : ℝ) ≤ (M : ℝ) ^ (-s + 1) := Real.rpow_nonneg (Nat.cast_nonneg M) _
  have e1 : -s + 1 = -(s - 1) := by ring
  have e2 : (1 : ℝ) - s = -s + 1 := by ring
  rw [e2, e1, div_neg, ← neg_div, neg_sub]
  rw [← e1]
  apply div_le_div_of_nonneg_right _ (by linarith)
  linarith


/-- `n ↦ n^(-s)`, patched at `n = 0` so as to be antitone. -/
noncomputable def aS (s : ℝ) (n : ℕ) : ℝ := ((max n 1 : ℕ) : ℝ) ^ (-s)

lemma aS_nonneg (s : ℝ) (n : ℕ) : 0 ≤ aS s n := Real.rpow_nonneg (Nat.cast_nonneg _) _

lemma aS_antitone (s : ℝ) (hs : 0 ≤ s) : Antitone (aS s) := by
  intro m n hmn
  unfold aS
  have h1 : (0 : ℝ) < ((max m 1 : ℕ) : ℝ) := by
    have : 1 ≤ max m 1 := le_max_right _ _
    exact_mod_cast this
  have h2 : ((max m 1 : ℕ) : ℝ) ≤ ((max n 1 : ℕ) : ℝ) := by
    exact_mod_cast max_le_max hmn (le_refl 1)
  exact Real.rpow_le_rpow_of_nonpos h1 h2 (by linarith)

lemma aS_of_pos (s : ℝ) {n : ℕ} (hn : 1 ≤ n) : aS s n = (n : ℝ) ^ (-s) := by
  unfold aS; rw [max_eq_left hn]

lemma aS_le_one (s : ℝ) (hs : 1 ≤ s) (n : ℕ) : aS s n ≤ aS 1 n := by
  unfold aS
  have h1 : (1 : ℝ) ≤ ((max n 1 : ℕ) : ℝ) := by
    have : 1 ≤ max n 1 := le_max_right _ _
    exact_mod_cast this
  exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith)

lemma tail_fin (s : ℝ) (hs : 1 < s) (K M : ℕ) (hK : 1 ≤ K) (hKM : K ≤ M) :
    ∑ n ∈ Ico K M, vonMangoldt n * aS s n ≤ c0 * ((K : ℝ) ^ (1 - s) * (2 + 1 / (s - 1))) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have h1 := abel_ineq (aS s) (aS_antitone s (by linarith)) (aS_nonneg s) K M hKM
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ c0_pos.le)
  have e1 : (K : ℝ) * aS s K = (K : ℝ) ^ (1 - s) := by
    rw [aS_of_pos s hK, sub_eq_add_neg, Real.rpow_add hK0, Real.rpow_one]
  have e2 : aS s K ≤ (K : ℝ) ^ (1 - s) := by
    rw [aS_of_pos s hK]
    exact Real.rpow_le_rpow_of_exponent_le hK1 (by linarith)
  have hpos : 0 ≤ (K : ℝ) ^ (1 - s) / (s - 1) :=
    div_nonneg (Real.rpow_nonneg hK0.le _) (by linarith)
  have e3 : ∑ n ∈ Ico K M, aS s n ≤ (K : ℝ) ^ (1 - s) + (K : ℝ) ^ (1 - s) / (s - 1) := by
    rcases Nat.eq_or_lt_of_le hKM with h | h
    · subst h
      simp only [Ico_self, sum_empty]
      have := Real.rpow_nonneg hK0.le (1 - s)
      linarith
    · obtain ⟨M', rfl⟩ : ∃ M', M = M' + 1 := ⟨M - 1, by omega⟩
      rw [sum_eq_sum_Ico_succ_bot h]
      have h4 : ∑ n ∈ Ico (K + 1) (M' + 1), aS s n = ∑ n ∈ Ico (K + 1) (M' + 1), (n : ℝ) ^ (-s) := by
        refine sum_congr rfl (fun n hn => aS_of_pos s ?_)
        have := (mem_Ico.mp hn).1
        omega
      rw [h4]
      have h5 := sum_rpow_tail s hs K M' hK (by omega)
      linarith
  rw [e1]
  have : (K : ℝ) ^ (1 - s) * (2 + 1 / (s - 1))
      = (K : ℝ) ^ (1 - s) + ((K : ℝ) ^ (1 - s) + (K : ℝ) ^ (1 - s) / (s - 1)) := by ring
  rw [this]
  linarith

lemma head_fin (K : ℕ) : ∑ n ∈ range K, vonMangoldt n * aS 1 n ≤ c0 * (2 + Real.log K) := by
  rw [← Nat.Ico_zero_eq_range]
  have h1 := abel_ineq (aS 1) (aS_antitone 1 (by norm_num)) (aS_nonneg 1) 0 K (Nat.zero_le K)
  refine h1.trans (mul_le_mul_of_nonneg_left ?_ c0_pos.le)
  rcases Nat.eq_zero_or_pos K with h | h
  · subst h; simp
  · rw [sum_eq_sum_Ico_succ_bot h]
    have h4 : ∑ n ∈ Ico (0 + 1) K, aS 1 n = ∑ n ∈ Ico 1 K, ((n : ℝ))⁻¹ := by
      refine sum_congr rfl (fun n hn => ?_)
      have := (mem_Ico.mp hn).1
      rw [aS_of_pos 1 (by omega), Real.rpow_neg_one]
    rw [h4]
    have h5 := sum_inv_le K
    have h6 : aS 1 0 = 1 := by simp [aS]
    simp only [Nat.cast_zero, zero_mul, zero_add]
    rw [h6]
    linarith


open ArithmeticFunction.vonMangoldt in
/-- The von Mangoldt function on the class `2 mod 3`. -/
noncomputable abbrev rc (n : ℕ) : ℝ := residueClass (2 : ZMod 3) n

noncomputable def gS (s : ℝ) (n : ℕ) : ℝ := rc n / (n : ℝ) ^ s

lemma rc_nonneg (n : ℕ) : 0 ≤ rc n := ArithmeticFunction.vonMangoldt.residueClass_nonneg _ n

lemma rc_le (n : ℕ) : rc n ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt.residueClass_le _ n

lemma gS_nonneg (s : ℝ) (n : ℕ) : 0 ≤ gS s n :=
  div_nonneg (rc_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) s)

lemma gS_zero (s : ℝ) : gS s 0 = 0 := by
  unfold gS rc
  rw [ArithmeticFunction.vonMangoldt.residueClass_apply_zero, zero_div]

lemma gS_le (s : ℝ) (n : ℕ) : gS s n ≤ vonMangoldt n * aS s n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [gS_zero]
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (aS_nonneg s 0)
  · rw [aS_of_pos s h, Real.rpow_neg (Nat.cast_nonneg n), gS, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (rc_le n)
      (inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) s))

lemma bound_nonneg (s : ℝ) (hs : 1 < s) (K : ℕ) :
    0 ≤ c0 * ((K : ℝ) ^ (1 - s) * (2 + 1 / (s - 1))) := by
  have h1 : 0 ≤ (K : ℝ) ^ (1 - s) := Real.rpow_nonneg (Nat.cast_nonneg K) _
  have h2 : 0 ≤ 1 / (s - 1) := by apply div_nonneg <;> linarith
  have := c0_pos
  positivity

lemma gS_sum_Ico_le (s : ℝ) (hs : 1 < s) (K M : ℕ) (hK : 1 ≤ K) :
    ∑ n ∈ Ico K M, gS s n ≤ c0 * ((K : ℝ) ^ (1 - s) * (2 + 1 / (s - 1))) := by
  rcases le_or_gt K M with h | h
  · exact (sum_le_sum (fun n _ => gS_le s n)).trans (tail_fin s hs K M hK h)
  · rw [Ico_eq_empty (by omega), sum_empty]
    exact bound_nonneg s hs K

lemma gS_summable (s : ℝ) (hs : 1 < s) : Summable (gS s) := by
  refine summable_of_sum_range_le (c := c0 * (((1 : ℕ) : ℝ) ^ (1 - s) * (2 + 1 / (s - 1))))
    (gS_nonneg s) (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h
    rw [range_zero, sum_empty]
    exact bound_nonneg s hs 1
  · rw [← Nat.Ico_zero_eq_range, sum_eq_sum_Ico_succ_bot h, gS_zero, zero_add]
    exact gS_sum_Ico_le s hs 1 n (le_refl 1)

lemma gS_tail_tsum (s : ℝ) (hs : 1 < s) (K : ℕ) (hK : 1 ≤ K) :
    ∑' i, gS s (i + K) ≤ c0 * ((K : ℝ) ^ (1 - s) * (2 + 1 / (s - 1))) := by
  refine Real.tsum_le_of_sum_range_le (fun n => gS_nonneg s _) (fun j => ?_)
  have h1 : ∑ i ∈ range j, gS s (i + K) = ∑ l ∈ Ico K (K + j), gS s l := by
    rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
    exact sum_congr rfl (fun i _ => by rw [add_comm])
  rw [h1]
  exact gS_sum_Ico_le s hs K (K + j) hK

lemma gS_head (s : ℝ) (hs : 1 ≤ s) (K : ℕ) :
    ∑ n ∈ range K, gS s n ≤ c0 * (2 + Real.log K) := by
  refine (sum_le_sum (fun n _ => ?_)).trans (head_fin K)
  exact (gS_le s n).trans
    (mul_le_mul_of_nonneg_left (aS_le_one s hs n) ArithmeticFunction.vonMangoldt_nonneg)

/-- The contribution of prime powers that are not primes. -/
noncomputable def c3 : ℝ := ∑' n : ℕ, (if n.Prime then 0 else rc n) / n

lemma rc_prime_le (n K₂ : ℕ) (hn : n < K₂) (hn1 : 1 ≤ n) :
    (if n.Prime then rc n else 0) ≤ if n.Prime ∧ n % 3 = 2 then Real.log K₂ else 0 := by
  by_cases hp : n.Prime
  · rw [if_pos hp]
    by_cases h3 : n % 3 = 2
    · rw [if_pos ⟨hp, h3⟩]
      refine (rc_le n).trans ?_
      rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
      exact Real.log_le_log (by exact_mod_cast hn1) (by exact_mod_cast hn.le)
    · rw [if_neg (fun h => h3 h.2)]
      have : rc n = 0 := by
        unfold rc ArithmeticFunction.vonMangoldt.residueClass
        apply Set.indicator_of_notMem
        intro hmem
        apply h3
        have h4 : (n : ZMod 3) = ((2 : ℕ) : ZMod 3) := by
          have : (n : ZMod 3) = 2 := hmem
          rw [this]; rfl
        exact (ZMod.natCast_eq_natCast_iff' n 2 3).mp h4
      rw [this]
  · rw [if_neg hp, if_neg (fun h => hp h.1)]

lemma gS_mid (s : ℝ) (hs : 1 ≤ s) (K₁ K₂ : ℕ) (hK₁ : 1 ≤ K₁) :
    ∑ n ∈ Ico K₁ K₂, gS s n
      ≤ (((Ico K₁ K₂).filter (fun n => n.Prime ∧ n % 3 = 2)).card : ℝ) * (Real.log K₂ / K₁)
        + c3 := by
  have hK₁0 : (0 : ℝ) < K₁ := by exact_mod_cast hK₁
  have hsum : Summable fun n : ℕ => (if n.Prime then 0 else rc n) / (n : ℝ) :=
    ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div (2 : ZMod 3)
  have hnn : ∀ n : ℕ, 0 ≤ (if n.Prime then 0 else rc n) / (n : ℝ) := by
    intro n
    apply div_nonneg _ (Nat.cast_nonneg n)
    split_ifs
    · exact le_refl _
    · exact rc_nonneg n
  have hlogK : 0 ≤ Real.log K₂ / K₁ := div_nonneg (Real.log_natCast_nonneg K₂) hK₁0.le
  have hterm : ∀ n ∈ Ico K₁ K₂, gS s n
      ≤ (if n.Prime ∧ n % 3 = 2 then Real.log K₂ / K₁ else 0)
        + (if n.Prime then 0 else rc n) / (n : ℝ) := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Ico.mp hn
    have hn1 : 1 ≤ n := hK₁.trans h1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hpow : (n : ℝ) ≤ (n : ℝ) ^ s := by
      have := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ n by exact_mod_cast hn1) hs
      rwa [Real.rpow_one] at this
    have h3 : gS s n ≤ rc n / n := div_le_div_of_nonneg_left (rc_nonneg n) hn0 hpow
    have h4 : rc n / (n : ℝ) = (if n.Prime then rc n else 0) / n
        + (if n.Prime then 0 else rc n) / n := by
      split_ifs <;> ring
    have h5 : (if n.Prime then rc n else 0) / (n : ℝ)
        ≤ if n.Prime ∧ n % 3 = 2 then Real.log K₂ / K₁ else 0 := by
      have h6 := rc_prime_le n K₂ h2 hn1
      by_cases hc : n.Prime ∧ n % 3 = 2
      · rw [if_pos hc] at h6 ⊢
        have h7 : 0 ≤ (if n.Prime then rc n else 0) := by
          split_ifs
          · exact rc_nonneg n
          · exact le_refl _
        calc (if n.Prime then rc n else 0) / (n : ℝ) ≤ Real.log K₂ / n :=
              div_le_div_of_nonneg_right h6 hn0.le
          _ ≤ Real.log K₂ / K₁ :=
              div_le_div_of_nonneg_left (Real.log_natCast_nonneg K₂) hK₁0 (by exact_mod_cast h1)
      · rw [if_neg hc] at h6 ⊢
        exact div_nonpos_of_nonpos_of_nonneg h6 hn0.le
    linarith
  calc ∑ n ∈ Ico K₁ K₂, gS s n
      ≤ ∑ n ∈ Ico K₁ K₂, ((if n.Prime ∧ n % 3 = 2 then Real.log K₂ / K₁ else 0)
          + (if n.Prime then 0 else rc n) / (n : ℝ)) := sum_le_sum hterm
    _ = ∑ n ∈ Ico K₁ K₂, (if n.Prime ∧ n % 3 = 2 then Real.log K₂ / K₁ else 0)
          + ∑ n ∈ Ico K₁ K₂, (if n.Prime then 0 else rc n) / (n : ℝ) := sum_add_distrib
    _ ≤ (((Ico K₁ K₂).filter (fun n => n.Prime ∧ n % 3 = 2)).card : ℝ) * (Real.log K₂ / K₁)
          + c3 := by
        have e1 : ∑ n ∈ Ico K₁ K₂, (if n.Prime ∧ n % 3 = 2 then Real.log K₂ / K₁ else 0)
            = (((Ico K₁ K₂).filter (fun n => n.Prime ∧ n % 3 = 2)).card : ℝ)
              * (Real.log K₂ / K₁) := by
          rw [← sum_filter, sum_const, nsmul_eq_mul]
        have e2 : ∑ n ∈ Ico K₁ K₂, (if n.Prime then 0 else rc n) / (n : ℝ) ≤ c3 :=
          hsum.sum_le_tsum _ (fun n _ => hnn n)
        linarith


/-- Splitting the Dirichlet series of the class `2 mod 3` into head, middle and tail. -/
theorem core_ineq : ∃ C : ℝ, ∀ s : ℝ, 1 < s → s ≤ 2 → ∀ K₁ K₂ : ℕ, 1 ≤ K₁ → K₁ ≤ K₂ →
    2⁻¹ / (s - 1) - C ≤ c0 * (2 + Real.log K₁)
      + (((Ico K₁ K₂).filter (fun n => n.Prime ∧ n % 3 = 2)).card : ℝ) * (Real.log K₂ / K₁)
      + c0 * ((K₂ : ℝ) ^ (1 - s) * (2 + 1 / (s - 1))) := by
  obtain ⟨C, hC⟩ := ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound
    (q := 3) (a := (2 : ZMod 3)) (by decide)
  refine ⟨C + c3, ?_⟩
  intro s hs1 hs2 K₁ K₂ hK₁ hK
  have h := hC (x := s) ⟨hs1, hs2⟩
  have htot : ((Nat.totient 3 : ℕ) : ℝ) = 2 := by
    rw [Nat.totient_prime Nat.prime_three]; norm_num
  rw [htot] at h
  have h' : 2⁻¹ / (s - 1) - C ≤ ∑' n, gS s n := h
  have hsplit : ∑ n ∈ range K₂, gS s n + ∑' i, gS s (i + K₂) = ∑' n, gS s n :=
    Summable.sum_add_tsum_nat_add' ((summable_nat_add_iff K₂).mpr (gS_summable s hs1))
  have hrange : ∑ n ∈ range K₁, gS s n + ∑ n ∈ Ico K₁ K₂, gS s n = ∑ n ∈ range K₂, gS s n :=
    sum_range_add_sum_Ico _ hK
  have h1 := gS_head s hs1.le K₁
  have h2 := gS_mid s hs1.le K₁ K₂ hK₁
  have h3 := gS_tail_tsum s hs1 K₂ (hK₁.trans hK)
  linarith

lemma c0_le : c0 ≤ 5.4 := by
  unfold c0
  have h1 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have h2 := Real.log_two_lt_d9
  rw [h1]; linarith

lemma exp_neg_five_le : Real.exp (-5) ≤ 0.01 := by
  have h1 : Real.exp 5 = Real.exp 1 ^ 5 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h2 := Real.exp_one_gt_d9
  have h3 : (100 : ℝ) ≤ Real.exp 5 := by
    rw [h1]
    have : (2.7 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) (by linarith) 5
    have h4 : (100 : ℝ) ≤ 2.7 ^ 5 := by norm_num
    linarith
  rw [Real.exp_neg]
  have hpos : (0 : ℝ) < Real.exp 5 := Real.exp_pos 5
  rw [inv_le_comm₀ hpos (by norm_num)]
  norm_num
  linarith

/-- Many primes `≡ 2 (mod 3)` in `[Λ, Λ^80)`. -/
theorem primes_mid : ∃ Λ₁ : ℕ, ∀ Λ : ℕ, Λ₁ ≤ Λ →
    Λ ≤ 160 * ((Ico Λ (Λ ^ 80)).filter (fun n => n.Prime ∧ n % 3 = 2)).card := by
  obtain ⟨C, hC⟩ := core_ineq
  set B : ℝ := max 1 (C + 11) with hB
  refine ⟨⌈Real.exp B⌉₊, ?_⟩
  intro Λ hΛ
  have hexp : Real.exp B ≤ Λ := (Nat.le_ceil _).trans (by exact_mod_cast hΛ)
  have hΛpos : (0 : ℝ) < Λ := (Real.exp_pos B).trans_le hexp
  have hΛ1 : 1 ≤ Λ := by exact_mod_cast hΛpos
  set L : ℝ := Real.log Λ with hL
  have hBL : B ≤ L := (Real.le_log_iff_exp_le hΛpos).mpr hexp
  have hL1 : 1 ≤ L := (le_max_left _ _).trans hBL
  have hLC : C + 11 ≤ L := (le_max_right _ _).trans hBL
  have hL0 : 0 < L := by linarith
  set s : ℝ := 1 + 1 / (16 * L) with hs
  have hs1 : 1 < s := by
    have : 0 < 1 / (16 * L) := by positivity
    linarith
  have hs2 : s ≤ 2 := by
    have : 1 / (16 * L) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    linarith
  have hK : Λ ≤ Λ ^ 80 := by
    calc Λ = Λ ^ 1 := (pow_one Λ).symm
      _ ≤ Λ ^ 80 := Nat.pow_le_pow_right hΛ1 (by norm_num)
  have key := hC s hs1 hs2 Λ (Λ ^ 80) hΛ1 hK
  set N : ℝ := (((Ico Λ (Λ ^ 80)).filter (fun n => n.Prime ∧ n % 3 = 2)).card : ℝ) with hN
  have e1 : s - 1 = 1 / (16 * L) := by rw [hs]; ring
  have e2 : 2⁻¹ / (s - 1) = 8 * L := by rw [e1]; field_simp; ring
  have e3 : 1 / (s - 1) = 16 * L := by rw [e1]; field_simp
  have e4 : Real.log ((Λ ^ 80 : ℕ) : ℝ) = 80 * L := by
    push_cast
    rw [Real.log_pow]; norm_num
    rfl
  have e5 : (((Λ ^ 80 : ℕ) : ℝ)) ^ (1 - s) = Real.exp (-5) := by
    have hpos : (0 : ℝ) < ((Λ ^ 80 : ℕ) : ℝ) := by positivity
    rw [Real.rpow_def_of_pos hpos, e4]
    congr 1
    have : 1 - s = -(1 / (16 * L)) := by rw [hs]; ring
    rw [this]; field_simp; ring
  rw [e2, e3, e4, e5] at key
  have hc0 := c0_le
  have hc0p := c0_pos
  have he5 := exp_neg_five_le
  have he5p : 0 < Real.exp (-5) := Real.exp_pos _
  have hA : c0 * (2 + L) ≤ 5.4 * (2 + L) := mul_le_mul_of_nonneg_right hc0 (by linarith)
  have hBb : c0 * (Real.exp (-5) * (2 + 16 * L)) ≤ 5.4 * (0.01 * (2 + 16 * L)) := by
    apply mul_le_mul hc0 _ (by positivity) (by norm_num)
    exact mul_le_mul_of_nonneg_right he5 (by linarith)
  have hmain : 0.736 * L ≤ N * (80 * L / Λ) := by linarith
  have h80 : N * (80 * L / Λ) = (80 * N / Λ) * L := by ring
  rw [h80] at hmain
  have h2 : 0.736 ≤ 80 * N / Λ := le_of_mul_le_mul_right hmain hL0
  rw [le_div_iff₀ hΛpos] at h2
  have h3 : (Λ : ℝ) ≤ 160 * N := by linarith
  rw [hN] at h3
  exact_mod_cast h3

/-- Quantitative supply of primes `≡ 2 (mod 3)` (statement `PrimesQuant` of the sieve file). -/
theorem primesQuant : ∃ n : ℕ, ∃ Λ₀ : ℕ, ∀ Λ : ℕ, Λ₀ ≤ Λ →
    Λ ≤ ((Finset.Ioc Λ (Λ ^ n)).filter (fun l => l.Prime ∧ l % 3 = 2)).card := by
  obtain ⟨Λ₁, h⟩ := primes_mid
  refine ⟨160, max Λ₁ 160, ?_⟩
  intro Λ hΛ
  have hΛ1 : Λ₁ ≤ Λ := (le_max_left _ _).trans hΛ
  have hΛ160 : 160 ≤ Λ := (le_max_right _ _).trans hΛ
  have hsq : Λ₁ ≤ Λ ^ 2 := hΛ1.trans (by nlinarith)
  have h1 := h (Λ ^ 2) hsq
  have hsub : (Ico (Λ ^ 2) ((Λ ^ 2) ^ 80)).filter (fun n => n.Prime ∧ n % 3 = 2)
      ⊆ (Finset.Ioc Λ (Λ ^ 160)).filter (fun l => l.Prime ∧ l % 3 = 2) := by
    intro l hl
    obtain ⟨h2, h3⟩ := mem_filter.mp hl
    obtain ⟨h4, h5⟩ := mem_Ico.mp h2
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_, ?_⟩, h3⟩
    · have : Λ < Λ ^ 2 := by nlinarith
      omega
    · rw [← pow_mul] at h5
      exact h5.le
  have h6 := card_le_card hsub
  have h7 : Λ * 160 ≤ Λ ^ 2 := by nlinarith
  have h8 : Λ * 160 ≤ 160 * ((Finset.Ioc Λ (Λ ^ 160)).filter
      (fun l => l.Prime ∧ l % 3 = 2)).card :=
    h7.trans (h1.trans (Nat.mul_le_mul_left 160 h6))
  omega


/-- Lemma 2 of PROOF.md, unconditional: among `X` consecutive integers `m`, at most
`(6 X + 6 Λ^(2n+1)) / Λ` have `F(m) = 9 s^2`, for every large `Λ`. -/
theorem small_bound_uncond (c : ℤ) (hc : c ≠ 0) :
    ∃ n Λ₀ : ℕ, ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ d r κ e : ℤ, c - r ^ 3 = d * κ → e ^ 2 = 1 →
      ∀ (a : ℤ) (X : ℕ) (B : Finset ℕ), B ⊆ range X →
        (∀ j ∈ B, ∃ s : ℤ, Fint d r κ e (a + j) = 9 * s ^ 2) →
        Λ * B.card ≤ 6 * X + 6 * Λ ^ (2 * n + 1) :=
  small_bound primesQuant c hc



end sieve

section meanvalue

open Polynomial NumberField



/-- The polynomial `X^3 - c` over `ℚ`. -/
noncomputable def fpoly (c : ℤ) : ℚ[X] := X ^ 3 - C (c : ℚ)

lemma fpoly_monic (c : ℤ) : (fpoly c).Monic := monic_X_pow_sub_C _ (by norm_num)

lemma fpoly_ne_zero (c : ℤ) : fpoly c ≠ 0 := (fpoly_monic c).ne_zero

lemma fpoly_irreducible (c : ℤ) (hc : ¬ ∃ m : ℤ, m ^ 3 = c) : Irreducible (fpoly c) := by
  unfold fpoly
  apply X_pow_sub_C_irreducible_of_prime Nat.prime_three
  intro b hb
  have hint : IsIntegral ℤ b := by
    refine ⟨X ^ 3 - C c, monic_X_pow_sub_C _ (by norm_num), ?_⟩
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, hb]
    simp
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  apply hc
  refine ⟨y, ?_⟩
  have : ((y ^ 3 : ℤ) : ℚ) = (c : ℚ) := by
    push_cast
    rw [← hb, ← hy]; rfl
  exact_mod_cast this

section field

variable (c : ℤ) [hirr : Fact (Irreducible (fpoly c))]

/-- The cubic field `ℚ(θ)`, `θ^3 = c`. -/
abbrev Kc := AdjoinRoot (fpoly c)

/-- The generator `θ`. -/
noncomputable def theta : Kc c := AdjoinRoot.root (fpoly c)

lemma theta_cube : (theta c) ^ 3 = (algebraMap ℚ (Kc c) (c : ℚ)) := by
  have h := AdjoinRoot.eval₂_root (fpoly c)
  unfold fpoly at h
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

lemma norm_sub_theta (a : ℚ) :
    Algebra.norm ℚ (algebraMap ℚ (Kc c) a - theta c) = a ^ 3 - c := by
  classical
  let pb := AdjoinRoot.powerBasis (fpoly_ne_zero c)
  have hgen : pb.gen = theta c := AdjoinRoot.powerBasis_gen (fpoly_ne_zero c)
  have hmin : minpoly ℚ pb.gen = fpoly c := by
    have h1 : minpoly ℚ (AdjoinRoot.root (fpoly c)) = fpoly c * C (fpoly c).leadingCoeff⁻¹ :=
      AdjoinRoot.minpoly_root (fpoly_ne_zero c)
    have h2 : fpoly c * C (fpoly c).leadingCoeff⁻¹ = fpoly c := by
      rw [(fpoly_monic c).leadingCoeff]; simp
    exact (congrArg (minpoly ℚ) hgen).trans (h1.trans h2)
  have h0 := Algebra.norm_eq_matrix_det pb.basis (algebraMap ℚ (Kc c) a - theta c)
  refine h0.trans ?_
  have h3 : Algebra.leftMulMatrix pb.basis (algebraMap ℚ (Kc c) a - theta c)
      = Matrix.scalar (Fin pb.dim) a - Algebra.leftMulMatrix pb.basis pb.gen := by
    rw [map_sub, hgen]
    congr 1
    exact AlgHom.commutes _ a
  rw [h3, ← Matrix.eval_charpoly, charpoly_leftMulMatrix]
  have h4 : eval a (fpoly c) = a ^ 3 - c := by simp [fpoly]
  exact (congrArg (eval a) hmin).trans h4

lemma theta_integral : IsIntegral ℤ (theta c) := by
  refine ⟨X ^ 3 - C c, monic_X_pow_sub_C _ (by norm_num), ?_⟩
  simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C]
  rw [theta_cube]
  simp

/-- `θ` as an algebraic integer. -/
noncomputable def thetaO : 𝓞 (Kc c) := ⟨theta c, theta_integral c⟩

lemma coe_thetaO : ((thetaO c : 𝓞 (Kc c)) : Kc c) = theta c := rfl

lemma thetaO_cube : (thetaO c) ^ 3 = (c : 𝓞 (Kc c)) := by
  apply RingOfIntegers.ext
  have h := theta_cube c
  push_cast
  change theta c ^ 3 = ((c : 𝓞 (Kc c)) : Kc c)
  rw [h]
  simp

lemma norm_int_sub (a : ℤ) :
    Algebra.norm ℤ ((a : 𝓞 (Kc c)) - thetaO c) = a ^ 3 - c := by
  have h := Algebra.coe_norm_int ((a : 𝓞 (Kc c)) - thetaO c)
  have h2 : (((a : 𝓞 (Kc c)) - thetaO c : 𝓞 (Kc c)) : Kc c)
      = algebraMap ℚ (Kc c) (a : ℚ) - theta c := by
    simp [coe_thetaO]
  rw [h2, norm_sub_theta] at h
  exact_mod_cast h

lemma finrank_Kc : Module.finrank ℚ (Kc c) = 3 := by
  have h := (AdjoinRoot.powerBasis (fpoly_ne_zero c)).finrank
  rw [AdjoinRoot.powerBasis_dim] at h
  rw [h]
  unfold fpoly
  exact natDegree_X_pow_sub_C

lemma norm_int (d : ℤ) : Algebra.norm ℤ (d : 𝓞 (Kc c)) = d ^ 3 := by
  have h := Algebra.coe_norm_int (d : 𝓞 (Kc c))
  have h2 : ((d : 𝓞 (Kc c)) : Kc c) = algebraMap ℚ (Kc c) (d : ℚ) := by simp
  rw [h2, Algebra.norm_algebraMap, finrank_Kc] at h
  exact_mod_cast h

/-- The cofactor `a^2 + a θ + θ^2` of `a - θ` in `a^3 - c`. -/
noncomputable def wO (a : ℤ) : 𝓞 (Kc c) := (a : 𝓞 (Kc c)) ^ 2 + a * thetaO c + (thetaO c) ^ 2

lemma sub_mul_wO (a : ℤ) :
    ((a : 𝓞 (Kc c)) - thetaO c) * wO c a = ((a ^ 3 - c : ℤ) : 𝓞 (Kc c)) := by
  have h := thetaO_cube c
  unfold wO
  push_cast
  linear_combination (-1 : 𝓞 (Kc c)) * h

lemma norm_wO (a : ℤ) (ha : a ^ 3 - c ≠ 0) : Algebra.norm ℤ (wO c a) = (a ^ 3 - c) ^ 2 := by
  have h := congrArg (Algebra.norm ℤ) (sub_mul_wO c a)
  rw [map_mul, norm_int_sub, norm_int] at h
  have h3 : (a ^ 3 - c) * Algebra.norm ℤ (wO c a) = (a ^ 3 - c) * (a ^ 3 - c) ^ 2 := by
    rw [h]; ring
  exact mul_left_cancel₀ ha h3

/-- The ideal `(d, r - θ)`. -/
noncomputable def Idr (d r : ℤ) : Ideal (𝓞 (Kc c)) :=
  Ideal.span {(d : 𝓞 (Kc c)), (r : 𝓞 (Kc c)) - thetaO c}

/-- The ideal `(d, r^2 + r θ + θ^2)`. -/
noncomputable def Idr' (d r : ℤ) : Ideal (𝓞 (Kc c)) :=
  Ideal.span {(d : 𝓞 (Kc c)), wO c r}

lemma absNorm_dvd_of_mem (I : Ideal (𝓞 (Kc c))) (x : 𝓞 (Kc c)) (hx : x ∈ I) :
    (Ideal.absNorm I : ℤ) ∣ Algebra.norm ℤ x := by
  have h1 : Ideal.span {x} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hx
  have h2 := Ideal.absNorm_dvd_absNorm_of_le h1
  rw [Ideal.absNorm_span_singleton] at h2
  exact Int.natCast_dvd.mpr h2

lemma d_mem_Idr (d r : ℤ) : (d : 𝓞 (Kc c)) ∈ Idr c d r :=
  Ideal.subset_span (by simp)

lemma sub_mem_Idr (d r : ℤ) : (r : 𝓞 (Kc c)) - thetaO c ∈ Idr c d r :=
  Ideal.subset_span (by simp)

/-- Upper bound: the norm of `(d, r - θ)` divides `27 c^2 d`. -/
lemma absNorm_Idr_dvd (d r k : ℤ) (hk : r ^ 3 - c = d * k) :
    (Ideal.absNorm (Idr c d r) : ℤ) ∣ 27 * c ^ 2 * d := by
  set N : ℤ := (Ideal.absNorm (Idr c d r) : ℤ) with hN
  have h1 : N ∣ d ^ 3 := by
    have := absNorm_dvd_of_mem c _ _ (d_mem_Idr c d r)
    rwa [norm_int] at this
  have h2 : N ∣ d * k := by
    have := absNorm_dvd_of_mem c _ _ (sub_mem_Idr c d r)
    rwa [norm_int_sub, hk] at this
  have h3 : N ∣ (r + d) ^ 3 - c := by
    have hmem : ((r + d : ℤ) : 𝓞 (Kc c)) - thetaO c ∈ Idr c d r := by
      have : ((r + d : ℤ) : 𝓞 (Kc c)) - thetaO c
          = ((r : 𝓞 (Kc c)) - thetaO c) + (d : 𝓞 (Kc c)) := by push_cast; ring
      rw [this]
      exact Ideal.add_mem _ (sub_mem_Idr c d r) (d_mem_Idr c d r)
    have := absNorm_dvd_of_mem c _ _ hmem
    rwa [norm_int_sub] at this
  have h4 : N ∣ d * (3 * r ^ 2 + 3 * r * d + d ^ 2) := by
    have e : d * (3 * r ^ 2 + 3 * r * d + d ^ 2) = ((r + d) ^ 3 - c) - d * k := by
      rw [← hk]; ring
    rw [e]
    exact dvd_sub h3 h2
  have hc : c = r ^ 3 - d * k := by linarith
  have key : 27 * c ^ 2 * d
      = d * (3 * r ^ 2 + 3 * r * d + d ^ 2)
          * ((3 * r ^ 2 + 3 * r * d + d ^ 2) ^ 2
            - 3 * (3 * r ^ 2 + 3 * r * d + d ^ 2) * (d * (3 * r + d)) + 3 * (d * (3 * r + d)) ^ 2)
        - d ^ 3 * (d * (3 * r + d) ^ 3 - 27 * k ^ 2) - d * k * (54 * r ^ 3 * d) := by
    rw [hc]; ring
  rw [key]
  exact dvd_sub (dvd_sub (Dvd.dvd.mul_right h4 _) (Dvd.dvd.mul_right h1 _)) (Dvd.dvd.mul_right h2 _)

lemma d_mem_Idr' (d r : ℤ) : (d : 𝓞 (Kc c)) ∈ Idr' c d r :=
  Ideal.subset_span (by simp)

lemma wO_mem_Idr' (d r : ℤ) : wO c r ∈ Idr' c d r :=
  Ideal.subset_span (by simp)

/-- The norm of `(d, r^2 + r θ + θ^2)` divides `27 c^2 d^2`. -/
lemma absNorm_Idr'_dvd (hcube : ∀ a : ℤ, a ^ 3 - c ≠ 0) (d r k : ℤ) (hk : r ^ 3 - c = d * k) :
    (Ideal.absNorm (Idr' c d r) : ℤ) ∣ 27 * c ^ 2 * d ^ 2 := by
  set N : ℤ := (Ideal.absNorm (Idr' c d r) : ℤ) with hN
  have h1 : N ∣ d ^ 3 := by
    have := absNorm_dvd_of_mem c _ _ (d_mem_Idr' c d r)
    rwa [norm_int] at this
  have h2 : N ∣ (d * k) ^ 2 := by
    have := absNorm_dvd_of_mem c _ _ (wO_mem_Idr' c d r)
    rwa [norm_wO c r (hcube r), hk] at this
  have h3 : N ∣ ((r + d) ^ 3 - c) ^ 2 := by
    have hmem : wO c (r + d) ∈ Idr' c d r := by
      have : wO c (r + d) = wO c r
          + (d : 𝓞 (Kc c)) * (2 * (r : 𝓞 (Kc c)) + d + thetaO c) := by
        unfold wO; push_cast; ring
      rw [this]
      exact Ideal.add_mem _ (wO_mem_Idr' c d r) (Ideal.mul_mem_right _ _ (d_mem_Idr' c d r))
    have := absNorm_dvd_of_mem c _ _ hmem
    rwa [norm_wO c (r + d) (hcube (r + d))] at this
  have e3 : ((r + d) ^ 3 - c) ^ 2 = d ^ 2 * (k + (3 * r ^ 2 + 3 * r * d + d ^ 2)) ^ 2 := by
    have : (r + d) ^ 3 - c = d * (k + (3 * r ^ 2 + 3 * r * d + d ^ 2)) := by
      have : (r + d) ^ 3 - c = (r ^ 3 - c) + d * (3 * r ^ 2 + 3 * r * d + d ^ 2) := by ring
      rw [this, hk]; ring
    rw [this]; ring
  rw [e3] at h3
  have hc : c = r ^ 3 - d * k := by linarith
  have key : 27 * c ^ 2 * d ^ 2
      = (d * k) ^ 2 * (3 * (3 * r ^ 2 + 3 * r * d + d ^ 2) + 2 * k)
        + d ^ 2 * (k + (3 * r ^ 2 + 3 * r * d + d ^ 2)) ^ 2
            * ((3 * r ^ 2 + 3 * r * d + d ^ 2) - 2 * k)
        + d ^ 3 * (-54 * r ^ 3 * k + 27 * d * k ^ 2 - 27 * r ^ 4 * (3 * r + d)
            - 9 * r ^ 2 * d * (3 * r + d) ^ 2 - d ^ 2 * (3 * r + d) ^ 3) := by
    rw [hc]; ring
  rw [key]
  exact dvd_add (dvd_add (Dvd.dvd.mul_right h2 _) (Dvd.dvd.mul_right h3 _)) (Dvd.dvd.mul_right h1 _)

lemma Idr_mul_Idr'_le (d r k : ℤ) (hk : r ^ 3 - c = d * k) :
    Idr c d r * Idr' c d r ≤ Ideal.span {(d : 𝓞 (Kc c))} := by
  rw [Ideal.mul_le]
  intro x hx y hy
  obtain ⟨a, b, rfl⟩ := Ideal.mem_span_pair.mp hx
  obtain ⟨a', b', rfl⟩ := Ideal.mem_span_pair.mp hy
  rw [Ideal.mem_span_singleton]
  have hxw : ((r : 𝓞 (Kc c)) - thetaO c) * wO c r = (d : 𝓞 (Kc c)) * (k : 𝓞 (Kc c)) := by
    rw [sub_mul_wO, hk]; push_cast; ring
  refine ⟨a * a' * d + a * b' * wO c r + b * a' * ((r : 𝓞 (Kc c)) - thetaO c) + b * b' * k, ?_⟩
  linear_combination (b * b') * hxw

/-- Lower bound: `d` divides `27 c^2` times the norm of `(d, r - θ)`. -/
lemma dvd_absNorm_Idr (hcube : ∀ a : ℤ, a ^ 3 - c ≠ 0) (d r k : ℤ) (hd : d ≠ 0)
    (hk : r ^ 3 - c = d * k) :
    d ∣ 27 * c ^ 2 * (Ideal.absNorm (Idr c d r) : ℤ) := by
  have h1 := Ideal.absNorm_dvd_absNorm_of_le (Idr_mul_Idr'_le c d r k hk)
  rw [map_mul, Ideal.absNorm_span_singleton, norm_int] at h1
  have h2 : d ^ 3 ∣ (Ideal.absNorm (Idr c d r) : ℤ) * (Ideal.absNorm (Idr' c d r) : ℤ) := by
    have h3 : ((d ^ 3).natAbs : ℤ) ∣ ((Ideal.absNorm (Idr c d r) * Ideal.absNorm (Idr' c d r) : ℕ) : ℤ) :=
      Int.natCast_dvd_natCast.mpr h1
    rw [Int.natCast_natAbs, abs_dvd] at h3
    exact_mod_cast h3
  have h4 := absNorm_Idr'_dvd c hcube d r k hk
  have h5 : d ^ 3 ∣ (Ideal.absNorm (Idr c d r) : ℤ) * (27 * c ^ 2 * d ^ 2) :=
    h2.trans (mul_dvd_mul_left _ h4)
  have h6 : d ^ 2 * d ∣ d ^ 2 * (27 * c ^ 2 * (Ideal.absNorm (Idr c d r) : ℤ)) := by
    have e1 : d ^ 2 * d = d ^ 3 := by ring
    have e2 : d ^ 2 * (27 * c ^ 2 * (Ideal.absNorm (Idr c d r) : ℤ))
        = (Ideal.absNorm (Idr c d r) : ℤ) * (27 * c ^ 2 * d ^ 2) := by ring
    rw [e1, e2]; exact h5
  exact (mul_dvd_mul_iff_left (pow_ne_zero 2 hd)).mp h6

/-- The least positive integer lying in `I` (zero if there is none). -/
noncomputable def nzero (I : Ideal (𝓞 (Kc c))) : ℕ :=
  sInf {n : ℕ | 0 < n ∧ ((n : ℤ) : 𝓞 (Kc c)) ∈ I}

lemma nzero_spec (I : Ideal (𝓞 (Kc c))) (h : ∃ n : ℕ, 0 < n ∧ ((n : ℤ) : 𝓞 (Kc c)) ∈ I) :
    0 < nzero c I ∧ ((nzero c I : ℤ) : 𝓞 (Kc c)) ∈ I :=
  Nat.sInf_mem (s := {n : ℕ | 0 < n ∧ ((n : ℤ) : 𝓞 (Kc c)) ∈ I}) h

lemma nzero_dvd (I : Ideal (𝓞 (Kc c))) (h : ∃ n : ℕ, 0 < n ∧ ((n : ℤ) : 𝓞 (Kc c)) ∈ I)
    (m : ℤ) (hm : (m : 𝓞 (Kc c)) ∈ I) : (nzero c I : ℤ) ∣ m := by
  obtain ⟨hpos, hmem⟩ := nzero_spec c I h
  set n := nzero c I with hn
  have hn0 : (0 : ℤ) < n := by exact_mod_cast hpos
  by_contra hnd
  have hs0 : m % (n : ℤ) ≠ 0 := fun h0 => hnd (Int.dvd_of_emod_eq_zero h0)
  have hs1 : 0 ≤ m % (n : ℤ) := Int.emod_nonneg _ hn0.ne'
  have hs2 : m % (n : ℤ) < n := Int.emod_lt_of_pos _ hn0
  have hsmem : ((m % (n : ℤ) : ℤ) : 𝓞 (Kc c)) ∈ I := by
    have e : m % (n : ℤ) = m - n * (m / n) := Int.emod_def m n
    rw [e]
    push_cast
    exact Ideal.sub_mem _ hm (Ideal.mul_mem_right _ _ hmem)
  have hle : n ≤ (m % (n : ℤ)).toNat := by
    apply Nat.sInf_le
    refine ⟨?_, ?_⟩
    · have : 0 < m % (n : ℤ) := lt_of_le_of_ne hs1 (Ne.symm hs0)
      omega
    · rw [Int.toNat_of_nonneg hs1]; exact hsmem
  omega

/-- The constant `27 c^2`. -/
def Mc : ℕ := 27 * c.natAbs ^ 2

omit hirr in
lemma Mc_cast : ((Mc c : ℕ) : ℤ) = 27 * c ^ 2 := by
  unfold Mc; push_cast; rw [sq_abs]

/-- All the facts about the ideal attached to a pair `(d, r)` with `d | r^3 - c`. -/
lemma pair_facts (hcube : ∀ a : ℤ, a ^ 3 - c ≠ 0) (d r : ℕ) (hd : 0 < d)
    (hdiv : (d : ℤ) ∣ (r : ℤ) ^ 3 - c) :
    Ideal.absNorm (Idr c d r) ∣ Mc c * d ∧ d ∣ Mc c * Ideal.absNorm (Idr c d r)
      ∧ 0 < Ideal.absNorm (Idr c d r) ∧ 0 < nzero c (Idr c d r)
      ∧ ((nzero c (Idr c d r) : ℤ) : 𝓞 (Kc c)) ∈ Idr c d r
      ∧ d ≤ Mc c * (Mc c * nzero c (Idr c d r)) := by
  have hc0 : c ≠ 0 := by
    intro h0
    apply hcube 0
    rw [h0]; ring
  have hM : 0 < Mc c := by
    unfold Mc
    have := Int.natAbs_pos.mpr hc0
    positivity
  obtain ⟨k, hk⟩ := hdiv
  have h1 : Ideal.absNorm (Idr c d r) ∣ Mc c * d := by
    have := absNorm_Idr_dvd c (d : ℤ) (r : ℤ) k hk
    rw [← Mc_cast] at this
    exact_mod_cast this
  have h2 : d ∣ Mc c * Ideal.absNorm (Idr c d r) := by
    have := dvd_absNorm_Idr c hcube (d : ℤ) (r : ℤ) k (by exact_mod_cast hd.ne') hk
    rw [← Mc_cast] at this
    exact_mod_cast this
  have h3 : 0 < Ideal.absNorm (Idr c d r) := by
    rcases Nat.eq_zero_or_pos (Ideal.absNorm (Idr c d r)) with h0 | h0
    · rw [h0, zero_dvd_iff] at h1
      have : 0 < Mc c * d := Nat.mul_pos hM hd
      omega
    · exact h0
  have hne : ∃ n : ℕ, 0 < n ∧ ((n : ℤ) : 𝓞 (Kc c)) ∈ Idr c d r :=
    ⟨d, hd, d_mem_Idr c d r⟩
  obtain ⟨h4, h5⟩ := nzero_spec c _ hne
  set n₀ := nzero c (Idr c d r) with hn₀
  have h6 : (n₀ : ℤ) ∣ (d : ℤ) := nzero_dvd c _ hne d (d_mem_Idr c d r)
  have heq : Idr c (n₀ : ℤ) (r : ℤ) = Idr c (d : ℤ) (r : ℤ) := by
    apply le_antisymm
    · unfold Idr
      rw [Ideal.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · exact h5
      · exact sub_mem_Idr c d r
    · unfold Idr
      rw [Ideal.span_le]
      intro x hx
      rcases hx with rfl | rfl
      · obtain ⟨q, hq⟩ := h6
        rw [hq]
        push_cast
        exact Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))
      · exact Ideal.subset_span (by simp)
  have h7 : Ideal.absNorm (Idr c d r) ∣ Mc c * n₀ := by
    obtain ⟨q, hq⟩ := h6
    have hk' : (r : ℤ) ^ 3 - c = (n₀ : ℤ) * (q * k) := by rw [hk, hq]; ring
    have := absNorm_Idr_dvd c (n₀ : ℤ) (r : ℤ) (q * k) hk'
    rw [heq, ← Mc_cast] at this
    exact_mod_cast this
  have h8 : d ∣ Mc c * (Mc c * n₀) := h2.trans (Nat.mul_dvd_mul_left _ h7)
  exact ⟨h1, h2, h3, h4, h5, Nat.le_of_dvd (by positivity) h8⟩

/-- The encoding of a pair `(d, r)` by its ideal and two bounded integers. -/
noncomputable def Phi (p : ℕ × ℕ) : Ideal (𝓞 (Kc c)) × ℕ × ℕ :=
  (Idr c p.1 p.2, Mc c * Ideal.absNorm (Idr c p.1 p.2) / p.1, p.2 / nzero c (Idr c p.1 p.2))

open Classical in
/-- Pairs `(d, r)` with `1 ≤ d ≤ y`, `r < d` and `d ∣ r^3 - c`. -/
noncomputable def Spairs (c : ℤ) (y : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 y) ×ˢ (Finset.range y)).filter
    (fun p => p.2 < p.1 ∧ (p.1 : ℤ) ∣ (p.2 : ℤ) ^ 3 - c)

omit hirr in
lemma mem_Spairs (y : ℕ) (p : ℕ × ℕ) (hp : p ∈ Spairs c y) :
    0 < p.1 ∧ p.1 ≤ y ∧ p.2 < p.1 ∧ (p.1 : ℤ) ∣ (p.2 : ℤ) ^ 3 - c := by
  classical
  unfold Spairs at hp
  obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hp
  obtain ⟨h4, _⟩ := Finset.mem_product.mp h1
  obtain ⟨h5, h6⟩ := Finset.mem_Icc.mp h4
  exact ⟨by omega, h6, h2, h3⟩

omit hirr in
lemma Mc_pos (hcube : ∀ a : ℤ, a ^ 3 - c ≠ 0) : 0 < Mc c := by
  have hc0 : c ≠ 0 := by
    intro h0
    apply hcube 0
    rw [h0]; ring
  unfold Mc
  have := Int.natAbs_pos.mpr hc0
  positivity

theorem card_Spairs_le (hcube : ∀ a : ℤ, a ^ 3 - c ≠ 0) (y : ℕ) :
    (Spairs c y).card
      ≤ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 (Kc c)) (Mc c * y)).toFinset.card
        * ((Mc c * Mc c + 1) * (Mc c * Mc c + 1)) := by
  classical
  have hM := Mc_pos c hcube
  set T := (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 (Kc c)) (Mc c * y)).toFinset
    ×ˢ (Finset.range (Mc c * Mc c + 1) ×ˢ Finset.range (Mc c * Mc c + 1)) with hT
  have hcard : T.card = (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 (Kc c)) (Mc c * y)).toFinset.card
      * ((Mc c * Mc c + 1) * (Mc c * Mc c + 1)) := by
    rw [hT, Finset.card_product, Finset.card_product, Finset.card_range]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn (Phi c)
  · intro p hp
    obtain ⟨hd, hdy, hr, hdiv⟩ := mem_Spairs c y p hp
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pair_facts c hcube p.1 p.2 hd hdiv
    have hNle : Ideal.absNorm (Idr c p.1 p.2) ≤ Mc c * p.1 :=
      Nat.le_of_dvd (Nat.mul_pos hM hd) h1
    refine Finset.mem_product.mpr ⟨?_, Finset.mem_product.mpr ⟨?_, ?_⟩⟩
    · rw [Set.Finite.mem_toFinset]
      exact hNle.trans (Nat.mul_le_mul_left _ hdy)
    · rw [Finset.mem_range]
      apply Nat.lt_succ_of_le
      apply Nat.div_le_of_le_mul
      calc Mc c * Ideal.absNorm (Idr c p.1 p.2) ≤ Mc c * (Mc c * p.1) :=
            Nat.mul_le_mul_left _ hNle
        _ = p.1 * (Mc c * Mc c) := by ring
    · rw [Finset.mem_range]
      apply Nat.lt_succ_of_le
      apply Nat.div_le_of_le_mul
      calc p.2 ≤ p.1 := hr.le
        _ ≤ Mc c * (Mc c * nzero c (Idr c p.1 p.2)) := h6
        _ = nzero c (Idr c p.1 p.2) * (Mc c * Mc c) := by ring
  · intro p hp p' hp' heq
    obtain ⟨hd, hdy, hr, hdiv⟩ := mem_Spairs c y p hp
    obtain ⟨hd', hdy', hr', hdiv'⟩ := mem_Spairs c y p' hp'
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := pair_facts c hcube p.1 p.2 hd hdiv
    obtain ⟨h1', h2', h3', h4', h5', h6'⟩ := pair_facts c hcube p'.1 p'.2 hd' hdiv'
    have hI : Idr c (p.1 : ℤ) (p.2 : ℤ) = Idr c (p'.1 : ℤ) (p'.2 : ℤ) := congrArg Prod.fst heq
    have hq : Mc c * Ideal.absNorm (Idr c p.1 p.2) / p.1
        = Mc c * Ideal.absNorm (Idr c p'.1 p'.2) / p'.1 := congrArg (fun z => z.2.1) heq
    have ht : p.2 / nzero c (Idr c p.1 p.2) = p'.2 / nzero c (Idr c p'.1 p'.2) :=
      congrArg (fun z => z.2.2) heq
    rw [← hI] at hq ht h2' h5'
    set A := Mc c * Ideal.absNorm (Idr c p.1 p.2) with hA
    have hApos : 0 < A := Nat.mul_pos hM h3
    have e1 : p.1 * (A / p.1) = A := Nat.mul_div_cancel' h2
    have e2 : p'.1 * (A / p'.1) = A := Nat.mul_div_cancel' h2'
    have hqpos : 0 < A / p.1 := Nat.div_pos (Nat.le_of_dvd hApos h2) hd
    have hdd : p.1 = p'.1 := by
      rw [← hq] at e2
      exact Nat.eq_of_mul_eq_mul_right hqpos (e1.trans e2.symm)
    have hne : ∃ n : ℕ, 0 < n ∧ ((n : ℤ) : 𝓞 (Kc c)) ∈ Idr c (p.1 : ℤ) (p.2 : ℤ) :=
      ⟨p.1, hd, d_mem_Idr c p.1 p.2⟩
    have hmem1 := sub_mem_Idr c (p.1 : ℤ) (p.2 : ℤ)
    have hmem2 := sub_mem_Idr c (p'.1 : ℤ) (p'.2 : ℤ)
    rw [← hI] at hmem2
    have hdiff : (((p'.2 : ℤ) - (p.2 : ℤ) : ℤ) : 𝓞 (Kc c)) ∈ Idr c (p.1 : ℤ) (p.2 : ℤ) := by
      have : (((p'.2 : ℤ) - (p.2 : ℤ) : ℤ) : 𝓞 (Kc c))
          = (((p'.2 : ℤ) : 𝓞 (Kc c)) - thetaO c) - (((p.2 : ℤ) : 𝓞 (Kc c)) - thetaO c) := by
        push_cast; ring
      rw [this]
      exact Ideal.sub_mem _ hmem2 hmem1
    have hdvd := nzero_dvd c _ hne _ hdiff
    have hmod : p.2 % nzero c (Idr c p.1 p.2) = p'.2 % nzero c (Idr c p.1 p.2) :=
      (Nat.modEq_iff_dvd.mpr hdvd)
    have hrr : p.2 = p'.2 := by
      calc p.2 = nzero c (Idr c p.1 p.2) * (p.2 / nzero c (Idr c p.1 p.2))
            + p.2 % nzero c (Idr c p.1 p.2) := (Nat.div_add_mod _ _).symm
        _ = nzero c (Idr c p.1 p.2) * (p'.2 / nzero c (Idr c p.1 p.2))
            + p'.2 % nzero c (Idr c p.1 p.2) := by rw [ht, hmod]
        _ = p'.2 := Nat.div_add_mod _ _
    exact Prod.ext hdd hrr

end field

/-- Ideals of bounded norm are at most linearly many (from Mathlib's asymptotic count). -/
lemma ideal_count_le (K : Type*) [Field K] [NumberField K] :
    ∃ C : ℝ, ∀ y : ℕ, 1 ≤ y →
      ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) y).toFinset.card : ℝ) ≤ C * y := by
  have h := NumberField.Ideal.tendsto_norm_le_div_atTop K
  set κ : ℝ := (2 ^ InfinitePlace.nrRealPlaces K * (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K
    * Units.regulator K * classNumber K) / (Units.torsionOrder K * Real.sqrt |(discr K : ℝ)|) with hκ
  have hev := h.eventually_lt_const (lt_add_one _)
  obtain ⟨s₀, hs₀⟩ := Filter.eventually_atTop.mp hev
  set Y₀ : ℕ := max 1 ⌈s₀⌉₊ with hY₀
  have hY1 : 1 ≤ Y₀ := le_max_left _ _
  have key : ∀ y : ℕ, Y₀ ≤ y →
      ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) y).toFinset.card : ℝ) ≤ (κ + 1) * y := by
    intro y hy
    have hy1 : 1 ≤ y := hY1.trans hy
    have hy0 : (0 : ℝ) < y := by exact_mod_cast hy1
    have hs : s₀ ≤ (y : ℝ) :=
      (Nat.le_ceil s₀).trans (by exact_mod_cast (le_max_right 1 ⌈s₀⌉₊).trans hy)
    have h1 := hs₀ (y : ℝ) hs
    have e : (Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ (y : ℝ)} : ℝ)
        = ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) y).toFinset.card : ℝ) := by
      congr 1
      have e1 : {I : Ideal (𝓞 K) | (Ideal.absNorm I : ℝ) ≤ (y : ℝ)}
          = {I : Ideal (𝓞 K) | Ideal.absNorm I ≤ y} := by
        ext I
        simp only [Set.mem_ofPred_eq, Nat.cast_le]
      have e2 : Nat.card {I : Ideal (𝓞 K) // (Ideal.absNorm I : ℝ) ≤ (y : ℝ)}
          = Set.ncard {I : Ideal (𝓞 K) | (Ideal.absNorm I : ℝ) ≤ (y : ℝ)} :=
        Nat.card_coe_set_eq _
      rw [e2, e1, Set.ncard_eq_toFinset_card _ (Ideal.finite_setOfPred_absNorm_le y)]
    rw [e] at h1
    rw [div_lt_iff₀ hy0] at h1
    exact h1.le
  refine ⟨(|κ| + 1) * Y₀, ?_⟩
  intro y hy
  have hy0 : (0 : ℝ) < y := by exact_mod_cast hy
  have hY0 : (1 : ℝ) ≤ Y₀ := by exact_mod_cast hY1
  have hk : κ + 1 ≤ |κ| + 1 := by linarith [le_abs_self κ]
  have hkpos : 0 ≤ |κ| + 1 := by positivity
  rcases le_or_gt Y₀ y with h1 | h1
  · calc ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) y).toFinset.card : ℝ)
        ≤ (κ + 1) * y := key y h1
      _ ≤ (|κ| + 1) * y := mul_le_mul_of_nonneg_right hk hy0.le
      _ = (|κ| + 1) * 1 * y := by ring
      _ ≤ (|κ| + 1) * Y₀ * y := by gcongr
  · have hsub : (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) y).toFinset
        ⊆ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) Y₀).toFinset := by
      intro I hI
      rw [Set.Finite.mem_toFinset] at hI ⊢
      exact le_trans hI h1.le
    calc ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) y).toFinset.card : ℝ)
        ≤ ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) Y₀).toFinset.card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ (κ + 1) * Y₀ := key Y₀ (le_refl _)
      _ ≤ (|κ| + 1) * Y₀ := mul_le_mul_of_nonneg_right hk (by positivity)
      _ = (|κ| + 1) * Y₀ * 1 := by ring
      _ ≤ (|κ| + 1) * Y₀ * y := by
          have : (1 : ℝ) ≤ y := by exact_mod_cast hy
          gcongr

/-- (MV): the number of pairs `(d, r)` with `d ≤ y`, `r < d`, `d ∣ r^3 - c` is `O(y)`. -/
theorem MV (c : ℤ) (hc : ¬ ∃ m : ℤ, m ^ 3 = c) :
    ∃ C : ℝ, ∀ y : ℕ, ((Spairs c y).card : ℝ) ≤ C * y := by
  have : Fact (Irreducible (fpoly c)) := ⟨fpoly_irreducible c hc⟩
  have hcube : ∀ a : ℤ, a ^ 3 - c ≠ 0 := fun a h => hc ⟨a, by linarith⟩
  obtain ⟨C, hC⟩ := ideal_count_le (Kc c)
  refine ⟨C * Mc c * ((Mc c * Mc c + 1) * (Mc c * Mc c + 1)), fun y => ?_⟩
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · simp [Spairs]
  · have h1 := card_Spairs_le c hcube y
    have h2 := hC (Mc c * y) (Nat.mul_pos (Mc_pos c hcube) hy)
    have h3 : ((Spairs c y).card : ℝ)
        ≤ ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 (Kc c)) (Mc c * y)).toFinset.card : ℝ)
          * (((Mc c * Mc c + 1) * (Mc c * Mc c + 1) : ℕ) : ℝ) := by exact_mod_cast h1
    refine h3.trans ?_
    calc ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 (Kc c)) (Mc c * y)).toFinset.card : ℝ)
          * (((Mc c * Mc c + 1) * (Mc c * Mc c + 1) : ℕ) : ℝ)
        ≤ (C * ((Mc c * y : ℕ) : ℝ)) * (((Mc c * Mc c + 1) * (Mc c * Mc c + 1) : ℕ) : ℝ) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = C * Mc c * (((Mc c * Mc c + 1) * (Mc c * Mc c + 1) : ℕ) : ℝ) * y := by
          push_cast; ring
      _ = C * Mc c * ((Mc c * Mc c + 1) * (Mc c * Mc c + 1)) * y := by push_cast; ring



end meanvalue

section smallrange

open Finset

open Classical in
/-- Shifts `t ∈ [-T, T]` that are bad through a divisor `d ≤ D`. -/
noncomputable def SmallBad (c : ℤ) (T D : ℕ) : Finset ℤ :=
  (Finset.Icc (-(T : ℤ)) T).filter (fun t => ∃ d s : ℤ, 1 ≤ d ∧ d ≤ D ∧ d ∣ c - t ^ 3
    ∧ 4 * |c - t ^ 3| = d * (d ^ 2 + 3 * s ^ 2))

/-- `κ = (c - r^3) / d` for a pair `p = (d, r)`. -/
def kap (c : ℤ) (p : ℕ × ℕ) : ℤ := (c - (p.2 : ℤ) ^ 3) / (p.1 : ℤ)

/-- First value of `m` to consider for the pair `p`. -/
def aT (T : ℕ) (p : ℕ × ℕ) : ℤ := -((T / p.1 : ℕ) : ℤ) - 1

/-- Number of values of `m` to consider for the pair `p`. -/
def XT (T : ℕ) (p : ℕ × ℕ) : ℕ := 2 * (T / p.1) + 2

open Classical in
/-- The indices `j < X` at which `F` is nine times a square. -/
noncomputable def Bset (c : ℤ) (T : ℕ) (p : ℕ × ℕ) (e : ℤ) : Finset ℕ :=
  (range (XT T p)).filter (fun j => ∃ s : ℤ,
    Fint (p.1 : ℤ) (p.2 : ℤ) (kap c p) e (aT T p + j) = 9 * s ^ 2)

noncomputable def bT (c : ℤ) (T : ℕ) (p : ℕ × ℕ) : ℕ :=
  (Bset c T p 1).card + (Bset c T p (-1)).card

/-- The shift attached to the pair `p` and the index `j`. -/
def gT (T : ℕ) (p : ℕ × ℕ) (j : ℕ) : ℤ := (p.2 : ℤ) + (p.1 : ℤ) * (aT T p + j)

/-- Every bad shift with a divisor `d ≤ D` comes from a pair `(d, r)`, a sign and an index. -/
lemma smallBad_subset (c : ℤ) (T D : ℕ) :
    SmallBad c T D ⊆ (Spairs c D).biUnion (fun p =>
      (Bset c T p 1).image (gT T p) ∪ (Bset c T p (-1)).image (gT T p)) := by
  classical
  intro t ht
  unfold SmallBad at ht
  obtain ⟨hIcc, d, s, hd1, hdD, hdvd, heq⟩ := mem_filter.mp ht
  obtain ⟨htl, htu⟩ := mem_Icc.mp hIcc
  have hd0 : (0 : ℤ) < d := by linarith
  set dn : ℕ := d.toNat with hdn
  have hdn' : (dn : ℤ) = d := Int.toNat_of_nonneg hd0.le
  have hr0 : 0 ≤ t % d := Int.emod_nonneg t hd0.ne'
  have hr1 : t % d < d := Int.emod_lt_of_pos t hd0
  set r : ℕ := (t % d).toNat with hr
  have hr' : (r : ℤ) = t % d := Int.toNat_of_nonneg hr0
  set m : ℤ := t / d with hm
  have htrm : t = (r : ℤ) + d * m := by
    rw [hr', hm]; exact (Int.emod_add_mul_ediv t d).symm
  have hdn_pos : 0 < dn := by
    have : (0 : ℤ) < (dn : ℤ) := by rw [hdn']; exact hd0
    exact_mod_cast this
  have hdnD : dn ≤ D := by
    have : (dn : ℤ) ≤ (D : ℤ) := by rw [hdn']; exact hdD
    exact_mod_cast this
  have hrdn : r < dn := by
    have : (r : ℤ) < (dn : ℤ) := by rw [hr', hdn']; exact hr1
    exact_mod_cast this
  have hdvd2 : d ∣ (r : ℤ) ^ 3 - c := by
    have e1 : (r : ℤ) ^ 3 - c = -(c - t ^ 3) - d * (m * (t ^ 2 + t * r + (r : ℤ) ^ 2)) := by
      rw [htrm]; ring
    rw [e1]
    exact dvd_sub (dvd_neg.mpr hdvd) (dvd_mul_right _ _)
  set p : ℕ × ℕ := (dn, r) with hp
  have hpS : p ∈ Spairs c D := by
    unfold Spairs
    refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨hdn_pos, hdnD⟩, mem_range.mpr (show r < D from lt_of_lt_of_le hrdn hdnD)⟩,
      hrdn, ?_⟩
    show ((dn : ℕ) : ℤ) ∣ ((r : ℕ) : ℤ) ^ 3 - c
    rw [hdn']; exact hdvd2
  -- the quotient `q = T / d` and the bounds on `m`
  set q : ℕ := T / dn with hq
  have hq1 : d * (q : ℤ) ≤ T := by
    have : dn * q ≤ T := Nat.mul_div_le T dn
    rw [← hdn']; exact_mod_cast this
  have hq2 : (T : ℤ) < d * ((q : ℤ) + 1) := by
    have : T < dn * (q + 1) := Nat.lt_mul_div_succ T hdn_pos
    rw [← hdn']; exact_mod_cast this
  have hm1 : d * m ≤ t := by
    have := Int.ediv_mul_le t hd0.ne'
    rw [hm]; linarith [mul_comm (t / d) d]
  have hm2 : t < d * (m + 1) := by
    have := Int.lt_ediv_add_one_mul_self t hd0
    rw [hm]; linarith [mul_comm (t / d + 1) d]
  have hmq : m ≤ q := by
    by_contra h
    rw [not_le] at h
    have h1 : (q : ℤ) + 1 ≤ m := h
    have := mul_le_mul_of_nonneg_left h1 hd0.le
    linarith
  have hmq' : -(q : ℤ) - 1 ≤ m := by
    by_contra h
    rw [not_le] at h
    have h1 : m + 1 ≤ -(q : ℤ) - 1 := by linarith
    have := mul_le_mul_of_nonneg_left h1 hd0.le
    nlinarith
  have haT : aT T p = -(q : ℤ) - 1 := rfl
  have hXT : XT T p = 2 * q + 2 := rfl
  set j : ℕ := (m - aT T p).toNat with hj
  have hj' : (j : ℤ) = m - aT T p := Int.toNat_of_nonneg (by rw [haT]; linarith)
  have hjX : j < XT T p := by
    have : (j : ℤ) < ((XT T p : ℕ) : ℤ) := by
      rw [hj', haT, hXT]; push_cast; linarith
    exact_mod_cast this
  have hgt : gT T p j = t := by
    unfold gT
    rw [hj']
    show ((r : ℕ) : ℤ) + ((dn : ℕ) : ℤ) * (aT T p + (m - aT T p)) = t
    rw [hdn', htrm]; ring
  -- the value of `F`
  have hκ : kap c p * d = c - (r : ℤ) ^ 3 := by
    unfold kap
    show (c - ((r : ℕ) : ℤ) ^ 3) / ((dn : ℕ) : ℤ) * d = c - (r : ℤ) ^ 3
    rw [hdn']
    exact Int.ediv_mul_cancel (by
      have := dvd_neg.mpr hdvd2
      rwa [neg_sub] at this)
  have hF : ∀ e : ℤ, 4 * (e * (c - t ^ 3)) = d * (d ^ 2 + 3 * s ^ 2) →
      Fint (p.1 : ℤ) (p.2 : ℤ) (kap c p) e (aT T p + j) = 9 * s ^ 2 := by
    intro e he
    have hmm : aT T p + (j : ℤ) = m := by rw [hj']; ring
    rw [hmm]
    show Fint ((dn : ℕ) : ℤ) ((r : ℕ) : ℤ) (kap c p) e m = 9 * s ^ 2
    rw [hdn']
    unfold Fint
    set u : ℤ := kap c p - 3 * (r : ℤ) ^ 2 * m - 3 * (r : ℤ) * d * m ^ 2 - d ^ 2 * m ^ 3 with hu
    have hdu : d * u = c - t ^ 3 := by
      rw [hu, htrm]
      linear_combination hκ
    have h1 : d * (4 * e * u) = d * (d ^ 2 + 3 * s ^ 2) := by
      rw [← he, ← hdu]; ring
    have h2 := mul_left_cancel₀ hd0.ne' h1
    linear_combination 3 * h2
  refine mem_biUnion.mpr ⟨p, hpS, ?_⟩
  by_cases hpos : 0 < c - t ^ 3
  · refine mem_union_left _ (mem_image.mpr ⟨j, ?_, hgt⟩)
    unfold Bset
    refine mem_filter.mpr ⟨mem_range.mpr hjX, s, hF 1 ?_⟩
    rw [one_mul, ← heq, abs_of_pos hpos]
  · refine mem_union_right _ (mem_image.mpr ⟨j, ?_, hgt⟩)
    unfold Bset
    refine mem_filter.mpr ⟨mem_range.mpr hjX, s, hF (-1) ?_⟩
    rw [not_lt] at hpos
    rw [← heq, abs_of_nonpos hpos]; ring

lemma smallBad_card_le (c : ℤ) (T D : ℕ) :
    (SmallBad c T D).card ≤ ∑ p ∈ Spairs c D, bT c T p := by
  classical
  refine (card_le_card (smallBad_subset c T D)).trans ?_
  refine card_biUnion_le.trans (sum_le_sum (fun p _ => ?_))
  refine (card_union_le _ _).trans ?_
  unfold bT
  exact Nat.add_le_add card_image_le card_image_le

end smallrange


section smallrange2

open Finset

lemma Spairs_zero (c : ℤ) : Spairs c 0 = ∅ := by
  classical
  simp [Spairs]

/-- Filtering `Spairs c y` by `d ≤ y'` gives `Spairs c y'`. -/
lemma Spairs_filter (c : ℤ) (y y' : ℕ) (h : y' ≤ y) :
    (Spairs c y).filter (fun p => p.1 ≤ y') = Spairs c y' := by
  classical
  ext p
  unfold Spairs
  simp only [mem_filter, mem_product, mem_Icc, mem_range]
  constructor
  · rintro ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩, h6⟩
    exact ⟨⟨⟨h1, h6⟩, by omega⟩, h4, h5⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4, h5⟩
    exact ⟨⟨⟨⟨h1, by omega⟩, by omega⟩, h4, h5⟩, h2⟩

/-- Small divisors: for every `k` there is `A` such that the shifts that are bad through a
divisor `d ≤ T / A` number at most `T / k`. -/
theorem small_range (c : ℤ) (hc : ¬ ∃ m : ℤ, m ^ 3 = c) (k : ℕ) :
    ∃ A : ℕ, 0 < A ∧ ∀ T : ℕ, k * (SmallBad c T (T / A)).card ≤ T := by
  classical
  have hc0 : c ≠ 0 := by
    intro h0
    exact hc ⟨0, by rw [h0]; ring⟩
  obtain ⟨n, Λ₀, hsb⟩ := small_bound_uncond c hc0
  obtain ⟨C, hC⟩ := MV c hc
  set Cn : ℕ := ⌈C⌉₊ with hCn
  have hcard : ∀ y : ℕ, (Spairs c y).card ≤ Cn * y := by
    intro y
    have h1 := hC y
    have h2 : C * (y : ℝ) ≤ (Cn : ℝ) * y :=
      mul_le_mul_of_nonneg_right (Nat.le_ceil C) (Nat.cast_nonneg y)
    have h3 : ((Spairs c y).card : ℝ) ≤ ((Cn * y : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast h3
  set q : ℕ := 2 * n + 1 with hq
  set K : ℕ := 36 * 2 ^ q * Cn with hK
  -- bound for one pair and one sign
  have hpair : ∀ (T y : ℕ) (p : ℕ × ℕ), p ∈ Spairs c y → ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ e : ℤ, e ^ 2 = 1 →
      Λ * (Bset c T p e).card ≤ 6 * XT T p + 6 * Λ ^ q := by
    intro T y p hp Λ hΛ e he
    obtain ⟨hd, _, _, hdiv⟩ := mem_Spairs c y p hp
    have hdiv' : (p.1 : ℤ) ∣ c - (p.2 : ℤ) ^ 3 := by
      have := dvd_neg.mpr hdiv
      rwa [neg_sub] at this
    have hκ : c - (p.2 : ℤ) ^ 3 = (p.1 : ℤ) * kap c p := by
      unfold kap
      rw [Int.mul_ediv_cancel' hdiv']
    exact hsb Λ hΛ (p.1 : ℤ) (p.2 : ℤ) (kap c p) e hκ he (aT T p) (XT T p) (Bset c T p e)
      (filter_subset _ _) (fun j hj => (mem_filter.mp hj).2)
  -- one dyadic layer
  have hstep : ∀ T i : ℕ, Λ₀ ≤ 2 ^ i →
      2 ^ i * ∑ p ∈ (Spairs c (T / 2 ^ (q * i))).filter
        (fun p => ¬ p.1 ≤ T / 2 ^ (q * (i + 1))), bT c T p ≤ K * T := by
    intro T i hi
    set W : ℕ := 2 ^ (q * (i + 1)) with hW
    have hWpos : 0 < W := by positivity
    have hWeq : W = 2 ^ q * 2 ^ (q * i) := by rw [hW, ← pow_add]; congr 1; ring
    have hpow : (2 ^ i) ^ q ≤ W := by
      rw [hW, ← pow_mul]
      exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
    have hterm : ∀ p ∈ (Spairs c (T / 2 ^ (q * i))).filter
        (fun p => ¬ p.1 ≤ T / 2 ^ (q * (i + 1))), 2 ^ i * bT c T p ≤ 36 * W := by
      intro p hp
      obtain ⟨hpS, hpgt⟩ := mem_filter.mp hp
      rw [not_le] at hpgt
      obtain ⟨hd, _, _, _⟩ := mem_Spairs c _ p hpS
      have hlt : T / p.1 < W := by
        rw [Nat.div_lt_iff_lt_mul hd]
        calc T < W * (T / W + 1) := Nat.lt_mul_div_succ T hWpos
          _ ≤ W * p.1 := Nat.mul_le_mul_left _ hpgt
      have hX : XT T p ≤ 2 * W := by
        unfold XT; omega
      have h1 := hpair T _ p hpS (2 ^ i) hi 1 (by norm_num)
      have h2 := hpair T _ p hpS (2 ^ i) hi (-1) (by norm_num)
      unfold bT
      rw [Nat.mul_add]
      omega
    calc 2 ^ i * ∑ p ∈ (Spairs c (T / 2 ^ (q * i))).filter
          (fun p => ¬ p.1 ≤ T / 2 ^ (q * (i + 1))), bT c T p
        = ∑ p ∈ (Spairs c (T / 2 ^ (q * i))).filter
          (fun p => ¬ p.1 ≤ T / 2 ^ (q * (i + 1))), 2 ^ i * bT c T p := mul_sum _ _ _
      _ ≤ ∑ _p ∈ (Spairs c (T / 2 ^ (q * i))).filter
          (fun p => ¬ p.1 ≤ T / 2 ^ (q * (i + 1))), 36 * W := sum_le_sum hterm
      _ = ((Spairs c (T / 2 ^ (q * i))).filter
          (fun p => ¬ p.1 ≤ T / 2 ^ (q * (i + 1)))).card * (36 * W) := by
          rw [sum_const, smul_eq_mul]
      _ ≤ (Cn * (T / 2 ^ (q * i))) * (36 * W) :=
          Nat.mul_le_mul_right _ ((card_le_card (filter_subset _ _)).trans (hcard _))
      _ = 36 * 2 ^ q * Cn * ((T / 2 ^ (q * i)) * 2 ^ (q * i)) := by rw [hWeq]; ring
      _ ≤ 36 * 2 ^ q * Cn * T := Nat.mul_le_mul_left _ (Nat.div_mul_le_self T _)
  -- summing the layers
  have hsum : ∀ (T m i : ℕ), T ≤ i + m → Λ₀ ≤ 2 ^ i →
      2 ^ i * ∑ p ∈ Spairs c (T / 2 ^ (q * i)), bT c T p ≤ 2 * K * T := by
    intro T m
    induction m with
    | zero =>
      intro i hi _
      have h1 : T < 2 ^ (q * i) := by
        calc T ≤ i := by omega
          _ < 2 ^ i := Nat.lt_two_pow_self
          _ ≤ 2 ^ (q * i) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
      rw [Nat.div_eq_of_lt h1, Spairs_zero, sum_empty]
      simp
    | succ m ih =>
      intro i hi hΛ
      have hΛ' : Λ₀ ≤ 2 ^ (i + 1) := hΛ.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
      have h1 := ih (i + 1) (by omega) hΛ'
      have h2 := hstep T i hΛ
      have hle : T / 2 ^ (q * (i + 1)) ≤ T / 2 ^ (q * i) :=
        Nat.div_le_div_left (Nat.pow_le_pow_right (by norm_num) (by nlinarith)) (by positivity)
      have hsplit : ∑ p ∈ Spairs c (T / 2 ^ (q * i)), bT c T p
          = ∑ p ∈ Spairs c (T / 2 ^ (q * (i + 1))), bT c T p
            + ∑ p ∈ (Spairs c (T / 2 ^ (q * i))).filter
              (fun p => ¬ p.1 ≤ T / 2 ^ (q * (i + 1))), bT c T p := by
        rw [← Spairs_filter c _ _ hle]
        exact (sum_filter_add_sum_filter_not _ _ _).symm
      rw [hsplit, Nat.mul_add]
      have h3 : 2 ^ (i + 1) * ∑ p ∈ Spairs c (T / 2 ^ (q * (i + 1))), bT c T p
          = 2 * (2 ^ i * ∑ p ∈ Spairs c (T / 2 ^ (q * (i + 1))), bT c T p) := by
        rw [pow_succ]; ring
      rw [h3] at h1
      have h4 : 2 ^ i * ∑ p ∈ Spairs c (T / 2 ^ (q * (i + 1))), bT c T p ≤ K * T := by
        have h5 : 2 * (2 ^ i * ∑ p ∈ Spairs c (T / 2 ^ (q * (i + 1))), bT c T p) ≤ 2 * (K * T) := by
          calc 2 * (2 ^ i * ∑ p ∈ Spairs c (T / 2 ^ (q * (i + 1))), bT c T p) ≤ 2 * K * T := h1
            _ = 2 * (K * T) := by ring
        exact Nat.le_of_mul_le_mul_left h5 (by norm_num)
      calc 2 ^ i * ∑ p ∈ Spairs c (T / 2 ^ (q * (i + 1))), bT c T p
            + 2 ^ i * ∑ p ∈ (Spairs c (T / 2 ^ (q * i))).filter
              (fun p => ¬ p.1 ≤ T / 2 ^ (q * (i + 1))), bT c T p
          ≤ K * T + K * T := Nat.add_le_add h4 h2
        _ = 2 * K * T := by ring
  -- conclusion
  set i₀ : ℕ := max Λ₀ (2 * K * k) with hi₀
  have h2i : i₀ < 2 ^ i₀ := Nat.lt_two_pow_self
  have hΛi : Λ₀ ≤ 2 ^ i₀ := (le_max_left _ _).trans h2i.le
  have hKi : 2 * K * k ≤ 2 ^ i₀ := (le_max_right _ _).trans h2i.le
  refine ⟨2 ^ (q * i₀), by positivity, ?_⟩
  intro T
  have h1 := smallBad_card_le c T (T / 2 ^ (q * i₀))
  have h2 := hsum T T i₀ (by omega) hΛi
  have h3 : 2 ^ i₀ * (k * (SmallBad c T (T / 2 ^ (q * i₀))).card) ≤ 2 ^ i₀ * T := by
    calc 2 ^ i₀ * (k * (SmallBad c T (T / 2 ^ (q * i₀))).card)
        ≤ 2 ^ i₀ * (k * ∑ p ∈ Spairs c (T / 2 ^ (q * i₀)), bT c T p) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h1)
      _ = k * (2 ^ i₀ * ∑ p ∈ Spairs c (T / 2 ^ (q * i₀)), bT c T p) := by ring
      _ ≤ k * (2 * K * T) := Nat.mul_le_mul_left _ h2
      _ = (2 * K * k) * T := by ring
      _ ≤ 2 ^ i₀ * T := Nat.mul_le_mul_right _ hKi
  exact Nat.le_of_mul_le_mul_left h3 (by positivity)

end smallrange2


section assembly

open Finset

/-- Section 1 of PROOF.md: a representation `N = u^3 - v^3` of a nonzero `N` gives a divisor
`d ≥ 1` of `N` and an integer `s` with `4|N| = d (d^2 + 3 s^2)`. -/
lemma bad_pair_of_diff_cubes (N u v : ℤ) (h : N = u ^ 3 - v ^ 3) (hN : N ≠ 0) :
    ∃ d s : ℤ, 0 < d ∧ d ∣ N ∧ 4 * |N| = d * (d ^ 2 + 3 * s ^ 2) := by
  have huv : u - v ≠ 0 := by
    intro h0
    apply hN
    rw [h, show u = v by linarith]; ring
  refine ⟨|u - v|, u + v, abs_pos.mpr huv, ?_, ?_⟩
  · rw [abs_dvd, h]
    exact ⟨u ^ 2 + u * v + v ^ 2, by ring⟩
  · rw [sq_abs, h, show (4 : ℤ) * |u ^ 3 - v ^ 3| = |4 * (u ^ 3 - v ^ 3)| by rw [abs_mul]; norm_num,
      show 4 * (u ^ 3 - v ^ 3) = (u - v) * ((u - v) ^ 2 + 3 * (u + v) ^ 2) by ring, abs_mul]
    congr 1
    exact abs_of_nonneg (by positivity)

/-- The size constraint `d^3 ≤ 4|N|`. -/
lemma bad_pair_size (N d s : ℤ) (hd : 0 < d) (h : 4 * |N| = d * (d ^ 2 + 3 * s ^ 2)) :
    d ^ 3 ≤ 4 * |N| := by
  rw [h]
  nlinarith [mul_nonneg hd.le (sq_nonneg s)]

open Classical in
/-- The set of bad shifts for `c` in `[-T, T]`. -/
noncomputable def badSet (c : ℤ) (T : ℕ) : Finset ℤ :=
  (Finset.Icc (-(T : ℤ)) T).filter (fun t => ∃ u v : ℤ, c - t ^ 3 = u ^ 3 - v ^ 3)


open Classical in
/-- Shifts `t ∈ [-T, T]` that are bad through a divisor `d > T / A`. -/
noncomputable def LargeBad (c : ℤ) (T A : ℕ) : Finset ℤ :=
  (Finset.Icc (-(T : ℤ)) T).filter (fun t => ∃ d s : ℤ, ((T / A : ℕ) : ℤ) < d ∧ d ∣ c - t ^ 3
    ∧ 4 * |c - t ^ 3| = d * (d ^ 2 + 3 * s ^ 2))


lemma badSet_subset (c : ℤ) (hc : ¬ ∃ m : ℤ, m ^ 3 = c) (T A : ℕ) :
    badSet c T ⊆ SmallBad c T (T / A) ∪ LargeBad c T A := by
  classical
  intro t ht
  unfold badSet at ht
  obtain ⟨hIcc, u, v, huv⟩ := mem_filter.mp ht
  have hN : c - t ^ 3 ≠ 0 := fun h0 => hc ⟨t, by linarith⟩
  obtain ⟨d, s, hd, hdvd, heq⟩ := bad_pair_of_diff_cubes (c - t ^ 3) u v huv hN
  by_cases hsmall : d ≤ ((T / A : ℕ) : ℤ)
  · refine mem_union_left _ ?_
    unfold SmallBad
    exact mem_filter.mpr ⟨hIcc, d, s, by omega, hsmall, hdvd, heq⟩
  · refine mem_union_right _ ?_
    unfold LargeBad
    exact mem_filter.mpr ⟨hIcc, d, s, by omega, hdvd, heq⟩


end assembly


section chain

-- Greedy criterion: adapted from Lemma 1.7 of the pipeline-math note (tiling-complement.pdf)
-- and its Lean formalization by Codex in plby/lean-proofs (Erdos477/Tiling.lean).

def IsPacking (A B : Set ℤ) : Prop :=
  ∀ a ∈ A, ∀ a' ∈ A, ∀ b ∈ B, ∀ b' ∈ B, a + b = a' + b' → a = a'

def Covers (A B : Set ℤ) (n : ℤ) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, a + b = n

def Cubes : Set ℤ := Set.range (fun k : ℤ => k ^ 3)

/-- The avoidance hypothesis for cubes: the open core. -/
def AvoidFinite : Prop :=
  ∀ C : Finset ℤ, (∀ c ∈ C, ¬ ∃ m : ℤ, m ^ 3 = c) →
    ∃ t : ℤ, ∀ c ∈ C, ¬ ∃ u v : ℤ, c - t ^ 3 = u ^ 3 - v ^ 3

lemma extend_packing (hB : AvoidFinite) (A : Finset ℤ) (hA : IsPacking (A : Set ℤ) Cubes)
    (n : ℤ) :
    ∃ A' : Finset ℤ, A ⊆ A' ∧ IsPacking (A' : Set ℤ) Cubes ∧ Covers (A' : Set ℤ) Cubes n := by
  classical
  by_cases hc : Covers (A : Set ℤ) Cubes n
  · exact ⟨A, Finset.Subset.refl A, hA, hc⟩
  let C := A.image (fun a => n - a)
  have hC : ∀ c ∈ C, ¬ ∃ m : ℤ, m ^ 3 = c := by
    rintro c hcC ⟨m, hm⟩
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hcC
    exact hc ⟨a, ha, n - a, ⟨m, hm⟩, by omega⟩
  obtain ⟨t, havoid⟩ := hB C hC
  have hnew : ∀ a ∈ A, ¬ ∃ u v : ℤ, n - a - t ^ 3 = u ^ 3 - v ^ 3 := fun a ha =>
    havoid (n - a) (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
  refine ⟨insert (n - t ^ 3) A, Finset.subset_insert _ _, ?_, ?_⟩
  · rintro a ha a' ha' _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ heq
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha ha'
    rcases ha with rfl | ha <;> rcases ha' with rfl | ha'
    · rfl
    · exact False.elim (hnew a' ha' ⟨v, u, by linarith⟩)
    · exact False.elim (hnew a ha ⟨u, v, by linarith⟩)
    · exact hA a ha a' ha' _ ⟨u, rfl⟩ _ ⟨v, rfl⟩ heq
  · exact ⟨n - t ^ 3, by simp, t ^ 3, ⟨t, rfl⟩, by ring⟩

lemma exists_tiling (hB : AvoidFinite) :
    ∃ A : Set ℤ, IsPacking A Cubes ∧ ∀ n, Covers A Cubes n := by
  classical
  let State := {A : Finset ℤ // IsPacking (A : Set ℤ) Cubes}
  have step : ∀ A : State, ∀ n : ℤ,
      ∃ A' : State, A.val ⊆ A'.val ∧ Covers (A'.val : Set ℤ) Cubes n := by
    intro A n
    obtain ⟨A', hsub, hpack, hcover⟩ := extend_packing hB A.val A.property n
    exact ⟨⟨A', hpack⟩, hsub, hcover⟩
  choose next hnext using step
  let initial : State := ⟨∅, by simp [IsPacking]⟩
  let s : ℕ → State := fun k =>
    Nat.rec initial (fun k A => next A (Equiv.intEquivNat.symm k)) k
  have hs (k : ℕ) : (s k).val ⊆ (s (k + 1)).val ∧
      Covers ((s (k + 1)).val : Set ℤ) Cubes (Equiv.intEquivNat.symm k) :=
    hnext (s k) (Equiv.intEquivNat.symm k)
  have hmono : Monotone (fun k => (s k).val) :=
    monotone_nat_of_le_succ (fun k => (hs k).1)
  refine ⟨{a | ∃ k, a ∈ (s k).val}, ?_, ?_⟩
  · rintro a ⟨i, hi⟩ a' ⟨j, hj⟩ b hb b' hb' heq
    exact (s (max i j)).property a (hmono (le_max_left i j) hi)
      a' (hmono (le_max_right i j) hj) b hb b' hb' heq
  · intro n
    obtain ⟨k, rfl⟩ := Equiv.intEquivNat.symm.surjective n
    obtain ⟨a, ha, b, hb, hab⟩ := (hs k).2
    exact ⟨a, ⟨k + 1, ha⟩, b, hb, hab⟩

/-- If simultaneous avoidance holds for cubes, the statement of the X^3 variant is false. -/
theorem disproof_of_avoid (hB : AvoidFinite) :
    ¬ (type_of% @Erdos477.erdos_477.variants.X_pow_three) := by
  intro h
  obtain ⟨A, hpack, hcov⟩ := exists_tiling hB
  obtain ⟨z, hz⟩ := h A
  apply hz
  obtain ⟨a, ha, b, hb, hab⟩ := hcov z
  have hrange : Set.range (fun x : ℤ => Polynomial.eval x (Polynomial.X ^ 3 : Polynomial ℤ)) = Cubes := by
    ext y; simp [Cubes]
  refine ⟨(a, b), ⟨⟨ha, by rw [hrange]; exact hb⟩, hab.symm⟩, ?_⟩
  rintro ⟨a', b'⟩ ⟨⟨ha', hb'⟩, heq⟩
  rw [hrange] at hb'
  simp only at ha' hb' heq
  have haa : a' = a := hpack a' ha' a ha b' hb' b hb (by linarith)
  ext
  · exact haa
  · simp only; linarith


end chain


section splitprimes

open Polynomial NumberField

/-- Cubing is injective modulo a prime `p ≡ 2 (mod 3)`. -/
lemma cube_inj_zmod (p : ℕ) [hp : Fact p.Prime] (hp3 : p % 3 = 2) (a b : ZMod p)
    (h : a ^ 3 = b ^ 3) : a = b := by
  have key : ∀ x : ZMod p, x ^ (3 * (2 * (p / 3) + 1)) = x := by
    intro x
    have h1 : 3 * (2 * (p / 3) + 1) = p + (p - 1) := by
      have := hp.out.two_le
      omega
    rw [h1, pow_add, ZMod.pow_card]
    have h2 : x * x ^ (p - 1) = x ^ p := by
      rw [← pow_succ', Nat.sub_add_cancel hp.out.one_le]
    rw [h2, ZMod.pow_card]
  rw [← key a, ← key b, pow_mul, pow_mul, h]

lemma prime_dvd_sub_of_dvd_cube_sub (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 2) (u v : ℤ)
    (h : (p : ℤ) ∣ u ^ 3 - v ^ 3) : (p : ℤ) ∣ u - v := by
  have : Fact p.Prime := ⟨hp⟩
  have h1 : ((u ^ 3 - v ^ 3 : ℤ) : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
  have h2 : ((u : ZMod p)) ^ 3 = (v : ZMod p) ^ 3 := by
    push_cast at h1
    exact sub_eq_zero.mp h1
  have h3 := cube_inj_zmod p hp3 _ _ h2
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
  push_cast
  exact sub_eq_zero.mpr h3


section split

variable (c : ℤ) [hirr : Fact (Irreducible (fpoly c))]

/-- A proper ideal containing a rational prime `p` and an integer `n` forces `p ∣ n`. -/
lemma int_dvd_of_mem (P : Ideal (𝓞 (Kc c))) (hP : P ≠ ⊤) (p : ℕ) (hp : p.Prime)
    (hpP : ((p : ℤ) : 𝓞 (Kc c)) ∈ P) (n : ℤ) (hn : (n : 𝓞 (Kc c)) ∈ P) : (p : ℤ) ∣ n := by
  by_contra hnd
  have hcop : IsCoprime (p : ℤ) n := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h2 : ¬ p ∣ n.natAbs := fun h => hnd (Int.natCast_dvd.mpr h)
    have h3 := (Nat.Prime.coprime_iff_not_dvd hp).mpr h2
    simpa [Int.gcd] using h3
  obtain ⟨a, b, hab⟩ := hcop
  apply hP
  rw [Ideal.eq_top_iff_one]
  have h1 : ((a * p + b * n : ℤ) : 𝓞 (Kc c)) ∈ P := by
    push_cast
    exact P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hn)
  rw [hab] at h1
  simpa using h1

lemma natCast_mem_of_absNorm (P : Ideal (𝓞 (Kc c))) (p : ℕ) (hN : Ideal.absNorm P = p) :
    ((p : ℤ) : 𝓞 (Kc c)) ∈ P := by
  have := Ideal.absNorm_mem P
  rw [hN] at this
  simpa using this

/-- A prime ideal of prime norm `p` gives a cube root of `c` modulo `p`. -/
lemma exists_root_of_absNorm_prime (P : Ideal (𝓞 (Kc c))) (hP : P ≠ ⊤) (p : ℕ) (hp : p.Prime)
    (hN : Ideal.absNorm P = p) :
    ∃ r : ℕ, r < p ∧ ((r : ℤ) : 𝓞 (Kc c)) - thetaO c ∈ P ∧ (p : ℤ) ∣ (r : ℤ) ^ 3 - c := by
  have hpP := natCast_mem_of_absNorm c P p hN
  have hfin : Finite (𝓞 (Kc c) ⧸ P) := by
    rw [← Ideal.absNorm_ne_zero_iff, hN]; exact hp.ne_zero
  let f : Fin p → 𝓞 (Kc c) ⧸ P := fun i => Ideal.Quotient.mk P (((i : ℕ) : ℤ) : 𝓞 (Kc c))
  have hinj : Function.Injective f := by
    intro i j hij
    have h1 : ((((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) : ℤ) : 𝓞 (Kc c)) ∈ P := by
      push_cast
      exact Ideal.Quotient.eq.mp hij
    have h2 := int_dvd_of_mem c P hP p hp hpP _ h1
    have hi := i.isLt
    have hj := j.isLt
    have h3 : ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) = 0 := by
      apply Int.eq_zero_of_abs_lt_dvd h2
      rw [abs_lt]; constructor <;> omega
    exact Fin.ext (by omega)
  have hcard : Nat.card (𝓞 (Kc c) ⧸ P) ≤ Nat.card (Fin p) := by
    rw [Nat.card_fin]
    have : Ideal.absNorm P = Nat.card (𝓞 (Kc c) ⧸ P) := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
    omega
  have hbij := hinj.bijective_of_nat_card_le hcard
  obtain ⟨i, hi⟩ := hbij.2 (Ideal.Quotient.mk P (thetaO c))
  have hmem : (((i : ℕ) : ℤ) : 𝓞 (Kc c)) - thetaO c ∈ P := Ideal.Quotient.eq.mp hi
  refine ⟨i, i.isLt, hmem, ?_⟩
  apply int_dvd_of_mem c P hP p hp hpP
  have := P.mul_mem_right (wO c ((i : ℕ) : ℤ)) hmem
  rw [sub_mul_wO] at this
  exact this

/-- Two prime ideals of the same prime norm `p ∤ 3c` attached to the same root coincide. -/
lemma prime_unique_of_root (P₁ P₂ : Ideal (𝓞 (Kc c))) (h1 : P₁.IsPrime) (h2 : P₂.IsPrime)
    (p : ℕ) (hp : p.Prime) (hN1 : Ideal.absNorm P₁ = p) (hN2 : Ideal.absNorm P₂ = p)
    (hp3c : ¬ (p : ℤ) ∣ 3 * c) (r : ℤ)
    (hr1 : (r : 𝓞 (Kc c)) - thetaO c ∈ P₁) (hr2 : (r : 𝓞 (Kc c)) - thetaO c ∈ P₂) :
    P₁ = P₂ := by
  by_contra hne
  have h10 : P₁ ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hN1
    exact hp.ne_zero hN1.symm
  have h20 : P₂ ≠ ⊥ := by
    rintro rfl
    rw [Ideal.absNorm_bot] at hN2
    exact hp.ne_zero hN2.symm
  have hmax1 : P₁.IsMaximal := h1.isMaximal h10
  have hmax2 : P₂.IsMaximal := h2.isMaximal h20
  have hcop : P₁ ⊔ P₂ = ⊤ := Ideal.IsMaximal.coprime_of_ne hmax1 hmax2 hne
  have hmul : P₁ * P₂ = P₁ ⊓ P₂ := Ideal.mul_eq_inf_of_coprime hcop
  have hpP1 := natCast_mem_of_absNorm c P₁ p hN1
  have hpP2 := natCast_mem_of_absNorm c P₂ p hN2
  have key : ∀ a : ℤ, (a : 𝓞 (Kc c)) - thetaO c ∈ P₁ → (a : 𝓞 (Kc c)) - thetaO c ∈ P₂ →
      ((p : ℤ) ^ 2) ∣ a ^ 3 - c := by
    intro a ha1 ha2
    have hmem : (a : 𝓞 (Kc c)) - thetaO c ∈ P₁ * P₂ := by
      rw [hmul]; exact ⟨ha1, ha2⟩
    have := absNorm_dvd_of_mem c (P₁ * P₂) _ hmem
    rw [map_mul, hN1, hN2, norm_int_sub] at this
    have e : ((p * p : ℕ) : ℤ) = (p : ℤ) ^ 2 := by push_cast; ring
    rw [e] at this
    exact this
  have k1 := key r hr1 hr2
  have k2 := key (r + p)
    (by
      have : ((r + p : ℤ) : 𝓞 (Kc c)) - thetaO c
          = ((r : 𝓞 (Kc c)) - thetaO c) + ((p : ℤ) : 𝓞 (Kc c)) := by push_cast; ring
      rw [this]; exact P₁.add_mem hr1 hpP1)
    (by
      have : ((r + p : ℤ) : 𝓞 (Kc c)) - thetaO c
          = ((r : 𝓞 (Kc c)) - thetaO c) + ((p : ℤ) : 𝓞 (Kc c)) := by push_cast; ring
      rw [this]; exact P₂.add_mem hr2 hpP2)
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have k3 : (p : ℤ) * (p : ℤ) ∣ (p : ℤ) * (3 * r ^ 2 + 3 * r * p + (p : ℤ) ^ 2) := by
    have := dvd_sub k2 k1
    have e : (r + (p : ℤ)) ^ 3 - c - (r ^ 3 - c)
        = (p : ℤ) * (3 * r ^ 2 + 3 * r * p + (p : ℤ) ^ 2) := by ring
    have e2 : (p : ℤ) ^ 2 = (p : ℤ) * (p : ℤ) := by ring
    rw [e] at this
    exact e2 ▸ this
  have k4 : (p : ℤ) ∣ 3 * r ^ 2 + 3 * r * p + (p : ℤ) ^ 2 :=
    (mul_dvd_mul_iff_left hp0).mp k3
  have k5 : (p : ℤ) ∣ 3 * r ^ 2 := by
    have h : (p : ℤ) ∣ 3 * r * p + (p : ℤ) ^ 2 := ⟨3 * r + p, by ring⟩
    have := dvd_sub k4 h
    have e : 3 * r ^ 2 + 3 * r * p + (p : ℤ) ^ 2 - (3 * r * p + (p : ℤ) ^ 2) = 3 * r ^ 2 := by ring
    rw [e] at this
    exact this
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  rcases hpp.dvd_or_dvd k5 with h | h
  · exact hp3c (dvd_mul_of_dvd_left h c)
  · have hr : (p : ℤ) ∣ r := hpp.dvd_of_dvd_pow h
    have h4 : (p : ℤ) ∣ r ^ 3 - c := dvd_trans (dvd_pow_self _ two_ne_zero) k1
    have h5 : (p : ℤ) ∣ c := by
      have h3 : (p : ℤ) ∣ r ^ 3 := dvd_pow hr three_ne_zero
      have := dvd_sub h3 h4
      simpa using this
    exact hp3c (dvd_mul_of_dvd_right h5 3)

lemma absNorm_dvd_cube (P : Ideal (𝓞 (Kc c))) (p : ℕ)
    (hpP : ((p : ℤ) : 𝓞 (Kc c)) ∈ P) : Ideal.absNorm P ∣ p ^ 3 := by
  have := Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem P).mpr hpP)
  rw [Ideal.absNorm_span_singleton, norm_int] at this
  simpa [Int.natAbs_pow] using this

/-- The norm of a prime ideal above `p` is `p ^ f` with `1 ≤ f ≤ 3`. -/
lemma absNorm_eq_pow (P : Ideal (𝓞 (Kc c))) (hP : P ≠ ⊤) (p : ℕ) (hp : p.Prime)
    (hpP : ((p : ℤ) : 𝓞 (Kc c)) ∈ P) :
    ∃ f : ℕ, 1 ≤ f ∧ f ≤ 3 ∧ Ideal.absNorm P = p ^ f := by
  obtain ⟨k, hk, hk2⟩ := (Nat.dvd_prime_pow hp).mp (absNorm_dvd_cube c P p hpP)
  refine ⟨k, ?_, hk, hk2⟩
  rcases Nat.eq_zero_or_pos k with rfl | h
  · rw [pow_zero] at hk2
    exact absurd (Ideal.absNorm_eq_one_iff.mp hk2) hP
  · exact h

/-- At most three prime ideals contain a given rational prime. -/
lemma card_primes_over_le (p : ℕ) (hp : p.Prime) (s : Finset (Ideal (𝓞 (Kc c))))
    (hs : ∀ P ∈ s, P.IsPrime ∧ ((p : ℤ) : 𝓞 (Kc c)) ∈ P) : s.card ≤ 3 := by
  have hp0 : ((p : ℤ) : 𝓞 (Kc c)) ≠ 0 := by
    exact_mod_cast hp.ne_zero
  have hne : ∀ P ∈ s, P ≠ ⊥ := by
    intro P hP h
    have := (hs P hP).2
    rw [h] at this
    exact hp0 (by simpa using this)
  have hdvd : ∏ P ∈ s, P ∣ Ideal.span {((p : ℤ) : 𝓞 (Kc c))} := by
    apply Finset.prod_primes_dvd
    · intro P hP; exact Ideal.prime_of_isPrime (hne P hP) (hs P hP).1
    · intro P hP
      rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
      exact (hs P hP).2
  have h1 := map_dvd Ideal.absNorm hdvd
  rw [map_prod, Ideal.absNorm_span_singleton, norm_int] at h1
  have h1' : ∏ P ∈ s, Ideal.absNorm P ∣ p ^ 3 := by simpa [Int.natAbs_pow] using h1
  have h2 : ∀ P ∈ s, p ≤ Ideal.absNorm P := by
    intro P hP
    obtain ⟨f, hf1, _, hf⟩ := absNorm_eq_pow c P (hs P hP).1.ne_top p hp (hs P hP).2
    rw [hf]
    exact Nat.le_self_pow (by omega) p
  have h3 : p ^ s.card ≤ ∏ P ∈ s, Ideal.absNorm P := by
    calc p ^ s.card = ∏ _P ∈ s, p := by simp
      _ ≤ ∏ P ∈ s, Ideal.absNorm P := Finset.prod_le_prod (fun _ _ => Nat.zero_le _) h2
  have h4 : ∏ P ∈ s, Ideal.absNorm P ≤ p ^ 3 := Nat.le_of_dvd (pow_pos hp.pos 3) h1'
  exact (Nat.pow_le_pow_iff_right hp.one_lt).mp (h3.trans h4)

/-- Every nonzero prime ideal contains a rational prime. -/
lemma exists_prime_mem (P : Ideal (𝓞 (Kc c))) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ ((p : ℤ) : 𝓞 (Kc c)) ∈ P := by
  have key : ∀ n : ℕ, n ≠ 0 → n ≠ 1 → (n : 𝓞 (Kc c)) ∈ P →
      ∃ p : ℕ, p.Prime ∧ ((p : ℤ) : 𝓞 (Kc c)) ∈ P := by
    intro n
    refine Nat.recOnMul (motive := fun n => n ≠ 0 → n ≠ 1 → (n : 𝓞 (Kc c)) ∈ P →
      ∃ p : ℕ, p.Prime ∧ ((p : ℤ) : 𝓞 (Kc c)) ∈ P) ?_ ?_ ?_ ?_ n
    · intro h; exact absurd rfl h
    · intro _ h; exact absurd rfl h
    · intro p hp _ _ h; exact ⟨p, hp, by simpa using h⟩
    · intro a b iha ihb h0 h1 h
      have hab : (a : 𝓞 (Kc c)) * (b : 𝓞 (Kc c)) ∈ P := by simpa using h
      rcases hP.mem_or_mem hab with ha | hb
      · have ha0 : a ≠ 0 := by rintro rfl; simp at h0
        have ha1 : a ≠ 1 := by
          rintro rfl
          apply hP.ne_top
          rw [Ideal.eq_top_iff_one]
          simpa using ha
        exact iha ha0 ha1 ha
      · have hb0 : b ≠ 0 := by rintro rfl; simp at h0
        have hb1 : b ≠ 1 := by
          rintro rfl
          apply hP.ne_top
          rw [Ideal.eq_top_iff_one]
          simpa using hb
        exact ihb hb0 hb1 hb
  have hN0 : Ideal.absNorm P ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]; exact hP0
  have hN1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  exact key _ hN0 hN1 (Ideal.absNorm_mem P)

end split

section idealsums

variable (K : Type*) [Field K] [NumberField K]

open Classical in
/-- Nonzero ideals of norm at most `Y`. -/
noncomputable def idealsLe (Y : ℕ) : Finset (Ideal (𝓞 K)) :=
  (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) Y).toFinset.filter (fun I => I ≠ ⊥)

lemma mem_idealsLe (Y : ℕ) (I : Ideal (𝓞 K)) :
    I ∈ idealsLe K Y ↔ Ideal.absNorm I ≤ Y ∧ I ≠ ⊥ := by
  classical
  simp [idealsLe]

open Classical in
/-- Nonzero prime ideals of norm at most `Y`. -/
noncomputable def primesLe (Y : ℕ) : Finset (Ideal (𝓞 K)) :=
  (idealsLe K Y).filter (fun I => I.IsPrime)

lemma mem_primesLe (Y : ℕ) (P : Ideal (𝓞 K)) :
    P ∈ primesLe K Y ↔ (Ideal.absNorm P ≤ Y ∧ P ≠ ⊥) ∧ P.IsPrime := by
  classical
  simp [primesLe, mem_idealsLe]

lemma absNorm_pos' (I : Ideal (𝓞 K)) (hI : I ≠ ⊥) : 0 < Ideal.absNorm I :=
  Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])

lemma two_le_absNorm (P : Ideal (𝓞 K)) (hP : P.IsPrime) (hP0 : P ≠ ⊥) : 2 ≤ Ideal.absNorm P := by
  have h0 := absNorm_pos' K P hP0
  have h1 : Ideal.absNorm P ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]; exact hP.ne_top
  omega

open Classical in
/-- `log N(I)` is at most the sum of `log N(P)` over prime powers `P ^ j` dividing `I`. -/
lemma log_absNorm_le (Y : ℕ) (I : Ideal (𝓞 K)) (hI : I ∈ idealsLe K Y) :
    Real.log (Ideal.absNorm I) ≤ ∑ P ∈ primesLe K Y, ∑ j ∈ Finset.Icc 1 Y,
      (if P ^ j ∣ I then Real.log (Ideal.absNorm P) else 0) := by
  classical
  obtain ⟨hIY, hI0⟩ := (mem_idealsLe K Y I).mp hI
  set F := UniqueFactorizationMonoid.normalizedFactors I with hF
  have hprod : I = ∏ P ∈ F.toFinset, P ^ F.count P := by
    rw [← Finset.prod_multiset_count]
    exact (Ideal.prod_normalizedFactors_eq_self hI0).symm
  have hNpos := absNorm_pos' K I hI0
  have hmemF : ∀ P ∈ F.toFinset, P.IsPrime ∧ P ≠ ⊥ ∧ P ∣ I := by
    intro P hP
    rw [Multiset.mem_toFinset] at hP
    have hpr := UniqueFactorizationMonoid.prime_of_normalized_factor P hP
    exact ⟨Ideal.isPrime_of_prime hpr, hpr.ne_zero,
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP⟩
  have hpowdvd : ∀ P ∈ F.toFinset, P ^ F.count P ∣ I := by
    intro P hP
    have := Finset.dvd_prod_of_mem (fun P => P ^ F.count P) hP
    rwa [← hprod] at this
  have hlog : Real.log (Ideal.absNorm I)
      = ∑ P ∈ F.toFinset, (F.count P : ℝ) * Real.log (Ideal.absNorm P) := by
    have h1 : Ideal.absNorm I = ∏ P ∈ F.toFinset, Ideal.absNorm P ^ F.count P := by
      conv_lhs => rw [hprod]
      rw [map_prod]
      simp only [map_pow]
    rw [h1]
    push_cast
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro P _
      rw [Real.log_pow]
    · intro P hP
      have := absNorm_pos' K P (hmemF P hP).2.1
      positivity
  rw [hlog]
  have hsub : F.toFinset ⊆ primesLe K Y := by
    intro P hP
    obtain ⟨h1, h2, h3⟩ := hmemF P hP
    rw [mem_primesLe]
    refine ⟨⟨?_, h2⟩, h1⟩
    exact (Nat.le_of_dvd hNpos (map_dvd Ideal.absNorm h3)).trans hIY
  have hnn : ∀ (P : Ideal (𝓞 K)) (j : ℕ),
      0 ≤ (if P ^ j ∣ I then Real.log (Ideal.absNorm P) else 0) := by
    intro P j
    split_ifs
    · exact Real.log_natCast_nonneg _
    · exact le_rfl
  calc ∑ P ∈ F.toFinset, (F.count P : ℝ) * Real.log (Ideal.absNorm P)
      ≤ ∑ P ∈ F.toFinset, ∑ j ∈ Finset.Icc 1 Y,
          (if P ^ j ∣ I then Real.log (Ideal.absNorm P) else 0) := by
        apply Finset.sum_le_sum
        intro P hP
        obtain ⟨h1, h2, h3⟩ := hmemF P hP
        have hcount : F.count P ≤ Y := by
          have hd : Ideal.absNorm P ^ F.count P ∣ Ideal.absNorm I := by
            have := map_dvd Ideal.absNorm (hpowdvd P hP)
            rwa [map_pow] at this
          have h2le := two_le_absNorm K P h1 h2
          have h4 : 2 ^ F.count P ≤ Ideal.absNorm I :=
            (Nat.pow_le_pow_left h2le _).trans (Nat.le_of_dvd hNpos hd)
          have h5 : F.count P < 2 ^ F.count P := Nat.lt_two_pow_self
          omega
        calc (F.count P : ℝ) * Real.log (Ideal.absNorm P)
            = ∑ _j ∈ Finset.Icc 1 (F.count P), Real.log (Ideal.absNorm P) := by simp
          _ = ∑ j ∈ Finset.Icc 1 (F.count P),
                (if P ^ j ∣ I then Real.log (Ideal.absNorm P) else 0) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [if_pos]
              exact dvd_trans (pow_dvd_pow P (Finset.mem_Icc.mp hj).2) (hpowdvd P hP)
          _ ≤ ∑ j ∈ Finset.Icc 1 Y, (if P ^ j ∣ I then Real.log (Ideal.absNorm P) else 0) :=
              Finset.sum_le_sum_of_subset_of_nonneg (Finset.Icc_subset_Icc le_rfl hcount)
                (fun j _ _ => hnn P j)
    _ ≤ ∑ P ∈ primesLe K Y, ∑ j ∈ Finset.Icc 1 Y,
          (if P ^ j ∣ I then Real.log (Ideal.absNorm P) else 0) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun P _ _ => Finset.sum_nonneg (fun j _ => hnn P j))

/-- The convolution inequality `∑ log N(I) N(I)^{-x} ≤ (∑ log N(P) N(P)^{-jx}) (∑ N(J)^{-x})`. -/
lemma sum_log_le (Y : ℕ) (x : ℝ) :
    ∑ I ∈ idealsLe K Y, Real.log (Ideal.absNorm I) * ((Ideal.absNorm I : ℝ)) ^ (-x)
      ≤ (∑ P ∈ primesLe K Y, ∑ j ∈ Finset.Icc 1 Y,
          Real.log (Ideal.absNorm P) * (((Ideal.absNorm P : ℝ)) ^ j) ^ (-x))
        * ∑ J ∈ idealsLe K Y, ((Ideal.absNorm J : ℝ)) ^ (-x) := by
  classical
  have hnn : ∀ I : Ideal (𝓞 K), 0 ≤ ((Ideal.absNorm I : ℝ)) ^ (-x) :=
    fun I => Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc ∑ I ∈ idealsLe K Y, Real.log (Ideal.absNorm I) * ((Ideal.absNorm I : ℝ)) ^ (-x)
      ≤ ∑ I ∈ idealsLe K Y, (∑ P ∈ primesLe K Y, ∑ j ∈ Finset.Icc 1 Y,
          (if P ^ j ∣ I then Real.log (Ideal.absNorm P) else 0))
            * ((Ideal.absNorm I : ℝ)) ^ (-x) :=
        Finset.sum_le_sum (fun I hI =>
          mul_le_mul_of_nonneg_right (log_absNorm_le K Y I hI) (hnn I))
    _ = ∑ P ∈ primesLe K Y, ∑ j ∈ Finset.Icc 1 Y, Real.log (Ideal.absNorm P)
          * ∑ I ∈ (idealsLe K Y).filter (fun I => P ^ j ∣ I), ((Ideal.absNorm I : ℝ)) ^ (-x) := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro P _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum, Finset.sum_filter]
        apply Finset.sum_congr rfl
        intro I _
        split_ifs <;> simp
    _ ≤ ∑ P ∈ primesLe K Y, ∑ j ∈ Finset.Icc 1 Y, Real.log (Ideal.absNorm P)
          * ((((Ideal.absNorm P : ℝ)) ^ j) ^ (-x)
            * ∑ J ∈ idealsLe K Y, ((Ideal.absNorm J : ℝ)) ^ (-x)) := by
        apply Finset.sum_le_sum
        intro P hP
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left _ (Real.log_natCast_nonneg _)
        obtain ⟨⟨_, hP0⟩, hPp⟩ := (mem_primesLe K Y P).mp hP
        have hP0' : P ≠ 0 := by rw [Ideal.zero_eq_bot]; exact hP0
        have hpow0 : P ^ j ≠ 0 := pow_ne_zero j hP0'
        have hinj : Function.Injective (fun J : Ideal (𝓞 K) => P ^ j * J) :=
          mul_right_injective₀ hpow0
        calc ∑ I ∈ (idealsLe K Y).filter (fun I => P ^ j ∣ I), ((Ideal.absNorm I : ℝ)) ^ (-x)
            ≤ ∑ I ∈ (idealsLe K Y).image (fun J => P ^ j * J),
                ((Ideal.absNorm I : ℝ)) ^ (-x) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · intro I hI
                rw [Finset.mem_filter] at hI
                obtain ⟨hI1, J, rfl⟩ := hI
                rw [Finset.mem_image]
                refine ⟨J, ?_, rfl⟩
                rw [mem_idealsLe] at hI1 ⊢
                obtain ⟨h1, h2⟩ := hI1
                have hJ0 : J ≠ ⊥ := by
                  rintro rfl
                  apply h2
                  simp
                refine ⟨?_, hJ0⟩
                rw [map_mul] at h1
                have hpos : 0 < Ideal.absNorm (P ^ j) :=
                  absNorm_pos' K _ (by rw [← Ideal.zero_eq_bot]; exact hpow0)
                exact (Nat.le_mul_of_pos_left _ hpos).trans h1
              · intro I _ _
                exact hnn I
          _ = ∑ J ∈ idealsLe K Y, ((Ideal.absNorm (P ^ j * J) : ℝ)) ^ (-x) :=
              Finset.sum_image (fun a _ b _ h => hinj h)
          _ = (((Ideal.absNorm P : ℝ)) ^ j) ^ (-x)
                * ∑ J ∈ idealsLe K Y, ((Ideal.absNorm J : ℝ)) ^ (-x) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro J _
              rw [map_mul, map_pow]
              push_cast
              rw [Real.mul_rpow (by positivity) (by positivity)]
    _ = (∑ P ∈ primesLe K Y, ∑ j ∈ Finset.Icc 1 Y,
          Real.log (Ideal.absNorm P) * (((Ideal.absNorm P : ℝ)) ^ j) ^ (-x))
        * ∑ J ∈ idealsLe K Y, ((Ideal.absNorm J : ℝ)) ^ (-x) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro P _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- Coefficients of the Dedekind zeta function. -/
noncomputable def acoef (n : ℕ) : ℕ := Nat.card {I : Ideal (𝓞 K) // Ideal.absNorm I = n}

lemma sum_idealsLe_eq (Y : ℕ) (f : ℕ → ℝ) :
    ∑ I ∈ idealsLe K Y, f (Ideal.absNorm I) = ∑ n ∈ Finset.Icc 1 Y, (acoef K n : ℝ) * f n := by
  classical
  have hmaps : ∀ I ∈ idealsLe K Y, Ideal.absNorm I ∈ Finset.Icc 1 Y := by
    intro I hI
    obtain ⟨h1, h2⟩ := (mem_idealsLe K Y I).mp hI
    rw [Finset.mem_Icc]
    exact ⟨absNorm_pos' K I h2, h1⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro n hn
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
  have hcard : acoef K n = ((idealsLe K Y).filter (fun I => Ideal.absNorm I = n)).card := by
    unfold acoef
    change Nat.card ↥{I : Ideal (𝓞 K) | Ideal.absNorm I = n} = _
    rw [Nat.card_coe_set_eq, ← Set.ncard_coe_finset]
    congr 1
    ext I
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, mem_idealsLe]
    constructor
    · intro h
      refine ⟨⟨by omega, ?_⟩, h⟩
      rintro rfl
      rw [Ideal.absNorm_bot] at h
      omega
    · intro h; exact h.2
  rw [hcard, ← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_congr rfl
  intro I hI
  rw [(Finset.mem_filter.mp hI).2]

lemma acoef_sum_le : ∃ C : ℝ, 0 ≤ C ∧
    ∀ Y : ℕ, (∑ n ∈ Finset.Icc 1 Y, (acoef K n : ℝ)) ≤ C * Y := by
  classical
  obtain ⟨C, hC⟩ := ideal_count_le K
  have hC0 : 0 ≤ C := by
    have := hC 1 le_rfl
    have h2 : (0 : ℝ) ≤ ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) 1).toFinset.card : ℝ) :=
      Nat.cast_nonneg _
    simp only [Nat.cast_one, mul_one] at this
    linarith
  refine ⟨C, hC0, fun Y => ?_⟩
  rcases Nat.eq_zero_or_pos Y with rfl | hY
  · simp
  have h1 := sum_idealsLe_eq K Y (fun _ => 1)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h1
  rw [← h1]
  have h2 : (idealsLe K Y).card ≤ (Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) Y).toFinset.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  calc ((idealsLe K Y).card : ℝ)
      ≤ ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K) Y).toFinset.card : ℝ) := by
        exact_mod_cast h2
    _ ≤ C * Y := hC Y hY

/-- The Dedekind zeta function on the real axis, as a real series. -/
noncomputable def zetaR (x : ℝ) : ℝ := ∑' n : ℕ, (acoef K n : ℝ) / (n : ℝ) ^ x

lemma summable_zetaR (x : ℝ) (hx : 1 < x) :
    Summable (fun n : ℕ => (acoef K n : ℝ) / (n : ℝ) ^ x) := by
  apply LSeries.summable_real_of_abscissaOfAbsConv_lt
  have h1 : LSeries.abscissaOfAbsConv (fun n : ℕ => ((acoef K n : ℝ) : ℂ)) ≤ 1 := by
    refine LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy => ?_
    obtain ⟨C, hC0, hC⟩ := acoef_sum_le K
    refine LSeriesSummable_of_sum_norm_bigO_and_nonneg (f := fun n => (acoef K n : ℝ))
      (r := 1) ?_ (fun n => Nat.cast_nonneg _) zero_le_one (by simpa using hy)
    refine Asymptotics.IsBigO.of_bound C (Filter.Eventually.of_forall fun n => ?_)
    rw [Real.norm_of_nonneg (Finset.sum_nonneg fun k _ => Nat.cast_nonneg _), Real.rpow_one,
      Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact hC n
  exact h1.trans_lt (by exact_mod_cast hx)

lemma dedekindZeta_eq_zetaR (x : ℝ) (hx : 1 < x) :
    NumberField.dedekindZeta K (x : ℂ) = ((zetaR K x : ℝ) : ℂ) := by
  unfold NumberField.dedekindZeta LSeries zetaR
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have hx0 : x ≠ 0 := by linarith
    simp [LSeries.term_zero, Real.zero_rpow hx0]
  · rw [LSeries.term_of_ne_zero hn]
    push_cast
    rw [Complex.ofReal_cpow (Nat.cast_nonneg n)]
    simp [acoef]

lemma tendsto_zetaR :
    Filter.Tendsto (fun x : ℝ => (x - 1) * zetaR K x) (nhdsWithin 1 (Set.Ioi 1))
      (nhds (NumberField.dedekindZeta_residue K)) := by
  have h := NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K
  have h2 := (Complex.continuous_re.tendsto _).comp h
  simp only [Complex.ofReal_re] at h2
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  simp only [Function.comp_apply]
  rw [dedekindZeta_eq_zetaR K x hx]
  have : ((x : ℂ) - 1) * ((zetaR K x : ℝ) : ℂ) = (((x - 1) * zetaR K x : ℝ) : ℂ) := by
    push_cast; ring
  rw [this, Complex.ofReal_re]

lemma sum_le_zetaR (Y : ℕ) (x : ℝ) (hx : 1 < x) :
    ∑ J ∈ idealsLe K Y, ((Ideal.absNorm J : ℝ)) ^ (-x) ≤ zetaR K x := by
  have h1 := sum_idealsLe_eq K Y (fun n => (n : ℝ) ^ (-x))
  rw [h1]
  have h2 : ∀ n : ℕ, (acoef K n : ℝ) * (n : ℝ) ^ (-x) = (acoef K n : ℝ) / (n : ℝ) ^ x := by
    intro n
    rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  simp_rw [h2]
  exact (summable_zetaR K x hx).sum_le_tsum _
    (fun n _ => div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))

/-- Finite-difference bound: the truncated zeta sums at `x` and `x + h` differ by at most
`h * B * ζ(x)` when `B` bounds the prime-ideal sum. -/
lemma zeta_diff_le (Y : ℕ) (x h B : ℝ) (hx : 1 < x) (hh : 0 < h)
    (hB : ∑ P ∈ primesLe K Y, ∑ j ∈ Finset.Icc 1 Y,
          Real.log (Ideal.absNorm P) * (((Ideal.absNorm P : ℝ)) ^ j) ^ (-x) ≤ B) :
    ∑ n ∈ Finset.Icc 1 Y, (acoef K n : ℝ) / (n : ℝ) ^ x
      ≤ ∑ n ∈ Finset.Icc 1 Y, (acoef K n : ℝ) / (n : ℝ) ^ (x + h) + h * B * zetaR K x := by
  have h1 : ∑ n ∈ Finset.Icc 1 Y, (acoef K n : ℝ) / (n : ℝ) ^ x
      - ∑ n ∈ Finset.Icc 1 Y, (acoef K n : ℝ) / (n : ℝ) ^ (x + h)
      ≤ h * ∑ n ∈ Finset.Icc 1 Y, (acoef K n : ℝ) * (Real.log n * (n : ℝ) ^ (-x)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have e1 : (n : ℝ) ^ (x + h) = (n : ℝ) ^ x * (n : ℝ) ^ h := Real.rpow_add hnpos x h
    have hxpos : 0 < (n : ℝ) ^ x := Real.rpow_pos_of_pos hnpos x
    have hhpos : 0 < (n : ℝ) ^ h := Real.rpow_pos_of_pos hnpos h
    have e2 : (n : ℝ) ^ (-x) = ((n : ℝ) ^ x)⁻¹ := Real.rpow_neg hnpos.le x
    have key : 1 - ((n : ℝ) ^ h)⁻¹ ≤ h * Real.log n := by
      have h3 : ((n : ℝ) ^ h)⁻¹ = Real.exp (-(h * Real.log n)) := by
        rw [Real.rpow_def_of_pos hnpos, ← Real.exp_neg]
        congr 1
        ring
      rw [h3]
      have := Real.add_one_le_exp (-(h * Real.log n))
      linarith
    rw [e1, e2]
    have e3 : (acoef K n : ℝ) / (n : ℝ) ^ x - (acoef K n : ℝ) / ((n : ℝ) ^ x * (n : ℝ) ^ h)
        = (acoef K n : ℝ) * ((n : ℝ) ^ x)⁻¹ * (1 - ((n : ℝ) ^ h)⁻¹) := by
      field_simp
    rw [e3]
    have hnn : 0 ≤ (acoef K n : ℝ) * ((n : ℝ) ^ x)⁻¹ := by positivity
    calc (acoef K n : ℝ) * ((n : ℝ) ^ x)⁻¹ * (1 - ((n : ℝ) ^ h)⁻¹)
        ≤ (acoef K n : ℝ) * ((n : ℝ) ^ x)⁻¹ * (h * Real.log n) :=
          mul_le_mul_of_nonneg_left key hnn
      _ = h * ((acoef K n : ℝ) * (Real.log n * ((n : ℝ) ^ x)⁻¹)) := by ring
  have h2 : ∑ I ∈ idealsLe K Y, Real.log (Ideal.absNorm I) * ((Ideal.absNorm I : ℝ)) ^ (-x)
      = ∑ n ∈ Finset.Icc 1 Y, (acoef K n : ℝ) * (Real.log n * (n : ℝ) ^ (-x)) :=
    sum_idealsLe_eq K Y (fun n => Real.log n * (n : ℝ) ^ (-x))
  have h3 := sum_log_le K Y x
  have h4 := sum_le_zetaR K Y x hx
  have hP0 : 0 ≤ ∑ P ∈ primesLe K Y, ∑ j ∈ Finset.Icc 1 Y,
      Real.log (Ideal.absNorm P) * (((Ideal.absNorm P : ℝ)) ^ j) ^ (-x) :=
    Finset.sum_nonneg (fun P _ => Finset.sum_nonneg (fun j _ =>
      mul_nonneg (Real.log_natCast_nonneg _) (Real.rpow_nonneg (by positivity) _)))
  have hJ0 : 0 ≤ ∑ J ∈ idealsLe K Y, ((Ideal.absNorm J : ℝ)) ^ (-x) :=
    Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have h5 : ∑ n ∈ Finset.Icc 1 Y, (acoef K n : ℝ) * (Real.log n * (n : ℝ) ^ (-x))
      ≤ B * zetaR K x := by
    rw [← h2]
    exact h3.trans (mul_le_mul hB h4 hJ0 (hP0.trans hB))
  have h6 := mul_le_mul_of_nonneg_left h5 hh.le
  linarith

end idealsums

/-- Primes `p ≡ 1 (mod 3)`, `p ∤ 3c`, modulo which `c` is a cube. -/
def Psplit (c : ℤ) (p : ℕ) : Prop :=
  p.Prime ∧ p % 3 = 1 ∧ ¬ (p : ℤ) ∣ 3 * c ∧ ∃ r : ℤ, (p : ℤ) ∣ r ^ 3 - c

lemma geom_tail_le (b : ℝ) (hb : 2 ≤ b) (m Y : ℕ) :
    ∑ j ∈ Finset.Ico m Y, (b⁻¹) ^ j ≤ 2 * (b⁻¹) ^ m := by
  have hbpos : 0 < b := by linarith
  have h0 : 0 ≤ b⁻¹ := by positivity
  have h1 : b⁻¹ ≤ 1 / 2 := by
    rw [inv_le_comm₀ hbpos (by norm_num)]
    norm_num
    exact hb
  have h2 := geom_sum_Ico_le_of_lt_one (m := m) (n := Y) h0 (by linarith : b⁻¹ < 1)
  refine h2.trans ?_
  rw [div_le_iff₀ (by linarith)]
  have : 0 ≤ (b⁻¹) ^ m := by positivity
  nlinarith

open Classical in
/-- The per-prime majorant of the prime-ideal sum. -/
noncomputable def Gmaj (c : ℤ) (x : ℝ) (p : ℕ) : ℝ :=
  18 * Real.log p / (p : ℝ) ^ 2 + (if (p : ℤ) ∣ 3 * c then 3 * Real.log p else 0)
    + (if p % 3 = 2 then Real.log p * (p : ℝ) ^ (-x) else 0)
    + 3 * (if Psplit c p then Real.log p * (p : ℝ) ^ (-x) else 0)

section split2

variable (c : ℤ) [hirr : Fact (Irreducible (fpoly c))]

lemma primeIdeal_term_le (P : Ideal (𝓞 (Kc c))) (hP : P.IsPrime) (p : ℕ) (hp : p.Prime)
    (hpP : ((p : ℤ) : 𝓞 (Kc c)) ∈ P) (Y : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    ∑ j ∈ Finset.Icc 1 Y, Real.log (Ideal.absNorm P) * (((Ideal.absNorm P : ℝ)) ^ j) ^ (-x)
      ≤ (if Ideal.absNorm P = p then Real.log p * (p : ℝ) ^ (-x) else 0)
        + 6 * Real.log p / (p : ℝ) ^ 2 := by
  obtain ⟨f, hf1, hf3, hf⟩ := absNorm_eq_pow c P hP.ne_top p hp hpP
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hterm : ∀ (q : ℝ), 1 ≤ q → ∀ j : ℕ, (q ^ j) ^ (-x) ≤ (q⁻¹) ^ j := by
    intro q hq j
    have h1 : (1 : ℝ) ≤ q ^ j := one_le_pow₀ hq
    calc (q ^ j) ^ (-x) ≤ (q ^ j) ^ (-1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
      _ = (q⁻¹) ^ j := by rw [Real.rpow_neg_one, inv_pow]
  have hIcc : Finset.Icc 1 Y = Finset.Ico 1 (Y + 1) := by
    ext j
    rw [Finset.mem_Icc, Finset.mem_Ico]
    omega
  by_cases hf1' : f = 1
  · have hN : Ideal.absNorm P = p := by rw [hf, hf1', pow_one]
    rw [if_pos hN, hN]
    have hsub : Finset.Icc 1 Y ⊆ insert 1 (Finset.Ico 2 (Y + 1)) := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [Finset.mem_insert, Finset.mem_Ico]
      omega
    have hnn : ∀ j : ℕ, 0 ≤ Real.log p * (((p : ℝ)) ^ j) ^ (-x) :=
      fun j => mul_nonneg hlogp (Real.rpow_nonneg (by positivity) _)
    have htail : ∑ j ∈ Finset.Ico 2 (Y + 1), Real.log p * (((p : ℝ)) ^ j) ^ (-x)
        ≤ Real.log p * (2 * ((p : ℝ)⁻¹) ^ 2) := by
      rw [← Finset.mul_sum]
      apply mul_le_mul_of_nonneg_left _ hlogp
      calc ∑ j ∈ Finset.Ico 2 (Y + 1), (((p : ℝ)) ^ j) ^ (-x)
          ≤ ∑ j ∈ Finset.Ico 2 (Y + 1), ((p : ℝ)⁻¹) ^ j :=
            Finset.sum_le_sum (fun j _ => hterm p (by linarith) j)
        _ ≤ 2 * ((p : ℝ)⁻¹) ^ 2 := geom_tail_le p hp2 2 (Y + 1)
    have e : Real.log p * (2 * ((p : ℝ)⁻¹) ^ 2) = 2 * Real.log p / (p : ℝ) ^ 2 := by
      rw [inv_pow]; ring
    have h6 : 2 * Real.log p / (p : ℝ) ^ 2 ≤ 6 * Real.log p / (p : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      linarith
    calc ∑ j ∈ Finset.Icc 1 Y, Real.log p * (((p : ℝ)) ^ j) ^ (-x)
        ≤ ∑ j ∈ insert 1 (Finset.Ico 2 (Y + 1)), Real.log p * (((p : ℝ)) ^ j) ^ (-x) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => hnn j)
      _ = Real.log p * (((p : ℝ)) ^ 1) ^ (-x)
            + ∑ j ∈ Finset.Ico 2 (Y + 1), Real.log p * (((p : ℝ)) ^ j) ^ (-x) := by
          rw [Finset.sum_insert]
          simp
      _ ≤ Real.log p * (p : ℝ) ^ (-x) + 6 * Real.log p / (p : ℝ) ^ 2 := by
          rw [pow_one]
          linarith
  · have hf2 : 2 ≤ f := by omega
    have hNne : Ideal.absNorm P ≠ p := by
      rw [hf]
      intro h
      exact hf1' (Nat.pow_right_injective hp.two_le (h.trans (pow_one p).symm))
    rw [if_neg hNne, zero_add]
    have hq : ((Ideal.absNorm P : ℕ) : ℝ) = (p : ℝ) ^ f := by rw [hf]; push_cast; rfl
    have hq1 : (1 : ℝ) ≤ (p : ℝ) ^ f := one_le_pow₀ (by linarith)
    have hlogq : Real.log (Ideal.absNorm P) ≤ 3 * Real.log p := by
      rw [hq, Real.log_pow]
      have : (f : ℝ) ≤ 3 := by exact_mod_cast hf3
      nlinarith
    have hb : (2 : ℝ) ≤ (p : ℝ) ^ 2 := by nlinarith
    have hqp : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ f := pow_le_pow_right₀ (by linarith) hf2
    calc ∑ j ∈ Finset.Icc 1 Y,
          Real.log (Ideal.absNorm P) * (((Ideal.absNorm P : ℝ)) ^ j) ^ (-x)
        ≤ ∑ j ∈ Finset.Icc 1 Y, (3 * Real.log p) * (((p : ℝ) ^ 2)⁻¹) ^ j := by
          apply Finset.sum_le_sum
          intro j _
          apply mul_le_mul hlogq _ (Real.rpow_nonneg (by positivity) _) (by positivity)
          rw [hq]
          calc (((p : ℝ) ^ f) ^ j) ^ (-x) ≤ (((p : ℝ) ^ f)⁻¹) ^ j := hterm _ hq1 j
            _ ≤ (((p : ℝ) ^ 2)⁻¹) ^ j := by
                apply pow_le_pow_left₀ (by positivity)
                exact inv_anti₀ (by positivity) hqp
      _ = (3 * Real.log p) * ∑ j ∈ Finset.Ico 1 (Y + 1), (((p : ℝ) ^ 2)⁻¹) ^ j := by
          rw [Finset.mul_sum, hIcc]
      _ ≤ (3 * Real.log p) * (2 * (((p : ℝ) ^ 2)⁻¹) ^ 1) :=
          mul_le_mul_of_nonneg_left (geom_tail_le _ hb 1 (Y + 1)) (by positivity)
      _ = 6 * Real.log p / (p : ℝ) ^ 2 := by rw [pow_one]; ring

open Classical in
/-- A rational prime contained in a nonzero prime ideal. -/
noncomputable def ratPrime (P : Ideal (𝓞 (Kc c))) : ℕ :=
  if h : P.IsPrime ∧ P ≠ ⊥ then Classical.choose (exists_prime_mem c P h.1 h.2) else 0

lemma ratPrime_spec (P : Ideal (𝓞 (Kc c))) (hP : P.IsPrime) (hP0 : P ≠ ⊥) :
    (ratPrime c P).Prime ∧ ((ratPrime c P : ℤ) : 𝓞 (Kc c)) ∈ P := by
  unfold ratPrime
  rw [dif_pos ⟨hP, hP0⟩]
  exact Classical.choose_spec (exists_prime_mem c P hP hP0)

open Classical in
/-- The sum over prime ideal powers is bounded by a sum over rational primes. -/
lemma primeIdeal_sum_le (Y : ℕ) (x : ℝ) (hx : 1 ≤ x) :
    ∑ P ∈ primesLe (Kc c) Y, ∑ j ∈ Finset.Icc 1 Y,
        Real.log (Ideal.absNorm P) * (((Ideal.absNorm P : ℝ)) ^ j) ^ (-x)
      ≤ ∑ p ∈ (Finset.range (Y + 1)).filter Nat.Prime, Gmaj c x p := by
  have hmaps : ∀ P ∈ primesLe (Kc c) Y,
      ratPrime c P ∈ (Finset.range (Y + 1)).filter Nat.Prime := by
    intro P hP
    obtain ⟨⟨hN, hP0⟩, hPp⟩ := (mem_primesLe (Kc c) Y P).mp hP
    obtain ⟨h1, h2⟩ := ratPrime_spec c P hPp hP0
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, h1⟩
    obtain ⟨f, hf1, _, hf⟩ := absNorm_eq_pow c P hPp.ne_top _ h1 h2
    have : ratPrime c P ≤ Ideal.absNorm P := by
      rw [hf]; exact Nat.le_self_pow (by omega) _
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_le_sum
  intro p hp
  obtain ⟨_, hpp⟩ := Finset.mem_filter.mp hp
  unfold Gmaj
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = Real.log p * (p : ℝ) ^ (-x) := ⟨_, rfl⟩
  rw [← hL]
  obtain ⟨s, hs⟩ : ∃ s : Finset (Ideal (𝓞 (Kc c))),
      s = (primesLe (Kc c) Y).filter (fun P => ratPrime c P = p) := ⟨_, rfl⟩
  rw [← hs]
  have hsP : ∀ P ∈ s, P.IsPrime ∧ ((p : ℤ) : 𝓞 (Kc c)) ∈ P := by
    intro P hP
    rw [hs] at hP
    obtain ⟨hP1, hP2⟩ := Finset.mem_filter.mp hP
    obtain ⟨⟨hN, hP0⟩, hPp⟩ := (mem_primesLe (Kc c) Y P).mp hP1
    obtain ⟨h1, h2⟩ := ratPrime_spec c P hPp hP0
    rw [hP2] at h2
    exact ⟨hPp, h2⟩
  have hcard : s.card ≤ 3 := card_primes_over_le c p hpp s hsP
  have hlogp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hL0 : 0 ≤ L := by
    rw [hL]; exact mul_nonneg hlogp (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  have hLle : L ≤ Real.log p := by
    have h1 : (p : ℝ) ^ (-x) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hpp.one_le) (by linarith)
    rw [hL]
    calc Real.log p * (p : ℝ) ^ (-x) ≤ Real.log p * 1 := mul_le_mul_of_nonneg_left h1 hlogp
      _ = Real.log p := mul_one _
  obtain ⟨s', hs'⟩ : ∃ s' : Finset (Ideal (𝓞 (Kc c))),
      s' = s.filter (fun P => Ideal.absNorm P = p) := ⟨_, rfl⟩
  have step1 : ∑ P ∈ s, ∑ j ∈ Finset.Icc 1 Y,
        Real.log (Ideal.absNorm P) * (((Ideal.absNorm P : ℝ)) ^ j) ^ (-x)
      ≤ (s'.card : ℝ) * L + 18 * Real.log p / (p : ℝ) ^ 2 := by
    have h6 : 0 ≤ 6 * Real.log p / (p : ℝ) ^ 2 := by positivity
    calc ∑ P ∈ s, ∑ j ∈ Finset.Icc 1 Y,
          Real.log (Ideal.absNorm P) * (((Ideal.absNorm P : ℝ)) ^ j) ^ (-x)
        ≤ ∑ P ∈ s, ((if Ideal.absNorm P = p then L else 0) + 6 * Real.log p / (p : ℝ) ^ 2) := by
          apply Finset.sum_le_sum
          intro P hP
          have := primeIdeal_term_le c P (hsP P hP).1 p hpp (hsP P hP).2 Y x hx
          rw [← hL] at this
          exact this
      _ = (s'.card : ℝ) * L + (s.card : ℝ) * (6 * Real.log p / (p : ℝ) ^ 2) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← hs', Finset.sum_const,
            Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      _ ≤ (s'.card : ℝ) * L + 18 * Real.log p / (p : ℝ) ^ 2 := by
          have h3 : (s.card : ℝ) ≤ 3 := by exact_mod_cast hcard
          have := mul_le_mul_of_nonneg_right h3 h6
          have e : 3 * (6 * Real.log p / (p : ℝ) ^ 2) = 18 * Real.log p / (p : ℝ) ^ 2 := by ring
          linarith
  have hs'card : s'.card ≤ 3 := by
    rw [hs']; exact (Finset.card_le_card (Finset.filter_subset _ _)).trans hcard
  have hs'P : ∀ P ∈ s', P.IsPrime ∧ ((p : ℤ) : 𝓞 (Kc c)) ∈ P ∧ Ideal.absNorm P = p := by
    intro P hP
    rw [hs'] at hP
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hP
    exact ⟨(hsP P h1).1, (hsP P h1).2, h2⟩
  have hc3 : (s'.card : ℝ) ≤ 3 := by exact_mod_cast hs'card
  have hnn3 : 0 ≤ 3 * (if Psplit c p then L else 0) := by
    split_ifs
    · linarith
    · norm_num
  have hnn2 : 0 ≤ (if p % 3 = 2 then L else 0) := by
    split_ifs
    · exact hL0
    · exact le_rfl
  have key : (s'.card : ℝ) * L ≤ (if (p : ℤ) ∣ 3 * c then 3 * Real.log p else 0)
      + (if p % 3 = 2 then L else 0) + 3 * (if Psplit c p then L else 0) := by
    by_cases h3c : (p : ℤ) ∣ 3 * c
    · rw [if_pos h3c]
      have h1 : (s'.card : ℝ) * L ≤ 3 * Real.log p := by nlinarith
      linarith
    · rw [if_neg h3c, zero_add]
      rcases Finset.eq_empty_or_nonempty s' with hemp | ⟨P₀, hP₀⟩
      · rw [hemp]
        simp only [Finset.card_empty, Nat.cast_zero, zero_mul]
        linarith
      · obtain ⟨hP₀p, hP₀m, hP₀N⟩ := hs'P P₀ hP₀
        obtain ⟨r₀, _, _, hr₀dvd⟩ :=
          exists_root_of_absNorm_prime c P₀ hP₀p.ne_top p hpp hP₀N
        have hmod : p % 3 = 1 ∨ p % 3 = 2 := by
          have h0 : p % 3 ≠ 0 := by
            intro h0
            have h3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
            have h4 : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hpp).mp h3
            apply h3c
            rw [← h4]
            exact dvd_mul_right _ _
          omega
        rcases hmod with h1 | h2
        · have hsp : Psplit c p := ⟨hpp, h1, h3c, r₀, hr₀dvd⟩
          rw [if_neg (by omega), if_pos hsp, zero_add]
          nlinarith
        · rw [if_pos h2]
          have hc1 : s'.card ≤ 1 := by
            rw [Finset.card_le_one]
            intro P₁ hP₁ P₂ hP₂
            obtain ⟨h1p, h1m, h1N⟩ := hs'P P₁ hP₁
            obtain ⟨h2p, h2m, h2N⟩ := hs'P P₂ hP₂
            obtain ⟨r₁, _, hr₁mem, hr₁dvd⟩ :=
              exists_root_of_absNorm_prime c P₁ h1p.ne_top p hpp h1N
            obtain ⟨r₂, _, hr₂mem, hr₂dvd⟩ :=
              exists_root_of_absNorm_prime c P₂ h2p.ne_top p hpp h2N
            have hd : (p : ℤ) ∣ (r₁ : ℤ) ^ 3 - (r₂ : ℤ) ^ 3 := by
              have := dvd_sub hr₁dvd hr₂dvd
              have e : (r₁ : ℤ) ^ 3 - c - ((r₂ : ℤ) ^ 3 - c) = (r₁ : ℤ) ^ 3 - (r₂ : ℤ) ^ 3 := by
                ring
              rwa [e] at this
            obtain ⟨k, hk⟩ := prime_dvd_sub_of_dvd_cube_sub p hpp h2 _ _ hd
            have hmem2 : (((r₁ : ℕ) : ℤ) : 𝓞 (Kc c)) - thetaO c ∈ P₂ := by
              have e : (((r₁ : ℕ) : ℤ) : 𝓞 (Kc c)) - thetaO c
                  = ((((r₂ : ℕ) : ℤ) : 𝓞 (Kc c)) - thetaO c)
                    + ((p : ℤ) : 𝓞 (Kc c)) * ((k : ℤ) : 𝓞 (Kc c)) := by
                have h9 : ((r₁ : ℕ) : ℤ) = (r₂ : ℤ) + p * k := by linarith
                rw [h9]
                push_cast
                ring
              rw [e]
              exact P₂.add_mem hr₂mem (P₂.mul_mem_right _ h2m)
            exact prime_unique_of_root c P₁ P₂ h1p h2p p hpp h1N h2N h3c _ hr₁mem hmem2
          have hc1' : (s'.card : ℝ) ≤ 1 := by exact_mod_cast hc1
          nlinarith
  linarith

end split2

section upper

open ArithmeticFunction ArithmeticFunction.vonMangoldt Complex LSeries DirichletCharacter


/-- Upper-bound companion of Mathlib's `LSeries_residueClass_lower_bound`. -/
lemma residueClass_upper_bound {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
    ∃ C : ℝ, ∀ {x : ℝ} (_ : x ∈ Set.Ioc 1 2),
      ∑' n, residueClass a n / (n : ℝ) ^ x ≤ (q.totient : ℝ)⁻¹ / (x - 1) + C := by
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, residueClass a n / (n : ℝ) ^ x =
        (LFunctionResidueClassAux a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
    refine ofReal_injective ?_
    simp only [ofReal_tsum, ofReal_div, ofReal_cpow (Nat.cast_nonneg _), ofReal_natCast,
      ofReal_add, ofReal_inv, ofReal_sub, ofReal_one]
    simp_rw [← LFunctionResidueClassAux_real ha hx,
      eqOn_LFunctionResidueClassAux ha <| Set.mem_ofPred.mpr (ofReal_re x ▸ hx), sub_add_cancel,
      LSeries, term]
    refine tsum_congr fun n ↦ ?_
    split_ifs with hn
    · simp only [hn, residueClass_apply_zero, ofReal_zero, zero_div]
    · rfl
  have : ContinuousOn (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) (Set.Icc 1 2) :=
    continuous_re.continuousOn.comp (t := Set.univ) (continuousOn_LFunctionResidueClassAux a)
      (fun ⦃x⦄ a ↦ trivial) |>.comp continuous_ofReal.continuousOn fun x hx ↦ by
        simpa only [Set.mem_ofPred_eq, ofReal_re] using hx.1
  obtain ⟨C, hC⟩ := bddAbove_def.mp <| IsCompact.bddAbove_image isCompact_Icc this
  replace hC {x : ℝ} (hx : x ∈ Set.Icc 1 2) : (LFunctionResidueClassAux a x).re ≤ C :=
    hC (LFunctionResidueClassAux a x).re <|
      Set.mem_image_of_mem (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) hx
  refine ⟨C, fun {x} hx ↦ ?_⟩
  rw [H hx.1, add_comm]
  have := hC (Set.mem_Icc_of_Ioc hx)
  linarith

end upper

lemma sumS1 (s : Finset ℕ) :
    ∑ p ∈ s, 18 * Real.log p / (p : ℝ) ^ 2 ≤ ∑' n : ℕ, 36 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
  have hsum : Summable (fun n : ℕ => 36 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
    (Real.summable_nat_rpow_inv.mpr (by norm_num)).mul_left 36
  have hterm : ∀ n : ℕ, 18 * Real.log n / (n : ℝ) ^ 2 ≤ 36 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
      have h1 := Real.log_le_rpow_div hnpos.le (by norm_num : (0 : ℝ) < 1 / 2)
      have h1' : Real.log n ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := h1.trans (le_of_eq (by ring))
      have h2 : (n : ℝ) ^ 2 = (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_add hnpos, show (1 / 2 : ℝ) + 3 / 2 = (2 : ℕ) by norm_num,
          Real.rpow_natCast]
      have h3 : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hnpos _
      have h4 : 0 < (n : ℝ) ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hnpos _
      rw [h2, div_le_iff₀ (by positivity)]
      have e : 36 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ * ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (3 / 2 : ℝ))
          = 36 * (n : ℝ) ^ (1 / 2 : ℝ) := by field_simp
      rw [e]
      linarith
  calc ∑ p ∈ s, 18 * Real.log p / (p : ℝ) ^ 2
      ≤ ∑ p ∈ s, 36 * ((p : ℝ) ^ (3 / 2 : ℝ))⁻¹ := Finset.sum_le_sum (fun p _ => hterm p)
    _ ≤ ∑' n : ℕ, 36 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ :=
        hsum.sum_le_tsum s (fun n _ => by positivity)

lemma sumS2 (c : ℤ) (hc0 : c ≠ 0) (s : Finset ℕ) :
    ∑ p ∈ s, (if (p : ℤ) ∣ 3 * c then 3 * Real.log p else 0)
      ≤ ∑ p ∈ Finset.range (3 * c.natAbs + 1), 3 * Real.log p := by
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨h1, h2⟩ := Finset.mem_filter.mp hp
    rw [Finset.mem_range]
    have h3 : p ∣ (3 * c).natAbs := Int.natCast_dvd.mp h2
    have h4 : (3 * c).natAbs = 3 * c.natAbs := by rw [Int.natAbs_mul]; rfl
    have h5 : 0 < c.natAbs := Int.natAbs_pos.mpr hc0
    rw [h4] at h3
    have := Nat.le_of_dvd (by omega) h3
    omega
  · intro p _ _
    have := Real.log_natCast_nonneg p
    positivity

lemma sumS3 (x : ℝ) (hx : 1 < x) (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, (if p % 3 = 2 then Real.log p * (p : ℝ) ^ (-x) else 0)
      ≤ ∑' n : ℕ, ArithmeticFunction.vonMangoldt.residueClass (2 : ZMod 3) n / (n : ℝ) ^ x := by
  have hsum : Summable (fun n : ℕ =>
      ArithmeticFunction.vonMangoldt.residueClass (2 : ZMod 3) n / (n : ℝ) ^ x) :=
    LSeries.summable_real_of_abscissaOfAbsConv_lt
      ((ArithmeticFunction.vonMangoldt.abscissaOfAbsConv_residueClass_le_one (2 : ZMod 3)).trans_lt
        (by exact_mod_cast hx))
  have hnn : ∀ n : ℕ,
      0 ≤ ArithmeticFunction.vonMangoldt.residueClass (2 : ZMod 3) n / (n : ℝ) ^ x :=
    fun n => div_nonneg (ArithmeticFunction.vonMangoldt.residueClass_nonneg _ n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  calc ∑ p ∈ s, (if p % 3 = 2 then Real.log p * (p : ℝ) ^ (-x) else 0)
      ≤ ∑ p ∈ s, ArithmeticFunction.vonMangoldt.residueClass (2 : ZMod 3) p / (p : ℝ) ^ x := by
        apply Finset.sum_le_sum
        intro p hp
        split_ifs with h2
        · have hpp := hs p hp
          have h3 : ((p : ℕ) : ZMod 3) = 2 := by
            have : ((p : ℕ) : ZMod 3) = ((2 : ℕ) : ZMod 3) :=
              (ZMod.natCast_eq_natCast_iff' p 2 3).mpr (by omega)
            simpa using this
          have h4 : ArithmeticFunction.vonMangoldt.residueClass (2 : ZMod 3) p = Real.log p := by
            rw [ArithmeticFunction.vonMangoldt.residueClass,
              Set.indicator_of_mem (show p ∈ {n : ℕ | (n : ZMod 3) = 2} from h3)]
            exact ArithmeticFunction.vonMangoldt_apply_prime hpp
          rw [h4, Real.rpow_neg (Nat.cast_nonneg p), div_eq_mul_inv]
        · exact hnn p
    _ ≤ _ := hsum.sum_le_tsum s (fun n _ => hnn n)

open Classical in
lemma sumS4 (c : ℤ) (x : ℝ) (hx : 1 < x) (z : ℕ) (τ : ℝ)
    (hsum : Summable (fun p : ℕ => if Psplit c p then (1 : ℝ) / p else 0))
    (hz : ∑' p : ℕ, (if Psplit c p then (1 : ℝ) / p else 0)
        - ∑ p ∈ Finset.range z, (if Psplit c p then (1 : ℝ) / p else 0) ≤ τ)
    (Y : ℕ) (s : Finset ℕ) (hs : s ⊆ Finset.range (Y + 1)) :
    ∑ p ∈ s, (if Psplit c p then Real.log p * (p : ℝ) ^ (-x) else 0)
      ≤ ∑ p ∈ Finset.range z, Real.log p + (1 / (x - 1)) * τ := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = fun p : ℕ => if Psplit c p then (1 : ℝ) / p else 0 :=
    ⟨_, rfl⟩
  rw [← hg] at hsum hz
  have hg0 : ∀ p, 0 ≤ g p := by
    intro p
    rw [hg]
    dsimp only
    split_ifs
    · positivity
    · exact le_rfl
  have hδ : 0 < x - 1 := by linarith
  have hterm : ∀ p : ℕ, (if Psplit c p then Real.log p * (p : ℝ) ^ (-x) else 0)
      ≤ (if p < z then Real.log p else 0) + (1 / (x - 1)) * (if z ≤ p then g p else 0) := by
    intro p
    by_cases hsp : Psplit c p
    · rw [if_pos hsp]
      have hpp := hsp.1
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_le
      have hppos : (0 : ℝ) < p := by linarith
      have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1
      by_cases hpz : p < z
      · rw [if_pos hpz, if_neg (by omega), mul_zero, add_zero]
        have h1 : (p : ℝ) ^ (-x) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
        calc Real.log p * (p : ℝ) ^ (-x) ≤ Real.log p * 1 := mul_le_mul_of_nonneg_left h1 hlog
          _ = Real.log p := mul_one _
      · rw [if_neg hpz, if_pos (by omega), zero_add]
        have hgp : g p = 1 / (p : ℝ) := by
          rw [hg]
          dsimp only
          rw [if_pos hsp]
        rw [hgp]
        have e : (p : ℝ) ^ (-x) = (p : ℝ) ^ (-(x - 1)) * (p : ℝ)⁻¹ := by
          rw [← Real.rpow_neg_one (p : ℝ), ← Real.rpow_add hppos]
          congr 1
          ring
        have h1 := Real.log_le_rpow_div hppos.le hδ
        have h2 : (p : ℝ) ^ (-(x - 1)) = ((p : ℝ) ^ (x - 1))⁻¹ := Real.rpow_neg hppos.le _
        have h3 : 0 < (p : ℝ) ^ (x - 1) := Real.rpow_pos_of_pos hppos _
        have h4 : Real.log p * (p : ℝ) ^ (-(x - 1)) ≤ 1 / (x - 1) := by
          rw [h2, ← div_eq_mul_inv, div_le_iff₀ h3]
          calc Real.log p ≤ (p : ℝ) ^ (x - 1) / (x - 1) := h1
            _ = 1 / (x - 1) * (p : ℝ) ^ (x - 1) := by ring
        rw [e]
        calc Real.log p * ((p : ℝ) ^ (-(x - 1)) * (p : ℝ)⁻¹)
            = (Real.log p * (p : ℝ) ^ (-(x - 1))) * (p : ℝ)⁻¹ := by ring
          _ ≤ (1 / (x - 1)) * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h4 (by positivity)
          _ = 1 / (x - 1) * (1 / (p : ℝ)) := by ring
    · rw [if_neg hsp]
      have h1 : 0 ≤ (if p < z then Real.log p else 0) := by
        split_ifs
        · exact Real.log_natCast_nonneg p
        · exact le_rfl
      have h2 : 0 ≤ (1 / (x - 1)) * (if z ≤ p then g p else 0) := by
        apply mul_nonneg (by positivity)
        split_ifs
        · exact hg0 p
        · exact le_rfl
      linarith
  have hA : ∑ p ∈ Finset.range (Y + 1), (if p < z then Real.log p else 0)
      ≤ ∑ p ∈ Finset.range z, Real.log p := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_range]
      exact hp.2
    · intro p _ _
      exact Real.log_natCast_nonneg p
  have hB : ∑ p ∈ Finset.range (Y + 1), (if z ≤ p then g p else 0) ≤ τ := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = max (Y + 1) z := ⟨_, rfl⟩
    have hN1 : Y + 1 ≤ N := by rw [hN]; exact le_max_left _ _
    have hN2 : z ≤ N := by rw [hN]; exact le_max_right _ _
    have e1 : ∀ p : ℕ, (if z ≤ p then g p else 0) + (if p < z then g p else 0) = g p := by
      intro p
      by_cases h : p < z
      · rw [if_neg (by omega), if_pos h, zero_add]
      · rw [if_pos (by omega), if_neg h, add_zero]
    have h1 : ∑ p ∈ Finset.range (Y + 1), (if z ≤ p then g p else 0)
        ≤ ∑ p ∈ Finset.range N, (if z ≤ p then g p else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN1)
      intro p _ _
      split_ifs
      · exact hg0 p
      · exact le_rfl
    have h2 : ∑ p ∈ Finset.range z, g p
        = ∑ p ∈ Finset.range N, (if p < z then g p else 0) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext p
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    have h3 : ∑ p ∈ Finset.range N, (if z ≤ p then g p else 0)
        + ∑ p ∈ Finset.range N, (if p < z then g p else 0) = ∑ p ∈ Finset.range N, g p := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun p _ => e1 p)
    have h4 : ∑ p ∈ Finset.range N, g p ≤ ∑' p, g p :=
      hsum.sum_le_tsum _ (fun p _ => hg0 p)
    linarith
  calc ∑ p ∈ s, (if Psplit c p then Real.log p * (p : ℝ) ^ (-x) else 0)
      ≤ ∑ p ∈ Finset.range (Y + 1),
          (if Psplit c p then Real.log p * (p : ℝ) ^ (-x) else 0) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hs
        intro p _ _
        split_ifs
        · exact mul_nonneg (Real.log_natCast_nonneg p) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
        · exact le_rfl
    _ ≤ ∑ p ∈ Finset.range (Y + 1), ((if p < z then Real.log p else 0)
          + (1 / (x - 1)) * (if z ≤ p then g p else 0)) :=
        Finset.sum_le_sum (fun p _ => hterm p)
    _ = ∑ p ∈ Finset.range (Y + 1), (if p < z then Real.log p else 0)
          + (1 / (x - 1)) * ∑ p ∈ Finset.range (Y + 1), (if z ≤ p then g p else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ p ∈ Finset.range z, Real.log p + (1 / (x - 1)) * τ := by
        have := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 1 / (x - 1))
        linarith

open Classical in
/-- **Block L4.** For a non-cube `c`, the primes `p ≡ 1 (mod 3)` modulo which `c` is a cube
have a divergent sum of reciprocals. -/
theorem split_not_summable (c : ℤ) (hc : ¬ ∃ m : ℤ, m ^ 3 = c) :
    ¬ Summable (fun p : ℕ => if Psplit c p then (1 : ℝ) / p else 0) := by
  intro hsum
  have : Fact (Irreducible (fpoly c)) := ⟨fpoly_irreducible c hc⟩
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc ⟨0, by norm_num⟩
  have hκpos := NumberField.dedekindZeta_residue_pos (Kc c)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = NumberField.dedekindZeta_residue (Kc c) := ⟨_, rfl⟩
  rw [← hκ] at hκpos
  have ht := tendsto_zetaR (Kc c)
  rw [← hκ] at ht
  obtain ⟨η, hη, hηb⟩ : ∃ η > 0, ∀ y : ℝ, 1 < y → y < 1 + η →
      |(y - 1) * zetaR (Kc c) y - κ| < κ / 100 := by
    rw [Metric.tendsto_nhdsWithin_nhds] at ht
    obtain ⟨η, hη, h⟩ := ht (κ / 100) (by positivity)
    refine ⟨η, hη, fun y hy1 hy2 => ?_⟩
    have := h (Set.mem_Ioi.mpr hy1) (by rw [Real.dist_eq, abs_lt]; constructor <;> linarith)
    rwa [Real.dist_eq] at this
  obtain ⟨z, hz⟩ : ∃ z : ℕ, ∑' p : ℕ, (if Psplit c p then (1 : ℝ) / p else 0)
      - ∑ p ∈ Finset.range z, (if Psplit c p then (1 : ℝ) / p else 0) ≤ 1 / 100 := by
    have h1 := hsum.hasSum.tendsto_sum_nat
    have h2 := h1.eventually (lt_mem_nhds
      (show ∑' p : ℕ, (if Psplit c p then (1 : ℝ) / p else 0) - 1 / 100
        < ∑' p : ℕ, (if Psplit c p then (1 : ℝ) / p else 0) by linarith))
    obtain ⟨z, hz⟩ := h2.exists
    exact ⟨z, by linarith⟩
  obtain ⟨C₅, hC₅⟩ := residueClass_upper_bound (q := 3) (a := (2 : ZMod 3))
    (isUnit_iff_exists_inv.mpr ⟨2, by decide⟩)
  obtain ⟨Ca, hCa⟩ : ∃ Ca : ℝ, Ca = ∑' n : ℕ, 36 * ((n : ℝ) ^ (3 / 2 : ℝ))⁻¹ := ⟨_, rfl⟩
  obtain ⟨Cb, hCb⟩ : ∃ Cb : ℝ, Cb = ∑ p ∈ Finset.range (3 * c.natAbs + 1), 3 * Real.log p :=
    ⟨_, rfl⟩
  obtain ⟨Cz, hCz⟩ : ∃ Cz : ℝ, Cz = ∑ p ∈ Finset.range z, Real.log p := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max 1 (Ca + Cb + C₅ + 3 * Cz) := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by rw [hC]; exact le_max_left _ _
  have hC2 : Ca + Cb + C₅ + 3 * Cz ≤ C := by rw [hC]; exact le_max_right _ _
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (η / 2) (min (1 / 2) (1 / (100 * C))) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδ]
    refine lt_min (by positivity) (lt_min (by norm_num) (by positivity))
  have hδ1 : δ ≤ η / 2 := by rw [hδ]; exact min_le_left _ _
  have hδ2 : δ ≤ 1 / 2 := by rw [hδ]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδ3 : δ ≤ 1 / (100 * C) := by rw [hδ]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hδC : δ * C ≤ 1 / 100 := by
    have h1 : δ * C ≤ 1 / (100 * C) * C := mul_le_mul_of_nonneg_right hδ3 (by linarith)
    have e : 1 / (100 * C) * C = 1 / 100 := by field_simp
    linarith
  obtain ⟨x, hx⟩ : ∃ x : ℝ, x = 1 + δ := ⟨_, rfl⟩
  obtain ⟨h, hh⟩ : ∃ h : ℝ, h = δ / 2 := ⟨_, rfl⟩
  have hx1 : 1 < x := by linarith
  have hx2 : x ≤ 2 := by linarith
  have hhpos : 0 < h := by rw [hh]; positivity
  have ex : x - 1 = δ := by rw [hx]; ring
  have exh : x + h - 1 = 3 / 2 * δ := by rw [hx, hh]; ring
  have hu := hηb x hx1 (by linarith)
  have hv := hηb (x + h) (by linarith) (by rw [hx, hh]; linarith)
  rw [abs_lt, ex] at hu
  rw [abs_lt, exh] at hv
  obtain ⟨ζ1, hζ1⟩ : ∃ ζ1 : ℝ, ζ1 = zetaR (Kc c) x := ⟨_, rfl⟩
  obtain ⟨ζ2, hζ2⟩ : ∃ ζ2 : ℝ, ζ2 = zetaR (Kc c) (x + h) := ⟨_, rfl⟩
  rw [← hζ1] at hu
  rw [← hζ2] at hv
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = C + 53 / 100 / δ := ⟨_, rfl⟩
  have hPB : ∀ Y : ℕ, ∑ P ∈ primesLe (Kc c) Y, ∑ j ∈ Finset.Icc 1 Y,
      Real.log (Ideal.absNorm P) * (((Ideal.absNorm P : ℝ)) ^ j) ^ (-x) ≤ B := by
    intro Y
    refine (primeIdeal_sum_le c Y x hx1.le).trans ?_
    obtain ⟨s, hs⟩ : ∃ s : Finset ℕ, s = (Finset.range (Y + 1)).filter Nat.Prime := ⟨_, rfl⟩
    rw [← hs]
    have hsP : ∀ p ∈ s, p.Prime := fun p hp => by
      rw [hs] at hp; exact (Finset.mem_filter.mp hp).2
    have h1 := sumS1 s
    have h2 := sumS2 c hc0 s
    have h3 := (sumS3 x hx1 s hsP).trans (hC₅ ⟨hx1, hx2⟩)
    have h4 := sumS4 c x hx1 z (1 / 100) hsum hz Y s (by rw [hs]; exact Finset.filter_subset _ _)
    unfold Gmaj
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
    have e3 : ((Nat.totient 3 : ℕ) : ℝ)⁻¹ / (x - 1) = 1 / 2 / δ := by
      rw [Nat.totient_prime Nat.prime_three, ex]
      norm_num
    rw [e3] at h3
    rw [ex] at h4
    have e5 : 1 / 2 / δ + 3 * (1 / δ * (1 / 100)) = 53 / 100 / δ := by
      field_simp
      ring
    rw [← hCa] at h1
    rw [← hCb] at h2
    rw [← hCz] at h4
    rw [hB]
    linarith
  have hmain : ζ1 ≤ ζ2 + h * B * ζ1 := by
    have hf0 : ∀ n : ℕ, 0 ≤ (acoef (Kc c) n : ℝ) / (n : ℝ) ^ x :=
      fun n => div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    rw [hζ1]
    apply Real.tsum_le_of_sum_range_le hf0
    intro N
    have h1 := zeta_diff_le (Kc c) N x h B hx1 hhpos (hPB N)
    have h2 : ∑ n ∈ Finset.Icc 1 N, (acoef (Kc c) n : ℝ) / (n : ℝ) ^ (x + h) ≤ ζ2 := by
      rw [hζ2]
      exact (summable_zetaR (Kc c) (x + h) (by linarith)).sum_le_tsum _
        (fun n _ => div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    have h3 : ∑ n ∈ Finset.range N, (acoef (Kc c) n : ℝ) / (n : ℝ) ^ x
        ≤ ∑ n ∈ Finset.Icc 1 N, (acoef (Kc c) n : ℝ) / (n : ℝ) ^ x := by
      rw [← Finset.sum_filter_of_ne (p := fun n => n ≠ 0)]
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro n hn
          rw [Finset.mem_filter, Finset.mem_range] at hn
          rw [Finset.mem_Icc]
          omega
        · intro n _ _
          exact hf0 n
      · intro n _ hne h0
        apply hne
        rw [h0]
        have : (0 : ℝ) ^ x = 0 := Real.zero_rpow (by linarith)
        simp [this]
    rw [← hζ1] at h1 ⊢
    linarith
  have e6 : δ * (h * B * ζ1) = (δ * C / 2 + 53 / 200) * (δ * ζ1) := by
    rw [hh, hB]
    field_simp
    ring
  have h7 := mul_le_mul_of_nonneg_left hmain hδpos.le
  rw [mul_add, e6] at h7
  have hζpos : 0 ≤ δ * ζ1 := by linarith [hu.1]
  have h8 : (δ * C / 2 + 53 / 200) * (δ * ζ1) ≤ (1 / 200 + 53 / 200) * (δ * ζ1) := by
    apply mul_le_mul_of_nonneg_right _ hζpos
    linarith
  linarith [hu.1, hu.2, hv.1, hv.2]

end splitprimes



section roots

/-- Cube roots of `c` modulo `d`, as natural numbers below `d`. -/
def rootsMod (c : ℤ) (d : ℕ) : Finset ℕ :=
  (Finset.range d).filter (fun r => (d : ℤ) ∣ (r : ℤ) ^ 3 - c)

/-- Number of cube roots of `c` modulo `d`. -/
def nu (c : ℤ) (d : ℕ) : ℕ := (rootsMod c d).card

lemma mem_rootsMod (c : ℤ) (d r : ℕ) :
    r ∈ rootsMod c d ↔ r < d ∧ (d : ℤ) ∣ (r : ℤ) ^ 3 - c := by
  simp [rootsMod]

lemma dvd_cube_sub_congr (k a b c : ℤ) (h : k ∣ a - b) : k ∣ a ^ 3 - c ↔ k ∣ b ^ 3 - c := by
  apply dvd_iff_dvd_of_dvd_sub
  have e : a ^ 3 - c - (b ^ 3 - c) = (a - b) * (a ^ 2 + a * b + b ^ 2) := by ring
  rw [e]
  exact dvd_mul_of_dvd_left h _

lemma natCast_mod_sub (r k : ℕ) : (k : ℤ) ∣ ((r % k : ℕ) : ℤ) - (r : ℤ) := by
  refine ⟨-((r / k : ℕ) : ℤ), ?_⟩
  have h3 : ((r % k : ℕ) : ℤ) + (k : ℤ) * ((r / k : ℕ) : ℤ) = (r : ℤ) := by
    exact_mod_cast Nat.mod_add_div r k
  linarith

lemma mod_mem_rootsMod (c : ℤ) (k n r : ℕ) (hk : 0 < k) (hkn : k ∣ n) (hr : r ∈ rootsMod c n) :
    r % k ∈ rootsMod c k := by
  rw [mem_rootsMod] at hr ⊢
  refine ⟨Nat.mod_lt r hk, ?_⟩
  have h1 : (k : ℤ) ∣ (r : ℤ) ^ 3 - c := dvd_trans (by exact_mod_cast hkn) hr.2
  exact (dvd_cube_sub_congr _ _ _ c (natCast_mod_sub r k)).mpr h1

lemma eq_of_modEq_of_lt {n a b : ℕ} (h : a ≡ b [MOD n]) (ha : a < n) (hb : b < n) : a = b := by
  have h' : a % n = b % n := h
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h'

/-- Chinese remainder theorem for the cube roots. -/
lemma crt_roots (c : ℤ) (k m : ℕ) (hk : 0 < k) (hm : 0 < m) (hcop : Nat.Coprime k m)
    (f : ℕ → ℕ → ℂ) :
    ∑ r ∈ rootsMod c (k * m), f (r % k) (r % m)
      = ∑ r₁ ∈ rootsMod c k, ∑ r₂ ∈ rootsMod c m, f r₁ r₂ := by
  rw [← Finset.sum_product']
  apply Finset.sum_bij (fun r _ => (r % k, r % m))
  · intro r hr
    rw [Finset.mem_product]
    exact ⟨mod_mem_rootsMod c k (k * m) r hk (dvd_mul_right k m) hr,
      mod_mem_rootsMod c m (k * m) r hm (dvd_mul_left m k) hr⟩
  · intro r hr r' hr' h
    rw [Prod.mk.injEq] at h
    have h1 : r ≡ r' [MOD k] := h.1
    have h2 : r ≡ r' [MOD m] := h.2
    have h3 : r ≡ r' [MOD k * m] := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩
    exact eq_of_modEq_of_lt h3 ((mem_rootsMod _ _ _).mp hr).1 ((mem_rootsMod _ _ _).mp hr').1
  · rintro ⟨r₁, r₂⟩ h12
    rw [Finset.mem_product] at h12
    obtain ⟨h1, h2⟩ := h12
    rw [mem_rootsMod] at h1 h2
    have hxlt := Nat.chineseRemainder_lt_mul hcop r₁ r₂ hk.ne' hm.ne'
    have hx1 : ((Nat.chineseRemainder hcop r₁ r₂ : ℕ)) ≡ r₁ [MOD k] :=
      (Nat.chineseRemainder hcop r₁ r₂).2.1
    have hx2 : ((Nat.chineseRemainder hcop r₁ r₂ : ℕ)) ≡ r₂ [MOD m] :=
      (Nat.chineseRemainder hcop r₁ r₂).2.2
    obtain ⟨x, hx⟩ : ∃ x : ℕ, x = (Nat.chineseRemainder hcop r₁ r₂ : ℕ) := ⟨_, rfl⟩
    rw [← hx] at hxlt hx1 hx2
    have e1 : x % k = r₁ := by
      have h' : x % k = r₁ % k := hx1
      rwa [Nat.mod_eq_of_lt h1.1] at h'
    have e2 : x % m = r₂ := by
      have h' : x % m = r₂ % m := hx2
      rwa [Nat.mod_eq_of_lt h2.1] at h'
    refine ⟨x, ?_, by rw [e1, e2]⟩
    rw [mem_rootsMod]
    refine ⟨hxlt, ?_⟩
    have d1 : (k : ℤ) ∣ (x : ℤ) ^ 3 - c :=
      (dvd_cube_sub_congr _ _ _ c (Nat.modEq_iff_dvd.mp hx1)).mp h1.2
    have d2 : (m : ℤ) ∣ (x : ℤ) ^ 3 - c :=
      (dvd_cube_sub_congr _ _ _ c (Nat.modEq_iff_dvd.mp hx2)).mp h2.2
    have hcopZ : IsCoprime (k : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
    push_cast
    exact hcopZ.mul_dvd d1 d2
  · intro r hr
    rfl

lemma nu_mul (c : ℤ) (k m : ℕ) (hk : 0 < k) (hm : 0 < m) (hcop : Nat.Coprime k m) :
    nu c (k * m) = nu c k * nu c m := by
  have h := crt_roots c k m hk hm hcop (fun _ _ => 1)
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one] at h
  unfold nu
  exact_mod_cast h

/-- `e(t) = exp(2πi t)`. -/
noncomputable def ee (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

lemma ee_add (s t : ℝ) : ee (s + t) = ee s * ee t := by
  unfold ee
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

lemma ee_int (n : ℤ) : ee (n : ℝ) = 1 := by
  unfold ee
  rw [← Complex.exp_int_mul_two_pi_mul_I n]
  congr 1
  push_cast
  ring

lemma norm_ee (t : ℝ) : ‖ee t‖ = 1 := by
  unfold ee
  have e : (2 * Real.pi * Complex.I * t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e, Complex.norm_exp_ofReal_mul_I]

lemma ee_eq_of_sub_int (s t : ℝ) (n : ℤ) (h : s - t = n) : ee s = ee t := by
  have e : s = t + n := by linarith
  rw [e, ee_add, ee_int, mul_one]

lemma conj_ee (t : ℝ) : (starRingEnd ℂ) (ee t) = ee (-t) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  have e : (2 * Real.pi * Complex.I * t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e, map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- Exponential sum over the cube roots of `c` modulo `d`. -/
noncomputable def Sx (c : ℤ) (a : ℤ) (d : ℕ) : ℂ :=
  ∑ r ∈ rootsMod c d, ee ((a : ℝ) * r / d)

lemma norm_Sx_le (c a : ℤ) (d : ℕ) : ‖Sx c a d‖ ≤ nu c d := by
  unfold Sx nu
  calc ‖∑ r ∈ rootsMod c d, ee ((a : ℝ) * r / d)‖
      ≤ ∑ r ∈ rootsMod c d, ‖ee ((a : ℝ) * r / d)‖ := norm_sum_le _ _
    _ = ((rootsMod c d).card : ℝ) := by simp [norm_ee]

/-- The exponential sum only depends on `a` modulo `d`. -/
lemma Sx_congr (c : ℤ) (a a' : ℤ) (d : ℕ) (hd : 0 < d) (h : (d : ℤ) ∣ a - a') :
    Sx c a d = Sx c a' d := by
  unfold Sx
  apply Finset.sum_congr rfl
  intro r _
  obtain ⟨u, hu⟩ := h
  apply ee_eq_of_sub_int _ _ (u * r)
  have hd' : (d : ℝ) ≠ 0 := by positivity
  have hu' : (a : ℝ) - a' = d * u := by exact_mod_cast hu
  push_cast
  field_simp
  linear_combination (r : ℝ) * hu'

/-- Multiplicativity of the exponential sums. -/
lemma Sx_crt (c : ℤ) (k m : ℕ) (hk : 0 < k) (hm : 0 < m) (hcop : Nat.Coprime k m)
    (a a₁ a₂ : ℤ) (h1 : (k : ℤ) ∣ a₁ * m - a) (h2 : (m : ℤ) ∣ a₂ * k - a) :
    Sx c a (k * m) = Sx c a₁ k * Sx c a₂ m := by
  unfold Sx
  rw [Finset.sum_mul_sum,
    ← crt_roots c k m hk hm hcop (fun r₁ r₂ => ee ((a₁ : ℝ) * r₁ / k) * ee ((a₂ : ℝ) * r₂ / m))]
  apply Finset.sum_congr rfl
  intro r _
  rw [← ee_add]
  have hcopZ : IsCoprime (k : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  have hrk : (r : ℤ) = ((r % k : ℕ) : ℤ) + (k : ℤ) * ((r / k : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mod_add_div r k).symm
  have hrm : (r : ℤ) = ((r % m : ℕ) : ℤ) + (m : ℤ) * ((r / m : ℕ) : ℤ) := by
    exact_mod_cast (Nat.mod_add_div r m).symm
  obtain ⟨u, hu⟩ := h1
  obtain ⟨v, hv⟩ := h2
  have d1 : (k : ℤ) ∣ a * r - (a₁ * ((r % k : ℕ) : ℤ) * m + a₂ * ((r % m : ℕ) : ℤ) * k) := by
    refine ⟨-r * u + a₁ * m * ((r / k : ℕ) : ℤ) - a₂ * ((r % m : ℕ) : ℤ), ?_⟩
    linear_combination (-(r : ℤ)) * hu + (a₁ * m) * hrk
  have d2 : (m : ℤ) ∣ a * r - (a₁ * ((r % k : ℕ) : ℤ) * m + a₂ * ((r % m : ℕ) : ℤ) * k) := by
    refine ⟨-r * v + a₂ * k * ((r / m : ℕ) : ℤ) - a₁ * ((r % k : ℕ) : ℤ), ?_⟩
    linear_combination (-(r : ℤ)) * hv + (a₂ * k) * hrm
  obtain ⟨n, hn⟩ := hcopZ.mul_dvd d1 d2
  apply ee_eq_of_sub_int _ _ n
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have hm' : (m : ℝ) ≠ 0 := by positivity
  have hn' := congrArg (Int.cast : ℤ → ℝ) hn
  simp only [Int.cast_sub, Int.cast_add, Int.cast_mul, Int.cast_natCast] at hn'
  push_cast
  field_simp
  linear_combination hn'

lemma norm_Sx_mul_le (c : ℤ) (k m : ℕ) (hk : 0 < k) (hm : 0 < m) (hcop : Nat.Coprime k m)
    (a a₁ : ℤ) (h1 : (k : ℤ) ∣ a₁ * m - a) :
    ‖Sx c a (k * m)‖ ≤ ‖Sx c a₁ k‖ * nu c m := by
  have hcopZ : IsCoprime (k : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  obtain ⟨u, v, huv⟩ := hcopZ
  have h2 : (m : ℤ) ∣ (a * u) * k - a := ⟨-(a * v), by linear_combination a * huv⟩
  rw [Sx_crt c k m hk hm hcop a a₁ (a * u) h1 h2, norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_Sx_le c _ m) (norm_nonneg _)

lemma sum_ee_range (k : ℕ) (hk : 0 < k) (t : ℤ) :
    ∑ b ∈ Finset.range k, ee ((b : ℝ) * t / k) = if (k : ℤ) ∣ t then (k : ℂ) else 0 := by
  have hk' : (k : ℝ) ≠ 0 := by positivity
  obtain ⟨z, hz⟩ : ∃ z : ℂ, z = ee ((t : ℝ) / k) := ⟨_, rfl⟩
  have hpow : ∀ b : ℕ, ee ((b : ℝ) * t / k) = z ^ b := by
    intro b
    rw [hz]
    unfold ee
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp_rw [hpow]
  have hzk : z ^ k = 1 := by
    rw [← hpow k]
    have e : (k : ℝ) * t / k = (t : ℝ) := by field_simp
    rw [e, ee_int]
  split_ifs with hdvd
  · obtain ⟨u, hu⟩ := hdvd
    have hz1 : z = 1 := by
      rw [hz, hu]
      push_cast
      have e : (k : ℝ) * u / k = (u : ℝ) := by field_simp
      rw [e, ee_int]
    rw [hz1]
    simp
  · have hz1 : z ≠ 1 := by
      intro h1
      rw [hz] at h1
      unfold ee at h1
      rw [Complex.exp_eq_one_iff] at h1
      obtain ⟨n, hn⟩ := h1
      apply hdvd
      refine ⟨n, ?_⟩
      have h2 : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
        simp [Real.pi_ne_zero]
      have h3 : (((t : ℝ) / k : ℝ) : ℂ) = (n : ℂ) := by
        apply mul_left_cancel₀ h2
        rw [hn]
        ring
      have h4 : (t : ℝ) / k = n := by exact_mod_cast h3
      have h5 : (t : ℝ) = k * n := by
        field_simp at h4
        linarith
      exact_mod_cast h5
    rw [geom_sum_eq hz1, hzk, sub_self, zero_div]

/-- Second moment of the exponential sums over all frequencies. -/
lemma second_moment (c : ℤ) (k : ℕ) (hk : 0 < k) :
    ∑ b ∈ Finset.range k, ‖Sx c b k‖ ^ 2 = (k : ℝ) * nu c k := by
  have hk' : (k : ℝ) ≠ 0 := by positivity
  have h1 : ∀ b : ℕ, ((‖Sx c b k‖ ^ 2 : ℝ) : ℂ)
      = ∑ r ∈ rootsMod c k, ∑ r' ∈ rootsMod c k,
          ee ((b : ℝ) * (((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) / k) := by
    intro b
    push_cast
    rw [← Complex.mul_conj']
    unfold Sx
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro r' _
    rw [conj_ee, ← ee_add]
    congr 1
    push_cast
    ring
  have h2 : ((∑ b ∈ Finset.range k, ‖Sx c b k‖ ^ 2 : ℝ) : ℂ) = (((k : ℝ) * nu c k : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp_rw [h1]
    rw [Finset.sum_comm]
    have h3 : ∀ r ∈ rootsMod c k, ∑ b ∈ Finset.range k, ∑ r' ∈ rootsMod c k,
        ee ((b : ℝ) * (((r : ℤ) - (r' : ℤ) : ℤ) : ℝ) / k) = (k : ℂ) := by
      intro r hr
      rw [Finset.sum_comm]
      simp_rw [sum_ee_range k hk]
      rw [Finset.sum_eq_single r]
      · simp
      · intro r' hr' hne
        rw [if_neg]
        intro hdvd
        apply hne
        have h4 : r' ≡ r [MOD k] := Nat.modEq_iff_dvd.mpr hdvd
        exact eq_of_modEq_of_lt h4 ((mem_rootsMod _ _ _).mp hr').1 ((mem_rootsMod _ _ _).mp hr).1
      · intro h
        exact absurd hr h
    rw [Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul]
    unfold nu
    push_cast
    ring
  exact_mod_cast h2

end roots

section fibers

lemma not_dvd_root (c : ℤ) (p : ℕ) (hpc : ¬ (p : ℤ) ∣ c) (r : ℤ)
    (h : (p : ℤ) ∣ r ^ 3 - c) : ¬ (p : ℤ) ∣ r := by
  intro hr
  apply hpc
  have h3 : (p : ℤ) ∣ r ^ 3 := dvd_pow hr three_ne_zero
  have := dvd_sub h3 h
  simpa using this

/-- Hensel step: if `p ∣ d` and `p ∤ 3c`, every root modulo `d` has exactly one lift modulo `p d`. -/
lemma nu_prime_mul_of_dvd (c : ℤ) (p d : ℕ) (hp : p.Prime) (hp3c : ¬ (p : ℤ) ∣ 3 * c)
    (hd : 0 < d) (hpd : p ∣ d) : nu c (p * d) = nu c d := by
  have hp3 : ¬ (p : ℤ) ∣ 3 := fun h => hp3c (dvd_mul_of_dvd_left h c)
  have hpc : ¬ (p : ℤ) ∣ c := fun h => hp3c (dvd_mul_of_dvd_right h 3)
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨d', hd'⟩ := hpd
  have hd'Z : (d : ℤ) = (p : ℤ) * (d' : ℤ) := by exact_mod_cast hd'
  have hpdZ : (p : ℤ) ∣ (d : ℤ) := ⟨d', hd'Z⟩
  unfold nu
  apply Finset.card_bij (fun r _ => r % d)
  · intro r hr
    exact mod_mem_rootsMod c d (p * d) r hd (dvd_mul_left d p) hr
  · intro r hr r' hr' h
    rw [mem_rootsMod] at hr hr'
    have hmod : (d : ℤ) ∣ (r' : ℤ) - r := Nat.modEq_iff_dvd.mp (show r ≡ r' [MOD d] from h)
    obtain ⟨j, hj⟩ := hmod
    have hr'eq : (r' : ℤ) = r + d * j := by linarith
    have h1 : ((p * d : ℕ) : ℤ) ∣ (r' : ℤ) ^ 3 - (r : ℤ) ^ 3 := by
      have := dvd_sub hr'.2 hr.2
      have e : (r' : ℤ) ^ 3 - c - ((r : ℤ) ^ 3 - c) = (r' : ℤ) ^ 3 - (r : ℤ) ^ 3 := by ring
      rwa [e] at this
    have h2 : ((p * d : ℕ) : ℤ) ∣ (d : ℤ) ^ 2 * (3 * r * j ^ 2 + d * j ^ 3) := by
      refine dvd_mul_of_dvd_left ⟨(d' : ℤ), ?_⟩ _
      push_cast
      rw [hd'Z]
      ring
    have h3 : ((p * d : ℕ) : ℤ) ∣ 3 * (r : ℤ) ^ 2 * d * j := by
      have e : (r' : ℤ) ^ 3 - (r : ℤ) ^ 3
          = 3 * (r : ℤ) ^ 2 * d * j + (d : ℤ) ^ 2 * (3 * r * j ^ 2 + d * j ^ 3) := by
        rw [hr'eq]
        ring
      rw [e] at h1
      exact (dvd_add_left h2).mp h1
    have h4 : (p : ℤ) ∣ 3 * (r : ℤ) ^ 2 * j := by
      have e1 : ((p * d : ℕ) : ℤ) = (d : ℤ) * p := by push_cast; ring
      have e2 : 3 * (r : ℤ) ^ 2 * d * j = (d : ℤ) * (3 * (r : ℤ) ^ 2 * j) := by ring
      rw [e1, e2] at h3
      exact (mul_dvd_mul_iff_left (by exact_mod_cast hd.ne')).mp h3
    have hpr : ¬ (p : ℤ) ∣ (r : ℤ) :=
      not_dvd_root c p hpc r (dvd_trans (by push_cast; exact dvd_mul_right _ _) hr.2)
    have h5 : (p : ℤ) ∣ j := by
      rcases hpp.dvd_or_dvd h4 with h | h
      · rcases hpp.dvd_or_dvd h with h | h
        · exact absurd h hp3
        · exact absurd (hpp.dvd_of_dvd_pow h) hpr
      · exact h
    obtain ⟨j', hj'⟩ := h5
    have h6 : ((p * d : ℕ) : ℤ) ∣ (r' : ℤ) - r := ⟨j', by rw [hj, hj']; push_cast; ring⟩
    exact eq_of_modEq_of_lt (Nat.modEq_iff_dvd.mpr h6) hr.1 hr'.1
  · intro r₀ hr₀
    rw [mem_rootsMod] at hr₀
    obtain ⟨κ, hκ⟩ := hr₀.2
    have hpr : ¬ (p : ℤ) ∣ (r₀ : ℤ) := not_dvd_root c p hpc r₀ (dvd_trans hpdZ hr₀.2)
    have hcop : IsCoprime (p : ℤ) (3 * (r₀ : ℤ) ^ 2) := by
      rw [Prime.coprime_iff_not_dvd hpp]
      intro h
      rcases hpp.dvd_or_dvd h with h | h
      · exact hp3 h
      · exact hpr (hpp.dvd_of_dvd_pow h)
    obtain ⟨v, u, huv⟩ := hcop
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have hppos : (0 : ℤ) < p := by exact_mod_cast hp.pos
    have hi0 : 0 ≤ (-κ * u) % (p : ℤ) := Int.emod_nonneg _ hp0
    have hilt : (-κ * u) % (p : ℤ) < p := Int.emod_lt_of_pos _ hppos
    obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = (-κ * u) % (p : ℤ) :=
      ⟨((-κ * u) % (p : ℤ)).toNat, Int.toNat_of_nonneg hi0⟩
    have hip : i < p := by
      have : (i : ℤ) < p := by rw [hi]; exact hilt
      exact_mod_cast this
    have hq : (i : ℤ) + (p : ℤ) * ((-κ * u) / (p : ℤ)) = -κ * u := by
      rw [hi, Int.emod_def]
      ring
    obtain ⟨q, hq'⟩ : ∃ q : ℤ, q = (-κ * u) / (p : ℤ) := ⟨_, rfl⟩
    rw [← hq'] at hq
    have hw : κ + 3 * (r₀ : ℤ) ^ 2 * i = (p : ℤ) * (κ * v - 3 * (r₀ : ℤ) ^ 2 * q) := by
      linear_combination (3 * (r₀ : ℤ) ^ 2) * hq - κ * huv
    refine ⟨r₀ + d * i, ?_, ?_⟩
    · rw [mem_rootsMod]
      refine ⟨?_, ?_⟩
      · calc r₀ + d * i < d + d * i := by omega
          _ = d * (i + 1) := by ring
          _ ≤ d * p := Nat.mul_le_mul_left d (by omega)
          _ = p * d := mul_comm _ _
      · refine ⟨(κ * v - 3 * (r₀ : ℤ) ^ 2 * q)
          + (d' : ℤ) * (3 * (r₀ : ℤ) * (i : ℤ) ^ 2 + (d : ℤ) * (i : ℤ) ^ 3), ?_⟩
        push_cast
        linear_combination hκ + (d : ℤ) * hw
          + ((d : ℤ) * (3 * (r₀ : ℤ) * (i : ℤ) ^ 2 + (d : ℤ) * (i : ℤ) ^ 3)) * hd'Z
    · show (r₀ + d * i) % d = r₀
      rw [Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hr₀.1

lemma pow_key (p : ℕ) [hp : Fact p.Prime] (hp3 : p % 3 = 2) (x : ZMod p) :
    x ^ (3 * (2 * (p / 3) + 1)) = x := by
  have h1 : 3 * (2 * (p / 3) + 1) = p + (p - 1) := by
    have := hp.out.two_le
    omega
  rw [h1, pow_add, ZMod.pow_card]
  have h2 : x * x ^ (p - 1) = x ^ p := by
    rw [← pow_succ', Nat.sub_add_cancel hp.out.one_le]
  rw [h2, ZMod.pow_card]

lemma nu_prime_eq_card (c : ℤ) (p : ℕ) [Fact p.Prime] :
    nu c p = (Finset.univ.filter (fun x : ZMod p => x ^ 3 = (c : ZMod p))).card := by
  unfold nu
  refine Finset.card_bij (t := Finset.univ.filter (fun x : ZMod p => x ^ 3 = (c : ZMod p)))
    (fun (r : ℕ) _ => ((r : ℕ) : ZMod p)) ?_ ?_ ?_
  · intro r hr
    rw [mem_rootsMod] at hr
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hr.2
    push_cast at this
    exact sub_eq_zero.mp this
  · intro r hr r' hr' h
    rw [mem_rootsMod] at hr hr'
    have := (ZMod.natCast_eq_natCast_iff' r r' p).mp h
    rwa [Nat.mod_eq_of_lt hr.1, Nat.mod_eq_of_lt hr'.1] at this
  · intro x hx
    rw [Finset.mem_filter] at hx
    refine ⟨x.val, ?_, ZMod.natCast_zmod_val x⟩
    rw [mem_rootsMod]
    refine ⟨ZMod.val_lt x, ?_⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact sub_eq_zero.mpr hx.2

lemma nu_prime_two (c : ℤ) (p : ℕ) (hp : p.Prime) (hp3 : p % 3 = 2) : nu c p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  rw [nu_prime_eq_card, Finset.card_eq_one]
  refine ⟨(c : ZMod p) ^ (2 * (p / 3) + 1), ?_⟩
  ext x
  rw [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨_, hx⟩
    rw [← hx, ← pow_mul]
    exact (pow_key p hp3 x).symm
  · intro hx
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hx, ← pow_mul, mul_comm]
    exact pow_key p hp3 _

lemma nu_split (c : ℤ) (p : ℕ) (h : Psplit c p) : nu c p = 3 := by
  obtain ⟨hp, hp1, hp3c, r, hr⟩ := h
  have : Fact p.Prime := ⟨hp⟩
  rw [nu_prime_eq_card]
  have hr0 : ((r : ZMod p)) ^ 3 = (c : ZMod p) := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hr
    push_cast at this
    exact sub_eq_zero.mp this
  have hc0 : (c : ZMod p) ≠ 0 := by
    intro h0
    apply hp3c
    exact dvd_mul_of_dvd_right ((ZMod.intCast_zmod_eq_zero_iff_dvd c p).mp h0) 3
  have hr00 : (r : ZMod p) ≠ 0 := by
    intro h0
    rw [h0] at hr0
    apply hc0
    rw [← hr0]
    ring
  obtain ⟨ω, hω3, hω1⟩ : ∃ ω : ZMod p, ω ^ 3 = 1 ∧ ω ≠ 1 := by
    have hcard : Nat.card (ZMod p)ˣ = p - 1 := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient, Nat.totient_prime hp]
    have h3 : 3 ∣ Nat.card (ZMod p)ˣ := by
      rw [hcard]
      have := hp.pos
      omega
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 3 h3
    refine ⟨(u : ZMod p), ?_, ?_⟩
    · have := pow_orderOf_eq_one u
      rw [hu] at this
      have h4 := congrArg Units.val this
      rw [Units.val_pow_eq_pow_val, Units.val_one] at h4
      exact h4
    · intro h1
      have : u = 1 := Units.ext h1
      rw [this, orderOf_one] at hu
      omega
  have hω : ω ^ 2 + ω + 1 = 0 := by
    have h1 : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      have e : (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
      rw [e, hω3, sub_self]
    exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hω1)
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0] at hω3
    norm_num at hω3
  rw [Finset.card_eq_three]
  refine ⟨(r : ZMod p), (r : ZMod p) * ω, (r : ZMod p) * ω ^ 2, ?_, ?_, ?_, ?_⟩
  · intro h
    apply hω1
    have h2 : (r : ZMod p) * 1 = (r : ZMod p) * ω := by rw [mul_one]; exact h
    exact (mul_left_cancel₀ hr00 h2).symm
  · intro h
    have h2 : (r : ZMod p) * 1 = (r : ZMod p) * ω ^ 2 := by rw [mul_one]; exact h
    have h3 : ω ^ 2 = 1 := (mul_left_cancel₀ hr00 h2).symm
    apply hω1
    have h4 : ω ^ 3 = ω ^ 2 * ω := by ring
    rw [h4, h3, one_mul] at hω3
    exact hω3
  · intro h
    have h2 : ω = ω ^ 2 := mul_left_cancel₀ hr00 h
    apply hω1
    have h3 : ω * 1 = ω * ω := by rw [mul_one, ← pow_two]; exact h2
    exact (mul_left_cancel₀ hω0 h3).symm
  · ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hx
      have h1 : (x - r) * (x - r * ω) * (x - r * ω ^ 2) = 0 := by
        have e : (x - r) * (x - r * ω) * (x - r * ω ^ 2)
            = x ^ 3 - (r : ZMod p) ^ 3 * ω ^ 3 - x ^ 2 * r * (ω ^ 2 + ω + 1)
              + x * (r : ZMod p) ^ 2 * ω * (ω ^ 2 + ω + 1) := by ring
        rw [e, hω, hω3, hx, hr0]
        ring
      rcases mul_eq_zero.mp h1 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · left; exact sub_eq_zero.mp h
        · right; left; exact sub_eq_zero.mp h
      · right; right; exact sub_eq_zero.mp h
    · rintro (h | h | h)
      · rw [h]; exact hr0
      · rw [h, mul_pow, hω3, mul_one, hr0]
      · rw [h, mul_pow, hr0]
        have e : (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 := by ring
        rw [e, hω3, one_pow, mul_one]

/-- Roots modulo `p d` for a prime `p ∤ 3c`. -/
lemma nu_prime_mul (c : ℤ) (p d : ℕ) (hp : p.Prime) (hp3c : ¬ (p : ℤ) ∣ 3 * c) (hd : 0 < d) :
    nu c (p * d) = (if p ∣ d then 1 else nu c p) * nu c d := by
  split_ifs with h
  · rw [one_mul]
    exact nu_prime_mul_of_dvd c p d hp hp3c hd h
  · exact nu_mul c p d hp.pos hd ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)

lemma nu_two_mul (c : ℤ) (p d : ℕ) (hp : p.Prime) (hp3 : p % 3 = 2) (hp3c : ¬ (p : ℤ) ∣ 3 * c)
    (hd : 0 < d) : nu c (p * d) = nu c d := by
  rw [nu_prime_mul c p d hp hp3c hd, nu_prime_two c p hp hp3]
  simp

lemma nu_split_mul (c : ℤ) (q m : ℕ) (hq : Psplit c q) (hm : 0 < m) (hqm : ¬ q ∣ m) :
    nu c (q * m) = 3 * nu c m := by
  rw [nu_prime_mul c q m hq.1 hq.2.2.1 hm, if_neg hqm, nu_split c q hq]

lemma nu_split_mul_le (c : ℤ) (q d : ℕ) (hq : Psplit c q) (hd : 0 < d) :
    nu c (q * d) ≤ 3 * nu c d := by
  rw [nu_prime_mul c q d hq.1 hq.2.2.1 hd, nu_split c q hq]
  split_ifs <;> omega

lemma nu_zero (c : ℤ) : nu c 0 = 0 := by
  simp [nu, rootsMod]

end fibers



section dirichlet

lemma card_Spairs_eq (c : ℤ) (y : ℕ) : (Spairs c y).card = ∑ d ∈ Finset.Icc 1 y, nu c d := by
  classical
  have hmaps : ∀ p ∈ Spairs c y, p.1 ∈ Finset.Icc 1 y := by
    intro p hp
    unfold Spairs at hp
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hp).1).1
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  apply Finset.sum_congr rfl
  intro d hd
  unfold nu
  refine Finset.card_bij (fun (p : ℕ × ℕ) _ => p.2) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    unfold Spairs at hp1
    obtain ⟨_, h3, h4⟩ := Finset.mem_filter.mp hp1
    rw [mem_rootsMod, ← hp2]
    exact ⟨h3, h4⟩
  · intro p hp p' hp' h
    have h1 := (Finset.mem_filter.mp hp).2
    have h2 := (Finset.mem_filter.mp hp').2
    exact Prod.ext (h1.trans h2.symm) h
  · intro r hr
    rw [mem_rootsMod] at hr
    refine ⟨(d, r), ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨?_, rfl⟩
    unfold Spairs
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    have := Finset.mem_Icc.mp hd
    exact ⟨⟨hd, by omega⟩, hr.1, hr.2⟩

/-- Abel summation as an inequality: partial sums `≤ C n` against a nonincreasing weight. -/
lemma abel_le (a g : ℕ → ℝ) (C : ℝ) (hV : ∀ n : ℕ, ∑ d ∈ Finset.Icc 1 n, a d ≤ C * n)
    (hg : ∀ n : ℕ, 1 ≤ n → g (n + 1) ≤ g n) (hg0 : ∀ n, 0 ≤ g n) (Y : ℕ) :
    ∑ d ∈ Finset.Icc 1 Y, a d * g d ≤ C * ∑ n ∈ Finset.Icc 1 Y, g n := by
  have inv : ∀ Y : ℕ, (C * Y - ∑ d ∈ Finset.Icc 1 Y, a d) * g Y
      ≤ C * ∑ n ∈ Finset.Icc 1 Y, g n - ∑ d ∈ Finset.Icc 1 Y, a d * g d := by
    intro Y
    induction Y with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega),
        Finset.sum_Icc_succ_top (by omega)]
      have hU : 0 ≤ C * n - ∑ d ∈ Finset.Icc 1 n, a d := by linarith [hV n]
      have hstep : (C * n - ∑ d ∈ Finset.Icc 1 n, a d) * g (n + 1)
          ≤ (C * n - ∑ d ∈ Finset.Icc 1 n, a d) * g n := by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        · exact mul_le_mul_of_nonneg_left (hg n hn) hU
      push_cast
      nlinarith
  have h1 := inv Y
  have h2 : 0 ≤ (C * Y - ∑ d ∈ Finset.Icc 1 Y, a d) * g Y :=
    mul_nonneg (by linarith [hV Y]) (hg0 Y)
  linarith

lemma sum_rpow_le (x : ℝ) (hx : 1 < x) (Y : ℕ) :
    ∑ n ∈ Finset.Icc 1 Y, (n : ℝ) ^ (-x) ≤ x / (x - 1) := by
  have hx1 : 0 < x - 1 := by linarith
  rcases Nat.eq_zero_or_pos Y with rfl | hY
  · simp
    exact div_nonneg (by linarith) hx1.le
  · have h1 := sum_rpow_tail x hx 1 Y le_rfl hY
    have e : Finset.Icc 1 Y = insert 1 (Finset.Ico (1 + 1) (Y + 1)) := by
      ext n
      simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
      omega
    rw [e, Finset.sum_insert (by simp)]
    simp only [Nat.cast_one, Real.one_rpow] at h1 ⊢
    have e2 : x / (x - 1) = 1 + 1 / (x - 1) := by
      field_simp
      ring
    rw [e2]
    linarith

/-- Dirichlet series of `ν`: summability and the bound `2C/(x-1)`. -/
lemma nu_series (c : ℤ) (C : ℝ) (hC : ∀ y : ℕ, ((Spairs c y).card : ℝ) ≤ C * y)
    (x : ℝ) (hx : 1 < x) (hx2 : x ≤ 2) :
    Summable (fun d : ℕ => (nu c d : ℝ) * (d : ℝ) ^ (-x))
      ∧ ∑' d : ℕ, (nu c d : ℝ) * (d : ℝ) ^ (-x) ≤ 2 * C / (x - 1) := by
  have hx1 : 0 < x - 1 := by linarith
  have hC0 : 0 ≤ C := by
    have := hC 1
    have h2 : (0 : ℝ) ≤ ((Spairs c 1).card : ℝ) := Nat.cast_nonneg _
    simp only [Nat.cast_one, mul_one] at this
    linarith
  have hV : ∀ n : ℕ, ∑ d ∈ Finset.Icc 1 n, (nu c d : ℝ) ≤ C * n := by
    intro n
    have := hC n
    rw [card_Spairs_eq] at this
    exact_mod_cast this
  have hg : ∀ n : ℕ, 1 ≤ n → ((n + 1 : ℕ) : ℝ) ^ (-x) ≤ (n : ℝ) ^ (-x) := by
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    exact Real.rpow_le_rpow_of_nonpos hn0 (by push_cast; linarith) (by linarith)
  have hfin : ∀ Y : ℕ, ∑ d ∈ Finset.Icc 1 Y, (nu c d : ℝ) * (d : ℝ) ^ (-x) ≤ 2 * C / (x - 1) := by
    intro Y
    have h1 := abel_le (fun d => (nu c d : ℝ)) (fun n => (n : ℝ) ^ (-x)) C hV hg
      (fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _) Y
    have h2 := sum_rpow_le x hx Y
    have h3 : C * ∑ n ∈ Finset.Icc 1 Y, (n : ℝ) ^ (-x) ≤ C * (x / (x - 1)) :=
      mul_le_mul_of_nonneg_left h2 hC0
    have h4 : C * (x / (x - 1)) ≤ 2 * C / (x - 1) := by
      rw [mul_div_assoc', div_le_div_iff_of_pos_right hx1]
      nlinarith
    linarith
  have hnn : ∀ d : ℕ, 0 ≤ (nu c d : ℝ) * (d : ℝ) ^ (-x) :=
    fun d => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hrange : ∀ N : ℕ, ∑ d ∈ Finset.range N, (nu c d : ℝ) * (d : ℝ) ^ (-x) ≤ 2 * C / (x - 1) := by
    intro N
    refine le_trans ?_ (hfin N)
    rw [← Finset.sum_filter_of_ne (p := fun n => n ≠ 0)]
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rw [Finset.mem_filter, Finset.mem_range] at hn
        rw [Finset.mem_Icc]
        omega
      · intro n _ _
        exact hnn n
    · intro n _ hne h0
      apply hne
      rw [h0, nu_zero]
      simp
  exact ⟨summable_of_sum_range_le hnn hrange, Real.tsum_le_of_sum_range_le hnn hrange⟩

/-- Peeling lemma: the Euler factor at `p` of a series with `F (p m) = z F m`. -/
lemma peel {𝕜 : Type*} [RCLike 𝕜] (F : ℕ → 𝕜) (hF : Summable F) (p : ℕ) (hp : 0 < p) (z : 𝕜)
    (hz : z ≠ 1) (h : ∀ m, F (p * m) = z * F m) :
    ∑' m, F m = (1 - z)⁻¹ * ∑' m, (if p ∣ m then 0 else F m) := by
  classical
  have e1 : ∀ m, F m = (if p ∣ m then F m else 0) + (if p ∣ m then 0 else F m) := by
    intro m
    split_ifs <;> simp
  have s1 : Summable (fun m => if p ∣ m then F m else 0) := by
    have := hF.indicator {m : ℕ | p ∣ m}
    refine this.congr (fun m => ?_)
    simp [Set.indicator]
  have s2 : Summable (fun m => if p ∣ m then 0 else F m) := by
    have := hF.indicator {m : ℕ | ¬ p ∣ m}
    refine this.congr (fun m => ?_)
    simp [Set.indicator]
  have hinj : Function.Injective (fun m : ℕ => p * m) :=
    fun a b hab => Nat.eq_of_mul_eq_mul_left hp hab
  have e2 : ∑' m, (if p ∣ m then F m else 0) = z * ∑' m, F m := by
    have hsupp : Function.support (fun m => if p ∣ m then F m else 0)
        ⊆ Set.range (fun m : ℕ => p * m) := by
      intro m hm
      rw [Function.mem_support] at hm
      by_cases hd : p ∣ m
      · obtain ⟨m', rfl⟩ := hd
        exact ⟨m', rfl⟩
      · rw [if_neg hd] at hm
        exact absurd rfl hm
    rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
    apply tsum_congr
    intro m
    rw [if_pos (dvd_mul_right p m), h m]
  have e3 : ∑' m, F m = z * ∑' m, F m + ∑' m, (if p ∣ m then 0 else F m) := by
    conv_lhs => rw [tsum_congr e1]
    rw [s1.tsum_add s2, e2]
  have hz' : (1 - z) ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  rw [eq_inv_mul_iff_mul_eq₀ hz']
  linear_combination e3

end dirichlet



section characters

lemma char_term_norm_le {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) (x : ℝ) (a : ℕ → ℝ)
    (ha : ∀ m, 0 ≤ a m) (m : ℕ) :
    ‖(a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)‖ ≤ a m * (m : ℝ) ^ (-x) := by
  have h3 : 0 ≤ (m : ℝ) ^ (-x) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (ha m),
    Real.norm_of_nonneg h3]
  have h1 := DirichletCharacter.norm_le_one χ (m : ZMod k)
  calc a m * ‖χ (m : ZMod k)‖ * (m : ℝ) ^ (-x) ≤ a m * 1 * (m : ℝ) ^ (-x) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (ha m)) h3
    _ = a m * (m : ℝ) ^ (-x) := by ring

lemma char_term_summable {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) (x : ℝ) (a : ℕ → ℝ)
    (ha : ∀ m, 0 ≤ a m) (hs : Summable (fun m : ℕ => a m * (m : ℝ) ^ (-x))) :
    Summable (fun m : ℕ => (a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)) :=
  Summable.of_norm (Summable.of_nonneg_of_le (fun m => norm_nonneg _)
    (char_term_norm_le χ x a ha) hs)

lemma char_sum_norm_le {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) (x : ℝ) (a : ℕ → ℝ)
    (ha : ∀ m, 0 ≤ a m) (hs : Summable (fun m : ℕ => a m * (m : ℝ) ^ (-x))) :
    ‖∑' m : ℕ, (a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)‖
      ≤ ∑' m : ℕ, a m * (m : ℝ) ^ (-x) := by
  have hsn : Summable (fun m : ℕ => ‖(a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun m => norm_nonneg _) (char_term_norm_le χ x a ha) hs
  exact (norm_tsum_le_tsum_norm hsn).trans (hsn.tsum_le_tsum (char_term_norm_le χ x a ha) hs)

/-- Twisted sums lose one Euler-factor ratio for every prime under which the weight is
invariant. -/
lemma char_sum_le {k : ℕ} [NeZero k] (χ : DirichletCharacter ℂ k) (x : ℝ) (hx : 1 < x) :
    ∀ (P : Finset ℕ), (∀ p ∈ P, p.Prime) → ∀ (a : ℕ → ℝ), (∀ m, 0 ≤ a m) →
      Summable (fun m : ℕ => a m * (m : ℝ) ^ (-x)) → (∀ p ∈ P, ∀ m, a (p * m) = a m) →
      ‖∑' m : ℕ, (a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)‖
        ≤ (∏ p ∈ P, (1 - (p : ℝ) ^ (-x)) / ‖1 - χ (p : ZMod k) * (((p : ℝ) ^ (-x) : ℝ) : ℂ)‖)
          * ∑' m : ℕ, a m * (m : ℝ) ^ (-x) := by
  classical
  intro P
  induction P using Finset.induction_on with
  | empty =>
    intro _ a ha hs _
    rw [Finset.prod_empty, one_mul]
    exact char_sum_norm_le χ x a ha hs
  | insert p P hpP ih =>
    intro hP a ha hs hinv
    have hp : p.Prime := hP p (Finset.mem_insert_self p P)
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (p : ℝ) ^ (-x) := ⟨_, rfl⟩
    have ht0 : 0 < t := by rw [ht]; exact Real.rpow_pos_of_pos hp0 _
    have ht1 : t < 1 := by rw [ht]; exact Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)
    obtain ⟨z, hz⟩ : ∃ z : ℂ, z = χ (p : ZMod k) * ((t : ℝ) : ℂ) := ⟨_, rfl⟩
    have hznorm : ‖z‖ ≤ t := by
      rw [hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht0.le]
      have := DirichletCharacter.norm_le_one χ (p : ZMod k)
      nlinarith [norm_nonneg (χ (p : ZMod k))]
    have hz1 : z ≠ 1 := by
      intro h
      rw [h, norm_one] at hznorm
      linarith
    obtain ⟨a', ha'def⟩ : ∃ a' : ℕ → ℝ, a' = fun m => if p ∣ m then 0 else a m := ⟨_, rfl⟩
    have ha'm : ∀ m, a' m = if p ∣ m then 0 else a m := fun _ => by rw [ha'def]
    have ha' : ∀ m, 0 ≤ a' m := by
      intro m
      rw [ha'm]
      split_ifs
      · exact le_rfl
      · exact ha m
    have hs' : Summable (fun m : ℕ => a' m * (m : ℝ) ^ (-x)) := by
      refine Summable.of_nonneg_of_le
        (fun m => mul_nonneg (ha' m) (Real.rpow_nonneg (Nat.cast_nonneg m) _)) (fun m => ?_) hs
      rw [ha'm]
      split_ifs
      · rw [zero_mul]
        exact mul_nonneg (ha m) (Real.rpow_nonneg (Nat.cast_nonneg m) _)
      · exact le_rfl
    have hinv' : ∀ q ∈ P, ∀ m, a' (q * m) = a' m := by
      intro q hq m
      have hqp : q.Prime := hP q (Finset.mem_insert_of_mem hq)
      have hne : p ≠ q := fun h => hpP (h ▸ hq)
      have hiff : p ∣ q * m ↔ p ∣ m := by
        constructor
        · intro h
          rcases (Nat.Prime.dvd_mul hp).mp h with h | h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hp hqp).mp h) hne
          · exact h
        · intro h
          exact dvd_mul_of_dvd_right h q
      rw [ha'm, ha'm, hinv q (Finset.mem_insert_of_mem hq) m]
      by_cases h : p ∣ m
      · rw [if_pos (hiff.mpr h), if_pos h]
      · rw [if_neg (fun h' => h (hiff.mp h')), if_neg h]
    have ih' := ih (fun q hq => hP q (Finset.mem_insert_of_mem hq)) a' ha' hs' hinv'
    have hrp : ∀ m : ℕ, (((p * m : ℕ) : ℝ)) ^ (-x) = t * (m : ℝ) ^ (-x) := by
      intro m
      push_cast
      rw [Real.mul_rpow hp0.le (Nat.cast_nonneg m), ht]
    have hFmul : ∀ m : ℕ, (a (p * m) : ℂ) * χ ((p * m : ℕ) : ZMod k)
        * ((((p * m : ℕ) : ℝ) ^ (-x) : ℝ) : ℂ)
        = z * ((a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)) := by
      intro m
      rw [hinv p (Finset.mem_insert_self p P) m, hrp m]
      have e1 : ((p * m : ℕ) : ZMod k) = (p : ZMod k) * (m : ZMod k) := by push_cast; ring
      rw [e1, map_mul, hz]
      push_cast
      ring
    have hpeelC := peel (fun m : ℕ => (a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ))
      (char_term_summable χ x a ha hs) p hp.pos z hz1 hFmul
    have hGmul : ∀ m : ℕ, a (p * m) * ((p * m : ℕ) : ℝ) ^ (-x) = t * (a m * (m : ℝ) ^ (-x)) := by
      intro m
      rw [hinv p (Finset.mem_insert_self p P) m, hrp m]
      ring
    have hpeelR := peel (fun m : ℕ => a m * (m : ℝ) ^ (-x)) hs p hp.pos t (ne_of_lt ht1) hGmul
    have eC : ∀ m : ℕ, (if p ∣ m then 0
        else (a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ))
        = (a' m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ) := by
      intro m
      rw [ha'm]
      split_ifs <;> simp
    have eR : ∀ m : ℕ, (if p ∣ m then 0 else a m * (m : ℝ) ^ (-x)) = a' m * (m : ℝ) ^ (-x) := by
      intro m
      rw [ha'm]
      split_ifs <;> simp
    rw [tsum_congr eC] at hpeelC
    rw [tsum_congr eR] at hpeelR
    rw [hpeelC, norm_mul, norm_inv, Finset.prod_insert hpP, hpeelR, ← ht, ← hz]
    have hnz : 0 < ‖1 - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hz1))
    have h1t : 0 < 1 - t := by linarith
    calc ‖1 - z‖⁻¹ * ‖∑' m : ℕ, (a' m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)‖
        ≤ ‖1 - z‖⁻¹ * ((∏ q ∈ P, (1 - (q : ℝ) ^ (-x))
            / ‖1 - χ (q : ZMod k) * (((q : ℝ) ^ (-x) : ℝ) : ℂ)‖)
            * ∑' m : ℕ, a' m * (m : ℝ) ^ (-x)) :=
          mul_le_mul_of_nonneg_left ih' (inv_nonneg.mpr hnz.le)
      _ = (1 - t) / ‖1 - z‖ * (∏ q ∈ P, (1 - (q : ℝ) ^ (-x))
            / ‖1 - χ (q : ZMod k) * (((q : ℝ) ^ (-x) : ℝ) : ℂ)‖)
            * ((1 - t)⁻¹ * ∑' m : ℕ, a' m * (m : ℝ) ^ (-x)) := by
          field_simp

lemma euler_ratio_le (ζ : ℂ) (hζ : ‖ζ‖ = 1) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    ((1 - t) / ‖1 - ζ * (t : ℂ)‖) ^ 2 * (1 + 2 * (1 - ζ.re) * t) ≤ 1 := by
  have h2 : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    have := Complex.normSq_eq_norm_sq ζ
    rw [hζ, Complex.normSq_apply] at this
    nlinarith
  have h1 : ‖1 - ζ * (t : ℂ)‖ ^ 2 = (1 - t) ^ 2 + 2 * (1 - ζ.re) * t := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    have hre : (1 - ζ * (t : ℂ)).re = 1 - ζ.re * t := by simp
    have him : (1 - ζ * (t : ℂ)).im = -(ζ.im * t) := by simp
    rw [hre, him]
    nlinarith
  have hre1 : ζ.re ≤ 1 := (Complex.re_le_norm ζ).trans hζ.le
  have hpos : 0 < (1 - t) ^ 2 + 2 * (1 - ζ.re) * t := by
    have : 0 < (1 - t) ^ 2 := by nlinarith
    nlinarith
  rw [div_pow, h1, div_mul_eq_mul_div, div_le_one hpos]
  have h3 : 0 ≤ 2 * (1 - ζ.re) * t := by nlinarith
  have h4 : (1 - t) ^ 2 ≤ 1 := by nlinarith
  nlinarith

lemma prod_ratio_le (ζ : ℂ) (hζ : ‖ζ‖ = 1) (f : ℕ → ℝ) :
    ∀ P : Finset ℕ, (∀ p ∈ P, 0 < f p ∧ f p < 1) →
      (∏ p ∈ P, (1 - f p) / ‖1 - ζ * (f p : ℂ)‖) ^ 2 * (1 + 2 * (1 - ζ.re) * ∑ p ∈ P, f p) ≤ 1 := by
  classical
  have hre1 : ζ.re ≤ 1 := (Complex.re_le_norm ζ).trans hζ.le
  intro P
  induction P using Finset.induction_on with
  | empty => intro _; simp
  | insert q P hqP ih =>
    intro hf
    have hq := hf q (Finset.mem_insert_self q P)
    have ih' := ih (fun p hp => hf p (Finset.mem_insert_of_mem hp))
    have h1 := euler_ratio_le ζ hζ (f q) hq.1 hq.2
    rw [Finset.prod_insert hqP, Finset.sum_insert hqP, mul_pow]
    have hS : 0 ≤ ∑ p ∈ P, f p := Finset.sum_nonneg (fun p hp => (hf p (Finset.mem_insert_of_mem hp)).1.le)
    have hA : 0 ≤ ((1 - f q) / ‖1 - ζ * (f q : ℂ)‖) ^ 2 := sq_nonneg _
    have hB : 0 ≤ (∏ p ∈ P, (1 - f p) / ‖1 - ζ * (f p : ℂ)‖) ^ 2 := sq_nonneg _
    have hη : 0 ≤ 2 * (1 - ζ.re) := by linarith
    have e : 1 + 2 * (1 - ζ.re) * (f q + ∑ p ∈ P, f p)
        ≤ (1 + 2 * (1 - ζ.re) * f q) * (1 + 2 * (1 - ζ.re) * ∑ p ∈ P, f p) := by
      have : 0 ≤ (2 * (1 - ζ.re) * f q) * (2 * (1 - ζ.re) * ∑ p ∈ P, f p) :=
        mul_nonneg (mul_nonneg hη hq.1.le) (mul_nonneg hη hS)
      nlinarith
    calc ((1 - f q) / ‖1 - ζ * (f q : ℂ)‖) ^ 2 * (∏ p ∈ P, (1 - f p) / ‖1 - ζ * (f p : ℂ)‖) ^ 2
          * (1 + 2 * (1 - ζ.re) * (f q + ∑ p ∈ P, f p))
        ≤ ((1 - f q) / ‖1 - ζ * (f q : ℂ)‖) ^ 2 * (∏ p ∈ P, (1 - f p) / ‖1 - ζ * (f p : ℂ)‖) ^ 2
          * ((1 + 2 * (1 - ζ.re) * f q) * (1 + 2 * (1 - ζ.re) * ∑ p ∈ P, f p)) :=
          mul_le_mul_of_nonneg_left e (mul_nonneg hA hB)
      _ = (((1 - f q) / ‖1 - ζ * (f q : ℂ)‖) ^ 2 * (1 + 2 * (1 - ζ.re) * f q))
          * ((∏ p ∈ P, (1 - f p) / ‖1 - ζ * (f p : ℂ)‖) ^ 2
            * (1 + 2 * (1 - ζ.re) * ∑ p ∈ P, f p)) := by ring
      _ ≤ 1 * 1 := mul_le_mul h1 ih' (mul_nonneg hB (by nlinarith)) (by norm_num)
      _ = 1 := one_mul 1

end characters

section classes

/-- Orthogonality: a class sum is at most its share plus the twisted sums. -/
lemma class_sum_le {k : ℕ} [NeZero k] (x : ℝ) (a : ℕ → ℝ) (ha : ∀ m, 0 ≤ a m)
    (hs : Summable (fun m : ℕ => a m * (m : ℝ) ^ (-x))) (ε : ℝ) (hε : 0 ≤ ε)
    (hχ : ∀ χ : DirichletCharacter ℂ k, χ ≠ 1 →
      ‖∑' m : ℕ, (a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)‖
        ≤ ε * ∑' m : ℕ, a m * (m : ℝ) ^ (-x))
    (β : ZMod k) (hβ : IsUnit β) :
    ∑' m : ℕ, (if (m : ZMod k) = β then a m * (m : ℝ) ^ (-x) else 0)
      ≤ (k.totient : ℝ)⁻¹ * (1 + Fintype.card (DirichletCharacter ℂ k) * ε)
        * ∑' m : ℕ, a m * (m : ℝ) ^ (-x) := by
  classical
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ∑' m : ℕ, a m * (m : ℝ) ^ (-x) := ⟨_, rfl⟩
  rw [← hD] at hχ ⊢
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact tsum_nonneg (fun m => mul_nonneg (ha m) (Real.rpow_nonneg (Nat.cast_nonneg m) _))
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos k)
  have hφ' : (k.totient : ℂ) ≠ 0 := by exact_mod_cast hφ.ne'
  have hterm : ∀ m : ℕ, (((if (m : ZMod k) = β then a m * (m : ℝ) ^ (-x) else 0 : ℝ)) : ℂ)
      = (k.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ k,
          χ β⁻¹ * ((a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)) := by
    intro m
    have h1 := DirichletCharacter.sum_char_inv_mul_char_eq ℂ hβ (m : ZMod k)
    have h2 : ∑ χ : DirichletCharacter ℂ k,
          χ β⁻¹ * ((a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ))
        = (∑ χ : DirichletCharacter ℂ k, χ β⁻¹ * χ (m : ZMod k))
          * ((a m : ℂ) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ _
      ring
    rw [h2, h1]
    by_cases hm : (m : ZMod k) = β
    · rw [if_pos hm, if_pos hm.symm]
      push_cast
      field_simp
    · rw [if_neg hm, if_neg (fun h => hm h.symm)]
      simp
  have hV : ((∑' m : ℕ, (if (m : ZMod k) = β then a m * (m : ℝ) ^ (-x) else 0) : ℝ) : ℂ)
      = (k.totient : ℂ)⁻¹ * ∑ χ : DirichletCharacter ℂ k, χ β⁻¹
          * ∑' m : ℕ, (a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum, tsum_congr hterm, tsum_mul_left]
    congr 1
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl
      intro χ _
      rw [tsum_mul_left]
    · intro χ _
      exact (char_term_summable χ x a ha hs).mul_left _
  have hVnn : 0 ≤ ∑' m : ℕ, (if (m : ZMod k) = β then a m * (m : ℝ) ^ (-x) else 0) := by
    apply tsum_nonneg
    intro m
    split_ifs
    · exact mul_nonneg (ha m) (Real.rpow_nonneg (Nat.cast_nonneg m) _)
    · exact le_rfl
  have hnorm := congrArg norm hV
  rw [Complex.norm_real, Real.norm_of_nonneg hVnn] at hnorm
  rw [hnorm, norm_mul, norm_inv, Complex.norm_natCast]
  have hsum : ‖∑ χ : DirichletCharacter ℂ k, χ β⁻¹
        * ∑' m : ℕ, (a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)‖
      ≤ (1 + Fintype.card (DirichletCharacter ℂ k) * ε) * D := by
    calc ‖∑ χ : DirichletCharacter ℂ k, χ β⁻¹
          * ∑' m : ℕ, (a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)‖
        ≤ ∑ χ : DirichletCharacter ℂ k, ‖χ β⁻¹
          * ∑' m : ℕ, (a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ χ : DirichletCharacter ℂ k, ((if χ = 1 then D else 0) + ε * D) := by
          apply Finset.sum_le_sum
          intro χ _
          rw [norm_mul]
          have h1 := DirichletCharacter.norm_le_one χ β⁻¹
          have h3 : ‖χ β⁻¹‖ * ‖∑' m : ℕ, (a m : ℂ) * χ (m : ZMod k)
              * (((m : ℝ) ^ (-x) : ℝ) : ℂ)‖
              ≤ ‖∑' m : ℕ, (a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)‖ := by
            calc _ ≤ 1 * ‖∑' m : ℕ, (a m : ℂ) * χ (m : ZMod k)
                  * (((m : ℝ) ^ (-x) : ℝ) : ℂ)‖ :=
                  mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
              _ = _ := one_mul _
          have hεD : 0 ≤ ε * D := mul_nonneg hε hD0
          by_cases h : χ = 1
          · rw [if_pos h]
            have := char_sum_norm_le χ x a ha hs
            rw [← hD] at this
            linarith
          · rw [if_neg h]
            have := hχ χ h
            linarith
      _ = (1 + Fintype.card (DirichletCharacter ℂ k) * ε) * D := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
          simp
          ring
  calc ((k.totient : ℕ) : ℝ)⁻¹ * ‖∑ χ : DirichletCharacter ℂ k, χ β⁻¹
          * ∑' m : ℕ, (a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)‖
      ≤ ((k.totient : ℕ) : ℝ)⁻¹ * ((1 + Fintype.card (DirichletCharacter ℂ k) * ε) * D) :=
        mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hφ.le)
    _ = _ := by ring

end classes

section dirdiv

open ArithmeticFunction ArithmeticFunction.vonMangoldt

/-- If `∑ 1/p` converges over a set of primes, then `∑ log p · p^{-x}` over that set is
`O(1) + o(1/(x-1))`. -/
lemma log_sum_le_of_summable (Pr : ℕ → Prop) [DecidablePred Pr] (hPr : ∀ p, Pr p → p.Prime)
    (x : ℝ) (hx : 1 < x) (z : ℕ) (τ : ℝ)
    (hsum : Summable (fun p : ℕ => if Pr p then (1 : ℝ) / p else 0))
    (hz : ∑' p : ℕ, (if Pr p then (1 : ℝ) / p else 0)
        - ∑ p ∈ Finset.range z, (if Pr p then (1 : ℝ) / p else 0) ≤ τ) (Y : ℕ) :
    ∑ p ∈ Finset.range Y, (if Pr p then Real.log p * (p : ℝ) ^ (-x) else 0)
      ≤ ∑ p ∈ Finset.range z, Real.log p + (1 / (x - 1)) * τ := by
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = fun p : ℕ => if Pr p then (1 : ℝ) / p else 0 := ⟨_, rfl⟩
  rw [← hg] at hsum hz
  have hg0 : ∀ p, 0 ≤ g p := by
    intro p
    rw [hg]
    dsimp only
    split_ifs
    · positivity
    · exact le_rfl
  have hδ : 0 < x - 1 := by linarith
  have hterm : ∀ p : ℕ, (if Pr p then Real.log p * (p : ℝ) ^ (-x) else 0)
      ≤ (if p < z then Real.log p else 0) + (1 / (x - 1)) * (if z ≤ p then g p else 0) := by
    intro p
    by_cases hsp : Pr p
    · rw [if_pos hsp]
      have hpp := hPr p hsp
      have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpp.one_le
      have hppos : (0 : ℝ) < p := by linarith
      have hlog : 0 ≤ Real.log p := Real.log_nonneg hp1
      by_cases hpz : p < z
      · rw [if_pos hpz, if_neg (by omega), mul_zero, add_zero]
        have h1 : (p : ℝ) ^ (-x) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hp1 (by linarith)
        calc Real.log p * (p : ℝ) ^ (-x) ≤ Real.log p * 1 := mul_le_mul_of_nonneg_left h1 hlog
          _ = Real.log p := mul_one _
      · rw [if_neg hpz, if_pos (by omega), zero_add]
        have hgp : g p = 1 / (p : ℝ) := by
          rw [hg]
          dsimp only
          rw [if_pos hsp]
        rw [hgp]
        have e : (p : ℝ) ^ (-x) = (p : ℝ) ^ (-(x - 1)) * (p : ℝ)⁻¹ := by
          rw [← Real.rpow_neg_one (p : ℝ), ← Real.rpow_add hppos]
          congr 1
          ring
        have h1 := Real.log_le_rpow_div hppos.le hδ
        have h2 : (p : ℝ) ^ (-(x - 1)) = ((p : ℝ) ^ (x - 1))⁻¹ := Real.rpow_neg hppos.le _
        have h3 : 0 < (p : ℝ) ^ (x - 1) := Real.rpow_pos_of_pos hppos _
        have h4 : Real.log p * (p : ℝ) ^ (-(x - 1)) ≤ 1 / (x - 1) := by
          rw [h2, ← div_eq_mul_inv, div_le_iff₀ h3]
          calc Real.log p ≤ (p : ℝ) ^ (x - 1) / (x - 1) := h1
            _ = 1 / (x - 1) * (p : ℝ) ^ (x - 1) := by ring
        rw [e]
        calc Real.log p * ((p : ℝ) ^ (-(x - 1)) * (p : ℝ)⁻¹)
            = (Real.log p * (p : ℝ) ^ (-(x - 1))) * (p : ℝ)⁻¹ := by ring
          _ ≤ (1 / (x - 1)) * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h4 (by positivity)
          _ = 1 / (x - 1) * (1 / (p : ℝ)) := by ring
    · rw [if_neg hsp]
      have h1 : 0 ≤ (if p < z then Real.log p else 0) := by
        split_ifs
        · exact Real.log_natCast_nonneg p
        · exact le_rfl
      have h2 : 0 ≤ (1 / (x - 1)) * (if z ≤ p then g p else 0) := by
        apply mul_nonneg (by positivity)
        split_ifs
        · exact hg0 p
        · exact le_rfl
      linarith
  have hA : ∑ p ∈ Finset.range Y, (if p < z then Real.log p else 0)
      ≤ ∑ p ∈ Finset.range z, Real.log p := by
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      rw [Finset.mem_filter] at hp
      rw [Finset.mem_range]
      exact hp.2
    · intro p _ _
      exact Real.log_natCast_nonneg p
  have hB : ∑ p ∈ Finset.range Y, (if z ≤ p then g p else 0) ≤ τ := by
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = max Y z := ⟨_, rfl⟩
    have hN1 : Y ≤ N := by rw [hN]; exact le_max_left _ _
    have hN2 : z ≤ N := by rw [hN]; exact le_max_right _ _
    have e1 : ∀ p : ℕ, (if z ≤ p then g p else 0) + (if p < z then g p else 0) = g p := by
      intro p
      by_cases h : p < z
      · rw [if_neg (by omega), if_pos h, zero_add]
      · rw [if_pos (by omega), if_neg h, add_zero]
    have h1 : ∑ p ∈ Finset.range Y, (if z ≤ p then g p else 0)
        ≤ ∑ p ∈ Finset.range N, (if z ≤ p then g p else 0) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hN1)
      intro p _ _
      split_ifs
      · exact hg0 p
      · exact le_rfl
    have h2 : ∑ p ∈ Finset.range z, g p
        = ∑ p ∈ Finset.range N, (if p < z then g p else 0) := by
      rw [← Finset.sum_filter]
      apply Finset.sum_congr _ (fun _ _ => rfl)
      ext p
      simp only [Finset.mem_range, Finset.mem_filter]
      omega
    have h3 : ∑ p ∈ Finset.range N, (if z ≤ p then g p else 0)
        + ∑ p ∈ Finset.range N, (if p < z then g p else 0) = ∑ p ∈ Finset.range N, g p := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun p _ => e1 p)
    have h4 : ∑ p ∈ Finset.range N, g p ≤ ∑' p, g p :=
      hsum.sum_le_tsum _ (fun p _ => hg0 p)
    linarith
  calc ∑ p ∈ Finset.range Y, (if Pr p then Real.log p * (p : ℝ) ^ (-x) else 0)
      ≤ ∑ p ∈ Finset.range Y, ((if p < z then Real.log p else 0)
          + (1 / (x - 1)) * (if z ≤ p then g p else 0)) :=
        Finset.sum_le_sum (fun p _ => hterm p)
    _ = ∑ p ∈ Finset.range Y, (if p < z then Real.log p else 0)
          + (1 / (x - 1)) * ∑ p ∈ Finset.range Y, (if z ≤ p then g p else 0) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ ∑ p ∈ Finset.range z, Real.log p + (1 / (x - 1)) * τ := by
        have := mul_le_mul_of_nonneg_left hB (by positivity : (0 : ℝ) ≤ 1 / (x - 1))
        linarith

/-- Dirichlet's theorem in the form: `∑ 1/p` diverges over the primes of an invertible class. -/
theorem not_summable_primes_class (N : ℕ) [NeZero N] (a : ZMod N) (ha : IsUnit a) :
    ¬ Summable (fun p : ℕ => if p.Prime ∧ (p : ZMod N) = a then (1 : ℝ) / p else 0) := by
  intro hsum
  obtain ⟨C', hC'⟩ := LSeries_residueClass_lower_bound ha
  have hnp := summable_residueClass_non_primes_div a
  obtain ⟨Cnp, hCnp⟩ : ∃ Cnp : ℝ,
      Cnp = ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / n := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (N.totient : ℝ)⁻¹ := ⟨_, rfl⟩
  have hA0 : 0 < A := by
    rw [hA]
    exact inv_pos.mpr (by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos N))
  rw [← hA] at hC'
  obtain ⟨z, hz⟩ : ∃ z : ℕ,
      ∑' p : ℕ, (if p.Prime ∧ (p : ZMod N) = a then (1 : ℝ) / p else 0)
        - ∑ p ∈ Finset.range z, (if p.Prime ∧ (p : ZMod N) = a then (1 : ℝ) / p else 0)
        ≤ A / 2 := by
    have h1 := hsum.hasSum.tendsto_sum_nat
    have h2 := h1.eventually (lt_mem_nhds
      (show ∑' p : ℕ, (if p.Prime ∧ (p : ZMod N) = a then (1 : ℝ) / p else 0) - A / 2
        < ∑' p : ℕ, (if p.Prime ∧ (p : ZMod N) = a then (1 : ℝ) / p else 0) by linarith))
    obtain ⟨z, hz⟩ := h2.exists
    exact ⟨z, by linarith⟩
  obtain ⟨Cz, hCz⟩ : ∃ Cz : ℝ, Cz = ∑ p ∈ Finset.range z, Real.log p := ⟨_, rfl⟩
  have key : ∀ x : ℝ, 1 < x → x ≤ 2 →
      A / (x - 1) - C' ≤ Cnp + Cz + (1 / (x - 1)) * (A / 2) := by
    intro x hx1 hx2
    refine (hC' ⟨hx1, hx2⟩).trans ?_
    apply Real.tsum_le_of_sum_range_le
      (fun n => div_nonneg (residueClass_nonneg a n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    intro M
    have hterm : ∀ n : ℕ, residueClass a n / (n : ℝ) ^ x
        ≤ (if n.Prime then 0 else residueClass a n) / n
          + (if n.Prime ∧ (n : ZMod N) = a then Real.log n * (n : ℝ) ^ (-x) else 0) := by
      intro n
      by_cases hn : n.Prime
      · rw [if_pos hn, zero_div, zero_add]
        by_cases hna : (n : ZMod N) = a
        · rw [if_pos ⟨hn, hna⟩]
          have h4 : residueClass a n = Real.log n := by
            rw [residueClass, Set.indicator_of_mem (show n ∈ {m : ℕ | (m : ZMod N) = a} from hna)]
            exact vonMangoldt_apply_prime hn
          rw [h4, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
        · rw [if_neg (fun h => hna h.2)]
          have h4 : residueClass a n = 0 := by
            rw [residueClass,
              Set.indicator_of_notMem (show n ∉ {m : ℕ | (m : ZMod N) = a} from hna)]
          rw [h4, zero_div]
      · rw [if_neg hn, if_neg (fun h => hn h.1), add_zero]
        rcases Nat.eq_zero_or_pos n with rfl | hpos
        · simp
        · apply div_le_div_of_nonneg_left (residueClass_nonneg a n) (by exact_mod_cast hpos)
          conv_lhs => rw [← Real.rpow_one n]
          exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpos) hx1.le
    have h5 : ∑ n ∈ Finset.range M, (if n.Prime then 0 else residueClass a n) / n ≤ Cnp := by
      rw [hCnp]
      refine hnp.sum_le_tsum _ (fun n _ => ?_)
      apply div_nonneg _ (Nat.cast_nonneg n)
      split_ifs
      · exact le_rfl
      · exact residueClass_nonneg a n
    have h6 := log_sum_le_of_summable (fun p : ℕ => p.Prime ∧ (p : ZMod N) = a)
      (fun p h => h.1) x hx1 z (A / 2) hsum hz M
    rw [← hCz] at h6
    calc ∑ n ∈ Finset.range M, residueClass a n / (n : ℝ) ^ x
        ≤ ∑ n ∈ Finset.range M, ((if n.Prime then 0 else residueClass a n) / n
          + (if n.Prime ∧ (n : ZMod N) = a then Real.log n * (n : ℝ) ^ (-x) else 0)) :=
          Finset.sum_le_sum (fun n _ => hterm n)
      _ = ∑ n ∈ Finset.range M, (if n.Prime then 0 else residueClass a n) / n
          + ∑ n ∈ Finset.range M,
            (if n.Prime ∧ (n : ZMod N) = a then Real.log n * (n : ℝ) ^ (-x) else 0) :=
          Finset.sum_add_distrib
      _ ≤ Cnp + Cz + (1 / (x - 1)) * (A / 2) := by linarith
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = max 1 (C' + Cnp + Cz) := ⟨_, rfl⟩
  have hK1 : 1 ≤ K := by rw [hK]; exact le_max_left _ _
  have hK2 : C' + Cnp + Cz ≤ K := by rw [hK]; exact le_max_right _ _
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min 1 (A / (4 * K)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by
    rw [hδ]
    exact lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := by rw [hδ]; exact min_le_left _ _
  have hδ2 : δ ≤ A / (4 * K) := by rw [hδ]; exact min_le_right _ _
  have h1 := key (1 + δ) (by linarith) (by linarith)
  rw [show (1 + δ) - 1 = δ by ring] at h1
  have h2 : A / 2 ≤ (C' + Cnp + Cz) * δ := by
    have e : A / δ - C' - (Cnp + Cz + 1 / δ * (A / 2)) = (A / 2 - (C' + Cnp + Cz) * δ) / δ := by
      field_simp
      ring
    have h3 : (A / 2 - (C' + Cnp + Cz) * δ) / δ ≤ 0 := by
      rw [← e]
      linarith
    have h4 : A / 2 - (C' + Cnp + Cz) * δ ≤ 0 := by
      by_contra hneg
      push Not at hneg
      have := div_pos hneg hδ0
      linarith
    linarith
  have h3 : (C' + Cnp + Cz) * δ ≤ K * δ := mul_le_mul_of_nonneg_right hK2 hδ0.le
  have h4 : K * δ ≤ K * (A / (4 * K)) := mul_le_mul_of_nonneg_left hδ2 (by linarith)
  have h5 : K * (A / (4 * K)) = A / 4 := by
    field_simp
  linarith

end dirdiv

section equidist

/-- Many primes `≡ 2 (mod 3)` in a prescribed invertible class modulo `k`, avoiding `E`. -/
lemma exists_primes_class (k : ℕ) [NeZero k] (hk3 : Nat.Coprime 3 k) (β : ZMod k)
    (hβ : IsUnit β) (E : Finset ℕ) (M : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ p % 3 = 2 ∧ (p : ZMod k) = β ∧ p ∉ E)
      ∧ M ≤ ∑ p ∈ P, (1 : ℝ) / p := by
  classical
  have hk0 : 0 < k := NeZero.pos k
  have : NeZero (3 * k) := ⟨by omega⟩
  obtain ⟨x₀, hx3, hxk⟩ : ∃ x₀ : ℕ, x₀ ≡ 2 [MOD 3] ∧ x₀ ≡ β.val [MOD k] :=
    ⟨_, (Nat.chineseRemainder hk3 2 β.val).2⟩
  have hβv : Nat.Coprime β.val k := by
    rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    exact hβ
  have hcop : Nat.Coprime x₀ (3 * k) := by
    apply Nat.Coprime.mul_right
    · rw [Nat.coprime_iff_gcd_eq_one, hx3.gcd_eq]
      rfl
    · rw [Nat.coprime_iff_gcd_eq_one, hxk.gcd_eq]
      exact hβv
  have ha' : IsUnit ((x₀ : ℕ) : ZMod (3 * k)) := (ZMod.isUnit_iff_coprime x₀ (3 * k)).mpr hcop
  have hns := not_summable_primes_class (3 * k) (x₀ : ZMod (3 * k)) ha'
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = fun p : ℕ =>
      if p.Prime ∧ (p : ZMod (3 * k)) = (x₀ : ZMod (3 * k)) then (1 : ℝ) / p else 0 := ⟨_, rfl⟩
  rw [← hg] at hns
  have hg0 : ∀ p, 0 ≤ g p := by
    intro p
    rw [hg]
    dsimp only
    split_ifs
    · positivity
    · exact le_rfl
  obtain ⟨g', hg'⟩ : ∃ g' : ℕ → ℝ, g' = fun p : ℕ => if p ∈ E then 0 else g p := ⟨_, rfl⟩
  have hg'0 : ∀ p, 0 ≤ g' p := by
    intro p
    rw [hg']
    dsimp only
    split_ifs
    · exact le_rfl
    · exact hg0 p
  have hns' : ¬ Summable g' := by
    intro h
    apply hns
    have hfin : Summable (fun p => if p ∈ E then g p else 0) :=
      summable_of_ne_finset_zero (s := E) (fun p hp => if_neg hp)
    refine (h.add hfin).congr (fun p => ?_)
    rw [hg']
    dsimp only
    split_ifs <;> simp
  have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg hg'0).mp hns'
  obtain ⟨n, hn⟩ := (htend.eventually (Filter.eventually_ge_atTop M)).exists
  refine ⟨(Finset.range n).filter
    (fun p => (p.Prime ∧ (p : ZMod (3 * k)) = (x₀ : ZMod (3 * k))) ∧ p ∉ E), ?_, ?_⟩
  · intro p hp
    obtain ⟨_, ⟨hpp, hpa⟩, hpE⟩ := Finset.mem_filter.mp hp
    have hmod : p ≡ x₀ [MOD 3 * k] := (ZMod.natCast_eq_natCast_iff p x₀ (3 * k)).mp hpa
    have h3 : p ≡ x₀ [MOD 3] := Nat.ModEq.of_mul_right k hmod
    have hk' : p ≡ x₀ [MOD k] := Nat.ModEq.of_mul_left 3 hmod
    refine ⟨hpp, ?_, ?_, hpE⟩
    · have h4 : p % 3 = 2 % 3 := h3.trans hx3
      omega
    · have h4 := (ZMod.natCast_eq_natCast_iff p β.val k).mpr (hk'.trans hxk)
      rw [h4, ZMod.natCast_zmod_val]
  · refine hn.trans (le_of_eq ?_)
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    rw [hg', hg]
    dsimp only
    by_cases hE : p ∈ E
    · rw [if_pos hE, if_neg (fun h => h.2 hE)]
    · rw [if_neg hE]
      by_cases hc : p.Prime ∧ (p : ZMod (3 * k)) = (x₀ : ZMod (3 * k))
      · rw [if_pos hc, if_pos ⟨hc, hE⟩]
      · rw [if_neg hc, if_neg (fun h => hc h.1)]

/-- For `x` close to `1`, `p ^ (-x) ≥ 1 / (2 p)` uniformly over a finite set. -/
lemma rpow_neg_ge (P : Finset ℕ) :
    ∃ η : ℝ, 0 < η ∧ ∀ p ∈ P, 0 < p → ∀ x : ℝ, 1 < x → x < 1 + η →
      1 / (2 * (p : ℝ)) ≤ (p : ℝ) ^ (-x) := by
  obtain ⟨B, hB⟩ : ∃ B : ℕ, B = ∑ p ∈ P, p := ⟨_, rfl⟩
  refine ⟨((B + 1 : ℕ) : ℝ)⁻¹, by positivity, ?_⟩
  intro p hp hp0 x hx1 hx2
  have hpB : p ≤ B := by
    rw [hB]
    exact Finset.single_le_sum (fun i _ => Nat.zero_le i) hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp0
  have hppos : (0 : ℝ) < p := by linarith
  have h1 : (p : ℝ) ^ (x - 1) ≤ (p : ℝ) ^ (((B + 1 : ℕ) : ℝ)⁻¹) :=
    Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
  have h2 : (p : ℝ) ^ (((B + 1 : ℕ) : ℝ)⁻¹) ≤ ((2 : ℝ) ^ (B + 1)) ^ (((B + 1 : ℕ) : ℝ)⁻¹) := by
    apply Real.rpow_le_rpow hppos.le _ (by positivity)
    have h3 : p < 2 ^ (B + 1) := lt_of_le_of_lt hpB (lt_trans (Nat.lt_succ_self B) Nat.lt_two_pow_self)
    exact_mod_cast h3.le
  have h4 : ((2 : ℝ) ^ (B + 1)) ^ (((B + 1 : ℕ) : ℝ)⁻¹) = 2 :=
    Real.pow_rpow_inv_natCast (by norm_num) (by omega)
  have h5 : (p : ℝ) ^ (x - 1) ≤ 2 := by
    rw [h4] at h2
    exact h1.trans h2
  have h6 : 0 < (p : ℝ) ^ (x - 1) := Real.rpow_pos_of_pos hppos _
  have e : (p : ℝ) ^ (-x) = ((p : ℝ) ^ (x - 1))⁻¹ * (p : ℝ)⁻¹ := by
    rw [← Real.rpow_neg hppos.le, ← Real.rpow_neg_one (p : ℝ), ← Real.rpow_add hppos]
    congr 1
    ring
  rw [e, one_div, mul_inv]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  exact inv_anti₀ h6 h5

/-- Equidistribution in the invertible classes modulo `k` (logarithmic density) for every
nonnegative weight invariant under multiplication by suitable primes `≡ 2 (mod 3)`. -/
lemma equidist (k : ℕ) [NeZero k] (hk3 : Nat.Coprime 3 k) (E : Finset ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ (P : Finset ℕ) (η : ℝ), 0 < η ∧ (∀ p ∈ P, p.Prime ∧ p % 3 = 2 ∧ p ∉ E) ∧
      ∀ x : ℝ, 1 < x → x < 1 + η → ∀ a : ℕ → ℝ, (∀ m, 0 ≤ a m) →
        Summable (fun m : ℕ => a m * (m : ℝ) ^ (-x)) → (∀ p ∈ P, ∀ m, a (p * m) = a m) →
        ∀ β : ZMod k, IsUnit β →
          ∑' m : ℕ, (if (m : ZMod k) = β then a m * (m : ℝ) ^ (-x) else 0)
            ≤ (1 + ε) / k.totient * ∑' m : ℕ, a m * (m : ℝ) ^ (-x) := by
  classical
  obtain ⟨Nχ, hNχ⟩ : ∃ Nχ : ℕ, Nχ = Fintype.card (DirichletCharacter ℂ k) := ⟨_, rfl⟩
  have hNpos : 0 < Nχ := by
    rw [hNχ]
    exact Fintype.card_pos
  have hNposR : (0 : ℝ) < Nχ := by exact_mod_cast hNpos
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = ε / Nχ := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε']; positivity
  have hchoice : ∀ χ : DirichletCharacter ℂ k, ∃ Pχ : Finset ℕ,
      (∀ p ∈ Pχ, p.Prime ∧ p % 3 = 2 ∧ p ∉ E) ∧
      (χ ≠ 1 → ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ (∀ p ∈ Pχ, χ (p : ZMod k) = ζ)
        ∧ 1 ≤ ε' ^ 2 * (1 + (1 - ζ.re) * ∑ p ∈ Pχ, (1 : ℝ) / p)) := by
    intro χ
    by_cases hχ : χ = 1
    · exact ⟨∅, by simp, fun h => absurd hχ h⟩
    · obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hχ
      have hnorm : ‖χ (u : ZMod k)‖ = 1 := DirichletCharacter.unit_norm_eq_one χ u
      have hre : (χ (u : ZMod k)).re < 1 := by
        rcases lt_or_eq_of_le ((Complex.re_le_norm _).trans hnorm.le) with h | h
        · exact h
        · exfalso
          apply hu
          have h2 := Complex.normSq_eq_norm_sq (χ (u : ZMod k))
          rw [hnorm, Complex.normSq_apply, h] at h2
          have him : (χ (u : ZMod k)).im = 0 := by nlinarith
          exact Complex.ext (by simpa using h) (by simpa using him)
      obtain ⟨Pχ, hP1, hP2⟩ := exists_primes_class k hk3 (u : ZMod k) u.isUnit E
        (1 / ε' ^ 2 / (1 - (χ (u : ZMod k)).re))
      refine ⟨Pχ, fun p hp => ⟨(hP1 p hp).1, (hP1 p hp).2.1, (hP1 p hp).2.2.2⟩, fun _ => ?_⟩
      refine ⟨χ (u : ZMod k), hnorm, fun p hp => by rw [(hP1 p hp).2.2.1], ?_⟩
      have hpos : 0 < 1 - (χ (u : ZMod k)).re := by linarith
      have h3 : 1 / ε' ^ 2 ≤ (1 - (χ (u : ZMod k)).re) * ∑ p ∈ Pχ, (1 : ℝ) / p := by
        have := mul_le_mul_of_nonneg_left hP2 hpos.le
        have e : (1 - (χ (u : ZMod k)).re) * (1 / ε' ^ 2 / (1 - (χ (u : ZMod k)).re))
            = 1 / ε' ^ 2 := by field_simp
        linarith
      have h4 : ε' ^ 2 * (1 / ε' ^ 2) = 1 := by field_simp
      have h5 : 0 < ε' ^ 2 := by positivity
      nlinarith
  choose Pf hPf using hchoice
  obtain ⟨P, hPdef⟩ : ∃ P : Finset ℕ, P = Finset.univ.biUnion Pf := ⟨_, rfl⟩
  have hsub : ∀ χ, Pf χ ⊆ P := by
    intro χ p hp
    rw [hPdef, Finset.mem_biUnion]
    exact ⟨χ, Finset.mem_univ _, hp⟩
  have hPprop : ∀ p ∈ P, p.Prime ∧ p % 3 = 2 ∧ p ∉ E := by
    intro p hp
    rw [hPdef, Finset.mem_biUnion] at hp
    obtain ⟨χ, _, hpχ⟩ := hp
    exact (hPf χ).1 p hpχ
  obtain ⟨η, hη, hηb⟩ := rpow_neg_ge P
  refine ⟨P, η, hη, hPprop, ?_⟩
  intro x hx1 hx2 a ha hs hinv β hβ
  have hφ : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos k)
  have hD0 : 0 ≤ ∑' m : ℕ, a m * (m : ℝ) ^ (-x) :=
    tsum_nonneg (fun m => mul_nonneg (ha m) (Real.rpow_nonneg (Nat.cast_nonneg m) _))
  have hχbound : ∀ χ : DirichletCharacter ℂ k, χ ≠ 1 →
      ‖∑' m : ℕ, (a m : ℂ) * χ (m : ZMod k) * (((m : ℝ) ^ (-x) : ℝ) : ℂ)‖
        ≤ ε' * ∑' m : ℕ, a m * (m : ℝ) ^ (-x) := by
    intro χ hχ
    obtain ⟨ζ, hζ, hζp, hbig⟩ := (hPf χ).2 hχ
    have h1 := char_sum_le χ x hx1 (Pf χ) (fun p hp => ((hPf χ).1 p hp).1) a ha hs
      (fun p hp m => hinv p (hsub χ hp) m)
    have hf : ∀ p ∈ Pf χ, 0 < (p : ℝ) ^ (-x) ∧ (p : ℝ) ^ (-x) < 1 := by
      intro p hp
      have hpp := ((hPf χ).1 p hp).1
      have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
      exact ⟨Real.rpow_pos_of_pos (by linarith) _,
        Real.rpow_lt_one_of_one_lt_of_neg hp1 (by linarith)⟩
    have h2 := prod_ratio_le ζ hζ (fun p : ℕ => (p : ℝ) ^ (-x)) (Pf χ) hf
    have hprodeq : ∏ p ∈ Pf χ, (1 - (p : ℝ) ^ (-x))
          / ‖1 - χ (p : ZMod k) * (((p : ℝ) ^ (-x) : ℝ) : ℂ)‖
        = ∏ p ∈ Pf χ, (1 - (p : ℝ) ^ (-x)) / ‖1 - ζ * (((p : ℝ) ^ (-x) : ℝ) : ℂ)‖ := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [hζp p hp]
    rw [hprodeq] at h1
    obtain ⟨Pi0, hPi0⟩ : ∃ Pi0 : ℝ, Pi0 = ∏ p ∈ Pf χ, (1 - (p : ℝ) ^ (-x))
        / ‖1 - ζ * (((p : ℝ) ^ (-x) : ℝ) : ℂ)‖ := ⟨_, rfl⟩
    rw [← hPi0] at h1 h2
    have hPi00 : 0 ≤ Pi0 := by
      rw [hPi0]
      apply Finset.prod_nonneg
      intro p hp
      exact div_nonneg (by linarith [(hf p hp).2]) (norm_nonneg _)
    have hre1 : ζ.re ≤ 1 := (Complex.re_le_norm ζ).trans hζ.le
    have hsum : ∑ p ∈ Pf χ, (1 : ℝ) / p ≤ 2 * ∑ p ∈ Pf χ, (p : ℝ) ^ (-x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro p hp
      have hpp := ((hPf χ).1 p hp).1
      have := hηb p (hsub χ hp) hpp.pos x hx1 hx2
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
      have e : (1 : ℝ) / p = 2 * (1 / (2 * (p : ℝ))) := by field_simp
      rw [e]
      linarith
    have hT : 1 + (1 - ζ.re) * ∑ p ∈ Pf χ, (1 : ℝ) / p
        ≤ 1 + 2 * (1 - ζ.re) * ∑ p ∈ Pf χ, (p : ℝ) ^ (-x) := by
      have := mul_le_mul_of_nonneg_left hsum (by linarith : (0 : ℝ) ≤ 1 - ζ.re)
      linarith
    have hTpos : 0 < 1 + (1 - ζ.re) * ∑ p ∈ Pf χ, (1 : ℝ) / p := by
      have : 0 ≤ (1 - ζ.re) * ∑ p ∈ Pf χ, (1 : ℝ) / p :=
        mul_nonneg (by linarith) (Finset.sum_nonneg (fun p _ => by positivity))
      linarith
    have h3 : Pi0 ^ 2 * (1 + (1 - ζ.re) * ∑ p ∈ Pf χ, (1 : ℝ) / p) ≤ 1 :=
      (mul_le_mul_of_nonneg_left hT (sq_nonneg Pi0)).trans h2
    have h4 : Pi0 ^ 2 ≤ ε' ^ 2 := by
      by_contra hneg
      push Not at hneg
      have := mul_lt_mul_of_pos_right hneg hTpos
      linarith
    have h5 : Pi0 ≤ ε' := (pow_le_pow_iff_left₀ hPi00 hε'0.le two_ne_zero).mp h4
    exact h1.trans (mul_le_mul_of_nonneg_right h5 hD0)
  have h6 := class_sum_le x a ha hs ε' hε'0.le hχbound β hβ
  rw [← hNχ] at h6
  have e : ((k.totient : ℕ) : ℝ)⁻¹ * (1 + (Nχ : ℝ) * ε') = (1 + ε) / k.totient := by
    rw [hε']
    field_simp
  rw [e] at h6
  exact h6

end equidist



section weights

/-- Primes of `Q` dividing `d` exactly once. -/
def exactSet (Q : Finset ℕ) (d : ℕ) : Finset ℕ := Q.filter (fun q => q ∣ d ∧ ¬ q ^ 2 ∣ d)

/-- Base weight: `ν(d) d^{-x}` on the integers coprime to `L`. -/
noncomputable def bw (c : ℤ) (L : ℕ) (x : ℝ) (d : ℕ) : ℝ :=
  if Nat.Coprime d L then (nu c d : ℝ) * (d : ℝ) ^ (-x) else 0

/-- Weight damped by `5/8` for each prime of `Q` dividing `d` exactly once. -/
noncomputable def Fw (c : ℤ) (L : ℕ) (x : ℝ) (Q : Finset ℕ) (d : ℕ) : ℝ :=
  (5 / 8 : ℝ) ^ (exactSet Q d).card * bw c L x d

lemma bw_nonneg (c : ℤ) (L : ℕ) (x : ℝ) (d : ℕ) : 0 ≤ bw c L x d := by
  unfold bw
  split_ifs
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  · exact le_rfl

lemma bw_le (c : ℤ) (L : ℕ) (x : ℝ) (d : ℕ) : bw c L x d ≤ (nu c d : ℝ) * (d : ℝ) ^ (-x) := by
  unfold bw
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)

lemma summable_bw (c : ℤ) (L : ℕ) (x : ℝ)
    (hs : Summable (fun d : ℕ => (nu c d : ℝ) * (d : ℝ) ^ (-x))) : Summable (bw c L x) :=
  Summable.of_nonneg_of_le (bw_nonneg c L x) (bw_le c L x) hs

lemma Fw_nonneg (c : ℤ) (L : ℕ) (x : ℝ) (Q : Finset ℕ) (d : ℕ) : 0 ≤ Fw c L x Q d :=
  mul_nonneg (by positivity) (bw_nonneg c L x d)

lemma Fw_le (c : ℤ) (L : ℕ) (x : ℝ) (Q : Finset ℕ) (d : ℕ) : Fw c L x Q d ≤ bw c L x d := by
  unfold Fw
  have h1 : (5 / 8 : ℝ) ^ (exactSet Q d).card ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  calc (5 / 8 : ℝ) ^ (exactSet Q d).card * bw c L x d ≤ 1 * bw c L x d :=
        mul_le_mul_of_nonneg_right h1 (bw_nonneg c L x d)
    _ = bw c L x d := one_mul _

lemma summable_Fw (c : ℤ) (L : ℕ) (x : ℝ) (Q : Finset ℕ)
    (hs : Summable (fun d : ℕ => (nu c d : ℝ) * (d : ℝ) ^ (-x))) : Summable (Fw c L x Q) :=
  Summable.of_nonneg_of_le (Fw_nonneg c L x Q) (Fw_le c L x Q) (summable_bw c L x hs)

/-- Multiplying by a prime outside `Q` does not change the exact-division set. -/
lemma exactSet_mul (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (p : ℕ) (hp : p.Prime) (hpQ : p ∉ Q)
    (m : ℕ) : exactSet Q (p * m) = exactSet Q m := by
  unfold exactSet
  apply Finset.filter_congr
  intro q hq
  have hqp : q.Prime := hQ q hq
  have hne : q ≠ p := fun h => hpQ (h ▸ hq)
  have hcop : Nat.Coprime q p := (Nat.coprime_primes hqp hp).mpr hne
  have h1 : q ∣ p * m ↔ q ∣ m := hcop.dvd_mul_left
  have h2 : q ^ 2 ∣ p * m ↔ q ^ 2 ∣ m := (Nat.Coprime.pow_left 2 hcop).dvd_mul_left
  rw [h1, h2]

lemma exactSet_insert_card (Q : Finset ℕ) (q : ℕ) (hq : q ∉ Q) (d : ℕ) :
    (exactSet (insert q Q) d).card
      = (exactSet Q d).card + (if q ∣ d ∧ ¬ q ^ 2 ∣ d then 1 else 0) := by
  unfold exactSet
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    intro hmem
    exact hq (Finset.mem_filter.mp hmem).1
  · rfl

lemma bw_mul_split (c : ℤ) (L : ℕ) (x : ℝ) (q : ℕ) (hq : Psplit c q) (hqL : ¬ q ∣ L) (m : ℕ) :
    bw c L x (q * m) = (if q ∣ m then 1 else 3) * (q : ℝ) ^ (-x) * bw c L x m := by
  have hqp := hq.1
  have hcopq : Nat.Coprime q L := (Nat.Prime.coprime_iff_not_dvd hqp).mpr hqL
  have hiff : Nat.Coprime (q * m) L ↔ Nat.Coprime m L := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨fun h => h.2, fun h => ⟨hcopq, h⟩⟩
  unfold bw
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [nu_zero]
  by_cases hcop : Nat.Coprime m L
  · rw [if_pos (hiff.mpr hcop), if_pos hcop, nu_prime_mul c q m hqp hq.2.2.1 hm, nu_split c q hq]
    have e : ((q * m : ℕ) : ℝ) ^ (-x) = (q : ℝ) ^ (-x) * (m : ℝ) ^ (-x) := by
      push_cast
      exact Real.mul_rpow (Nat.cast_nonneg q) (Nat.cast_nonneg m)
    rw [e]
    split_ifs <;> push_cast <;> ring
  · rw [if_neg (fun h => hcop (hiff.mp h)), if_neg hcop, mul_zero]

lemma Fw_mul_split (c : ℤ) (L : ℕ) (x : ℝ) (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (q : ℕ)
    (hq : Psplit c q) (hqQ : q ∉ Q) (hqL : ¬ q ∣ L) (m : ℕ) :
    Fw c L x Q (q * m) = (if q ∣ m then 1 else 3) * (q : ℝ) ^ (-x) * Fw c L x Q m := by
  unfold Fw
  rw [exactSet_mul Q hQ q hq.1 hqQ m, bw_mul_split c L x q hq hqL m]
  ring

/-- Each split prime of `Q` saves a factor `1 - q^{-x}/2` on the damped sum. -/
lemma Fw_sum_le (c : ℤ) (L : ℕ) (x : ℝ) (hx : 1 < x)
    (hs : Summable (fun d : ℕ => (nu c d : ℝ) * (d : ℝ) ^ (-x))) :
    ∀ Q : Finset ℕ, (∀ q ∈ Q, Psplit c q ∧ ¬ q ∣ L ∧ 7 ≤ q) →
      ∑' d, Fw c L x Q d ≤ (∏ q ∈ Q, (1 - (q : ℝ) ^ (-x) / 2)) * ∑' d, bw c L x d := by
  classical
  intro Q
  induction Q using Finset.induction_on with
  | empty =>
    intro _
    rw [Finset.prod_empty, one_mul]
    apply le_of_eq
    apply tsum_congr
    intro d
    simp [Fw, exactSet]
  | insert q Q hqQ ih =>
    intro hQ
    obtain ⟨hqs, hqL, hq7⟩ := hQ q (Finset.mem_insert_self q Q)
    have hQ' : ∀ r ∈ Q, Psplit c r ∧ ¬ r ∣ L ∧ 7 ≤ r :=
      fun r hr => hQ r (Finset.mem_insert_of_mem hr)
    have hQp : ∀ r ∈ Q, r.Prime := fun r hr => (hQ' r hr).1.1
    have ih' := ih hQ'
    have hqp := hqs.1
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hqp.pos
    obtain ⟨t, ht⟩ : ∃ t : ℝ, t = (q : ℝ) ^ (-x) := ⟨_, rfl⟩
    have ht0 : 0 < t := by rw [ht]; exact Real.rpow_pos_of_pos hq0 _
    have ht7 : t ≤ 1 / 7 := by
      have h7 : (7 : ℝ) ≤ q := by exact_mod_cast hq7
      have h1 : (q : ℝ) ^ (-x) ≤ (q : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      rw [Real.rpow_neg_one] at h1
      have h2 : (q : ℝ)⁻¹ ≤ 1 / 7 := by
        rw [one_div]
        exact inv_anti₀ (by norm_num) h7
      rw [ht]
      linarith
    have hsF' := summable_Fw c L x Q hs
    have hF'0 := Fw_nonneg c L x Q
    obtain ⟨A', hA'⟩ : ∃ A' : ℝ, A' = ∑' d, Fw c L x Q d := ⟨_, rfl⟩
    have hA'0 : 0 ≤ A' := by rw [hA']; exact tsum_nonneg hF'0
    have hmul : ∀ m, Fw c L x Q (q * m) = (if q ∣ m then 1 else 3) * t * Fw c L x Q m := by
      intro m
      rw [ht]
      exact Fw_mul_split c L x Q hQp q hqs hqQ hqL m
    have hinj : Function.Injective (fun m : ℕ => q * m) :=
      fun a b hab => Nat.eq_of_mul_eq_mul_left hqp.pos hab
    -- the part supported on multiples of q
    have hsG : Summable (fun d => if q ∣ d then Fw c L x Q d else 0) := by
      refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) hsF'
      · split_ifs
        · exact hF'0 d
        · exact le_rfl
      · split_ifs
        · exact le_rfl
        · exact hF'0 d
    have hG : ∑' d, (if q ∣ d then Fw c L x Q d else 0) ≤ 3 * t * A' := by
      have hsupp : Function.support (fun d => if q ∣ d then Fw c L x Q d else 0)
          ⊆ Set.range (fun m : ℕ => q * m) := by
        intro d hd
        rw [Function.mem_support] at hd
        by_cases hdvd : q ∣ d
        · obtain ⟨m', rfl⟩ := hdvd
          exact ⟨m', rfl⟩
        · rw [if_neg hdvd] at hd
          exact absurd rfl hd
      rw [← hinj.tsum_eq hsupp, hA', ← tsum_mul_left]
      have hsL : Summable (fun m : ℕ => (fun d => if q ∣ d then Fw c L x Q d else 0) (q * m)) :=
        hsG.comp_injective hinj
      refine hsL.tsum_le_tsum (fun m => ?_) (hsF'.mul_left _)
      show (if q ∣ q * m then Fw c L x Q (q * m) else 0) ≤ 3 * t * Fw c L x Q m
      rw [if_pos (dvd_mul_right q m), hmul m]
      have h1 : ((if q ∣ m then 1 else 3 : ℝ)) ≤ 3 := by split_ifs <;> norm_num
      have h2 : 0 ≤ t * Fw c L x Q m := mul_nonneg ht0.le (hF'0 m)
      nlinarith
    -- the part with q dividing exactly once
    have hsE : Summable (fun d => if q ∣ d ∧ ¬ q ^ 2 ∣ d then Fw c L x Q d else 0) := by
      refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) hsF'
      · split_ifs
        · exact hF'0 d
        · exact le_rfl
      · split_ifs
        · exact le_rfl
        · exact hF'0 d
    have hE : 3 * t * (A' - 3 * t * A')
        ≤ ∑' d, (if q ∣ d ∧ ¬ q ^ 2 ∣ d then Fw c L x Q d else 0) := by
      have hsupp : Function.support (fun d => if q ∣ d ∧ ¬ q ^ 2 ∣ d then Fw c L x Q d else 0)
          ⊆ Set.range (fun m : ℕ => q * m) := by
        intro d hd
        rw [Function.mem_support] at hd
        by_cases hdvd : q ∣ d ∧ ¬ q ^ 2 ∣ d
        · obtain ⟨m', rfl⟩ := hdvd.1
          exact ⟨m', rfl⟩
        · rw [if_neg hdvd] at hd
          exact absurd rfl hd
      rw [← hinj.tsum_eq hsupp]
      have hterm : ∀ m : ℕ,
          (fun d => if q ∣ d ∧ ¬ q ^ 2 ∣ d then Fw c L x Q d else 0) (q * m)
            = 3 * t * (Fw c L x Q m - (if q ∣ m then Fw c L x Q m else 0)) := by
        intro m
        have hsq : q ^ 2 ∣ q * m ↔ q ∣ m := by
          rw [pow_two]
          exact Nat.mul_dvd_mul_iff_left hqp.pos
        show (if q ∣ q * m ∧ ¬ q ^ 2 ∣ q * m then Fw c L x Q (q * m) else 0) = _
        by_cases hm : q ∣ m
        · rw [if_neg (fun h => h.2 (hsq.mpr hm)), if_pos hm]
          ring
        · rw [if_pos ⟨dvd_mul_right q m, fun h => hm (hsq.mp h)⟩, hmul m, if_neg hm, if_neg hm]
          ring
      rw [tsum_congr hterm, tsum_mul_left, hsF'.tsum_sub hsG, ← hA']
      have h3 : 0 ≤ 3 * t := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hG h3]
    -- the damped sum for `insert q Q`
    have hFins : ∀ d, Fw c L x (insert q Q) d
        = Fw c L x Q d - 3 / 8 * (if q ∣ d ∧ ¬ q ^ 2 ∣ d then Fw c L x Q d else 0) := by
      intro d
      unfold Fw
      rw [exactSet_insert_card Q q hqQ d]
      split_ifs
      · rw [pow_succ]
        ring
      · rw [add_zero]
        ring
    rw [tsum_congr hFins, hsF'.tsum_sub (hsE.mul_left _), tsum_mul_left, ← hA',
      Finset.prod_insert hqQ, ← ht]
    rw [← hA'] at ih'
    have hprod0 : 0 ≤ ∏ r ∈ Q, (1 - (r : ℝ) ^ (-x) / 2) := by
      apply Finset.prod_nonneg
      intro r hr
      have hrp := (hQ' r hr).1.1
      have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hrp.one_le
      have : (r : ℝ) ^ (-x) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hr1 (by linarith)
      linarith
    have h5 : A' - 3 / 8 * (3 * t * (A' - 3 * t * A')) ≤ (1 - t / 2) * A' := by
      have h6 : 0 ≤ t * A' := mul_nonneg ht0.le hA'0
      have h7 : 0 ≤ t * A' * (1 / 7 - t) := mul_nonneg h6 (by linarith)
      nlinarith
    have h8 : 0 ≤ 1 - t / 2 := by linarith
    calc A' - 3 / 8 * ∑' d, (if q ∣ d ∧ ¬ q ^ 2 ∣ d then Fw c L x Q d else 0)
        ≤ A' - 3 / 8 * (3 * t * (A' - 3 * t * A')) := by linarith
      _ ≤ (1 - t / 2) * A' := h5
      _ ≤ (1 - t / 2) * ((∏ r ∈ Q, (1 - (r : ℝ) ^ (-x) / 2)) * ∑' d, bw c L x d) :=
          mul_le_mul_of_nonneg_left ih' h8
      _ = (1 - t / 2) * (∏ r ∈ Q, (1 - (r : ℝ) ^ (-x) / 2)) * ∑' d, bw c L x d := by ring

lemma prod_one_sub_le (f : ℕ → ℝ) :
    ∀ Q : Finset ℕ, (∀ q ∈ Q, 0 ≤ f q ∧ f q ≤ 1) →
      (∏ q ∈ Q, (1 - f q)) * (1 + ∑ q ∈ Q, f q) ≤ 1 := by
  classical
  intro Q
  induction Q using Finset.induction_on with
  | empty => intro _; simp
  | insert q Q hqQ ih =>
    intro hf
    obtain ⟨h0, h1⟩ := hf q (Finset.mem_insert_self q Q)
    have ih' := ih (fun r hr => hf r (Finset.mem_insert_of_mem hr))
    rw [Finset.prod_insert hqQ, Finset.sum_insert hqQ]
    have hS : 0 ≤ ∑ r ∈ Q, f r :=
      Finset.sum_nonneg (fun r hr => (hf r (Finset.mem_insert_of_mem hr)).1)
    have hP : 0 ≤ ∏ r ∈ Q, (1 - f r) :=
      Finset.prod_nonneg (fun r hr => by linarith [(hf r (Finset.mem_insert_of_mem hr)).2])
    have e : (1 - f q) * (1 + (f q + ∑ r ∈ Q, f r)) ≤ 1 + ∑ r ∈ Q, f r := by
      nlinarith [mul_nonneg h0 hS, mul_nonneg h0 h0]
    calc (1 - f q) * (∏ r ∈ Q, (1 - f r)) * (1 + (f q + ∑ r ∈ Q, f r))
        = (∏ r ∈ Q, (1 - f r)) * ((1 - f q) * (1 + (f q + ∑ r ∈ Q, f r))) := by ring
      _ ≤ (∏ r ∈ Q, (1 - f r)) * (1 + ∑ r ∈ Q, f r) := mul_le_mul_of_nonneg_left e hP
      _ ≤ 1 := ih'

end weights



section assembly

/-- A Bezout inverse of `L` modulo `d`. -/
def Linv (L d : ℕ) : ℤ := Int.gcdA L d

lemma Linv_spec (L d : ℕ) (h : Nat.Coprime L d) : (d : ℤ) ∣ (L : ℤ) * Linv L d - 1 := by
  have h1 := Int.gcd_eq_gcd_ab (L : ℤ) (d : ℤ)
  have h2 : (Int.gcd (L : ℤ) (d : ℤ) : ℤ) = 1 := by
    have h3 : Int.gcd (L : ℤ) (d : ℤ) = Nat.gcd L d := Int.gcd_natCast_natCast L d
    rw [h3, h]
    rfl
  unfold Linv
  refine ⟨-Int.gcdB L d, ?_⟩
  linear_combination h2 - h1

lemma nu_one (c : ℤ) : nu c 1 = 1 := by
  unfold nu rootsMod
  simp

lemma prodK_props (c : ℤ) : ∀ K : Finset ℕ, (∀ q ∈ K, Psplit c q ∧ 7 ≤ q) →
    0 < ∏ q ∈ K, q ∧ nu c (∏ q ∈ K, q) = 3 ^ K.card
      ∧ ((∏ q ∈ K, q : ℕ) : ℝ) ≤ (Nat.totient (∏ q ∈ K, q) : ℝ) * (75 / 64 : ℝ) ^ K.card := by
  classical
  intro K
  induction K using Finset.induction_on with
  | empty =>
    intro _
    simp [nu_one]
  | insert q K hqK ih =>
    intro hK
    obtain ⟨hqs, hq7⟩ := hK q (Finset.mem_insert_self q K)
    obtain ⟨h0, h1, h2⟩ := ih (fun r hr => hK r (Finset.mem_insert_of_mem hr))
    have hqp := hqs.1
    have hcop : Nat.Coprime q (∏ r ∈ K, r) := by
      apply Nat.Coprime.prod_right
      intro r hr
      have hrp := (hK r (Finset.mem_insert_of_mem hr)).1.1
      exact (Nat.coprime_primes hqp hrp).mpr (fun h => hqK (h ▸ hr))
    rw [Finset.prod_insert hqK, Finset.card_insert_of_notMem hqK]
    refine ⟨Nat.mul_pos hqp.pos h0, ?_, ?_⟩
    · rw [nu_mul c q _ hqp.pos h0 hcop, nu_split c q hqs, h1, pow_succ]
      ring
    · rw [Nat.totient_mul hcop, Nat.totient_prime hqp]
      have hq7' : (7 : ℝ) ≤ q := by exact_mod_cast hq7
      have e : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
        rw [Nat.cast_sub hqp.one_le]
        simp
      push_cast
      rw [e, pow_succ]
      have h3 : (q : ℝ) ≤ ((q : ℝ) - 1) * (75 / 64) := by linarith
      have h4 : (0 : ℝ) ≤ ((∏ r ∈ K, r : ℕ) : ℝ) := Nat.cast_nonneg _
      have h5 : (0 : ℝ) ≤ ((q : ℝ) - 1) * (75 / 64) := by nlinarith
      have h6 := mul_le_mul h3 h2 h4 h5
      push_cast at h6
      calc (q : ℝ) * ∏ r ∈ K, (r : ℝ)
          ≤ ((q : ℝ) - 1) * (75 / 64)
            * ((Nat.totient (∏ r ∈ K, r) : ℝ) * (75 / 64 : ℝ) ^ K.card) := h6
        _ = _ := by ring

lemma exact_decomp (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (d : ℕ) :
    (∏ q ∈ exactSet Q d, q) ∣ d
      ∧ Nat.Coprime (∏ q ∈ exactSet Q d, q) (d / ∏ q ∈ exactSet Q d, q) := by
  have hmem : ∀ q ∈ exactSet Q d, q.Prime ∧ q ∣ d ∧ ¬ q ^ 2 ∣ d := by
    intro q hq
    unfold exactSet at hq
    obtain ⟨h1, h2, h3⟩ := Finset.mem_filter.mp hq
    exact ⟨hQ q h1, h2, h3⟩
  have hdvd : (∏ q ∈ exactSet Q d, q) ∣ d := by
    apply Finset.prod_primes_dvd
    · intro q hq
      exact Nat.prime_iff.mp (hmem q hq).1
    · intro q hq
      exact (hmem q hq).2.1
  refine ⟨hdvd, ?_⟩
  apply Nat.Coprime.prod_left
  intro q hq
  obtain ⟨hqp, hqd, hq2⟩ := hmem q hq
  rw [Nat.Prime.coprime_iff_not_dvd hqp]
  intro h
  apply hq2
  have hqk : q ∣ ∏ r ∈ exactSet Q d, r := Finset.dvd_prod_of_mem _ hq
  have h3 := Nat.mul_dvd_mul hqk h
  rw [Nat.mul_div_cancel' hdvd] at h3
  rwa [pow_two]

/-- Factorisation bound for the twisted exponential sum at `d = k m`. -/
lemma Sx_decomp_le (c : ℤ) (L : ℕ) (g : ℤ) (k m : ℕ) (hk : 0 < k) (hm : 0 < m)
    (hcop : Nat.Coprime k m) (hLk : Nat.Coprime L k) (hLd : Nat.Coprime L (k * m)) :
    ‖Sx c (g * Linv L (k * m)) (k * m)‖
      ≤ ‖Sx c ((((g : ZMod k) * ((L : ZMod k) * (m : ZMod k))⁻¹).val : ℕ) : ℤ) k‖ * nu c m := by
  have : NeZero k := ⟨hk.ne'⟩
  apply norm_Sx_mul_le c k m hk hm hcop
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).mp
  push_cast
  rw [ZMod.natCast_zmod_val]
  have hLu : IsUnit (L : ZMod k) := (ZMod.isUnit_iff_coprime L k).mpr hLk
  have hmu : IsUnit (m : ZMod k) := (ZMod.isUnit_iff_coprime m k).mpr hcop.symm
  have h1 : ((L : ZMod k) * (m : ZMod k))⁻¹ * ((L : ZMod k) * (m : ZMod k)) = 1 :=
    ZMod.inv_mul_of_unit _ (hLu.mul hmu)
  have h2 : (L : ZMod k) * ((Linv L (k * m) : ℤ) : ZMod k) = 1 := by
    have h3 := Linv_spec L (k * m) hLd
    have h4 : ((k : ℕ) : ℤ) ∣ (L : ℤ) * Linv L (k * m) - 1 :=
      dvd_trans (by push_cast; exact dvd_mul_right _ _) h3
    have h5 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).mpr h4
    push_cast at h5
    exact sub_eq_zero.mp h5
  have h6 : ((L : ZMod k) * (m : ZMod k))⁻¹ * (m : ZMod k)
      = ((Linv L (k * m) : ℤ) : ZMod k) := by
    calc ((L : ZMod k) * (m : ZMod k))⁻¹ * (m : ZMod k)
        = ((L : ZMod k) * (m : ZMod k))⁻¹ * (m : ZMod k)
          * ((L : ZMod k) * ((Linv L (k * m) : ℤ) : ZMod k)) := by rw [h2, mul_one]
      _ = (((L : ZMod k) * (m : ZMod k))⁻¹ * ((L : ZMod k) * (m : ZMod k)))
          * ((Linv L (k * m) : ℤ) : ZMod k) := by ring
      _ = ((Linv L (k * m) : ℤ) : ZMod k) := by rw [h1, one_mul]
  rw [mul_assoc, h6]
  ring

/-- Cauchy–Schwarz and the second moment over the invertible classes. -/
lemma unit_sum_le (c : ℤ) (k : ℕ) [NeZero k] (n : ℕ) (hν : nu c k = 3 ^ n)
    (hφ : (k : ℝ) ≤ (Nat.totient k : ℝ) * (75 / 64 : ℝ) ^ n) (G₀ L₀ : ZMod k)
    (hG : IsUnit G₀) (hL : IsUnit L₀) :
    ∑ β ∈ Finset.univ.filter (fun β : ZMod k => IsUnit β),
        ‖Sx c (((G₀ * (L₀ * β)⁻¹).val : ℕ) : ℤ) k‖
      ≤ (Nat.totient k : ℝ) * (5 / 8 : ℝ) ^ n * 3 ^ n := by
  classical
  have hk : 0 < k := NeZero.pos k
  obtain ⟨U, hU⟩ : ∃ U : Finset (ZMod k), U = Finset.univ.filter (fun β : ZMod k => IsUnit β) :=
    ⟨_, rfl⟩
  rw [← hU]
  have hUmem : ∀ β ∈ U, IsUnit β := by
    intro β hβ
    rw [hU] at hβ
    exact (Finset.mem_filter.mp hβ).2
  have hcard : (U.card : ℝ) ≤ Nat.totient k := by
    have h1 : U = Finset.univ.filter (fun β : ZMod k => Nat.Coprime β.val k) := by
      rw [hU]
      apply Finset.filter_congr
      intro β _
      rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
    have h2 : U.card = Nat.totient k := by
      rw [h1, ← Fintype.card_subtype, ← ZMod.card_units_eq_totient k]
      exact Fintype.card_congr ZMod.unitsEquivCoprime.symm
    rw [h2]
  have hcs := sq_sum_le_card_mul_sum_sq (s := U)
    (f := fun β : ZMod k => ‖Sx c (((G₀ * (L₀ * β)⁻¹).val : ℕ) : ℤ) k‖)
  have hinj : Set.InjOn (fun β : ZMod k => G₀ * (L₀ * β)⁻¹) (U : Set (ZMod k)) := by
    intro β hβ β' hβ' h
    have hb := hUmem β hβ
    have hb' := hUmem β' hβ'
    have hu := hL.mul hb
    have hu' := hL.mul hb'
    have h1 : (L₀ * β)⁻¹ = (L₀ * β')⁻¹ := by
      have h2 : G₀⁻¹ * (G₀ * (L₀ * β)⁻¹) = G₀⁻¹ * (G₀ * (L₀ * β')⁻¹) := congrArg _ h
      rw [← mul_assoc, ← mul_assoc, ZMod.inv_mul_of_unit G₀ hG, one_mul, one_mul] at h2
      exact h2
    have h3 : L₀ * β = L₀ * β' := by
      calc L₀ * β = L₀ * β * ((L₀ * β')⁻¹ * (L₀ * β')) := by
            rw [ZMod.inv_mul_of_unit _ hu', mul_one]
        _ = (L₀ * β * (L₀ * β)⁻¹) * (L₀ * β') := by rw [← h1]; ring
        _ = L₀ * β' := by rw [ZMod.mul_inv_of_unit _ hu, one_mul]
    have h4 : L₀⁻¹ * (L₀ * β) = L₀⁻¹ * (L₀ * β') := congrArg _ h3
    rw [← mul_assoc, ← mul_assoc, ZMod.inv_mul_of_unit L₀ hL, one_mul, one_mul] at h4
    exact h4
  have hsq : ∑ β ∈ U, ‖Sx c (((G₀ * (L₀ * β)⁻¹).val : ℕ) : ℤ) k‖ ^ 2 ≤ (k : ℝ) * nu c k := by
    have h1 : ∑ β ∈ U, ‖Sx c (((G₀ * (L₀ * β)⁻¹).val : ℕ) : ℤ) k‖ ^ 2
        = ∑ γ ∈ U.image (fun β : ZMod k => G₀ * (L₀ * β)⁻¹),
            ‖Sx c ((γ.val : ℕ) : ℤ) k‖ ^ 2 :=
      (Finset.sum_image (f := fun γ : ZMod k => ‖Sx c ((γ.val : ℕ) : ℤ) k‖ ^ 2) hinj).symm
    have h2 : ∑ γ ∈ U.image (fun β : ZMod k => G₀ * (L₀ * β)⁻¹),
          ‖Sx c ((γ.val : ℕ) : ℤ) k‖ ^ 2
        ≤ ∑ γ : ZMod k, ‖Sx c ((γ.val : ℕ) : ℤ) k‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun γ _ _ => sq_nonneg _)
    have h3 : ∑ γ : ZMod k, ‖Sx c ((γ.val : ℕ) : ℤ) k‖ ^ 2
        = ∑ b ∈ Finset.range k, ‖Sx c (b : ℤ) k‖ ^ 2 := by
      apply Finset.sum_bij (fun (γ : ZMod k) _ => γ.val)
      · intro γ _
        exact Finset.mem_range.mpr (ZMod.val_lt γ)
      · intro γ _ γ' _ h
        exact ZMod.val_injective k h
      · intro b hb
        exact ⟨(b : ZMod k), Finset.mem_univ _, ZMod.val_cast_of_lt (Finset.mem_range.mp hb)⟩
      · intro γ _
        rfl
    rw [h1]
    refine h2.trans ?_
    rw [h3]
    have h4 := second_moment c k hk
    exact h4.le
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = ∑ β ∈ U, ‖Sx c (((G₀ * (L₀ * β)⁻¹).val : ℕ) : ℤ) k‖ := ⟨_, rfl⟩
  rw [← hT] at hcs ⊢
  have hT0 : 0 ≤ T := by
    rw [hT]
    exact Finset.sum_nonneg (fun β _ => norm_nonneg _)
  have hφ0 : (0 : ℝ) ≤ Nat.totient k := Nat.cast_nonneg _
  have hkey : T ^ 2 ≤ ((Nat.totient k : ℝ) * (5 / 8 : ℝ) ^ n * 3 ^ n) ^ 2 := by
    have h5 : T ^ 2 ≤ (Nat.totient k : ℝ) * ((k : ℝ) * nu c k) :=
      hcs.trans (mul_le_mul hcard hsq (Finset.sum_nonneg (fun β _ => sq_nonneg _)) hφ0)
    rw [hν] at h5
    push_cast at h5
    have h6 : (Nat.totient k : ℝ) * ((k : ℝ) * 3 ^ n)
        ≤ (Nat.totient k : ℝ) * (((Nat.totient k : ℝ) * (75 / 64 : ℝ) ^ n) * 3 ^ n) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hφ (by positivity)) hφ0
    have e : (Nat.totient k : ℝ) * (((Nat.totient k : ℝ) * (75 / 64 : ℝ) ^ n) * 3 ^ n)
        = ((Nat.totient k : ℝ) * (5 / 8 : ℝ) ^ n * 3 ^ n) ^ 2 := by
      have e1 : (75 / 64 : ℝ) ^ n = ((5 / 8 : ℝ) ^ n) ^ 2 * 3 ^ n := by
        rw [← pow_mul, mul_comm n 2, pow_mul, ← mul_pow]
        norm_num
      rw [e1]
      ring
    linarith
  exact (pow_le_pow_iff_left₀ hT0 (by positivity) two_ne_zero).mp hkey

end assembly

section assembly2

open Classical in
/-- The weight on the cofactor `m` for a given exact set `K`. -/
noncomputable def aK (c : ℤ) (L : ℕ) (Q K : Finset ℕ) (m : ℕ) : ℝ :=
  if Nat.Coprime ((∏ q ∈ K, q) * m) L ∧ exactSet Q ((∏ q ∈ K, q) * m) = K
  then (nu c m : ℝ) else 0

lemma aK_nonneg (c : ℤ) (L : ℕ) (Q K : Finset ℕ) (m : ℕ) : 0 ≤ aK c L Q K m := by
  unfold aK
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_rfl

lemma aK_le (c : ℤ) (L : ℕ) (Q K : Finset ℕ) (m : ℕ) : aK c L Q K m ≤ nu c m := by
  unfold aK
  split_ifs
  · exact le_rfl
  · exact Nat.cast_nonneg _

lemma aK_inv (c : ℤ) (L : ℕ) (Q K : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (p : ℕ) (hp : p.Prime)
    (hp3 : p % 3 = 2) (hp3c : ¬ (p : ℤ) ∣ 3 * c) (hpL : ¬ p ∣ L) (hpQ : p ∉ Q) (m : ℕ) :
    aK c L Q K (p * m) = aK c L Q K m := by
  unfold aK
  have e : (∏ q ∈ K, q) * (p * m) = p * ((∏ q ∈ K, q) * m) := by ring
  have hcopp : Nat.Coprime p L := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpL
  have h1 : Nat.Coprime (p * ((∏ q ∈ K, q) * m)) L ↔ Nat.Coprime ((∏ q ∈ K, q) * m) L := by
    rw [Nat.coprime_mul_iff_left]
    exact ⟨fun h => h.2, fun h => ⟨hcopp, h⟩⟩
  rw [e, exactSet_mul Q hQ p hp hpQ]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [nu_zero]
  · rw [nu_two_mul c p m hp hp3 hp3c hm]
    by_cases hc : Nat.Coprime ((∏ q ∈ K, q) * m) L ∧ exactSet Q ((∏ q ∈ K, q) * m) = K
    · rw [if_pos hc, if_pos ⟨h1.mpr hc.1, hc.2⟩]
    · rw [if_neg hc, if_neg (fun h => hc ⟨h1.mp h.1, h.2⟩)]

lemma aK_supp (c : ℤ) (L : ℕ) (Q K : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (hK : 0 < ∏ q ∈ K, q)
    (m : ℕ) (h : aK c L Q K m ≠ 0) : Nat.Coprime (∏ q ∈ K, q) m := by
  unfold aK at h
  by_cases hc : Nat.Coprime ((∏ q ∈ K, q) * m) L ∧ exactSet Q ((∏ q ∈ K, q) * m) = K
  · have h1 := (exact_decomp Q hQ ((∏ q ∈ K, q) * m)).2
    rw [hc.2, Nat.mul_div_cancel_left m hK] at h1
    exact h1
  · rw [if_neg hc] at h
    exact absurd rfl h

/-- Contribution of the moduli with a given exact set `K`. -/
lemma K_bound (c : ℤ) (L : ℕ) (g : ℤ) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, Psplit c q ∧ ¬ q ∣ L ∧ 7 ≤ q ∧ ¬ (q : ℤ) ∣ g) (K : Finset ℕ) (hKQ : K ⊆ Q)
    (x : ℝ) (hs : Summable (fun d : ℕ => (nu c d : ℝ) * (d : ℝ) ^ (-x)))
    (hV : ∀ β : ZMod (∏ q ∈ K, q), IsUnit β →
      ∑' m : ℕ, (if (m : ZMod (∏ q ∈ K, q)) = β then aK c L Q K m * (m : ℝ) ^ (-x) else 0)
        ≤ 2 / (Nat.totient (∏ q ∈ K, q)) * ∑' m : ℕ, aK c L Q K m * (m : ℝ) ^ (-x))
    (Y : ℕ) :
    ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L ∧ exactSet Q d = K),
        ‖Sx c (g * Linv L d) d‖ * (d : ℝ) ^ (-x)
      ≤ 2 * ∑' d : ℕ, (if exactSet Q d = K then Fw c L x Q d else 0) := by
  classical
  have hQp : ∀ q ∈ Q, q.Prime := fun q hq => (hQ q hq).1.1
  obtain ⟨hk0', hνk', hφk'⟩ := prodK_props c K
    (fun q hq => ⟨(hQ q (hKQ hq)).1, (hQ q (hKQ hq)).2.2.1⟩)
  have haKsupp := aK_supp c L Q K hQp hk0'
  have haKdef : ∀ m, aK c L Q K m = if Nat.Coprime ((∏ q ∈ K, q) * m) L
      ∧ exactSet Q ((∏ q ∈ K, q) * m) = K then (nu c m : ℝ) else 0 := fun _ => rfl
  have hLk' : Nat.Coprime L (∏ q ∈ K, q) := by
    apply Nat.Coprime.prod_right
    intro q hq
    exact ((Nat.Prime.coprime_iff_not_dvd (hQp q (hKQ hq))).mpr (hQ q (hKQ hq)).2.1).symm
  have hgk' : IsCoprime g ((∏ q ∈ K, q : ℕ) : ℤ) := by
    push_cast
    apply IsCoprime.prod_right
    intro q hq
    have hqp := Nat.prime_iff_prime_int.mp (hQp q (hKQ hq))
    exact ((Prime.coprime_iff_not_dvd hqp).mpr (hQ q (hKQ hq)).2.2.2).symm
  have hdec : ∀ d, exactSet Q d = K → (∏ q ∈ K, q) ∣ d
      ∧ Nat.Coprime (∏ q ∈ K, q) (d / ∏ q ∈ K, q) := by
    intro d hd
    have := exact_decomp Q hQp d
    rwa [hd] at this
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = K.card := ⟨_, rfl⟩
  rw [← hn] at hνk' hφk'
  obtain ⟨k, hkdef⟩ : ∃ k : ℕ, k = ∏ q ∈ K, q := ⟨_, rfl⟩
  rw [← hkdef] at hV hk0' hνk' hφk' haKsupp haKdef hLk' hgk' hdec
  have : NeZero k := ⟨hk0'.ne'⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0'
  have hLu : IsUnit (L : ZMod k) := (ZMod.isUnit_iff_coprime L k).mpr hLk'
  have hGu : IsUnit ((g : ℤ) : ZMod k) := by
    obtain ⟨u, v, huv⟩ := hgk'
    have h1 := congrArg (Int.cast : ℤ → ZMod k) huv
    push_cast at h1
    rw [ZMod.natCast_self, mul_zero, add_zero] at h1
    exact IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact h1)
  obtain ⟨fΓ, hfΓ⟩ : ∃ fΓ : ZMod k → ℝ, fΓ = fun β =>
      ‖Sx c ((((g : ZMod k) * ((L : ZMod k) * β)⁻¹).val : ℕ) : ℤ) k‖ := ⟨_, rfl⟩
  have hfΓa : ∀ β, fΓ β = ‖Sx c ((((g : ZMod k) * ((L : ZMod k) * β)⁻¹).val : ℕ) : ℤ) k‖ :=
    fun _ => by rw [hfΓ]
  have hfΓ0 : ∀ β, 0 ≤ fΓ β := fun β => by rw [hfΓa]; exact norm_nonneg _
  have hfΓle : ∀ β, fΓ β ≤ nu c k := fun β => by rw [hfΓa]; exact norm_Sx_le c _ k
  have hrp0 : ∀ m : ℕ, 0 ≤ (m : ℝ) ^ (-x) := fun m => Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hsa : Summable (fun m : ℕ => aK c L Q K m * (m : ℝ) ^ (-x)) :=
    Summable.of_nonneg_of_le (fun m => mul_nonneg (aK_nonneg c L Q K m) (hrp0 m))
      (fun m => mul_le_mul_of_nonneg_right (aK_le c L Q K m) (hrp0 m)) hs
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ∑' m : ℕ, aK c L Q K m * (m : ℝ) ^ (-x) := ⟨_, rfl⟩
  rw [← hD] at hV
  have hD0 : 0 ≤ D := by
    rw [hD]
    exact tsum_nonneg (fun m => mul_nonneg (aK_nonneg c L Q K m) (hrp0 m))
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ, G = fun m : ℕ =>
      (k : ℝ) ^ (-x) * (fΓ (m : ZMod k) * (aK c L Q K m * (m : ℝ) ^ (-x))) := ⟨_, rfl⟩
  have hGa : ∀ m, G m = (k : ℝ) ^ (-x) * (fΓ (m : ZMod k) * (aK c L Q K m * (m : ℝ) ^ (-x))) :=
    fun _ => by rw [hG]
  have hkx0 : 0 ≤ (k : ℝ) ^ (-x) := Real.rpow_nonneg hkR.le _
  have hG0 : ∀ m, 0 ≤ G m := by
    intro m
    rw [hGa]
    exact mul_nonneg hkx0 (mul_nonneg (hfΓ0 _) (mul_nonneg (aK_nonneg c L Q K m) (hrp0 m)))
  have hGs : Summable G := by
    refine Summable.of_nonneg_of_le hG0 (fun m => ?_)
      ((hsa.mul_left (nu c k : ℝ)).mul_left ((k : ℝ) ^ (-x)))
    rw [hGa]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hfΓle _)
      (mul_nonneg (aK_nonneg c L Q K m) (hrp0 m))) hkx0
  -- step 1: the finite sum is at most the series of `G`
  have hstep1 : ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L ∧ exactSet Q d = K),
        ‖Sx c (g * Linv L d) d‖ * (d : ℝ) ^ (-x) ≤ ∑' m, G m := by
    have hterm : ∀ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L ∧ exactSet Q d = K),
        ‖Sx c (g * Linv L d) d‖ * (d : ℝ) ^ (-x) ≤ G (d / k) := by
      intro d hd
      obtain ⟨hd1, hdL, hdK⟩ := Finset.mem_filter.mp hd
      have hd1' := (Finset.mem_Icc.mp hd1).1
      obtain ⟨hkd, hcop⟩ := hdec d hdK
      obtain ⟨m, hm⟩ := hkd
      have hm0 : 0 < m := by
        rcases Nat.eq_zero_or_pos m with rfl | h
        · rw [mul_zero] at hm
          omega
        · exact h
      have hdiv : d / k = m := by rw [hm]; exact Nat.mul_div_cancel_left m hk0'
      rw [hdiv] at hcop ⊢
      have hS := Sx_decomp_le c L g k m hk0' hm0 hcop hLk' (by rw [← hm]; exact hdL.symm)
      rw [← hm] at hS
      have haK : aK c L Q K m = nu c m := by
        rw [haKdef, ← hm, if_pos ⟨hdL, hdK⟩]
      have hdx : (d : ℝ) ^ (-x) = (k : ℝ) ^ (-x) * (m : ℝ) ^ (-x) := by
        rw [hm]
        push_cast
        exact Real.mul_rpow (Nat.cast_nonneg k) (Nat.cast_nonneg m)
      rw [hGa, hfΓa, haK, hdx]
      calc ‖Sx c (g * Linv L d) d‖ * ((k : ℝ) ^ (-x) * (m : ℝ) ^ (-x))
          ≤ (‖Sx c ((((g : ZMod k) * ((L : ZMod k) * (m : ZMod k))⁻¹).val : ℕ) : ℤ) k‖
              * nu c m) * ((k : ℝ) ^ (-x) * (m : ℝ) ^ (-x)) :=
            mul_le_mul_of_nonneg_right hS (mul_nonneg hkx0 (hrp0 m))
        _ = _ := by ring
    have hinjF : Set.InjOn (fun d : ℕ => d / k)
        ((Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L ∧ exactSet Q d = K) : Set ℕ) := by
      intro d hd d' hd' h
      have h1 := (hdec d (Finset.mem_filter.mp hd).2.2).1
      have h2 := (hdec d' (Finset.mem_filter.mp hd').2.2).1
      have h3 : d / k = d' / k := h
      rw [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2, h3]
    calc ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L ∧ exactSet Q d = K),
          ‖Sx c (g * Linv L d) d‖ * (d : ℝ) ^ (-x)
        ≤ ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L ∧ exactSet Q d = K),
            G (d / k) := Finset.sum_le_sum hterm
      _ = ∑ m ∈ ((Finset.Icc 1 Y).filter
            (fun d => Nat.Coprime d L ∧ exactSet Q d = K)).image (fun d : ℕ => d / k), G m :=
          (Finset.sum_image (f := G) hinjF).symm
      _ ≤ ∑' m, G m := hGs.sum_le_tsum _ (fun m _ => hG0 m)
  -- step 2: split the series of `G` according to the class of `m`
  have hVs : ∀ β : ZMod k,
      Summable (fun m : ℕ => if (m : ZMod k) = β then aK c L Q K m * (m : ℝ) ^ (-x) else 0) := by
    intro β
    refine Summable.of_nonneg_of_le (fun m => ?_) (fun m => ?_) hsa
    · split_ifs
      · exact mul_nonneg (aK_nonneg c L Q K m) (hrp0 m)
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact mul_nonneg (aK_nonneg c L Q K m) (hrp0 m)
  have hstep2 : ∑' m, G m = (k : ℝ) ^ (-x) * ∑ β : ZMod k, fΓ β
      * ∑' m : ℕ, (if (m : ZMod k) = β then aK c L Q K m * (m : ℝ) ^ (-x) else 0) := by
    have e1 : ∀ m : ℕ, G m = (k : ℝ) ^ (-x) * ∑ β : ZMod k, fΓ β
        * (if (m : ZMod k) = β then aK c L Q K m * (m : ℝ) ^ (-x) else 0) := by
      intro m
      rw [hGa, Finset.sum_eq_single (m : ZMod k)]
      · rw [if_pos rfl]
      · intro β _ hβ
        rw [if_neg (fun h => hβ h.symm), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    rw [tsum_congr e1, tsum_mul_left]
    congr 1
    rw [Summable.tsum_finsetSum]
    · apply Finset.sum_congr rfl
      intro β _
      rw [tsum_mul_left]
    · intro β _
      exact (hVs β).mul_left _
  -- step 3: equidistribution and Cauchy–Schwarz
  have hφpos : (0 : ℝ) < Nat.totient k := by exact_mod_cast Nat.totient_pos.mpr hk0'
  have hstep3 : ∑ β : ZMod k, fΓ β
      * ∑' m : ℕ, (if (m : ZMod k) = β then aK c L Q K m * (m : ℝ) ^ (-x) else 0)
      ≤ 2 * ((5 / 8 : ℝ) ^ n * 3 ^ n) * D := by
    have hzero : ∀ β : ZMod k, ¬ IsUnit β →
        ∑' m : ℕ, (if (m : ZMod k) = β then aK c L Q K m * (m : ℝ) ^ (-x) else 0) = 0 := by
      intro β hβ
      have : ∀ m : ℕ, (if (m : ZMod k) = β then aK c L Q K m * (m : ℝ) ^ (-x) else 0) = 0 := by
        intro m
        split_ifs with hm
        · by_cases ha : aK c L Q K m = 0
          · rw [ha, zero_mul]
          · exfalso
            apply hβ
            rw [← hm]
            exact (ZMod.isUnit_iff_coprime m k).mpr (haKsupp m ha).symm
        · rfl
      rw [tsum_congr this, tsum_zero]
    have h1 : ∑ β : ZMod k, fΓ β
          * ∑' m : ℕ, (if (m : ZMod k) = β then aK c L Q K m * (m : ℝ) ^ (-x) else 0)
        ≤ ∑ β : ZMod k, (if IsUnit β then fΓ β else 0) * (2 / (Nat.totient k) * D) := by
      apply Finset.sum_le_sum
      intro β _
      by_cases hβ : IsUnit β
      · rw [if_pos hβ]
        exact mul_le_mul_of_nonneg_left (hV β hβ) (hfΓ0 β)
      · rw [if_neg hβ, hzero β hβ, mul_zero, zero_mul]
    have h2 : ∑ β : ZMod k, (if IsUnit β then fΓ β else 0)
        ≤ (Nat.totient k : ℝ) * (5 / 8 : ℝ) ^ n * 3 ^ n := by
      rw [← Finset.sum_filter]
      have := unit_sum_le c k n hνk' hφk' ((g : ℤ) : ZMod k) (L : ZMod k) hGu hLu
      simp only [hfΓa]
      exact this
    refine h1.trans ?_
    rw [← Finset.sum_mul]
    have h3 : 0 ≤ 2 / (Nat.totient k : ℝ) * D := by positivity
    calc (∑ β : ZMod k, (if IsUnit β then fΓ β else 0)) * (2 / (Nat.totient k) * D)
        ≤ ((Nat.totient k : ℝ) * (5 / 8 : ℝ) ^ n * 3 ^ n) * (2 / (Nat.totient k) * D) :=
          mul_le_mul_of_nonneg_right h2 h3
      _ = 2 * ((5 / 8 : ℝ) ^ n * 3 ^ n) * D := by
          field_simp
  -- step 4: back to the moduli `d = k m`
  obtain ⟨H, hH⟩ : ∃ H : ℕ → ℝ, H = fun d => if exactSet Q d = K then Fw c L x Q d else 0 :=
    ⟨_, rfl⟩
  have hHa : ∀ d, H d = if exactSet Q d = K then Fw c L x Q d else 0 := fun _ => by rw [hH]
  have hH0 : ∀ d, 0 ≤ H d := by
    intro d
    rw [hHa]
    split_ifs
    · exact Fw_nonneg c L x Q d
    · exact le_rfl
  have hHs : Summable H := by
    refine Summable.of_nonneg_of_le hH0 (fun d => ?_) (summable_Fw c L x Q hs)
    rw [hHa]
    split_ifs
    · exact le_rfl
    · exact Fw_nonneg c L x Q d
  have hstep4 : (k : ℝ) ^ (-x) * ((5 / 8 : ℝ) ^ n * 3 ^ n * D) ≤ ∑' d, H d := by
    have e2 : ∀ m : ℕ, (k : ℝ) ^ (-x) * ((5 / 8 : ℝ) ^ n * 3 ^ n * (aK c L Q K m * (m : ℝ) ^ (-x)))
        = H (k * m) := by
      intro m
      rw [hHa, haKdef]
      by_cases hc : Nat.Coprime (k * m) L ∧ exactSet Q (k * m) = K
      · rw [if_pos hc, if_pos hc.2]
        unfold Fw bw
        rw [hc.2, if_pos hc.1, ← hn]
        have hkm : (((k * m : ℕ) : ℝ)) ^ (-x) = (k : ℝ) ^ (-x) * (m : ℝ) ^ (-x) := by
          push_cast
          exact Real.mul_rpow (Nat.cast_nonneg k) (Nat.cast_nonneg m)
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp [nu_zero]
        · have hcop : Nat.Coprime k m := by
            have := (hdec (k * m) hc.2).2
            rwa [Nat.mul_div_cancel_left m hk0'] at this
          rw [nu_mul c k m hk0' hm hcop, hνk', hkm]
          push_cast
          ring
      · rw [if_neg hc, zero_mul, mul_zero, mul_zero]
        by_cases he : exactSet Q (k * m) = K
        · rw [if_pos he]
          unfold Fw bw
          rw [if_neg (fun h => hc ⟨h, he⟩), mul_zero]
        · rw [if_neg he]
    have hinj : Function.Injective (fun m : ℕ => k * m) :=
      fun a b hab => Nat.eq_of_mul_eq_mul_left hk0' hab
    calc (k : ℝ) ^ (-x) * ((5 / 8 : ℝ) ^ n * 3 ^ n * D)
        = ∑' m : ℕ, (k : ℝ) ^ (-x)
            * ((5 / 8 : ℝ) ^ n * 3 ^ n * (aK c L Q K m * (m : ℝ) ^ (-x))) := by
          rw [tsum_mul_left, tsum_mul_left, hD]
      _ = ∑' m : ℕ, H (k * m) := tsum_congr e2
      _ ≤ ∑' d, H d := tsum_comp_le_tsum_of_inj hHs hH0 hinj
  calc ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L ∧ exactSet Q d = K),
        ‖Sx c (g * Linv L d) d‖ * (d : ℝ) ^ (-x)
      ≤ ∑' m, G m := hstep1
    _ = (k : ℝ) ^ (-x) * ∑ β : ZMod k, fΓ β
          * ∑' m : ℕ, (if (m : ZMod k) = β then aK c L Q K m * (m : ℝ) ^ (-x) else 0) := hstep2
    _ ≤ (k : ℝ) ^ (-x) * (2 * ((5 / 8 : ℝ) ^ n * 3 ^ n) * D) :=
        mul_le_mul_of_nonneg_left hstep3 hkx0
    _ = 2 * ((k : ℝ) ^ (-x) * ((5 / 8 : ℝ) ^ n * 3 ^ n * D)) := by ring
    _ ≤ 2 * ∑' d, H d := by linarith
    _ = 2 * ∑' d : ℕ, (if exactSet Q d = K then Fw c L x Q d else 0) := by
        rw [tsum_congr hHa]

end assembly2

section coreThm

lemma exists_finset_sum_ge (Pr : ℕ → Prop) [DecidablePred Pr]
    (hns : ¬ Summable (fun p : ℕ => if Pr p then (1 : ℝ) / p else 0)) (E : Finset ℕ) (M : ℝ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Pr p ∧ p ∉ E) ∧ M ≤ ∑ p ∈ P, (1 : ℝ) / p := by
  classical
  obtain ⟨g, hg⟩ : ∃ g : ℕ → ℝ, g = fun p : ℕ => if Pr p then (1 : ℝ) / p else 0 := ⟨_, rfl⟩
  rw [← hg] at hns
  have hg0 : ∀ p, 0 ≤ g p := by
    intro p
    rw [hg]
    dsimp only
    split_ifs
    · positivity
    · exact le_rfl
  obtain ⟨g', hg'⟩ : ∃ g' : ℕ → ℝ, g' = fun p : ℕ => if p ∈ E then 0 else g p := ⟨_, rfl⟩
  have hg'0 : ∀ p, 0 ≤ g' p := by
    intro p
    rw [hg']
    dsimp only
    split_ifs
    · exact le_rfl
    · exact hg0 p
  have hns' : ¬ Summable g' := by
    intro h
    apply hns
    have hfin : Summable (fun p => if p ∈ E then g p else 0) :=
      summable_of_ne_finset_zero (s := E) (fun p hp => if_neg hp)
    refine (h.add hfin).congr (fun p => ?_)
    rw [hg']
    dsimp only
    split_ifs <;> simp
  have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg hg'0).mp hns'
  obtain ⟨n, hn⟩ := (htend.eventually (Filter.eventually_ge_atTop M)).exists
  refine ⟨(Finset.range n).filter (fun p => Pr p ∧ p ∉ E), ?_, ?_⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · refine hn.trans (le_of_eq ?_)
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    rw [hg', hg]
    dsimp only
    by_cases hE : p ∈ E
    · rw [if_pos hE, if_neg (fun h => h.2 hE)]
    · rw [if_neg hE]
      by_cases hc : Pr p
      · rw [if_pos hc, if_pos ⟨hc, hE⟩]
      · rw [if_neg hc, if_neg (fun h => hc h.1)]

lemma equidist' (k : ℕ) (hk : 0 < k) (hk3 : Nat.Coprime 3 k) (E : Finset ℕ) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ (P : Finset ℕ) (η : ℝ), 0 < η ∧ (∀ p ∈ P, p.Prime ∧ p % 3 = 2 ∧ p ∉ E) ∧
      ∀ x : ℝ, 1 < x → x < 1 + η → ∀ a : ℕ → ℝ, (∀ m, 0 ≤ a m) →
        Summable (fun m : ℕ => a m * (m : ℝ) ^ (-x)) → (∀ p ∈ P, ∀ m, a (p * m) = a m) →
        ∀ β : ZMod k, IsUnit β →
          ∑' m : ℕ, (if (m : ZMod k) = β then a m * (m : ℝ) ^ (-x) else 0)
            ≤ (1 + ε) / k.totient * ∑' m : ℕ, a m * (m : ℝ) ^ (-x) := by
  have : NeZero k := ⟨hk.ne'⟩
  exact equidist k hk3 E ε hε

open Classical in
/-- **Core estimate** (logarithmic Hooley bound): the twisted exponential sums over the cube
roots of `c` are `o(1/(x-1))` in Dirichlet-series average. -/
theorem core_bound (c : ℤ) (hc0 : c ≠ 0) (C : ℝ)
    (hC : ∀ y : ℕ, ((Spairs c y).card : ℝ) ≤ C * y)
    (hsplit : ¬ Summable (fun p : ℕ => if Psplit c p then (1 : ℝ) / p else 0))
    (L : ℕ) (hL : 0 < L) (g : ℤ) (hg : g ≠ 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : ℝ, 1 < x → x < 1 + η → ∀ Y : ℕ,
      ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L),
        ‖Sx c (g * Linv L d) d‖ * (d : ℝ) ^ (-x) ≤ ε / (x - 1) := by
  have hC1 : 1 ≤ C := by
    have h1 := hC 1
    rw [card_Spairs_eq] at h1
    simp [nu_one] at h1
    exact h1
  have hCpos : 0 < C := by linarith
  -- the split primes
  obtain ⟨Q, hQ1, hQ2⟩ := exists_finset_sum_ge (Psplit c) hsplit
    (Finset.range (max 7 (max (L + 1) (g.natAbs + 1)))) (16 * C / ε)
  have hQ : ∀ q ∈ Q, Psplit c q ∧ ¬ q ∣ L ∧ 7 ≤ q ∧ ¬ (q : ℤ) ∣ g := by
    intro q hq
    obtain ⟨h1, h2⟩ := hQ1 q hq
    rw [Finset.mem_range, not_lt] at h2
    have h7 : 7 ≤ q := (le_max_left _ _).trans h2
    have hL' : L + 1 ≤ q := ((le_max_left _ _).trans (le_max_right _ _)).trans h2
    have hg' : g.natAbs + 1 ≤ q := ((le_max_right _ _).trans (le_max_right _ _)).trans h2
    refine ⟨h1, ?_, h7, ?_⟩
    · intro h
      have := Nat.le_of_dvd hL h
      omega
    · intro h
      have h3 : q ∣ g.natAbs := Int.natCast_dvd.mp h
      have := Nat.le_of_dvd (Int.natAbs_pos.mpr hg) h3
      omega
  have hQp : ∀ q ∈ Q, q.Prime := fun q hq => (hQ q hq).1.1
  -- the equidistribution data for each `K ⊆ Q`
  obtain ⟨E, hE⟩ : ∃ E : Finset ℕ, E = Finset.range (3 * c.natAbs * L + 1) := ⟨_, rfl⟩
  have hEprop : ∀ p : ℕ, p ∉ E → ¬ (p : ℤ) ∣ 3 * c ∧ ¬ p ∣ L := by
    intro p hp
    rw [hE, Finset.mem_range, not_lt] at hp
    have hcpos : 0 < c.natAbs := Int.natAbs_pos.mpr hc0
    constructor
    · intro h
      have h3 : p ∣ (3 * c).natAbs := Int.natCast_dvd.mp h
      rw [Int.natAbs_mul] at h3
      have h4 : (3 : ℤ).natAbs = 3 := rfl
      rw [h4] at h3
      have h5 := Nat.le_of_dvd (by omega) h3
      have h6 : 3 * c.natAbs ≤ 3 * c.natAbs * L := Nat.le_mul_of_pos_right _ hL
      omega
    · intro h
      have h5 := Nat.le_of_dvd hL h
      have h6 : L ≤ 3 * c.natAbs * L := by
        calc L = 1 * L := (one_mul L).symm
          _ ≤ 3 * c.natAbs * L := Nat.mul_le_mul_right L (by omega)
      omega
  have hKdata : ∀ K : Finset ℕ, ∃ (P : Finset ℕ) (η : ℝ), 0 < η ∧ (K ⊆ Q →
      (∀ p ∈ P, p.Prime ∧ p % 3 = 2 ∧ p ∉ E) ∧
      ∀ x : ℝ, 1 < x → x < 1 + η → ∀ a : ℕ → ℝ, (∀ m, 0 ≤ a m) →
        Summable (fun m : ℕ => a m * (m : ℝ) ^ (-x)) → (∀ p ∈ P, ∀ m, a (p * m) = a m) →
        ∀ β : ZMod (∏ q ∈ K, q), IsUnit β →
          ∑' m : ℕ, (if (m : ZMod (∏ q ∈ K, q)) = β then a m * (m : ℝ) ^ (-x) else 0)
            ≤ (1 + 1) / (∏ q ∈ K, q).totient * ∑' m : ℕ, a m * (m : ℝ) ^ (-x)) := by
    intro K
    by_cases hKQ : K ⊆ Q
    · have hk0 : 0 < ∏ q ∈ K, q := Finset.prod_pos (fun q hq => (hQp q (hKQ hq)).pos)
      have hk3 : Nat.Coprime 3 (∏ q ∈ K, q) := by
        apply Nat.Coprime.prod_right
        intro q hq
        have hq1 := (hQ q (hKQ hq)).1
        rw [Nat.coprime_primes Nat.prime_three hq1.1]
        intro h
        have := hq1.2.1
        omega
      obtain ⟨P, η, hη, hP, hmain⟩ := equidist' (∏ q ∈ K, q) hk0 hk3 E 1 one_pos
      exact ⟨P, η, hη, fun _ => ⟨hP, hmain⟩⟩
    · exact ⟨∅, 1, one_pos, fun h => absurd h hKQ⟩
  choose Pf ηf hηf hPf using hKdata
  obtain ⟨ηQ, hηQ, hηQb⟩ := rpow_neg_ge Q
  have hne : (Q.powerset).Nonempty := ⟨∅, Finset.empty_mem_powerset Q⟩
  obtain ⟨η₁, hη₁def⟩ : ∃ η₁ : ℝ, η₁ = (Q.powerset).inf' hne ηf := ⟨_, rfl⟩
  have hη₁pos : 0 < η₁ := by
    rw [hη₁def, Finset.lt_inf'_iff]
    intro K _
    exact hηf K
  have hη₁le : ∀ K ∈ Q.powerset, η₁ ≤ ηf K := by
    intro K hK
    rw [hη₁def]
    exact Finset.inf'_le _ hK
  refine ⟨min (min 1 ηQ) η₁, lt_min (lt_min one_pos hηQ) hη₁pos, ?_⟩
  intro x hx1 hx2 Y
  have hxa : x < 1 + 1 := lt_of_lt_of_le hx2 (by linarith [min_le_left (min 1 ηQ) η₁, min_le_left 1 ηQ])
  have hxb : x < 1 + ηQ := lt_of_lt_of_le hx2 (by linarith [min_le_left (min 1 ηQ) η₁, min_le_right 1 ηQ])
  have hxc : x < 1 + η₁ := lt_of_lt_of_le hx2 (by linarith [min_le_right (min 1 ηQ) η₁])
  have hxpos : 0 < x - 1 := by linarith
  obtain ⟨hs, hsbound⟩ := nu_series c C hC x hx1 (by linarith)
  -- split according to the exact set
  have hmaps : ∀ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L),
      exactSet Q d ∈ Q.powerset := by
    intro d _
    rw [Finset.mem_powerset]
    exact Finset.filter_subset _ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hKb : ∀ K ∈ Q.powerset,
      ∑ d ∈ ((Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L)).filter
          (fun d => exactSet Q d = K), ‖Sx c (g * Linv L d) d‖ * (d : ℝ) ^ (-x)
        ≤ 2 * ∑' d : ℕ, (if exactSet Q d = K then Fw c L x Q d else 0) := by
    intro K hK
    have hKQ : K ⊆ Q := Finset.mem_powerset.mp hK
    obtain ⟨hP, hmain⟩ := hPf K hKQ
    rw [Finset.filter_filter]
    apply K_bound c L g Q hQ K hKQ x hs
    intro β hβ
    have hinv : ∀ p ∈ Pf K, ∀ m, aK c L Q K (p * m) = aK c L Q K m := by
      intro p hp m
      obtain ⟨hpp, hp3, hpE⟩ := hP p hp
      obtain ⟨h3c, hpL⟩ := hEprop p hpE
      have hpQ : p ∉ Q := by
        intro h
        have := (hQ p h).1.2.1
        omega
      exact aK_inv c L Q K hQp p hpp hp3 h3c hpL hpQ m
    have hsa : Summable (fun m : ℕ => aK c L Q K m * (m : ℝ) ^ (-x)) :=
      Summable.of_nonneg_of_le
        (fun m => mul_nonneg (aK_nonneg c L Q K m) (Real.rpow_nonneg (Nat.cast_nonneg m) _))
        (fun m => mul_le_mul_of_nonneg_right (aK_le c L Q K m)
          (Real.rpow_nonneg (Nat.cast_nonneg m) _)) hs
    have h1 := hmain x hx1 (lt_of_lt_of_le hxc (by linarith [hη₁le K hK]))
      (aK c L Q K) (aK_nonneg c L Q K) hsa hinv β hβ
    have e : ((1 : ℝ) + 1) = 2 := by norm_num
    rw [e] at h1
    exact h1
  refine (Finset.sum_le_sum hKb).trans ?_
  rw [← Finset.mul_sum]
  have hsF := summable_Fw c L x Q hs
  have hsumK : ∑ K ∈ Q.powerset, ∑' d : ℕ, (if exactSet Q d = K then Fw c L x Q d else 0)
      = ∑' d : ℕ, Fw c L x Q d := by
    rw [← Summable.tsum_finsetSum]
    · apply tsum_congr
      intro d
      rw [Finset.sum_ite_eq,
        if_pos (Finset.mem_powerset.mpr (show exactSet Q d ⊆ Q from Finset.filter_subset _ _))]
    · intro K _
      refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) hsF
      · split_ifs
        · exact Fw_nonneg c L x Q d
        · exact le_rfl
      · split_ifs
        · exact le_rfl
        · exact Fw_nonneg c L x Q d
  rw [hsumK]
  have hFw := Fw_sum_le c L x hx1 hs Q (fun q hq => ⟨(hQ q hq).1, (hQ q hq).2.1, (hQ q hq).2.2.1⟩)
  have hbw : ∑' d, bw c L x d ≤ 2 * C / (x - 1) :=
    ((summable_bw c L x hs).tsum_le_tsum (bw_le c L x) hs).trans hsbound
  -- the product over `Q` is small
  have hf : ∀ q ∈ Q, 0 ≤ (q : ℝ) ^ (-x) / 2 ∧ (q : ℝ) ^ (-x) / 2 ≤ 1 := by
    intro q hq
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (hQp q hq).one_le
    have h1 : (q : ℝ) ^ (-x) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by linarith)
    have h0 : 0 ≤ (q : ℝ) ^ (-x) := Real.rpow_nonneg (by linarith) _
    constructor <;> linarith
  have hprod := prod_one_sub_le (fun q : ℕ => (q : ℝ) ^ (-x) / 2) Q hf
  have hsumQ : 4 * C / ε ≤ ∑ q ∈ Q, (q : ℝ) ^ (-x) / 2 := by
    have h1 : ∑ q ∈ Q, (1 : ℝ) / q / 4 ≤ ∑ q ∈ Q, (q : ℝ) ^ (-x) / 2 := by
      apply Finset.sum_le_sum
      intro q hq
      have := hηQb q hq (hQp q hq).pos x hx1 hxb
      have hq0 : (0 : ℝ) < q := by exact_mod_cast (hQp q hq).pos
      have e : (1 : ℝ) / q / 4 = 1 / (2 * (q : ℝ)) / 2 := by
        field_simp
        ring
      rw [e]
      linarith
    have h2 : ∑ q ∈ Q, (1 : ℝ) / q / 4 = (∑ q ∈ Q, (1 : ℝ) / q) / 4 := by
      rw [Finset.sum_div]
    have h3 : 4 * C / ε = 16 * C / ε / 4 := by ring
    rw [h3]
    linarith
  obtain ⟨Pi0, hPi0⟩ : ∃ Pi0 : ℝ, Pi0 = ∏ q ∈ Q, (1 - (q : ℝ) ^ (-x) / 2) := ⟨_, rfl⟩
  rw [← hPi0] at hFw hprod
  have hPi0nn : 0 ≤ Pi0 := by
    rw [hPi0]
    exact Finset.prod_nonneg (fun q hq => by linarith [(hf q hq).2])
  have hPismall : Pi0 * (4 * C / ε) ≤ 1 := by
    have h1 : Pi0 * (4 * C / ε) ≤ Pi0 * (1 + ∑ q ∈ Q, (q : ℝ) ^ (-x) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) hPi0nn
    linarith
  have hbw0 : 0 ≤ ∑' d, bw c L x d := tsum_nonneg (bw_nonneg c L x)
  have hfinal : 2 * (Pi0 * (2 * C / (x - 1))) ≤ ε / (x - 1) := by
    have e : 2 * (Pi0 * (2 * C / (x - 1))) = (Pi0 * (4 * C / ε)) * (ε / (x - 1)) := by
      field_simp
      ring
    rw [e]
    have h4 : 0 ≤ ε / (x - 1) := by positivity
    calc (Pi0 * (4 * C / ε)) * (ε / (x - 1)) ≤ 1 * (ε / (x - 1)) :=
          mul_le_mul_of_nonneg_right hPismall h4
      _ = ε / (x - 1) := one_mul _
  calc 2 * ∑' d : ℕ, Fw c L x Q d
      ≤ 2 * (Pi0 * ∑' d, bw c L x d) := by linarith
    _ ≤ 2 * (Pi0 * (2 * C / (x - 1))) := by
        have := mul_le_mul_of_nonneg_left hbw hPi0nn
        linarith
    _ ≤ ε / (x - 1) := hfinal

end coreThm



section sieveClasses

/-- The quantity `3 d (4 e (c - (d (m - j))^3) - d^3)`, a square modulo `ℓ` for bad pairs. -/
def Wf (c m e : ℤ) (d j : ℤ) : ℤ := 3 * d * (4 * e * (c - (d * (m - j)) ^ 3) - d ^ 3)

lemma Wf_sub_dvd (c m e : ℤ) (d j j' n : ℤ) (h : n ∣ j - j') :
    n ∣ Wf c m e d j - Wf c m e d j' := by
  obtain ⟨u, hu⟩ := h
  refine ⟨12 * e * d * (d * u) * ((d * (m - j')) ^ 2 + (d * (m - j')) * (d * (m - j))
    + (d * (m - j)) ^ 2), ?_⟩
  unfold Wf
  have hj : j = j' + n * u := by linarith
  rw [hj]
  ring

/-- Admissible arc index `j` for the modulus `d` at the prime `ℓ`. -/
def adm (c m e : ℤ) (ℓ d j : ℕ) : Prop :=
  ∃ z : ℤ, (ℓ : ℤ) ∣ Wf c m e d j - z ^ 2

lemma adm_congr (c m e : ℤ) (ℓ d j j' : ℕ) (h : (ℓ : ℤ) ∣ (j : ℤ) - j') :
    adm c m e ℓ d j → adm c m e ℓ d j' := by
  rintro ⟨z, hz⟩
  refine ⟨z, ?_⟩
  have h1 := Wf_sub_dvd c m e d j j' ℓ h
  have h2 := dvd_sub hz h1
  have e1 : Wf c m e d j - z ^ 2 - (Wf c m e d j - Wf c m e d j') = Wf c m e d j' - z ^ 2 := by
    ring
  rwa [e1] at h2

lemma adm_mod (c m e : ℤ) (ℓ d j n : ℕ) (hn : ℓ ∣ n) (h : adm c m e ℓ d j) :
    adm c m e ℓ d (j % n) := by
  apply adm_congr c m e ℓ d j (j % n) _ h
  have h1 : (n : ℤ) ∣ ((j % n : ℕ) : ℤ) - (j : ℤ) := natCast_mod_sub j n
  have h2 : (ℓ : ℤ) ∣ ((j % n : ℕ) : ℤ) - (j : ℤ) := dvd_trans (by exact_mod_cast hn) h1
  have h3 := dvd_neg.mpr h2
  have e1 : -(((j % n : ℕ) : ℤ) - (j : ℤ)) = (j : ℤ) - ((j % n : ℕ) : ℤ) := by ring
  rwa [e1] at h3

lemma prime_not_dvd_twelve (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ) : ¬ (ℓ : ℤ) ∣ 12 := by
  intro h
  have h1 : ℓ ∣ 12 := by exact_mod_cast h
  have h2 : ℓ ∣ 2 * (2 * 3) := h1
  rcases (Nat.Prime.dvd_mul hℓ).mp h2 with h3 | h3
  · have := Nat.le_of_dvd (by norm_num) h3
    omega
  · rcases (Nat.Prime.dvd_mul hℓ).mp h3 with h4 | h4
    · have := Nat.le_of_dvd (by norm_num) h4
      omega
    · have := Nat.le_of_dvd (by norm_num) h4
      omega

open Classical in
/-- At most `(ℓ + 1) / 2` residues `a` modulo `ℓ` are admissible. -/
lemma adm_card_le (c m e : ℤ) (he : e ^ 2 = 1) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : ℓ % 3 = 2)
    (hℓ5 : 5 ≤ ℓ) (d : ℕ) (hd : ¬ ℓ ∣ d) :
    ((Finset.range ℓ).filter (adm c m e ℓ d)).card ≤ (ℓ + 1) / 2 := by
  have hpp : Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  have hodd : ℓ % 2 = 1 := by
    rcases Nat.Prime.eq_two_or_odd hℓ with h | h
    · omega
    · exact h
  have hred : ∀ a ∈ (Finset.range ℓ).filter (adm c m e ℓ d),
      ∃ w : ℕ, w < (ℓ + 1) / 2 ∧ (ℓ : ℤ) ∣ Wf c m e d a - (w : ℤ) ^ 2 := by
    intro a ha
    obtain ⟨z, hz⟩ := (Finset.mem_filter.mp ha).2
    have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast hℓ.ne_zero
    have hℓpos : (0 : ℤ) < ℓ := by exact_mod_cast hℓ.pos
    have h0 : 0 ≤ z % (ℓ : ℤ) := Int.emod_nonneg _ hℓ0
    have h1 : z % (ℓ : ℤ) < ℓ := Int.emod_lt_of_pos _ hℓpos
    obtain ⟨y, hy⟩ : ∃ y : ℕ, (y : ℤ) = z % (ℓ : ℤ) := ⟨(z % (ℓ : ℤ)).toNat, Int.toNat_of_nonneg h0⟩
    have hylt : y < ℓ := by
      have : (y : ℤ) < ℓ := by rw [hy]; exact h1
      exact_mod_cast this
    have hzy : (ℓ : ℤ) ∣ z - y := by
      rw [hy, Int.emod_def]
      exact ⟨z / (ℓ : ℤ), by ring⟩
    have hzy2 : (ℓ : ℤ) ∣ z ^ 2 - (y : ℤ) ^ 2 := by
      have e1 : z ^ 2 - (y : ℤ) ^ 2 = (z - y) * (z + y) := by ring
      rw [e1]
      exact dvd_mul_of_dvd_left hzy _
    by_cases hsmall : y < (ℓ + 1) / 2
    · refine ⟨y, hsmall, ?_⟩
      have := dvd_add hz hzy2
      have e1 : Wf c m e d a - z ^ 2 + (z ^ 2 - (y : ℤ) ^ 2) = Wf c m e d a - (y : ℤ) ^ 2 := by
        ring
      rwa [e1] at this
    · refine ⟨ℓ - y, by omega, ?_⟩
      have hcast : ((ℓ - y : ℕ) : ℤ) = (ℓ : ℤ) - y := by
        rw [Nat.cast_sub hylt.le]
      rw [hcast]
      have h3 : (ℓ : ℤ) ∣ (y : ℤ) ^ 2 - ((ℓ : ℤ) - y) ^ 2 :=
        ⟨2 * (y : ℤ) - ℓ, by ring⟩
      have := dvd_add (dvd_add hz hzy2) h3
      have e1 : Wf c m e d a - z ^ 2 + (z ^ 2 - (y : ℤ) ^ 2)
          + ((y : ℤ) ^ 2 - ((ℓ : ℤ) - y) ^ 2) = Wf c m e d a - ((ℓ : ℤ) - y) ^ 2 := by ring
      rwa [e1] at this
  obtain ⟨f, hf⟩ : ∃ f : ℕ → ℕ, ∀ a ∈ (Finset.range ℓ).filter (adm c m e ℓ d),
      f a < (ℓ + 1) / 2 ∧ (ℓ : ℤ) ∣ Wf c m e d a - (f a : ℤ) ^ 2 := by
    refine ⟨fun a => if h : ∃ w : ℕ, w < (ℓ + 1) / 2 ∧ (ℓ : ℤ) ∣ Wf c m e d a - (w : ℤ) ^ 2
      then Classical.choose h else 0, ?_⟩
    intro a ha
    have h := hred a ha
    simp only [dif_pos h]
    exact Classical.choose_spec h
  have hcard : ((Finset.range ℓ).filter (adm c m e ℓ d)).card ≤ (Finset.range ((ℓ + 1) / 2)).card := by
    apply Finset.card_le_card_of_injOn f
    · intro a ha
      exact Finset.mem_coe.mpr (Finset.mem_range.mpr (hf a ha).1)
    · intro a ha a' ha' hfa
      have ha1 := Finset.mem_coe.mp ha
      have ha1' := Finset.mem_coe.mp ha'
      have h1 := (hf a ha1).2
      have h2 := (hf a' ha1').2
      have hfa' : f a = f a' := hfa
      rw [hfa'] at h1
      have h3 := dvd_sub h1 h2
      have e1 : Wf c m e d a - (f a' : ℤ) ^ 2 - (Wf c m e d a' - (f a' : ℤ) ^ 2)
          = 12 * (e * ((d : ℤ) * (((d : ℤ) * (m - a')) ^ 3 - ((d : ℤ) * (m - a)) ^ 3))) := by
        unfold Wf
        ring
      rw [e1] at h3
      have hne : ¬ (ℓ : ℤ) ∣ e := by
        intro h
        have h4 : (ℓ : ℤ) ∣ e ^ 2 := dvd_pow h two_ne_zero
        rw [he] at h4
        have h5 : ℓ ∣ 1 := by exact_mod_cast h4
        have := Nat.le_of_dvd one_pos h5
        omega
      have hnd : ¬ (ℓ : ℤ) ∣ (d : ℤ) := by
        intro h
        exact hd (by exact_mod_cast h)
      have h4 : (ℓ : ℤ) ∣ ((d : ℤ) * (m - a')) ^ 3 - ((d : ℤ) * (m - a)) ^ 3 := by
        rcases hpp.dvd_or_dvd h3 with h | h
        · exact absurd h (prime_not_dvd_twelve ℓ hℓ hℓ5)
        · rcases hpp.dvd_or_dvd h with h | h
          · exact absurd h hne
          · rcases hpp.dvd_or_dvd h with h | h
            · exact absurd h hnd
            · exact h
      have h5 := prime_dvd_sub_of_dvd_cube_sub ℓ hℓ hℓ3 _ _ h4
      have e2 : (d : ℤ) * (m - a') - (d : ℤ) * (m - a) = (d : ℤ) * ((a : ℤ) - a') := by ring
      rw [e2] at h5
      have h6 : (ℓ : ℤ) ∣ (a : ℤ) - a' := by
        rcases hpp.dvd_or_dvd h5 with h | h
        · exact absurd h hnd
        · exact h
      have hlt := Finset.mem_range.mp (Finset.mem_filter.mp ha1).1
      have hlt' := Finset.mem_range.mp (Finset.mem_filter.mp ha1').1
      have h7 : (a : ℤ) - a' = 0 := by
        apply Int.eq_zero_of_abs_lt_dvd h6
        rw [abs_lt]
        constructor <;> omega
      omega
  rw [Finset.card_range] at hcard
  exact hcard

open Classical in
/-- Chinese remainder count of the admissible arc indices modulo `L = ∏ S`. -/
lemma jclass_card_le (c m e : ℤ) (he : e ^ 2 = 1) (d : ℕ) :
    ∀ S : Finset ℕ, (∀ ℓ ∈ S, ℓ.Prime ∧ ℓ % 3 = 2 ∧ 5 ≤ ℓ ∧ ¬ ℓ ∣ d) →
      (((Finset.range (∏ ℓ ∈ S, ℓ)).filter (fun j => ∀ ℓ ∈ S, adm c m e ℓ d j)).card : ℝ)
        ≤ ∏ ℓ ∈ S, (((ℓ : ℝ) + 1) / 2) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro _
    simp
  | insert ℓ S hℓS ih =>
    intro hS
    obtain ⟨hℓp, hℓ3, hℓ5, hℓd⟩ := hS ℓ (Finset.mem_insert_self ℓ S)
    have hS' : ∀ ℓ' ∈ S, ℓ'.Prime ∧ ℓ' % 3 = 2 ∧ 5 ≤ ℓ' ∧ ¬ ℓ' ∣ d :=
      fun ℓ' h => hS ℓ' (Finset.mem_insert_of_mem h)
    have ih' := ih hS'
    have hcop : Nat.Coprime ℓ (∏ ℓ' ∈ S, ℓ') := by
      apply Nat.Coprime.prod_right
      intro ℓ' h
      exact (Nat.coprime_primes hℓp (hS' ℓ' h).1).mpr (fun h2 => hℓS (h2 ▸ h))
    have hL'pos : 0 < ∏ ℓ' ∈ S, ℓ' := Finset.prod_pos (fun ℓ' h => (hS' ℓ' h).1.pos)
    rw [Finset.prod_insert hℓS, Finset.prod_insert hℓS]
    have hinj : ((Finset.range (ℓ * ∏ ℓ' ∈ S, ℓ')).filter
          (fun j => ∀ ℓ'' ∈ insert ℓ S, adm c m e ℓ'' d j)).card
        ≤ (((Finset.range ℓ).filter (adm c m e ℓ d)) ×ˢ
            ((Finset.range (∏ ℓ' ∈ S, ℓ')).filter (fun j => ∀ ℓ' ∈ S, adm c m e ℓ' d j))).card := by
      apply Finset.card_le_card_of_injOn (fun j => (j % ℓ, j % ∏ ℓ' ∈ S, ℓ'))
      · intro j hj
        obtain ⟨hj1, hj2⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hj)
        rw [Finset.mem_coe, Finset.mem_product, Finset.mem_filter, Finset.mem_filter,
          Finset.mem_range, Finset.mem_range]
        refine ⟨⟨Nat.mod_lt j hℓp.pos, ?_⟩, ⟨Nat.mod_lt j hL'pos, ?_⟩⟩
        · exact adm_mod c m e ℓ d j ℓ (dvd_refl ℓ) (hj2 ℓ (Finset.mem_insert_self ℓ S))
        · intro ℓ' h
          exact adm_mod c m e ℓ' d j _ (Finset.dvd_prod_of_mem _ h)
            (hj2 ℓ' (Finset.mem_insert_of_mem h))
      · intro j hj j' hj' h
        have hj1 := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hj)).1
        have hj1' := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_coe.mp hj')).1
        rw [Prod.mk.injEq] at h
        have h1 : j ≡ j' [MOD ℓ] := h.1
        have h2 : j ≡ j' [MOD ∏ ℓ' ∈ S, ℓ'] := h.2
        exact eq_of_modEq_of_lt ((Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h1, h2⟩) hj1 hj1'
    rw [Finset.card_product] at hinj
    have h1 := adm_card_le c m e he ℓ hℓp hℓ3 hℓ5 d hℓd
    have h2 : (((Finset.range ℓ).filter (adm c m e ℓ d)).card : ℝ) ≤ ((ℓ : ℝ) + 1) / 2 := by
      have h3 : (((ℓ + 1) / 2 : ℕ) : ℝ) ≤ ((ℓ : ℝ) + 1) / 2 := by
        have := Nat.div_mul_le_self (ℓ + 1) 2
        have h4 : ((((ℓ + 1) / 2 : ℕ) : ℝ)) * 2 ≤ (ℓ : ℝ) + 1 := by exact_mod_cast this
        linarith
      exact (by exact_mod_cast h1 : (((Finset.range ℓ).filter (adm c m e ℓ d)).card : ℝ)
        ≤ (((ℓ + 1) / 2 : ℕ) : ℝ)).trans h3
    calc (((Finset.range (ℓ * ∏ ℓ' ∈ S, ℓ')).filter
          (fun j => ∀ ℓ'' ∈ insert ℓ S, adm c m e ℓ'' d j)).card : ℝ)
        ≤ (((Finset.range ℓ).filter (adm c m e ℓ d)).card : ℝ)
          * (((Finset.range (∏ ℓ' ∈ S, ℓ')).filter
              (fun j => ∀ ℓ' ∈ S, adm c m e ℓ' d j)).card : ℝ) := by exact_mod_cast hinj
      _ ≤ (((ℓ : ℝ) + 1) / 2) * ∏ ℓ' ∈ S, (((ℓ' : ℝ) + 1) / 2) :=
          mul_le_mul h2 ih' (Nat.cast_nonneg _) (by positivity)

end sieveClasses



section arcs

/-- `u = r · L⁻¹ mod d`, as a natural number below `d`. -/
def uL (L d r : ℕ) : ℕ := Int.toNat (((r : ℤ) * Linv L d) % (d : ℤ))

/-- Index of the arc of length `1/L` containing `u/d`. -/
def jidx (L d r : ℕ) : ℕ := uL L d r * L / d

lemma uL_spec (L d r : ℕ) (hd : 0 < d) :
    uL L d r < d ∧ (d : ℤ) ∣ (uL L d r : ℤ) - (r : ℤ) * Linv L d := by
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdpos : (0 : ℤ) < d := by exact_mod_cast hd
  have h0 : 0 ≤ ((r : ℤ) * Linv L d) % (d : ℤ) := Int.emod_nonneg _ hd0
  have h1 : ((r : ℤ) * Linv L d) % (d : ℤ) < d := Int.emod_lt_of_pos _ hdpos
  have hu : (uL L d r : ℤ) = ((r : ℤ) * Linv L d) % (d : ℤ) := Int.toNat_of_nonneg h0
  constructor
  · have : (uL L d r : ℤ) < d := by rw [hu]; exact h1
    exact_mod_cast this
  · rw [hu, Int.emod_def]
    exact ⟨-(((r : ℤ) * Linv L d) / (d : ℤ)), by ring⟩

lemma uL_mul (L d r : ℕ) (hd : 0 < d) (hcop : Nat.Coprime L d) (hr : r < d) :
    uL L d r * L = d * jidx L d r + r := by
  obtain ⟨_, h2⟩ := uL_spec L d r hd
  obtain ⟨v, hv⟩ := Linv_spec L d hcop
  obtain ⟨w, hw⟩ := h2
  have h3 : (d : ℤ) ∣ ((uL L d r * L : ℕ) : ℤ) - (r : ℤ) := by
    refine ⟨w * L + r * v, ?_⟩
    push_cast
    linear_combination (L : ℤ) * hw + (r : ℤ) * hv
  have h4 : (uL L d r * L) % d = r := by
    have h5 : r ≡ uL L d r * L [MOD d] := Nat.modEq_iff_dvd.mpr h3
    have h6 : r % d = (uL L d r * L) % d := h5
    rw [← h6, Nat.mod_eq_of_lt hr]
  have h7 := Nat.div_add_mod (uL L d r * L) d
  unfold jidx
  rw [h4] at h7
  exact h7.symm

lemma jidx_lt (L d r : ℕ) (hd : 0 < d) (hL : 0 < L) : jidx L d r < L := by
  unfold jidx
  apply Nat.div_lt_of_lt_mul
  exact Nat.mul_lt_mul_of_pos_right (uL_spec L d r hd).1 hL

lemma ee_re (t : ℝ) : (ee t).re = Real.cos (2 * Real.pi * t) := by
  unfold ee
  have e : (2 * Real.pi * Complex.I * t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [e, Complex.exp_ofReal_mul_I_re]

/-- Fejér-type lower bound: a short exponential sum is large near the origin. -/
lemma norm_sum_ee_ge (N : ℕ) (w : ℝ) (hw : |w| * (6 * N) ≤ 1) :
    (N : ℝ) / 2 ≤ ‖∑ k ∈ Finset.range N, ee ((k : ℝ) * w)‖ := by
  refine le_trans ?_ (Complex.re_le_norm _)
  rw [Complex.re_sum]
  have hterm : ∀ k ∈ Finset.range N, (1 : ℝ) / 2 ≤ (ee ((k : ℝ) * w)).re := by
    intro k hk
    have hkN : (k : ℝ) ≤ N := by exact_mod_cast (Finset.mem_range.mp hk).le
    have habs : |2 * Real.pi * ((k : ℝ) * w)| = 2 * Real.pi * ((k : ℝ) * |w|) := by
      have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
      rw [abs_mul (2 * Real.pi) ((k : ℝ) * w), abs_of_pos h2pi, abs_mul (k : ℝ) w,
        abs_of_nonneg (Nat.cast_nonneg k)]
    rw [ee_re, ← Real.cos_abs, ← Real.cos_pi_div_three, habs]
    apply Real.cos_le_cos_of_nonneg_of_le_pi
    · have := abs_nonneg w
      positivity
    · linarith [Real.pi_pos]
    · have h1 : (k : ℝ) * |w| ≤ 1 / 6 := by
        have h2 : (k : ℝ) * |w| ≤ N * |w| := mul_le_mul_of_nonneg_right hkN (abs_nonneg w)
        nlinarith [abs_nonneg w]
      nlinarith [Real.pi_pos]
  calc (N : ℝ) / 2 = ∑ _k ∈ Finset.range N, (1 : ℝ) / 2 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        ring
    _ ≤ ∑ k ∈ Finset.range N, (ee ((k : ℝ) * w)).re := Finset.sum_le_sum hterm

/-- The number of roots whose `u/d` lies in a given arc is controlled by exponential sums. -/
lemma arc_count_le (c : ℤ) (L d : ℕ) (hd : 0 < d) (hcop : Nat.Coprime L d) (N : ℕ) (hN : 0 < N)
    (hNL : 3 * N ≤ L) (j : ℕ) :
    (((rootsMod c d).filter (fun r => jidx L d r = j)).card : ℝ)
      ≤ 4 / (N : ℝ) ^ 2 * ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N,
          ‖Sx c (((k : ℤ) - (k' : ℤ)) * Linv L d) d‖ := by
  have hLpos : 0 < L := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨y, hy⟩ : ∃ y : ℝ, y = (2 * (j : ℝ) + 1) / (2 * L) := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A : ℕ → ℂ, A = fun r : ℕ =>
      ∑ k ∈ Finset.range N, ee ((k : ℝ) * ((uL L d r : ℝ) / d - y)) := ⟨_, rfl⟩
  have hAa : ∀ r, A r = ∑ k ∈ Finset.range N, ee ((k : ℝ) * ((uL L d r : ℝ) / d - y)) :=
    fun _ => by rw [hA]
  -- each root in the arc contributes at least 1
  have hone : ∀ r ∈ (rootsMod c d).filter (fun r => jidx L d r = j),
      (1 : ℝ) ≤ 4 / (N : ℝ) ^ 2 * ‖A r‖ ^ 2 := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
    have hrd := ((mem_rootsMod c d r).mp hr1).1
    have hmul := uL_mul L d r hd hcop hrd
    rw [hr2] at hmul
    have hmulR : (uL L d r : ℝ) * L = d * j + r := by exact_mod_cast hmul
    have hrR : (r : ℝ) < d := by exact_mod_cast hrd
    have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hw : (uL L d r : ℝ) / d - y = ((r : ℝ) / d - 1 / 2) / L := by
      rw [hy]
      field_simp
      linear_combination (2 : ℝ) * hmulR
    have hrd1 : (r : ℝ) / d < 1 := (div_lt_one hdR).mpr hrR
    have hrd0 : 0 ≤ (r : ℝ) / d := div_nonneg hr0 hdR.le
    have hwabs : |(uL L d r : ℝ) / d - y| * (6 * N) ≤ 1 := by
      rw [hw, abs_div, abs_of_pos hLR]
      have h1 : |(r : ℝ) / d - 1 / 2| ≤ 1 / 2 := by
        rw [abs_le]
        constructor <;> linarith
      have h2 : (6 : ℝ) * N ≤ 2 * L := by
        have : (3 * N : ℕ) ≤ L := hNL
        have h3 : ((3 * N : ℕ) : ℝ) ≤ L := by exact_mod_cast this
        push_cast at h3
        linarith
      rw [div_mul_eq_mul_div, div_le_one hLR]
      nlinarith [abs_nonneg ((r : ℝ) / d - 1 / 2)]
    have h3 := norm_sum_ee_ge N _ hwabs
    rw [← hAa] at h3
    have h4 : ((N : ℝ) / 2) ^ 2 ≤ ‖A r‖ ^ 2 := pow_le_pow_left₀ (by positivity) h3 2
    have h5 : (1 : ℝ) = 4 / (N : ℝ) ^ 2 * ((N : ℝ) / 2) ^ 2 := by
      field_simp
      norm_num
    rw [h5]
    exact mul_le_mul_of_nonneg_left h4 (by positivity)
  -- sum of squares as a double sum of exponential sums
  have hsq : ∑ r ∈ rootsMod c d, ‖A r‖ ^ 2
      ≤ ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N,
          ‖Sx c (((k : ℤ) - (k' : ℤ)) * Linv L d) d‖ := by
    have h1 : ((∑ r ∈ rootsMod c d, ‖A r‖ ^ 2 : ℝ) : ℂ)
        = ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N,
            ee (-(((k : ℝ) - k') * y)) * Sx c (((k : ℤ) - (k' : ℤ)) * Linv L d) d := by
      have h2 : ∀ r ∈ rootsMod c d, ((‖A r‖ ^ 2 : ℝ) : ℂ)
          = ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N, ee (-(((k : ℝ) - k') * y))
              * ee ((((((k : ℤ) - (k' : ℤ)) * Linv L d : ℤ)) : ℝ) * r / d) := by
        intro r hr
        have hrd := ((mem_rootsMod c d r).mp hr).1
        obtain ⟨_, w, hw⟩ := uL_spec L d r hd
        push_cast
        rw [← Complex.mul_conj', hAa, map_sum, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro k' _
        rw [conj_ee, ← ee_add, ← ee_add]
        apply ee_eq_of_sub_int _ _ (((k : ℤ) - k') * w)
        have hwR : (uL L d r : ℝ) - (r : ℝ) * (Linv L d : ℝ) = d * w := by exact_mod_cast hw
        push_cast
        field_simp
        linear_combination ((k : ℝ) - k') * hwR
      rw [Complex.ofReal_sum, Finset.sum_congr rfl h2, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k' _
      unfold Sx
      rw [Finset.mul_sum]
    have h3 : 0 ≤ ∑ r ∈ rootsMod c d, ‖A r‖ ^ 2 := Finset.sum_nonneg (fun r _ => sq_nonneg _)
    have h4 := congrArg norm h1
    rw [Complex.norm_real, Real.norm_of_nonneg h3] at h4
    rw [h4]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k _ => ?_))
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun k' _ => ?_))
    rw [norm_mul, norm_ee, one_mul]
  calc (((rootsMod c d).filter (fun r => jidx L d r = j)).card : ℝ)
      = ∑ _r ∈ (rootsMod c d).filter (fun r => jidx L d r = j), (1 : ℝ) := by simp
    _ ≤ ∑ r ∈ (rootsMod c d).filter (fun r => jidx L d r = j), 4 / (N : ℝ) ^ 2 * ‖A r‖ ^ 2 :=
        Finset.sum_le_sum hone
    _ ≤ ∑ r ∈ rootsMod c d, 4 / (N : ℝ) ^ 2 * ‖A r‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun r _ _ => by positivity)
    _ = 4 / (N : ℝ) ^ 2 * ∑ r ∈ rootsMod c d, ‖A r‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ 4 / (N : ℝ) ^ 2 * ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N,
          ‖Sx c (((k : ℤ) - (k' : ℤ)) * Linv L d) d‖ :=
        mul_le_mul_of_nonneg_left hsq (by positivity)

end arcs



section reduction

/-- Bad roots for the modulus `d`: `4 e (c - t^3) = d (d^2 + 3 s^2)` with `t = r + d m`. -/
def badRoot (c m e : ℤ) (d r : ℕ) : Prop :=
  ∃ s : ℤ, 4 * e * (c - ((r : ℤ) + d * m) ^ 3) = d * ((d : ℤ) ^ 2 + 3 * s ^ 2)

lemma adm_of_bad (c m e : ℤ) (L d r : ℕ) (hd : 0 < d) (hcop : Nat.Coprime L d) (hr : r < d)
    (ℓ : ℕ) (hℓ : ℓ ∣ L) (hbad : badRoot c m e d r) : adm c m e ℓ d (jidx L d r) := by
  obtain ⟨s, hs⟩ := hbad
  have hmul := uL_mul L d r hd hcop hr
  refine ⟨3 * d * s, ?_⟩
  have ht : (ℓ : ℤ) ∣ ((r : ℤ) + d * m) - (d : ℤ) * (m - (jidx L d r : ℤ)) := by
    have e1 : ((r : ℤ) + d * m) - (d : ℤ) * (m - (jidx L d r : ℤ))
        = ((uL L d r * L : ℕ) : ℤ) := by
      rw [hmul]
      push_cast
      ring
    rw [e1]
    push_cast
    exact dvd_mul_of_dvd_right (by exact_mod_cast hℓ) _
  obtain ⟨u, hu⟩ := ht
  unfold Wf
  refine ⟨12 * e * d * u * (((r : ℤ) + d * m) ^ 2
    + ((r : ℤ) + d * m) * ((d : ℤ) * (m - (jidx L d r : ℤ)))
    + ((d : ℤ) * (m - (jidx L d r : ℤ))) ^ 2), ?_⟩
  linear_combination (3 * (d : ℤ)) * hs + (12 * e * d * (((r : ℤ) + d * m) ^ 2
    + ((r : ℤ) + d * m) * ((d : ℤ) * (m - (jidx L d r : ℤ)))
    + ((d : ℤ) * (m - (jidx L d r : ℤ))) ^ 2)) * hu

/-- Arbitrarily many large primes `≡ 2 (mod 3)`. -/
lemma exists_primes_two (B : ℕ) : ∀ n : ℕ, ∃ S : Finset ℕ, S.card = n
    ∧ ∀ ℓ ∈ S, ℓ.Prime ∧ ℓ % 3 = 2 ∧ B < ℓ := by
  intro n
  induction n with
  | zero => exact ⟨∅, rfl, by simp⟩
  | succ n ih =>
    obtain ⟨S, hS1, hS2⟩ := ih
    obtain ⟨p, hp1, hp2, hp3⟩ := Nat.forall_exists_prime_gt_and_modEq (max B (∑ ℓ ∈ S, ℓ))
      (q := 3) (a := 2) (by norm_num) (by norm_num)
    have hpS : p ∉ S := by
      intro h
      have h1 : p ≤ ∑ ℓ ∈ S, ℓ := Finset.single_le_sum (fun i _ => Nat.zero_le i) h
      have h2 : ∑ ℓ ∈ S, ℓ ≤ max B (∑ ℓ ∈ S, ℓ) := le_max_right _ _
      omega
    refine ⟨insert p S, by rw [Finset.card_insert_of_notMem hpS, hS1], ?_⟩
    intro ℓ hℓ
    rcases Finset.mem_insert.mp hℓ with rfl | h
    · refine ⟨hp2, ?_, lt_of_le_of_lt (le_max_left _ _) hp1⟩
      have h4 : ℓ % 3 = 2 % 3 := hp3
      omega
    · exact hS2 ℓ h

open Classical in
/-- Bad roots are counted by the admissible arcs. -/
lemma bad_card_le (c m e : ℤ) (he : e ^ 2 = 1) (S : Finset ℕ)
    (hS : ∀ ℓ ∈ S, ℓ.Prime ∧ ℓ % 3 = 2 ∧ 5 ≤ ℓ) (d : ℕ) (hd : 0 < d)
    (hcop : Nat.Coprime (∏ ℓ ∈ S, ℓ) d) (N : ℕ) (hN : 0 < N) (hNL : 3 * N ≤ ∏ ℓ ∈ S, ℓ) :
    (((rootsMod c d).filter (badRoot c m e d)).card : ℝ)
      ≤ (∏ ℓ ∈ S, (((ℓ : ℝ) + 1) / 2)) * (4 / (N : ℝ) ^ 2 * ∑ k ∈ Finset.range N,
          ∑ k' ∈ Finset.range N, ‖Sx c (((k : ℤ) - (k' : ℤ)) * Linv (∏ ℓ ∈ S, ℓ) d) d‖) := by
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = ∏ ℓ ∈ S, ℓ := ⟨_, rfl⟩
  rw [← hL] at hcop hNL ⊢
  have hLpos : 0 < L := by omega
  have hSd : ∀ ℓ ∈ S, ℓ.Prime ∧ ℓ % 3 = 2 ∧ 5 ≤ ℓ ∧ ¬ ℓ ∣ d := by
    intro ℓ hℓ
    obtain ⟨h1, h2, h3⟩ := hS ℓ hℓ
    refine ⟨h1, h2, h3, ?_⟩
    intro h
    have hℓL : ℓ ∣ L := by rw [hL]; exact Finset.dvd_prod_of_mem _ hℓ
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hℓL hcop) h
    have := h1.one_lt
    omega
  obtain ⟨J, hJ⟩ : ∃ J : Finset ℕ,
      J = (Finset.range L).filter (fun j => ∀ ℓ ∈ S, adm c m e ℓ d j) := ⟨_, rfl⟩
  have hJcard : (J.card : ℝ) ≤ ∏ ℓ ∈ S, (((ℓ : ℝ) + 1) / 2) := by
    rw [hJ, hL]
    exact jclass_card_le c m e he d S hSd
  have hsub : (rootsMod c d).filter (badRoot c m e d)
      ⊆ J.biUnion (fun j => (rootsMod c d).filter (fun r => jidx L d r = j)) := by
    intro r hr
    obtain ⟨hr1, hr2⟩ := Finset.mem_filter.mp hr
    have hrd := ((mem_rootsMod c d r).mp hr1).1
    rw [Finset.mem_biUnion]
    refine ⟨jidx L d r, ?_, Finset.mem_filter.mpr ⟨hr1, rfl⟩⟩
    rw [hJ, Finset.mem_filter, Finset.mem_range]
    refine ⟨jidx_lt L d r hd hLpos, ?_⟩
    intro ℓ hℓ
    have hℓL : ℓ ∣ L := by rw [hL]; exact Finset.dvd_prod_of_mem _ hℓ
    exact adm_of_bad c m e L d r hd hcop hrd ℓ hℓL hr2
  have h1 : (((rootsMod c d).filter (badRoot c m e d)).card : ℝ)
      ≤ ∑ j ∈ J, (((rootsMod c d).filter (fun r => jidx L d r = j)).card : ℝ) := by
    have h2 := (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    exact_mod_cast h2
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = 4 / (N : ℝ) ^ 2 * ∑ k ∈ Finset.range N,
      ∑ k' ∈ Finset.range N, ‖Sx c (((k : ℤ) - (k' : ℤ)) * Linv L d) d‖ := ⟨_, rfl⟩
  rw [← hZ]
  have hZ0 : 0 ≤ Z := by
    rw [hZ]
    exact mul_nonneg (by positivity)
      (Finset.sum_nonneg (fun k _ => Finset.sum_nonneg (fun k' _ => norm_nonneg _)))
  have h3 : ∑ j ∈ J, (((rootsMod c d).filter (fun r => jidx L d r = j)).card : ℝ)
      ≤ ∑ _j ∈ J, Z := by
    apply Finset.sum_le_sum
    intro j _
    rw [hZ]
    exact arc_count_le c L d hd hcop N hN hNL j
  rw [Finset.sum_const, nsmul_eq_mul] at h3
  exact h1.trans (h3.trans (mul_le_mul_of_nonneg_right hJcard hZ0))

end reduction



section reductionMain

lemma multiples_sum_le (c : ℤ) (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ3 : ℓ % 3 = 2)
    (hℓc : ¬ (ℓ : ℤ) ∣ 3 * c) (x : ℝ)
    (hs : Summable (fun d : ℕ => (nu c d : ℝ) * (d : ℝ) ^ (-x))) (Y : ℕ) :
    ∑ d ∈ Finset.Icc 1 Y, (if ℓ ∣ d then (nu c d : ℝ) * (d : ℝ) ^ (-x) else 0)
      ≤ (ℓ : ℝ) ^ (-x) * ∑' d : ℕ, (nu c d : ℝ) * (d : ℝ) ^ (-x) := by
  have hnn : ∀ d : ℕ, 0 ≤ (nu c d : ℝ) * (d : ℝ) ^ (-x) :=
    fun d => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hsG : Summable (fun d : ℕ => if ℓ ∣ d then (nu c d : ℝ) * (d : ℝ) ^ (-x) else 0) := by
    refine Summable.of_nonneg_of_le (fun d => ?_) (fun d => ?_) hs
    · split_ifs
      · exact hnn d
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact hnn d
  have hinj : Function.Injective (fun m : ℕ => ℓ * m) :=
    fun a b hab => Nat.eq_of_mul_eq_mul_left hℓ.pos hab
  have hsupp : Function.support (fun d : ℕ => if ℓ ∣ d then (nu c d : ℝ) * (d : ℝ) ^ (-x) else 0)
      ⊆ Set.range (fun m : ℕ => ℓ * m) := by
    intro d hd
    rw [Function.mem_support] at hd
    by_cases hdvd : ℓ ∣ d
    · obtain ⟨m', rfl⟩ := hdvd
      exact ⟨m', rfl⟩
    · rw [if_neg hdvd] at hd
      exact absurd rfl hd
  have h1 : ∑ d ∈ Finset.Icc 1 Y, (if ℓ ∣ d then (nu c d : ℝ) * (d : ℝ) ^ (-x) else 0)
      ≤ ∑' d : ℕ, (if ℓ ∣ d then (nu c d : ℝ) * (d : ℝ) ^ (-x) else 0) :=
    hsG.sum_le_tsum _ (fun d _ => by
      split_ifs
      · exact hnn d
      · exact le_rfl)
  refine h1.trans (le_of_eq ?_)
  rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
  apply tsum_congr
  intro m
  show (if ℓ ∣ ℓ * m then (nu c (ℓ * m) : ℝ) * ((ℓ * m : ℕ) : ℝ) ^ (-x) else 0) = _
  rw [if_pos (dvd_mul_right ℓ m)]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp [nu_zero]
  · rw [nu_two_mul c ℓ m hℓ hℓ3 hℓc hm]
    push_cast
    rw [Real.mul_rpow (Nat.cast_nonneg ℓ) (Nat.cast_nonneg m)]
    ring

open Classical in
/-- **Reduction.** The bad pairs `(d, r)` for fixed `m` and `e` have logarithmic density
zero among the pairs (modulus, cube root of `c`). -/
theorem bad_pairs_bound (c : ℤ) (hc0 : c ≠ 0) (C : ℝ)
    (hC : ∀ y : ℕ, ((Spairs c y).card : ℝ) ≤ C * y)
    (hsplit : ¬ Summable (fun p : ℕ => if Psplit c p then (1 : ℝ) / p else 0))
    (m e : ℤ) (he : e ^ 2 = 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : ℝ, 1 < x → x < 1 + η → ∀ Y : ℕ,
      ∑ d ∈ Finset.Icc 1 Y,
        (((rootsMod c d).filter (badRoot c m e d)).card : ℝ) * (d : ℝ) ^ (-x)
        ≤ ε / (x - 1) := by
  have hC1 : 1 ≤ C := by
    have h1 := hC 1
    rw [card_Spairs_eq] at h1
    simp [nu_one] at h1
    exact h1
  have hCpos : 0 < C := by linarith
  -- number of auxiliary primes
  obtain ⟨n₀, hn₀⟩ := exists_pow_lt_of_lt_one (show (0 : ℝ) < ε / (144 * C) by positivity)
    (show (3 / 5 : ℝ) < 1 by norm_num)
  obtain ⟨n, hndef⟩ : ∃ n : ℕ, n = n₀ + 1 := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by omega
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hpow : (3 / 5 : ℝ) ^ n ≤ ε / (144 * C) := by
    rw [hndef, pow_succ]
    have h1 : (0 : ℝ) ≤ (3 / 5 : ℝ) ^ n₀ := by positivity
    nlinarith
  have hn48 : 48 * C * (3 / 5 : ℝ) ^ n ≤ ε / 3 := by
    have h1 := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ 48 * C)
    have e1 : 48 * C * (ε / (144 * C)) = ε / 3 := by
      field_simp
      ring
    linarith
  -- the auxiliary primes
  obtain ⟨B, hB⟩ : ∃ B : ℕ, B = max (max 5 (3 * c.natAbs)) ⌈6 * n * C / ε⌉₊ := ⟨_, rfl⟩
  obtain ⟨S, hScard, hSp⟩ := exists_primes_two B n
  have hS5 : ∀ ℓ ∈ S, ℓ.Prime ∧ ℓ % 3 = 2 ∧ 5 ≤ ℓ := by
    intro ℓ hℓ
    obtain ⟨h1, h2, h3⟩ := hSp ℓ hℓ
    have h4 : 5 ≤ B := by rw [hB]; exact (le_max_left _ _).trans (le_max_left _ _)
    exact ⟨h1, h2, by omega⟩
  have hS3c : ∀ ℓ ∈ S, ¬ (ℓ : ℤ) ∣ 3 * c := by
    intro ℓ hℓ h
    obtain ⟨_, _, h3⟩ := hSp ℓ hℓ
    have h4 : 3 * c.natAbs ≤ B := by rw [hB]; exact (le_max_right _ _).trans (le_max_left _ _)
    have h5 : ℓ ∣ (3 * c).natAbs := Int.natCast_dvd.mp h
    rw [Int.natAbs_mul] at h5
    have h6 : (3 : ℤ).natAbs = 3 := rfl
    rw [h6] at h5
    have hcpos : 0 < c.natAbs := Int.natAbs_pos.mpr hc0
    have := Nat.le_of_dvd (by omega) h5
    omega
  have hSbig : ∀ ℓ ∈ S, 6 * n * C / ε ≤ ℓ := by
    intro ℓ hℓ
    obtain ⟨_, _, h3⟩ := hSp ℓ hℓ
    have h4 : ⌈6 * n * C / ε⌉₊ ≤ B := by rw [hB]; exact le_max_right _ _
    have h5 : (⌈6 * n * C / ε⌉₊ : ℝ) ≤ ℓ := by exact_mod_cast (h4.trans h3.le)
    exact (Nat.le_ceil _).trans h5
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = ∏ ℓ ∈ S, ℓ := ⟨_, rfl⟩
  have hLpos : 0 < L := by
    rw [hL]
    exact Finset.prod_pos (fun ℓ hℓ => (hS5 ℓ hℓ).1.pos)
  have hL5 : 5 ≤ L := by
    have hne : S.Nonempty := by
      rw [← Finset.card_pos, hScard]
      omega
    obtain ⟨ℓ₀, hℓ₀⟩ := hne
    have h1 : ℓ₀ ∣ L := by rw [hL]; exact Finset.dvd_prod_of_mem _ hℓ₀
    have h2 := Nat.le_of_dvd hLpos h1
    have h3 := (hS5 ℓ₀ hℓ₀).2.2
    omega
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = L / 3 := ⟨_, rfl⟩
  have hN0 : 0 < N := by omega
  have h3N : 3 * N ≤ L := by omega
  have hL6N : L ≤ 6 * N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN0
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hL6NR : (L : ℝ) ≤ 6 * N := by exact_mod_cast hL6N
  obtain ⟨Θ, hΘ⟩ : ∃ Θ : ℝ, Θ = ∏ ℓ ∈ S, (((ℓ : ℝ) + 1) / 2) := ⟨_, rfl⟩
  have hΘ0 : 0 ≤ Θ := by
    rw [hΘ]
    exact Finset.prod_nonneg (fun ℓ _ => by positivity)
  have hΘL : Θ ≤ (3 / 5 : ℝ) ^ n * L := by
    rw [hΘ, hL, ← hScard]
    push_cast
    rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro ℓ _
      positivity
    · intro ℓ hℓ
      have h5 : (5 : ℝ) ≤ ℓ := by exact_mod_cast (hS5 ℓ hℓ).2.2
      linarith
  have hΘleL : Θ ≤ L := by
    have h1 : (3 / 5 : ℝ) ^ n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    nlinarith
  -- the core bounds for the finitely many frequencies
  obtain ⟨ε', hε'⟩ : ∃ ε' : ℝ, ε' = ε / (12 * L) := ⟨_, rfl⟩
  have hε'pos : 0 < ε' := by rw [hε']; positivity
  have hcore : ∀ g : ℤ, ∃ η : ℝ, 0 < η ∧ (g ≠ 0 → ∀ x : ℝ, 1 < x → x < 1 + η → ∀ Y : ℕ,
      ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L),
        ‖Sx c (g * Linv L d) d‖ * (d : ℝ) ^ (-x) ≤ ε' / (x - 1)) := by
    intro g
    by_cases hg : g = 0
    · exact ⟨1, one_pos, fun h => absurd hg h⟩
    · obtain ⟨η, hη, h⟩ := core_bound c hc0 C hC hsplit L hLpos g hg ε' hε'pos
      exact ⟨η, hη, fun _ => h⟩
  choose ηg hηg hηgb using hcore
  have hGne : (Finset.Icc (-(N : ℤ)) N).Nonempty := ⟨0, by
    rw [Finset.mem_Icc]
    constructor <;> omega⟩
  obtain ⟨η₁, hη₁def⟩ : ∃ η₁ : ℝ, η₁ = (Finset.Icc (-(N : ℤ)) N).inf' hGne ηg := ⟨_, rfl⟩
  have hη₁pos : 0 < η₁ := by
    rw [hη₁def, Finset.lt_inf'_iff]
    intro g _
    exact hηg g
  have hη₁le : ∀ g ∈ Finset.Icc (-(N : ℤ)) N, η₁ ≤ ηg g := by
    intro g hg
    rw [hη₁def]
    exact Finset.inf'_le _ hg
  refine ⟨min 1 η₁, lt_min one_pos hη₁pos, ?_⟩
  intro x hx1 hx2 Y
  have hxa : x < 1 + 1 := lt_of_lt_of_le hx2 (by linarith [min_le_left 1 η₁])
  have hxb : x < 1 + η₁ := lt_of_lt_of_le hx2 (by linarith [min_le_right 1 η₁])
  have hxpos : 0 < x - 1 := by linarith
  obtain ⟨hs, hsbound⟩ := nu_series c C hC x hx1 (by linarith)
  obtain ⟨Z, hZ⟩ : ∃ Z : ℝ, Z = ∑' d : ℕ, (nu c d : ℝ) * (d : ℝ) ^ (-x) := ⟨_, rfl⟩
  rw [← hZ] at hsbound
  have hnn : ∀ d : ℕ, 0 ≤ (nu c d : ℝ) * (d : ℝ) ^ (-x) :=
    fun d => mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg d) _)
  have hZ0 : 0 ≤ Z := by rw [hZ]; exact tsum_nonneg hnn
  have hrp0 : ∀ d : ℕ, 0 ≤ (d : ℝ) ^ (-x) := fun d => Real.rpow_nonneg (Nat.cast_nonneg d) _
  -- termwise bound
  have hterm : ∀ d ∈ Finset.Icc 1 Y,
      (((rootsMod c d).filter (badRoot c m e d)).card : ℝ) * (d : ℝ) ^ (-x)
        ≤ (if Nat.Coprime d L then Θ * (4 / (N : ℝ) ^ 2 * ∑ k ∈ Finset.range N,
            ∑ k' ∈ Finset.range N, ‖Sx c (((k : ℤ) - (k' : ℤ)) * Linv L d) d‖) * (d : ℝ) ^ (-x)
          else 0)
          + ∑ ℓ ∈ S, (if ℓ ∣ d then (nu c d : ℝ) * (d : ℝ) ^ (-x) else 0) := by
    intro d hd
    have hd1 := (Finset.mem_Icc.mp hd).1
    have hsecond : 0 ≤ ∑ ℓ ∈ S, (if ℓ ∣ d then (nu c d : ℝ) * (d : ℝ) ^ (-x) else 0) := by
      apply Finset.sum_nonneg
      intro ℓ _
      split_ifs
      · exact hnn d
      · exact le_rfl
    by_cases hcop : Nat.Coprime d L
    · rw [if_pos hcop]
      have h1 := bad_card_le c m e he S hS5 d hd1 (by rw [← hL]; exact hcop.symm) N hN0
        (by rw [← hL]; exact h3N)
      rw [← hL, ← hΘ] at h1
      have h2 := mul_le_mul_of_nonneg_right h1 (hrp0 d)
      linarith
    · rw [if_neg hcop, zero_add]
      have hex : ∃ ℓ ∈ S, ℓ ∣ d := by
        by_contra hne
        push Not at hne
        apply hcop
        rw [hL]
        apply Nat.Coprime.prod_right
        intro ℓ hℓ
        exact ((Nat.Prime.coprime_iff_not_dvd (hS5 ℓ hℓ).1).mpr (hne ℓ hℓ)).symm
      obtain ⟨ℓ, hℓ, hℓd⟩ := hex
      have h1 : (((rootsMod c d).filter (badRoot c m e d)).card : ℝ) ≤ nu c d := by
        unfold nu
        exact_mod_cast Finset.card_filter_le _ _
      have h2 : (nu c d : ℝ) * (d : ℝ) ^ (-x)
          ≤ ∑ ℓ' ∈ S, (if ℓ' ∣ d then (nu c d : ℝ) * (d : ℝ) ^ (-x) else 0) := by
        have h3 : (if ℓ ∣ d then (nu c d : ℝ) * (d : ℝ) ^ (-x) else 0)
            ≤ ∑ ℓ' ∈ S, (if ℓ' ∣ d then (nu c d : ℝ) * (d : ℝ) ^ (-x) else 0) :=
          Finset.single_le_sum
            (f := fun ℓ' : ℕ => (if ℓ' ∣ d then (nu c d : ℝ) * (d : ℝ) ^ (-x) else 0))
            (fun ℓ' _ => by split_ifs <;> first | exact hnn d | exact le_rfl) hℓ
        rwa [if_pos hℓd] at h3
      exact (mul_le_mul_of_nonneg_right h1 (hrp0 d)).trans h2
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib]
  -- second part: moduli divisible by an auxiliary prime
  have hpart2 : ∑ d ∈ Finset.Icc 1 Y, ∑ ℓ ∈ S,
      (if ℓ ∣ d then (nu c d : ℝ) * (d : ℝ) ^ (-x) else 0) ≤ ε / 3 / (x - 1) := by
    rw [Finset.sum_comm]
    have h1 : ∀ ℓ ∈ S, ∑ d ∈ Finset.Icc 1 Y,
        (if ℓ ∣ d then (nu c d : ℝ) * (d : ℝ) ^ (-x) else 0) ≤ ε / (6 * n * C) * Z := by
      intro ℓ hℓ
      obtain ⟨hℓp, hℓ3, hℓ5⟩ := hS5 ℓ hℓ
      have h2 := multiples_sum_le c ℓ hℓp hℓ3 (hS3c ℓ hℓ) x hs Y
      rw [← hZ] at h2
      have hℓR : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓp.one_le
      have h3 : (ℓ : ℝ) ^ (-x) ≤ (ℓ : ℝ) ^ (-1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hℓR (by linarith)
      rw [Real.rpow_neg_one] at h3
      have h4 := hSbig ℓ hℓ
      have h5 : (ℓ : ℝ)⁻¹ ≤ ε / (6 * n * C) := by
        have h6 : 0 < 6 * (n : ℝ) * C / ε := by positivity
        have h7 : (ℓ : ℝ)⁻¹ ≤ (6 * (n : ℝ) * C / ε)⁻¹ := inv_anti₀ h6 h4
        rw [inv_div] at h7
        exact h7
      exact h2.trans (mul_le_mul_of_nonneg_right (h3.trans h5) hZ0)
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_const, hScard, nsmul_eq_mul]
    have h8 : (n : ℝ) * (ε / (6 * n * C) * Z) ≤ (n : ℝ) * (ε / (6 * n * C) * (2 * C / (x - 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsbound (by positivity))
        (by positivity)
    have e1 : (n : ℝ) * (ε / (6 * n * C) * (2 * C / (x - 1))) = ε / 3 / (x - 1) := by
      field_simp
      ring
    linarith
  -- first part: moduli coprime to `L`
  have hpart1 : ∑ d ∈ Finset.Icc 1 Y, (if Nat.Coprime d L then Θ * (4 / (N : ℝ) ^ 2
        * ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N,
          ‖Sx c (((k : ℤ) - (k' : ℤ)) * Linv L d) d‖) * (d : ℝ) ^ (-x) else 0)
      ≤ 2 * ε / 3 / (x - 1) := by
    rw [← Finset.sum_filter]
    have e1 : ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L),
          Θ * (4 / (N : ℝ) ^ 2 * ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N,
            ‖Sx c (((k : ℤ) - (k' : ℤ)) * Linv L d) d‖) * (d : ℝ) ^ (-x)
        = Θ * (4 / (N : ℝ) ^ 2) * ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N,
            ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L),
              ‖Sx c (((k : ℤ) - (k' : ℤ)) * Linv L d) d‖ * (d : ℝ) ^ (-x) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun k' _ => ?_)
      refine Finset.sum_congr rfl (fun d _ => ?_)
      ring
    rw [e1]
    have hkk : ∀ k ∈ Finset.range N, ∀ k' ∈ Finset.range N,
        ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L),
          ‖Sx c (((k : ℤ) - (k' : ℤ)) * Linv L d) d‖ * (d : ℝ) ^ (-x)
        ≤ (if k = k' then 2 * C / (x - 1) else 0) + ε' / (x - 1) := by
      intro k hk k' hk'
      have hεx : 0 ≤ ε' / (x - 1) := by positivity
      by_cases hkk' : k = k'
      · rw [if_pos hkk']
        have h1 : ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L),
            ‖Sx c (((k : ℤ) - (k' : ℤ)) * Linv L d) d‖ * (d : ℝ) ^ (-x)
            ≤ ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L),
              (nu c d : ℝ) * (d : ℝ) ^ (-x) :=
          Finset.sum_le_sum (fun d _ =>
            mul_le_mul_of_nonneg_right (norm_Sx_le c _ d) (hrp0 d))
        have h2 : ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L),
            (nu c d : ℝ) * (d : ℝ) ^ (-x) ≤ Z := by
          rw [hZ]
          exact hs.sum_le_tsum _ (fun d _ => hnn d)
        linarith
      · rw [if_neg hkk', zero_add]
        have hg : ((k : ℤ) - (k' : ℤ)) ≠ 0 := by
          intro h
          apply hkk'
          omega
        have hgmem : ((k : ℤ) - (k' : ℤ)) ∈ Finset.Icc (-(N : ℤ)) N := by
          have h1 := Finset.mem_range.mp hk
          have h2 := Finset.mem_range.mp hk'
          rw [Finset.mem_Icc]
          constructor <;> omega
        exact hηgb _ hg x hx1 (lt_of_lt_of_le hxb (by linarith [hη₁le _ hgmem])) Y
    have hsum : ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N,
          ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L),
            ‖Sx c (((k : ℤ) - (k' : ℤ)) * Linv L d) d‖ * (d : ℝ) ^ (-x)
        ≤ (N : ℝ) * (2 * C / (x - 1)) + (N : ℝ) * ((N : ℝ) * (ε' / (x - 1))) := by
      calc ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N,
            ∑ d ∈ (Finset.Icc 1 Y).filter (fun d => Nat.Coprime d L),
              ‖Sx c (((k : ℤ) - (k' : ℤ)) * Linv L d) d‖ * (d : ℝ) ^ (-x)
          ≤ ∑ k ∈ Finset.range N, ∑ k' ∈ Finset.range N,
              ((if k = k' then 2 * C / (x - 1) else 0) + ε' / (x - 1)) :=
            Finset.sum_le_sum (fun k hk => Finset.sum_le_sum (fun k' hk' => hkk k hk k' hk'))
        _ = ∑ k ∈ Finset.range N, (2 * C / (x - 1) + (N : ℝ) * (ε' / (x - 1))) := by
            apply Finset.sum_congr rfl
            intro k hk
            rw [Finset.sum_add_distrib, Finset.sum_ite_eq, if_pos hk, Finset.sum_const,
              Finset.card_range, nsmul_eq_mul]
        _ = (N : ℝ) * (2 * C / (x - 1)) + (N : ℝ) * ((N : ℝ) * (ε' / (x - 1))) := by
            rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            ring
    have hcoef : 0 ≤ Θ * (4 / (N : ℝ) ^ 2) := by positivity
    refine (mul_le_mul_of_nonneg_left hsum hcoef).trans ?_
    have e2 : Θ * (4 / (N : ℝ) ^ 2) * ((N : ℝ) * (2 * C / (x - 1))
          + (N : ℝ) * ((N : ℝ) * (ε' / (x - 1))))
        = (8 * C * (Θ / N) + 4 * Θ * ε') / (x - 1) := by
      field_simp
      ring
    rw [e2]
    have h1 : Θ / N ≤ 6 * (3 / 5 : ℝ) ^ n := by
      rw [div_le_iff₀ hNR]
      have h2 : (3 / 5 : ℝ) ^ n * L ≤ (3 / 5 : ℝ) ^ n * (6 * N) :=
        mul_le_mul_of_nonneg_left hL6NR (by positivity)
      linarith
    have h3 : 8 * C * (Θ / N) ≤ ε / 3 := by
      have h4 : 8 * C * (Θ / N) ≤ 8 * C * (6 * (3 / 5 : ℝ) ^ n) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    have h5 : 4 * Θ * ε' ≤ ε / 3 := by
      have h6 : 4 * Θ * ε' ≤ 4 * L * ε' := by
        have := mul_le_mul_of_nonneg_right hΘleL hε'pos.le
        linarith
      have e3 : 4 * (L : ℝ) * ε' = ε / 3 := by
        rw [hε']
        field_simp
        ring
      linarith
    have h7 : (8 * C * (Θ / N) + 4 * Θ * ε') / (x - 1) ≤ (ε / 3 + ε / 3) / (x - 1) :=
      div_le_div_of_nonneg_right (by linarith) hxpos.le
    have e4 : (ε / 3 + ε / 3) / (x - 1) = 2 * ε / 3 / (x - 1) := by ring
    linarith
  have e5 : 2 * ε / 3 / (x - 1) + ε / 3 / (x - 1) = ε / (x - 1) := by
    field_simp
    ring
  linarith

end reductionMain



section blocks

/-- Lower bound for a Dirichlet-type sum from lower bounds of the partial sums on a geometric
sequence of scales (a substitute for Abel summation). -/
lemma blocks_lower (b : ℕ → ℝ) (hb : ∀ d, 0 ≤ b d) (U κ : ℝ) (hκ : 0 < κ) (Λ : ℕ) (hΛ : 2 ≤ Λ)
    (hΛU : 2 * κ * U ≤ Λ) (i₀ : ℕ)
    (hU : ∀ Y : ℕ, ∑ d ∈ Finset.Icc 1 Y, b d ≤ U * Y)
    (hLo : ∀ i : ℕ, i₀ ≤ i → (Λ : ℝ) ^ i / κ ≤ ∑ d ∈ Finset.Icc 1 (Λ ^ i), b d)
    (Mf : ℕ) (hMf : 0 < Mf) :
    ∀ M : ℕ, i₀ ≤ M → M ≤ Mf →
      ((M : ℝ) - i₀) / (2 * κ * Λ)
        ≤ ∑ d ∈ Finset.Icc 1 (Λ ^ M), b d * (d : ℝ) ^ (-(1 + 1 / (Mf : ℝ))) := by
  have hΛR : (2 : ℝ) ≤ Λ := by exact_mod_cast hΛ
  have hΛpos : (0 : ℝ) < Λ := by linarith
  have hMfR : (0 : ℝ) < Mf := by exact_mod_cast hMf
  intro M hM
  induction M, hM using Nat.le_induction with
  | base =>
    intro _
    rw [sub_self, zero_div]
    exact Finset.sum_nonneg
      (fun d _ => mul_nonneg (hb d) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
  | succ M hM ih =>
    intro hMf'
    have ih' := ih (by omega)
    have hle : Λ ^ M ≤ Λ ^ (M + 1) := Nat.pow_le_pow_right (by omega) (by omega)
    have h1 : 1 ≤ Λ ^ M := Nat.one_le_pow _ _ (by omega)
    have hsplit : Finset.Icc 1 (Λ ^ (M + 1))
        = Finset.Icc 1 (Λ ^ M) ∪ Finset.Ioc (Λ ^ M) (Λ ^ (M + 1)) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
      omega
    have hdisj : Disjoint (Finset.Icc 1 (Λ ^ M)) (Finset.Ioc (Λ ^ M) (Λ ^ (M + 1))) := by
      rw [Finset.disjoint_left]
      intro d h2 h3
      rw [Finset.mem_Icc] at h2
      rw [Finset.mem_Ioc] at h3
      omega
    have hY : (0 : ℝ) < (Λ : ℝ) ^ (M + 1) := by positivity
    have hYcast : (((Λ ^ (M + 1) : ℕ)) : ℝ) = (Λ : ℝ) ^ (M + 1) := by push_cast; rfl
    have hblock : 1 / (2 * κ * Λ) ≤ ∑ d ∈ Finset.Ioc (Λ ^ M) (Λ ^ (M + 1)),
        b d * (d : ℝ) ^ (-(1 + 1 / (Mf : ℝ))) := by
      have hxneg : -(1 + 1 / (Mf : ℝ)) ≤ 0 := by
        have : 0 < 1 / (Mf : ℝ) := by positivity
        linarith
      have h2 : ∑ d ∈ Finset.Ioc (Λ ^ M) (Λ ^ (M + 1)),
            b d * ((Λ : ℝ) ^ (M + 1)) ^ (-(1 + 1 / (Mf : ℝ)))
          ≤ ∑ d ∈ Finset.Ioc (Λ ^ M) (Λ ^ (M + 1)), b d * (d : ℝ) ^ (-(1 + 1 / (Mf : ℝ))) := by
        apply Finset.sum_le_sum
        intro d hd
        obtain ⟨hd1, hd2⟩ := Finset.mem_Ioc.mp hd
        apply mul_le_mul_of_nonneg_left _ (hb d)
        have hdpos : (0 : ℝ) < d := by
          have : 0 < d := by omega
          exact_mod_cast this
        have hdle : (d : ℝ) ≤ (Λ : ℝ) ^ (M + 1) := by
          rw [← hYcast]
          exact_mod_cast hd2
        exact Real.rpow_le_rpow_of_nonpos hdpos hdle hxneg
      have h3 : ∑ d ∈ Finset.Ioc (Λ ^ M) (Λ ^ (M + 1)), b d
          = ∑ d ∈ Finset.Icc 1 (Λ ^ (M + 1)), b d - ∑ d ∈ Finset.Icc 1 (Λ ^ M), b d := by
        rw [hsplit, Finset.sum_union hdisj]
        ring
      have h4 := hLo (M + 1) (by omega)
      have h5 := hU (Λ ^ M)
      have h6 : (Λ : ℝ) ^ (M + 1) / (2 * κ) ≤ ∑ d ∈ Finset.Ioc (Λ ^ M) (Λ ^ (M + 1)), b d := by
        rw [h3]
        have h7 : U * ((Λ ^ M : ℕ) : ℝ) ≤ (Λ : ℝ) ^ (M + 1) / (2 * κ) := by
          push_cast
          rw [pow_succ, le_div_iff₀ (by positivity)]
          have h8 : (0 : ℝ) ≤ (Λ : ℝ) ^ M := by positivity
          nlinarith
        have e : (Λ : ℝ) ^ (M + 1) / κ
            = (Λ : ℝ) ^ (M + 1) / (2 * κ) + (Λ : ℝ) ^ (M + 1) / (2 * κ) := by
          field_simp
          ring
        linarith
      have h8 : ((Λ : ℝ) ^ (M + 1))⁻¹ * (Λ : ℝ)⁻¹
          ≤ ((Λ : ℝ) ^ (M + 1)) ^ (-(1 + 1 / (Mf : ℝ))) := by
        have hx : -(1 + 1 / (Mf : ℝ)) = -1 + -(1 / (Mf : ℝ)) := by ring
        rw [hx, Real.rpow_add hY, Real.rpow_neg_one]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [← Real.rpow_natCast, ← Real.rpow_mul hΛpos.le, ← Real.rpow_neg_one]
        apply Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ Λ)
        have h9 : ((M + 1 : ℕ) : ℝ) ≤ Mf := by exact_mod_cast hMf'
        have h10 : ((M + 1 : ℕ) : ℝ) * (1 / (Mf : ℝ)) ≤ 1 := by
          rw [mul_one_div, div_le_one hMfR]
          exact h9
        linarith
      have hsum0 : 0 ≤ ∑ d ∈ Finset.Ioc (Λ ^ M) (Λ ^ (M + 1)), b d :=
        Finset.sum_nonneg (fun d _ => hb d)
      calc 1 / (2 * κ * Λ)
          = ((Λ : ℝ) ^ (M + 1) / (2 * κ)) * (((Λ : ℝ) ^ (M + 1))⁻¹ * (Λ : ℝ)⁻¹) := by
            field_simp
        _ ≤ (∑ d ∈ Finset.Ioc (Λ ^ M) (Λ ^ (M + 1)), b d)
              * ((Λ : ℝ) ^ (M + 1)) ^ (-(1 + 1 / (Mf : ℝ))) :=
            mul_le_mul h6 h8 (by positivity) hsum0
        _ = ∑ d ∈ Finset.Ioc (Λ ^ M) (Λ ^ (M + 1)),
              b d * ((Λ : ℝ) ^ (M + 1)) ^ (-(1 + 1 / (Mf : ℝ))) := Finset.sum_mul _ _ _
        _ ≤ _ := h2
    rw [hsplit, Finset.sum_union hdisj]
    have e : (((M + 1 : ℕ) : ℝ) - i₀) / (2 * κ * Λ)
        = ((M : ℝ) - i₀) / (2 * κ * Λ) + 1 / (2 * κ * Λ) := by
      push_cast
      ring
    rw [e]
    linarith

end blocks



section largeBad

open Classical in
/-- Number of bad pairs `(d, r)` with `d ≤ Y`, for given `m` and `e`. -/
noncomputable def Nbad (c m e : ℤ) (Y : ℕ) : ℕ :=
  ∑ d ∈ Finset.Icc 1 Y, ((rootsMod c d).filter (badRoot c m e d)).card

lemma largeBad_data (c : ℤ) (hc : ¬ ∃ m : ℤ, m ^ 3 = c) (T A : ℕ) (hA : 0 < A)
    (hT : c.natAbs ≤ T ^ 3) (t : ℤ) (ht : t ∈ LargeBad c T A) :
    ∃ (m e : ℤ) (d r : ℕ), m ∈ Finset.Icc (-(A : ℤ)) A ∧ e ∈ ({1, -1} : Finset ℤ)
      ∧ d ∈ Finset.Icc 1 (2 * T) ∧ r ∈ rootsMod c d ∧ badRoot c m e d r
      ∧ t = (r : ℤ) + (d : ℤ) * m := by
  classical
  unfold LargeBad at ht
  obtain ⟨htI, d, s, hDd, hdvd, heq⟩ := Finset.mem_filter.mp ht
  obtain ⟨ht1, ht2⟩ := Finset.mem_Icc.mp htI
  have hN : c - t ^ 3 ≠ 0 := fun h0 => hc ⟨t, by linarith⟩
  have hD0 : (0 : ℤ) ≤ ((T / A : ℕ) : ℤ) := Int.natCast_nonneg _
  have hdpos : 0 < d := by linarith
  -- the sign
  obtain ⟨e, he1, he2⟩ : ∃ e : ℤ, e ∈ ({1, -1} : Finset ℤ) ∧ e * (c - t ^ 3) = |c - t ^ 3| := by
    rcases lt_or_gt_of_ne hN with h | h
    · exact ⟨-1, by simp, by rw [abs_of_neg h]; ring⟩
    · exact ⟨1, by simp, by rw [abs_of_pos h]; ring⟩
  -- naturals
  obtain ⟨d', hd'⟩ : ∃ d' : ℕ, (d' : ℤ) = d := ⟨d.toNat, Int.toNat_of_nonneg hdpos.le⟩
  have hr0 : 0 ≤ t % d := Int.emod_nonneg _ hdpos.ne'
  have hrlt : t % d < d := Int.emod_lt_of_pos _ hdpos
  obtain ⟨r', hr'⟩ : ∃ r' : ℕ, (r' : ℤ) = t % d := ⟨(t % d).toNat, Int.toNat_of_nonneg hr0⟩
  have ht_eq : t = (r' : ℤ) + (d' : ℤ) * (t / d) := by
    rw [hr', hd', Int.emod_def]
    ring
  have hd'pos : 0 < d' := by
    have : (0 : ℤ) < (d' : ℤ) := by rw [hd']; exact hdpos
    exact_mod_cast this
  have hr'lt : r' < d' := by
    have : (r' : ℤ) < (d' : ℤ) := by rw [hr', hd']; exact hrlt
    exact_mod_cast this
  -- size of d
  have habs_t : |t| ≤ (T : ℤ) := abs_le.mpr ⟨ht1, ht2⟩
  have hcabs : |c| ≤ ((T ^ 3 : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hT
  have hNabs : |c - t ^ 3| ≤ 2 * (T : ℤ) ^ 3 := by
    have h1 : |c - t ^ 3| ≤ |c| + |t ^ 3| := abs_sub _ _
    have h2 : |t ^ 3| ≤ (T : ℤ) ^ 3 := by
      rw [abs_pow]
      exact pow_le_pow_left₀ (abs_nonneg t) habs_t 3
    push_cast at hcabs
    linarith
  have hd3 : d ^ 3 ≤ (2 * (T : ℤ)) ^ 3 := by
    have h1 : d ^ 3 ≤ d * (d ^ 2 + 3 * s ^ 2) := by nlinarith [sq_nonneg s, hdpos]
    have h2 : (2 * (T : ℤ)) ^ 3 = 4 * (2 * (T : ℤ) ^ 3) := by ring
    rw [h2]
    linarith
  have hd2T : d ≤ 2 * (T : ℤ) := by
    by_contra hcon
    push Not at hcon
    have h1 : (2 * (T : ℤ)) ^ 3 < d ^ 3 :=
      pow_lt_pow_left₀ hcon (by positivity) (by norm_num)
    linarith
  have hd'2T : d' ≤ 2 * T := by
    have : (d' : ℤ) ≤ 2 * (T : ℤ) := by rw [hd']; exact hd2T
    exact_mod_cast this
  -- size of m
  have hTA : (T : ℤ) < d * A := by
    have h1 : T < A * (T / A) + A := by
      have h2 := Nat.div_add_mod T A
      have h3 := Nat.mod_lt T hA
      omega
    have h4 : (T : ℤ) < (A : ℤ) * ((T / A : ℕ) : ℤ) + A := by exact_mod_cast h1
    have h5 : ((T / A : ℕ) : ℤ) + 1 ≤ d := by linarith
    have hA' : (0 : ℤ) < A := by exact_mod_cast hA
    nlinarith
  have hm1 : -(A : ℤ) ≤ t / d := by
    apply Int.le_ediv_of_mul_le hdpos
    nlinarith
  have hm2 : t / d ≤ (A : ℤ) := by
    have h1 : t / d < (A : ℤ) := by
      apply Int.ediv_lt_of_lt_mul hdpos
      nlinarith
    exact h1.le
  refine ⟨t / d, e, d', r', Finset.mem_Icc.mpr ⟨hm1, hm2⟩, he1,
    Finset.mem_Icc.mpr ⟨hd'pos, hd'2T⟩, ?_, ?_, ht_eq⟩
  · rw [mem_rootsMod]
    refine ⟨hr'lt, ?_⟩
    rw [hd']
    have h1 : d ∣ t ^ 3 - c := by
      have := dvd_neg.mpr hdvd
      have e1 : -(c - t ^ 3) = t ^ 3 - c := by ring
      rwa [e1] at this
    have h2 : d ∣ t - (r' : ℤ) := by
      rw [hr', Int.emod_def]
      exact ⟨t / d, by ring⟩
    exact (dvd_cube_sub_congr d t r' c h2).mp h1
  · refine ⟨s, ?_⟩
    rw [← ht_eq, hd']
    have e1 : 4 * e * (c - t ^ 3) = 4 * (e * (c - t ^ 3)) := by ring
    rw [e1, he2]
    exact heq

open Classical in
/-- The bad shifts with a large divisor inject into the bad pairs. -/
lemma largeBad_card_le (c : ℤ) (hc : ¬ ∃ m : ℤ, m ^ 3 = c) (T A : ℕ) (hA : 0 < A)
    (hT : c.natAbs ≤ T ^ 3) :
    (LargeBad c T A).card
      ≤ ∑ m ∈ Finset.Icc (-(A : ℤ)) A, ∑ e ∈ ({1, -1} : Finset ℤ), Nbad c m e (2 * T) := by
  have hdata := largeBad_data c hc T A hA hT
  choose! fm fe fd fr hf using hdata
  have hcard : ((Finset.Icc (-(A : ℤ)) A).sigma (fun m => ({1, -1} : Finset ℤ).sigma
      (fun e => (Finset.Icc 1 (2 * T)).sigma
        (fun d => (rootsMod c d).filter (badRoot c m e d))))).card
      = ∑ m ∈ Finset.Icc (-(A : ℤ)) A, ∑ e ∈ ({1, -1} : Finset ℤ), Nbad c m e (2 * T) := by
    simp only [Finset.card_sigma, Nbad]
  rw [← hcard]
  apply Finset.card_le_card_of_injOn
    (fun t => (⟨fm t, ⟨fe t, ⟨fd t, fr t⟩⟩⟩ : Σ _ : ℤ, Σ _ : ℤ, Σ _ : ℕ, ℕ))
  · intro t ht
    have h := hf t (Finset.mem_coe.mp ht)
    rw [Finset.mem_coe, Finset.mem_sigma, Finset.mem_sigma, Finset.mem_sigma, Finset.mem_filter]
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  · intro t ht t' ht' h
    have h1 := (hf t (Finset.mem_coe.mp ht)).2.2.2.2.2
    have h2 := (hf t' (Finset.mem_coe.mp ht')).2.2.2.2.2
    simp only [Sigma.mk.injEq, heq_eq_eq] at h
    obtain ⟨hm, _, hd, hr⟩ := h
    rw [h1, h2, hm, hd, hr]

end largeBad



section goodT

open Classical in
lemma bc_dirichlet (c : ℤ) (hc0 : c ≠ 0) (Cc : ℝ)
    (hCc : ∀ y : ℕ, ((Spairs c y).card : ℝ) ≤ Cc * y)
    (hsplit : ¬ Summable (fun p : ℕ => if Psplit c p then (1 : ℝ) / p else 0))
    (A : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ η : ℝ, 0 < η ∧ ∀ x : ℝ, 1 < x → x < 1 + η → ∀ Y : ℕ,
      ∑ d ∈ Finset.Icc 1 Y, (∑ m ∈ Finset.Icc (-(A : ℤ)) A, ∑ e ∈ ({1, -1} : Finset ℤ),
          (((rootsMod c d).filter (badRoot c m e d)).card : ℝ)) * (d : ℝ) ^ (-x)
        ≤ (∑ _m ∈ Finset.Icc (-(A : ℤ)) A, ∑ _e ∈ ({1, -1} : Finset ℤ), (1 : ℝ))
          * (ε / (x - 1)) := by
  have hall : ∀ m e : ℤ, ∃ η : ℝ, 0 < η ∧ (e ^ 2 = 1 → ∀ x : ℝ, 1 < x → x < 1 + η → ∀ Y : ℕ,
      ∑ d ∈ Finset.Icc 1 Y,
        (((rootsMod c d).filter (badRoot c m e d)).card : ℝ) * (d : ℝ) ^ (-x)
        ≤ ε / (x - 1)) := by
    intro m e
    by_cases he : e ^ 2 = 1
    · obtain ⟨η, hη, h⟩ := bad_pairs_bound c hc0 Cc hCc hsplit m e he ε hε
      exact ⟨η, hη, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h he⟩
  choose ηf hηf hηfb using hall
  have hne : ((Finset.Icc (-(A : ℤ)) A) ×ˢ ({1, -1} : Finset ℤ)).Nonempty :=
    ⟨(0, 1), by
      rw [Finset.mem_product, Finset.mem_Icc]
      refine ⟨⟨by omega, by omega⟩, by simp⟩⟩
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = ((Finset.Icc (-(A : ℤ)) A) ×ˢ ({1, -1} : Finset ℤ)).inf' hne
      (fun p => ηf p.1 p.2) := ⟨_, rfl⟩
  have hηpos : 0 < η := by
    rw [hηdef, Finset.lt_inf'_iff]
    intro p _
    exact hηf p.1 p.2
  have hηle : ∀ m ∈ Finset.Icc (-(A : ℤ)) A, ∀ e ∈ ({1, -1} : Finset ℤ), η ≤ ηf m e := by
    intro m hm e he
    rw [hηdef]
    have hmem : (m, e) ∈ (Finset.Icc (-(A : ℤ)) A) ×ˢ ({1, -1} : Finset ℤ) :=
      Finset.mem_product.mpr ⟨hm, he⟩
    exact Finset.inf'_le (fun p : ℤ × ℤ => ηf p.1 p.2) hmem
  refine ⟨η, hηpos, ?_⟩
  intro x hx1 hx2 Y
  have e1 : ∑ d ∈ Finset.Icc 1 Y, (∑ m ∈ Finset.Icc (-(A : ℤ)) A, ∑ e ∈ ({1, -1} : Finset ℤ),
        (((rootsMod c d).filter (badRoot c m e d)).card : ℝ)) * (d : ℝ) ^ (-x)
      = ∑ m ∈ Finset.Icc (-(A : ℤ)) A, ∑ e ∈ ({1, -1} : Finset ℤ), ∑ d ∈ Finset.Icc 1 Y,
          (((rootsMod c d).filter (badRoot c m e d)).card : ℝ) * (d : ℝ) ^ (-x) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_comm]
  rw [e1, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m hm
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro e he
  rw [one_mul]
  have he2 : e ^ 2 = 1 := by
    rcases Finset.mem_insert.mp he with h | h
    · rw [h]; norm_num
    · rw [Finset.mem_singleton.mp h]; norm_num
  exact hηfb m e he2 x hx1 (lt_of_lt_of_le hx2 (by linarith [hηle m hm e he])) Y

open Classical in
/-- **Final analytic statement.** For finitely many non-cubes simultaneously, some `T` has
few bad shifts with a large divisor. -/
theorem exists_good_T (C : Finset ℤ) (hC : ∀ c ∈ C, ¬ ∃ m : ℤ, m ^ 3 = c) (A : ℤ → ℕ)
    (hA : ∀ c ∈ C, 0 < A c) (k : ℕ) (hk : 0 < k)
    (hMV : ∀ c ∈ C, ∃ Cc : ℝ, ∀ y : ℕ, ((Spairs c y).card : ℝ) ≤ Cc * y)
    (hsplit : ∀ c ∈ C, ¬ Summable (fun p : ℕ => if Psplit c p then (1 : ℝ) / p else 0)) :
    ∃ T : ℕ, 0 < T ∧ k * ∑ c ∈ C, (LargeBad c T (A c)).card ≤ T := by
  by_contra hcon
  push Not at hcon
  have hc0 : ∀ c ∈ C, c ≠ 0 := by
    intro c hc h0
    exact hC c hc ⟨0, by rw [h0]; ring⟩
  -- constants from the mean value theorem
  have hMV' : ∀ c : ℤ, ∃ Cc : ℝ, ∀ y : ℕ, c ∈ C → ((Spairs c y).card : ℝ) ≤ Cc * y := by
    intro c
    by_cases hc : c ∈ C
    · obtain ⟨Cc, h⟩ := hMV c hc
      exact ⟨Cc, fun y _ => h y⟩
    · exact ⟨0, fun _ h => absurd h hc⟩
  choose Cf hCf' using hMV'
  have hCf : ∀ c ∈ C, ∀ y : ℕ, ((Spairs c y).card : ℝ) ≤ Cf c * y :=
    fun c hc y => hCf' c y hc
  have hCf0 : ∀ c ∈ C, 0 ≤ Cf c := by
    intro c hc
    have h1 := hCf c hc 1
    have h2 : (0 : ℝ) ≤ ((Spairs c 1).card : ℝ) := Nat.cast_nonneg _
    simp only [Nat.cast_one, mul_one] at h1
    linarith
  -- the weights
  obtain ⟨bc, hbc⟩ : ∃ bc : ℤ → ℕ → ℝ, bc = fun c d =>
      ∑ m ∈ Finset.Icc (-(A c : ℤ)) (A c), ∑ e ∈ ({1, -1} : Finset ℤ),
        (((rootsMod c d).filter (badRoot c m e d)).card : ℝ) := ⟨_, rfl⟩
  have hbca : ∀ c d, bc c d = ∑ m ∈ Finset.Icc (-(A c : ℤ)) (A c), ∑ e ∈ ({1, -1} : Finset ℤ),
      (((rootsMod c d).filter (badRoot c m e d)).card : ℝ) := fun _ _ => by rw [hbc]
  have hbc0 : ∀ c d, 0 ≤ bc c d := by
    intro c d
    rw [hbca]
    exact Finset.sum_nonneg (fun m _ => Finset.sum_nonneg (fun e _ => Nat.cast_nonneg _))
  obtain ⟨b, hb⟩ : ∃ b : ℕ → ℝ, b = fun d => ∑ c ∈ C, bc c d := ⟨_, rfl⟩
  have hba : ∀ d, b d = ∑ c ∈ C, bc c d := fun _ => by rw [hb]
  have hb0 : ∀ d, 0 ≤ b d := by
    intro d
    rw [hba]
    exact Finset.sum_nonneg (fun c _ => hbc0 c d)
  obtain ⟨Jc, hJc⟩ : ∃ Jc : ℤ → ℝ, Jc = fun c =>
      ∑ _m ∈ Finset.Icc (-(A c : ℤ)) (A c), ∑ _e ∈ ({1, -1} : Finset ℤ), (1 : ℝ) := ⟨_, rfl⟩
  have hJca : ∀ c, Jc c = ∑ _m ∈ Finset.Icc (-(A c : ℤ)) (A c),
      ∑ _e ∈ ({1, -1} : Finset ℤ), (1 : ℝ) := fun _ => by rw [hJc]
  have hJc0 : ∀ c, 0 ≤ Jc c := by
    intro c
    rw [hJca]
    exact Finset.sum_nonneg (fun m _ => Finset.sum_nonneg (fun e _ => zero_le_one))
  obtain ⟨J, hJ⟩ : ∃ J : ℝ, J = ∑ c ∈ C, Jc c := ⟨_, rfl⟩
  have hJ0 : 0 ≤ J := by rw [hJ]; exact Finset.sum_nonneg (fun c _ => hJc0 c)
  obtain ⟨U, hU⟩ : ∃ U : ℝ, U = ∑ c ∈ C, Jc c * Cf c := ⟨_, rfl⟩
  have hU0 : 0 ≤ U := by
    rw [hU]
    exact Finset.sum_nonneg (fun c hc => mul_nonneg (hJc0 c) (hCf0 c hc))
  -- partial sums of `bc` in terms of `Nbad`
  have hpart : ∀ c (Y : ℕ), ∑ d ∈ Finset.Icc 1 Y, bc c d
      = ∑ m ∈ Finset.Icc (-(A c : ℤ)) (A c), ∑ e ∈ ({1, -1} : Finset ℤ),
          (Nbad c m e Y : ℝ) := by
    intro c Y
    simp only [hbca, Nbad]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    push_cast
    rfl
  -- upper bound for the partial sums
  have hUb : ∀ Y : ℕ, ∑ d ∈ Finset.Icc 1 Y, b d ≤ U * Y := by
    intro Y
    simp only [hba]
    rw [Finset.sum_comm, hU, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro c hc
    rw [hpart c Y, hJca, Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro m _
    rw [Finset.sum_mul, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro e _
    rw [one_mul]
    have h1 : (Nbad c m e Y : ℝ) ≤ ((Spairs c Y).card : ℝ) := by
      rw [card_Spairs_eq]
      unfold Nbad nu
      exact_mod_cast Finset.sum_le_sum (fun d _ => Finset.card_filter_le _ _)
    exact h1.trans (hCf c hc Y)
  -- large-bad shifts are counted by the partial sums at `2 T`
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : ℕ, T₁ = ∑ c ∈ C, c.natAbs + 1 := ⟨_, rfl⟩
  have hLB : ∀ T : ℕ, T₁ ≤ T →
      ((∑ c ∈ C, (LargeBad c T (A c)).card : ℕ) : ℝ) ≤ ∑ d ∈ Finset.Icc 1 (2 * T), b d := by
    intro T hT
    simp only [hba]
    rw [Finset.sum_comm]
    push_cast
    apply Finset.sum_le_sum
    intro c hc
    rw [hpart c (2 * T)]
    have hnat : c.natAbs ≤ T ^ 3 := by
      have h1 : c.natAbs ≤ ∑ c' ∈ C, c'.natAbs :=
        Finset.single_le_sum (f := fun c' : ℤ => c'.natAbs) (fun _ _ => Nat.zero_le _) hc
      have h2 : T ≤ T ^ 3 := by
        have hT1 : 1 ≤ T := by omega
        calc T = T ^ 1 := (pow_one T).symm
          _ ≤ T ^ 3 := Nat.pow_le_pow_right hT1 (by norm_num)
      omega
    have h3 := largeBad_card_le c (hC c hc) T (A c) (hA c hc) hnat
    exact_mod_cast h3
  -- parameters
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = 2 * (k : ℝ) := ⟨_, rfl⟩
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hκpos : 0 < κ := by rw [hκ]; positivity
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℕ, Λ = 2 * (⌈2 * κ * U⌉₊ + 1) := ⟨_, rfl⟩
  have hΛ2 : 2 ≤ Λ := by omega
  have hΛU : 2 * κ * U ≤ Λ := by
    have h1 : 2 * κ * U ≤ (⌈2 * κ * U⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈2 * κ * U⌉₊ : ℕ) : ℝ) ≤ (Λ : ℝ) := by
      have : ⌈2 * κ * U⌉₊ ≤ Λ := by omega
      exact_mod_cast this
    linarith
  have hΛR : (2 : ℝ) ≤ Λ := by exact_mod_cast hΛ2
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ℕ, i₀ = T₁ + 1 := ⟨_, rfl⟩
  have hLo : ∀ i : ℕ, i₀ ≤ i → (Λ : ℝ) ^ i / κ ≤ ∑ d ∈ Finset.Icc 1 (Λ ^ i), b d := by
    intro i hi
    have hi1 : 1 ≤ i := by omega
    obtain ⟨T, hTdef⟩ : ∃ T : ℕ, T = (⌈2 * κ * U⌉₊ + 1) * Λ ^ (i - 1) := ⟨_, rfl⟩
    have h2T : 2 * T = Λ ^ i := by
      rw [hTdef, ← mul_assoc, ← hΛ]
      have : Λ ^ i = Λ * Λ ^ (i - 1) := by
        rw [← pow_succ', Nat.sub_add_cancel hi1]
      rw [this]
    have hTbig : T₁ ≤ T := by
      have h1 : i - 1 < 2 ^ (i - 1) := Nat.lt_two_pow_self
      have h2 : 2 ^ (i - 1) ≤ Λ ^ (i - 1) := Nat.pow_le_pow_left hΛ2 _
      have h3 : Λ ^ (i - 1) ≤ T := by
        rw [hTdef]
        exact Nat.le_mul_of_pos_left _ (by omega)
      omega
    have hTpos : 0 < T := by omega
    have h4 := hcon T hTpos
    have h5 := hLB T hTbig
    rw [h2T] at h5
    have h6 : (T : ℝ) < (k : ℝ) * ((∑ c ∈ C, (LargeBad c T (A c)).card : ℕ) : ℝ) := by
      exact_mod_cast h4
    have h7 : (T : ℝ) < (k : ℝ) * ∑ d ∈ Finset.Icc 1 (Λ ^ i), b d :=
      lt_of_lt_of_le h6 (mul_le_mul_of_nonneg_left h5 hkR.le)
    have h8 : (Λ : ℝ) ^ i = 2 * (T : ℝ) := by
      have : ((Λ ^ i : ℕ) : ℝ) = ((2 * T : ℕ) : ℝ) := by rw [h2T]
      push_cast at this
      exact this
    rw [h8, hκ, div_le_iff₀ (by positivity)]
    linarith
  -- the Dirichlet bound
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = 1 / (8 * κ * Λ * (J + 1)) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by rw [hε]; positivity
  have hdir : ∀ c : ℤ, ∃ η : ℝ, 0 < η ∧ (c ∈ C → ∀ x : ℝ, 1 < x → x < 1 + η → ∀ Y : ℕ,
      ∑ d ∈ Finset.Icc 1 Y, bc c d * (d : ℝ) ^ (-x) ≤ Jc c * (ε / (x - 1))) := by
    intro c
    by_cases hc : c ∈ C
    · obtain ⟨η, hη, h⟩ := bc_dirichlet c (hc0 c hc) (Cf c) (hCf c hc) (hsplit c hc) (A c) ε hεpos
      refine ⟨η, hη, fun _ x hx1 hx2 Y => ?_⟩
      have := h x hx1 hx2 Y
      simp only [hbca, hJca]
      exact this
    · exact ⟨1, one_pos, fun h => absurd h hc⟩
  choose ηc hηc hηcb using hdir
  have hCne : C.Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have := hcon 1 one_pos
    rw [hemp] at this
    simp at this
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = C.inf' hCne ηc := ⟨_, rfl⟩
  have hηpos : 0 < η := by
    rw [hηdef, Finset.lt_inf'_iff]
    intro c _
    exact hηc c
  have hηle : ∀ c ∈ C, η ≤ ηc c := by
    intro c hc
    rw [hηdef]
    exact Finset.inf'_le _ hc
  obtain ⟨Mf, hMf⟩ : ∃ Mf : ℕ, Mf = max (2 * i₀ + 1) (⌈1 / η⌉₊ + 1) := ⟨_, rfl⟩
  have hMf1 : 2 * i₀ + 1 ≤ Mf := by rw [hMf]; exact le_max_left _ _
  have hMf2 : ⌈1 / η⌉₊ + 1 ≤ Mf := by rw [hMf]; exact le_max_right _ _
  have hMfpos : 0 < Mf := by omega
  have hMfR : (0 : ℝ) < Mf := by exact_mod_cast hMfpos
  have hinvMf : 1 / (Mf : ℝ) < η := by
    have h1 : 1 / η ≤ (⌈1 / η⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈1 / η⌉₊ : ℕ) : ℝ) + 1 ≤ Mf := by exact_mod_cast hMf2
    have h3 : 1 / η < Mf := by linarith
    rw [div_lt_iff₀ hMfR]
    rw [div_lt_iff₀ hηpos] at h3
    linarith
  have hlow := blocks_lower b hb0 U κ hκpos Λ hΛ2 hΛU i₀ hUb hLo Mf hMfpos Mf (by omega) le_rfl
  have hx1 : (1 : ℝ) < 1 + 1 / (Mf : ℝ) := by
    have : 0 < 1 / (Mf : ℝ) := by positivity
    linarith
  have hupp : ∑ d ∈ Finset.Icc 1 (Λ ^ Mf), b d * (d : ℝ) ^ (-(1 + 1 / (Mf : ℝ)))
      ≤ J * (ε * Mf) := by
    simp only [hba, Finset.sum_mul]
    rw [Finset.sum_comm, hJ, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro c hc
    have h1 := hηcb c hc (1 + 1 / (Mf : ℝ)) hx1 (by linarith [hηle c hc]) (Λ ^ Mf)
    have e1 : ε / (1 + 1 / (Mf : ℝ) - 1) = ε * Mf := by
      rw [show (1 + 1 / (Mf : ℝ) - 1) = 1 / (Mf : ℝ) by ring]
      field_simp
    rw [e1] at h1
    exact h1
  have hfin : J * (ε * Mf) ≤ (Mf : ℝ) / (8 * κ * Λ) := by
    rw [hε]
    have h1 : J / (J + 1) ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    have e1 : J * (1 / (8 * κ * Λ * (J + 1)) * Mf) = (J / (J + 1)) * ((Mf : ℝ) / (8 * κ * Λ)) := by
      field_simp
    rw [e1]
    have h2 : 0 ≤ (Mf : ℝ) / (8 * κ * Λ) := by positivity
    nlinarith
  have hchain : ((Mf : ℝ) - i₀) / (2 * κ * Λ) ≤ (Mf : ℝ) / (8 * κ * Λ) :=
    hlow.trans (hupp.trans hfin)
  have hpos : (0 : ℝ) < 8 * κ * Λ := by positivity
  have e2 : ((Mf : ℝ) - i₀) / (2 * κ * Λ) = (4 * ((Mf : ℝ) - i₀)) / (8 * κ * Λ) := by
    field_simp
    ring
  rw [e2, div_le_div_iff_of_pos_right hpos] at hchain
  have h9 : (2 * (i₀ : ℝ) + 1) ≤ Mf := by exact_mod_cast hMf1
  linarith

end goodT



section finalAssembly

open Classical in
/-- Simultaneous avoidance for every finite set of non-cubes. -/
theorem avoidFinite_proved : AvoidFinite := by
  intro C hC
  by_cases hne : C.card = 0
  · refine ⟨0, fun c hc => ?_⟩
    rw [Finset.card_eq_zero] at hne
    simp [hne] at hc
  have hkpos : 0 < C.card := Nat.pos_of_ne_zero hne
  have hsm : ∀ c : ℤ, ∃ A : ℕ, 0 < A ∧ (c ∈ C → ∀ T : ℕ,
      4 * C.card * (SmallBad c T (T / A)).card ≤ T) := by
    intro c
    by_cases hc : c ∈ C
    · obtain ⟨A, hA, h⟩ := small_range c (hC c hc) (4 * C.card)
      exact ⟨A, hA, fun _ => h⟩
    · exact ⟨1, one_pos, fun h => absurd h hc⟩
  choose Af hAf hsmall using hsm
  obtain ⟨T, hT, hlarge⟩ := exists_good_T C hC Af (fun c _ => hAf c) 2 (by norm_num)
    (fun c hc => MV c (hC c hc)) (fun c hc => split_not_summable c (hC c hc))
  by_contra hcon
  push Not at hcon
  have hcover : Finset.Icc (-(T : ℤ)) T ⊆ C.biUnion (fun c => badSet c T) := by
    intro t ht
    obtain ⟨c, hc, huv⟩ := hcon t
    rw [Finset.mem_biUnion]
    refine ⟨c, hc, ?_⟩
    unfold badSet
    exact Finset.mem_filter.mpr ⟨ht, huv⟩
  have h1 : (Finset.Icc (-(T : ℤ)) T).card ≤ ∑ c ∈ C, (badSet c T).card :=
    (Finset.card_le_card hcover).trans Finset.card_biUnion_le
  have h2 : (Finset.Icc (-(T : ℤ)) T).card = 2 * T + 1 := by
    rw [Int.card_Icc]
    omega
  have h3 : ∀ c ∈ C, (badSet c T).card
      ≤ (SmallBad c T (T / Af c)).card + (LargeBad c T (Af c)).card := fun c hc =>
    (Finset.card_le_card (badSet_subset c (hC c hc) T (Af c))).trans (Finset.card_union_le _ _)
  have h4 : ∑ c ∈ C, (badSet c T).card
      ≤ ∑ c ∈ C, (SmallBad c T (T / Af c)).card + ∑ c ∈ C, (LargeBad c T (Af c)).card := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum h3
  have h5 : 4 * C.card * ∑ c ∈ C, (SmallBad c T (T / Af c)).card ≤ C.card * T := by
    rw [Finset.mul_sum]
    calc ∑ c ∈ C, 4 * C.card * (SmallBad c T (T / Af c)).card
        ≤ ∑ _c ∈ C, T := Finset.sum_le_sum (fun c hc => hsmall c hc T)
      _ = C.card * T := by rw [Finset.sum_const, smul_eq_mul]
  have h6 : 4 * ∑ c ∈ C, (SmallBad c T (T / Af c)).card ≤ T := by
    have h7 : C.card * (4 * ∑ c ∈ C, (SmallBad c T (T / Af c)).card) ≤ C.card * T := by
      rw [← mul_assoc, mul_comm C.card 4]
      exact h5
    exact Nat.le_of_mul_le_mul_left h7 hkpos
  omega

theorem disproof_final : ¬ (type_of% @Erdos477.erdos_477.variants.X_pow_three) :=
  disproof_of_avoid avoidFinite_proved

end finalAssembly


end OMA477

theorem OMA.disproof : ¬ (type_of% @Erdos477.erdos_477.variants.X_pow_three) :=
  OMA477.disproof_final
