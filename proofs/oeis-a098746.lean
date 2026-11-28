import OMAStatements.S_oeis_a098746
import Mathlib

-- Problem: A098746: Number of permutations of [1..n] which avoid 4231 and 42513.
-- Upstream: formal-conjectures statements/oeis-a098746.lean:0 (declaration OMA.S_oeis_a098746.main)
-- Credit: @marcelopierry (the owner of the agent is credited as the solver)
-- Prove EXACTLY this target. No sorry, no axiom, no native_decide.

namespace OMA.S_oeis_a098746

section KernelMethod

private def C_nat : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ i : Fin (n + 1), C_nat i.1 * C_nat (n - i.1)

private lemma C_nat_zero : C_nat 0 = 1 := by rw [C_nat]

private lemma C_nat_succ (n : ℕ) :
    C_nat (n + 1) = ∑ i ∈ Finset.range (n + 1), C_nat i * C_nat (n - i) := by
  rw [C_nat, Fin.sum_univ_eq_sum_range (fun i => C_nat i * C_nat (n - i))]

private def T_nat : ℕ → ℕ
  | 0 => 1
  | n + 1 => ∑ i : Fin (n + 1), ∑ j : Fin (n + 1 - i.1),
      T_nat i.1 * T_nat j.1 * T_nat (n - i.1 - j.1)

private lemma T_nat_zero : T_nat 0 = 1 := by rw [T_nat]

private lemma T_nat_succ (n : ℕ) :
    T_nat (n + 1) = ∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (n + 1 - i),
      T_nat i * T_nat j * T_nat (n - i - j) := by
  rw [T_nat, Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin (n + 1 - i),
    T_nat i * T_nat j.1 * T_nat (n - i - j.1))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Fin.sum_univ_eq_sum_range (fun j => T_nat i * T_nat j * T_nat (n - i - j))]

private lemma coeff_mul_range (f g : PowerSeries ℚ) (N : ℕ) :
    PowerSeries.coeff N (f * g) =
      ∑ k ∈ Finset.range (N + 1), PowerSeries.coeff k f * PowerSeries.coeff (N - k) g := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => PowerSeries.coeff a f * PowerSeries.coeff b g) N

private noncomputable def T_ps : PowerSeries ℚ :=
  PowerSeries.mk fun n => (T_nat n : ℚ)

private lemma coeff_T_ps (n : ℕ) : PowerSeries.coeff n T_ps = (T_nat n : ℚ) :=
  PowerSeries.coeff_mk n _

private lemma T_ps_eq : T_ps = 1 + PowerSeries.X * T_ps ^ 3 := by
  ext n
  cases n with
  | zero =>
    simp [T_ps, T_nat_zero]
  | succ n =>
    rw [coeff_T_ps, map_add, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), zero_add,
      PowerSeries.coeff_succ_X_mul, pow_three, coeff_mul_range]
    simp only [T_nat_succ, Nat.cast_sum, Nat.cast_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [coeff_T_ps, coeff_mul_range, Finset.mul_sum]
    have hhi : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hrange : n - i + 1 = n + 1 - i := by omega
    rw [hrange]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coeff_T_ps, coeff_T_ps]
    ring

private noncomputable def diagEval (T : PowerSeries ℚ) (P : ℕ → Polynomial ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun N =>
    ∑ n ∈ Finset.range (N + 1), PowerSeries.coeff (N - n) (Polynomial.aeval T (P n))

private lemma coeff_diagEval (T : PowerSeries ℚ) (P : ℕ → Polynomial ℚ) (N : ℕ) :
    PowerSeries.coeff N (diagEval T P) =
      ∑ n ∈ Finset.range (N + 1), PowerSeries.coeff (N - n) (Polynomial.aeval T (P n)) :=
  PowerSeries.coeff_mk N _

private lemma diagEval_add (T : PowerSeries ℚ) (P Q : ℕ → Polynomial ℚ) :
    diagEval T (fun n => P n + Q n) = diagEval T P + diagEval T Q := by
  ext N
  simp only [coeff_diagEval, map_add, Finset.sum_add_distrib]

private lemma diagEval_sub (T : PowerSeries ℚ) (P Q : ℕ → Polynomial ℚ) :
    diagEval T (fun n => P n - Q n) = diagEval T P - diagEval T Q := by
  ext N
  simp only [coeff_diagEval, map_sub, Finset.sum_sub_distrib]

private lemma diagEval_const_mul (T : PowerSeries ℚ) (q : Polynomial ℚ) (P : ℕ → Polynomial ℚ) :
    diagEval T (fun n => q * P n) = Polynomial.aeval T q * diagEval T P := by
  ext N
  rw [coeff_diagEval, coeff_mul_range]
  simp_rw [coeff_diagEval, Finset.mul_sum]
  have hswap :
      ∑ k ∈ Finset.range (N + 1), ∑ n ∈ Finset.range (N - k + 1),
        PowerSeries.coeff k (Polynomial.aeval T q) *
          PowerSeries.coeff (N - k - n) (Polynomial.aeval T (P n)) =
      ∑ n ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N - n + 1),
        PowerSeries.coeff k (Polynomial.aeval T q) *
          PowerSeries.coeff (N - n - k) (Polynomial.aeval T (P n)) := by
    have h1 : ∀ k ∈ Finset.range (N + 1),
        ∑ n ∈ Finset.range (N - k + 1),
          PowerSeries.coeff k (Polynomial.aeval T q) *
            PowerSeries.coeff (N - k - n) (Polynomial.aeval T (P n)) =
        ∑ n ∈ Finset.range (N + 1),
          if k + n ≤ N then
            PowerSeries.coeff k (Polynomial.aeval T q) *
              PowerSeries.coeff (N - k - n) (Polynomial.aeval T (P n))
          else 0 := by
      intro k hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext n; simp only [Finset.mem_range, Finset.mem_filter]; omega
    have h2 : ∀ n ∈ Finset.range (N + 1),
        ∑ k ∈ Finset.range (N - n + 1),
          PowerSeries.coeff k (Polynomial.aeval T q) *
            PowerSeries.coeff (N - n - k) (Polynomial.aeval T (P n)) =
        ∑ k ∈ Finset.range (N + 1),
          if k + n ≤ N then
            PowerSeries.coeff k (Polynomial.aeval T q) *
              PowerSeries.coeff (N - k - n) (Polynomial.aeval T (P n))
          else 0 := by
      intro n hn
      have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun k hk => ?_
      · ext k; simp only [Finset.mem_range, Finset.mem_filter]; omega
      · have hsub : N - n - k = N - k - n := by omega
        rw [hsub]
    rw [Finset.sum_congr rfl h1, Finset.sum_comm]
    exact Finset.sum_congr rfl fun n hn => (h2 n hn).symm
  rw [hswap]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, coeff_mul_range]

private lemma diagEval_conv (T : PowerSeries ℚ) (P Q : ℕ → Polynomial ℚ) :
    diagEval T (fun n => ∑ i ∈ Finset.range (n + 1), P i * Q (n - i)) =
      diagEval T P * diagEval T Q := by
  ext N
  rw [coeff_diagEval, coeff_mul_range]
  let term (i j a : ℕ) : ℚ :=
    PowerSeries.coeff a (Polynomial.aeval T (P i)) *
      PowerSeries.coeff (N - i - j - a) (Polynomial.aeval T (Q j))
  have hlhs :
      ∑ n ∈ Finset.range (N + 1),
        PowerSeries.coeff (N - n) (Polynomial.aeval T (∑ i ∈ Finset.range (n + 1), P i * Q (n - i))) =
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∑ a ∈ Finset.range (N + 1),
        if i + j + a ≤ N then term i j a else 0 := by
    have hstep1 : ∀ n ∈ Finset.range (N + 1),
        PowerSeries.coeff (N - n) (Polynomial.aeval T (∑ i ∈ Finset.range (n + 1), P i * Q (n - i))) =
        ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∑ a ∈ Finset.range (N + 1),
          if i + j = n ∧ a ≤ N - n then term i j a else 0 := by
      intro n hn
      have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      rw [map_sum, map_sum]
      calc
        ∑ i ∈ Finset.range (n + 1), PowerSeries.coeff (N - n) (Polynomial.aeval T (P i * Q (n - i)))
            = ∑ i ∈ Finset.range (n + 1), ∑ a ∈ Finset.range (N - n + 1),
                PowerSeries.coeff a (Polynomial.aeval T (P i)) *
                  PowerSeries.coeff (N - n - a) (Polynomial.aeval T (Q (n - i))) := by
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [map_mul, coeff_mul_range]
        _ = ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∑ a ∈ Finset.range (N + 1),
              if i + j = n ∧ a ≤ N - n then term i j a else 0 := by
              have hinner : ∀ i ∈ Finset.range (N + 1),
                  (∑ j ∈ Finset.range (N + 1), ∑ a ∈ Finset.range (N + 1),
                    if i + j = n ∧ a ≤ N - n then term i j a else 0) =
                  if i ≤ n then
                    ∑ a ∈ Finset.range (N - n + 1),
                      PowerSeries.coeff a (Polynomial.aeval T (P i)) *
                        PowerSeries.coeff (N - n - a) (Polynomial.aeval T (Q (n - i)))
                  else 0 := by
                intro i _
                by_cases hi : i ≤ n
                · simp only [hi, ↓reduceIte]
                  rw [Finset.sum_eq_single (n - i)]
                  · rw [← Finset.sum_filter]
                    refine Finset.sum_congr ?_ fun a _ => ?_
                    · ext a; simp only [Finset.mem_range, Finset.mem_filter]; omega
                    · simp only [term]
                      have hsub : N - i - (n - i) - a = N - n - a := by omega
                      rw [hsub]
                  · intro j _ hjne
                    refine Finset.sum_eq_zero fun a _ => ?_
                    split_ifs with h
                    · exfalso; exact hjne (by omega)
                    · rfl
                  · intro hnot
                    exfalso; exact hnot (Finset.mem_range.mpr (by omega))
                · simp only [hi, ↓reduceIte]
                  refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun a _ => ?_
                  split_ifs with h
                  · exfalso; omega
                  · rfl
              rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
              refine Finset.sum_congr ?_ (fun _ _ => rfl)
              ext i; simp only [Finset.mem_range, Finset.mem_filter]; omega
    rw [Finset.sum_congr rfl hstep1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hle : i + j + a ≤ N
    · simp only [hle, ↓reduceIte]
      rw [Finset.sum_eq_single (i + j)]
      · simp [show a ≤ N - (i + j) by omega]
      · intro n _ hne; simp [Ne.symm hne]
      · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
    · simp only [hle, ↓reduceIte]
      refine Finset.sum_eq_zero fun n hn => ?_
      have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      split_ifs with h
      · exfalso; omega
      · rfl
  have hrhs :
      ∑ k ∈ Finset.range (N + 1),
        PowerSeries.coeff k (diagEval T P) * PowerSeries.coeff (N - k) (diagEval T Q) =
      ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∑ a ∈ Finset.range (N + 1),
        if i + j + a ≤ N then term i j a else 0 := by
    have hstep : ∀ k ∈ Finset.range (N + 1),
        PowerSeries.coeff k (diagEval T P) * PowerSeries.coeff (N - k) (diagEval T Q) =
        ∑ i ∈ Finset.range (N + 1), ∑ j ∈ Finset.range (N + 1), ∑ a ∈ Finset.range (N + 1),
          if i + a = k ∧ j ≤ N - k then term i j a else 0 := by
      intro k hk
      have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [coeff_diagEval, coeff_diagEval, Finset.sum_mul]
      have hinner : ∀ i ∈ Finset.range (N + 1),
          (∑ j ∈ Finset.range (N + 1), ∑ a ∈ Finset.range (N + 1),
            if i + a = k ∧ j ≤ N - k then term i j a else 0) =
          if i ≤ k then
            PowerSeries.coeff (k - i) (Polynomial.aeval T (P i)) *
              ∑ j ∈ Finset.range (N - k + 1), PowerSeries.coeff (N - k - j) (Polynomial.aeval T (Q j))
          else 0 := by
        intro i _
        by_cases hi : i ≤ k
        · simp only [hi, ↓reduceIte, Finset.mul_sum]
          have h1 : ∀ j ∈ Finset.range (N + 1),
              (∑ a ∈ Finset.range (N + 1), if i + a = k ∧ j ≤ N - k then term i j a else 0) =
              if j ≤ N - k then
                PowerSeries.coeff (k - i) (Polynomial.aeval T (P i)) *
                  PowerSeries.coeff (N - k - j) (Polynomial.aeval T (Q j))
              else 0 := by
            intro j _
            by_cases hj : j ≤ N - k
            · simp only [hj, and_true, ↓reduceIte]
              rw [Finset.sum_eq_single (k - i)]
              · simp only [term, show i + (k - i) = k by omega, ↓reduceIte]
                have hsub : N - i - j - (k - i) = N - k - j := by omega
                rw [hsub]
              · intro a _ hne
                split_ifs with h
                · exfalso; exact hne (by omega)
                · rfl
              · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
            · simp [hj]
          rw [Finset.sum_congr rfl h1, ← Finset.sum_filter]
          refine Finset.sum_congr ?_ (fun _ _ => rfl)
          ext j; simp only [Finset.mem_range, Finset.mem_filter]; omega
        · simp only [hi, ↓reduceIte]
          refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun a _ => ?_
          split_ifs with h
          · exfalso; omega
          · rfl
      rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter]
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      ext i; simp only [Finset.mem_range, Finset.mem_filter]; omega
    rw [Finset.sum_congr rfl hstep]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hle : i + j + a ≤ N
    · simp only [hle, ↓reduceIte]
      rw [Finset.sum_eq_single (i + a)]
      · simp [show j ≤ N - (i + a) by omega]
      · intro k _ hne; simp [Ne.symm hne]
      · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))
    · simp only [hle, ↓reduceIte]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      split_ifs with h
      · exfalso; omega
      · rfl
  rw [hlhs, hrhs]

private lemma diagEval_C (T : PowerSeries ℚ) (a : ℕ → ℚ) :
    diagEval T (fun n => Polynomial.C (a n)) = PowerSeries.mk a := by
  ext N
  rw [coeff_diagEval, PowerSeries.coeff_mk]
  rw [Finset.sum_eq_single N]
  · simp [PowerSeries.coeff_C]
  · intro n hn hne
    have hnN : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    have hpos : N - n ≠ 0 := by omega
    simp [PowerSeries.coeff_C, hpos]
  · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (Nat.lt_succ_self N))

private lemma diagEval_shift (T : PowerSeries ℚ) (P : ℕ → Polynomial ℚ) :
    diagEval T (fun n => if n = 0 then 0 else P (n - 1)) = PowerSeries.X * diagEval T P := by
  ext N
  cases N with
  | zero =>
    simp [coeff_diagEval]
  | succ N =>
    rw [coeff_diagEval, PowerSeries.coeff_succ_X_mul, coeff_diagEval]
    rw [Finset.sum_range_succ']
    simp

private lemma diagEval_single_one (T : PowerSeries ℚ) (q : Polynomial ℚ) :
    diagEval T (fun n => if n = 1 then q else 0) = PowerSeries.X * Polynomial.aeval T q := by
  ext N
  cases N with
  | zero => simp [coeff_diagEval]
  | succ N =>
    rw [coeff_diagEval, PowerSeries.coeff_succ_X_mul]
    rw [Finset.sum_eq_single 1]
    · simp
    · intro n _ hne; simp [hne]
    · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (by omega))

private noncomputable def C_seq (n : ℕ) : Polynomial ℚ :=
  Polynomial.C (C_nat n : ℚ) * Polynomial.X ^ n

private lemma diagEval_C_seq : diagEval T_ps C_seq = T_ps := by
  set CT := diagEval T_ps C_seq
  let P_conv : ℕ → Polynomial ℚ := fun m =>
    Polynomial.X * ∑ i ∈ Finset.range (m + 1), C_seq i * C_seq (m - i)
  have hrec_seq : ∀ n : ℕ,
      C_seq n = (if n = 0 then 1 else 0) + (if n = 0 then 0 else P_conv (n - 1)) := by
    intro n
    cases n with
    | zero => simp [C_seq, C_nat_zero]
    | succ n =>
      simp only [Nat.succ_ne_zero, ↓reduceIte, zero_add, Nat.add_sub_cancel, P_conv]
      simp only [C_seq, C_nat_succ, Nat.cast_sum, Nat.cast_mul, map_sum, Finset.sum_mul,
        Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [map_mul]
      calc
        Polynomial.C (C_nat i : ℚ) * Polynomial.C (C_nat (n - i) : ℚ) * Polynomial.X ^ (n + 1)
            = Polynomial.X * (Polynomial.C (C_nat i : ℚ) * Polynomial.C (C_nat (n - i) : ℚ) *
                (Polynomial.X ^ i * Polynomial.X ^ (n - i))) := by
              rw [← pow_add, show i + (n - i) = n by omega]; ring
        _ = Polynomial.X *
              (Polynomial.C (C_nat i : ℚ) * Polynomial.X ^ i *
                (Polynomial.C (C_nat (n - i) : ℚ) * Polynomial.X ^ (n - i))) := by ring
  have hCT_eq : CT = 1 + PowerSeries.X * T_ps * CT ^ 2 := by
    have h1 : CT = diagEval T_ps (fun n => (if n = 0 then (1 : Polynomial ℚ) else 0) +
        (if n = 0 then 0 else P_conv (n - 1))) := by
      change diagEval T_ps C_seq = _
      congr 1; funext n; exact hrec_seq n
    have hzero : diagEval T_ps (fun n => if n = 0 then (1 : Polynomial ℚ) else 0) = 1 := by
      ext N; rw [coeff_diagEval, PowerSeries.coeff_one]
      rw [Finset.sum_eq_single 0]
      · simp [PowerSeries.coeff_one]
      · intro n _ hne; simp [hne]
      · intro hnot; exfalso; exact hnot (Finset.mem_range.mpr (Nat.succ_pos N))
    have hshift : diagEval T_ps (fun n => if n = 0 then 0 else P_conv (n - 1)) =
        PowerSeries.X * (T_ps * CT ^ 2) := by
      rw [diagEval_shift]
      dsimp only [P_conv]
      rw [diagEval_const_mul, diagEval_conv]
      simp [CT, sq]
    calc
      CT = diagEval T_ps (fun n => (if n = 0 then (1 : Polynomial ℚ) else 0) +
            (if n = 0 then 0 else P_conv (n - 1))) := h1
      _ = diagEval T_ps (fun n => if n = 0 then (1 : Polynomial ℚ) else 0) +
            diagEval T_ps (fun n => if n = 0 then 0 else P_conv (n - 1)) := diagEval_add _ _ _
      _ = 1 + PowerSeries.X * (T_ps * CT ^ 2) := by rw [hzero, hshift]
      _ = 1 + PowerSeries.X * T_ps * CT ^ 2 := by ring
  ext N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    cases N with
    | zero =>
      conv_lhs => rw [hCT_eq]
      conv_rhs => rw [T_ps_eq]
      simp
    | succ N =>
      conv_lhs => rw [hCT_eq]
      conv_rhs => rw [T_ps_eq]
      simp only [map_add, PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero N), zero_add]
      rw [mul_assoc PowerSeries.X T_ps (CT ^ 2), PowerSeries.coeff_succ_X_mul,
        PowerSeries.coeff_succ_X_mul, pow_three, coeff_mul_range, coeff_mul_range]
      refine Finset.sum_congr rfl fun k hk => ?_
      congr 1
      rw [sq, coeff_mul_range, coeff_mul_range]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hkN : k ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hjN : j ≤ N - k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [ih j (by omega), ih (N - k - j) (by omega)]

private lemma kernel_F_eval_one (F_poly : ℕ → Polynomial ℚ)
    (hF0 : F_poly 0 = 0) (hF1 : F_poly 1 = 1)
    (hFrec : ∀ n ≥ 2,
      (1 - Polynomial.X) * F_poly n =
        ∑ m ∈ Finset.range (n - 1),
          C_seq m * (Polynomial.X * Polynomial.C ((F_poly (n - 1 - m)).eval 1) -
            Polynomial.X ^ 2 * F_poly (n - 1 - m))) :
    ∀ n : ℕ, 1 ≤ n → (F_poly n).eval 1 = (T_nat (n - 1) : ℚ) := by
  let E := diagEval T_ps F_poly
  let F1 := PowerSeries.mk fun n => (F_poly n).eval 1
  let Q_F : ℕ → Polynomial ℚ := fun k =>
    Polynomial.X * Polynomial.C ((F_poly k).eval 1) - Polynomial.X ^ 2 * F_poly k
  let P_F : ℕ → Polynomial ℚ := fun k => ∑ m ∈ Finset.range (k + 1), C_seq m * Q_F (k - m)
  have hseq : ∀ n : ℕ,
      (1 - Polynomial.X) * F_poly n =
        (if n = 1 then (1 - Polynomial.X) else 0) + (if n = 0 then 0 else P_F (n - 1)) := by
    intro n
    match n with
    | 0 => simp [hF0]
    | 1 => simp [hF1, P_F, Q_F, hF0]
    | n + 2 =>
      simp only [show n + 2 ≠ 1 by omega, show n + 2 ≠ 0 by omega, ↓reduceIte, zero_add,
        Nat.add_sub_cancel, P_F]
      rw [hFrec (n + 2) (by omega)]
      simp only [show n + 2 - 1 = n + 1 by omega]
      rw [Finset.sum_range_succ (n := n + 1)]
      simp [Q_F, hF0]
  have hps : (1 - T_ps) * E =
      PowerSeries.X * (1 - T_ps) + PowerSeries.X * (T_ps * (T_ps * F1 - T_ps ^ 2 * E)) := by
    have hL : diagEval T_ps (fun n => (1 - Polynomial.X) * F_poly n) = (1 - T_ps) * E := by
      rw [diagEval_const_mul]; simp [E]
    have hR1 : diagEval T_ps (fun n => if n = 1 then (1 - Polynomial.X) else 0) =
        PowerSeries.X * (1 - T_ps) := by
      rw [diagEval_single_one]; simp
    have hR2 : diagEval T_ps (fun n => if n = 0 then 0 else P_F (n - 1)) =
        PowerSeries.X * (T_ps * (T_ps * F1 - T_ps ^ 2 * E)) := by
      rw [diagEval_shift]
      dsimp only [P_F]
      rw [diagEval_conv, diagEval_C_seq]
      dsimp only [Q_F]
      rw [diagEval_sub, diagEval_const_mul, diagEval_const_mul, diagEval_C]
      simp [E, F1]
    have hboth : diagEval T_ps (fun n => (1 - Polynomial.X) * F_poly n) =
        diagEval T_ps (fun n => (if n = 1 then (1 - Polynomial.X) else 0) +
          (if n = 0 then 0 else P_F (n - 1))) := by
      congr 1; funext n; exact hseq n
    rw [hL, diagEval_add, hR1, hR2] at hboth
    exact hboth
  have h1 : 1 - T_ps = -(PowerSeries.X * T_ps ^ 3) := by linear_combination -T_ps_eq
  rw [h1] at hps
  have hfac : PowerSeries.X * T_ps ^ 2 * (F1 - PowerSeries.X * T_ps) = 0 := by
    linear_combination -hps
  have hX_ne : (PowerSeries.X : PowerSeries ℚ) ≠ 0 := PowerSeries.X_ne_zero
  have hT_ne : T_ps ≠ 0 := by
    intro h0; have := congrArg (PowerSeries.coeff 0) h0; simp [T_ps, T_nat_zero] at this
  have hF1_eq : F1 = PowerSeries.X * T_ps :=
    sub_eq_zero.mp ((mul_eq_zero.mp hfac).resolve_left (mul_ne_zero hX_ne (pow_ne_zero 2 hT_ne)))
  intro n hn
  cases n with
  | zero => omega
  | succ m =>
    have hc := congrArg (PowerSeries.coeff (m + 1)) hF1_eq
    simpa [F1, PowerSeries.coeff_succ_X_mul, coeff_T_ps] using hc

private lemma kernel_G_eval_one (G_poly : ℕ → Polynomial ℚ)
    (hG0 : G_poly 0 = 0) (hG1 : G_poly 1 = 1)
    (hGrec : ∀ n ≥ 2,
      let G0 : ℕ → Polynomial ℚ := fun k => if k = 0 then 0 else C_seq (k - 1)
      let G1 : ℕ → Polynomial ℚ := fun k => G_poly k - G0 k
      (1 - Polynomial.X) * G_poly n =
        (1 - Polynomial.X) *
          (∑ m ∈ Finset.range (n + 1), C_seq m *
            ∑ n1 ∈ Finset.range (n - m + 1), G1 n1 * Polynomial.C ((G_poly (n - m - n1)).eval 1)) +
        (∑ m ∈ Finset.range (n - 1), C_seq m *
          (Polynomial.X * Polynomial.C ((G_poly (n - 1 - m)).eval 1) -
            Polynomial.X * G_poly (n - 1 - m))) +
        (1 - Polynomial.X) *
          (∑ m ∈ Finset.range (n - 1), C_seq m * (Polynomial.X * G0 (n - 1 - m)))) :
    ∀ n : ℕ, 1 ≤ n → (G_poly n).eval 1 = (T_nat (n - 1) : ℚ) := by
  let G0 : ℕ → Polynomial ℚ := fun k => if k = 0 then 0 else C_seq (k - 1)
  let G1 : ℕ → Polynomial ℚ := fun k => G_poly k - G0 k
  let E := diagEval T_ps G_poly
  let g := PowerSeries.mk fun n => (G_poly n).eval 1
  have hG0_0 : G0 0 = 0 := rfl
  have hG0_1 : G0 1 = 1 := by simp [G0, C_seq, C_nat_zero]
  have hG1_0 : G1 0 = 0 := by simp [G1, hG0, hG0_0]
  have hG1_1 : G1 1 = 0 := by simp [G1, hG1, hG0_1]
  let H_conv : ℕ → Polynomial ℚ := fun r =>
    ∑ n1 ∈ Finset.range (r + 1), G1 n1 * Polynomial.C ((G_poly (r - n1)).eval 1)
  let Q3 : ℕ → Polynomial ℚ := fun k =>
    Polynomial.X * Polynomial.C ((G_poly k).eval 1) - Polynomial.X * G_poly k
  let P3 : ℕ → Polynomial ℚ := fun k => ∑ m ∈ Finset.range (k + 1), C_seq m * Q3 (k - m)
  let P4 : ℕ → Polynomial ℚ := fun k => ∑ m ∈ Finset.range (k + 1), C_seq m * (Polynomial.X * G0 (k - m))
  have hseq : ∀ n : ℕ,
      (1 - Polynomial.X) * G_poly n =
        (if n = 1 then (1 - Polynomial.X) else 0) +
        (1 - Polynomial.X) * (∑ m ∈ Finset.range (n + 1), C_seq m * H_conv (n - m)) +
        (if n = 0 then 0 else P3 (n - 1)) +
        (1 - Polynomial.X) * (if n = 0 then 0 else P4 (n - 1)) := by
    intro n
    match n with
    | 0 => simp [hG0, H_conv, hG1_0]
    | 1 =>
      simp only [↓reduceIte, Nat.one_ne_zero, Nat.sub_self, hG1, P3, P4, Q3, H_conv]
      simp [Finset.sum_range_succ, hG0, hG1, hG0_0, hG1_0, hG1_1]
    | n + 2 =>
      simp only [show n + 2 ≠ 1 by omega, show n + 2 ≠ 0 by omega, ↓reduceIte, zero_add,
        Nat.add_sub_cancel, P3, P4, H_conv]
      have hr := hGrec (n + 2) (by omega)
      dsimp only [G0, G1] at hr ⊢
      rw [hr]
      simp only [show n + 2 - 1 = n + 1 by omega]
      rw [Finset.sum_range_succ (n := n + 1), Finset.sum_range_succ (n := n + 1)]
      simp [Q3, hG0, hG0_0]
  have hdiag_G0 : diagEval T_ps G0 = PowerSeries.X * T_ps := by
    change diagEval T_ps (fun k => if k = 0 then 0 else C_seq (k - 1)) = _
    rw [diagEval_shift, diagEval_C_seq]
  have hdiag_G1 : diagEval T_ps G1 = E - PowerSeries.X * T_ps := by
    change diagEval T_ps (fun k => G_poly k - G0 k) = _
    rw [diagEval_sub, hdiag_G0]
  have hps : (1 - T_ps) * E =
      PowerSeries.X * (1 - T_ps) +
      (1 - T_ps) * (T_ps * ((E - PowerSeries.X * T_ps) * g)) +
      PowerSeries.X * (T_ps * (T_ps * g - T_ps * E)) +
      (1 - T_ps) * (PowerSeries.X * (T_ps * (T_ps * (PowerSeries.X * T_ps)))) := by
    have hL : diagEval T_ps (fun n => (1 - Polynomial.X) * G_poly n) = (1 - T_ps) * E := by
      rw [diagEval_const_mul]; simp [E]
    have hR1 : diagEval T_ps (fun n => if n = 1 then (1 - Polynomial.X) else 0) =
        PowerSeries.X * (1 - T_ps) := by
      rw [diagEval_single_one]; simp
    have hR2 :
        diagEval T_ps (fun n => (1 - Polynomial.X) * (∑ m ∈ Finset.range (n + 1), C_seq m * H_conv (n - m))) =
        (1 - T_ps) * (T_ps * ((E - PowerSeries.X * T_ps) * g)) := by
      rw [diagEval_const_mul, diagEval_conv, diagEval_C_seq]
      have hH : diagEval T_ps H_conv = (E - PowerSeries.X * T_ps) * g := by
        dsimp only [H_conv]
        rw [diagEval_conv T_ps G1 (fun k => Polynomial.C ((G_poly k).eval 1)), hdiag_G1, diagEval_C]
      rw [hH]; simp
    have hR3 : diagEval T_ps (fun n => if n = 0 then 0 else P3 (n - 1)) =
        PowerSeries.X * (T_ps * (T_ps * g - T_ps * E)) := by
      rw [diagEval_shift]
      dsimp only [P3]
      rw [diagEval_conv, diagEval_C_seq]
      dsimp only [Q3]
      rw [diagEval_sub, diagEval_const_mul, diagEval_const_mul, diagEval_C]
      simp [E, g]
    have hR4 :
        diagEval T_ps (fun n => (1 - Polynomial.X) * (if n = 0 then 0 else P4 (n - 1))) =
        (1 - T_ps) * (PowerSeries.X * (T_ps * (T_ps * (PowerSeries.X * T_ps)))) := by
      rw [diagEval_const_mul, diagEval_shift]
      dsimp only [P4]
      rw [diagEval_conv T_ps C_seq (fun k => Polynomial.X * G0 k), diagEval_C_seq,
        diagEval_const_mul, hdiag_G0]
      simp
    have hboth : diagEval T_ps (fun n => (1 - Polynomial.X) * G_poly n) =
        diagEval T_ps (fun n =>
          (if n = 1 then (1 - Polynomial.X) else 0) +
          (1 - Polynomial.X) * (∑ m ∈ Finset.range (n + 1), C_seq m * H_conv (n - m)) +
          (if n = 0 then 0 else P3 (n - 1)) +
          (1 - Polynomial.X) * (if n = 0 then 0 else P4 (n - 1))) := by
      congr 1; funext n; exact hseq n
    rw [hL, diagEval_add, diagEval_add, diagEval_add, hR1, hR2, hR3, hR4] at hboth
    exact hboth
  have h1 : 1 - T_ps = -(PowerSeries.X * T_ps ^ 3) := by linear_combination -T_ps_eq
  rw [h1] at hps
  have hfac : PowerSeries.X * T_ps ^ 3 * (T_ps * E - 1) * (g - PowerSeries.X * T_ps) = 0 := by
    linear_combination hps - (PowerSeries.X * T_ps ^ 2 * (E - g) + PowerSeries.X ^ 2 * T_ps ^ 3) * h1
  have hX_ne : (PowerSeries.X : PowerSeries ℚ) ≠ 0 := PowerSeries.X_ne_zero
  have hT_ne : T_ps ≠ 0 := by
    intro h0; have := congrArg (PowerSeries.coeff 0) h0; simp [T_ps, T_nat_zero] at this
  have hE0 : PowerSeries.coeff 0 E = 0 := by
    simp [E, coeff_diagEval, hG0]
  have hTE_ne : T_ps * E - 1 ≠ 0 := by
    intro h0
    have hc := congrArg (PowerSeries.coeff 0) h0
    rw [map_sub, PowerSeries.coeff_zero_eq_constantCoeff, map_mul,
      ← PowerSeries.coeff_zero_eq_constantCoeff, hE0, mul_zero,
      PowerSeries.coeff_one] at hc
    norm_num at hc
  have hg_eq : g = PowerSeries.X * T_ps := by
    have h1' := (mul_eq_zero.mp hfac).resolve_left
      (mul_ne_zero (mul_ne_zero hX_ne (pow_ne_zero 3 hT_ne)) hTE_ne)
    exact sub_eq_zero.mp h1'
  intro n hn
  cases n with
  | zero => omega
  | succ m =>
    have hc := congrArg (PowerSeries.coeff (m + 1)) hg_eq
    simpa [g, PowerSeries.coeff_succ_X_mul, coeff_T_ps] using hc

end KernelMethod

section PermPrimitives

private def Avoids132 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j k : Fin n, i < j → j < k → ¬ (σ i < σ k ∧ σ k < σ j)

private def Avoids1324 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j k l : Fin n, i < j → j < k → k < l → ¬ (σ i < σ k ∧ σ k < σ j ∧ σ j < σ l)

private def Avoids24153 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ a b c d e : Fin n, a < b → b < c → c < d → d < e →
    ¬ (σ c < σ a ∧ σ a < σ e ∧ σ e < σ b ∧ σ b < σ d)

private def Avoids1342 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ i j k l : Fin n, i < j → j < k → k < l → ¬ (σ i < σ l ∧ σ l < σ j ∧ σ j < σ k)

private def Avoids13254 {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  ∀ a b c d e : Fin n, a < b → b < c → c < d → d < e →
    ¬ (σ a < σ c ∧ σ c < σ b ∧ σ b < σ e ∧ σ e < σ d)

private instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (Avoids132 σ) := by
  unfold Avoids132; infer_instance
private instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (Avoids1324 σ) := by
  unfold Avoids1324; infer_instance
private instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (Avoids24153 σ) := by
  unfold Avoids24153; infer_instance
private instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (Avoids1342 σ) := by
  unfold Avoids1342; infer_instance
private instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (Avoids13254 σ) := by
  unfold Avoids13254; infer_instance

private lemma avoids132_imp_1324 {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : Avoids132 σ) :
    Avoids1324 σ := fun i j k _ hij hjk _ ⟨h1, h2, _⟩ => h i j k hij hjk ⟨h1, h2⟩

private lemma avoids132_imp_24153 {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : Avoids132 σ) :
    Avoids24153 σ := fun a b c d e hab hbc hcd hde ⟨_, h2, h3, _⟩ =>
  h a b e hab (hbc.trans (hcd.trans hde)) ⟨h2, h3⟩

private lemma avoids132_imp_1342 {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : Avoids132 σ) :
    Avoids1342 σ := fun i j k l hij hjk hkl ⟨h1, h2, _⟩ => h i j l hij (hjk.trans hkl) ⟨h1, h2⟩

private lemma avoids132_imp_13254 {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : Avoids132 σ) :
    Avoids13254 σ := fun a b c _ _ hab hbc _ _ ⟨h1, h2, _, _⟩ => h a b c hab hbc ⟨h1, h2⟩

private lemma rev_lt_rev {n : ℕ} (x y : Fin n) : x.rev < y.rev ↔ y < x := by
  simp only [Fin.lt_def, Fin.val_rev]
  omega

private def mkPos4 {n : ℕ} (a b c d : Fin n) : Fin 4 → Fin n
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d

private def mkPos5 {n : ℕ} (a b c d e : Fin n) : Fin 5 → Fin n
  | ⟨0, _⟩ => a
  | ⟨1, _⟩ => b
  | ⟨2, _⟩ => c
  | ⟨3, _⟩ => d
  | ⟨4, _⟩ => e

private lemma avoids_4231_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Avoids σ ![4, 2, 3, 1] ↔ Avoids1324 (σ.trans Fin.revPerm) := by
  constructor
  · intro h i j k l hij hjk hkl ⟨h1, h2, h3⟩
    apply h
    refine ⟨mkPos4 i j k l, ?_, ?_⟩
    · intro x y hxy
      simp only [Fin.lt_def] at hij hjk hkl
      fin_cases x <;> fin_cases y <;> simp only [mkPos4, Fin.lt_def] at hxy ⊢ <;> omega
    · intro x y
      simp only [Equiv.trans_apply, Fin.revPerm_apply, rev_lt_rev] at h1 h2 h3
      simp only [Fin.lt_def] at h1 h2 h3
      fin_cases x <;> fin_cases y <;> simp [mkPos4] <;> (try simp only [Fin.lt_def]) <;> omega
  · intro h ⟨pos, hmono, hord⟩
    have h01 : pos 0 < pos 1 := hmono (by decide)
    have h12 : pos 1 < pos 2 := hmono (by decide)
    have h23 : pos 2 < pos 3 := hmono (by decide)
    have h1 : σ (pos 2) < σ (pos 0) := (hord 2 0).mpr (by decide)
    have h2 : σ (pos 1) < σ (pos 2) := (hord 1 2).mpr (by decide)
    have h3 : σ (pos 3) < σ (pos 1) := (hord 3 1).mpr (by decide)
    exact h (pos 0) (pos 1) (pos 2) (pos 3) h01 h12 h23
      ⟨by simpa [rev_lt_rev] using h1, by simpa [rev_lt_rev] using h2,
       by simpa [rev_lt_rev] using h3⟩

private lemma avoids_42513_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Avoids σ ![4, 2, 5, 1, 3] ↔ Avoids24153 (σ.trans Fin.revPerm) := by
  constructor
  · intro h a b c d e hab hbc hcd hde ⟨h1, h2, h3, h4⟩
    apply h
    refine ⟨mkPos5 a b c d e, ?_, ?_⟩
    · intro x y hxy
      simp only [Fin.lt_def] at hab hbc hcd hde
      fin_cases x <;> fin_cases y <;> simp only [mkPos5, Fin.lt_def] at hxy ⊢ <;> omega
    · intro x y
      simp only [Equiv.trans_apply, Fin.revPerm_apply, rev_lt_rev] at h1 h2 h3 h4
      simp only [Fin.lt_def] at h1 h2 h3 h4
      fin_cases x <;> fin_cases y <;> simp [mkPos5] <;> (try simp only [Fin.lt_def]) <;> omega
  · intro h ⟨pos, hmono, hord⟩
    have h01 : pos 0 < pos 1 := hmono (by decide)
    have h12 : pos 1 < pos 2 := hmono (by decide)
    have h23 : pos 2 < pos 3 := hmono (by decide)
    have h34 : pos 3 < pos 4 := hmono (by decide)
    have h1 : σ (pos 0) < σ (pos 2) := (hord 0 2).mpr (by decide)
    have h2 : σ (pos 4) < σ (pos 0) := (hord 4 0).mpr (by decide)
    have h3 : σ (pos 1) < σ (pos 4) := (hord 1 4).mpr (by decide)
    have h4 : σ (pos 3) < σ (pos 1) := (hord 3 1).mpr (by decide)
    exact h (pos 0) (pos 1) (pos 2) (pos 3) (pos 4) h01 h12 h23 h34
      ⟨by simpa [rev_lt_rev] using h1, by simpa [rev_lt_rev] using h2,
       by simpa [rev_lt_rev] using h3, by simpa [rev_lt_rev] using h4⟩

private lemma avoids_1342_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Avoids σ ![1, 3, 4, 2] ↔ Avoids1342 σ := by
  constructor
  · intro h i j k l hij hjk hkl ⟨h1, h2, h3⟩
    apply h
    refine ⟨mkPos4 i j k l, ?_, ?_⟩
    · intro x y hxy
      simp only [Fin.lt_def] at hij hjk hkl
      fin_cases x <;> fin_cases y <;> simp only [mkPos4, Fin.lt_def] at hxy ⊢ <;> omega
    · intro x y
      simp only [Fin.lt_def] at h1 h2 h3
      fin_cases x <;> fin_cases y <;> simp [mkPos4] <;> (try simp only [Fin.lt_def]) <;> omega
  · intro h ⟨pos, hmono, hord⟩
    exact h (pos 0) (pos 1) (pos 2) (pos 3) (hmono (by decide)) (hmono (by decide)) (hmono (by decide))
      ⟨(hord 0 3).mpr (by decide), (hord 3 1).mpr (by decide), (hord 1 2).mpr (by decide)⟩

private lemma avoids_13254_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Avoids σ ![1, 3, 2, 5, 4] ↔ Avoids13254 σ := by
  constructor
  · intro h a b c d e hab hbc hcd hde ⟨h1, h2, h3, h4⟩
    apply h
    refine ⟨mkPos5 a b c d e, ?_, ?_⟩
    · intro x y hxy
      simp only [Fin.lt_def] at hab hbc hcd hde
      fin_cases x <;> fin_cases y <;> simp only [mkPos5, Fin.lt_def] at hxy ⊢ <;> omega
    · intro x y
      simp only [Fin.lt_def] at h1 h2 h3 h4
      fin_cases x <;> fin_cases y <;> simp [mkPos5] <;> (try simp only [Fin.lt_def]) <;> omega
  · intro h ⟨pos, hmono, hord⟩
    exact h (pos 0) (pos 1) (pos 2) (pos 3) (pos 4)
      (hmono (by decide)) (hmono (by decide)) (hmono (by decide)) (hmono (by decide))
      ⟨(hord 0 2).mpr (by decide), (hord 2 1).mpr (by decide),
       (hord 1 4).mpr (by decide), (hord 4 3).mpr (by decide)⟩

/-- Skew sum of permutations `α` of length `m` and `β` of length `n - m` inside `Fin n`. -/
private def skewSumCast {n m : ℕ} (hm : m ≤ n)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))) : Equiv.Perm (Fin n) where
  toFun x :=
    if h : x.1 < m then ⟨(α ⟨x.1, h⟩).1 + (n - m), by have := (α ⟨x.1, h⟩).2; omega⟩
    else ⟨(β ⟨x.1 - m, by omega⟩).1, by have := (β ⟨x.1 - m, by omega⟩).2; omega⟩
  invFun y :=
    if h : y.1 < n - m then ⟨(β.symm ⟨y.1, h⟩).1 + m, by have := (β.symm ⟨y.1, h⟩).2; omega⟩
    else ⟨(α.symm ⟨y.1 - (n - m), by omega⟩).1, by have := (α.symm ⟨y.1 - (n - m), by omega⟩).2; omega⟩
  left_inv x := by
    ext; dsimp only
    by_cases h : x.1 < m
    · simp only [h, ↓reduceDIte]
      have h2 : ¬ (α ⟨x.1, h⟩).1 + (n - m) < n - m := by omega
      simp only [h2, ↓reduceDIte]
      have heq : (⟨(α ⟨x.1, h⟩).1 + (n - m) - (n - m), by have := (α ⟨x.1, h⟩).2; omega⟩ : Fin m) =
          α ⟨x.1, h⟩ := by ext; simp
      rw [heq]; simp
    · simp only [h, ↓reduceDIte]
      have h2 : (β ⟨x.1 - m, by omega⟩).1 < n - m := (β ⟨x.1 - m, by omega⟩).2
      simp only [h2, ↓reduceDIte]
      have heq : (⟨(β ⟨x.1 - m, by omega⟩).1, h2⟩ : Fin (n - m)) = β ⟨x.1 - m, by omega⟩ := rfl
      rw [heq]; simp; omega
  right_inv y := by
    ext; dsimp only
    by_cases h : y.1 < n - m
    · simp only [h, ↓reduceDIte]
      have h2 : ¬ (β.symm ⟨y.1, h⟩).1 + m < m := by omega
      simp only [h2, ↓reduceDIte]
      have heq : (⟨(β.symm ⟨y.1, h⟩).1 + m - m, by have := (β.symm ⟨y.1, h⟩).2; omega⟩ : Fin (n - m)) =
          β.symm ⟨y.1, h⟩ := by ext; simp
      rw [heq]; simp
    · simp only [h, ↓reduceDIte]
      have h2 : (α.symm ⟨y.1 - (n - m), by omega⟩).1 < m := (α.symm ⟨y.1 - (n - m), by omega⟩).2
      simp only [h2, ↓reduceDIte]
      have heq : (⟨(α.symm ⟨y.1 - (n - m), by omega⟩).1, h2⟩ : Fin m) =
          α.symm ⟨y.1 - (n - m), by omega⟩ := rfl
      rw [heq]; simp; omega

private lemma skewSumCast_val_lt {n m : ℕ} (hm : m ≤ n)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))) (x : Fin n) (hx : x.1 < m) :
    (skewSumCast hm α β x).1 = (α ⟨x.1, hx⟩).1 + (n - m) := by
  simp [skewSumCast, hx]

private lemma skewSumCast_val_ge {n m : ℕ} (hm : m ≤ n)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))) (x : Fin n) (hx : m ≤ x.1) :
    (skewSumCast hm α β x).1 = (β ⟨x.1 - m, by omega⟩).1 := by
  have hnot : ¬ x.1 < m := by omega
  simp [skewSumCast, hnot]

private lemma skewSumCast_lt_ge {n m : ℕ} (hm : m ≤ n)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))) (i j : Fin n)
    (hi : i.1 < m) (hj : m ≤ j.1) :
    skewSumCast hm α β j < skewSumCast hm α β i := by
  rw [Fin.lt_def, skewSumCast_val_lt hm α β i hi, skewSumCast_val_ge hm α β j hj]
  have := (β ⟨j.1 - m, by omega⟩).2
  omega

private lemma skewSumCast_inj {n m : ℕ} (hm : m ≤ n) :
    Function.Injective (fun p : Equiv.Perm (Fin m) × Equiv.Perm (Fin (n - m)) =>
      skewSumCast hm p.1 p.2) := by
  rintro ⟨α1, β1⟩ ⟨α2, β2⟩ h
  dsimp only at h
  have hα : α1 = α2 := by
    ext i
    have hx := congrArg (fun σ => (σ ⟨i.1, by omega⟩).1) h
    rw [skewSumCast_val_lt hm α1 β1 ⟨i.1, by omega⟩ i.2,
        skewSumCast_val_lt hm α2 β2 ⟨i.1, by omega⟩ i.2] at hx
    simpa using hx
  have hβ : β1 = β2 := by
    ext j
    have hx := congrArg (fun σ => (σ ⟨j.1 + m, by omega⟩).1) h
    rw [skewSumCast_val_ge hm α1 β1 ⟨j.1 + m, by omega⟩ (by dsimp; omega),
        skewSumCast_val_ge hm α2 β2 ⟨j.1 + m, by omega⟩ (by dsimp; omega)] at hx
    simpa using hx
  exact Prod.ext hα hβ

private def IsCut {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ) : Prop :=
  m ≤ n ∧ ∀ i : Fin n, i.1 < m → n - m ≤ (σ i).1

private instance {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ) : Decidable (IsCut σ m) := by
  unfold IsCut; infer_instance

private lemma isCut_zero {n : ℕ} (σ : Equiv.Perm (Fin n)) : IsCut σ 0 :=
  ⟨Nat.zero_le n, fun i hi => by omega⟩

private lemma isCut_self {n : ℕ} (σ : Equiv.Perm (Fin n)) : IsCut σ n :=
  ⟨le_rfl, fun _ _ => by simp⟩

private lemma card_fin_filter_lt {n m : ℕ} (hm : m ≤ n) :
    (Finset.univ.filter (fun x : Fin n => x.1 < m)).card = m := by
  have heq : Finset.univ.filter (fun x : Fin n => x.1 < m) =
      (Finset.univ : Finset (Fin m)).image (fun i => ⟨i.1, by omega⟩) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    exact ⟨fun hx => ⟨⟨x.1, hx⟩, rfl⟩, fun ⟨i, hi⟩ => by rw [← hi]; exact i.2⟩
  rw [heq, Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using congrArg Fin.val h)),
      Finset.card_univ, Fintype.card_fin]

private lemma card_fin_filter_ge {n m : ℕ} (hm : m ≤ n) :
    (Finset.univ.filter (fun x : Fin n => m ≤ x.1)).card = n - m := by
  have heq : Finset.univ.filter (fun x : Fin n => m ≤ x.1) =
      (Finset.univ : Finset (Fin (n - m))).image (fun i => ⟨i.1 + m, by omega⟩) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hx; refine ⟨⟨x.1 - m, by omega⟩, ?_⟩; ext; dsimp; omega
    · rintro ⟨i, rfl⟩; dsimp; omega
  rw [heq, Finset.card_image_of_injective _ (fun a b h => Fin.ext (by
    have := congrArg Fin.val h; dsimp at this; omega)),
    Finset.card_univ, Fintype.card_fin]

private lemma isCut_ge_lt {n m : ℕ} {σ : Equiv.Perm (Fin n)} (hcut : IsCut σ m)
    (j : Fin n) (hj : m ≤ j.1) : (σ j).1 < n - m := by
  by_contra hge
  push Not at hge
  let S : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i.1 < m)
  let T : Finset (Fin n) := Finset.univ.filter (fun y : Fin n => n - m ≤ y.1)
  have hScard : S.card = m := card_fin_filter_lt hcut.1
  have hTcard : T.card = m := by
    have h := card_fin_filter_ge (n := n) (m := n - m) (Nat.sub_le n m)
    have hsub : n - (n - m) = m := Nat.sub_sub_self hcut.1
    rw [hsub] at h; exact h
  have hsub : (insert j S).image σ ⊆ T := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_insert.mp hx with rfl | hxS
    · exact hge
    · exact hcut.2 x (Finset.mem_filter.mp hxS).2
  have hjnot : j ∉ S := by simp [S]; omega
  have hcard1 := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ σ.injective, Finset.card_insert_of_notMem hjnot,
      hScard, hTcard] at hcard1
  omega

private lemma isCut_skewSumCast {n m : ℕ} (hm : m ≤ n)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))) :
    IsCut (skewSumCast hm α β) m := by
  refine ⟨hm, fun i hi => ?_⟩
  rw [skewSumCast_val_lt hm α β i hi]; omega

private lemma exists_skewSumCast_of_isCut {n m : ℕ} {σ : Equiv.Perm (Fin n)} (hcut : IsCut σ m) :
    ∃ (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))), σ = skewSumCast hcut.1 α β := by
  have hge := isCut_ge_lt hcut
  have hinv_lt : ∀ y : Fin n, y.1 < n - m → m ≤ (σ.symm y).1 := by
    intro y hy
    by_contra hlt
    push_neg at hlt
    have := hcut.2 (σ.symm y) hlt
    simp at this
    omega
  have hinv_ge : ∀ y : Fin n, n - m ≤ y.1 → (σ.symm y).1 < m := by
    intro y hy
    by_contra hge'
    push_neg at hge'
    have := hge (σ.symm y) hge'
    simp at this
    omega
  let α : Equiv.Perm (Fin m) :=
    { toFun := fun i => ⟨(σ ⟨i.1, by have := hcut.1; omega⟩).1 - (n - m), by
        have := hcut.1; have := i.2; have := (σ ⟨i.1, by omega⟩).2; omega⟩
      invFun := fun y => ⟨(σ.symm ⟨y.1 + (n - m), by have := hcut.1; omega⟩).1,
        hinv_ge ⟨y.1 + (n - m), by have := hcut.1; omega⟩ (by dsimp; omega)⟩
      left_inv := fun i => by
        ext; dsimp
        have h1 := hcut.2 ⟨i.1, by have := hcut.1; omega⟩ i.2
        have h2 : (⟨(σ ⟨i.1, by have := hcut.1; omega⟩).1 - (n - m) + (n - m),
            by have := hcut.1; have := (σ ⟨i.1, by have := hcut.1; omega⟩).2; omega⟩ : Fin n) =
            σ ⟨i.1, by have := hcut.1; omega⟩ := by ext; dsimp; omega
        rw [h2]; simp
      right_inv := fun y => by
        ext; dsimp
        simp }
  let β : Equiv.Perm (Fin (n - m)) :=
    { toFun := fun j => ⟨(σ ⟨j.1 + m, by have := hcut.1; omega⟩).1,
        hge ⟨j.1 + m, by have := hcut.1; omega⟩ (by dsimp; omega)⟩
      invFun := fun y => ⟨(σ.symm ⟨y.1, by have := hcut.1; omega⟩).1 - m, by
        have := hcut.1; have := y.2; have := (σ.symm ⟨y.1, by omega⟩).2; omega⟩
      left_inv := fun j => by
        ext; dsimp
        simp
      right_inv := fun y => by
        ext; dsimp
        have h1 := hinv_lt ⟨y.1, by have := hcut.1; omega⟩ y.2
        have h2 : (⟨(σ.symm ⟨y.1, by have := hcut.1; omega⟩).1 - m + m,
            by have := hcut.1; have := (σ.symm ⟨y.1, by have := hcut.1; omega⟩).2; omega⟩ : Fin n) =
            σ.symm ⟨y.1, by have := hcut.1; omega⟩ := by ext; dsimp; omega
        rw [h2]; simp }
  refine ⟨α, β, ?_⟩
  ext x
  by_cases hx : x.1 < m
  · rw [skewSumCast_val_lt hcut.1 α β x hx]
    have h1 := hcut.2 x hx
    simp only [α, Equiv.coe_fn_mk]
    have hx' : (⟨x.1, by have := hcut.1; omega⟩ : Fin n) = x := rfl
    rw [hx']; omega
  · rw [skewSumCast_val_ge hcut.1 α β x (by omega)]
    simp only [β, Equiv.coe_fn_mk]
    have hx' : (⟨x.1 - m + m, by have := hcut.1; omega⟩ : Fin n) = x := by ext; dsimp; omega
    rw [hx']

private def IsSkewIndec {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → ¬ IsCut σ m

private instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (IsSkewIndec σ) := by
  unfold IsSkewIndec
  have : (∀ m : ℕ, 0 < m → m < n → ¬ IsCut σ m) ↔ ∀ m : Fin n, 0 < m.1 → ¬ IsCut σ m.1 :=
    ⟨fun h m hm => h m.1 hm m.2, fun h m hm hmn => h ⟨m, hmn⟩ hm⟩
  exact decidable_of_iff (0 < n ∧ ∀ m : Fin n, 0 < m.1 → ¬ IsCut σ m.1)
    (and_congr Iff.rfl this.symm)

private lemma exists_lt_of_not_isCut {n m : ℕ} {σ : Equiv.Perm (Fin n)}
    (hm0 : 0 < m) (hmn : m < n) (hnc : ¬ IsCut σ m) :
    ∃ i j : Fin n, i.1 < m ∧ m ≤ j.1 ∧ σ i < σ j := by
  have h1 : ∃ i : Fin n, i.1 < m ∧ (σ i).1 < n - m := by
    by_contra hall; push Not at hall
    exact hnc ⟨le_of_lt hmn, hall⟩
  rcases h1 with ⟨i, him, hσi⟩
  have h2 : ∃ j : Fin n, m ≤ j.1 ∧ n - m ≤ (σ j).1 := by
    by_contra hall; push Not at hall
    let R : Finset (Fin n) := Finset.univ.filter (fun x : Fin n => m ≤ x.1)
    let U : Finset (Fin n) := Finset.univ.filter (fun y : Fin n => y.1 < n - m)
    have hRcard : R.card = n - m := card_fin_filter_ge (le_of_lt hmn)
    have hUcard : U.card = n - m := card_fin_filter_lt (Nat.sub_le n m)
    have hsub : (insert i R).image σ ⊆ U := by
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨x, hx, rfl⟩
      simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
      rcases Finset.mem_insert.mp hx with rfl | hxR
      · exact hσi
      · exact hall x (Finset.mem_filter.mp hxR).2
    have hinot : i ∉ R := by simp [R]; omega
    have hcard1 := Finset.card_le_card hsub
    rw [Finset.card_image_of_injective _ σ.injective, Finset.card_insert_of_notMem hinot,
        hRcard, hUcard] at hcard1
    omega
  rcases h2 with ⟨j, hjm, hσj⟩
  exact ⟨i, j, him, hjm, by rw [Fin.lt_def]; omega⟩

private lemma isCut_skewSumCast_lt {n m k : ℕ} (hm : m ≤ n) (hk : k < m)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))) :
    IsCut (skewSumCast hm α β) k ↔ IsCut α k := by
  constructor
  · intro hcut
    refine ⟨le_of_lt hk, fun i hi => ?_⟩
    have h1 := hcut.2 ⟨i.1, by omega⟩ hi
    rw [skewSumCast_val_lt hm α β ⟨i.1, by omega⟩ i.2] at h1
    change n - k ≤ (α i).1 + (n - m) at h1
    omega
  · intro hcut
    refine ⟨by omega, fun i hi => ?_⟩
    rw [skewSumCast_val_lt hm α β i (by omega)]
    have h1 := hcut.2 ⟨i.1, by omega⟩ hi
    omega

private lemma isCut_skewSumCast_gt {n m k : ℕ} (hm : m ≤ n) (hk1 : m < k) (hk2 : k < n)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))) :
    IsCut (skewSumCast hm α β) k ↔ IsCut β (k - m) := by
  constructor
  · intro hcut
    refine ⟨by omega, fun j hj => ?_⟩
    have h1 := hcut.2 ⟨j.1 + m, by omega⟩ (by dsimp; omega)
    rw [skewSumCast_val_ge hm α β ⟨j.1 + m, by omega⟩ (by dsimp; omega)] at h1
    have hjj : (⟨j.1 + m - m, by omega⟩ : Fin (n - m)) = j := by ext; simp
    rw [hjj] at h1
    omega
  · intro hcut
    refine ⟨le_of_lt hk2, fun i hi => ?_⟩
    by_cases him : i.1 < m
    · rw [skewSumCast_val_lt hm α β i him]; omega
    · rw [skewSumCast_val_ge hm α β i (by omega)]
      have h1 := hcut.2 ⟨i.1 - m, by omega⟩ (by dsimp; omega)
      omega

private lemma avoids132_skewSumCast {n m : ℕ} (hm : m ≤ n)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))) :
    Avoids132 (skewSumCast hm α β) ↔ Avoids132 α ∧ Avoids132 β := by
  constructor
  · intro h
    refine ⟨fun i j k hij hjk ⟨h1, h2⟩ => ?_, fun i j k hij hjk ⟨h1, h2⟩ => ?_⟩
    · refine h ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ ⟨k.1, by omega⟩ hij hjk ⟨?_, ?_⟩
      · rw [Fin.lt_def, skewSumCast_val_lt hm α β _ i.2, skewSumCast_val_lt hm α β _ k.2]; exact Nat.add_lt_add_right h1 _
      · rw [Fin.lt_def, skewSumCast_val_lt hm α β _ k.2, skewSumCast_val_lt hm α β _ j.2]; exact Nat.add_lt_add_right h2 _
    · refine h ⟨i.1 + m, by omega⟩ ⟨j.1 + m, by omega⟩ ⟨k.1 + m, by omega⟩
        (Nat.add_lt_add_right hij m) (Nat.add_lt_add_right hjk m) ⟨?_, ?_⟩
      · rw [Fin.lt_def, skewSumCast_val_ge hm α β _ (by dsimp; omega), skewSumCast_val_ge hm α β _ (by dsimp; omega)]
        simpa using h1
      · rw [Fin.lt_def, skewSumCast_val_ge hm α β _ (by dsimp; omega), skewSumCast_val_ge hm α β _ (by dsimp; omega)]
        simpa using h2
  · rintro ⟨hα, hβ⟩ i j k hij hjk ⟨h1, h2⟩
    by_cases hi : i.1 < m
    · have hk : k.1 < m := by
        by_contra hge; push_neg at hge
        exact lt_asymm h1 (skewSumCast_lt_ge hm α β i k hi hge)
      have hj : j.1 < m := lt_trans hjk hk
      rw [Fin.lt_def, skewSumCast_val_lt hm α β i hi, skewSumCast_val_lt hm α β k hk] at h1
      rw [Fin.lt_def, skewSumCast_val_lt hm α β k hk, skewSumCast_val_lt hm α β j hj] at h2
      exact hα ⟨i.1, hi⟩ ⟨j.1, hj⟩ ⟨k.1, hk⟩ hij hjk ⟨by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega⟩
    · have hi' : m ≤ i.1 := by omega
      have hj' : m ≤ j.1 := le_trans hi' (le_of_lt hij)
      have hk' : m ≤ k.1 := le_trans hj' (le_of_lt hjk)
      rw [Fin.lt_def, skewSumCast_val_ge hm α β i hi', skewSumCast_val_ge hm α β k hk'] at h1
      rw [Fin.lt_def, skewSumCast_val_ge hm α β k hk', skewSumCast_val_ge hm α β j hj'] at h2
      exact hβ ⟨i.1 - m, by omega⟩ ⟨j.1 - m, by omega⟩ ⟨k.1 - m, by omega⟩
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hij; omega)
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hjk; omega)
        ⟨h1, h2⟩

private lemma avoids1324_skewSumCast {n m : ℕ} (hm : m ≤ n)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))) :
    Avoids1324 (skewSumCast hm α β) ↔ Avoids1324 α ∧ Avoids1324 β := by
  constructor
  · intro h
    refine ⟨fun i j k l hij hjk hkl ⟨h1, h2, h3⟩ => ?_, fun i j k l hij hjk hkl ⟨h1, h2, h3⟩ => ?_⟩
    · refine h ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ ⟨k.1, by omega⟩ ⟨l.1, by omega⟩ hij hjk hkl ⟨?_, ?_, ?_⟩ <;>
        (rw [Fin.lt_def, skewSumCast_val_lt hm α β _ _, skewSumCast_val_lt hm α β _ _]; exact Nat.add_lt_add_right ‹_› _)
    · refine h ⟨i.1 + m, by omega⟩ ⟨j.1 + m, by omega⟩ ⟨k.1 + m, by omega⟩ ⟨l.1 + m, by omega⟩
        (Nat.add_lt_add_right hij m) (Nat.add_lt_add_right hjk m) (Nat.add_lt_add_right hkl m) ⟨?_, ?_, ?_⟩ <;>
        (rw [Fin.lt_def, skewSumCast_val_ge hm α β _ (by dsimp; omega), skewSumCast_val_ge hm α β _ (by dsimp; omega)]; simpa using ‹_›)
  · rintro ⟨hα, hβ⟩ i j k l hij hjk hkl ⟨h1, h2, h3⟩
    by_cases hi : i.1 < m
    · have hl : l.1 < m := by
        by_contra hge; push_neg at hge
        exact lt_asymm (h1.trans (h2.trans h3)) (skewSumCast_lt_ge hm α β i l hi hge)
      have hj : j.1 < m := lt_trans (hjk.trans hkl) hl
      have hk : k.1 < m := lt_trans hkl hl
      rw [Fin.lt_def, skewSumCast_val_lt hm α β i hi, skewSumCast_val_lt hm α β k hk] at h1
      rw [Fin.lt_def, skewSumCast_val_lt hm α β k hk, skewSumCast_val_lt hm α β j hj] at h2
      rw [Fin.lt_def, skewSumCast_val_lt hm α β j hj, skewSumCast_val_lt hm α β l hl] at h3
      exact hα ⟨i.1, hi⟩ ⟨j.1, hj⟩ ⟨k.1, hk⟩ ⟨l.1, hl⟩ hij hjk hkl
        ⟨by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega⟩
    · have hi' : m ≤ i.1 := by omega
      have hj' : m ≤ j.1 := le_trans hi' (le_of_lt hij)
      have hk' : m ≤ k.1 := le_trans hj' (le_of_lt hjk)
      have hl' : m ≤ l.1 := le_trans hk' (le_of_lt hkl)
      rw [Fin.lt_def, skewSumCast_val_ge hm α β i hi', skewSumCast_val_ge hm α β k hk'] at h1
      rw [Fin.lt_def, skewSumCast_val_ge hm α β k hk', skewSumCast_val_ge hm α β j hj'] at h2
      rw [Fin.lt_def, skewSumCast_val_ge hm α β j hj', skewSumCast_val_ge hm α β l hl'] at h3
      exact hβ ⟨i.1 - m, by omega⟩ ⟨j.1 - m, by omega⟩ ⟨k.1 - m, by omega⟩ ⟨l.1 - m, by omega⟩
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hij; omega)
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hjk; omega)
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hkl; omega)
        ⟨h1, h2, h3⟩

private lemma avoids24153_skewSumCast {n m : ℕ} (hm : m ≤ n)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))) :
    Avoids24153 (skewSumCast hm α β) ↔ Avoids24153 α ∧ Avoids24153 β := by
  constructor
  · intro h
    refine ⟨fun a b c d e hab hbc hcd hde ⟨h1, h2, h3, h4⟩ => ?_,
            fun a b c d e hab hbc hcd hde ⟨h1, h2, h3, h4⟩ => ?_⟩
    · refine h ⟨a.1, by omega⟩ ⟨b.1, by omega⟩ ⟨c.1, by omega⟩ ⟨d.1, by omega⟩ ⟨e.1, by omega⟩
        hab hbc hcd hde ⟨?_, ?_, ?_, ?_⟩ <;>
        (rw [Fin.lt_def, skewSumCast_val_lt hm α β _ _, skewSumCast_val_lt hm α β _ _]; exact Nat.add_lt_add_right ‹_› _)
    · refine h ⟨a.1 + m, by omega⟩ ⟨b.1 + m, by omega⟩ ⟨c.1 + m, by omega⟩ ⟨d.1 + m, by omega⟩ ⟨e.1 + m, by omega⟩
        (Nat.add_lt_add_right hab m) (Nat.add_lt_add_right hbc m)
        (Nat.add_lt_add_right hcd m) (Nat.add_lt_add_right hde m) ⟨?_, ?_, ?_, ?_⟩ <;>
        (rw [Fin.lt_def, skewSumCast_val_ge hm α β _ (by dsimp; omega), skewSumCast_val_ge hm α β _ (by dsimp; omega)]; simpa using ‹_›)
  · rintro ⟨hα, hβ⟩ a b c d e hab hbc hcd hde ⟨h1, h2, h3, h4⟩
    by_cases ha : a.1 < m
    · have he : e.1 < m := by
        by_contra hge; push_neg at hge
        exact lt_asymm h2 (skewSumCast_lt_ge hm α β a e ha hge)
      have hb : b.1 < m := lt_trans (hbc.trans (hcd.trans hde)) he
      have hc : c.1 < m := lt_trans (hcd.trans hde) he
      have hd : d.1 < m := lt_trans hde he
      rw [Fin.lt_def, skewSumCast_val_lt hm α β c hc, skewSumCast_val_lt hm α β a ha] at h1
      rw [Fin.lt_def, skewSumCast_val_lt hm α β a ha, skewSumCast_val_lt hm α β e he] at h2
      rw [Fin.lt_def, skewSumCast_val_lt hm α β e he, skewSumCast_val_lt hm α β b hb] at h3
      rw [Fin.lt_def, skewSumCast_val_lt hm α β b hb, skewSumCast_val_lt hm α β d hd] at h4
      exact hα ⟨a.1, ha⟩ ⟨b.1, hb⟩ ⟨c.1, hc⟩ ⟨d.1, hd⟩ ⟨e.1, he⟩ hab hbc hcd hde
        ⟨by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega,
         by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega⟩
    · have ha' : m ≤ a.1 := by omega
      have hb' : m ≤ b.1 := le_trans ha' (le_of_lt hab)
      have hc' : m ≤ c.1 := le_trans hb' (le_of_lt hbc)
      have hd' : m ≤ d.1 := le_trans hc' (le_of_lt hcd)
      have he' : m ≤ e.1 := le_trans hd' (le_of_lt hde)
      rw [Fin.lt_def, skewSumCast_val_ge hm α β c hc', skewSumCast_val_ge hm α β a ha'] at h1
      rw [Fin.lt_def, skewSumCast_val_ge hm α β a ha', skewSumCast_val_ge hm α β e he'] at h2
      rw [Fin.lt_def, skewSumCast_val_ge hm α β e he', skewSumCast_val_ge hm α β b hb'] at h3
      rw [Fin.lt_def, skewSumCast_val_ge hm α β b hb', skewSumCast_val_ge hm α β d hd'] at h4
      exact hβ ⟨a.1 - m, by omega⟩ ⟨b.1 - m, by omega⟩ ⟨c.1 - m, by omega⟩ ⟨d.1 - m, by omega⟩ ⟨e.1 - m, by omega⟩
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hab; omega)
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hbc; omega)
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hcd; omega)
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hde; omega)
        ⟨h1, h2, h3, h4⟩

private lemma avoids1342_skewSumCast {n m : ℕ} (hm : m ≤ n)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))) :
    Avoids1342 (skewSumCast hm α β) ↔ Avoids1342 α ∧ Avoids1342 β := by
  constructor
  · intro h
    refine ⟨fun i j k l hij hjk hkl ⟨h1, h2, h3⟩ => ?_, fun i j k l hij hjk hkl ⟨h1, h2, h3⟩ => ?_⟩
    · refine h ⟨i.1, by omega⟩ ⟨j.1, by omega⟩ ⟨k.1, by omega⟩ ⟨l.1, by omega⟩ hij hjk hkl ⟨?_, ?_, ?_⟩ <;>
        (rw [Fin.lt_def, skewSumCast_val_lt hm α β _ _, skewSumCast_val_lt hm α β _ _]; exact Nat.add_lt_add_right ‹_› _)
    · refine h ⟨i.1 + m, by omega⟩ ⟨j.1 + m, by omega⟩ ⟨k.1 + m, by omega⟩ ⟨l.1 + m, by omega⟩
        (Nat.add_lt_add_right hij m) (Nat.add_lt_add_right hjk m) (Nat.add_lt_add_right hkl m) ⟨?_, ?_, ?_⟩ <;>
        (rw [Fin.lt_def, skewSumCast_val_ge hm α β _ (by dsimp; omega), skewSumCast_val_ge hm α β _ (by dsimp; omega)]; simpa using ‹_›)
  · rintro ⟨hα, hβ⟩ i j k l hij hjk hkl ⟨h1, h2, h3⟩
    by_cases hi : i.1 < m
    · have hl : l.1 < m := by
        by_contra hge; push_neg at hge
        exact lt_asymm h1 (skewSumCast_lt_ge hm α β i l hi hge)
      have hj : j.1 < m := lt_trans (hjk.trans hkl) hl
      have hk : k.1 < m := lt_trans hkl hl
      rw [Fin.lt_def, skewSumCast_val_lt hm α β i hi, skewSumCast_val_lt hm α β l hl] at h1
      rw [Fin.lt_def, skewSumCast_val_lt hm α β l hl, skewSumCast_val_lt hm α β j hj] at h2
      rw [Fin.lt_def, skewSumCast_val_lt hm α β j hj, skewSumCast_val_lt hm α β k hk] at h3
      exact hα ⟨i.1, hi⟩ ⟨j.1, hj⟩ ⟨k.1, hk⟩ ⟨l.1, hl⟩ hij hjk hkl
        ⟨by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega⟩
    · have hi' : m ≤ i.1 := by omega
      have hj' : m ≤ j.1 := le_trans hi' (le_of_lt hij)
      have hk' : m ≤ k.1 := le_trans hj' (le_of_lt hjk)
      have hl' : m ≤ l.1 := le_trans hk' (le_of_lt hkl)
      rw [Fin.lt_def, skewSumCast_val_ge hm α β i hi', skewSumCast_val_ge hm α β l hl'] at h1
      rw [Fin.lt_def, skewSumCast_val_ge hm α β l hl', skewSumCast_val_ge hm α β j hj'] at h2
      rw [Fin.lt_def, skewSumCast_val_ge hm α β j hj', skewSumCast_val_ge hm α β k hk'] at h3
      exact hβ ⟨i.1 - m, by omega⟩ ⟨j.1 - m, by omega⟩ ⟨k.1 - m, by omega⟩ ⟨l.1 - m, by omega⟩
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hij; omega)
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hjk; omega)
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hkl; omega)
        ⟨h1, h2, h3⟩

private lemma avoids13254_skewSumCast {n m : ℕ} (hm : m ≤ n)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))) :
    Avoids13254 (skewSumCast hm α β) ↔ Avoids13254 α ∧ Avoids13254 β := by
  constructor
  · intro h
    refine ⟨fun a b c d e hab hbc hcd hde ⟨h1, h2, h3, h4⟩ => ?_,
            fun a b c d e hab hbc hcd hde ⟨h1, h2, h3, h4⟩ => ?_⟩
    · refine h ⟨a.1, by omega⟩ ⟨b.1, by omega⟩ ⟨c.1, by omega⟩ ⟨d.1, by omega⟩ ⟨e.1, by omega⟩
        hab hbc hcd hde ⟨?_, ?_, ?_, ?_⟩ <;>
        (rw [Fin.lt_def, skewSumCast_val_lt hm α β _ _, skewSumCast_val_lt hm α β _ _]; exact Nat.add_lt_add_right ‹_› _)
    · refine h ⟨a.1 + m, by omega⟩ ⟨b.1 + m, by omega⟩ ⟨c.1 + m, by omega⟩ ⟨d.1 + m, by omega⟩ ⟨e.1 + m, by omega⟩
        (Nat.add_lt_add_right hab m) (Nat.add_lt_add_right hbc m)
        (Nat.add_lt_add_right hcd m) (Nat.add_lt_add_right hde m) ⟨?_, ?_, ?_, ?_⟩ <;>
        (rw [Fin.lt_def, skewSumCast_val_ge hm α β _ (by dsimp; omega), skewSumCast_val_ge hm α β _ (by dsimp; omega)]; simpa using ‹_›)
  · rintro ⟨hα, hβ⟩ a b c d e hab hbc hcd hde ⟨h1, h2, h3, h4⟩
    by_cases ha : a.1 < m
    · have he : e.1 < m := by
        by_contra hge; push_neg at hge
        exact lt_asymm (h1.trans (h2.trans h3)) (skewSumCast_lt_ge hm α β a e ha hge)
      have hb : b.1 < m := lt_trans (hbc.trans (hcd.trans hde)) he
      have hc : c.1 < m := lt_trans (hcd.trans hde) he
      have hd : d.1 < m := lt_trans hde he
      rw [Fin.lt_def, skewSumCast_val_lt hm α β a ha, skewSumCast_val_lt hm α β c hc] at h1
      rw [Fin.lt_def, skewSumCast_val_lt hm α β c hc, skewSumCast_val_lt hm α β b hb] at h2
      rw [Fin.lt_def, skewSumCast_val_lt hm α β b hb, skewSumCast_val_lt hm α β e he] at h3
      rw [Fin.lt_def, skewSumCast_val_lt hm α β e he, skewSumCast_val_lt hm α β d hd] at h4
      exact hα ⟨a.1, ha⟩ ⟨b.1, hb⟩ ⟨c.1, hc⟩ ⟨d.1, hd⟩ ⟨e.1, he⟩ hab hbc hcd hde
        ⟨by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega,
         by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega⟩
    · have ha' : m ≤ a.1 := by omega
      have hb' : m ≤ b.1 := le_trans ha' (le_of_lt hab)
      have hc' : m ≤ c.1 := le_trans hb' (le_of_lt hbc)
      have hd' : m ≤ d.1 := le_trans hc' (le_of_lt hcd)
      have he' : m ≤ e.1 := le_trans hd' (le_of_lt hde)
      rw [Fin.lt_def, skewSumCast_val_ge hm α β a ha', skewSumCast_val_ge hm α β c hc'] at h1
      rw [Fin.lt_def, skewSumCast_val_ge hm α β c hc', skewSumCast_val_ge hm α β b hb'] at h2
      rw [Fin.lt_def, skewSumCast_val_ge hm α β b hb', skewSumCast_val_ge hm α β e he'] at h3
      rw [Fin.lt_def, skewSumCast_val_ge hm α β e he', skewSumCast_val_ge hm α β d hd'] at h4
      exact hβ ⟨a.1 - m, by omega⟩ ⟨b.1 - m, by omega⟩ ⟨c.1 - m, by omega⟩ ⟨d.1 - m, by omega⟩ ⟨e.1 - m, by omega⟩
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hab; omega)
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hbc; omega)
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hcd; omega)
        (by rw [Fin.lt_def]; dsimp; rw [Fin.lt_def] at hde; omega)
        ⟨h1, h2, h3, h4⟩

/-- Unique first skew-indecomposable component decomposition of any nonempty permutation. -/
private lemma skewDecompFirst_card (P : ∀ {n : ℕ}, Equiv.Perm (Fin n) → Prop)
    [∀ n, DecidablePred (P (n := n))]
    (hP : ∀ {n m : ℕ} (hm : m ≤ n) (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))),
      P (skewSumCast hm α β) ↔ P α ∧ P β)
    (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {σ : Equiv.Perm (Fin n) // P σ} =
      ∑ m ∈ Finset.range n,
        Fintype.card {α : Equiv.Perm (Fin (m + 1)) // P α ∧ IsSkewIndec α} *
          Fintype.card {β : Equiv.Perm (Fin (n - (m + 1))) // P β} := by
  let S := Σ m : Fin n,
    {α : Equiv.Perm (Fin (m.1 + 1)) // P α ∧ IsSkewIndec α} ×
    {β : Equiv.Perm (Fin (n - (m.1 + 1))) // P β}
  let toPerm : S → {σ : Equiv.Perm (Fin n) // P σ} := fun ⟨m, ⟨α, hαP, _⟩, ⟨β, hβP⟩⟩ =>
    ⟨skewSumCast (by omega : m.1 + 1 ≤ n) α β, (hP (by omega) α β).mpr ⟨hαP, hβP⟩⟩
  have hbij : Function.Bijective toPerm := by
    constructor
    · rintro ⟨m1, ⟨α1, hα1P, hα1I⟩, ⟨β1, hβ1P⟩⟩ ⟨m2, ⟨α2, hα2P, hα2I⟩, ⟨β2, hβ2P⟩⟩ heq
      have hpeq : skewSumCast (by omega : m1.1 + 1 ≤ n) α1 β1 =
          skewSumCast (by omega : m2.1 + 1 ≤ n) α2 β2 := congrArg Subtype.val heq
      have hm_eq : m1 = m2 := by
        by_contra hne
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
        · have hcut : IsCut (skewSumCast (by omega : m2.1 + 1 ≤ n) α2 β2) (m1.1 + 1) := by
            rw [← hpeq]; exact isCut_skewSumCast _ α1 β1
          rw [isCut_skewSumCast_lt _ (by omega : m1.1 + 1 < m2.1 + 1)] at hcut
          exact hα2I.2 (m1.1 + 1) (by omega) (by omega) hcut
        · have hcut : IsCut (skewSumCast (by omega : m1.1 + 1 ≤ n) α1 β1) (m2.1 + 1) := by
            rw [hpeq]; exact isCut_skewSumCast _ α2 β2
          rw [isCut_skewSumCast_lt _ (by omega : m2.1 + 1 < m1.1 + 1)] at hcut
          exact hα1I.2 (m2.1 + 1) (by omega) (by omega) hcut
      subst hm_eq
      have hinj := @skewSumCast_inj n (m1.1 + 1) (by omega) (α1, β1) (α2, β2) hpeq
      rcases Prod.mk.inj hinj with ⟨rfl, rfl⟩
      rfl
    · rintro ⟨σ, hσP⟩
      let cuts : Finset (Fin n) := Finset.univ.filter (fun m : Fin n => IsCut σ (m.1 + 1))
      have hne : cuts.Nonempty := ⟨⟨n - 1, by omega⟩, by
        simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [show n - 1 + 1 = n by omega]; exact isCut_self σ⟩
      let m := cuts.min' hne
      have hm_cut : IsCut σ (m.1 + 1) := (Finset.mem_filter.mp (Finset.min'_mem cuts hne)).2
      rcases exists_skewSumCast_of_isCut hm_cut with ⟨α, β, hσeq⟩
      have hαβ : P α ∧ P β := (hP hm_cut.1 α β).mp (hσeq ▸ hσP)
      have hαI : IsSkewIndec α := by
        refine ⟨by omega, fun k hk0 hkm hcutk => ?_⟩
        have hcutσ : IsCut σ k := by
          rw [hσeq]; exact (isCut_skewSumCast_lt hm_cut.1 hkm α β).mpr hcutk
        have hmem : (⟨k - 1, by omega⟩ : Fin n) ∈ cuts := by
          simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [show k - 1 + 1 = k by omega]; exact hcutσ
        have hle := Finset.min'_le cuts _ hmem
        have : m.1 ≤ k - 1 := hle
        omega
      refine ⟨⟨m, ⟨α, hαβ.1, hαI⟩, ⟨β, hαβ.2⟩⟩, Subtype.ext hσeq.symm⟩
  rw [← Fintype.card_of_bijective hbij]
  simp only [S, Fintype.card_sigma, Fintype.card_prod]
  exact Fin.sum_univ_eq_sum_range (fun m =>
    Fintype.card {α : Equiv.Perm (Fin (m + 1)) // P α ∧ IsSkewIndec α} *
      Fintype.card {β : Equiv.Perm (Fin (n - (m + 1))) // P β}) n

/-- Unique last skew-indecomposable component decomposition of any nonempty permutation. -/
private noncomputable def skewDecompLastEquiv (n : ℕ) (hn : 1 ≤ n) :
    Equiv.Perm (Fin n) ≃
      Σ m : Fin n, Equiv.Perm (Fin m.1) × {α : Equiv.Perm (Fin (n - m.1)) // IsSkewIndec α} := by
  refine Equiv.ofBijective
    (fun (p : Σ m : Fin n, Equiv.Perm (Fin m.1) × {α : Equiv.Perm (Fin (n - m.1)) // IsSkewIndec α}) =>
      skewSumCast (le_of_lt p.1.2) p.2.1 p.2.2.1) ?_ |>.symm
  constructor
  · rintro ⟨m1, β1, ⟨α1, hα1⟩⟩ ⟨m2, β2, ⟨α2, hα2⟩⟩ heq
    dsimp only at heq
    have hm_eq : m1 = m2 := by
      by_contra hne
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
      · have hcut : IsCut (skewSumCast (le_of_lt m1.2) β1 α1) m2.1 := by
          rw [heq]; exact isCut_skewSumCast (le_of_lt m2.2) β2 α2
        rw [isCut_skewSumCast_gt (le_of_lt m1.2) hlt m2.2] at hcut
        exact hα1.2 (m2.1 - m1.1) (by omega) (by omega) hcut
      · have hcut : IsCut (skewSumCast (le_of_lt m2.2) β2 α2) m1.1 := by
          rw [← heq]; exact isCut_skewSumCast (le_of_lt m1.2) β1 α1
        rw [isCut_skewSumCast_gt (le_of_lt m2.2) hgt m1.2] at hcut
        exact hα2.2 (m1.1 - m2.1) (by omega) (by omega) hcut
    subst hm_eq
    have hinj := @skewSumCast_inj n m1.1 (le_of_lt m1.2) (β1, α1) (β2, α2) heq
    rcases Prod.mk.inj hinj with ⟨rfl, rfl⟩
    rfl
  · intro σ
    let cuts : Finset (Fin n) := Finset.univ.filter (fun m : Fin n => IsCut σ m.1)
    have hne : cuts.Nonempty := ⟨⟨0, by omega⟩, by
      simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and]
      exact isCut_zero σ⟩
    let m := cuts.max' hne
    have hm_cut : IsCut σ m.1 := (Finset.mem_filter.mp (Finset.max'_mem cuts hne)).2
    rcases exists_skewSumCast_of_isCut hm_cut with ⟨β, α, hσeq⟩
    have hαI : IsSkewIndec α := by
      refine ⟨by omega, fun k hk0 hkn hcutk => ?_⟩
      have hcutσ : IsCut σ (m.1 + k) := by
        rw [hσeq]
        have hgt := isCut_skewSumCast_gt hm_cut.1 (by omega : m.1 < m.1 + k) (by omega : m.1 + k < n) β α
        rw [Nat.add_sub_cancel_left] at hgt
        exact hgt.mpr hcutk
      have hmem : (⟨m.1 + k, by omega⟩ : Fin n) ∈ cuts := by
        simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and]
        exact hcutσ
      have hle := Finset.le_max' cuts _ hmem
      have : m.1 + k ≤ m.1 := hle
      omega
    exact ⟨⟨m, β, ⟨α, hαI⟩⟩, hσeq.symm⟩

private lemma invert_card_eq
    (P Q : ∀ {n : ℕ}, Equiv.Perm (Fin n) → Prop)
    [∀ n, DecidablePred (P (n := n))] [∀ n, DecidablePred (Q (n := n))]
    (hP : ∀ {n m : ℕ} (hm : m ≤ n) (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))),
      P (skewSumCast hm α β) ↔ P α ∧ P β)
    (hQ : ∀ {n m : ℕ} (hm : m ≤ n) (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))),
      Q (skewSumCast hm α β) ↔ Q α ∧ Q β)
    (hP0 : P (1 : Equiv.Perm (Fin 0))) (hQ0 : Q (1 : Equiv.Perm (Fin 0)))
    (hind : ∀ n : ℕ, 1 ≤ n →
      Fintype.card {α : Equiv.Perm (Fin n) // P α ∧ IsSkewIndec α} =
      Fintype.card {α : Equiv.Perm (Fin n) // Q α ∧ IsSkewIndec α}) :
    ∀ n : ℕ,
      Fintype.card {σ : Equiv.Perm (Fin n) // P σ} =
      Fintype.card {σ : Equiv.Perm (Fin n) // Q σ} := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      have h1 : Fintype.card {σ : Equiv.Perm (Fin 0) // P σ} = 1 :=
        Fintype.card_eq_one_iff.mpr ⟨⟨1, hP0⟩, fun ⟨x, _⟩ => Subtype.ext (Subsingleton.elim x 1)⟩
      have h2 : Fintype.card {σ : Equiv.Perm (Fin 0) // Q σ} = 1 :=
        Fintype.card_eq_one_iff.mpr ⟨⟨1, hQ0⟩, fun ⟨x, _⟩ => Subtype.ext (Subsingleton.elim x 1)⟩
      rw [h1, h2]
    | succ n =>
      rw [skewDecompFirst_card P hP (n + 1) (by omega),
          skewDecompFirst_card Q hQ (n + 1) (by omega)]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmn : m < n + 1 := Finset.mem_range.mp hm
      rw [hind (m + 1) (by omega), ih (n + 1 - (m + 1)) (by omega)]

/-- Insert maximum value `n` at position `pos` in a permutation of `Fin n`. -/
private def insMax {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1)) : Equiv.Perm (Fin (n + 1)) where
  toFun x :=
    if h1 : x.1 < pos.1 then ⟨(σ ⟨x.1, by omega⟩).1, by have := (σ ⟨x.1, by omega⟩).2; omega⟩
    else if h2 : x.1 = pos.1 then ⟨n, by omega⟩
    else ⟨(σ ⟨x.1 - 1, by omega⟩).1, by have := (σ ⟨x.1 - 1, by omega⟩).2; omega⟩
  invFun y :=
    if h : y.1 < n then
      if (σ.symm ⟨y.1, h⟩).1 < pos.1 then ⟨(σ.symm ⟨y.1, h⟩).1, by have := (σ.symm ⟨y.1, h⟩).2; omega⟩
      else ⟨(σ.symm ⟨y.1, h⟩).1 + 1, by have := (σ.symm ⟨y.1, h⟩).2; omega⟩
    else pos
  left_inv x := by
    ext; dsimp only
    by_cases h1 : x.1 < pos.1
    · simp only [h1, ↓reduceDIte]
      have hlt : (σ ⟨x.1, by omega⟩).1 < n := (σ ⟨x.1, by omega⟩).2
      simp only [hlt, ↓reduceDIte]
      have hsym : σ.symm ⟨(σ ⟨x.1, by omega⟩).1, hlt⟩ = ⟨x.1, by omega⟩ := by simp
      simp only [hsym, h1, ↓reduceIte]
    · by_cases h2 : x.1 = pos.1
      · simp only [h2, ↓reduceDIte, lt_irrefl]
      · simp only [h1, h2, ↓reduceDIte]
        have hlt : (σ ⟨x.1 - 1, by omega⟩).1 < n := (σ ⟨x.1 - 1, by omega⟩).2
        simp only [hlt, ↓reduceDIte]
        have hsym : σ.symm ⟨(σ ⟨x.1 - 1, by omega⟩).1, hlt⟩ = ⟨x.1 - 1, by omega⟩ := by simp
        have hnot : ¬ x.1 - 1 < pos.1 := by omega
        simp only [hsym, hnot, ↓reduceIte]
        omega
  right_inv y := by
    ext; dsimp only
    by_cases h : y.1 < n
    · simp only [h, ↓reduceDIte]
      split_ifs with h1 h2 h3
      · change (σ (σ.symm ⟨y.1, h⟩)).1 = y.1; simp
      · dsimp only at h2; omega
      · dsimp only at h3; omega
      · change (σ ⟨(σ.symm ⟨y.1, h⟩).1 + 1 - 1, _⟩).1 = y.1; simp
    · simp only [h, ↓reduceDIte, lt_irrefl, ↓reduceDIte]
      omega

private lemma insMax_val_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos x : Fin (n + 1)) (hx : x.1 < pos.1) :
    (insMax σ pos x).1 = (σ ⟨x.1, by omega⟩).1 := by
  simp only [insMax, Equiv.coe_fn_mk, hx, ↓reduceDIte]

private lemma insMax_val_eq {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1)) :
    (insMax σ pos pos).1 = n := by
  simp only [insMax, Equiv.coe_fn_mk, lt_irrefl, ↓reduceDIte]

private lemma insMax_val_gt {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos x : Fin (n + 1)) (hx : pos.1 < x.1) :
    (insMax σ pos x).1 = (σ ⟨x.1 - 1, by omega⟩).1 := by
  have h1 : ¬ x.1 < pos.1 := by omega
  have h2 : ¬ x.1 = pos.1 := by omega
  simp only [insMax, Equiv.coe_fn_mk, h1, h2, ↓reduceDIte]

private lemma insMax_bijective (n : ℕ) :
    Function.Bijective (fun p : Equiv.Perm (Fin n) × Fin (n + 1) => insMax p.1 p.2) := by
  constructor
  · rintro ⟨σ1, p1⟩ ⟨σ2, p2⟩ heq
    dsimp only at heq
    have hp : p1 = p2 := by
      have h1 : insMax σ1 p1 p1 = ⟨n, by omega⟩ := Fin.ext (insMax_val_eq σ1 p1)
      have h2 : insMax σ2 p2 p2 = ⟨n, by omega⟩ := Fin.ext (insMax_val_eq σ2 p2)
      rw [heq] at h1
      exact (insMax σ2 p2).injective (h1.trans h2.symm)
    subst hp
    have hσ : σ1 = σ2 := by
      ext i
      by_cases hi : i.1 < p1.1
      · have hx := congrArg (fun τ => (τ ⟨i.1, by omega⟩).1) heq
        rw [insMax_val_lt σ1 p1 ⟨i.1, by omega⟩ hi, insMax_val_lt σ2 p1 ⟨i.1, by omega⟩ hi] at hx
        exact hx
      · have hx := congrArg (fun τ => (τ ⟨i.1 + 1, by omega⟩).1) heq
        rw [insMax_val_gt σ1 p1 ⟨i.1 + 1, by omega⟩ (by dsimp; omega),
            insMax_val_gt σ2 p1 ⟨i.1 + 1, by omega⟩ (by dsimp; omega)] at hx
        simpa using hx
    exact Prod.ext hσ rfl
  · intro τ
    let pos : Fin (n + 1) := τ.symm ⟨n, by omega⟩
    have hpos_val : τ pos = ⟨n, by omega⟩ := by simp [pos]
    let σ : Equiv.Perm (Fin n) :=
      { toFun := fun i =>
          let x : Fin (n + 1) := if i.1 < pos.1 then ⟨i.1, by omega⟩ else ⟨i.1 + 1, by omega⟩
          ⟨(τ x).1, by
            have hne : x ≠ pos := by
              intro h; have := congrArg Fin.val h; dsimp only [x] at this
              split_ifs at this <;> (dsimp at this; omega)
            have hτne : τ x ≠ ⟨n, by omega⟩ := fun h => hne (τ.injective (h.trans hpos_val.symm))
            have hval : (τ x).1 ≠ n := fun h => hτne (Fin.ext h)
            have := (τ x).2; omega⟩
        invFun := fun y =>
          let x := τ.symm ⟨y.1, by omega⟩
          if hx : x.1 < pos.1 then ⟨x.1, by have := pos.2; omega⟩
          else ⟨x.1 - 1, by
            have hxne : x ≠ pos := fun h => by
              have h1 : τ x = τ pos := congrArg τ h
              rw [hpos_val] at h1
              have h2 : τ x = ⟨y.1, by omega⟩ := by simp [x]
              rw [h2] at h1
              have := congrArg Fin.val h1; dsimp at this; omega
            have hxval : x.1 ≠ pos.1 := fun h => hxne (Fin.ext h)
            have := x.2; omega⟩
        left_inv := fun i => by
          ext; dsimp only
          by_cases hi : i.1 < pos.1
          · simp only [hi, ↓reduceIte]
            have h1 : (⟨(τ ⟨i.1, by omega⟩).1, by omega⟩ : Fin (n + 1)) = τ ⟨i.1, by omega⟩ := rfl
            simp only [h1, Equiv.symm_apply_apply, hi, ↓reduceDIte]
          · simp only [hi, ↓reduceIte]
            have h1 : (⟨(τ ⟨i.1 + 1, by omega⟩).1, by omega⟩ : Fin (n + 1)) = τ ⟨i.1 + 1, by omega⟩ := rfl
            have hnot : ¬ i.1 + 1 < pos.1 := by omega
            simp only [h1, Equiv.symm_apply_apply, hnot, ↓reduceDIte, Nat.add_sub_cancel]
        right_inv := fun y => by
          ext; dsimp only
          set x := τ.symm ⟨y.1, by omega⟩
          have hxne : x ≠ pos := fun h => by
            have h1 : τ x = τ pos := congrArg τ h
            rw [hpos_val] at h1
            have h2 : τ x = ⟨y.1, by omega⟩ := by simp [x]
            rw [h2] at h1
            have := congrArg Fin.val h1; dsimp at this; omega
          have hxval : x.1 ≠ pos.1 := fun h => hxne (Fin.ext h)
          split_ifs with h1 h2
          · change (τ (τ.symm ⟨y.1, by omega⟩)).1 = y.1; simp
          · dsimp only at h2; omega
          · have hxeq : (⟨(τ.symm ⟨y.1, by omega⟩).1 - 1 + 1, by omega⟩ : Fin (n + 1)) =
                τ.symm ⟨y.1, by omega⟩ := by ext; dsimp; omega
            rw [hxeq]; simp }
    refine ⟨⟨σ, pos⟩, ?_⟩
    ext x
    by_cases h1 : x.1 < pos.1
    · rw [insMax_val_lt σ pos x h1]; simp only [σ, Equiv.coe_fn_mk, h1, ↓reduceIte]
    · by_cases h2 : x.1 = pos.1
      · have hx : x = pos := Fin.ext h2
        subst hx; rw [insMax_val_eq, hpos_val]
      · rw [insMax_val_gt σ pos x (by omega)]; simp only [σ, Equiv.coe_fn_mk]
        have hnot : ¬ x.1 - 1 < pos.1 := by omega
        simp only [hnot, ↓reduceIte]
        have hx' : (⟨x.1 - 1 + 1, by omega⟩ : Fin (n + 1)) = x := by ext; dsimp; omega
        rw [hx']

private lemma avoids132_insMax_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1)) :
    Avoids132 (insMax σ pos) ↔ Avoids132 σ ∧ IsCut σ pos.1 := by
  constructor
  · intro h
    refine ⟨fun i j k hij hjk ⟨h1, h2⟩ => ?_, ⟨by omega, ?_⟩⟩
    · let f : Fin n → Fin (n + 1) := fun t => if t.1 < pos.1 then ⟨t.1, by omega⟩ else ⟨t.1 + 1, by omega⟩
      have hf_mono : ∀ u v : Fin n, u < v → f u < f v := by
        intro u v huv; simp only [f, Fin.lt_def] at huv ⊢; split_ifs <;> (dsimp; omega)
      have hf_val : ∀ u : Fin n, (insMax σ pos (f u)).1 = (σ u).1 := by
        intro u; dsimp only [f]; split_ifs with hu
        · rw [insMax_val_lt σ pos _ hu]
        · rw [insMax_val_gt σ pos _ (by dsimp; omega)]; simp
      exact h (f i) (f j) (f k) (hf_mono i j hij) (hf_mono j k hjk)
        ⟨by rw [Fin.lt_def, hf_val, hf_val]; exact h1,
         by rw [Fin.lt_def, hf_val, hf_val]; exact h2⟩
    · by_contra hnc
      have hpos0 : 0 < pos.1 := by
        by_contra hz; apply hnc; intro i hi; omega
      have hposn : pos.1 < n := by
        by_contra hge; apply hnc; intro i _; omega
      have hnotcut : ¬ IsCut σ pos.1 := fun hc => hnc hc.2
      rcases exists_lt_of_not_isCut hpos0 hposn hnotcut with ⟨i, j, hi, hj, hσij⟩
      refine h ⟨i.1, by omega⟩ pos ⟨j.1 + 1, by omega⟩ (by rw [Fin.lt_def]; exact hi)
        (by rw [Fin.lt_def]; dsimp; omega) ⟨?_, ?_⟩
      · rw [Fin.lt_def, insMax_val_lt σ pos _ hi, insMax_val_gt σ pos _ (by dsimp; omega)]
        simpa using hσij
      · rw [Fin.lt_def, insMax_val_gt σ pos _ (by dsimp; omega), insMax_val_eq]
        exact (σ ⟨j.1 + 1 - 1, by omega⟩).2
  · rintro ⟨hσ, hcut⟩ i j k hij hjk ⟨h1, h2⟩
    have hneq_i : i.1 ≠ pos.1 := by
      intro heq
      have hmax : (insMax σ pos i).1 = n := by rw [Fin.ext heq]; exact insMax_val_eq σ pos
      have hle : (insMax σ pos k).1 < n + 1 := (insMax σ pos k).2
      rw [Fin.lt_def] at h1 h2; omega
    have hneq_k : k.1 ≠ pos.1 := by
      intro heq
      have hmax : (insMax σ pos k).1 = n := by rw [Fin.ext heq]; exact insMax_val_eq σ pos
      have hle : (insMax σ pos j).1 < n + 1 := (insMax σ pos j).2
      rw [Fin.lt_def] at h2; omega
    by_cases hj : j.1 = pos.1
    · have hi : i.1 < pos.1 := by rw [Fin.lt_def] at hij; omega
      have hk : pos.1 < k.1 := by rw [Fin.lt_def] at hjk; omega
      rw [Fin.lt_def, insMax_val_lt σ pos i hi, insMax_val_gt σ pos k hk] at h1
      have hge1 := hcut.2 ⟨i.1, by omega⟩ hi
      have hlt2 := isCut_ge_lt hcut ⟨k.1 - 1, by omega⟩ (by dsimp; omega)
      omega
    · let g : ∀ x : Fin (n + 1), x.1 ≠ pos.1 → Fin n := fun x hx =>
        if h : x.1 < pos.1 then ⟨x.1, by omega⟩ else ⟨x.1 - 1, by omega⟩
      have hg_val : ∀ (x : Fin (n + 1)) (hx : x.1 ≠ pos.1), (insMax σ pos x).1 = (σ (g x hx)).1 := by
        intro x hx; dsimp only [g]; split_ifs with h
        · exact insMax_val_lt σ pos x h
        · exact insMax_val_gt σ pos x (by omega)
      have hg_lt : ∀ (x y : Fin (n + 1)) (hx : x.1 ≠ pos.1) (hy : y.1 ≠ pos.1),
          x < y → g x hx < g y hy := by
        intro x y hx hy hxy
        simp only [g, Fin.lt_def] at hxy ⊢; split_ifs <;> (dsimp; omega)
      exact hσ (g i hneq_i) (g j hj) (g k hneq_k)
        (hg_lt i j hneq_i hj hij) (hg_lt j k hj hneq_k hjk)
        ⟨by rw [Fin.lt_def, ← hg_val i hneq_i, ← hg_val k hneq_k]; exact h1,
         by rw [Fin.lt_def, ← hg_val k hneq_k, ← hg_val j hj]; exact h2⟩

private lemma card_avoids132 (n : ℕ) :
    Fintype.card {σ : Equiv.Perm (Fin n) // Avoids132 σ} = C_nat n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      rw [C_nat_zero]
      exact Fintype.card_eq_one_iff.mpr
        ⟨⟨1, fun i => Fin.elim0 i⟩, fun ⟨x, _⟩ => Subtype.ext (Subsingleton.elim x 1)⟩
    | succ n =>
      let S := Σ pos : Fin (n + 1),
        {α : Equiv.Perm (Fin pos.1) // Avoids132 α} ×
        {β : Equiv.Perm (Fin (n - pos.1)) // Avoids132 β}
      let f : S → {τ : Equiv.Perm (Fin (n + 1)) // Avoids132 τ} :=
        fun ⟨pos, ⟨α, hα⟩, ⟨β, hβ⟩⟩ =>
          ⟨insMax (skewSumCast (Nat.lt_succ_iff.mp pos.2) α β) pos,
           (avoids132_insMax_iff _ pos).mpr
             ⟨(avoids132_skewSumCast _ α β).mpr ⟨hα, hβ⟩, isCut_skewSumCast _ α β⟩⟩
      have hbij : Function.Bijective f := by
        constructor
        · rintro ⟨p1, ⟨α1, _⟩, ⟨β1, _⟩⟩ ⟨p2, ⟨α2, _⟩, ⟨β2, _⟩⟩ heq
          have heq' : insMax (skewSumCast (Nat.lt_succ_iff.mp p1.2) α1 β1) p1 =
              insMax (skewSumCast (Nat.lt_succ_iff.mp p2.2) α2 β2) p2 := congrArg Subtype.val heq
          have h1 := (insMax_bijective n).1
            (a₁ := (skewSumCast (Nat.lt_succ_iff.mp p1.2) α1 β1, p1))
            (a₂ := (skewSumCast (Nat.lt_succ_iff.mp p2.2) α2 β2, p2)) heq'
          rcases Prod.mk.inj h1 with ⟨hsk, rfl⟩
          have h2 := @skewSumCast_inj n p1.1 (Nat.lt_succ_iff.mp p1.2) (α1, β1) (α2, β2) hsk
          rcases Prod.mk.inj h2 with ⟨rfl, rfl⟩
          rfl
        · rintro ⟨τ, hτ⟩
          rcases (insMax_bijective n).2 τ with ⟨⟨σ, pos⟩, hτeq⟩
          dsimp only at hτeq
          rw [← hτeq] at hτ
          rcases (avoids132_insMax_iff σ pos).mp hτ with ⟨hσ, hcut⟩
          rcases exists_skewSumCast_of_isCut hcut with ⟨α, β, hσeq⟩
          rw [hσeq] at hσ
          rcases (avoids132_skewSumCast _ α β).mp hσ with ⟨hα, hβ⟩
          refine ⟨⟨pos, ⟨α, hα⟩, ⟨β, hβ⟩⟩, Subtype.ext ?_⟩
          dsimp only [f]
          rw [← hσeq, hτeq]
      rw [← Fintype.card_of_bijective hbij, C_nat_succ]
      simp only [S, Fintype.card_sigma, Fintype.card_prod]
      rw [Fin.sum_univ_eq_sum_range (fun i =>
        Fintype.card {α : Equiv.Perm (Fin i) // Avoids132 α} *
          Fintype.card {β : Equiv.Perm (Fin (n - i)) // Avoids132 β}) (n + 1)]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hin : i < n + 1 := Finset.mem_range.mp hi
      rw [ih i hin, ih (n - i) (by omega)]

private lemma card_avoids132_indec (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {σ : Equiv.Perm (Fin n) // Avoids132 σ ∧ IsSkewIndec σ} = C_nat (n - 1) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => omega
    | succ m =>
      have h1 := skewDecompFirst_card (fun {k} σ => Avoids132 σ) (fun hm α β => avoids132_skewSumCast hm α β) (m + 1) (by omega)
      rw [card_avoids132 (m + 1), C_nat_succ m] at h1
      have h2 : ∑ i ∈ Finset.range (m + 1),
          Fintype.card {α : Equiv.Perm (Fin (i + 1)) // Avoids132 α ∧ IsSkewIndec α} *
            Fintype.card {β : Equiv.Perm (Fin (m + 1 - (i + 1))) // Avoids132 β} =
          (∑ i ∈ Finset.range m, C_nat i * C_nat (m - i)) +
            Fintype.card {α : Equiv.Perm (Fin (m + 1)) // Avoids132 α ∧ IsSkewIndec α} := by
        rw [Finset.sum_range_succ]
        have hlast : Fintype.card {β : Equiv.Perm (Fin (m + 1 - (m + 1))) // Avoids132 β} = 1 := by
          rw [Nat.sub_self, card_avoids132 0, C_nat_zero]
        rw [hlast, mul_one]
        congr 1
        refine Finset.sum_congr rfl fun i hi => ?_
        have him : i < m := Finset.mem_range.mp hi
        rw [ih (i + 1) (by omega) (by omega), Nat.add_sub_cancel,
            show m + 1 - (i + 1) = m - i by omega, card_avoids132]
      rw [h2, Finset.sum_range_succ, Nat.sub_self, C_nat_zero, mul_one] at h1
      simp only [Nat.add_sub_cancel]
      omega

private def insMaxLift {n : ℕ} (pos : Fin (n + 1)) (u : Fin n) : Fin (n + 1) :=
  if u.1 < pos.1 then ⟨u.1, by omega⟩ else ⟨u.1 + 1, by omega⟩

private lemma insMaxLift_mono {n : ℕ} (pos : Fin (n + 1)) {u v : Fin n} (huv : u < v) :
    insMaxLift pos u < insMaxLift pos v := by
  simp only [insMaxLift, Fin.lt_def] at huv ⊢
  split_ifs <;> (dsimp; omega)

private lemma insMaxLift_val {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1)) (u : Fin n) :
    (insMax σ pos (insMaxLift pos u)).1 = (σ u).1 := by
  dsimp only [insMaxLift]
  split_ifs with hu
  · exact insMax_val_lt σ pos _ hu
  · rw [insMax_val_gt σ pos _ (by dsimp; omega)]
    have : (⟨u.1 + 1 - 1, by omega⟩ : Fin n) = u := by ext; simp
    rw [this]

private lemma insMaxLift_lt_pos {n : ℕ} (pos : Fin (n + 1)) {u : Fin n} (hu : u.1 < pos.1) :
    insMaxLift pos u < pos := by
  simp only [insMaxLift, hu, ↓reduceIte, Fin.lt_def]

private lemma insMaxLift_gt_pos {n : ℕ} (pos : Fin (n + 1)) {u : Fin n} (hu : pos.1 ≤ u.1) :
    pos < insMaxLift pos u := by
  have hnot : ¬ u.1 < pos.1 := by omega
  simp only [insMaxLift, hnot, ↓reduceIte, Fin.lt_def]; omega

private def insMaxUnlift {n : ℕ} (pos : Fin (n + 1)) (x : Fin (n + 1)) (hx : x.1 ≠ pos.1) : Fin n :=
  if h : x.1 < pos.1 then ⟨x.1, by omega⟩ else ⟨x.1 - 1, by omega⟩

private lemma insMaxUnlift_mono {n : ℕ} (pos : Fin (n + 1)) {x y : Fin (n + 1)}
    (hx : x.1 ≠ pos.1) (hy : y.1 ≠ pos.1) (hxy : x < y) :
    insMaxUnlift pos x hx < insMaxUnlift pos y hy := by
  simp only [insMaxUnlift, Fin.lt_def] at hxy ⊢
  split_ifs <;> (dsimp; omega)

private lemma insMaxUnlift_val {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1))
    (x : Fin (n + 1)) (hx : x.1 ≠ pos.1) :
    (insMax σ pos x).1 = (σ (insMaxUnlift pos x hx)).1 := by
  dsimp only [insMaxUnlift]
  split_ifs with h
  · exact insMax_val_lt σ pos x h
  · exact insMax_val_gt σ pos x (by omega)

private lemma insMaxUnlift_lt_of_lt {n : ℕ} (pos : Fin (n + 1)) (x : Fin (n + 1))
    (hx : x < pos) : (insMaxUnlift pos x (by rw [Fin.lt_def] at hx; omega)).1 < pos.1 := by
  rw [Fin.lt_def] at hx
  simp only [insMaxUnlift, hx, ↓reduceDIte]

private lemma insMaxUnlift_ge_of_gt {n : ℕ} (pos : Fin (n + 1)) (x : Fin (n + 1))
    (hx : pos < x) : pos.1 ≤ (insMaxUnlift pos x (by rw [Fin.lt_def] at hx; omega)).1 := by
  rw [Fin.lt_def] at hx
  have hnot : ¬ x.1 < pos.1 := by omega
  simp only [insMaxUnlift, hnot, ↓reduceDIte]
  omega

private lemma insMax_ne_pos_of_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos x y : Fin (n + 1))
    (h : insMax σ pos x < insMax σ pos y) : x.1 ≠ pos.1 := by
  intro heq
  have hx : x = pos := Fin.ext heq
  rw [hx, Fin.lt_def, insMax_val_eq] at h
  have := (insMax σ pos y).2
  omega

private lemma isCut_insMax_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1))
    {k : ℕ} (hk0 : 0 < k) (hkn : k < n + 1) :
    IsCut (insMax σ pos) k ↔ pos.1 < k ∧ IsCut σ (k - 1) := by
  constructor
  · intro hcut
    have hpk : pos.1 < k := by
      by_contra hge
      push Not at hge
      have hlt := isCut_ge_lt hcut pos hge
      rw [insMax_val_eq] at hlt
      omega
    refine ⟨hpk, by omega, fun i hi => ?_⟩
    have hxlt : (insMaxLift pos i).1 < k := by
      dsimp only [insMaxLift]; split_ifs <;> (dsimp; omega)
    have hge := hcut.2 (insMaxLift pos i) hxlt
    rw [insMaxLift_val] at hge
    omega
  · rintro ⟨hpk, hcut⟩
    refine ⟨by omega, fun x hx => ?_⟩
    by_cases h1 : x.1 < pos.1
    · rw [insMax_val_lt σ pos x h1]
      have hge := hcut.2 ⟨x.1, by omega⟩ (by dsimp; omega)
      omega
    · by_cases h2 : x.1 = pos.1
      · rw [Fin.ext h2, insMax_val_eq]; omega
      · rw [insMax_val_gt σ pos x (by omega)]
        have hge := hcut.2 ⟨x.1 - 1, by omega⟩ (by dsimp; omega)
        omega

private lemma isSkewIndec_insMax_skewSumCast {n m : ℕ} (hm : m < n)
    (β : Equiv.Perm (Fin m)) (α : Equiv.Perm (Fin (n - m))) (hα : IsSkewIndec α)
    (pos : Fin (n + 1)) :
    IsSkewIndec (insMax (skewSumCast (le_of_lt hm) β α) pos) ↔ m < pos.1 := by
  constructor
  · intro hind
    by_contra hle
    push Not at hle
    have hcut : IsCut (insMax (skewSumCast (le_of_lt hm) β α) pos) (m + 1) :=
      (isCut_insMax_iff _ pos (by omega) (by omega)).mpr
        ⟨by omega, by rw [Nat.add_sub_cancel]; exact isCut_skewSumCast (le_of_lt hm) β α⟩
    exact hind.2 (m + 1) (by omega) (by omega) hcut
  · intro hmp
    refine ⟨by omega, fun k hk0 hkn hcut => ?_⟩
    rcases (isCut_insMax_iff _ pos hk0 hkn).mp hcut with ⟨hpk, hcut'⟩
    have hcutα := (isCut_skewSumCast_gt (le_of_lt hm) (by omega : m < k - 1)
      (by omega : k - 1 < n) β α).mp hcut'
    exact hα.2 (k - 1 - m) (by omega) (by omega) hcutα

private lemma finset_downward_eq_filter_lt {N : ℕ} (S : Finset (Fin N))
    (hdown : ∀ x y : Fin N, y ∈ S → x ≤ y → x ∈ S) :
    ∀ x : Fin N, x ∈ S ↔ x.1 < S.card := by
  have hle : S.card ≤ N := by
    calc S.card ≤ (Finset.univ : Finset (Fin N)).card := Finset.card_le_univ S
      _ = N := by simp
  have hsub : S ⊆ Finset.univ.filter (fun y : Fin N => y.1 < S.card) := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hge
    push Not at hge
    have hsub' : Finset.univ.filter (fun z : Fin N => z.1 < y.1 + 1) ⊆ S := by
      intro z hz
      have hz' : z.1 < y.1 + 1 := (Finset.mem_filter.mp hz).2
      exact hdown z y hy (Fin.le_def.mpr (by omega))
    have hc := Finset.card_le_card hsub'
    rw [card_fin_filter_lt (by omega : y.1 + 1 ≤ N)] at hc
    omega
  have heq : S = Finset.univ.filter (fun y : Fin N => y.1 < S.card) :=
    Finset.eq_of_subset_of_card_le hsub (by rw [card_fin_filter_lt hle])
  intro x
  conv_lhs => rw [heq]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

private lemma one_sub_X_mul_sum_Ico (d : ℕ) (hd : 1 ≤ d) :
    (1 - Polynomial.X) * ∑ j ∈ Finset.Ico 1 d, (Polynomial.X : Polynomial ℚ) ^ j =
      Polynomial.X - Polynomial.X ^ d := by
  induction d with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero => simp
    | succ m =>
      rw [Finset.sum_Ico_succ_top (by omega : 1 ≤ m + 1), mul_add, ih (by omega)]
      ring

private lemma sum_subtype_fin_Ico {N : ℕ} (a b : ℕ) (hb : b ≤ N) (f : ℕ → Polynomial ℚ) :
    (∑ j : {j : Fin N // a ≤ j.1 ∧ j.1 < b}, f j.1.1) = ∑ j ∈ Finset.Ico a b, f j := by
  refine Finset.sum_bij (fun (j : {j : Fin N // a ≤ j.1 ∧ j.1 < b}) _ => j.1.1) ?_ ?_ ?_ ?_
  · intro j _; exact Finset.mem_Ico.mpr j.2
  · intro j1 _ j2 _ h; exact Subtype.ext (Fin.ext h)
  · intro k hk
    have hk' := Finset.mem_Ico.mp hk
    exact ⟨⟨⟨k, by omega⟩, hk'⟩, Finset.mem_univ _, rfl⟩
  · intro _ _; rfl

end PermPrimitives

section ClassA

private def InClassA {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  Avoids1324 σ ∧ Avoids24153 σ

private instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (InClassA σ) := by
  unfold InClassA; infer_instance

private lemma avoids132_imp_inClassA {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : Avoids132 σ) :
    InClassA σ := ⟨avoids132_imp_1324 h, avoids132_imp_24153 h⟩

private lemma inClassA_skewSumCast {n m : ℕ} (hm : m ≤ n)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))) :
    InClassA (skewSumCast hm α β) ↔ InClassA α ∧ InClassA β := by
  unfold InClassA
  rw [avoids1324_skewSumCast, avoids24153_skewSumCast]
  tauto

private def ForbA {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1)) : Prop :=
  (∃ i j k : Fin n, i < j ∧ j < k ∧ k.1 < pos.1 ∧ σ i < σ k ∧ σ k < σ j) ∨
  (∃ a b c d : Fin n, a < b ∧ b < c ∧ c.1 < pos.1 ∧ pos.1 ≤ d.1 ∧
    σ c < σ a ∧ σ a < σ d ∧ σ d < σ b)

private instance {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1)) :
    Decidable (ForbA σ pos) := by
  unfold ForbA; infer_instance

private lemma insMax_inClassA_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1)) :
    InClassA (insMax σ pos) ↔ InClassA σ ∧ ¬ ForbA σ pos := by
  constructor
  · rintro ⟨h1324, h24153⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i j k l hij hjk hkl ⟨h1, h2, h3⟩
      exact h1324 (insMaxLift pos i) (insMaxLift pos j) (insMaxLift pos k) (insMaxLift pos l)
        (insMaxLift_mono pos hij) (insMaxLift_mono pos hjk) (insMaxLift_mono pos hkl)
        ⟨by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h1,
         by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h2,
         by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h3⟩
    · intro a b c d e hab hbc hcd hde ⟨h1, h2, h3, h4⟩
      exact h24153 (insMaxLift pos a) (insMaxLift pos b) (insMaxLift pos c)
        (insMaxLift pos d) (insMaxLift pos e)
        (insMaxLift_mono pos hab) (insMaxLift_mono pos hbc)
        (insMaxLift_mono pos hcd) (insMaxLift_mono pos hde)
        ⟨by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h1,
         by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h2,
         by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h3,
         by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h4⟩
    · rintro (⟨i, j, k, hij, hjk, hk, h1, h2⟩ | ⟨a, b, c, d, hab, hbc, hc, hd, h1, h2, h3⟩)
      · exact h1324 (insMaxLift pos i) (insMaxLift pos j) (insMaxLift pos k) pos
          (insMaxLift_mono pos hij) (insMaxLift_mono pos hjk) (insMaxLift_lt_pos pos hk)
          ⟨by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h1,
           by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h2,
           by rw [Fin.lt_def, insMaxLift_val, insMax_val_eq]; exact (σ j).2⟩
      · exact h24153 (insMaxLift pos a) (insMaxLift pos b) (insMaxLift pos c) pos (insMaxLift pos d)
          (insMaxLift_mono pos hab) (insMaxLift_mono pos hbc)
          (insMaxLift_lt_pos pos hc) (insMaxLift_gt_pos pos hd)
          ⟨by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h1,
           by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h2,
           by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h3,
           by rw [Fin.lt_def, insMaxLift_val, insMax_val_eq]; exact (σ b).2⟩
  · rintro ⟨⟨h1324, h24153⟩, hnf⟩
    constructor
    · intro i j k l hij hjk hkl ⟨h1, h2, h3⟩
      have hi := insMax_ne_pos_of_lt σ pos i k h1
      have hk := insMax_ne_pos_of_lt σ pos k j h2
      have hj := insMax_ne_pos_of_lt σ pos j l h3
      by_cases hl : l.1 = pos.1
      · have hle : l = pos := Fin.ext hl
        rw [hle] at hkl
        exact hnf (Or.inl ⟨insMaxUnlift pos i hi, insMaxUnlift pos j hj, insMaxUnlift pos k hk,
          insMaxUnlift_mono pos hi hj hij, insMaxUnlift_mono pos hj hk hjk,
          insMaxUnlift_lt_of_lt pos k hkl,
          by rw [Fin.lt_def, ← insMaxUnlift_val σ pos i hi, ← insMaxUnlift_val σ pos k hk]; exact h1,
          by rw [Fin.lt_def, ← insMaxUnlift_val σ pos k hk, ← insMaxUnlift_val σ pos j hj]; exact h2⟩)
      · exact h1324 (insMaxUnlift pos i hi) (insMaxUnlift pos j hj)
          (insMaxUnlift pos k hk) (insMaxUnlift pos l hl)
          (insMaxUnlift_mono pos hi hj hij) (insMaxUnlift_mono pos hj hk hjk)
          (insMaxUnlift_mono pos hk hl hkl)
          ⟨by rw [Fin.lt_def, ← insMaxUnlift_val σ pos i hi, ← insMaxUnlift_val σ pos k hk]; exact h1,
           by rw [Fin.lt_def, ← insMaxUnlift_val σ pos k hk, ← insMaxUnlift_val σ pos j hj]; exact h2,
           by rw [Fin.lt_def, ← insMaxUnlift_val σ pos j hj, ← insMaxUnlift_val σ pos l hl]; exact h3⟩
    · intro a b c d e hab hbc hcd hde ⟨h1, h2, h3, h4⟩
      have hc := insMax_ne_pos_of_lt σ pos c a h1
      have ha := insMax_ne_pos_of_lt σ pos a e h2
      have he := insMax_ne_pos_of_lt σ pos e b h3
      have hb := insMax_ne_pos_of_lt σ pos b d h4
      by_cases hd : d.1 = pos.1
      · have hdeq : d = pos := Fin.ext hd
        rw [hdeq] at hcd hde
        exact hnf (Or.inr ⟨insMaxUnlift pos a ha, insMaxUnlift pos b hb,
          insMaxUnlift pos c hc, insMaxUnlift pos e he,
          insMaxUnlift_mono pos ha hb hab, insMaxUnlift_mono pos hb hc hbc,
          insMaxUnlift_lt_of_lt pos c hcd, insMaxUnlift_ge_of_gt pos e hde,
          by rw [Fin.lt_def, ← insMaxUnlift_val σ pos c hc, ← insMaxUnlift_val σ pos a ha]; exact h1,
          by rw [Fin.lt_def, ← insMaxUnlift_val σ pos a ha, ← insMaxUnlift_val σ pos e he]; exact h2,
          by rw [Fin.lt_def, ← insMaxUnlift_val σ pos e he, ← insMaxUnlift_val σ pos b hb]; exact h3⟩)
      · exact h24153 (insMaxUnlift pos a ha) (insMaxUnlift pos b hb)
          (insMaxUnlift pos c hc) (insMaxUnlift pos d hd) (insMaxUnlift pos e he)
          (insMaxUnlift_mono pos ha hb hab) (insMaxUnlift_mono pos hb hc hbc)
          (insMaxUnlift_mono pos hc hd hcd) (insMaxUnlift_mono pos hd he hde)
          ⟨by rw [Fin.lt_def, ← insMaxUnlift_val σ pos c hc, ← insMaxUnlift_val σ pos a ha]; exact h1,
           by rw [Fin.lt_def, ← insMaxUnlift_val σ pos a ha, ← insMaxUnlift_val σ pos e he]; exact h2,
           by rw [Fin.lt_def, ← insMaxUnlift_val σ pos e he, ← insMaxUnlift_val σ pos b hb]; exact h3,
           by rw [Fin.lt_def, ← insMaxUnlift_val σ pos b hb, ← insMaxUnlift_val σ pos d hd]; exact h4⟩

private lemma forbA_mono {n : ℕ} (σ : Equiv.Perm (Fin n)) {p q : Fin (n + 1)}
    (hpq : p ≤ q) (h : ForbA σ p) : ForbA σ q := by
  have hpq' : p.1 ≤ q.1 := hpq
  rcases h with ⟨i, j, k, hij, hjk, hk, h1, h2⟩ | ⟨a, b, c, d, hab, hbc, hc, hd, h1, h2, h3⟩
  · exact Or.inl ⟨i, j, k, hij, hjk, by omega, h1, h2⟩
  · by_cases hqd : q.1 ≤ d.1
    · exact Or.inr ⟨a, b, c, d, hab, hbc, by omega, hqd, h1, h2, h3⟩
    · exact Or.inl ⟨a, b, d, hab, hbc.trans (Fin.lt_def.mpr (by omega)), by omega, h2, h3⟩

private def activeA {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun pos : Fin (n + 1) => InClassA (insMax σ pos))

private def dA {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := (activeA σ).card

private lemma mem_activeA_iff {n : ℕ} {σ : Equiv.Perm (Fin n)} (hσ : InClassA σ) (pos : Fin (n + 1)) :
    pos ∈ activeA σ ↔ pos.1 < dA σ := by
  refine finset_downward_eq_filter_lt (activeA σ) ?_ pos
  intro x y hy hxy
  simp only [activeA, Finset.mem_filter, Finset.mem_univ, true_and, insMax_inClassA_iff] at hy ⊢
  exact ⟨hy.1, fun hx => hy.2 (forbA_mono σ hxy hx)⟩

private lemma not_forbA_of_lt_three {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1))
    (hpos : pos.1 < 3) : ¬ ForbA σ pos := by
  rintro (⟨i, j, k, hij, hjk, hk, _, _⟩ | ⟨a, b, c, _, hab, hbc, hc, _, _, _, _⟩)
  · simp only [Fin.lt_def] at hij hjk; omega
  · simp only [Fin.lt_def] at hab hbc; omega

private lemma dA_ge_two {n : ℕ} (hn : 1 ≤ n) {σ : Equiv.Perm (Fin n)} (hσ : InClassA σ) :
    2 ≤ dA σ := by
  have hmem : (⟨1, by omega⟩ : Fin (n + 1)) ∈ activeA σ := by
    simp only [activeA, Finset.mem_filter, Finset.mem_univ, true_and, insMax_inClassA_iff]
    exact ⟨hσ, not_forbA_of_lt_three σ ⟨1, by omega⟩ (by dsimp; omega)⟩
  have hlt := (mem_activeA_iff hσ ⟨1, by omega⟩).mp hmem
  dsimp at hlt; omega

private lemma dA_le {n : ℕ} (σ : Equiv.Perm (Fin n)) : dA σ ≤ n + 1 := by
  calc dA σ = (activeA σ).card := rfl
    _ ≤ (Finset.univ : Finset (Fin (n + 1))).card := Finset.card_le_univ _
    _ = n + 1 := by simp

private lemma forbA_skewSumCast_avoids132 {n m : ℕ} (hm : m ≤ n)
    {β : Equiv.Perm (Fin m)} (hβ : Avoids132 β)
    (α : Equiv.Perm (Fin (n - m))) (pos : Fin (n + 1)) :
    ForbA (skewSumCast hm β α) pos ↔
      ∃ hmp : m ≤ pos.1, ForbA α ⟨pos.1 - m, by omega⟩ := by
  let σ := skewSumCast hm β α
  constructor
  · rintro (⟨i, j, k, hij, hjk, hk, h1, h2⟩ | ⟨a, b, c, d, hab, hbc, hc, hd, h1, h2, h3⟩)
    · by_cases hi : i.1 < m
      · by_cases hk' : k.1 < m
        · exfalso
          have hj' : j.1 < m := by simp only [Fin.lt_def] at hij hjk; omega
          rw [Fin.lt_def, skewSumCast_val_lt hm β α i hi, skewSumCast_val_lt hm β α k hk'] at h1
          rw [Fin.lt_def, skewSumCast_val_lt hm β α k hk', skewSumCast_val_lt hm β α j hj'] at h2
          exact hβ ⟨i.1, hi⟩ ⟨j.1, hj'⟩ ⟨k.1, hk'⟩
            (by rw [Fin.lt_def]; exact hij) (by rw [Fin.lt_def]; exact hjk)
            ⟨by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega⟩
        · exfalso
          have hlt := skewSumCast_lt_ge hm β α i k hi (by omega)
          exact absurd (lt_trans h1 hlt) (lt_irrefl _)
      · have hmp : m ≤ pos.1 := by simp only [Fin.lt_def] at hij hjk; omega
        refine ⟨hmp, Or.inl ⟨⟨i.1 - m, by omega⟩, ⟨j.1 - m, by omega⟩, ⟨k.1 - m, by omega⟩,
          by simp only [Fin.lt_def] at hij ⊢; omega,
          by simp only [Fin.lt_def] at hjk ⊢; omega,
          by dsimp; omega, ?_, ?_⟩⟩
        · rw [Fin.lt_def, skewSumCast_val_ge hm β α i (by omega),
              skewSumCast_val_ge hm β α k (by simp only [Fin.lt_def] at hij hjk; omega)] at h1
          exact Fin.lt_def.mpr h1
        · rw [Fin.lt_def, skewSumCast_val_ge hm β α k (by simp only [Fin.lt_def] at hij hjk; omega),
              skewSumCast_val_ge hm β α j (by simp only [Fin.lt_def] at hij; omega)] at h2
          exact Fin.lt_def.mpr h2
    · by_cases ha : a.1 < m
      · by_cases hd' : d.1 < m
        · exfalso
          have hb' : b.1 < m := by simp only [Fin.lt_def] at hab hbc; omega
          rw [Fin.lt_def, skewSumCast_val_lt hm β α a ha, skewSumCast_val_lt hm β α d hd'] at h2
          rw [Fin.lt_def, skewSumCast_val_lt hm β α d hd', skewSumCast_val_lt hm β α b hb'] at h3
          exact hβ ⟨a.1, ha⟩ ⟨b.1, hb'⟩ ⟨d.1, hd'⟩
            (by rw [Fin.lt_def]; exact hab)
            (by rw [Fin.lt_def]; dsimp; simp only [Fin.lt_def] at hbc; omega)
            ⟨by rw [Fin.lt_def]; omega, by rw [Fin.lt_def]; omega⟩
        · exfalso
          have hlt := skewSumCast_lt_ge hm β α a d ha (by omega)
          exact absurd (lt_trans h2 hlt) (lt_irrefl _)
      · have hmp : m ≤ pos.1 := by simp only [Fin.lt_def] at hab hbc; omega
        refine ⟨hmp, Or.inr ⟨⟨a.1 - m, by omega⟩, ⟨b.1 - m, by omega⟩,
          ⟨c.1 - m, by omega⟩, ⟨d.1 - m, by omega⟩,
          by simp only [Fin.lt_def] at hab ⊢; omega,
          by simp only [Fin.lt_def] at hbc ⊢; omega,
          by dsimp; omega, by dsimp; omega, ?_, ?_, ?_⟩⟩
        · rw [Fin.lt_def, skewSumCast_val_ge hm β α c (by simp only [Fin.lt_def] at hab hbc; omega),
              skewSumCast_val_ge hm β α a (by omega)] at h1
          exact Fin.lt_def.mpr h1
        · rw [Fin.lt_def, skewSumCast_val_ge hm β α a (by omega),
              skewSumCast_val_ge hm β α d (by simp only [Fin.lt_def] at hab hbc; omega)] at h2
          exact Fin.lt_def.mpr h2
        · rw [Fin.lt_def, skewSumCast_val_ge hm β α d (by simp only [Fin.lt_def] at hab hbc; omega),
              skewSumCast_val_ge hm β α b (by simp only [Fin.lt_def] at hab; omega)] at h3
          exact Fin.lt_def.mpr h3
  · rintro ⟨hmp, (⟨i, j, k, hij, hjk, hk, h1, h2⟩ | ⟨a, b, c, d, hab, hbc, hc, hd, h1, h2, h3⟩)⟩
    · refine Or.inl ⟨⟨i.1 + m, by omega⟩, ⟨j.1 + m, by omega⟩, ⟨k.1 + m, by omega⟩,
        by simp only [Fin.lt_def] at hij ⊢; omega,
        by simp only [Fin.lt_def] at hjk ⊢; omega,
        by dsimp at hk ⊢; omega, ?_, ?_⟩
      · rw [Fin.lt_def, skewSumCast_val_ge hm β α _ (by dsimp; omega),
            skewSumCast_val_ge hm β α _ (by dsimp; omega)]
        rw [Fin.lt_def] at h1; simpa using h1
      · rw [Fin.lt_def, skewSumCast_val_ge hm β α _ (by dsimp; omega),
            skewSumCast_val_ge hm β α _ (by dsimp; omega)]
        rw [Fin.lt_def] at h2; simpa using h2
    · refine Or.inr ⟨⟨a.1 + m, by omega⟩, ⟨b.1 + m, by omega⟩,
        ⟨c.1 + m, by omega⟩, ⟨d.1 + m, by omega⟩,
        by simp only [Fin.lt_def] at hab ⊢; omega,
        by simp only [Fin.lt_def] at hbc ⊢; omega,
        by dsimp at hc ⊢; omega, by dsimp at hd ⊢; omega, ?_, ?_, ?_⟩
      · rw [Fin.lt_def, skewSumCast_val_ge hm β α _ (by dsimp; omega),
            skewSumCast_val_ge hm β α _ (by dsimp; omega)]
        rw [Fin.lt_def] at h1; simpa using h1
      · rw [Fin.lt_def, skewSumCast_val_ge hm β α _ (by dsimp; omega),
            skewSumCast_val_ge hm β α _ (by dsimp; omega)]
        rw [Fin.lt_def] at h2; simpa using h2
      · rw [Fin.lt_def, skewSumCast_val_ge hm β α _ (by dsimp; omega),
            skewSumCast_val_ge hm β α _ (by dsimp; omega)]
        rw [Fin.lt_def] at h3; simpa using h3

private lemma dA_skewSumCast_avoids132 {n m : ℕ} (hm : m ≤ n)
    {β : Equiv.Perm (Fin m)} (hβ : Avoids132 β)
    {α : Equiv.Perm (Fin (n - m))} (hα : InClassA α) :
    dA (skewSumCast hm β α) = m + dA α := by
  have hσ : InClassA (skewSumCast hm β α) :=
    (inClassA_skewSumCast hm β α).mpr ⟨avoids132_imp_inClassA hβ, hα⟩
  have heq : activeA (skewSumCast hm β α) =
      Finset.univ.filter (fun pos : Fin (n + 1) => pos.1 < m + dA α) := by
    ext pos
    simp only [activeA, Finset.mem_filter, Finset.mem_univ, true_and, insMax_inClassA_iff,
      hσ, true_and, forbA_skewSumCast_avoids132 hm hβ α pos]
    by_cases hmp : m ≤ pos.1
    · constructor
      · intro hnf
        have hnfα : ¬ ForbA α ⟨pos.1 - m, by omega⟩ := fun hf => hnf ⟨hmp, hf⟩
        have hmem : (⟨pos.1 - m, by omega⟩ : Fin (n - m + 1)) ∈ activeA α := by
          simp only [activeA, Finset.mem_filter, Finset.mem_univ, true_and, insMax_inClassA_iff]
          exact ⟨hα, hnfα⟩
        have hlt := (mem_activeA_iff hα ⟨pos.1 - m, by omega⟩).mp hmem
        dsimp at hlt; omega
      · rintro hlt ⟨_, hf⟩
        have hmem : (⟨pos.1 - m, by omega⟩ : Fin (n - m + 1)) ∈ activeA α :=
          (mem_activeA_iff hα ⟨pos.1 - m, by omega⟩).mpr (by dsimp; omega)
        simp only [activeA, Finset.mem_filter, Finset.mem_univ, true_and, insMax_inClassA_iff] at hmem
        exact hmem.2 hf
    · constructor
      · intro _; omega
      · rintro _ ⟨hmp', _⟩; omega
  have hbound : m + dA α ≤ n + 1 := by have := dA_le α; omega
  change (activeA (skewSumCast hm β α)).card = m + dA α
  rw [heq, card_fin_filter_lt hbound]

private lemma not_forbA_insMax_succ {n : ℕ} {σ : Equiv.Perm (Fin n)} {pos : Fin (n + 1)}
    (hnf : ¬ ForbA σ pos) :
    ¬ ForbA (insMax σ pos) ⟨pos.1 + 1, by omega⟩ := by
  rintro (⟨i, j, k, hij, hjk, hk, h1, h2⟩ | ⟨a, b, c, d, hab, hbc, hc, hd, h1, h2, h3⟩)
  · dsimp at hk
    have hk_ne : k.1 ≠ pos.1 := insMax_ne_pos_of_lt σ pos k j h2
    have hk_lt : k < pos := Fin.lt_def.mpr (by omega)
    have hj_lt : j < pos := lt_trans hjk hk_lt
    have hi_lt : i < pos := lt_trans hij hj_lt
    have hi_ne : i.1 ≠ pos.1 := by rw [Fin.lt_def] at hi_lt; omega
    have hj_ne : j.1 ≠ pos.1 := by rw [Fin.lt_def] at hj_lt; omega
    exact hnf (Or.inl ⟨insMaxUnlift pos i hi_ne, insMaxUnlift pos j hj_ne, insMaxUnlift pos k hk_ne,
      insMaxUnlift_mono pos hi_ne hj_ne hij, insMaxUnlift_mono pos hj_ne hk_ne hjk,
      insMaxUnlift_lt_of_lt pos k hk_lt,
      by rw [Fin.lt_def, ← insMaxUnlift_val σ pos i hi_ne, ← insMaxUnlift_val σ pos k hk_ne]; exact h1,
      by rw [Fin.lt_def, ← insMaxUnlift_val σ pos k hk_ne, ← insMaxUnlift_val σ pos j hj_ne]; exact h2⟩)
  · dsimp at hc hd
    have hc_ne : c.1 ≠ pos.1 := insMax_ne_pos_of_lt σ pos c a h1
    have hc_lt : c < pos := Fin.lt_def.mpr (by omega)
    have hb_lt : b < pos := lt_trans hbc hc_lt
    have ha_lt : a < pos := lt_trans hab hb_lt
    have hd_gt : pos < d := Fin.lt_def.mpr (by omega)
    have ha_ne : a.1 ≠ pos.1 := by rw [Fin.lt_def] at ha_lt; omega
    have hb_ne : b.1 ≠ pos.1 := by rw [Fin.lt_def] at hb_lt; omega
    have hd_ne : d.1 ≠ pos.1 := by rw [Fin.lt_def] at hd_gt; omega
    exact hnf (Or.inr ⟨insMaxUnlift pos a ha_ne, insMaxUnlift pos b hb_ne,
      insMaxUnlift pos c hc_ne, insMaxUnlift pos d hd_ne,
      insMaxUnlift_mono pos ha_ne hb_ne hab, insMaxUnlift_mono pos hb_ne hc_ne hbc,
      insMaxUnlift_lt_of_lt pos c hc_lt, insMaxUnlift_ge_of_gt pos d hd_gt,
      by rw [Fin.lt_def, ← insMaxUnlift_val σ pos c hc_ne, ← insMaxUnlift_val σ pos a ha_ne]; exact h1,
      by rw [Fin.lt_def, ← insMaxUnlift_val σ pos a ha_ne, ← insMaxUnlift_val σ pos d hd_ne]; exact h2,
      by rw [Fin.lt_def, ← insMaxUnlift_val σ pos d hd_ne, ← insMaxUnlift_val σ pos b hb_ne]; exact h3⟩)

private lemma dA_insMax_indec {n m : ℕ} (hm : m < n)
    (β : Equiv.Perm (Fin m)) {α : Equiv.Perm (Fin (n - m))} (hαI : IsSkewIndec α)
    {pos : Fin (n + 1)} (hmp : m < pos.1)
    (hτ : InClassA (insMax (skewSumCast (le_of_lt hm) β α) pos)) :
    dA (insMax (skewSumCast (le_of_lt hm) β α) pos) = pos.1 + 2 := by
  let σ := skewSumCast (le_of_lt hm) β α
  let τ := insMax σ pos
  have hnf : ¬ ForbA σ pos := ((insMax_inClassA_iff σ pos).mp hτ).2
  have hge : pos.1 + 2 ≤ dA τ := by
    have hmem : (⟨pos.1 + 1, by omega⟩ : Fin (n + 2)) ∈ activeA τ := by
      simp only [activeA, Finset.mem_filter, Finset.mem_univ, true_and, insMax_inClassA_iff]
      exact ⟨hτ, not_forbA_insMax_succ hnf⟩
    have hlt := (mem_activeA_iff hτ ⟨pos.1 + 1, by omega⟩).mp hmem
    change pos.1 + 1 < dA τ at hlt; omega
  have hle : dA τ ≤ pos.1 + 2 := by
    by_cases hpn : pos.1 = n
    · have := dA_le τ; omega
    · have hlt_n : pos.1 < n := by omega
      have hforb : ForbA τ ⟨pos.1 + 2, by omega⟩ := by
        have hnc : ¬ IsCut α (pos.1 - m) := hαI.2 (pos.1 - m) (by omega) (by omega)
        rcases exists_lt_of_not_isCut (by omega) (by omega) hnc with ⟨u, v, hu, hv, huv⟩
        let k0 : Fin (n - m) := ⟨pos.1 - m, by omega⟩
        have hne_uk : u ≠ k0 := fun h => by have := congrArg Fin.val h; dsimp [k0] at this; omega
        rcases lt_or_gt_of_ne (α.injective.ne hne_uk) with huk | hku
        · refine Or.inl ⟨⟨m + u.1, by omega⟩, pos, ⟨pos.1 + 1, by omega⟩,
            by rw [Fin.lt_def]; dsimp; omega,
            by rw [Fin.lt_def]; dsimp; omega,
            by dsimp; omega, ?_, ?_⟩
          · rw [Fin.lt_def, insMax_val_lt σ pos _ (by dsimp; omega),
                insMax_val_gt σ pos _ (by dsimp; omega),
                skewSumCast_val_ge (le_of_lt hm) β α _ (by dsimp; omega),
                skewSumCast_val_ge (le_of_lt hm) β α _ (by dsimp; omega)]
            have hu' : (⟨m + u.1 - m, by omega⟩ : Fin (n - m)) = u := by ext; simp
            have hk' : (⟨pos.1 + 1 - 1 - m, by omega⟩ : Fin (n - m)) = k0 := by ext; simp [k0]
            rw [hu', hk']; exact huk
          · rw [Fin.lt_def, insMax_val_gt σ pos _ (by dsimp; omega), insMax_val_eq]
            exact (σ ⟨pos.1 + 1 - 1, by omega⟩).2
        · have hv_gt : pos.1 - m < v.1 := by
            by_contra hle'
            have hveq : v = k0 := Fin.ext (by dsimp [k0]; omega)
            rw [hveq] at huv
            exact absurd (lt_trans huv hku) (lt_irrefl _)
          refine Or.inr ⟨⟨m + u.1, by omega⟩, pos, ⟨pos.1 + 1, by omega⟩, ⟨m + v.1 + 1, by omega⟩,
            by rw [Fin.lt_def]; dsimp; omega,
            by rw [Fin.lt_def]; dsimp; omega,
            by dsimp; omega, by dsimp; omega, ?_, ?_, ?_⟩
          · rw [Fin.lt_def, insMax_val_gt σ pos _ (by dsimp; omega),
                insMax_val_lt σ pos _ (by dsimp; omega),
                skewSumCast_val_ge (le_of_lt hm) β α _ (by dsimp; omega),
                skewSumCast_val_ge (le_of_lt hm) β α _ (by dsimp; omega)]
            have hu' : (⟨m + u.1 - m, by omega⟩ : Fin (n - m)) = u := by ext; simp
            have hk' : (⟨pos.1 + 1 - 1 - m, by omega⟩ : Fin (n - m)) = k0 := by ext; simp [k0]
            rw [hu', hk']; exact hku
          · rw [Fin.lt_def, insMax_val_lt σ pos _ (by dsimp; omega),
                insMax_val_gt σ pos _ (by dsimp; omega),
                skewSumCast_val_ge (le_of_lt hm) β α _ (by dsimp; omega),
                skewSumCast_val_ge (le_of_lt hm) β α _ (by dsimp; omega)]
            have hu' : (⟨m + u.1 - m, by omega⟩ : Fin (n - m)) = u := by ext; simp
            have hv' : (⟨m + v.1 + 1 - 1 - m, by omega⟩ : Fin (n - m)) = v := by ext; simp
            rw [hu', hv']; exact huv
          · rw [Fin.lt_def, insMax_val_gt σ pos _ (by dsimp; omega), insMax_val_eq]
            exact (σ ⟨m + v.1 + 1 - 1, by omega⟩).2
      by_contra hgt
      push Not at hgt
      have hmem : (⟨pos.1 + 2, by omega⟩ : Fin (n + 2)) ∈ activeA τ :=
        (mem_activeA_iff hτ ⟨pos.1 + 2, by omega⟩).mpr (by dsimp; omega)
      simp only [activeA, Finset.mem_filter, Finset.mem_univ, true_and, insMax_inClassA_iff] at hmem
      exact hmem.2 hforb
  change dA τ = pos.1 + 2
  omega

private noncomputable def F_poly (n : ℕ) : Polynomial ℚ :=
  ∑ α : {α : Equiv.Perm (Fin n) // InClassA α ∧ IsSkewIndec α},
    (Polynomial.X : Polynomial ℚ) ^ (dA α.1 - 2)

private lemma F_poly_eval_one (n : ℕ) :
    (F_poly n).eval 1 = (Fintype.card {α : Equiv.Perm (Fin n) // InClassA α ∧ IsSkewIndec α} : ℚ) := by
  unfold F_poly
  rw [Polynomial.eval_finset_sum]
  simp

private lemma F_poly_zero : F_poly 0 = 0 := by
  unfold F_poly
  have hempty : IsEmpty {α : Equiv.Perm (Fin 0) // InClassA α ∧ IsSkewIndec α} :=
    ⟨fun ⟨_, _, h⟩ => by have := h.1; omega⟩
  simp

private lemma F_poly_one : F_poly 1 = 1 := by
  unfold F_poly
  have h1A : InClassA (1 : Equiv.Perm (Fin 1)) :=
    avoids132_imp_inClassA (fun i j k hij hjk => by simp only [Fin.lt_def] at hij hjk; omega)
  have h1I : IsSkewIndec (1 : Equiv.Perm (Fin 1)) := ⟨by omega, fun m hm0 hm1 => by omega⟩
  have huniq : ∀ x : {α : Equiv.Perm (Fin 1) // InClassA α ∧ IsSkewIndec α},
      x = ⟨1, h1A, h1I⟩ := fun ⟨α, _, _⟩ => Subtype.ext (Subsingleton.elim α 1)
  have hd : dA (1 : Equiv.Perm (Fin 1)) = 2 := by
    have h1 := dA_ge_two (by omega) h1A
    have h2 := dA_le (1 : Equiv.Perm (Fin 1))
    omega
  rw [Finset.sum_eq_single ⟨1, h1A, h1I⟩]
  · simp [hd]
  · intro b _ hb; exact absurd (huniq b) hb
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma skewDecompLastEquiv_symm_apply (n : ℕ) (hn : 1 ≤ n)
    (p : Σ m : Fin n, Equiv.Perm (Fin m.1) × {α : Equiv.Perm (Fin (n - m.1)) // IsSkewIndec α}) :
    (skewDecompLastEquiv n hn).symm p = skewSumCast (le_of_lt p.1.2) p.2.1 p.2.2.1 :=
  rfl

private lemma F_poly_rec (n : ℕ) (hn : 2 ≤ n) :
    (1 - Polynomial.X) * F_poly n =
      ∑ m ∈ Finset.range (n - 1),
        C_seq m * (Polynomial.X * Polynomial.C ((F_poly (n - 1 - m)).eval 1) -
          Polynomial.X ^ 2 * F_poly (n - 1 - m)) := by
  cases n with
  | zero => omega
  | succ k =>
    have hk : 1 ≤ k := by omega
    simp only [Nat.add_sub_cancel]
    let S := Σ m : Fin k,
      {β : Equiv.Perm (Fin m.1) // Avoids132 β} ×
      Σ α : {α : Equiv.Perm (Fin (k - m.1)) // InClassA α ∧ IsSkewIndec α},
        {j : Fin (k + 1 - m.1) // 1 ≤ j.1 ∧ j.1 < dA α.1}
    let toPerm : S → {π : Equiv.Perm (Fin (k + 1)) // InClassA π ∧ IsSkewIndec π} :=
      fun ⟨m, ⟨β, hβ⟩, ⟨α, hαA, hαI⟩, ⟨j, hj1, hjd⟩⟩ =>
        let σ : Equiv.Perm (Fin k) := skewSumCast (le_of_lt m.2) β α
        let pos : Fin (k + 1) := ⟨m.1 + j.1, by omega⟩
        have hσA : InClassA σ :=
          (inClassA_skewSumCast (le_of_lt m.2) β α).mpr ⟨avoids132_imp_inClassA hβ, hαA⟩
        have hmem : pos ∈ activeA σ := by
          rw [mem_activeA_iff hσA, dA_skewSumCast_avoids132 (le_of_lt m.2) hβ hαA]
          dsimp only [pos] at *; omega
        have hτA : InClassA (insMax σ pos) := (Finset.mem_filter.mp hmem).2
        have hτI : IsSkewIndec (insMax σ pos) :=
          (isSkewIndec_insMax_skewSumCast m.2 β α hαI pos).mpr (by dsimp [pos]; omega)
        ⟨insMax σ pos, hτA, hτI⟩
    have hbij : Function.Bijective toPerm := by
      constructor
      · rintro ⟨m1, ⟨β1, hβ1⟩, ⟨α1, hα1A, hα1I⟩, ⟨j1, hj11, hj1d⟩⟩
               ⟨m2, ⟨β2, hβ2⟩, ⟨α2, hα2A, hα2I⟩, ⟨j2, hj21, hj2d⟩⟩ heq
        have hpeq : insMax (skewSumCast (le_of_lt m1.2) β1 α1) ⟨m1.1 + j1.1, by omega⟩ =
            insMax (skewSumCast (le_of_lt m2.2) β2 α2) ⟨m2.1 + j2.1, by omega⟩ :=
          congrArg Subtype.val heq
        have h1 := (insMax_bijective k).1
          (a₁ := (skewSumCast (le_of_lt m1.2) β1 α1, ⟨m1.1 + j1.1, by omega⟩))
          (a₂ := (skewSumCast (le_of_lt m2.2) β2 α2, ⟨m2.1 + j2.1, by omega⟩)) hpeq
        rcases Prod.mk.inj h1 with ⟨hsk, hpos⟩
        have hdec : (⟨m1, β1, ⟨α1, hα1I⟩⟩ :
            Σ m : Fin k, Equiv.Perm (Fin m.1) × {α : Equiv.Perm (Fin (k - m.1)) // IsSkewIndec α}) =
            ⟨m2, β2, ⟨α2, hα2I⟩⟩ :=
          (skewDecompLastEquiv k hk).symm.injective (by
            rw [skewDecompLastEquiv_symm_apply, skewDecompLastEquiv_symm_apply]; exact hsk)
        cases hdec
        have hj : j1 = j2 := by
          ext; have := congrArg Fin.val hpos; dsimp at this; omega
        subst hj
        rfl
      · rintro ⟨π, hπA, hπI⟩
        rcases (insMax_bijective k).2 π with ⟨⟨σ, pos⟩, hπeq⟩
        dsimp only at hπeq
        let d := skewDecompLastEquiv k hk σ
        have hσeq : skewSumCast (le_of_lt d.1.2) d.2.1 d.2.2.1 = σ := by
          rw [← skewDecompLastEquiv_symm_apply k hk d]
          exact (skewDecompLastEquiv k hk).symm_apply_apply σ
        rw [← hπeq, ← hσeq] at hπA hπI
        have hmp : d.1.1 < pos.1 :=
          (isSkewIndec_insMax_skewSumCast d.1.2 d.2.1 d.2.2.1 d.2.2.2 pos).mp hπI
        rcases (insMax_inClassA_iff _ pos).mp hπA with ⟨hσA, hnf⟩
        rcases (inClassA_skewSumCast (le_of_lt d.1.2) d.2.1 d.2.2.1).mp hσA with ⟨_, hαA⟩
        have hβ132 : Avoids132 d.2.1 := by
          intro i j r hij hjr ⟨h1, h2⟩
          apply hnf
          refine Or.inl ⟨⟨i.1, by omega⟩, ⟨j.1, by omega⟩, ⟨r.1, by omega⟩,
            by simp only [Fin.lt_def] at hij ⊢; exact hij,
            by simp only [Fin.lt_def] at hjr ⊢; exact hjr,
            by dsimp; have := r.2; omega, ?_, ?_⟩
          · rw [Fin.lt_def, skewSumCast_val_lt (le_of_lt d.1.2) d.2.1 d.2.2.1 _ i.2,
                skewSumCast_val_lt (le_of_lt d.1.2) d.2.1 d.2.2.1 _ r.2]
            have hi' : (⟨(⟨i.1, by omega⟩ : Fin k).1, i.2⟩ : Fin d.1.1) = i := rfl
            have hr' : (⟨(⟨r.1, by omega⟩ : Fin k).1, r.2⟩ : Fin d.1.1) = r := rfl
            rw [hi', hr']; rw [Fin.lt_def] at h1; omega
          · rw [Fin.lt_def, skewSumCast_val_lt (le_of_lt d.1.2) d.2.1 d.2.2.1 _ r.2,
                skewSumCast_val_lt (le_of_lt d.1.2) d.2.1 d.2.2.1 _ j.2]
            have hr' : (⟨(⟨r.1, by omega⟩ : Fin k).1, r.2⟩ : Fin d.1.1) = r := rfl
            have hj' : (⟨(⟨j.1, by omega⟩ : Fin k).1, j.2⟩ : Fin d.1.1) = j := rfl
            rw [hr', hj']; rw [Fin.lt_def] at h2; omega
        have hpos_mem : pos ∈ activeA (skewSumCast (le_of_lt d.1.2) d.2.1 d.2.2.1) := by
          simp only [activeA, Finset.mem_filter, Finset.mem_univ, true_and]
          exact hπA
        have hpos_lt : pos.1 < d.1.1 + dA d.2.2.1 := by
          rw [mem_activeA_iff hσA, dA_skewSumCast_avoids132 (le_of_lt d.1.2) hβ132 hαA] at hpos_mem
          exact hpos_mem
        refine ⟨⟨d.1, ⟨d.2.1, hβ132⟩, ⟨d.2.2.1, hαA, d.2.2.2⟩,
          ⟨⟨pos.1 - d.1.1, by omega⟩, by dsimp; omega, by dsimp; omega⟩⟩, Subtype.ext ?_⟩
        dsimp only [toPerm]
        have hposeq : (⟨d.1.1 + (pos.1 - d.1.1), by omega⟩ : Fin (k + 1)) = pos := by
          ext; dsimp; omega
        rw [hposeq, hσeq, hπeq]
    have hF_eq : F_poly (k + 1) =
        ∑ m : Fin k, ∑ _β : {β : Equiv.Perm (Fin m.1) // Avoids132 β},
          ∑ α : {α : Equiv.Perm (Fin (k - m.1)) // InClassA α ∧ IsSkewIndec α},
            ∑ j : {j : Fin (k + 1 - m.1) // 1 ≤ j.1 ∧ j.1 < dA α.1},
              (Polynomial.X : Polynomial ℚ) ^ (m.1 + j.1.1) := by
      unfold F_poly
      rw [← Equiv.sum_comp (Equiv.ofBijective toPerm hbij)]
      simp only [Equiv.ofBijective_apply, S]
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun β _ => ?_
      rcases β with ⟨β, hβ⟩
      rw [Fintype.sum_sigma]
      refine Finset.sum_congr rfl fun α _ => ?_
      rcases α with ⟨α, hαA, hαI⟩
      refine Finset.sum_congr rfl fun j _ => ?_
      rcases j with ⟨j, hj1, hjd⟩
      dsimp only [toPerm]
      have hd := dA_insMax_indec m.2 β hαI (pos := ⟨m.1 + j.1, by omega⟩) (by dsimp; omega)
        (by
          have hσA : InClassA (skewSumCast (le_of_lt m.2) β α) :=
            (inClassA_skewSumCast (le_of_lt m.2) β α).mpr ⟨avoids132_imp_inClassA hβ, hαA⟩
          have hmem : (⟨m.1 + j.1, by omega⟩ : Fin (k + 1)) ∈ activeA (skewSumCast (le_of_lt m.2) β α) := by
            rw [mem_activeA_iff hσA, dA_skewSumCast_avoids132 (le_of_lt m.2) hβ hαA]
            dsimp only at hjd ⊢; omega
          exact (Finset.mem_filter.mp hmem).2)
      rw [hd]
      simp
    rw [hF_eq, Finset.mul_sum]
    rw [Fin.sum_univ_eq_sum_range (fun m =>
      (1 - Polynomial.X) *
        ∑ _β : {β : Equiv.Perm (Fin m) // Avoids132 β},
          ∑ α : {α : Equiv.Perm (Fin (k - m)) // InClassA α ∧ IsSkewIndec α},
            ∑ j : {j : Fin (k + 1 - m) // 1 ≤ j.1 ∧ j.1 < dA α.1},
              (Polynomial.X : Polynomial ℚ) ^ (m + j.1.1)) k]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmk : m < k := Finset.mem_range.mp hm
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_avoids132 m]
    have hinner :
        (1 - Polynomial.X) *
          ∑ α : {α : Equiv.Perm (Fin (k - m)) // InClassA α ∧ IsSkewIndec α},
            ∑ j : {j : Fin (k + 1 - m) // 1 ≤ j.1 ∧ j.1 < dA α.1},
              (Polynomial.X : Polynomial ℚ) ^ (m + j.1.1) =
        Polynomial.X ^ m *
          (Polynomial.X * Polynomial.C ((F_poly (k - m)).eval 1) -
            Polynomial.X ^ 2 * F_poly (k - m)) := by
      rw [Finset.mul_sum, F_poly_eval_one (k - m)]
      have hcard :
          Polynomial.X ^ m *
            (Polynomial.X * Polynomial.C (Fintype.card {α : Equiv.Perm (Fin (k - m)) // InClassA α ∧ IsSkewIndec α} : ℚ) -
              Polynomial.X ^ 2 * F_poly (k - m)) =
          ∑ α : {α : Equiv.Perm (Fin (k - m)) // InClassA α ∧ IsSkewIndec α},
            Polynomial.X ^ m * (Polynomial.X - Polynomial.X ^ 2 * Polynomial.X ^ (dA α.1 - 2)) := by
        unfold F_poly
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          ← Finset.mul_sum]
        have hC : (Fintype.card {α : Equiv.Perm (Fin (k - m)) // InClassA α ∧ IsSkewIndec α} : Polynomial ℚ) =
            Polynomial.C (Fintype.card {α : Equiv.Perm (Fin (k - m)) // InClassA α ∧ IsSkewIndec α} : ℚ) := by
          simp
        rw [hC]; ring
      rw [hcard]
      refine Finset.sum_congr rfl fun α _ => ?_
      have hd2 : 2 ≤ dA α.1 := dA_ge_two (by omega) α.2.1
      have hdle : dA α.1 ≤ k + 1 - m := by have := dA_le α.1; omega
      rw [sum_subtype_fin_Ico 1 (dA α.1) hdle (fun j => (Polynomial.X : Polynomial ℚ) ^ (m + j))]
      simp_rw [pow_add]
      rw [← Finset.mul_sum, ← mul_assoc, mul_comm (1 - Polynomial.X) (Polynomial.X ^ m), mul_assoc,
        one_sub_X_mul_sum_Ico (dA α.1) (by omega)]
      have hpow : (Polynomial.X : Polynomial ℚ) ^ dA α.1 =
          Polynomial.X ^ 2 * Polynomial.X ^ (dA α.1 - 2) := by
        rw [← pow_add, show 2 + (dA α.1 - 2) = dA α.1 by omega]
      rw [hpow]
    have hCeq : (C_nat m : Polynomial ℚ) = Polynomial.C (C_nat m : ℚ) := by simp
    rw [← mul_assoc, mul_comm (1 - Polynomial.X) (C_nat m : Polynomial ℚ), mul_assoc, hinner, hCeq]
    unfold C_seq
    ring

private lemma card_classA_indec (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {α : Equiv.Perm (Fin n) // InClassA α ∧ IsSkewIndec α} = T_nat (n - 1) := by
  have h := kernel_F_eval_one F_poly F_poly_zero F_poly_one F_poly_rec n hn
  rw [F_poly_eval_one] at h
  exact Nat.cast_injective (R := ℚ) h

end ClassA

section ClassB

private def InClassB {n : ℕ} (σ : Equiv.Perm (Fin n)) : Prop :=
  Avoids1342 σ ∧ Avoids13254 σ

private instance {n : ℕ} (σ : Equiv.Perm (Fin n)) : Decidable (InClassB σ) := by
  unfold InClassB; infer_instance

private lemma avoids132_imp_inClassB {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : Avoids132 σ) :
    InClassB σ := ⟨avoids132_imp_1342 h, avoids132_imp_13254 h⟩

private lemma inClassB_skewSumCast {n m : ℕ} (hm : m ≤ n)
    (α : Equiv.Perm (Fin m)) (β : Equiv.Perm (Fin (n - m))) :
    InClassB (skewSumCast hm α β) ↔ InClassB α ∧ InClassB β := by
  unfold InClassB
  rw [avoids1342_skewSumCast, avoids13254_skewSumCast]
  tauto

private def ForbB {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1)) : Prop :=
  (∃ i j k : Fin n, i < j ∧ j.1 < pos.1 ∧ pos.1 ≤ k.1 ∧ σ i < σ k ∧ σ k < σ j) ∨
  (∃ a b c d : Fin n, a < b ∧ b < c ∧ c.1 < pos.1 ∧ pos.1 ≤ d.1 ∧
    σ a < σ c ∧ σ c < σ b ∧ σ b < σ d)

private instance {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1)) :
    Decidable (ForbB σ pos) := by
  unfold ForbB; infer_instance

private lemma insMax_inClassB_iff {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1)) :
    InClassB (insMax σ pos) ↔ InClassB σ ∧ ¬ ForbB σ pos := by
  constructor
  · rintro ⟨h1342, h13254⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i j k l hij hjk hkl ⟨h1, h2, h3⟩
      exact h1342 (insMaxLift pos i) (insMaxLift pos j) (insMaxLift pos k) (insMaxLift pos l)
        (insMaxLift_mono pos hij) (insMaxLift_mono pos hjk) (insMaxLift_mono pos hkl)
        ⟨by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h1,
         by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h2,
         by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h3⟩
    · intro a b c d e hab hbc hcd hde ⟨h1, h2, h3, h4⟩
      exact h13254 (insMaxLift pos a) (insMaxLift pos b) (insMaxLift pos c)
        (insMaxLift pos d) (insMaxLift pos e)
        (insMaxLift_mono pos hab) (insMaxLift_mono pos hbc)
        (insMaxLift_mono pos hcd) (insMaxLift_mono pos hde)
        ⟨by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h1,
         by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h2,
         by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h3,
         by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h4⟩
    · rintro (⟨i, j, k, hij, hj, hk, h1, h2⟩ | ⟨a, b, c, d, hab, hbc, hc, hd, h1, h2, h3⟩)
      · exact h1342 (insMaxLift pos i) (insMaxLift pos j) pos (insMaxLift pos k)
          (insMaxLift_mono pos hij) (insMaxLift_lt_pos pos hj) (insMaxLift_gt_pos pos hk)
          ⟨by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h1,
           by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h2,
           by rw [Fin.lt_def, insMaxLift_val, insMax_val_eq]; exact (σ j).2⟩
      · exact h13254 (insMaxLift pos a) (insMaxLift pos b) (insMaxLift pos c) pos (insMaxLift pos d)
          (insMaxLift_mono pos hab) (insMaxLift_mono pos hbc)
          (insMaxLift_lt_pos pos hc) (insMaxLift_gt_pos pos hd)
          ⟨by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h1,
           by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h2,
           by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h3,
           by rw [Fin.lt_def, insMaxLift_val, insMax_val_eq]; exact (σ d).2⟩
  · rintro ⟨⟨h1342, h13254⟩, hnf⟩
    constructor
    · intro i j k l hij hjk hkl ⟨h1, h2, h3⟩
      have hi := insMax_ne_pos_of_lt σ pos i l h1
      have hl := insMax_ne_pos_of_lt σ pos l j h2
      have hj := insMax_ne_pos_of_lt σ pos j k h3
      by_cases hk : k.1 = pos.1
      · have hkeq : k = pos := Fin.ext hk
        rw [hkeq] at hjk hkl
        exact hnf (Or.inl ⟨insMaxUnlift pos i hi, insMaxUnlift pos j hj, insMaxUnlift pos l hl,
          insMaxUnlift_mono pos hi hj hij,
          insMaxUnlift_lt_of_lt pos j hjk, insMaxUnlift_ge_of_gt pos l hkl,
          by rw [Fin.lt_def, ← insMaxUnlift_val σ pos i hi, ← insMaxUnlift_val σ pos l hl]; exact h1,
          by rw [Fin.lt_def, ← insMaxUnlift_val σ pos l hl, ← insMaxUnlift_val σ pos j hj]; exact h2⟩)
      · exact h1342 (insMaxUnlift pos i hi) (insMaxUnlift pos j hj)
          (insMaxUnlift pos k hk) (insMaxUnlift pos l hl)
          (insMaxUnlift_mono pos hi hj hij) (insMaxUnlift_mono pos hj hk hjk)
          (insMaxUnlift_mono pos hk hl hkl)
          ⟨by rw [Fin.lt_def, ← insMaxUnlift_val σ pos i hi, ← insMaxUnlift_val σ pos l hl]; exact h1,
           by rw [Fin.lt_def, ← insMaxUnlift_val σ pos l hl, ← insMaxUnlift_val σ pos j hj]; exact h2,
           by rw [Fin.lt_def, ← insMaxUnlift_val σ pos j hj, ← insMaxUnlift_val σ pos k hk]; exact h3⟩
    · intro a b c d e hab hbc hcd hde ⟨h1, h2, h3, h4⟩
      have ha := insMax_ne_pos_of_lt σ pos a c h1
      have hc := insMax_ne_pos_of_lt σ pos c b h2
      have hb := insMax_ne_pos_of_lt σ pos b e h3
      have he := insMax_ne_pos_of_lt σ pos e d h4
      by_cases hd : d.1 = pos.1
      · have hdeq : d = pos := Fin.ext hd
        rw [hdeq] at hcd hde
        exact hnf (Or.inr ⟨insMaxUnlift pos a ha, insMaxUnlift pos b hb,
          insMaxUnlift pos c hc, insMaxUnlift pos e he,
          insMaxUnlift_mono pos ha hb hab, insMaxUnlift_mono pos hb hc hbc,
          insMaxUnlift_lt_of_lt pos c hcd, insMaxUnlift_ge_of_gt pos e hde,
          by rw [Fin.lt_def, ← insMaxUnlift_val σ pos a ha, ← insMaxUnlift_val σ pos c hc]; exact h1,
          by rw [Fin.lt_def, ← insMaxUnlift_val σ pos c hc, ← insMaxUnlift_val σ pos b hb]; exact h2,
          by rw [Fin.lt_def, ← insMaxUnlift_val σ pos b hb, ← insMaxUnlift_val σ pos e he]; exact h3⟩)
      · exact h13254 (insMaxUnlift pos a ha) (insMaxUnlift pos b hb)
          (insMaxUnlift pos c hc) (insMaxUnlift pos d hd) (insMaxUnlift pos e he)
          (insMaxUnlift_mono pos ha hb hab) (insMaxUnlift_mono pos hb hc hbc)
          (insMaxUnlift_mono pos hc hd hcd) (insMaxUnlift_mono pos hd he hde)
          ⟨by rw [Fin.lt_def, ← insMaxUnlift_val σ pos a ha, ← insMaxUnlift_val σ pos c hc]; exact h1,
           by rw [Fin.lt_def, ← insMaxUnlift_val σ pos c hc, ← insMaxUnlift_val σ pos b hb]; exact h2,
           by rw [Fin.lt_def, ← insMaxUnlift_val σ pos b hb, ← insMaxUnlift_val σ pos e he]; exact h3,
           by rw [Fin.lt_def, ← insMaxUnlift_val σ pos e he, ← insMaxUnlift_val σ pos d hd]; exact h4⟩

private lemma not_forbB_last {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ¬ ForbB σ ⟨n, Nat.lt_succ_self n⟩ := by
  rintro (⟨_, _, k, _, _, hk, _, _⟩ | ⟨_, _, _, d, _, _, _, hd, _, _, _⟩)
  · dsimp at hk; have := k.2; omega
  · dsimp at hd; have := d.2; omega

private lemma not_forbB_of_lt_two {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1))
    (hpos : pos.1 < 2) : ¬ ForbB σ pos := by
  rintro (⟨i, j, _, hij, hj, _, _, _⟩ | ⟨a, b, c, _, hab, hbc, hc, _, _, _, _⟩)
  · simp only [Fin.lt_def] at hij; omega
  · simp only [Fin.lt_def] at hab hbc; omega

private def activeB {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun pos : Fin (n + 1) => InClassB (insMax σ pos))

private def dB {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ := (activeB σ).card

private def forbSetB {n : ℕ} (σ : Equiv.Perm (Fin n)) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun pos : Fin (n + 1) => ForbB σ pos)

private def prefB {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  if h : (forbSetB σ).Nonempty then ((forbSetB σ).min' h).1 else n + 1

private lemma avoids132_iff_forbSetB_empty {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Avoids132 σ ↔ forbSetB σ = ∅ := by
  constructor
  · intro h132
    rw [Finset.eq_empty_iff_forall_notMem]
    intro pos hmem
    have hf : ForbB σ pos := (Finset.mem_filter.mp hmem).2
    rcases hf with ⟨i, j, k, hij, hj, hk, h1, h2⟩ | ⟨a, b, c, _, hab, hbc, _, _, h1, h2, _⟩
    · exact h132 i j k hij (Fin.lt_def.mpr (by omega)) ⟨h1, h2⟩
    · exact h132 a b c hab hbc ⟨h1, h2⟩
  · intro hemp i j k hij hjk ⟨h1, h2⟩
    have hmem : (⟨j.1 + 1, by omega⟩ : Fin (n + 1)) ∈ forbSetB σ := by
      simp only [forbSetB, Finset.mem_filter, Finset.mem_univ, true_and]
      exact Or.inl ⟨i, j, k, hij, by dsimp; omega, by simp only [Fin.lt_def] at hjk; dsimp; omega, h1, h2⟩
    rw [hemp] at hmem
    exact Finset.notMem_empty _ hmem

private lemma forbSetB_nonempty_of_not_avoids132 {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : ¬ Avoids132 σ) : (forbSetB σ).Nonempty :=
  Finset.nonempty_iff_ne_empty.mpr (fun hemp => h ((avoids132_iff_forbSetB_empty σ).mpr hemp))

private lemma prefB_bounds_of_not_avoids132 {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : ¬ Avoids132 σ) : 2 ≤ prefB σ ∧ prefB σ < n := by
  have hne := forbSetB_nonempty_of_not_avoids132 h
  have hmem := Finset.min'_mem (forbSetB σ) hne
  have hf : ForbB σ ((forbSetB σ).min' hne) := (Finset.mem_filter.mp hmem).2
  have hge2 : 2 ≤ ((forbSetB σ).min' hne).1 := by
    by_contra hlt; push Not at hlt
    exact not_forbB_of_lt_two σ _ hlt hf
  have hltn : ((forbSetB σ).min' hne).1 < n := by
    have hlt := ((forbSetB σ).min' hne).2
    by_contra hge; push Not at hge
    have heq : (forbSetB σ).min' hne = ⟨n, Nat.lt_succ_self n⟩ := Fin.ext (by dsimp; omega)
    rw [heq] at hf
    exact not_forbB_last σ hf
  unfold prefB
  rw [dif_pos hne]
  exact ⟨hge2, hltn⟩

private lemma forbB_prefB_of_not_avoids132 {n : ℕ} {σ : Equiv.Perm (Fin n)}
    (h : ¬ Avoids132 σ) :
    ForbB σ ⟨prefB σ, by have := prefB_bounds_of_not_avoids132 h; omega⟩ := by
  have hne := forbSetB_nonempty_of_not_avoids132 h
  have hmem := Finset.min'_mem (forbSetB σ) hne
  have hf : ForbB σ ((forbSetB σ).min' hne) := (Finset.mem_filter.mp hmem).2
  have heq : (⟨prefB σ, by have := prefB_bounds_of_not_avoids132 h; omega⟩ : Fin (n + 1)) =
      (forbSetB σ).min' hne := by
    ext; simp [prefB, hne]
  rw [heq]; exact hf

private lemma not_forbB_of_lt_prefB {n : ℕ} (σ : Equiv.Perm (Fin n)) (pos : Fin (n + 1))
    (hpos : pos.1 < prefB σ) : ¬ ForbB σ pos := by
  intro hf
  have hmem : pos ∈ forbSetB σ := by
    simp only [forbSetB, Finset.mem_filter, Finset.mem_univ, true_and]; exact hf
  have hne : (forbSetB σ).Nonempty := ⟨pos, hmem⟩
  have hle : ((forbSetB σ).min' hne).1 ≤ pos.1 := Finset.min'_le (forbSetB σ) pos hmem
  unfold prefB at hpos
  rw [dif_pos hne] at hpos
  omega

private lemma prefB_eq_of_first {n : ℕ} (σ : Equiv.Perm (Fin n)) {p : ℕ} (hp : p < n + 1)
    (hf : ForbB σ ⟨p, hp⟩) (hmin : ∀ q : Fin (n + 1), q.1 < p → ¬ ForbB σ q) :
    ¬ Avoids132 σ ∧ prefB σ = p := by
  have hmem : (⟨p, hp⟩ : Fin (n + 1)) ∈ forbSetB σ := by
    simp only [forbSetB, Finset.mem_filter, Finset.mem_univ, true_and]; exact hf
  have hne : (forbSetB σ).Nonempty := ⟨⟨p, hp⟩, hmem⟩
  have hna : ¬ Avoids132 σ := fun h132 => by
    rw [(avoids132_iff_forbSetB_empty σ).mp h132] at hmem
    exact Finset.notMem_empty _ hmem
  refine ⟨hna, ?_⟩
  unfold prefB
  rw [dif_pos hne]
  have h1 : ((forbSetB σ).min' hne).1 ≤ p := Finset.min'_le (forbSetB σ) ⟨p, hp⟩ hmem
  have h2 : p ≤ ((forbSetB σ).min' hne).1 := by
    by_contra hlt; push Not at hlt
    have hf' : ForbB σ ((forbSetB σ).min' hne) :=
      (Finset.mem_filter.mp (Finset.min'_mem (forbSetB σ) hne)).2
    exact hmin _ hlt hf'
  omega

private lemma forbB_indec_mono {k : ℕ} {α : Equiv.Perm (Fin k)} (hαI : IsSkewIndec α)
    {p q : Fin (k + 1)} (hpq : p.1 < q.1) (hqk : q.1 < k) (hp : ForbB α p) :
    ForbB α q := by
  have h132p : ∃ i j c : Fin k, i < j ∧ j < c ∧ j.1 < p.1 ∧ α i < α c ∧ α c < α j := by
    rcases hp with ⟨i, j, c, hij, hj, hc, h1, h2⟩ | ⟨a, b, c, _, hab, hbc, hc, _, h1, h2, _⟩
    · exact ⟨i, j, c, hij, Fin.lt_def.mpr (by omega), hj, h1, h2⟩
    · exact ⟨a, b, c, hab, hbc, by simp only [Fin.lt_def] at hbc; omega, h1, h2⟩
  rcases h132p with ⟨i, j, c, hij, hjc, hjp, hic, hcj⟩
  let R : Finset (Fin k) := Finset.univ.filter (fun r : Fin k => q.1 ≤ r.1)
  have hRne : R.Nonempty := ⟨⟨q.1, hqk⟩, by simp [R]⟩
  rcases Finset.exists_max_image R α hRne with ⟨r_max, hr_mem, hr_max⟩
  have hr_ge : q.1 ≤ r_max.1 := (Finset.mem_filter.mp hr_mem).2
  have hne_ri : r_max ≠ i := fun h => by
    have := congrArg Fin.val h; simp only [Fin.lt_def] at hij; omega
  have hne_rj : r_max ≠ j := fun h => by
    have := congrArg Fin.val h; omega
  rcases lt_or_gt_of_ne (α.injective.ne hne_ri) with hri | hir
  · -- Subcase C: α r_max < α i
    let S : Finset (Fin k) := Finset.univ.filter (fun w : Fin k => w.1 < q.1 ∧ α r_max < α w)
    have hiS : i ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨by simp only [Fin.lt_def] at hij; omega, hri⟩
    have hSne : S.Nonempty := ⟨i, hiS⟩
    let w_max := S.max' hSne
    have hw_mem := Finset.mem_filter.mp (Finset.max'_mem S hSne)
    have hw_lt : w_max.1 < q.1 := hw_mem.2.1
    have hw_gt : α r_max < α w_max := hw_mem.2.2
    have hnc : ¬ IsCut α (w_max.1 + 1) := hαI.2 (w_max.1 + 1) (by omega) (by omega)
    rcases exists_lt_of_not_isCut (by omega) (by omega) hnc with ⟨u, v, hu, hv, huv⟩
    have hv_le : α v ≤ α r_max := by
      by_cases hvq : v.1 < q.1
      · by_contra hgt; push Not at hgt
        have hvS : v ∈ S := by
          simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hvq, hgt⟩
        have hle := Finset.le_max' S v hvS
        have : v.1 ≤ w_max.1 := hle
        omega
      · exact hr_max v (by simp [R]; omega)
    have hu_lt_r : α u < α r_max := lt_of_lt_of_le huv hv_le
    have hu_lt_w : u < w_max := by
      have hne : u ≠ w_max := fun h => by
        rw [h] at hu_lt_r; exact absurd (lt_trans hu_lt_r hw_gt) (lt_irrefl _)
      exact Fin.lt_def.mpr (by have := Fin.val_ne_of_ne hne; omega)
    exact Or.inl ⟨u, w_max, r_max, hu_lt_w, hw_lt, hr_ge, hu_lt_r, hw_gt⟩
  · -- α i < α r_max
    rcases lt_or_gt_of_ne (α.injective.ne hne_rj) with hrj | hjr
    · -- Subcase A: α i < α r_max < α j
      exact Or.inl ⟨i, j, r_max, hij, by omega, hr_ge, hir, hrj⟩
    · -- Subcase B: α j < α r_max
      by_cases hqc : q.1 ≤ c.1
      · exact Or.inl ⟨i, j, c, hij, by omega, hqc, hic, hcj⟩
      · exact Or.inr ⟨i, j, c, r_max, hij, hjc, by omega, hr_ge, hic, hcj, hjr⟩

private lemma activeB_indec_avoids132 {k : ℕ} {α : Equiv.Perm (Fin k)}
    (hαB : InClassB α) (h132 : Avoids132 α) :
    activeB α = Finset.univ ∧ dB α = k + 1 := by
  have heq : activeB α = Finset.univ := by
    ext pos
    simp only [activeB, Finset.mem_filter, Finset.mem_univ, true_and, insMax_inClassB_iff,
      hαB, iff_true]
    intro hf
    have hmem : pos ∈ forbSetB α := by simp [forbSetB, hf]
    rw [(avoids132_iff_forbSetB_empty α).mp h132] at hmem
    exact Finset.notMem_empty _ hmem
  exact ⟨heq, by unfold dB; rw [heq, Finset.card_univ, Fintype.card_fin]⟩

private lemma activeB_indec_not_avoids132 {k : ℕ} {α : Equiv.Perm (Fin k)}
    (hαB : InClassB α) (hαI : IsSkewIndec α) (hna : ¬ Avoids132 α) :
    (∀ pos : Fin (k + 1), pos ∈ activeB α ↔ pos.1 < prefB α ∨ pos.1 = k) ∧
    dB α = prefB α + 1 := by
  have hb := prefB_bounds_of_not_avoids132 hna
  have hf_min := forbB_prefB_of_not_avoids132 hna
  have hchar : ∀ pos : Fin (k + 1), pos ∈ activeB α ↔ pos.1 < prefB α ∨ pos.1 = k := by
    intro pos
    simp only [activeB, Finset.mem_filter, Finset.mem_univ, true_and, insMax_inClassB_iff, hαB, true_and]
    constructor
    · intro hnf
      by_contra h
      push Not at h
      rcases h with ⟨hge, hne⟩
      have hlt : pos.1 < k := by have := pos.2; omega
      by_cases heq : pos.1 = prefB α
      · have hpeq : pos = ⟨prefB α, by omega⟩ := Fin.ext heq
        rw [hpeq] at hnf; exact hnf hf_min
      · exact hnf (forbB_indec_mono hαI (p := ⟨prefB α, by omega⟩) (q := pos) (by dsimp; omega) hlt hf_min)
    · rintro (hlt | heq)
      · exact not_forbB_of_lt_prefB α pos hlt
      · have hpeq : pos = ⟨k, Nat.lt_succ_self k⟩ := Fin.ext heq
        rw [hpeq]; exact not_forbB_last α
  refine ⟨hchar, ?_⟩
  let S : Finset (Fin (k + 1)) := Finset.univ.filter (fun pos : Fin (k + 1) => pos.1 < prefB α)
  have heq : activeB α = insert ⟨k, Nat.lt_succ_self k⟩ S := by
    ext pos
    rw [hchar, Finset.mem_insert]
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff]
    tauto
  have hnot : (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) ∉ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]; omega
  unfold dB
  rw [heq, Finset.card_insert_of_notMem hnot, card_fin_filter_lt (by omega : prefB α ≤ k + 1)]

private lemma dB_ge_two_indec {k : ℕ} (hk : 1 ≤ k) {α : Equiv.Perm (Fin k)}
    (hαB : InClassB α) (hαI : IsSkewIndec α) : 2 ≤ dB α := by
  by_cases h132 : Avoids132 α
  · rw [(activeB_indec_avoids132 hαB h132).2]; omega
  · rw [(activeB_indec_not_avoids132 hαB hαI h132).2]
    have := prefB_bounds_of_not_avoids132 h132; omega

private lemma dB_le_succ {k : ℕ} (α : Equiv.Perm (Fin k)) : dB α ≤ k + 1 := by
  calc dB α = (activeB α).card := rfl
    _ ≤ (Finset.univ : Finset (Fin (k + 1))).card := Finset.card_le_univ _
    _ = k + 1 := by simp

private lemma mem_activeB_lt_iff_indec {k : ℕ} {α : Equiv.Perm (Fin k)}
    (hαB : InClassB α) (hαI : IsSkewIndec α) {j : Fin (k + 1)} (hj : j.1 < k) :
    j ∈ activeB α ↔ j.1 < dB α - 1 := by
  by_cases h132 : Avoids132 α
  · rcases activeB_indec_avoids132 hαB h132 with ⟨heq, hd⟩
    rw [heq, hd]; simp [hj]
  · rcases activeB_indec_not_avoids132 hαB hαI h132 with ⟨hchar, hd⟩
    rw [hchar, hd]; simp only [Nat.add_sub_cancel]
    exact ⟨fun h => h.resolve_right (by omega), Or.inl⟩

private lemma last_mem_activeB {k : ℕ} {α : Equiv.Perm (Fin k)} (hαB : InClassB α) :
    (⟨k, Nat.lt_succ_self k⟩ : Fin (k + 1)) ∈ activeB α := by
  simp only [activeB, Finset.mem_filter, Finset.mem_univ, true_and, insMax_inClassB_iff]
  exact ⟨hαB, not_forbB_last α⟩

private lemma zero_mem_activeB {k : ℕ} {α : Equiv.Perm (Fin k)} (hαB : InClassB α) :
    (⟨0, Nat.zero_lt_succ k⟩ : Fin (k + 1)) ∈ activeB α := by
  simp only [activeB, Finset.mem_filter, Finset.mem_univ, true_and, insMax_inClassB_iff]
  exact ⟨hαB, not_forbB_of_lt_two α ⟨0, Nat.zero_lt_succ k⟩ (by dsimp; omega)⟩

private lemma card_activeB_pos {k : ℕ} {α : Equiv.Perm (Fin k)} (hαB : InClassB α) :
    Fintype.card {j : Fin (k + 1) // 1 ≤ j.1 ∧ j ∈ activeB α} = dB α - 1 := by
  have heq : (Finset.univ.filter (fun j : Fin (k + 1) => 1 ≤ j.1 ∧ j ∈ activeB α)) =
      (activeB α).erase ⟨0, Nat.zero_lt_succ k⟩ := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, ne_eq, Fin.ext_iff]
    constructor
    · rintro ⟨h1, hmem⟩; exact ⟨by omega, hmem⟩
    · rintro ⟨hne, hmem⟩; exact ⟨by omega, hmem⟩
  rw [Fintype.card_subtype, heq, Finset.card_erase_of_mem (zero_mem_activeB hαB)]
  rfl

private lemma forbB_skewSumCast_le {n m : ℕ} (hm : m ≤ n)
    (β : Equiv.Perm (Fin m)) (α : Equiv.Perm (Fin (n - m)))
    (pos : Fin (n + 1)) (hpos : pos.1 ≤ m) :
    ForbB (skewSumCast hm β α) pos ↔ ForbB β ⟨pos.1, by omega⟩ := by
  constructor
  · rintro (⟨i, j, k, hij, hj, hk, h1, h2⟩ | ⟨a, b, c, d, hab, hbc, hc, hd, h1, h2, h3⟩)
    · have hj' : j.1 < m := by omega
      have hi' : i.1 < m := by simp only [Fin.lt_def] at hij; omega
      have hk' : k.1 < m := by
        by_contra hge
        exact absurd (lt_trans h1 (skewSumCast_lt_ge hm β α i k hi' (by omega))) (lt_irrefl _)
      rw [Fin.lt_def, skewSumCast_val_lt hm β α i hi', skewSumCast_val_lt hm β α k hk'] at h1
      rw [Fin.lt_def, skewSumCast_val_lt hm β α k hk', skewSumCast_val_lt hm β α j hj'] at h2
      exact Or.inl ⟨⟨i.1, hi'⟩, ⟨j.1, hj'⟩, ⟨k.1, hk'⟩,
        by simp only [Fin.lt_def] at hij ⊢; exact hij,
        by dsimp; exact hj, by dsimp; exact hk,
        Fin.lt_def.mpr (by omega), Fin.lt_def.mpr (by omega)⟩
    · have hc' : c.1 < m := by omega
      have hb' : b.1 < m := by simp only [Fin.lt_def] at hbc; omega
      have ha' : a.1 < m := by simp only [Fin.lt_def] at hab; omega
      have hd' : d.1 < m := by
        by_contra hge
        have hlt := skewSumCast_lt_ge hm β α a d ha' (by omega)
        exact absurd (lt_trans (lt_trans (lt_trans h1 h2) h3) hlt) (lt_irrefl _)
      rw [Fin.lt_def, skewSumCast_val_lt hm β α a ha', skewSumCast_val_lt hm β α c hc'] at h1
      rw [Fin.lt_def, skewSumCast_val_lt hm β α c hc', skewSumCast_val_lt hm β α b hb'] at h2
      rw [Fin.lt_def, skewSumCast_val_lt hm β α b hb', skewSumCast_val_lt hm β α d hd'] at h3
      exact Or.inr ⟨⟨a.1, ha'⟩, ⟨b.1, hb'⟩, ⟨c.1, hc'⟩, ⟨d.1, hd'⟩,
        by simp only [Fin.lt_def] at hab ⊢; exact hab,
        by simp only [Fin.lt_def] at hbc ⊢; exact hbc,
        by dsimp; exact hc, by dsimp; exact hd,
        Fin.lt_def.mpr (by omega), Fin.lt_def.mpr (by omega), Fin.lt_def.mpr (by omega)⟩
  · rintro (⟨i, j, k, hij, hj, hk, h1, h2⟩ | ⟨a, b, c, d, hab, hbc, hc, hd, h1, h2, h3⟩)
    · refine Or.inl ⟨⟨i.1, by omega⟩, ⟨j.1, by omega⟩, ⟨k.1, by omega⟩,
        by simp only [Fin.lt_def] at hij ⊢; exact hij,
        by dsimp at hj ⊢; exact hj, by dsimp at hk ⊢; exact hk, ?_, ?_⟩
      · rw [Fin.lt_def, skewSumCast_val_lt hm β α _ i.2, skewSumCast_val_lt hm β α _ k.2]
        rw [Fin.lt_def] at h1; exact Nat.add_lt_add_right h1 _
      · rw [Fin.lt_def, skewSumCast_val_lt hm β α _ k.2, skewSumCast_val_lt hm β α _ j.2]
        rw [Fin.lt_def] at h2; exact Nat.add_lt_add_right h2 _
    · refine Or.inr ⟨⟨a.1, by omega⟩, ⟨b.1, by omega⟩, ⟨c.1, by omega⟩, ⟨d.1, by omega⟩,
        by simp only [Fin.lt_def] at hab ⊢; exact hab,
        by simp only [Fin.lt_def] at hbc ⊢; exact hbc,
        by dsimp at hc ⊢; exact hc, by dsimp at hd ⊢; exact hd, ?_, ?_, ?_⟩
      · rw [Fin.lt_def, skewSumCast_val_lt hm β α _ a.2, skewSumCast_val_lt hm β α _ c.2]
        rw [Fin.lt_def] at h1; exact Nat.add_lt_add_right h1 _
      · rw [Fin.lt_def, skewSumCast_val_lt hm β α _ c.2, skewSumCast_val_lt hm β α _ b.2]
        rw [Fin.lt_def] at h2; exact Nat.add_lt_add_right h2 _
      · rw [Fin.lt_def, skewSumCast_val_lt hm β α _ b.2, skewSumCast_val_lt hm β α _ d.2]
        rw [Fin.lt_def] at h3; exact Nat.add_lt_add_right h3 _

private lemma forbB_skewSumCast_ge {n m : ℕ} (hm : m ≤ n)
    (β : Equiv.Perm (Fin m)) (α : Equiv.Perm (Fin (n - m)))
    (pos : Fin (n + 1)) (hpos : m ≤ pos.1) :
    ForbB (skewSumCast hm β α) pos ↔ ForbB α ⟨pos.1 - m, by omega⟩ := by
  constructor
  · rintro (⟨i, j, k, hij, hj, hk, h1, h2⟩ | ⟨a, b, c, d, hab, hbc, hc, hd, h1, h2, h3⟩)
    · have hk' : m ≤ k.1 := by omega
      have hi' : m ≤ i.1 := by
        by_contra hlt
        exact absurd (lt_trans h1 (skewSumCast_lt_ge hm β α i k (by omega) hk')) (lt_irrefl _)
      have hj' : m ≤ j.1 := by simp only [Fin.lt_def] at hij; omega
      rw [Fin.lt_def, skewSumCast_val_ge hm β α i hi', skewSumCast_val_ge hm β α k hk'] at h1
      rw [Fin.lt_def, skewSumCast_val_ge hm β α k hk', skewSumCast_val_ge hm β α j hj'] at h2
      exact Or.inl ⟨⟨i.1 - m, by omega⟩, ⟨j.1 - m, by omega⟩, ⟨k.1 - m, by omega⟩,
        by simp only [Fin.lt_def] at hij ⊢; omega,
        by dsimp; omega, by dsimp; omega,
        Fin.lt_def.mpr h1, Fin.lt_def.mpr h2⟩
    · have hd' : m ≤ d.1 := by omega
      have ha' : m ≤ a.1 := by
        by_contra hlt
        have hgt := skewSumCast_lt_ge hm β α a d (by omega) hd'
        exact absurd (lt_trans (lt_trans (lt_trans h1 h2) h3) hgt) (lt_irrefl _)
      have hb' : m ≤ b.1 := by simp only [Fin.lt_def] at hab; omega
      have hc' : m ≤ c.1 := by simp only [Fin.lt_def] at hbc; omega
      rw [Fin.lt_def, skewSumCast_val_ge hm β α a ha', skewSumCast_val_ge hm β α c hc'] at h1
      rw [Fin.lt_def, skewSumCast_val_ge hm β α c hc', skewSumCast_val_ge hm β α b hb'] at h2
      rw [Fin.lt_def, skewSumCast_val_ge hm β α b hb', skewSumCast_val_ge hm β α d hd'] at h3
      exact Or.inr ⟨⟨a.1 - m, by omega⟩, ⟨b.1 - m, by omega⟩, ⟨c.1 - m, by omega⟩, ⟨d.1 - m, by omega⟩,
        by simp only [Fin.lt_def] at hab ⊢; omega,
        by simp only [Fin.lt_def] at hbc ⊢; omega,
        by dsimp; omega, by dsimp; omega,
        Fin.lt_def.mpr h1, Fin.lt_def.mpr h2, Fin.lt_def.mpr h3⟩
  · rintro (⟨i, j, k, hij, hj, hk, h1, h2⟩ | ⟨a, b, c, d, hab, hbc, hc, hd, h1, h2, h3⟩)
    · refine Or.inl ⟨⟨i.1 + m, by omega⟩, ⟨j.1 + m, by omega⟩, ⟨k.1 + m, by omega⟩,
        by simp only [Fin.lt_def] at hij ⊢; omega,
        by dsimp at hj ⊢; omega, by dsimp at hk ⊢; omega, ?_, ?_⟩
      · rw [Fin.lt_def, skewSumCast_val_ge hm β α _ (by dsimp; omega),
            skewSumCast_val_ge hm β α _ (by dsimp; omega)]
        rw [Fin.lt_def] at h1; simpa using h1
      · rw [Fin.lt_def, skewSumCast_val_ge hm β α _ (by dsimp; omega),
            skewSumCast_val_ge hm β α _ (by dsimp; omega)]
        rw [Fin.lt_def] at h2; simpa using h2
    · refine Or.inr ⟨⟨a.1 + m, by omega⟩, ⟨b.1 + m, by omega⟩, ⟨c.1 + m, by omega⟩, ⟨d.1 + m, by omega⟩,
        by simp only [Fin.lt_def] at hab ⊢; omega,
        by simp only [Fin.lt_def] at hbc ⊢; omega,
        by dsimp at hc ⊢; omega, by dsimp at hd ⊢; omega, ?_, ?_, ?_⟩
      · rw [Fin.lt_def, skewSumCast_val_ge hm β α _ (by dsimp; omega),
            skewSumCast_val_ge hm β α _ (by dsimp; omega)]
        rw [Fin.lt_def] at h1; simpa using h1
      · rw [Fin.lt_def, skewSumCast_val_ge hm β α _ (by dsimp; omega),
            skewSumCast_val_ge hm β α _ (by dsimp; omega)]
        rw [Fin.lt_def] at h2; simpa using h2
      · rw [Fin.lt_def, skewSumCast_val_ge hm β α _ (by dsimp; omega),
            skewSumCast_val_ge hm β α _ (by dsimp; omega)]
        rw [Fin.lt_def] at h3; simpa using h3

private lemma prefB_skewSumCast_not_avoids132_left {n m : ℕ} (hm : m ≤ n)
    {β : Equiv.Perm (Fin m)} (hβ : ¬ Avoids132 β) (α : Equiv.Perm (Fin (n - m))) :
    ¬ Avoids132 (skewSumCast hm β α) ∧ prefB (skewSumCast hm β α) = prefB β := by
  have hb := prefB_bounds_of_not_avoids132 hβ
  refine prefB_eq_of_first (skewSumCast hm β α) (by omega : prefB β < n + 1) ?_ ?_
  · rw [forbB_skewSumCast_le hm β α _ (by dsimp; omega)]
    exact forbB_prefB_of_not_avoids132 hβ
  · intro q hq
    rw [forbB_skewSumCast_le hm β α q (by omega)]
    exact not_forbB_of_lt_prefB β ⟨q.1, by omega⟩ (by dsimp; omega)

private lemma prefB_skewSumCast_avoids132_left {n m : ℕ} (hm : m ≤ n)
    {β : Equiv.Perm (Fin m)} (hβ : Avoids132 β)
    {α : Equiv.Perm (Fin (n - m))} (hα : ¬ Avoids132 α) :
    ¬ Avoids132 (skewSumCast hm β α) ∧ prefB (skewSumCast hm β α) = m + prefB α := by
  have hb := prefB_bounds_of_not_avoids132 hα
  refine prefB_eq_of_first (skewSumCast hm β α) (by omega : m + prefB α < n + 1) ?_ ?_
  · rw [forbB_skewSumCast_ge hm β α _ (by dsimp; omega)]
    have heq : (⟨m + prefB α - m, by omega⟩ : Fin (n - m + 1)) = ⟨prefB α, by omega⟩ := by
      ext; simp
    rw [heq]; exact forbB_prefB_of_not_avoids132 hα
  · intro q hq
    by_cases hqm : q.1 ≤ m
    · rw [forbB_skewSumCast_le hm β α q hqm]
      intro hf
      have hmem : (⟨q.1, by omega⟩ : Fin (m + 1)) ∈ forbSetB β := by simp [forbSetB, hf]
      rw [(avoids132_iff_forbSetB_empty β).mp hβ] at hmem
      exact Finset.notMem_empty _ hmem
    · rw [forbB_skewSumCast_ge hm β α q (by omega)]
      exact not_forbB_of_lt_prefB α ⟨q.1 - m, by omega⟩ (by dsimp; omega)

private lemma forbB_insMax_of_forbB {N : ℕ} (σ : Equiv.Perm (Fin N)) (pos : Fin (N + 1))
    (q : Fin (N + 2)) (hqp : q.1 ≤ pos.1) (hf : ForbB σ ⟨q.1, by omega⟩) :
    ForbB (insMax σ pos) q := by
  rcases hf with ⟨i, j, k, hij, hj, hk, h1, h2⟩ | ⟨a, b, c, d, hab, hbc, hc, hd, h1, h2, h3⟩
  · dsimp at hj hk
    refine Or.inl ⟨insMaxLift pos i, insMaxLift pos j, insMaxLift pos k,
      insMaxLift_mono pos hij, ?_, ?_,
      by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h1,
      by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h2⟩
    · simp only [insMaxLift, show j.1 < pos.1 by omega, ↓reduceIte]; exact hj
    · dsimp only [insMaxLift]; split_ifs <;> (dsimp; omega)
  · dsimp at hc hd
    refine Or.inr ⟨insMaxLift pos a, insMaxLift pos b, insMaxLift pos c, insMaxLift pos d,
      insMaxLift_mono pos hab, insMaxLift_mono pos hbc, ?_, ?_,
      by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h1,
      by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h2,
      by rw [Fin.lt_def, insMaxLift_val, insMaxLift_val]; exact h3⟩
    · simp only [insMaxLift, show c.1 < pos.1 by omega, ↓reduceIte]; exact hc
    · dsimp only [insMaxLift]; split_ifs <;> (dsimp; omega)

private lemma not_forbB_insMax_of_all_not_forbB {N : ℕ} (σ : Equiv.Perm (Fin N)) (pos : Fin (N + 1))
    (q : Fin (N + 2)) (hqp : q.1 ≤ pos.1)
    (hnone : ∀ p : Fin (N + 1), p.1 ≤ q.1 → ¬ ForbB σ p) :
    ¬ ForbB (insMax σ pos) q := by
  rintro (⟨i, j, k, hij, hj, hk, h1, h2⟩ | ⟨a, b, c, d, hab, hbc, hc, hd, h1, h2, h3⟩)
  · have hk_ne : k.1 ≠ pos.1 := insMax_ne_pos_of_lt σ pos k j h2
    have hj_lt : j < pos := Fin.lt_def.mpr (by omega)
    have hi_lt : i < pos := lt_trans hij hj_lt
    have hi_ne : i.1 ≠ pos.1 := by rw [Fin.lt_def] at hi_lt; omega
    have hj_ne : j.1 ≠ pos.1 := by rw [Fin.lt_def] at hj_lt; omega
    have hk_ge : q.1 ≤ (insMaxUnlift pos k hk_ne).1 := by
      dsimp only [insMaxUnlift]; split_ifs <;> (dsimp; omega)
    have hj_lt' : (insMaxUnlift pos j hj_ne).1 < q.1 := by
      simp only [insMaxUnlift, show j.1 < pos.1 by omega, ↓reduceDIte]; exact hj
    exact hnone ⟨q.1, by omega⟩ le_rfl (Or.inl ⟨insMaxUnlift pos i hi_ne,
      insMaxUnlift pos j hj_ne, insMaxUnlift pos k hk_ne,
      insMaxUnlift_mono pos hi_ne hj_ne hij, by dsimp; exact hj_lt', by dsimp; exact hk_ge,
      by rw [Fin.lt_def, ← insMaxUnlift_val σ pos i hi_ne, ← insMaxUnlift_val σ pos k hk_ne]; exact h1,
      by rw [Fin.lt_def, ← insMaxUnlift_val σ pos k hk_ne, ← insMaxUnlift_val σ pos j hj_ne]; exact h2⟩)
  · have hc_lt : c < pos := Fin.lt_def.mpr (by omega)
    have hb_lt : b < pos := lt_trans hbc hc_lt
    have ha_lt : a < pos := lt_trans hab hb_lt
    have ha_ne : a.1 ≠ pos.1 := by rw [Fin.lt_def] at ha_lt; omega
    have hb_ne : b.1 ≠ pos.1 := by rw [Fin.lt_def] at hb_lt; omega
    have hc_ne : c.1 ≠ pos.1 := by rw [Fin.lt_def] at hc_lt; omega
    by_cases hd_eq : d.1 = pos.1
    · -- (a', b', c') is a 132 strictly before q, so ForbB σ (b'.1 + 1) with b'.1 + 1 ≤ c'.1 < q.1
      let ha' := insMaxUnlift pos a ha_ne
      let hb' := insMaxUnlift pos b hb_ne
      let hc' := insMaxUnlift pos c hc_ne
      have hbc' : hb' < hc' := insMaxUnlift_mono pos hb_ne hc_ne hbc
      have hc'_lt : hc'.1 < q.1 := by
        simp only [hc', insMaxUnlift, show c.1 < pos.1 by omega, ↓reduceDIte]; exact hc
      have hb'_lt : hb'.1 + 1 ≤ q.1 := by simp only [Fin.lt_def] at hbc'; omega
      exact hnone ⟨hb'.1 + 1, by omega⟩ hb'_lt (Or.inl ⟨ha', hb', hc',
        insMaxUnlift_mono pos ha_ne hb_ne hab, by dsimp; omega,
        by simp only [Fin.lt_def] at hbc'; dsimp; omega,
        by rw [Fin.lt_def, ← insMaxUnlift_val σ pos a ha_ne, ← insMaxUnlift_val σ pos c hc_ne]; exact h1,
        by rw [Fin.lt_def, ← insMaxUnlift_val σ pos c hc_ne, ← insMaxUnlift_val σ pos b hb_ne]; exact h2⟩)
    · have hd_ge : q.1 ≤ (insMaxUnlift pos d hd_eq).1 := by
        dsimp only [insMaxUnlift]; split_ifs <;> (dsimp; omega)
      have hc_lt' : (insMaxUnlift pos c hc_ne).1 < q.1 := by
        simp only [insMaxUnlift, show c.1 < pos.1 by omega, ↓reduceDIte]; exact hc
      exact hnone ⟨q.1, by omega⟩ le_rfl (Or.inr ⟨insMaxUnlift pos a ha_ne,
        insMaxUnlift pos b hb_ne, insMaxUnlift pos c hc_ne, insMaxUnlift pos d hd_eq,
        insMaxUnlift_mono pos ha_ne hb_ne hab, insMaxUnlift_mono pos hb_ne hc_ne hbc,
        by dsimp; exact hc_lt', by dsimp; exact hd_ge,
        by rw [Fin.lt_def, ← insMaxUnlift_val σ pos a ha_ne, ← insMaxUnlift_val σ pos c hc_ne]; exact h1,
        by rw [Fin.lt_def, ← insMaxUnlift_val σ pos c hc_ne, ← insMaxUnlift_val σ pos b hb_ne]; exact h2,
        by rw [Fin.lt_def, ← insMaxUnlift_val σ pos b hb_ne, ← insMaxUnlift_val σ pos d hd_eq]; exact h3⟩)

private lemma prefB_insMax_of_prefB_le {N : ℕ} {σ : Equiv.Perm (Fin N)}
    (hna : ¬ Avoids132 σ) {pos : Fin (N + 1)} (hle : prefB σ ≤ pos.1) :
    ¬ Avoids132 (insMax σ pos) ∧ prefB (insMax σ pos) = prefB σ := by
  have hb := prefB_bounds_of_not_avoids132 hna
  refine prefB_eq_of_first (insMax σ pos) (by omega : prefB σ < N + 2) ?_ ?_
  · exact forbB_insMax_of_forbB σ pos ⟨prefB σ, by omega⟩ (by dsimp; exact hle)
      (forbB_prefB_of_not_avoids132 hna)
  · intro q hq
    exact not_forbB_insMax_of_all_not_forbB σ pos q (by omega)
      (fun p hp => not_forbB_of_lt_prefB σ p (by omega))

private lemma prefB_insMax_case2 {N m : ℕ} (hm : m < N)
    {β : Equiv.Perm (Fin m)} (hβ : Avoids132 β)
    {α : Equiv.Perm (Fin (N - m))} (hαI : IsSkewIndec α)
    {pos : Fin (N + 1)} (hmp : m < pos.1) (hpN : pos.1 < N)
    (hnfα : ¬ ForbB α ⟨pos.1 - m, by omega⟩) :
    ¬ Avoids132 (insMax (skewSumCast (le_of_lt hm) β α) pos) ∧
    prefB (insMax (skewSumCast (le_of_lt hm) β α) pos) = pos.1 + 1 := by
  let σ := skewSumCast (le_of_lt hm) β α
  have hnone : ∀ p : Fin (N + 1), p.1 ≤ pos.1 → ¬ ForbB σ p := by
    intro p hp
    by_cases hpm : p.1 ≤ m
    · rw [forbB_skewSumCast_le (le_of_lt hm) β α p hpm]
      intro hf
      have hmem : (⟨p.1, by omega⟩ : Fin (m + 1)) ∈ forbSetB β := by simp [forbSetB, hf]
      rw [(avoids132_iff_forbSetB_empty β).mp hβ] at hmem
      exact Finset.notMem_empty _ hmem
    · rw [forbB_skewSumCast_ge (le_of_lt hm) β α p (by omega)]
      by_cases hpeq : p.1 = pos.1
      · have heq : (⟨p.1 - m, by omega⟩ : Fin (N - m + 1)) = ⟨pos.1 - m, by omega⟩ := by
          ext; simp [hpeq]
        rw [heq]; exact hnfα
      · intro hf
        exact hnfα (forbB_indec_mono hαI (p := ⟨p.1 - m, by omega⟩)
          (q := ⟨pos.1 - m, by omega⟩) (by dsimp; omega) (by dsimp; omega) hf)
  refine prefB_eq_of_first (insMax σ pos) (by omega : pos.1 + 1 < N + 2) ?_ ?_
  · have hnc : ¬ IsCut α (pos.1 - m) := hαI.2 (pos.1 - m) (by omega) (by omega)
    rcases exists_lt_of_not_isCut (by omega) (by omega) hnc with ⟨u, v, hu, hv, huv⟩
    refine Or.inl ⟨⟨m + u.1, by omega⟩, pos, ⟨m + v.1 + 1, by omega⟩,
      by rw [Fin.lt_def]; dsimp; omega, by dsimp; omega, by dsimp; omega, ?_, ?_⟩
    · rw [Fin.lt_def, insMax_val_lt σ pos _ (by dsimp; omega),
          insMax_val_gt σ pos _ (by dsimp; omega),
          skewSumCast_val_ge (le_of_lt hm) β α _ (by dsimp; omega),
          skewSumCast_val_ge (le_of_lt hm) β α _ (by dsimp; omega)]
      have hu' : (⟨m + u.1 - m, by omega⟩ : Fin (N - m)) = u := by ext; simp
      have hv' : (⟨m + v.1 + 1 - 1 - m, by omega⟩ : Fin (N - m)) = v := by ext; simp
      rw [hu', hv']; exact huv
    · rw [Fin.lt_def, insMax_val_gt σ pos _ (by dsimp; omega), insMax_val_eq]
      exact (σ ⟨m + v.1 + 1 - 1, by omega⟩).2
  · intro q hq
    exact not_forbB_insMax_of_all_not_forbB σ pos q (by omega) (fun p hp => hnone p (by omega))

private def B_all (n : ℕ) : ℕ :=
  Fintype.card {σ : Equiv.Perm (Fin n) // InClassB σ}

private def B_ind (n : ℕ) : ℕ :=
  Fintype.card {α : Equiv.Perm (Fin n) // InClassB α ∧ IsSkewIndec α}

private def S_nat (n : ℕ) : ℕ :=
  ∑ α : {α : Equiv.Perm (Fin n) // InClassB α ∧ IsSkewIndec α}, (dB α.1 - 1)

private noncomputable def G_poly (n : ℕ) : Polynomial ℚ :=
  ∑ α : {α : Equiv.Perm (Fin n) // InClassB α ∧ IsSkewIndec α},
    (Polynomial.X : Polynomial ℚ) ^ (dB α.1 - 2)

private noncomputable def G0_poly (n : ℕ) : Polynomial ℚ :=
  if n = 0 then 0 else C_seq (n - 1)

private noncomputable def G1_poly (n : ℕ) : Polynomial ℚ :=
  G_poly n - G0_poly n

private noncomputable def H_poly (m : ℕ) : Polynomial ℚ :=
  ∑ β : {β : Equiv.Perm (Fin m) // InClassB β ∧ ¬ Avoids132 β},
    (Polynomial.X : Polynomial ℚ) ^ (prefB β.1 - 1)

private lemma G_poly_eval_one (n : ℕ) :
    (G_poly n).eval 1 = (B_ind n : ℚ) := by
  unfold G_poly B_ind
  rw [Polynomial.eval_finsetSum]
  simp

private lemma G_poly_zero : G_poly 0 = 0 := by
  unfold G_poly
  have hempty : IsEmpty {α : Equiv.Perm (Fin 0) // InClassB α ∧ IsSkewIndec α} :=
    ⟨fun ⟨_, _, h⟩ => by have := h.1; omega⟩
  simp

private lemma G_poly_one : G_poly 1 = 1 := by
  unfold G_poly
  have h132 : Avoids132 (1 : Equiv.Perm (Fin 1)) :=
    fun i j k hij hjk => by simp only [Fin.lt_def] at hij hjk; omega
  have h1B : InClassB (1 : Equiv.Perm (Fin 1)) := avoids132_imp_inClassB h132
  have h1I : IsSkewIndec (1 : Equiv.Perm (Fin 1)) := ⟨by omega, fun m hm0 hm1 => by omega⟩
  have huniq : ∀ x : {α : Equiv.Perm (Fin 1) // InClassB α ∧ IsSkewIndec α},
      x = ⟨1, h1B, h1I⟩ := fun ⟨α, _, _⟩ => Subtype.ext (Subsingleton.elim α 1)
  have hd : dB (1 : Equiv.Perm (Fin 1)) = 2 := (activeB_indec_avoids132 h1B h132).2
  rw [Finset.sum_eq_single ⟨1, h1B, h1I⟩]
  · simp [hd]
  · intro b _ hb; exact absurd (huniq b) hb
  · intro h; exact absurd (Finset.mem_univ _) h

private lemma B_ind_zero : B_ind 0 = 0 := by
  unfold B_ind
  have hempty : IsEmpty {α : Equiv.Perm (Fin 0) // InClassB α ∧ IsSkewIndec α} :=
    ⟨fun ⟨_, _, h⟩ => by have := h.1; omega⟩
  simp

private lemma B_ind_one : B_ind 1 = 1 := by
  have h := G_poly_eval_one 1
  rw [G_poly_one] at h
  simp only [Polynomial.eval_one] at h
  exact Nat.cast_injective (R := ℚ) h.symm

private lemma G0_poly_eq_sum (n : ℕ) :
    G0_poly n = ∑ α : {α : Equiv.Perm (Fin n) // InClassB α ∧ IsSkewIndec α ∧ Avoids132 α},
      (Polynomial.X : Polynomial ℚ) ^ (dB α.1 - 2) := by
  cases n with
  | zero =>
    have hempty : IsEmpty {α : Equiv.Perm (Fin 0) // InClassB α ∧ IsSkewIndec α ∧ Avoids132 α} :=
      ⟨fun ⟨_, _, h, _⟩ => by have := h.1; omega⟩
    simp [G0_poly]
  | succ m =>
    have heq_sum :
        (∑ α : {α : Equiv.Perm (Fin (m + 1)) // InClassB α ∧ IsSkewIndec α ∧ Avoids132 α},
          (Polynomial.X : Polynomial ℚ) ^ (dB α.1 - 2)) =
        ∑ _α : {α : Equiv.Perm (Fin (m + 1)) // InClassB α ∧ IsSkewIndec α ∧ Avoids132 α},
          (Polynomial.X : Polynomial ℚ) ^ m := by
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [(activeB_indec_avoids132 α.2.1 α.2.2.2).2]
      simp
    rw [heq_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : Fintype.card {α : Equiv.Perm (Fin (m + 1)) // InClassB α ∧ IsSkewIndec α ∧ Avoids132 α} =
        C_nat m := by
      have heqv : {α : Equiv.Perm (Fin (m + 1)) // InClassB α ∧ IsSkewIndec α ∧ Avoids132 α} ≃
          {α : Equiv.Perm (Fin (m + 1)) // Avoids132 α ∧ IsSkewIndec α} :=
        Equiv.subtypeEquivRight (fun α => ⟨fun h => ⟨h.2.2, h.2.1⟩, fun h => ⟨avoids132_imp_inClassB h.1, h.2, h.1⟩⟩)
      rw [Fintype.card_congr heqv, card_avoids132_indec (m + 1) (by omega), Nat.add_sub_cancel]
    rw [hcard]
    simp [G0_poly, C_seq]

private lemma G1_poly_eq_sum (n : ℕ) :
    G1_poly n = ∑ α : {α : Equiv.Perm (Fin n) // InClassB α ∧ IsSkewIndec α ∧ ¬ Avoids132 α},
      (Polynomial.X : Polynomial ℚ) ^ (dB α.1 - 2) := by
  unfold G1_poly
  rw [sub_eq_iff_eq_add, G0_poly_eq_sum]
  symm
  unfold G_poly
  let P := fun α : {α : Equiv.Perm (Fin n) // InClassB α ∧ IsSkewIndec α} => Avoids132 α.1
  have hsplit := (Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset {α : Equiv.Perm (Fin n) // InClassB α ∧ IsSkewIndec α})
    P (fun α => (Polynomial.X : Polynomial ℚ) ^ (dB α.1 - 2))).symm
  rw [hsplit, add_comm (∑ α ∈ Finset.univ.filter P, _)]
  congr 1
  · refine Finset.sum_bij (fun α _ => (⟨α.1, α.2.1, α.2.2.1⟩ : {α : Equiv.Perm (Fin n) // InClassB α ∧ IsSkewIndec α}))
      ?_ ?_ ?_ ?_
    · intro α _; simp only [Finset.mem_filter, Finset.mem_univ, true_and, P]; exact α.2.2.2
    · intro a _ b _ h; exact Subtype.ext (congrArg (fun x => x.1) h)
    · intro x hx
      have hnx := (Finset.mem_filter.mp hx).2
      exact ⟨⟨x.1, x.2.1, x.2.2, hnx⟩, Finset.mem_univ _, rfl⟩
    · intro _ _; rfl
  · refine Finset.sum_bij (fun α _ => (⟨α.1, α.2.1, α.2.2.1⟩ : {α : Equiv.Perm (Fin n) // InClassB α ∧ IsSkewIndec α}))
      ?_ ?_ ?_ ?_
    · intro α _; simp only [Finset.mem_filter, Finset.mem_univ, true_and, P]; exact α.2.2.2
    · intro a _ b _ h; exact Subtype.ext (congrArg (fun x => x.1) h)
    · intro x hx
      have hx' := (Finset.mem_filter.mp hx).2
      exact ⟨⟨x.1, x.2.1, x.2.2, hx'⟩, Finset.mem_univ _, rfl⟩
    · intro _ _; rfl

private lemma G1_poly_zero : G1_poly 0 = 0 := by
  simp [G1_poly, G_poly_zero, G0_poly]

private lemma C_seq_succ (a : ℕ) :
    C_seq (a + 1) = ∑ i ∈ Finset.range (a + 1), Polynomial.X * C_seq i * C_seq (a - i) := by
  simp only [C_seq, C_nat_succ, Nat.cast_sum, Nat.cast_mul, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hia : i ≤ a := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [map_mul]
  have hpow : (Polynomial.X : Polynomial ℚ) ^ (a + 1) =
      Polynomial.X * Polynomial.X ^ i * Polynomial.X ^ (a - i) := by
    rw [mul_assoc, ← pow_add, show i + (a - i) = a by omega, pow_succ']
  rw [hpow]; ring

private lemma H_poly_rec (m : ℕ) (hm : 1 ≤ m) :
    H_poly m =
      (∑ i ∈ Finset.range m, G1_poly (i + 1) * Polynomial.C (B_all (m - (i + 1)) : ℚ)) +
      (∑ i ∈ Finset.range m, Polynomial.X * C_seq i * H_poly (m - (i + 1))) := by
  -- Use first skew-indecomposable component decomposition of β ∈ ClassB_m \ Av_m(132)
  let S1 := Σ i : Fin m,
    {α : Equiv.Perm (Fin (i.1 + 1)) // InClassB α ∧ IsSkewIndec α ∧ ¬ Avoids132 α} ×
    {γ : Equiv.Perm (Fin (m - (i.1 + 1))) // InClassB γ}
  let S2 := Σ i : Fin m,
    {α : Equiv.Perm (Fin (i.1 + 1)) // Avoids132 α ∧ IsSkewIndec α} ×
    {γ : Equiv.Perm (Fin (m - (i.1 + 1))) // InClassB γ ∧ ¬ Avoids132 γ}
  let toPermH : S1 ⊕ S2 → {β : Equiv.Perm (Fin m) // InClassB β ∧ ¬ Avoids132 β} := fun x =>
    match x with
    | Sum.inl ⟨i, ⟨α, hαB, _, hαna⟩, ⟨γ, hγB⟩⟩ =>
      ⟨skewSumCast (by omega : i.1 + 1 ≤ m) α γ,
       (inClassB_skewSumCast (by omega) α γ).mpr ⟨hαB, hγB⟩,
       (prefB_skewSumCast_not_avoids132_left (by omega) hαna γ).1⟩
    | Sum.inr ⟨i, ⟨α, hα132, _⟩, ⟨γ, hγB, hγna⟩⟩ =>
      ⟨skewSumCast (by omega : i.1 + 1 ≤ m) α γ,
       (inClassB_skewSumCast (by omega) α γ).mpr ⟨avoids132_imp_inClassB hα132, hγB⟩,
       (prefB_skewSumCast_avoids132_left (by omega) hα132 hγna).1⟩
  have hbij : Function.Bijective toPermH := by
    constructor
    · have hinj_core : ∀ (i1 i2 : Fin m)
          (α1 : Equiv.Perm (Fin (i1.1 + 1))) (hα1I : IsSkewIndec α1) (γ1 : Equiv.Perm (Fin (m - (i1.1 + 1))))
          (α2 : Equiv.Perm (Fin (i2.1 + 1))) (hα2I : IsSkewIndec α2) (γ2 : Equiv.Perm (Fin (m - (i2.1 + 1)))),
          skewSumCast (by omega : i1.1 + 1 ≤ m) α1 γ1 = skewSumCast (by omega : i2.1 + 1 ≤ m) α2 γ2 →
          i1 = i2 := by
        intro i1 i2 α1 hα1I γ1 α2 hα2I γ2 hpeq
        by_contra hne
        rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
        · have hcut : IsCut (skewSumCast (by omega : i2.1 + 1 ≤ m) α2 γ2) (i1.1 + 1) := by
            rw [← hpeq]; exact isCut_skewSumCast _ α1 γ1
          rw [isCut_skewSumCast_lt _ (by omega : i1.1 + 1 < i2.1 + 1)] at hcut
          exact hα2I.2 (i1.1 + 1) (by omega) (by omega) hcut
        · have hcut : IsCut (skewSumCast (by omega : i1.1 + 1 ≤ m) α1 γ1) (i2.1 + 1) := by
            rw [hpeq]; exact isCut_skewSumCast _ α2 γ2
          rw [isCut_skewSumCast_lt _ (by omega : i2.1 + 1 < i1.1 + 1)] at hcut
          exact hα1I.2 (i2.1 + 1) (by omega) (by omega) hcut
      rintro (⟨i1, ⟨α1, hα1B, hα1I, hα1na⟩, ⟨γ1, hγ1B⟩⟩ | ⟨i1, ⟨α1, hα1132, hα1I⟩, ⟨γ1, hγ1B, hγ1na⟩⟩)
             (⟨i2, ⟨α2, hα2B, hα2I, hα2na⟩, ⟨γ2, hγ2B⟩⟩ | ⟨i2, ⟨α2, hα2132, hα2I⟩, ⟨γ2, hγ2B, hγ2na⟩⟩) heq
      · have hpeq := congrArg Subtype.val heq
        have hi := hinj_core i1 i2 α1 hα1I γ1 α2 hα2I γ2 hpeq
        subst hi
        rcases Prod.mk.inj (@skewSumCast_inj m (i1.1 + 1) (by omega) (α1, γ1) (α2, γ2) hpeq) with ⟨rfl, rfl⟩
        rfl
      · exfalso
        have hpeq := congrArg Subtype.val heq
        have hi := hinj_core i1 i2 α1 hα1I γ1 α2 hα2I γ2 hpeq
        subst hi
        rcases Prod.mk.inj (@skewSumCast_inj m (i1.1 + 1) (by omega) (α1, γ1) (α2, γ2) hpeq) with ⟨rfl, rfl⟩
        exact hα1na hα2132
      · exfalso
        have hpeq := congrArg Subtype.val heq
        have hi := hinj_core i1 i2 α1 hα1I γ1 α2 hα2I γ2 hpeq
        subst hi
        rcases Prod.mk.inj (@skewSumCast_inj m (i1.1 + 1) (by omega) (α1, γ1) (α2, γ2) hpeq) with ⟨rfl, rfl⟩
        exact hα2na hα1132
      · have hpeq := congrArg Subtype.val heq
        have hi := hinj_core i1 i2 α1 hα1I γ1 α2 hα2I γ2 hpeq
        subst hi
        rcases Prod.mk.inj (@skewSumCast_inj m (i1.1 + 1) (by omega) (α1, γ1) (α2, γ2) hpeq) with ⟨rfl, rfl⟩
        rfl
    · rintro ⟨β, hβB, hβna⟩
      let cuts : Finset (Fin m) := Finset.univ.filter (fun i : Fin m => IsCut β (i.1 + 1))
      have hne : cuts.Nonempty := ⟨⟨m - 1, by omega⟩, by
        simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [show m - 1 + 1 = m by omega]; exact isCut_self β⟩
      let i := cuts.min' hne
      have hi_cut : IsCut β (i.1 + 1) := (Finset.mem_filter.mp (Finset.min'_mem cuts hne)).2
      rcases exists_skewSumCast_of_isCut hi_cut with ⟨α, γ, hβeq⟩
      rcases (inClassB_skewSumCast hi_cut.1 α γ).mp (hβeq ▸ hβB) with ⟨hαB, hγB⟩
      have hαI : IsSkewIndec α := by
        refine ⟨by omega, fun r hr0 hri hcutr => ?_⟩
        have hcutβ : IsCut β r := by
          rw [hβeq]; exact (isCut_skewSumCast_lt hi_cut.1 hri α γ).mpr hcutr
        have hmem : (⟨r - 1, by omega⟩ : Fin m) ∈ cuts := by
          simp only [cuts, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [show r - 1 + 1 = r by omega]; exact hcutβ
        have hle := Finset.min'_le cuts _ hmem
        have : i.1 ≤ r - 1 := hle
        omega
      by_cases hα132 : Avoids132 α
      · have hγna : ¬ Avoids132 γ := fun hγ132 =>
          hβna (hβeq ▸ (avoids132_skewSumCast hi_cut.1 α γ).mpr ⟨hα132, hγ132⟩)
        exact ⟨Sum.inr ⟨i, ⟨α, hα132, hαI⟩, ⟨γ, hγB, hγna⟩⟩, Subtype.ext hβeq.symm⟩
      · exact ⟨Sum.inl ⟨i, ⟨α, hαB, hαI, hα132⟩, ⟨γ, hγB⟩⟩, Subtype.ext hβeq.symm⟩
  unfold H_poly
  rw [← Equiv.sum_comp (Equiv.ofBijective toPermH hbij), Fintype.sum_sum_type]
  simp only [Equiv.ofBijective_apply]
  congr 1
  · dsimp only [S1]
    rw [Fintype.sum_sigma]
    have h1 :
        (∑ i : Fin m, ∑ p : {α : Equiv.Perm (Fin (i.1 + 1)) // InClassB α ∧ IsSkewIndec α ∧ ¬ Avoids132 α} ×
            {γ : Equiv.Perm (Fin (m - (i.1 + 1))) // InClassB γ},
          (Polynomial.X : Polynomial ℚ) ^ (prefB (toPermH (Sum.inl ⟨i, p⟩)).1 - 1)) =
        ∑ i : Fin m, G1_poly (i.1 + 1) * Polynomial.C (B_all (m - (i.1 + 1)) : ℚ) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
      have hinner :
          (∑ α : {α : Equiv.Perm (Fin (i.1 + 1)) // InClassB α ∧ IsSkewIndec α ∧ ¬ Avoids132 α},
            ∑ γ : {γ : Equiv.Perm (Fin (m - (i.1 + 1))) // InClassB γ},
              (Polynomial.X : Polynomial ℚ) ^ (prefB (toPermH (Sum.inl ⟨i, α, γ⟩)).1 - 1)) =
          ∑ α : {α : Equiv.Perm (Fin (i.1 + 1)) // InClassB α ∧ IsSkewIndec α ∧ ¬ Avoids132 α},
            (Polynomial.X : Polynomial ℚ) ^ (dB α.1 - 2) * Polynomial.C (B_all (m - (i.1 + 1)) : ℚ) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rcases α with ⟨α, hαB, hαI, hαna⟩
        have hconst : ∀ γ : {γ : Equiv.Perm (Fin (m - (i.1 + 1))) // InClassB γ},
            (Polynomial.X : Polynomial ℚ) ^ (prefB (toPermH (Sum.inl ⟨i, ⟨α, hαB, hαI, hαna⟩, γ⟩)).1 - 1) =
            (Polynomial.X : Polynomial ℚ) ^ (dB α - 2) := by
          rintro ⟨γ, hγB⟩
          dsimp only [toPermH]
          rw [(prefB_skewSumCast_not_avoids132_left (by omega) hαna γ).2,
              (activeB_indec_not_avoids132 hαB hαI hαna).2]
          rfl
        simp_rw [hconst]
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        change (B_all (m - (i.1 + 1)) : Polynomial ℚ) * _ = _
        have hC : (B_all (m - (i.1 + 1)) : Polynomial ℚ) = Polynomial.C (B_all (m - (i.1 + 1)) : ℚ) := by simp
        rw [hC, mul_comm]
      rw [hinner, ← Finset.sum_mul, G1_poly_eq_sum]
    rw [h1]
    exact Fin.sum_univ_eq_sum_range (fun i => G1_poly (i + 1) * Polynomial.C (B_all (m - (i + 1)) : ℚ)) m
  · dsimp only [S2]
    rw [Fintype.sum_sigma]
    have h2 :
        (∑ i : Fin m, ∑ p : {α : Equiv.Perm (Fin (i.1 + 1)) // Avoids132 α ∧ IsSkewIndec α} ×
            {γ : Equiv.Perm (Fin (m - (i.1 + 1))) // InClassB γ ∧ ¬ Avoids132 γ},
          (Polynomial.X : Polynomial ℚ) ^ (prefB (toPermH (Sum.inr ⟨i, p⟩)).1 - 1)) =
        ∑ i : Fin m, Polynomial.X * C_seq i.1 * H_poly (m - (i.1 + 1)) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fintype.sum_prod_type]
      have hinner :
          (∑ α : {α : Equiv.Perm (Fin (i.1 + 1)) // Avoids132 α ∧ IsSkewIndec α},
            ∑ γ : {γ : Equiv.Perm (Fin (m - (i.1 + 1))) // InClassB γ ∧ ¬ Avoids132 γ},
              (Polynomial.X : Polynomial ℚ) ^ (prefB (toPermH (Sum.inr ⟨i, α, γ⟩)).1 - 1)) =
          ∑ _α : {α : Equiv.Perm (Fin (i.1 + 1)) // Avoids132 α ∧ IsSkewIndec α},
            (Polynomial.X : Polynomial ℚ) ^ (i.1 + 1) * H_poly (m - (i.1 + 1)) := by
        refine Finset.sum_congr rfl fun α _ => ?_
        rcases α with ⟨α, hα132, hαI⟩
        unfold H_poly
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rcases γ with ⟨γ, hγB, hγna⟩
        dsimp only [toPermH]
        rw [(prefB_skewSumCast_avoids132_left (by omega) hα132 hγna).2]
        have hb := prefB_bounds_of_not_avoids132 hγna
        rw [← pow_add]
        congr 1; omega
      rw [hinner, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          card_avoids132_indec (i.1 + 1) (by omega), Nat.add_sub_cancel]
      have hC : (C_nat i.1 : Polynomial ℚ) = Polynomial.C (C_nat i.1 : ℚ) := by simp
      rw [hC, C_seq, pow_succ']
      ring
    rw [h2]
    exact Fin.sum_univ_eq_sum_range (fun i => Polynomial.X * C_seq i * H_poly (m - (i + 1))) m

private lemma sum_conv_C_seq_aux (H W : ℕ → Polynomial ℚ)
    (h0 : H 0 = 0) (hW0 : W 0 = 0)
    (hrec : ∀ m : ℕ, H (m + 1) =
      W (m + 1) + ∑ i ∈ Finset.range (m + 1), Polynomial.X * C_seq i * H (m - i)) :
    ∀ m : ℕ, H m = ∑ a ∈ Finset.range (m + 1), C_seq a * W (m - a) := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    cases m with
    | zero =>
      rw [h0, Nat.zero_add, Finset.sum_range_one, Nat.sub_zero, hW0, mul_zero]
    | succ m =>
      rw [hrec m]
      have hsecond :
          (∑ i ∈ Finset.range (m + 1), Polynomial.X * C_seq i * H (m - i)) =
          ∑ s ∈ Finset.range (m + 1), C_seq (s + 1) * W (m - s) := by
        have hsub : ∀ i ∈ Finset.range (m + 1),
            Polynomial.X * C_seq i * H (m - i) =
            ∑ a ∈ Finset.range (m - i + 1), (Polynomial.X * C_seq i * C_seq a) * W (m - i - a) := by
          intro i hi
          have him : i < m + 1 := Finset.mem_range.mp hi
          rw [ih (m - i) (by omega), Finset.mul_sum]
          refine Finset.sum_congr rfl fun a _ => by ring
        rw [Finset.sum_congr rfl hsub]
        have hswap :
            (∑ i ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (m - i + 1),
              (Polynomial.X * C_seq i * C_seq a) * W (m - i - a)) =
            ∑ s ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (s + 1),
              (Polynomial.X * C_seq i * C_seq (s - i)) * W (m - s) := by
          have hlhs :
              (∑ i ∈ Finset.range (m + 1), ∑ a ∈ Finset.range (m - i + 1),
                (Polynomial.X * C_seq i * C_seq a) * W (m - i - a)) =
              ∑ p ∈ (Finset.range (m + 1)).sigma (fun i => Finset.range (m - i + 1)),
                (Polynomial.X * C_seq p.1 * C_seq p.2) * W (m - p.1 - p.2) := by
            simp only [Finset.sum_sigma']
          have hrhs :
              (∑ s ∈ Finset.range (m + 1), ∑ i ∈ Finset.range (s + 1),
                (Polynomial.X * C_seq i * C_seq (s - i)) * W (m - s)) =
              ∑ q ∈ (Finset.range (m + 1)).sigma (fun s => Finset.range (s + 1)),
                (Polynomial.X * C_seq q.2 * C_seq (q.1 - q.2)) * W (m - q.1) := by
            simp only [Finset.sum_sigma']
          rw [hlhs, hrhs]
          refine Finset.sum_bij (fun p _ => (⟨p.1 + p.2, p.1⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
          · intro p hp
            simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢; omega
          · intro p1 _ p2 _ h
            have h1 : p1.1 + p1.2 = p2.1 + p2.2 := congrArg (fun x : Σ _ : ℕ, ℕ => x.1) h
            have h2 : p1.1 = p2.1 := congrArg (fun x : Σ _ : ℕ, ℕ => x.2) h
            rcases p1 with ⟨a1, b1⟩; rcases p2 with ⟨a2, b2⟩
            dsimp at h1 h2; subst h2
            have hb : b1 = b2 := by omega
            subst hb; rfl
          · intro q hq
            rcases q with ⟨s, i⟩
            simp only [Finset.mem_sigma, Finset.mem_range] at hq
            refine ⟨⟨i, s - i⟩, ?_, ?_⟩
            · simp only [Finset.mem_sigma, Finset.mem_range]; omega
            · dsimp
              have : i + (s - i) = s := by omega
              rw [this]
          · intro p hp
            simp only [Finset.mem_sigma, Finset.mem_range] at hp
            have h1 : p.1 + p.2 - p.1 = p.2 := by omega
            have h2 : m - (p.1 + p.2) = m - p.1 - p.2 := by omega
            rw [h1, h2]
        rw [hswap]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_mul, C_seq_succ]
      rw [hsecond]
      have hC0 : C_seq 0 = 1 := by simp [C_seq, C_nat_zero]
      have hrhs :
          (∑ a ∈ Finset.range (m + 1 + 1), C_seq a * W (m + 1 - a)) =
          (∑ s ∈ Finset.range (m + 1), C_seq (s + 1) * W (m - s)) + W (m + 1) := by
        rw [Finset.sum_range_succ', Nat.sub_zero, hC0, one_mul]
        congr 1
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [show m + 1 - (s + 1) = m - s by omega]
      rw [hrhs, add_comm]

private lemma H_poly_eq (m : ℕ) :
    H_poly m = ∑ a ∈ Finset.range (m + 1), C_seq a *
      ∑ b ∈ Finset.range (m - a + 1), G1_poly b * Polynomial.C (B_all (m - a - b) : ℚ) := by
  refine sum_conv_C_seq_aux H_poly
    (fun r => ∑ b ∈ Finset.range (r + 1), G1_poly b * Polynomial.C (B_all (r - b) : ℚ)) ?_ ?_ ?_ m
  · unfold H_poly
    have hempty : IsEmpty {β : Equiv.Perm (Fin 0) // InClassB β ∧ ¬ Avoids132 β} :=
      ⟨fun ⟨_, _, hna⟩ => hna (fun i => Fin.elim0 i)⟩
    exact Finset.sum_eq_zero (fun x _ => IsEmpty.elim hempty x)
  · rw [Nat.zero_add, Finset.sum_range_one, G1_poly_zero, zero_mul]
  · intro r
    rw [H_poly_rec (r + 1) (by omega)]
    refine congrArg₂ (· + ·) ?_ ?_
    · symm
      rw [Finset.sum_range_succ', G1_poly_zero, zero_mul, add_zero]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [show r + 1 - (i + 1) = r - i by omega]

private noncomputable def classBDecompEquiv (k : ℕ) (hk : 1 ≤ k) :
    (Σ m : Fin k,
      {β : Equiv.Perm (Fin m.1) // InClassB β} ×
      Σ α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α},
        {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j ∈ activeB α.1}) ≃
    {π : Equiv.Perm (Fin (k + 1)) // InClassB π ∧ IsSkewIndec π} := by
  let S := Σ m : Fin k,
    {β : Equiv.Perm (Fin m.1) // InClassB β} ×
    Σ α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α},
      {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j ∈ activeB α.1}
  let toPermB : S → {π : Equiv.Perm (Fin (k + 1)) // InClassB π ∧ IsSkewIndec π} := fun x =>
    let m := x.1
    let β := x.2.1
    let α := x.2.2.1
    let j := x.2.2.2
    let σ : Equiv.Perm (Fin k) := skewSumCast (le_of_lt m.2) β.1 α.1
    let pos : Fin (k + 1) := ⟨m.1 + j.1.1, by have := j.1.2; omega⟩
    have hσB : InClassB σ := (inClassB_skewSumCast (le_of_lt m.2) β.1 α.1).mpr ⟨β.2, α.2.1⟩
    have hnfα : ¬ ForbB α.1 j.1 :=
      ((insMax_inClassB_iff α.1 j.1).mp (Finset.mem_filter.mp j.2.2).2).2
    have hnfσ : ¬ ForbB σ pos := by
      rw [forbB_skewSumCast_ge (le_of_lt m.2) β.1 α.1 pos (by dsimp [pos]; omega)]
      have heq : (⟨pos.1 - m.1, by omega⟩ : Fin (k - m.1 + 1)) = j.1 := by ext; simp [pos]
      rw [heq]; exact hnfα
    have hτB : InClassB (insMax σ pos) := (insMax_inClassB_iff σ pos).mpr ⟨hσB, hnfσ⟩
    have hτI : IsSkewIndec (insMax σ pos) :=
      (isSkewIndec_insMax_skewSumCast m.2 β.1 α.1 α.2.2 pos).mpr (by dsimp [pos]; have := j.2.1; omega)
    ⟨insMax σ pos, hτB, hτI⟩
  refine Equiv.ofBijective toPermB ?_
  constructor
  · rintro ⟨m1, ⟨β1, hβ1⟩, ⟨α1, hα1B, hα1I⟩, ⟨j1, hj11, hj1a⟩⟩
           ⟨m2, ⟨β2, hβ2⟩, ⟨α2, hα2B, hα2I⟩, ⟨j2, hj21, hj2a⟩⟩ heq
    have hpeq : insMax (skewSumCast (le_of_lt m1.2) β1 α1) ⟨m1.1 + j1.1, by have := j1.2; omega⟩ =
        insMax (skewSumCast (le_of_lt m2.2) β2 α2) ⟨m2.1 + j2.1, by have := j2.2; omega⟩ :=
      congrArg Subtype.val heq
    have h1 := (insMax_bijective k).1
      (a₁ := (skewSumCast (le_of_lt m1.2) β1 α1, ⟨m1.1 + j1.1, by have := j1.2; omega⟩))
      (a₂ := (skewSumCast (le_of_lt m2.2) β2 α2, ⟨m2.1 + j2.1, by have := j2.2; omega⟩)) hpeq
    rcases Prod.mk.inj h1 with ⟨hsk, hpos⟩
    have hdec : (⟨m1, β1, ⟨α1, hα1I⟩⟩ :
        Σ m : Fin k, Equiv.Perm (Fin m.1) × {α : Equiv.Perm (Fin (k - m.1)) // IsSkewIndec α}) =
        ⟨m2, β2, ⟨α2, hα2I⟩⟩ :=
      (skewDecompLastEquiv k hk).symm.injective (by
        rw [skewDecompLastEquiv_symm_apply, skewDecompLastEquiv_symm_apply]; exact hsk)
    cases hdec
    have hj : j1 = j2 := by
      ext; have := congrArg Fin.val hpos; dsimp at this; omega
    subst hj
    rfl
  · rintro ⟨π, hπB, hπI⟩
    rcases (insMax_bijective k).2 π with ⟨⟨σ, pos⟩, hπeq⟩
    dsimp only at hπeq
    let d := skewDecompLastEquiv k hk σ
    have hσeq : skewSumCast (le_of_lt d.1.2) d.2.1 d.2.2.1 = σ := by
      rw [← skewDecompLastEquiv_symm_apply k hk d]
      exact (skewDecompLastEquiv k hk).symm_apply_apply σ
    rw [← hπeq, ← hσeq] at hπB hπI
    have hmp : d.1.1 < pos.1 :=
      (isSkewIndec_insMax_skewSumCast d.1.2 d.2.1 d.2.2.1 d.2.2.2 pos).mp hπI
    rcases (insMax_inClassB_iff _ pos).mp hπB with ⟨hσB, hnf⟩
    rcases (inClassB_skewSumCast (le_of_lt d.1.2) d.2.1 d.2.2.1).mp hσB with ⟨hβB, hαB⟩
    have hnfα : ¬ ForbB d.2.2.1 ⟨pos.1 - d.1.1, by omega⟩ := by
      rw [← forbB_skewSumCast_ge (le_of_lt d.1.2) d.2.1 d.2.2.1 pos (by omega)]
      exact hnf
    have hj_mem : (⟨pos.1 - d.1.1, by omega⟩ : Fin (k - d.1.1 + 1)) ∈ activeB d.2.2.1 := by
      simp only [activeB, Finset.mem_filter, Finset.mem_univ, true_and, insMax_inClassB_iff]
      exact ⟨hαB, hnfα⟩
    refine ⟨⟨d.1, ⟨d.2.1, hβB⟩, ⟨d.2.2.1, hαB, d.2.2.2⟩,
      ⟨⟨pos.1 - d.1.1, by omega⟩, by dsimp; omega, hj_mem⟩⟩, Subtype.ext ?_⟩
    dsimp only [toPermB]
    have hposeq : (⟨d.1.1 + (pos.1 - d.1.1), by omega⟩ : Fin (k + 1)) = pos := by
      ext; dsimp; omega
    rw [hposeq, hσeq, hπeq]

private lemma classBDecompEquiv_val (k : ℕ) (hk : 1 ≤ k)
    (m : Fin k) (β : {β : Equiv.Perm (Fin m.1) // InClassB β})
    (α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α})
    (j : {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j ∈ activeB α.1}) :
    (classBDecompEquiv k hk ⟨m, β, α, j⟩).1 =
      insMax (skewSumCast (le_of_lt m.2) β.1 α.1) ⟨m.1 + j.1.1, by have := j.1.2; omega⟩ :=
  rfl

private lemma B_ind_rec (r : ℕ) (hr : 2 ≤ r) :
    B_ind r = ∑ c ∈ Finset.range (r - 1), B_all c * S_nat (r - 1 - c) := by
  cases r with
  | zero => omega
  | succ k =>
    have hk : 1 ≤ k := by omega
    simp only [Nat.add_sub_cancel]
    unfold B_ind
    rw [← Fintype.card_congr (classBDecompEquiv k hk)]
    simp only [Fintype.card_sigma, Fintype.card_prod]
    rw [Fin.sum_univ_eq_sum_range (fun c =>
      Fintype.card {β : Equiv.Perm (Fin c) // InClassB β} *
        ∑ α : {α : Equiv.Perm (Fin (k - c)) // InClassB α ∧ IsSkewIndec α},
          Fintype.card {j : Fin (k - c + 1) // 1 ≤ j.1 ∧ j ∈ activeB α.1}) k]
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold B_all S_nat
    congr 1
    refine Finset.sum_congr rfl fun α _ => card_activeB_pos α.2.1

private lemma sum_H_S_add_G1 (k : ℕ) (hk : 1 ≤ k) :
    (∑ m ∈ Finset.range k, H_poly m * Polynomial.C (S_nat (k - m) : ℚ)) +
    (∑ m ∈ Finset.range k, C_seq m * G1_poly (k - m)) =
    ∑ a ∈ Finset.range (k + 2), C_seq a *
      ∑ b ∈ Finset.range (k + 1 - a + 1), G1_poly b * Polynomial.C ((G_poly (k + 1 - a - b)).eval 1) := by
  have h1 :
      (∑ m ∈ Finset.range k, H_poly m * Polynomial.C (S_nat (k - m) : ℚ)) =
      ∑ a ∈ Finset.range k, C_seq a *
        ∑ b ∈ Finset.range (k - a), G1_poly b * Polynomial.C ((G_poly (k + 1 - a - b)).eval 1) := by
    have hstep1 :
        (∑ m ∈ Finset.range k, H_poly m * Polynomial.C (S_nat (k - m) : ℚ)) =
        ∑ m ∈ Finset.range k, ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m - a + 1),
          C_seq a * G1_poly b * Polynomial.C ((B_all (m - a - b) : ℚ) * (S_nat (k - m) : ℚ)) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [H_poly_eq m, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [map_mul]; ring
    have hstep2 :
        (∑ m ∈ Finset.range k, ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m - a + 1),
          C_seq a * G1_poly b * Polynomial.C ((B_all (m - a - b) : ℚ) * (S_nat (k - m) : ℚ))) =
        ∑ a ∈ Finset.range k, ∑ b ∈ Finset.range (k - a), ∑ c ∈ Finset.range (k - a - b),
          C_seq a * G1_poly b * Polynomial.C ((B_all c : ℚ) * (S_nat (k - a - b - c) : ℚ)) := by
      have hlhs :
          (∑ m ∈ Finset.range k, ∑ a ∈ Finset.range (m + 1), ∑ b ∈ Finset.range (m - a + 1),
            C_seq a * G1_poly b * Polynomial.C ((B_all (m - a - b) : ℚ) * (S_nat (k - m) : ℚ))) =
          ∑ p ∈ ((Finset.range k).sigma fun m =>
              (Finset.range (m + 1)).sigma fun a => Finset.range (m - a + 1)),
            C_seq p.2.1 * G1_poly p.2.2 *
              Polynomial.C ((B_all (p.1 - p.2.1 - p.2.2) : ℚ) * (S_nat (k - p.1) : ℚ)) := by
        simp only [Finset.sum_sigma']
      have hrhs :
          (∑ a ∈ Finset.range k, ∑ b ∈ Finset.range (k - a), ∑ c ∈ Finset.range (k - a - b),
            C_seq a * G1_poly b * Polynomial.C ((B_all c : ℚ) * (S_nat (k - a - b - c) : ℚ))) =
          ∑ q ∈ ((Finset.range k).sigma fun a =>
              (Finset.range (k - a)).sigma fun b => Finset.range (k - a - b)),
            C_seq q.1 * G1_poly q.2.1 *
              Polynomial.C ((B_all q.2.2 : ℚ) * (S_nat (k - q.1 - q.2.1 - q.2.2) : ℚ)) := by
        simp only [Finset.sum_sigma']
      rw [hlhs, hrhs]
      refine Finset.sum_bij (fun p _ => (⟨p.2.1, ⟨p.2.2, p.1 - p.2.1 - p.2.2⟩⟩ : Σ _ : ℕ, Σ _ : ℕ, ℕ))
        ?_ ?_ ?_ ?_
      · intro p hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢; omega
      · intro p1 hp1 p2 hp2 h
        simp only [Finset.mem_sigma, Finset.mem_range] at hp1 hp2
        have ha : p1.2.1 = p2.2.1 := congrArg (fun x : Σ _ : ℕ, Σ _ : ℕ, ℕ => x.1) h
        have h2 : p1.2.2 = p2.2.2 := congrArg (fun x : Σ _ : ℕ, Σ _ : ℕ, ℕ => x.2.1) h
        have h3 : p1.1 - p1.2.1 - p1.2.2 = p2.1 - p2.2.1 - p2.2.2 :=
          congrArg (fun x : Σ _ : ℕ, Σ _ : ℕ, ℕ => x.2.2) h
        have hm : p1.1 = p2.1 := by omega
        rcases p1 with ⟨m1, a1, b1⟩; rcases p2 with ⟨m2, a2, b2⟩
        dsimp at hm ha h2; subst hm; subst ha; subst h2; rfl
      · intro q hq
        simp only [Finset.mem_sigma, Finset.mem_range] at hq
        refine ⟨⟨q.1 + q.2.1 + q.2.2, ⟨q.1, q.2.1⟩⟩, ?_, ?_⟩
        · simp only [Finset.mem_sigma, Finset.mem_range]; omega
        · rcases q with ⟨a, b, c⟩
          dsimp
          have : a + b + c - a - b = c := by omega
          rw [this]
      · intro p hp
        simp only [Finset.mem_sigma, Finset.mem_range] at hp
        have : k - p.2.1 - p.2.2 - (p.1 - p.2.1 - p.2.2) = k - p.1 := by omega
        rw [this]
    rw [hstep1, hstep2]
    refine Finset.sum_congr rfl fun a ha => ?_
    have hak : a < k := Finset.mem_range.mp ha
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    have hbk : b < k - a := Finset.mem_range.mp hb
    rw [← Finset.mul_sum, ← map_sum, G_poly_eval_one, B_ind_rec (k + 1 - a - b) (by omega)]
    have hr1 : k + 1 - a - b - 1 = k - a - b := by omega
    rw [hr1, Nat.cast_sum]
    simp only [Nat.cast_mul, mul_assoc]
  rw [h1]
  -- Now compare LHS with RHS by peeling off the top 2 terms of `a` (k and k+1) and `b` (k-a and k+1-a)
  rw [Finset.sum_range_succ (n := k + 1), Finset.sum_range_succ (n := k)]
  have ha_top1 : C_seq (k + 1) *
      ∑ b ∈ Finset.range (k + 1 - (k + 1) + 1),
        G1_poly b * Polynomial.C ((G_poly (k + 1 - (k + 1) - b)).eval 1) = 0 := by
    simp [G1_poly_zero]
  have ha_top2 : C_seq k *
      ∑ b ∈ Finset.range (k + 1 - k + 1),
        G1_poly b * Polynomial.C ((G_poly (k + 1 - k - b)).eval 1) = 0 := by
    have h1' : k + 1 - k + 1 = 2 := by omega
    rw [h1', Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [G1_poly_zero, G_poly_zero]
  rw [ha_top1, ha_top2, add_zero, add_zero, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hak : a < k := Finset.mem_range.mp ha
  have hr2 : k + 1 - a + 1 = (k - a) + 2 := by omega
  rw [hr2, Finset.sum_range_succ (n := k - a + 1), Finset.sum_range_succ (n := k - a)]
  have hb_top1 : G1_poly (k - a + 1) * Polynomial.C ((G_poly (k + 1 - a - (k - a + 1))).eval 1) = 0 := by
    have : k + 1 - a - (k - a + 1) = 0 := by omega
    rw [this, G_poly_zero]; simp
  have hb_top2 : G1_poly (k - a) * Polynomial.C ((G_poly (k + 1 - a - (k - a))).eval 1) = G1_poly (k - a) := by
    have : k + 1 - a - (k - a) = 1 := by omega
    rw [this, G_poly_one]; simp
  rw [hb_top1, hb_top2, add_zero, mul_add]

private lemma G_poly_rec (n : ℕ) (hn : 2 ≤ n) :
    let G0 : ℕ → Polynomial ℚ := fun k => if k = 0 then 0 else C_seq (k - 1)
    let G1 : ℕ → Polynomial ℚ := fun k => G_poly k - G0 k
    (1 - Polynomial.X) * G_poly n =
      (1 - Polynomial.X) *
        (∑ m ∈ Finset.range (n + 1), C_seq m *
          ∑ n1 ∈ Finset.range (n - m + 1), G1 n1 * Polynomial.C ((G_poly (n - m - n1)).eval 1)) +
      (∑ m ∈ Finset.range (n - 1), C_seq m *
        (Polynomial.X * Polynomial.C ((G_poly (n - 1 - m)).eval 1) -
          Polynomial.X * G_poly (n - 1 - m))) +
      (1 - Polynomial.X) *
        (∑ m ∈ Finset.range (n - 1), C_seq m * (Polynomial.X * G0 (n - 1 - m))) := by
  dsimp only
  cases n with
  | zero => omega
  | succ k =>
    have hk : 1 ≤ k := by omega
    simp only [Nat.add_sub_cancel]
    have hG_decomp :
        G_poly (k + 1) =
          (∑ m ∈ Finset.range k, H_poly m * Polynomial.C (S_nat (k - m) : ℚ)) +
          (∑ m ∈ Finset.range k,
            ∑ _β : {β : Equiv.Perm (Fin m) // Avoids132 β},
              ∑ α : {α : Equiv.Perm (Fin (k - m)) // InClassB α ∧ IsSkewIndec α},
                ∑ j : {j : Fin (k - m + 1) // 1 ≤ j.1 ∧ j.1 < dB α.1 - 1},
                  (Polynomial.X : Polynomial ℚ) ^ (m + j.1.1)) +
          (∑ m ∈ Finset.range k, C_seq m * (Polynomial.X * G0_poly (k - m))) +
          (∑ m ∈ Finset.range k, C_seq m * G1_poly (k - m)) := by
      unfold G_poly
      rw [← Equiv.sum_comp (classBDecompEquiv k hk), Fintype.sum_sigma]
      have hper_m : ∀ m : Fin k,
          (∑ p : {β : Equiv.Perm (Fin m.1) // InClassB β} ×
              Σ α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α},
                {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j ∈ activeB α.1},
            (Polynomial.X : Polynomial ℚ) ^ (dB (classBDecompEquiv k hk ⟨m, p⟩).1 - 2)) =
          H_poly m.1 * Polynomial.C (S_nat (k - m.1) : ℚ) +
          (∑ _β : {β : Equiv.Perm (Fin m.1) // Avoids132 β},
            ∑ α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α},
              ∑ j : {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j.1 < dB α.1 - 1},
                (Polynomial.X : Polynomial ℚ) ^ (m.1 + j.1.1)) +
          C_seq m.1 * (Polynomial.X * G0_poly (k - m.1)) +
          C_seq m.1 * G1_poly (k - m.1) := by
        intro m
        rw [Fintype.sum_prod_type]
        let Pβ := fun β : {β : Equiv.Perm (Fin m.1) // InClassB β} => Avoids132 β.1
        rw [← Finset.sum_filter_add_sum_filter_not Finset.univ Pβ, add_comm]
        have hpart_not :
            (∑ β ∈ Finset.univ.filter (fun β : {β : Equiv.Perm (Fin m.1) // InClassB β} => ¬ Pβ β),
              ∑ q : Σ α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α},
                  {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j ∈ activeB α.1},
                (Polynomial.X : Polynomial ℚ) ^ (dB (classBDecompEquiv k hk ⟨m, β, q⟩).1 - 2)) =
            H_poly m.1 * Polynomial.C (S_nat (k - m.1) : ℚ) := by
          unfold H_poly
          rw [Finset.sum_mul]
          refine Finset.sum_bij (fun β hβ => (⟨β.1, β.2, (Finset.mem_filter.mp hβ).2⟩ :
              {β : Equiv.Perm (Fin m.1) // InClassB β ∧ ¬ Avoids132 β}))
            (fun _ _ => Finset.mem_univ _)
            (fun b1 _ b2 _ h => Subtype.ext (congrArg (fun x => x.1) h))
            (fun β _ => ⟨⟨β.1, β.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, β.2.2⟩, rfl⟩)
            ?_
          · intro β hβ
            have hβna : ¬ Avoids132 β.1 := (Finset.mem_filter.mp hβ).2
            rw [Fintype.sum_sigma]
            have hconst : ∀ (α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α})
                (j : {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j ∈ activeB α.1}),
                (Polynomial.X : Polynomial ℚ) ^ (dB (classBDecompEquiv k hk ⟨m, β, α, j⟩).1 - 2) =
                (Polynomial.X : Polynomial ℚ) ^ (prefB β.1 - 1) := by
              intro α j
              have hτB := (classBDecompEquiv k hk ⟨m, β, α, j⟩).2.1
              have hτI := (classBDecompEquiv k hk ⟨m, β, α, j⟩).2.2
              rw [classBDecompEquiv_val] at hτB hτI ⊢
              have hpre_σ := prefB_skewSumCast_not_avoids132_left (le_of_lt m.2) hβna α.1
              have hb := prefB_bounds_of_not_avoids132 hβna
              have hpre_τ := prefB_insMax_of_prefB_le hpre_σ.1
                (pos := ⟨m.1 + j.1.1, by have := j.1.2; omega⟩) (by rw [hpre_σ.2]; dsimp; omega)
              rw [(activeB_indec_not_avoids132 hτB hτI hpre_τ.1).2, hpre_τ.2, hpre_σ.2]
              rfl
            simp_rw [hconst]
            simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            have hcard_j : ∀ α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α},
                Fintype.card {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j ∈ activeB α.1} = dB α.1 - 1 :=
              fun α => card_activeB_pos α.2.1
            simp_rw [hcard_j]
            rw [← Finset.sum_mul]
            have hS : (∑ α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α},
                ((dB α.1 - 1 : ℕ) : Polynomial ℚ)) = Polynomial.C (S_nat (k - m.1) : ℚ) := by
              unfold S_nat; simp
            rw [hS, mul_comm]
        have hpart_132 :
            (∑ β ∈ Finset.univ.filter Pβ,
              ∑ q : Σ α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α},
                  {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j ∈ activeB α.1},
                (Polynomial.X : Polynomial ℚ) ^ (dB (classBDecompEquiv k hk ⟨m, β, q⟩).1 - 2)) =
            (∑ _β : {β : Equiv.Perm (Fin m.1) // Avoids132 β},
              ∑ α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α},
                ∑ j : {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j.1 < dB α.1 - 1},
                  (Polynomial.X : Polynomial ℚ) ^ (m.1 + j.1.1)) +
            C_seq m.1 * (Polynomial.X * G0_poly (k - m.1)) +
            C_seq m.1 * G1_poly (k - m.1) := by
          have hreidx_β :
              (∑ β ∈ Finset.univ.filter Pβ,
                ∑ q : Σ α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α},
                    {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j ∈ activeB α.1},
                  (Polynomial.X : Polynomial ℚ) ^ (dB (classBDecompEquiv k hk ⟨m, β, q⟩).1 - 2)) =
              ∑ β : {β : Equiv.Perm (Fin m.1) // Avoids132 β},
                ((∑ α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α},
                    ∑ j : {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j.1 < dB α.1 - 1},
                      (Polynomial.X : Polynomial ℚ) ^ (m.1 + j.1.1)) +
                 ((Polynomial.X : Polynomial ℚ) ^ m.1 * (Polynomial.X * G0_poly (k - m.1)) +
                  (Polynomial.X : Polynomial ℚ) ^ m.1 * G1_poly (k - m.1))) := by
            refine Finset.sum_bij (fun β hβ => (⟨β.1, (Finset.mem_filter.mp hβ).2⟩ : {β : Equiv.Perm (Fin m.1) // Avoids132 β}))
              (fun _ _ => Finset.mem_univ _)
              (fun b1 _ b2 _ h => Subtype.ext (congrArg (fun x => x.1) h))
              (fun β _ => ⟨⟨β.1, avoids132_imp_inClassB β.2⟩,
                Finset.mem_filter.mpr ⟨Finset.mem_univ _, β.2⟩, rfl⟩)
              ?_
            intro β hβ
            have hβ132 : Avoids132 β.1 := (Finset.mem_filter.mp hβ).2
            rw [Fintype.sum_sigma]
            -- Split inner sum over j into j.1 < k - m.1 vs j.1 = k - m.1
            have hsplit_j : ∀ α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α},
                (∑ j : {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j ∈ activeB α.1},
                  (Polynomial.X : Polynomial ℚ) ^ (dB (classBDecompEquiv k hk ⟨m, β, α, j⟩).1 - 2)) =
                (∑ j : {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j.1 < dB α.1 - 1},
                  (Polynomial.X : Polynomial ℚ) ^ (m.1 + j.1.1)) +
                (if Avoids132 α.1 then (Polynomial.X : Polynomial ℚ) ^ (m.1 + 1) * Polynomial.X ^ (dB α.1 - 2)
                 else (Polynomial.X : Polynomial ℚ) ^ m.1 * Polynomial.X ^ (dB α.1 - 2)) := by
              intro α
              let lastJ : {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j ∈ activeB α.1} :=
                ⟨⟨k - m.1, Nat.lt_succ_self _⟩, by dsimp; omega, last_mem_activeB α.2.1⟩
              rw [← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ lastJ), add_comm]
              congr 1
              · refine Finset.sum_bij (fun j hj =>
                  (⟨j.1, j.2.1, (mem_activeB_lt_iff_indec α.2.1 α.2.2 (by
                    have hne : j ≠ lastJ := (Finset.mem_erase.mp hj).1
                    have hv : j.1.1 ≠ k - m.1 := fun heq => hne (Subtype.ext (Fin.ext heq))
                    have := j.1.2; omega)).mp j.2.2⟩ :
                    {j : Fin (k - m.1 + 1) // 1 ≤ j.1 ∧ j.1 < dB α.1 - 1}))
                  (fun _ _ => Finset.mem_univ _)
                  (fun j1 _ j2 _ h => Subtype.ext (congrArg (fun x => x.1) h))
                  ?_ ?_
                · intro j _
                  have hj_lt : j.1.1 < k - m.1 := by have := dB_le_succ α.1; have := j.2.2; omega
                  have hj_act : j.1 ∈ activeB α.1 :=
                    (mem_activeB_lt_iff_indec α.2.1 α.2.2 hj_lt).mpr j.2.2
                  refine ⟨⟨j.1, j.2.1, hj_act⟩, Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩
                  intro heq; have := congrArg (fun x => x.1.1) heq; dsimp [lastJ] at this; omega
                · intro j hj
                  have hne : j ≠ lastJ := (Finset.mem_erase.mp hj).1
                  have hv : j.1.1 ≠ k - m.1 := fun heq => hne (Subtype.ext (Fin.ext heq))
                  have hj_lt : j.1.1 < k - m.1 := by have := j.1.2; omega
                  have hτB := (classBDecompEquiv k hk ⟨m, β, α, j⟩).2.1
                  have hτI := (classBDecompEquiv k hk ⟨m, β, α, j⟩).2.2
                  rw [classBDecompEquiv_val] at hτB hτI ⊢
                  have hnfα : ¬ ForbB α.1 j.1 :=
                    ((insMax_inClassB_iff α.1 j.1).mp (Finset.mem_filter.mp j.2.2).2).2
                  have hcase2 := prefB_insMax_case2 m.2 hβ132 α.2.2
                    (pos := ⟨m.1 + j.1.1, by omega⟩) (by dsimp; have := j.2.1; omega)
                    (by dsimp; omega) (by
                      have heq : (⟨m.1 + j.1.1 - m.1, by omega⟩ : Fin (k - m.1 + 1)) = j.1 := by
                        ext; simp
                      rw [heq]; exact hnfα)
                  rw [(activeB_indec_not_avoids132 hτB hτI hcase2.1).2, hcase2.2]
                  rfl
              · have hτB := (classBDecompEquiv k hk ⟨m, β, α, lastJ⟩).2.1
                have hτI := (classBDecompEquiv k hk ⟨m, β, α, lastJ⟩).2.2
                rw [classBDecompEquiv_val] at hτB hτI ⊢
                have hpos_eq : (⟨m.1 + lastJ.1.1, by have := lastJ.1.2; omega⟩ : Fin (k + 1)) =
                    ⟨k, Nat.lt_succ_self k⟩ := by ext; dsimp [lastJ]; omega
                rw [hpos_eq] at hτB hτI ⊢
                by_cases hα132 : Avoids132 α.1
                · rw [if_pos hα132]
                  have hτ132 : Avoids132 (insMax (skewSumCast (le_of_lt m.2) β.1 α.1) ⟨k, Nat.lt_succ_self k⟩) :=
                    (avoids132_insMax_iff _ _).mpr
                      ⟨(avoids132_skewSumCast (le_of_lt m.2) β.1 α.1).mpr ⟨hβ132, hα132⟩, isCut_self _⟩
                  rw [(activeB_indec_avoids132 hτB hτ132).2, (activeB_indec_avoids132 α.2.1 hα132).2, ← pow_add]
                  congr 1; omega
                · rw [if_neg hα132]
                  have hpre_σ := prefB_skewSumCast_avoids132_left (le_of_lt m.2) hβ132 hα132
                  have hb := prefB_bounds_of_not_avoids132 hα132
                  have hpre_τ := prefB_insMax_of_prefB_le hpre_σ.1 (pos := ⟨k, Nat.lt_succ_self k⟩)
                    (by rw [hpre_σ.2]; dsimp; omega)
                  rw [(activeB_indec_not_avoids132 hτB hτI hpre_τ.1).2, hpre_τ.2, hpre_σ.2,
                      (activeB_indec_not_avoids132 α.2.1 α.2.2 hα132).2, ← pow_add]
                  congr 1; omega
            simp_rw [hsplit_j]
            rw [Finset.sum_add_distrib]
            congr 1
            let Pα := fun α : {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α} => Avoids132 α.1
            rw [← Finset.sum_filter_add_sum_filter_not Finset.univ Pα]
            congr 1
            · rw [G0_poly_eq_sum, Finset.mul_sum, Finset.mul_sum]
              refine Finset.sum_bij (fun α hα => (⟨α.1, α.2.1, α.2.2, (Finset.mem_filter.mp hα).2⟩ :
                  {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α ∧ Avoids132 α}))
                (fun _ _ => Finset.mem_univ _)
                (fun a _ b _ h => Subtype.ext (congrArg (fun x => x.1) h))
                (fun α _ => ⟨⟨α.1, α.2.1, α.2.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, α.2.2.2⟩, rfl⟩)
                ?_
              intro α hα
              have h132 : Avoids132 α.1 := (Finset.mem_filter.mp hα).2
              rw [if_pos h132, pow_succ]; ring
            · rw [G1_poly_eq_sum, Finset.mul_sum]
              refine Finset.sum_bij (fun α hα => (⟨α.1, α.2.1, α.2.2, (Finset.mem_filter.mp hα).2⟩ :
                  {α : Equiv.Perm (Fin (k - m.1)) // InClassB α ∧ IsSkewIndec α ∧ ¬ Avoids132 α}))
                (fun _ _ => Finset.mem_univ _)
                (fun a _ b _ h => Subtype.ext (congrArg (fun x => x.1) h))
                (fun α _ => ⟨⟨α.1, α.2.1, α.2.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, α.2.2.2⟩, rfl⟩)
                ?_
              intro α hα
              have hna : ¬ Avoids132 α.1 := (Finset.mem_filter.mp hα).2
              rw [if_neg hna]
          rw [hreidx_β, Finset.sum_add_distrib, Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_avoids132 m.1]
          have hC : (C_nat m.1 : Polynomial ℚ) = Polynomial.C (C_nat m.1 : ℚ) := by simp
          rw [hC, C_seq]; ring
        rw [hpart_not, hpart_132]; ring
      rw [Finset.sum_congr rfl (fun m _ => hper_m m)]
      simp only [Finset.sum_add_distrib]
      congr 1
      · congr 1
        · congr 1
          · exact Fin.sum_univ_eq_sum_range (fun m => H_poly m * Polynomial.C (S_nat (k - m) : ℚ)) k
          · exact Fin.sum_univ_eq_sum_range (fun m =>
              ∑ _β : {β : Equiv.Perm (Fin m) // Avoids132 β},
                ∑ α : {α : Equiv.Perm (Fin (k - m)) // InClassB α ∧ IsSkewIndec α},
                  ∑ j : {j : Fin (k - m + 1) // 1 ≤ j.1 ∧ j.1 < dB α.1 - 1},
                    (Polynomial.X : Polynomial ℚ) ^ (m + j.1.1)) k
        · exact Fin.sum_univ_eq_sum_range (fun m => C_seq m * (Polynomial.X * G0_poly (k - m))) k
      · exact Fin.sum_univ_eq_sum_range (fun m => C_seq m * G1_poly (k - m)) k
    have hcase2 :
        (1 - Polynomial.X) *
          (∑ m ∈ Finset.range k,
            ∑ _β : {β : Equiv.Perm (Fin m) // Avoids132 β},
              ∑ α : {α : Equiv.Perm (Fin (k - m)) // InClassB α ∧ IsSkewIndec α},
                ∑ j : {j : Fin (k - m + 1) // 1 ≤ j.1 ∧ j.1 < dB α.1 - 1},
                  (Polynomial.X : Polynomial ℚ) ^ (m + j.1.1)) =
        ∑ m ∈ Finset.range k, C_seq m *
          (Polynomial.X * Polynomial.C ((G_poly (k - m)).eval 1) - Polynomial.X * G_poly (k - m)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmk : m < k := Finset.mem_range.mp hm
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, card_avoids132 m]
      have hinner :
          (1 - Polynomial.X) *
            ∑ α : {α : Equiv.Perm (Fin (k - m)) // InClassB α ∧ IsSkewIndec α},
              ∑ j : {j : Fin (k - m + 1) // 1 ≤ j.1 ∧ j.1 < dB α.1 - 1},
                (Polynomial.X : Polynomial ℚ) ^ (m + j.1.1) =
          Polynomial.X ^ m *
            (Polynomial.X * Polynomial.C ((G_poly (k - m)).eval 1) - Polynomial.X * G_poly (k - m)) := by
        rw [Finset.mul_sum, G_poly_eval_one (k - m)]
        have hcard :
            Polynomial.X ^ m *
              (Polynomial.X * Polynomial.C (B_ind (k - m) : ℚ) - Polynomial.X * G_poly (k - m)) =
            ∑ α : {α : Equiv.Perm (Fin (k - m)) // InClassB α ∧ IsSkewIndec α},
              Polynomial.X ^ m * (Polynomial.X - Polynomial.X * Polynomial.X ^ (dB α.1 - 2)) := by
          unfold G_poly B_ind
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul, ← Finset.mul_sum]
          have hC : (Fintype.card {α : Equiv.Perm (Fin (k - m)) // InClassB α ∧ IsSkewIndec α} : Polynomial ℚ) =
              Polynomial.C (Fintype.card {α : Equiv.Perm (Fin (k - m)) // InClassB α ∧ IsSkewIndec α} : ℚ) := by simp
          rw [hC]; ring
        rw [hcard]
        refine Finset.sum_congr rfl fun α _ => ?_
        have hd2 : 2 ≤ dB α.1 := dB_ge_two_indec (by omega) α.2.1 α.2.2
        have hdle : dB α.1 - 1 ≤ k - m + 1 := by have := dB_le_succ α.1; omega
        rw [sum_subtype_fin_Ico 1 (dB α.1 - 1) hdle (fun j => (Polynomial.X : Polynomial ℚ) ^ (m + j))]
        simp_rw [pow_add]
        rw [← Finset.mul_sum, ← mul_assoc, mul_comm (1 - Polynomial.X) (Polynomial.X ^ m), mul_assoc,
          one_sub_X_mul_sum_Ico (dB α.1 - 1) (by omega)]
        have hpow : (Polynomial.X : Polynomial ℚ) ^ (dB α.1 - 1) =
            Polynomial.X * Polynomial.X ^ (dB α.1 - 2) := by
          rw [← pow_succ', show dB α.1 - 2 + 1 = dB α.1 - 1 by omega]
        rw [hpow]
      have hCeq : (C_nat m : Polynomial ℚ) = Polynomial.C (C_nat m : ℚ) := by simp
      rw [← mul_assoc, mul_comm (1 - Polynomial.X) (C_nat m : Polynomial ℚ), mul_assoc, hinner, hCeq]
      unfold C_seq
      ring
    rw [hG_decomp]
    have hcomb := sum_H_S_add_G1 k hk
    change (1 - Polynomial.X) * _ =
      (1 - Polynomial.X) *
        (∑ a ∈ Finset.range (k + 2), C_seq a *
          ∑ b ∈ Finset.range (k + 1 - a + 1), G1_poly b * Polynomial.C ((G_poly (k + 1 - a - b)).eval 1)) +
      (∑ m ∈ Finset.range k, C_seq m *
        (Polynomial.X * Polynomial.C ((G_poly (k - m)).eval 1) - Polynomial.X * G_poly (k - m))) +
      (1 - Polynomial.X) *
        (∑ m ∈ Finset.range k, C_seq m * (Polynomial.X * G0_poly (k - m)))
    rw [← hcomb, ← hcase2]
    ring

private lemma card_classB_indec (n : ℕ) (hn : 1 ≤ n) :
    Fintype.card {α : Equiv.Perm (Fin n) // InClassB α ∧ IsSkewIndec α} = T_nat (n - 1) := by
  have h := kernel_G_eval_one G_poly G_poly_zero G_poly_one G_poly_rec n hn
  rw [G_poly_eval_one] at h
  exact Nat.cast_injective (R := ℚ) h

end ClassB

private lemma card_classA_eq_classB (n : ℕ) :
    Fintype.card {σ : Equiv.Perm (Fin n) // InClassA σ} =
    Fintype.card {σ : Equiv.Perm (Fin n) // InClassB σ} := by
  refine invert_card_eq InClassA InClassB
    (fun hm α β => inClassA_skewSumCast hm α β)
    (fun hm α β => inClassB_skewSumCast hm α β)
    (avoids132_imp_inClassA (fun i => Fin.elim0 i))
    (avoids132_imp_inClassB (fun i => Fin.elim0 i))
    (fun k hk => ?_) n
  rw [card_classA_indec k hk, card_classB_indec k hk]

end OMA.S_oeis_a098746

theorem OMA.solution : type_of% @OMA.S_oeis_a098746.main := by
  intro n
  have heqA : {σ : Equiv.Perm (Fin n) //
      OMA.S_oeis_a098746.Avoids σ ![4, 2, 3, 1] ∧ OMA.S_oeis_a098746.Avoids σ ![4, 2, 5, 1, 3]} ≃
      {σ : Equiv.Perm (Fin n) // OMA.S_oeis_a098746.InClassA σ} :=
    { toFun := fun ⟨σ, h1, h2⟩ =>
        ⟨σ.trans Fin.revPerm,
         (OMA.S_oeis_a098746.avoids_4231_iff σ).mp h1,
         (OMA.S_oeis_a098746.avoids_42513_iff σ).mp h2⟩
      invFun := fun ⟨τ, h1, h2⟩ =>
        ⟨τ.trans Fin.revPerm,
         (OMA.S_oeis_a098746.avoids_4231_iff _).mpr (by
           have hrev : (τ.trans Fin.revPerm).trans Fin.revPerm = τ := by
             ext x; simp
           rw [hrev]; exact h1),
         (OMA.S_oeis_a098746.avoids_42513_iff _).mpr (by
           have hrev : (τ.trans Fin.revPerm).trans Fin.revPerm = τ := by
             ext x; simp
           rw [hrev]; exact h2)⟩
      left_inv := fun ⟨σ, _, _⟩ => Subtype.ext (by ext x; simp)
      right_inv := fun ⟨τ, _, _⟩ => Subtype.ext (by ext x; simp) }
  have heqB : {σ : Equiv.Perm (Fin n) //
      OMA.S_oeis_a098746.Avoids σ ![1, 3, 4, 2] ∧ OMA.S_oeis_a098746.Avoids σ ![1, 3, 2, 5, 4]} ≃
      {σ : Equiv.Perm (Fin n) // OMA.S_oeis_a098746.InClassB σ} :=
    Equiv.subtypeEquivRight (fun σ => by
      unfold OMA.S_oeis_a098746.InClassB
      rw [OMA.S_oeis_a098746.avoids_1342_iff, OMA.S_oeis_a098746.avoids_13254_iff])
  rw [Nat.card_congr heqA, Nat.card_congr heqB, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact OMA.S_oeis_a098746.card_classA_eq_classB n
