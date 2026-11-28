import OMAStatements.S_oeis_a183068
import Mathlib

open Finset Polynomial

namespace A183068R3

/-- product over `x < M` of `(if p ∣ x+1 then 1 else c + (x+1))` -/
private lemma reflect_eq (p M : ℕ) (hpM : p ∣ M) (hev : Even (#{j ∈ range M | ¬ p ∣ j})) :
    ∏ x ∈ range M, (if p ∣ x + 1 then (1:ℤ) else ((x:ℤ) + 1) - M)
      = ∏ x ∈ range M, (if p ∣ x + 1 then (1:ℤ) else (x:ℤ) + 1) := by
  rw [← prod_range_reflect]
  have h1 : ∀ j ∈ range M, (if p ∣ M - 1 - j + 1 then (1:ℤ) else (((M - 1 - j : ℕ):ℤ) + 1) - M)
      = (if p ∣ j then (1:ℤ) else -1) * (if p ∣ j then (1:ℤ) else (j:ℤ)) := by
    intro j hj
    rw [mem_range] at hj
    have he : M - 1 - j + 1 = M - j := by omega
    have hiff : p ∣ M - j ↔ p ∣ j := by
      constructor
      · intro h
        have := (Nat.dvd_add_right h).mp (by rw [Nat.sub_add_cancel hj.le]; exact hpM)
        exact this
      · intro h
        exact (Nat.dvd_add_right h).mp (by rw [Nat.add_sub_cancel' hj.le]; exact hpM)
    simp only [he, hiff]
    split_ifs
    · ring
    · push_cast [show M - 1 - j = M - (j + 1) by omega, Nat.cast_sub (show j + 1 ≤ M by omega)]
      ring
  rw [prod_congr rfl h1, prod_mul_distrib]
  have h2 : ∏ x ∈ range M, (if p ∣ x then (1:ℤ) else -1) = 1 := by
    rw [prod_ite, prod_const_one, one_mul, prod_const]
    exact Even.neg_one_pow hev
  rw [h2, one_mul]
  -- shift
  have h3 : ∀ f : ℕ → ℤ, f 0 = 1 → f M = 1 →
      ∏ x ∈ range M, f x = ∏ x ∈ range M, f (x + 1) := by
    intro f h0 hM
    have a := prod_range_succ f M
    have b := prod_range_succ' f M
    rw [hM, mul_one] at a
    rw [h0, mul_one] at b
    rw [← a, b]
  have := h3 (fun x => if p ∣ x then (1:ℤ) else (x:ℤ)) (by simp) (by simp [hpM])
  rw [this]
  apply prod_congr rfl
  intro x _
  push_cast
  rfl

/-- Key lemma K. -/
private lemma keyK (p s : ℕ) (hp : p.Prime) (hM : 2 < p ^ (s + 1)) (c : ℤ)
    (hc : ((p ^ (s + 1) : ℕ) : ℤ) ∣ c) :
    (((p ^ (s + 1) : ℕ) : ℤ)) ^ 2 ∣
      ∏ x ∈ range (p ^ (s + 1)), (if p ∣ x + 1 then (1:ℤ) else c + ((x:ℤ) + 1))
      - ∏ x ∈ range (p ^ (s + 1)), (if p ∣ x + 1 then (1:ℤ) else (x:ℤ) + 1) := by
  set M := p ^ (s + 1) with hMdef
  have hpM : p ∣ M := dvd_pow_self p (Nat.succ_ne_zero s)
  have hev : Even (#{j ∈ range M | ¬ p ∣ j}) := by
    have : ({j ∈ range M | ¬ p ∣ j} : Finset ℕ) = {j ∈ range M | M.Coprime j} := by
      ext j
      simp only [mem_filter, mem_range]
      rw [hMdef, Nat.coprime_pow_left_iff (Nat.succ_pos s), Nat.Prime.coprime_iff_not_dvd hp]
    rw [this]
    exact Nat.totient_even hM
  have hR := reflect_eq p M hpM hev
  have hR' : ∏ x ∈ range M, (if p ∣ x + 1 then (1 : ZMod (M ^ 2)) else -(M : ZMod (M ^ 2)) + ((x : ZMod (M ^ 2)) + 1))
      = ∏ x ∈ range M, (if p ∣ x + 1 then (1 : ZMod (M ^ 2)) else (x : ZMod (M ^ 2)) + 1) := by
    have := congrArg (fun z : ℤ => (z : ZMod (M ^ 2))) hR
    simp only [Int.cast_prod, apply_ite (Int.cast : ℤ → ZMod (M ^ 2)), Int.cast_one, Int.cast_sub,
      Int.cast_add, Int.cast_natCast] at this
    rw [← this]
    apply prod_congr rfl
    intro x _
    split_ifs
    · rfl
    · ring
  let P : (ZMod (M ^ 2))[X] :=
    ∏ x ∈ range M, (if p ∣ x + 1 then (1 : (ZMod (M ^ 2))[X]) else X + C ((x : ZMod (M ^ 2)) + 1))
  have hev' : ∀ y : ZMod (M ^ 2), P.eval y =
      ∏ x ∈ range M, (if p ∣ x + 1 then (1 : ZMod (M ^ 2)) else y + ((x : ZMod (M ^ 2)) + 1)) := by
    intro y
    simp only [P, eval_prod]
    apply prod_congr rfl
    intro x _
    split_ifs <;> simp
  have hMsq : (M : ZMod (M ^ 2)) ^ 2 = 0 := by
    rw [← Nat.cast_pow, ZMod.natCast_self]
  have e2 := eval_add_of_sq_eq_zero P 0 (-(M : ZMod (M ^ 2))) (by rw [neg_sq, hMsq])
  have e3 : P.eval (0 + -(M : ZMod (M ^ 2))) = P.eval 0 := by
    rw [hev', hev', zero_add, hR']
    apply prod_congr rfl
    intro x _
    split_ifs <;> simp
  have hD : P.derivative.eval 0 * (M : ZMod (M ^ 2)) = 0 := by
    rw [e3] at e2
    linear_combination e2
  have key : ∀ t : ZMod (M ^ 2), P.eval (0 + (M : ZMod (M ^ 2)) * t) = P.eval 0 := by
    intro t
    rw [eval_add_of_sq_eq_zero P 0 ((M : ZMod (M ^ 2)) * t) (by rw [mul_pow, hMsq, zero_mul])]
    rw [← mul_assoc, hD, zero_mul, add_zero]
  obtain ⟨t, rfl⟩ := hc
  have k := key (t : ZMod (M ^ 2))
  rw [hev', hev', zero_add] at k
  rw [show ((M:ℤ)) ^ 2 = ((M ^ 2 : ℕ) : ℤ) by push_cast; ring, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub, Int.cast_prod, apply_ite (Int.cast : ℤ → ZMod (M ^ 2)), Int.cast_one,
    Int.cast_add, Int.cast_mul, Int.cast_natCast]
  rw [sub_eq_zero]
  convert k using 2
  · simp

/-- unit factorial -/
private def U (p L : ℕ) : ℕ := ∏ x ∈ range L, (if p ∣ x + 1 then 1 else x + 1)

private lemma U_cast (p L : ℕ) :
    ((U p L : ℕ) : ℤ) = ∏ x ∈ range L, (if p ∣ x + 1 then (1:ℤ) else (x:ℤ) + 1) := by
  simp only [U, Nat.cast_prod]
  apply prod_congr rfl
  intro x _
  split_ifs <;> simp

private lemma U_not_dvd {p : ℕ} (hp : p.Prime) (L : ℕ) : ¬ p ∣ U p L := by
  unfold U
  rw [Prime.dvd_finset_prod_iff hp.prime]
  rintro ⟨x, _, hx⟩
  split_ifs at hx with h
  · exact hp.one_lt.ne' (Nat.dvd_one.mp hx)
  · exact h hx

private lemma U_block {p s : ℕ} (hp : p.Prime) (hM : 2 < p ^ (s + 1)) (y : ℕ) :
    (((p ^ (s + 1) : ℕ) : ℤ)) ^ 2 ∣ ((U p (p ^ (s + 1) * y) : ℕ) : ℤ) - ((U p (p ^ (s + 1)) : ℕ) : ℤ) ^ y := by
  set M := p ^ (s + 1) with hMdef
  have hpM : p ∣ M := dvd_pow_self p (Nat.succ_ne_zero s)
  induction y with
  | zero => simp [U]
  | succ y ih =>
    have hsplit : ((U p (M * (y + 1)) : ℕ) : ℤ) = ((U p (M * y) : ℕ) : ℤ) *
        ∏ x ∈ range M, (if p ∣ x + 1 then (1:ℤ) else ((M * y : ℕ) : ℤ) + ((x:ℤ) + 1)) := by
      rw [U_cast, U_cast, show M * (y + 1) = M * y + M by ring, prod_range_add]
      congr 1
      apply prod_congr rfl
      intro x _
      have hiff : p ∣ M * y + x + 1 ↔ p ∣ x + 1 := by
        rw [add_assoc]; exact Nat.dvd_add_right (dvd_mul_of_dvd_left hpM y)
      simp only [hiff]
      split_ifs <;> push_cast <;> ring
    have hK := keyK p s hp hM ((M * y : ℕ) : ℤ) (by push_cast; exact dvd_mul_right _ _)
    rw [← U_cast] at hK
    rw [hsplit, pow_succ ((U p M : ℕ) : ℤ) y]
    have : ((U p (M * y) : ℕ) : ℤ) * ∏ x ∈ range M, (if p ∣ x + 1 then (1:ℤ) else ((M * y : ℕ) : ℤ) + ((x:ℤ) + 1))
        - ((U p M : ℕ) : ℤ) ^ y * ((U p M : ℕ) : ℤ)
        = ((U p (M * y) : ℕ) : ℤ) * (∏ x ∈ range M, (if p ∣ x + 1 then (1:ℤ) else ((M * y : ℕ) : ℤ) + ((x:ℤ) + 1))
            - ((U p M : ℕ) : ℤ)) + (((U p (M * y) : ℕ) : ℤ) - ((U p M : ℕ) : ℤ) ^ y) * ((U p M : ℕ) : ℤ) := by ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right hK _) (dvd_mul_of_dvd_left ih _)

private lemma U_comb {p s : ℕ} (hp : p.Prime) (hM : 2 < p ^ (s + 1)) (a b : ℕ) :
    (((p ^ (s + 1) : ℕ) : ℤ)) ^ 2 ∣ ((U p (p ^ (s + 1) * (4 * a + 2 * b)) : ℕ) : ℤ)
      - ((U p (p ^ (s + 1) * a) : ℕ) : ℤ) ^ 4 * ((U p (p ^ (s + 1) * b) : ℕ) : ℤ) ^ 2 := by
  have hE := (Int.modEq_iff_dvd.mpr (U_block hp hM (4 * a + 2 * b))).symm
  have hA := (Int.modEq_iff_dvd.mpr (U_block hp hM a)).symm
  have hB := (Int.modEq_iff_dvd.mpr (U_block hp hM b)).symm
  have h2 := (hA.pow 4).mul (hB.pow 2)
  have : (((U p (p ^ (s + 1)) : ℕ) : ℤ) ^ a) ^ 4 * (((U p (p ^ (s + 1)) : ℕ) : ℤ) ^ b) ^ 2
      = ((U p (p ^ (s + 1)) : ℕ) : ℤ) ^ (4 * a + 2 * b) := by ring
  rw [this] at h2
  exact Int.modEq_iff_dvd.mp (h2.trans hE.symm)

private lemma V_eq {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ∏ x ∈ range (p * m), (if p ∣ x + 1 then x + 1 else 1) = p ^ m * m.factorial := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show p * (m + 1) = p * m + p by ring, prod_range_add, ih]
    have hin : ∏ x ∈ range p, (if p ∣ p * m + x + 1 then p * m + x + 1 else 1) = p * (m + 1) := by
      rw [hq, prod_range_succ, ← hq]
      have h1 : ∏ x ∈ range q, (if p ∣ p * m + x + 1 then p * m + x + 1 else 1) = 1 := by
        apply prod_eq_one
        intro x hx
        rw [mem_range] at hx
        have : ¬ p ∣ p * m + x + 1 := by
          intro h
          rw [add_assoc] at h
          have h' := (Nat.dvd_add_right (dvd_mul_right p m)).mp h
          have := Nat.le_of_dvd (Nat.succ_pos x) h'
          omega
        simp [this]
      rw [h1, one_mul]
      have : p * m + q + 1 = p * (m + 1) := by rw [hq]; ring
      rw [this]
      simp
    rw [hin, Nat.factorial_succ]
    ring

private lemma fact_split {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (p * m).factorial = p ^ m * m.factorial * U p (p * m) := by
  rw [← V_eq hp m, U, ← prod_mul_distrib, ← Finset.prod_range_add_one_eq_factorial]
  apply prod_congr rfl
  intro x _
  split_ifs <;> simp

/-- the summand -/
private def T (N k : ℕ) : ℕ :=
  Nat.choose (2 * N) N * (Nat.choose N k ^ 2 * Nat.choose (2 * N + 2 * k) (2 * k) * Nat.choose (2 * k) k)

private lemma T_fact (k d : ℕ) :
    T (k + d) k * (k.factorial ^ 4 * d.factorial ^ 2) = (2 * (k + d) + 2 * k).factorial := by
  have h1 := Nat.choose_mul_factorial_mul_factorial (show k ≤ 2 * k by omega)
  rw [show 2 * k - k = k by omega] at h1
  have h2 := Nat.choose_mul_factorial_mul_factorial (show k ≤ k + d by omega)
  rw [show k + d - k = d by omega] at h2
  have h3 := Nat.choose_mul_factorial_mul_factorial (show k + d ≤ 2 * (k + d) by omega)
  rw [show 2 * (k + d) - (k + d) = k + d by omega] at h3
  have h4 := Nat.choose_mul_factorial_mul_factorial (show 2 * k ≤ 2 * (k + d) + 2 * k by omega)
  rw [show 2 * (k + d) + 2 * k - 2 * k = 2 * (k + d) by omega] at h4
  rw [← h4, ← h3, ← h1, ← h2, T]
  ring

private lemma T_ident {p : ℕ} (hp : p.Prime) (j d : ℕ) :
    T (p * (j + d)) (p * j) * (U p (p * j) ^ 4 * U p (p * d) ^ 2)
      = T (j + d) j * U p (p * (2 * (j + d) + 2 * j)) := by
  have hA := T_fact (p * j) (p * d)
  rw [show p * j + p * d = p * (j + d) by ring,
    show 2 * (p * (j + d)) + 2 * (p * j) = p * (2 * (j + d) + 2 * j) by ring,
    fact_split hp, fact_split hp, fact_split hp] at hA
  have hB := T_fact j d
  have hX : 0 < p ^ (4 * j + 2 * d) * (j.factorial ^ 4 * d.factorial ^ 2) :=
    Nat.mul_pos (pow_pos hp.pos _) (Nat.mul_pos (pow_pos (Nat.factorial_pos _) _) (pow_pos (Nat.factorial_pos _) _))
  apply Nat.eq_of_mul_eq_mul_right hX
  calc T (p * (j + d)) (p * j) * (U p (p * j) ^ 4 * U p (p * d) ^ 2) * (p ^ (4 * j + 2 * d) * (j.factorial ^ 4 * d.factorial ^ 2))
      = T (p * (j + d)) (p * j) * ((p ^ j * j.factorial * U p (p * j)) ^ 4 * (p ^ d * d.factorial * U p (p * d)) ^ 2) := by ring
    _ = p ^ (2 * (j + d) + 2 * j) * (2 * (j + d) + 2 * j).factorial * U p (p * (2 * (j + d) + 2 * j)) := hA
    _ = p ^ (2 * (j + d) + 2 * j) * (T (j + d) j * (j.factorial ^ 4 * d.factorial ^ 2)) * U p (p * (2 * (j + d) + 2 * j)) := by rw [hB]
    _ = T (j + d) j * U p (p * (2 * (j + d) + 2 * j)) * (p ^ (4 * j + 2 * d) * (j.factorial ^ 4 * d.factorial ^ 2)) := by ring
/-- Kummer-type bound: if `p^r ∣ N` and `p ∤ k` then `p^r ∣ C(N,k)`. -/
private lemma ppow_dvd_choose {p r N k : ℕ} (hp : p.Prime) (hN : p ^ r ∣ N) (hk : ¬ p ∣ k) :
    p ^ r ∣ Nat.choose N k := by
  rcases Nat.eq_zero_or_pos k with h0 | hkpos
  · subst h0; exact absurd (dvd_zero p) hk
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0; rw [Nat.choose_eq_zero_of_lt hkpos]; exact dvd_zero _
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hid := Nat.add_one_mul_choose_eq M j
  have hcop : Nat.Coprime (p ^ r) (j + 1) :=
    Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hk)
  apply hcop.dvd_of_dvd_mul_right
  rw [← hid]
  exact Dvd.dvd.mul_right hN _

/-- Terms with `p ∤ k` vanish modulo `p^(2r)`. -/
private lemma term_dvd {p r N k : ℕ} (hp : p.Prime) (hN : p ^ r ∣ N) (hk : ¬ p ∣ k) :
    p ^ (2 * r) ∣ Nat.choose (2 * N) N * (Nat.choose N k ^ 2 * Nat.choose (2 * N + 2 * k) (2 * k)
      * Nat.choose (2 * k) k) := by
  have h := ppow_dvd_choose hp hN hk
  have h2 : p ^ (2 * r) ∣ Nat.choose N k ^ 2 := by
    rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd h 2
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right h2 _) _) _

private lemma T_dvd_of {p e Q j : ℕ} (h : p ^ e ∣ Nat.choose Q j) : p ^ (2 * e) ∣ T Q j := by
  unfold T
  have h2 : p ^ (2 * e) ∣ Nat.choose Q j ^ 2 := by
    rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd h 2
  exact Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_right h2 _) _) _

private lemma T_dvd_two {e Q j : ℕ} (hQ : 1 ≤ Q) (h : 2 ^ e ∣ Nat.choose Q j) :
    2 ^ (2 * e + 1) ∣ T Q j := by
  unfold T
  have h2 : 2 ^ (2 * e) ∣ Nat.choose Q j ^ 2 := by
    rw [mul_comm, pow_mul]; exact pow_dvd_pow_of_dvd h 2
  have hc : 2 ∣ Nat.choose (2 * Q) Q := by
    rw [← Nat.centralBinom_eq_two_mul_choose]; exact Nat.two_dvd_centralBinom_of_one_le hQ
  rw [pow_succ, mul_comm]
  exact mul_dvd_mul hc (Dvd.dvd.mul_right (Dvd.dvd.mul_right h2 _) _)

private lemma two_lt_pow {p s : ℕ} (hp : p.Prime) (h : p ≠ 2 ∨ 1 ≤ s) : 2 < p ^ (s + 1) := by
  have h2 := hp.two_le
  rcases h with h | h
  · have h3 : 3 ≤ p := by omega
    calc 2 < p := by omega
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ (s + 1) := Nat.pow_le_pow_right hp.pos (by omega)
  · calc 2 < 2 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left h2 2
      _ ≤ p ^ (s + 1) := Nat.pow_le_pow_right hp.pos (by omega)

private lemma term_cong {p r j d : ℕ} (hp : p.Prime) (hr : 1 ≤ r) (hQ1 : 1 ≤ j + d)
    (hQ : p ^ (r - 1) ∣ j + d) :
    (p : ℤ) ^ (2 * r) ∣ ((T (p * (j + d)) (p * j) : ℕ) : ℤ) - ((T (j + d) j : ℕ) : ℤ) := by
  have hI := congrArg (fun z : ℕ => (z : ℤ)) (T_ident hp j d)
  push_cast at hI
  set D : ℤ := ((U p (p * j) : ℕ) : ℤ) ^ 4 * ((U p (p * d) : ℕ) : ℤ) ^ 2 with hDdef
  set E : ℤ := ((U p (p * (2 * (j + d) + 2 * j)) : ℕ) : ℤ) with hEdef
  have hDc : IsCoprime ((p : ℤ) ^ (2 * r)) D := by
    apply IsCoprime.pow_left
    rw [hDdef]
    apply IsCoprime.mul_right <;> apply IsCoprime.pow_right <;>
      exact (Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr (U_not_dvd hp _)))
  suffices hs : (p : ℤ) ^ (2 * r) ∣ ((T (j + d) j : ℕ) : ℤ) * (E - D) by
    apply hDc.dvd_of_dvd_mul_right
    have : (((T (p * (j + d)) (p * j) : ℕ) : ℤ) - ((T (j + d) j : ℕ) : ℤ)) * D
        = ((T (j + d) j : ℕ) : ℤ) * (E - D) := by
      rw [hDdef, hEdef]; linear_combination hI
    rw [this]; exact hs
  have H : ∀ s, s ≤ r - 1 → p ^ s ∣ j → p ^ s ∣ d → (p ≠ 2 ∨ 1 ≤ s) →
      p ^ (r - 1 - s) ∣ Nat.choose (j + d) j →
      (p : ℤ) ^ (2 * r) ∣ ((T (j + d) j : ℕ) : ℤ) * (E - D) := by
    intro s hs hj hd hcase hC
    have hU := U_comb hp (two_lt_pow hp hcase) (j / p ^ s) (d / p ^ s)
    have hja : j = p ^ s * (j / p ^ s) := (Nat.mul_div_cancel' hj).symm
    have hdb : d = p ^ s * (d / p ^ s) := (Nat.mul_div_cancel' hd).symm
    have e1 : p ^ (s + 1) * (4 * (j / p ^ s) + 2 * (d / p ^ s)) = p * (2 * (j + d) + 2 * j) := by
      conv_rhs => rw [hja, hdb]
      ring
    have e2 : p ^ (s + 1) * (j / p ^ s) = p * j := by conv_rhs => rw [hja]
                                                      ring
    have e3 : p ^ (s + 1) * (d / p ^ s) = p * d := by conv_rhs => rw [hdb]
                                                      ring
    rw [e1, e2, e3] at hU
    have hT' : (p : ℤ) ^ (2 * (r - 1 - s)) ∣ ((T (j + d) j : ℕ) : ℤ) := by
      exact_mod_cast T_dvd_of hC
    have hp2 : (((p ^ (s + 1) : ℕ) : ℤ)) ^ 2 = (p : ℤ) ^ (2 * s + 2) := by push_cast; ring
    rw [hp2] at hU
    have := mul_dvd_mul hT' hU
    rw [← pow_add, show 2 * (r - 1 - s) + (2 * s + 2) = 2 * r by omega] at this
    exact this
  have H2 : p = 2 → p ^ (r - 1) ∣ Nat.choose (j + d) j →
      (p : ℤ) ^ (2 * r) ∣ ((T (j + d) j : ℕ) : ℤ) * (E - D) := by
    intro h2 hC
    subst h2
    have hT' : (2 : ℤ) ^ (2 * (r - 1) + 1) ∣ ((T (j + d) j : ℕ) : ℤ) := by
      exact_mod_cast T_dvd_two hQ1 hC
    have hodd : ∀ L, Odd (((U 2 L : ℕ) : ℤ)) := by
      intro L
      have := U_not_dvd Nat.prime_two L
      rw [← Int.not_even_iff_odd, even_iff_two_dvd]
      exact_mod_cast this
    have hED : (2 : ℤ) ∣ E - D := by
      rw [← even_iff_two_dvd, hEdef, hDdef]
      exact Odd.sub_odd (hodd _) (((hodd _).pow).mul (hodd _).pow)
    have := mul_dvd_mul hT' hED
    rw [← pow_succ, show 2 * (r - 1) + 1 + 1 = 2 * r by omega] at this
    exact_mod_cast this
  by_cases hA : p ^ (r - 1) ∣ j
  · have hd : p ^ (r - 1) ∣ d := (Nat.dvd_add_right hA).mp hQ
    by_cases hc : p ≠ 2 ∨ 1 ≤ r - 1
    · exact H (r - 1) le_rfl hA hd hc (by simp)
    · push Not at hc
      exact H2 hc.1 (by rw [show r - 1 = 0 by omega]; simp)
  · have hj0 : j ≠ 0 := by rintro rfl; exact hA (dvd_zero _)
    have hfact : Fact p.Prime := ⟨hp⟩
    obtain ⟨s, hsdef⟩ : ∃ s, s = padicValNat p j := ⟨_, rfl⟩
    have hjs : p ^ s ∣ j := by rw [hsdef]; exact pow_padicValNat_dvd
    have hjs1 : ¬ p ^ (s + 1) ∣ j := by rw [hsdef]; exact pow_succ_padicValNat_not_dvd hj0
    have hsr : s < r - 1 := by
      by_contra hcon
      exact hA ((pow_dvd_pow p (by omega)).trans hjs)
    have hQs : p ^ s ∣ j + d := (pow_dvd_pow p hsr.le).trans hQ
    have hds : p ^ s ∣ d := (Nat.dvd_add_right hjs).mp hQs
    have hC : p ^ (r - 1 - s) ∣ Nat.choose (j + d) j := by
      obtain ⟨a, ha⟩ := hjs
      have hpa : ¬ p ∣ a := by
        rintro ⟨c, rfl⟩; exact hjs1 ⟨c, by rw [ha]; ring⟩
      obtain ⟨M, hM⟩ : ∃ M, j + d = M + 1 := ⟨j + d - 1, by omega⟩
      obtain ⟨i, hi⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have hid := Nat.add_one_mul_choose_eq M i
      have h1 : p ^ (r - 1) ∣ Nat.choose (j + d) j * j := by
        rw [hM, hi, ← hid, ← hM]; exact Dvd.dvd.mul_right hQ _
      have h1' : p ^ s * p ^ (r - 1 - s) ∣ p ^ s * (Nat.choose (j + d) j * a) := by
        rw [← pow_add, show s + (r - 1 - s) = r - 1 by omega,
          show p ^ s * (Nat.choose (j + d) j * a) = Nat.choose (j + d) j * j by rw [ha]; ring]
        exact h1
      have h2 := Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos s) h1'
      exact (Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).2 hpa)).dvd_of_dvd_mul_right h2
    by_cases hc : p ≠ 2 ∨ 1 ≤ s
    · exact H s hsr.le hjs hds hc hC
    · push Not at hc
      have hs0 : s = 0 := by omega
      exact H2 hc.1 (by rw [hs0, Nat.sub_zero] at hC; exact hC)

private lemma sum_blocks (f : ℕ → ℤ) (p m : ℕ) :
    ∑ k ∈ range (p * m), f k = ∑ j ∈ range m, ∑ i ∈ range p, f (p * j + i) := by
  induction m with
  | zero => simp
  | succ m ih => rw [show p * (m + 1) = p * m + p by ring, sum_range_add, ih, sum_range_succ]

private lemma sum_cong {p r Q : ℕ} (hp : p.Prime) (hN : p ^ r ∣ p * Q) :
    (p : ℤ) ^ (2 * r) ∣ ∑ k ∈ range (p * Q + 1), ((T (p * Q) k : ℕ) : ℤ)
      - ∑ j ∈ range (Q + 1), ((T (p * Q) (p * j) : ℕ) : ℤ) := by
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  have h1 : ∑ k ∈ range (p * (Q + 1)), ((T (p * Q) k : ℕ) : ℤ)
      = ∑ k ∈ range (p * Q + 1), ((T (p * Q) k : ℕ) : ℤ) := by
    rw [show p * (Q + 1) = (p * Q + 1) + q by rw [hq]; ring, sum_range_add]
    have : ∑ x ∈ range q, ((T (p * Q) (p * Q + 1 + x) : ℕ) : ℤ) = 0 := by
      apply sum_eq_zero
      intro x _
      simp [T, Nat.choose_eq_zero_of_lt (show p * Q < p * Q + 1 + x by omega)]
    rw [this, add_zero]
  rw [← h1, sum_blocks, ← sum_sub_distrib]
  apply dvd_sum
  intro j _
  rw [hq, sum_range_succ', ← hq]
  simp only [add_zero, add_sub_cancel_right]
  apply dvd_sum
  intro i hi
  rw [mem_range] at hi
  have hk : ¬ p ∣ p * j + (i + 1) := by
    intro h
    have h' := (Nat.dvd_add_right (dvd_mul_right p j)).mp h
    have := Nat.le_of_dvd (Nat.succ_pos i) h'
    omega
  have := term_dvd hp hN hk
  have h2 : p ^ (2 * r) ∣ T (p * Q) (p * j + (i + 1)) := this
  exact_mod_cast h2

private lemma main_gen (a : ℕ → ℕ) (ha : ∀ n, ((a n : ℕ) : ℤ) = ∑ k ∈ range (n + 1), ((T n k : ℕ) : ℤ)) :
    ∀ p n r : ℕ, p.Prime → 1 ≤ n → 1 ≤ r →
      ((p : ℤ) ^ (2 * r)) ∣ ((a (n * p ^ r) : ℤ) - (a (n * p ^ (r - 1)) : ℤ)) := by
  intro p n r hp hn hr
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  obtain ⟨Q, hQdef⟩ : ∃ Q, Q = n * p ^ r' := ⟨_, rfl⟩
  have hNQ : n * p ^ (r' + 1) = p * Q := by rw [hQdef]; ring
  rw [hNQ, ← hQdef, ha, ha]
  have hQ1 : 1 ≤ Q := by rw [hQdef]; exact Nat.mul_pos hn (pow_pos hp.pos _)
  have hdiv : p ^ (r' + 1) ∣ p * Q := ⟨n, by rw [← hNQ]; ring⟩
  have hS := sum_cong hp hdiv
  have hT : (p : ℤ) ^ (2 * (r' + 1)) ∣
      ∑ j ∈ range (Q + 1), (((T (p * Q) (p * j) : ℕ) : ℤ) - ((T Q j : ℕ) : ℤ)) := by
    apply dvd_sum
    intro j hj
    rw [mem_range] at hj
    obtain ⟨d, hd⟩ : ∃ d, Q = j + d := ⟨Q - j, by omega⟩
    have := term_cong (r := r' + 1) (j := j) (d := d) hp (by omega) (by omega)
      (by rw [Nat.add_sub_cancel, ← hd, hQdef]; exact dvd_mul_left _ _)
    rw [← hd] at this
    exact this
  have := dvd_add hS hT
  rw [sum_sub_distrib, sub_add_sub_cancel] at this
  exact this

end A183068R3

theorem OMA.solution : type_of% @OMA.S_oeis_a183068.main :=
  A183068R3.main_gen OMA.S_oeis_a183068.a (fun n => by
    rw [OMA.S_oeis_a183068.a, Finset.mul_sum]; push_cast; rfl)
