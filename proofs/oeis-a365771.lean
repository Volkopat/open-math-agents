import OMAStatements.S_oeis_a365771
import Mathlib

-- Problem: OEIS A365771, conjectures of Paul D. Hanna for
-- a(n) = C(2n+1, n)/(2n+1) * C(3n-1, n): with A033042 = sums of distinct powers of 5,
-- (1) a(5k) == 4, (2) a(5k+1) == 2 (mod 5) for the positive terms k of A033042, and
-- (3) a(n) == 0 (mod 5) for all other n > 0.
-- Statement: statements/oeis-a365771.lean (declaration OMA.S_oeis_a365771.main)
-- Credit: @schulzee (agent: Claude Code, model claude-fable-5-2)
--
-- Proof. The first factor is the Catalan number C(2n, n) - C(2n, n+1). Lucas' theorem modulo 5
-- with n = 5m + r gives a(5m) == C(2m, m) C(3m-1, m) (m > 0), a(5m+1) == 2 C(2m, m) C(3m, m)
-- and a(5m+2) == a(5m+3) == a(5m+4) == 0. The identity 3 C(3m-1, m) = 2 C(3m, m) gives
-- C(3m-1, m) == 4 C(3m, m). Let X(m) = C(2m, m) C(3m, m) modulo 5. Lucas' theorem gives
-- X(5m) = X(m), X(5m+1) = X(m) and X(5m+2) = X(5m+3) = X(5m+4) = 0. A number is a sum of
-- distinct powers of 5 if and only if its last digit in base 5 is 0 or 1 and the quotient by 5
-- is such a sum. So X(m) = 1 for the sums of distinct powers of 5, and X(m) = 0 for the other m.
-- Thus a(5m) == 4 X(m) and a(5m+1) == 2 X(m), which gives the three claims.

namespace OMA.A365771

open Finset OMA.S_oeis_a365771

instance fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

lemma luc (N K : ℕ) : ((N.choose K : ℕ) : ZMod 5)
    = (((N % 5).choose (K % 5) : ℕ) : ZMod 5) * (((N / 5).choose (K / 5) : ℕ) : ZMod 5) := by
  have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := N) (k := K) (p := 5)
  have h2 := (ZMod.natCast_eq_natCast_iff _ _ 5).2 h
  push_cast at h2
  exact h2

/-- Lucas' theorem with explicit quotients and remainders. -/
lemma lucr (N K q1 q2 r1 r2 : ℕ) (hN : N = 5 * q1 + r1) (hK : K = 5 * q2 + r2) (h1 : r1 < 5)
    (h2 : r2 < 5) : ((N.choose K : ℕ) : ZMod 5)
    = ((r1.choose r2 : ℕ) : ZMod 5) * ((q1.choose q2 : ℕ) : ZMod 5) := by
  rw [luc]
  have e1 : N % 5 = r1 := by omega
  have e2 : K % 5 = r2 := by omega
  have e3 : N / 5 = q1 := by omega
  have e4 : K / 5 = q2 := by omega
  rw [e1, e2, e3, e4]

lemma h5 : (5 : ZMod 5) = 0 := by decide

/-- The first factor is the Catalan number C(2n, n) - C(2n, n+1). -/
lemma a_cast (n : ℕ) : (a n : ZMod 5)
    = (((2 * n).choose n : ℕ) - ((2 * n).choose (n + 1) : ℕ)) * ((3 * n - 1).choose n : ℕ) := by
  have h1 := Nat.choose_mul_succ_eq (2 * n) n
  have h2 := Nat.choose_succ_right_eq (2 * n) n
  have e1 : 2 * n + 1 - n = n + 1 := by omega
  have e2 : 2 * n - n = n := by omega
  rw [e1] at h1
  rw [e2] at h2
  have hle : (2 * n).choose (n + 1) ≤ (2 * n).choose n := by
    have : (2 * n).choose (n + 1) * (n + 1) ≤ (2 * n).choose n * (n + 1) := by
      rw [h2]; exact Nat.mul_le_mul_left _ (by omega)
    exact Nat.le_of_mul_le_mul_right this (by omega)
  have hc : ((2 * n).choose n - (2 * n).choose (n + 1)) * (n + 1) = (2 * n).choose n := by
    rw [Nat.sub_mul, h2, ← Nat.mul_sub]
    have : n + 1 - n = 1 := by omega
    rw [this, mul_one]
  have hdiv : (2 * n + 1).choose n / (2 * n + 1)
      = (2 * n).choose n - (2 * n).choose (n + 1) := by
    generalize (2 * n).choose n - (2 * n).choose (n + 1) = c at hc ⊢
    apply Nat.div_eq_of_eq_mul_left (by omega)
    apply Nat.eq_of_mul_eq_mul_right (by omega : 0 < n + 1)
    rw [← h1, ← hc]; ring
  unfold a
  rw [hdiv, Nat.cast_mul, Nat.cast_sub hle]

lemma val0 (m : ℕ) (hm : 0 < m) : (a (5 * m) : ZMod 5)
    = ((2 * m).choose m : ℕ) * ((3 * m - 1).choose m : ℕ) := by
  rw [a_cast,
    lucr (2 * (5 * m)) (5 * m) (2 * m) m 0 0 (by ring) (by ring) (by norm_num) (by norm_num),
    lucr (2 * (5 * m)) (5 * m + 1) (2 * m) m 0 1 (by ring) (by ring) (by norm_num) (by norm_num),
    lucr (3 * (5 * m) - 1) (5 * m) (3 * m - 1) m 4 0 (by omega) (by ring) (by norm_num)
      (by norm_num)]
  simp [Nat.choose]

lemma val1 (m : ℕ) : (a (5 * m + 1) : ZMod 5)
    = 2 * (((2 * m).choose m : ℕ) * ((3 * m).choose m : ℕ)) := by
  rw [a_cast,
    lucr (2 * (5 * m + 1)) (5 * m + 1) (2 * m) m 2 1 (by ring) (by ring) (by norm_num)
      (by norm_num),
    lucr (2 * (5 * m + 1)) (5 * m + 1 + 1) (2 * m) m 2 2 (by ring) (by ring) (by norm_num)
      (by norm_num),
    lucr (3 * (5 * m + 1) - 1) (5 * m + 1) (3 * m) m 2 1 (by omega) (by ring) (by norm_num)
      (by norm_num)]
  have c1 : Nat.choose 2 1 = 2 := by decide
  have c2 : Nat.choose 2 2 = 1 := by decide
  rw [c1, c2]
  push_cast
  ring

lemma val2 (m : ℕ) : (a (5 * m + 2) : ZMod 5) = 0 := by
  rw [a_cast,
    lucr (3 * (5 * m + 2) - 1) (5 * m + 2) (3 * m + 1) m 0 2 (by omega) (by ring) (by norm_num)
      (by norm_num)]
  simp [Nat.choose]

lemma val3 (m : ℕ) : (a (5 * m + 3) : ZMod 5) = 0 := by
  rw [a_cast,
    lucr (2 * (5 * m + 3)) (5 * m + 3) (2 * m + 1) m 1 3 (by ring) (by ring) (by norm_num)
      (by norm_num),
    lucr (2 * (5 * m + 3)) (5 * m + 3 + 1) (2 * m + 1) m 1 4 (by ring) (by ring) (by norm_num)
      (by norm_num)]
  simp [Nat.choose]

lemma val4 (m : ℕ) : (a (5 * m + 4) : ZMod 5) = 0 := by
  rw [a_cast,
    lucr (3 * (5 * m + 4) - 1) (5 * m + 4) (3 * m + 2) m 1 4 (by omega) (by ring) (by norm_num)
      (by norm_num)]
  simp [Nat.choose]

lemma three_m (m : ℕ) (hm : 0 < m) :
    (((3 * m - 1).choose m : ℕ) : ZMod 5) = 4 * ((3 * m).choose m : ℕ) := by
  have h := Nat.choose_mul_succ_eq (3 * m - 1) m
  have e1 : 3 * m - 1 + 1 = 3 * m := by omega
  have e2 : 3 * m - m = 2 * m := by omega
  rw [e1, e2] at h
  have h' : (3 * m - 1).choose m * 3 = (3 * m).choose m * 2 := by
    apply Nat.eq_of_mul_eq_mul_right hm
    calc (3 * m - 1).choose m * 3 * m = (3 * m - 1).choose m * (3 * m) := by ring
      _ = (3 * m).choose m * (2 * m) := h
      _ = (3 * m).choose m * 2 * m := by ring
  have hz := congrArg (fun x : ℕ => (x : ZMod 5)) h'
  simp only [Nat.cast_mul, Nat.cast_ofNat] at hz
  linear_combination 2 * hz - (((3 * m - 1).choose m : ℕ) : ZMod 5) * h5

/-- X(m) = C(2m, m) C(3m, m) modulo 5. -/
def X (m : ℕ) : ZMod 5 := ((2 * m).choose m : ℕ) * ((3 * m).choose m : ℕ)

lemma X0 (m : ℕ) : X (5 * m) = X m := by
  unfold X
  rw [lucr (2 * (5 * m)) (5 * m) (2 * m) m 0 0 (by ring) (by ring) (by norm_num) (by norm_num),
    lucr (3 * (5 * m)) (5 * m) (3 * m) m 0 0 (by ring) (by ring) (by norm_num) (by norm_num)]
  simp

lemma X1 (m : ℕ) : X (5 * m + 1) = X m := by
  unfold X
  rw [lucr (2 * (5 * m + 1)) (5 * m + 1) (2 * m) m 2 1 (by ring) (by ring) (by norm_num)
      (by norm_num),
    lucr (3 * (5 * m + 1)) (5 * m + 1) (3 * m) m 3 1 (by ring) (by ring) (by norm_num)
      (by norm_num)]
  have c1 : Nat.choose 2 1 = 2 := by decide
  have c2 : Nat.choose 3 1 = 3 := by decide
  rw [c1, c2]
  push_cast
  linear_combination ((((2 * m).choose m : ℕ) : ZMod 5) * (((3 * m).choose m : ℕ) : ZMod 5)) * h5

lemma X2 (m : ℕ) : X (5 * m + 2) = 0 := by
  unfold X
  rw [lucr (3 * (5 * m + 2)) (5 * m + 2) (3 * m + 1) m 1 2 (by ring) (by ring) (by norm_num)
      (by norm_num)]
  simp [Nat.choose]

lemma X3 (m : ℕ) : X (5 * m + 3) = 0 := by
  unfold X
  rw [lucr (2 * (5 * m + 3)) (5 * m + 3) (2 * m + 1) m 1 3 (by ring) (by ring) (by norm_num)
      (by norm_num)]
  simp [Nat.choose]

lemma X4 (m : ℕ) : X (5 * m + 4) = 0 := by
  unfold X
  rw [lucr (2 * (5 * m + 4)) (5 * m + 4) (2 * m + 1) m 3 4 (by ring) (by ring) (by norm_num)
      (by norm_num)]
  simp [Nat.choose]

lemma D_mul (m : ℕ) (h : IsSumPow5 m) : IsSumPow5 (5 * m) := by
  obtain ⟨S, rfl⟩ := h
  refine ⟨S.image Nat.succ, ?_⟩
  rw [sum_image (fun x _ y _ hxy => Nat.succ_injective hxy), mul_sum]
  apply sum_congr rfl
  intro i _
  rw [Nat.succ_eq_add_one, pow_succ]; ring

lemma D_mul1 (m : ℕ) (h : IsSumPow5 m) : IsSumPow5 (5 * m + 1) := by
  obtain ⟨S, rfl⟩ := h
  refine ⟨insert 0 (S.image Nat.succ), ?_⟩
  have h0 : (0 : ℕ) ∉ S.image Nat.succ := by
    intro h0
    obtain ⟨x, _, hx⟩ := mem_image.1 h0
    exact Nat.succ_ne_zero x hx
  rw [sum_insert h0, sum_image (fun x _ y _ hxy => Nat.succ_injective hxy), mul_sum, pow_zero,
    add_comm]
  congr 1
  apply sum_congr rfl
  intro i _
  rw [Nat.succ_eq_add_one, pow_succ]; ring

lemma D_inv (k : ℕ) (h : IsSumPow5 k) : k % 5 ≤ 1 ∧ IsSumPow5 (k / 5) := by
  obtain ⟨S, rfl⟩ := h
  have hT : ∑ i ∈ S.erase 0, 5 ^ i = 5 * ∑ j ∈ (S.erase 0).image Nat.pred, 5 ^ j := by
    rw [sum_image, mul_sum]
    · apply sum_congr rfl
      intro i hi
      have hi0 : i ≠ 0 := (mem_erase.1 hi).1
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rw [Nat.pred_eq_sub_one, Nat.add_sub_cancel, pow_succ]; ring
    · intro x hx y hy hxy
      have hx0 : x ≠ 0 := (mem_erase.1 hx).1
      have hy0 : y ≠ 0 := (mem_erase.1 hy).1
      rw [Nat.pred_eq_sub_one, Nat.pred_eq_sub_one] at hxy
      omega
  by_cases h0 : 0 ∈ S
  · have hs : ∑ i ∈ S, 5 ^ i = 1 + ∑ i ∈ S.erase 0, 5 ^ i := by
      rw [← add_sum_erase S _ h0, pow_zero]
    rw [hs, hT]
    exact ⟨by omega, ⟨(S.erase 0).image Nat.pred, by omega⟩⟩
  · have hs : S.erase 0 = S := erase_eq_of_notMem h0
    rw [hs] at hT
    rw [hT]
    exact ⟨by omega, ⟨S.image Nat.pred, by omega⟩⟩

lemma XD : ∀ m : ℕ, (IsSumPow5 m → X m = 1) ∧ (¬ IsSumPow5 m → X m = 0) := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    by_cases hm : m = 0
    · subst hm
      refine ⟨fun _ => by unfold X; simp, fun h => absurd ⟨∅, by simp⟩ h⟩
    · obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 5 ∧ m = 5 * q + r :=
        ⟨m / 5, m % 5, Nat.mod_lt _ (by norm_num), by omega⟩
      have ihq := ih q (by omega)
      have hinv : IsSumPow5 (5 * q + r) → r ≤ 1 ∧ IsSumPow5 q := by
        intro h
        have h' := D_inv _ h
        have e1 : (5 * q + r) % 5 = r := by omega
        have e2 : (5 * q + r) / 5 = q := by omega
        rw [e1, e2] at h'
        exact h'
      interval_cases r
      · rw [add_zero] at hinv ⊢
        rw [X0]
        exact ⟨fun h => ihq.1 (hinv h).2, fun h => ihq.2 (fun hq => h (D_mul q hq))⟩
      · rw [X1]
        exact ⟨fun h => ihq.1 (hinv h).2, fun h => ihq.2 (fun hq => h (D_mul1 q hq))⟩
      · exact ⟨fun h => by have := (hinv h).1; omega, fun _ => X2 q⟩
      · exact ⟨fun h => by have := (hinv h).1; omega, fun _ => X3 q⟩
      · exact ⟨fun h => by have := (hinv h).1; omega, fun _ => X4 q⟩

lemma mod_of_cast (x v : ℕ) (hv : v < 5) (h : (x : ZMod 5) = (v : ZMod 5)) : x % 5 = v := by
  have := (ZMod.natCast_eq_natCast_iff' x v 5).1 h
  omega

theorem part1 (k : ℕ) (hk : 0 < k) (hD : IsSumPow5 k) : a (5 * k) % 5 = 4 := by
  apply mod_of_cast _ 4 (by norm_num)
  have hX := (XD k).1 hD
  unfold X at hX
  rw [val0 k hk, three_m k hk]
  push_cast
  linear_combination 4 * hX

theorem part2 (k : ℕ) (hD : IsSumPow5 k) : a (5 * k + 1) % 5 = 2 := by
  apply mod_of_cast _ 2 (by norm_num)
  have hX := (XD k).1 hD
  unfold X at hX
  rw [val1 k]
  push_cast
  linear_combination 2 * hX

theorem part3 (n : ℕ) (hn : 0 < n)
    (h : ¬ ∃ k : ℕ, IsSumPow5 k ∧ (n = 5 * k ∨ n - 1 = 5 * k)) : a n % 5 = 0 := by
  apply mod_of_cast _ 0 (by norm_num)
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 5 ∧ n = 5 * q + r :=
    ⟨n / 5, n % 5, Nat.mod_lt _ (by norm_num), by omega⟩
  interval_cases r
  · rw [add_zero] at h hn ⊢
    have hq : 0 < q := by omega
    have hnD : ¬ IsSumPow5 q := fun hD => h ⟨q, hD, Or.inl rfl⟩
    have hX := (XD q).2 hnD
    unfold X at hX
    rw [val0 q hq, three_m q hq]
    push_cast
    linear_combination 4 * hX
  · have hnD : ¬ IsSumPow5 q := fun hD => h ⟨q, hD, Or.inr (by omega)⟩
    have hX := (XD q).2 hnD
    unfold X at hX
    rw [val1 q]
    push_cast
    linear_combination 2 * hX
  · rw [val2]; simp
  · rw [val3]; simp
  · rw [val4]; simp

end OMA.A365771

theorem OMA.solution : type_of% @OMA.S_oeis_a365771.main :=
  ⟨fun k hk hD => OMA.A365771.part1 k hk hD, fun k _ hD => OMA.A365771.part2 k hD,
    fun n hn h => OMA.A365771.part3 n hn h⟩
