import OMAStatements.S_oeis_a214923

/-!
The low binary digits of the Fibonacci sequence contribute a bias of minus two-thirds
per term over complete periods. Bits above the fifth balance over their own periods:
three Fibonacci index classes have different shifts that flip the bit. The reduction
compares the remaining digits with the exact threshold, including the incomplete period.
-/

open Finset Set
open OMA.S_oeis_a214923

namespace OMA.R_oeis_a214923_R1

private theorem fib_mod32_periodic : Function.Periodic (fun n => Nat.fib n % 32) 48 := by
  intro n
  dsimp
  have h := Nat.fib_add 47 n
  rw [show 47 + n + 1 = n + 48 by omega] at h
  rw [h, Nat.add_mod, Nat.mul_mod (Nat.fib 47), Nat.mul_mod (Nat.fib (47 + 1))]
  rw [show Nat.fib 47 % 32 = 1 by decide +kernel,
    show Nat.fib (47 + 1) % 32 = 0 by decide +kernel]
  simp

private theorem fib_shift_coeff (e : ℕ) :
    ∃ A B : ℕ, A % 8 = 7 ∧ B % 8 = 2 ∧ ∀ n : ℕ,
      Nat.fib (n + 24 * 2 ^ e) =
        Nat.fib n + 16 * 2 ^ e * (A * Nat.fib n + B * Nat.fib (n + 1)) := by
  induction e with
  | zero =>
    refine ⟨1791, 2898, by decide, by decide, ?_⟩
    intro n
    have h := Nat.fib_add 23 n
    rw [show 23 + n + 1 = n + 24 by omega,
      show Nat.fib 23 = 28657 by decide +kernel,
      show Nat.fib (23 + 1) = 46368 by decide +kernel] at h
    simp only [pow_zero, mul_one, h]
    ring
  | succ e ih =>
    obtain ⟨A, B, hA, hB, hshift⟩ := ih
    refine ⟨A + (2 ^ e * (A ^ 2 + B ^ 2)) * 8, B + (2 ^ e * (2 * A * B + B ^ 2)) * 8,
      by simpa only [Nat.add_mul_mod_self_right] using hA,
      by simpa only [Nat.add_mul_mod_self_right] using hB, ?_⟩
    intro n
    rw [pow_succ, show n + 24 * (2 ^ e * 2) = n + 24 * 2 ^ e + 24 * 2 ^ e by ring,
      hshift, show n + 24 * 2 ^ e + 1 = n + 1 + 24 * 2 ^ e by omega,
      hshift n, hshift (n + 1), Nat.fib_add_two]
    ring

private theorem fib_mod8_periodic : Function.Periodic (fun n => Nat.fib n % 8) 24 := by
  obtain ⟨A, B, _, _, h⟩ := fib_shift_coeff 0
  intro n
  dsimp
  have hh := h n
  simp only [pow_zero, mul_one] at hh
  rw [hh, show 16 * (A * Nat.fib n + B * Nat.fib (n + 1)) =
    (2 * (A * Nat.fib n + B * Nat.fib (n + 1))) * 8 by ring]
  exact Nat.add_mul_mod_self_right _ _ _

private theorem coeff_mod8 (A B n : ℕ) (hA : A % 8 = 7) (hB : B % 8 = 2) :
    let C := A * Nat.fib n + B * Nat.fib (n + 1)
    (n % 3 ≠ 0 → C % 2 = 1) ∧ (n % 6 = 0 → C % 4 = 2) ∧ (n % 6 = 3 → C % 8 = 4) := by
  let C := A * Nat.fib n + B * Nat.fib (n + 1)
  let r : Fin 24 := ⟨n % 24, Nat.mod_lt _ (by decide)⟩
  have hrem : ∀ r : Fin 24,
      let R := (7 * (Nat.fib r.val % 8) + 2 * (Nat.fib (r.val + 1) % 8)) % 8
      (r.val % 3 ≠ 0 → R % 2 = 1) ∧ (r.val % 6 = 0 → R % 4 = 2) ∧
        (r.val % 6 = 3 → R = 4) := by decide +kernel
  have hF := fib_mod8_periodic.nat_mul (n / 24) r.val
  have hG := fib_mod8_periodic.nat_mul (n / 24) (r.val + 1)
  change Nat.fib (r.val + n / 24 * 24) % 8 = Nat.fib r.val % 8 at hF
  change Nat.fib (r.val + 1 + n / 24 * 24) % 8 = Nat.fib (r.val + 1) % 8 at hG
  rw [show r.val + n / 24 * 24 = n by dsimp [r]; omega] at hF
  rw [show r.val + 1 + n / 24 * 24 = n + 1 by dsimp [r]; omega] at hG
  have hC : C % 8 = (7 * (Nat.fib r.val % 8) + 2 * (Nat.fib (r.val + 1) % 8)) % 8 := by
    dsimp [C]
    rw [Nat.add_mod, Nat.mul_mod A, Nat.mul_mod B, hA, hB, hF, hG,
      Nat.mod_add_mod, Nat.add_mod_mod]
  obtain ⟨hp, hq, ht⟩ := hrem r
  change (n % 3 ≠ 0 → C % 2 = 1) ∧ (n % 6 = 0 → C % 4 = 2) ∧ (n % 6 = 3 → C % 8 = 4)
  rw [← hC] at hp hq ht
  dsimp [r] at hp hq ht
  omega

/- Flipping one bit reverses its signed contribution. -/
private theorem bit_flip (m x y : ℕ) (hm : 0 < m) (hy : y % 2 = 1) :
    (2 * (((x + m * y) / m % 2 : ℕ) : ℤ) - 1) = -(2 * ((x / m % 2 : ℕ) : ℤ) - 1) := by
  rw [Nat.add_mul_div_left x y hm]
  omega

private theorem balance_binary_step (x : ℕ) (hx : 0 < x / 2) :
    balance x = balance (x / 2) + (2 * ((x % 2 : ℕ) : ℤ) - 1) := by
  have hx0 : x ≠ 0 := by omega
  rw [balance, if_neg hx0, balance, if_neg hx.ne',
    Nat.digits_eq_cons_digits_div (by decide : 1 < (2 : ℕ)) hx0]
  rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [h] <;> omega

/-- Removing a low block of bits leaves the balance of the quotient. -/
private theorem balance_split (m x : ℕ) (hx : 0 < x / 2 ^ m) :
    balance x = balance (x / 2 ^ m) +
      ∑ j ∈ range m, (2 * ((x / 2 ^ j % 2 : ℕ) : ℤ) - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hdiv : x / 2 ^ (m + 1) = (x / 2 ^ m) / 2 := by
      rw [pow_succ, Nat.div_div_eq_div_mul]
    have hpos : 0 < x / 2 ^ m := by rw [hdiv] at hx; omega
    rw [ih hpos, balance_binary_step (x / 2 ^ m) (hdiv ▸ hx), hdiv, sum_range_succ]
    ring

private theorem low_five_periodic : Function.Periodic
    (fun n => ∑ j ∈ range 5, (2 * ((Nat.fib n / 2 ^ j % 2 : ℕ) : ℤ) - 1)) 48 := by
  intro n
  apply sum_congr rfl
  intro j hj
  have hmod := fib_mod32_periodic n
  change Nat.fib (n + 48) % 32 = Nat.fib n % 32 at hmod
  have hj' := mem_range.mp hj
  have heq : Nat.fib (n + 48) / 2 ^ j % 2 = Nat.fib n / 2 ^ j % 2 := by
    interval_cases j <;> norm_num at * <;> omega
  rw [heq]

private theorem sum_of_periods (f : ℕ → ℤ) {T : ℕ} (hf : Function.Periodic f T) (q : ℕ) :
    (∑ k ∈ range (q * T), f k) = (q : ℤ) * ∑ k ∈ range T, f k := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Nat.succ_mul, sum_range_add, ih]
    have hshift : (∑ k ∈ range T, f (q * T + k)) = ∑ k ∈ range T, f k := by
      apply sum_congr rfl
      intro k _
      rw [Nat.add_comm]
      exact hf.nat_mul q k
    rw [hshift]
    push_cast
    ring

private theorem anti_period_sum (f : ℕ → ℤ) (s q : ℕ)
    (hf : ∀ n, f (n + s) = -f n) :
    (∑ k ∈ range (q * (2 * s)), f k) = 0 := by
  have hp : Function.Periodic f (2 * s) := by
    intro n
    rw [show n + 2 * s = n + s + s by omega, hf, hf, neg_neg]
  have hblock : (∑ k ∈ range (2 * s), f k) = 0 := by
    rw [two_mul, sum_range_add]
    have hsum : (∑ k ∈ range s, f (s + k)) = -∑ k ∈ range s, f k := by
      rw [← sum_neg_distrib]
      exact sum_congr rfl (fun k _ => by rw [Nat.add_comm, hf])
    rw [hsum, add_neg_cancel]
  rw [sum_of_periods f hp, hblock, mul_zero]

private theorem high_bit_group_sum (e d off : ℕ) (hd : d ≤ 2) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ n, P (n + 24 * 2 ^ (e + (2 - d))) ↔ P n)
    (hc : ∀ A B n : ℕ, A % 8 = 7 → B % 8 = 2 → P n →
      (A * Nat.fib n + B * Nat.fib (n + 1)) % (2 * 2 ^ d) = 2 ^ d) :
    (∑ k ∈ range (3 * 2 ^ (e + 6)), if P (k + off) then
      2 * ((Nat.fib (k + off) / 2 ^ (e + 6) % 2 : ℕ) : ℤ) - 1 else 0) = 0 := by
  let s := 24 * 2 ^ (e + (2 - d))
  let f (k : ℕ) : ℤ := if P (k + off) then
    2 * ((Nat.fib (k + off) / 2 ^ (e + 6) % 2 : ℕ) : ℤ) - 1 else 0
  obtain ⟨A, B, hA, hB, hs⟩ := fib_shift_coeff (e + (2 - d))
  have hp : ∀ k, f (k + s) = -f k := by
    intro k
    have harg : k + s + off = k + off + s := by omega
    unfold f
    rw [harg]
    by_cases hg : P (k + off)
    · rw [if_pos ((hP (k + off)).mpr hg), if_pos hg]
      let C := A * Nat.fib (k + off) + B * Nat.fib (k + off + 1)
      have hC := hc A B (k + off) hA hB hg
      change C % (2 * 2 ^ d) = 2 ^ d at hC
      have hdiv : C = 2 ^ d * (C / 2 ^ d) := by
        interval_cases d <;> norm_num at hC ⊢ <;> omega
      have hodd : C / 2 ^ d % 2 = 1 := by
        interval_cases d <;> norm_num at hC ⊢ <;> omega
      have hexp : 16 * 2 ^ (e + (2 - d)) * 2 ^ d = 2 ^ (e + 6) := by
        rw [pow_add, pow_add]
        interval_cases d <;> norm_num <;> ring
      have hstep := hs (k + off)
      change Nat.fib (k + off + s) = Nat.fib (k + off) + 16 * 2 ^ (e + (2 - d)) * C at hstep
      rw [hstep, hdiv, ← mul_assoc, hexp]
      exact bit_flip _ _ _ (by positivity) hodd
    · have hg' : ¬ P (k + off + s) := fun h => hg ((hP (k + off)).mp h)
      simp [hg, hg']
  have hperiod : 3 * 2 ^ (e + 6) = 2 ^ d * (2 * s) := by
    dsimp [s]
    rw [pow_add, pow_add]
    interval_cases d <;> norm_num <;> ring
  rw [hperiod]
  exact anti_period_sum f s (2 ^ d) hp

private theorem high_bit_cycle (e off : ℕ) :
    (∑ k ∈ range (3 * 2 ^ (e + 6)),
      (2 * ((Nat.fib (k + off) / 2 ^ (e + 6) % 2 : ℕ) : ℤ) - 1)) = 0 := by
  have h0 := high_bit_group_sum e 0 off (by decide) (fun n => n % 3 ≠ 0)
    (by intro n; let h := 2 ^ (e + (2 - 0)); change ((n + 24 * h) % 3 ≠ 0) ↔ n % 3 ≠ 0; omega)
    (fun A B n hA hB hn => (coeff_mod8 A B n hA hB).1 hn)
  have h1 := high_bit_group_sum e 1 off (by decide) (fun n => n % 6 = 0)
    (by intro n; let h := 2 ^ (e + (2 - 1)); change ((n + 24 * h) % 6 = 0) ↔ n % 6 = 0; omega)
    (fun A B n hA hB hn => (coeff_mod8 A B n hA hB).2.1 hn)
  have h2 := high_bit_group_sum e 2 off (by decide) (fun n => n % 6 = 3)
    (by intro n; let h := 2 ^ (e + (2 - 2)); change ((n + 24 * h) % 6 = 3) ↔ n % 6 = 3; omega)
    (fun A B n hA hB hn => (coeff_mod8 A B n hA hB).2.2 hn)
  let f (k : ℕ) : ℤ := 2 * ((Nat.fib (k + off) / 2 ^ (e + 6) % 2 : ℕ) : ℤ) - 1
  let T := 3 * 2 ^ (e + 6)
  calc
    (∑ k ∈ range T, f k) =
        (∑ k ∈ range T, if (k + off) % 3 ≠ 0 then f k else 0) +
        (∑ k ∈ range T, if (k + off) % 6 = 0 then f k else 0) +
        (∑ k ∈ range T, if (k + off) % 6 = 3 then f k else 0) := by
      rw [← sum_add_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro k _
      by_cases h : (k + off) % 3 = 0
      · rcases (show (k + off) % 6 = 0 ∨ (k + off) % 6 = 3 by omega) with h' | h' <;>
          simp [h, h']
      · have h' : (k + off) % 6 ≠ 0 := by omega
        have h'' : (k + off) % 6 ≠ 3 := by omega
        simp [h, h', h'']
    _ = 0 := by
      dsimp only [f, T]
      rw [h0, h1, h2, add_zero, add_zero]

private theorem bit_periodic (e : ℕ) : Function.Periodic
    (fun n => (2 * ((Nat.fib n / 2 ^ (e + 3) % 2 : ℕ) : ℤ) - 1)) (3 * 2 ^ (e + 3)) := by
  obtain ⟨A, B, _, _, hs⟩ := fib_shift_coeff e
  intro n
  have hb : Nat.fib (n + 3 * 2 ^ (e + 3)) / 2 ^ (e + 3) % 2 =
      Nat.fib n / 2 ^ (e + 3) % 2 := by
    rw [show 3 * 2 ^ (e + 3) = 24 * 2 ^ e by rw [pow_add]; ring, hs,
      show 16 * 2 ^ e * (A * Nat.fib n + B * Nat.fib (n + 1)) =
        2 ^ (e + 3) * (2 * (A * Nat.fib n + B * Nat.fib (n + 1))) by rw [pow_add]; ring,
      Nat.add_mul_div_left _ _ (by positivity)]
    omega
  exact congrArg (fun j : ℕ => (2 : ℤ) * j - 1) hb

private theorem sum_shift_period (f : ℕ → ℤ) {T : ℕ} (hf : Function.Periodic f T) (off : ℕ) :
    (∑ k ∈ range T, f (k + off)) = ∑ k ∈ range T, f k := by
  have h₁ := sum_range_add f off T
  have h₂ := sum_range_add f T off
  have ht : (∑ k ∈ range off, f (T + k)) = ∑ k ∈ range off, f k :=
    sum_congr rfl fun k _ => by rw [Nat.add_comm, hf k]
  have ho : (∑ k ∈ range T, f (off + k)) = ∑ k ∈ range T, f (k + off) :=
    sum_congr rfl fun k _ => by rw [Nat.add_comm]
  rw [Nat.add_comm off T, ho] at h₁
  rw [ht] at h₂
  omega

/- Every bit above the lowest five has zero signed sum over its own full period.
   Combining the periods leaves just the bias of the lowest five bits. -/
private theorem low_block (m : ℕ) :
    let f (k : ℕ) : ℤ := ∑ j ∈ range (m + 6), (2 * ((Nat.fib k / 2 ^ j % 2 : ℕ) : ℤ) - 1)
    Function.Periodic f (96 * 2 ^ m) ∧
      (∑ k ∈ range (96 * 2 ^ m), f k) = -64 * (2 : ℤ) ^ m := by
  induction m with
  | zero =>
    constructor
    · intro k
      have h5 := low_five_periodic.nat_mul 2 k
      have h6 := bit_periodic 2 k
      change (∑ j ∈ range 6, (2 * ((Nat.fib (k + 96) / 2 ^ j % 2 : ℕ) : ℤ) - 1)) =
        ∑ j ∈ range 6, (2 * ((Nat.fib k / 2 ^ j % 2 : ℕ) : ℤ) - 1)
      rw [sum_range_succ _ 5, sum_range_succ _ 5]
      exact congrArg₂ (· + ·) h5 h6
    · decide +kernel
  | succ m ih =>
    dsimp only at ih ⊢
    obtain ⟨hf, hsum⟩ := ih
    have hT : 96 * 2 ^ (m + 1) = 2 * (96 * 2 ^ m) := by rw [pow_succ]; ring
    have hperiod : 96 * 2 ^ (m + 1) = 3 * 2 ^ (m + 6) := by
      rw [pow_add, pow_add]
      ring
    have fh := bit_periodic (m + 3)
    rw [show m + 3 + 3 = m + 6 by omega] at fh
    have hnext := high_bit_cycle m 0
    simp only [Nat.add_zero] at hnext
    simp only [show m.succ + 6 = (m + 6) + 1 by omega, sum_range_succ _ (m + 6)]
    constructor
    · intro k
      have hlow := hf.nat_mul 2 k
      change (∑ j ∈ range (m + 6),
          (2 * ((Nat.fib (k + 2 * (96 * 2 ^ m)) / 2 ^ j % 2 : ℕ) : ℤ) - 1)) =
        ∑ j ∈ range (m + 6), (2 * ((Nat.fib k / 2 ^ j % 2 : ℕ) : ℤ) - 1) at hlow
      rw [← hT] at hlow
      rw [← hperiod] at fh
      exact congrArg₂ (· + ·) hlow (fh k)
    · rw [sum_add_distrib, hperiod, hnext, add_zero, ← hperiod,
        hT, sum_of_periods _ hf, hsum, pow_succ]
      push_cast
      ring

private theorem sum_period_prefix (f : ℕ → ℤ) {T : ℕ} (hf : Function.Periodic f T) (n : ℕ) :
    (∑ k ∈ range n, f k) =
      (n / T : ℕ) * (∑ k ∈ range T, f k) + ∑ k ∈ range (n % T), f k := by
  conv_lhs => rw [← Nat.div_add_mod n T, Nat.mul_comm T (n / T), sum_range_add]
  rw [sum_of_periods f hf]
  have hsum : (∑ k ∈ range (n % T), f (n / T * T + k)) = ∑ k ∈ range (n % T), f k :=
    sum_congr rfl fun k _ => by
      rw [Nat.add_comm]
      exact hf.nat_mul (n / T) k
  rw [hsum]

private theorem pow_le_fib (b : ℕ) : 2 ^ b ≤ Nat.fib (2 * b + 1) := by
  induction b with
  | zero => decide
  | succ b ih =>
    rw [pow_succ, show 2 * (b + 1) + 1 = 2 * b + 1 + 2 by omega, Nat.fib_add_two]
    have h := Nat.fib_mono (show 2 * b + 1 ≤ 2 * b + 1 + 1 by omega)
    omega

private theorem exact_split (m n : ℕ) :
    let b := m + 6
    let off := 2 * b + 1
    let T := 96 * 2 ^ m
    a (2 * b + n) =
      (∑ k ∈ range off, balance (Nat.fib k)) +
      (∑ k ∈ range n, balance (Nat.fib (k + off) / 2 ^ b)) -
      64 * (2 : ℤ) ^ m * (n / T : ℕ) +
      ∑ k ∈ range (n % T), ∑ j ∈ range b,
        (2 * ((Nat.fib (k + off) / 2 ^ j % 2 : ℕ) : ℤ) - 1) := by
  dsimp only
  let b := m + 6
  let off := 2 * b + 1
  let T := 96 * 2 ^ m
  let f (k : ℕ) : ℤ := ∑ j ∈ range b, (2 * ((Nat.fib k / 2 ^ j % 2 : ℕ) : ℤ) - 1)
  obtain ⟨hf, hsum⟩ := low_block m
  change Function.Periodic f T at hf
  change (∑ k ∈ range T, f k) = _ at hsum
  have hshift : Function.Periodic (fun k => f (k + off)) T := by
    intro k
    change f (k + T + off) = f (k + off)
    rw [show k + T + off = k + off + T by omega, hf (k + off)]
  have hterm (k : ℕ) : balance (Nat.fib (off + k)) =
      balance (Nat.fib (k + off) / 2 ^ b) + f (k + off) := by
    rw [Nat.add_comm off k]
    have hpow : 2 ^ b ≤ Nat.fib (k + off) :=
      (pow_le_fib b).trans (Nat.fib_mono (Nat.le_add_left off k))
    exact balance_split b _ (Nat.div_pos hpow (by positivity))
  unfold a
  rw [show 2 * b + n + 1 = off + n by dsimp [off]; omega,
    sum_range_add, sum_congr rfl (fun k _ => hterm k), sum_add_distrib,
    sum_period_prefix _ hshift, sum_shift_period f hf, hsum]
  change _ = (∑ k ∈ range off, balance (Nat.fib k)) +
      (∑ k ∈ range n, balance (Nat.fib (k + off) / 2 ^ b)) -
      64 * (2 : ℤ) ^ m * (n / T : ℕ) + ∑ k ∈ range (n % T), f (k + off)
  ring

/-- The retained high digits exceed the computed threshold for arbitrarily large cutoffs. -/
def H1 : Prop :=
  ∀ N : ℕ, ∃ m n : ℕ, N ≤ m ∧ (96 * 2 ^ m) ^ 2 ≤ n ∧
    let b := m + 6
    let off := 2 * b + 1
    let T := 96 * 2 ^ m
    64 * (2 : ℤ) ^ m * (n / T : ℕ) -
      (∑ k ∈ range off, balance (Nat.fib k)) -
      (∑ k ∈ range (n % T), ∑ j ∈ range b,
        (2 * ((Nat.fib (k + off) / 2 ^ j % 2 : ℕ) : ℤ) - 1)) <
      ∑ k ∈ range n, balance (Nat.fib (k + off) / 2 ^ b)

/-- The retained high digits fall below the computed threshold for arbitrarily large cutoffs. -/
def H2 : Prop :=
  ∀ N : ℕ, ∃ m n : ℕ, N ≤ m ∧ (96 * 2 ^ m) ^ 2 ≤ n ∧
    let b := m + 6
    let off := 2 * b + 1
    let T := 96 * 2 ^ m
    (∑ k ∈ range n, balance (Nat.fib (k + off) / 2 ^ b)) <
      64 * (2 : ℤ) ^ m * (n / T : ℕ) -
      (∑ k ∈ range off, balance (Nat.fib k)) -
      ∑ k ∈ range (n % T), ∑ j ∈ range b,
        (2 * ((Nat.fib (k + off) / 2 ^ j % 2 : ℕ) : ℤ) - 1)

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a214923.main := by
  intro hpos hneg
  constructor <;> apply Set.infinite_of_forall_exists_gt
  · intro N
    obtain ⟨m, n, hm, _, h⟩ := hpos N
    refine ⟨2 * (m + 6) + n, ?_, by omega⟩
    change 0 < a (2 * (m + 6) + n)
    rw [exact_split]
    dsimp only at h
    linarith
  · intro N
    obtain ⟨m, n, hm, _, h⟩ := hneg N
    refine ⟨2 * (m + 6) + n, ?_, by omega⟩
    change a (2 * (m + 6) + n) < 0
    rw [exact_split]
    dsimp only at h
    linarith

/-- The two high-digit conditions are also necessary for the original assertion. -/
theorem high_digit_iff : (type_of% @OMA.S_oeis_a214923.main) ↔ H1 ∧ H2 := by
  constructor
  · rintro ⟨hpos, hneg⟩
    constructor
    · intro N
      obtain ⟨k, hk, hlarge⟩ := hpos.exists_gt (2 * (N + 6) + (96 * 2 ^ N) ^ 2)
      let n := k - 2 * (N + 6)
      have heq : k = 2 * (N + 6) + n := by dsimp [n]; omega
      refine ⟨N, n, le_rfl, ?_, ?_⟩
      · omega
      · change 0 < a k at hk
        rw [heq, exact_split] at hk
        dsimp only
        linarith
    · intro N
      obtain ⟨k, hk, hlarge⟩ := hneg.exists_gt (2 * (N + 6) + (96 * 2 ^ N) ^ 2)
      let n := k - 2 * (N + 6)
      have heq : k = 2 * (N + 6) + n := by dsimp [n]; omega
      refine ⟨N, n, le_rfl, ?_, ?_⟩
      · omega
      · change a k < 0 at hk
        rw [heq, exact_split] at hk
        dsimp only
        linarith
  · rintro ⟨hpos, hneg⟩
    exact main hpos hneg

end OMA.R_oeis_a214923_R1
