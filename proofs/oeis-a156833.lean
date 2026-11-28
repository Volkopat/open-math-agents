import OMAStatements.S_oeis_a156833
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Positivity needed for OEIS A156833

For k >= 2 and r >= 1, prove that the integer
  Q(k,r) = sum_{m | r} mu(r/m) * choose(m+k-2,k-1)
is strictly positive.

The proof uses Dirichlet convolution. Multiplication of a sequence by its
index becomes convolution with Euler's totient after Mobius inversion.
Induction proves positivity for rising factorials; division by the positive
factorial gives the binomial coefficient result.

Original sequence and conjecture: https://oeis.org/A156833
This module introduces no additional axioms or admitted proofs.
-/

namespace A156833Positivity
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

abbrev AF := ArithmeticFunction ℚ
def ident : AF := ⟨fun n => n, by simp⟩
def phi : AF := ⟨fun n => n.totient, by simp⟩
def twist (f : AF) : AF := ⟨fun n => (n : ℚ) * f n, by simp⟩

@[simp] lemma ident_apply (n : ℕ) : ident n = n := rfl
@[simp] lemma phi_apply (n : ℕ) : phi n = n.totient := rfl
@[simp] lemma twist_apply (f : AF) (n : ℕ) : twist f n = n * f n := rfl

lemma twist_mul (f g : AF) : twist (f * g) = twist f * twist g := by
  ext n
  simp only [twist_apply, ArithmeticFunction.mul_apply, Finset.mul_sum]
  apply sum_congr rfl
  intro x hx
  have he := (Nat.mem_divisorsAntidiagonal.mp hx).1
  rw [← he, Nat.cast_mul]
  ring

lemma twist_zeta : twist (ζ : AF) = ident := by
  ext n
  by_cases hn : n = 0 <;> simp [twist, ident, hn]

lemma zeta_phi : (ζ : AF) * phi = ident := by
  ext n
  rw [coe_zeta_mul_apply]
  simp only [phi_apply, ident_apply]
  exact_mod_cast Nat.sum_totient n

lemma moebius_ident : (μ : AF) * ident = phi := by
  rw [← zeta_phi, ← mul_assoc, coe_moebius_mul_coe_zeta, one_mul]

lemma moebius_twist (f : AF) :
    (μ : AF) * twist f = phi * twist ((μ : AF) * f) := by
  have hf : f = (ζ : AF) * ((μ : AF) * f) := by
    rw [← mul_assoc, coe_zeta_mul_coe_moebius, one_mul]
  calc
    (μ : AF) * twist f = (μ : AF) * twist ((ζ : AF) * ((μ : AF) * f)) :=
      congrArg (fun a => (μ : AF) * twist a) hf
    _ = phi * twist ((μ : AF) * f) := by
      rw [twist_mul, twist_zeta, ← mul_assoc, moebius_ident]

lemma convolution_nonneg {f g : AF}
    (hf : ∀ n, 0 ≤ f n) (hg : ∀ n, 0 ≤ g n) (n : ℕ) : 0 ≤ (f*g) n := by
  rw [ArithmeticFunction.mul_apply]
  exact sum_nonneg fun x _ => mul_nonneg (hf x.1) (hg x.2)

lemma phi_twist_pos {f : AF} (hf : ∀ n, 0 ≤ f n) {n : ℕ}
    (hn : 0 < n) (hfn : 0 < f n) : 0 < (phi * twist f) n := by
  rw [ArithmeticFunction.mul_apply]
  have hm : (1,n) ∈ n.divisorsAntidiagonal := by
    simp [Nat.mem_divisorsAntidiagonal, hn.ne']
  have hle := single_le_sum
    (s := n.divisorsAntidiagonal)
    (f := fun x : ℕ × ℕ => phi x.1 * twist f x.2)
    (fun x _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hf _))) hm
  have hpos : 0 < phi 1 * twist f n := by
    simp only [phi_apply, Nat.totient_one, Nat.cast_one, twist_apply, one_mul]
    exact mul_pos (Nat.cast_pos.mpr hn) hfn
  exact lt_of_lt_of_le hpos hle

def rising (k : ℕ) : AF :=
  ⟨fun n => if n = 0 then 0 else (n.ascFactorial k : ℚ), by simp⟩

lemma rising_zero : rising 0 = (ζ : AF) := by
  ext n
  by_cases hn : n = 0 <;> simp [rising, hn]

lemma rising_succ (k : ℕ) : rising (k+1) = twist (rising k) + (k : ℚ) • rising k := by
  ext n
  by_cases hn : n = 0
  · simp [hn]
  · change (if n = 0 then (0 : ℚ) else ↑(n.ascFactorial (k+1))) =
      (n : ℚ) * (if n = 0 then 0 else ↑(n.ascFactorial k)) +
      (k : ℚ) * (if n = 0 then 0 else ↑(n.ascFactorial k))
    simp only [if_neg hn, Nat.ascFactorial_succ, Nat.cast_mul, Nat.cast_add]
    ring

lemma rising_one : rising 1 = ident := by
  ext n
  by_cases hn : n = 0 <;> simp [rising, ident, hn, Nat.ascFactorial_succ]

lemma mob_rising_succ (k : ℕ) :
    (μ : AF) * rising (k+1) =
      phi * twist ((μ : AF) * rising k) + (k : ℚ) • ((μ : AF) * rising k) := by
  rw [rising_succ, mul_add, moebius_twist, mul_smul_comm]

theorem mob_rising_nonneg (k n : ℕ) : 0 ≤ ((μ : AF) * rising k) n := by
  induction k generalizing n with
  | zero =>
      rw [rising_zero, coe_moebius_mul_coe_zeta]
      simp only [one_apply]
      split <;> norm_num
  | succ k ih =>
      rw [mob_rising_succ, add_apply]
      apply add_nonneg
      · exact convolution_nonneg (fun n => Nat.cast_nonneg _) (fun n =>
          mul_nonneg (Nat.cast_nonneg _) (ih n)) n
      · simpa only [smul_map, smul_eq_mul] using mul_nonneg (Nat.cast_nonneg k : (0:ℚ) ≤ k) (ih n)

theorem mob_rising_pos (k n : ℕ) (hk : 0 < k) (hn : 0 < n) :
    0 < ((μ : AF) * rising k) n := by
  induction k with
  | zero => omega
  | succ k ih =>
      by_cases hk0 : k = 0
      · subst k
        rw [rising_one, moebius_ident]
        simp only [phi_apply]
        exact_mod_cast Nat.totient_pos.mpr hn
      · rw [mob_rising_succ, add_apply]
        apply add_pos_of_pos_of_nonneg
        · exact phi_twist_pos (mob_rising_nonneg k) hn (ih (Nat.pos_of_ne_zero hk0))
        · simpa only [smul_map, smul_eq_mul] using
            mul_nonneg (Nat.cast_nonneg k : (0:ℚ) ≤ k) (mob_rising_nonneg k n)


def binomial (s : ℕ) : AF :=
  ⟨fun n => if n = 0 then 0 else ((n+s-1).choose s : ℚ), by simp⟩

lemma rising_eq_factorial_binomial (s : ℕ) :
    rising s = (s.factorial : ℚ) • binomial s := by
  ext n
  change (if n = 0 then (0 : ℚ) else ↑(n.ascFactorial s)) =
    (s.factorial : ℚ) * (if n = 0 then 0 else ↑((n+s-1).choose s))
  by_cases hn : n = 0
  · simp [hn]
  · simp only [if_neg hn]
    exact_mod_cast Nat.ascFactorial_eq_factorial_mul_choose' n s

theorem mob_binomial_pos (s n : ℕ) (hs : 0 < s) (hn : 0 < n) :
    0 < ((μ : AF) * binomial s) n := by
  have h := mob_rising_pos s n hs hn
  rw [rising_eq_factorial_binomial, mul_smul_comm, smul_map, smul_eq_mul] at h
  exact (mul_pos_iff.mp h).resolve_right (fun h' => (not_lt_of_ge (Nat.cast_nonneg _)) h'.1) |>.2

def Q (k r : ℕ) : ℤ :=
  ∑ m ∈ r.divisors, μ (r/m) * ((m+k-2).choose (k-1) : ℤ)

lemma Q_cast_eq (k r : ℕ) (hk : 2 ≤ k) :
    (Q k r : ℚ) = ((μ : AF) * binomial (k-1)) r := by
  rw [ArithmeticFunction.mul_apply]
  rw [Nat.sum_divisorsAntidiagonal' (fun x y => ((μ : AF) x) * binomial (k-1) y)]
  unfold Q
  push_cast
  apply sum_congr rfl
  intro m hm
  have hm0 : m ≠ 0 := (Nat.pos_of_mem_divisors hm).ne'
  have he : m + (k-1) - 1 = m+k-2 := by omega
  simp [binomial, hm0, he]

theorem Q_pos (k r : ℕ) (hk : 2 ≤ k) (hr : 0 < r) : 0 < Q k r := by
  have h := mob_binomial_pos (k-1) r (by omega) hr
  rw [← Q_cast_eq k r hk] at h
  exact_mod_cast h

theorem Q_one_right (k : ℕ) (hk : 0 < k) : Q k 1 = 1 := by
  have he : 1 + k - 2 = k - 1 := by omega
  simp [Q, he]

theorem Q_one_left (r : ℕ) (hr : 1 < r) : Q 1 r = 0 := by
  have h : (∑ m ∈ r.divisors, μ m) = 0 := by
    have he := congrArg (fun f : ArithmeticFunction ℤ => f r) moebius_mul_coe_zeta
    rw [coe_mul_zeta_apply] at he
    simpa [one_apply, ne_of_gt hr] using he
  simpa [Q, Nat.sum_div_divisors] using h

end A156833Positivity


/-!
# OEIS A156833: equality with n characterizes primes

The definitions below are the divisor-sum expansion of the original
lower-triangular matrix definition A054525 * A156348 * [1,2,3,...].
See https://oeis.org/A156833 and its Mathematica definitions.

The complete theorem is `A156833Main.main`. For every natural n > 1,
the exact sequence a(n) equals n if and only if n is prime. The stronger
inequality a(n) > n for every composite n > 1 is also proved.
-/

namespace A156833Main
open Finset Nat ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta
open A156833Positivity
open OMA.S_oeis_a156833 (a b)

lemma triple_swap (n : ℕ) (f : ℕ → ℕ → ℕ → ℤ) :
    (∑ x ∈ n.divisorsAntidiagonal,
      ∑ y ∈ x.2.divisorsAntidiagonal, f x.1 y.1 y.2) =
    (∑ x ∈ n.divisorsAntidiagonal,
      ∑ y ∈ x.2.divisorsAntidiagonal, f y.1 x.1 y.2) := by
  simp only [sum_sigma']
  apply sum_nbij' (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ => ⟨(k, i*l), (i,l)⟩)
    (fun ⟨⟨i, _j⟩, ⟨k, l⟩⟩ => ⟨(k, i*l), (i,l)⟩) <;>
    aesop (add simp [Nat.mem_divisorsAntidiagonal, mul_assoc, mul_left_comm])

lemma b_antidiagonal (n : ℕ) : b n =
    ∑ y ∈ n.divisorsAntidiagonal,
      (y.1 : ℤ) * ((y.2+y.1-2).choose (y.1-1) : ℤ) := by
  rw [Nat.sum_divisorsAntidiagonal (fun k m =>
    (k : ℤ) * ((m+k-2).choose (k-1) : ℤ))]
  rfl

lemma a_antidiagonal (n : ℕ) : a n =
    ∑ x ∈ n.divisorsAntidiagonal,
      ∑ y ∈ x.2.divisorsAntidiagonal,
        μ x.1 * ((y.1 : ℤ) * ((y.2+y.1-2).choose (y.1-1) : ℤ)) := by
  unfold a
  rw [← Nat.sum_divisorsAntidiagonal' (fun i j => μ i * b j)]
  apply sum_congr rfl
  intro x hx
  rw [b_antidiagonal, Finset.mul_sum]

theorem a_eq_sum_Q (n : ℕ) :
    a n = ∑ k ∈ n.divisors, (k : ℤ) * Q k (n/k) := by
  rw [a_antidiagonal,
    triple_swap n (fun i k m => μ i * ((k : ℤ) * ((m+k-2).choose (k-1) : ℤ)))]
  rw [Nat.sum_divisorsAntidiagonal (fun k r =>
    ∑ y ∈ r.divisorsAntidiagonal,
      μ y.1 * ((k : ℤ) * ((y.2+k-2).choose (k-1) : ℤ)))]
  apply sum_congr rfl
  intro k hk
  rw [Nat.sum_divisorsAntidiagonal' (fun i m =>
    μ i * ((k : ℤ) * ((m+k-2).choose (k-1) : ℤ)))]
  unfold Q
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro m hm
  ring

lemma contribution_nonneg {n k : ℕ} (hn : 1 < n) (hk : k ∈ n.divisors) :
    0 ≤ (k : ℤ) * Q k (n/k) := by
  have hkpos := Nat.pos_of_mem_divisors hk
  have hkn := Nat.le_of_dvd (by omega : 0 < n) (Nat.dvd_of_mem_divisors hk)
  have hr : 0 < n/k := Nat.div_pos hkn hkpos
  by_cases hk1 : k = 1
  · subst k
    simp [Q_one_left n hn]
  · have hk2 : 2 ≤ k := by omega
    exact mul_nonneg (Nat.cast_nonneg _) (le_of_lt (Q_pos k (n/k) hk2 hr))

theorem prime_implies_a_eq {p : ℕ} (hp : p.Prime) : a p = p := by
  rw [a_eq_sum_Q, hp.sum_divisors]
  simp [Q_one_left p hp.one_lt, Q_one_right p hp.pos, Nat.div_self hp.pos]

theorem composite_strict {n : ℕ} (hn : 1 < n) (hcomp : ¬ n.Prime) :
    (n : ℤ) < a n := by
  obtain ⟨k, hkdvd, hk2, hkn⟩ := Nat.exists_dvd_of_not_prime2 (by omega) hcomp
  have hnpos : 0 < n := by omega
  have hnmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hnpos.ne'⟩
  have hkmem : k ∈ n.divisors := Nat.mem_divisors.mpr ⟨hkdvd, hnpos.ne'⟩
  have hke : k ∈ n.divisors.erase n := mem_erase.mpr ⟨_root_.ne_of_lt hkn, hkmem⟩
  have hkpos : 0 < k := by omega
  have hr : 0 < n/k := Nat.div_pos (le_of_lt hkn) hkpos
  have hterm : 0 < (k : ℤ) * Q k (n/k) :=
    mul_pos (Nat.cast_pos.mpr hkpos) (Q_pos k (n/k) hk2 hr)
  have hrest : 0 < ∑ j ∈ n.divisors.erase n, (j : ℤ) * Q j (n/j) := by
    exact sum_pos' (fun j hj => contribution_nonneg hn (mem_of_mem_erase hj))
      ⟨k, hke, hterm⟩
  rw [a_eq_sum_Q, ← sum_erase_add _ _ hnmem]
  simp only [Nat.div_self hnpos, Q_one_right n hnpos, mul_one]
  omega

theorem main (n : ℕ) (hn : 1 < n) : a n = (n : ℤ) ↔ n.Prime := by
  constructor
  · intro h
    by_contra hcomp
    have hs := composite_strict hn hcomp
    omega
  · exact prime_implies_a_eq


end A156833Main

theorem OMA.solution : type_of% @OMA.S_oeis_a156833.main := A156833Main.main
