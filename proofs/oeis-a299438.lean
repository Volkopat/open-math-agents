import OMAStatements.S_oeis_a299438
import Mathlib

/-!
# OEIS A299438: for every n >= 1 some positive length k admits no k numbers in [1..n] with product equal to sum (so a(n) > 0)

Credit: @Squee451. The proof was found with Claude (claude-fable-5-2) and Codex; the Lean text was
written by Codex.

Outline. Fix n and put K = 2^(4n^2), L = 4n^2 + n. In a representation of a length k <= K let e_i be the
number of entries equal to i, for 2 <= i <= n. The product P equals the sum, which is at most n*k <=
n*K <= 2^L, and 2^(e_i) <= P, so e_i <= L. Also P = k + Sum_{i>=2} (i-1)*e_i, so the tuple (e_2,
..., e_n) determines P = Prod i^(e_i) and then k. Hence at most (L+1)^(n-1) lengths k <= K are
represented, and (L+1)^(n-1) <= 2^(4n(n-1)) < 2^(4n^2) = K, so some length in 1..K is not
represented.
-/

open OMA.S_oeis_a299438

namespace OMA.A299438Proof

-- Count entries by their value minus one; the zero coordinate represents ones.
def count {n k : ℕ} (w : Fin k → Fin n) (i : Fin n) : ℕ :=
  (Finset.univ.filter fun j => w j = i).card

def exponent {n k : ℕ} (w : Fin k → Fin n) (i : Fin n) : ℕ :=
  if i.val = 0 then 0 else count w i

lemma product_counts {n k : ℕ} (w : Fin k → Fin n) :
    ∏ i : Fin n, (i.val + 1) ^ count w i = ∏ j, ((w j).val + 1) := by
  simpa [count] using
    (Finset.prod_fiberwise' Finset.univ w (fun i : Fin n => i.val + 1))

lemma sum_counts {n k : ℕ} (w : Fin k → Fin n) :
    ∑ i : Fin n, i.val * count w i = ∑ j, (w j).val := by
  simpa [count, Nat.mul_comm] using
    (Finset.sum_fiberwise' Finset.univ w (fun i : Fin n => i.val))

lemma product_exponents {n k : ℕ} (w : Fin k → Fin n) :
    ∏ i : Fin n, (i.val + 1) ^ exponent w i = ∏ j, ((w j).val + 1) := by
  rw [← product_counts w]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : i.val = 0 <;> simp [exponent, h]

lemma sum_exponents {n k : ℕ} (w : Fin k → Fin n) :
    ∑ i : Fin n, i.val * exponent w i = ∑ j, (w j).val := by
  rw [← sum_counts w]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h : i.val = 0 <;> simp [exponent, h]

lemma bounded_tuple {n k L : ℕ} (hrep : Represents n k)
    (hbound : n * k ≤ 2 ^ L) :
    ∃ e : Fin n → Fin (L + 1),
      ∏ i : Fin n, (i.val + 1) ^ (e i).val =
        k + ∑ i : Fin n, i.val * (e i).val := by
  classical
  obtain ⟨v, hv, hp⟩ := hrep
  let w : Fin k → Fin n := fun j => ⟨v j - 1, by have := hv j; omega⟩
  have hw (j : Fin k) : (w j).val + 1 = v j := by
    dsimp [w]
    exact Nat.sub_add_cancel (hv j).1
  have heq : ∏ i : Fin n, (i.val + 1) ^ exponent w i =
      k + ∑ i : Fin n, i.val * exponent w i := by
    rw [product_exponents, sum_exponents]
    calc
      ∏ j, ((w j).val + 1) = ∑ j, ((w j).val + 1) := by
        simpa only [hw] using hp
      _ = k + ∑ j, (w j).val := by
        simp [Finset.sum_add_distrib, Nat.add_comm]
  have hprod : ∏ i : Fin n, (i.val + 1) ^ exponent w i ≤ 2 ^ L := by
    rw [product_exponents]
    calc
      ∏ j, ((w j).val + 1) = ∑ j, v j := by simpa only [hw] using hp
      _ ≤ ∑ j : Fin k, n := Finset.sum_le_sum fun j _ => (hv j).2
      _ = n * k := by simp [Nat.mul_comm]
      _ ≤ 2 ^ L := hbound
  have he_bound (i : Fin n) : exponent w i ≤ L := by
    by_cases hi : i.val = 0
    · simp [exponent, hi]
    · apply (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp
      calc
        2 ^ exponent w i ≤ (i.val + 1) ^ exponent w i :=
          Nat.pow_le_pow_left (by omega) _
        _ ≤ ∏ j : Fin n, (j.val + 1) ^ exponent w j := by
          apply Finset.single_le_prod' _ (Finset.mem_univ i)
          intro j hj
          have hpos : 0 < (j.val + 1) ^ exponent w j := pow_pos (by omega) _
          omega
        _ ≤ 2 ^ L := hprod
  exact ⟨fun i => ⟨exponent w i, by have := he_bound i; omega⟩, heq⟩

-- Use K = 2^(4*(n+1)^2) and L = 4*(n+1)^2+n, allowing n coordinates.
lemma tuple_card_bound (n : ℕ) :
    (4 * (n + 1) ^ 2 + n + 1) ^ n < 2 ^ (4 * (n + 1) ^ 2) := by
  have hn : n + 1 ≤ 2 ^ n := Nat.lt_two_pow_self
  have hbase : 4 * (n + 1) ^ 2 + n + 1 ≤ 2 ^ (4 * (n + 1)) := by
    calc
      4 * (n + 1) ^ 2 + n + 1 ≤ 8 * (n + 1) ^ 2 := by nlinarith
      _ ≤ 8 * (2 ^ n) ^ 2 := by gcongr
      _ = 2 ^ (2 * n + 3) := by
        rw [Nat.mul_comm 2 n, pow_add, pow_mul]
        ring
      _ ≤ 2 ^ (4 * (n + 1)) := Nat.pow_le_pow_right (by decide) (by omega)
  calc
    (4 * (n + 1) ^ 2 + n + 1) ^ n ≤ (2 ^ (4 * (n + 1))) ^ n :=
      Nat.pow_le_pow_left hbase n
    _ = 2 ^ (4 * (n + 1) * n) := (pow_mul _ _ _).symm
    _ < 2 ^ (4 * (n + 1) ^ 2) := Nat.pow_lt_pow_right (by decide) (by nlinarith)

end OMA.A299438Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a299438.main := by
  classical
  intro n hn
  by_contra h
  push Not at h
  let K := 2 ^ (4 * (n + 1) ^ 2)
  let L := 4 * (n + 1) ^ 2 + n
  have hbound (j : Fin K) : n * (j.val + 1) ≤ 2 ^ L := by
    calc
      n * (j.val + 1) ≤ n * K := Nat.mul_le_mul_left n (by omega)
      _ ≤ 2 ^ n * K := Nat.mul_le_mul_right K (Nat.le_of_lt Nat.lt_two_pow_self)
      _ = 2 ^ L := by simp [K, L, pow_add, Nat.mul_comm]
  have ht (j : Fin K) := OMA.A299438Proof.bounded_tuple (h (j.val + 1) (by omega)) (hbound j)
  choose e he using ht
  have hinj : Function.Injective e := by
    intro a b hab
    have ha := he a
    have hb := he b
    rw [hab] at ha
    apply Fin.ext
    omega
  have hcard : K ≤ (L + 1) ^ n := by
    simpa using Fintype.card_le_of_injective e hinj
  have hlt : (L + 1) ^ n < K := OMA.A299438Proof.tuple_card_bound n
  omega

