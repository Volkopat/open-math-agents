import OMAStatements.S_oeis_a340991
import Mathlib

/-
A340991: the row polynomial of the convolution triangle satisfies R(m+1) = X * rec(m, 0), for
every weight sequence w over every commutative semiring (the listed weight is one instance).

The definitions enter only through their defining equations, so the lemmas are stated for
arbitrary functions conv and rec satisfying them.
- conv_zero: conv(k, n) = 0 for n < k (the weights start at index 1).
- recForm: rec(m, p) = sum over k <= m of C(sum over i <= m of conv(k, i) w(m + p + 1 - i)) X^k,
  by induction on m. In the step, the inner sum at p = 0 is conv(k+1, m+1) by definition, the
  term k = m + 1 vanishes by conv_zero, and conv(0, m+1) = 0.
- At p = 0 this gives the claim after shifting the index k by one.
-/

namespace OMA.P340991

open Finset Polynomial

lemma conv_zero {S : Type} [CommSemiring S] (w : ℕ → S) (conv : ℕ → ℕ → S)
    (hcs : ∀ k n, conv (k + 1) n = ∑ i ∈ range n, conv k i * w (n - i)) :
    ∀ k n, n < k → conv k n = 0 := by
  intro k
  induction k with
  | zero => intro n hn; omega
  | succ k ih =>
    intro n hn
    rw [hcs]
    exact Finset.sum_eq_zero fun i hi => by
      rw [ih i (by have := mem_range.1 hi; omega), zero_mul]

lemma recForm {S : Type} [CommSemiring S] (w : ℕ → S) (conv : ℕ → ℕ → S)
    (hc0 : ∀ n, conv 0 n = if n = 0 then 1 else 0)
    (hcs : ∀ k n, conv (k + 1) n = ∑ i ∈ range n, conv k i * w (n - i))
    (rec : ℕ → ℕ → S[X]) (hr0 : ∀ p, rec 0 p = C (w (p + 1)))
    (hrs : ∀ m p, rec (m + 1) p = rec m (p + 1) + X * rec m 0 * C (w (p + 1))) :
    ∀ m p, rec m p = ∑ k ∈ range (m + 1),
      C (∑ i ∈ range (m + 1), conv k i * w (m + p + 1 - i)) * X ^ k := by
  intro m
  induction m with
  | zero => intro p; simp [hr0, hc0]
  | succ m ih =>
    intro p
    rw [hrs, ih (p + 1), ih 0]
    have hA : ∀ k, ∑ i ∈ range (m + 1 + 1), conv k i * w (m + 1 + p + 1 - i) =
        (∑ i ∈ range (m + 1), conv k i * w (m + (p + 1) + 1 - i)) + conv k (m + 1) * w (p + 1) := by
      intro k
      rw [Finset.sum_range_succ]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        congr 2
        omega
      · congr 2
        omega
    have hB : ∀ k, ∑ i ∈ range (m + 1), conv k i * w (m + 0 + 1 - i) = conv (k + 1) (m + 1) := by
      intro k
      rw [hcs]
    simp only [hA, hB, map_add, add_mul, Finset.sum_add_distrib]
    congr 1
    · rw [Finset.sum_range_succ _ (m + 1)]
      have h0 : ∑ i ∈ range (m + 1), conv (m + 1) i * w (m + (p + 1) + 1 - i) = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [conv_zero w conv hcs (m + 1) i (mem_range.1 hi), zero_mul]
      rw [h0]
      simp
    · rw [Finset.sum_range_succ' _ (m + 1), hc0 (m + 1), if_neg (Nat.add_one_ne_zero m), zero_mul,
        map_zero, zero_mul, add_zero, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul]
      ring

lemma main' {S : Type} [CommSemiring S] (w : ℕ → S) (conv : ℕ → ℕ → S)
    (hc0 : ∀ n, conv 0 n = if n = 0 then 1 else 0)
    (hcs : ∀ k n, conv (k + 1) n = ∑ i ∈ range n, conv k i * w (n - i))
    (rec : ℕ → ℕ → S[X]) (hr0 : ∀ p, rec 0 p = C (w (p + 1)))
    (hrs : ∀ m p, rec (m + 1) p = rec m (p + 1) + X * rec m 0 * C (w (p + 1))) (m : ℕ) :
    ∑ k ∈ range (m + 1 + 1), C (conv k (m + 1)) * X ^ k = X * rec m 0 := by
  rw [recForm w conv hc0 hcs rec hr0 hrs m 0, Finset.sum_range_succ' _ (m + 1), hc0 (m + 1),
    if_neg (Nat.add_one_ne_zero m), map_zero, zero_mul, add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hcs k (m + 1)]
  simp only [Nat.add_zero]
  ring

end OMA.P340991

theorem OMA.solution : type_of% @OMA.S_oeis_a340991.main :=
  ⟨fun m => OMA.P340991.main' OMA.S_oeis_a340991.givenWeight (OMA.S_oeis_a340991.convolution OMA.S_oeis_a340991.givenWeight) (fun _ => rfl)
      (fun _ _ => rfl) (OMA.S_oeis_a340991.recursion OMA.S_oeis_a340991.givenWeight) (fun _ => rfl) (fun _ _ => rfl) m,
    fun _ _ w m => OMA.P340991.main' w (OMA.S_oeis_a340991.convolution w) (fun _ => rfl) (fun _ _ => rfl)
      (OMA.S_oeis_a340991.recursion w) (fun _ => rfl) (fun _ _ => rfl) m⟩
