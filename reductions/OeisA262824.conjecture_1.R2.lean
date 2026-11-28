import FormalConjectures.OEIS.«262824»

/-!
# A finite circle-method reduction for the weighted cubes

On the dyadic block ending at N, each of the four summands is at most N.
Orthogonality modulo 8N therefore detects equality over the naturals.
The comparison scale is one seventh of the square-root scale, corrected by
the local density modulo 504. The two remaining bounds concern disjoint
frequency sets. Only the signed real contribution of the minor arcs matters.

The finite base through 32768 is certified by a kernel-evaluated bitset.
-/
-- Credit: @Pixelstorm44

namespace OMA.R_OeisA262824_conjecture_1_R2

open Finset
open scoped Classical

theorem bitWitness (L : List ℕ) (f : ℕ → ℕ) (seed i : ℕ)
    (h : (L.foldr (fun u acc => (seed <<< f u) ||| acc) 0).testBit i = true) :
    ∃ u, f u ≤ i ∧ seed.testBit (i - f u) = true := by
  induction L with
  | nil => simp at h
  | cons u us ih =>
    simp only [List.foldr_cons, Nat.testBit_lor, Bool.or_eq_true, Nat.testBit_shiftLeft,
      Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.elim (fun p => ⟨u, p⟩) ih

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem small (m n : ℕ) (hm : m ∈ ({3,4,5,6} : Finset ℕ)) (hn : n ≤ 32768) :
    ∃ w x y z : ℕ, n = w^2 + x^3 + 2*y^3 + m*z^3 := by
  let addLayer (count : ℕ) (f : ℕ → ℕ) (seed : ℕ) :=
    (List.range count).foldr (fun u acc => (seed <<< f u) ||| acc) 0
  let squares := addLayer 182 (fun w => w^2) 1
  let first := addLayer 33 (fun x => x^3) squares
  let second := addLayer 26 (fun y => 2*y^3) first
  let allTerms := addLayer 23 (fun z => m*z^3) second
  have checkBits : allTerms % 2^32769 = 2^32769 - 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with rfl | rfl | rfl | rfl <;> decide +kernel
  have hbit := congrArg (fun a : ℕ => a.testBit n) checkBits
  simp only [Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one,
    show decide (n < 32769) = true by simp [show n < 32769 by omega],
    Bool.true_and] at hbit
  obtain ⟨z,hz,bz⟩ := bitWitness _ _ _ _ hbit
  obtain ⟨y,hy,by'⟩ := bitWitness _ _ _ _ bz
  obtain ⟨x,hx,bx⟩ := bitWitness _ _ _ _ by'
  obtain ⟨w,hw,bw⟩ := bitWitness _ _ _ _ bx
  change (1 : ℕ).testBit (n - m*z^3 - 2*y^3 - x^3 - w^2) = true at bw
  have last : n - m*z^3 - 2*y^3 - x^3 - w^2 < 1 := by
    have hb := Nat.testBit_two_pow_sub_one 1 (n - m*z^3 - 2*y^3 - x^3 - w^2)
    change (1 : ℕ).testBit _ = _ at hb
    rw [hb, decide_eq_true_eq] at bw
    exact bw
  exact ⟨w,x,y,z,by omega⟩

theorem detect {Q : ℕ} [NeZero Q] (n : ℕ) (hn : n < Q)
    (s : Finset (ℕ × ℕ × ℕ × ℕ)) (f : (ℕ × ℕ × ℕ × ℕ) → ℕ)
    (bound : ∀ t ∈ s, f t < Q)
    (h : (∑ j : ZMod Q, ∑ t ∈ s, ZMod.stdAddChar
      (j * ((f t : ZMod Q) - (n : ZMod Q)))).re > 0) : ∃ t ∈ s, f t = n := by
  by_contra! none
  rw [sum_comm] at h
  have vanish (t) (ht : t ∈ s) : (∑ j : ZMod Q, ZMod.stdAddChar
      (j * ((f t : ZMod Q) - (n : ZMod Q)))) = 0 := by
    have neq : (f t : ZMod Q) ≠ (n : ZMod Q) := by
      rw [Ne, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (bound t ht), Nat.mod_eq_of_lt hn]
      exact none t ht
    rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar Q), if_neg (sub_ne_zero.mpr neq)]
    simp
  rw [sum_eq_zero vanish] at h
  exact (lt_irrefl 0) h

theorem factor {Q : ℕ} [NeZero Q] (m n : ℕ) (j : ZMod Q)
    (W X Y Z : Finset ℕ) :
    (∑ w ∈ W, ZMod.stdAddChar (j * ((w^2 : ℕ) : ZMod Q))) *
    (∑ x ∈ X, ZMod.stdAddChar (j * ((x^3 : ℕ) : ZMod Q))) *
    (∑ y ∈ Y, ZMod.stdAddChar (j * ((2*y^3 : ℕ) : ZMod Q))) *
    (∑ z ∈ Z, ZMod.stdAddChar (j * ((m*z^3 : ℕ) : ZMod Q))) *
      ZMod.stdAddChar (j * -(n : ZMod Q)) =
    ∑ t ∈ Z ×ˢ (Y ×ˢ (X ×ˢ W)), ZMod.stdAddChar
      (j * (((t.2.2.2^2 + t.2.2.1^3 + 2*t.2.1^3 + m*t.1^3 : ℕ) : ZMod Q) - (n : ZMod Q))) := by
  simp only [sum_product, sum_mul, mul_sum]
  apply sum_congr rfl
  intro last _
  apply sum_congr rfl
  intro third _
  apply sum_congr rfl
  intro second _
  apply sum_congr rfl
  intro first _
  simp only [← AddChar.map_add_eq_mul, Nat.cast_add, ← mul_add, sub_eq_add_neg]

/-- A lower bound for the low-denominator arcs. -/
def H1 : Prop := ∀ m ∈ ({3,4,5,6} : Finset ℕ), ∀ n : ℕ, 32768 < n →
  let k := Nat.clog 2 n
  let N := 2^k
  let Q := 8 * N
  let K := 32 * (k+1)
  let box (c d : ℕ) := (range (N+1)).filter (fun u => c*u^d ≤ N)
  let S (c d : ℕ) (j : ZMod Q) := ∑ u ∈ box c d,
    ZMod.stdAddChar (j * ((c*u^d : ℕ) : ZMod Q))
  let wave (j : ZMod Q) := S 1 2 j * S 1 3 j * S 2 3 j * S m 3 j *
    ZMod.stdAddChar (j * -(n : ZMod Q))
  let major := (univ : Finset (ZMod Q)).filter (fun j =>
    ∃ b ∈ Icc 1 K, ∃ a ≤ b, Nat.dist (b*j.val) (a*Q) ≤ K)
  let localCount := ((univ : Finset (Fin 504 × Fin 504 × Fin 504 × Fin 504)).filter
    (fun t => (t.1.val^2 + t.2.1.val^3 + 2*t.2.2.1.val^3 + m*t.2.2.2.val^3) % 504 =
      n % 504)).card
  let scale : ℝ := Q * Real.sqrt n * localCount / (7 * 504^3)
  scale < (∑ j ∈ major, wave j).re

/-- A one-sided cancellation bound off the low-denominator arcs. -/
def H2 : Prop := ∀ m ∈ ({3,4,5,6} : Finset ℕ), ∀ n : ℕ, 32768 < n →
  let k := Nat.clog 2 n
  let N := 2^k
  let Q := 8 * N
  let K := 32 * (k+1)
  let box (c d : ℕ) := (range (N+1)).filter (fun u => c*u^d ≤ N)
  let S (c d : ℕ) (j : ZMod Q) := ∑ u ∈ box c d,
    ZMod.stdAddChar (j * ((c*u^d : ℕ) : ZMod Q))
  let wave (j : ZMod Q) := S 1 2 j * S 1 3 j * S 2 3 j * S m 3 j *
    ZMod.stdAddChar (j * -(n : ZMod Q))
  let major := (univ : Finset (ZMod Q)).filter (fun j =>
    ∃ b ∈ Icc 1 K, ∃ a ≤ b, Nat.dist (b*j.val) (a*Q) ≤ K)
  let localCount := ((univ : Finset (Fin 504 × Fin 504 × Fin 504 × Fin 504)).filter
    (fun t => (t.1.val^2 + t.2.1.val^3 + 2*t.2.2.1.val^3 + m*t.2.2.2.val^3) % 504 =
      n % 504)).card
  let scale : ℝ := Q * Real.sqrt n * localCount / (7 * 504^3)
  (∑ j ∈ majorᶜ, wave j).re ≥ -scale

theorem main : H1 → H2 → type_of% @OeisA262824.conjecture_1 := by
  intro lower upper m hm n
  by_cases smallN : n ≤ 32768
  · exact small m n hm smallN
  let k := Nat.clog 2 n
  let N := 2^k
  let Q := 8 * N
  let K := 32 * (k+1)
  let box (c d : ℕ) := (range (N+1)).filter (fun u => c*u^d ≤ N)
  let S (c d : ℕ) (j : ZMod Q) := ∑ u ∈ box c d,
    ZMod.stdAddChar (j * ((c*u^d : ℕ) : ZMod Q))
  let wave (j : ZMod Q) := S 1 2 j * S 1 3 j * S 2 3 j * S m 3 j *
    ZMod.stdAddChar (j * -(n : ZMod Q))
  let major := (univ : Finset (ZMod Q)).filter (fun j =>
    ∃ b ∈ Icc 1 K, ∃ a ≤ b, Nat.dist (b*j.val) (a*Q) ≤ K)
  let localCount := ((univ : Finset (Fin 504 × Fin 504 × Fin 504 × Fin 504)).filter
    (fun t => (t.1.val^2 + t.2.1.val^3 + 2*t.2.2.1.val^3 + m*t.2.2.2.val^3) % 504 =
      n % 504)).card
  let scale : ℝ := Q * Real.sqrt n * localCount / (7 * 504^3)
  have lo : scale < (∑ j ∈ major, wave j).re := lower m hm n (by omega)
  have hi : -scale ≤ (∑ j ∈ majorᶜ, wave j).re := upper m hm n (by omega)
  have pos : 0 < (∑ j, wave j).re := by
    rw [← sum_add_sum_compl major wave, Complex.add_re]
    linarith
  let value (t : ℕ × ℕ × ℕ × ℕ) := t.2.2.2^2 + t.2.2.1^3 + 2*t.2.1^3 + m*t.1^3
  let tuples := box m 3 ×ˢ (box 2 3 ×ˢ (box 1 3 ×ˢ box 1 2))
  have expand (j : ZMod Q) : wave j = ∑ t ∈ tuples, ZMod.stdAddChar
      (j * ((value t : ZMod Q) - (n : ZMod Q))) := by
    simpa only [wave, S, one_mul, tuples, value] using
      factor m n j (box 1 2) (box 1 3) (box 2 3) (box m 3)
  simp_rw [expand] at pos
  have hN : 0 < N := pow_pos (by decide) _
  have hn : n ≤ N := Nat.le_pow_clog (by decide) n
  have bound (t) (ht : t ∈ tuples) : value t < Q := by
    simp only [tuples, mem_product, box, mem_filter, one_mul] at ht
    dsimp only [value, Q]
    have hw := ht.1.2
    have hx := ht.2.1.2
    have hy := ht.2.2.1.2
    have hz := ht.2.2.2.2
    omega
  obtain ⟨⟨z,y,x,w⟩, _, heq⟩ := detect n (by dsimp only [Q]; omega) tuples value bound pos
  exact ⟨w,x,y,z,heq.symm⟩

end OMA.R_OeisA262824_conjecture_1_R2
