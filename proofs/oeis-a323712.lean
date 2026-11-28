import OMAStatements.S_oeis_a323712
import Mathlib

/-
Proof of conjectures (C1) and (C2) of A323712.

Route: positions are embedded into a ring `ZMod M` by an injective map `φ` with `φ top = 1` and
`φ i = -2 * φ (shuf n i)` (even `n`: `M = n + 1`, `φ i = i + 1`; odd `n`: `M = 3 * n`, `φ i = 3 * i + 1`).
Iterating, `φ i = (-2) ^ k * φ ((shuf n ^ k) i)`. If `shuf n ^ k` fixes the top card then `(-2) ^ k = 1`, so
`shuf n ^ k` fixes every card.
(C1): by pigeonhole two of the `n + 1` positions `(shuf n ^ j) top`, `j ≤ n`, coincide, which gives some
`1 ≤ d ≤ n` with `(shuf n ^ d) top = top`, hence `shuf n ^ d = 1` and `orderOf (shuf n) ≤ d ≤ n`.
(C2): the same relation gives `orderOf (shuf n) = orderOf (-2 : ZMod M)`. For a prime `p ≥ 5`,
`a (p - 1) = orderOf (-2 : ZMod p)` and `a p = orderOf (-2 : ZMod (3 * p))`; since `3` divides `1 - (-2) ^ k`
for every `k` and `3`, `p` are coprime, `(-2) ^ k = 1` holds modulo `3 * p` exactly when it holds modulo `p`, so the
two orders agree; and `orderOf (-2 : ZMod p)` divides `p - 1` (Fermat), as `-2 ≠ 0` modulo `p`.
-/

namespace OMA.A323712Proof

open OMA.S_oeis_a323712

theorem iter_rel {n M : ℕ} (σ : Equiv.Perm (Fin n)) (φ : Fin n → ZMod M) (g : ZMod M)
    (hrel : ∀ i, φ i = g * φ (σ i)) : ∀ j : ℕ, ∀ i, φ i = g ^ j * φ ((σ ^ j) i) := by
  intro j
  induction j with
  | zero => intro i; simp
  | succ j ih =>
    intro i
    have h1 := hrel ((σ ^ j) i)
    have h2 : (σ ^ (j + 1)) i = σ ((σ ^ j) i) := by
      rw [pow_succ', Equiv.Perm.mul_apply]
    rw [h2, ih i, h1]
    ring

theorem key {n M : ℕ} (σ : Equiv.Perm (Fin n)) (φ : Fin n → ZMod M) (hφ : Function.Injective φ)
    (g : ZMod M) (hrel : ∀ i, φ i = g * φ (σ i)) (t : Fin n) (ht : φ t = 1)
    (k : ℕ) (hk : (σ ^ k) t = t) : σ ^ k = 1 := by
  have hit := iter_rel σ φ g hrel
  have hg : g ^ k = 1 := by
    have h := hit k t
    rw [hk, ht, mul_one] at h
    exact h.symm
  apply Equiv.ext
  intro i
  have h := hit k i
  rw [hg, one_mul] at h
  rw [Equiv.Perm.one_apply]
  exact (hφ h).symm

theorem orderOf_le_of_top {n : ℕ} (σ : Equiv.Perm (Fin n)) (t : Fin n)
    (hkey : ∀ k : ℕ, (σ ^ k) t = t → σ ^ k = 1) : orderOf σ ≤ n := by
  have aux : ∀ a d : ℕ, 0 < d → a + d ≤ n → (σ ^ a) t = (σ ^ (a + d)) t → orderOf σ ≤ n := by
    intro a d hd hle h
    rw [pow_add, Equiv.Perm.mul_apply] at h
    have h2 : (σ ^ d) t = t := ((σ ^ a).injective h).symm
    have h3 := orderOf_le_of_pow_eq_one hd (hkey d h2)
    omega
  obtain ⟨x, y, hxy, hf⟩ := Fintype.exists_ne_map_eq_of_card_lt
    (fun i : Fin (n + 1) => (σ ^ (i : ℕ)) t) (by simp)
  have hx := x.isLt
  have hy := y.isLt
  have hne : (x : ℕ) ≠ y := fun h => hxy (Fin.ext h)
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · obtain ⟨d, hd⟩ : ∃ d, (y : ℕ) = x + d := ⟨y - x, by omega⟩
    exact aux x d (by omega) (by omega) (by rw [← hd]; exact hf)
  · obtain ⟨d, hd⟩ : ∃ d, (x : ℕ) = y + d := ⟨x - y, by omega⟩
    exact aux y d (by omega) (by omega) (by rw [← hd]; exact hf.symm)

theorem spec_even (n i : ℕ) (hi : i < n) (hn : n % 2 = 0) :
    ∃ q : ℕ, i + 1 + 2 * (newPos n i + 1) = (n + 1) * q := by
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · refine ⟨1, ?_⟩
    rw [newPos, if_pos h]
    omega
  · refine ⟨2, ?_⟩
    rw [newPos, if_neg (by omega)]
    omega

theorem spec_odd (n i : ℕ) (hi : i < n) (hn : n % 2 = 1) :
    ∃ q : ℕ, i + 1 + 2 * newPos n i = n * q := by
  rcases Nat.mod_two_eq_zero_or_one i with h | h
  · refine ⟨1, ?_⟩
    rw [newPos, if_pos h]
    omega
  · refine ⟨2, ?_⟩
    rw [newPos, if_neg (by omega)]
    omega

theorem top_fix (n : ℕ) (hn : 1 ≤ n) (k : ℕ) (hk : (shuf n ^ k) ⟨0, hn⟩ = ⟨0, hn⟩) :
    shuf n ^ k = 1 := by
  rcases Nat.mod_two_eq_zero_or_one n with hpar | hpar
  · refine key (shuf n) (fun i => ((i.val + 1 : ℕ) : ZMod (n + 1))) ?_ (-2) ?_ ⟨0, hn⟩ ?_ k hk
    · intro i j h
      have hi := i.isLt
      have hj := j.isLt
      have h' : ((i.val + 1 : ℕ) : ZMod (n + 1)) = ((j.val + 1 : ℕ) : ZMod (n + 1)) := h
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
      exact Fin.ext (by omega)
    · intro i
      obtain ⟨q, hq⟩ := spec_even n i.val i.isLt hpar
      show ((i.val + 1 : ℕ) : ZMod (n + 1)) = -2 * ((newPos n i.val + 1 : ℕ) : ZMod (n + 1))
      have hc : ((i.val + 1 + 2 * (newPos n i.val + 1) : ℕ) : ZMod (n + 1)) = 0 := by
        rw [hq, Nat.cast_mul, ZMod.natCast_self, zero_mul]
      push_cast at hc ⊢
      linear_combination hc
    · simp
  · refine key (shuf n) (fun i => ((3 * i.val + 1 : ℕ) : ZMod (3 * n))) ?_ (-2) ?_ ⟨0, hn⟩ ?_ k hk
    · intro i j h
      have hi := i.isLt
      have hj := j.isLt
      have h' : ((3 * i.val + 1 : ℕ) : ZMod (3 * n)) = ((3 * j.val + 1 : ℕ) : ZMod (3 * n)) := h
      rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
      exact Fin.ext (by omega)
    · intro i
      obtain ⟨q, hq⟩ := spec_odd n i.val i.isLt hpar
      show ((3 * i.val + 1 : ℕ) : ZMod (3 * n)) = -2 * ((3 * newPos n i.val + 1 : ℕ) : ZMod (3 * n))
      have e : 3 * i.val + 1 + 2 * (3 * newPos n i.val + 1) = 3 * n * q := by
        rw [mul_assoc, ← hq]
        ring
      have hc : ((3 * i.val + 1 + 2 * (3 * newPos n i.val + 1) : ℕ) : ZMod (3 * n)) = 0 := by
        rw [e, Nat.cast_mul, ZMod.natCast_self, zero_mul]
      push_cast at hc ⊢
      linear_combination hc
    · simp

-- (C2)

theorem order_eq_of_iff {G H : Type*} [Monoid G] [Monoid H] (x : G) (y : H)
    (h : ∀ k : ℕ, x ^ k = 1 ↔ y ^ k = 1) : orderOf x = orderOf y := by
  apply Nat.dvd_antisymm
  · rw [orderOf_dvd_iff_pow_eq_one, h]
    exact pow_orderOf_eq_one y
  · rw [orderOf_dvd_iff_pow_eq_one, ← h]
    exact pow_orderOf_eq_one x

theorem order_eq {n M : ℕ} (σ : Equiv.Perm (Fin n)) (φ : Fin n → ZMod M) (hφ : Function.Injective φ)
    (g : ZMod M) (hrel : ∀ i, φ i = g * φ (σ i)) (t : Fin n) (ht : φ t = 1) :
    orderOf σ = orderOf g := by
  have hit := iter_rel σ φ g hrel
  have hiff : ∀ k : ℕ, σ ^ k = 1 ↔ g ^ k = 1 := by
    intro k
    constructor
    · intro hk
      have h := hit k t
      rw [hk, Equiv.Perm.one_apply, ht, mul_one] at h
      exact h.symm
    · intro hg
      apply Equiv.ext
      intro i
      have h := hit k i
      rw [hg, one_mul] at h
      rw [Equiv.Perm.one_apply]
      exact (hφ h).symm
  exact order_eq_of_iff σ g hiff

theorem order_even (n : ℕ) (hn : 1 ≤ n) (hpar : n % 2 = 0) :
    orderOf (shuf n) = orderOf (-2 : ZMod (n + 1)) := by
  refine order_eq (shuf n) (fun i => ((i.val + 1 : ℕ) : ZMod (n + 1))) ?_ (-2) ?_ ⟨0, hn⟩ ?_
  · intro i j h
    have hi := i.isLt
    have hj := j.isLt
    have h' : ((i.val + 1 : ℕ) : ZMod (n + 1)) = ((j.val + 1 : ℕ) : ZMod (n + 1)) := h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
    exact Fin.ext (by omega)
  · intro i
    obtain ⟨q, hq⟩ := spec_even n i.val i.isLt hpar
    show ((i.val + 1 : ℕ) : ZMod (n + 1)) = -2 * ((newPos n i.val + 1 : ℕ) : ZMod (n + 1))
    have hc : ((i.val + 1 + 2 * (newPos n i.val + 1) : ℕ) : ZMod (n + 1)) = 0 := by
      rw [hq, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    push_cast at hc ⊢
    linear_combination hc
  · simp

theorem order_odd (n : ℕ) (hn : 1 ≤ n) (hpar : n % 2 = 1) :
    orderOf (shuf n) = orderOf (-2 : ZMod (3 * n)) := by
  refine order_eq (shuf n) (fun i => ((3 * i.val + 1 : ℕ) : ZMod (3 * n))) ?_ (-2) ?_ ⟨0, hn⟩ ?_
  · intro i j h
    have hi := i.isLt
    have hj := j.isLt
    have h' : ((3 * i.val + 1 : ℕ) : ZMod (3 * n)) = ((3 * j.val + 1 : ℕ) : ZMod (3 * n)) := h
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h'
    exact Fin.ext (by omega)
  · intro i
    obtain ⟨q, hq⟩ := spec_odd n i.val i.isLt hpar
    show ((3 * i.val + 1 : ℕ) : ZMod (3 * n)) = -2 * ((3 * newPos n i.val + 1 : ℕ) : ZMod (3 * n))
    have e : 3 * i.val + 1 + 2 * (3 * newPos n i.val + 1) = 3 * n * q := by
      rw [mul_assoc, ← hq]
      ring
    have hc : ((3 * i.val + 1 + 2 * (3 * newPos n i.val + 1) : ℕ) : ZMod (3 * n)) = 0 := by
      rw [e, Nat.cast_mul, ZMod.natCast_self, zero_mul]
    push_cast at hc ⊢
    linear_combination hc
  · simp

theorem crit (m k : ℕ) : (-2 : ZMod m) ^ k = 1 ↔ (m : ℤ) ∣ 1 - (-2 : ℤ) ^ k := by
  rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]
  simp

theorem three_dvd (k : ℕ) : ((3 : ℕ) : ℤ) ∣ 1 - (-2 : ℤ) ^ k := by
  have h := sub_dvd_pow_sub_pow (1 : ℤ) (-2) k
  rw [one_pow] at h
  have e : (1 : ℤ) - (-2) = ((3 : ℕ) : ℤ) := by norm_num
  rw [e] at h
  exact h

theorem order_3p (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) :
    orderOf (-2 : ZMod (3 * p)) = orderOf (-2 : ZMod p) := by
  apply order_eq_of_iff
  intro k
  rw [crit, crit]
  constructor
  · intro h
    have hd : (p : ℤ) ∣ ((3 * p : ℕ) : ℤ) := ⟨3, by push_cast; ring⟩
    exact dvd_trans hd h
  · intro h
    have hc : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (by omega)
    have hcop : IsCoprime ((3 : ℕ) : ℤ) (p : ℤ) := Nat.isCoprime_iff_coprime.mpr hc
    have h3 := hcop.mul_dvd (three_dvd k) h
    rw [Nat.cast_mul]
    exact h3

theorem order_dvd (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) : orderOf (-2 : ZMod p) ∣ p - 1 := by
  have := Fact.mk hp
  apply ZMod.orderOf_dvd_card_sub_one
  intro h
  have h2 : ((2 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination -h
  rw [CharP.cast_eq_zero_iff (ZMod p) p] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

theorem c2 (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p) : a p = a (p - 1) ∧ a p ∣ p - 1 := by
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have e1 : a p = orderOf (-2 : ZMod p) := by
    show orderOf (shuf p) = _
    rw [order_odd p (by omega) hodd, order_3p p hp h5]
  have e2 : a (p - 1) = orderOf (-2 : ZMod p) := by
    show orderOf (shuf (p - 1)) = _
    rw [order_even (p - 1) (by omega) (by omega)]
    have e : p - 1 + 1 = p := by omega
    rw [e]
  refine ⟨e1.trans e2.symm, ?_⟩
  rw [e1]
  exact order_dvd p hp h5

end OMA.A323712Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a323712.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    show orderOf (OMA.S_oeis_a323712.shuf n) ≤ n
    exact OMA.A323712Proof.orderOf_le_of_top (OMA.S_oeis_a323712.shuf n) ⟨0, hn⟩
      (OMA.A323712Proof.top_fix n hn)
  · intro p hp h5
    exact OMA.A323712Proof.c2 p hp h5
