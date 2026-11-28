import OMAStatements.S_mo_455020
import Mathlib

/-!
Each pair of mirror entries passes exactly when both its initial and shifted
entries are coprime. Their sums are the two candidate primes. For n ≥ m+3,
a composite candidate has a prime factor at most n, so the arithmetic
progression of entries contains a multiple of that factor.
-/

section
namespace Mo455020

open OMA.S_mo_455020

private theorem entry_bound {m i : ℕ} (hm : 3 ≤ m) (hi : 1 ≤ i) :
    6 ≤ m * (i+1) := Nat.mul_le_mul hm (by omega : 2 ≤ i+1)

private theorem mirror_sum {m n i c : ℕ} (hm : 3 ≤ m)
    (hi : i ∈ Finset.Icc 1 n) (hc : c ≤ 2) :
    target m n c = entry m i c + entry m (n+1-i) c := by
  obtain ⟨hi1, hin⟩ := Finset.mem_Icc.mp hi
  have hj : 1 ≤ n+1-i := by omega
  have h₁ := entry_bound hm hi1
  have h₂ := entry_bound hm hj
  have hidx : n+3 = (i+1)+(n+1-i+1) := by omega
  unfold entry target
  rw [hidx, Nat.mul_add]
  omega

private theorem tests_at {m n i c : ℕ} (hm : 3 ≤ m)
    (hi : i ∈ Finset.Icc 1 n) (hc : c ≤ 2) :
    Nat.Coprime (entry m i c) (target m n c) ↔
      Nat.Coprime (entry m i c) (entry m (n+1-i) c) := by
  rw [mirror_sum hm hi hc, Nat.coprime_self_add_right]

private theorem row {m n i : ℕ} (hm : 3 ≤ m) (hi : i ∈ Finset.Icc 1 n) :
    finalEntry m n i = m*(i+1) ↔
    Nat.Coprime (entry m i 2) (entry m (n+1-i) 2) ∧
    Nat.Coprime (entry m i 1) (entry m (n+1-i) 1) := by
  obtain ⟨hi1, hin⟩ := Finset.mem_Icc.mp hi
  have hu := entry_bound hm hi1
  have hv := entry_bound (m := m) (i := n+1-i) hm (by omega)
  let x := entry m i 2
  let y := entry m (n+1-i) 2
  have hx : 4 ≤ x := by dsimp [x,entry]; omega
  have hy : 4 ≤ y := by dsimp [y,entry]; omega
  have he1 : entry m i 1 = x+1 := by dsimp [x,entry]; omega
  have he2 : entry m (n+1-i) 1 = y+1 := by dsimp [y,entry]; omega
  have ht : m*(i+1) = x+2 := by dsimp [x,entry]; omega
  rw [he1, he2, ht]
  change (if i = n+1-i then x+2*x.gcd y else x+x.gcd y+(x+x.gcd y).gcd (y+x.gcd y)) = x+2 ↔
    x.gcd y = 1 ∧ (x+1).gcd (y+1) = 1
  split_ifs with h
  · have he : y = x := congrArg (fun j => entry m j 2) h.symm
    rw [he, Nat.gcd_self]
    omega
  · have h₁ := Nat.gcd_pos_of_pos_left y (by omega : 0 < x)
    have h₂ := Nat.gcd_pos_of_pos_left (y+x.gcd y) (by omega : 0 < x+x.gcd y)
    constructor
    · intro h
      have hg : x.gcd y = 1 := by omega
      rw [hg] at h
      exact ⟨hg, by omega⟩
    · rintro ⟨h, h'⟩
      rw [h, h']

theorem passes_iff_tests {m n : ℕ} (hm : 3 ≤ m) :
    passes m n ↔ ∀ c, (c=1 ∨ c=2) → ∀ i ∈ Finset.Icc 1 n,
      Nat.Coprime (entry m i c) (target m n c) := by
  constructor
  · rintro h c (rfl | rfl) i hi
    · exact (tests_at hm hi (by decide)).2 ((row hm hi).1 (h i hi)).2
    · exact (tests_at hm hi (by decide)).2 ((row hm hi).1 (h i hi)).1
  · intro h i hi
    apply (row hm hi).2
    exact ⟨(tests_at hm hi (by decide)).1 (h 2 (Or.inr rfl) i hi),
      (tests_at hm hi (by decide)).1 (h 1 (Or.inl rfl) i hi)⟩

theorem passes_of_twins {m n : ℕ} (hm : 3 ≤ m) (ht : twins m n) : passes m n := by
  apply (passes_iff_tests hm).2
  intro c hc i hi
  have hp : (target m n c).Prime := by rcases hc with rfl|rfl; exact ht.2; exact ht.1
  obtain ⟨hi1, hin⟩ := Finset.mem_Icc.mp hi
  have hci : c ≤ 2 := by rcases hc with rfl|rfl <;> decide
  have hu := entry_bound hm hi1
  have hv := entry_bound (m := m) (i := n+1-i) hm (by omega)
  apply (Nat.coprime_of_lt_prime _ _ hp).symm
  · unfold entry
    omega
  · rw [mirror_sum hm hi hci]
    unfold entry
    omega

end Mo455020
end

section
namespace Mo455020

open OMA.S_mo_455020

theorem prime_of_tests {m n c : ℕ} (hm : 3 ≤ m) (hodd : Odd m) (hn : m + 3 ≤ n)
    (hc : c = 1 ∨ c = 2)
    (ht : ∀ i ∈ Finset.Icc 1 n, Nat.Coprime (entry m i c) (target m n c)) :
    (target m n c).Prime := by
  by_contra hcom
  let N := target m n c
  let p := N.minFac
  have hc2 : c ≤ 2 := by omega
  have hbig : 2 * c + 2 ≤ m * (n + 3) := by
    nlinarith [Nat.mul_le_mul_right (n + 3) hm]
  have hN : 2 ≤ N := by dsimp [N, target]; omega
  have hp : p.Prime := Nat.minFac_prime (by omega : N ≠ 1)
  have hdN : p ∣ N := Nat.minFac_dvd _
  have hNsq : N ≤ n ^ 2 := by
    apply (Nat.sub_le _ _).trans
    nlinarith [Nat.mul_le_mul_right (n + 3) hn]
  have hpsq : p ^ 2 ≤ N := Nat.minFac_sq_le_self (by omega) hcom
  have hpn : p ≤ n := by nlinarith
  have hpm : ¬p ∣ m := by
    intro hd
    have hfull : p ∣ m * (n + 3) := dvd_mul_of_dvd_left hd _
    have hsum : N + 2 * c = m * (n + 3) := by dsimp [N, target]; omega
    rw [← hsum, Nat.dvd_add_right hdN] at hfull
    have hp2 : p ∣ 2 := by
      rcases hc with rfl | rfl
      · simpa using hfull
      · exact (hp.dvd_mul.mp hfull).elim id id
    have heq := (Nat.dvd_prime Nat.prime_two).mp hp2
    rcases hodd with ⟨k, hk⟩
    rcases heq with h | h
    · exact hp.ne_one h
    · rw [h] at hd
      omega
  let : Fact p.Prime := ⟨hp⟩
  have hm0 : (m : ZMod p) ≠ 0 := fun h => hpm ((ZMod.natCast_eq_zero_iff _ _).mp h)
  let z : ZMod p := (c : ZMod p) * (m : ZMod p)⁻¹ - 2
  let i := z.val + 1
  have hi : i ∈ Finset.Icc 1 n := Finset.mem_Icc.mpr (by
    dsimp [i]
    have hz := ZMod.val_lt z
    omega)
  have hci : c ≤ m * (i + 1) := by nlinarith [Nat.mul_le_mul_right (i + 1) hm]
  have hzero : (entry m i c : ZMod p) = 0 := by
    rw [entry, Nat.cast_sub hci, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    dsimp [i]
    push_cast
    rw [ZMod.natCast_zmod_val]
    dsimp [z]
    field_simp
    ring
  have hdentry := (ZMod.natCast_eq_zero_iff _ _).mp hzero
  have hg := Nat.dvd_gcd hdentry hdN
  have hone := (ht i hi).gcd_eq_one
  change p ∣ (entry m i c).gcd (target m n c) at hg
  rw [hone] at hg
  exact hp.not_dvd_one hg

end Mo455020
end

theorem OMA.solution : type_of% @OMA.S_mo_455020.main := by
  intro m hm hodd
  refine ⟨fun _ _ ht => Mo455020.passes_of_twins hm ht, m+3, ?_⟩
  intro n hn
  constructor
  · intro h
    have ht := (Mo455020.passes_iff_tests hm).1 h
    exact ⟨Mo455020.prime_of_tests hm hodd hn (Or.inr rfl) (ht 2 (Or.inr rfl)),
      Mo455020.prime_of_tests hm hodd hn (Or.inl rfl) (ht 1 (Or.inl rfl))⟩
  · exact Mo455020.passes_of_twins hm
