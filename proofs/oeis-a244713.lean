import OMAStatements.S_oeis_a244713

namespace OMA.P_oeis_a244713

open OMA.S_oeis_a244713

/-- The decidable form of `primRep`. -/
def q (k : ℕ) : Prop := 0 < k ∧ (k % 3 = 1 ∨ k % 27 = 0 ∨ k % 27 = 18)

instance : DecidablePred q := fun k => by unfold q; infer_instance

lemma z27 : ∀ a b : ZMod 27, (a ^ 2 + a * b - 2 * b ^ 2).val % 3 = 1 ∨
    (a ^ 2 + a * b - 2 * b ^ 2).val = 0 ∨
    (a ^ 2 + a * b - 2 * b ^ 2).val = 18 ∨ (a.val % 3 = 0 ∧ b.val % 3 = 0) := by decide

lemma isCoprime_gcd {x y : ℤ} (h : IsCoprime x y) : Int.gcd x y = 1 :=
  Int.isCoprime_iff_gcd_eq_one.mp h

lemma char (k : ℕ) : primRep k ↔ q k := by
  constructor
  · rintro ⟨hk, x, y, hg, he⟩
    refine ⟨hk, ?_⟩
    have hz := z27 (x : ZMod 27) (y : ZMod 27)
    have hv : ((x : ZMod 27) ^ 2 + (x : ZMod 27) * (y : ZMod 27) - 2 * (y : ZMod 27) ^ 2)
        = (k : ZMod 27) := by
      have := congrArg (fun t : ℤ => (t : ZMod 27)) he
      push_cast at this
      exact this
    rw [hv, ZMod.val_natCast] at hz
    rcases hz with h | h | h | ⟨h1, h2⟩
    · left; omega
    · right; left; exact h
    · right; right; exact h
    · exfalso
      have hx : ((x : ZMod 27).val : ℤ) = x % 27 := by
        rw [ZMod.val_intCast]; norm_cast
      have hy : ((y : ZMod 27).val : ℤ) = y % 27 := by
        rw [ZMod.val_intCast]; norm_cast
      have hx3 : (3 : ℤ) ∣ x := by omega
      have hy3 : (3 : ℤ) ∣ y := by omega
      have h3 : (3 : ℤ) ∣ (Int.gcd x y : ℤ) := Int.dvd_coe_gcd hx3 hy3
      rw [hg] at h3
      norm_num at h3
  · rintro ⟨hk, h⟩
    refine ⟨hk, ?_⟩
    rcases h with h | h | h
    · obtain ⟨t, rfl⟩ : ∃ t, k = 3 * t + 1 := ⟨k / 3, by omega⟩
      refine ⟨t + 1, t, isCoprime_gcd ⟨1, -1, by ring⟩, ?_⟩
      push_cast; ring
    · obtain ⟨t, rfl⟩ : ∃ t, k = 27 * t := ⟨k / 27, by omega⟩
      refine ⟨3 * t + 2, 3 * t - 1, isCoprime_gcd ⟨t, -(t + 1), by ring⟩, ?_⟩
      push_cast; ring
    · obtain ⟨t, rfl⟩ : ∃ t, k = 27 * t + 18 := ⟨k / 27, by omega⟩
      refine ⟨3 * t + 4, 3 * t + 1, isCoprime_gcd ⟨-t, t + 1, by ring⟩, ?_⟩
      push_cast; ring

lemma primRep_eq : primRep = q := funext fun k => propext (char k)

lemma q_inf : {k | q k}.Infinite :=
  Set.infinite_of_forall_exists_gt fun m => ⟨3 * m + 1, ⟨by omega, Or.inl (by omega)⟩, by omega⟩

lemma q_shift (k : ℕ) (hk : 1 ≤ k) : q (k + 27) ↔ q k := by
  unfold q; omega

lemma count_shift : ∀ k : ℕ, 1 ≤ k → Nat.count q (k + 27) = Nat.count q k + 11 := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    rw [show k + 1 + 27 = (k + 27) + 1 by ring, Nat.count_succ q (k + 27), Nat.count_succ q k, ih]
    have := q_shift k hk
    by_cases h : q k
    · rw [if_pos h, if_pos (this.mpr h)]
    · rw [if_neg h, if_neg (fun h' => h (this.mp h'))]

lemma nth_shift (i : ℕ) : Nat.nth q (i + 11) = Nat.nth q i + 27 := by
  have hm := Nat.nth_mem_of_infinite q_inf i
  have hc := Nat.count_nth_of_infinite q_inf i
  have h1 : 1 ≤ Nat.nth q i := hm.1
  have hm' : q (Nat.nth q i + 27) := (q_shift _ h1).mpr hm
  have hc' : Nat.count q (Nat.nth q i + 27) = i + 11 := by
    rw [count_shift _ h1, hc]
  rw [← hc', Nat.nth_count hm']

end OMA.P_oeis_a244713

theorem OMA.solution : type_of% @OMA.S_oeis_a244713.main := by
  intro n hn
  unfold OMA.S_oeis_a244713.a
  rw [OMA.P_oeis_a244713.primRep_eq]
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 13 := ⟨n - 13, by omega⟩
  rw [show j + 13 - 1 - 1 = j + 11 by omega, show j + 13 - 11 - 1 = j + 1 by omega,
    show j + 13 - 12 - 1 = j by omega, show j + 13 - 1 = (j + 1) + 11 by omega,
    OMA.P_oeis_a244713.nth_shift (j + 1), OMA.P_oeis_a244713.nth_shift j]
  push_cast
  ring
