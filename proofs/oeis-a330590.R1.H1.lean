import OMAReductions.R_oeis_a330590_R1

/-!
Every universal divisor for x^n−x is squarefree, by substituting each
prime divisor for x. For each prime divisor p, substitute an integer lift
of a generator of the units of ZMod p to get p−1 ∣ n−1. The universal
divisor is the product of its distinct eligible primes.
-/

open Finset OMA.S_oeis_a330590

private theorem universal_squarefree {n m : ℕ} (hn : 2 ≤ n)
    (h : ∀ x : ℤ, (m : ℤ) ∣ x ^ n - x ^ 1) : Squarefree m := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hd
  have hd' : (p : ℤ) * p ∣ (m : ℤ) := by exact_mod_cast hd
  have hpow : (p : ℤ) * p ∣ (p : ℤ) ^ n := by
    rw [← pow_two]
    exact pow_dvd_pow _ hn
  have hl : (p : ℤ) * p ∣ (p : ℤ) := by
    simpa only [sub_sub_cancel, pow_one] using dvd_sub hpow (hd'.trans (h p))
  have hpNat : p * p ∣ p := by exact_mod_cast hl
  have hlt : p < p * p := calc
    p = p * 1 := (Nat.mul_one p).symm
    _ < _ := Nat.mul_lt_mul_of_pos_left hp.one_lt hp.pos
  exact (not_lt_of_ge (Nat.le_of_dvd hp.pos hpNat)) hlt

private theorem prime_exponent_condition {n p : ℕ} (hn : 2 ≤ n) (hp : p.Prime)
    (h : ∀ x : ℤ, (p : ℤ) ∣ x ^ n - x ^ 1) : p - 1 ∣ n - 1 := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  let z : ℤ := (u.val.val : ℤ)
  have hz_cast : (z : ZMod p) = u.val := by
    dsimp only [z]
    rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (h z)
  rw [Int.cast_sub, Int.cast_pow, Int.cast_pow, hz_cast, sub_eq_zero] at hz
  have hpow : u ^ n = u ^ 1 := Units.val_injective hz
  have hpow' : u ^ (n - 1) = 1 := by
    apply mul_right_cancel (b := u ^ 1)
    rw [← pow_add, Nat.sub_add_cancel (by omega : 1 ≤ n), hpow, one_mul]
  have hd := orderOf_dvd_of_pow_eq_one hpow'
  rw [hu, Nat.card_units, Nat.card_eq_fintype_card, ZMod.card p] at hd
  exact hd

theorem OMA.solution : OMA.R_oeis_a330590_R1.H1 := by
  intro n hn
  let D := (Nat.divisors (n - 1)).filter (fun d => (d + 1).Prime)
  let P := D.image (fun d => d + 1)
  let F := P.powerset.image (fun Q => ∏ p ∈ Q, p)
  let U : Set ℕ := {m | 0 < m ∧ ∀ x : ℤ, (m : ℤ) ∣ x ^ n - x ^ 1}
  have hPcard : P.card = A067513 (n - 1) := by
    exact card_image_of_injective D (fun _ _ h => by omega)
  have hUF : U ⊆ (F : Set ℕ) := by
    intro m hm
    have hQ : m.primeFactors ⊆ P := by
      intro p hp
      obtain ⟨hp, hpm, _⟩ := Nat.mem_primeFactors.mp hp
      have hpm' : (p : ℤ) ∣ (m : ℤ) := by exact_mod_cast hpm
      have hd := prime_exponent_condition hn hp (fun x => hpm'.trans (hm.2 x))
      have he : p - 1 + 1 = p := Nat.sub_add_cancel hp.pos
      apply mem_image.mpr
      refine ⟨p - 1, mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd, by omega⟩, ?_⟩, he⟩
      rwa [he]
    exact mem_image.mpr ⟨m.primeFactors, mem_powerset.mpr hQ,
      Nat.prod_primeFactors_of_squarefree (universal_squarefree hn hm.2)⟩
  change U.ncard ≤ 2 ^ A067513 (n - 1)
  calc
    _ ≤ (F : Set ℕ).ncard := Set.ncard_le_ncard hUF F.finite_toSet
    _ = F.card := Set.ncard_coe_finset _
    _ ≤ P.powerset.card := card_image_le
    _ = _ := by rw [card_powerset, hPcard]
