import OMAReductions.R_Erdos203_erdos_203_R1

namespace E203H2Helper

lemma coeff_ne_zero (p a b : ℕ) (hp : p.Prime) (h6 : ¬ p ∣ 6) :
    ((2 ^ a * 3 ^ b : ℕ) : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with h | h
  · exact h6 (Dvd.dvd.mul_right (hp.dvd_of_dvd_pow h) 3)
  · exact h6 (Dvd.dvd.mul_left (hp.dvd_of_dvd_pow h) 2)

lemma coprime6 (p : ℕ) (hp : p.Prime) (h6 : ¬ p ∣ 6) : Nat.Coprime p 6 :=
  (Nat.Prime.coprime_iff_not_dvd hp).mpr h6

end E203H2Helper

theorem OMA.solution : OMA.R_Erdos203_erdos_203_R1.H2 := by
  intro n p alpha beta hp hp6 hinj
  classical
  let r : Fin n → ℕ := fun i =>
    haveI : Fact (p i).Prime := ⟨hp i⟩
    (-((2 ^ alpha i * 3 ^ beta i : ℕ) : ZMod (p i))⁻¹).val
  let s : Option (Fin n) → ℕ := fun o => o.elim 6 p
  let a : Option (Fin n) → ℕ := fun o => o.elim 1 r
  have hs : ∀ o ∈ (Finset.univ : Finset (Option (Fin n))), s o ≠ 0 := by
    intro o _
    cases o with
    | none => simp [s]
    | some i => exact (hp i).ne_zero
  have pp : Set.Pairwise ((Finset.univ : Finset (Option (Fin n))) : Set (Option (Fin n)))
      (Function.onFun Nat.Coprime s) := by
    intro o _ o' _ hne
    cases o with
    | none =>
      cases o' with
      | none => exact absurd rfl hne
      | some j => exact (E203H2Helper.coprime6 _ (hp j) (hp6 j)).symm
    | some i =>
      cases o' with
      | none => exact E203H2Helper.coprime6 _ (hp i) (hp6 i)
      | some j =>
        have hij : i ≠ j := fun h => hne (by rw [h])
        exact (Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h))
  obtain ⟨m0, hm0⟩ := Nat.chineseRemainderOfFinset a s Finset.univ hs pp
  let L : ℕ := ∏ o : Option (Fin n), s o
  have hLpos : 0 < L := Finset.prod_pos (fun o _ => Nat.pos_of_ne_zero (hs o (Finset.mem_univ o)))
  let B : ℕ := ∑ i, p i + 1
  refine ⟨m0 + L * B, ?_, ?_, ?_⟩
  · have hmod : m0 + L * B ≡ m0 [MOD s none] := by
      have hd : s none ∣ L * B := Dvd.dvd.mul_right (Finset.dvd_prod_of_mem s (Finset.mem_univ _)) B
      have := Nat.ModEq.add_left m0 ((Nat.modEq_zero_iff_dvd).mpr hd)
      simpa using this
    have h1 := hmod.trans (hm0 none (Finset.mem_univ _))
    have h1' : (m0 + L * B) % 6 = 1 := h1
    rw [Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, h1']
    rfl
  · intro i
    have h1 : p i ≤ ∑ j, p j := Finset.single_le_sum (fun j _ => Nat.zero_le (p j)) (Finset.mem_univ i)
    have h2 : B ≤ L * B := Nat.le_mul_of_pos_left B hLpos
    omega
  · intro i
    have : Fact (p i).Prime := ⟨hp i⟩
    have hmod : m0 + L * B ≡ m0 [MOD s (some i)] := by
      have hd : s (some i) ∣ L * B :=
        Dvd.dvd.mul_right (Finset.dvd_prod_of_mem s (Finset.mem_univ _)) B
      have := Nat.ModEq.add_left m0 ((Nat.modEq_zero_iff_dvd).mpr hd)
      simpa using this
    have h1 : m0 + L * B ≡ r i [MOD p i] := hmod.trans (hm0 (some i) (Finset.mem_univ _))
    rw [← ZMod.natCast_eq_zero_iff]
    have hc := E203H2Helper.coeff_ne_zero (p i) (alpha i) (beta i) (hp i) (hp6 i)
    have hm : ((m0 + L * B : ℕ) : ZMod (p i)) = -((2 ^ alpha i * 3 ^ beta i : ℕ) : ZMod (p i))⁻¹ := by
      rw [(ZMod.natCast_eq_natCast_iff _ _ _).mpr h1]
      exact ZMod.natCast_zmod_val _
    rw [Nat.cast_add, Nat.cast_mul, hm, Nat.cast_one, mul_neg, mul_inv_cancel₀ hc]
    exact neg_add_cancel 1
