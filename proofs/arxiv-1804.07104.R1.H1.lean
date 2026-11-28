import OMAReductions.R_arxiv_1804_07104_R1

namespace OMA.Proof_arxiv_1804_07104_R1_H1

private lemma mul_inv_mod {n s t : ℕ} (hn : 2 ≤ n) (hst : (s * t) % n = 1) (j : ℕ) (hj : j < n) :
    ((j * s) % n * t) % n = j := by
  calc ((j * s) % n * t) % n
      = (j * s * t) % n := Nat.mod_mul_mod (j * s) t n
    _ = (j * (s * t)) % n := by rw [mul_assoc]
    _ = (j * ((s * t) % n)) % n := (Nat.mul_mod_mod j (s * t) n).symm
    _ = (j * 1) % n := by rw [hst]
    _ = j := by rw [mul_one, Nat.mod_eq_of_lt hj]

private def tourFun (n s : ℕ) (hn : 2 ≤ n) (k : Fin (2 * n)) : Fin (2 * n) :=
  if k.val % 2 = 0 then
    ⟨2 * ((k.val / 2 * s) % n), by have := Nat.mod_lt (k.val / 2 * s) (show 0 < n by omega); omega⟩
  else
    ⟨2 * n - 1 - 2 * ((k.val / 2 * s) % n), by
      have := Nat.mod_lt (k.val / 2 * s) (show 0 < n by omega); omega⟩

private def tourInv (n t : ℕ) (hn : 2 ≤ n) (x : Fin (2 * n)) : Fin (2 * n) :=
  if x.val % 2 = 0 then
    ⟨2 * ((x.val / 2 * t) % n), by have := Nat.mod_lt (x.val / 2 * t) (show 0 < n by omega); omega⟩
  else
    ⟨2 * (((2 * n - 1 - x.val) / 2 * t) % n) + 1, by
      have := Nat.mod_lt ((2 * n - 1 - x.val) / 2 * t) (show 0 < n by omega); omega⟩

private lemma tourFun_val (n s : ℕ) (hn : 2 ≤ n) (k : Fin (2 * n)) :
    (tourFun n s hn k).val =
      if k.val % 2 = 0 then 2 * ((k.val / 2 * s) % n)
      else 2 * n - 1 - 2 * ((k.val / 2 * s) % n) := by
  unfold tourFun
  split_ifs <;> rfl

private lemma tourInv_val (n t : ℕ) (hn : 2 ≤ n) (x : Fin (2 * n)) :
    (tourInv n t hn x).val =
      if x.val % 2 = 0 then 2 * ((x.val / 2 * t) % n)
      else 2 * (((2 * n - 1 - x.val) / 2 * t) % n) + 1 := by
  unfold tourInv
  split_ifs <;> rfl

private def tourEquiv (n s t : ℕ) (hn : 2 ≤ n) (hst : (s * t) % n = 1) :
    Fin (2 * n) ≃ Fin (2 * n) where
  toFun := tourFun n s hn
  invFun := tourInv n t hn
  left_inv k := by
    ext
    rw [tourInv_val, tourFun_val]
    set j := k.val / 2
    have hj : j < n := by omega
    set r := (j * s) % n
    have hr : r < n := Nat.mod_lt _ (by omega)
    by_cases hev : k.val % 2 = 0
    · simp only [hev, ↓reduceIte]
      have h2r_ev : (2 * r) % 2 = 0 := by omega
      simp only [h2r_ev, ↓reduceIte, show (2 * r) / 2 = r by omega]
      rw [mul_inv_mod hn hst j hj]
      omega
    · simp only [hev, ↓reduceIte]
      have hodd : ¬ (2 * n - 1 - 2 * r) % 2 = 0 := by omega
      simp only [hodd, ↓reduceIte, show (2 * n - 1 - (2 * n - 1 - 2 * r)) / 2 = r by omega]
      rw [mul_inv_mod hn hst j hj]
      omega
  right_inv x := by
    ext
    rw [tourFun_val, tourInv_val]
    have hts : (t * s) % n = 1 := by rw [mul_comm]; exact hst
    by_cases hev : x.val % 2 = 0
    · simp only [hev, ↓reduceIte]
      set r := x.val / 2
      have hr : r < n := by omega
      set j := (r * t) % n
      have h2j_ev : (2 * j) % 2 = 0 := by omega
      simp only [h2j_ev, ↓reduceIte, show (2 * j) / 2 = j by omega]
      rw [mul_inv_mod hn hts r hr]
      omega
    · simp only [hev, ↓reduceIte]
      set r := (2 * n - 1 - x.val) / 2
      have hr : r < n := by omega
      set j := (r * t) % n
      have hodd : ¬ (2 * j + 1) % 2 = 0 := by omega
      simp only [hodd, ↓reduceIte, show (2 * j + 1) / 2 = j by omega]
      rw [mul_inv_mod hn hts r hr]
      omega

private lemma finRotate_val {N : ℕ} (hN : 2 ≤ N) (k : Fin N) :
    (finRotate N k).val = (k.val + 1) % N := by
  obtain ⟨m, rfl⟩ : ∃ m, N = m + 2 := ⟨N - 2, by omega⟩
  rw [finRotate_apply, Fin.val_add]
  have h1 : (1 : Fin (m + 2)).val = 1 := by
    simp [Nat.mod_eq_of_lt (show 1 < m + 2 by omega)]
  rw [h1]

end OMA.Proof_arxiv_1804_07104_R1_H1

theorem OMA.solution : OMA.R_arxiv_1804_07104_R1.H1 := by
  intro n s hn hsn hcop hp_center hp_low hp_high
  open OMA.Proof_arxiv_1804_07104_R1_H1 in
  have : NeZero n := ⟨by omega⟩
  have : Fact (1 < n) := ⟨by omega⟩
  have hunit : IsUnit (s : ZMod n) := (ZMod.isUnit_iff_coprime s n).mpr hcop.symm
  let t : ℕ := ((hunit.unit⁻¹ : (ZMod n)ˣ) : ZMod n).val
  have hst : (s * t) % n = 1 := by
    have hmul : ((s * t : ℕ) : ZMod n) = 1 := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
      calc (s : ZMod n) * ((hunit.unit⁻¹ : (ZMod n)ˣ) : ZMod n)
          = (hunit.unit : ZMod n) * ((hunit.unit⁻¹ : (ZMod n)ˣ) : ZMod n) :=
            congrArg (· * _) hunit.unit_spec.symm
        _ = 1 := hunit.unit.mul_inv
    have hv := congrArg ZMod.val hmul
    rw [ZMod.val_natCast, ZMod.val_one] at hv
    exact hv
  refine ⟨tourEquiv n s t hn hst, fun k => ?_⟩
  have hrot : (finRotate (2 * n) k).val = (k.val + 1) % (2 * n) := finRotate_val (by omega) k
  change ((tourFun n s hn k).val + 1 + ((tourFun n s hn (finRotate (2 * n) k)).val + 1)).Prime
  rw [tourFun_val, tourFun_val, hrot]
  set j := k.val / 2
  have hj : j < n := by omega
  set r := (j * s) % n
  have hr : r < n := Nat.mod_lt _ (by omega)
  by_cases hev : k.val % 2 = 0
  · have hlt : k.val + 1 < 2 * n := by omega
    rw [Nat.mod_eq_of_lt hlt]
    have hodd : ¬ (k.val + 1) % 2 = 0 := by omega
    have hdiv : (k.val + 1) / 2 = j := by omega
    simp only [hev, hodd, hdiv, ↓reduceIte]
    have hsum : 2 * r + 1 + (2 * n - 1 - 2 * r + 1) = 2 * n + 1 := by omega
    rw [hsum]
    exact hp_center
  · have hstep_mod : (((k.val + 1) % (2 * n)) / 2 * s) % n = (r + s) % n := by
      by_cases hlt : k.val + 1 < 2 * n
      · rw [Nat.mod_eq_of_lt hlt, show (k.val + 1) / 2 = j + 1 by omega, add_mul, one_mul,
          ← Nat.mod_add_mod (j * s) n s]
      · have hlast : k.val + 1 = 2 * n := by omega
        have hjlast : j + 1 = n := by omega
        rw [hlast, Nat.mod_self, Nat.zero_div, zero_mul, Nat.zero_mod]
        have hsum_eq : (r + s) % n = ((j + 1) * s) % n := by
          rw [add_mul, one_mul, Nat.mod_add_mod]
        rw [hsum_eq, hjlast, Nat.mul_mod_right]
    have hrot_ev : ((k.val + 1) % (2 * n)) % 2 = 0 := by
      by_cases hlt : k.val + 1 < 2 * n
      · rw [Nat.mod_eq_of_lt hlt]; omega
      · rw [show k.val + 1 = 2 * n by omega, Nat.mod_self]
    simp only [hev, hrot_ev, ↓reduceIte]
    rw [hstep_mod]
    by_cases hrs : r + s < n
    · rw [Nat.mod_eq_of_lt hrs]
      have hsum : 2 * n - 1 - 2 * r + 1 + (2 * (r + s) + 1) = 2 * n + 2 * s + 1 := by omega
      rw [hsum]
      exact hp_high
    · have hsub : r + s = (r + s - n) + n := by omega
      rw [hsub, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hsum : 2 * n - 1 - 2 * r + 1 + (2 * (r + s - n) + 1) = 2 * s + 1 := by omega
      rw [hsum]
      exact hp_low
