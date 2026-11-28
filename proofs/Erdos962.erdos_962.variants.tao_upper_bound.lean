import FormalConjectures.ErdosProblems.«962»

/-!
# A square-root bound for Erdős 962

If m < k², the first multiple of k strictly above m has the form kq with
1 ≤ q ≤ k. It belongs to the interval from m+1 to m+k, yet every prime
factor divides k or q and is consequently at most k.
-/

theorem OMA.solution : type_of% @Erdos962.erdos_962.variants.tao_upper_bound := by
  classical
  refine ⟨fun _ => 0, fun δ hδ => Filter.Eventually.of_forall fun _ => by simpa using hδ, ?_⟩
  refine Filter.Eventually.of_forall fun n => ?_
  simp only [add_zero, one_mul]
  apply Real.le_sqrt_of_sq_le
  let k := Erdos962.k n
  change (k : ℝ) ^ 2 ≤ n
  suffices hs : k ^ 2 ≤ n by exact_mod_cast hs
  have hz : Erdos962.Erdos962Prop n 0 := ⟨0, Nat.zero_le _, by simp⟩
  have h : Erdos962.Erdos962Prop n k := Nat.findGreatest_spec (Nat.zero_le n) hz
  obtain ⟨m, hmn, hall⟩ := h
  by_contra! hs
  have hk : 0 < k := by
    apply Nat.pos_of_ne_zero
    intro hzero
    simp [hzero] at hs
  have hq : m / k < k := (Nat.div_lt_iff_lt_mul hk).mpr
    (by simpa [pow_two] using hmn.trans_lt hs)
  have hr := Nat.mod_lt m hk
  have hd := Nat.mod_add_div m k
  obtain ⟨p, hp, hpk, hdiv⟩ := hall (k - m % k) ⟨by omega, by omega⟩
  have heq : m + (k - m % k) = k * (m / k + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [heq] at hdiv
  exact hpk.not_ge ((hp.dvd_mul.mp hdiv).elim (Nat.le_of_dvd hk)
    (fun hd => (Nat.le_of_dvd (Nat.succ_pos (m / k)) hd).trans (Nat.succ_le_of_lt hq)))
