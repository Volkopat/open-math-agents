import OMAReductions.R_oeis_a397683_R1
import Mathlib.RingTheory.ZMod.UnitsCyclic

-- Prime-level existence follows mathematically from S. D. Cohen, Pairs of primitive roots.
-- This reduction continues Ciphore's prime-power step for OEIS A397683.
namespace OMA.R_oeis_a397683_R1_H1_R1

def H1 : Prop := ∀ p : ℕ, p.Prime → Odd p → p ≠ 3 → p ≠ 7 →
  ∃ x d : ℕ, 1 ≤ x ∧ x + 1 < p ∧ d ≠ 0 ∧
    orderOf (x : ZMod p) = d ∧ orderOf ((x+1 : ℕ) : ZMod p) = d

-- A simultaneous first-order lift. For y = x + kp each nonvanishing
-- condition rules out at most one digit k by the binomial expansion.
def H2 : Prop := ∀ p x d : ℕ, p.Prime → Odd p → 1 ≤ x → x+1 < p → d ≠ 0 →
  orderOf (x : ZMod p) = d → orderOf ((x+1 : ℕ) : ZMod p) = d →
  ∃ y t u : ℕ, 1 ≤ y ∧ y < p^2 ∧ y ≡ x [MOD p] ∧
    y^d = 1+p*t ∧ (y+1)^d = 1+p*u ∧ ¬ (p : ℤ) ∣ (t : ℤ) ∧ ¬ (p : ℤ) ∣ (u : ℤ)

theorem primePowerOrderLift {p x d t : ℕ} (hp : p.Prime) (ho : p ≠ 2)
    (hd : d ≠ 0) (hbase : orderOf (x : ZMod p) = d)
    (hpow : x ^ d = 1 + p * t) (ht : ¬ (p : ℤ) ∣ (t : ℤ)) (n : ℕ) :
    orderOf (x : ZMod (p ^ (n+1))) = d * p ^ n := by
  let hmap := ZMod.castHom (dvd_pow_self p (Nat.succ_ne_zero n)) (ZMod p)
  have hdiv := orderOf_map_dvd hmap.toMonoidHom (x : ZMod (p^(n+1)))
  have hdiv' : d ∣ orderOf (x : ZMod (p^(n+1))) := by
    simpa [hmap, hbase] using hdiv
  have h := ZMod.orderOf_one_add_mul_prime hp ho (t : ℤ) ht n
  have he : (x : ZMod (p^(n+1)))^d = 1 + (p : ℕ) * (t : ℤ) := by
    exact_mod_cast congrArg (fun z : ℕ => (z : ZMod (p^(n+1)))) hpow
  rw [← he, orderOf_pow_of_dvd hd hdiv'] at h
  rw [← h, Nat.mul_div_cancel' hdiv']


theorem main : H1 → H2 → OMA.R_oeis_a397683_R1.H1 := by
  intro h₁ h₂ p a hp ho hp3 hp7 ha
  obtain ⟨x,d,hx,hxp,hd,h₀,h₁'⟩ := h₁ p hp ho hp3 hp7
  obtain ⟨y,t,u,hy,hyp,hyx,ht,hu,hpt,hpu⟩ := h₂ p x d hp ho hx hxp hd h₀ h₁'
  have certify (z : ℕ) (hz : 1 ≤ z) (hzp : z < p^a) (hc : z.Coprime p)
      (hc' : (z+1).Coprime p)
      (he : orderOf (z : ZMod (p^a)) = orderOf ((z+1 : ℕ) : ZMod (p^a))) :
      OMA.S_oeis_a397683.f (p^a) ≠ 0 := by
    have hg := one_lt_pow₀ hp.one_lt (by omega : a ≠ 0)
    rw [OMA.S_oeis_a397683.f, if_neg hg.ne']
    exact Nat.ne_of_gt (Finset.card_pos.mpr ⟨z, Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨hz,hzp⟩, hc.pow_right a, hc'.pow_right a, he⟩⟩)
  have cop (z : ℕ) (hz : 0 < z) (hzp : z < p) : z.Coprime p :=
    (hp.coprime_iff_not_dvd.mpr (fun h => (Nat.le_of_dvd hz h).not_gt hzp)).symm
  by_cases h : a = 1
  · apply certify x hx (by simpa [h] using (by omega : x < p)) (cop x hx (by omega))
      (cop _ (by omega) hxp)
    rw [h, pow_one]; exact h₀.trans h₁'.symm
  · obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : a ≠ 0)
    have hcast := (ZMod.natCast_eq_natCast_iff ..).mpr hyx
    have hsucc := (ZMod.natCast_eq_natCast_iff ..).mpr (hyx.add_right 1)
    have hcop (z w : ℕ) (e : z ≡ w [MOD p]) (hw : w.Coprime p) : z.Coprime p := by
      exact e.gcd_eq.trans hw
    apply certify y hy (hyp.trans_le (Nat.pow_le_pow_right hp.pos (by omega)))
      (hcop _ _ hyx (cop _ hx (by omega))) (hcop _ _ (hyx.add_right 1) (cop _ (by omega) hxp))
    exact (primePowerOrderLift hp (by rintro rfl; obtain ⟨k,hk⟩ := ho; omega)
      hd (congrArg orderOf hcast |>.trans h₀) ht hpt n).trans
      (primePowerOrderLift hp (by rintro rfl; obtain ⟨k,hk⟩ := ho; omega)
      hd (congrArg orderOf hsucc |>.trans h₁') hu hpu n).symm

end OMA.R_oeis_a397683_R1_H1_R1
