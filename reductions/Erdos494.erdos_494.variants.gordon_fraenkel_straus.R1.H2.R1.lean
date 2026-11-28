import OMAReductions.R_Erdos494_erdos_494_variants_gordon_fraenkel_straus_R1
import Mathlib

/-! Separate the coprime smooth-number gap theorem from the scaling
bound for a fixed primitive pair. Dividing by the greatest common
divisor keeps the same relative-gap inequality. -/
open Set Real
namespace OMA.R_Erdos494_erdos_494_variants_gordon_fraenkel_straus_R1_H2_R1

/-- The smooth-gap result for coprime pairs. Its primitive form follows
from the standard smooth-number corollary of Ridout's theorem. -/
def H1 : Prop := ∀ (s : ℕ) (ε : ℝ), 0 < ε →
  Set.Finite {pq : ℕ × ℕ | 0 < pq.1 ∧ 0 < pq.2 ∧
    (∀ p : ℕ, p.Prime → p ∣ pq.1 → p ≤ s) ∧
    (∀ p : ℕ, p.Prime → p ∣ pq.2 → p ≤ s) ∧
    pq.1 ≠ pq.2 ∧ Nat.Coprime pq.1 pq.2 ∧
    |(pq.2 : ℝ) - (pq.1 : ℝ)| < (pq.2 : ℝ) ^ (1 - ε)}

/-- For a fixed nontrivial pair, the relative-gap condition allows
only finitely many positive common scaling factors. -/
def H2 : Prop := ∀ (ε : ℝ) (a b : ℕ), 0 < ε → 0 < a → 0 < b → a ≠ b →
  Set.Finite {d : ℕ | 0 < d ∧
    |((d*b : ℕ) : ℝ) - ((d*a : ℕ) : ℝ)| < ((d*b : ℕ) : ℝ) ^ (1 - ε)}

theorem gap_divide {ε : ℝ} (he : 0 < ε) {a b d : ℕ} (hd : 0 < d) :
    |((d*b : ℕ) : ℝ) - ((d*a : ℕ) : ℝ)| < ((d*b : ℕ) : ℝ) ^ (1 - ε) →
    |(b : ℝ) - (a : ℝ)| < (b : ℝ) ^ (1 - ε) := by
  intro h
  have dp : (0:ℝ) < (d:ℝ) := by exact_mod_cast hd
  have d1 : (1:ℝ) ≤ (d:ℝ) := by exact_mod_cast hd
  push_cast at h
  rw [← mul_sub,abs_mul,abs_of_pos dp,Real.mul_rpow dp.le (by positivity)] at h
  have le_d : (d:ℝ) ^ (1 - ε) ≤ (d:ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le d1
      (show 1-ε ≤ 1 by linarith)
  by_contra! hl
  have hdle := mul_le_mul_of_nonneg_left hl dp.le
  exact (not_lt_of_ge hdle)
    (h.trans_le (mul_le_mul_of_nonneg_right le_d (Real.rpow_nonneg (by positivity) _)))

theorem main : H1 → H2 → OMA.R_Erdos494_erdos_494_variants_gordon_fraenkel_straus_R1.H2 := by
  intro hprimitive hscale s ε he
  let P : Set (ℕ × ℕ) := {pq | 0 < pq.1 ∧ 0 < pq.2 ∧
    (∀ p : ℕ, p.Prime → p ∣ pq.1 → p ≤ s) ∧
    (∀ p : ℕ, p.Prime → p ∣ pq.2 → p ≤ s) ∧
    pq.1 ≠ pq.2 ∧ Nat.Coprime pq.1 pq.2 ∧
    |(pq.2 : ℝ) - (pq.1 : ℝ)| < (pq.2 : ℝ) ^ (1 - ε)}
  let S (p : ℕ × ℕ) : Set ℕ := {d | 0 < d ∧
    |((d*p.2 : ℕ) : ℝ) - ((d*p.1 : ℕ) : ℝ)| < ((d*p.2 : ℕ) : ℝ) ^ (1 - ε)}
  let chart (p : ℕ × ℕ) (d : ℕ) := (d*p.1,d*p.2)
  let U := ⋃ p ∈ P, chart p '' S p
  have pFin : P.Finite := hprimitive s ε he
  have uFin : U.Finite := pFin.biUnion (fun p hp ↦
    (hscale ε p.1 p.2 he hp.1 hp.2.1 hp.2.2.2.2.1).image (chart p))
  refine uFin.subset ?_
  rintro ⟨a,b⟩ ⟨ha,hb,sa,sb,hne,hgap⟩
  let d := Nat.gcd a b
  let x := a/d
  let y := b/d
  have hd : 0 < d := Nat.gcd_pos_of_pos_left _ ha
  have dx : d*x=a := Nat.mul_div_cancel' (Nat.gcd_dvd_left a b)
  have dy : d*y=b := Nat.mul_div_cancel' (Nat.gcd_dvd_right a b)
  have hx : 0 < x := Nat.div_pos (Nat.gcd_le_left b ha) hd
  have hy : 0 < y := Nat.div_pos (Nat.gcd_le_right a hb) hd
  have nxy : x ≠ y := by
    intro h
    apply hne
    rw [← dx,← dy,h]
  have sx (p : ℕ) (hp : p.Prime) (hp' : p ∣ x) : p ≤ s :=
    sa p hp (hp'.trans ⟨d,by simpa [Nat.mul_comm] using dx.symm⟩)
  have sy (p : ℕ) (hp : p.Prime) (hp' : p ∣ y) : p ≤ s :=
    sb p hp (hp'.trans ⟨d,by simpa [Nat.mul_comm] using dy.symm⟩)
  have hs : d ∈ S (x,y) := ⟨hd,by simpa only [dx,dy] using hgap⟩
  have hc : Nat.Coprime x y := Nat.coprime_div_gcd_div_gcd hd
  have hp : (x,y) ∈ P := ⟨hx,hy,sx,sy,nxy,hc,gap_divide he hd hs.2⟩
  exact Set.mem_iUnion.mpr ⟨(x,y),Set.mem_iUnion.mpr ⟨hp,d,hs,Prod.ext dx dy⟩⟩

end OMA.R_Erdos494_erdos_494_variants_gordon_fraenkel_straus_R1_H2_R1
