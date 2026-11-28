import OMAReductions.R_Erdos473_erdos_473_variants_finite_R1
import Mathlib

/-! The two-reflection construction of Hong-Bin Chen, Hung-Lin Fu and
Jun-Yi Guo, *Hamiltonicity in Prime Sum Graphs*, Graphs and Combinatorics
37 (2021), DOI 10.1007/s00373-020-02241-1.

Odd vertices are 2i+1 and even vertices are 2j+2, indexed modulo m.
A reflection matching i+j=r mod m has at most two possible edge sums.
Alternating reflections with indices u and v translates the odd index by
v−u, hence gives one circle when the difference is coprime to m. -/

namespace PrimeCircles

private theorem prime_sum_of_residue {m r i j : ℕ}
    (hr : r < m) (hi : i < m) (hj : j < m)
    (he : Nat.ModEq m (i+j) r) (low : (2*r+3).Prime)
    (high : r+1 < m → (2*r+3+2*m).Prime) : (2*(i+j)+3).Prime := by
  change (i+j)%m = r%m at he
  rw [Nat.mod_eq_of_lt hr] at he
  by_cases hs : i+j < m
  · rw [Nat.mod_eq_of_lt hs] at he
    simpa [he] using low
  · rw [Nat.mod_eq_sub_mod (by omega : m ≤ i+j), Nat.mod_eq_of_lt (by omega)] at he
    have h := high (by omega)
    convert h using 1
    omega

theorem reflection_circle (m u v : ℕ) (hm : 0 < m) (huv : u < v) (hv : v < m)
    (hcop : (v-u).Coprime m)
    (hulo : (2*u+3).Prime) (huhi : u+1 < m → (2*u+3+2*m).Prime)
    (hvlo : (2*v+3).Prime) (hvhi : v+1 < m → (2*v+3+2*m).Prime) :
    ∃ a : Fin (2*m) ≃ Fin (2*m), ∀ k : Fin (2*m),
      ((a k).val + 1 + (a ⟨(k.val+1)%(2*m), Nat.mod_lt _ (by omega)⟩).val + 1).Prime := by
  let d := v-u
  let i (k : Fin (2*m)) := d*(k.val/2)%m
  let j (k : Fin (2*m)) := if i k ≤ u then u-i k else u+m-i k
  have hi (k : Fin (2*m)) : i k < m := Nat.mod_lt _ hm
  have hj (k : Fin (2*m)) : j k < m := by
    have := hi k
    dsimp [j]
    split <;> omega
  have pair (k : Fin (2*m)) : Nat.ModEq m (i k+j k) u := by
    dsimp only [j]
    split
    · rw [show i k+(u-i k)=u by omega]
    · have := hi k
      rw [show i k+(u+m-i k)=u+m by omega]
      exact Nat.modEq_add_modulus_iff.mpr Nat.ModEq.rfl |>.symm
  let f (k : Fin (2*m)) : Fin (2*m) :=
    ⟨if k.val%2=0 then 2*i k else 2*j k+1, by
      have := hi k
      have := hj k
      split <;> omega⟩
  have sameHalf (k l : Fin (2*m)) (h : i k=i l) : k.val/2=l.val/2 := by
    have e : Nat.ModEq m (d*(k.val/2)) (d*(l.val/2)) := h
    exact (Nat.ModEq.cancel_left_of_coprime hcop.symm e).eq_of_lt_of_lt
      (by have := k.isLt; omega) (by have := l.isLt; omega)
  have injective : Function.Injective f := by
    intro k l h
    have hv' := congrArg Fin.val h
    change (if k.val%2=0 then 2*i k else 2*j k+1) =
      (if l.val%2=0 then 2*i l else 2*j l+1) at hv'
    apply Fin.ext
    split at hv' <;> split at hv'
    · have := sameHalf k l (by omega)
      omega
    · omega
    · omega
    · have hje : j k = j l := by omega
      have hjk := pair k
      have hjl := pair l
      rw [hje] at hjk
      have eq := (Nat.ModEq.add_right_cancel' _ (hjk.trans hjl.symm)).eq_of_lt_of_lt (hi k) (hi l)
      have := sameHalf k l eq
      omega
  let e := Equiv.ofBijective f ⟨injective, Finite.surjective_of_injective injective⟩
  refine ⟨e, ?_⟩
  intro k
  let t : Fin (2*m) := ⟨(k.val+1)%(2*m), Nat.mod_lt _ (by omega)⟩
  have kt := k.isLt
  change ((if k.val%2=0 then 2*i k else 2*j k+1) + 1 +
    (if t.val%2=0 then 2*i t else 2*j t+1) + 1).Prime
  have next : t.val = if k.val+1 < 2*m then k.val+1 else 0 := by
    dsimp [t]
    split
    · exact Nat.mod_eq_of_lt ‹_›
    · rw [show k.val+1 = 2*m by omega, Nat.mod_self]
  by_cases even : k.val%2=0
  · have nt : t.val=k.val+1 := by rw [next,if_pos (by omega)]
    have ij : i t=i k := by
      have hk : t.val/2=k.val/2 := by omega
      simp only [i,hk]
    have jj : j t=j k := by simp only [j,ij]
    rw [if_pos even,if_neg (by omega),jj]
    convert prime_sum_of_residue (by omega : u < m) (hi k) (hj k) (pair k) hulo huhi using 1
    omega
  · have ev : t.val%2=0 := by rw [next]; split <;> omega
    have step : Nat.ModEq m (t.val/2) (k.val/2+1) := by
      rw [next]
      split
      · rw [show (k.val+1)/2=k.val/2+1 by omega]
      · rw [show k.val/2+1=m by omega]
        simp [Nat.ModEq]
    have moved : Nat.ModEq m (i t) (i k+d) := by
      calc
        i t ≡ d*(t.val/2) [MOD m] := Nat.mod_modEq _ _
        _ ≡ d*(k.val/2+1) [MOD m] := step.mul_left d
        _ = d*(k.val/2)+d := by ring
        _ ≡ i k+d [MOD m] := (Nat.mod_modEq _ _).symm.add_right d
    have hpair : Nat.ModEq m (i t+j k) v := by
      calc
        i t+j k ≡ i k+d+j k [MOD m] := moved.add_right _
        _ = i k+j k+d := by omega
        _ ≡ u+d [MOD m] := (pair k).add_right _
        _ = v := by dsimp [d]; omega
    rw [if_neg even,if_pos ev]
    convert prime_sum_of_residue hv (hi t) (hj k) hpair hvlo hvhi using 1
    omega

end PrimeCircles


namespace OMA.R_Erdos473_erdos_473_variants_finite_R1_H1_R1

/-- Finite arithmetic certificates for the two-reflection criterion. -/
def H1 : Prop :=
  ∀ m : ℕ, 10 ≤ m → m ≤ 5000 → m % 2 = 0 →
    ∃ u v, u < v ∧ v < m ∧ (v-u).Coprime m ∧
      (2*u+3).Prime ∧ ((u+1 < m) → (2*u+3+2*m).Prime) ∧
      (2*v+3).Prime ∧ ((v+1 < m) → (2*v+3+2*m).Prime)

/-- Larger orders for which the reflection criterion fails. -/
def H2 : Prop :=
  ∀ m : ℕ, (hm : 5000 < m) → m % 2 = 0 →
    (¬ ∃ u v, u < v ∧ v < m ∧ (v-u).Coprime m ∧
      (2*u+3).Prime ∧ ((u+1 < m) → (2*u+3+2*m).Prime) ∧
      (2*v+3).Prime ∧ ((v+1 < m) → (2*v+3+2*m).Prime)) →
    ∃ a : Fin (2*m) ≃ Fin (2*m), ∀ k : Fin (2*m),
      ((a k).val + 1 + (a ⟨(k.val+1)%(2*m), Nat.mod_lt _ (by omega)⟩).val + 1).Prime

theorem main : H1 → H2 → OMA.R_Erdos473_erdos_473_variants_finite_R1.H1 := by
  intro small rest n hn even
  obtain ⟨m,rfl⟩ : ∃ m, n = 2*m := ⟨n/2,by omega⟩
  have hlo : 10 ≤ m := by omega
  have he : m % 2 = 0 := by omega
  by_cases h : ∃ u v, u < v ∧ v < m ∧ (v-u).Coprime m ∧
      (2*u+3).Prime ∧ ((u+1 < m) → (2*u+3+2*m).Prime) ∧
      (2*v+3).Prime ∧ ((v+1 < m) → (2*v+3+2*m).Prime)
  · obtain ⟨u,v,huv,hv,coprime,pl,ph,ql,qh⟩ := h
    exact PrimeCircles.reflection_circle m u v (by omega) huv hv coprime pl ph ql qh
  · exact rest m (by
      by_contra! bound
      exact h (small m hlo bound he)) he h

end OMA.R_Erdos473_erdos_473_variants_finite_R1_H1_R1
