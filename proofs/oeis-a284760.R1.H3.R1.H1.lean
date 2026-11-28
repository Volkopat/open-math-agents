import OMAReductions.R_oeis_a284760_R1_H3_R1
import Mathlib

/-! The prime-local obstruction for Meštrović's A284760 power sum.
Compare Carlitz–von Staudt and Meštrović, arXiv:1211.4570, §2.4.
Here the prime occurs exactly once, so complete residue blocks and Fermat's
theorem suffice. -/
namespace OMA.PowerSum284760
open Finset Nat

private theorem taylor {R : Type*} [CommRing R] (x y:R) (hy:y^2=0) (e:ℕ) :
    (x+y)^e=x^e+e*x^(e-1)*y := by
  cases e with
  | zero => simp
  | succ e =>
    induction e with
    | zero=>simp
    | succ e ih =>
      rw [pow_succ (x+y),ih]
      simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,pow_succ]
      linear_combination ((e:R)+1)*x^e*hy

private theorem blocks {R : Type*} [AddCommMonoid R] (f : ℕ→R) (m k : ℕ) :
    (∑i∈range (m*k),f i)=∑j∈range k,∑i∈range m,f (m*j+i) := by
  induction k with
  | zero=>simp
  | succ k ih=>rw [Nat.mul_succ,sum_range_succ,sum_range_add,ih]

private theorem blocks_cast (m k e : ℕ) :
    (∑i∈range (m*k), (i:ZMod m)^e)=(k:ZMod m)*∑i∈range m,(i:ZMod m)^e := by
  rw [blocks];simp

private theorem base_nonzero {p e : ℕ} (hp:p.Prime) (ep:0<e) (he:p-1∣e) :
    (∑ i∈range p,(i:ZMod p)^e)≠0 := by
  let _ : Fact p.Prime := ⟨hp⟩
  have h1:=sum_range_add_sum_Ico (fun i:ℕ=>(i:ZMod p)^e) hp.one_le
  rw [←h1]
  have same (i) (hi:i∈Ico 1 p) : (i:ZMod p)^e=1 := by
    have nz : (i:ZMod p)≠0 := by
      intro h
      have := Nat.le_of_dvd (mem_Ico.mp hi).1 ((ZMod.natCast_eq_zero_iff ..).mp h)
      exact (mem_Ico.mp hi).2.not_ge this
    obtain ⟨a,ha⟩:=he
    rw [ha,pow_mul,ZMod.pow_card_sub_one_eq_one nz,one_pow]
  simp only [sum_congr rfl same,sum_const,Nat.card_Ico,nsmul_eq_mul,mul_one]
  simp [zero_pow ep.ne',Nat.cast_sub hp.one_le]

/-- A single factor of p reduces the complete residue sum directly to Fermat's theorem. -/
private theorem obstruction {p e : ℕ} (hp:p.Prime) (ep:0<e) (he:p-1∣e)
    (n:ℕ) (div:p∣n) (once:¬p^2∣n) : ¬n∣∑i∈range n,i^e := by
  obtain ⟨m,rfl⟩:=div
  have pm : ¬p∣m := fun h=>once (by simpa only [pow_two] using Nat.mul_dvd_mul_left p h)
  intro hz
  have hzero : (∑i∈range (p*m),(i:ZMod p)^e)=0 := by
    simpa only [←Nat.cast_pow,←Nat.cast_sum,ZMod.natCast_eq_zero_iff] using
      (show p∣∑i∈range (p*m),i^e from (dvd_mul_right p m).trans hz)
  rw [blocks_cast] at hzero
  let _ : Fact p.Prime:=⟨hp⟩
  exact (mul_ne_zero (fun hm=>pm ((ZMod.natCast_eq_zero_iff ..).mp hm)) (base_nonzero hp ep he)) hzero

private theorem reflect {n e : ℕ} (he : Odd e) :
    2*(∑i∈Ico 1 n,(i:ZMod (n^2))^e)=
      (n:ZMod (n^2))*e*(∑i∈Ico 1 n,(i:ZMod (n^2))^(e-1)) := by
  let R:= ZMod (n^2)
  have sq : (n:R)^2=0 := by rw [←Nat.cast_pow];exact ZMod.natCast_self _
  have mirror : (∑i∈Ico 1 n,((n-i:ℕ):R)^e)=∑i∈Ico 1 n,(i:R)^e := by
    apply sum_bij' (fun i _=>n-i) (fun i _=>n-i)
    all_goals intro i hi;obtain ⟨low,high⟩:=mem_Ico.mp hi
    all_goals first | exact mem_Ico.mpr ⟨by omega,by omega⟩ | omega | rfl
  have ev : Even (e-1) := by obtain ⟨b,hb⟩:=he;exact ⟨b,by omega⟩
  rw [two_mul]
  nth_rw 1 [←mirror]
  rw [←sum_add_distrib,mul_sum]
  apply sum_congr rfl
  intro i hi
  rw [Nat.cast_sub (mem_Ico.mp hi).2.le,sub_eq_neg_add,taylor _ _ sq,he.neg_pow,ev.neg_pow]
  ring

/-- A prime with p−1 ∣ n−3 already obstructs divisibility by n². -/
theorem local_obstruction {n p:ℕ} (odd:Odd n) (hp:p.Prime) (pn:p∣n) (once:¬p^2∣n) (he:p-1∣n-3) :
    ¬ n^2∣∑i∈Ico 1 n,i^(n-2) := by
  have pos:=odd.pos
  have hn:=Nat.le_of_dvd pos pn
  have big : 3≤n := by have :=hp.two_le;obtain ⟨b,h⟩:=odd;omega
  by_cases eq : n=3
  · subst n;decide
  have exp : 0<n-3 := by omega
  have eodd : Odd (n-2) := by obtain ⟨b,h⟩:=odd;exact ⟨b-1,by omega⟩
  intro zz
  have val := reflect (n:=n) eodd
  have left : (∑i∈Ico 1 n,(i:ZMod (n^2))^(n-2))=0 := by
    simpa only [←Nat.cast_pow,←Nat.cast_sum,ZMod.natCast_eq_zero_iff] using zz
  rw [left,mul_zero,show n-2-1=n-3 by omega] at val
  have sqdiv : n^2∣n*(n-2)*(∑i∈Ico 1 n,i^(n-3)) := by
    simpa only [←Nat.cast_pow,←Nat.cast_sum,←Nat.cast_mul,ZMod.natCast_eq_zero_iff] using val.symm
  rw [pow_two,mul_assoc n] at sqdiv
  have cut:=Nat.dvd_of_mul_dvd_mul_left pos sqdiv
  have cop : n.Coprime (n-2) :=
    (Nat.coprime_self_sub_right (by omega)).mpr (Nat.coprime_two_right.mpr odd)
  have dvd:=cop.dvd_of_dvd_mul_left cut
  have id := sum_range_add_sum_Ico (fun i:ℕ=>i^(n-3)) (show 1≤n by omega)
  have conv : (∑i∈Ico 1 n,i^(n-3))=∑i∈range n,i^(n-3) := by
    simpa [zero_pow exp.ne'] using id
  exact obstruction hp exp he n pn once (conv ▸ dvd)

end OMA.PowerSum284760

-- Reduction and case split: @adanthar. Formal proof: @JaviSoto (Codex).
theorem OMA.solution : OMA.R_oeis_a284760_R1_H3_R1.H1 := by
  intro n p odd hp pn once he z
  exact OMA.PowerSum284760.local_obstruction odd hp pn once he
    ((pow_dvd_pow n (by decide : 2≤4)).trans (Nat.dvd_of_mod_eq_zero z))


