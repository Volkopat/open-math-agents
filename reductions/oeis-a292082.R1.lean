import OMAStatements.S_oeis_a292082
import Mathlib
namespace OMA.R_oeis_a292082_R1
open Pell
open Pell.Solution₁

lemma fundamental : Pell.IsFundamental (Solution₁.mk (d:=2) 3 2 (by decide)) := by
  refine ⟨by decide,by decide,?_⟩
  intro b hb
  change 3 ≤ b.x
  by_contra! small
  have eqn : b.x=2 := by omega
  have e := b.prop
  rw [eqn] at e
  omega

lemma odd_dvd (a : Solution₁ 2) (k : ℕ) : a.x ∣ (a^(2*k+1)).x := by
  induction k with
  | zero => simp
  | succ k ih =>
    obtain ⟨c,hc⟩ := ih
    rw [show 2*(k+1)+1=(2*k+1)+1+1 by omega,pow_succ,pow_succ,x_mul,x_mul,y_mul,hc]
    exact ⟨a.x^2*c + 4*(a^(2*k+1)).y*a.y + 2*c*a.y^2, by ring⟩

lemma iterate_coordinates (n : ℕ) :
    let a := Solution₁.mk (d:=2) 3 2 (by decide)
    (a^(2^n)).x = ((Nat.rec 3 (fun _ k => 2*k^2-1) n : ℕ) : ℤ) ∧
    2 ≤ (Nat.rec 3 (fun _ k => 2*k^2-1) n : ℕ) := by
  let a := Solution₁.mk (d:=2) 3 2 (by decide)
  change (a^(2^n)).x = _ ∧ _
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    let c : ℕ := Nat.rec 3 (fun _ k => 2*k^2-1) n
    obtain ⟨ix,hc⟩ := ih
    change (a^(2^(n+1))).x = ((2*c^2-1:ℕ):ℤ) ∧ 2 ≤ 2*c^2-1
    change (a^(2^n)).x = Int.ofNat c at ix
    change 2 ≤ c at hc
    have hsq : 4 ≤ c^2 := by nlinarith
    constructor
    · rw [Nat.pow_succ,pow_mul,pow_two,x_mul,Nat.cast_sub (by omega : 1 ≤ 2*c^2)]
      push_cast
      have h := (a^(2^n)).prop
      rw [ix] at h ⊢
      change Int.ofNat c * Int.ofNat c + 2 * ((a^(2^n)).y * (a^(2^n)).y) = 2*(Int.ofNat c)^2-1
      nlinarith
    · omega

lemma classify (p : ℕ) (hp : p.Prime) (k : ℕ) (hk : p^2-1=2*k^2) :
    ∃ n : ℕ, p = Nat.rec 3 (fun _ t => 2*t^2-1) n := by
  have pp : 1 ≤ p^2 := Nat.one_le_pow _ _ hp.pos
  have e : p^2=1+2*k^2 := by omega
  have ez : (p:ℤ)^2-2*(k:ℤ)^2=1 := sub_eq_iff_eq_add.mpr (by exact_mod_cast e)
  let a := Solution₁.mk (d:=2) 3 2 (by decide)
  let b := Solution₁.mk (d:=2) (p:ℤ) (k:ℤ) ez
  obtain ⟨j,hj⟩ := fundamental.eq_pow_of_nonneg (a:=b) (by change 0 < (p:ℤ); exact_mod_cast hp.pos)
    (by change 0 ≤ (k:ℤ); positivity)
  have coord : (p:ℤ) = (a^j).x := congrArg Solution₁.x hj
  have jn : j≠0 := by
    rintro rfl
    simp [a] at coord
    have := hp.two_le
    omega
  obtain ⟨n,m,⟨t,ht⟩,eqn⟩ := Nat.exists_eq_two_pow_mul_odd jn
  have mul : j=2^n*(2*t+1) := by rw [eqn,ht]
  have d := odd_dvd (a^(2^n)) t
  rw [←pow_mul,←mul,←coord] at d
  obtain ⟨cp,ge⟩ := iterate_coordinates n
  change (a^(2^n)).x = _ at cp
  rw [cp] at d
  have dn : (Nat.rec 3 (fun _ t => 2*t^2-1) n : ℕ) ∣ p := by exact_mod_cast d
  rcases (Nat.dvd_prime hp).mp dn with h|h
  · omega
  · exact ⟨n,h.symm⟩

lemma reverse_classification (n : ℕ) :
    let c : ℕ := Nat.rec 3 (fun _ k => 2*k^2-1) n
    ∃ k : ℕ, c^2-1=2*k^2 := by
  let a := Solution₁.mk (d:=2) 3 2 (by decide)
  let b := a^(2^n)
  let c : ℕ := Nat.rec 3 (fun _ k => 2*k^2-1) n
  change ∃ k : ℕ, c^2-1=2*k^2
  obtain ⟨hv,_⟩ := iterate_coordinates n
  change b.x=(Nat.cast c : ℤ) at hv
  refine ⟨b.y.natAbs,?_⟩
  have eqn := b.prop
  have hc : (Nat.cast c : ℤ)^2=1+2*(Nat.cast b.y.natAbs : ℤ)^2 := by
    rw [Int.natCast_natAbs,sq_abs,←hv]
    linarith
  have h : c^2=1+2*b.y.natAbs^2 := by exact_mod_cast hc
  omega

def H1 : Prop := ∀ p k : ℕ, p.Prime → p^2-1=2*k^2 →
    ∃ n : ℕ, p = Nat.rec 3 (fun _ t => 2*t^2-1) n

lemma first_step : H1 := fun p k hp hk => classify p hp k hk

def H2 : Prop := ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ¬ (Nat.rec 3 (fun _ k => 2*k^2-1) n : ℕ).Prime

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a292082.main := by
  rintro prime_indices ⟨N,hN⟩
  let f := fun n : ℕ => (Nat.rec 3 (fun _ k => 2*k^2-1) n : ℕ)
  apply ((Finset.range N).finite_toSet.image f).subset
  rintro p ⟨hp,k,hk⟩
  obtain ⟨n,hn⟩ := prime_indices p k hp hk
  refine ⟨n,?_,hn.symm⟩
  change n ∈ Finset.range N
  apply Finset.mem_range.mpr
  by_contra! late
  exact hN n late (hn ▸ hp)
end OMA.R_oeis_a292082_R1
