import OMAStatements.S_oeis_a082630
import Mathlib.Tactic

open OMA.S_oeis_a082630

namespace InsertionPell

-- C and S are the coefficients of (2+sqrt(3))^k.
private def pair : ℕ → ℕ × ℕ
  | 0 => (1,0)
  | k+1 =>
    let (c,s) := pair k
    (2*c+3*s,c+2*s)

private def C (k : ℕ) := (pair k).1
private def S (k : ℕ) := (pair k).2
private lemma c_next (k : ℕ) : C (k+1) = 2*C k+3*S k := rfl
private lemma s_next (k : ℕ) : S (k+1) = C k+2*S k := rfl

private lemma norm (k : ℕ) : (C k)^2 = 3*(S k)^2+1 := by
  induction k with
  | zero => decide
  | succ k ih => rw [c_next,s_next]; nlinarith only [ih]

private lemma bounds (k : ℕ) : S k < C k ∧ 5*S k < 3*C k := by
  induction k with
  | zero => decide
  | succ k ih => rw [c_next, s_next]; omega

private lemma stream_even (k : ℕ)
    (h : stream (2*k) = (C k+3*S k,C k+S k)) :
    stream (2*k+1) = (2*C k+4*S k,C k+S k) := by
  have g : ¬ 7*((C k+3*S k)+(C k+S k)) ≤ 11*(C k+3*S k) := by
    have := (bounds k).2
    omega
  rw [stream,h]
  simp [g]
  omega

private lemma stream_both (k : ℕ) :
    stream (2*k) = (C k+3*S k,C k+S k) ∧
    stream (2*k+1) = (2*C k+4*S k,C k+S k) := by
  suffices h : stream (2*k) = (C k+3*S k,C k+S k) from ⟨h,stream_even k h⟩
  induction k with
  | zero => decide
  | succ k ih =>
    have g : 7*((2*C k+4*S k)+(C k+S k)) ≤ 11*(2*C k+4*S k) := by omega
    rw [show 2*(k+1)=2*k+1+1 by omega, stream, stream_even k ih, c_next,s_next]
    simp [g]
    omega

private lemma lower_step k : lower (k+4) = 4*lower (k+2)-lower k := rfl
private lemma denom_step k :
    denominator (k+3) = (1+denominator (k+1)*denominator (k+2))/denominator k := rfl

private lemma numerators (k : ℕ) :
    lower (2*k)=3*S k ∧ lower (2*k+1)=C k+3*S k ∧
    lower (2*k+2)=3*C k+6*S k ∧ lower (2*k+3)=5*C k+9*S k := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨h0,h1,h2,h3⟩ := ih
    have h4 := lower_step (2*k)
    have h5 := lower_step (2*k+1)
    rw [c_next, s_next]
    simp only [Nat.mul_succ, Nat.add_assoc, Nat.reduceAdd] at *
    omega

private lemma denominators (k : ℕ) :
    denominator (2*k+1)=C k ∧ denominator (2*k+2)=C k+S k ∧
    denominator (2*k+3)=2*C k+3*S k := by
  induction k with
  | zero => decide
  | succ k ih =>
    obtain ⟨h1,h2,h3⟩ := ih
    have hc : 0 < C k := by have := (bounds k).1; omega
    have hcs : 0 < C k+S k := by omega
    have d1 : 1+(C k+S k)*(2*C k+3*S k) = (3*C k+5*S k)*C k := by
      nlinarith only [norm k]
    have d2 : 1+(2*C k+3*S k)*(3*C k+5*S k) = (7*C k+12*S k)*(C k+S k) := by
      nlinarith only [norm k]
    have h4 : denominator (2*k+4) = 3*C k+5*S k := by
      rw [denom_step (2*k+1),h2,h3,h1,d1,Nat.mul_div_cancel _ hc]
    have h5 : denominator (2*k+5) = 7*C k+12*S k := by
      rw [denom_step (2*k+2),h3,h4,h2,d2,Nat.mul_div_cancel _ hcs]
    rw [c_next,s_next]
    simp only [Nat.mul_succ, Nat.add_assoc, Nat.reduceAdd] at *
    omega

private lemma lucas_eq (k : ℕ) : lucasU k=S k := by
  induction k using Nat.twoStepInduction with
  | zero => decide
  | one => decide
  | more k h h' =>
    rw [lucasU,h',h,s_next (k+1),c_next,s_next]
    omega

private lemma product_pair (k j : ℕ) :
    C (k+j)=C k*C j+3*S k*S j ∧ S (k+j)=C k*S j+S k*C j := by
  induction j with
  | zero => simp [C,S,pair]
  | succ j ih =>
    simp only [Nat.add_succ, c_next (k+j), s_next (k+j), c_next j, s_next j, ih.1, ih.2]
    constructor <;> ring

private lemma pell_iff {x y : ℕ} : pell x y ↔
    0 < x ∧ (3*x^2=y^2+2 ∨ 3*x^2=y^2+3) := by
  have residues : y^2%3=0 ∨ y^2%3=1 := by
    rw [Nat.pow_mod]
    have hy := Nat.mod_lt y (by decide : 0<3)
    interval_cases h : y%3 <;> decide
  unfold pell
  omega

private lemma pell_orbits (x y : ℕ) (hp : pell x y) :
    ∃ k : ℕ, (x=C k ∧ y=3*S k) ∨ (x=C k+S k ∧ y=C k+3*S k) := by
  induction x using Nat.strong_induction_on generalizing y with
  | h x ih =>
    obtain ⟨pos,eq⟩ := pell_iff.mp hp
    by_cases small : x = 1
    · subst x
      have hy : y ≤ 1 := by
        by_contra! h2
        have bound := Nat.mul_le_mul h2 h2
        rcases eq with he | he <;> nlinarith
      interval_cases y
      · exact ⟨0,Or.inl (by decide)⟩
      · exact ⟨0,Or.inr (by decide)⟩
    · have x2 : 2 ≤ x := by omega
      have square : 4 ≤ x*x := Nat.mul_le_mul x2 x2
      have xy : x < y := by
        by_contra! hy
        have sq := Nat.mul_le_mul hy hy
        rcases eq with he | he <;> nlinarith
      have yx : y < 2*x := by
        by_contra! hy
        have sq := Nat.mul_le_mul hy hy
        rcases eq with he | he <;> nlinarith
      have half : 3*x ≤ 2*y := by
        by_contra! hy
        have sq := Nat.mul_self_lt_mul_self hy
        rcases eq with he | he <;> nlinarith
      let u := 2*x-y
      let v := 2*y-3*x
      have hu : u+y=2*x := Nat.sub_add_cancel yx.le
      have hv : v+3*x=2*y := Nat.sub_add_cancel half
      have balance : 3*u^2+y^2=v^2+3*x^2 := by
        have ui : (u:ℤ)=2*(x:ℤ)-y := by dsimp [u]; rw [Nat.cast_sub yx.le]; push_cast; rfl
        have vi : (v:ℤ)=2*(y:ℤ)-3*x := by dsimp [v]; rw [Nat.cast_sub half]; push_cast; rfl
        exact_mod_cast (show 3*(u:ℤ)^2+(y:ℤ)^2=(v:ℤ)^2+3*(x:ℤ)^2 by rw [ui,vi]; ring)
      have good : pell u v := pell_iff.mpr ⟨by omega, by omega⟩
      obtain ⟨k, prior | prior⟩ := ih u (by omega) v good
      · exact ⟨k+1, Or.inl (by rw [c_next,s_next]; omega)⟩
      · exact ⟨k+1, Or.inr (by rw [c_next,s_next]; omega)⟩

private lemma values (k : ℕ) : a (2*k+1)=C k+3*S k ∧ a (2*k+2)=2*C k+4*S k := by
  simp [a, show 2*k+2-1=2*k+1 by omega, (stream_both k).1, (stream_both k).2]

private lemma parities (n : ℕ) (hn : 1 ≤ n) : ∃ k, n=2*k+1 ∨ n=2*k+2 :=
  ⟨(n-1)/2, by omega⟩

private lemma terms (n : ℕ) (hn : 1 ≤ n) :
    pell (denominator n) (lower (n-1)) ∧ a n=lower (n-1)+denominator n := by
  obtain ⟨k, rfl | rfl⟩ := parities n hn
  · rw [Nat.add_sub_cancel, (denominators k).1, (numerators k).1, (values k).1]
    exact ⟨pell_iff.mpr ⟨by have := (bounds k).1; omega, Or.inr (by nlinarith only [norm k])⟩,
      by omega⟩
  · rw [show 2*k+2-1=2*k+1 by omega, (denominators k).2.1, (numerators k).2.1, (values k).2]
    exact ⟨pell_iff.mpr ⟨by have := (bounds k).1; omega, Or.inl (by nlinarith only [norm k])⟩,
      by omega⟩

private lemma exhaustive (x y : ℕ) (hp : pell x y) :
    ∃ n : ℕ, 1 ≤ n ∧ denominator n=x ∧ lower (n-1)=y := by
  obtain ⟨k, h | h⟩ := pell_orbits x y hp
  · refine ⟨2*k+1, by omega, ?_, ?_⟩
    · rw [(denominators k).1, h.1]
    · rw [Nat.add_sub_cancel, (numerators k).1, h.2]
  · refine ⟨2*k+2, by omega, ?_, ?_⟩
    · rw [(denominators k).2.1, h.1]
    · rw [show 2*k+2-1=2*k+1 by omega, (numerators k).2.1, h.2]

private lemma quotient (n : ℕ) (hn : 1 ≤ n) : a n = lucasU n/denominator (n+1) := by
  obtain ⟨k,rfl | rfl⟩ := parities n hn
  · have twice := product_pair k k
    have u : S (2*k+1)=(C k+3*S k)*(C k+S k) := by
      rw [s_next, show 2*k=k+k by omega, twice.1, twice.2]
      ring
    have hp : 0<C k+S k := by have := (bounds k).1; omega
    rw [(values k).1, lucas_eq, u, (denominators k).2.1, Nat.mul_div_cancel _ hp]
  · have twice := product_pair (k+1) (k+1)
    have u : S (2*k+2)=(2*C k+4*S k)*(2*C k+3*S k) := by
      rw [show 2*k+2=(k+1)+(k+1) by omega, twice.2, c_next,s_next]
      ring
    have hp : 0<2*C k+3*S k := by have := (bounds k).1; omega
    rw [(values k).2, lucas_eq, u, (denominators k).2.2, Nat.mul_div_cancel _ hp]

end InsertionPell

theorem OMA.solution : type_of% @OMA.S_oeis_a082630.main :=
  ⟨InsertionPell.terms, InsertionPell.exhaustive, InsertionPell.quotient⟩
