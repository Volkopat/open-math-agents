import OMAStatements.S_mo_270442
import Mathlib

open Polynomial OMA.S_mo_270442

namespace DiscreteShift

abbrev P := ℤ[X]

def Pos (p : P) := ∀ i, 0 ≤ p.coeff i

lemma posC (k : ℤ) (hk : 0 ≤ k) : Pos (C k) := by
  intro i
  simp only [coeff_C]
  split <;> omega

lemma posN (k : ℕ) : Pos (k : P) := by
  simpa using posC (k : ℤ) (by positivity)

lemma posX : Pos (X : P) := by
  intro i
  simp [coeff_X]
  split <;> omega

lemma posAdd {p q : P} (hp : Pos p) (hq : Pos q) : Pos (p + q) := by
  intro i
  simpa using add_nonneg (hp i) (hq i)

lemma posMul {p q : P} (hp : Pos p) (hq : Pos q) : Pos (p * q) := by
  intro i
  rw [coeff_mul]
  exact Finset.sum_nonneg fun j _ => mul_nonneg (hp j.1) (hq j.2)

lemma posPow {p : P} (hp : Pos p) (k : ℕ) : Pos (p^k) := by
  induction k with
  | zero => simpa using posN 1
  | succ k ih => simpa [pow_succ] using posMul ih hp

lemma posComp {p q : P} (hp : Pos p) (hq : Pos q) : Pos (p.comp q) := by
  intro i
  conv_rhs => rw [p.as_sum_support_C_mul_X_pow]
  simp only [sum_comp, mul_comp, C_comp, pow_comp, X_comp, finsetSum_coeff]
  exact Finset.sum_nonneg fun k _ => posMul (posC _ (hp k)) (posPow hq k) i

lemma signPow (a : ℕ) : (-1 : ℤ)^a = 1 ∨ (-1 : ℤ)^a = -1 := by
  induction a with
  | zero => simp
  | succ a ih => rcases ih with h | h <;> simp [pow_succ, h]

lemma negCoeff (p : P) (i : ℕ) : (p.comp (-X)).coeff i = p.coeff i * (-1)^i := by
  simpa using (comp_C_mul_X_coeff (p := p) (r := (-1 : ℤ)) (n := i))

noncomputable def project (v : ℤ) (p : P) : P := p + C v * p.comp (-X)

lemma posProject {v : ℤ} (hv : v = 1 ∨ v = -1) {p : P} (hp : Pos p) :
    Pos (project v p) := by
  intro i
  have hi := hp i
  simp only [project, coeff_add, coeff_C_mul, negCoeff]
  rcases hv with h | h <;> rcases signPow i with hi' | hi' <;> rw [h, hi'] <;> linarith

lemma projectParity {v : ℤ} (hv : v = 1 ∨ v = -1) (p : P) :
    (project v p).comp (-X) = C v * project v p := by
  rcases hv with rfl | rfl
  · simp [project, add_comp, comp_neg_X_comp_neg_X, add_comm]
  · simp [project, add_comp, comp_neg_X_comp_neg_X, add_comm]

noncomputable def edge (h : ℕ) : ℕ → P
  | 0 => 1
  | a+1 => edge h a * (X + (h : P) + 2 * ((a+1 : ℕ) : P))

lemma posEdge (h a : ℕ) : Pos (edge h a) := by
  induction a with
  | zero => simpa [edge] using posN 1
  | succ a ih =>
    exact posMul ih (posAdd (posAdd posX (posN h)) (posMul (posN 2) (posN (a+1))))

lemma fallUp (n : ℕ) (z : P) : falling (n+1) (z+1) = (z+1)*falling n z := by
  induction n with
  | zero => simp [falling]
  | succ n ih =>
    rw [falling, ih, falling]
    push_cast
    ring

lemma upper (h a : ℕ) (z : P) :
    2^a * falling (h+a+1) (z+a) =
    falling (h+1) z * (edge h a).comp (2*z-h) := by
  induction a with
  | zero => simp [edge]
  | succ a ih =>
    rw [show h+(a+1)+1 = (h+a+1)+1 by omega, Nat.cast_succ, ← add_assoc z, fallUp,
      edge, mul_comp, add_comp, add_comp, X_comp, pow_succ]
    simp only [natCast_comp, mul_comp, ofNat_comp, Nat.cast_succ, add_comp, one_comp]
    linear_combination (2 * (z + a + 1)) * ih

lemma lower (h a : ℕ) (z : P) :
    2^a * falling (h+a+1) z =
    falling (h+1) z * C ((-1 : ℤ)^a) * (edge h a).comp (-(2*z-h)) := by
  induction a with
  | zero => simp [edge]
  | succ a ih =>
    rw [show h+(a+1)+1 = (h+a+1)+1 by omega, falling, edge,
      mul_comp, add_comp, add_comp, X_comp, pow_succ, pow_succ (-1 : ℤ)]
    simp only [Nat.cast_add, Nat.cast_one, mul_comp, natCast_comp, ofNat_comp, add_comp,
      one_comp, map_mul, map_neg, map_one]
    linear_combination (2 * (z - (h+a+1))) * ih

lemma substParity (p : P) (e : ℤ) (he : p.comp (-X) = C e * p) (z : P) :
    p.comp (-z) = C e * p.comp z := by
  have h := congrArg (fun q : P => q.comp z) he
  simpa only [comp_assoc, neg_comp, X_comp, mul_comp, C_comp] using h

lemma invariant (l : List ℕ) (h : ℕ) :
    ∃ (p : P) (e : ℤ), (e = 1 ∨ e = -1) ∧ Pos p ∧ p.comp (-X) = C e * p ∧
      ∀ z : P, 2^l.sum * differences l (falling (h+l.sum+1)) z =
        falling (h+1) z * p.comp (2*z-h) := by
  induction l generalizing h with
  | nil => exact ⟨1, 1, Or.inl rfl, by simpa using posN 1, by simp,
      fun z => by simp [differences]⟩
  | cons a l ih =>
    obtain ⟨p,e,he,hp,hpar,ih⟩ := ih (h+a)
    let H : P := edge h a * p.comp (X + (a : P))
    let v : ℤ := -((-1)^a * e)
    have hv : v = 1 ∨ v = -1 := by
      rcases he with h | h <;> rcases signPow a with g | g <;> simp [v,h,g]
    have hH : Pos H := posMul (posEdge h a) (posComp hp (posAdd posX (posN a)))
    refine ⟨project v H, v, hv, posProject hv hH, projectParity hv H, ?_⟩
    intro z
    let u : P := 2*z-h
    have hhi : 2*(z+a)-(↑(h+a) : P) = u+a := by dsimp [u]; push_cast; ring
    have hlo : 2*z-(↑(h+a) : P) = -(-u+a) := by dsimp [u]; push_cast; ring
    have hi := ih (z+a)
    have lo := ih z
    rw [hhi] at hi
    rw [hlo, substParity p e hpar] at lo
    simp only [List.sum_cons, differences, ← Nat.add_assoc, pow_add]
    change (2^a * 2^l.sum) * (_ - _) = falling (h+1) z * (project v H).comp u
    have distribute : ∀ x y : P, (2^a * 2^l.sum)*(x-y) =
      2^a*(2^l.sum*x) - 2^a*(2^l.sum*y) := by intros; ring
    rw [distribute, hi, lo,
      ← mul_assoc, upper, ← mul_assoc, lower]
    simp only [project, H, v, add_comp, mul_comp, C_comp, comp_assoc, neg_comp, X_comp,
      natCast_comp, map_neg, map_mul]
    ring

lemma unitStep (l : List ℕ) (n : ℕ) (z : P) :
    differences l (falling (n+1)) (z+1) - differences l (falling (n+1)) z =
    (n+1 : P) * differences l (falling n) z := by
  induction l generalizing z with
  | nil =>
    simp only [differences]
    rw [fallUp, falling]
    ring
  | cons a l ih =>
    simp only [differences]
    rw [show z+1+(a : P)=z+a+1 by ring]
    linear_combination ih (z+a) - ih z

lemma telescope (l : List ℕ) (n a : ℕ) :
    differences (a::l) (falling (n+1)) X = (n+1 : P) * phi n a l := by
  unfold phi
  simp only [differences]
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Finset.sum_range_succ, Nat.cast_succ, ← add_assoc]
    linear_combination ih + unitStep l n (X+(a : P))

end DiscreteShift

open DiscreteShift

theorem OMA.solution : type_of% @OMA.S_mo_270442.main := by
  intro n a l hn _ _
  obtain ⟨p,e,he,hp,hpar,h⟩ := invariant (a::l) 0
  have hh := h X
  rw [hn] at hh
  simp only [Nat.zero_add, Nat.cast_zero, sub_zero] at hh
  rw [show falling (0+1) (X : P) = X by simp [falling]] at hh
  rw [telescope] at hh
  let k : ℤ := 2^n * (n+1)
  have hk : 0 < k := by dsimp [k]; positivity
  have ident : C k * phi n a l = X * p.comp (2*X) := by
    simpa [k, mul_assoc] using hh
  have hpos : Pos (X * p.comp (2*X)) := posMul posX (posComp hp (posMul (posN 2) posX))
  have hr : (X * p.comp (2*X)).comp (-X) = C (-e) * (X * p.comp (2*X)) := by
    simp only [mul_comp, X_comp, comp_assoc, ofNat_comp, mul_neg, substParity p e hpar,
      map_neg]
    ring
  have hl := congrArg (fun q : P => q.comp (-X)) ident
  change (C k * phi n a l).comp (-X) = _ at hl
  rw [mul_comp, C_comp, hr, ← ident, mul_left_comm] at hl
  have hphi := mul_left_cancel₀ (show C k ≠ 0 by simpa using hk.ne') hl
  constructor
  · rcases he with rfl | rfl
    · right; simpa using hphi
    · left; simpa using hphi
  · intro i
    have hi := hpos i
    rw [← ident, coeff_C_mul] at hi
    exact nonneg_of_mul_nonneg_right hi hk

