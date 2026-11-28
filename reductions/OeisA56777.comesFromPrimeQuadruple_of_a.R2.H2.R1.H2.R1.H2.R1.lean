import OMAReductions.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1

/-!
# Split the large-prime single-root obstruction by the repeated prime modulo five

A positive quadratic upper approximation to the doubled cubic puts the repeated
prime above the positive discriminant threshold. The modulo-three condition
excludes offsets four and ten. In the two-modulo-five branch the cubic excludes
offset six, while primality excludes offset eight.
-/

namespace OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1_H2_R1

private theorem discriminant_pos (p q x : ℤ) (hq : 0 ≤ q) (hgap : q+4 ≤ x)
    (hxp : x < p) (hroot : ((fun p q x : ℤ => 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)) p q x)=0) : 2*p*q+q^2 < p^2 := by
  let G := -(2*p+q)*x^2+2*p*(p+q)*x-2*p^2*q
  let E := p^2*(x-q-1)+(p+1)*(q+1)*(x-1)-2*x^2+2
  have hp : 0 < p := by omega
  have hx : 0 < x := by omega
  have hF : ((fun p q x : ℤ => 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)) p q x) = p^2*G-x*E-24 := by dsimp [G,E]; ring
  have hE : 0 < E := by
    have h₁ := mul_nonneg (sq_nonneg p) (show 0 ≤ x-q-4 by omega)
    have h₂ := mul_nonneg (show 0 ≤ p-x by omega) (show 0 ≤ p+x by omega)
    have h₃ : 0 ≤ (p+1)*(q+1)*(x-1) := by
      have : 0 ≤ x-1 := by omega
      positivity
    dsimp [E]
    nlinarith only [h₁,h₂,h₃,sq_nonneg p]
  have hg : 0 < G := by
    have : 0 < p^2*G := by nlinarith only [hF,hroot,mul_pos hx hE]
    exact pos_of_mul_pos_right this (sq_nonneg p)
  have hsq : (2*p+q)*G=p^2*(p^2-2*p*q-q^2)-((2*p+q)*x-p*(p+q))^2 := by
    dsimp [G]
    ring
  have hprod : 0 < p^2*(p^2-2*p*q-q^2) := by
    nlinarith only [hsq, sq_nonneg ((2*p+q)*x-p*(p+q)),
      mul_pos (show 0 < 2*p+q by omega) hg]
  have hdisc := pos_of_mul_pos_right hprod (sq_nonneg p)
  linarith

private theorem cast_F {n : ℕ} (p q x : ℕ) (h : ((fun p q x : ℤ => 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)) (p:ℤ) q x)=0) :
    ((fun p q x : ZMod n => 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)) (p:ZMod n) q x)=0 := by
  simpa using congrArg (fun t : ℤ => (t:ZMod n)) h

private theorem prime_mod3_ne_zero {x : ℕ} (hx : x.Prime) (hx3 : 3 < x) : x%3 ≠ 0 := by
  intro h
  have hd : 3 ∣ x := Nat.dvd_iff_mod_eq_zero.mpr h
  rcases (Nat.dvd_prime hx).mp hd with h|h <;> omega

private theorem gap_mod3 {p q x : ℕ} (hpq : p%3 ≠ q%3)
    (hp : p.Prime) (hq : q.Prime) (hx : x.Prime)
    (hp3 : 3 < p) (hq3 : 3 < q) (hx3 : 3 < x)
    (hroot : ((fun p q x : ℤ => 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)) (p:ℤ) q x)=0) : (x-q)%3 ≠ 1 ∨ x < q := by
  by_cases hxq : x < q
  · exact Or.inr hxq
  left
  intro h
  have hpn := prime_mod3_ne_zero hp hp3
  have hqn := prime_mod3_ne_zero hq hq3
  have hxn := prime_mod3_ne_zero hx hx3
  have hp2 : p%3=2 := by omega
  have hq1 : q%3=1 := by omega
  have hx2 : x%3=2 := by omega
  have h3 := cast_F (n:=3) p q x hroot
  have hp' : (p:ZMod 3)=2 := calc
    (p:ZMod 3) = (p%3:ℕ) := by simp
    _ = 2 := by rw [hp2]; rfl
  have hq' : (q:ZMod 3)=1 := calc
    (q:ZMod 3) = (q%3:ℕ) := by simp
    _ = 1 := by rw [hq1]; rfl
  have hx' : (x:ZMod 3)=2 := calc
    (x:ZMod 3) = (x%3:ℕ) := by simp
    _ = 2 := by rw [hx2]; rfl
  rw [hp',hq',hx'] at h3
  exact (by decide : ((fun p q x : ZMod 3 => 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)) (2:ZMod 3) 1 2) ≠ 0) h3

private theorem gap_ge_six {p q x : ℕ} (hpq : p%3 ≠ q%3)
    (hp : p.Prime) (hq : q.Prime) (hx : x.Prime)
    (hp3 : 3 < p) (hq3 : 3 < q) (hgap : q+4 ≤ x)
    (hroot : ((fun p q x : ℤ => 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)) (p:ℤ) q x)=0) : q+6 ≤ x := by
  have hx3 : 3 < x := by omega
  have hxodd := hx.eq_two_or_odd.resolve_left (by omega)
  have hqodd := hq.eq_two_or_odd.resolve_left (by omega)
  rcases gap_mod3 hpq hp hq hx hp3 hq3 hx3 hroot with h|h <;> omega

private theorem gap_ge_twelve_of_mod_five {p q x : ℕ} (hpq : p%3 ≠ q%3)
    (hp : p.Prime) (hq : q.Prime) (hx : x.Prime)
    (hp3 : 3 < p) (hq3 : 3 < q) (hgap : q+4 ≤ x)
    (hp5 : p%5=2) (hq5 : q%5=2)
    (hroot : ((fun p q x : ℤ => 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)) (p:ℤ) q x)=0) : q+12 ≤ x := by
  have hx3 : 3 < x := by omega
  have hxodd := hx.eq_two_or_odd.resolve_left (by omega)
  have hqodd := hq.eq_two_or_odd.resolve_left (by omega)
  have hgap6 := gap_ge_six hpq hp hq hx hp3 hq3 hgap hroot
  have h6 : x ≠ q+6 := by
    intro hx6
    have h5 := cast_F (n:=5) p q x hroot
    have hp' : (p:ZMod 5)=2 := calc
      (p:ZMod 5) = (p%5:ℕ) := by simp
      _ = 2 := by rw [hp5]; rfl
    have hq' : (q:ZMod 5)=2 := calc
      (q:ZMod 5) = (q%5:ℕ) := by simp
      _ = 2 := by rw [hq5]; rfl
    rw [hx6, Nat.cast_add, Nat.cast_ofNat, hp', hq'] at h5
    exact (by decide : ((fun p q x : ZMod 5 => 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)) (2:ZMod 5) 2 (2+6)) ≠ 0) h5
  have h8 : x ≠ q+8 := by
    intro h
    have hd : 5 ∣ x := Nat.dvd_iff_mod_eq_zero.mpr (by omega)
    rcases (Nat.dvd_prime hx).mp hd with hh|hh <;> omega
  rcases gap_mod3 hpq hp hq hx hp3 hq3 hx3 hroot with h|h <;> omega

set_option maxHeartbeats 1000000 in
private theorem mod_nine_table :
    ∀ P Q X : Fin 9, P.val%3 ≠ 0 → Q.val%3 ≠ 0 → X.val%3 ≠ 0 →
      P.val%3 ≠ Q.val%3 → ((fun p q x : ZMod 9 => 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)) (P.val:ZMod 9) Q.val X.val) = 0 →
      (Q.val%3=1 → Q.val=4 ∧ X.val%3=1) ∧
      (Q.val%3=2 → X.val%3=1 → P.val=7) := by
  decide

private theorem mod_nine_of_prime_root {p q x : ℕ} (hpq : p%3 ≠ q%3)
    (hp : p.Prime) (hq : q.Prime) (hx : x.Prime)
    (hp3 : 3 < p) (hq3 : 3 < q) (hx3 : 3 < x)
    (hroot : ((fun p q x : ℤ => 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)) (p:ℤ) q x)=0) :
    (q%3=1 → q%9=4 ∧ x%3=1) ∧ (q%3=2 → x%3=1 → p%9=7) := by
  let P : Fin 9 := ⟨p%9,Nat.mod_lt _ (by decide)⟩
  let Q : Fin 9 := ⟨q%9,Nat.mod_lt _ (by decide)⟩
  let X : Fin 9 := ⟨x%9,Nat.mod_lt _ (by decide)⟩
  have hP : P.val%3=p%3 := by dsimp [P]; omega
  have hQ : Q.val%3=q%3 := by dsimp [Q]; omega
  have hX : X.val%3=x%3 := by dsimp [X]; omega
  have hz := cast_F (n:=9) p q x hroot
  have h9 : ((fun p q x : ZMod 9 => 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)) (P.val:ZMod 9) Q.val X.val) = 0 := by simpa [P,Q,X] using hz
  have h := mod_nine_table P Q X (hP.trans_ne (prime_mod3_ne_zero hp hp3))
    (hQ.trans_ne (prime_mod3_ne_zero hq hq3)) (hX.trans_ne (prime_mod3_ne_zero hx hx3))
    (by simpa only [hP,hQ] using hpq) h9
  simpa only [hP,hQ,hX,P,Q] using h

set_option maxHeartbeats 1000000 in
private theorem mod_twenty_five_table :
    ∀ P Q X : Fin 5,
    (let p : ZMod 25 := 5*(P.val:ℕ)+2
     let q : ZMod 25 := 5*(Q.val:ℕ)+2
     let x : ZMod 25 := 5*(X.val:ℕ)+1
     2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
       (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)=0) →
       Q.val=2 := by
  decide

private theorem mod_twenty_five_of_prime_root {p q x : ℕ} (hp : p%5=2)
    (hq : q%5=2) (hx : x%5=1) (hroot : ((fun p q x : ℤ => 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)) (p:ℤ) q x)=0) : q%25=12 := by
  let P : Fin 5 := ⟨(p%25)/5, by omega⟩
  let Q : Fin 5 := ⟨(q%25)/5, by omega⟩
  let X : Fin 5 := ⟨(x%25)/5, by omega⟩
  have hP : p%25=5*P.val+2 := by dsimp [P]; omega
  have hQ : q%25=5*Q.val+2 := by dsimp [Q]; omega
  have hX : x%25=5*X.val+1 := by dsimp [X]; omega
  have hp' : (p:ZMod 25)=5*(P.val:ℕ)+2 := calc
    (p:ZMod 25) = (p%25:ℕ) := by simp
    _ = 5*(P.val:ℕ)+2 := by rw [hP]; push_cast; rfl
  have hq' : (q:ZMod 25)=5*(Q.val:ℕ)+2 := calc
    (q:ZMod 25) = (q%25:ℕ) := by simp
    _ = 5*(Q.val:ℕ)+2 := by rw [hQ]; push_cast; rfl
  have hx' : (x:ZMod 25)=5*(X.val:ℕ)+1 := calc
    (x:ZMod 25) = (x%25:ℕ) := by simp
    _ = 5*(X.val:ℕ)+1 := by rw [hX]; push_cast; rfl
  have hz := cast_F (n:=25) p q x hroot
  rw [hp',hq',hx'] at hz
  have h := mod_twenty_five_table P Q X hz
  omega

def H1 : Prop :=
  ∀ p q x : ℕ, p.Prime → q.Prime → x.Prime →
    p % 4 = 3 → q % 8 = 3 → 11 ≤ q → 2*q < p → p % 3 ≠ q % 3 →
    p^2 < q^3 → p % 5 = 2 → q % 5 = 2 →
    4000 ≤ q →
    7*p^2 < q^3 → (q % 3 = 2 → 11*p^2 < q^3) →
    2*p*q+q^2 < p^2 → q+12 ≤ x → x < p →
    (q%3=1 → q%9=4 ∧ x%3=1) → (q%3=2 → x%3=1 → p%9=7) →
    (x%5=1 → q%25=12) → x ∣ p^4*q+12 →
    let P : ℤ := p
    let X : ℤ := x
    let T := (P^2+P+1)*X^2-(2*P^3+P^2+P+1)*X+2*P^4
    0 < T →
    (q : ℤ)*T = 2*X^3-(P^2+P+1+2*P^3)*X^2+(2*P^4+P^2+P-1)*X-24 →
    T ∣ 2*(P^16+2*P^15-P^14-2*P^13+P^12-13*P^11-32*P^10-
      29*P^9+2*P^8+29*P^7+72*P^6+234*P^5+438*P^4+492*P^3+432*P^2+216*P+72) →
    False


def H2 : Prop :=
  ∀ p q x : ℕ, p.Prime → q.Prime → x.Prime →
    p % 4 = 3 → q % 8 = 3 → 11 ≤ q → 2*q < p → p % 3 ≠ q % 3 →
    p^2 < q^3 → p % 5 = 3 → q % 5 = 2 →
    4000 ≤ q →
    11*p^2 < q^3 →
    2*p*q+q^2 < p^2 → q+6 ≤ x → x < p →
    (q%3=1 → q%9=4 ∧ x%3=1) → (q%3=2 → x%3=1 → p%9=7) →
    x ∣ p^4*q+12 →
    let P : ℤ := p
    let X : ℤ := x
    let T := (P^2+P+1)*X^2-(2*P^3+P^2+P+1)*X+2*P^4
    0 < T →
    (q : ℤ)*T = 2*X^3-(P^2+P+1+2*P^3)*X^2+(2*P^4+P^2+P-1)*X-24 →
    T ∣ 2*(P^16+2*P^15-P^14-2*P^13+P^12-13*P^11-32*P^10-
      29*P^9+2*P^8+29*P^7+72*P^6+234*P^5+438*P^4+492*P^3+432*P^2+216*P+72) →
    False


theorem main : H1 → H2 → OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1.H2 := by
  intro branchTwo branchThree p q x hp hq hx hp4 hq8 hq11 hpq hpq3 hpqsize hp5 hq5
    hlarge h7 h11 hgap4 _ hxp hxdiv
  dsimp only
  intro hT hrec hres
  have hroot : ((fun p q x : ℤ => 2*x^3-((p^2+p+1)*(q+1)+2*p^3)*x^2+
    (2*p^3*(p+q-1)+(p^2+p+1)*(q+1)+2*p^3-2)*x-2*(p^4*q+12)) (p:ℤ) q x)=0 := by
    nlinarith only [hrec]
  have hdisc : 2*p*q+q^2 < p^2 := by
    exact_mod_cast discriminant_pos p q x (by positivity) (by exact_mod_cast hgap4)
      (by exact_mod_cast hxp) hroot
  obtain ⟨hmodQ,hmodP⟩ := mod_nine_of_prime_root hpq3 hp hq hx (by omega)
    (by omega) (by omega) hroot
  rcases hp5 with hp52 | hp53
  · have hgap12 := gap_ge_twelve_of_mod_five hpq3 hp hq hx (by omega) (by omega)
      hgap4 hp52 hq5 hroot
    exact branchTwo p q x hp hq hx hp4 hq8 hq11 hpq hpq3 hpqsize hp52 hq5 hlarge h7
      (fun hq32 => h11 (Or.inl hq32)) hdisc hgap12 hxp hmodQ hmodP (fun h => mod_twenty_five_of_prime_root hp52 hq5 h hroot) hxdiv hT hrec hres
  · have hgap6 := gap_ge_six hpq3 hp hq hx (by omega) (by omega) hgap4 hroot
    exact branchThree p q x hp hq hx hp4 hq8 hq11 hpq hpq3 hpqsize hp53 hq5 hlarge
      (h11 (Or.inr hp53)) hdisc hgap6 hxp hmodQ hmodP hxdiv hT hrec hres

end OMA.R_OeisA56777_comesFromPrimeQuadruple_of_a_R2_H2_R1_H2_R1_H2_R1
