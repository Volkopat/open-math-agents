import OMAReductions.R_Catalan_pillais_conjecture_R1

/-!
Cancel the common divisor of the coefficients and handle comparable perfect powers by
divisibility. For unit coefficients, a common divisor d > 1 of the exponents gives a
gap between d-th powers: if U^d - V^d = c > 0, then U^d ≤ c². This leaves the
coprime-exponent unweighted case and the unequal, coprime-coefficient weighted case.
-/

namespace OMA.R_Catalan_pillais_conjecture_R1_H2_R1

def H1 : Prop := ∀ c : ℕ, 0 < c → ∃ B : ℕ, ∀ x y m n : ℕ,
  1 < x → 1 < y → 2 < m → 2 < n → (m.Prime ∨ m = 4) → (n.Prime ∨ n = 4) →
  m.Coprime n → ¬ x^n ∣ y^m → ¬ y^m ∣ x^n → x^n - y^m = c → x^n+y^m ≤ B

def H2 : Prop := ∀ a b c : ℕ, 0 < a → 0 < b → 0 < c → a.Coprime b → a ≠ b →
  ∃ B : ℕ, ∀ x y m n : ℕ, 1 < x → 1 < y → 2 < m → 2 < n →
  (m.Prime ∨ m = 4) → (n.Prime ∨ n = 4) → ¬ x^n ∣ y^m → ¬ y^m ∣ x^n →
  a*x^n-b*y^m = c → x^n+y^m ≤ B

theorem pillai_comparable_bound {a b c u v : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a*u - b*v = c) (comparable : u ∣ v ∨ v ∣ u) :
    u+v ≤ (a+b+1)*c := by
  have eq : a*u = b*v+c := by omega
  have lower : u ≤ a*u := Nat.le_mul_of_pos_left _ ha
  have lower' : v ≤ b*v := Nat.le_mul_of_pos_left _ hb
  rcases comparable with hu | hv
  · have dvd : u ∣ c := h ▸ Nat.dvd_sub (dvd_mul_left _ _) (hu.trans (dvd_mul_left _ _))
    have small := Nat.le_of_dvd hc dvd
    have large := Nat.mul_le_mul_left a small
    nlinarith only [eq,lower',small,large,Nat.zero_le (b*c)]
  · have dvd : v ∣ c := h ▸ Nat.dvd_sub (hv.trans (dvd_mul_left _ _)) (dvd_mul_left _ _)
    have small := Nat.le_of_dvd hc dvd
    have large := Nat.mul_le_mul_left b small
    have ca : c ≤ a*c := Nat.le_mul_of_pos_left _ ha
    nlinarith only [eq,lower,small,large,ca]

lemma power_gap {u v c d : ℕ} (hd : 2 ≤ d) (hc : 0 < c) (he : u^d-v^d=c) :
    u^d+v^d ≤ 2*c^2 := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hd
  have uv : v < u := by
    by_contra! hh
    have := Nat.pow_le_pow_left hh (2+t)
    omega
  have huv : 1 ≤ u := by omega
  have hmul := Nat.mul_le_mul (Nat.pow_le_pow_left uv.le (t+1)) (le_refl v)
  have hinc := Nat.mul_le_mul_left (u^(t+1)) (show v+1 ≤ u by omega)
  have hvpow : v^(2+t) = v^(t+1)*v := by rw [show 2+t=t+1+1 by omega,pow_succ]
  have hupow : u^(2+t) = u^(t+1)*u := by rw [show 2+t=t+1+1 by omega,pow_succ]
  have hbound : u^(t+1) ≤ c := by
    rw [hvpow,hupow] at he
    rw [Nat.mul_add] at hinc
    omega
  have hp : u^(2+t) ≤ (u^(t+1))^2 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right huv (by omega)
  have sq := Nat.pow_le_pow_left hbound 2
  have cmp := Nat.pow_le_pow_left uv.le (2+t)
  omega

lemma unweighted (h1 : H1) (c : ℕ) (hc : 0 < c) : ∃ B : ℕ,
    ∀ x y m n : ℕ, 1 < x → 1 < y → 2 < m → 2 < n →
    (m.Prime ∨ m=4) → (n.Prime ∨ n=4) → x^n-y^m=c → x^n+y^m≤B := by
  obtain ⟨B,hB⟩ := h1 c hc
  refine ⟨max B (max (3*c) (2*c^2)), ?_⟩
  intro x y m n hx hy hm hn hmp hnp he
  by_cases comp : x^n ∣ y^m ∨ y^m ∣ x^n
  · have e : 1*x^n-1*y^m=c := by simpa using he
    have hh := pillai_comparable_bound (a:=1) (b:=1) (by decide) (by decide) hc e comp
    omega
  by_cases co : m.Coprime n
  · exact (hB x y m n hx hy hm hn hmp hnp co
      (fun h => comp (.inl h)) (fun h => comp (.inr h)) he).trans (le_max_left ..)
  let d := m.gcd n
  have gd : 2 ≤ d := by
    have hd := Nat.gcd_pos_of_pos_left n (by omega : 0 < m)
    change m.gcd n ≠ 1 at co
    dsimp [d]; omega
  obtain ⟨r,hr⟩ := Nat.gcd_dvd_left m n
  obtain ⟨s,hs⟩ := Nat.gcd_dvd_right m n
  have em : y^m = (y^r)^d := by rw [← pow_mul]; congr 1; exact hr.trans (Nat.mul_comm ..)
  have en : x^n = (x^s)^d := by rw [← pow_mul]; congr 1; exact hs.trans (Nat.mul_comm ..)
  rw [em,en] at he ⊢
  exact (power_gap gd hc he).trans ((le_max_right ..).trans (le_max_right ..))

lemma primitive (h1 : H1) (h2 : H2) (a b c : ℕ) (ha : 0<a) (hb : 0<b)
    (hc : 0<c) (cop : a.Coprime b) : ∃ B : ℕ,
    ∀ x y m n : ℕ, 1 < x → 1 < y → 2 < m → 2 < n →
    (m.Prime ∨ m=4) → (n.Prime ∨ n=4) → a*x^n-b*y^m=c → x^n+y^m≤B := by
  by_cases eq : a=b
  · subst b
    have one : a=1 := by simpa using cop
    subst a
    simpa using unweighted h1 c hc
  obtain ⟨B,hB⟩ := h2 a b c ha hb hc cop eq
  refine ⟨max B ((a+b+1)*c), ?_⟩
  intro x y m n hx hy hm hn hmp hnp he
  by_cases comp : x^n ∣ y^m ∨ y^m ∣ x^n
  · exact (pillai_comparable_bound ha hb hc he comp).trans (le_max_right ..)
  exact (hB x y m n hx hy hm hn hmp hnp (fun h => comp (.inl h))
    (fun h => comp (.inr h)) he).trans (le_max_left ..)

theorem main : H1 → H2 → OMA.R_Catalan_pillais_conjecture_R1.H2 := by
  intro h1 h2 a b c ha hb hc
  let g := a.gcd b
  have gp : 0 < g := Nat.gcd_pos_of_pos_left b ha
  have ea : a / g * g = a := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have eb : b / g * g = b := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  have scale (u v : ℕ) : a*u-b*v = (a/g*u-b/g*v)*g := by
    rw [Nat.sub_mul,Nat.mul_right_comm (a/g),Nat.mul_right_comm (b/g),ea,eb]
  by_cases cd : g ∣ c
  · have ec := Nat.div_mul_cancel cd
    obtain ⟨B,hB⟩ := primitive h1 h2 (a/g) (b/g) (c/g) (Nat.div_pos (Nat.le_of_dvd ha (Nat.gcd_dvd_left ..)) gp)
      (Nat.div_pos (Nat.le_of_dvd hb (Nat.gcd_dvd_right ..)) gp)
      (Nat.div_pos (Nat.le_of_dvd hc cd) gp) (Nat.coprime_div_gcd_div_gcd gp)
    refine ⟨B,?_⟩
    intro x y m n hx hy hm hn hmp hnp he
    apply hB x y m n hx hy hm hn hmp hnp
    apply Nat.eq_of_mul_eq_mul_right gp
    rw [← scale,he,ec]
  · refine ⟨0,?_⟩
    intro x y m n _ _ _ _ _ _ he
    exact (cd ⟨a/g*x^n-b/g*y^m,he.symm.trans ((scale ..).trans (Nat.mul_comm ..))⟩).elim

end OMA.R_Catalan_pillais_conjecture_R1_H2_R1
