import OMAStatements.S_oeis_a391613
import Mathlib

namespace OMA.R_oeis_a391613_R1


lemma square_lcm (a b : ℕ) : Nat.lcm (a^2) (b^2) = (Nat.lcm a b)^2 := by
  rcases eq_or_ne a 0 with rfl|ha
  · simp
  rcases eq_or_ne b 0 with rfl|hb
  · simp
  apply Nat.eq_of_factorization_eq (Nat.lcm_ne_zero (pow_ne_zero _ ha) (pow_ne_zero _ hb))
    (pow_ne_zero _ (Nat.lcm_ne_zero ha hb))
  intro p
  rw [Nat.factorization_lcm (pow_ne_zero _ ha) (pow_ne_zero _ hb)]
  simp only [Nat.factorization_pow,Nat.factorization_lcm ha hb,Finsupp.sup_apply,Finsupp.smul_apply,smul_eq_mul]
  change max _ _ = 2*max _ _
  omega

lemma arrange {n x y z : ℕ} (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (he : n=x^2+y+z) (hs : IsSquare (Nat.lcm (x^2) (Nat.lcm y z))) : (fun n : ℕ => ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ z ∧ z ≤ y ∧
    n=x^2+y+z ∧ IsSquare (Nat.lcm (x^2) (Nat.lcm y z))) n := by
  rcases le_total z y with h|h
  · exact ⟨x,y,z,hx,hz,h,he,hs⟩
  · exact ⟨x,z,y,hx,hy,h,by omega,by rwa [Nat.lcm_comm z y]⟩

lemma three {n a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : n=a^2+b^2+c^2) : (fun n : ℕ => ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ z ∧ z ≤ y ∧
    n=x^2+y+z ∧ IsSquare (Nat.lcm (x^2) (Nat.lcm y z))) n := by
  apply arrange ha (by positivity) (by positivity) he
  rw [square_lcm,square_lcm]
  exact ⟨_,pow_two _⟩

lemma mixed {n a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (ev : 2 ∣ a ∨ 2 ∣ b) (odd : Odd c) (he : n=a^2+b^2+2*c^2) : (fun n : ℕ => ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ z ∧ z ≤ y ∧
    n=x^2+y+z ∧ IsSquare (Nat.lcm (x^2) (Nat.lcm y z))) n := by
  apply arrange ha (by positivity) (by positivity) he
  let L := Nat.lcm (Nat.lcm a b) c
  have la : a ∣ L := (Nat.dvd_lcm_left a b).trans (Nat.dvd_lcm_left _ _)
  have lb : b ∣ L := (Nat.dvd_lcm_right a b).trans (Nat.dvd_lcm_left _ _)
  have lc : c ∣ L := Nat.dvd_lcm_right _ _
  have ld : 2 ∣ L := ev.elim (fun h => h.trans la) (fun h => h.trans lb)
  have le : 2*c^2 ∣ L^2 := ((Nat.coprime_two_left.mpr odd).pow_right 2).mul_dvd_of_dvd_of_dvd
    (ld.trans (dvd_pow_self _ (by decide : 2≠0))) (pow_dvd_pow_of_dvd lc 2)
  have eqn : Nat.lcm (a^2) (Nat.lcm (b^2) (2*c^2)) = L^2 := by
    apply Nat.dvd_antisymm (Nat.lcm_dvd (pow_dvd_pow_of_dvd la 2) (Nat.lcm_dvd (pow_dvd_pow_of_dvd lb 2) le))
    change (Nat.lcm (Nat.lcm a b) c)^2 ∣ _
    rw [←square_lcm,←square_lcm,Nat.lcm_assoc]
    apply Nat.lcm_dvd (Nat.dvd_lcm_left _ _)
    apply Nat.dvd_trans _ (Nat.dvd_lcm_right _ _)
    exact Nat.lcm_dvd (Nat.dvd_lcm_left _ _) ((dvd_mul_left _ _).trans (Nat.dvd_lcm_right _ _))
  rw [eqn]; exact ⟨_,pow_two _⟩

lemma scale {n : ℕ} (h : (fun n : ℕ => ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ z ∧ z ≤ y ∧
    n=x^2+y+z ∧ IsSquare (Nat.lcm (x^2) (Nat.lcm y z))) n) (k : ℕ) (hk : 0 < k) : (fun n : ℕ => ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ z ∧ z ≤ y ∧
    n=x^2+y+z ∧ IsSquare (Nat.lcm (x^2) (Nat.lcm y z))) (k^2*n) := by
  obtain ⟨x,y,z,hx,hz,hy,he,L,hl⟩ := h
  refine ⟨k*x,k^2*y,k^2*z,Nat.mul_pos hk hx,Nat.mul_pos (pow_pos hk _) hz,Nat.mul_le_mul_left _ hy,?_,?_⟩
  · rw [he]; ring
  · rw [mul_pow,Nat.lcm_mul_left,Nat.lcm_mul_left,hl]
    exact ⟨k*L,by ring⟩



lemma residues (a : ℕ) : (a^2%8=0 ∧ a%2=0) ∨ (a^2%8=1 ∧ a%2=1) ∨
    (a^2%8=4 ∧ a%4=2) := by
  rw [Nat.pow_mod]
  generalize he : a%8 = t
  have ht : t < 8 := he ▸ Nat.mod_lt _ (by decide)
  have hp : a%2 = t%2 := by omega
  have hq : a%4 = t%4 := by omega
  rw [hp,hq]
  interval_cases t <;> decide

lemma half_sorted {n a b c : ℕ} (hn : n%8=7) (h : 2*n=a^2+b^2+c^2)
    (ha : a%2=1) (hb : b%2=1) (hc : c%4=2) (le : b ≤ a) : (fun n : ℕ => ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ z ∧ z ≤ y ∧
    n=x^2+y+z ∧ IsSquare (Nat.lcm (x^2) (Nat.lcm y z))) n := by
  let u := (a+b)/2
  let v := (a-b)/2
  let w := c/2
  have eu : 2*u=a+b := by dsimp [u]; omega
  have ev : 2*v=a-b := by dsimp [v]; omega
  have sub : a-b+b=a := Nat.sub_add_cancel le
  have ew : 2*w=c := by dsimp [w]; omega
  have euv : 2*v+b=a := by omega
  have va : u+v=a := by omega
  have vb : u=v+b := by omega
  have en : n=u^2+v^2+2*w^2 := by
    rw [←va, ←ew] at h
    have sq : (v+b)^2 = u^2 := by rw [←vb]
    nlinarith [sq,congrArg (fun x : ℕ => x^2) vb,congrArg (fun x : ℕ => x*v) vb]
  have wo : w%2=1 := by omega
  have vpos : 0 < v := by
    by_contra! neg
    have zero : v=0 := by omega
    rw [zero] at en; simp at en
    rcases residues u with hu|hu|hu <;> rcases residues w with hw|hw|hw <;> omega
  apply mixed (a:=u) (b:=v) (c:=w) (by omega) vpos (by omega) (by omega) (by exact Nat.odd_iff.mpr wo) en

lemma half {n a b c : ℕ} (hn : n%8=7) (h : 2*n=a^2+b^2+c^2)
    (ha : a%2=1) (hb : b%2=1) (hc : c%4=2) : (fun n : ℕ => ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ z ∧ z ≤ y ∧
    n=x^2+y+z ∧ IsSquare (Nat.lcm (x^2) (Nat.lcm y z))) n := by
  rcases le_total b a with le|le
  · exact half_sorted hn h ha hb hc le
  · exact half_sorted hn (by simpa only [add_comm (a^2) (b^2)] using h) hb ha hc le

/-- A representation of 2n by three squares gives the required LCM witness for n≡7 mod 8. -/
lemma seven {n a b c : ℕ} (hn : n%8=7) (h : 2*n=a^2+b^2+c^2) : (fun n : ℕ => ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ z ∧ z ≤ y ∧
    n=x^2+y+z ∧ IsSquare (Nat.lcm (x^2) (Nat.lcm y z))) n := by
  have which : (a%2=1 ∧ b%2=1 ∧ c%4=2) ∨ (a%2=1 ∧ c%2=1 ∧ b%4=2) ∨
      (b%2=1 ∧ c%2=1 ∧ a%4=2) := by
    rcases residues a with h₁|h₁|h₁ <;> rcases residues b with h₂|h₂|h₂ <;>
      rcases residues c with h₃|h₃|h₃ <;> omega
  rcases which with ⟨a₁,b₁,c₂⟩|⟨a₁,c₁,b₂⟩|⟨b₁,c₁,a₂⟩
  · exact half hn h a₁ b₁ c₂
  · exact half hn (a:=a) (b:=c) (c:=b) (by omega) a₁ c₁ b₂
  · exact half hn (a:=b) (b:=c) (c:=a) (by omega) b₁ c₁ a₂

lemma known {n : ℕ} (h : n ∈ ({8,10,12,13,16,20,25,37,58,85,130} : Finset ℕ)) : (fun n : ℕ => ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ z ∧ z ≤ y ∧
    n=x^2+y+z ∧ IsSquare (Nat.lcm (x^2) (Nat.lcm y z))) n := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at h
  rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨2,2,2,by decide,by decide,by decide,by decide,⟨2,by decide +kernel⟩⟩
  · exact ⟨2,4,2,by decide,by decide,by decide,by decide,⟨2,by decide +kernel⟩⟩
  · exact ⟨2,4,4,by decide,by decide,by decide,by decide,⟨2,by decide +kernel⟩⟩
  · exact ⟨1,9,3,by decide,by decide,by decide,by decide,⟨3,by decide +kernel⟩⟩
  · exact ⟨2,9,3,by decide,by decide,by decide,by decide,⟨6,by decide +kernel⟩⟩
  · exact ⟨4,2,2,by decide,by decide,by decide,by decide,⟨4,by decide +kernel⟩⟩
  · exact ⟨1,16,8,by decide,by decide,by decide,by decide,⟨4,by decide +kernel⟩⟩
  · exact ⟨3,25,3,by decide,by decide,by decide,by decide,⟨15,by decide +kernel⟩⟩
  · exact ⟨1,48,9,by decide,by decide,by decide,by decide,⟨12,by decide +kernel⟩⟩
  · exact ⟨1,81,3,by decide,by decide,by decide,by decide,⟨9,by decide +kernel⟩⟩
  · exact ⟨1,81,48,by decide,by decide,by decide,by decide,⟨36,by decide +kernel⟩⟩

def H1 : Prop := ∀ n : ℕ, n%8=7 → ∃ a b c : ℕ, 2*n=a^2+b^2+c^2

def H2 : Prop := ∀ n : ℕ, 5 < n → ¬4 ∣ n → n%8 ≠ 7 →
    n ∉ ({8,10,12,13,16,20,25,37,58,85,130} : Finset ℕ) →
    (¬∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ n=a^2+b^2+c^2) → (fun n : ℕ => ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ z ∧ z ≤ y ∧
    n=x^2+y+z ∧ IsSquare (Nat.lcm (x^2) (Nat.lcm y z))) n

lemma resolve (h₁ : H1) (h₂ : H2) (n : ℕ) (hn : 5 < n) : (fun n : ℕ => ∃ x y z : ℕ, 1 ≤ x ∧ 1 ≤ z ∧ z ≤ y ∧
    n=x^2+y+z ∧ IsSquare (Nat.lcm (x^2) (Nat.lcm y z))) n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases list : n ∈ ({8,10,12,13,16,20,25,37,58,85,130} : Finset ℕ)
    · exact known list
    by_cases d : 4 ∣ n
    · obtain ⟨k,rfl⟩ := d
      have hk : 5 < k := by
        by_contra! small
        simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at list
        omega
      have g := scale (ih k (by omega) hk) 2 (by decide)
      simpa using g
    by_cases mod : n%8=7
    · obtain ⟨a,b,c,eqn⟩ := h₁ n mod
      exact seven mod eqn
    by_cases sq : ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ n=a^2+b^2+c^2
    · obtain ⟨a,b,c,ha,hb,hc,eqn⟩ := sq
      exact three ha hb hc eqn
    · exact h₂ n hn d mod list sq

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a391613.main := resolve
end OMA.R_oeis_a391613_R1
