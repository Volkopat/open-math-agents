import FormalConjectures.Arxiv.«1601.03081».UniqueCrystalComponents

/-! A crystal decomposes into the cubic family, the parabolic family, or an
exponentially growing row past its first nontrivial member. The two dominant
families have no nontrivial intersection: this is an integral-point computation
on 2432.a1. The sparse families contain the remaining open cases.

Source of the underlying recurrence: Abrate, Barbero, Cerruti and Murru,
*The biharmonic mean*, arXiv:1601.03081, §3. The separation by growth, the
elliptic-curve identification, and this reduction are our argument. -/

namespace OMA.R_Arxiv_1601_03081_crystals_components_unique_R3
open Arxiv.«1601.03081»

private theorem cubic_strict : StrictMono (fun d : ℕ => (2*d+7)*(2*d^2+12*d+17)) := by
  apply strictMono_nat_of_lt_succ
  intro d
  nlinarith

private theorem para_strict : StrictMono (fun j : ℕ =>
    (2*j^2+4*j+1)*(2*j^2+8*j+7)) := by
  apply strictMono_nat_of_lt_succ
  intro j
  ring_nf
  omega

/-- Four types of sorted decompositions, from the crystal recurrence. -/
def H1 : Prop := ∀ n a b : ℕ, IsCrystalWithComponents n a b → a≤b →
    (a=5 ∧ b=7) ∨ (∃ d : ℕ, a=2*d+7 ∧ b=2*d^2+12*d+17) ∨
    (∃ j : ℕ, a=2*j^2+4*j+1 ∧ b=2*j^2+8*j+7) ∨
    ∃ q : ℕ, 5≤q ∧ 2*q<a ∧ (a+b)^2=q*((a+1)*(b+1))

/-- The exhaustive integral x-coordinate list for LMFDB curve 2432.a1
(Cremona 2432d1), using its minimal equation. Magma and SageMath independently
computed this data; the enumeration itself is an explicit formal hypothesis. -/
def H2 : Prop := ∀ X Y : ℤ, Y^2=X^3-X^2-9*X+25 →
    X ∈ ({-3,0,1,3,7,13,16,81,1197} : Finset ℤ)

/-- Uniqueness when one of the decompositions lies on a sparse row:
its quotient is at least five and it lies past the cubic member. -/
def H3 : Prop := ∀ n a b c e q : ℕ, IsCrystalWithComponents n a b → a≤b →
    IsCrystalWithComponents n c e → c≤e → 5≤q → 2*q<a →
    (a+b)^2=q*((a+1)*(b+1)) → a=c

/-- The cubic/parabolic intersection consists only of the identical pair (7,17). -/
theorem cross (list : H2) (d j : ℕ)
    (eq : (2*d+7)*(2*d^2+12*d+17)=(2*j^2+4*j+1)*(2*j^2+8*j+7)) :
    d=0 ∧ j=1 := by
  have eqZ : (2*(d:ℤ)+7)*(2*d^2+12*d+17)=
      (2*(j:ℤ)^2+4*j+1)*(2*j^2+8*j+7) := by exact_mod_cast eq
  have hit := list (4*(d:ℤ)+13) (4*(2*(j:ℤ)^2+6*j+3)) (by nlinarith only [eqZ])
  simp only [Finset.mem_insert,Finset.mem_singleton] at hit
  have choices : d=0 ∨ d=17 ∨ d=296 := by omega
  rcases choices with rfl|rfl|rfl
  · exact ⟨rfl,para_strict.injective (a₁:=j) (a₂:=1) (by simpa using eq.symm)⟩
  · by_cases h : j≤8
    · have b := para_strict.monotone h
      norm_num at eq b
      omega
    · have b := para_strict.monotone (show 9≤j by omega)
      norm_num at eq b
      omega
  · by_cases h : j≤70
    · have b := para_strict.monotone h
      norm_num at eq b
      omega
    · have b := para_strict.monotone (show 71≤j by omega)
      norm_num at eq b
      omega

private theorem thirtyfive {a b : ℕ} (h : IsCrystalWithComponents 35 a b) (ord : a≤b) : a=5 := by
  obtain ⟨_,ha,_,prod,_⟩ := h
  have sq : a*a≤35 := by rw [prod]; exact Nat.mul_le_mul_left _ ord
  have bound : a≤5 := by nlinarith
  interval_cases a <;> omega

private theorem ordered (cls : H1) (list : H2) (sp : H3) {n a b c e : ℕ}
    (hab : IsCrystalWithComponents n a b) (ab : a≤b)
    (hce : IsCrystalWithComponents n c e) (ce : c≤e) : a=c := by
  have prod : a*b=c*e := hab.2.2.2.1.symm.trans hce.2.2.2.1
  by_cases small : n=35
  · subst n
    exact (thirtyfive hab ab).trans (thirtyfive hce ce).symm
  have notSmall : ∀ u v, IsCrystalWithComponents n u v → ¬(u=5 ∧ v=7) := by
    rintro u v h ⟨rfl,rfl⟩
    exact small h.2.2.2.1
  rcases (cls n a b hab ab).resolve_left (notSmall a b hab) with
    ⟨d,ha,hb⟩ | ⟨j,ha,hb⟩ | ⟨q,hq,lo,eq⟩
  · rcases (cls n c e hce ce).resolve_left (notSmall c e hce) with
      ⟨D,hc,he⟩ | ⟨J,hc,he⟩ | ⟨q,hq,lo,eq⟩
    · rw [ha,hb,hc,he] at prod
      rw [ha,hc,cubic_strict.injective prod]
    · rw [ha,hb,hc,he] at prod
      obtain ⟨rfl,rfl⟩ := cross list d J prod
      omega
    · exact (sp n c e a b q hce ce hab ab hq lo eq).symm
  · rcases (cls n c e hce ce).resolve_left (notSmall c e hce) with
      ⟨D,hc,he⟩ | ⟨J,hc,he⟩ | ⟨q,hq,lo,eq⟩
    · rw [ha,hb,hc,he] at prod
      obtain ⟨rfl,rfl⟩ := cross list D j prod.symm
      omega
    · rw [ha,hb,hc,he] at prod
      rw [ha,hc,para_strict.injective prod]
    · exact (sp n c e a b q hce ce hab ab hq lo eq).symm
  · exact sp n a b c e q hab ab hce ce hq lo eq

private theorem sort_pair {n a b : ℕ} (h : IsCrystalWithComponents n a b) :
    ∃ u v, IsCrystalWithComponents n u v ∧ u≤v ∧ ({a,b}:Finset ℕ)={u,v} := by
  rcases le_total a b with ab|ba
  · exact ⟨a,b,h,ab,rfl⟩
  refine ⟨b,a,?_,ba,Finset.pair_comm ..⟩
  obtain ⟨hn,ha,hb,prod,dvd⟩ := (isCrystalWithComponents_iff_sum_sq_dvd ..).mp h
  exact (isCrystalWithComponents_iff_sum_sq_dvd ..).mpr
    ⟨hn,hb,ha,by simpa only [Nat.mul_comm] using prod,by simpa only [Nat.add_comm,Nat.mul_comm] using dvd⟩

theorem main : H1 → H2 → H3 → type_of% @Arxiv.«1601.03081».crystals_components_unique := by
  intro cls list sp n a b c e hab hce
  obtain ⟨u,v,h,uv,pair⟩ := sort_pair hab
  obtain ⟨U,V,H,UV,PAIR⟩ := sort_pair hce
  have same := ordered cls list sp h uv H UV
  subst U
  have vv := Nat.eq_of_mul_eq_mul_left (show 0<u by have := h.2.1; omega)
    (h.2.2.2.1.symm.trans H.2.2.2.1)
  simp only [pair,PAIR,vv]

end OMA.R_Arxiv_1601_03081_crystals_components_unique_R3
