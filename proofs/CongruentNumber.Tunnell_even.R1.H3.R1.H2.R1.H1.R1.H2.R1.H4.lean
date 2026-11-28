import OMAReductions.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1_H2_R1
import Mathlib
/-! The two signed ternary shell calibrations at 2 and 34. -/
namespace TunnellSmallPeriod
open Finset

def shell (n:ℕ) (r:ℤ) :=
  let b := Icc (-r) r
  (b ×ˢ (b ×ˢ b)).filter (fun v => v.1^2+v.2.1^2+v.2.2^2=(n:ℤ))

def period (s:Finset (ℤ×ℤ×ℤ)) :=
  ((s.filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%8=0)).card:ℤ)-
    (s.filter (fun v => v.1%4=v.2.1%4 ∧ v.2.2%4=0 ∧ (v.1+v.2.1+2*(v.2.2/4))%4=0)).card

lemma narrow (n:ℕ) (r:ℤ) (hr:0≤r) (h:(n:ℤ)<(r+1)^2) (hu:r≤(n:ℤ)+1) : shell n ((n:ℤ)+1)=shell n r := by
  ext ⟨x,y,z⟩
  simp only [shell,mem_filter,mem_product,mem_Icc]
  constructor
  · rintro ⟨_,he⟩
    have bd (a:ℤ) (ha:a^2≤n) : -r≤a ∧ a≤r := by
      constructor
      · by_contra! H
        have := mul_nonneg (show 0≤ -a-(r+1) by omega) (show 0≤ -a+(r+1) by omega)
        nlinarith
      · by_contra! H
        have := mul_nonneg (show 0≤a-(r+1) by omega) (show 0≤a+(r+1) by omega)
        nlinarith
    exact ⟨⟨bd x (by nlinarith [sq_nonneg y,sq_nonneg z]),bd y (by nlinarith [sq_nonneg x,sq_nonneg z]),bd z (by nlinarith [sq_nonneg x,sq_nonneg y])⟩,he⟩
  · rintro ⟨⟨⟨a,b⟩,⟨c,d⟩,e,f⟩,he⟩; exact ⟨⟨⟨by omega,by omega⟩,⟨by omega,by omega⟩,by omega,by omega⟩,he⟩

lemma one : period (shell 2 (((2:ℕ):ℤ)+1))=2 := by
  rw [narrow 2 1 (by norm_num) (by norm_num) (by norm_num)]
  decide

set_option maxRecDepth 14000 in
lemma seventeen : period (shell 34 (((34:ℕ):ℤ)+1))=0 := by
  rw [narrow 34 5 (by norm_num) (by norm_num) (by norm_num)]
  decide

end TunnellSmallPeriod

theorem OMA.solution : OMA.R_CongruentNumber_Tunnell_even_R1_H3_R1_H2_R1_H1_R1_H2_R1.H4 := by
  intro d hd
  have eq : (-(↑(2*d):ℤ)-1)= -((↑(2*d):ℤ)+1) := by ring
  dsimp only
  rw [eq]
  change (d=1 → TunnellSmallPeriod.period (TunnellSmallPeriod.shell (2*d) (((2*d:ℕ):ℤ)+1))=2) ∧
    (d=17 → TunnellSmallPeriod.period (TunnellSmallPeriod.shell (2*d) (((2*d:ℕ):ℤ)+1))=0)
  constructor
  · rintro rfl; exact TunnellSmallPeriod.one
  · rintro rfl; exact TunnellSmallPeriod.seventeen
