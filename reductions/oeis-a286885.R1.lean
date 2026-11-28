import OMAStatements.S_oeis_a286885
import Mathlib

/-! Prime targets 6n+1 are represented with z=0. A short vector in the
lattice of a square root of −3 gives the binary representation. -/
namespace OMA.R_oeis_a286885_R1

def H1 : Prop := ∀ p : ℕ, p.Prime → p % 3 = 1 → ∃ x y : ℕ, x^2+3*y^2=p

def H2 : Prop := ∀ n : ℕ, 0 < n → ¬ (6*n+1).Prime →
  ∃ x y z : ℕ, x^2+3*y^2+54*z^2=6*n+1

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a286885.main := by
  intro hp hc n
  rcases n with _ | n
  · exact ⟨1,0,0,by decide⟩
  by_cases h : (6*(n+1)+1).Prime
  · obtain ⟨x,y,hxy⟩ := hp _ h (by omega)
    exact ⟨x,y,0,by simpa using hxy⟩
  · exact hc _ (by omega) h

end OMA.R_oeis_a286885_R1
