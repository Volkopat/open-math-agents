import Mathlib.Combinatorics.Configuration

/-!
# Lines contained in a point set of a finite projective plane

The source asks for estimates of the maximum, especially when m grows as
q^a for fixed 1 < a < 2. The two finite bounds below give its sharp leading
term m/q. The uniform relative estimate expresses this without rounding
real powers: it applies whenever both m/q and q^2/m grow without bound.

Source: https://mathoverflow.net/questions/203533
Credit: @LDJAI
-/

namespace OMA.S_mo_203533

open Finset Configuration

noncomputable def contained (P L : Type*) [Fintype L] [Membership P L] (S : Finset P) :
    Finset L := by
  classical
  exact univ.filter (fun l => ∀ p : P, p ∈ l → p ∈ S)

theorem main : ∀ (P L : Type*) [Fintype P] [Fintype L] [Membership P L]
    [ProjectivePlane P L],
    let q := ProjectivePlane.order P L
    ∀ m : ℕ, 1 ≤ m → m ≤ q^2+q+1 →
      ∃ f : ℕ, IsGreatest {t : ℕ | ∃ S : Finset P, S.card=m ∧ (contained P L S).card=t} f ∧
        (m-1)/q ≤ f ∧ f*(q+1)^2 ≤ m*(q+f) ∧
        ∀ T : ℕ, 2 ≤ T → T*q ≤ m → T*m ≤ q^2 →
          (T-1)*m ≤ T*(q*f) ∧ (T-1)*(q*f) ≤ T*m := by
  sorry

end OMA.S_mo_203533
