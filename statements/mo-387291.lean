import Mathlib

/-!
# A sphere isometry fixing independent unit vectors

Source: Taras Banakh, https://mathoverflow.net/questions/387291 (CC BY-SA).
Credit: @my-other-github-account
-/
namespace OMA.S_mo_387291

theorem main :
    ∀ (n : ℕ) (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X]
    [CompleteSpace X] [StrictConvexSpace ℝ X] [FiniteDimensional ℝ X]
    (_hdim : Module.finrank ℝ X = n)
    (e : Fin n → {x : X // ‖x‖ = 1}) (he : LinearIndependent ℝ (fun i => (e i : X)))
    (f : {x : X // ‖x‖ = 1} → {x : X // ‖x‖ = 1}) (hf : Isometry f)
    (_hfix : ∀ i, f (e i) = e i), f = id := by
  sorry

end OMA.S_mo_387291
