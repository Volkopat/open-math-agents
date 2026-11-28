import OMAStatements.S_mse_3925067
import Mathlib

/- A group G with Aut(G) isomorphic to (R,+) must be non-abelian and nilpotent of
class two (commutators are central), and its central quotient G/Z(G) is torsion-free.
Reason: R is torsion-free, so every automorphism of finite order is trivial. If G were
abelian, inversion would be trivial, so G would be an elementary abelian 2-group; it then
has a nontrivial involutive transvection (or only trivial automorphisms when it has at
most two elements). Inner automorphisms commute in the abelian group Aut(G), which makes
commutators central, and conj(g)^n = conj(g^n) = 1 forces conj(g) = 1.
H1 and H2 split the remaining class-two case by whether G itself is torsion-free. -/
namespace OMA.R_mse_3925067_R1

def H1 : Prop :=
  ∀ (G : Type) [Group G], ¬ (∀ a b : G, a * b = b * a) →
    (∀ a b c : G, a * b * a⁻¹ * b⁻¹ * c = c * (a * b * a⁻¹ * b⁻¹)) →
    (∀ g : G, ∀ n : ℕ, 0 < n → (∀ c : G, g ^ n * c = c * g ^ n) → ∀ c : G, g * c = c * g) →
    (∀ g : G, ∀ n : ℕ, 0 < n → g ^ n = 1 → g = 1) →
    ¬ OMA.S_mse_3925067.AutIsReal G

def H2 : Prop :=
  ∀ (G : Type) [Group G], ¬ (∀ a b : G, a * b = b * a) →
    (∀ a b c : G, a * b * a⁻¹ * b⁻¹ * c = c * (a * b * a⁻¹ * b⁻¹)) →
    (∀ g : G, ∀ n : ℕ, 0 < n → (∀ c : G, g ^ n * c = c * g ^ n) → ∀ c : G, g * c = c * g) →
    (∃ g : G, g ≠ 1 ∧ ∃ n : ℕ, 0 < n ∧ g ^ n = 1) →
    ¬ OMA.S_mse_3925067.AutIsReal G

/-- Every automorphism of finite order is trivial. -/
theorem aut_torsionfree {G : Type} [Group G] (e : MulAut G ≃* Multiplicative ℝ)
    (φ : MulAut G) (n : ℕ) (hn : 0 < n) (h : φ ^ n = 1) : φ = 1 := by
  have h2 : (e φ) ^ n = 1 := by rw [← map_pow, h, map_one]
  have h3 : (n : ℝ) * Multiplicative.toAdd (e φ) = 0 := by
    have := congrArg Multiplicative.toAdd h2
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul] at this
    exact this
  have h4 : Multiplicative.toAdd (e φ) = 0 := by
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h (by positivity)
    · exact h
  apply e.injective
  rw [map_one]
  exact h4

/-- The automorphism group is abelian. -/
theorem aut_comm {G : Type} [Group G] (e : MulAut G ≃* Multiplicative ℝ)
    (φ ψ : MulAut G) : φ * ψ = ψ * φ := by
  apply e.injective
  rw [map_mul, map_mul, mul_comm]

/-- G is not abelian. -/
theorem not_abelian {G : Type} [Group G] (e : MulAut G ≃* Multiplicative ℝ) :
    ¬ (∀ a b : G, a * b = b * a) := by
  intro hab
  -- inversion is an automorphism, hence trivial
  let ι : MulAut G :=
    { toFun := fun x => x⁻¹
      invFun := fun x => x⁻¹
      left_inv := fun x => inv_inv x
      right_inv := fun x => inv_inv x
      map_mul' := fun x y => by
        simp only [mul_inv_rev]
        exact hab _ _ }
  have hι : ι ^ 2 = 1 := by
    ext x
    simp [pow_two, ι]
  have hinv : ∀ x : G, x⁻¹ = x := by
    intro x
    have := congrArg (fun f : MulAut G => f x) (aut_torsionfree e ι 2 (by norm_num) hι)
    simpa [ι] using this
  have hsq : ∀ x : G, x * x = 1 := by
    intro x
    calc x * x = x⁻¹ * x := by rw [hinv]
      _ = 1 := inv_mul_cancel x
  -- the automorphism group is nontrivial
  have hnt : e.symm (Multiplicative.ofAdd 1) ≠ 1 := by
    intro h
    have h2 : e (e.symm (Multiplicative.ofAdd 1)) = e 1 := by rw [h]
    rw [MulEquiv.apply_symm_apply, MulEquiv.map_one] at h2
    have h3 := congrArg Multiplicative.toAdd h2
    simp at h3
  by_cases hsmall : ∀ x y : G, x ≠ 1 → y ≠ 1 → x = y
  · apply hnt
    ext x
    by_cases hx : x = 1
    · subst hx
      simp
    · apply hsmall _ _ _ hx
      intro h1
      apply hx
      have := congrArg (e.symm (Multiplicative.ofAdd 1)).symm h1
      simpa using this
  push Not at hsmall
  obtain ⟨a, b, ha, hb, hne⟩ := hsmall
  let _ : CommGroup G := { (inferInstance : Group G) with mul_comm := hab }
  let _ : Module (ZMod 2) (Additive G) := AddCommGroup.zmodModule (n := 2) (fun x => by
    rw [two_nsmul]
    exact hsq (Additive.toMul x))
  have ha' : Additive.ofMul a ≠ 0 := ha
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) ha'
  let F : G → ZMod 2 := fun x => f (Additive.ofMul x)
  have hF : ∀ x y : G, F (x * y) = F x + F y := fun x y => map_add f (Additive.ofMul x) (Additive.ofMul y)
  have z2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have z11 : (1 : ZMod 2) + 1 = 0 := by decide
  have hFa : F a = 1 := (z2 _).resolve_left hf
  -- a nonidentity element c with F c = 0
  obtain ⟨c, hc1, hc⟩ : ∃ c : G, c ≠ 1 ∧ F c = 0 := by
    rcases z2 (F b) with h | h
    · exact ⟨b, hb, h⟩
    · refine ⟨a * b, ?_, ?_⟩
      · intro h1
        apply hne
        calc a = a * (a * b) := by rw [h1, mul_one]
          _ = b := by rw [← mul_assoc, hsq, one_mul]
      · rw [hF, hFa, h, z11]
  let T : G → G := fun x => if F x = 0 then x else x * c
  have hTT : ∀ x, T (T x) = x := by
    intro x
    by_cases hx : F x = 0
    · simp [T, hx]
    · have : F (x * c) ≠ 0 := by rw [hF, hc, add_zero]; exact hx
      simp only [T, hx, this, if_false]
      rw [mul_assoc, hsq, mul_one]
  have hfin : ∀ x y : G, x * y = x * c * (y * c) := by
    intro x y
    rw [hab y c, ← mul_assoc (x * c) c y, mul_assoc x c c, hsq, mul_one]
  let τ : MulAut G :=
    { toFun := T
      invFun := T
      left_inv := hTT
      right_inv := hTT
      map_mul' := fun x y => by
        simp only [T, hF]
        rcases z2 (F x) with hx | hx <;> rcases z2 (F y) with hy | hy <;>
          simp only [hx, hy, z11, add_zero, zero_add, if_true, if_false, one_ne_zero] <;>
          first
          | rfl
          | exact mul_assoc _ _ _
          | exact hfin x y
          | rw [mul_assoc, hab y c, ← mul_assoc] }
  have hτ : τ ^ 2 = 1 := by
    ext x
    simp only [pow_two, MulAut.mul_apply, MulAut.one_apply]
    exact hTT x
  have := congrArg (fun f : MulAut G => f a) (aut_torsionfree e τ 2 (by norm_num) hτ)
  simp only [MulAut.one_apply] at this
  change T a = a at this
  have hFa0 : ¬ F a = 0 := by rw [hFa]; exact one_ne_zero
  simp only [T, hFa0, if_false] at this
  apply hc1
  calc c = a⁻¹ * (a * c) := by group
    _ = 1 := by rw [this, inv_mul_cancel]

/-- Commutators are central. -/
theorem comm_central {G : Type} [Group G] (e : MulAut G ≃* Multiplicative ℝ) :
    ∀ a b c : G, a * b * a⁻¹ * b⁻¹ * c = c * (a * b * a⁻¹ * b⁻¹) := by
  intro a b c
  have h := congrArg (fun f : MulAut G => f (a⁻¹ * b⁻¹ * c * b * a))
    (aut_comm e (MulAut.conj b) (MulAut.conj a))
  simp only [MulAut.mul_apply, MulAut.conj_apply] at h
  have h' : c = a * b * a⁻¹ * b⁻¹ * c * (a * b * a⁻¹ * b⁻¹)⁻¹ := by
    calc c = b * (a * (a⁻¹ * b⁻¹ * c * b * a) * a⁻¹) * b⁻¹ := by group
      _ = a * (b * (a⁻¹ * b⁻¹ * c * b * a) * b⁻¹) * a⁻¹ := h
      _ = a * b * a⁻¹ * b⁻¹ * c * (a * b * a⁻¹ * b⁻¹)⁻¹ := by group
  calc a * b * a⁻¹ * b⁻¹ * c
      = a * b * a⁻¹ * b⁻¹ * c * (a * b * a⁻¹ * b⁻¹)⁻¹ * (a * b * a⁻¹ * b⁻¹) := by group
    _ = c * (a * b * a⁻¹ * b⁻¹) := by rw [← h']

/-- G/Z(G) is torsion-free. -/
theorem quot_torsionfree {G : Type} [Group G] (e : MulAut G ≃* Multiplicative ℝ) :
    ∀ g : G, ∀ n : ℕ, 0 < n → (∀ c : G, g ^ n * c = c * g ^ n) → ∀ c : G, g * c = c * g := by
  intro g n hn hz c
  have h1 : (MulAut.conj g) ^ n = 1 := by
    rw [← map_pow]
    ext x
    simp only [MulAut.conj_apply, MulAut.one_apply]
    rw [hz x, mul_assoc, mul_inv_cancel, mul_one]
  have h2 := congrArg (fun f : MulAut G => f c) (aut_torsionfree e _ n hn h1)
  simp only [MulAut.conj_apply, MulAut.one_apply] at h2
  calc g * c = g * c * g⁻¹ * g := by group
    _ = c * g := by rw [h2]

theorem main : H1 → H2 → type_of% @OMA.S_mse_3925067.main := by
  intro h1 h2
  rintro ⟨G, inst, ⟨e⟩⟩
  have hna := not_abelian e
  have hc := comm_central e
  have hq := quot_torsionfree e
  by_cases ht : ∀ g : G, ∀ n : ℕ, 0 < n → g ^ n = 1 → g = 1
  · exact h1 G hna hc hq ht ⟨e⟩
  · push Not at ht
    obtain ⟨g, n, hn, hg, hne⟩ := ht
    exact h2 G hna hc hq ⟨g, hne, n, hn, hg⟩ ⟨e⟩

end OMA.R_mse_3925067_R1
