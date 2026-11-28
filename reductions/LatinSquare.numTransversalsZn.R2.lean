import FormalConjectures.Paper.LatinSquare

-- Credit: @jacklarmer.
namespace OMA.R_LatinSquare_numTransversalsZn_R2

/-- An exponential lower bound for complete mappings with a prescribed value at zero. -/
def H1 : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∀ n : ℕ, 3 ≤ n → Odd n →
    a ^ n * (n-1).factorial ≤
      (Nat.card {σ : Equiv.Perm (ZMod n) //
        Function.Bijective (fun x ↦ x + σ x) ∧ σ 0 = 0} : ℝ)

/-- The finite upper bound obtained by pairing factors of the entropy product. -/
def H2 : Prop :=
  ∀ k : ℕ, 1 ≤ k → (LatinSquare.z (2*k+1) : ℝ) ≤
    (3/4 : ℝ)^k * (2*k+1).factorial

lemma cyclic_transversals_eq_complete_mappings (n : ℕ) (hn : 0 < n) :
    LatinSquare.z n = Nat.card {σ : Equiv.Perm (ZMod n) //
      Function.Bijective fun x ↦ x + σ x} := by
  classical
  cases n with
  | zero => omega
  | succ k =>
    let X := Fin (k + 1)
    let T := {f : X → X // Function.Injective f ∧ Function.Injective (fun x ↦ x + f x)}
    let C := {σ : Equiv.Perm X // Function.Bijective fun x ↦ x + σ x}
    have bij (f : X → X) (hf : Function.Injective f) : Function.Bijective f :=
      (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf, rfl⟩
    let e : T ≃ C :=
      { toFun := fun ⟨f, hf, hs⟩ ↦ ⟨Equiv.ofBijective f (bij f hf), bij _ hs⟩
        invFun := fun ⟨σ, hs⟩ ↦ ⟨σ, σ.injective, hs.injective⟩
        left_inv := fun ⟨_, _, _⟩ ↦ rfl
        right_inv := fun ⟨σ, _⟩ ↦ by
          apply Subtype.ext
          apply Equiv.ext
          intro x
          rfl }
    unfold LatinSquare.z numTransversals
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr e

lemma complete_mappings_factor (n : ℕ) (_hn : 0 < n) :
    Nat.card {σ : Equiv.Perm (ZMod n) // Function.Bijective fun x ↦ x + σ x} =
      n * Nat.card {σ : Equiv.Perm (ZMod n) //
        Function.Bijective (fun x ↦ x + σ x) ∧ σ 0 = 0} := by
  let G := ZMod n
  let C := {σ : Equiv.Perm G // Function.Bijective fun x ↦ x + σ x}
  let D := {σ : Equiv.Perm G // Function.Bijective (fun x ↦ x + σ x) ∧ σ 0 = 0}
  let t (a : G) : Equiv.Perm G :=
    { toFun := fun x ↦ x + a
      invFun := fun x ↦ x - a
      left_inv := fun x ↦ add_sub_cancel_right x a
      right_inv := fun x ↦ sub_add_cancel x a }
  let shift (p : C) (a : G) : C :=
    ⟨p.1.trans (t a), by
      have h := (t a).bijective.comp p.2
      simpa only [Function.comp_def, Equiv.trans_apply, t, Equiv.coe_fn_mk, add_assoc] using h⟩
  let e : C ≃ G × D :=
    { toFun := fun p ↦ (p.1 0, ⟨(shift p (-(p.1 0))).1,
        (shift p (-(p.1 0))).2, by simp [shift, t]⟩)
      invFun := fun q ↦ shift ⟨q.2.1, q.2.2.1⟩ q.1
      left_inv := by
        intro p
        apply Subtype.ext
        apply Equiv.ext
        intro x
        simp [shift, t]
      right_inv := by
        rintro ⟨a, σ, hs, hz⟩
        apply Prod.ext
        · simp [shift, t, hz]
        · apply Subtype.ext
          apply Equiv.ext
          intro x
          simp [shift, t, hz, add_assoc] }
  simpa only [Nat.card_prod, Nat.card_zmod, G, C, D] using Nat.card_congr e

theorem main : H1 → H2 → type_of% @LatinSquare.numTransversalsZn := by
  rintro ⟨a, ha, lower⟩ upper
  let b := min a (1/2 : ℝ)
  have hb : 0 < b := lt_min ha (by norm_num)
  refine ⟨b, hb, (99/100 : ℝ), by norm_num, lt_of_le_of_lt (min_le_right _ _) (by norm_num), ?_⟩
  intro n hn odd
  constructor
  · have pos : 0 < n := by omega
    have idcard := (cyclic_transversals_eq_complete_mappings n pos).trans
      (complete_mappings_factor n pos)
    have hfac : (n : ℝ) * (n-1).factorial = n.factorial := by
      exact_mod_cast Nat.mul_factorial_pred pos.ne'
    rw [idcard, Nat.cast_mul, ← hfac]
    calc
      b ^ n * ((n : ℝ) * (n-1).factorial) = (n : ℝ) * (b ^ n * (n-1).factorial) := by ring
      _ ≤ (n : ℝ) * (a ^ n * (n-1).factorial) := by
        gcongr
        exact min_le_left _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (lower n hn odd) (by positivity)
  · obtain ⟨k, rfl⟩ := odd
    have hk : 1 ≤ k := by omega
    refine (upper k hk).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    calc
      (3/4 : ℝ) ^ k ≤ ((99/100 : ℝ)^3) ^ k :=
        pow_le_pow_left₀ (by norm_num) (by norm_num) k
      _ = (99/100 : ℝ)^(3*k) := (pow_mul _ _ _).symm
      _ ≤ (99/100 : ℝ)^(2*k+1) := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

end OMA.R_LatinSquare_numTransversalsZn_R2
