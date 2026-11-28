import FormalConjectures.GreensOpenProblems.«40»

-- Reduction Green40.green_40.f_eq_one_for_all.R1 of Ben Green's Open Problem 40 — f eq one for all
-- Credit: @rickmanelius
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-!
# Ben Green's Open Problem 40: is `f r = 1` for every radius `r`?

`f r` is the liminf over `n` of the least density `|V| |H(r)| / 2^n` of a linear code `V` in
`F_2^n` whose Hamming balls of radius `r` cover the space.

`main` proves:
* the sphere-covering bound `1 ≤ minDensity n r` for all `n` and `r` (the addition map
  `V × H(r) → F_2^n` is onto), hence `1 ≤ f r` for every `r`;
* `f 0 = 1` (the whole space, with `H(0) = {0}`);
* `f 1 = 1`, from the binary Hamming code of length `2^m - 1`. The kernel of the linear map
  whose columns are the nonzero vectors of `F_2^m` covers with radius one, and the addition map
  `V × H(1) → F_2^n` is injective (the code is perfect), so `minDensity (2^m - 1) 1 ≤ 1` for
  every `m`.

What remains:
* `H1`: `f 2 = 1`. This is now known (Kohlmeyer and Kruer, 2026). It is proved on main as
  `Green40.green_40.f_two_eq_one`.
* `H2`: `f r ≤ 1` for every `r ≥ 3`, that is, asymptotically perfect linear covering codes of
  every radius at least three. This is the open core.
-/

namespace OMA.R_Green40_green_40_f_eq_one_for_all_R1

open Green40 Filter
open scoped ENNReal Pointwise

/-- `f 2 = 1`: linear covering codes of radius two whose density tends to one along a
sequence of lengths. -/
def H1 : Prop := Green40.f 2 = 1

/-- `f r ≤ 1` for every radius `r ≥ 3`. -/
def H2 : Prop := ∀ r : ℕ, 3 ≤ r → Green40.f r ≤ 1

lemma card_space (n : ℕ) : Nat.card (𝔽₂ n) = 2 ^ n := by
  rw [Nat.card_eq_fintype_card]
  simp [ZMod.card]

/-- The sphere-covering bound: every covering subspace has density at least one. -/
lemma one_le_minDensity (n r : ℕ) : (1 : ℝ≥0∞) ≤ minDensity n r := by
  unfold minDensity
  refine le_iInf₂ fun V hV => ?_
  have hsurj : Function.Surjective
      (fun p : V × hammingBall n r => (p.1 : 𝔽₂ n) + (p.2 : 𝔽₂ n)) := by
    intro x
    have hx : x ∈ (V : Set (𝔽₂ n)) + hammingBall n r := by
      rw [hV]
      exact Set.mem_univ x
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), hab⟩
  have hle : 2 ^ n ≤ Nat.card V * Nat.card (hammingBall n r) := by
    rw [← card_space n, ← Nat.card_prod]
    exact Nat.card_le_card_of_surjective _ hsurj
  have h0 : (2 ^ n : ℝ≥0∞) ≠ 0 := by positivity
  have ht : (2 ^ n : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [ENNReal.le_div_iff_mul_le (Or.inl h0) (Or.inl ht), one_mul]
  exact_mod_cast hle

lemma one_le_f (r : ℕ) : (1 : ℝ≥0∞) ≤ f r := by
  unfold f
  exact Filter.le_liminf_of_le (by isBoundedDefault)
    (Eventually.of_forall fun n => one_le_minDensity n r)

/-- A covering subspace whose ball translates are pairwise disjoint has density at most one. -/
lemma minDensity_le_one {n r : ℕ} (V : Submodule (ZMod 2) (𝔽₂ n))
    (hV : IsCoveringSubspace n r V)
    (hinj : ∀ v ∈ V, ∀ v' ∈ V, ∀ b ∈ hammingBall n r, ∀ b' ∈ hammingBall n r,
      v + b = v' + b' → v = v' ∧ b = b') :
    minDensity n r ≤ 1 := by
  unfold minDensity
  refine le_trans (iInf₂_le V hV) ?_
  have hi : Function.Injective
      (fun p : V × hammingBall n r => (p.1 : 𝔽₂ n) + (p.2 : 𝔽₂ n)) := by
    rintro ⟨⟨v, hv⟩, ⟨b, hb⟩⟩ ⟨⟨v', hv'⟩, ⟨b', hb'⟩⟩ h
    obtain ⟨h1, h2⟩ := hinj v hv v' hv' b hb b' hb' h
    subst h1
    subst h2
    rfl
  have hle : Nat.card V * Nat.card (hammingBall n r) ≤ 2 ^ n := by
    rw [← card_space n, ← Nat.card_prod]
    exact Nat.card_le_card_of_injective _ hi
  have h0 : (2 ^ n : ℝ≥0∞) ≠ 0 := by positivity
  have ht : (2 ^ n : ℝ≥0∞) ≠ ⊤ := ENNReal.pow_ne_top ENNReal.ofNat_ne_top
  rw [ENNReal.div_le_iff h0 ht, one_mul]
  exact_mod_cast hle

/-- Radius zero: the whole space is the only covering subspace, with density one. -/
lemma minDensity_zero_le (n : ℕ) : minDensity n 0 ≤ 1 := by
  apply minDensity_le_one ⊤
  · refine Set.eq_univ_of_forall fun x => ?_
    exact Set.mem_add.mpr ⟨x, by simp, 0, by simp [hammingBall], add_zero x⟩
  · intro v _ v' _ b hb b' hb' h
    have hb0 : b = 0 := hammingNorm_eq_zero.mp (Nat.le_zero.mp hb)
    have hb0' : b' = 0 := hammingNorm_eq_zero.mp (Nat.le_zero.mp hb')
    subst hb0
    subst hb0'
    simpa using h

lemma f_zero : f 0 = 1 := by
  refine le_antisymm ?_ (one_le_f 0)
  unfold f
  apply Filter.liminf_le_of_frequently_le'
  exact Filter.frequently_atTop.mpr fun N => ⟨N, le_rfl, minDensity_zero_le N⟩

/-- In `ZMod 2` a nonzero element is `1`. -/
lemma zmod2_eq_one (c : ZMod 2) (hc : c ≠ 0) : c = 1 := by
  revert c
  decide

/-- A vector of Hamming weight at most one is `0` or a unit vector. -/
lemma weight_le_one {n : ℕ} (x : 𝔽₂ n) (hx : hammingNorm x ≤ 1) :
    x = 0 ∨ ∃ i, x = Pi.single i 1 := by
  by_cases h0 : x = 0
  · exact Or.inl h0
  · right
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      exact h0 (funext fun j => by_contra fun hj => h ⟨j, hj⟩)
    refine ⟨i, funext fun j => ?_⟩
    by_cases hj : j = i
    · subst hj
      rw [Pi.single_eq_same]
      exact zmod2_eq_one _ hi
    · rw [Pi.single_apply, if_neg hj]
      by_contra hxj
      unfold hammingNorm at hx
      exact hj (Finset.card_le_one.mp hx j (by simp [hxj]) i (by simp [hi]))

lemma hammingNorm_single_le {n : ℕ} (i : Fin n) : hammingNorm (Pi.single i 1 : 𝔽₂ n) ≤ 1 := by
  unfold hammingNorm
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  have ha' : a = i := by
    by_contra h
    exact ha (by rw [Pi.single_apply, if_neg h])
  have hb' : b = i := by
    by_contra h
    exact hb (by rw [Pi.single_apply, if_neg h])
  rw [ha', hb']

/-- There are `2^m - 1` nonzero vectors in `F_2^m`. -/
lemma card_nonzero (m : ℕ) : Fintype.card {v : Fin m → ZMod 2 // v ≠ 0} = 2 ^ m - 1 := by
  rw [Fintype.card_subtype_compl]
  simp [ZMod.card]

section Hamming

/- `e` lists the nonzero vectors of `F_2^m`. The Hamming code of length `2^m - 1` is the kernel
of the parity-check map `Fintype.linearCombination (ZMod 2) (fun j => (e.symm j).1)`, whose
column at `j` is the `j`-th nonzero vector. -/
variable {m : ℕ} (e : {v : Fin m → ZMod 2 // v ≠ 0} ≃ Fin (2 ^ m - 1))

lemma syn_single (i : Fin (2 ^ m - 1)) :
    Fintype.linearCombination (ZMod 2) (fun j => (e.symm j).1) (Pi.single i 1) =
      (e.symm i).1 := by
  rw [Fintype.linearCombination_apply_single, one_smul]

/-- The Hamming code covers with radius one: a nonzero syndrome is a column, so one flipped
coordinate reaches the code. -/
lemma hamming_covers : IsCoveringSubspace (2 ^ m - 1) 1
    (LinearMap.ker (Fintype.linearCombination (ZMod 2) (fun j => (e.symm j).1))) := by
  refine Set.eq_univ_of_forall fun y => ?_
  by_cases hy : Fintype.linearCombination (ZMod 2) (fun j => (e.symm j).1) y = 0
  · exact Set.mem_add.mpr ⟨y, hy, 0, by simp [hammingBall], add_zero y⟩
  · let s : {v : Fin m → ZMod 2 // v ≠ 0} :=
      ⟨Fintype.linearCombination (ZMod 2) (fun j => (e.symm j).1) y, hy⟩
    refine Set.mem_add.mpr ⟨y - Pi.single (e s) 1, ?_, Pi.single (e s) 1,
      hammingNorm_single_le _, sub_add_cancel _ _⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, syn_single, Equiv.symm_apply_apply, sub_self]

/-- The Hamming code is perfect: a codeword plus a vector of weight at most one determines both,
because distinct columns are distinct and nonzero. -/
lemma hamming_inj :
    ∀ v ∈ LinearMap.ker (Fintype.linearCombination (ZMod 2) (fun j => (e.symm j).1)),
    ∀ v' ∈ LinearMap.ker (Fintype.linearCombination (ZMod 2) (fun j => (e.symm j).1)),
    ∀ b ∈ hammingBall (2 ^ m - 1) 1, ∀ b' ∈ hammingBall (2 ^ m - 1) 1,
      v + b = v' + b' → v = v' ∧ b = b' := by
  intro v hv v' hv' b hb b' hb' h
  rw [LinearMap.mem_ker] at hv hv'
  have hs : Fintype.linearCombination (ZMod 2) (fun j => (e.symm j).1) b =
      Fintype.linearCombination (ZMod 2) (fun j => (e.symm j).1) b' := by
    have h2 := congrArg (Fintype.linearCombination (ZMod 2) (fun j => (e.symm j).1)) h
    rwa [map_add, map_add, hv, hv', zero_add, zero_add] at h2
  have hbb : b = b' := by
    rcases weight_le_one b hb with rfl | ⟨i, rfl⟩ <;>
      rcases weight_le_one b' hb' with rfl | ⟨j, rfl⟩
    · rfl
    · exfalso
      rw [map_zero, syn_single] at hs
      exact (e.symm j).2 hs.symm
    · exfalso
      rw [map_zero, syn_single] at hs
      exact (e.symm i).2 hs
    · rw [syn_single, syn_single] at hs
      rw [e.symm.injective (Subtype.ext hs)]
  refine ⟨?_, hbb⟩
  subst hbb
  exact add_right_cancel h

end Hamming

/-- Length `2^m - 1`, radius one: the Hamming code has density one. -/
lemma minDensity_hamming_le (m : ℕ) : minDensity (2 ^ m - 1) 1 ≤ 1 :=
  minDensity_le_one _ (hamming_covers (Fintype.equivFinOfCardEq (card_nonzero m)))
    (hamming_inj (Fintype.equivFinOfCardEq (card_nonzero m)))

lemma f_one : f 1 = 1 := by
  refine le_antisymm ?_ (one_le_f 1)
  unfold f
  apply Filter.liminf_le_of_frequently_le'
  refine Filter.frequently_atTop.mpr fun N => ⟨2 ^ (N + 1) - 1, ?_, minDensity_hamming_le (N + 1)⟩
  have h1 : N < 2 ^ N := Nat.lt_two_pow_self
  have h2 : 2 ^ (N + 1) = 2 * 2 ^ N := by ring
  omega

theorem main : H1 → H2 → type_of% @Green40.green_40.f_eq_one_for_all := by
  intro h1 h2 r
  match r with
  | 0 => exact f_zero
  | 1 => exact f_one
  | 2 => exact h1
  | r + 3 => exact le_antisymm (h2 (r + 3) (by omega)) (one_le_f (r + 3))

end OMA.R_Green40_green_40_f_eq_one_for_all_R1
