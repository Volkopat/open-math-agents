import OMAStatements.S_oeis_a352259

/-!
Zhi-Wei Sun's cubic representation conjectures, https://oeis.org/A352259.

The classification at offsets zero and one implies all three coefficient-one
power cases. Each of its four excluded numbers has a checked repair at base two
for each exponent. The same cubic also has exact factorization criteria on
several small coordinate slices. For the other coefficients, only the indices
where bases zero through three fail remain in the power subgoals.
-/

namespace A352259Slices

/-- The slice `z=3` gives two factors with ratio between one and two. -/
lemma at_z_three (n : ℕ) :
    (∃ x y : ℕ, x^2 + 2*y^2 + 3*3^2 + x*y*3 = n) ↔
      ∃ a b : ℕ, a ≤ b ∧ b ≤ 2*a ∧ n = 27 + a*b := by
  constructor
  · rintro ⟨x,y,rfl⟩
    exact ⟨x+y,x+2*y,by omega,by omega,by ring⟩
  · rintro ⟨a,b,hab,hba,rfl⟩
    refine ⟨2*a-b,b-a,?_⟩
    have ha : (2*a-b)+(b-a) = a := by omega
    have hb : (2*a-b)+2*(b-a) = b := by omega
    calc _ = 27 + ((2*a-b)+(b-a))*((2*a-b)+2*(b-a)) := by ring
         _ = _ := by rw [ha,hb]

/-- The slice `x=5` gives two factors with ratio between two and three. -/
lemma at_x_five (n : ℕ) :
    (∃ y z : ℕ, 5^2 + 2*y^2 + 3*z^2 + 5*y*z = n) ↔
      ∃ a b : ℕ, 2*a ≤ b ∧ b ≤ 3*a ∧ n = 25 + a*b := by
  constructor
  · rintro ⟨y,z,rfl⟩
    exact ⟨y+z,2*y+3*z,by omega,by omega,by ring⟩
  · rintro ⟨a,b,hab,hba,rfl⟩
    refine ⟨3*a-b,b-2*a,?_⟩
    have ha : (3*a-b)+(b-2*a) = a := by omega
    have hb : 2*(3*a-b)+3*(b-2*a) = b := by omega
    calc _ = 25 + ((3*a-b)+(b-2*a))*(2*(3*a-b)+3*(b-2*a)) := by ring
         _ = _ := by rw [ha,hb]

/-- The two factors in the `y=4` slice have the same parity. -/
lemma at_y_four (n : ℕ) :
    (∃ x z : ℕ, x^2 + 2*4^2 + 3*z^2 + x*4*z = n) ↔
      ∃ a b : ℕ, a ≤ b ∧ b ≤ 3*a ∧ a % 2 = b % 2 ∧ n = 32 + a*b := by
  constructor
  · rintro ⟨x,z,rfl⟩
    exact ⟨x+z,x+3*z,by omega,by omega,by omega,by ring⟩
  · rintro ⟨a,b,hab,hba,hpar,rfl⟩
    let z := (b-a)/2
    have hz : 2*z+a = b := by dsimp [z]; omega
    have hzle : z ≤ a := by omega
    refine ⟨a-z,z,?_⟩
    have ha : a-z+z = a := by omega
    have hb : a-z+3*z = b := by omega
    calc _ = 32 + (a-z+z)*(a-z+3*z) := by ring
         _ = _ := by rw [ha,hb]

/-- Ordering the two squares gives nonnegative coordinates in the `z=2` slice. -/
lemma at_z_two (n : ℕ) :
    (∃ x y : ℕ, x^2 + 2*y^2 + 3*2^2 + x*y*2 = n) ↔
      ∃ a b : ℕ, n = 12 + a^2 + b^2 := by
  constructor
  · rintro ⟨x,y,rfl⟩
    exact ⟨x+y,y,by ring⟩
  · rintro ⟨a,b,rfl⟩
    rcases le_total a b with ha | hb
    · refine ⟨b-a,a,?_⟩
      calc _ = 12 + a^2 + ((b-a)+a)^2 := by ring
           _ = _ := by rw [Nat.sub_add_cancel ha]
    · refine ⟨a-b,b,?_⟩
      calc _ = 12 + ((a-b)+b)^2 + b^2 := by ring
           _ = _ := by rw [Nat.sub_add_cancel hb]

lemma at_z_two_prime_criterion (n : ℕ) :
    (∃ x y : ℕ, x^2 + 2*y^2 + 3*2^2 + x*y*2 = n) ↔
      12 ≤ n ∧ ∀ p ∈ (n-12).primeFactors, p % 4 = 3 → Even (padicValNat p (n-12)) := by
  rw [at_z_two, ← Nat.eq_sq_add_sq_iff]
  constructor
  · rintro ⟨a,b,rfl⟩
    exact ⟨by omega, a,b,by omega⟩
  · rintro ⟨hn,a,b,hab⟩
    exact ⟨a,b,by omega⟩

/-- The unimodular factorization on `z=3` represents all elements of every
commutative ring, by making the first factor one. -/
lemma signed_slice {R : Type*} [CommRing R] (n : R) :
    (29-n)^2 + 2*(n-28)^2 + 3*3^2 + (29-n)*(n-28)*3 = n := by ring

/-- Every residue modulo every positive modulus has a representation by the
original nonnegative polynomial even with `z=3` fixed. -/
lemma all_residues (m : ℕ) (hm : 0 < m) (n : ℕ) :
    ∃ x y : ℕ, x < m ∧ y < m ∧ x^2 + 2*y^2 + 3*3^2 + x*y*3 ≡ n [MOD m] := by
  have : NeZero m := ⟨hm.ne'⟩
  let u := 29-(n : ZMod m)
  let v := (n : ZMod m)-28
  refine ⟨u.val, v.val, u.val_lt, v.val_lt, (ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
  push_cast
  simp only [ZMod.natCast_zmod_val, u, v]
  ring

end A352259Slices

namespace A352259Repair

/-- The offset is unchanged by taking a positive power of zero or one. -/
theorem binary_pow (w k : ℕ) (hw : w ≤ 1) (hk : k ≠ 0) : w^k=w := by
  rcases (show w=0 ∨ w=1 by omega) with rfl | rfl
  · exact zero_pow hk
  · simp

/-- Power exponents 4, 5 and 6 all repair the four exceptional indices. -/
theorem repair (n k : ℕ) (bad : n ∈ ({106,744,5469,331269} : Finset ℕ))
    (hk : k=4 ∨ k=5 ∨ k=6) :
    ∃ w x y z : ℕ, w^k+x^2+2*y^2+3*z^2+x*y*z=n := by
  simp only [Finset.mem_insert,Finset.mem_singleton] at bad
  rcases bad with rfl | rfl | rfl | rfl <;> rcases hk with rfl | rfl | rfl
  · exact ⟨2,5,2,3,by decide⟩
  · exact ⟨2,7,2,1,by decide⟩
  · exact ⟨2,1,2,3,by decide⟩
  · exact ⟨2,4,10,8,by decide⟩
  · exact ⟨2,8,18,0,by decide⟩
  · exact ⟨2,4,14,4,by decide⟩
  · exact ⟨2,40,35,1,by decide⟩
  · exact ⟨2,73,0,6,by decide⟩
  · exact ⟨2,65,8,2,by decide⟩
  · exact ⟨2,69,371,2,by decide⟩
  · exact ⟨2,208,331,1,by decide⟩
  · exact ⟨2,575,1,1,by decide⟩

/-- Positive coverage with offsets zero and one implies all three coefficient-one
power statements, once the exceptional numerical cases are repaired. -/
theorem coefficient_one
    (cover : ∀ n : ℕ, n ∉ ({106,744,5469,331269} : Finset ℕ) →
      ∃ w x y z : ℕ, w≤1 ∧ w+x^2+2*y^2+3*z^2+x*y*z=n)
    (k : ℕ) (hk : k=4 ∨ k=5 ∨ k=6) (n : ℕ) :
    ∃ w x y z : ℕ, w^k+x^2+2*y^2+3*z^2+x*y*z=n := by
  by_cases hex : n ∈ ({106,744,5469,331269} : Finset ℕ)
  · exact repair n k hex hk
  · obtain ⟨w,x,y,z,hw,he⟩ := cover n hex
    have hk₀ : k≠0 := by rcases hk with rfl | rfl | rfl <;> decide
    exact ⟨w,x,y,z,by simpa only [binary_pow w k hw hk₀] using he⟩

end A352259Repair

namespace OMA.R_oeis_a352259_R1

/-- The four stated exclusions at offsets zero and one. -/
def H1 : Prop :=
  ∀ n : ℕ, n ∈ ({106,744,5469,331269} : Finset ℕ) →
    ¬ ∃ w x y z : ℕ, w≤1 ∧ w+x^2+2*y^2+3*z^2+x*y*z=n

/-- The positive coverage outside the four stated exclusions. -/
def H2 : Prop :=
  ∀ n : ℕ, n ∉ ({106,744,5469,331269} : Finset ℕ) →
    ∃ w x y z : ℕ, w≤1 ∧ w+x^2+2*y^2+3*z^2+x*y*z=n

/-- Find a larger offset for coefficient ten if the first four offsets all fail. -/
def H3 : Prop :=
  ∀ k : ℕ, 4≤k → k≤7 → ∀ n : ℕ,
    (¬ ∃ w x y z : ℕ, w≤3 ∧ 10*w^k+x^2+2*y^2+3*z^2+x*y*z=n) →
    ∃ w x y z : ℕ, 3<w ∧ 10*w^k+x^2+2*y^2+3*z^2+x*y*z=n

/-- The remaining coefficients after removing the coefficient-one case. -/
def H4 : Prop :=
  ∀ c k : ℕ, c ∈ ({3,4,6,7} : Finset ℕ) → (k=4 ∨ k=5) → ∀ n : ℕ,
    (¬ ∃ w x y z : ℕ, w≤3 ∧ c*w^k+x^2+2*y^2+3*z^2+x*y*z=n) →
    ∃ w x y z : ℕ, 3<w ∧ c*w^k+x^2+2*y^2+3*z^2+x*y*z=n

theorem main : H1 → H2 → H3 → H4 → type_of% @OMA.S_oeis_a352259.main := by
  classical
  intro excluded cover ten other
  refine ⟨A352259Repair.coefficient_one cover 6 (Or.inr (Or.inr rfl)), ?_, ?_, ?_⟩
  · intro n
    exact ⟨fun rep bad => excluded n bad rep, cover n⟩
  · intro k hlo hhi n
    by_cases small : ∃ w x y z : ℕ, w≤3 ∧ 10*w^k+x^2+2*y^2+3*z^2+x*y*z=n
    · obtain ⟨w,x,y,z,_,h⟩ := small
      exact ⟨w,x,y,z,h⟩
    · obtain ⟨w,x,y,z,_,h⟩ := ten k hlo hhi n small
      exact ⟨w,x,y,z,h⟩
  · intro c k hc hk n
    by_cases hone : c=1
    · subst c
      obtain ⟨w,x,y,z,h⟩ := A352259Repair.coefficient_one cover k
        (hk.elim Or.inl fun h => Or.inr (Or.inl h)) n
      exact ⟨w,x,y,z,by simpa only [one_mul] using h⟩
    · have hrest : c ∈ ({3,4,6,7} : Finset ℕ) := by simpa [hone] using hc
      by_cases small : ∃ w x y z : ℕ, w≤3 ∧ c*w^k+x^2+2*y^2+3*z^2+x*y*z=n
      · obtain ⟨w,x,y,z,_,h⟩ := small
        exact ⟨w,x,y,z,h⟩
      · obtain ⟨w,x,y,z,_,h⟩ := other c k hrest hk n small
        exact ⟨w,x,y,z,h⟩

end OMA.R_oeis_a352259_R1
