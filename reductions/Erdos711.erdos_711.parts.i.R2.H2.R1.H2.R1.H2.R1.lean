import OMAReductions.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1

/-!
Erdős and Pomerance, Matching the natural numbers up to n with distinct
multiples in another interval (1980), §6 (17), give h(n,k) ≪ n√k.
We use the consecutive multiples straddling the boundary of two length-n
blocks to obtain the explicit finite cutoff b(4b+1), b = ⌊q/2⌋. Eight
disjoint families of smooth integers also settle the square-root endpoint.

The remaining case is a minimal Hall obstruction. Its neighborhood has
exactly one fewer element, and deleting any one divisor leaves it unchanged.
The sparse and centre-cover bounds used below are the prior reductions
by Steve Digital (PR #5001) and @physbuzz.
-/
-- Credit: @studer

namespace OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1_H2_R1

open Filter Finset

/-- Extract a minimal deficient subfamily of an arbitrary finite numbered set system. -/
def H1 : Prop :=
  ∀ (U : Finset ℕ) (T : ℕ → Finset ℕ), (U.biUnion T).card < U.card →
    ∃ V ⊆ U, V.Nonempty ∧ (V.biUnion T).card + 1 = V.card ∧
      (∀ W ⊂ V, W.card ≤ (W.biUnion T).card) ∧
      (∀ d ∈ V, (V.erase d).biUnion T = V.biUnion T)

/-- Rule out a Hall-critical rough family above the block cutoff. -/
def H2 : Prop :=
  ∀ δ : ℝ, 0 < δ → δ < 1/2 → ∀ᶠ n : ℕ in atTop,
    let q := ⌊(n:ℝ)^δ⌋₊
    let b := q/2
    ∀ r : ℕ, n^2 < r → r < (Icc 1 n).lcm id →
      let I := Icc (r+1) (r+n*q)
      let N := fun W : Finset ℕ => I.filter fun y => ∃ d ∈ W, d ∣ y
      ∀ V : Finset ℕ,
        (∀ d ∈ V, 1 ≤ d ∧ d ≤ n ∧ ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ Nat.sqrt n < p) →
        (∃ y ∈ I, q < (V.filter (· ∣ y)).card) →
        (∀ C ⊆ I, C.card ≤ ⌊(n:ℝ)^(δ/4)⌋₊ → ∃ d ∈ V, ∀ c ∈ C, ¬ d ∣ c) →
        b*(4*b+1) < V.card →
        (N V).card + 1 = V.card →
        (∀ W ⊂ V, W.card ≤ (N W).card) →
        (∀ d ∈ V, N (V.erase d) = N V) → False

theorem card_append (r w v : ℕ) (U : Finset ℕ) :
    ((Icc (r+1) (r+(w+v))).filter (fun y => ∃ d ∈ U, d ∣ y)).card = ((Icc (r+1) (r+w)).filter (fun y => ∃ d ∈ U, d ∣ y)).card + ((Icc (r+w+1) (r+w+v)).filter (fun y => ∃ d ∈ U, d ∣ y)).card := by
  classical
  have heq : (Icc (r+1) (r+(w+v))).filter (fun y => ∃ d ∈ U, d ∣ y) = (Icc (r+1) (r+w)).filter (fun y => ∃ d ∈ U, d ∣ y) ∪ (Icc (r+w+1) (r+w+v)).filter (fun y => ∃ d ∈ U, d ∣ y) := by
    ext x
    simp only [mem_filter, mem_Icc, mem_union]
    constructor
    · rintro ⟨⟨hlo,hhi⟩,hd⟩
      by_cases h : x ≤ r+w
      · exact Or.inl ⟨⟨hlo,h⟩,hd⟩
      · exact Or.inr ⟨⟨by omega, by omega⟩,hd⟩
    · rintro (⟨⟨_,_⟩,hd⟩|⟨⟨_,_⟩,hd⟩) <;> exact ⟨⟨by omega,by omega⟩,hd⟩
  rw [heq, card_union_of_disjoint]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hx).1).2
  have hy' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hy).1).1
  omega

/-- Recover each divisor as the gap between the consecutive multiples on
opposite sides of the common boundary of two length-n windows. -/
theorem adjacent_product (r n : ℕ) (U : Finset ℕ)
    (bounds : ∀ d ∈ U, 1 ≤ d ∧ d ≤ n) :
    U.card ≤ ((Icc (r+1) (r+n)).filter (fun y => ∃ d ∈ U, d ∣ y)).card * ((Icc (r+n+1) (r+n+n)).filter (fun y => ∃ d ∈ U, d ∣ y)).card := by
  classical
  let last (d : ℕ) := (r+n) / d * d
  rw [← card_product]
  apply card_le_card_of_injOn (fun d => (last d, last d + d))
  · intro d hd
    obtain ⟨hdpos,hdn⟩ := bounds d hd
    have hmod := Nat.mod_lt (r+n) hdpos
    have heq := Nat.mod_add_div (r+n) d
    rw [Nat.mul_comm d] at heq
    change (r+n)%d + last d = r+n at heq
    have hdvd : d ∣ last d := dvd_mul_left _ _
    exact mem_product.mpr
      ⟨mem_filter.mpr ⟨mem_Icc.mpr ⟨by dsimp only; omega, by dsimp only; omega⟩,
        d,hd,hdvd⟩,
       mem_filter.mpr ⟨mem_Icc.mpr ⟨by dsimp only; omega, by dsimp only; omega⟩,
        d,hd,dvd_add hdvd (dvd_refl _)⟩⟩
  · intro d hd e he h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    dsimp only at h₁ h₂
    omega

private theorem two_blocks_mass {u a c b : ℕ}
    (hu : u ≤ b*(4*b+1)) (hac : u ≤ a*c) : u ≤ b*(a+c) := by
  by_cases h : 4*b < a+c
  · exact hu.trans (Nat.mul_le_mul_left b h)
  have hle : (a : ℤ)+c ≤ 4*b := by exact_mod_cast (Nat.le_of_not_gt h)
  have hpos : 0 ≤ (a:ℤ)+c := by positivity
  have hac' : (u : ℤ) ≤ a*c := by exact_mod_cast hac
  suffices (u : ℤ) ≤ b*((a : ℤ)+c) by exact_mod_cast this
  nlinarith [sq_nonneg ((a:ℤ)-c), mul_nonneg hpos (sub_nonneg.mpr hle)]

/-- Uniform Hall expansion for small families, with a bound independent of
both prime factors and divisor-count estimates. -/
theorem blocks_hall (r n q : ℕ) (U : Finset ℕ)
    (bounds : ∀ d ∈ U, 1 ≤ d ∧ d ≤ n)
    (small : U.card ≤ (q/2) * (4*(q/2)+1)) :
    U.card ≤ ((Icc (r+1) (r+(n*q))).filter (fun y => ∃ d ∈ U, d ∣ y)).card := by
  let b := q/2
  have localBound (s : ℕ) : U.card ≤ b*((Icc (s+1) (s+(n+n))).filter (fun y => ∃ d ∈ U, d ∣ y)).card := by
    rw [card_append]
    exact two_blocks_mass small (adjacent_product s n U bounds)
  have accum (t : ℕ) : t * U.card ≤ b * ((Icc (r+1) (r+(t*(n+n)))).filter (fun y => ∃ d ∈ U, d ∣ y)).card := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [Nat.succ_mul, Nat.succ_mul, card_append, Nat.mul_add]
      exact Nat.add_le_add ih (localBound _)
  by_cases hb : b = 0
  · change U.card ≤ b * (4*b+1) at small
    simp [hb] at small
    simp [small]
  have hl := Nat.le_of_mul_le_mul_left (accum b) (Nat.pos_of_ne_zero hb)
  apply hl.trans
  apply card_le_card
  intro y hy
  obtain ⟨hyI,hd⟩ := mem_filter.mp hy
  obtain ⟨hlo,hhi⟩ := mem_Icc.mp hyI
  have hbq : 2*b ≤ q := by dsimp [b]; omega
  have hwidth : b*(n+n) ≤ n*q := by
    calc b*(n+n) = n*(2*b) := by ring
         _ ≤ n*q := Nat.mul_le_mul_left _ hbq
  exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hlo,by omega⟩,hd⟩


/-- Eight disjoint sets of smooth numbers leave sufficiently few eligible
divisors for the exact square-root window, including the rounding losses. -/
theorem rough_card {n : ℕ} (hq : 128 ≤ Nat.sqrt n) (U : Finset ℕ)
    (bounds : ∀ d ∈ U, 1 ≤ d ∧ d ≤ n ∧
      ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ Nat.sqrt n < p) :
    U.card ≤ (Nat.sqrt n / 2) * (4*(Nat.sqrt n / 2)+1) := by
  classical
  let b := Nat.sqrt n / 2
  let X := Icc (b+1) (2*b)
  let S := (range 8) ×ˢ X
  let f (z : ℕ × ℕ) := 2^z.1 * z.2
  have hX {x : ℕ} (hx : x ∈ X) := mem_Icc.mp hx
  have sep {i j x y : ℕ} (hij : i<j) (hx : x ∈ X) (hy : y ∈ X) :
      2^i*x < 2^j*y := by
    have hp : 2^(i+1) ≤ (2:ℕ)^j := Nat.pow_le_pow_right (by decide) hij
    calc 2^i*x ≤ 2^i*(2*b) := Nat.mul_le_mul_left _ (hX hx).2
         _ = 2^(i+1)*b := by rw [pow_succ, Nat.mul_assoc]
         _ ≤ 2^j*b := Nat.mul_le_mul_right _ hp
         _ < 2^j*y := Nat.mul_lt_mul_of_pos_left (hX hy).1 (by positivity)
  have inj : Set.InjOn f (S : Set (ℕ × ℕ)) := by
    rintro ⟨i,x⟩ hi ⟨j,y⟩ hj heq
    have hx := (mem_product.mp hi).2
    have hy := (mem_product.mp hj).2
    change 2^i*x = 2^j*y at heq
    have e : i = j := by
      rcases lt_trichotomy i j with h|h|h
      · exact False.elim ((sep h hx hy).ne heq)
      · exact h
      · exact False.elim ((sep h hy hx).ne heq.symm)
    subst j
    exact Prod.ext rfl (Nat.eq_of_mul_eq_mul_left (by positivity) heq)
  have hcard : (S.image f).card = 8*b := by
    rw [card_image_of_injOn inj, card_product, card_range, Nat.card_Icc]
    congr 1
    omega
  have twice : 2*b ≤ Nat.sqrt n := by dsimp [b]; omega
  have disj : Disjoint U (S.image f) := by
    apply disjoint_left.mpr
    intro d hd hy
    obtain ⟨⟨i,x⟩,hix,rfl⟩ := mem_image.mp hy
    obtain ⟨p,hp,hdvd,hpq⟩ := (bounds _ hd).2.2
    have hx := hX (mem_product.mp hix).2
    change p ∣ 2^i*x at hdvd
    rcases hp.dvd_mul.mp hdvd with h|h
    · have := Nat.le_of_dvd (by decide : 0 < 2) (hp.dvd_of_dvd_pow h)
      omega
    · have := Nat.le_of_dvd (by omega : 0 < x) h
      omega
  have sub : U ∪ S.image f ⊆ Icc 1 n := by
    intro y hy
    rcases mem_union.mp hy with h|h
    · exact mem_Icc.mpr ⟨(bounds _ h).1,(bounds _ h).2.1⟩
    obtain ⟨⟨i,x⟩,hix,rfl⟩ := mem_image.mp h
    obtain ⟨hi,hx⟩ := mem_product.mp hix
    have hi₇ : i ≤ 7 := by have := mem_range.mp hi; omega
    have hp : (2:ℕ)^i ≤ Nat.sqrt n :=
      (Nat.pow_le_pow_right (by decide) hi₇).trans hq
    have hxx := hX hx
    apply mem_Icc.mpr
    change 1 ≤ 2^i*x ∧ 2^i*x ≤ n
    constructor
    · exact Nat.mul_pos (by positivity) (by omega)
    · exact (Nat.mul_le_mul hp (hxx.2.trans twice)).trans (Nat.sqrt_le n)
  have total := card_le_card sub
  rw [card_union_of_disjoint disj, hcard, Nat.card_Icc] at total
  have upper : Nat.sqrt n+1 ≤ 2*b+2 := by dsimp [b]; omega
  have nn := (Nat.lt_succ_sqrt' n).trans_le (Nat.pow_le_pow_left upper 2)
  have enough : 3 ≤ b := by dsimp [b]; omega
  change U.card ≤ b*(4*b+1)
  nlinarith [show U.card + 8*b ≤ n by omega]

/-- The residual statement holds at its endpoint δ = 1/2 in every shift. -/
theorem rough_endpoint (r n : ℕ) (hq : 128 ≤ Nat.sqrt n) (U : Finset ℕ)
    (bounds : ∀ d ∈ U, 1 ≤ d ∧ d ≤ n ∧
      ∃ p : ℕ, p.Prime ∧ p ∣ d ∧ Nat.sqrt n < p) :
    U.card ≤ ((Icc (r+1) (r+(n*⌊(n:ℝ)^(1/2:ℝ)⌋₊))).filter (fun y => ∃ d ∈ U, d ∣ y)).card := by
  rw [← Real.sqrt_eq_rpow, Real.nat_floor_real_sqrt_eq_nat_sqrt]
  exact blocks_hall r n n.sqrt U (fun d hd => ⟨(bounds d hd).1,(bounds d hd).2.1⟩)
    (rough_card hq U bounds)


private theorem multiples_union (I W : Finset ℕ) :
    W.biUnion (fun d => I.filter (d ∣ ·)) = I.filter (fun y => ∃ d ∈ W, d ∣ y) := by
  apply Finset.ext
  intro y
  constructor
  · intro hy
    obtain ⟨d,hd,hdy⟩ := mem_biUnion.mp hy
    exact mem_filter.mpr ⟨(mem_filter.mp hdy).1,d,hd,(mem_filter.mp hdy).2⟩
  · intro hy
    obtain ⟨hyI,d,hd,hdy⟩ := mem_filter.mp hy
    exact mem_biUnion.mpr ⟨d,hd,mem_filter.mpr ⟨hyI,hdy⟩⟩

set_option maxHeartbeats 1000000 in
theorem main : H1 → H2 → OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1.H2 := by
  classical
  intro extract exclude δ hd hhalf
  by_cases endpoint : δ = 1/2
  · subst δ
    filter_upwards [eventually_ge_atTop (128^2 : ℕ)] with n hn
    dsimp only
    intro r _ _ U bounds _ _
    exact rough_endpoint r n (Nat.le_sqrt'.mpr hn) U bounds
  filter_upwards [exclude δ hd (lt_of_le_of_ne hhalf endpoint),
    OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1.small_centres_separate δ hd hhalf,
    eventually_ge_atTop (1 : ℕ)] with n residual moduli hn
  dsimp only at moduli residual ⊢
  intro r hr hm U spec _ _
  let q := ⌊(n:ℝ)^δ⌋₊
  let I := Icc (r+1) (r+n*q)
  let N (V : Finset ℕ) := I.filter fun y => ∃ d ∈ V, d ∣ y
  let T (d : ℕ) := I.filter (d ∣ ·)
  have neighbors (W : Finset ℕ) : W.biUnion T = N W := multiples_union I W
  change U.card ≤ (N U).card
  by_contra! deficient
  obtain ⟨V,hVU,_,hcard,hmin,herase⟩ := extract U T (by rwa [neighbors])
  rw [neighbors] at hcard
  have bad : (N V).card < V.card := by omega
  have rough d (hd : d ∈ V) := spec d (hVU hd)
  have size d (hd : d ∈ V) := And.intro (rough d hd).1 (rough d hd).2.1
  have hq : 0 < q := Nat.le_floor (by
    simpa only [Nat.cast_one] using Real.one_le_rpow (by exact_mod_cast hn : (1:ℝ) ≤ n) hd.le)
  apply residual r hr hm V rough
  · by_contra! sparse
    exact bad.not_ge (OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1.sparse_hall
      r n q hq V size sparse)
  · intro C inside few
    by_contra! cover
    obtain ⟨K,hK,hroom,hsep⟩ := moduli r C inside few
    exact bad.not_ge (OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1.fixed_interval
      V C hK hroom (fun d hd => (size d hd).2) inside cover hsep)
  · by_contra! small
    exact bad.not_ge (blocks_hall r n q V size small)
  · exact hcard
  · intro W hW
    simpa only [neighbors] using hmin W hW
  · intro d hd
    simpa only [neighbors] using herase d hd

end OMA.R_Erdos711_erdos_711_parts_i_R2_H2_R1_H2_R1_H2_R1
