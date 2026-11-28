import OMAStatements.S_mo_507196

/-!
# A counterexample to Marcel K. Goh's sum-product monotonicity question

For A = {301 + 24i | 0 ≤ i ≤ 9} as a finite subset of the reals,
increasing h = 924253162587040062998649 by one decreases |(hA)·A| by seven.
We transfer to natural numbers, translate all ten progressions by a common
offset so their members are multiples of their respective steps, and count
their union by inclusion–exclusion on intersections of intervals of multiples.

Source: https://mathoverflow.net/questions/507196
-/

namespace OMA.Goh

open scoped Pointwise

/-- Multiples of a positive step in the half-open interval (lo, hi]. -/
structure Block where
  lo : ℕ
  hi : ℕ
  step : ℕ
  pos : 0 < step

def Block.elems (b : Block) : Finset ℕ :=
  (Finset.Ioc (b.lo / b.step) (b.hi / b.step)).image (· * b.step)

theorem Block.mem_elems {b : Block} {x : ℕ} :
    x ∈ b.elems ↔ b.lo < x ∧ x ≤ b.hi ∧ b.step ∣ x := by
  simp only [Block.elems, Finset.mem_image, Finset.mem_Ioc,
    Nat.div_lt_iff_lt_mul b.pos, Nat.le_div_iff_mul_le b.pos]
  constructor
  · rintro ⟨k, ⟨hlo, hhi⟩, rfl⟩
    exact ⟨hlo, hhi, dvd_mul_left _ _⟩
  · rintro ⟨hlo, hhi, k, rfl⟩
    exact ⟨k, by simpa [mul_comm] using And.intro hlo hhi, Nat.mul_comm ..⟩

def Block.size (b : Block) : ℕ := b.hi / b.step - b.lo / b.step

theorem Block.card_elems (b : Block) : b.elems.card = b.size := by
  rw [Block.elems, Finset.card_image_of_injective, Nat.card_Ioc]
  · rfl
  · intro i j h
    exact Nat.mul_left_cancel b.pos (by simpa [Nat.mul_comm] using h)

def Block.meet (b c : Block) : Block :=
  ⟨max b.lo c.lo, min b.hi c.hi, Nat.lcm b.step c.step, Nat.lcm_pos b.pos c.pos⟩

theorem Block.elems_meet (b c : Block) : (b.meet c).elems = b.elems ∩ c.elems := by
  ext x
  simp only [Block.mem_elems, Finset.mem_inter, Block.meet, max_lt_iff, le_min_iff,
    Nat.lcm_dvd_iff]
  tauto

def blockUnion : List Block → Finset ℕ
  | [] => ∅
  | b :: bs => b.elems ∪ blockUnion bs

theorem mem_blockUnion {bs : List Block} {x : ℕ} :
    x ∈ blockUnion bs ↔ ∃ b ∈ bs, x ∈ b.elems := by
  induction bs with
  | nil => simp [blockUnion]
  | cons b bs ih => simp [blockUnion, ih]

def countWithin (w : Block) : List Block → ℕ
  | [] => 0
  | b :: bs => (w.meet b).size + countWithin w bs - countWithin (w.meet b) bs

theorem card_within (w : Block) (bs : List Block) :
    (w.elems ∩ blockUnion bs).card = countWithin w bs := by
  induction bs generalizing w with
  | nil => simp [blockUnion, countWithin]
  | cons b bs ih =>
    rw [blockUnion, Finset.inter_union_distrib_left, countWithin,
      ← Block.card_elems, ← ih, ← ih, Block.elems_meet]
    have H := Finset.card_union_add_card_inter (w.elems ∩ b.elems) (w.elems ∩ blockUnion bs)
    have E : (w.elems ∩ b.elems) ∩ (w.elems ∩ blockUnion bs) =
        (w.elems ∩ b.elems) ∩ blockUnion bs := by ext; simp; tauto
    rw [E] at H
    omega

def countUnion : List Block → ℕ
  | [] => 0
  | b :: bs => b.size + countUnion bs - countWithin b bs

theorem card_blockUnion (bs : List Block) : (blockUnion bs).card = countUnion bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [blockUnion, countUnion, ← Block.card_elems, ← ih, ← card_within]
    have H := Finset.card_union_add_card_inter b.elems (blockUnion bs)
    omega

def gohNatFactors : Finset ℕ := {301, 325, 349, 373, 397, 421, 445, 469, 493, 517}

def gohNatSums (t : ℕ) : Finset ℕ :=
  (Finset.range (9*t+1)).image (fun k : ℕ => 301*t+24*k)

theorem mem_gohNatSums {t y : ℕ} :
    y ∈ gohNatSums t ↔ ∃ i ≤ 9*t, 301*t+24*i = y := by
  simp [gohNatSums]

theorem gohNatFactors_one : gohNatFactors = gohNatSums 1 := by decide

theorem gohNat_sums (t : ℕ) : t • gohNatFactors = gohNatSums t := by
  induction t with
  | zero => rw [zero_nsmul]; decide
  | succ t ih =>
    rw [succ_nsmul, ih, gohNatFactors_one]
    ext y
    rw [Finset.mem_add, mem_gohNatSums]
    constructor
    · rintro ⟨u, hu, v, hv, rfl⟩
      obtain ⟨i, hi, rfl⟩ := mem_gohNatSums.mp hu
      obtain ⟨j, hj, rfl⟩ := mem_gohNatSums.mp hv
      exact ⟨i+j, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      let i := min k (9*t)
      let j := k-i
      have hi : i ≤ 9*t := min_le_right _ _
      have he : i ≤ k := min_le_left _ _
      have hj : j ≤ 9 := by dsimp [j,i]; omega
      exact ⟨_, mem_gohNatSums.mpr ⟨i, hi, rfl⟩,
        _, mem_gohNatSums.mpr ⟨j, by omega, rfl⟩, by dsimp [j]; omega⟩

noncomputable def gohRealFactors : Finset ℝ := gohNatFactors.image (Nat.castRingHom ℝ)

theorem gohReal_sums (t : ℕ) :
    t • gohRealFactors = (gohNatSums t).image (Nat.castRingHom ℝ) := by
  rw [← gohNat_sums, Finset.image_nsmul]
  rfl

theorem gohReal_card (t : ℕ) :
    ((t • gohRealFactors)*gohRealFactors).card = (gohNatSums t * gohNatFactors).card := by
  rw [gohReal_sums, gohRealFactors, ← Finset.image_mul, Finset.card_image_of_injective]
  exact Nat.cast_injective

def gohList : List ℕ := [301, 325, 349, 373, 397, 421, 445, 469, 493, 517]

def gohShift : ℕ := 42053518897710322866438575

theorem gohList_pos {a : ℕ} (ha : a ∈ gohList) : 0 < a := by
  simp only [gohList, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h|h|h|h|h|h|h|h|h <;> omega

def gohBlock (t a : ℕ) : Block where
  lo := t * (gohShift + 301 * a) - 1
  hi := t * (gohShift + 517 * a)
  step := 24 * max a 1
  pos := Nat.mul_pos (by decide) (lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _))

def gohBlocks (t : ℕ) : List Block := gohList.map (gohBlock t)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem goh_count_before :
    countUnion (gohBlocks 924253162587040062998649) = 82576450023294683720152026 := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem goh_count_after :
    countUnion (gohBlocks 924253162587040062998650) = 82576450023294683720152019 := by
  decide +kernel

private theorem gohList_factor_mem {a : ℕ} : a ∈ gohList ↔ a ∈ gohNatFactors := by
  simp [gohList, gohNatFactors]

private theorem gohBase_dvd {a : ℕ} (ha : a ∈ gohList) :
    24*a ∣ gohShift + 301*a := by
  simp only [gohList, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with h|h|h|h|h|h|h|h|h|h <;> subst a <;> decide

private theorem mem_gohBlock_iff {t a x : ℕ} (ht : 0 < t) (ha : a ∈ gohList) :
    x ∈ (gohBlock t a).elems ↔
      ∃ k ≤ 9*t, x = gohShift*t + (301*t + 24*k)*a := by
  have hpos : 0 < a := gohList_pos ha
  have hbasepos : 0 < t*(gohShift + 301*a) := by
    exact Nat.mul_pos ht (by unfold gohShift; positivity)
  have hdvd : 24*a ∣ t*(gohShift + 301*a) :=
    dvd_mul_of_dvd_right (gohBase_dvd ha) t
  rw [Block.mem_elems]
  change (t*(gohShift + 301*a)-1 < x ∧ x ≤ t*(gohShift+517*a) ∧ 24*max a 1 ∣ x) ↔ _
  rw [max_eq_left hpos]
  constructor
  · rintro ⟨hlo,hhi,hx⟩
    have hle : t*(gohShift+301*a) ≤ x := by omega
    obtain ⟨k, hk⟩ := Nat.dvd_sub hx hdvd
    have hxk : x = t*(gohShift+301*a) + (24*a)*k := by omega
    refine ⟨k, ?_, ?_⟩
    · have hb : t*(gohShift+517*a) = t*(gohShift+301*a) + (24*a)*(9*t) := by ring
      rw [hb, hxk] at hhi
      exact (Nat.le_of_mul_le_mul_left (Nat.le_of_add_le_add_left hhi) (by positivity))
    · rw [hxk]; ring
  · rintro ⟨k,hk,rfl⟩
    have he : gohShift*t+(301*t+24*k)*a = t*(gohShift+301*a)+(24*a)*k := by ring
    have hb : t*(gohShift+517*a) = t*(gohShift+301*a)+(24*a)*(9*t) := by ring
    rw [he,hb]
    exact ⟨by omega, Nat.add_le_add_left (Nat.mul_le_mul_left _ hk) _,
      dvd_add hdvd (dvd_mul_right _ _)⟩

theorem nat_product_count (t : ℕ) (ht : 0 < t) :
    (gohNatSums t * gohNatFactors).card = (blockUnion (gohBlocks t)).card := by
  have hsets : (gohNatSums t * gohNatFactors).image (fun y => gohShift*t+y) =
      blockUnion (gohBlocks t) := by
    ext x
    rw [Finset.mem_image, mem_blockUnion]
    constructor
    · rintro ⟨y,hy,rfl⟩
      obtain ⟨s,hs,a,ha,rfl⟩ := Finset.mem_mul.mp hy
      obtain ⟨k,hk,rfl⟩ := mem_gohNatSums.mp hs
      have hal := gohList_factor_mem.mpr ha
      exact ⟨gohBlock t a, List.mem_map.mpr ⟨a,hal,rfl⟩,
        (mem_gohBlock_iff ht hal).mpr ⟨k,hk,rfl⟩⟩
    · rintro ⟨b,hb,hx⟩
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      obtain ⟨k,hk,rfl⟩ := (mem_gohBlock_iff ht ha).mp hx
      exact ⟨_, Finset.mem_mul.mpr ⟨_, mem_gohNatSums.mpr ⟨k,hk,rfl⟩,
        a,gohList_factor_mem.mp ha,rfl⟩, rfl⟩
  rw [← hsets, Finset.card_image_of_injective]
  exact fun _ _ h => Nat.add_left_cancel h

theorem real_product_count (t : ℕ) (ht : 0 < t) :
    ((t • gohRealFactors) * gohRealFactors).card = countUnion (gohBlocks t) := by
  rw [gohReal_card, nat_product_count t ht, card_blockUnion]

/-- Refutation of Goh’s Statement 1. -/
theorem refutation : ¬ (type_of% @OMA.S_mo_507196.main) := by
  intro h
  have hcard := h gohRealFactors 924253162587040062998649 (by decide)
  rw [real_product_count _ (by decide), real_product_count _ (by decide)] at hcard
  rw [goh_count_before] at hcard
  change 82576450023294683720152026 ≤
    countUnion (gohBlocks 924253162587040062998650) at hcard
  rw [goh_count_after] at hcard
  exact (by decide : ¬ (82576450023294683720152026 ≤ 82576450023294683720152019)) hcard

/-- Goh's Statement 2 also fails, by taking B to be the h-fold sumset. -/
theorem statement_two_false :
    ¬ (∀ A B : Finset ℝ, (B * A).card ≤ ((A + B) * A).card) := by
  intro hyp
  apply refutation
  intro A h _
  rw [succ_nsmul, add_comm (h • A)]
  exact hyp A (h • A)

end OMA.Goh

theorem OMA.disproof : ¬ (type_of% @OMA.S_mo_507196.main) := OMA.Goh.refutation
