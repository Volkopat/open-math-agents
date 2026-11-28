import OMAStatements.S_oeis_a275667
import Mathlib.Algebra.MonoidAlgebra.Support
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace OpenMath.A275667

open OMA.S_oeis_a275667

noncomputable section

private def doubling : Point →+ Point where
  toFun p := (2 * p.1, 2 * p.2)
  map_zero' := by decide
  map_add' p q := by ext <;> simp [mul_add]

private theorem doubling_injective : Function.Injective doubling := by
  intro p q h
  apply Prod.ext
  · have hx := congrArg Prod.fst h
    change 2 * p.1 = 2 * q.1 at hx
    omega
  · have hy := congrArg Prod.snd h
    change 2 * p.2 = 2 * q.2 at hy
    omega

private def dilate : Config →+* Config :=
  AddMonoidAlgebra.mapDomainRingHom (ZMod 2) doubling

private theorem dilate_eq_square (p : Config) : dilate p = p ^ 2 := by
  induction p using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | single p c =>
    have hc : c * c = c := by
      have h0 : (0 : ZMod 2) * 0 = 0 := zero_mul _
      have h1 : (1 : ZMod 2) * 1 = 1 := one_mul _
      fin_cases c <;> first | exact h0 | exact h1
    rw [pow_two, AddMonoidAlgebra.single_mul_single, hc]
    change AddMonoidAlgebra.mapDomain doubling (AddMonoidAlgebra.single p c) = _
    rw [AddMonoidAlgebra.mapDomain_single]
    congr 1
    ext <;> simp [doubling, two_mul]
  | add p q hp hq =>
    have h₂ : (2 : Config) = 0 := by
      let i : ZMod 2 →+* Config := AddMonoidAlgebra.singleZeroRingHom
      calc
        (2 : Config) = i 2 := (map_ofNat i 2).symm
        _ = i 0 := congrArg i (show (2 : ZMod 2) = 0 by decide)
        _ = 0 := map_zero i
    rw [map_add, hp, hq]
    calc
      p ^ 2 + q ^ 2 = p ^ 2 + q ^ 2 + 2 * p * q := by simp [h₂]
      _ = (p + q) ^ 2 := by ring

private theorem support_dilate (p : Config) :
    (dilate p).coeff.support = p.coeff.support.image doubling :=
  Finsupp.mapDomain_support_of_injective doubling_injective p.coeff

private theorem support_shift_dilate (p : Config) (v : Point) :
    (monomial v * dilate p).coeff.support = (p.coeff.support.image doubling).image (v + ·) := by
  rw [monomial, AddMonoidAlgebra.support_coeff_single_mul_eq_image _ (fun _ => by rw [one_mul]) (.all v),
    support_dilate]

private theorem shift_dilate_card (p : Config) (v : Point) :
    (monomial v * dilate p).coeff.support.card = p.coeff.support.card := by
  rw [support_shift_dilate, Finset.card_image_of_injective _ (add_right_injective v),
    Finset.card_image_of_injective _ doubling_injective]

private theorem disjoint_shift_dilate (p : Config) (v w : Point)
    (h : (v.1 % 2, v.2 % 2) ≠ (w.1 % 2, w.2 % 2)) :
    Disjoint (monomial v * dilate p).coeff.support (monomial w * dilate p).coeff.support := by
  rw [support_shift_dilate, support_shift_dilate, Finset.disjoint_left]
  intro r hr hs
  rcases Finset.mem_image.mp hr with ⟨a, ha, rfl⟩
  rcases Finset.mem_image.mp hs with ⟨b, hb, hab⟩
  rcases Finset.mem_image.mp ha with ⟨x, _, rfl⟩
  rcases Finset.mem_image.mp hb with ⟨y, _, rfl⟩
  apply h
  have hx := congrArg Prod.fst hab
  have hy := congrArg Prod.snd hab
  change w.1 + 2 * y.1 = v.1 + 2 * x.1 at hx
  change w.2 + 2 * y.2 = v.2 + 2 * x.2 at hy
  exact Prod.ext (by omega) (by omega)

private theorem stencil_square_card (p : Config) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    (stencil s * p ^ 2).coeff.support.card = 3 * p.coeff.support.card := by
  rw [← dilate_eq_square, stencil, add_mul, add_mul]
  have h01 : ((0 : ℤ) % 2, (0 : ℤ) % 2) ≠ (s % 2, 0 % 2) := by
    rcases hs with rfl | rfl <;> decide
  have h02 : ((0 : ℤ) % 2, (0 : ℤ) % 2) ≠ (0 % 2, s % 2) := by
    rcases hs with rfl | rfl <;> decide
  have h12 : (s % 2, (0 : ℤ) % 2) ≠ (0 % 2, s % 2) := by
    rcases hs with rfl | rfl <;> decide
  have d01 := disjoint_shift_dilate p (0, 0) (s, 0) h01
  have d02 := disjoint_shift_dilate p (0, 0) (0, s) h02
  have d12 := disjoint_shift_dilate p (s, 0) (0, s) h12
  simp only [AddMonoidAlgebra.coeff_add]
  have dUnion := Finset.disjoint_union_left.mpr ⟨d02, d12⟩
  have hFirst := Finsupp.support_add_eq d01
  have dLast : Disjoint
      ((monomial (0, 0) * dilate p).coeff + (monomial (s, 0) * dilate p).coeff).support
      (monomial (0, s) * dilate p).coeff.support := hFirst.symm ▸ dUnion
  rw [Finsupp.support_add_eq dLast, hFirst, Finset.card_union_of_disjoint dUnion,
    Finset.card_union_of_disjoint d01, shift_dilate_card, shift_dilate_card, shift_dilate_card]
  omega

private def stepPair : Config := stencil 1 * stencil (-1)

private theorem generation_even (n : ℕ) : generation (2 * n) = stepPair ^ n := by
  induction n with
  | zero => simp [generation]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega]
    rw [generation, generation, if_neg (by omega), if_pos (by omega), ih, pow_succ]
    unfold stepPair
    ring

private theorem generation_odd (n : ℕ) :
    generation (2 * n + 1) = stencil 1 * stepPair ^ n := by
  rw [generation, if_pos (by omega), generation_even]

theorem recurrence : population 0 = 1 ∧ ∀ n : ℕ, population (2 * n + 1) = 3 * population n := by
  constructor
  · simp [population, generation]
  intro n
  rcases (show ∃ k, n = 2 * k ∨ n = 2 * k + 1 from ⟨n / 2, by omega⟩) with
    ⟨k, rfl | rfl⟩
  · have hshape : generation (2 * (2 * k) + 1) = stencil 1 * generation (2 * k) ^ 2 := by
      rw [generation_odd, generation_even, show 2 * k = k * 2 by omega, pow_mul]
    simpa only [population, hshape] using stencil_square_card (generation (2 * k)) 1 (Or.inl rfl)
  · have hshape : generation (2 * (2 * k + 1) + 1) = stencil (-1) * generation (2 * k + 1) ^ 2 := by
      rw [generation_odd (2 * k + 1), generation_odd k, pow_succ,
        show 2 * k = k * 2 by omega, pow_mul, mul_pow]
      unfold stepPair
      ring
    simpa only [population, hshape] using stencil_square_card (generation (2 * k + 1)) (-1) (Or.inr rfl)


private def pointResidue (k : ℤ) (v : Point) : Point := (v.1 % k, v.2 % k)

private def blockWidth (wide : Bool) : ℤ := if wide then 4 else 2

private def inflate (wide : Bool) : Config →+* Config :=
  if wide then dilate.comp dilate else dilate

private def cfgSupport (q : Config) : Finset Point := q.coeff.support

private def cfgCard (q : Config) : ℕ := (cfgSupport q).card

private abbrev Block := Point × Option Point

private def blockSupportSource (p : Config) (dir : Option Point) : Config :=
  match dir with
  | none => p
  | some d => p + monomial d * p

private def blockConfig (wide : Bool) (p : Config) (b : Block) : Config :=
  monomial b.1 * inflate wide (blockSupportSource p b.2)

private theorem support_shift_inflate (wide : Bool) (p : Config) (v : Point) :
    cfgSupport (monomial v * inflate wide p) =
      (cfgSupport p).image (fun q => v + (blockWidth wide * q.1, blockWidth wide * q.2)) := by
  rw [cfgSupport, monomial, AddMonoidAlgebra.support_coeff_single_mul_eq_image _ (fun _ => by rw [one_mul]) (.all v)]
  cases wide
  · simp [inflate, blockWidth, support_dilate, cfgSupport, Finset.image_image, doubling, Function.comp_def]
  · change ((dilate (dilate p)).coeff.support).image (v + ·) = _
    simp [support_dilate, Finset.image_image, cfgSupport, doubling, blockWidth, Function.comp_def]
    congr 1
    funext q
    exact congrArg (v + ·) (Prod.ext (by omega) (by omega))

private theorem block_residue (wide : Bool) (p : Config) (b : Block) {q : Point}
    (hq : q ∈ cfgSupport (blockConfig wide p b)) :
    pointResidue (blockWidth wide) q = pointResidue (blockWidth wide) b.1 := by
  unfold blockConfig at hq
  rw [support_shift_inflate] at hq
  obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hq
  cases wide <;> apply Prod.ext <;> simp [pointResidue, blockWidth, Int.add_emod]

private theorem block_card (wide : Bool) (p : Config) (b : Block) :
    cfgCard (blockConfig wide p b) = cfgCard (blockSupportSource p b.2) := by
  rw [cfgCard, blockConfig, support_shift_inflate]
  apply Finset.card_image_of_injective
  intro q r h
  have h' := add_left_cancel h
  have hx := congrArg Prod.fst h'
  have hy := congrArg Prod.snd h'
  cases wide <;> simp only [blockWidth, Bool.false_eq_true, if_false, if_true] at hx hy
  all_goals exact Prod.ext (by omega) (by omega)

private theorem support_cfgAdd_le (p q : Config) :
    cfgSupport (p + q) ⊆ cfgSupport p ∪ cfgSupport q := by
  change (p + q).coeff.support ⊆ _
  rw [AddMonoidAlgebra.coeff_add]
  exact Finsupp.support_add

private theorem cfgCard_add (p q : Config) (h : Disjoint (cfgSupport p) (cfgSupport q)) :
    cfgCard (p + q) = cfgCard p + cfgCard q := by
  change (p+q).coeff.support.card = _
  change Disjoint p.coeff.support q.coeff.support at h
  rw [AddMonoidAlgebra.coeff_add, Finsupp.support_add_eq h, Finset.card_union_of_disjoint h]
  rfl

private theorem mem_block_sum (wide : Bool) (p : Config) (L : List Block) {q : Point}
    (hq : q ∈ cfgSupport ((L.map (blockConfig wide p)).sum)) :
    ∃ b ∈ L, q ∈ cfgSupport (blockConfig wide p b) := by
  induction L with
  | nil => simp [cfgSupport] at hq
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons] at hq
    rcases Finset.mem_union.mp (support_cfgAdd_le _ _ hq) with hb | hs
    · exact ⟨b, List.mem_cons_self, hb⟩
    · obtain ⟨b', hL, ht⟩ := ih hs
      exact ⟨b', List.mem_cons_of_mem _ hL, ht⟩

private theorem sum_block_card (wide : Bool) (p : Config) (L : List Block)
    (distinct : L.Pairwise (fun b c => pointResidue (blockWidth wide) b.1 ≠
      pointResidue (blockWidth wide) c.1)) :
    cfgCard ((L.map (blockConfig wide p)).sum) =
      (L.map (fun b => cfgCard (blockSupportSource p b.2))).sum := by
  induction L with
  | nil => simp [cfgCard, cfgSupport]
  | cons b L ih =>
    rw [List.pairwise_cons] at distinct
    simp only [List.map_cons, List.sum_cons]
    have disj : Disjoint (cfgSupport (blockConfig wide p b))
        (cfgSupport ((L.map (blockConfig wide p)).sum)) := by
      rw [Finset.disjoint_left]
      intro q hq hqL
      obtain ⟨c, hc, hqc⟩ := mem_block_sum wide p L hqL
      exact distinct.1 c hc ((block_residue wide p b hq).symm.trans (block_residue wide p c hqc))
    rw [cfgCard_add _ _ disj, block_card, ih distinct.2]

private theorem monomial_mul (v w : Point) : monomial v * monomial w = monomial (v+w) := by
  simp [monomial, AddMonoidAlgebra.single_mul_single]

private theorem dilate_monomial (v : Point) : dilate (monomial v) = monomial (2*v.1,2*v.2) := by
  change AddMonoidAlgebra.mapDomain doubling (AddMonoidAlgebra.single v 1) = _
  rw [AddMonoidAlgebra.mapDomain_single]
  rfl

private theorem inflate_monomial (wide : Bool) (v : Point) :
    inflate wide (monomial v) = monomial (blockWidth wide * v.1, blockWidth wide * v.2) := by
  cases wide
  · exact dilate_monomial v
  · change dilate (dilate (monomial v)) = _
    rw [dilate_monomial, dilate_monomial]
    simp only [blockWidth, if_true]
    exact congrArg monomial (Prod.ext (by omega) (by omega))

private theorem cfg_double (p : Config) : p + p = 0 := by
  let i : ZMod 2 →+* Config := AddMonoidAlgebra.singleZeroRingHom
  have twoZero : (2 : Config) = 0 := by
    calc
      (2 : Config) = i 2 := (map_ofNat i 2).symm
      _ = i 0 := congrArg i (show (2 : ZMod 2) = 0 by decide)
      _ = 0 := map_zero i
  rw [← two_mul, twoZero, zero_mul]

private def blockPolynomial (wide : Bool) (b : Block) : Config :=
  match b.2 with
  | none => monomial b.1
  | some d => monomial b.1 + monomial (b.1 + (blockWidth wide * d.1, blockWidth wide * d.2))

private theorem blockConfig_eq (wide : Bool) (p : Config) (b : Block) :
    blockConfig wide p b = blockPolynomial wide b * inflate wide p := by
  rcases b with ⟨v, _ | d⟩
  · rfl
  · simp only [blockConfig, blockSupportSource, blockPolynomial, map_add, map_mul, mul_add, add_mul,
      ← mul_assoc, monomial_mul, inflate_monomial]

private theorem sum_block_poly (wide : Bool) (p : Config) (L : List Block) :
    ((L.map (blockConfig wide p)).sum) = (L.map (blockPolynomial wide)).sum * inflate wide p := by
  induction L with
  | nil => simp
  | cons b L ih => simp only [List.map_cons, List.sum_cons, blockConfig_eq, ih, add_mul]

private def offsets : List Point :=
  [(0,0), (1,0), (-1,0), (0,1), (0,-1), (1,-1), (-1,1)]

private def smallBlocks : List Block :=
  [((0,0), none), ((-1,0), some (1,0)), ((0,-1), some (0,1)), ((-1,1), some (1,-1))]

private def separateBlocks : List Block :=
  offsets.map (fun v => (v, none))

/-- The sixteen residue classes of the surviving offsets modulo four.
Each block is a singleton or a pair separated by four times its direction. -/
private def cubeBlocks : List Block :=
  [((0,0), none), ((0,-3), none), ((0,-2), some (0,1)), ((0,3), none),
   ((-3,0), none), ((-3,1), some (1,-1)), ((-3,2), some (1,0)), ((-3,3), none),
   ((-2,0), some (1,0)), ((2,-3), some (0,1)), ((-2,2), some (1,-1)), ((-2,-1), some (0,1)),
   ((3,0), none), ((3,-3), none), ((-1,-2), some (1,0)), ((-1,3), some (1,-1))]

private theorem stepPair_offsets : stepPair = (offsets.map monomial).sum := by
  simp only [stepPair, stencil, mul_add, add_mul, monomial_mul, offsets,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  norm_num [Prod.mk_add_mk]
  calc
    _ = (monomial (0,0) + monomial (1,0) + monomial (-1,0) + monomial (0,1) + monomial (0,-1) +
      monomial (1,-1) + monomial (-1,1)) + (monomial (0,0) + monomial (0,0)) := by abel
    _ = _ := by rw [cfg_double, add_zero]; abel

private theorem smallBlocks_poly : (smallBlocks.map (blockPolynomial false)).sum = stepPair := by
  rw [stepPair_offsets]
  norm_num [smallBlocks, blockPolynomial, blockWidth, offsets, Prod.mk_add_mk]
  abel

private theorem separateBlocks_poly : (separateBlocks.map (blockPolynomial true)).sum = stepPair := by
  rw [stepPair_offsets, separateBlocks, List.map_map]
  rfl


private def blockOffsets (wide : Bool) (b : Block) : List Point :=
  match b.2 with
  | none => [b.1]
  | some d => [b.1, b.1 + (blockWidth wide * d.1, blockWidth wide * d.2)]

private theorem blockPolynomial_eq (wide : Bool) (b : Block) :
    blockPolynomial wide b = ((blockOffsets wide b).map monomial).sum := by
  rcases b with ⟨v, _ | d⟩ <;> simp [blockPolynomial, blockOffsets]

private theorem wholeBlockPolynomial (wide : Bool) (L : List Block) :
    (L.map (blockPolynomial wide)).sum = ((L.flatMap (blockOffsets wide)).map monomial).sum := by
  induction L with
  | nil => rfl
  | cons b L ih =>
    simp only [List.map_cons, List.sum_cons, blockPolynomial_eq, List.flatMap_cons,
      List.map_append, List.sum_append]
    rw [ih]

private def doublePoint (v : Point) : Point := (2*v.1, 2*v.2)

private def products (L R : List Point) : List Point :=
  L.flatMap (fun v => R.map (v + ·))

private theorem mapDilate_sum (L : List Point) :
    dilate (L.map monomial).sum = ((L.map doublePoint).map monomial).sum := by
  induction L with
  | nil => simp
  | cons v L ih =>
    simp only [List.map_cons, List.sum_cons, map_add, ih, dilate_monomial, doublePoint]

private theorem monomial_mul_sum (v : Point) (L : List Point) :
    monomial v * (L.map monomial).sum = ((L.map (v + ·)).map monomial).sum := by
  induction L with
  | nil => simp
  | cons q L ih =>
    simp only [List.map_cons, List.sum_cons, mul_add, monomial_mul, ih]

private theorem monomial_sum_mul_sum (L R : List Point) :
    (L.map monomial).sum * (R.map monomial).sum = ((products L R).map monomial).sum := by
  induction L with
  | nil => simp [products]
  | cons v L ih =>
    simp only [List.map_cons, List.sum_cons, add_mul, monomial_mul_sum, ih, products,
      List.flatMap_cons, List.map_append, List.sum_append]

/-- The offsets produced twice in the product of the stencil with its dilate. -/
private def cancelledOffsets : List Point :=
  [(-2,1), (-1,-1), (-1,0), (-1,1), (-1,2), (0,-1), (0,1), (1,-2), (1,-1), (1,0), (1,1), (2,-1)]

private theorem cancelled_sum (L : List Point) :
    ((L.flatMap (fun v => [v,v])).map monomial).sum = 0 := by
  induction L with
  | nil => rfl
  | cons v L ih =>
    simp only [List.flatMap_cons, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, add_zero, cfg_double, ih]

private theorem cubeBlocks_poly : (cubeBlocks.map (blockPolynomial true)).sum = stepPair ^ 3 := by
  have hc : stepPair ^ 3 = stepPair * dilate stepPair := by
    rw [dilate_eq_square]
    ring
  rw [hc, stepPair_offsets, mapDilate_sum, monomial_sum_mul_sum, wholeBlockPolynomial]
  have h : (products offsets (offsets.map doublePoint)).Perm
      ((cubeBlocks.flatMap (blockOffsets true)) ++ (cancelledOffsets.flatMap (fun v => [v,v]))) := by decide +kernel
  have hs := (h.map monomial).sum_eq
  simpa only [List.map_append, List.sum_append, cancelled_sum, add_zero] using hs.symm

private def evenCard (t : ℕ) : ℕ := cfgCard (stepPair ^ t)

private theorem evenCard_eq (t : ℕ) : population (2*t) = evenCard t := by
  rw [population, generation_even]
  rfl

private theorem inflate_square (q : Config) : inflate false q = q ^ 2 :=
  dilate_eq_square q

private theorem inflate_fourth (q : Config) : inflate true q = q ^ 4 := by
  change dilate (dilate q) = _
  rw [dilate_eq_square (dilate q), dilate_eq_square q, ← pow_mul]

private theorem evenCard_double (t : ℕ) : evenCard (2*t) = evenCard t := by
  unfold evenCard cfgCard cfgSupport
  rw [Nat.mul_comm 2 t, pow_mul, ← dilate_eq_square, support_dilate,
    Finset.card_image_of_injective _ doubling_injective]

private theorem block_card_small (q : Config) :
    cfgCard (stepPair * inflate false q) =
      cfgCard q +
        cfgCard (q + monomial (1,0) * q) +
        cfgCard (q + monomial (0,1) * q) +
        cfgCard (q + monomial (1,-1) * q) := by
  have h := sum_block_card false q smallBlocks (by decide)
  rw [sum_block_poly, smallBlocks_poly] at h
  simp only [smallBlocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    blockSupportSource] at h
  simpa only [Nat.add_assoc] using h

private theorem block_card_separate (q : Config) :
    cfgCard (stepPair * inflate true q) = 7 * cfgCard q := by
  have h := sum_block_card true q separateBlocks (by decide)
  rw [sum_block_poly, separateBlocks_poly] at h
  simp only [separateBlocks, offsets, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    add_zero, blockSupportSource] at h
  omega

private theorem block_card_cube (q : Config) :
    cfgCard (stepPair ^ 3 * inflate true q) =
      7 * cfgCard q +
        3 * cfgCard (q + monomial (1,0) * q) +
        3 * cfgCard (q + monomial (0,1) * q) +
        3 * cfgCard (q + monomial (1,-1) * q) := by
  have h := sum_block_card true q cubeBlocks (by decide)
  rw [sum_block_poly, cubeBlocks_poly] at h
  simp only [cubeBlocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    blockSupportSource] at h
  omega

private theorem evenCard_small (t : ℕ) :
    evenCard (2*t+1) = cfgCard (stepPair * inflate false (stepPair ^ t)) := by
  unfold evenCard
  rw [inflate_square, ← pow_mul, mul_comm 2 t, pow_succ, mul_comm]

private theorem evenCard_separate (t : ℕ) : evenCard (4*t+1) = 7 * evenCard t := by
  unfold evenCard
  rw [Nat.mul_comm 4 t, pow_succ, pow_mul, ← inflate_fourth, mul_comm]
  exact block_card_separate _

private theorem evenCard_cube (t : ℕ) :
    evenCard (4*t+3) = 4 * evenCard t + 3 * evenCard (2*t+1) := by
  rw [evenCard_small, block_card_small]
  unfold evenCard
  rw [Nat.mul_comm 4 t, pow_add, pow_mul, ← inflate_fourth, mul_comm, block_card_cube]
  omega

theorem fullRecurrence :
    population 0 = 1 ∧
    (∀ t : ℕ, population (2 * t + 1) = 3 * population t) ∧
    (∀ t : ℕ, population (8 * t + 6) = 3 * population (4 * t + 2) + 4 * population (2 * t)) ∧
    (∀ t : ℕ, population (8 * t + 2) = 3 * population (4 * t) + 4 * population (2 * t)) ∧
    (∀ t : ℕ, population (4 * t) = population (2 * t)) := by
  refine ⟨recurrence.1, recurrence.2, ?_, ?_, ?_⟩
  · intro t
    rw [show 8*t+6 = 2*(4*t+3) by omega, show 4*t+2 = 2*(2*t+1) by omega,
      evenCard_eq, evenCard_eq, evenCard_eq, evenCard_cube]
    omega
  · intro t
    rw [show 8*t+2 = 2*(4*t+1) by omega, show 4*t = 2*(2*t) by omega,
      evenCard_eq, evenCard_eq, evenCard_eq, show 2*(2*t)+1 = 4*t+1 by omega,
      evenCard_separate, evenCard_double]
    omega
  · intro t
    rw [show 4*t = 2*(2*t) by omega, evenCard_eq, evenCard_eq, evenCard_double]

end
end OpenMath.A275667

theorem OMA.solution : type_of% @OMA.S_oeis_a275667.main :=
  OpenMath.A275667.fullRecurrence
