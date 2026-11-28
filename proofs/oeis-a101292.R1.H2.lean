import OMAReductions.R_oeis_a101292_R1
import Mathlib

/-!
# The finite Fibonacci factoriangular bound

This proves the finite step in the reduction of OEIS A101292. For every Fibonacci
number F, one of 5F² + 4 and 5F² - 4 is a square. If F = n! + n(n+1)/2
and d ≤ n is positive, then 2F is congruent to n(n+1) modulo d. Hence the same
choice of sign has to pass a square-residue test for every such d.

Bit i of a block mask represents the candidate n = base + i. For each sign
the kernel checks the residue tables and the intersection of their periodic
masks. The interval [101, 151) uses only moduli at most 101. Subsequent blocks
cover the rest of [151, 140000000) and can use all listed moduli.
-/

namespace OMA.FactoriangularSieve

def leftOffset (positive : Bool) : ℕ := if positive then 0 else 16

def rightOffset (positive : Bool) : ℕ := if positive then 16 else 0

private theorem cassini (m : ℕ) :
    (2 * (Nat.fib (m + 1) : ℤ) - Nat.fib m)^2 - 5 * (Nat.fib m : ℤ)^2 =
      4 * (-1)^m := by
  induction m with
  | zero => norm_num [Nat.fib]
  | succ m ih =>
    rw [show m.succ + 1 = m + 2 by omega, Nat.fib_add_two, Nat.cast_add, pow_succ (-1 : ℤ) m]
    linarith only [ih]

private theorem fibonacci_square (m : ℕ) :
    ∃ (positive : Bool) (z : ℕ),
      z^2 + leftOffset positive = 5 * (2 * Nat.fib m)^2 + rightOffset positive := by
  let t : ℤ := 2 * (Nat.fib (m+1) : ℤ) - Nat.fib m
  have h : t^2 - 5 * (Nat.fib m : ℤ)^2 = 4 * (-1)^m := cassini m
  have habs := sq_abs t
  rcases neg_one_pow_eq_or ℤ m with e | e
  · refine ⟨true, 2 * t.natAbs, ?_⟩
    change (2 * t.natAbs)^2 + 0 = 5 * (2 * Nat.fib m)^2 + 16
    rw [e] at h
    zify
    nlinarith only [h, habs]
  · refine ⟨false, 2 * t.natAbs, ?_⟩
    change (2 * t.natAbs)^2 + 16 = 5 * (2 * Nat.fib m)^2 + 0
    rw [e] at h
    zify
    nlinarith only [h, habs]

/-- Each row stores two masks of shifted square residues, two masks of admissible
input residues, and enough repetitions of the period to cover a block. -/
structure Row where
  modulus : ℕ
  depth : ℕ
  squaresPlus : ℕ
  squaresMinus : ℕ
  allowedPlus : ℕ
  allowedMinus : ℕ

def squares (t : Row) (s : Bool) := if s then t.squaresPlus else t.squaresMinus

def allowed (t : Row) (s : Bool) := if s then t.allowedPlus else t.allowedMinus

/-- Check that every square has its bit set and each matching input residue is retained. -/
def valid (t : Row) (s : Bool) : Bool :=
  (List.range t.modulus).all fun r =>
    (squares t s).testBit ((r^2 + leftOffset s) % t.modulus) &&
    (!(squares t s).testBit ((5 * (r * (r+1))^2 + rightOffset s) % t.modulus) ||
      (allowed t s).testBit r)

private theorem allowed_of_solution {n m : ℕ} (he : Nat.fib m = n.factorial + n*(n+1)/2)
    {s : Bool} {z : ℕ} (hz : z^2 + leftOffset s = 5*(2*Nat.fib m)^2 + rightOffset s)
    {t : Row} (hv : valid t s = true) (hp : 0 < t.modulus) (hle : t.modulus ≤ n) :
    (allowed t s).testBit (n % t.modulus) = true := by
  let p := t.modulus
  have hf : 2*Nat.fib m = 2*n.factorial + n*(n+1) := by
    rw [he, Nat.mul_add, Nat.mul_div_cancel' (Nat.two_dvd_mul_add_one n)]
  have fact : n.factorial ≡ 0 [MOD p] :=
    Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_factorial hp hle)
  have rn : n ≡ n%p [MOD p] := (Nat.mod_modEq _ _).symm
  have tri : 2*Nat.fib m ≡ (n%p)*(n%p+1) [MOD p] := by
    rw [hf]
    simpa using (fact.mul_left 2).add (rn.mul (rn.add_right 1))
  have e : (z%p)^2 + leftOffset s ≡ 5*((n%p)*(n%p+1))^2 + rightOffset s [MOD p] :=
    calc
      _ ≡ z^2 + leftOffset s [MOD p] := ((Nat.mod_modEq _ _).pow 2).add_right _
      _ = _ := hz
      _ ≡ _ [MOD p] := ((tri.pow 2).mul_left 5).add_right _
  have hchecks := List.all_eq_true.mp hv
  have hzmem := hchecks (z%p) (List.mem_range.mpr (Nat.mod_lt _ hp))
  have hnmem := hchecks (n%p) (List.mem_range.mpr (Nat.mod_lt _ hp))
  simp only [Bool.and_eq_true] at hzmem hnmem
  have hsq := hzmem.1
  change ((z%p)^2 + leftOffset s)%p = _ at e
  change (squares t s).testBit (((z%p)^2 + leftOffset s)%p) = true at hsq
  rw [e] at hsq
  have hor := hnmem.2
  change (!(squares t s).testBit ((5*((n%p)*(n%p+1))^2 + rightOffset s)%p) || _) = true at hor
  simpa [hsq] using hor

/-- Double a periodic bit mask at each level. -/
def tiles (p mask : ℕ) : ℕ → ℕ
  | 0 => mask
  | h+1 => let prev := tiles p mask h; prev ||| (prev <<< (p * 2^h))

private theorem tile_keeps {p mask h i : ℕ} (hi : i < p*2^h)
    (hb : mask.testBit (i%p) = true) : (tiles p mask h).testBit i = true := by
  induction h generalizing i with
  | zero =>
    have hi' : i < p := by simpa using hi
    simpa [tiles, Nat.mod_eq_of_lt hi'] using hb
  | succ h ih =>
    rw [tiles, Nat.testBit_or, Bool.or_eq_true]
    by_cases hsmall : i < p * 2^h
    · exact Or.inl (ih hsmall hb)
    · right
      have hle : p * 2^h ≤ i := by omega
      rw [Nat.testBit_shiftLeft, Bool.and_eq_true]
      refine ⟨decide_eq_true hle, ih ?_ ?_⟩
      · rw [pow_succ, ← Nat.mul_assoc] at hi
        omega
      · have hid := Nat.sub_add_cancel hle
        have he : (i - p*2^h)%p = i%p := by
          calc
            _ = ((i - p*2^h) + p*2^h)%p := by simp
            _ = _ := by rw [hid]
        rwa [he]


def blockWidth : ℕ := 1048576

def screen (s : Bool) (base span : ℕ) : List Row → ℕ
  | [] => (1 <<< span) - 1
  | t :: ts =>
    if t.modulus ≤ base then
      ((tiles t.modulus (allowed t s) t.depth) >>> (base % t.modulus)) &&& screen s base span ts
    else screen s base span ts

private theorem screen_keeps {s : Bool} {base span i : ℕ} (hi : i < span)
    (hs : span ≤ blockWidth) (ts : List Row)
    (hw : ∀ t ∈ ts, 0 < t.modulus ∧ blockWidth + t.modulus ≤ t.modulus * 2^t.depth)
    (hb : ∀ t ∈ ts, t.modulus ≤ base → (allowed t s).testBit ((base+i)%t.modulus) = true) :
    (screen s base span ts).testBit i = true := by
  induction ts with
  | nil => simp [screen, Nat.shiftLeft_eq, hi]
  | cons t ts ih =>
    have hrest := ih (fun u hu => hw u (List.mem_cons_of_mem _ hu))
      (fun u hu => hb u (List.mem_cons_of_mem _ hu))
    by_cases hle : t.modulus ≤ base
    · simp only [screen, if_pos hle, Nat.testBit_and, Nat.testBit_shiftRight, Bool.and_eq_true]
      refine ⟨tile_keeps ?_ ?_, hrest⟩
      · obtain ⟨hp, hl⟩ := hw t List.mem_cons_self
        have := Nat.mod_lt base hp
        omega
      · simpa only [Nat.mod_add_mod] using hb t List.mem_cons_self hle
    · simpa only [screen, if_neg hle] using hrest

/-- The shifts of the squares and the inputs are scaled by four to keep all
congruences over natural numbers. The kernel checks each table in `row_checks`. -/
def rows : List Row := [
  ⟨3, 19, 3, 6, 7, 2⟩,
  ⟨7, 18, 23, 92, 127, 42⟩,
  ⟨11, 17, 571, 1896, 1879, 730⟩,
  ⟨13, 17, 5659, 4317, 7511, 6371⟩,
  ⟨17, 16, 107287, 119179, 115783, 101731⟩,
  ⟨19, 16, 199411, 221534, 464199, 177514⟩,
  ⟨23, 16, 340831, 6228582, 8076911, 3533782⟩,
  ⟨29, 16, 332473075, 49520265, 476466375, 406393731⟩,
  ⟨31, 16, 303908791, 1203184698, 1976567255, 936294902⟩,
  ⟨37, 15, 96068509339, 4808487665, 130448187215, 131336914223⟩,
  ⟨41, 15, 1870503675703, 777510181313, 2082488776271, 2007550504343⟩,
  ⟨43, 15, 3678700564051, 4002612996880, 8226495280887, 4133836747294⟩,
  ⟨47, 15, 4626135339999, 29855724800106, 131059018147447, 35688112805634⟩,
  ⟨53, 15, 5310023542746835, 4559690538391275, 8671683090280047, 7449575848893899⟩,
  ⟨59, 15, 156326468341437115, 150939287980557676, 546344317708666191, 229007069278686630⟩,
  ⟨61, 15, 1662926210933060155, 474015242213111967, 2264539484251510495, 2047510085516495559⟩,
  ⟨67, 14, 61808106872519771731, 46241316017578142520, 135024578183033740375, 39412852994624682530⟩,
  ⟨71, 14, 20052041432995567487, 1312705115036141421100, 2132802546168155651303, 614188133798314830146⟩,
  ⟨73, 14, 9059857384996697084767, 3675691943047429354897, 8979540798317416425167, 8265751238099565072391⟩,
  ⟨79, 14, 89932533647391829339959, 305154494153700930954774, 581259486944638223397999, 211297228205252636262042⟩,
  ⟨83, 14, 2911111237809585785085595, 4420339343613209337351438, 8612122338082161130762183, 4546813605711303947999774⟩,
  ⟨89, 14, 526807005835216593886842679, 533148806426900443895945697, 549911450052394084309667527, 517246313116422567616952235⟩,
  ⟨97, 14, 152076272278209298711361952607, 43104705356517105549237548465, 143065502793686150744142595303, 137081622542883235717911539387⟩,
  ⟨101, 14, 1550432784880709368503235994227, 1896779248669726661325393992845, 2324198542892312979887206495575, 2013169934805709923061296063187⟩,
  ⟨103, 14, 1760368345969468176824550810519, 1154095884365064961796603325552, 9928571437940014881025863157087, 4086174539809030564927952282854⟩,
  ⟨107, 14, 50079290986288516948354744811035, 140280929734758769319719848333058, 148745175924801768990076287432023, 73304414495468987564784203785678⟩,
  ⟨109, 14, 473022961816146413042658758988475, 73468808099822475922407501314707, 616584320010384252891427931475151, 524255393464662330197461837157235⟩,
  ⟨113, 14, 8586949319576899938239170417650583, 2792486070026317050019337616217007, 9713796101419942226347351489212151, 10232638333830505024060620724535871⟩,
  ⟨127, 14, 30790515292689894969866990722818747159, 12774380559868407391681940263919890004, 152974102249399584616010748410608931943, 81332813549378923504726570344621672030⟩,
  ⟨131, 13, 736595995152387833549853625256200223419, 2459696370242386462738872949426437702980, 2634143403482249904644896814526521765359, 1225878236855633372424652856998965011150⟩,
  ⟨137, 13, 144045494737659012533968429665233398647703, 155565846090157318109513049281549099848615, 160232142359427941724971025929746856087255, 146216865560419225389533699253318521789291⟩,
  ⟨139, 13, 264983527547230301571683161851591864167155, 648934554470436277233072673053409870569814, 660072155693322665946012564967820188130895, 346478357446234249224633083873620124852990⟩,
  ⟨149, 13, 441852139177177952668163358831104772057793267, 506979650667259209718993179200267078184705665, 686396187477764947898361543838440675230211183, 562002560821123560467226493273816250440735123⟩,
  ⟨151, 13, 425021430996567349671854096638566139059703607, 38530941524789361121097528723407771052484126, 2566746353862747411610681792189425004047862887, 1030747089958792358333466747631923634411605562⟩]

private theorem row_checks :
    (rows.all fun t =>
      decide (0 < t.modulus ∧ blockWidth + t.modulus ≤ t.modulus * 2^t.depth) &&
      valid t true && valid t false) = true := by decide +kernel

/-- Both signs have empty intersections in the initial interval and in all 134 blocks. -/
private theorem range_checks :
    (screen false 101 50 rows == 0 && screen true 101 50 rows == 0 &&
      (List.range 134).all fun j =>
        let base := 151 + j * blockWidth
        screen false base blockWidth rows == 0 && screen true base blockWidth rows == 0) = true := by
  decide +kernel

private theorem excluded {n m : ℕ} (hn : 101 ≤ n) (hbound : n < 140000000)
    (he : Nat.fib m = n.factorial + n*(n+1)/2) : False := by
  obtain ⟨s, z, hz⟩ := fibonacci_square m
  have checks := range_checks
  simp only [Bool.and_eq_true, beq_iff_eq] at checks
  have keep {base span i : ℕ} (hrep : n = base+i) (hi : i < span) (hs : span ≤ blockWidth) :
      (screen s base span rows).testBit i = true := by
    have perRow := List.all_eq_true.mp row_checks
    apply screen_keeps hi hs
    · intro t ht
      have hc := perRow t ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      exact hc.1.1
    · intro t ht hle
      have hc := perRow t ht
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      rw [← hrep]
      apply allowed_of_solution he hz _ hc.1.1.1 (by omega)
      cases s
      · exact hc.2
      · exact hc.1.2
  by_cases small : n < 151
  · have bit := keep (base := 101) (span := 50) (i := n-101) (by omega) (by omega) (by decide)
    cases s <;> simp_all
  · let j := (n-151) / blockWidth
    let i := (n-151) % blockWidth
    have hj : j < 134 := by dsimp [j, blockWidth]; omega
    have hr : n = (151 + j*blockWidth) + i := by dsimp [j,i,blockWidth]; omega
    have hi : i < blockWidth := Nat.mod_lt _ (by decide)
    have bit := keep hr hi (le_refl _)
    have hc := List.all_eq_true.mp checks.2 j (List.mem_range.mpr hj)
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    cases s <;> simp_all

end OMA.FactoriangularSieve

theorem OMA.solution : OMA.R_oeis_a101292_R1.H2 := by
  intro n m hn hbound he
  exact OMA.FactoriangularSieve.excluded hn hbound he
