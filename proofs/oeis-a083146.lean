import OMAStatements.S_oeis_a083146
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Tactic

/-!
Franklin T. Adams-Watters's infinitude conjecture in OEIS A083146 holds for
all palindromes consisting of two outer sevens and a positive odd number of
sixes. A proper multiple below the double concatenation has between k+1
and 2k digits, where k is the length of the original palindrome.

Splitting at the middle gives a linear equation relating a digit word to
its reversal. Shorter words have a repeated middle block that cancels.
The three carry tables certify the resulting word equations for arbitrary
lengths. Every table is checked for closure under the carry transitions,
and the checks also verify the initial carries and the terminal conditions.
-/

namespace A083146Carry

/-- Decimal value of a word listed from the least significant digit. -/
def value (word : List ℕ) : ℤ := (Nat.ofDigits (10 : ℕ) word : ℕ)

@[simp] lemma value_nil : value [] = 0 := rfl

lemma value_cons (digit : ℕ) (word : List ℕ) :
    value (digit :: word) = (digit : ℤ) + 10 * value word := by
  simp [value, Nat.ofDigits_cons]

lemma value_append (a b : List ℕ) :
    value (a ++ b) = value a + 10 ^ a.length * value b := by
  simp [value, Nat.ofDigits_append]

@[simp] lemma value_single (x : ℕ) : value [x] = x := by
  simp [value_cons]

lemma value_sandwich (x : ℕ) (word : List ℕ) (y : ℕ) :
    value (x :: (word ++ [y])) = (x : ℤ) + 10 * value word + 10 ^ (word.length + 1) * y := by
  rw [value_cons, value_append, value_single, pow_succ]
  ring

lemma value_bounds (word : List ℕ) (digits : ∀ d ∈ word, d < 10) :
    0 ≤ value word ∧ value word < 10 ^ word.length := by
  constructor
  · exact Int.natCast_nonneg _
  · induction word with
    | nil => norm_num
    | cons d word ih =>
        have hd : (d : ℤ) < 10 := by exact_mod_cast digits d (by simp)
        have hr := ih (fun n hn => digits n (List.mem_cons_of_mem _ hn))
        rw [value_cons, List.length_cons, pow_succ]
        omega

def Carry (b left right : ℤ) (word : List ℕ) : Prop :=
  left + 69 * value word.reverse - b * value word = right * 10 ^ word.length

def bounded (x : ℤ) : Prop := -32 ≤ x ∧ x ≤ 70

def highDigit (b left x : ℤ) : ℤ := (left - b * x) % 10

def leftStep (b left x : ℤ) : ℤ := (left + 69 * highDigit b left x - b * x) / 10

def rightStep (b left upper x : ℤ) : ℤ := upper - 69 * x + b * highDigit b left x

lemma envelope (b left right : ℤ) (word : List ℕ)
    (hb : 0 ≤ b ∧ b ≤ 30) (hl : bounded left)
    (digits : ∀ d ∈ word, d < 10) (h : Carry b left right word) : bounded right := by
  obtain ⟨h0, h1⟩ := value_bounds word digits
  obtain ⟨g0, g1⟩ := value_bounds word.reverse (by simpa using digits)
  rw [List.length_reverse] at g1
  have hp : (0 : ℤ) < 10 ^ word.length := by positivity
  unfold Carry at h
  unfold bounded at hl ⊢
  constructor
  · by_contra! hn
    have hbad : right ≤ -33 := by omega
    have hmul := mul_le_mul_of_nonneg_right hbad hp.le
    have hsmall := mul_le_mul_of_nonneg_left (show value word ≤ 10 ^ word.length - 1 by omega) hb.1
    have hsmall' := mul_le_mul_of_nonneg_right hb.2 (show 0 ≤ 10 ^ word.length - 1 by omega)
    nlinarith only [h, hl.1, g0, hmul, hsmall, hsmall', hp]
  · by_contra! hn
    have hbad : 71 ≤ right := by omega
    have hmul := mul_le_mul_of_nonneg_right hbad hp.le
    have hprod : 0 ≤ b * value word := mul_nonneg hb.1 h0
    nlinarith only [h, hl.2, g1, hmul, hprod, hp]

lemma peel (b left upper : ℤ) (x y : ℕ) (word : List ℕ)
    (hb : 0 ≤ b ∧ b ≤ 30) (hl : bounded left)
    (hx : x < 10) (hy : y < 10)
    (digits : ∀ d ∈ word, d < 10)
    (h : left + 69 * value (x :: (word ++ [y])).reverse - b * value (x :: (word ++ [y])) =
      upper * 10 ^ (word.length + 1)) :
    (y : ℤ) = highDigit b left x ∧ bounded (leftStep b left x) ∧
      bounded (rightStep b left upper x) ∧
      Carry b (leftStep b left x) (rightStep b left upper x) word := by
  rw [show (x :: (word ++ [y])).reverse = y :: (word.reverse ++ [x]) by simp,
    value_sandwich, value_sandwich, List.length_reverse, pow_succ] at h
  have hdigit : (y : ℤ) = highDigit b left x := by
    have eq : left - b * x - y = 10 *
        ((upper - 69 * x + b * y) * 10 ^ word.length -
          (69 * value word.reverse - b * value word) - 7 * y) := by linear_combination h
    unfold highDigit
    omega
  have hdiv : left + 69 * y - b * x = 10 *
      ((upper - 69 * x + b * y) * 10 ^ word.length -
        (69 * value word.reverse - b * value word)) := by linear_combination h
  have hnext : Carry b (leftStep b left x) (rightStep b left upper x) word := by
    unfold Carry leftStep rightStep
    rw [← hdigit, hdiv]
    omega
  have hleft : bounded (leftStep b left x) := by
    unfold bounded leftStep at *
    rw [← hdigit]
    have c1 := mul_le_mul_of_nonneg_left (show (x : ℤ) ≤ 9 by omega) hb.1
    have c2 := mul_le_mul_of_nonneg_right hb.2 (show (0 : ℤ) ≤ 9 by norm_num)
    have cx : 0 ≤ b * x := mul_nonneg hb.1 (Int.natCast_nonneg _)
    omega
  exact ⟨hdigit, hleft, envelope b _ _ word hb hleft digits hnext, hnext⟩

/-- Reachable carry pairs, indexed by the left carry and packed by right carry. -/
private def shortTable : List ℕ := [
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  1073741824, 128, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0,
  0]

/-- Reachable carry pairs, indexed by the left carry and packed by right carry. -/
private def oddTable : List ℕ := [
  0, 0, 0, 2417851639229258349412352, 0, 0,
  1155173304420532224, 2475880078570760549798248448, 2361183241434822606848, 1152922055438499840, 2305843009213693952, 2535301202817642044428230066176,
  635065658005039310281600139777, 2147483648, 2535920170476101495329879228416, 302822905887870175674368, 1267650600228229401496703205376, 2361183243633845862400,
  144397214018437120, 70368744177664, 2535301202817642187365344608256, 714291402667664700091905868289, 2305844246164340736, 2891827931770649450263284287744,
  79383207842078927123489226752, 38685626227668135738147840, 1362439624921939971147776, 73931373508722425856, 1267689890317366885740974186498, 620178946111951521133363200,
  635063240153400081023385207305, 4836883870149602854313984, 576460752841361444, 79383212564445128518291947520, 4835703278458516732379136, 317542521660303333939371573248,
  79228162588195750683609137152, 19807040628570596794106381442, 316912650099149276721161699328, 73787011548066353665, 681201653384322477981696, 295724365936564649984,
  80621147953998080782496727104, 2475880078570760687505637392, 362107133192679678795529060388, 79247543180261674323470712896, 158456334475567483935596216320, 19185272488103436615680,
  37778949912608899334208, 147573961387916918784, 141012911522048, 80623300689031517802688708672, 1267650600228517632010293878784, 2857165762082109633240385077504,
  19380667129991486454628352, 4835703278458516967325824, 316999846529633376283423408384, 18050202565083136, 158495086212620070334513545216, 151115727612637054369792,
  713208205133289746069236777032, 2475880078863573692562015232, 316990021604732649414747881760, 5080525306615399804374463021064, 1270127084769709969498532544512, 77543618831961009298604032,
  9903525045890946757445025792, 348170638355419161482494080, 39614081257204369327388754176, 89131682828547384199390199872, 75557863725914323419136, 39691603662280502668485085440,
  5080525301893033321513390964744, 562949991171072, 40321453977334178726981664800, 5070602405644669907139246948360, 19807645091475891713242300416, 18931619624025128435744,
  4731589859313153511488, 158765810056796764329790668800, 18889465931513016090624, 5080680044324157022142371729416, 158456325176102627793944182784, 44565841414273707488621625376,
  4731752019677457416192, 147573952589676478464, 39614100183563663643355643936, 4406653222912, 38685626227668133590597632, 18889465949109421604864,
  5080505921227200648186005819400, 8796093022208, 9024791440801792, 4731589854906499989504, 8192, 9671406565924232660779008,
  4406636445696, 4835703278458516698824704, 4951760161753207118023884800, 5070602400912917605986812825600, 0, 0,
  0]

/-- Reachable carry pairs, indexed by the left carry and packed by right carry. -/
private def longTable : List ℕ := [
  0, 0, 0, 0, 0, 2361183241434822606848,
  0, 1099511627776, 0, 0, 1024, 0,
  0, 604462909807314587353088, 0, 0, 562949953486848, 131072,
  0, 38685626227668133591121920, 77371252455336267181195264, 0, 309485009821345068724781056, 8388608,
  0, 288230376151711744, 4951760157141521099596496896, 0, 0, 4611686018964258816,
  1073741824, 0, 316912650093950838521594904576, 633825300114114700748351602689, 0, 4,
  590295810358705651712, 137438953472, 32, 549755813888, 128, 18889465931478580854784,
  512, 75557863725914323419136, 17592186044416, 302231454903657293676544, 70368744177664, 16384,
  0, 562949953486848, 9671406556917033397649408, 2251799813685248, 38685626227668133590597632, 9007199254740992,
  2097152, 36028797018963968, 0, 1237940039285380274899124224, 33554432, 576460752303423488,
  1152921504606846976, 19807040628566084398654423040, 536870912, 0, 158456325028528675187087900672, 316912650057057350378470768640,
  73786976294838206465, 147573952589676412928, 2535301200456458803027766149124, 590295810427425128448, 16, 32,
  64, 9444732965739290427392, 18889465931478580854784, 37778931862957161710080, 8796093022208, 0,
  302231454938841665769472, 8192, 0, 2417851639229258349412352, 4835703278458516698824704, 0,
  0, 4503599627370496, 0, 0, 36028797023158272, 0,
  0, 0, 0, 0, 0, 0,
  0, 0, 4294967296, 0, 0, 0,
  0]

private def coord (i : Fin 103) : ℤ := (i.val : ℤ) - 32

private def index (x : ℤ) (hx : bounded x) : Fin 103 :=
  ⟨(x + 32).toNat, by unfold bounded at hx; omega⟩

@[simp] private lemma coord_index (x : ℤ) (hx : bounded x) : coord (index x hx) = x := by
  unfold coord index bounded at *
  simp
  omega

private def member (table : List ℕ) (left right : ℤ) : Bool :=
  ((table[(left + 32).toNat]?).getD 0).testBit (right + 32).toNat

instance (x : ℤ) : Decidable (bounded x) := by unfold bounded; infer_instance

private def Closed (table : List ℕ) (b : ℤ) : Prop :=
  ∀ i j : Fin 103, member table (coord i) (coord j) = true → ∀ x : Fin 10,
    bounded (leftStep b (coord i) x.val) → bounded (rightStep b (coord i) (10 * coord j) x.val) →
      member table (leftStep b (coord i) x.val) (rightStep b (coord i) (10 * coord j) x.val) = true

private def Forbidden (table : List ℕ) (b : ℤ) (odd : Bool) : Prop :=
  ∀ i j : Fin 103, member table (coord i) (coord j) = true →
    if odd then ∀ x : Fin 10, coord i + (69 - b) * x.val ≠ 10 * coord j else coord i ≠ coord j

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem short_closed : Closed shortTable 3 := by
  unfold Closed
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem short_forbidden : Forbidden shortTable 3 false ∧ Forbidden shortTable 3 true := by
  unfold Forbidden
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
private theorem odd_closed : Closed oddTable 30 := by
  unfold Closed
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem odd_forbidden : Forbidden oddTable 30 false := by
  unfold Forbidden
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem long_closed : Closed longTable 30 := by
  unfold Closed
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem long_forbidden : Forbidden longTable 30 true := by
  unfold Forbidden
  decide +kernel

private theorem no_word (table : List ℕ) (b : ℤ) (odd : Bool)
    (closed : Closed table b) (forbidden : Forbidden table b odd) (hb : 0 ≤ b ∧ b ≤ 30)
    (word : List ℕ) (digits : ∀ d ∈ word, d < 10)
    (parity : word.length % 2 = if odd then 1 else 0)
    (l r : ℤ) (hl : bounded l) (hr : bounded r) (mem : member table l r = true)
    (h : Carry b l r word) : False := by
  induction word using List.bidirectionalRec generalizing l r with
  | nil =>
      have hf := forbidden (index l hl) (index r hr) (by simpa using mem)
      cases odd
      · simp [Carry] at h
        exact hf (by simpa using h)
      · simp at parity
  | singleton x =>
      have hf := forbidden (index l hl) (index r hr) (by simpa using mem)
      cases odd
      · simp at parity
      · have hg := hf ⟨x, digits x (by simp)⟩
        simp only [coord_index] at hg
        apply hg
        simp [Carry] at h
        linear_combination h
  | cons_append x word y ih =>
      have hx : x < 10 := digits x (by simp)
      have hy : y < 10 := digits y (by simp)
      have ds : ∀ d ∈ word, d < 10 := by
        intro d hd
        exact digits d (by simp [hd])
      have hp : word.length % 2 = if odd then 1 else 0 := by
        simp only [List.length_cons, List.length_append, List.length_nil] at parity
        omega
      have hpull : l + 69 * value (x :: (word ++ [y])).reverse -
          b * value (x :: (word ++ [y])) = (10 * r) * 10 ^ (word.length + 1) := by
        simpa [Carry, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h
      obtain ⟨_, hleft, hright, heq⟩ := peel b l (10*r) x y word hb hl hx hy ds hpull
      have hmem := closed (index l hl) (index r hr) (by simpa using mem) ⟨x,hx⟩
      simp only [coord_index] at hmem
      exact ih ds hp _ _ hleft hright (hmem hleft hright) heq

private theorem short_root : ∀ h : Fin 3, ∀ x : Fin 10,
    0 < highDigit 3 (-(h.val : ℤ)) x.val →
    bounded (leftStep 3 (-(h.val : ℤ)) x.val) →
    bounded (rightStep 3 (-(h.val : ℤ)) (230 * h.val) x.val) →
    member shortTable (leftStep 3 (-(h.val : ℤ)) x.val)
      (rightStep 3 (-(h.val : ℤ)) (230 * h.val) x.val) = true := by decide +kernel

private def delta (i : Fin 4) : ℤ := (i.val : ℤ) - 1

private theorem odd_root : ∀ i : Fin 4, ∀ c x : Fin 10,
    0 < highDigit 30 (-delta i - 3 * c.val) x.val →
    bounded (leftStep 30 (-delta i - 3 * c.val) x.val) →
    bounded (rightStep 30 (-delta i - 3 * c.val) (230 * delta i) x.val) →
    member oddTable (leftStep 30 (-delta i - 3 * c.val) x.val)
      (rightStep 30 (-delta i - 3 * c.val) (230 * delta i) x.val) = true := by decide +kernel

private def eta (i : Fin 44) : ℤ := (i.val : ℤ) - 13

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem long_root : ∀ i : Fin 44, ∀ x : Fin 10,
    0 < highDigit 30 (-eta i) x.val → highDigit 30 (-eta i) x.val ≤ 7 →
    bounded (leftStep 30 (-eta i) x.val) →
    bounded (rightStep 30 (-eta i) (23 * eta i) x.val) →
    member longTable (leftStep 30 (-eta i) x.val) (rightStep 30 (-eta i) (23 * eta i) x.val) = true ∨
      (x.val = 7 ∧ highDigit 30 (-eta i) x.val = 7 ∧
        leftStep 30 (-eta i) x.val = 26 ∧ rightStep 30 (-eta i) (23 * eta i) x.val = 26) := by
  decide +kernel

private theorem special_step : ∀ x : Fin 10,
    bounded (leftStep 30 26 x.val) → bounded (rightStep 30 26 260 x.val) →
    member longTable (leftStep 30 26 x.val) (rightStep 30 26 260 x.val) = true ∨
      (x.val = 6 ∧ highDigit 30 26 x.val = 6 ∧
        leftStep 30 26 x.val = 26 ∧ rightStep 30 26 260 x.val = 26) := by decide +kernel

private lemma digits_middle {x y : ℕ} {word : List ℕ}
    (digits : ∀ d ∈ x :: (word ++ [y]), d < 10) : ∀ d ∈ word, d < 10 := by
  intro d hd
  exact digits d (by simp [hd])

private lemma carry_expand {b l r : ℤ} {x y : ℕ} {word : List ℕ}
    (h : Carry b l r (x :: (word ++ [y]))) :
    l + 69 * value (x :: (word ++ [y])).reverse - b * value (x :: (word ++ [y])) =
      (10 * r) * 10 ^ (word.length + 1) := by
  simpa [Carry, pow_succ, mul_assoc, mul_comm, mul_left_comm] using h

/-- The shortened reversal equation admits no word of at least two digits. -/
lemma no_short_word (h : ℤ) (hrange : 0 ≤ h ∧ h ≤ 2) (word : List ℕ)
    (len : 2 ≤ word.length) (last : word.getLast? ≠ some 0)
    (digits : ∀ d ∈ word, d < 10) : ¬ Carry 3 (-h) (23*h) word := by
  intro heq
  cases word using List.bidirectionalRec with
  | nil => simp at len
  | singleton x => simp at len
  | cons_append x mid y =>
      have hx : x < 10 := digits x (by simp)
      have hy : y < 10 := digits y (by simp)
      have hy0 : 0 < y := by
        simpa [Nat.pos_iff_ne_zero, List.getLast?_cons, List.getLast?_concat] using last
      have hm := digits_middle digits
      have hl : bounded (-h) := by unfold bounded; omega
      obtain ⟨hdy, hleft, hright, next⟩ := peel 3 (-h) (230*h) x y mid (by decide) hl hx hy hm
        (by rw [show 230 * h = 10 * (23 * h) by ring]; exact carry_expand heq)
      let i : Fin 3 := ⟨h.toNat, by omega⟩
      have hi : (i.val : ℤ) = h := by dsimp [i]; omega
      have hh := short_root i ⟨x,hx⟩
      simp only [hi] at hh
      have hm' := hh (by omega) hleft hright
      by_cases hp : mid.length % 2 = 0
      · exact no_word _ _ false short_closed short_forbidden.1 (by decide) mid hm hp _ _ hleft hright hm' next
      · exact no_word _ _ true short_closed short_forbidden.2 (by decide) mid hm (by simp; omega) _ _ hleft hright hm' next

/-- An odd palindrome of maximal odd length leads to an impossible even word. -/
lemma no_odd_word (h : ℤ) (hrange : -1 ≤ h ∧ h ≤ 2) (c : ℕ) (hc : c < 10)
    (word : List ℕ) (len : 2 ≤ word.length) (parity : word.length % 2 = 0)
    (last : word.getLast? ≠ some 0) (digits : ∀ d ∈ word, d < 10) :
    ¬ Carry 30 (-h - 3 * c) (23*h) word := by
  intro heq
  cases word using List.bidirectionalRec with
  | nil => simp at len
  | singleton x => simp at len
  | cons_append x mid y =>
      have hx : x < 10 := digits x (by simp)
      have hy : y < 10 := digits y (by simp)
      have hy0 : 0 < y := by simpa [Nat.pos_iff_ne_zero, List.getLast?_cons, List.getLast?_concat] using last
      have hm := digits_middle digits
      have hl : bounded (-h - 3 * c) := by unfold bounded; omega
      obtain ⟨hdy, hleft, hright, next⟩ := peel 30 (-h - 3*c) (230*h) x y mid (by decide) hl hx hy hm
        (by rw [show 230 * h = 10 * (23 * h) by ring]; exact carry_expand heq)
      let i : Fin 4 := ⟨(h+1).toNat, by omega⟩
      have hi : delta i = h := by dsimp [i, delta]; omega
      have hh := odd_root i ⟨c,hc⟩ ⟨x,hx⟩
      simp only [hi] at hh
      have hm' := hh (by omega) hleft hright
      apply no_word _ _ false odd_closed odd_forbidden (by decide) mid hm ?_ _ _ hleft hright hm' next
      change mid.length % 2 = 0
      simp at parity
      omega

private lemma special_word (word : List ℕ) (parity : word.length % 2 = 1)
    (digits : ∀ d ∈ word, d < 10) (h : Carry 30 26 26 word) :
    word = List.replicate word.length 6 := by
  induction word using List.bidirectionalRec with
  | nil => simp at parity
  | singleton x =>
      simp [Carry] at h
      have eq : x = 6 := by omega
      simp [eq]
  | cons_append x mid y ih =>
      have hm := digits_middle digits
      have hp : mid.length % 2 = 1 := by simp at parity; omega
      obtain ⟨hdy, hleft, hright, heq⟩ := peel 30 26 260 x y mid (by decide) (by decide)
        (digits x (by simp)) (digits y (by simp)) hm (carry_expand h)
      rcases special_step ⟨x, digits x (by simp)⟩ hleft hright with bad | ⟨hx,hy,hl,hr⟩
      · exact (no_word _ _ true long_closed long_forbidden (by decide) mid hm hp _ _ hleft hright bad heq).elim
      · have hy' : y = 6 := by
          have hh : (y : ℤ) = 6 := hdy.trans hy
          exact_mod_cast hh
        rw [hl, hr] at heq
        have hs := ih hp hm heq
        simp only [List.length_cons, List.length_append, List.length_nil, zero_add]
        change x :: (mid ++ [y]) = List.replicate (mid.length + 1 + 1) 6
        rw [List.replicate_succ, List.replicate_add]
        change x = 6 at hx
        rw [hx, hy']
        exact congrArg (fun v => 6 :: (v ++ [6])) hs

/-- For the full even palindrome, only the carry pattern of the doubled block works. -/
lemma full_word (h : ℤ) (hrange : -13 ≤ h ∧ h ≤ 30) (word : List ℕ)
    (len : 2 ≤ word.length) (parity : word.length % 2 = 1)
    (last : ∃ d : ℕ, 0 < d ∧ d ≤ 7 ∧ word.getLast? = some d)
    (digits : ∀ d ∈ word, d < 10)
    (heq : -h + 69 * value word.reverse - 30 * value word = 23*h * 10 ^ (word.length - 1)) :
    word = 7 :: (List.replicate (word.length - 2) 6 ++ [7]) := by
  cases word using List.bidirectionalRec with
  | nil => simp at len
  | singleton x => simp at len
  | cons_append x mid y =>
      have hx : x < 10 := digits x (by simp)
      have hy : y < 10 := digits y (by simp)
      obtain ⟨d, hd0, hd7, hy'⟩ := last
      have eq : y = d := by simpa [List.getLast?_cons, List.getLast?_concat] using hy'
      have hm := digits_middle digits
      have hp : mid.length % 2 = 1 := by simp at parity; omega
      have hl : bounded (-h) := by unfold bounded; omega
      obtain ⟨hdy, hleft, hright, next⟩ := peel 30 (-h) (23*h) x y mid (by decide) hl hx hy hm
        (by simpa using heq)
      let i : Fin 44 := ⟨(h+13).toNat, by omega⟩
      have hi : eta i = h := by dsimp [i, eta]; omega
      have hh := long_root i ⟨x,hx⟩
      simp only [hi] at hh
      rcases hh (by omega) (by omega) hleft hright with bad | ⟨hx,hy,hl,hr⟩
      · exact (no_word _ _ true long_closed long_forbidden (by decide) mid hm hp _ _ hleft hright bad next).elim
      · have hy' : y = 7 := by omega
        rw [hl, hr] at next
        have hs := special_word mid hp hm next
        have hn : (x :: (mid ++ [y])).length - 2 = mid.length := by simp
        rw [hn, hx, hy', ← hs]

end A083146Carry

namespace A083146
open A083146Carry OMA.S_oeis_a083146

private def familyWord (t : ℕ) : List ℕ := 7 :: (List.replicate (2*t-1) 6 ++ [7])
private def family (t : ℕ) : ℕ := Nat.ofDigits 10 (familyWord t)

private lemma familyWord_length {t : ℕ} (ht : 0 < t) : (familyWord t).length = 2*t+1 := by
  simp [familyWord]
  omega

private lemma familyWord_reverse (t : ℕ) : (familyWord t).reverse = familyWord t := by
  simp [familyWord]

private lemma familyWord_digits (t : ℕ) : ∀ d ∈ familyWord t, d < 10 := by
  intro d hd
  simp only [familyWord, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | hd | rfl
  · decide
  · have := List.eq_of_mem_replicate hd
    omega
  · decide

private lemma digits_family (t : ℕ) : Nat.digits 10 (family t) = familyWord t := by
  refine Nat.digits_ofDigits _ (by decide) _ (familyWord_digits t) ?_
  intro hd
  have hh : (familyWord t).getLast? = some 7 := by
    simp [familyWord, List.getLast?_cons]
  have he := List.getLast_of_getLast?_eq_some hh
  simp [he]

private lemma repeat_value (q m : ℕ) :
    3 * value (List.replicate m (3*q)) = (q : ℤ) * (10^m - 1) := by
  induction m with
  | zero => simp
  | succ m ih =>
      simp only [List.replicate_succ, value_cons, Nat.cast_mul, Nat.cast_ofNat, pow_succ]
      linear_combination 10 * ih

private lemma family_value {t : ℕ} (ht : 0 < t) : (3 : ℤ) * family t = 23 * 10^(2*t) + 1 := by
  change 3 * value (familyWord t) = _
  have he : 2*t = (2*t-1)+1 := by omega
  have h := repeat_value 2 (2*t-1)
  rw [familyWord, value_sandwich, List.length_replicate, he, pow_succ]
  norm_num at h ⊢
  linear_combination 10 * h

private lemma digits_good (n : ℕ) : ∀ d ∈ Nat.digits 10 n, d < 10 := by
  intro d hd
  exact Nat.digits_lt_base (by decide) hd

private lemma digits_last_nonzero (n : ℕ) : (Nat.digits 10 n).getLast? ≠ some 0 := by
  intro h
  obtain ⟨v, hv⟩ := List.getLast?_eq_some_iff.mp h
  have hvalue : Nat.ofDigits 10 v = n := by
    rw [← Nat.ofDigits_digits 10 n, hv, Nat.ofDigits_append_zero]
  have hd : ∀ d ∈ v, d < 10 := by
    intro d hd
    apply digits_good n d
    rw [hv]
    simp [hd]
  have hb := (value_bounds v hd).2
  have hu : n < 10^v.length := by
    change (↑(Nat.ofDigits (10 : ℕ) v) : ℤ) < 10^v.length at hb
    rw [hvalue] at hb
    exact_mod_cast hb
  have hlen := (Nat.digits_length_le_iff (by decide : 1 < 10) n).mpr hu
  rw [hv] at hlen
  simp at hlen

private lemma pal_words (word : List ℕ) (h : word.reverse = word) :
    (∃ u, word = u.reverse ++ u) ∨ (∃ u c, word = u.reverse ++ (c :: u)) := by
  induction word using List.bidirectionalRec with
  | nil => exact Or.inl ⟨[], rfl⟩
  | singleton c => exact Or.inr ⟨[], c, rfl⟩
  | cons_append x mid y ih =>
      have he : (y :: (mid.reverse ++ [x])) = x :: (mid ++ [y]) := by simpa using h
      obtain ⟨rfl, hh⟩ := List.cons.inj he
      have hm : mid.reverse = mid := List.append_cancel_right hh
      rcases ih hm with ⟨v,hv⟩ | ⟨v,c,hv⟩
      · left
        exact ⟨v ++ [y], by simp [hv, List.reverse_append, List.append_assoc]⟩
      · right
        exact ⟨v ++ [y], c, by simp [hv, List.reverse_append, List.append_assoc]⟩

private lemma value_injective_words {u v : List ℕ} (len : u.length = v.length)
    (hu : ∀ d ∈ u, d < 10) (hv : ∀ d ∈ v, d < 10) (eq : value u = value v) : u = v := by
  induction u generalizing v with
  | nil => simpa using len.symm
  | cons a u ih =>
      cases v with
      | nil => simp at len
      | cons b v =>
          have ha : (a : ℤ) < 10 := by exact_mod_cast hu a (by simp)
          have hb : (b : ℤ) < 10 := by exact_mod_cast hv b (by simp)
          simp only [value_cons] at eq
          have hab : a = b := by omega
          have huv : value u = value v := by omega
          exact congrArg₂ List.cons hab (ih (by simpa using len)
            (fun d hd => hu d (by simp [hd])) (fun d hd => hv d (by simp [hd])) huv)

private lemma strip_suffix (word : List ℕ) (digits : ∀ d ∈ word, d < 10)
    (δ : ℕ) (hδ : δ ≤ word.length) (h : ℕ) (hh : h ≤ 2)
    (div : (10:ℤ)^δ ∣ 3 * value word + h) :
    word.take δ = List.replicate δ (3*h) := by
  let low := word.take δ
  have hlow : low.length = δ := by simp [low, Nat.min_eq_left hδ]
  have dlow : ∀ d ∈ low, d < 10 := fun d hd => digits d (List.mem_of_mem_take hd)
  have he : value word = value low + 10^δ * value (word.drop δ) :=
    calc
      value word = value (low ++ word.drop δ) := congrArg value (List.take_append_drop δ word).symm
      _ = _ := by rw [value_append, hlow]
  obtain ⟨q,hq⟩ := div
  have hp : (0:ℤ) < 10^δ := by positivity
  obtain ⟨hv0,hvlt⟩ := value_bounds low dlow
  rw [hlow] at hvlt
  let l := q - 3 * value (word.drop δ)
  have hl : 3*value low+(h:ℤ) = 10^δ*l := by
    rw [he] at hq
    dsimp [l]
    linear_combination hq
  have hl0 : 0 ≤ l := by
    by_contra! ht
    have hn := mul_neg_of_pos_of_neg hp ht
    omega
  have hl2 : l ≤ 2 := by
    by_contra! ht
    have hn := mul_le_mul_of_nonneg_left (show (3:ℤ) ≤ l by omega) hp.le
    omega
  have powmod := (show (10 : ℤ) ≡ 1 [ZMOD 3] by decide).pow δ
  have hmod : (10:ℤ)^δ % 3 = 1 := by simpa [Int.ModEq] using powmod
  have hlh : l = (h : ℤ) := by
    interval_cases l <;> omega
  have hval : value low = value (List.replicate δ (3*h)) := by
    have hr := repeat_value h δ
    rw [hlh] at hl
    linarith only [hl, hr]
  exact value_injective_words (by rw [hlow, List.length_replicate]) dlow (by intro d hd; have := List.eq_of_mem_replicate hd; omega) hval

private lemma collapse (h δ k : ℕ) (rest : List ℕ)
    (he : 3 * value (List.replicate δ (3*h) ++ rest) + h =
      23 * 10^δ * (3 * value (List.replicate k (3*h) ++ rest).reverse - h * 10^(k+rest.length))) :
    Carry 3 (-(h : ℤ)) (23*h) rest := by
  simp only [List.reverse_append, List.reverse_replicate, value_append, List.length_reverse,
    List.length_replicate, pow_add] at he
  have hlow := repeat_value h δ
  have hhigh := repeat_value h k
  have hp : (0 : ℤ) < 10^δ := by positivity
  unfold Carry
  apply mul_left_cancel₀ hp.ne'
  linear_combination -he + hlow - 23 * 10^δ * 10^rest.length * hhigh

private lemma exclude_short (center digits : List ℕ) (δ h : ℕ)
    (hc : center.length ≤ δ) (hlen : δ + 2 ≤ (center ++ digits).length) (hh : h ≤ 2)
    (good : ∀ d ∈ center ++ digits, d < 10) (last : digits.getLast? ≠ some 0)
    (eq : 3 * value (center ++ digits) + h =
      23 * 10^δ * (3 * value digits.reverse - h * 10^digits.length)) : False := by
  let w := center ++ digits
  let rest := w.drop δ
  change δ + 2 ≤ w.length at hlen
  have hlen' : 2 ≤ rest.length := by simp [rest]; omega
  have div : (10:ℤ)^δ ∣ 3 * value w + h := by
    refine ⟨23 * (3 * value digits.reverse - h * 10^digits.length), ?_⟩
    dsimp [w]
    rw [eq]
    ring
  have hs := strip_suffix w good δ (by omega) h hh div
  have hw : w = List.replicate δ (3*h) ++ rest := by
    conv_lhs => rw [← List.take_append_drop δ w]
    rw [hs]
  have he := congrArg (List.drop center.length) hw
  have hd : digits = List.replicate (δ-center.length) (3*h) ++ rest := by
    simpa [w, List.drop_append_of_le_length (by simpa using hc : center.length ≤ (List.replicate δ (3*h)).length)] using he
  have lastRest : rest.getLast? ≠ some 0 := by
    rw [hd, List.getLast?_append] at last
    intro heq
    exact last (by simp [heq])
  have gr : ∀ d ∈ rest, d < 10 := by
    intro d hd'
    exact good d (List.mem_of_mem_drop hd')
  have raw : 3 * value (List.replicate δ (3*h) ++ rest) + h =
      23 * 10^δ * (3 * value (List.replicate (δ-center.length) (3*h) ++ rest).reverse -
        h * 10^((δ-center.length) + rest.length)) := by
    change 3 * value w + h = _ at eq
    rw [hw] at eq
    conv at eq => rhs; rw [hd]
    simpa using eq
  exact no_short_word h (by omega) rest hlen' lastRest gr (collapse h δ (δ-center.length) rest raw)

private lemma shorter_equation (t j m : ℕ) (ht : 0 < t) (hj : j ≤ 2*t)
    (u v : ℤ) (hu : 0 ≤ u ∧ u < 10^(j+1)) (hv : 0 ≤ v ∧ v < 10^j)
    (split : (family t : ℤ)*m = v + 10^j*u) :
    ∃ h : ℤ, (-1 ≤ h ∧ h ≤ 2) ∧ (u < family t → 0 ≤ h) ∧
      3*u+h = 23*10^(2*t-j)*(3*v-h*10^j) := by
  let δ := 2*t-j
  have hsum : δ+j = 2*t := by dsimp [δ]; omega
  have hpow : (10:ℤ)^δ * 10^j = 10^(2*t) := by rw [← pow_add, hsum]
  have hF := family_value ht
  have hf : (0 : ℤ) < 10^δ := by positivity
  have hP : (0 : ℤ) < family t := by
    have hp : (0:ℤ) < 10^(2*t) := by positivity
    omega
  have uBound : u < 10*10^(2*t) := by
    have he : (10:ℤ)^j ≤ 10^(2*t) := pow_le_pow_right₀ (by decide) hj
    rw [pow_succ] at hu
    linarith only [hu.2, he]
  have vBound := mul_lt_mul_of_pos_left hv.2 hf
  let h : ℤ := 23 * 10^δ * m - 3*u
  have heq : (family t : ℤ)*h = 23*10^δ*v-u := by
    dsimp [h]
    rw [← hpow] at hF
    linear_combination 23*10^δ*split - u*hF
  refine ⟨h, ⟨?_, ?_⟩, ?_, ?_⟩
  · by_contra! hn
    have h1 := mul_le_mul_of_nonneg_left (show h ≤ -2 by omega) hP.le
    have h2 : 0 ≤ 10^δ*v := mul_nonneg hf.le hv.1
    nlinarith only [h1, h2, heq, uBound, hF]
  · by_contra! hn
    have h1 := mul_le_mul_of_nonneg_left (show 3 ≤ h by omega) hP.le
    rw [hpow] at vBound
    nlinarith only [h1, heq, vBound, hF, hu.1]
  · intro huP
    by_contra! hn
    have h1 := mul_le_mul_of_nonneg_left (show h ≤ -1 by omega) hP.le
    have h2 : 0 ≤ 10^δ*v := mul_nonneg hf.le hv.1
    nlinarith only [h1, heq, h2, huP]
  · change 3*u+h = 23*10^δ*(3*v-h*10^j)
    rw [← hpow] at hF
    linear_combination 3*heq - h*hF

private lemma longest_equation (t m : ℕ) (ht : 0 < t) (u v : ℤ)
    (hu : 0 ≤ u ∧ u < 10^(2*t+1)) (hv : 0 ≤ v ∧ v < 10^(2*t+1))
    (split : (family t : ℤ)*m = v + 10^(2*t+1)*u) :
    ∃ h : ℤ, (-13 ≤ h ∧ h ≤ 30) ∧ -h+69*v-30*u = 23*h*10^(2*t) := by
  have hF := family_value ht
  have hp : (0:ℤ) < 10^(2*t) := by positivity
  have hP : (0 : ℤ) < family t := by omega
  let h : ℤ := 23*m-30*u
  rw [pow_succ] at hu hv split
  have heq : (family t : ℤ)*h = 23*v-10*u := by
    dsimp [h]
    linear_combination 23*split - 10*u*hF
  refine ⟨h, ⟨?_, ?_⟩, ?_⟩
  · by_contra! hn
    have hh := mul_le_mul_of_nonneg_left (show h ≤ -14 by omega) hP.le
    nlinarith only [hh, heq, hu.2, hv.1, hF, hp]
  · by_contra! hn
    have hh := mul_le_mul_of_nonneg_left (show 31 ≤ h by omega) hP.le
    nlinarith only [hh, heq, hv.2, hu.1, hF, hp]
  · linear_combination h*hF - 3*heq

private lemma value_digits (n : ℕ) : value (Nat.digits 10 n) = n := by
  simp [value, Nat.ofDigits_digits]

private lemma value_familyWord (t : ℕ) : value (familyWord t) = family t := rfl

private lemma upper_digits_for (a b : List ℕ) (pos : b ≠ [])
    (last : (a ++ b).getLast? ≠ some 0) : b.getLast? ≠ some 0 := by
  simpa [List.getLast?_append_of_ne_nil a pos] using last

private lemma no_between (t m : ℕ) (ht : 0 < t) (hm : 2 ≤ m)
    (hy : family t * m < twice (family t)) (hp : Pal (family t * m)) : False := by
  let k := 2*t+1
  let y := family t * m
  have hpk : (Nat.digits 10 (family t)).length = k := by rw [digits_family, familyWord_length ht]
  have hpow : (10:ℤ)^k = 10^(2*t)*10 := by dsimp [k]; rw [pow_succ]
  have hk : 3 ≤ k := by dsimp [k]; omega
  have hT : (1:ℤ) < 10^(2*t) := by
    have e : (10:ℤ)^0 < 10^(2*t) := pow_lt_pow_right₀ (by decide) (by omega)
    simpa using e
  have hF := family_value ht
  have hpLower : 5 * (10:ℤ)^(2*t) < family t := by linarith only [hF, hT]
  have hpUpper : (family t : ℤ) < 8 * 10^(2*t) := by linarith only [hF, hT]
  have hyUpper : y < family t*(10^k+1) := by simpa [twice, hpk, y] using hy
  have hyLower : 10^k ≤ y := by
    have hm' : (2:ℤ) ≤ m := by exact_mod_cast hm
    have hp0 : (0:ℤ) ≤ family t := Int.natCast_nonneg _
    have hh := mul_le_mul_of_nonneg_left hm' hp0
    have hyz : (10:ℤ)^k ≤ (y:ℤ) := by
      rw [hpow]
      dsimp [y]
      linarith only [hh, hpLower]
    exact_mod_cast hyz
  have hyLengthUpper : y < 10^(2*k) := by
    have plt : family t < 10^k := by
      exact (Nat.digits_length_le_iff (by decide : 1 < 10) _).mp hpk.le
    rw [two_mul, pow_add]
    have hyz : (y:ℤ) < (family t:ℤ)*((10:ℤ)^k+1) := by exact_mod_cast hyUpper
    have hpz : (family t:ℤ) < (10:ℤ)^k := by exact_mod_cast plt
    have hle := mul_le_mul_of_nonneg_right (show (family t:ℤ)+1 ≤ (10:ℤ)^k by omega)
      (show (0:ℤ) ≤ (10:ℤ)^k+1 by positivity)
    have hout : (y:ℤ) < (10:ℤ)^k*10^k := by nlinarith only [hyz, hle]
    exact_mod_cast hout
  let w := Nat.digits 10 y
  have hmin : k < w.length := (Nat.lt_digits_length_iff (by decide : 1 < 10) y).mpr hyLower
  have hmax : w.length ≤ 2*k := (Nat.digits_length_le_iff (by decide : 1 < 10) y).mpr hyLengthUpper
  rcases pal_words w hp with ⟨u, hd⟩ | ⟨u, c, hd⟩
  · let j := u.length
    have hw : w.length = 2*j := by simp [hd, j, two_mul]
    have hjPos : 0 < j := by omega
    have huNonempty : u ≠ [] := by
      intro h
      simp [j, h] at hjPos
    have good : ∀ d ∈ u, d < 10 := by
      intro d hm'
      apply digits_good y d
      change d ∈ w
      simp [hd, hm']
    have last : u.getLast? ≠ some 0 := upper_digits_for _ _ huNonempty (by rw [← hd]; exact digits_last_nonzero y)
    have hu := value_bounds u good
    have hv := value_bounds u.reverse (by simpa using good)
    rw [List.length_reverse] at hv
    have split : (family t : ℤ)*m = value u.reverse+10^j*value u := by
      calc
        (family t : ℤ)*m = value w := by rw [value_digits]; simp [y]
        _ = _ := by rw [hd, value_append, List.length_reverse]
    by_cases hj : j = k
    · have huB : value u ≤ family t := by
        have hyz : (y:ℤ) < (family t:ℤ)*((10:ℤ)^k+1) := by exact_mod_cast hyUpper
        have hpT : (family t:ℤ) < 10^k := by rw [hpow]; linarith only [hpUpper,hT]
        have hsplit : (y:ℤ)=value u.reverse+10^k*value u := by simpa [hj,y] using split
        by_contra! hcontra
        have h1 := mul_le_mul_of_nonneg_left (show (family t : ℤ)+1 ≤ value u by omega)
          (show (0:ℤ) ≤ 10^k by positivity)
        nlinarith only [h1, hyz, hpT, hsplit, hv.1]
      let d := u.getLast huNonempty
      have dlast : u.getLast? = some d := List.getLast?_eq_some_getLast huNonempty
      have dpos : 0 < d := by rw [dlast] at last; simpa [Nat.pos_iff_ne_zero] using last
      have dmax : d ≤ 7 := by
        have htail := List.dropLast_concat_getLast huNonempty
        have hlen := List.length_dropLast (xs := u)
        have he : value u = value u.dropLast + 10^(2*t)*(d:ℤ) := by
          calc
            value u = value (u.dropLast ++ [d]) := congrArg value htail.symm
            _ = _ := by
              rw [value_append, value_single, hlen]
              have e : u.length-1 = 2*t := by change j - 1 = 2*t; rw [hj]; simp [k]
              rw [e]
        have hd0 := (value_bounds u.dropLast (fun a hm' => good a (List.mem_of_mem_dropLast hm'))).1
        by_contra! hh
        have hm' := mul_le_mul_of_nonneg_left (show (8:ℤ) ≤ d by omega) (show (0:ℤ) ≤ 10^(2*t) by positivity)
        linarith only [hm', he, hd0, huB, hpUpper]
      have eh : u.length = 2*t+1 := hj
      obtain ⟨h, hr, heq⟩ := longest_equation t m ht (value u) (value u.reverse)
        (by simpa [eh] using hu) (by simpa [eh] using hv) (by simpa [hj,k] using split)
      have eq : u = familyWord t := by
        rw [familyWord, ← show u.length-2 = 2*t-1 by omega]
        apply full_word h hr u (by omega) (by omega) ⟨d,dpos,dmax,dlast⟩ good
        rwa [show u.length-1 = 2*t by omega]
      rw [eq, familyWord_reverse, value_familyWord, hj] at split
      have hyz : (y:ℤ) < (family t:ℤ)*((10:ℤ)^k+1) := by exact_mod_cast hyUpper
      dsimp [y] at hyz
      nlinarith only [split, hyz]
    · have hjle : j ≤ 2*t := by omega
      have hu1 : value u < 10^(j+1) := by
        have huv : value u < (10:ℤ)^j := hu.2
        rw [pow_succ]
        have hpos : (0:ℤ) < 10^j := by positivity
        linarith only [huv, hpos]
      obtain ⟨h, hr, hp0, heq⟩ := shorter_equation t j m ht hjle _ _ ⟨hu.1,hu1⟩ hv split
      have huP : value u < family t := by
        have hq : (10:ℤ)^j ≤ 10^(2*t) := pow_le_pow_right₀ (by decide) hjle
        have huv : value u < (10:ℤ)^j := hu.2
        linarith only [hq, huv, hpLower, hT]
      have hz := hp0 huP
      have hh : ((h.toNat:ℕ):ℤ)=h := by omega
      have heq' : 3 * value u + (h.toNat:ℤ) =
          23*10^(2*t-j)*(3*value u.reverse-(h.toNat:ℤ)*10^j) := by simpa [hh] using heq
      exact exclude_short [] u (2*t-j) h.toNat (by simp) (by simp; change 2*t-j+2 ≤ j; omega)
        (by omega) good last heq'
  · let j := u.length
    have hw : w.length = 2*j+1 := by simp [hd, j, two_mul]; omega
    have hjPos : 0 < j := by omega
    have huNonempty : u ≠ [] := by
      intro h
      simp [j, h] at hjPos
    have good : ∀ d ∈ c :: u, d < 10 := by
      intro d hm'
      apply digits_good y d
      change d ∈ w
      simp [hd, List.mem_cons] at hm' ⊢
      tauto
    have last : u.getLast? ≠ some 0 := by
      have he : w.getLast? = u.getLast? := by
        rw [hd, List.getLast?_append_of_ne_nil (l₂ := c :: u) _ (by simp),
          List.getLast?_cons_of_ne_nil huNonempty]
      rw [← he]
      exact digits_last_nonzero y
    have hu := value_bounds (c::u) good
    have hv := value_bounds u.reverse (by
      intro d hm'
      exact good d (List.mem_cons_of_mem _ (List.mem_reverse.mp hm')))
    rw [List.length_reverse] at hv
    have split : (family t : ℤ)*m = value u.reverse+10^j*value (c::u) := by
      calc
        (family t : ℤ)*m = value w := by rw [value_digits]; simp [y]
        _ = _ := by rw [hd, value_append, List.length_reverse]
    have hjle : j ≤ 2*t := by omega
    obtain ⟨h, hr, hp0, heq⟩ := shorter_equation t j m ht hjle _ _ hu hv split
    by_cases hj : j=2*t
    · have hdg : ∀ d ∈ u, d < 10 := fun d hd => good d (List.mem_cons_of_mem _ hd)
      apply no_odd_word h hr c (good c (by simp)) u (by change 2≤j; omega)
        (by change j % 2 = 0; omega) last hdg
      rw [hj, Nat.sub_self, pow_zero, mul_one, value_cons] at heq
      unfold Carry
      change -h - 3*(c:ℤ) + 69*value u.reverse - 30*value u = 23*h*10^j
      rw [hj]
      linear_combination -heq
    · have huP : value (c::u) < family t := by
        have hq : (10:ℤ)^(j+1) ≤ 10^(2*t) := pow_le_pow_right₀ (by decide) (by omega)
        have htight : value (c::u) < (10:ℤ)^(j+1) := hu.2
        linarith only [hq, htight, hpLower, hT]
      have hz := hp0 huP
      have hh : (h.toNat:ℤ)=h := by omega
      have heq' : 3*value (c::u)+(h.toNat:ℤ) =
          23*10^(2*t-j)*(3*value u.reverse-(h.toNat:ℤ)*10^j) := by simpa [hh] using heq
      exact exclude_short [c] u (2*t-j) h.toNat (by simp; omega)
        (by simp only [List.length_append, List.length_singleton]; change 2*t-j+2 ≤ 1+j; omega) (by omega) good last heq'

private lemma family_pos {t : ℕ} (ht : 0 < t) : 0 < family t := by
  have hp := family_value ht
  have hT : (0:ℤ) < 10^(2*t) := by positivity
  omega

private lemma twice_digits_family (t : ℕ) :
    Nat.digits 10 (twice (family t)) = familyWord t ++ familyWord t := by
  have hword : Nat.ofDigits 10 (familyWord t ++ familyWord t) = twice (family t) := by
    rw [Nat.ofDigits_append, twice, digits_family]
    change family t + (10:ℕ)^(familyWord t).length*family t = _
    ring
  rw [← hword]
  apply Nat.digits_ofDigits _ (by decide)
  · intro d hd
    simp only [List.mem_append, or_self] at hd
    exact familyWord_digits t d hd
  · intro h
    have hl : (familyWord t ++ familyWord t).getLast? = some 7 := by
      have hr : (familyWord t).getLast? = some 7 := by simp [familyWord,List.getLast?_cons]
      simp [List.getLast?_append,hr]
    exact (by decide : (7:ℕ) ≠ 0) ∘ (List.getLast_of_getLast?_eq_some hl).symm.trans

private lemma family_least (t : ℕ) (ht : 0 < t) :
    IsLeast {y : ℕ | family t < y ∧ family t ∣ y ∧ Pal y} (twice (family t)) := by
  have hpos := family_pos ht
  constructor
  · refine ⟨?_, ?_, ?_⟩
    · unfold twice
      have hp : 0 < (10:ℕ)^(Nat.digits 10 (family t)).length := by positivity
      nlinarith only [Nat.mul_pos hpos hp]
    · exact dvd_mul_right _ _
    · unfold Pal
      rw [twice_digits_family, List.reverse_append, familyWord_reverse]
  · intro y hy
    obtain ⟨hy1, ⟨m, rfl⟩, hpal⟩ := hy
    by_contra! hlt
    have hm : 2 ≤ m := by
      by_contra! hm'
      interval_cases m <;> simp at hy1
    exact no_between t m ht hm hlt hpal

end A083146

open OMA.S_oeis_a083146 in
theorem OMA.solution : type_of% @OMA.S_oeis_a083146.main := by
  let g := fun n : ℕ => A083146.family (n+1)
  have hinj : Function.Injective g := by
    intro a b h
    have he := congrArg (fun p => (Nat.digits 10 p).length) h
    change (Nat.digits 10 (A083146.family (a+1))).length =
      (Nat.digits 10 (A083146.family (b+1))).length at he
    rw [A083146.digits_family, A083146.digits_family,
      A083146.familyWord_length (by omega), A083146.familyWord_length (by omega)] at he
    omega
  apply (Set.infinite_range_of_injective hinj).mono
  rintro _ ⟨n,rfl⟩
  change 0 < A083146.family (n+1) ∧ Pal (A083146.family (n+1)) ∧ _
  refine ⟨A083146.family_pos (by omega), ?_, A083146.family_least (n+1) (by omega)⟩
  unfold Pal
  rw [A083146.digits_family,A083146.familyWord_reverse]
