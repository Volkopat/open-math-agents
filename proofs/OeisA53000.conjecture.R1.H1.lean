import OMAReductions.R_OeisA53000_conjecture_R1
import Mathlib

-- Credit: @jacklarmer.
-- An offset supplies a prime strictly above each square. The proof needs only an
-- upper bound on the first prime, so it suffices to certify that one witness.
namespace SquarePrimeGap



/-- Least common multiple of the positive integers through 10001. -/
def trialMultiple : ℕ := 57933396702876429686922708791662400986348602979985188253931383511489793001457731823088325981761829221665744176794023407056559491402467891577328326763021299466843118474637852656831938521549472347971073068161679301705472685236926463387338495220571064420250677315000599457941340849496227227628926493771018264821842230370349640102573492881424317306189569467101495834601991270039918780924506495405797923762205360790652073159333382795670426041033566699342449050309786673681670483369155689567554239898879039744147333971988258061042090970476729293484513072443614795766878726325795854855394491290821167148355514749149683707585283381546153703014210442470318180511906691108325146494219343498899382918018246586609827667470329166012110874981104800415741527586280026737848182673635645872230905234515169611121042867043956727839314198728626274066655467846183343599194761590368608472578398169740111485924046986870714883894285841394964627408094161019230662749101230783008668676907211199488107523306410531772045452853957706873238466829988649822157557103503283563398281775464911904789159515900987401574678885942493907604740891878907698622679570965569483682456042918236444719794534411171907606336090534029349351300276141892529795448751826394399153216183270385737795748770508612096374765333578237973395907265484337502903901947799663388329849198045756207969590055686607678195206367273600632909417024224754750428711236917913663419215925830944035539848749163178489614227546656090790164108195741048033614368495827231281392190063051315248070192263400801315095608512139510731469732311313898995746040563433121427776071482655904346538281010668476731132415829844984600414136781404774213539507859790229205890271721600309169926806121871750008163738773911610009508609149665332579632767397078877996926581337419351834754370411008686136818501030862345505385357198060894463821342298717851567836562984344806469613768024764967372979655179066074398198246805104576134474823016488842818077041661676098399378809713894284994865370648616800689225595431967181072865363430005250840767890912164530705704936837915584856606960687347372391339254432119085932175541392954343684716695162629271229789289404752104218596977036941910521266321726821940533986384237994403780618301379099347975260122724194454275088825587044488208965690373706904056926509324696308810974331790119456438147168585552011926921912167450509941646104076818762060881903969616431646384985895944231218505620547093874241169759205450145478746112796898626711966320965057212219958567338851356631739947125096250452942497473309299907612330435197454392788637359253116308685007014249605492659524429134513344137517101872279428202285951652856354827230765931502805341696470148698002737700823078904634554776750169178259216255903968865588749827789888950172452455448248833712309835657561369233157977405579365293671943131412034109901944892819245001657496671822581274180596255340507054499934060282320458240722454209933569735940032859109934686878274110864394924463573852015338428881961843292083566034669814619612606638283615766521897504566616272305253931938372830446073384019299355320864342734019517633662346790422915951954822645137091494126100390104510987373366328615363056042137440808225973600809566845718073791616927784260557845021823094999326904373592319407516660896764388092262510369182153559285446074990941863516247226532653142198551840063631989428776799533286215464660644129411503287306838551341184739976807097763115368031748646043780549055143428297230678053738453010234949008253769355207208167999203353157524666017029803679612131824740794652592875662818479980117505768541194835524231818203552256426752730455115752280837099763237606348192867936457993970866446264015812819179994138642295108872381709181937092290392544335464025324661284746003660247161196698209062164637264114930766444473471083408200329662059064201896721165015687487728300854501780810155844837489798144309942999091774466406270065305461848242329380636274754660519867343112275861821293501112101434868225378041813836808745417606289159904294165941408692922250601127804971962342807927743390030395048263275616935165347620718001157478088456439083590834464409622781693790883289597024043982584220069224170235863458745344365684082114430362867446193601075569803650773018026700003812298460527976219100308016537538008597751565631582745643139434508332515569645426771932483266712323523039014220800000

/-- Certify divisibility in intervals of length 1000. The fixed multiple is shared
by every primality check, including those in different offset blocks. -/
def trialRange (base : ℕ) : ℕ → Bool
  | 0 => true
  | k+1 => (trialMultiple % (base+k+1) == 0) && trialRange base k

lemma trialRange_sound (base : ℕ) {k d : ℕ} (ck : trialRange base k = true)
    (lo : base < d) (hi : d ≤ base+k) : d ∣ trialMultiple := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [trialRange, Bool.and_eq_true, beq_iff_eq] at ck
    by_cases h : d = base+k+1
    · rw [h]
      exact Nat.dvd_of_mod_eq_zero ck.1
    · exact ih ck.2 (by omega)

set_option maxRecDepth 20000 in
lemma divisorBlock0 : trialRange 0 1000 = true := by decide +kernel

set_option maxRecDepth 20000 in
lemma divisorBlock1 : trialRange 1000 1000 = true := by decide +kernel

set_option maxRecDepth 20000 in
lemma divisorBlock2 : trialRange 2000 1000 = true := by decide +kernel

set_option maxRecDepth 20000 in
lemma divisorBlock3 : trialRange 3000 1000 = true := by decide +kernel

set_option maxRecDepth 20000 in
lemma divisorBlock4 : trialRange 4000 1000 = true := by decide +kernel

set_option maxRecDepth 20000 in
lemma divisorBlock5 : trialRange 5000 1000 = true := by decide +kernel

set_option maxRecDepth 20000 in
lemma divisorBlock6 : trialRange 6000 1000 = true := by decide +kernel

set_option maxRecDepth 20000 in
lemma divisorBlock7 : trialRange 7000 1000 = true := by decide +kernel

set_option maxRecDepth 20000 in
lemma divisorBlock8 : trialRange 8000 1000 = true := by decide +kernel

set_option maxRecDepth 20000 in
lemma divisorBlock9 : trialRange 9000 1000 = true := by decide +kernel

lemma small_divides (d : ℕ) (positive : 0 < d) (bound : d ≤ 10001) : d ∣ trialMultiple := by
  by_cases last : d = 10001
  · subst d
    exact Nat.dvd_of_mod_eq_zero (by decide +kernel : trialMultiple % 10001 = 0)
  let b : Fin 10 := ⟨(d-1)/1000, by omega⟩
  have covers (j : Fin 10) : trialRange (1000*j.val) 1000 = true := by
    fin_cases j
    · exact divisorBlock0
    · exact divisorBlock1
    · exact divisorBlock2
    · exact divisorBlock3
    · exact divisorBlock4
    · exact divisorBlock5
    · exact divisorBlock6
    · exact divisorBlock7
    · exact divisorBlock8
    · exact divisorBlock9
  apply trialRange_sound (1000*b.val) (covers b) <;> dsimp [b] <;> omega

/-- A smaller multiple suffices when the candidate prime is below 10002. -/
def smallMultiple : ℕ := 69720375229712477164533808935312303556800

def smallRange (base : ℕ) : ℕ → Bool
  | 0 => true
  | k+1 => (smallMultiple % (base+k+1) == 0) && smallRange base k

lemma smallRange_sound (base : ℕ) {k d : ℕ} (ck : smallRange base k = true)
    (lo : base < d) (hi : d ≤ base+k) : d ∣ smallMultiple := by
  induction k with
  | zero => omega
  | succ k ih =>
    simp only [smallRange, Bool.and_eq_true, beq_iff_eq] at ck
    by_cases h : d = base+k+1
    · rw [h]
      exact Nat.dvd_of_mod_eq_zero ck.1
    · exact ih ck.2 (by omega)

lemma smallRange_checked : smallRange 0 100 = true := by decide +kernel

def primeCheck (p : ℕ) : Bool :=
  if p ≤ 100 then decide p.Prime
  else if p ≤ 10001 then decide (p.gcd smallMultiple = 1)
  else decide (p.gcd trialMultiple = 1)

lemma prime_of_certified (p m bound : ℕ) (two : 2 ≤ p) (sq : p < (bound+1)^2)
    (covers : ∀ d, 0 < d → d ≤ bound → d ∣ m) (hg : p.gcd m = 1) : p.Prime := by
  by_contra notPrime
  have hf := Nat.minFac_sq_le_self (by omega : 0 < p) notPrime
  have small : p.minFac ≤ bound := by
    by_contra! large
    have le := Nat.pow_le_pow_left (show bound+1 ≤ p.minFac by omega) 2
    omega
  have divides := Nat.dvd_gcd (Nat.minFac_dvd p) (covers _ (Nat.minFac_pos p) small)
  rw [hg] at divides
  have one := Nat.dvd_one.mp divides
  have twoFac := (Nat.minFac_prime (by omega : p ≠ 1)).two_le
  omega

lemma primeCheck_sound (p : ℕ) (bound : p ≤ 100020001)
    (test : primeCheck p = true) : p.Prime := by
  by_cases tiny : p ≤ 100
  · simpa [primeCheck, tiny] using test
  by_cases small : p ≤ 10001
  · apply prime_of_certified p smallMultiple 100 (by omega) (by omega)
    · intro d pos hi
      exact smallRange_sound 0 smallRange_checked pos hi
    · simpa [primeCheck, tiny, small] using test
  · apply prime_of_certified p trialMultiple 10001 (by omega) (by omega)
    · exact small_divides
    · simpa [primeCheck, tiny, small] using test

open Finset

/-- Distinct integers at least two are no smaller than 2, 3, ..., card+1.
The corresponding factors p/(p-1) telescope to at most card+1. -/
lemma products_from_two (s : Finset ℕ) (hs : ∀ p ∈ s, 2 ≤ p) :
    (s.card+1).factorial ≤ ∏ p ∈ s, p ∧
      (∏ p ∈ s, p) ≤ (s.card+1) * ∏ p ∈ s, (p-1) := by
  induction s using Finset.induction_on_max with
  | empty => simp
  | insert a s above ih =>
    have ha := hs a (mem_insert_self _ _)
    have hsub : s ⊆ Ico 2 a := fun p hp ↦ mem_Ico.mpr ⟨hs p (mem_insert_of_mem hp), above p hp⟩
    have hcard := Finset.card_le_card hsub
    rw [Nat.card_Ico] at hcard
    have hfit : s.card+2 ≤ a := by omega
    have fresh : a ∉ s := fun h ↦ (lt_irrefl a) (above a h)
    obtain ⟨hf,hr⟩ := ih (fun p hp ↦ hs p (mem_insert_of_mem hp))
    rw [card_insert_of_notMem fresh, prod_insert fresh, prod_insert fresh]
    constructor
    · rw [Nat.factorial_succ]
      exact Nat.mul_le_mul hfit hf
    · have hstep : a*(s.card+1) ≤ (s.card+1+1)*(a-1) := by
        calc
          a*(s.card+1) = ((a-1)+1)*(s.card+1) := by rw [Nat.sub_add_cancel (by omega : 1 ≤ a)]
          _ ≤ _ := by nlinarith [show s.card+1 ≤ a-1 by omega]
      calc
        a * (∏ p ∈ s, p) ≤ a * ((s.card+1) * ∏ p ∈ s, (p-1)) := Nat.mul_le_mul_left _ hr
        _ = (a*(s.card+1)) * ∏ p ∈ s, (p-1) := by ring
        _ ≤ ((s.card+1+1)*(a-1)) * ∏ p ∈ s, (p-1) := Nat.mul_le_mul_right _ hstep
        _ = _ := by ring

lemma le_seven_totient (n : ℕ) (hn : n ≤ 10000) : n ≤ 7*n.totient := by
  by_cases h0 : n = 0
  · simp [h0]
  have hp (p : ℕ) (h : p ∈ n.primeFactors) : 2 ≤ p := (Nat.prime_of_mem_primeFactors h).two_le
  obtain ⟨hf, hr⟩ := products_from_two n.primeFactors hp
  have hbound := hf.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) (Nat.prod_primeFactors_dvd n))
  have hcard : n.primeFactors.card+1 ≤ 7 := by
    by_contra! h
    have hlarge : 40320 ≤ (n.primeFactors.card+1).factorial :=
      Nat.factorial_le (show 8 ≤ n.primeFactors.card+1 by omega)
    omega
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p-1) := prod_pos (fun p h ↦ by have := hp p h; omega)
  apply Nat.le_of_mul_le_mul_right _ hpos
  calc
    n * (∏ p ∈ n.primeFactors, (p-1)) = n.totient * ∏ p ∈ n.primeFactors, p :=
      (Nat.totient_mul_prod_primeFactors n).symm
    _ ≤ n.totient * ((n.primeFactors.card+1) * ∏ p ∈ n.primeFactors, (p-1)) :=
      Nat.mul_le_mul_left _ hr
    _ ≤ (7*n.totient) * ∏ p ∈ n.primeFactors, (p-1) := by
      rw [← Nat.mul_assoc, Nat.mul_comm n.totient]
      exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hcard)

lemma totient_bound_linear (n d : ℕ) (hn : n ≤ 10000) (h : 7*(d-1) ≤ n) : d ≤ 1+n.totient := by
  have := le_seven_totient n hn
  omega

def coprimeCount (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => coprimeCount n k + if n.gcd k = 1 then 1 else 0

theorem coprimeCount_eq (n k : ℕ) :
    coprimeCount n k = Nat.count (n.Coprime ·) k := by
  induction k with
  | zero => simp [coprimeCount]
  | succ k ih => rw [coprimeCount, ih, Nat.count_succ]

def prefixCheck (n d : ℕ) : Bool := decide (d ≤ 1 + coprimeCount n (min n (5 * d)))

theorem prefixCheck_sound (n d : ℕ)
    (hc : prefixCheck n d = true) : d ≤ 1 + n.totient := by
  have h : d ≤ 1 + coprimeCount n (min n (5 * d)) := of_decide_eq_true hc
  apply h.trans
  apply Nat.add_le_add_left
  rw [coprimeCount_eq, Nat.totient_eq_card_coprime, ← Nat.count_eq_card_filter_range]
  exact Nat.count_monotone _ (min_le_left _ _)

/-- The linear bound handles every input except 38 small squares. -/
def totientCheck (n d : ℕ) : Bool :=
  if 7 * (d-1) ≤ n then true else prefixCheck n d

lemma totientCheck_sound (n d : ℕ) (hn : n ≤ 10000) (hc : totientCheck n d = true) :
    d ≤ 1 + n.totient := by
  by_cases h : 7 * (d-1) ≤ n
  · exact totient_bound_linear n d hn h
  · apply prefixCheck_sound
    simpa only [totientCheck, if_neg h] using hc

def check (n d : ℕ) : Bool :=
  let p := n^2 + d
  ((decide (0 < d) && decide (p ≤ 100020001)) && primeCheck p) && totientCheck n d

/-- Check one proposed offset for each successive input, beginning at `start`. -/
def checkList (start : ℕ) : List ℕ → Bool
  | [] => true
  | d :: ds => check start d && checkList (start+1) ds

lemma checkList_sound {ds : List ℕ} {start n : ℕ} (h : checkList start ds = true)
    (lo : start ≤ n) (hi : n < start + ds.length) : ∃ d, check n d = true := by
  induction ds generalizing start with
  | nil => simp at hi; omega
  | cons d ds ih =>
    simp only [checkList, Bool.and_eq_true] at h
    simp only [List.length_cons] at hi
    by_cases eq : start = n
    · exact ⟨d, eq ▸ h.1⟩
    · exact ih h.2 (by omega) (by omega)

def blockBound (b : ℕ) : Prop :=
  ∀ n, 100*b < n → n ≤ 100*b + 100 → ∃ d, check n d = true

lemma certifyBlock (b : ℕ) {ds : List ℕ} (length_ok : ds.length = 100)
    (h : checkList (100*b+1) ds = true) : blockBound b := by
  intro n lo hi
  apply checkList_sound h (by omega)
  rw [length_ok]
  omega

set_option maxRecDepth 20000 in
theorem block_00 : blockBound 0 := by
  apply certifyBlock 0 (ds := [
    1, 1, 2, 1, 4, 1, 4, 3, 2, 1, 6, 5, 4, 1, 2, 1, 4, 7, 6, 1, 2, 3, 12, 1, 6,
    1, 4, 3, 12, 7, 6, 7, 2, 7, 4, 1, 4, 3, 2, 1, 12, 13, 12, 13, 2, 13, 4, 5, 10, 3,
    8, 3, 10, 1, 12, 1, 2, 7, 10, 7, 6, 3, 20, 3, 4, 1, 4, 13, 22, 3, 10, 5, 4, 1, 14,
    3, 10, 5, 6, 21, 2, 9, 10, 1, 4, 15, 4, 9, 6, 1, 6, 3, 14, 1, 4, 5, 4, 9, 2, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_01 : blockBound 1 := by
  apply certifyBlock 1 (ds := [
    10, 23, 4, 15, 2, 3, 18, 13, 6, 1, 2, 3, 12, 5, 4, 1, 2, 7, 12, 1, 12, 3, 2, 1, 4,
    1, 10, 27, 8, 1, 6, 7, 18, 1, 4, 7, 4, 7, 12, 3, 8, 9, 28, 7, 6, 1, 2, 7, 28, 1,
    6, 13, 8, 3, 4, 1, 10, 3, 20, 1, 10, 5, 4, 7, 14, 25, 4, 5, 10, 1, 2, 3, 18, 17, 6,
    1, 4, 3, 10, 1, 10, 25, 4, 1, 6, 7, 12, 9, 8, 7, 12, 7, 4, 7, 14, 15, 12, 5, 6, 9])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_02 : blockBound 2 := by
  apply certifyBlock 2 (ds := [
    22, 9, 4, 1, 18, 1, 4, 7, 10, 1, 10, 9, 8, 21, 4, 7, 4, 3, 2, 7, 6, 13, 10, 1, 2,
    33, 10, 7, 12, 1, 16, 7, 4, 11, 4, 1, 2, 15, 10, 1, 18, 3, 2, 3, 4, 5, 18, 3, 2, 1,
    28, 17, 4, 37, 2, 1, 18, 5, 22, 1, 20, 15, 22, 1, 4, 13, 4, 13, 6, 1, 12, 15, 2, 3, 4,
    31, 4, 7, 8, 1, 16, 7, 18, 1, 8, 3, 4, 19, 16, 21, 10, 33, 4, 5, 12, 7, 2, 3, 12, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_03 : blockBound 3 := by
  apply certifyBlock 3 (ds := [
    16, 25, 2, 3, 22, 1, 4, 9, 2, 37, 10, 23, 4, 1, 8, 3, 4, 17, 10, 7, 2, 3, 18, 11, 24,
    1, 8, 15, 6, 7, 6, 9, 10, 21, 12, 5, 22, 15, 20, 1, 12, 5, 10, 7, 2, 7, 4, 19, 42, 1,
    2, 7, 24, 13, 6, 3, 4, 9, 22, 7, 16, 15, 2, 3, 16, 7, 10, 3, 2, 43, 12, 5, 4, 7, 2,
    21, 22, 13, 10, 7, 16, 7, 12, 1, 4, 1, 2, 7, 16, 11, 16, 25, 10, 15, 16, 1, 18, 3, 8, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_04 : blockBound 4 := by
  apply certifyBlock 4 (ds := [
    6, 7, 4, 7, 14, 1, 4, 7, 28, 9, 16, 7, 10, 5, 18, 3, 2, 13, 12, 1, 16, 7, 2, 3, 4,
    23, 4, 7, 2, 1, 6, 5, 18, 3, 4, 1, 10, 17, 16, 1, 2, 25, 22, 1, 6, 13, 2, 9, 10, 19,
    16, 7, 2, 7, 4, 5, 28, 3, 28, 19, 36, 5, 4, 1, 8, 1, 18, 7, 10, 1, 8, 3, 18, 1, 4,
    25, 2, 25, 18, 31, 6, 9, 4, 3, 6, 11, 4, 7, 16, 1, 12, 5, 24, 7, 4, 1, 22, 17, 16, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_05 : blockBound 5 := by
  apply certifyBlock 5 (ds := [
    2, 9, 4, 5, 18, 13, 4, 3, 18, 11, 6, 3, 2, 15, 6, 5, 10, 19, 16, 7, 10, 23, 22, 3, 16,
    31, 12, 17, 6, 9, 10, 3, 4, 5, 18, 1, 14, 9, 6, 19, 12, 3, 10, 1, 24, 37, 4, 13, 2, 7,
    12, 5, 12, 3, 2, 1, 24, 7, 28, 3, 2, 7, 22, 7, 12, 21, 20, 3, 6, 1, 16, 9, 2, 13, 16,
    1, 4, 9, 8, 3, 22, 7, 18, 1, 8, 15, 18, 5, 12, 49, 10, 39, 4, 1, 6, 45, 32, 7, 10, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_06 : blockBound 6 := by
  apply certifyBlock 6 (ds := [
    10, 3, 2, 13, 4, 7, 4, 9, 2, 7, 6, 13, 4, 15, 4, 3, 18, 13, 10, 3, 16, 3, 4, 5, 22,
    3, 8, 9, 16, 19, 10, 9, 14, 1, 16, 1, 12, 3, 16, 9, 18, 7, 12, 1, 46, 1, 22, 17, 6, 37,
    2, 3, 12, 1, 18, 7, 8, 15, 12, 19, 36, 9, 4, 7, 4, 5, 4, 3, 8, 7, 16, 17, 24, 1, 2,
    3, 4, 7, 10, 1, 2, 9, 28, 11, 4, 1, 28, 7, 16, 1, 16, 7, 38, 3, 6, 1, 10, 7, 2, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_07 : blockBound 7 := by
  apply certifyBlock 7 (ds := [
    16, 35, 4, 1, 16, 3, 4, 7, 6, 3, 2, 19, 4, 1, 12, 1, 4, 15, 12, 11, 22, 15, 8, 13, 16,
    5, 30, 3, 16, 7, 6, 25, 18, 7, 8, 3, 18, 7, 16, 1, 8, 13, 4, 7, 4, 3, 8, 7, 18, 1,
    12, 3, 2, 7, 4, 5, 52, 33, 8, 1, 12, 19, 4, 1, 26, 13, 4, 5, 16, 3, 8, 25, 10, 11, 6,
    3, 2, 25, 6, 1, 18, 7, 8, 1, 4, 5, 4, 3, 8, 19, 16, 5, 12, 15, 4, 7, 40, 5, 22, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_08 : blockBound 8 := by
  apply certifyBlock 8 (ds := [
    22, 9, 28, 5, 4, 3, 2, 7, 10, 13, 22, 9, 4, 21, 18, 1, 12, 3, 2, 39, 16, 29, 4, 13, 8,
    1, 4, 7, 36, 7, 22, 15, 54, 5, 34, 3, 2, 13, 22, 13, 12, 15, 14, 3, 4, 11, 4, 15, 28, 9,
    10, 5, 4, 13, 8, 13, 22, 17, 6, 1, 16, 3, 22, 1, 24, 15, 2, 3, 10, 19, 30, 27, 58, 3, 24,
    5, 18, 13, 8, 27, 12, 53, 4, 25, 2, 7, 34, 5, 6, 1, 8, 3, 24, 23, 12, 13, 2, 43, 10, 13])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_09 : blockBound 9 := by
  apply certifyBlock 9 (ds := [
    18, 9, 2, 21, 4, 1, 18, 13, 2, 1, 28, 7, 24, 3, 32, 15, 18, 5, 40, 1, 10, 9, 24, 17, 16,
    37, 32, 7, 6, 1, 16, 15, 2, 13, 4, 1, 28, 15, 8, 13, 6, 13, 12, 15, 4, 1, 28, 13, 6, 1,
    40, 9, 4, 5, 6, 7, 2, 3, 10, 1, 18, 3, 4, 7, 12, 1, 4, 7, 2, 3, 6, 19, 4, 31, 8,
    7, 10, 19, 18, 19, 2, 9, 4, 7, 6, 1, 8, 3, 28, 7, 6, 19, 4, 15, 12, 5, 4, 7, 8, 3])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_10 : blockBound 10 := by
  apply certifyBlock 10 (ds := [
    16, 23, 12, 1, 8, 7, 12, 5, 10, 1, 2, 7, 28, 5, 16, 3, 20, 3, 22, 7, 10, 25, 28, 7, 6,
    17, 4, 9, 20, 37, 16, 13, 48, 15, 2, 1, 22, 5, 6, 31, 8, 3, 12, 5, 16, 7, 10, 7, 18, 23,
    12, 37, 8, 1, 4, 53, 4, 25, 28, 1, 18, 5, 22, 27, 14, 1, 30, 13, 12, 1, 2, 7, 4, 7, 4,
    15, 38, 9, 12, 1, 58, 3, 4, 15, 12, 7, 4, 9, 8, 49, 10, 5, 10, 1, 14, 1, 12, 5, 40, 3])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_11 : blockBound 11 := by
  apply certifyBlock 11 (ds := [
    20, 3, 10, 5, 4, 1, 10, 19, 16, 71, 12, 9, 2, 3, 46, 23, 4, 15, 16, 27, 18, 5, 4, 1, 14,
    7, 12, 25, 30, 3, 2, 7, 12, 13, 22, 7, 14, 7, 12, 1, 6, 3, 2, 1, 4, 1, 12, 13, 10, 1,
    18, 7, 28, 3, 32, 1, 4, 17, 18, 21, 16, 3, 28, 5, 108, 7, 14, 15, 16, 7, 18, 7, 8, 1, 4,
    1, 4, 7, 2, 7, 16, 7, 4, 1, 4, 13, 18, 25, 28, 9, 10, 15, 10, 13, 4, 3, 4, 15, 6, 11])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_12 : blockBound 12 := by
  apply certifyBlock 12 (ds := [
    10, 7, 4, 3, 22, 5, 18, 13, 2, 1, 12, 5, 28, 7, 2, 7, 10, 5, 42, 13, 2, 7, 22, 37, 18,
    15, 34, 9, 28, 23, 16, 13, 2, 13, 4, 7, 4, 3, 2, 7, 6, 7, 10, 1, 2, 1, 4, 5, 6, 13,
    8, 9, 34, 5, 4, 3, 4, 9, 12, 11, 10, 9, 4, 3, 16, 5, 10, 7, 8, 3, 6, 5, 10, 1, 4,
    1, 34, 35, 22, 31, 10, 15, 12, 41, 4, 57, 14, 13, 28, 1, 30, 15, 58, 1, 6, 11, 28, 25, 20, 9])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_13 : blockBound 13 := by
  apply certifyBlock 13 (ds := [
    28, 5, 18, 7, 16, 1, 34, 5, 12, 3, 2, 3, 4, 1, 4, 1, 8, 37, 6, 1, 16, 15, 22, 1, 4,
    7, 18, 19, 2, 3, 46, 23, 24, 15, 14, 7, 4, 19, 6, 1, 8, 9, 18, 5, 4, 7, 4, 27, 18, 1,
    6, 25, 4, 1, 6, 5, 24, 15, 22, 9, 6, 49, 4, 7, 4, 1, 4, 13, 16, 49, 2, 19, 22, 1, 6,
    1, 4, 3, 10, 7, 28, 3, 4, 13, 12, 17, 12, 25, 8, 7, 6, 35, 4, 1, 4, 31, 18, 7, 42, 9])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_14 : blockBound 14 := by
  apply certifyBlock 14 (ds := [
    8, 15, 18, 25, 4, 1, 34, 3, 6, 1, 6, 13, 4, 27, 4, 1, 10, 3, 28, 1, 16, 17, 4, 7, 2,
    21, 10, 13, 18, 1, 20, 15, 18, 1, 6, 33, 2, 7, 16, 1, 58, 37, 4, 7, 36, 7, 4, 9, 10, 19,
    6, 13, 22, 25, 14, 1, 4, 7, 16, 1, 8, 7, 18, 17, 6, 15, 4, 33, 28, 13, 10, 13, 20, 3, 4,
    5, 10, 7, 16, 3, 10, 7, 10, 13, 8, 7, 10, 17, 22, 51, 20, 25, 34, 1, 6, 7, 2, 87, 18, 13])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_15 : blockBound 15 := by
  apply certifyBlock 15 (ds := [
    22, 9, 20, 1, 24, 7, 4, 25, 2, 7, 16, 5, 10, 25, 8, 37, 4, 19, 6, 21, 20, 3, 4, 1, 4,
    15, 4, 9, 10, 11, 6, 7, 4, 3, 34, 7, 42, 13, 2, 9, 18, 5, 4, 7, 14, 1, 24, 5, 6, 1,
    20, 19, 12, 5, 12, 1, 10, 7, 6, 31, 18, 37, 2, 1, 6, 1, 10, 9, 8, 1, 6, 17, 54, 45, 38,
    1, 22, 7, 18, 1, 16, 9, 12, 5, 4, 1, 8, 3, 6, 29, 12, 7, 4, 13, 4, 31, 28, 7, 2, 21])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_16 : blockBound 16 := by
  apply certifyBlock 16 (ds := [
    6, 7, 40, 43, 8, 13, 42, 43, 12, 3, 2, 9, 4, 1, 12, 1, 2, 33, 6, 11, 16, 7, 2, 3, 18,
    13, 4, 3, 40, 9, 12, 5, 4, 3, 2, 27, 4, 5, 16, 1, 10, 3, 4, 1, 4, 3, 4, 9, 6, 7,
    16, 3, 28, 1, 6, 7, 12, 7, 26, 1, 16, 7, 10, 1, 2, 3, 12, 55, 16, 27, 8, 9, 4, 1, 6,
    1, 2, 7, 10, 11, 12, 9, 2, 1, 46, 1, 10, 7, 22, 7, 10, 19, 12, 13, 4, 27, 10, 25, 6, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_17 : blockBound 17 := by
  apply certifyBlock 17 (ds := [
    8, 9, 28, 7, 4, 13, 14, 25, 10, 11, 10, 3, 32, 21, 6, 1, 30, 13, 16, 13, 10, 5, 4, 7, 14,
    15, 28, 7, 6, 3, 16, 3, 18, 5, 54, 1, 2, 7, 16, 17, 22, 9, 22, 15, 16, 7, 24, 9, 2, 9,
    16, 25, 4, 13, 4, 1, 4, 23, 18, 31, 20, 25, 4, 25, 12, 1, 10, 7, 22, 7, 6, 7, 4, 1, 18,
    11, 22, 9, 10, 49, 6, 7, 18, 1, 4, 3, 12, 7, 22, 1, 8, 15, 18, 1, 6, 31, 22, 9, 6, 19])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_18 : blockBound 18 := by
  apply certifyBlock 18 (ds := [
    12, 3, 2, 7, 4, 5, 82, 7, 10, 3, 16, 5, 22, 45, 8, 1, 10, 23, 16, 51, 16, 19, 70, 1, 16,
    21, 2, 15, 6, 13, 10, 13, 10, 15, 28, 11, 30, 9, 2, 9, 18, 29, 12, 25, 8, 27, 24, 19, 28, 1,
    16, 57, 4, 5, 16, 3, 4, 15, 6, 1, 12, 9, 52, 7, 4, 11, 12, 33, 2, 1, 30, 23, 10, 15, 14,
    1, 12, 25, 6, 7, 26, 15, 4, 1, 4, 3, 10, 7, 16, 13, 12, 15, 80, 1, 22, 5, 4, 33, 8, 3])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_19 : blockBound 19 := by
  apply certifyBlock 19 (ds := [
    6, 5, 52, 13, 2, 43, 18, 7, 16, 1, 8, 3, 18, 23, 6, 13, 8, 19, 10, 1, 10, 7, 4, 3, 4,
    11, 58, 25, 8, 7, 18, 5, 12, 15, 2, 3, 40, 5, 6, 1, 2, 13, 48, 23, 16, 3, 80, 7, 28, 11,
    22, 15, 2, 7, 4, 11, 4, 13, 8, 3, 16, 23, 10, 1, 8, 1, 12, 17, 12, 1, 2, 39, 12, 1, 24,
    15, 8, 3, 12, 1, 48, 37, 14, 15, 6, 23, 4, 19, 22, 1, 6, 7, 22, 7, 2, 15, 12, 7, 6, 37])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_20 : blockBound 20 := by
  apply certifyBlock 20 (ds := [
    8, 9, 4, 5, 6, 1, 20, 7, 10, 19, 58, 27, 4, 13, 12, 43, 12, 13, 2, 3, 76, 37, 18, 3, 2,
    1, 28, 23, 16, 3, 10, 7, 24, 1, 18, 3, 4, 3, 42, 7, 18, 7, 4, 3, 12, 7, 22, 15, 8, 1,
    10, 5, 42, 1, 2, 1, 12, 13, 10, 7, 8, 3, 18, 1, 12, 45, 8, 3, 6, 19, 12, 3, 32, 1, 4,
    11, 48, 3, 2, 1, 6, 7, 24, 1, 2, 1, 4, 5, 6, 7, 8, 3, 34, 1, 4, 1, 22, 37, 28, 19])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_21 : blockBound 21 := by
  apply certifyBlock 21 (ds := [
    16, 13, 8, 27, 4, 1, 4, 25, 8, 31, 6, 5, 12, 31, 16, 1, 18, 7, 18, 1, 10, 3, 4, 7, 4,
    1, 10, 15, 12, 13, 22, 9, 2, 7, 18, 1, 12, 9, 2, 9, 18, 29, 4, 97, 4, 7, 12, 7, 12, 9,
    26, 7, 28, 1, 28, 13, 28, 9, 10, 53, 28, 7, 62, 7, 4, 11, 24, 7, 16, 19, 10, 5, 4, 1, 22,
    3, 34, 7, 6, 9, 8, 13, 10, 11, 24, 7, 2, 3, 16, 11, 6, 3, 2, 3, 18, 5, 4, 33, 16, 27])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_22 : blockBound 22 := by
  apply certifyBlock 22 (ds := [
    16, 35, 34, 21, 2, 7, 12, 7, 6, 1, 2, 33, 10, 5, 4, 7, 4, 3, 6, 61, 12, 3, 2, 1, 4,
    5, 4, 25, 32, 9, 6, 37, 10, 3, 2, 7, 24, 13, 12, 3, 16, 25, 22, 7, 6, 15, 38, 3, 12, 29,
    46, 7, 8, 13, 24, 5, 10, 3, 2, 1, 6, 23, 4, 3, 28, 1, 12, 13, 10, 9, 16, 9, 12, 11, 12,
    37, 4, 7, 6, 23, 10, 25, 2, 7, 6, 1, 18, 43, 2, 3, 6, 13, 28, 1, 14, 3, 24, 5, 16, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_23 : blockBound 23 := by
  apply certifyBlock 23 (ds := [
    2, 9, 10, 1, 16, 3, 4, 25, 12, 1, 22, 15, 14, 1, 6, 5, 52, 3, 8, 1, 18, 5, 12, 3, 16,
    1, 22, 13, 16, 1, 8, 3, 4, 23, 6, 1, 44, 13, 22, 37, 6, 15, 34, 3, 6, 5, 60, 3, 22, 19,
    12, 23, 4, 1, 2, 3, 12, 5, 6, 1, 22, 9, 22, 5, 4, 3, 4, 15, 16, 7, 12, 7, 40, 45, 4,
    7, 4, 27, 10, 1, 28, 5, 24, 7, 22, 25, 24, 19, 36, 21, 16, 25, 10, 23, 42, 13, 20, 37, 6, 11])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_24 : blockBound 24 := by
  apply certifyBlock 24 (ds := [
    16, 45, 2, 1, 22, 1, 4, 3, 2, 7, 6, 7, 4, 3, 32, 7, 18, 23, 28, 1, 8, 13, 10, 5, 4,
    7, 8, 19, 6, 1, 6, 3, 2, 27, 58, 11, 24, 7, 32, 3, 18, 17, 4, 3, 22, 15, 10, 13, 10, 9,
    2, 9, 4, 1, 12, 1, 8, 45, 16, 1, 22, 15, 14, 1, 4, 25, 28, 3, 16, 1, 36, 5, 12, 13, 28,
    27, 4, 37, 16, 9, 56, 7, 18, 61, 4, 3, 2, 3, 22, 7, 10, 3, 2, 7, 4, 1, 4, 3, 10, 9])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_25 : blockBound 25 := by
  apply certifyBlock 25 (ds := [
    12, 13, 10, 7, 28, 3, 28, 13, 6, 3, 8, 7, 22, 23, 4, 1, 8, 19, 16, 11, 16, 19, 14, 7, 6,
    5, 4, 15, 20, 21, 18, 25, 28, 1, 2, 1, 10, 23, 12, 9, 10, 9, 4, 17, 24, 7, 14, 19, 40, 1,
    18, 7, 22, 15, 6, 7, 18, 3, 8, 21, 12, 13, 4, 13, 2, 3, 4, 35, 18, 1, 8, 15, 22, 5, 16,
    1, 10, 69, 10, 37, 22, 25, 2, 15, 6, 31, 4, 7, 2, 13, 40, 5, 18, 1, 4, 15, 22, 17, 16, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_26 : blockBound 26 := by
  apply certifyBlock 26 (ds := [
    10, 15, 18, 1, 12, 51, 4, 39, 12, 61, 10, 37, 28, 15, 16, 5, 12, 13, 8, 27, 6, 25, 12, 1, 8,
    25, 34, 17, 6, 19, 2, 37, 4, 5, 16, 21, 4, 39, 22, 7, 6, 3, 32, 13, 12, 1, 12, 9, 2, 7,
    6, 7, 10, 1, 14, 25, 34, 7, 10, 3, 2, 7, 18, 1, 4, 1, 20, 7, 18, 7, 10, 19, 38, 3, 24,
    1, 10, 7, 20, 33, 6, 25, 34, 1, 4, 15, 4, 5, 10, 21, 10, 3, 4, 23, 6, 7, 2, 7, 16, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_27 : blockBound 27 := by
  apply certifyBlock 27 (ds := [
    60, 15, 4, 43, 4, 1, 12, 15, 8, 21, 6, 29, 42, 7, 2, 3, 4, 19, 6, 3, 2, 7, 10, 5, 6,
    13, 58, 13, 18, 1, 18, 19, 14, 3, 4, 1, 30, 7, 8, 13, 42, 7, 22, 37, 2, 1, 22, 13, 18, 19,
    20, 3, 18, 1, 6, 21, 2, 15, 10, 1, 6, 13, 20, 3, 12, 1, 12, 3, 16, 1, 12, 5, 4, 21, 4,
    1, 4, 29, 10, 1, 22, 7, 30, 5, 16, 3, 32, 7, 18, 59, 6, 9, 2, 1, 12, 23, 10, 37, 26, 13])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_28 : blockBound 28 := by
  apply certifyBlock 28 (ds := [
    10, 23, 10, 1, 2, 15, 4, 5, 22, 39, 20, 7, 22, 17, 4, 7, 2, 15, 16, 7, 6, 9, 2, 1, 4,
    41, 10, 37, 10, 7, 18, 13, 4, 1, 4, 1, 12, 17, 16, 13, 26, 9, 4, 13, 18, 7, 14, 19, 12, 1,
    12, 9, 2, 7, 18, 13, 18, 15, 22, 7, 48, 5, 10, 1, 26, 13, 22, 5, 16, 19, 26, 7, 10, 11, 4,
    1, 20, 3, 6, 11, 6, 7, 8, 1, 4, 41, 4, 49, 20, 1, 22, 5, 12, 15, 22, 1, 10, 5, 18, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_29 : blockBound 29 := by
  apply certifyBlock 29 (ds := [
    8, 15, 4, 17, 18, 15, 4, 3, 10, 23, 30, 3, 10, 13, 18, 1, 4, 19, 10, 3, 6, 23, 28, 1, 4,
    1, 12, 5, 30, 9, 22, 7, 18, 1, 6, 13, 4, 7, 28, 19, 10, 7, 2, 1, 4, 11, 12, 9, 2, 3,
    10, 7, 18, 25, 2, 7, 4, 7, 18, 1, 16, 25, 22, 1, 4, 13, 8, 13, 22, 7, 22, 9, 4, 1, 16,
    17, 12, 37, 20, 13, 18, 13, 12, 7, 8, 1, 18, 5, 6, 9, 2, 3, 18, 43, 12, 13, 4, 9, 16, 11])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_30 : blockBound 30 := by
  apply certifyBlock 30 (ds := [
    12, 3, 2, 33, 6, 11, 4, 13, 10, 9, 10, 47, 48, 15, 4, 1, 18, 7, 16, 3, 32, 7, 4, 5, 12,
    1, 8, 9, 22, 17, 10, 3, 4, 31, 6, 7, 4, 13, 8, 43, 6, 25, 4, 7, 8, 1, 28, 25, 6, 21,
    2, 3, 24, 1, 4, 3, 20, 15, 52, 31, 6, 27, 28, 7, 16, 5, 22, 7, 16, 7, 28, 5, 4, 1, 56,
    3, 22, 23, 16, 9, 2, 15, 10, 11, 12, 3, 4, 9, 6, 11, 28, 19, 2, 1, 18, 23, 10, 9, 8, 33])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_31 : blockBound 31 := by
  apply certifyBlock 31 (ds := [
    6, 17, 30, 3, 4, 1, 4, 47, 10, 1, 2, 13, 4, 7, 6, 21, 8, 3, 6, 11, 10, 13, 22, 25, 4,
    17, 30, 33, 26, 33, 12, 23, 24, 1, 14, 1, 12, 7, 46, 1, 22, 7, 18, 5, 4, 3, 14, 13, 10, 29,
    12, 7, 22, 3, 4, 1, 18, 9, 2, 1, 18, 5, 4, 45, 4, 37, 24, 7, 18, 43, 22, 3, 28, 1, 16,
    27, 2, 15, 36, 7, 70, 7, 2, 1, 6, 7, 54, 9, 22, 9, 12, 13, 22, 7, 2, 1, 18, 5, 16, 33])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_32 : blockBound 32 := by
  apply certifyBlock 32 (ds := [
    2, 13, 28, 1, 18, 25, 28, 13, 6, 11, 60, 43, 2, 1, 16, 31, 24, 13, 46, 1, 12, 7, 10, 51, 14,
    21, 12, 7, 22, 7, 8, 25, 24, 47, 24, 13, 34, 7, 12, 1, 16, 15, 14, 31, 16, 1, 24, 3, 2, 7,
    6, 25, 34, 1, 16, 7, 30, 23, 16, 19, 2, 3, 12, 23, 4, 1, 4, 7, 30, 11, 18, 9, 14, 1, 4,
    17, 22, 7, 2, 1, 12, 23, 4, 15, 2, 15, 4, 7, 10, 1, 10, 19, 22, 11, 4, 7, 4, 19, 18, 23])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_33 : blockBound 33 := by
  apply certifyBlock 33 (ds := [
    6, 25, 8, 1, 54, 1, 10, 9, 2, 31, 6, 29, 12, 1, 4, 15, 10, 13, 16, 37, 2, 13, 18, 25, 22,
    1, 14, 25, 16, 7, 10, 3, 8, 1, 4, 7, 18, 3, 26, 1, 6, 35, 4, 7, 2, 43, 22, 19, 10, 1,
    16, 3, 10, 5, 16, 1, 8, 19, 12, 1, 10, 13, 4, 25, 6, 23, 4, 45, 16, 3, 22, 5, 22, 1, 16,
    7, 10, 25, 60, 33, 16, 7, 28, 11, 6, 27, 2, 15, 18, 1, 28, 3, 32, 3, 16, 7, 4, 7, 46, 19])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_34 : blockBound 34 := by
  apply certifyBlock 34 (ds := [
    10, 17, 10, 13, 14, 3, 4, 5, 22, 21, 46, 13, 28, 13, 4, 13, 8, 27, 10, 13, 6, 19, 4, 67, 12,
    7, 10, 9, 32, 67, 22, 5, 4, 37, 32, 1, 12, 43, 12, 9, 8, 9, 12, 5, 12, 1, 2, 15, 6, 7,
    10, 9, 2, 13, 16, 5, 4, 15, 32, 7, 18, 7, 4, 7, 4, 33, 30, 25, 10, 7, 10, 9, 18, 1, 6,
    51, 22, 39, 6, 1, 6, 3, 4, 7, 16, 13, 12, 15, 22, 1, 36, 25, 12, 25, 8, 31, 4, 43, 18, 9])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_35 : blockBound 35 := by
  apply certifyBlock 35 (ds := [
    8, 7, 10, 1, 12, 31, 20, 73, 16, 17, 6, 7, 2, 13, 28, 1, 28, 13, 8, 1, 12, 47, 28, 3, 4,
    7, 22, 5, 10, 1, 8, 3, 22, 1, 4, 1, 4, 37, 18, 37, 42, 9, 28, 13, 48, 25, 18, 3, 2, 3,
    6, 29, 4, 25, 2, 27, 4, 25, 22, 7, 16, 3, 18, 7, 12, 3, 20, 7, 12, 29, 12, 25, 4, 37, 4,
    5, 12, 7, 40, 9, 46, 5, 4, 13, 8, 15, 4, 37, 6, 21, 2, 25, 4, 7, 6, 7, 52, 3, 16, 19])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_36 : blockBound 36 := by
  apply certifyBlock 36 (ds := [
    18, 7, 2, 3, 18, 11, 28, 7, 8, 33, 10, 37, 22, 7, 2, 31, 22, 17, 16, 37, 2, 3, 18, 1, 24,
    73, 4, 9, 16, 29, 16, 25, 8, 25, 4, 25, 42, 19, 8, 9, 16, 7, 10, 1, 4, 25, 10, 23, 22, 1,
    2, 9, 18, 17, 4, 51, 2, 3, 40, 1, 16, 3, 2, 3, 4, 77, 10, 13, 26, 1, 6, 23, 18, 3, 16,
    3, 4, 7, 16, 13, 8, 25, 28, 11, 24, 1, 2, 19, 18, 7, 22, 3, 4, 55, 24, 25, 18, 13, 20, 31])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_37 : blockBound 37 := by
  apply certifyBlock 37 (ds := [
    28, 25, 10, 15, 14, 7, 10, 19, 16, 9, 32, 7, 10, 7, 36, 1, 74, 7, 22, 13, 16, 9, 2, 13, 12,
    43, 24, 13, 20, 1, 6, 17, 4, 1, 4, 7, 10, 25, 28, 13, 8, 15, 22, 5, 22, 1, 14, 15, 6, 7,
    18, 3, 4, 1, 16, 1, 18, 15, 16, 21, 60, 7, 22, 1, 8, 15, 10, 13, 16, 3, 92, 7, 10, 1, 22,
    1, 2, 9, 42, 41, 12, 9, 8, 1, 6, 25, 4, 7, 2, 1, 10, 19, 24, 1, 2, 27, 4, 7, 12, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_38 : blockBound 38 := by
  apply certifyBlock 38 (ds := [
    16, 7, 4, 13, 4, 1, 2, 3, 22, 7, 16, 7, 20, 21, 12, 7, 12, 3, 2, 7, 10, 5, 18, 21, 8,
    1, 82, 5, 12, 33, 22, 7, 42, 5, 4, 27, 4, 7, 16, 17, 6, 9, 4, 3, 6, 13, 42, 9, 8, 1,
    18, 5, 4, 7, 4, 3, 4, 7, 28, 3, 2, 49, 4, 11, 42, 13, 10, 43, 6, 1, 6, 25, 2, 25, 22,
    13, 22, 9, 2, 19, 6, 7, 12, 1, 8, 31, 22, 7, 6, 1, 40, 3, 12, 1, 52, 15, 14, 15, 10, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_39 : blockBound 39 := by
  apply certifyBlock 39 (ds := [
    18, 3, 14, 7, 4, 13, 10, 7, 8, 1, 18, 5, 10, 3, 2, 3, 4, 23, 30, 57, 56, 7, 10, 1, 34,
    31, 4, 3, 12, 31, 10, 7, 40, 33, 18, 5, 18, 39, 20, 19, 6, 35, 12, 3, 4, 1, 10, 19, 16, 13,
    16, 3, 40, 23, 6, 15, 8, 9, 22, 23, 12, 9, 14, 7, 16, 1, 12, 3, 2, 7, 72, 25, 22, 25, 14,
    25, 4, 7, 6, 49, 16, 43, 4, 1, 22, 7, 2, 9, 10, 23, 10, 39, 4, 1, 22, 5, 18, 15, 16, 57])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_40 : blockBound 40 := by
  apply certifyBlock 40 (ds := [
    10, 5, 18, 3, 28, 1, 18, 7, 12, 39, 10, 43, 28, 7, 4, 61, 8, 3, 18, 47, 6, 3, 4, 1, 4,
    1, 12, 13, 28, 7, 16, 5, 24, 1, 22, 13, 30, 5, 6, 19, 8, 3, 4, 23, 18, 1, 28, 15, 18, 13,
    28, 3, 22, 43, 16, 1, 22, 33, 10, 9, 10, 5, 22, 3, 22, 7, 4, 49, 16, 1, 8, 13, 12, 5, 4,
    15, 20, 3, 6, 1, 6, 15, 50, 21, 22, 1, 10, 25, 26, 9, 16, 13, 4, 3, 8, 43, 4, 65, 18, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_41 : blockBound 41 := by
  apply certifyBlock 41 (ds := [
    8, 13, 10, 5, 22, 3, 8, 9, 16, 19, 16, 25, 8, 1, 18, 17, 18, 25, 2, 1, 40, 5, 52, 1, 14,
    3, 10, 5, 10, 57, 2, 13, 4, 23, 6, 1, 2, 9, 6, 1, 6, 9, 4, 25, 24, 1, 4, 9, 20, 3,
    48, 5, 4, 1, 16, 1, 18, 5, 16, 21, 8, 13, 28, 5, 12, 21, 4, 3, 6, 1, 10, 37, 14, 1, 18,
    1, 22, 33, 2, 1, 6, 13, 18, 1, 14, 3, 10, 37, 6, 3, 2, 49, 12, 7, 4, 7, 4, 19, 10, 13])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_42 : blockBound 42 := by
  apply certifyBlock 42 (ds := [
    60, 13, 4, 15, 6, 1, 10, 3, 16, 21, 10, 19, 18, 33, 2, 25, 22, 23, 6, 3, 8, 19, 4, 13, 28,
    1, 4, 27, 16, 7, 66, 9, 44, 7, 12, 17, 4, 3, 8, 21, 12, 25, 18, 21, 2, 3, 12, 37, 6, 1,
    86, 27, 18, 25, 16, 33, 4, 19, 6, 1, 12, 3, 2, 33, 16, 1, 18, 19, 56, 31, 10, 13, 18, 3, 8,
    43, 48, 47, 6, 37, 16, 19, 4, 5, 4, 7, 10, 3, 6, 37, 6, 33, 8, 1, 36, 7, 22, 19, 26, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_43 : blockBound 43 := by
  apply certifyBlock 43 (ds := [
    16, 23, 4, 7, 2, 3, 12, 7, 6, 1, 22, 19, 58, 11, 16, 7, 28, 3, 12, 11, 6, 9, 20, 7, 4,
    5, 12, 13, 16, 1, 30, 79, 4, 7, 44, 1, 28, 7, 16, 1, 2, 7, 24, 7, 12, 25, 2, 7, 18, 11,
    6, 33, 14, 45, 12, 5, 18, 45, 8, 7, 10, 25, 22, 1, 2, 1, 4, 5, 10, 1, 32, 7, 4, 1, 4,
    15, 28, 9, 28, 11, 10, 13, 4, 1, 4, 31, 4, 7, 10, 3, 6, 17, 18, 75, 14, 31, 10, 13, 16, 9])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_44 : blockBound 44 := by
  apply certifyBlock 44 (ds := [
    20, 9, 40, 1, 6, 7, 2, 7, 36, 1, 16, 9, 8, 1, 12, 5, 10, 3, 22, 3, 6, 23, 28, 27, 8,
    25, 4, 13, 22, 31, 10, 3, 4, 17, 4, 7, 32, 3, 22, 19, 6, 27, 2, 1, 6, 53, 22, 3, 20, 7,
    10, 23, 4, 7, 2, 1, 54, 37, 12, 31, 16, 3, 60, 5, 22, 15, 4, 13, 18, 7, 18, 25, 8, 1, 12,
    13, 30, 37, 8, 33, 12, 7, 4, 27, 22, 1, 24, 19, 6, 39, 28, 13, 10, 13, 16, 1, 14, 7, 16, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_45 : blockBound 45 := by
  apply certifyBlock 45 (ds := [
    10, 7, 2, 1, 22, 13, 18, 9, 26, 1, 6, 17, 12, 3, 22, 7, 4, 25, 6, 9, 8, 27, 4, 1, 16,
    7, 2, 19, 10, 1, 12, 7, 8, 1, 16, 5, 4, 9, 2, 1, 6, 19, 4, 7, 2, 27, 18, 5, 22, 19,
    8, 13, 52, 1, 12, 15, 4, 19, 12, 7, 36, 9, 8, 37, 18, 1, 22, 15, 20, 7, 18, 5, 12, 3, 2,
    7, 30, 5, 18, 7, 22, 25, 4, 5, 24, 25, 32, 15, 10, 1, 18, 3, 4, 7, 6, 71, 72, 3, 2, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_46 : blockBound 46 := by
  apply certifyBlock 46 (ds := [
    18, 7, 10, 1, 92, 1, 30, 25, 36, 7, 16, 3, 12, 1, 16, 1, 4, 19, 12, 17, 70, 9, 4, 3, 6,
    25, 4, 19, 2, 27, 16, 5, 22, 31, 8, 37, 42, 35, 40, 9, 2, 3, 4, 1, 34, 21, 4, 13, 12, 1,
    16, 3, 2, 3, 4, 7, 42, 3, 32, 21, 10, 17, 18, 25, 8, 1, 18, 23, 6, 21, 26, 7, 10, 5, 24,
    13, 38, 15, 10, 7, 6, 43, 8, 3, 4, 13, 18, 19, 16, 3, 18, 7, 10, 15, 2, 15, 12, 5, 12, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_47 : blockBound 47 := by
  apply certifyBlock 47 (ds := [
    2, 7, 18, 1, 16, 15, 14, 7, 12, 17, 10, 15, 4, 3, 16, 1, 10, 3, 28, 7, 6, 7, 58, 21, 4,
    1, 12, 17, 46, 7, 2, 19, 10, 1, 16, 1, 20, 19, 6, 7, 6, 3, 4, 15, 18, 31, 4, 13, 22, 21,
    28, 5, 12, 1, 8, 3, 4, 5, 66, 39, 2, 9, 10, 31, 36, 7, 22, 3, 12, 29, 6, 13, 4, 27, 4,
    13, 48, 13, 2, 1, 12, 7, 4, 1, 8, 1, 12, 5, 12, 21, 28, 15, 4, 1, 18, 1, 2, 27, 6, 23])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_48 : blockBound 48 := by
  apply certifyBlock 48 (ds := [
    12, 3, 8, 21, 46, 31, 12, 3, 2, 21, 70, 23, 18, 13, 16, 31, 4, 7, 6, 3, 26, 9, 12, 31, 12,
    15, 22, 13, 12, 71, 36, 9, 10, 1, 18, 5, 10, 15, 8, 63, 30, 13, 12, 31, 4, 13, 24, 43, 16, 1,
    20, 79, 42, 7, 4, 13, 22, 3, 28, 11, 22, 3, 2, 31, 6, 11, 12, 9, 10, 7, 12, 59, 18, 15, 8,
    1, 34, 5, 18, 9, 20, 13, 30, 7, 18, 1, 10, 25, 10, 7, 18, 19, 4, 1, 6, 11, 34, 7, 2, 31])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_49 : blockBound 49 := by
  apply certifyBlock 49 (ds := [
    10, 5, 28, 1, 8, 7, 30, 5, 6, 1, 50, 27, 4, 17, 22, 27, 2, 25, 30, 1, 12, 3, 20, 3, 18,
    11, 4, 3, 40, 19, 30, 23, 18, 45, 16, 1, 64, 17, 16, 33, 2, 25, 22, 1, 18, 7, 22, 3, 22, 29,
    6, 3, 14, 1, 12, 1, 4, 19, 2, 9, 6, 19, 48, 37, 4, 7, 4, 7, 40, 39, 22, 13, 22, 11, 6,
    3, 2, 33, 12, 11, 6, 9, 80, 57, 4, 5, 24, 3, 22, 1, 6, 17, 28, 13, 2, 15, 12, 5, 36, 9])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_50 : blockBound 50 := by
  apply certifyBlock 50 (ds := [
    2, 15, 4, 1, 16, 3, 8, 3, 16, 23, 10, 27, 4, 1, 58, 1, 4, 147, 32, 7, 78, 7, 18, 7, 26,
    13, 24, 5, 36, 1, 2, 75, 12, 5, 64, 15, 2, 7, 12, 11, 16, 7, 2, 1, 4, 5, 12, 9, 26, 7,
    36, 37, 12, 1, 2, 1, 22, 13, 12, 3, 38, 9, 4, 23, 4, 7, 22, 3, 28, 19, 6, 3, 28, 3, 36,
    1, 18, 7, 8, 1, 18, 29, 12, 15, 38, 1, 4, 7, 22, 9, 2, 15, 10, 11, 42, 27, 14, 25, 6, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_51 : blockBound 51 := by
  apply certifyBlock 51 (ds := [
    6, 15, 4, 25, 6, 71, 28, 7, 2, 3, 10, 5, 4, 3, 14, 7, 4, 19, 42, 1, 2, 15, 4, 5, 12,
    1, 8, 9, 40, 7, 16, 3, 4, 37, 4, 5, 10, 3, 16, 7, 10, 7, 28, 3, 8, 45, 4, 17, 6, 13,
    28, 13, 4, 1, 24, 25, 20, 9, 16, 11, 58, 37, 2, 21, 12, 23, 10, 9, 8, 1, 18, 17, 10, 3, 4,
    1, 18, 7, 46, 1, 38, 9, 24, 7, 36, 3, 68, 19, 6, 13, 42, 7, 8, 1, 64, 5, 10, 45, 2, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_52 : blockBound 52 := by
  apply certifyBlock 52 (ds := [
    30, 47, 18, 1, 2, 21, 12, 17, 12, 7, 10, 9, 4, 17, 6, 57, 4, 13, 6, 7, 12, 33, 2, 7, 6,
    1, 54, 7, 20, 37, 6, 7, 48, 21, 4, 1, 12, 19, 6, 9, 20, 3, 4, 73, 6, 1, 4, 15, 66, 11,
    22, 9, 2, 1, 76, 1, 12, 7, 26, 3, 42, 13, 10, 1, 8, 7, 30, 25, 18, 33, 2, 37, 18, 17, 24,
    37, 4, 9, 16, 23, 28, 3, 32, 37, 46, 5, 22, 7, 10, 27, 10, 5, 58, 1, 16, 15, 4, 37, 6, 3])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_53 : blockBound 53 := by
  apply certifyBlock 53 (ds := [
    2, 15, 18, 1, 36, 3, 14, 9, 22, 17, 28, 19, 20, 1, 4, 17, 34, 27, 16, 3, 22, 5, 4, 13, 2,
    3, 12, 43, 6, 7, 16, 39, 10, 11, 4, 51, 10, 45, 12, 1, 6, 7, 40, 1, 16, 7, 28, 3, 22, 19,
    22, 13, 48, 15, 2, 31, 40, 17, 16, 1, 8, 9, 10, 7, 76, 25, 2, 19, 16, 1, 36, 3, 28, 7, 18,
    11, 22, 27, 8, 37, 6, 25, 18, 1, 2, 13, 18, 25, 12, 43, 8, 9, 34, 23, 4, 3, 10, 3, 22, 29])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_54 : blockBound 54 := by
  apply certifyBlock 54 (ds := [
    6, 13, 2, 1, 36, 13, 10, 3, 16, 19, 16, 5, 12, 45, 14, 51, 18, 25, 10, 1, 32, 13, 28, 1, 12,
    3, 2, 25, 10, 1, 12, 27, 8, 7, 16, 13, 40, 9, 10, 39, 22, 23, 30, 15, 14, 1, 24, 19, 10, 3,
    16, 3, 4, 11, 6, 15, 2, 19, 10, 19, 10, 13, 8, 3, 6, 1, 18, 7, 8, 49, 46, 5, 12, 1, 14,
    1, 4, 13, 30, 19, 8, 3, 64, 7, 76, 1, 8, 3, 12, 1, 42, 49, 2, 51, 4, 23, 28, 37, 2, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_55 : blockBound 55 := by
  apply certifyBlock 55 (ds := [
    16, 13, 4, 7, 14, 1, 18, 7, 6, 1, 16, 7, 4, 5, 58, 15, 22, 13, 10, 49, 6, 7, 44, 1, 12,
    11, 10, 15, 2, 33, 28, 7, 24, 15, 32, 1, 18, 17, 6, 3, 20, 9, 12, 25, 4, 13, 8, 7, 6, 1,
    12, 7, 2, 3, 4, 37, 4, 27, 2, 1, 6, 29, 30, 1, 8, 1, 12, 25, 18, 9, 10, 9, 18, 1, 46,
    7, 20, 9, 6, 7, 40, 39, 20, 1, 12, 1, 22, 7, 2, 1, 6, 7, 12, 15, 4, 15, 4, 7, 12, 27])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_56 : blockBound 56 := by
  apply certifyBlock 56 (ds := [
    2, 19, 10, 17, 6, 3, 22, 9, 36, 7, 6, 9, 14, 15, 4, 11, 10, 3, 2, 1, 12, 19, 4, 7, 34,
    7, 4, 19, 22, 9, 38, 13, 4, 5, 36, 7, 4, 9, 10, 11, 16, 3, 8, 15, 24, 7, 34, 7, 10, 9,
    6, 35, 24, 15, 4, 1, 4, 7, 58, 7, 8, 39, 4, 1, 6, 15, 4, 7, 16, 11, 16, 13, 32, 63, 12,
    5, 4, 3, 8, 3, 10, 13, 4, 25, 14, 15, 18, 17, 6, 31, 26, 7, 22, 7, 18, 25, 38, 3, 12, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_57 : blockBound 57 := by
  apply certifyBlock 57 (ds := [
    6, 3, 44, 7, 12, 7, 12, 13, 2, 1, 28, 23, 22, 43, 4, 7, 54, 5, 6, 7, 2, 13, 18, 1, 22,
    1, 2, 15, 6, 7, 6, 7, 2, 1, 4, 7, 42, 9, 8, 13, 16, 53, 24, 15, 4, 57, 10, 23, 16, 31,
    28, 9, 28, 5, 22, 1, 4, 15, 28, 1, 18, 19, 20, 21, 4, 53, 54, 15, 2, 27, 16, 7, 60, 1, 2,
    3, 28, 7, 18, 39, 2, 3, 10, 37, 18, 21, 8, 9, 12, 7, 12, 13, 2, 7, 12, 11, 10, 55, 2, 3])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_58 : blockBound 58 := by
  apply certifyBlock 58 (ds := [
    22, 5, 22, 1, 8, 3, 4, 19, 12, 9, 22, 7, 28, 1, 4, 21, 38, 9, 6, 11, 16, 7, 2, 1, 4,
    5, 22, 37, 8, 1, 30, 5, 4, 1, 2, 13, 10, 5, 46, 7, 16, 13, 30, 5, 22, 45, 2, 15, 36, 1,
    28, 25, 2, 25, 6, 1, 12, 3, 20, 3, 6, 7, 34, 13, 58, 1, 4, 5, 6, 13, 16, 15, 60, 1, 6,
    1, 14, 7, 10, 1, 30, 27, 4, 15, 4, 5, 12, 37, 46, 7, 16, 5, 4, 25, 2, 13, 24, 59, 70, 3])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_59 : blockBound 59 := by
  apply certifyBlock 59 (ds := [
    10, 33, 4, 17, 6, 7, 8, 9, 10, 7, 16, 3, 4, 31, 4, 23, 18, 3, 2, 21, 10, 5, 4, 27, 32,
    7, 28, 29, 48, 1, 2, 7, 4, 5, 18, 13, 22, 19, 16, 13, 12, 9, 8, 1, 12, 43, 4, 7, 32, 19,
    18, 7, 4, 7, 4, 21, 10, 43, 6, 1, 20, 15, 28, 1, 12, 27, 28, 3, 16, 1, 16, 19, 2, 15, 24,
    5, 10, 25, 10, 9, 10, 17, 12, 1, 4, 21, 28, 49, 6, 1, 10, 39, 10, 61, 6, 1, 14, 3, 18, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_60 : blockBound 60 := by
  apply certifyBlock 60 (ds := [
    16, 13, 20, 13, 22, 1, 18, 13, 98, 1, 6, 7, 10, 3, 14, 1, 10, 23, 30, 3, 26, 13, 28, 7, 54,
    15, 8, 9, 18, 1, 6, 15, 4, 13, 12, 7, 34, 7, 2, 31, 16, 7, 34, 3, 22, 1, 4, 55, 12, 21,
    46, 9, 4, 11, 12, 15, 4, 25, 6, 1, 18, 9, 4, 7, 36, 23, 28, 3, 16, 21, 36, 17, 24, 15, 4,
    13, 24, 5, 10, 3, 2, 3, 4, 5, 22, 7, 22, 9, 16, 11, 18, 33, 14, 3, 12, 1, 18, 19, 32, 9])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_61 : blockBound 61 := by
  apply certifyBlock 61 (ds := [
    16, 5, 10, 37, 4, 7, 10, 17, 18, 1, 26, 3, 34, 11, 4, 25, 38, 9, 30, 1, 6, 27, 4, 3, 16,
    1, 12, 3, 20, 1, 12, 37, 10, 1, 8, 25, 22, 23, 16, 1, 8, 25, 18, 7, 42, 15, 68, 7, 16, 17,
    12, 7, 20, 3, 22, 1, 4, 9, 22, 13, 16, 5, 18, 1, 16, 1, 22, 5, 6, 7, 2, 9, 10, 17, 24,
    1, 4, 9, 30, 17, 12, 7, 2, 13, 6, 11, 4, 9, 8, 1, 52, 13, 4, 7, 4, 25, 34, 29, 6, 13])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_62 : blockBound 62 := by
  apply certifyBlock 62 (ds := [
    10, 19, 4, 7, 24, 3, 20, 9, 10, 7, 16, 15, 10, 27, 18, 1, 12, 63, 22, 1, 22, 19, 4, 15, 4,
    15, 4, 5, 18, 3, 46, 7, 4, 1, 4, 1, 10, 7, 6, 1, 16, 7, 10, 13, 12, 65, 18, 7, 8, 3,
    18, 23, 22, 1, 2, 15, 12, 5, 10, 39, 2, 39, 22, 11, 6, 1, 4, 45, 46, 43, 72, 39, 8, 15, 4,
    11, 4, 3, 16, 3, 28, 7, 4, 55, 74, 25, 4, 5, 10, 13, 2, 3, 4, 11, 6, 3, 20, 13, 12, 37])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_63 : blockBound 63 := by
  apply certifyBlock 63 (ds := [
    28, 13, 8, 7, 6, 1, 4, 25, 22, 13, 28, 49, 4, 1, 2, 33, 22, 7, 18, 39, 10, 3, 12, 11, 18,
    7, 2, 19, 12, 13, 46, 3, 14, 45, 22, 5, 22, 43, 10, 1, 18, 23, 18, 27, 4, 3, 34, 5, 16, 1,
    8, 25, 18, 5, 12, 15, 38, 13, 28, 1, 18, 7, 10, 21, 12, 1, 48, 7, 2, 19, 10, 5, 10, 13, 22,
    7, 4, 5, 6, 7, 46, 13, 12, 5, 42, 7, 8, 9, 12, 37, 10, 3, 58, 21, 34, 25, 10, 3, 26, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_64 : blockBound 64 := by
  apply certifyBlock 64 (ds := [
    6, 7, 12, 3, 16, 73, 18, 17, 18, 21, 32, 9, 40, 7, 4, 43, 2, 9, 18, 1, 36, 15, 4, 25, 22,
    25, 10, 9, 2, 9, 12, 25, 10, 1, 64, 3, 10, 47, 30, 9, 2, 25, 10, 11, 6, 15, 44, 19, 40, 7,
    6, 13, 4, 31, 22, 11, 60, 3, 32, 1, 12, 7, 18, 7, 4, 13, 4, 19, 16, 9, 8, 3, 34, 11, 18,
    21, 14, 7, 6, 1, 10, 39, 4, 7, 6, 11, 28, 3, 8, 19, 12, 25, 10, 7, 38, 25, 54, 29, 6, 9])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_65 : blockBound 65 := by
  apply certifyBlock 65 (ds := [
    8, 7, 24, 61, 18, 13, 4, 7, 16, 19, 12, 49, 8, 1, 54, 65, 18, 7, 8, 7, 10, 5, 12, 31, 28,
    21, 22, 13, 22, 1, 16, 15, 4, 7, 24, 1, 8, 9, 28, 1, 16, 9, 32, 3, 36, 1, 4, 3, 20, 1,
    10, 23, 22, 27, 22, 3, 22, 5, 36, 3, 26, 25, 10, 5, 12, 13, 4, 39, 6, 7, 12, 7, 2, 15, 6,
    1, 4, 19, 16, 3, 16, 5, 10, 7, 8, 7, 24, 7, 6, 1, 2, 7, 12, 31, 18, 91, 8, 25, 6, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_66 : blockBound 66 := by
  apply certifyBlock 66 (ds := [
    6, 37, 4, 1, 18, 5, 12, 25, 2, 27, 36, 7, 4, 1, 4, 15, 22, 35, 16, 57, 2, 15, 30, 11, 4,
    15, 20, 3, 46, 7, 30, 39, 14, 7, 16, 1, 12, 13, 2, 27, 6, 17, 4, 57, 2, 1, 30, 13, 28, 9,
    2, 25, 24, 13, 6, 3, 52, 3, 12, 7, 16, 7, 4, 3, 24, 23, 28, 9, 16, 3, 12, 49, 12, 3, 14,
    7, 10, 19, 10, 19, 32, 3, 4, 23, 22, 3, 2, 7, 22, 13, 16, 19, 14, 7, 16, 11, 12, 3, 8, 3])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_67 : blockBound 67 := by
  apply certifyBlock 67 (ds := [
    30, 43, 4, 1, 14, 33, 10, 47, 18, 1, 2, 3, 4, 1, 6, 15, 2, 7, 36, 11, 30, 7, 2, 1, 4,
    7, 4, 7, 26, 37, 6, 25, 24, 1, 32, 7, 10, 13, 16, 33, 2, 3, 12, 13, 4, 27, 8, 3, 16, 7,
    6, 37, 4, 25, 4, 5, 22, 15, 10, 9, 36, 5, 52, 1, 2, 25, 4, 19, 12, 7, 2, 9, 4, 37, 16,
    1, 22, 15, 6, 1, 12, 3, 22, 1, 6, 1, 10, 15, 8, 3, 22, 7, 10, 7, 4, 25, 30, 23, 12, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_68 : blockBound 68 := by
  apply certifyBlock 68 (ds := [
    28, 7, 4, 31, 22, 1, 34, 25, 28, 11, 6, 3, 14, 7, 22, 37, 4, 9, 22, 43, 6, 25, 4, 1, 32,
    1, 4, 53, 30, 9, 2, 9, 28, 5, 24, 7, 4, 33, 10, 53, 12, 37, 2, 21, 4, 11, 4, 15, 2, 1,
    22, 5, 24, 1, 8, 15, 58, 23, 16, 13, 22, 13, 18, 7, 6, 1, 20, 9, 12, 23, 22, 7, 4, 1, 46,
    7, 24, 3, 16, 7, 6, 7, 28, 1, 38, 13, 18, 13, 30, 7, 10, 7, 12, 7, 4, 33, 2, 39, 30, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_69 : blockBound 69 := by
  apply certifyBlock 69 (ds := [
    78, 33, 38, 15, 4, 11, 34, 3, 20, 1, 12, 35, 28, 13, 44, 3, 24, 7, 28, 9, 22, 15, 22, 11, 4,
    1, 28, 19, 12, 1, 18, 9, 28, 15, 18, 25, 4, 3, 32, 27, 6, 19, 4, 1, 2, 13, 24, 67, 22, 21,
    20, 7, 4, 11, 28, 1, 2, 13, 16, 43, 10, 7, 8, 61, 6, 17, 48, 49, 28, 1, 12, 25, 4, 13, 2,
    21, 4, 25, 10, 1, 8, 37, 24, 1, 18, 15, 2, 105, 18, 1, 6, 7, 58, 25, 6, 1, 18, 13, 22, 27])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_70 : blockBound 70 := by
  apply certifyBlock 70 (ds := [
    18, 7, 24, 21, 26, 33, 4, 7, 12, 1, 8, 15, 18, 1, 28, 1, 14, 3, 16, 23, 16, 7, 2, 27, 64,
    5, 22, 9, 2, 9, 16, 17, 30, 31, 4, 3, 18, 37, 28, 27, 70, 9, 10, 1, 16, 25, 20, 7, 10, 1,
    16, 27, 4, 7, 42, 47, 10, 9, 32, 27, 12, 25, 22, 45, 4, 1, 4, 13, 36, 3, 28, 9, 18, 31, 16,
    3, 2, 9, 6, 29, 6, 9, 4, 15, 4, 13, 18, 9, 2, 31, 10, 23, 58, 7, 2, 7, 10, 25, 10, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_71 : blockBound 71 := by
  apply certifyBlock 71 (ds := [
    20, 9, 4, 23, 4, 31, 4, 9, 16, 7, 46, 3, 4, 1, 66, 13, 28, 7, 22, 21, 16, 17, 4, 15, 8,
    31, 28, 47, 36, 1, 8, 3, 4, 5, 36, 3, 2, 15, 10, 13, 12, 7, 2, 27, 4, 5, 12, 33, 16, 1,
    6, 5, 58, 3, 16, 7, 10, 17, 6, 1, 8, 19, 12, 1, 42, 7, 4, 9, 18, 19, 6, 39, 2, 25, 18,
    7, 4, 25, 2, 19, 10, 5, 10, 25, 2, 7, 12, 7, 18, 1, 8, 15, 18, 13, 4, 27, 10, 9, 18, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_72 : blockBound 72 := by
  apply certifyBlock 72 (ds := [
    16, 3, 2, 15, 28, 25, 4, 19, 2, 9, 12, 7, 10, 3, 8, 1, 30, 35, 12, 7, 10, 7, 4, 11, 16,
    15, 58, 45, 16, 17, 10, 37, 20, 15, 4, 13, 22, 3, 50, 1, 22, 7, 58, 1, 26, 7, 4, 13, 10, 9,
    52, 3, 18, 5, 16, 31, 20, 9, 16, 1, 46, 9, 4, 25, 4, 13, 24, 7, 8, 7, 18, 25, 4, 15, 8,
    3, 22, 7, 10, 9, 8, 27, 18, 13, 6, 1, 10, 15, 30, 11, 6, 7, 4, 3, 66, 5, 30, 3, 20, 21])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_73 : blockBound 73 := by
  apply certifyBlock 73 (ds := [
    6, 19, 12, 1, 4, 43, 22, 5, 12, 9, 32, 7, 28, 61, 6, 1, 50, 3, 18, 7, 10, 13, 22, 55, 4,
    1, 4, 15, 58, 7, 16, 7, 4, 15, 22, 33, 4, 19, 28, 7, 2, 39, 18, 23, 42, 15, 4, 15, 18, 11,
    10, 9, 10, 7, 36, 23, 72, 7, 26, 13, 6, 29, 4, 1, 2, 7, 4, 13, 16, 3, 16, 3, 54, 7, 18,
    15, 2, 15, 22, 11, 10, 3, 2, 1, 4, 17, 18, 3, 8, 19, 36, 13, 12, 15, 14, 37, 4, 29, 10, 3])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_74 : blockBound 74 := by
  apply certifyBlock 74 (ds := [
    2, 3, 10, 1, 52, 25, 2, 13, 22, 1, 22, 3, 8, 1, 18, 43, 22, 7, 26, 1, 10, 7, 4, 7, 2,
    15, 22, 7, 30, 13, 2, 19, 10, 1, 46, 37, 2, 15, 12, 7, 6, 7, 14, 31, 22, 11, 4, 39, 28, 7,
    16, 7, 54, 45, 22, 1, 4, 13, 48, 1, 10, 3, 4, 83, 22, 1, 4, 45, 18, 11, 12, 3, 4, 1, 4,
    23, 10, 55, 22, 3, 18, 17, 12, 3, 16, 3, 22, 5, 16, 1, 2, 7, 4, 11, 4, 15, 32, 3, 58, 11])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_75 : blockBound 75 := by
  apply certifyBlock 75 (ds := [
    28, 13, 4, 1, 12, 7, 4, 9, 8, 3, 36, 5, 18, 3, 8, 1, 40, 13, 16, 1, 32, 39, 12, 1, 12,
    3, 4, 15, 18, 13, 16, 9, 8, 13, 46, 1, 34, 39, 2, 9, 6, 7, 34, 57, 16, 61, 4, 19, 18, 1,
    46, 7, 10, 5, 34, 15, 20, 37, 58, 11, 12, 79, 2, 7, 4, 11, 48, 3, 2, 63, 18, 7, 22, 13, 8,
    55, 4, 49, 6, 31, 10, 39, 4, 11, 4, 27, 8, 39, 28, 13, 6, 37, 22, 31, 12, 1, 22, 9, 2, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_76 : blockBound 76 := by
  apply certifyBlock 76 (ds := [
    12, 19, 42, 1, 4, 15, 54, 5, 48, 3, 2, 15, 4, 35, 28, 13, 2, 33, 16, 17, 48, 7, 4, 1, 12,
    23, 4, 15, 2, 13, 10, 35, 18, 7, 2, 57, 10, 5, 46, 13, 2, 19, 4, 41, 28, 33, 20, 25, 46, 7,
    48, 9, 4, 3, 24, 1, 12, 3, 10, 21, 6, 7, 12, 45, 4, 7, 12, 17, 22, 19, 8, 13, 24, 1, 28,
    15, 4, 39, 6, 23, 16, 9, 2, 7, 12, 23, 22, 9, 28, 7, 28, 19, 22, 3, 4, 15, 22, 13, 46, 9])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_77 : blockBound 77 := by
  apply certifyBlock 77 (ds := [
    28, 9, 4, 7, 16, 3, 20, 7, 6, 29, 6, 9, 8, 3, 4, 1, 18, 37, 40, 1, 6, 7, 4, 27, 8,
    37, 10, 25, 12, 7, 16, 13, 4, 1, 12, 7, 2, 7, 90, 13, 30, 15, 8, 1, 34, 25, 28, 7, 16, 33,
    22, 25, 10, 1, 2, 13, 24, 23, 30, 3, 2, 3, 4, 5, 16, 15, 14, 25, 12, 1, 16, 7, 2, 1, 6,
    5, 10, 25, 8, 1, 22, 13, 4, 3, 4, 13, 4, 23, 6, 3, 8, 9, 4, 7, 24, 1, 10, 3, 30, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_78 : blockBound 78 := by
  apply certifyBlock 78 (ds := [
    16, 15, 8, 1, 18, 1, 4, 3, 2, 1, 12, 13, 10, 57, 4, 3, 4, 5, 30, 1, 56, 3, 48, 47, 24,
    45, 14, 33, 36, 11, 6, 49, 2, 15, 16, 1, 42, 79, 10, 3, 16, 19, 4, 3, 2, 15, 12, 5, 18, 3,
    32, 19, 58, 1, 18, 1, 4, 15, 6, 7, 16, 15, 44, 1, 6, 35, 12, 9, 8, 39, 6, 13, 18, 21, 2,
    3, 4, 43, 18, 19, 46, 25, 24, 5, 4, 7, 4, 7, 12, 7, 16, 3, 44, 7, 18, 5, 12, 27, 16, 81])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_79 : blockBound 79 := by
  apply certifyBlock 79 (ds := [
    12, 37, 10, 43, 22, 1, 28, 13, 10, 1, 38, 7, 24, 11, 4, 21, 8, 3, 12, 7, 6, 19, 4, 27, 18,
    5, 34, 27, 16, 3, 40, 5, 48, 7, 2, 51, 4, 29, 12, 39, 8, 7, 12, 1, 64, 1, 14, 3, 76, 19,
    10, 3, 28, 25, 4, 1, 18, 7, 20, 3, 6, 17, 4, 13, 8, 15, 12, 5, 6, 3, 16, 15, 4, 11, 4,
    7, 28, 19, 10, 23, 10, 25, 4, 27, 18, 5, 22, 9, 8, 3, 6, 23, 30, 3, 4, 13, 4, 23, 6, 31])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_80 : blockBound 80 := by
  apply certifyBlock 80 (ds := [
    10, 49, 4, 35, 36, 75, 22, 9, 18, 13, 6, 3, 2, 1, 22, 25, 22, 37, 20, 7, 12, 5, 10, 7, 34,
    15, 4, 17, 6, 1, 26, 45, 30, 1, 78, 15, 2, 19, 16, 7, 30, 7, 34, 7, 4, 35, 10, 13, 10, 37,
    42, 7, 18, 21, 4, 7, 24, 7, 18, 9, 2, 7, 12, 1, 12, 7, 2, 37, 6, 7, 16, 15, 4, 7, 16,
    13, 28, 3, 58, 1, 10, 25, 22, 25, 58, 25, 4, 17, 10, 9, 26, 9, 4, 11, 24, 3, 4, 43, 40, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_81 : blockBound 81 := by
  apply certifyBlock 81 (ds := [
    28, 9, 38, 7, 22, 37, 10, 9, 2, 3, 18, 17, 4, 1, 8, 1, 18, 7, 12, 13, 8, 19, 4, 7, 12,
    3, 52, 9, 18, 13, 28, 27, 4, 27, 54, 7, 10, 3, 22, 51, 6, 25, 18, 7, 4, 21, 4, 5, 36, 13,
    8, 3, 58, 5, 16, 15, 20, 7, 28, 11, 46, 3, 4, 25, 36, 11, 60, 73, 8, 9, 28, 17, 24, 1, 2,
    1, 10, 5, 102, 1, 70, 39, 18, 1, 6, 3, 8, 25, 10, 17, 10, 15, 14, 1, 12, 1, 22, 7, 2, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_82 : blockBound 82 := by
  apply certifyBlock 82 (ds := [
    6, 23, 10, 13, 2, 1, 4, 23, 36, 1, 20, 7, 12, 7, 4, 15, 50, 3, 10, 41, 18, 25, 62, 3, 4,
    1, 12, 27, 46, 1, 10, 5, 4, 37, 4, 7, 22, 17, 6, 7, 16, 7, 42, 11, 12, 3, 28, 37, 6, 13,
    22, 25, 52, 1, 6, 7, 64, 15, 16, 3, 46, 5, 22, 3, 22, 7, 4, 5, 18, 1, 16, 13, 4, 5, 64,
    13, 2, 3, 18, 11, 6, 3, 8, 15, 16, 5, 18, 9, 16, 1, 6, 13, 18, 15, 4, 1, 48, 37, 16, 9])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_83 : blockBound 83 := by
  apply certifyBlock 83 (ds := [
    2, 9, 60, 1, 16, 3, 2, 3, 46, 29, 46, 13, 8, 15, 4, 41, 24, 39, 28, 3, 36, 17, 10, 1, 4,
    31, 24, 7, 12, 27, 26, 9, 18, 31, 36, 25, 8, 9, 6, 13, 30, 55, 2, 13, 36, 61, 10, 39, 2, 1,
    6, 5, 4, 13, 14, 15, 40, 19, 42, 7, 2, 3, 18, 37, 4, 73, 2, 9, 36, 13, 18, 9, 14, 7, 18,
    1, 54, 7, 10, 3, 6, 23, 18, 27, 14, 1, 10, 29, 16, 37, 20, 9, 54, 11, 12, 21, 8, 9, 10, 11])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_84 : blockBound 84 := by
  apply certifyBlock 84 (ds := [
    22, 13, 34, 7, 22, 5, 18, 3, 2, 7, 10, 5, 52, 3, 26, 13, 28, 7, 12, 1, 2, 3, 22, 1, 4,
    7, 2, 9, 10, 7, 6, 37, 4, 1, 24, 11, 58, 7, 20, 7, 18, 13, 12, 25, 8, 3, 28, 7, 6, 19,
    8, 13, 22, 1, 12, 15, 10, 7, 18, 29, 12, 3, 2, 3, 6, 7, 22, 19, 2, 19, 12, 89, 52, 7, 14,
    21, 22, 25, 12, 7, 16, 9, 10, 31, 16, 21, 10, 3, 16, 11, 16, 3, 4, 13, 4, 7, 4, 9, 26, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_85 : blockBound 85 := by
  apply certifyBlock 85 (ds := [
    22, 7, 84, 3, 2, 25, 4, 17, 6, 13, 26, 3, 12, 67, 4, 27, 14, 3, 6, 29, 12, 7, 2, 7, 24,
    5, 4, 37, 10, 3, 18, 35, 4, 61, 2, 21, 4, 47, 16, 1, 22, 7, 10, 7, 6, 7, 2, 7, 12, 1,
    10, 37, 32, 1, 4, 5, 18, 7, 2, 37, 10, 23, 12, 67, 52, 7, 24, 53, 42, 19, 20, 3, 4, 5, 34,
    1, 8, 25, 6, 37, 22, 3, 8, 1, 22, 13, 22, 15, 2, 7, 6, 7, 22, 61, 14, 13, 4, 5, 22, 57])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_86 : blockBound 86 := by
  apply certifyBlock 86 (ds := [
    26, 3, 12, 11, 28, 21, 2, 7, 16, 1, 30, 27, 4, 7, 28, 47, 4, 7, 2, 3, 16, 5, 12, 31, 4,
    1, 10, 13, 12, 7, 2, 3, 22, 1, 24, 15, 8, 9, 18, 7, 6, 7, 8, 45, 12, 5, 40, 13, 20, 7,
    10, 17, 4, 15, 2, 1, 4, 17, 6, 21, 8, 9, 22, 13, 12, 3, 22, 75, 6, 1, 6, 7, 4, 21, 34,
    23, 28, 19, 8, 1, 12, 29, 10, 1, 2, 3, 12, 19, 6, 21, 2, 13, 4, 1, 16, 33, 4, 9, 6, 23])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_87 : blockBound 87 := by
  apply certifyBlock 87 (ds := [
    16, 7, 8, 21, 22, 1, 10, 3, 10, 21, 6, 23, 18, 21, 8, 67, 12, 17, 48, 1, 2, 19, 24, 7, 6,
    3, 4, 3, 36, 7, 6, 3, 2, 7, 16, 85, 4, 13, 28, 3, 12, 17, 24, 45, 28, 3, 28, 7, 12, 1,
    10, 15, 22, 17, 4, 7, 20, 3, 22, 1, 18, 15, 8, 3, 12, 5, 28, 7, 22, 19, 12, 5, 28, 1, 4,
    13, 24, 13, 22, 19, 20, 25, 12, 1, 12, 1, 2, 7, 16, 1, 10, 9, 2, 15, 4, 23, 12, 3, 8, 43])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_88 : blockBound 88 := by
  apply certifyBlock 88 (ds := [
    58, 23, 64, 7, 28, 3, 10, 5, 10, 7, 2, 39, 22, 7, 16, 1, 2, 27, 12, 11, 12, 19, 2, 21, 12,
    23, 4, 15, 8, 3, 30, 47, 52, 27, 4, 15, 10, 17, 82, 9, 32, 33, 18, 7, 4, 1, 10, 9, 12, 13,
    36, 45, 2, 1, 24, 5, 28, 7, 2, 9, 12, 19, 10, 13, 2, 3, 58, 25, 16, 21, 26, 9, 4, 5, 22,
    1, 2, 37, 28, 1, 16, 39, 2, 7, 4, 13, 28, 13, 2, 3, 10, 29, 10, 1, 8, 7, 34, 5, 76, 3])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_89 : blockBound 89 := by
  apply certifyBlock 89 (ds := [
    8, 9, 4, 17, 12, 7, 8, 9, 12, 29, 12, 15, 4, 27, 18, 43, 18, 3, 16, 27, 10, 7, 4, 51, 2,
    15, 18, 29, 10, 21, 8, 9, 18, 11, 18, 7, 2, 49, 10, 1, 28, 73, 4, 7, 24, 11, 12, 39, 10, 13,
    18, 43, 4, 45, 14, 15, 10, 5, 70, 3, 2, 7, 22, 1, 12, 31, 32, 3, 40, 11, 6, 13, 22, 1, 4,
    1, 30, 25, 16, 3, 10, 35, 18, 3, 8, 61, 4, 55, 22, 39, 16, 3, 28, 7, 48, 1, 20, 3, 18, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_90 : blockBound 90 := by
  apply certifyBlock 90 (ds := [
    12, 15, 22, 13, 16, 7, 12, 19, 40, 1, 30, 55, 52, 7, 4, 1, 10, 79, 16, 1, 8, 19, 4, 1, 6,
    3, 2, 7, 28, 29, 12, 13, 14, 3, 42, 11, 34, 7, 16, 9, 18, 7, 22, 27, 8, 1, 4, 17, 18, 7,
    16, 7, 42, 1, 4, 7, 8, 3, 12, 11, 18, 9, 4, 7, 6, 5, 12, 15, 16, 7, 16, 5, 4, 15, 4,
    7, 12, 19, 12, 31, 2, 87, 4, 5, 4, 13, 14, 43, 6, 7, 22, 9, 8, 15, 4, 11, 34, 7, 16, 19])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_91 : blockBound 91 := by
  apply certifyBlock 91 (ds := [
    16, 7, 22, 13, 26, 43, 4, 7, 28, 3, 20, 9, 18, 5, 4, 7, 2, 7, 30, 1, 6, 3, 2, 1, 22,
    1, 28, 3, 8, 7, 16, 13, 4, 15, 16, 7, 18, 7, 16, 13, 2, 19, 24, 7, 22, 13, 2, 9, 10, 11,
    6, 7, 4, 1, 12, 41, 4, 13, 8, 7, 28, 19, 40, 1, 16, 7, 34, 7, 22, 3, 8, 9, 24, 25, 16,
    3, 22, 73, 18, 1, 58, 9, 28, 31, 24, 25, 4, 9, 20, 3, 10, 19, 30, 3, 14, 15, 12, 13, 36, 27])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_92 : blockBound 92 := by
  apply certifyBlock 92 (ds := [
    10, 13, 4, 1, 22, 3, 8, 9, 6, 7, 36, 15, 4, 1, 58, 101, 40, 43, 40, 3, 16, 25, 10, 7, 2,
    3, 12, 5, 6, 9, 2, 19, 10, 5, 12, 13, 4, 43, 28, 1, 12, 9, 8, 3, 4, 1, 4, 3, 46, 69,
    6, 7, 10, 25, 22, 25, 34, 23, 18, 1, 26, 7, 12, 13, 28, 1, 4, 27, 30, 1, 28, 7, 14, 7, 6,
    1, 12, 3, 62, 1, 18, 19, 4, 43, 16, 15, 12, 35, 10, 33, 2, 3, 4, 1, 12, 3, 8, 7, 22, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_93 : blockBound 93 := by
  apply certifyBlock 93 (ds := [
    6, 7, 4, 3, 28, 7, 22, 19, 40, 1, 12, 5, 58, 1, 8, 3, 4, 29, 60, 31, 22, 7, 4, 1, 16,
    15, 20, 7, 42, 19, 6, 7, 14, 3, 18, 1, 60, 25, 2, 1, 28, 43, 12, 21, 16, 3, 12, 17, 30, 19,
    2, 15, 4, 7, 16, 1, 20, 43, 36, 17, 16, 7, 10, 21, 12, 17, 4, 9, 8, 13, 28, 5, 48, 1, 32,
    3, 4, 5, 10, 19, 2, 9, 18, 7, 4, 1, 2, 33, 6, 43, 30, 15, 2, 3, 12, 35, 10, 49, 16, 31])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_94 : blockBound 94 := by
  apply certifyBlock 94 (ds := [
    16, 7, 4, 55, 8, 1, 10, 47, 16, 33, 10, 3, 18, 17, 6, 7, 22, 15, 28, 11, 16, 13, 8, 1, 34,
    1, 12, 7, 8, 31, 70, 7, 24, 1, 26, 1, 82, 7, 46, 3, 16, 3, 18, 7, 4, 3, 8, 7, 18, 17,
    36, 9, 62, 3, 12, 11, 4, 9, 8, 1, 6, 5, 4, 3, 2, 13, 10, 25, 6, 9, 20, 9, 4, 1, 36,
    1, 2, 9, 12, 23, 18, 7, 4, 25, 6, 1, 12, 25, 52, 7, 36, 17, 24, 1, 8, 7, 30, 5, 12, 7])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_95 : blockBound 95 := by
  apply certifyBlock 95 (ds := [
    8, 39, 18, 7, 4, 31, 32, 19, 22, 11, 18, 25, 20, 7, 4, 11, 28, 15, 32, 1, 12, 19, 10, 15, 44,
    21, 34, 23, 16, 1, 56, 7, 42, 5, 12, 93, 2, 7, 16, 11, 22, 75, 4, 3, 6, 1, 60, 25, 8, 9,
    6, 37, 18, 1, 2, 3, 4, 13, 6, 37, 10, 37, 10, 1, 6, 15, 4, 33, 18, 23, 6, 15, 4, 7, 28,
    11, 4, 33, 8, 7, 12, 5, 4, 63, 2, 3, 10, 13, 10, 9, 16, 7, 4, 17, 16, 1, 2, 7, 36, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_96 : blockBound 96 := by
  apply certifyBlock 96 (ds := [
    6, 13, 38, 13, 4, 11, 34, 3, 40, 21, 12, 17, 34, 13, 62, 27, 12, 5, 10, 9, 10, 3, 22, 5, 6,
    31, 8, 7, 18, 1, 16, 55, 8, 85, 24, 7, 4, 3, 10, 21, 16, 43, 64, 15, 2, 3, 40, 5, 6, 1,
    2, 9, 24, 5, 28, 21, 4, 9, 12, 13, 12, 13, 4, 31, 18, 1, 12, 25, 8, 1, 6, 19, 10, 15, 2,
    21, 28, 17, 18, 7, 20, 3, 4, 7, 4, 7, 4, 55, 42, 11, 6, 25, 32, 87, 16, 1, 18, 7, 8, 21])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_97 : blockBound 97 := by
  apply certifyBlock 97 (ds := [
    16, 25, 12, 15, 28, 3, 4, 23, 10, 19, 2, 3, 4, 1, 16, 3, 4, 7, 6, 29, 6, 15, 2, 1, 4,
    11, 28, 9, 2, 39, 18, 7, 22, 15, 28, 33, 4, 5, 18, 9, 28, 9, 10, 1, 16, 27, 8, 25, 18, 7,
    46, 25, 14, 15, 6, 5, 4, 19, 2, 1, 16, 23, 18, 7, 4, 31, 48, 13, 6, 1, 38, 27, 18, 7, 4,
    27, 14, 3, 90, 17, 46, 9, 2, 13, 4, 1, 28, 13, 2, 21, 30, 5, 18, 15, 2, 7, 52, 5, 12, 31])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_98 : blockBound 98 := by
  apply certifyBlock 98 (ds := [
    2, 37, 4, 1, 16, 1, 20, 7, 22, 13, 16, 7, 4, 3, 16, 11, 10, 15, 8, 7, 10, 23, 34, 51, 38,
    1, 4, 17, 10, 13, 16, 3, 4, 37, 6, 3, 4, 7, 16, 29, 10, 27, 28, 1, 18, 13, 28, 15, 2, 37,
    18, 7, 18, 25, 8, 25, 18, 43, 48, 1, 26, 3, 12, 5, 28, 63, 10, 7, 10, 31, 16, 33, 14, 1, 4,
    1, 18, 19, 2, 1, 16, 19, 24, 25, 2, 51, 4, 7, 16, 3, 2, 3, 4, 1, 36, 1, 4, 13, 18, 1])
  · rfl
  · decide +kernel

set_option maxRecDepth 20000 in
theorem block_99 : blockBound 99 := by
  apply certifyBlock 99 (ds := [
    16, 3, 20, 1, 6, 5, 42, 7, 8, 13, 10, 19, 72, 37, 16, 13, 12, 5, 12, 19, 26, 9, 34, 41, 4,
    27, 2, 7, 18, 7, 16, 15, 4, 3, 76, 25, 10, 7, 46, 13, 40, 19, 4, 3, 8, 21, 10, 23, 6, 3,
    46, 9, 12, 37, 16, 1, 14, 3, 18, 89, 12, 25, 4, 25, 22, 7, 18, 3, 16, 1, 6, 17, 18, 45, 4,
    3, 4, 35, 6, 1, 46, 3, 4, 25, 16, 1, 2, 3, 16, 1, 6, 3, 58, 15, 4, 5, 4, 7, 2, 7])
  · rfl
  · decide +kernel

lemma extend_bound {P : ℕ → Prop} (n : ℕ) (earlier : ∀ i < n, P i) (last : P n) :
    ∀ i < n+1, P i := by
  intro i hi
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
  · exact earlier i h
  · exact last

theorem batches (b : Fin 100) : blockBound b.val := by
  have prefix0 : ∀ i < 0, blockBound i := fun i hi => (Nat.not_lt_zero i hi).elim
  have prefix1 := extend_bound (P := fun i => blockBound i) 0 prefix0 block_00
  have prefix2 := extend_bound (P := fun i => blockBound i) 1 prefix1 block_01
  have prefix3 := extend_bound (P := fun i => blockBound i) 2 prefix2 block_02
  have prefix4 := extend_bound (P := fun i => blockBound i) 3 prefix3 block_03
  have prefix5 := extend_bound (P := fun i => blockBound i) 4 prefix4 block_04
  have prefix6 := extend_bound (P := fun i => blockBound i) 5 prefix5 block_05
  have prefix7 := extend_bound (P := fun i => blockBound i) 6 prefix6 block_06
  have prefix8 := extend_bound (P := fun i => blockBound i) 7 prefix7 block_07
  have prefix9 := extend_bound (P := fun i => blockBound i) 8 prefix8 block_08
  have prefix10 := extend_bound (P := fun i => blockBound i) 9 prefix9 block_09
  have prefix11 := extend_bound (P := fun i => blockBound i) 10 prefix10 block_10
  have prefix12 := extend_bound (P := fun i => blockBound i) 11 prefix11 block_11
  have prefix13 := extend_bound (P := fun i => blockBound i) 12 prefix12 block_12
  have prefix14 := extend_bound (P := fun i => blockBound i) 13 prefix13 block_13
  have prefix15 := extend_bound (P := fun i => blockBound i) 14 prefix14 block_14
  have prefix16 := extend_bound (P := fun i => blockBound i) 15 prefix15 block_15
  have prefix17 := extend_bound (P := fun i => blockBound i) 16 prefix16 block_16
  have prefix18 := extend_bound (P := fun i => blockBound i) 17 prefix17 block_17
  have prefix19 := extend_bound (P := fun i => blockBound i) 18 prefix18 block_18
  have prefix20 := extend_bound (P := fun i => blockBound i) 19 prefix19 block_19
  have prefix21 := extend_bound (P := fun i => blockBound i) 20 prefix20 block_20
  have prefix22 := extend_bound (P := fun i => blockBound i) 21 prefix21 block_21
  have prefix23 := extend_bound (P := fun i => blockBound i) 22 prefix22 block_22
  have prefix24 := extend_bound (P := fun i => blockBound i) 23 prefix23 block_23
  have prefix25 := extend_bound (P := fun i => blockBound i) 24 prefix24 block_24
  have prefix26 := extend_bound (P := fun i => blockBound i) 25 prefix25 block_25
  have prefix27 := extend_bound (P := fun i => blockBound i) 26 prefix26 block_26
  have prefix28 := extend_bound (P := fun i => blockBound i) 27 prefix27 block_27
  have prefix29 := extend_bound (P := fun i => blockBound i) 28 prefix28 block_28
  have prefix30 := extend_bound (P := fun i => blockBound i) 29 prefix29 block_29
  have prefix31 := extend_bound (P := fun i => blockBound i) 30 prefix30 block_30
  have prefix32 := extend_bound (P := fun i => blockBound i) 31 prefix31 block_31
  have prefix33 := extend_bound (P := fun i => blockBound i) 32 prefix32 block_32
  have prefix34 := extend_bound (P := fun i => blockBound i) 33 prefix33 block_33
  have prefix35 := extend_bound (P := fun i => blockBound i) 34 prefix34 block_34
  have prefix36 := extend_bound (P := fun i => blockBound i) 35 prefix35 block_35
  have prefix37 := extend_bound (P := fun i => blockBound i) 36 prefix36 block_36
  have prefix38 := extend_bound (P := fun i => blockBound i) 37 prefix37 block_37
  have prefix39 := extend_bound (P := fun i => blockBound i) 38 prefix38 block_38
  have prefix40 := extend_bound (P := fun i => blockBound i) 39 prefix39 block_39
  have prefix41 := extend_bound (P := fun i => blockBound i) 40 prefix40 block_40
  have prefix42 := extend_bound (P := fun i => blockBound i) 41 prefix41 block_41
  have prefix43 := extend_bound (P := fun i => blockBound i) 42 prefix42 block_42
  have prefix44 := extend_bound (P := fun i => blockBound i) 43 prefix43 block_43
  have prefix45 := extend_bound (P := fun i => blockBound i) 44 prefix44 block_44
  have prefix46 := extend_bound (P := fun i => blockBound i) 45 prefix45 block_45
  have prefix47 := extend_bound (P := fun i => blockBound i) 46 prefix46 block_46
  have prefix48 := extend_bound (P := fun i => blockBound i) 47 prefix47 block_47
  have prefix49 := extend_bound (P := fun i => blockBound i) 48 prefix48 block_48
  have prefix50 := extend_bound (P := fun i => blockBound i) 49 prefix49 block_49
  have prefix51 := extend_bound (P := fun i => blockBound i) 50 prefix50 block_50
  have prefix52 := extend_bound (P := fun i => blockBound i) 51 prefix51 block_51
  have prefix53 := extend_bound (P := fun i => blockBound i) 52 prefix52 block_52
  have prefix54 := extend_bound (P := fun i => blockBound i) 53 prefix53 block_53
  have prefix55 := extend_bound (P := fun i => blockBound i) 54 prefix54 block_54
  have prefix56 := extend_bound (P := fun i => blockBound i) 55 prefix55 block_55
  have prefix57 := extend_bound (P := fun i => blockBound i) 56 prefix56 block_56
  have prefix58 := extend_bound (P := fun i => blockBound i) 57 prefix57 block_57
  have prefix59 := extend_bound (P := fun i => blockBound i) 58 prefix58 block_58
  have prefix60 := extend_bound (P := fun i => blockBound i) 59 prefix59 block_59
  have prefix61 := extend_bound (P := fun i => blockBound i) 60 prefix60 block_60
  have prefix62 := extend_bound (P := fun i => blockBound i) 61 prefix61 block_61
  have prefix63 := extend_bound (P := fun i => blockBound i) 62 prefix62 block_62
  have prefix64 := extend_bound (P := fun i => blockBound i) 63 prefix63 block_63
  have prefix65 := extend_bound (P := fun i => blockBound i) 64 prefix64 block_64
  have prefix66 := extend_bound (P := fun i => blockBound i) 65 prefix65 block_65
  have prefix67 := extend_bound (P := fun i => blockBound i) 66 prefix66 block_66
  have prefix68 := extend_bound (P := fun i => blockBound i) 67 prefix67 block_67
  have prefix69 := extend_bound (P := fun i => blockBound i) 68 prefix68 block_68
  have prefix70 := extend_bound (P := fun i => blockBound i) 69 prefix69 block_69
  have prefix71 := extend_bound (P := fun i => blockBound i) 70 prefix70 block_70
  have prefix72 := extend_bound (P := fun i => blockBound i) 71 prefix71 block_71
  have prefix73 := extend_bound (P := fun i => blockBound i) 72 prefix72 block_72
  have prefix74 := extend_bound (P := fun i => blockBound i) 73 prefix73 block_73
  have prefix75 := extend_bound (P := fun i => blockBound i) 74 prefix74 block_74
  have prefix76 := extend_bound (P := fun i => blockBound i) 75 prefix75 block_75
  have prefix77 := extend_bound (P := fun i => blockBound i) 76 prefix76 block_76
  have prefix78 := extend_bound (P := fun i => blockBound i) 77 prefix77 block_77
  have prefix79 := extend_bound (P := fun i => blockBound i) 78 prefix78 block_78
  have prefix80 := extend_bound (P := fun i => blockBound i) 79 prefix79 block_79
  have prefix81 := extend_bound (P := fun i => blockBound i) 80 prefix80 block_80
  have prefix82 := extend_bound (P := fun i => blockBound i) 81 prefix81 block_81
  have prefix83 := extend_bound (P := fun i => blockBound i) 82 prefix82 block_82
  have prefix84 := extend_bound (P := fun i => blockBound i) 83 prefix83 block_83
  have prefix85 := extend_bound (P := fun i => blockBound i) 84 prefix84 block_84
  have prefix86 := extend_bound (P := fun i => blockBound i) 85 prefix85 block_85
  have prefix87 := extend_bound (P := fun i => blockBound i) 86 prefix86 block_86
  have prefix88 := extend_bound (P := fun i => blockBound i) 87 prefix87 block_87
  have prefix89 := extend_bound (P := fun i => blockBound i) 88 prefix88 block_88
  have prefix90 := extend_bound (P := fun i => blockBound i) 89 prefix89 block_89
  have prefix91 := extend_bound (P := fun i => blockBound i) 90 prefix90 block_90
  have prefix92 := extend_bound (P := fun i => blockBound i) 91 prefix91 block_91
  have prefix93 := extend_bound (P := fun i => blockBound i) 92 prefix92 block_92
  have prefix94 := extend_bound (P := fun i => blockBound i) 93 prefix93 block_93
  have prefix95 := extend_bound (P := fun i => blockBound i) 94 prefix94 block_94
  have prefix96 := extend_bound (P := fun i => blockBound i) 95 prefix95 block_95
  have prefix97 := extend_bound (P := fun i => blockBound i) 96 prefix96 block_96
  have prefix98 := extend_bound (P := fun i => blockBound i) 97 prefix97 block_97
  have prefix99 := extend_bound (P := fun i => blockBound i) 98 prefix98 block_98
  have prefix100 := extend_bound (P := fun i => blockBound i) 99 prefix99 block_99
  exact prefix100 b.val b.isLt

theorem gap_bound (n d : ℕ) (hn : n ≤ 10000) (h : check n d = true) : OeisA53000.a n ≤ 1 + n.totient := by
  unfold check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨pos, bound⟩, hp⟩, ht⟩ := h
  have prime := primeCheck_sound (n^2 + d) bound hp
  have tot := totientCheck_sound n d hn ht
  have le : sInf {p : ℕ | Nat.Prime p ∧ n^2 < p} ≤ n^2 + d :=
    Nat.sInf_le ⟨prime, by omega⟩
  unfold OeisA53000.a
  omega

end SquarePrimeGap

theorem OMA.solution : OMA.R_OeisA53000_conjecture_R1.H1 := by
  intro n hn hi
  let b : Fin 100 := ⟨(n-1)/100, by omega⟩
  obtain ⟨d, pass⟩ := SquarePrimeGap.batches b n (by dsimp [b]; omega) (by dsimp [b]; omega)
  exact SquarePrimeGap.gap_bound n d hi pass
