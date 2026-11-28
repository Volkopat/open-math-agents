import OMAReductions.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H1_R1
import Mathlib

/-!
# Crossing masks for the rooted Ramsey(4,4,16) gluing

Read the 56 crossing edges in row-major order. Avoiding monochromatic
four-sets rules out 25 block pairs. The two remaining pairs each have 32
candidate masks. The four numerical census obligations below isolate the
exhaustion step. All 64 permutations from these masks to the two graph
words are checked in this file. Permutations are packed in four-bit digits.
-/

open Finset SimpleGraph
namespace OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H1_R1_H2_R2

def H1 : Prop :=
  ∀ a ∈ ([480904,944196,944204,483585] : List ℕ), ∀ b ∈ ([153315680,206327905,60117131] : List ℕ),
    (a≠480904 ∨ b≠60117131) → ∀ key : Fin (2^56),
  let E (i j : Fin 16) : Bool :=
    let u := i.val
    let v := j.val
    if v=15 then decide (u<7)
    else if v<7 then a.testBit (v*(v-1)/2+u)
    else if u<7 then key.val.testBit (8*u+(v-7))
    else !(b.testBit ((v-7)*(v-8)/2+(u-7)))
  (∀ i j k l : Fin 16, i<j → j<k → k<l →
      ¬(E i j = E i k ∧ E i j = E i l ∧ E i j = E j k ∧
        E i j = E j l ∧ E i j = E k l)) → False

def H2 : Prop :=
  ∀ a ∈ ([746529,1581345,666115,1714691,946323] : List ℕ), ∀ b ∈ ([153315680,206327905,60117131] : List ℕ),
    (a≠946323 ∨ b≠153315680) → ∀ key : Fin (2^56),
  let E (i j : Fin 16) : Bool :=
    let u := i.val
    let v := j.val
    if v=15 then decide (u<7)
    else if v<7 then a.testBit (v*(v-1)/2+u)
    else if u<7 then key.val.testBit (8*u+(v-7))
    else !(b.testBit ((v-7)*(v-8)/2+(u-7)))
  (∀ i j k l : Fin 16, i<j → j<k → k<l →
      ¬(E i j = E i k ∧ E i j = E i l ∧ E i j = E j k ∧
        E i j = E j l ∧ E i j = E k l)) → False

def H3 : Prop :=
  ∀ key : Fin (2^56),
  let E (i j : Fin 16) : Bool :=
    let u := i.val
    let v := j.val
    if v=15 then decide (u<7)
    else if v<7 then (480904 : ℕ).testBit (v*(v-1)/2+u)
    else if u<7 then key.val.testBit (8*u+(v-7))
    else !((60117131 : ℕ).testBit ((v-7)*(v-8)/2+(u-7)))
  (∀ i j k l : Fin 16, i<j → j<k → k<l →
      ¬(E i j = E i k ∧ E i j = E i l ∧ E i j = E j k ∧
        E i j = E j l ∧ E i j = E k l)) → key.val ∈ ([51907286058939675,15034500931565595,33945870567879469,14524317875730477,43198594614439219,12799184136870195,29758086361914165,7803012962740533,64399053931714119,42443864117208135,57651910428624742,38230810462768230,51821665785623913,14948764242917481,43122054871264632,12723097119988088,59334496917939847,28935539166663303,57108829795010454,20235928252304022,33826783575159705,14405683609303193,29613729920719800,7658540106213816,64254581075187402,42299507676013770,59258409901057740,28858999423488716,57533276162197458,38111723470048466,57023093106362340,20150307978988260] : List ℕ)

def H4 : Prop :=
  ∀ key : Fin (2^56),
  let E (i j : Fin 16) : Bool :=
    let u := i.val
    let v := j.val
    if v=15 then decide (u<7)
    else if v<7 then (946323 : ℕ).testBit (v*(v-1)/2+u)
    else if u<7 then key.val.testBit (8*u+(v-7))
    else !((153315680 : ℕ).testBit ((v-7)*(v-8)/2+(u-7)))
  (∀ i j k l : Fin 16, i<j → j<k → k<l →
      ¬(E i j = E i k ∧ E i j = E i l ∧ E i j = E j k ∧
        E i j = E j l ∧ E i j = E k l)) → key.val ∈ ([55637857725330672,48067720168092912,55637733657818352,48067596100580592,56952130552215792,24148201137518832,56951638560356592,24147709145659632,38937731506388208,24077831856995568,47926982411566320,19609060438195440,47926789893012720,19608867919641840,38937102612446448,24077202963053808,47629513705178352,15386335220647152,47629013156938992,15385834672407792,24270369124042992,16139480636639472,24270253612910832,16139365125507312,24252659279908080,11635763351178480,47594054455446768,6378861088263408,47593827711372528,6378634344189168,24252227182710000,11635331253980400] : List ℕ)

theorem crossing (G : SimpleGraph (Fin 16)) :
    ∃ key : Fin (2^56), ∀ i : Fin 7, ∀ j : Fin 8,
      G.Adj ((fun (i : Fin 7) => (Fin.castAdd 8 i).castSucc) i) ((fun (j : Fin 8) => (Fin.natAdd 7 j).castSucc) j) ↔ key.val.testBit (8*i.val+j.val) = true := by
  classical
  let f (q : Fin 56) : Bool := decide (G.Adj
    ((fun (i : Fin 7) => (Fin.castAdd 8 i).castSucc) ⟨q.val / 8, by have := q.isLt; omega⟩) ((fun (j : Fin 8) => (Fin.natAdd 7 j).castSucc) ⟨q.val % 8, Nat.mod_lt _ (by decide)⟩))
  let vec := BitVec.ofBoolListLE (List.ofFn f)
  let key : Fin (2^56) := ⟨vec.toNat, by simpa [vec] using vec.isLt⟩
  have hb (q : Fin 56) : key.val.testBit q.val = f q := by
    change (BitVec.ofBoolListLE (List.ofFn f)).getLsbD q.val = _
    rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
    simp only [List.getElem?_ofFn, dif_pos q.isLt, Option.getD_some]
  refine ⟨key,?_⟩
  intro i j
  let q : Fin 56 := ⟨8*i.val+j.val, by have := i.isLt; have := j.isLt; omega⟩
  change _ ↔ key.val.testBit q.val = true
  rw [hb]
  have hl : (⟨q.val / 8, by have := q.isLt; omega⟩ : Fin 7) = i := by
    apply Fin.ext; change (8*i.val+j.val)/8 = i.val; have := j.isLt; omega
  have hr : (⟨q.val % 8, Nat.mod_lt _ (by decide)⟩ : Fin 8) = j := by
    apply Fin.ext; change (8*i.val+j.val)%8 = j.val; have := j.isLt; omega
  unfold f
  rw [hl,hr,decide_eq_true_eq]

theorem full_rep {G : SimpleGraph (Fin 16)} {a b key : ℕ}
    (pivot : ∀ i : Fin 16, G.Adj (Fin.last 15) i ↔ i.val < 7)
    (left : ∀ i j : Fin 7, i < j → (G.Adj ((fun (i : Fin 7) => (Fin.castAdd 8 i).castSucc) i) ((fun (i : Fin 7) => (Fin.castAdd 8 i).castSucc) j) ↔ a.testBit (j.val*(j.val-1)/2+i.val) = true))
    (right : ∀ i j : Fin 8, i < j → (Gᶜ.Adj ((fun (j : Fin 8) => (Fin.natAdd 7 j).castSucc) i) ((fun (j : Fin 8) => (Fin.natAdd 7 j).castSucc) j) ↔ b.testBit (j.val*(j.val-1)/2+i.val) = true))
    (cross : ∀ i : Fin 7, ∀ j : Fin 8, G.Adj ((fun (i : Fin 7) => (Fin.castAdd 8 i).castSucc) i) ((fun (j : Fin 8) => (Fin.natAdd 7 j).castSucc) j) ↔ key.testBit (8*i.val+j.val) = true) :
  let raw (a b key u v : ℕ) : Bool :=
    if v = 15 then decide (u < 7)
    else if v < 7 then a.testBit (v*(v-1)/2+u)
    else if u < 7 then key.testBit (8*u+(v-7))
    else !(b.testBit ((v-7)*(v-8)/2+(u-7)))
  let full (a b key u v : ℕ) : Bool :=
    (u != v) && raw a b key (min u v) (max u v)
    ∀ i j : Fin 16, G.Adj i j ↔ full a b key i.val j.val = true := by
  intro raw full
  have ordered (u v : Fin 16) (huv : u<v) : G.Adj u v ↔ raw a b key u.val v.val = true := by
    have uv : u.val < v.val := huv
    by_cases hp : v.val=15
    · have hv : v=Fin.last 15 := Fin.ext hp
      rw [hv, G.adj_comm, pivot]
      simp [raw]
    by_cases hv : v.val<7
    · let i : Fin 7 := ⟨u.val,by omega⟩
      let j : Fin 7 := ⟨v.val,hv⟩
      have hi : (fun (i : Fin 7) => (Fin.castAdd 8 i).castSucc) i=u := Fin.ext rfl
      have hj : (fun (i : Fin 7) => (Fin.castAdd 8 i).castSucc) j=v := Fin.ext rfl
      have hc := left i j huv
      rw [hi,hj] at hc
      simpa [raw,hp,hv,i,j] using hc
    by_cases hu : u.val<7
    · let i : Fin 7 := ⟨u.val,hu⟩
      let j : Fin 8 := ⟨v.val-7,by have := v.isLt; omega⟩
      have hj : (fun (j : Fin 8) => (Fin.natAdd 7 j).castSucc) j=v := by apply Fin.ext; change 7+(v.val-7)=v.val; omega
      have hi : (fun (i : Fin 7) => (Fin.castAdd 8 i).castSucc) i=u := Fin.ext rfl
      have hc := cross i j
      rw [hi,hj] at hc
      simpa [raw,hp,hv,hu,i,j] using hc
    · let i : Fin 8 := ⟨u.val-7,by have := v.isLt; omega⟩
      let j : Fin 8 := ⟨v.val-7,by have := v.isLt; omega⟩
      have hi : (fun (j : Fin 8) => (Fin.natAdd 7 j).castSucc) i=u := by apply Fin.ext; change 7+(u.val-7)=u.val; omega
      have hj : (fun (j : Fin 8) => (Fin.natAdd 7 j).castSucc) j=v := by apply Fin.ext; change 7+(v.val-7)=v.val; omega
      have hij : i<j := by change u.val-7<v.val-7; omega
      have hblue := right i j hij
      rw [hi,hj,G.compl_adj] at hblue
      have hne : u≠v := ne_of_lt huv
      have hnblue : ¬ G.Adj u v ↔ b.testBit (j.val*(j.val-1)/2+i.val) = true :=
        ⟨fun h => hblue.mp ⟨hne,h⟩,fun h => (hblue.mpr h).2⟩
      simp only [raw, if_neg hp,if_neg hv,if_neg hu,Bool.not_eq_true']
      change (¬G.Adj u v ↔ b.testBit ((v.val-7)*((v.val-7)-1)/2+(u.val-7)) = true) at hnblue
      have he : v.val-7-1=v.val-8 := by omega
      rw [he] at hnblue
      cases h : b.testBit ((v.val-7)*(v.val-8)/2+(u.val-7)) <;> simp_all only [Bool.false_eq_true,iff_true,iff_false,not_not,Bool.true_eq_false]
  intro u v
  rcases lt_trichotomy u v with h | rfl | h
  · have hh : u.val<v.val := h
    simpa [full,ne_of_lt hh,min_eq_left hh.le,max_eq_right hh.le] using ordered u v h
  · simp [full]
  · have hh : v.val<u.val := h
    rw [G.adj_comm]
    simpa [full,ne_of_gt hh,min_eq_right hh.le,max_eq_left hh.le] using ordered v u h

theorem forbidden {V : Type*} [DecidableEq V] {G : SimpleGraph V} {k : ℕ}
    (hG : G.CliqueFree k) (f : Fin k → V)
    (h : ∀ i j, i ≠ j → f i ≠ f j ∧ G.Adj (f i) (f j)) : False := by
  have inj : Function.Injective f := by
    intro i j he
    by_contra hn
    exact (h i j hn).1 he
  apply hG (univ.image f)
  refine ⟨?_, by simp [card_image_of_injective _ inj]⟩
  intro x hx y hy hxy
  obtain ⟨i,_,rfl⟩ := mem_image.mp hx
  obtain ⟨j,_,rfl⟩ := mem_image.mp hy
  exact (h i j (fun he => hxy (congrArg f he))).2


theorem forbidden_four {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    (hG : G.CliqueFree 4) {a b c d : V}
    (ab : G.Adj a b) (ac : G.Adj a c) (ad : G.Adj a d)
    (bc : G.Adj b c) (bd : G.Adj b d) (cd : G.Adj c d) : False := by
  apply forbidden hG ![a,b,c,d]
  intro i j hij
  suffices h : G.Adj (![a,b,c,d] i) (![a,b,c,d] j) from ⟨h.ne,h⟩
  fin_cases i <;> fin_cases j <;> simp_all [SimpleGraph.adj_comm]

theorem no_mono {G : SimpleGraph (Fin 16)} (hG : G.CliqueFree 4) (hC : Gᶜ.CliqueFree 4)
    (E : Fin 16 → Fin 16 → Bool) (raw_ok : ∀ i j, i<j → (G.Adj i j ↔ E i j=true)) :
    ∀ i j k l : Fin 16, i<j → j<k → k<l →
    ¬(E i j = E i k ∧ E i j = E i l ∧ E i j = E j k ∧
      E i j = E j l ∧ E i j = E k l) := by
  intro i j k l hij hjk hkl
  rintro ⟨hik,hil,hjk',hjl,hkl'⟩
  have hred (x y : Fin 16) (h : x<y) (hc : E x y=true) := (raw_ok x y h).mpr hc
  have hblue (x y : Fin 16) (h : x<y) (hc : E x y=false) : Gᶜ.Adj x y := by
    refine (G.compl_adj x y).mpr ⟨ne_of_lt h,?_⟩
    intro ha
    have hh := (raw_ok x y h).mp ha
    simp [hc] at hh
  cases h : E i j with
  | false =>
    exact forbidden_four hC (hblue _ _ hij h) (hblue _ _ (hij.trans hjk) (hik.symm.trans h))
      (hblue _ _ ((hij.trans hjk).trans hkl) (hil.symm.trans h)) (hblue _ _ hjk (hjk'.symm.trans h))
      (hblue _ _ (hjk.trans hkl) (hjl.symm.trans h)) (hblue _ _ hkl (hkl'.symm.trans h))
  | true =>
    exact forbidden_four hG (hred _ _ hij h) (hred _ _ (hij.trans hjk) (hik.symm.trans h))
      (hred _ _ ((hij.trans hjk).trans hkl) (hil.symm.trans h)) (hred _ _ hjk (hjk'.symm.trans h))
      (hred _ _ (hjk.trans hkl) (hjl.symm.trans h)) (hred _ _ hkl (hkl'.symm.trans h))

theorem recover {G : SimpleGraph (Fin 16)} {a b key w : ℕ} {cs : List (ℕ × ℕ)} :
  let raw (a b key u v : ℕ) : Bool :=
    if v = 15 then decide (u < 7)
    else if v < 7 then a.testBit (v*(v-1)/2+u)
    else if u < 7 then key.testBit (8*u+(v-7))
    else !(b.testBit ((v-7)*(v-8)/2+(u-7)))
  let full (a b key u v : ℕ) : Bool :=
    (u != v) && raw a b key (min u v) (max u v)
  let permDigit (word : ℕ) (i : Fin 16) : Fin 16 := ⟨(word >>> (4*i.val)) % 16,Nat.mod_lt _ (by decide)⟩
  let cert (a b w : ℕ) (c : ℕ × ℕ) : Bool :=
    decide (∀ i j : Fin 16, (permDigit c.2 i=permDigit c.2 j → i=j) ∧
      (i<j → full a b c.1 (permDigit c.2 i).val (permDigit c.2 j).val =
        w.testBit (j.val*(j.val-1)/2+i.val)))
  (∀ i j : Fin 16, G.Adj i j ↔ full a b key i.val j.val = true) →
    cs.all (cert a b w)=true → key ∈ cs.map Prod.fst →
    ∃ e : Fin 16 ≃ Fin 16, ∀ i j : Fin 16, i<j →
      (G.Adj (e i) (e j) ↔ w.testBit (j.val*(j.val-1)/2+i.val)=true) := by
  intro raw full permDigit cert rep good listed
  obtain ⟨⟨key',pi⟩,hc,he⟩ := List.mem_map.mp listed
  change key'=key at he
  subst key'
  have allv := of_decide_eq_true (List.all_eq_true.mp good _ hc)
  let f := permDigit pi
  have inj : Function.Injective f := fun i j => (allv i j).1
  let e := Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩
  refine ⟨e,?_⟩
  intro i j hij
  change G.Adj (f i) (f j) ↔ _
  rw [rep,(allv i j).2 hij]


set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem transfer_0 {G : SimpleGraph (Fin 16)} {key : ℕ}
    (listed : key ∈ ([51907286058939675,15034500931565595,33945870567879469,14524317875730477,43198594614439219,12799184136870195,29758086361914165,7803012962740533,64399053931714119,42443864117208135,57651910428624742,38230810462768230,51821665785623913,14948764242917481,43122054871264632,12723097119988088,59334496917939847,28935539166663303,57108829795010454,20235928252304022,33826783575159705,14405683609303193,29613729920719800,7658540106213816,64254581075187402,42299507676013770,59258409901057740,28858999423488716,57533276162197458,38111723470048466,57023093106362340,20150307978988260] : List ℕ)) :
  let raw (a b key u v : ℕ) : Bool :=
    if v = 15 then decide (u < 7)
    else if v < 7 then a.testBit (v*(v-1)/2+u)
    else if u < 7 then key.testBit (8*u+(v-7))
    else !(b.testBit ((v-7)*(v-8)/2+(u-7)))
  let full (a b key u v : ℕ) : Bool :=
    (u != v) && raw a b key (min u v) (max u v)
  (∀ i j : Fin 16, G.Adj i j ↔ full 480904 60117131 key i.val j.val = true) →
  ∃ e : Fin 16 ≃ Fin 16, ∀ i j : Fin 16, i<j →
    (G.Adj (e i) (e j) ↔ (0xcb94e332f53ae143a3b6933356490b : ℕ).testBit (j.val*(j.val-1)/2+i.val)=true) := by
  intro raw full rep
  let digit (v : ℕ) (i : Fin 16) : Fin 16 := ⟨(v >>> (4*i.val)) % 16,Nat.mod_lt _ (by decide)⟩
  let cert (x : ℕ × ℕ) := decide (∀ i j : Fin 16, (digit x.2 i = digit x.2 j → i=j) ∧
    (i<j → full 480904 60117131 x.1 (digit x.2 i).val (digit x.2 j).val = (0xcb94e332f53ae143a3b6933356490b : ℕ).testBit (j.val*(j.val-1)/2+i.val)))
  let c0 : List (ℕ × ℕ) :=
    [(51907286058939675, 14154028280660000640),
     (15034500931565595, 7621396063791806640),
     (33945870567879469, 13001388319479857040),
     (14524317875730477, 7544834870127491520)]
  have ok0 : c0.all cert = true := by
    dsimp only [c0,cert,digit,full,raw]
    decide +kernel
  let c1 : List (ℕ × ℕ) :=
    [(43198594614439219, 7972712036278335600),
     (12799184136870195, 11848185003821416320),
     (29758086361914165, 7900636854350313840),
     (7803012962740533, 11848466474233679760)]
  have ok1 : c1.all cert = true := by
    dsimp only [c1,cert,digit,full,raw]
    decide +kernel
  let c2 : List (ℕ × ℕ) :=
    [(64399053931714119, 16459026739854741360),
     (42443864117208135, 7774571231972226960),
     (57651910428624742, 7702425698479635600),
     (38230810462768230, 16459308192013410240)]
  have ok2 : c2.all cert = true := by
    dsimp only [c2,cert,digit,full,raw]
    decide +kernel
  let c3 : List (ℕ × ℕ) :=
    [(51821665785623913, 7977127670675275200),
     (14948764242917481, 12999699455667253200),
     (43122054871264632, 8388013318317723600),
     (12723097119988088, 7598895679310593440)]
  have ok3 : c3.all cert = true := by
    dsimp only [c3,cert,digit,full,raw]
    decide +kernel
  let c4 : List (ℕ × ℕ) :=
    [(59334496917939847, 15306105170556002160),
     (28935539166663303, 7842142822863730560),
     (57108829795010454, 7697939695334325120),
     (20235928252304022, 15306668097958768560)]
  have ok4 : c4.all cert = true := by
    dsimp only [c4,cert,digit,full,raw]
    decide +kernel
  let c5 : List (ℕ × ℕ) :=
    [(33826783575159705, 7909573676265701040),
     (14405683609303193, 14152902366261850080),
     (29613729920719800, 8388294797319913440),
     (7658540106213816, 7526855673164725920)]
  have ok5 : c5.all cert = true := by
    dsimp only [c5,cert,digit,full,raw]
    decide +kernel
  let c6 : List (ℕ × ℕ) :=
    [(64254581075187402, 7824022888414706400),
     (42299507676013770, 10693575113745555360),
     (59258409901057740, 7747479291230485200),
     (28858999423488716, 9540653544981589920)]
  have ok6 : c6.all cert = true := by
    dsimp only [c6,cert,digit,full,raw]
    decide +kernel
  let c7 : List (ℕ × ℕ) :=
    [(57533276162197458, 10694982509830246320),
     (38111723470048466, 7463822857685629920),
     (57023093106362340, 9541779465822183360),
     (20150307978988260, 7459336854538222800)]
  have ok7 : c7.all cert = true := by
    dsimp only [c7,cert,digit,full,raw]
    decide +kernel
  let cs := c0 ++ c1 ++ c2 ++ c3 ++ c4 ++ c5 ++ c6 ++ c7
  refine recover (cs:=cs) rep ?_ listed
  change cs.all cert = true
  simp only [cs,List.all_append,ok0,ok1,ok2,ok3,ok4,ok5,ok6,ok7,Bool.and_self]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 2000000 in
theorem transfer_1 {G : SimpleGraph (Fin 16)} {key : ℕ}
    (listed : key ∈ ([55637857725330672,48067720168092912,55637733657818352,48067596100580592,56952130552215792,24148201137518832,56951638560356592,24147709145659632,38937731506388208,24077831856995568,47926982411566320,19609060438195440,47926789893012720,19608867919641840,38937102612446448,24077202963053808,47629513705178352,15386335220647152,47629013156938992,15385834672407792,24270369124042992,16139480636639472,24270253612910832,16139365125507312,24252659279908080,11635763351178480,47594054455446768,6378861088263408,47593827711372528,6378634344189168,24252227182710000,11635331253980400] : List ℕ)) :
  let raw (a b key u v : ℕ) : Bool :=
    if v = 15 then decide (u < 7)
    else if v < 7 then a.testBit (v*(v-1)/2+u)
    else if u < 7 then key.testBit (8*u+(v-7))
    else !(b.testBit ((v-7)*(v-8)/2+(u-7)))
  let full (a b key u v : ℕ) : Bool :=
    (u != v) && raw a b key (min u v) (max u v)
  (∀ i j : Fin 16, G.Adj i j ↔ full 946323 153315680 key i.val j.val = true) →
  ∃ e : Fin 16 ≃ Fin 16, ∀ i j : Fin 16, i<j →
    (G.Adj (e i) (e j) ↔ (0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val*(j.val-1)/2+i.val)=true) := by
  intro raw full rep
  let digit (v : ℕ) (i : Fin 16) : Fin 16 := ⟨(v >>> (4*i.val)) % 16,Nat.mod_lt _ (by decide)⟩
  let cert (x : ℕ × ℕ) := decide (∀ i j : Fin 16, (digit x.2 i = digit x.2 j → i=j) ∧
    (i<j → full 946323 153315680 x.1 (digit x.2 i).val (digit x.2 j).val = (0xacb96354eb266b51b2b6553699403b : ℕ).testBit (j.val*(j.val-1)/2+i.val)))
  let c0 : List (ℕ × ℕ) :=
    [(55637857725330672, 7229330651013968400),
     (48067720168092912, 6080912746034491920),
     (55637733657818352, 7157554531952751120),
     (48067596100580592, 6009136626973274640)]
  have ok0 : c0.all cert = true := by
    dsimp only [c0,cert,digit,full,raw]
    decide +kernel
  let c1 : List (ℕ × ℕ) :=
    [(56952130552215792, 7229349269444555280),
     (24148201137518832, 6080931364465078800),
     (56951638560356592, 7157573150383338000),
     (24147709145659632, 6009155245403861520)]
  have ok1 : c1.all cert = true := by
    dsimp only [c1,cert,digit,full,raw]
    decide +kernel
  let c2 : List (ℕ × ℕ) :=
    [(38937731506388208, 5345404803677450115),
     (24077831856995568, 5345404872396922755),
     (47926982411566320, 5273083399881056115),
     (19609060438195440, 5273083331161583475)]
  have ok2 : c2.all cert = true := by
    dsimp only [c2,cert,digit,full,raw]
    decide +kernel
  let c3 : List (ℕ × ℕ) :=
    [(47926789893012720, 4120161895274209140),
     (19608867919641840, 4120161826554736500),
     (38937102612446448, 4192483299070603140),
     (24077202963053808, 4192483367790075780)]
  have ok3 : c3.all cert = true := by
    dsimp only [c3,cert,digit,full,raw]
    decide +kernel
  let c4 : List (ℕ × ℕ) :=
    [(47629513705178352, 6009169483472106000),
     (15386335220647152, 7157587388451582480),
     (47629013156938992, 6080945602533323280),
     (15385834672407792, 7229363507512799760)]
  have ok4 : c4.all cert = true := by
    dsimp only [c4,cert,digit,full,raw]
    decide +kernel
  let c5 : List (ℕ × ℕ) :=
    [(24270369124042992, 6009188101904658960),
     (16139480636639472, 7157606006884135440),
     (24270253612910832, 6080964220965876240),
     (16139365125507312, 7229382125945352720)]
  have ok5 : c5.all cert = true := by
    dsimp only [c5,cert,digit,full,raw]
    decide +kernel
  let c6 : List (ℕ × ℕ) :=
    [(24252659279908080, 5344877106830401395),
     (11635763351178480, 5344877038110928755),
     (47594054455446768, 4119634129674133380),
     (6378861088263408, 4119634060954660740)]
  have ok6 : c6.all cert = true := by
    dsimp only [c6,cert,digit,full,raw]
    decide +kernel
  let c7 : List (ℕ × ℕ) :=
    [(47593827711372528, 5272555634280980355),
     (6378634344189168, 5272555565561507715),
     (24252227182710000, 4191955602223554420),
     (11635331253980400, 4191955533504081780)]
  have ok7 : c7.all cert = true := by
    dsimp only [c7,cert,digit,full,raw]
    decide +kernel
  let cs := c0 ++ c1 ++ c2 ++ c3 ++ c4 ++ c5 ++ c6 ++ c7
  refine recover (cs:=cs) rep ?_ listed
  change cs.all cert = true
  simp only [cs,List.all_append,ok0,ok1,ok2,ok3,ok4,ok5,ok6,ok7,Bool.and_self]

theorem main : H1 → H2 → H3 → H4 → OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H1_R1.H2 := by
  intro excludeA excludeB censusA censusB G hG hC pivot a ha b hb left right
  obtain ⟨key,cross⟩ := crossing G
  let raw (a b key u v : ℕ) : Bool :=
    if v = 15 then decide (u < 7)
    else if v < 7 then a.testBit (v*(v-1)/2+u)
    else if u < 7 then key.testBit (8*u+(v-7))
    else !(b.testBit ((v-7)*(v-8)/2+(u-7)))
  let full (a b key u v : ℕ) : Bool :=
    (u != v) && raw a b key (min u v) (max u v)
  have rep : ∀ i j : Fin 16, G.Adj i j ↔ full a b key.val i.val j.val=true :=
    full_rep pivot left right cross
  have ordered (i j : Fin 16) (h : i<j) : G.Adj i j ↔ raw a b key.val i.val j.val=true := by
    have hh : i.val<j.val := h
    simpa [full,ne_of_lt hh,min_eq_left hh.le,max_eq_right hh.le] using rep i j
  have free := no_mono hG hC (fun i j => raw a b key.val i.val j.val) ordered
  by_cases hA : a=480904 ∧ b=60117131
  · obtain ⟨rfl,rfl⟩ := hA
    exact ⟨0xcb94e332f53ae143a3b6933356490b,Or.inl rfl,transfer_0 (censusA key free) rep⟩
  by_cases hB : a=946323 ∧ b=153315680
  · obtain ⟨rfl,rfl⟩ := hB
    exact ⟨0xacb96354eb266b51b2b6553699403b,Or.inr rfl,transfer_1 (censusB key free) rep⟩
  have blocks : a∈([480904,944196,944204,483585] : List ℕ) ∨ a∈([746529,1581345,666115,1714691,946323] : List ℕ) := by
    change a ∈ ([480904,944196,944204,483585] : List ℕ) ++ ([746529,1581345,666115,1714691,946323] : List ℕ) at ha
    exact List.mem_append.mp ha
  rcases blocks with h|h
  · exact False.elim (excludeA a h b hb (by tauto) key free)
  · exact False.elim (excludeB a h b hb (by tauto) key free)

end OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H1_R1_H2_R2
