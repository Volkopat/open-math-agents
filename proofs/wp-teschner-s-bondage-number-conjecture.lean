import OMAStatements.S_wp_teschner_s_bondage_number_conjecture

-- Problem: Teschner's bondage number conjecture
-- Credit: @sobrien032

/- Counterexample to Ulrich Teschner's conjecture on the bondage number.
   Yousof Yavari, A Counterexample to Teschner's Bondage-Number Conjecture,
   arXiv:2609.04257 (2026), equation (3.1) and Theorem 1.2.
   https://arxiv.org/abs/2609.04257

   The graph has 18 vertices and maximum degree 3. No five vertices
   dominate it. To verify that four edge deletions still leave a
   dominating set of size six, each entry in the certificate describes
   six vertices and enough edges for them to dominate the graph. For
   each edge, a bit mask records which entries survive its removal.
   Intersecting four masks always leaves a witness. All finite checks
   below are evaluated by the kernel.
-/

namespace TeschnerCert

/- The two parts in equation (3.2) of Yousof Yavari's paper are listed
   in increasing order, with the left part first. Each set bit is a neighbor. -/
def neighbors (u : Fin 18) : ℕ :=
  (#[141312, 53248, 132608, 17920, 71680, 74752, 6656, 57344, 229376,
      76, 44, 81, 82, 161, 138, 386, 304, 261] : Array ℕ)[u.val]'u.isLt

def G : SimpleGraph (Fin 18) where
  Adj u v := (neighbors u).testBit v.val = true
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel G.Adj := fun u v =>
  inferInstanceAs (Decidable ((neighbors u).testBit v.val = true))

def leftEnd (i : Fin 27) : Fin 18 := ⟨i.val / 3, by have := i.isLt; omega⟩

def rightEnd (i : Fin 27) : Fin 18 :=
  (#[11,13,17, 12,14,15, 9,10,17, 9,10,14, 11,12,16,
     10,13,16, 9,11,12, 13,14,15, 15,16,17] : Array (Fin 18))[i.val]'i.isLt

def edgeAt (i : Fin 27) : Sym2 (Fin 18) := s(leftEnd i, rightEnd i)

theorem edgeAt_mem (i : Fin 27) : edgeAt i ∈ G.edgeFinset :=
  SimpleGraph.mem_edgeFinset.mpr (G.mem_edgeSet.mpr
    ((by decide : ∀ j : Fin 27, G.Adj (leftEnd j) (rightEnd j)) i))

theorem exists_edgeAt (e : Sym2 (Fin 18)) (h : e ∈ G.edgeFinset) :
    ∃ i, edgeAt i = e := by
  induction e using Sym2.inductionOn with
  | _ u v =>
    have h' := G.mem_edgeSet.mp (SimpleGraph.mem_edgeFinset.mp h)
    have cover : ∀ x y : Fin 18, G.Adj x y →
        ∃ i : Fin 27, leftEnd i = x ∧ rightEnd i = y ∨ leftEnd i = y ∧ rightEnd i = x :=
      by decide
    obtain ⟨i,hi⟩ := cover u v h'
    exact ⟨i, Sym2.eq_iff.mpr hi⟩

theorem edgeAt_injective : Function.Injective edgeAt := by
  have inj : ∀ i j : Fin 27,
      (leftEnd i = leftEnd j ∧ rightEnd i = rightEnd j ∨
       leftEnd i = rightEnd j ∧ rightEnd i = leftEnd j) → i = j := by decide
  exact fun i j h => inj i j (Sym2.eq_iff.mp h)

theorem maxDegree_le : G.maxDegree ≤ 3 :=
  G.maxDegree_le_of_forall_degree_le 3 (by decide)

theorem nonempty_edges : G.edgeFinset.Nonempty := ⟨edgeAt 0, edgeAt_mem 0⟩

end TeschnerCert

namespace TeschnerCert

open OMA.S_wp_teschner_s_bondage_number_conjecture

/-- Each bit marks a vertex in the closed neighbourhood of the argument. -/
private def closedMask (v : Fin 18) : ℕ :=
  neighbors v ||| 2 ^ v.val

private theorem closedMask_correct : ∀ u v : Fin 18,
    (u = v ∨ G.Adj v u) ↔ (closedMask u).testBit v.val = true := by
  decide +kernel

private def fiveMask (a b c d e : Fin 18) : ℕ :=
  (closedMask a ||| closedMask b ||| closedMask c ||| closedMask d ||| closedMask e) &&&
    (2 ^ 18 - 1)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2400000 in
/-- The union of the closed neighbourhoods of five increasing vertices always misses a bit. -/
private theorem five_miss : ∀ a b : Fin 18, a < b → ∀ c : Fin 18, b < c →
    ∀ d : Fin 18, c < d → ∀ e : Fin 18, d < e → fiveMask a b c d e ≠ 2 ^ 18 - 1 := by
  intro a
  fin_cases a <;> decide +kernel

theorem lower {D : Finset (Fin 18)} (hD : IsDominatingSet G D) : 6 ≤ D.card := by
  by_contra! h
  obtain ⟨E, hDE, _, hE⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ D)
    (show D.card ≤ 5 by omega) (show 5 ≤ (Finset.univ : Finset (Fin 18)).card by decide)
  let f := E.orderEmbOfFin hE
  have hdom (v : Fin 18) : ∃ i : Fin 5, (closedMask (f i)).testBit v.val = true := by
    obtain ⟨w, hw, hv⟩ : ∃ w ∈ D, w = v ∨ G.Adj v w := by
      rcases hD v with hv | ⟨w, hw, hwv⟩
      · exact ⟨v, hv, Or.inl rfl⟩
      · exact ⟨w, hw, Or.inr hwv⟩
    have hew : w ∈ Set.range f := by rw [Finset.range_orderEmbOfFin]; exact hDE hw
    obtain ⟨i, rfl⟩ := hew
    exact ⟨i, (closedMask_correct _ v).mp hv⟩
  apply five_miss (f 0) (f 1) (f.strictMono (by decide)) (f 2) (f.strictMono (by decide))
    (f 3) (f.strictMono (by decide)) (f 4) (f.strictMono (by decide))
  apply Nat.eq_of_testBit_eq
  intro j
  simp only [fiveMask, Nat.testBit_and, Nat.testBit_or, Nat.testBit_two_pow_sub_one]
  by_cases hj : j < 18
  · obtain ⟨i, hi⟩ := hdom ⟨j,hj⟩
    change (closedMask (f i)).testBit j = true at hi
    simp only [hj, decide_true, Bool.and_true, Bool.or_eq_true]
    fin_cases i <;> solve_by_elim (maxDepth := 6) [Or.inl, Or.inr]
  · simp [hj]

end TeschnerCert

namespace TeschnerCert

open OMA.S_wp_teschner_s_bondage_number_conjecture

-- Each six-vertex set has twelve designated edges covering its complement.
-- Bit j in an edge mask indicates that cover j avoids the edge.
private def avoidMask (e : ℕ) : ℕ :=
  (#[
  150720611579180465427094902694, 126271137461700643827207484122,
  39323956110341176261185808700, 31222287955719903222490915750,
  120234904663060255618920434553, 150288247388748226281675664590,
  127444781406084622698065353270, 43382550476077395728200963930,
  85706788127318640026482994629, 115346000081356297388354040717,
  30741811558382258310490009315, 127372182709905466908151077974,
  99963492072111201712605526733, 48016567747617515535964411573,
  116629340086697352784751791964, 74040301323902612835749245369,
  124102261622898773963412196565, 158401217779781000718395341158,
  77014032187174214309309131961, 71799267423732137752231922027,
  98770625417922488824053265747, 618920120172112970114821899,
  39421213676351578310346331566, 39174087129728635249545065077,
  126908016680667901043890035091, 122982991312670696012094465722,
  30947281328626554085535307369
] : Array ℕ).getD e 0

private def verticesMask (i : Fin 97) : ℕ := (#[
  81991, 180784, 25936, 38956, 198794, 45084, 6017, 213188, 41752, 180336,
  35363, 6017, 205890, 26900, 50705, 84164, 136848, 25364, 237640, 133794,
  14604, 35988, 136416, 115777, 75790, 25392, 36909, 83011, 202888, 139354,
  23328, 67203, 137384, 83265, 30980, 70305, 205890, 172568, 150050, 237640,
  5569, 8982, 69773, 131762, 180336, 88196, 5025, 76294, 12034, 82117,
  22273, 166434, 27968, 66755, 196810, 163960, 57428, 57876, 176152, 140818,
  98381, 53793, 34862, 184416, 214208, 5513, 17201, 92166, 205890, 170024,
  137888, 73806, 18726, 15624, 33331, 230592, 98381, 33337, 115777, 71297,
  135400, 66755, 83459, 69773, 20773, 102921, 103433, 22273, 41494, 76294,
  8986, 206858, 12034, 24916, 30980, 135352, 201920
] : Array ℕ).getD i 0

private def coverVertices (i : Fin 97) : Finset (Fin 18) :=
  Finset.univ.filter fun v => (verticesMask i).testBit v

private def supportCode (i : Fin 97) (v : Fin 18) : ℕ :=
  (((#[
  411051299111334952505700547886107397764857987072, 5708990819584190067628223503157635811085954101,
  5445192119828246234085679906431653454946041375775, 1673960853985176078222687059310365545170131256331,
  3997956445308420317168239699889697042202635, 1672734312950574057977892355394486246622179152415,
  421280275850566022979571245752714182816093733888, 18337200276727349636193664858926627797642293,
  5445172972224488565329813881485393587448766059039, 6935531805544993845717092645639678263946433077,
  417982873469221277700333825639324585238642032640, 5445191326547850118275761699619132201474585560064,
  3969819181160490805128045978632731941404725, 5440687369298101289422941370857136510123877903371,
  416756326273208283675308384214913629737778729472, 1667043642280837647855041603905620644992601074699,
  5727362254430179079419843986820241508074292277, 1677258211084470528744956688026102977340859526175,
  17099307932365945390217808905760477073951, 6939501624606939401876546449105176159304548363,
  5445192136927316177727138353247420582660837245963, 1672734330198879780598049206658772099973494395403,
  6953903225063322531114081594338280277274559541, 411047335502425982526741499542811355697995885568,
  1667029274899742081153603098325330409781653930015, 5441913910284020613319003082386387069469396872223,
  417982884403931383005418871649222419653251355136, 411051299111335172918980589930123542097406459904,
  18371483606200340562557988523834359253599285, 5712960590064306006863520801811153800057323573,
  5445192119876810215409094646326964128687542545419, 411051305321488148654105213608266349376831750144,
  6953886056089694744078334809764356357804557323, 5434978378530309751106168168640143775696263621632,
  1677258211084393153887885920865668149741168395295, 411065706967636524247313922744652920732412838912,
  3969819181160490805217770941068383386599455, 5709007870090152385272805277970844409987912223,
  6939495414453743094749592024461413615696871477, 17099307932366344425463244907911389172277,
  5445192154175545024876740188961799783863923278848, 1672738265670625447014453595095907333296638394399,
  411065706982922646017129233189124910820601398272, 6953903240426599108408524855557454952454684725,
  5708990819625728443294392983888671638630476853, 1667043642280718874063870692369346658543545134091,
  418001238678687335689222847374299736239007630336, 1667029274899742081153337134645015933075482214431,
  5445192126038298284550616763179708800514175270943, 1667043642280837868425714116256906071399586638848,
  5445192119831118002713554652392065750355361967104, 6935538015597044310653949568938353657547849739,
  5445192119828246013514475466894981678819245599755, 411051305321589294496295315067157154136164663296,
  18354299465665195013576975323299851148722229, 6935548904733931508585632170656306510231294517,
  1672734295851462355616372290249271717582673587231, 1672734295851462355616106326399711225162152071711,
  5709007870012916969901224688098191493143233567, 5712960590004918884602056007110474171437547573,
  411047352601615141101247720408333896401037611520, 417982867304742445227862137094175568602227573760,
  1673960843096158185205020739791312990937878102027, 6935531805426220055078287913563409111924911157,
  18337200276727191711795996960688277622664245, 421280258605328159165944770704009747768014832640,
  5440687369346784404391841161901737411864073382912, 1667029268689588884846476140293988631752392835083,
  3969819181160490805128045977893860120985631, 6935548904614937146742028833170560206992888373,
  6953903225063102299545261650955134893972292661, 1667029274899843226994995308742916751874062286879,
  1673964800495014883989114091899091859141038178315, 5445192136927316177500595326058538265926013322271,
  417982873469221277700333825638964281669131173888, 34347536558944342785876142451633044902453,
  411047352601614920530442315941854038125591974400, 416756343372397361120575225543936556478332457472,
  411047335502425982526741499718053946654608904704, 411065706921944311551773928810818866838425863168,
  6953903225063322871547592397817855849038906421, 411065706922063085343210804027064324719936274432,
  411051299111334952346978259183262298857519972352, 411065706921944311778715901520516284747081614336,
  1677258211087383916878401981754935193831041172480, 411047352601496146739005350999941367947184099840,
  411047352601496146512861269331890687554715963904, 421280241506139221388388039930545431829968628736,
  1672734302061556165027913792865784630640637902879, 1667029274899742081153337134644654906233478709279,
  5440687386397290366709485923301721038209745682463, 3969819180940145744859734136789338576650251,
  5445176924944403192387576927309244869695374360587, 1677258211084470528745222651525175332360899570719,
  1677258211084393153887885920865668149741168405535, 5727362254430179306361816696507807792592356405,
  18371483606420685623005749948272666323485749
] : Array ℕ).getD i 0) >>> (9 * v.val)) % 512

private def targetVertex (i : Fin 97) (v : Fin 18) : Fin 18 :=
  Fin.ofNat 18 (supportCode i v)

private def supportEdge (i : Fin 97) (v : Fin 18) : Fin 27 :=
  Fin.ofNat 27 (supportCode i v / 18)

private def checkBlock (start len : ℕ) (f : ℕ → Bool) : Bool :=
  (List.range' start len).all f

private theorem checkBlock_at {start len k : ℕ} {f : ℕ → Bool}
    (hc : checkBlock start len f = true) (h1 : start ≤ k) (h2 : k < start+len) :
    f k = true := List.all_eq_true.mp hc _ (List.mem_range'_1.mpr ⟨h1,h2⟩)

private def sixAt (k : ℕ) : Bool := decide ((coverVertices (Fin.ofNat 97 k)).card ≤ 6)

private theorem sixChecked0 : checkBlock 0 16 sixAt = true := by decide
private theorem sixChecked16 : checkBlock 16 16 sixAt = true := by decide
private theorem sixChecked32 : checkBlock 32 16 sixAt = true := by decide
private theorem sixChecked48 : checkBlock 48 16 sixAt = true := by decide
private theorem sixChecked64 : checkBlock 64 16 sixAt = true := by decide
private theorem sixChecked80 : checkBlock 80 16 sixAt = true := by decide
private theorem sixChecked96 : checkBlock 96 1 sixAt = true := by decide

private theorem sixChecked (k : Fin 97) : sixAt k.val = true := by
  by_cases h0 : k.val < 16
  · exact checkBlock_at sixChecked0 (by omega) (by omega)
  by_cases h16 : k.val < 32
  · exact checkBlock_at sixChecked16 (by omega) (by omega)
  by_cases h32 : k.val < 48
  · exact checkBlock_at sixChecked32 (by omega) (by omega)
  by_cases h48 : k.val < 64
  · exact checkBlock_at sixChecked48 (by omega) (by omega)
  by_cases h64 : k.val < 80
  · exact checkBlock_at sixChecked64 (by omega) (by omega)
  by_cases h80 : k.val < 96
  · exact checkBlock_at sixChecked80 (by omega) (by omega)
  exact checkBlock_at sixChecked96 (by omega) (by have := k.isLt; omega)

private theorem coverCard (i : Fin 97) : (coverVertices i).card ≤ 6 := by
  have H := sixChecked i
  simpa [sixAt] using H

private def supportCondition (i : Fin 97) (v : Fin 18) : Prop :=
  (verticesMask i).testBit v.val = true ∨
    (verticesMask i).testBit (targetVertex i v).val = true ∧
    ((leftEnd (supportEdge i v) = v ∧ rightEnd (supportEdge i v) = targetVertex i v) ∨
     (rightEnd (supportEdge i v) = v ∧ leftEnd (supportEdge i v) = targetVertex i v)) ∧
    (avoidMask (supportEdge i v).val).testBit i.val = false

private instance (i : Fin 97) (v : Fin 18) : Decidable (supportCondition i v) := by
  unfold supportCondition
  infer_instance

private def rowCondition (i : Fin 97) : Bool :=
  (List.finRange 18).all fun v => decide (supportCondition i v)

private def supportedAt (k : ℕ) : Bool := rowCondition (Fin.ofNat 97 k)

private theorem supportedChecked0 : checkBlock 0 16 supportedAt = true := by decide
private theorem supportedChecked16 : checkBlock 16 16 supportedAt = true := by decide
private theorem supportedChecked32 : checkBlock 32 16 supportedAt = true := by decide
private theorem supportedChecked48 : checkBlock 48 16 supportedAt = true := by decide
private theorem supportedChecked64 : checkBlock 64 16 supportedAt = true := by decide
private theorem supportedChecked80 : checkBlock 80 16 supportedAt = true := by decide
private theorem supportedChecked96 : checkBlock 96 1 supportedAt = true := by decide

private theorem supportedChecked (k : Fin 97) : supportedAt k.val = true := by
  by_cases h0 : k.val < 16
  · exact checkBlock_at supportedChecked0 (by omega) (by omega)
  by_cases h16 : k.val < 32
  · exact checkBlock_at supportedChecked16 (by omega) (by omega)
  by_cases h32 : k.val < 48
  · exact checkBlock_at supportedChecked32 (by omega) (by omega)
  by_cases h48 : k.val < 64
  · exact checkBlock_at supportedChecked48 (by omega) (by omega)
  by_cases h64 : k.val < 80
  · exact checkBlock_at supportedChecked64 (by omega) (by omega)
  by_cases h80 : k.val < 96
  · exact checkBlock_at supportedChecked80 (by omega) (by omega)
  exact checkBlock_at supportedChecked96 (by omega) (by have := k.isLt; omega)

private theorem maskSpec (i : Fin 97) (v : Fin 18) : supportCondition i v := by
  have hi : rowCondition i = true := by simpa [supportedAt] using supportedChecked i
  exact of_decide_eq_true (List.all_eq_true.mp hi v (List.mem_finRange v))

private def allEdgesFrom (s : ℕ) (p : ℕ → Bool) : Bool :=
  (List.range' s (27-s)).all p

private theorem allEdgesFrom_spec {s v : ℕ} {p : ℕ → Bool}
    (h : allEdgesFrom s p = true) (hs : s ≤ v) (hv : v < 27) : p v = true :=
  List.all_eq_true.mp h _ (List.mem_range'_1.mpr ⟨hs, by omega⟩)

private def surviving (a b c d : ℕ) : ℕ :=
  avoidMask a &&& avoidMask b &&& avoidMask c &&& avoidMask d

private def fourAt (k : ℕ) : Bool := allEdgesFrom k fun b => allEdgesFrom b fun c => allEdgesFrom c fun d => decide (surviving k b c d ≠ 0)

private theorem fourChecked0 : checkBlock 0 4 fourAt = true := by decide
private theorem fourChecked4 : checkBlock 4 4 fourAt = true := by decide
private theorem fourChecked8 : checkBlock 8 4 fourAt = true := by decide
private theorem fourChecked12 : checkBlock 12 4 fourAt = true := by decide
private theorem fourChecked16 : checkBlock 16 4 fourAt = true := by decide
private theorem fourChecked20 : checkBlock 20 4 fourAt = true := by decide
private theorem fourChecked24 : checkBlock 24 3 fourAt = true := by decide

private theorem fourChecked (k : Fin 27) : fourAt k.val = true := by
  by_cases h0 : k.val < 4
  · exact checkBlock_at fourChecked0 (by omega) (by omega)
  by_cases h4 : k.val < 8
  · exact checkBlock_at fourChecked4 (by omega) (by omega)
  by_cases h8 : k.val < 12
  · exact checkBlock_at fourChecked8 (by omega) (by omega)
  by_cases h12 : k.val < 16
  · exact checkBlock_at fourChecked12 (by omega) (by omega)
  by_cases h16 : k.val < 20
  · exact checkBlock_at fourChecked16 (by omega) (by omega)
  by_cases h20 : k.val < 24
  · exact checkBlock_at fourChecked20 (by omega) (by omega)
  exact checkBlock_at fourChecked24 (by omega) (by have := k.isLt; omega)

theorem upperFour (a b c d : Fin 27) (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d) :
    ∃ D : Finset (Fin 18),
      IsDominatingSet (G.deleteEdges ({edgeAt a,edgeAt b,edgeAt c,edgeAt d} : Set _)) D ∧
      D.card ≤ 6 := by
  have h₁ := fourChecked a
  have h₂ := allEdgesFrom_spec h₁ (show a.val ≤ b.val from hab) b.isLt
  have h₃ := allEdgesFrom_spec h₂ (show b.val ≤ c.val from hbc) c.isLt
  have h₄ := allEdgesFrom_spec h₃ (show c.val ≤ d.val from hcd) d.isLt
  let m := surviving a.val b.val c.val d.val
  have hm : m ≠ 0 := of_decide_eq_true h₄
  have bound : ∀ e : Fin 27, avoidMask e.val < 2^97 := by decide
  have hm' : m ≤ avoidMask d.val := Nat.and_le_right
  let i : Fin 97 := ⟨m.log2,(Nat.log2_lt hm).mpr (lt_of_le_of_lt hm' (bound d))⟩
  have hs : (m.testBit i.val) = true := Nat.testBit_log2 hm
  simp only [m, surviving, Nat.testBit_and, Bool.and_eq_true] at hs
  refine ⟨coverVertices i, ?_,coverCard i⟩
  intro v
  rcases maskSpec i v with H | ⟨hw, hp, havoid⟩
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _,H⟩)
  · have he : edgeAt (supportEdge i v) = s(v, targetVertex i v) := by
      apply Sym2.eq_iff.mpr
      exact hp.imp_right And.symm
    refine Or.inr ⟨targetVertex i v, Finset.mem_filter.mpr ⟨Finset.mem_univ _,hw⟩, SimpleGraph.deleteEdges_adj.mpr ⟨?_, ?_⟩⟩
    · have hh := SimpleGraph.mem_edgeFinset.mp (edgeAt_mem (supportEdge i v))
      rw [he] at hh
      exact G.mem_edgeSet.mp hh
    · rw [← he]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rintro (h | h | h | h)
      · have h' := edgeAt_injective h
        rw [h'] at havoid
        simp [hs.1.1.1] at havoid
      · have h' := edgeAt_injective h
        rw [h'] at havoid
        simp [hs.1.1.2] at havoid
      · have h' := edgeAt_injective h
        rw [h'] at havoid
        simp [hs.1.2] at havoid
      · have h' := edgeAt_injective h
        rw [h'] at havoid
        simp [hs.2] at havoid

end TeschnerCert

namespace TeschnerCert

open OMA.S_wp_teschner_s_bondage_number_conjecture

/-- Enlarge the indices of a deletion to four distinct indices in increasing order. -/
private theorem cover_by_four {E : Type*} (edge : Fin 27 → E) (F : Finset E)
    (hF : ∀ e ∈ F, ∃ i, edge i = e) (hc : F.card ≤ 4) :
    ∃ a b c d : Fin 27, a ≤ b ∧ b ≤ c ∧ c ≤ d ∧
      (F : Set E) ⊆ {edge a, edge b, edge c, edge d} := by
  classical
  let index (e : E) : Fin 27 :=
    if h : ∃ i, edge i = e then h.choose else 0
  have hindex (e : E) (he : e ∈ F) : edge (index e) = e := by
    dsimp [index]
    rw [dif_pos (hF _ he)]
    exact (hF _ he).choose_spec
  let small := F.image index
  have hsmall : small.card ≤ 4 := Finset.card_image_le.trans hc
  obtain ⟨S,hS,_,hcard⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ small)
    hsmall (by decide : 4 ≤ (Finset.univ : Finset (Fin 27)).card)
  let g := S.orderEmbOfFin hcard
  refine ⟨g 0, g 1, g 2, g 3, g.monotone (by decide), g.monotone (by decide),
    g.monotone (by decide), ?_⟩
  intro e he
  have hmem : index e ∈ S := hS (Finset.mem_image_of_mem index he)
  have hrange : index e ∈ Set.range g := by
    simpa [g,Finset.range_orderEmbOfFin] using hmem
  obtain ⟨j,hj⟩ := hrange
  rw [← hindex _ he, ← hj]
  fin_cases j <;> simp

theorem contradiction_of_certificates (G : SimpleGraph (Fin 18)) [DecidableRel G.Adj]
    (edge : Fin 27 → Sym2 (Fin 18))
    (edge_complete : ∀ e ∈ G.edgeFinset, ∃ i, edge i = e)
    (degree_bound : G.maxDegree ≤ 3) (has_edge : G.edgeFinset.Nonempty)
    (lower_bound : ∀ {D : Finset (Fin 18)}, IsDominatingSet G D → 6 ≤ D.card)
    (upper_bound : ∀ a b c d : Fin 27, a ≤ b → b ≤ c → c ≤ d →
      ∃ D : Finset (Fin 18),
        IsDominatingSet (G.deleteEdges ({edge a, edge b, edge c, edge d} : Set _)) D ∧
        D.card ≤ 6) :
    ¬ (type_of% @OMA.S_wp_teschner_s_bondage_number_conjecture.main) := by
  intro h
  obtain ⟨F,hF,hincrease,hsize⟩ := h 18 G has_edge
  obtain ⟨a,b,c,d,hab,hbc,hcd,hsub⟩ :=
    cover_by_four edge F (fun e he => edge_complete e (hF he)) (by omega)
  obtain ⟨D,hD,hcard⟩ := upper_bound a b c d hab hbc hcd
  have hsmall : IsDominatingSet (G.deleteEdges (F : Set _)) D := by
    intro v
    rcases hD v with h | ⟨w,hw,hadj⟩
    · exact Or.inl h
    · exact Or.inr ⟨w,hw,G.deleteEdges_anti hsub hadj⟩
  have low : 6 ≤ dominationNumber G := by
    apply le_csInf
    · exact ⟨18, Finset.univ, fun v => Or.inl (Finset.mem_univ v), by simp⟩
    · rintro k ⟨s,hs,rfl⟩
      exact lower_bound hs
  have high : dominationNumber (G.deleteEdges (F : Set _)) ≤ D.card :=
    csInf_le (OrderBot.bddBelow _) ⟨D,hsmall,rfl⟩
  omega

end TeschnerCert

theorem OMA.disproof : ¬ (type_of% @OMA.S_wp_teschner_s_bondage_number_conjecture.main) := by
  apply TeschnerCert.contradiction_of_certificates TeschnerCert.G TeschnerCert.edgeAt
    TeschnerCert.exists_edgeAt TeschnerCert.maxDegree_le TeschnerCert.nonempty_edges
  · exact TeschnerCert.lower
  · exact TeschnerCert.upperFour
