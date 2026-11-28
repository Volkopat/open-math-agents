import OMAReductions.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H3_R1
import Mathlib

/-! Exclude an eight-vertex counterexample by checking one-vertex extensions. Stop extending a representative as soon as it contains one of the 25 induced obstructions. -/
open SimpleGraph Finset
namespace EarlyBlockerAtlas

def edge (w i j : ℕ) : Bool :=
  (i != j) && w.testBit (max i j * (max i j - 1) / 2 + min i j)

def extended (n w m i j : ℕ) : Bool :=
  if i = j then false else if i = n then m.testBit j else
    if j = n then m.testBit i else edge w i j

def Represents {n : ℕ} (G : SimpleGraph (Fin n)) (w : ℕ) : Prop :=
  ∃ e : Equiv.Perm (Fin n), ∀ i j, G.Adj (e i) (e j) ↔ edge w i.val j.val = true

def targets : List (ℕ × ℕ) := ([(6,2112),(6,3136),(6,4232),(6,6208),(6,14400),(7,236608),(7,332992),(7,368064),(7,396480),(7,433344),(7,437696),(7,439488),(7,466056),(7,472256),(7,494784),(7,496832),(7,498752),(7,506944),(7,507840),(7,922816),(7,924864),(8,31956160),(8,31960512),(8,59186376),(8,59227328)] : List (ℕ × ℕ))

def Obstruction {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ p ∈ targets, ∃ e : Fin p.1 ↪ Fin n, ∀ i j, i<j →
    (G.Adj (e i) (e j) ↔ p.2.testBit (j.val*(j.val-1)/2+i.val) = true)

def Census (n : ℕ) (L : List ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n), G.CliqueFree 3 → Gᶜ.CliqueFree 5 → ¬Obstruction G →
    ∃ w ∈ L, Represents G w

/-- The low ten bits select a representative or an obstruction. Subsequent
base-eight digits list vertices in the candidate extension. -/
def vertex (n c i : ℕ) : Fin (n+1) :=
  ⟨((c / 1024 / 8^i) % 8) % (n+1), Nat.mod_lt _ (by omega)⟩

def MonoCert (n w m c k : ℕ) (colour : Bool) : Prop :=
  ∀ i j : Fin k, i ≠ j →
    vertex n c i.val ≠ vertex n c j.val ∧
    extended n w m (vertex n c i.val).val (vertex n c j.val).val = colour

instance (n w m c k : ℕ) (b : Bool) : Decidable (MonoCert n w m c k b) := by
  unfold MonoCert
  infer_instance

def PermCert (n w m c : ℕ) (L : List ℕ) : Prop :=
  c%1024 < L.length ∧
  (∀ i j : Fin (n+1), vertex n c i.val = vertex n c j.val → i=j) ∧
  ∀ i j : Fin (n+1),
    extended n w m (vertex n c i.val).val (vertex n c j.val).val =
      edge (L.getD (c%1024) 0) i.val j.val

instance (n w m c : ℕ) (L : List ℕ) : Decidable (PermCert n w m c L) := by
  unfold PermCert
  infer_instance

def BlockCert (n w m c : ℕ) : Prop :=
  let ix := c%1024-960
  let p := targets.getD ix (0,0)
  ix<targets.length ∧
  (∀ i j : Fin p.1, vertex n c i.val = vertex n c j.val → i=j) ∧
  ∀ i j : Fin p.1, i<j →
    extended n w m (vertex n c i.val).val (vertex n c j.val).val =
      p.2.testBit (j.val*(j.val-1)/2+i.val)

instance (n w m c : ℕ) : Decidable (BlockCert n w m c) := by
  unfold BlockCert
  infer_instance

def Valid (n w m : ℕ) (L : List ℕ) (c : ℕ) : Prop :=
  if c%1024 = 1022 then MonoCert n w m c 3 true
  else if c%1024 = 1023 then MonoCert n w m c 5 false
  else if 960 ≤ c%1024 then BlockCert n w m c else PermCert n w m c L

instance (n w m : ℕ) (L : List ℕ) (c : ℕ) : Decidable (Valid n w m L c) := by
  unfold Valid
  infer_instance

/-- A bounded Boolean loop for kernel evaluation of a single row. -/
def scan : ℕ → (ℕ → Bool) → Bool
  | 0, _ => true
  | n+1, f => scan n f && f n

theorem scan_at {n i : ℕ} {f : ℕ → Bool} (h : scan n f = true) (hi : i<n) : f i = true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [scan, Bool.and_eq_true] at h
    obtain ⟨h₁,h₂⟩ := h
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
    · exact ih h₁ hlt
    · exact h₂

def pairs (k : ℕ) (f : ℕ → ℕ → Bool) : Bool :=
  scan k (fun i => scan k (f i))

theorem pair_at {k i j : ℕ} {f : ℕ → ℕ → Bool} (h : pairs k f = true)
    (hi : i<k) (hj : j<k) : f i j = true := scan_at (scan_at h hi) hj

def monoTest (n w m c k : ℕ) (b : Bool) : Bool :=
  pairs k (fun i j => decide (i ≠ j →
    vertex n c i ≠ vertex n c j ∧ extended n w m (vertex n c i).val (vertex n c j).val = b))

theorem mono_sound {n w m c k : ℕ} {b : Bool} (h : monoTest n w m c k b = true) :
    MonoCert n w m c k b := by
  intro i j hij
  exact of_decide_eq_true (pair_at h i.isLt j.isLt) (fun eq ↦ hij (Fin.ext eq))

def permTest (n w m c : ℕ) (L : List ℕ) : Bool :=
  decide (c%1024 < L.length) && pairs (n+1) (fun i j =>
    decide ((vertex n c i = vertex n c j → i=j) ∧
      extended n w m (vertex n c i).val (vertex n c j).val = edge (L.getD (c%1024) 0) i j))

theorem perm_sound {n w m c : ℕ} {L : List ℕ} (h : permTest n w m c L = true) :
    PermCert n w m c L := by
  simp only [permTest, Bool.and_eq_true] at h
  obtain ⟨hi,hp⟩ := h
  exact ⟨of_decide_eq_true hi,fun i j hh ↦ Fin.ext ((of_decide_eq_true (pair_at hp i.isLt j.isLt)).1 hh),
    fun i j ↦ (of_decide_eq_true (pair_at hp i.isLt j.isLt)).2⟩

def blockTest (n w m c : ℕ) : Bool :=
  let ix := c%1024-960
  let p := targets.getD ix (0,0)
  decide (ix < targets.length) && pairs p.1 (fun i j =>
    decide ((vertex n c i = vertex n c j → i=j) ∧ (i<j →
      extended n w m (vertex n c i).val (vertex n c j).val = p.2.testBit (j*(j-1)/2+i))))

theorem block_sound {n w m c : ℕ} (h : blockTest n w m c = true) : BlockCert n w m c := by
  simp only [blockTest, Bool.and_eq_true] at h
  obtain ⟨hi,hp⟩ := h
  exact ⟨of_decide_eq_true hi,fun i j hh ↦ Fin.ext ((of_decide_eq_true (pair_at hp i.isLt j.isLt)).1 hh),
    fun i j ↦ (of_decide_eq_true (pair_at hp i.isLt j.isLt)).2⟩

def test (n w m : ℕ) (L : List ℕ) (c : ℕ) : Bool :=
  if c%1024 = 1022 then monoTest n w m c 3 true
  else if c%1024 = 1023 then monoTest n w m c 5 false
  else if 960 ≤ c%1024 then blockTest n w m c else permTest n w m c L

theorem test_sound {n w m c : ℕ} {L : List ℕ} (h : test n w m L c = true) : Valid n w m L c := by
  unfold test at h
  unfold Valid
  split <;> rename_i h₁
  · exact mono_sound (by simpa [h₁] using h)
  · simp only [if_neg h₁] at h
    split <;> rename_i h₂
    · exact mono_sound (by simpa [h₂] using h)
    · simp only [if_neg h₂] at h
      split <;> rename_i h₃
      · exact block_sound (by simpa [h₃] using h)
      · exact perm_sound (by simpa [h₃] using h)

def Rows (n : ℕ) (old next : List ℕ) : Prop :=
  ∀ w ∈ old, ∀ m : Fin (2^n), ∃ c, Valid n w m.val next c

theorem row_cons {n w : ℕ} {tail next : List ℕ} (data : Array ℕ)
    (ok : scan (2^n) (fun m => test n w m next data[m]!) = true)
    (rest : Rows n tail next) : Rows n (w::tail) next := by
  intro v hv m
  rcases List.mem_cons.mp hv with eq | hmem
  · subst v
    exact ⟨data[m.val]!,test_sound (scan_at (f:=fun z => test n w z next data[z]!) (i:=m.val) ok m.isLt)⟩
  · exact rest _ hmem m

theorem rows_nil {n : ℕ} {next : List ℕ} : Rows n [] next := by
  intro w h
  simp at h

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

theorem valid_sound {n w m c : ℕ} {L : List ℕ} {G : SimpleGraph (Fin (n+1))}
    (hG : G.CliqueFree 3) (hC : Gᶜ.CliqueFree 5) (e : Equiv.Perm (Fin (n+1)))
    (raw : ∀ i j, G.Adj (e i) (e j) ↔ extended n w m i.val j.val = true)
    (avoid : ¬Obstruction G) (v : Valid n w m L c) : ∃ a ∈ L, Represents G a := by
  unfold Valid at v
  split at v
  · exfalso
    apply forbidden hG (fun i => e (vertex n c i.val))
    intro i j hij
    have hh := v i j hij
    exact ⟨fun he => hh.1 (e.injective he), (raw _ _).mpr hh.2⟩
  · split at v
    · exfalso
      apply forbidden hC (fun i => e (vertex n c i.val))
      intro i j hij
      have hh := v i j hij
      have he : e (vertex n c i.val) ≠ e (vertex n c j.val) := fun eq => hh.1 (e.injective eq)
      refine ⟨he,he,?_⟩
      intro adj
      have hv := (raw _ _).mp adj
      simp only [hh.2] at hv
      contradiction
    · split at v
      · exfalso
        apply avoid
        let ix := c%1024-960
        let p := targets.getD ix (0,0)
        obtain ⟨hlt,hinj,hadj⟩ := v
        refine ⟨p,?_,⟨fun i => e (vertex n c i.val),fun i j h => hinj i j (e.injective h)⟩,?_⟩
        · simp [p,ix,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hlt]
        · intro i j hij
          change G.Adj (e (vertex n c i.val)) (e (vertex n c j.val)) ↔ _
          rw [raw,hadj i j hij]
      · obtain ⟨hlt,hinj,hmatch⟩ := v
        let f (i : Fin (n+1)) := vertex n c i.val
        have inj : Function.Injective f := fun i j => hinj i j
        let π := Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩
        refine ⟨L.getD (c%1024) 0,?_,π.trans e,?_⟩
        · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
        · intro i j
          change G.Adj (e (f i)) (e (f j)) ↔ _
          rw [raw, hmatch i j]

def liftPerm {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n+1)) where
  toFun := Fin.lastCases (Fin.last n) (fun i => (e i).castSucc)
  invFun := Fin.lastCases (Fin.last n) (fun i => (e.symm i).castSucc)
  left_inv := Fin.lastCases (by simp) (fun i => by simp)
  right_inv := Fin.lastCases (by simp) (fun i => by simp)

theorem lift_last {n : ℕ} (e : Equiv.Perm (Fin n)) :
    liftPerm e (Fin.last n) = Fin.last n := by simp [liftPerm]

theorem lift_old {n : ℕ} (e : Equiv.Perm (Fin n)) (i : Fin n) :
    liftPerm e i.castSucc = (e i).castSucc := by simp [liftPerm]

/-- Every extension of a labeled induced graph occurs in precisely one
neighborhood-mask column, before taking graph isomorphism. -/
theorem extension {n w : ℕ} (G : SimpleGraph (Fin (n+1)))
    (h : Represents (G.comap (Fin.castSucc : Fin n → Fin (n+1))) w) :
    ∃ (m : Fin (2^n)) (e : Equiv.Perm (Fin (n+1))), ∀ i j,
      G.Adj (e i) (e j) ↔ extended n w m.val i.val j.val = true := by
  classical
  obtain ⟨e,he⟩ := h
  change ∀ i j, G.Adj (e i).castSucc (e j).castSucc ↔ edge w i.val j.val = true at he
  let f (i : Fin n) := decide (G.Adj (e i).castSucc (Fin.last n))
  let vec := BitVec.ofBoolListLE (List.ofFn f)
  let m : Fin (2^n) := ⟨vec.toNat, by simpa [vec] using vec.isLt⟩
  have hb (i : Fin n) : m.val.testBit i.val = f i := by
    change (BitVec.ofBoolListLE (List.ofFn f)).getLsbD i.val = _
    rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD]
    simp [i.isLt]
  refine ⟨m,liftPerm e,?_⟩
  intro i j
  refine Fin.lastCases ?_ (fun a => ?_) i <;> refine Fin.lastCases ?_ (fun b => ?_) j
  · simp [lift_last,extended]
  · simp [lift_last,lift_old,extended,Ne.symm (Nat.ne_of_lt b.isLt),hb,f,G.adj_comm]
  · simp [lift_last,lift_old,extended,Nat.ne_of_lt a.isLt,hb,f]
  · by_cases eq : a=b
    · subst b
      simp [lift_old,extended]
    · have hv : a.val ≠ b.val := fun h => eq (Fin.ext h)
      simpa only [lift_old, Fin.val_castSucc,extended,if_neg hv,if_neg (Nat.ne_of_lt a.isLt),
        if_neg (Nat.ne_of_lt b.isLt)] using he a b

theorem step {n : ℕ} {old next : List ℕ}
    (previous : Census n old) (checked : Rows n old next) : Census (n+1) next := by
  intro G hG hC avoid
  let H := G.comap (Fin.castSuccEmb : Fin n ↪ Fin (n+1))
  let emb : H ↪g G := SimpleGraph.Embedding.comap Fin.castSuccEmb G
  have hH := hG.comap emb.isContained
  have hHC := hC.comap (SimpleGraph.Embedding.complEquiv emb).isContained
  have absent : ¬Obstruction H := by
    intro obstruction
    apply avoid
    obtain ⟨p,hp,f,hf⟩ := obstruction
    exact ⟨p,hp,f.trans Fin.castSuccEmb,fun i j h => hf i j h⟩
  obtain ⟨w,hw,hrep⟩ := previous H hH hHC absent
  obtain ⟨m,e,raw⟩ := extension G hrep
  obtain ⟨c,hc⟩ := checked w hw m
  exact valid_sound hG hC e raw avoid hc

theorem empty : Census 0 [0] := by
  intro G _ _ _
  exact ⟨0,by simp,Equiv.refl _,fun i => Fin.elim0 i⟩

def cells0_0 : Array ℕ := #[0]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells0_0_ok : scan (2^0) (fun m => test 0 0 m [0] cells0_0[m]!) = true := by decide +kernel

theorem level1 : Census 1 [0] := by
  apply step empty
  apply row_cons cells0_0 cells0_0_ok
  exact rows_nil

def cells1_0 : Array ℕ := #[8192,8193]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells1_0_ok : scan (2^1) (fun m => test 1 0 m [0,1] cells1_0[m]!) = true := by decide +kernel

theorem level2 : Census 2 [0,1] := by
  apply step level1
  apply row_cons cells1_0 cells1_0_ok
  exact rows_nil

def cells2_0 : Array ℕ := #[139264,139265,132097,139266]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells2_0_ok : scan (2^2) (fun m => test 2 0 m [0,2,6] cells2_0[m]!) = true := by decide +kernel

def cells2_1 : Array ℕ := #[81921,17410,81922,140286]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells2_1_ok : scan (2^2) (fun m => test 2 1 m [0,2,6] cells2_1[m]!) = true := by decide +kernel

theorem level3 : Census 3 [0,2,6] := by
  apply step level2
  apply row_cons cells2_0 cells2_0_ok
  apply row_cons cells2_1 cells2_1_ok
  exact rows_nil

def cells3_0 : Array ℕ := #[1712128,1712129,1704961,1712130,1640449,1654786,1590274,1712131]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells3_0_ok : scan (2^3) (fun m => test 3 0 m [0,8,24,56,18,26,30] cells3_0[m]!) = true := by decide +kernel

def cells3_1 : Array ℕ := #[1253377,92162,1712132,1712133,1138690,214014,1583109,214014]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells3_1_ok : scan (2^3) (fun m => test 3 2 m [0,8,24,56,18,26,30] cells3_1[m]!) = true := by decide +kernel

def cells3_2 : Array ℕ := #[1253378,1253381,1246213,1712134,1253379,214014,215038,214014]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells3_2_ok : scan (2^3) (fun m => test 3 6 m [0,8,24,56,18,26,30] cells3_2[m]!) = true := by decide +kernel

theorem level4 : Census 4 [0,8,24,56,18,26,30] := by
  apply step level3
  apply row_cons cells3_0 cells3_0_ok
  apply row_cons cells3_1 cells3_1_ok
  apply row_cons cells3_2 cells3_2_ok
  exact rows_nil

def cells4_0 : Array ℕ := #[18490367,18489344,18482176,18489345,18417664,18432001,18367489,18489346,17894400,17915905,17851393,18030594,17328129,17514498,16991234,18489347]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells4_0_ok : scan (2^4) (fun m => test 4 0 m [64,192,448,960,136,200,392,456,216,344,472,504,410] cells4_0[m]!) = true := by decide +kernel

def cells4_1 : Array ℕ := #[14819328,1149953,18489348,18489349,18432004,18432005,18489350,18489351,13729793,287742,16919557,287742,16862213,287742,16919559,287742]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells4_1_ok : scan (2^4) (fun m => test 4 8 m [64,192,448,960,136,200,392,456,216,344,472,504,410] cells4_1[m]!) = true := by decide +kernel

def cells4_2 : Array ℕ := #[14819329,14819333,14812165,18489352,14747654,18489353,18482185,18489354,13901826,287742,288766,287742,13701127,287742,288766,287742]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells4_2_ok : scan (2^4) (fun m => test 4 24 m [64,192,448,960,136,200,392,456,216,344,472,504,410] cells4_2[m]!) = true := by decide +kernel

def cells4_3 : Array ℕ := #[14819330,14819335,14812167,14819338,14747655,14761994,14697482,18489355,14819331,287742,288766,287742,289790,287742,288766,287742]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells4_3_ok : scan (2^4) (fun m => test 4 56 m [64,192,448,960,136,200,392,456,216,344,472,504,410] cells4_3[m]!) = true := by decide +kernel

def cells4_4 : Array ℕ := #[13901828,1852422,5529606,4411401,10224646,279550,5443593,279550,13901830,1716233,288766,288766,13701129,279550,288766,279550]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells4_4_ok : scan (2^4) (fun m => test 4 18 m [64,192,448,960,136,200,392,456,216,344,472,504,410] cells4_4[m]!) = true := by decide +kernel

def cells4_5 : Array ℕ := #[13901829,805895,4475913,691210,10231817,279550,18489356,279550,13901831,287742,288766,287742,13729802,279550,288766,279550]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells4_5_ok : scan (2^4) (fun m => test 4 26 m [64,192,448,960,136,200,392,456,216,344,472,504,410] cells4_5[m]!) = true := by decide +kernel

def cells4_6 : Array ℕ := #[13901832,813066,4483082,4483083,10231818,279550,280574,279550,13901834,287742,288766,287742,13901835,279550,280574,279550]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells4_6_ok : scan (2^4) (fun m => test 4 30 m [64,192,448,960,136,200,392,456,216,344,472,504,410] cells4_6[m]!) = true := by decide +kernel

theorem level5 : Census 5 [64,192,448,960,136,200,392,456,216,344,472,504,410] := by
  apply step level4
  apply row_cons cells4_0 cells4_0_ok
  apply row_cons cells4_1 cells4_1_ok
  apply row_cons cells4_2 cells4_2_ok
  apply row_cons cells4_3 cells4_3_ok
  apply row_cons cells4_4 cells4_4_ok
  apply row_cons cells4_5 cells4_5_ok
  apply row_cons cells4_6 cells4_6_ok
  exact rows_nil

def cells5_0 : Array ℕ := #[22684671,23283711,186262464,186262465,186205120,186205121,186262467,186261504,185689024,185689025,185803715,185802752,185287619,185286656,186262468,186261505,22684671,361470,169489345,361470,169432001,361470,169488384,361470,168915905,361470,169029632,361470,168513536,361470,169488385,361470]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells5_0_ok : scan (2^5) (fun m => test 5 64 m [7232,15424,3264,5312,7360,12480,13504,15552,28864,7616,11712,15808,16320,5256,7304,6344,7368,10440,14536,6536,7560,7624,14792,6488,7512,7640,7672] cells5_0[m]!) = true := by decide +kernel

def cells5_1 : Array ℕ := #[22684671,156902337,156895169,186261506,156830659,186261507,186254339,186261508,156307395,185802755,185795587,185802756,186261509,186261510,186254342,186261511,22684671,361470,362494,361470,144249856,361470,362494,361470,147919872,361470,362494,361470,186261512,361470,362494,361470]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells5_1_ok : scan (2^5) (fun m => test 5 192 m [7232,15424,3264,5312,7360,12480,13504,15552,28864,7616,11712,15808,16320,5256,7304,6344,7368,10440,14536,6536,7560,7624,14792,6488,7512,7640,7672] cells5_1[m]!) = true := by decide +kernel

def cells5_2 : Array ℕ := #[22684671,156901376,156894208,156901380,156829696,156844036,156779524,186261513,156307396,156327942,156263430,186261514,155740166,186204170,186139658,186261515,22684671,361470,362494,361470,363518,361470,362494,361470,147919873,361470,362494,361470,363518,361470,362494,361470]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells5_2_ok : scan (2^5) (fun m => test 5 448 m [7232,15424,3264,5312,7360,12480,13504,15552,28864,7616,11712,15808,16320,5256,7304,6344,7368,10440,14536,6536,7560,7624,14792,6488,7512,7640,7672] cells5_2[m]!) = true := by decide +kernel

def cells5_3 : Array ℕ := #[22684671,156901377,156894209,156901383,156829697,156844039,156779527,156901387,156306433,156327943,156263431,156442635,155740167,155926539,155403275,186261516,22684671,361470,362494,361470,363518,361470,362494,361470,364542,361470,362494,361470,363518,361470,362494,361470]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells5_3_ok : scan (2^5) (fun m => test 5 960 m [7232,15424,3264,5312,7360,12480,13504,15552,28864,7616,11712,15808,16320,5256,7304,6344,7368,10440,14536,6536,7560,7624,14792,6488,7512,7640,7672] cells5_3[m]!) = true := by decide +kernel

def cells5_4 : Array ℕ := #[149562304,18180035,47547331,34894851,186262466,186261517,182584333,186261518,118818755,353278,47453187,353278,184691725,353278,170025998,353278,148186051,18035715,362494,362494,181014541,173703182,362494,362494,147919875,353278,362494,353278,172133390,353278,362494,353278]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells5_4_ok : scan (2^5) (fun m => test 5 136 m [7232,15424,3264,5312,7360,12480,13504,15552,28864,7616,11712,15808,16320,5256,7304,6344,7368,10440,14536,6536,7560,7624,14792,6488,7512,7640,7672] cells5_4[m]!) = true := by decide +kernel

def cells5_5 : Array ℕ := #[149562305,5599232,34959363,5484548,156844045,9154574,186261519,186261520,118824963,353278,186261521,353278,147919887,353278,186261522,353278,148185088,361470,362494,361470,144285710,361470,362494,361470,147955716,353278,362494,353278,168456208,353278,362494,353278]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells5_5_ok : scan (2^5) (fun m => test 5 200 m [7232,15424,3264,5312,7360,12480,13504,15552,28864,7616,11712,15808,16320,5256,7304,6344,7368,10440,14536,6536,7560,7624,14792,6488,7512,7640,7672] cells5_5[m]!) = true := by decide +kernel

def cells5_6 : Array ℕ := #[149562307,135375877,149554189,156901391,149489677,156844047,186261523,186261524,147955717,353278,105951247,353278,109621263,353278,184691732,353278,149562308,135361542,362494,362494,363518,363518,362494,362494,147919878,353278,362494,353278,363518,353278,362494,353278]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells5_6_ok : scan (2^5) (fun m => test 5 392 m [7232,15424,3264,5312,7360,12480,13504,15552,28864,7616,11712,15808,16320,5256,7304,6344,7368,10440,14536,6536,7560,7624,14792,6488,7512,7640,7672] cells5_6[m]!) = true := by decide +kernel

def cells5_7 : Array ℕ := #[149561344,135375880,156901390,156901392,156844046,156844048,156901396,186261525,147955718,353278,155331602,353278,155274258,353278,186261526,353278,149561345,361470,362494,361470,363518,361470,362494,361470,147955719,353278,362494,353278,363518,353278,362494,353278]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells5_7_ok : scan (2^5) (fun m => test 5 456 m [7232,15424,3264,5312,7360,12480,13504,15552,28864,7616,11712,15808,16320,5256,7304,6344,7368,10440,14536,6536,7560,7624,14792,6488,7512,7640,7672] cells5_7[m]!) = true := by decide +kernel

def cells5_8 : Array ℕ := #[149561346,5606404,34966532,34966537,149489683,5534740,34894868,34894869,118824964,353278,354302,353278,118559764,353278,354302,353278,148185092,361470,362494,361470,147919892,361470,362494,361470,148185097,353278,354302,353278,147919893,353278,354302,353278]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells5_8_ok : scan (2^5) (fun m => test 5 216 m [7232,15424,3264,5312,7360,12480,13504,15552,28864,7616,11712,15808,16320,5256,7304,6344,7368,10440,14536,6536,7560,7624,14792,6488,7512,7640,7672] cells5_8[m]!) = true := by decide +kernel

def cells5_9 : Array ℕ := #[149561347,9276430,149554191,5599252,120129551,9276436,186261527,186261528,120143878,353278,354302,353278,120129554,353278,354302,353278,149561350,361470,149554194,361470,363518,361470,363518,361470,147955722,353278,354302,353278,363518,353278,354302,353278]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells5_9_ok : scan (2^5) (fun m => test 5 344 m [7232,15424,3264,5312,7360,12480,13504,15552,28864,7616,11712,15808,16320,5256,7304,6344,7368,10440,14536,6536,7560,7624,14792,6488,7512,7640,7672] cells5_9[m]!) = true := by decide +kernel

def cells5_10 : Array ℕ := #[149561348,149561360,149554192,34959381,149489684,156901400,156894232,186261529,120201226,353278,354302,353278,147919894,353278,354302,353278,149561351,361470,362494,361470,363518,361470,362494,361470,148185099,353278,354302,353278,363518,353278,354302,353278]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells5_10_ok : scan (2^5) (fun m => test 5 472 m [7232,15424,3264,5312,7360,12480,13504,15552,28864,7616,11712,15808,16320,5256,7304,6344,7368,10440,14536,6536,7560,7624,14792,6488,7512,7640,7672] cells5_10[m]!) = true := by decide +kernel

def cells5_11 : Array ℕ := #[149561353,149561365,149554197,149561369,149489685,149504025,149439513,186261530,120201227,353278,354302,353278,355326,353278,354302,353278,149561355,361470,362494,361470,363518,361470,362494,361470,149561356,353278,354302,353278,355326,353278,354302,353278]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells5_11_ok : scan (2^5) (fun m => test 5 504 m [7232,15424,3264,5312,7360,12480,13504,15552,28864,7616,11712,15808,16320,5256,7304,6344,7368,10440,14536,6536,7560,7624,14792,6488,7512,7640,7672] cells5_11[m]!) = true := by decide +kernel

def cells5_12 : Array ℕ := #[148185105,18695186,43876370,36005910,82117650,345086,71666710,345086,117778450,353278,354302,353278,109907990,345086,354302,345086,148185106,135089174,362494,362494,363518,345086,362494,345086,148185110,353278,354302,353278,363518,345086,354302,345086]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells5_12_ok : scan (2^5) (fun m => test 5 410 m [7232,15424,3264,5312,7360,12480,13504,15552,28864,7616,11712,15808,16320,5256,7304,6344,7368,10440,14536,6536,7560,7624,14792,6488,7512,7640,7672] cells5_12[m]!) = true := by decide +kernel

theorem level6 : Census 6 [7232,15424,3264,5312,7360,12480,13504,15552,28864,7616,11712,15808,16320,5256,7304,6344,7368,10440,14536,6536,7560,7624,14792,6488,7512,7640,7672] := by
  apply step level5
  apply row_cons cells5_0 cells5_0_ok
  apply row_cons cells5_1 cells5_1_ok
  apply row_cons cells5_2 cells5_2_ok
  apply row_cons cells5_3 cells5_3_ok
  apply row_cons cells5_4 cells5_4_ok
  apply row_cons cells5_5 cells5_5_ok
  apply row_cons cells5_6 cells5_6_ok
  apply row_cons cells5_7 cells5_7_ok
  apply row_cons cells5_8 cells5_8_ok
  apply row_cons cells5_9 cells5_9_ok
  apply row_cons cells5_10 cells5_10_ok
  apply row_cons cells5_11 cells5_11_ok
  apply row_cons cells5_12 cells5_12_ok
  exact rows_nil

def cells6_0 : Array ℕ := #[26878975,27478015,219816896,219816897,219759552,219759553,219816899,1796875205,219243456,219243457,219358147,1796874240,218842051,1796816896,219816900,1796875216,26878975,427006,203043777,427006,202986433,427006,1796874241,427006,147921857,427006,1796874242,427006,1796816898,427006,1796874243,427006,26878975,435198,436222,435198,437246,435198,436222,435198,118604736,435198,436222,435198,437246,435198,436222,435198,26878975,427006,436222,427006,437246,427006,436222,427006,147921857,427006,436222,427006,437246,427006,436222,427006]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_0_ok : scan (2^6) (fun m => test 6 7232 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_0[m]!) = true := by decide +kernel

def cells6_1 : Array ℕ := #[26878975,27478015,219816896,219816897,219759552,219759553,219816899,1561994192,219243456,219243457,219358147,1561535440,218842051,1561019344,219816900,1796875217,26878975,427006,203043777,427006,202986433,427006,1545220099,427006,202470337,427006,1544761347,427006,1544245251,427006,1796874244,427006,26878975,435198,436222,435198,437246,435198,436222,435198,438270,435198,436222,435198,437246,435198,436222,435198,26878975,427006,436222,427006,437246,427006,436222,427006,438270,427006,436222,427006,437246,427006,436222,427006]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_1_ok : scan (2^6) (fun m => test 6 15424 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_1[m]!) = true := by decide +kernel

def cells6_2 : Array ℕ := #[26878975,28077055,28077055,28077055,161024963,43883459,10329027,278764485,160501699,47553475,13999043,282434501,1796875208,1796874245,1796867077,1796875214,26878975,427006,428030,427006,177806275,427006,428030,427006,181476291,427006,428030,427006,1645916165,427006,428030,427006,26878975,435198,436222,435198,144251843,435198,436222,435198,147921859,435198,436222,435198,1645908997,435198,436222,435198,26878975,427006,428030,427006,1486429125,427006,428030,427006,1490099141,427006,428030,427006,1645917134,427006,428030,427006]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_2_ok : scan (2^6) (fun m => test 6 3264 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_2[m]!) = true := by decide +kernel

def cells6_3 : Array ℕ := #[26878975,73315264,161089473,43947971,194579393,73315267,1796874246,1796874247,187838402,224610242,1796875206,1796874248,1767457734,1767456776,1796874249,1796875215,26878975,427006,428030,427006,194579393,427006,428030,427006,181017539,427006,428030,427006,1796875219,427006,428030,427006,26878975,435198,161089473,435198,437246,435198,437246,435198,147921859,435198,1767457747,435198,437246,435198,437246,435198,26878975,427006,428030,427006,437246,427006,428030,427006,1490098176,427006,428030,427006,437246,427006,428030,427006]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_3_ok : scan (2^6) (fun m => test 6 5312 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_3[m]!) = true := by decide +kernel

def cells6_4 : Array ℕ := #[26878975,161096641,161089473,278828997,161024963,1561993223,1561986055,1796874250,160501699,1561534472,1561527304,1796874251,1796874252,1796875209,1796868041,1796874253,26878975,427006,428030,427006,1486428161,427006,428030,427006,181476292,427006,428030,427006,1796875220,427006,428030,427006,26878975,435198,436222,435198,437246,435198,436222,435198,147921859,435198,436222,435198,437246,435198,436222,435198,26878975,427006,428030,427006,437246,427006,428030,427006,1490099152,427006,428030,427006,437246,427006,428030,427006]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_4_ok : scan (2^6) (fun m => test 6 7360 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_4[m]!) = true := by decide +kernel

def cells6_5 : Array ℕ := #[26878975,161096641,161089473,1561994184,193489857,1503216582,1503152070,1561993228,193482689,1502700486,1502635974,1561534476,1296591816,1296590860,1296132108,1796874254,26878975,427006,428030,427006,80271297,427006,428030,427006,109631425,427006,428030,427006,1183365125,427006,428030,427006,26878975,5952449,35312577,1377474565,437246,437246,437246,437246,438270,438270,438270,438270,437246,437246,437246,437246,26878975,427006,428030,427006,437246,427006,428030,427006,438270,427006,428030,427006,437246,427006,428030,427006]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_5_ok : scan (2^6) (fun m => test 6 12480 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_5[m]!) = true := by decide +kernel

def cells6_6 : Array ℕ := #[26878975,161096641,161089473,1561993221,161024963,1503215624,1561986057,1561994185,160501699,1502699528,1561527305,1561535433,1267230732,1796875211,1796875213,1796874255,26878975,427006,428030,427006,1486428162,427006,428030,427006,1490098178,427006,428030,427006,1267231700,427006,428030,427006,26878975,435198,161089473,435198,437246,435198,437246,435198,438270,435198,438270,435198,437246,435198,437246,435198,26878975,427006,428030,427006,437246,427006,428030,427006,438270,427006,428030,427006,437246,427006,428030,427006]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_6_ok : scan (2^6) (fun m => test 6 13504 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_6[m]!) = true := by decide +kernel

def cells6_7 : Array ℕ := #[26878975,161096641,161089473,1561994190,161024963,1561994191,1561987023,1561993229,160501699,1561535439,1561528271,1561534477,1561993230,1561993231,1561986063,1796874256,26878975,427006,428030,427006,1486428163,427006,428030,427006,1490098179,427006,428030,427006,1796874257,427006,428030,427006,26878975,435198,436222,435198,437246,435198,436222,435198,438270,435198,436222,435198,437246,435198,436222,435198,26878975,427006,428030,427006,437246,427006,428030,427006,438270,427006,428030,427006,437246,427006,428030,427006]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_7_ok : scan (2^6) (fun m => test 6 15552 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_7[m]!) = true := by decide +kernel

def cells6_8 : Array ℕ := #[26878975,5952449,35312577,1377488901,80271297,1561994195,1561987027,1561994196,109631425,1561535443,1561528275,1561535444,1183372293,1296591828,1296133076,1561993233,26878975,427006,428030,427006,80271297,427006,428030,427006,109631425,427006,428030,427006,1183373262,427006,428030,427006,26878975,5952449,35312577,1377489870,437246,437246,437246,437246,438270,438270,438270,438270,437246,437246,437246,437246,439294,427006,428030,427006,437246,427006,428030,427006,438270,427006,428030,427006,437246,427006,428030,427006]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_8_ok : scan (2^6) (fun m => test 6 28864 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_8[m]!) = true := by decide +kernel

def cells6_9 : Array ℕ := #[26878975,1503273925,1503266757,1503272970,1503202245,1503215626,1503151114,1796874258,160501700,1502700491,1502635979,1796875207,1502112715,1796817863,1796753351,1796874259,26878975,427006,428030,427006,429054,427006,428030,427006,181476292,427006,428030,427006,429054,427006,428030,427006,26878975,435198,436222,435198,437246,435198,436222,435198,147921860,435198,436222,435198,437246,435198,436222,435198,26878975,427006,428030,427006,429054,427006,428030,427006,1490099153,427006,428030,427006,429054,427006,428030,427006]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_9_ok : scan (2^6) (fun m => test 6 7616 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_9[m]!) = true := by decide +kernel

def cells6_10 : Array ℕ := #[26878975,1503272960,1503265792,1503272971,194579396,1503216585,1503152073,1561994183,160501700,1267819465,1267754953,1297294279,1502112717,1796875210,1796868042,1796874260,26878975,427006,428030,427006,429054,427006,428030,427006,1267796995,427006,428030,427006,429054,427006,428030,427006,26878975,435198,436222,435198,1503201283,435198,436222,435198,438270,435198,436222,435198,438270,435198,436222,435198,26878975,427006,428030,427006,429054,427006,428030,427006,438270,427006,428030,427006,429054,427006,428030,427006]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_10_ok : scan (2^6) (fun m => test 6 11712 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_10[m]!) = true := by decide +kernel

def cells6_11 : Array ℕ := #[26878975,1503273936,1503266768,1503272973,1503202256,1503215629,1503151117,1561993235,160501700,1502699535,1502635023,1561993236,1502111759,1561935892,1561871380,1796874261,26878975,427006,428030,427006,429054,427006,428030,427006,1490098180,427006,428030,427006,429054,427006,428030,427006,26878975,435198,436222,435198,437246,435198,436222,435198,438270,435198,436222,435198,437246,435198,436222,435198,26878975,427006,428030,427006,429054,427006,428030,427006,438270,427006,428030,427006,429054,427006,428030,427006]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_11_ok : scan (2^6) (fun m => test 6 15808 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_11[m]!) = true := by decide +kernel

def cells6_12 : Array ℕ := #[26878975,1503273937,1503266769,1503272976,1503202257,1503215632,1503151120,1503272981,1502678993,1502699536,1502635024,1502814229,1502111760,1502298133,1501774869,1796875218,26878975,427006,428030,427006,429054,427006,428030,427006,430078,427006,428030,427006,429054,427006,428030,427006,26878975,435198,436222,435198,437246,435198,436222,435198,438270,435198,436222,435198,437246,435198,436222,435198,26878975,427006,428030,427006,429054,427006,428030,427006,430078,427006,428030,427006,429054,427006,428030,427006]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_12_ok : scan (2^6) (fun m => test 6 16320 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_12[m]!) = true := by decide +kernel

def cells6_13 : Array ℕ := #[150086592,145962944,183780289,43833283,69625794,85895107,279173062,43825160,182634434,418814,451068870,418814,1796874262,418814,1796874263,418814,183583681,144299971,428030,428030,144292806,144291848,428030,428030,1490099142,418814,428030,418814,1784315927,418814,428030,418814,150086592,435198,47498179,435198,437246,435198,437246,435198,118884291,418814,1389631496,418814,437246,418814,437246,418814,147964867,435198,428030,435198,437246,435198,428030,435198,1490098184,418814,428030,418814,437246,418814,428030,418814]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_13_ok : scan (2^6) (fun m => test 6 5256 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_13[m]!) = true := by decide +kernel

def cells6_14 : Array ℕ := #[150086592,45324225,11827137,279172096,71733186,43832328,279172104,279172107,118884291,418814,392578003,418814,1560423447,418814,1796875212,418814,148251587,157173715,428030,428030,1556746263,1793198028,428030,428030,1490098185,418814,428030,418814,1796874264,418814,428030,418814,150086592,435198,436222,435198,437246,435198,436222,435198,118884291,418814,436222,418814,437246,418814,436222,418814,148251587,435198,428030,435198,437246,435198,428030,435198,1490099151,418814,428030,418814,437246,418814,428030,418814]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_14_ok : scan (2^6) (fun m => test 6 7304 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_14[m]!) = true := by decide +kernel

def cells6_15 : Array ℕ := #[150086593,45324225,11769795,10393540,544453574,73307145,43832332,43826121,993134534,418814,380018711,418814,1796874265,418814,1796874266,418814,183641027,427006,428030,427006,1257310231,427006,428030,427006,1490141196,418814,428030,418814,1616090138,418814,428030,418814,150086593,186303490,436222,436222,437246,437246,436222,436222,1461067785,418814,436222,418814,437246,418814,436222,418814,181806020,427006,428030,427006,437246,427006,428030,427006,1490099145,418814,428030,418814,437246,418814,428030,418814]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_15_ok : scan (2^6) (fun m => test 6 6344 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_15[m]!) = true := by decide +kernel

def cells6_16 : Array ℕ := #[150086593,45324225,280204288,43947984,73307144,73308111,43833289,43832333,1461067784,418814,280276940,418814,1490098202,418814,1796874267,418814,1257381888,427006,428030,427006,1257311180,427006,428030,427006,1490142153,418814,428030,418814,1490098203,418814,428030,418814,150086593,435198,436222,435198,437246,435198,436222,435198,1461068751,418814,436222,418814,437246,418814,436222,418814,1490428880,427006,428030,427006,437246,427006,428030,427006,1490141197,418814,428030,418814,437246,418814,428030,418814]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_16_ok : scan (2^6) (fun m => test 6 7368 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_16[m]!) = true := by decide +kernel

def cells6_17 : Array ℕ := #[150086593,186017729,118924225,290884609,1503215638,178504727,379961367,279760844,156633025,418814,840347649,418814,950584343,418814,379962316,418814,169226177,427006,428030,427006,1250020375,427006,428030,427006,1180046337,418814,428030,418814,950585292,418814,428030,418814,148251585,1347842049,436222,436222,1486471191,178505676,436222,436222,438270,418814,436222,418814,438270,418814,436222,418814,1490427905,427006,428030,427006,1486472140,427006,428030,427006,438270,418814,428030,418814,438270,418814,428030,418814]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_17_ok : scan (2^6) (fun m => test 6 10440 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_17[m]!) = true := by decide +kernel

def cells6_18 : Array ℕ := #[150086593,187851778,292835283,1347670996,1503215639,1351340056,1561993242,1561993243,963659731,418814,380019660,418814,1544187930,418814,1796874268,418814,1244802050,427006,428030,427006,1486471192,427006,428030,427006,1490142164,418814,428030,418814,1183372315,418814,428030,418814,150086593,1347842051,436222,436222,437246,437246,436222,436222,438270,418814,436222,418814,437246,418814,436222,418814,1490427907,427006,428030,427006,437246,427006,428030,427006,438270,418814,428030,418814,437246,418814,428030,418814]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_18_ok : scan (2^6) (fun m => test 6 14536 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_18[m]!) = true := by decide +kernel

def cells6_19 : Array ℕ := #[150086595,187910088,83198915,43954188,49644483,73314316,49644484,573340619,993019848,418814,847687692,418814,877047820,418814,585898955,418814,183641027,157172748,428030,428030,429054,429054,428030,428030,960906252,418814,428030,418814,429054,418814,428030,418814,150086595,186532876,436222,436222,437246,437246,436222,436222,990266380,418814,436222,418814,437246,418814,436222,418814,150086596,1477540811,428030,428030,429054,429054,428030,428030,1490099147,418814,428030,418814,429054,418814,428030,418814]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_19_ok : scan (2^6) (fun m => test 6 6536 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_19[m]!) = true := by decide +kernel

def cells6_20 : Array ℕ := #[150086595,74683397,280204296,43947977,544445448,73308105,573863883,73193415,993018892,418814,1501703194,418814,1501645850,418814,585941020,418814,150086596,157173716,428030,428030,429054,429054,428030,428030,1490099149,418814,428030,418814,429054,418814,428030,418814,150086595,435198,436222,435198,437246,435198,436222,435198,1490141198,418814,436222,418814,437246,418814,436222,418814,150086596,435198,428030,435198,429054,435198,428030,435198,1490098191,418814,428030,418814,429054,418814,428030,418814]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_20_ok : scan (2^6) (fun m => test 6 7560 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_20[m]!) = true := by decide +kernel

def cells6_21 : Array ℕ := #[1492263877,74691534,280211467,43954189,544452619,73314317,73315271,73314323,1490142155,418814,1501703196,418814,1501645852,418814,1796874269,418814,1257382864,427006,428030,427006,429054,427006,428030,427006,1255260175,418814,428030,418814,429054,418814,428030,418814,1492263888,435198,436222,435198,437246,435198,436222,435198,1490141199,418814,436222,418814,437246,418814,436222,418814,1492263889,427006,428030,427006,429054,427006,428030,427006,1490141200,418814,428030,418814,429054,418814,428030,418814]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_21_ok : scan (2^6) (fun m => test 6 7624 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_21[m]!) = true := by decide +kernel

def cells6_22 : Array ℕ := #[1492262913,187910100,1503273932,1503272987,1503216588,1503215643,585539612,1561993245,963659732,418814,1266822171,418814,1266764827,418814,1296182301,418814,1244802051,427006,428030,427006,429054,427006,428030,427006,1490141201,418814,428030,418814,429054,418814,428030,418814,1492262915,1242680337,436222,436222,437246,437246,436222,436222,438270,418814,436222,418814,437246,418814,436222,418814,1492262916,427006,428030,427006,429054,427006,428030,427006,438270,418814,428030,418814,429054,418814,428030,418814]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_22_ok : scan (2^6) (fun m => test 6 14792 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_22[m]!) = true := by decide +kernel

def cells6_23 : Array ℕ := #[1492262918,74740745,339046409,280212429,573934601,544518093,573935565,573340618,993069065,418814,419838,418814,877047832,418814,419838,418814,1257374729,427006,1116122136,427006,429054,427006,429054,427006,1198540749,418814,419838,418814,429054,418814,419838,418814,1492262921,1351519256,436222,436222,437246,437246,436222,436222,1462846413,418814,419838,418814,437246,418814,419838,418814,1492263885,427006,436222,427006,429054,427006,436222,427006,1490099146,418814,419838,418814,429054,418814,419838,418814]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_23_ok : scan (2^6) (fun m => test 6 6488 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_23[m]!) = true := by decide +kernel

def cells6_24 : Array ℕ := #[1492262919,74741711,280205257,45323279,544503753,74740751,573863882,73651220,993084361,418814,419838,418814,993069083,418814,419838,418814,1257382857,427006,1257374747,427006,429054,427006,429054,427006,1198662602,418814,419838,418814,429054,418814,419838,418814,1492263887,435198,436222,435198,437246,435198,436222,435198,1462845455,418814,419838,418814,437246,418814,419838,418814,1492262927,427006,436222,427006,429054,427006,436222,427006,1490141204,418814,419838,418814,429054,418814,419838,418814]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_24_ok : scan (2^6) (fun m => test 6 7512 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_24[m]!) = true := by decide +kernel

def cells6_25 : Array ℕ := #[1492262922,45330445,280211469,280211472,573813703,74690580,338931732,278835221,993141703,418814,419838,418814,993069085,418814,419838,418814,1257381901,427006,428030,427006,429054,427006,428030,427006,1198661652,418814,419838,418814,429054,418814,419838,418814,1492262925,435198,436222,435198,437246,435198,436222,435198,1462902804,418814,419838,418814,437246,418814,419838,418814,1492262928,427006,428030,427006,429054,427006,428030,427006,1490427925,418814,419838,418814,429054,418814,419838,418814]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_25_ok : scan (2^6) (fun m => test 6 7640 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_25[m]!) = true := by decide +kernel

def cells6_26 : Array ℕ := #[1492262930,74812435,339053587,280333333,573934611,544574485,573934613,573935570,993140755,418814,419838,418814,420862,418814,419838,418814,1257381907,427006,428030,427006,429054,427006,428030,427006,1198661653,418814,419838,418814,420862,418814,419838,418814,1492262931,435198,436222,435198,437246,435198,436222,435198,1462902805,418814,419838,418814,420862,418814,419838,418814,1492262933,427006,428030,427006,429054,427006,428030,427006,1492263890,418814,419838,418814,420862,418814,419838,418814]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells6_26_ok : scan (2^6) (fun m => test 6 7672 m [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] cells6_26[m]!) = true := by decide +kernel

theorem level7 : Census 7 [367680,728128,859200,990272,998464,429248,201920,234688,365760,464064,236736,367808,400576,498880,504000,505024,507072,933056,236992,499136,503232,507328,398472,464008,924808,399560,465096,466120,473288,466376] := by
  apply step level6
  apply row_cons cells6_0 cells6_0_ok
  apply row_cons cells6_1 cells6_1_ok
  apply row_cons cells6_2 cells6_2_ok
  apply row_cons cells6_3 cells6_3_ok
  apply row_cons cells6_4 cells6_4_ok
  apply row_cons cells6_5 cells6_5_ok
  apply row_cons cells6_6 cells6_6_ok
  apply row_cons cells6_7 cells6_7_ok
  apply row_cons cells6_8 cells6_8_ok
  apply row_cons cells6_9 cells6_9_ok
  apply row_cons cells6_10 cells6_10_ok
  apply row_cons cells6_11 cells6_11_ok
  apply row_cons cells6_12 cells6_12_ok
  apply row_cons cells6_13 cells6_13_ok
  apply row_cons cells6_14 cells6_14_ok
  apply row_cons cells6_15 cells6_15_ok
  apply row_cons cells6_16 cells6_16_ok
  apply row_cons cells6_17 cells6_17_ok
  apply row_cons cells6_18 cells6_18_ok
  apply row_cons cells6_19 cells6_19_ok
  apply row_cons cells6_20 cells6_20_ok
  apply row_cons cells6_21 cells6_21_ok
  apply row_cons cells6_22 cells6_22_ok
  apply row_cons cells6_23 cells6_23_ok
  apply row_cons cells6_24 cells6_24_ok
  apply row_cons cells6_25 cells6_25_ok
  apply row_cons cells6_26 cells6_26_ok
  exact rows_nil

def cells7_0 : Array ℕ := #[31073279,31672319,253371328,111663040,253313984,48741313,253371331,82295747,252797888,44554177,252912579,111663043,252396483,2103059402,253371332,111591375,31073279,492542,236598209,492542,144252865,492542,1809336265,492542,147922881,492542,1573939145,492542,1808296909,492542,2103052234,492542,31073279,500734,501758,500734,502782,500734,501758,500734,164696000,500734,501758,500734,502782,500734,501758,500734,31073279,492542,501758,492542,502782,492542,501758,492542,147922881,492542,501758,492542,502782,492542,501758,492542,31073279,508926,509950,508926,165219264,508926,509950,508926,511998,508926,509950,508926,511998,508926,509950,508926,31073279,492542,509950,492542,144252865,492542,509950,492542,511998,492542,509950,492542,511998,492542,509950,492542,31073279,500734,501758,500734,502782,500734,501758,500734,511998,500734,501758,500734,502782,500734,501758,500734,31073279,492542,501758,492542,502782,492542,501758,492542,511998,492542,501758,492542,502782,492542,501758,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_0_ok : scan (2^7) (fun m => test 7 367680 m [] cells7_0[m]!) = true := by decide +kernel

def cells7_1 : Array ℕ := #[31073279,31672319,253371328,253371329,253313984,253313985,157270977,2065310661,252797888,252797889,252912579,2073577417,252396483,2073570249,253371332,284554188,31073279,492542,236598209,492542,236540865,492542,2082091973,492542,236024769,492542,2103199689,492542,2103192521,492542,418309068,492542,31073279,500734,501758,500734,502782,500734,501758,500734,101839808,500734,501758,500734,502782,500734,501758,500734,31073279,492542,501758,492542,502782,492542,501758,492542,236024769,492542,501758,492542,502782,492542,501758,492542,31073279,31672319,509950,509950,510974,510974,509950,509950,118612928,252797889,509950,509950,510974,510974,509950,509950,513022,492542,509950,492542,510974,492542,509950,492542,513022,492542,509950,492542,510974,492542,509950,492542,31073279,500734,501758,500734,502782,500734,501758,500734,118612928,500734,501758,500734,502782,500734,501758,500734,513022,492542,501758,492542,502782,492542,501758,492542,513022,492542,501758,492542,502782,492542,501758,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_1_ok : scan (2^7) (fun m => test 7 728128 m [] cells7_1[m]!) = true := by decide +kernel

def cells7_2 : Array ℕ := #[31073279,31672319,253371328,253371329,253313984,253313985,253371331,2065310661,236024768,252797889,236139459,1603299273,252396483,2073061325,253371332,1868777417,31073279,492542,236139457,492542,236540865,492542,1868318665,492542,236024769,492542,2081633221,492542,2103199693,492542,1602381769,492542,31073279,500734,501758,500734,502782,500734,501758,500734,30511040,500734,501758,500734,502782,500734,501758,500734,31073279,492542,501758,492542,502782,492542,501758,492542,105970625,492542,501758,492542,502782,492542,501758,492542,31073279,31672319,509950,509950,253313984,73201601,509950,509950,511998,511998,509950,509950,511998,511998,509950,509950,513022,492542,509950,492542,513022,492542,509950,492542,511998,492542,509950,492542,511998,492542,509950,492542,31073279,500734,501758,500734,502782,500734,501758,500734,511998,500734,501758,500734,502782,500734,501758,500734,513022,492542,501758,492542,502782,492542,501758,492542,511998,492542,501758,492542,502782,492542,501758,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_2_ok : scan (2^7) (fun m => test 7 859200 m [] cells7_2[m]!) = true := by decide +kernel

def cells7_3 : Array ℕ := #[31073279,31672319,253371328,253371329,253313984,253313985,253371331,2065310661,252797888,252797889,252912579,1868171210,252396483,1868106698,253371332,2065310672,31073279,492542,236598209,492542,236540865,492542,418366412,492542,147922881,492542,1573021641,492542,1572957129,492542,1602439111,492542,31073279,500734,501758,500734,502782,500734,501758,500734,118612928,500734,501758,500734,502782,500734,501758,500734,31073279,492542,501758,492542,502782,492542,501758,492542,236024769,492542,501758,492542,502782,492542,501758,492542,31073279,31672319,509950,509950,510974,510974,509950,509950,511998,511998,509950,509950,510974,510974,509950,509950,513022,492542,509950,492542,510974,492542,509950,492542,511998,492542,509950,492542,510974,492542,509950,492542,31073279,500734,501758,500734,502782,500734,501758,500734,511998,500734,501758,500734,502782,500734,501758,500734,513022,492542,501758,492542,502782,492542,501758,492542,511998,492542,501758,492542,502782,492542,501758,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_3_ok : scan (2^7) (fun m => test 7 990272 m [] cells7_3[m]!) = true := by decide +kernel

def cells7_4 : Array ℕ := #[31073279,31672319,253371328,253371329,253313984,253313985,253371331,1595548624,252797888,252797889,252912579,1595089872,252396483,1594573776,253371332,2065310673,31073279,492542,236598209,492542,236540865,492542,1847210960,492542,236024769,492542,1846752208,492542,1846236112,492542,2082091985,492542,31073279,500734,501758,500734,502782,500734,501758,500734,503806,500734,501758,500734,502782,500734,501758,500734,31073279,492542,501758,492542,502782,492542,501758,492542,503806,492542,501758,492542,502782,492542,501758,492542,31073279,31672319,509950,509950,510974,510974,509950,509950,511998,511998,509950,509950,510974,510974,509950,509950,513022,492542,509950,492542,510974,492542,509950,492542,511998,492542,509950,492542,510974,492542,509950,492542,31073279,500734,501758,500734,502782,500734,501758,500734,503806,500734,501758,500734,502782,500734,501758,500734,513022,492542,501758,492542,502782,492542,501758,492542,503806,492542,501758,492542,502782,492542,501758,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_4_ok : scan (2^7) (fun m => test 7 998464 m [] cells7_4[m]!) = true := by decide +kernel

def cells7_5 : Array ℕ := #[31073279,32271359,32271359,32271359,82639809,82639809,82639809,82639809,111999937,111999937,111999937,111999937,2065310664,380435400,2098865101,2065310670,31073279,492542,493566,492542,177807299,492542,493566,492542,181477315,492542,493566,492542,1304980436,492542,493566,492542,31073279,500734,501758,500734,144252867,500734,501758,500734,147922883,500734,501758,500734,1573415892,500734,501758,500734,31073279,492542,493566,492542,1486430149,492542,493566,492542,1490100165,492542,493566,492542,1914352590,492542,493566,492542,31073279,508926,32271359,508926,510974,508926,510974,508926,511998,508926,511998,508926,510974,508926,510974,508926,31073279,492542,493566,492542,510974,492542,493566,492542,511998,492542,493566,492542,510974,492542,493566,492542,31073279,500734,501758,500734,510974,500734,501758,500734,511998,500734,501758,500734,510974,500734,501758,500734,31073279,492542,493566,492542,510974,492542,493566,492542,511998,492542,493566,492542,510974,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_5_ok : scan (2^7) (fun m => test 7 429248 m [] cells7_5[m]!) = true := by decide +kernel

def cells7_6 : Array ℕ := #[31073279,32870399,32870399,32870399,32870399,32870399,32870399,32870399,188362690,73244610,69115842,82231235,35569602,49192899,16097219,573939658,31073279,492542,493566,492542,35641280,492542,493566,492542,223944642,492542,493566,492542,262874050,492542,493566,492542,31073279,500734,69194688,500734,502782,500734,502782,500734,219815874,500734,262357954,500734,502782,500734,502782,500734,31073279,492542,493566,492542,502782,492542,493566,492542,214056899,492542,493566,492542,502782,492542,493566,492542,31073279,73380800,509950,509950,510974,510974,509950,509950,186269634,258164674,509950,509950,510974,510974,509950,509950,31073279,492542,493566,492542,510974,492542,493566,492542,181018563,492542,493566,492542,510974,492542,493566,492542,31073279,500734,509950,500734,502782,500734,509950,500734,147922883,500734,509950,500734,502782,500734,509950,500734,31073279,492542,493566,492542,502782,492542,493566,492542,1796284362,492542,493566,492542,502782,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_6_ok : scan (2^7) (fun m => test 7 201920 m [] cells7_6[m]!) = true := by decide +kernel

def cells7_7 : Array ℕ := #[31073279,32870399,32870399,32870399,32870399,32870399,32870399,32870399,188362690,73244610,82173891,82173891,49078211,49078211,15523780,2065310671,31073279,492542,493566,492542,198773697,492542,493566,492542,181018563,492542,493566,492542,2065310675,492542,493566,492542,31073279,500734,165283777,500734,502782,500734,502782,500734,147922883,500734,2035893203,500734,502782,500734,502782,500734,31073279,492542,493566,492542,502782,492542,493566,492542,215031748,492542,493566,492542,502782,492542,493566,492542,31073279,508926,509950,508926,510974,508926,509950,508926,186269634,508926,509950,508926,510974,508926,509950,508926,31073279,492542,493566,492542,510974,492542,493566,492542,181018563,492542,493566,492542,510974,492542,493566,492542,31073279,500734,509950,500734,502782,500734,509950,500734,147922883,500734,509950,500734,502782,500734,509950,500734,31073279,492542,493566,492542,502782,492542,493566,492542,1952291791,492542,493566,492542,502782,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_7_ok : scan (2^7) (fun m => test 7 234688 m [] cells7_7[m]!) = true := by decide +kernel

def cells7_8 : Array ℕ := #[31073279,83672000,83672000,83672000,198773697,50174913,82295747,82181059,188362690,106403778,111663043,111663043,2035893190,585956294,2098399177,2065310671,31073279,492542,493566,492542,198773697,492542,493566,492542,181018563,492542,493566,492542,1299779532,492542,493566,492542,31073279,500734,164825025,500734,502782,500734,502782,500734,164696003,500734,1506830291,500734,502782,500734,502782,500734,31073279,492542,493566,492542,502782,492542,493566,492542,1503077321,492542,493566,492542,502782,492542,493566,492542,31073279,508926,509950,508926,198773697,508926,509950,508926,511998,508926,509950,508926,511998,508926,509950,508926,31073279,492542,493566,492542,198773697,492542,493566,492542,511998,492542,493566,492542,511998,492542,493566,492542,31073279,500734,509950,500734,502782,500734,509950,500734,511998,500734,509950,500734,502782,500734,509950,500734,31073279,492542,493566,492542,502782,492542,493566,492542,511998,492542,493566,492542,502782,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_8_ok : scan (2^7) (fun m => test 7 365760 m [] cells7_8[m]!) = true := by decide +kernel

def cells7_9 : Array ℕ := #[31073279,188434368,165283777,83672001,198773697,50174913,16620483,15530948,188362690,258164674,1595082694,1863518153,1330318278,1867189193,2098857931,49078217,31073279,492542,493566,492542,198773697,492542,493566,492542,181018563,492542,493566,492542,2103658444,492542,493566,492542,31073279,500734,165283777,500734,502782,500734,502782,500734,147922883,500734,2099981260,500734,502782,500734,502782,500734,31073279,492542,493566,492542,502782,492542,493566,492542,1502037965,492542,493566,492542,502782,492542,493566,492542,31073279,73380800,509950,509950,510974,510974,509950,509950,511998,511998,509950,509950,510974,510974,509950,509950,31073279,492542,493566,492542,510974,492542,493566,492542,511998,492542,493566,492542,510974,492542,493566,492542,31073279,500734,509950,500734,502782,500734,509950,500734,511998,500734,509950,500734,502782,500734,509950,500734,31073279,492542,493566,492542,502782,492542,493566,492542,511998,492542,493566,492542,502782,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_9_ok : scan (2^7) (fun m => test 7 464064 m [] cells7_9[m]!) = true := by decide +kernel

def cells7_10 : Array ℕ := #[31073279,32870399,32870399,32870399,32870399,32870399,32870399,32870399,164696003,82231235,82231235,82231235,15122372,48676804,15122372,82231248,31073279,492542,493566,492542,1809386437,492542,493566,492542,181477316,492542,493566,492542,1808296907,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,147922883,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,502782,492542,493566,492542,215031748,492542,493566,492542,502782,492542,493566,492542,31073279,508926,509950,508926,510974,508926,509950,508926,147922883,508926,509950,508926,510974,508926,509950,508926,31073279,492542,493566,492542,510974,492542,493566,492542,181477316,492542,493566,492542,510974,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,147922883,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,502782,492542,493566,492542,1490100176,492542,493566,492542,502782,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_10_ok : scan (2^7) (fun m => test 7 236736 m [] cells7_10[m]!) = true := by decide +kernel

def cells7_11 : Array ℕ := #[31073279,113039296,113039296,113039296,165219267,82295747,82295747,82295747,164696003,111663043,111663043,111663043,279377867,2065310665,2065303497,111591375,31073279,492542,493566,492542,232328132,492542,493566,492542,198250436,492542,493566,492542,1808296909,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,164696003,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,502782,492542,493566,492542,246722508,492542,493566,492542,502782,492542,493566,492542,31073279,508926,509950,508926,165219267,508926,509950,508926,511998,508926,509950,508926,511998,508926,509950,508926,31073279,492542,493566,492542,250399692,492542,493566,492542,511998,492542,493566,492542,511998,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,511998,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,502782,492542,493566,492542,511998,492542,493566,492542,502782,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_11_ok : scan (2^7) (fun m => test 7 367808 m [] cells7_11[m]!) = true := by decide +kernel

def cells7_12 : Array ℕ := #[31073279,83672001,83672001,83672001,231238593,50117571,16563139,15186884,231231425,1775330246,1775265734,279435211,1334340552,2065310665,2065303497,573896647,31073279,492542,493566,492542,231238593,492542,493566,492542,109640641,492542,493566,492542,2065310676,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,231231425,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,502782,492542,493566,492542,109640641,492542,493566,492542,502782,492542,493566,492542,31073279,165290945,165283777,278722501,510974,510974,510974,510974,511998,511998,511998,511998,510974,510974,510974,510974,31073279,492542,493566,492542,510974,492542,493566,492542,511998,492542,493566,492542,510974,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,511998,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,502782,492542,493566,492542,511998,492542,493566,492542,502782,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_12_ok : scan (2^7) (fun m => test 7 400576 m [] cells7_12[m]!) = true := by decide +kernel

def cells7_13 : Array ℕ := #[31073279,165290945,165283777,83672001,165219267,1863984079,1863976911,82295760,164696003,1863525327,1863518159,111655887,574412743,2065310665,2065303497,16829260757,31073279,492542,493566,492542,82173900,492542,493566,492542,181477316,492542,493566,492542,2065310676,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,147922883,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,502782,492542,493566,492542,1490100176,492542,493566,492542,502782,492542,493566,492542,31073279,508926,509950,508926,510974,508926,509950,508926,511998,508926,509950,508926,510974,508926,509950,508926,31073279,492542,493566,492542,510974,492542,493566,492542,511998,492542,493566,492542,510974,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,511998,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,502782,492542,493566,492542,511998,492542,493566,492542,502782,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_13_ok : scan (2^7) (fun m => test 7 498880 m [] cells7_13[m]!) = true := by decide +kernel

def cells7_14 : Array ℕ := #[31073279,165290945,165283777,1595548616,197684161,1507410886,1507346374,573366215,197676993,1506894790,1506830278,841801671,1330146248,111534023,379969479,573373383,31073279,492542,493566,492542,80279489,492542,493566,492542,109639617,492542,493566,492542,1808296910,492542,493566,492542,31073279,5960641,35320769,1775903694,502782,502782,502782,502782,503806,503806,503806,503806,502782,502782,502782,502782,31073279,492542,493566,492542,502782,492542,493566,492542,503806,492542,493566,492542,502782,492542,493566,492542,31073279,508926,509950,508926,510974,508926,509950,508926,511998,508926,509950,508926,510974,508926,509950,508926,31073279,492542,493566,492542,510974,492542,493566,492542,511998,492542,493566,492542,510974,492542,493566,492542,31073279,508926,509950,508926,502782,508926,509950,508926,503806,508926,509950,508926,502782,508926,509950,508926,31073279,492542,493566,492542,502782,492542,493566,492542,503806,492542,493566,492542,502782,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_14_ok : scan (2^7) (fun m => test 7 504000 m [] cells7_14[m]!) = true := by decide +kernel

def cells7_15 : Array ℕ := #[31073279,165290945,165283777,1863984078,165219267,1775846351,284998601,1595548617,164696003,1775330255,280804297,1595089865,111663047,2065310667,111663047,379976647,31073279,492542,493566,492542,1299801033,492542,493566,492542,1299792841,492542,493566,492542,1271426004,492542,493566,492542,31073279,500734,165283777,500734,502782,500734,502782,500734,503806,500734,503806,500734,502782,500734,502782,500734,31073279,492542,493566,492542,502782,492542,493566,492542,503806,492542,493566,492542,502782,492542,493566,492542,31073279,508926,509950,508926,510974,508926,509950,508926,511998,508926,509950,508926,510974,508926,509950,508926,31073279,492542,493566,492542,510974,492542,493566,492542,511998,492542,493566,492542,510974,492542,493566,492542,31073279,500734,509950,500734,502782,500734,509950,500734,503806,500734,509950,500734,502782,500734,509950,500734,31073279,492542,493566,492542,502782,492542,493566,492542,503806,492542,493566,492542,502782,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_15_ok : scan (2^7) (fun m => test 7 505024 m [] cells7_15[m]!) = true := by decide +kernel

def cells7_16 : Array ℕ := #[31073279,165290945,165283777,1595548622,165219267,1595548623,1595541455,14480450517,164696003,1595089871,1595082703,14479991765,574412743,380098503,111663047,2103059410,31073279,492542,493566,492542,1299915719,492542,493566,492542,1299850183,492542,493566,492542,16829260760,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,503806,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,502782,492542,493566,492542,503806,492542,493566,492542,502782,492542,493566,492542,31073279,508926,509950,508926,510974,508926,509950,508926,511998,508926,509950,508926,510974,508926,509950,508926,31073279,492542,493566,492542,510974,492542,493566,492542,511998,492542,493566,492542,510974,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,503806,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,502782,492542,493566,492542,503806,492542,493566,492542,502782,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_16_ok : scan (2^7) (fun m => test 7 507072 m [] cells7_16[m]!) = true := by decide +kernel

def cells7_17 : Array ℕ := #[31073279,5960641,35320769,1595548622,80280513,1274089420,1274032076,1863984084,109640641,1274088396,1274031052,1863525332,1602776014,1334340564,1333881812,14950212568,31073279,492542,493566,492542,231238593,492542,493566,492542,231231425,492542,493566,492542,1183382478,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,503806,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,502782,492542,493566,492542,503806,492542,493566,492542,502782,492542,493566,492542,31073279,165290945,165283777,1595548622,510974,510974,510974,510974,511998,511998,511998,511998,510974,510974,510974,510974,513022,492542,493566,492542,510974,492542,493566,492542,511998,492542,493566,492542,510974,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,503806,500734,501758,500734,502782,500734,501758,500734,513022,492542,493566,492542,502782,492542,493566,492542,503806,492542,493566,492542,502782,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_17_ok : scan (2^7) (fun m => test 7 933056 m [] cells7_17[m]!) = true := by decide +kernel

def cells7_18 : Array ℕ := #[31073279,32870399,32870399,32870399,32870399,32870399,32870399,32870399,164696004,49651652,16097220,83206084,16097220,49651652,16097220,284532689,31073279,492542,493566,492542,494590,492542,493566,492542,181477316,492542,493566,492542,494590,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,147922884,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,494590,492542,493566,492542,215031748,492542,493566,492542,494590,492542,493566,492542,31073279,508926,509950,508926,510974,508926,509950,508926,147922884,508926,509950,508926,510974,508926,509950,508926,31073279,492542,493566,492542,494590,492542,493566,492542,181477316,492542,493566,492542,494590,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,147922884,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,494590,492542,493566,492542,1490100177,492542,493566,492542,494590,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_18_ok : scan (2^7) (fun m => test 7 236992 m [] cells7_18[m]!) = true := by decide +kernel

def cells7_19 : Array ℕ := #[31073279,1507468229,1507461061,83729360,1507396549,50174928,285055952,285055953,164696004,1506894795,1506830283,2065310663,1506307019,2065253319,2065188807,573373394,31073279,492542,493566,492542,494590,492542,493566,492542,198250436,492542,493566,492542,494590,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,164696004,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,494590,492542,493566,492542,1490100177,492542,493566,492542,494590,492542,493566,492542,31073279,508926,509950,508926,510974,508926,509950,508926,511998,508926,509950,508926,510974,508926,509950,508926,31073279,492542,493566,492542,494590,492542,493566,492542,511998,492542,493566,492542,494590,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,511998,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,494590,492542,493566,492542,511998,492542,493566,492542,494590,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_19_ok : scan (2^7) (fun m => test 7 499136 m [] cells7_19[m]!) = true := by decide +kernel

def cells7_20 : Array ℕ := #[31073279,113089487,381524943,113089487,198773700,1507410889,1507346377,1595548615,164696004,1272013769,1271949257,1330848711,574477255,2065310666,2065303498,16829260758,31073279,492542,493566,492542,494590,492542,493566,492542,1808863184,492542,493566,492542,494590,492542,493566,492542,31073279,500734,501758,500734,1775832016,500734,501758,500734,503806,500734,501758,500734,503806,500734,501758,500734,31073279,492542,493566,492542,494590,492542,493566,492542,503806,492542,493566,492542,494590,492542,493566,492542,31073279,508926,509950,508926,510974,508926,509950,508926,511998,508926,509950,508926,510974,508926,509950,508926,31073279,492542,493566,492542,494590,492542,493566,492542,511998,492542,493566,492542,494590,492542,493566,492542,31073279,500734,501758,500734,510974,500734,501758,500734,503806,500734,501758,500734,510974,500734,501758,500734,31073279,492542,493566,492542,494590,492542,493566,492542,503806,492542,493566,492542,494590,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_20_ok : scan (2^7) (fun m => test 7 503232 m [] cells7_20[m]!) = true := by decide +kernel

def cells7_21 : Array ℕ := #[31073279,1507468240,1507461072,14392370133,1507396560,14392312789,14392248277,574412754,164696004,880596935,876402631,14480450518,842848199,14480393174,14480328662,2103059410,31073279,492542,493566,492542,494590,492542,493566,492542,1808863185,492542,493566,492542,494590,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,503806,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,494590,492542,493566,492542,503806,492542,493566,492542,494590,492542,493566,492542,31073279,508926,509950,508926,510974,508926,509950,508926,511998,508926,509950,508926,510974,508926,509950,508926,31073279,492542,493566,492542,494590,492542,493566,492542,511998,492542,493566,492542,494590,492542,493566,492542,31073279,500734,501758,500734,502782,500734,501758,500734,503806,500734,501758,500734,502782,500734,501758,500734,31073279,492542,493566,492542,494590,492542,493566,492542,503806,492542,493566,492542,494590,492542,493566,492542]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_21_ok : scan (2^7) (fun m => test 7 507328 m [] cells7_21[m]!) = true := by decide +kernel

def cells7_22 : Array ℕ := #[150610880,159067072,184304577,224881601,159261632,163393472,124240833,61665219,163064768,484350,195496897,484350,138295232,484350,37025731,484350,184107969,223308737,493566,493566,122667969,162131907,493566,493566,193924033,484350,493566,484350,137492419,484350,493566,484350,138031040,500734,203902913,500734,502782,500734,502782,500734,146291648,484350,42269635,484350,502782,484350,502782,484350,202330049,500734,493566,500734,502782,500734,493566,500734,142736323,484350,493566,484350,502782,484350,493566,484350,150610880,146487232,182928321,43841475,510974,510974,510974,510974,511998,484350,511998,484350,510974,484350,510974,484350,181355457,144308163,493566,493566,510974,510974,493566,493566,511998,484350,493566,484350,510974,484350,493566,484350,150610880,500734,47506371,500734,502782,500734,502782,500734,511998,484350,511998,484350,502782,484350,502782,484350,147973059,500734,493566,500734,502782,500734,493566,500734,511998,484350,493566,484350,502782,484350,493566,484350]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_22_ok : scan (2^7) (fun m => test 7 398472 m [] cells7_22[m]!) = true := by decide +kernel

def cells7_23 : Array ℕ := #[150610880,159067072,184304577,82295745,125617089,50174913,124240833,338083785,71096257,484350,69720001,484350,37541827,484350,57131972,484350,184107969,144308163,493566,493566,1082914758,557182924,493566,493566,1254810566,484350,493566,484350,2082629580,484350,493566,484350,138031040,500734,111614913,500734,502782,500734,502782,500734,45652929,484350,392568777,484350,502782,484350,502782,484350,147973059,500734,493566,500734,502782,500734,493566,500734,993061836,484350,493566,484350,502782,484350,493566,484350,150610880,146487232,509950,509950,510974,510974,509950,509950,511998,484350,509950,484350,510974,484350,509950,484350,184107969,144308163,493566,493566,510974,510974,493566,493566,511998,484350,493566,484350,510974,484350,493566,484350,150610880,500734,509950,500734,502782,500734,509950,500734,511998,484350,509950,484350,502782,484350,509950,484350,147973059,500734,493566,500734,502782,500734,493566,500734,511998,484350,493566,484350,502782,484350,493566,484350]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_23_ok : scan (2^7) (fun m => test 7 464008 m [] cells7_23[m]!) = true := by decide +kernel

def cells7_24 : Array ℕ := #[150610880,45848513,12351425,297635789,71798722,544714700,574075852,297635789,146291649,484350,392643539,484350,657441740,484350,1593978828,484350,112794561,157239251,493566,493566,686802892,1590301644,493566,493566,1199449037,484350,493566,484350,1199449037,484350,493566,484350,37392320,500734,501758,500734,502782,500734,501758,500734,146291649,484350,501758,484350,502782,484350,501758,484350,112794561,500734,493566,500734,502782,500734,493566,500734,1489559498,484350,493566,484350,502782,484350,493566,484350,150610880,45848513,12351425,1646510026,510974,510974,510974,510974,511998,484350,511998,484350,510974,484350,510974,484350,513022,513022,493566,493566,510974,510974,493566,493566,511998,484350,493566,484350,510974,484350,493566,484350,150610880,500734,501758,500734,502782,500734,501758,500734,511998,484350,501758,484350,502782,484350,501758,484350,513022,500734,493566,500734,502782,500734,493566,500734,511998,484350,493566,484350,502782,484350,493566,484350]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_24_ok : scan (2^7) (fun m => test 7 924808 m [] cells7_24[m]!) = true := by decide +kernel

def cells7_25 : Array ℕ := #[150610881,188434369,121488321,226257857,159254465,62754755,29200321,61665220,196619201,484350,71218115,484350,37663681,484350,86959044,484350,205082561,492542,493566,492542,108582851,492542,493566,492542,75028417,484350,493566,484350,124839876,484350,493566,484350,8025025,209351619,501758,501758,502782,502782,501758,501758,146348995,484350,501758,484350,502782,484350,501758,484350,112794561,492542,493566,492542,502782,492542,493566,492542,159509444,484350,493566,484350,502782,484350,493566,484350,150610881,45848513,12294083,23325636,510974,510974,510974,510974,511998,484350,511998,484350,510974,484350,510974,484350,184165315,492542,493566,492542,510974,492542,493566,492542,511998,484350,493566,484350,510974,484350,493566,484350,150610881,219867076,501758,501758,502782,502782,501758,501758,511998,484350,501758,484350,502782,484350,501758,484350,181527492,492542,493566,492542,502782,492542,493566,492542,511998,484350,493566,484350,502782,484350,493566,484350]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_25_ok : scan (2^7) (fun m => test 7 399560 m [] cells7_25[m]!) = true := by decide +kernel

def cells7_26 : Array ℕ := #[150610881,188434369,121488321,226257857,121488321,573502413,121488321,43827145,71160771,484350,87933891,484350,87016388,484350,87016388,484350,171585475,492542,493566,492542,350609356,492542,493566,492542,1758585812,484350,493566,484350,657334217,484350,493566,484350,150610881,1544679373,501758,501758,502782,502782,501758,501758,1796882380,484350,501758,484350,502782,484350,501758,484350,181871556,492542,493566,492542,502782,492542,493566,492542,1490100169,484350,493566,484350,502782,484350,493566,484350,150610881,45848513,509950,509950,510974,510974,509950,509950,511998,484350,509950,484350,510974,484350,509950,484350,184165315,492542,493566,492542,510974,492542,493566,492542,511998,484350,493566,484350,510974,484350,493566,484350,150610881,224616393,501758,501758,502782,502782,501758,501758,511998,484350,501758,484350,502782,484350,501758,484350,181871556,492542,493566,492542,502782,492542,493566,492542,511998,484350,493566,484350,502782,484350,493566,484350]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_26_ok : scan (2^7) (fun m => test 7 465096 m [] cells7_26[m]!) = true := by decide +kernel

def cells7_27 : Array ℕ := #[150610881,83672001,83672001,83672001,574527433,75290570,43841481,350731216,968378323,484350,43827148,484350,574527433,484350,82181076,484350,1270368201,492542,493566,492542,1809400780,492542,493566,492542,1270368201,484350,493566,484350,16829260759,484350,493566,484350,150610881,500734,501758,500734,502782,500734,501758,500734,1796882380,484350,501758,484350,502782,484350,501758,484350,1796925385,492542,493566,492542,502782,492542,493566,492542,1758585812,484350,493566,484350,502782,484350,493566,484350,150610881,188434369,509950,509950,510974,510974,509950,509950,511998,484350,509950,484350,510974,484350,509950,484350,1769605066,492542,493566,492542,510974,492542,493566,492542,511998,484350,493566,484350,510974,484350,493566,484350,150610881,500734,501758,500734,502782,500734,501758,500734,511998,484350,501758,484350,502782,484350,501758,484350,1490494416,492542,493566,492542,502782,492542,493566,492542,511998,484350,493566,484350,502782,484350,493566,484350]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_27_ok : scan (2^7) (fun m => test 7 466120 m [] cells7_27[m]!) = true := by decide +kernel

def cells7_28 : Array ℕ := #[150610881,1798989765,87991235,352114638,87991236,573961165,87991236,82302932,71218115,484350,71218115,484350,71218116,484350,87991236,484350,1782198213,492542,493566,492542,657843149,492542,493566,492542,880334798,484350,493566,484350,1145558996,484350,493566,484350,150610881,195514313,501758,501758,502782,502782,501758,501758,503806,484350,501758,484350,502782,484350,501758,484350,1267156937,492542,493566,492542,502782,492542,493566,492542,503806,484350,493566,484350,502782,484350,493566,484350,150610881,224874441,509950,509950,510974,510974,509950,509950,511998,484350,509950,484350,510974,484350,509950,484350,1296517065,492542,493566,492542,510974,492542,493566,492542,511998,484350,493566,484350,510974,484350,493566,484350,150610881,224587719,501758,501758,502782,502782,501758,501758,503806,484350,501758,484350,502782,484350,501758,484350,1296230343,492542,493566,492542,502782,492542,493566,492542,503806,484350,493566,484350,502782,484350,493566,484350]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_28_ok : scan (2^7) (fun m => test 7 473288 m [] cells7_28[m]!) = true := by decide +kernel

def cells7_29 : Array ℕ := #[1492788165,587045829,1304571852,352164816,1304514508,587045840,73380807,587045841,1490150347,484350,876524500,484350,842970068,484350,7016985560,484350,301305804,492542,493566,492542,494590,492542,493566,492542,1001932756,484350,493566,484350,494590,484350,493566,484350,301248460,500734,501758,500734,502782,500734,501758,500734,968378324,484350,501758,484350,502782,484350,501758,484350,1797212103,492542,493566,492542,494590,492542,493566,492542,14375052248,484350,493566,484350,494590,484350,493566,484350,1492788165,75215822,509950,509950,510974,510974,509950,509950,511998,484350,509950,484350,510974,484350,509950,484350,1257907152,492542,493566,492542,494590,492542,493566,492542,511998,484350,493566,484350,494590,484350,493566,484350,1492788176,500734,501758,500734,502782,500734,501758,500734,511998,484350,501758,484350,502782,484350,501758,484350,1492788177,492542,493566,492542,494590,492542,493566,492542,511998,484350,493566,484350,494590,484350,493566,484350]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 8000000 in
theorem cells7_29_ok : scan (2^7) (fun m => test 7 466376 m [] cells7_29[m]!) = true := by decide +kernel

theorem level8 : Census 8 [] := by
  apply step level7
  apply row_cons cells7_0 cells7_0_ok
  apply row_cons cells7_1 cells7_1_ok
  apply row_cons cells7_2 cells7_2_ok
  apply row_cons cells7_3 cells7_3_ok
  apply row_cons cells7_4 cells7_4_ok
  apply row_cons cells7_5 cells7_5_ok
  apply row_cons cells7_6 cells7_6_ok
  apply row_cons cells7_7 cells7_7_ok
  apply row_cons cells7_8 cells7_8_ok
  apply row_cons cells7_9 cells7_9_ok
  apply row_cons cells7_10 cells7_10_ok
  apply row_cons cells7_11 cells7_11_ok
  apply row_cons cells7_12 cells7_12_ok
  apply row_cons cells7_13 cells7_13_ok
  apply row_cons cells7_14 cells7_14_ok
  apply row_cons cells7_15 cells7_15_ok
  apply row_cons cells7_16 cells7_16_ok
  apply row_cons cells7_17 cells7_17_ok
  apply row_cons cells7_18 cells7_18_ok
  apply row_cons cells7_19 cells7_19_ok
  apply row_cons cells7_20 cells7_20_ok
  apply row_cons cells7_21 cells7_21_ok
  apply row_cons cells7_22 cells7_22_ok
  apply row_cons cells7_23 cells7_23_ok
  apply row_cons cells7_24 cells7_24_ok
  apply row_cons cells7_25 cells7_25_ok
  apply row_cons cells7_26 cells7_26_ok
  apply row_cons cells7_27 cells7_27_ok
  apply row_cons cells7_28 cells7_28_ok
  apply row_cons cells7_29 cells7_29_ok
  exact rows_nil

end EarlyBlockerAtlas

theorem OMA.solution : OMA.R_RamseyNumbers_ramsey_number_four_five_R1_H1_R1_H3_R1.H1 := by
  intro G hg hc
  change EarlyBlockerAtlas.Obstruction G
  by_contra avoid
  obtain ⟨w,hw,_⟩ := EarlyBlockerAtlas.level8 G hg hc avoid
  exact List.not_mem_nil hw
